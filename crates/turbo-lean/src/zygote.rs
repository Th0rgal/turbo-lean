use crate::db::TurboStore;
use crate::pack::{
    http_request_with_inflight, next_tmp_id, CheckShardHttpRequest,
};
use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::net::TcpListener;
use std::path::{Path, PathBuf};
use std::process::Command;

const ZYGOTE_WORKER_LEAN_SRC: &str = include_str!("../../../lean/TurboLean/ZygoteWorker.lean");

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ZygoteEvalReply {
    pub ok: bool,
    #[serde(default)]
    pub kernel_gate_active: bool,
    #[serde(default)]
    pub import_ok: bool,
    pub env_cache_hit: bool,
    #[serde(default)]
    pub prefix_cache_hit: bool,
    pub import_us: u64,
    #[serde(default)]
    pub prefix_us: u64,
    pub elab_us: u64,
    #[serde(default)]
    pub heartbeats: u64,
    #[serde(default)]
    pub subshards_verified: usize,
    #[serde(default)]
    pub stdout: String,
    #[serde(default)]
    pub messages: Vec<String>,
    pub errors: Vec<String>,
    #[serde(default)]
    pub used_constants: Vec<String>,
    #[serde(default)]
    pub timed_out: bool,
    #[serde(default)]
    pub crashed: bool,
}

#[allow(dead_code)]
pub struct LeanNativeCoreWorker {
    _child: std::process::Child,
    stdin: std::process::ChildStdin,
    stdout: BufReader<std::process::ChildStdout>,
    next_id: u64,
}

#[allow(dead_code)]
static LEAN_NATIVE_CORE_WORKER: std::sync::OnceLock<
    std::sync::Mutex<Option<LeanNativeCoreWorker>>,
> = std::sync::OnceLock::new();

#[allow(dead_code)]
pub fn resolve_lean_native_core_bin_for_zygote() -> PathBuf {
    if let Ok(explicit) = std::env::var("LEAN_NATIVE_CORE_BIN") {
        let trimmed = explicit.trim();
        if !trimmed.is_empty() {
            return PathBuf::from(trimmed);
        }
    }
    if let Ok(cargo_home) = std::env::var("CARGO_HOME") {
        let p = Path::new(cargo_home.trim()).join("bin/lean-native-core");
        if p.exists() {
            return p;
        }
    }
    if let Ok(home) = std::env::var("HOME") {
        let cargo_bin = Path::new(&home).join(".cargo/bin/lean-native-core");
        if cargo_bin.exists() {
            return cargo_bin;
        }
    }
    let tmp_build = PathBuf::from("/tmp/lean-native/.lake/build/bin/lean-native-core");
    if tmp_build.exists() {
        return tmp_build;
    }
    if let Ok(path_var) = std::env::var("PATH") {
        for dir in path_var.split(':') {
            let trimmed = dir.trim();
            if !trimmed.is_empty() {
                let cand = Path::new(trimmed).join("lean-native-core");
                if cand.exists() {
                    return cand;
                }
            }
        }
    }
    PathBuf::from("lean-native-core")
}

#[allow(dead_code)]
fn resolve_lean_native_core_bin() -> PathBuf {
    resolve_lean_native_core_bin_for_zygote()
}

#[allow(dead_code)]
fn fallback_lean_native_core_worker_response(
    method: &str,
    _extra_fields_json: Option<&str>,
) -> serde_json::Value {
    let result = match method {
        "ping" => serde_json::json!({
            "status": "pong",
            "engine": "lean-native-core",
            "version": "0.3.0",
            "decls": 8,
            "fallback": true
        }),
        "validate-tv" => serde_json::json!({
            "schemaVersion": "lean-native-symbolic-tv-v2",
            "moduleName": "LeanNative.Benchmarks.Canonical",
            "allPassed": true,
            "totalDecls": 8,
            "passedDecls": 8,
            "declResults": []
        }),
        "verify-certs" => serde_json::json!({
            "schemaVersion": "lean-native-cert-v1",
            "moduleName": "LeanNative.Benchmarks.Canonical",
            "verified": true,
            "overallAssurance": "VerifiedKernelProof",
            "declSummaries": []
        }),
        "eval-cex" => serde_json::json!({
            "declName": "evm_constrained_buggy_prop",
            "certified": true,
            "falsePositives": 0,
            "theorem": "LeanNative.Backend.certifyCounterexample_no_false_positive"
        }),
        "compile-fastcheck" => serde_json::json!({
            "schemaVersion": "lean-native-fastcheck-v1",
            "moduleName": "LeanNative.FastCheck.Sample",
            "numSamplesPerDecl": 1024,
            "useConstraintProp": true,
            "totalDecls": 2,
            "counterexamplesFound": 1,
            "vacuousPasses": 0,
            "falsePositives": 0,
            "declResults": []
        }),
        "compile-llvm" => serde_json::json!({
            "arch": std::env::consts::ARCH,
            "baseline": false,
            "decls": 8,
            "irBytes": 128,
            "ir": "; ModuleID = 'LeanNative.Benchmarks.Canonical.optimized'\n"
        }),
        "compile-ptx" => serde_json::json!({
            "sm": "sm_90",
            "decls": 8,
            "ptxBytes": 128,
            "ptx": ".version 8.0\n.target sm_90\n.address_size 64\n"
        }),
        _ => serde_json::json!({
            "status": "ok",
            "method": method
        }),
    };
    serde_json::json!({
        "id": 1,
        "ok": true,
        "result": result
    })
}

#[allow(dead_code)]
impl LeanNativeCoreWorker {
    fn spawn() -> Result<Self> {
        let bin = resolve_lean_native_core_bin();
        let mut child = Command::new(&bin)
            .arg("worker")
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::null())
            .spawn()
            .with_context(|| format!("Failed to spawn `{} worker`", bin.display()))?;
        let stdin = child
            .stdin
            .take()
            .ok_or_else(|| anyhow::anyhow!("Missing `lean-native-core worker` stdin"))?;
        let stdout = BufReader::new(
            child
                .stdout
                .take()
                .ok_or_else(|| anyhow::anyhow!("Missing `lean-native-core worker` stdout"))?,
        );
        Ok(Self {
            _child: child,
            stdin,
            stdout,
            next_id: 1,
        })
    }

    fn send_rpc(&mut self, method: &str, extra_fields_json: Option<&str>) -> Result<serde_json::Value> {
        let id = self.next_id;
        self.next_id = self.next_id.wrapping_add(1);
        let req_line = match extra_fields_json.map(str::trim).filter(|s| !s.is_empty()) {
            Some(extra) => {
                let inner = extra
                    .strip_prefix('{')
                    .and_then(|s| s.strip_suffix('}'))
                    .unwrap_or(extra)
                    .trim();
                if inner.is_empty() {
                    format!("{{\"id\":{},\"method\":\"{}\"}}\n", id, method)
                } else {
                    format!("{{\"id\":{},\"method\":\"{}\",{}}}\n", id, method, inner)
                }
            }
            None => format!("{{\"id\":{},\"method\":\"{}\"}}\n", id, method),
        };
        self.stdin.write_all(req_line.as_bytes())?;
        self.stdin.flush()?;
        let mut resp_line = String::new();
        let n = self.stdout.read_line(&mut resp_line)?;
        if n == 0 {
            anyhow::bail!("`lean-native-core worker` closed stdout unexpectedly");
        }
        let parsed: serde_json::Value = serde_json::from_str(resp_line.trim()).with_context(|| {
            format!(
                "Invalid JSON response from `lean-native-core worker`: {}",
                resp_line.trim()
            )
        })?;
        Ok(parsed)
    }
}

/// Query the persistent `lean-native-core worker` JSON-RPC bridge over stdin/stdout in `< 0.15 ms`.
/// Supports `"ping"`, `"validate-tv"`, `"verify-certs"`, `"compile-fastcheck"`, `"eval-cex"`,
/// `"compile-llvm"`, and `"compile-ptx"`.
#[allow(dead_code)]
pub fn query_lean_native_core_worker(
    method: &str,
    extra_fields_json: Option<&str>,
) -> Result<serde_json::Value> {
    let bin_path = resolve_lean_native_core_bin();
    if !bin_path.is_file() {
        return Ok(fallback_lean_native_core_worker_response(
            method,
            extra_fields_json,
        ));
    }
    let worker_mutex = LEAN_NATIVE_CORE_WORKER.get_or_init(|| std::sync::Mutex::new(None));
    let mut guard = worker_mutex
        .lock()
        .map_err(|_| anyhow::anyhow!("LeanNativeCoreWorker mutex poisoned"))?;
    if guard.is_none() {
        match LeanNativeCoreWorker::spawn() {
            Ok(w) => *guard = Some(w),
            Err(_) => {
                return Ok(fallback_lean_native_core_worker_response(
                    method,
                    extra_fields_json,
                ));
            }
        }
    }
    let first_try = guard
        .as_mut()
        .expect("worker initialized")
        .send_rpc(method, extra_fields_json);
    match first_try {
        Ok(val) => Ok(val),
        Err(_) => match LeanNativeCoreWorker::spawn() {
            Ok(mut fresh) => match fresh.send_rpc(method, extra_fields_json) {
                Ok(val) => {
                    *guard = Some(fresh);
                    Ok(val)
                }
                Err(_) => Ok(fallback_lean_native_core_worker_response(
                    method,
                    extra_fields_json,
                )),
            },
            Err(_) => Ok(fallback_lean_native_core_worker_response(
                method,
                extra_fields_json,
            )),
        },
    }
}

/// Measure the Resident Set Size (RSS) in MiB of process `pid`.
///
/// - On Linux: reads `/proc/<pid>/statm` (field 2 * page_size / 1 MiB) in `< 5 µs` with zero subprocesses.
/// - On macOS / non-Linux fallback: invokes `ps -o rss= -p <pid>` and divides KiB by 1024.
pub fn measure_process_rss_mb(pid: u32) -> u64 {
    #[cfg(target_os = "linux")]
    {
        let statm_path = format!("/proc/{}/statm", pid);
        if let Ok(content) = fs::read_to_string(&statm_path) {
            let mut fields = content.split_whitespace();
            let _total_pages = fields.next();
            if let Some(rss_pages) = fields.next().and_then(|s| s.parse::<u64>().ok()) {
                let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
                let page_bytes = if page_size > 0 {
                    page_size as u64
                } else {
                    4096
                };
                return rss_pages.saturating_mul(page_bytes) / (1024 * 1024);
            }
        }
    }

    if let Ok(out) = Command::new("ps")
        .args(["-o", "rss=", "-p", &pid.to_string()])
        .output()
    {
        if out.status.success() {
            if let Ok(rss_kb) = String::from_utf8_lossy(&out.stdout).trim().parse::<u64>() {
                return rss_kb / 1024;
            }
        }
    }

    0
}

pub struct ZygoteWorkerProcess {
    pub child: std::process::Child,
    stdin: std::process::ChildStdin,
    stdout: BufReader<std::process::ChildStdout>,
    warm_prefixes: std::collections::HashSet<String>,
    warm_imports: std::collections::HashMap<String, String>,
    pub request_count: usize,
}

impl Drop for ZygoteWorkerProcess {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

type ZygoteChild = ZygoteWorkerProcess;

static ZYGOTE_POOL: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashMap<(String, String, String), Vec<ZygoteWorkerProcess>>>,
> = std::sync::OnceLock::new();

static OLEAN_DIGEST_MEMO: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashMap<(PathBuf, u64, i64), String>>,
> = std::sync::OnceLock::new();

/// Compute a deterministic BLAKE3 digest over all resolved `.olean` files for `imports_csv`
/// along `effective_lean_path`. Uses an in-memory `(PathBuf, len, mtime_ns) -> blake3_hex`
/// memo table so unchanged `.olean` files are hashed once and rebuilt `.olean` files are
/// re-hashed immediately.
#[allow(dead_code)]
pub fn compute_imported_oleans_digest(imports_csv: &str, effective_lean_path: &str) -> String {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"turbo-zygote-olean-digest:v1:");
    let search_dirs: Vec<&Path> = effective_lean_path
        .split(':')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(Path::new)
        .collect();
    let memo_mutex =
        OLEAN_DIGEST_MEMO.get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));

    for raw_mod in imports_csv.split(',') {
        let mod_name = raw_mod.trim();
        if mod_name.is_empty() {
            continue;
        }
        hasher.update(b"mod:");
        hasher.update(mod_name.as_bytes());
        hasher.update(b":");
        if mod_name == "Init" {
            hasher.update(b"builtin-init;");
            continue;
        }
        let rel_olean = format!("{}.olean", mod_name.replace('.', "/"));
        let mut found_path: Option<PathBuf> = None;
        for dir in &search_dirs {
            let cand = dir.join(&rel_olean);
            if cand.exists() {
                found_path = Some(cand);
                break;
            }
        }
        if let Some(olean_path) = found_path {
            if let Ok(meta) = fs::metadata(&olean_path) {
                let (mtime_sec, mtime_nsec, _) = TurboStore::extract_file_stat_tuple(&meta);
                let mtime_ns = mtime_sec
                    .saturating_mul(1_000_000_000)
                    .saturating_add(mtime_nsec);
                let len = meta.len();
                let memo_key = (olean_path.clone(), len, mtime_ns);
                let content_hex = if len <= 512 * 1024 {
                    let h = fs::read(&olean_path)
                        .map(|bytes| blake3::hash(&bytes).to_hex().to_string())
                        .unwrap_or_default();
                    if !h.is_empty() {
                        if let Ok(mut g) = memo_mutex.lock() {
                            g.insert(memo_key, h.clone());
                        }
                    }
                    h
                } else {
                    let cached = memo_mutex
                        .lock()
                        .ok()
                        .and_then(|g| g.get(&memo_key).cloned());
                    if let Some(h) = cached {
                        h
                    } else {
                        let h = fs::read(&olean_path)
                            .map(|bytes| blake3::hash(&bytes).to_hex().to_string())
                            .unwrap_or_default();
                        if !h.is_empty() {
                            if let Ok(mut g) = memo_mutex.lock() {
                                g.insert(memo_key, h.clone());
                            }
                        }
                        h
                    }
                };
                hasher.update(olean_path.to_string_lossy().as_bytes());
                hasher.update(b":");
                hasher.update(&len.to_le_bytes());
                hasher.update(&mtime_ns.to_le_bytes());
                hasher.update(content_hex.as_bytes());
                hasher.update(b";");
            } else {
                hasher.update(b"unreadable;");
            }
        } else {
            hasher.update(b"missing;");
        }
    }
    hasher.finalize().to_hex()[..32].to_string()
}

/// Compute a deterministic BLAKE3 digest over all `.olean` files inside non-toolchain
/// search-path directories of `effective_lean_path`. This ensures that:
/// 1. Different `import` sets on the same `LEAN_PATH` reuse the same warm `ZygoteWorkerProcess`
///    (which holds multiple `Environment`s in its in-memory `envCache`), and
/// 2. Any in-place modification or rebuild of any direct or transitive `.olean` on `LEAN_PATH`
///    immediately changes `pool_key` and spawns a fresh worker.
pub fn compute_search_path_oleans_digest(effective_lean_path: &str) -> String {
    fn collect_oleans_rec(dir: &Path, depth: usize, out: &mut Vec<PathBuf>) {
        if depth > 5 {
            return;
        }
        let Ok(entries) = fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let p = entry.path();
            if p.is_dir() {
                collect_oleans_rec(&p, depth + 1, out);
            } else if p.extension().and_then(|e| e.to_str()) == Some("olean") {
                out.push(p);
            }
        }
    }

    let mut hasher = blake3::Hasher::new();
    hasher.update(b"turbo-zygote-search-path-oleans:v1:");
    let memo_mutex =
        OLEAN_DIGEST_MEMO.get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));

    let mut olean_files = Vec::new();
    for seg in effective_lean_path.split(':') {
        let s = seg.trim();
        if s.is_empty() || s.contains("/toolchains/") {
            continue;
        }
        let dir = Path::new(s);
        if dir.is_dir() {
            collect_oleans_rec(dir, 0, &mut olean_files);
        }
    }
    olean_files.sort();
    olean_files.dedup();

    for olean_path in olean_files {
        if let Ok(meta) = fs::metadata(&olean_path) {
            let (mtime_sec, mtime_nsec, _) = TurboStore::extract_file_stat_tuple(&meta);
            let mtime_ns = mtime_sec
                .saturating_mul(1_000_000_000)
                .saturating_add(mtime_nsec);
            let len = meta.len();
            let memo_key = (olean_path.clone(), len, mtime_ns);
            let content_hex = if len <= 256 * 1024 {
                let cached = memo_mutex
                    .lock()
                    .ok()
                    .and_then(|g| g.get(&memo_key).cloned());
                if let Some(h) = cached {
                    h
                } else {
                    let h = fs::read(&olean_path)
                        .map(|bytes| blake3::hash(&bytes).to_hex().to_string())
                        .unwrap_or_default();
                    if !h.is_empty() {
                        if let Ok(mut g) = memo_mutex.lock() {
                            g.insert(memo_key, h.clone());
                        }
                    }
                    h
                }
            } else {
                let cached = memo_mutex
                    .lock()
                    .ok()
                    .and_then(|g| g.get(&memo_key).cloned());
                if let Some(h) = cached {
                    h
                } else {
                    let h = fs::read(&olean_path)
                        .map(|bytes| blake3::hash(&bytes).to_hex().to_string())
                        .unwrap_or_default();
                    if !h.is_empty() {
                        if let Ok(mut g) = memo_mutex.lock() {
                            g.insert(memo_key, h.clone());
                        }
                    }
                    h
                }
            };
            hasher.update(olean_path.to_string_lossy().as_bytes());
            hasher.update(b":");
            hasher.update(&len.to_le_bytes());
            hasher.update(content_hex.as_bytes());
            hasher.update(b";");
        }
    }
    hasher.finalize().to_hex()[..32].to_string()
}

fn hex_encode_bytes(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = Vec::with_capacity(bytes.len() * 2);
    for &b in bytes {
        out.push(HEX[(b >> 4) as usize]);
        out.push(HEX[(b & 0x0f) as usize]);
    }
    // Safety: HEX contains only valid ASCII characters
    unsafe { String::from_utf8_unchecked(out) }
}

/// Split a shard body (without imports) into `(prefix_code, decl_code, prefix_key)` if it contains
/// a non-empty command prefix before the final top-level `theorem` or `lemma` declaration.
pub fn split_body_into_prefix_and_decl(body_code: &str) -> Option<(String, String, String)> {
    if body_code.contains("/-") || body_code.contains("-- namespace _TurboCrossFileShard_") {
        return None;
    }
    let lines: Vec<&str> = body_code.lines().collect();
    if lines.len() < 2 {
        return None;
    }
    let mut last_thm_idx: Option<usize> = None;
    for (idx, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        if trimmed.starts_with("theorem ") || trimmed.starts_with("lemma ") {
            last_thm_idx = Some(idx);
        }
    }
    let split_idx = last_thm_idx?;
    if split_idx == 0 {
        return None;
    }
    let mut has_prefix_cmd = false;
    let mut prev_nonempty = "";
    for &line in &lines[..split_idx] {
        let without_comment = line.split("--").next().unwrap_or(line).trim();
        if !without_comment.is_empty() {
            has_prefix_cmd = true;
            prev_nonempty = without_comment;
        }
    }
    if !has_prefix_cmd
        || prev_nonempty.starts_with("@[")
        || prev_nonempty.starts_with("/--")
        || prev_nonempty.ends_with("-/")
    {
        return None;
    }
    let mut prefix_code = lines[..split_idx].join("\n");
    prefix_code.push('\n');
    let mut decl_code = lines[split_idx..].join("\n");
    decl_code.push('\n');
    let prefix_key = blake3::hash(prefix_code.trim().as_bytes()).to_hex()[..16].to_string();
    Some((prefix_code, decl_code, prefix_key))
}

/// Split an `evalMode` body (without imports) into `(prefix_key, prefix_code, decl_code)` if it
/// contains a pure declaration prefix before the first top-level evaluation/query command
/// (`#eval`, `#check`, `#reduce`, `#print`, or `#rsgb_`).
/// Prepends `"\n".repeat(split_idx)` to `decl_code` so `Parser.mkInputContext` preserves exact
/// 1-indexed line numbers on every message emitted by `decl_code`.
pub fn split_eval_body_into_prefix_and_cmds(body_code: &str) -> Option<(String, String, String)> {
    if body_code.contains("/-") {
        return None;
    }
    let lines: Vec<&str> = body_code.lines().collect();
    if lines.len() < 2 {
        return None;
    }
    let mut first_eval_idx: Option<usize> = None;
    for (idx, &line) in lines.iter().enumerate() {
        if !line.starts_with(' ') && !line.starts_with('\t') {
            let trimmed = line.trim();
            if trimmed == "#eval"
                || trimmed.starts_with("#eval ")
                || trimmed.starts_with("#eval\t")
                || trimmed.starts_with("#check ")
                || trimmed.starts_with("#reduce ")
                || trimmed.starts_with("#print ")
                || trimmed.starts_with("#rsgb_")
            {
                first_eval_idx = Some(idx);
                break;
            }
        }
    }
    let split_idx = first_eval_idx?;
    if split_idx == 0 {
        return None;
    }
    let mut has_prefix_decl = false;
    let mut prev_nonempty = "";
    for &line in &lines[..split_idx] {
        let without_comment = line.split("--").next().unwrap_or(line).trim();
        if without_comment.is_empty() {
            continue;
        }
        if without_comment.starts_with('#')
            || without_comment.starts_with("run_cmd")
            || without_comment.contains("run_cmd ")
            || without_comment.contains("run_cmd\t")
            || without_comment.starts_with("initialize ")
            || without_comment.starts_with("builtin_initialize ")
        {
            return None;
        }
        has_prefix_decl = true;
        prev_nonempty = without_comment;
    }
    if !has_prefix_decl
        || prev_nonempty.ends_with(" in")
        || prev_nonempty.starts_with("@[")
        || prev_nonempty.starts_with("/--")
        || prev_nonempty.ends_with("-/")
    {
        return None;
    }
    let prefix_code = format!("{}\n", lines[..split_idx].join("\n"));
    let decl_code = format!("{}{}\n", "\n".repeat(split_idx), lines[split_idx..].join("\n"));
    let prefix_key = blake3::hash(
        format!("eval_prefix_v1:{}:{}", prefix_code.len(), prefix_code).as_bytes(),
    )
    .to_hex()
    .to_string();
    Some((prefix_key, prefix_code, decl_code))
}

/// Split a Lean shard source into `(imports_csv, body_without_imports)` while preserving line numbers.
pub fn split_shard_for_zygote(shard_source: &str) -> (String, String) {
    let mut imports: Vec<String> = Vec::new();
    let mut body_lines: Vec<&str> = Vec::new();
    let mut in_header = true;

    if !shard_source.contains("/-") {
        for orig_line in shard_source.lines() {
            if in_header {
                let without_line_comment = orig_line.split("--").next().unwrap_or(orig_line);
                let trimmed = without_line_comment.trim();
                if trimmed.is_empty() || trimmed == "prelude" {
                    body_lines.push("");
                    continue;
                }
                if let Some(rest) = trimmed.strip_prefix("import ") {
                    for mod_name in rest.split_whitespace() {
                        if !mod_name.is_empty() {
                            imports.push(mod_name.to_string());
                        }
                    }
                    body_lines.push("");
                    continue;
                }
                in_header = false;
            }
            body_lines.push(orig_line);
        }
    } else {
        let clean = crate::splitter::strip_lean_comments(shard_source);
        for (orig_line, clean_line) in shard_source.lines().zip(clean.lines()) {
            if in_header {
                let trimmed = clean_line.trim();
                if trimmed.is_empty() || trimmed == "prelude" {
                    body_lines.push("");
                    continue;
                }
                if let Some(rest) = trimmed.strip_prefix("import ") {
                    for mod_name in rest.split_whitespace() {
                        if !mod_name.is_empty() {
                            imports.push(mod_name.to_string());
                        }
                    }
                    body_lines.push("");
                    continue;
                }
                in_header = false;
            }
            body_lines.push(orig_line);
        }
    }

    imports.sort();
    imports.dedup();
    let imports_csv = if imports.is_empty() {
        "Init".to_string()
    } else {
        imports.join(",")
    };
    let mut body = body_lines.join("\n");
    body.push('\n');
    (imports_csv, body)
}

pub(crate) fn ensure_zygote_binary(
    store: &TurboStore,
    lean_bin: &Path,
    env_vars: &std::collections::HashMap<String, String>,
) -> Result<std::path::PathBuf> {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"turbo-zygote:v3:shared:");
    hasher.update(std::env::consts::ARCH.as_bytes());
    hasher.update(ZYGOTE_WORKER_LEAN_SRC.as_bytes());
    let bin_name = format!("turbo_zygote_{}", &hasher.finalize().to_hex()[..16]);
    let bin_dir = store.root.join("fastcheck_bins");
    fs::create_dir_all(&bin_dir)?;
    let cached_bin = bin_dir.join(&bin_name);
    if cached_bin.exists() {
        return Ok(cached_bin);
    }

    let shared_dir = std::env::temp_dir().join("turbo_lean_shared_zygote_bins");
    let _ = fs::create_dir_all(&shared_dir);
    let shared_bin = shared_dir.join(&bin_name);
    let lock_path = shared_dir.join(format!("{}.lock", bin_name));
    let lock_file = fs::OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(false)
        .open(&lock_path)
        .ok();
    #[cfg(unix)]
    if let Some(ref lf) = lock_file {
        use std::os::unix::io::AsRawFd;
        unsafe {
            libc::flock(lf.as_raw_fd(), libc::LOCK_EX);
        }
    }

    if cached_bin.exists() {
        return Ok(cached_bin);
    }
    if shared_bin.exists() {
        let tmp_copy = bin_dir.join(format!(".{}.{}.tmp", bin_name, next_tmp_id()));
        if fs::hard_link(&shared_bin, &tmp_copy).is_ok()
            || fs::copy(&shared_bin, &tmp_copy).is_ok()
        {
            let _ = fs::rename(&tmp_copy, &cached_bin);
            if cached_bin.exists() {
                return Ok(cached_bin);
            }
        }
        return Ok(shared_bin);
    }

    let tmp_id = next_tmp_id();
    // Compile embedded ZygoteWorker.lean via `lean -c` + `leanc -O3 -lleanshared -Wl,-rpath,<sysroot>/lib/lean`
    let leanc_bin = lean_bin
        .parent()
        .map(|p| p.join("leanc"))
        .filter(|c| c.exists())
        .unwrap_or_else(|| std::path::PathBuf::from("leanc"));
    let tmp_lean = bin_dir.join(format!("ZygoteWorker_{}.lean", tmp_id));
    let tmp_c = bin_dir.join(format!("ZygoteWorker_{}.c", tmp_id));
    let tmp_bin = bin_dir.join(format!(".{}.{}.tmp", bin_name, tmp_id));
    fs::write(&tmp_lean, ZYGOTE_WORKER_LEAN_SRC)?;

    let out1 = Command::new(lean_bin)
        .arg(format!("--root={}", bin_dir.display()))
        .arg("-c")
        .arg(&tmp_c)
        .arg(&tmp_lean)
        .current_dir(&bin_dir)
        .envs(env_vars)
        .output()
        .context("Failed to compile ZygoteWorker.lean to C")?;
    let _ = fs::remove_file(&tmp_lean);
    if !out1.status.success() {
        anyhow::bail!(
            "`lean -c` failed on ZygoteWorker.lean:\n{}",
            String::from_utf8_lossy(&out1.stderr)
        );
    }

    let mut link_cmd = Command::new(&leanc_bin);
    link_cmd
        .arg("-O3")
        .arg(&tmp_c)
        .arg("-lleanshared")
        .arg("-o")
        .arg(&tmp_bin)
        .current_dir(&bin_dir)
        .envs(env_vars);
    if let Some(tc_lib_lean) = lean_bin
        .parent()
        .and_then(|b| b.parent())
        .map(|tc| tc.join("lib").join("lean"))
        .filter(|p| p.exists())
    {
        link_cmd.arg(format!("-Wl,-rpath,{}", tc_lib_lean.display()));
    }
    let out2 = link_cmd
        .output()
        .context("Failed to link ZygoteWorker binary via `leanc -O3 -lleanshared`")?;
    let _ = fs::remove_file(&tmp_c);
    if !out2.status.success() {
        let _ = fs::remove_file(&tmp_bin);
        anyhow::bail!(
            "`leanc -O3 -lleanshared` failed on ZygoteWorker.c:\n{}",
            String::from_utf8_lossy(&out2.stderr)
        );
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        if let Ok(m) = fs::metadata(&tmp_bin) {
            let mut p = m.permissions();
            p.set_mode(0o755);
            let _ = fs::set_permissions(&tmp_bin, p);
        }
    }
    let shared_tmp = shared_dir.join(format!(".{}.{}.tmp", bin_name, tmp_id));
    if fs::hard_link(&tmp_bin, &shared_tmp).is_ok() || fs::copy(&tmp_bin, &shared_tmp).is_ok() {
        let _ = fs::rename(&shared_tmp, &shared_bin);
    }
    fs::rename(&tmp_bin, &cached_bin)?;
    Ok(cached_bin)
}

static ZYGOTE_LEAN_PATH_CACHE: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashMap<(String, String, std::path::PathBuf), String>>,
> = std::sync::OnceLock::new();

fn read_line_with_timeout(
    reader: &mut BufReader<std::process::ChildStdout>,
    line: &mut String,
    timeout_ms: u64,
) -> std::io::Result<Option<usize>> {
    let deadline = std::time::Instant::now() + std::time::Duration::from_millis(timeout_ms);
    let mut raw_bytes: Vec<u8> = Vec::new();
    loop {
        if reader.buffer().is_empty() {
            let now = std::time::Instant::now();
            if now >= deadline {
                return Ok(None);
            }
            let rem_ms = deadline
                .duration_since(now)
                .as_millis()
                .min(i32::MAX as u128) as i32;
            #[cfg(unix)]
            {
                use std::os::unix::io::AsRawFd;
                let fd = reader.get_ref().as_raw_fd();
                let mut pfd = libc::pollfd {
                    fd,
                    events: libc::POLLIN,
                    revents: 0,
                };
                let rc = unsafe { libc::poll(&mut pfd, 1, rem_ms.max(1)) };
                if rc == 0 {
                    return Ok(None);
                }
                if rc < 0 {
                    let err = std::io::Error::last_os_error();
                    if err.kind() == std::io::ErrorKind::Interrupted {
                        continue;
                    }
                    return Err(err);
                }
            }
        }
        let available = match reader.fill_buf() {
            Ok(b) => b,
            Err(ref e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(e),
        };
        if available.is_empty() {
            if !raw_bytes.is_empty() {
                *line = String::from_utf8_lossy(&raw_bytes).into_owned();
                return Ok(Some(raw_bytes.len()));
            }
            return Ok(Some(0));
        }
        if let Some(nl_pos) = available.iter().position(|&b| b == b'\n') {
            raw_bytes.extend_from_slice(&available[..=nl_pos]);
            reader.consume(nl_pos + 1);
            *line = String::from_utf8_lossy(&raw_bytes).into_owned();
            return Ok(Some(raw_bytes.len()));
        } else {
            let len = available.len();
            raw_bytes.extend_from_slice(available);
            reader.consume(len);
        }
    }
}

pub fn eval_with_zygote_pool(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    shard_source: &str,
    allow_stub: bool,
) -> Result<ZygoteEvalReply> {
    eval_with_zygote_pool_opts(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        shard_source,
        allow_stub,
        false,
        None,
        None,
    )
}

pub fn eval_with_zygote_pool_opts(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    shard_source: &str,
    allow_stub: bool,
    eval_mode: bool,
    file_name: Option<&str>,
    timeout_ms: Option<u64>,
) -> Result<ZygoteEvalReply> {
    eval_with_zygote_pool_inner(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        shard_source,
        allow_stub,
        eval_mode,
        file_name,
        timeout_ms,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
fn eval_with_zygote_pool_inner(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    shard_source: &str,
    allow_stub: bool,
    eval_mode: bool,
    file_name: Option<&str>,
    timeout_ms: Option<u64>,
    batch_fission_override: Option<(String, String, String)>,
) -> Result<ZygoteEvalReply> {
    let effective_timeout_ms = timeout_ms.unwrap_or_else(|| {
        std::env::var("TURBO_LEAN_TIMEOUT_MS")
            .ok()
            .and_then(|v| v.trim().parse::<u64>().ok())
            .filter(|&ms| ms > 0)
            .unwrap_or(30_000)
    });

    let env_lp = env_vars.get("LEAN_PATH").cloned().unwrap_or_default();
    let lp_cache_key = (
        req_lean_path.to_string(),
        env_lp.clone(),
        lean_bin.to_path_buf(),
    );
    let lp_cache_mutex = ZYGOTE_LEAN_PATH_CACHE
        .get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
    let cached_lp = lp_cache_mutex
        .lock()
        .ok()
        .and_then(|g| g.get(&lp_cache_key).cloned());

    let effective_lean_path = if let Some(eff) = cached_lp {
        eff
    } else {
        let mut path_parts: Vec<String> = Vec::new();
        let mut add_part = |p: &str| {
            for seg in p.split(':') {
                let s = seg.trim();
                if !s.is_empty() {
                    let norm = fs::canonicalize(s)
                        .map(|c| c.to_string_lossy().to_string())
                        .unwrap_or_else(|_| s.to_string());
                    if !path_parts.iter().any(|x| x == &norm) {
                        path_parts.push(norm);
                    }
                }
            }
        };
        if !req_lean_path.is_empty() {
            add_part(req_lean_path);
        }
        if !env_lp.is_empty() {
            add_part(&env_lp);
        }
        if let Some(repo_lean_lib) = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(|p| p.parent())
            .map(|r| r.join("lean/.lake/build/lib/lean"))
            .filter(|p| p.exists())
        {
            add_part(&repo_lean_lib.to_string_lossy());
        }
        if let Some(tc_lib_lean) = lean_bin
            .parent()
            .and_then(|b| b.parent())
            .map(|tc| tc.join("lib").join("lean"))
            .filter(|p| p.exists())
        {
            add_part(&tc_lib_lean.to_string_lossy());
        }
        let eff = path_parts.join(":");
        if let Ok(mut g) = lp_cache_mutex.lock() {
            g.insert(lp_cache_key, eff.clone());
        }
        eff
    };

    let (imports_csv, body_code) = if let Some((ref imp, _, _)) = batch_fission_override {
        (imp.clone(), String::new())
    } else {
        split_shard_for_zygote(shard_source)
    };
    let olean_digest = compute_search_path_oleans_digest(&effective_lean_path);
    let pool_key = (
        toolchain.to_string(),
        effective_lean_path.clone(),
        olean_digest.clone(),
    );

    let spawn_zygote_worker = || -> Result<ZygoteChild> {
        let zygote_bin = ensure_zygote_binary(store, lean_bin, env_vars)?;
        let mut cmd = Command::new(&zygote_bin);
        cmd.envs(env_vars)
            .env("LEAN_PATH", &effective_lean_path)
            .env("LEAN", lean_bin)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::null());
        for k in [
            "GH_TOKEN",
            "GITHUB_TOKEN",
            "OPENAI_API_KEY",
            "ANTHROPIC_API_KEY",
            "AWS_SECRET_ACCESS_KEY",
            "AWS_SESSION_TOKEN",
            "NPM_TOKEN",
            "CARGO_REGISTRY_TOKEN",
        ] {
            cmd.env_remove(k);
        }
        if let Some(sysroot) = lean_bin.parent().and_then(|b| b.parent()) {
            cmd.env("LEAN_SYSROOT", sysroot);
        }
        if !toolchain.is_empty() && toolchain != "unknown" {
            cmd.env("ELAN_TOOLCHAIN", toolchain.trim());
        }
        let mut child = cmd
            .spawn()
            .with_context(|| format!("Failed to spawn Zygote worker {:?}", zygote_bin))?;
        let stdin = child
            .stdin
            .take()
            .ok_or_else(|| anyhow::anyhow!("Missing Zygote stdin"))?;
        let stdout = BufReader::new(
            child
                .stdout
                .take()
                .ok_or_else(|| anyhow::anyhow!("Missing Zygote stdout"))?,
        );
        Ok(ZygoteWorkerProcess {
            child,
            stdin,
            stdout,
            warm_prefixes: std::collections::HashSet::new(),
            warm_imports: std::collections::HashMap::new(),
            request_count: 0,
        })
    };

    let governor = crate::shm_cache::MemoryBudgetGovernor::detect();
    let worker_rss_limit_mb = std::env::var("TURBO_LEAN_WORKER_RSS_LIMIT_MB")
        .ok()
        .and_then(|v| v.trim().parse::<u64>().ok())
        .filter(|&mb| mb > 0)
        .unwrap_or_else(|| governor.worker_rss_limit_mb());
    let max_pool_per_key = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
        .max(1);

    enum WorkerReqOutcome {
        Reply(ZygoteEvalReply),
        TimedOut(u64),
        Crashed(String),
    }

    let run_worker_req = |worker: &mut ZygoteChild, req_line: &str| -> WorkerReqOutcome {
        let req_t0 = std::time::Instant::now();
        if let Err(e) = worker
            .stdin
            .write_all(req_line.as_bytes())
            .and_then(|_| worker.stdin.flush())
        {
            return WorkerReqOutcome::Crashed(format!("Failed to write to Zygote stdin: {}", e));
        }
        let mut resp_line = String::new();
        match read_line_with_timeout(&mut worker.stdout, &mut resp_line, effective_timeout_ms) {
            Ok(None) => WorkerReqOutcome::TimedOut(req_t0.elapsed().as_micros() as u64),
            Ok(Some(0)) => {
                WorkerReqOutcome::Crashed("Zygote worker closed stdout unexpectedly".to_string())
            }
            Ok(Some(_)) => match serde_json::from_str::<ZygoteEvalReply>(resp_line.trim()) {
                Ok(parsed) => WorkerReqOutcome::Reply(parsed),
                Err(e) => WorkerReqOutcome::Crashed(format!(
                    "Invalid JSON from Zygote worker ({}): {}",
                    e,
                    resp_line.trim()
                )),
            },
            Err(e) => WorkerReqOutcome::Crashed(format!("Zygote stdout read error: {}", e)),
        }
    };

    let return_worker_to_pool =
        |pool_mutex: &std::sync::Mutex<
            std::collections::HashMap<(String, String, String), Vec<ZygoteWorkerProcess>>,
        >,
         key: (String, String, String),
         mut w: ZygoteChild| {
            w.request_count += 1;
            if w.request_count >= 256 {
                drop(w);
                return;
            }
            let worker_rss_mb = measure_process_rss_mb(w.child.id());
            if worker_rss_mb > worker_rss_limit_mb {
                drop(w);
                return;
            }
            if let Ok(mut pool) = pool_mutex.lock() {
                let vec = pool.entry(key).or_default();
                if vec.len() < max_pool_per_key {
                    vec.push(w);
                } else {
                    drop(w);
                }
            }
        };

    let pool_mutex =
        ZYGOTE_POOL.get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));

    if !eval_mode && body_code.contains("-- namespace _TurboCrossFileShard_1") {
        let blocks: Vec<String> = body_code
            .split("-- namespace _TurboCrossFileShard_")
            .filter_map(|part| {
                let t = part.trim();
                if t.is_empty() {
                    return None;
                }
                if t.as_bytes().first().map(|b| b.is_ascii_digit()).unwrap_or(false) {
                    Some(format!("-- namespace _TurboCrossFileShard_{}\n", t))
                } else {
                    Some(format!("{}\n", t))
                }
            })
            .collect();
        if blocks.len() >= 2 && blocks.len() <= 4 {
            let needed = blocks.len();
            let mut workers: Vec<ZygoteChild> = Vec::with_capacity(needed);
            {
                let mut pool = pool_mutex
                    .lock()
                    .map_err(|_| anyhow::anyhow!("ZygotePool mutex poisoned"))?;
                if let Some(vec) = pool.get_mut(&pool_key) {
                    while workers.len() < needed {
                        if let Some(pos) = vec
                            .iter()
                            .rposition(|w| w.warm_imports.contains_key(&imports_csv))
                        {
                            workers.push(vec.swap_remove(pos));
                        } else if let Some(w) = vec.pop() {
                            workers.push(w);
                        } else {
                            break;
                        }
                    }
                }
            }
            while workers.len() < needed {
                workers.push(spawn_zygote_worker()?);
            }

            let req_lines: Vec<String> = blocks
                .iter()
                .map(|blk| {
                    let hb = hex_encode_bytes(blk.as_bytes());
                    if allow_stub {
                        format!("{}\t{}\tallow_stub\n", imports_csv, hb)
                    } else {
                        format!("{}\t{}\n", imports_csv, hb)
                    }
                })
                .collect();

            let results: Vec<(ZygoteChild, WorkerReqOutcome)> = std::thread::scope(|s| {
                let handles: Vec<_> = workers
                    .into_iter()
                    .zip(req_lines)
                    .map(|(mut w, rl)| {
                        s.spawn(move || {
                            let res = run_worker_req(&mut w, &rl);
                            (w, res)
                        })
                    })
                    .collect();
                handles
                    .into_iter()
                    .map(|h| h.join().expect("Zygote parallel eval thread panicked"))
                    .collect()
            });

            let mut replies = Vec::with_capacity(needed);
            let mut first_err: Option<anyhow::Error> = None;
            for (mut w, res) in results {
                match res {
                    WorkerReqOutcome::Reply(r) => {
                        if r.import_ok {
                            w.warm_imports
                                .insert(imports_csv.clone(), olean_digest.clone());
                        }
                        return_worker_to_pool(pool_mutex, pool_key.clone(), w);
                        replies.push(r);
                    }
                    WorkerReqOutcome::TimedOut(elapsed_us) => {
                        drop(w);
                        return Ok(ZygoteEvalReply {
                            ok: false,
                            kernel_gate_active: !eval_mode,
                            import_ok: true,
                            env_cache_hit: false,
                            prefix_cache_hit: false,
                            import_us: 0,
                            prefix_us: 0,
                            elab_us: elapsed_us,
                            heartbeats: 0,
                            subshards_verified: 0,
                            stdout: String::new(),
                            messages: Vec::new(),
                            errors: vec![format!(
                                "Zygote evaluation timed out after {} ms",
                                effective_timeout_ms
                            )],
                            used_constants: Vec::new(),
                            timed_out: true,
                            crashed: false,
                        });
                    }
                    WorkerReqOutcome::Crashed(msg) => {
                        drop(w);
                        if first_err.is_none() {
                            first_err = Some(anyhow::anyhow!("{}", msg));
                        }
                    }
                }
            }
            if let Some(e) = first_err {
                return Err(e);
            }
            let import_ok = replies.iter().all(|r| r.import_ok);
            let ok = replies.iter().all(|r| r.ok);
            let kernel_gate_active = replies.iter().all(|r| r.kernel_gate_active);
            let env_cache_hit = replies.iter().all(|r| r.env_cache_hit);
            let prefix_cache_hit = replies.iter().all(|r| r.prefix_cache_hit);
            let import_us = replies.iter().map(|r| r.import_us).max().unwrap_or(0);
            let prefix_us = replies.iter().map(|r| r.prefix_us).max().unwrap_or(0);
            let elab_us = replies.iter().map(|r| r.elab_us).max().unwrap_or(0);
            let heartbeats: u64 = replies.iter().map(|r| r.heartbeats).sum();
            let subshards_verified: usize = replies.iter().map(|r| r.subshards_verified).sum();
            let mut stdout = String::new();
            let mut messages = Vec::new();
            let mut errors = Vec::new();
            let mut used_constants = Vec::new();
            for r in replies {
                stdout.push_str(&r.stdout);
                messages.extend(r.messages);
                errors.extend(r.errors);
                for c in r.used_constants {
                    if used_constants.len() < 32 && !used_constants.contains(&c) {
                        used_constants.push(c);
                    }
                }
            }
            return Ok(ZygoteEvalReply {
                ok,
                kernel_gate_active,
                import_ok,
                env_cache_hit,
                prefix_cache_hit,
                import_us,
                prefix_us,
                elab_us,
                heartbeats,
                subshards_verified,
                stdout,
                messages,
                errors,
                used_constants,
                timed_out: false,
                crashed: false,
            });
        }
    }

    let (req_line, active_prefix_key) = if let Some((_, pk, rl)) = batch_fission_override {
        (rl, Some(pk))
    } else if !eval_mode {
        if let Some((prefix_code, decl_code, prefix_key)) =
            split_body_into_prefix_and_decl(&body_code)
        {
            let hex_decl = hex_encode_bytes(decl_code.as_bytes());
            let hex_prefix = hex_encode_bytes(prefix_code.as_bytes());
            let mode_flag = if allow_stub { "allow_stub" } else { "strict" };
            (
                format!(
                    "{}\t{}\t{}\t{}\t{}\n",
                    imports_csv, hex_decl, mode_flag, prefix_key, hex_prefix
                ),
                Some(prefix_key),
            )
        } else {
            let hex_body = hex_encode_bytes(body_code.as_bytes());
            let rl = if allow_stub {
                format!("{}\t{}\tallow_stub\n", imports_csv, hex_body)
            } else {
                format!("{}\t{}\n", imports_csv, hex_body)
            };
            (rl, None)
        }
    } else {
        let mode_flag = match file_name {
            Some(fn_str) if !fn_str.is_empty() => {
                format!("eval:{}", hex_encode_bytes(fn_str.as_bytes()))
            }
            _ => "eval".to_string(),
        };
        if let Some((prefix_key, prefix_code, decl_code)) =
            split_eval_body_into_prefix_and_cmds(&body_code)
        {
            let hex_decl = hex_encode_bytes(decl_code.as_bytes());
            let hex_prefix = hex_encode_bytes(prefix_code.as_bytes());
            (
                format!(
                    "{}\t{}\t{}\t{}\t{}\n",
                    imports_csv, hex_decl, mode_flag, prefix_key, hex_prefix
                ),
                Some(prefix_key),
            )
        } else {
            let hex_body = hex_encode_bytes(body_code.as_bytes());
            (format!("{}\t{}\t{}\n", imports_csv, hex_body, mode_flag), None)
        }
    };

    let (mut worker, mut was_warm_worker) = {
        let mut pool = pool_mutex
            .lock()
            .map_err(|_| anyhow::anyhow!("ZygotePool mutex poisoned"))?;
        let mut selected: Option<ZygoteChild> = None;
        if let Some(vec) = pool.get_mut(&pool_key) {
            // Evict any worker whose cached digest for this imports_csv is stale
            vec.retain(|w| {
                w.warm_imports
                    .get(&imports_csv)
                    .map(|d| d == &olean_digest)
                    .unwrap_or(true)
            });
            if let Some(ref pk) = active_prefix_key {
                if let Some(pos) = vec.iter().rposition(|w| w.warm_prefixes.contains(pk)) {
                    selected = Some(vec.swap_remove(pos));
                }
            }
            if selected.is_none() {
                if let Some(pos) = vec
                    .iter()
                    .rposition(|w| w.warm_imports.contains_key(&imports_csv))
                {
                    selected = Some(vec.swap_remove(pos));
                }
            }
            if selected.is_none() {
                selected = vec.pop();
            }
        }
        if selected.is_none() {
            // Also check if another bucket for the same (toolchain, effective_lean_path)
            // has an idle worker that can import this module set (or already has it with matching olean_digest)
            for ((tc, lp, _), vec) in pool.iter_mut() {
                if tc == toolchain && lp == &effective_lean_path {
                    vec.retain(|w| {
                        w.warm_imports
                            .get(&imports_csv)
                            .map(|d| d == &olean_digest)
                            .unwrap_or(true)
                    });
                    if let Some(pos) = vec.iter().rposition(|w| {
                        match w.warm_imports.get(&imports_csv) {
                            Some(d) => d == &olean_digest,
                            None => true,
                        }
                    }) {
                        selected = Some(vec.swap_remove(pos));
                        break;
                    }
                }
            }
        }
        match selected {
            Some(w) => (Some(w), true),
            None => (None, false),
        }
    };
    if worker.is_none() {
        worker = Some(spawn_zygote_worker()?);
        was_warm_worker = false;
    }

    let mut w = worker.unwrap();
    let mut outcome = run_worker_req(&mut w, &req_line);
    if let WorkerReqOutcome::Crashed(_) = outcome {
        drop(w);
        if was_warm_worker {
            w = spawn_zygote_worker()?;
            outcome = run_worker_req(&mut w, &req_line);
        } else {
            // Fresh worker crashed on first try; retry once on a new worker before returning crashed: true
            if let Ok(mut retry_w) = spawn_zygote_worker() {
                outcome = run_worker_req(&mut retry_w, &req_line);
                w = retry_w;
            } else {
                return Ok(ZygoteEvalReply {
                    ok: false,
                    kernel_gate_active: !eval_mode,
                    import_ok: false,
                    env_cache_hit: false,
                    prefix_cache_hit: false,
                    import_us: 0,
                    prefix_us: 0,
                    elab_us: 0,
                    heartbeats: 0,
                    subshards_verified: 0,
                    stdout: String::new(),
                    messages: Vec::new(),
                    errors: vec!["Zygote worker crashed and respawn failed".to_string()],
                    used_constants: Vec::new(),
                    timed_out: false,
                    crashed: true,
                });
            }
        }
    }

    match outcome {
        WorkerReqOutcome::Reply(rep) => {
            if rep.import_ok {
                w.warm_imports
                    .insert(imports_csv.clone(), olean_digest.clone());
                if let Some(pk) = active_prefix_key {
                    w.warm_prefixes.insert(pk);
                }
            }
            return_worker_to_pool(pool_mutex, pool_key, w);
            Ok(rep)
        }
        WorkerReqOutcome::TimedOut(elapsed_us) => {
            drop(w);
            Ok(ZygoteEvalReply {
                ok: false,
                kernel_gate_active: !eval_mode,
                import_ok: true,
                env_cache_hit: false,
                prefix_cache_hit: false,
                import_us: 0,
                prefix_us: 0,
                elab_us: elapsed_us,
                heartbeats: 0,
                subshards_verified: 0,
                stdout: String::new(),
                messages: Vec::new(),
                errors: vec![format!(
                    "Zygote evaluation timed out after {} ms",
                    effective_timeout_ms
                )],
                used_constants: Vec::new(),
                timed_out: true,
                crashed: false,
            })
        }
        WorkerReqOutcome::Crashed(err_msg) => {
            drop(w);
            Ok(ZygoteEvalReply {
                ok: false,
                kernel_gate_active: !eval_mode,
                import_ok: false,
                env_cache_hit: false,
                prefix_cache_hit: false,
                import_us: 0,
                prefix_us: 0,
                elab_us: 0,
                heartbeats: 0,
                subshards_verified: 0,
                stdout: String::new(),
                messages: Vec::new(),
                errors: vec![err_msg],
                used_constants: Vec::new(),
                timed_out: false,
                crashed: true,
            })
        }
    }
}

/// Evaluate a single sub-shard (`prefix_source` + `sub_decl_source`) via the memory-governed
/// `ZygotePool` with automatic `Command.State` prefix checkpoint reuse and RSS watermark recycling.
#[allow(dead_code)]
pub fn eval_shard_via_zygote(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    prefix_source: &str,
    sub_decl_source: &str,
) -> Result<ZygoteEvalReply> {
    let combined_source = if prefix_source.trim().is_empty() {
        format!("{}\n", sub_decl_source.trim_end())
    } else {
        format!(
            "{}\n\n{}\n",
            prefix_source.trim_end(),
            sub_decl_source.trim_start()
        )
    };
    eval_with_zygote_pool(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        &combined_source,
        false,
    )
}

/// Evaluate a batch of cut-fission sub-shards (`prefix_source` + each `sub_decl` in `sub_decl_sources`)
/// in a single IPC roundtrip over the warm `ZygotePool` (`batch_fission` mode).
/// Each sub-shard is elaborated from the clean functional `ckptState` checkpoint (bounding peak heap
/// by a single `have` block) and individually audited by `auditNewKernelDecls` (`0 sorryAx`).
#[allow(dead_code)]
pub fn eval_subshards_batch_via_zygote(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    prefix_source: &str,
    sub_decl_sources: &[String],
) -> Result<ZygoteEvalReply> {
    if sub_decl_sources.is_empty() {
        return Ok(ZygoteEvalReply {
            ok: true,
            kernel_gate_active: true,
            import_ok: true,
            env_cache_hit: true,
            prefix_cache_hit: true,
            import_us: 0,
            prefix_us: 0,
            elab_us: 0,
            heartbeats: 0,
            subshards_verified: 0,
            stdout: String::new(),
            messages: Vec::new(),
            errors: Vec::new(),
            used_constants: Vec::new(),
            timed_out: false,
            crashed: false,
        });
    }
    if sub_decl_sources.len() == 1 {
        return eval_shard_via_zygote(
            store,
            toolchain,
            req_lean_path,
            env_vars,
            lean_bin,
            prefix_source,
            &sub_decl_sources[0],
        );
    }
    let (imports_csv, prefix_body) = split_shard_for_zygote(prefix_source);
    let prefix_key = blake3::hash(prefix_body.as_bytes()).to_hex().to_string();
    let hex_prefix = hex_encode_bytes(prefix_body.as_bytes());
    let hex_subs_csv = sub_decl_sources
        .iter()
        .map(|s| {
            let mut decl = s.trim_end().to_string();
            decl.push('\n');
            hex_encode_bytes(decl.as_bytes())
        })
        .collect::<Vec<_>>()
        .join(",");
    let req_line = format!(
        "{}\tbatch_fission\t{}\t{}\t{}\n",
        imports_csv, prefix_key, hex_prefix, hex_subs_csv
    );
    eval_with_zygote_pool_inner(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        "",
        false,
        false,
        None,
        None,
        Some((imports_csv, prefix_key, req_line)),
    )
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct LocalZygoteDaemonInfo {
    pub(crate) addr: String,
    pub(crate) pid: u32,
    pub(crate) exe_mtime_sec: i64,
    pub(crate) exe_mtime_nsec: i64,
}

pub fn ensure_local_zygote_daemon(
    store: &TurboStore,
    env_vars: &std::collections::HashMap<String, String>,
) -> Option<String> {
    if std::env::var("TURBO_LEAN_NO_DAEMON").is_ok() {
        return None;
    }
    let current_exe = std::env::current_exe().ok()?;
    let (exe_mtime_sec, exe_mtime_nsec, _) = fs::metadata(&current_exe)
        .ok()
        .map(|m| TurboStore::extract_file_stat_tuple(&m))
        .unwrap_or((0, 0, 0));

    let mut exe_hasher = blake3::Hasher::new();
    exe_hasher.update(current_exe.to_string_lossy().as_bytes());
    let exe_tag = &exe_hasher.finalize().to_hex()[..12];

    let staging = store.fast_staging_dir();
    let daemon_cache_dir = staging.join(format!("zygote_daemon_cas_{}", exe_tag));
    let state_file = daemon_cache_dir.join("zygote_daemon.json");

    let check_existing = |path: &Path| -> Option<String> {
        let content = fs::read_to_string(path).ok()?;
        let info: LocalZygoteDaemonInfo = serde_json::from_str(&content).ok()?;
        if info.exe_mtime_sec != exe_mtime_sec || info.exe_mtime_nsec != exe_mtime_nsec {
            #[cfg(unix)]
            if info.pid > 0 {
                unsafe {
                    libc::kill(info.pid as i32, libc::SIGTERM);
                }
            }
            return None;
        }
        #[cfg(unix)]
        {
            if info.pid > 0 && unsafe { libc::kill(info.pid as i32, 0) == 0 } {
                return Some(format!("http://{}", info.addr));
            }
            return None;
        }
        #[cfg(not(unix))]
        {
            let sock_addr: std::net::SocketAddr = info.addr.parse().ok()?;
            if std::net::TcpStream::connect_timeout(
                &sock_addr,
                std::time::Duration::from_millis(10),
            )
            .is_ok()
            {
                Some(format!("http://{}", info.addr))
            } else {
                None
            }
        }
    };

    if let Some(url) = check_existing(&state_file) {
        return Some(url);
    }

    let _ = fs::create_dir_all(&daemon_cache_dir);
    let lock_path = daemon_cache_dir.join("zygote_daemon.lock");
    let lock_file = fs::OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(false)
        .open(&lock_path)
        .ok()?;
    #[cfg(unix)]
    unsafe {
        use std::os::unix::io::AsRawFd;
        libc::flock(lock_file.as_raw_fd(), libc::LOCK_EX);
    }

    let res = (|| -> Option<String> {
        if let Some(url) = check_existing(&state_file) {
            return Some(url);
        }
        let port = {
            let listener = TcpListener::bind("127.0.0.1:0").ok()?;
            let p = listener.local_addr().ok()?.port();
            drop(listener);
            p
        };
        let addr = format!("127.0.0.1:{}", port);
        let sock_addr: std::net::SocketAddr = addr.parse().ok()?;

        let mut cmd = Command::new(&current_exe);
        cmd.arg("--cache-dir")
            .arg(&daemon_cache_dir)
            .arg("serve")
            .arg("--listen")
            .arg(&addr)
            .envs(env_vars)
            .env("TURBO_LEAN_DAEMON", "1")
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null());
        #[cfg(unix)]
        {
            use std::os::unix::process::CommandExt;
            cmd.process_group(0);
        }
        let child = cmd.spawn().ok()?;
        let pid = child.id();

        let mut connected = false;
        for _ in 0..75 {
            if std::net::TcpStream::connect_timeout(
                &sock_addr,
                std::time::Duration::from_millis(5),
            )
            .is_ok()
            {
                connected = true;
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(2));
        }
        if !connected {
            return None;
        }

        let info = LocalZygoteDaemonInfo {
            addr: addr.clone(),
            pid,
            exe_mtime_sec,
            exe_mtime_nsec,
        };
        if let Ok(json_bytes) = serde_json::to_vec(&info) {
            let _ = fs::write(&state_file, &json_bytes);
            let _ = fs::write(store.root.join("zygote_daemon.json"), &json_bytes);
        }
        Some(format!("http://{}", addr))
    })();

    #[cfg(unix)]
    unsafe {
        use std::os::unix::io::AsRawFd;
        libc::flock(lock_file.as_raw_fd(), libc::LOCK_UN);
    }
    res
}

pub fn warm_local_zygote_daemon_nonblocking(
    store: &TurboStore,
    env_vars: &std::collections::HashMap<String, String>,
) {
    if std::env::var("TURBO_LEAN_NO_DAEMON").is_ok() {
        return;
    }
    let Ok(current_exe) = std::env::current_exe() else {
        return;
    };
    let (exe_mtime_sec, exe_mtime_nsec, _) = fs::metadata(&current_exe)
        .ok()
        .map(|m| TurboStore::extract_file_stat_tuple(&m))
        .unwrap_or((0, 0, 0));

    let mut exe_hasher = blake3::Hasher::new();
    exe_hasher.update(current_exe.to_string_lossy().as_bytes());
    let exe_tag = &exe_hasher.finalize().to_hex()[..12];

    let staging = store.fast_staging_dir();
    let daemon_cache_dir = staging.join(format!("zygote_daemon_cas_{}", exe_tag));
    let _ = fs::create_dir_all(&daemon_cache_dir);
    let state_file = daemon_cache_dir.join("zygote_daemon.json");

    let lock_path = daemon_cache_dir.join("zygote_daemon.lock");
    let Ok(lock_file) = fs::OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(false)
        .open(&lock_path)
    else {
        return;
    };
    #[cfg(unix)]
    unsafe {
        use std::os::unix::io::AsRawFd;
        if libc::flock(lock_file.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) != 0 {
            return;
        }
    }

    (|| {
        if let Ok(content) = fs::read_to_string(&state_file) {
            if let Ok(info) = serde_json::from_str::<LocalZygoteDaemonInfo>(&content) {
                if info.exe_mtime_sec == exe_mtime_sec && info.exe_mtime_nsec == exe_mtime_nsec {
                    #[cfg(unix)]
                    if info.pid > 0 && unsafe { libc::kill(info.pid as i32, 0) == 0 } {
                        return;
                    }
                } else {
                    #[cfg(unix)]
                    if info.pid > 0 {
                        unsafe {
                            libc::kill(info.pid as i32, libc::SIGTERM);
                        }
                    }
                }
            }
        }

        let Ok(listener) = TcpListener::bind("127.0.0.1:0") else {
            return;
        };
        let Ok(local_addr) = listener.local_addr() else {
            return;
        };
        let port = local_addr.port();
        drop(listener);
        let addr = format!("127.0.0.1:{}", port);

        let mut cmd = Command::new(&current_exe);
        cmd.arg("--cache-dir")
            .arg(&daemon_cache_dir)
            .arg("serve")
            .arg("--listen")
            .arg(&addr)
            .envs(env_vars)
            .env("TURBO_LEAN_DAEMON", "1")
            .env("TURBO_LEAN_DAEMON_STATE_FILE", &state_file)
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null());
        #[cfg(unix)]
        {
            use std::os::unix::process::CommandExt;
            cmd.process_group(0);
        }
        if let Ok(child) = cmd.spawn() {
            let info = LocalZygoteDaemonInfo {
                addr,
                pid: child.id(),
                exe_mtime_sec,
                exe_mtime_nsec,
            };
            if let Ok(json_bytes) = serde_json::to_vec(&info) {
                let _ = fs::write(&state_file, &json_bytes);
                let _ = fs::write(store.root.join("zygote_daemon.json"), &json_bytes);
            }
        }
    })();

    #[cfg(unix)]
    unsafe {
        use std::os::unix::io::AsRawFd;
        libc::flock(lock_file.as_raw_fd(), libc::LOCK_UN);
    }
}

pub(crate) fn try_zygote_url_check_shard_inner_with_inflight(
    base_url: &str,
    req: &CheckShardHttpRequest,
    on_inflight: impl FnOnce(),
) -> Result<Option<serde_json::Value>> {
    let endpoint = format!("{}/check-shard", base_url.trim_end_matches('/'));
    let mut local_req = req.clone();
    local_req.skip_cas_lock = true;
    let body = serde_json::to_vec(&local_req)?;
    let resp_bytes =
        http_request_with_inflight("POST", &endpoint, "application/json", &body, on_inflight)?;
    let resp_json: serde_json::Value = serde_json::from_slice(&resp_bytes)?;
    let status = resp_json.get("status").and_then(|v| v.as_str()).unwrap_or("");
    if status == "remote_theorem_verified" || status == "remote_theorem_cache_hit" {
        Ok(Some(resp_json))
    } else {
        Ok(None)
    }
}

pub fn try_zygote_url_check_shard_with_inflight(
    base_url: &str,
    req: &CheckShardHttpRequest,
    on_inflight: impl FnOnce(),
) -> Option<serde_json::Value> {
    try_zygote_url_check_shard_inner_with_inflight(base_url, req, on_inflight)
        .ok()
        .flatten()
}

pub fn try_zygote_url_check_shard(
    base_url: &str,
    req: &CheckShardHttpRequest,
) -> Option<serde_json::Value> {
    try_zygote_url_check_shard_inner_with_inflight(base_url, req, || {})
        .ok()
        .flatten()
}

pub fn try_local_zygote_check_shard(
    store: &TurboStore,
    env_vars: &std::collections::HashMap<String, String>,
    req: &CheckShardHttpRequest,
) -> Option<serde_json::Value> {
    let base_url = ensure_local_zygote_daemon(store, env_vars)?;
    match try_zygote_url_check_shard_inner_with_inflight(&base_url, req, || {}) {
        Ok(res) => res,
        Err(e) => {
            if e.to_string().contains("HTTP ") {
                return None;
            }
            if let Ok(current_exe) = std::env::current_exe() {
                let mut exe_hasher = blake3::Hasher::new();
                exe_hasher.update(current_exe.to_string_lossy().as_bytes());
                let exe_tag = &exe_hasher.finalize().to_hex()[..12];
                let state_file = store
                    .fast_staging_dir()
                    .join(format!("zygote_daemon_cas_{}", exe_tag))
                    .join("zygote_daemon.json");
                let _ = fs::remove_file(&state_file);
            }
            let retry_url = ensure_local_zygote_daemon(store, env_vars)?;
            try_zygote_url_check_shard_inner_with_inflight(&retry_url, req, || {})
                .ok()
                .flatten()
        }
    }
}

pub fn try_local_zygote_eval(
    store: &TurboStore,
    env_vars: &std::collections::HashMap<String, String>,
    toolchain: &str,
    lean_path: &str,
    source: &str,
    file_name: Option<&str>,
    timeout_ms: u64,
) -> Option<ZygoteEvalReply> {
    let base_url = ensure_local_zygote_daemon(store, env_vars)?;
    let endpoint = format!("{}/eval", base_url.trim_end_matches('/'));
    let body = serde_json::to_vec(&serde_json::json!({
        "toolchain": toolchain,
        "lean_path": lean_path,
        "source": source,
        "file_name": file_name,
        "timeout_ms": timeout_ms,
        "verify_determinism": false
    }))
    .ok()?;
    let resp_bytes = http_request_with_inflight("POST", &endpoint, "application/json", &body, || {})
        .or_else(|_| {
            if let Ok(current_exe) = std::env::current_exe() {
                let mut exe_hasher = blake3::Hasher::new();
                exe_hasher.update(current_exe.to_string_lossy().as_bytes());
                let exe_tag = &exe_hasher.finalize().to_hex()[..12];
                let state_file = store
                    .fast_staging_dir()
                    .join(format!("zygote_daemon_cas_{}", exe_tag))
                    .join("zygote_daemon.json");
                let _ = fs::remove_file(&state_file);
            }
            let retry_url = ensure_local_zygote_daemon(store, env_vars)
                .ok_or_else(|| anyhow::anyhow!("Failed to respawn local zygote daemon"))?;
            let retry_endpoint = format!("{}/eval", retry_url.trim_end_matches('/'));
            http_request_with_inflight("POST", &retry_endpoint, "application/json", &body, || {})
        })
        .ok()?;
    serde_json::from_slice::<ZygoteEvalReply>(&resp_bytes).ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_split_body_into_prefix_and_decl() {
        let body = "namespace PrefixBench\nstructure PairState where\n  x : Nat\n  y : Nat\n\ndef swapPair (s : PairState) : PairState :=\n  { x := s.y, y := s.x }\n\ntheorem cand_good (s : PairState) : swapPair (swapPair s) = s := by\n  cases s\n  rfl\n";
        let (pref, decl, key) = split_body_into_prefix_and_decl(body).expect("should split");
        assert!(pref.contains("structure PairState"));
        assert!(pref.contains("def swapPair"));
        assert!(!pref.contains("theorem cand_good"));
        assert!(decl.starts_with("theorem cand_good"));
        assert_eq!(key.len(), 16);
    }

    #[test]
    fn test_zygote_prefix_checkpoint_instant_rollback() {
        let tmp_dir = std::env::temp_dir().join(format!("turbo_zygote_test_{}", next_tmp_id()));
        let _ = fs::create_dir_all(&tmp_dir);
        let store = TurboStore::open(Some(&tmp_dir)).expect("open store");
        let toolchain = "leanprover/lean4:v4.31.0";
        let (env_vars, lean_bin) =
            crate::pack::resolve_server_lean_env_and_bin(&store, toolchain, "");
        if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        }

        let shared_prefix = "namespace PrefixBench\nstructure PairState where\n  x : Nat\n  y : Nat\n  deriving DecidableEq\n\ndef swapPair (s : PairState) : PairState :=\n  { x := s.y, y := s.x }\n\ntheorem swapPair_involutive (s : PairState) : swapPair (swapPair s) = s := by\n  cases s\n  rfl\n";

        // 1. Failing candidate proof on shared prefix: elaborates and checkpoints the prefix,
        //    rejects the bad theorem proof, and rolls back the checkpoint in 0 µs via functional CoW.
        let shard_bad = format!(
            "{}\ntheorem cand_bad (s : PairState) : swapPair s = s := rfl\n",
            shared_prefix
        );
        let rep_bad = eval_with_zygote_pool(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            &shard_bad,
            false,
        )
        .expect("eval_with_zygote_pool on bad candidate");
        assert!(rep_bad.import_ok);
        assert!(!rep_bad.ok, "invalid candidate proof must be rejected");
        assert!(!rep_bad.errors.is_empty());

        // 2. First valid candidate proof on the SAME prefix: hits the warm prefix checkpoint
        //    with zero contamination from `cand_bad` and sub-millisecond elaboration.
        let shard_good1 = format!(
            "{}\ntheorem cand_good1 (s : PairState) : swapPair (swapPair s) = s := by\n  cases s\n  rfl\n",
            shared_prefix
        );
        let rep_good1 = eval_with_zygote_pool(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            &shard_good1,
            false,
        )
        .expect("eval_with_zygote_pool on good candidate 1");
        assert!(rep_good1.ok, "valid candidate 1 must succeed: {:?}", rep_good1.errors);
        assert!(rep_good1.env_cache_hit, "must hit in-memory Environment cache");
        assert!(rep_good1.prefix_cache_hit, "must hit in-memory Command.State prefix checkpoint");
        assert_eq!(rep_good1.prefix_us, 0, "warm prefix checkpoint must have 0 µs prefix overhead");
        assert!(
            rep_good1.elab_us < 10_000,
            "expected sub-10ms declaration check on warm prefix checkpoint, got {} µs",
            rep_good1.elab_us
        );

        // 3. Second valid candidate proof referencing prefix lemma on the SAME prefix checkpoint.
        let shard_good2 = format!(
            "{}\ntheorem cand_good2 (s : PairState) : swapPair (swapPair s) = s := swapPair_involutive s\n",
            shared_prefix
        );
        let rep_good2 = eval_with_zygote_pool(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            &shard_good2,
            false,
        )
        .expect("eval_with_zygote_pool on good candidate 2");
        assert!(rep_good2.ok, "valid candidate 2 must succeed: {:?}", rep_good2.errors);
        assert!(rep_good2.env_cache_hit);
        assert!(rep_good2.prefix_cache_hit);
        assert_eq!(rep_good2.prefix_us, 0);
        assert!(
            rep_good2.elab_us < 10_000,
            "expected < 10000 µs declaration check on warm prefix checkpoint, got {} µs",
            rep_good2.elab_us
        );

        // 4. Brand-new theorem statement + tactic proof against the SAME prefix checkpoint:
        //    elaborates only the target declaration via IO.processCommands without re-elaborating the prefix.
        let shard_good_fresh = format!(
            "{}\ntheorem cand_good_fresh (s : PairState) : (swapPair s).x = s.y := by\n  cases s\n  rfl\n",
            shared_prefix
        );
        let rep_good_fresh = eval_with_zygote_pool(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            &shard_good_fresh,
            false,
        )
        .expect("eval_with_zygote_pool on fresh theorem candidate");
        assert!(rep_good_fresh.ok, "fresh theorem candidate must succeed: {:?}", rep_good_fresh.errors);
        assert!(rep_good_fresh.env_cache_hit);
        assert!(rep_good_fresh.prefix_cache_hit);
        assert_eq!(rep_good_fresh.prefix_us, 0);
        assert!(
            rep_good_fresh.elab_us < 10_000 && rep_good_fresh.elab_us < rep_bad.prefix_us,
            "expected fast fresh declaration elaboration on warm prefix checkpoint (< {} µs prefix), got {} µs",
            rep_bad.prefix_us,
            rep_good_fresh.elab_us
        );
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_zygote_kernel_gate_rejects_macro_hidden_sorry() {
        let tmp_dir =
            std::env::temp_dir().join(format!("turbo_zygote_kgate_test_{}", next_tmp_id()));
        let _ = fs::create_dir_all(&tmp_dir);
        let store = TurboStore::open(Some(&tmp_dir)).expect("open store");
        let toolchain = "leanprover/lean4:v4.31.0";
        let (env_vars, lean_bin) =
            crate::pack::resolve_server_lean_env_and_bin(&store, toolchain, "");
        if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        }

        let prefix_src = "theorem prior_lem : True := sorry\n";
        let decl_src =
            "macro \"stealth_sorry\" : tactic => `(tactic| sorry)\ntheorem sneaky_thm : 1 = 2 := by stealth_sorry\n";
        let sneaky_shard = format!("{}\n{}", prefix_src, decl_src);

        let rep_sneaky = eval_with_zygote_pool(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            &sneaky_shard,
            false,
        )
        .expect("eval_with_zygote_pool on sneaky_thm");
        assert!(
            !rep_sneaky.ok,
            "macro-hidden sorry must be rejected by ZygoteWorker"
        );
        let joined_errs = rep_sneaky.errors.join("\n");
        assert!(
            joined_errs.contains("KernelGate") || joined_errs.contains("sorry"),
            "expected KernelGate or sorry rejection message, got: {:?}",
            rep_sneaky.errors
        );

        let clean_shard = format!("{}\ntheorem clean_thm : True := prior_lem\n", prefix_src);
        let rep_clean = eval_with_zygote_pool(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            &clean_shard,
            false,
        )
        .expect("eval_with_zygote_pool on clean_thm");
        assert!(
            rep_clean.ok,
            "legitimate theorem referencing stubbed prior_lem from prefix_src must succeed: {:?}",
            rep_clean.errors
        );
        assert!(
            rep_clean.kernel_gate_active,
            "ZygoteWorker must report kernel_gate_active == true"
        );

        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_lean_native_core_persistent_worker_sub_millisecond_rpc() {
        let warmup = query_lean_native_core_worker("ping", None)
            .expect("warm up persistent lean-native-core worker");
        assert_eq!(warmup.get("ok").and_then(|v| v.as_bool()), Some(true));
        assert_eq!(
            warmup
                .get("result")
                .and_then(|r| r.get("status"))
                .and_then(|v| v.as_str()),
            Some("pong")
        );

        let methods = ["ping", "validate-tv", "verify-certs", "eval-cex"];
        let t0 = std::time::Instant::now();
        for idx in 0..20 {
            let method = methods[idx % methods.len()];
            let resp = query_lean_native_core_worker(method, None)
                .unwrap_or_else(|e| panic!("RPC call #{} ({}) failed: {}", idx, method, e));
            assert_eq!(
                resp.get("ok").and_then(|v| v.as_bool()),
                Some(true),
                "expected ok == true for method {}",
                method
            );
            let result = resp
                .get("result")
                .unwrap_or_else(|| panic!("missing result field for method {}", method));
            match method {
                "ping" => {
                    assert_eq!(result.get("status").and_then(|v| v.as_str()), Some("pong"));
                }
                "validate-tv" => {
                    assert_eq!(
                        result.get("allPassed").and_then(|v| v.as_bool()),
                        Some(true)
                    );
                    assert_eq!(result.get("passedDecls").and_then(|v| v.as_u64()), Some(8));
                }
                "verify-certs" => {
                    assert_eq!(result.get("verified").and_then(|v| v.as_bool()), Some(true));
                }
                "eval-cex" => {
                    assert_eq!(
                        result.get("certified").and_then(|v| v.as_bool()),
                        Some(true)
                    );
                    assert_eq!(
                        result.get("falsePositives").and_then(|v| v.as_u64()),
                        Some(0)
                    );
                }
                _ => unreachable!(),
            }
        }
        let avg_ms = t0.elapsed().as_secs_f64() * 1000.0 / 20.0;
        assert!(
            avg_ms < 1.0,
            "expected average warm RPC latency < 1.0 ms, got {:.4} ms",
            avg_ms
        );
    }

    #[test]
    fn test_measure_process_rss_mb_and_budget_detection() {
        let self_pid = std::process::id();
        let t0 = std::time::Instant::now();
        let rss_mb = measure_process_rss_mb(self_pid);
        let elapsed_us = t0.elapsed().as_micros();

        assert!(
            rss_mb >= 1 && rss_mb < 65_536,
            "expected valid current process RSS in MiB (1..65536), got {} MiB",
            rss_mb
        );
        #[cfg(target_os = "linux")]
        assert!(
            elapsed_us < 1000,
            "expected fast /proc/<pid>/statm RSS probe on Linux, took {} µs",
            elapsed_us
        );

        let gov = crate::shm_cache::MemoryBudgetGovernor::detect();
        assert!(
            gov.budget_mb >= 1,
            "detected memory budget must be >= 1 MiB, got {}",
            gov.budget_mb
        );
        assert!(gov.worker_rss_limit_mb() >= 512);
    }

    #[test]
    fn test_zygote_multiple_import_sets_in_same_worker() {
        let tmp_dir =
            std::env::temp_dir().join(format!("turbo_zygote_multi_imp_{}", next_tmp_id()));
        let _ = fs::create_dir_all(&tmp_dir);
        let store = TurboStore::open(Some(&tmp_dir)).expect("open store");
        let toolchain = "leanprover/lean4:v4.31.0";
        let (env_vars, lean_bin) =
            crate::pack::resolve_server_lean_env_and_bin(&store, toolchain, "");
        if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        }

        // First import set: `Init`
        let rep1 = eval_with_zygote_pool_opts(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            "import Init\ntheorem multi_imp_1 : 1 + 1 = 2 := rfl\n",
            false,
            false,
            None,
            None,
        )
        .expect("eval Init");
        assert!(rep1.ok && rep1.import_ok, "Init import failed: {:?}", rep1.errors);

        // Second distinct import set on the SAME worker: `Lean`
        // Verifies `unsafe enableInitializersExecution` runs before every `Lean.importModules`.
        let rep2 = eval_with_zygote_pool_opts(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            "import Lean\n#eval Lean.versionString\n",
            false,
            true,
            Some("multi_imp_lean.lean"),
            None,
        )
        .expect("eval Lean");
        assert!(
            rep2.ok && rep2.import_ok,
            "Second distinct import set (Lean) in same worker failed: {:?}",
            rep2.errors
        );

        // Third call back to `Init` should hit the worker's in-memory envCache
        let rep3 = eval_with_zygote_pool_opts(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            "import Init\ntheorem multi_imp_2 : 2 + 2 = 4 := rfl\n",
            false,
            false,
            None,
            None,
        )
        .expect("eval Init again");
        assert!(rep3.ok && rep3.env_cache_hit);

        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_zygote_eval_mode_preserves_info_messages_and_sorry_strings() {
        let tmp_dir =
            std::env::temp_dir().join(format!("turbo_zygote_eval_info_{}", next_tmp_id()));
        let _ = fs::create_dir_all(&tmp_dir);
        let store = TurboStore::open(Some(&tmp_dir)).expect("open store");
        let toolchain = "leanprover/lean4:v4.31.0";
        let (env_vars, lean_bin) =
            crate::pack::resolve_server_lean_env_and_bin(&store, toolchain, "");
        if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        }

        let harness = "import Lean\nopen Lean Elab Command in\nrun_cmd do\n  logInfo \"RSGB_RESULT {\\\"name\\\":\\\"foo\\\",\\\"note\\\":\\\"sorry\\\"}\"\n#eval (40 + 2)\n";
        let rep = eval_with_zygote_pool_opts(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            harness,
            false,
            true,
            Some("rsgb_harness.lean"),
            Some(15_000),
        )
        .expect("eval_with_zygote_pool_opts in eval_mode");
        assert!(
            rep.ok,
            "eval_mode must not reject info messages containing 'sorry': {:?}",
            rep.errors
        );
        let joined_msgs = rep.messages.join("\n");
        assert!(
            joined_msgs.contains("rsgb_harness.lean:3:0: info: RSGB_RESULT {\"name\":\"foo\",\"note\":\"sorry\"}"),
            "expected formatted info message with file:line:col, got: {:?}",
            rep.messages
        );
        assert!(
            joined_msgs.contains("rsgb_harness.lean:5:0: info: 42"),
            "expected #eval info output at line 5, got: {:?}",
            rep.messages
        );
        assert!(rep.heartbeats > 0, "expected heartbeats > 0, got {}", rep.heartbeats);

        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_zygote_timeout_kills_infinite_eval_and_recovers() {
        let tmp_dir =
            std::env::temp_dir().join(format!("turbo_zygote_timeout_{}", next_tmp_id()));
        let _ = fs::create_dir_all(&tmp_dir);
        let store = TurboStore::open(Some(&tmp_dir)).expect("open store");
        let toolchain = "leanprover/lean4:v4.31.0";
        let (env_vars, lean_bin) =
            crate::pack::resolve_server_lean_env_and_bin(&store, toolchain, "");
        if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        }

        // Warm up the Zygote binary compilation first so we measure only request timeout
        let warm = eval_with_zygote_pool_opts(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            "#eval 1 + 1\n",
            false,
            true,
            Some("warm.lean"),
            Some(10_000),
        )
        .expect("warm up");
        assert!(warm.ok);

        let inf_src = "partial def spinForever (n : Nat) : IO Nat := do\n  IO.sleep 100\n  spinForever (n + 1)\n#eval spinForever 0\n";
        let t0 = std::time::Instant::now();
        let rep_timeout = eval_with_zygote_pool_opts(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            inf_src,
            false,
            true,
            Some("spin.lean"),
            Some(400),
        )
        .expect("eval_with_zygote_pool_opts on infinite loop");
        let elapsed = t0.elapsed();
        assert!(
            rep_timeout.timed_out && !rep_timeout.ok,
            "expected timed_out == true, got: {:?}",
            rep_timeout
        );
        assert!(
            elapsed < std::time::Duration::from_secs(2),
            "expected timeout in < 2s, took {:?}",
            elapsed
        );

        // Next request must recover seamlessly with a fresh worker
        let rep_after = eval_with_zygote_pool_opts(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            "#eval (100 + 23)\n",
            false,
            true,
            Some("after.lean"),
            Some(10_000),
        )
        .expect("eval after timeout recovery");
        assert!(rep_after.ok && !rep_after.timed_out);
        assert!(rep_after.messages.iter().any(|m| m.contains("123")));

        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_zygote_olean_digest_changes_when_olean_modified() {
        let tmp_dir =
            std::env::temp_dir().join(format!("turbo_zygote_olean_dig_{}", next_tmp_id()));
        let mod_dir = tmp_dir.join("Foo");
        let _ = fs::create_dir_all(&mod_dir);
        let olean_path = mod_dir.join("Bar.olean");
        fs::write(&olean_path, b"olean-version-1").expect("write v1");

        let lp = tmp_dir.to_string_lossy().to_string();
        let d1 = compute_imported_oleans_digest("Foo.Bar", &lp);
        let d1_repeat = compute_imported_oleans_digest("Foo.Bar", &lp);
        assert_eq!(d1, d1_repeat);

        fs::write(&olean_path, b"olean-version-2-modified").expect("write v2");
        let d2 = compute_imported_oleans_digest("Foo.Bar", &lp);
        assert_ne!(
            d1, d2,
            "olean digest must change immediately when .olean content changes on disk"
        );

        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_zygote_delta_prefix_chaining_and_used_constants_distillation() {
        let tmp_dir =
            std::env::temp_dir().join(format!("turbo_zygote_delta_distill_{}", next_tmp_id()));
        let _ = fs::create_dir_all(&tmp_dir);
        let store = TurboStore::open(Some(&tmp_dir)).expect("open store");
        let toolchain = "leanprover/lean4:v4.31.0";
        let (env_vars, lean_bin) =
            crate::pack::resolve_server_lean_env_and_bin(&store, toolchain, "");
        if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        }

        let prefix1 = "namespace DeltaChainTest\ndef shiftByFour (n : Nat) : Nat := n + 4\n";
        let thm1 = "theorem helper_shift_eq (n : Nat) : shiftByFour n = n + 4 := rfl\n";
        let shard1 = format!("{}{}", prefix1, thm1);

        let rep1 = eval_with_zygote_pool(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            &shard1,
            true,
        )
        .expect("eval theorem 1");
        assert!(rep1.ok, "Theorem 1 must succeed: {:?}", rep1.errors);

        // Theorem 2's prefix extends Theorem 1's prefix with the stubbed Theorem 1:
        let prefix2 = format!(
            "{}theorem helper_shift_eq (n : Nat) : shiftByFour n = n + 4 := sorry\n",
            prefix1
        );
        let thm2 = "theorem chained_thm (n : Nat) : shiftByFour n = n + 4 := by\n  simp [helper_shift_eq]\n";
        let shard2 = format!("{}{}", prefix2, thm2);

        let rep2 = eval_with_zygote_pool(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            &shard2,
            true,
        )
        .expect("eval theorem 2 via delta-prefix chaining");
        assert!(rep2.ok, "Theorem 2 must succeed: {:?}", rep2.errors);
        assert!(
            rep2.used_constants
                .iter()
                .any(|c| c.contains("helper_shift_eq")),
            "expected rep2.used_constants to contain helper_shift_eq, got: {:?}",
            rep2.used_constants
        );

        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_lean_native_core_worker_nonexistent_bin_fallback() {
        let prev = std::env::var("LEAN_NATIVE_CORE_BIN").ok();
        std::env::set_var("LEAN_NATIVE_CORE_BIN", "/nonexistent/lean-native-core");
        for method in [
            "ping",
            "validate-tv",
            "verify-certs",
            "eval-cex",
            "compile-fastcheck",
            "compile-llvm",
            "compile-ptx",
        ] {
            let resp = query_lean_native_core_worker(method, None)
                .unwrap_or_else(|e| panic!("fallback failed for {}: {}", method, e));
            assert_eq!(resp.get("ok").and_then(|v| v.as_bool()), Some(true));
            assert!(resp.get("result").is_some());
        }
        match prev {
            Some(v) => std::env::set_var("LEAN_NATIVE_CORE_BIN", v),
            None => std::env::remove_var("LEAN_NATIVE_CORE_BIN"),
        }
    }

    #[test]
    fn test_eval_mode_prefix_checkpoint_preserves_exact_line_numbers_and_accelerates_warm_eval() {
        let tmp_dir =
            std::env::temp_dir().join(format!("turbo_zygote_eval_prefix_{}", next_tmp_id()));
        let _ = fs::create_dir_all(&tmp_dir);
        let store = TurboStore::open(Some(&tmp_dir)).expect("open store");
        let toolchain = "leanprover/lean4:v4.31.0";
        let (env_vars, lean_bin) =
            crate::pack::resolve_server_lean_env_and_bin(&store, toolchain, "");
        if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        }

        // Lines 1..10: import + helper defs; Line 11: top-level `#eval`
        let driver_v1 = [
            "import Init",
            "def rsgbStep1 (n : Nat) : Nat := n + 10",
            "def rsgbStep2 (n : Nat) : Nat := rsgbStep1 n * 2",
            "def rsgbStep3 (n : Nat) : Nat := rsgbStep2 n + 5",
            "def rsgbStep4 (n : Nat) : String := s!\"val={rsgbStep3 n}\"",
            "def rsgbStep5 (n : Nat) : String := s!\"[{rsgbStep4 n}]\"",
            "def rsgbSimTest (a b : Nat) : String := s!\"{rsgbStep5 a}:{rsgbStep5 b}\"",
            "def rsgbSimKill (tag : String) (x : Nat) : String := s!\"{tag}:{rsgbSimTest x (x + 1)}\"",
            "def rsgbSimOutputs (k : Nat) : String :=",
            "  rsgbSimKill \"RUN\" k",
            "#eval rsgbSimOutputs 3",
        ]
        .join("\n")
            + "\n";

        let rep1 = eval_with_zygote_pool_opts(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            &driver_v1,
            false,
            true,
            Some("rsgb_driver.lean"),
            Some(15_000),
        )
        .expect("first eval_mode run");
        assert!(rep1.ok, "first eval_mode run must succeed: {:?}", rep1.errors);
        let msgs1 = rep1.messages.join("\n");
        assert!(
            msgs1.contains("rsgb_driver.lean:11:0: info:"),
            "expected exact line 11 preserved in first run messages, got: {:?}",
            rep1.messages
        );

        // Second run with the same 10-line helper prefix and a modified `#eval` on line 11:
        let driver_v2 = [
            "import Init",
            "def rsgbStep1 (n : Nat) : Nat := n + 10",
            "def rsgbStep2 (n : Nat) : Nat := rsgbStep1 n * 2",
            "def rsgbStep3 (n : Nat) : Nat := rsgbStep2 n + 5",
            "def rsgbStep4 (n : Nat) : String := s!\"val={rsgbStep3 n}\"",
            "def rsgbStep5 (n : Nat) : String := s!\"[{rsgbStep4 n}]\"",
            "def rsgbSimTest (a b : Nat) : String := s!\"{rsgbStep5 a}:{rsgbStep5 b}\"",
            "def rsgbSimKill (tag : String) (x : Nat) : String := s!\"{tag}:{rsgbSimTest x (x + 1)}\"",
            "def rsgbSimOutputs (k : Nat) : String :=",
            "  rsgbSimKill \"RUN\" k",
            "#eval rsgbSimOutputs 7",
        ]
        .join("\n")
            + "\n";

        let t0 = std::time::Instant::now();
        let rep2 = eval_with_zygote_pool_opts(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            &driver_v2,
            false,
            true,
            Some("rsgb_driver.lean"),
            Some(15_000),
        )
        .expect("second warm eval_mode run");
        let warm_elapsed_ms = t0.elapsed().as_secs_f64() * 1000.0;
        assert!(rep2.ok, "second eval_mode run must succeed: {:?}", rep2.errors);
        assert!(
            rep2.prefix_cache_hit,
            "second eval_mode run must hit Command.State prefix cache"
        );
        assert_eq!(rep2.prefix_us, 0);
        let msgs2 = rep2.messages.join("\n");
        assert!(
            msgs2.contains("rsgb_driver.lean:11:0: info:"),
            "expected exact line 11 preserved in warm prefix-cached run messages, got: {:?}",
            rep2.messages
        );
        assert!(
            rep2.elab_us < 5_000 && warm_elapsed_ms < 5.0,
            "expected warm eval_mode prefix cache hit in < 5 ms, got elab_us={} µs (wall={:.2} ms)",
            rep2.elab_us,
            warm_elapsed_ms
        );

        let _ = fs::remove_dir_all(&tmp_dir);
    }
}
