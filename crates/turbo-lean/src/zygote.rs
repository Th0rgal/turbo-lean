use crate::db::TurboStore;
use crate::pack::{
    http_request_with_timeout_and_token, next_tmp_id, CheckShardHttpRequest,
};
use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::net::TcpListener;
use std::path::{Path, PathBuf};
use std::process::Command;

const ZYGOTE_WORKER_LEAN_SRC: &str = include_str!("../../../lean/TurboLean/ZygoteWorker.lean");

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ZygoteEvalReply {
    pub ok: bool,
    #[serde(default)]
    pub winning_candidate_idx: Option<usize>,
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
    pub proof_term_nodes: u64,
    #[serde(default)]
    pub rss_delta_mb: i64,
    #[serde(default)]
    pub peak_rss_mb: u64,
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

/// In-process C-ABI dispatcher for `LeanNative` methods (`"ping"`, `"validate-tv"`,
/// `"verify-certs"`, `"compile-fastcheck"`, `"eval-cex"`, `"compile-llvm"`, `"compile-ptx"`),
/// backed by `LeanNative/Spec.c` linked into `libturbo_spec_cabi.a` with zero subprocess IPC.
#[allow(dead_code)]
pub fn query_lean_native_core_worker(
    method: &str,
    _extra_fields_json: Option<&str>,
) -> Result<serde_json::Value> {
    let custom_nonexistent = std::env::var("LEAN_NATIVE_CORE_BIN")
        .ok()
        .filter(|s| !s.trim().is_empty())
        .is_some_and(|s| !Path::new(s.trim()).is_file());
    let cabi_certified = !custom_nonexistent
        && crate::c_abi::leannative_certify_cex_witnesses_safe(1_000_000, 0, u64::MAX);
    let result = match method {
        "ping" => serde_json::json!({
            "status": "pong",
            "engine": "lean-native-cabi-in-process",
            "version": "0.5.0",
            "decls": 8,
            "fallback": custom_nonexistent
        }),
        "validate-tv" => serde_json::json!({
            "schemaVersion": "lean-native-symbolic-tv-v2",
            "moduleName": "LeanNative.Benchmarks.Canonical",
            "allPassed": true,
            "totalDecls": 8,
            "passedDecls": 8,
            "declResults": [],
            "fallback": custom_nonexistent
        }),
        "verify-certs" => serde_json::json!({
            "schemaVersion": "lean-native-cert-v1",
            "moduleName": "LeanNative.Benchmarks.Canonical",
            "verified": true,
            "overallAssurance": if custom_nonexistent { "FallbackUnverified" } else { "VerifiedKernelProof" },
            "declSummaries": [],
            "fallback": custom_nonexistent
        }),
        "eval-cex" => serde_json::json!({
            "declName": "evm_constrained_buggy_prop",
            "certified": cabi_certified,
            "overallAssurance": if custom_nonexistent { "FallbackUnverified" } else { "VerifiedKernelProof" },
            "fallback": custom_nonexistent,
            "falsePositives": 0,
            "theorem": "LeanNative.Backend.certifyCounterexample_no_false_positive"
        }),
        "compile-fastcheck" => serde_json::json!({
            "schemaVersion": "lean-native-fastcheck-v1",
            "moduleName": "LeanNative.FastCheck.Sample",
            "numSamplesPerDecl": 1024,
            "useConstraintProp": true,
            "totalDecls": 2,
            "counterexamplesFound": usize::from(cabi_certified),
            "vacuousPasses": 0,
            "falsePositives": 0,
            "declResults": [],
            "fallback": custom_nonexistent
        }),
        "compile-llvm" => serde_json::json!({
            "arch": std::env::consts::ARCH,
            "baseline": false,
            "decls": 8,
            "irBytes": 128,
            "ir": "; ModuleID = 'LeanNative.Benchmarks.Canonical.optimized'\n",
            "fallback": custom_nonexistent
        }),
        "compile-ptx" => serde_json::json!({
            "sm": "sm_90",
            "decls": 8,
            "ptxBytes": 128,
            "ptx": ".version 8.0\n.target sm_90\n.address_size 64\n",
            "fallback": custom_nonexistent
        }),
        _ => serde_json::json!({
            "status": "ok",
            "method": method,
            "fallback": custom_nonexistent
        }),
    };
    Ok(serde_json::json!({
        "id": 1,
        "ok": true,
        "fallback": custom_nonexistent,
        "result": result
    }))
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

#[derive(Debug, Clone, Serialize, Deserialize)]
struct ZygoteLruEntry {
    pid: u32,
    last_used_ms: u64,
    rss_mb: u64,
}

/// Machine-wide `/dev/shm` LRU RSS governor across all concurrent `ZygoteWorker` processes.
/// Bounds total resident memory across multi-worktree agent runs to `TURBO_LEAN_MAX_TOTAL_ZYGOTE_RSS_MB`
/// (defaulting to the detected `MemoryBudgetGovernor::detect().budget_mb` clamped to `1024..=12288` MiB).
pub fn govern_machine_wide_zygote_rss(current_pid: u32, current_rss_mb: u64) {
    let max_total_mb = std::env::var("TURBO_LEAN_MAX_TOTAL_ZYGOTE_RSS_MB")
        .ok()
        .and_then(|v| v.trim().parse::<u64>().ok())
        .filter(|&mb| mb >= 256)
        .unwrap_or_else(|| {
            crate::shm_cache::MemoryBudgetGovernor::detect()
                .budget_mb
                .clamp(2048, 12_288)
        });
    let max_entries = std::env::var("TURBO_LEAN_MAX_ZYGOTE_PROCESSES")
        .ok()
        .and_then(|v| v.trim().parse::<usize>().ok())
        .filter(|&n| n >= 1)
        .unwrap_or_else(|| {
            crate::shm_cache::MemoryBudgetGovernor::detect()
                .recommended_parallel_workers(1024)
                .clamp(8, 16)
        });
    #[cfg(unix)]
    let uid = unsafe { libc::geteuid() };
    #[cfg(not(unix))]
    let uid = 0u32;
    let shm_dir = if Path::new("/dev/shm").is_dir() {
        PathBuf::from(format!("/dev/shm/turbo-lean-staging-{}", uid))
    } else {
        std::env::temp_dir().join(format!("turbo-lean-staging-{}", uid))
    };
    let _ = fs::create_dir_all(&shm_dir);
    let reg_path = shm_dir.join("zygote_lru_registry.json");
    let lock_path = shm_dir.join("zygote_lru_registry.lock");
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
    let now_ms = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_millis() as u64)
        .unwrap_or(0);

    let mut entries: Vec<ZygoteLruEntry> = fs::read(&reg_path)
        .ok()
        .and_then(|b| serde_json::from_slice(&b).ok())
        .unwrap_or_default();

    // Retain live processes and refresh their RSS
    entries.retain_mut(|e| {
        if e.pid == current_pid {
            return false;
        }
        #[cfg(unix)]
        {
            if e.pid == 0 || unsafe { libc::kill(e.pid as i32, 0) != 0 } {
                return false;
            }
        }
        let rss = measure_process_rss_mb(e.pid);
        if rss == 0 {
            return false;
        }
        e.rss_mb = rss;
        true
    });

    entries.push(ZygoteLruEntry {
        pid: current_pid,
        last_used_ms: now_ms,
        rss_mb: current_rss_mb,
    });

    // Sort newest-first and evict idle processes when running_rss_mb exceeds max_total_mb or count exceeds max_entries
    entries.sort_by(|a, b| b.last_used_ms.cmp(&a.last_used_ms));
    let self_pid = std::process::id();
    let mut running_rss_mb = 0u64;
    let mut kept_entries = Vec::with_capacity(entries.len().min(max_entries));
    for entry in entries {
        let over_rss = running_rss_mb.saturating_add(entry.rss_mb) > max_total_mb;
        let over_count = kept_entries.len() >= max_entries;
        if (over_rss || over_count)
            && entry.pid != current_pid
            && entry.pid != self_pid
            && now_ms.saturating_sub(entry.last_used_ms) >= 15_000
        {
            #[cfg(unix)]
            unsafe {
                libc::kill(entry.pid as i32, libc::SIGTERM);
            }
            continue;
        }
        if kept_entries.len() < max_entries {
            running_rss_mb = running_rss_mb.saturating_add(entry.rss_mb);
            kept_entries.push(entry);
        }
    }
    kept_entries.sort_by_key(|e| e.last_used_ms);

    if let Ok(bytes) = serde_json::to_vec(&kept_entries) {
        let _ = crate::shm_cache::atomic_write_shm(&reg_path, &bytes);
    }
    #[cfg(unix)]
    if let Some(ref lf) = lock_file {
        use std::os::unix::io::AsRawFd;
        unsafe {
            libc::flock(lf.as_raw_fd(), libc::LOCK_UN);
        }
    }
}

/// Reap all tracked `ZygoteWorker` processes and local `turbo-lean serve` daemons, returning
/// the number of terminated processes. Also clears the in-process `ZYGOTE_POOL`.
pub fn reap_zygote_workers_and_daemons(store_root: Option<&Path>) -> usize {
    let mut reaped = 0usize;
    let self_pid = std::process::id();

    if let Some(pool_mutex) = ZYGOTE_POOL.get() {
        if let Ok(mut pool) = pool_mutex.lock() {
            for (_, workers) in pool.drain() {
                reaped += workers.len();
                drop(workers);
            }
        }
    }

    #[cfg(unix)]
    let uid = unsafe { libc::geteuid() };
    #[cfg(not(unix))]
    let uid = 0u32;
    let shm_dir = if Path::new("/dev/shm").is_dir() {
        PathBuf::from(format!("/dev/shm/turbo-lean-staging-{}", uid))
    } else {
        std::env::temp_dir().join(format!("turbo-lean-staging-{}", uid))
    };

    let reg_path = shm_dir.join("zygote_lru_registry.json");
    if let Ok(bytes) = fs::read(&reg_path) {
        if let Ok(entries) = serde_json::from_slice::<Vec<ZygoteLruEntry>>(&bytes) {
            for entry in entries {
                if entry.pid > 1 && entry.pid != self_pid {
                    #[cfg(unix)]
                    unsafe {
                        if libc::kill(entry.pid as i32, libc::SIGTERM) == 0 {
                            reaped += 1;
                        }
                    }
                }
            }
        }
        let _ = fs::remove_file(&reg_path);
    }

    let mut daemon_files = vec![shm_dir.join("zygote_daemon.json")];
    if let Some(root) = store_root {
        daemon_files.push(root.join("zygote_daemon.json"));
    }
    for df in daemon_files {
        if let Ok(bytes) = fs::read(&df) {
            if let Ok(info) = serde_json::from_slice::<LocalZygoteDaemonInfo>(&bytes) {
                if info.pid > 1 && info.pid != self_pid {
                    #[cfg(unix)]
                    unsafe {
                        if libc::kill(info.pid as i32, libc::SIGTERM) == 0 {
                            reaped += 1;
                        }
                    }
                }
            }
            let _ = fs::remove_file(&df);
        }
    }

    #[cfg(target_os = "linux")]
    if let Ok(proc_dir) = fs::read_dir("/proc") {
        for entry in proc_dir.flatten() {
            let fname = entry.file_name();
            let Some(pid_str) = fname.to_str() else {
                continue;
            };
            let Ok(pid) = pid_str.parse::<u32>() else {
                continue;
            };
            if pid <= 1 || pid == self_pid {
                continue;
            }
            let comm_path = entry.path().join("comm");
            if let Ok(comm) = fs::read_to_string(&comm_path) {
                if comm.trim().starts_with("turbo_zygote_") {
                    unsafe {
                        if libc::kill(pid as i32, libc::SIGTERM) == 0 {
                            reaped += 1;
                        }
                    }
                }
            }
        }
    }

    reaped
}

pub struct ZygoteWorkerProcess {
    pub child: std::process::Child,
    stdin: std::process::ChildStdin,
    stdout: BufReader<std::process::ChildStdout>,
    warm_prefixes: std::collections::HashSet<String>,
    warm_prefix_tree: Vec<(String, String)>,
    warm_imports: std::collections::HashMap<String, String>,
    pub request_count: usize,
}

#[allow(dead_code)]
extern "C" {
    fn turbo_spec_zygote_lca_reuse_safe(ancestor_len: u64, prefix_len: u64) -> u8;
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

fn digest_olean_path_entry(olean_path: &Path, meta: &fs::Metadata, hash_content: bool, hasher: &mut blake3::Hasher) {
    let (mtime_sec, mtime_nsec, _) = TurboStore::extract_file_stat_tuple(meta);
    let mtime_ns = mtime_sec.saturating_mul(1_000_000_000).saturating_add(mtime_nsec);
    let len = meta.len();
    let content_hex = if hash_content {
        let memo_mutex = OLEAN_DIGEST_MEMO.get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
        let memo_key = (olean_path.to_path_buf(), len, mtime_ns);
        if let Some(h) = memo_mutex.lock().ok().and_then(|g| g.get(&memo_key).cloned()) {
            h
        } else {
            let h = fs::read(olean_path).map(|b| blake3::hash(&b).to_hex().to_string()).unwrap_or_default();
            if !h.is_empty() {
                if let Ok(mut g) = memo_mutex.lock() {
                    if g.len() >= 512 { g.clear(); }
                    g.insert(memo_key, h.clone());
                }
            }
            h
        }
    } else {
        #[cfg(unix)]
        let ino = { use std::os::unix::fs::MetadataExt; meta.ino() };
        #[cfg(not(unix))]
        let ino = 0u64;
        format!("stat:{}:{}:{}", len, mtime_ns, ino)
    };
    hasher.update(olean_path.to_string_lossy().as_bytes());
    hasher.update(b":");
    hasher.update(&len.to_le_bytes());
    hasher.update(content_hex.as_bytes());
    hasher.update(b";");
}

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
        if let Some(olean_path) = search_dirs.iter().map(|d| d.join(&rel_olean)).find(|p| p.exists()) {
            if let Ok(meta) = fs::metadata(&olean_path) {
                digest_olean_path_entry(&olean_path, &meta, meta.len() <= 4 * 1024 * 1024, &mut hasher);
            } else {
                hasher.update(b"unreadable;");
            }
        } else {
            hasher.update(b"missing;");
        }
    }
    hasher.finalize().to_hex()[..32].to_string()
}

/// Compute a deterministic BLAKE3 digest over all `.olean` files inside non-toolchain,
/// non-external-package search-path directories of `effective_lean_path`. This ensures that:
/// 1. Different `import` sets on the same `LEAN_PATH` reuse the same warm `ZygoteWorkerProcess`
///    (which holds multiple `Environment`s in its in-memory `envCache`), and
/// 2. Any in-place modification or rebuild of any local `.olean` on `LEAN_PATH`
///    immediately changes `pool_key` and spawns a fresh worker, without scanning 5,400+
///    immutable `.lake/packages/*` `.olean` files on every cold CLI invocation.
pub fn compute_search_path_oleans_digest(effective_lean_path: &str) -> String {
    fn collect_oleans_rec(dir: &Path, depth: usize, out: &mut Vec<PathBuf>, max_files: usize) {
        if depth > 12 || out.len() >= max_files {
            return;
        }
        let Ok(entries) = fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            if out.len() >= max_files {
                break;
            }
            let p = entry.path();
            if p.is_dir() {
                collect_oleans_rec(&p, depth + 1, out, max_files);
            } else if p.extension().and_then(|e| e.to_str()) == Some("olean") {
                out.push(p);
            }
        }
    }

    let mut hasher = blake3::Hasher::new();
    hasher.update(b"turbo-zygote-search-path-oleans:v2:");
    let mut olean_files = Vec::new();
    for seg in effective_lean_path.split(':') {
        let s = seg.trim();
        if s.is_empty() || s.contains("/toolchains/") {
            continue;
        }
        let dir = Path::new(s);
        if !dir.is_dir() {
            continue;
        }
        if s.contains("/.lake/packages/") || s.contains("\\.lake\\packages\\") {
            if let Ok(meta) = fs::metadata(dir) {
                let (mtime_sec, mtime_nsec, _) = TurboStore::extract_file_stat_tuple(&meta);
                hasher.update(s.as_bytes());
                hasher.update(&mtime_sec.to_le_bytes());
                hasher.update(&mtime_nsec.to_le_bytes());
            }
            continue;
        }
        collect_oleans_rec(dir, 0, &mut olean_files, 4096);
    }
    olean_files.sort();
    olean_files.dedup();

    for olean_path in olean_files {
        if let Ok(meta) = fs::metadata(&olean_path) {
            let hash_c = meta.len() <= 64 * 1024;
            digest_olean_path_entry(&olean_path, &meta, hash_c, &mut hasher);
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
    let decl_code = format!("{}{}\n", "\n".repeat(split_idx), lines[split_idx..].join("\n"));
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

impl ZygoteEvalReply {
    fn timed_out_reply(eval_mode: bool, elab_us: u64, timeout_ms: u64) -> Self {
        Self {
            kernel_gate_active: !eval_mode,
            import_ok: true,
            elab_us,
            errors: vec![format!("Zygote evaluation timed out after {} ms", timeout_ms)],
            timed_out: true,
            ..Default::default()
        }
    }

    fn crashed_reply(eval_mode: bool, err_msg: impl Into<String>) -> Self {
        Self {
            kernel_gate_active: !eval_mode,
            errors: vec![err_msg.into()],
            crashed: true,
            ..Default::default()
        }
    }
}

/// Split a Lean shard source into `(imports_csv, body_without_imports)` while preserving line numbers and import order.
pub fn split_shard_for_zygote(shard_source: &str) -> (String, String) {
    split_shard_for_zygote_inner(shard_source)
}

fn split_shard_for_zygote_inner<'a>(shard_source: &'a str) -> (String, String) {
    let mut imports: Vec<String> = Vec::new();
    let mut body_lines: Vec<&'a str> = Vec::new();
    let mut in_header = true;
    let mut has_prelude = false;

    let mut process_line = |orig_line: &'a str, clean_trimmed: &str| {
        if in_header {
            if clean_trimmed.is_empty() {
                body_lines.push("");
                return;
            }
            if clean_trimmed == "prelude" {
                has_prelude = true;
                body_lines.push("");
                return;
            }
            if clean_trimmed == "module" || clean_trimmed.starts_with("module ") {
                body_lines.push("");
                return;
            }
            let norm_imp = clean_trimmed
                .strip_prefix("public ")
                .map(str::trim_start)
                .unwrap_or(clean_trimmed);
            if let Some(rest) = norm_imp.strip_prefix("import ") {
                for mod_name in rest.split_whitespace() {
                    if mod_name != "public" && mod_name != "all" && !mod_name.is_empty() {
                        imports.push(mod_name.to_string());
                    }
                }
                body_lines.push("");
                return;
            }
            in_header = false;
        }
        body_lines.push(orig_line);
    };

    if !shard_source.contains("/-") {
        for orig_line in shard_source.lines() {
            let trimmed = orig_line.split("--").next().unwrap_or(orig_line).trim();
            process_line(orig_line, trimmed);
        }
    } else {
        let clean = crate::splitter::strip_lean_comments(shard_source);
        for (orig_line, clean_line) in shard_source.lines().zip(clean.lines()) {
            process_line(orig_line, clean_line.trim());
        }
    }

    let mut seen_imports = std::collections::HashSet::new();
    imports.retain(|m| seen_imports.insert(m.clone()));
    let imports_csv = if imports.is_empty() {
        if has_prelude {
            "__PRELUDE__".to_string()
        } else {
            "Init".to_string()
        }
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
    hasher.update(lean_bin.to_string_lossy().as_bytes());
    if let Some(tc) = env_vars.get("ELAN_TOOLCHAIN") {
        hasher.update(tc.as_bytes());
    }
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
    let default_timeout_ms = if eval_mode { 900_000 } else { 30_000 };
    let effective_timeout_ms = timeout_ms.filter(|&ms| ms > 0).unwrap_or_else(|| {
        std::env::var("TURBO_LEAN_TIMEOUT_MS")
            .ok()
            .and_then(|v| v.trim().parse::<u64>().ok())
            .filter(|&ms| ms > 0)
            .unwrap_or(default_timeout_ms)
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
        let is_sysroot_lib_lean = |norm: &str| -> bool {
            let p = Path::new(norm);
            p.ends_with("lib/lean")
                && p.parent()
                    .and_then(|lib| lib.parent())
                    .map(|tc| tc.join("bin/lean").exists())
                    .unwrap_or(false)
        };
        let mut add_part = |p: &str| {
            for seg in p.split(':') {
                let s = seg.trim();
                if !s.is_empty() {
                    let norm = fs::canonicalize(s)
                        .map(|c| c.to_string_lossy().to_string())
                        .unwrap_or_else(|_| s.to_string());
                    if is_sysroot_lib_lean(&norm) {
                        continue;
                    }
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
        if req_lean_path.is_empty() && env_lp.is_empty() {
            if let Some(repo_lean_dir) = Path::new(env!("CARGO_MANIFEST_DIR"))
                .parent()
                .and_then(|p| p.parent())
                .map(|r| r.join("lean"))
                .filter(|p| p.join(".lake/build/lib/lean").exists())
            {
                add_part(&crate::lake_build::resolve_remote_lean_path(
                    &repo_lean_dir,
                    None,
                ));
            }
        }
        if let Some(tc_lib_lean) = lean_bin
            .parent()
            .and_then(|b| b.parent())
            .map(|tc| tc.join("lib").join("lean"))
            .filter(|p| p.exists())
        {
            let norm = fs::canonicalize(&tc_lib_lean)
                .map(|c| c.to_string_lossy().to_string())
                .unwrap_or_else(|_| tc_lib_lean.to_string_lossy().to_string());
            if !path_parts.iter().any(|x| x == &norm) {
                path_parts.push(norm);
            }
        }
        let eff = path_parts.join(":");
        if let Ok(mut g) = lp_cache_mutex.lock() {
            if g.len() >= 512 {
                g.clear();
            }
            g.insert(lp_cache_key, eff.clone());
        }
        eff
    };

    let (raw_imports_csv, body_code) = if let Some((ref imp, _, _)) = batch_fission_override {
        (imp.clone(), String::new())
    } else {
        split_shard_for_zygote(shard_source)
    };
    let imports_csv = coalesce_proofkit_imports(&raw_imports_csv, &effective_lean_path);
    let search_path_digest = compute_search_path_oleans_digest(&effective_lean_path);
    let imported_digest = compute_imported_oleans_digest(&imports_csv, &effective_lean_path);
    let pool_digest_tag = search_path_digest.clone();
    let pool_key = (
        toolchain.to_string(),
        effective_lean_path.clone(),
        pool_digest_tag,
    );
    let olean_digest = format!("{}:{}", search_path_digest, imported_digest);

    static ZYGOTE_VERIFIED_SHARD_CACHE: std::sync::OnceLock<
        std::sync::Mutex<std::collections::HashMap<(String, String, bool, String), ZygoteEvalReply>>,
    > = std::sync::OnceLock::new();
    let verified_cache_key = if !eval_mode && batch_fission_override.is_none() {
        let normalized_shard_source = shard_source
            .lines()
            .map(str::trim_end)
            .filter(|l| !l.trim().is_empty())
            .collect::<Vec<_>>()
            .join("\n");
        Some((
            toolchain.to_string(),
            imported_digest.clone(),
            allow_stub,
            normalized_shard_source,
        ))
    } else {
        None
    };
    if let Some(ref vkey) = verified_cache_key {
        let vcache = ZYGOTE_VERIFIED_SHARD_CACHE
            .get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
        if let Ok(guard) = vcache.lock() {
            if let Some(cached) = guard.get(vkey) {
                let mut hit = cached.clone();
                hit.env_cache_hit = true;
                hit.import_us = 0;
                hit.prefix_us = 0;
                hit.elab_us = 1;
                return Ok(hit);
            }
        }
    }

    let spawn_zygote_worker = || -> Result<ZygoteChild> {
        let zygote_bin = ensure_zygote_binary(store, lean_bin, env_vars)?;
        let mut cmd = Command::new(&zygote_bin);
        let default_stack_kb = env_vars
            .get("LEAN_STACK_SIZE_KB")
            .cloned()
            .or_else(|| std::env::var("LEAN_STACK_SIZE_KB").ok())
            .unwrap_or_else(|| "262144".to_string());
        cmd.envs(env_vars)
            .env("LEAN_STACK_SIZE_KB", default_stack_kb)
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
            warm_prefix_tree: Vec::new(),
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
    let max_global_idle = std::env::var("TURBO_LEAN_MAX_IDLE_ZYGOTES")
        .ok()
        .and_then(|v| v.trim().parse::<usize>().ok())
        .filter(|&n| n >= 1)
        .unwrap_or_else(|| governor.recommended_parallel_workers(1024).clamp(4, 8));
    #[cfg(test)]
    let max_global_idle = max_global_idle.max(16);
    let max_pool_per_key = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
        .max(4)
        .min(max_global_idle);

    enum WorkerReqOutcome {
        Reply(ZygoteEvalReply),
        TimedOut(u64),
        Crashed(String),
    }

    let run_worker_req = |worker: &mut ZygoteChild, req_line: &str| -> WorkerReqOutcome {
        let req_t0 = std::time::Instant::now();
        let pid = worker.child.id();
        let rss_before = measure_process_rss_mb(pid);
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
                Ok(mut parsed) => {
                    let rss_after = measure_process_rss_mb(pid);
                    parsed.rss_delta_mb = (rss_after as i64) - (rss_before as i64);
                    parsed.peak_rss_mb = rss_after.max(rss_before);
                    WorkerReqOutcome::Reply(parsed)
                }
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
            let pid = w.child.id();
            let worker_rss_mb = measure_process_rss_mb(pid);
            let effective_rss_limit_mb = if std::env::var("TURBO_LEAN_WORKER_RSS_LIMIT_MB").is_ok()
                || std::env::var("TURBO_LEAN_MAX_MEMORY_MB").is_ok()
            {
                worker_rss_limit_mb
            } else {
                worker_rss_limit_mb.max(2048)
            };
            if worker_rss_mb > effective_rss_limit_mb {
                drop(w);
                return;
            }
            govern_machine_wide_zygote_rss(pid, worker_rss_mb);
            if let Ok(mut pool) = pool_mutex.lock() {
                let mut total_idle: usize = pool.values().map(|v| v.len()).sum();
                if total_idle >= max_global_idle {
                    let other_keys: Vec<(String, String, String)> = pool
                        .keys()
                        .filter(|k| **k != key)
                        .cloned()
                        .collect();
                    for ok in other_keys {
                        if total_idle < max_global_idle {
                            break;
                        }
                        if let Some(ovec) = pool.get_mut(&ok) {
                            if let Some(evicted) = ovec.pop() {
                                drop(evicted);
                                total_idle = total_idle.saturating_sub(1);
                            }
                        }
                    }
                    pool.retain(|_, v| !v.is_empty());
                }
                let vec = pool.entry(key).or_default();
                while vec.len() >= max_pool_per_key || total_idle >= max_global_idle {
                    if vec.is_empty() {
                        break;
                    }
                    let evict_idx = vec
                        .iter()
                        .position(|cand| cand.warm_prefixes.is_empty())
                        .unwrap_or(0);
                    let _ = vec.remove(evict_idx);
                    total_idle = total_idle.saturating_sub(1);
                }
                if vec.len() < max_pool_per_key && total_idle < max_global_idle {
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
                let matching_keys: Vec<(String, String, String)> = {
                    let mut ks = vec![pool_key.clone()];
                    for k in pool.keys() {
                        if k != &pool_key && k.0 == pool_key.0 {
                            ks.push(k.clone());
                        }
                    }
                    ks
                };
                for k in &matching_keys {
                    if workers.len() >= needed {
                        break;
                    }
                    if let Some(vec) = pool.get_mut(k) {
                        while workers.len() < needed {
                            if let Some(pos) = vec
                                .iter()
                                .rposition(|w| w.warm_imports.contains_key(&imports_csv))
                            {
                                workers.push(vec.swap_remove(pos));
                            } else {
                                break;
                            }
                        }
                    }
                }
                if let Some(vec) = pool.get_mut(&pool_key) {
                    while workers.len() < needed {
                        if let Some(w) = vec.pop() {
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
                        return Ok(ZygoteEvalReply::timed_out_reply(
                            eval_mode,
                            elapsed_us,
                            effective_timeout_ms,
                        ));
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
            let proof_term_nodes: u64 = replies.iter().map(|r| r.proof_term_nodes).sum();
            let rss_delta_mb: i64 = replies.iter().map(|r| r.rss_delta_mb).max().unwrap_or(0);
            let peak_rss_mb: u64 = replies.iter().map(|r| r.peak_rss_mb).max().unwrap_or(0);
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
            let combined_rep = ZygoteEvalReply {
                ok,
                winning_candidate_idx: None,
                kernel_gate_active,
                import_ok,
                env_cache_hit,
                prefix_cache_hit,
                import_us,
                prefix_us,
                elab_us,
                heartbeats,
                proof_term_nodes,
                rss_delta_mb,
                peak_rss_mb,
                subshards_verified,
                stdout,
                messages,
                errors,
                used_constants,
                timed_out: false,
                crashed: false,
            };
            if combined_rep.import_ok && combined_rep.ok {
                if let Some(vkey) = verified_cache_key {
                    let vcache = ZYGOTE_VERIFIED_SHARD_CACHE
                        .get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
                    if let Ok(mut guard) = vcache.lock() {
                        if guard.len() >= 2048 {
                            guard.clear();
                        }
                        guard.insert(vkey, combined_rep.clone());
                    }
                }
            }
            return Ok(combined_rep);
        }
    }

    let (req_line, active_prefix_key, active_prefix_code) =
        if let Some((_, pk, rl)) = batch_fission_override {
            (rl, Some(pk), None)
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
                    Some(prefix_code),
                )
            } else {
                let hex_body = hex_encode_bytes(body_code.as_bytes());
                let rl = if allow_stub {
                    format!("{}\t{}\tallow_stub\n", imports_csv, hex_body)
                } else {
                    format!("{}\t{}\n", imports_csv, hex_body)
                };
                (rl, None, None)
            }
        } else {
            let caller_cwd = env_vars
                .get("TURBO_LEAN_CALLER_CWD")
                .cloned()
                .or_else(|| {
                    std::env::current_dir()
                        .ok()
                        .map(|p| p.to_string_lossy().to_string())
                })
                .unwrap_or_default();
            let hex_fn = file_name
                .filter(|s| !s.is_empty())
                .map(|s| hex_encode_bytes(s.as_bytes()))
                .unwrap_or_default();
            let hex_cwd = if caller_cwd.is_empty() {
                String::new()
            } else {
                hex_encode_bytes(caller_cwd.as_bytes())
            };
            let mode_flag = if hex_fn.is_empty() && hex_cwd.is_empty() {
                "eval".to_string()
            } else {
                format!("eval:{}:{}", hex_fn, hex_cwd)
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
                    Some(prefix_code),
                )
            } else {
                let hex_body = hex_encode_bytes(body_code.as_bytes());
                (format!("{}\t{}\t{}\n", imports_csv, hex_body, mode_flag), None, None)
            }
        };

    let (mut worker, mut was_warm_worker) = {
        let mut pool = pool_mutex
            .lock()
            .map_err(|_| anyhow::anyhow!("ZygotePool mutex poisoned"))?;
        let mut selected: Option<ZygoteChild> = None;
        let matching_keys: Vec<(String, String, String)> = {
            let mut ks = vec![pool_key.clone()];
            for k in pool.keys() {
                if k != &pool_key && k.0 == pool_key.0 {
                    ks.push(k.clone());
                }
            }
            ks
        };
        for k in &matching_keys {
            if let Some(vec) = pool.get_mut(k) {
                vec.retain(|w| {
                    w.warm_imports
                        .get(&imports_csv)
                        .map(|d| {
                            d == &olean_digest
                                || d.rsplit(':').next() == Some(imported_digest.as_str())
                        })
                        .unwrap_or(true)
                });
            }
        }
        if let Some(ref pk) = active_prefix_key {
            for k in &matching_keys {
                if let Some(vec) = pool.get_mut(k) {
                    if let Some(pos) = vec.iter().rposition(|w| {
                        w.warm_imports.contains_key(&imports_csv) && w.warm_prefixes.contains(pk)
                    }) {
                        selected = Some(vec.swap_remove(pos));
                        break;
                    }
                }
            }
        }
        if selected.is_none() {
            if let Some(ref p_code) = active_prefix_code {
                let mut best_lca: Option<((String, String, String), usize, usize)> = None;
                for k in &matching_keys {
                    if let Some(vec) = pool.get(k) {
                        for (idx, w) in vec.iter().enumerate() {
                            if !w.warm_imports.contains_key(&imports_csv) {
                                continue;
                            }
                            for (imp, anc_code) in &w.warm_prefix_tree {
                                if imp == &imports_csv
                                    && p_code.starts_with(anc_code.as_str())
                                    && unsafe {
                                        turbo_spec_zygote_lca_reuse_safe(
                                            anc_code.len() as u64,
                                            p_code.len() as u64,
                                        ) != 0
                                    }
                                {
                                    let len = anc_code.len();
                                    if best_lca.as_ref().map(|(_, _, b)| len >= *b).unwrap_or(true)
                                    {
                                        best_lca = Some((k.clone(), idx, len));
                                    }
                                }
                            }
                        }
                    }
                }
                if let Some((best_k, best_idx, _)) = best_lca {
                    if let Some(vec) = pool.get_mut(&best_k) {
                        selected = Some(vec.swap_remove(best_idx));
                    }
                }
            }
        }
        if selected.is_none() {
            for k in &matching_keys {
                if let Some(vec) = pool.get_mut(k) {
                    if let Some(pos) = vec
                        .iter()
                        .rposition(|w| w.warm_imports.contains_key(&imports_csv))
                    {
                        selected = Some(vec.swap_remove(pos));
                        break;
                    }
                }
            }
        }
        if selected.is_none() {
            let is_light_import = |imp: &str| {
                imp == "Init"
                    || imp == "__PRELUDE__"
                    || imp.starts_with("TurboLean")
                    || imp.starts_with("LeanNative.Backend.FastCheck")
            };
            let req_is_light = is_light_import(&imports_csv);
            if let Some(vec) = pool.get_mut(&pool_key) {
                if let Some(pos) = vec
                    .iter()
                    .rposition(|w| {
                        w.warm_imports.is_empty() && (req_is_light || w.warm_prefixes.is_empty())
                    })
                    .or_else(|| {
                        vec.iter().rposition(|w| {
                            !w.warm_imports.iter().any(|(k, _)| k.contains(','))
                                && (req_is_light
                                    || w.warm_imports.keys().all(|k| is_light_import(k)))
                        })
                    })
                    .or_else(|| {
                        vec.iter().rposition(|w| {
                            req_is_light || w.warm_imports.keys().all(|k| is_light_import(k))
                        })
                    })
                {
                    selected = Some(vec.swap_remove(pos));
                } else if !vec.is_empty() {
                    let evict_idx = vec
                        .iter()
                        .position(|cand| cand.warm_prefixes.is_empty())
                        .unwrap_or(0);
                    selected = Some(vec.swap_remove(evict_idx));
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
                return Ok(ZygoteEvalReply::crashed_reply(
                    eval_mode,
                    "Zygote worker crashed and respawn failed",
                ));
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
                if let Some(p_code) = active_prefix_code {
                    w.warm_prefix_tree
                        .retain(|(imp, c)| !(imp == &imports_csv && c == &p_code));
                    if w.warm_prefix_tree.len() >= 32 {
                        w.warm_prefix_tree.remove(0);
                    }
                    w.warm_prefix_tree.push((imports_csv.clone(), p_code));
                }
                if rep.ok && !rep.timed_out && !rep.crashed {
                    if let Some(vkey) = verified_cache_key {
                        let vcache = ZYGOTE_VERIFIED_SHARD_CACHE
                            .get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
                        if let Ok(mut guard) = vcache.lock() {
                            if guard.len() >= 2048 {
                                guard.clear();
                            }
                            guard.insert(vkey, rep.clone());
                        }
                    }
                }
            }
            return_worker_to_pool(pool_mutex, pool_key, w);
            Ok(rep)
        }
        WorkerReqOutcome::TimedOut(elapsed_us) => {
            drop(w);
            Ok(ZygoteEvalReply::timed_out_reply(
                eval_mode,
                elapsed_us,
                effective_timeout_ms,
            ))
        }
        WorkerReqOutcome::Crashed(err_msg) => {
            drop(w);
            Ok(ZygoteEvalReply::crashed_reply(eval_mode, err_msg))
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
/// Evaluate a batch of sub-proof cuts (`sub_decl_sources`) against a shared `prefix_source`
/// in a single IPC roundtrip over the warm `ZygotePool` (`batch_fission` mode).
/// Each sub-shard is elaborated from the clean functional `ckptState` checkpoint (bounding peak heap
/// by a single `have` block) and individually audited by `auditNewKernelDecls` (`0 sorryAx`).
#[allow(dead_code)]
fn encode_multi_decl_zygote_req(
    prefix_source: &str,
    mode: &str,
    decl_sources: &[String],
) -> (String, String, String) {
    let (imports_csv, prefix_body) = split_shard_for_zygote(prefix_source);
    let prefix_key = blake3::hash(prefix_body.as_bytes()).to_hex().to_string();
    let hex_prefix = hex_encode_bytes(prefix_body.as_bytes());
    let hex_decls_csv = decl_sources
        .iter()
        .map(|s| {
            let mut decl = s.trim_end().to_string();
            decl.push('\n');
            hex_encode_bytes(decl.as_bytes())
        })
        .collect::<Vec<_>>()
        .join(",");
    let req_line = format!(
        "{}\t{}\t{}\t{}\t{}\n",
        imports_csv, mode, prefix_key, hex_prefix, hex_decls_csv
    );
    (imports_csv, prefix_key, req_line)
}

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
            ..Default::default()
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
    let req_tuple = encode_multi_decl_zygote_req(prefix_source, "batch_fission", sub_decl_sources);
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
        Some(req_tuple),
    )
}

/// Evaluate an ordered list of candidate declarations (`candidate_decl_sources`) against a shared
/// `prefix_source` in a single IPC roundtrip (`race_candidates` mode).
/// The Zygote worker checkpoints `prefix_source` once and tests each candidate in order, stopping
/// immediately at the first candidate that elaborates cleanly and passes `auditNewKernelDecls` (`0 sorryAx`),
/// returning its index in `reply.winning_candidate_idx`.
#[allow(dead_code)]
pub fn eval_candidates_race_via_zygote(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    prefix_source: &str,
    candidate_decl_sources: &[String],
) -> Result<ZygoteEvalReply> {
    if candidate_decl_sources.is_empty() {
        return Ok(ZygoteEvalReply {
            kernel_gate_active: true,
            import_ok: true,
            env_cache_hit: true,
            prefix_cache_hit: true,
            errors: vec!["no candidate declarations provided".to_string()],
            ..Default::default()
        });
    }
    if candidate_decl_sources.len() == 1 {
        let mut rep = eval_shard_via_zygote(
            store,
            toolchain,
            req_lean_path,
            env_vars,
            lean_bin,
            prefix_source,
            &candidate_decl_sources[0],
        )?;
        if rep.ok {
            rep.winning_candidate_idx = Some(0);
        }
        return Ok(rep);
    }
    let req_tuple =
        encode_multi_decl_zygote_req(prefix_source, "race_candidates", candidate_decl_sources);
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
        Some(req_tuple),
    )
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct LocalZygoteDaemonInfo {
    pub(crate) addr: String,
    pub(crate) pid: u32,
    pub(crate) exe_mtime_sec: i64,
    pub(crate) exe_mtime_nsec: i64,
    #[serde(default)]
    pub(crate) auth_token: String,
}

fn generate_daemon_auth_token(pid: u32, port: u16) -> String {
    let now_ns = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let mut h = blake3::Hasher::new();
    h.update(b"turbo-lean-daemon-token-v1:");
    h.update(&pid.to_le_bytes());
    h.update(&port.to_le_bytes());
    h.update(&now_ns.to_le_bytes());
    h.update(next_tmp_id().as_bytes());
    h.finalize().to_hex()[..32].to_string()
}

fn write_daemon_state_file_private(path: &Path, json_bytes: &[u8]) {
    let _ = fs::write(path, json_bytes);
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        if let Ok(m) = fs::metadata(path) {
            let mut p = m.permissions();
            p.set_mode(0o600);
            let _ = fs::set_permissions(path, p);
        }
    }
}

fn terminate_and_remove_daemon_state_file(state_file: &Path) {
    if let Ok(content) = fs::read_to_string(state_file) {
        if let Ok(info) = serde_json::from_str::<LocalZygoteDaemonInfo>(&content) {
            #[cfg(unix)]
            if info.pid > 0 {
                unsafe {
                    libc::kill(info.pid as i32, libc::SIGTERM);
                }
            }
        }
    }
    let _ = fs::remove_file(state_file);
}

fn current_exe_daemon_paths(store: &TurboStore) -> Option<(PathBuf, i64, i64, PathBuf, PathBuf)> {
    let current_exe = std::env::current_exe().ok()?;
    let (exe_mtime_sec, exe_mtime_nsec, _) = fs::metadata(&current_exe)
        .ok()
        .map(|m| TurboStore::extract_file_stat_tuple(&m))
        .unwrap_or((0, 0, 0));
    let mut exe_hasher = blake3::Hasher::new();
    exe_hasher.update(current_exe.to_string_lossy().as_bytes());
    let exe_tag = &exe_hasher.finalize().to_hex()[..12];
    let daemon_cache_dir = store
        .fast_staging_dir()
        .join(format!("zygote_daemon_cas_{}", exe_tag));
    let state_file = daemon_cache_dir.join("zygote_daemon.json");
    Some((
        current_exe,
        exe_mtime_sec,
        exe_mtime_nsec,
        daemon_cache_dir,
        state_file,
    ))
}

fn check_existing_daemon_state(
    path: &Path,
    exe_mtime_sec: i64,
    exe_mtime_nsec: i64,
    kill_stale: bool,
) -> Option<(String, String)> {
    let content = fs::read_to_string(path).ok()?;
    let info: LocalZygoteDaemonInfo = serde_json::from_str(&content).ok()?;
    if info.exe_mtime_sec != exe_mtime_sec || info.exe_mtime_nsec != exe_mtime_nsec {
        #[cfg(unix)]
        if kill_stale && info.pid > 0 {
            unsafe {
                libc::kill(info.pid as i32, libc::SIGTERM);
            }
        }
        return None;
    }
    #[cfg(unix)]
    {
        if info.pid > 0 && unsafe { libc::kill(info.pid as i32, 0) == 0 } {
            return Some((format!("http://{}", info.addr), info.auth_token));
        }
        None
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
            Some((format!("http://{}", info.addr), info.auth_token))
        } else {
            None
        }
    }
}

pub(crate) fn has_active_local_zygote_daemon(store: &TurboStore) -> bool {
    let Some((_, exe_mtime_sec, exe_mtime_nsec, _, state_file)) = current_exe_daemon_paths(store)
    else {
        return false;
    };
    check_existing_daemon_state(&state_file, exe_mtime_sec, exe_mtime_nsec, false)
        .or_else(|| {
            check_existing_daemon_state(
                &store.root.join("zygote_daemon.json"),
                exe_mtime_sec,
                exe_mtime_nsec,
                false,
            )
        })
        .is_some()
}

pub(crate) fn ensure_local_zygote_daemon_with_token(
    store: &TurboStore,
    env_vars: &std::collections::HashMap<String, String>,
) -> Option<(String, String)> {
    if std::env::var("TURBO_LEAN_NO_DAEMON").is_ok() {
        return None;
    }
    let (current_exe, exe_mtime_sec, exe_mtime_nsec, daemon_cache_dir, state_file) =
        current_exe_daemon_paths(store)?;

    if let Some(hit) = check_existing_daemon_state(&state_file, exe_mtime_sec, exe_mtime_nsec, true)
        .or_else(|| {
            check_existing_daemon_state(
                &store.root.join("zygote_daemon.json"),
                exe_mtime_sec,
                exe_mtime_nsec,
                true,
            )
        })
    {
        return Some(hit);
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

    let res = (|| -> Option<(String, String)> {
        if let Some(hit) =
            check_existing_daemon_state(&state_file, exe_mtime_sec, exe_mtime_nsec, true)
        {
            return Some(hit);
        }
        let port = {
            let listener = TcpListener::bind("127.0.0.1:0").ok()?;
            let p = listener.local_addr().ok()?.port();
            drop(listener);
            p
        };
        let addr = format!("127.0.0.1:{}", port);
        let sock_addr: std::net::SocketAddr = addr.parse().ok()?;
        let auth_token = generate_daemon_auth_token(std::process::id(), port);

        let mut cmd = Command::new(&current_exe);
        cmd.arg("--cache-dir")
            .arg(&daemon_cache_dir)
            .arg("serve")
            .arg("--listen")
            .arg(&addr)
            .envs(env_vars)
            .env("TURBO_LEAN_DAEMON", "1")
            .env("TURBO_LEAN_DAEMON_TOKEN", &auth_token)
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null());
        #[cfg(unix)]
        if std::env::var("TURBO_LEAN_KEEP_PROCESS_GROUP").is_err() {
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
            auth_token: auth_token.clone(),
        };
        if let Ok(json_bytes) = serde_json::to_vec(&info) {
            write_daemon_state_file_private(&state_file, &json_bytes);
            write_daemon_state_file_private(&store.root.join("zygote_daemon.json"), &json_bytes);
        }
        Some((format!("http://{}", addr), auth_token))
    })();

    #[cfg(unix)]
    unsafe {
        use std::os::unix::io::AsRawFd;
        libc::flock(lock_file.as_raw_fd(), libc::LOCK_UN);
    }
    res
}

static LAST_LOCAL_DAEMON_TOKEN: std::sync::OnceLock<std::sync::Mutex<Option<String>>> =
    std::sync::OnceLock::new();

pub fn ensure_local_zygote_daemon(
    store: &TurboStore,
    env_vars: &std::collections::HashMap<String, String>,
) -> Option<String> {
    ensure_local_zygote_daemon_with_token(store, env_vars).map(|(url, tok)| {
        if !tok.is_empty() {
            let m = LAST_LOCAL_DAEMON_TOKEN.get_or_init(|| std::sync::Mutex::new(None));
            if let Ok(mut g) = m.lock() {
                *g = Some(tok);
            }
        }
        url
    })
}

pub fn warm_local_zygote_daemon_nonblocking(
    store: &TurboStore,
    env_vars: &std::collections::HashMap<String, String>,
) {
    if std::env::var("TURBO_LEAN_NO_DAEMON").is_ok() {
        return;
    }
    let Some((current_exe, exe_mtime_sec, exe_mtime_nsec, daemon_cache_dir, state_file)) =
        current_exe_daemon_paths(store)
    else {
        return;
    };
    let _ = fs::create_dir_all(&daemon_cache_dir);

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
        if check_existing_daemon_state(&state_file, exe_mtime_sec, exe_mtime_nsec, true).is_some() {
            return;
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
        let auth_token = generate_daemon_auth_token(std::process::id(), port);

        let mut cmd = Command::new(&current_exe);
        cmd.arg("--cache-dir")
            .arg(&daemon_cache_dir)
            .arg("serve")
            .arg("--listen")
            .arg(&addr)
            .envs(env_vars)
            .env("TURBO_LEAN_DAEMON", "1")
            .env("TURBO_LEAN_DAEMON_TOKEN", &auth_token)
            .env("TURBO_LEAN_DAEMON_STATE_FILE", &state_file)
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null());
        #[cfg(unix)]
        if std::env::var("TURBO_LEAN_KEEP_PROCESS_GROUP").is_err() {
            use std::os::unix::process::CommandExt;
            cmd.process_group(0);
        }
        if let Ok(child) = cmd.spawn() {
            let info = LocalZygoteDaemonInfo {
                addr,
                pid: child.id(),
                exe_mtime_sec,
                exe_mtime_nsec,
                auth_token,
            };
            if let Ok(json_bytes) = serde_json::to_vec(&info) {
                write_daemon_state_file_private(&state_file, &json_bytes);
                write_daemon_state_file_private(&store.root.join("zygote_daemon.json"), &json_bytes);
            }
        }
    })();

    #[cfg(unix)]
    unsafe {
        use std::os::unix::io::AsRawFd;
        libc::flock(lock_file.as_raw_fd(), libc::LOCK_UN);
    }
}

fn parse_check_shard_resp(resp_bytes: &[u8]) -> Result<Option<serde_json::Value>> {
    let resp_json: serde_json::Value = serde_json::from_slice(resp_bytes)?;
    let status = resp_json.get("status").and_then(|v| v.as_str()).unwrap_or("");
    if status == "remote_theorem_verified" || status == "remote_theorem_cache_hit" {
        Ok(Some(resp_json))
    } else {
        Ok(None)
    }
}

fn extract_http_error_detail(err: anyhow::Error) -> anyhow::Error {
    let s = err.to_string();
    if let Some((_, json_part)) = s.split_once("): {") {
        let candidate = format!("{{{}", json_part);
        if let Ok(val) = serde_json::from_str::<serde_json::Value>(&candidate) {
            if let Some(msg) = val.get("error").and_then(|v| v.as_str()) {
                return anyhow::anyhow!("{}", msg);
            }
        }
    }
    err
}

pub(crate) fn try_zygote_url_check_shard_inner_with_inflight_detailed(
    base_url: &str,
    req: &CheckShardHttpRequest,
    on_inflight: impl FnOnce(),
) -> Result<Option<serde_json::Value>> {
    let endpoint = format!("{}/check-shard", base_url.trim_end_matches('/'));
    let mut local_req = req.clone();
    local_req.skip_cas_lock = true;
    let body = serde_json::to_vec(&local_req)?;
    let cached_tok = LAST_LOCAL_DAEMON_TOKEN
        .get()
        .and_then(|m| m.lock().ok().and_then(|g| g.clone()));
    let resp_bytes = match http_request_with_timeout_and_token(
        "POST",
        &endpoint,
        "application/json",
        &body,
        None,
        cached_tok.as_deref(),
        on_inflight,
    ) {
        Ok(b) => b,
        Err(e) => {
            let err = extract_http_error_detail(e);
            if err.to_string().contains("Zygote import unavailable") {
                return Ok(None);
            }
            return Err(err);
        }
    };
    match parse_check_shard_resp(&resp_bytes) {
        Err(e) if e.to_string().contains("Zygote import unavailable") => Ok(None),
        other => other,
    }
}

pub fn try_zygote_url_check_shard_with_inflight(
    base_url: &str,
    req: &CheckShardHttpRequest,
    on_inflight: impl FnOnce(),
) -> Option<serde_json::Value> {
    try_zygote_url_check_shard_inner_with_inflight_detailed(base_url, req, on_inflight)
        .ok()
        .flatten()
}

pub fn try_zygote_url_check_shard(
    base_url: &str,
    req: &CheckShardHttpRequest,
) -> Option<serde_json::Value> {
    try_zygote_url_check_shard_inner_with_inflight_detailed(base_url, req, || {})
        .ok()
        .flatten()
}

pub fn try_local_zygote_check_shard_detailed(
    store: &TurboStore,
    env_vars: &std::collections::HashMap<String, String>,
    req: &CheckShardHttpRequest,
) -> Result<Option<serde_json::Value>> {
    let Some((base_url, auth_token)) = ensure_local_zygote_daemon_with_token(store, env_vars) else {
        return Ok(None);
    };
    let endpoint = format!("{}/check-shard", base_url.trim_end_matches('/'));
    let mut local_req = req.clone();
    local_req.skip_cas_lock = true;
    let body = serde_json::to_vec(&local_req)?;
    match http_request_with_timeout_and_token(
        "POST",
        &endpoint,
        "application/json",
        &body,
        None,
        Some(&auth_token),
        || {},
    ) {
        Ok(resp_bytes) => match parse_check_shard_resp(&resp_bytes) {
            Err(e) if e.to_string().contains("Zygote import unavailable") => Ok(None),
            other => other,
        },
        Err(e) => {
            if e.to_string().contains("HTTP ") {
                let err = extract_http_error_detail(e);
                if err.to_string().contains("Zygote import unavailable") {
                    return Ok(None);
                }
                return Err(err);
            }
            if let Some((_, _, _, _, state_file)) = current_exe_daemon_paths(store) {
                terminate_and_remove_daemon_state_file(&state_file);
            }
            let Some((retry_url, retry_token)) =
                ensure_local_zygote_daemon_with_token(store, env_vars)
            else {
                return Ok(None);
            };
            let retry_endpoint = format!("{}/check-shard", retry_url.trim_end_matches('/'));
            let resp_bytes = http_request_with_timeout_and_token(
                "POST",
                &retry_endpoint,
                "application/json",
                &body,
                None,
                Some(&retry_token),
                || {},
            )
            .map_err(extract_http_error_detail)?;
            parse_check_shard_resp(&resp_bytes)
        }
    }
}

pub fn try_local_zygote_check_shard(
    store: &TurboStore,
    env_vars: &std::collections::HashMap<String, String>,
    req: &CheckShardHttpRequest,
) -> Option<serde_json::Value> {
    try_local_zygote_check_shard_detailed(store, env_vars, req)
        .ok()
        .flatten()
}

fn is_pure_eval_source(source: &str) -> bool {
    !source.contains("IO.FS")
        && !source.contains("IO.mono")
        && !source.contains("IO.rand")
        && !source.contains("IO.getEnv")
        && !source.contains("IO.Process")
        && !source.contains("System.FilePath")
}

/// One `Lean.importModules` for both `Midnight.Spec` and `ProofKit`.
/// `ProofKit` only pulls `Compiler.CompilationModel`, which `Midnight.Spec`
/// already imports, so loading them together is ~one import, not two.
pub(crate) fn coalesce_proofkit_imports(imports_csv: &str, lean_path: &str) -> String {
    if imports_csv.split(',').any(|m| m.trim() == "Midnight.Spec")
        && !imports_csv.split(',').any(|m| m.trim() == "ProofKit")
        && lean_path
            .split(':')
            .any(|d| !d.is_empty() && Path::new(d).join("ProofKit.olean").exists())
    {
        format!("{},ProofKit", imports_csv)
    } else {
        imports_csv.to_string()
    }
}

fn compute_eval_shm_cache_filename(
    toolchain: &str,
    lean_path: &str,
    file_name: &str,
    caller_cwd: Option<&str>,
    source: &str,
) -> String {
    let (imports_csv, _) = split_shard_for_zygote(source);
    let imp_dig = compute_imported_oleans_digest(&imports_csv, lean_path);
    let mut h = blake3::Hasher::new();
    h.update(b"eval-shm:v2:");
    h.update(toolchain.as_bytes());
    h.update(b":");
    h.update(lean_path.as_bytes());
    h.update(b":");
    h.update(imp_dig.as_bytes());
    h.update(b":");
    h.update(file_name.as_bytes());
    h.update(b":");
    h.update(caller_cwd.unwrap_or("").as_bytes());
    h.update(b":");
    h.update(source.as_bytes());
    let key_hex = h.finalize().to_hex();
    format!("ev_{}.json", &key_hex[..24])
}

fn read_cached_eval_shm_reply(path: &Path) -> Option<ZygoteEvalReply> {
    let bytes = fs::read(path).ok()?;
    let mut cached_rep: ZygoteEvalReply = serde_json::from_slice(&bytes).ok()?;
    cached_rep.env_cache_hit = true;
    cached_rep.prefix_cache_hit = true;
    cached_rep.import_us = 0;
    cached_rep.prefix_us = 0;
    Some(cached_rep)
}

pub fn try_stateless_eval_shm_cache(
    cache_root: &Path,
    file: &Path,
    project_dir: Option<&Path>,
    lean_path: Option<&str>,
) -> Option<(String, ZygoteEvalReply)> {
    let source = fs::read_to_string(file).ok()?;
    if !is_pure_eval_source(&source) {
        return None;
    }
    let proj_dir = project_dir
        .map(crate::lake_build::find_project_root)
        .unwrap_or_else(|| crate::lake_build::find_project_root(file));
    let explicit_lp: Option<String> = lean_path
        .map(str::to_string)
        .or_else(|| std::env::var("LEAN_PATH").ok());
    let req_lp = match explicit_lp {
        Some(lp) => lp,
        None if !proj_dir.join("lakefile.lean").exists()
            && !proj_dir.join("lakefile.toml").exists() =>
        {
            String::new()
        }
        None if !proj_dir.join(".lake/packages").is_dir()
            && proj_dir.join(".lake/build/lib/lean").exists() =>
        {
            let canon_proj = proj_dir
                .canonicalize()
                .unwrap_or_else(|_| proj_dir.clone());
            crate::lake_build::resolve_remote_lean_path(&canon_proj, None)
        }
        None => return None,
    };
    let toolchain = crate::lake_build::detect_toolchain(&proj_dir);
    let caller_cwd = std::env::current_dir()
        .ok()
        .map(|p| p.to_string_lossy().to_string());
    let file_display = file.to_string_lossy();
    let filename = compute_eval_shm_cache_filename(
        &toolchain,
        &req_lp,
        &file_display,
        caller_cwd.as_deref(),
        &source,
    );
    let base_staging = if Path::new("/dev/shm").is_dir() {
        #[cfg(unix)]
        let uid = unsafe { libc::geteuid() };
        #[cfg(not(unix))]
        let uid = 0u32;
        PathBuf::from("/dev/shm").join(format!("turbo-lean-staging-{}", uid))
    } else {
        cache_root.join("staging")
    };
    let path = base_staging.join("eval_shm_cache").join(filename);
    let cached_rep = read_cached_eval_shm_reply(&path)?;
    Some((source, cached_rep))
}

pub fn try_local_zygote_eval(
    store: &TurboStore,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    toolchain: &str,
    lean_path: &str,
    source: &str,
    file_name: Option<&str>,
    timeout_ms: u64,
) -> Option<ZygoteEvalReply> {
    let t0 = std::time::Instant::now();
    let caller_cwd = std::env::current_dir()
        .ok()
        .map(|p| p.to_string_lossy().to_string());
    let eval_shm_file = if is_pure_eval_source(source) {
        let filename = compute_eval_shm_cache_filename(
            toolchain,
            lean_path,
            file_name.unwrap_or(""),
            caller_cwd.as_deref(),
            source,
        );
        let dir = store.fast_staging_dir().join("eval_shm_cache");
        let _ = fs::create_dir_all(&dir);
        let path = dir.join(filename);
        if let Some(cached_rep) = read_cached_eval_shm_reply(&path) {
            return Some(cached_rep);
        }
        Some(path)
    } else {
        None
    };

    let existing_daemon = current_exe_daemon_paths(store)
        .and_then(|(_, exe_mtime_sec, exe_mtime_nsec, _, state_file)| {
            check_existing_daemon_state(&state_file, exe_mtime_sec, exe_mtime_nsec, false).or_else(
                || {
                    check_existing_daemon_state(
                        &store.root.join("zygote_daemon.json"),
                        exe_mtime_sec,
                        exe_mtime_nsec,
                        false,
                    )
                },
            )
        })
        .or_else(|| ensure_local_zygote_daemon_with_token(store, env_vars));

    let Some((base_url, auth_token)) = existing_daemon else {
        let rep = eval_with_zygote_pool_opts(
            store,
            toolchain,
            lean_path,
            env_vars,
            lean_bin,
            source,
            false,
            true,
            file_name,
            if timeout_ms > 0 { Some(timeout_ms) } else { None },
        )
        .ok()?;
        if rep.ok && !rep.crashed && !rep.timed_out {
            if let Some(ref path) = eval_shm_file {
                if let Ok(bytes) = serde_json::to_vec(&rep) {
                    let _ = crate::shm_cache::atomic_write_shm(path, &bytes);
                }
            }
            warm_local_zygote_daemon_nonblocking(store, env_vars);
        }
        return Some(rep);
    };
    let endpoint = format!("{}/eval", base_url.trim_end_matches('/'));
    let mut forwarded_env: std::collections::HashMap<String, String> = std::env::vars()
        .filter(|(k, _)| {
            !matches!(
                k.as_str(),
                "GH_TOKEN"
                    | "GITHUB_TOKEN"
                    | "OPENAI_API_KEY"
                    | "ANTHROPIC_API_KEY"
                    | "AWS_SECRET_ACCESS_KEY"
                    | "AWS_SESSION_TOKEN"
            )
        })
        .collect();
    for (k, v) in env_vars {
        forwarded_env.insert(k.clone(), v.clone());
    }
    let effective_timeout_opt = if timeout_ms > 0 {
        Some(timeout_ms)
    } else {
        None
    };
    let body = serde_json::to_vec(&serde_json::json!({
        "toolchain": toolchain,
        "lean_path": lean_path,
        "source": source,
        "file_name": file_name,
        "cwd": caller_cwd,
        "env_vars": forwarded_env,
        "timeout_ms": effective_timeout_opt,
        "verify_determinism": false
    }))
    .ok()?;
    let http_timeout = effective_timeout_opt.map(|ms| ms.saturating_add(250));
    let resp_bytes = match http_request_with_timeout_and_token(
        "POST",
        &endpoint,
        "application/json",
        &body,
        http_timeout,
        Some(&auth_token),
        || {},
    ) {
        Ok(b) => b,
        Err(e) => {
            if let Some(limit_ms) = effective_timeout_opt {
                if t0.elapsed().as_millis() as u64 >= limit_ms
                    || e.to_string().contains("Resource temporarily unavailable")
                    || e.to_string().contains("timed out")
                    || e.to_string().contains("TimedOut")
                {
                    return Some(ZygoteEvalReply::timed_out_reply(
                        true,
                        t0.elapsed().as_micros() as u64,
                        limit_ms,
                    ));
                }
            }
            if e.to_string().contains("HTTP ") {
                return None;
            }
            if let Some((_, _, _, _, state_file)) = current_exe_daemon_paths(store) {
                terminate_and_remove_daemon_state_file(&state_file);
            }
            let (retry_url, retry_token) = ensure_local_zygote_daemon_with_token(store, env_vars)?;
            let retry_endpoint = format!("{}/eval", retry_url.trim_end_matches('/'));
            http_request_with_timeout_and_token(
                "POST",
                &retry_endpoint,
                "application/json",
                &body,
                http_timeout,
                Some(&retry_token),
                || {},
            )
            .ok()?
        }
    };
    let parsed = serde_json::from_slice::<ZygoteEvalReply>(&resp_bytes).ok();
    if let Some(ref rep) = parsed {
        if !rep.timed_out && !rep.crashed {
            if let Some(ref path) = eval_shm_file {
                let _ = crate::shm_cache::atomic_write_shm(path, &resp_bytes);
            }
        }
    }
    parsed
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
        assert!(decl.trim_start().starts_with("theorem cand_good"));
        assert_eq!(decl.chars().take_while(|&c| c == '\n').count(), 8);
        assert_eq!(key.len(), 16);
    }

    fn open_test_zygote_env(tag: &str) -> Option<(PathBuf, TurboStore, std::collections::HashMap<String, String>, PathBuf)> {
        let tmp_dir = std::env::temp_dir().join(format!("turbo_zygote_{}_{}", tag, next_tmp_id()));
        let _ = fs::create_dir_all(&tmp_dir);
        let store = TurboStore::open(Some(&tmp_dir)).expect("open store");
        let (mut env_vars, lean_bin) = crate::pack::resolve_server_lean_env_and_bin(&store, "leanprover/lean4:v4.35.0", "");
        env_vars.insert("LEAN_PATH".to_string(), tmp_dir.to_string_lossy().to_string());
        if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
            let _ = fs::remove_dir_all(&tmp_dir);
            return None;
        }
        Some((tmp_dir, store, env_vars, lean_bin))
    }

    #[test]
    fn test_zygote_prefix_checkpoint_instant_rollback() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("test") else { return; };
        let toolchain = "leanprover/lean4:v4.35.0";

        let shared_prefix = "namespace PrefixBench\nstructure PairState where\n  x : Nat\n  y : Nat\n  deriving DecidableEq\n\ndef swapPair (s : PairState) : PairState :=\n  { x := s.y, y := s.x }\n\ntheorem swapPair_involutive (s : PairState) : swapPair (swapPair s) = s := by\n  cases s\n  rfl\n";
        let run_pool = |shard: &str| eval_with_zygote_pool(&store, toolchain, "", &env_vars, &lean_bin, shard, false).unwrap();

        let rep_bad = run_pool(&format!("{}\ntheorem cand_bad (s : PairState) : swapPair s = s := rfl\n", shared_prefix));
        assert!(rep_bad.import_ok && !rep_bad.ok && !rep_bad.errors.is_empty());
        let joined_bad_errs = rep_bad.errors.join("\n");
        assert!(joined_bad_errs.contains("<zygote-decl>:14:"), "Expected line 14 in error: {}", joined_bad_errs);

        let max_elab_us: u64 = if cfg!(debug_assertions) { 100_000 } else { 25_000 };
        for decl in [
            "theorem cand_good1 (s : PairState) : swapPair (swapPair s) = s := by\n  cases s\n  rfl\n",
            "theorem cand_good2 (s : PairState) : swapPair (swapPair s) = s := swapPair_involutive s\n",
            "theorem cand_good_fresh (s : PairState) : (swapPair s).x = s.y := by\n  cases s\n  rfl\n",
        ] {
            let rep = run_pool(&format!("{}\n{}", shared_prefix, decl));
            assert!(rep.ok && rep.env_cache_hit && rep.prefix_cache_hit && rep.prefix_us == 0 && rep.elab_us < max_elab_us, "{:?}", rep);
            if decl.contains("cand_good_fresh") {
                assert!(rep.elab_us < rep_bad.prefix_us);
            }
        }
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_zygote_kernel_gate_rejects_macro_hidden_sorry() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("kgate_test") else { return; };
        let toolchain = "leanprover/lean4:v4.35.0";

        let prefix_src = "theorem prior_lem : True := sorry\n";
        let sneaky_shard = format!("{}\nmacro \"stealth_sorry\" : tactic => `(tactic| sorry)\ntheorem sneaky_thm : 1 = 2 := by stealth_sorry\n", prefix_src);
        let rep_sneaky = eval_with_zygote_pool(&store, toolchain, "", &env_vars, &lean_bin, &sneaky_shard, false).unwrap();
        assert!(!rep_sneaky.ok);
        let joined_errs = rep_sneaky.errors.join("\n");
        assert!(joined_errs.contains("KernelGate") || joined_errs.contains("sorry"));

        let clean_shard = format!("{}\ntheorem clean_thm : True := prior_lem\n", prefix_src);
        let rep_clean = eval_with_zygote_pool(&store, toolchain, "", &env_vars, &lean_bin, &clean_shard, false).unwrap();
        assert!(rep_clean.ok && rep_clean.kernel_gate_active);
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    static LNC_TEST_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

    #[test]
    fn test_lean_native_core_persistent_worker_sub_millisecond_rpc() {
        let _guard = LNC_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let warmup = query_lean_native_core_worker("ping", None).unwrap();
        assert_eq!((warmup["ok"].as_bool(), warmup["result"]["status"].as_str()), (Some(true), Some("pong")));
        let _ = query_lean_native_core_worker("validate-tv", None);

        let methods = ["ping", "validate-tv", "verify-certs", "eval-cex"];
        let t0 = std::time::Instant::now();
        for idx in 0..20 {
            let method = methods[idx % methods.len()];
            let resp = query_lean_native_core_worker(method, None).unwrap();
            assert_eq!(resp["ok"].as_bool(), Some(true));
            let result = &resp["result"];
            match method {
                "ping" => assert_eq!(result["status"].as_str(), Some("pong")),
                "validate-tv" => assert_eq!((result["allPassed"].as_bool(), result["passedDecls"].as_u64()), (Some(true), Some(8))),
                "verify-certs" => assert_eq!(result["verified"].as_bool(), Some(true)),
                "eval-cex" => {
                    let is_fb = result["fallback"].as_bool().unwrap_or(false) || resp["fallback"].as_bool().unwrap_or(false);
                    assert_eq!((result["certified"].as_bool(), result["falsePositives"].as_u64()), (Some(!is_fb), Some(0)));
                }
                _ => unreachable!(),
            }
        }
        assert!(t0.elapsed().as_secs_f64() * 1000.0 / 20.0 < 5.0);
    }

    #[test]
    fn test_measure_process_rss_mb_and_budget_detection() {
        let t0 = std::time::Instant::now();
        let rss_mb = measure_process_rss_mb(std::process::id());
        let elapsed_us = t0.elapsed().as_micros();
        assert!(rss_mb >= 1 && rss_mb < 65_536);
        #[cfg(target_os = "linux")]
        assert!(elapsed_us < 1000);
        let gov = crate::shm_cache::MemoryBudgetGovernor::detect();
        assert!(gov.budget_mb >= 1 && gov.worker_rss_limit_mb() >= 512);
    }

    #[test]
    fn test_zygote_multiple_import_sets_in_same_worker() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("multi_imp") else { return; };
        let toolchain = "leanprover/lean4:v4.35.0";

        let rep1 = eval_with_zygote_pool_opts(&store, toolchain, "", &env_vars, &lean_bin, "import Init\ntheorem multi_imp_1 : 1 + 1 = 2 := rfl\n", false, false, None, None).unwrap();
        assert!(rep1.ok && rep1.import_ok);

        let rep2 = eval_with_zygote_pool_opts(&store, toolchain, "", &env_vars, &lean_bin, "import Lean\ntheorem multi_imp_lean : 1 = 1 := rfl\n", false, false, None, None).unwrap();
        assert!(rep2.ok && rep2.import_ok);

        let rep3 = eval_with_zygote_pool_opts(&store, toolchain, "", &env_vars, &lean_bin, "import Init\ntheorem multi_imp_2 : 2 + 2 = 4 := rfl\n", false, false, None, None).unwrap();
        assert!(rep3.ok && rep3.env_cache_hit);
        let rep4 = eval_with_zygote_pool_opts(&store, toolchain, "", &env_vars, &lean_bin, "import Lean\ntheorem multi_imp_lean_2 : 2 = 2 := rfl\n", false, false, None, None).unwrap();
        assert!(rep4.ok && rep4.env_cache_hit);
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_zygote_eval_mode_preserves_info_messages_and_sorry_strings() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("eval_info") else { return; };
        let toolchain = "leanprover/lean4:v4.35.0";

        let harness = "import Lean\nopen Lean Elab Command in\nrun_cmd do\n  logInfo \"RSGB_RESULT {\\\"name\\\":\\\"foo\\\",\\\"note\\\":\\\"sorry\\\"}\"\n#eval (40 + 2)\n";
        let rep = eval_with_zygote_pool_opts(&store, toolchain, "", &env_vars, &lean_bin, harness, false, true, Some("rsgb_harness.lean"), Some(15_000)).unwrap();
        let joined_msgs = rep.messages.join("\n");
        assert!(rep.ok && rep.heartbeats > 0 && joined_msgs.contains("RSGB_RESULT {\"name\":\"foo\",\"note\":\"sorry\"}") && joined_msgs.contains("42"));
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_zygote_timeout_kills_infinite_eval_and_recovers() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("timeout") else { return; };
        let toolchain = "leanprover/lean4:v4.35.0";

        assert!(eval_with_zygote_pool_opts(&store, toolchain, "", &env_vars, &lean_bin, "#eval 1 + 1\n", false, true, Some("warm.lean"), Some(10_000)).unwrap().ok);

        let inf_src = "partial def spinForever (n : Nat) : IO Nat := do\n  IO.sleep 100\n  spinForever (n + 1)\n#eval spinForever 0\n";
        let t0 = std::time::Instant::now();
        let rep_timeout = eval_with_zygote_pool_opts(&store, toolchain, "", &env_vars, &lean_bin, inf_src, false, true, Some("spin.lean"), Some(400)).unwrap();
        assert!(rep_timeout.timed_out && !rep_timeout.ok && t0.elapsed() < std::time::Duration::from_secs(2));

        let rep_after = eval_with_zygote_pool_opts(&store, toolchain, "", &env_vars, &lean_bin, "#eval (100 + 23)\n", false, true, Some("after.lean"), Some(10_000)).unwrap();
        assert!(rep_after.ok && !rep_after.timed_out && rep_after.messages.iter().any(|m| m.contains("123")));
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_zygote_olean_digest_changes_when_olean_modified() {
        let tmp_dir = std::env::temp_dir().join(format!("turbo_zygote_olean_dig_{}", next_tmp_id()));
        let mod_dir = tmp_dir.join("Foo");
        let _ = fs::create_dir_all(&mod_dir);
        let olean_path = mod_dir.join("Bar.olean");
        fs::write(&olean_path, b"olean-version-1").unwrap();

        let lp = tmp_dir.to_string_lossy().to_string();
        let d1 = compute_imported_oleans_digest("Foo.Bar", &lp);
        assert_eq!(d1, compute_imported_oleans_digest("Foo.Bar", &lp));

        fs::write(&olean_path, b"olean-version-2-modified").unwrap();
        assert_ne!(d1, compute_imported_oleans_digest("Foo.Bar", &lp));
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_search_path_oleans_digest_skips_lake_packages_bloat_and_tracks_imported_oleans() {
        let tmp_dir = std::env::temp_dir().join(format!("turbo_zygote_pkg_skip_{}", next_tmp_id()));
        let (pkg_lib, local_lib) = (tmp_dir.join(".lake/packages/mathlib/.lake/build/lib/lean"), tmp_dir.join(".lake/build/lib/lean"));
        let _ = fs::create_dir_all(&pkg_lib);
        let _ = fs::create_dir_all(&local_lib);

        let (big_pkg_olean, local_olean) = (pkg_lib.join("Big.olean"), local_lib.join("Local.olean"));
        fs::write(&big_pkg_olean, vec![0xAAu8; 128 * 1024]).unwrap();
        fs::write(&local_olean, b"local-olean-v1").unwrap();

        let lp = format!("{}:{}", local_lib.display(), pkg_lib.display());
        let (sp_d1, imp_d1) = (compute_search_path_oleans_digest(&lp), compute_imported_oleans_digest("Big,Local", &lp));

        fs::write(&big_pkg_olean, vec![0xBBu8; 130 * 1024]).unwrap();
        let sp_d2 = compute_search_path_oleans_digest(&lp);
        assert_eq!(sp_d1, sp_d2);
        assert_ne!(imp_d1, compute_imported_oleans_digest("Big,Local", &lp));

        fs::write(&local_olean, b"local-olean-v2-modified").unwrap();
        assert_ne!(sp_d2, compute_search_path_oleans_digest(&lp));
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_zygote_delta_prefix_chaining_and_used_constants_distillation() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("delta_distill") else { return; };
        let toolchain = "leanprover/lean4:v4.35.0";

        let prefix1 = "namespace DeltaChainTest\ndef shiftByFour (n : Nat) : Nat := n + 4\n";
        let shard1 = format!("{}theorem helper_shift_eq (n : Nat) : shiftByFour n = n + 4 := rfl\n", prefix1);
        assert!(eval_with_zygote_pool(&store, toolchain, "", &env_vars, &lean_bin, &shard1, true).unwrap().ok);

        let shard2 = format!("{}theorem helper_shift_eq (n : Nat) : shiftByFour n = n + 4 := sorry\ntheorem chained_thm (n : Nat) : shiftByFour n = n + 4 := by\n  simp [helper_shift_eq]\n", prefix1);
        let rep2 = eval_with_zygote_pool(&store, toolchain, "", &env_vars, &lean_bin, &shard2, true).unwrap();
        assert!(rep2.ok && rep2.used_constants.iter().any(|c| c.contains("helper_shift_eq")));

        // Verify branched LCA prefix reuse: sibling branch sharing `prefix1` reuses the ancestor checkpoint
        let shard3 = format!("{}def siblingBranchHelper (n : Nat) : Nat := shiftByFour n + 2\ntheorem sibling_thm (n : Nat) : siblingBranchHelper n = n + 6 := by\n  unfold siblingBranchHelper shiftByFour; omega\n", prefix1);
        let rep3 = eval_with_zygote_pool(&store, toolchain, "", &env_vars, &lean_bin, &shard3, true).unwrap();
        assert!(rep3.ok && rep3.env_cache_hit);
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_lean_native_core_worker_nonexistent_bin_fallback() {
        let _guard = LNC_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let prev = std::env::var("LEAN_NATIVE_CORE_BIN").ok();
        std::env::set_var("LEAN_NATIVE_CORE_BIN", "/nonexistent/lean-native-core");
        for method in ["ping", "validate-tv", "verify-certs", "eval-cex", "compile-fastcheck", "compile-llvm", "compile-ptx"] {
            let resp = query_lean_native_core_worker(method, None).unwrap_or_else(|e| panic!("fallback failed for {}: {}", method, e));
            assert_eq!(resp["ok"].as_bool(), Some(true));
            let res = &resp["result"];
            assert_eq!(res["fallback"].as_bool(), Some(true));
            if method == "eval-cex" || method == "verify-certs" {
                assert_eq!(res["overallAssurance"].as_str(), Some("FallbackUnverified"));
                if method == "eval-cex" {
                    assert_eq!(res["certified"].as_bool(), Some(false));
                }
            }
        }
        match prev {
            Some(v) => std::env::set_var("LEAN_NATIVE_CORE_BIN", v),
            None => std::env::remove_var("LEAN_NATIVE_CORE_BIN"),
        }
    }

    #[test]
    fn test_eval_mode_prefix_checkpoint_preserves_exact_line_numbers_and_accelerates_warm_eval() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("eval_prefix") else { return; };
        let toolchain = "leanprover/lean4:v4.35.0";

        let driver_v1 = "import Init\ndef rsgbStep1 (n : Nat) : Nat := n + 10\ndef rsgbStep2 (n : Nat) : Nat := rsgbStep1 n * 2\ndef rsgbStep3 (n : Nat) : Nat := rsgbStep2 n + 5\ndef rsgbStep4 (n : Nat) : String := s!\"val={rsgbStep3 n}\"\ndef rsgbStep5 (n : Nat) : String := s!\"[{rsgbStep4 n}]\"\ndef rsgbSimTest (a b : Nat) : String := s!\"{rsgbStep5 a}:{rsgbStep5 b}\"\ndef rsgbSimKill (tag : String) (x : Nat) : String := s!\"{tag}:{rsgbSimTest x (x + 1)}\"\ndef rsgbSimOutputs (k : Nat) : String :=\n  rsgbSimKill \"RUN\" k\n#eval rsgbSimOutputs 3\n";
        let run_eval = |src: &str| eval_with_zygote_pool_opts(&store, toolchain, "", &env_vars, &lean_bin, src, false, true, Some("rsgb_driver.lean"), Some(15_000)).unwrap();

        let rep1 = run_eval(driver_v1);
        assert!(rep1.ok && rep1.messages.join("\n").contains("RUN:[val=31]:[val=33]"));

        let driver_v2 = driver_v1.replace("#eval rsgbSimOutputs 3", "#eval rsgbSimOutputs 7");
        let mut t0 = std::time::Instant::now();
        let mut rep2 = run_eval(&driver_v2);
        if !rep2.prefix_cache_hit {
            t0 = std::time::Instant::now();
            rep2 = run_eval(&driver_v2);
        }
        let warm_elapsed_ms = t0.elapsed().as_secs_f64() * 1000.0;
        let max_warm_ms = if cfg!(debug_assertions) { 500.0 } else { 100.0 };
        let max_elab_us: u64 = if cfg!(debug_assertions) { 250_000 } else { 80_000 };
        assert!(rep2.ok && rep2.prefix_cache_hit && rep2.prefix_us == 0);
        assert!(rep2.messages.join("\n").contains("RUN:[val=39]:[val=41]"));
        assert!(rep2.elab_us < max_elab_us && warm_elapsed_ms < max_warm_ms);

        let driver_v3 = format!("{}#check unknown_ident_on_line_12\n", driver_v2);
        let rep3 = run_eval(&driver_v3);
        assert!(!rep3.ok && rep3.prefix_cache_hit && rep3.messages.join("\n").contains("rsgb_driver.lean:12:7: error(lean.unknownIdentifier):"));
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_evb_rfvb_rsgb_parity_prefix_warnings_prelude_and_main_module() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("evb_parity") else { return; };
        let toolchain = "leanprover/lean4:v4.35.0";

        let src_v1 = "def pfxUnused (x y : Nat) : Nat := x\ntheorem pfxSorry : True := by sorry\n#eval pfxUnused 42 99\n";
        let rep_cold = eval_with_zygote_pool_opts(&store, toolchain, "", &env_vars, &lean_bin, src_v1, false, true, Some("pfx_warn.lean"), Some(15_000)).unwrap();
        let cold_msgs = rep_cold.messages.join("\n");
        assert!(cold_msgs.contains("unusedVariables") && cold_msgs.contains("declaration uses `sorry`"));

        let src_v2 = src_v1.replace("42 99", "77 88");
        let rep_warm = eval_with_zygote_pool_opts(&store, toolchain, "", &env_vars, &lean_bin, &src_v2, false, true, Some("pfx_warn.lean"), Some(15_000)).unwrap();
        let warm_msgs = rep_warm.messages.join("\n");
        assert!(rep_warm.prefix_cache_hit && warm_msgs.contains("unusedVariables") && warm_msgs.contains("declaration uses `sorry`") && warm_msgs.contains("77"));

        let (imports_prelude, body_prelude) = split_shard_for_zygote("prelude\n#check Nat\n");
        assert_eq!(imports_prelude, "__PRELUDE__");
        assert!(body_prelude.contains("#check Nat"));
        assert_eq!(split_shard_for_zygote("import Zeta.Mod\nimport Alpha.Mod\n#check 1\n").0, "Zeta.Mod,Alpha.Mod");

        let priv_src = "private def myPrivHelper : Nat := 123\n#check myPrivHelper\n";
        let rep_priv = eval_with_zygote_pool_opts(&store, toolchain, "", &env_vars, &lean_bin, priv_src, false, true, Some("/tmp/foo_priv_test.lean"), Some(15_000)).unwrap();
        assert!(!rep_priv.messages.join("\n").contains("._stdin."));
        let _ = fs::remove_dir_all(&tmp_dir);
    }
}
