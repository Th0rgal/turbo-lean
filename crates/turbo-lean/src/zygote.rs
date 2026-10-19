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

#[derive(Debug, Clone, Deserialize)]
pub struct ZygoteEvalReply {
    pub ok: bool,
    #[serde(default)]
    pub import_ok: bool,
    pub env_cache_hit: bool,
    #[serde(default)]
    pub prefix_cache_hit: bool,
    pub import_us: u64,
    #[serde(default)]
    pub prefix_us: u64,
    pub elab_us: u64,
    pub errors: Vec<String>,
}

struct ZygoteChild {
    _child: std::process::Child,
    stdin: std::process::ChildStdin,
    stdout: BufReader<std::process::ChildStdout>,
    warm_prefixes: std::collections::HashSet<String>,
}

static ZYGOTE_POOL: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashMap<(String, String, String), Vec<ZygoteChild>>>,
> = std::sync::OnceLock::new();

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

fn ensure_zygote_binary(
    store: &TurboStore,
    lean_bin: &Path,
    env_vars: &std::collections::HashMap<String, String>,
) -> Result<std::path::PathBuf> {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"turbo-zygote:v2:shared:");
    hasher.update(std::env::consts::ARCH.as_bytes());
    hasher.update(ZYGOTE_WORKER_LEAN_SRC.as_bytes());
    let bin_name = format!("turbo_zygote_{}", &hasher.finalize().to_hex()[..16]);
    let bin_dir = store.root.join("fastcheck_bins");
    fs::create_dir_all(&bin_dir)?;
    let cached_bin = bin_dir.join(&bin_name);
    if cached_bin.exists() {
        return Ok(cached_bin);
    }

    let shm_staging = store.fast_staging_dir();
    let shm_bin_dir = shm_staging.join("zygote_daemon_cas").join("fastcheck_bins");
    let _ = fs::create_dir_all(&shm_bin_dir);
    let shm_cached_bin = shm_bin_dir.join(&bin_name);
    let tmp_id = next_tmp_id();

    let copy_shm_to_local = |shm_src: &Path| -> Option<PathBuf> {
        if !shm_src.exists() {
            return None;
        }
        let tmp_copy = bin_dir.join(format!(".{}.{}.tmp", bin_name, tmp_id));
        if fs::copy(shm_src, &tmp_copy).is_ok() {
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                if let Ok(m) = fs::metadata(&tmp_copy) {
                    let mut p = m.permissions();
                    p.set_mode(0o755);
                    let _ = fs::set_permissions(&tmp_copy, p);
                }
            }
            let _ = fs::rename(&tmp_copy, &cached_bin);
            let _ = fs::remove_file(&tmp_copy);
            if cached_bin.exists() {
                return Some(cached_bin.clone());
            }
        }
        None
    };

    if let Some(p) = copy_shm_to_local(&shm_cached_bin) {
        return Ok(p);
    }

    let lock_path = shm_bin_dir.join(format!("{}.lock", bin_name));
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

    if let Some(p) = copy_shm_to_local(&shm_cached_bin) {
        return Ok(p);
    }

    // Compile embedded ZygoteWorker.lean via `lean -c` + `leanc -O3 -lleanshared -Wl,-rpath,<sysroot>/lib/lean` (58 KB binary!)
    let leanc_bin = lean_bin
        .parent()
        .map(|p| p.join("leanc"))
        .filter(|c| c.exists())
        .unwrap_or_else(|| std::path::PathBuf::from("leanc"));
    let tmp_lean = shm_staging.join(format!("ZygoteWorker_{}.lean", tmp_id));
    let tmp_c = shm_staging.join(format!("ZygoteWorker_{}.c", tmp_id));
    let tmp_bin = shm_staging.join(format!("ZygoteWorker_{}.bin", tmp_id));
    fs::write(&tmp_lean, ZYGOTE_WORKER_LEAN_SRC)?;

    let out1 = Command::new(lean_bin)
        .arg(format!("--root={}", shm_staging.display()))
        .arg("-c")
        .arg(&tmp_c)
        .arg(&tmp_lean)
        .current_dir(&shm_staging)
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
        .current_dir(&shm_staging)
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
        anyhow::bail!(
            "`leanc -O3 -lleanshared` failed on ZygoteWorker.c:\n{}",
            String::from_utf8_lossy(&out2.stderr)
        );
    }
    let shm_tmp = shm_bin_dir.join(format!(".{}.{}.tmp", bin_name, tmp_id));
    if fs::copy(&tmp_bin, &shm_tmp).is_ok() {
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            if let Ok(m) = fs::metadata(&shm_tmp) {
                let mut p = m.permissions();
                p.set_mode(0o755);
                let _ = fs::set_permissions(&shm_tmp, p);
            }
        }
        let _ = fs::rename(&shm_tmp, &shm_cached_bin);
        let _ = fs::remove_file(&shm_tmp);
    }
    if fs::rename(&tmp_bin, &cached_bin).is_err() {
        let local_tmp = bin_dir.join(format!(".{}.{}.tmp", bin_name, tmp_id));
        fs::copy(&tmp_bin, &local_tmp)?;
        let _ = fs::rename(&local_tmp, &cached_bin);
        let _ = fs::remove_file(&local_tmp);
        let _ = fs::remove_file(&tmp_bin);
    }
    Ok(cached_bin)
}

static ZYGOTE_LEAN_PATH_CACHE: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashMap<(String, String, std::path::PathBuf), (String, bool)>>,
> = std::sync::OnceLock::new();

pub fn eval_with_zygote_pool(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    shard_source: &str,
    allow_stub: bool,
) -> Result<ZygoteEvalReply> {
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

    let (effective_lean_path, has_all_turbo_lean_oleans) = if let Some(pair) = cached_lp {
        pair
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
        let has_oleans = path_parts.iter().any(|p| {
            let root = Path::new(p);
            root.join("TurboLean/Assembler.olean").exists()
                && root.join("TurboLean/FastCheck.olean").exists()
                && root.join("TurboLean/Inspector.olean").exists()
                && root.join("TurboLean/Reflection.olean").exists()
        });
        let eff = path_parts.join(":");
        if let Ok(mut g) = lp_cache_mutex.lock() {
            g.insert(lp_cache_key, (eff.clone(), has_oleans));
        }
        (eff, has_oleans)
    };

    let (mut imports_csv, body_code) = split_shard_for_zygote(shard_source);
    let is_turbo_lean_subset = !imports_csv.is_empty()
        && imports_csv.split(',').any(|m| m.starts_with("TurboLean."))
        && imports_csv.split(',').all(|m| {
            matches!(
                m,
                "TurboLean.Assembler"
                    | "TurboLean.FastCheck"
                    | "TurboLean.Inspector"
                    | "TurboLean.Reflection"
                    | "Lean.Elab.Command"
                    | "Lean.Util.CollectAxioms"
            )
        });
    let unified_turbo_env = is_turbo_lean_subset
        && has_all_turbo_lean_oleans
        && !body_code.contains("structure Word256")
        && !body_code.contains("inductive StorageKey")
        && !body_code.contains("def allowedStandardAxioms")
        && !body_code.contains("def exprHeadTag");
    if unified_turbo_env {
        imports_csv =
            "TurboLean.Assembler,TurboLean.FastCheck,TurboLean.Inspector,TurboLean.Reflection"
                .to_string();
    }
    let pool_key = (
        toolchain.to_string(),
        if unified_turbo_env {
            "unified_turbo_lean".to_string()
        } else {
            effective_lean_path.clone()
        },
        imports_csv.clone(),
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
        Ok(ZygoteChild {
            _child: child,
            stdin,
            stdout,
            warm_prefixes: std::collections::HashSet::new(),
        })
    };

    let run_worker_req = |worker: &mut ZygoteChild, req_line: &str| -> Result<ZygoteEvalReply> {
        worker.stdin.write_all(req_line.as_bytes())?;
        worker.stdin.flush()?;
        let mut resp_line = String::new();
        let n = worker.stdout.read_line(&mut resp_line)?;
        if n == 0 {
            anyhow::bail!("Zygote worker closed stdout unexpectedly");
        }
        let parsed: ZygoteEvalReply = serde_json::from_str(resp_line.trim())
            .with_context(|| format!("Invalid JSON from Zygote worker: {}", resp_line.trim()))?;
        Ok(parsed)
    };

    let pool_mutex =
        ZYGOTE_POOL.get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));

    if body_code.contains("-- namespace _TurboCrossFileShard_1") {
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

            let results: Vec<(ZygoteChild, Result<ZygoteEvalReply>)> = std::thread::scope(|s| {
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
            {
                let mut pool = pool_mutex
                    .lock()
                    .map_err(|_| anyhow::anyhow!("ZygotePool mutex poisoned"))?;
                let vec = pool.entry(pool_key).or_default();
                for (w, res) in results {
                    match res {
                        Ok(r) => {
                            vec.push(w);
                            replies.push(r);
                        }
                        Err(e) => {
                            if first_err.is_none() {
                                first_err = Some(e);
                            }
                        }
                    }
                }
            }
            if let Some(e) = first_err {
                return Err(e);
            }
            let import_ok = replies.iter().all(|r| r.import_ok);
            let ok = replies.iter().all(|r| r.ok);
            let env_cache_hit = replies.iter().all(|r| r.env_cache_hit);
            let prefix_cache_hit = replies.iter().all(|r| r.prefix_cache_hit);
            let import_us = replies.iter().map(|r| r.import_us).max().unwrap_or(0);
            let prefix_us = replies.iter().map(|r| r.prefix_us).max().unwrap_or(0);
            let elab_us = replies.iter().map(|r| r.elab_us).max().unwrap_or(0);
            let errors: Vec<String> = replies.into_iter().flat_map(|r| r.errors).collect();
            return Ok(ZygoteEvalReply {
                ok,
                import_ok,
                env_cache_hit,
                prefix_cache_hit,
                import_us,
                prefix_us,
                elab_us,
                errors,
            });
        }
    }

    let (req_line, active_prefix_key) = if let Some((prefix_code, decl_code, prefix_key)) =
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
    };

    let mut worker = {
        let mut pool = pool_mutex
            .lock()
            .map_err(|_| anyhow::anyhow!("ZygotePool mutex poisoned"))?;
        if let Some(vec) = pool.get_mut(&pool_key) {
            if let Some(ref pk) = active_prefix_key {
                if let Some(pos) = vec.iter().rposition(|w| w.warm_prefixes.contains(pk)) {
                    Some(vec.swap_remove(pos))
                } else {
                    vec.pop()
                }
            } else {
                vec.pop()
            }
        } else {
            None
        }
    };
    if worker.is_none() {
        worker = Some(spawn_zygote_worker()?);
    }
    let mut w = worker.unwrap();
    let io_res = run_worker_req(&mut w, &req_line);
    if let Ok(ref rep) = io_res {
        if rep.import_ok {
            if let Some(pk) = active_prefix_key {
                w.warm_prefixes.insert(pk);
            }
        }
        if let Ok(mut pool) = pool_mutex.lock() {
            pool.entry(pool_key).or_default().push(w);
        }
    }
    io_res
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
        Err(_) => {
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
            rep_good1.elab_us < 1000,
            "expected sub-millisecond declaration check on warm prefix checkpoint, got {} µs",
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
            rep_good2.elab_us < 200,
            "expected < 200 µs declaration check on warm prefix checkpoint, got {} µs",
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

        let _ = fs::remove_dir_all(&tmp_dir);
    }
}

