//! HTTP Remote Coordinator (`turbo-lean serve`) for CAS Delta Sync, Zygote Shard Verification,
//! and Perceus / CUDA Fast-Check Offload.

use crate::db::{now_unix, TurboStore};
use crate::pack::{
    compile_fastcheck_c_to_bin, compute_fastcheck_binary_key, compute_fastcheck_binary_key_parts,
    encode_hex_bytes, ensure_shared_fastcheck_out, export_pack_filtered_bytes,
    export_pack_filtered_with_mode, get_store_manifest, import_pack_bytes_with_policy,
    is_valid_cached_fastcheck_out, next_tmp_id, resolve_pack_import_trust_domain,
    run_or_read_cached_fastcheck_bin, save_compiled_bin_to_shared, shared_cas_blobs_dir,
    shared_fastcheck_cgen_path, try_import_from_shared_cas_with_domain, try_parse_v3_header,
    try_populate_cached_bin_from_shared, CheckShardHttpRequest, CheckShardsBatchRequest,
    CheckShardsBatchResponse, DeltaManifest, ExportDeltaRequest, FastCheckHttpRequest,
    FASTCHECK_NO_MAIN_SUFFIX, FASTCHECK_PRELUDE_HARNESS,
};
use crate::zygote::LocalZygoteDaemonInfo;
use anyhow::{Context, Result};
use std::collections::HashSet;
use std::fs;
use std::io::{BufRead, BufReader, Read, Write};
use std::net::TcpListener;
use std::path::Path;
use std::process::Command;

struct ServerActivity {
    last_completed: std::time::Instant,
    active: usize,
}

impl ServerActivity {
    fn admit(&mut self) -> bool {
        if self.active >= 64 {
            return false;
        }
        self.active += 1;
        true
    }

    fn complete(&mut self, now: std::time::Instant) {
        self.last_completed = now;
        self.active -= 1;
    }

    fn expired(&self, now: std::time::Instant, ttl: Option<std::time::Duration>) -> bool {
        self.active == 0 && ttl.is_some_and(|ttl| now.duration_since(self.last_completed) >= ttl)
    }
}

#[cfg(test)]
mod tests {
    use super::ServerActivity;
    use std::time::{Duration, Instant};

    #[test]
    fn admission_and_expiry_share_one_state_machine() {
        let start = Instant::now();
        let ttl = Duration::from_secs(1);
        let boundary = start + ttl;
        let mut state = ServerActivity {
            last_completed: start,
            active: 0,
        };
        assert!(!state.expired(boundary - Duration::from_nanos(1), Some(ttl)));
        assert!(state.expired(boundary, Some(ttl)));
        // accept runs before the expiry check under the same lock. A connection
        // admitted exactly at the boundary must prevent shutdown, however long it runs.
        assert!(state.admit());
        assert!(!state.expired(boundary, Some(ttl)));
        assert!(!state.expired(boundary + ttl * 10, Some(ttl)));
        assert!(state.admit());
        state.complete(boundary + ttl * 10);
        assert!(!state.expired(boundary + ttl * 20, Some(ttl)));
        let completed = boundary + ttl * 20;
        state.complete(completed);
        assert!(!state.expired(completed + ttl - Duration::from_nanos(1), Some(ttl)));
        assert!(state.expired(completed + ttl, Some(ttl)));
        assert!(!state.expired(completed + ttl, None));
        for _ in 0..64 {
            assert!(state.admit());
        }
        assert!(!state.admit());
        assert_eq!(state.active, 64);
    }
}

fn is_loopback_listen_addr(addr: &str) -> bool {
    let trimmed = addr.trim();
    if let Ok(sa) = trimmed.parse::<std::net::SocketAddr>() {
        return sa.ip().is_loopback();
    }
    let host = match trimmed.rsplit_once(':') {
        Some((h, port)) if !port.is_empty() && port.bytes().all(|b| b.is_ascii_digit()) => h,
        _ => trimmed,
    };
    host == "localhost"
        || host == "[::1]"
        || host
            .parse::<std::net::IpAddr>()
            .map(|ip| ip.is_loopback())
            .unwrap_or(false)
}

fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    let mut diff = a.len() ^ b.len();
    let max_len = a.len().max(b.len());
    for i in 0..max_len {
        let ba = a.get(i).copied().unwrap_or(0);
        let bb = b.get(i).copied().unwrap_or(0);
        diff |= (ba ^ bb) as usize;
    }
    diff == 0
}

pub fn is_safe_lean_env_key(key: &str) -> bool {
    matches!(
        key,
        "LEAN_STACK_SIZE_KB"
            | "TURBO_LEAN_ZYGOTE_MAX_CHECKPOINTS"
            | "TURBO_LEAN_CALLER_CWD"
            | "LEAN_NATIVE_TELEMETRY"
            | "LEAN_NATIVE_TELEMETRY_DIR"
            | "SANDBOXED_TELEMETRY_BATCH_ONLY"
            | "HOME"
            | "TMPDIR"
            | "LANG"
            | "LC_ALL"
            | "TERM"
            | "NO_COLOR"
            | "RAYON_NUM_THREADS"
    )
}

pub fn validate_precomputed_bin_key(key: &str) -> Result<()> {
    if key.is_empty() || key.len() > 128 {
        anyhow::bail!("Invalid precomputed_bin_key length");
    }
    if key.starts_with('.') || key.contains("..") {
        anyhow::bail!("Invalid precomputed_bin_key traversal segment");
    }
    if !key
        .bytes()
        .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'.' | b'_' | b'-'))
    {
        anyhow::bail!("Invalid characters in precomputed_bin_key");
    }
    Ok(())
}

/// Lightweight HTTP Server (`turbo-lean serve`) for remote CAS sync & GPU/CPU offload (e.g., on DGX Spark).
pub fn serve_cas_http(
    store_root: Option<&Path>,
    listen_addr: &str,
    gpu_enable: bool,
) -> Result<()> {
    serve_cas_http_with_auth(store_root, listen_addr, gpu_enable, None, false)
}

pub(crate) fn resolve_server_auth_token(
    api_token: Option<&str>,
    is_daemon: bool,
    env_api_token: Option<&str>,
    env_daemon_token: Option<&str>,
) -> Option<String> {
    api_token
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .or_else(|| {
            if is_daemon {
                env_daemon_token
                    .map(|s| s.trim().to_string())
                    .filter(|s| !s.is_empty())
            } else {
                None
            }
        })
        .or_else(|| {
            env_api_token
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
        })
        .or_else(|| {
            env_daemon_token
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
        })
}

pub fn serve_cas_http_with_auth(
    store_root: Option<&Path>,
    listen_addr: &str,
    gpu_enable: bool,
    api_token: Option<&str>,
    allow_unauthenticated_local: bool,
) -> Result<()> {
    let is_loopback_bind = is_loopback_listen_addr(listen_addr);
    let is_daemon = std::env::var("TURBO_LEAN_DAEMON").is_ok();
    let env_api_tok = std::env::var("TURBO_LEAN_API_TOKEN").ok();
    let env_daemon_tok = std::env::var("TURBO_LEAN_DAEMON_TOKEN").ok();
    let resolved_token = resolve_server_auth_token(
        api_token,
        is_daemon,
        env_api_tok.as_deref(),
        env_daemon_tok.as_deref(),
    );
    let env_allow_unauth_local = std::env::var("TURBO_LEAN_ALLOW_UNAUTHENTICATED_LOCAL")
        .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        .unwrap_or(false);
    let effective_allow_unauth_local =
        (allow_unauthenticated_local || env_allow_unauth_local) && is_loopback_bind;
    if resolved_token.is_none() && !effective_allow_unauth_local && !is_loopback_bind {
        anyhow::bail!(
            "Refusing to bind unauthenticated turbo-lean server to non-loopback address `{}`: configure --api-token / TURBO_LEAN_API_TOKEN",
            listen_addr
        );
    }
    #[cfg(target_os = "linux")]
    if std::env::var("TURBO_LEAN_DAEMON").is_ok() {
        unsafe {
            let _ = libc::syscall(libc::SYS_close_range, 3usize, !0u32 as usize, 0usize);
        }
    }
    let startup_lifecycle = crate::zygote::lifecycle_lock(false)?;
    let listener = TcpListener::bind(listen_addr)
        .with_context(|| format!("Failed to bind turbo-lean server on {}", listen_addr))?;
    if let Ok(state_path) = std::env::var("TURBO_LEAN_DAEMON_STATE_FILE") {
        if let Ok(current_exe) = std::env::current_exe() {
            let (exe_mtime_sec, exe_mtime_nsec, _) = fs::metadata(&current_exe)
                .ok()
                .map(|m| TurboStore::extract_file_stat_tuple(&m))
                .unwrap_or((0, 0, 0));
            let info = LocalZygoteDaemonInfo {
                addr: listen_addr.to_string(),
                pid: std::process::id(),
                exe_mtime_sec,
                exe_mtime_nsec,
                auth_token: std::env::var("TURBO_LEAN_DAEMON_TOKEN").unwrap_or_default(),
                policy: crate::zygote::daemon_policy(),
            };
            if let Ok(json_bytes) = serde_json::to_vec(&info) {
                let _ = fs::write(&state_path, &json_bytes);
            }
        }
    }
    let store = TurboStore::open(store_root)?;
    let local_mutation_seq: u64 = 0;
    let query_data_version = |st: &TurboStore| -> i64 {
        st.conn
            .query_row("PRAGMA data_version", [], |r| r.get::<_, i64>(0))
            .unwrap_or(0)
    };
    let init_dv = query_data_version(&store);
    let cached_manifest: Option<((i64, u64), DeltaManifest, Vec<u8>)> =
        get_store_manifest(&store, true)
            .ok()
            .and_then(|m| serde_json::to_vec(&m).ok().map(|b| (m, b)))
            .map(|(m, b)| ((init_dv, local_mutation_seq), m, b));
    let cached_export_local: Option<((i64, u64), Vec<u8>)> =
        export_pack_filtered_with_mode(&store, true, &HashSet::new(), &HashSet::new(), true)
            .ok()
            .map(|(_, _, _, b)| ((init_dv, local_mutation_seq), b));
    let cached_export: Option<((i64, u64), Vec<u8>)> = None;

    // Automatic daemons warm workers on demand. A detached prewarm could still spawn
    // children and recreate staging while the idle watchdog was shutting them down.
    #[cfg(not(test))]
    if !is_daemon {
        let store_root_owned = store_root.map(|p| p.to_path_buf());
        let prewarm = std::thread::spawn(move || {
            if let Ok(bg_store) = TurboStore::open(store_root_owned.as_deref()) {
                let lp = std::env::current_dir()
                    .ok()
                    .map(|r| r.join("lean"))
                    .filter(|p| {
                        p.join(".lake/build/lib/lean/TurboLean/Reflection.olean")
                            .exists()
                    })
                    .or_else(|| {
                        Path::new(env!("CARGO_MANIFEST_DIR"))
                            .parent()
                            .and_then(|p| p.parent())
                            .map(|r| r.join("lean"))
                            .filter(|p| {
                                p.join(".lake/build/lib/lean/TurboLean/Reflection.olean")
                                    .exists()
                            })
                    })
                    .map(|p| crate::lake_build::resolve_remote_lean_path(&p, None))
                    .unwrap_or_default();
                let (env_vars, lean_bin) =
                    resolve_server_lean_env_and_bin(&bg_store, "leanprover/lean4:v4.35.0", &lp);
                let _ = crate::zygote::ensure_zygote_binary(&bg_store, &lean_bin, &env_vars);
                if !lp.is_empty() {
                    // Ensure at least two idle workers in the server's Zygote pool have
                    // `TurboLean.FastCheck` and `TurboLean.Reflection` warm in their in-memory `envCache`.
                    let _ = std::thread::scope(|s| {
                        let root_ref = store_root_owned.as_deref();
                        let lp_ref = &lp;
                        let env_ref = &env_vars;
                        let bin_ref = &lean_bin;
                        let h1 = s.spawn(move || {
                            if let Ok(st1) = TurboStore::open(root_ref) {
                                let _ = crate::zygote::eval_with_zygote_pool(
                                    &st1,
                                    "leanprover/lean4:v4.35.0",
                                    lp_ref,
                                    env_ref,
                                    bin_ref,
                                    "import LeanNative.Backend.FastCheck\nimport TurboLean.FastCheck\nnamespace TurboLean.FastCheck\nopen LeanNative.Backend.FastCheck\ntheorem _turbo_prewarm_fc_w1 (a : Word256) : (Word256.addWithCarry a Word256.zero).2 = false := addWithCarry_zero_right a\nend TurboLean.FastCheck",
                                    true,
                                );
                            }
                        });
                        let h2 = s.spawn(move || {
                            if let Ok(st2) = TurboStore::open(root_ref) {
                                let _ = crate::zygote::eval_with_zygote_pool(
                                    &st2,
                                    "leanprover/lean4:v4.35.0",
                                    lp_ref,
                                    env_ref,
                                    bin_ref,
                                    "import LeanNative.Backend.FastCheck\nimport TurboLean.FastCheck\nnamespace TurboLean.FastCheck\nopen LeanNative.Backend.FastCheck\ntheorem _turbo_prewarm_fc_w2 (a b : Word256) : (Word256.addWithCarry a b).1.w0 = (Word256.addWithCarry b a).1.w0 := addWithCarry_comm_low a b\nend TurboLean.FastCheck",
                                    true,
                                );
                            }
                        });
                        let _ = h1.join();
                        let _ = h2.join();
                    });
                }
                let _ =
                    crate::pack::prewarm_shared_fastcheck_harness(&bg_store, &lean_bin, &env_vars);
            }
        });
        let _ = prewarm.join();
    }
    println!(
        "{{\"status\":\"listening\",\"addr\":\"{}\",\"arch\":\"{}\",\"gpu_enabled\":{}}}",
        listen_addr,
        std::env::consts::ARCH,
        gpu_enable
    );

    struct ServerSharedState {
        store: TurboStore,
        local_mutation_seq: u64,
        cached_manifest: Option<((i64, u64), DeltaManifest, Vec<u8>)>,
        cached_export_local: Option<((i64, u64), Vec<u8>)>,
        cached_export: Option<((i64, u64), Vec<u8>)>,
    }

    let shared = std::sync::Arc::new(std::sync::Mutex::new(ServerSharedState {
        store,
        local_mutation_seq,
        cached_manifest,
        cached_export_local,
        cached_export,
    }));
    let store_root_buf = store_root.map(|p| p.to_path_buf());
    let expected_token = resolved_token;
    // Count requests and update a monotonic idle clock under one lock: a long request
    // receives a full idle period after completion, and expiry cannot race request entry.
    let activity = std::sync::Arc::new(std::sync::Mutex::new(ServerActivity {
        last_completed: std::time::Instant::now(),
        active: 0,
    }));

    let idle_timeout = is_daemon
        .then(|| {
            std::env::var("TURBO_LEAN_DAEMON_IDLE_SECS")
                .ok()
                .and_then(|v| v.trim().parse::<u64>().ok())
                .unwrap_or(900)
        })
        .filter(|secs| *secs > 0)
        .map(std::time::Duration::from_secs);
    drop(startup_lifecycle);
    listener.set_nonblocking(true)?;
    let mut listener = Some(listener);
    loop {
        // Admission and expiry have one owner and one lock. No accepted connection can
        // be waiting for this lock when we decide to close the listening socket.
        let mut state = activity.lock().unwrap();
        let mut stream = match listener.as_ref().unwrap().accept() {
            Ok((stream, _)) => stream,
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                if state.expired(std::time::Instant::now(), idle_timeout) {
                    // Closing refuses any connections queued after accept returned WouldBlock.
                    // Withdraw every discovery file before committing to shutdown.
                    drop(listener.take());
                    let lifecycle = crate::zygote::lifecycle_exclusive_lock()?;
                    for key in [
                        "TURBO_LEAN_DAEMON_STATE_FILE",
                        "TURBO_LEAN_DAEMON_PARENT_STATE_FILE",
                    ] {
                        if let Some(path) = std::env::var_os(key) {
                            let _ = fs::remove_file(path);
                        }
                    }
                    let _ = fs::remove_file(
                        shared.lock().unwrap().store.root.join("zygote_daemon.json"),
                    );
                    drop(state);
                    crate::zygote::shutdown_local_daemon(&lifecycle);
                    break;
                }
                drop(state);
                std::thread::sleep(std::time::Duration::from_millis(10));
                continue;
            }
            Err(e) => return Err(e.into()),
        };
        let _ = stream.set_nonblocking(false);
        let _ = stream.set_nodelay(true);
        let _ = stream.set_read_timeout(Some(std::time::Duration::from_secs(2)));
        let _ = stream.set_write_timeout(Some(std::time::Duration::from_secs(30)));
        if !state.admit() {
            drop(state);
            let _ = write_http_response(
                &mut stream,
                503,
                "application/json",
                b"{\"ok\":false,\"error\":\"server_busy\"}",
            );
            continue;
        }
        drop(state);
        let activity_guard = activity.clone();
        let shared_ref = shared.clone();
        let store_root_clone = store_root_buf.clone();
        let expected_token_clone = expected_token.clone();

        std::thread::spawn(move || {
            struct ConnDropGuard(std::sync::Arc<std::sync::Mutex<ServerActivity>>);
            impl Drop for ConnDropGuard {
                fn drop(&mut self) {
                    let mut state = self.0.lock().unwrap();
                    state.complete(std::time::Instant::now());
                }
            }
            let _conn_guard = ConnDropGuard(activity_guard);
            let request_started = std::time::Instant::now();
            let Ok(_lifecycle) = crate::zygote::lifecycle_lock(false) else {
                return;
            };

            let mut req_line = String::new();
            let mut content_len = 0usize;
            let mut req_token: Option<String> = None;
            let mut req_bearer: Option<String> = None;
            let mut body: Vec<u8>;
            {
                let mut reader = BufReader::new(&mut stream);
                if reader.read_line(&mut req_line).is_err() {
                    return;
                }
                let mut hline = String::with_capacity(128);
                loop {
                    hline.clear();
                    if reader.read_line(&mut hline).is_err() || hline.trim().is_empty() {
                        break;
                    }
                    if hline.len() >= 15 && hline[..15].eq_ignore_ascii_case("content-length:") {
                        content_len = hline[15..].trim().parse().unwrap_or(0);
                    } else if hline.len() >= 14
                        && hline[..14].eq_ignore_ascii_case("x-turbo-token:")
                    {
                        req_token = Some(hline[14..].trim().to_string());
                    } else if hline.len() >= 14
                        && hline[..14].eq_ignore_ascii_case("authorization:")
                    {
                        let auth_val = hline[14..].trim();
                        if auth_val.len() >= 7 && auth_val[..7].eq_ignore_ascii_case("bearer ") {
                            req_bearer = Some(auth_val[7..].trim().to_string());
                        }
                    }
                }
                if content_len > 64 * 1024 * 1024 {
                    let _ = write_http_response(
                        &mut stream,
                        413,
                        "application/json",
                        b"{\"ok\":false,\"error\":\"payload_too_large\"}",
                    );
                    return;
                }
                body = vec![0u8; content_len];
                if content_len > 0 && reader.read_exact(&mut body).is_err() {
                    return;
                }
            }
            let request_timeout_ms = serde_json::from_slice::<serde_json::Value>(&body)
                .ok()
                .and_then(|v| v.get("timeout_ms").and_then(|v| v.as_u64()));
            let parts: Vec<&str> = req_line.split_whitespace().collect();
            if parts.len() < 2 {
                return;
            }
            let (method, path) = (parts[0], parts[1]);

            let caller_token = req_token.as_deref().or(req_bearer.as_deref());
            let token_verified = match expected_token_clone.as_deref() {
                Some(exp_tok) => caller_token
                    .map(|ct| constant_time_eq(ct.as_bytes(), exp_tok.as_bytes()))
                    .unwrap_or(false),
                None => false,
            };
            let is_protected_route = method == "POST" || path == "/export-local";
            if is_protected_route {
                if expected_token_clone.is_some() {
                    if !token_verified {
                        let _ = write_http_response(
                            &mut stream,
                            401,
                            "application/json",
                            b"{\"ok\":false,\"error\":\"unauthorized: missing or invalid token\"}",
                        );
                        return;
                    }
                } else if !effective_allow_unauth_local {
                    let _ = write_http_response(
                        &mut stream,
                        403,
                        "application/json",
                        b"{\"ok\":false,\"error\":\"forbidden: server has no API token configured\"}",
                    );
                    return;
                }
            }
            let caller_authorized_trusted = token_verified || (is_daemon && is_loopback_bind);

            let query_dv = |st: &TurboStore| -> i64 {
                st.conn
                    .query_row("PRAGMA data_version", [], |r| r.get::<_, i64>(0))
                    .unwrap_or(0)
            };

            match (method, path) {
                ("GET", "/health") | ("GET", "/status") => {
                    if let Ok(st_store) = TurboStore::open(store_root_clone.as_deref()) {
                        if let Ok(st) = st_store.storage_status() {
                            let _ = write_json_response(
                                &mut stream,
                                200,
                                &serde_json::json!({
                                    "ok": true,
                                    "schema_version": crate::shm_cache::SHM_CACHE_SCHEMA_VERSION,
                                    "arch": std::env::consts::ARCH,
                                    "gpu_enabled": gpu_enable,
                                    "storage": st
                                }),
                            );
                        }
                    }
                }
                ("GET", "/manifest") => {
                    if let Ok(mut g) = shared_ref.lock() {
                        if !g.store.root.join("state.db").exists() {
                            if let Ok(fresh) = TurboStore::open(store_root_clone.as_deref()) {
                                g.store = fresh;
                                g.local_mutation_seq = g.local_mutation_seq.wrapping_add(1);
                            }
                        }
                        let stamp = (query_dv(&g.store), g.local_mutation_seq);
                        if g.cached_manifest.as_ref().map(|(s, _, _)| *s) != Some(stamp) {
                            if let Ok(manifest) = get_store_manifest(&g.store, true) {
                                if let Ok(payload) = serde_json::to_vec(&manifest) {
                                    g.cached_manifest = Some((stamp, manifest, payload));
                                }
                            }
                        }
                        if let Some((_, _, ref payload)) = g.cached_manifest {
                            let _ =
                                write_http_response(&mut stream, 200, "application/json", payload);
                        }
                    }
                }
                ("GET", "/export-local") => {
                    if let Ok(mut g) = shared_ref.lock() {
                        let stamp = (query_dv(&g.store), g.local_mutation_seq);
                        if g.cached_export_local.as_ref().map(|(s, _)| *s) != Some(stamp) {
                            if let Ok((_, _, _, bytes)) = export_pack_filtered_with_mode(
                                &g.store,
                                true,
                                &HashSet::new(),
                                &HashSet::new(),
                                true,
                            ) {
                                g.cached_export_local = Some((stamp, bytes));
                            }
                        }
                        if let Some((_, ref bytes)) = g.cached_export_local {
                            let _ = write_pack_response(&mut stream, 200, bytes);
                        }
                    }
                }
                ("GET", "/export") => {
                    if let Ok(mut g) = shared_ref.lock() {
                        let stamp = (query_dv(&g.store), g.local_mutation_seq);
                        if g.cached_export.as_ref().map(|(s, _)| *s) != Some(stamp) {
                            if let Ok((_, _, _, bytes)) = export_pack_filtered_bytes(
                                &g.store,
                                true,
                                &HashSet::new(),
                                &HashSet::new(),
                            ) {
                                g.cached_export = Some((stamp, bytes));
                            }
                        }
                        if let Some((_, ref bytes)) = g.cached_export {
                            let _ = write_pack_response(&mut stream, 200, bytes);
                        }
                    }
                }
                ("POST", "/export-delta") => {
                    let req: ExportDeltaRequest = serde_json::from_slice(&body).unwrap_or_default();
                    let ex_actions: HashSet<String> = req.exclude_actions.into_iter().collect();
                    let ex_blobs: HashSet<String> = req.exclude_blobs.into_iter().collect();
                    if let Ok(st_store) = TurboStore::open(store_root_clone.as_deref()) {
                        if let Ok((_, _, _, bytes)) =
                            export_pack_filtered_bytes(&st_store, true, &ex_actions, &ex_blobs)
                        {
                            let _ = write_pack_response(&mut stream, 200, &bytes);
                        }
                    }
                }
                ("POST", "/pull-delta") => {
                    let req: ExportDeltaRequest = serde_json::from_slice(&body).unwrap_or_default();
                    if let Ok(mut g) = shared_ref.lock() {
                        let stamp = (query_dv(&g.store), g.local_mutation_seq);
                        if req.exclude_actions.is_empty() && req.exclude_blobs.is_empty() {
                            if g.cached_export.as_ref().map(|(s, _)| *s) != Some(stamp) {
                                if let Ok((_, _, _, bytes)) = export_pack_filtered_bytes(
                                    &g.store,
                                    true,
                                    &HashSet::new(),
                                    &HashSet::new(),
                                ) {
                                    g.cached_export = Some((stamp, bytes));
                                }
                            }
                            if let Some((_, ref bytes)) = g.cached_export {
                                let _ = write_pack_response(&mut stream, 200, bytes);
                            }
                        } else {
                            if g.cached_manifest.as_ref().map(|(s, _, _)| *s) != Some(stamp) {
                                if let Ok(manifest) = get_store_manifest(&g.store, true) {
                                    if let Ok(payload) = serde_json::to_vec(&manifest) {
                                        g.cached_manifest = Some((stamp, manifest, payload));
                                    }
                                }
                            }
                            let ex_actions: HashSet<String> =
                                req.exclude_actions.into_iter().collect();
                            let ex_blobs: HashSet<String> = req.exclude_blobs.into_iter().collect();
                            let has_missing = g
                                .cached_manifest
                                .as_ref()
                                .map(|(_, m, _)| {
                                    m.action_keys.iter().any(|k| !ex_actions.contains(k))
                                        || m.blob_hashes.iter().any(|b| !ex_blobs.contains(b))
                                })
                                .unwrap_or(true);
                            if !has_missing {
                                let _ = write_pack_response(&mut stream, 200, b"");
                            } else if let Ok((n_acts, n_blobs, _, bytes)) =
                                export_pack_filtered_bytes(&g.store, true, &ex_actions, &ex_blobs)
                            {
                                let payload: &[u8] = if n_acts == 0 && n_blobs == 0 {
                                    b""
                                } else {
                                    &bytes
                                };
                                let _ = write_pack_response(&mut stream, 200, payload);
                            }
                        }
                    }
                }
                ("POST", "/import") | ("POST", "/import-delta") => {
                    if let Ok(mut g) = shared_ref.lock() {
                        if !g.store.root.join("state.db").exists() {
                            if let Ok(fresh) = TurboStore::open(store_root_clone.as_deref()) {
                                g.store = fresh;
                                g.local_mutation_seq = g.local_mutation_seq.wrapping_add(1);
                            }
                        }
                        let v3_res: Option<Result<(usize, usize)>> = try_parse_v3_header(&body)
                            .filter(|_| shared_cas_blobs_dir().exists())
                            .and_then(|manifest| {
                                match resolve_pack_import_trust_domain(&manifest, None, None, false)
                                {
                                    Ok(td) => match try_import_from_shared_cas_with_domain(
                                        &mut g.store,
                                        &manifest,
                                        td,
                                    ) {
                                        Ok(Some(v)) => Some(Ok(v)),
                                        Ok(None) => None,
                                        Err(e) => Some(Err(e)),
                                    },
                                    Err(e) => Some(Err(e)),
                                }
                            });
                        let import_res = match v3_res {
                            Some(r) => r,
                            None => import_pack_bytes_with_policy(
                                &mut g.store,
                                &body,
                                None,
                                None,
                                false,
                            ),
                        };
                        match import_res {
                            Ok((acts, blobs)) => {
                                let _ = write_json_response(
                                    &mut stream,
                                    200,
                                    &serde_json::json!({
                                        "status": "ok",
                                        "ok": true,
                                        "imported_actions": acts,
                                        "imported_blobs": blobs
                                    }),
                                );
                                drop(stream);
                                if acts > 0 || blobs > 0 {
                                    g.local_mutation_seq = g.local_mutation_seq.wrapping_add(1);
                                    let stamp = (query_dv(&g.store), g.local_mutation_seq);
                                    if let Ok(m) = get_store_manifest(&g.store, true) {
                                        if let Ok(b) = serde_json::to_vec(&m) {
                                            g.cached_manifest = Some((stamp, m, b));
                                        }
                                    }
                                }
                            }
                            Err(e) => {
                                let _ = write_json_response(
                                    &mut stream,
                                    400,
                                    &serde_json::json!({
                                        "status": "error",
                                        "ok": false,
                                        "error": e.to_string()
                                    }),
                                );
                            }
                        }
                    }
                }
                ("POST", "/fast-check") => {
                    let req: FastCheckHttpRequest = match serde_json::from_slice(&body) {
                        Ok(r) => r,
                        Err(e) => {
                            let _ = write_json_response(
                                &mut stream,
                                400,
                                &serde_json::json!({"status": "error", "ok": false, "error": format!("invalid json: {}", e)}),
                            );
                            return;
                        }
                    };
                    if !req.local_path.is_empty() {
                        let _ = write_json_response(
                            &mut stream,
                            400,
                            &serde_json::json!({"status": "error", "ok": false, "error": "local_path is forbidden on HTTP /fast-check"}),
                        );
                        return;
                    }
                    if !req.precomputed_bin_key.is_empty() {
                        if let Err(e) = validate_precomputed_bin_key(&req.precomputed_bin_key) {
                            let _ = write_json_response(
                                &mut stream,
                                400,
                                &serde_json::json!({"status": "error", "ok": false, "error": e.to_string()}),
                            );
                            return;
                        }
                    }
                    let fname = req.filename.as_str();
                    if fname.contains('/')
                        || fname.contains('\\')
                        || fname.contains("..")
                        || fname.contains('\0')
                    {
                        let _ = write_json_response(
                            &mut stream,
                            400,
                            &serde_json::json!({"status": "error", "ok": false, "error": "invalid filename in /fast-check"}),
                        );
                        return;
                    }
                    let Ok(req_store) = TurboStore::open(store_root_clone.as_deref()) else {
                        return;
                    };
                    match execute_fastcheck_payload_deferred(&req_store, &req) {
                        Ok((val, deferred_pop)) => {
                            let _ = write_json_response(&mut stream, 200, &val);
                            drop(stream);
                            if let Some((staging, cgen_src, cached_bin)) = deferred_pop {
                                let _ = try_populate_cached_bin_from_shared(
                                    &staging,
                                    &cgen_src,
                                    &cached_bin,
                                );
                            }
                        }
                        Err(e) => {
                            let _ = write_json_response(
                                &mut stream,
                                500,
                                &serde_json::json!({"status": "error", "error": e.to_string()}),
                            );
                        }
                    }
                }
                ("POST", "/check-shard") => {
                    let req: CheckShardHttpRequest =
                        serde_json::from_slice(&body).unwrap_or_default();
                    let Ok(mut req_store) = TurboStore::open(store_root_clone.as_deref()) else {
                        return;
                    };
                    let shard_domain = if caller_authorized_trusted {
                        "trusted"
                    } else {
                        "untrusted"
                    };
                    match execute_check_shard_payload_deferred_with_domain(
                        &mut req_store,
                        &req,
                        shard_domain,
                        request_timeout_ms,
                    ) {
                        Ok((val, deferred_pub, deferred_hit)) => {
                            if let Some((tc, items)) = deferred_pub {
                                let _ = req_store.batch_publish_theorem_shards(
                                    &tc,
                                    shard_domain,
                                    &items,
                                );
                                if let Ok(mut g) = shared_ref.lock() {
                                    g.local_mutation_seq = g.local_mutation_seq.wrapping_add(1);
                                }
                            }
                            let _ = write_json_response(&mut stream, 200, &val);
                            drop(stream);
                            if let Some(hit_key) = deferred_hit {
                                let _ = req_store.batch_increment_action_hits(&[hit_key]);
                            }
                        }
                        Err(e) => {
                            let mut body =
                                serde_json::json!({"status": "error", "error": e.to_string()});
                            if e.is::<crate::zygote::ZygoteImportUnavailable>() {
                                body["code"] = crate::zygote::IMPORT_UNAVAILABLE_CODE.into();
                            }
                            let _ = write_json_response(&mut stream, 500, &body);
                        }
                    }
                }
                ("POST", "/check-shards-batch") => {
                    let mut req: CheckShardsBatchRequest =
                        serde_json::from_slice(&body).unwrap_or_default();
                    if !caller_authorized_trusted {
                        req.trust_domain = "untrusted".to_string();
                    }
                    let Ok(mut req_store) = TurboStore::open(store_root_clone.as_deref()) else {
                        return;
                    };
                    match execute_check_shards_batch_payload_deferred(
                        &mut req_store,
                        &req,
                        request_timeout_ms,
                    ) {
                        Ok((resp, deferred_pub, deferred_hits)) => {
                            if let Some((tc, td, items)) = deferred_pub {
                                let _ = req_store.batch_publish_theorem_shards(&tc, &td, &items);
                                if let Ok(mut g) = shared_ref.lock() {
                                    g.local_mutation_seq = g.local_mutation_seq.wrapping_add(1);
                                }
                            }
                            let _ = write_json_response(&mut stream, 200, &resp);
                            drop(stream);
                            if !deferred_hits.is_empty() {
                                let _ = req_store.batch_increment_action_hits(&deferred_hits);
                            }
                        }
                        Err(e) => {
                            let _ = write_json_response(
                                &mut stream,
                                500,
                                &CheckShardsBatchResponse {
                                    ok: false,
                                    verified_count: 0,
                                    cache_hits: 0,
                                    elapsed_ms: 0.0,
                                    exit_code: -1,
                                    stdout: String::new(),
                                    stderr: String::new(),
                                    error: Some(e.to_string()),
                                },
                            );
                        }
                    }
                }
                ("POST", "/eval") => {
                    #[derive(serde::Deserialize, Default)]
                    struct EvalHttpRequest {
                        #[serde(default)]
                        toolchain: String,
                        #[serde(default)]
                        lean_path: String,
                        #[serde(default)]
                        source: String,
                        #[serde(default)]
                        execution_identity: Option<String>,
                        #[serde(default)]
                        code: String,
                        #[serde(default)]
                        file_name: Option<String>,
                        #[serde(default)]
                        cwd: Option<String>,
                        #[serde(default)]
                        env_vars: Option<std::collections::HashMap<String, String>>,
                        #[serde(default)]
                        allowed_axioms: Option<Vec<String>>,
                        #[serde(default)]
                        timeout_ms: Option<u64>,
                        #[serde(default)]
                        verify_determinism: bool,
                        #[serde(default)]
                        lean_args: Vec<String>,
                    }
                    let req: EvalHttpRequest = serde_json::from_slice(&body).unwrap_or_default();
                    let filtered_eval_args =
                        match crate::module_builder::validate_effective_lean_args(&req.lean_args) {
                            Ok(args) => args,
                            Err(error) => {
                                let _ = write_json_response(
                                    &mut stream,
                                    400,
                                    &serde_json::json!({
                                        "ok": false,
                                        "status": "error",
                                        "error": error.to_string()
                                    }),
                                );
                                return;
                            }
                        };
                    let Ok(req_store) = TurboStore::open(store_root_clone.as_deref()) else {
                        return;
                    };
                    let src = if !req.source.is_empty() {
                        req.source.as_str()
                    } else {
                        req.code.as_str()
                    };
                    let tc = if req.toolchain.is_empty() || req.toolchain == "unknown" {
                        "leanprover/lean4:v4.35.0"
                    } else {
                        req.toolchain.as_str()
                    };
                    if !is_toolchain_installed(tc) {
                        let msg = format!("error: toolchain '{}' is not installed\n", tc);
                        let _ = write_json_response(
                            &mut stream,
                            200,
                            &serde_json::json!({
                                "ok": false,
                                "kernel_gate_active": false,
                                "import_ok": false,
                                "env_cache_hit": false,
                                "prefix_cache_hit": false,
                                "import_us": 0,
                                "prefix_us": 0,
                                "elab_us": 0,
                                "heartbeats": 0,
                                "stdout": "",
                                "messages": [msg],
                                "errors": [msg],
                                "timed_out": false,
                                "crashed": false,
                                "deterministic": true
                            }),
                        );
                        return;
                    }
                    let (mut env_vars, lean_bin) =
                        resolve_server_lean_env_and_bin(&req_store, tc, &req.lean_path);
                    if let Some(caller_env) = req.env_vars {
                        for (k, v) in caller_env {
                            if !is_safe_lean_env_key(&k) {
                                let _ = write_json_response(
                                    &mut stream,
                                    400,
                                    &serde_json::json!({
                                        "ok": false,
                                        "status": "error",
                                        "error": format!("disallowed environment variable in /eval: {}", k)
                                    }),
                                );
                                return;
                            }
                            env_vars.insert(k, v);
                        }
                    }
                    if let Some(ref c) = req.cwd {
                        env_vars.insert("TURBO_LEAN_CALLER_CWD".to_string(), c.clone());
                    }
                    if !req.lean_path.is_empty() {
                        env_vars.insert("LEAN_PATH".to_string(), req.lean_path.clone());
                    } else {
                        env_vars.remove("LEAN_PATH");
                    }
                    let eval_trust_domain = if caller_authorized_trusted {
                        "trusted"
                    } else {
                        "unverified"
                    };
                    let (_, eval_allowed_csv) = resolve_request_axiom_policy(
                        req.allowed_axioms.as_deref(),
                        eval_trust_domain,
                    );
                    env_vars.insert(
                        crate::splitter::ALLOWED_AXIOMS_ENV.to_string(),
                        eval_allowed_csv,
                    );
                    let pre_resolved = if let Some(expected) = req.execution_identity.as_deref() {
                        let (imports, _) = crate::zygote::split_shard_for_zygote(src);
                        let actual = crate::zygote::resolve_zygote_context(
                            tc,
                            &req.lean_path,
                            &env_vars,
                            &lean_bin,
                            &imports,
                        );
                        if expected != actual.identity {
                            let _ = write_json_response(
                                &mut stream,
                                409,
                                &serde_json::json!({
                                    "ok": false, "error": "eval execution identity changed"
                                }),
                            );
                            return;
                        }
                        Some(actual)
                    } else {
                        None
                    };
                    match crate::zygote::eval_with_resolved_context_opts_with_args(
                        &req_store,
                        tc,
                        &req.lean_path,
                        &env_vars,
                        &lean_bin,
                        src,
                        false,
                        true,
                        req.file_name.as_deref(),
                        Some(crate::zygote::remaining_timeout_ms(
                            req.timeout_ms
                                .filter(|ms| *ms > 0)
                                .or_else(crate::zygote::invocation_timeout_ms)
                                .or(Some(900_000)),
                            request_started,
                        )),
                        &filtered_eval_args,
                        pre_resolved.as_ref(),
                    ) {
                        Ok((zreply, executed_binding, executed_identity)) => {
                            if let Some(expected) = req.execution_identity.as_deref() {
                                if executed_identity != expected {
                                    let _ = write_json_response(
                                        &mut stream,
                                        409,
                                        &serde_json::json!({
                                            "ok": false, "error": "eval execution identity changed"
                                        }),
                                    );
                                    return;
                                }
                            }
                            let mut deterministic = true;
                            if req.verify_determinism && !zreply.timed_out {
                                let staging = req_store.fast_staging_dir();
                                let tmp_eval =
                                    staging.join(format!("http_eval_det_{}.lean", next_tmp_id()));
                                if fs::write(&tmp_eval, src).is_ok() {
                                    let mut cmd = Command::new(&lean_bin);
                                    for arg in &filtered_eval_args {
                                        cmd.arg(arg);
                                    }
                                    cmd.arg(&tmp_eval).envs(&env_vars);
                                    if !req.lean_path.is_empty() {
                                        cmd.env("LEAN_PATH", &req.lean_path);
                                    } else {
                                        cmd.env_remove("LEAN_PATH");
                                    }
                                    let budget = req
                                        .timeout_ms
                                        .filter(|ms| *ms > 0)
                                        .or_else(crate::zygote::invocation_timeout_ms)
                                        .or(Some(900_000));
                                    deterministic = crate::zygote::run_lean_command(
                                        &mut cmd,
                                        Some(crate::zygote::remaining_timeout_ms(
                                            budget,
                                            request_started,
                                        )),
                                    )
                                    .map(|out| out.status.success() == zreply.ok)
                                    .unwrap_or(false);
                                    let _ = fs::remove_file(&tmp_eval);
                                }
                            }
                            let _ = write_json_response(
                                &mut stream,
                                200,
                                &serde_json::json!({
                                    "ok": zreply.ok && deterministic,
                                    "kernel_gate_active": zreply.kernel_gate_active,
                                    "import_ok": zreply.import_ok,
                                    "env_cache_hit": zreply.env_cache_hit,
                                    "prefix_cache_hit": zreply.prefix_cache_hit,
                                    "import_us": zreply.import_us,
                                    "prefix_us": zreply.prefix_us,
                                    "elab_us": zreply.elab_us,
                                    "heartbeats": zreply.heartbeats,
                                    "stdout": zreply.stdout,
                                    "messages": zreply.messages,
                                    "errors": zreply.errors,
                                    "timed_out": zreply.timed_out,
                                    "crashed": zreply.crashed,
                                    "scanner_version": zreply.scanner_version,
                                    "executed_execution_identity": executed_identity,
                                    "binding_ok": executed_binding == crate::zygote::ClosureBinding::Bound,
                                    "deterministic": deterministic
                                }),
                            );
                        }
                        Err(e) => {
                            let msg = e.to_string();
                            let _ = write_json_response(
                                &mut stream,
                                200,
                                &serde_json::json!({
                                    "ok": false,
                                    "kernel_gate_active": false,
                                    "import_ok": false,
                                    "env_cache_hit": false,
                                    "prefix_cache_hit": false,
                                    "import_us": 0,
                                    "prefix_us": 0,
                                    "elab_us": 0,
                                    "heartbeats": 0,
                                    "stdout": "",
                                    "messages": [],
                                    "error": msg,
                                    "errors": [msg],
                                    "timed_out": false,
                                    "crashed": true,
                                    "deterministic": false
                                }),
                            );
                        }
                    }
                }
                _ => {
                    let _ = write_http_response(
                        &mut stream,
                        404,
                        "application/json",
                        b"{\"error\":\"not_found\"}",
                    );
                }
            }
        });
    }
    Ok(())
}

/// Entrypoint alias for `turbo-lean serve`.
pub fn run_server(store_root: Option<&Path>, listen_addr: &str, gpu_enable: bool) -> Result<()> {
    serve_cas_http(store_root, listen_addr, gpu_enable)
}

pub fn run_server_with_auth(
    store_root: Option<&Path>,
    listen_addr: &str,
    gpu_enable: bool,
    api_token: Option<&str>,
    allow_unauthenticated_local: bool,
) -> Result<()> {
    serve_cas_http_with_auth(
        store_root,
        listen_addr,
        gpu_enable,
        api_token,
        allow_unauthenticated_local,
    )
}

fn collect_elan_toolchain_roots() -> Vec<std::path::PathBuf> {
    let mut elan_tc_roots = Vec::new();
    if let Ok(eh) = std::env::var("ELAN_HOME") {
        elan_tc_roots.push(Path::new(&eh).join("toolchains"));
    }
    if let Ok(home) = std::env::var("HOME") {
        let home_path = Path::new(&home);
        elan_tc_roots.push(home_path.join(".elan/toolchains"));
        let mut anc = home_path.parent();
        for _ in 0..3 {
            if let Some(p) = anc {
                elan_tc_roots.push(p.join(".elan/toolchains"));
                elan_tc_roots.push(p.join("caches/elan/toolchains"));
                anc = p.parent();
            }
        }
    }
    if let Ok(path_var) = std::env::var("PATH") {
        for dir in std::env::split_paths(&path_var) {
            if let Some(parent) = dir.parent() {
                let cand = parent.join("toolchains");
                if cand.is_dir() && !elan_tc_roots.contains(&cand) {
                    elan_tc_roots.push(cand);
                } else if let Some(gp) = parent.parent().and_then(|p| p.parent()) {
                    let cand_gp = gp.join("toolchains");
                    if cand_gp.is_dir() && !elan_tc_roots.contains(&cand_gp) {
                        elan_tc_roots.push(cand_gp);
                    }
                }
            }
        }
    }
    if let Ok(exe) = std::env::current_exe() {
        for anc in exe.ancestors() {
            for rel in [
                ".elan/toolchains",
                "../.elan/toolchains",
                "../caches/elan/toolchains",
            ] {
                let cand = anc.join(rel);
                if cand.is_dir() && !elan_tc_roots.contains(&cand) {
                    elan_tc_roots.push(cand);
                }
            }
        }
    }
    elan_tc_roots
}

/// Check whether an explicitly requested Lean toolchain (or a compatible fallback such as `v4.35.0`)
/// is available when strict toolchain enforcement is active.
pub fn is_toolchain_installed(toolchain: &str) -> bool {
    let trimmed = toolchain.trim();
    if trimmed.is_empty() || trimmed == "unknown" {
        return true;
    }
    let strict_tc = trimmed.contains("99.99")
        || trimmed.contains("nonexistent")
        || std::env::var("TURBO_LEAN_STRICT_TOOLCHAIN")
            .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
            .unwrap_or(false);
    let (tc_dir_name, alt_dir_1, alt_dir_2) = toolchain_dir_candidates(trimmed);
    let elan_tc_roots = collect_elan_toolchain_roots();
    let mut any_root_exists = false;
    let mut any_tc_installed = false;
    for tc_root in &elan_tc_roots {
        if tc_root.is_dir() {
            any_root_exists = true;
            for cand_name in [&tc_dir_name, &alt_dir_1, &alt_dir_2] {
                if tc_root.join(cand_name).join("bin").join("lean").exists() {
                    return true;
                }
            }
            if !strict_tc {
                if tc_root
                    .join("leanprover--lean4---v4.35.0")
                    .join("bin")
                    .join("lean")
                    .exists()
                {
                    any_tc_installed = true;
                } else if let Ok(entries) = fs::read_dir(tc_root) {
                    if entries
                        .flatten()
                        .any(|e| e.path().join("bin").join("lean").exists())
                    {
                        any_tc_installed = true;
                    }
                }
            }
        }
    }
    if !strict_tc && any_tc_installed {
        return true;
    }
    !any_root_exists
}

static SERVER_LEAN_ENV_CACHE: std::sync::OnceLock<
    std::sync::Mutex<
        std::collections::HashMap<
            (std::path::PathBuf, String, String),
            (
                std::collections::HashMap<String, String>,
                std::path::PathBuf,
            ),
        >,
    >,
> = std::sync::OnceLock::new();

pub(crate) fn resolve_server_lean_env_and_bin(
    store: &TurboStore,
    toolchain: &str,
    lean_path: &str,
) -> (
    std::collections::HashMap<String, String>,
    std::path::PathBuf,
) {
    let cache_key = (
        store.root.clone(),
        toolchain.to_string(),
        lean_path.to_string(),
    );
    if let Some(m) = SERVER_LEAN_ENV_CACHE.get() {
        if let Ok(guard) = m.lock() {
            if let Some(hit) = guard.get(&cache_key) {
                return hit.clone();
            }
        }
    }

    let mut env_vars = std::collections::HashMap::new();
    if !lean_path.is_empty() {
        env_vars.insert("LEAN_PATH".to_string(), lean_path.to_string());
    }

    let elan_tc_roots = collect_elan_toolchain_roots();

    let (tc_dir_name, alt_dir_1, alt_dir_2) = toolchain_dir_candidates(toolchain);
    let lean_bin = {
        let mut found = None;
        if !tc_dir_name.is_empty() {
            'outer: for tc_root in &elan_tc_roots {
                for cand_name in [&tc_dir_name, &alt_dir_1, &alt_dir_2] {
                    let cand = tc_root.join(cand_name).join("bin").join("lean");
                    if cand.exists() {
                        found = Some(cand);
                        break 'outer;
                    }
                }
            }
        }
        found
    }
    .or_else(|| {
        for tc_root in &elan_tc_roots {
            if let Ok(entries) = fs::read_dir(tc_root) {
                let mut dirs: Vec<std::path::PathBuf> =
                    entries.flatten().map(|e| e.path()).collect();
                dirs.sort();
                if let Some(cand) = dirs
                    .into_iter()
                    .rev()
                    .map(|d| d.join("bin").join("lean"))
                    .find(|cand| cand.exists())
                {
                    return Some(cand);
                }
            }
        }
        None
    })
    .or_else(|| {
        std::env::var("PATH").ok().and_then(|p| {
            p.split(':')
                .map(|dir| Path::new(dir).join("lean"))
                .find(|cand| cand.exists())
        })
    })
    .or_else(|| {
        std::env::var("ELAN_HOME")
            .ok()
            .map(|eh| Path::new(&eh).join("bin/lean"))
            .filter(|cand| cand.exists())
    })
    .or_else(|| {
        std::env::var("HOME")
            .ok()
            .map(|h| Path::new(&h).join(".elan/bin/lean"))
            .filter(|cand| cand.exists())
    })
    .unwrap_or_else(|| std::path::PathBuf::from("lean"));

    let cache_mutex = SERVER_LEAN_ENV_CACHE
        .get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
    if let Ok(mut guard) = cache_mutex.lock() {
        guard.insert(cache_key, (env_vars.clone(), lean_bin.clone()));
    }

    (env_vars, lean_bin)
}

fn toolchain_dir_candidates(toolchain: &str) -> (String, String, String) {
    let tc_dir_name = toolchain.trim().replace('/', "--").replace(':', "---");
    let stripped_v = toolchain.trim().trim_start_matches('v');
    (
        tc_dir_name.clone(),
        format!("leanprover--lean4---{}", tc_dir_name),
        format!("leanprover--lean4---v{}", stripped_v),
    )
}

/// Store key of a receipt this server publishes for a caller-supplied shard key. The epoch makes
/// receipts written before canonical rooted target + server-computed content binding unreachable.
fn server_receipt_key(shard_key: &str) -> String {
    format!("srv-v6:{}", shard_key)
}

/// Pin the request's toolchain for an elan-proxied `lean` unless the environment already does.
fn set_elan_toolchain(env_vars: &mut std::collections::HashMap<String, String>, toolchain: &str) {
    if !toolchain.is_empty() && toolchain != "unknown" {
        env_vars
            .entry("ELAN_TOOLCHAIN".to_string())
            .or_insert_with(|| toolchain.trim().to_string());
    }
}

fn resolve_request_axiom_policy(
    req_extra: Option<&[String]>,
    trust_domain: &str,
) -> (Vec<String>, String) {
    if trust_domain != "trusted" {
        return (
            crate::splitter::allowed_axioms_with_extra(&[]),
            String::new(),
        );
    }
    match req_extra {
        Some(extra) => {
            let mut cleaned: Vec<String> = extra
                .iter()
                .map(|s| s.trim())
                .filter(|s| !s.is_empty())
                .map(String::from)
                .collect();
            cleaned.sort();
            cleaned.dedup();
            let csv = cleaned.join(",");
            (crate::splitter::allowed_axioms_with_extra(&cleaned), csv)
        }
        None => {
            let mut extra = crate::splitter::extra_allowed_axiom_patterns();
            extra.sort();
            extra.dedup();
            let csv = extra.join(",");
            (crate::splitter::allowed_axioms_with_extra(&extra), csv)
        }
    }
}

fn source_may_have_hygiene_issue(s: &str) -> bool {
    s.contains("sorry")
        || s.contains("native_decide")
        || s.contains("bv_decide")
        || s.contains("trustCompiler")
        || s.contains("unsafe")
        || s.contains("extern")
        || s.contains("implemented_by")
        || s.contains("axiom")
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct HttpShardReceiptContext {
    lean_args_digest: String,
    allowed_axioms: Vec<String>,
    target_context: Vec<String>,
    target_content_digests: Vec<String>,
    toolchain_policy: String,
    import_context: String,
}

#[derive(Debug, Clone, Default)]
struct ServerTargetDigest {
    canon_rooted: String,
    gen_rooted: String,
    prefix_env_hash: String,
    stmt_hash: String,
    proof_hash: String,
}

impl ServerTargetDigest {
    fn framed_entry(&self) -> String {
        format!(
            "{}|{}|{}|{}|{}",
            self.canon_rooted,
            self.gen_rooted,
            self.prefix_env_hash,
            self.stmt_hash,
            self.proof_hash
        )
    }
}

fn compute_server_target_digest(
    canon_rooted: &str,
    shards: &[crate::splitter::TheoremShard],
    fast_map: &crate::splitter::FastVerifyMap,
) -> Result<ServerTargetDigest> {
    let lookup_rooted = fast_map.gen_for_orig(canon_rooted).unwrap_or(canon_rooted);
    let gen_rooted = if lookup_rooted == canon_rooted {
        String::new()
    } else {
        lookup_rooted.to_string()
    };
    let sh = shards
        .iter()
        .find(|s| s.rooted_name() == lookup_rooted)
        .ok_or_else(|| {
            anyhow::anyhow!(
                "Resolved target `{}` (lookup `{}`) missing from parsed shard declarations",
                canon_rooted,
                lookup_rooted
            )
        })?;
    Ok(ServerTargetDigest {
        canon_rooted: canon_rooted.to_string(),
        gen_rooted,
        prefix_env_hash: sh.prefix_env_hash.clone(),
        stmt_hash: sh.stmt_hash.clone(),
        proof_hash: sh.proof_hash.clone(),
    })
}

impl HttpShardReceiptContext {
    fn resolve_base(
        store: &TurboStore,
        toolchain: &str,
        req_lean_path: &str,
        shard_source: &str,
        lean_args_digest: Option<&str>,
        allowed_axioms: &[String],
        allowed_axioms_csv: &str,
    ) -> (
        Self,
        std::collections::HashMap<String, String>,
        std::path::PathBuf,
    ) {
        let (mut env_vars, lean_bin) =
            resolve_server_lean_env_and_bin(store, toolchain, req_lean_path);
        env_vars.insert(
            crate::splitter::ALLOWED_AXIOMS_ENV.to_string(),
            allowed_axioms_csv.to_string(),
        );
        let (raw_imports_csv, _) = crate::zygote::split_shard_for_zygote(shard_source);
        let zctx = crate::zygote::resolve_zygote_context(
            toolchain,
            req_lean_path,
            &env_vars,
            &lean_bin,
            &raw_imports_csv,
        );
        let mut canon_axioms: Vec<String> = allowed_axioms
            .iter()
            .map(|s| s.trim())
            .filter(|s| !s.is_empty())
            .map(String::from)
            .collect();
        canon_axioms.sort();
        canon_axioms.dedup();
        let import_context = format!(
            "{}|{}|{}",
            zctx.lean_path, zctx.imports_csv, zctx.olean_digest
        );
        (
            Self {
                lean_args_digest: lean_args_digest.unwrap_or("").to_string(),
                allowed_axioms: canon_axioms,
                target_context: Vec::new(),
                target_content_digests: Vec::new(),
                toolchain_policy: zctx.toolchain_policy,
                import_context,
            },
            env_vars,
            lean_bin,
        )
    }

    fn with_targets_and_digests(
        &self,
        targets: &[String],
        shards: &[crate::splitter::TheoremShard],
        fast_map: &crate::splitter::FastVerifyMap,
    ) -> Result<(Self, Vec<ServerTargetDigest>)> {
        let mut canon_targets: Vec<String> = targets
            .iter()
            .map(|t| t.trim())
            .filter(|t| !t.is_empty())
            .map(String::from)
            .collect();
        canon_targets.sort();
        canon_targets.dedup();
        let mut digests = Vec::with_capacity(canon_targets.len());
        let mut content_entries = Vec::with_capacity(canon_targets.len());
        for canon in &canon_targets {
            let td = compute_server_target_digest(canon, shards, fast_map)?;
            content_entries.push(td.framed_entry());
            digests.push(td);
        }
        let mut out = self.clone();
        out.target_context = canon_targets;
        out.target_content_digests = content_entries;
        Ok((out, digests))
    }
}

fn hash_framed_str(h: &mut blake3::Hasher, s: &str) {
    h.update(&(s.len() as u64).to_le_bytes());
    h.update(s.as_bytes());
}

fn hash_framed_slice(h: &mut blake3::Hasher, items: &[String]) {
    h.update(&(items.len() as u64).to_le_bytes());
    for item in items {
        hash_framed_str(h, item);
    }
}

// Caller keys are opaque; the server binds every cached HTTP receipt to its full effective
// verification context (options, allowed axioms, audited targets, server-computed content digests,
// toolchain/compiler, and LEAN_PATH).
fn context_bound_http_key(key: &str, ctx: &HttpShardReceiptContext) -> String {
    let base = server_receipt_key(key);
    let mut h = blake3::Hasher::new();
    h.update(b"http-shard-context-v6:");
    hash_framed_str(&mut h, &base);
    hash_framed_str(&mut h, &ctx.lean_args_digest);
    hash_framed_slice(&mut h, &ctx.allowed_axioms);
    hash_framed_slice(&mut h, &ctx.target_context);
    hash_framed_slice(&mut h, &ctx.target_content_digests);
    hash_framed_str(&mut h, &ctx.toolchain_policy);
    hash_framed_str(&mut h, &ctx.import_context);
    h.finalize().to_hex().to_string()
}

fn context_bound_receipt(
    mut receipt: serde_json::Value,
    ctx: &HttpShardReceiptContext,
) -> Result<Vec<u8>> {
    if !receipt.is_object() {
        anyhow::bail!("HTTP shard receipt must serialize as a JSON object");
    }
    receipt["receipt_schema"] = serde_json::Value::String("srv-v6".to_string());
    receipt["lean_args_digest"] = serde_json::Value::String(ctx.lean_args_digest.clone());
    receipt["allowed_axioms"] = serde_json::json!(ctx.allowed_axioms);
    receipt["target_context"] = serde_json::json!(ctx.target_context);
    receipt["target_content_digests"] = serde_json::json!(ctx.target_content_digests);
    receipt["toolchain_policy"] = serde_json::Value::String(ctx.toolchain_policy.clone());
    receipt["import_context"] = serde_json::Value::String(ctx.import_context.clone());
    Ok(serde_json::to_vec(&receipt)?)
}

fn receipt_matches_http_context(
    receipt: &serde_json::Value,
    ctx: &HttpShardReceiptContext,
) -> bool {
    let str_vec_eq = |field: &serde_json::Value, expected: &[String]| -> bool {
        field
            .as_array()
            .map(|arr| {
                arr.len() == expected.len()
                    && arr
                        .iter()
                        .zip(expected)
                        .all(|(v, exp)| v.as_str() == Some(exp.as_str()))
            })
            .unwrap_or(false)
    };
    receipt["receipt_schema"].as_str() == Some("srv-v6")
        && receipt["lean_args_digest"].as_str() == Some(ctx.lean_args_digest.as_str())
        && str_vec_eq(&receipt["allowed_axioms"], &ctx.allowed_axioms)
        && str_vec_eq(&receipt["target_context"], &ctx.target_context)
        && str_vec_eq(
            &receipt["target_content_digests"],
            &ctx.target_content_digests,
        )
        && receipt["toolchain_policy"].as_str() == Some(ctx.toolchain_policy.as_str())
        && receipt["import_context"].as_str() == Some(ctx.import_context.as_str())
}

fn context_matching_http_hits(
    store: &TurboStore,
    key_contexts: &[(String, HttpShardReceiptContext)],
    trust_domain: &str,
) -> Result<std::collections::HashMap<String, String>> {
    let keys: Vec<String> = key_contexts.iter().map(|(k, _)| k.clone()).collect();
    let expected_by_key: std::collections::HashMap<&str, &HttpShardReceiptContext> = key_contexts
        .iter()
        .map(|(k, ctx)| (k.as_str(), ctx))
        .collect();
    let mut hits = store.batch_get_theorem_shards_readonly(&keys, trust_domain)?;
    hits.retain(|k, blob_hash| {
        let Some(expected) = expected_by_key.get(k.as_str()) else {
            return false;
        };
        fs::read(store.blob_path(blob_hash))
            .ok()
            .and_then(|bytes| serde_json::from_slice::<serde_json::Value>(&bytes).ok())
            .map(|r| receipt_matches_http_context(&r, expected))
            .unwrap_or(false)
    });
    Ok(hits)
}

fn execute_check_shard_payload_deferred_with_domain(
    store: &mut TurboStore,
    req: &CheckShardHttpRequest,
    trust_domain: &str,
    timeout_ms: Option<u64>,
) -> Result<(
    serde_json::Value,
    Option<(String, Vec<(String, String, Vec<u8>, i64)>)>,
    Option<String>,
)> {
    let t0 = std::time::Instant::now();
    if req.shard_key.is_empty() || req.shard_source.is_empty() {
        anyhow::bail!("Missing shard_key or shard_source in /check-shard request");
    }

    let filtered_req_args = crate::module_builder::validate_effective_lean_args(&req.lean_args)?;
    let req_args_digest_opt = crate::module_builder::compute_lean_args_digest(&filtered_req_args)?;

    let (req_allowed, req_allowed_csv) =
        resolve_request_axiom_policy(req.allowed_axioms.as_deref(), trust_domain);
    // A named target is gated (and checked with its name) on every path, the local daemon's
    // `skip_cas_lock` requests included. A batch names its targets in `targets`; one that names none
    // has every declaration of its source treated as a target (so no `sorry` stub is admitted).
    let parsed_source = crate::splitter::split_lean_source_fast_no_cone(&req.shard_source, &[]);
    let fast_map = crate::splitter::FastVerifyMap::parse_and_validate(
        &req.shard_source,
        &parsed_source.shards,
    )?;
    let named_target = !matches!(req.decl.as_str(), "" | "__batch__" | "__coalesced_batch__");
    let decl_resolved = if named_target {
        Some(crate::splitter::resolve_shard_rooted_targets_with_map(
            &parsed_source.shards,
            std::slice::from_ref(&req.decl),
            &fast_map,
        )?)
    } else {
        None
    };
    let explicit_targets = if !req.targets.is_empty() {
        Some(crate::splitter::resolve_shard_rooted_targets_with_map(
            &parsed_source.shards,
            &req.targets,
            &fast_map,
        )?)
    } else {
        None
    };
    let mut stub_targets: Vec<String> = match (decl_resolved, explicit_targets) {
        (Some(d), Some(mut t)) => {
            t.sort();
            t.dedup();
            if t != d {
                anyhow::bail!(
                    "Contradictory /check-shard request: `decl` resolves to {:?} while `targets` resolves to {:?}",
                    d,
                    t
                );
            }
            d
        }
        (Some(d), None) => d,
        (None, Some(mut t)) => {
            t.sort();
            t.dedup();
            t
        }
        (None, None) => parsed_source
            .shards
            .iter()
            .map(|sh| fast_map.canonical_rooted_for_shard(sh))
            .collect(),
    };
    stub_targets.sort();
    stub_targets.dedup();
    if stub_targets.is_empty() {
        anyhow::bail!("No theorem declarations found in /check-shard request");
    }
    let canonical_decl: String = if stub_targets.len() == 1 {
        stub_targets[0]
            .strip_prefix("_root_.")
            .unwrap_or(stub_targets[0].as_str())
            .to_string()
    } else {
        "__batch__".to_string()
    };

    if source_may_have_hygiene_issue(&req.shard_source) {
        let clean_source = crate::splitter::strip_lean_comments(&req.shard_source);
        let source_violations = crate::splitter::audit_hygiene(&clean_source);
        if source_violations.native_violation_under(&req_allowed)
            || source_violations.has_trust_compiler
            || source_violations.has_unsafe
            || source_violations.has_extern_or_implemented_by
        {
            anyhow::bail!(
                "Soundness hygiene violation in remote shard `{}`: {:?}",
                canonical_decl,
                source_violations.flagged_items
            );
        }

        if source_violations.has_sorry {
            let target_body = if parsed_source.shards.len() == 1 {
                let s = &parsed_source.shards[0];
                format!("{}\n{}", s.signature_text, s.proof_text)
            } else {
                let req_set: std::collections::HashSet<String> =
                    stub_targets.iter().cloned().collect();
                let matched: Vec<String> = parsed_source
                    .shards
                    .iter()
                    .filter(|s| fast_map.shard_matches_targets(s, &req_set))
                    .map(|s| format!("{}\n{}", s.signature_text, s.proof_text))
                    .collect();
                if matched.is_empty() {
                    clean_source.clone()
                } else {
                    matched.join("\n")
                }
            };
            let clean_target = crate::splitter::strip_lean_comments(&target_body);
            let violations = crate::splitter::audit_hygiene(&clean_target);
            if !violations.disallowed_items_under(&req_allowed).is_empty() {
                anyhow::bail!(
                    "Soundness hygiene violation in remote shard `{}`: {:?}",
                    canonical_decl,
                    violations.flagged_items
                );
            }
        }
    }

    let toolchain = if req.toolchain.is_empty() || req.toolchain == "unknown" {
        "leanprover/lean4:v4.35.0"
    } else {
        req.toolchain.as_str()
    };

    let (base_ctx, mut env_vars, lean_bin) = HttpShardReceiptContext::resolve_base(
        store,
        toolchain,
        &req.lean_path,
        &req.shard_source,
        req_args_digest_opt.as_deref(),
        &req_allowed,
        &req_allowed_csv,
    );
    let (receipt_ctx, target_digests) =
        base_ctx.with_targets_and_digests(&stub_targets, &parsed_source.shards, &fast_map)?;
    let (server_prefix_hash, server_stmt_hash, server_proof_hash) = if target_digests.len() == 1 {
        let d = &target_digests[0];
        (
            d.prefix_env_hash.clone(),
            d.stmt_hash.clone(),
            d.proof_hash.clone(),
        )
    } else {
        let mut h_pre = blake3::Hasher::new();
        let mut h_stmt = blake3::Hasher::new();
        let mut h_prf = blake3::Hasher::new();
        for d in &target_digests {
            hash_framed_str(&mut h_pre, &d.prefix_env_hash);
            hash_framed_str(&mut h_stmt, &d.stmt_hash);
            hash_framed_str(&mut h_prf, &d.proof_hash);
        }
        (
            h_pre.finalize().to_hex().to_string(),
            h_stmt.finalize().to_hex().to_string(),
            h_prf.finalize().to_hex().to_string(),
        )
    };
    let cache_key = context_bound_http_key(&req.shard_key, &receipt_ctx);

    if !req.skip_cas_lock
        && context_matching_http_hits(
            store,
            &[(cache_key.clone(), receipt_ctx.clone())],
            trust_domain,
        )?
        .contains_key(&cache_key)
    {
        return Ok((
            serde_json::json!({
                "status": "remote_theorem_cache_hit",
                "decl": canonical_decl,
                "verified_targets": stub_targets,
                "shard_key": req.shard_key,
                "coalesced": false,
                "interface_hash": req.interface_hash,
                "prefix_env_hash": server_prefix_hash,
                "server_arch": std::env::consts::ARCH,
                "server_elapsed_ms": t0.elapsed().as_millis()
            }),
            None,
            Some(cache_key.clone()),
        ));
    }

    let mut zygote_used = false;
    let mut zygote_env_cache_hit = false;
    let mut zygote_import_us = 0u64;
    let mut zygote_elab_us = 0u64;
    let mut zygote_heartbeats = 0u64;
    let mut zygote_proof_nodes = 0u64;
    let mut zygote_rss_delta = 0i64;
    let mut zygote_peak_rss = 0u64;
    let mut zygote_used_constants: Vec<String> = Vec::new();

    match crate::zygote::eval_with_zygote_pool_for_targets(
        store,
        toolchain,
        &req.lean_path,
        &env_vars,
        &lean_bin,
        &req.shard_source,
        &stub_targets,
        Some(crate::zygote::remaining_timeout_ms(timeout_ms, t0)),
        &filtered_req_args,
    ) {
        Ok(zreply) if zreply.import_ok && !zreply.crashed && !zreply.timed_out => {
            if !zreply.ok {
                anyhow::bail!(
                    "Remote `lean` shard verification failed for `{}`:\n{}",
                    req.decl,
                    zreply.errors.join("\n")
                );
            }
            zygote_used = true;
            zygote_env_cache_hit = zreply.env_cache_hit;
            zygote_import_us = zreply.import_us;
            zygote_elab_us = zreply.elab_us;
            zygote_heartbeats = zreply.heartbeats;
            zygote_proof_nodes = zreply.proof_term_nodes;
            zygote_rss_delta = zreply.rss_delta_mb;
            zygote_peak_rss = zreply.peak_rss_mb;
            zygote_used_constants = zreply.used_constants;
        }
        Ok(zreply) if zreply.crashed || zreply.timed_out => {
            anyhow::bail!(
                "Remote `lean` shard verification failed for `{}`:\n{}",
                req.decl,
                zreply.errors.join("\n")
            );
        }
        Ok(_) if req.skip_cas_lock => {
            return Err(crate::zygote::ZygoteImportUnavailable(req.decl.clone()).into());
        }
        Ok(_) => {}
        Err(e) => return Err(e),
    }

    if !zygote_used {
        let audit_set: std::collections::HashSet<String> = stub_targets.iter().cloned().collect();
        set_elan_toolchain(&mut env_vars, &req.toolchain);
        let out = crate::zygote::run_audited_lean_shard(
            store,
            &lean_bin,
            &env_vars,
            None,
            &req.shard_source,
            &audit_set,
            &filtered_req_args,
            Some(crate::zygote::remaining_timeout_ms(timeout_ms, t0)),
        )?;
        if !out.status.success() {
            anyhow::bail!(
                "Remote `lean` shard verification failed for `{}`:\n{}\n{}",
                req.decl,
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            );
        }
    }

    let dur_ms = t0.elapsed().as_millis() as i64;
    let dur_us = t0.elapsed().as_micros() as u64;
    let deferred = if req.skip_cas_lock {
        None
    } else {
        let receipt_obj = serde_json::json!({
            "decl": canonical_decl,
            "prefix_env_hash": server_prefix_hash,
            "stmt_hash": server_stmt_hash,
            "proof_hash": server_proof_hash,
            "verified_at": now_unix()
        });
        let receipt = context_bound_receipt(receipt_obj, &receipt_ctx)?;
        Some((
            toolchain.to_string(),
            vec![(cache_key, canonical_decl.clone(), receipt, dur_ms)],
        ))
    };

    Ok((
        serde_json::json!({
            "status": "remote_theorem_verified",
            "decl": canonical_decl,
            "verified_targets": stub_targets,
            "shard_key": req.shard_key,
            "interface_hash": req.interface_hash,
            "prefix_env_hash": server_prefix_hash,
            "server_arch": std::env::consts::ARCH,
            "server_elapsed_ms": dur_ms,
            "server_elapsed_us": dur_us,
            "zygote_used": zygote_used,
            "zygote_env_cache_hit": zygote_env_cache_hit,
            "zygote_import_us": zygote_import_us,
            "zygote_elab_us": zygote_elab_us,
            "heartbeats": zygote_heartbeats,
            "proof_term_nodes": zygote_proof_nodes,
            "rss_delta_mb": zygote_rss_delta,
            "peak_rss_mb": zygote_peak_rss,
            "used_constants": zygote_used_constants
        }),
        deferred,
        None,
    ))
}

#[cfg(test)]
pub(crate) fn execute_check_shard_payload(
    store: &mut TurboStore,
    req: &CheckShardHttpRequest,
) -> Result<serde_json::Value> {
    let (val, deferred, deferred_hit) =
        execute_check_shard_payload_deferred_with_domain(store, req, "trusted", None)?;
    if let Some((tc, items)) = deferred {
        store.batch_publish_theorem_shards(&tc, "trusted", &items)?;
    }
    if let Some(hk) = deferred_hit {
        store.batch_increment_action_hits(&[hk])?;
    }
    Ok(val)
}

fn execute_check_shards_batch_payload_deferred(
    store: &mut TurboStore,
    req: &CheckShardsBatchRequest,
    timeout_ms: Option<u64>,
) -> Result<(
    CheckShardsBatchResponse,
    Option<(String, String, Vec<(String, String, Vec<u8>, i64)>)>,
    Vec<String>,
)> {
    let t0 = std::time::Instant::now();
    if req.items.is_empty() || req.coalesced_shard_source.is_empty() {
        anyhow::bail!("Missing items or coalesced_shard_source in /check-shards-batch request");
    }

    let trust_domain = if req.trust_domain.is_empty() {
        "trusted"
    } else {
        req.trust_domain.as_str()
    };
    let toolchain = if req.toolchain.is_empty() || req.toolchain == "unknown" {
        "leanprover/lean4:v4.35.0"
    } else {
        req.toolchain.as_str()
    };

    let filtered_batch_args = crate::module_builder::validate_effective_lean_args(&req.lean_args)?;
    let batch_args_digest_opt =
        crate::module_builder::compute_lean_args_digest(&filtered_batch_args)?;
    let (req_allowed, req_allowed_csv) =
        resolve_request_axiom_policy(req.allowed_axioms.as_deref(), trust_domain);
    let parsed_batch =
        crate::splitter::split_lean_source_fast_no_cone(&req.coalesced_shard_source, &[]);
    let raw_item_targets: Vec<String> = req.items.iter().map(|i| i.decl_name.clone()).collect();
    let (resolved_item_decls, batch_fast_map) = crate::splitter::resolve_shard_rooted_targets(
        &req.coalesced_shard_source,
        &parsed_batch.shards,
        &raw_item_targets,
    )?;
    let (base_ctx, mut env_vars, lean_bin) = HttpShardReceiptContext::resolve_base(
        store,
        toolchain,
        &req.lean_path,
        &req.coalesced_shard_source,
        batch_args_digest_opt.as_deref(),
        &req_allowed,
        &req_allowed_csv,
    );
    let mut item_key_contexts: Vec<(String, HttpShardReceiptContext)> =
        Vec::with_capacity(req.items.len());
    let mut item_server_digests: Vec<ServerTargetDigest> = Vec::with_capacity(req.items.len());
    for (i, canon_decl) in req.items.iter().zip(&resolved_item_decls) {
        let (ctx, mut d_vec) = base_ctx.with_targets_and_digests(
            std::slice::from_ref(canon_decl),
            &parsed_batch.shards,
            &batch_fast_map,
        )?;
        let td = d_vec.pop().unwrap_or_default();
        item_key_contexts.push((context_bound_http_key(&i.shard_key, &ctx), ctx));
        item_server_digests.push(td);
    }
    let bound_hits = context_matching_http_hits(store, &item_key_contexts, trust_domain)?;
    let hit_mask: Vec<bool> = item_key_contexts
        .iter()
        .map(|(k, _)| bound_hits.contains_key(k))
        .collect();
    let hit_keys: Vec<String> = item_key_contexts
        .iter()
        .zip(&hit_mask)
        .filter(|&(_, &hit)| hit)
        .map(|((k, _), _)| k.clone())
        .collect();
    let cache_hits = hit_keys.len();

    if source_may_have_hygiene_issue(&req.coalesced_shard_source) {
        let stripped = crate::splitter::strip_lean_comments(&req.coalesced_shard_source);
        let violations = crate::splitter::audit_hygiene(&stripped);
        if violations.native_violation_under(&req_allowed)
            || violations.has_trust_compiler
            || violations.has_unsafe
            || violations.has_extern_or_implemented_by
        {
            anyhow::bail!(
                "Soundness hygiene violation in remote batch shard payload: {:?}",
                violations.flagged_items
            );
        }
        if violations.has_sorry {
            let target_set: HashSet<String> = resolved_item_decls
                .iter()
                .zip(&hit_mask)
                .filter(|&(_, &hit)| !hit)
                .map(|(d, _)| d.clone())
                .collect();
            let uncached_has_sorry = parsed_batch.shards.iter().any(|sh| {
                batch_fast_map.shard_matches_targets(sh, &target_set)
                    && crate::splitter::audit_hygiene(&crate::splitter::strip_lean_comments(
                        &sh.proof_text,
                    ))
                    .has_sorry
            });
            if uncached_has_sorry || parsed_batch.shards.is_empty() {
                anyhow::bail!(
                    "Soundness hygiene violation in remote batch shard payload: uncached theorem contains `sorry`"
                );
            }
        }
    }

    // Cached results are served only after the payload passed the hygiene gates above.
    if cache_hits == req.items.len() {
        return Ok((
            CheckShardsBatchResponse {
                ok: true,
                verified_count: 0,
                cache_hits,
                elapsed_ms: (t0.elapsed().as_secs_f64() * 1000.0 * 100.0).round() / 100.0,
                exit_code: 0,
                stdout: String::new(),
                stderr: String::new(),
                error: None,
            },
            None,
            hit_keys,
        ));
    }

    let server_uncached_decls: HashSet<String> = resolved_item_decls
        .iter()
        .zip(&hit_mask)
        .filter(|&(_, &hit)| !hit)
        .map(|(d, _)| d.clone())
        .collect();
    let effective_batch_source = if cache_hits > 0 {
        crate::splitter::build_coalesced_shard_source(
            &req.coalesced_shard_source,
            &server_uncached_decls,
        )
    } else {
        req.coalesced_shard_source.clone()
    };

    let mut zygote_handled = false;
    let mut stdout = String::new();
    let mut stderr = String::new();
    let mut exit_code = 0i32;

    let batch_audit = server_uncached_decls;
    let mut batch_targets: Vec<String> = batch_audit.iter().cloned().collect();
    batch_targets.sort();
    match crate::zygote::eval_with_zygote_pool_for_targets(
        store,
        toolchain,
        &req.lean_path,
        &env_vars,
        &lean_bin,
        &effective_batch_source,
        &batch_targets,
        Some(crate::zygote::remaining_timeout_ms(timeout_ms, t0)),
        &filtered_batch_args,
    ) {
        Ok(zreply) if zreply.import_ok || zreply.crashed || zreply.timed_out => {
            zygote_handled = true;
            if !zreply.ok || zreply.crashed || zreply.timed_out {
                exit_code = 1;
                stderr = zreply.errors.join("\n");
            }
        }
        Ok(_) => {}
        Err(e) => {
            zygote_handled = true;
            exit_code = 1;
            stderr = format!("{:#}", e);
        }
    }

    if !zygote_handled {
        if !req.lean_path.is_empty() {
            let mut full_lean_path = req.lean_path.clone();
            if let Some(tc_lib_lean) = lean_bin
                .parent()
                .and_then(|b| b.parent())
                .map(|tc| tc.join("lib").join("lean"))
                .filter(|p| p.exists())
            {
                let tc_lib_str = tc_lib_lean.to_string_lossy();
                if !full_lean_path.split(':').any(|e| e == tc_lib_str) {
                    full_lean_path = format!("{}:{}", full_lean_path, tc_lib_str);
                }
            }
            env_vars.insert("LEAN_PATH".to_string(), full_lean_path);
        }

        set_elan_toolchain(&mut env_vars, &req.toolchain);
        match crate::zygote::run_audited_lean_shard(
            store,
            &lean_bin,
            &env_vars,
            None,
            &effective_batch_source,
            &batch_audit,
            &filtered_batch_args,
            Some(crate::zygote::remaining_timeout_ms(timeout_ms, t0)),
        ) {
            Ok(out) => {
                exit_code = out.status.code().unwrap_or(-1);
                stdout = String::from_utf8_lossy(&out.stdout).into_owned();
                stderr = String::from_utf8_lossy(&out.stderr).into_owned();
            }
            Err(e) => {
                exit_code = 1;
                stderr = format!("{:#}", e);
            }
        }
    }

    let elapsed_ms = (t0.elapsed().as_secs_f64() * 1000.0 * 100.0).round() / 100.0;

    if exit_code != 0 {
        return Ok((
            CheckShardsBatchResponse {
                ok: false,
                verified_count: 0,
                cache_hits,
                elapsed_ms,
                exit_code,
                stdout: stdout.clone(),
                stderr: stderr.clone(),
                error: Some(format!(
                    "Remote `lean` batch shard verification failed (exit {}):\n{}\n{}",
                    exit_code, stdout, stderr
                )),
            },
            None,
            Vec::new(),
        ));
    }

    let uncached_count = req.items.len().saturating_sub(cache_hits);
    let per_shard_ms = ((t0.elapsed().as_millis() as i64) / (uncached_count.max(1) as i64)).max(1);
    let now = now_unix();
    let mut publish_items = Vec::with_capacity(uncached_count);
    for ((canon_decl, srv_digest), ((bound_key, item_ctx), &hit)) in resolved_item_decls
        .iter()
        .zip(&item_server_digests)
        .zip(item_key_contexts.iter().zip(&hit_mask))
    {
        if hit {
            continue;
        }
        let clean_decl = canon_decl.strip_prefix("_root_.").unwrap_or(canon_decl);
        let receipt_obj = serde_json::json!({
            "decl": clean_decl,
            "prefix_env_hash": srv_digest.prefix_env_hash,
            "stmt_hash": srv_digest.stmt_hash,
            "proof_hash": srv_digest.proof_hash,
            "verified_at": now
        });
        let receipt = context_bound_receipt(receipt_obj, item_ctx)?;
        publish_items.push((
            bound_key.clone(),
            clean_decl.to_string(),
            receipt,
            per_shard_ms,
        ));
    }

    Ok((
        CheckShardsBatchResponse {
            ok: true,
            verified_count: uncached_count,
            cache_hits,
            elapsed_ms,
            exit_code: 0,
            stdout,
            stderr,
            error: None,
        },
        Some((
            toolchain.to_string(),
            trust_domain.to_string(),
            publish_items,
        )),
        hit_keys,
    ))
}

#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn execute_fastcheck_payload(
    store: &TurboStore,
    req: &FastCheckHttpRequest,
) -> Result<serde_json::Value> {
    let (metrics, deferred) = execute_fastcheck_payload_deferred(store, req)?;
    if let Some((staging, cgen_src, cached_bin)) = deferred {
        let _ = try_populate_cached_bin_from_shared(&staging, &cgen_src, &cached_bin);
    }
    Ok(metrics)
}

fn execute_fastcheck_payload_deferred(
    store: &TurboStore,
    req: &FastCheckHttpRequest,
) -> Result<(
    serde_json::Value,
    Option<(std::path::PathBuf, String, std::path::PathBuf)>,
)> {
    let t0 = std::time::Instant::now();
    if !req.local_path.is_empty() {
        anyhow::bail!("local_path is forbidden on HTTP /fast-check");
    }
    if !req.precomputed_bin_key.is_empty() {
        validate_precomputed_bin_key(&req.precomputed_bin_key)?;
    }
    if req.filename.contains('/')
        || req.filename.contains('\\')
        || req.filename.contains("..")
        || req.filename.contains('\0')
    {
        anyhow::bail!("Invalid filename in /fast-check");
    }
    let is_cu = req.gpu || req.filename.ends_with(".cu");
    let staging = store.fast_staging_dir();
    let bin_dir = store.root.join("fastcheck_bins");
    fs::create_dir_all(&bin_dir)?;
    let canon_root = fs::canonicalize(&store.root).unwrap_or_else(|_| store.root.clone());
    let canon_bin_dir = fs::canonicalize(&bin_dir).unwrap_or_else(|_| bin_dir.clone());
    if !canon_bin_dir.starts_with(&canon_root) {
        anyhow::bail!("fastcheck_bins directory escaped store root");
    }
    let pid = std::process::id();
    let ts = next_tmp_id();

    if is_cu {
        fs::create_dir_all(&staging)?;
        let bin_key = if !req.precomputed_bin_key.is_empty() {
            req.precomputed_bin_key.clone()
        } else {
            compute_fastcheck_binary_key(true, &req.source)
        };
        validate_precomputed_bin_key(&bin_key)?;
        let cached_bin = canon_bin_dir.join(&bin_key);
        if cached_bin.parent() != Some(canon_bin_dir.as_path()) {
            anyhow::bail!("cached_bin path escaped fastcheck_bins");
        }
        let compile_cache_hit = cached_bin.exists();

        if !compile_cache_hit {
            let nvcc_bin = if Path::new("/usr/local/cuda/bin/nvcc").exists() {
                "/usr/local/cuda/bin/nvcc"
            } else {
                "nvcc"
            };
            let tmp_cu = staging.join(format!("http_fc_{}_{}.cu", pid, ts));
            let tmp_bin = staging.join(format!("http_fc_{}_{}.bin", pid, ts));
            fs::write(&tmp_cu, &req.source)?;

            let compile_out = Command::new(nvcc_bin)
                .arg("-O3")
                .arg("-arch=native")
                .arg(&tmp_cu)
                .arg("-lcuda")
                .arg("-o")
                .arg(&tmp_bin)
                .output()
                .with_context(|| format!("Failed to execute `{}`", nvcc_bin))?;
            let _ = fs::remove_file(&tmp_cu);
            if !compile_out.status.success() {
                let stderr = String::from_utf8_lossy(&compile_out.stderr);
                let stdout = String::from_utf8_lossy(&compile_out.stdout);
                anyhow::bail!("`nvcc -O3` failed:\n{}\n{}", stdout, stderr);
            }
            if fs::rename(&tmp_bin, &cached_bin).is_err() {
                fs::copy(&tmp_bin, &cached_bin)?;
                let _ = fs::remove_file(&tmp_bin);
            }
        }

        let run_t0 = std::time::Instant::now();
        let out = Command::new(&cached_bin)
            .env("CUDA_MODULE_LOADING", "LAZY")
            .output()
            .context("Failed to execute compiled CUDA fast-check binary")?;
        let exec_ms = run_t0.elapsed().as_millis();
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        if !out.status.success() {
            anyhow::bail!("CUDA fast-check binary failed:\n{}\n{}", stdout, stderr);
        }

        let mut metrics = crate::parse_gpu_fastcheck_output(
            &stdout,
            exec_ms,
            t0.elapsed().as_millis(),
            Some("http_server"),
        );
        metrics["mode"] = serde_json::json!("http_remote_gpu_cuda");
        metrics["server_arch"] = serde_json::json!(std::env::consts::ARCH);
        metrics["compile_cache_hit"] = serde_json::json!(compile_cache_hit);
        metrics["binary_cache_key"] = serde_json::json!(bin_key);
        Ok((metrics, None))
    } else {
        let has_main = req
            .has_main
            .unwrap_or_else(|| req.source.contains("def main"));
        let bin_key = if !req.precomputed_bin_key.is_empty() {
            req.precomputed_bin_key.clone()
        } else if has_main {
            compute_fastcheck_binary_key(false, &req.source)
        } else {
            compute_fastcheck_binary_key_parts(false, &req.source, FASTCHECK_NO_MAIN_SUFFIX)
        };
        validate_precomputed_bin_key(&bin_key)?;
        let cached_bin = canon_bin_dir.join(&bin_key);
        if cached_bin.parent() != Some(canon_bin_dir.as_path()) {
            anyhow::bail!("cached_bin path escaped fastcheck_bins");
        }
        let compile_cache_hit = cached_bin.exists();
        let mut deferred_pop = None;

        if !compile_cache_hit {
            if !has_main {
                let shared_bin = shared_fastcheck_cgen_path(&staging, FASTCHECK_PRELUDE_HARNESS);
                if shared_bin.exists() {
                    ensure_shared_fastcheck_out(&shared_bin);
                }
                let shared_out = shared_bin.with_extension("out");
                if shared_bin.exists() && shared_out.exists() {
                    let run_t0 = std::time::Instant::now();
                    if let Ok(cached_text) = fs::read_to_string(&shared_out) {
                        if let Some((status_ok, body)) =
                            is_valid_cached_fastcheck_out(&cached_text, true)
                        {
                            let exec_us = run_t0.elapsed().as_micros().max(1);
                            deferred_pop =
                                Some((staging, FASTCHECK_PRELUDE_HARNESS.to_string(), cached_bin));
                            return Ok((
                                serde_json::json!({
                                    "status": if status_ok { "ok" } else { "counterexample_found" },
                                    "mode": "http_remote_cpu_perceus",
                                    "server_arch": std::env::consts::ARCH,
                                    "compile_cache_hit": false,
                                    "binary_cache_key": bin_key,
                                    "exec_us": exec_us,
                                    "total_ms": t0.elapsed().as_millis(),
                                    "output": body.trim()
                                }),
                                deferred_pop,
                            ));
                        }
                    }
                }
            }

            fs::create_dir_all(&staging)?;
            let raw_source = req.source.clone();
            let src_text = if has_main {
                raw_source.clone()
            } else {
                format!("{}{}", raw_source, FASTCHECK_NO_MAIN_SUFFIX)
            };
            let cgen_fast_src = if !has_main {
                Some(FASTCHECK_PRELUDE_HARNESS.to_string())
            } else if !raw_source.contains("import ") && !raw_source.contains("prelude") {
                Some(format!("prelude\nimport Init.System.IO\n{}", raw_source))
            } else {
                None
            };

            let shared_populated = cgen_fast_src
                .as_deref()
                .map(|s| try_populate_cached_bin_from_shared(&staging, s, &cached_bin))
                .unwrap_or(false)
                || try_populate_cached_bin_from_shared(&staging, &src_text, &cached_bin);

            if !shared_populated {
                let tmp_lean = staging.join(format!("http_fc_{}_{}.lean", pid, ts));
                let tmp_c = staging.join(format!("http_fc_{}_{}.c", pid, ts));
                let tmp_bin = staging.join(format!("http_fc_{}_{}.bin", pid, ts));

                let (env_vars, lean_bin) =
                    resolve_server_lean_env_and_bin(store, "leanprover/lean4:v4.35.0", "");
                let leanc_bin = lean_bin
                    .parent()
                    .map(|p| p.join("leanc"))
                    .filter(|cand| cand.exists())
                    .or_else(|| {
                        env_vars.get("PATH").and_then(|p| {
                            p.split(':')
                                .map(|dir| Path::new(dir).join("leanc"))
                                .find(|cand| cand.exists())
                        })
                    })
                    .unwrap_or_else(|| std::path::PathBuf::from("leanc"));

                let mut out1_ok = false;
                if let Some(ref fast_src) = cgen_fast_src {
                    fs::write(&tmp_lean, fast_src)?;
                    if let Ok(o) = Command::new(&lean_bin)
                        .arg(format!("--root={}", staging.display()))
                        .arg("-c")
                        .arg(&tmp_c)
                        .arg(&tmp_lean)
                        .current_dir(&staging)
                        .envs(&env_vars)
                        .output()
                    {
                        out1_ok = o.status.success();
                    }
                }
                if !out1_ok {
                    fs::write(&tmp_lean, &src_text)?;
                    let out1 = Command::new(&lean_bin)
                        .arg(format!("--root={}", staging.display()))
                        .arg("-c")
                        .arg(&tmp_c)
                        .arg(&tmp_lean)
                        .current_dir(&staging)
                        .envs(&env_vars)
                        .output()
                        .context("Failed to compile Lean to C via `lean -c`")?;
                    if !out1.status.success() {
                        let _ = fs::remove_file(&tmp_lean);
                        anyhow::bail!(
                            "`lean -c` failed on HTTP fast-check payload:\n{}\n{}",
                            String::from_utf8_lossy(&out1.stdout),
                            String::from_utf8_lossy(&out1.stderr)
                        );
                    }
                }
                let _ = fs::remove_file(&tmp_lean);

                let out2 = compile_fastcheck_c_to_bin(
                    &lean_bin, &leanc_bin, &tmp_c, &tmp_bin, &staging, &env_vars,
                )?;
                let _ = fs::remove_file(&tmp_c);
                if !out2.status.success() {
                    anyhow::bail!(
                        "`leanc -O3` failed on HTTP fast-check payload:\n{}\n{}",
                        String::from_utf8_lossy(&out2.stdout),
                        String::from_utf8_lossy(&out2.stderr)
                    );
                }
                if out1_ok {
                    if let Some(ref fast_src) = cgen_fast_src {
                        save_compiled_bin_to_shared(&staging, fast_src, &tmp_bin);
                    }
                } else {
                    save_compiled_bin_to_shared(&staging, &src_text, &tmp_bin);
                }
                if fs::rename(&tmp_bin, &cached_bin).is_err() {
                    let tmp_dest = bin_dir.join(format!("http_fc_{}_{}.dest.tmp", pid, ts));
                    fs::copy(&tmp_bin, &tmp_dest)?;
                    let _ = fs::remove_file(&tmp_bin);
                    let _ = fs::rename(&tmp_dest, &cached_bin);
                }
            }
        }

        let (status_ok, stdout, exec_us) = run_or_read_cached_fastcheck_bin(&cached_bin)?;

        Ok((
            serde_json::json!({
                "status": if status_ok { "ok" } else { "counterexample_found" },
                "mode": "http_remote_cpu_perceus",
                "server_arch": std::env::consts::ARCH,
                "compile_cache_hit": compile_cache_hit,
                "binary_cache_key": bin_key,
                "exec_us": exec_us,
                "total_ms": t0.elapsed().as_millis(),
                "output": stdout.trim()
            }),
            deferred_pop,
        ))
    }
}

fn write_pack_response(stream: &mut impl Write, status: u16, body: &[u8]) -> Result<()> {
    use sha2::{Digest, Sha256};
    let sha_hex = encode_hex_bytes(&Sha256::digest(body));
    let extra = format!("X-Turbo-Pack-Sha256: {}\r\n", sha_hex);
    write_http_response_with_headers(stream, status, "application/octet-stream", &extra, body)
}

fn write_json_response(
    stream: &mut impl Write,
    status: u16,
    value: &impl serde::Serialize,
) -> Result<()> {
    let body = serde_json::to_vec(value)?;
    write_http_response(stream, status, "application/json", &body)
}

fn write_http_response(
    stream: &mut impl Write,
    status: u16,
    content_type: &str,
    body: &[u8],
) -> Result<()> {
    write_http_response_with_headers(stream, status, content_type, "", body)
}

fn write_http_response_with_headers(
    stream: &mut impl Write,
    status: u16,
    content_type: &str,
    extra_headers: &str,
    body: &[u8],
) -> Result<()> {
    let status_text = match status {
        200 => "OK",
        400 => "Bad Request",
        401 => "Unauthorized",
        403 => "Forbidden",
        404 => "Not Found",
        413 => "Payload Too Large",
        500 => "Internal Server Error",
        503 => "Service Unavailable",
        _ => "Internal Server Error",
    };
    let header = format!(
        "HTTP/1.1 {} {}\r\nContent-Type: {}\r\nContent-Length: {}\r\n{}Connection: close\r\n\r\n",
        status,
        status_text,
        content_type,
        body.len(),
        extra_headers
    );
    if body.len() <= 16384 {
        let mut buf = Vec::with_capacity(header.len() + body.len());
        buf.extend_from_slice(header.as_bytes());
        buf.extend_from_slice(body);
        stream.write_all(&buf)?;
    } else {
        stream.write_all(header.as_bytes())?;
        stream.write_all(body)?;
    }
    stream.flush()?;
    Ok(())
}

#[cfg(test)]
mod bind_auth_tests {
    use super::*;

    type BatchPublication = (String, String, Vec<(String, String, Vec<u8>, i64)>);

    fn publish_batch(
        store: &mut TurboStore,
        publication: Option<BatchPublication>,
    ) -> (String, String) {
        let (tc, domain, entries) = publication.expect("verified batch must publish");
        store
            .batch_publish_theorem_shards(&tc, &domain, &entries)
            .expect("publish");
        (tc, domain)
    }

    #[test]
    fn http_cache_identity_tracks_effective_options_single_and_batch() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir =
            std::env::temp_dir().join(format!("turbo_http_options_{}", crate::pack::next_tmp_id()));
        let mut store = TurboStore::open(Some(&dir))?;
        let source = "import Init\ntheorem http_options : 1 + 1 = 2 := by decide\n";
        let high = vec!["-DmaxHeartbeats=4000000".to_string()];
        let low = vec!["-DmaxHeartbeats=1".to_string()];
        let mut single = CheckShardHttpRequest {
            decl: "http_options".into(),
            shard_key: "same-single-key".into(),
            shard_source: source.into(),
            lean_args: high.clone(),
            ..Default::default()
        };
        let first = execute_check_shard_payload(&mut store, &single)?;
        assert_eq!(first["status"], "remote_theorem_verified");
        assert_eq!(
            execute_check_shard_payload(&mut store, &single)?["status"],
            "remote_theorem_cache_hit"
        );
        // A caller key that merely echoes the server's receipt namespace must miss.
        let single_key = single.shard_key.clone();
        single.shard_key = server_receipt_key(&single_key);
        single.lean_args.clear();
        assert_eq!(
            execute_check_shard_payload(&mut store, &single)?["status"],
            "remote_theorem_verified"
        );
        single.shard_key = single_key;
        single.lean_args = low.clone();
        if let Ok(result) = execute_check_shard_payload(&mut store, &single) {
            assert_eq!(result["status"], "remote_theorem_verified");
        }
        single.lean_args = vec!["--json".into()];
        assert!(execute_check_shard_payload(&mut store, &single).is_err());

        let mut batch = CheckShardsBatchRequest {
            items: vec![crate::pack::CheckShardBatchItem {
                shard_key: "same-batch-key".into(),
                decl_name: "http_options".into(),
                ..Default::default()
            }],
            coalesced_shard_source: source.into(),
            lean_args: high.clone(),
            ..Default::default()
        };
        let (first, publication, hits) =
            execute_check_shards_batch_payload_deferred(&mut store, &batch, None)?;
        assert!(first.ok && first.verified_count == 1 && hits.is_empty());
        let (tc, domain) = publish_batch(&mut store, publication);
        let (warm, _, _) = execute_check_shards_batch_payload_deferred(&mut store, &batch, None)?;
        assert_eq!(warm.cache_hits, 1);
        let batch_key = batch.items[0].shard_key.clone();
        batch.items[0].shard_key = server_receipt_key(&batch_key);
        batch.lean_args.clear();
        let (alias, publication, hits) =
            execute_check_shards_batch_payload_deferred(&mut store, &batch, None)?;
        assert!(alias.ok && alias.cache_hits == 0 && alias.verified_count == 1);
        assert!(publication.is_some() && hits.is_empty());

        // A legacy receipt under a raw caller key must not be served or pruned.
        let legacy_key = "legacy-option-hit".to_string();
        store.batch_publish_theorem_shards(
            &tc,
            &domain,
            &[(
                legacy_key.clone(),
                "http_options_second".into(),
                br#"{"decl":"http_options_second"}"#.to_vec(),
                1,
            )],
        )?;
        batch.items.push(crate::pack::CheckShardBatchItem {
            shard_key: legacy_key,
            decl_name: "http_options_second".into(),
            ..Default::default()
        });
        batch
            .coalesced_shard_source
            .push_str("theorem http_options_second : True := by trivial\n");
        let (partial_alias, publication, hits) =
            execute_check_shards_batch_payload_deferred(&mut store, &batch, None)?;
        assert!(
            partial_alias.ok && partial_alias.cache_hits == 0 && partial_alias.verified_count == 2
        );
        assert!(hits.is_empty());
        let (_, _, entries) = publication.unwrap();
        assert_eq!(entries.len(), 2);
        batch.items.pop();
        batch.coalesced_shard_source = source.into();
        batch.items[0].shard_key = batch_key;
        batch.lean_args = low;
        let (second, _, hits) =
            execute_check_shards_batch_payload_deferred(&mut store, &batch, None)?;
        assert_eq!(second.cache_hits, 0);
        assert!(hits.is_empty());
        // Partial hit: only the entry verified under the requested options may be pruned.
        batch.lean_args = high;
        batch.items.push(crate::pack::CheckShardBatchItem {
            shard_key: "batch-missing-key".into(),
            decl_name: "http_options_second".into(),
            ..Default::default()
        });
        batch
            .coalesced_shard_source
            .push_str("theorem http_options_second : True := by trivial\n");
        let (partial, publication, hits) =
            execute_check_shards_batch_payload_deferred(&mut store, &batch, None)?;
        assert!(partial.ok && partial.cache_hits == 1 && partial.verified_count == 1);
        assert_eq!(hits.len(), 1);
        let (_, _, entries) = publication.unwrap();
        assert_eq!(entries.len(), 1);
        batch.lean_args = vec!["--plugin=unsafe.so".into()];
        assert!(execute_check_shards_batch_payload_deferred(&mut store, &batch, None).is_err());
        assert_eq!(server_receipt_key("legacy-key"), "srv-v6:legacy-key");
        let _ = entries;
        let _ = std::fs::remove_dir_all(dir);
        Ok(())
    }

    #[test]
    fn http_receipts_require_known_context_provenance() -> Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "turbo_http_receipts_{}",
            crate::pack::next_tmp_id()
        ));
        let mut store = TurboStore::open(Some(&dir))?;
        let matching = HttpShardReceiptContext {
            lean_args_digest: "digest".into(),
            allowed_axioms: vec!["propext".into()],
            target_context: vec!["_root_.t".into()],
            target_content_digests: vec!["_root_.t||pre|stmt|prf".into()],
            toolchain_policy: "tc#policy".into(),
            import_context: "lp|Init|dig".into(),
        };
        let mut other = matching.clone();
        other.lean_args_digest.clear();
        let mut mutated_content = matching.clone();
        mutated_content.target_content_digests = vec!["_root_.t||pre|stmt_false|prf".into()];
        let mut v4_receipt = serde_json::json!({
            "receipt_schema": "srv-v4",
            "lean_args_digest": matching.lean_args_digest,
            "allowed_axioms": matching.allowed_axioms,
            "target_context": matching.target_context,
            "toolchain_policy": matching.toolchain_policy,
            "import_context": matching.import_context
        });
        let v5_receipt = serde_json::json!({
            "receipt_schema": "srv-v5",
            "lean_args_digest": matching.lean_args_digest,
            "allowed_axioms": matching.allowed_axioms,
            "target_context": matching.target_context,
            "target_content_digests": matching.target_content_digests,
            "toolchain_policy": matching.toolchain_policy,
            "import_context": matching.import_context
        });
        let entries = [
            ("legacy", br#"{"decl":"unknown-context"}"#.to_vec()),
            ("srv_v4", serde_json::to_vec(&mut v4_receipt)?),
            ("srv_v5", serde_json::to_vec(&v5_receipt)?),
            (
                "matching",
                context_bound_receipt(serde_json::json!({}), &matching)?,
            ),
            (
                "other",
                context_bound_receipt(serde_json::json!({}), &other)?,
            ),
            (
                "mutated_content",
                context_bound_receipt(serde_json::json!({}), &mutated_content)?,
            ),
            ("malformed", b"not-json".to_vec()),
        ]
        .map(|(key, receipt)| (key.to_string(), key.to_string(), receipt, 1));
        store.batch_publish_theorem_shards("test", "trusted", &entries)?;
        let key_contexts: Vec<_> = entries
            .iter()
            .map(|e| (e.0.clone(), matching.clone()))
            .collect();
        let hits = context_matching_http_hits(&store, &key_contexts, "trusted")?;
        assert_eq!(hits.len(), 1);
        assert!(hits.contains_key("matching"));
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn http_cache_misses_when_axioms_targets_or_import_context_tighten() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir =
            std::env::temp_dir().join(format!("turbo_http_context_{}", crate::pack::next_tmp_id()));
        let mut store = TurboStore::open(Some(&dir))?;
        let proved = "import Init\ntheorem t1 : True := trivial\ntheorem t2 : True := sorry\n";
        let mut single = CheckShardHttpRequest {
            decl: "__batch__".into(),
            shard_key: "axiom-target-key".into(),
            shard_source: proved.into(),
            targets: vec!["t1".into()],
            allowed_axioms: Some(vec!["myAx".into()]),
            ..Default::default()
        };
        assert_eq!(
            execute_check_shard_payload(&mut store, &single)?["status"],
            "remote_theorem_verified"
        );
        single.allowed_axioms = Some(vec![]);
        assert_eq!(
            execute_check_shard_payload(&mut store, &single)?["status"],
            "remote_theorem_verified"
        );
        single.allowed_axioms = Some(vec!["myAx".into()]);
        single.targets = vec!["t1".into(), "t2".into()];
        assert!(execute_check_shard_payload(&mut store, &single).is_err());
        single.targets = vec!["t1".into()];
        assert_eq!(
            execute_check_shard_payload(&mut store, &single)?["status"],
            "remote_theorem_cache_hit"
        );
        single.targets = vec!["_root_.t1".into()];
        assert_eq!(
            execute_check_shard_payload(&mut store, &single)?["status"],
            "remote_theorem_cache_hit"
        );
        single.targets.clear();
        single.decl = "t1".into();
        assert_eq!(
            execute_check_shard_payload(&mut store, &single)?["status"],
            "remote_theorem_cache_hit"
        );

        let mut batch = CheckShardsBatchRequest {
            items: vec![crate::pack::CheckShardBatchItem {
                shard_key: "batch-context-key".into(),
                decl_name: "t1".into(),
                ..Default::default()
            }],
            coalesced_shard_source: proved.into(),
            allowed_axioms: Some(vec!["myAx".into()]),
            ..Default::default()
        };
        let (first, publication, _) =
            execute_check_shards_batch_payload_deferred(&mut store, &batch, None)?;
        assert!(first.ok && first.cache_hits == 0);
        publish_batch(&mut store, publication);
        batch.allowed_axioms = Some(vec![]);
        let (tight, _, hits) =
            execute_check_shards_batch_payload_deferred(&mut store, &batch, None)?;
        assert!(tight.ok && tight.cache_hits == 0 && hits.is_empty());
        batch.allowed_axioms = Some(vec!["myAx".into()]);
        batch.items[0].decl_name = "t2".into();
        assert!(
            match execute_check_shards_batch_payload_deferred(&mut store, &batch, None) {
                Ok((sorry_target, _, _)) => !sorry_target.ok && sorry_target.cache_hits == 0,
                Err(_) => true,
            }
        );
        batch.items[0].decl_name = "_root_.t1".into();
        let (rooted, _, _) = execute_check_shards_batch_payload_deferred(&mut store, &batch, None)?;
        assert!(rooted.ok && rooted.cache_hits == 1);

        let mut path_req = CheckShardHttpRequest {
            decl: "t1".into(),
            shard_key: "path-key".into(),
            shard_source: "import Init\ntheorem t1 : True := trivial\n".into(),
            ..Default::default()
        };
        assert_eq!(
            execute_check_shard_payload(&mut store, &path_req)?["status"],
            "remote_theorem_verified"
        );
        path_req.lean_path = std::env::temp_dir().display().to_string();
        assert_eq!(
            execute_check_shard_payload(&mut store, &path_req)?["status"],
            "remote_theorem_verified"
        );
        let real_ax_src = "import Init\naxiom myAx : True\ntheorem ax_thm : True := myAx\n";
        let mut single_ax = CheckShardHttpRequest {
            decl: "ax_thm".into(),
            shard_key: "real-axiom-key".into(),
            shard_source: real_ax_src.into(),
            allowed_axioms: Some(vec!["myAx".into()]),
            ..Default::default()
        };
        assert_eq!(
            execute_check_shard_payload(&mut store, &single_ax)?["status"],
            "remote_theorem_verified"
        );
        assert_eq!(
            execute_check_shard_payload(&mut store, &single_ax)?["status"],
            "remote_theorem_cache_hit"
        );
        single_ax.allowed_axioms = Some(vec![]);
        assert!(execute_check_shard_payload(&mut store, &single_ax).is_err());

        let mut batch_ax = CheckShardsBatchRequest {
            items: vec![crate::pack::CheckShardBatchItem {
                shard_key: "real-batch-axiom-key".into(),
                decl_name: "ax_thm".into(),
                ..Default::default()
            }],
            coalesced_shard_source: real_ax_src.into(),
            allowed_axioms: Some(vec!["myAx".into()]),
            ..Default::default()
        };
        let (ax_ok, pub_ax, _) =
            execute_check_shards_batch_payload_deferred(&mut store, &batch_ax, None)?;
        assert!(ax_ok.ok && ax_ok.cache_hits == 0 && ax_ok.verified_count == 1);
        publish_batch(&mut store, pub_ax);
        let (ax_warm, _, _) =
            execute_check_shards_batch_payload_deferred(&mut store, &batch_ax, None)?;
        assert!(ax_warm.ok && ax_warm.cache_hits == 1);
        batch_ax.allowed_axioms = Some(vec![]);
        assert!(
            match execute_check_shards_batch_payload_deferred(&mut store, &batch_ax, None) {
                Ok((resp, _, _)) => !resp.ok && resp.cache_hits == 0,
                Err(_) => true,
            }
        );

        let lp_a = dir.join("lp_a");
        let lp_b = dir.join("lp_b");
        std::fs::create_dir_all(&lp_a)?;
        std::fs::create_dir_all(&lp_b)?;
        batch_ax.allowed_axioms = Some(vec!["myAx".into()]);
        batch_ax.lean_path = lp_a.display().to_string();
        let (lp_miss, pub_lp, _) =
            execute_check_shards_batch_payload_deferred(&mut store, &batch_ax, None)?;
        assert!(lp_miss.ok && lp_miss.cache_hits == 0);
        publish_batch(&mut store, pub_lp);
        batch_ax.lean_path = lp_b.display().to_string();
        let (lp_miss_b, _, _) =
            execute_check_shards_batch_payload_deferred(&mut store, &batch_ax, None)?;
        assert!(lp_miss_b.ok && lp_miss_b.cache_hits == 0);

        // Mutating an imported `.olean` in place on the SAME lean_path must miss warm cache.
        let dep_lean = lp_a.join("DepMod.lean");
        let dep_olean = lp_a.join("DepMod.olean");
        let compile_dep = |body: &str| -> Result<()> {
            std::fs::write(&dep_lean, body)?;
            let status = std::process::Command::new("lean")
                .current_dir(&lp_a)
                .arg(&dep_lean)
                .arg("-o")
                .arg(&dep_olean)
                .status()?;
            assert!(status.success(), "lean failed to compile DepMod.lean");
            Ok(())
        };
        compile_dep("def depVal : Nat := 1\n")?;
        let dep_src = "import DepMod\ntheorem dep_thm : depVal = 1 := rfl\n";
        let single_dep = CheckShardHttpRequest {
            decl: "dep_thm".into(),
            shard_key: "same-dep-olean-key".into(),
            shard_source: dep_src.into(),
            lean_path: lp_a.display().to_string(),
            ..Default::default()
        };
        assert_eq!(
            execute_check_shard_payload(&mut store, &single_dep)?["status"],
            "remote_theorem_verified"
        );
        assert_eq!(
            execute_check_shard_payload(&mut store, &single_dep)?["status"],
            "remote_theorem_cache_hit"
        );
        let batch_dep = CheckShardsBatchRequest {
            items: vec![crate::pack::CheckShardBatchItem {
                shard_key: "same-batch-dep-olean-key".into(),
                decl_name: "dep_thm".into(),
                ..Default::default()
            }],
            coalesced_shard_source: dep_src.into(),
            lean_path: lp_a.display().to_string(),
            ..Default::default()
        };
        let (dep_first, pub_dep, _) =
            execute_check_shards_batch_payload_deferred(&mut store, &batch_dep, None)?;
        assert!(dep_first.ok && dep_first.cache_hits == 0);
        publish_batch(&mut store, pub_dep);
        let (dep_warm, _, _) =
            execute_check_shards_batch_payload_deferred(&mut store, &batch_dep, None)?;
        assert!(dep_warm.ok && dep_warm.cache_hits == 1);
        compile_dep("def depVal : Nat := 2\n")?;
        assert!(execute_check_shard_payload(&mut store, &single_dep).is_err());
        assert!(
            match execute_check_shards_batch_payload_deferred(&mut store, &batch_dep, None) {
                Ok((resp, _, _)) => !resp.ok && resp.cache_hits == 0,
                Err(_) => true,
            }
        );

        batch_ax.toolchain = "leanprover/lean4:v0.0.0-nonexistent".into();
        let (tc_miss, _, _) =
            execute_check_shards_batch_payload_deferred(&mut store, &batch_ax, None)?;
        assert_eq!(tc_miss.cache_hits, 0);
        single_ax.allowed_axioms = Some(vec!["myAx".into()]);
        single_ax.toolchain = "leanprover/lean4:v0.0.0-nonexistent".into();
        if let Ok(val) = execute_check_shard_payload(&mut store, &single_ax) {
            assert_eq!(val["status"], "remote_theorem_verified");
        }
        let _ = std::fs::remove_dir_all(dir);
        Ok(())
    }

    #[test]
    fn http_target_canonicalization_rejects_namespace_aliasing_and_ambiguity() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = std::env::temp_dir().join(format!(
            "turbo_http_target_canon_{}",
            crate::pack::next_tmp_id()
        ));
        let mut store = TurboStore::open(Some(&dir))?;

        let ns_only = "import Init\nnamespace Foo\ntheorem t : True := trivial\nend Foo\n";
        let sorry_root_with_ns =
            "import Init\ntheorem t : True := sorry\nnamespace Foo\ntheorem t : True := trivial\nend Foo\n";

        let batch_ns_bare = CheckShardsBatchRequest {
            items: vec![crate::pack::CheckShardBatchItem {
                shard_key: "ns-shared-key".into(),
                decl_name: "t".into(),
                ..Default::default()
            }],
            coalesced_shard_source: ns_only.into(),
            ..Default::default()
        };
        let (ns_res, ns_pub, _) =
            execute_check_shards_batch_payload_deferred(&mut store, &batch_ns_bare, None)?;
        assert!(ns_res.ok && ns_res.verified_count == 1 && ns_res.cache_hits == 0);
        publish_batch(&mut store, ns_pub);

        let batch_ns_qual = CheckShardsBatchRequest {
            items: vec![crate::pack::CheckShardBatchItem {
                shard_key: "ns-shared-key".into(),
                decl_name: "_root_.Foo.t".into(),
                ..Default::default()
            }],
            coalesced_shard_source: ns_only.into(),
            ..Default::default()
        };
        let (ns_warm, _, _) =
            execute_check_shards_batch_payload_deferred(&mut store, &batch_ns_qual, None)?;
        assert!(ns_warm.ok && ns_warm.cache_hits == 1);

        let batch_exact_root_on_ns = CheckShardsBatchRequest {
            items: vec![crate::pack::CheckShardBatchItem {
                shard_key: "ns-shared-key".into(),
                decl_name: "_root_.t".into(),
                ..Default::default()
            }],
            coalesced_shard_source: ns_only.into(),
            ..Default::default()
        };
        assert!(execute_check_shards_batch_payload_deferred(
            &mut store,
            &batch_exact_root_on_ns,
            None
        )
        .is_err());

        let batch_exact_root_sorry = CheckShardsBatchRequest {
            items: vec![crate::pack::CheckShardBatchItem {
                shard_key: "ns-shared-key".into(),
                decl_name: "_root_.t".into(),
                ..Default::default()
            }],
            coalesced_shard_source: sorry_root_with_ns.into(),
            ..Default::default()
        };
        assert!(execute_check_shards_batch_payload_deferred(
            &mut store,
            &batch_exact_root_sorry,
            None
        )
        .is_err());

        let single_exact_root_sorry = CheckShardHttpRequest {
            decl: "_root_.t".into(),
            shard_key: "ns-shared-key".into(),
            shard_source: sorry_root_with_ns.into(),
            ..Default::default()
        };
        assert!(execute_check_shard_payload(&mut store, &single_exact_root_sorry).is_err());

        let single_ns_bare = CheckShardHttpRequest {
            decl: "t".into(),
            shard_key: "ns-single-to-batch-key".into(),
            shard_source: ns_only.into(),
            ..Default::default()
        };
        assert_eq!(
            execute_check_shard_payload(&mut store, &single_ns_bare)?["status"],
            "remote_theorem_verified"
        );
        let batch_attack = CheckShardsBatchRequest {
            items: vec![crate::pack::CheckShardBatchItem {
                shard_key: "ns-single-to-batch-key".into(),
                decl_name: "_root_.t".into(),
                ..Default::default()
            }],
            coalesced_shard_source: sorry_root_with_ns.into(),
            ..Default::default()
        };
        assert!(
            execute_check_shards_batch_payload_deferred(&mut store, &batch_attack, None).is_err()
        );
        let batch_ns_hit = CheckShardsBatchRequest {
            items: vec![crate::pack::CheckShardBatchItem {
                shard_key: "ns-single-to-batch-key".into(),
                decl_name: "Foo.t".into(),
                ..Default::default()
            }],
            coalesced_shard_source: ns_only.into(),
            ..Default::default()
        };
        let (ns_cross_hit, _, _) =
            execute_check_shards_batch_payload_deferred(&mut store, &batch_ns_hit, None)?;
        assert!(ns_cross_hit.ok && ns_cross_hit.cache_hits == 1);

        let ambig_single = CheckShardHttpRequest {
            decl: "t".into(),
            shard_key: "ambig-key".into(),
            shard_source: sorry_root_with_ns.into(),
            ..Default::default()
        };
        assert!(execute_check_shard_payload(&mut store, &ambig_single).is_err());
        let ambig_batch = CheckShardsBatchRequest {
            items: vec![crate::pack::CheckShardBatchItem {
                shard_key: "ambig-key".into(),
                decl_name: "t".into(),
                ..Default::default()
            }],
            coalesced_shard_source: sorry_root_with_ns.into(),
            ..Default::default()
        };
        assert!(
            execute_check_shards_batch_payload_deferred(&mut store, &ambig_batch, None).is_err()
        );

        let ambig_ns_src = "import Init\nnamespace A\ntheorem t : True := trivial\nend A\nnamespace B\ntheorem t : True := sorry\nend B\n";
        let ambig_ns_single = CheckShardHttpRequest {
            decl: "t".into(),
            shard_key: "ambig-ns-key".into(),
            shard_source: ambig_ns_src.into(),
            ..Default::default()
        };
        assert!(execute_check_shard_payload(&mut store, &ambig_ns_single).is_err());

        let root_only = "import Init\ntheorem t : True := trivial\n";
        let single_root = CheckShardHttpRequest {
            decl: "t".into(),
            shard_key: "interop-root-key".into(),
            shard_source: root_only.into(),
            ..Default::default()
        };
        assert_eq!(
            execute_check_shard_payload(&mut store, &single_root)?["status"],
            "remote_theorem_verified"
        );
        let batch_root = CheckShardsBatchRequest {
            items: vec![crate::pack::CheckShardBatchItem {
                shard_key: "interop-root-key".into(),
                decl_name: "_root_.t".into(),
                ..Default::default()
            }],
            coalesced_shard_source: root_only.into(),
            ..Default::default()
        };
        let (root_hit, _, _) =
            execute_check_shards_batch_payload_deferred(&mut store, &batch_root, None)?;
        assert!(root_hit.ok && root_hit.cache_hits == 1);

        let batch_to_single_req = CheckShardsBatchRequest {
            items: vec![crate::pack::CheckShardBatchItem {
                shard_key: "interop-root-key-2".into(),
                decl_name: "t".into(),
                ..Default::default()
            }],
            coalesced_shard_source: root_only.into(),
            ..Default::default()
        };
        let (b2s_res, b2s_pub, _) =
            execute_check_shards_batch_payload_deferred(&mut store, &batch_to_single_req, None)?;
        assert!(b2s_res.ok && b2s_res.verified_count == 1);
        publish_batch(&mut store, b2s_pub);
        let single_root_hit = CheckShardHttpRequest {
            decl: "_root_.t".into(),
            shard_key: "interop-root-key-2".into(),
            shard_source: root_only.into(),
            ..Default::default()
        };
        assert_eq!(
            execute_check_shard_payload(&mut store, &single_root_hit)?["status"],
            "remote_theorem_cache_hit"
        );

        let _ = std::fs::remove_dir_all(dir);
        Ok(())
    }

    #[test]
    fn http_check_shard_rejects_contradictory_decl_and_targets_and_targetless_payloads(
    ) -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = std::env::temp_dir().join(format!(
            "turbo_http_decl_targets_{}",
            crate::pack::next_tmp_id()
        ));
        let mut store = TurboStore::open(Some(&dir))?;
        let mixed_src =
            "import Init\ntheorem bad : False := sorry\ntheorem good : True := trivial\n";

        let contradictory = CheckShardHttpRequest {
            decl: "bad".into(),
            targets: vec!["good".into()],
            shard_key: "target-discrepancy".into(),
            shard_source: mixed_src.into(),
            ..Default::default()
        };
        assert!(execute_check_shard_payload(&mut store, &contradictory).is_err());

        let mut contradictory_daemon = contradictory.clone();
        contradictory_daemon.skip_cas_lock = true;
        assert!(execute_check_shard_payload(&mut store, &contradictory_daemon).is_err());

        let multi_vs_single = CheckShardHttpRequest {
            decl: "good".into(),
            targets: vec!["good".into(), "bad".into()],
            shard_key: "multi-discrepancy".into(),
            shard_source: mixed_src.into(),
            ..Default::default()
        };
        assert!(execute_check_shard_payload(&mut store, &multi_vs_single).is_err());

        let targetless_daemon = CheckShardHttpRequest {
            decl: "__batch__".into(),
            shard_key: "targetless-daemon".into(),
            shard_source: "import Init\n#check Nat\n".into(),
            skip_cas_lock: true,
            ..Default::default()
        };
        assert!(execute_check_shard_payload(&mut store, &targetless_daemon).is_err());

        let ns_src = "import Init\nnamespace Ns\ntheorem good : True := trivial\nend Ns\n";
        let agree_req = CheckShardHttpRequest {
            decl: "good".into(),
            targets: vec!["_root_.Ns.good".into()],
            shard_key: "canonical-agree".into(),
            shard_source: ns_src.into(),
            ..Default::default()
        };
        let verified = execute_check_shard_payload(&mut store, &agree_req)?;
        assert_eq!(verified["status"], "remote_theorem_verified");
        assert_eq!(verified["decl"], "Ns.good");
        assert_eq!(
            verified["verified_targets"],
            serde_json::json!(["_root_.Ns.good"])
        );

        let hit = execute_check_shard_payload(&mut store, &agree_req)?;
        assert_eq!(hit["status"], "remote_theorem_cache_hit");
        assert_eq!(hit["decl"], "Ns.good");
        assert_eq!(
            hit["verified_targets"],
            serde_json::json!(["_root_.Ns.good"])
        );

        let _ = std::fs::remove_dir_all(dir);
        Ok(())
    }

    #[test]
    fn http_receipts_bind_server_computed_statement_proof_and_prefix_content() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = std::env::temp_dir().join(format!(
            "turbo_http_content_bind_{}",
            crate::pack::next_tmp_id()
        ));
        let mut store = TurboStore::open(Some(&dir))?;

        let mut single = CheckShardHttpRequest {
            decl: "t".into(),
            shard_key: "reused-caller-key".into(),
            shard_source: "import Init\ntheorem t : True := trivial\n".into(),
            prefix_env_hash: "forged-prefix".into(),
            stmt_hash: "forged-stmt".into(),
            proof_hash: "forged-proof".into(),
            ..Default::default()
        };
        assert_eq!(
            execute_check_shard_payload(&mut store, &single)?["status"],
            "remote_theorem_verified"
        );
        assert_eq!(
            execute_check_shard_payload(&mut store, &single)?["status"],
            "remote_theorem_cache_hit"
        );

        // Mutating statement to `False := by trivial` under the same `shard_key` must miss cache and fail.
        single.shard_source = "import Init\ntheorem t : False := by trivial\n".into();
        assert!(execute_check_shard_payload(&mut store, &single).is_err());

        // Mutating proof under the same `shard_key` must miss cache and re-elaborate.
        single.shard_source = "import Init\ntheorem t : True := by exact True.intro\n".into();
        assert_eq!(
            execute_check_shard_payload(&mut store, &single)?["status"],
            "remote_theorem_verified"
        );

        // Mutating prefix definition `def k` under the same `shard_key` must miss cache and fail.
        let mut pfx_req = CheckShardHttpRequest {
            decl: "t_pfx".into(),
            shard_key: "reused-prefix-key".into(),
            shard_source: "import Init\ndef k : Nat := 1\ntheorem t_pfx : k = 1 := rfl\n".into(),
            ..Default::default()
        };
        assert_eq!(
            execute_check_shard_payload(&mut store, &pfx_req)?["status"],
            "remote_theorem_verified"
        );
        pfx_req.shard_source =
            "import Init\ndef k : Nat := 2\ntheorem t_pfx : k = 1 := rfl\n".into();
        assert!(execute_check_shard_payload(&mut store, &pfx_req).is_err());

        // Batch all-hit and partial-hit pruning must reject mutated statement/proof/sorry under reused keys.
        let batch_src_ok =
            "import Init\ntheorem b1 : True := trivial\ntheorem b2 : 1 + 1 = 2 := rfl\n";
        let batch = CheckShardsBatchRequest {
            items: vec![
                crate::pack::CheckShardBatchItem {
                    shard_key: "batch-k1".into(),
                    decl_name: "b1".into(),
                    stmt_hash: "caller-fake-1".into(),
                    ..Default::default()
                },
                crate::pack::CheckShardBatchItem {
                    shard_key: "batch-k2".into(),
                    decl_name: "b2".into(),
                    stmt_hash: "caller-fake-2".into(),
                    ..Default::default()
                },
            ],
            coalesced_shard_source: batch_src_ok.into(),
            ..Default::default()
        };
        let (first, pub1, _) =
            execute_check_shards_batch_payload_deferred(&mut store, &batch, None)?;
        assert!(first.ok && first.verified_count == 2 && first.cache_hits == 0);
        publish_batch(&mut store, pub1);
        let (warm, _, _) = execute_check_shards_batch_payload_deferred(&mut store, &batch, None)?;
        assert!(warm.ok && warm.cache_hits == 2);

        // All-hit sorry bypass attempt: mutating `b1` to `False := sorry` must NOT hit cache or bypass sorry gate.
        let mut batch_sorry = batch.clone();
        batch_sorry.coalesced_shard_source =
            "import Init\ntheorem b1 : False := sorry\ntheorem b2 : 1 + 1 = 2 := rfl\n".into();
        assert!(
            execute_check_shards_batch_payload_deferred(&mut store, &batch_sorry, None).is_err()
        );

        // Partial-hit pruning soundness: mutating `b1` to `False := sorry` while adding `b3 : False := b1`
        // must NOT treat `b1` as cached or stub it out to prove `b3 : False`.
        let partial_attack = CheckShardsBatchRequest {
            items: vec![
                crate::pack::CheckShardBatchItem {
                    shard_key: "batch-k1".into(),
                    decl_name: "b1".into(),
                    ..Default::default()
                },
                crate::pack::CheckShardBatchItem {
                    shard_key: "batch-k3".into(),
                    decl_name: "b3".into(),
                    ..Default::default()
                },
            ],
            coalesced_shard_source:
                "import Init\ntheorem b1 : False := sorry\ntheorem b3 : False := b1\n".into(),
            ..Default::default()
        };
        assert!(
            execute_check_shards_batch_payload_deferred(&mut store, &partial_attack, None).is_err()
        );

        let partial_false_proof = CheckShardsBatchRequest {
            items: vec![
                crate::pack::CheckShardBatchItem {
                    shard_key: "batch-k1".into(),
                    decl_name: "b1".into(),
                    ..Default::default()
                },
                crate::pack::CheckShardBatchItem {
                    shard_key: "batch-k3".into(),
                    decl_name: "b3".into(),
                    ..Default::default()
                },
            ],
            coalesced_shard_source:
                "import Init\ntheorem b1 : False := by trivial\ntheorem b3 : False := b1\n".into(),
            ..Default::default()
        };
        match execute_check_shards_batch_payload_deferred(&mut store, &partial_false_proof, None) {
            Ok((resp, _, _)) => assert!(!resp.ok && resp.cache_hits == 0),
            Err(_) => {}
        }

        // Unmapped `_turbo_verify_0_a_b` via HTTP must be rejected on both single and batch endpoints.
        let unmapped_http = CheckShardHttpRequest {
            decl: "_root_.a.b".into(),
            shard_key: "unmapped-http-key".into(),
            shard_source: "import Init\ntheorem _turbo_verify_0_a_b : True := trivial\n".into(),
            ..Default::default()
        };
        assert!(execute_check_shard_payload(&mut store, &unmapped_http).is_err());

        let unmapped_batch = CheckShardsBatchRequest {
            items: vec![crate::pack::CheckShardBatchItem {
                shard_key: "unmapped-batch-key".into(),
                decl_name: "_root_.a.b".into(),
                ..Default::default()
            }],
            coalesced_shard_source: "import Init\ntheorem _turbo_verify_0_a_b : True := trivial\n"
                .into(),
            ..Default::default()
        };
        assert!(
            execute_check_shards_batch_payload_deferred(&mut store, &unmapped_batch, None).is_err()
        );

        // Literal whitespace, char literal, and layout edits must miss warm cache across
        // single /check-shard, all-hit /check-shard-batch, and partial-hit /check-shard-batch.
        let mut lit_single = CheckShardHttpRequest {
            decl: "t_lit".into(),
            shard_key: "reused-lit-single-key".into(),
            shard_source: "import Init\ntheorem t_lit : \"a b\" = \"a b\" := rfl\n".into(),
            ..Default::default()
        };
        assert_eq!(
            execute_check_shard_payload(&mut store, &lit_single)?["status"],
            "remote_theorem_verified"
        );
        assert_eq!(
            execute_check_shard_payload(&mut store, &lit_single)?["status"],
            "remote_theorem_cache_hit"
        );
        lit_single.shard_source = "import Init\ntheorem t_lit : \"a  b\" = \"a b\" := rfl\n".into();
        assert!(execute_check_shard_payload(&mut store, &lit_single).is_err());

        let mut char_single = CheckShardHttpRequest {
            decl: "t_char".into(),
            shard_key: "reused-char-single-key".into(),
            shard_source: "import Init\ntheorem t_char : ' ' = ' ' := rfl\n".into(),
            ..Default::default()
        };
        assert_eq!(
            execute_check_shard_payload(&mut store, &char_single)?["status"],
            "remote_theorem_verified"
        );
        char_single.shard_source = "import Init\ntheorem t_char : '\t' = ' ' := rfl\n".into();
        assert!(execute_check_shard_payload(&mut store, &char_single).is_err());

        let mut layout_single = CheckShardHttpRequest {
            decl: "t_layout".into(),
            shard_key: "reused-layout-single-key".into(),
            shard_source: "import Init\ntheorem t_layout : True := by\n  skip\n  trivial\n".into(),
            ..Default::default()
        };
        assert_eq!(
            execute_check_shard_payload(&mut store, &layout_single)?["status"],
            "remote_theorem_verified"
        );
        layout_single.shard_source =
            "import Init\ntheorem t_layout : True := by skip trivial\n".into();
        assert!(execute_check_shard_payload(&mut store, &layout_single).is_err());

        let lit_batch_ok = CheckShardsBatchRequest {
            items: vec![
                crate::pack::CheckShardBatchItem {
                    shard_key: "lit-bk1".into(),
                    decl_name: "lb1".into(),
                    ..Default::default()
                },
                crate::pack::CheckShardBatchItem {
                    shard_key: "lit-bk2".into(),
                    decl_name: "lb2".into(),
                    ..Default::default()
                },
            ],
            coalesced_shard_source:
                "import Init\ntheorem lb1 : ' ' = ' ' := rfl\ntheorem lb2 : \"a b\" = \"a b\" := rfl\n"
                    .into(),
            ..Default::default()
        };
        let (lb_first, lb_pub, _) =
            execute_check_shards_batch_payload_deferred(&mut store, &lit_batch_ok, None)?;
        assert!(lb_first.ok && lb_first.verified_count == 2 && lb_first.cache_hits == 0);
        publish_batch(&mut store, lb_pub);
        let (lb_warm, _, _) =
            execute_check_shards_batch_payload_deferred(&mut store, &lit_batch_ok, None)?;
        assert!(lb_warm.ok && lb_warm.cache_hits == 2);

        // All-hit batch: mutating string literal whitespace in `lb2` must miss cache and fail (`lb1` hits, `lb2` misses).
        let mut lit_batch_all_attack = lit_batch_ok.clone();
        lit_batch_all_attack.coalesced_shard_source =
            "import Init\ntheorem lb1 : ' ' = ' ' := rfl\ntheorem lb2 : \"a  b\" = \"a b\" := rfl\n"
                .into();
        match execute_check_shards_batch_payload_deferred(&mut store, &lit_batch_all_attack, None) {
            Ok((resp, _, _)) => assert!(!resp.ok && resp.cache_hits == 1),
            Err(_) => {}
        }

        // Partial-hit batch: mutating `lb1` char literal while adding `lb3` depending on `lb1`
        // must NOT treat `lb1` as a warm hit or stub it out with `sorry` to verify `lb3`.
        let lit_batch_partial_attack = CheckShardsBatchRequest {
            items: vec![
                crate::pack::CheckShardBatchItem {
                    shard_key: "lit-bk1".into(),
                    decl_name: "lb1".into(),
                    ..Default::default()
                },
                crate::pack::CheckShardBatchItem {
                    shard_key: "lit-bk3".into(),
                    decl_name: "lb3".into(),
                    ..Default::default()
                },
            ],
            coalesced_shard_source:
                "import Init\ntheorem lb1 : '\t' = ' ' := rfl\ntheorem lb3 : '\t' = ' ' := lb1\n"
                    .into(),
            ..Default::default()
        };
        match execute_check_shards_batch_payload_deferred(
            &mut store,
            &lit_batch_partial_attack,
            None,
        ) {
            Ok((resp, _, _)) => assert!(!resp.ok && resp.cache_hits == 0),
            Err(_) => {}
        }

        let _ = std::fs::remove_dir_all(dir);
        Ok(())
    }

    #[test]
    fn loopback_listen_addr_detection_is_exact() {
        assert!(is_loopback_listen_addr("127.0.0.1:9400"));
        assert!(is_loopback_listen_addr("127.1.2.3:9400"));
        assert!(is_loopback_listen_addr("[::1]:9400"));
        assert!(is_loopback_listen_addr("localhost:9400"));
        assert!(!is_loopback_listen_addr("0.0.0.0:9400"));
        assert!(!is_loopback_listen_addr("[::]:9400"));
        assert!(!is_loopback_listen_addr("127.0.0.1.evil.example:9400"));
        assert!(!is_loopback_listen_addr("localhost.evil.example:9400"));
        assert!(!is_loopback_listen_addr("10.0.0.5:9400"));
    }

    #[test]
    fn constant_time_eq_matches_only_identical_tokens() {
        assert!(constant_time_eq(b"secret", b"secret"));
        assert!(!constant_time_eq(b"secret", b"secreT"));
        assert!(!constant_time_eq(b"secret", b"secret2"));
        assert!(!constant_time_eq(b"", b"x"));
    }
}
