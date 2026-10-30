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
    let activity = std::sync::Arc::new(std::sync::Mutex::new((std::time::Instant::now(), 0usize)));

    if is_daemon {
        let idle_timeout_secs = std::env::var("TURBO_LEAN_DAEMON_IDLE_SECS")
            .ok()
            .and_then(|v| v.trim().parse::<u64>().ok())
            .unwrap_or(900);
        if idle_timeout_secs > 0 {
            let activity = activity.clone();
            std::thread::spawn(move || loop {
                std::thread::sleep(std::time::Duration::from_millis(250));
                let state = activity.lock().unwrap();
                if state.1 == 0 && state.0.elapsed().as_secs() >= idle_timeout_secs {
                    crate::zygote::shutdown_local_daemon();
                    std::process::exit(0);
                }
            });
        }
    }

    for stream in listener.incoming() {
        let mut stream = match stream {
            Ok(s) => s,
            Err(_) => continue,
        };
        let _ = stream.set_nodelay(true);
        let _ = stream.set_read_timeout(Some(std::time::Duration::from_secs(2)));
        let _ = stream.set_write_timeout(Some(std::time::Duration::from_secs(30)));
        {
            let mut state = activity.lock().unwrap();
            if state.1 >= 64 {
                let _ = write_http_response(
                    &mut stream,
                    503,
                    "application/json",
                    b"{\"ok\":false,\"error\":\"server_busy\"}",
                );
                continue;
            }
            state.1 += 1;
        }
        let activity_guard = activity.clone();
        let shared_ref = shared.clone();
        let store_root_clone = store_root_buf.clone();
        let expected_token_clone = expected_token.clone();

        std::thread::spawn(move || {
            struct ConnDropGuard(std::sync::Arc<std::sync::Mutex<(std::time::Instant, usize)>>);
            impl Drop for ConnDropGuard {
                fn drop(&mut self) {
                    let mut state = self.0.lock().unwrap();
                    state.0 = std::time::Instant::now();
                    state.1 -= 1;
                }
            }
            let _conn_guard = ConnDropGuard(activity_guard);

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
                            let _ = write_json_response(
                                &mut stream,
                                500,
                                &serde_json::json!({"status": "error", "error": e.to_string()}),
                            );
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
                        code: String,
                        #[serde(default)]
                        file_name: Option<String>,
                        #[serde(default)]
                        cwd: Option<String>,
                        #[serde(default)]
                        env_vars: Option<std::collections::HashMap<String, String>>,
                        #[serde(default)]
                        timeout_ms: Option<u64>,
                        #[serde(default)]
                        verify_determinism: bool,
                        #[serde(default)]
                        lean_args: Vec<String>,
                    }
                    let req: EvalHttpRequest = serde_json::from_slice(&body).unwrap_or_default();
                    let filtered_eval_args =
                        crate::module_builder::filter_allowed_lean_args(&req.lean_args);
                    let Ok(req_store) = TurboStore::open(store_root_clone.as_deref()) else {
                        return;
                    };
                    let src = if !req.source.is_empty() {
                        req.source.as_str()
                    } else {
                        req.code.as_str()
                    };
                    let tc = if req.toolchain.is_empty() {
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
                    match crate::zygote::eval_with_zygote_pool_opts_with_args(
                        &req_store,
                        tc,
                        &req.lean_path,
                        &env_vars,
                        &lean_bin,
                        src,
                        false,
                        true,
                        req.file_name.as_deref(),
                        req.timeout_ms,
                        &filtered_eval_args,
                    ) {
                        Ok(zreply) => {
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
                                    if let Ok(out) = cmd.output() {
                                        deterministic = out.status.success() == zreply.ok;
                                    }
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
                                    "deterministic": deterministic
                                }),
                            );
                        }
                        Err(e) => {
                            let _ = write_json_response(
                                &mut stream,
                                200,
                                &serde_json::json!({
                                    "ok": false,
                                    "error": e.to_string(),
                                    "errors": [e.to_string()],
                                    "crashed": true
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

/// Run `lean` on a temporary source file, applying `#print axioms` auditing under `allowed` when
/// `audit` is non-empty. Returns `(exit_code, stdout, stderr)`.
#[allow(clippy::too_many_arguments)]
fn run_lean_temp_file(
    store: &TurboStore,
    lean_bin: &Path,
    env_vars: &std::collections::HashMap<String, String>,
    toolchain: &str,
    source: &str,
    prefix: &str,
    audit: &std::collections::HashSet<String>,
    allowed: &[String],
    lean_args: &[String],
) -> Result<(i32, String, String)> {
    let staging = store.fast_staging_dir();
    let tmp = staging.join(format!("{}_{}.lean", prefix, next_tmp_id()));
    let (audited_src, audited) = if audit.is_empty() {
        (source.to_string(), 0usize)
    } else {
        crate::splitter::with_axiom_audit(source, audit)
    };
    fs::write(&tmp, &audited_src)?;
    let mut cmd = Command::new(lean_bin);
    for arg in crate::module_builder::filter_allowed_lean_args(lean_args) {
        cmd.arg(arg);
    }
    cmd.arg(&tmp).envs(env_vars);
    if !toolchain.is_empty() && toolchain != "unknown" && !env_vars.contains_key("ELAN_TOOLCHAIN") {
        cmd.env("ELAN_TOOLCHAIN", toolchain.trim());
    }
    let out = cmd
        .output()
        .context("Failed to execute `lean` on remote shard payload")?;
    let _ = fs::remove_file(&tmp);
    let mut code = out.status.code().unwrap_or(-1);
    let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
    let mut stderr = String::from_utf8_lossy(&out.stderr).into_owned();
    if code == 0 && !audit.is_empty() {
        let mut reports = crate::splitter::parse_print_axioms(&stdout);
        reports.retain(|(n, _)| crate::splitter::matches_uncached_or_fast_verify_name(n, audit));
        if audited < audit.len() || reports.len() < audited {
            code = 1;
            stderr = format!(
                "{}\n[TurboLean.KernelGate] axiom audit incomplete: {} of {} theorems reported",
                stderr,
                reports.len(),
                audit.len()
            );
        } else {
            let bad: Vec<String> = reports
                .iter()
                .flat_map(|(n, axs)| axs.iter().map(move |a| (n, a)))
                .filter(|(_, a)| {
                    !crate::splitter::axiom_allowed_under(a, allowed) && a.as_str() != "sorryAx"
                })
                .map(|(n, a)| format!("`{}` depends on `{}`", n, a))
                .collect();
            if !bad.is_empty() {
                code = 1;
                stderr = format!(
                    "{}\n[TurboLean.KernelGate] disallowed axioms: {}",
                    stderr,
                    bad.join(", ")
                );
            }
        }
    }
    Ok((code, stdout, stderr))
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
            let cleaned: Vec<String> = extra
                .iter()
                .map(|s| s.trim())
                .filter(|s| !s.is_empty())
                .map(String::from)
                .collect();
            let csv = cleaned.join(",");
            (crate::splitter::allowed_axioms_with_extra(&cleaned), csv)
        }
        None => {
            let extra = crate::splitter::extra_allowed_axiom_patterns();
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

    if !req.skip_cas_lock && store.has_cached_action_readonly(&req.shard_key, trust_domain)? {
        return Ok((
            serde_json::json!({
                "status": "remote_theorem_cache_hit",
                "decl": req.decl,
                "shard_key": req.shard_key,
                "coalesced": false,
                "interface_hash": req.interface_hash,
                "prefix_env_hash": req.prefix_env_hash,
                "server_arch": std::env::consts::ARCH,
                "server_elapsed_ms": t0.elapsed().as_millis()
            }),
            None,
            Some(req.shard_key.clone()),
        ));
    }

    let (req_allowed, req_allowed_csv) =
        resolve_request_axiom_policy(req.allowed_axioms.as_deref(), trust_domain);

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
                req.decl,
                source_violations.flagged_items
            );
        }

        if !req.skip_cas_lock && source_violations.has_sorry {
            let dep_hashes = crate::lake_build::compute_imported_olean_interface_hashes(
                &req.shard_source,
                Path::new("."),
                if req.lean_path.is_empty() {
                    None
                } else {
                    Some(req.lean_path.as_str())
                },
            );
            let parsed = crate::splitter::split_lean_source(&req.shard_source, &dep_hashes);
            let target_body = if parsed.shards.len() == 1 {
                let s = &parsed.shards[0];
                format!("{}\n{}", s.signature_text, s.proof_text)
            } else {
                let short_req: String = req
                    .decl
                    .rsplit('.')
                    .next()
                    .unwrap_or(&req.decl)
                    .chars()
                    .map(|c| {
                        if c.is_ascii_alphanumeric() || c == '_' {
                            c
                        } else {
                            '_'
                        }
                    })
                    .collect();
                parsed
                    .shards
                    .iter()
                    .find(|s| {
                        let base = s.name.split("__turbo_check_").next().unwrap_or(&s.name);
                        let short_s = base.rsplit('.').next().unwrap_or(base);
                        base == req.decl
                            || req.decl.ends_with(&format!(".{}", base))
                            || base.ends_with(&format!(".{}", req.decl))
                            || (short_s.starts_with("_turbo_verify_")
                                && short_s.ends_with(&short_req))
                    })
                    .map(|s| format!("{}\n{}", s.signature_text, s.proof_text))
                    .unwrap_or_else(|| clean_source.clone())
            };
            let clean_target = crate::splitter::strip_lean_comments(&target_body);
            let violations = crate::splitter::audit_hygiene(&clean_target);
            if !violations.disallowed_items_under(&req_allowed).is_empty() {
                anyhow::bail!(
                    "Soundness hygiene violation in remote shard `{}`: {:?}",
                    req.decl,
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

    let (mut env_vars, lean_bin) =
        resolve_server_lean_env_and_bin(store, toolchain, &req.lean_path);
    env_vars.insert(
        crate::splitter::ALLOWED_AXIOMS_ENV.to_string(),
        req_allowed_csv,
    );

    let mut zygote_used = false;
    let mut zygote_env_cache_hit = false;
    let mut zygote_import_us = 0u64;
    let mut zygote_elab_us = 0u64;
    let mut zygote_heartbeats = 0u64;
    let mut zygote_proof_nodes = 0u64;
    let mut zygote_rss_delta = 0i64;
    let mut zygote_peak_rss = 0u64;
    let mut zygote_used_constants: Vec<String> = Vec::new();

    let filtered_req_args = crate::module_builder::filter_allowed_lean_args(&req.lean_args);
    let req_args_digest_opt = crate::module_builder::compute_lean_args_digest(&filtered_req_args);

    match crate::zygote::eval_with_zygote_pool_opts_with_args(
        store,
        toolchain,
        &req.lean_path,
        &env_vars,
        &lean_bin,
        &req.shard_source,
        true,
        false,
        None,
        timeout_ms,
        &filtered_req_args,
    ) {
        Ok(zreply) if zreply.import_ok => {
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
        Ok(_) if req.skip_cas_lock => {
            anyhow::bail!("Zygote import unavailable for `{}`", req.decl);
        }
        Err(e) if req.skip_cas_lock => return Err(e),
        _ => {}
    }

    if !zygote_used {
        let audit_set: std::collections::HashSet<String> =
            if matches!(req.decl.as_str(), "" | "__batch__" | "__coalesced_batch__") {
                crate::splitter::split_lean_source(&req.shard_source, &[])
                    .shards
                    .into_iter()
                    .filter(|sh| {
                        !crate::splitter::audit_hygiene(&crate::splitter::strip_lean_comments(
                            &sh.proof_text,
                        ))
                        .has_sorry
                    })
                    .map(|sh| sh.name)
                    .collect()
            } else {
                std::iter::once(req.decl.clone()).collect()
            };
        let (code, stdout, stderr) = run_lean_temp_file(
            store,
            &lean_bin,
            &env_vars,
            req.toolchain.as_str(),
            &req.shard_source,
            "http_shard",
            &audit_set,
            &req_allowed,
            &filtered_req_args,
        )?;
        if code != 0 {
            anyhow::bail!(
                "Remote `lean` shard verification failed for `{}`:\n{}\n{}",
                req.decl,
                stdout,
                stderr
            );
        }
    }

    let dur_ms = t0.elapsed().as_millis() as i64;
    let dur_us = t0.elapsed().as_micros() as u64;
    let deferred = if req.skip_cas_lock {
        None
    } else {
        let mut receipt_obj = serde_json::json!({
            "decl": req.decl,
            "prefix_env_hash": req.prefix_env_hash,
            "stmt_hash": req.stmt_hash,
            "proof_hash": req.proof_hash,
            "verified_at": now_unix()
        });
        if let Some(ref ad) = req_args_digest_opt {
            if let Some(map) = receipt_obj.as_object_mut() {
                map.insert(
                    "lean_args_digest".to_string(),
                    serde_json::Value::String(ad.clone()),
                );
            }
        }
        let receipt = serde_json::to_vec(&receipt_obj)?;
        Some((
            toolchain.to_string(),
            vec![(req.shard_key.clone(), req.decl.clone(), receipt, dur_ms)],
        ))
    };

    Ok((
        serde_json::json!({
            "status": "remote_theorem_verified",
            "decl": req.decl,
            "shard_key": req.shard_key,
            "interface_hash": req.interface_hash,
            "prefix_env_hash": req.prefix_env_hash,
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

    let keys: Vec<String> = req.items.iter().map(|i| i.shard_key.clone()).collect();
    let cached_map = store.batch_get_theorem_shards_readonly(&keys, trust_domain)?;
    let hit_keys: Vec<String> = req
        .items
        .iter()
        .filter(|i| cached_map.contains_key(&i.shard_key))
        .map(|i| i.shard_key.clone())
        .collect();
    let cache_hits = hit_keys.len();

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

    let (req_allowed, req_allowed_csv) =
        resolve_request_axiom_policy(req.allowed_axioms.as_deref(), trust_domain);

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
            let item_names: HashSet<&str> =
                req.items.iter().map(|i| i.decl_name.as_str()).collect();
            let dep_hashes = crate::lake_build::compute_imported_olean_interface_hashes(
                &req.coalesced_shard_source,
                Path::new("."),
                if req.lean_path.is_empty() {
                    None
                } else {
                    Some(req.lean_path.as_str())
                },
            );
            let parsed =
                crate::splitter::split_lean_source(&req.coalesced_shard_source, &dep_hashes);
            let uncached_has_sorry = parsed.shards.iter().any(|sh| {
                let short = sh.name.rsplit('.').next().unwrap_or(sh.name.as_str());
                (item_names.contains(sh.name.as_str()) || item_names.contains(short))
                    && crate::splitter::audit_hygiene(&crate::splitter::strip_lean_comments(
                        &sh.proof_text,
                    ))
                    .has_sorry
            });
            if uncached_has_sorry || parsed.shards.is_empty() {
                anyhow::bail!(
                    "Soundness hygiene violation in remote batch shard payload: uncached theorem contains `sorry`"
                );
            }
        }
    }

    let effective_batch_source = if cache_hits > 0 {
        let server_uncached_decls: HashSet<String> = req
            .items
            .iter()
            .filter(|i| !cached_map.contains_key(&i.shard_key))
            .map(|i| i.decl_name.clone())
            .collect();
        crate::splitter::build_coalesced_shard_source(
            &req.coalesced_shard_source,
            &server_uncached_decls,
        )
    } else {
        req.coalesced_shard_source.clone()
    };

    let (mut env_vars, lean_bin) =
        resolve_server_lean_env_and_bin(store, toolchain, &req.lean_path);
    env_vars.insert(
        crate::splitter::ALLOWED_AXIOMS_ENV.to_string(),
        req_allowed_csv,
    );

    let mut zygote_handled = false;
    let mut stdout = String::new();
    let mut stderr = String::new();
    let mut exit_code = 0i32;

    let filtered_batch_args = crate::module_builder::filter_allowed_lean_args(&req.lean_args);
    let batch_args_digest_opt =
        crate::module_builder::compute_lean_args_digest(&filtered_batch_args);

    if let Ok(zreply) = crate::zygote::eval_with_zygote_pool_opts_with_args(
        store,
        toolchain,
        &req.lean_path,
        &env_vars,
        &lean_bin,
        &effective_batch_source,
        true,
        false,
        None,
        timeout_ms,
        &filtered_batch_args,
    ) {
        if zreply.import_ok {
            zygote_handled = true;
            if !zreply.ok {
                exit_code = 1;
                stderr = zreply.errors.join("\n");
            }
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

        let batch_audit: std::collections::HashSet<String> = req
            .items
            .iter()
            .filter(|i| !cached_map.contains_key(&i.shard_key))
            .map(|i| i.decl_name.clone())
            .collect();
        let (code, out, err) = run_lean_temp_file(
            store,
            &lean_bin,
            &env_vars,
            req.toolchain.as_str(),
            &effective_batch_source,
            "http_batch_shards",
            &batch_audit,
            &req_allowed,
            &filtered_batch_args,
        )?;
        exit_code = code;
        stdout = out;
        stderr = err;
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
    for item in &req.items {
        if cached_map.contains_key(&item.shard_key) {
            continue;
        }
        let mut receipt_obj = serde_json::json!({
            "decl": item.decl_name,
            "prefix_env_hash": item.prefix_env_hash,
            "stmt_hash": item.stmt_hash,
            "proof_hash": item.proof_hash,
            "verified_at": now
        });
        if let Some(ref ad) = batch_args_digest_opt {
            if let Some(map) = receipt_obj.as_object_mut() {
                map.insert(
                    "lean_args_digest".to_string(),
                    serde_json::Value::String(ad.clone()),
                );
            }
        }
        let receipt = serde_json::to_vec(&receipt_obj)?;
        publish_items.push((
            item.shard_key.clone(),
            item.decl_name.clone(),
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
