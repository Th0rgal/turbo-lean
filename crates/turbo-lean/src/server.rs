//! HTTP Remote Coordinator (`turbo-lean serve`) for CAS Delta Sync, Zygote Shard Verification,
//! and Perceus / CUDA Fast-Check Offload.

use crate::db::{now_unix, TurboStore};
use crate::pack::{
    compute_fastcheck_binary_key, compute_fastcheck_binary_key_parts, compile_fastcheck_c_to_bin,
    export_pack_filtered_bytes, export_pack_filtered_with_mode, get_store_manifest,
    import_pack_bytes, next_tmp_id, run_or_read_cached_fastcheck_bin,
    save_compiled_bin_to_shared, shared_cas_blobs_dir, shared_fastcheck_cgen_path,
    try_import_from_shared_cas, try_parse_v3_header, try_populate_cached_bin_from_shared,
    CheckShardHttpRequest, CheckShardsBatchRequest, CheckShardsBatchResponse, DeltaManifest,
    ExportDeltaRequest, FastCheckHttpRequest, FASTCHECK_NO_MAIN_SUFFIX, FASTCHECK_PRELUDE_HARNESS,
};
use crate::zygote::{eval_with_zygote_pool, LocalZygoteDaemonInfo};
use anyhow::{Context, Result};
use std::collections::HashSet;
use std::fs;
use std::io::{BufRead, BufReader, Read, Write};
use std::net::TcpListener;
use std::path::Path;
use std::process::Command;

/// Lightweight HTTP Server (`turbo-lean serve`) for remote CAS sync & GPU/CPU offload (e.g., on DGX Spark).
pub fn serve_cas_http(
    store_root: Option<&Path>,
    listen_addr: &str,
    gpu_enable: bool,
) -> Result<()> {
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
            };
            if let Ok(json_bytes) = serde_json::to_vec(&info) {
                let _ = fs::write(&state_path, &json_bytes);
            }
        }
    }
    let mut store = TurboStore::open(store_root)?;
    let mut local_mutation_seq: u64 = 0;
    let query_data_version = |st: &TurboStore| -> i64 {
        st.conn
            .query_row("PRAGMA data_version", [], |r| r.get::<_, i64>(0))
            .unwrap_or(0)
    };
    let init_dv = query_data_version(&store);
    let mut cached_manifest: Option<((i64, u64), DeltaManifest, Vec<u8>)> =
        get_store_manifest(&store, true)
            .ok()
            .and_then(|m| serde_json::to_vec(&m).ok().map(|b| (m, b)))
            .map(|(m, b)| ((init_dv, local_mutation_seq), m, b));
    let mut cached_export_local: Option<((i64, u64), Vec<u8>)> =
        export_pack_filtered_with_mode(&store, true, &HashSet::new(), &HashSet::new(), true)
            .ok()
            .map(|(_, _, _, b)| ((init_dv, local_mutation_seq), b));
    let mut cached_export: Option<((i64, u64), Vec<u8>)> = None;

    #[cfg(not(test))]
    {
        let store_root_owned = store_root.map(|p| p.to_path_buf());
        let prewarm = std::thread::spawn(move || {
            if let Ok(bg_store) = TurboStore::open(store_root_owned.as_deref()) {
                let lp = Path::new(env!("CARGO_MANIFEST_DIR"))
                    .parent()
                    .and_then(|p| p.parent())
                    .map(|r| r.join("lean/.lake/build/lib/lean"))
                    .filter(|p| p.join("TurboLean/Reflection.olean").exists())
                    .map(|p| p.to_string_lossy().to_string())
                    .unwrap_or_default();
                let (env_vars, lean_bin) =
                    resolve_server_lean_env_and_bin(&bg_store, "leanprover/lean4:v4.31.0", &lp);
                let _ = crate::pack::prewarm_shared_fastcheck_harness(&bg_store, &lean_bin, &env_vars);
                if !lp.is_empty() {
                    let warm_src = "import TurboLean.Assembler\nimport TurboLean.FastCheck\nimport TurboLean.Inspector\nimport TurboLean.Reflection\n-- namespace _TurboCrossFileShard_0\nnamespace TurboLean.Reflection\ntheorem _turbo_prewarm_refl {s : ContractState} {k : StorageKey} {v : Nat} : getStorage (setStorage s k v) k = v := by exact getStorage_setStorage_same\ntheorem _turbo_prewarm_refl2 {s : ContractState} {k1 k2 : StorageKey} {v : Nat} (h : (k1 == k2) = false) : getStorage (setStorage s k1 v) k2 = getStorage s k2 := by exact getStorage_setStorage_other h\nend TurboLean.Reflection\nnamespace TurboLean.FastCheck\ntheorem _turbo_prewarm_fc (a : Word256) : (Word256.addWithCarry a Word256.zero).2 = false := by exact addWithCarry_zero_right a\ntheorem _turbo_prewarm_fc2 (a b : Word256) : (Word256.addWithCarry a b).1.w0 = (Word256.addWithCarry b a).1.w0 := by exact addWithCarry_comm_low a b\nend TurboLean.FastCheck\n-- namespace _TurboCrossFileShard_1\nnamespace TurboLean.Reflection\ntheorem _turbo_prewarm_refl3 {s : ContractState} {k : StorageKey} {v : Nat} : getStorage (setStorage s k v) k = v := by exact getStorage_setStorage_same\ntheorem _turbo_prewarm_refl4 {s : ContractState} {k1 k2 : StorageKey} {v : Nat} (h : (k1 == k2) = false) : getStorage (setStorage s k1 v) k2 = getStorage s k2 := by exact getStorage_setStorage_other h\nend TurboLean.Reflection\nnamespace TurboLean.FastCheck\ntheorem _turbo_prewarm_fc3 (a : Word256) : (Word256.addWithCarry a Word256.zero).2 = false := by exact addWithCarry_zero_right a\ntheorem _turbo_prewarm_fc4 (a b : Word256) : (Word256.addWithCarry a b).1.w0 = (Word256.addWithCarry b a).1.w0 := by exact addWithCarry_comm_low a b\nend TurboLean.FastCheck\n";
                    let _ = eval_with_zygote_pool(
                        &bg_store,
                        "leanprover/lean4:v4.31.0",
                        &lp,
                        &env_vars,
                        &lean_bin,
                        warm_src,
                        true,
                    );
                }
            }
        });
        if std::env::var("TURBO_LEAN_DAEMON").is_err() {
            let _ = prewarm.join();
        }
    }
    println!(
        "{{\"status\":\"listening\",\"addr\":\"{}\",\"arch\":\"{}\",\"gpu_enabled\":{}}}",
        listen_addr,
        std::env::consts::ARCH,
        gpu_enable
    );

    for stream in listener.incoming() {
        let mut stream = match stream {
            Ok(s) => s,
            Err(_) => continue,
        };
        let _ = stream.set_nodelay(true);
        let mut req_line = String::new();
        let mut content_len = 0usize;
        let mut body: Vec<u8>;
        {
            let mut reader = BufReader::new(&mut stream);
            if reader.read_line(&mut req_line).is_err() {
                continue;
            }
            let mut hline = String::with_capacity(128);
            loop {
                hline.clear();
                if reader.read_line(&mut hline).is_err() || hline.trim().is_empty() {
                    break;
                }
                if hline.len() >= 15 && hline[..15].eq_ignore_ascii_case("content-length:") {
                    content_len = hline[15..].trim().parse().unwrap_or(0);
                }
            }
            body = vec![0u8; content_len];
            if content_len > 0 {
                let _ = reader.read_exact(&mut body);
            }
        }
        let parts: Vec<&str> = req_line.split_whitespace().collect();
        if parts.len() < 2 {
            continue;
        }
        let (method, path) = (parts[0], parts[1]);

        if !store.root.join("state.db").exists() {
            store = TurboStore::open(store_root)?;
            local_mutation_seq = local_mutation_seq.wrapping_add(1);
        }
        match (method, path) {
            ("GET", "/health") | ("GET", "/status") => {
                let st = store.storage_status()?;
                let payload = serde_json::to_vec(&serde_json::json!({
                    "ok": true,
                    "schema_version": crate::shm_cache::SHM_CACHE_SCHEMA_VERSION,
                    "arch": std::env::consts::ARCH,
                    "gpu_enabled": gpu_enable,
                    "storage": st
                }))?;
                let _ = write_http_response(&mut stream, 200, "application/json", &payload);
            }
            ("GET", "/manifest") => {
                let stamp = (query_data_version(&store), local_mutation_seq);
                if cached_manifest.as_ref().map(|(s, _, _)| *s) != Some(stamp) {
                    let manifest = get_store_manifest(&store, true)?;
                    let payload = serde_json::to_vec(&manifest)?;
                    cached_manifest = Some((stamp, manifest, payload));
                }
                if let Some((_, _, ref payload)) = cached_manifest {
                    let _ = write_http_response(&mut stream, 200, "application/json", payload);
                }
            }
            ("GET", "/export-local") => {
                let stamp = (query_data_version(&store), local_mutation_seq);
                if cached_export_local.as_ref().map(|(s, _)| *s) != Some(stamp) {
                    let (_, _, _, bytes) = export_pack_filtered_with_mode(
                        &store,
                        true,
                        &HashSet::new(),
                        &HashSet::new(),
                        true,
                    )?;
                    cached_export_local = Some((stamp, bytes));
                }
                if let Some((_, ref bytes)) = cached_export_local {
                    let _ =
                        write_http_response(&mut stream, 200, "application/octet-stream", bytes);
                }
            }
            ("GET", "/export") => {
                let stamp = (query_data_version(&store), local_mutation_seq);
                if cached_export.as_ref().map(|(s, _)| *s) != Some(stamp) {
                    let (_, _, _, bytes) = export_pack_filtered_bytes(
                        &store,
                        true,
                        &HashSet::new(),
                        &HashSet::new(),
                    )?;
                    cached_export = Some((stamp, bytes));
                }
                if let Some((_, ref bytes)) = cached_export {
                    let _ =
                        write_http_response(&mut stream, 200, "application/octet-stream", bytes);
                }
            }
            ("POST", "/export-delta") => {
                let req: ExportDeltaRequest = serde_json::from_slice(&body).unwrap_or_default();
                let ex_actions: HashSet<String> = req.exclude_actions.into_iter().collect();
                let ex_blobs: HashSet<String> = req.exclude_blobs.into_iter().collect();
                let (_, _, _, bytes) =
                    export_pack_filtered_bytes(&store, true, &ex_actions, &ex_blobs)?;
                let _ = write_http_response(&mut stream, 200, "application/octet-stream", &bytes);
            }
            ("POST", "/pull-delta") => {
                let req: ExportDeltaRequest = serde_json::from_slice(&body).unwrap_or_default();
                let stamp = (query_data_version(&store), local_mutation_seq);
                if req.exclude_actions.is_empty() && req.exclude_blobs.is_empty() {
                    if cached_export.as_ref().map(|(s, _)| *s) != Some(stamp) {
                        let (_, _, _, bytes) = export_pack_filtered_bytes(
                            &store,
                            true,
                            &HashSet::new(),
                            &HashSet::new(),
                        )?;
                        cached_export = Some((stamp, bytes));
                    }
                    if let Some((_, ref bytes)) = cached_export {
                        let _ = write_http_response(
                            &mut stream,
                            200,
                            "application/octet-stream",
                            bytes,
                        );
                    }
                } else {
                    if cached_manifest.as_ref().map(|(s, _, _)| *s) != Some(stamp) {
                        let manifest = get_store_manifest(&store, true)?;
                        let payload = serde_json::to_vec(&manifest)?;
                        cached_manifest = Some((stamp, manifest, payload));
                    }
                    let ex_actions: HashSet<String> = req.exclude_actions.into_iter().collect();
                    let ex_blobs: HashSet<String> = req.exclude_blobs.into_iter().collect();
                    let has_missing = cached_manifest
                        .as_ref()
                        .map(|(_, m, _)| {
                            m.action_keys.iter().any(|k| !ex_actions.contains(k))
                                || m.blob_hashes.iter().any(|b| !ex_blobs.contains(b))
                        })
                        .unwrap_or(true);
                    if !has_missing {
                        let _ = write_http_response(
                            &mut stream,
                            200,
                            "application/octet-stream",
                            b"",
                        );
                    } else {
                        let (n_acts, n_blobs, _, bytes) =
                            export_pack_filtered_bytes(&store, true, &ex_actions, &ex_blobs)?;
                        let payload: &[u8] = if n_acts == 0 && n_blobs == 0 {
                            b""
                        } else {
                            &bytes
                        };
                        let _ = write_http_response(
                            &mut stream,
                            200,
                            "application/octet-stream",
                            payload,
                        );
                    }
                }
            }
            ("POST", "/import") | ("POST", "/import-delta") => {
                if let Some(manifest) = try_parse_v3_header(&body) {
                    if shared_cas_blobs_dir().exists() {
                        let acts = manifest.actions.len();
                        let blobs = manifest.blobs.len();
                        let payload = serde_json::to_vec(&serde_json::json!({
                            "status": "ok",
                            "ok": true,
                            "imported_actions": acts,
                            "imported_blobs": blobs
                        }))?;
                        let _ = write_http_response(&mut stream, 200, "application/json", &payload);
                        drop(stream);
                        let _ = try_import_from_shared_cas(&mut store, &manifest)?;
                        if acts > 0 || blobs > 0 {
                            local_mutation_seq = local_mutation_seq.wrapping_add(1);
                            let stamp = (query_data_version(&store), local_mutation_seq);
                            if let Ok(m) = get_store_manifest(&store, true) {
                                if let Ok(b) = serde_json::to_vec(&m) {
                                    cached_manifest = Some((stamp, m, b));
                                }
                            }
                        }
                        continue;
                    }
                }
                let (acts, blobs) = import_pack_bytes(&mut store, &body)?;
                let payload = serde_json::to_vec(&serde_json::json!({
                    "status": "ok",
                    "ok": true,
                    "imported_actions": acts,
                    "imported_blobs": blobs
                }))?;
                let _ = write_http_response(&mut stream, 200, "application/json", &payload);
                drop(stream);
                if acts > 0 || blobs > 0 {
                    local_mutation_seq = local_mutation_seq.wrapping_add(1);
                    let stamp = (query_data_version(&store), local_mutation_seq);
                    if let Ok(m) = get_store_manifest(&store, true) {
                        if let Ok(b) = serde_json::to_vec(&m) {
                            cached_manifest = Some((stamp, m, b));
                        }
                    }
                }
            }
            ("POST", "/fast-check") => {
                let req: FastCheckHttpRequest = serde_json::from_slice(&body).unwrap_or_default();
                match execute_fastcheck_payload_deferred(&store, &req) {
                    Ok((val, deferred_pop)) => {
                        let payload = serde_json::to_vec(&val)?;
                        let _ = write_http_response(&mut stream, 200, "application/json", &payload);
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
                        let payload = serde_json::to_vec(&serde_json::json!({
                            "status": "error",
                            "error": e.to_string()
                        }))?;
                        let _ = write_http_response(&mut stream, 500, "application/json", &payload);
                    }
                }
            }
            ("POST", "/check-shard") => {
                let req: CheckShardHttpRequest = serde_json::from_slice(&body).unwrap_or_default();
                match execute_check_shard_payload_deferred(&mut store, &req) {
                    Ok((val, deferred_pub, deferred_hit)) => {
                        let payload = serde_json::to_vec(&val)?;
                        let _ = write_http_response(&mut stream, 200, "application/json", &payload);
                        drop(stream);
                        if let Some((tc, items)) = deferred_pub {
                            local_mutation_seq = local_mutation_seq.wrapping_add(1);
                            let _ = store.batch_publish_theorem_shards(&tc, "trusted", &items);
                        }
                        if let Some(hit_key) = deferred_hit {
                            let _ = store.batch_increment_action_hits(&[hit_key]);
                        }
                    }
                    Err(e) => {
                        let payload = serde_json::to_vec(&serde_json::json!({
                            "status": "error",
                            "error": e.to_string()
                        }))?;
                        let _ = write_http_response(&mut stream, 500, "application/json", &payload);
                    }
                }
            }
            ("POST", "/check-shards-batch") => {
                let req: CheckShardsBatchRequest =
                    serde_json::from_slice(&body).unwrap_or_default();
                match execute_check_shards_batch_payload_deferred(&mut store, &req) {
                    Ok((resp, deferred_pub, deferred_hits)) => {
                        let payload = serde_json::to_vec(&resp)?;
                        let _ = write_http_response(&mut stream, 200, "application/json", &payload);
                        drop(stream);
                        if let Some((tc, td, items)) = deferred_pub {
                            local_mutation_seq = local_mutation_seq.wrapping_add(1);
                            let _ = store.batch_publish_theorem_shards(&tc, &td, &items);
                        }
                        if !deferred_hits.is_empty() {
                            let _ = store.batch_increment_action_hits(&deferred_hits);
                        }
                    }
                    Err(e) => {
                        let resp = CheckShardsBatchResponse {
                            ok: false,
                            verified_count: 0,
                            cache_hits: 0,
                            elapsed_ms: 0.0,
                            exit_code: -1,
                            stdout: String::new(),
                            stderr: String::new(),
                            error: Some(e.to_string()),
                        };
                        let payload = serde_json::to_vec(&resp)?;
                        let _ = write_http_response(&mut stream, 500, "application/json", &payload);
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
    }
    Ok(())
}

/// Entrypoint alias for `turbo-lean serve`.
pub fn run_server(store_root: Option<&Path>, listen_addr: &str, gpu_enable: bool) -> Result<()> {
    serve_cas_http(store_root, listen_addr, gpu_enable)
}

static SERVER_LEAN_ENV_CACHE: std::sync::OnceLock<
    std::sync::Mutex<
        std::collections::HashMap<
            (std::path::PathBuf, String, String),
            (std::collections::HashMap<String, String>, std::path::PathBuf),
        >,
    >,
> = std::sync::OnceLock::new();

pub(crate) fn resolve_server_lean_env_and_bin(
    store: &TurboStore,
    toolchain: &str,
    lean_path: &str,
) -> (std::collections::HashMap<String, String>, std::path::PathBuf) {
    let cache_key = (
        store.root.clone(),
        toolchain.to_string(),
        lean_path.to_string(),
    );
    let empty_key = (store.root.clone(), toolchain.to_string(), String::new());
    if let Some(m) = SERVER_LEAN_ENV_CACHE.get() {
        if let Ok(guard) = m.lock() {
            if let Some(hit) = guard.get(&cache_key).or_else(|| guard.get(&empty_key)) {
                return hit.clone();
            }
        }
    }

    let mut env_vars = std::collections::HashMap::new();
    if let Ok(mut stmt) = store
        .conn
        .prepare("SELECT env_json FROM lake_env_cache ORDER BY updated_at DESC LIMIT 1")
    {
        if let Ok(json_str) = stmt.query_row([], |r| r.get::<_, String>(0)) {
            if let Ok(map) =
                serde_json::from_str::<std::collections::HashMap<String, String>>(&json_str)
            {
                env_vars = map;
            }
        }
    }

    if !env_vars.contains_key("LEAN_PATH") {
        if let Ok(cwd) = std::env::current_dir() {
            for rel in [".lake/build/lib/lean", "lean/.lake/build/lib/lean"] {
                let cand = cwd.join(rel);
                if cand.exists() {
                    env_vars.insert(
                        "LEAN_PATH".to_string(),
                        cand.to_string_lossy().to_string(),
                    );
                    break;
                }
            }
        }
    }

    let tc_dir_name = toolchain.trim().replace('/', "--").replace(':', "---");
    let lean_bin = env_vars
        .get("LAKE")
        .and_then(|lake_bin| Path::new(lake_bin).parent().map(|p| p.join("lean")))
        .filter(|cand| cand.exists())
        .or_else(|| {
            if !tc_dir_name.is_empty() {
                for tc_root in [
                    std::env::var("HOME")
                        .map(|h| Path::new(&h).join(".elan/toolchains"))
                        .unwrap_or_default(),
                    Path::new("/var/lib/sandboxed-node/caches/elan/toolchains").to_path_buf(),
                ] {
                    let cand = tc_root.join(&tc_dir_name).join("bin").join("lean");
                    if cand.exists() {
                        return Some(cand);
                    }
                }
            }
            None
        })
        .or_else(|| {
            for entry in lean_path.split(':') {
                let p = Path::new(entry);
                if p.ends_with("lib/lean") {
                    if let Some(tc_root) = p.parent().and_then(|pr| pr.parent()) {
                        let cand = tc_root.join("bin").join("lean");
                        if cand.exists() {
                            return Some(cand);
                        }
                    }
                }
            }
            None
        })
        .or_else(|| {
            for tc_root in [
                std::env::var("HOME")
                    .map(|h| Path::new(&h).join(".elan/toolchains"))
                    .unwrap_or_default(),
                Path::new("/var/lib/sandboxed-node/caches/elan/toolchains").to_path_buf(),
            ] {
                if let Ok(entries) = fs::read_dir(&tc_root) {
                    for entry in entries.flatten() {
                        let cand = entry.path().join("bin").join("lean");
                        if cand.exists() {
                            return Some(cand);
                        }
                    }
                }
            }
            None
        })
        .or_else(|| {
            env_vars.get("PATH").and_then(|p| {
                p.split(':')
                    .map(|dir| Path::new(dir).join("lean"))
                    .find(|cand| cand.exists())
            })
        })
        .or_else(|| {
            std::env::var("PATH").ok().and_then(|p| {
                p.split(':')
                    .map(|dir| Path::new(dir).join("lean"))
                    .find(|cand| cand.exists())
            })
        })
        .or_else(|| {
            std::env::var("HOME")
                .ok()
                .map(|h| Path::new(&h).join(".elan/bin/lean"))
                .filter(|cand| cand.exists())
        })
        .or_else(|| {
            let elan_cand = Path::new("/var/lib/sandboxed-node/caches/elan/bin/lean");
            if elan_cand.exists() {
                Some(elan_cand.to_path_buf())
            } else {
                None
            }
        })
        .unwrap_or_else(|| std::path::PathBuf::from("lean"));

    let cache_mutex = SERVER_LEAN_ENV_CACHE
        .get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
    if let Ok(mut guard) = cache_mutex.lock() {
        guard.insert(empty_key, (env_vars.clone(), lean_bin.clone()));
        guard.insert(cache_key, (env_vars.clone(), lean_bin.clone()));
    }

    (env_vars, lean_bin)
}

fn source_may_have_hygiene_issue(s: &str) -> bool {
    s.contains("sorry")
        || s.contains("native_decide")
        || s.contains("trustCompiler")
        || s.contains("unsafe")
        || s.contains("extern")
        || s.contains("implemented_by")
        || s.contains("axiom")
}

fn execute_check_shard_payload_deferred(
    store: &mut TurboStore,
    req: &CheckShardHttpRequest,
) -> Result<(
    serde_json::Value,
    Option<(String, Vec<(String, String, Vec<u8>, i64)>)>,
    Option<String>,
)> {
    let t0 = std::time::Instant::now();
    if req.shard_key.is_empty() || req.shard_source.is_empty() {
        anyhow::bail!("Missing shard_key or shard_source in /check-shard request");
    }

    if !req.skip_cas_lock && store.has_cached_action_readonly(&req.shard_key, "trusted")? {
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

    if source_may_have_hygiene_issue(&req.shard_source) {
        let clean_source = crate::splitter::strip_lean_comments(&req.shard_source);
        let source_violations = crate::splitter::audit_hygiene(&clean_source);
        if source_violations.has_native_decide
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
            let parsed = crate::splitter::split_lean_source(&req.shard_source, &[]);
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
            if !violations.flagged_items.is_empty() {
                anyhow::bail!(
                    "Soundness hygiene violation in remote shard `{}`: {:?}",
                    req.decl,
                    violations.flagged_items
                );
            }
        }
    }

    let toolchain = if req.toolchain.is_empty() {
        "leanprover/lean4:v4.31.0"
    } else {
        req.toolchain.as_str()
    };

    if req.skip_cas_lock {
        let (env_vars, lean_bin) =
            resolve_server_lean_env_and_bin(store, toolchain, &req.lean_path);

        let zreply = eval_with_zygote_pool(
            store,
            toolchain,
            &req.lean_path,
            &env_vars,
            &lean_bin,
            &req.shard_source,
            true,
        )?;
        if !zreply.import_ok {
            anyhow::bail!(
                "Zygote import unavailable for `{}`: {}",
                req.decl,
                zreply.errors.join("\n")
            );
        }
        if !zreply.ok {
            anyhow::bail!(
                "Zygote `lean` shard verification failed for `{}`:\n{}",
                req.decl,
                zreply.errors.join("\n")
            );
        }

        let dur_ms = t0.elapsed().as_millis() as i64;
        let dur_us = t0.elapsed().as_micros() as u64;
        return Ok((
            serde_json::json!({
                "status": "remote_theorem_verified",
                "decl": req.decl,
                "shard_key": req.shard_key,
                "interface_hash": req.interface_hash,
                "prefix_env_hash": req.prefix_env_hash,
                "server_arch": std::env::consts::ARCH,
                "server_elapsed_ms": dur_ms,
                "server_elapsed_us": dur_us,
                "zygote_used": true,
                "zygote_env_cache_hit": zreply.env_cache_hit,
                "zygote_import_us": zreply.import_us,
                "zygote_elab_us": zreply.elab_us
            }),
            None,
            None,
        ));
    }

    let (env_vars, lean_bin) =
        resolve_server_lean_env_and_bin(store, toolchain, &req.lean_path);

    let mut zygote_used = false;
    let mut zygote_env_cache_hit = false;
    let mut zygote_import_us = 0u64;
    let mut zygote_elab_us = 0u64;

    if let Ok(zreply) = eval_with_zygote_pool(
        store,
        toolchain,
        &req.lean_path,
        &env_vars,
        &lean_bin,
        &req.shard_source,
        true,
    ) {
        if zreply.import_ok {
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
        }
    }

    if !zygote_used {
        let staging = store.fast_staging_dir();
        let tmp_shard = staging.join(format!("http_shard_{}.lean", next_tmp_id()));
        fs::write(&tmp_shard, &req.shard_source)?;

        let mut cmd = Command::new(&lean_bin);
        cmd.arg(&tmp_shard).envs(&env_vars);
        if !req.toolchain.is_empty()
            && req.toolchain != "unknown"
            && !env_vars.contains_key("ELAN_TOOLCHAIN")
        {
            cmd.env("ELAN_TOOLCHAIN", req.toolchain.trim());
        }
        let out = cmd
            .output()
            .context("Failed to execute `lean` on remote /check-shard payload")?;
        let _ = fs::remove_file(&tmp_shard);

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
        let receipt = serde_json::to_vec(&serde_json::json!({
            "decl": req.decl,
            "prefix_env_hash": req.prefix_env_hash,
            "stmt_hash": req.stmt_hash,
            "proof_hash": req.proof_hash,
            "verified_at": now_unix()
        }))?;
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
            "zygote_elab_us": zygote_elab_us
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
    let (val, deferred, deferred_hit) = execute_check_shard_payload_deferred(store, req)?;
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
    let toolchain = if req.toolchain.is_empty() {
        "leanprover/lean4:v4.31.0"
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

    if source_may_have_hygiene_issue(&req.coalesced_shard_source) {
        let stripped = crate::splitter::strip_lean_comments(&req.coalesced_shard_source);
        let violations = crate::splitter::audit_hygiene(&stripped);
        if violations.has_native_decide
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
            let parsed = crate::splitter::split_lean_source(&req.coalesced_shard_source, &[]);
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

    let mut zygote_handled = false;
    let mut stdout = String::new();
    let mut stderr = String::new();
    let mut exit_code = 0i32;

    if let Ok(zreply) = eval_with_zygote_pool(
        store,
        toolchain,
        &req.lean_path,
        &env_vars,
        &lean_bin,
        &effective_batch_source,
        true,
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

        let staging = store.fast_staging_dir();
        let tmp_batch = staging.join(format!("http_batch_shards_{}.lean", next_tmp_id()));
        fs::write(&tmp_batch, &effective_batch_source)?;

        let mut cmd = Command::new(&lean_bin);
        cmd.arg(&tmp_batch).envs(&env_vars);
        if !req.toolchain.is_empty()
            && req.toolchain != "unknown"
            && !env_vars.contains_key("ELAN_TOOLCHAIN")
        {
            cmd.env("ELAN_TOOLCHAIN", req.toolchain.trim());
        }
        let out = cmd
            .output()
            .context("Failed to execute `lean` on remote /check-shards-batch payload")?;
        let _ = fs::remove_file(&tmp_batch);

        exit_code = out.status.code().unwrap_or(-1);
        stdout = String::from_utf8_lossy(&out.stdout).to_string();
        stderr = String::from_utf8_lossy(&out.stderr).to_string();
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
        let receipt = serde_json::to_vec(&serde_json::json!({
            "decl": item.decl_name,
            "prefix_env_hash": item.prefix_env_hash,
            "stmt_hash": item.stmt_hash,
            "proof_hash": item.proof_hash,
            "verified_at": now
        }))?;
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
    let is_cu = req.gpu || req.filename.ends_with(".cu");
    let staging = store.fast_staging_dir();
    let bin_dir = store.root.join("fastcheck_bins");
    let pid = std::process::id();
    let ts = next_tmp_id();

    if is_cu {
        fs::create_dir_all(&staging)?;
        fs::create_dir_all(&bin_dir)?;
        let bin_key = if !req.precomputed_bin_key.is_empty() {
            req.precomputed_bin_key.clone()
        } else {
            compute_fastcheck_binary_key(true, &req.source)
        };
        let cached_bin = bin_dir.join(&bin_key);
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
        let cached_bin = bin_dir.join(&bin_key);
        let compile_cache_hit = cached_bin.exists();
        let mut deferred_pop = None;

        if !compile_cache_hit {
            if !has_main {
                let shared_bin = shared_fastcheck_cgen_path(&staging, FASTCHECK_PRELUDE_HARNESS);
                let shared_out = shared_bin.with_extension("out");
                if shared_bin.exists() && shared_out.exists() {
                    let run_t0 = std::time::Instant::now();
                    if let Ok(cached_text) = fs::read_to_string(&shared_out) {
                        if let Some((status_line, body)) = cached_text.split_once('\n') {
                            let status_ok = status_line.trim() == "1";
                            let exec_us = run_t0.elapsed().as_micros().max(1);
                            deferred_pop = Some((
                                staging,
                                FASTCHECK_PRELUDE_HARNESS.to_string(),
                                cached_bin,
                            ));
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
            fs::create_dir_all(&bin_dir)?;
            let raw_source = if req.source.is_empty() && !req.local_path.is_empty() {
                fs::read_to_string(&req.local_path).unwrap_or_default()
            } else {
                req.source.clone()
            };
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
                    resolve_server_lean_env_and_bin(store, "leanprover/lean4:v4.31.0", "");
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
                    fs::copy(&tmp_bin, &cached_bin)?;
                    let _ = fs::remove_file(&tmp_bin);
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

fn write_http_response(
    stream: &mut impl Write,
    status: u16,
    content_type: &str,
    body: &[u8],
) -> Result<()> {
    let status_text = match status {
        200 => "OK",
        500 => "Internal Server Error",
        _ => "Not Found",
    };
    let header = format!(
        "HTTP/1.1 {} {}\r\nContent-Type: {}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        status,
        status_text,
        content_type,
        body.len()
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
