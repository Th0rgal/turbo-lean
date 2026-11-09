use super::*;
use crate::db::{ActionRecord, BlobEntry, TurboStore};
use crate::pack::archive::ensure_blob_in_shared_cas;
use anyhow::Result;
use std::collections::HashSet;
use std::fs;
use std::io::{Read, Write};
use std::net::TcpListener;
use std::path::Path;

#[cfg(unix)]
#[test]
fn verifier_helpers_fail_closed_when_toolchain_siblings_are_missing() -> Result<()> {
    use std::os::unix::fs::PermissionsExt;
    let dir = std::env::temp_dir().join(format!(
        "turbo-missing-tools-{}-{}",
        std::process::id(),
        next_tmp_id()
    ));
    fs::create_dir_all(dir.join("bin"))?;
    fs::create_dir_all(dir.join("path"))?;
    let marker = dir.join("invoked");
    let script = format!("#!/bin/sh\necho invoked > '{}'\n", marker.display());
    for tool in ["lean", "lake", "leanc"] {
        for bin in ["bin", "path"] {
            let path = dir.join(bin).join(tool);
            fs::write(&path, &script)?;
            fs::set_permissions(&path, fs::Permissions::from_mode(0o755))?;
        }
    }
    let lean = dir.join("bin/lean");
    let store = TurboStore::open(Some(&dir.join("store")))?;
    let env = std::collections::HashMap::from([(
        "PATH".into(),
        dir.join("path").to_string_lossy().into_owned(),
    )]);
    for missing in ["lake", "leanc"] {
        let path = dir.join("bin").join(missing);
        fs::rename(&path, path.with_extension("saved"))?;
        for error in [
            crate::zygote::ensure_zygote_binary(&store, &lean, &env).unwrap_err(),
            prewarm_shared_fastcheck_harness(&store, &lean, &env).unwrap_err(),
            compile_fastcheck_c_to_bin(
                &lean,
                &dir.join("input.c"),
                &dir.join("output"),
                &dir,
                &env,
            )
            .unwrap_err(),
        ] {
            let message = format!("{error:#}");
            assert!(
                message.contains("Missing required toolchain sibling") && message.contains(missing),
                "{message}"
            );
        }
        assert!(
            !marker.exists(),
            "helper resolved a missing sibling through PATH"
        );
        fs::rename(path.with_extension("saved"), path)?;
    }
    assert!(
        crate::module_builder::ToolchainExecutables::from_lean(Path::new("lean"))
            .unwrap_err()
            .to_string()
            .contains("must be absolute")
    );
    fs::remove_dir_all(dir)?;
    Ok(())
}

#[test]
fn test_is_loopback_http_url_rejects_lookalike_hosts() {
    assert!(is_loopback_http_url("http://127.0.0.1:9400"));
    assert!(is_loopback_http_url("http://127.0.0.1:9400/export"));
    assert!(is_loopback_http_url("http://127.0.0.1"));
    assert!(is_loopback_http_url("http://localhost:9400"));
    assert!(is_loopback_http_url("http://[::1]:9400"));
    assert!(!is_loopback_http_url("http://127.0.0.1.evil.example:9400"));
    assert!(!is_loopback_http_url("http://localhost.evil.example"));
    assert!(!is_loopback_http_url("http://localhost@evil.example"));
    assert!(!is_loopback_http_url("https://127.0.0.1:9400"));
    assert!(!is_loopback_http_url("http://10.0.0.1:9400"));
}
use crate::db::SingleflightOutcome;

pub(crate) fn env_test_lock() -> &'static std::sync::Mutex<()> {
    static ENV_LOCK: std::sync::OnceLock<std::sync::Mutex<()>> = std::sync::OnceLock::new();
    ENV_LOCK.get_or_init(|| std::sync::Mutex::new(()))
}

struct ScopedEnvClear(&'static [&'static str]);
impl Drop for ScopedEnvClear {
    fn drop(&mut self) {
        for k in self.0 {
            std::env::remove_var(k);
        }
    }
}

#[test]
fn test_env_tokens_never_sent_over_non_loopback_plain_http() {
    let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
    std::env::set_var("TURBO_LEAN_API_TOKEN", "api-tok");
    std::env::set_var("TURBO_LEAN_DAEMON_TOKEN", "daemon-tok");
    let _clear = ScopedEnvClear(&["TURBO_LEAN_API_TOKEN", "TURBO_LEAN_DAEMON_TOKEN"]);
    assert_eq!(
        resolve_http_auth_token("http://10.0.0.1:9400/import", None),
        None
    );
    assert_eq!(
        resolve_http_auth_token("http://127.0.0.1.evil.example/x", None),
        None
    );
    assert_eq!(
        resolve_http_auth_token("http://127.0.0.1:9400/import", None).as_deref(),
        Some("api-tok")
    );
    assert_eq!(
        resolve_http_auth_token("https://cas.example/import", None).as_deref(),
        Some("api-tok")
    );
    std::env::remove_var("TURBO_LEAN_API_TOKEN");
    assert_eq!(
        resolve_http_auth_token("https://cas.example/import", None),
        None
    );
    assert_eq!(
        resolve_http_auth_token("http://localhost:9400/eval", None).as_deref(),
        Some("daemon-tok")
    );
    assert_eq!(
        resolve_http_auth_token("http://10.0.0.1:9400", Some("explicit")).as_deref(),
        Some("explicit")
    );
}

#[test]
fn anonymous_request_never_sends_ambient_loopback_tokens() {
    use std::io::{Read, Write};
    let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
    std::env::set_var("TURBO_LEAN_API_TOKEN", "api-tok");
    std::env::set_var("TURBO_LEAN_DAEMON_TOKEN", "daemon-tok");
    let _clear = ScopedEnvClear(&["TURBO_LEAN_API_TOKEN", "TURBO_LEAN_DAEMON_TOKEN"]);
    let request_seen_by_server = |anonymous: bool| {
        let listener = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
        let url = format!("http://{}/artifact", listener.local_addr().unwrap());
        let srv = std::thread::spawn(move || {
            let (mut sock, _) = listener.accept().unwrap();
            let mut buf = [0u8; 4096];
            let n = sock.read(&mut buf).unwrap();
            let _ = sock
                .write_all(b"HTTP/1.1 200 OK\r\nContent-Length: 2\r\nConnection: close\r\n\r\nok");
            String::from_utf8_lossy(&buf[..n]).to_ascii_lowercase()
        });
        let body = if anonymous {
            http_request_full_anonymous("GET", &url, "x/y", &[], Some(5_000), None, || {})
        } else {
            http_request_full("GET", &url, "x/y", &[], Some(5_000), None, None, || {})
        };
        assert_eq!(body.unwrap(), b"ok");
        srv.join().unwrap()
    };
    let ambient = request_seen_by_server(false);
    assert!(
        ambient.contains("authorization: bearer api-tok"),
        "{ambient}"
    );
    let anon = request_seen_by_server(true);
    assert!(
        !anon.contains("authorization") && !anon.contains("x-turbo-token"),
        "{anon}"
    );
}

#[test]
fn test_export_pack_filtered_zero_redundancy_delta() -> Result<()> {
    let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
    let dir1 = std::env::temp_dir().join(format!("turbo_lean_pack_test1_{}", std::process::id()));
    let dir2 = std::env::temp_dir().join(format!("turbo_lean_pack_test2_{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir1);
    let _ = fs::remove_dir_all(&dir2);

    let mut store1 = TurboStore::open(Some(&dir1))?;
    let mut store2 = TurboStore::open(Some(&dir2))?;

    let b1 = store1.store_immutable_blob(b"olean-payload-1", "olean", "trusted", 0)?;
    if let SingleflightOutcome::Leader(lease) =
        store1.acquire_singleflight("act-1", "v4.35.0", "module_full", "trusted")?
    {
        store1.publish_action(
            &lease,
            &[BlobEntry {
                blob_hash: b1,
                kind: "olean".into(),
                size_bytes: 15,
                rel_path: "A.olean".into(),
            }],
            10,
            0,
            0,
            "trusted",
        )?;
    }

    let pack1 = dir1.join("cold.tlpack");
    assert_eq!(
        export_pack_filtered(&store1, &pack1, true, &HashSet::new(), &HashSet::new())?,
        (1, 1, 15)
    );
    assert_eq!(
        import_pack_with_policy(&mut store2, &pack1, Some("trusted"), None, true)?,
        (1, 1)
    );

    let m2 = get_store_manifest(&store2, true)?;
    let (ex_acts, ex_blobs): (HashSet<_>, HashSet<_>) = (
        m2.action_keys.into_iter().collect(),
        m2.blob_hashes.into_iter().collect(),
    );
    assert_eq!(
        export_pack_filtered(
            &store1,
            &dir1.join("noop.tlpack"),
            true,
            &ex_acts,
            &ex_blobs
        )?,
        (0, 0, 0)
    );

    let b2 = store1.store_immutable_blob(b"shard-payload-222", "expr_shard", "trusted", 0)?;
    if let SingleflightOutcome::Leader(lease2) =
        store1.acquire_singleflight("act-2", "v4.35.0", "theorem_shard", "trusted")?
    {
        store1.publish_action(
            &lease2,
            &[BlobEntry {
                blob_hash: b2,
                kind: "expr_shard".into(),
                size_bytes: 17,
                rel_path: "thm:foo".into(),
            }],
            5,
            0,
            0,
            "trusted",
        )?;
    }
    assert_eq!(
        export_pack_filtered(&store1, &dir1.join("inc.tlpack"), true, &ex_acts, &ex_blobs)?,
        (1, 1, 17)
    );

    let _ = fs::remove_dir_all(&dir1);
    let _ = fs::remove_dir_all(&dir2);
    Ok(())
}

#[test]
fn test_fastcheck_binary_cas_cache_hit() -> Result<()> {
    let dir = std::env::temp_dir().join(format!("turbo_lean_fc_bin_test_{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    let store = TurboStore::open(Some(&dir))?;

    let src = "def main : IO Unit := IO.println \"[Perceus FBIP] Checked 1,000,000 256-bit states (checksum=42)\"\n";
    let bin_key = compute_fastcheck_binary_key(false, src);
    let bin_dir = store.root.join("fastcheck_bins");
    fs::create_dir_all(&bin_dir)?;
    let cached_bin = bin_dir.join(&bin_key);
    fs::write(
        &cached_bin,
        b"#!/bin/sh\necho '[Perceus FBIP] Checked 1,000,000 256-bit states (checksum=42)'\n",
    )?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut perms = fs::metadata(&cached_bin)?.permissions();
        perms.set_mode(0o755);
        fs::set_permissions(&cached_bin, perms)?;
    }

    let req = FastCheckHttpRequest {
        filename: "test.lean".into(),
        source: src.into(),
        gpu: false,
        precomputed_bin_key: String::new(),
        has_main: None,
        local_path: String::new(),
    };
    let res = execute_fastcheck_payload(&store, &req)?;
    assert_eq!(
        (
            res["status"].as_str(),
            res["compile_cache_hit"].as_bool(),
            res["binary_cache_key"].as_str()
        ),
        (Some("ok"), Some(true), Some(bin_key.as_str()))
    );
    assert!(res["output"]
        .as_str()
        .unwrap_or("")
        .contains("Checked 1,000,000 256-bit states"));

    // Corrupt the cached `.out` sidecar with a 2-byte `"0\n"` failed-run stub and verify self-healing:
    fs::write(cached_bin.with_extension("out"), b"0\n")?;
    let res_healed = execute_fastcheck_payload(&store, &req)?;
    assert_eq!(
        (
            res_healed["status"].as_str(),
            res_healed["compile_cache_hit"].as_bool()
        ),
        (Some("ok"), Some(true))
    );
    assert!(res_healed["output"]
        .as_str()
        .unwrap_or("")
        .contains("Checked 1,000,000 256-bit states"));

    // Verify shared-bin sidecar self-healing on failed (`0\n...`) sidecars and non-caching of failing binaries:
    let shared_staging = dir.join("shared_staging");
    save_compiled_bin_to_shared(&shared_staging, src, &cached_bin);
    let shared_bin = shared_fastcheck_cgen_path(&shared_staging, src);
    fs::write(shared_bin.with_extension("out"), b"0\n")?;
    ensure_shared_fastcheck_out(&shared_bin);
    assert!(fs::read_to_string(shared_bin.with_extension("out"))?.starts_with("1\n"));
    fs::write(
        shared_bin.with_extension("out"),
        b"0\nuncertified crash output\n",
    )?;
    ensure_shared_fastcheck_out(&shared_bin);
    assert!(fs::read_to_string(shared_bin.with_extension("out"))?.starts_with("1\n"));

    let fail_src = "def main : IO Unit := throw (IO.userError \"boom\")\n";
    let fail_key = compute_fastcheck_binary_key(false, fail_src);
    let fail_bin = bin_dir.join(&fail_key);
    fs::write(&fail_bin, b"#!/bin/sh\necho 'boom'\nexit 1\n")?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut perms = fs::metadata(&fail_bin)?.permissions();
        perms.set_mode(0o755);
        fs::set_permissions(&fail_bin, perms)?;
    }
    let fail_req = FastCheckHttpRequest {
        filename: "fail.lean".into(),
        source: fail_src.into(),
        gpu: false,
        precomputed_bin_key: String::new(),
        has_main: Some(true),
        local_path: String::new(),
    };
    let fail_res = execute_fastcheck_payload(&store, &fail_req)?;
    assert_eq!(fail_res["status"].as_str(), Some("execution_failed"));
    assert_eq!(fail_res["ok"].as_bool(), Some(false));
    assert_eq!(fail_res["lean_native_certified"].as_bool(), Some(false));
    assert_eq!(fail_res["certification"].as_str(), Some("unavailable"));
    assert!(!fail_bin.with_extension("out").exists());

    let _ = fs::remove_dir_all(&dir);
    Ok(())
}

#[test]
fn test_batch_pack_import_and_zero_copy_existing_blob_skip() -> Result<()> {
    let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
    let dir_src =
        std::env::temp_dir().join(format!("turbo_lean_batch_imp_src_{}", std::process::id()));
    let dir_dst =
        std::env::temp_dir().join(format!("turbo_lean_batch_imp_dst_{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir_src);
    let _ = fs::remove_dir_all(&dir_dst);
    let (mut store_src, mut store_dst) = (
        TurboStore::open(Some(&dir_src))?,
        TurboStore::open(Some(&dir_dst))?,
    );

    let mut blob_hashes = Vec::new();
    for i in 0..10 {
        let payload = format!("blob-payload-{}", i).into_bytes();
        let bh = store_src.store_immutable_blob(&payload, "expr_shard", "trusted", 0)?;
        blob_hashes.push((bh.clone(), payload.len() as u64));
        if let SingleflightOutcome::Leader(lease) = store_src.acquire_singleflight(
            &format!("batch-act-{}", i),
            "v4.35.0",
            "theorem_shard",
            "trusted",
        )? {
            store_src.publish_action(
                &lease,
                &[BlobEntry {
                    blob_hash: bh,
                    kind: "expr_shard".into(),
                    size_bytes: payload.len() as u64,
                    rel_path: format!("thm:decl_{}", i),
                }],
                1,
                0,
                0,
                "trusted",
            )?;
        }
    }

    let pack_file = dir_src.join("batch.tlpack");
    let (exp_acts, exp_blobs, _) = export_pack(&store_src, &pack_file, true)?;
    assert_eq!((exp_acts, exp_blobs), (10, 10));
    assert_eq!(
        import_pack_with_policy(&mut store_dst, &pack_file, Some("trusted"), None, true)?,
        (10, 10)
    );

    #[cfg(unix)]
    let orig_inode = {
        use std::os::unix::fs::MetadataExt;
        fs::metadata(store_dst.blob_path(&blob_hashes[0].0))?.ino()
    };
    assert_eq!(
        import_pack_with_policy(&mut store_dst, &pack_file, Some("trusted"), None, true)?,
        (10, 10)
    );
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        assert_eq!(
            orig_inode,
            fs::metadata(store_dst.blob_path(&blob_hashes[0].0))?.ino()
        );
    }

    assert_eq!(
        store_dst
            .batch_get_theorem_shards(
                &[
                    "batch-act-0".into(),
                    "batch-act-5".into(),
                    "batch-act-9".into()
                ],
                "trusted"
            )?
            .len(),
        3
    );
    let _ = fs::remove_dir_all(&dir_src);
    let _ = fs::remove_dir_all(&dir_dst);
    Ok(())
}

pub(crate) fn spawn_test_server(dir_server: &Path) -> Result<String> {
    let port = TcpListener::bind("127.0.0.1:0")?.local_addr()?.port();
    let (srv_dir, addr) = (dir_server.to_path_buf(), format!("127.0.0.1:{}", port));
    let addr_clone = addr.clone();
    std::thread::spawn(move || {
        let _ = run_server_with_auth(Some(&srv_dir), &addr_clone, false, None, true);
    });
    for _ in 0..20 {
        if std::net::TcpStream::connect(&addr).is_ok() {
            break;
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
    Ok(addr)
}

#[test]
fn test_sync_push_http_zero_redundancy_delta_push() -> Result<()> {
    let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
    let dir_client = std::env::temp_dir().join(format!("turbo_lean_push_client_{}", next_tmp_id()));
    let dir_server = std::env::temp_dir().join(format!("turbo_lean_push_server_{}", next_tmp_id()));
    let _ = fs::remove_dir_all(&dir_client);
    let _ = fs::remove_dir_all(&dir_server);
    let mut store_client = TurboStore::open(Some(&dir_client))?;
    let _ = TurboStore::open(Some(&dir_server))?;

    let sk_hex = "1111111111111111111111111111111111111111111111111111111111111111";
    let vk_hex = {
        use ed25519_dalek::SigningKey;
        let sk_bytes = decode_hex_fixed::<32>(sk_hex)?;
        encode_hex_bytes(SigningKey::from_bytes(&sk_bytes).verifying_key().as_bytes())
    };
    std::env::set_var("TURBO_LEAN_PACK_SIGNING_KEY", sk_hex);
    std::env::set_var("TURBO_LEAN_PACK_TRUSTED_PUBKEY", &vk_hex);
    let _clear = ScopedEnvClear(&[
        "TURBO_LEAN_PACK_SIGNING_KEY",
        "TURBO_LEAN_PACK_TRUSTED_PUBKEY",
    ]);

    for i in 0..3 {
        let payload = format!("push-shard-{}", i).into_bytes();
        let bh = store_client.store_immutable_blob(&payload, "expr_shard", "trusted", 0)?;
        if let SingleflightOutcome::Leader(lease) = store_client.acquire_singleflight(
            &format!("push-act-{}", i),
            "v4.35.0",
            "theorem_shard",
            "trusted",
        )? {
            store_client.publish_action(
                &lease,
                &[BlobEntry {
                    blob_hash: bh,
                    kind: "expr_shard".into(),
                    size_bytes: payload.len() as u64,
                    rel_path: format!("thm:p_{}", i),
                }],
                1,
                0,
                0,
                "trusted",
            )?;
        }
    }

    let url = format!("http://{}", spawn_test_server(&dir_server)?);
    let (pushed_acts1, pushed_blobs1, raw_bytes1, pack_bytes1, noop1) =
        sync_push_http(&store_client, &url, true)?;
    assert!(pushed_acts1 == 3 && pushed_blobs1 == 3 && raw_bytes1 > 0 && pack_bytes1 > 0 && !noop1);
    assert_eq!(
        sync_push_http(&store_client, &url, true)?,
        (0, 0, 0, 0, true)
    );

    let dir_pull_client =
        std::env::temp_dir().join(format!("turbo_lean_pull_client_{}", next_tmp_id()));
    let _ = fs::remove_dir_all(&dir_pull_client);
    let mut store_pull = TurboStore::open(Some(&dir_pull_client))?;
    let ((pulled_acts1, pulled_blobs1), pulled_bytes1) =
        sync_pull_http(&mut store_pull, &url, true)?;
    assert!(pulled_acts1 == 3 && pulled_blobs1 == 3 && pulled_bytes1 > 0);
    assert_eq!(sync_pull_http(&mut store_pull, &url, true)?, ((0, 0), 0));

    std::env::remove_var("TURBO_LEAN_PACK_SIGNING_KEY");
    std::env::remove_var("TURBO_LEAN_PACK_TRUSTED_PUBKEY");
    for d in [&dir_pull_client, &dir_client, &dir_server] {
        let _ = fs::remove_dir_all(d);
    }
    Ok(())
}

#[test]
fn test_check_shard_http_offload_and_cache_hit() -> Result<()> {
    let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
    let dir_server =
        std::env::temp_dir().join(format!("turbo_lean_check_shard_srv_{}", next_tmp_id()));
    let _ = fs::remove_dir_all(&dir_server);
    let _ = TurboStore::open(Some(&dir_server))?;

    let endpoint = format!("http://{}/check-shard", spawn_test_server(&dir_server)?);
    let req = CheckShardHttpRequest {
        decl: "remote_thm_1".into(),
        shard_key: "shard_key_remote_thm_1".into(),
        shard_source: "theorem remote_thm_1 : 1 + 1 = 2 := rfl\n".into(),
        interface_hash: "iface_1".into(),
        prefix_env_hash: "prefix_1".into(),
        stmt_hash: "stmt_1".into(),
        proof_hash: "proof_1".into(),
        expected_kernel_type_hash: None,
        toolchain: "leanprover/lean4:v4.35.0".into(),
        lean_path: String::new(),
        skip_cas_lock: false,
        allowed_axioms: None,
        lean_args: Vec::new(),
        targets: Vec::new(),
    };
    let body = serde_json::to_vec(&req)?;
    let resp1: serde_json::Value =
        serde_json::from_slice(&http_request("POST", &endpoint, "application/json", &body)?)?;
    assert_eq!(resp1["status"].as_str(), Some("remote_theorem_verified"));
    let resp2: serde_json::Value =
        serde_json::from_slice(&http_request("POST", &endpoint, "application/json", &body)?)?;
    assert_eq!(resp2["status"].as_str(), Some("remote_theorem_cache_hit"));

    // Permissive server (`*`) must still enforce a strict caller's `allowed_axioms = Some(vec![])`
    // and reject a `bv_decide` shard instead of admitting or caching it under the strict policy.
    // `TURBO_LEAN_ALLOWED_AXIOMS` is otherwise mutated under `BWRAP_TEST_ENV_LOCK` (`check`,
    // `mcp`, `zygote`). Take it here too, after the `env_test_lock` held above, so the axiom
    // policy has a single owning lock and no key-reading test can observe a half-applied one.
    let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let prev_allow = std::env::var(crate::splitter::ALLOWED_AXIOMS_ENV).ok();
    std::env::set_var(crate::splitter::ALLOWED_AXIOMS_ENV, "*");
    let strict_bv_req = CheckShardHttpRequest {
        decl: "strict_bv_thm".into(),
        shard_key: "shard_key_strict_bv_thm".into(),
        shard_source: "theorem strict_bv_thm (x : UInt8) : x = x := by bv_decide\n".into(),
        interface_hash: "iface_bv".into(),
        prefix_env_hash: "prefix_bv".into(),
        stmt_hash: "stmt_bv".into(),
        proof_hash: "proof_bv".into(),
        expected_kernel_type_hash: None,
        toolchain: "leanprover/lean4:v4.35.0".into(),
        lean_path: String::new(),
        skip_cas_lock: false,
        allowed_axioms: Some(Vec::new()),
        lean_args: Vec::new(),
        targets: Vec::new(),
    };
    let strict_res = http_request(
        "POST",
        &endpoint,
        "application/json",
        &serde_json::to_vec(&strict_bv_req)?,
    );
    match prev_allow {
        Some(v) => std::env::set_var(crate::splitter::ALLOWED_AXIOMS_ENV, v),
        None => std::env::remove_var(crate::splitter::ALLOWED_AXIOMS_ENV),
    }
    assert!(
        strict_res.is_err(),
        "remote /check-shard must enforce caller's strict allowed_axioms policy"
    );

    let _ = fs::remove_dir_all(&dir_server);
    Ok(())
}

pub(crate) fn spawn_authed_test_server(dir_server: &Path, token: &str) -> Result<String> {
    let port = TcpListener::bind("127.0.0.1:0")?.local_addr()?.port();
    let (srv_dir, addr, tok) = (
        dir_server.to_path_buf(),
        format!("127.0.0.1:{}", port),
        token.to_string(),
    );
    let addr_clone = addr.clone();
    std::thread::spawn(move || {
        let _ = run_server_with_auth(Some(&srv_dir), &addr_clone, false, Some(&tok), false);
    });
    for _ in 0..20 {
        if std::net::TcpStream::connect(&addr).is_ok() {
            break;
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
    Ok(addr)
}

#[test]
fn test_check_shards_batch_http_offload() -> Result<()> {
    let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
    let dir_server =
        std::env::temp_dir().join(format!("turbo_lean_batch_shard_srv_{}", next_tmp_id()));
    let dir_client =
        std::env::temp_dir().join(format!("turbo_lean_batch_shard_cli_{}", next_tmp_id()));
    let _ = fs::remove_dir_all(&dir_server);
    let _ = fs::remove_dir_all(&dir_client);
    let _ = TurboStore::open(Some(&dir_server))?;
    let mut store_client = TurboStore::open(Some(&dir_client))?;

    let tok = "test-batch-shard-token";
    std::env::set_var("TURBO_LEAN_API_TOKEN", tok);
    let _clear = ScopedEnvClear(&["TURBO_LEAN_API_TOKEN"]);
    let endpoint = format!("http://{}", spawn_authed_test_server(&dir_server, tok)?);
    let mk_item = |k: &str, d: &str, p: &str, s: &str, pr: &str| CheckShardBatchItem {
        shard_key: k.into(),
        decl_name: d.into(),
        prefix_env_hash: p.into(),
        stmt_hash: s.into(),
        proof_hash: pr.into(),
        expected_kernel_type_hash: None,
    };
    let items = vec![
        mk_item("batch_shard_key_1", "batch_thm_1", "p1", "s1", "pr1"),
        mk_item("batch_shard_key_2", "batch_thm_2", "p2", "s2", "pr2"),
    ];
    let coalesced_src =
        "theorem batch_thm_1 : 2 + 2 = 4 := rfl\ntheorem batch_thm_2 : 3 + 3 = 6 := rfl\n";

    let resp1 = offload_check_shards_batch_http(
        &mut store_client,
        &endpoint,
        &items,
        coalesced_src,
        "trusted",
        "leanprover/lean4:v4.35.0",
        "",
        &[],
    )?;
    assert!(resp1.ok && resp1.verified_count == 2 && resp1.cache_hits == 0 && resp1.exit_code == 0);

    let both_keys = [
        "batch_shard_key_1".to_string(),
        "batch_shard_key_2".to_string(),
    ];
    assert!(
        store_client
            .batch_get_theorem_shards(&both_keys, "trusted")?
            .is_empty(),
        "raw unattested caller shard keys must never be published locally"
    );
    let attested_keys: Vec<String> = both_keys
        .iter()
        .map(|k| client_attested_receipt_key(k))
        .collect();
    let client1_hits = store_client.batch_get_theorem_shards(&attested_keys, "trusted")?;
    assert_eq!(client1_hits.len(), 2);
    for k in &attested_keys {
        let entries = store_client
            .get_cached_action_no_hit_bump(k, "trusted")?
            .expect("attested receipt entry");
        let raw = store_client
            .read_verified_blob(&entries[0].blob_hash)
            .expect("verified receipt blob");
        let val: serde_json::Value = serde_json::from_slice(&raw)?;
        assert!(val.get("prefix_env_hash").is_none());
        assert!(val.get("stmt_hash").is_none());
        assert!(val.get("proof_hash").is_none());
        assert!(val["kernel_type_hash"].as_str().is_some());
    }

    let dir_client2 =
        std::env::temp_dir().join(format!("turbo_lean_batch_shard_cli2_{}", next_tmp_id()));
    let _ = fs::remove_dir_all(&dir_client2);
    let mut store_client2 = TurboStore::open(Some(&dir_client2))?;
    let resp2 = offload_check_shards_batch_http(
        &mut store_client2,
        &endpoint,
        &items,
        coalesced_src,
        "trusted",
        "leanprover/lean4:v4.35.0",
        "",
        &[],
    )?;
    assert!(resp2.ok && resp2.verified_count == 0 && resp2.cache_hits == 2 && resp2.exit_code == 0);
    assert!(store_client2
        .batch_get_theorem_shards(&both_keys, "trusted")?
        .is_empty());
    assert_eq!(
        store_client2
            .batch_get_theorem_shards(&attested_keys, "trusted")?
            .len(),
        2
    );

    let dir_client3 =
        std::env::temp_dir().join(format!("turbo_lean_batch_shard_cli3_{}", next_tmp_id()));
    let _ = fs::remove_dir_all(&dir_client3);
    let mut store_client3 = TurboStore::open(Some(&dir_client3))?;
    let partial_items = vec![
        mk_item("batch_shard_key_1", "batch_thm_1", "p1", "s1", "pr1"),
        mk_item("batch_shard_key_3", "batch_thm_3", "p3", "s3", "pr3"),
    ];
    let partial_fast_src =
        "theorem batch_thm_1 : 2 + 2 = 4 := rfl\ntheorem batch_thm_3 : 4 + 4 = 8 := rfl\n";
    let resp3 = offload_check_shards_batch_http(
        &mut store_client3,
        &endpoint,
        &partial_items,
        partial_fast_src,
        "trusted",
        "leanprover/lean4:v4.35.0",
        "",
        &[],
    )?;
    assert!(resp3.ok && resp3.cache_hits == 1 && resp3.verified_count == 1);

    std::env::remove_var("TURBO_LEAN_API_TOKEN");
    for d in [&dir_server, &dir_client, &dir_client2, &dir_client3] {
        let _ = fs::remove_dir_all(d);
    }
    Ok(())
}

#[test]
fn test_remote_batch_and_single_shard_reject_unattested_or_mismatched_coordinator() -> Result<()> {
    let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
    let dir_server = std::env::temp_dir().join(format!("turbo_lean_att_srv_{}", next_tmp_id()));
    let dir_client = std::env::temp_dir().join(format!("turbo_lean_att_cli_{}", next_tmp_id()));
    let _ = fs::remove_dir_all(&dir_server);
    let _ = fs::remove_dir_all(&dir_client);
    let _ = TurboStore::open(Some(&dir_server))?;
    let mut store_client = TurboStore::open(Some(&dir_client))?;

    let tok = "test-att-batch-token";
    std::env::set_var("TURBO_LEAN_API_TOKEN", tok);
    let _clear = ScopedEnvClear(&["TURBO_LEAN_API_TOKEN"]);
    let endpoint = format!("http://{}", spawn_authed_test_server(&dir_server, tok)?);

    // 1) Mock an older coordinator that returns `ok: true` WITHOUT `verified_decl_types`.
    let fake_listener = std::net::TcpListener::bind("127.0.0.1:0")?;
    let fake_addr = fake_listener.local_addr()?;
    let fake_handle = std::thread::spawn(move || {
        use std::io::{Read, Write};
        for _ in 0..2 {
            if let Ok((mut sock, _)) = fake_listener.accept() {
                let mut buf = [0u8; 4096];
                let _ = sock.read(&mut buf);
                let body = r#"{"ok":true,"verified_count":1,"cache_hits":0,"elapsed_ms":1.0,"exit_code":0,"stdout":"","stderr":"","error":null}"#;
                let resp = format!(
                        "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{}",
                        body.len(),
                        body
                    );
                let _ = sock.write_all(resp.as_bytes());
            }
        }
    });
    let unattested_items = vec![CheckShardBatchItem {
        shard_key: "unattested_remote_key".into(),
        decl_name: "Ns.thm".into(),
        prefix_env_hash: "p".into(),
        stmt_hash: "s".into(),
        proof_hash: "pr".into(),
        expected_kernel_type_hash: Some("a".repeat(64)),
    }];
    let err = offload_check_shards_batch_http(
        &mut store_client,
        &format!("http://{fake_addr}"),
        &unattested_items,
        "namespace Ns\ntheorem thm : 2 + 2 = 4 := rfl\nend Ns\n",
        "trusted",
        include_str!("../../../../lean/lean-toolchain").trim(),
        "",
        &[],
    )
    .unwrap_err();
    assert!(
        format!("{err:#}").contains("did not attest expected kernel statement types"),
        "unexpected error: {err:#}"
    );
    assert!(
        store_client
            .batch_get_theorem_shards(
                &[
                    "unattested_remote_key".to_string(),
                    client_attested_receipt_key("unattested_remote_key"),
                ],
                "trusted"
            )?
            .is_empty(),
        "local CAS must not publish when remote coordinator omits verified_decl_types"
    );

    let unpinned_unattested_items = vec![CheckShardBatchItem {
        shard_key: "unattested_unpinned_key".into(),
        decl_name: "Ns.thm".into(),
        prefix_env_hash: "forged_prefix".into(),
        stmt_hash: "forged_stmt".into(),
        proof_hash: "forged_proof".into(),
        expected_kernel_type_hash: None,
    }];
    let unpinned_resp = offload_check_shards_batch_http(
        &mut store_client,
        &format!("http://{fake_addr}"),
        &unpinned_unattested_items,
        "namespace Ns\ntheorem thm : 2 + 2 = 4 := rfl\nend Ns\n",
        "trusted",
        include_str!("../../../../lean/lean-toolchain").trim(),
        "",
        &[],
    )?;
    let _ = fake_handle.join();
    assert!(unpinned_resp.ok);
    assert!(
        store_client
            .batch_get_theorem_shards(
                &[
                    "unattested_unpinned_key".to_string(),
                    client_attested_receipt_key("unattested_unpinned_key"),
                ],
                "trusted"
            )?
            .is_empty(),
        "unattested ok response without verified_decl_types must never cache caller hashes"
    );

    // 2) Real coordinator returns `verified_decl_types` for namespaced declarations on both cold verify and warm cache hit.
    let ns_src = "namespace Ns\ntheorem thm : 2 + 2 = 4 := rfl\nend Ns\n";
    let probe_items = vec![CheckShardBatchItem {
        shard_key: "real_ns_probe".into(),
        decl_name: "Ns.thm".into(),
        prefix_env_hash: "p".into(),
        stmt_hash: "s".into(),
        proof_hash: "pr".into(),
        expected_kernel_type_hash: None,
    }];
    let probe_resp = offload_check_shards_batch_http(
        &mut store_client,
        &endpoint,
        &probe_items,
        ns_src,
        "trusted",
        include_str!("../../../../lean/lean-toolchain").trim(),
        "",
        &[],
    )?;
    let real_kth = probe_resp
        .verified_decl_types
        .get("Ns.thm")
        .cloned()
        .expect("real coordinator reports verified_decl_types for Ns.thm");

    let attested_items = vec![CheckShardBatchItem {
        shard_key: "real_ns_attested".into(),
        decl_name: "Ns.thm".into(),
        prefix_env_hash: "p".into(),
        stmt_hash: "s".into(),
        proof_hash: "pr".into(),
        expected_kernel_type_hash: Some(real_kth.clone()),
    }];
    let cold_att = offload_check_shards_batch_http(
        &mut store_client,
        &endpoint,
        &attested_items,
        ns_src,
        "trusted",
        include_str!("../../../../lean/lean-toolchain").trim(),
        "",
        &[],
    )?;
    assert!(cold_att.ok && cold_att.verified_count == 1);
    assert!(store_client
        .batch_get_theorem_shards(&["real_ns_attested".to_string()], "trusted")?
        .is_empty());
    assert!(store_client.has_attested_decl_receipt(
        &client_attested_receipt_key("real_ns_attested"),
        "trusted",
        "Ns.thm",
        &real_kth
    ));

    let dir_client2 = std::env::temp_dir().join(format!("turbo_lean_att_cli2_{}", next_tmp_id()));
    let mut store_client2 = TurboStore::open(Some(&dir_client2))?;
    let warm_att = offload_check_shards_batch_http(
        &mut store_client2,
        &endpoint,
        &attested_items,
        ns_src,
        "trusted",
        include_str!("../../../../lean/lean-toolchain").trim(),
        "",
        &[],
    )?;
    assert!(warm_att.ok && warm_att.cache_hits == 1);
    assert_eq!(warm_att.verified_decl_types.get("Ns.thm"), Some(&real_kth));
    assert!(store_client2.has_attested_decl_receipt(
        &client_attested_receipt_key("real_ns_attested"),
        "trusted",
        "Ns.thm",
        &real_kth
    ));

    let mismatched_items = vec![CheckShardBatchItem {
        shard_key: "real_ns_mismatched".into(),
        decl_name: "Ns.thm".into(),
        prefix_env_hash: "p".into(),
        stmt_hash: "s".into(),
        proof_hash: "pr".into(),
        expected_kernel_type_hash: Some("0".repeat(64)),
    }];
    let mismatched_resp = offload_check_shards_batch_http(
        &mut store_client2,
        &endpoint,
        &mismatched_items,
        ns_src,
        "trusted",
        include_str!("../../../../lean/lean-toolchain").trim(),
        "",
        &[],
    )?;
    assert!(!mismatched_resp.ok);
    assert!(store_client2
        .batch_get_theorem_shards(
            &[
                "real_ns_mismatched".to_string(),
                client_attested_receipt_key("real_ns_mismatched"),
            ],
            "trusted"
        )?
        .is_empty());

    std::env::remove_var("TURBO_LEAN_API_TOKEN");
    for d in [&dir_server, &dir_client, &dir_client2] {
        let _ = fs::remove_dir_all(d);
    }
    Ok(())
}

#[test]
fn test_zygote_worker_in_memory_env_reuse() -> Result<()> {
    let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
    let dir_server = std::env::temp_dir().join(format!("turbo_lean_zygote_srv_{}", next_tmp_id()));
    let _ = fs::remove_dir_all(&dir_server);
    let iso_lp = dir_server.join("isolated_lean_path");
    fs::create_dir_all(&iso_lp)?;
    let iso_lp_str = iso_lp.to_string_lossy().to_string();
    let _ = TurboStore::open(Some(&dir_server))?;

    let endpoint = format!("http://{}/check-shard", spawn_test_server(&dir_server)?);
    let mk_req = |decl: &str, src: &str, stmt: &str, proof: &str| CheckShardHttpRequest {
        decl: decl.into(),
        shard_key: format!("shard_key_{}", decl),
        shard_source: src.into(),
        interface_hash: "iface_z".into(),
        prefix_env_hash: "prefix_z".into(),
        stmt_hash: stmt.into(),
        proof_hash: proof.into(),
        expected_kernel_type_hash: None,
        toolchain: "leanprover/lean4:v4.35.0".into(),
        lean_path: iso_lp_str.clone(),
        skip_cas_lock: false,
        allowed_axioms: None,
        lean_args: Vec::new(),
        targets: Vec::new(),
    };
    let post = |req: &CheckShardHttpRequest| -> Result<serde_json::Value> {
        Ok(serde_json::from_slice(&http_request(
            "POST",
            &endpoint,
            "application/json",
            &serde_json::to_vec(req)?,
        )?)?)
    };

    let resp1 = post(&mk_req(
        "zygote_thm_a",
        "import Init\ntheorem zygote_thm_a (a b : Nat) : a + b = b + a := by omega\n",
        "stmt_za",
        "proof_za",
    ))?;
    assert_eq!(
        (resp1["status"].as_str(), resp1["zygote_used"].as_bool()),
        (Some("remote_theorem_verified"), Some(true))
    );

    let resp2 = post(&mk_req(
        "zygote_thm_b",
        "import Init\ntheorem zygote_thm_b (x : Nat) : x + 0 = x := by omega\n",
        "stmt_zb",
        "proof_zb",
    ))?;
    assert_eq!(
        (
            resp2["status"].as_str(),
            resp2["zygote_used"].as_bool(),
            resp2["zygote_env_cache_hit"].as_bool(),
            resp2["zygote_import_us"].as_u64()
        ),
        (
            Some("remote_theorem_verified"),
            Some(true),
            Some(true),
            Some(0)
        )
    );

    assert!(http_request(
        "POST",
        &endpoint,
        "application/json",
        &serde_json::to_vec(&mk_req(
            "zygote_thm_bad",
            "import Init\ntheorem zygote_thm_bad : 1 = 2 := rfl\n",
            "stmt_zbad",
            "proof_zbad"
        ))?
    )
    .is_err());
    let _ = fs::remove_dir_all(&dir_server);
    Ok(())
}

#[test]
fn test_fastcheck_cold_dynamic_link_and_warm_cache_hit() -> Result<()> {
    let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
    let dir = std::env::temp_dir().join(format!(
        "turbo_lean_fc_cold_dyn_test_{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&dir);
    let store = TurboStore::open(Some(&dir))?;
    let req = FastCheckHttpRequest {
        filename: "FastCheck.lean".into(),
        source: "def dummyVal : UInt64 := 42\n".into(),
        gpu: false,
        precomputed_bin_key: String::new(),
        has_main: None,
        local_path: String::new(),
    };
    let res_cold = execute_fastcheck_payload(&store, &req)?;
    assert_eq!(
        (
            res_cold["status"].as_str(),
            res_cold["compile_cache_hit"].as_bool()
        ),
        (Some("ok"), Some(false))
    );
    assert!(res_cold["output"]
        .as_str()
        .unwrap_or("")
        .contains("Checked 1,000,000 256-bit states"));
    let res_warm = execute_fastcheck_payload(&store, &req)?;
    assert_eq!(
        (
            res_warm["status"].as_str(),
            res_warm["compile_cache_hit"].as_bool(),
            res_warm["binary_cache_key"].as_str()
        ),
        (
            Some("ok"),
            Some(true),
            res_cold["binary_cache_key"].as_str()
        )
    );
    let _ = fs::remove_dir_all(&dir);
    Ok(())
}

#[test]
fn test_local_daemon_request_rejects_named_sorry_target() -> Result<()> {
    // The local daemon helpers send `skip_cas_lock: true`; a named target's own `sorry` is
    // still rejected (P0-1), before any elaboration, and nothing is cached for it.
    let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
    let dir = std::env::temp_dir().join(format!("turbo_lean_daemon_sorry_{}", next_tmp_id()));
    let _ = fs::remove_dir_all(&dir);
    let mut store = TurboStore::open(Some(&dir))?;
    let req = CheckShardHttpRequest {
        decl: "bad".into(),
        shard_key: "shard_key_daemon_sorry".into(),
        shard_source: "theorem good : 1 + 1 = 2 := sorry\ntheorem bad : False := sorry\n".into(),
        interface_hash: String::new(),
        prefix_env_hash: String::new(),
        stmt_hash: String::new(),
        proof_hash: String::new(),
        expected_kernel_type_hash: None,
        toolchain: "leanprover/lean4:v4.35.0".into(),
        lean_path: String::new(),
        skip_cas_lock: true,
        allowed_axioms: None,
        lean_args: Vec::new(),
        targets: Vec::new(),
    };
    let err = execute_check_shard_payload(&mut store, &req).unwrap_err();
    assert!(
        err.to_string().contains("Soundness hygiene violation"),
        "{err}"
    );
    assert!(!store.has_cached_action_readonly(&req.shard_key, "trusted")?);
    let _ = fs::remove_dir_all(&dir);
    Ok(())
}

#[test]
fn test_zygote_parallel_cross_file_shard_eval() -> Result<()> {
    let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
    let dir = std::env::temp_dir().join(format!("turbo_lean_zygote_par_cross_{}", next_tmp_id()));
    let _ = fs::remove_dir_all(&dir);
    let iso_lp = dir.join("isolated_lean_path");
    fs::create_dir_all(&iso_lp)?;
    let mut store = TurboStore::open(Some(&dir))?;
    let req = CheckShardHttpRequest {
            decl: "__batch__".into(),
            shard_key: "shard_key_par_cross_1".into(),
            shard_source: "import Init\n-- namespace _TurboCrossFileShard_0\n-- end _TurboCrossFileShard_0\ntheorem par1 (a b : Nat) : a + b = b + a := Nat.add_comm a b\n-- namespace _TurboCrossFileShard_1\n-- end _TurboCrossFileShard_1\ntheorem par2 (x : Nat) : x + 0 = x := rfl\n".into(),
            interface_hash: String::new(),
            prefix_env_hash: String::new(),
            stmt_hash: String::new(),
            proof_hash: String::new(),
            expected_kernel_type_hash: None,
            toolchain: "leanprover/lean4:v4.35.0".into(),
            lean_path: iso_lp.to_string_lossy().to_string(),
            skip_cas_lock: true,
            allowed_axioms: None,
            lean_args: Vec::new(),
            targets: Vec::new(),
        };
    let res1 = execute_check_shard_payload(&mut store, &req)?;
    assert_eq!(
        (res1["status"].as_str(), res1["zygote_used"].as_bool()),
        (Some("remote_theorem_verified"), Some(true))
    );
    let res2 = execute_check_shard_payload(&mut store, &req)?;
    assert_eq!(res2["zygote_env_cache_hit"].as_bool(), Some(true));
    let _ = fs::remove_dir_all(&dir);
    Ok(())
}

#[test]
fn test_server_auth_local_path_traversal_and_eval_env_hardening() -> Result<()> {
    let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
    let dir_server = std::env::temp_dir().join(format!("turbo_lean_sec_srv_{}", next_tmp_id()));
    let _ = fs::remove_dir_all(&dir_server);
    let _ = TurboStore::open(Some(&dir_server))?;
    let tok = "sec-test-token-20261029";
    let addr = spawn_authed_test_server(&dir_server, tok)?;
    let base = format!("http://{}", addr);

    // 1. Unauthenticated access to protected routes is rejected with HTTP 401
    let unauth_err = http_request_with_timeout_and_token(
        "POST",
        &format!("{}/eval", base),
        "application/json",
        b"{\"code\":\"#eval 1\"}",
        Some(2_000),
        None,
        || {},
    )
    .unwrap_err()
    .to_string();
    assert!(
        unauth_err.contains("401"),
        "expected 401, got: {}",
        unauth_err
    );

    // 2. Non-loopback bind without token fails closed before binding
    let non_loopback_res = run_server_with_auth(Some(&dir_server), "0.0.0.0:0", false, None, false);
    assert!(non_loopback_res.is_err());

    // 3. `/fast-check` rejects `local_path` (no arbitrary server file read) and `precomputed_bin_key` traversal
    let fc_local_err = http_request_with_timeout_and_token(
        "POST",
        &format!("{}/fast-check", base),
        "application/json",
        b"{\"local_path\":\"/etc/passwd\"}",
        Some(2_000),
        Some(tok),
        || {},
    )
    .unwrap_err()
    .to_string();
    assert!(
        fc_local_err.contains("400") && fc_local_err.contains("local_path"),
        "expected 400 on local_path, got: {}",
        fc_local_err
    );

    let fc_trav_err = http_request_with_timeout_and_token(
        "POST",
        &format!("{}/fast-check", base),
        "application/json",
        b"{\"source\":\"def x := 1\",\"precomputed_bin_key\":\"../../../../bin/sh\"}",
        Some(2_000),
        Some(tok),
        || {},
    )
    .unwrap_err()
    .to_string();
    assert!(
        fc_trav_err.contains("400"),
        "expected 400 on precomputed_bin_key traversal, got: {}",
        fc_trav_err
    );

    // 4. `/eval` rejects disallowed environment variables (`LD_PRELOAD`, `PATH`, `LAKE`)
    let eval_env_err = http_request_with_timeout_and_token(
        "POST",
        &format!("{}/eval", base),
        "application/json",
        b"{\"code\":\"#eval 1\",\"env_vars\":{\"LD_PRELOAD\":\"/tmp/evil.so\"}}",
        Some(2_000),
        Some(tok),
        || {},
    )
    .unwrap_err()
    .to_string();
    assert!(
        eval_env_err.contains("400") && eval_env_err.contains("LD_PRELOAD"),
        "expected 400 on disallowed env_vars, got: {}",
        eval_env_err
    );

    // Warm the empty-option eval path before trying arguments that filtering used to erase.
    let eval_body = serde_json::json!({"source": "#eval 17305\n"});
    for _ in 0..2 {
        let reply: serde_json::Value =
            serde_json::from_slice(&http_request_with_timeout_and_token(
                "POST",
                &format!("{}/eval", base),
                "application/json",
                &serde_json::to_vec(&eval_body)?,
                Some(30_000),
                Some(tok),
                || {},
            )?)?;
        assert_eq!(reply["ok"], true, "{reply}");
    }
    for invalid in ["--plugin=bad.so", "--json", "-q", " -DautoImplicit=false "] {
        let body = serde_json::json!({"source": "#eval 17305\n", "lean_args": [invalid]});
        let err = http_request_with_timeout_and_token(
            "POST",
            &format!("{}/eval", base),
            "application/json",
            &serde_json::to_vec(&body)?,
            Some(2_000),
            Some(tok),
            || {},
        )
        .unwrap_err()
        .to_string();
        assert!(
            err.contains("400") && err.contains("Unsupported effective Lean compiler flag"),
            "expected rejection before eval cache access: {err}"
        );
    }

    // 5. SHA-256 verification fails closed on mismatch
    let sha_err = http_request_full(
        "GET",
        &format!("{}/export", base),
        "application/octet-stream",
        &[],
        Some(2_000),
        Some(tok),
        Some("0000000000000000000000000000000000000000000000000000000000000000"),
        || {},
    )
    .unwrap_err()
    .to_string();
    assert!(
        sha_err.contains("SHA-256 integrity mismatch"),
        "got: {}",
        sha_err
    );

    let dir_empty_pull =
        std::env::temp_dir().join(format!("turbo_lean_empty_pull_sha_{}", next_tmp_id()));
    let _ = fs::remove_dir_all(&dir_empty_pull);
    let mut store_empty_pull = TurboStore::open(Some(&dir_empty_pull))?;
    std::env::set_var("TURBO_LEAN_API_TOKEN", tok);
    let _tok_clear = ScopedEnvClear(&["TURBO_LEAN_API_TOKEN"]);
    let init_pull_err = sync_pull_http_with_policy(
        &mut store_empty_pull,
        &base,
        true,
        None,
        None,
        false,
        Some("0000000000000000000000000000000000000000000000000000000000000000"),
    )
    .unwrap_err()
    .to_string();
    assert!(
        init_pull_err.contains("SHA-256 integrity mismatch"),
        "initial empty-store pull must propagate SHA-256 mismatch, got: {}",
        init_pull_err
    );

    let _ = fs::remove_dir_all(&dir_empty_pull);
    let _ = fs::remove_dir_all(&dir_server);
    Ok(())
}

#[test]
fn test_ed25519_signed_pack_trust_domain_isolation_and_non_downgrade() -> Result<()> {
    let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
    let dir_src = std::env::temp_dir().join(format!("turbo_lean_pack_sig_src_{}", next_tmp_id()));
    let dir_dst = std::env::temp_dir().join(format!("turbo_lean_pack_sig_dst_{}", next_tmp_id()));
    let _ = fs::remove_dir_all(&dir_src);
    let _ = fs::remove_dir_all(&dir_dst);
    let mut store_src = TurboStore::open(Some(&dir_src))?;
    let mut store_dst = TurboStore::open(Some(&dir_dst))?;

    let payload = b"verified-shard-payload";
    let bh = store_src.store_immutable_blob(payload, "expr_shard", "trusted", 0)?;
    if let SingleflightOutcome::Leader(lease) =
        store_src.acquire_singleflight("sig-act-1", "v4.35.0", "theorem_shard", "trusted")?
    {
        store_src.publish_action(
            &lease,
            &[BlobEntry {
                blob_hash: bh.clone(),
                kind: "expr_shard".into(),
                size_bytes: payload.len() as u64,
                rel_path: "thm:sig_decl".into(),
            }],
            1,
            0,
            0,
            "trusted",
        )?;
    }

    // Unattested pack defaults to `untrusted` and is refused when `trusted` is requested without override
    let unsigned_pack = dir_src.join("unsigned.tlpack");
    export_pack_with_signing_key(&store_src, &unsigned_pack, true, None)?;
    assert!(
        import_pack_with_policy(&mut store_dst, &unsigned_pack, Some("trusted"), None, false)
            .is_err()
    );
    import_pack_with_policy(&mut store_dst, &unsigned_pack, None, None, false)?;
    assert!(store_dst
        .batch_get_theorem_shards(&["sig-act-1".into()], "trusted")?
        .is_empty());
    assert_eq!(
        store_dst
            .batch_get_theorem_shards(&["sig-act-1".into()], "untrusted")?
            .len(),
        1
    );

    // Signed pack with Ed25519 key promotes to `trusted`, and subsequent untrusted import cannot downgrade it
    let sk_hex = "1111111111111111111111111111111111111111111111111111111111111111";
    let pk_hex = crate::receipt::ed25519_verifying_key_hex(&[0x11u8; 32]);
    let wrong_pk_hex = crate::receipt::ed25519_verifying_key_hex(&[0x22u8; 32]);
    let signed_pack = dir_src.join("signed.tlpack");
    export_pack_with_signing_key(&store_src, &signed_pack, true, Some(sk_hex))?;

    assert!(import_pack_with_policy(
        &mut store_dst,
        &signed_pack,
        Some("trusted"),
        Some(&wrong_pk_hex),
        false
    )
    .is_err());
    import_pack_with_policy(
        &mut store_dst,
        &signed_pack,
        Some("trusted"),
        Some(&pk_hex),
        false,
    )?;
    assert_eq!(
        store_dst
            .batch_get_theorem_shards(&["sig-act-1".into()], "trusted")?
            .len(),
        1
    );
    // Re-importing unsigned pack into `untrusted` must NOT downgrade existing `trusted` action/blob
    import_pack_with_policy(
        &mut store_dst,
        &unsigned_pack,
        Some("untrusted"),
        None,
        false,
    )?;
    assert_eq!(
        store_dst
            .batch_get_theorem_shards(&["sig-act-1".into()], "trusted")?
            .len(),
        1
    );

    let _ = fs::remove_dir_all(&dir_src);
    let _ = fs::remove_dir_all(&dir_dst);
    Ok(())
}

#[test]
fn test_configured_pubkey_honored_over_allow_unattested_and_trusted_promotion_replaces_outputs(
) -> Result<()> {
    let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
    let dir_untrusted_src =
        std::env::temp_dir().join(format!("turbo_lean_pack_ut_src_{}", next_tmp_id()));
    let dir_trusted_src =
        std::env::temp_dir().join(format!("turbo_lean_pack_tr_src_{}", next_tmp_id()));
    let dir_dst = std::env::temp_dir().join(format!("turbo_lean_pack_promo_dst_{}", next_tmp_id()));
    let dir_wt = std::env::temp_dir().join(format!("turbo_lean_pack_promo_wt_{}", next_tmp_id()));
    let _ = fs::remove_dir_all(&dir_untrusted_src);
    let _ = fs::remove_dir_all(&dir_trusted_src);
    let _ = fs::remove_dir_all(&dir_dst);
    let _ = fs::remove_dir_all(&dir_wt);
    fs::create_dir_all(&dir_wt)?;

    let mut store_ut = TurboStore::open(Some(&dir_untrusted_src))?;
    let mut store_tr = TurboStore::open(Some(&dir_trusted_src))?;
    let mut store_dst = TurboStore::open(Some(&dir_dst))?;

    let good_payload = b"legit-olean-bytes";
    let evil_payload = b"injected-untrusted-extra-olean";
    let good_bh = store_ut.store_immutable_blob(good_payload, "olean", "trusted", 0)?;
    let evil_bh = store_ut.store_immutable_blob(evil_payload, "olean", "trusted", 0)?;
    if let SingleflightOutcome::Leader(lease) =
        store_ut.acquire_singleflight("mod-act-promo", "v4.35.0", "module_unit", "trusted")?
    {
        store_ut.publish_action(
            &lease,
            &[
                BlobEntry {
                    blob_hash: good_bh.clone(),
                    kind: "olean".into(),
                    size_bytes: good_payload.len() as u64,
                    rel_path: "build/lib/lean/Good.olean".into(),
                },
                BlobEntry {
                    blob_hash: evil_bh.clone(),
                    kind: "olean".into(),
                    size_bytes: evil_payload.len() as u64,
                    rel_path: "build/lib/lean/EvilInjected.olean".into(),
                },
            ],
            1,
            0,
            0,
            "trusted",
        )?;
    }
    let unsigned_extra_pack = dir_untrusted_src.join("unsigned_extra.tlpack");
    export_pack_with_signing_key(&store_ut, &unsigned_extra_pack, true, None)?;

    let good_bh_tr = store_tr.store_immutable_blob(good_payload, "olean", "trusted", 0)?;
    assert_eq!(good_bh, good_bh_tr);
    if let SingleflightOutcome::Leader(lease) =
        store_tr.acquire_singleflight("mod-act-promo", "v4.35.0", "module_unit", "trusted")?
    {
        store_tr.publish_action(
            &lease,
            &[BlobEntry {
                blob_hash: good_bh_tr.clone(),
                kind: "olean".into(),
                size_bytes: good_payload.len() as u64,
                rel_path: "build/lib/lean/Good.olean".into(),
            }],
            1,
            0,
            0,
            "trusted",
        )?;
    }
    let sk_hex = "3333333333333333333333333333333333333333333333333333333333333333";
    let pk_hex = crate::receipt::ed25519_verifying_key_hex(&[0x33u8; 32]);
    let wrong_pk_hex = crate::receipt::ed25519_verifying_key_hex(&[0x44u8; 32]);
    let signed_clean_pack = dir_trusted_src.join("signed_clean.tlpack");
    export_pack_with_signing_key(&store_tr, &signed_clean_pack, true, Some(sk_hex))?;

    // 1. When a trusted pubkey is configured, `--allow-unattested-trusted` with `requested_domain = None`
    //    MUST NOT admit an unsigned pack into `trusted` (quarantines to `untrusted`), and MUST fail closed
    //    when `requested_domain = Some("trusted")` or when signature verification fails.
    assert!(import_pack_with_policy(
        &mut store_dst,
        &unsigned_extra_pack,
        Some("trusted"),
        Some(&pk_hex),
        true,
    )
    .is_err());
    assert!(import_pack_with_policy(
        &mut store_dst,
        &signed_clean_pack,
        None,
        Some(&wrong_pk_hex),
        true,
    )
    .is_err());
    import_pack_with_policy(
        &mut store_dst,
        &unsigned_extra_pack,
        None,
        Some(&pk_hex),
        true,
    )?;
    assert!(store_dst
        .get_cached_action("mod-act-promo", "trusted")?
        .is_none());
    let untrusted_outs = store_dst
        .get_cached_action("mod-act-promo", "untrusted")?
        .expect("quarantined in untrusted");
    assert_eq!(untrusted_outs.len(), 2);

    // 2. Importing a legitimately signed pack for `mod-act-promo` promotes it to `trusted` AND atomically
    //    replaces `action_outputs`, purging `EvilInjected.olean` so it is never returned or materialized.
    import_pack_with_policy(
        &mut store_dst,
        &signed_clean_pack,
        None,
        Some(&pk_hex),
        true,
    )?;
    let trusted_outs = store_dst
        .get_cached_action("mod-act-promo", "trusted")?
        .expect("promoted to trusted");
    assert_eq!(trusted_outs.len(), 1);
    assert_eq!(trusted_outs[0].rel_path, "build/lib/lean/Good.olean");
    assert_eq!(trusted_outs[0].blob_hash, good_bh);

    store_dst.materialize_into_worktree(&dir_wt, "promo-test", &trusted_outs)?;
    assert!(dir_wt.join("build/lib/lean/Good.olean").exists());
    assert!(!dir_wt.join("build/lib/lean/EvilInjected.olean").exists());

    // 3. Atomic single-file deferred pack record (`TLDP\x00\x00\x00\x05` + domain byte + epoch + V3 header)
    //    preserves `untrusted` across concurrent `TurboStore::open` calls and rejects unbound header-only records.
    let dir_cold = std::env::temp_dir().join(format!("turbo_lean_pack_cold_def_{}", next_tmp_id()));
    let _ = fs::remove_dir_all(&dir_cold);
    fs::create_dir_all(&dir_cold)?;
    let (_, _, raw_hdr) = read_pack_header_from_file(&unsigned_extra_pack).unwrap();
    let mut raw_v3 = Vec::with_capacity(16 + raw_hdr.len());
    raw_v3.extend_from_slice(b"TLPK\x00\x00\x00\x03");
    raw_v3.extend_from_slice(&(raw_hdr.len() as u64).to_le_bytes());
    raw_v3.extend_from_slice(&raw_hdr);
    assert!(
        decode_deferred_pack_record(&raw_v3).is_none(),
        "unbound legacy V3 deferred record must be rejected"
    );
    let bound_v5 =
        encode_deferred_pack_record_with_epoch("untrusted", &raw_v3, crate::TURBO_LEAN_BUILD_EPOCH);
    assert_eq!(
        decode_deferred_pack_record(&bound_v5).map(|(td, _)| td),
        Some("untrusted")
    );
    assert!(try_stateless_cold_import_with_domain(
        &dir_cold,
        &unsigned_extra_pack,
        None,
        Some(&pk_hex),
        true,
    )
    .is_some());
    let c1 = dir_cold.clone();
    let c2 = dir_cold.clone();
    let h1 = std::thread::spawn(move || TurboStore::open(Some(&c1)));
    let h2 = std::thread::spawn(move || TurboStore::open(Some(&c2)));
    let s1 = h1.join().unwrap()?;
    let s2 = h2.join().unwrap()?;
    assert!(s1.get_cached_action("mod-act-promo", "trusted")?.is_none());
    assert!(s2.get_cached_action("mod-act-promo", "trusted")?.is_none());
    assert!(s1
        .get_cached_action("mod-act-promo", "untrusted")?
        .is_some());
    assert!(s2
        .get_cached_action("mod-act-promo", "untrusted")?
        .is_some());

    // 4. Plain HTTP `X-Turbo-Pack-Sha256` response header mismatch fails closed even with `expected_sha256 = None`
    let bad_sha_listener = TcpListener::bind("127.0.0.1:0")?;
    let bad_sha_addr = bad_sha_listener.local_addr()?;
    std::thread::spawn(move || {
        if let Ok((mut sock, _)) = bad_sha_listener.accept() {
            let mut rbuf = [0u8; 512];
            let _ = sock.read(&mut rbuf);
            let resp = b"HTTP/1.1 200 OK\r\nContent-Length: 4\r\nX-Turbo-Pack-Sha256: ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff\r\n\r\ntest";
            let _ = sock.write_all(resp);
        }
    });
    let hdr_sha_err = http_request_full(
        "GET",
        &format!("http://{}/export", bad_sha_addr),
        "application/octet-stream",
        &[],
        Some(2_000),
        None,
        None,
        || {},
    )
    .unwrap_err()
    .to_string();
    assert!(
        hdr_sha_err.contains("SHA-256 integrity mismatch"),
        "expected header SHA-256 mismatch error, got: {}",
        hdr_sha_err
    );

    // 5. Daemon mode (`TURBO_LEAN_DAEMON=1`) honors `TURBO_LEAN_DAEMON_TOKEN` ahead of inherited `TURBO_LEAN_API_TOKEN`
    assert_eq!(
        crate::server::resolve_server_auth_token(
            None,
            true,
            Some("remote-coordinator-token"),
            Some("local-daemon-token-xyz"),
        ),
        Some("local-daemon-token-xyz".to_string())
    );
    assert_eq!(
        crate::server::resolve_server_auth_token(
            None,
            false,
            Some("remote-coordinator-token"),
            Some("local-daemon-token-xyz"),
        ),
        Some("remote-coordinator-token".to_string())
    );
    assert_eq!(
        crate::server::resolve_server_auth_token(
            Some("explicit-cli-token"),
            true,
            Some("remote-coordinator-token"),
            Some("local-daemon-token-xyz"),
        ),
        Some("explicit-cli-token".to_string())
    );

    let _ = fs::remove_dir_all(&dir_cold);
    let _ = fs::remove_dir_all(&dir_untrusted_src);
    let _ = fs::remove_dir_all(&dir_trusted_src);
    let _ = fs::remove_dir_all(&dir_dst);
    let _ = fs::remove_dir_all(&dir_wt);
    Ok(())
}

#[test]
fn test_deferred_pack_spool_multi_pack_crash_claim_and_failed_replay_preservation() -> Result<()> {
    let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
    let root_a = std::env::temp_dir().join(format!("turbo_lean_def_src_a_{}", next_tmp_id()));
    let root_b = std::env::temp_dir().join(format!("turbo_lean_def_src_b_{}", next_tmp_id()));
    let root_dst = std::env::temp_dir().join(format!("turbo_lean_def_spool_dst_{}", next_tmp_id()));
    let _ = fs::remove_dir_all(&root_a);
    let _ = fs::remove_dir_all(&root_b);
    let _ = fs::remove_dir_all(&root_dst);
    fs::create_dir_all(&root_dst)?;

    let mut store_a = TurboStore::open(Some(&root_a))?;
    let mut store_b = TurboStore::open(Some(&root_b))?;
    let pay_a = b"deferred-pack-payload-alpha";
    let pay_b = b"deferred-pack-payload-bravo";
    let bh_a = store_a.store_immutable_blob(pay_a, "olean", "trusted", 0)?;
    let bh_b = store_b.store_immutable_blob(pay_b, "olean", "trusted", 0)?;
    if let SingleflightOutcome::Leader(l) =
        store_a.acquire_singleflight("def-act-alpha", "v4.35.0", "module_unit", "trusted")?
    {
        store_a.publish_action(
            &l,
            &[BlobEntry {
                blob_hash: bh_a.clone(),
                kind: "olean".into(),
                size_bytes: pay_a.len() as u64,
                rel_path: "build/lib/lean/Alpha.olean".into(),
            }],
            1,
            0,
            0,
            "trusted",
        )?;
    }
    if let SingleflightOutcome::Leader(l) =
        store_b.acquire_singleflight("def-act-bravo", "v4.35.0", "module_unit", "trusted")?
    {
        store_b.publish_action(
            &l,
            &[BlobEntry {
                blob_hash: bh_b.clone(),
                kind: "olean".into(),
                size_bytes: pay_b.len() as u64,
                rel_path: "build/lib/lean/Bravo.olean".into(),
            }],
            1,
            0,
            0,
            "trusted",
        )?;
    }
    let pack_a = root_a.join("alpha.tlpack");
    let pack_b = root_b.join("bravo.tlpack");
    export_pack_with_signing_key(&store_a, &pack_a, true, None)?;
    export_pack_with_signing_key(&store_b, &pack_b, true, None)?;

    // 1. Multiple sequential cold imports before any `TurboStore::open` must preserve BOTH
    //    spooled records without overwriting the earlier record.
    assert!(
        try_stateless_cold_import_with_domain(&root_dst, &pack_a, Some("trusted"), None, true)
            .is_some()
    );
    assert!(
        try_stateless_cold_import_with_domain(&root_dst, &pack_b, Some("trusted"), None, true)
            .is_some()
    );
    assert_eq!(
        list_pending_deferred_pack_files(&root_dst.join("locks"))?.len(),
        2
    );

    let opened = TurboStore::open(Some(&root_dst))?;
    assert!(opened
        .get_cached_action("def-act-alpha", "trusted")?
        .is_some());
    assert!(opened
        .get_cached_action("def-act-bravo", "trusted")?
        .is_some());
    assert!(list_pending_deferred_pack_files(&root_dst.join("locks"))?.is_empty());
    drop(opened);

    // 2. Crash recovery + failed-import preservation:
    //    - Simulate an orphaned `deferred_pack_v3.claim.<pid>.<id>` whose blob is missing on
    //      disk AND absent from shared CAS (so replay fails), alongside a newer valid
    //      `deferred_pack_v4.*.bin` record.
    //    - Replay must return `Err`, keep BOTH the failed `.claim.` file and the newer `.v4.`
    //      spool file intact (never clobbering the newer record), and once the missing blob is
    //      restored on disk, a subsequent `TurboStore::open` must recover BOTH records cleanly.
    let root_crash = std::env::temp_dir().join(format!("turbo_lean_def_crash_{}", next_tmp_id()));
    let _ = fs::remove_dir_all(&root_crash);
    fs::create_dir_all(root_crash.join("locks"))?;

    let missing_payload = b"transiently-missing-claim-blob-bytes";
    let missing_bh = blake3::hash(missing_payload).to_hex().to_string();
    let claim_manifest = PackManifest {
        format_version: 2,
        host_arch: std::env::consts::ARCH.into(),
        created_at: 1,
        ed25519_pubkey: None,
        ed25519_signature: None,
        replayed_oleans: Vec::new(),
        blobs: vec![PackedBlob {
            blob_hash: missing_bh.clone(),
            kind: "olean".into(),
            size_bytes: missing_payload.len() as u64,
            portable: true,
            data_hex_or_base64: Vec::new(),
        }],
        actions: vec![ActionRecord {
            action_key: "def-act-crashed-claim".into(),
            toolchain_githash: "v4.35.0".into(),
            kind: "module_unit".into(),
            status: "completed".into(),
            fencing_token: 1,
            output_manifest_hash: "mhash".into(),
            duration_ms: 1,
            peak_pss_bytes: 0,
            heartbeats: 0,
            trust_domain: "trusted".into(),
            outputs: vec![BlobEntry {
                blob_hash: missing_bh.clone(),
                kind: "olean".into(),
                size_bytes: missing_payload.len() as u64,
                rel_path: "build/lib/lean/Claim.olean".into(),
            }],
        }],
    };
    let claim_hdr = serde_json::to_vec(&claim_manifest)?;
    let mut claim_v3 = Vec::new();
    claim_v3.extend_from_slice(b"TLPK\x00\x00\x00\x03");
    claim_v3.extend_from_slice(&(claim_hdr.len() as u64).to_le_bytes());
    claim_v3.extend_from_slice(&claim_hdr);
    let claim_v5 =
        encode_deferred_pack_record_with_epoch("trusted", &claim_v3, crate::TURBO_LEAN_BUILD_EPOCH);
    let orphan_claim_path = root_crash
        .join("locks")
        .join("deferred_pack_v3.claim.999999.1");
    fs::write(&orphan_claim_path, &claim_v5)?;

    // Stage a newer valid pack (`pack_b`) while the crashed `.claim.` file is present.
    assert!(try_stateless_cold_import_with_domain(
        &root_crash,
        &pack_b,
        Some("trusted"),
        None,
        true
    )
    .is_some());
    assert_eq!(
        list_pending_deferred_pack_files(&root_crash.join("locks"))?.len(),
        2
    );

    // Opening now fails because `missing_bh` is neither in local `blobs/` nor in shared CAS.
    assert!(TurboStore::open(Some(&root_crash)).is_err());
    // Crucially, NEITHER the `.claim.` record NOR the newer `deferred_pack_v4.*` record was lost!
    assert!(orphan_claim_path.exists());
    assert_eq!(
        list_pending_deferred_pack_files(&root_crash.join("locks"))?.len(),
        2
    );

    // Restore the missing blob in local `blobs/` and re-open: both records replay & clean up.
    let restored_blob_path = root_crash
        .join("blobs")
        .join(&missing_bh[..2])
        .join(&missing_bh);
    crate::db::write_blob_atomic(
        &root_crash,
        &restored_blob_path,
        &missing_bh,
        missing_payload,
        false,
    )?;
    let recovered = TurboStore::open(Some(&root_crash))?;
    assert!(recovered
        .get_cached_action("def-act-crashed-claim", "trusted")?
        .is_some());
    assert!(recovered
        .get_cached_action("def-act-bravo", "trusted")?
        .is_some());
    assert!(list_pending_deferred_pack_files(&root_crash.join("locks"))?.is_empty());
    drop(recovered);

    // 3. Concurrent `TurboStore::open` deferred-pack replay vs `run_gc` + `stage_deferred_pack_record`
    //    must follow uniform lock order (`gc_publish.lock` -> `deferred_pack.lock`) without deadlocking,
    //    and cold stateless import into a previously nonexistent store directory must succeed cleanly.
    let root_nonexistent = root_dst
        .join("nonexistent_parent")
        .join("cold_target_store");
    assert!(!root_nonexistent.exists());
    assert!(try_stateless_cold_import_with_domain(
        &root_nonexistent,
        &pack_a,
        Some("trusted"),
        None,
        true
    )
    .is_some());
    let mut gc_peer = TurboStore::open(Some(&root_nonexistent))?;
    assert!(gc_peer
        .get_cached_action("def-act-alpha", "trusted")?
        .is_some());

    let (_, _, hdr_b) = read_pack_header_from_file(&pack_b).unwrap();
    let mut v3_b = Vec::with_capacity(16 + hdr_b.len());
    v3_b.extend_from_slice(b"TLPK\x00\x00\x00\x03");
    v3_b.extend_from_slice(&(hdr_b.len() as u64).to_le_bytes());
    v3_b.extend_from_slice(&hdr_b);

    for _ in 0..8 {
        assert!(stage_deferred_pack_record(
            &root_nonexistent,
            "trusted",
            &v3_b
        ));
        let r_open = root_nonexistent.clone();
        let h_open = std::thread::spawn(move || TurboStore::open(Some(&r_open)));
        let _ = gc_peer.run_gc(u64::MAX, 7 * 86400, true)?;
        let s_open = h_open
            .join()
            .expect("open replay thread must not panic/deadlock")?;
        assert!(s_open
            .get_cached_action("def-act-bravo", "trusted")?
            .is_some());
    }
    drop(gc_peer);

    // 4. SQLite durability handoff ordering & fail-closed spool preservation:
    //    - During cold-import replay, `last_import_stamp` must stay absent while the deferred
    //      spool is still pending so `try_stateless_warm_import_with_domain` never short-circuits
    //      ahead of SQLite replay.
    //    - If the SQLite durability barrier (`file:state.db`) fails, `TurboStore::open` must fail
    //      closed, preserve the pending deferred spool file, and leave `last_import_stamp` absent.
    //    - When the barrier succeeds, `file:state.db` (and `file:state.db-wal` when present)
    //      must be synced BEFORE `.last_import_stamp.*` / `dir:locks` retire the spool.
    let root_handoff =
        std::env::temp_dir().join(format!("turbo_lean_def_handoff_{}", next_tmp_id()));
    let _ = fs::remove_dir_all(&root_handoff);
    assert!(try_stateless_cold_import_with_domain(
        &root_handoff,
        &pack_a,
        Some("trusted"),
        None,
        true
    )
    .is_some());
    assert!(
        !root_handoff
            .join("locks")
            .join("last_import_stamp")
            .exists(),
        "cold stateless import must not publish last_import_stamp before SQLite replay"
    );
    assert!(try_stateless_warm_import_with_domain(
        &root_handoff,
        &pack_a,
        Some("trusted"),
        None,
        true
    )
    .is_none());

    let fault_log = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
    crate::db::set_durability_recorder_with_fault(fault_log.clone(), Some("file:state.db"));
    let fault_open = TurboStore::open(Some(&root_handoff));
    crate::db::clear_durability_recorder();
    assert!(
        fault_open.is_err(),
        "SQLite durability barrier failure must abort deferred-pack handoff"
    );
    assert_eq!(
        list_pending_deferred_pack_files(&root_handoff.join("locks"))?.len(),
        1,
        "deferred spool must remain intact when SQLite durability barrier fails"
    );
    assert!(
        !root_handoff
            .join("locks")
            .join("last_import_stamp")
            .exists(),
        "last_import_stamp must not be published when SQLite durability barrier fails"
    );
    assert!(try_stateless_warm_import_with_domain(
        &root_handoff,
        &pack_a,
        Some("trusted"),
        None,
        true
    )
    .is_none());

    // Clear any uncommitted/pre-barrier SQLite state as in a post-crash reboot, then record
    // successful barrier ordering across deferred replay -> stamp -> spool removal.
    let _ = fs::remove_file(root_handoff.join("state.db"));
    let _ = fs::remove_file(root_handoff.join("state.db-wal"));
    let _ = fs::remove_file(root_handoff.join("state.db-shm"));
    let ok_log = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
    crate::db::set_durability_recorder(ok_log.clone());
    let handoff_store = TurboStore::open(Some(&root_handoff))?;
    crate::db::clear_durability_recorder();
    let evs = std::mem::take(&mut *ok_log.lock().unwrap());
    let db_sync_pos = evs
        .iter()
        .position(|s| s == "file:state.db")
        .expect("SQLite state.db barrier recorded before stamp/spool retirement");
    let stamp_sync_pos = evs
        .iter()
        .position(|s| s.starts_with("file:.last_import_stamp."))
        .expect("last_import_stamp barrier recorded");
    let final_locks_sync_pos = evs
        .iter()
        .rposition(|s| s == "dir:locks")
        .expect("locks directory synced after spool removal");
    assert!(
        db_sync_pos < stamp_sync_pos && stamp_sync_pos < final_locks_sync_pos,
        "expected file:state.db -> file:.last_import_stamp.* -> dir:locks ordering, got {evs:?}"
    );
    if let Some(wal_pos) = evs.iter().position(|s| s == "file:state.db-wal") {
        assert!(
            wal_pos < stamp_sync_pos,
            "state.db-wal barrier must precede last_import_stamp: {evs:?}"
        );
    }
    assert!(list_pending_deferred_pack_files(&root_handoff.join("locks"))?.is_empty());
    assert!(handoff_store
        .get_cached_action("def-act-alpha", "trusted")?
        .is_some());
    drop(handoff_store);
    assert_eq!(
        try_stateless_warm_import_with_domain(&root_handoff, &pack_a, Some("trusted"), None, true),
        Some((1, 1))
    );

    let _ = fs::remove_dir_all(&root_handoff);
    let _ = fs::remove_dir_all(&root_crash);
    let _ = fs::remove_dir_all(&root_a);
    let _ = fs::remove_dir_all(&root_b);
    let _ = fs::remove_dir_all(&root_dst);
    Ok(())
}

#[cfg(unix)]
#[test]
fn test_pack_export_and_shared_cas_fail_closed_on_corrupt_or_symlinked_blobs() -> Result<()> {
    use std::os::unix::fs::PermissionsExt;
    let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
    let root_src = std::env::temp_dir().join(format!("turbo_lean_exp_int_src_{}", next_tmp_id()));
    let root_dst = std::env::temp_dir().join(format!("turbo_lean_exp_int_dst_{}", next_tmp_id()));
    let _ = fs::remove_dir_all(&root_src);
    let _ = fs::remove_dir_all(&root_dst);

    let mut store_src = TurboStore::open(Some(&root_src))?;
    let good_payload = b"verified-pack-export-olean-payload-".repeat(24);
    let bh = store_src.store_immutable_blob(&good_payload, "olean", "trusted", 0)?;
    if let SingleflightOutcome::Leader(l) =
        store_src.acquire_singleflight("exp-int-act-1", "v4.35.0", "module_unit", "trusted")?
    {
        store_src.publish_action(
            &l,
            &[BlobEntry {
                blob_hash: bh.clone(),
                kind: "olean".into(),
                size_bytes: good_payload.len() as u64,
                rel_path: "build/lib/lean/ExpInt.olean".into(),
            }],
            1,
            0,
            0,
            "trusted",
        )?;
    }

    // 1. Seed a valid cached v3 header-only export and valid shared CAS entry, then corrupt
    //    the shared CAS entry with same-length bytes AND corrupt the store CAS entry:
    //    both v2 (`header_only_shared_cas = false`) and v3 (`header_only_shared_cas = true`)
    //    exports MUST fail closed with `Err`, never returning a digest-mismatched payload or
    //    cached pack stream.
    let empty = std::collections::HashSet::new();
    let (acts_v3, blobs_v3, _, _) =
        export_pack_filtered_with_mode(&store_src, true, &empty, &empty, true)?;
    assert_eq!((acts_v3, blobs_v3), (1, 1));
    let (acts_v2, blobs_v2, _, _) =
        export_pack_filtered_with_mode(&store_src, true, &empty, &empty, false)?;
    assert_eq!((acts_v2, blobs_v2), (1, 1));

    let mut corrupt_same_len = good_payload.clone();
    corrupt_same_len[0] ^= 0xFF;
    let shared_blobs = shared_cas_blobs_dir_for_store(&store_src.root);
    let shared_shm = shared_cas_blobs_dir();
    let sp_disk = shared_blobs.join(&bh[..2]).join(&bh);
    let sp_shm = shared_shm.join(&bh[..2]).join(&bh);

    // Corrupt shared CAS entries with same-length `0o444` bytes while keeping `store_src` intact:
    // `ensure_blob_in_shared_cas` and v3-to-v2 fallback must detect the digest mismatch and heal
    // or read from verified `store_src`, never emitting `corrupt_same_len`.
    for sp in [&sp_disk, &sp_shm] {
        if sp.exists() {
            let _ = fs::remove_file(sp);
            fs::write(sp, &corrupt_same_len)?;
            let mut p = fs::metadata(sp)?.permissions();
            p.set_mode(0o444);
            fs::set_permissions(sp, p)?;
        }
    }
    // Remove v2 cache so `export_pack_filtered_with_mode(..., false)` exercises the v3-to-v2
    // conversion path (`v3_file` exists!).
    for entry in fs::read_dir(store_src.root.join("locks"))?.flatten() {
        let name = entry.file_name().to_string_lossy().to_string();
        if name.starts_with("pack_exp_v2_") || name.starts_with("last_full_export_") {
            let _ = fs::remove_file(entry.path());
        }
    }
    let (_, _, _, v2_healed_stream) =
        export_pack_filtered_with_mode(&store_src, true, &empty, &empty, false)?;
    let mut store_dst = TurboStore::open(Some(&root_dst))?;
    let imp = import_pack_bytes_with_policy(
        &mut store_dst,
        &v2_healed_stream,
        Some("trusted"),
        None,
        true,
    )?;
    assert_eq!(imp, (1, 1));
    assert_eq!(fs::read(store_dst.blob_path(&bh))?, good_payload);

    // Also verify `ensure_blob_in_shared_cas` healed `sp_disk` back to `good_payload`!
    let mut seen = [false; 256];
    assert!(ensure_blob_in_shared_cas(
        &store_src,
        &bh,
        good_payload.len() as u64,
        &shared_blobs,
        &mut seen
    ));
    assert_eq!(fs::read(&sp_disk)?, good_payload);

    // 2. Now corrupt `store_src`'s own raw CAS blob with same-length bytes (even with warm
    //    `pack_exp_v2_*` and `pack_exp_v3_*` caches present!): both v2 and v3 exports must
    //    invalidate the stale cache and fail closed with `Err` rather than exporting corrupt bytes
    //    or silently dropping the blob from the pack.
    let cas_p = store_src.blob_path(&bh);
    fs::remove_file(&cas_p)?;
    fs::write(&cas_p, &corrupt_same_len)?;
    let mut p_cas = fs::metadata(&cas_p)?.permissions();
    p_cas.set_mode(0o444);
    fs::set_permissions(&cas_p, p_cas)?;
    assert!(
        export_pack_filtered_with_mode(&store_src, true, &empty, &empty, false).is_err(),
        "v2 export must fail closed when raw CAS blob fails digest verification"
    );
    assert!(
        export_pack_filtered_with_mode(&store_src, true, &empty, &empty, true).is_err(),
        "v3 export must fail closed when raw CAS blob fails digest verification"
    );

    // 3. Plant a symlink at `cas_p` pointing to a valid file: export must still fail closed.
    let valid_target = root_src.join("decoy_valid.olean");
    fs::write(&valid_target, &good_payload)?;
    fs::remove_file(&cas_p)?;
    std::os::unix::fs::symlink(&valid_target, &cas_p)?;
    assert!(
        export_pack_filtered_with_mode(&store_src, true, &empty, &empty, false).is_err(),
        "export must reject symlinked CAS blob"
    );

    // 4. Retained writable descriptor on shared-CAS source across `prestage_blobs_from_shared_cas`:
    //    Even when a writer holds an already-open writable fd to the shared-CAS blob, mutates it
    //    after verification (before rename) and again after `prestage_blobs_from_shared_cas`
    //    returns, the imported destination store blob MUST remain intact on a private inode.
    #[cfg(unix)]
    {
        use std::io::{Seek, Write};
        use std::os::unix::fs::MetadataExt;
        let iso_root =
            std::env::temp_dir().join(format!("turbo_lean_pack_fd_iso_{}", next_tmp_id()));
        let _ = fs::remove_dir_all(&iso_root);
        let iso_payload = b"shared-cas-retained-fd-original-bytes".to_vec();
        let iso_bh = blake3::hash(&iso_payload).to_hex().to_string();
        let mut iso_mut1 = iso_payload.clone();
        iso_mut1[0] ^= 0x33;
        let mut iso_mut2 = iso_payload.clone();
        iso_mut2[1] ^= 0x77;

        let sp_iso = shared_cas_blobs_dir_for_store(&iso_root)
            .join(&iso_bh[..2])
            .join(&iso_bh);
        fs::create_dir_all(sp_iso.parent().unwrap())?;
        let _ = fs::remove_file(&sp_iso);
        let shared_rw = std::sync::Arc::new(std::sync::Mutex::new(
            fs::OpenOptions::new()
                .create(true)
                .truncate(true)
                .read(true)
                .write(true)
                .open(&sp_iso)?,
        ));
        shared_rw.lock().unwrap().write_all(&iso_payload)?;
        let shared_ino = fs::metadata(&sp_iso)?.ino();

        let rw_hook = std::sync::Arc::clone(&shared_rw);
        let m1 = iso_mut1.clone();
        crate::db::set_after_blob_verify_before_rename_hook(std::sync::Arc::new(move |_s, _d| {
            if let Ok(mut f) = rw_hook.lock() {
                let _ = f.seek(std::io::SeekFrom::Start(0));
                let _ = f.write_all(&m1);
            }
        }));
        let iso_manifest = PackManifest {
            format_version: 3,
            host_arch: "linux-x86_64".to_string(),
            created_at: 0,
            actions: vec![],
            blobs: vec![PackedBlob {
                blob_hash: iso_bh.clone(),
                kind: "olean".to_string(),
                size_bytes: iso_payload.len() as u64,
                portable: true,
                data_hex_or_base64: vec![],
            }],
            ed25519_pubkey: None,
            ed25519_signature: None,
            replayed_oleans: Vec::new(),
        };
        let staged = prestage_blobs_from_shared_cas(&iso_root, &iso_manifest);
        crate::db::clear_after_blob_verify_before_rename_hook();
        assert!(
            staged.is_some(),
            "prestage_blobs_from_shared_cas must succeed from verified snapshot"
        );
        let dst_blob = iso_root.join("blobs").join(&iso_bh[..2]).join(&iso_bh);
        assert_ne!(fs::metadata(&dst_blob)?.ino(), shared_ino);
        assert_eq!(fs::read(&dst_blob)?, iso_payload);

        {
            let mut f = shared_rw.lock().unwrap();
            f.seek(std::io::SeekFrom::Start(0))?;
            f.write_all(&iso_mut2)?;
        }
        assert_eq!(
            fs::read(&dst_blob)?,
            iso_payload,
            "retained writable fd on shared CAS must never corrupt prestaged destination CAS blob"
        );
        let _ = fs::remove_file(&sp_iso);
        let _ = fs::remove_dir_all(&iso_root);

        // Post-restart header-only v3 pack import when shared CAS has been cleaned:
        // `ExclusivelyCreatedCasRegistry` no longer knows the local `<store>/blobs/<p>/<hash>`
        // inode (`unseal_cas_inode`), and both shared CAS locations are absent, yet the local
        // persistent store holds a digest-valid blob. `import_pack_bytes_with_policy` must
        // snapshot & verify the local blob into a fresh sealed owned inode and succeed.
        let restart_root =
            std::env::temp_dir().join(format!("turbo_lean_pack_restart_v3_{}", next_tmp_id()));
        let _ = fs::remove_dir_all(&restart_root);
        let mut restart_store = TurboStore::open(Some(&restart_root))?;
        let local_payload = b"post-restart-local-cas-only-blob-v3".to_vec();
        let local_bh = blake3::hash(&local_payload).to_hex().to_string();
        let local_dest = restart_root
            .join("blobs")
            .join(&local_bh[..2])
            .join(&local_bh);
        fs::create_dir_all(local_dest.parent().unwrap())?;
        let mut pre_restart_rw = fs::OpenOptions::new()
            .create(true)
            .truncate(true)
            .read(true)
            .write(true)
            .open(&local_dest)?;
        pre_restart_rw.write_all(&local_payload)?;
        let old_local_meta = pre_restart_rw.metadata()?;
        crate::db::unseal_cas_inode(old_local_meta.dev(), old_local_meta.ino());
        assert!(!crate::db::is_exclusively_created_immutable_cas_inode(
            &old_local_meta,
            &local_bh
        ));
        let _ = fs::remove_file(
            shared_cas_blobs_dir_for_store(&restart_root)
                .join(&local_bh[..2])
                .join(&local_bh),
        );
        let _ = fs::remove_file(shared_cas_blobs_dir().join(&local_bh[..2]).join(&local_bh));

        let tlz1_raw = b"post-restart-local-tlz1-compressed-cas-blob-v3-payload-bytes".to_vec();
        let tlz1_bh = blake3::hash(&tlz1_raw).to_hex().to_string();
        let tlz1_dest = restart_root
            .join("blobs")
            .join(&tlz1_bh[..2])
            .join(&tlz1_bh);
        fs::create_dir_all(tlz1_dest.parent().unwrap())?;
        fs::write(&tlz1_dest, crate::db::compress_tlz1(&tlz1_raw))?;
        let old_tlz1_meta = fs::metadata(&tlz1_dest)?;
        crate::db::unseal_cas_inode(old_tlz1_meta.dev(), old_tlz1_meta.ino());
        let _ = fs::remove_file(
            shared_cas_blobs_dir_for_store(&restart_root)
                .join(&tlz1_bh[..2])
                .join(&tlz1_bh),
        );
        let _ = fs::remove_file(shared_cas_blobs_dir().join(&tlz1_bh[..2]).join(&tlz1_bh));

        let restart_manifest = PackManifest {
            format_version: 3,
            host_arch: std::env::consts::ARCH.to_string(),
            created_at: 1,
            actions: vec![ActionRecord {
                action_key: "act_post_restart_v3".to_string(),
                toolchain_githash: "leanprover/lean4:v4.35.0".to_string(),
                kind: "check_shard".to_string(),
                status: "completed".to_string(),
                fencing_token: 1,
                output_manifest_hash: blake3::hash(b"manifest-post-restart-v3")
                    .to_hex()
                    .to_string(),
                duration_ms: 5,
                peak_pss_bytes: 0,
                heartbeats: 0,
                trust_domain: "untrusted".to_string(),
                outputs: vec![
                    BlobEntry {
                        rel_path: "receipt.json".to_string(),
                        blob_hash: local_bh.clone(),
                        kind: "receipt".to_string(),
                        size_bytes: local_payload.len() as u64,
                    },
                    BlobEntry {
                        rel_path: "compressed_shard.olean".to_string(),
                        blob_hash: tlz1_bh.clone(),
                        kind: "olean".to_string(),
                        size_bytes: tlz1_raw.len() as u64,
                    },
                ],
            }],
            blobs: vec![
                PackedBlob {
                    blob_hash: local_bh.clone(),
                    kind: "receipt".to_string(),
                    size_bytes: local_payload.len() as u64,
                    portable: true,
                    data_hex_or_base64: vec![],
                },
                PackedBlob {
                    blob_hash: tlz1_bh.clone(),
                    kind: "olean".to_string(),
                    size_bytes: tlz1_raw.len() as u64,
                    portable: true,
                    data_hex_or_base64: vec![],
                },
            ],
            ed25519_pubkey: None,
            ed25519_signature: None,
            replayed_oleans: Vec::new(),
        };
        let hdr_bytes = serde_json::to_vec(&restart_manifest)?;
        let mut v3_pack = Vec::with_capacity(16 + hdr_bytes.len());
        v3_pack.extend_from_slice(b"TLPK\x00\x00\x00\x03");
        v3_pack.extend_from_slice(&(hdr_bytes.len() as u64).to_le_bytes());
        v3_pack.extend_from_slice(&hdr_bytes);

        let (imp_acts, imp_blobs) = import_pack_bytes_with_policy(
            &mut restart_store,
            &v3_pack,
            Some("untrusted"),
            None,
            false,
        )?;
        assert_eq!((imp_acts, imp_blobs), (1, 2));
        let resealed_meta = fs::metadata(&local_dest)?;
        assert_ne!(
            resealed_meta.ino(),
            old_local_meta.ino(),
            "unsealed local blob must be snapshotted into a fresh exclusively created inode"
        );
        assert!(
            crate::db::is_exclusively_created_immutable_cas_inode(&resealed_meta, &local_bh),
            "re-published local blob must be sealed in ExclusivelyCreatedCasRegistry"
        );
        let resealed_tlz1_meta = fs::metadata(&tlz1_dest)?;
        assert_ne!(resealed_tlz1_meta.ino(), old_tlz1_meta.ino());
        assert!(
            crate::db::is_exclusively_created_immutable_cas_inode(&resealed_tlz1_meta, &tlz1_bh),
            "re-published TLZ1 local blob must be sealed in ExclusivelyCreatedCasRegistry"
        );
        assert_eq!(fs::read(&tlz1_dest)?, tlz1_raw);
        pre_restart_rw.seek(std::io::SeekFrom::Start(0))?;
        pre_restart_rw.write_all(b"mutated-via-pre-restart-writable-fd")?;
        assert_eq!(
            fs::read(&local_dest)?,
            local_payload,
            "retained writable fd on old unsealed local inode must not affect re-sealed blob"
        );
        let _ = fs::remove_dir_all(&restart_root);
    }

    let _ = fs::remove_file(&sp_disk);
    let _ = fs::remove_file(&sp_shm);
    let _ = fs::remove_dir_all(&root_src);
    let _ = fs::remove_dir_all(&root_dst);
    Ok(())
}

#[test]
fn test_speed3_v1_signed_pack_backward_compat_and_v2_replay_tamper_rejected() -> Result<()> {
    let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
    let dir = std::env::temp_dir().join(format!("turbo_lean_speed3_v1_v2_{}", next_tmp_id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir)?;

    let sk_hex = "5555555555555555555555555555555555555555555555555555555555555555";
    let pk_hex = crate::receipt::ed25519_verifying_key_hex(&[0x55u8; 32]);

    let payload = b"speed3-v1-compat-blob";
    let bh = blake3::hash(payload).to_hex().to_string();
    let mut v1_manifest = PackManifest {
        format_version: 2,
        host_arch: std::env::consts::ARCH.into(),
        created_at: 1000,
        ed25519_pubkey: Some(pk_hex.clone()),
        ed25519_signature: None,
        actions: vec![ActionRecord {
            action_key: "speed3-v1-act".into(),
            toolchain_githash: "v4.35.0".into(),
            kind: "module_unit".into(),
            status: "done".into(),
            fencing_token: 1,
            output_manifest_hash: "00".repeat(32),
            duration_ms: 12,
            peak_pss_bytes: 0,
            heartbeats: 1,
            trust_domain: "trusted".into(),
            outputs: vec![BlobEntry {
                blob_hash: bh.clone(),
                kind: "olean".into(),
                size_bytes: payload.len() as u64,
                rel_path: "build/lib/lean/V1Mod.olean".into(),
            }],
        }],
        blobs: vec![PackedBlob {
            blob_hash: bh.clone(),
            kind: "olean".into(),
            size_bytes: payload.len() as u64,
            portable: true,
            data_hex_or_base64: Vec::new(),
        }],
        replayed_oleans: Vec::new(),
    };
    {
        use ed25519_dalek::{Signer, SigningKey};
        let sk = SigningKey::from_bytes(&decode_hex_fixed::<32>(sk_hex)?);
        let dig_v1 = compute_pack_attestation_digest_v1_legacy(&v1_manifest);
        let sig_v1 = sk.sign(&dig_v1);
        v1_manifest.ed25519_signature = Some(encode_hex_bytes(&sig_v1.to_bytes()));
    }
    verify_pack_manifest_ed25519(&v1_manifest, &pk_hex)?;

    // Injecting an unsigned `replayed_oleans` entry onto a v1-signed pack MUST fail closed.
    let mut injected_v1 = v1_manifest.clone();
    injected_v1.replayed_oleans.push(AttestedOleanReplay {
        artifact_digest: "aa".repeat(32),
        environment_digest: "bb".repeat(32),
        replay_version: crate::zygote::ZYGOTE_REPLAY_VERSION,
        toolchain_hash: "deadbeef".into(),
        module_name: "Evil.Mod".into(),
    });
    assert!(
        verify_pack_manifest_ed25519(&injected_v1, &pk_hex).is_err(),
        "v1 fallback must never verify when replayed_oleans is non-empty"
    );

    let v1_hdr = serde_json::to_vec(&v1_manifest)?;
    let mut v1_stream = Vec::with_capacity(16 + v1_hdr.len() + payload.len());
    v1_stream.extend_from_slice(b"TLPK\x00\x00\x00\x02");
    v1_stream.extend_from_slice(&(v1_hdr.len() as u64).to_le_bytes());
    v1_stream.extend_from_slice(&v1_hdr);
    v1_stream.extend_from_slice(payload);
    let mut dst_v1 = TurboStore::open(Some(&dir.join("dst_v1")))?;
    let (acts, blobs) = import_pack_bytes_with_policy(
        &mut dst_v1,
        &v1_stream,
        Some("trusted"),
        Some(&pk_hex),
        false,
    )?;
    assert_eq!((acts, blobs), (1, 1));
    assert!(dst_v1
        .get_cached_action("speed3-v1-act", "trusted")?
        .is_some());

    // Now build a v2-signed pack carrying `replayed_oleans` and verify any field mutation fails closed.
    let mut src_v2 = TurboStore::open(Some(&dir.join("src_v2")))?;
    let bh2 = src_v2.store_immutable_blob(payload, "olean", "trusted", 0)?;
    if let SingleflightOutcome::Leader(lease) =
        src_v2.acquire_singleflight("speed3-v2-act", "v4.35.0", "module_unit", "trusted")?
    {
        src_v2.publish_action(
            &lease,
            &[BlobEntry {
                blob_hash: bh2,
                kind: "olean".into(),
                size_bytes: payload.len() as u64,
                rel_path: "build/lib/lean/V2Mod.olean".into(),
            }],
            10,
            0,
            0,
            "trusted",
        )?;
    }
    src_v2.record_kernel_replayed_olean(
        &"11".repeat(32),
        &"22".repeat(32),
        crate::zygote::ZYGOTE_REPLAY_VERSION,
        "cafebabe1234",
        "Dep.V2Mod",
        &[],
    )?;
    let (_, _, _, v2_stream) = export_pack_with_filter_mode_and_signing_key(
        &src_v2,
        true,
        &HashSet::new(),
        &HashSet::new(),
        None,
        false,
        Some(sk_hex),
    )?;
    let hlen = read_u64_le_at(&v2_stream, 8) as usize;
    let orig_m: PackManifest = serde_json::from_slice(&v2_stream[16..16 + hlen])?;
    assert_eq!(orig_m.replayed_oleans.len(), 1);
    verify_pack_manifest_ed25519(&orig_m, &pk_hex)?;

    for tamper_idx in 0..5 {
        let mut tampered = orig_m.clone();
        match tamper_idx {
            0 => tampered.replayed_oleans[0].artifact_digest = "ff".repeat(32),
            1 => tampered.replayed_oleans[0].environment_digest = "ee".repeat(32),
            2 => tampered.replayed_oleans[0].replay_version += 1,
            3 => tampered.replayed_oleans[0].toolchain_hash = "forged_githash".into(),
            _ => tampered.replayed_oleans.clear(),
        }
        let thdr = serde_json::to_vec(&tampered)?;
        let mut tstream = Vec::new();
        tstream.extend_from_slice(b"TLPK\x00\x00\x00\x02");
        tstream.extend_from_slice(&(thdr.len() as u64).to_le_bytes());
        tstream.extend_from_slice(&thdr);
        tstream.extend_from_slice(&v2_stream[16 + hlen..]);
        let mut dst_t = TurboStore::open(Some(&dir.join(format!("dst_tamper_{tamper_idx}"))))?;
        assert!(
            import_pack_bytes_with_policy(
                &mut dst_t,
                &tstream,
                Some("trusted"),
                Some(&pk_hex),
                false,
            )
            .is_err(),
            "tampered v2 replayed_oleans case {tamper_idx} must be rejected"
        );
        let replay_rows: i64 = dst_t.conn.query_row(
            "SELECT COUNT(*) FROM kernel_replayed_oleans_auth",
            [],
            |r| r.get(0),
        )?;
        assert_eq!(replay_rows, 0);
    }

    let _ = fs::remove_dir_all(&dir);
    Ok(())
}

#[test]
fn test_speed3_mismatched_toolchain_githash_or_replay_version_never_installs_hmac() -> Result<()> {
    let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
    let dir = std::env::temp_dir().join(format!("turbo_lean_speed3_mismatch_{}", next_tmp_id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir)?;

    let sk_hex = "6666666666666666666666666666666666666666666666666666666666666666";
    let pk_hex = crate::receipt::ed25519_verifying_key_hex(&[0x66u8; 32]);
    let installed_ghs = crate::module_builder::discover_host_installed_lean_githashes();
    let real_gh = installed_ghs
        .iter()
        .next()
        .cloned()
        .unwrap_or_else(|| "real_githash_fallback".to_string());

    let payload = b"speed3-mismatch-blob";
    let bh = blake3::hash(payload).to_hex().to_string();
    let mut manifest = PackManifest {
        format_version: 2,
        host_arch: std::env::consts::ARCH.into(),
        created_at: 2000,
        ed25519_pubkey: None,
        ed25519_signature: None,
        actions: vec![ActionRecord {
            action_key: "speed3-mismatch-act".into(),
            toolchain_githash: "v4.35.0".into(),
            kind: "module_unit".into(),
            status: "done".into(),
            fencing_token: 1,
            output_manifest_hash: "00".repeat(32),
            duration_ms: 5,
            peak_pss_bytes: 0,
            heartbeats: 1,
            trust_domain: "trusted".into(),
            outputs: vec![BlobEntry {
                blob_hash: bh.clone(),
                kind: "olean".into(),
                size_bytes: payload.len() as u64,
                rel_path: "build/lib/lean/Mismatch.olean".into(),
            }],
        }],
        blobs: vec![PackedBlob {
            blob_hash: bh,
            kind: "olean".into(),
            size_bytes: payload.len() as u64,
            portable: true,
            data_hex_or_base64: Vec::new(),
        }],
        replayed_oleans: vec![
            AttestedOleanReplay {
                artifact_digest: "33".repeat(32),
                environment_digest: "44".repeat(32),
                replay_version: crate::zygote::ZYGOTE_REPLAY_VERSION,
                toolchain_hash: "nonexistent_foreign_toolchain_githash_0000".into(),
                module_name: "Dep.ForeignTc".into(),
            },
            AttestedOleanReplay {
                artifact_digest: "55".repeat(32),
                environment_digest: "66".repeat(32),
                replay_version: crate::zygote::ZYGOTE_REPLAY_VERSION + 99,
                toolchain_hash: real_gh.clone(),
                module_name: "Dep.WrongVer".into(),
            },
        ],
    };
    sign_pack_manifest_ed25519(&mut manifest, sk_hex)?;
    let hdr = serde_json::to_vec(&manifest)?;
    let mut stream = Vec::with_capacity(16 + hdr.len() + payload.len());
    stream.extend_from_slice(b"TLPK\x00\x00\x00\x02");
    stream.extend_from_slice(&(hdr.len() as u64).to_le_bytes());
    stream.extend_from_slice(&hdr);
    stream.extend_from_slice(payload);

    let mut dst = TurboStore::open(Some(&dir.join("dst")))?;
    import_pack_bytes_with_policy(&mut dst, &stream, Some("trusted"), Some(&pk_hex), false)?;
    let replay_rows: i64 = dst.conn.query_row(
        "SELECT COUNT(*) FROM kernel_replayed_oleans_auth",
        [],
        |r| r.get(0),
    )?;
    assert_eq!(
        replay_rows, 0,
        "mismatched toolchain_hash or replay_version must never install local replay HMAC rows"
    );
    assert!(!dst.has_kernel_replayed_olean(
        &"33".repeat(32),
        &"44".repeat(32),
        crate::zygote::ZYGOTE_REPLAY_VERSION,
        "nonexistent_foreign_toolchain_githash_0000",
        &[]
    ));
    assert!(!dst.has_kernel_replayed_olean(
        &"55".repeat(32),
        &"66".repeat(32),
        crate::zygote::ZYGOTE_REPLAY_VERSION + 99,
        &real_gh,
        &[]
    ));

    let _ = fs::remove_dir_all(&dir);
    Ok(())
}

#[test]
fn test_uver7_migration_purges_locks_sidecars_and_pending_deferred_spools() -> Result<()> {
    let dir = std::env::temp_dir().join(format!("turbo_lean_uver7_locks_purge_{}", next_tmp_id()));
    let _ = fs::remove_dir_all(&dir);

    // Create an export archive from a separate source store so we have valid V3/V2 pack bytes.
    let src_dir = dir.join("src");
    let mut src_store = TurboStore::open(Some(&src_dir))?;
    let payload = b"pre-epoch-v7-blob";
    let bh = src_store.store_immutable_blob(payload, "olean", "trusted", 0)?;
    if let SingleflightOutcome::Leader(lease) = src_store.acquire_singleflight(
        "pre-epoch-v7-action",
        "v4.35.0",
        "module_unit",
        "trusted",
    )? {
        src_store.publish_action(
            &lease,
            &[BlobEntry {
                blob_hash: bh.clone(),
                kind: "olean".into(),
                size_bytes: payload.len() as u64,
                rel_path: "build/lib/lean/PreEpoch.olean".into(),
            }],
            1,
            0,
            1,
            "trusted",
        )?;
    }
    let pack_path = dir.join("pre_epoch.tlpack");
    export_pack(&src_store, &pack_path, true)?;
    let (_, _, _, v3_bytes) =
        export_pack_filtered_with_mode(&src_store, true, &HashSet::new(), &HashSet::new(), true)?;

    // Open target store, seed pre-epoch sidecars + pending deferred spool, downgrade to uver = 7.
    let dst_dir = dir.join("dst");
    let store = TurboStore::open(Some(&dst_dir))?;
    let (_, _) = prestage_blobs_from_shared_cas(
        &dst_dir,
        &try_parse_v3_header(&v3_bytes).expect("v3 header"),
    )
    .expect("prestage");
    let locks_dir = dst_dir.join("locks");
    fs::create_dir_all(&locks_dir)?;

    // Seed current-epoch-looking and pre-epoch sidecars + pending spools + locks that must survive.
    assert!(stage_deferred_pack_record_with_epoch(
        &dst_dir,
        "trusted",
        &v3_bytes,
        crate::TURBO_LEAN_BUILD_EPOCH
    ));
    fs::write(locks_dir.join("deferred_pack_v3.bin"), &v3_bytes)?;
    fs::write(locks_dir.join("deferred_pack_v3.domain"), b"trusted")?;
    fs::write(
        locks_dir.join("deferred_pack_v3.claim.999999.1.bin"),
        &v3_bytes,
    )?;
    fs::write(
        locks_dir.join("last_import_stamp"),
        format_last_import_stamp_with_epoch(
            "deadbeef",
            1,
            1,
            "trusted",
            crate::TURBO_LEAN_BUILD_EPOCH,
        ),
    )?;
    write_cached_portable_manifest_with_epoch(
        &dst_dir,
        &DeltaManifest {
            action_keys: vec!["pre-epoch-v7-action".into()],
            blob_hashes: vec![bh.clone()],
        },
        crate::TURBO_LEAN_BUILD_EPOCH,
    );
    fs::write(
        locks_dir.join("last_full_export_0.bin"),
        encode_last_full_export_with_epoch(
            1,
            1,
            payload.len() as u64,
            &v3_bytes,
            crate::TURBO_LEAN_BUILD_EPOCH,
        ),
    )?;
    fs::write(
        locks_dir.join("last_full_export_1.bin"),
        encode_last_full_export_with_epoch(
            1,
            1,
            payload.len() as u64,
            &v3_bytes,
            crate::TURBO_LEAN_BUILD_EPOCH,
        ),
    )?;
    fs::write(locks_dir.join("store_tree_durable.v1"), b"1")?;

    store.conn.execute_batch("PRAGMA user_version = 7;")?;
    drop(store);

    // Reopen triggers uver < 8 migration BEFORE replay_pending_deferred_packs.
    let migrated = TurboStore::open(Some(&dst_dir))?;
    let uv: i64 = migrated
        .conn
        .query_row("PRAGMA user_version;", [], |r| r.get(0))?;
    assert_eq!(uv, 8);
    assert!(
        !migrated.has_cached_action_readonly("pre-epoch-v7-action", "trusted")?,
        "pre-v8 pending deferred-pack spools must be purged before replay_pending_deferred_packs"
    );
    assert!(list_pending_deferred_pack_files(&locks_dir)?.is_empty());
    assert!(!locks_dir.join("deferred_pack_v3.domain").exists());
    assert!(!locks_dir.join("last_import_stamp").exists());
    assert!(!locks_dir.join("cached_portable_manifest.json").exists());
    assert!(!locks_dir.join("last_full_export_0.bin").exists());
    assert!(!locks_dir.join("last_full_export_1.bin").exists());
    assert!(locks_dir.join("store_tree_durable.v1").exists());
    assert!(locks_dir.join("gc_publish.lock").exists());
    assert!(locks_dir.join("deferred_pack.lock").exists());
    drop(migrated);

    // Stateless warm import and sync helpers must NOT short-circuit after the migration purge.
    assert!(
        try_stateless_warm_import_with_domain(&dst_dir, &pack_path, None, None, true).is_none()
    );
    assert!(!try_stateless_noop_pull_sync(
        &dst_dir,
        "http://127.0.0.1:9"
    ));
    assert!(try_stateless_push_sync(&dst_dir, "http://127.0.0.1:9").is_none());

    let _ = fs::remove_dir_all(&dir);
    Ok(())
}

#[test]
fn test_epoch_mismatch_and_same_epoch_locks_sidecars_and_spools() -> Result<()> {
    let dir =
        std::env::temp_dir().join(format!("turbo_lean_epoch_locks_sidecars_{}", next_tmp_id()));
    let _ = fs::remove_dir_all(&dir);

    let src_dir = dir.join("src");
    let mut src = TurboStore::open(Some(&src_dir))?;
    let payload = b"epoch-sidecar-blob";
    let bh = src.store_immutable_blob(payload, "olean", "trusted", 0)?;
    if let SingleflightOutcome::Leader(lease) =
        src.acquire_singleflight("epoch-sidecar-act", "v4.35.0", "module_unit", "trusted")?
    {
        src.publish_action(
            &lease,
            &[BlobEntry {
                blob_hash: bh.clone(),
                kind: "olean".into(),
                size_bytes: payload.len() as u64,
                rel_path: "build/lib/lean/EpochSidecar.olean".into(),
            }],
            1,
            0,
            1,
            "trusted",
        )?;
    }
    let pack_path = dir.join("epoch_sidecar.tlpack");
    export_pack(&src, &pack_path, true)?;
    let (_, _, _, v3_bytes) =
        export_pack_filtered_with_mode(&src, true, &HashSet::new(), &HashSet::new(), true)?;
    let manifest = try_parse_v3_header(&v3_bytes).expect("v3 header");

    // 1. User_version = 8 store with foreign-epoch (`epoch_b`) sidecars & deferred spool:
    //    readers/replay must fail closed and delete the mismatched files.
    let dst_dir = dir.join("dst");
    let store = TurboStore::open(Some(&dst_dir))?;
    let (_, _) = prestage_blobs_from_shared_cas(&dst_dir, &manifest).expect("prestage");
    drop(store);

    let epoch_b = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
    assert_ne!(epoch_b, crate::TURBO_LEAN_BUILD_EPOCH);
    let locks_dir = dst_dir.join("locks");

    let (_, _, header_buf) = read_pack_header_from_file(&pack_path).expect("pack header");
    let header_hash = blake3::hash(&header_buf).to_hex().to_string();
    fs::write(
        locks_dir.join("last_import_stamp"),
        format_last_import_stamp_with_epoch(&header_hash, 1, 1, "untrusted", epoch_b),
    )?;
    write_cached_portable_manifest_with_epoch(
        &dst_dir,
        &DeltaManifest {
            action_keys: vec!["epoch-sidecar-act".into()],
            blob_hashes: vec![bh.clone()],
        },
        epoch_b,
    );
    fs::write(
        locks_dir.join("last_full_export_0.bin"),
        encode_last_full_export_with_epoch(1, 1, payload.len() as u64, &v3_bytes, epoch_b),
    )?;
    fs::write(
        locks_dir.join("last_full_export_1.bin"),
        encode_last_full_export_with_epoch(1, 1, payload.len() as u64, &v3_bytes, epoch_b),
    )?;

    // Mismatched sidecars fail closed AND are unlinked on read.
    assert!(
        try_stateless_warm_import_with_domain(&dst_dir, &pack_path, None, None, false).is_none()
    );
    assert!(!locks_dir.join("last_import_stamp").exists());

    assert!(
        load_cached_portable_manifest_with_epoch(&dst_dir, crate::TURBO_LEAN_BUILD_EPOCH).is_none()
    );
    assert!(!locks_dir.join("cached_portable_manifest.json").exists());

    assert!(
        read_last_full_export_with_epoch(&dst_dir, false, crate::TURBO_LEAN_BUILD_EPOCH).is_none()
    );
    assert!(!locks_dir.join("last_full_export_0.bin").exists());
    assert!(
        read_last_full_export_with_epoch(&dst_dir, true, crate::TURBO_LEAN_BUILD_EPOCH).is_none()
    );
    assert!(!locks_dir.join("last_full_export_1.bin").exists());

    // Legacy/unbound sidecars (v1 stamp, raw DeltaManifest JSON, raw 24-byte export header) also fail closed & unlink.
    fs::write(
        locks_dir.join("last_import_stamp"),
        format!("{}:1:1:untrusted", header_hash),
    )?;
    assert!(
        try_stateless_warm_import_with_domain(&dst_dir, &pack_path, None, None, false).is_none()
    );
    assert!(!locks_dir.join("last_import_stamp").exists());

    fs::write(
        locks_dir.join("cached_portable_manifest.json"),
        serde_json::to_vec(&DeltaManifest {
            action_keys: vec!["epoch-sidecar-act".into()],
            blob_hashes: vec![bh.clone()],
        })?,
    )?;
    assert!(
        load_cached_portable_manifest_with_epoch(&dst_dir, crate::TURBO_LEAN_BUILD_EPOCH).is_none()
    );
    assert!(!locks_dir.join("cached_portable_manifest.json").exists());

    let mut legacy_export = Vec::new();
    legacy_export.extend_from_slice(&1u64.to_le_bytes());
    legacy_export.extend_from_slice(&1u64.to_le_bytes());
    legacy_export.extend_from_slice(&(payload.len() as u64).to_le_bytes());
    legacy_export.extend_from_slice(&v3_bytes);
    fs::write(locks_dir.join("last_full_export_0.bin"), &legacy_export)?;
    assert!(
        read_last_full_export_with_epoch(&dst_dir, false, crate::TURBO_LEAN_BUILD_EPOCH).is_none()
    );
    assert!(!locks_dir.join("last_full_export_0.bin").exists());

    // Mismatched-epoch deferred spool on uver = 8 store must be rejected & deleted on open without replaying.
    assert!(stage_deferred_pack_record_with_epoch(
        &dst_dir, "trusted", &v3_bytes, epoch_b
    ));
    assert_eq!(list_pending_deferred_pack_files(&locks_dir)?.len(), 1);
    let reopened = TurboStore::open(Some(&dst_dir))?;
    assert!(
        !reopened.has_cached_action_readonly("epoch-sidecar-act", "trusted")?,
        "foreign-epoch deferred spool must never replay into SQLite"
    );
    assert!(
        list_pending_deferred_pack_files(&locks_dir)?.is_empty(),
        "foreign-epoch deferred spool must be unlinked on replay"
    );
    drop(reopened);

    // 2. Same-epoch warm/cold paths continue to work, AND wiped SQLite + stale stamp fails closed.
    let cold_dir = dir.join("cold_same_epoch");
    let cold_counts =
        try_stateless_cold_import_with_domain(&cold_dir, &pack_path, Some("trusted"), None, true)
            .expect("same-epoch cold stateless import");
    assert_eq!(cold_counts, (1, 1));
    let mut warm_store = TurboStore::open(Some(&cold_dir))?;
    assert!(warm_store.has_cached_action_readonly("epoch-sidecar-act", "trusted")?);
    assert!(
        load_cached_portable_manifest_with_epoch(&cold_dir, crate::TURBO_LEAN_BUILD_EPOCH)
            .is_some()
    );

    // Populate same-epoch warm stamp via full import_pack_with_policy, then verify warm hit.
    let imp_counts =
        import_pack_with_policy(&mut warm_store, &pack_path, Some("trusted"), None, true)?;
    assert_eq!(imp_counts, (1, 1));
    drop(warm_store);
    assert_eq!(
        try_stateless_warm_import_with_domain(&cold_dir, &pack_path, Some("trusted"), None, true),
        Some((1, 1))
    );

    // If SQLite actions are wiped while a same-epoch `last_import_stamp` remains,
    // `import_pack_with_policy` must verify SQLite action presence and re-import instead of short-circuiting.
    let mut wiped_actions = TurboStore::open(Some(&cold_dir))?;
    wiped_actions
        .conn
        .execute("DELETE FROM action_outputs", [])?;
    wiped_actions.conn.execute("DELETE FROM actions", [])?;
    assert!(cold_dir.join("locks/last_import_stamp").exists());
    import_pack_with_policy(&mut wiped_actions, &pack_path, Some("trusted"), None, true)?;
    assert!(
        wiped_actions.has_cached_action_readonly("epoch-sidecar-act", "trusted")?,
        "import_pack_with_policy must re-populate SQLite even when last_import_stamp matches"
    );
    drop(wiped_actions);

    // If `state.db` itself is deleted while `locks/last_import_stamp` remains, stateless warm import must refuse & unlink.
    fs::remove_file(cold_dir.join("state.db"))?;
    assert!(try_stateless_warm_import_with_domain(
        &cold_dir,
        &pack_path,
        Some("trusted"),
        None,
        true
    )
    .is_none());
    assert!(!cold_dir.join("locks/last_import_stamp").exists());

    let _ = fs::remove_dir_all(&dir);
    Ok(())
}
