use crate::db::TurboStore;
use crate::pack::next_tmp_id;
use anyhow::{Context, Result};
use std::fs;
use std::io::{BufRead, BufReader, Write};
#[cfg(test)]
use std::net::TcpListener;
use std::path::{Path, PathBuf};
use std::process::Command;

mod budget;
pub use self::budget::*;
mod daemon;
pub use self::daemon::*;
mod closure;
pub use self::closure::*;
mod audit;
pub use self::audit::*;
mod worker;
pub use self::worker::*;
mod dispatch;
pub use self::dispatch::*;


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg(unix)]
    fn parallel_cross_file_stale_workers_are_retried() {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let (dir, store, mut env, lean_bin) = open_test_zygote_env("parallel_cross_file").unwrap();
        let policy_tag = format!("R7Parallel{}", next_tmp_id());
        env.insert(
            crate::splitter::ALLOWED_AXIOMS_ENV.into(),
            policy_tag.clone(),
        );
        let source = "import Init\n-- namespace _TurboCrossFileShard_0\ntheorem r7_first : True := True.intro\n-- namespace _TurboCrossFileShard_1\ntheorem r7_second : True := True.intro\n";
        let eval = |source: &str| {
            eval_with_zygote_pool(
                &store,
                "leanprover/lean4:v4.35.0",
                "",
                &env,
                &lean_bin,
                source,
                false,
            )
            .unwrap()
        };
        let first = eval(source);
        assert!(first.ok && first.kernel_gate_active, "{first:?}");
        let mut held_pipes = Vec::new();
        let mut stale_pids = Vec::new();
        {
            let mut pool = ZYGOTE_POOL.get().unwrap().lock().unwrap();
            for worker in pool
                .iter_mut()
                .filter(|(key, _)| key.0.contains(&policy_tag))
                .flat_map(|(_, workers)| workers)
            {
                stale_pids.push(worker.pid());
                held_pipes.push(std::mem::replace(
                    &mut worker.stdin,
                    fs::File::open("/dev/null").unwrap(),
                ));
            }
        }
        assert_eq!(stale_pids.len(), 2);
        let retried = eval(&source.replace("True.intro", "by trivial"));
        assert!(retried.ok && retried.kernel_gate_active, "{retried:?}");
        assert!(retried.decl_types.contains_key("r7_first"));
        assert!(retried.decl_types.contains_key("r7_second"));
        let pool = ZYGOTE_POOL.get().unwrap().lock().unwrap();
        assert!(pool
            .iter()
            .filter(|(key, _)| key.0.contains(&policy_tag))
            .flat_map(|(_, workers)| workers)
            .all(|worker| !stale_pids.contains(&worker.pid())));
        drop(pool);
        drop(held_pipes);
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn test_mcp_transport_detects_early_child_exit() {
        let mut child = Command::new("sh").args(["-c", "exit 7"]).spawn().unwrap();
        let started = std::time::Instant::now();
        let error = wait_for_mcp_transport_child(
            "http://127.0.0.1:1",
            "unused",
            &std::env::temp_dir().join(format!("absent-daemon-{}.sock", next_tmp_id())),
            Some(&mut child),
        )
        .unwrap_err();
        assert_eq!(error.to_string(), "Shared daemon exited before ready");
        assert!(started.elapsed() < std::time::Duration::from_secs(1));
    }

    #[test]
    fn mcp_explicit_kernel_and_relative_audit_policy() {
        let _guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let keys = [
            "TURBO_LEAN_KERNEL_ENGINE",
            "TURBO_LEAN_KERNEL_ENGINE_FROM_CONFIG",
            "TURBO_LEAN_AUDIT_SPEC_CONFIG",
            "TURBO_LEAN_AUDIT_SPEC_CONFIG_FROM_CONFIG",
        ];
        let saved: Vec<_> = keys
            .iter()
            .map(|key| (*key, std::env::var_os(key)))
            .collect();
        clear_inbound_policy();
        std::env::set_var(keys[0], "explicit-engine");
        std::env::remove_var(keys[1]);
        std::env::set_var(keys[2], "policy/audit.toml");
        std::env::remove_var(keys[3]);
        let policy = mcp_caller_policy();
        assert_eq!(policy.get(keys[0]).unwrap(), "explicit-engine");
        assert_eq!(
            Path::new(policy.get(keys[2]).unwrap()),
            std::env::current_dir().unwrap().join("policy/audit.toml")
        );
        std::env::set_var(keys[1], "1");
        assert!(!mcp_caller_policy().contains_key(keys[0]));
        set_inbound_policy(policy);
        let mut child = Command::new("unused");
        configure_mcp_child_policy(&mut child);
        assert!(child
            .get_envs()
            .any(|(k, v)| k == keys[0] && v == Some(std::ffi::OsStr::new("explicit-engine"))));
        set_inbound_policy(Default::default());
        configure_mcp_child_policy(&mut child);
        for key in &keys[..2] {
            assert!(child.get_envs().any(|(k, v)| k == *key && v.is_none()));
        }
        clear_inbound_policy();
        for (key, value) in saved {
            match value {
                Some(v) => std::env::set_var(key, v),
                None => std::env::remove_var(key),
            }
        }
        for inline in [
            "{\"enabled\":true}",
            "enabled=true",
            "[audit]\nenabled=true",
        ] {
            assert_eq!(
                normalize_mcp_runtime_setting(keys[2], inline.into()),
                inline
            );
        }
    }

    #[test]
    fn mcp_runtime_policy_preserves_raw_values_separately_from_allowlists() {
        let raw = " b,a,b ";
        let env: std::collections::HashMap<_, _> = REQUEST_POLICY_KEYS
            .into_iter()
            .chain(MCP_RUNTIME_POLICY_KEYS)
            .map(|key| (key.to_string(), raw.to_string()))
            .collect();
        let canonical = request_policy(&env);
        assert_eq!(canonical.len(), 4);
        assert!(canonical.values().all(|value| value == "a,b"));
        set_inbound_policy(env.into_iter().collect());
        let mut child = Command::new("unused");
        configure_mcp_child_policy(&mut child);
        for key in MCP_RUNTIME_POLICY_KEYS {
            assert_eq!(inbound_setting(key).as_deref(), Some(raw));
            assert_eq!(mcp_caller_policy().get(key).map(String::as_str), Some(raw));
            assert!(child
                .get_envs()
                .any(|(name, value)| name == key && value == Some(std::ffi::OsStr::new(raw))));
        }
        clear_inbound_policy();
    }

    #[test]
    fn worker_api_keys_are_scrubbed_from_command_overrides() {
        let mut child = Command::new("unused");
        child.env("TURBO_TEST_API_KEY", "private");
        scrub_worker_api_keys(&mut child);
        assert!(child
            .get_envs()
            .any(|(key, value)| key == "TURBO_TEST_API_KEY" && value.is_none()));
    }

    #[test]
    fn mcp_unset_telemetry_is_forwarded_as_tombstones() {
        set_inbound_policy(Default::default());
        let policy = mcp_caller_policy();
        for key in ["SANDBOXED_TELEMETRY_MODE", "SANDBOXED_TELEMETRY"] {
            assert_eq!(policy.get(key).map(String::as_str), Some(""));
            let mut child = Command::new("unused");
            configure_mcp_child_policy(&mut child);
            assert!(child
                .get_envs()
                .any(|(k, v)| k == key && v == Some(std::ffi::OsStr::new(""))));
        }
        clear_inbound_policy();
    }

    #[test]
    fn mcp_policy_preserves_only_explicit_cross_project_overrides() {
        let _guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let saved: Vec<_> = REQUEST_POLICY_KEYS
            .into_iter()
            .chain(MCP_RUNTIME_POLICY_KEYS)
            .flat_map(|key| [key.to_string(), format!("{key}_FROM_CONFIG")])
            .map(|key| {
                let value = std::env::var_os(&key);
                (key, value)
            })
            .collect();
        for key in REQUEST_POLICY_KEYS
            .into_iter()
            .chain(MCP_RUNTIME_POLICY_KEYS)
        {
            std::env::set_var(key, "*");
            std::env::set_var(format!("{key}_FROM_CONFIG"), "1");
        }
        let captured = mcp_caller_policy();
        assert_eq!(
            captured,
            std::collections::BTreeMap::from([
                ("SANDBOXED_TELEMETRY_MODE".into(), String::new()),
                ("SANDBOXED_TELEMETRY".into(), String::new()),
            ])
        );
        set_inbound_policy(captured);
        let mut child = Command::new("unused");
        configure_mcp_child_policy(&mut child);
        for key in REQUEST_POLICY_KEYS
            .into_iter()
            .chain(MCP_RUNTIME_POLICY_KEYS)
        {
            let expected = key
                .starts_with("SANDBOXED_TELEMETRY")
                .then_some(std::ffi::OsStr::new(""));
            assert!(child.get_envs().any(|(k, v)| k == key && v == expected));
        }
        INBOUND_POLICY.with(|p| *p.borrow_mut() = None);
        for key in REQUEST_POLICY_KEYS
            .into_iter()
            .chain(MCP_RUNTIME_POLICY_KEYS)
        {
            std::env::remove_var(format!("{key}_FROM_CONFIG"));
        }
        set_inbound_policy(mcp_caller_policy());
        let mut child = Command::new("unused");
        configure_mcp_child_policy(&mut child);
        for key in REQUEST_POLICY_KEYS
            .into_iter()
            .chain(MCP_RUNTIME_POLICY_KEYS)
        {
            assert!(child.get_envs().any(|(k, v)| k == key
                && v == Some(std::ffi::OsStr::new(&normalize_mcp_runtime_setting(
                    key,
                    "*".into()
                )))));
        }
        INBOUND_POLICY.with(|p| *p.borrow_mut() = None);
        for (key, value) in saved {
            match value { Some(value) => std::env::set_var(key, value), None => std::env::remove_var(key) }
        }
    }

    #[test]
    #[cfg(unix)]
    fn caller_staging_dir_preserves_0755_and_rejects_symlinks() -> Result<()> {
        use std::os::unix::fs::{symlink, PermissionsExt};
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let prev = std::env::var_os("TURBO_LEAN_STAGING_DIR");
        let root = private_temp_subdir("staging-mode-test")
            .context("private directory")?
            .join(format!("run-{}", next_tmp_id()));
        fs::create_dir_all(&root)?;
        let caller_dir = root.join("caller_0755");
        fs::create_dir(&caller_dir)?;
        fs::set_permissions(&caller_dir, fs::Permissions::from_mode(0o755))?;
        std::env::set_var("TURBO_LEAN_STAGING_DIR", &caller_dir);
        let guard = lifecycle_lock(false)?;
        assert_eq!(
            fs::symlink_metadata(&caller_dir)?.permissions().mode() & 0o777,
            0o755
        );
        drop(guard);
        ensure_staging_namespace_dir(true)?;
        for name in ["transport", "fork-sockets", "zygote_daemon_cas_test"] {
            let child = private_staging_child(name)?;
            assert_eq!(fs::metadata(child)?.permissions().mode() & 0o777, 0o700);
        }
        let payload = LocalPayload::create(b"private payload")?;
        assert_eq!(LocalPayload::read(&payload.tag())?, b"private payload");
        assert_eq!(
            fs::symlink_metadata(&caller_dir)?.permissions().mode() & 0o777,
            0o755
        );

        let live_link = root.join("live_link");
        symlink(&caller_dir, &live_link)?;
        std::env::set_var("TURBO_LEAN_STAGING_DIR", &live_link);
        assert!(lifecycle_lock(false).is_err());
        assert!(ensure_staging_namespace_dir(true).is_err());

        let dangling_link = root.join("dangling_link");
        symlink(root.join("missing_target"), &dangling_link)?;
        std::env::set_var("TURBO_LEAN_STAGING_DIR", &dangling_link);
        assert!(lifecycle_lock(false).is_err());
        assert!(ensure_staging_namespace_dir(true).is_err());
        assert!(!root.join("missing_target").exists());

        match prev {
            Some(v) => std::env::set_var("TURBO_LEAN_STAGING_DIR", v),
            None => std::env::remove_var("TURBO_LEAN_STAGING_DIR"),
        }
        fs::remove_dir_all(&root)?;
        Ok(())
    }

    #[test]
    #[cfg(target_os = "linux")]
    fn dead_zygote_master_is_replaced_with_fresh_master() {
        let Some((dir, store, mut env, lean)) = open_test_zygote_env("dead_master") else {
            return;
        };
        fs::write(
            dir.join("DeadMasterSeed.olean"),
            compile_test_olean(&lean, &dir, "DeadMasterSeed", "def dmSeed : Nat := 11\n"),
        )
        .unwrap();
        env.insert("LEAN_PATH".into(), dir.to_string_lossy().into_owned());
        let first = eval_with_zygote_pool_for_targets(
            &store,
            "leanprover/lean4:v4.35.0",
            &env["LEAN_PATH"],
            &env,
            &lean,
            "import DeadMasterSeed\ntheorem dm_one : dmSeed = 11 := rfl\n",
            &["dm_one".into()],
            None,
            &[],
        )
        .unwrap();
        assert!(first.ok, "{:?}", first.errors);
        let old_master_pid = {
            let masters = ZYGOTE_MASTERS.get().unwrap().lock().unwrap();
            masters
                .values()
                .find(|e| {
                    e.worker
                        .lock()
                        .unwrap()
                        .warm_imports
                        .contains_key("DeadMasterSeed")
                })
                .unwrap()
                .pid
        };
        if let Some(pool) = ZYGOTE_POOL.get() {
            pool.lock().unwrap().clear();
        }
        unsafe {
            libc::kill(old_master_pid as i32, libc::SIGKILL);
        }
        for _ in 0..100 {
            if !owned_process_alive(old_master_pid) {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
        assert!(!owned_process_alive(old_master_pid));
        let second = eval_with_zygote_pool_for_targets(
            &store,
            "leanprover/lean4:v4.35.0",
            &env["LEAN_PATH"],
            &env,
            &lean,
            "import DeadMasterSeed\ntheorem dm_two : dmSeed = 11 := rfl\n",
            &["dm_two".into()],
            None,
            &[],
        )
        .unwrap();
        assert!(second.ok, "{:?}", second.errors);
        let new_master_pid = {
            let masters = ZYGOTE_MASTERS.get().unwrap().lock().unwrap();
            masters
                .values()
                .find(|e| {
                    e.worker
                        .lock()
                        .unwrap()
                        .warm_imports
                        .contains_key("DeadMasterSeed")
                })
                .unwrap()
                .pid
        };
        assert_ne!(new_master_pid, old_master_pid);
        assert!(owned_process_alive(new_master_pid));
        let _ = fs::remove_dir_all(dir);
    }

    #[test]
    fn long_unix_socket_paths_roundtrip() -> Result<()> {
        use std::io::{Read, Write};
        let dir = private_temp_subdir("long-socket-test").context("private directory")?;
        let nested = dir.join("nested-directory-name-that-exceeds-the-unix-socket-address-limit".repeat(2));
        fs::create_dir(&nested)?;
        let path = nested.join("daemon.sock");
        let (short, _dir) = unix_socket_path(&path)?;
        let listener = std::os::unix::net::UnixListener::bind(short)?;
        let (short, _dir) = unix_socket_path(&path)?;
        let mut client = std::os::unix::net::UnixStream::connect(short)?;
        let (mut server, _) = listener.accept()?;
        client.write_all(b"ok")?;
        let mut bytes = [0; 2];
        server.read_exact(&mut bytes)?;
        assert_eq!(&bytes, b"ok");
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn bounded_wire_lines_reject_oversized_and_truncated_input() {
        let mut buf = String::new();
        let mut input: &[u8] = b"short\r\nrest";
        assert!(matches!(read_bounded_line(&mut input, &mut buf), Ok(BoundedLine::Line)));
        assert_eq!(buf, "short\r\n");
        assert!(matches!(read_bounded_line(&mut input, &mut buf), Ok(BoundedLine::Truncated)));
        assert_eq!(buf, "rest");
        let mut input: &[u8] = b"";
        assert!(matches!(read_bounded_line(&mut input, &mut buf), Ok(BoundedLine::Eof)));
        let mut long = vec![b'A'; MAX_WIRE_LINE_BYTES + 2];
        long.push(b'\n');
        assert!(matches!(read_bounded_line(&mut long.as_slice(), &mut buf), Ok(BoundedLine::TooLong)));
        let mut exact = vec![b'A'; MAX_WIRE_LINE_BYTES - 1];
        exact.push(b'\n');
        assert!(matches!(read_bounded_line(&mut exact.as_slice(), &mut buf), Ok(BoundedLine::Line)));
        assert_eq!(buf, format!("{}\n", "A".repeat(MAX_WIRE_LINE_BYTES - 1)));
        let mut invalid: &[u8] = b"\xff\xfe\r\n";
        assert!(read_bounded_line(&mut invalid, &mut buf).is_err());
    }

    #[test]
    fn local_transport_rejects_oversized_response_lines() -> Result<()> {
        use std::io::Write;
        let dir = private_temp_subdir("transport-flood-test").context("private directory")?;
        let socket = dir.join(format!("{}.sock", std::process::id()));
        let listener = std::os::unix::net::UnixListener::bind(&socket)?;
        let url = format!("http://transport-flood-{}", next_tmp_id());
        LOCAL_DAEMON_SOCKETS.get_or_init(Default::default).lock().unwrap().insert(url.clone(), socket);
        let server = std::thread::spawn(move || -> Result<()> {
            use std::io::BufRead;
            let (stream, _) = listener.accept()?;
            let mut reader = std::io::BufReader::new(stream);
            // Read the request head first (like the real daemon) so the client's
            // writes never race the adversarial response below.
            let mut line = String::new();
            loop {
                line.clear();
                if reader.read_line(&mut line).unwrap_or(0) == 0 || line.trim().is_empty() {
                    break;
                }
            }
            let mut w = std::io::BufWriter::new(reader.into_inner());
            // The client is expected to reject the response and hang up; ignore EPIPE.
            let _ = write!(w, "HTTP/1.1 200 OK\r\nX-Flood: {}\r\n\r\n", "A".repeat(MAX_WIRE_LINE_BYTES + 1));
            let _ = w.flush();
            Ok(())
        });
        let error = http_request_with_timeout_and_token(
            "POST", &format!("{url}/eval"), "application/json", b"{}", Some(5000), Some("test"), || {},
        )
        .err()
        .context("expected oversized response line rejection")?;
        assert!(error.to_string().contains("too large"), "{error}");
        server.join().unwrap()?;
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn local_transport_rejects_garbage_response_status_line() -> Result<()> {
        use std::io::Write;
        let dir = private_temp_subdir("transport-garbage-test").context("private directory")?;
        let socket = dir.join(format!("{}.sock", std::process::id()));
        let listener = std::os::unix::net::UnixListener::bind(&socket)?;
        let url = format!("http://transport-garbage-{}", next_tmp_id());
        LOCAL_DAEMON_SOCKETS.get_or_init(Default::default).lock().unwrap().insert(url.clone(), socket);
        let server = std::thread::spawn(move || -> Result<()> {
            use std::io::BufRead;
            let (stream, _) = listener.accept()?;
            let mut reader = std::io::BufReader::new(stream);
            // Read the request head first (like the real daemon) so the client's
            // writes never race the adversarial response below.
            let mut line = String::new();
            loop {
                line.clear();
                if reader.read_line(&mut line).unwrap_or(0) == 0 || line.trim().is_empty() {
                    break;
                }
            }
            let mut w = std::io::BufWriter::new(reader.into_inner());
            // The client is expected to reject the response and hang up; ignore EPIPE.
            let _ = write!(w, "garbage-without-status\r\n\r\n");
            let _ = w.flush();
            Ok(())
        });
        let error = http_request_with_timeout_and_token(
            "POST", &format!("{url}/eval"), "application/json", b"{}", Some(5000), Some("test"), || {},
        )
        .err()
        .context("expected garbage status line rejection")?;
        assert!(error.to_string().contains("status"), "{error}");
        server.join().unwrap()?;
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn local_transport_large_payload_roundtrip() -> Result<()> {
    use std::io::{Read, Write};
        let dir = private_temp_subdir("transport-test").context("private directory")?;
        let socket = dir.join(format!("{}.sock", std::process::id()));
        let listener = std::os::unix::net::UnixListener::bind(&socket)?;
        let url = format!("http://transport-test-{}", next_tmp_id());
        LOCAL_DAEMON_SOCKETS.get_or_init(Default::default).lock().unwrap().insert(url.clone(), socket);
        let bytes = vec![b'x'; 2 * 1024 * 1024];
        let expected = bytes.clone();
        let server = std::thread::spawn(move || -> Result<()> {
            let (stream, _) = listener.accept()?;
            let mut reader = std::io::BufReader::new(stream);
            let mut line = String::new();
            let mut tag = None;
            loop {
                line.clear();
                reader.read_line(&mut line)?;
                if line.trim().is_empty() { break; }
                if let Some(value) = line.strip_prefix("X-Turbo-Shm: ") { tag = Some(value.trim().to_string()); }
            }
            assert_eq!(LocalPayload::read(tag.as_deref().context("missing shared frame")?)?, expected);
            let payload = LocalPayload::create(&expected)?;
            write!(reader.get_mut(), "HTTP/1.1 200 OK\r\nContent-Length: 0\r\nX-Turbo-Shm: {}\r\n\r\n", payload.tag())?;
            let mut ack = [0];
            reader.read_exact(&mut ack)?;
            assert_eq!(ack, [1]);
            Ok(())
        });
        let start = std::time::Instant::now();
        let reply = http_request_with_timeout_and_token("POST", &format!("{url}/eval"), "application/json", &bytes, Some(5000), Some("test"), || {})?;
        assert_eq!(reply, bytes);
        server.join().unwrap()?;
        eprintln!("shared framing roundtrip: {} bytes each direction in {} us", bytes.len(), start.elapsed().as_micros());
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn request_policy_is_canonical_and_covers_all_tags() {
        let mut env: std::collections::HashMap<String, String> = REQUEST_POLICY_KEYS.into_iter().map(|k| (k.into(), String::new())).collect();
        for key in REQUEST_POLICY_KEYS {
            env.insert(key.into(), " b,a,b ".into());
            assert_eq!(request_policy(&env)[key], "a,b");
            env.insert(key.into(), String::new());
        }
        assert_eq!(request_policy(&env).len(), 4);
    }

    #[test]
    fn daemon_discovery_ignores_request_policy_but_workers_do_not() -> Result<()> {
        let dir = private_temp_subdir("policy-identity-test").context("private directory")?;
        let store = TurboStore::open(Some(&dir))?;
        let daemon = current_exe_daemon_paths(&store).context("daemon paths")?.4;
        let mut env: std::collections::HashMap<String, String> = REQUEST_POLICY_KEYS.into_iter().map(|k| (k.into(), String::new())).collect();
        let lean_bin = Path::new("/nonexistent-policy-test-lean");
        let base = resolve_zygote_context("policy-test", "", &env, lean_bin, "");
        for key in REQUEST_POLICY_KEYS {
            env.insert(key.into(), "Policy.permitted".into());
            let changed = resolve_zygote_context("policy-test", "", &env, lean_bin, "");
            assert_ne!(base.closure_pool_digest, changed.closure_pool_digest, "{key}");
            assert_ne!(base.identity, changed.identity, "{key}");
            assert_eq!(daemon, current_exe_daemon_paths(&store).unwrap().4);
            env.insert(key.into(), String::new());
        }
        drop(store);
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn readonly_mode_does_not_authorize_live_source_hardlinks() -> Result<()> {
        use std::os::unix::fs::PermissionsExt;
        let dir = private_temp_subdir("immutable-link-test").context("private directory")?;
        let src = dir.join("source.olean");
        let dst = dir.join("snapshot.olean");
        fs::write(&src, b"immutable only by mode")?;
        fs::set_permissions(&src, fs::Permissions::from_mode(0o444))?;
        let hash = blake3::hash(b"immutable only by mode").to_hex().to_string();
        assert!(!link_immutable_snapshot_file(&src, &dst, &hash).unwrap());
        assert!(!dst.exists());
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn test_finish_check_shard_request_rejection_is_final() {
        let http = |e: &str| {
            finish_check_shard_request(Err(anyhow::anyhow!(
                "HTTP request POST http://127.0.0.1:1/check-shard failed (HTTP 500): {{\"status\":\"error\",\"error\":\"{}\"}}",
                e
            )))
        };
        let err = http("Remote `lean` shard verification failed for `t`").unwrap_err();
        assert!(err
            .to_string()
            .starts_with("Remote `lean` shard verification failed"));
        // Only the structured code means unavailable, never text the shard can put in a message.
        assert!(http("Zygote import unavailable for `«Zygote import unavailable»`").is_err());
        assert!(matches!(
            finish_check_shard_request(Err(anyhow::anyhow!(
                "HTTP request POST http://127.0.0.1:1/check-shard failed (HTTP 500): {{\"status\":\"error\",\"error\":\"x\",\"code\":\"{}\"}}",
                IMPORT_UNAVAILABLE_CODE
            ))),
            Ok(None)
        ));
        assert!(matches!(
            finish_check_shard_request(Err(std::io::Error::from(
                std::io::ErrorKind::ConnectionRefused
            )
            .into())),
            Ok(None)
        ));
    }

    #[test]
    fn test_finish_eval_http_request_fails_closed_on_errors_and_crash_replies() {
        let http_409 = finish_eval_http_request(Err(anyhow::anyhow!(
            "HTTP request POST http://127.0.0.1:1/eval failed (HTTP 409): {{\"ok\":false,\"error\":\"eval execution identity changed\"}}"
        )))
        .unwrap_err();
        assert_eq!(http_409.to_string(), "eval execution identity changed");
        let http_err = finish_eval_http_request(Err(anyhow::anyhow!(
            "HTTP request POST http://127.0.0.1:1/eval failed (HTTP 500): {{\"ok\":false,\"error\":\"internal daemon failure\"}}"
        )))
        .unwrap_err();
        assert_eq!(http_err.to_string(), "internal daemon failure");
        assert!(finish_eval_http_request(Ok(b"{\"ok\":false}".to_vec())).is_err());
        let server_crash = serde_json::to_vec(&serde_json::json!({
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
            "error": "worker pool failed",
            "errors": ["worker pool failed"],
            "timed_out": false,
            "crashed": true,
            "deterministic": false
        }))
        .unwrap();
        let rep = finish_eval_http_request(Ok(server_crash))
            .unwrap()
            .expect("server crash payload must parse as a crash reply");
        assert!(rep.crashed && !rep.ok && !rep.import_ok);
        assert_eq!(rep.errors, vec!["worker pool failed"]);
        assert!(matches!(
            finish_eval_http_request(Err(std::io::Error::from(
                std::io::ErrorKind::ConnectionRefused
            )
            .into())),
            Ok(None)
        ));
    }

    /// A user `macro_rules` that makes Lean 4.35's `#print axioms` report no axioms.
    pub(crate) const PRINT_AXIOMS_SPOOF: &str = "macro_rules\n  | `(#print axioms $i:ident) => `(#eval IO.println s!\"'{$(Lean.quote i.getId.toString)}' does not depend on any axioms\")\n";

    #[test]
    fn test_certification_admission_checks_worker_prefixes_and_candidates() -> Result<()> {
        let dir = std::env::temp_dir().join(format!("turbo_source_admission_{}", next_tmp_id()));
        let store = TurboStore::open(Some(&dir))?;
        let env = std::collections::HashMap::new();
        for source in [
            "set_option debug.skipKernelTC true",
            "run_cmd pure ()",
            "run_meta pure ()",
        ] {
            let error = eval_with_zygote_pool_with_args(
                &store,
                "test",
                "",
                &env,
                Path::new("lean"),
                source,
                false,
                &[],
            )
            .unwrap_err();
            assert!(format!("{error:#}").contains("checking-weakening"));
            for as_prefix in [false, true] {
                let prefix = if as_prefix { source } else { "" };
                let decls = vec![
                    if as_prefix {
                        "theorem good : True := True.intro"
                    } else {
                        source
                    }
                    .to_string();
                    2
                ];
                for race in [false, true] {
                    let result = if race {
                        eval_candidates_race_via_zygote(
                            &store,
                            "test",
                            "",
                            &env,
                            Path::new("lean"),
                            prefix,
                            &decls,
                            &[],
                        )
                    } else {
                        eval_subshards_batch_via_zygote(
                            &store,
                            "test",
                            "",
                            &env,
                            Path::new("lean"),
                            prefix,
                            &decls,
                            &[],
                        )
                    };
                    let error = result.unwrap_err();
                    assert!(
                        format!("{error:#}").contains("checking-weakening"),
                        "prefix={as_prefix}, race={race}: {error:#}"
                    );
                }
            }
        }
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn test_compiled_module_audit_replays_kernel_types() -> Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "turbo_raw_replay_{}_{}",
            std::process::id(),
            next_tmp_id()
        ));
        fs::create_dir_all(&dir)?;
        let store = TurboStore::open(Some(&dir.join("store")))?;
        let mut env = std::collections::HashMap::from([
            (
                "ELAN_TOOLCHAIN".to_string(),
                "leanprover/lean4:v4.35.0".to_string(),
            ),
            ("LEAN_PATH".to_string(), dir.display().to_string()),
        ]);
        let lean =
            crate::module_builder::ToolchainExecutables::resolve(&dir, "leanprover/lean4:v4.35.0")?
                .lean;
        let prefix = Command::new(&lean)
            .arg("--print-prefix")
            .envs(&env)
            .output()?;
        assert!(prefix.status.success());
        let prefix = String::from_utf8_lossy(&prefix.stdout).trim().to_string();
        env.insert(
            "LD_LIBRARY_PATH".into(),
            format!("{prefix}/lib/lean:{prefix}/lib"),
        );
        let auditor = ensure_zygote_binary(&store, &lean, &env)?;
        let bad = include_str!("../tests/fixtures/weakening-options/Bad.lean").replace(
            "import Lean\n",
            "import Lean\nset_option debug.skipKernelTC true\n",
        );
        for (module, source, accepted) in [
            (
                "BadArtifact",
                format!("{bad}\ntheorem uses_bad : False := bad\n"),
                false,
            ),
            (
                "GoodArtifact",
                "set_option maxHeartbeats 400000\ntheorem good : True := True.intro\n".to_string(),
                true,
            ),
        ] {
            let file = dir.join(format!("{module}.lean"));
            let olean = file.with_extension("olean");
            fs::write(&file, source)?;
            let compiled = Command::new(&lean)
                .envs(&env)
                .arg("-Ddebug.skipKernelTC=false")
                .arg("-R")
                .arg(&dir)
                .arg(&file)
                .arg("-o")
                .arg(&olean)
                .output()?;
            assert!(compiled.status.success() && olean.is_file(), "{compiled:?}");
            if !accepted {
                assert!(String::from_utf8_lossy(&compiled.stdout)
                    .contains("does not depend on any axioms"));
            }
            for shard in [false, true] {
                let mut command = Command::new(&auditor);
                command.envs(&env).arg("--audit-modules");
                if shard {
                    command.arg("--shard");
                }
                let audited = command.arg(module).output()?;
                let verdict = parse_audit_modules_reply(&audited, &[module.to_string()]);
                assert_eq!(
                    verdict.is_ok(),
                    accepted,
                    "{module}/shard={shard}: {audited:?}"
                );
                if !accepted {
                    assert!(format!("{:#}", verdict.unwrap_err())
                        .contains("independent kernel re-check"));
                }
            }
        }
        // Repeated independent imports used to exhaust the untrusted auditor's 8 GiB
        // limit, reported misleadingly as a missing .olean.private file (CI #301).
        let modules: Vec<String> = (0..8).map(|i| format!("Replay{i}")).collect();
        for module in &modules {
            let file = dir.join(format!("{module}.lean"));
            fs::write(
                &file,
                format!("import Lean\ntheorem good{module} : True := True.intro\n"),
            )?;
            let compiled = Command::new(&lean)
                .envs(&env)
                .arg("-R")
                .arg(&dir)
                .arg(&file)
                .arg("-o")
                .arg(file.with_extension("olean"))
                .output()?;
            assert!(compiled.status.success(), "{compiled:?}");
        }
        let mut command = Command::new(&auditor);
        command.envs(&env).arg("--audit-modules").args(&modules);
        let audited = crate::module_builder::run_command_with_timeout(
            &mut command,
            std::time::Duration::from_secs(120),
            true,
        )?;
        parse_audit_modules_reply(&audited, &modules)?;
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn test_audited_lean_shard_exempts_only_named_explicit_stubs() -> Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "turbo_audited_shard_{}_{}",
            std::process::id(),
            next_tmp_id()
        ));
        fs::create_dir_all(&dir)?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        let store = TurboStore::open(Some(&dir.join("store")))?;
        // Verifier commands take only absolute, installed toolchain executables.
        let lean =
            crate::module_builder::ToolchainExecutables::resolve(&dir, "leanprover/lean4:v4.35.0")?
                .lean;
        let env = std::collections::HashMap::from([(
            "ELAN_TOOLCHAIN".to_string(),
            "leanprover/lean4:v4.35.0".to_string(),
        )]);
        let run = |src: &str| {
            let audit = std::collections::HashSet::from(["tgt".to_string()]);
            run_audited_lean_shard(&store, &lean, &env, Some(&dir), src, &audit, &[], None)
        };
        let stubs = "namespace N\ntheorem s1 (n : Nat) {m : Nat} : n + m = m + n := sorry\ntheorem s2 : 1 = 1 := sorry\nend N\nnamespace M\ntheorem s2 : 2 = 2 := sorry\nend M\n";
        // Host-named prefix stubs (binders, namespaces, a short name used twice) are exempt; the
        // target is audited.
        let ok = run(&format!(
            "{}theorem N.tgt (a b : Nat) : a + b = b + a := N.s1 a\ntheorem other : 2 = 2 := M.s2\n",
            stubs
        ))?;
        assert!(ok.status.success(), "{:?}", ok);
        let reject = |src: String, why: &str, needle: &str| {
            let err = run(&src).expect_err(why);
            assert!(format!("{:#}", err).contains(needle), "{}: {:#}", why, err);
        };
        reject(
            "theorem tgt : 1 = 1 := sorry\n".into(),
            "an audited theorem is never a stub",
            "disallowed axiom `sorryAx`",
        );
        // Cross-namespace `Evil.s1` no longer collides with root-anchored `_root_.N.s1` / `_root_.s1`
        // stubs and is rejected directly as an unexempt `sorryAx`; a macro-injected second `N.s1`
        // inside the same namespace is rejected as an ambiguous `_root_.N.s1` stub.
        reject(
            format!(
                "import Lean\n{}theorem Evil.s1 : False := by\n  run_tac do\n    let g ← Lean.Elab.Tactic.getMainGoal\n    g.assign (← Lean.Meta.mkSorry (← g.getType) false)\ntheorem tgt : False := Evil.s1\n",
                stubs
            ),
            "cross-namespace sorry is not exempted by N.s1 stub",
            "disallowed axiom `sorryAx`",
        );
        reject(
            format!(
                "import Lean\n{}\nopen Lean Elab Command in\nelab \"inject_s1\" : command => liftCoreM do\n  addDecl <| .thmDecl {{ name := mkPrivateNameCore `Other `N.s1, levelParams := [], type := mkConst ``False, value := mkApp2 (mkConst ``sorryAx [0]) (mkConst ``False) (mkConst ``Bool.false) }}\n  addDecl <| .thmDecl {{ name := `tgt, levelParams := [], type := mkConst ``False, value := mkConst (mkPrivateNameCore `Other `N.s1) }}\ninject_s1\n",
                "namespace N\nmacro_rules | `(term| sorry) => `(term| trivial)\ntheorem s1 : True := sorry\nend N\n"
            ),
            "a root-anchored stub turned into a proof cannot lend its name to a same-namespace injected sorry",
            "prefix stub `_root_.N.s1` is ambiguous",
        );
        reject(
            "import Lean\nmacro_rules | `(term| sorry) => `(term| trivial)\ntheorem s1 : True := sorry\ntheorem Evil.s1 : False := by\n  run_tac do\n    let g ← Lean.Elab.Tactic.getMainGoal\n    g.assign (← Lean.Meta.mkSorry (← g.getType) false)\ntheorem tgt : False := Evil.s1\n".into(),
            "a root stub turned into a proof cannot lend its name to an injected sorry",
            "declaration `Evil.s1`",
        );
        reject(
            "import Lean\nnamespace N\nmacro_rules | `(term| sorry) => `(term| trivial)\ntheorem s1 : True := sorry\nend N\nopen Lean in\n#eval show Elab.Command.CommandElabM Unit from Elab.Command.liftCoreM do\n  let pn := mkPrivateNameCore `Other `N.s1\n  addDecl <| .thmDecl { name := pn, levelParams := [], type := mkConst ``False, value := mkApp2 (mkConst ``sorryAx [0]) (mkConst ``False) (mkConst ``false) }\n  addDecl <| .thmDecl { name := `tgt, levelParams := [], type := mkConst ``False, value := mkConst pn }\n".into(),
            "an addDecl-injected private theorem with the same user name is ambiguous",
            "prefix stub `_root_.N.s1` is ambiguous",
        );
        reject(
            "theorem other : 1 = 1 := rfl\n".into(),
            "the audited theorem must be declared",
            "missing from the compiled shard",
        );
        // P0-3: the verdict never comes from shard-controlled output (`#print axioms` spoofed by a
        // user macro), and `addDecl`-made axioms are seen in the kernel environment.
        reject(
            format!(
                "import Lean\n{}theorem tgt : 1 = 1 := by\n  run_tac Lean.Elab.admitGoal (← Lean.Elab.Tactic.getMainGoal)\n",
                PRINT_AXIOMS_SPOOF
            ),
            "a metaprogram sorry under a `#print axioms` spoof",
            "disallowed axiom `sorryAx`",
        );
        reject(
            "import Lean\nopen Lean in\n#eval show Elab.Command.CommandElabM Unit from Elab.Command.liftCoreM <| addDecl <| .axiomDecl { name := `hidden, levelParams := [], type := mkConst ``False, isUnsafe := false }\ntheorem tgt : 1 = 1 := (hidden).elim\n".into(),
            "an `addDecl` axiom",
            "`hidden`",
        );
        // The stock compiler can emit an axiom-free, ill-typed theorem when source options
        // disable checking. The artifact auditor must replay it, rather than trust imports.
        let bad = include_str!("../tests/fixtures/weakening-options/Bad.lean").replace(
            "import Lean\n",
            "import Lean\nset_option debug.skipKernelTC true\n",
        );
        reject(
            format!("{bad}\ntheorem tgt : False := bad\n"),
            "source-level options cannot weaken the artifact audit",
            "independent kernel re-check",
        );
        assert!(!run("theorem tgt : 1 = 2 := rfl\n")?.status.success());
        // A request budget bounds the whole fallback; it never yields a late verdict.
        let audit = std::collections::HashSet::from(["tgt".to_string()]);
        let late = run_audited_lean_shard(
            &store,
            &lean,
            &env,
            Some(&dir),
            "theorem tgt : 1 = 1 := rfl\n",
            &audit,
            &[],
            Some(1),
        );
        assert!(
            !matches!(late, Ok(ref o) if o.status.success()),
            "{:?}",
            late
        );
        // Auditor preparation (a cold auditor build in a fresh store) stays within the budget.
        let cold = TurboStore::open(Some(&dir.join("cold-store")))?;
        let t0 = std::time::Instant::now();
        let _ = run_audited_lean_shard(
            &cold,
            &lean,
            &env,
            Some(&dir),
            "theorem tgt : 1 = 1 := rfl\n",
            &audit,
            &[],
            Some(3_000),
        );
        assert!(t0.elapsed() < std::time::Duration::from_secs(15));
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[cfg(target_os = "linux")]
    fn open_test_lifecycle_process(
        child: &mut std::process::Child,
        staging: Option<&Path>,
    ) -> LifecycleProcess {
        // spawn's exec handshake can precede the final /proc identity becoming readable.
        // Establish a stable baseline before testing deliberate identity changes.
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(2);
        loop {
            if let Some(process) = LifecycleProcess::open(child.id(), staging, None) {
                std::thread::sleep(std::time::Duration::from_millis(5));
                if process.valid_identity() {
                    return process;
                }
            }
            assert!(
                child.try_wait().unwrap().is_none(),
                "test child exited before identity validation"
            );
            if std::time::Instant::now() >= deadline {
                let pid = child.id();
                let exe = fs::read_link(format!("/proc/{pid}/exe"));
                let start = process_start_time(pid);
                let _ = child.kill();
                let _ = child.wait();
                panic!("test child identity not ready: pid={pid}, exe={exe:?}, start={start:?}");
            }
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
    }

    #[test]
    #[cfg(target_os = "linux")]
    fn test_pidfd_revalidates_start_time_and_identity_before_signaling() {
        let dir = std::env::temp_dir().join(format!("turbo-pidfd-{}", next_tmp_id()));
        fs::create_dir_all(&dir).unwrap();
        let exe = dir.join("turbo_zygote_pidfd_test");
        fs::copy("/bin/bash", &exe).unwrap();
        let mut child = std::process::Command::new(&exe)
            .args(["-c", "read -t 30"])
            .env("TURBO_LEAN_STAGING_DIR", &dir)
            .stdin(std::process::Stdio::piped())
            .spawn()
            .unwrap();
        let mut process = open_test_lifecycle_process(&mut child, Some(&dir));
        process.start_time += 1;
        assert!(
            !process.signal(libc::SIGTERM),
            "changed start time must refuse SIGTERM"
        );
        assert!(
            !process.signal(libc::SIGKILL),
            "changed start time must refuse SIGKILL"
        );
        assert!(child.try_wait().unwrap().is_none());
        process.start_time -= 1;
        process.identity.1.push(b'x');
        assert!(
            !process.signal(libc::SIGKILL),
            "changed cmdline must refuse SIGKILL"
        );
        process.identity.1.pop();
        assert!(process.signal(libc::SIGTERM));
        child.wait().unwrap();
        assert!(!process.alive());
        assert!(
            !process.signal(libc::SIGKILL),
            "held pidfd must reject an exited process"
        );
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    #[cfg(target_os = "linux")]
    fn test_multi_namespace_teardown_cleans_every_killed_namespace() {
        let lifecycle = lifecycle_exclusive_lock().unwrap();
        let mut children = Vec::new();
        let mut processes = Vec::new();
        let mut dirs = Vec::new();
        for _ in 0..2 {
            let dir = std::env::temp_dir().join(format!("turbo-stop-namespace-{}", next_tmp_id()));
            fs::create_dir_all(&dir).unwrap();
            let exe = dir.join("turbo_zygote_stop_test");
            fs::copy("/bin/bash", &exe).unwrap();
            let mut child = Command::new(exe)
                .args(["-c", "read -t 30"])
                .env("TURBO_LEAN_STAGING_DIR", &dir)
                .stdin(std::process::Stdio::piped())
                .spawn()
                .unwrap();
            // Same user-wide (staging=None) identity path, with an explicit candidate set
            // so this test cannot affect any developer's live daemons.
            processes.push(open_test_lifecycle_process(&mut child, None));
            children.push(child);
            dirs.push(dir);
        }
        let cleanup = terminate_linux_processes(processes);
        for child in &mut children {
            child.wait().unwrap();
        }
        assert_eq!(cleanup.count, 2);
        assert_eq!(cleanup.staging.len(), 2);
        assert_eq!(
            cleanup_lifecycle_staging(cleanup, None, &lifecycle).unwrap(),
            2
        );
        assert!(dirs.iter().all(|dir| !dir.exists()));
    }

    #[test]
    #[cfg(unix)]
    fn test_portable_pidfile_sigterm_fallback() {
        use std::os::unix::process::CommandExt;
        let dir = std::env::temp_dir().join(format!("turbo-pidfile-{}", next_tmp_id()));
        fs::create_dir_all(&dir).unwrap();
        let exe = dir.join("turbo-lean");
        fs::copy("/bin/bash", &exe).unwrap();
        fs::write(dir.join("serve"), "read -t 30\n").unwrap();
        let mut child = Command::new(&exe)
            .arg("serve")
            .current_dir(&dir)
            .env("TURBO_LEAN_DAEMON", "1")
            .stdin(std::process::Stdio::piped())
            .process_group(0)
            .spawn()
            .unwrap();
        let state = dir.join("zygote_daemon.json");
        let info = LocalZygoteDaemonInfo {
            addr: String::new(),
            pid: child.id(),
            exe_mtime_sec: 0,
            exe_mtime_nsec: 0,
            auth_token: String::new(),
            policy: vec![],
            build_epoch: crate::TURBO_LEAN_BUILD_EPOCH.to_string(),
        };
        fs::write(&state, serde_json::to_vec(&info).unwrap()).unwrap();
        let mut identity = portable_process_identity(child.id())
            .unwrap()
            .expect("portable identity");
        identity.start_time.push_str(" changed");
        assert!(!signal_portable_process(child.id(), &identity, libc::SIGTERM).unwrap());
        identity = portable_process_identity(child.id()).unwrap().unwrap();
        identity.command.push_str(" changed");
        assert!(!signal_portable_process(child.id(), &identity, libc::SIGKILL).unwrap());
        assert!(child.try_wait().unwrap().is_none());
        assert!(portable_staging_namespace_in_use(&dir, Some(&dir)));
        assert_eq!(stop_pidfile_daemons(&dir, Some(&dir)).unwrap().count, 1);
        assert!(!child.wait().unwrap().success());
        assert!(!stop_pidfile_daemon(&state).unwrap());
        assert!(!portable_staging_namespace_in_use(&dir, Some(&dir)));
        // A live PID without the daemon identity must not be killed, nor may its
        // state file or staging be deleted. Malformed state is conservative too.
        let mut foreign = Command::new("sleep").arg("30").spawn().unwrap();
        let foreign_info = LocalZygoteDaemonInfo {
            pid: foreign.id(),
            ..info
        };
        fs::write(&state, serde_json::to_vec(&foreign_info).unwrap()).unwrap();
        let cleanup = stop_pidfile_daemons(&dir, Some(&dir)).unwrap();
        assert_eq!(cleanup.count, 0);
        assert!(!cleanup.state_files.contains(&state));
        assert!(portable_staging_namespace_in_use(&dir, Some(&dir)));
        // A legacy PID file outside an otherwise empty staging namespace still
        // vetoes deletion, even though scoped signalling must spare that PID.
        let empty_staging = dir.join("empty-staging");
        fs::create_dir_all(&empty_staging).unwrap();
        assert!(portable_staging_namespace_in_use(
            &empty_staging,
            Some(&dir)
        ));
        assert!(foreign.try_wait().unwrap().is_none());
        foreign.kill().unwrap();
        foreign.wait().unwrap();
        assert!(!portable_staging_namespace_in_use(&dir, Some(&dir)));
        fs::write(&state, "invalid state").unwrap();
        assert!(portable_staging_namespace_in_use(&dir, Some(&dir)));
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn test_closed_daemon_transport_is_recoverable() {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let url = format!("http://{}/check-shard", listener.local_addr().unwrap());
        let server = std::thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            let mut byte = [0];
            let _ = std::io::Read::read(&mut stream, &mut byte);
            // Expiry can close admission before a response is written.
        });
        let err = http_request_with_timeout_and_token(
            "POST",
            &url,
            "application/json",
            b"{}",
            Some(1000),
            None,
            || {},
        )
        .unwrap_err();
        assert!(is_expired_daemon_transport_error(&err), "{err:#}");
        assert!(finish_check_shard_request(Err(err)).unwrap().is_none());
        server.join().unwrap();
        let err = http_request_with_timeout_and_token(
            "POST",
            &url,
            "application/json",
            b"{}",
            Some(1000),
            None,
            || {},
        )
        .unwrap_err();
        assert!(is_expired_daemon_transport_error(&err), "{err:#}");
        assert!(finish_check_shard_request(Err(err)).unwrap().is_none());
        assert!(!is_expired_daemon_transport_error(&anyhow::anyhow!(
            "HTTP 500: proof failed"
        )));
    }

    #[test]
    fn test_daemon_stop_recognizes_the_serve_subcommand_only() {
        for args in [
            b"turbo-lean\0serve\0".as_slice(),
            b"turbo-lean\0--cache-dir\0/tmp/cas\0--json\0serve\0--listen\x00127.0.0.1:9400\0"
                .as_slice(),
        ] {
            assert!(is_serve_command(args));
        }
        for args in [
            b"turbo-lean\0check\0File.lean\0--decl\0serve\0".as_slice(),
            b"turbo-lean\0--cache-dir\0serve\0check\0File.lean\0".as_slice(),
        ] {
            assert!(!is_serve_command(args));
        }
    }

    fn repo_lean_cfg() -> Option<crate::module_builder::ProjectConfig> {
        let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean");
        dir.join(".lake/packages/lean-sys/LeanSys/Posix.lean")
            .is_file()
            .then(|| crate::module_builder::resolve_project_config(&dir).ok())
            .flatten()
    }

    #[cfg(unix)]
    #[test]
    fn local_eval_cache_tracks_environment_lean_path() -> Result<()> {
        use crate::worktree_test_support::LakeTree;
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tree = LakeTree::new("eval_env_path", &[("P/A.lean", "def value : Nat := 0\n")])?;
        let cfg = crate::module_builder::resolve_project_config(&tree.project)?;
        for (name, value) in [("A", 17), ("B", 29)] {
            let dir = tree.root.join(name);
            fs::create_dir_all(&dir)?;
            fs::write(
                dir.join("Dep.lean"),
                format!("def Dep.value : Nat := {value}\n"),
            )?;
            let out = Command::new(&cfg.lean_bin)
                .current_dir(&dir)
                .args(["-o", "Dep.olean", "Dep.lean"])
                .output()?;
            anyhow::ensure!(
                out.status.success(),
                "{}{}",
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            );
        }
        let store = TurboStore::open(Some(&tree.root.join("cache")))?;
        let previous = std::env::var_os("TURBO_LEAN_NO_DAEMON");
        std::env::set_var("TURBO_LEAN_NO_DAEMON", "1");
        let result = (|| -> Result<()> {
            let source = "import Dep\n#eval Dep.value\n";
            let file = tree.project.join("Eval.lean").to_string_lossy().to_string();
            for (name, expected) in [("A", "17"), ("A", "17"), ("B", "29"), ("B", "29")] {
                let env = std::collections::HashMap::from([(
                    "LEAN_PATH".into(),
                    tree.root.join(name).to_string_lossy().to_string(),
                )]);
                let reply = try_local_zygote_eval_with_args(
                    &store,
                    &env,
                    &cfg.lean_bin,
                    &cfg.toolchain,
                    "",
                    source,
                    Some(&file),
                    60_000,
                    &[],
                )?
                .context("local eval must produce a reply")?;
                assert!(reply.ok && reply.import_ok, "{reply:?}");
                assert_eq!(
                    reply.messages.concat().trim(),
                    expected,
                    "LEAN_PATH={name}: {reply:?}"
                );
            }
            // Replacing an artifact at the same resolved path must also invalidate the reply.
            fs::copy(tree.root.join("A/Dep.olean"), tree.root.join("B/Dep.olean"))?;
            let env = std::collections::HashMap::from([(
                "LEAN_PATH".into(),
                tree.root.join("B").to_string_lossy().to_string(),
            )]);
            let reply = try_local_zygote_eval_with_args(
                &store,
                &env,
                &cfg.lean_bin,
                &cfg.toolchain,
                "",
                source,
                Some(&file),
                60_000,
                &[],
            )?
            .context("replaced import eval")?;
            assert!(reply.ok && reply.import_ok, "{reply:?}");
            assert_eq!(reply.messages.concat().trim(), "17", "{reply:?}");
            Ok(())
        })();
        if let Some(value) = previous {
            std::env::set_var("TURBO_LEAN_NO_DAEMON", value);
        } else {
            std::env::remove_var("TURBO_LEAN_NO_DAEMON");
        }
        result
    }

    #[test]
    fn local_eval_rejects_invalid_args_before_empty_option_cache_hit() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir =
            std::env::temp_dir().join(format!("turbo_eval_options_{}", crate::pack::next_tmp_id()));
        let store = TurboStore::open(Some(&dir))?;
        let source = "#eval 17305\n";
        let file_name = dir.join("Cached.lean").to_string_lossy().to_string();
        let cwd = std::env::current_dir()?.to_string_lossy().to_string();
        let (imports_csv, _) = split_shard_for_zygote(source);
        let context = resolve_zygote_context(
            "test",
            "",
            &std::collections::HashMap::new(),
            Path::new("/no-lean-needed"),
            &imports_csv,
        );
        let filename =
            compute_eval_shm_cache_filename(&context, &file_name, Some(&cwd), source, &[])?;
        let cache_dir = store.fast_staging_dir().join("eval_shm_cache");
        crate::shm_cache::ensure_private_dir_all(&cache_dir)?;
        let path = cache_dir.join(filename);
        let reply = ZygoteEvalReply {
            ok: true,
            import_ok: true,
            scanner_version: ZYGOTE_SCANNER_VERSION,
            replay_version: ZYGOTE_REPLAY_VERSION,
            stdout: "empty-option-cached-reply".into(),
            ..Default::default()
        };
        let bytes = serde_json::to_vec(&reply)?;
        crate::shm_cache::atomic_write_shm(&path, &bytes)?;
        let eval = |args: &[String]| {
            try_local_zygote_eval_with_args(
                &store,
                &std::collections::HashMap::new(),
                Path::new("/no-lean-needed"),
                "test",
                "",
                source,
                Some(&file_name),
                1000,
                args,
            )
        };
        let cached = eval(&[])?.expect("fixture must hit the empty-option cache");
        assert!(cached.ok && cached.env_cache_hit && cached.prefix_cache_hit);
        assert_eq!(cached.stdout, reply.stdout);
        for invalid in ["--plugin=bad.so", "--json", "-q", " -DautoImplicit=false "] {
            let rejected =
                eval(&[invalid.to_string()])?.expect("invalid options return a final rejection");
            assert!(
                !rejected.ok && !rejected.env_cache_hit && !rejected.prefix_cache_hit,
                "invalid argument must not reuse cached reply: {invalid}: {rejected:?}"
            );
            assert!(rejected.errors.join("\n").contains(invalid), "{rejected:?}");
            assert_ne!(rejected.stdout, reply.stdout);
        }
        assert_eq!(fs::read(&path)?, bytes);
        fs::remove_file(path)?;
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn test_pinned_ffi_allow_args_admits_exact_pinned_lean_sys() {
        let Some(cfg) = repo_lean_cfg() else { return };
        let args = pinned_ffi_allow_args(&cfg, &["LeanSys.Posix".to_string()]);
        assert_eq!(args.len(), 8, "{args:?}");
        assert!(args.contains(
            &"--ffi-allow=LeanSys.Posix=LeanSys.Posix.rawWriteAll=leansys_write_all".to_string()
        ));
        assert!(pinned_ffi_allow_args(&cfg, &["TurboLean.Spec".to_string()]).is_empty());
    }

    #[test]
    fn test_project_ffi_allow_args_scopes_to_audited_modules() {
        let args = parse_project_ffi_allow(
            " App.Posix=App.Posix.getpid=app_getpid, Other.M=Other.M.f=f_sym,bad=entry, A=B=C=D ",
            &["App.Posix".to_string()],
        );
        assert_eq!(args, vec!["--ffi-allow=App.Posix=App.Posix.getpid=app_getpid".to_string()]);
    }

    #[test]
    fn test_pinned_ffi_allow_args_rejects_unpinned_or_path_dependency() {
        let Some(cfg) = repo_lean_cfg() else { return };
        let mods = ["LeanSys.Posix".to_string()];
        let mut bad_rev = cfg.clone();
        bad_rev
            .manifest_packages
            .iter_mut()
            .for_each(|p| p.rev = Some("0".repeat(40)));
        assert!(pinned_ffi_allow_args(&bad_rev, &mods).is_empty());
        let mut path_dep = cfg.clone();
        path_dep
            .manifest_packages
            .iter_mut()
            .for_each(|p| p.pkg_type = "path".into());
        assert!(pinned_ffi_allow_args(&path_dep, &mods).is_empty());
        let mut bad_url = cfg.clone();
        bad_url
            .manifest_packages
            .iter_mut()
            .for_each(|p| p.url = Some("https://example.invalid/lean-sys.git".into()));
        assert!(pinned_ffi_allow_args(&bad_url, &mods).is_empty());
        let mut in_tree = cfg.clone();
        in_tree.dep_pkgs.clear();
        assert!(pinned_ffi_allow_args(&in_tree, &mods).is_empty());
    }

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

    fn open_test_zygote_env(
        tag: &str,
    ) -> Option<(
        PathBuf,
        TurboStore,
        std::collections::HashMap<String, String>,
        PathBuf,
    )> {
        let tmp_dir = std::env::temp_dir().join(format!("turbo_zygote_{}_{}", tag, next_tmp_id()));
        let _ = fs::create_dir_all(&tmp_dir);
        let store = TurboStore::open(Some(&tmp_dir)).expect("open store");
        let (mut env_vars, lean_bin) =
            crate::pack::resolve_server_lean_env_and_bin(&store, "leanprover/lean4:v4.35.0", "")
                .unwrap();
        env_vars.insert(
            "LEAN_PATH".to_string(),
            tmp_dir.to_string_lossy().to_string(),
        );
        if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
            let _ = fs::remove_dir_all(&tmp_dir);
            return None;
        }
        // Fixture setup compiles the worker before any request's deadline begins.
        ensure_zygote_binary(&store, &lean_bin, &env_vars).expect("prepare test worker");
        Some((tmp_dir, store, env_vars, lean_bin))
    }

    #[test]
    fn test_zygote_prefix_checkpoint_instant_rollback() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("test") else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";
        let isolated_lp = tmp_dir.to_string_lossy().to_string();

        let shared_prefix = "namespace PrefixBench\nstructure PairState where\n  x : Nat\n  y : Nat\n  deriving DecidableEq\n\ndef swapPair (s : PairState) : PairState :=\n  { x := s.y, y := s.x }\n\ntheorem swapPair_involutive (s : PairState) : swapPair (swapPair s) = s := by\n  cases s\n  rfl\n";
        let run_pool = |shard: &str| {
            eval_with_zygote_pool(
                &store,
                toolchain,
                &isolated_lp,
                &env_vars,
                &lean_bin,
                shard,
                false,
            )
            .unwrap()
        };

        let rep_bad = run_pool(&format!(
            "{}\ntheorem cand_bad (s : PairState) : swapPair s = s := rfl\n",
            shared_prefix
        ));
        assert!(rep_bad.import_ok && !rep_bad.ok && !rep_bad.errors.is_empty());
        let joined_bad_errs = rep_bad.errors.join("\n");
        assert!(
            joined_bad_errs.contains("<zygote-decl>:14:"),
            "Expected line 14 in error: {}",
            joined_bad_errs
        );

        let max_elab_us: u64 = if cfg!(debug_assertions) {
            100_000
        } else {
            25_000
        };
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
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("kgate_test") else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";

        let prefix_src = "theorem prior_lem : True := sorry\n";
        let sneaky_shard = format!("{}\nmacro \"stealth_sorry\" : tactic => `(tactic| sorry)\ntheorem sneaky_thm : 1 = 2 := by stealth_sorry\n", prefix_src);
        let rep_sneaky = eval_with_zygote_pool(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            &sneaky_shard,
            false,
        )
        .unwrap();
        assert!(!rep_sneaky.ok);
        let joined_errs = rep_sneaky.errors.join("\n");
        assert!(joined_errs.contains("KernelGate") || joined_errs.contains("sorry"));

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
        .unwrap();
        assert!(rep_clean.ok && rep_clean.kernel_gate_active);
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_zygote_kernel_gate_applies_axiom_allowlist() {
        let shard = "theorem nd : 2 ^ 3 = 8 := by native_decide\n";
        for (allow, expect_ok) in [("", false), ("Foo.*, *._native.native_decide.ax_*", true)] {
            let Some((tmp_dir, store, mut env_vars, lean_bin)) = open_test_zygote_env("axpol")
            else {
                return;
            };
            env_vars.insert(
                crate::splitter::ALLOWED_AXIOMS_ENV.to_string(),
                allow.to_string(),
            );
            let toolchain = "leanprover/lean4:v4.35.0";
            let rep =
                eval_with_zygote_pool(&store, toolchain, "", &env_vars, &lean_bin, shard, false)
                    .unwrap();
            assert_eq!(rep.ok, expect_ok, "allow={:?}: {:?}", allow, rep.errors);
            assert!(
                expect_ok
                    || rep
                        .errors
                        .join("\n")
                        .contains("nd._native.native_decide.ax_")
            );
            let _ = fs::remove_dir_all(&tmp_dir);
        }
    }

    #[test]
    fn test_zygote_bv_decide_finds_toolchain_cadical() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("cadical") else {
            return;
        };
        let shard = "import Std.Tactic.BVDecide\ntheorem bv (x y : BitVec 8) : (x &&& y) + (x ||| y) = x + y := by bv_decide\n";
        let rep = eval_with_zygote_pool(
            &store,
            "leanprover/lean4:v4.35.0",
            "",
            &env_vars,
            &lean_bin,
            shard,
            false,
        )
        .unwrap();
        // The SAT call succeeds (the default kernel gate then rejects the `bv_decide` axiom).
        let errs = rep.errors.join("\n");
        assert!(
            !errs.contains("cadical") && errs.contains("bv._native.bv_decide.ax_"),
            "{}",
            errs
        );
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    static LNC_TEST_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

    #[test]
    fn test_lean_native_core_persistent_worker_sub_millisecond_rpc() {
        let _guard = LNC_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let warmup = query_lean_native_core_worker("ping", None).unwrap();
        assert_eq!(
            (warmup["ok"].as_bool(), warmup["result"]["status"].as_str()),
            (Some(true), Some("pong"))
        );
        let _ = query_lean_native_core_worker("validate-tv", None);
        let _ = query_lean_native_core_worker("eval-cex", None);

        let methods = ["ping", "validate-tv", "verify-certs", "eval-cex"];
        let t0 = std::time::Instant::now();
        for idx in 0..20 {
            let method = methods[idx % methods.len()];
            let resp = query_lean_native_core_worker(method, None).unwrap();
            assert_eq!(resp["ok"].as_bool(), Some(true));
            let result = &resp["result"];
            match method {
                "ping" => assert_eq!(result["status"].as_str(), Some("pong")),
                "validate-tv" => assert_eq!(
                    (
                        result["allPassed"].as_bool(),
                        result["passedDecls"].as_u64()
                    ),
                    (Some(true), Some(8))
                ),
                "verify-certs" => assert_eq!(result["verified"].as_bool(), Some(true)),
                "eval-cex" => {
                    assert_eq!(result["certified"].as_bool(), Some(false));
                    assert_eq!(
                        result["overallAssurance"].as_str(),
                        Some("FallbackUnverified")
                    );
                    assert_eq!(result["certification"].as_str(), Some("unavailable"));
                    assert_eq!(result["falsePositives"].as_u64(), Some(1));
                }
                _ => unreachable!(),
            }
        }
        assert!(t0.elapsed().as_secs_f64() * 1000.0 / 20.0 < 5.0);

        let raw_pair =
            query_lean_native_core_worker("eval-cex", Some(r#"{"lhs":"0x1","rhs":"0x0"}"#))
                .unwrap();
        assert_eq!(raw_pair["result"]["certified"].as_bool(), Some(false));
        assert_eq!(raw_pair["result"]["falsePositives"].as_u64(), Some(1));
        assert_eq!(
            raw_pair["result"]["certification"].as_str(),
            Some("unavailable")
        );
        assert_eq!(
            raw_pair["result"]["reason"].as_str(),
            Some("statement_required")
        );
        let equal = query_lean_native_core_worker("eval-cex", Some(r#"{"lhs":"0x1","rhs":"0x1"}"#))
            .unwrap();
        assert_eq!(equal["result"]["certified"].as_bool(), Some(false));
        assert_eq!(equal["result"]["reason"].as_str(), Some("lhs_eq_rhs"));
        let garbage =
            query_lean_native_core_worker("eval-cex", Some(r#"{"lhs":"garbage","rhs":"0x0"}"#))
                .unwrap();
        assert_eq!(garbage["result"]["certified"].as_bool(), Some(false));
        assert_eq!(garbage["result"]["falsePositives"].as_u64(), Some(1));
        assert_eq!(
            garbage["result"]["reason"].as_str(),
            Some("missing_witness")
        );

        let bogus_extra = serde_json::json!({
            "decl": "good_u64_refl",
            "stmt_src": "theorem good_u64_refl (a : UInt64) : a = a := by rfl",
            "bindings": [["a", "0"]],
            "lhs": "0",
            "rhs": "1",
        })
        .to_string();
        let uncertified = query_lean_native_core_worker("eval-cex", Some(&bogus_extra)).unwrap();
        assert_eq!(uncertified["result"]["certified"], false);
        assert_eq!(
            uncertified["result"]["overallAssurance"],
            "FallbackUnverified"
        );
        assert_eq!(uncertified["result"]["falsePositives"], 1);

        if crate::lake_build::resolve_lean_bin(Path::new(".")).is_ok() {
            let genuine_extra = serde_json::json!({
                "decl": "bad_u64_add",
                "stmt_src": "theorem bad_u64_add (a : UInt64) : a + 1 = a := by sorry",
                "bindings": [["a", "0"]],
                "lhs": "1",
                "rhs": "0",
            })
            .to_string();
            let certified =
                query_lean_native_core_worker("eval-cex", Some(&genuine_extra)).unwrap();
            assert_eq!(certified["result"]["certified"], true);
            assert_eq!(
                certified["result"]["overallAssurance"],
                "VerifiedKernelProof"
            );
            assert_eq!(certified["result"]["certification"], "lean_kernel");
            assert_eq!(certified["result"]["falsePositives"], 0);
        }
    }

    #[test]
    fn test_measure_process_rss_mb_and_budget_detection() {
        let mut min_elapsed_us = u128::MAX;
        let mut rss_mb = 0;
        for _ in 0..3 {
            let t0 = std::time::Instant::now();
            rss_mb = measure_process_rss_mb(std::process::id());
            min_elapsed_us = min_elapsed_us.min(t0.elapsed().as_micros());
        }
        assert!((1..65_536).contains(&rss_mb));
        #[cfg(target_os = "linux")]
        assert!(min_elapsed_us < 50_000);
        let gov = crate::shm_cache::MemoryBudgetGovernor::detect();
        assert!(gov.budget_mb >= 1 && gov.worker_rss_limit_mb() >= 512);
    }

    #[test]
    fn test_zygote_multiple_import_sets_in_same_worker() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("multi_imp") else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";

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
        .unwrap();
        assert!(rep1.ok && rep1.import_ok);

        let rep2 = eval_with_zygote_pool_opts(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            "import Lean\ntheorem multi_imp_lean : 1 = 1 := rfl\n",
            false,
            false,
            None,
            None,
        )
        .unwrap();
        assert!(rep2.ok && rep2.import_ok);

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
        .unwrap();
        assert!(rep3.ok && rep3.env_cache_hit);
        let rep4 = eval_with_zygote_pool_opts(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            "import Lean\ntheorem multi_imp_lean_2 : 2 = 2 := rfl\n",
            false,
            false,
            None,
            None,
        )
        .unwrap();
        assert!(rep4.ok && rep4.env_cache_hit);
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_zygote_eval_mode_preserves_info_messages_and_sorry_strings() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("eval_info") else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";

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
        .unwrap();
        let joined_msgs = rep.messages.join("\n");
        assert!(
            rep.ok
                && rep.heartbeats > 0
                && joined_msgs.contains("RSGB_RESULT {\"name\":\"foo\",\"note\":\"sorry\"}")
                && joined_msgs.contains("42")
        );
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_compiler_failure_preserves_both_diagnostic_streams() {
        use std::os::unix::process::ExitStatusExt;
        let out = std::process::Output {
            status: std::process::ExitStatus::from_raw(256),
            stdout: b"source.lean: error: missing instance".to_vec(),
            stderr: b"compiler stderr".to_vec(),
        };
        let err = compiler_failure(Path::new("source.lean"), &out);
        let text = err.to_string();
        assert!(
            text.contains("source.lean: error: missing instance"),
            "{text}"
        );
        assert!(text.contains("compiler stderr"), "{text}");
    }

    #[test]
    fn test_exhausted_budget_does_not_spawn_fallback() {
        let started = std::time::Instant::now() - std::time::Duration::from_secs(1);
        let remaining = remaining_timeout_ms(Some(100), started);
        assert_eq!(remaining, 0);
        let err = run_lean_command(&mut Command::new("must-not-be-spawned"), Some(remaining))
            .unwrap_err();
        assert!(err.to_string().contains("timed out"), "{err}");

        assert_eq!(audit_timeout_ms(true), 120_000);
        assert_eq!(audit_timeout_ms(false), 300_000);
        let expired_audit = std::time::Instant::now() - std::time::Duration::from_secs(301);
        assert_eq!(decl_identity_reader_budget_ms(true, Some(expired_audit)), 0);
        assert_eq!(
            decl_identity_reader_budget_ms(false, Some(expired_audit)),
            0
        );
    }

    #[test]
    fn test_zygote_timeout_kills_infinite_eval_and_recovers() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("timeout") else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";

        assert!(
            eval_with_zygote_pool_opts(
                &store,
                toolchain,
                "",
                &env_vars,
                &lean_bin,
                "#eval 1 + 1\n",
                false,
                true,
                Some("warm.lean"),
                Some(10_000)
            )
            .unwrap()
            .ok
        );

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
        .unwrap();
        assert!(
            rep_timeout.timed_out
                && !rep_timeout.ok
                && t0.elapsed() < std::time::Duration::from_secs(2)
        );

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
        .unwrap();
        assert!(
            rep_after.ok
                && !rep_after.timed_out
                && rep_after.messages.iter().any(|m| m.contains("123"))
        );
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_zygote_olean_digest_changes_when_olean_modified() {
        let tmp_dir =
            std::env::temp_dir().join(format!("turbo_zygote_olean_dig_{}", next_tmp_id()));
        let mod_dir = tmp_dir.join("Foo");
        let _ = fs::create_dir_all(&mod_dir);
        let olean_path = mod_dir.join("Bar.olean");
        fs::write(&olean_path, b"olean-version-1").unwrap();

        let lp = tmp_dir.to_string_lossy().to_string();
        let d1 = compute_imported_oleans_digest("Foo.Bar", &lp);
        assert_eq!(d1, compute_imported_oleans_digest("Foo.Bar", &lp));
        let sp1 = compute_search_path_oleans_digest(&lp);
        assert_eq!(sp1, compute_search_path_oleans_digest(&lp));

        // Same-size overwrite as well as companion creation/modification must invalidate memoized digests.
        fs::write(&olean_path, b"olean-version-2").unwrap();
        let d2 = compute_imported_oleans_digest("Foo.Bar", &lp);
        let sp2 = compute_search_path_oleans_digest(&lp);
        assert_ne!(d1, d2);
        assert_ne!(sp1, sp2);

        let srv_path = PathBuf::from(format!("{}.server", olean_path.display()));
        fs::write(&srv_path, b"server-companion-v1").unwrap();
        let d3 = compute_imported_oleans_digest("Foo.Bar", &lp);
        assert_ne!(d2, d3);

        fs::write(&srv_path, b"server-companion-v2").unwrap();
        let d4 = compute_imported_oleans_digest("Foo.Bar", &lp);
        assert_ne!(d3, d4);

        std::thread::sleep(std::time::Duration::from_millis(65));
        let d4_warm_populate = compute_imported_oleans_digest("Foo.Bar", &lp);
        assert_eq!(d4, d4_warm_populate);
        assert_eq!(d4, compute_imported_oleans_digest("Foo.Bar", &lp));

        fs::write(&olean_path, b"olean-version-3").unwrap();
        let d5 = compute_imported_oleans_digest("Foo.Bar", &lp);
        assert_ne!(d4, d5);

        let _ = fs::remove_dir_all(&tmp_dir);
    }

    /// A warm worker is handed back on the strength of the pool key and `olean_digest`, and the
    /// in-process verified-shard memo is keyed on `olean_digest` too. A `needs`-ed `input_dir` file
    /// is read while a module elaborates and moves no `.olean` byte, so without this component an
    /// edited input left every one of them matching and the worker answered from the old bytes.
    ///
    /// Covers the layouts as well as the contents: the package root is recovered by walking the
    /// search-path entry up to the nearest Lake config, so a package whose `buildDir` is not
    /// `.lake/build` is folded in just the same.
    #[test]
    fn test_zygote_lake_inputs_digest_tracks_declared_input_contents() {
        // Drives the process-global Lake-input memo window, as the tests in `module_builder` do.
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_zygote_lake_inputs_{}_{}",
            std::process::id(),
            next_tmp_id()
        ));
        let lib = tmp_dir.join(".lake/build/lib/lean");
        fs::create_dir_all(&lib).unwrap();
        fs::create_dir_all(tmp_dir.join("Data")).unwrap();
        fs::write(
            tmp_dir.join("lean-toolchain"),
            include_str!("../../../lean/lean-toolchain"),
        )
        .unwrap();
        let lp = lib.to_string_lossy().to_string();
        // Each read stands for a fresh command, which is what the memo window is scoped to.
        let digest = |path: &str| {
            crate::module_builder::reset_lake_inputs_tag_memo();
            let (d, uncacheable) =
                compute_lean_path_lake_inputs_digest(path, &std::collections::HashMap::new());
            assert!(!uncacheable, "supported Lake input must remain cacheable");
            d
        };
        // No Lake config yet: nothing declared, so nothing is mixed in and every existing
        // project's pool key and `olean_digest` stay byte-identical.
        assert_eq!(digest(&lp), "");

        fs::write(
            tmp_dir.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage demo\ninput_dir smokeSources where\n  path := \"Data\"\n  filter := .extension \"sol\"\n@[default_target]\nlean_lib Smoke where\n  globs := #[.submodules `Smoke]\n  needs := #[smokeSources]\n",
        )
        .unwrap();
        fs::write(tmp_dir.join("Data/a.sol"), "contract A {}").unwrap();
        let d1 = digest(&lp);
        assert!(!d1.is_empty(), "a declared input must reach the worker key");
        assert_eq!(d1, digest(&lp), "stable");

        // A matched edit moves it; an unmatched file does not.
        fs::write(tmp_dir.join("Data/a.sol"), "contract ALongerName {}").unwrap();
        let d2 = digest(&lp);
        assert_ne!(d1, d2, "editing a matched input must retire warm workers");
        fs::write(tmp_dir.join("Data/notes.txt"), "notes").unwrap();
        assert_eq!(d2, digest(&lp));
        // Restoring the bytes restores the digest, so a warm worker is reusable again.
        fs::write(tmp_dir.join("Data/a.sol"), "contract A {}").unwrap();
        assert_eq!(d1, digest(&lp));

        // A custom `buildDir` / `leanLibDir` must contribute the same tag. `buildDir` is a Lake
        // package field, so `<pkg_root>/.lake/build/lib/lean` is only the default layout; counting
        // a fixed four components up from the search path entry left every such package out of
        // `olean_digest`, and a warm worker survived an edit to its inputs.
        let custom_lib = tmp_dir.join("out/lib/lean");
        fs::create_dir_all(&custom_lib).unwrap();
        assert_eq!(
            digest(&custom_lib.to_string_lossy()),
            d1,
            "a custom build directory must resolve to the same package root"
        );
        // So must the package root itself, which is the shallowest entry that can name it.
        assert_eq!(digest(&tmp_dir.to_string_lossy()), d1);

        // A search-path entry with no Lake package above it -- every toolchain entry, for one --
        // still contributes nothing. Nested deeply enough that the ancestor walk cannot reach the
        // shared temp root.
        let other = std::env::temp_dir().join(format!(
            "turbo_zygote_no_lake_{}_{}",
            std::process::id(),
            next_tmp_id()
        ));
        let bare = other.join("a/b/c/d/e/lib/lean");
        fs::create_dir_all(&bare).unwrap();
        assert_eq!(digest(&bare.to_string_lossy()), "");

        // Deeply nested custom `buildDir` (> 8 ancestor levels) must still locate its enclosing
        // package root rather than silently dropping Lake input digests.
        let deep_lib = tmp_dir.join("a/b/c/d/e/f/g/h/i/j/lib/lean");
        fs::create_dir_all(&deep_lib).unwrap();
        assert_eq!(
            digest(&deep_lib.to_string_lossy()),
            d1,
            "deeply nested buildDir (>8 levels) must still resolve package Lake inputs"
        );

        // Even with an empty LEAN_PATH, `TURBO_LEAN_PROJECT_DIR` must surface the caller
        // workspace's Lake input digest to Zygote context resolution.
        crate::module_builder::reset_lake_inputs_tag_memo();
        let mut env_with_proj = std::collections::HashMap::new();
        env_with_proj.insert(
            "TURBO_LEAN_PROJECT_DIR".to_string(),
            tmp_dir.to_string_lossy().to_string(),
        );
        let (d_proj, uncacheable_proj) = compute_lean_path_lake_inputs_digest("", &env_with_proj);
        assert!(!uncacheable_proj);
        assert_eq!(
            d_proj, d1,
            "empty LEAN_PATH with TURBO_LEAN_PROJECT_DIR must still include workspace Lake inputs"
        );

        // Unsupported `filter := .text` or missing `input_file` must mark the Zygote context
        // uncacheable (`lake_inputs_uncacheable == true`) and emit fresh nonces so SHM/pool caches
        // never replay stale verdicts.
        fs::write(
            tmp_dir.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage demo\ninput_dir smokeSources where\n  path := \"Data\"\n  filter := .text\n@[default_target]\nlean_lib Smoke where\n  globs := #[.submodules `Smoke]\n  needs := #[smokeSources]\n",
        )
        .unwrap();
        crate::module_builder::reset_lake_inputs_tag_memo();
        let (u1, bad1) = compute_lean_path_lake_inputs_digest("", &env_with_proj);
        crate::module_builder::reset_lake_inputs_tag_memo();
        let (u2, bad2) = compute_lean_path_lake_inputs_digest("", &env_with_proj);
        assert!(
            bad1 && bad2,
            "unsupported filter must mark Zygote context uncacheable"
        );
        assert!(
            !u1.is_empty() && !u2.is_empty() && u1 != u2,
            "uncacheable workspaces must receive distinct per-call nonces: {u1} vs {u2}"
        );
        let cache_dir = tmp_dir.join("isolated_cache");
        let eval_file = tmp_dir.join("SmokeEval.lean");
        fs::write(&eval_file, "def x : Nat := 1\n").unwrap();
        crate::module_builder::reset_lake_inputs_tag_memo();
        assert!(
            try_stateless_eval_shm_cache(&cache_dir, &eval_file, Some(&tmp_dir), Some(""))
                .is_none(),
            "try_stateless_eval_shm_cache must bail out on unsupported Lake input workspace"
        );

        let _ = fs::remove_dir_all(&other);
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    /// Compile `src` as module `name` under `lib` (`lean -R lib`) and return the `.olean` bytes.
    fn compile_test_olean(lean_bin: &Path, lib: &Path, name: &str, src: &str) -> Vec<u8> {
        let src_path = lib.join(format!("{name}.lean"));
        let out = lib.join(format!("{name}.build.olean"));
        fs::write(&src_path, src).unwrap();
        let env = std::collections::HashMap::from([(
            "LEAN_PATH".to_string(),
            lib.to_string_lossy().into_owned(),
        )]);
        let st = crate::module_builder::verifier_command(lean_bin, &env)
            .unwrap()
            .arg("-R")
            .arg(lib)
            .arg(&src_path)
            .arg("-o")
            .arg(&out)
            .status()
            .unwrap();
        assert!(st.success());
        let bytes = fs::read(&out).unwrap();
        let _ = fs::remove_file(&out);
        bytes
    }

    #[test]
    fn test_closure_snapshot_reread_change_is_incomplete_and_never_cached() {
        let Some((tmp_dir, _store, _env_vars, lean_bin)) = open_test_zygote_env("reread") else {
            return;
        };
        let lib = tmp_dir.join("lib");
        fs::create_dir_all(&lib).unwrap();
        let a = compile_test_olean(&lean_bin, &lib, "Rr", "def rrVal : Nat := 1\n");
        let b = compile_test_olean(&lean_bin, &lib, "Rr", "def rrVal : Nat := 2\n");
        let olean = lib.join("Rr.olean");
        fs::write(&olean, &a).unwrap();
        let lp = lib.to_string_lossy().to_string();

        let stable = ClosureSnapshot::take("Rr", &lp, None);
        assert!(stable.complete);
        assert_eq!(stable.rebind(), ClosureBinding::Bound);

        let swap = olean.clone();
        digest_test_hooks::set("closure_reread", move || fs::write(&swap, &b).unwrap());
        let raced = ClosureSnapshot::take("Rr", &lp, None);
        digest_test_hooks::clear();
        assert!(
            !raced.complete,
            "a module that changed between discovery and re-read must not be complete"
        );
        assert_ne!(raced.rebind(), ClosureBinding::Bound);

        // The eval shm cache refuses a snapshot that no longer describes the closure.
        fs::write(&olean, &a).unwrap();
        let snap = ClosureSnapshot::take("Rr", &lp, None);
        assert!(snap.complete);
        fs::write(&olean, b"garbage").unwrap();
        fs::write(&olean, &a).unwrap();
        let shm = tmp_dir.join("ev_test.json");
        write_eval_shm_cache(&shm, &snap, b"{}");
        assert!(
            !shm.exists(),
            "eval shm reply cached under a stale closure digest"
        );
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_coarse_timestamp_granularity_same_length_rewrite_rehashes() {
        let tmp_dir = std::env::temp_dir().join(format!("turbo_zygote_coarse_{}", next_tmp_id()));
        fs::create_dir_all(tmp_dir.join("Foo")).unwrap();
        let olean = tmp_dir.join("Foo/Bar.olean");
        let lp = tmp_dir.to_string_lossy().to_string();
        digest_test_hooks::set_forced_ts_granularity_ns(Some(1_000_000_000));
        // Start early in a wall-clock second so that every write below shares one truncated
        // second: (dev, ino, mtime, ctime, size) are then identical across the rewrite.
        while wall_clock_ns().rem_euclid(1_000_000_000) > 300_000_000 {
            std::thread::sleep(std::time::Duration::from_millis(5));
        }
        fs::write(&olean, b"coarse-olean-v1").unwrap();
        let sig1 = OleanFileStatSig::from_meta(&fs::metadata(&olean).unwrap());
        std::thread::sleep(std::time::Duration::from_millis(100));
        let d1 = compute_imported_oleans_digest("Foo.Bar", &lp);
        assert_eq!(d1, compute_imported_oleans_digest("Foo.Bar", &lp));
        fs::write(&olean, b"coarse-olean-v2").unwrap();
        let sig2 = OleanFileStatSig::from_meta(&fs::metadata(&olean).unwrap());
        let d2 = compute_imported_oleans_digest("Foo.Bar", &lp);
        let snap = ClosureSnapshot::take("Foo.Bar", &lp, None);
        digest_test_hooks::clear();
        if sig1 == sig2 {
            eprintln!("coarse-granularity test: identical stat tuples across the rewrite");
        }
        assert_ne!(
            d1, d2,
            "a same-length rewrite within one coarse tick must re-hash"
        );
        assert_ne!(snap.rebind(), ClosureBinding::Bound);
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    /// A symlinked directory switched A -> B between the `fstat` and the read, and B -> A
    /// after it: the memo must never pair A's stat tuple with B's bytes.
    #[cfg(unix)]
    #[test]
    fn test_file_digest_memo_symlink_switch_between_stat_and_read_is_not_poisoned() {
        let tmp_dir = std::env::temp_dir().join(format!("turbo_zygote_memo_aba_{}", next_tmp_id()));
        let (dir_a, dir_b, link) = (tmp_dir.join("A"), tmp_dir.join("B"), tmp_dir.join("lib"));
        fs::create_dir_all(&dir_a).unwrap();
        fs::create_dir_all(&dir_b).unwrap();
        fs::write(dir_a.join("Foo.olean"), b"olean-content-A").unwrap();
        fs::write(dir_b.join("Foo.olean"), b"olean-content-B").unwrap();
        std::os::unix::fs::symlink(&dir_a, &link).unwrap();
        // Old enough for the trust rule, so a stable read is memoized.
        std::thread::sleep(std::time::Duration::from_millis(2200));
        let retarget = |to: PathBuf| {
            let link = link.clone();
            move || {
                let tmp = link.with_extension("swap");
                let _ = fs::remove_file(&tmp);
                std::os::unix::fs::symlink(&to, &tmp).unwrap();
                fs::rename(&tmp, &link).unwrap();
            }
        };
        let path = link.join("Foo.olean");
        let hash = |b: &[u8]| blake3::hash(b).to_hex().to_string();
        // A -> B between the `fstat` and the read, B -> A before the closing `fstat`.
        for _ in 0..2 {
            digest_test_hooks::set("file_digest_after_stat", retarget(dir_b.clone()));
            digest_test_hooks::set("file_digest_after_read", retarget(dir_a.clone()));
            let r = read_file_digest(&path).unwrap().unwrap();
            digest_test_hooks::clear();
            // The digest is of the one object that was opened and `fstat`ed: A.
            assert_eq!(r.hash, hash(b"olean-content-A"));
            // Every memo entry describes the object it is keyed by.
            let memo = FILE_DIGEST_MEMO.get().unwrap().lock().unwrap();
            for ((p, dev, ino), e) in memo.iter().filter(|(k, _)| k.0.starts_with(&tmp_dir)) {
                use std::os::unix::fs::MetadataExt;
                let m = fs::metadata(p).unwrap();
                assert_eq!((m.dev(), m.ino()), (*dev, *ino));
                assert_eq!(
                    e.hash,
                    hash(&fs::read(p).unwrap()),
                    "poisoned memo entry for {p:?}"
                );
            }
        }
        // The switch is observed through the memo: B is served B's digest, A is served A's.
        retarget(dir_b.clone())();
        assert_eq!(
            read_file_digest(&path).unwrap().unwrap().hash,
            hash(b"olean-content-B")
        );
        retarget(dir_a.clone())();
        assert_eq!(
            read_file_digest(&path).unwrap().unwrap().hash,
            hash(b"olean-content-A")
        );
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_zygote_aba_swap_during_import_caches_nothing_under_hashed_digest() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("aba_swap") else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";
        let lib = tmp_dir.join("lib");
        fs::create_dir_all(&lib).unwrap();
        let a = compile_test_olean(&lean_bin, &lib, "Swap", "def swapVal : Nat := 1\n");
        let b = compile_test_olean(&lean_bin, &lib, "Swap", "def swapVal : Nat := 2\n");
        let olean = lib.join("Swap.olean");
        fs::write(&olean, &a).unwrap();
        let lp = lib.to_string_lossy().to_string();
        let digest_a = compute_imported_oleans_digest("Swap", &lp);
        let run = |src: &str| {
            eval_with_zygote_pool(&store, toolchain, &lp, &env_vars, &lean_bin, src, false).unwrap()
        };
        let wrong = "import Swap\ntheorem swap_two : swapVal = 2 := rfl\n";

        // A -> B after the host hashed A, B -> A after the worker imported B: content (and the
        // digest) is A again, yet the worker's env and verdict were computed on B.
        let swaps = std::rc::Rc::new(std::cell::Cell::new(0));
        let (to_b, b_bytes, swaps_b) = (olean.clone(), b.clone(), swaps.clone());
        digest_test_hooks::set("after_closure_snapshot", move || {
            if swaps_b.get() == 0 {
                fs::write(&to_b, &b_bytes).unwrap();
            }
        });
        let (to_a, a_bytes, swaps_a) = (olean.clone(), a.clone(), swaps.clone());
        digest_test_hooks::set("after_worker_reply", move || {
            if swaps_a.get() == 0 {
                fs::write(&to_a, &a_bytes).unwrap();
                swaps_a.set(1);
            }
        });
        let rep1 = run(wrong);
        digest_test_hooks::clear();
        assert_eq!(swaps.get(), 1);
        assert_eq!(compute_imported_oleans_digest("Swap", &lp), digest_a);
        assert!(
            !rep1.ok,
            "the retry runs on the restored A, where `swapVal = 2` is false: {rep1:?}"
        );
        // Neither the verdict nor the env computed on B may be served under D(A).
        let rep2 = run(wrong);
        assert!(
            !rep2.ok,
            "verdict computed on B served under D(A): {rep2:?}"
        );
        let rep3 = run("import Swap\ntheorem swap_two' : swapVal = 2 := rfl\n");
        assert!(!rep3.ok, "env imported from B served under D(A): {rep3:?}");
        let rep4 = run("import Swap\ntheorem swap_one : swapVal = 1 := rfl\n");
        assert!(rep4.ok, "{rep4:?}");

        // In-place rewrites after the snapshot never reach the worker: it imports the
        // verified private copy of A, on every attempt.
        let (to_b, b_bytes) = (olean.clone(), b.clone());
        digest_test_hooks::set("after_closure_snapshot", move || {
            fs::write(&to_b, &b_bytes).unwrap()
        });
        let (to_a, a_bytes) = (olean.clone(), a.clone());
        digest_test_hooks::set("after_worker_reply", move || {
            fs::write(&to_a, &a_bytes).unwrap()
        });
        let rep5 = run("import Swap\ntheorem swap_one' : swapVal = 1 := rfl\n");
        let rep6 = run("import Swap\ntheorem swap_two'' : swapVal = 2 := rfl\n");
        digest_test_hooks::clear();
        assert!(rep5.ok, "{rep5:?}");
        assert!(!rep6.ok, "{rep6:?}");

        // A source that changes between the scan and its copy into the snapshot fails closed
        // after one retry: no snapshot, no verdict, nothing cached.
        let c = compile_test_olean(&lean_bin, &lib, "Swap", "def swapVal : Nat := 3\n");
        fs::write(&olean, &c).unwrap();
        // Every copy finds the source flipped (C -> B, then B -> C) since it was hashed.
        let (to, b_bytes, c_bytes, mut flips) = (olean.clone(), b.clone(), c.clone(), 0);
        digest_test_hooks::set("closure_blob_copy", move || {
            flips += 1;
            fs::write(&to, if flips % 2 == 1 { &b_bytes } else { &c_bytes }).unwrap()
        });
        let rep7 = run("import Swap\ntheorem swap_three : swapVal = 3 := rfl\n");
        digest_test_hooks::clear();
        assert!(
            !rep7.ok && rep7.errors.iter().any(|e| e == CLOSURE_CHANGED_ERR),
            "{rep7:?}"
        );
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    /// The worker's search path is the verified snapshot plus the toolchain: nothing it
    /// imports can come from the live search path, and snapshot files are private inodes.
    #[test]
    fn test_closure_snapshot_is_private_and_sole_search_root() {
        let Some((tmp_dir, _store, env_vars, lean_bin)) = open_test_zygote_env("snap_root") else {
            return;
        };
        let (lib1, lib2) = (tmp_dir.join("lib1"), tmp_dir.join("lib2"));
        fs::create_dir_all(&lib1).unwrap();
        fs::create_dir_all(&lib2).unwrap();
        let a = compile_test_olean(&lean_bin, &lib2, "Priv", "def privVal : Nat := 1\n");
        fs::write(lib2.join("Priv.olean"), &a).unwrap();
        let lp = format!("{}:{}", lib1.display(), lib2.display());
        let ctx = resolve_zygote_context(
            "leanprover/lean4:v4.35.0",
            &lp,
            &env_vars,
            &lean_bin,
            "Priv",
        );
        let snap = ctx
            .closure
            .materialized
            .as_ref()
            .expect("closure materialized");
        let tc = fs::canonicalize(toolchain_lib_dir(&lean_bin).unwrap()).unwrap();
        assert_eq!(
            ctx.worker_lean_path,
            format!("{}:{}", snap.dir.display(), tc.display())
        );
        assert!(snap.dir.starts_with(closure_snapshot_root()));
        use std::os::unix::fs::MetadataExt;
        let (src, copy) = (
            fs::metadata(lib2.join("Priv.olean")).unwrap(),
            fs::metadata(snap.dir.join("Priv.olean")).unwrap(),
        );
        assert_ne!((src.dev(), src.ino()), (copy.dev(), copy.ino()));
        assert!(copy.permissions().readonly());
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let dir_mode = fs::symlink_metadata(&snap.dir)
                .unwrap()
                .permissions()
                .mode()
                & 0o777;
            assert_eq!(dir_mode, 0o500, "snapshot root must be sealed 0o500");
        }
        assert_eq!(ctx.closure.binding(), ClosureBinding::Bound);
        // A write to a snapshot file after verification unbinds it.
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&snap.dir, fs::Permissions::from_mode(0o700)).unwrap();
        }
        let mut perms = copy.permissions();
        #[allow(clippy::permissions_set_readonly_false)]
        perms.set_readonly(false);
        let blob = snap.dir.join("Priv.olean");
        fs::set_permissions(&blob, perms).unwrap();
        fs::write(&blob, b"tampered").unwrap();
        assert_eq!(ctx.closure.binding(), ClosureBinding::Changed);
        // ...and the tampered snapshot is rebuilt from the source on next use.
        let ctx2 = resolve_zygote_context(
            "leanprover/lean4:v4.35.0",
            &lp,
            &env_vars,
            &lean_bin,
            "Priv",
        );
        assert_eq!(ctx2.closure.label(), ctx.closure.label());
        assert_eq!(fs::read(snap.dir.join("Priv.olean")).unwrap(), a);
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    /// A shadow `.olean` appearing earlier on the search path while the worker imports (and
    /// disappearing afterwards) is never imported: the worker reads only the snapshot of A,
    /// so no env or verdict computed on the shadow exists to be cached under D(A).
    #[test]
    fn test_zygote_shadow_appearing_during_import_never_reaches_worker() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("shadow") else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";
        let (lib1, lib2) = (tmp_dir.join("lib1"), tmp_dir.join("lib2"));
        fs::create_dir_all(&lib1).unwrap();
        fs::create_dir_all(&lib2).unwrap();
        let a = compile_test_olean(&lean_bin, &lib2, "Shd", "def shdVal : Nat := 1\n");
        let b = compile_test_olean(&lean_bin, &lib2, "Shd", "def shdVal : Nat := 2\n");
        fs::write(lib2.join("Shd.olean"), &a).unwrap();
        let lp = format!("{}:{}", lib1.display(), lib2.display());
        let shadow = lib1.join("Shd.olean");
        let run = |src: &str| {
            eval_with_zygote_pool(&store, toolchain, &lp, &env_vars, &lean_bin, src, false).unwrap()
        };
        let digest_a = compute_imported_oleans_digest("Shd", &lp);
        let (put, b_bytes) = (shadow.clone(), b.clone());
        digest_test_hooks::set("after_closure_snapshot", move || {
            fs::write(&put, &b_bytes).unwrap()
        });
        let (del, replies) = (shadow.clone(), std::rc::Rc::new(std::cell::Cell::new(0)));
        let seen = replies.clone();
        digest_test_hooks::set("after_worker_reply", move || {
            seen.set(seen.get() + 1);
            let _ = fs::remove_file(&del);
        });
        let wrong = "import Shd\ntheorem shd_two : shdVal = 2 := rfl\n";
        let rep1 = run(wrong);
        digest_test_hooks::clear();
        assert!(!shadow.exists());
        // No retry: nothing the worker imported changed (the old live-path check had to detect
        // the shadow after the fact and retry). Zero on a timeout under load.
        assert!(replies.get() <= 1, "{rep1:?}");
        assert_eq!(compute_imported_oleans_digest("Shd", &lp), digest_a);
        assert!(!rep1.ok, "worker imported the shadow: {rep1:?}");
        assert!(
            !run(wrong).ok,
            "verdict computed on the shadow served under D(A)"
        );
        assert!(run("import Shd\ntheorem shd_one : shdVal = 1 := rfl\n").ok);
        // Once the shadow is really there when the closure is resolved, it is what is imported.
        fs::write(&shadow, &b).unwrap();
        assert!(run(wrong).ok);
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    /// Variant: the module on the search path is a symlink retargeted A -> B during the import
    /// and back afterwards (the search root itself is canonicalized when resolved).
    #[cfg(unix)]
    #[test]
    fn test_zygote_symlink_retarget_during_import_never_reaches_worker() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("symret") else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";
        let (dir_a, dir_b, lib) = (tmp_dir.join("A"), tmp_dir.join("B"), tmp_dir.join("lib"));
        for d in [&dir_a, &dir_b, &lib] {
            fs::create_dir_all(d).unwrap();
        }
        let a = compile_test_olean(&lean_bin, &dir_a, "Sym", "def symVal : Nat := 1\n");
        let b = compile_test_olean(&lean_bin, &dir_b, "Sym", "def symVal : Nat := 2\n");
        fs::write(dir_a.join("Sym.olean"), &a).unwrap();
        fs::write(dir_b.join("Sym.olean"), &b).unwrap();
        let link = lib.join("Sym.olean");
        std::os::unix::fs::symlink(dir_a.join("Sym.olean"), &link).unwrap();
        let retarget = |to: PathBuf| {
            let link = link.clone();
            move || {
                let tmp = link.with_extension("swap");
                let _ = fs::remove_file(&tmp);
                std::os::unix::fs::symlink(&to, &tmp).unwrap();
                fs::rename(&tmp, &link).unwrap();
            }
        };
        let lp = lib.to_string_lossy().to_string();
        let run = |src: &str| {
            eval_with_zygote_pool(&store, toolchain, &lp, &env_vars, &lean_bin, src, false).unwrap()
        };
        let replies = std::rc::Rc::new(std::cell::Cell::new(0));
        let (seen, back) = (replies.clone(), retarget(dir_a.join("Sym.olean")));
        digest_test_hooks::set("after_closure_snapshot", retarget(dir_b.join("Sym.olean")));
        digest_test_hooks::set("after_worker_reply", move || {
            seen.set(seen.get() + 1);
            back();
        });
        let wrong = "import Sym\ntheorem sym_two : symVal = 2 := rfl\n";
        let rep1 = run(wrong);
        digest_test_hooks::clear();
        assert!(
            replies.get() <= 1,
            "the worker must not have seen the retarget: {rep1:?}"
        );
        assert!(
            !rep1.ok,
            "worker imported through the retargeted symlink: {rep1:?}"
        );
        assert!(!run(wrong).ok, "verdict computed on B served under D(A)");
        assert!(run("import Sym\ntheorem sym_one : symVal = 1 := rfl\n").ok);
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_attach_host_closure_digest_protocol_columns() {
        let r2 = attach_host_closure_digest("Init\t6162\n", "dig123");
        assert_eq!(r2, "Init\t6162\t\t\t\t\tdig123\n");
        assert_eq!(r2.trim_end_matches('\n').split('\t').nth(6), Some("dig123"));

        let r5 = attach_host_closure_digest("Init\t6162\tstrict\tpk\t7072\n", "dig456");
        assert_eq!(r5, "Init\t6162\tstrict\tpk\t7072\t\tdig456\n");
        assert_eq!(r5.trim_end_matches('\n').split('\t').nth(6), Some("dig456"));

        let r6 = attach_host_closure_digest("Init\t6162\tstrict\t\t\t6f70\n", "dig789");
        assert_eq!(r6, "Init\t6162\tstrict\t\t\t6f70\tdig789\n");
        assert_eq!(r6.trim_end_matches('\n').split('\t').nth(5), Some("6f70"));
        assert_eq!(r6.trim_end_matches('\n').split('\t').nth(6), Some("dig789"));
    }

    #[test]
    fn test_search_path_oleans_digest_skips_lake_packages_bloat_and_tracks_imported_oleans() {
        let tmp_dir = std::env::temp_dir().join(format!("turbo_zygote_pkg_skip_{}", next_tmp_id()));
        let (pkg_lib, local_lib) = (
            tmp_dir.join(".lake/packages/mathlib/.lake/build/lib/lean"),
            tmp_dir.join(".lake/build/lib/lean"),
        );
        let _ = fs::create_dir_all(&pkg_lib);
        let _ = fs::create_dir_all(&local_lib);

        let (big_pkg_olean, local_olean) =
            (pkg_lib.join("Big.olean"), local_lib.join("Local.olean"));
        fs::write(&big_pkg_olean, vec![0xAAu8; 128 * 1024]).unwrap();
        fs::write(&local_olean, b"local-olean-v1").unwrap();

        let lp = format!("{}:{}", local_lib.display(), pkg_lib.display());
        let (sp_d1, imp_d1) = (
            compute_search_path_oleans_digest(&lp),
            compute_imported_oleans_digest("Big,Local", &lp),
        );

        fs::write(&big_pkg_olean, vec![0xBBu8; 130 * 1024]).unwrap();
        let sp_d2 = compute_search_path_oleans_digest(&lp);
        assert_eq!(sp_d1, sp_d2);
        assert_ne!(imp_d1, compute_imported_oleans_digest("Big,Local", &lp));

        fs::write(&local_olean, b"local-olean-v2-modified").unwrap();
        assert_ne!(sp_d2, compute_search_path_oleans_digest(&lp));
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_search_path_oleans_digest_uses_sysroot_identity_not_toolchains_substring() {
        let tmp_dir = std::env::temp_dir().join(format!("turbo_zygote_tc_id_{}", next_tmp_id()));
        let user_tc_named_dir = tmp_dir.join("toolchains/custom_pkg/lib/lean");
        let real_sysroot_root = tmp_dir.join("custom_sysroot");
        let real_sysroot_bin = real_sysroot_root.join("bin");
        let real_sysroot_lib = real_sysroot_root.join("lib/lean");
        fs::create_dir_all(&user_tc_named_dir).unwrap();
        fs::create_dir_all(&real_sysroot_bin).unwrap();
        fs::create_dir_all(&real_sysroot_lib).unwrap();
        fs::write(real_sysroot_bin.join("lean"), b"#!/bin/sh\n").unwrap();

        let user_olean = user_tc_named_dir.join("UserMod.olean");
        let sysroot_olean = real_sysroot_lib.join("Init.olean");
        fs::write(&user_olean, b"user-v1").unwrap();
        fs::write(&sysroot_olean, b"sysroot-v1").unwrap();

        let lp = format!(
            "{}:{}",
            user_tc_named_dir.display(),
            real_sysroot_lib.display()
        );
        let d1 = compute_search_path_oleans_digest(&lp);

        fs::write(&sysroot_olean, b"sysroot-v2-ignored").unwrap();
        let d2 = compute_search_path_oleans_digest(&lp);
        assert_eq!(d1, d2);

        fs::write(&user_olean, b"user-v2-tracked").unwrap();
        let d3 = compute_search_path_oleans_digest(&lp);
        assert_ne!(d2, d3);

        let second_tc_root = tmp_dir.join("second_toolchain");
        let second_tc_lib = second_tc_root.join("lib/lean");
        fs::create_dir_all(second_tc_root.join("bin")).unwrap();
        fs::create_dir_all(&second_tc_lib).unwrap();
        fs::write(second_tc_root.join("bin/lean"), b"#!/bin/sh\n").unwrap();
        let second_tc_olean = second_tc_lib.join("ExtraMod.olean");
        fs::write(&second_tc_olean, b"extra-v1").unwrap();
        let lp_two_tc = format!("{}:{}", second_tc_lib.display(), real_sysroot_lib.display());
        let dt1 =
            compute_search_path_oleans_digest_with_toolchain(&lp_two_tc, Some(&real_sysroot_lib));
        fs::write(&second_tc_olean, b"extra-v2").unwrap();
        let dt2 =
            compute_search_path_oleans_digest_with_toolchain(&lp_two_tc, Some(&real_sysroot_lib));
        assert_ne!(dt1, dt2);

        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_zygote_delta_prefix_chaining_and_used_constants_distillation() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("delta_distill")
        else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";

        let prefix1 = "namespace DeltaChainTest\ndef shiftByFour (n : Nat) : Nat := n + 4\n";
        let shard1 = format!(
            "{}theorem helper_shift_eq (n : Nat) : shiftByFour n = n + 4 := rfl\n",
            prefix1
        );
        assert!(
            eval_with_zygote_pool(&store, toolchain, "", &env_vars, &lean_bin, &shard1, true)
                .unwrap()
                .ok
        );

        let shard2 = format!("{}theorem helper_shift_eq (n : Nat) : shiftByFour n = n + 4 := sorry\ntheorem chained_thm (n : Nat) : shiftByFour n = n + 4 := by\n  simp [helper_shift_eq]\n", prefix1);
        // Stub exemptions need the checked declaration named (an unnamed request exempts nothing).
        let rep2 = eval_with_zygote_pool_for_targets(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            &shard2,
            &["chained_thm".to_string()],
            None,
            &[],
        )
        .unwrap();
        assert!(
            rep2.ok
                && rep2
                    .used_constants
                    .iter()
                    .any(|c| c.contains("helper_shift_eq"))
        );

        // Verify branched LCA prefix reuse: sibling branch sharing `prefix1` reuses the ancestor checkpoint
        let shard3 = format!("{}def siblingBranchHelper (n : Nat) : Nat := shiftByFour n + 2\ntheorem sibling_thm (n : Nat) : siblingBranchHelper n = n + 6 := by\n  unfold siblingBranchHelper shiftByFour; omega\n", prefix1);
        let rep3 =
            eval_with_zygote_pool(&store, toolchain, "", &env_vars, &lean_bin, &shard3, true)
                .unwrap();
        assert!(rep3.ok && rep3.env_cache_hit);

        // Live worker rejects an ambiguous stub name (a second `sorryAx` theorem injected under a
        // colliding `userNameComponents` identity `N.1`), both via a cached prefix checkpoint and in a single block.
        let ambig_prefix = "import Lean\nnamespace N\nlocal macro_rules | `(term| sorry) => `(term| trivial)\ntheorem «1» : True := sorry\nend N\nopen Lean Elab Command in\nelab \"inject\" : command => liftCoreM do\n  addDecl <| .thmDecl { name := Name.mkNum `N 1, levelParams := [], type := mkConst ``False, value := mkApp2 (mkConst ``sorryAx [0]) (mkConst ``False) (mkConst ``Bool.false) }\ninject\n";
        let ambig_ckpt = format!(
            "{}theorem _root_.tgt : False := by\n  run_tac do\n    (← Lean.Elab.Tactic.getMainGoal).assign (Lean.mkConst (Lean.Name.mkNum `N 1))\n",
            ambig_prefix
        );
        for run in 0..2 {
            let rep = eval_with_zygote_pool_for_targets(
                &store,
                toolchain,
                "Lean",
                &env_vars,
                &lean_bin,
                &ambig_ckpt,
                &["_root_.tgt".to_string()],
                None,
                &[],
            )
            .unwrap();
            assert!(!rep.ok, "ambiguous prefix stub must fail: {:?}", rep);
            if run == 1 {
                assert!(rep.prefix_cache_hit, "expected warm prefix hit: {:?}", rep);
            }
            assert!(
                rep.errors
                    .iter()
                    .any(|e| e.contains("prefix stub `_root_.N.«1»` is ambiguous")),
                "unexpected live-worker errors: {:?}",
                rep.errors
            );
        }
        let ambig_final = "import Lean\n/- no-prefix-split -/\n".to_string()
            + ambig_ckpt.strip_prefix("import Lean\n").unwrap();
        let rep_final = eval_with_zygote_pool_for_targets(
            &store,
            toolchain,
            "Lean",
            &env_vars,
            &lean_bin,
            &ambig_final,
            &["_root_.tgt".to_string()],
            None,
            &[],
        )
        .unwrap();
        assert!(
            !rep_final.ok
                && !rep_final.prefix_cache_hit
                && rep_final
                    .errors
                    .iter()
                    .any(|e| e.contains("prefix stub `_root_.N.«1»` is ambiguous")),
            "ambiguous final-run stub must fail: {:?}",
            rep_final
        );
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_lean_native_core_worker_nonexistent_bin_fallback() {
        let _guard = LNC_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
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
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("eval_prefix") else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";
        let isolated_lp = tmp_dir.to_string_lossy().to_string();

        let driver_v1 = "import Init\ndef rsgbStep1 (n : Nat) : Nat := n + 10\ndef rsgbStep2 (n : Nat) : Nat := rsgbStep1 n * 2\ndef rsgbStep3 (n : Nat) : Nat := rsgbStep2 n + 5\ndef rsgbStep4 (n : Nat) : String := s!\"val={rsgbStep3 n}\"\ndef rsgbStep5 (n : Nat) : String := s!\"[{rsgbStep4 n}]\"\ndef rsgbSimTest (a b : Nat) : String := s!\"{rsgbStep5 a}:{rsgbStep5 b}\"\ndef rsgbSimKill (tag : String) (x : Nat) : String := s!\"{tag}:{rsgbSimTest x (x + 1)}\"\ndef rsgbSimOutputs (k : Nat) : String :=\n  rsgbSimKill \"RUN\" k\n#eval rsgbSimOutputs 3\n";
        let run_eval = |src: &str| {
            eval_with_zygote_pool_opts(
                &store,
                toolchain,
                &isolated_lp,
                &env_vars,
                &lean_bin,
                src,
                false,
                true,
                Some("rsgb_driver.lean"),
                Some(30_000),
            )
            .unwrap()
        };

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
        let max_elab_us: u64 = if cfg!(debug_assertions) {
            250_000
        } else {
            80_000
        };
        assert!(rep2.ok && rep2.prefix_cache_hit && rep2.prefix_us == 0);
        assert!(rep2.messages.join("\n").contains("RUN:[val=39]:[val=41]"));
        assert!(rep2.elab_us < max_elab_us && warm_elapsed_ms < max_warm_ms);

        let driver_v3 = format!("{}#check unknown_ident_on_line_12\n", driver_v2);
        let rep3 = run_eval(&driver_v3);
        assert!(
            !rep3.ok
                && rep3.prefix_cache_hit
                && rep3
                    .messages
                    .join("\n")
                    .contains("rsgb_driver.lean:12:7: error(lean.unknownIdentifier):")
        );
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_eval_mode_ancestor_prefix_reuse_preserves_line_numbers() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("eval_ancestor")
        else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";
        let isolated_lp = tmp_dir.to_string_lossy().to_string();
        let run_eval = |src: &str| {
            eval_with_zygote_pool_opts(
                &store,
                toolchain,
                &isolated_lp,
                &env_vars,
                &lean_bin,
                src,
                false,
                true,
                Some("anc.lean"),
                Some(30_000),
            )
            .unwrap()
        };
        let base = "import Init\ndef ancA : Nat := 1\ndef ancB : Nat := ancA + 1\n";
        assert!(run_eval(&format!("{base}#eval ancB\n")).ok);
        // The new prefix extends the cached one; the warning in the delta sits on line 4.
        let rep = run_eval(&format!("{base}theorem ancW : True := sorry\n#eval ancB\n"));
        let msgs = rep.messages.join("\n");
        assert!(rep.ok && msgs.contains("anc.lean:4:8: warning"), "{msgs}");
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_eval_reply_cacheable_only_for_clean_successes() {
        let ok = ZygoteEvalReply {
            ok: true,
            import_ok: true,
            scanner_version: ZYGOTE_SCANNER_VERSION,
            replay_version: ZYGOTE_REPLAY_VERSION,
            ..Default::default()
        };
        assert!(eval_reply_cacheable(&ok));
        // Scanner-vetted but produced before the kernel replay existed: never replayed.
        assert!(!eval_reply_cacheable(&ZygoteEvalReply {
            replay_version: 0,
            ..ok.clone()
        }));
        // Not vetted by the current stderr scanner (pre-upgrade host): never cached or replayed.
        assert!(!eval_reply_cacheable(&ZygoteEvalReply {
            scanner_version: 0,
            ..ok.clone()
        }));
        // e.g. "toolchain not installed": ok=false and import_ok=false
        assert!(!eval_reply_cacheable(&ZygoteEvalReply {
            ok: false,
            ..ok.clone()
        }));
        assert!(!eval_reply_cacheable(&ZygoteEvalReply {
            import_ok: false,
            ..ok.clone()
        }));
        assert!(!eval_reply_cacheable(&ZygoteEvalReply {
            crashed: true,
            ..ok.clone()
        }));
        assert!(!eval_reply_cacheable(&ZygoteEvalReply {
            timed_out: true,
            ..ok
        }));
    }

    #[cfg(unix)]
    #[test]
    fn test_shared_zygote_dir_rejects_foreign_or_open_directories() {
        use std::os::unix::fs::PermissionsExt;
        let tmp = std::env::temp_dir().join(format!("turbo_zyg_shared_{}", next_tmp_id()));
        fs::create_dir_all(&tmp).unwrap();
        let uid = unsafe { libc::geteuid() };
        let dir = tmp.join(format!("turbo_lean_shared_zygote_bins_{uid}"));
        // Pre-planted world-writable dir (as another local user could create) is rejected.
        fs::create_dir(&dir).unwrap();
        fs::set_permissions(&dir, fs::Permissions::from_mode(0o777)).unwrap();
        assert!(private_shared_zygote_dir_in(&tmp).is_none());
        // A symlink in its place is rejected too.
        fs::remove_dir(&dir).unwrap();
        let target = tmp.join("elsewhere");
        fs::create_dir(&target).unwrap();
        fs::set_permissions(&target, fs::Permissions::from_mode(0o700)).unwrap();
        std::os::unix::fs::symlink(&target, &dir).unwrap();
        assert!(private_shared_zygote_dir_in(&tmp).is_none());
        fs::remove_file(&dir).unwrap();
        // A non-sticky group/other-writable parent could let others rename our dir.
        fs::set_permissions(&tmp, fs::Permissions::from_mode(0o777)).unwrap();
        assert!(private_shared_zygote_dir_in(&tmp).is_none());
        fs::set_permissions(&tmp, fs::Permissions::from_mode(0o1777)).unwrap();
        let sticky = private_shared_zygote_dir_in(&tmp).expect("sticky parent accepted");
        fs::remove_dir(&sticky).unwrap();
        fs::set_permissions(&tmp, fs::Permissions::from_mode(0o755)).unwrap();
        // Fresh dir is created 0700 and accepted.
        let got = private_shared_zygote_dir_in(&tmp).expect("private dir");
        assert_eq!(
            fs::metadata(&got).unwrap().permissions().mode() & 0o777,
            0o700
        );
        // A group/other-writable binary is not executable material.
        let bin = got.join("turbo_zygote_x");
        fs::write(&bin, b"x").unwrap();
        fs::set_permissions(&bin, fs::Permissions::from_mode(0o755)).unwrap();
        assert!(owned_private_file(&bin));
        fs::set_permissions(&bin, fs::Permissions::from_mode(0o775)).unwrap();
        assert!(!owned_private_file(&bin));
        let _ = fs::remove_dir_all(&tmp);
    }

    #[test]
    fn test_evb_rfvb_rsgb_parity_prefix_warnings_prelude_and_main_module() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("evb_parity") else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";
        let isolated_lp = tmp_dir.to_string_lossy().to_string();

        let src_v1 = "def pfxUnused (x y : Nat) : Nat := x\ntheorem pfxSorry : True := by sorry\n#eval pfxUnused 42 99\n";
        let rep_cold = eval_with_zygote_pool_opts(
            &store,
            toolchain,
            &isolated_lp,
            &env_vars,
            &lean_bin,
            src_v1,
            false,
            true,
            Some("pfx_warn.lean"),
            Some(30_000),
        )
        .unwrap();
        let cold_msgs = rep_cold.messages.join("\n");
        assert!(
            cold_msgs.contains("unusedVariables") && cold_msgs.contains("declaration uses `sorry`")
        );

        let src_v2 = src_v1.replace("42 99", "77 88");
        let rep_warm = eval_with_zygote_pool_opts(
            &store,
            toolchain,
            &isolated_lp,
            &env_vars,
            &lean_bin,
            &src_v2,
            false,
            true,
            Some("pfx_warn.lean"),
            Some(30_000),
        )
        .unwrap();
        let warm_msgs = rep_warm.messages.join("\n");
        assert!(
            rep_warm.prefix_cache_hit
                && warm_msgs.contains("unusedVariables")
                && warm_msgs.contains("declaration uses `sorry`")
                && warm_msgs.contains("77")
        );

        let (imports_prelude, body_prelude) = split_shard_for_zygote("prelude\n#check Nat\n");
        assert_eq!(imports_prelude, "__PRELUDE__");
        assert!(body_prelude.contains("#check Nat"));
        assert_eq!(
            split_shard_for_zygote("import Zeta.Mod\nimport Alpha.Mod\n#check 1\n").0,
            "Zeta.Mod,Alpha.Mod"
        );

        let priv_src = "private def myPrivHelper : Nat := 123\n#check myPrivHelper\n";
        let rep_priv = eval_with_zygote_pool_opts(
            &store,
            toolchain,
            &isolated_lp,
            &env_vars,
            &lean_bin,
            priv_src,
            false,
            true,
            Some("/tmp/foo_priv_test.lean"),
            Some(30_000),
        )
        .unwrap();
        assert!(!rep_priv.messages.join("\n").contains("._stdin."));
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_zygote_transitive_olean_closure_and_module_visibility_isolation() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("mod_vis_closure")
        else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";
        let lib_a = tmp_dir.join("lib_a");
        let lib_b = tmp_dir.join("lib_b");
        fs::create_dir_all(&lib_a).unwrap();
        fs::create_dir_all(&lib_b).unwrap();

        let src_c1 = lib_a.join("DepC.lean");
        let src_b = lib_a.join("DepB.lean");
        fs::write(&src_c1, "def depValue : Nat := 11\n").unwrap();
        fs::write(&src_b, "import DepC\ndef midValue : Nat := depValue + 1\n").unwrap();

        let status_c1 = Command::new(&lean_bin)
            .arg("-R")
            .arg(&lib_a)
            .arg(&src_c1)
            .arg("-o")
            .arg(lib_a.join("DepC.olean"))
            .env("LEAN_PATH", &lib_a)
            .status()
            .unwrap();
        assert!(status_c1.success());
        let status_b = Command::new(&lean_bin)
            .arg("-R")
            .arg(&lib_a)
            .arg(&src_b)
            .arg("-o")
            .arg(lib_a.join("DepB.olean"))
            .env("LEAN_PATH", &lib_a)
            .status()
            .unwrap();
        assert!(status_b.success());

        let lp_a = lib_a.to_string_lossy().to_string();
        let (dig1, complete1) = compute_imported_oleans_digest_inner("DepB", &lp_a);
        assert!(complete1);
        let rep_warm_seed = eval_with_zygote_pool(
            &store,
            toolchain,
            &lp_a,
            &env_vars,
            &lean_bin,
            "import DepB\ntheorem t_warm_1 : midValue = 12 := rfl\n",
            false,
        )
        .unwrap();
        assert!(rep_warm_seed.ok && rep_warm_seed.import_ok);
        let rep_warm_hit = eval_with_zygote_pool(
            &store,
            toolchain,
            &lp_a,
            &env_vars,
            &lean_bin,
            "import DepB\ntheorem t_warm_2 : midValue + 1 = 13 := rfl\n",
            false,
        )
        .unwrap();
        assert!(
            rep_warm_hit.ok && rep_warm_hit.env_cache_hit,
            "Zygote worker must hit env_cache via hostClosureDigest on second request"
        );

        // Rebuild transitive leaf DepC with same-length source / different constant value without touching DepB.olean
        fs::write(&src_c1, "def depValue : Nat := 99\n").unwrap();
        let status_c2 = Command::new(&lean_bin)
            .arg("-R")
            .arg(&lib_a)
            .arg(&src_c1)
            .arg("-o")
            .arg(lib_a.join("DepC.olean"))
            .env("LEAN_PATH", &lib_a)
            .status()
            .unwrap();
        assert!(status_c2.success());
        let dig2 = compute_imported_oleans_digest("DepB", &lp_a);
        assert_ne!(
            dig1, dig2,
            "compute_imported_oleans_digest must track transitive .olean dependencies (DepB -> DepC)"
        );
        let rep_after_dep_edit = eval_with_zygote_pool(
            &store,
            toolchain,
            &lp_a,
            &env_vars,
            &lean_bin,
            "import DepB\ntheorem t_after_edit : depValue = 99 := rfl\n",
            false,
        )
        .unwrap();
        assert!(
            rep_after_dep_edit.ok && !rep_after_dep_edit.env_cache_hit,
            "Zygote worker must miss env_cache and reload when transitive DepC.olean changes"
        );

        // Module visibility isolation: private import in `module` must be enforced, and `LEAN_PATH`
        // isolation must prevent cross-path worker pollution.
        let mod_priv_src = lib_a.join("ModPriv.lean");
        fs::write(
            &mod_priv_src,
            "module\ndef secretInternal : Nat := 7\n@[expose] public def exportedVal : Nat := 42\n",
        )
        .unwrap();
        let st_mp = Command::new(&lean_bin)
            .arg("-R")
            .arg(&lib_a)
            .arg(&mod_priv_src)
            .arg("-o")
            .arg(lib_a.join("ModPriv.olean"))
            .env("LEAN_PATH", &lib_a)
            .status()
            .unwrap();
        assert!(st_mp.success());

        let (mod_csv, _) = split_shard_for_zygote(
            "module\nimport ModPriv\ntheorem t : secretInternal = 7 := rfl\n",
        );
        assert!(
            mod_csv.contains("__MODULE__"),
            "module header must be encoded in Zygote imports_csv: {}",
            mod_csv
        );
        let rep_priv_fail = eval_with_zygote_pool(
            &store,
            toolchain,
            &lp_a,
            &env_vars,
            &lean_bin,
            "module\nimport ModPriv\ntheorem t : secretInternal = 7 := rfl\n",
            false,
        )
        .unwrap();
        assert!(
            !rep_priv_fail.ok,
            "module importing ModPriv without `import all` must reject private constant `secretInternal`"
        );

        let rep_pub_ok = eval_with_zygote_pool(
            &store,
            toolchain,
            &lp_a,
            &env_vars,
            &lean_bin,
            "module\nimport ModPriv\ntheorem t : exportedVal = 42 := rfl\n",
            false,
        )
        .unwrap();
        assert!(
            rep_pub_ok.ok,
            "exported constant must succeed in module mode: {:?}",
            rep_pub_ok.errors
        );

        // Distinct LEAN_PATH `lib_b` without ModPriv must NOT reuse `lib_a`'s worker
        let lp_b = lib_b.to_string_lossy().to_string();
        let rep_wrong_lp = eval_with_zygote_pool(
            &store,
            toolchain,
            &lp_b,
            &env_vars,
            &lean_bin,
            "module\nimport ModPriv\ntheorem t : exportedVal = 42 := rfl\n",
            false,
        )
        .unwrap();
        assert!(
            !rep_wrong_lp.ok,
            "Zygote worker must not leak cached Environment across distinct LEAN_PATHs"
        );

        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_build_auditor_bootstrap_env_uses_toolchain_paths_only() {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_bootstrap_env_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        fs::create_dir_all(tmp_dir.join("App")).unwrap();
        fs::write(tmp_dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            tmp_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nroots = [\"App.Main\"]\n",
        )
        .unwrap();
        fs::write(tmp_dir.join("App/Main.lean"), "def x : Nat := 1\n").unwrap();
        let Ok(cfg) = crate::module_builder::resolve_project_config(&tmp_dir) else {
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        };
        let env = build_auditor_bootstrap_env(&cfg);
        let lp = env.get("LEAN_PATH").cloned().unwrap_or_default();
        let ld = env.get("LD_LIBRARY_PATH").cloned().unwrap_or_default();
        assert_eq!(lp, cfg.toolchain_lib_lean.to_string_lossy());
        assert!(!lp.contains(".lake"));
        assert!(!lp.contains(&tmp_dir.to_string_lossy().to_string()));
        assert!(!ld.contains(".lake"));
        assert!(!ld.contains(&tmp_dir.to_string_lossy().to_string()));
        assert_eq!(
            env.get("LEAN").map(String::as_str),
            Some(cfg.lean_bin.to_string_lossy().as_ref())
        );

        let store_dir = tmp_dir.join("store");
        let store = TurboStore::open(Some(&store_dir)).unwrap();
        let olean_dir = tmp_dir.join(".lake/build/lib/lean/App");
        fs::create_dir_all(&olean_dir).unwrap();
        let out = Command::new(&cfg.lean_bin)
            .current_dir(&tmp_dir)
            .arg("-R")
            .arg(&tmp_dir)
            .arg("-o")
            .arg(olean_dir.join("Main.olean"))
            .arg(tmp_dir.join("App/Main.lean"))
            .env("LEAN_PATH", &cfg.toolchain_lib_lean)
            .env("LD_LIBRARY_PATH", &ld)
            .output()
            .unwrap();
        assert!(out.status.success(), "lean compile failed: {:?}", out);

        let poisoned_lib_dir = tmp_dir.join(".lake/build/lib");
        fs::create_dir_all(&poisoned_lib_dir).unwrap();
        fs::write(poisoned_lib_dir.join("libleanshared.so"), b"CORRUPT_ELF").unwrap();
        let (lean_path_env, project_ld_path_env) =
            crate::module_builder::build_lean_search_path(&cfg, true);
        assert!(
            project_ld_path_env.contains(".lake/build/lib"),
            "project search path must include .lake/build/lib to exercise regression"
        );
        audit_compiled_modules_with_zygote(
            &store,
            &cfg,
            &["App.Main".to_string()],
            &lean_path_env,
            &[],
            false,
        )
        .expect("trusted auditor must ignore poisoned .lake/build/lib/libleanshared.so");
        if crate::module_builder::probe_bwrap_sandbox(std::path::Path::new(".")).is_some() {
            audit_compiled_modules_with_zygote(
                &store,
                &cfg,
                &["App.Main".to_string()],
                &lean_path_env,
                &[],
                true,
            )
            .expect("sandboxed auditor must ignore poisoned .lake/build/lib/libleanshared.so");
        }
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_audit_compiled_modules_respects_axiom_allowlist_and_never_allows_sorry_or_trust_compiler(
    ) {
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_audit_axioms_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        fs::create_dir_all(tmp_dir.join("App")).unwrap();
        fs::write(tmp_dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            tmp_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nroots = [\"App.Nd\", \"App.Sorry\", \"App.Trust\"]\n",
        )
        .unwrap();
        fs::write(
            tmp_dir.join("App/Nd.lean"),
            "theorem t_nd : 2 ^ 3 = 8 := by native_decide\n",
        )
        .unwrap();
        fs::write(
            tmp_dir.join("App/Sorry.lean"),
            "theorem t_sorry : 1 = 2 := sorry\n",
        )
        .unwrap();
        let trust_src = "import Lean\nopen Lean Elab Tactic in\nelab \"sneak_tc\" : tactic => do\n  let g ← getMainGoal\n  let t ← g.getType\n  let nm := Name.mkStr2 \"Lean\" (\"trust\" ++ \"Compiler\")\n  let e ← Meta.mkAppOptM nm #[some t]\n  g.assign e\ntheorem t_tc : True := by sneak_tc\n";
        fs::write(tmp_dir.join("App/Trust.lean"), trust_src).unwrap();
        let Ok(cfg) = crate::module_builder::resolve_project_config(&tmp_dir) else {
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        };
        let env = build_auditor_bootstrap_env(&cfg);
        let ld = env.get("LD_LIBRARY_PATH").cloned().unwrap_or_default();
        let olean_dir = tmp_dir.join(".lake/build/lib/lean/App");
        fs::create_dir_all(&olean_dir).unwrap();
        for (src, olean, must_succeed) in [
            ("App/Nd.lean", "Nd.olean", true),
            ("App/Sorry.lean", "Sorry.olean", true),
            ("App/Trust.lean", "Trust.olean", false),
        ] {
            let out = Command::new(&cfg.lean_bin)
                .current_dir(&tmp_dir)
                .arg("-R")
                .arg(&tmp_dir)
                .arg("-o")
                .arg(olean_dir.join(olean))
                .arg(tmp_dir.join(src))
                .env("LEAN_PATH", &cfg.toolchain_lib_lean)
                .env("LD_LIBRARY_PATH", &ld)
                .output()
                .unwrap();
            if must_succeed {
                assert!(
                    out.status.success(),
                    "lean compile {} failed: {:?}",
                    src,
                    out
                );
            }
        }
        let store = TurboStore::open(Some(&tmp_dir.join("store"))).unwrap();
        let (lean_path_env, _) = crate::module_builder::build_lean_search_path(&cfg, true);
        let prev_allow = std::env::var(crate::splitter::ALLOWED_AXIOMS_ENV).ok();
        let has_bwrap =
            crate::module_builder::probe_bwrap_sandbox(std::path::Path::new(".")).is_some();

        // 1. Default policy rejects `native_decide` auxiliary axioms in both trusted and untrusted Stage 1C audits.
        std::env::remove_var(crate::splitter::ALLOWED_AXIOMS_ENV);
        for is_untrusted in [false, true] {
            if is_untrusted && !has_bwrap {
                continue;
            }
            let err = audit_compiled_modules_with_zygote(
                &store,
                &cfg,
                &["App.Nd".to_string()],
                &lean_path_env,
                &[],
                is_untrusted,
            )
            .unwrap_err()
            .to_string();
            assert!(
                err.contains("_native.native_decide.ax_")
                    || err.contains("Lean.ofReduceBool")
                    || err.contains("Lean.trustCompiler"),
                "untrusted={}: {}",
                is_untrusted,
                err
            );
        }

        // 2. Allowlist `Lean.ofReduceBool,*._native.native_decide.ax_*` admits `App.Nd` (unless `Lean.trustCompiler` was emitted),
        // while even wildcard `*` unconditionally rejects `sorryAx` (`App.Sorry`) and `Lean.trustCompiler`.
        std::env::set_var(crate::splitter::ALLOWED_AXIOMS_ENV, "*");
        for is_untrusted in [false, true] {
            if is_untrusted && !has_bwrap {
                continue;
            }
            let nd_res = audit_compiled_modules_with_zygote(
                &store,
                &cfg,
                &["App.Nd".to_string()],
                &lean_path_env,
                &[],
                is_untrusted,
            );
            if let Err(e) = nd_res {
                let msg = e.to_string();
                assert!(
                    msg.contains("Lean.trustCompiler")
                        && !msg.contains("_native.native_decide.ax_"),
                    "wildcard must admit native_decide aux axioms (only Lean.trustCompiler stays non-allowable): {}",
                    msg
                );
            }
            let sorry_err = audit_compiled_modules_with_zygote(
                &store,
                &cfg,
                &["App.Sorry".to_string()],
                &lean_path_env,
                &[],
                is_untrusted,
            )
            .unwrap_err()
            .to_string();
            assert!(
                sorry_err.contains("sorryAx"),
                "wildcard must never admit sorryAx (untrusted={}): {}",
                is_untrusted,
                sorry_err
            );
            if olean_dir.join("Trust.olean").exists() {
                let tc_err = audit_compiled_modules_with_zygote(
                    &store,
                    &cfg,
                    &["App.Trust".to_string()],
                    &lean_path_env,
                    &[],
                    is_untrusted,
                )
                .unwrap_err()
                .to_string();
                assert!(
                    tc_err.contains("Lean.trustCompiler"),
                    "wildcard must never admit Lean.trustCompiler (untrusted={}): {}",
                    is_untrusted,
                    tc_err
                );
            }
        }

        match prev_allow {
            Some(v) => std::env::set_var(crate::splitter::ALLOWED_AXIOMS_ENV, v),
            None => std::env::remove_var(crate::splitter::ALLOWED_AXIOMS_ENV),
        }
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_runtime_panic_detection_rejects_reply_even_when_ok_flag_is_true() {
        let mut rep = ZygoteEvalReply {
            ok: true,
            import_ok: true,
            messages: vec![
                "<zygote-decl>:4:0: info: PANIC at Lean.EnvExtension.modifyStateImpl: invalid environment extension"
                    .to_string(),
            ],
            ..Default::default()
        };
        assert!(mark_runtime_panic(&mut rep, false));
        assert!(!rep.ok);
        assert_eq!(rep.errors, vec![RUNTIME_PANIC_ERR.to_string()]);
        // Idempotent, and ordinary output mentioning PANIC is not a runtime panic.
        assert!(mark_runtime_panic(&mut rep, false) && rep.errors.len() == 1);
        let mut benign = ZygoteEvalReply {
            ok: true,
            messages: vec!["info: \"PANIC button pressed\"".to_string()],
            errors: vec!["unknown identifier 'runtime panic'".to_string()],
            ..Default::default()
        };
        assert!(!mark_runtime_panic(&mut benign, false) && benign.ok);
        assert!(mark_runtime_panic(&mut benign, true) && !benign.ok);

        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("panic_guard") else {
            return;
        };
        let lp = tmp_dir.to_string_lossy().to_string();
        let tc = "leanprover/lean4:v4.35.0";
        let idle_workers = || -> usize {
            ZYGOTE_POOL
                .get()
                .and_then(|m| m.lock().ok())
                .map(|g| {
                    g.iter()
                        .filter(|(k, _)| k.1.contains(&lp))
                        .map(|(_, v)| v.len())
                        .sum()
                })
                .unwrap_or(0)
        };
        // Panics reported as messages, printed only to stderr (`stderrAsMessages false`), and
        // raised inside tactic elaboration (which `lean` itself only prints to stderr).
        let tactic_boom = "import Lean\nopen Lean Elab Tactic\nelab \"boom\" : tactic => do\n  let n : Nat := panic! \"tacp\"\n  logInfo m!\"{n}\"\ntheorem c : True := by boom; trivial\n";
        for (eval_mode, src) in [
            (true, "import Lean\n#eval (panic! \"Lean.EnvExtension.modifyStateImpl\" : Nat)\n"),
            (false, "#eval (panic! \"msg\" : Nat)\ntheorem p1 : True := trivial\n"),
            (false, "set_option stderrAsMessages false\n#eval (panic! \"stderr only\" : Nat)\ntheorem p2 : True := trivial\n"),
            // Stderr-only panic behind a long unterminated stderr line (> any line buffer).
            (false, "set_option stderrAsMessages false\n#eval show IO Unit from do\n  let e ← IO.getStderr\n  e.putStr (String.ofList (List.replicate 10000 'x'))\n  e.flush\n  let n : Nat := panic! s!\"after long line {(← IO.monoNanosNow) % 1}\"\n  IO.println n\ntheorem p3 : True := trivial\n"),
            (false, tactic_boom),
            (true, tactic_boom),
        ] {
            let before = idle_workers();
            let live_rep = eval_with_zygote_pool_opts(
                &store, tc, &lp, &env_vars, &lean_bin, src, false, eval_mode,
                Some("PanicTest.lean"), Some(60_000),
            )
            .unwrap();
            assert!(
                !live_rep.ok && live_rep.errors.iter().any(|e| e == RUNTIME_PANIC_ERR),
                "panic must fail the request: {src:?} -> {live_rep:?}"
            );
            assert!(idle_workers() <= before, "panicked worker returned to the pool: {src:?}");
            // A panicked request is never cached: the same request panics again on a new worker.
            let again = eval_with_zygote_pool_opts(
                &store, tc, &lp, &env_vars, &lean_bin, src, false, eval_mode,
                Some("PanicTest.lean"), Some(60_000),
            )
            .unwrap();
            assert!(!again.ok, "panicked reply was cached: {src:?}");
        }
        let follow = eval_with_zygote_pool(
            &store,
            tc,
            &lp,
            &env_vars,
            &lean_bin,
            "theorem post_panic_clean : 1 + 1 = 2 := rfl\n",
            false,
        )
        .unwrap();
        assert!(
            follow.ok,
            "fresh/healthy worker must succeed after panic shard: {:?}",
            follow
        );
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    /// Upgrade path: replies cached by hosts without the stderr panic scan — main before #310
    /// (`eval-shm:v3:`) and main with #305 (`eval-shm:v4`, resolved identity) — for a
    /// stderr-only tactic panic followed by a successful theorem (`ok=true`) are never replayed.
    #[test]
    fn test_pre_scanner_eval_cache_entry_is_never_replayed() {
        TEST_NO_DAEMON.with(|c| c.set(true));
        let (tmp_dir, store, env_vars, lean_bin) =
            open_test_zygote_env("eval_cache_upgrade").expect("Lean v4.35.0 toolchain required");
        let tc = "leanprover/lean4:v4.35.0";
        let lp = tmp_dir.to_string_lossy().to_string();
        let src = format!(
            "import Lean\nopen Lean Elab Tactic\n-- {}\nelab \"boom\" : tactic => do\n  let n : Nat := panic! \"tacp\"\n  logInfo m!\"{{n}}\"\ntheorem c : True := by boom; trivial\n",
            next_tmp_id()
        );
        let file_name = "UpgradePanic.lean";
        let caller_cwd = std::env::current_dir()
            .ok()
            .map(|p| p.to_string_lossy().to_string());
        let (imports_csv, _) = split_shard_for_zygote(&src);
        // The exact v3 key of main before #310.
        let v3_name = {
            let mut h = blake3::Hasher::new();
            h.update(b"eval-shm:v3:");
            for part in [
                tc,
                &lp,
                &compute_imported_oleans_digest(&imports_csv, &lp),
                file_name,
                caller_cwd.as_deref().unwrap_or(""),
            ] {
                h.update(part.as_bytes());
                h.update(b":");
            }
            h.update(src.as_bytes());
            format!("ev_{}.json", &h.finalize().to_hex()[..24])
        };
        let context = resolve_zygote_context(tc, &lp, &env_vars, &lean_bin, &imports_csv);
        // The exact v4 key of main with #305 (resolved identity, no scanner version).
        let v4_name = {
            let args_digest = crate::module_builder::compute_lean_args_digest(&[]).unwrap();
            let bytes = serde_json::to_vec(&(
                "eval-shm:v4",
                &context.identity,
                file_name,
                caller_cwd.as_deref(),
                &src,
                args_digest,
            ))
            .unwrap();
            format!("ev_{}.json", &blake3::hash(&bytes).to_hex()[..24])
        };
        let new_name =
            compute_eval_shm_cache_filename(&context, file_name, caller_cwd.as_deref(), &src, &[])
                .unwrap();
        assert_ne!(v3_name, new_name, "the namespace bump must change the key");
        assert_ne!(
            v4_name, new_name,
            "scanner namespace must change the #305 key"
        );
        let dir = store.fast_staging_dir().join("eval_shm_cache");
        crate::shm_cache::ensure_private_dir_all(&dir).unwrap();
        // A pre-scanner (no `scanner_version`) false success, planted at the v3 and v4 keys
        // and, as a foreign/unversioned writer would, at the new key.
        let stale = br#"{"ok":true,"kernel_gate_active":false,"import_ok":true,"env_cache_hit":false,"prefix_cache_hit":false,"import_us":1,"prefix_us":0,"elab_us":1,"heartbeats":0,"proof_term_nodes":0,"rss_delta_mb":0,"peak_rss_mb":0,"subshards_verified":1,"stdout":"","messages":[],"errors":[],"used_constants":[],"timed_out":false,"crashed":false}"#;
        for name in [&v3_name, &v4_name, &new_name] {
            crate::shm_cache::atomic_write_shm(&dir.join(name), stale).unwrap();
        }
        assert!(read_cached_eval_shm_reply(&dir.join(&v3_name)).is_none());
        assert!(read_cached_eval_shm_reply(&dir.join(&v4_name)).is_none());
        crate::shm_cache::atomic_write_shm(&dir.join(&v4_name), stale).unwrap();
        crate::shm_cache::atomic_write_shm(&dir.join(&new_name), stale).unwrap();

        let rep = try_local_zygote_eval_with_args(
            &store,
            &env_vars,
            &lean_bin,
            tc,
            &lp,
            &src,
            Some(file_name),
            60_000,
            &[],
        )
        .expect("eval must not error")
        .expect("worker must execute");
        assert!(
            !rep.ok && rep.errors.iter().any(|e| e == RUNTIME_PANIC_ERR),
            "stale cached ok replayed: {rep:?}"
        );
        assert_eq!(rep.scanner_version, ZYGOTE_SCANNER_VERSION);
        assert!(
            !dir.join(&new_name).exists(),
            "unversioned entry must be dropped"
        );
        // And a scanner-vetted failure is not cached either: the next call executes again.
        let again = try_local_zygote_eval_with_args(
            &store,
            &env_vars,
            &lean_bin,
            tc,
            &lp,
            &src,
            Some(file_name),
            60_000,
            &[],
        )
        .unwrap()
        .unwrap();
        assert!(!again.ok && again.errors.iter().any(|e| e == RUNTIME_PANIC_ERR));
        for name in [&v3_name, &v4_name] {
            let _ = fs::remove_file(dir.join(name));
        }
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    /// Upgrade path for the kernel replay: a `forge_bad` false success (a theorem of `False`
    /// added by an elaborator with `debug.skipKernelTC`) cached by a host before this PR — at
    /// the #305 `eval-shm:v4` key and at the #306 `eval-shm:v5` key, where it even carries the
    /// current `scanner_version` — is never replayed: the worker re-runs and rejects it.
    #[test]
    fn test_pre_replay_eval_cache_entry_is_never_replayed() {
        TEST_NO_DAEMON.with(|c| c.set(true));
        let (tmp_dir, store, env_vars, lean_bin) =
            open_test_zygote_env("eval_cache_replay_upgrade")
                .expect("Lean v4.35.0 toolchain required");
        let tc = "leanprover/lean4:v4.35.0";
        let lp = tmp_dir.to_string_lossy().to_string();
        let src = format!(
            "import Lean\nopen Lean Elab Command\n-- {}\nelab \"forge_bad\" : command => do\n  let k := Name.mkStr (Name.mkStr .anonymous \"debug\") (\"skip\" ++ \"KernelTC\")\n  withScope (fun sc => {{ sc with opts := sc.opts.setBool k true }}) do\n    liftCoreM <| addDecl <| .thmDecl {{\n      name := `bad, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }}\nforge_bad\ntheorem uses_bad : False := bad\n",
            next_tmp_id()
        );
        crate::splitter::reject_checking_weakening(&src)
            .expect("forge_bad must reach the worker, not the source hygiene gate");
        let file_name = "Bad.lean";
        let caller_cwd = std::env::current_dir()
            .ok()
            .map(|p| p.to_string_lossy().to_string());
        let (imports_csv, _) = split_shard_for_zygote(&src);
        let context = resolve_zygote_context(tc, &lp, &env_vars, &lean_bin, &imports_csv);
        let args_digest = crate::module_builder::compute_lean_args_digest(&[]).unwrap();
        let key = |bytes: Vec<u8>| format!("ev_{}.json", &blake3::hash(&bytes).to_hex()[..24]);
        let v4_name = key(serde_json::to_vec(&(
            "eval-shm:v4",
            &context.identity,
            file_name,
            caller_cwd.as_deref(),
            &src,
            &args_digest,
        ))
        .unwrap());
        // The exact key of main with #306 (scanner version, no replay version).
        let v5_name = key(serde_json::to_vec(&(
            "eval-shm:v5",
            ZYGOTE_SCANNER_VERSION,
            &context.identity,
            file_name,
            caller_cwd.as_deref(),
            &src,
            &args_digest,
        ))
        .unwrap());
        let new_name =
            compute_eval_shm_cache_filename(&context, file_name, caller_cwd.as_deref(), &src, &[])
                .unwrap();
        assert_ne!(
            v5_name, new_name,
            "the replay namespace must change the #306 key"
        );
        assert_ne!(v4_name, new_name);
        let dir = store.fast_staging_dir().join("eval_shm_cache");
        crate::shm_cache::ensure_private_dir_all(&dir).unwrap();
        // What a #306 host cached: scanner-vetted, ok, but never kernel-replayed.
        let stale = br#"{"ok":true,"kernel_gate_active":true,"import_ok":true,"env_cache_hit":false,"prefix_cache_hit":false,"import_us":1,"prefix_us":0,"elab_us":1,"heartbeats":0,"proof_term_nodes":0,"rss_delta_mb":0,"peak_rss_mb":0,"subshards_verified":2,"stdout":"","messages":[],"errors":[],"used_constants":["bad"],"timed_out":false,"crashed":false,"scanner_version":1}"#;
        for name in [&v4_name, &v5_name, &new_name] {
            crate::shm_cache::atomic_write_shm(&dir.join(name), stale).unwrap();
            assert!(
                read_cached_eval_shm_reply(&dir.join(name)).is_none(),
                "pre-replay entry {name} was accepted"
            );
            crate::shm_cache::atomic_write_shm(&dir.join(name), stale).unwrap();
        }
        let rep = try_local_zygote_eval_with_args(
            &store,
            &env_vars,
            &lean_bin,
            tc,
            &lp,
            &src,
            Some(file_name),
            60_000,
            &[],
        )
        .expect("eval must not error")
        .expect("worker must execute");
        assert!(!rep.ok, "pre-replay cached ok replayed: {rep:?}");
        assert!(
            rep.errors.iter().any(|e| e.contains("KernelReplay")),
            "the worker kernel replay must reject forge_bad: {rep:?}"
        );
        assert_eq!(rep.replay_version, ZYGOTE_REPLAY_VERSION);
        assert!(
            !dir.join(&new_name).exists(),
            "pre-replay entry must be dropped"
        );
        for name in [&v4_name, &v5_name] {
            let _ = fs::remove_file(dir.join(name));
        }
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_stderr_scan_sees_every_byte_and_fails_closed_without_reply_mark() {
        let wait = std::time::Duration::from_millis(200);
        let mark = format!("\n{ZYGOTE_STDERR_REPLY_MARK}\n");
        // A panic after a long unterminated line, and signatures/marks split across any chunk size.
        let long = format!("{}PANIC at boom{mark}", "x".repeat(100_000));
        for chunk in [1, 7, 1024, long.len()] {
            let scan = StderrScan::default();
            let before = scan.snapshot();
            long.as_bytes().chunks(chunk).for_each(|c| scan.feed(c));
            assert_eq!(scan.snapshot(), (1, 1), "chunk={chunk}");
            assert!(scan.panicked_since(before, wait), "chunk={chunk}");
            // A clean request after it, with its mark, is clean; no double counting of the overlap.
            let before = scan.snapshot();
            format!("{}{mark}", "y".repeat(5000))
                .as_bytes()
                .chunks(chunk)
                .for_each(|c| scan.feed(c));
            assert_eq!(scan.snapshot(), (1, 2), "chunk={chunk}");
            assert!(!scan.panicked_since(before, wait), "chunk={chunk}");
        }
        // Missing mark: fail closed even though no panic was seen.
        let scan = std::sync::Arc::new(StderrScan::default());
        let before = scan.snapshot();
        scan.feed(b"ordinary output\n");
        assert!(scan.panicked_since(before, wait));
        // Delayed mark (after the wait): fail closed; a mark within the wait: clean.
        for (delay, expect) in [(wait * 3, true), (wait / 4, false)] {
            let before = scan.snapshot();
            let s = scan.clone();
            let m = mark.clone();
            let t = std::thread::spawn(move || {
                std::thread::sleep(delay);
                s.feed(m.as_bytes());
            });
            assert_eq!(scan.panicked_since(before, wait), expect, "delay={delay:?}");
            t.join().unwrap();
        }
    }

    /// Raw worker IPC against stock `lean`: the worker must never accept what `lean` rejects.
    #[test]
    fn test_zygote_worker_ipc_matches_stock_lean_boundary() {
        // No silent skips: a missing toolchain or a worker that fails to compile fails the test.
        let (tmp_dir, store, env_vars, lean_bin) =
            open_test_zygote_env("ipc_boundary").expect("Lean v4.35.0 toolchain required");
        let bin = ensure_zygote_binary(&store, &lean_bin, &env_vars)
            .unwrap_or_else(|e| panic!("Zygote worker failed to compile: {e:#}"));
        let tc_lib = lean_bin
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .join("lib/lean");
        let hx = |s: &str| hex_encode_bytes(s.as_bytes());
        let opts = |o: &[&str]| {
            if o.is_empty() {
                String::new()
            } else {
                hx(&o.join("\n"))
            }
        };
        let session = |lines: &[String]| -> Vec<serde_json::Value> {
            let mut child = Command::new(&bin)
                .env("LEAN", &lean_bin)
                .env("LEAN_PATH", &tc_lib)
                .env("LEAN_NUM_THREADS", "4")
                .stdin(std::process::Stdio::piped())
                .stdout(std::process::Stdio::piped())
                .stderr(std::process::Stdio::null())
                .spawn()
                .expect("spawn zygote worker");
            let mut stdin = child.stdin.take().unwrap();
            let mut out = BufReader::new(child.stdout.take().unwrap());
            let replies = lines
                .iter()
                .map(|l| {
                    stdin.write_all(format!("{l}\n").as_bytes()).unwrap();
                    stdin.flush().unwrap();
                    let mut r = String::new();
                    out.read_line(&mut r).unwrap();
                    serde_json::from_str(r.trim()).expect("worker JSON reply")
                })
                .collect();
            let _ = child.kill();
            let _ = child.wait();
            replies
        };
        let stock_ok = |body: &str, o: &[&str]| -> bool {
            let f = tmp_dir.join(format!("Stock{}.lean", next_tmp_id()));
            fs::write(&f, body).unwrap();
            let mut c = Command::new(&lean_bin);
            c.env("LEAN_PATH", &tc_lib).args(o).arg(&f);
            c.output().unwrap().status.success()
        };
        let ok = |r: &serde_json::Value| r["ok"].as_bool() == Some(true);

        // 1 + 2: option allowlist (with any number of `weak.` prefixes) and Lean's own value parsing.
        let triv = "theorem t : True := trivial\n";
        let sorry_thm = "theorem s : 1 = 2 := sorry\n";
        for (body, o) in [
            (triv, "-Ddebug.skipKernelTC=true"),
            (triv, "-Dweak.debug.skipKernelTC=true"),
            (triv, "-DstderrAsMessages=false"),
            (triv, "-Ddebug.byAsSorry=true"),
            (sorry_thm, "-Dweak.warn.sorry=false"),
            (sorry_thm, "-Dweak.weak.warn.sorry=false"),
            (triv, "-DmaxHeartbeats=garbage"),
            (triv, "-DautoImplicit=maybe"),
            (triv, "-Dlinter.auditUnregistered=true"),
            (triv, "-Dpp.all=true"),
        ] {
            let r = &session(&[format!("Init\t{}\tstrict\t\t\t{}", hx(body), opts(&[o]))])[0];
            assert!(!ok(r), "{o} must be rejected: {r}");
            assert!(
                r["errors"][0].as_str().unwrap_or("").contains(o),
                "{o}: {r}"
            );
        }
        for o in [
            "-Dweak.linter.auditUnregistered=true",
            "-DmaxHeartbeats=1000",
            "-DautoImplicit=false",
            "-Ddebug.skipKernelTC=false",
            "-Dweak.warn.sorry=true",
        ] {
            let r = &session(&[format!("Init\t{}\tstrict\t\t\t{}", hx(triv), opts(&[o]))])[0];
            assert!(ok(r) && stock_ok(triv, &[o]), "{o} must be accepted: {r}");
            // Hardening forced after parsing: `sorry` is still rejected under any accepted option.
            let r = &session(&[format!(
                "Init\t{}\tstrict\t\t\t{}",
                hx(sorry_thm),
                opts(&[o])
            )])[0];
            assert!(!ok(r), "sorry accepted under {o}: {r}");
        }
        for o in [
            "-DmaxHeartbeats=garbage",
            "-DautoImplicit=maybe",
            "-Dlinter.auditUnregistered=true",
        ] {
            assert!(!stock_ok(triv, &[o]), "stock lean must reject {o}");
        }

        // 3: a panicking race candidate fails the whole request and poisons the worker.
        let panic_cand = "#eval (panic! \"boom\" : Nat)\ntheorem pz : True := trivial\n";
        let good = "theorem good : 1 + 1 = 2 := rfl\n";
        // (`[good, panic]` never runs the panic: the race stops at a cheap winner.)
        {
            let cands = [panic_cand, good];
            let pre = hx("def pre : Nat := 1\n");
            let race = format!(
                "Init\trace_candidates\tk1\t{pre}\t{},{}",
                hx(cands[0]),
                hx(cands[1])
            );
            let rs = session(&[race.clone(), format!("Init\t{}\tstrict", hx(good))]);
            assert!(
                !ok(&rs[0]) && rs[0]["winning_candidate_idx"].is_null(),
                "{}",
                rs[0]
            );
            assert!(
                !ok(&rs[1]),
                "worker must stay poisoned after a race panic: {}",
                rs[1]
            );
        }
        // 3: a prefix (or prefix delta) that panics only on its first run ends the request: the
        // combined fallback, which would not panic again, never turns it into ok=true.
        let first_run_panic = |tag: &str| {
            let marker = tmp_dir.join(format!("first_run_{tag}_{}", next_tmp_id()));
            format!(
                "#eval show IO Unit from do\n  if (← System.FilePath.pathExists {:?}) then return\n  IO.FS.writeFile {:?} \"\"\n  let n : Nat := panic! s!\"first run only {{(← IO.monoNanosNow) % 1}}\"\n  IO.println n\ntheorem pre_{tag} : True := trivial\n",
                marker.to_string_lossy(),
                marker.to_string_lossy()
            )
        };
        let tgt = "theorem tgt : 1 + 1 = 2 := rfl\n";
        let panicked = |r: &serde_json::Value| {
            !ok(r)
                && r["errors"]
                    .as_array()
                    .is_some_and(|e| e.iter().any(|e| e.as_str() == Some(RUNTIME_PANIC_ERR)))
        };
        for mode in ["strict", "race_candidates", "batch_fission", "delta"] {
            let seed = "def seed_base : Nat := 1\n";
            let pre = if mode == "delta" {
                format!("{seed}{}", first_run_panic(mode))
            } else {
                first_run_panic(mode)
            };
            let pad = |p: &str| format!("{}{tgt}", "\n".repeat(p.lines().count()));
            let req = |p: &str, key: &str| match mode {
                "race_candidates" | "batch_fission" => {
                    format!("Init\t{mode}\t{key}\t{}\t{}", hx(p), hx(tgt))
                }
                _ => format!("Init\t{}\tstrict\t{key}\t{}", hx(&pad(p)), hx(p)),
            };
            let mut lines = Vec::new();
            if mode == "delta" {
                // Seeds the prefix tree so the panicking request runs as a delta on top of it.
                lines.push(req(seed, "k_seed"));
            }
            lines.push(req(&pre, "k_panic"));
            lines.push(format!("Init\t{}\tstrict", hx(tgt)));
            let rs = session(&lines);
            let (r, next) = (&rs[lines.len() - 2], &rs[lines.len() - 1]);
            if mode == "delta" {
                assert!(ok(&rs[0]), "seed prefix must succeed: {}", rs[0]);
            }
            assert!(panicked(r), "{mode}: first-run prefix panic masked: {r}");
            if mode == "race_candidates" {
                assert!(r["winning_candidate_idx"].is_null(), "{r}");
            }
            assert!(panicked(next), "{mode}: worker must stay poisoned: {next}");
        }

        // 3: the first request binds the worker even with an empty importsCsv.
        let rs = session(&[
            format!(",\t{}\tstrict", hx(triv)),
            format!("Lean\t{}\tstrict", hx(triv)),
        ]);
        assert!(ok(&rs[0]) && !ok(&rs[1]), "{rs:?}");
        assert!(rs[1]["errors"][0]
            .as_str()
            .unwrap()
            .contains("importsCsv changed"));

        // 4: a prefix checkpoint keeps the target's warningAsError policy (from -D or set_option).
        let target = "def audit_unused (x : Nat) : Nat := 0\n";
        assert!(!stock_ok(target, &["-DwarningAsError=true"]));
        for (pre, o) in [
            (
                "theorem prior : True := sorry\n",
                opts(&["-DwarningAsError=true"]),
            ),
            (
                "set_option warningAsError true\ntheorem prior2 : True := trivial\n",
                String::new(),
            ),
            (
                "set_option warningAsError true\ntheorem prior3 : True := sorry\n",
                String::new(),
            ),
        ] {
            let body = format!("{}{}", "\n".repeat(pre.lines().count()), target);
            let req = format!("Init\t{}\tstrict\tpk\t{}\t{}", hx(&body), hx(pre), o);
            let rs = session(&[req.clone(), req]);
            assert!(
                !ok(&rs[0]) && !ok(&rs[1]),
                "warningAsError lost through prefix {pre:?}: {rs:?}"
            );
            // Stubs in the prefix stay allowed for a clean target.
            let clean = format!(
                "{}theorem tgt : 1 + 1 = 2 := rfl\n",
                "\n".repeat(pre.lines().count())
            );
            let r = &session(&[format!(
                "Init\t{}\tstrict\tpk\t{}\t{}",
                hx(&clean),
                hx(pre),
                o
            )])[0];
            assert!(ok(r), "stub prefix must not fail a clean target: {r}");
        }
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_worker_crash_diagnostics_capture_exit_code_signal_and_stderr() {
        let spawn_dummy_worker = |script: &str| -> ZygoteWorkerProcess {
            let mut child = Command::new("sh")
                .arg("-c")
                .arg(script)
                .stdin(std::process::Stdio::piped())
                .stdout(std::process::Stdio::piped())
                .stderr(std::process::Stdio::piped())
                .spawn()
                .expect("spawn sh");
            let stdin = child.stdin.take().unwrap();
            let stdout = BufReader::new(child.stdout.take().unwrap());
            let stderr_tail = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
            if let Some(mut err_pipe) = child.stderr.take() {
                let tail_clone = stderr_tail.clone();
                let handle = std::thread::spawn(move || {
                    use std::io::Read;
                    let mut buf = Vec::new();
                    let _ = err_pipe.read_to_end(&mut buf);
                    if let Ok(mut g) = tail_clone.lock() {
                        *g = buf;
                    }
                });
                let _ = handle.join();
            }
            let _ = child.wait();
            ZygoteWorkerProcess {
                child: Some(child),
                clone_pid: None,
                _owner: std::sync::mpsc::channel().0,
                stdin: worker_input(stdin),
                stdout: BufReader::new(worker_output(stdout.into_inner())),
                stderr_tail,
                stderr_scan: Default::default(),
                #[cfg(target_os = "linux")]
                pinned_snapshot_dir: None,
                spawn_lean_path: String::new(),
                warm_prefixes: std::collections::HashSet::new(),
                warm_prefix_tree: Vec::new(),
                warm_imports: std::collections::HashMap::new(),
                request_count: 1,
                cold_import_us: None,
                is_master: false,
                _master: None,
            }
        };

        let mut exited = spawn_dummy_worker("echo 'stack overflow in Lean runtime' >&2; exit 134");
        let diag = build_worker_crash_diagnostics(
            &mut exited,
            "Zygote worker closed stdout unexpectedly",
            512,
            "imports=Init file=Foo.lean mode=strict bytes=128",
        );
        let rep = ZygoteEvalReply::crashed_reply_with_diag(false, diag);
        assert!(rep.crashed);
        assert!(!rep.ok);
        assert_eq!(rep.exit_code, Some(134));
        assert_eq!(rep.peak_rss_mb, 512);
        assert!(rep.stderr_tail.contains("stack overflow in Lean runtime"));
        assert_eq!(
            rep.last_request.as_deref(),
            Some("imports=Init file=Foo.lean mode=strict bytes=128")
        );
        assert!(rep.errors[0].contains("exit_code=134"));
        assert!(rep.errors[0].contains("stack overflow in Lean runtime"));

        #[cfg(unix)]
        {
            let mut killed = spawn_dummy_worker("echo 'killed by oom' >&2; kill -9 $$");
            let sig_diag = build_worker_crash_diagnostics(
                &mut killed,
                "Zygote worker closed stdout unexpectedly",
                1024,
                "imports=Init file=Oom.lean mode=strict bytes=64",
            );
            let sig_rep = ZygoteEvalReply::crashed_reply_with_diag(false, sig_diag);
            assert!(sig_rep.crashed);
            assert_eq!(sig_rep.exit_signal, Some(9));
            assert!(sig_rep.errors[0].contains("signal=9"));
        }
    }

    #[test]
    fn test_zygote_options_fail_closed_before_worker_execution() {
        use crate::module_builder::option_cases::*;
        let (dir, store, env_vars, _) =
            open_test_zygote_env("rejected_options").expect("Lean toolchain");
        let mut failures = Vec::new();
        for &(name, value) in ORIGINAL_OPTIONS.iter().chain(RESTRICTED_OPTIONS) {
            for prefix in PREFIXES {
                if original_case_allowed(name, value, prefix) {
                    continue;
                }
                let arg = format!("-D{prefix}{name}={value}");
                let args = std::slice::from_ref(&arg);
                let result = eval_with_zygote_pool_with_args(
                    &store,
                    "leanprover/lean4:v4.35.0",
                    "",
                    &env_vars,
                    Path::new("must-not-execute"),
                    "theorem good : True := True.intro",
                    false,
                    args,
                );
                let batch = eval_subshards_batch_via_zygote(
                    &store,
                    "leanprover/lean4:v4.35.0",
                    "",
                    &env_vars,
                    Path::new("must-not-execute"),
                    "",
                    &[],
                    args,
                );
                let race = eval_candidates_race_via_zygote(
                    &store,
                    "leanprover/lean4:v4.35.0",
                    "",
                    &env_vars,
                    Path::new("must-not-execute"),
                    "",
                    &[],
                    args,
                );
                for (mode, result) in [
                    ("pool", result),
                    ("empty batch", batch),
                    ("empty race", race),
                ] {
                    match result {
                        Err(error) if format!("{error:#}").contains(&arg) => {}
                        result => failures.push(format!("{mode}/{arg}: {result:?}")),
                    }
                }
                let reply = try_local_zygote_eval_with_args(
                    &store,
                    &env_vars,
                    Path::new("must-not-execute"),
                    "leanprover/lean4:v4.35.0",
                    "",
                    "theorem good : True := True.intro",
                    None,
                    0,
                    args,
                )
                .expect("invalid options must not error")
                .expect("invalid options must fail closed, never trigger fallback");
                assert!(
                    !reply.ok && reply.errors.iter().any(|e| e.contains(&arg)),
                    "{reply:?}"
                );
            }
        }
        fs::remove_dir_all(dir).unwrap();
        assert!(
            failures.is_empty(),
            "zygote options were not rejected: {}",
            failures.join("\n")
        );
    }

    #[test]
    fn test_zygote_raw_options_cannot_bypass_kernel_checking() {
        use crate::module_builder::option_cases::*;
        let (dir, store, env_vars, lean_bin) =
            open_test_zygote_env("raw_options").expect("Lean toolchain");
        let bin = ensure_zygote_binary(&store, &lean_bin, &env_vars).unwrap();
        let mut child = Command::new(bin)
            .envs(&env_vars)
            .env("LEAN", &lean_bin)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::null())
            .spawn()
            .unwrap();
        let mut stdin = child.stdin.take().unwrap();
        let mut stdout = BufReader::new(child.stdout.take().unwrap());
        let src = include_str!("../tests/fixtures/weakening-options/Bad.lean")
            .replace("import Lean\n", "");
        let mut accepted = Vec::new();
        for arg in std::iter::once(String::new()).chain(
            ORIGINAL_OPTIONS
                .iter()
                .chain(RESTRICTED_OPTIONS)
                .flat_map(|(name, value)| {
                    PREFIXES
                        .iter()
                        .map(move |prefix| format!("-D{prefix}{name}={value}"))
                }),
        ) {
            writeln!(
                stdin,
                "Lean\t{}\tstrict\t\t\t{}\traw-test-closure",
                hex_encode_bytes(src.as_bytes()),
                hex_encode_bytes(arg.as_bytes())
            )
            .unwrap();
            stdin.flush().unwrap();
            let mut line = String::new();
            stdout.read_line(&mut line).unwrap();
            let reply: serde_json::Value = serde_json::from_str(&line).unwrap();
            if reply["ok"] == true {
                accepted.push((arg, reply));
            }
        }
        let control = "theorem raw_control : True := True.intro";
        writeln!(
            stdin,
            "Lean\t{}\tstrict\t\t\t\traw-test-closure",
            hex_encode_bytes(control.as_bytes())
        )
        .unwrap();
        stdin.flush().unwrap();
        let mut line = String::new();
        stdout.read_line(&mut line).unwrap();
        let control: serde_json::Value = serde_json::from_str(&line).unwrap();
        drop(stdin);
        assert!(child.wait().unwrap().success());
        assert_eq!(control["ok"], true, "{control}");
        fs::remove_dir_all(dir).unwrap();
        assert!(
            accepted.is_empty(),
            "raw worker accepted False with zero axioms: {accepted:?}"
        );
    }

    /// Source text can set `debug.skipKernelTC` itself (top level, `set_option … in`, a cached
    /// prefix, programmatically). The worker's independent kernel replay must reject all of them.
    #[test]
    fn test_zygote_source_options_cannot_bypass_kernel_checking() {
        let (dir, store, env_vars, lean_bin) =
            open_test_zygote_env("source_options").expect("Lean toolchain");
        let bin = ensure_zygote_binary(&store, &lean_bin, &env_vars).unwrap();
        let mut child = Command::new(bin)
            .envs(&env_vars)
            .env("LEAN", &lean_bin)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::null())
            .spawn()
            .unwrap();
        let mut stdin = child.stdin.take().unwrap();
        let mut stdout = BufReader::new(child.stdout.take().unwrap());
        let mut ask = |body: &str, mode: &str, key: &str, prefix: &str| -> serde_json::Value {
            let hex_prefix = if prefix.is_empty() {
                String::new()
            } else {
                hex_encode_bytes(prefix.as_bytes())
            };
            writeln!(
                stdin,
                "Lean\t{}\t{mode}\t{key}\t{hex_prefix}\t\tsrc-test-closure",
                hex_encode_bytes(body.as_bytes())
            )
            .unwrap();
            stdin.flush().unwrap();
            let mut line = String::new();
            stdout.read_line(&mut line).unwrap();
            serde_json::from_str(&line).unwrap()
        };
        let bad = include_str!("../tests/fixtures/weakening-options/Bad.lean")
            .replace("import Lean\n", "");
        let skip = "set_option debug.skipKernelTC true\n";
        let skip_in = bad.replace(
            "run_elab",
            "set_option debug.skipKernelTC true in\nrun_elab",
        );
        let programmatic = bad.replace(
            "run_elab do",
            "run_elab withOptions (fun o => o.setBool `debug.skipKernelTC true) do",
        );
        let top = format!("{skip}{bad}");
        let weak = format!("set_option weak.debug.skipKernelTC true\n{bad}");
        let rejected_artifacts: Vec<_> = ["RejectedBody", "RejectedPrefix"]
            .into_iter()
            .map(|name| (name, dir.join(format!("{name}.olean"))))
            .collect();
        let emit_modes: Vec<_> = rejected_artifacts
            .iter()
            .map(|(name, path)| {
                format!(
                    "emit_olean:{}:{}:",
                    hex_encode_bytes(name.as_bytes()),
                    hex_encode_bytes(path.to_str().unwrap().as_bytes())
                )
            })
            .collect();
        let mut accepted = Vec::new();
        let mut replay_missing = Vec::new();
        // (label, body, mode, prefix key, prefix): the prefix rows use the cached-checkpoint path.
        let cases: Vec<(&str, &str, &str, &str, &str)> = vec![
            ("top-level", &top, "strict", "", ""),
            ("set_option in", &skip_in, "strict", "", ""),
            ("programmatic", &programmatic, "strict", "", ""),
            ("weak prefix", &weak, "strict", "", ""),
            ("cached prefix", &bad, "strict", "skip-prefix", skip),
            (
                "cached prefix (reused)",
                &bad,
                "strict",
                "skip-prefix",
                skip,
            ),
            ("stub prefix", &bad, "allow_stub", "skip-stub-prefix", skip),
            (
                "bad decl in prefix",
                "theorem uses_bad : True := True.intro\n",
                "strict",
                "bad-prefix",
                &top,
            ),
            ("emit body", &top, &emit_modes[0], "", ""),
            ("emit prefix", "", &emit_modes[1], "bad-emit-prefix", &top),
            ("eval", &top, "eval", "", ""),
        ];
        for (label, body, mode, key, prefix) in cases {
            let reply = ask(body, mode, key, prefix);
            let errors = reply["errors"].to_string();
            if reply["ok"] == true {
                accepted.push(format!("{label}: {reply}"));
            } else if label != "weak prefix" && !errors.contains("KernelReplay") {
                // `weak.` options are ignored by Lean, so the normal kernel check rejects that one.
                replay_missing.push(format!("{label}: {reply}"));
            }
        }
        for (_, path) in &rejected_artifacts {
            assert!(
                !path.exists(),
                "rejected declarations emitted {}",
                path.display()
            );
        }
        // Legitimate resource options and normal declarations keep working, including via prefixes.
        let legit = "set_option maxHeartbeats 400000\nstructure P where\n  a : Nat\n  h : a = a\n\
            mutual\ninductive A | a | b (x : B)\ninductive B | c (x : A)\nend\n\
            def f : Nat → Nat\n  | 0 => 0\n  | n+1 => f n\n\
            theorem tf : f 3 = 0 := by simp [f]\ninstance : Inhabited P := ⟨⟨0, rfl⟩⟩\n";
        let legit_in = "set_option maxHeartbeats 400000 in\ntheorem good : True := True.intro\n";
        for (label, body, key, prefix) in [
            ("legit", legit, "", ""),
            ("legit in", legit_in, "", ""),
            (
                "legit prefix",
                "theorem z : f 0 = 0 := rfl\n",
                "legit-prefix",
                legit,
            ),
        ] {
            let reply = ask(body, "strict", key, prefix);
            assert_eq!(reply["ok"], true, "{label}: {reply}");
        }
        drop(stdin);
        assert!(child.wait().unwrap().success());
        fs::remove_dir_all(dir).unwrap();
        assert!(
            accepted.is_empty(),
            "raw worker accepted False from source options: {accepted:#?}"
        );
        assert!(
            replay_missing.is_empty(),
            "kernel replay did not report: {replay_missing:#?}"
        );
    }

    #[test]
    fn test_zygote_applies_encoded_max_heartbeats_and_isolates_prefix_cache() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("lean_args_hb")
        else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";
        let isolated_lp = tmp_dir.to_string_lossy().to_string();

        let prefix =
            "namespace HbParity\ndef spin : Nat → Nat\n  | 0 => 0\n  | n + 1 => spin n + 1\n";
        let decl = "theorem spin_80 : spin 80 = 80 := rfl\n";
        let shard = format!("{}\n{}", prefix, decl);

        let low_hb = vec!["-DmaxHeartbeats=2".to_string()];
        let high_hb = vec!["-DmaxHeartbeats=400000".to_string()];

        let rep_low = eval_with_zygote_pool_with_args(
            &store,
            toolchain,
            &isolated_lp,
            &env_vars,
            &lean_bin,
            &shard,
            false,
            &low_hb,
        )
        .unwrap();
        assert!(
            !rep_low.ok
                && rep_low
                    .errors
                    .iter()
                    .any(|e| e.contains("maxHeartbeats") || e.contains("heartbeats")),
            "expected heartbeat failure under -DmaxHeartbeats=2, got: {:?}",
            rep_low
        );

        let rep_high = eval_with_zygote_pool_with_args(
            &store,
            toolchain,
            &isolated_lp,
            &env_vars,
            &lean_bin,
            &shard,
            false,
            &high_hb,
        )
        .unwrap();
        assert!(
            rep_high.ok,
            "expected success under -DmaxHeartbeats=400000, got: {:?}",
            rep_high
        );
        assert!(rep_high.proof_term_nodes > 0);

        let rep_low_after = eval_with_zygote_pool_with_args(
            &store,
            toolchain,
            &isolated_lp,
            &env_vars,
            &lean_bin,
            &format!("{}\ntheorem spin_81 : spin 81 = 81 := rfl\n", prefix),
            false,
            &low_hb,
        )
        .unwrap();
        assert!(
            !rep_low_after.ok,
            "warm prefix from high maxHeartbeats must not leak into low maxHeartbeats: {:?}",
            rep_low_after
        );
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_zygote_and_audited_fallback_enforce_fast_verify_kernel_statement_pinning() {
        let Some((tmp_dir, store, mut env_vars, lean_bin)) = open_test_zygote_env("fast_map_pin")
        else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";
        let mod_lean = tmp_dir.join("FastPinMod.lean");
        let mod_olean = tmp_dir.join("FastPinMod.olean");
        let orig_mod_src =
            "namespace a\ndef k : Nat := 7\ntheorem b : k = 7 := rfl\ntheorem other : 1 = 1 := rfl\nend a\n";
        fs::write(&mod_lean, orig_mod_src).unwrap();
        let status = std::process::Command::new(&lean_bin)
            .envs(&env_vars)
            .current_dir(&tmp_dir)
            .arg(&mod_lean)
            .arg("-o")
            .arg(&mod_olean)
            .status()
            .unwrap();
        assert!(status.success(), "failed to compile FastPinMod.lean");
        let lp = tmp_dir.to_string_lossy().to_string();
        env_vars.insert("LEAN_PATH".to_string(), lp.clone());

        let uncached: std::collections::HashSet<String> =
            ["_root_.a.b".to_string()].into_iter().collect();
        let valid_fast =
            crate::splitter::build_fast_olean_shard_source(orig_mod_src, "FastPinMod", &uncached)
                .unwrap();

        let rep_ok = eval_with_zygote_pool_for_targets(
            &store,
            toolchain,
            &lp,
            &env_vars,
            &lean_bin,
            &valid_fast,
            &["_root_.a.b".to_string()],
            None,
            &[],
        )
        .unwrap();
        assert!(
            rep_ok.ok,
            "expected valid fast-verify shard to pass: {:?}",
            rep_ok
        );

        let fallback_ok = run_audited_lean_shard(
            &store,
            &lean_bin,
            &env_vars,
            None,
            &valid_fast,
            &uncached,
            &[],
            None,
        )
        .unwrap();
        assert!(fallback_ok.status.success());

        // Forge a fast-verify directive whose expected_gen_stmt_hash matches a weakened statement
        // (`True` instead of `k = 7`), verifying that the Lean kernel check rejects the mismatch
        // against imported `_root_.a.b` in `FastPinMod.olean`.
        let forged_body =
            "import FastPinMod\nnamespace a\ntheorem _turbo_verify_0_b : True := trivial\nend a\n";
        let forged_shards = crate::splitter::split_lean_source(forged_body, &[]).shards;
        let forged_dir = crate::splitter::format_fast_verify_directive(
            "_root_.a.b",
            "_root_.a._turbo_verify_0_b",
            &forged_shards[0].stmt_hash,
        );
        let forged_src = format!("{}\n{}", forged_dir, forged_body);

        let rep_forged = eval_with_zygote_pool_for_targets(
            &store,
            toolchain,
            &lp,
            &env_vars,
            &lean_bin,
            &forged_src,
            &["_root_.a.b".to_string()],
            None,
            &[],
        )
        .unwrap();
        assert!(
            !rep_forged.ok,
            "forged fast-verify statement must be rejected by kernel type check: {:?}",
            rep_forged
        );

        let fallback_forged = run_audited_lean_shard(
            &store,
            &lean_bin,
            &env_vars,
            None,
            &forged_src,
            &uncached,
            &[],
            None,
        );
        match fallback_forged {
            Ok(out) => assert!(
                !out.status.success(),
                "audited fallback must reject forged fast-verify statement"
            ),
            Err(e) => assert!(
                format!("{:#}", e).contains("fast-verify kernel statement mismatch"),
                "unexpected fallback error: {:#}",
                e
            ),
        }

        // Unmapped `_turbo_verify_0_a_b` must fail both zygote and audited fallback.
        let unmapped = "import Init\ntheorem _turbo_verify_0_a_b : True := trivial\n";
        assert!(eval_with_zygote_pool_for_targets(
            &store,
            toolchain,
            &lp,
            &env_vars,
            &lean_bin,
            unmapped,
            &["_root_.a.b".to_string()],
            None,
            &[],
        )
        .is_err());
        let bad_set: std::collections::HashSet<String> =
            ["_root_.a.b".to_string()].into_iter().collect();
        assert!(run_audited_lean_shard(
            &store,
            &lean_bin,
            &env_vars,
            None,
            unmapped,
            &bad_set,
            &[],
            None,
        )
        .is_err());

        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_local_zygote_eval_aba_swap_never_poisons_eval_shm_cache() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("eval_aba_cache")
        else {
            return;
        };
        let tc = "leanprover/lean4:v4.35.0";
        let lib = tmp_dir.join("lib");
        fs::create_dir_all(&lib).unwrap();
        let a = compile_test_olean(&lean_bin, &lib, "EvSwap", "def evSwapVal : Nat := 1\n");
        let b = compile_test_olean(&lean_bin, &lib, "EvSwap", "def evSwapVal : Nat := 2\n");
        let olean = lib.join("EvSwap.olean");
        fs::write(&olean, &a).unwrap();
        let lp = lib.to_string_lossy().to_string();
        let src = format!("import EvSwap\n-- {}\n#eval evSwapVal\n", next_tmp_id());
        let file_name = "EvalAba.lean";
        let caller_cwd = std::env::current_dir()
            .ok()
            .map(|p| p.to_string_lossy().to_string());
        let (imports_csv, _) = split_shard_for_zygote(&src);
        let ctx_a = resolve_zygote_context(tc, &lp, &env_vars, &lean_bin, &imports_csv);
        let cache_name_a =
            compute_eval_shm_cache_filename(&ctx_a, file_name, caller_cwd.as_deref(), &src, &[])
                .unwrap();
        let cache_path_a = store
            .fast_staging_dir()
            .join("eval_shm_cache")
            .join(&cache_name_a);
        let _ = fs::remove_file(&cache_path_a);

        // 1. In-process (`NO_DAEMON`) path: `try_local_zygote_eval_with_args` resolves context A,
        // `after_closure_snapshot` swaps live `.olean` to B, `after_worker_reply` swaps back to A.
        // Without passing the pre-resolved context into the evaluator, a second resolution would
        // execute B and `write_eval_shm_cache` would validate A's untouched snapshot, caching B's
        // output ("2") under A's key!
        TEST_NO_DAEMON.with(|c| c.set(true));
        let resolutions = std::rc::Rc::new(std::cell::Cell::new(0usize));
        let (res_cnt, to_b, b_bytes) = (resolutions.clone(), olean.clone(), b.clone());
        digest_test_hooks::set("after_closure_snapshot", move || {
            let n = res_cnt.get() + 1;
            res_cnt.set(n);
            if n == 1 {
                fs::write(&to_b, &b_bytes).unwrap();
            }
        });
        let (to_a, a_bytes) = (olean.clone(), a.clone());
        digest_test_hooks::set("after_worker_reply", move || {
            fs::write(&to_a, &a_bytes).unwrap();
        });
        let rep = try_local_zygote_eval_with_args(
            &store,
            &env_vars,
            &lean_bin,
            tc,
            &lp,
            &src,
            Some(file_name),
            60_000,
            &[],
        )
        .expect("eval must not error")
        .expect("eval must succeed on snapshot A");
        digest_test_hooks::clear();
        assert_eq!(
            resolutions.get(),
            1,
            "in-process eval must resolve closure snapshot exactly once"
        );
        assert!(
            rep.ok && rep.messages.join("\n").trim() == "1",
            "evaluator must run on snapshot A, not swapped B: {rep:?}"
        );
        if let Some(cached) = read_cached_eval_shm_reply(&cache_path_a) {
            assert_eq!(
                cached.messages.join("\n").trim(),
                "1",
                "eval_shm_cache under A's key was poisoned with B's output: {cached:?}"
            );
        }
        let _ = fs::remove_file(&cache_path_a);

        // 2. HTTP daemon `/eval` path: if the live `.olean` swaps A -> B after the client resolves
        // A (or if a rogue/unaligned daemon reply reports another identity or unbound snapshot),
        // `/eval` rejects the mismatched identity (409) and never poisons A's `eval_shm_cache`.
        TEST_NO_DAEMON.with(|c| c.set(false));
        let srv_dir = tmp_dir.join("srv_store");
        let _ = TurboStore::open(Some(&srv_dir)).unwrap();
        let port = TcpListener::bind("127.0.0.1:0")
            .unwrap()
            .local_addr()
            .unwrap()
            .port();
        let addr = format!("127.0.0.1:{port}");
        let tok = "eval-aba-daemon-tok";
        let (srv_dir_bg, addr_bg, tok_bg) = (srv_dir.clone(), addr.clone(), tok.to_string());
        std::thread::spawn(move || {
            let _ = crate::server::run_server_with_auth(
                Some(&srv_dir_bg),
                &addr_bg,
                false,
                Some(&tok_bg),
                false,
            );
        });
        for _ in 0..40 {
            if std::net::TcpStream::connect(&addr).is_ok() {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
        let (_, exe_mtime_sec, exe_mtime_nsec, _, _) = current_exe_daemon_paths(&store).unwrap();
        let daemon_info = LocalZygoteDaemonInfo {
            addr: addr.clone(),
            pid: std::process::id(),
            exe_mtime_sec,
            exe_mtime_nsec,
            auth_token: tok.to_string(),
            policy: daemon_policy(),
            build_epoch: crate::TURBO_LEAN_BUILD_EPOCH.to_string(),
        };
        fs::write(
            store.root.join("zygote_daemon.json"),
            serde_json::to_vec(&daemon_info).unwrap(),
        )
        .unwrap();

        let (to_b2, b_bytes2) = (olean.clone(), b.clone());
        digest_test_hooks::set("after_closure_snapshot", move || {
            fs::write(&to_b2, &b_bytes2).unwrap();
        });
        let daemon_mismatch = try_local_zygote_eval_with_args(
            &store,
            &env_vars,
            &lean_bin,
            tc,
            &lp,
            &src,
            Some(file_name),
            60_000,
            &[],
        );
        digest_test_hooks::clear();
        fs::write(&olean, &a).unwrap();
        assert!(
            daemon_mismatch
                .as_ref()
                .is_err_and(|e| e.to_string().contains("eval execution identity changed")),
            "daemon /eval must reject execution_identity mismatch with HTTP 409: {daemon_mismatch:?}"
        );
        assert!(
            !cache_path_a.exists(),
            "mismatched daemon /eval must never populate A's eval_shm_cache"
        );

        let daemon_ok = try_local_zygote_eval_with_args(
            &store,
            &env_vars,
            &lean_bin,
            tc,
            &lp,
            &src,
            Some(file_name),
            60_000,
            &[],
        )
        .expect("daemon /eval must not error")
        .expect("daemon /eval must succeed when identity matches");
        assert!(
            daemon_ok.ok && daemon_ok.messages.join("\n").trim() == "1",
            "unexpected daemon reply: {daemon_ok:?}"
        );
        let cached_daemon = read_cached_eval_shm_reply(&cache_path_a)
            .expect("aligned Bound daemon /eval must populate eval_shm_cache");
        assert_eq!(cached_daemon.messages.join("\n").trim(), "1");

        let _ = fs::remove_file(&cache_path_a);
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[cfg(unix)]
    #[test]
    fn test_materialized_closure_directory_aba_swap_is_detected_and_never_poisons_cache() {
        use std::os::unix::fs::PermissionsExt;

        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("dir_aba") else {
            return;
        };
        let tc = "leanprover/lean4:v4.35.0";
        let lib = tmp_dir.join("lib");
        fs::create_dir_all(lib.join("Pkg")).unwrap();
        let build_b = tmp_dir.join("build_b");
        fs::create_dir_all(build_b.join("Pkg")).unwrap();

        let a = compile_test_olean(&lean_bin, &lib, "Pkg/Mod", "def pkgVal : Nat := 1\n");
        let b = compile_test_olean(&lean_bin, &build_b, "Pkg/Mod", "def pkgVal : Nat := 2\n");
        fs::write(lib.join("Pkg/Mod.olean"), &a).unwrap();

        let lp = lib.to_string_lossy().to_string();
        let ctx_a = resolve_zygote_context(tc, &lp, &env_vars, &lean_bin, "Pkg.Mod");
        let snap = ctx_a
            .closure
            .materialized
            .as_ref()
            .expect("closure materialized");
        let snap_dir = snap.dir.clone();
        let snap_pkg = snap_dir.join("Pkg");
        let leaf_a_before =
            OleanFileStatSig::from_meta(&fs::symlink_metadata(snap_pkg.join("Mod.olean")).unwrap());

        // Normal snapshot creation must seal both the snapshot root and subdirectories `0o500`
        // and store last-used metadata outside the snapshot tree.
        assert_eq!(
            fs::symlink_metadata(&snap_dir)
                .unwrap()
                .permissions()
                .mode()
                & 0o777,
            0o500
        );
        assert_eq!(
            fs::symlink_metadata(&snap_pkg)
                .unwrap()
                .permissions()
                .mode()
                & 0o777,
            0o500
        );
        assert!(
            closure_snapshot_root()
                .join(CLOSURE_SNAPSHOT_USAGE_DIR)
                .join(&snap.label)
                .is_file(),
            "last-used metadata must live outside the sealed snapshot tree"
        );
        assert_eq!(ctx_a.closure.binding(), ClosureBinding::Bound);

        // Stage a replacement `Pkg_B` directory on the SAME filesystem as `closure_snapshot_root()`
        // (`rename(2)` across subdirectories updates `..` on `Pkg`, which on Linux also requires
        // `Pkg` to be writable if moving between different parent dirs, whereas renaming `Pkg`
        // within the SAME parent `snap_dir` (`Pkg` -> `Pkg.orig`, `Pkg.evil` -> `Pkg`) does NOT
        // change `Pkg`'s parent `..` and thus never touches `Pkg`'s `ctime` or leaf file `Mod.olean`!).
        // Staging `stage_pkg_b` and `saved_pkg_a` inside `closure_snapshot_root()/.last-used`
        // keeps them on the exact same device as `snap_dir` while outside `snap_dir` at rest!
        let same_dev_scratch = closure_snapshot_root().join(CLOSURE_SNAPSHOT_USAGE_DIR);
        let stage_b = same_dev_scratch.join(format!("stage_pkg_b_{}", next_tmp_id()));
        let saved_a = same_dev_scratch.join(format!("saved_pkg_a_{}", next_tmp_id()));
        fs::create_dir_all(&stage_b).unwrap();
        fs::write(stage_b.join("Mod.olean"), &b).unwrap();
        fs::set_permissions(&stage_b, fs::Permissions::from_mode(0o500)).unwrap();

        // Notice: within `snap_dir`, renaming `Pkg` -> `Pkg.bak` (same parent directory!) works
        // even when `Pkg` itself is `0o500`, keeping `Pkg`'s own inode/ctime AND `Mod.olean`
        // completely untouched! Moving `stage_b` into `snap_dir/Pkg` only needs `stage_b` to be
        // `0o700` during the cross-parent rename.
        let in_place_bak = snap_dir.join(".pkg_orig");

        // 1. Direct `MaterializedClosure::binding()` unit proof: when `Pkg` is renamed
        // `Pkg` -> `.pkg_orig`, `stage_b` -> `Pkg`, and restored `.pkg_orig` -> `Pkg` + `0o500`
        // on `snap_dir`, the leaf `Pkg/Mod.olean` inode and stat tuple remain completely
        // identical (the exact blind spot of leaf-only stat checks!), while both `snap_dir` and
        // `Pkg/` advance `ctime` past `fence`, so `binding()` returns `Changed`.
        fs::set_permissions(&snap_dir, fs::Permissions::from_mode(0o700)).unwrap();
        fs::set_permissions(&stage_b, fs::Permissions::from_mode(0o700)).unwrap();
        fs::rename(&snap_pkg, &in_place_bak).unwrap();
        fs::rename(&stage_b, &snap_pkg).unwrap();
        fs::rename(&snap_pkg, &stage_b).unwrap();
        fs::rename(&in_place_bak, &snap_pkg).unwrap();
        fs::set_permissions(&snap_dir, fs::Permissions::from_mode(0o500)).unwrap();
        let leaf_a_after =
            OleanFileStatSig::from_meta(&fs::symlink_metadata(snap_pkg.join("Mod.olean")).unwrap());
        assert_eq!(
            leaf_a_before, leaf_a_after,
            "leaf file stat tuple must be identical across directory ABA swap"
        );
        assert_eq!(
            ctx_a.closure.binding(),
            ClosureBinding::Changed,
            "directory rename ABA swap must invalidate MaterializedClosure::binding()"
        );

        // Re-resolve cleanly so `snap_dir` has fresh verified directory stats & fence.
        purge_snapshot_dir(&snap_dir);
        let ctx_clean = resolve_zygote_context(tc, &lp, &env_vars, &lean_bin, "Pkg.Mod");
        let snap_dir = ctx_clean.closure.materialized.as_ref().unwrap().dir.clone();
        let file_name = "dir_aba_eval.lean";
        let src = "import Pkg.Mod\n#eval pkgVal\n";
        let caller_cwd = env_vars.get("TURBO_LEAN_CALLER_CWD").cloned().or_else(|| {
            std::env::current_dir()
                .ok()
                .map(|p| p.to_string_lossy().to_string())
        });
        let cache_name_a =
            compute_eval_shm_cache_filename(&ctx_clean, file_name, caller_cwd.as_deref(), src, &[])
                .unwrap();
        let cache_path_a = store
            .fast_staging_dir()
            .join("eval_shm_cache")
            .join(&cache_name_a);
        let _ = fs::remove_file(&cache_path_a);

        // 2. End-to-end fault injection across worker import: swap `Pkg/` -> `stage_b` in
        // `after_closure_snapshot` (only on the first attempt) using same-parent backup
        // `.pkg_orig` so `Pkg/` itself keeps mode `0o500` and identical stat tuple, and restore
        // `Pkg/` + `0o500` in `after_worker_reply` before `closure.binding()` runs.
        let swapped_once = std::rc::Rc::new(std::cell::Cell::new(false));
        let swapped_active = std::rc::Rc::new(std::cell::Cell::new(false));
        let (sd1, sb1, once1, act1) = (
            snap_dir.clone(),
            stage_b.clone(),
            swapped_once.clone(),
            swapped_active.clone(),
        );
        digest_test_hooks::set("after_closure_snapshot", move || {
            if !once1.get() && sd1.join("Pkg").is_dir() {
                once1.set(true);
                act1.set(true);
                fs::set_permissions(&sd1, fs::Permissions::from_mode(0o700)).unwrap();
                fs::set_permissions(&sb1, fs::Permissions::from_mode(0o700)).unwrap();
                fs::rename(sd1.join("Pkg"), sd1.join(".pkg_orig")).unwrap();
                fs::rename(&sb1, sd1.join("Pkg")).unwrap();
            }
        });
        let (sd2, sb2, act2) = (snap_dir.clone(), stage_b.clone(), swapped_active.clone());
        digest_test_hooks::set("after_worker_reply", move || {
            if act2.replace(false) {
                fs::rename(sd2.join("Pkg"), &sb2).unwrap();
                fs::rename(sd2.join(".pkg_orig"), sd2.join("Pkg")).unwrap();
                fs::set_permissions(&sd2, fs::Permissions::from_mode(0o500)).unwrap();
            }
        });

        // Exercise `eval_with_zygote_pool` (tactic/theorem check): attempt 1 imports B (`pkgVal = 2`),
        // `after_worker_reply` restores `Pkg/` to A, `binding()` detects `Changed`, drops the
        // tainted worker without caching `mod_two`, and retries cleanly on rebuilt snapshot A!
        let wrong_thm = "import Pkg.Mod\ntheorem mod_two : pkgVal = 2 := rfl\n";
        let rep_thm =
            eval_with_zygote_pool(&store, tc, &lp, &env_vars, &lean_bin, wrong_thm, false).unwrap();
        digest_test_hooks::clear();
        assert!(swapped_once.get(), "directory ABA hook must have fired");
        assert!(
            !rep_thm.ok,
            "directory ABA swap during import must be caught, retried on A, and reject theorem proved on B: {rep_thm:?}"
        );
        // Subsequent warm-pool call must also see A, never a tainted pooled worker or shard cache.
        let rep_warm =
            eval_with_zygote_pool(&store, tc, &lp, &env_vars, &lean_bin, wrong_thm, false).unwrap();
        assert!(
            !rep_warm.ok,
            "warm pool / verified shard cache must not retain B's env or verdict: {rep_warm:?}"
        );
        let right_thm = "import Pkg.Mod\ntheorem mod_one : pkgVal = 1 := rfl\n";
        assert!(
            eval_with_zygote_pool(&store, tc, &lp, &env_vars, &lean_bin, right_thm, false)
                .unwrap()
                .ok
        );

        // Also verify `try_local_zygote_eval_with_args` (`eval_shm_cache`) never caches B's output:
        // under single-snapshot execution, `eval_with_resolved_context_opts_with_args` runs A's
        // pre-resolved context (`after_closure_snapshot` already ran during `resolve_zygote_context`),
        // so inject the swap right before `try_local_zygote_eval_with_args` by hooking
        // `after_closure_snapshot` when `try_local_zygote_eval_with_args` resolves context!
        TEST_NO_DAEMON.with(|c| c.set(true));
        let swapped_eval_once = std::rc::Rc::new(std::cell::Cell::new(false));
        let swapped_eval_active = std::rc::Rc::new(std::cell::Cell::new(false));
        let (sd3, sb3, once3, act3) = (
            snap_dir.clone(),
            stage_b.clone(),
            swapped_eval_once.clone(),
            swapped_eval_active.clone(),
        );
        digest_test_hooks::set("after_closure_snapshot", move || {
            if !once3.get() && sd3.join("Pkg").is_dir() {
                once3.set(true);
                act3.set(true);
                fs::set_permissions(&sd3, fs::Permissions::from_mode(0o700)).unwrap();
                fs::set_permissions(&sb3, fs::Permissions::from_mode(0o700)).unwrap();
                fs::rename(sd3.join("Pkg"), sd3.join(".pkg_orig")).unwrap();
                fs::rename(&sb3, sd3.join("Pkg")).unwrap();
            }
        });
        let (sd4, sb4, act4) = (
            snap_dir.clone(),
            stage_b.clone(),
            swapped_eval_active.clone(),
        );
        digest_test_hooks::set("after_worker_reply", move || {
            if act4.replace(false) {
                fs::rename(sd4.join("Pkg"), &sb4).unwrap();
                fs::rename(sd4.join(".pkg_orig"), sd4.join("Pkg")).unwrap();
                fs::set_permissions(&sd4, fs::Permissions::from_mode(0o500)).unwrap();
            }
        });
        let rep_eval = try_local_zygote_eval_with_args(
            &store,
            &env_vars,
            &lean_bin,
            tc,
            &lp,
            src,
            Some(file_name),
            60_000,
            &[],
        )
        .expect("eval must not error")
        .expect("eval must recover on retry with clean snapshot A");
        digest_test_hooks::clear();
        TEST_NO_DAEMON.with(|c| c.set(false));
        assert!(swapped_eval_once.get());
        assert!(
            rep_eval.ok && rep_eval.messages.join("\n").trim() == "1",
            "eval after directory ABA swap must return A's output (1), not B's (2): {rep_eval:?}"
        );
        if let Some(cached) = read_cached_eval_shm_reply(&cache_path_a) {
            assert_eq!(
                cached.messages.join("\n").trim(),
                "1",
                "eval_shm_cache must never contain B's output: {cached:?}"
            );
        }

        let _ = fs::remove_file(&cache_path_a);
        purge_snapshot_dir(&stage_b);
        purge_snapshot_dir(&saved_a);
        purge_snapshot_dir(&snap_dir);
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[cfg(unix)]
    #[test]
    fn test_materialized_closure_ancestor_directory_aba_swap_never_poisons_caches() {
        use std::os::unix::fs::PermissionsExt;

        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("ancestor_dir_aba")
        else {
            return;
        };
        struct ResetCacheBase;
        impl Drop for ResetCacheBase {
            fn drop(&mut self) {
                TEST_CLOSURE_SNAPSHOT_CACHE_BASE.with(|c| *c.borrow_mut() = None);
                TEST_NO_DAEMON.with(|c| c.set(false));
                digest_test_hooks::clear();
            }
        }
        let _reset_guard = ResetCacheBase;

        // 1. Verify `ensure_private_dir` creates missing nested parent components under
        // `closure_cache_base()` with mode `0o700` from birth (never world/group-traversable).
        let private_cache_base = tmp_dir.join("nested_missing/parent_dir/turbo-lean-cache");
        TEST_CLOSURE_SNAPSHOT_CACHE_BASE
            .with(|c| *c.borrow_mut() = Some(private_cache_base.clone()));
        let snap_root = ensure_private_dir(&closure_snapshot_root()).unwrap();
        assert_eq!(
            fs::symlink_metadata(&private_cache_base)
                .unwrap()
                .permissions()
                .mode()
                & 0o777,
            0o700,
            "missing cache_root parent must be created with 0o700"
        );
        assert_eq!(
            fs::symlink_metadata(&snap_root)
                .unwrap()
                .permissions()
                .mode()
                & 0o777,
            0o700,
            "closure-snapshots root must be created with 0o700"
        );
        // Also verify `ensure_private_dir` tightens pre-existing permissive `0o755` parents under `cache_root()`.
        fs::set_permissions(&private_cache_base, fs::Permissions::from_mode(0o755)).unwrap();
        let _ = ensure_private_dir(&closure_snapshot_root()).unwrap();
        assert_eq!(
            fs::symlink_metadata(&private_cache_base)
                .unwrap()
                .permissions()
                .mode()
                & 0o777,
            0o700,
            "permissive cache_root parent must be tightened to 0o700"
        );

        let tc = "leanprover/lean4:v4.35.0";
        let lib = tmp_dir.join("lib");
        fs::create_dir_all(lib.join("Pkg")).unwrap();
        let build_b = tmp_dir.join("build_b");
        fs::create_dir_all(build_b.join("Pkg")).unwrap();

        let a = compile_test_olean(&lean_bin, &lib, "Pkg/Mod", "def pkgVal : Nat := 1\n");
        let b = compile_test_olean(&lean_bin, &build_b, "Pkg/Mod", "def pkgVal : Nat := 2\n");
        fs::write(lib.join("Pkg/Mod.olean"), &a).unwrap();

        let lp = lib.to_string_lossy().to_string();
        let ctx_a = resolve_zygote_context(tc, &lp, &env_vars, &lean_bin, "Pkg.Mod");
        let snap = ctx_a
            .closure
            .materialized
            .as_ref()
            .expect("closure materialized");
        let label = snap.label.clone();
        let snap_dir = snap.dir.clone();
        assert_eq!(ctx_a.closure.binding(), ClosureBinding::Bound);

        // Stage a complete fake `closure-snapshots` root (`fake_root/<label>/Pkg/Mod.olean` = B)
        // on the same filesystem so `rename(snap_root, saved_root)` + `rename(fake_root, snap_root)`
        // swaps the ancestor directory ABOVE `<snap_root>/<label>` without touching `<label>` or
        // any of its descendants!
        let saved_root = private_cache_base.join("closure-snapshots.saved");
        let fake_root = private_cache_base.join("closure-snapshots.fake");
        let fake_label_dir = fake_root.join(&label);
        fs::create_dir_all(fake_label_dir.join("Pkg")).unwrap();
        fs::write(fake_label_dir.join("Pkg/Mod.olean"), &b).unwrap();
        let mut ro_perms = fs::metadata(fake_label_dir.join("Pkg/Mod.olean"))
            .unwrap()
            .permissions();
        ro_perms.set_readonly(true);
        fs::set_permissions(fake_label_dir.join("Pkg/Mod.olean"), ro_perms).unwrap();
        fs::set_permissions(
            fake_label_dir.join("Pkg"),
            fs::Permissions::from_mode(0o500),
        )
        .unwrap();
        fs::set_permissions(&fake_label_dir, fs::Permissions::from_mode(0o500)).unwrap();

        let dir_sig_before = OleanFileStatSig::from_meta(&fs::symlink_metadata(&snap_dir).unwrap());
        let leaf_sig_before = OleanFileStatSig::from_meta(
            &fs::symlink_metadata(snap_dir.join("Pkg/Mod.olean")).unwrap(),
        );

        // 2. While `snap_root` is swapped to `fake_root`, `ctx_a.closure.binding()` MUST observe
        // `Changed` (pathname `<snap_root>/<label>` now points to `fake_label_dir`).
        fs::rename(&snap_root, &saved_root).unwrap();
        fs::rename(&fake_root, &snap_root).unwrap();
        assert_eq!(
            ctx_a.closure.binding(),
            ClosureBinding::Changed,
            "active ancestor swap must invalidate binding()"
        );
        // Restore `saved_root` -> `snap_root`: notice `<snap_root>/<label>` and `Pkg/Mod.olean`
        // have the EXACT SAME `(dev, ino, mtime, ctime)` and `0o500` mode as before!
        fs::rename(&snap_root, &fake_root).unwrap();
        fs::rename(&saved_root, &snap_root).unwrap();
        assert_eq!(
            OleanFileStatSig::from_meta(&fs::symlink_metadata(&snap_dir).unwrap()),
            dir_sig_before,
            "ancestor ABA swap leaves <label> stat signature completely unchanged"
        );
        assert_eq!(
            OleanFileStatSig::from_meta(
                &fs::symlink_metadata(snap_dir.join("Pkg/Mod.olean")).unwrap()
            ),
            leaf_sig_before,
            "ancestor ABA swap leaves leaf file stat signature completely unchanged"
        );

        // 3. End-to-end fault injection across `eval_with_zygote_pool`:
        // Swap `closure-snapshots` -> `fake_root` in `after_closure_snapshot` (while the worker
        // spawns and imports `Pkg.Mod`), and restore `saved_root` -> `closure-snapshots` in
        // `after_worker_reply` BEFORE `closure.binding()` runs.
        // Because the worker imports through its pinned directory FD (`/proc/self/fd/<fd>` on Linux)
        // or `binding()` catches the ancestor swap, `theorem mod_two : pkgVal = 2 := rfl` MUST be
        // rejected and MUST NOT poison `ZYGOTE_VERIFIED_SHARD_CACHE` or the warm `ZYGOTE_POOL`!
        let swapped_once = std::rc::Rc::new(std::cell::Cell::new(false));
        let swapped_active = std::rc::Rc::new(std::cell::Cell::new(false));
        let (sr1, sv1, fk1, once1, act1) = (
            snap_root.clone(),
            saved_root.clone(),
            fake_root.clone(),
            swapped_once.clone(),
            swapped_active.clone(),
        );
        digest_test_hooks::set("after_closure_snapshot", move || {
            if !once1.get() && sr1.is_dir() && fk1.is_dir() {
                once1.set(true);
                act1.set(true);
                fs::rename(&sr1, &sv1).unwrap();
                fs::rename(&fk1, &sr1).unwrap();
            }
        });
        let (sr2, sv2, fk2, act2) = (
            snap_root.clone(),
            saved_root.clone(),
            fake_root.clone(),
            swapped_active.clone(),
        );
        digest_test_hooks::set("after_worker_reply", move || {
            if act2.replace(false) {
                fs::rename(&sr2, &fk2).unwrap();
                fs::rename(&sv2, &sr2).unwrap();
            }
        });

        let wrong_thm = "import Pkg.Mod\ntheorem mod_two : pkgVal = 2 := rfl\n";
        let rep_thm =
            eval_with_zygote_pool(&store, tc, &lp, &env_vars, &lean_bin, wrong_thm, false).unwrap();
        digest_test_hooks::clear();
        assert!(swapped_once.get(), "ancestor ABA hook must have fired");
        assert!(
            !rep_thm.ok,
            "ancestor directory ABA swap during import must never prove theorem on B: {rep_thm:?}"
        );

        // Subsequent warm-pool / verified-shard-cache call must also reject `pkgVal = 2` and prove `pkgVal = 1`.
        let rep_warm =
            eval_with_zygote_pool(&store, tc, &lp, &env_vars, &lean_bin, wrong_thm, false).unwrap();
        assert!(
            !rep_warm.ok,
            "warm pool / verified shard cache must not retain B's env or verdict: {rep_warm:?}"
        );
        let right_thm = "import Pkg.Mod\ntheorem mod_one : pkgVal = 1 := rfl\n";
        assert!(
            eval_with_zygote_pool(&store, tc, &lp, &env_vars, &lean_bin, right_thm, false)
                .unwrap()
                .ok
        );

        // 4. End-to-end fault injection across `try_local_zygote_eval_with_args` (`eval_shm_cache`):
        // Clear idle workers for this snapshot (`snap_dir`) so `try_local_zygote_eval_with_args`
        // spawns/imports fresh while `closure-snapshots` is swapped to `fake_root`, then restores
        // before `binding()`.
        if let Some(pool) = ZYGOTE_POOL.get() {
            if let Ok(mut guard) = pool.lock() {
                guard.retain(|(_, lp_key, _), _| {
                    !lp_key.starts_with(&snap_dir.to_string_lossy().to_string())
                });
            }
        }
        let ctx_eval = resolve_zygote_context(tc, &lp, &env_vars, &lean_bin, "Pkg.Mod");
        let file_name = "ancestor_dir_aba_eval.lean";
        let src = "import Pkg.Mod\n#eval pkgVal\n";
        let caller_cwd = env_vars.get("TURBO_LEAN_CALLER_CWD").cloned().or_else(|| {
            std::env::current_dir()
                .ok()
                .map(|p| p.to_string_lossy().to_string())
        });
        let cache_name_a =
            compute_eval_shm_cache_filename(&ctx_eval, file_name, caller_cwd.as_deref(), src, &[])
                .unwrap();
        let cache_path_a = store
            .fast_staging_dir()
            .join("eval_shm_cache")
            .join(&cache_name_a);
        let _ = fs::remove_file(&cache_path_a);

        TEST_NO_DAEMON.with(|c| c.set(true));
        let swapped_eval_once = std::rc::Rc::new(std::cell::Cell::new(false));
        let swapped_eval_active = std::rc::Rc::new(std::cell::Cell::new(false));
        let (sr3, sv3, fk3, once3, act3) = (
            snap_root.clone(),
            saved_root.clone(),
            fake_root.clone(),
            swapped_eval_once.clone(),
            swapped_eval_active.clone(),
        );
        digest_test_hooks::set("after_closure_snapshot", move || {
            if !once3.get() && sr3.is_dir() && fk3.is_dir() {
                once3.set(true);
                act3.set(true);
                fs::rename(&sr3, &sv3).unwrap();
                fs::rename(&fk3, &sr3).unwrap();
            }
        });
        let (sr4, sv4, fk4, act4) = (
            snap_root.clone(),
            saved_root.clone(),
            fake_root.clone(),
            swapped_eval_active.clone(),
        );
        digest_test_hooks::set("after_worker_reply", move || {
            if act4.replace(false) {
                fs::rename(&sr4, &fk4).unwrap();
                fs::rename(&sv4, &sr4).unwrap();
            }
        });
        let rep_eval = try_local_zygote_eval_with_args(
            &store,
            &env_vars,
            &lean_bin,
            tc,
            &lp,
            src,
            Some(file_name),
            60_000,
            &[],
        )
        .expect("eval must not error")
        .expect("eval must return A's output despite ancestor ABA swap");
        digest_test_hooks::clear();
        TEST_NO_DAEMON.with(|c| c.set(false));
        assert!(swapped_eval_once.get());
        assert!(
            rep_eval.ok && rep_eval.messages.join("\n").trim() == "1",
            "eval during ancestor ABA swap must return A's output (1), never B's (2): {rep_eval:?}"
        );
        if let Some(cached) = read_cached_eval_shm_reply(&cache_path_a) {
            assert_eq!(
                cached.messages.join("\n").trim(),
                "1",
                "eval_shm_cache must never contain B's output: {cached:?}"
            );
        }

        let _ = fs::remove_file(&cache_path_a);
        if let Some(pool) = ZYGOTE_POOL.get() {
            if let Ok(mut guard) = pool.lock() {
                guard.retain(|(_, lp_key, _), _| {
                    !lp_key.starts_with(&snap_dir.to_string_lossy().to_string())
                });
            }
        }
        purge_snapshot_dir(&fake_label_dir);
        purge_snapshot_dir(&snap_dir);
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_run_audited_lean_shard_at_rejects_live_source_toctou_and_aba_swap() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("audited_toctou")
        else {
            return;
        };
        struct ResetHooks;
        impl Drop for ResetHooks {
            fn drop(&mut self) {
                digest_test_hooks::clear();
            }
        }
        let _reset = ResetHooks;

        let live_file = tmp_dir.join("LiveToctou.lean");
        let in_mem_false = "theorem target : False := by trivial\n";
        let disk_true = "theorem target : True := trivial\n";
        let audit_targets: std::collections::HashSet<String> =
            ["_root_.target".to_string()].into_iter().collect();

        // Case A: file on disk overwritten before `lean` runs and left as `True`.
        fs::write(&live_file, in_mem_false).unwrap();
        let lf_a = live_file.clone();
        digest_test_hooks::set("audited_shard_before_lean", move || {
            fs::write(&lf_a, disk_true).unwrap();
        });
        let err_a = run_audited_lean_shard_at(
            &store.root,
            &store.fast_staging_dir(),
            &lean_bin,
            &env_vars,
            Some(&tmp_dir),
            Some(&live_file),
            in_mem_false,
            &audit_targets,
            false,
            &[],
            Some(60_000),
        )
        .expect_err("must reject live source overwrite to True before lean");
        assert!(
            format!("{err_a:#}").contains("KernelGate"),
            "unexpected error for Case A: {err_a:#}"
        );
        digest_test_hooks::clear();

        // Case B: ABA swap — overwritten with `True` before `lean`, then restored to `False` right after `lean`!
        fs::write(&live_file, in_mem_false).unwrap();
        let lf_b1 = live_file.clone();
        let lf_b2 = live_file.clone();
        digest_test_hooks::set("audited_shard_before_lean", move || {
            fs::write(&lf_b1, disk_true).unwrap();
        });
        digest_test_hooks::set("audited_shard_after_lean", move || {
            fs::write(&lf_b2, in_mem_false).unwrap();
        });
        let err_b = run_audited_lean_shard_at(
            &store.root,
            &store.fast_staging_dir(),
            &lean_bin,
            &env_vars,
            Some(&tmp_dir),
            Some(&live_file),
            in_mem_false,
            &audit_targets,
            false,
            &[],
            Some(60_000),
        )
        .expect_err("must reject ABA live source swap (False -> True -> False)");
        assert!(
            format!("{err_b:#}").contains("KernelGate"),
            "unexpected error for Case B: {err_b:#}"
        );
        digest_test_hooks::clear();

        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_daemon_eval_with_lake_input_dir_needs_tracks_edits_without_identity_mismatch() {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let Some((tmp_dir, store, mut env_vars, lean_bin)) =
            open_test_zygote_env("daemon_eval_lake_inputs")
        else {
            return;
        };
        TEST_NO_DAEMON.with(|c| c.set(false));

        let tc = "leanprover/lean4:v4.35.0";
        let proj_dir = tmp_dir.join("workspace");
        let outside_dir = tmp_dir.join("outside");
        fs::create_dir_all(proj_dir.join("Data")).unwrap();
        fs::create_dir_all(&outside_dir).unwrap();
        fs::write(
            proj_dir.join("lean-toolchain"),
            include_str!("../../../lean/lean-toolchain"),
        )
        .unwrap();
        fs::write(
            proj_dir.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage demo\ninput_dir smokeSources where\n  path := \"Data\"\n  filter := .extension \"sol\"\n@[default_target]\nlean_lib Smoke where\n  globs := #[.submodules `Smoke]\n  needs := #[smokeSources]\n",
        )
        .unwrap();
        let input_path = proj_dir.join("Data/a.sol");
        fs::write(&input_path, "contract A {}").unwrap();

        let srv_dir = tmp_dir.join("srv_store");
        let _ = TurboStore::open(Some(&srv_dir)).unwrap();
        let port = TcpListener::bind("127.0.0.1:0")
            .unwrap()
            .local_addr()
            .unwrap()
            .port();
        let addr = format!("127.0.0.1:{port}");
        let tok = "eval-lake-inputs-daemon-tok";
        let (srv_dir_bg, addr_bg, tok_bg) = (srv_dir.clone(), addr.clone(), tok.to_string());
        std::thread::spawn(move || {
            let _ = crate::server::run_server_with_auth(
                Some(&srv_dir_bg),
                &addr_bg,
                false,
                Some(&tok_bg),
                false,
            );
        });
        for _ in 0..40 {
            if std::net::TcpStream::connect(&addr).is_ok() {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
        let (_, exe_mtime_sec, exe_mtime_nsec, daemon_cache_dir, state_file) =
            current_exe_daemon_paths(&store).unwrap();
        fs::create_dir_all(&daemon_cache_dir).unwrap();
        let daemon_info = LocalZygoteDaemonInfo {
            addr: addr.clone(),
            pid: std::process::id(),
            exe_mtime_sec,
            exe_mtime_nsec,
            auth_token: tok.to_string(),
            policy: daemon_policy(),
            build_epoch: crate::TURBO_LEAN_BUILD_EPOCH.to_string(),
        };
        let daemon_json = serde_json::to_vec(&daemon_info).unwrap();
        fs::write(&state_file, &daemon_json).unwrap();
        fs::write(store.root.join("zygote_daemon.json"), &daemon_json).unwrap();

        let canon_proj = proj_dir.canonicalize().unwrap_or_else(|_| proj_dir.clone());
        let canon_outside = outside_dir
            .canonicalize()
            .unwrap_or_else(|_| outside_dir.clone());
        env_vars.remove("LEAN_PATH");
        env_vars.insert(
            "TURBO_LEAN_PROJECT_DIR".to_string(),
            canon_proj.to_string_lossy().to_string(),
        );
        env_vars.insert(
            "TURBO_LEAN_CALLER_CWD".to_string(),
            canon_outside.to_string_lossy().to_string(),
        );

        let scratch_file = canon_proj.join("Scratch.lean");
        let scratch_name = scratch_file.to_string_lossy().to_string();
        let src = format!(
            "def solText : String := include_str \"Data/a.sol\"\n-- {}\n#eval solText\n",
            next_tmp_id()
        );

        crate::module_builder::reset_lake_inputs_tag_memo();
        let rep1 = try_local_zygote_eval_with_args(
            &store,
            &env_vars,
            &lean_bin,
            tc,
            "",
            &src,
            Some(&scratch_name),
            60_000,
            &[],
        )
        .expect("daemon /eval must not error")
        .expect("daemon /eval must preserve TURBO_LEAN_PROJECT_DIR and match execution_identity");
        assert!(
            rep1.ok && rep1.messages.join("\n").contains("contract A {}"),
            "unexpected daemon /eval v1 reply: {rep1:?}"
        );
        let (imports, _) = split_shard_for_zygote(&src);
        crate::module_builder::reset_lake_inputs_tag_memo();
        let ctx1 = resolve_zygote_context(tc, "", &env_vars, &lean_bin, &imports);
        let cache_name1 = compute_eval_shm_cache_filename(
            &ctx1,
            &scratch_name,
            env_vars.get("TURBO_LEAN_CALLER_CWD").map(String::as_str),
            &src,
            &[],
        )
        .unwrap();
        let cache_path1 = store
            .fast_staging_dir()
            .join("eval_shm_cache")
            .join(&cache_name1);
        assert!(
            read_cached_eval_shm_reply(&cache_path1).is_some(),
            "Bound daemon /eval on Lake-input workspace must populate eval_shm_cache"
        );

        // Also verify when `file_name` is bare (`None` or `"Bare.lean"` without parent dir) and
        // `cwd` is outside the project, `TURBO_LEAN_PROJECT_DIR` is still forwarded and matched
        // without HTTP 409 identity mismatch.
        let bare_src = format!("-- {}\n#eval (41 + 1)\n", next_tmp_id());
        crate::module_builder::reset_lake_inputs_tag_memo();
        let bare_rep = try_local_zygote_eval_with_args(
            &store,
            &env_vars,
            &lean_bin,
            tc,
            "",
            &bare_src,
            Some("Bare.lean"),
            60_000,
            &[],
        )
        .expect("daemon /eval must not error")
        .expect(
            "daemon /eval with bare file_name and outside cwd must forward TURBO_LEAN_PROJECT_DIR",
        );
        assert!(bare_rep.ok && bare_rep.messages.join("\n").trim() == "42");
        let (bare_imports, _) = split_shard_for_zygote(&bare_src);
        crate::module_builder::reset_lake_inputs_tag_memo();
        let bare_ctx = resolve_zygote_context(tc, "", &env_vars, &lean_bin, &bare_imports);
        let bare_cache_path = store.fast_staging_dir().join("eval_shm_cache").join(
            compute_eval_shm_cache_filename(
                &bare_ctx,
                "Bare.lean",
                env_vars.get("TURBO_LEAN_CALLER_CWD").map(String::as_str),
                &bare_src,
                &[],
            )
            .unwrap(),
        );

        fs::write(&input_path, "contract B {}").unwrap();
        crate::module_builder::reset_lake_inputs_tag_memo();
        let rep2 = try_local_zygote_eval_with_args(
            &store,
            &env_vars,
            &lean_bin,
            tc,
            "",
            &src,
            Some(&scratch_name),
            60_000,
            &[],
        )
        .expect("daemon /eval must not error")
        .expect("daemon /eval after input_dir edit must succeed with updated identity");
        assert!(
            rep2.ok && rep2.messages.join("\n").contains("contract B {}"),
            "daemon /eval must observe edited input_dir file instead of stale eval_shm_cache or worker: {rep2:?}"
        );

        crate::module_builder::reset_lake_inputs_tag_memo();
        let ctx2 = resolve_zygote_context(tc, "", &env_vars, &lean_bin, &imports);
        assert_ne!(
            ctx1.identity, ctx2.identity,
            "editing declared input_dir file must rotate execution_identity"
        );
        let cache_name2 = compute_eval_shm_cache_filename(
            &ctx2,
            &scratch_name,
            env_vars.get("TURBO_LEAN_CALLER_CWD").map(String::as_str),
            &src,
            &[],
        )
        .unwrap();
        let cache_path2 = store
            .fast_staging_dir()
            .join("eval_shm_cache")
            .join(&cache_name2);
        assert_ne!(cache_name1, cache_name2);

        let _ = fs::remove_file(&bare_cache_path);
        let _ = fs::remove_file(&cache_path1);
        let _ = fs::remove_file(&cache_path2);
        let _ = fs::remove_file(&state_file);
        let _ = fs::remove_file(store.root.join("zygote_daemon.json"));
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_zygote_coalesced_batch_attests_only_non_stub_theorems_and_blocks_prefix_sorry() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("coal_decl_types")
        else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";

        let clean_coalesced = "\
theorem cached_stub : True := sorry

theorem uncached_first : 1 + 1 = 2 := rfl

theorem uncached_second : 2 + 2 = 4 := rfl
";
        let rep_ok = eval_with_zygote_pool_for_targets(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            clean_coalesced,
            &[
                "_root_.uncached_first".to_string(),
                "_root_.uncached_second".to_string(),
            ],
            None,
            &[],
        )
        .unwrap();
        assert!(rep_ok.ok && rep_ok.kernel_gate_active, "{rep_ok:?}");
        assert!(
            !rep_ok.decl_types.contains_key("cached_stub"),
            "explicit sorry stub in prefix must not be attested as a verified theorem: {:?}",
            rep_ok.decl_types
        );
        assert!(
            rep_ok.decl_types.contains_key("uncached_first")
                && rep_ok.decl_types.contains_key("uncached_second"),
            "all non-stub theorems across prefix and body must be attested: {:?}",
            rep_ok.decl_types
        );

        let sneaky_coalesced = "\
theorem cached_stub : True := sorry

theorem sneaky_in_prefix : 1 = 2 := by sorry

theorem uncached_tail : 2 + 2 = 4 := rfl
";
        let rep_bad = eval_with_zygote_pool_for_targets(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            sneaky_coalesced,
            &["_root_.uncached_tail".to_string()],
            None,
            &[],
        )
        .unwrap();
        assert!(
            !rep_bad.ok,
            "tactic sorry inside non-stub theorem in prefix must be rejected even with allow_stub: {rep_bad:?}"
        );
        assert!(
            rep_bad
                .errors
                .iter()
                .any(|e| e.contains("sorryAx") || e.contains("`sorry` theorem")),
            "{rep_bad:?}"
        );

        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[cfg(unix)]
    #[test]
    fn test_audit_compiled_modules_bisects_colliding_root_main_modules_across_processes() {
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_audit_main_collide_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        fs::create_dir_all(tmp_dir.join("App")).unwrap();
        fs::write(tmp_dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            tmp_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nroots = [\"App.MainA\", \"App.MainB\", \"App.Sorry\"]\n",
        )
        .unwrap();
        fs::write(
            tmp_dir.join("App/MainA.lean"),
            "def main : IO Unit := pure ()\ntheorem mainA_ok : (1 : Nat) = 1 := rfl\n",
        )
        .unwrap();
        fs::write(
            tmp_dir.join("App/MainB.lean"),
            "def main : IO UInt32 := pure 0\ntheorem mainB_ok : (2 : Nat) = 2 := rfl\n",
        )
        .unwrap();
        fs::write(
            tmp_dir.join("App/Sorry.lean"),
            "theorem t_sorry : 1 = 2 := sorry\n",
        )
        .unwrap();
        let Ok(cfg) = crate::module_builder::resolve_project_config(&tmp_dir) else {
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        };
        let env = build_auditor_bootstrap_env(&cfg);
        let ld = env.get("LD_LIBRARY_PATH").cloned().unwrap_or_default();
        let olean_dir = tmp_dir.join(".lake/build/lib/lean/App");
        fs::create_dir_all(&olean_dir).unwrap();
        for (src, olean) in [
            ("App/MainA.lean", "MainA.olean"),
            ("App/MainB.lean", "MainB.olean"),
            ("App/Sorry.lean", "Sorry.olean"),
        ] {
            let out = Command::new(&cfg.lean_bin)
                .current_dir(&tmp_dir)
                .arg("-R")
                .arg(&tmp_dir)
                .arg("-o")
                .arg(olean_dir.join(olean))
                .arg(tmp_dir.join(src))
                .env("LEAN_PATH", &cfg.toolchain_lib_lean)
                .env("LD_LIBRARY_PATH", &ld)
                .output()
                .unwrap();
            assert!(
                out.status.success(),
                "lean compile {} failed: {:?}",
                src,
                out
            );
        }
        let fake_bwrap =
            crate::module_builder::ScopedTestBwrapOverride::write_fake_bwrap_script(&tmp_dir)
                .unwrap();
        let _bwrap =
            crate::module_builder::ScopedTestBwrapOverride::set(fake_bwrap.to_string_lossy());
        let store = TurboStore::open(Some(&tmp_dir.join("store"))).unwrap();
        let (lean_path_env, _) = crate::module_builder::build_lean_search_path(&cfg, true);

        for is_untrusted in [false, true] {
            audit_compiled_modules_with_zygote(
                &store,
                &cfg,
                &["App.MainA".to_string(), "App.MainB".to_string()],
                &lean_path_env,
                &[],
                is_untrusted,
            )
            .unwrap_or_else(|e| {
                panic!("colliding root `main` modules must pass batch audit via process bisection (untrusted={is_untrusted}): {e:#}")
            });

            let err = audit_compiled_modules_with_zygote(
                &store,
                &cfg,
                &[
                    "App.MainA".to_string(),
                    "App.MainB".to_string(),
                    "App.Sorry".to_string(),
                ],
                &lean_path_env,
                &[],
                is_untrusted,
            )
            .unwrap_err()
            .to_string();
            assert!(
                err.contains("sorryAx"),
                "bisected batch audit must still reject sorryAx (untrusted={is_untrusted}): {err}"
            );
        }
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_speed4_zygote_eval_reply_attaches_timeout_hotspots_while_failing_closed() {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_speed4_zygote_hotspots_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = std::fs::remove_dir_all(&tmp_dir);
        std::fs::create_dir_all(&tmp_dir).unwrap();
        std::fs::write(
            tmp_dir.join("lean-toolchain"),
            include_str!("../../../lean/lean-toolchain"),
        )
        .unwrap();
        std::fs::write(
            tmp_dir.join("lakefile.toml"),
            "name = \"hot\"\n[[lean_lib]]\nname = \"Hot\"\n",
        )
        .unwrap();
        let Ok(cfg) = crate::module_builder::resolve_project_config(&tmp_dir) else {
            let _ = std::fs::remove_dir_all(&tmp_dir);
            return;
        };
        let store = crate::TurboStore::open(Some(&tmp_dir.join("store"))).unwrap();
        let env_vars = build_auditor_bootstrap_env(&cfg);

        let src = "\
def stepId (n : Nat) : Nat := n
@[simp] theorem loop_step (n : Nat) : stepId n = stepId (stepId n) := rfl

set_option maxHeartbeats 500 in
theorem simp_blowup (n : Nat) : stepId n = 1 := by
  simp [loop_step]
";
        let rep = eval_with_zygote_pool(
            &store,
            &cfg.toolchain,
            &cfg.toolchain_lib_lean.to_string_lossy(),
            &env_vars,
            &cfg.lean_bin,
            src,
            false,
        )
        .unwrap();

        assert!(
            !rep.ok,
            "heartbeat timeout must fail closed (`rep.ok == false`), got {:?}",
            rep
        );
        assert!(
            !rep.timeout_hotspots.is_empty() || !rep.simp_hotspots.is_empty(),
            "`ZygoteEvalReply` must directly carry `timeout_hotspots` or `simp_hotspots` on heartbeat timeout: {:?}",
            rep
        );
        let formatted = format_hotspot_diagnostics(&rep.timeout_hotspots, &rep.simp_hotspots);
        assert!(
            formatted.contains("[hotspot]"),
            "formatted hotspot diagnostics must include `[hotspot]`: {formatted}"
        );
        let _ = std::fs::remove_dir_all(&tmp_dir);
    }

    #[cfg(unix)]
    #[test]
    fn ensure_zygote_binary_at_rejects_planted_symlink_or_group_writable_cached_bin() {
        use std::os::unix::fs::PermissionsExt;
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_zygote_cached_bin_perm_{}_{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos()
        ));
        let store_1 = tmp_dir.join("store_1");
        let store_2 = tmp_dir.join("store_2");
        fs::create_dir_all(&store_1).unwrap();
        fs::create_dir_all(&store_2).unwrap();

        let proj = tmp_dir.join("proj");
        fs::create_dir_all(&proj).unwrap();
        fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"zp\"\n[[lean_lib]]\nname = \"Zp\"\n",
        )
        .unwrap();
        let Ok(cfg) = crate::module_builder::resolve_project_config(&proj) else {
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        };
        let env_vars = build_auditor_bootstrap_env(&cfg);
        let valid_bin = ensure_zygote_binary_at(&store_1, &cfg.lean_bin, &env_vars).unwrap();
        let bin_name = valid_bin.file_name().unwrap().to_os_string();

        let bin_dir_2 = store_2.join("fastcheck_bins");
        fs::create_dir_all(&bin_dir_2).unwrap();
        fs::set_permissions(&bin_dir_2, fs::Permissions::from_mode(0o777)).unwrap();

        let decoy = tmp_dir.join("decoy_bin");
        fs::write(&decoy, b"#!/bin/sh\nexit 99\n").unwrap();
        fs::set_permissions(&decoy, fs::Permissions::from_mode(0o700)).unwrap();

        let planted = bin_dir_2.join(&bin_name);
        std::os::unix::fs::symlink(&decoy, &planted).unwrap();
        let repaired = ensure_zygote_binary_at(&store_2, &cfg.lean_bin, &env_vars).unwrap();
        assert_eq!(repaired, planted);
        assert!(
            !fs::symlink_metadata(&repaired)
                .unwrap()
                .file_type()
                .is_symlink(),
            "planted symlink cached_bin must be replaced with an owned regular file"
        );
        assert_eq!(
            fs::symlink_metadata(&bin_dir_2)
                .unwrap()
                .permissions()
                .mode()
                & 0o777,
            0o700,
            "fastcheck_bins directory must be tightened to 0700"
        );

        fs::remove_file(&planted).unwrap();
        fs::write(&planted, b"corrupted").unwrap();
        fs::set_permissions(&planted, fs::Permissions::from_mode(0o775)).unwrap();
        let repaired_2 = ensure_zygote_binary_at(&store_2, &cfg.lean_bin, &env_vars).unwrap();
        assert!(owned_private_file(&repaired_2));
        assert_ne!(fs::read(&repaired_2).unwrap(), b"corrupted");

        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[cfg(unix)]
    #[test]
    fn test_audit_compiled_modules_parallel_multichunk_persists_kernel_audited_authority() {
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_audit_multichunk_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let proj = tmp_dir.join("proj");
        fs::create_dir_all(proj.join("Mc")).unwrap();
        fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        let mut mod_names = Vec::new();
        let mut roots_toml = Vec::new();
        for idx in 0..34 {
            let m = format!("Mc.M{idx:02}");
            roots_toml.push(format!("\"{m}\""));
            fs::write(
                proj.join(format!("Mc/M{idx:02}.lean")),
                format!("theorem t_{idx:02} : ({idx} : Nat) = {idx} := rfl\n"),
            )
            .unwrap();
            mod_names.push(m);
        }
        fs::write(
            proj.join("lakefile.toml"),
            format!(
                "name = \"mc_pkg\"\ndefaultTargets = [\"Mc\"]\n[[lean_lib]]\nname = \"Mc\"\nroots = [{}]\n",
                roots_toml.join(", ")
            ),
        )
        .unwrap();
        let Ok(cfg) = crate::module_builder::resolve_project_config(&proj) else {
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        };
        let env = build_auditor_bootstrap_env(&cfg);
        let ld = env.get("LD_LIBRARY_PATH").cloned().unwrap_or_default();
        let olean_dir = proj.join(".lake/build/lib/lean/Mc");
        fs::create_dir_all(&olean_dir).unwrap();
        for idx in 0..34 {
            let src = format!("Mc/M{idx:02}.lean");
            let olean = format!("M{idx:02}.olean");
            let out = Command::new(&cfg.lean_bin)
                .current_dir(&proj)
                .arg("-R")
                .arg(&proj)
                .arg("-o")
                .arg(olean_dir.join(&olean))
                .arg(proj.join(&src))
                .env("LEAN_PATH", &cfg.toolchain_lib_lean)
                .env("LD_LIBRARY_PATH", &ld)
                .output()
                .unwrap();
            assert!(out.status.success(), "lean compile {src} failed: {:?}", out);
        }
        let store_dir = tmp_dir.join("external_store");
        let store = TurboStore::open(Some(&store_dir)).unwrap();
        let (lean_path_env, _) = crate::module_builder::build_lean_search_path(&cfg, true);

        let prev_batch = std::env::var_os("TURBO_LEAN_AUDIT_BATCH_SIZE");
        let prev_jobs = std::env::var_os("TURBO_LEAN_JOBS");
        std::env::set_var("TURBO_LEAN_AUDIT_BATCH_SIZE", "1");
        std::env::set_var("TURBO_LEAN_JOBS", "2");
        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            audit_compiled_modules_with_zygote(
                &store,
                &cfg,
                &mod_names,
                &lean_path_env,
                &[],
                false,
            )
            .expect("parallel multi-chunk audit_compiled_modules_with_zygote must succeed");

            let mut lookup =
                crate::module_builder::ReplayLookupBatchCache::new(&store, &cfg, &lean_path_env);
            for m in &mod_names {
                let olean_path = lookup
                    .resolve_module_olean(m)
                    .unwrap_or_else(|| panic!("expected resolved .olean for {m}"));
                assert!(
                    lookup.is_audited_in_store(&store, &cfg, &lean_path_env, m, &olean_path),
                    "parallel multi-chunk audit must persist kernel_audited_oleans_auth for {m}"
                );
            }
        }));
        match prev_batch {
            Some(v) => std::env::set_var("TURBO_LEAN_AUDIT_BATCH_SIZE", v),
            None => std::env::remove_var("TURBO_LEAN_AUDIT_BATCH_SIZE"),
        }
        match prev_jobs {
            Some(v) => std::env::set_var("TURBO_LEAN_JOBS", v),
            None => std::env::remove_var("TURBO_LEAN_JOBS"),
        }
        let _ = fs::remove_dir_all(&tmp_dir);
        if let Err(p) = res {
            std::panic::resume_unwind(p);
        }
    }

    #[test]
    fn test_audit_and_replay_bind_immutable_closure_snapshot_against_live_olean_swap() {
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_audit_closure_swap_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let proj = tmp_dir.join("proj");
        fs::create_dir_all(proj.join("Sw")).unwrap();
        fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"sw_pkg\"\ndefaultTargets = [\"Sw\"]\n[[lean_lib]]\nname = \"Sw\"\nroots = [\"Sw.Base\", \"Sw.Leaf\"]\n",
        )
        .unwrap();
        fs::write(
            proj.join("Sw/Base.lean"),
            "theorem t_base : True := trivial\n",
        )
        .unwrap();
        fs::write(
            proj.join("Sw/Leaf.lean"),
            "import Sw.Base\ntheorem t_leaf : True := t_base\n",
        )
        .unwrap();
        let Ok(cfg) = crate::module_builder::resolve_project_config(&proj) else {
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        };
        let env = build_auditor_bootstrap_env(&cfg);
        let ld = env.get("LD_LIBRARY_PATH").cloned().unwrap_or_default();
        let olean_dir = proj.join(".lake/build/lib/lean/Sw");
        fs::create_dir_all(&olean_dir).unwrap();
        let compile_mod = |src: &str, out_path: &Path, lp: &str| {
            let out = Command::new(&cfg.lean_bin)
                .current_dir(&proj)
                .arg("-R")
                .arg(&proj)
                .arg("-o")
                .arg(out_path)
                .arg(proj.join(src))
                .env("LEAN_PATH", lp)
                .env("LD_LIBRARY_PATH", &ld)
                .output()
                .unwrap();
            assert!(out.status.success(), "lean compile {src} failed: {:?}", out);
        };
        let base_olean = olean_dir.join("Base.olean");
        let leaf_olean = olean_dir.join("Leaf.olean");
        compile_mod(
            "Sw/Base.lean",
            &base_olean,
            &cfg.toolchain_lib_lean.to_string_lossy(),
        );
        let (lean_path_env, _) = crate::module_builder::build_lean_search_path(&cfg, true);
        compile_mod("Sw/Leaf.lean", &leaf_olean, &lean_path_env);
        let clean_leaf_bytes = fs::read(&leaf_olean).unwrap();

        let bad_leaf_src = tmp_dir.join("BadLeaf.lean");
        fs::write(
            proj.join("Sw/Leaf.lean"),
            "import Sw.Base\ntheorem t_leaf : 1 = 2 := sorry\n",
        )
        .unwrap();
        let sorry_leaf_olean = tmp_dir.join("SorryLeaf.olean");
        compile_mod("Sw/Leaf.lean", &sorry_leaf_olean, &lean_path_env);
        let sorry_leaf_bytes = fs::read(&sorry_leaf_olean).unwrap();
        let _ = bad_leaf_src;
        fs::write(
            proj.join("Sw/Leaf.lean"),
            "import Sw.Base\ntheorem t_leaf : True := t_base\n",
        )
        .unwrap();
        fs::write(&leaf_olean, &clean_leaf_bytes).unwrap();

        // 1) Trusted multi-module `audit_compiled_modules_with_zygote`: swap live `Leaf.olean` to
        //    `sorryAx` right after pre-replay (`audit_after_replay`). Both `--skip-child-replay`
        //    audit and authority recording stay pinned to the clean snapshot, AND the entrypoint
        //    fails closed because live `Leaf.olean` diverged from the audited snapshot, while the
        //    live `sorryAx` `.olean` on disk is NOT stamped as audited in `TurboStore`.
        let store_dir = tmp_dir.join("store_audit");
        let store = TurboStore::open(Some(&store_dir)).unwrap();
        let swap_path = leaf_olean.clone();
        let bad_bytes = sorry_leaf_bytes.clone();
        digest_test_hooks::set("audit_after_replay", move || {
            fs::write(&swap_path, &bad_bytes).unwrap();
        });
        let mods = vec!["Sw.Base".to_string(), "Sw.Leaf".to_string()];
        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let err =
                audit_compiled_modules_with_zygote(&store, &cfg, &mods, &lean_path_env, &[], false)
                    .expect_err("live `.olean` swap during audit must fail closed for callers");
            assert!(
                err.to_string().contains("fail-closed"),
                "expected fail-closed live-divergence error, got: {err:#}"
            );
            let mut lookup_bad =
                crate::module_builder::ReplayLookupBatchCache::new(&store, &cfg, &lean_path_env);
            assert!(
                !lookup_bad.is_audited_in_store(&store, &cfg, &lean_path_env, "Sw.Leaf", &leaf_olean),
                "post-replay swapped `sorryAx` Leaf.olean on disk must NOT inherit audited authority!"
            );
            fs::write(&leaf_olean, &clean_leaf_bytes).unwrap();
            let mut lookup_clean =
                crate::module_builder::ReplayLookupBatchCache::new(&store, &cfg, &lean_path_env);
            assert!(
                lookup_clean.is_audited_in_store(
                    &store,
                    &cfg,
                    &lean_path_env,
                    "Sw.Leaf",
                    &leaf_olean
                ),
                "the exact clean snapshot Leaf.olean bytes MUST hold audited authority"
            );
        }));
        digest_test_hooks::clear();
        if let Err(p) = res {
            let _ = fs::remove_dir_all(&tmp_dir);
            std::panic::resume_unwind(p);
        }

        // 2) `replay_and_audit_modules_with_zygote`: swap live `Leaf.olean` right after closure
        //    replay (`replay_and_audit_after_replay`) and verify it fails closed and live `sorryAx`
        //    gets zero authority.
        fs::write(&leaf_olean, &clean_leaf_bytes).unwrap();
        let store2 = TurboStore::open(Some(&tmp_dir.join("store_unified"))).unwrap();
        let swap_path2 = leaf_olean.clone();
        let bad_bytes2 = sorry_leaf_bytes.clone();
        digest_test_hooks::set("replay_and_audit_after_replay", move || {
            fs::write(&swap_path2, &bad_bytes2).unwrap();
        });
        let res2 = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let err2 = replay_and_audit_modules_with_zygote(
                &store2,
                &cfg,
                &["Sw.Leaf".to_string()],
                &["Sw.Base".to_string()],
                &lean_path_env,
                None,
            )
            .expect_err("live `.olean` swap during unified replay_and_audit must fail closed");
            assert!(
                err2.to_string().contains("fail-closed"),
                "expected fail-closed live-divergence error, got: {err2:#}"
            );
            let mut lookup_bad =
                crate::module_builder::ReplayLookupBatchCache::new(&store2, &cfg, &lean_path_env);
            assert!(
                !lookup_bad.is_audited_in_store(
                    &store2,
                    &cfg,
                    &lean_path_env,
                    "Sw.Leaf",
                    &leaf_olean
                ),
                "unified replay_and_audit must NOT record authority for post-replay swapped Leaf.olean"
            );
            assert!(
                !lookup_bad.is_replayed_in_store(&store2, &cfg, &lean_path_env, &leaf_olean),
                "unified replay_and_audit must NOT record replay authority for post-replay swapped Leaf.olean"
            );
        }));
        digest_test_hooks::clear();
        let _ = fs::remove_dir_all(&tmp_dir);
        if let Err(p) = res2 {
            std::panic::resume_unwind(p);
        }
    }

    #[cfg(unix)]
    #[test]
    fn test_audit_compiled_modules_ancestor_aba_swap_fails_closed_without_poisoning_store() {
        use std::os::unix::fs::PermissionsExt;

        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        struct ResetCacheBase;
        impl Drop for ResetCacheBase {
            fn drop(&mut self) {
                TEST_CLOSURE_SNAPSHOT_CACHE_BASE.with(|c| *c.borrow_mut() = None);
                digest_test_hooks::clear();
            }
        }
        let _reset = ResetCacheBase;

        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_audit_anc_aba_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let cache_base = tmp_dir.join("cache_base/turbo-lean-cache");
        TEST_CLOSURE_SNAPSHOT_CACHE_BASE.with(|c| *c.borrow_mut() = Some(cache_base.clone()));
        let snap_root = ensure_private_dir(&closure_snapshot_root()).unwrap();

        let proj = tmp_dir.join("proj");
        fs::create_dir_all(proj.join("Sw")).unwrap();
        fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"sw_anc\"\ndefaultTargets = [\"Sw\"]\n[[lean_lib]]\nname = \"Sw\"\nroots = [\"Sw.Base\", \"Sw.Leaf\"]\n",
        )
        .unwrap();
        fs::write(
            proj.join("Sw/Base.lean"),
            "theorem t_base : True := trivial\n",
        )
        .unwrap();
        fs::write(
            proj.join("Sw/Leaf.lean"),
            "import Sw.Base\ntheorem t_leaf : True := t_base\n",
        )
        .unwrap();
        let Ok(cfg) = crate::module_builder::resolve_project_config(&proj) else {
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        };
        let env = build_auditor_bootstrap_env(&cfg);
        let ld = env.get("LD_LIBRARY_PATH").cloned().unwrap_or_default();
        let olean_dir = proj.join(".lake/build/lib/lean/Sw");
        fs::create_dir_all(&olean_dir).unwrap();
        let compile_mod = |src: &str, out_path: &Path, lp: &str| {
            let out = Command::new(&cfg.lean_bin)
                .current_dir(&proj)
                .arg("-R")
                .arg(&proj)
                .arg("-o")
                .arg(out_path)
                .arg(proj.join(src))
                .env("LEAN_PATH", lp)
                .env("LD_LIBRARY_PATH", &ld)
                .output()
                .unwrap();
            assert!(out.status.success(), "lean compile {src} failed: {:?}", out);
        };
        let base_olean = olean_dir.join("Base.olean");
        let leaf_olean = olean_dir.join("Leaf.olean");
        compile_mod(
            "Sw/Base.lean",
            &base_olean,
            &cfg.toolchain_lib_lean.to_string_lossy(),
        );
        let (lean_path_env, _) = crate::module_builder::build_lean_search_path(&cfg, true);
        compile_mod("Sw/Leaf.lean", &leaf_olean, &lean_path_env);

        fs::write(
            proj.join("Sw/Leaf.lean"),
            "import Sw.Base\ntheorem t_leaf : 1 = 2 := sorry\n",
        )
        .unwrap();
        let sorry_leaf = tmp_dir.join("SorryLeaf.olean");
        compile_mod("Sw/Leaf.lean", &sorry_leaf, &lean_path_env);
        let sorry_bytes = fs::read(&sorry_leaf).unwrap();
        fs::write(
            proj.join("Sw/Leaf.lean"),
            "import Sw.Base\ntheorem t_leaf : True := t_base\n",
        )
        .unwrap();

        let mods = vec!["Sw.Base".to_string(), "Sw.Leaf".to_string()];
        let pre_snap = materialize_bound_audit_closure(&cfg, &mods, &lean_path_env).unwrap();
        let label = pre_snap.materialized.as_ref().unwrap().label.clone();
        drop(pre_snap);

        let saved_root = cache_base.join("closure-snapshots.saved");
        let fake_root = cache_base.join("closure-snapshots.fake");
        let fake_sw = fake_root.join(&label).join("Sw");
        fs::create_dir_all(&fake_sw).unwrap();
        fs::write(fake_sw.join("Base.olean"), fs::read(&base_olean).unwrap()).unwrap();
        fs::write(fake_sw.join("Leaf.olean"), &sorry_bytes).unwrap();
        for p in [fake_sw.join("Base.olean"), fake_sw.join("Leaf.olean")] {
            let mut perms = fs::metadata(&p).unwrap().permissions();
            perms.set_readonly(true);
            fs::set_permissions(&p, perms).unwrap();
        }
        fs::set_permissions(&fake_sw, fs::Permissions::from_mode(0o500)).unwrap();
        fs::set_permissions(fake_root.join(&label), fs::Permissions::from_mode(0o500)).unwrap();

        let store = TurboStore::open(Some(&tmp_dir.join("store"))).unwrap();
        let (sr1, sv1, fk1) = (snap_root.clone(), saved_root.clone(), fake_root.clone());
        digest_test_hooks::set("audit_before_replay", move || {
            if sr1.is_dir() && fk1.is_dir() {
                fs::rename(&sr1, &sv1).unwrap();
                fs::rename(&fk1, &sr1).unwrap();
                fs::rename(&sr1, &fk1).unwrap();
                fs::rename(&sv1, &sr1).unwrap();
            }
        });
        let run = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let err =
                audit_compiled_modules_with_zygote(&store, &cfg, &mods, &lean_path_env, &[], false)
                    .expect_err("ancestor directory ABA swap before audit replay must fail closed");
            assert!(
                err.to_string().contains("fail-closed"),
                "expected fail-closed error on ancestor ABA swap, got: {err:#}"
            );
            fs::write(&leaf_olean, &sorry_bytes).unwrap();
            let mut lookup_bad =
                crate::module_builder::ReplayLookupBatchCache::new(&store, &cfg, &lean_path_env);
            assert!(
                !lookup_bad.is_audited_in_store(
                    &store,
                    &cfg,
                    &lean_path_env,
                    "Sw.Leaf",
                    &leaf_olean
                ),
                "sorryAx Leaf.olean must never hold audited authority after ancestor ABA swap"
            );
        }));
        digest_test_hooks::clear();
        purge_snapshot_dir(&fake_root);
        purge_snapshot_dir(&saved_root);
        purge_snapshot_dir(&snap_root);
        let _ = fs::remove_dir_all(&tmp_dir);
        if let Err(p) = run {
            std::panic::resume_unwind(p);
        }
    }

    #[cfg(unix)]
    #[test]
    fn test_cold_turbo_lean_home_audit_does_not_self_invalidate_snapshot_binding() {
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_cold_home_audit_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let cold_home = tmp_dir.join("cold_turbo_lean_home");
        let prev_home = std::env::var_os("TURBO_LEAN_HOME");
        std::env::set_var("TURBO_LEAN_HOME", &cold_home);
        let restore_home = |prev: Option<std::ffi::OsString>| match prev {
            Some(v) => std::env::set_var("TURBO_LEAN_HOME", v),
            None => std::env::remove_var("TURBO_LEAN_HOME"),
        };

        let proj = tmp_dir.join("proj");
        fs::create_dir_all(proj.join("Cold")).unwrap();
        fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"cold_pkg\"\ndefaultTargets = [\"Cold\"]\n[[lean_lib]]\nname = \"Cold\"\nroots = [\"Cold.A\"]\n",
        )
        .unwrap();
        fs::write(
            proj.join("Cold/A.lean"),
            "theorem cold_ok : True := trivial\n",
        )
        .unwrap();
        let Ok(cfg) = crate::module_builder::resolve_project_config(&proj) else {
            restore_home(prev_home);
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        };
        let env = build_auditor_bootstrap_env(&cfg);
        let ld = env.get("LD_LIBRARY_PATH").cloned().unwrap_or_default();
        let (lean_path_env, _) = crate::module_builder::build_lean_search_path(&cfg, false);
        let out_dir = proj.join(".lake/build/lib/lean/Cold");
        fs::create_dir_all(&out_dir).unwrap();
        let a_olean = out_dir.join("A.olean");
        let st = std::process::Command::new(&cfg.lean_bin)
            .current_dir(&proj)
            .env("LEAN_PATH", &lean_path_env)
            .env("LD_LIBRARY_PATH", &ld)
            .args(["-R", "."])
            .arg(proj.join("Cold/A.lean"))
            .arg("-o")
            .arg(&a_olean)
            .status()
            .expect("invoke lean for Cold.A");
        assert!(st.success(), "compiling Cold.A must succeed");

        let run = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let store = TurboStore::open(None).unwrap();
            assert_eq!(store.root, cold_home);
            assert!(!cold_home.join("fastcheck_bins").exists());
            assert!(!cold_home.join(".verifier_replay_hmac_key").exists());
            let mods = vec!["Cold.A".to_string()];
            audit_compiled_modules_with_zygote(&store, &cfg, &mods, &lean_path_env, &[], false)
                .expect("cold TURBO_LEAN_HOME audit must not self-invalidate snapshot binding");
            assert!(cold_home.join("fastcheck_bins").is_dir());
            assert!(cold_home.join(".verifier_replay_hmac_key").is_file());
            assert!(cold_home.join("closure-realm/closure-snapshots").is_dir());
            let mut lookup =
                crate::module_builder::ReplayLookupBatchCache::new(&store, &cfg, &lean_path_env);
            assert!(
                lookup.is_audited_in_store(&store, &cfg, &lean_path_env, "Cold.A", &a_olean),
                "Cold.A must hold audited authority in cold TURBO_LEAN_HOME store"
            );
        }));
        restore_home(prev_home);
        purge_snapshot_dir(&cold_home.join("closure-realm/closure-snapshots"));
        let _ = fs::remove_dir_all(&tmp_dir);
        if let Err(p) = run {
            std::panic::resume_unwind(p);
        }
    }

    #[test]
    fn test_overlapping_snapshots_sharing_dep_do_not_invalidate_binding() {
        let Some((tmp_dir, _store, env_vars, lean_bin)) = open_test_zygote_env("overlap_snap")
        else {
            return;
        };
        let lib = tmp_dir.join("lib");
        fs::create_dir_all(&lib).unwrap();
        let dep = compile_test_olean(&lean_bin, &lib, "SharedDep", "def sharedVal : Nat := 7\n");
        fs::write(lib.join("SharedDep.olean"), &dep).unwrap();
        let a = compile_test_olean(
            &lean_bin,
            &lib,
            "LeafA",
            "import SharedDep\ndef valA : Nat := sharedVal + 1\n",
        );
        fs::write(lib.join("LeafA.olean"), &a).unwrap();
        let b = compile_test_olean(
            &lean_bin,
            &lib,
            "LeafB",
            "import SharedDep\ndef valB : Nat := sharedVal + 2\n",
        );
        fs::write(lib.join("LeafB.olean"), &b).unwrap();
        let lp = lib.to_string_lossy().into_owned();
        let ctx_a = resolve_zygote_context(
            "leanprover/lean4:v4.35.0",
            &lp,
            &env_vars,
            &lean_bin,
            "LeafA",
        );
        assert_eq!(ctx_a.closure.binding(), ClosureBinding::Bound);
        // Wait so a shared-inode ctime bump would strictly differ from ctx_a's recorded FileSig.
        std::thread::sleep(std::time::Duration::from_millis(20));
        let ctx_b = resolve_zygote_context(
            "leanprover/lean4:v4.35.0",
            &lp,
            &env_vars,
            &lean_bin,
            "LeafB",
        );
        assert_eq!(ctx_b.closure.binding(), ClosureBinding::Bound);
        assert_eq!(
            ctx_a.closure.binding(),
            ClosureBinding::Bound,
            "materializing a sibling snapshot sharing SharedDep.olean must not invalidate ctx_a"
        );
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    #[cfg(target_os = "linux")]
    fn test_zygote_master_eviction_preserves_checked_out_clone() {
        let (dir, store, mut env, lean) = open_test_zygote_env("master_eviction").expect("Lean toolchain");
        fs::write(dir.join("EvictionSeed.olean"), compile_test_olean(&lean, &dir,
            "EvictionSeed", "def evictionSeed : Nat := 7\n")).unwrap();
        env.insert("LEAN_PATH".into(), dir.to_string_lossy().into_owned());
        let pid = std::rc::Rc::new(std::cell::Cell::new(0));
        let seen = pid.clone();
        digest_test_hooks::set("cloned_worker_request", move || {
            let mut masters = ZYGOTE_MASTERS.get().unwrap().lock().unwrap();
            let key = masters.iter().find(|(_, e)| e.worker.lock().unwrap()
                .warm_imports.contains_key("EvictionSeed")).unwrap().0.clone();
            let entry = masters.remove(&key).unwrap();
            seen.set(entry.pid);
            let registry: Vec<ZygoteLruEntry> = serde_json::from_slice(&fs::read(
                crate::shm_cache::staging_shm_dir().join("zygote_lru_registry.json")).unwrap()).unwrap();
            assert!(registry.iter().any(|e| e.pid == entry.pid && e.rss_mb > 0));
            drop(masters);
            drop(entry);
            assert!(Path::new(&format!("/proc/{}", seen.get())).exists());
        });
        let reply = eval_with_zygote_pool_for_targets(&store, "leanprover/lean4:v4.35.0",
            &env["LEAN_PATH"], &env, &lean,
            "import EvictionSeed\ntheorem eviction_ok : evictionSeed = 7 := rfl\n",
            &["eviction_ok".into()], None, &[]).unwrap();
        digest_test_hooks::clear();
        assert!(reply.ok, "{:?}", reply.errors);
        assert_ne!(pid.get(), 0, "must evaluate a checked-out clone");
        let mut retired = Vec::new();
        let mut pool = ZYGOTE_POOL.get().unwrap().lock().unwrap();
        for workers in pool.values_mut() {
            let mut i = 0;
            while i < workers.len() {
                if workers[i]._master.as_ref().is_some_and(|e| e.pid == pid.get()) {
                    retired.push(workers.swap_remove(i));
                } else { i += 1; }
            }
        }
        drop(pool);
        assert!(Path::new(&format!("/proc/{}", pid.get())).exists());
        drop(retired);
        assert!(!Path::new(&format!("/proc/{}", pid.get())).exists(), "last clone must reap master");
        let _ = fs::remove_dir_all(dir);
    }

    #[test]
    #[cfg(target_os = "linux")]
    fn test_zygote_master_rss_cap() {
        if std::env::var_os("TURBO_LEAN_TEST_MASTER_RSS_CHILD").is_none() {
            let staging = std::env::temp_dir().join(format!("turbo-master-rss-staging-{}", std::process::id()));
            let output = Command::new(std::env::current_exe().unwrap())
                .args(["--exact", "zygote::tests::test_zygote_master_rss_cap", "--nocapture"])
                .env("TURBO_LEAN_TEST_MASTER_RSS_CHILD", "1")
                .env("TURBO_LEAN_WORKER_RSS_LIMIT_MB", "1")
                .env("TURBO_LEAN_STAGING_DIR", &staging)
                .output().unwrap();
            let _ = fs::remove_dir_all(staging);
            assert!(output.status.success(), "{}\n{}", String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr));
            return;
        }
        let (dir, store, mut env, lean) = open_test_zygote_env("master_rss_cap").expect("Lean toolchain");
        crate::shm_cache::ensure_verified_private_staging_dir(None).expect("private staging");
        fs::write(dir.join("RssSeed.olean"), compile_test_olean(&lean, &dir,
            "RssSeed", "def rssSeed : Nat := 7\n")).unwrap();
        env.insert("LEAN_PATH".into(), dir.to_string_lossy().into_owned());
        let reply = eval_with_zygote_pool_for_targets(&store, "leanprover/lean4:v4.35.0",
            &env["LEAN_PATH"], &env, &lean,
            "import RssSeed\ntheorem rss_ok : rssSeed = 7 := rfl\n",
            &["rss_ok".into()], None, &[]).unwrap();
        assert!(reply.ok, "{:?}", reply.errors);
        assert!(ZYGOTE_MASTERS.get().unwrap().lock().unwrap().is_empty(), "oversized master must not be pinned");
        use std::os::unix::fs::PermissionsExt;
        assert_eq!(fs::metadata(crate::shm_cache::staging_shm_dir()).unwrap()
            .permissions().mode() & 0o777, 0o700);
        let _ = fs::remove_dir_all(dir);
    }

    #[test]
    fn test_zygote_cow_fork_concurrent_pool_miss() {
        if std::env::var_os("TURBO_LEAN_TEST_POOL_TEARDOWN").is_none() {
            let output = Command::new(std::env::current_exe().unwrap())
                .args(["--exact", "zygote::tests::test_zygote_cow_fork_concurrent_pool_miss"])
                .env("TURBO_LEAN_TEST_POOL_TEARDOWN", "1").output().unwrap();
            assert!(output.status.success(), "{}\n{}", String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr));
            return;
        }
        let (dir, _store, mut env, lean) = open_test_zygote_env("clone_pool").expect("Lean toolchain");
        fs::write(dir.join("ClonePool.olean"), compile_test_olean(&lean, &dir, "ClonePool", "def cloneSeed : Nat := 7\n")).unwrap();
        env.insert("LEAN_PATH".into(), dir.to_string_lossy().into_owned());
        eval_with_zygote_pool_for_targets(&_store, "leanprover/lean4:v4.35.0", &dir.to_string_lossy(), &env, &lean, "import ClonePool\ntheorem clone_warm : True := trivial\n", &["clone_warm".into()], None, &[]).unwrap();
        std::thread::scope(|s| {
            let handles: Vec<_> = (0..4).map(|i| {
                let (env, lean) = (&env, &lean);
                s.spawn(move || {
                    let (_dir, store, _, _) = open_test_zygote_env(&format!("clone_thread_{i}")).unwrap();
                    let cloned = std::rc::Rc::new(std::cell::Cell::new(false));
                    let seen = cloned.clone();
                    digest_test_hooks::set("cloned_worker_request", move || seen.set(true));
                    let code = format!("import ClonePool\ntheorem clone_pool_{i} : cloneSeed = 7 := rfl\n");
                    let r = eval_with_zygote_pool_for_targets(&store, "leanprover/lean4:v4.35.0", &env["LEAN_PATH"], env, lean, &code, &[format!("clone_pool_{i}")], None, &[]).unwrap();
                    assert!(r.ok && r.kernel_gate_active, "{:?}", r.errors);
                    assert!(r.env_cache_hit, "clone must inherit the imported environment");
                    assert_eq!(r.import_us, 0);
                    assert!(cloned.get(), "request must execute in a fork clone");
                    let bad = code.replace("rfl", "by sorry");
                    assert!(!eval_with_zygote_pool_for_targets(&store, "leanprover/lean4:v4.35.0", &env["LEAN_PATH"], env, lean, &bad, &[format!("clone_pool_{i}")], None, &[]).unwrap().ok);
                    digest_test_hooks::clear();
                })
            }).collect();
            for h in handles { h.join().unwrap(); }
        });
        #[cfg(target_os = "linux")]
        {
            let masters = ZYGOTE_MASTERS.get().unwrap().lock().unwrap();
            assert!(!masters.is_empty(), "test must exercise a live master");
            let mut pids: Vec<_> = masters.values().map(|w| w.pid).collect();
            drop(masters);
            pids.extend(ZYGOTE_POOL.get().unwrap().lock().unwrap().values()
                .flatten().map(|w| w.pid()));
            clear_zygote_pool();
            assert!(ZYGOTE_MASTERS.get().unwrap().lock().unwrap().is_empty());
            assert!(ZYGOTE_POOL.get().unwrap().lock().unwrap().is_empty());
            for pid in pids {
                assert!(!Path::new(&format!("/proc/{pid}")).exists(), "worker {pid} must be killed and reaped");
            }
        }
        let _ = fs::remove_dir_all(dir);
    }

    #[test]
    fn test_zygote_cow_fork_race_candidates_and_sorry_rejection() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("cow_fork_race")
        else {
            return;
        };
        let prefix = "import Init\ndef seedVal : Nat := 20\ndef baseVal : Nat := seedVal + 1\n";
        let cands_ok = vec![
            "theorem race_t : baseVal + baseVal = 42 := by exact False.elim sorry".to_string(),
            "theorem race_t : baseVal + baseVal = 999 := by rfl".to_string(),
            "theorem race_t : baseVal + baseVal = 42 := by rfl".to_string(),
        ];
        let rep = eval_candidates_race_via_zygote(
            &store,
            "leanprover/lean4:v4.35.0",
            "",
            &env_vars,
            &lean_bin,
            prefix,
            &cands_ok,
            &[],
        )
        .expect("race_candidates IPC must succeed");
        assert!(
            rep.ok && rep.import_ok && rep.kernel_gate_active,
            "expected valid candidate to win race: {:?}",
            (rep.errors.clone(), rep.stderr_tail.clone())
        );
        assert_eq!(rep.winning_candidate_idx, Some(2));
        assert!(rep.compact_prefix, "prefix compaction must succeed at runtime: {rep:?}");
        assert!(!rep.used_sorry && rep.sorry_decls.is_empty());

        for prefix in [
            "import Init\nprivate def hiddenSeed : Nat := 21\n",
            "import Init\n@[simp] theorem prefix_simp : True := trivial\n",
            "import Init\nlocal instance : Inhabited Nat := ⟨21⟩\n",
            "import Init\nnamespace ScopedPrefix\nscoped instance : Inhabited Nat := ⟨21⟩\nend ScopedPrefix\n",
            "import Init\nnoncomputable def opaqueSeed : Nat := 21\n",
            "import Init\nnamespace StillOpen\ndef seed : Nat := 21\n",
            "import Init\nopen Nat\ndef seed : Nat := 21\n",
        ] {
            let rep = eval_candidates_race_via_zygote(
                &store, "leanprover/lean4:v4.35.0", "", &env_vars, &lean_bin,
                prefix, &["theorem scoped_body : True := trivial\n".into()], &[],
            ).unwrap();
            assert!(rep.ok, "checkpoint replay failed for {prefix}: {rep:?}");
            assert!(!rep.compact_prefix, "scoped/modifier prefix must retain its checkpoint: {prefix}");
        }

        let cands_sorry_only = vec!["theorem race_bad : baseVal = 999 := by sorry".to_string()];
        let rep_bad = eval_candidates_race_via_zygote(
            &store,
            "leanprover/lean4:v4.35.0",
            "",
            &env_vars,
            &lean_bin,
            prefix,
            &cands_sorry_only,
            &[],
        )
        .expect("race_candidates sorry-only IPC must return structured reply");
        assert!(
            !rep_bad.ok,
            "sorry-backed candidate must be rejected fail-closed by kernel gate"
        );

        let mut fork_env = env_vars.clone();
        fork_env.insert("TURBO_LEAN_ZYGOTE_FORK_SHARDS".to_string(), "1".to_string());
        let fork_rep = eval_with_zygote_pool_for_targets(
            &store,
            "leanprover/lean4:v4.35.0",
            "",
            &fork_env,
            &lean_bin,
            "import Init\ntheorem forked_ok : 2 + 2 = 4 := rfl\n",
            &["forked_ok".to_string()],
            None,
            &[],
        )
        .expect("forked shard check must succeed");
        assert!(fork_rep.ok && fork_rep.import_ok && !fork_rep.used_sorry);

        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_cross_worktree_closure_pool_dedup() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("xwt_dedup") else {
            return;
        };
        let wt1 = tmp_dir.join("worktree_alpha/.lake/packages/dep/build/lib/lean");
        let wt2 = tmp_dir.join("worktree_beta/.lake/packages/dep/build/lib/lean");
        fs::create_dir_all(&wt1).unwrap();
        fs::create_dir_all(&wt2).unwrap();
        let dep_bytes =
            compile_test_olean(&lean_bin, &wt1, "XwtShared", "def xwtConst : Nat := 108\n");
        fs::write(wt1.join("XwtShared.olean"), &dep_bytes).unwrap();
        std::thread::sleep(std::time::Duration::from_millis(15));
        fs::write(wt2.join("XwtShared.olean"), &dep_bytes).unwrap();

        let lp1 = wt1.to_string_lossy().into_owned();
        let lp2 = wt2.to_string_lossy().into_owned();
        let mut ev1 = env_vars.clone();
        ev1.insert("LEAN_PATH".to_string(), lp1.clone());
        let mut ev2 = env_vars.clone();
        ev2.insert("LEAN_PATH".to_string(), lp2.clone());

        let ctx1 = resolve_zygote_context(
            "leanprover/lean4:v4.35.0",
            &lp1,
            &ev1,
            &lean_bin,
            "XwtShared",
        );
        let ctx2 = resolve_zygote_context(
            "leanprover/lean4:v4.35.0",
            &lp2,
            &ev2,
            &lean_bin,
            "XwtShared",
        );
        assert_ne!(ctx1.lean_path, ctx2.lean_path);
        assert_eq!(ctx1.host_closure_digest, ctx2.host_closure_digest);
        assert_eq!(ctx1.closure_pool_digest, ctx2.closure_pool_digest);

        let r1 = eval_with_zygote_pool_for_targets(
            &store,
            "leanprover/lean4:v4.35.0",
            &lp1,
            &ev1,
            &lean_bin,
            "import XwtShared\ntheorem t_wt1 : xwtConst = 108 := rfl\n",
            &["t_wt1".to_string()],
            None,
            &[],
        )
        .unwrap();
        assert!(r1.ok && r1.import_ok);

        let r2 = eval_with_zygote_pool_for_targets(
            &store,
            "leanprover/lean4:v4.35.0",
            &lp2,
            &ev2,
            &lean_bin,
            "import XwtShared\ntheorem t_wt2 : xwtConst + 1 = 109 := rfl\n",
            &["t_wt2".to_string()],
            None,
            &[],
        )
        .unwrap();
        assert!(r2.ok && r2.import_ok);
        assert!(
            r2.env_cache_hit,
            "second worktree with identical .olean closure must hit warm Zygote worker pool"
        );

        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_turbo_outline_prefix_module_never_exempts_unlisted_sorry() {
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_outline_evil_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        fs::create_dir_all(&tmp_dir).unwrap();
        fs::write(tmp_dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            tmp_dir.join("lakefile.toml"),
            "name = \"evil_pkg\"\ndefaultTargets = [\"_TurboOutline_evil\"]\n[[lean_lib]]\nname = \"_TurboOutline_evil\"\nroots = [\"_TurboOutline_evil\"]\n",
        )
        .unwrap();
        fs::write(
            tmp_dir.join("_TurboOutline_evil.lean"),
            "theorem bad : False := sorry\n",
        )
        .unwrap();
        let Ok(cfg) = crate::module_builder::resolve_project_config(&tmp_dir) else {
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        };
        let env = build_auditor_bootstrap_env(&cfg);
        let ld = env.get("LD_LIBRARY_PATH").cloned().unwrap_or_default();
        let olean_dir = tmp_dir.join(".lake/build/lib/lean");
        fs::create_dir_all(&olean_dir).unwrap();
        let out = Command::new(&cfg.lean_bin)
            .current_dir(&tmp_dir)
            .arg("-R")
            .arg(&tmp_dir)
            .arg("-o")
            .arg(olean_dir.join("_TurboOutline_evil.olean"))
            .arg(tmp_dir.join("_TurboOutline_evil.lean"))
            .env("LEAN_PATH", &cfg.toolchain_lib_lean)
            .env("LD_LIBRARY_PATH", &ld)
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "compiling _TurboOutline_evil.lean failed: {:?}",
            out
        );

        let store = TurboStore::open(Some(&tmp_dir.join("store"))).unwrap();
        let (lean_path_env, _) = crate::module_builder::build_lean_search_path(&cfg, true);

        let audit_res = audit_compiled_modules_with_zygote(
            &store,
            &cfg,
            &["_TurboOutline_evil".to_string()],
            &lean_path_env,
            &[],
            false,
        );
        assert!(
            audit_res.is_err(),
            "audit_compiled_modules_with_zygote must reject sorry in _TurboOutline_evil"
        );
        let audit_err = audit_res.unwrap_err().to_string();
        assert!(
            audit_err.contains("sorryAx"),
            "expected sorryAx violation on _TurboOutline_evil, got: {audit_err}"
        );

        let mut eval_env = env.clone();
        eval_env.insert("LEAN_PATH".to_string(), lean_path_env.clone());
        let rep = eval_with_zygote_pool_for_targets(
            &store,
            &cfg.toolchain,
            &lean_path_env,
            &eval_env,
            &cfg.lean_bin,
            "import _TurboOutline_evil\ntheorem pwn : False := bad\n",
            &["pwn".to_string()],
            None,
            &[],
        )
        .expect("eval_with_zygote_pool_for_targets IPC must return structured reply");
        assert!(
            !rep.ok,
            "theorem importing _TurboOutline_evil without extra_stubs must fail closed: {:?}",
            rep
        );
        assert!(
            rep.errors.iter().any(|e| e.contains("sorryAx")),
            "expected sorryAx error in errors, got: {:?}",
            rep.errors
        );

        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_s2_zygote_public_api_surface_pinned() {
        let _ = std::mem::size_of::<crate::zygote::TimeoutHotspot>();
        let _ = std::mem::size_of::<crate::zygote::SimpHotspot>();
        let _ = std::mem::size_of::<crate::zygote::ZygoteEvalReply>();
        let _ = std::mem::size_of::<crate::zygote::ZygoteWorkerProcess>();
        let _ = std::mem::size_of::<crate::zygote::OleanPublicDeclSig>();
        let _ = std::mem::size_of::<crate::zygote::OleanPublicSignatureReply>();
        let _ = std::mem::size_of::<crate::zygote::OneShotGuard>();
        let _ = std::mem::size_of::<crate::zygote::ExclusiveLifecycleLock>();
        let _ = std::mem::size_of::<crate::zygote::OleanFileStatSig>();
        let _ = std::mem::size_of::<crate::zygote::OleanEntryDigest>();
        let _ = std::mem::size_of::<crate::zygote::ClosureSnapshot>();
        let _ = std::mem::size_of::<crate::zygote::MaterializedClosure>();
        let _ = std::mem::size_of::<crate::zygote::ClosureBinding>();
        let _ = std::mem::size_of::<crate::zygote::ZygoteAuditModulesReply>();
        let _ = std::mem::size_of::<crate::zygote::PinnedFfiPackage>();
        let _ = std::mem::size_of::<crate::zygote::AuditedShardReport>();
        let _ = std::mem::size_of::<crate::zygote::ResolvedZygoteContext>();
        let _ = std::mem::size_of::<crate::zygote::LocalZygoteDaemonInfo>();
        let _ = std::mem::size_of::<crate::zygote::McpTimeoutGuard>();
        let _ = std::mem::size_of::<crate::zygote::LocalPayload>();
        let _ = std::mem::size_of::<crate::zygote::BoundedLine>();
        let _ = std::mem::size_of::<crate::zygote::ZygoteImportUnavailable>();

        assert_eq!(crate::zygote::ZYGOTE_SCANNER_VERSION, 5);
        assert_eq!(crate::zygote::ZYGOTE_REPLAY_VERSION, 3);
        assert!(crate::zygote::verifier_provenance_ok(5, 3));
        assert!(!crate::zygote::PINNED_FFI_PACKAGES.is_empty());
        assert_eq!(crate::zygote::REQUEST_POLICY_KEYS.len(), 4);
        assert_eq!(crate::zygote::MCP_RUNTIME_POLICY_KEYS.len(), 5);
        assert_eq!(crate::zygote::MAX_WIRE_LINE_BYTES, 16 * 1024);
        assert_eq!(crate::zygote::IMPORT_UNAVAILABLE_CODE, "zygote_import_unavailable");

        let _ = crate::zygote::query_lean_native_core_worker as fn(&str, Option<&str>) -> Result<serde_json::Value>;
        let _ = crate::zygote::measure_process_rss_mb as fn(u32) -> u64;
        let _ = crate::zygote::govern_machine_wide_zygote_rss as fn(u32, u64);
        let _ = crate::zygote::reap_zygote_workers_and_daemons as fn(Option<&Path>) -> usize;
        let _ = crate::zygote::compute_imported_oleans_digest as fn(&str, &str) -> String;
        let _ = crate::zygote::compute_search_path_oleans_digest as fn(&str) -> String;
        let _ = crate::zygote::split_body_into_prefix_and_decl as fn(&str) -> Option<(String, String, String)>;
        let _ = crate::zygote::split_eval_body_into_prefix_and_cmds as fn(&str) -> Option<(String, String, String)>;
        let _ = crate::zygote::parse_zygote_import_entry as fn(&str) -> Option<(String, bool, bool, bool)>;
        let _ = crate::zygote::split_shard_for_zygote as fn(&str) -> (String, String);
        let _ = crate::zygote::reply_indicates_timeout_or_heartbeat as fn(&ZygoteEvalReply) -> bool;
        let _ = crate::zygote::text_indicates_timeout_or_heartbeat as fn(&str) -> bool;
        let _ = crate::zygote::ensure_local_zygote_daemon
            as fn(&TurboStore, &std::collections::HashMap<String, String>) -> Option<String>;
        let _ = crate::zygote::warm_local_zygote_daemon_nonblocking
            as fn(&TurboStore, &std::collections::HashMap<String, String>);
    }
}
