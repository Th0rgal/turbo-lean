use serde_json::{json, Value};
use std::fs;
use std::io::{Read, Write};
use std::net::TcpListener;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

// Real curl transport, including HTTP body capture. Synchronous emission lets us
// inspect all requests after the CLI exits, without timing-based negative assertions.
struct Endpoint {
    url: String,
    events: Arc<Mutex<Vec<Value>>>,
    stop: Arc<AtomicBool>,
    worker: Option<thread::JoinHandle<()>>,
}
impl Endpoint {
    fn new() -> Self {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        listener.set_nonblocking(true).unwrap();
        let url = format!("http://{}", listener.local_addr().unwrap());
        let events = Arc::new(Mutex::new(Vec::new()));
        let stop = Arc::new(AtomicBool::new(false));
        let (captured, stopping) = (events.clone(), stop.clone());
        let worker = thread::spawn(move || {
            while !stopping.load(Ordering::SeqCst) {
                match listener.accept() {
                    Ok((mut stream, _)) => {
                        stream
                            .set_read_timeout(Some(Duration::from_secs(5)))
                            .unwrap();
                        let mut bytes = Vec::new();
                        let mut buf = [0; 4096];
                        loop {
                            let n = stream.read(&mut buf).unwrap();
                            assert!(n > 0, "incomplete telemetry POST");
                            bytes.extend_from_slice(&buf[..n]);
                            if let Some(end) = bytes.windows(4).position(|w| w == b"\r\n\r\n") {
                                let header = String::from_utf8_lossy(&bytes[..end]);
                                assert!(header.starts_with("POST /v2/ns/"), "{header}");
                                let len: usize = header
                                    .lines()
                                    .find_map(|line| {
                                        let (key, val) = line.split_once(':')?;
                                        key.eq_ignore_ascii_case("content-length")
                                            .then(|| val.trim().parse().unwrap())
                                    })
                                    .expect("Content-Length");
                                if bytes.len() >= end + 4 + len {
                                    captured.lock().unwrap().push(
                                        serde_json::from_slice(&bytes[end + 4..end + 4 + len])
                                            .unwrap(),
                                    );
                                    break;
                                }
                            }
                        }
                        stream.write_all(b"HTTP/1.1 200 OK\r\nContent-Length: 2\r\nConnection: close\r\n\r\n{}").unwrap();
                    }
                    Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                        thread::sleep(Duration::from_millis(2))
                    }
                    Err(e) => panic!("telemetry listener: {e}"),
                }
            }
        });
        Self {
            url,
            events,
            stop,
            worker: Some(worker),
        }
    }
    fn take(&self) -> Vec<Value> {
        std::mem::take(&mut *self.events.lock().unwrap())
    }
}
impl Drop for Endpoint {
    fn drop(&mut self) {
        self.stop.store(true, Ordering::SeqCst);
        self.worker.take().unwrap().join().unwrap();
    }
}

struct Fixture {
    root: PathBuf,
    endpoint: Endpoint,
}
impl Fixture {
    fn new() -> Self {
        let root = std::env::temp_dir().join(format!(
            "turbo_telemetry_cli_{}_{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("lean-toolchain"),
            include_str!("../../../lean/lean-toolchain"),
        )
        .unwrap();
        fs::write(
            root.join("lakefile.toml"),
            "name = \"fixture\"\n[[lean_lib]]\nname = \"Fixture\"\n",
        )
        .unwrap();
        fs::write(
            root.join("Fixture.lean"),
            "theorem telemetry_fixture (x : Nat) : x + 0 = x := by simp\n",
        )
        .unwrap();
        let output = Command::new("lake")
            .args(["build", "Fixture"])
            .current_dir(&root)
            .env("LEAN_NUM_THREADS", "4")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "lake fixture: {}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        Self {
            root,
            endpoint: Endpoint::new(),
        }
    }
    fn command(&self, args: &[&str], env: &[(&str, &str)], input: Option<Value>) -> Value {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_turbo-lean"));
        // Isolate all ambient telemetry/governor settings, while retaining toolchain PATH.
        for (key, _) in std::env::vars_os() {
            let k = key.to_string_lossy();
            if k.contains("TELEMETRY")
                || k.starts_with("TURBO_LEAN_")
                || k == "SANDBOXED_MISSION_ID"
            {
                cmd.env_remove(key);
            }
        }
        cmd.current_dir(&self.root)
            .args(["--json", "--cache-dir"])
            .arg(self.root.join("cache"))
            .args(args)
            .env("TURBO_LEAN_USER_CONFIG", self.root.join("user.toml"))
            .env("SANDBOXED_TELEMETRY_CONFIG", self.root.join("hub.json"))
            .env("SANDBOXED_TELEMETRY_URL", &self.endpoint.url)
            .env("SANDBOXED_TELEMETRY_SYNC", "1")
            .env("SANDBOXED_TELEMETRY_TOKEN", "token-alone-is-not-consent")
            .env("SANDBOXED_TELEMETRY_TMP_DIR", self.root.join("batch"))
            .env("TURBO_LEAN_TELEMETRY_DIR", self.root.join("spool"))
            .env("TURBO_LEAN_STAGING_DIR", self.root.join("staging"))
            .env("TURBO_LEAN_NO_DAEMON", "1")
            .env("LEAN_NUM_THREADS", "4")
            .env("NO_PROXY", "127.0.0.1,localhost")
            .env("no_proxy", "127.0.0.1,localhost")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        for (k, v) in env {
            cmd.env(k, v);
        }
        if input.is_some() {
            cmd.stdin(Stdio::piped());
        }
        let mut child = cmd.spawn().unwrap();
        if let Some(request) = input {
            writeln!(child.stdin.take().unwrap(), "{request}").unwrap();
        }
        let out = child.wait_with_output().unwrap();
        assert!(
            out.status.success(),
            "{args:?}: {}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        serde_json::from_slice(&out.stdout)
            .unwrap_or_else(|e| panic!("{args:?}: {e}: {}", String::from_utf8_lossy(&out.stdout)))
    }
    fn mcp(&self, args: Value, cli: &[&str], env: &[(&str, &str)]) {
        self.mcp_at(args, cli, env, None);
    }
    fn mcp_at(&self, args: Value, cli: &[&str], env: &[(&str, &str)], workspace: Option<&str>) {
        let mut argv = cli.to_vec();
        argv.push("mcp");
        if let Some(dir) = workspace {
            argv.extend(["--project-dir", dir]);
        }
        let response = self.command(&argv, env, Some(json!({"jsonrpc":"2.0", "id":1, "method":"tools/call", "params":{"name":"turbo_audit_spec", "arguments":args}})));
        assert!(response.get("result").is_some(), "{response}");
        assert_eq!(response["result"]["isError"], false, "{response}");
    }
    fn project_policy(&self, policy: &str) {
        fs::write(
            self.root.join("turbo-lean.toml"),
            format!("[telemetry]\n{policy}\n"),
        )
        .unwrap();
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

#[test]
fn build_real_cli_remote_requires_opt_in() {
    let f = Fixture::new();
    for opt_in in [false, true] {
        f.project_policy(if opt_in { "remote = true" } else { "" });
        // First execution stages already-built outputs; second is a real CAS hit.
        for expected_status in ["built", "cache_hit"] {
            let result = f.command(&["build"], &[], None);
            if !opt_in {
                assert_eq!(result["status"], expected_status);
            }
            let events = f.endpoint.take();
            assert_eq!(!events.is_empty(), opt_in);
            for ev in events {
                assert_eq!(ev["tool_name"], "build");
            }
        }
    }
}

#[test]
fn check_and_fast_check_real_cli_do_not_emit_in_either_mode() {
    let f = Fixture::new();
    for opt_in in [false, true] {
        f.project_policy(if opt_in { "remote = true" } else { "" });
        let result = f.command(
            &[
                "check",
                "Fixture.lean",
                "--decl",
                "telemetry_fixture",
                "--jobs",
                "4",
            ],
            &[],
            None,
        );
        assert!(
            matches!(
                result["status"].as_str(),
                Some(
                    "theorem_verified"
                        | "theorem_cache_hit"
                        | "all_shards_cached"
                        | "file_verified"
                )
            ),
            "{result}"
        );
        assert!(f.endpoint.take().is_empty(), "CLI check must not emit");
        let result = f.command(
            &[
                "fast-check",
                "Fixture.lean",
                "--backend",
                "cpu",
                "--transpile-lean",
                "telemetry_fixture",
            ],
            &[],
            None,
        );
        assert_eq!(result["status"], "ok", "{result}");
        assert_eq!(result["verified"], true, "{result}");
        assert!(result["n_states"].as_u64().unwrap() > 0);
        assert!(f.endpoint.take().is_empty(), "CLI fast-check must not emit");
    }
}

#[test]
fn mcp_real_tool_remote_consent_and_workspace_precedence() {
    let f = Fixture::new();
    let args = json!({"file": f.root.join("Fixture.lean")});
    f.mcp(args.clone(), &[], &[]);
    assert!(f.endpoint.take().is_empty());
    fs::write(f.root.join("hub.json"), r#"{"opt_in":true}"#).unwrap();
    f.mcp(args.clone(), &[], &[]);
    assert!(!f.endpoint.take().is_empty(), "explicit hub opt-in");
    fs::write(f.root.join("user.toml"), "[telemetry]\nremote = false\n").unwrap();
    f.mcp(args.clone(), &[], &[]);
    assert!(
        f.endpoint.take().is_empty(),
        "user config overrides hub opt-in"
    );
    fs::write(f.root.join("user.toml"), "[telemetry]\nremote = true\n").unwrap();
    f.mcp(args.clone(), &[], &[]);
    assert!(!f.endpoint.take().is_empty(), "explicit user opt-in");
    f.project_policy("remote = false");
    f.mcp(args.clone(), &[], &[]);
    assert!(f.endpoint.take().is_empty(), "project can veto user opt-in");
    f.project_policy("remote = true");
    f.mcp(args.clone(), &[], &[]);
    let events = f.endpoint.take();
    assert!(!events.is_empty());
    assert!(events
        .iter()
        .all(|ev| ev["tool_name"] == "turbo_audit_spec"));
    // Server starts in an opted-in CWD; an explicit request workspace can opt out.
    let local = f.root.join("local");
    fs::create_dir_all(&local).unwrap();
    fs::write(
        local.join("turbo-lean.toml"),
        "[telemetry]\nremote = false\n",
    )
    .unwrap();
    f.mcp(
        json!({"file":f.root.join("Fixture.lean"), "project_dir":local}),
        &[],
        &[],
    );
    assert!(f.endpoint.take().is_empty());
    fs::copy(f.root.join("Fixture.lean"), local.join("Fixture.lean")).unwrap();
    f.mcp(json!({"file":local.join("Fixture.lean")}), &[], &[]);
    assert!(
        f.endpoint.take().is_empty(),
        "file parent supplies the project policy"
    );
    let local_str = local.to_str().unwrap();
    f.mcp_at(args.clone(), &[], &[], Some(local_str));
    assert!(
        f.endpoint.take().is_empty(),
        "server workspace overrides file parent"
    );
    // Request workspace takes precedence over server --project-dir as well.
    f.mcp_at(
        json!({"file":f.root.join("Fixture.lean"), "project_dir":f.root}),
        &[],
        &[],
        Some(local_str),
    );
    assert!(!f.endpoint.take().is_empty());
    fs::write(f.root.join("user.toml"), "[telemetry]\nremote = false\n").unwrap();
    f.mcp(args.clone(), &[], &[]);
    assert!(
        !f.endpoint.take().is_empty(),
        "project overrides user config"
    );
    f.mcp(args.clone(), &[], &[("TURBO_LEAN_TELEMETRY", "local")]);
    assert!(
        f.endpoint.take().is_empty(),
        "environment overrides project"
    );
    f.mcp(
        args.clone(),
        &["--telemetry", "full"],
        &[("TURBO_LEAN_TELEMETRY", "off")],
    );
    assert!(
        !f.endpoint.take().is_empty(),
        "CLI mode overrides environment mode"
    );
    f.mcp(
        args.clone(),
        &["--no-telemetry"],
        &[("TURBO_LEAN_TELEMETRY_REMOTE", "1")],
    );
    assert!(
        f.endpoint.take().is_empty(),
        "full disable wins over remote flag"
    );
    f.mcp(
        args.clone(),
        &["--telemetry", "full"],
        &[("TURBO_LEAN_NO_REMOTE_TELEMETRY", "1")],
    );
    assert!(
        f.endpoint.take().is_empty(),
        "no-remote veto wins over CLI opt-in"
    );
    f.mcp(args, &[], &[("TURBO_LEAN_TRUST_PROJECT_TELEMETRY", "0")]);
    assert!(
        f.endpoint.take().is_empty(),
        "untrusted project cannot opt in"
    );
}

#[cfg(unix)]
#[test]
fn optout_real_build_and_dedup_preserve_existing_lake_tree() {
    use std::os::unix::fs::{MetadataExt, PermissionsExt};
    let f = Fixture::new();
    f.command(&["build"], &[], None);
    assert!(f.endpoint.take().is_empty());
    let artifact = f.root.join(".lake/build/lib/lean/Fixture.olean");
    fs::set_permissions(&artifact, fs::Permissions::from_mode(0o444)).unwrap();
    fs::hard_link(&artifact, f.root.join("external-olean-link")).unwrap();
    for rel in [
        "packages/pkg/A.olean",
        "packages/pkg/B.olean",
        "cache/keep.barrel",
        "packages/pkg/.git/objects/pack/keep.pack",
    ] {
        let path = f.root.join(".lake").join(rel);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, b"existing package artifact").unwrap();
    }
    let snapshot = || {
        let mut rows: Vec<_> = walkdir::WalkDir::new(f.root.join(".lake"))
            .into_iter()
            .map(|entry| {
                let entry = entry.unwrap();
                let meta = entry.metadata().unwrap();
                (
                    entry.path().to_path_buf(),
                    meta.dev(),
                    meta.ino(),
                    meta.mode(),
                    meta.nlink(),
                    if meta.is_file() {
                        blake3::hash(&fs::read(entry.path()).unwrap())
                            .to_hex()
                            .to_string()
                    } else {
                        String::new()
                    },
                )
            })
            .collect();
        rows.sort_by(|a, b| a.0.cmp(&b.0));
        rows
    };
    let before = snapshot();
    for source in ["toml", "env", "cli"] {
        fs::write(
            f.root.join("turbo-lean.toml"),
            if source == "toml" {
                "[worktree]\nauto_link = false\n"
            } else {
                "[worktree]\nauto_link = true\n"
            },
        )
        .unwrap();
        let env = if source == "env" {
            vec![("TURBO_LEAN_NO_WORKTREE_LINK", "1")]
        } else {
            vec![]
        };
        let mut cli = if source == "cli" {
            vec!["--no-auto-worktree-link"]
        } else {
            vec![]
        };
        cli.push("worktree-dedup");
        let result = f.command(&cli, &env, None);
        assert_eq!(result["status"], "worktree_link_disabled");
        assert_eq!(snapshot(), before, "{source}: dedup changed .lake");
        *cli.last_mut().unwrap() = "build";
        for _ in 0..2 {
            // Executes real CAS hits against an already verified, pre-existing tree.
            let result = f.command(&cli, &env, None);
            assert!(
                matches!(result["status"].as_str(), Some("built" | "cache_hit")),
                "{result}"
            );
            let after = snapshot();
            assert_eq!(
                after.len(),
                before.len(),
                "{source}: build changed .lake entries"
            );
            for (after, before) in after.iter().zip(&before) {
                assert_eq!(after, before, "{source}: build changed .lake");
            }
        }
        assert!(f.endpoint.take().is_empty());
    }
}
