//! Real CLI/Lean lifecycle tests. Each fixture has a private HOME, CAS, and shm namespace.
#![cfg(target_os = "linux")]

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

const BIN: &str = env!("CARGO_BIN_EXE_turbo-lean");
// Each server prewarms real Lean environments. Bound peak memory on shared/CI machines.
static LIFECYCLE_TEST_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

// Direct writes keep acceptance evidence visible in the default CI test logs.
fn evidence(message: String) {
    writeln!(std::io::stdout().lock(), "{message}").unwrap();
}

fn wait_until(
    child: &mut std::process::Child,
    deadline: Instant,
) -> std::io::Result<std::process::ExitStatus> {
    loop {
        if let Some(status) = child.try_wait()? {
            return Ok(status);
        }
        if Instant::now() >= deadline {
            return Err(std::io::Error::new(
                std::io::ErrorKind::TimedOut,
                "child deadline exceeded",
            ));
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

fn wait_child(
    child: &mut std::process::Child,
    timeout: Duration,
) -> std::io::Result<std::process::ExitStatus> {
    let result = wait_until(child, Instant::now() + timeout);
    if result.is_err() {
        let _ = child.kill();
        // Reaping is bounded too: a broken kernel/child must not hang panic cleanup.
        let _ = wait_until(child, Instant::now() + Duration::from_secs(2));
    }
    result
}

struct ChildGuard(std::process::Child);
impl Drop for ChildGuard {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = wait_child(&mut self.0, Duration::from_secs(2));
    }
}

#[test]
fn child_wait_deadline_kills_and_reaps() {
    let mut child = ChildGuard(Command::new("sleep").arg("30").spawn().unwrap());
    let start = Instant::now();
    let err = wait_child(&mut child.0, Duration::from_millis(50)).unwrap_err();
    assert_eq!(err.kind(), std::io::ErrorKind::TimedOut);
    assert!(child.0.try_wait().unwrap().is_some());
    assert!(start.elapsed() < Duration::from_secs(1));
}

struct Fixture {
    root: PathBuf,
    staging: PathBuf,
}

impl Fixture {
    fn new() -> Self {
        let tag = format!(
            "{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        );
        let root = std::env::temp_dir().join(format!("turbo-lifecycle-{tag}"));
        let staging = Path::new("/dev/shm").join(format!("turbo-lifecycle-{tag}"));
        fs::create_dir_all(root.join("home")).unwrap();
        fs::create_dir_all(&staging).unwrap();
        fs::write(root.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            root.join("lakefile.toml"),
            "name = \"lifecycle\"\nversion = \"0.1.0\"\n",
        )
        .unwrap();
        fs::write(
            root.join("Quick.lean"),
            "import Lean\ntheorem quick : True := by trivial\n",
        )
        .unwrap();
        Self { root, staging }
    }

    fn command(&self) -> Command {
        let mut cmd = Command::new(BIN);
        cmd.current_dir(&self.root)
            .env("HOME", self.root.join("home"))
            .env("TURBO_LEAN_HOME", self.root.join("cas"))
            .env("TURBO_LEAN_STAGING_DIR", &self.staging)
            .env("TURBO_LEAN_TELEMETRY", "off")
            .env("LEAN_NATIVE_TELEMETRY", "off")
            .env("LEAN_NUM_THREADS", "4")
            .env_remove("TURBO_LEAN_NO_DAEMON")
            .env_remove("TURBO_LEAN_DAEMON")
            .env_remove("TURBO_LEAN_DAEMON_STATE_FILE")
            .env_remove("TURBO_LEAN_DAEMON_IDLE_SECS")
            .env_remove("TURBO_LEAN_TIMEOUT_MS");
        // HOME is deliberately temporary, but Lean must use the installed toolchain.
        let elan = std::env::var_os("ELAN_HOME")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from(std::env::var_os("HOME").unwrap()).join(".elan"));
        cmd.env("ELAN_HOME", elan);
        cmd
    }

    fn run(&self, mut cmd: Command) -> Output {
        let log = self.root.join("command.log");
        let file = fs::File::create(&log).unwrap();
        cmd.stdout(file.try_clone().unwrap()).stderr(file);
        let mut child = ChildGuard(cmd.spawn().unwrap());
        let status = wait_child(&mut child.0, Duration::from_secs(120))
            .unwrap_or_else(|e| panic!("CLI deadline: {e}: {}", fs::read_to_string(&log).unwrap()));
        Output {
            status,
            stdout: fs::read(&log).unwrap(),
            stderr: Vec::new(),
        }
    }

    fn check(&self, name: &str) -> Command {
        let mut cmd = self.command();
        cmd.args(["check", name, "--project-dir", ".", "--json"]);
        cmd
    }

    fn warm(&self) {
        let out = self.run(self.check("Quick.lean"));
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stdout)
        );
        self.wait_for(Duration::from_secs(10), || self.pids().len() >= 2);
    }

    fn pids(&self) -> Vec<u32> {
        let marker = format!("TURBO_LEAN_STAGING_DIR={}", self.staging.display());
        fs::read_dir("/proc")
            .unwrap()
            .flatten()
            .filter_map(|e| {
                let pid = e.file_name().to_str()?.parse::<u32>().ok()?;
                let env = fs::read(e.path().join("environ")).ok()?;
                if !env.split(|b| *b == 0).any(|v| {
                    v == marker.as_bytes() || v.starts_with(format!("{marker}-oneshot-").as_bytes())
                }) {
                    return None;
                }
                let exe = fs::read_link(e.path().join("exe")).ok()?;
                let name = exe.file_name()?.to_str()?;
                (name.starts_with("turbo_zygote_")
                    || name == "turbo-zygote"
                    || name == "turbo-lean"
                    || name == "lean")
                    .then_some(pid)
            })
            .collect()
    }

    fn one_shot_dirs(&self) -> Vec<PathBuf> {
        let prefix = format!(
            "{}-oneshot-",
            self.staging.file_name().unwrap().to_string_lossy()
        );
        fs::read_dir(self.staging.parent().unwrap())
            .unwrap()
            .flatten()
            .filter(|entry| entry.file_name().to_string_lossy().starts_with(&prefix))
            .map(|entry| entry.path())
            .collect()
    }

    fn wait_for(&self, timeout: Duration, condition: impl Fn() -> bool) {
        let start = Instant::now();
        while !condition() {
            assert!(
                start.elapsed() < timeout,
                "lifecycle deadline exceeded; pids={:?}, staging={}",
                self.pids(),
                self.staging.display()
            );
            std::thread::sleep(Duration::from_millis(50));
        }
    }

    fn stop(&self) {
        let mut cmd = self.command();
        cmd.args(["daemon", "stop"]);
        let out = self.run(cmd);
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stdout)
        );
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        // Scope is always explicit, including on assertion failure.
        if let Ok(child) = self
            .command()
            .args(["daemon", "stop"])
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
        {
            let mut child = ChildGuard(child);
            let _ = wait_child(&mut child.0, Duration::from_secs(10));
        }
        for dir in self.one_shot_dirs() {
            let _ = fs::remove_dir_all(dir);
        }
        let _ = fs::remove_dir_all(&self.root);
        let _ = fs::remove_dir_all(&self.staging);
    }
}

#[test]
fn check_no_daemon_leaves_no_processes_or_staging() {
    let _serial = LIFECYCLE_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let f = Fixture::new();
    for flag in [true, false] {
        let name = if flag { "quick_flag" } else { "quick_env" };
        fs::write(
            f.root.join("Quick.lean"),
            format!("import Lean\ntheorem {name} : True := by trivial\n"),
        )
        .unwrap();
        let mut cmd = f.check("Quick.lean");
        cmd.args(["--decl", name]);
        if flag {
            cmd.arg("--no-daemon");
        } else {
            cmd.env("TURBO_LEAN_NO_DAEMON", "1");
        }
        let out = f.run(cmd);
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stdout)
        );
        f.wait_for(Duration::from_secs(3), || f.pids().is_empty());
        assert_eq!(fs::read_dir(&f.staging).unwrap().count(), 0);
        assert!(
            f.one_shot_dirs().is_empty(),
            "private sibling staging leaked: {:?}",
            f.one_shot_dirs()
        );
        evidence(format!(
            "no-daemon (flag={flag}): 0 PIDs, 0 staging entries"
        ));
    }
    // Expiring an existing daemon must not remove a concurrent one-shot's files.
    fs::write(
        f.root.join("turbo-lean.toml"),
        "[zygote]\nidle_ttl_secs = 1\n",
    )
    .unwrap();
    fs::write(
        f.root.join("Quick.lean"),
        "import Lean\ntheorem warm_after_oneshot : True := by trivial\n",
    )
    .unwrap();
    f.warm();
    fs::write(f.root.join("OneShot.lean"), "#eval IO.sleep 2000\n").unwrap();
    let mut cmd = f.command();
    cmd.args([
        "eval",
        "OneShot.lean",
        "--project-dir",
        ".",
        "--no-daemon",
        "--timeout-ms",
        "15000",
    ]);
    let out = f.run(cmd);
    assert!(
        out.status.success(),
        "daemon TTL removed one-shot staging: {}",
        String::from_utf8_lossy(&out.stdout)
    );
    f.wait_for(Duration::from_secs(5), || f.pids().is_empty());
    assert!(!f.staging.exists());
    assert!(
        f.one_shot_dirs().is_empty(),
        "private sibling staging leaked: {:?}",
        f.one_shot_dirs()
    );
    evidence("one-shot survived peer daemon TTL: 0 PIDs and private staging removed".to_string());
}

#[test]
fn daemon_stop_removes_workers_and_staging_in_its_namespace() {
    let _serial = LIFECYCLE_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let f = Fixture::new();
    let peer = Fixture::new();
    f.warm();
    peer.warm();
    let peer_pids = peer.pids();
    fs::write(f.staging.join("owned-staging"), "staging").unwrap();
    f.stop();
    f.wait_for(Duration::from_secs(3), || f.pids().is_empty());
    assert!(!f.staging.exists());
    assert_eq!(peer.pids(), peer_pids, "stop killed another namespace");
    f.stop(); // idempotent
    evidence("daemon stop: 0 PIDs, staging removed, peer namespace survived".to_string());
}

#[test]
fn idle_ttl_exits_and_cleans_staging() {
    let _serial = LIFECYCLE_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let f = Fixture::new();
    fs::write(
        f.root.join("turbo-lean.toml"),
        "[zygote]\nidle_ttl_secs = 5\n",
    )
    .unwrap();
    f.warm();
    fs::write(f.root.join("Active.lean"), "#eval IO.sleep 6000\n").unwrap();
    let mut cmd = f.command();
    cmd.args([
        "eval",
        "Active.lean",
        "--project-dir",
        ".",
        "--timeout-ms",
        "15000",
    ]);
    let out = f.run(cmd);
    assert!(
        out.status.success(),
        "idle TTL interrupted an active request: {}",
        String::from_utf8_lossy(&out.stdout)
    );
    assert!(!f.pids().is_empty());
    let start = Instant::now();
    f.wait_for(Duration::from_secs(15), || {
        f.pids().is_empty() && !f.staging.exists()
    });
    evidence(format!(
        "idle_ttl_secs=5: 0 PIDs and staging removed in {:?}",
        start.elapsed()
    ));
}

#[test]
fn check_timeout_reaches_existing_daemon_without_restart() {
    let _serial = LIFECYCLE_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let f = Fixture::new();
    fs::write(
        f.root.join("turbo-lean.toml"),
        "[zygote]\ntimeout_secs = 60\n",
    )
    .unwrap();
    f.warm();
    let server_pids: Vec<_> = f
        .pids()
        .into_iter()
        .filter(|pid| {
            fs::read_link(format!("/proc/{pid}/exe"))
                .unwrap()
                .file_name()
                .unwrap()
                == "turbo-lean"
        })
        .collect();
    assert_eq!(server_pids.len(), 1);
    // A closed decidable theorem whose reduction exceeds the one-second deadline.
    for decl in [false, true] {
        let name = if decl { "slow_decl" } else { "slow" };
        fs::write(f.root.join("Slow.lean"), format!("import Lean\nset_option maxRecDepth 10000000\nset_option maxHeartbeats 0\ntheorem {name} : (List.range 1000000).length = 1000000 := by decide\n")).unwrap();
        let mut cmd = f.check("Slow.lean");
        cmd.args(["--timeout", "1"])
            .env("TURBO_LEAN_TIMEOUT_MS", "60000"); // explicit CLI flag must win
        if decl {
            cmd.args(["--decl", name]);
        }
        let start = Instant::now();
        let out = f.run(cmd);
        let elapsed = start.elapsed();
        let text = String::from_utf8_lossy(&out.stdout);
        assert!(
            !out.status.success(),
            "slow theorem unexpectedly passed: {text}"
        );
        assert!(text.contains("timed out"), "{text}");
        assert!(
            (Duration::from_millis(800)..Duration::from_secs(10)).contains(&elapsed),
            "timeout took {elapsed:?}: {text}"
        );
        for pid in &server_pids {
            assert!(
                Path::new(&format!("/proc/{pid}/exe")).exists(),
                "daemon restarted"
            );
        }
        evidence(format!("existing-daemon check --timeout 1 (decl={decl}): timed out in {elapsed:?}; server PID unchanged"));
    }
    fs::write(
        f.root.join("Fresh.lean"),
        "import Lean\ntheorem fresh : 2 + 2 = 4 := by decide\n",
    )
    .unwrap();
    let out = f.run(f.check("Fresh.lean"));
    assert!(
        out.status.success(),
        "daemon unusable after timeout: {}",
        String::from_utf8_lossy(&out.stdout)
    );
}

#[test]
fn warm_daemon_late_crash_retry_shares_eval_deadline() {
    use std::io::Read;
    let _serial = LIFECYCLE_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let f = Fixture::new();
    f.warm();
    let state: serde_json::Value =
        serde_json::from_slice(&fs::read(f.root.join("cas/zygote_daemon.json")).unwrap()).unwrap();
    let eval = |source: &str, timeout_ms: u64| {
        let mut stream = std::net::TcpStream::connect(state["addr"].as_str().unwrap()).unwrap();
        stream
            .set_read_timeout(Some(Duration::from_secs(5)))
            .unwrap();
        stream
            .set_write_timeout(Some(Duration::from_secs(5)))
            .unwrap();
        let body = serde_json::json!({"source": source, "timeout_ms": timeout_ms}).to_string();
        write!(stream, "POST /eval HTTP/1.1\r\nHost: localhost\r\nX-Turbo-Token: {}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{}",
            state["auth_token"].as_str().unwrap(), body.len(), body).unwrap();
        let mut response = String::new();
        stream.read_to_string(&mut response).unwrap();
        serde_json::from_str::<serde_json::Value>(response.split_once("\r\n\r\n").unwrap().1)
            .unwrap()
    };
    assert_eq!(eval("#eval (0 : Nat)", 10_000)["ok"], true);
    let start = Instant::now();
    let reply = eval("#eval (do IO.sleep 800; IO.Process.exit 1 : IO Unit)", 1000);
    let elapsed = start.elapsed();
    assert_eq!(reply["timed_out"], true, "{reply}");
    assert_eq!(reply["crashed"], false, "{reply}");
    assert!(
        elapsed < Duration::from_millis(1250),
        "late crash replay exceeded shared deadline: {elapsed:?}: {reply}"
    );
    evidence(format!(
        "late crash + replay: timeout_ms=1000, timed_out=true in {elapsed:?}"
    ));
}

#[test]
// Scheduler-dependent integration smoke test; exact admission/expiry transitions are
// covered by server::tests::admission_and_expiry_share_one_state_machine.
fn expiry_boundary_checks_succeed_smoke() {
    let _serial = LIFECYCLE_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let f = Fixture::new();
    fs::write(
        f.root.join("turbo-lean.toml"),
        "[zygote]\nidle_ttl_secs = 1\n",
    )
    .unwrap();
    f.warm();
    for (i, delay_ms) in [950, 1000, 1050].into_iter().enumerate() {
        std::thread::sleep(Duration::from_millis(delay_ms));
        let name = format!("boundary_{i}");
        fs::write(
            f.root.join("Boundary.lean"),
            format!("import Lean\ntheorem {name} : True := by trivial\n"),
        )
        .unwrap();
        let mut cmd = f.check("Boundary.lean");
        cmd.args(["--decl", &name]);
        let out = f.run(cmd);
        assert!(
            out.status.success(),
            "request at TTL boundary failed: {}",
            String::from_utf8_lossy(&out.stdout)
        );
    }
    f.wait_for(Duration::from_secs(10), || {
        f.pids().is_empty() && !f.staging.exists()
    });
    assert!(!f.root.join("cas/zygote_daemon.json").exists());
    evidence(
        "expiry-boundary check: requests before, at and after TTL succeeded; discovery withdrawn"
            .into(),
    );
}

#[test]
fn unavailable_zygote_fallback_obeys_check_timeout_and_reaps_lean() {
    use std::os::unix::fs::PermissionsExt;
    let _serial = LIFECYCLE_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let f = Fixture::new();
    let mut seed = f.check("Quick.lean");
    seed.args(["--decl", "quick", "--no-daemon"]);
    let out = f.run(seed);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stdout)
    );
    let mut replaced = 0;
    let marker = f.root.join("import-unavailable");
    // Inject an import-unavailable reply at the worker protocol boundary. Stock Lean
    // still checks the real slow source below; never modify a shared cached inode.
    for entry in fs::read_dir(f.root.join("cas/fastcheck_bins"))
        .unwrap()
        .flatten()
    {
        if entry
            .file_name()
            .to_string_lossy()
            .starts_with("turbo_zygote_")
        {
            let tmp = entry.path().with_extension("replacement");
            fs::write(&tmp, format!(r#"#!/bin/sh
while IFS= read -r request; do
  echo unavailable >> '{}'
  echo '{{"ok":false,"import_ok":false,"env_cache_hit":false,"import_us":0,"elab_us":0,"errors":["import unavailable"]}}'
done
"#, marker.display())).unwrap();
            fs::set_permissions(&tmp, fs::Permissions::from_mode(0o700)).unwrap();
            fs::rename(tmp, entry.path()).unwrap();
            replaced += 1;
        }
    }
    assert!(replaced > 0, "seed did not cache a worker");
    for decl in [false, true] {
        // Allow environment discovery and declaration identity elaboration to
        // reach the injected worker, then deterministically outlast the budget
        // inside the stock Lean fallback rather than relying on proof speed.
        fs::write(f.root.join("Fallback.lean"), "import Lean\ntheorem fallback_slow : True := by\n  run_tac do IO.sleep 30000\n  trivial\n").unwrap();
        let mut cmd = f.check("Fallback.lean");
        cmd.args(["--timeout", "5", "--no-daemon"]);
        if decl {
            cmd.args(["--decl", "fallback_slow"]);
        }
        let start = Instant::now();
        let out = f.run(cmd);
        let text = String::from_utf8_lossy(&out.stdout);
        assert!(
            !out.status.success() && text.contains("timed out"),
            "{text}"
        );
        assert!(
            start.elapsed() < Duration::from_secs(15),
            "fallback exceeded bound: {text}"
        );
        f.wait_for(Duration::from_secs(3), || f.pids().is_empty());
        evidence(format!(
            "import-unavailable fallback --timeout 5 (decl={decl}): {:?}, 0 Lean PIDs",
            start.elapsed()
        ));
    }
    assert!(
        marker.exists(),
        "unavailable-import worker was not exercised"
    );
}

#[test]
fn eval_first_startup_honours_project_idle_ttl() {
    let _serial = LIFECYCLE_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let f = Fixture::new();
    fs::write(
        f.root.join("turbo-lean.toml"),
        "[zygote]\nidle_ttl_secs = 2\n",
    )
    .unwrap();
    fs::create_dir_all(f.root.join("nested")).unwrap();
    for explicit_project in [false, true] {
        fs::write(
            f.root.join("nested/EvalFirst.lean"),
            format!("#eval {}\n", if explicit_project { 43 } else { 42 }),
        )
        .unwrap();
        let mut cmd = f.command();
        cmd.args(["eval", "nested/EvalFirst.lean"]);
        if explicit_project {
            cmd.args(["--project-dir", "."]);
        }
        let out = f.run(cmd);
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stdout)
        );
        assert!(!f.pids().is_empty(), "eval did not start a daemon");
        f.wait_for(Duration::from_secs(10), || {
            f.pids().is_empty() && !f.staging.exists()
        });
        evidence(format!("eval-first idle_ttl_secs=2 (explicit_project={explicit_project}): 0 PIDs and staging removed"));
    }
}

#[test]
fn lifecycle_lock_serializes_startup_and_staging_removal() {
    use std::os::fd::AsRawFd;
    let _serial = LIFECYCLE_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let f = Fixture::new();
    let lock = fs::OpenOptions::new()
        .create(true)
        .truncate(false)
        .read(true)
        .write(true)
        .open(format!("/tmp/turbo-lean-lifecycle-{}.lock", unsafe {
            libc::geteuid()
        }))
        .unwrap();
    assert_eq!(unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX) }, 0);
    fs::remove_dir_all(&f.staging).unwrap();
    let mut startup = ChildGuard(
        f.check("Quick.lean")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .unwrap(),
    );
    std::thread::sleep(Duration::from_millis(300));
    assert!(
        startup.0.try_wait().unwrap().is_none(),
        "startup did not wait for teardown lock"
    );
    assert!(
        !f.staging.exists(),
        "startup prepared staging without the lifecycle lock"
    );
    assert_eq!(unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_UN) }, 0);
    assert!(wait_child(&mut startup.0, Duration::from_secs(120))
        .unwrap()
        .success());
    assert!(f.staging.exists());
    assert_eq!(unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_SH) }, 0);
    let mut stop = ChildGuard(
        f.command()
            .args(["daemon", "stop"])
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .unwrap(),
    );
    std::thread::sleep(Duration::from_millis(300));
    assert!(
        stop.0.try_wait().unwrap().is_none(),
        "teardown did not wait for staging preparation"
    );
    assert!(f.staging.exists());
    assert_eq!(unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_UN) }, 0);
    assert!(wait_child(&mut stop.0, Duration::from_secs(10))
        .unwrap()
        .success());
    assert!(!f.staging.exists());
    assert!(f.pids().is_empty());
    evidence("lifecycle flock: startup and staging removal waited for conflicting holders".into());
}

#[test]
fn daemon_stop_spares_auditors_and_foreground_serve() {
    let _serial = LIFECYCLE_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let f = Fixture::new();
    f.warm();
    let audit_bin = f.root.join("turbo_zygote_audit_fixture");
    fs::copy("/bin/bash", &audit_bin).unwrap();
    let mut audit = ChildGuard(
        Command::new(audit_bin)
            .args(["-c", "read -t 90", "--audit-modules"])
            .env("TURBO_LEAN_STAGING_DIR", &f.staging)
            .stdin(Stdio::piped())
            .spawn()
            .unwrap(),
    );
    let port = std::net::TcpListener::bind("127.0.0.1:0")
        .unwrap()
        .local_addr()
        .unwrap()
        .port();
    let addr = format!("127.0.0.1:{port}");
    let mut foreground = ChildGuard(
        f.command()
            .args(["serve", "--listen", &addr])
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .unwrap(),
    );
    f.wait_for(Duration::from_secs(30), || {
        std::net::TcpStream::connect(&addr).is_ok()
    });
    let mut stop = f.command();
    stop.args(["daemon", "stop"]);
    let out = f.run(stop);
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(out.status.success(), "{text}");
    assert!(
        audit.0.try_wait().unwrap().is_none(),
        "stop killed --audit-modules"
    );
    assert!(
        foreground.0.try_wait().unwrap().is_none(),
        "stop killed foreground serve"
    );
    assert!(
        f.staging.exists() && text.contains("Retained staging"),
        "{text}"
    );
    drop(audit);
    drop(foreground);
    f.stop();
    assert!(!f.staging.exists());
    evidence(
        "daemon stop: audit worker and foreground serve survived; retained namespace reported"
            .into(),
    );
}

#[test]
fn no_daemon_env_uses_relaxed_booleans() {
    let _serial = LIFECYCLE_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let f = Fixture::new();
    for (i, value) in ["0", "false", "true", "yes"].into_iter().enumerate() {
        let name = format!("boolean_{i}");
        fs::write(
            f.root.join("Boolean.lean"),
            format!("import Lean\ntheorem {name} : True := by trivial\n"),
        )
        .unwrap();
        let mut cmd = f.check("Boolean.lean");
        cmd.args(["--decl", &name])
            .env("TURBO_LEAN_NO_DAEMON", value);
        let out = f.run(cmd);
        assert!(
            out.status.success(),
            "{value}: {}",
            String::from_utf8_lossy(&out.stdout)
        );
        if i < 2 {
            assert!(f.pids().len() >= 2, "{value} disabled the daemon");
            f.stop();
        } else {
            f.wait_for(Duration::from_secs(3), || f.pids().is_empty());
        }
        evidence(format!(
            "TURBO_LEAN_NO_DAEMON={value}: daemon_allowed={}",
            i < 2
        ));
    }
}
