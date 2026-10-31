#![cfg(unix)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Output, Stdio};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

const MARKER: &str = "PROJECT_TOOLCHAIN_SHIM_EXECUTED";

struct Fixture(PathBuf);
impl Fixture {
    fn cli(&self, cache: &str) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_turbo-lean"));
        command
            .current_dir(&self.0)
            .env(
                "PATH",
                std::env::join_paths([self.0.join(".lake/build/bin")].into_iter().chain(
                    std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default()),
                ))
                .unwrap(),
            )
            .env("TURBO_LEAN_HOME", self.0.join(cache))
            .env(
                "TURBO_LEAN_STAGING_DIR",
                self.0.join(format!("{cache}-staging")),
            )
            .env("TURBO_LEAN_NO_DAEMON", "1")
            .env_remove("TURBO_LEAN_DAEMON")
            .env_remove("LEAN_PATH");
        command
    }
    fn clean(&self) {
        assert!(!self.0.join("shim-invoked").exists(), "a project shim ran");
    }
    fn run(&self, cache: &str, args: &[&str], success: bool) -> Output {
        let out = self.cli(cache).args(args).output().unwrap();
        self.clean();
        assert!(!String::from_utf8_lossy(&out.stdout).contains(MARKER));
        assert_eq!(
            out.status.success(),
            success,
            "{args:?}:\n{}\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        out
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
struct Server(Child);
impl Drop for Server {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}
fn checked(command: &mut Command) -> Output {
    let out = command.output().unwrap();
    assert!(
        out.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    out
}

#[test]
fn project_toolchain_names_cannot_substitute_verifiers_or_prewarm_helpers() {
    let f = Fixture(std::env::temp_dir().join(format!(
            "turbo-absolute-tools-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        )));
    fs::create_dir_all(&f.0).unwrap();
    fs::write(f.0.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
    let mut config = "name = \"shim_fixture\"\ndefaultTargets = [\"Demo\", \"lean\", \"lake\", \"leanc\"]\n[[lean_lib]]\nname = \"Demo\"\n".to_string();
    for tool in ["lean", "lake", "leanc"] {
        config.push_str(&format!(
            "[[lean_exe]]\nname = \"{tool}\"\nroot = \"Shim_{tool}\"\n"
        ));
    }
    fs::write(f.0.join("lakefile.toml"), config).unwrap();
    for tool in ["lean", "lake", "leanc"] {
        fs::write(f.0.join(format!("Shim_{tool}.lean")), format!(
            "def main : IO Unit := do\n  IO.FS.writeFile {} \"{MARKER}\"\n  IO.println \"{MARKER}\"\n",
            serde_json::to_string(&f.0.join("shim-invoked").to_string_lossy()).unwrap()
        )).unwrap();
    }
    fs::write(f.0.join("Demo.lean"), "theorem pinned : 1 + 1 = 2 := rfl\n").unwrap();
    fs::write(
        f.0.join("Harness.lean"),
        "def main : IO Unit := IO.println \"real-fastcheck-harness\"\n",
    )
    .unwrap();
    let prefix = checked(Command::new("lean").arg("--print-prefix"));
    let stock_lake =
        Path::new(std::str::from_utf8(&prefix.stdout).unwrap().trim()).join("bin/lake");
    checked(Command::new(&stock_lake).current_dir(&f.0).arg("build"));
    // Prove the attack fixture works: stock Lake's PATH exposes all three shims.
    for tool in ["lean", "lake", "leanc"] {
        let out = checked(
            Command::new(&stock_lake)
                .current_dir(&f.0)
                .args(["env", tool]),
        );
        assert!(String::from_utf8_lossy(&out.stdout).contains(MARKER));
        fs::remove_file(f.0.join("shim-invoked")).unwrap();
    }
    checked(Command::new("git").current_dir(&f.0).args(["init", "-q"]));
    checked(Command::new("git").current_dir(&f.0).args([
        "add",
        "*.lean",
        "lakefile.toml",
        "lean-toolchain",
    ]));
    checked(Command::new("git").current_dir(&f.0).args([
        "-c",
        "user.name=Test",
        "-c",
        "user.email=test@example.com",
        "commit",
        "-qm",
        "base",
    ]));
    fs::write(
        f.0.join("Demo.lean"),
        "theorem pinned : 1 + 1 = 2 := by\n  decide\n",
    )
    .unwrap();
    f.run(
        "check",
        &[
            "--json",
            "check",
            "Demo.lean",
            "--decl",
            "pinned",
            "--project-dir",
            ".",
        ],
        true,
    );
    let sandbox_available = Command::new("/usr/bin/bwrap")
        .args([
            "--unshare-all",
            "--ro-bind",
            "/",
            "/",
            "--",
            "/usr/bin/true",
        ])
        .output()
        .is_ok_and(|out| out.status.success());
    for mode in ["trusted", "untrusted"] {
        let success = mode == "trusted" || sandbox_available;
        for (cache, args) in [
            (
                format!("pr-{mode}"),
                vec![
                    "--json",
                    "pr-verify",
                    "--project-dir",
                    ".",
                    "--base",
                    "HEAD",
                    "--mode",
                    mode,
                ],
            ),
            (
                format!("ci-{mode}"),
                vec!["--json", "ci-verify", "--project-dir", ".", "--mode", mode],
            ),
        ] {
            let out = f.run(&cache, &args, success);
            if !success {
                // Restricted hosts must reject untrusted verification before any shim can run.
                assert!(
                    String::from_utf8_lossy(&out.stderr).contains("bubblewrap"),
                    "{}",
                    String::from_utf8_lossy(&out.stderr)
                );
            }
        }
    }
    // A shim that exits zero must never turn a broken proof into a passing verdict.
    fs::write(
        f.0.join("Demo.lean"),
        "theorem pinned : 1 + 1 = 2 := by\n  exact (0 : Nat)\n",
    )
    .unwrap();
    for args in [
        vec![
            "check",
            "Demo.lean",
            "--decl",
            "pinned",
            "--project-dir",
            ".",
        ],
        vec!["pr-verify", "--project-dir", ".", "--base", "HEAD"],
        vec!["ci-verify", "--project-dir", "."],
    ] {
        f.run("broken", &args, false);
    }
    let out = f.run(
        "fastcheck",
        &["--json", "fast-check", "Harness.lean", "--backend", "cpu"],
        true,
    );
    assert!(String::from_utf8_lossy(&out.stdout).contains("real-fastcheck-harness"));
    // This is the real CLI binary, so serve's non-test helper prewarm runs.
    let log = f.0.join("server.log");
    let mut server = Server(
        f.cli("prewarm")
            .args([
                "serve",
                "--listen",
                "127.0.0.1:0",
                "--allow-unauthenticated-local",
            ])
            .stdout(fs::File::create(&log).unwrap())
            .stderr(Stdio::inherit())
            .spawn()
            .unwrap(),
    );
    let deadline = Instant::now() + Duration::from_secs(120);
    loop {
        f.clean();
        assert!(
            server.0.try_wait().unwrap().is_none(),
            "server exited before prewarm completed"
        );
        if fs::read_to_string(&log).unwrap().contains("listening") {
            break;
        }
        assert!(Instant::now() < deadline, "server prewarm timed out");
        std::thread::sleep(Duration::from_millis(50));
    }
    assert!(fs::read_dir(f.0.join("prewarm/fastcheck_bins"))
        .unwrap()
        .any(|e| e
            .unwrap()
            .file_name()
            .to_string_lossy()
            .starts_with("turbo_zygote_")));
    assert!(
        fs::read_dir(f.0.join("prewarm-staging/fastcheck_shared_bins"))
            .unwrap()
            .any(|e| e.unwrap().path().extension().is_some_and(|e| e == "bin"))
    );
    f.clean();
}
