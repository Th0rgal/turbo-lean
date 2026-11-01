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
            .env("GIT_CONFIG_COUNT", "1")
            .env("GIT_CONFIG_KEY_0", "core.fsmonitor")
            .env(
                "GIT_CONFIG_VALUE_0",
                self.0.join(".lake/build/bin/repo-exec"),
            )
            .env(
                "GIT_EXTERNAL_DIFF",
                self.0.join(".lake/build/bin/repo-exec"),
            )
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

fn sandbox_available() -> bool {
    Command::new("/usr/bin/bwrap")
        .args([
            "--unshare-all",
            "--ro-bind",
            "/",
            "/",
            "--",
            "/usr/bin/true",
        ])
        .output()
        .is_ok_and(|out| out.status.success())
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
    fs::write(f.0.join("turbo-lean.toml"), "[axioms]\nallow = []\n").unwrap();
    fs::write(f.0.join(".gitattributes"), "*.lean filter=attack\n").unwrap();
    checked(Command::new("git").current_dir(&f.0).args([
        "add",
        "turbo-lean.toml",
        ".gitattributes",
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
    // Host-side Git/sandbox shims exit successfully: an exit-code-only probe
    // would accept them. A single marker also catches repository-configured code.
    use std::os::unix::fs::PermissionsExt;
    for tool in ["git", "bwrap", "repo-exec"] {
        let path = f.0.join(".lake/build/bin").join(tool);
        fs::write(
            &path,
            format!(
                "#!/bin/sh\nprintf '{MARKER}' > '{}'\nexit 0\n",
                f.0.join("shim-invoked").display()
            ),
        )
        .unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).unwrap();
        checked(&mut Command::new(&path));
        assert!(f.0.join("shim-invoked").exists());
        fs::remove_file(f.0.join("shim-invoked")).unwrap();
    }
    let repo_exec = f.0.join(".lake/build/bin/repo-exec");
    for key in [
        "core.fsmonitor",
        "core.hooksPath",
        "diff.external",
        "filter.attack.smudge",
        "filter.attack.process",
    ] {
        checked(
            Command::new("/usr/bin/git")
                .current_dir(&f.0)
                .args(["config", key])
                .arg(&repo_exec),
        );
    }
    checked(
        Command::new("/usr/bin/git")
            .current_dir(&f.0)
            .args(["status", "--porcelain"]),
    );
    assert!(
        f.0.join("shim-invoked").exists(),
        "fsmonitor control must execute the attack"
    );
    fs::remove_file(f.0.join("shim-invoked")).unwrap();
    for override_path in [PathBuf::from("git"), f.0.join(".lake/build/bin/git")] {
        let out = f
            .cli("invalid-git-override")
            .env("TURBO_LEAN_GIT", &override_path)
            .args(["pr-verify", "--project-dir", ".", "--base", "HEAD"])
            .output()
            .unwrap();
        assert!(!out.status.success());
        assert!(String::from_utf8_lossy(&out.stderr).contains("Trusted Git"));
        f.clean();
    }
    // The working tree cannot relax the base policy.
    fs::write(f.0.join("turbo-lean.toml"), "[axioms]\nallow = [\"*\"]\n").unwrap();
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
    let sandbox_available = sandbox_available();
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
    fs::write(
        f.0.join("Untracked.lean"),
        "theorem fresh : True := True.intro\n",
    )
    .unwrap();
    let changed = f.run(
        "git-change-discovery",
        &[
            "--json",
            "pr-verify",
            "--project-dir",
            ".",
            "--base",
            "HEAD~0",
        ],
        true,
    );
    assert!(String::from_utf8_lossy(&changed.stdout).contains("Untracked.lean"));
    fs::write(
        f.0.join("Demo.lean"),
        "axiom injected : False\ntheorem pinned : 1 + 1 = 2 := False.elim injected\n",
    )
    .unwrap();
    let rejected = f.run(
        "git-base-policy",
        &["pr-verify", "--project-dir", ".", "--base", "HEAD"],
        false,
    );
    assert!(
        String::from_utf8_lossy(&rejected.stderr).contains("axiom")
            || String::from_utf8_lossy(&rejected.stdout).contains("axiom")
    );
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
            .env_remove("TURBO_LEAN_NO_DAEMON")
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

// Conditional Git config is invisible in the original repository, but becomes
// active in a linked worktree. Exercise both snapshot branches through the CLI.
#[test]
fn conditional_worktree_filters_cannot_run_during_pr_verification() {
    let f = Fixture(std::env::temp_dir().join(format!(
        "turbo-conditional-filter-{}-{}", std::process::id(),
        SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()
    )));
    fs::create_dir_all(&f.0).unwrap();
    fs::write(f.0.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
    fs::write(f.0.join(".gitignore"), ".lake/\ncache/\ncache-staging/\n").unwrap();
    fs::write(f.0.join(".gitattributes"), "*.lean filter=attack\n").unwrap();
    fs::write(f.0.join("Demo.lean"), "theorem pinned : 1 + 1 = 2 := rfl\n").unwrap();
    checked(
        Command::new("/usr/bin/git")
            .current_dir(&f.0)
            .args(["init", "-q"]),
    );
    checked(
        Command::new("/usr/bin/git")
            .current_dir(&f.0)
            .args(["add", "."]),
    );
    checked(Command::new("/usr/bin/git").current_dir(&f.0).args([
        "-c",
        "user.name=Test",
        "-c",
        "user.email=test@example.com",
        "commit",
        "-qm",
        "base",
    ]));
    let config = f.0.join(".git/attack-config");
    let marker = f.0.join("shim-invoked");
    for (key, command) in [
        (
            "smudge",
            format!("echo attacked > '{}'; cat", marker.display()),
        ),
        (
            "process",
            format!("echo attacked > '{}'; exit 1", marker.display()),
        ),
    ] {
        checked(
            Command::new("/usr/bin/git")
                .args(["config", "--file"])
                .arg(&config)
                .arg(format!("filter.attack.{key}"))
                .arg(command),
        );
    }
    checked(
        Command::new("/usr/bin/git")
            .current_dir(&f.0)
            .args(["config", "includeIf.gitdir:**/worktrees/**.path"])
            .arg(&config),
    );
    let invisible = Command::new("/usr/bin/git")
        .current_dir(&f.0)
        .args(["config", "--get", "filter.attack.process"])
        .output()
        .unwrap();
    assert_eq!(
        invisible.status.code(),
        Some(1),
        "filter must be unseen in original repo"
    );
    // Positive control: ordinary checkout executes the conditional filter.
    let control = f.0.join("control");
    let checkout = Command::new("/usr/bin/git")
        .current_dir(&f.0)
        .args(["worktree", "add", "--detach"])
        .arg(&control)
        .arg("HEAD")
        .output()
        .unwrap();
    assert!(
        marker.exists(),
        "conditional checkout attack fixture did not execute"
    );
    if checkout.status.success() {
        checked(
            Command::new("/usr/bin/git")
                .current_dir(&f.0)
                .args(["worktree", "remove", "--force"])
                .arg(&control),
        );
    } else {
        // A process filter that exits during the handshake can abort checkout;
        // Git removes the failed worktree registration itself.
        checked(
            Command::new("/usr/bin/git")
                .current_dir(&f.0)
                .args(["worktree", "prune"]),
        );
    }
    fs::remove_file(&marker).unwrap();

    // With no Lake config, pr-verify materializes both the base and HEAD.
    fs::write(
        f.0.join("Demo.lean"),
        "theorem pinned : 1 + 1 = 2 := by decide\n",
    )
    .unwrap();
    let out = f.run(
        "cache",
        &[
            "--json",
            "pr-verify",
            "--project-dir",
            ".",
            "--base",
            "HEAD",
        ],
        true,
    );
    let json: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(json["statement_edited_theorems_count"], 0);
    // A changed type needs Lake to recheck dependents before the statement gate.
    fs::write(
        f.0.join("lakefile.toml"),
        "name = \"filter_fixture\"\ndefaultTargets = [\"Demo\"]\n[[lean_lib]]\nname = \"Demo\"\n",
    )
    .unwrap();
    // A changed type must still be compared with the real base statement.
    fs::write(f.0.join("Demo.lean"), "theorem pinned : 2 + 2 = 4 := rfl\n").unwrap();
    let rejected = f.run(
        "cache",
        &[
            "pr-verify",
            "--project-dir",
            ".",
            "--base",
            "HEAD",
            "--disallow-statement-changes",
        ],
        false,
    );
    let diagnostic = format!(
        "{}{}",
        String::from_utf8_lossy(&rejected.stdout),
        String::from_utf8_lossy(&rejected.stderr)
    );
    assert!(diagnostic.contains("Demo.lean::pinned"), "{diagnostic}");
    f.clean();
    assert!(
        !f.0.join(".git/worktrees").exists()
            || fs::read_dir(f.0.join(".git/worktrees"))
                .unwrap()
                .next()
                .is_none()
    );
}

// A partial clone's promised base blob is missing locally. Plain Git would lazily fetch it
// over the repository's own `core.sshCommand`; pr-verify must fail closed instead, and never
// run that command or the repository's credential helper.
#[test]
fn missing_promised_base_blob_fails_closed_without_running_repository_helpers() {
    let f = Fixture(std::env::temp_dir().join(format!(
        "turbo-promisor-{}-{}",
        std::process::id(),
        SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()
    )));
    fs::create_dir_all(&f.0).unwrap();
    let marker = f.0.join("shim-invoked");
    let plain = |args: &[&str]| {
        Command::new("/usr/bin/git")
            .env_clear()
            .env("PATH", "/usr/bin:/bin")
            .env("HOME", &f.0)
            .env("GIT_CONFIG_NOSYSTEM", "1")
            .env("GIT_TERMINAL_PROMPT", "0")
            .current_dir(&f.0)
            .args(args)
            .output()
            .unwrap()
    };
    fs::write(f.0.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
    fs::write(f.0.join(".gitignore"), ".lake/\ncache/\ncache-staging/\n").unwrap();
    fs::write(f.0.join("Demo.lean"), "theorem pinned : 1 + 1 = 2 := rfl\n").unwrap();
    for args in [
        &["init", "-q"][..],
        &["add", "."],
        &[
            "-c",
            "user.name=T",
            "-c",
            "user.email=t@e",
            "commit",
            "-qm",
            "base",
        ],
    ] {
        assert!(plain(args).status.success(), "{args:?}");
    }
    let oid = String::from_utf8(plain(&["rev-parse", "HEAD:Demo.lean"]).stdout).unwrap();
    let oid = oid.trim();
    fs::remove_file(f.0.join(".git/objects").join(&oid[..2]).join(&oid[2..])).unwrap();
    let touch = format!("sh -c 'touch {}; exit 1' --", marker.display());
    let helper = format!("!touch {} #", marker.display());
    for (key, value) in [
        ("remote.origin.url", "ssh://example.invalid/repo"),
        ("remote.origin.promisor", "true"),
        ("extensions.partialClone", "origin"),
        ("core.sshCommand", touch.as_str()),
        ("protocol.ssh.allow", "always"),
        ("credential.helper", helper.as_str()),
    ] {
        assert!(plain(&["config", key, value]).status.success(), "{key}");
    }
    // Positive control: plain Git lazily fetches and runs the repository's ssh command.
    assert!(!plain(&["cat-file", "-p", "HEAD:Demo.lean"])
        .status
        .success());
    assert!(marker.exists(), "lazy-fetch control did not run sshCommand");
    fs::remove_file(&marker).unwrap();

    fs::write(
        f.0.join("Demo.lean"),
        "theorem pinned : 1 + 1 = 2 := by decide\n",
    )
    .unwrap();
    for mode in ["trusted", "untrusted"] {
        let out = f.run(
            &format!("cache-{mode}"),
            &[
                "pr-verify",
                "--project-dir",
                ".",
                "--base",
                "HEAD",
                "--mode",
                mode,
            ],
            false,
        );
        let diagnostic = format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        // Only a host without a working sandbox may reject untrusted mode earlier.
        let gated = mode == "untrusted" && !sandbox_available();
        assert!(
            diagnostic.contains(if gated { "bubblewrap" } else { "is missing" }),
            "{mode}: {diagnostic}"
        );
        assert!(!marker.exists(), "{mode}: a repository Git helper ran");
    }
}

// A clean filter defined ONLY in an initialized submodule's own config (directly, or through
// an `include.path` there) is invisible to the superproject. Plain `git status` recurses into
// the submodule and runs it on the host; pr-verify must never do so.
#[test]
fn submodule_only_filters_never_run_during_pr_verification() {
    for via_include in [false, true] {
        let f = Fixture(std::env::temp_dir().join(format!(
            "turbo-submodule-filter-{}-{}",
            std::process::id(),
            SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()
        )));
        let (sub, proj) = (f.0.join(".sub-origin"), f.0.join("proj"));
        let marker = f.0.join("shim-invoked");
        fs::create_dir_all(&sub).unwrap();
        fs::create_dir_all(&proj).unwrap();
        let plain = |dir: &Path, args: &[&str]| {
            Command::new("/usr/bin/git")
                .env_clear()
                .env("PATH", "/usr/bin:/bin")
                .env("HOME", &f.0)
                .env("GIT_CONFIG_NOSYSTEM", "1")
                .args(["-c", "user.name=T", "-c", "user.email=t@e"])
                .args(["-c", "protocol.file.allow=always"])
                .current_dir(dir)
                .args(args)
                .output()
                .unwrap()
        };
        let ok = |dir: &Path, args: &[&str]| {
            let out = plain(dir, args);
            assert!(out.status.success(), "{args:?}: {out:?}");
            String::from_utf8(out.stdout).unwrap().trim().to_string()
        };
        ok(&sub, &["init", "-q"]);
        fs::write(sub.join(".gitattributes"), "*.txt filter=subattack\n").unwrap();
        fs::write(sub.join("data.txt"), "a\n").unwrap();
        ok(&sub, &["add", "."]);
        ok(&sub, &["commit", "-qm", "sub"]);
        ok(&f.0, &["init", "-q"]);
        fs::write(
            f.0.join(".gitignore"),
            ".sub-origin/\n.lake/\ncache*/\nproj/.lake/\nproj/cache*/\n",
        )
        .unwrap();
        for dir in [&f.0, &proj] {
            fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
            fs::write(dir.join("Demo.lean"), "theorem pinned : 1 + 1 = 2 := rfl\n").unwrap();
        }
        ok(&f.0, &["add", "."]);
        ok(&f.0, &["commit", "-qm", "base"]);
        ok(
            &f.0,
            &["submodule", "add", "-q", &sub.to_string_lossy(), "dep"],
        );
        ok(&f.0, &["commit", "-qm", "dep"]);
        let base = ok(&f.0, &["rev-parse", "HEAD"]);
        let dep = f.0.join("dep");
        let filter = format!("touch '{}'; cat", marker.display());
        if via_include {
            let inc = f.0.join(".sub-origin/include");
            ok(
                &f.0,
                &[
                    "config",
                    "--file",
                    &inc.to_string_lossy(),
                    "filter.subattack.clean",
                    &filter,
                ],
            );
            ok(&dep, &["config", "include.path", &inc.to_string_lossy()]);
        } else {
            ok(&dep, &["config", "filter.subattack.clean", &filter]);
        }
        // A repository setting that would otherwise force Git to inspect the submodule.
        ok(&f.0, &["config", "submodule.dep.ignore", "none"]);
        let mut stamp = 0u64;
        let mut restat = || {
            stamp += 1;
            // Same size as the committed blob: only the clean filter can tell it changed.
            fs::write(dep.join("data.txt"), "b\n").unwrap();
            fs::File::options()
                .append(true)
                .open(dep.join("data.txt"))
                .unwrap()
                .set_modified(SystemTime::now() + Duration::from_secs(stamp))
                .unwrap();
        };
        assert_eq!(
            plain(&f.0, &["config", "--get", "filter.subattack.clean"])
                .status
                .code(),
            Some(1),
            "filter must be unseen in the superproject"
        );
        // Positive control: plain status runs the submodule-only filter on the host.
        restat();
        ok(&f.0, &["status", "--porcelain"]);
        assert!(
            marker.exists(),
            "{via_include}: submodule filter control did not run"
        );
        fs::remove_file(&marker).unwrap();

        fs::write(
            f.0.join("Demo.lean"),
            "theorem pinned : 1 + 1 = 2 := by decide\n",
        )
        .unwrap();
        fs::write(
            proj.join("Demo.lean"),
            "theorem pinned : 1 + 1 = 2 := by decide\n",
        )
        .unwrap();
        for base_ref in ["HEAD", base.as_str()] {
            // Both the project containing the gitlink and a sibling project of the same
            // repository are refused: a gitlink's contents are never inspected, by change
            // discovery (root) or by the raw statement snapshot of the whole tree (sibling).
            for (dir, cache) in [(".", "cache"), ("proj", "cache-proj")] {
                restat();
                let out = f.run(
                    cache,
                    &["pr-verify", "--project-dir", dir, "--base", base_ref],
                    false,
                );
                let diagnostic = format!(
                    "{}{}",
                    String::from_utf8_lossy(&out.stdout),
                    String::from_utf8_lossy(&out.stderr)
                );
                assert!(
                    diagnostic.contains("gitlinks"),
                    "{dir} {base_ref}: {diagnostic}"
                );
                assert!(
                    !marker.exists(),
                    "{via_include} {dir} {base_ref}: filter ran"
                );
            }
        }
    }
}
