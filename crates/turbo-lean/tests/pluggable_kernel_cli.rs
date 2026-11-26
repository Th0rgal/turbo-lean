use serde_json::Value;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

mod c_abi {
    pub fn route_kernel_engine(requested_engine: u8, con_leche_supported: bool) -> u8 {
        match (requested_engine, con_leche_supported) {
            (0, false) => 1,
            (0, true) => 2,
            (1, _) => 1,
            (2, true) => 2,
            (2, false) => 0,
            (3, true) => 3,
            (3, false) => 0,
            _ => 0,
        }
    }
}

mod lake_build {
    use std::path::Path;
    pub fn detect_toolchain(project_dir: &Path) -> String {
        std::fs::read_to_string(project_dir.join("lean-toolchain"))
            .map(|s| s.trim().to_string())
            .unwrap_or_else(|_| "unknown".to_string())
    }
}

mod pack {
    pub mod tests {
        // Stub matching `crate::pack::tests::env_test_lock()` so the #[path]-included
        // `kernel.rs` tests module compiles in this integration crate. The env-mutating
        // integration tests below take the same lock, so included and local tests that
        // touch process env serialize against each other.
        pub fn env_test_lock() -> &'static std::sync::Mutex<()> {
            static LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
            &LOCK
        }
    }
}

mod trusted_tools {
    // Stub matching `crate::trusted_tools::git(...)` so the #[path]-included `kernel.rs`
    // compiles in this integration crate; the fixtures here are repo-local temp checkouts,
    // so the PATH `git` is the right tool for them.
    pub fn git(_project: &std::path::Path) -> anyhow::Result<std::process::Command> {
        Ok(std::process::Command::new("git"))
    }
}

#[allow(dead_code)]
#[path = "../src/kernel.rs"]
mod kernel;

struct KernelTestFixture {
    root: PathBuf,
}

impl KernelTestFixture {
    fn new(name: &str) -> Self {
        let root = std::env::temp_dir().join(format!(
            "turbo_pluggable_kernel_{}_{}_{}",
            name,
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir_all(&root).unwrap();
        Self { root }
    }

    fn git_bin() -> String {
        std::env::var("TURBO_LEAN_GIT").unwrap_or_else(|_| "git".to_string())
    }

    fn run_git(&self, repo: &Path, args: &[&str]) {
        let out = Command::new(Self::git_bin())
            .current_dir(repo)
            .args(args)
            .env("GIT_AUTHOR_NAME", "Test User")
            .env("GIT_AUTHOR_EMAIL", "test@example.com")
            .env("GIT_COMMITTER_NAME", "Test User")
            .env("GIT_COMMITTER_EMAIL", "test@example.com")
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "git {args:?} failed:\n{}\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
    }

    fn cli(&self, cache_tag: &str) -> Command {
        let cache_dir = self.root.join(format!("cache-{cache_tag}"));
        let staging_dir = self.root.join(format!("staging-{cache_tag}"));
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_turbo-lean"));
        cmd.current_dir(&self.root)
            .env("TURBO_LEAN_HOME", &cache_dir)
            .env("TURBO_LEAN_STAGING_DIR", &staging_dir)
            .env("TURBO_LEAN_NO_DAEMON", "1")
            .env("TURBO_LEAN_TELEMETRY", "off")
            .env("TURBO_LEAN_NO_REMOTE_TELEMETRY", "1")
            .env_remove("TURBO_LEAN_KERNEL_ENGINE")
            .env_remove("TURBO_LEAN_KERNEL_ENGINE_FROM_CONFIG");
        cmd
    }
}

impl Drop for KernelTestFixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

fn assert_ok(out: &Output, ctx: &str) {
    assert!(
        out.status.success(),
        "{ctx} expected success, failed with {:?}:\nstdout:\n{}\nstderr:\n{}",
        out.status.code(),
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
}

fn assert_err(out: &Output, ctx: &str) {
    assert!(
        !out.status.success(),
        "{ctx} expected failure, succeeded:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn check_kernel_precedence_fail_closed_and_json_provenance() {
    let f = KernelTestFixture::new("check");
    let proj = f.root.join("proj");
    fs::create_dir_all(&proj).unwrap();
    let toolchain = include_str!("../../../lean/lean-toolchain").trim();
    fs::write(proj.join("lean-toolchain"), format!("{toolchain}\n")).unwrap();
    fs::write(proj.join("Sample.lean"), "theorem t1 : 1 + 1 = 2 := rfl\n").unwrap();

    // 1. Default `--kernel auto` resolves to `standard` with full provenance in `--json`.
    fs::write(
        proj.join("turbo-lean.toml"),
        "[kernel]\nengine = \"standard\"\n",
    )
    .unwrap();
    let std_cfg_out = f
        .cli("c0")
        .args([
            "--json",
            "check",
            proj.join("Sample.lean").to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_ok(&std_cfg_out, "check with [kernel] engine = \"standard\"");
    let v_std_cfg: Value = serde_json::from_slice(&std_cfg_out.stdout).unwrap();
    assert_eq!(v_std_cfg["kernel_engine"], "standard");
    assert_eq!(v_std_cfg["kernel_requested"], "standard");
    fs::remove_file(proj.join("turbo-lean.toml")).unwrap();

    let out = f
        .cli("c1")
        .args([
            "--json",
            "check",
            proj.join("Sample.lean").to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_ok(&out, "default check");
    let v: Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(v["kernel_engine"], "standard");
    assert_eq!(v["kernel_requested"], "auto");
    assert_eq!(v["lean_toolchain"], toolchain);
    assert!(v["con_leche_rev"].is_null());

    // 2. Explicit `--kernel con-leche` and `--kernel both` fail closed when unbundled.
    for req in ["con-leche", "con_leche", "both", "bogus"] {
        let bad_out = f
            .cli("c2")
            .args([
                "--json",
                "check",
                "--kernel",
                req,
                proj.join("Sample.lean").to_str().unwrap(),
            ])
            .output()
            .unwrap();
        assert_err(&bad_out, &format!("check --kernel {req}"));
    }

    // 3. `[kernel] engine = "con-leche"` in `turbo-lean.toml` fails closed by default,
    //    is overridden by `TURBO_LEAN_KERNEL_ENGINE=standard`, and CLI `--kernel` wins over env.
    fs::write(
        proj.join("turbo-lean.toml"),
        "[kernel]\nengine = \"con-leche\"\n",
    )
    .unwrap();
    let cfg_fail = f
        .cli("c3")
        .args([
            "--json",
            "check",
            proj.join("Sample.lean").to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_err(&cfg_fail, "check with [kernel] engine = con-leche");

    let env_override = f
        .cli("c3")
        .env("TURBO_LEAN_KERNEL_ENGINE", "standard")
        .args([
            "--json",
            "check",
            proj.join("Sample.lean").to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_ok(&env_override, "env overrides config");
    let v_env: Value = serde_json::from_slice(&env_override.stdout).unwrap();
    assert_eq!(v_env["kernel_engine"], "standard");
    assert_eq!(v_env["kernel_requested"], "standard");

    let cli_over_env = f
        .cli("c3")
        .env("TURBO_LEAN_KERNEL_ENGINE", "con-leche")
        .args([
            "--json",
            "check",
            "--kernel",
            "standard",
            proj.join("Sample.lean").to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_ok(&cli_over_env, "CLI --kernel overrides env");
    let v_cli: Value = serde_json::from_slice(&cli_over_env.stdout).unwrap();
    assert_eq!(v_cli["kernel_engine"], "standard");
    assert_eq!(v_cli["kernel_requested"], "standard");
    fs::remove_file(proj.join("turbo-lean.toml")).unwrap();

    // 4. Outer sentinel `lean-toolchain` in CWD (`f.root`) must NOT shadow `proj/lean-toolchain`
    //    when invoking `check` without `--project-dir` on relative/absolute file, `--decl`, or dir.
    fs::write(
        f.root.join("lean-toolchain"),
        "leanprover/lean4:v4.0.0-outer-sentinel\n",
    )
    .unwrap();
    for (tag, args) in [
        ("c4_rel", vec!["--json", "check", "proj/Sample.lean"]),
        (
            "c4_abs",
            vec![
                "--json",
                "check",
                proj.join("Sample.lean").to_str().unwrap(),
            ],
        ),
        (
            "c4_decl",
            vec!["--json", "check", "proj/Sample.lean", "--decl", "t1"],
        ),
        ("c4_dir", vec!["--json", "check", "proj"]),
    ] {
        let nested_out = f.cli(tag).args(&args).output().unwrap();
        assert_ok(&nested_out, tag);
        let v_nested: Value = serde_json::from_slice(&nested_out.stdout).unwrap();
        assert_eq!(v_nested["kernel_engine"], "standard");
        assert_eq!(v_nested["lean_toolchain"], toolchain);
        assert_ne!(
            v_nested["lean_toolchain"],
            "leanprover/lean4:v4.0.0-outer-sentinel"
        );
    }
    assert!(!f.root.join(".lake").exists());
}

#[test]
fn pr_and_ci_verify_base_policy_isolation_and_receipt_verification() {
    let f = KernelTestFixture::new("pr_ci");
    let repo = f.root.join("repo");
    fs::create_dir_all(&repo).unwrap();
    let toolchain = include_str!("../../../lean/lean-toolchain").trim();

    f.run_git(&repo, &["init", "-b", "main"]);
    fs::write(repo.join("lean-toolchain"), format!("{toolchain}\n")).unwrap();
    fs::write(
        repo.join("lakefile.toml"),
        "name = \"demo\"\ndefaultTargets = [\"Demo\"]\n[[lean_lib]]\nname = \"Demo\"\n",
    )
    .unwrap();
    fs::write(
        repo.join("turbo-lean.toml"),
        "[kernel]\nengine = \"standard\"\n",
    )
    .unwrap();
    fs::write(
        repo.join("Demo.lean"),
        "theorem sample (n : Nat) : n + 0 = n := by simp\n",
    )
    .unwrap();
    f.run_git(&repo, &["add", "."]);
    f.run_git(&repo, &["commit", "-m", "base commit"]);

    // Create an untrusted PR branch that mutates `turbo-lean.toml` to an invalid/unsupported engine
    // and edits a proof body.
    f.run_git(&repo, &["checkout", "-b", "pr-branch"]);
    fs::write(
        repo.join("turbo-lean.toml"),
        "[kernel]\nengine = \"not-a-valid-engine\"\n",
    )
    .unwrap();
    fs::write(
        repo.join("Demo.lean"),
        "theorem sample (n : Nat) : n + 0 = n := Nat.add_zero n\n",
    )
    .unwrap();
    f.run_git(&repo, &["add", "."]);
    f.run_git(&repo, &["commit", "-m", "untrusted pr edit"]);

    // 1. `ci-verify` without `--base` ignores checkout `turbo-lean.toml` AND inherited FROM_CONFIG=1,
    //    emitting a valid receipt with kernel provenance.
    let ci_receipt_path = f.root.join("ci-receipt.json");
    let ci_out = f
        .cli("ci")
        .env("TURBO_LEAN_KERNEL_ENGINE", "con-leche")
        .env("TURBO_LEAN_KERNEL_ENGINE_FROM_CONFIG", "1")
        .args([
            "--json",
            "ci-verify",
            "--project-dir",
            repo.to_str().unwrap(),
            "--mode",
            "trusted",
            "--receipt",
            ci_receipt_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_ok(&ci_out, "ci-verify without --base ignores checkout config");
    let ci_json: Value = serde_json::from_slice(&ci_out.stdout).unwrap();
    assert_eq!(ci_json["kernel_requested"], "auto");
    assert_eq!(ci_json["lean_toolchain"], toolchain);
    // Host-honest resolved-engine assertion (G1c r2; DA 388e906a F7): computed by the REAL
    // selection probe through the #[path]-included kernel module, under the same environment
    // the CLI child sees (`ELAN_HOME`, `HOME` and `TURBO_CON_LECHE_BIN` reach both), so this
    // test cannot drift from the resolver the way a hand-rolled copy did. A capable bundled
    // binary records the probed-capability marker, never the unverified pinned rev.
    match kernel::probe_con_leche_support_for_selection(
        kernel::KernelEngineSelection::Auto,
        toolchain,
        Some(&repo),
    ) {
        Some(expected_rev) => {
            assert_eq!(ci_json["kernel_engine"], "con-leche");
            assert_eq!(ci_json["con_leche_rev"], expected_rev);
        }
        None => {
            assert_eq!(ci_json["kernel_engine"], "standard");
            assert!(ci_json["con_leche_rev"].is_null());
        }
    }

    // Explicit caller env (without FROM_CONFIG=1) in `ci-verify` without `--base` still applies and fails closed.
    let ci_env_fail = f
        .cli("ci")
        .env("TURBO_LEAN_KERNEL_ENGINE", "con-leche")
        .args([
            "--json",
            "ci-verify",
            "--project-dir",
            repo.to_str().unwrap(),
            "--mode",
            "trusted",
        ])
        .output()
        .unwrap();
    assert_err(
        &ci_env_fail,
        "ci-verify explicit caller env con-leche fails closed",
    );

    // 2. `pr-verify --base main` reads `[kernel] engine = "standard"` from `main`, ignoring the
    //    malicious `not-a-valid-engine` on `pr-branch`.
    let pr_receipt_path = f.root.join("pr-receipt.json");
    let pr_out = f
        .cli("ci")
        .args([
            "--json",
            "pr-verify",
            "--project-dir",
            repo.to_str().unwrap(),
            "--base",
            "main",
            "--mode",
            "trusted",
            "--receipt",
            pr_receipt_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_ok(&pr_out, "pr-verify reads [kernel] engine at --base");
    let pr_json: Value = serde_json::from_slice(&pr_out.stdout).unwrap();
    assert_eq!(pr_json["kernel_engine"], "standard");
    assert_eq!(pr_json["kernel_requested"], "standard");
    assert_eq!(pr_json["lean_toolchain"], toolchain);
    assert!(pr_json["con_leche_rev"].is_null());

    // Explicit `--kernel both` on `pr-verify` fails closed and does NOT write a receipt.
    let missing_receipt = f.root.join("must-not-exist-receipt.json");
    let pr_both_fail = f
        .cli("ci")
        .args([
            "--json",
            "pr-verify",
            "--project-dir",
            repo.to_str().unwrap(),
            "--base",
            "main",
            "--mode",
            "trusted",
            "--kernel",
            "both",
            "--receipt",
            missing_receipt.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_err(&pr_both_fail, "pr-verify --kernel both fails closed");
    assert!(!missing_receipt.exists());

    // 3. `verify-receipt` succeeds on valid v2 receipts and fails closed on tampered provenance.
    let pr_rec_val: Value = serde_json::from_slice(&fs::read(&pr_receipt_path).unwrap()).unwrap();
    assert_eq!(pr_rec_val["schema_version"], 2);
    let vr_ok = f
        .cli("vr")
        .args([
            "--json",
            "verify-receipt",
            pr_receipt_path.to_str().unwrap(),
            "--baseline-receipt",
            ci_receipt_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_ok(&vr_ok, "verify-receipt on valid pr+ci receipts");
    let vr_json: Value = serde_json::from_slice(&vr_ok.stdout).unwrap();
    assert_eq!(vr_json["status"], "receipt_verified");
    assert_eq!(vr_json["schema_version"], 2);
    assert_eq!(vr_json["kernel_engine"], "standard");
    assert_eq!(vr_json["lean_toolchain"], toolchain);
    assert!(vr_json["con_leche_rev"].is_null());

    // Legacy `schema_version = 1` receipts remain verifiable standalone AND as `--baseline-receipt`
    // for a `schema_version = 2` receipt.
    let per_file = pr_rec_val["per_file_interfaces"].as_object().unwrap();
    let mut v1_payload = format!(
        "turbo-lean-verification-receipt-v1\nschema_version:1\nmode:{}\ninterface_hash:{}\naction_key:legacy-v1-act\nfiles_audited:{}\ntheorem_shards:{}\nforbidden_constructs_found:0\n",
        pr_rec_val["mode"].as_str().unwrap(),
        pr_rec_val["interface_hash"].as_str().unwrap(),
        pr_rec_val["files_audited"].as_u64().unwrap(),
        pr_rec_val["theorem_shards"].as_u64().unwrap(),
    );
    for (rel_path, ih_val) in per_file {
        v1_payload.push_str(&format!("file:{rel_path}={}\n", ih_val.as_str().unwrap()));
    }
    let v1_blake3 = blake3::hash(v1_payload.as_bytes()).to_hex().to_string();
    let legacy_v1_path = f.root.join("legacy-v1-receipt.json");
    let legacy_v1_json = serde_json::json!({
        "schema_version": 1,
        "mode": pr_rec_val["mode"],
        "interface_hash": pr_rec_val["interface_hash"],
        "action_key": "legacy-v1-act",
        "files_audited": pr_rec_val["files_audited"],
        "theorem_shards": pr_rec_val["theorem_shards"],
        "forbidden_constructs_found": 0,
        "per_file_interfaces": pr_rec_val["per_file_interfaces"],
        "receipt_blake3": v1_blake3,
    });
    fs::write(
        &legacy_v1_path,
        serde_json::to_vec_pretty(&legacy_v1_json).unwrap(),
    )
    .unwrap();
    let vr_v1_ok = f
        .cli("vr")
        .args(["--json", "verify-receipt", legacy_v1_path.to_str().unwrap()])
        .output()
        .unwrap();
    assert_ok(&vr_v1_ok, "verify-receipt accepts legacy v1 receipt");
    let vr_v1_json: Value = serde_json::from_slice(&vr_v1_ok.stdout).unwrap();
    assert_eq!(vr_v1_json["status"], "receipt_verified");
    assert_eq!(vr_v1_json["schema_version"], 1);
    assert!(vr_v1_json["kernel_engine"].is_null());
    assert!(vr_v1_json["lean_toolchain"].is_null());
    assert!(vr_v1_json["con_leche_rev"].is_null());

    let vr_v2_vs_v1_base = f
        .cli("vr")
        .args([
            "--json",
            "verify-receipt",
            pr_receipt_path.to_str().unwrap(),
            "--baseline-receipt",
            legacy_v1_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_ok(
        &vr_v2_vs_v1_base,
        "verify-receipt accepts legacy v1 baseline for v2 receipt",
    );

    // Tamper `lean_toolchain` without recomputing `receipt_blake3` -> BLAKE3 mismatch rejected.
    let mut tampered: Value = serde_json::from_slice(&fs::read(&pr_receipt_path).unwrap()).unwrap();
    tampered["lean_toolchain"] = Value::String("leanprover/lean4:v4.28.0".to_string());
    let tampered_path = f.root.join("tampered-receipt.json");
    fs::write(
        &tampered_path,
        serde_json::to_vec_pretty(&tampered).unwrap(),
    )
    .unwrap();
    let vr_tampered = f
        .cli("vr")
        .args(["--json", "verify-receipt", tampered_path.to_str().unwrap()])
        .output()
        .unwrap();
    assert_err(
        &vr_tampered,
        "verify-receipt rejects tampered lean_toolchain",
    );

    // Provenance invariant violation (`standard` with non-null `con_leche_rev`) fails closed.
    let mut bad_inv: Value = serde_json::from_slice(&fs::read(&pr_receipt_path).unwrap()).unwrap();
    bad_inv["con_leche_rev"] = Value::String("deadbeef".to_string());
    let bad_inv_path = f.root.join("bad-inv-receipt.json");
    fs::write(&bad_inv_path, serde_json::to_vec_pretty(&bad_inv).unwrap()).unwrap();
    let vr_bad_inv = f
        .cli("vr")
        .args(["--json", "verify-receipt", bad_inv_path.to_str().unwrap()])
        .output()
        .unwrap();
    assert_err(
        &vr_bad_inv,
        "verify-receipt rejects standard + con_leche_rev",
    );

    // 4. If `--base` itself sets `[kernel] engine = "con-leche"`, `pr-verify --base` fails closed.
    f.run_git(&repo, &["checkout", "main"]);
    fs::write(
        repo.join("turbo-lean.toml"),
        "[kernel]\nengine = \"con-leche\"\n",
    )
    .unwrap();
    f.run_git(&repo, &["add", "turbo-lean.toml"]);
    f.run_git(&repo, &["commit", "-m", "base requires con-leche"]);
    f.run_git(&repo, &["checkout", "pr-branch"]);
    fs::write(
        repo.join("turbo-lean.toml"),
        "[kernel]\nengine = \"standard\"\n",
    )
    .unwrap();
    f.run_git(&repo, &["add", "turbo-lean.toml"]);
    f.run_git(
        &repo,
        &["commit", "-m", "pr tries to downgrade to standard"],
    );

    let pr_downgrade_attempt = f
        .cli("ci")
        .args([
            "--json",
            "pr-verify",
            "--project-dir",
            repo.to_str().unwrap(),
            "--base",
            "main",
            "--mode",
            "trusted",
        ])
        .output()
        .unwrap();
    assert_err(
        &pr_downgrade_attempt,
        "pr-verify cannot downgrade base [kernel] engine = con-leche",
    );
}

#[cfg(unix)]
fn write_executable_script(path: &Path, body: &str) {
    use std::os::unix::fs::PermissionsExt;
    fs::write(path, body).unwrap();
    let mut perms = fs::metadata(path).unwrap().permissions();
    perms.set_mode(0o755);
    fs::set_permissions(path, perms).unwrap();
}

/// G1b: compile `<module>.lean` in `dir` into a REAL `<module>.olean` with the repo's pinned
/// toolchain, so the con-leche verification path is tested over real compiled artifacts and
/// never over synthesized `.olean` bytes or an empty search path. Returns `None` (after
/// printing a skip message) when no runnable Lean toolchain (`elan` or `lean`) is on PATH;
/// a toolchain that is present but fails to compile is still a hard test failure.
#[cfg(unix)]
fn compile_real_olean_module(dir: &Path, module: &str) -> Option<PathBuf> {
    let toolchain = include_str!("../../../lean/lean-toolchain").trim();
    fs::write(dir.join("lean-toolchain"), format!("{toolchain}\n")).unwrap();
    // Locate the pinned `lean` cleanly even when no elan default toolchain is configured.
    let lean_bin = Command::new("elan")
        .current_dir(dir)
        .args(["which", "lean"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| PathBuf::from(String::from_utf8_lossy(&o.stdout).trim()))
        .unwrap_or_else(|| PathBuf::from("lean"));
    // Review finding 7: skip (never panic) when neither `elan` nor `lean` resolves to a
    // runnable toolchain on this host.
    match Command::new(&lean_bin)
        .current_dir(dir)
        .arg("--version")
        .output()
    {
        Ok(v) if v.status.success() => {}
        _ => {
            eprintln!(
                "no runnable Lean toolchain (`elan`/`lean`) on PATH; cannot compile a real `{module}.olean`"
            );
            return None;
        }
    }
    let src = dir.join(format!("{module}.lean"));
    fs::write(
        &src,
        "module\nprelude\npublic section\ninductive Yes : Prop where\n  | intro\ntheorem yes : Yes := Yes.intro\nend\n",
    )
    .unwrap();
    let olean = dir.join(format!("{module}.olean"));
    let out = Command::new(&lean_bin)
        .current_dir(dir)
        .args([
            "-R",
            dir.to_str().unwrap(),
            "-o",
            olean.to_str().unwrap(),
            src.to_str().unwrap(),
        ])
        .output()
        .expect("`lean --version` succeeded, so spawning the compile must too");
    assert!(
        out.status.success(),
        "compile {module}.lean with the pinned `lean` failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    Some(olean)
}

#[cfg(unix)]
#[test]
fn con_leche_exit_code_protocol_and_verified_cli_flags() {
    // Held across every child spawn and in-process probe below: this test mutates process
    // env (MOCK_CODE), and the included `kernel.rs` tests mutate the same process env.
    let _env_guard = pack::tests::env_test_lock().lock().unwrap();
    let f = KernelTestFixture::new("con_leche_runner");
    let mock_bin = f.root.join("mock-con-leche.sh");
    let args_log = f.root.join("args.log");
    let sp_dir = f.root.join("oleans");
    let scratch_dir = f.root.join("scratch-tmp");
    fs::create_dir_all(&sp_dir).unwrap();
    fs::create_dir_all(&scratch_dir).unwrap();
    // Review finding 7: skip with a message instead of panicking on a toolchain-less host.
    if compile_real_olean_module(&sp_dir, "DemoMod").is_none() {
        eprintln!(
            "skipping con_leche_exit_code_protocol_and_verified_cli_flags: no Lean toolchain on PATH"
        );
        return;
    }

    // G1b: the con-leche verification path is exercised over a REAL compiled `.olean`
    // artifact produced by the pinned toolchain — never an empty or synthesized search path.
    let demo_olean = sp_dir.join("DemoMod.olean");
    let demo_bytes = fs::read(&demo_olean).unwrap_or_else(|e| {
        panic!(
            "G1b: expected a real compiled DemoMod.olean on the con-leche search path at {}: {e}",
            demo_olean.display()
        )
    });
    assert!(demo_bytes.len() > 5, "real DemoMod.olean must be non-empty");
    assert_eq!(&demo_bytes[..5], &b"olean"[..], "real Lean 4 `.olean` magic");
    assert_ne!(
        &demo_bytes[..4],
        &[0x4Fu8, 0x4C, 0x45, 0x4E][..],
        "a real `.olean` is not an OLEN v1 model shard"
    );

    write_executable_script(
        &mock_bin,
        &format!(
            "#!/usr/bin/env bash\nprintf '%s\\n' \"$@\" > \"{}\"\nprintf 'TMPDIR=%s\\n' \"$TMPDIR\" >> \"{}\"\nsp=\nfor a in \"$@\"; do case \"$a\" in --search-path=*) sp=\"${{a#--search-path=}}\";; esac; done\nif [ -n \"$sp\" ] && [ -f \"$sp/DemoMod.olean\" ]; then printf 'OLEAN_SHA256=%s\\n' \"$(sha256sum \"$sp/DemoMod.olean\" | cut -d' ' -f1)\" >> \"{}\"; fi\ncase \"$MOCK_CODE\" in\n  0)\n    echo 'con-leche: accepted 42 declarations (--verified)'\n    exit 0\n    ;;\n  1)\n    echo 'con-leche: rejected: invalid declaration' >&2\n    exit 1\n    ;;\n  2)\n    echo 'con-leche: declined: unsupported feature' >&2\n    exit 2\n    ;;\n  3)\n    echo 'con-leche: usage/internal error' >&2\n    exit 3\n    ;;\n  134)\n    echo 'con-leche: panic abort' >&2\n    exit 134\n    ;;\n  sigabrt)\n    kill -ABRT $$\n    ;;\nesac\n",
            args_log.display(),
            args_log.display(),
            args_log.display()
        ),
    );

    let resolved_mock = kernel::ResolvedConLecheBinary::resolve(
        &mock_bin,
        kernel::ConLecheBinaryProvenance::ProvisionedPinnedRev,
    )
    .unwrap();
    let search_paths = vec![sp_dir.clone()];
    let roots = vec!["DemoMod".to_string()];

    // Exit 0 -> Accepted, parses declaration count, passes --verified and never --trusted.
    std::env::set_var("MOCK_CODE", "0");
    let rep_ok = kernel::verify_olean_modules_with_con_leche(
        &resolved_mock,
        &search_paths,
        &roots,
        &["DemoMod.thm".to_string()],
        Some(99),
        Some(&scratch_dir),
    )
    .unwrap();
    assert_eq!(rep_ok.verdict, kernel::ConLecheVerdict::Accepted);
    assert_eq!(rep_ok.exit_code, 0);
    assert_eq!(rep_ok.con_leche_rev, kernel::PINNED_CON_LECHE_REV);
    assert_eq!(rep_ok.jobs, kernel::DEFAULT_MAX_CON_LECHE_JOBS);
    assert_eq!(rep_ok.accepted_declarations, Some(42));
    let logged = fs::read_to_string(&args_log).unwrap();
    assert!(logged.lines().any(|l| l == "--verified"), "{logged}");
    assert!(!logged.contains("--trusted"), "{logged}");
    assert!(
        logged
            .lines()
            .any(|l| l == format!("--jobs={}", kernel::DEFAULT_MAX_CON_LECHE_JOBS)),
        "{logged}"
    );
    assert!(logged.lines().any(|l| l == "--olean"), "{logged}");
    assert!(
        logged.lines().any(|l| l == "--constant=DemoMod.thm"),
        "{logged}"
    );
    assert!(
        logged
            .lines()
            .any(|l| l == format!("TMPDIR={}", scratch_dir.display())),
        "{logged}"
    );
    // G1b (review finding 7): the engine under test consumed the compiled artifact — the
    // mock read `DemoMod.olean` off its `--search-path` and hashed it, and the hash must
    // match the bytes the test compiled.
    let demo_sha256 = {
        use sha2::Digest as _;
        let mut h = sha2::Sha256::new();
        h.update(&demo_bytes);
        h.finalize()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>()
    };
    assert!(
        logged
            .lines()
            .any(|l| l == format!("OLEAN_SHA256={demo_sha256}")),
        "{logged}"
    );

    // Exit 1 -> Rejected
    std::env::set_var("MOCK_CODE", "1");
    let rep_rej = kernel::verify_olean_modules_with_con_leche(
        &resolved_mock,
        &search_paths,
        &roots,
        &[],
        Some(2),
        Some(&scratch_dir),
    )
    .unwrap();
    assert_eq!(rep_rej.verdict, kernel::ConLecheVerdict::Rejected);
    assert_eq!(rep_rej.exit_code, 1);
    assert_eq!(rep_rej.accepted_declarations, None);

    // Exit 2 -> Declined
    std::env::set_var("MOCK_CODE", "2");
    let rep_dec = kernel::verify_olean_modules_with_con_leche(
        &resolved_mock,
        &search_paths,
        &roots,
        &[],
        Some(2),
        Some(&scratch_dir),
    )
    .unwrap();
    assert_eq!(rep_dec.verdict, kernel::ConLecheVerdict::Declined);
    assert_eq!(rep_dec.exit_code, 2);

    // Exit 3, 134, and SIGABRT -> fail-closed Err
    for fatal_mode in ["3", "134", "sigabrt"] {
        std::env::set_var("MOCK_CODE", fatal_mode);
        let err = kernel::verify_olean_modules_with_con_leche(
            &resolved_mock,
            &search_paths,
            &roots,
            &[],
            Some(2),
            Some(&scratch_dir),
        )
        .unwrap_err();
        let msg = err.to_string();
        assert!(
            msg.contains("exit 3") || msg.contains("134") || msg.contains("signal"),
            "unexpected error for {fatal_mode}: {msg}"
        );
    }
    std::env::remove_var("MOCK_CODE");

    // NDJSON invocation also enforces --verified and fails closed on missing input.
    let ndjson_path = f.root.join("sample.ndjson");
    fs::write(&ndjson_path, "{}\n").unwrap();
    std::env::set_var("MOCK_CODE", "0");
    let nd_ok = kernel::verify_ndjson_with_con_leche(
        &resolved_mock,
        &ndjson_path,
        Some(2),
        Some(&scratch_dir),
    )
    .unwrap();
    assert_eq!(nd_ok.verdict, kernel::ConLecheVerdict::Accepted);
    std::env::remove_var("MOCK_CODE");
}

#[cfg(unix)]
#[test]
fn ci_verify_executes_con_leche_on_olean_closure_and_rejects_checkout_binary() {
    let f = KernelTestFixture::new("ci_con_leche");
    let repo = f.root.join("repo");
    fs::create_dir_all(&repo).unwrap();
    let toolchain = include_str!("../../../lean/lean-toolchain").trim();

    f.run_git(&repo, &["init", "-b", "main"]);
    fs::write(repo.join("lean-toolchain"), format!("{toolchain}\n")).unwrap();
    fs::write(
        repo.join("lakefile.toml"),
        "name = \"demo\"\ndefaultTargets = [\"Demo\"]\n[[lean_lib]]\nname = \"Demo\"\n",
    )
    .unwrap();
    fs::write(
        repo.join("Demo.lean"),
        "theorem sample : 1 + 1 = 2 := rfl\n",
    )
    .unwrap();
    f.run_git(&repo, &["add", "."]);
    f.run_git(&repo, &["commit", "-m", "initial"]);

    let args_log = f.root.join("ci-con-leche-args.log");
    let mock_bin = f.root.join("external-con-leche.sh");
    write_executable_script(
        &mock_bin,
        &format!(
            "#!/usr/bin/env bash\nprintf '%s\\n' \"$@\" > \"{}\"\ncase \"${{CI_CON_LECHE_CODE:-0}}\" in\n  0)\n    echo 'con-leche: accepted 7 declarations (--verified)'\n    exit 0\n    ;;\n  1)\n    echo 'con-leche: rejected: adversarial olean' >&2\n    exit 1\n    ;;\n  2)\n    echo 'con-leche: declined: unsupported feature' >&2\n    exit 2\n    ;;\nesac\n",
            args_log.display()
        ),
    );

    // 1. `ci-verify --kernel con-leche` and `--kernel both` execute `con-leche --verified --olean`
    //    on the built `.olean` closure and emit valid v2 receipts with `con_leche_rev`.
    for (tag, req_engine) in [("cl_only", "con-leche"), ("cl_both", "both")] {
        let receipt_path = f.root.join(format!("receipt-{tag}.json"));
        let out = f
            .cli(tag)
            .env(kernel::CON_LECHE_BIN_ENV, &mock_bin)
            .env("CI_CON_LECHE_CODE", "0")
            .args([
                "--json",
                "ci-verify",
                "--project-dir",
                repo.to_str().unwrap(),
                "--mode",
                "trusted",
                "--kernel",
                req_engine,
                "--receipt",
                receipt_path.to_str().unwrap(),
            ])
            .output()
            .unwrap();
        assert_ok(&out, &format!("ci-verify --kernel {req_engine}"));
        let v: Value = serde_json::from_slice(&out.stdout).unwrap();
        assert_eq!(v["kernel_engine"], req_engine);
        assert_eq!(v["kernel_requested"], req_engine);
        assert_eq!(v["lean_toolchain"], toolchain);
        assert_eq!(v["con_leche_rev"], kernel::PINNED_CON_LECHE_REV);

        let logged = fs::read_to_string(&args_log).unwrap();
        assert!(logged.lines().any(|l| l == "--verified"), "{logged}");
        assert!(logged.lines().any(|l| l == "--olean"), "{logged}");
        assert!(logged.lines().any(|l| l == "Demo"), "{logged}");

        let vr = f
            .cli(tag)
            .args(["--json", "verify-receipt", receipt_path.to_str().unwrap()])
            .output()
            .unwrap();
        assert_ok(&vr, &format!("verify-receipt for {req_engine}"));
        let vr_json: Value = serde_json::from_slice(&vr.stdout).unwrap();
        assert_eq!(vr_json["kernel_engine"], req_engine);
        assert_eq!(vr_json["con_leche_rev"], kernel::PINNED_CON_LECHE_REV);
    }

    // 2. Exit 1 (Rejected) and Exit 2 (Declined) from `con-leche` fail closed and do NOT emit receipts.
    for code in ["1", "2"] {
        let bad_receipt = f.root.join(format!("bad-receipt-{code}.json"));
        let bad_out = f
            .cli(&format!("cl_fail_{code}"))
            .env(kernel::CON_LECHE_BIN_ENV, &mock_bin)
            .env("CI_CON_LECHE_CODE", code)
            .args([
                "--json",
                "ci-verify",
                "--project-dir",
                repo.to_str().unwrap(),
                "--mode",
                "trusted",
                "--kernel",
                "con-leche",
                "--receipt",
                bad_receipt.to_str().unwrap(),
            ])
            .output()
            .unwrap();
        assert_err(&bad_out, &format!("ci-verify con-leche exit {code}"));
        assert!(!bad_receipt.exists());
    }

    // 3. A `TURBO_CON_LECHE_BIN` placed inside the project/checkout (outside the pinned bridge path)
    //    is rejected fail-closed so an untrusted checkout cannot supply its own verifier binary.
    let in_repo_bin = repo.join("evil-con-leche.sh");
    write_executable_script(&in_repo_bin, "#!/usr/bin/env bash\nexit 0\n");
    let evil_out = f
        .cli("cl_evil")
        .env(kernel::CON_LECHE_BIN_ENV, &in_repo_bin)
        .args([
            "--json",
            "ci-verify",
            "--project-dir",
            repo.to_str().unwrap(),
            "--mode",
            "trusted",
            "--kernel",
            "con-leche",
        ])
        .output()
        .unwrap();
    assert_err(
        &evil_out,
        "ci-verify rejects TURBO_CON_LECHE_BIN inside checkout",
    );

    // 4. `check --emit-olean --kernel con-leche` and `pr-verify --kernel con-leche`
    //    execute `con-leche --verified --olean` on the materialized `.olean` closure,
    //    fail closed on exit 1 / exit 2, and reject checkout-contained binaries.
    let emit_ok = f
        .cli("cl_emit_ok")
        .env(kernel::CON_LECHE_BIN_ENV, &mock_bin)
        .env("CI_CON_LECHE_CODE", "0")
        .args([
            "--json",
            "check",
            "--emit-olean",
            "--kernel",
            "con-leche",
            repo.join("Demo.lean").to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_ok(&emit_ok, "check --emit-olean --kernel con-leche");
    let emit_json: Value = serde_json::from_slice(&emit_ok.stdout).unwrap();
    assert_eq!(emit_json["kernel_engine"], "con-leche");
    assert_eq!(emit_json["con_leche_rev"], kernel::PINNED_CON_LECHE_REV);
    let logged_emit = fs::read_to_string(&args_log).unwrap();
    assert!(
        logged_emit.lines().any(|l| l == "--verified"),
        "{logged_emit}"
    );
    assert!(logged_emit.lines().any(|l| l == "--olean"), "{logged_emit}");
    assert!(logged_emit.lines().any(|l| l == "Demo"), "{logged_emit}");

    let emit_fail = f
        .cli("cl_emit_fail")
        .env(kernel::CON_LECHE_BIN_ENV, &mock_bin)
        .env("CI_CON_LECHE_CODE", "1")
        .args([
            "--json",
            "check",
            "--emit-olean",
            "--kernel",
            "con-leche",
            repo.join("Demo.lean").to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_err(&emit_fail, "check --emit-olean con-leche exit 1");

    // Non-`--emit-olean` `check` still fails closed because `con-leche` verifies `.olean` closures.
    let no_emit_fail = f
        .cli("cl_no_emit_fail")
        .env(kernel::CON_LECHE_BIN_ENV, &mock_bin)
        .env("CI_CON_LECHE_CODE", "0")
        .args([
            "--json",
            "check",
            "--kernel",
            "con-leche",
            repo.join("Demo.lean").to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_err(
        &no_emit_fail,
        "check without --emit-olean rejects --kernel con-leche",
    );

    // `pr-verify` with `--kernel con-leche` and `--kernel both` verifies head statement `.olean` closure.
    fs::write(
        repo.join("Demo.lean"),
        "theorem sample : 1 + 1 = 2 := by exact rfl\n",
    )
    .unwrap();
    for (tag, req_engine) in [("pr_cl_only", "con-leche"), ("pr_cl_both", "both")] {
        let pr_receipt = f.root.join(format!("pr-receipt-{tag}.json"));
        let pr_ok = f
            .cli(tag)
            .env(kernel::CON_LECHE_BIN_ENV, &mock_bin)
            .env("CI_CON_LECHE_CODE", "0")
            .args([
                "--json",
                "pr-verify",
                "--project-dir",
                repo.to_str().unwrap(),
                "--base",
                "HEAD",
                "--mode",
                "trusted",
                "--kernel",
                req_engine,
                "--receipt",
                pr_receipt.to_str().unwrap(),
            ])
            .output()
            .unwrap();
        assert_ok(&pr_ok, &format!("pr-verify --kernel {req_engine}"));
        let pr_v: Value = serde_json::from_slice(&pr_ok.stdout).unwrap();
        assert_eq!(pr_v["kernel_engine"], req_engine);
        assert_eq!(pr_v["con_leche_rev"], kernel::PINNED_CON_LECHE_REV);
        let pr_vr = f
            .cli(tag)
            .args(["--json", "verify-receipt", pr_receipt.to_str().unwrap()])
            .output()
            .unwrap();
        assert_ok(&pr_vr, &format!("verify-receipt pr-verify {req_engine}"));
    }

    let pr_bad_receipt = f.root.join("pr-bad-receipt.json");
    let pr_fail = f
        .cli("pr_cl_fail")
        .env(kernel::CON_LECHE_BIN_ENV, &mock_bin)
        .env("CI_CON_LECHE_CODE", "1")
        .args([
            "--json",
            "pr-verify",
            "--project-dir",
            repo.to_str().unwrap(),
            "--base",
            "HEAD",
            "--mode",
            "trusted",
            "--kernel",
            "con-leche",
            "--receipt",
            pr_bad_receipt.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_err(&pr_fail, "pr-verify con-leche exit 1");
    assert!(!pr_bad_receipt.exists());

    let pr_evil = f
        .cli("pr_cl_evil")
        .env(kernel::CON_LECHE_BIN_ENV, &in_repo_bin)
        .args([
            "--json",
            "pr-verify",
            "--project-dir",
            repo.to_str().unwrap(),
            "--base",
            "HEAD",
            "--mode",
            "trusted",
            "--kernel",
            "con-leche",
        ])
        .output()
        .unwrap();
    assert_err(
        &pr_evil,
        "pr-verify rejects TURBO_CON_LECHE_BIN inside checkout",
    );
}

#[cfg(unix)]
#[test]
fn real_con_leche_binary_verifies_valid_and_rejects_adversarial_olean_if_built() {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    let Ok(con_leche_bin) = kernel::discover_con_leche_binary(Some(&repo_root)) else {
        return;
    };
    let f = KernelTestFixture::new("real_con_leche");
    let olean_dir = f.root.join("lib");
    let scratch_dir = f.root.join("tmp");
    fs::create_dir_all(&olean_dir).unwrap();
    fs::create_dir_all(&scratch_dir).unwrap();

    // Locate the v4.35.0 `lean` compiler cleanly even when no elan default toolchain is configured.
    fs::write(
        olean_dir.join("lean-toolchain"),
        format!("{}\n", kernel::PINNED_CON_LECHE_TOOLCHAIN),
    )
    .unwrap();
    let lean_bin = Command::new("elan")
        .current_dir(&olean_dir)
        .args(["which", "lean"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| PathBuf::from(String::from_utf8_lossy(&o.stdout).trim()))
        .unwrap_or_else(|| PathBuf::from("lean"));

    let valid_src = olean_dir.join("ValidPrelude.lean");
    fs::write(
        &valid_src,
        "module\nprelude\npublic section\ninductive Yes : Prop where\n  | intro\ntheorem yes : Yes := Yes.intro\nend\n",
    )
    .unwrap();
    let comp_valid = Command::new(&lean_bin)
        .current_dir(&olean_dir)
        .args([
            "-R",
            olean_dir.to_str().unwrap(),
            "-o",
            olean_dir.join("ValidPrelude.olean").to_str().unwrap(),
            valid_src.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_ok(&comp_valid, "compile ValidPrelude.lean");

    let resolved_con_leche = kernel::ResolvedConLecheBinary::resolve(
        &con_leche_bin,
        kernel::ConLecheBinaryProvenance::ProvisionedPinnedRev,
    )
    .unwrap();
    let rep_valid = kernel::verify_olean_modules_with_con_leche(
        &resolved_con_leche,
        std::slice::from_ref(&olean_dir),
        &["ValidPrelude".to_string()],
        &[],
        Some(2),
        Some(&scratch_dir),
    )
    .unwrap();
    assert_eq!(rep_valid.verdict, kernel::ConLecheVerdict::Accepted);
    assert_eq!(rep_valid.exit_code, 0);
    assert!(rep_valid.accepted_declarations.unwrap_or(0) >= 1);

    // Adversarial Nat.div axiom spoofing: accepted by `lean` under `prelude`, rejected (exit 1) by `con-leche --verified`.
    let spoof_src = olean_dir.join("SpoofNatDiv.lean");
    fs::write(
        &spoof_src,
        "module\nprelude\npublic section\nset_option genCtorIdx false in\ninductive Nat where\n  | zero : Nat\n  | succ (n : Nat) : Nat\naxiom Nat.div : Nat -> Nat -> Nat\nend\n",
    )
    .unwrap();
    let comp_spoof = Command::new(&lean_bin)
        .current_dir(&olean_dir)
        .args([
            "-R",
            olean_dir.to_str().unwrap(),
            "-o",
            olean_dir.join("SpoofNatDiv.olean").to_str().unwrap(),
            spoof_src.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_ok(&comp_spoof, "compile SpoofNatDiv.lean");

    let rep_spoof = kernel::verify_olean_modules_with_con_leche(
        &resolved_con_leche,
        std::slice::from_ref(&olean_dir),
        &["SpoofNatDiv".to_string()],
        &[],
        Some(2),
        Some(&scratch_dir),
    )
    .unwrap();
    assert_eq!(rep_spoof.verdict, kernel::ConLecheVerdict::Rejected);
    assert_eq!(rep_spoof.exit_code, 1);

    // Missing module on search path -> exit 3 -> fail-closed Err.
    let err_missing = kernel::verify_olean_modules_with_con_leche(
        &resolved_con_leche,
        std::slice::from_ref(&olean_dir),
        &["NoSuchModuleAnywhere".to_string()],
        &[],
        Some(2),
        Some(&scratch_dir),
    )
    .unwrap_err();
    assert!(err_missing.to_string().contains("exit 3"));

    // Even when `TURBO_CON_LECHE_BIN` points at the real built binary, `turbo-lean check --kernel con-leche`
    // STILL fails closed until full project `.olean` closure replay is wired into `check`/`pr-verify`/`ci-verify`.
    let proj = f.root.join("cli_proj");
    fs::create_dir_all(&proj).unwrap();
    fs::write(
        proj.join("lean-toolchain"),
        format!("{}\n", kernel::PINNED_CON_LECHE_TOOLCHAIN),
    )
    .unwrap();
    fs::write(proj.join("Sample.lean"), "theorem t : 1 + 1 = 2 := rfl\n").unwrap();
    let cli_fail = f
        .cli("still_fail_closed")
        .env(kernel::CON_LECHE_BIN_ENV, &con_leche_bin)
        .args([
            "--json",
            "check",
            "--kernel",
            "con-leche",
            proj.join("Sample.lean").to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_err(
        &cli_fail,
        "CLI --kernel con-leche remains fail-closed even when binary exists",
    );
}
