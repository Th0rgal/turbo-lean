use serde_json::Value;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

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
    assert_eq!(ci_json["kernel_engine"], "standard");
    assert_eq!(ci_json["kernel_requested"], "auto");
    assert_eq!(ci_json["lean_toolchain"], toolchain);
    assert!(ci_json["con_leche_rev"].is_null());

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

    // 3. `verify-receipt` succeeds on valid receipts and fails closed on tampered provenance.
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
    assert_eq!(vr_json["kernel_engine"], "standard");
    assert_eq!(vr_json["lean_toolchain"], toolchain);
    assert!(vr_json["con_leche_rev"].is_null());

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
