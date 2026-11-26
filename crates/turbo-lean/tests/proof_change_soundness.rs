//! End-to-end CLI regression suite for proof-change soundness and the Wave 8 PR-2 surfaces
//! (`check --allow-sorry`, dependent recheck, `export --cone`).
//!
//! Ported from the owner's closed draft PR #342 (`test_wave8.rs`), adapted to this tree's report schema.
//! Every test skips when no `lean` is on PATH, as the other CLI suites do.

use serde_json::Value;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

fn lean_available() -> bool {
    Command::new("lean").arg("--version").output().is_ok()
}

struct TestWorkspace {
    root: PathBuf,
}

impl TestWorkspace {
    fn new(label: &str) -> Self {
        let root = std::env::temp_dir().join(format!(
            "turbo_test_wave8_{}_{}_{}",
            label,
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let proj = root.join("proj");
        fs::create_dir_all(proj.join("W8")).unwrap();
        fs::write(
            proj.join("lean-toolchain"),
            include_str!("../../../lean/lean-toolchain"),
        )
        .unwrap();
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"w8cli\"\ndefaultTargets = [\"W8\"]\n[[lean_lib]]\nname = \"W8\"\nglobs = [\"W8.+\"]\n",
        )
        .unwrap();
        Self { root }
    }

    fn proj(&self) -> PathBuf {
        self.root.join("proj")
    }

    fn cache(&self) -> PathBuf {
        self.root.join("cache")
    }

    fn run(&self, args: &[&str]) -> Output {
        self.run_in_with_env(&self.proj(), &self.cache(), args, &[])
    }

    fn run_in_with_env(
        &self,
        cwd: &Path,
        cache_dir: &Path,
        args: &[&str],
        extra_env: &[(&str, &str)],
    ) -> Output {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_turbo-lean"));
        for (key, _) in std::env::vars_os() {
            let k = key.to_string_lossy();
            if k.starts_with("TURBO_LEAN_") && k != "TURBO_LEAN_GIT" {
                cmd.env_remove(key);
            }
        }
        cmd.current_dir(cwd)
            .args(["--no-daemon", "--cache-dir"])
            .arg(cache_dir)
            .args(args)
            .env("TURBO_LEAN_HOME", cache_dir)
            .env("TURBO_LEAN_STAGING_DIR", self.root.join("staging"))
            .env("TURBO_LEAN_TELEMETRY", "off")
            .env("TURBO_LEAN_TIMEOUT_MS", "300000")
            .env("LEAN_NUM_THREADS", "2");
        for (k, v) in extra_env {
            cmd.env(k, v);
        }
        cmd.output().unwrap()
    }
}

impl Drop for TestWorkspace {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

/// `W8/U.lean` v1: proves `accProof` constructively, so `g` reduces to `5` in the kernel through
/// `Acc.rec` subsingleton elimination.
const U_CONSTRUCTIVE: &str = "\
theorem accProof : Acc (fun _ _ : Unit => False) () :=
  Acc.intro () (fun _ h => False.elim h)

def g : Nat :=
  Acc.rec (motive := fun _ _ => Nat) (fun _ _ _ => 5) accProof
";

/// `W8/U.lean` v2: the exact same theorem type proved through `Classical.choice`, so `g` gets stuck.
const U_NONCONSTRUCTIVE: &str = "\
theorem accProof : Acc (fun _ _ : Unit => False) () :=
  Classical.choice ⟨Acc.intro () (fun _ h => False.elim h)⟩

def g : Nat :=
  Acc.rec (motive := fun _ _ => Nat) (fun _ _ _ => 5) accProof
";

const D3_SRC: &str = "\
import W8.U
theorem t : g = 5 := by decide +kernel
";

#[test]
fn cli_acc_rec_subsingleton_proof_change_invalidates_downstream_shard_cache_and_fails() {
    if !lean_available() {
        return;
    }
    let ws = TestWorkspace::new("acc_rec_soundness");
    let proj = ws.proj();

    fs::write(proj.join("W8/U.lean"), U_CONSTRUCTIVE).unwrap();
    fs::write(proj.join("W8/D3.lean"), D3_SRC).unwrap();

    // 1) Build `W8.U` and run `check` on `W8/D3.lean` (both `--decl t` and whole-file check) to populate shard CAS.
    let b1 = ws.run(&["build", "+W8.U"]);
    assert!(
        b1.status.success(),
        "initial build +W8.U failed: {}",
        String::from_utf8_lossy(&b1.stderr)
    );

    let c1_decl = ws.run(&["--json", "check", "W8/D3.lean", "--decl", "t"]);
    assert!(
        c1_decl.status.success(),
        "D3 check --decl t must succeed under constructive U.lean: stdout={} stderr={}",
        String::from_utf8_lossy(&c1_decl.stdout),
        String::from_utf8_lossy(&c1_decl.stderr)
    );
    let j1_decl: Value = serde_json::from_slice(&c1_decl.stdout).unwrap();
    assert_eq!(j1_decl["status"], "theorem_verified");
    let shard_key_v1 = j1_decl["shard_key"].as_str().unwrap().to_string();

    // Repeat check to confirm the shard CAS hit works when `U.olean` is unchanged.
    let c1_hit = ws.run(&["--json", "check", "W8/D3.lean", "--decl", "t"]);
    assert!(c1_hit.status.success());
    let j1_hit: Value = serde_json::from_slice(&c1_hit.stdout).unwrap();
    assert_eq!(j1_hit["status"], "theorem_cache_hit");
    assert_eq!(j1_hit["shard_key"].as_str().unwrap(), shard_key_v1);

    let c1_file = ws.run(&["--json", "check", "W8/D3.lean"]);
    assert!(
        c1_file.status.success(),
        "whole-file D3 check must succeed under constructive U.lean"
    );

    // 2) Mutate the proof of `accProof` to `Classical.choice ⟨Acc.intro ...⟩` and rebuild `W8.U`.
    fs::write(proj.join("W8/U.lean"), U_NONCONSTRUCTIVE).unwrap();
    let b2 = ws.run(&["build", "+W8.U"]);
    assert!(
        b2.status.success(),
        "rebuild +W8.U failed: {}",
        String::from_utf8_lossy(&b2.stderr)
    );

    // 3) Downstream `check` on `W8/D3.lean` must not hit the stale v1 shard cache and must fail.
    let c2_decl = ws.run(&["--json", "check", "W8/D3.lean", "--decl", "t"]);
    assert!(
        !c2_decl.status.success(),
        "SOUNDNESS: `check W8/D3.lean --decl t` certified a stuck Acc.rec reduction after a non-constructive proof edit: stdout={} stderr={}",
        String::from_utf8_lossy(&c2_decl.stdout),
        String::from_utf8_lossy(&c2_decl.stderr)
    );

    let c2_file = ws.run(&["--json", "check", "W8/D3.lean"]);
    assert!(
        !c2_file.status.success(),
        "SOUNDNESS: `check W8/D3.lean` certified a stuck Acc.rec reduction after a non-constructive proof edit: stdout={} stderr={}",
        String::from_utf8_lossy(&c2_file.stdout),
        String::from_utf8_lossy(&c2_file.stderr)
    );

    let c2_allow = ws.run(&["--json", "check", "W8/D3.lean", "--allow-sorry"]);
    assert!(
        !c2_allow.status.success(),
        "SOUNDNESS: `check W8/D3.lean --allow-sorry` certified a stuck Acc.rec reduction: stdout={} stderr={}",
        String::from_utf8_lossy(&c2_allow.stdout),
        String::from_utf8_lossy(&c2_allow.stderr)
    );

    // Module-level build: even if `W8.D3` was built under v1, rebuilding `+W8.D3` under v2 must fail.
    fs::write(proj.join("W8/U.lean"), U_CONSTRUCTIVE).unwrap();
    assert!(ws.run(&["build", "+W8.D3"]).status.success());
    fs::write(proj.join("W8/U.lean"), U_NONCONSTRUCTIVE).unwrap();
    let b_d3_stuck = ws.run(&["build", "+W8.D3"]);
    assert!(
        !b_d3_stuck.status.success(),
        "SOUNDNESS: module-level early cutoff certified `+W8.D3` after a non-constructive proof edit of an importer-visible theorem: stdout={} stderr={}",
        String::from_utf8_lossy(&b_d3_stuck.stdout),
        String::from_utf8_lossy(&b_d3_stuck.stderr)
    );
}

fn git_in(dir: &Path, args: &[&str]) -> Output {
    Command::new("git")
        .arg("-C")
        .arg(dir)
        .args([
            "-c",
            "user.name=test",
            "-c",
            "user.email=test@example.invalid",
            "-c",
            "commit.gpgsign=false",
        ])
        .args(args)
        .output()
        .unwrap()
}

/// `pr-verify` variant of the Acc.rec case: the only change against `--base` is the proof body of
/// `accProof` in `W8/U.lean`; the statement is unchanged, but the importer `W8/D3.lean` stops verifying.
#[test]
fn pr_verify_rechecks_importer_after_non_constructive_proof_edit() {
    if !lean_available() {
        return;
    }
    let ws = TestWorkspace::new("acc_rec_pr_verify");
    let proj = ws.proj();

    fs::write(proj.join("W8/U.lean"), U_CONSTRUCTIVE).unwrap();
    fs::write(proj.join("W8/D3.lean"), D3_SRC).unwrap();
    assert!(git_in(&proj, &["init", "-q"]).status.success());
    assert!(git_in(&proj, &["add", "-A"]).status.success());
    let commit = git_in(&proj, &["commit", "-q", "-m", "base"]);
    assert!(
        commit.status.success(),
        "fixture commit failed: {}",
        String::from_utf8_lossy(&commit.stderr)
    );
    let head = git_in(&proj, &["rev-parse", "HEAD"]);
    let base = String::from_utf8_lossy(&head.stdout).trim().to_string();

    // Warm the cache under the constructive proof so a stale cache entry could be reused.
    let warm = ws.run(&["build", "+W8.D3"]);
    assert!(
        warm.status.success(),
        "baseline build +W8.D3 failed: {}",
        String::from_utf8_lossy(&warm.stderr)
    );

    fs::write(proj.join("W8/U.lean"), U_NONCONSTRUCTIVE).unwrap();
    let out = ws.run(&["pr-verify", "--project-dir", ".", "--base", &base]);
    assert!(
        !out.status.success(),
        "SOUNDNESS: `pr-verify --base {base}` passed after an edit that makes the importer's `decide +kernel` stuck: stdout={} stderr={}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
}
