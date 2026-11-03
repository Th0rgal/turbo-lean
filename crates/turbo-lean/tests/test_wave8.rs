//! End-to-end CLI regression suite for Wave 8 PR-2 (`impact`, `check --allow-sorry`, `gate`, `export --cone`).

use serde_json::Value;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

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

#[test]
fn cli_allow_sorry_rejects_broken_trailing_defs_and_def_sorry() {
    let ws = TestWorkspace::new("allow_sorry");
    let proj = ws.proj();

    // 1) [P0-2] Broken trailing `def` after a clean theorem + sorry theorem MUST fail `--allow-sorry`,
    //    report `<module_definitions>` error verdict, and cache the clean theorem shard.
    fs::write(
        proj.join("W8/Partial.lean"),
        "theorem clean_one : 1 + 1 = 2 := rfl\n\
         theorem wip_one : 2 + 2 = 4 := by\n\
           sorry\n\
         def brokenTrailing : Nat := \"not_a_nat\"\n",
    )
    .unwrap();

    let out1 = ws.run(&["--json", "check", "W8/Partial.lean", "--allow-sorry"]);
    assert!(
        !out1.status.success(),
        "check --allow-sorry must exit non-zero on broken trailing def; stdout={}",
        String::from_utf8_lossy(&out1.stdout)
    );
    let j1: Value = serde_json::from_slice(&out1.stdout).expect("valid JSON output");
    assert_eq!(j1["status"], "partial_file_failed");
    assert_eq!(j1["certified_module"], false);
    assert_eq!(j1["verified_count"], 1);
    assert_eq!(j1["sorry_count"], 1);
    assert!(
        j1["error_count"].as_u64().unwrap_or(0) >= 1,
        "error_count must reflect module skeleton failure: {j1}"
    );
    assert!(
        j1["declarations"].as_array().unwrap().iter().any(|d| {
            d["decl"] == "<module_definitions>"
                && d["kind"] == "module_skeleton"
                && d["status"] == "error"
        }),
        "declarations must include <module_definitions> error verdict: {j1}"
    );

    // 2) [P0-2] Zero-sorry file with broken trailing `def` MUST also fail (never `certified_module: true`),
    //    and `clean_one` must be a CAS hit (`cached_count == 1`) from run 1!
    fs::write(
        proj.join("W8/Partial.lean"),
        "theorem clean_one : 1 + 1 = 2 := rfl\n\
         def brokenTrailing : Nat := \"not_a_nat\"\n",
    )
    .unwrap();
    let out2 = ws.run(&["--json", "check", "W8/Partial.lean", "--allow-sorry"]);
    assert!(
        !out2.status.success(),
        "zero-sorry file with broken trailing def must fail: {}",
        String::from_utf8_lossy(&out2.stdout)
    );
    let j2: Value = serde_json::from_slice(&out2.stdout).expect("valid JSON output");
    assert_eq!(j2["status"], "partial_file_failed");
    assert_eq!(j2["certified_module"], false);
    assert_eq!(
        j2["cached_count"], 1,
        "clean_one from prior partial run must hit CAS: {j2}"
    );

    // 3) [P1-3] `check --decl <thm> --allow-sorry` rejects `sorry` in a non-theorem `def`
    //    outside theorem shards even when `<thm>` does not reference that `def`.
    fs::write(
        proj.join("W8/DefSorry.lean"),
        "def sneakyBad : Nat := sorry\n\ntheorem clean_target : 3 + 3 = 6 := rfl\n",
    )
    .unwrap();
    let out3 = ws.run(&[
        "--json",
        "check",
        "W8/DefSorry.lean",
        "--decl",
        "clean_target",
        "--allow-sorry",
    ]);
    assert!(
        !out3.status.success(),
        "check --decl --allow-sorry must reject sorry in non-theorem def: stdout={} stderr={}",
        String::from_utf8_lossy(&out3.stdout),
        String::from_utf8_lossy(&out3.stderr)
    );
    let stderr3 = String::from_utf8_lossy(&out3.stderr);
    let stdout3 = String::from_utf8_lossy(&out3.stdout);
    assert!(
        stderr3.contains("outside theorem shards") || stdout3.contains("outside theorem shards"),
        "expected outside theorem shards diagnostic; stdout={stdout3} stderr={stderr3}"
    );

    // Meanwhile, a sibling `theorem` with `sorry` IS allowed when checking `clean_target` under `--allow-sorry`.
    fs::write(
        proj.join("W8/ThmSorry.lean"),
        "theorem wip_sibling : 1 = 1 := by\n  sorry\n\ntheorem clean_target : 3 + 3 = 6 := rfl\n",
    )
    .unwrap();
    let out4 = ws.run(&[
        "--json",
        "check",
        "W8/ThmSorry.lean",
        "--decl",
        "clean_target",
        "--allow-sorry",
    ]);
    assert!(
        out4.status.success(),
        "sibling theorem sorry must permit checking clean_target: stdout={} stderr={}",
        String::from_utf8_lossy(&out4.stdout),
        String::from_utf8_lossy(&out4.stderr)
    );
    let j4: Value = serde_json::from_slice(&out4.stdout).expect("valid JSON");
    assert_eq!(j4["status"], "theorem_verified");

    // 4) [P2] `check --decl <thm> --allow-sorry` MUST reject a broken trailing `def` in the same file
    //    (cannot pass module-level skeleton mistakes just because `--decl` targeted an earlier theorem).
    fs::write(
        proj.join("W8/DeclTrailingBadDef.lean"),
        "theorem clean_target : 3 + 3 = 6 := rfl\ndef brokenAfter : Nat := \"bad_string\"\n",
    )
    .unwrap();
    let out5 = ws.run(&[
        "--json",
        "check",
        "W8/DeclTrailingBadDef.lean",
        "--decl",
        "clean_target",
        "--allow-sorry",
    ]);
    assert!(
        !out5.status.success(),
        "check --decl --allow-sorry must reject broken trailing def; stdout={} stderr={}",
        String::from_utf8_lossy(&out5.stdout),
        String::from_utf8_lossy(&out5.stderr)
    );

    // 5) [P1] `check --allow-sorry` and `check --decl <d> --allow-sorry` MUST reject `sorry`
    //    inside theorem signatures/statements (`theorem t1 (h : False := sorry) : False := h`,
    //    `theorem t1 : sorry := trivial`) and same-line `def bad : Nat := sorry; theorem ok : True := trivial`,
    //    never poisoning trusted CAS with `clean_false : False := t1` or reporting `decl_sorry` on `t1 : sorry`.
    for (file_name, bad_src, decls) in [
        (
            "W8/StmtParamSorry.lean",
            "theorem t1 (h : False := sorry) : False := h\ntheorem clean_false : False := t1\n",
            &["t1", "clean_false"][..],
        ),
        (
            "W8/StmtTypeSorry.lean",
            "theorem t1 : sorry := trivial\n",
            &["t1"][..],
        ),
        (
            "W8/SameLineDefSorry.lean",
            "def bad : Nat := sorry; theorem ok : True := trivial\n",
            &["ok"][..],
        ),
    ] {
        fs::write(proj.join(file_name), bad_src).unwrap();
        let whole_out = ws.run(&["--json", "check", file_name, "--allow-sorry"]);
        assert!(
            !whole_out.status.success(),
            "check {file_name} --allow-sorry must fail closed; stdout={} stderr={}",
            String::from_utf8_lossy(&whole_out.stdout),
            String::from_utf8_lossy(&whole_out.stderr)
        );
        for d in decls {
            let decl_out = ws.run(&["--json", "check", file_name, "--decl", d, "--allow-sorry"]);
            assert!(
                !decl_out.status.success(),
                "check {file_name} --decl {d} --allow-sorry must fail closed; stdout={} stderr={}",
                String::from_utf8_lossy(&decl_out.stdout),
                String::from_utf8_lossy(&decl_out.stderr)
            );
            let stdout_str = String::from_utf8_lossy(&decl_out.stdout);
            assert!(
                !stdout_str.contains("decl_sorry") && !stdout_str.contains("theorem_verified"),
                "must never report decl_sorry or theorem_verified on {file_name}::{d}: {stdout_str}"
            );
        }
    }
}

#[test]
fn cli_check_withholds_stdout_and_runs_dependent_recheck_on_broken_importer() {
    let ws = TestWorkspace::new("dep_recheck");
    let proj = ws.proj();

    fs::write(
        proj.join("W8/Base.lean"),
        "def baseVal : Nat := 10\n\
         #eval baseVal\n\
         theorem base_ok : baseVal = 10 := rfl\n",
    )
    .unwrap();
    fs::write(
        proj.join("W8/Downstream.lean"),
        "import W8.Base\ntheorem down_ok : baseVal = 10 := rfl\n",
    )
    .unwrap();

    // Initial full build succeeds; commit baseline in git so `nonlocal_edits` compares against HEAD
    // under Git >= 2.46 (where `trusted_tools::git` succeeds instead of failing closed).
    let b_out = ws.run(&["build", "+W8.Downstream"]);
    assert!(
        b_out.status.success(),
        "initial build failed: {}",
        String::from_utf8_lossy(&b_out.stderr)
    );
    assert!(Command::new("git")
        .arg("init")
        .current_dir(&proj)
        .status()
        .unwrap()
        .success());
    assert!(Command::new("git")
        .args(["config", "user.email", "test@example.com"])
        .current_dir(&proj)
        .status()
        .unwrap()
        .success());
    assert!(Command::new("git")
        .args(["config", "user.name", "Test"])
        .current_dir(&proj)
        .status()
        .unwrap()
        .success());
    assert!(Command::new("git")
        .args([
            "add",
            "lakefile.toml",
            "lean-toolchain",
            "W8/Base.lean",
            "W8/Downstream.lean"
        ])
        .current_dir(&proj)
        .status()
        .unwrap()
        .success());
    assert!(Command::new("git")
        .args(["commit", "--no-gpg-sign", "-m", "baseline"])
        .current_dir(&proj)
        .status()
        .unwrap()
        .success());

    // Mutate `W8/Base.lean` non-locally (`baseVal := 99`), breaking `W8/Downstream.lean`.
    fs::write(
        proj.join("W8/Base.lean"),
        "def baseVal : Nat := 99\n\
         #eval 777888999\n\
         theorem base_ok : baseVal = 99 := rfl\n",
    )
    .unwrap();

    // 1) [P1-4c] Standard `check` (text mode, NOT `--json`) on `W8/Base.lean` must fail on broken
    //    `W8.Downstream` AND withhold `#eval 777888999` / `[turbo-lean] OK` from stdout!
    let c_std = ws.run(&["check", "W8/Base.lean"]);
    assert!(
        !c_std.status.success(),
        "standard check must fail when dependent module breaks"
    );
    let stdout_std = String::from_utf8_lossy(&c_std.stdout);
    assert!(
        !stdout_std.contains("777888999") && !stdout_std.contains("OK:"),
        "check must not emit #eval stdout or OK banner before dependent recheck succeeds; stdout={stdout_std}"
    );

    // 2) [P0-2] `check --allow-sorry` on a 0-sorry file (`certified_module: true` candidate) must ALSO
    //    recheck dependents and fail instead of claiming `certified_module: true` when downstream breaks!
    let c_allow = ws.run(&["--json", "check", "W8/Base.lean", "--allow-sorry"]);
    assert!(
        !c_allow.status.success(),
        "0-sorry check --allow-sorry must fail when non-local edit breaks downstream importer; stdout={} stderr={}",
        String::from_utf8_lossy(&c_allow.stdout),
        String::from_utf8_lossy(&c_allow.stderr)
    );

    // 3) [P2] In a git repo with a committed baseline, `check --decl base_ok --allow-sorry` on a
    //    0-sorry file with a non-local signature/def edit that breaks `W8.Downstream` must ALSO
    //    run `recheck_dependents_if_nonlocal` and fail!
    fs::write(
        proj.join("W8/Base.lean"),
        "def baseVal : Nat := 10\ntheorem base_ok : baseVal = 10 := rfl\n",
    )
    .unwrap();
    assert!(ws.run(&["build", "+W8.Downstream"]).status.success());
    assert!(Command::new("git")
        .args(["add", "W8/Base.lean"])
        .current_dir(&proj)
        .status()
        .unwrap()
        .success());
    assert!(Command::new("git")
        .args(["commit", "--no-gpg-sign", "-m", "baseline2"])
        .current_dir(&proj)
        .status()
        .unwrap()
        .success());

    // Baseline matches HEAD: `check --decl base_ok --allow-sorry` MUST succeed cleanly.
    let c_decl_clean = ws.run(&[
        "--json",
        "check",
        "W8/Base.lean",
        "--decl",
        "base_ok",
        "--allow-sorry",
    ]);
    assert!(
        c_decl_clean.status.success(),
        "0-sorry check --decl --allow-sorry matching HEAD must succeed; stdout={} stderr={}",
        String::from_utf8_lossy(&c_decl_clean.stdout),
        String::from_utf8_lossy(&c_decl_clean.stderr)
    );

    // Mutate `W8/Base.lean` non-locally (`baseVal := 99`), breaking `W8/Downstream.lean` vs HEAD.
    fs::write(
        proj.join("W8/Base.lean"),
        "def baseVal : Nat := 99\ntheorem base_ok : baseVal = 99 := rfl\n",
    )
    .unwrap();
    let c_decl_allow = ws.run(&[
        "--json",
        "check",
        "W8/Base.lean",
        "--decl",
        "base_ok",
        "--allow-sorry",
    ]);
    assert!(
        !c_decl_allow.status.success(),
        "0-sorry check --decl --allow-sorry must fail when non-local edit vs HEAD breaks downstream importer; stdout={} stderr={}",
        String::from_utf8_lossy(&c_decl_allow.stdout),
        String::from_utf8_lossy(&c_decl_allow.stderr)
    );
}

#[test]
fn cli_gate_reports_native_artifact_error_and_cone_export_isolates_same_decl_names() {
    let ws = TestWorkspace::new("gate_cone");
    let proj = ws.proj();

    // Part A: [P1-6] `export --cone +W8.ModA` excludes identically named `theorem shared_name` from `W8.ModB`.
    fs::write(
        proj.join("W8/ModA.lean"),
        "def aConst : Nat := 11\ntheorem shared_name : aConst = 11 := rfl\n",
    )
    .unwrap();
    fs::write(
        proj.join("W8/ModB.lean"),
        "def bConst : Nat := 22\ntheorem shared_name : bConst = 22 := rfl\n",
    )
    .unwrap();

    let out_a = ws.run(&[
        "--json",
        "check",
        "W8/ModA.lean",
        "--decl",
        "shared_name",
        "--allow-sorry",
    ]);
    assert!(
        out_a.status.success(),
        "ModA check failed: {}",
        String::from_utf8_lossy(&out_a.stderr)
    );
    let out_b = ws.run(&[
        "--json",
        "check",
        "W8/ModB.lean",
        "--decl",
        "shared_name",
        "--allow-sorry",
    ]);
    assert!(
        out_b.status.success(),
        "ModB check failed: {}",
        String::from_utf8_lossy(&out_b.stderr)
    );

    let pack_file = ws.root.join("moda.tlpack");
    let sk_hex = "4444444444444444444444444444444444444444444444444444444444444444";
    let exp_out = ws.run(&[
        "--json",
        "export",
        "--output",
        pack_file.to_str().unwrap(),
        "--cone",
        "+W8.ModA",
        "--signing-key",
        sk_hex,
    ]);
    assert!(
        exp_out.status.success(),
        "export --cone failed: stdout={} stderr={}",
        String::from_utf8_lossy(&exp_out.stdout),
        String::from_utf8_lossy(&exp_out.stderr)
    );

    let fresh_cache = ws.root.join("fresh_cache");
    let imp_out = ws.run_in_with_env(
        &proj,
        &fresh_cache,
        &[
            "--json",
            "import",
            pack_file.to_str().unwrap(),
            "--trust-domain",
            "trusted",
            "--allow-unattested-trusted",
        ],
        &[],
    );
    assert!(
        imp_out.status.success(),
        "import failed: stdout={} stderr={}",
        String::from_utf8_lossy(&imp_out.stdout),
        String::from_utf8_lossy(&imp_out.stderr)
    );

    // Checking `ModA`'s `shared_name` against `fresh_cache` MUST hit CAS (`status == "theorem_cache_hit"`),
    // whereas checking `ModB`'s `shared_name` MUST miss CAS (`status == "theorem_verified"`)!
    let hit_a = ws.run_in_with_env(
        &proj,
        &fresh_cache,
        &[
            "--json",
            "check",
            "W8/ModA.lean",
            "--decl",
            "shared_name",
            "--allow-sorry",
        ],
        &[],
    );
    assert!(hit_a.status.success());
    let ja: Value = serde_json::from_slice(&hit_a.stdout).unwrap();
    assert_eq!(
        ja["status"], "theorem_cache_hit",
        "in-cone theorem shard must hit CAS after import: {ja}"
    );

    let miss_b = ws.run_in_with_env(
        &proj,
        &fresh_cache,
        &[
            "--json",
            "check",
            "W8/ModB.lean",
            "--decl",
            "shared_name",
            "--allow-sorry",
        ],
        &[],
    );
    assert!(miss_b.status.success());
    let jb: Value = serde_json::from_slice(&miss_b.stdout).unwrap();
    assert_eq!(
        jb["status"], "theorem_verified",
        "out-of-cone theorem shard with colliding decl name must NOT hit CAS in cone pack: {jb}"
    );

    // Part B: [P1-5] `turbo-lean --json gate` emits structured `GateReport` JSON (`gate_passed: false`,
    // `failure_kind: "native_artifact_error"`) instead of aborting without JSON when native C compilation fails.
    let nat_proj = ws.root.join("nat_proj");
    fs::create_dir_all(nat_proj.join("NatW8")).unwrap();
    fs::write(
        nat_proj.join("lean-toolchain"),
        include_str!("../../../lean/lean-toolchain"),
    )
    .unwrap();
    fs::write(
        nat_proj.join("lakefile.toml"),
        "name = \"natw8\"\ndefaultTargets = [\"NatW8\"]\nprecompileModules = true\n[[lean_lib]]\nname = \"NatW8\"\nglobs = [\"NatW8.+\"]\n",
    )
    .unwrap();
    fs::write(nat_proj.join("NatW8/Base.lean"), "def natVal : Nat := 7\n").unwrap();
    fs::write(
        nat_proj.join("NatW8/Top.lean"),
        "import NatW8.Base\ntheorem nat_ok : natVal = 7 := rfl\n",
    )
    .unwrap();

    let gate_cache = ws.root.join("gate_cache");
    let bad_cc = ws.root.join("missing_cc_compiler_w8");
    let gate_out = ws.run_in_with_env(
        &nat_proj,
        &gate_cache,
        &["--json", "gate", "+NatW8.Top"],
        &[("LEAN_CC", bad_cc.to_str().unwrap())],
    );
    assert!(
        !gate_out.status.success(),
        "gate must exit non-zero when native_artifact_error occurs"
    );
    let gate_json: Value = serde_json::from_slice(&gate_out.stdout).unwrap_or_else(|e| {
        panic!(
            "gate --json must emit valid JSON report on native artifact error ({e}); stdout={} stderr={}",
            String::from_utf8_lossy(&gate_out.stdout),
            String::from_utf8_lossy(&gate_out.stderr)
        )
    });
    assert_eq!(gate_json["gate_passed"], false);
    assert!(
        gate_json["root_cause_failures"]
            .as_array()
            .unwrap()
            .iter()
            .any(|f| f["module"] == "NatW8.Base" && f["failure_kind"] == "native_artifact_error"),
        "expected native_artifact_error on NatW8.Base: {gate_json}"
    );
    assert!(
        gate_json["blocked_downstream"]
            .as_array()
            .unwrap()
            .iter()
            .any(|b| b["module"] == "NatW8.Top"),
        "expected NatW8.Top in blocked_downstream: {gate_json}"
    );
}

#[test]
fn cli_acc_rec_subsingleton_proof_change_invalidates_downstream_shard_cache_and_fails() {
    let ws = TestWorkspace::new("acc_rec_soundness");
    let proj = ws.proj();

    // Upstream `W8/U.lean` v1: proves `accProof` constructively (`Acc.intro () (fun _ h => False.elim h)`),
    // so `g` reduces to `5` in Lean's kernel via `Acc.rec` subsingleton elimination!
    let u_constructive = "\
theorem accProof : Acc (fun _ _ : Unit => False) () :=
  Acc.intro () (fun _ h => False.elim h)

def g : Nat :=
  Acc.rec (motive := fun _ _ => Nat) (fun _ _ _ => 5) accProof
";
    // Upstream `W8/U.lean` v2: proves the EXACT SAME theorem type non-constructively via `Classical.choice`,
    // so `g` gets stuck in the kernel (`Reduction got stuck` / definitional equality failure)!
    let u_nonconstructive = "\
theorem accProof : Acc (fun _ _ : Unit => False) () :=
  Classical.choice ⟨Acc.intro () (fun _ h => False.elim h)⟩

def g : Nat :=
  Acc.rec (motive := fun _ _ => Nat) (fun _ _ _ => 5) accProof
";
    let d3_src = "\
import W8.U
theorem t : g = 5 := by decide +kernel
";

    fs::write(proj.join("W8/U.lean"), u_constructive).unwrap();
    fs::write(proj.join("W8/D3.lean"), d3_src).unwrap();

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

    // Repeat check to confirm shard CAS hit works when `U.olean` is unchanged.
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

    // 2) Mutate `W8/U.lean` proof of `accProof` to `Classical.choice ⟨Acc.intro ...⟩` and rebuild `W8.U`.
    fs::write(proj.join("W8/U.lean"), u_nonconstructive).unwrap();
    let b2 = ws.run(&["build", "+W8.U"]);
    assert!(
        b2.status.success(),
        "rebuild +W8.U failed: {}",
        String::from_utf8_lossy(&b2.stderr)
    );

    // 3) Downstream `turbo-lean check` on `W8/D3.lean` MUST NOT hit the stale v1 shard cache and MUST FAIL!
    let c2_decl = ws.run(&["--json", "check", "W8/D3.lean", "--decl", "t"]);
    assert!(
        !c2_decl.status.success(),
        "SOUNDNESS BUG: `check W8/D3.lean --decl t` falsely certified stuck Acc.rec reduction after non-constructive proof edit! stdout={} stderr={}",
        String::from_utf8_lossy(&c2_decl.stdout),
        String::from_utf8_lossy(&c2_decl.stderr)
    );

    let c2_file = ws.run(&["--json", "check", "W8/D3.lean"]);
    assert!(
        !c2_file.status.success(),
        "SOUNDNESS BUG: `check W8/D3.lean` falsely certified stuck Acc.rec reduction after non-constructive proof edit! stdout={} stderr={}",
        String::from_utf8_lossy(&c2_file.stdout),
        String::from_utf8_lossy(&c2_file.stderr)
    );

    let c2_allow = ws.run(&["--json", "check", "W8/D3.lean", "--allow-sorry"]);
    assert!(
        !c2_allow.status.success(),
        "SOUNDNESS BUG: `check W8/D3.lean --allow-sorry` falsely certified stuck Acc.rec reduction! stdout={} stderr={}",
        String::from_utf8_lossy(&c2_allow.stdout),
        String::from_utf8_lossy(&c2_allow.stderr)
    );

    // Also verify module-level build (`build +W8.D3`): even if `W8.D3` had been built under v1,
    // rebuilding `+W8.D3` under v2 MUST fail closed via `audit_or_replay_modules`!
    fs::write(proj.join("W8/U.lean"), u_constructive).unwrap();
    assert!(ws.run(&["build", "+W8.D3"]).status.success());
    fs::write(proj.join("W8/U.lean"), u_nonconstructive).unwrap();
    let b_d3_stuck = ws.run(&["build", "+W8.D3"]);
    assert!(
        !b_d3_stuck.status.success(),
        "module-level early cutoff must also fail closed via kernel replay when Acc.rec reduction gets stuck! stdout={} stderr={}",
        String::from_utf8_lossy(&b_d3_stuck.stdout),
        String::from_utf8_lossy(&b_d3_stuck.stderr)
    );
}
