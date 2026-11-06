#![cfg(unix)]

use serde_json::Value;
use std::fs;
use std::os::unix::fs::{symlink, MetadataExt, PermissionsExt};
use std::path::PathBuf;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        let root = std::env::temp_dir().join(format!(
            "turbo_audit_cli_{}_{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&root).unwrap();
        fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
        fs::write(
            root.join("A.lean"),
            "theorem good (n : Nat) : n + 0 = n := by simp\n",
        )
        .unwrap();
        Self(root)
    }

    fn run_args(&self, args: &[&str], disabled: bool) -> std::process::Output {
        Command::new(env!("CARGO_BIN_EXE_turbo-lean"))
            .current_dir(&self.0)
            .args(args)
            .env("TURBO_LEAN_AUDIT_CACHE_DIR", self.0.join("cache"))
            .env(
                "TURBO_LEAN_NO_AUDIT_CACHE",
                if disabled { "1" } else { "0" },
            )
            .env_remove("TURBO_LEAN_AUDIT_SPEC_CONFIG")
            .env("TURBO_LEAN_TELEMETRY", "0")
            .output()
            .unwrap()
    }

    fn run(&self, disabled: bool) -> Value {
        let output = self.run_args(
            &["--json", "audit-spec", "A.lean", "--policy", "default"],
            disabled,
        );
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        serde_json::from_slice(&output.stdout).unwrap()
    }

    fn entry(&self) -> PathBuf {
        fs::read_dir(self.0.join("cache"))
            .unwrap()
            .next()
            .unwrap()
            .unwrap()
            .path()
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn private_cache_round_trip_and_disable() {
    let f = Fixture::new();
    let cold = f.run(false);
    assert_eq!(cold["ok"], true);
    assert_eq!(cold["cache_hit"], false);
    assert_eq!(f.run(false)["cache_hit"], true);
    assert_eq!(f.run(true)["cache_hit"], false);
    assert_eq!(
        fs::metadata(f.0.join("cache")).unwrap().mode() & 0o777,
        0o700
    );
    assert_eq!(fs::metadata(f.entry()).unwrap().mode() & 0o777, 0o600);
}

#[test]
fn unsafe_directory_and_symlink_are_not_used() {
    for link in [false, true] {
        let f = Fixture::new();
        let cache = f.0.join("cache");
        if link {
            fs::create_dir(f.0.join("outside")).unwrap();
            symlink(f.0.join("outside"), &cache).unwrap();
        } else {
            fs::create_dir(&cache).unwrap();
            fs::set_permissions(&cache, fs::Permissions::from_mode(0o777)).unwrap();
        }
        for _ in 0..2 {
            let report = f.run(false);
            assert_eq!(report["ok"], true);
            assert_eq!(report["cache_hit"], false);
        }
        assert_eq!(fs::read_dir(&cache).unwrap().count(), 0);
    }
}

#[test]
fn writable_and_symlink_entries_are_recomputed() {
    for link in [false, true] {
        let f = Fixture::new();
        f.run(false);
        let entry = f.entry();
        let victim = f.0.join("victim");
        let poison = b"{\"ok\":false,\"total_specs_audited\":999}";
        if link {
            fs::write(&victim, poison).unwrap();
            fs::remove_file(&entry).unwrap();
            symlink(&victim, &entry).unwrap();
        } else {
            fs::write(&entry, poison).unwrap();
            fs::set_permissions(&entry, fs::Permissions::from_mode(0o666)).unwrap();
        }
        let report = f.run(false);
        assert_eq!(report["cache_hit"], false);
        assert_eq!(report["ok"], true);
        assert_eq!(report["total_specs_audited"], 1);
        assert_eq!(f.run(false)["cache_hit"], true);
        if link {
            assert_eq!(fs::read(victim).unwrap(), poison);
        }
    }
}

#[test]
fn per_target_policy_glob_segments_and_cli_validation() {
    let f = Fixture::new();
    let strict = f.0.join("strict");
    let open = f.0.join("open");
    fs::create_dir_all(strict.join("lean/Pkg/Proofs")).unwrap();
    fs::create_dir_all(strict.join("lean/Pkg/ProofsExtra")).unwrap();
    fs::create_dir_all(&open).unwrap();
    fs::write(
        strict.join("turbo-lean.toml"),
        "[audit_spec.path_rules.\"lean/**/Proofs/**\"]\nforbid_decl_kinds = [\"inductive\"]\n",
    )
    .unwrap();
    let src = "inductive Bad where | mk\ntheorem t (n : Nat) : n + 0 = n := by simp\n";
    fs::write(strict.join("lean/Pkg/Proofs/P.lean"), src).unwrap();
    fs::write(strict.join("lean/Pkg/ProofsExtra/Q.lean"), src).unwrap();
    fs::write(open.join("O.lean"), src).unwrap();

    for cold in [false, true] {
        let a: Value = serde_json::from_slice(
            &f.run_args(
                &[
                    "--json",
                    "audit-spec",
                    "open/O.lean",
                    "strict/lean/Pkg/Proofs/P.lean",
                ],
                cold,
            )
            .stdout,
        )
        .unwrap();
        let b: Value = serde_json::from_slice(
            &f.run_args(
                &[
                    "--json",
                    "audit-spec",
                    "strict/lean/Pkg/Proofs/P.lean",
                    "open/O.lean",
                ],
                cold,
            )
            .stdout,
        )
        .unwrap();
        assert_eq!(a["ok"], false);
        assert_eq!(b["ok"], false);
        assert_eq!(a["forbidden_scope_decls"], b["forbidden_scope_decls"]);
    }
    let extra: Value = serde_json::from_slice(
        &f.run_args(
            &["--json", "audit-spec", "strict/lean/Pkg/ProofsExtra/Q.lean"],
            false,
        )
        .stdout,
    )
    .unwrap();
    assert_eq!(extra["ok"], true);
    let cwd_proof = Command::new(env!("CARGO_BIN_EXE_turbo-lean"))
        .current_dir(strict.join("lean/Pkg/Proofs"))
        .args(["--json", "audit-spec", "P.lean"])
        .env("TURBO_LEAN_AUDIT_CACHE_DIR", f.0.join("cache"))
        .env_remove("TURBO_LEAN_AUDIT_SPEC_CONFIG")
        .env("TURBO_LEAN_TELEMETRY", "0")
        .output()
        .unwrap();
    let cwd_rep: Value = serde_json::from_slice(&cwd_proof.stdout).unwrap();
    assert_eq!(cwd_rep["ok"], false);

    fs::write(f.0.join("bad.toml"), "not_audit_spec = 1\n").unwrap();
    assert!(!f
        .run_args(&["audit-spec", "A.lean", "--policy", ""], false)
        .status
        .success());
    assert!(!f
        .run_args(&["audit-spec", "A.lean", "--policy", "bogus"], false)
        .status
        .success());
    assert!(!f
        .run_args(&["audit-spec", "A.lean", "--config", "bad.toml"], false)
        .status
        .success());
    assert!(!f
        .run_args(&["audit-spec", "A.lean", "--config", "missing.toml"], false)
        .status
        .success());
}
