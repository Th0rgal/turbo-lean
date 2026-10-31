#[allow(dead_code)]
#[path = "support/corpus.rs"]
mod corpus;
use std::{fs, process::Command};

#[test]
fn lexical_scope_and_elaborated_identity_across_verdict_paths() {
    let tmp = corpus::Temp::new("lexical-identity");
    fs::write(
        tmp.0.join("lean-toolchain"),
        include_str!("../../../lean/lean-toolchain"),
    )
    .unwrap();
    fs::write(
        tmp.0.join("lakefile.toml"),
        "name = \"identity\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    let file = tmp.0.join("Identity.lean");
    let variants = [
        "def message : String := \"\nend B\nnamespace A\n\"",
        "def message : String := r##\"\nend B\nnamespace A\n\" -- /- still raw\n\"##",
        "/-! doc comment\n/- nested /- deeper -/\nend B\n-/\nnamespace A\n-/",
        "def mark : Char := '\"'\ndef message : String := \"escaped \\\"\nend B\nnamespace A\n\"\n-- namespace A",
    ];
    for (variant, setup) in variants.iter().enumerate() {
        for valid in [true, false] {
            let body = if valid {
                "n = n := rfl"
            } else {
                "n = n + 1 := by rfl"
            };
            let src = format!("namespace B\n{setup}\ntheorem same (n : Nat) : {body}\nend B\n");
            fs::write(&file, &src).unwrap();
            let oracle = corpus::oracle(
                &tmp.0,
                "Identity",
                &src.replace("n = n + 1 := by rfl", "n = n + 1 := by sorry"),
            );
            assert_eq!(oracle.into_iter().collect::<Vec<_>>(), ["B.same"]);
            for mode in ["check", "fast-check", "agent-step"] {
                for target in ["A.same", "B.same"] {
                    let mut cmd = Command::new(env!("CARGO_BIN_EXE_turbo-lean"));
                    cmd.current_dir(&tmp.0)
                        .env("TURBO_LEAN_NO_DAEMON", "1")
                        .args(["--json", "--cache-dir"])
                        .arg(tmp.0.join("cache"))
                        .arg(mode)
                        .arg("Identity.lean")
                        .args(["--decl", target]);
                    if mode != "fast-check" {
                        cmd.arg("--project-dir").arg(&tmp.0);
                    }
                    let out = corpus::run(&mut cmd);
                    let text = corpus::diagnostic(&out);
                    let context = format!(
                        "variant={variant}, valid={valid}, mode={mode}, target={target}: {text}"
                    );
                    if target == "A.same" {
                        assert!(!out.status.success(), "{context}");
                        assert!(text.contains("not found"), "{context}");
                        assert!(!text.contains("\"status\""), "{context}");
                    } else if mode == "check" && !valid {
                        assert!(!out.status.success(), "{context}");
                    } else {
                        // A confirmed false statement may return a Stage-1 counterexample.
                        assert!(text.contains("B.same"), "{context}");
                        assert!(!text.contains("identity unconfirmed"), "{context}");
                        if !valid {
                            assert!(text.contains("counterexample"), "{context}");
                        } else {
                            assert!(out.status.success(), "{context}");
                        }
                    }
                }
            }
        }
    }
}
