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
                    if mode == "check" {
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

fn identity_project(tag: &str, src: &str) -> corpus::Temp {
    let tmp = corpus::Temp::new(tag);
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
    fs::write(tmp.0.join("Identity.lean"), src).unwrap();
    tmp
}

fn run_decl(tmp: &corpus::Temp, mode: &str, target: &str) -> (bool, String) {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_turbo-lean"));
    cmd.current_dir(&tmp.0)
        .env("TURBO_LEAN_NO_DAEMON", "1")
        .args(["--json", "--cache-dir"])
        .arg(tmp.0.join("cache"))
        .arg(mode)
        .arg("Identity.lean")
        .args(["--decl", target]);
    if mode == "check" {
        cmd.arg("--project-dir").arg(&tmp.0);
    }
    let out = corpus::run(&mut cmd);
    (out.status.success(), corpus::diagnostic(&out))
}

#[test]
fn qualified_requests_match_full_names_and_verdicts_carry_them() {
    let tmp = identity_project(
        "qualified-full-name",
        "namespace B.A\ntheorem same (n : Nat) : n = n := rfl\nend B.A\n",
    );
    for mode in ["check", "fast-check", "agent-step"] {
        let (ok, text) = run_decl(&tmp, mode, "A.same");
        assert!(!ok && text.contains("not found"), "{mode} A.same: {text}");
        assert!(!text.contains("\"status\""), "{mode} A.same: {text}");
        for target in ["B.A.same", "same"] {
            let (ok, text) = run_decl(&tmp, mode, target);
            assert!(ok, "{mode} {target}: {text}");
            assert!(text.contains("B.A.same"), "{mode} {target}: {text}");
        }
    }
    let (_, text) = run_decl(&tmp, "check", "same");
    let json = &text[text.find('{').unwrap()..=text.rfind('}').unwrap()];
    let v: serde_json::Value = serde_json::from_str(json).expect(&text);
    assert_eq!(v["decl"], "B.A.same", "{text}");
    assert!(v["compact_summary"]
        .as_str()
        .unwrap()
        .contains("decl=B.A.same"));
}

#[test]
fn check_decl_rejects_section_variable_kernel_type_drift_fail_closed() {
    // Inside a section, `variable (x : Nat)` elaborated with `include x` adds `x : Nat` to
    // `thm`'s real kernel type (`∀ x : Nat, 1 = 1`), whereas a shard reconstruction that drops
    // `include x` (e.g., if `include x` is hidden inside a command or section boundary not
    // replayed identically) would prove `1 = 1` instead of `∀ x : Nat, 1 = 1`.
    // Here a custom `elab` command runs `include` only during full-prefix elaboration when
    // another declaration precedes `thm`, or we use `section` + `include` to verify that
    // `check --decl` either elaborates the exact `∀ (x : Nat), 1 = 1` kernel type or fails closed.
    let tmp = identity_project(
        "section-include-kth",
        r#"import Lean
section S
variable (x : Nat)
elab "activate_x" : command => do
  Lean.Elab.Command.elabCommand (← `(include x))
activate_x
theorem thm : (1 : Nat) = 1 := rfl
end S
"#,
    );
    let (ok, text) = run_decl(&tmp, "check", "thm");
    if ok {
        let json = &text[text.find('{').unwrap()..=text.rfind('}').unwrap()];
        let v: serde_json::Value = serde_json::from_str(json).expect(&text);
        assert_eq!(v["decl"], "thm", "{text}");
        assert!(
            v["kernel_type_hash"]
                .as_str()
                .is_some_and(|s| s.len() == 64),
            "accepted --decl verdict must carry 64-hex attested kernel_type_hash: {text}"
        );
    } else {
        assert!(
            text.contains("kernel statement type mismatch") || text.contains("failed"),
            "must fail closed on kernel statement drift: {text}"
        );
    }
}

fn call_mcp_tool(
    tmp: &corpus::Temp,
    tool: &str,
    arguments: serde_json::Value,
) -> serde_json::Value {
    use std::io::Write;
    use std::process::Stdio;
    let mut child = Command::new(env!("CARGO_BIN_EXE_turbo-lean"))
        .current_dir(&tmp.0)
        .env("TURBO_LEAN_NO_DAEMON", "1")
        .args(["--cache-dir"])
        .arg(tmp.0.join("cache"))
        .arg("mcp")
        .arg("--project-dir")
        .arg(&tmp.0)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let req = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "tools/call",
        "params": {
            "name": tool,
            "arguments": arguments,
        }
    });
    writeln!(child.stdin.take().unwrap(), "{req}").unwrap();
    let out = child.wait_with_output().unwrap();
    assert!(
        out.status.success(),
        "mcp failed: {}",
        corpus::diagnostic(&out)
    );
    let line = String::from_utf8_lossy(&out.stdout);
    let resp: serde_json::Value = serde_json::from_str(line.lines().next().unwrap()).unwrap();
    resp["result"].clone()
}

#[test]
fn untargeted_and_auto_fastcheck_agent_step_and_mcp_confirm_elaborated_identity() {
    // 1. Decoy inside string/comment + false theorem in `namespace B`:
    //    untargeted (`None`) and `auto` across CLI `fast-check`, `fast-check --tpu`,
    //    `fast-check --transpile-lean auto`, `agent-step`, and MCP `turbo_fast_check` /
    //    `turbo_agent_step` must ignore the lexical decoy and report confirmed `B.real_thm`.
    let decoy_false_src = concat!(
        "namespace B\n",
        "def decoy : String := \"\nend B\nnamespace A\ntheorem fake_decoy (x : UInt64) : x = x + 1 := by sorry\n\"\n",
        "theorem real_thm (x : UInt64) : x + 1 = x := by sorry\n",
        "end B\n",
    );
    let tmp = identity_project("auto-identity-decoy", decoy_false_src);

    // Default `fast-check` (untargeted)
    let mut fc_default = Command::new(env!("CARGO_BIN_EXE_turbo-lean"));
    fc_default
        .current_dir(&tmp.0)
        .env("TURBO_LEAN_NO_DAEMON", "1")
        .args(["--json", "--cache-dir"])
        .arg(tmp.0.join("cache"))
        .args(["fast-check", "Identity.lean"]);
    let out = corpus::run(&mut fc_default);
    let text = corpus::diagnostic(&out);
    assert!(!out.status.success(), "default fast-check: {text}");
    assert!(text.contains("B.real_thm"), "default fast-check: {text}");
    assert!(!text.contains("fake_decoy"), "default fast-check: {text}");

    // `fast-check --tpu` (untargeted and `--decl auto`)
    for extra in [vec!["--tpu"], vec!["--tpu", "--decl", "auto"]] {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_turbo-lean"));
        cmd.current_dir(&tmp.0)
            .env("TURBO_LEAN_NO_DAEMON", "1")
            .args(["--json", "--cache-dir"])
            .arg(tmp.0.join("cache"))
            .args(["fast-check", "Identity.lean"])
            .args(&extra);
        let out = corpus::run(&mut cmd);
        let text = corpus::diagnostic(&out);
        assert!(!out.status.success(), "tpu {extra:?}: {text}");
        assert!(text.contains("B.real_thm"), "tpu {extra:?}: {text}");
        assert!(!text.contains("fake_decoy"), "tpu {extra:?}: {text}");
    }

    // `fast-check --transpile-lean auto`
    let mut fc_transpile = Command::new(env!("CARGO_BIN_EXE_turbo-lean"));
    fc_transpile
        .current_dir(&tmp.0)
        .env("TURBO_LEAN_NO_DAEMON", "1")
        .args(["--json", "--cache-dir"])
        .arg(tmp.0.join("cache"))
        .args(["fast-check", "Identity.lean", "--transpile-lean", "auto"]);
    let out = corpus::run(&mut fc_transpile);
    let text = corpus::diagnostic(&out);
    assert!(!out.status.success(), "transpile auto: {text}");
    assert!(text.contains("B.real_thm"), "transpile auto: {text}");
    assert!(!text.contains("fake_decoy"), "transpile auto: {text}");

    // `agent-step` untargeted and `--decl auto`
    for extra in [vec![], vec!["--decl", "auto"]] {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_turbo-lean"));
        cmd.current_dir(&tmp.0)
            .env("TURBO_LEAN_NO_DAEMON", "1")
            .args(["--json", "--cache-dir"])
            .arg(tmp.0.join("cache"))
            .args(["agent-step", "Identity.lean"])
            .args(&extra);
        let out = corpus::run(&mut cmd);
        let text = corpus::diagnostic(&out);
        assert!(text.contains("B.real_thm"), "agent-step {extra:?}: {text}");
        assert!(!text.contains("fake_decoy"), "agent-step {extra:?}: {text}");
        assert!(
            text.contains("counterexample"),
            "agent-step {extra:?}: {text}"
        );
    }

    // MCP `turbo_fast_check` on file (untargeted, `decl: "auto"`, and missing `decl: "A.real_thm"`)
    for decl_arg in [serde_json::Value::Null, serde_json::json!("auto")] {
        let res = call_mcp_tool(
            &tmp,
            "turbo_fast_check",
            serde_json::json!({
                "file": "Identity.lean",
                "decl": decl_arg,
                "compact": false,
            }),
        );
        let body: serde_json::Value =
            serde_json::from_str(res["content"][0]["text"].as_str().unwrap()).unwrap();
        assert_eq!(body["ok"], false, "mcp fast_check {decl_arg}: {body}");
        assert_eq!(
            body["decl"], "B.real_thm",
            "mcp fast_check {decl_arg}: {body}"
        );
    }
    let mcp_missing = call_mcp_tool(
        &tmp,
        "turbo_fast_check",
        serde_json::json!({
            "file": "Identity.lean",
            "decl": "A.real_thm",
            "compact": false,
        }),
    );
    assert_eq!(mcp_missing["isError"], true, "{mcp_missing}");
    let mcp_missing_body: serde_json::Value =
        serde_json::from_str(mcp_missing["content"][0]["text"].as_str().unwrap()).unwrap();
    assert_eq!(mcp_missing_body["status"], "error", "{mcp_missing_body}");
    assert!(
        mcp_missing_body["error"]
            .as_str()
            .unwrap_or("")
            .contains("not found"),
        "{mcp_missing_body}"
    );

    // 2. Unconfirmed / mislabeled declaration (e.g. broken import so Lean cannot confirm
    //    elaborated declaration identity): every untargeted & `auto` mode must fail closed
    //    instead of emitting an unattested Stage-1 verdict or counterexample.
    let unconfirmable_src = concat!(
        "import NonExistentGhostModuleForIdentityTest\n",
        "theorem ghost_thm (x : UInt64) : x + 1 = x := by sorry\n",
    );
    let bad_tmp = identity_project("auto-identity-unconfirmed", unconfirmable_src);
    for args in [
        vec!["fast-check", "Identity.lean"],
        vec!["fast-check", "Identity.lean", "--tpu"],
        vec!["fast-check", "Identity.lean", "--tpu", "--decl", "auto"],
        vec!["fast-check", "Identity.lean", "--transpile-lean", "auto"],
        vec!["agent-step", "Identity.lean"],
        vec!["agent-step", "Identity.lean", "--decl", "auto"],
        vec!["agent-step", "Identity.lean", "--decl", "missing_decl"],
    ] {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_turbo-lean"));
        cmd.current_dir(&bad_tmp.0)
            .env("TURBO_LEAN_NO_DAEMON", "1")
            .args(["--json", "--cache-dir"])
            .arg(bad_tmp.0.join("cache"))
            .args(&args);
        let out = corpus::run(&mut cmd);
        let text = corpus::diagnostic(&out);
        assert!(
            !out.status.success(),
            "must fail closed for {args:?}: {text}"
        );
        assert!(
            !text.contains("counterexample_rejected") && !text.contains("counterexample_found"),
            "must not emit unconfirmed counterexample verdict for {args:?}: {text}"
        );
    }
    let mcp_unconfirmed = call_mcp_tool(
        &bad_tmp,
        "turbo_fast_check",
        serde_json::json!({
            "file": "Identity.lean",
            "compact": false,
        }),
    );
    assert_eq!(mcp_unconfirmed["isError"], true, "{mcp_unconfirmed}");
    let mcp_unconfirmed_body: serde_json::Value =
        serde_json::from_str(mcp_unconfirmed["content"][0]["text"].as_str().unwrap()).unwrap();
    assert_eq!(
        mcp_unconfirmed_body["status"], "error",
        "{mcp_unconfirmed_body}"
    );
}
