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

#[test]
fn anonymous_local_and_private_instances_match_kernel_statement_hashes() {
    let tmp = identity_project(
        "anon-local-instance-kth",
        concat!(
            "namespace Foo\n",
            "section\n",
            "local instance : HAdd UInt8 UInt8 UInt8 where\n",
            "  hAdd a _ := a\n",
            "private local instance : HSub UInt8 UInt8 UInt8 where\n",
            "  hSub _ b := b\n",
            "theorem local_inst_valid (x : UInt8) : x + 1 = x ∧ x - 1 = 1 := ⟨rfl, rfl⟩\n",
            "end\n",
            "end Foo\n",
        ),
    );
    for mode in ["check", "agent-step"] {
        let (ok, text) = run_decl(&tmp, mode, "Foo.local_inst_valid");
        assert!(ok, "{mode}: {text}");
        let json = &text[text.find('{').unwrap()..=text.rfind('}').unwrap()];
        let v: serde_json::Value = serde_json::from_str(json).expect(&text);
        assert_eq!(v["decl"], "Foo.local_inst_valid", "{text}");
        assert!(
            matches!(
                v["status"].as_str(),
                Some("theorem_verified" | "theorem_cache_hit")
            ),
            "{text}"
        );
    }

    // Stage-1 fast-check (both CLI and MCP `turbo_fast_check` file mode) must fail closed on
    // files containing `local instance` / untrusted elaboration context instead of emitting
    // `verified: true` or a false counterexample via a synthetic `:= by sorry` fallback.
    let (fc_ok, fc_text) = run_decl(&tmp, "fast-check", "Foo.local_inst_valid");
    assert!(!fc_ok, "fast-check must fail closed: {fc_text}");
    assert!(
        !fc_text.contains("counterexample_found") && !fc_text.contains("\"verified\":true"),
        "fast-check must not verify or refute untrusted context: {fc_text}"
    );
    for decl_arg in [
        serde_json::Value::Null,
        serde_json::json!("Foo.local_inst_valid"),
    ] {
        let mcp_res = call_mcp_tool(
            &tmp,
            "turbo_fast_check",
            serde_json::json!({
                "file": "Identity.lean",
                "decl": decl_arg,
                "compact": false,
            }),
        );
        assert_eq!(mcp_res["isError"], true, "{mcp_res}");
        let body: serde_json::Value =
            serde_json::from_str(mcp_res["content"][0]["text"].as_str().unwrap()).unwrap();
        assert_eq!(body["ok"], false, "{body}");
        assert_eq!(body["status"], "error", "{body}");
        assert_ne!(body["verified"], true, "{body}");
    }
}

#[test]
fn multiline_theorem_and_modifier_headers_preserve_identity_and_fail_closed_shadow() {
    let valid_multiline_src = concat!(
        "namespace Multi\n",
        "private\n",
        "theorem\n",
        "  split_hdr_ok\n",
        "  (x : UInt64)\n",
        "  : x = x := rfl\n",
        "end Multi\n",
    );
    let tmp = identity_project("multiline-hdr-identity", valid_multiline_src);

    for mode in ["check", "fast-check", "agent-step"] {
        let (ok, text) = run_decl(&tmp, mode, "Multi.split_hdr_ok");
        assert!(ok, "{mode} Multi.split_hdr_ok: {text}");
        assert!(text.contains("Multi.split_hdr_ok"), "{mode}: {text}");
    }
    let mcp_ok = call_mcp_tool(
        &tmp,
        "turbo_fast_check",
        serde_json::json!({
            "file": "Identity.lean",
            "decl": "Multi.split_hdr_ok",
            "compact": false,
        }),
    );
    assert_ne!(mcp_ok["isError"], true, "{mcp_ok}");
    let mcp_ok_body: serde_json::Value =
        serde_json::from_str(mcp_ok["content"][0]["text"].as_str().unwrap()).unwrap();
    assert_eq!(mcp_ok_body["ok"], true, "{mcp_ok_body}");

    let cex_multiline_src = concat!(
        "namespace Multi\n",
        "theorem\n",
        "  split_hdr_cex\n",
        "  (x : UInt64)\n",
        "  : x + 1 = x := by sorry\n",
        "end Multi\n",
    );
    let cex_tmp = identity_project("multiline-hdr-cex", cex_multiline_src);
    let (cex_ok, cex_text) = run_decl(&cex_tmp, "fast-check", "Multi.split_hdr_cex");
    assert!(!cex_ok, "expected cex: {cex_text}");
    assert!(cex_text.contains("Multi.split_hdr_cex"), "{cex_text}");
    assert!(cex_text.contains("counterexample"), "{cex_text}");

    let attr_multiline_src = concat!(
        "namespace AttrMulti\n",
        "@[\n  simp\n]\n",
        "theorem\n",
        "  attr_hdr_ok\n",
        "  (x : Nat)\n",
        "  : x + 0 = x := Nat.add_zero x\n",
        "end AttrMulti\n",
    );
    let attr_tmp = identity_project("multiline-attr-identity", attr_multiline_src);
    let (attr_check_ok, attr_check_text) = run_decl(&attr_tmp, "check", "AttrMulti.attr_hdr_ok");
    assert!(
        attr_check_ok,
        "check AttrMulti.attr_hdr_ok: {attr_check_text}"
    );
    assert!(
        attr_check_text.contains("AttrMulti.attr_hdr_ok"),
        "{attr_check_text}"
    );
    let (attr_fc_ok, attr_fc_text) = run_decl(&attr_tmp, "fast-check", "AttrMulti.attr_hdr_ok");
    assert!(
        !attr_fc_ok,
        "attribute header must fail closed in Stage-1 fast-check: {attr_fc_text}"
    );

    let shadowed_multiline_src = concat!(
        "private def\n",
        "  add (a b : UInt64) : UInt64 := a\n",
        "theorem\n",
        "  multiline_untrusted (x : UInt64) : x = x := rfl\n",
    );
    let bad_tmp = identity_project("multiline-shadow-untrusted", shadowed_multiline_src);
    let (bad_fc_ok, bad_fc_text) = run_decl(&bad_tmp, "fast-check", "multiline_untrusted");
    assert!(
        !bad_fc_ok,
        "multiline shadow must fail closed: {bad_fc_text}"
    );
    let mcp_bad = call_mcp_tool(
        &bad_tmp,
        "turbo_fast_check",
        serde_json::json!({
            "file": "Identity.lean",
            "decl": "multiline_untrusted",
            "compact": false,
        }),
    );
    assert_eq!(mcp_bad["isError"], true, "{mcp_bad}");
    let mcp_bad_body: serde_json::Value =
        serde_json::from_str(mcp_bad["content"][0]["text"].as_str().unwrap()).unwrap();
    assert_eq!(mcp_bad_body["status"], "error", "{mcp_bad_body}");

    let notation_multiline_src = concat!(
        "local\n",
        "  notation \"⊕\" => HAdd.hAdd\n",
        "theorem\n",
        "  multiline_not_untrusted (x : UInt64) : x = x := rfl\n",
    );
    let not_tmp = identity_project("multiline-notation-untrusted", notation_multiline_src);
    let (not_check_ok, not_check_text) = run_decl(&not_tmp, "check", "multiline_not_untrusted");
    assert!(
        not_check_ok,
        "check multiline_not_untrusted: {not_check_text}"
    );
    let (not_fc_ok, _) = run_decl(&not_tmp, "fast-check", "multiline_not_untrusted");
    assert!(!not_fc_ok);

    // Targetless `lakefile.toml` with multi-file imports (`Dep.lean` + `Main.lean` importing
    // `Dep`): checking `Dep.lean` (with dependent recheck of `Main.lean`) and checking `Main.lean`
    // after `Dep.olean` becomes stale must purge standalone `Dep.olean` instead of calling
    // `lake build Dep` (`unknown target`).
    let dep_tmp = corpus::Temp::new("targetless-lakefile-dep-check");
    fs::write(
        dep_tmp.0.join("lean-toolchain"),
        include_str!("../../../lean/lean-toolchain"),
    )
    .unwrap();
    fs::write(
        dep_tmp.0.join("lakefile.toml"),
        "name = \"targetless\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    let olean_dir = dep_tmp.0.join(".lake/build/lib/lean");
    fs::create_dir_all(&olean_dir).unwrap();
    fs::write(dep_tmp.0.join("Dep.lean"), "def depVal : Nat := 7\n").unwrap();
    let lean_status = Command::new("lean")
        .current_dir(&dep_tmp.0)
        .args(["Dep.lean", "-o"])
        .arg(olean_dir.join("Dep.olean"))
        .status()
        .unwrap();
    assert!(lean_status.success());
    fs::write(
        dep_tmp.0.join("Main.lean"),
        "import Dep\ntheorem uses_dep : depVal = 7 := rfl\n",
    )
    .unwrap();
    let mut dep_cmd = Command::new(env!("CARGO_BIN_EXE_turbo-lean"));
    dep_cmd
        .current_dir(&dep_tmp.0)
        .env("TURBO_LEAN_NO_DAEMON", "1")
        .args(["--json", "--cache-dir"])
        .arg(dep_tmp.0.join("cache"))
        .args(["check", "Main.lean", "--project-dir"])
        .arg(&dep_tmp.0);
    let dep_out = corpus::run(&mut dep_cmd);
    let dep_text = corpus::diagnostic(&dep_out);
    assert!(
        dep_out.status.success(),
        "targetless lakefile.toml multi-file check must succeed without `unknown target`: {dep_text}"
    );
    assert!(
        dep_text.contains("\"status\": \"file_verified\""),
        "{dep_text}"
    );
    assert!(!dep_text.contains("unknown target"), "{dep_text}");

    // Dependent recheck when `Dep.lean` changes (triggers `lake_recheck_dependents_with_store`
    // standalone path under targetless `lakefile.toml`).
    std::thread::sleep(std::time::Duration::from_millis(1100));
    fs::write(
        dep_tmp.0.join("Dep.lean"),
        "def depVal : Nat := 7\ntheorem dep_eq : depVal = 7 := rfl\n",
    )
    .unwrap();
    let mut recheck_cmd = Command::new(env!("CARGO_BIN_EXE_turbo-lean"));
    recheck_cmd
        .current_dir(&dep_tmp.0)
        .env("TURBO_LEAN_NO_DAEMON", "1")
        .args(["--json", "--cache-dir"])
        .arg(dep_tmp.0.join("cache"))
        .args(["check", "Dep.lean", "--project-dir"])
        .arg(&dep_tmp.0);
    let recheck_out = corpus::run(&mut recheck_cmd);
    let recheck_text = corpus::diagnostic(&recheck_out);
    assert!(
        recheck_out.status.success(),
        "targetless lakefile.toml dependent recheck must succeed without `unknown target`: {recheck_text}"
    );
    assert!(!recheck_text.contains("unknown target"), "{recheck_text}");

    // Stale `Dep.olean` on `check Main.lean`: `ensure_project_imports_fresh_for_check` must purge
    // the non-target `Dep.olean` rather than calling `lake build Dep` (`unknown target`).
    let mut stale_cmd = Command::new(env!("CARGO_BIN_EXE_turbo-lean"));
    stale_cmd
        .current_dir(&dep_tmp.0)
        .env("TURBO_LEAN_NO_DAEMON", "1")
        .args(["--json", "--cache-dir"])
        .arg(dep_tmp.0.join("cache"))
        .args(["check", "Main.lean", "--project-dir"])
        .arg(&dep_tmp.0);
    let stale_out = corpus::run(&mut stale_cmd);
    let stale_text = corpus::diagnostic(&stale_out);
    assert!(
        !stale_text.contains("unknown target"),
        "stale import under targetless lakefile.toml must never call `lake build Dep`: {stale_text}"
    );
    assert!(
        !olean_dir.join("Dep.olean").exists(),
        "stale standalone Dep.olean should have been purged"
    );
}
