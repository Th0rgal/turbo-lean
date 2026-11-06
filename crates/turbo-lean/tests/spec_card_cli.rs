use serde_json::Value;
use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

fn fixture(name: &str) -> PathBuf {
    let root = std::env::temp_dir().join(format!(
        "turbo_spec_card_{name}_{}_{}",
        std::process::id(),
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    fs::create_dir_all(&root).unwrap();
    root
}

fn run(args: &[&str]) -> Output {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_turbo-lean"));
    cmd.args(args)
        .env("TURBO_LEAN_TELEMETRY", "off")
        .env("TURBO_LEAN_NO_REMOTE_TELEMETRY", "1")
        .env("TURBO_LEAN_NO_DAEMON", "1");
    cmd.output().unwrap()
}

fn write_spec(dir: &std::path::Path, name: &str, src: &str) -> PathBuf {
    let path = dir.join(name);
    fs::write(&path, src).unwrap();
    path
}

const TIGHT: &str = r#"
def bounded (n : Nat) : Prop := n < 4

theorem bounded_succ (n : Nat) (h : bounded n) : bounded (n + 1) ∨ n = 3 := by
  omega
"#;

#[test]
fn spec_card_json_labels_source_tier_and_local_def() {
    let dir = fixture("tight");
    let path = write_spec(&dir, "Tight.lean", TIGHT);
    let out = run(&[
        "--json",
        "spec-card",
        path.to_str().unwrap(),
        "--decl",
        "bounded_succ",
    ]);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        out.status.success(),
        "stdout:\n{stdout}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let report: Value = serde_json::from_str(&stdout).unwrap();
    assert_eq!(report["analysis_tier"], "source_syntactic");
    assert_eq!(report["ok"], true);
    assert_eq!(report["status"], "ok");
    assert!(report["unchecked_boundaries"].as_array().unwrap().len() >= 4);
    let card = &report["cards"][0];
    assert_eq!(card["decl"], "bounded_succ");
    assert_eq!(card["visibility"], "public");
    assert_eq!(card["verdict"], "TIGHT");
    assert_eq!(card["contract"]["hypotheses"][0]["id"], "H_1");
    assert_eq!(card["contract"]["conclusion"]["id"], "C");
    assert_eq!(
        card["referenced_definitions"]["label"],
        "syntactic_statement_refs"
    );
    let locals = card["referenced_definitions"]["local_defs"]
        .as_array()
        .unwrap();
    assert!(locals
        .iter()
        .any(|row| row["name"] == "bounded"
            && row["body_preview"].as_str().unwrap().contains("n < 4")));
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn spec_card_human_output_and_missing_decl_exit() {
    let dir = fixture("human");
    let path = write_spec(&dir, "Tight.lean", TIGHT);
    let out = run(&["spec-card", path.to_str().unwrap()]);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(out.status.success(), "{stdout}");
    assert!(stdout.contains("tier=source_syntactic"));
    assert!(stdout.contains("TIGHT"));
    assert!(stdout.contains("H_1"));
    assert!(stdout.contains("syntactic_statement_refs"));
    assert!(stdout.contains("unchecked:"));
    let missing = run(&[
        "--json",
        "spec-card",
        path.to_str().unwrap(),
        "--decl",
        "missing_decl",
    ]);
    assert!(!missing.status.success());
    let report: Value = serde_json::from_str(&String::from_utf8_lossy(&missing.stdout)).unwrap();
    assert_eq!(report["ok"], false);
    assert_eq!(report["summary"]["matched_decls"], 0);
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn spec_card_public_only_hides_private_and_flags_sorry() {
    let dir = fixture("private");
    let path = write_spec(
        &dir,
        "Priv.lean",
        r#"
module

private theorem hidden (n : Nat) : n = n := by
  sorry

public theorem shown (n : Nat) (h : n < 2) : n = 0 ∨ n = 1 := by
  omega
"#,
    );
    let out = run(&[
        "--json",
        "spec-card",
        path.to_str().unwrap(),
        "--public-only",
    ]);
    let stdout = String::from_utf8_lossy(&out.stdout);
    let report: Value = serde_json::from_str(stdout.trim()).unwrap_or_else(|_| {
        panic!(
            "status {:?} stdout:\n{stdout}\nstderr:\n{}",
            out.status.code(),
            String::from_utf8_lossy(&out.stderr)
        )
    });
    assert_eq!(report["summary"]["hidden_by_public_only"], 1);
    let cards = report["cards"].as_array().unwrap();
    assert_eq!(cards.len(), 1);
    assert_eq!(cards[0]["decl"], "shown");
    assert_eq!(cards[0]["visibility"], "public");
    let flags = cards[0]["hygiene"]["source_flags"].as_array().unwrap();
    assert!(flags.iter().any(|flag| flag == "sorry"));
    assert!(!out.status.success(), "file-level sorry must fail the card");
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn spec_card_directory_keeps_per_file_verdicts() {
    let dir = fixture("dir");
    let nested = dir.join("specs");
    fs::create_dir_all(&nested).unwrap();
    write_spec(&nested, "Tight.lean", TIGHT);
    write_spec(
        &nested,
        "Vacuous.lean",
        "theorem gone (h : False) : True := by\n  cases h\n",
    );
    let out = run(&["--json", "spec-card", nested.to_str().unwrap()]);
    let report: Value = serde_json::from_str(&String::from_utf8_lossy(&out.stdout)).unwrap();
    assert!(!out.status.success());
    let cards = report["cards"].as_array().unwrap();
    assert_eq!(cards.len(), 2);
    assert!(cards.iter().any(|card| card["decl"] == "bounded_succ"
        && card["verdict"] == "TIGHT"
        && card["file"].as_str().unwrap().ends_with("Tight.lean")));
    assert!(cards.iter().any(|card| card["decl"] == "gone"
        && card["verdict"] == "VACUOUS"
        && card["file"].as_str().unwrap().ends_with("Vacuous.lean")));
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn spec_card_public_only_does_not_cross_namespaces() {
    let dir = fixture("ns");
    let path = write_spec(
        &dir,
        "Ns.lean",
        r#"
module

public theorem same (n : Nat) (h : n < 2) : n = 0 ∨ n = 1 := by
  omega

namespace Hidden

private theorem same (n : Nat) (h : n < 2) : n = 0 ∨ n = 1 := by
  omega

end Hidden
"#,
    );
    let out = run(&[
        "--json",
        "spec-card",
        path.to_str().unwrap(),
        "--public-only",
    ]);
    let report: Value = serde_json::from_str(&String::from_utf8_lossy(&out.stdout)).unwrap();
    assert!(out.status.success(), "{}", report);
    let cards = report["cards"].as_array().unwrap();
    assert_eq!(cards.len(), 1);
    assert_eq!(cards[0]["decl"], "same");
    assert_eq!(report["summary"]["hidden_by_public_only"], 1);
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn spec_card_refuses_tight_when_assumptions_are_unmodeled() {
    let dir = fixture("assumptions");
    let path = write_spec(
        &dir,
        "Assumptions.lean",
        r#"
section
variable (p : Prop)

theorem uses_var (n : Nat) (h : n < 2) : n = 0 ∨ n = 1 := by
  omega

end

theorem fact_false [Fact False] (n : Nat) (h : n < 2) : n = 0 ∨ n = 1 := by
  omega

theorem lawful {α : Type} [BEq α] [LawfulBEq α] (x : α) (h : x == x) : x == x := by
  exact h
"#,
    );
    let out = run(&["--json", "spec-card", path.to_str().unwrap()]);
    let stdout = String::from_utf8_lossy(&out.stdout);
    let report: Value = serde_json::from_str(&stdout).unwrap_or_else(|_| panic!("{stdout}"));
    assert!(!out.status.success());
    let cards = report["cards"].as_array().unwrap();
    let uses_var = cards
        .iter()
        .find(|card| card["decl"] == "uses_var")
        .unwrap();
    assert_eq!(uses_var["verdict"], "UNCHECKED_ASSUMPTIONS");
    assert_eq!(uses_var["contract"]["extraction_complete"], false);
    assert!(uses_var["contract"]["context_assumptions"][0]
        .as_str()
        .unwrap()
        .contains("variable (p : Prop)"));
    let fact = cards
        .iter()
        .find(|card| card["decl"] == "fact_false")
        .unwrap();
    assert_eq!(fact["verdict"], "UNCHECKED_ASSUMPTIONS");
    assert_eq!(fact["contract"]["instance_binders"][0], "Fact False");
    let lawful = cards.iter().find(|card| card["decl"] == "lawful").unwrap();
    assert_eq!(lawful["contract"]["extraction_complete"], true);
    assert_eq!(lawful["contract"]["instance_binders"][0], "BEq α");
    assert_eq!(lawful["contract"]["instance_binders"][1], "LawfulBEq α");
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn spec_card_prefixed_decls_and_sections_fail_closed() {
    let dir = fixture("prefixed");
    let path = write_spec(
        &dir,
        "Prefixed.lean",
        r#"
section Outer
variable (h : False)

public section
theorem nested (n : Nat) (hn : n < 2) : n = 0 ∨ n = 1 := by
  omega
end

@[simp] public theorem tagged [Fact False] (n : Nat) (hn : n < 2) : n = 0 ∨ n = 1 := by
  omega

end Outer

variable (bad : False) in
theorem scoped_in (n : Nat) (hn : n < 2) : n = 0 ∨ n = 1 := by
  omega

variable (gone : False) in
section Scoped
theorem inside (n : Nat) (hn : n < 2) : n = 0 ∨ n = 1 := by
  omega
end

theorem clean_after_in (n : Nat) (hn : n < 2) : n = 0 ∨ n = 1 := by
  omega
"#,
    );
    let out = run(&["--json", "spec-card", path.to_str().unwrap()]);
    let report: Value = serde_json::from_str(&String::from_utf8_lossy(&out.stdout)).unwrap();
    assert!(!out.status.success(), "{report}");
    for name in ["nested", "tagged", "scoped_in", "inside"] {
        let card = report["cards"]
            .as_array()
            .unwrap()
            .iter()
            .find(|card| card["decl"] == name)
            .unwrap();
        assert_eq!(card["verdict"], "UNCHECKED_ASSUMPTIONS", "{name}: {card}");
        assert_eq!(card["contract"]["extraction_complete"], false);
    }
    let clean = report["cards"]
        .as_array()
        .unwrap()
        .iter()
        .find(|card| card["decl"] == "clean_after_in")
        .unwrap();
    assert_eq!(clean["verdict"], "TIGHT", "{clean}");
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn spec_card_keeps_assumptions_across_nested_scopes_and_duplicate_names() {
    let dir = fixture("scopes");
    let path = write_spec(
        &dir,
        "Scopes.lean",
        r#"
section Outer
variable (h : False)

namespace A.B
end A.B

theorem after_ns (n : Nat) (hn : n < 2) : n = 0 ∨ n = 1 := by
  omega

section Inner
variable (q : Prop)
end Outer

theorem after_outer (n : Nat) (hn : n < 2) : n = 0 ∨ n = 1 := by
  omega

section First
variable (p : Prop)
theorem same_name (n : Nat) (hn : n < 2) : n = 0 ∨ n = 1 := by
  omega
end First

section Second
theorem same_name (n : Nat) (hn : n < 2) : n = 0 ∨ n = 1 := by
  omega
end Second
"#,
    );
    let out = run(&["--json", "spec-card", path.to_str().unwrap()]);
    let report: Value = serde_json::from_str(&String::from_utf8_lossy(&out.stdout)).unwrap();
    let cards = report["cards"].as_array().unwrap();
    let after_ns = cards
        .iter()
        .find(|card| card["decl"] == "after_ns")
        .unwrap();
    assert_eq!(after_ns["verdict"], "UNCHECKED_ASSUMPTIONS");
    let after_outer = cards
        .iter()
        .find(|card| card["decl"] == "after_outer")
        .unwrap();
    assert_eq!(after_outer["contract"]["extraction_complete"], true);
    let duplicates = cards
        .iter()
        .filter(|card| card["decl"] == "same_name")
        .collect::<Vec<_>>();
    assert_eq!(duplicates.len(), 2);
    assert_eq!(duplicates[0]["contract"]["extraction_complete"], false);
    assert_eq!(duplicates[1]["contract"]["extraction_complete"], true);
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn spec_card_reads_guillemet_names_and_literals_inside_binders() {
    let dir = fixture("lexemes");
    let path = write_spec(
        &dir,
        "Lexemes.lean",
        "theorem «bad» [Fact False] (n : Nat) (h : n < 2) : n = 0 ∨ n = 1 := by\n  omega\n\ntheorem quoted (s : String := \")\") [Fact False] (n : Nat) (h : n < 2) : n = 0 ∨ n = 1 := by\n  omega\n",
    );
    let out = run(&["--json", "spec-card", path.to_str().unwrap()]);
    let report: Value = serde_json::from_str(&String::from_utf8_lossy(&out.stdout)).unwrap();
    assert!(!out.status.success(), "{report}");
    let cards = report["cards"].as_array().unwrap();
    assert!(cards
        .iter()
        .all(|card| card["verdict"] == "UNCHECKED_ASSUMPTIONS"
            && card["contract"]["instance_binders"][0] == "Fact False"));
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn spec_card_does_not_treat_nonempty_false_as_standard() {
    let dir = fixture("nonempty");
    let path = write_spec(
        &dir,
        "Nonempty.lean",
        r#"
inductive Bad where | mk

theorem vacuous [Nonempty False] (n : Nat) (h : n < 2) : n = 0 ∨ n = 1 := by
  omega

theorem inhabited_false [Inhabited False] (n : Nat) (h : n < 2) : n = 0 ∨ n = 1 := by
  omega

theorem named_inst [BEq : Fact False] (n : Nat) (h : n < 2) : n = 0 ∨ n = 1 := by
  omega

theorem concrete_lawful [LawfulBEq Bad] (n : Nat) (h : n < 2) : n = 0 ∨ n = 1 := by
  omega

theorem strict_implicit ⦃h : False⦄ (n : Nat) (hn : n < 2) : n = 0 ∨ n = 1 := by
  omega
"#,
    );
    let out = run(&["--json", "spec-card", path.to_str().unwrap()]);
    let report: Value = serde_json::from_str(&String::from_utf8_lossy(&out.stdout)).unwrap();
    assert!(!out.status.success(), "{report}");
    let cards = report["cards"].as_array().unwrap();
    assert_eq!(cards.len(), 5, "{report}");
    assert!(
        cards
            .iter()
            .all(|card| card["contract"]["extraction_complete"] == false
                && card["verdict"] != "TIGHT"),
        "{report}"
    );
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn spec_card_rejects_public_namespace_bypass_and_invalid_policy() {
    let dir = fixture("pubns");
    let path = write_spec(
        &dir,
        "PubNs.lean",
        r#"
module

public theorem clean (n : Nat) (h : n < 2) : n = 0 ∨ n = 1 := by
  omega

public namespace Outer
public theorem backdoor [Fact False] (n : Nat) (h : n < 2) : n = 0 ∨ n = 1 := by
  omega
end Outer
"#,
    );
    let out = run(&[
        "--json",
        "spec-card",
        path.to_str().unwrap(),
        "--public-only",
    ]);
    let report: Value = serde_json::from_str(&String::from_utf8_lossy(&out.stdout)).unwrap();
    assert!(!out.status.success(), "{report}");
    let cards = report["cards"].as_array().unwrap();
    assert!(
        cards
            .iter()
            .any(|card| card["decl"] == "Outer.backdoor"
                && card["verdict"] == "UNCHECKED_ASSUMPTIONS"),
        "{report}"
    );
    assert_eq!(report["summary"]["extraction_complete"], false, "{report}");

    let bad_policy = run(&[
        "--json",
        "spec-card",
        path.to_str().unwrap(),
        "--policy",
        "typo-policy",
    ]);
    assert!(!bad_policy.status.success());

    let scopes = write_spec(
        &dir,
        "BareEnds.lean",
        r#"
section Outer
variable (h : False)
namespace A.B
end
end
theorem still_outer (n : Nat) (hn : n < 2) : n = 0 ∨ n = 1 := by
  omega
end Outer
"#,
    );
    let scopes_out = run(&["--json", "spec-card", scopes.to_str().unwrap()]);
    let scopes_report: Value =
        serde_json::from_str(&String::from_utf8_lossy(&scopes_out.stdout)).unwrap();
    assert!(!scopes_out.status.success(), "{scopes_report}");
    assert_eq!(
        scopes_report["cards"][0]["verdict"],
        "UNCHECKED_ASSUMPTIONS"
    );

    let bad_dir = dir.join("BrokenDir");
    fs::create_dir_all(&bad_dir).unwrap();
    fs::write(bad_dir.join("NotUtf8.lean"), [0xff, 0xfe, 0xfd]).unwrap();
    let unreadable = run(&["--json", "spec-card", bad_dir.to_str().unwrap()]);
    assert!(!unreadable.status.success());
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn spec_card_public_only_unresolved_does_not_hide_a_mixed_run() {
    let dir = fixture("unresolved");
    let broken = write_spec(
        &dir,
        "Broken.lean",
        "my_custom_cmd\ntheorem hidden (n : Nat) : n = n := rfl\n",
    );
    let shown = write_spec(&dir, "Shown.lean", TIGHT);
    let out = run(&[
        "--json",
        "spec-card",
        broken.to_str().unwrap(),
        shown.to_str().unwrap(),
        "--public-only",
    ]);
    let report: Value = serde_json::from_str(&String::from_utf8_lossy(&out.stdout)).unwrap();
    assert!(!out.status.success(), "{report}");
    assert_eq!(report["summary"]["extraction_complete"], false);
    assert!(report["cards"]
        .as_array()
        .unwrap()
        .iter()
        .any(|card| card["decl"] == "bounded_succ"));
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn spec_card_public_only_hides_non_module_private_and_includes_companion_dir() {
    let dir = fixture("companion");
    let root = write_spec(
        &dir,
        "Root.lean",
        "private theorem secret (n : Nat) : n = n := rfl\ntheorem visible (n : Nat) (h : n < 2) : n = 0 ∨ n = 1 := by\n  omega\n",
    );
    let companion = dir.join("Root");
    fs::create_dir_all(&companion).unwrap();
    write_spec(
        &companion,
        "Sub.lean",
        "theorem bad (h : False) : True := by\n  cases h\n",
    );
    let out = run(&[
        "--json",
        "spec-card",
        root.to_str().unwrap(),
        "--public-only",
    ]);
    let report: Value = serde_json::from_str(&String::from_utf8_lossy(&out.stdout)).unwrap();
    assert!(!out.status.success(), "{report}");
    assert_eq!(report["summary"]["hidden_by_public_only"], 1);
    let cards = report["cards"].as_array().unwrap();
    assert!(!cards.iter().any(|card| card["decl"] == "secret"));
    assert!(cards.iter().any(|card| card["decl"] == "visible"));
    assert!(cards
        .iter()
        .any(|card| card["decl"] == "bad" && card["verdict"] == "VACUOUS"));
    let _ = fs::remove_dir_all(&dir);
}
