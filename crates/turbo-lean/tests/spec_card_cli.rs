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

#[test]
fn spec_card_multiline_prefixes_and_inline_env_fail_closed() {
    let dir = fixture("multiline_in");
    let chained = write_spec(
        &dir,
        "Chained.lean",
        r#"
open Nat
  in variable [Nonempty False] in
theorem sound_looking (n : Nat) (_hn : n < 2) : n = 0 ∨ n = 1 := by
  exact False.elim (Classical.choice inferInstance)

section S
variable
  [Nonempty False]

theorem multiline_var (n : Nat) (_hn : n < 2) : n = 0 ∨ n = 1 := by
  exact False.elim (Classical.choice inferInstance)
end S

def ok_prefix :=
  let x := 1;
  x in
theorem clean_after_def_in (n : Nat) (_hn : n < 2) : n = 0 ∨ n = 1 := by
  omega
"#,
    );
    let out = run(&["--json", "spec-card", chained.to_str().unwrap()]);
    let report: Value = serde_json::from_str(&String::from_utf8_lossy(&out.stdout)).unwrap();
    assert!(!out.status.success(), "{report}");
    let cards = report["cards"].as_array().unwrap();
    for bad in ["sound_looking", "S.multiline_var"] {
        let short = bad.rsplit('.').next().unwrap();
        let card = cards
            .iter()
            .find(|c| c["decl"] == bad || c["decl"] == short)
            .unwrap();
        assert_eq!(card["verdict"], "UNCHECKED_ASSUMPTIONS", "{card}");
        assert_eq!(card["contract"]["extraction_complete"], false);
    }
    let clean = cards
        .iter()
        .find(|c| c["decl"] == "clean_after_def_in")
        .unwrap();
    assert_eq!(clean["verdict"], "TIGHT", "{clean}");

    let attr_inst = write_spec(
        &dir,
        "AttrInst.lean",
        r#"
@[implicit_reducible]
def sneakyInst : BEq Nat := ⟨fun _ _ => false⟩

attribute
  [instance 10000] sneakyInst

theorem exploit [LawfulBEq Nat] (n : Nat) (_h : n < 2) : n = 999 := by
  have h1 : (0 == 0) = true := beq_self_eq_true 0
  exact False.elim (Bool.noConfusion h1)
"#,
    );
    let attr_out = run(&["--json", "spec-card", attr_inst.to_str().unwrap()]);
    let attr_report: Value =
        serde_json::from_str(&String::from_utf8_lossy(&attr_out.stdout)).unwrap();
    assert!(!attr_out.status.success(), "{attr_report}");
    assert_eq!(attr_report["cards"][0]["verdict"], "UNCHECKED_ASSUMPTIONS");

    let open_shadow = write_spec(
        &dir,
        "OpenShadow.lean",
        r#"
namespace Shadow
class BEq (α : Type) where
  falsehood : False
end Shadow

open
  Shadow

theorem exploit {α : Type} [BEq α] (n : Nat) (_h : n < 2) : n = 999 := by
  exact False.elim BEq.falsehood
"#,
    );
    let open_out = run(&["--json", "spec-card", open_shadow.to_str().unwrap()]);
    let open_report: Value =
        serde_json::from_str(&String::from_utf8_lossy(&open_out.stdout)).unwrap();
    assert!(!open_out.status.success(), "{open_report}");
    assert_eq!(open_report["cards"][0]["verdict"], "UNCHECKED_ASSUMPTIONS");
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn spec_card_telescopes_binders_and_vacuous_types_fail_closed() {
    let dir = fixture("telescopes");
    let path = write_spec(
        &dir,
        "Telescopes.lean",
        r#"
theorem m1 (n : Nat) (_hn : n < 2) : [Nonempty False] → n = 0 ∨ n = 1 := by
  intro _; exact False.elim (Classical.choice inferInstance)

theorem m2 : ∀ [Nonempty False] (n : Nat), n < 2 → n = 0 ∨ n = 1 := by
  intro _ _ _; exact False.elim (Classical.choice inferInstance)

theorem m3 (n : Nat) (_hn : n < 2) : ⦃_h : False⦄ → n = 0 ∨ n = 1 := by
  intro h; exact False.elim h

theorem m4 (n : Nat) (_hn : n < 2) : {_h : False} → n = 0 ∨ n = 1 := by
  intro h; exact False.elim h

theorem outer_paren (n : Nat) : (False → n = 999) := by
  intro h; exact False.elim h

theorem nested_paren (n : Nat) : (n < 2 → (False → n = 999)) := by
  intro _ h; exact False.elim h

theorem paren_impl ((n : Nat)) : ((False → n = 0)) → (n < 2 → n = 0 ∨ n = 1) := by
  intro _ hn; omega

theorem fin_zero (h : Fin 0) (n : Nat) : n = 999 := by
  exact h.elim0

theorem prod_empty (h : Prod Nat Empty) (n : Nat) : n = 999 := by
  exact Empty.elim h.2

theorem prod_op (h : Nat × Empty) (n : Nat) : n = 999 := by
  exact Empty.elim h.2

theorem root_empty (h : _root_.Empty) (n : Nat) : n = 999 := by
  exact Empty.elim h

theorem arrow_false (h : Nat → False) (n : Nat) : n = 999 := by
  exact False.elim (h n)

theorem id_false (h : id False) (n : Nat) : n = 999 := by
  exact False.elim h

theorem subtype_false (h : { _x : Nat // False }) (n : Nat) : n = 999 := by
  exact False.elim h.2

theorem sigma_empty (h : Sigma (fun _ : Nat => PEmpty)) (n : Nat) : n = 999 := by
  cases h.2

theorem exists_false (h : ∃ _ : Nat, False) (n : Nat) : n = 999 := by
  obtain ⟨_, hf⟩ := h; exact False.elim hf

theorem untyped_binder (x) (n : Nat) (_hn : n < 2) : n = 0 ∨ n = 1 := by
  omega

theorem out_param_binder (h : outParam False) (n : Nat) : n = 999 := by
  exact False.elim h

theorem have_stmt (n : Nat) (_hn : n < 2) : have _x : Nat := 0; n = 0 ∨ n = 1 := by
  omega

theorem let_unused_false (h : Empty) (n : Nat) : let x : False := Empty.elim h; n = 999 := by
  exact Empty.elim h

theorem let_safe (n : Nat) (_hn : n < 2) : let x : Nat := 1; n < x + 1 → n = 0 ∨ n = 1 := by
  intro _; omega

theorem iff_conj (a b : Nat) : (a = b → b = a) ∧ (b = a → a = b) := by
  constructor <;> intro h <;> omega
"#,
    );
    let out = run(&["--json", "spec-card", path.to_str().unwrap()]);
    let report: Value = serde_json::from_str(&String::from_utf8_lossy(&out.stdout)).unwrap();
    assert!(!out.status.success(), "{report}");
    let cards = report["cards"].as_array().unwrap();
    for card in cards {
        let decl = card["decl"].as_str().unwrap();
        if matches!(decl, "let_safe" | "iff_conj") {
            assert_eq!(card["verdict"], "TIGHT", "{decl}: {card}");
            assert_eq!(
                card["contract"]["extraction_complete"], true,
                "{decl}: {card}"
            );
        } else {
            assert_ne!(card["verdict"], "TIGHT", "{decl}: {card}");
            assert_eq!(
                card["contract"]["extraction_complete"], false,
                "{decl}: {card}"
            );
        }
    }
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn spec_card_instances_macros_and_module_sections_fail_closed() {
    let dir = fixture("inst_macro_mod");
    let evil_beq = write_spec(
        &dir,
        "EvilBeq.lean",
        r#"
namespace Evil
class BEq (p : Prop) : Prop where out : p
end Evil
theorem vacuous_via_evil_beq [Evil.BEq False] (n : Nat) (_hn : n < 2) : n = 0 ∨ n = 1 := by
  exact False.elim Evil.BEq.out
"#,
    );
    let out1 = run(&["--json", "spec-card", evil_beq.to_str().unwrap()]);
    let rep1: Value = serde_json::from_str(&String::from_utf8_lossy(&out1.stdout)).unwrap();
    assert!(!out1.status.success(), "{rep1}");
    assert_eq!(rep1["cards"][0]["verdict"], "UNCHECKED_ASSUMPTIONS");

    let inst_checks = write_spec(
        &dir,
        "InstChecks.lean",
        r#"
theorem bad_order [LawfulBEq α] {α : Type} [BEq α] (x : α) (n : Nat) (_hn : n < 2) : n = 0 ∨ n = 1 := by
  omega

theorem dec_pred [DecidablePred (fun _ : Nat => False)] (n : Nat) (_hn : n < 2) : n = 0 ∨ n = 1 := by
  omega

theorem dec_arrow [DecidablePred (fun _ : Nat => True) → Nonempty False] (n : Nat) (_hn : n < 2) : n = 0 ∨ n = 1 := by
  omega

theorem good_lawful {α : Type} [BEq α] [LawfulBEq α] (x : α) (n : Nat) (_hn : n < 2) : n = 0 ∨ n = 1 := by
  omega

theorem good_nat_lawful [LawfulBEq Nat] (n : Nat) (_hn : n < 2) : n = 0 ∨ n = 1 := by
  omega
"#,
    );
    let out2 = run(&["--json", "spec-card", inst_checks.to_str().unwrap()]);
    let rep2: Value = serde_json::from_str(&String::from_utf8_lossy(&out2.stdout)).unwrap();
    assert!(!out2.status.success(), "{rep2}");
    for card in rep2["cards"].as_array().unwrap() {
        let decl = card["decl"].as_str().unwrap();
        if decl.starts_with("good_") {
            assert_eq!(card["verdict"], "TIGHT", "{card}");
        } else {
            assert_eq!(card["verdict"], "UNCHECKED_ASSUMPTIONS", "{card}");
        }
    }

    let macro_taint = write_spec(
        &dir,
        "MacroTaint.lean",
        r#"
section S
local macro_rules | `($a < $b) => `(False)
end S
theorem after_macro (n : Nat) (h : n < 2) : n = 0 ∨ n = 1 := by
  omega
"#,
    );
    let out3 = run(&["--json", "spec-card", macro_taint.to_str().unwrap()]);
    let rep3: Value = serde_json::from_str(&String::from_utf8_lossy(&out3.stdout)).unwrap();
    assert!(!out3.status.success(), "{rep3}");
    assert_eq!(rep3["summary"]["extraction_complete"], false);
    assert_eq!(rep3["cards"][0]["verdict"], "UNCHECKED_ASSUMPTIONS");

    let zero_thm_elab = write_spec(
        &dir,
        "ZeroThmElab.lean",
        "elab \"declare_hidden\" : command => pure ()\n",
    );
    let out4 = run(&["--json", "spec-card", zero_thm_elab.to_str().unwrap()]);
    let rep4: Value = serde_json::from_str(&String::from_utf8_lossy(&out4.stdout)).unwrap();
    assert!(!out4.status.success(), "{rep4}");
    assert_eq!(rep4["summary"]["extraction_complete"], false);

    let zero_cards = write_spec(
        &dir,
        "OnlyDef.lean",
        "def helper (n : Nat) : Nat := n + 1\n",
    );
    let out5 = run(&["--json", "spec-card", zero_cards.to_str().unwrap()]);
    let rep5: Value = serde_json::from_str(&String::from_utf8_lossy(&out5.stdout)).unwrap();
    assert!(out5.status.success(), "{rep5}");
    assert_eq!(rep5["ok"], true);
    assert_eq!(rep5["summary"]["cards"], 0);

    let pub_meta = write_spec(
        &dir,
        "PubMeta.lean",
        r#"
module
public theorem clean (n : Nat) (_hn : n < 2) : n = 0 ∨ n = 1 := by omega
@[expose] public section
end
public meta section
theorem sneaky_meta [Nonempty False] (n : Nat) (_hn : n < 2) : n = 0 ∨ n = 1 := by
  exact False.elim (Classical.choice inferInstance)
end
meta section
theorem hidden_meta (n : Nat) (_hn : n < 2) : n = 0 ∨ n = 1 := by omega
end
"#,
    );
    let out6 = run(&[
        "--json",
        "spec-card",
        "--public-only",
        pub_meta.to_str().unwrap(),
    ]);
    let rep6: Value = serde_json::from_str(&String::from_utf8_lossy(&out6.stdout)).unwrap();
    assert!(!out6.status.success(), "{rep6}");
    let cards6 = rep6["cards"].as_array().unwrap();
    assert!(cards6
        .iter()
        .any(|c| c["decl"] == "sneaky_meta" && c["verdict"] == "UNCHECKED_ASSUMPTIONS"));
    assert!(!cards6.iter().any(|c| c["decl"] == "hidden_meta"));

    let where_escape = write_spec(
        &dir,
        "WhereEscape.lean",
        r#"
module
structure P : Prop where
  mk ::
private theorem t1 : P where
public theorem t2 [Nonempty False] (n : Nat) (_h : n < 2) : n = 0 ∨ n = 1 := by
  exact False.elim (Classical.choice inferInstance)
public theorem clean (n : Nat) (_h : n < 2) : n = 0 ∨ n = 1 := by
  omega
"#,
    );
    let out7 = run(&[
        "--json",
        "spec-card",
        "--public-only",
        where_escape.to_str().unwrap(),
    ]);
    let rep7: Value = serde_json::from_str(&String::from_utf8_lossy(&out7.stdout)).unwrap();
    assert!(!out7.status.success(), "{rep7}");
    assert_eq!(rep7["summary"]["extraction_complete"], false);
    let _ = fs::remove_dir_all(&dir);
}

#[cfg(unix)]
#[test]
fn spec_card_rejects_symlinks_unreadable_dirs_and_mixed_policies() {
    use std::os::unix::fs::{symlink, PermissionsExt};

    let dir = fixture("fs_safety");
    let tree = dir.join("tree");
    fs::create_dir_all(&tree).unwrap();
    let good = write_spec(&tree, "Good.lean", TIGHT);
    let outside = write_spec(&dir, "Outside.lean", TIGHT);
    symlink(&outside, tree.join("Linked.lean")).unwrap();
    let sym_out = run(&["--json", "spec-card", tree.to_str().unwrap()]);
    assert!(!sym_out.status.success());
    fs::remove_file(tree.join("Linked.lean")).unwrap();

    symlink(dir.join("Missing.lean"), tree.join("Broken.lean")).unwrap();
    let broken_out = run(&["--json", "spec-card", tree.to_str().unwrap()]);
    assert!(!broken_out.status.success());
    fs::remove_file(tree.join("Broken.lean")).unwrap();

    let locked = tree.join("locked");
    fs::create_dir_all(&locked).unwrap();
    write_spec(
        &locked,
        "Secret.lean",
        "theorem bad (h : False) : True := by cases h\n",
    );
    fs::set_permissions(&locked, fs::Permissions::from_mode(0o000)).unwrap();
    let can_block_read = fs::read_dir(&locked).is_err();
    let locked_out = run(&["--json", "spec-card", tree.to_str().unwrap()]);
    fs::set_permissions(&locked, fs::Permissions::from_mode(0o700)).unwrap();
    if can_block_read {
        assert!(!locked_out.status.success());
    }

    let proj_a = dir.join("proj_a");
    let proj_b = dir.join("proj_b");
    fs::create_dir_all(&proj_a).unwrap();
    fs::create_dir_all(&proj_b).unwrap();
    fs::write(proj_a.join("audit-spec.toml"), "policy = \"default\"\n").unwrap();
    fs::write(
        proj_b.join("audit-spec.toml"),
        "policy = \"strict-proofs\"\n",
    )
    .unwrap();
    let file_a = write_spec(&proj_a, "A.lean", TIGHT);
    let file_b = write_spec(&proj_b, "B.lean", TIGHT);
    let _ = good;
    let mixed_out = run(&[
        "--json",
        "spec-card",
        file_a.to_str().unwrap(),
        file_b.to_str().unwrap(),
    ]);
    let mixed_rep: Value =
        serde_json::from_str(&String::from_utf8_lossy(&mixed_out.stdout)).unwrap();
    assert!(!mixed_out.status.success(), "{mixed_rep}");
    assert_eq!(mixed_rep["summary"]["policy"], "mixed");
    assert_eq!(mixed_rep["ok"], false);
    let _ = fs::remove_dir_all(&dir);
}
