use serde_json::Value;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

/// Subprocess CLI regression suite for `turbo-lean audit-spec` Layer 4 fail-closed guarantees.
///
/// Note on Git prerequisite: `audit-spec` runs standalone without invoking `git`, whereas
/// workspace tests exercising Git-backed commands (`pr-verify`, `ci-verify`) require Git >= 2.46
/// on `PATH` or via `TURBO_LEAN_GIT` (`trusted_tools::MIN_GIT`).
struct AuditSpecFixture {
    root: PathBuf,
}

impl AuditSpecFixture {
    fn new(name: &str) -> Self {
        let root = std::env::temp_dir().join(format!(
            "turbo_audit_spec_cli_{}_{}_{}",
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
            .env_remove("TURBO_LEAN_AUDIT_CACHE_DIR")
            .env_remove("TURBO_LEAN_NO_AUDIT_CACHE");
        cmd
    }

    fn write(&self, rel: &str, contents: &str) -> PathBuf {
        let p = self.root.join(rel);
        if let Some(parent) = p.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(&p, contents).unwrap();
        p
    }
}

impl Drop for AuditSpecFixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

fn parse_json_stdout(out: &Output, ctx: &str) -> Value {
    serde_json::from_slice(&out.stdout).unwrap_or_else(|e| {
        panic!(
            "{ctx}: expected valid JSON stdout ({e}):\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        )
    })
}

fn assert_cli_ok(out: &Output, ctx: &str) -> Value {
    let json = parse_json_stdout(out, ctx);
    assert!(
        out.status.success(),
        "{ctx}: expected exit 0, got {:?}\njson:\n{json}\nstderr:\n{}",
        out.status.code(),
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(json["ok"].as_bool(), Some(true), "{ctx}: {json}");
    json
}

fn assert_cli_fail_json(out: &Output, ctx: &str) -> Value {
    let json = parse_json_stdout(out, ctx);
    assert!(
        !out.status.success(),
        "{ctx}: expected non-zero exit when ok=false, got exit 0:\n{json}"
    );
    assert_eq!(json["ok"].as_bool(), Some(false), "{ctx}: {json}");
    json
}

#[test]
fn let_inliner_preserves_string_literals_and_interpolated_splices() {
    let fx = AuditSpecFixture::new("let_inliner");
    let valid = fx.write(
        "ValidLet.lean",
        r#"
def fmtTag (id : Nat) : String := s!"tag={id}"

theorem let_with_semi_and_eq_in_string (n : Nat) (h : n > 1) :
    let tag := "a := b; in c"
    let m := n + 1
    m > 2 ∧ (tag.length > 0 → fmtTag n = s!"tag={1 + (n - 1)}") := by
  sorry
"#,
    );
    let out = fx
        .cli("let-ok")
        .args(["--json", "audit-spec"])
        .arg(&valid)
        .output()
        .unwrap();
    let json = assert_cli_ok(&out, "let_with_semi_and_eq_in_string");
    assert_eq!(json["tight_specs"].as_u64(), Some(1));
    assert_eq!(json["stub_defs"].as_array().unwrap().len(), 0);

    // Negative control 1: unused param `id` referenced ONLY inside a plain string literal
    // (not an `s!"...{id}..."` splice) must still be caught as a stub!
    let bad = fx.write(
        "PlainStringStub.lean",
        r#"
def fakeFmt (id : Nat) : String := "tag={id}"

theorem uses_fake_fmt (id : Nat) : fakeFmt id = "tag={id}" := by rfl
"#,
    );
    let bad_out = fx
        .cli("let-bad")
        .args(["--json", "audit-spec", "--policy", "strict-proofs"])
        .arg(&bad)
        .output()
        .unwrap();
    let bad_json = assert_cli_fail_json(&bad_out, "PlainStringStub");
    let stubs = bad_json["stub_defs"].as_array().unwrap();
    assert!(
        stubs
            .iter()
            .any(|s| s.as_str().unwrap_or("").contains("fakeFmt")),
        "expected fakeFmt stub finding, got: {bad_json}"
    );

    // Negative control 2: `let tag := "a := b; c"; let y := x; y = y` must NOT get confused by
    // `:=` or `;` inside the string literal and MUST reject `y = y` as a tautology (`trivial_specs == 1`).
    let taut_let = fx.write(
        "TautLetWithString.lean",
        "theorem let_string_taut (x : Nat) : let tag := \"a := b; c\"; let y := x; y = y := by rfl\n",
    );
    let taut_out = fx
        .cli("let-taut-str")
        .args(["--json", "audit-spec"])
        .arg(&taut_let)
        .output()
        .unwrap();
    let taut_json = assert_cli_fail_json(&taut_out, "let tag := \"a := b; c\"; let y := x; y = y");
    assert_eq!(taut_json["trivial_specs"].as_u64(), Some(1));

    // Negative control 3: multiline `let` declaration placing `:=` on a continuation line (`let x : Nat\n := n; x = x`)
    // and `in`-delimited `let y := x in y = y` must also inline and be rejected as tautologies!
    let multiline_let = fx.write(
        "MultilineLetTaut.lean",
        r#"
theorem multiline_let_taut (n : Nat) :
    let x : Nat
      := n; x = x := by
  rfl

theorem let_in_taut (n : Nat) : let y := n in y = y := by rfl
"#,
    );
    let ml_out = fx
        .cli("let-multiline")
        .args(["--json", "audit-spec"])
        .arg(&multiline_let)
        .output()
        .unwrap();
    let ml_json = assert_cli_fail_json(&ml_out, "multiline let := and let ... in tautologies");
    assert_eq!(ml_json["trivial_specs"].as_u64(), Some(2));
}

#[test]
fn config_loader_fails_closed_on_unknown_preset_malformed_toml_and_unknown_keys() {
    let fx = AuditSpecFixture::new("config_fail_closed");
    let spec = fx.write(
        "proj/Spec.lean",
        "theorem good_spec (n : Nat) (h : n > 0) : n >= 1 := by omega\n",
    );

    // 1. Positive: valid `--policy strict-proofs`
    let ok_out = fx
        .cli("cfg-ok")
        .args(["--json", "audit-spec", "--policy", "strict-proofs"])
        .arg(&spec)
        .output()
        .unwrap();
    assert_cli_ok(&ok_out, "valid strict-proofs preset");

    // 2. Negative: unknown `--policy` preset
    let bad_pol = fx
        .cli("cfg-bad-preset")
        .args(["--json", "audit-spec", "--policy", "stict-proofs-typo"])
        .arg(&spec)
        .output()
        .unwrap();
    let bad_pol_json = assert_cli_fail_json(&bad_pol, "unknown policy preset");
    assert_eq!(bad_pol_json["verdict"].as_str(), Some("error"));
    assert!(bad_pol_json["error"]
        .as_str()
        .unwrap_or("")
        .contains("Unknown audit-spec policy preset"));

    // 3. Negative: malformed `audit-spec.toml` in ancestor directory
    fx.write("proj/audit-spec.toml", "policy = [unclosed\n");
    let malformed = fx
        .cli("cfg-malformed")
        .args(["--json", "audit-spec"])
        .arg(&spec)
        .output()
        .unwrap();
    let malformed_json = assert_cli_fail_json(&malformed, "malformed audit-spec.toml");
    assert_eq!(malformed_json["verdict"].as_str(), Some("error"));

    // 4. Negative: unknown key in `[audit_spec]` inside `turbo-lean.toml`
    let _ = fs::remove_file(fx.root.join("proj/audit-spec.toml"));
    fx.write(
        "proj/turbo-lean.toml",
        "[audit_spec]\npolicy = \"default\"\nunknown_typo_field = true\n",
    );
    let unk_key = fx
        .cli("cfg-unk-key")
        .args(["--json", "audit-spec"])
        .arg(&spec)
        .output()
        .unwrap();
    let unk_json = assert_cli_fail_json(&unk_key, "unknown key in turbo-lean.toml");
    assert_eq!(unk_json["verdict"].as_str(), Some("error"));
    assert!(unk_json["error"]
        .as_str()
        .unwrap_or("")
        .contains("unknown_typo_field"));

    // 5. Negative: wrong value type in `audit-spec.toml`
    let _ = fs::remove_file(fx.root.join("proj/turbo-lean.toml"));
    fx.write(
        "proj/audit-spec.toml",
        "policy = \"default\"\nreject_identity_stubs = \"yes\"\n",
    );
    let bad_type = fx
        .cli("cfg-bad-type")
        .args(["--json", "audit-spec"])
        .arg(&spec)
        .output()
        .unwrap();
    let bad_type_json = assert_cli_fail_json(&bad_type, "wrong type in audit-spec.toml");
    assert_eq!(bad_type_json["verdict"].as_str(), Some("error"));

    // 6. Positive: `turbo-lean.toml` with unrelated top-level tables (`[kernel]`, `[build]`, `[axioms]`)
    // plus standard `[[audit_spec.path_rules]]` array-of-tables must load cleanly!
    let _ = fs::remove_file(fx.root.join("proj/audit-spec.toml"));
    fx.write(
        "proj/turbo-lean.toml",
        r#"
[kernel]
engine = "standard"

[build]
jobs = 4

[axioms]
allow = ["Custom.axiom"]

[audit_spec]
policy = "strict-proofs"

[[audit_spec.path_rules]]
glob = "proj/*.lean"
forbid_decl_kinds = ["opaque"]
"#,
    );
    let multi_table_ok = fx
        .cli("cfg-multi-table")
        .args(["--json", "audit-spec"])
        .arg(&spec)
        .output()
        .unwrap();
    let multi_json = assert_cli_ok(
        &multi_table_ok,
        "turbo-lean.toml with unrelated tables + path_rules",
    );
    assert_eq!(multi_json["policy"].as_str(), Some("strict-proofs"));
}

#[test]
fn glob_matching_enforces_path_segment_boundaries() {
    let fx = AuditSpecFixture::new("glob_segments");
    let cfg = fx.write(
        "audit-spec.toml",
        r#"
policy = "default"

[[path_overrides]]
glob = "lean/Allowed/*.lean"
forbid_decl_kinds = []

[[path_overrides]]
glob = "lean/**/Proofs/*.lean"
forbid_decl_kinds = ["structure"]
"#,
    );

    // Positive: `lean/Allowed/Helper.lean` matches `lean/Allowed/*.lean` (single segment)
    let allowed = fx.write(
        "lean/Allowed/Helper.lean",
        "structure AllowedBox where\n  val : Nat\ntheorem box_eq (b : AllowedBox) : b.val = b.val + 0 := by omega\n",
    );
    // Negative: `lean/Allowed/Sub/Sneaky.lean` must NOT match `lean/Allowed/*.lean` because `*` cannot cross `/`
    let sneaky = fx.write(
        "lean/Allowed/Sub/Sneaky.lean",
        "structure SneakyBox where\n  val : Nat\ntheorem sneaky_eq (n : Nat) (h : n > 0) : n >= 1 := by omega\n",
    );
    let cfg_with_root_forbid = fx.write(
        "strict-glob.toml",
        r#"
policy = "strict-proofs"
forbid_decl_kinds = ["structure"]

[[path_overrides]]
glob = "lean/Allowed/*.lean"
allow_decl_names = ["AllowedBox", "SneakyBox"]
"#,
    );

    let ok_out = fx
        .cli("glob-ok")
        .args(["--json", "audit-spec", "--config"])
        .arg(&cfg_with_root_forbid)
        .arg(&allowed)
        .output()
        .unwrap();
    assert_cli_ok(&ok_out, "single-segment glob match");

    let fail_out = fx
        .cli("glob-sneaky")
        .args(["--json", "audit-spec", "--config"])
        .arg(&cfg_with_root_forbid)
        .arg(&sneaky)
        .output()
        .unwrap();
    let fail_json = assert_cli_fail_json(&fail_out, "single star must not cross slash");
    assert!(
        !fail_json["forbidden_scope_decls"]
            .as_array()
            .unwrap()
            .is_empty(),
        "expected SneakyBox to be rejected: {fail_json}"
    );

    // Also verify `lean/**/Proofs/*.lean` matches zero intermediate directories (`lean/Proofs/P.lean`)
    let zero_seg = fx.write(
        "lean/Proofs/P.lean",
        "structure ForbiddenInProofs where\n  x : Nat\ntheorem p_ok (n : Nat) (h : n > 0) : n >= 1 := by omega\n",
    );
    let zero_out = fx
        .cli("glob-doublestar")
        .args(["--json", "audit-spec", "--config"])
        .arg(&cfg)
        .arg(&zero_seg)
        .output()
        .unwrap();
    let zero_json = assert_cli_fail_json(&zero_out, "** matches zero segments");
    assert!(!zero_json["forbidden_scope_decls"]
        .as_array()
        .unwrap()
        .is_empty());

    // Substring lookalikes (`other/not_Proofs_note.lean`, `my_lean_archive/not_Proofs_notes.lean`)
    // MUST NOT falsely match `lean/Proofs/*.lean` or `lean/**/Proofs/*.lean`!
    for (idx, rel) in [
        "other/not_Proofs_note.lean",
        "my_lean_archive/not_Proofs_notes.lean",
    ]
    .iter()
    .enumerate()
    {
        let lookalike = fx.write(
            rel,
            "structure AllowedOutsideProofs where\n  x : Nat\ntheorem lk_ok (n : Nat) (h : n > 0) : n >= 1 := by omega\n",
        );
        let lk_out = fx
            .cli(&format!("glob-lookalike-{idx}"))
            .args(["--json", "audit-spec", "--config"])
            .arg(&cfg)
            .arg(&lookalike)
            .output()
            .unwrap();
        assert_cli_ok(&lk_out, rel);
    }
}

#[test]
fn forbidden_scope_scanner_catches_multiline_and_bracketed_attributes() {
    let fx = AuditSpecFixture::new("attr_bypass");
    let bypass = fx.write(
        "Bypass.lean",
        r#"
@[simp, customAttr "a]b"]
private unsafe inductive HiddenInductive where
  | mk (x : Nat)

@[always_inline]
noncomputable opaque hiddenOpaque : Nat := 0

@[csimp]
def hiddenCsimpDef : Nat := 1

@[simp]
def multilineSimpDef (n : Nat) : Nat := n + 1

@[simp]
theorem allowed_simp_thm (n : Nat) (h : n > 0) : n >= 1 := by omega
"#,
    );
    let out = fx
        .cli("attr-bad")
        .args([
            "--json",
            "audit-spec",
            "--policy",
            "strict-proofs",
            "--forbid-decl-kinds",
            "inductive",
            "--forbid-decl-kinds",
            "opaque",
            "--forbid-decl-kinds",
            "def",
        ])
        .arg(&bypass)
        .output()
        .unwrap();
    let json = assert_cli_fail_json(&out, "multiline attribute forbidden decls");
    let forb = json["forbidden_scope_decls"].as_array().unwrap();
    for expected in [
        "HiddenInductive",
        "hiddenOpaque",
        "hiddenCsimpDef",
        "multilineSimpDef",
    ] {
        assert!(
            forb.iter()
                .any(|v| v.as_str().unwrap_or("").contains(expected)),
            "missing {expected} in {forb:?}"
        );
    }
    assert!(
        !forb
            .iter()
            .any(|v| v.as_str().unwrap_or("").contains("allowed_simp_thm")),
        "allowed theorem should not be flagged in {forb:?}"
    );
}

#[test]
fn diagonal_vacuity_and_honest_witness_labels_are_enforced() {
    let fx = AuditSpecFixture::new("diag_vacuity");

    // 1. Positive: equality/aliasing & injectivity preconditions (`f x = f y → x = y`) MUST NOT be falsely marked vacuous
    let diag_ok = fx.write(
        "DiagOk.lean",
        r#"
def dbl (x : Nat) : Nat := x + x

theorem eq_alias_nonvacuous (a b : Nat) (h1 : a = b) (h2 : a > 0) : b >= 1 := by omega

theorem dbl_injective (x y : Nat) : dbl x = dbl y → x = y := by omega
"#,
    );
    let ok_out = fx
        .cli("diag-ok")
        .args(["--json", "audit-spec"])
        .arg(&diag_ok)
        .output()
        .unwrap();
    let ok_json = assert_cli_ok(&ok_out, "diagonal equality & injectivity preconditions");
    assert_eq!(ok_json["vacuous_specs"].as_u64(), Some(0));
    assert_eq!(ok_json["tight_specs"].as_u64(), Some(2));

    // 2. Negative: contradictory precondition `a < b ∧ b < a` MUST still be caught as vacuous
    let vac = fx.write(
        "DiagVacuous.lean",
        "theorem contradictory_hyps (a b : Nat) (h1 : a < b) (h2 : b < a) : a = 42 := by omega\n",
    );
    let vac_out = fx
        .cli("diag-vac")
        .args(["--json", "audit-spec"])
        .arg(&vac)
        .output()
        .unwrap();
    let vac_json = assert_cli_fail_json(&vac_out, "contradictory precondition");
    assert_eq!(vac_json["vacuous_specs"].as_u64(), Some(1));

    // 2b. Negative: narrow-width `UInt8` wrapping overflow (`x + 255 > 255`) MUST preserve `UInt8`
    //     scalar domain during boundary specialization and remain rejected as vacuous!
    let u8_vac = fx.write(
        "UInt8Vacuous.lean",
        "theorem u8_impossible (x : UInt8) (h : x + 255 > 255) : x = 0 := by omega\n",
    );
    let u8_out = fx
        .cli("diag-u8-vac")
        .args(["--json", "audit-spec"])
        .arg(&u8_vac)
        .output()
        .unwrap();
    let u8_json = assert_cli_fail_json(&u8_out, "UInt8 wrapping impossible precondition");
    assert_eq!(u8_json["vacuous_specs"].as_u64(), Some(1));

    // 3. Honest witness label: symbolic abstract theorem without concrete arithmetic assignment
    //    must emit `heuristic_unverified_*` rather than claiming `concrete_refutation_found`.
    let abstract_spec = fx.write(
        "AbstractSpec.lean",
        "opaque P : Nat → Prop\nopaque Q : Nat → Prop\ntheorem abstract_imp (x : Nat) (h : P x) : Q x := sorry\n",
    );
    let abs_out = fx
        .cli("diag-abs")
        .args(["--json", "audit-spec"])
        .arg(&abstract_spec)
        .output()
        .unwrap();
    let abs_json = assert_cli_ok(&abs_out, "abstract non-trivial implication");
    let neg_w = abs_json["specs"][0]["neg_witness"].as_str().unwrap_or("");
    assert!(
        neg_w.starts_with("heuristic_unverified_"),
        "expected heuristic_unverified_* witness label for symbolic predicate, got: {neg_w}"
    );
}

#[test]
fn cache_dir_uses_private_permissions_and_honors_global_cache_dir() {
    let fx = AuditSpecFixture::new("private_cache");
    let spec = fx.write(
        "Spec.lean",
        "theorem cache_test (n : Nat) (h : n > 0) : n >= 1 := by omega\n",
    );
    let custom_cache = fx.root.join("global-cache-flag");
    let out = fx
        .cli("cache-perm")
        .arg("--json")
        .arg("--cache-dir")
        .arg(&custom_cache)
        .arg("audit-spec")
        .arg(&spec)
        .output()
        .unwrap();
    let json1 = assert_cli_ok(&out, "first run populates private cache");
    assert_eq!(json1["cache_hit"].as_bool(), Some(false));

    let audit_cache_subdir = custom_cache.join("audit-spec-cache-v1");
    assert!(
        audit_cache_subdir.is_dir(),
        "expected --cache-dir/audit-spec-cache-v1 to be created"
    );
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mode = fs::metadata(&audit_cache_subdir)
            .unwrap()
            .permissions()
            .mode()
            & 0o777;
        assert_eq!(
            mode, 0o700,
            "expected private 0700 cache dir, got {:o}",
            mode
        );
    }

    let out2 = fx
        .cli("cache-perm")
        .arg("--json")
        .arg("--cache-dir")
        .arg(&custom_cache)
        .arg("audit-spec")
        .arg(&spec)
        .output()
        .unwrap();
    let json2 = assert_cli_ok(&out2, "second run hits private cache");
    assert_eq!(json2["cache_hit"].as_bool(), Some(true));
}

#[test]
fn multi_file_batch_resolves_per_target_policy_permutation_invariantly() {
    let fx = AuditSpecFixture::new("per_target_batch");
    fx.write("proj_lenient/audit-spec.toml", "policy = \"default\"\n");
    let lenient_file = fx.write(
        "proj_lenient/A.lean",
        "structure AllowedInDefault where\n  x : Nat\ntheorem a_ok (n : Nat) (h : n > 0) : n >= 1 := by omega\n",
    );

    fx.write(
        "proj_strict/audit-spec.toml",
        "policy = \"strict-proofs\"\nforbid_decl_kinds = [\"structure\"]\n",
    );
    let strict_bad_file = fx.write(
        "proj_strict/B.lean",
        "structure ForbiddenInStrict where\n  x : Nat\ntheorem b_ok (n : Nat) (h : n > 0) : n >= 1 := by omega\n",
    );
    let strict_good_file = fx.write(
        "proj_strict/C.lean",
        "theorem c_ok (n : Nat) (h : n > 0) : n >= 1 := by omega\n",
    );

    // Order 1: lenient first, strict-violating second -> MUST still fail `strict_bad_file`!
    let out_ab = fx
        .cli("batch-ab")
        .args(["--json", "audit-spec"])
        .arg(&lenient_file)
        .arg(&strict_bad_file)
        .output()
        .unwrap();
    let json_ab = assert_cli_fail_json(&out_ab, "batch (lenient, strict_bad)");

    // Order 2: strict-violating first, lenient second -> identical failure & forbidden decls!
    let out_ba = fx
        .cli("batch-ba")
        .args(["--json", "audit-spec"])
        .arg(&strict_bad_file)
        .arg(&lenient_file)
        .output()
        .unwrap();
    let json_ba = assert_cli_fail_json(&out_ba, "batch (strict_bad, lenient)");
    assert_eq!(
        json_ab["forbidden_scope_decls"],
        json_ba["forbidden_scope_decls"]
    );
    assert_eq!(json_ab["policy"].as_str(), Some("mixed"));
    assert_eq!(json_ba["policy"].as_str(), Some("mixed"));

    // Single-file reference runs must match the corresponding entries in `file_reports` regardless of batch order
    let single_lenient = parse_json_stdout(
        &fx.cli("single-lenient")
            .args(["--json", "audit-spec"])
            .arg(&lenient_file)
            .output()
            .unwrap(),
        "single lenient_file",
    );
    let single_strict_bad = parse_json_stdout(
        &fx.cli("single-strict-bad")
            .args(["--json", "audit-spec"])
            .arg(&strict_bad_file)
            .output()
            .unwrap(),
        "single strict_bad_file",
    );
    assert_eq!(json_ab["file_reports"][0]["ok"], single_lenient["ok"]);
    assert_eq!(json_ab["file_reports"][1]["ok"], single_strict_bad["ok"]);
    assert_eq!(json_ba["file_reports"][0]["ok"], single_strict_bad["ok"]);
    assert_eq!(json_ba["file_reports"][1]["ok"], single_lenient["ok"]);
    assert_eq!(
        json_ba["file_reports"][0]["forbidden_scope_decls"],
        single_strict_bad["forbidden_scope_decls"]
    );

    // Positive mixed batch: lenient (with structure) + strict (theorem only) -> passes in both orders!
    for (tag, pair) in [
        ("ok-ac", [&lenient_file, &strict_good_file]),
        ("ok-ca", [&strict_good_file, &lenient_file]),
    ] {
        let out_ok = fx
            .cli(tag)
            .args(["--json", "audit-spec"])
            .arg(pair[0])
            .arg(pair[1])
            .output()
            .unwrap();
        let json_ok = assert_cli_ok(&out_ok, tag);
        assert_eq!(json_ok["policy"].as_str(), Some("mixed"));
        assert_eq!(json_ok["tight_specs"].as_u64(), Some(2));
    }
}

#[test]
fn decl_filter_miss_missing_file_and_require_nonempty_fail_closed_with_json_and_nonzero_exit() {
    let fx = AuditSpecFixture::new("exit_codes");
    let spec = fx.write(
        "Spec.lean",
        "theorem existing_thm (n : Nat) (h : n > 0) : n >= 1 := by omega\n",
    );
    let empty_lean = fx.write("OnlyDefs.lean", "def helper (n : Nat) : Nat := n + 1\n");

    // 1. Positive `--decl existing_thm`
    let ok_decl = fx
        .cli("decl-ok")
        .args(["--json", "audit-spec", "--decl", "existing_thm"])
        .arg(&spec)
        .output()
        .unwrap();
    let ok_json = assert_cli_ok(&ok_decl, "matching --decl");
    assert_eq!(ok_json["total_specs_audited"].as_u64(), Some(1));

    // 2. Negative `--decl does_not_exist` -> ok: false, verdict: "decl_not_found", exit != 0
    let miss_decl = fx
        .cli("decl-miss")
        .args(["--json", "audit-spec", "--decl", "does_not_exist"])
        .arg(&spec)
        .output()
        .unwrap();
    let miss_json = assert_cli_fail_json(&miss_decl, "missing --decl");
    assert_eq!(miss_json["verdict"].as_str(), Some("decl_not_found"));

    // 3. Batch `--decl existing_thm` where 1 of 2 files defines it -> succeeds!
    let batch_decl_hit = fx
        .cli("decl-batch-hit")
        .args(["--json", "audit-spec", "--decl", "existing_thm"])
        .arg(&empty_lean)
        .arg(&spec)
        .output()
        .unwrap();
    let batch_hit_json = assert_cli_ok(&batch_decl_hit, "batch --decl found in second file");
    assert_eq!(batch_hit_json["total_specs_audited"].as_u64(), Some(1));

    // 4a. Default whole-file audit on theorem-less file WITHOUT `--require-nonempty` remains optional (`ok: true`, exit 0)
    let opt_empty = fx
        .cli("opt-empty")
        .args(["--json", "audit-spec"])
        .arg(&empty_lean)
        .output()
        .unwrap();
    let opt_json = assert_cli_ok(&opt_empty, "0-theorem file without --require-nonempty");
    assert_eq!(opt_json["verdict"].as_str(), Some("no_specs_found"));

    // 4b. Negative `--require-nonempty` on theorem-less file -> ok: false, exit != 0
    let req_nonempty = fx
        .cli("req-nonempty")
        .args(["--json", "audit-spec", "--require-nonempty"])
        .arg(&empty_lean)
        .output()
        .unwrap();
    let req_json = assert_cli_fail_json(&req_nonempty, "--require-nonempty on 0-theorem file");
    assert_eq!(req_json["verdict"].as_str(), Some("no_specs_found"));

    // 5. Negative missing file path in `--json` mode -> structured JSON error + exit != 0
    let missing_path: &Path = Path::new("does_not_exist_anywhere.lean");
    let miss_file = fx
        .cli("missing-file")
        .args(["--json", "audit-spec"])
        .arg(missing_path)
        .output()
        .unwrap();
    let miss_file_json = assert_cli_fail_json(&miss_file, "missing file path");
    assert_eq!(miss_file_json["verdict"].as_str(), Some("error"));
}

#[test]
fn cross_namespace_transitive_stubs_and_umbrella_directory_dedup_are_enforced() {
    let fx = AuditSpecFixture::new("ns_and_umbrella");

    // 1. Cross-namespace wrapper calling an unqualified identity stub or unused-param stub in its
    //    own namespace must be caught on hop >= 2 without colliding with unrelated namespaces.
    let cross_ns = fx.write(
        "CrossNsStubs.lean",
        r#"
namespace Lib
def identityStub (n : Nat) : Nat := n
def wrapId (n : Nat) : Nat := identityStub n + 1
end Lib

namespace Helpers
def unusedStub (n : Nat) : Nat := 0
def wrapper (n : Nat) : Nat := unusedStub n + 1
end Helpers

namespace Uses
theorem test_wrap_id (n : Nat) : Lib.wrapId n = n + 1 := rfl
theorem test_wrap_unused (n : Nat) : Helpers.wrapper n > 0 := by omega
end Uses
"#,
    );
    let ns_out = fx
        .cli("cross-ns")
        .args(["--json", "audit-spec"])
        .arg(&cross_ns)
        .output()
        .unwrap();
    let ns_json = assert_cli_fail_json(&ns_out, "cross-namespace transitive stub detection");
    let stubs = ns_json["stub_defs"].as_array().unwrap();
    assert!(
        stubs
            .iter()
            .any(|s| s.as_str().unwrap_or("").contains("Lib.identityStub")),
        "expected Lib.identityStub in {stubs:?}"
    );
    assert!(
        stubs
            .iter()
            .any(|s| s.as_str().unwrap_or("").contains("Helpers.unusedStub")),
        "expected Helpers.unusedStub in {stubs:?}"
    );

    // 1b. Negative (`open`): unqualified reference to an `open`-imported stub (`open OpenedLib`)
    //     must be caught, whereas an unopened 1-letter sibling stub (`UnopenedSib.v`) must NOT
    //     collide with an ordinary binder `(v : Nat)` in `Uses`!
    let open_neg = fx.write(
        "OpenStubNeg.lean",
        r#"
namespace OpenedLib
def openIdentityStub (n : Nat) : Nat := n
end OpenedLib

open OpenedLib

namespace Uses
theorem test_open_stub (n : Nat) : openIdentityStub n + 1 > 0 := by omega
end Uses
"#,
    );
    let open_neg_out = fx
        .cli("open-ns-neg")
        .args(["--json", "audit-spec"])
        .arg(&open_neg)
        .output()
        .unwrap();
    let open_neg_json = assert_cli_fail_json(&open_neg_out, "open-imported identity stub");
    assert!(open_neg_json["stub_defs"]
        .as_array()
        .unwrap()
        .iter()
        .any(|s| s
            .as_str()
            .unwrap_or("")
            .contains("OpenedLib.openIdentityStub")));

    fx.write(
        "sib_no_collide/OtherSib.lean",
        "namespace UnopenedSib\ndef v (x : Nat) : Nat := x\nend UnopenedSib\n",
    );
    let unopened_pos = fx.write(
        "sib_no_collide/UnopenedNoCollide.lean",
        "namespace Uses\ntheorem clean_binder_v (v : Nat) (h : v > 0) : v >= 1 := by omega\nend Uses\n",
    );
    let unopened_pos_out = fx
        .cli("unopened-pos")
        .args(["--json", "audit-spec"])
        .arg(&unopened_pos)
        .output()
        .unwrap();
    assert_cli_ok(
        &unopened_pos_out,
        "unopened 1-letter sibling def must not collide with binder v",
    );

    // 2. Directory containing an umbrella module `Pkg.lean` + `Pkg/A.lean` must audit `Pkg/A.lean`
    //    exactly once (total_specs_audited == 2, never double-counted as 3).
    let dir_root = fx.root.join("umbrella_tree");
    let pkg_umbrella = fx.write(
        "umbrella_tree/Pkg.lean",
        "theorem pkg_root_thm (n : Nat) (h : n > 0) : n >= 1 := by omega\n",
    );
    fx.write(
        "umbrella_tree/Pkg/A.lean",
        "theorem pkg_sub_thm (n : Nat) (h : n > 1) : n >= 2 := by omega\n",
    );
    let dir_out = fx
        .cli("umbrella-dir")
        .args(["--json", "audit-spec"])
        .arg(&dir_root)
        .output()
        .unwrap();
    let dir_json = assert_cli_ok(&dir_out, "umbrella directory deduplication");
    assert_eq!(dir_json["total_specs_audited"].as_u64(), Some(2));
    assert_eq!(dir_json["tight_specs"].as_u64(), Some(2));
    assert_eq!(dir_json["file_reports"].as_array().map(Vec::len), Some(2));

    // 3. Single-umbrella target (`audit-spec Pkg.lean`) MUST resolve descendant policies per file:
    //    a strict `Pkg/audit-spec.toml` forbidding `structure` (or malformed TOML) in `Pkg/` must
    //    fail closed when auditing `Pkg.lean`, while passing when `Pkg/A.lean` obeys its policy.
    let single_umb_ok = fx
        .cli("umbrella-single-ok")
        .args(["--json", "audit-spec"])
        .arg(&pkg_umbrella)
        .output()
        .unwrap();
    let single_umb_ok_json = assert_cli_ok(&single_umb_ok, "single umbrella positive");
    assert_eq!(single_umb_ok_json["total_specs_audited"].as_u64(), Some(2));

    fx.write(
        "umbrella_tree/Pkg/audit-spec.toml",
        "policy = \"strict-proofs\"\nforbid_decl_kinds = [\"structure\"]\n",
    );
    fx.write(
        "umbrella_tree/Pkg/A.lean",
        "structure ForbiddenInSubdir where\n  x : Nat\ntheorem pkg_sub_thm (n : Nat) (h : n > 1) : n >= 2 := by omega\n",
    );
    let single_umb_bad = fx
        .cli("umbrella-single-bad")
        .args(["--json", "audit-spec"])
        .arg(&pkg_umbrella)
        .output()
        .unwrap();
    let single_umb_bad_json = assert_cli_fail_json(
        &single_umb_bad,
        "single umbrella must enforce descendant Pkg/audit-spec.toml",
    );
    assert!(single_umb_bad_json["forbidden_scope_decls"]
        .as_array()
        .unwrap()
        .iter()
        .any(|v| v.as_str().unwrap_or("").contains("ForbiddenInSubdir")));

    fx.write(
        "umbrella_tree/Pkg/audit-spec.toml",
        "policy = \"strict-proofs\"\nunknown_descendant_key = true\n",
    );
    let single_umb_malformed = fx
        .cli("umbrella-single-malformed")
        .args(["--json", "audit-spec"])
        .arg(&pkg_umbrella)
        .output()
        .unwrap();
    let single_umb_mal_json = assert_cli_fail_json(
        &single_umb_malformed,
        "single umbrella must fail closed on malformed descendant config",
    );
    assert_eq!(single_umb_mal_json["verdict"].as_str(), Some("error"));
}

#[test]
fn subdirectory_cwd_and_dotdot_relative_paths_enforce_project_path_rules_and_reject_outside_spoofs()
{
    let fx = AuditSpecFixture::new("subdir_path_rules");
    fx.write(
        "repo/turbo-lean.toml",
        r#"
[audit_spec]
policy = "strict-proofs"

[audit_spec.path_rules."lean/**/Proofs/**"]
forbid_decl_kinds = ["inductive"]
allow_decl_names = ["SymExpr"]
forbid_namespaces = ["ConLeche"]
"#,
    );
    fs::create_dir_all(fx.root.join("repo/sub")).unwrap();
    fx.write(
        "repo/lean/Pkg/Proofs/Bad.lean",
        "inductive ForbiddenAst where\n  | mk (n : Nat)\ntheorem p_ok (n : Nat) (h : n > 0) : n >= 1 := by omega\n",
    );
    fx.write(
        "repo/lean/Pkg/Proofs/Good.lean",
        "inductive SymExpr where\n  | lit (n : Nat)\ntheorem good_ok (n : Nat) (h : n > 0) : n >= 1 := by omega\n",
    );
    // Outside `lean/**/Proofs/**`: `inductive` is permitted
    fx.write(
        "repo/lean/Pkg/Defs.lean",
        "inductive AllowedOutsideProofs where\n  | mk (n : Nat)\ntheorem defs_ok (n : Nat) (h : n > 0) : n >= 1 := by omega\n",
    );

    // Negative 1: invoked from `<repo>/lean/Pkg/Proofs` on bare `Bad.lean` and `.`
    for (tag, target) in [("sub-proofs-file", "Bad.lean"), ("sub-proofs-dot", ".")] {
        let out = fx
            .cli(tag)
            .current_dir(fx.root.join("repo/lean/Pkg/Proofs"))
            .args(["--json", "audit-spec", target])
            .output()
            .unwrap();
        let json = assert_cli_fail_json(&out, tag);
        assert!(json["forbidden_scope_decls"]
            .as_array()
            .unwrap()
            .iter()
            .any(|v| v.as_str().unwrap_or("").contains("ForbiddenAst")));
    }

    // Negative 2: invoked from `<repo>/lean` on `Pkg/Proofs/Bad.lean`
    let out_lean = fx
        .cli("sub-lean")
        .current_dir(fx.root.join("repo/lean"))
        .args(["--json", "audit-spec", "Pkg/Proofs/Bad.lean"])
        .output()
        .unwrap();
    let json_lean = assert_cli_fail_json(&out_lean, "cwd=<repo>/lean Pkg/Proofs/Bad.lean");
    assert!(json_lean["forbidden_scope_decls"]
        .as_array()
        .unwrap()
        .iter()
        .any(|v| v.as_str().unwrap_or("").contains("ForbiddenAst")));

    // Negative 3: invoked from `<repo>/sub` via `../lean/Pkg/Proofs/Bad.lean`
    let out_dotdot = fx
        .cli("sub-dotdot")
        .current_dir(fx.root.join("repo/sub"))
        .args(["--json", "audit-spec", "../lean/Pkg/Proofs/Bad.lean"])
        .output()
        .unwrap();
    let json_dotdot = assert_cli_fail_json(&out_dotdot, "../lean/Pkg/Proofs/Bad.lean");
    assert!(json_dotdot["forbidden_scope_decls"]
        .as_array()
        .unwrap()
        .iter()
        .any(|v| v.as_str().unwrap_or("").contains("ForbiddenAst")));

    // Negative 4: invoked from `<repo>` via `sub/../lean/Pkg/Proofs/Bad.lean`
    let out_mid_dotdot = fx
        .cli("root-mid-dotdot")
        .current_dir(fx.root.join("repo"))
        .args(["--json", "audit-spec", "sub/../lean/Pkg/Proofs/Bad.lean"])
        .output()
        .unwrap();
    let json_mid = assert_cli_fail_json(&out_mid_dotdot, "sub/../lean/Pkg/Proofs/Bad.lean");
    assert!(json_mid["forbidden_scope_decls"]
        .as_array()
        .unwrap()
        .iter()
        .any(|v| v.as_str().unwrap_or("").contains("ForbiddenAst")));

    // Positive 1: allowed `SymExpr` inside `Proofs` from subdirectory `cwd`, and `Defs.lean` outside `Proofs`
    let ok_good = fx
        .cli("sub-good")
        .current_dir(fx.root.join("repo/lean/Pkg/Proofs"))
        .args(["--json", "audit-spec", "Good.lean"])
        .output()
        .unwrap();
    assert_cli_ok(&ok_good, "allowed SymExpr from Proofs cwd");

    let ok_defs = fx
        .cli("sub-defs")
        .current_dir(fx.root.join("repo/sub"))
        .args(["--json", "audit-spec", "../lean/Pkg/Defs.lean"])
        .output()
        .unwrap();
    assert_cli_ok(&ok_defs, "Defs.lean outside Proofs via ..");

    // Positive 2: ancestor directory names ABOVE `turbo-lean.toml` (`lean/outer/Proofs/repo/Other.lean`)
    // must NOT falsely trigger repo-relative `lean/**/Proofs/**` rules!
    fx.write(
        "lean/outer/Proofs/nested_repo/turbo-lean.toml",
        r#"
[audit_spec]
policy = "strict-proofs"
"#,
    );
    let nested_other = fx.write(
        "lean/outer/Proofs/nested_repo/src/Other.lean",
        "inductive AllowedBecauseAboveRepoRoot where\n  | mk (n : Nat)\ntheorem nested_ok (n : Nat) (h : n > 0) : n >= 1 := by omega\n",
    );
    let ok_nested = fx
        .cli("nested-above-root")
        .args(["--json", "audit-spec"])
        .arg(&nested_other)
        .output()
        .unwrap();
    assert_cli_ok(
        &ok_nested,
        "ancestor segments above turbo-lean.toml must not falsely match relative path_rules",
    );
}

#[cfg(unix)]
#[test]
fn cache_rejects_symlink_poisoning_symlinked_parents_and_enforces_0600_entries() {
    use std::os::unix::fs::{symlink, PermissionsExt};
    let fx = AuditSpecFixture::new("cache_hardening");
    let bad_spec = fx.write(
        "PoisonTarget.lean",
        "theorem vacuous_bad (n : Nat) (h : n < 0) : n = 99 := by omega\n",
    );
    let cache_dir = fx.root.join("audit-cache-sec");

    // 1. First run on vacuous file fails and writes a `0600` cache entry inside a `0700` dir
    let out1 = fx
        .cli("sec-1")
        .env("TURBO_LEAN_AUDIT_CACHE_DIR", &cache_dir)
        .args(["--json", "audit-spec"])
        .arg(&bad_spec)
        .output()
        .unwrap();
    assert_cli_fail_json(&out1, "initial vacuous audit");

    let dir_mode = fs::symlink_metadata(&cache_dir)
        .unwrap()
        .permissions()
        .mode()
        & 0o777;
    assert_eq!(
        dir_mode, 0o700,
        "expected 0700 cache dir, got {:o}",
        dir_mode
    );

    let entries: Vec<PathBuf> = fs::read_dir(&cache_dir)
        .unwrap()
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("json"))
        .collect();
    assert_eq!(
        entries.len(),
        1,
        "expected 1 cached json file, got {entries:?}"
    );
    let cache_entry = &entries[0];
    let file_mode = fs::symlink_metadata(cache_entry)
        .unwrap()
        .permissions()
        .mode()
        & 0o777;
    assert_eq!(
        file_mode, 0o600,
        "expected 0600 cache entry (not world-readable 0644), got {:o}",
        file_mode
    );

    // 2. Replace `<hash>.json` with a symlink pointing to a forged `"ok": true` JSON payload ->
    //    reader MUST reject via O_NOFOLLOW, recompute fail-closed (`ok: false`, `cache_hit: false`),
    //    and atomically replace the symlink without writing through to `forged_ok.json`!
    let forged_target = fx.write(
        "forged_ok.json",
        r#"{"status":"ok","ok":true,"verdict":"specs_audited","policy":"default","total_specs_audited":1,"vacuous_specs":0,"trivial_specs":0,"tight_specs":1,"vacuous":false,"shadowed_constants":[],"forbidden_scope_decls":[],"stub_defs":[],"warnings":[],"specs":[]}"#,
    );
    fs::remove_file(cache_entry).unwrap();
    symlink(&forged_target, cache_entry).unwrap();

    let out_sym = fx
        .cli("sec-sym")
        .env("TURBO_LEAN_AUDIT_CACHE_DIR", &cache_dir)
        .args(["--json", "audit-spec"])
        .arg(&bad_spec)
        .output()
        .unwrap();
    let sym_json = assert_cli_fail_json(&out_sym, "symlinked cache entry must not poison audit");
    assert_eq!(sym_json["cache_hit"].as_bool(), Some(false));
    let forged_after = fs::read_to_string(&forged_target).unwrap();
    assert!(
        forged_after.contains("\"ok\":true"),
        "atomic cache write must never overwrite symlink target"
    );
    assert!(
        !fs::symlink_metadata(cache_entry)
            .unwrap()
            .file_type()
            .is_symlink(),
        "atomic rename should replace symlink with regular 0600 file"
    );

    // 3. Making `<hash>.json` group/world-readable (`0644`) must also be rejected as untrusted
    fs::set_permissions(cache_entry, fs::Permissions::from_mode(0o644)).unwrap();
    let out_perm = fx
        .cli("sec-perm")
        .env("TURBO_LEAN_AUDIT_CACHE_DIR", &cache_dir)
        .args(["--json", "audit-spec"])
        .arg(&bad_spec)
        .output()
        .unwrap();
    let perm_json = assert_cli_fail_json(&out_perm, "0644 cache entry must miss cache");
    assert_eq!(perm_json["cache_hit"].as_bool(), Some(false));

    // 4. Symlinked parent component in `TURBO_LEAN_AUDIT_CACHE_DIR=<root>/sym_parent/subcache`
    //    must NEVER be traversed or populated!
    let victim_dir = fx.root.join("victim_real_dir");
    fs::create_dir_all(&victim_dir).unwrap();
    let sym_parent = fx.root.join("sym_parent");
    symlink(&victim_dir, &sym_parent).unwrap();
    let escaped_cache = sym_parent.join("subcache");

    let good_spec = fx.write(
        "CleanSpec.lean",
        "theorem clean_spec (n : Nat) (h : n > 0) : n >= 1 := by omega\n",
    );
    let out_parent_sym = fx
        .cli("sec-parent-sym")
        .env("TURBO_LEAN_AUDIT_CACHE_DIR", &escaped_cache)
        .args(["--json", "audit-spec"])
        .arg(&good_spec)
        .output()
        .unwrap();
    let parent_sym_json = assert_cli_ok(
        &out_parent_sym,
        "audit still runs without poisoned cache dir",
    );
    assert_eq!(parent_sym_json["cache_hit"].as_bool(), Some(false));
    assert!(
        !victim_dir.join("subcache").exists(),
        "must NEVER create subdirectories through symlinked cache parent!"
    );
}

#[test]
fn combined_custom_multiline_attributes_and_modifiers_on_local_defs_are_audited_for_stubs() {
    let fx = AuditSpecFixture::new("attr_mod_stubs");

    // Negative: `@[simp, inline]`, `@[csimp]`, multiline `@[simp]\ndef`, `partial def`, `unsafe def`,
    // and `scoped @[reducible] def` hiding identity stubs, unused-param stubs, or tautological wrappers
    let bad = fx.write(
        "AttrStubsBad.lean",
        r#"
@[simp, inline] def comboStub (x : Nat) : Nat := x

@[always_inline]
def multilineUnusedStub (x y : Nat) : Nat := x + 1

partial def partialIdentityStub (x : Nat) : Nat := x

unsafe def unsafeIdentityStub (x : Nat) : Nat := x

scoped @[reducible] def tautPred (x : Nat) : Prop := x = x

theorem bad_combo (x : Nat) : comboStub x = x := rfl
theorem bad_multiline_unused (x y : Nat) : multilineUnusedStub x y > 0 := by omega
theorem bad_partial (x : Nat) : partialIdentityStub x + 1 > 0 := by omega
theorem bad_unsafe (x : Nat) : unsafeIdentityStub x + 1 > 0 := by omega
theorem bad_taut_pred (x : Nat) (h : x > 0) : tautPred x := rfl
"#,
    );
    let bad_out = fx
        .cli("attr-stubs-bad")
        .args(["--json", "audit-spec", "--policy", "strict-proofs"])
        .arg(&bad)
        .output()
        .unwrap();
    let bad_json = assert_cli_fail_json(&bad_out, "attributed/modified stubs must fail");
    let stubs = bad_json["stub_defs"].as_array().unwrap();
    for expected in [
        "comboStub",
        "multilineUnusedStub",
        "partialIdentityStub",
        "unsafeIdentityStub",
    ] {
        assert!(
            stubs
                .iter()
                .any(|s| s.as_str().unwrap_or("").contains(expected)),
            "expected {expected} in stub_defs, got {stubs:?}"
        );
    }
    assert!(
        bad_json["trivial_spec_names"]
            .as_array()
            .unwrap()
            .iter()
            .any(|s| s.as_str() == Some("bad_taut_pred")),
        "expected bad_taut_pred unfolded via scoped @[reducible] def in {bad_json}"
    );

    // Positive: non-stub attributed/modified helper definitions pass cleanly
    let good = fx.write(
        "AttrStubsGood.lean",
        r#"
@[simp, inline] def addTwo (x : Nat) : Nat := x + 2

@[always_inline]
partial def stepCount (x y : Nat) : Nat := x + y + 1

theorem good_attributed (x y : Nat) (h : x > 0) : addTwo x + stepCount x y >= 4 := by omega
"#,
    );
    let good_out = fx
        .cli("attr-stubs-good")
        .args(["--json", "audit-spec", "--policy", "strict-proofs"])
        .arg(&good)
        .output()
        .unwrap();
    let good_json = assert_cli_ok(&good_out, "non-stub attributed defs");
    assert_eq!(good_json["tight_specs"].as_u64(), Some(1));
}

#[test]
fn section_and_anonymous_end_preserve_enclosing_namespace_stack() {
    let fx = AuditSpecFixture::new("section_ns_stack");

    // Negative 1: `section S ... end` inside `namespace TurboLean.Kernel` followed by
    // `namespace ConLeche` MUST resolve to `TurboLean.Kernel.ConLeche` and fail `--forbid-namespace`!
    let bad_ns = fx.write(
        "SectionClobberBad.lean",
        r#"
namespace TurboLean.Kernel
section S
def benignHelper (x : Nat) : Nat := x + 1
end
namespace ConLeche
theorem smuggled_thm (x : Nat) (h : x > 0) : benignHelper x >= 2 := by omega
end ConLeche
end TurboLean.Kernel
"#,
    );
    let bad_out = fx
        .cli("sec-ns-bad")
        .args([
            "--json",
            "audit-spec",
            "--forbid-namespace",
            "TurboLean.Kernel.ConLeche",
        ])
        .arg(&bad_ns)
        .output()
        .unwrap();
    let bad_json = assert_cli_fail_json(
        &bad_out,
        "section ... end inside namespace must not clobber TurboLean.Kernel prefix",
    );
    assert!(bad_json["forbidden_scope_decls"]
        .as_array()
        .unwrap()
        .iter()
        .any(|v| v
            .as_str()
            .unwrap_or("")
            .contains("TurboLean.Kernel.ConLeche")));

    // Negative 2: anonymous `end` after nested `namespace A` -> `namespace B` only pops `B`
    // (leaving `A` active so `namespace ForbiddenSub` is `A.ForbiddenSub`, and local def qualification
    // inside `A` after `section ... end` still resolves `A.localStub`).
    let anon_end_bad = fx.write(
        "AnonEndStackBad.lean",
        r#"
namespace Outer
namespace Inner
def innerVal : Nat := 1
end
section LocalSec
end
def localStub (x : Nat) : Nat := x
namespace ForbiddenChild
theorem child_thm (x : Nat) : Outer.localStub x = x := rfl
end ForbiddenChild
end Outer
"#,
    );
    let anon_out = fx
        .cli("anon-end-bad")
        .args([
            "--json",
            "audit-spec",
            "--forbid-namespace",
            "Outer.ForbiddenChild",
        ])
        .arg(&anon_end_bad)
        .output()
        .unwrap();
    let anon_json = assert_cli_fail_json(&anon_out, "anonymous end pops only innermost scope");
    assert!(anon_json["forbidden_scope_decls"]
        .as_array()
        .unwrap()
        .iter()
        .any(|v| v.as_str().unwrap_or("").contains("Outer.ForbiddenChild")));
    assert!(anon_json["stub_defs"]
        .as_array()
        .unwrap()
        .iter()
        .any(|v| v.as_str().unwrap_or("").contains("Outer.localStub")));

    // Positive: properly closed `end TurboLean.Kernel` before top-level `namespace AllowedOther`
    // does NOT falsely trigger `--forbid-namespace TurboLean.Kernel.AllowedOther`
    let good_ns = fx.write(
        "SectionStackGood.lean",
        r#"
namespace TurboLean.Kernel
section S
def okHelper (x : Nat) : Nat := x + 1
end S
end TurboLean.Kernel

namespace AllowedOther
theorem ok_thm (x : Nat) (h : x > 0) : x >= 1 := by omega
end AllowedOther
"#,
    );
    let good_out = fx
        .cli("sec-ns-good")
        .args([
            "--json",
            "audit-spec",
            "--forbid-namespace",
            "TurboLean.Kernel.AllowedOther",
        ])
        .arg(&good_ns)
        .output()
        .unwrap();
    assert_cli_ok(
        &good_out,
        "closed outer namespace must not bleed into AllowedOther",
    );
}

#[test]
fn empty_or_whitespace_policy_flag_fails_closed() {
    let fx = AuditSpecFixture::new("empty_policy");
    // Even if a valid project config exists, explicit `--policy ""` or `--policy "   "` MUST fail closed!
    fx.write(
        "turbo-lean.toml",
        "[audit_spec]\npolicy = \"strict-proofs\"\n",
    );
    let spec = fx.write(
        "Spec.lean",
        "theorem ok_thm (n : Nat) (h : n > 0) : n >= 1 := by omega\n",
    );

    for (tag, bad_pol) in [("empty-pol", ""), ("space-pol", "   ")] {
        let json_out = fx
            .cli(tag)
            .args(["--json", "audit-spec", "--policy", bad_pol])
            .arg(&spec)
            .output()
            .unwrap();
        let err_json = assert_cli_fail_json(&json_out, tag);
        assert_eq!(err_json["verdict"].as_str(), Some("error"));
        assert!(err_json["error"]
            .as_str()
            .unwrap_or("")
            .contains("Unknown audit-spec policy preset"));

        let text_out = fx
            .cli(&format!("{tag}-txt"))
            .args(["audit-spec", "--policy", bad_pol])
            .arg(&spec)
            .output()
            .unwrap();
        assert!(
            !text_out.status.success(),
            "text mode --policy {bad_pol:?} must exit non-zero"
        );
    }

    // Positive: valid `--policy strict-proofs` succeeds
    let ok_out = fx
        .cli("valid-pol")
        .args(["--json", "audit-spec", "--policy", "strict-proofs"])
        .arg(&spec)
        .output()
        .unwrap();
    assert_cli_ok(&ok_out, "valid --policy strict-proofs");
}

#[cfg(unix)]
struct Fixture(PathBuf);

#[cfg(unix)]
impl Fixture {
    fn new() -> Self {
        use std::os::unix::fs::PermissionsExt;
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

#[cfg(unix)]
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[cfg(unix)]
#[test]
fn private_cache_round_trip_and_disable() {
    use std::os::unix::fs::MetadataExt;
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

#[cfg(unix)]
#[test]
fn unsafe_directory_and_symlink_are_not_used() {
    use std::os::unix::fs::{symlink, PermissionsExt};
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

#[cfg(unix)]
#[test]
fn writable_and_symlink_entries_are_recomputed() {
    use std::os::unix::fs::{symlink, PermissionsExt};
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

#[cfg(unix)]
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

#[test]
fn build_replay_cas_expr_flag_and_elab_audit_contract_v4_m3() {
    let help = Command::new(env!("CARGO_BIN_EXE_turbo-lean"))
        .args(["build", "--help"])
        .output()
        .unwrap();
    assert!(help.status.success());
    let help_stdout = String::from_utf8_lossy(&help.stdout);
    assert!(
        help_stdout.contains("--replay-cas-expr"),
        "expected --replay-cas-expr in `turbo-lean build --help`, got:\n{help_stdout}"
    );

    let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap();
    let elab_audit = fs::read_to_string(repo_root.join("lean/TurboLean/ElabAudit.lean")).unwrap();
    assert!(
        elab_audit.contains(
            "theorem header_pin_prevents_statement_spoofing (surf : SurfaceSig) (kType : ConLeche.Expr)"
        ) && elab_audit.contains(
            "eraseAnnotations (reparseExplicit (ppExplicit kType)) = eraseAnnotations surf ∧"
        ) && elab_audit.contains("shadowedBindersCount surf = 0"),
        "missing Contract V4 M3 header_pin_prevents_statement_spoofing signature"
    );
    assert!(
        elab_audit.contains(
            "theorem cas_proof_replay_sound (env : ConLeche.Env) (expectedType : ConLeche.Expr) (blob : ByteArray)"
        ) && elab_audit.contains(
            "h_replay : verifyCasProofBlob env expectedType blob = true"
        ) && elab_audit.contains(
            "∃ (proofTerm : ConLeche.Expr), decodeExprBlob blob = .ok proofTerm ∧"
        ) && elab_audit.contains("ConLeche.HasType env proofTerm expectedType"),
        "missing Contract V4 M3 cas_proof_replay_sound signature"
    );

    let fx = AuditSpecFixture::new("replay_cas_expr");
    fx.write("lean-toolchain", "leanprover/lean4:v4.35.0\n");
    fx.write(
        "lakefile.toml",
        r#"name = "CasReplayPkg"
defaultTargets = ["CasReplayPkg"]

[[lean_lib]]
name = "CasReplayPkg"
"#,
    );
    fx.write(
        "CasReplayPkg.lean",
        "theorem cas_replay_demo : True := trivial\n",
    );

    // 1. Without seeded CAS expr_shards, `build --replay-cas-expr` fails closed.
    let unseeded = fx
        .cli("cas-replay-unseeded")
        .args(["--json", "build", "--project-dir"])
        .arg(&fx.root)
        .arg("--replay-cas-expr")
        .output()
        .unwrap();
    assert!(
        !unseeded.status.success(),
        "expected unseeded `build --replay-cas-expr` to fail closed, stderr:\n{}",
        String::from_utf8_lossy(&unseeded.stderr)
    );
    assert!(
        String::from_utf8_lossy(&unseeded.stderr).contains("--replay-cas-expr failed closed"),
        "unexpected stderr:\n{}",
        String::from_utf8_lossy(&unseeded.stderr)
    );

    // 2. With `--seed-shards --replay-cas-expr`, warm CAS expr_shard replay succeeds.
    let seeded = fx
        .cli("cas-replay-warm")
        .args(["--json", "build", "--project-dir"])
        .arg(&fx.root)
        .args(["--seed-shards", "--replay-cas-expr"])
        .output()
        .unwrap();
    assert!(
        seeded.status.success(),
        "expected seeded `build --seed-shards --replay-cas-expr` to succeed, stderr:\n{}",
        String::from_utf8_lossy(&seeded.stderr)
    );
    let seeded_json = parse_json_stdout(&seeded, "seeded_cas_replay");
    assert_eq!(seeded_json["cas_expr_replayed"].as_u64(), Some(1));

    // Warm cache-hit replay without `--seed-shards` also succeeds and replays 1 theorem shard.
    let warm = fx
        .cli("cas-replay-warm")
        .args(["--json", "build", "--project-dir"])
        .arg(&fx.root)
        .arg("--replay-cas-expr")
        .output()
        .unwrap();
    assert!(
        warm.status.success(),
        "expected warm `build --replay-cas-expr` to succeed, stderr:\n{}",
        String::from_utf8_lossy(&warm.stderr)
    );
    let warm_json = parse_json_stdout(&warm, "warm_cas_replay");
    assert_eq!(warm_json["cas_expr_replayed"].as_u64(), Some(1));
}

/// A2 (#367, Contract V3): every audited spec carries an honest `witness_provenance`
/// field and the per-file report a `kernel_witness` summary; kernel replay stays OFF by
/// default so the auditor never spawns a Lean toolchain unless asked to.
#[test]
fn audit_spec_kernel_witness_fields_present_and_off_by_default() {
    let fx = AuditSpecFixture::new("kw_default_off");
    let spec = fx.write(
        "KwSpec.lean",
        "theorem kw_succ_pred (n : Nat) (h : 1 ≤ n) : n - 1 + 1 = n := by omega\n",
    );
    let out = fx
        .cli("kw-off")
        .args(["--json", "audit-spec"])
        .arg(&spec)
        .output()
        .unwrap();
    let json = assert_cli_ok(&out, "kernel_witness_default_off");
    let kw = json.get("kernel_witness").unwrap_or_else(|| {
        panic!("audit-spec report must carry a `kernel_witness` summary object: {json}")
    });
    assert_eq!(
        kw["mode"].as_str(),
        Some("off"),
        "kernel witness replay must be off by default: {json}"
    );
    let spec0 = &json["specs"][0];
    assert_eq!(
        spec0["witness_provenance"].as_str(),
        Some("eval_concrete"),
        "a spec with concrete eval witnesses on both sides must be labeled eval_concrete: {json}"
    );
    let pos = spec0["pos_witness"].as_str().unwrap_or("");
    let neg = spec0["neg_witness"].as_str().unwrap_or("");
    assert!(
        pos.starts_with("satisfied_states="),
        "default-off run must keep the eval-level positive witness label, got: {pos}"
    );
    assert!(
        neg.starts_with("eval_refuted_postcondition("),
        "default-off run must keep the eval-level negative witness label, got: {neg}"
    );
}

/// A2 (#367, Contract V3): with `--kernel-witness`, concrete eval witnesses are replayed
/// through the Lean kernel and the labels upgrade to `kernel_certified_*`; when no Lean
/// toolchain resolves, the labels honestly stay at eval level and the summary says so.
#[test]
fn audit_spec_kernel_witness_replay_certifies_or_reports_unavailable() {
    let lean_available = Command::new("lean")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    let fx = AuditSpecFixture::new("kw_replay");
    // `kw_chk`'s conclusion unfolds to `p && !q = false`, whose textual form re-parses in
    // Lean with `=` tighter than `&&` (a type error): the kernel probe must therefore
    // replay the RAW conclusion and let the kernel delta-unfold `chk` itself.
    // DELIBERATE BREAKAGE: the Rust `\` line continuations strip the proof indentation,
    // so the tactic below sits at column 0 and the embedded audited block fails to
    // re-elaborate (unsolved goals at 3:61, "expected command" at 4:0). The probe
    // ladder then certifies through the self-contained fallback, which is what the
    // `kernel_probe_shape == "self_contained"` assertion below pins; re-indenting the
    // fixture flips that shape to "verbatim".
    let spec = fx.write(
        "KwReplay.lean",
        "theorem kw_succ_pred (n : Nat) (h : 1 ≤ n) : n - 1 + 1 = n := by omega\n\
         def chk (p q : Bool) : Bool := p && !q\n\
         theorem kw_chk (p q : Bool) (h : p ≤ q) : chk p q = false := by\n\
           revert h; cases p <;> cases q <;> decide\n",
    );
    let out = fx
        .cli("kw-on")
        .args(["--json", "audit-spec", "--kernel-witness"])
        .arg(&spec)
        .output()
        .unwrap();
    let json = assert_cli_ok(&out, "kernel_witness_replay");
    let kw = &json["kernel_witness"];
    let spec0 = &json["specs"][0];
    let pos = spec0["pos_witness"].as_str().unwrap_or("");
    let neg = spec0["neg_witness"].as_str().unwrap_or("");
    if lean_available {
        assert_eq!(kw["mode"].as_str(), Some("replayed"), "{json}");
        assert!(kw["certified_pos"].as_u64() >= Some(1), "{json}");
        assert!(kw["certified_neg"].as_u64() >= Some(1), "{json}");
        assert!(
            pos.starts_with("kernel_certified_satisfied_precondition("),
            "kernel-replayed positive witness must carry the kernel_certified label, got: {pos}"
        );
        assert!(
            neg.starts_with("kernel_certified_refuted_postcondition("),
            "kernel-replayed negative witness must carry the kernel_certified label, got: {neg}"
        );
        assert!(
            neg.contains("; eval=eval_refuted_postcondition("),
            "the kernel checked one state; the eval count must stay its own labeled \
             layer, got: {neg}"
        );
        assert_eq!(
            spec0["witness_provenance"].as_str(),
            Some("kernel_certified_two_sided"),
            "{json}"
        );
        assert_eq!(
            spec0["kernel_probe_shape"].as_str(),
            Some("self_contained"),
            "a fixture whose audited block fails to re-elaborate must be certified by \
             the self-contained fallback and say so: {json}"
        );
        let chk_neg = json["specs"][1]["neg_witness"].as_str().unwrap_or("");
        assert!(
            chk_neg.starts_with("kernel_certified_refuted_postcondition("),
            "a local-def conclusion must kernel-replay via its RAW text (kernel-side \
             delta unfolding), got: {chk_neg}\n{json}"
        );
    } else {
        assert!(
            kw["mode"]
                .as_str()
                .unwrap_or("")
                .starts_with("unavailable(no_lean_toolchain"),
            "without a Lean toolchain the summary must name the missing toolchain, not a \
             generic or infrastructure unavailability: {json}"
        );
        assert!(
            pos.starts_with("satisfied_states=") && neg.starts_with("eval_refuted_postcondition("),
            "without a Lean toolchain the labels must honestly stay at eval level: {json}"
        );
    }
}

/// A2 r2 (#367): the self-contained fallback must never overrule the audited context.
/// The audited file elaborates on its own (the hypothesis is `False` under its local
/// `LE Nat` instance, so `nomatch h` closes the proof), the host evaluator still finds
/// concrete witnesses under core `Nat` semantics, and the verbatim probe then fails
/// exactly in the appended witness theorems (`1 ≤ 1` is `False` in this context): the
/// kernel has spoken, and a reconstructed probe without the instance must not certify
/// the same witnesses under core semantics.
#[test]
fn audit_spec_kernel_witness_fallback_never_overrules_audited_semantics() {
    let lean_available = Command::new("lean")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    if !lean_available {
        eprintln!("skipping: no `lean` on PATH, nothing to replay");
        return;
    }
    let fx = AuditSpecFixture::new("kw_local_inst");
    let spec = fx.write(
        "KwLocalInst.lean",
        "local instance : LE Nat := ⟨fun _ _ => False⟩\n\
         theorem kw_succ_pred (n : Nat) (h : 1 ≤ n) : n - 1 + 1 = n := nomatch h\n",
    );
    let out = fx
        .cli("kw-local-inst")
        .args(["--json", "audit-spec", "--kernel-witness"])
        .arg(&spec)
        .output()
        .unwrap();
    let json = assert_cli_ok(&out, "kernel_witness_local_instance");
    let text = json.to_string();
    assert!(
        !text.contains("kernel_certified_"),
        "a probe context without the audited source's local instance must never \
         certify a witness: {json}"
    );
    assert_eq!(
        json["kernel_witness"]["mode"].as_str(),
        Some("probe_rejected"),
        "{json}"
    );
}

/// A2 r2 (#367): an ambient `TURBO_LEAN_ALLOWED_AXIOMS` glob must never widen what a
/// `kernel_certified_*` label means: an audited source that rewrites `decide` into
/// `native_decide` proves the appended theorems only through compiler-trust axioms,
/// and the replay must refuse that whatever the environment says.
#[test]
fn audit_spec_kernel_witness_axiom_globs_never_widen_certification() {
    let lean_available = Command::new("lean")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    if !lean_available {
        eprintln!("skipping: no `lean` on PATH, nothing to replay");
        return;
    }
    let fx = AuditSpecFixture::new("kw_axiom_glob");
    let spec = fx.write(
        "KwAxiomGlob.lean",
        "macro_rules | `(tactic| decide) => `(tactic| native_decide)\n\
         theorem kw_succ_pred (n : Nat) (h : 1 ≤ n) : n - 1 + 1 = n := by omega\n",
    );
    let out = fx
        .cli("kw-axiom-glob")
        .env("TURBO_LEAN_ALLOWED_AXIOMS", "Lean.*")
        .args(["--json", "audit-spec", "--kernel-witness"])
        .arg(&spec)
        .output()
        .unwrap();
    let json = assert_cli_ok(&out, "kernel_witness_axiom_glob");
    let text = json.to_string();
    assert!(
        !text.contains("kernel_certified_"),
        "compiler-trust axioms admitted by an ambient glob must never certify a \
         witness: {json}"
    );
    assert_ne!(
        json["kernel_witness"]["mode"].as_str(),
        Some("replayed"),
        "{json}"
    );
    assert!(
        json["kernel_witness"]["mode"]
            .as_str()
            .unwrap_or("")
            .starts_with("unavailable(probe_runner("),
        "the refusal must come from the in-kernel soundness auditor failing closed, \
         not from a merely malformed probe or a missing store: {json}"
    );
}

/// A2 r3 (#367): an unresolved import is no kernel verdict at all. The audited file's
/// semantic context is unknown (the sibling here changes what `≤` means on `Nat`), so
/// replay must say `unavailable(imports_unresolved)` and never let a reconstructed
/// Init-only context certify the witnesses. This fixture is byte-identical to the
/// review's example, which certified before the positive-evidence gate.
#[test]
fn audit_spec_kernel_witness_import_failure_is_unavailable_never_reconstructed() {
    let lean_available = Command::new("lean")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    if !lean_available {
        eprintln!("skipping: no `lean` on PATH, nothing to replay");
        return;
    }
    let fx = AuditSpecFixture::new("kw_import_fail");
    fx.write("Defs.lean", "instance : LE Nat := ⟨fun _ _ => False⟩\n");
    let spec = fx.write(
        "Spec.lean",
        "import Defs\ntheorem kw_succ_pred (n : Nat) (h : 1 ≤ n) : n - 1 + 1 = n := nomatch h\n",
    );
    let out = fx
        .cli("kw-import-fail")
        .args(["--json", "audit-spec", "--kernel-witness"])
        .arg(&spec)
        .output()
        .unwrap();
    let json = assert_cli_ok(&out, "kernel_witness_import_failure");
    let text = json.to_string();
    assert!(
        !text.contains("kernel_certified_"),
        "an unresolved import means the audited semantics are unknown; nothing may be \
         certified: {json}"
    );
    assert!(
        json["kernel_witness"]["mode"]
            .as_str()
            .unwrap_or("")
            .starts_with("unavailable(imports_unresolved"),
        "a failed header must read as replay unavailability, not as a kernel verdict: {json}"
    );
}

/// A2 r3 (#367): a `#exit` in the audited block stops Lean before the appended witness
/// theorems, the probe compiles without them, and the runner's missing-theorem check
/// fails closed as unavailability; the sentinel keeps the reconstructed fallback out.
#[test]
fn audit_spec_kernel_witness_hash_exit_never_reconstructs() {
    let lean_available = Command::new("lean")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    if !lean_available {
        eprintln!("skipping: no `lean` on PATH, nothing to replay");
        return;
    }
    let fx = AuditSpecFixture::new("kw_hash_exit");
    let spec = fx.write(
        "KwExit.lean",
        "theorem kw_succ_pred (n : Nat) (h : 1 ≤ n) : n - 1 + 1 = n := by omega\n#exit\n",
    );
    let out = fx
        .cli("kw-hash-exit")
        .args(["--json", "audit-spec", "--kernel-witness"])
        .arg(&spec)
        .output()
        .unwrap();
    let json = assert_cli_ok(&out, "kernel_witness_hash_exit");
    let text = json.to_string();
    assert!(
        !text.contains("kernel_certified_"),
        "a `#exit`-truncated probe never elaborated the witness theorems; nothing may \
         be certified: {json}"
    );
    assert!(
        json["kernel_witness"]["mode"]
            .as_str()
            .unwrap_or("")
            .starts_with("unavailable("),
        "{json}"
    );
}

/// A2 r3 (#367): the hostile-command scan is the SOLE defence here. The audited
/// block's column-0 tactic breaks in-block (the error-position gate would admit the
/// fallback), the `notation` line never touches the candidates' semantics (a
/// reconstructed probe would certify soundly), and the scan's deliberate file-global
/// conservatism is what keeps the fallback out: deleting the scan turns this red,
/// where the r2 local-instance case has the error-position gate as a second defence.
#[test]
fn audit_spec_kernel_witness_sibling_hostile_disables_fallback() {
    let lean_available = Command::new("lean")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    if !lean_available {
        eprintln!("skipping: no `lean` on PATH, nothing to replay");
        return;
    }
    let fx = AuditSpecFixture::new("kw_sib_hostile");
    // The sibling's defs are pulled into the self-contained probe via the external
    // local-def sweep, so a probe-hostile command in a SIBLING is as disqualifying as
    // one in the audited file itself. The audited file carries the same deliberate
    // column-0 breakage shape as the sole-defence test (every error in-block), so only
    // the hostile scan can refuse the fallback.
    let _sib = fx.write("KwSibDefs.lean", "notation \"⟪\" x \"⟫\" => Nat.succ x\n");
    let spec = fx.write(
        "KwSibHostile.lean",
        "theorem kw_chk (p q : Bool) (h : p ≤ q) : (p && !q) = false := by\n\
         revert h; cases p <;> cases q <;> decide\n",
    );
    let out = fx
        .cli("kw-sib-hostile")
        .args(["--json", "audit-spec", "--kernel-witness"])
        .arg(&spec)
        .output()
        .unwrap();
    let json = assert_cli_ok(&out, "kernel_witness_sibling_hostile");
    let text = json.to_string();
    assert!(
        !text.contains("kernel_certified_"),
        "a sibling declaring notation must disable the reconstructed fallback exactly \
         as the audited file would: {json}"
    );
    assert_eq!(
        json["kernel_witness"]["mode"].as_str(),
        Some("probe_rejected"),
        "{json}"
    );
}

#[cfg(unix)]
#[test]
fn audit_spec_kernel_witness_hostile_scan_is_sole_defence() {
    let lean_available = Command::new("lean")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    if !lean_available {
        eprintln!("skipping: no `lean` on PATH, nothing to replay");
        return;
    }
    let fx = AuditSpecFixture::new("kw_hostile_only");
    // DELIBERATE BREAKAGE: the Rust `\` continuations strip the proof indentation, so
    // the tactic sits at column 0 and the embedded audited block fails to re-elaborate
    // with every error inside the block (the kw_replay fixture's shape), while the
    // appended witness theorems stay true under core semantics.
    let spec = fx.write(
        "KwHostileOnly.lean",
        "notation \"⟪\" x \"⟫\" => Nat.succ x\n\
         theorem kw_chk (p q : Bool) (h : p ≤ q) : (p && !q) = false := by\n\
         revert h; cases p <;> cases q <;> decide\n",
    );
    let out = fx
        .cli("kw-hostile-only")
        .args(["--json", "audit-spec", "--kernel-witness"])
        .arg(&spec)
        .output()
        .unwrap();
    let json = assert_cli_ok(&out, "kernel_witness_hostile_only");
    let text = json.to_string();
    assert!(
        !text.contains("kernel_certified_"),
        "a file declaring notation disables the reconstructed fallback even when the \
         error-position gate would admit it: {json}"
    );
    assert_eq!(
        json["kernel_witness"]["mode"].as_str(),
        Some("probe_rejected"),
        "{json}"
    );
}
