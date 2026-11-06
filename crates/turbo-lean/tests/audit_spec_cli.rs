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

    // 2. Directory containing an umbrella module `Pkg.lean` + `Pkg/A.lean` must audit `Pkg/A.lean`
    //    exactly once (total_specs_audited == 2, never double-counted as 3).
    let dir_root = fx.root.join("umbrella_tree");
    fx.write(
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
}
