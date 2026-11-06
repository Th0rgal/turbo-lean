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
