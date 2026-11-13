use anyhow::{Context, Result};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::Path;
use std::time::Instant;

use crate::db::{self, SingleflightOutcome, TurboStore};
use crate::lake_build::{
    compute_shard_key_with_args, is_file_hash_verified_in_lake_build,
    is_file_verified_in_lake_build, resolve_lake_env, resolve_lean_bin, resolve_remote_lean_path,
    resolve_replayed_prebuilt_module_import,
};
use crate::pack;
use crate::splitter;

use super::diagnostics::{
    extract_mismatch_diagnostics, format_mismatch_diagnostics_summary, insert_allow_sorry_fields,
};
use super::identity::{confirm_decl_identity_with_budget, prewarm_local_check_zygote};
use super::make_attested_shard_receipt_bytes;
use super::remote::emit_remote_decl_result;

#[cfg(test)]
mod regression_tests {
    use super::*;
    use crate::check::{PrivateScratchDir, verified_private_temp_scratch_base};
    use crate::splitter::split_lean_source;
    use std::process::Command;

    #[test]
    fn test_cone_preserves_implicit_dependencies() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let scratch =
            PrivateScratchDir::create(&verified_private_temp_scratch_base()?, "cone_implicit")?;
        fs::write(
            scratch.path.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        for (prefix, target, retained) in [
            (
                "def «hidden helper» : Nat := 7\ndef message : String := s!\"{s!\"{«hidden helper»}\"}\"\n",
                "theorem good : message = \"7\" := rfl\n",
                "def «hidden helper»",
            ),
            (
                "def hiddenHelper : Nat := 7\ndef message : String := s!\"{hiddenHelper}\"\n",
                "theorem good : message = \"7\" := rfl\n",
                "def hiddenHelper",
            ),
            (
                "class AnonymousWitness (α : Type) where\n  value : α\ninstance : AnonymousWitness Nat := ⟨7⟩\n",
                "theorem good : AnonymousWitness.value (α := Nat) = 7 := rfl\n",
                "instance : AnonymousWitness Nat",
            ),
            (
                "class Witness (α : Type) where\n  value : α\ninstance namedWitness : Witness Nat := ⟨7⟩\n",
                "theorem good : Witness.value (α := Nat) = 7 := rfl\n",
                "instance namedWitness",
            ),
            (
                "def f (n : Nat) := 0 + n\n@[simp] theorem simplify_f (n : Nat) : f n = n := Nat.zero_add n\n",
                "theorem good (n : Nat) : f n = n := by simp\n",
                "theorem simplify_f",
            ),
            (
                "def f (n : Nat) := 0 + n\ntheorem simplify_f (n : Nat) : f n = n := Nat.zero_add n\nattribute [simp] simplify_f\n",
                "theorem good (n : Nat) : f n = n := by simp\n",
                "theorem simplify_f",
            ),
            (
                "structure Box where\n  val : Nat\n@[ext] theorem box_ext {a b : Box} (h : a.val = b.val) : a = b := by cases a; cases b; simp_all\n",
                "theorem good {a b : Box} (h : a.val = b.val) : a = b := by ext; exact h\n",
                "theorem box_ext",
            ),
            (
                "structure Box where\n  val : Nat\n@[coe] def Box.toNat (b : Box) : Nat := b.val\ninstance namedCoe : Coe Box Nat := ⟨Box.toNat⟩\n",
                "theorem good (b : Box) : (b : Nat) = b.val := rfl\n",
                "@[coe] def Box.toNat",
            ),
        ] {
            let src = format!("import Lean\n{prefix}theorem wip : False := sorry\n{target}");
            let split = split_lean_source(&src, &[]);
            let idx = splitter::find_decl_shard_index(&split.shards, "good")?.unwrap();
            let cone = build_cone_scoped_decl_audit_source(&src, &split.shards[idx]);
            assert!(cone.contains(retained), "missing {retained}: {cone}");
            assert!(!cone.contains("theorem wip"), "{cone}");
            fs::write(scratch.path.join("Cone.lean"), &cone)?;
            let output = Command::new("lean")
                .arg("Cone.lean")
                .current_dir(&scratch.path)
                .output()?;
            assert!(
                output.status.success(),
                "{cone}\n{}{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
        }
        scratch.remove()?;
        Ok(())
    }

    #[test]
    fn test_clean_decl_uses_interpolation_and_anonymous_instances() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let scratch =
            PrivateScratchDir::create(&verified_private_temp_scratch_base()?, "clean_cone")?;
        fs::write(
            scratch.path.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        fs::write(
            scratch.path.join("lakefile.toml"),
            "name = \"fixture\"\n[[lean_lib]]\nname = \"Cone\"\n",
        )?;
        for source in [
            "def hiddenHelper : Nat := 7\ndef message : String := s!\"{hiddenHelper}\"\ntheorem good : message = \"7\" := rfl\n",
            "class Witness (α : Type) where\n  value : α\ninstance (priority := 100) : Witness Nat where\n  value := 7\ntheorem good : Witness.value (α := Nat) = 7 := rfl\n",
        ] {
            let file = scratch.path.join("Cone.lean");
            fs::write(&file, source)?;
            let mut store = TurboStore::open(Some(
                &scratch
                    .path
                    .join(format!("store_{}", crate::pack::next_tmp_id())),
            ))?;
            let result = crate::check::evaluate_check_command_value(
                &mut store,
                file,
                Some("good".into()),
                scratch.path.clone(),
            )?;
            assert_eq!(result["status"], "theorem_verified", "{result}");
            let result = crate::check::run_check_command_inner(
                &mut store,
                false,
                false,
                false,
                false,
                scratch.path.join("Cone.lean"),
                Some("good".into()),
                scratch.path.clone(),
                None,
                false,
                None,
                true,
            )?;
            assert_eq!(result["status"], "theorem_verified", "{result}");
        }
        scratch.remove()?;
        Ok(())
    }

    #[test]
    fn test_cone_synthesis_attributes_and_anonymous_binders() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        for attribute in [
            "deriving",
            "elab_as_elim",
            "norm_cast",
            "aesop",
            "default_instance",
            "init",
            "builtin_init",
        ] {
            let source = format!(
                "@[{attribute}] def helper : Nat := 1\ntheorem good : True := True.intro\n"
            );
            let split = split_lean_source(&source, &[]);
            let idx = splitter::find_decl_shard_index(&split.shards, "good")?.unwrap();
            assert!(
                build_cone_scoped_decl_audit_source(&source, &split.shards[idx])
                    .contains("def helper"),
                "{attribute}"
            );
            let source = format!(
                "structure Other where\n  value : Nat\naxiom bad : Other\n@[{attribute}] def helper : Other := bad\ntheorem good : True := True.intro\n"
            );
            let split = split_lean_source(&source, &[]);
            let idx = splitter::find_decl_shard_index(&split.shards, "good")?.unwrap();
            assert!(
                !audited_cone_source(&source, &split.shards[idx])?.contains("def helper"),
                "{attribute}"
            );
        }
        for header in [
            "instance [Inhabited α] : Witness α where",
            "instance (priority := 100) : Witness Nat where",
            "instance #[priority] : Witness Nat where",
        ] {
            assert_eq!(
                cone_classify_decl(header),
                Some(("instance", String::new()))
            );
        }
        Ok(())
    }

    #[test]
    fn test_cone_interpolation_lexical_boundaries() {
        for source in [
            r##"s!"literalWip { hiddenHelper }""##,
            r##"s!"\α {hiddenHelper}""##,
            r##"s!"{s!"literalWip {hiddenHelper}"}""##,
            r##"s!"{ ({ value := hiddenHelper } : Box) } literalWip""##,
            r##"s!"{ (hiddenHelper, "} literalWip", r#"{ literalWip"#, '{') }""##,
            "s!\"{ /- } literalWip /- { -/ -/ hiddenHelper -- } literalWip\n }\"",
        ] {
            let tokens = cone_extract_ident_tokens(source);
            assert!(
                tokens.iter().any(|name| name == "hiddenHelper"),
                "{source}: {tokens:?}"
            );
            assert!(
                !tokens.iter().any(|name| name == "literalWip"),
                "{source}: {tokens:?}"
            );
        }
        assert!(
            cone_extract_ident_tokens("«hidden helper»").contains(&"hidden helper".to_string())
        );
        for source in [
            r##""hiddenHelper""##,
            r##"r#"hiddenHelper"#"##,
            r##"s!"hiddenHelper""##,
        ] {
            assert!(
                !cone_extract_ident_tokens(source)
                    .iter()
                    .any(|name| name == "hiddenHelper")
            );
        }
    }

    #[test]
    fn test_cone_dirty_implicit_dependencies_do_not_fall_back() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let scratch =
            PrivateScratchDir::create(&verified_private_temp_scratch_base()?, "dirty_implicit")?;
        fs::write(
            scratch.path.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        fs::write(
            scratch.path.join("lakefile.toml"),
            "name = \"fixture\"\n[[lean_lib]]\nname = \"Cone\"\n",
        )?;
        for source in [
            "class Witness where
  value : Nat
instance (priority := 100) : Witness := ⟨7⟩
instance (priority := 200) : Witness := sorry
theorem good : Witness.value = 7 := rfl
",
            "def value : Nat := 7
@[simp] theorem clean : value = 7 := rfl
@[simp] theorem dirty : value = 7 := sorry
theorem good : value = 7 := by simp
",
            "def value : Nat := 7\ntheorem clean : value = 7 := rfl\nattribute [simp] clean\ntheorem dirty : value = 7 := sorry\nattribute [simp] dirty\ntheorem good : value = 7 := by simp\n",
            "@[simp] theorem clean : True := True.intro\n@[simp] theorem dirty : True := sorry\ntheorem good : True := by simp\n",
            "@[simp] theorem dirty : 0 = 1 := sorry\ntheorem good : 0 = 0 := by simp\n",
            "class Witness where\n  value : Nat\ndef hidden : Nat := sorry\ninstance (priority := 100) : Witness := ⟨7⟩\ninstance (priority := 200) : Witness := ⟨hidden⟩\ntheorem good : Witness.value = 7 := rfl\n",
            "syntax \"chosen\" : term
macro_rules | `(chosen) => `(True.intro)
macro_rules | `(chosen) => `(sorry)
theorem good : True := chosen
",
            "macro \"chosen\" : term => `(sorry)
theorem good : True := chosen
",
            "notation \"chosen\" => (sorry : True)\ntheorem good : True := chosen\n",
            "macro \"unused\" : term => `(sorry)\ntheorem good : True := True.intro\n",
        ] {
            let split = split_lean_source(source, &[]);
            let idx = splitter::find_decl_shard_index(&split.shards, "good")?.unwrap();
            let cone = build_cone_scoped_decl_audit_source(source, &split.shards[idx]);
            assert!(cone.contains("sorry"), "{cone}");
            let file = scratch.path.join("Cone.lean");
            fs::write(&file, source)?;
            let mut store = TurboStore::open(Some(
                &scratch
                    .path
                    .join(format!("store_{}", crate::pack::next_tmp_id())),
            ))?;
            assert!(
                crate::check::evaluate_check_command_value(
                    &mut store,
                    file,
                    Some("good".into()),
                    scratch.path.clone()
                )
                .is_err(),
                "{cone}"
            );
        }
        let source = "class Witness where
  value : Nat
class Other where
  value : Nat
instance : Witness := ⟨7⟩
instance : Other := sorry
theorem good : Witness.value = 7 := rfl
";
        let split = split_lean_source(source, &[]);
        let idx = splitter::find_decl_shard_index(&split.shards, "good")?.unwrap();
        let cone = audited_cone_source(source, &split.shards[idx])?;
        assert!(!cone.contains("sorry"), "{cone}");
        let file = scratch.path.join("Cone.lean");
        fs::write(&file, source)?;
        let mut store = TurboStore::open(Some(&scratch.path.join("store_clean")))?;
        assert_eq!(
            crate::check::evaluate_check_command_value(
                &mut store,
                file,
                Some("good".into()),
                scratch.path.clone()
            )?["status"],
            "theorem_verified"
        );
        scratch.remove()?;

        Ok(())
    }

    #[test]
    fn test_cone_imported_implicit_dependencies_fail_closed() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let scratch =
            PrivateScratchDir::create(&verified_private_temp_scratch_base()?, "imported_implicit")?;
        fs::write(
            scratch.path.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        let target = "theorem good : ∃ n : Nat, n = n := ⟨default, rfl⟩\n";
        let source = format!("instance : Inhabited Nat := ⟨sorry⟩\n{target}");
        let file = scratch.path.join("Cone.lean");
        fs::write(&file, &source)?;
        let mut store = TurboStore::open(Some(&scratch.path.join("store")))?;
        let error = crate::check::evaluate_check_command_value(
            &mut store,
            file.clone(),
            Some("good".into()),
            scratch.path.clone(),
        )
        .expect_err("imported instance must not fall back to the standard instance");
        assert!(
            format!("{error:#}").contains("declaration cone"),
            "{error:#}"
        );
        let source = format!(
            "structure UnrelatedLocalType where\n  value : Nat\ninstance : Inhabited UnrelatedLocalType := ⟨sorry⟩\n{target}"
        );
        fs::write(&file, &source)?;
        assert_eq!(
            crate::check::evaluate_check_command_value(
                &mut store,
                file,
                Some("good".into()),
                scratch.path.clone(),
            )?["status"],
            "theorem_verified"
        );
        scratch.remove()?;
        Ok(())
    }

    #[test]
    fn test_cone_round15_trigger_syntax() {
        for source in [
            "(value n = hidden n)",
            "((value n = hidden n))",
            "forall\n(n : Nat), (value n = hidden n)",
            "∀ (n : Nat), True → (value n = hidden n)",
        ] {
            assert_eq!(
                cone_match_trigger(source, true, false, false).trim(),
                "value n"
            );
        }
        for source in [
            "value = hidden ∧ other = hidden",
            "(value = hidden /\\ other = hidden)",
        ] {
            assert_eq!(cone_match_trigger(source, true, false, false), "");
        }
        for operator in [":=", "==", "!=", "<=", ">=", "=>"] {
            assert!(cone_split_top_level(&format!("a {operator} b"), &["="]).is_none());
        }
        for header in [
            "instance ( priority := 200 ) namedInst : Witness := ⟨7⟩",
            "instance (priority := (100 + 100)) namedInst : Witness := ⟨7⟩",
        ] {
            assert_eq!(
                cone_classify_decl(header),
                Some(("instance", "namedInst".into()))
            );
        }
        for source in [
            "@[reducible] def d (_ : Type) := Nat",
            "@[reducible] def d.{u} (_ : Type u) := Nat",
            "@[reducible] def d : Type → Type := fun _ => Nat",
            "@[reducible] def d := (fun (_ : Type) => Nat)",
            "@[reducible] def d := λ (_ : Type) => Nat",
        ] {
            let signature = cone_command_header(splitter::strip_decl_prefixes(source));
            let result = cone_split_top_level(signature, &[":"]);
            assert!(
                cone_parameterized_alias(
                    source,
                    "def",
                    "d",
                    result.map(|(_, r)| r).unwrap_or(signature),
                    result.is_some()
                ),
                "{source}"
            );
        }
        assert!(!cone_parameterized_alias(
            "def d := Nat",
            "def",
            "d",
            "def d",
            false
        ));
    }

    #[test]
    fn test_cone_round15_implicit_policies_fail_closed() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let scratch =
            PrivateScratchDir::create(&verified_private_temp_scratch_base()?, "round15_policies")?;
        fs::write(
            scratch.path.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        let file = scratch.path.join("Cone.lean");
        let mut store = TurboStore::open(Some(&scratch.path.join("store")))?;
        for source in [
            "structure Unrelated where v : Nat\n@[default_instance 2000] instance : HMul Unrelated Nat Unrelated := ⟨fun _ _ => sorry⟩\ntheorem good : True := True.intro\n",
            "structure Unrelated where v : Nat\ndef myInst : Inhabited Unrelated := ⟨sorry⟩\nattribute [default_instance 2000] myInst\ntheorem good : True := True.intro\n",
            "structure Unrelated where v : Nat\nclass Pick (α : outParam Type) (β : Type) where val : β\ninstance : Pick Unrelated Nat := ⟨sorry⟩\ntheorem good : ∃ n : Nat, n = n := ⟨Pick.val, rfl⟩\n",
            "structure Unrelated where v : Nat\nclass Pick (α : semiOutParam Type) (β : Type) where val : β\ninstance : Pick Unrelated Nat := ⟨sorry⟩\ntheorem good : ∃ n : Nat, n = n := ⟨Pick.val, rfl⟩\n",
            "structure Unrelated where v : Nat\ninstance : Membership Unrelated Nat := ⟨fun _ _ => sorry⟩\ntheorem good : True := True.intro\n",
            "def myInst := (⟨sorry⟩ : Inhabited Nat)\nattribute [instance] myInst\ntheorem good : ∃ n : Nat, n = n := ⟨default, rfl⟩\n",
            "def helper := (sorry : Nat)\nattribute [ext] helper\ntheorem good : True := True.intro\n",
            "structure Unrelated where v : Nat\ndef untypedInst := (⟨sorry⟩ : Inhabited Nat)\ndef typedInst : Inhabited Unrelated := ⟨⟨0⟩⟩\nattribute [instance] untypedInst typedInst\ntheorem good : True := True.intro\n",
            "structure Unrelated where v : Nat\ndef typedInst : Inhabited Unrelated := ⟨sorry⟩\nattribute [instance] typedInst missingInst\ntheorem good : True := True.intro\n",
            "structure Unrelated where v : Nat\n@[simp] def dirty (_ : Unrelated) := (sorry : 0 = 1)\ntheorem good : True := True.intro\n",
            "structure Unrelated where v : Nat\n@[class] structure Pick.{u} (α : outParam (Type u)) (β : Type) where val : β\ninstance : Pick.{0} Unrelated Nat := ⟨sorry⟩\ntheorem good : ∃ n : Nat, n = n := ⟨Pick.val, rfl⟩\n",
            "structure Unrelated where v : Nat\n@[class] inductive Pick (α : semiOutParam Type) (β : Type) where | mk : β → Pick α β\ninstance : Pick Unrelated Nat := .mk sorry\ntheorem good : ∃ p : Pick Nat Nat, p = p := ⟨.mk 0, rfl⟩\n",
            "def value (n : Nat) := n\ndef hidden (n : Nat) := n\n@[simp] theorem dirty (n : Nat) : (value n = hidden n) := sorry\ntheorem good : value 0 = 0 := rfl\n",
            "def value (n : Nat) := n\ndef hidden (n : Nat) := n\n@[simp] theorem dirty : forall\n(n : Nat), (value n = hidden n) := sorry\ntheorem good : value 0 = 0 := rfl\n",
            "def hidden := True\n@[simp] theorem dirty : hidden ∧ True := sorry\ntheorem good : True := by simp\n",
            "structure Unrelated where v : Nat\n@[reducible] def d (_ : Type) := Nat\nabbrev Alias := d Unrelated\ninstance : Inhabited Alias := ⟨sorry⟩\ntheorem good : ∃ n : Nat, n = n := ⟨default, rfl⟩\n",
            "structure Unrelated where v : Nat\n@[reducible] def d : Type → Type := fun _ => Nat\nabbrev Alias := d Unrelated\ninstance : Inhabited Alias := ⟨sorry⟩\ntheorem good : ∃ n : Nat, n = n := ⟨default, rfl⟩\n",
            "structure Unrelated where v : Nat\n@[reducible] def d := (fun (_ : Type) => Nat)\nabbrev Alias := d Unrelated\ninstance : Inhabited Alias := ⟨sorry⟩\ntheorem good : ∃ n : Nat, n = n := ⟨default, rfl⟩\n",
        ] {
            let split = split_lean_source(source, &[]);
            let idx = splitter::find_decl_shard_index(&split.shards, "good")?.unwrap();
            let cone = build_cone_scoped_decl_audit_source(source, &split.shards[idx]);
            assert!(cone.contains("sorry"), "{source}\ncone: {cone}");
            fs::write(&file, source)?;
            let error = crate::check::evaluate_check_command_value(
                &mut store,
                file.clone(),
                Some("good".into()),
                scratch.path.clone(),
            )
            .expect_err("matching implicit dependency must fail closed");
            assert!(
                format!("{error:#}").contains("declaration cone"),
                "{source}\n{error:#}"
            );
        }
        for prefix in [
            "structure Unrelated where v : Nat\ninstance : Inhabited Unrelated := ⟨sorry⟩\n",
            "def unrelated := 0\ndef hidden := 0\n@[csimp] theorem dirty : unrelated = hidden := sorry\n",
        ] {
            let source = format!("{prefix}theorem good : True := True.intro\n");
            let split = split_lean_source(&source, &[]);
            let idx = splitter::find_decl_shard_index(&split.shards, "good")?.unwrap();
            let cone = audited_cone_source(&source, &split.shards[idx])?;
            assert!(!cone.contains("sorry"), "{cone}");
        }
        scratch.remove()?;
        Ok(())
    }

    #[test]
    fn test_cone_scoped_audit_standalone_attribute_mixed_targets() -> Result<()> {
        for attribute in ["instance", "instance 2000"] {
            let source = format!(
                "class Witness where pf : True\nstructure Unrelated where v : Nat\ndef dirtyWitness : Witness := ⟨sorry⟩\ndef cleanUnrelated : Inhabited Unrelated := ⟨⟨0⟩⟩\nattribute [{attribute}] dirtyWitness cleanUnrelated\ntheorem good : True := Witness.pf\n"
            );
            let split = split_lean_source(&source, &[]);
            let idx = splitter::find_decl_shard_index(&split.shards, "good")?.unwrap();
            let cone = build_cone_scoped_decl_audit_source(&source, &split.shards[idx]);
            for retained in [
                "def dirtyWitness",
                "def cleanUnrelated",
                "attribute [",
                "sorry",
            ] {
                assert!(cone.contains(retained), "{cone}");
            }
            assert!(audited_cone_source(&source, &split.shards[idx]).is_err());
        }
        Ok(())
    }

    #[test]
    fn test_cone_universe_levels_and_standalone_class_attributes() -> Result<()> {
        assert_eq!(
            cone_extract_ident_tokens("Inhabited.{u + 1} (ULift.{u} Nat)"),
            ["Inhabited", "ULift", "Nat"]
        );
        assert_eq!(
            cone_match_trigger("_root_.Membership.{u, v} α β", false, true, false),
            "_root_.Membership"
        );
        for parameter in ["outParam", "semiOutParam"] {
            let source = format!(
                "structure Unrelated where v : Nat\nstructure Pick (α : {parameter} Type) (β : Type) where val : β\nattribute [class] Pick\ninstance : Pick Unrelated Nat := ⟨sorry⟩\ntheorem good : ∃ p : Pick Nat Nat, p = p := ⟨⟨0⟩, rfl⟩\n"
            );
            let split = split_lean_source(&source, &[]);
            let idx = splitter::find_decl_shard_index(&split.shards, "good")?.unwrap();
            let cone = build_cone_scoped_decl_audit_source(&source, &split.shards[idx]);
            assert!(cone.contains("sorry"), "{cone}");
            assert!(audited_cone_source(&source, &split.shards[idx]).is_err());
        }
        let source = "universe u\ndef u := 0\ninstance : Inhabited.{u + 1} (ULift.{u} Nat) := ⟨sorry⟩\ntheorem good : ∃ n : ULift.{u} Nat, n = n := ⟨default, rfl⟩\n";
        let split = split_lean_source(source, &[]);
        let idx = splitter::find_decl_shard_index(&split.shards, "good")?.unwrap();
        let cone = build_cone_scoped_decl_audit_source(source, &split.shards[idx]);
        assert!(cone.contains("sorry"), "{cone}");
        assert!(!cone.contains("def u"), "{cone}");
        assert!(audited_cone_source(source, &split.shards[idx]).is_err());
        Ok(())
    }

    #[test]
    fn test_dirty_mutual_peer_bypasses_attested_cache_hit() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let scratch =
            PrivateScratchDir::create(&verified_private_temp_scratch_base()?, "mutual_cache")?;
        let toolchain = "leanprover/lean4:v4.35.0";
        fs::write(
            scratch.path.join("lean-toolchain"),
            format!("{toolchain}\n"),
        )?;
        let file = scratch.path.join("Cone.lean");
        let source = "mutual\ntheorem good : True := dirty\ntheorem dirty : True := sorry\nend\n";
        fs::write(&file, source)?;
        let split = split_lean_source(source, &[]);
        let idx = splitter::find_decl_shard_index(&split.shards, "good")?.unwrap();
        let shard = &split.shards[idx];
        let cone = build_cone_scoped_decl_audit_source(source, shard);
        assert!(split.hygiene.is_clean_modulo_sorry());
        assert!(
            !splitter::audit_hygiene(&splitter::strip_lean_comments(&cone))
                .is_clean_for_certification()
        );
        let attested = crate::check::confirm_decl_identity(source, shard, &scratch.path, &file)?;
        let key = compute_shard_key_with_args(toolchain, shard, &[]);
        let receipt = make_attested_shard_receipt_bytes(
            shard.decl_name(),
            &shard.prefix_env_hash,
            &shard.stmt_hash,
            &shard.proof_hash,
            db::now_unix(),
            Some(&attested.kernel_type_hash),
        )?;
        let mut store = TurboStore::open(Some(&scratch.path.join("store")))?;
        store.batch_publish_theorem_shards(
            toolchain,
            "trusted",
            &[(key.clone(), shard.decl_name().into(), receipt, 1)],
        )?;
        assert!(store.has_attested_decl_receipt(
            &key,
            "trusted",
            shard.decl_name(),
            &attested.kernel_type_hash
        ));
        let result = crate::check::run_check_command_inner(
            &mut store,
            true,
            true,
            false,
            false,
            file.clone(),
            Some("good".into()),
            scratch.path.clone(),
            None,
            false,
            None,
            false,
        );
        let error = result.expect_err("dirty mutual peer must not reuse the attested receipt");
        assert!(
            format!("{error:#}").contains("declaration cone"),
            "{error:#}"
        );
        let result = crate::check::run_check_command_inner(
            &mut store,
            true,
            true,
            false,
            false,
            file,
            Some("good".into()),
            scratch.path.clone(),
            None,
            false,
            None,
            true,
        )?;
        assert_ne!(result["status"], "theorem_cache_hit", "{result}");
        assert_eq!(result["zygote_used"], true, "{result}");
        scratch.remove()?;
        Ok(())
    }

    #[test]
    fn test_cone_rewrite_and_output_parameter_triggers() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let source = "structure UnrelatedLocalType where v : Nat\ndef MyAlias := UnrelatedLocalType\nattribute [abbrev] MyAlias\ninstance : Inhabited MyAlias := ⟨sorry⟩\ntheorem good : True := True.intro\n";
        let split = split_lean_source(source, &[]);
        let idx = splitter::find_decl_shard_index(&split.shards, "good")?.unwrap();
        let cone = build_cone_scoped_decl_audit_source(source, &split.shards[idx]);
        assert!(!cone.contains("MyAlias"), "{cone}");
        let scratch =
            PrivateScratchDir::create(&verified_private_temp_scratch_base()?, "rewrite_triggers")?;
        fs::write(
            scratch.path.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        let mut store = TurboStore::open(Some(&scratch.path.join("store")))?;
        let file = scratch.path.join("Cone.lean");
        for source in [
            "def value (n : Nat) := n\ndef hidden (n : Nat) := n\n@[simp 2000] theorem dirty (n : Nat) : value n = hidden n := sorry\ntheorem good : value 0 = 0 := by simp [value]\n",
            "def value (n : Nat) := n\ndef hidden (n : Nat) := n\ntheorem dirty (n : Nat) : value n = hidden n := sorry\nattribute [simp] dirty\ntheorem good : value 0 = 0 := by simp [value]\n",
            "def hidden := 1\n@[simp high] theorem nat_add_sorry : 1 + 0 = (let _ := hidden; 1) := sorry\ntheorem good : 1 + 0 = 1 := by simp\n",
            "structure UnrelatedLocalType where v : Nat\n@[default_instance 2000] instance : HMul Nat Nat UnrelatedLocalType := ⟨fun _ _ => sorry⟩\ntheorem good : True := by have _ := (1 : Nat) * (2 : Nat); trivial\n",
            "structure UnrelatedLocalType where v : Nat\nclass Pick (α : Type) (β : outParam Type) where val : α\ninstance : Pick Nat UnrelatedLocalType := ⟨sorry⟩\ntheorem good : ∃ n : Nat, n = n := ⟨Pick.val, rfl⟩\n",
        ] {
            let split = split_lean_source(source, &[]);
            let idx = splitter::find_decl_shard_index(&split.shards, "good")?.unwrap();
            let cone = build_cone_scoped_decl_audit_source(source, &split.shards[idx]);
            assert!(cone.contains("sorry"), "{source}\ncone: {cone}");
            fs::write(&file, source)?;
            let error = crate::check::evaluate_check_command_value(
                &mut store,
                file.clone(),
                Some("good".into()),
                scratch.path.clone(),
            )
            .expect_err("active implicit dependency must fail closed");
            assert!(
                format!("{error:#}").contains("declaration cone"),
                "{error:#}"
            );
        }
        assert_eq!(
            cone_classify_decl("instance (priority := 200) namedInst : UnrelatedWitness := ⟨7⟩"),
            Some(("instance", "namedInst".into()))
        );
        let source = "class UnrelatedWitness where v : Nat\ninstance (priority := 200) namedInst : UnrelatedWitness := ⟨7⟩\ntheorem good : namedInst.v = 7 := rfl\n";
        let split = split_lean_source(source, &[]);
        let idx = splitter::find_decl_shard_index(&split.shards, "good")?.unwrap();
        assert!(
            build_cone_scoped_decl_audit_source(source, &split.shards[idx])
                .contains("instance (priority := 200) namedInst")
        );
        fs::write(&file, source)?;
        assert_eq!(
            crate::check::evaluate_check_command_value(
                &mut store,
                file,
                Some("good".into()),
                scratch.path.clone()
            )?["status"],
            "theorem_verified"
        );
        scratch.remove()?;
        Ok(())
    }

    #[test]
    fn test_cone_aliases_and_instance_binders_fail_closed() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let scratch =
            PrivateScratchDir::create(&verified_private_temp_scratch_base()?, "alias_implicit")?;
        fs::write(
            scratch.path.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        let target = "theorem good : ∃ n : Nat, n = n := ⟨default, rfl⟩\n";
        let file = scratch.path.join("Cone.lean");
        let mut store = TurboStore::open(Some(&scratch.path.join("store")))?;
        for prefix in [
            "@[reducible] def MyNat := Nat\ninstance : Inhabited MyNat := ⟨sorry⟩\n",
            "@[reducible] def F (α : Type) : Type := α\ninstance : Inhabited (F Nat) := ⟨sorry⟩\n",
            "class Flag where ok : Unit := ()\ninstance : Flag := {}\ninstance [Flag] : Inhabited Nat := ⟨sorry⟩\n",
            "structure U where v : Nat\ninstance : Inhabited U := ⟨⟨0⟩⟩\ninstance [Inhabited U] : Inhabited Nat := ⟨sorry⟩\n",
            "abbrev MyNat := Nat\ninstance : Inhabited MyNat := ⟨sorry⟩\n",
            "def MyNat := Nat\nattribute [reducible] MyNat\ninstance : Inhabited MyNat := ⟨sorry⟩\n",
            "@[reducible] def MyNat := Nat\nabbrev Alias := MyNat\ninstance : Inhabited Alias := ⟨sorry⟩\n",
            "structure UnrelatedLocalType where v : Nat\n@[reducible] def ConstNat (_ : Type) : Type := Nat\nabbrev MyAlias := ConstNat UnrelatedLocalType\ninstance : Inhabited MyAlias := ⟨sorry⟩\n",
            "structure UnrelatedLocalType where v : Nat\n@[reducible] def ConstNat (_ : Type) : Type := Nat\ninstance : Inhabited (ConstNat UnrelatedLocalType) := ⟨sorry⟩\n",
            "structure Unrelated where v : Nat\ndef myInst [Inhabited Unrelated] : Inhabited Nat := ⟨sorry⟩\nattribute [instance] myInst\n",
        ] {
            let source = format!("{prefix}{target}");
            let split = split_lean_source(&source, &[]);
            let idx = splitter::find_decl_shard_index(&split.shards, "good")?.unwrap();
            let cone = build_cone_scoped_decl_audit_source(&source, &split.shards[idx]);
            assert!(cone.contains("sorry"), "{source}\ncone: {cone}");
            fs::write(&file, &source)?;
            let error = crate::check::evaluate_check_command_value(
                &mut store,
                file.clone(),
                Some("good".into()),
                scratch.path.clone(),
            )
            .expect_err("implicit dependencies must not fall back through aliases or binders");
            assert!(
                format!("{error:#}").contains("declaration cone"),
                "{error:#}"
            );
        }
        let source = "class Flag where ok : Unit := ()\ninstance : Flag := {}\ninstance [Flag] : Inhabited Nat := ⟨0⟩\n";
        fs::write(&file, format!("{source}{target}"))?;
        assert_eq!(
            crate::check::evaluate_check_command_value(
                &mut store,
                file.clone(),
                Some("good".into()),
                scratch.path.clone(),
            )?["status"],
            "theorem_verified"
        );
        for alias in [
            "@[reducible] def MyAlias := UnrelatedLocalType",
            "abbrev MyAlias := UnrelatedLocalType",
            "def MyAlias := UnrelatedLocalType\nattribute [reducible] MyAlias",
            "@[reducible] def First := UnrelatedLocalType\nabbrev MyAlias := First",
        ] {
            fs::write(
                &file,
                format!(
                    "structure UnrelatedLocalType where v : Nat\n{alias}\ninstance : Inhabited MyAlias := ⟨sorry⟩\n{target}"
                ),
            )?;
            assert_eq!(
                crate::check::evaluate_check_command_value(
                    &mut store,
                    file.clone(),
                    Some("good".into()),
                    scratch.path.clone(),
                )?["status"],
                "theorem_verified",
                "{alias}"
            );
        }
        scratch.remove()?;
        Ok(())
    }

    #[test]
    fn test_cone_result_types_skip_nested_binders() {
        for signature in [
            "instance [Flag] : Inhabited Nat",
            "instance (h : Unrelated) : Inhabited Nat",
            "instance {α : Type} [Inhabited α] : Inhabited Nat",
            "instance ⦃α : Type⦄ [Inhabited α] : Inhabited Nat",
            "instance (h : (Nat → Nat)) [Flag] : Inhabited Nat",
        ] {
            assert_eq!(
                cone_split_top_level(signature, &[":"]).unwrap().1.trim(),
                "Inhabited Nat"
            );
        }
        assert!(cone_split_top_level("abbrev Alias := Nat", &[":"]).is_none());
        assert_eq!(
            cone_command_header("macro_rules | `(chosen) => `(sorry)"),
            "macro_rules "
        );
    }

    #[test]
    fn test_cone_local_binders_do_not_reference_global_siblings() -> Result<()> {
        for target in [
            "theorem good : True → True := fun h => h\n",
            "theorem good (h : True) : True := h\n",
            "theorem good : True := by let h := True.intro; exact h\n",
            "theorem good : True := by have h : True := True.intro; exact h\n",
        ] {
            let source = format!("theorem h : False := sorry\n{target}");
            let split = split_lean_source(&source, &[]);
            let idx = splitter::find_decl_shard_index(&split.shards, "good")?.unwrap();
            let cone = build_cone_scoped_decl_audit_source(&source, &split.shards[idx]);
            assert!(!cone.contains("theorem h"), "{cone}");
        }
        for target in [
            "theorem good : False := (fun h => h) h\n",
            "theorem good : False := by let h := h; exact h\n",
            "theorem good : False := by have h : False := h; exact h\n",
            "theorem good (h : h) : False := h\n",
            "theorem good : False := by\n  let f := fun h => h\n  exact h\n",
        ] {
            let source = format!("theorem h : False := sorry\n{target}");
            let split = split_lean_source(&source, &[]);
            let idx = splitter::find_decl_shard_index(&split.shards, "good")?.unwrap();
            assert!(
                build_cone_scoped_decl_audit_source(&source, &split.shards[idx])
                    .contains("theorem h")
            );
        }
        Ok(())
    }

    #[test]
    fn test_cone_hygiene_boundary() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        for helper in [
            "axiom forbidden : True",
            "unsafe def forbidden : Nat := 0",
            "theorem forbidden : True := by native_decide",
        ] {
            let src = format!(
                "{helper}\ntheorem wip : False := sorry\ntheorem good : True := True.intro\n"
            );
            let split = split_lean_source(&src, &[]);
            let idx = splitter::find_decl_shard_index(&split.shards, "good")?.unwrap();
            let cone = audited_cone_source(&src, &split.shards[idx])?;
            assert!(!cone.contains("forbidden"), "{cone}");
            let src = format!(
                "{helper}\ntheorem wip : False := sorry\ntheorem good : True := by have _ := forbidden; trivial\n"
            );
            let split = split_lean_source(&src, &[]);
            let idx = splitter::find_decl_shard_index(&split.shards, "good")?.unwrap();
            assert!(
                audited_cone_source(&src, &split.shards[idx]).is_err(),
                "{src}"
            );
        }
        Ok(())
    }

    #[test]
    fn test_cone_selective_synthesis_and_resolution() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let scratch =
            PrivateScratchDir::create(&verified_private_temp_scratch_base()?, "cone_names")?;
        fs::write(
            scratch.path.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        for prefix in [
            "@[inline] unsafe def forbidden : Nat := 0\n",
            "def unrelated : Nat := 0\naxiom forbidden : unrelated = unrelated\n@[simp] theorem irrelevant : unrelated = unrelated := forbidden\n",
            "structure UnrelatedLocalType where\n  value : Nat\naxiom forbidden : UnrelatedLocalType\ninstance irrelevant : Inhabited UnrelatedLocalType := ⟨forbidden⟩\n",
            "namespace Bad\naxiom helper : True\nend Bad\nnamespace Good\ntheorem helper : True := True.intro\n",
            "namespace Bad\naxiom helper : True\nend Bad\nnamespace Good\ntheorem helper : True := True.intro\nend Good\nopen Good\n",
            "namespace Bad\naxiom helper : True\nend Bad\nnamespace Outer\nnamespace Good\ntheorem helper : True := True.intro\nend Good\nopen Good\n",
        ] {
            let target = if prefix.contains("helper") {
                "theorem good : True := helper\n"
            } else {
                "theorem good : True := True.intro\n"
            };
            let src = format!("{prefix}{target}");
            let split = split_lean_source(&src, &[]);
            let idx = splitter::find_decl_shard_index(&split.shards, "good")?.unwrap();
            let cone = audited_cone_source(&src, &split.shards[idx])?;
            assert!(!cone.contains("forbidden"), "{cone}");
            assert!(!cone.contains("axiom helper"), "{cone}");
            if prefix.contains("helper") {
                assert!(cone.contains("theorem helper"), "{cone}");
            }
            fs::write(scratch.path.join("Cone.lean"), &cone)?;
            let output = Command::new("lean")
                .arg("Cone.lean")
                .current_dir(&scratch.path)
                .output()?;
            assert!(
                output.status.success(),
                "{cone}\n{}{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
        }
        scratch.remove()?;
        Ok(())
    }

    #[test]
    fn test_cone_post_target_runtime_attachments() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        for suffix in [
            "unsafe def fast : Nat := 0\nattribute [implemented_by fast] good\n",
            "@[csimp] theorem replacement : good = 0 := sorry\n",
            "theorem replacement : good = 0 := sorry\nattribute [csimp] replacement\n",
        ] {
            let src = format!("theorem good : 0 = 0 := rfl\n{suffix}");
            let split = split_lean_source(&src, &[]);
            let idx = splitter::find_decl_shard_index(&split.shards, "good")?.unwrap();
            assert!(
                audited_cone_source(&src, &split.shards[idx]).is_err(),
                "{src}"
            );
        }
        for attachment in [
            "@[csimp] theorem replacement : base = base := sorry\n",
            "theorem replacement : base = base := sorry\nattribute [csimp] replacement\n",
        ] {
            let source =
                format!("def base : Nat := 0\n{attachment}theorem good : base = 0 := rfl\n");
            let split = split_lean_source(&source, &[]);
            let idx = splitter::find_decl_shard_index(&split.shards, "good")?.unwrap();
            assert!(
                audited_cone_source(&source, &split.shards[idx]).is_err(),
                "{source}"
            );
        }
        let source = "theorem good : True := True.intro\ndef other : Nat := 0\n@[csimp] theorem replacement : other = other := sorry\n";
        let split = split_lean_source(source, &[]);
        let idx = splitter::find_decl_shard_index(&split.shards, "good")?.unwrap();
        assert!(!audited_cone_source(source, &split.shards[idx])?.contains("replacement"));
        Ok(())
    }

    #[test]
    fn test_cone_headers_after_block_comments() -> Result<()> {
        for prefix in ["/- comment\n-/ ", "/- outer /- inner -/ -/ "] {
            let source = format!(
                "def x := 0\n{prefix}theorem lost : x = 0 := rfl\n/- infer\n-/ theorem infer_lost : x = 0\n  | => rfl\ntheorem visible : x = 0 := lost\n"
            );
            let split = split_lean_source(&source, &[]);
            let idx = splitter::find_decl_shard_index(&split.shards, "lost")?.unwrap();
            let cone = audited_cone_source(&source, &split.shards[idx])?;
            assert!(cone.contains("def x := 0"), "{cone}");
            assert!(cone.contains("theorem lost"), "{cone}");
            assert!(!cone.contains("infer_lost"), "{cone}");
        }
        Ok(())
    }

    #[test]
    fn test_cone_early_hygiene_before_import_refresh() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let scratch =
            PrivateScratchDir::create(&verified_private_temp_scratch_base()?, "cone_early")?;
        fs::write(
            scratch.path.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        fs::write(
            scratch.path.join("lakefile.toml"),
            "name = \"fixture\"\n[[lean_lib]]\nname = \"Cone\"\n",
        )?;
        for source in [
            "import Missing\naxiom bad : True\ntheorem good : True := bad\n",
            "import Missing\ntheorem good : True := True.intro\n@[csimp] theorem replacement : good = good := sorry\n",
        ] {
            fs::write(scratch.path.join("Cone.lean"), source)?;
            let mut store = TurboStore::open(Some(
                &scratch
                    .path
                    .join(format!("store_{}", crate::pack::next_tmp_id())),
            ))?;
            let error = crate::check::evaluate_check_command_value(
                &mut store,
                scratch.path.join("Cone.lean"),
                Some("good".into()),
                scratch.path.clone(),
            )
            .unwrap_err();
            let output = format!("{error:#}");
            assert!(output.contains("declaration cone"), "{output}");
            assert!(
                !scratch
                    .path
                    .join(".lake/build/lib/lean/Cone.olean")
                    .exists()
            );
        }
        scratch.remove()?;
        Ok(())
    }

    #[test]
    fn test_cone_recovers_truncated_source_with_complete_shard_text() -> Result<()> {
        let scratch =
            PrivateScratchDir::create(&verified_private_temp_scratch_base()?, "cone_recover")?;
        let prefix = "theorem good : True := True.intro\n";
        let full = format!("{prefix}@[csimp] theorem replacement : good = good := sorry\n");
        let file = scratch.path.join("Cone.lean");
        fs::write(&file, &full)?;
        let split = split_lean_source(&full, &[]);
        let shard = &split.shards[splitter::find_decl_shard_index(&split.shards, "good")?.unwrap()];
        assert!(!shard.signature_text.is_empty() && !shard.proof_text.is_empty());
        let recovered = recover_decl_source(prefix.to_string(), &file)?;
        assert_eq!(recovered, full);
        assert!(audited_cone_source(&recovered, shard).is_err());
        scratch.remove()?;
        Ok(())
    }

    #[test]
    fn test_umbrella_decl_ambiguity() -> Result<()> {
        let scratch =
            PrivateScratchDir::create(&verified_private_temp_scratch_base()?, "umbrella")?;
        fs::write(
            scratch.path.join("Root.lean"),
            "import Left\nimport Right\n",
        )?;
        fs::write(
            scratch.path.join("Left.lean"),
            "namespace L\ntheorem good : True := True.intro\nend L\n",
        )?;
        fs::write(
            scratch.path.join("Right.lean"),
            "namespace R\ntheorem good : True := True.intro\nend R\n",
        )?;
        let resolve = |target| {
            crate::check::resolve_workspace_imported_decl_submodule(
                &scratch.path,
                &scratch.path.join("Root.lean"),
                target,
            )
        };
        assert!(resolve("good").is_err());
        assert_eq!(resolve("L.good")?, Some(scratch.path.join("Left.lean")));
        scratch.remove()?;
        Ok(())
    }

    #[test]
    fn test_scoped_build_target_excludes_wip() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let scratch =
            PrivateScratchDir::create(&verified_private_temp_scratch_base()?, "scoped_build")?;
        fs::create_dir_all(scratch.path.join("P"))?;
        fs::write(
            scratch.path.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        fs::write(
            scratch.path.join("lakefile.toml"),
            "name = \"fixture\"\n[[lean_lib]]\nname = \"P\"\n",
        )?;
        fs::write(
            scratch.path.join("P/Good.lean"),
            "theorem good : True := True.intro\n",
        )?;
        fs::write(
            scratch.path.join("P/Wip.lean"),
            "theorem wip : False := by exact unknown_proof\n",
        )?;
        let cfg = crate::module_builder::resolve_project_config(&scratch.path)?;
        let targets = ["+P.Good".to_string()];
        let dag = crate::module_builder::build_module_dag(&cfg, &targets)?;
        assert!(dag.nodes.contains_key("P.Good"));
        assert!(!dag.nodes.contains_key("P.Wip"));
        let mut store = TurboStore::open(Some(&scratch.path.join("store")))?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &scratch.path,
            &targets,
            "trusted",
            0,
            false,
            true,
            None,
        )?;
        assert!(
            scratch
                .path
                .join(".lake/build/lib/lean/P/Good.olean")
                .is_file()
        );
        assert!(
            !scratch
                .path
                .join(".lake/build/lib/lean/P/Wip.olean")
                .exists()
        );
        scratch.remove()?;
        Ok(())
    }

    #[test]
    fn test_check_runtime_policy_deferral_cli_and_config() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        use clap::Parser;
        struct PolicyEnv(Vec<(std::ffi::OsString, std::ffi::OsString)>);
        impl Drop for PolicyEnv {
            fn drop(&mut self) {
                for (key, _) in std::env::vars_os().filter(|(key, _)| {
                    let key = key.to_string_lossy();
                    key.starts_with("TURBO_LEAN_") || key.starts_with("LEAN_NATIVE_")
                }) {
                    std::env::remove_var(key);
                }
                for (key, value) in &self.0 {
                    std::env::set_var(key, value);
                }
            }
        }
        let _env = PolicyEnv(
            std::env::vars_os()
                .filter(|(key, _)| {
                    let key = key.to_string_lossy();
                    key.starts_with("TURBO_LEAN_") || key.starts_with("LEAN_NATIVE_")
                })
                .collect(),
        );
        let dir = std::env::temp_dir().join(format!("check_policy_{}", crate::pack::next_tmp_id()));
        fs::create_dir_all(&dir)?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            dir.join("lakefile.toml"),
            "name = \"fixture\"\n[[lean_lib]]\nname = \"Policy\"\n",
        )?;
        fs::write(
            dir.join("Policy.lean"),
            "unsafe def fast : Nat := 1\n@[implemented_by fast] def slow : Nat := 1\n@[csimp] theorem replacement : slow = slow := rfl\nnamespace N\ntheorem good : True := by trivial\nend N\n",
        )?;
        let policies = [
            ("TURBO_LEAN_ALLOWED_UNSAFE", "fast"),
            ("TURBO_LEAN_ALLOWED_IMPLEMENTED_BY", "slow"),
            ("TURBO_LEAN_ALLOWED_CSIMP", "replacement"),
        ];
        for config in [false, true] {
            if config {
                fs::write(
                    dir.join("turbo-lean.toml"),
                    "[unsafe]\nallow = [\"fast\"]\n[implemented_by]\nallow = [\"slow\"]\n[csimp]\nallow = [\"replacement\"]\n",
                )?;
            }
            for target in [None, Some("good"), Some("_root_.N.good")] {
                let mut args = vec![
                    "turbo-lean".to_string(),
                    "--no-daemon".into(),
                    "--no-telemetry".into(),
                    "--json".into(),
                    "--cache-dir".into(),
                    dir.join("cache").display().to_string(),
                    "check".into(),
                    "Policy.lean".into(),
                    "--project-dir".into(),
                    dir.display().to_string(),
                ];
                for (key, value) in policies {
                    if config {
                        std::env::remove_var(key);
                    } else {
                        std::env::set_var(key, value);
                    }
                    std::env::remove_var(format!("{key}_FROM_CONFIG"));
                }
                if let Some(target) = target {
                    args.extend(["--decl".into(), target.into()]);
                }
                let cli = crate::Cli::try_parse_from(args)?;
                match &cli.command {
                    crate::Commands::Check {
                        file,
                        decl,
                        project_dir,
                        allow_sorry,
                        ..
                    } => {
                        assert_eq!(file, Path::new("Policy.lean"));
                        assert_eq!(decl.as_deref(), target);
                        assert_eq!(project_dir, &dir);
                        assert!(!allow_sorry);
                    }
                    _ => anyhow::bail!("expected check command"),
                }
                crate::run(cli).with_context(|| format!("config={config} target={target:?}"))?;
            }
        }
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn test_single_decl_original_sorry_dependencies_and_mutual() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = std::env::temp_dir().join(format!("decl_sibling_{}", crate::pack::next_tmp_id()));
        fs::create_dir_all(&dir)?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            dir.join("lakefile.toml"),
            "name = \"fixture\"\n[[lean_lib]]\nname = \"Poison\"\n",
        )?;
        let file = dir.join("Poison.lean");
        fs::write(&file, "theorem baseline : True := by trivial\n")?;
        for args in [
            vec!["init"],
            vec!["add", "."],
            vec![
                "-c",
                "user.name=Fixture",
                "-c",
                "user.email=fixture@example.com",
                "-c",
                "commit.gpgsign=false",
                "commit",
                "-m",
                "fixture",
            ],
        ] {
            assert!(
                std::process::Command::new("git")
                    .args(args)
                    .current_dir(&dir)
                    .output()?
                    .status
                    .success()
            );
        }
        for sibling in [
            "theorem bad : False := sorry",
            "theorem bad : False := by sorry",
            "def bad : False := sorry",
        ] {
            for (body, accepted) in [("False := bad", false), ("True := by trivial", true)] {
                for mutual in [false, true] {
                    let mut store = TurboStore::open(Some(
                        &dir.join(format!("store_{}", crate::pack::next_tmp_id())),
                    ))?;
                    let (open, close) = if mutual {
                        (
                            "mutual\n",
                            if accepted {
                                "theorem other : True := good\nend\n"
                            } else {
                                "theorem other : False := good\nend\n"
                            },
                        )
                    } else {
                        ("", "")
                    };
                    fs::write(
                        &file,
                        format!(
                            "{sibling}\nnamespace N\n{open}theorem good : {body}\n{close}end N\n"
                        ),
                    )?;
                    let result = crate::check::evaluate_check_command_value(
                        &mut store,
                        file.clone(),
                        Some(if mutual { "_root_.N.good" } else { "good" }.into()),
                        dir.clone(),
                    );
                    assert_eq!(
                        result.is_ok(),
                        accepted,
                        "{sibling}/{body}/mutual={mutual}: {result:?}"
                    );
                    if accepted {
                        let result = result?;
                        assert_eq!(result["decl"], "N.good");
                        assert_eq!(result["status"], "theorem_verified");
                    } else {
                        let source = fs::read_to_string(&file)?;
                        let split = split_lean_source(&source, &[]);
                        let target = split
                            .shards
                            .iter()
                            .find(|s| s.decl_name() == "N.good")
                            .unwrap();
                        let key =
                            compute_shard_key_with_args("leanprover/lean4:v4.35.0", target, &[]);
                        assert!(
                            store
                                .batch_get_theorem_shards(&[key], "trusted")?
                                .is_empty()
                        );
                    }
                }
            }
        }
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    fn git_commit_all(dir: &Path, msg: &str) -> Result<bool> {
        if std::env::var_os("TURBO_LEAN_GIT").is_none() {
            if let Some(path) = [
                "/var/lib/orb-node/.local/share/git-2.47.3/bin/git",
                "/tmp/git-2.47.1/git",
                "/var/lib/sandboxed-node/.local/share/git-2.47.3/bin/git",
            ]
            .into_iter()
            .map(Path::new)
            .find(|path| path.is_file())
            {
                std::env::set_var("TURBO_LEAN_GIT", path);
            }
        }
        let Some(git_prog) = crate::trusted_tools::discover_or_skip_trusted_git_for_test(dir)?
        else {
            return Ok(false);
        };
        std::env::set_var("TURBO_LEAN_GIT", &git_prog);
        for args in [
            vec!["init"],
            vec!["add", "-A"],
            vec![
                "-c",
                "user.name=Fixture",
                "-c",
                "user.email=fixture@example.com",
                "-c",
                "commit.gpgsign=false",
                "commit",
                "-m",
                msg,
            ],
        ] {
            let mut cmd = std::process::Command::new(&git_prog);
            cmd.env_remove("GIT_DIR")
                .env_remove("GIT_WORK_TREE")
                .env_remove("GIT_INDEX_FILE")
                .args(&args)
                .current_dir(dir);
            let out = cmd.output()?;
            if args[0] != "init" {
                anyhow::ensure!(
                    out.status.success(),
                    "git {:?} failed: {}{}",
                    args,
                    String::from_utf8_lossy(&out.stdout),
                    String::from_utf8_lossy(&out.stderr)
                );
            }
        }
        Ok(true)
    }

    #[test]
    fn test_blocker1_proof_and_internal_names_and_mutual_cas_poisoning() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir =
            std::env::temp_dir().join(format!("decl_blocker1_cas_{}", crate::pack::next_tmp_id()));
        fs::create_dir_all(&dir)?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            dir.join("lakefile.toml"),
            "name = \"fixture\"\n[[lean_lib]]\nname = \"Poison\"\n",
        )?;
        let file = dir.join("Poison.lean");
        fs::write(&file, "theorem baseline : True := by trivial\n")?;
        if !git_commit_all(&dir, "init")? {
            fs::remove_dir_all(&dir)?;
            return Ok(());
        }

        {
            let mut store = TurboStore::open(Some(
                &dir.join(format!("store_{}", crate::pack::next_tmp_id())),
            ))?;
            fs::write(
                &file,
                "theorem a_sib : False := sorry\ntheorem z_proof_final : False := a_sib\n",
            )?;
            let res = crate::check::evaluate_check_command_value(
                &mut store,
                file.clone(),
                Some("z_proof_final".into()),
                dir.clone(),
            );
            assert!(
                res.is_err(),
                "z_proof_final depending on sorry sibling must fail: {res:?}"
            );
        }

        {
            let mut store = TurboStore::open(Some(
                &dir.join(format!("store_{}", crate::pack::next_tmp_id())),
            ))?;
            fs::write(
                &file,
                "theorem a_sib : False := sorry\nnamespace N._Internal\ntheorem good : False := a_sib\nend N._Internal\n",
            )?;
            let res = crate::check::evaluate_check_command_value(
                &mut store,
                file.clone(),
                Some("good".into()),
                dir.clone(),
            );
            assert!(
                res.is_err(),
                "N._Internal.good depending on sorry sibling must fail: {res:?}"
            );
        }

        {
            let mut store = TurboStore::open(Some(
                &dir.join(format!("store_{}", crate::pack::next_tmp_id())),
            ))?;
            fs::write(
                &file,
                "mutual\ntheorem z_proof_final : False := later_sib\ntheorem later_sib : False := sorry\nend\n",
            )?;
            let res1 = crate::check::evaluate_check_command_value(
                &mut store,
                file.clone(),
                Some("z_proof_final".into()),
                dir.clone(),
            );
            assert!(
                res1.is_err(),
                "mutual z_proof_final depending on later sorry sibling must fail on first run: {res1:?}"
            );
            let res2 = crate::check::evaluate_check_command_value(
                &mut store,
                file.clone(),
                Some("z_proof_final".into()),
                dir.clone(),
            );
            assert!(
                res2.is_err(),
                "mutual z_proof_final must not hit poisoned CAS on second run: {res2:?}"
            );
            let source = fs::read_to_string(&file)?;
            let split = split_lean_source(&source, &[]);
            let target = split
                .shards
                .iter()
                .find(|s| s.decl_name() == "z_proof_final")
                .unwrap();
            let key = compute_shard_key_with_args("leanprover/lean4:v4.35.0", target, &[]);
            assert!(
                store
                    .batch_get_theorem_shards(&[key], "trusted")?
                    .is_empty(),
                "trusted CAS must remain empty after rejected mutual sorry dependency"
            );
        }

        {
            let mut store = TurboStore::open(Some(
                &dir.join(format!("store_{}", crate::pack::next_tmp_id())),
            ))?;
            fs::write(
                &file,
                "theorem a_sib : False := sorry\nnamespace N._Internal\ntheorem z_proof_clean : True := by trivial\nend N._Internal\n",
            )?;
            let res = crate::check::evaluate_check_command_value(
                &mut store,
                file.clone(),
                Some("z_proof_clean".into()),
                dir.clone(),
            )?;
            assert_eq!(res["status"], "theorem_verified");
        }

        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn test_blocker2_nonlocal_dependents_with_sorry_sibling_and_large_suffix_hygiene() -> Result<()>
    {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir =
            std::env::temp_dir().join(format!("decl_blocker2_deps_{}", crate::pack::next_tmp_id()));
        fs::create_dir_all(dir.join("P"))?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            dir.join("lakefile.toml"),
            "name = \"fixture\"\n[[lean_lib]]\nname = \"P\"\n",
        )?;
        fs::write(dir.join("P.lean"), "import P.A\nimport P.B\n")?;
        fs::write(dir.join("P/A.lean"), "theorem good : 1 = 1 := rfl\n")?;
        fs::write(
            dir.join("P/B.lean"),
            "import P.A\ntheorem downstream : 1 = 1 := good\n",
        )?;
        if !git_commit_all(&dir, "initial clean workspace")? {
            fs::remove_dir_all(&dir)?;
            return Ok(());
        }

        fs::write(
            dir.join("P/A.lean"),
            "theorem wip : False := sorry\ntheorem good : 2 = 2 := rfl\n",
        )?;
        let mut store = TurboStore::open(Some(
            &dir.join(format!("store_{}", crate::pack::next_tmp_id())),
        ))?;
        let broken_res = crate::check::evaluate_check_command_value(
            &mut store,
            dir.join("P/A.lean"),
            Some("good".into()),
            dir.clone(),
        );
        assert!(
            broken_res.is_err(),
            "non-local signature edit breaking downstream P/B.lean must fail even when P/A.lean has sorry sibling: {broken_res:?}"
        );
        assert!(
            !dir.join(".lake/build/lib/lean/P/A.olean").exists(),
            "sorry-tainted P/A.olean must not remain in .lake/build after failed dependent recheck"
        );

        fs::write(
            dir.join("P/B.lean"),
            "import P.A\ntheorem downstream : 2 = 2 := good\n",
        )?;
        let fixed_res = crate::check::evaluate_check_command_value(
            &mut store,
            dir.join("P/A.lean"),
            Some("good".into()),
            dir.clone(),
        )?;
        assert_eq!(fixed_res["decl"], "good");
        assert!(
            !dir.join(".lake/build/lib/lean/P/A.olean").exists(),
            "sorry-tainted P/A.olean must be purged after dependent recheck"
        );

        fs::write(
            dir.join("P/B.lean"),
            "import P.A\ntheorem downstream : False := wip\n",
        )?;
        let tainted = crate::check::evaluate_check_command_value(
            &mut store,
            dir.join("P/A.lean"),
            Some("good".into()),
            dir.clone(),
        );
        let err = tainted.expect_err("dependent inherited sorryAx");
        assert!(
            err.to_string().contains("strict soundness audit"),
            "{err:#}"
        );
        fs::write(
            dir.join("P/B.lean"),
            "import P.A\ntheorem downstream : 2 = 2 := good\n",
        )?;

        fs::write(
            dir.join("Extra.lean"),
            "import P.A\ntheorem standalone : False := wip\n",
        )?;
        let tainted_standalone = crate::check::evaluate_check_command_value(
            &mut store,
            dir.join("P/A.lean"),
            Some("good".into()),
            dir.clone(),
        );
        let err = tainted_standalone.expect_err("standalone inherited sorryAx");
        assert!(
            err.to_string().contains("strict soundness audit"),
            "{err:#}"
        );
        fs::remove_file(dir.join("Extra.lean"))?;

        let mut big_src = String::with_capacity(72 * 1024);
        for i in 0..8 {
            big_src.push_str(&format!(
                "theorem pad_thm_{i:04} : ({i} : Nat) = {i} := rfl\n"
            ));
        }
        big_src.push_str("theorem target_after_pad : 1 = 1 := rfl\n");
        for i in 0..1050 {
            big_src.push_str(&format!(
                "-- trailing comment line {i:04} padding suffix over 64KiB total file size\n"
            ));
        }
        big_src.push_str("def tail_sorry : False := sorry\n");
        assert!(big_src.len() > 65 * 1024);
        let big_file = dir.join("P/Big.lean");
        fs::write(&big_file, &big_src)?;
        git_commit_all(&dir, "commit >64KiB file with trailing def sorry")?;

        let mut big_store = TurboStore::open(Some(
            &dir.join(format!("store_big_{}", crate::pack::next_tmp_id())),
        ))?;
        let canon_dir = dir.canonicalize()?;
        let canon_big = big_file.canonicalize()?;
        crate::pr_verify::warm_git_head_tree_cache(
            &big_store,
            &canon_dir,
            std::slice::from_ref(&canon_big),
            "leanprover/lean4:v4.35.0",
            None,
        );
        let modified_big = big_src.replacen(
            "theorem target_after_pad : 1 = 1 := rfl\n",
            "theorem target_after_pad : 3 = 3 := rfl\n",
            1,
        );
        fs::write(&big_file, &modified_big)?;
        let whole_big_res = crate::check::evaluate_check_command_value(
            &mut big_store,
            big_file.clone(),
            None,
            dir.clone(),
        );
        assert!(
            whole_big_res.is_err(),
            "whole-file check on >64KiB prefix-split file must detect sorry in trailing def suffix: {whole_big_res:?}"
        );
        let allow_res_1 = crate::check::run_check_command_inner(
            &mut big_store,
            true,
            true,
            false,
            false,
            big_file.clone(),
            None,
            dir.clone(),
            None,
            false,
            None,
            true,
        )?;
        assert_eq!(allow_res_1["status"], "verified_modulo_sorry");
        assert_eq!(allow_res_1["used_sorry"], true);
        let allow_res_2 = crate::check::run_check_command_inner(
            &mut big_store,
            true,
            true,
            false,
            false,
            big_file.clone(),
            None,
            dir.clone(),
            None,
            false,
            None,
            true,
        )?;
        assert_eq!(allow_res_2["status"], "verified_modulo_sorry");
        assert_eq!(allow_res_2["used_sorry"], true);

        let mut unsafe_big_src = String::with_capacity(72 * 1024);
        for i in 0..8 {
            unsafe_big_src.push_str(&format!(
                "theorem pad_thm_{i:04} : ({i} : Nat) = {i} := rfl\n"
            ));
        }
        unsafe_big_src.push_str("theorem target_after_pad : 3 = 3 := rfl\n");
        for i in 0..1050 {
            unsafe_big_src.push_str(&format!(
                "-- trailing comment line {i:04} padding suffix over 64KiB total file size\n"
            ));
        }
        unsafe_big_src.push_str("unsafe def tail_unsafe : Nat := 42\n");
        assert!(unsafe_big_src.len() > 65 * 1024);
        fs::write(&big_file, &unsafe_big_src)?;
        git_commit_all(&dir, "commit >64KiB file with trailing unsafe def")?;
        crate::pr_verify::warm_git_head_tree_cache(
            &big_store,
            &canon_dir,
            std::slice::from_ref(&canon_big),
            "leanprover/lean4:v4.35.0",
            None,
        );
        let modified_unsafe_big = unsafe_big_src.replacen(
            "theorem target_after_pad : 3 = 3 := rfl\n",
            "theorem target_after_pad : 4 = 4 := rfl\n",
            1,
        );
        fs::write(&big_file, &modified_unsafe_big)?;
        let strict_unsafe_whole = crate::check::evaluate_check_command_value(
            &mut big_store,
            big_file.clone(),
            None,
            dir.clone(),
        );
        assert!(
            strict_unsafe_whole.is_err(),
            "whole-file check on >64KiB prefix-split file must reject unallowed unsafe def in trailing suffix: {strict_unsafe_whole:?}"
        );

        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn test_blocker3_submodule_decl_resolution_and_broken_wip_siblings() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir =
            std::env::temp_dir().join(format!("decl_blocker3_sub_{}", crate::pack::next_tmp_id()));
        fs::create_dir_all(dir.join("P"))?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            dir.join("lakefile.toml"),
            "name = \"fixture\"\n[[lean_lib]]\nname = \"P\"\n",
        )?;
        fs::write(
            dir.join("P.lean"),
            "import P.Sub\ntheorem root_wip : False := sorry\n",
        )?;
        fs::write(
            dir.join("P/Sub.lean"),
            "theorem early_wip : False := sorry\ntheorem good : True := by trivial\ntheorem broken_later : False := by exact nonexistent_ident_xyz\n",
        )?;
        if !git_commit_all(&dir, "submodule fixture")? {
            fs::remove_dir_all(&dir)?;
            return Ok(());
        }

        let mut store = TurboStore::open(Some(
            &dir.join(format!("store_{}", crate::pack::next_tmp_id())),
        ))?;
        let res = crate::check::evaluate_check_command_value(
            &mut store,
            dir.join("P.lean"),
            Some("good".into()),
            dir.clone(),
        )?;
        assert_eq!(res["decl"], "good");
        assert_eq!(res["status"], "theorem_verified");

        fs::write(
            dir.join("P/Sub.lean"),
            "theorem early_broken_proof : False := by exact no_such_proof_1\ntheorem good : True := by trivial\ntheorem broken_later : False := by exact no_such_proof_2\n",
        )?;
        git_commit_all(&dir, "broken sibling proofs")?;
        let res_direct = crate::check::evaluate_check_command_value(
            &mut store,
            dir.join("P/Sub.lean"),
            Some("good".into()),
            dir.clone(),
        )?;
        assert_eq!(res_direct["decl"], "good");

        fs::write(
            dir.join("P/Leaf.lean"),
            "theorem leaf_good : True := by trivial\n",
        )?;
        git_commit_all(&dir, "add clean leaf")?;
        fs::write(
            dir.join("P/Leaf.lean"),
            "def leaf_helper : Nat := 7\ntheorem leaf_good : True := by trivial\ntheorem leaf_broken : False := by exact no_such_leaf_ident\n",
        )?;
        let res_leaf = crate::check::evaluate_check_command_value(
            &mut store,
            dir.join("P/Leaf.lean"),
            Some("leaf_good".into()),
            dir.clone(),
        )?;
        assert_eq!(res_leaf["decl"], "leaf_good");

        fs::remove_dir_all(dir)?;
        Ok(())
    }
}

#[cfg(test)]
pub(crate) fn compute_fission_store_key(
    toolchain: &str,
    prefix_env_hash: &str,
    sub_shard_key: &str,
) -> String {
    compute_fission_store_key_with_args(toolchain, prefix_env_hash, sub_shard_key, &[])
}

pub(crate) fn compute_fission_store_key_with_args(
    toolchain: &str,
    prefix_env_hash: &str,
    sub_shard_key: &str,
    lean_args: &[String],
) -> String {
    let allowed = splitter::allowed_axioms();
    let mut base = if allowed.len() > splitter::STANDARD_AXIOMS.len() {
        let ax_hash = blake3::hash(allowed.join(",").as_bytes()).to_hex();
        format!(
            "fission-v8:{}:{}:{}:{}:{}:ax:{}",
            crate::zygote::ZYGOTE_SCANNER_VERSION,
            crate::zygote::ZYGOTE_REPLAY_VERSION,
            toolchain,
            prefix_env_hash,
            sub_shard_key,
            &ax_hash.as_str()[..24]
        )
    } else {
        format!(
            "fission-v8:{}:{}:{}:{}:{}",
            crate::zygote::ZYGOTE_SCANNER_VERSION,
            crate::zygote::ZYGOTE_REPLAY_VERSION,
            toolchain,
            prefix_env_hash,
            sub_shard_key
        )
    };
    if let Some(opts_digest) = crate::module_builder::effective_lean_args_digest(lean_args) {
        base.push_str(":opts:");
        base.push_str(&opts_digest);
    }
    base
}

fn subshard_receipt_provenance_ok(store: &TurboStore, blob_hash: &str) -> bool {
    let Some(bytes) = store.read_verified_blob(blob_hash) else {
        return false;
    };
    let Ok(val) = serde_json::from_slice::<serde_json::Value>(&bytes) else {
        return false;
    };
    let version = |field: &str| val[field].as_u64().and_then(|v| u32::try_from(v).ok());
    crate::zygote::verifier_provenance_ok(
        version("scanner_version").unwrap_or(0),
        version("replay_version").unwrap_or(0),
    )
}

#[cfg(test)]
pub(super) fn store_has_provenanced_subshard(store: &TurboStore, key: &str) -> bool {
    store
        .batch_get_theorem_shards_readonly(std::slice::from_ref(&key.to_string()), "trusted")
        .ok()
        .and_then(|m| m.get(key).cloned())
        .is_some_and(|bh| subshard_receipt_provenance_ok(store, &bh))
}

pub(super) fn extract_decl_source_from_file(
    active_src: &str,
    shard: &splitter::TheoremShard,
) -> String {
    let extracted = splitter::extract_shard_orig_decl(active_src, shard);
    if !extracted.is_empty() {
        return extracted;
    }
    if !shard.signature_text.is_empty() && !shard.proof_text.is_empty() {
        return format!("{} := {}", shard.signature_text, shard.proof_text);
    }
    String::new()
}

pub(super) fn target_hygiene_violations(
    split: &splitter::SplitResult,
    shard: &splitter::TheoremShard,
    allow_sorry: bool,
) -> Vec<String> {
    let on_shard_lines = |item: &String| {
        item.strip_prefix('L')
            .and_then(|r| r.split_once(": "))
            .and_then(|(ln, _)| ln.parse::<usize>().ok())
            .is_some_and(|ln| shard.start_line <= ln && ln <= shard.end_line)
    };
    let mut items: Vec<String> = if allow_sorry {
        split.hygiene.disallowed_items_modulo_sorry()
    } else {
        split.hygiene.disallowed_items()
    };
    items.retain(on_shard_lines);
    if items.is_empty() {
        let text = format!("{}\n{}", shard.signature_text, shard.proof_text);
        let fresh = splitter::audit_hygiene(&splitter::strip_lean_comments(&text));
        items = if allow_sorry {
            fresh.disallowed_items_modulo_sorry()
        } else {
            fresh.disallowed_items()
        };
    }
    items
}

pub(super) fn shard_text_contains_sorry_or_admit(shard: &splitter::TheoremShard) -> bool {
    let text = format!("{}\n{}", shard.signature_text, shard.proof_text);
    let rep = splitter::audit_hygiene(&splitter::strip_lean_comments(&text));
    rep.has_sorry
}

#[derive(Clone)]
struct ConeTopSpan<'a> {
    start_line: usize,
    end_line: usize,
    orig_text: &'a str,
    clean_text: &'a str,
}

fn cone_is_letter_like(c: char) -> bool {
    let v = c as u32;
    (0x03b1..=0x03c9).contains(&v)
        || (0x0391..=0x03a9).contains(&v)
        || (0x03ca..=0x03fb).contains(&v)
        || (0x1f00..=0x1ffe).contains(&v)
        || (0x2100..=0x214f).contains(&v)
        || (0x1d400..=0x1d7ff).contains(&v)
        || (0x00c0..=0x00ff).contains(&v) && v != 0x00d7 && v != 0x00f7
        || (0x0100..=0x017f).contains(&v)
}

fn cone_is_subscript_alnum(c: char) -> bool {
    let v = c as u32;
    (0x2080..=0x2089).contains(&v)
        || (0x2090..=0x209c).contains(&v)
        || (0x1d62..=0x1d6a).contains(&v)
        || v == 0x2c7c
}

fn cone_is_id_first(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_' || cone_is_letter_like(c)
}

fn cone_is_id_rest(c: char) -> bool {
    c.is_ascii_alphanumeric()
        || matches!(c, '_' | '\'' | '!' | '?')
        || cone_is_letter_like(c)
        || cone_is_subscript_alnum(c)
}

fn cone_take_leading_ident(s: &str) -> Option<(&str, &str)> {
    let mut pos = 0usize;
    let mut last_valid_end = 0usize;
    while pos < s.len() {
        let seg_end = if let Some(gend) = splitter::scan_lean_guillemet_ident_end(s, pos) {
            gend
        } else {
            let mut chars = s[pos..].char_indices();
            let (_, c0) = chars.next()?;
            if !cone_is_id_first(c0) {
                break;
            }
            let mut end_rel = c0.len_utf8();
            for (rel, ch) in chars {
                if cone_is_id_rest(ch) {
                    end_rel = rel + ch.len_utf8();
                } else {
                    break;
                }
            }
            pos + end_rel
        };
        if seg_end == pos {
            break;
        }
        last_valid_end = seg_end;
        if s.as_bytes().get(seg_end) == Some(&b'.') {
            pos = seg_end + 1;
        } else {
            break;
        }
    }
    (last_valid_end > 0).then(|| (&s[..last_valid_end], &s[last_valid_end..]))
}

fn cone_is_top_level_cmd_start(trimmed: &str) -> bool {
    const STARTERS: &[&str] = &[
        "module",
        "import ",
        "public import ",
        "public section",
        "namespace",
        "section",
        "noncomputable section",
        "meta section",
        "end",
        "open ",
        "variable ",
        "variables ",
        "universe ",
        "universes ",
        "set_option ",
        "attribute ",
        "export ",
        "include ",
        "omit ",
        "@[",
        "private ",
        "protected ",
        "noncomputable ",
        "scoped ",
        "local ",
        "unsafe ",
        "partial ",
        "nonrec ",
        "public ",
        "meta ",
        "theorem ",
        "lemma ",
        "def ",
        "abbrev ",
        "instance ",
        "inductive ",
        "coinductive ",
        "structure ",
        "class ",
        "axiom ",
        "opaque ",
        "constant ",
        "example ",
        "alias ",
        "assert_not_exists ",
        "assert_not_imported",
        "library_note ",
        "add_decl_doc ",
        "grind_pattern ",
        "initialize_simps_projections ",
        "compile_inductive%",
        "declare_aesop_rule_sets",
        "register_simp_attr",
        "simproc",
        "dsimproc",
        "builtin_simproc",
        "builtin_dsimproc",
        "mutual",
        "deriving ",
        "#check",
        "#eval",
        "#print",
        "#guard_msgs",
        "#guard_panic",
        "#guard",
        "#info_trees",
        "#time",
        "#with_exporting",
        "#exit",
        "#where",
        "#version",
        "#recall",
        "#show_deprecated_modules",
        "#import_path",
        "#discr_tree_key",
        "#discr_tree_simp_key",
        "#reduce",
        "#synth",
        "run_cmd",
        "initialize ",
        "builtin_initialize ",
        "syntax ",
        "macro ",
        "macro_rules",
        "elab ",
        "elab_rules",
        "notation ",
        "infix",
        "prefix",
        "postfix",
    ];
    STARTERS.iter().any(|s| trimmed.starts_with(s))
        || matches!(
            trimmed.trim_end(),
            "private"
                | "protected"
                | "noncomputable"
                | "scoped"
                | "local"
                | "unsafe"
                | "partial"
                | "nonrec"
                | "public"
                | "meta"
                | "module"
        )
}

fn cone_starts_command(clean: &str, keyword: &str) -> bool {
    let after = splitter::strip_decl_prefixes(clean);
    after == keyword
        || after
            .strip_prefix(keyword)
            .is_some_and(|rest| rest.starts_with(char::is_whitespace))
}

fn cone_has_unbalanced_delimiters(clean_chunk: &str) -> bool {
    let bytes = clean_chunk.as_bytes();
    let (mut paren, mut bracket, mut brace, mut strict_brace) = (0i32, 0i32, 0i32, 0i32);
    let mut i = 0usize;
    while i < bytes.len() {
        if let Some(end) = splitter::scan_lean_norm_literal_end(clean_chunk, i) {
            i = end;
            continue;
        }
        if bytes[i..].starts_with("⦃".as_bytes()) {
            strict_brace += 1;
            i += "⦃".len();
            continue;
        }
        if bytes[i..].starts_with("⦄".as_bytes()) {
            strict_brace = (strict_brace - 1).max(0);
            i += "⦄".len();
            continue;
        }
        match bytes[i] {
            b'(' => paren += 1,
            b')' => paren = (paren - 1).max(0),
            b'[' => bracket += 1,
            b']' => bracket = (bracket - 1).max(0),
            b'{' => brace += 1,
            b'}' => brace = (brace - 1).max(0),
            _ => {}
        }
        i += 1;
    }
    paren > 0 || bracket > 0 || brace > 0 || strict_brace > 0
}

fn cone_is_incomplete_prefix_only(orig_chunk: &str, clean_chunk: &str) -> bool {
    let trimmed = clean_chunk.trim();
    if trimmed.is_empty() {
        return !orig_chunk.trim_start().starts_with("/-!");
    }
    cone_has_unbalanced_delimiters(trimmed) || splitter::strip_decl_prefixes(trimmed).is_empty()
}

fn cone_segment_commands<'a>(
    src: &'a str,
    clean: &'a str,
    base_line: usize,
    track_scopes: bool,
    max_indent: Option<usize>,
) -> Vec<ConeTopSpan<'a>> {
    if src.is_empty() || src.len() != clean.len() {
        return Vec::new();
    }
    let masked_code = splitter::mask_lean_lexemes(src, true);
    let bytes = src.as_bytes();
    let total_len = bytes.len();
    let mut spans = Vec::new();
    let mut cur_start_line = base_line;
    let mut cur_byte_start = 0usize;
    let mut cur_byte_end = 0usize;
    let mut cur_cmd_indent: Option<usize> = None;
    let mut mutual_depth = 0usize;
    let mut scope_depth = 0usize;
    let mut pos = 0usize;
    let mut line_idx = 0usize;

    while pos < total_len {
        let line_start = pos;
        let mut line_end = pos;
        while line_end < total_len && bytes[line_end] != b'\n' {
            line_end += 1;
        }
        let next_pos = (line_end + 1).min(total_len);
        let line_end_no_cr =
            line_end - usize::from(line_end > line_start && bytes[line_end - 1] == b'\r');
        let line_num = base_line + line_idx;
        let masked_line = &masked_code[line_start..line_end_no_cr];
        let clean_line = &clean[line_start..line_end_no_cr];
        let orig_line = &src[line_start..line_end_no_cr];
        let has_code = !masked_line.trim().is_empty();
        let trimmed_orig = orig_line.trim_start();
        let starts_doc = trimmed_orig.starts_with("/--") || trimmed_orig.starts_with("/-!");

        if !has_code && !starts_doc {
            cur_byte_end = line_end_no_cr;
            pos = next_pos;
            line_idx += 1;
            continue;
        }

        let indent = if has_code {
            masked_line.len() - masked_line.trim_start().len()
        } else {
            orig_line.len() - trimmed_orig.len()
        };
        let trimmed = clean_line.trim_start();
        let at_cmd_indent = match max_indent {
            Some(mi) => indent <= mi,
            None => cur_cmd_indent.is_none_or(|base| indent <= base),
        };

        if track_scopes && mutual_depth > 0 {
            if at_cmd_indent {
                if cone_starts_command(trimmed, "mutual") {
                    mutual_depth += 1;
                } else if cone_starts_command(trimmed, "end") {
                    mutual_depth -= 1;
                }
            }
            cur_byte_end = line_end_no_cr;
            pos = next_pos;
            line_idx += 1;
            continue;
        }

        let prev_orig = &src[cur_byte_start..cur_byte_end];
        let prev_clean = &clean[cur_byte_start..cur_byte_end];
        let prev_trimmed = prev_clean.trim();
        let prev_is_scope_hdr = track_scopes
            && (splitter::is_section_header_line(splitter::strip_decl_prefixes(prev_trimmed))
                || cone_starts_command(prev_trimmed, "namespace")
                || cone_starts_command(prev_trimmed, "end"));
        let can_start = at_cmd_indent || (scope_depth > 0 && prev_is_scope_hdr);

        if line_idx > 0
            && can_start
            && ((starts_doc
                && (indent == 0 || (scope_depth > 0 && at_cmd_indent) || max_indent.is_some()))
                || (!trimmed.is_empty() && cone_is_top_level_cmd_start(trimmed)))
            && !cone_is_incomplete_prefix_only(prev_orig, prev_clean)
        {
            spans.push(ConeTopSpan {
                start_line: cur_start_line,
                end_line: line_num - 1,
                orig_text: prev_orig,
                clean_text: prev_clean,
            });
            cur_start_line = line_num;
            cur_byte_start = line_start;
            cur_cmd_indent = None;
        }

        if !trimmed.is_empty() && cur_cmd_indent.is_none() {
            cur_cmd_indent = Some(indent);
        }

        if track_scopes && can_start {
            if splitter::is_section_header_line(splitter::strip_decl_prefixes(trimmed))
                || cone_starts_command(trimmed, "namespace")
            {
                scope_depth += 1;
            } else if cone_starts_command(trimmed, "end") && scope_depth > 0 {
                scope_depth -= 1;
            } else if cone_starts_command(trimmed, "mutual") {
                mutual_depth = 1;
            }
        }

        cur_byte_end = line_end_no_cr;
        pos = next_pos;
        line_idx += 1;
    }

    let final_end_line = base_line + line_idx.saturating_sub(1);
    if line_idx > 0 && final_end_line >= cur_start_line {
        spans.push(ConeTopSpan {
            start_line: cur_start_line,
            end_line: final_end_line,
            orig_text: &src[cur_byte_start..cur_byte_end],
            clean_text: &clean[cur_byte_start..cur_byte_end],
        });
    }
    spans
}

fn cone_split_mutual_subspans<'a>(
    span: &ConeTopSpan<'a>,
) -> Option<(&'a str, Vec<ConeTopSpan<'a>>, &'a str)> {
    let trimmed_clean = span.clean_text.trim_start();
    if !cone_starts_command(trimmed_clean, "mutual") {
        return None;
    }
    let orig = span.orig_text;
    let clean = span.clean_text;
    if orig.len() != clean.len() {
        return None;
    }
    let first_nl = orig.find('\n')?;
    let trimmed_end_len = clean.trim_end().len();
    if trimmed_end_len <= first_nl {
        return None;
    }
    let last_nl = clean[..trimmed_end_len].rfind('\n')?;
    if last_nl <= first_nl {
        return None;
    }
    let last_line_clean = clean[last_nl + 1..trimmed_end_len].trim();
    if !cone_starts_command(last_line_clean, "end") {
        return None;
    }
    let header_orig = &orig[..first_nl];
    let footer_orig = &orig[last_nl + 1..];
    let body_orig = &orig[first_nl + 1..last_nl];
    let body_clean = &clean[first_nl + 1..last_nl];
    if body_clean.trim().is_empty() {
        return None;
    }
    let min_indent = body_orig
        .lines()
        .zip(body_clean.lines())
        .filter(|(_, lc)| cone_is_top_level_cmd_start(lc.trim_start()))
        .map(|(lo, lc)| {
            lo.bytes()
                .take_while(|&b| b == b' ' || b == b'\t')
                .count()
                .min(lc.len() - lc.trim_start().len())
        })
        .min()?;
    let inner = cone_segment_commands(
        body_orig,
        body_clean,
        span.start_line + 1,
        false,
        Some(min_indent),
    );
    if inner.is_empty() {
        return None;
    }
    Some((header_orig, inner, footer_orig))
}

fn cone_unwrap_parens(mut text: &str) -> &str {
    text = text.trim();
    while let Some(inner) = text.strip_prefix('(') {
        let Some((body, tail)) = cone_split_top_level(inner, &[")"]) else {
            break;
        };
        if !tail.trim().is_empty() {
            break;
        }
        text = body.trim();
    }
    text
}

fn cone_application_parts(result: &str) -> Vec<(usize, usize)> {
    let mut start = 0;
    let mut depth = 0usize;
    let mut parts = Vec::new();
    for (offset, ch) in result.char_indices() {
        match ch {
            '(' | '[' | '{' | '⦃' => depth += 1,
            ')' | ']' | '}' | '⦄' => depth = depth.saturating_sub(1),
            _ => {}
        }
        if depth == 0 && ch.is_whitespace() {
            if start < offset {
                parts.push((start, offset));
            }
            start = offset + ch.len_utf8();
        }
    }
    if start < result.len() {
        parts.push((start, result.len()));
    }
    parts
}

fn cone_match_trigger(mut result: &str, simp: bool, instance: bool, head_only: bool) -> &str {
    loop {
        result = cone_unwrap_parens(result);
        if result.starts_with('∀')
            || cone_take_leading_ident(result).is_some_and(|(id, _)| id == "forall")
        {
            if let Some((_, tail)) = cone_split_top_level(result, &[","]) {
                result = tail;
                continue;
            }
        }
        if let Some((_, tail)) = cone_split_top_level(result, &["→", "->"]) {
            result = tail;
            continue;
        }
        break;
    }
    if simp {
        if cone_split_top_level(result, &["∧", "/\\"]).is_some() {
            return "";
        }
        if let Some((lhs, _)) = cone_split_top_level(result, &["=", "↔"]) {
            return lhs;
        }
    }
    if instance {
        let parts = cone_application_parts(result);
        if let Some(&(start, end)) = parts.first() {
            let head = &result[start..end];
            let head_base = head.strip_prefix("_root_.").unwrap_or(head);
            let head_base = head_base
                .split_once(".{")
                .map(|(b, _)| b)
                .unwrap_or(head_base);
            if head_only
                || matches!(
                    head_base,
                    "MonadStateOf"
                        | "MonadReaderOf"
                        | "MonadWithReaderOf"
                        | "MonadExceptOf"
                        | "MonadError"
                        | "MonadControl"
                        | "MonadControlT"
                        | "MonadLift"
                        | "MonadLiftT"
                        | "MonadFunctor"
                        | "MonadFunctorT"
                        | "Membership"
                        | "GetElem"
                        | "GetElem?"
                        | "Coe"
                        | "CoeTC"
                        | "CoeHead"
                        | "CoeFun"
                        | "CoeSort"
                        | "CoeOut"
                        | "CoeDep"
                        | "CoeTail"
                        | "CoeHTCT"
                        | "HasSubset"
                        | "HasSSubset"
                        | "HAdd"
                        | "HSub"
                        | "HMul"
                        | "HDiv"
                        | "HMod"
                        | "HPow"
                        | "HAppend"
                        | "HAnd"
                        | "HOr"
                        | "HXor"
                        | "HShiftLeft"
                        | "HShiftRight"
                )
            {
                return head.split_once(".{").map(|(b, _)| b).unwrap_or(head);
            }
        }
        if parts.len() >= 3 {
            return &result[..parts[1].1];
        }
    }
    result
}

fn cone_parameterized_alias(
    text: &str,
    kw: &str,
    name: &str,
    result: &str,
    has_type: bool,
) -> bool {
    let rest = splitter::strip_decl_prefixes(text);
    let after = rest.strip_prefix(kw).unwrap_or(rest).trim_start();
    let mut after = after.strip_prefix(name).unwrap_or("").trim_start();
    if let Some(universes) = after.strip_prefix(".{") {
        after = cone_split_top_level(universes, &["}"])
            .map(|(_, tail)| tail.trim_start())
            .unwrap_or("");
    }
    after.starts_with(['(', '[', '{', '⦃'])
        || (has_type && cone_split_top_level(result, &["→", "->"]).is_some())
        || cone_split_top_level(rest, &[":="]).is_some_and(|(_, body)| {
            let body = cone_unwrap_parens(body);
            body.starts_with(['λ', '∀'])
                || cone_take_leading_ident(body).is_some_and(|(id, _)| id == "fun")
        })
}

fn cone_classify_decl(clean_cmd: &str) -> Option<(&'static str, String)> {
    const KWS: &[&str] = &[
        "theorem",
        "lemma",
        "def",
        "abbrev",
        "structure",
        "class",
        "inductive",
        "coinductive",
        "instance",
        "axiom",
        "opaque",
        "constant",
        "example",
        "simproc_decl",
        "dsimproc_decl",
        "simproc",
        "dsimproc",
        "builtin_simproc",
        "builtin_dsimproc",
        "initialize",
        "builtin_initialize",
        "deriving",
    ];
    let rest = splitter::strip_decl_prefixes(clean_cmd);
    for &kw in KWS {
        if let Some(mut after) = rest.strip_prefix(kw) {
            if after.is_empty() || after.starts_with(char::is_whitespace) || after.starts_with('[')
            {
                after = after.trim_start();
                if kw == "instance" && after.starts_with('(') {
                    if let Some((group, tail)) = cone_split_top_level(&after[1..], &[")"]) {
                        if group
                            .trim_start()
                            .strip_prefix("priority")
                            .is_some_and(|rest| {
                                rest.starts_with(char::is_whitespace) || rest.starts_with(":=")
                            })
                        {
                            after = tail.trim_start();
                        }
                    }
                }
                let anonymous_instance = kw == "instance"
                    && (after.starts_with(['[', '(', '{', '⦃'])
                        || after.starts_with("#[")
                        || after.starts_with("where"));
                if after.starts_with('[') {
                    if let Some(close_idx) = after.find(']') {
                        after = after[close_idx + 1..].trim_start();
                    }
                }
                let name = if matches!(kw, "example" | "deriving")
                    || anonymous_instance
                    || (matches!(kw, "initialize" | "builtin_initialize") && !after.contains(':'))
                {
                    String::new()
                } else {
                    cone_take_leading_ident(after)
                        .map(|(n, _)| n.to_string())
                        .unwrap_or_default()
                };
                return Some((kw, name));
            }
        }
    }
    None
}

fn cone_extract_ident_tokens(clean_text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    let mut pending = vec![clean_text];
    while let Some(text) = pending.pop() {
        let bytes = text.as_bytes();
        let mut i = 0usize;
        while i < bytes.len() {
            if let Some(end) = splitter::scan_lean_interpolated_string_end(text, i) {
                let mut j = i + 1;
                while j < end {
                    match bytes[j] {
                        b'\\' => {
                            j += 1;
                            if j < end {
                                j += text[j..].chars().next().unwrap().len_utf8();
                            }
                        }
                        b'{' => {
                            let start = j + 1;
                            j = start;
                            let mut depth = 1usize;
                            while j < end && depth > 0 {
                                if let Some(span) = splitter::skip_lean_lexeme(text, j) {
                                    j = span.end;
                                    continue;
                                }
                                match bytes[j] {
                                    b'{' => depth += 1,
                                    b'}' => depth -= 1,
                                    _ => {}
                                }
                                if depth > 0 {
                                    j += text[j..].chars().next().unwrap().len_utf8();
                                }
                            }
                            pending.push(&text[start..j]);
                            j = (j + 1).min(end);
                        }
                        _ => j += text[j..].chars().next().unwrap().len_utf8(),
                    }
                }
                i = end;
                continue;
            }
            if let Some(span) = splitter::skip_lean_lexeme(text, i) {
                if span.is_comment || span.is_literal {
                    i = span.end;
                    continue;
                }
            }
            if bytes[i..].starts_with(b".{") {
                i += 2;
                let mut depth = 1usize;
                while i < bytes.len() && depth > 0 {
                    if let Some(span) = splitter::skip_lean_lexeme(text, i) {
                        if span.is_comment || span.is_literal {
                            i = span.end;
                            continue;
                        }
                    }
                    match bytes[i] {
                        b'{' => depth += 1,
                        b'}' => depth -= 1,
                        _ => {}
                    }
                    i += text[i..].chars().next().unwrap().len_utf8();
                }
                continue;
            }
            if let Some((qual_tok, _)) = cone_take_leading_ident(&text[i..]) {
                let mut name = qual_tok;
                loop {
                    let canon = splitter::canonicalize_lean_name(name);
                    if !canon.is_empty() && seen.insert(canon.clone()) {
                        out.push(canon);
                    }
                    let Some((prefix, _)) = name.rsplit_once('.') else {
                        break;
                    };
                    if prefix.contains('«') && !prefix.contains('»') {
                        break;
                    }
                    name = prefix;
                }
                i += qual_tok.len();
                continue;
            }
            i += text[i..].chars().next().unwrap().len_utf8();
        }
    }
    out
}

fn cone_split_top_level<'a>(text: &'a str, separators: &[&str]) -> Option<(&'a str, &'a str)> {
    let mut depth = 0usize;
    let mut at = 0;
    while at < text.len() {
        if let Some(span) = splitter::skip_lean_lexeme(text, at) {
            at = span.end;
            continue;
        }
        let tail = &text[at..];
        if depth == 0 {
            if let Some(separator) = separators.iter().find(|&&separator| {
                tail.starts_with(separator)
                    && (separator != ":" || !tail.starts_with(":="))
                    && (separator != "="
                        || (!tail.starts_with("==")
                            && !tail.starts_with("=>")
                            && !text[..at].ends_with([':', '=', '!', '<', '>'])))
                    && (separator != "where"
                        || cone_take_leading_ident(tail).is_some_and(|(name, _)| name == "where"))
            }) {
                return Some((&text[..at], &text[at + separator.len()..]));
            }
        }
        if let Some((name, _)) = cone_take_leading_ident(tail) {
            at += name.len();
            continue;
        }
        let ch = tail.chars().next().unwrap();
        match ch {
            '(' | '[' | '{' | '⦃' => depth += 1,
            ')' | ']' | '}' | '⦄' => depth = depth.saturating_sub(1),
            _ => {}
        }
        at += ch.len_utf8();
    }
    None
}

fn cone_command_header(text: &str) -> &str {
    cone_split_top_level(text, &[":=", "=>", "where", "|"])
        .map(|(header, _)| header)
        .unwrap_or(text)
}

fn cone_dependency_tokens(text: &str) -> Vec<String> {
    let masked = splitter::mask_lean_lexemes(text, true);
    let mut tokens = Vec::new();
    let mut pos = 0;
    let mut depth = 0usize;
    while pos < masked.len() {
        let tail = &masked[pos..];
        let token = if let Some((name, _)) = cone_take_leading_ident(tail) {
            name
        } else if tail.starts_with(":=") || tail.starts_with("=>") {
            &tail[..2]
        } else {
            &tail[..tail.chars().next().unwrap().len_utf8()]
        };
        if !token.trim().is_empty() {
            tokens.push((token, pos, pos + token.len(), depth));
        }
        match token {
            "(" | "[" | "{" | "⦃" => depth += 1,
            ")" | "]" | "}" | "⦄" => depth = depth.saturating_sub(1),
            _ => {}
        }
        pos += token.len();
    }
    let mut bindings: Vec<(&str, usize, usize, usize)> = Vec::new();
    let scope_end = |start: usize, depth: usize| {
        tokens
            .iter()
            .skip(start)
            .find(|(t, _, _, d)| *d <= depth && matches!(*t, ")" | "]" | "}" | "⦄" | ";"))
            .map(|t| t.1)
            .unwrap_or(text.len())
    };
    let signature_end = tokens
        .iter()
        .find(|t| t.3 == 0 && matches!(t.0, ":" | ":="))
        .map(|t| t.1)
        .unwrap_or(0);
    for (idx, &(token, start, _, d)) in tokens.iter().enumerate() {
        if matches!(token, "(" | "[" | "{" | "⦃") && d == 0 && start < signature_end {
            let Some(colon) = tokens
                .iter()
                .enumerate()
                .skip(idx + 1)
                .find(|(_, t)| t.3 <= d || t.0 == ":")
                .map(|(i, _)| i)
            else {
                continue;
            };
            if tokens[colon].0 != ":" {
                continue;
            }
            let Some(close) = tokens
                .iter()
                .enumerate()
                .skip(colon + 1)
                .find(|(_, t)| t.3 == d + 1 && matches!(t.0, ")" | "]" | "}" | "⦄"))
                .map(|(i, _)| i)
            else {
                continue;
            };
            for &(name, at, _, _) in &tokens[idx + 1..colon] {
                if cone_take_leading_ident(name).is_some_and(|(n, r)| n == name && r.is_empty()) {
                    bindings.push((name, at, tokens[close].2, text.len()));
                }
            }
        }
        if token == "fun" {
            let mut end = idx + 1;
            while end < tokens.len()
                && cone_take_leading_ident(tokens[end].0)
                    .is_some_and(|(n, r)| n == tokens[end].0 && r.is_empty())
            {
                end += 1;
            }
            if tokens.get(end).is_some_and(|t| t.0 == "=>") {
                let limit = scope_end(end + 1, d).min(
                    text[tokens[end].2..]
                        .find('\n')
                        .map(|n| tokens[end].2 + n)
                        .unwrap_or(text.len()),
                );
                for &(name, at, _, _) in &tokens[idx + 1..end] {
                    bindings.push((name, at, tokens[end].2, limit));
                }
            }
        }
        if matches!(token, "let" | "have") {
            let Some(&(name, at, _, _)) = tokens.get(idx + 1) else {
                continue;
            };
            if !cone_take_leading_ident(name).is_some_and(|(n, r)| n == name && r.is_empty()) {
                continue;
            }
            let Some(assign) = tokens
                .iter()
                .enumerate()
                .skip(idx + 2)
                .find(|(_, t)| t.3 <= d && matches!(t.0, ":=" | ";" | ")" | "]" | "}" | "⦄"))
                .filter(|(_, t)| t.0 == ":=")
                .map(|(i, _)| i)
            else {
                continue;
            };
            let rhs = tokens[assign].2;
            let semicolon = (tokens.get(assign + 1).is_none_or(|t| t.0 != "by"))
                .then(|| scope_end(assign + 1, d))
                .filter(|&end| text.as_bytes().get(end) == Some(&b';'));
            let column = start - text[..start].rfind('\n').map(|n| n + 1).unwrap_or(0);
            let newline = text[rhs..].match_indices('\n').find_map(|(offset, _)| {
                let after = rhs + offset + 1;
                let tail = &text[after..];
                let indent = tail.len() - tail.trim_start_matches([' ', '\t']).len();
                (!tail.trim().is_empty() && indent <= column).then_some(after)
            });
            if let Some(boundary) = semicolon.into_iter().chain(newline).min() {
                let limit = tokens
                    .iter()
                    .skip(assign + 1)
                    .find(|t| t.3 <= d && matches!(t.0, ")" | "]" | "}" | "⦄"))
                    .map(|t| t.1)
                    .unwrap_or(text.len())
                    .min(
                        text[boundary..]
                            .find('\n')
                            .map(|n| boundary + n)
                            .unwrap_or(text.len()),
                    );
                bindings.push((name, at, boundary, limit));
            }
        }
    }
    let mut filtered = text.as_bytes().to_vec();
    for (token, start, end, _) in tokens {
        if bindings.iter().any(|&(name, declaration, scope, limit)| {
            token == name && (start == declaration || (start >= scope && start < limit))
        }) {
            filtered[start..end].fill(b' ');
        }
    }
    cone_extract_ident_tokens(std::str::from_utf8(&filtered).unwrap())
}

fn cone_extract_inductive_ctors(clean_text: &str) -> Vec<String> {
    let mut ctors = Vec::new();
    for line in clean_text.lines().skip(1) {
        let trimmed = line.trim_start();
        if let Some(rest) = trimmed.strip_prefix('|') {
            if let Some((name, _)) = cone_take_leading_ident(rest.trim_start()) {
                ctors.push(splitter::canonicalize_lean_name(name));
            }
        }
    }
    ctors
}

fn recover_decl_source(src: String, file: &Path) -> Result<String> {
    if src.is_empty() || fs::metadata(file)?.len() > src.len() as u64 {
        return fs::read_to_string(file)
            .with_context(|| format!("Read declaration source {}", file.display()));
    }
    Ok(src)
}

pub(super) fn audited_cone_source(src: &str, shard: &splitter::TheoremShard) -> Result<String> {
    anyhow::ensure!(
        !splitter::audit_hygiene(&splitter::strip_lean_comments(src)).has_checking_weakening,
        "Soundness hygiene violation: checking weakening in declaration source"
    );
    let cone = build_cone_scoped_decl_audit_source(src, shard);
    let hygiene = splitter::audit_hygiene(&splitter::strip_lean_comments(&cone));
    anyhow::ensure!(
        hygiene.is_clean_or_deferred_to_kernel_gate(),
        "Soundness hygiene violation in declaration cone: {}",
        hygiene.disallowed_items().join(", ")
    );
    Ok(cone)
}

fn build_cone_scoped_decl_audit_source(src: &str, shard: &splitter::TheoremShard) -> String {
    let clean = splitter::strip_lean_comments(src);
    if clean.len() != src.len() {
        return src.to_string();
    }
    let mut normalized = String::with_capacity(clean.len());
    for (original, stripped) in src.split_inclusive('\n').zip(clean.split_inclusive('\n')) {
        let indent = original.len() - original.trim_start().len();
        let code_start = stripped.len() - stripped.trim_start().len();
        if !stripped.trim().is_empty() && code_start > indent {
            normalized.push_str(&stripped[..indent]);
            normalized.push_str(&stripped[code_start..]);
        } else {
            normalized.push_str(stripped);
        }
    }
    let spans = cone_segment_commands(&normalized, &normalized, 1, true, None);
    if spans.is_empty() {
        return src.to_string();
    }

    struct DeclNode {
        top_idx: usize,
        sub_idx: Option<usize>,
        implicit_dependency: bool,
        triggers: Vec<String>,
        transparent_alias: bool,
        rhs_deps: Vec<String>,
        parameterized_alias: bool,
        result_type: String,
        result_type_deps: Vec<String>,
        simp: bool,
        instance: bool,
        default_instance: bool,
        out_param_class: bool,
        has_out_param: bool,
        class_attr: bool,
        has_explicit_type: bool,
        attachment: bool,
        runtime_attachment: bool,
        prefixes: Vec<String>,
        names: Vec<String>,
        deps: Vec<String>,
    }

    let mut nodes: Vec<DeclNode> = Vec::new();
    let mut mutual_map: HashMap<usize, (&str, Vec<ConeTopSpan<'_>>, &str)> = HashMap::new();
    let mut scope_stack: Vec<splitter::ScopeFrame> = Vec::new();
    let mut opens: Vec<(usize, String)> = Vec::new();
    let mut target_node_idx: Option<usize> = None;
    let mut target_top_idx: Option<usize> = None;

    let register_decl_span = |sub_span: &ConeTopSpan<'_>,
                              top_idx: usize,
                              sub_idx: Option<usize>,
                              stack: &[splitter::ScopeFrame],
                              opens: &[(usize, String)],
                              nodes: &mut Vec<DeclNode>,
                              target_node_idx: &mut Option<usize>,
                              target_top_idx: &mut Option<usize>| {
        let attachment =
            splitter::strip_decl_prefixes(sub_span.clean_text).starts_with("attribute ");
        let Some((kw, raw_name)) = cone_classify_decl(sub_span.clean_text)
            .or_else(|| attachment.then(|| ("attribute", String::new())))
            .or_else(|| {
                [
                    "macro_rules",
                    "macro",
                    "syntax",
                    "notation",
                    "elab",
                    "elab_rules",
                    "infix",
                    "infixl",
                    "infixr",
                    "prefix",
                    "postfix",
                ]
                .into_iter()
                .find(|kw| cone_starts_command(sub_span.clean_text, kw))
                .map(|kw| (kw, String::new()))
            })
        else {
            return;
        };
        let qual_name = if raw_name.is_empty() {
            String::new()
        } else {
            splitter::qualified_decl_name(&raw_name, stack)
        };
        let is_target = sub_span.start_line <= shard.end_line
            && sub_span.end_line >= shard.start_line
            && (qual_name == shard.qualified_name
                || splitter::canonicalize_lean_name(&raw_name) == shard.name
                || splitter::decl_name_matches_target(&qual_name, &shard.rooted_name()));
        let mut names = Vec::new();
        if !qual_name.is_empty() {
            names.push(qual_name.clone());
        }
        if matches!(kw, "inductive" | "coinductive") {
            for ctor in cone_extract_inductive_ctors(sub_span.clean_text) {
                if !qual_name.is_empty() {
                    let qctor = format!("{qual_name}.{ctor}");
                    if !names.contains(&qctor) {
                        names.push(qctor);
                    }
                }
            }
        }
        let tokens = cone_dependency_tokens(sub_span.clean_text);
        let header = if attachment {
            sub_span
                .clean_text
                .split_once(']')
                .map(|(header, _)| header)
                .unwrap_or("")
        } else {
            let rest = splitter::strip_decl_prefixes(sub_span.clean_text);
            &sub_span.clean_text[..sub_span.clean_text.len() - rest.len()]
        };
        let attributes = cone_extract_ident_tokens(header);
        let transparent_alias = kw == "abbrev"
            || attributes
                .iter()
                .any(|t| matches!(t.as_str(), "reducible" | "abbrev"));
        let rhs_deps = cone_split_top_level(sub_span.clean_text, &[":="])
            .map(|(_, body)| {
                cone_extract_ident_tokens(body)
                    .into_iter()
                    .filter(|token| tokens.contains(token))
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        let has_synthesis_attribute = attributes.iter().any(|t| {
            matches!(
                t.as_str(),
                "simp"
                    | "ext"
                    | "coe"
                    | "instance"
                    | "deriving"
                    | "elab_as_elim"
                    | "norm_cast"
                    | "aesop"
                    | "default_instance"
                    | "csimp"
                    | "implemented_by"
                    | "init"
                    | "builtin_init"
                    | "norm_num"
                    | "fun_prop"
                    | "positivity"
                    | "app_unexpander"
                    | "delab"
                    | "elab"
                    | "macro"
            )
        });
        let runtime_attachment = attributes
            .iter()
            .any(|t| matches!(t.as_str(), "implemented_by" | "csimp"));
        let implicit_dependency = kw != "example"
            && (matches!(
                kw,
                "instance"
                    | "deriving"
                    | "initialize"
                    | "builtin_initialize"
                    | "macro_rules"
                    | "macro"
                    | "syntax"
                    | "notation"
                    | "elab"
                    | "elab_rules"
                    | "infix"
                    | "infixl"
                    | "infixr"
                    | "prefix"
                    | "postfix"
            ) || has_synthesis_attribute);
        let signature = cone_command_header(splitter::strip_decl_prefixes(sub_span.clean_text));
        let explicit_type = cone_split_top_level(signature, &[":"]);
        let has_explicit_type = explicit_type.is_some();
        let result_type = explicit_type.map(|(_, result)| result).unwrap_or("");
        let simp = attributes
            .iter()
            .any(|t| matches!(t.as_str(), "simp" | "csimp"));
        let default_instance = attributes.iter().any(|t| t == "default_instance");
        let has_out_param = cone_extract_ident_tokens(signature)
            .iter()
            .any(|t| matches!(t.as_str(), "outParam" | "semiOutParam"));
        let class_attr = attributes.iter().any(|t| t == "class");
        let out_param_class = (kw == "class" || class_attr) && has_out_param;
        let instance = kw == "instance"
            || attributes
                .iter()
                .any(|t| matches!(t.as_str(), "instance" | "default_instance"));
        let result_type_deps = cone_extract_ident_tokens(result_type)
            .into_iter()
            .filter(|token| tokens.contains(token))
            .collect::<Vec<_>>();
        let parameterized_alias = !raw_name.is_empty()
            && cone_parameterized_alias(
                sub_span.clean_text,
                kw,
                &raw_name,
                result_type,
                has_explicit_type,
            );
        let mut triggers = cone_extract_ident_tokens(if attachment {
            sub_span
                .clean_text
                .split_once(']')
                .map(|(_, tail)| tail)
                .unwrap_or("")
        } else if has_explicit_type {
            cone_match_trigger(result_type, simp, instance, default_instance)
        } else {
            ""
        })
        .into_iter()
        .filter(|token| tokens.contains(token))
        .collect::<Vec<_>>();
        triggers.retain(|t| {
            t != kw
                && t != &splitter::canonicalize_lean_name(&raw_name)
                && !matches!(
                    t.as_str(),
                    "priority" | "where" | "term" | "command" | "tactic" | "max"
                )
        });
        let namespace = splitter::qualified_decl_name("", stack);
        let mut prefixes = Vec::new();
        let mut prefix = namespace.as_str();
        while !prefix.is_empty() {
            prefixes.push(format!("{prefix}."));
            prefix = prefix.rsplit_once('.').map(|(p, _)| p).unwrap_or("");
        }
        prefixes.push(String::new());
        prefixes.extend(opens.iter().rev().map(|(_, name)| format!("{name}.")));
        let idx = nodes.len();
        if is_target {
            *target_node_idx = Some(idx);
            *target_top_idx = Some(top_idx);
        }
        nodes.push(DeclNode {
            top_idx,
            sub_idx,
            implicit_dependency,
            triggers,
            transparent_alias,
            rhs_deps,
            parameterized_alias,
            result_type: result_type.to_string(),
            result_type_deps,
            simp,
            instance,
            default_instance,
            out_param_class,
            has_out_param,
            class_attr,
            has_explicit_type,
            attachment,
            runtime_attachment,
            prefixes,
            names,
            deps: tokens,
        });
    };

    for (top_idx, span) in spans.iter().enumerate() {
        if let Some((hdr, inner, ftr)) = cone_split_mutual_subspans(span) {
            for (s_idx, sub) in inner.iter().enumerate() {
                register_decl_span(
                    sub,
                    top_idx,
                    Some(s_idx),
                    &scope_stack,
                    &opens,
                    &mut nodes,
                    &mut target_node_idx,
                    &mut target_top_idx,
                );
            }
            mutual_map.insert(top_idx, (hdr, inner, ftr));
        } else {
            register_decl_span(
                span,
                top_idx,
                None,
                &scope_stack,
                &opens,
                &mut nodes,
                &mut target_node_idx,
                &mut target_top_idx,
            );
            splitter::update_scope_stack_with_idx(&mut scope_stack, span.orig_text, top_idx);
            opens.retain(|(depth, _)| *depth <= scope_stack.len());
            if let Some(rest) = span.clean_text.trim_start().strip_prefix("open ") {
                if !rest.starts_with("scoped ") {
                    for name in rest.split_whitespace().take_while(|s| *s != "in") {
                        if cone_take_leading_ident(name)
                            .is_some_and(|(n, r)| n == name && r.is_empty())
                        {
                            let namespace = splitter::qualified_decl_name("", &scope_stack);
                            let mut prefix = namespace.as_str();
                            let resolved = loop {
                                let candidate = if prefix.is_empty() {
                                    splitter::canonicalize_lean_name(name)
                                } else {
                                    format!("{prefix}.{}", splitter::canonicalize_lean_name(name))
                                };
                                if prefix.is_empty()
                                    || nodes.iter().any(|node| {
                                        node.names
                                            .iter()
                                            .any(|n| n.starts_with(&format!("{candidate}.")))
                                    })
                                {
                                    break candidate;
                                }
                                prefix = prefix.rsplit_once('.').map(|(p, _)| p).unwrap_or("");
                            };
                            opens.push((scope_stack.len(), resolved));
                        }
                    }
                }
            }
        }
    }

    let Some(t_node_idx) = target_node_idx else {
        return src.to_string();
    };
    let max_top_idx = target_top_idx.unwrap_or(spans.len() - 1);

    let mut name_to_nodes: HashMap<String, Vec<usize>> = HashMap::new();
    for (idx, node) in nodes.iter().enumerate() {
        for nm in &node.names {
            name_to_nodes.entry(nm.clone()).or_default().push(idx);
        }
    }
    let resolve = |node: &DeclNode, dep: &str| -> Vec<usize> {
        let rooted = dep.strip_prefix("_root_.");
        let mut opened = Vec::new();
        let mut in_opens = false;
        for prefix in &node.prefixes {
            let key = rooted
                .map(str::to_owned)
                .unwrap_or_else(|| format!("{prefix}{dep}"));
            if let Some(indices) = name_to_nodes.get(&key) {
                let candidates: Vec<_> = indices
                    .iter()
                    .copied()
                    .filter(|&i| nodes[i].top_idx <= node.top_idx)
                    .collect();
                if !candidates.is_empty() {
                    if !in_opens {
                        return candidates;
                    }
                    opened.extend(candidates);
                }
            }
            if rooted.is_some() {
                break;
            }
            in_opens |= prefix.is_empty();
        }
        opened
    };
    let mut out_param_classes: Vec<_> = nodes.iter().map(|node| node.out_param_class).collect();
    let mut transparent_aliases: Vec<_> = nodes.iter().map(|node| node.transparent_alias).collect();
    for node in &nodes {
        if node.attachment && node.top_idx <= max_top_idx {
            for idx in node.triggers.iter().flat_map(|t| resolve(node, t)) {
                transparent_aliases[idx] |= node.transparent_alias && node.names.is_empty();
                out_param_classes[idx] |= node.class_attr && nodes[idx].has_out_param;
            }
        }
    }
    let trigger_references = |source: &DeclNode, policy: &DeclNode| -> Vec<usize> {
        if !source.has_explicit_type {
            return Vec::new();
        }
        let conclusion = cone_match_trigger(&source.result_type, false, false, false);
        let parts = cone_application_parts(conclusion);
        let local_out_param = parts.first().is_some_and(|&(start, end)| {
            let head_raw = &conclusion[start..end];
            let head_base = head_raw
                .split_once(".{")
                .map(|(b, _)| b)
                .unwrap_or(head_raw);
            resolve(source, head_base)
                .iter()
                .any(|&i| out_param_classes[i])
        });
        let trigger = cone_match_trigger(
            &source.result_type,
            policy.simp,
            policy.instance,
            policy.default_instance || local_out_param,
        );
        cone_extract_ident_tokens(trigger)
            .iter()
            .filter(|t| source.result_type_deps.contains(t))
            .flat_map(|t| resolve(source, t))
            .collect()
    };
    let expand_aliases = |references: Vec<usize>| {
        let erasing: Vec<_> = references
            .iter()
            .copied()
            .filter(|&i| transparent_aliases[i] && nodes[i].parameterized_alias)
            .collect();
        let mut pending = if erasing.is_empty() {
            references
        } else {
            erasing
        };
        let mut seen = vec![false; nodes.len()];
        let mut expanded = Vec::new();
        while let Some(idx) = pending.pop() {
            if seen[idx] {
                continue;
            }
            seen[idx] = true;
            if transparent_aliases[idx] {
                let rhs: Vec<_> = nodes[idx]
                    .rhs_deps
                    .iter()
                    .flat_map(|t| resolve(&nodes[idx], t))
                    .collect();
                let erasing: Vec<_> = rhs
                    .iter()
                    .copied()
                    .filter(|&i| transparent_aliases[i] && nodes[i].parameterized_alias)
                    .collect();
                pending.extend(if erasing.is_empty() { rhs } else { erasing });
            } else {
                expanded.push(idx);
            }
        }
        expanded
    };
    let dependencies: Vec<Vec<usize>> = nodes
        .iter()
        .map(|node| {
            node.deps
                .iter()
                .flat_map(|dep| resolve(node, dep))
                .collect()
        })
        .collect();
    let closure = |seeds: Vec<usize>| {
        let mut seen = vec![false; nodes.len()];
        let mut pending = seeds;
        while let Some(idx) = pending.pop() {
            if !seen[idx] {
                seen[idx] = true;
                pending.extend(dependencies[idx].iter().copied());
            }
        }
        seen
    };
    let mut relevant = closure(vec![t_node_idx]);
    loop {
        let mut additions = Vec::new();
        for (idx, node) in nodes.iter().enumerate() {
            if relevant[idx] || !node.implicit_dependency || node.top_idx > max_top_idx {
                continue;
            }
            let matches_relevant = if node.attachment {
                node.triggers.is_empty()
                    || node.triggers.iter().any(|t| {
                        let resolved = resolve(node, t);
                        resolved.is_empty()
                            || resolved.into_iter().any(|i| {
                                expand_aliases(trigger_references(&nodes[i], node))
                                    .iter()
                                    .all(|&r| relevant[r])
                            })
                    })
            } else {
                let references = if node.instance {
                    trigger_references(node, node)
                } else if !node.has_explicit_type {
                    Vec::new()
                } else {
                    node.triggers
                        .iter()
                        .flat_map(|t| resolve(node, t))
                        .collect()
                };
                expand_aliases(references).iter().all(|&i| relevant[i])
            };
            if matches_relevant {
                additions.push(idx);
            }
        }
        if additions.is_empty() {
            break;
        }
        for (idx, seen) in closure(additions).into_iter().enumerate() {
            relevant[idx] |= seen;
        }
    }
    let mut needed = relevant;
    loop {
        let attachments: Vec<_> = nodes
            .iter()
            .enumerate()
            .filter(|(idx, node)| {
                node.top_idx <= max_top_idx
                    && (node.attachment || node.runtime_attachment)
                    && !needed[*idx]
                    && (dependencies[*idx].iter().any(|&i| needed[i])
                        || (node.runtime_attachment
                            && closure(vec![*idx])
                                .iter()
                                .enumerate()
                                .any(|(i, &seen)| seen && needed[i])))
            })
            .map(|(idx, _)| idx)
            .collect();
        if attachments.is_empty() {
            break;
        }
        for (idx, seen) in closure(attachments).into_iter().enumerate() {
            needed[idx] |= seen;
        }
    }
    for (idx, node) in nodes.iter().enumerate() {
        if node.top_idx > max_top_idx
            && node
                .deps
                .iter()
                .any(|s| matches!(s.as_str(), "implemented_by" | "csimp"))
        {
            let reachable = closure(vec![idx]);
            if reachable
                .iter()
                .enumerate()
                .any(|(i, &seen)| seen && needed[i])
            {
                return src.to_string();
            }
        }
    }

    let mut single_decl_by_top: HashMap<usize, usize> = HashMap::new();
    let mut mutual_decls_by_top: HashMap<usize, HashMap<usize, usize>> = HashMap::new();
    for (n_idx, node) in nodes.iter().enumerate() {
        if let Some(s_idx) = node.sub_idx {
            mutual_decls_by_top
                .entry(node.top_idx)
                .or_default()
                .insert(s_idx, n_idx);
        } else {
            single_decl_by_top.insert(node.top_idx, n_idx);
        }
    }

    let mut out = String::with_capacity(src.len());
    let mut open_scopes: Vec<splitter::ScopeFrame> = Vec::new();
    let mut prev_end_line: Option<usize> = None;

    for (top_idx, span) in spans[..=max_top_idx].iter().enumerate() {
        if let Some((hdr, inner, ftr)) = mutual_map.get(&top_idx) {
            let sub_map = mutual_decls_by_top.get(&top_idx);
            let mut kept_subs: Vec<&ConeTopSpan<'_>> = Vec::new();
            for (s_idx, sub) in inner.iter().enumerate() {
                let keep_sub = match sub_map.and_then(|m| m.get(&s_idx)) {
                    Some(&n_idx) => needed[n_idx],
                    None => !splitter::audit_hygiene(sub.clean_text).has_sorry,
                };
                if keep_sub {
                    kept_subs.push(sub);
                }
            }
            if kept_subs.is_empty() {
                continue;
            }
            if let Some(pe) = prev_end_line {
                out.push(if pe == span.start_line { ' ' } else { '\n' });
            }
            out.push_str(hdr);
            let mut sub_prev_end = span.start_line + hdr.matches('\n').count();
            for sub in kept_subs {
                out.push(if sub_prev_end == sub.start_line {
                    ' '
                } else {
                    '\n'
                });
                out.push_str(sub.orig_text);
                sub_prev_end = sub.end_line;
            }
            let ftr_start_line = span.end_line.saturating_sub(ftr.matches('\n').count());
            out.push(if sub_prev_end == ftr_start_line {
                ' '
            } else {
                '\n'
            });
            out.push_str(ftr);
            prev_end_line = Some(span.end_line);
        } else if let Some(&n_idx) = single_decl_by_top.get(&top_idx) {
            if needed[n_idx] {
                if let Some(pe) = prev_end_line {
                    out.push(if pe == span.start_line { ' ' } else { '\n' });
                }
                out.push_str(span.orig_text);
                prev_end_line = Some(span.end_line);
            }
        } else {
            splitter::update_scope_stack_with_idx(&mut open_scopes, span.orig_text, top_idx);
            if !splitter::audit_hygiene(span.clean_text).has_sorry {
                if let Some(pe) = prev_end_line {
                    out.push(if pe == span.start_line { ' ' } else { '\n' });
                }
                out.push_str(span.orig_text);
                prev_end_line = Some(span.end_line);
            }
        }
    }

    let mut i = open_scopes.len();
    while i > 0 {
        let top = &open_scopes[i - 1];
        if top.kind == splitter::ScopeKind::Namespace && !top.name.is_empty() {
            let group = top.open_span_idx;
            let mut start = i - 1;
            while start > 0
                && open_scopes[start - 1].kind == splitter::ScopeKind::Namespace
                && !open_scopes[start - 1].name.is_empty()
                && open_scopes[start - 1].open_span_idx == group
            {
                start -= 1;
            }
            let joined: Vec<&str> = open_scopes[start..i]
                .iter()
                .map(|f| f.name.as_str())
                .collect();
            out.push('\n');
            out.push_str("end ");
            out.push_str(&joined.join("."));
            i = start;
        } else {
            out.push('\n');
            if top.name.is_empty() {
                out.push_str("end");
            } else {
                out.push_str("end ");
                out.push_str(&top.name);
            }
            i -= 1;
        }
    }
    out.push('\n');
    out
}

#[allow(clippy::too_many_arguments)]
pub(super) fn maybe_append_hotspot_diagnostics_for_source(
    store: &TurboStore,
    toolchain: &str,
    local_lean_path: &str,
    env_vars: &HashMap<String, String>,
    lean_bin: &Path,
    source: &str,
    file_name: Option<&str>,
    lean_args: &[String],
    err_text: &str,
) -> String {
    if !crate::zygote::text_indicates_timeout_or_heartbeat(err_text)
        || err_text.contains("[hotspot] ")
    {
        return String::new();
    }
    crate::zygote::diagnose_hotspots_with_zygote_pool(
        store,
        toolchain,
        local_lean_path,
        env_vars,
        lean_bin,
        source,
        file_name,
        None,
        lean_args,
    )
    .map(|(th, sh)| {
        let fmt = crate::zygote::format_hotspot_diagnostics(&th, &sh);
        if fmt.is_empty() {
            String::new()
        } else {
            format!("\n{fmt}")
        }
    })
    .unwrap_or_default()
}

#[allow(clippy::too_many_arguments)]
pub(super) fn check_single_decl(
    store: &mut TurboStore,
    db_warm_on_open: bool,
    json_output: bool,
    emit_stdout: bool,
    kernel_prov: &crate::kernel::KernelProvenance,
    t0: &Instant,
    file: &Path,
    resolved_file: &Path,
    canon_resolved_initial: &Path,
    canon_dir: &Path,
    toolchain: &str,
    target_decl: &str,
    src: String,
    cached_file_blake3: &mut Option<String>,
    split: &mut splitter::SplitResult,
    known_modified_vs_head: bool,
    _single_split_hits: usize,
    remote_http: Option<&str>,
    allow_sorry: bool,
) -> Result<serde_json::Value> {
    let active_file = resolved_file.to_path_buf();
    let mut active_src = recover_decl_source(src, &active_file)?;

    let shard_idx =
        splitter::find_decl_shard_index(&split.shards, target_decl)?.with_context(|| {
            format!(
                "Declaration `{}` not found in {} (found {} theorem shards)",
                target_decl,
                file.display(),
                split.shards.len()
            )
        })?;
    if split.shards[shard_idx].signature_text.is_empty()
        || split.shards[shard_idx].proof_text.is_empty()
    {
        let end_line = split.shards[shard_idx].end_line;
        if active_src.is_empty() || active_src.lines().count() < end_line {
            if let Ok(full_src) = fs::read_to_string(&active_file) {
                active_src = full_src;
            }
        }
        let (sig, prf) =
            splitter::extract_shard_stmt_and_proof(&active_src, &split.shards[shard_idx]);
        if split.shards[shard_idx].signature_text.is_empty() {
            split.shards[shard_idx].signature_text = sig;
        }
        if split.shards[shard_idx].proof_text.is_empty() {
            split.shards[shard_idx].proof_text = prf;
        }
    }
    anyhow::ensure!(
        !split.hygiene.has_checking_weakening,
        "Soundness hygiene violation in {}: {:?}",
        active_file.display(),
        split.hygiene.disallowed_items()
    );
    // Every verdict, receipt and cache entry carries the resolved full Lean name.
    let resolved_decl = split.shards[shard_idx].decl_name().to_string();
    let target_decl = resolved_decl.as_str();
    let shard = &split.shards[shard_idx];
    let target_violations = target_hygiene_violations(split, shard, allow_sorry);
    if !target_violations.is_empty() {
        anyhow::bail!(
            "Soundness hygiene violation in `{}` ({}): {}",
            target_decl,
            file.display(),
            target_violations.join(", ")
        );
    }
    let shard_has_sorry = shard_text_contains_sorry_or_admit(shard);
    let cone_src = if allow_sorry {
        build_cone_scoped_decl_audit_source(&active_src, shard)
    } else {
        audited_cone_source(&active_src, shard)?
    };
    let cone_clean_for_certification =
        splitter::audit_hygiene(&splitter::strip_lean_comments(&cone_src))
            .is_clean_for_certification();
    let clean_for_certification = split.hygiene.is_clean_for_certification();
    let allow_attested_cache_hit = clean_for_certification
        || (split.hygiene.is_clean_modulo_sorry() && cone_clean_for_certification);
    // Stat/split caches are not evidence of the identity in the current source.
    if active_src.is_empty() {
        active_src = fs::read_to_string(&active_file)?;
    }
    let attested = confirm_decl_identity_with_budget(
        &active_src,
        shard,
        canon_dir,
        &active_file,
        false,
        Some(*t0),
    )?;
    let expected_type_pair = [(
        attested.decl_name.clone(),
        attested.kernel_type_hash.clone(),
    )];
    let file_lean_args =
        crate::module_builder::try_resolve_lean_args_for_path(canon_dir, Some(&active_file))?;

    let shard_key = compute_shard_key_with_args(toolchain, shard, &file_lean_args);
    let make_cache_hit_json = |coalesced: bool, elapsed_ms: u128| {
        let cached_consts =
            crate::accelerators::lookup_distilled_constants(target_decl, &shard.signature_text);
        let feats = crate::matryoshka::parse_lean_stmt_features(target_decl, &shard.signature_text);
        let skel = crate::matryoshka::extract_tactic_skeleton(&shard.proof_text);
        let cached_proof_nodes = crate::accelerators::lookup_distilled_proof_term_nodes(
            target_decl,
            &shard.signature_text,
        )
        .unwrap_or_else(|| {
            crate::matryoshka::estimate_decl_proof_term_nodes(
                target_decl,
                &shard.signature_text,
                &shard.proof_text,
            )
        });
        let mut hit_json = serde_json::json!({
            "status": "theorem_cache_hit",
            "decl": target_decl,
            "coalesced": coalesced,
            "shard_key": &shard_key,
            "interface_hash": &split.interface_hash,
            "prefix_env_hash": &shard.prefix_env_hash,
            "used_constants": cached_consts,
            "stmt_nodes": feats.stmt_nodes,
            "stmt_depth": feats.stmt_depth,
            "num_binders": feats.num_binders,
            "goal_head": feats.goal_head,
            "stmt_consts": feats.stmt_consts,
            "tactic_skeleton": skel,
            "proof_term_nodes": cached_proof_nodes,
            "compact_summary": format!("OK decl={} ms={} stage=cache_hit", target_decl, elapsed_ms),
            "estimated_tokens": 18,
            "elapsed_ms": elapsed_ms
        });
        insert_allow_sorry_fields(&mut hit_json, allow_sorry, false, &[]);
        kernel_prov.insert_json_fields(&mut hit_json);
        hit_json
    };

    if !allow_sorry && !clean_for_certification {
        if allow_attested_cache_hit
            && !shard_has_sorry
            && db_warm_on_open
            && (store.has_attested_decl_receipt(
                &shard_key,
                "trusted",
                target_decl,
                &attested.kernel_type_hash,
            ) || store.has_attested_decl_receipt(
                &pack::client_attested_receipt_key(&shard_key),
                "trusted",
                target_decl,
                &attested.kernel_type_hash,
            ))
        {
            let elapsed_ms = t0.elapsed().as_millis();
            let out_json = make_cache_hit_json(false, elapsed_ms);
            if emit_stdout {
                if json_output {
                    println!("{}", serde_json::to_string_pretty(&out_json)?);
                } else {
                    println!(
                        "[turbo-lean] SHARD CACHE HIT `{}` (coalesced=false, {} ms)",
                        target_decl, elapsed_ms
                    );
                }
            }
            return Ok(out_json);
        }
        let (env_vars, _) = resolve_lake_env(store, canon_dir)?;
        let lean_bin = resolve_lean_bin(canon_dir)?;
        let (output, report) = crate::zygote::run_audited_lean_shard_at_with_full_report(
            &store.root,
            &store.fast_staging_dir(),
            Path::new(&lean_bin),
            &env_vars,
            Some(canon_dir),
            None,
            &cone_src,
            &HashSet::from([shard.rooted_name()]),
            false,
            false,
            &expected_type_pair,
            &file_lean_args,
            Some(crate::zygote::remaining_timeout_ms(None, *t0)),
        )?;
        anyhow::ensure!(
            output.status.success() && !report.used_sorry && report.sorry_decls.is_empty(),
            "Soundness audit failed for `{target_decl}`: {}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let mut verified_via_fast_olean = false;
        let rooted_target = shard.rooted_name();
        let prefix = active_src
            .lines()
            .take(shard.start_line.saturating_sub(1))
            .collect::<Vec<_>>()
            .join("\n");
        if !splitter::audit_hygiene(&splitter::strip_lean_comments(&prefix)).has_sorry
            && !split.hygiene.has_unsafe
            && !split.hygiene.has_extern_or_implemented_by
            && !split
                .hygiene
                .flagged_items
                .iter()
                .any(|item| item.ends_with(": csimp"))
        {
            if let Some(outline_plan) =
                splitter::build_prefix_outline_plan_with_split(&active_src, split, &rooted_target)
            {
                let local_lean_path = resolve_remote_lean_path(canon_dir, Some(&env_vars));
                let orig_display = file.display().to_string();
                if let Ok((outline_dir, outline_mod)) = crate::zygote::ensure_prefix_outline_olean(
                    store,
                    toolchain,
                    &local_lean_path,
                    &env_vars,
                    Path::new(&lean_bin),
                    &outline_plan.outline_source,
                    &orig_display,
                    &file_lean_args,
                ) {
                    let delta_lp = if local_lean_path.is_empty() {
                        outline_dir.to_string_lossy().into_owned()
                    } else {
                        format!("{}:{}", outline_dir.display(), local_lean_path)
                    };
                    let delta_src = outline_plan.render_delta_shard_source(&outline_mod);
                    let mut delta_ev = env_vars.clone();
                    delta_ev.insert("LEAN_PATH".to_string(), delta_lp.clone());
                    let stub_targets = vec![rooted_target.clone()];
                    if let Ok(reply) = crate::zygote::eval_with_zygote_pool_for_targets_and_stubs(
                        store,
                        toolchain,
                        &delta_lp,
                        &delta_ev,
                        Path::new(&lean_bin),
                        &delta_src,
                        &stub_targets,
                        &outline_plan.outline_stubs,
                        Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                        &file_lean_args,
                    ) {
                        if reply.import_ok
                            && reply.ok
                            && !reply.crashed
                            && !reply.timed_out
                            && crate::zygote::verify_attested_decl_types(
                                &reply.decl_types,
                                &expected_type_pair,
                            )
                            .is_ok()
                        {
                            verified_via_fast_olean = true;
                        }
                    }
                }
            }
        }
        let mut result = serde_json::json!({
            "status": "theorem_verified",
            "decl": target_decl,
            "shard_key": shard_key,
            "fast_olean_import": verified_via_fast_olean,
            "elapsed_ms": t0.elapsed().as_millis(),
            "compact_summary": format!("OK decl={target_decl} stage=kernel_audit"),
        });
        insert_allow_sorry_fields(&mut result, false, false, &[]);
        kernel_prov.insert_json_fields(&mut result);
        if emit_stdout {
            if json_output {
                println!("{}", serde_json::to_string_pretty(&result)?);
            } else {
                println!("[turbo-lean] VERIFIED `{target_decl}` (kernel audit)");
            }
        }
        return Ok(result);
    }

    if allow_sorry {
        // Under `--allow-sorry`, a clean sibling shard may still hit `TheoremProofCAS`,
        // whereas any modulo-sorry check runs in-process without touching singleflight or CAS.
        // Always route `allow_sorry` through this branch even when `file` itself is lexically
        // `sorry`-free so a transitive `sorryAx` dependency from an imported workspace module
        // is reported as `verified_modulo_sorry` (and never cached in `TheoremProofCAS`).
        if !shard_has_sorry
            && allow_attested_cache_hit
            && db_warm_on_open
            && store.has_attested_decl_receipt(
                &shard_key,
                "trusted",
                target_decl,
                &attested.kernel_type_hash,
            )
        {
            let elapsed_ms = t0.elapsed().as_millis();
            let out_json = make_cache_hit_json(false, elapsed_ms);
            if emit_stdout {
                if json_output {
                    println!("{}", serde_json::to_string_pretty(&out_json)?);
                } else {
                    println!(
                        "[turbo-lean] SHARD CACHE HIT `{}` (coalesced=false, {} ms)",
                        target_decl, elapsed_ms
                    );
                }
            }
            return Ok(out_json);
        }

        let rooted_target = shard.rooted_name();
        let single_set = HashSet::from([rooted_target.clone()]);
        let full_shard_src = cone_src.clone();
        let (env_vars, env_cache_hit) = resolve_lake_env(store, canon_dir)?;
        let lean_bin = resolve_lean_bin(canon_dir)?;
        let t0 = &prewarm_local_check_zygote(store, canon_dir, toolchain, t0)?;
        let local_lean_path = resolve_remote_lean_path(canon_dir, Some(&env_vars));
        let mut stub_targets: Vec<String> = single_set.iter().cloned().collect();
        stub_targets.sort();

        let mut verified_via_zygote = false;
        let mut zygote_env_cache_hit = false;
        let mut zygote_import_us = 0u64;
        let mut zygote_elab_us = 0u64;
        let mut heartbeats_used = 0u64;
        let mut proof_term_nodes = 0u64;
        let mut rss_delta_mb = 0i64;
        let mut peak_rss_mb = crate::zygote::measure_process_rss_mb(std::process::id());
        let mut used_constants: Vec<String> = Vec::new();
        let mut used_sorry = shard_has_sorry;
        let mut sorry_decls: Vec<String> = Vec::new();

        let reply = crate::zygote::eval_with_zygote_pool_for_targets_modulo_sorry(
            store,
            toolchain,
            &local_lean_path,
            &env_vars,
            Path::new(&lean_bin),
            &full_shard_src,
            &stub_targets,
            Some(crate::zygote::remaining_timeout_ms(None, *t0)),
            &file_lean_args,
            true,
        )
        .with_context(|| {
            format!(
                "Zygote check failed for `{}` in {} (lines {}..={})",
                target_decl,
                file.display(),
                shard.start_line,
                shard.end_line
            )
        })?;
        let c_abi_sound = unsafe {
            crate::splitter::turbo_spec_is_sound_decl_summary(0, 0, 0, if reply.ok { 0 } else { 1 })
                != 0
        };
        if reply.import_ok && reply.ok && !reply.crashed && !reply.timed_out && c_abi_sound {
            crate::zygote::verify_attested_decl_types(&reply.decl_types, &expected_type_pair)?;
            verified_via_zygote = true;
            zygote_env_cache_hit = reply.env_cache_hit;
            zygote_import_us = reply.import_us;
            zygote_elab_us = reply.elab_us;
            heartbeats_used = reply.heartbeats;
            proof_term_nodes = reply.proof_term_nodes;
            rss_delta_mb = reply.rss_delta_mb;
            peak_rss_mb = peak_rss_mb.max(reply.peak_rss_mb);
            used_constants = reply.used_constants;
            used_sorry |= reply.used_sorry || !reply.sorry_decls.is_empty();
            sorry_decls = reply.sorry_decls;
        } else if reply.crashed || reply.timed_out || reply.import_ok {
            let orig_display = file.display().to_string();
            let raw_err = reply
                .errors
                .join("\n")
                .replace("<zygote-decl>", &orig_display)
                .replace("<zygote-shard>", &orig_display);
            let m_diags = extract_mismatch_diagnostics(&raw_err);
            let m_suffix = format_mismatch_diagnostics_summary(&m_diags);
            let h_fmt = crate::zygote::format_hotspot_diagnostics(
                &reply.timeout_hotspots,
                &reply.simp_hotspots,
            );
            let h_suffix = if h_fmt.is_empty() {
                String::new()
            } else {
                format!("\n{h_fmt}")
            };
            anyhow::bail!(
                "lean check failed for `{}` in {} (lines {}..={}):\n{}{}{}",
                target_decl,
                file.display(),
                shard.start_line,
                shard.end_line,
                raw_err,
                m_suffix,
                h_suffix
            );
        }

        if !verified_via_zygote {
            let default_stack = env_vars
                .get("LEAN_STACK_SIZE_KB")
                .cloned()
                .or_else(|| std::env::var("LEAN_STACK_SIZE_KB").ok())
                .unwrap_or_else(|| "262144".to_string());
            let mut fallback_env = env_vars.clone();
            fallback_env.insert("LEAN_STACK_SIZE_KB".to_string(), default_stack);
            let (out, audit_rep) = crate::zygote::run_audited_lean_shard_with_sorry_report(
                store,
                Path::new(&lean_bin),
                &fallback_env,
                Some(canon_dir),
                &full_shard_src,
                &single_set,
                &expected_type_pair,
                &file_lean_args,
                Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                true,
            )
            .with_context(|| {
                format!(
                    "Shard check failed for `{}` in {} (lines {}..={})",
                    target_decl,
                    file.display(),
                    shard.start_line,
                    shard.end_line
                )
            })?;
            if !out.status.success() {
                let orig_display = file.display().to_string();
                let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
                let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
                let combined_err = format!("{}\n{}", stdout, stderr);
                let m_diags = extract_mismatch_diagnostics(&combined_err);
                let m_suffix = format_mismatch_diagnostics_summary(&m_diags);
                let h_suffix = maybe_append_hotspot_diagnostics_for_source(
                    store,
                    toolchain,
                    &local_lean_path,
                    &fallback_env,
                    Path::new(&lean_bin),
                    &full_shard_src,
                    Some(&orig_display),
                    &file_lean_args,
                    &combined_err,
                );
                anyhow::bail!(
                    "Shard check failed for `{}` in {} (lines {}..={}):\n{}{}{}",
                    target_decl,
                    orig_display,
                    shard.start_line,
                    shard.end_line,
                    combined_err,
                    m_suffix,
                    h_suffix
                );
            }
            used_sorry |= audit_rep.used_sorry || !audit_rep.sorry_decls.is_empty();
            sorry_decls = audit_rep.sorry_decls;
        }

        if used_sorry && sorry_decls.is_empty() {
            sorry_decls.push(target_decl.to_string());
        }
        sorry_decls.sort();
        sorry_decls.dedup();

        let dur_ms = t0.elapsed().as_millis() as i64;
        if !used_sorry
            && !shard_has_sorry
            && sorry_decls.is_empty()
            && split.hygiene.is_clean_for_certification()
        {
            let receipt = make_attested_shard_receipt_bytes(
                target_decl,
                &shard.prefix_env_hash,
                &shard.stmt_hash,
                &shard.proof_hash,
                db::now_unix(),
                Some(&attested.kernel_type_hash),
            )?;
            store.batch_publish_theorem_shards(
                toolchain,
                "trusted",
                &[(
                    shard_key.clone(),
                    target_decl.to_string(),
                    receipt,
                    dur_ms.max(1),
                )],
            )?;
        }

        if proof_term_nodes == 0 {
            proof_term_nodes = crate::matryoshka::estimate_decl_proof_term_nodes(
                target_decl,
                &shard.signature_text,
                &shard.proof_text,
            );
        }
        let stmt_feats =
            crate::matryoshka::parse_lean_stmt_features(target_decl, &shard.signature_text);
        let tactic_skeleton = crate::matryoshka::extract_tactic_skeleton(&shard.proof_text);
        let status_str = if used_sorry {
            "verified_modulo_sorry"
        } else {
            "theorem_verified"
        };
        let compact_summary = if used_sorry {
            format!(
                "MODULO_SORRY decl={} sorry_count={} ms={} hbs={}",
                target_decl,
                sorry_decls.len(),
                dur_ms,
                heartbeats_used
            )
        } else {
            format!(
                "OK decl={} ms={} hbs={} stage={}",
                target_decl,
                dur_ms,
                heartbeats_used,
                if verified_via_zygote {
                    "zygote"
                } else {
                    "lean"
                }
            )
        };
        let mut out_json = serde_json::json!({
            "status": status_str,
            "allow_sorry": true,
            "used_sorry": used_sorry,
            "sorry_count": sorry_decls.len(),
            "sorry_decls": sorry_decls,
            "decl": target_decl,
            "shard_key": shard_key,
            "lake_env_cache_hit": env_cache_hit,
            "fast_olean_import": false,
            "zygote_used": verified_via_zygote,
            "zygote_env_cache_hit": zygote_env_cache_hit,
            "zygote_import_us": zygote_import_us,
            "zygote_elab_us": zygote_elab_us,
            "heartbeats_used": heartbeats_used,
            "proof_term_nodes": proof_term_nodes,
            "used_constants": used_constants,
            "stmt_nodes": stmt_feats.stmt_nodes,
            "stmt_depth": stmt_feats.stmt_depth,
            "num_binders": stmt_feats.num_binders,
            "goal_head": stmt_feats.goal_head,
            "stmt_consts": stmt_feats.stmt_consts,
            "tactic_skeleton": tactic_skeleton,
            "rss_delta_mb": rss_delta_mb,
            "peak_rss_mb": peak_rss_mb,
            "accelerator_assisted": false,
            "winning_accelerator": serde_json::Value::Null,
            "fission_cached_subshards": 0,
            "fission_verified_subshards": 0,
            "interface_hash": split.interface_hash,
            "prefix_env_hash": shard.prefix_env_hash,
            "total_shards_in_file": split.shards.len(),
            "compact_summary": compact_summary,
            "estimated_tokens": 18,
            "elapsed_ms": dur_ms
        });
        kernel_prov.insert_json_fields(&mut out_json);
        if emit_stdout {
            if json_output {
                println!("{}", serde_json::to_string_pretty(&out_json)?);
            } else if used_sorry {
                println!(
                    "[turbo-lean] VERIFIED MODULO SORRY `{}` ({} sorry decl(s): [{}], {} ms)",
                    target_decl,
                    sorry_decls.len(),
                    sorry_decls.join(", "),
                    dur_ms
                );
            } else {
                println!(
                    "[turbo-lean] SHARD VERIFIED `{}` ({}/{} shards in file, env_cache_hit={}, fast_olean=false, zygote={}, interface_hash={}.., {} ms)",
                    target_decl,
                    1,
                    split.shards.len(),
                    env_cache_hit,
                    verified_via_zygote,
                    &split.interface_hash[..12],
                    dur_ms
                );
            }
        }
        return Ok(out_json);
    }

    if split.hygiene.is_clean_for_certification() {
        if let Some(remote_url) = remote_http {
            if db_warm_on_open
                && (store.has_attested_decl_receipt(
                    &shard_key,
                    "trusted",
                    target_decl,
                    &attested.kernel_type_hash,
                ) || store.has_attested_decl_receipt(
                    &pack::client_attested_receipt_key(&shard_key),
                    "trusted",
                    target_decl,
                    &attested.kernel_type_hash,
                ))
            {
                let elapsed_ms = t0.elapsed().as_millis();
                let out_json = make_cache_hit_json(false, elapsed_ms);
                if emit_stdout {
                    if json_output {
                        println!("{}", serde_json::to_string_pretty(&out_json)?);
                    } else {
                        println!(
                            "[turbo-lean] SHARD CACHE HIT `{}` (coalesced=false, {} ms)",
                            target_decl, elapsed_ms
                        );
                    }
                }
                return Ok(out_json);
            }
            if active_src.is_empty() {
                active_src = fs::read_to_string(&active_file)
                    .with_context(|| format!("Failed to read {}", active_file.display()))?;
            }
            let canon_file = if active_file == resolved_file {
                canon_resolved_initial.to_path_buf()
            } else {
                active_file
                    .canonicalize()
                    .unwrap_or_else(|_| active_file.clone())
            };
            let rooted_target = shard.rooted_name();
            let single_set = HashSet::from([rooted_target.clone()]);
            let fast_olean_src = if split.shards.len() <= 1 {
                None
            } else {
                resolve_replayed_prebuilt_module_import(store, canon_dir, &canon_file).and_then(
                    |mod_imp| {
                        splitter::build_fast_olean_shard_source_with_split(
                            &active_src,
                            split,
                            &mod_imp,
                            &single_set,
                        )
                    },
                )
            };
            let endpoint = format!("{}/check-shard", remote_url.trim_end_matches('/'));
            let cached_env = if db_warm_on_open {
                let env_key = TurboStore::compute_lake_env_key(canon_dir);
                store.get_lake_env(&env_key).ok().flatten()
            } else {
                None
            };
            let local_lean_path = resolve_remote_lean_path(canon_dir, cached_env.as_ref());

            let fast_candidates: Vec<(&str, bool)> = fast_olean_src
                .as_ref()
                .map(|src| vec![(src.as_str(), true)])
                .unwrap_or_default();

            let mut resp_json = serde_json::Value::Null;
            let mut remote_status = String::from("unknown");
            let mut fast_olean_used = false;
            let mut last_err: Option<anyhow::Error> = None;

            let full_shard_src: String;
            let mut candidates = fast_candidates;
            if candidates.is_empty() {
                full_shard_src = cone_src.clone();
                candidates.push((full_shard_src.as_str(), false));
            }

            let effective_remote_args =
                crate::module_builder::validate_effective_lean_args(&file_lean_args)?;
            for (cand_src, is_fast) in &candidates {
                let is_fast = *is_fast;
                let req_body = serde_json::to_vec(&pack::CheckShardHttpRequest {
                    decl: target_decl.to_string(),
                    shard_key: shard_key.clone(),
                    shard_source: (*cand_src).to_string(),
                    interface_hash: split.interface_hash.clone(),
                    prefix_env_hash: shard.prefix_env_hash.clone(),
                    stmt_hash: shard.stmt_hash.clone(),
                    proof_hash: shard.proof_hash.clone(),
                    toolchain: toolchain.to_string(),
                    lean_path: local_lean_path.clone(),
                    skip_cas_lock: false,
                    allowed_axioms: Some(splitter::extra_allowed_axiom_patterns()),
                    lean_args: effective_remote_args.clone(),
                    targets: vec![rooted_target.clone()],
                    expected_kernel_type_hash: Some(attested.kernel_type_hash.clone()),
                })?;
                match pack::http_request("POST", &endpoint, "application/json", &req_body) {
                    Ok(resp_bytes) => {
                        match serde_json::from_slice::<serde_json::Value>(&resp_bytes) {
                            Ok(rj) => {
                                let st = rj
                                    .get("status")
                                    .and_then(|v| v.as_str())
                                    .unwrap_or("unknown")
                                    .to_string();
                                if st == "remote_theorem_verified"
                                    || st == "remote_theorem_cache_hit"
                                {
                                    let remote_type_ok = rj
                                        .get("kernel_type_hash")
                                        .and_then(|v| v.as_str())
                                        .is_some_and(|h| h == attested.kernel_type_hash)
                                        || rj
                                            .get("decl_types")
                                            .and_then(|v| {
                                                serde_json::from_value::<
                                                    std::collections::BTreeMap<String, String>,
                                                >(
                                                    v.clone()
                                                )
                                                .ok()
                                            })
                                            .is_some_and(|m| {
                                                crate::zygote::verify_attested_decl_types(
                                                    &m,
                                                    &expected_type_pair,
                                                )
                                                .is_ok()
                                            });
                                    if remote_type_ok {
                                        resp_json = rj;
                                        remote_status = st;
                                        fast_olean_used = is_fast;
                                        last_err = None;
                                        break;
                                    }
                                    last_err = Some(anyhow::anyhow!(
                                        "Remote shard check for `{target_decl}` on {endpoint} missed or mismatched `kernel_type_hash`"
                                    ));
                                } else {
                                    last_err = Some(anyhow::anyhow!(
                                        "Remote shard check failed on {}: {}",
                                        endpoint,
                                        rj
                                    ));
                                }
                            }
                            Err(e) => {
                                last_err = Some(anyhow::anyhow!(
                                    "Remote shard check on {endpoint} returned invalid JSON: {e}"
                                ));
                            }
                        }
                    }
                    Err(e) => {
                        last_err = Some(e);
                    }
                }
            }
            if last_err.is_some() && !candidates.iter().any(|(_, is_fast)| !*is_fast) {
                let fallback_src = cone_src.clone();
                let req_body = serde_json::to_vec(&pack::CheckShardHttpRequest {
                    decl: target_decl.to_string(),
                    shard_key: shard_key.clone(),
                    shard_source: fallback_src,
                    interface_hash: split.interface_hash.clone(),
                    prefix_env_hash: shard.prefix_env_hash.clone(),
                    stmt_hash: shard.stmt_hash.clone(),
                    proof_hash: shard.proof_hash.clone(),
                    toolchain: toolchain.to_string(),
                    lean_path: local_lean_path.clone(),
                    skip_cas_lock: false,
                    allowed_axioms: Some(splitter::extra_allowed_axiom_patterns()),
                    lean_args: effective_remote_args,
                    targets: vec![rooted_target],
                    expected_kernel_type_hash: Some(attested.kernel_type_hash.clone()),
                })?;
                if let Ok(resp_bytes) =
                    pack::http_request("POST", &endpoint, "application/json", &req_body)
                {
                    if let Ok(rj) = serde_json::from_slice::<serde_json::Value>(&resp_bytes) {
                        let st = rj
                            .get("status")
                            .and_then(|v| v.as_str())
                            .unwrap_or("unknown")
                            .to_string();
                        let remote_type_ok = rj
                            .get("kernel_type_hash")
                            .and_then(|v| v.as_str())
                            .is_some_and(|h| h == attested.kernel_type_hash)
                            || rj
                                .get("decl_types")
                                .and_then(|v| {
                                    serde_json::from_value::<
                                        std::collections::BTreeMap<String, String>,
                                    >(v.clone())
                                    .ok()
                                })
                                .is_some_and(|m| {
                                    crate::zygote::verify_attested_decl_types(
                                        &m,
                                        &expected_type_pair,
                                    )
                                    .is_ok()
                                });
                        if (st == "remote_theorem_verified" || st == "remote_theorem_cache_hit")
                            && remote_type_ok
                        {
                            resp_json = rj;
                            remote_status = st;
                            fast_olean_used = false;
                            last_err = None;
                        }
                    }
                }
            }
            if let Some(err) = last_err {
                return Err(err);
            }

            let dur_ms = t0.elapsed().as_millis() as i64;
            let server_elapsed_ms = resp_json
                .get("server_elapsed_ms")
                .and_then(|v| v.as_u64())
                .unwrap_or(0);
            let receipt = make_attested_shard_receipt_bytes(
                target_decl,
                &shard.prefix_env_hash,
                &shard.stmt_hash,
                &shard.proof_hash,
                db::now_unix(),
                Some(&attested.kernel_type_hash),
            )?;
            store.batch_publish_theorem_shards(
                toolchain,
                "trusted",
                &[(
                    shard_key.clone(),
                    target_decl.to_string(),
                    receipt,
                    (server_elapsed_ms as i64).max(dur_ms),
                )],
            )?;

            let (_, out_json) = emit_remote_decl_result(
                json_output,
                emit_stdout,
                kernel_prov,
                &resp_json,
                &remote_status,
                target_decl,
                &shard_key,
                remote_url,
                fast_olean_used,
                &split.interface_hash,
                &shard.prefix_env_hash,
                split.shards.len(),
                dur_ms,
            )?;
            return Ok(out_json);
        }
    }

    anyhow::ensure!(
        split.hygiene.is_clean_for_certification(),
        "Internal invariant violation: dirty file reached TheoremProofCAS path for `{target_decl}`"
    );

    if !shard_has_sorry
        && db_warm_on_open
        && store.has_attested_decl_receipt(
            &pack::client_attested_receipt_key(&shard_key),
            "trusted",
            target_decl,
            &attested.kernel_type_hash,
        )
    {
        let elapsed_ms = t0.elapsed().as_millis();
        let out_json = make_cache_hit_json(false, elapsed_ms);
        if emit_stdout {
            if json_output {
                println!("{}", serde_json::to_string_pretty(&out_json)?);
            } else {
                println!(
                    "[turbo-lean] SHARD CACHE HIT `{}` (coalesced=false, {} ms)",
                    target_decl, elapsed_ms
                );
            }
        }
        return Ok(out_json);
    }

    let t0 = &prewarm_local_check_zygote(store, canon_dir, toolchain, t0)?;
    let singleflight_outcome =
        match store.acquire_singleflight(&shard_key, toolchain, "theorem_shard", "trusted")? {
            SingleflightOutcome::CacheHit { outputs, coalesced } => {
                if store.outputs_have_attested_decl_receipt(
                    &outputs,
                    target_decl,
                    &attested.kernel_type_hash,
                ) {
                    SingleflightOutcome::CacheHit { outputs, coalesced }
                } else {
                    store.invalidate_action_for_reattestation(&shard_key)?;
                    store.acquire_singleflight(&shard_key, toolchain, "theorem_shard", "trusted")?
                }
            }
            other => other,
        };

    match singleflight_outcome {
        SingleflightOutcome::CacheHit { coalesced, .. } => {
            let elapsed_ms = t0.elapsed().as_millis();
            let out_json = make_cache_hit_json(coalesced, elapsed_ms);
            if emit_stdout {
                if json_output {
                    println!("{}", serde_json::to_string_pretty(&out_json)?);
                } else {
                    println!(
                        "[turbo-lean] SHARD CACHE HIT `{}` (coalesced={}, {} ms)",
                        target_decl, coalesced, elapsed_ms
                    );
                }
            }
            Ok(out_json)
        }
        SingleflightOutcome::Leader(lease) => {
            let same_as_initial = active_file == resolved_file;
            let canon_file = if same_as_initial {
                canon_resolved_initial.to_path_buf()
            } else {
                active_file
                    .canonicalize()
                    .unwrap_or_else(|_| active_file.clone())
            };
            let rooted_target = shard.rooted_name();
            let single_set = HashSet::from([rooted_target.clone()]);

            let proj_build_verified = !(known_modified_vs_head && same_as_initial)
                && split.hygiene.is_clean_for_certification()
                && cached_file_blake3
                    .as_deref()
                    .map(|h| is_file_hash_verified_in_lake_build(canon_dir, &canon_file, h))
                    .unwrap_or_else(|| {
                        if active_src.is_empty() {
                            active_src = fs::read_to_string(&active_file).unwrap_or_default();
                        }
                        is_file_verified_in_lake_build(canon_dir, &canon_file, &active_src)
                    });
            let prebuilt_mod =
                resolve_replayed_prebuilt_module_import(store, canon_dir, &canon_file);
            let mut verified_via_fast_olean = if proj_build_verified {
                if let (Some(ref mod_imp), Ok(cfg)) = (
                    &prebuilt_mod,
                    crate::module_builder::resolve_project_config(canon_dir),
                ) {
                    let lp = resolve_remote_lean_path(canon_dir, None);
                    crate::zygote::audit_compiled_shard_module_with_zygote(
                        store,
                        &cfg,
                        mod_imp,
                        &lp,
                        &[],
                        &[],
                        &single_set,
                        &expected_type_pair,
                        false,
                    )
                    .is_ok()
                } else {
                    false
                }
            } else {
                false
            };
            let mut verified_via_zygote = verified_via_fast_olean;
            let mut zygote_env_cache_hit = verified_via_fast_olean;
            let mut zygote_import_us = 0u64;
            let mut zygote_elab_us = 0u64;
            let mut heartbeats_used = 0u64;
            let mut proof_term_nodes = 0u64;
            let mut rss_delta_mb = 0i64;
            let mut peak_rss_mb = if verified_via_fast_olean {
                0
            } else {
                crate::zygote::measure_process_rss_mb(std::process::id())
            };
            let mut used_constants: Vec<String> = Vec::new();
            let mut fission_cached_subshards = 0usize;
            let mut fission_verified_subshards = 0usize;
            let mut accelerator_assisted = false;
            let mut winning_accelerator: Option<String> = None;

            let fast_lib_dir = canon_dir.join(".lake/build/lib/lean");
            let has_pkg_lib_dir = canon_dir.join(".lake/packages").is_dir();
            let fast_local_zygote_url = if !verified_via_zygote {
                let mut fast_ev = HashMap::new();
                if fast_lib_dir.exists() || has_pkg_lib_dir {
                    fast_ev.insert(
                        "LEAN_PATH".to_string(),
                        resolve_remote_lean_path(canon_dir, None),
                    );
                }
                pack::ensure_local_zygote_daemon(store, &fast_ev)
            } else {
                None
            };
            let (mut env_vars, mut env_cache_hit, mut lean_bin, local_lean_path) =
                if verified_via_zygote {
                    (
                        HashMap::new(),
                        db_warm_on_open,
                        resolve_lean_bin(canon_dir)?,
                        String::new(),
                    )
                } else if fast_lib_dir.exists()
                    || has_pkg_lib_dir
                    || fast_local_zygote_url.is_some()
                {
                    let lp = resolve_remote_lean_path(canon_dir, None);
                    let mut fast_ev = HashMap::new();
                    fast_ev.insert("LEAN_PATH".to_string(), lp.clone());
                    (fast_ev, db_warm_on_open, resolve_lean_bin(canon_dir)?, lp)
                } else {
                    let (ev, ech) = resolve_lake_env(store, canon_dir)?;
                    let lb = resolve_lean_bin(canon_dir)?;
                    let lp = resolve_remote_lean_path(canon_dir, Some(&ev));
                    (ev, ech, lb, lp)
                };

            if !verified_via_zygote && active_src.is_empty() {
                active_src = fs::read_to_string(&active_file)
                    .with_context(|| format!("Failed to read {}", active_file.display()))?;
            }

            let decl_src = if verified_via_zygote {
                String::new()
            } else {
                extract_decl_source_from_file(&active_src, shard)
            };
            let fission_sub_shards: Vec<splitter::FissionSubShard> =
                if !verified_via_zygote && decl_src.contains("have ") {
                    let accel_cfg = crate::accelerators::AcceleratorConfig::load(Some(canon_dir));
                    let cut_fission_enabled = accel_cfg.enabled
                        && !accel_cfg
                            .disabled_builtins
                            .iter()
                            .any(|d| d == "builtin:cut-fission" || d == "cut-fission");
                    if cut_fission_enabled {
                        splitter::fission_theorem_have_blocks(&decl_src, &shard.name)
                    } else {
                        Vec::new()
                    }
                } else {
                    Vec::new()
                };

            // Closed-Loop Incremental `FissionPlan` Replay:
            // When at least 1 prior `have` cut or conclusion sub-shard is already verified in CAS
            // under this exact `(toolchain, prefix_env_hash)`, skip re-elaborating cached sub-shards
            // and verify only the uncached/edited sub-shard(s) via `ZygoteWorker` (`0 sorryAx`).
            if !verified_via_zygote && fission_sub_shards.len() >= 2 {
                let fission_keys: Vec<String> = fission_sub_shards
                    .iter()
                    .map(|s| {
                        compute_fission_store_key_with_args(
                            toolchain,
                            &shard.prefix_env_hash,
                            &s.sub_shard_key,
                            &file_lean_args,
                        )
                    })
                    .collect();
                let cached_subs: HashMap<String, String> = store
                    .batch_get_theorem_shards_readonly(&fission_keys, "trusted")
                    .unwrap_or_default()
                    .into_iter()
                    .filter(|(_, bh)| subshard_receipt_provenance_ok(store, bh))
                    .collect();
                let fission_cold_enabled = std::env::var("TURBO_LEAN_FISSION_COLD").as_deref()
                    == Ok("1")
                    || crate::shm_cache::MemoryBudgetGovernor::detect().is_low_memory_mode();
                if !cached_subs.is_empty() || fission_cold_enabled {
                    if env_vars.len() <= 1 {
                        let (ev, ech) = resolve_lake_env(store, canon_dir)?;
                        lean_bin = resolve_lean_bin(canon_dir)?;
                        env_vars = ev;
                        env_cache_hit = ech;
                    }
                    let full_shard_src = cone_src.clone();
                    let (prefix_src, closing_suffix) = if !decl_src.is_empty() {
                        if let Some(pos) = full_shard_src.rfind(&decl_src) {
                            (
                                full_shard_src[..pos].to_string(),
                                full_shard_src[pos + decl_src.len()..].to_string(),
                            )
                        } else {
                            (String::new(), String::new())
                        }
                    } else {
                        (String::new(), String::new())
                    };
                    let stub_sig = if closing_suffix.trim().is_empty() {
                        format!("{} := sorry", shard.signature_text.trim_end())
                    } else {
                        format!(
                            "{} := sorry\n{}",
                            shard.signature_text.trim_end(),
                            closing_suffix.trim_start()
                        )
                    };
                    let prefix_type_matches = !shard.signature_text.trim().is_empty()
                        && crate::zygote::probe_stub_decl_types_via_zygote(
                            store,
                            toolchain,
                            &local_lean_path,
                            &env_vars,
                            Path::new(&lean_bin),
                            &prefix_src,
                            &stub_sig,
                            &file_lean_args,
                        )
                        .is_ok_and(|rep| {
                            rep.import_ok
                                && rep.ok
                                && crate::zygote::verify_attested_decl_types(
                                    &rep.decl_types,
                                    &expected_type_pair,
                                )
                                .is_ok()
                        });

                    let mut cached_hit_keys: Vec<String> = Vec::new();
                    let mut uncached_subs: Vec<(&splitter::FissionSubShard, &String, String)> =
                        Vec::new();
                    if prefix_type_matches {
                        for (sub, f_key) in fission_sub_shards.iter().zip(fission_keys.iter()) {
                            if cached_subs.contains_key(f_key) {
                                cached_hit_keys.push(f_key.clone());
                            } else {
                                let sub_decl_full = if closing_suffix.trim().is_empty() {
                                    sub.sub_decl_source.clone()
                                } else {
                                    format!(
                                        "{}\n{}",
                                        sub.sub_decl_source,
                                        closing_suffix.trim_start()
                                    )
                                };
                                uncached_subs.push((sub, f_key, sub_decl_full));
                            }
                        }
                    }

                    if prefix_type_matches && uncached_subs.is_empty() {
                        if !cached_hit_keys.is_empty() {
                            let _ = store.batch_increment_action_hits(&cached_hit_keys);
                        }
                        fission_cached_subshards = cached_hit_keys.len();
                        fission_verified_subshards = 0;
                        verified_via_zygote = true;
                        accelerator_assisted = true;
                        winning_accelerator = Some("builtin:cut-fission".to_string());
                    } else if prefix_type_matches {
                        let batch_t0 = Instant::now();
                        let uncached_decl_texts: Vec<String> = uncached_subs
                            .iter()
                            .map(|(_, _, full_txt)| full_txt.clone())
                            .collect();
                        if let Ok(reply) = crate::zygote::eval_subshards_batch_via_zygote(
                            store,
                            toolchain,
                            &local_lean_path,
                            &env_vars,
                            Path::new(&lean_bin),
                            &prefix_src,
                            &uncached_decl_texts,
                            &file_lean_args,
                        ) {
                            let c_abi_sound = unsafe {
                                crate::splitter::turbo_spec_is_sound_decl_summary(
                                    0,
                                    0,
                                    0,
                                    if reply.ok { 0 } else { 1 },
                                ) != 0
                            };
                            if reply.import_ok && reply.ok && c_abi_sound {
                                let per_sub_dur_ms = ((batch_t0.elapsed().as_millis() as i64)
                                    / (uncached_subs.len() as i64).max(1))
                                .max(1);
                                zygote_env_cache_hit |= reply.env_cache_hit;
                                zygote_import_us += reply.import_us;
                                zygote_elab_us += reply.elab_us;
                                heartbeats_used += reply.heartbeats;
                                proof_term_nodes += reply.proof_term_nodes;
                                rss_delta_mb = rss_delta_mb.max(reply.rss_delta_mb);
                                peak_rss_mb = peak_rss_mb.max(reply.peak_rss_mb);
                                for c in reply.used_constants {
                                    if !used_constants.contains(&c) {
                                        used_constants.push(c);
                                    }
                                }
                                let now_ts = db::now_unix();
                                let mut newly_verified_subshards: Vec<(
                                    String,
                                    String,
                                    Vec<u8>,
                                    i64,
                                )> = Vec::with_capacity(uncached_subs.len());
                                for (sub, f_key, _) in &uncached_subs {
                                    let sub_hash = blake3::hash(sub.sub_decl_source.as_bytes())
                                        .to_hex()
                                        .to_string();
                                    let receipt_bytes = serde_json::to_vec(&serde_json::json!({
                                        "decl": sub.step_label,
                                        "parent_decl": target_decl,
                                        "sub_shard_key": sub.sub_shard_key,
                                        "prefix_env_hash": shard.prefix_env_hash,
                                        "stmt_hash": sub_hash,
                                        "proof_hash": sub_hash,
                                        "verified_at": now_ts,
                                        "scanner_version": crate::zygote::ZYGOTE_SCANNER_VERSION,
                                        "replay_version": crate::zygote::ZYGOTE_REPLAY_VERSION,
                                    }))?;
                                    newly_verified_subshards.push((
                                        (*f_key).clone(),
                                        sub.step_label.clone(),
                                        receipt_bytes,
                                        per_sub_dur_ms,
                                    ));
                                }
                                store.batch_put_theorem_shards(
                                    toolchain,
                                    &newly_verified_subshards,
                                )?;
                                if !cached_hit_keys.is_empty() {
                                    let _ = store.batch_increment_action_hits(&cached_hit_keys);
                                }
                                fission_cached_subshards = cached_hit_keys.len();
                                fission_verified_subshards = uncached_subs.len();
                                verified_via_zygote = true;
                                accelerator_assisted = true;
                                winning_accelerator = Some("builtin:cut-fission".to_string());
                            }
                        }
                    }
                }
            }

            let fast_olean_src = if verified_via_zygote {
                None
            } else {
                prebuilt_mod.as_ref().and_then(|mod_imp| {
                    if split.shards.len() > 1 {
                        splitter::build_fast_olean_shard_source_with_split(
                            &active_src,
                            split,
                            mod_imp,
                            &single_set,
                        )
                    } else {
                        None
                    }
                })
            };

            let mut inflight_tx_open = false;
            let mut last_daemon_verify_err: Option<String> = None;
            let reply_json_matches_expected_type = |rj: &serde_json::Value| -> bool {
                rj.get("kernel_type_hash")
                    .and_then(|v| v.as_str())
                    .is_some_and(|h| h == attested.kernel_type_hash)
                    || rj
                        .get("decl_types")
                        .and_then(|v| {
                            serde_json::from_value::<std::collections::BTreeMap<String, String>>(
                                v.clone(),
                            )
                            .ok()
                        })
                        .is_some_and(|m| {
                            crate::zygote::verify_attested_decl_types(&m, &expected_type_pair)
                                .is_ok()
                        })
            };
            let mut try_zygote_src = |src_text: &str,
                                      ev: &HashMap<String, String>,
                                      record_err: bool|
             -> Option<serde_json::Value> {
                let zreq = pack::CheckShardHttpRequest {
                    decl: target_decl.to_string(),
                    shard_key: shard_key.clone(),
                    shard_source: src_text.to_string(),
                    interface_hash: split.interface_hash.clone(),
                    prefix_env_hash: shard.prefix_env_hash.clone(),
                    stmt_hash: shard.stmt_hash.clone(),
                    proof_hash: shard.proof_hash.clone(),
                    toolchain: toolchain.to_string(),
                    lean_path: local_lean_path.clone(),
                    skip_cas_lock: true,
                    allowed_axioms: Some(splitter::extra_allowed_axiom_patterns()),
                    lean_args: file_lean_args.clone(),
                    targets: vec![rooted_target.clone()],
                    expected_kernel_type_hash: Some(attested.kernel_type_hash.clone()),
                };
                if let Some(ref z_url) = fast_local_zygote_url {
                    let res = pack::try_zygote_url_check_shard_inner_with_inflight_detailed(
                        z_url,
                        &zreq,
                        || {
                            if !inflight_tx_open {
                                if let Ok(r_bytes) = make_attested_shard_receipt_bytes(
                                    target_decl,
                                    &shard.prefix_env_hash,
                                    &shard.stmt_hash,
                                    &shard.proof_hash,
                                    db::now_unix(),
                                    Some(&attested.kernel_type_hash),
                                ) {
                                    let single_pub = vec![(
                                        shard_key.clone(),
                                        target_decl.to_string(),
                                        r_bytes,
                                        1i64,
                                    )];
                                    if store
                                        .begin_inflight_publish_theorem_shards(
                                            toolchain,
                                            "trusted",
                                            &single_pub,
                                        )
                                        .is_ok()
                                    {
                                        inflight_tx_open = true;
                                    }
                                }
                            }
                        },
                    );
                    match res {
                        Ok(Some(r)) if reply_json_matches_expected_type(&r) => return Some(r),
                        Ok(Some(_)) => {
                            if record_err {
                                last_daemon_verify_err = Some(format!(
                                    "[TurboLean.KernelGate] kernel declaration type mismatch for `{target_decl}`"
                                ));
                            }
                        }
                        Ok(None) => {}
                        Err(e) => {
                            if record_err {
                                last_daemon_verify_err = Some(e.to_string());
                            }
                        }
                    }
                    if inflight_tx_open {
                        store.rollback_inflight_publish();
                        store.remove_singleflight_done(&shard_key);
                        inflight_tx_open = false;
                    }
                    return None;
                }
                match pack::try_local_zygote_check_shard_detailed(store, ev, &zreq) {
                    Ok(Some(r)) if reply_json_matches_expected_type(&r) => Some(r),
                    Ok(Some(_)) => {
                        if record_err {
                            last_daemon_verify_err = Some(format!(
                                "[TurboLean.KernelGate] kernel declaration type mismatch for `{target_decl}`"
                            ));
                        }
                        None
                    }
                    Ok(None) => None,
                    Err(e) => {
                        if record_err {
                            last_daemon_verify_err = Some(e.to_string());
                        }
                        None
                    }
                }
            };

            macro_rules! apply_zygote_json {
                ($zjson:expr) => {{
                    let zj = $zjson;
                    verified_via_zygote = true;
                    zygote_env_cache_hit = zj
                        .get("zygote_env_cache_hit")
                        .and_then(|v| v.as_bool())
                        .unwrap_or(false);
                    zygote_import_us = zj
                        .get("zygote_import_us")
                        .and_then(|v| v.as_u64())
                        .unwrap_or(0);
                    zygote_elab_us = zj
                        .get("zygote_elab_us")
                        .and_then(|v| v.as_u64())
                        .unwrap_or(0);
                    heartbeats_used = zj
                        .get("heartbeats")
                        .or_else(|| zj.get("heartbeats_used"))
                        .and_then(|v| v.as_u64())
                        .unwrap_or(heartbeats_used);
                    proof_term_nodes = zj
                        .get("proof_term_nodes")
                        .and_then(|v| v.as_u64())
                        .unwrap_or(proof_term_nodes);
                    if let Some(rd) = zj.get("rss_delta_mb").and_then(|v| v.as_i64()) {
                        rss_delta_mb = rd;
                    }
                    if let Some(pk) = zj.get("peak_rss_mb").and_then(|v| v.as_u64()) {
                        peak_rss_mb = peak_rss_mb.max(pk);
                    }
                    used_constants = zj
                        .get("used_constants")
                        .and_then(|v| v.as_array())
                        .map(|arr| {
                            arr.iter()
                                .filter_map(|x| x.as_str().map(str::to_string))
                                .collect()
                        })
                        .unwrap_or_default();
                    if proof_term_nodes > 0 {
                        crate::accelerators::record_distilled_proof_term_nodes(
                            canon_dir,
                            target_decl,
                            &shard.signature_text,
                            proof_term_nodes,
                        );
                        if shard.name != target_decl {
                            crate::accelerators::record_distilled_proof_term_nodes(
                                canon_dir,
                                &shard.name,
                                &shard.signature_text,
                                proof_term_nodes,
                            );
                        }
                    } else {
                        proof_term_nodes = crate::accelerators::lookup_distilled_proof_term_nodes(
                            target_decl,
                            &shard.signature_text,
                        )
                        .unwrap_or_else(|| {
                            crate::matryoshka::estimate_decl_proof_term_nodes(
                                target_decl,
                                &shard.signature_text,
                                &shard.proof_text,
                            )
                        });
                    }

                    if !used_constants.is_empty() {
                        crate::accelerators::record_distilled_constants(
                            target_decl,
                            &shard.signature_text,
                            &used_constants,
                        );
                    }
                }};
            }

            macro_rules! apply_zygote_reply {
                ($reply:expr) => {{
                    let rep = $reply;
                    verified_via_zygote = true;
                    zygote_env_cache_hit = rep.env_cache_hit;
                    zygote_import_us = rep.import_us;
                    zygote_elab_us = rep.elab_us;
                    heartbeats_used = rep.heartbeats;
                    proof_term_nodes = rep.proof_term_nodes;
                    rss_delta_mb = rep.rss_delta_mb;
                    peak_rss_mb = peak_rss_mb.max(rep.peak_rss_mb);
                    if !rep.used_constants.is_empty() {
                        crate::accelerators::record_distilled_constants(
                            target_decl,
                            &shard.signature_text,
                            &rep.used_constants,
                        );
                    }
                    if rep.proof_term_nodes > 0 {
                        crate::accelerators::record_distilled_proof_term_nodes(
                            canon_dir,
                            target_decl,
                            &shard.signature_text,
                            rep.proof_term_nodes,
                        );
                    }
                    used_constants = rep.used_constants;
                }};
            }

            if !verified_via_zygote {
                if let Some(ref fsrc) = fast_olean_src {
                    if let Some(zjson) = try_zygote_src(fsrc, &env_vars, false) {
                        verified_via_fast_olean = true;
                        apply_zygote_json!(&zjson);
                    }
                }
            }

            if !verified_via_zygote && fast_olean_src.is_none() {
                if let Some(outline_plan) = splitter::build_prefix_outline_plan_with_split(
                    &active_src,
                    split,
                    &rooted_target,
                ) {
                    if env_vars.len() <= 1 {
                        let (ev, ech) = resolve_lake_env(store, canon_dir)?;
                        lean_bin = resolve_lean_bin(canon_dir)?;
                        env_vars = ev;
                        env_cache_hit = ech;
                    }
                    let orig_display = file.display().to_string();
                    if let Ok((outline_dir, outline_mod)) =
                        crate::zygote::ensure_prefix_outline_olean(
                            store,
                            toolchain,
                            &local_lean_path,
                            &env_vars,
                            Path::new(&lean_bin),
                            &outline_plan.outline_source,
                            &orig_display,
                            &file_lean_args,
                        )
                    {
                        let delta_lp = if local_lean_path.is_empty() {
                            outline_dir.to_string_lossy().into_owned()
                        } else {
                            format!("{}:{}", outline_dir.display(), local_lean_path)
                        };
                        let delta_src = outline_plan.render_delta_shard_source(&outline_mod);
                        let mut delta_ev = env_vars.clone();
                        delta_ev.insert("LEAN_PATH".to_string(), delta_lp.clone());
                        let mut stub_targets: Vec<String> = single_set.iter().cloned().collect();
                        stub_targets.sort();
                        if let Ok(reply) =
                            crate::zygote::eval_with_zygote_pool_for_targets_and_stubs(
                                store,
                                toolchain,
                                &delta_lp,
                                &delta_ev,
                                Path::new(&lean_bin),
                                &delta_src,
                                &stub_targets,
                                &outline_plan.outline_stubs,
                                Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                                &file_lean_args,
                            )
                        {
                            let c_abi_sound = unsafe {
                                crate::splitter::turbo_spec_is_sound_decl_summary(
                                    0,
                                    0,
                                    0,
                                    if reply.ok { 0 } else { 1 },
                                ) != 0
                            };
                            if reply.import_ok
                                && reply.ok
                                && !reply.crashed
                                && !reply.timed_out
                                && c_abi_sound
                                && crate::zygote::verify_attested_decl_types(
                                    &reply.decl_types,
                                    &expected_type_pair,
                                )
                                .is_ok()
                            {
                                verified_via_fast_olean = true;
                                apply_zygote_reply!(reply);
                            }
                        }
                    }
                }
            }

            if !verified_via_zygote && env_vars.is_empty() && fast_local_zygote_url.is_none() {
                let (ev, ech) = resolve_lake_env(store, canon_dir)?;
                lean_bin = resolve_lean_bin(canon_dir)?;
                env_vars = ev;
                env_cache_hit = ech;
            }

            if !verified_via_zygote && !verified_via_fast_olean {
                let full_shard_src = cone_src.clone();
                if !verified_via_zygote {
                    if let Some(zjson) = try_zygote_src(&full_shard_src, &env_vars, true) {
                        apply_zygote_json!(&zjson);
                    }
                }
                if !verified_via_zygote
                    && last_daemon_verify_err.is_none()
                    && !decl_src.is_empty()
                    && !shard.signature_text.is_empty()
                    && !shard.proof_text.is_empty()
                    && !decl_src.contains("sorry")
                    && !decl_src.contains("admit")
                {
                    if let Some(pos) = full_shard_src.rfind(&decl_src) {
                        let prefix_src = full_shard_src[..pos].to_string();
                        let closing_suffix = full_shard_src[pos + decl_src.len()..].to_string();
                        let accel_cfg =
                            crate::accelerators::AcceleratorConfig::load(Some(canon_dir));
                        if accel_cfg.enabled {
                            let registry =
                                crate::accelerators::AcceleratorRegistry::from_config(accel_cfg);
                            let (imports_csv, _) =
                                crate::zygote::split_shard_for_zygote(&full_shard_src);
                            let accel_input = crate::accelerators::AcceleratorInput {
                                decl_name: shard.name.clone(),
                                stmt_src: shard.signature_text.clone(),
                                body_src: shard.proof_text.clone(),
                                imports_csv,
                                available_constants:
                                    crate::accelerators::lookup_distilled_constants(
                                        target_decl,
                                        &shard.signature_text,
                                    ),
                                budget_ms: 25,
                            };
                            let certs = registry.run_all(&accel_input);
                            let mut cand_decls: Vec<String> = Vec::new();
                            let mut cand_accels: Vec<String> = Vec::new();
                            for cert in certs {
                                if let crate::accelerators::AcceleratorCertificate::RewrittenProof {
                                    new_body_src,
                                    accelerator_name,
                                    ..
                                } = cert
                                {
                                    let clean_body = new_body_src
                                        .trim()
                                        .strip_prefix(":=")
                                        .map(str::trim_start)
                                        .unwrap_or_else(|| new_body_src.trim());
                                    let rewritten_decl = if closing_suffix.trim().is_empty() {
                                        format!(
                                            "{} := {}",
                                            shard.signature_text.trim_end(),
                                            clean_body
                                        )
                                    } else {
                                        format!(
                                            "{} := {}\n{}",
                                            shard.signature_text.trim_end(),
                                            clean_body,
                                            closing_suffix.trim_start()
                                        )
                                    };
                                    if !cand_decls.contains(&rewritten_decl) {
                                        cand_decls.push(rewritten_decl);
                                        cand_accels.push(accelerator_name);
                                    }
                                }
                            }
                            if !cand_decls.is_empty() {
                                if env_vars.len() <= 1 {
                                    let (ev, ech) = resolve_lake_env(store, canon_dir)?;
                                    lean_bin = resolve_lean_bin(canon_dir)?;
                                    env_vars = ev;
                                    env_cache_hit = ech;
                                }
                                let orig_full = if closing_suffix.trim().is_empty() {
                                    decl_src.clone()
                                } else {
                                    format!("{}\n{}", decl_src, closing_suffix.trim_start())
                                };
                                if !cand_decls.contains(&orig_full) {
                                    cand_decls.push(orig_full);
                                    cand_accels.push("original".to_string());
                                }
                                if let Ok(reply) = crate::zygote::eval_candidates_race_via_zygote(
                                    store,
                                    toolchain,
                                    &local_lean_path,
                                    &env_vars,
                                    Path::new(&lean_bin),
                                    &prefix_src,
                                    &cand_decls,
                                    &file_lean_args,
                                ) {
                                    let c_abi_sound = unsafe {
                                        crate::splitter::turbo_spec_is_sound_decl_summary(
                                            0,
                                            0,
                                            0,
                                            if reply.ok { 0 } else { 1 },
                                        ) != 0
                                    };
                                    if reply.import_ok
                                        && reply.ok
                                        && c_abi_sound
                                        && crate::zygote::verify_attested_decl_types(
                                            &reply.decl_types,
                                            &expected_type_pair,
                                        )
                                        .is_ok()
                                    {
                                        if let Some(win_idx) = reply.winning_candidate_idx {
                                            if let Some(acc_name) = cand_accels.get(win_idx) {
                                                accelerator_assisted = true;
                                                winning_accelerator = Some(acc_name.clone());
                                            }
                                        }
                                        apply_zygote_reply!(reply);
                                    } else if reply.import_ok
                                        && !reply.ok
                                        && !reply.errors.is_empty()
                                    {
                                        last_daemon_verify_err = Some(reply.errors.join("\n"));
                                    }
                                }
                            }
                        }
                    }
                }
                if !verified_via_zygote {
                    if let Some(daemon_err) = last_daemon_verify_err.take() {
                        let orig_display = file.display().to_string();
                        let raw_err = daemon_err
                            .replace("<zygote-decl>", &orig_display)
                            .replace("<zygote-shard>", &orig_display);
                        let m_diags = extract_mismatch_diagnostics(&raw_err);
                        let m_suffix = format_mismatch_diagnostics_summary(&m_diags);
                        let h_suffix = maybe_append_hotspot_diagnostics_for_source(
                            store,
                            toolchain,
                            &local_lean_path,
                            &env_vars,
                            Path::new(&lean_bin),
                            &full_shard_src,
                            Some(&orig_display),
                            &file_lean_args,
                            &raw_err,
                        );
                        anyhow::bail!(
                            "lean check failed for `{}` in {} (lines {}..={}):\n{}{}{}",
                            target_decl,
                            file.display(),
                            shard.start_line,
                            shard.end_line,
                            raw_err,
                            m_suffix,
                            h_suffix
                        );
                    }
                    if env_vars.len() <= 1 {
                        let (ev, ech) = resolve_lake_env(store, canon_dir)?;
                        lean_bin = resolve_lean_bin(canon_dir)?;
                        env_vars = ev;
                        env_cache_hit = ech;
                    }
                    let mut stub_targets: Vec<String> = single_set.iter().cloned().collect();
                    stub_targets.sort();
                    let reply = crate::zygote::eval_with_zygote_pool_for_targets(
                        store,
                        toolchain,
                        &local_lean_path,
                        &env_vars,
                        Path::new(&lean_bin),
                        &full_shard_src,
                        &stub_targets,
                        Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                        &file_lean_args,
                    )
                    .with_context(|| {
                        format!(
                            "Zygote check failed for `{}` in {} (lines {}..={})",
                            target_decl,
                            file.display(),
                            shard.start_line,
                            shard.end_line
                        )
                    })?;
                    let c_abi_sound = unsafe {
                        crate::splitter::turbo_spec_is_sound_decl_summary(
                            0,
                            0,
                            0,
                            if reply.ok { 0 } else { 1 },
                        ) != 0
                    };
                    if reply.import_ok
                        && reply.ok
                        && !reply.crashed
                        && !reply.timed_out
                        && c_abi_sound
                    {
                        crate::zygote::verify_attested_decl_types(
                            &reply.decl_types,
                            &expected_type_pair,
                        )?;
                        apply_zygote_reply!(reply);
                    } else if reply.crashed || reply.timed_out || reply.import_ok {
                        let orig_display = file.display().to_string();
                        let raw_err = reply
                            .errors
                            .join("\n")
                            .replace("<zygote-decl>", &orig_display)
                            .replace("<zygote-shard>", &orig_display);
                        let m_diags = extract_mismatch_diagnostics(&raw_err);
                        let m_suffix = format_mismatch_diagnostics_summary(&m_diags);
                        let h_fmt = crate::zygote::format_hotspot_diagnostics(
                            &reply.timeout_hotspots,
                            &reply.simp_hotspots,
                        );
                        let h_suffix = if h_fmt.is_empty() {
                            String::new()
                        } else {
                            format!("\n{h_fmt}")
                        };
                        anyhow::bail!(
                            "lean check failed for `{}` in {} (lines {}..={}):\n{}{}{}",
                            target_decl,
                            file.display(),
                            shard.start_line,
                            shard.end_line,
                            raw_err,
                            m_suffix,
                            h_suffix
                        );
                    }
                }
                if !verified_via_zygote {
                    let default_stack = env_vars
                        .get("LEAN_STACK_SIZE_KB")
                        .cloned()
                        .or_else(|| std::env::var("LEAN_STACK_SIZE_KB").ok())
                        .unwrap_or_else(|| "262144".to_string());
                    let mut fallback_env = env_vars.clone();
                    fallback_env.insert("LEAN_STACK_SIZE_KB".to_string(), default_stack);
                    let out = crate::zygote::run_audited_lean_shard_with_types(
                        store,
                        Path::new(&lean_bin),
                        &fallback_env,
                        Some(canon_dir),
                        &full_shard_src,
                        &single_set,
                        &expected_type_pair,
                        &file_lean_args,
                        Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                    )
                    .with_context(|| {
                        format!(
                            "Shard check failed for `{}` in {} (lines {}..={})",
                            target_decl,
                            file.display(),
                            shard.start_line,
                            shard.end_line
                        )
                    })?;

                    if !out.status.success() {
                        let orig_display = file.display().to_string();
                        let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
                        let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
                        let combined_err = format!("{}\n{}", stdout, stderr);
                        let m_diags = extract_mismatch_diagnostics(&combined_err);
                        let m_suffix = format_mismatch_diagnostics_summary(&m_diags);
                        let h_suffix = maybe_append_hotspot_diagnostics_for_source(
                            store,
                            toolchain,
                            &local_lean_path,
                            &fallback_env,
                            Path::new(&lean_bin),
                            &full_shard_src,
                            Some(&orig_display),
                            &file_lean_args,
                            &combined_err,
                        );
                        anyhow::bail!(
                            "Shard check failed for `{}` in {} (lines {}..={}):\n{}{}{}",
                            target_decl,
                            orig_display,
                            shard.start_line,
                            shard.end_line,
                            combined_err,
                            m_suffix,
                            h_suffix
                        );
                    }
                }
            }

            if proof_term_nodes == 0 {
                proof_term_nodes = crate::accelerators::lookup_distilled_proof_term_nodes(
                    target_decl,
                    &shard.signature_text,
                )
                .unwrap_or_else(|| {
                    crate::matryoshka::estimate_decl_proof_term_nodes(
                        target_decl,
                        &shard.signature_text,
                        &shard.proof_text,
                    )
                });
            }

            if !used_constants.is_empty() {
                crate::accelerators::record_distilled_constants(
                    target_decl,
                    &shard.signature_text,
                    &used_constants,
                );
                if shard.name != target_decl {
                    crate::accelerators::record_distilled_constants(
                        &shard.name,
                        &shard.signature_text,
                        &used_constants,
                    );
                }
            } else if shard.proof_text.contains("simp") && !shard.proof_text.contains("simp only") {
                let cached_distilled = crate::accelerators::lookup_distilled_constants(
                    target_decl,
                    &shard.signature_text,
                );
                if !cached_distilled.is_empty() {
                    used_constants = cached_distilled;
                }
            }

            let dur_ms = t0.elapsed().as_millis() as i64;
            let distilled_non_core: Vec<String> = used_constants
                .iter()
                .filter(|c| !crate::accelerators::is_excluded_core_constant(c))
                .cloned()
                .collect();
            let distilled_list = if !distilled_non_core.is_empty() {
                &distilled_non_core
            } else {
                &used_constants
            };
            let has_distilled_hint = !distilled_list.is_empty()
                && shard.proof_text.contains("simp")
                && !shard.proof_text.contains("simp only");
            let compact_summary = if has_distilled_hint {
                format!(
                    "OK decl={} ms={} hbs={} hint=simp only [{}]",
                    target_decl,
                    dur_ms,
                    heartbeats_used,
                    distilled_list.join(", ")
                )
            } else {
                format!(
                    "OK decl={} ms={} hbs={} stage={}",
                    target_decl,
                    dur_ms,
                    heartbeats_used,
                    if verified_via_zygote {
                        "zygote"
                    } else {
                        "lean"
                    }
                )
            };
            let stmt_feats =
                crate::matryoshka::parse_lean_stmt_features(target_decl, &shard.signature_text);
            let tactic_skeleton = crate::matryoshka::extract_tactic_skeleton(&shard.proof_text);
            let emitted_used_constants = used_constants.clone();
            let mut out_json = serde_json::json!({
                "status": "theorem_verified",
                "decl": target_decl,
                "shard_key": shard_key,
                "lake_env_cache_hit": env_cache_hit,
                "fast_olean_import": verified_via_fast_olean,
                "zygote_used": verified_via_zygote,
                "zygote_env_cache_hit": zygote_env_cache_hit,
                "zygote_import_us": zygote_import_us,
                "zygote_elab_us": zygote_elab_us,
                "heartbeats_used": heartbeats_used,
                "proof_term_nodes": proof_term_nodes,
                "used_constants": emitted_used_constants,
                "stmt_nodes": stmt_feats.stmt_nodes,
                "stmt_depth": stmt_feats.stmt_depth,
                "num_binders": stmt_feats.num_binders,
                "goal_head": stmt_feats.goal_head,
                "stmt_consts": stmt_feats.stmt_consts,
                "tactic_skeleton": tactic_skeleton,
                "rss_delta_mb": rss_delta_mb,
                "peak_rss_mb": peak_rss_mb,
                "accelerator_assisted": accelerator_assisted,
                "winning_accelerator": winning_accelerator,
                "fission_cached_subshards": fission_cached_subshards,
                "fission_verified_subshards": fission_verified_subshards,
                "interface_hash": split.interface_hash,
                "prefix_env_hash": shard.prefix_env_hash,
                "total_shards_in_file": split.shards.len(),
                "compact_summary": compact_summary,
                "estimated_tokens": 18,
                "elapsed_ms": dur_ms
            });
            if has_distilled_hint {
                if let Some(obj) = out_json.as_object_mut() {
                    obj.insert(
                        "distilled_simp_hint".to_string(),
                        serde_json::Value::String(format!(
                            "simp only [{}]",
                            distilled_list.join(", ")
                        )),
                    );
                }
            }
            insert_allow_sorry_fields(&mut out_json, allow_sorry, false, &[]);
            kernel_prov.insert_json_fields(&mut out_json);
            if inflight_tx_open {
                store.commit_inflight_publish_for_lease(&lease.action_key)?;
            } else {
                let receipt = make_attested_shard_receipt_bytes(
                    target_decl,
                    &shard.prefix_env_hash,
                    &shard.stmt_hash,
                    &shard.proof_hash,
                    db::now_unix(),
                    Some(&attested.kernel_type_hash),
                )?;
                store.publish_action_with_blob(
                    &lease,
                    &receipt,
                    "expr_shard",
                    &format!("thm:{}", target_decl),
                    dur_ms,
                    "trusted",
                )?;
            }
            drop(lease);

            if db_warm_on_open
                && fission_sub_shards.len() >= 2
                && fission_cached_subshards == 0
                && fission_verified_subshards == 0
            {
                let now = db::now_unix();
                let per_sub_dur = (dur_ms / (fission_sub_shards.len() as i64).max(1)).max(1);
                let mut seed_items = Vec::with_capacity(fission_sub_shards.len());
                for sub in &fission_sub_shards {
                    let f_key = compute_fission_store_key_with_args(
                        toolchain,
                        &shard.prefix_env_hash,
                        &sub.sub_shard_key,
                        &file_lean_args,
                    );
                    let sub_hash = blake3::hash(sub.sub_decl_source.as_bytes())
                        .to_hex()
                        .to_string();
                    let sub_receipt = serde_json::to_vec(&serde_json::json!({
                        "decl": sub.step_label,
                        "parent_decl": target_decl,
                        "sub_shard_key": sub.sub_shard_key,
                        "prefix_env_hash": shard.prefix_env_hash,
                        "stmt_hash": sub_hash,
                        "proof_hash": sub_hash,
                        "seeded_from_full_decl": true,
                        "verified_at": now,
                        "scanner_version": crate::zygote::ZYGOTE_SCANNER_VERSION,
                        "replay_version": crate::zygote::ZYGOTE_REPLAY_VERSION,
                    }))?;
                    seed_items.push((f_key, sub.step_label.clone(), sub_receipt, per_sub_dur));
                }
                store.batch_put_theorem_shards(toolchain, &seed_items)?;
            }
            if emit_stdout {
                if json_output {
                    println!("{}", serde_json::to_string_pretty(&out_json)?);
                } else {
                    println!(
                        "[turbo-lean] SHARD VERIFIED `{}` ({}/{} shards in file, env_cache_hit={}, fast_olean={}, zygote={}, interface_hash={}.., {} ms)",
                        target_decl,
                        1,
                        split.shards.len(),
                        env_cache_hit,
                        verified_via_fast_olean,
                        verified_via_zygote,
                        &split.interface_hash[..12],
                        dur_ms
                    );
                }
            }
            if remote_http.is_none()
                && fast_local_zygote_url.is_none()
                && !crate::zygote::daemon_disabled()
            {
                let ev = if !env_vars.is_empty() {
                    env_vars
                } else if fast_lib_dir.exists() || has_pkg_lib_dir {
                    let mut fast_ev = HashMap::new();
                    fast_ev.insert(
                        "LEAN_PATH".to_string(),
                        resolve_remote_lean_path(canon_dir, None),
                    );
                    fast_ev
                } else {
                    resolve_lake_env(store, canon_dir)
                        .map(|(m, _)| m)
                        .unwrap_or_default()
                };
                pack::warm_local_zygote_daemon_nonblocking(store, &ev);
            }
            Ok(out_json)
        }
    }
}
