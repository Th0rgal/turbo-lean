use super::*;
use crate::check::identity::{
    confirm_decl_identity_with_extra_dirs, match_expected_decl_identity, OleanDeclEntry,
};
use crate::check::single_decl::extract_decl_source_from_file;
use crate::lake_build::{
    compute_shard_key, compute_shard_key_with_args, resolve_lean_bin, resolve_remote_lean_path,
};
use crate::pack;
use std::collections::HashSet;

#[test]
fn declaration_identity_rejects_mislabeled_shards_and_unavailable_elaboration() {
    let dir = std::env::temp_dir().join(format!(
        "turbo_identity_guard_{}",
        crate::pack::next_tmp_id()
    ));
    fs::create_dir_all(&dir).unwrap();
    fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
    let file = dir.join("Identity.lean");
    let src = "namespace A\ntheorem same : True := True.intro\nend A\nnamespace B\ntheorem same (n : Nat) : n = n + 1 := by rfl\nend B\n";
    let split = split_lean_source(src, &[]);
    let mut shard = split.shards[1].clone();
    confirm_decl_identity(src, &shard, &dir, &file).unwrap();
    shard.qualified_name = "A.same".into();
    let error = format!(
        "{:#}",
        confirm_decl_identity(src, &shard, &dir, &file).unwrap_err()
    );
    assert!(error.contains("identity unconfirmed"), "{error}");
    assert!(error.contains("B.same"), "{error}");
    let invalid = "namespace B\ndef broken : Nat := noSuchConstant\ntheorem same : True := True.intro\nend B\n";
    let split = split_lean_source(invalid, &[]);
    assert!(confirm_decl_identity(invalid, &split.shards[0], &dir, &file).is_err());
    // The checked source controls the compiler's stdout and exit code: forging the old
    // marker and exiting 0 before any `.olean` exists must not confirm an identity.
    let spoof = "import Lean\nopen Lean Elab Command in\nrun_cmd do\n  let f ← getFileName\n  IO.println s!\"TURBO_IDENTITY_0 A.same {f}\"\n  (IO.Process.exit 0 : IO Unit)\nnamespace A\ntheorem same : True := True.intro\nend A\n";
    // Dynamic namespaces are invisible to the splitter, which labels this `A.same`;
    // Lean declares `B.A.same`.
    let dynamic = "import Lean\nrun_cmd Lean.Elab.Command.elabCommand (← `(namespace $(Lean.mkIdent `B)))\ntheorem A.same (n : Nat) : n = n + 1 := by rfl\n";
    for src in [spoof, dynamic] {
        let split = split_lean_source(src, &[]);
        let shard = &split.shards[0];
        assert_eq!(shard.decl_name(), "A.same");
        let error = format!(
            "{:#}",
            confirm_decl_identity(src, shard, &dir, &file).unwrap_err()
        );
        assert!(error.contains("identity unconfirmed"), "{error}");
        let reason = if src == spoof {
            "produced no `.olean`"
        } else {
            "declares [\"B.A.same\"]"
        };
        assert!(error.contains(reason), "{error}");
    }
    assert!(fs::read_dir(&dir).unwrap().all(|e| !e
        .unwrap()
        .file_name()
        .to_string_lossy()
        .contains("identity")));
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn identity_probe_scratch_never_reuses_existing_entries() {
    let base = std::env::temp_dir().join(format!("turbo_scratch_{}", crate::pack::next_tmp_id()));
    fs::create_dir_all(&base).unwrap();
    // A colliding nonce must fail instead of adopting or clearing someone else's dir.
    let taken = base.join("turbo_identity_collide");
    fs::create_dir(&taken).unwrap();
    fs::write(taken.join("keep.lean"), "victim").unwrap();
    assert!(
        PrivateScratchDir::create_with_nonce(&base, "turbo_identity", "collide".into()).is_err()
    );
    assert_eq!(
        fs::read_to_string(taken.join("keep.lean")).unwrap(),
        "victim"
    );
    #[cfg(unix)]
    {
        std::os::unix::fs::symlink(&taken, base.join("turbo_identity_link")).unwrap();
        assert!(
            PrivateScratchDir::create_with_nonce(&base, "turbo_identity", "link".into()).is_err()
        );
        std::os::unix::fs::symlink(taken.join("keep.lean"), base.join("probe.lean")).unwrap();
        assert!(create_private_file(&base.join("probe.lean"), b"clobber").is_err());
    }
    // Neither an existing file nor a symlink to one is ever written through.
    assert!(create_private_file(&taken.join("keep.lean"), b"clobber").is_err());
    assert_eq!(
        fs::read_to_string(taken.join("keep.lean")).unwrap(),
        "victim"
    );
    let scratch = PrivateScratchDir::create(&base, "turbo_identity").unwrap();
    let path = scratch.path.clone();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        assert_eq!(
            fs::metadata(&path).unwrap().permissions().mode() & 0o777,
            0o700
        );
    }
    create_private_file(&path.join("probe.lean"), b"ok").unwrap();
    scratch.remove().unwrap();
    assert!(!path.exists());
    fs::remove_dir_all(base).unwrap();
}

#[test]
fn test_extract_mismatch_diagnostics_parses_rhs_and_numeric_delta() {
    let sample_err = "\
<zygote-decl>:42:4: error: type mismatch
  h_pc_step
has type
  sym_78.pc = 1138 : Prop
but is expected to have type
  sym_78.pc = 1152 : Prop
";
    let diags = extract_mismatch_diagnostics(sample_err);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0]["term"], "h_pc_step");
    assert_eq!(diags[0]["inferred_rhs"], "1138");
    assert_eq!(diags[0]["expected_rhs"], "1152");
    assert_eq!(diags[0]["numeric_delta"], 14);
}

#[test]
fn test_verify_subshards_out_of_core_disk_checkpoint_resume() {
    let tmp_dir = std::env::temp_dir().join(format!(
        "turbo_ooc_subshards_test_{}",
        crate::pack::next_tmp_id()
    ));
    let _ = fs::remove_dir_all(&tmp_dir);
    fs::create_dir_all(&tmp_dir).unwrap();
    let mut store = TurboStore::open(Some(&tmp_dir)).unwrap();
    let toolchain = "leanprover/lean4:v4.35.0";
    let (env_vars, lean_bin) =
        crate::pack::resolve_server_lean_env_and_bin(&store, toolchain, "").unwrap();
    if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
        let _ = fs::remove_dir_all(&tmp_dir);
        return;
    }
    // Worker compilation is fixture setup, before any request deadline starts.
    crate::zygote::ensure_zygote_binary(&store, &lean_bin, &env_vars).unwrap();

    let prefix_src = "namespace OutOfCoreFission\ndef doubleNat (n : Nat) : Nat := n + n\n";
    let step0 = (
        "cut_step_0".to_string(),
        "ooc_subshard_key_step_0".to_string(),
        "theorem cut_step_0 (n : Nat) : doubleNat n = n + n := rfl\n".to_string(),
    );
    let step1 = (
        "cut_step_1".to_string(),
        "ooc_subshard_key_step_1".to_string(),
        "theorem cut_step_1 : doubleNat 3 = 6 := rfl\n".to_string(),
    );
    let step2 = (
        "cut_step_2".to_string(),
        "ooc_subshard_key_step_2".to_string(),
        "theorem cut_step_2 (a : Nat) : doubleNat a + 0 = a + a := by\n  simp [doubleNat]\n"
            .to_string(),
    );

    let (hits1, verified1) = verify_subshards_out_of_core(
        &mut store,
        toolchain,
        "",
        &env_vars,
        &lean_bin,
        prefix_src,
        &[step0.clone(), step1.clone()],
    )
    .unwrap();
    assert_eq!((hits1, verified1), (0, 2));
    assert!(
        store.has_theorem_shard(&step0.1)
            && store.has_theorem_shard(&step1.1)
            && !store.has_theorem_shard(&step2.1)
    );

    let (hits2, verified2) = verify_subshards_out_of_core(
        &mut store,
        toolchain,
        "",
        &env_vars,
        &lean_bin,
        prefix_src,
        &[step0, step1, step2.clone()],
    )
    .unwrap();
    assert_eq!((hits2, verified2), (2, 1));
    assert!(store.has_theorem_shard(&step2.1));
    let _ = fs::remove_dir_all(&tmp_dir);
}

#[test]
fn test_closed_loop_fission_plan_incremental_edit_skips_unchanged_have_cuts() {
    let tmp_dir = std::env::temp_dir().join(format!(
        "turbo_closed_loop_fission_test_{}",
        crate::pack::next_tmp_id()
    ));
    let _ = fs::remove_dir_all(&tmp_dir);
    let (store_dir, proj_dir) = (tmp_dir.join("store"), tmp_dir.join("proj"));
    fs::create_dir_all(&store_dir).unwrap();
    fs::create_dir_all(&proj_dir).unwrap();

    let toolchain = "leanprover/lean4:v4.35.0";
    fs::write(proj_dir.join("lean-toolchain"), format!("{}\n", toolchain)).unwrap();
    let mut store = TurboStore::open(Some(&store_dir)).unwrap();
    let (env_vars, lean_bin) =
        crate::pack::resolve_server_lean_env_and_bin(&store, toolchain, "").unwrap();
    if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
        let _ = fs::remove_dir_all(&tmp_dir);
        return;
    }
    // Worker compilation is fixture setup, before any request deadline starts.
    crate::zygote::ensure_zygote_binary(&store, &lean_bin, &env_vars).unwrap();

    let lean_file = proj_dir.join("FissionLoopTest.lean");
    let canon_proj = proj_dir.canonicalize().unwrap_or_else(|_| proj_dir.clone());
    let src_v1 = "def stepA (n : Nat) : Nat := n + 1\ndef stepB (n : Nat) : Nat := n + 2\ntheorem multi_step_thm (a b : Nat) : (a + 1) + (b + 2) = a + b + 3 := by\n  have h1 : a + 1 = 1 + a := by\n    omega\n  have h2 : b + 2 = 2 + b := by\n    omega\n  have h3 : (1 + a) + (2 + b) = a + b + 3 := by\n    omega\n  omega\n";
    fs::write(&lean_file, src_v1).unwrap();
    let canon_file = lean_file
        .canonicalize()
        .unwrap_or_else(|_| lean_file.clone());

    let test_kp = crate::kernel::resolve_kernel_engine(
        crate::kernel::KernelEngineSelection::Standard,
        toolchain,
    )
    .unwrap();
    let run_decl = |st: &mut TurboStore, src: &str| {
        fs::write(&lean_file, src).unwrap();
        let mut split = split_lean_source(src, &[]);
        let mut cb3 = None;
        let t0 = Instant::now();
        let res = check_single_decl(
            st,
            true,
            false,
            false,
            &test_kp,
            &t0,
            &lean_file,
            &lean_file,
            &canon_file,
            &canon_proj,
            toolchain,
            "multi_step_thm",
            src.to_string(),
            &mut cb3,
            &mut split,
            true,
            0,
            None,
            false,
        );
        (res, split)
    };

    let (res_v1, split_v1) = run_decl(&mut store, src_v1);
    assert_eq!(res_v1.unwrap()["status"], "theorem_verified");
    let shard_v1 = &split_v1.shards[0];
    let subs_v1 = splitter::fission_theorem_have_blocks(
        &extract_decl_source_from_file(src_v1, shard_v1),
        "multi_step_thm",
    );
    assert_eq!(subs_v1.len(), 4);
    for sub in &subs_v1 {
        assert!(store.has_theorem_shard(&compute_fission_store_key(
            toolchain,
            &shard_v1.prefix_env_hash,
            &sub.sub_shard_key
        )));
    }

    let src_v2 = src_v1.replacen(
        "    omega\n  omega\n",
        "    omega\n  rw [h1, h2]\n  exact h3\n",
        1,
    );
    let (res_v2, _) = run_decl(&mut store, &src_v2);
    let res_v2 = res_v2.unwrap();
    assert_eq!(
        (
            res_v2["status"].as_str(),
            res_v2["fission_cached_subshards"].as_i64(),
            res_v2["fission_verified_subshards"].as_i64(),
            res_v2["winning_accelerator"].as_str()
        ),
        (
            Some("theorem_verified"),
            Some(3),
            Some(1),
            Some("builtin:cut-fission")
        )
    );

    let src_v3 = src_v1.replacen(
        "    omega\n  omega\n",
        "    omega\n  exact nonexistent_lemma_xyz\n",
        1,
    );
    assert!(run_decl(&mut store, &src_v3).0.is_err());
    let _ = fs::remove_dir_all(&tmp_dir);
}

#[test]
fn test_batch_fission_ipc_verifies_multiple_have_cuts_in_single_roundtrip() {
    let tmp_dir = std::env::temp_dir().join(format!(
        "turbo_batch_fission_ipc_test_{}",
        crate::pack::next_tmp_id()
    ));
    let _ = fs::remove_dir_all(&tmp_dir);
    fs::create_dir_all(&tmp_dir).unwrap();
    let store = TurboStore::open(Some(&tmp_dir)).unwrap();
    let toolchain = "leanprover/lean4:v4.35.0";
    let (env_vars, lean_bin) =
        crate::pack::resolve_server_lean_env_and_bin(&store, toolchain, "").unwrap();
    if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
        let _ = fs::remove_dir_all(&tmp_dir);
        return;
    }
    // Worker compilation is fixture setup, before any request deadline starts.
    crate::zygote::ensure_zygote_binary(&store, &lean_bin, &env_vars).unwrap();

    let prefix_src = "def incNat (n : Nat) : Nat := n + 1\n";
    let thm_decl = "theorem batch_cut_thm (a b : Nat) : incNat a + incNat b = a + b + 2 := by\n  have h1 : incNat a = a + 1 := by\n    rfl\n  have h2 : incNat b = b + 1 := by\n    rfl\n  omega\n";
    let sub_decl_sources: Vec<String> =
        splitter::fission_theorem_have_blocks(thm_decl, "batch_cut_thm")
            .into_iter()
            .map(|s| s.sub_decl_source)
            .collect();
    assert_eq!(sub_decl_sources.len(), 3);

    let reply = crate::zygote::eval_subshards_batch_via_zygote(
        &store,
        toolchain,
        "",
        &env_vars,
        &lean_bin,
        prefix_src,
        &sub_decl_sources,
        &[],
    )
    .unwrap();
    assert!(reply.import_ok && reply.ok && reply.subshards_verified == 3);

    let mut bad_sub_decl_sources = sub_decl_sources;
    bad_sub_decl_sources[1] =
        "theorem _fission_cut_1 (a b : Nat) : incNat b = b + 999 := sorry\n".to_string();
    let bad_reply = crate::zygote::eval_subshards_batch_via_zygote(
        &store,
        toolchain,
        "",
        &env_vars,
        &lean_bin,
        prefix_src,
        &bad_sub_decl_sources,
        &[],
    )
    .unwrap();
    assert!(!bad_reply.ok && bad_reply.subshards_verified == 1);
    let _ = fs::remove_dir_all(&tmp_dir);
}

#[test]
fn test_race_candidates_single_roundtrip_speculative_tactic_replay() {
    let tmp_dir = std::env::temp_dir().join(format!(
        "turbo_race_candidates_test_{}",
        crate::pack::next_tmp_id()
    ));
    let _ = fs::remove_dir_all(&tmp_dir);
    fs::create_dir_all(&tmp_dir).unwrap();
    let store = TurboStore::open(Some(&tmp_dir)).unwrap();
    let toolchain = "leanprover/lean4:v4.35.0";
    let (env_vars, lean_bin) =
        crate::pack::resolve_server_lean_env_and_bin(&store, toolchain, "").unwrap();
    if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
        let _ = fs::remove_dir_all(&tmp_dir);
        return;
    }
    // Worker compilation is fixture setup, before any request deadline starts.
    crate::zygote::ensure_zygote_binary(&store, &lean_bin, &env_vars).unwrap();

    let candidates: Vec<String> = [
        "theorem race_thm (a b : Nat) : a + b = b + a := rfl\n",
        "theorem race_thm (a b : Nat) : a + b = b + a := sorry\n",
        "theorem race_thm (a b : Nat) : a + b = b + a := by omega\n",
        "theorem race_thm (a b : Nat) : a + b = b + a := by simp [Nat.add_comm]\n",
    ]
    .into_iter()
    .map(String::from)
    .collect();

    let reply = crate::zygote::eval_candidates_race_via_zygote(
        &store,
        toolchain,
        "",
        &env_vars,
        &lean_bin,
        "def stepAdd (n : Nat) : Nat := n + 1\n",
        &candidates,
        &[],
    )
    .unwrap();
    assert!(reply.import_ok && reply.ok && matches!(reply.winning_candidate_idx, Some(2 | 3)));
    let _ = fs::remove_dir_all(&tmp_dir);
}

#[test]
fn test_law15_c_abi_routing_and_prng_exports() {
    use crate::cluster::*;

    unsafe {
        assert_eq!(turbo_spec_node_effective_cost(0, 0, 420, 1), 420);
        assert_eq!(
            turbo_spec_node_effective_cost(1500, 3, 400, 2),
            1500 + (4 * 400) / 2
        );
        assert_eq!(turbo_spec_is_remote_eligible(0, 1, 1), 0);
        assert_eq!(turbo_spec_is_remote_eligible(2, 0, 1), 0);
        assert_eq!(turbo_spec_is_remote_eligible(2, 1, 1), 1);
        assert_eq!(turbo_spec_should_switch_route(420, 1800, 1), 0);
        assert_eq!(turbo_spec_should_switch_route(1800, 900, 1), 1);
        assert_eq!(turbo_spec_should_switch_route(1800, 900, 0), 0);
        assert_eq!(turbo_spec_classify_compute_target(1024, 1, 1, 1, 1), 0);
        assert_eq!(turbo_spec_classify_compute_target(65536, 0, 1, 1, 1), 2);
        assert_eq!(turbo_spec_classify_compute_target(65536, 1, 0, 1, 1), 1);
        assert_ne!(turbo_spec_splitmix64(1), turbo_spec_splitmix64(2));
        assert_eq!(turbo_spec_boundary_u256_limb(2, 0), u64::MAX);
        assert_eq!(turbo_spec_gen_u256_limb(2, 42, 0, 0), u64::MAX);
        assert_eq!(turbo_spec_u256_lt(1, 0, 0, 0, 2, 0, 0, 0), 1);
        assert_eq!(turbo_spec_u256_lt(5, 0, 0, 1, 9, 0, 0, 0), 0);
        assert_eq!(turbo_spec_eval_u64_binop(0, 10, 20), 30);
        assert_eq!(turbo_spec_eval_u64_binop(1, 5, 20), 0);
        assert_eq!(turbo_spec_step_verdict_consistent(1, 1), 1);
        assert_eq!(turbo_spec_step_verdict_consistent(1, 0), 0);
    }
}

#[test]
fn test_stage1_qualified_decl_selection_cli_and_stateful() {
    // Unit-test executables live in <profile>/deps; exercise the actual CLI too.
    let mut build = Command::new(env!("CARGO"));
    build
        .arg("build")
        .current_dir(concat!(env!("CARGO_MANIFEST_DIR"), "/../.."));
    if !cfg!(debug_assertions) {
        build.arg("--release");
    }
    assert!(build.status().unwrap().success());
    let binary = std::env::current_exe()
        .unwrap()
        .ancestors()
        .skip(1)
        .find_map(|d| {
            let p = d.join("turbo-lean");
            p.is_file().then_some(p)
        })
        .unwrap();
    let dir = std::env::temp_dir().join(format!(
        "turbo_stage1_selection_{}",
        crate::pack::next_tmp_id()
    ));
    fs::create_dir_all(&dir).unwrap();
    fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
    let file = dir.join("Selection.lean");
    let good = "namespace A\ntheorem same (n : Nat) : n = n := rfl\nend A\n";
    let bad = "namespace B\ntheorem same (n : Nat) : n = n + 1 := by rfl\nend B\n";
    let indented = format!("{good}{bad}")
        .lines()
        .map(|line| format!("  {line}\n"))
        .collect::<String>();
    let quoted = format!("def message := \"\nnamespace Literal\ntheorem same (n : Nat) : n = n + 1 := by rfl\nend Literal\n\"\n{good}{bad}");
    for (order, src) in [
            format!("{good}{bad}"),
            format!("{bad}{good}"),
            indented,
            quoted,
            "namespace B\ndef message : String := \"\nend B\nnamespace A\n\"\ntheorem same (n : Nat) : n = n + 1 := by rfl\nend B\n".to_string() + good,
        ]
        .iter()
        .enumerate()
        {
            fs::write(&file, src).unwrap();
            let cache = dir.join(format!("cache{order}"));
            let mut store = TurboStore::open(Some(&dir.join(format!("stateful{order}")))).unwrap();
            for target in ["A.same", "same", "B.same", "Other.A.same", "Literal.same"] {
                let stateful = crate::gpu_fastcheck::evaluate_agent_step_value(
                    &mut store,
                    &file,
                    Some(target),
                    Some(&dir),
                    false,
                    false,
                );
                match target {
                    "same" => assert!(stateful
                        .unwrap_err()
                        .to_string()
                        .contains("Ambiguous declaration")),
                    "Other.A.same" | "Literal.same" => assert!(stateful.is_err()),
                    _ => {
                        let value = stateful.unwrap();
                        assert_eq!(value["decl"], target);
                        assert_eq!(
                            value["status"],
                            if target == "A.same" {
                                "theorem_verified"
                            } else {
                                "counterexample_rejected"
                            }
                        );
                    }
                }
                for command in ["agent-step", "fast-check"] {
                    let mut cli = Command::new(&binary);
                    cli.current_dir(&dir)
                        .arg("--cache-dir")
                        .arg(&cache)
                        .args(["--json", command])
                        .arg(&file)
                        .args(["--decl", target]);
                    if command == "agent-step" {
                        cli.arg("--project-dir").arg(&dir);
                    }
                    let output = cli.output().unwrap();
                    let stderr = String::from_utf8_lossy(&output.stderr);
                    let stdout = String::from_utf8_lossy(&output.stdout);
                    if matches!(target, "same" | "Other.A.same" | "Literal.same") {
                        assert!(
                            !output.status.success(),
                            "{command} {target}: {stdout} {stderr}"
                        );
                        if target == "same" {
                            assert!(
                                stderr.contains("Ambiguous declaration")
                                    && stderr.contains("A.same")
                                    && stderr.contains("B.same"),
                                "{stderr}"
                            );
                        }
                        assert!(!stdout.contains("counterexample"), "{stdout}");
                        continue;
                    }
                    let value: serde_json::Value = serde_json::from_slice(&output.stdout)
                        .unwrap_or_else(|_| panic!("{command} {target}: {stdout} {stderr}"));
                    if command == "agent-step" {
                        assert!(output.status.success(), "{stderr}");
                        assert_eq!(value["decl"], target);
                        assert_eq!(
                            value["status"],
                            if target == "A.same" {
                                "theorem_verified"
                            } else {
                                "counterexample_rejected"
                            }
                        );
                    } else {
                        assert_eq!(value["decl_name"], target);
                        assert_eq!(value["verified"], target == "A.same");
                        assert_eq!(
                            value["status"],
                            if target == "A.same" {
                                "ok"
                            } else {
                                "counterexample_found"
                            }
                        );
                    }
                }
            }
        }
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn test_check_qualified_decl_rebuilds_legacy_stat_split() {
    let dir = std::env::temp_dir().join(format!(
        "turbo_legacy_qualified_split_{}",
        crate::pack::next_tmp_id()
    ));
    let proj = dir.join("proj");
    fs::create_dir_all(&proj).unwrap();
    fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
    let file = proj.join("Legacy.lean");
    // Checking A must succeed even though the later, same-spelled B theorem is invalid.
    let src = "namespace A\ntheorem same : True := True.intro\nend A\nnamespace B\ntheorem same : False := True.intro\nend B\n";
    fs::write(&file, src).unwrap();
    let mut store = TurboStore::open(Some(&dir.join("store"))).unwrap();
    let src_b3 = blake3::hash(src.as_bytes()).to_hex().to_string();
    let split = split_lean_source(src, &[]);
    let mut legacy = serde_json::to_value(ShmCachedFileSplit {
        src_blake3: src_b3.clone(),
        split_key: format!("file-split:v3:{}", src_b3),
        split: compact_split_for_shm_cache(&split),
        prefix_src: String::new(),
        known_modified: false,
        dep_hashes: Vec::new(),
    })
    .unwrap();
    for shard in legacy["split"]["shards"].as_array_mut().unwrap() {
        shard["name"] = serde_json::json!("same");
        shard.as_object_mut().unwrap().remove("qualified_name");
    }
    let canon_file = file.canonicalize().unwrap();
    let (ms, mn, sz) = TurboStore::extract_file_stat_tuple(&fs::metadata(&file).unwrap());
    let pk = canon_file.to_string_lossy();
    let hash_for_version = |version: &[u8]| {
        let mut hash = blake3::Hasher::new();
        hash.update(version);
        hash.update(pk.as_bytes());
        hash.update(b":");
        hash.update(&ms.to_le_bytes());
        hash.update(&mn.to_le_bytes());
        hash.update(&sz.to_le_bytes());
        hash.finalize().to_hex().to_string()
    };
    let old_hash = hash_for_version(b"single-stat-split:v3\n");
    let splits_dir = shm_file_splits_dir(&store);
    let old_path = splits_dir.join(format!("st_{}.json", &old_hash[..24]));
    fs::write(&old_path, serde_json::to_vec(&legacy).unwrap()).unwrap();
    // The previous PR head stored nonempty, but lexically wrong, identities.
    let stale_hash = hash_for_version(b"single-stat-split:v6\n");
    let stale_path = splits_dir.join(format!("st_{}.json", &stale_hash[..24]));
    for shard in legacy["split"]["shards"].as_array_mut().unwrap() {
        shard["qualified_name"] = serde_json::json!("Wrong.same");
    }
    fs::write(&stale_path, serde_json::to_vec(&legacy).unwrap()).unwrap();

    let new_hash = compute_single_stat_hash(&pk, ms, mn, sz);
    assert_ne!(new_hash, old_hash);
    assert_ne!(new_hash, stale_hash);

    let result = evaluate_check_command_value(
        &mut store,
        file.clone(),
        Some("A.same".into()),
        proj.clone(),
    )
    .unwrap();
    assert_eq!(result["status"], "theorem_verified");
    assert_eq!(result["decl"], "A.same");
    let rebuilt: ShmCachedFileSplit = serde_json::from_slice(
        &fs::read(splits_dir.join(format!("st_{}.json", &new_hash[..24]))).unwrap(),
    )
    .unwrap();
    assert_eq!(rebuilt.split.shards[0].decl_name(), "A.same");
    assert_eq!(rebuilt.split.shards[1].decl_name(), "B.same");
    let warm = evaluate_check_command_value(
        &mut store,
        file.clone(),
        Some("A.same".into()),
        proj.clone(),
    )
    .unwrap();
    assert_eq!(warm["status"], "theorem_cache_hit");
    let agent = crate::gpu_fastcheck::evaluate_agent_step_value(
        &mut store,
        &file,
        Some("A.same"),
        Some(&proj),
        false,
        false,
    )
    .unwrap();
    assert_eq!(agent["status"], "theorem_cache_hit");
    assert_eq!(agent["shard_hits"], 1);
    let ambiguous = crate::gpu_fastcheck::evaluate_agent_step_value(
        &mut store,
        &file,
        Some("same"),
        Some(&proj),
        false,
        false,
    )
    .unwrap_err();
    assert!(ambiguous.to_string().contains("Ambiguous declaration"));
    assert!(evaluate_check_command_value(&mut store, file, Some("B.same".into()), proj).is_err());
    let _ = fs::remove_file(old_path);
    let _ = fs::remove_file(stale_path);
    let _ = fs::remove_file(splits_dir.join(format!("st_{}.json", &new_hash[..24])));
    let _ = fs::remove_dir_all(dir);
}

#[test]
fn test_check_decl_stat_cache_reconstructs_signature_and_proof_telemetry() {
    let tmp_dir = std::env::temp_dir().join(format!(
        "turbo_stat_cache_telemetry_{}",
        crate::pack::next_tmp_id()
    ));
    let _ = fs::remove_dir_all(&tmp_dir);
    let (store_dir, proj_dir) = (tmp_dir.join("store"), tmp_dir.join("proj"));
    fs::create_dir_all(&store_dir).unwrap();
    fs::create_dir_all(&proj_dir).unwrap();

    let toolchain = "leanprover/lean4:v4.35.0";
    fs::write(proj_dir.join("lean-toolchain"), format!("{}\n", toolchain)).unwrap();
    let lean_file = proj_dir.join("StatCacheTelemetry.lean");
    let src = "theorem stat_cache_eq_thm (a b : Nat) (h : a = b) : Nat.succ a = Nat.succ b := by\n  simp only [h]\n";
    fs::write(&lean_file, src).unwrap();

    let mut store = TurboStore::open(Some(&store_dir)).unwrap();
    let split = split_lean_source(src, &[]);
    let shard = &split.shards[0];
    let attested = confirm_decl_identity(src, shard, &proj_dir, &lean_file).unwrap();
    let shard_key = compute_shard_key(toolchain, shard);
    let receipt = make_attested_shard_receipt_bytes(
        &shard.name,
        &shard.prefix_env_hash,
        &shard.stmt_hash,
        &shard.proof_hash,
        db::now_unix(),
        Some(&attested.kernel_type_hash),
    )
    .unwrap();
    store
        .batch_publish_theorem_shards(
            toolchain,
            "trusted",
            &[(shard_key, shard.name.clone(), receipt, 1)],
        )
        .unwrap();

    let first = evaluate_check_command_value(
        &mut store,
        lean_file.clone(),
        Some("stat_cache_eq_thm".to_string()),
        proj_dir.clone(),
    )
    .unwrap();
    let second = evaluate_check_command_value(
        &mut store,
        lean_file.clone(),
        Some("stat_cache_eq_thm".to_string()),
        proj_dir.clone(),
    )
    .unwrap();

    for res in [&first, &second] {
        assert_eq!(res["status"], "theorem_cache_hit");
        assert_eq!(res["goal_head"], "Eq");
        assert_eq!(res["tactic_skeleton"], "simp_only");
        assert!(res["stmt_nodes"].as_u64().unwrap_or(0) > 4);
        assert!(res["proof_term_nodes"].as_u64().unwrap_or(0) > 0);
        let consts: Vec<&str> = res["stmt_consts"]
            .as_array()
            .unwrap()
            .iter()
            .filter_map(|v| v.as_str())
            .collect();
        assert!(consts.contains(&"Nat") && consts.contains(&"Nat.succ"));
    }
    assert_eq!(first["stmt_nodes"], second["stmt_nodes"]);
    assert_eq!(first["stmt_depth"], second["stmt_depth"]);
    assert_eq!(first["num_binders"], second["num_binders"]);
    assert_eq!(first["stmt_consts"], second["stmt_consts"]);
    let _ = fs::remove_dir_all(&tmp_dir);
}

#[test]
fn test_fission_store_key_namespaces_axiom_allowlist_and_mcp_rechecks_dependents() {
    let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let prev_allow = std::env::var(splitter::ALLOWED_AXIOMS_ENV).ok();
    std::env::remove_var(splitter::ALLOWED_AXIOMS_ENV);
    let k_default = compute_fission_store_key("tc", "pref", "sub0");
    std::env::set_var(splitter::ALLOWED_AXIOMS_ENV, "*");
    let k_wildcard = compute_fission_store_key("tc", "pref", "sub0");
    std::env::set_var(splitter::ALLOWED_AXIOMS_ENV, "*._native.bv_decide.ax_*");
    let k_bv = compute_fission_store_key("tc", "pref", "sub0");
    match prev_allow {
        Some(v) => std::env::set_var(splitter::ALLOWED_AXIOMS_ENV, v),
        None => std::env::remove_var(splitter::ALLOWED_AXIOMS_ENV),
    }
    assert_ne!(k_default, k_wildcard);
    assert_ne!(k_default, k_bv);
    assert_ne!(k_wildcard, k_bv);

    let dir = std::env::temp_dir().join(format!(
        "turbo_mcp_nonlocal_recheck_{}_{}",
        std::process::id(),
        crate::pack::next_tmp_id()
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(dir.join("P")).unwrap();
    fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
    fs::write(
            dir.join("lakefile.toml"),
            "name = \"p\"\n[[lean_lib]]\nname = \"P\"\nglobs = [\"P.+\"]\n[[lean_exe]]\nname = \"app\"\nroot = \"Main\"\n",
        )
        .unwrap();
    let a_src = "theorem t (n : Nat) : n + 0 = n := by\n  simp\n";
    fs::write(dir.join("P/A.lean"), a_src).unwrap();
    fs::write(
        dir.join("P/B.lean"),
        "import P.A\ntheorem u (m : Nat) : m + 0 = m := by\n  omega\n",
    )
    .unwrap();
    fs::write(
        dir.join("Main.lean"),
        "import P.A\ntheorem exe_dep (m : Nat) : m + 0 = m := t m\ndef main : IO Unit := pure ()\n",
    )
    .unwrap();
    let ok = |c: &mut Command| c.current_dir(&dir).output().map(|o| o.status.success());
    if !ok(Command::new("lake").args(["build", "P", "Main"])).unwrap_or(false) {
        let _ = fs::remove_dir_all(&dir);
        return;
    }
    for args in [
        &["init", "-q"][..],
        &["add", "."],
        &[
            "-c",
            "user.name=t",
            "-c",
            "user.email=t@t",
            "commit",
            "-qm",
            "base",
        ],
    ] {
        assert!(ok(Command::new("git").args(args)).unwrap());
    }
    // Statement edit on `P/A.lean` remains locally provable in `P.A` (`0 + n = n`),
    // but breaks importer `P.B`: in-process `evaluate_agent_step_value`,
    // `evaluate_check_command_value`, and `execute_mcp_agent_step` must all reject!
    fs::write(
        dir.join("P/A.lean"),
        "theorem t (n : Nat) : 0 + n = n := by\n  omega\n",
    )
    .unwrap();
    let mut store = TurboStore::open(Some(&dir.join(".cache"))).unwrap();
    assert!(crate::gpu_fastcheck::evaluate_agent_step_value(
        &mut store,
        &dir.join("P/A.lean"),
        Some("t"),
        Some(&dir),
        false,
        false,
    )
    .is_err());
    assert!(evaluate_check_command_value(
        &mut store,
        dir.join("P/A.lean"),
        Some("t".to_string()),
        dir.clone(),
    )
    .is_err());
    let mcp_out = crate::mcp::execute_mcp_agent_step(
        &dir.join("P/A.lean"),
        Some("t"),
        false,
        false,
        Some(&dir),
        Some(&dir.join(".cache")),
    );
    assert_eq!(mcp_out["ok"], false);
    assert_eq!(mcp_out["verified"], false);
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn invalid_config_errors_before_empty_option_cache_lookup() -> Result<()> {
    let dir = std::env::temp_dir().join(format!("turbo_check_bad_options_{}", pack::next_tmp_id()));
    let project = dir.join("project");
    fs::create_dir_all(&project)?;
    let file = project.join("Options.lean");
    let source = "theorem option_error : True := by trivial\n";
    fs::write(&file, source)?;
    let tc = "leanprover/lean4:v4.35.0";
    let split = split_lean_source(source, &[]);
    let shard = &split.shards[0];
    let key = compute_shard_key(tc, shard);
    let receipt = make_shard_receipt_bytes(
        &shard.name,
        &shard.prefix_env_hash,
        &shard.stmt_hash,
        &shard.proof_hash,
        db::now_unix(),
    )?;
    let mut store = TurboStore::open(Some(&dir.join("store")))?;
    store.batch_publish_theorem_shards(tc, "trusted", &[(key, shard.name.clone(), receipt, 1)])?;
    fs::write(
        project.join("lakefile.toml"),
        "name = \"invalid\"\nmoreLeanArgs = [\"--plugin=bad.so\"]\n",
    )?;
    for decl in [Some("option_error".to_string()), None] {
        let err = evaluate_check_command_value(&mut store, file.clone(), decl, project.clone())
            .unwrap_err();
        assert!(format!("{err:#}").contains("Failed to resolve Lean options"));
    }
    let _ = fs::remove_dir_all(dir);
    Ok(())
}

#[test]
fn test_lean_args_digest_isolates_shard_and_fission_cache_keys() {
    let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let src = "theorem hb_thm (n : Nat) : n + 0 = n := by\n  simp\n";
    let split = split_lean_source(src, &[]);
    let shard = &split.shards[0];
    let tc = "leanprover/lean4:v4.35.0";
    let bare = compute_shard_key(tc, shard);
    let with_hb = crate::lake_build::compute_shard_key_with_args(
        tc,
        shard,
        &["-DmaxHeartbeats=4000000".to_string()],
    );
    let with_other = crate::lake_build::compute_shard_key_with_args(
        tc,
        shard,
        &["-DmaxHeartbeats=200000".to_string()],
    );
    assert_ne!(bare, with_hb);
    assert_ne!(with_hb, with_other);
    assert_eq!(
        crate::lake_build::compute_shard_key_with_args(tc, shard, &[]),
        bare
    );

    let f_bare = compute_fission_store_key(tc, "pref", "sub0");
    let f_hb = compute_fission_store_key_with_args(
        tc,
        "pref",
        "sub0",
        &["-DmaxHeartbeats=4000000".to_string()],
    );
    assert_ne!(f_bare, f_hb);
}

#[test]
fn literal_and_layout_edits_miss_warm_check_and_agent_step_caches() -> Result<()> {
    let dir = std::env::temp_dir().join(format!("turbo_check_lit_layout_{}", pack::next_tmp_id()));
    let project = dir.join("project");
    fs::create_dir_all(&project)?;
    fs::write(project.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
    let file = project.join("Lit.lean");
    let valid_src = "theorem t_str : \"a b\" = \"a b\" := rfl\ntheorem t_chr : ' ' = ' ' := rfl\ntheorem t_lay : True := by\n  skip\n  trivial\n";
    fs::write(&file, valid_src)?;

    let mut store = TurboStore::open(Some(&dir.join("store")))?;
    let first_check =
        evaluate_check_command_value(&mut store, file.clone(), None, project.clone())?;
    assert_eq!(first_check["status"], "file_verified");
    let warm_check = evaluate_check_command_value(&mut store, file.clone(), None, project.clone())?;
    assert_eq!(warm_check["status"], "all_shards_cached");
    assert_eq!(warm_check["shard_hits"], 3);

    let warm_step = crate::gpu_fastcheck::evaluate_agent_step_value(
        &mut store,
        &file,
        Some("t_str"),
        Some(&project),
        false,
        false,
    )?;
    assert_eq!(warm_step["verified"], true);
    assert_eq!(warm_step["status"], "theorem_cache_hit");

    for (bad_src, decl) in [
            (
                "theorem t_str : \"a  b\" = \"a b\" := rfl\ntheorem t_chr : ' ' = ' ' := rfl\ntheorem t_lay : True := by\n  skip\n  trivial\n",
                "t_str",
            ),
            (
                "theorem t_str : \"a b\" = \"a b\" := rfl\ntheorem t_chr : '\t' = ' ' := rfl\ntheorem t_lay : True := by\n  skip\n  trivial\n",
                "t_chr",
            ),
            (
                "theorem t_str : \"a b\" = \"a b\" := rfl\ntheorem t_chr : ' ' = ' ' := rfl\ntheorem t_lay : True := by skip trivial\n",
                "t_lay",
            ),
        ] {
            fs::write(&file, bad_src)?;
            assert!(
                evaluate_check_command_value(
                    &mut store,
                    file.clone(),
                    Some(decl.to_string()),
                    project.clone(),
                )
                .is_err(),
                "expected check failure for {decl}"
            );
            assert!(
                crate::gpu_fastcheck::evaluate_agent_step_value(
                    &mut store,
                    &file,
                    Some(decl),
                    Some(&project),
                    false,
                    false,
                )
                .is_err(),
                "expected agent-step failure for {decl}"
            );
        }

    let _ = fs::remove_dir_all(dir);
    Ok(())
}

#[test]
fn agent_step_warm_cache_invalidates_on_rebuilt_transitive_import_and_stale_trace() {
    let dir = std::env::temp_dir().join(format!(
        "turbo_agent_step_warm_trans_{}",
        pack::next_tmp_id()
    ));
    let proj = dir.join("proj");
    fs::create_dir_all(proj.join("P")).unwrap();
    fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
    fs::write(
        proj.join("lakefile.toml"),
        "name = \"P\"\ndefaultTargets = [\"P\"]\n[[lean_lib]]\nname = \"P\"\nglobs = [\"P.+\"]\n",
    )
    .unwrap();
    fs::write(proj.join("P/A.lean"), "def k : Nat := 1\n").unwrap();
    fs::write(proj.join("P/B.lean"), "import P.A\ndef m : Nat := k\n").unwrap();
    let c_file = proj.join("P/C.lean");
    fs::write(&c_file, "import P.B\ntheorem c_ok : m = 1 := rfl\n").unwrap();
    let run_lake = |args: &[&str]| {
        Command::new("lake")
            .args(args)
            .current_dir(&proj)
            .status()
            .map(|s| s.success())
            .unwrap_or(false)
    };
    if !run_lake(&["build", "P.B"]) {
        let _ = fs::remove_dir_all(&dir);
        return;
    }
    let cache_dir = dir.join(".cache");
    let mut store = TurboStore::open(Some(&cache_dir)).unwrap();
    let cold = crate::gpu_fastcheck::evaluate_agent_step_value(
        &mut store,
        &c_file,
        Some("c_ok"),
        Some(&proj),
        false,
        false,
    )
    .unwrap();
    assert_eq!(cold["verified"], true);
    let warm = crate::gpu_fastcheck::evaluate_agent_step_value(
        &mut store,
        &c_file,
        Some("c_ok"),
        Some(&proj),
        false,
        false,
    )
    .unwrap();
    assert_eq!(warm["status"], "theorem_cache_hit");

    let b_trace = proj.join(".lake/build/lib/lean/P/B.trace");
    let saved_b_trace = fs::read(&b_trace).unwrap();
    fs::remove_file(&b_trace).unwrap();
    fs::write(
        proj.join("turbo-lean.toml"),
        "[worktree]\nauto_link = false\n",
    )
    .unwrap();
    let trace_err = crate::gpu_fastcheck::evaluate_agent_step_value(
        &mut store,
        &c_file,
        Some("c_ok"),
        Some(&proj),
        false,
        false,
    )
    .unwrap_err();
    assert!(
        format!("{trace_err:#}").contains("Worktree opt-out prevents refreshing stale imports"),
        "unexpected error on missing trace: {trace_err:#}"
    );
    fs::write(&b_trace, &saved_b_trace).unwrap();

    std::thread::sleep(std::time::Duration::from_millis(20));
    fs::write(proj.join("P/A.lean"), "def k : Nat := 2\n").unwrap();
    assert!(run_lake(&["build", "P.A"]));
    let opt_err = crate::gpu_fastcheck::evaluate_agent_step_value(
        &mut store,
        &c_file,
        Some("c_ok"),
        Some(&proj),
        false,
        false,
    )
    .unwrap_err();
    assert!(
        format!("{opt_err:#}").contains("Worktree opt-out prevents refreshing stale imports"),
        "warm agent-step bypassed opt-out stale import check: {opt_err:#}"
    );
    fs::remove_file(proj.join("turbo-lean.toml")).unwrap();
    assert!(
        crate::gpu_fastcheck::evaluate_agent_step_value(
            &mut store,
            &c_file,
            Some("c_ok"),
            Some(&proj),
            false,
            false,
        )
        .is_err(),
        "warm agent-step accepted unchanged P/C.lean after P.A changed from 1 to 2"
    );
    let mcp_out = crate::mcp::execute_mcp_agent_step(
        &c_file,
        Some("c_ok"),
        false,
        false,
        Some(&proj),
        Some(&cache_dir),
    );
    assert_eq!(mcp_out["ok"], false);
    assert_eq!(mcp_out["verified"], false);
    let _ = fs::remove_dir_all(&dir);
}

#[cfg(unix)]
#[test]
fn test_active_check_staging_writer_protected_against_store_local_gc_and_shm_spill() -> Result<()> {
    use std::os::unix::fs::PermissionsExt;
    let _env_guard = crate::pack::tests::env_test_lock()
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let dir = std::env::temp_dir().join(format!(
        "turbo_check_staging_gc_race_{}_{}",
        std::process::id(),
        pack::next_tmp_id()
    ));
    let _ = fs::remove_dir_all(&dir);
    let project = dir.join("project");
    let store_root = dir.join("store");
    let store_staging = store_root.join("staging");
    let fake_elan_root = dir.join("fake_elan");
    let tc_name = "leanprover/lean4:v4.35.0-check-gc-race";
    let tc_root = fake_elan_root
        .join("toolchains")
        .join("leanprover--lean4---v4.35.0-check-gc-race");
    let bin_dir = tc_root.join("bin");
    fs::create_dir_all(&project)?;
    fs::create_dir_all(&store_staging)?;
    fs::create_dir_all(&bin_dir)?;

    // Configure `fast_staging_dir()` to resolve directly to `<store>/staging` (exercising the
    // store-local fallback where `run_gc(0, ...)` sweeps 0-second unleased entries immediately),
    // point `ELAN_HOME` at our isolated synthetic toolchain so `ToolchainExecutables` resolves
    // our wrapper `lean` binary cleanly under PR #308's absolute toolchain gate, and disable
    // the background Zygote daemon so `evaluate_check_command_value` executes the real
    // `PrivateScratchDir` -> `run_audited_lean_shard_with_types` staging path.
    let prev_staging = std::env::var("TURBO_LEAN_STAGING_DIR").ok();
    let prev_no_daemon = std::env::var("TURBO_LEAN_NO_DAEMON").ok();
    let prev_elan_home = std::env::var("ELAN_HOME").ok();
    let prev_test_bwrap = std::env::var("TURBO_LEAN_TEST_BWRAP_BIN").ok();
    struct RestoreCheckEnv(
        Option<String>,
        Option<String>,
        Option<String>,
        Option<String>,
    );
    impl Drop for RestoreCheckEnv {
        fn drop(&mut self) {
            match &self.0 {
                Some(v) => std::env::set_var("TURBO_LEAN_STAGING_DIR", v),
                None => std::env::remove_var("TURBO_LEAN_STAGING_DIR"),
            }
            match &self.1 {
                Some(v) => std::env::set_var("TURBO_LEAN_NO_DAEMON", v),
                None => std::env::remove_var("TURBO_LEAN_NO_DAEMON"),
            }
            match &self.2 {
                Some(v) => std::env::set_var("ELAN_HOME", v),
                None => std::env::remove_var("ELAN_HOME"),
            }
            match &self.3 {
                Some(v) => std::env::set_var("TURBO_LEAN_TEST_BWRAP_BIN", v),
                None => std::env::remove_var("TURBO_LEAN_TEST_BWRAP_BIN"),
            }
        }
    }
    let _restore_env = RestoreCheckEnv(
        prev_staging,
        prev_no_daemon,
        prev_elan_home,
        prev_test_bwrap,
    );
    std::env::set_var("TURBO_LEAN_STAGING_DIR", &store_staging);
    std::env::set_var("TURBO_LEAN_NO_DAEMON", "1");
    std::env::set_var("TURBO_LEAN_TEST_BWRAP_BIN", dir.join("missing_bwrap"));

    let fake_lean = bin_dir.join("lean");
    let repo_lean_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lean");
    let resolve_cwd = if repo_lean_dir.is_dir() {
        repo_lean_dir
    } else {
        dir.clone()
    };
    let real_prefix = Command::new("lean")
        .arg("--print-prefix")
        .current_dir(&resolve_cwd)
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| PathBuf::from(String::from_utf8_lossy(&o.stdout).trim()))
        .and_then(|p| p.canonicalize().ok())
        .filter(|p| {
            p.join("bin/lean").is_file()
                && !p.starts_with(&fake_elan_root)
                && !p.join("bin/elan").exists()
        });
    let Some(real_prefix) = real_prefix else {
        let _ = fs::remove_dir_all(&dir);
        return Ok(());
    };
    let real_lean = real_prefix.join("bin/lean");
    for sub in ["lib", "include", "share"] {
        let src_sub = real_prefix.join(sub);
        if src_sub.exists() {
            std::os::unix::fs::symlink(&src_sub, tc_root.join(sub))?;
        }
    }
    for sib in ["lake", "leanc"] {
        let real_sib = real_prefix.join("bin").join(sib);
        let sp = bin_dir.join(sib);
        if real_sib.is_file() {
            fs::write(
                &sp,
                format!("#!/bin/sh\nexec '{}' \"$@\"\n", real_sib.display()),
            )?;
        } else {
            fs::write(&sp, "#!/bin/sh\nexit 0\n")?;
        }
        fs::set_permissions(&sp, fs::Permissions::from_mode(0o755))?;
    }
    std::env::set_var("ELAN_HOME", &fake_elan_root);

    // Wrapper `lean` binary: forwards identity/build calls directly, then when invoked on the
    // staged `TurboAuditedShard_*.lean` file inside `<store>/staging` signals `arrived_marker`
    // BEFORE compiling it, blocks until concurrent `run_gc(0, ...)` and `spill_shm_to_disk_dir`
    // sweeps complete (`proceed_marker`), and finally compiles the staged shard.
    let arrived_marker = dir.join("child_arrived");
    let proceed_marker = dir.join("child_proceed");
    let script = format!(
            "#!/bin/sh\nif [ \"${{1:-}}\" = \"--githash\" ]; then exec '{rl}' --githash; fi\nif [ \"${{1:-}}\" = \"--print-prefix\" ]; then echo '{tc}'; exit 0; fi\nif [ \"${{1:-}}\" = \"--version\" ]; then exec '{rl}' --version; fi\ncase \"$*\" in\n  *TurboAuditedShard_*)\n    : > '{arr}'\n    while [ ! -f '{proc}' ]; do\n      if [ -x /bin/sleep ]; then /bin/sleep 0.01; elif [ -x /usr/bin/sleep ]; then /usr/bin/sleep 0.01; fi\n    done\n    ;;\nesac\nexec '{rl}' \"$@\"\n",
            rl = real_lean.display(),
            tc = tc_root.display(),
            arr = arrived_marker.display(),
            proc = proceed_marker.display(),
        );
    fs::write(&fake_lean, script)?;
    fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755))?;

    fs::write(project.join("lean-toolchain"), format!("{tc_name}\n"))?;
    let lean_file = project.join("CheckGcRace.lean");
    fs::write(&lean_file, "theorem gc_race_a : True := trivial\n")?;

    let store = TurboStore::open(Some(&store_root))?;
    assert_eq!(store.fast_staging_dir(), store_staging);
    let canon_project = project.canonicalize()?;
    let proj_key = TurboStore::compute_lake_env_key(&canon_project);
    let mut fake_env = HashMap::new();
    fake_env.insert("LEAN_PATH".to_string(), String::new());
    store.put_lake_env(&proj_key, &fake_env)?;
    drop(store);

    // Pre-warm the declaration-identity / shard auditor binary BEFORE spawning the timed
    // `evaluate_check_command_value` worker so a cold `ensure_zygote_binary_at` compile does
    // not consume the request timeout budget, and give the parked subprocess generous slack.
    let prev_timeout_ms = std::env::var("TURBO_LEAN_TIMEOUT_MS").ok();
    std::env::set_var("TURBO_LEAN_TIMEOUT_MS", "120000");
    struct RestoreTimeout(Option<String>);
    impl Drop for RestoreTimeout {
        fn drop(&mut self) {
            match &self.0 {
                Some(v) => std::env::set_var("TURBO_LEAN_TIMEOUT_MS", v),
                None => std::env::remove_var("TURBO_LEAN_TIMEOUT_MS"),
            }
        }
    }
    let _restore_timeout = RestoreTimeout(prev_timeout_ms);
    let mut warm_env = HashMap::new();
    warm_env.insert("LEAN_PATH".to_string(), String::new());
    let _ = crate::zygote::ensure_zygote_binary_at(
        &crate::shm_cache::cache_root(),
        &fake_lean,
        &warm_env,
    )?;
    let _ = crate::zygote::ensure_zygote_binary_at(&store_root, &fake_lean, &warm_env)?;

    // Seed unleased file and directory orphans in `<store>/staging` so we prove `run_gc(0, ...)`
    // actively sweeps `<store>/staging` during the window while sparing the live leased scratch dirs.
    let orphan_tmp = store_staging.join("unleased_orphan_before_check.lean");
    fs::write(&orphan_tmp, b"-- stale unleased staging file\n")?;
    let orphan_dir = store_staging.join("turbo_audited_src_stale_orphan");
    fs::create_dir_all(&orphan_dir)?;
    fs::write(orphan_dir.join("Stale.lean"), b"-- stale orphan dir\n")?;

    let check_store_root = store_root.clone();
    let check_file = lean_file.clone();
    let check_proj = project.clone();
    let worker = std::thread::spawn(move || -> Result<serde_json::Value> {
        let mut worker_store = TurboStore::open(Some(&check_store_root))?;
        evaluate_check_command_value(&mut worker_store, check_file, None, check_proj)
    });

    let wait_t0 = Instant::now();
    while !arrived_marker.exists() {
        if worker.is_finished() {
            break;
        }
        assert!(
            wait_t0.elapsed().as_secs() < 120,
            "timed out waiting for check subprocess to spawn"
        );
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
    if !arrived_marker.exists() && worker.is_finished() {
        let val = worker.join().unwrap()?;
        anyhow::bail!("check path finished without invoking lean subprocess on staged file: {val}");
    }
    assert!(
        arrived_marker.exists(),
        "check path must invoke lean subprocess on staged file"
    );
    let active_src_dir = fs::read_dir(&store_staging)?
        .flatten()
        .map(|e| e.path())
        .find(|p| {
            p != &orphan_dir
                && p.is_dir()
                && p.file_name()
                    .and_then(|n| n.to_str())
                    .is_some_and(|n| n.starts_with("turbo_audited_src_"))
        })
        .expect("active leased turbo_audited_src_* dir must exist while lean is parked");
    let active_leased_lean = fs::read_dir(&active_src_dir)?
        .flatten()
        .map(|e| e.path())
        .find(|p| p.extension().and_then(|s| s.to_str()) == Some("lean"))
        .expect("staged TurboAuditedShard_*.lean must exist inside active_src_dir");

    let mut gc_store = TurboStore::open(Some(&store_root))?;
    let gc_rep = gc_store.run_gc(0, 7 * 86400, true)?;
    assert!(
        !orphan_tmp.exists() && !orphan_dir.exists(),
        "run_gc(0) must still reap unleased file and dir orphans in <store>/staging"
    );
    assert!(
            active_src_dir.exists() && fs::symlink_metadata(&active_leased_lean).is_ok(),
            "run_gc(0) must preserve active leased check staging scratch dir and file in <store>/staging"
        );
    assert!(gc_rep.cleaned_staging_files >= 2);

    let spill_dir = dir.join("shm_spill");
    let _ = crate::shm_cache::spill_shm_to_disk_dir(&store_staging, &spill_dir, 0)?;
    assert!(
        fs::symlink_metadata(&active_leased_lean).is_ok()
            && !spill_dir
                .join(active_leased_lean.file_name().unwrap())
                .exists(),
        "spill_shm_to_disk_dir must not evict/move leased active check staging files"
    );
    let _ = crate::shm_cache::enforce_shm_quota_lru(&store_staging, 1)?;
    assert!(
        fs::symlink_metadata(&active_leased_lean).is_ok(),
        "enforce_shm_quota_lru must not evict leased active check staging files"
    );

    fs::write(&proceed_marker, b"go")?;
    let check_val = worker
        .join()
        .expect("check worker thread panicked")
        .context("active check must succeed despite concurrent run_gc(0) + SHM eviction")?;
    assert_eq!(check_val["status"], "file_verified");

    // After check completes and drops `PrivateScratchDir`, neither scratch dirs nor `.lease.lock` remain.
    let remaining: Vec<String> = fs::read_dir(&store_staging)?
        .flatten()
        .map(|e| e.file_name().to_string_lossy().into_owned())
        .filter(|n| n.contains("turbo_audited_") || n.ends_with(".lease.lock"))
        .collect();
    assert!(
            remaining.is_empty(),
            "PrivateScratchDir drop must clean up both scratch dirs and sidecar .lease.lock, found {remaining:?}"
        );
    let _ = fs::remove_dir_all(&dir);
    Ok(())
}

#[test]
fn test_read_single_isolated_olean_rejects_extra_files_symlinks_and_hardlinks() -> Result<()> {
    let scratch = PrivateScratchDir::create(
        &verified_private_temp_scratch_base()?,
        "turbo_iso_olean_test",
    )?;
    let out_dir = scratch.path.join("out");
    fs::create_dir_all(&out_dir)?;

    // Empty output dir fails closed.
    assert!(read_single_isolated_olean(&out_dir, "ExpectedMod").is_err());

    // Exact single regular `.olean` succeeds.
    let expected = out_dir.join("ExpectedMod.olean");
    fs::write(&expected, b"valid-olean-bytes")?;
    assert_eq!(
        read_single_isolated_olean(&out_dir, "ExpectedMod")?,
        b"valid-olean-bytes"
    );

    // Any extra/forged file inside `out_dir` fails closed.
    let forged = out_dir.join("ForgedOther.olean");
    fs::write(&forged, b"forged-bytes")?;
    let err = read_single_isolated_olean(&out_dir, "ExpectedMod").unwrap_err();
    assert!(
        format!("{err:#}").contains("must contain only"),
        "unexpected error: {err:#}"
    );
    fs::remove_file(&forged)?;

    #[cfg(unix)]
    {
        // Hardlink (`st_nlink > 1`) fails closed so no out-of-dir alias can mutate after check.
        let outside_link = scratch.path.join("alias.olean");
        fs::hard_link(&expected, &outside_link)?;
        let err = read_single_isolated_olean(&out_dir, "ExpectedMod").unwrap_err();
        assert!(
            format!("{err:#}").contains("hard-link count"),
            "unexpected error: {err:#}"
        );
        fs::remove_file(&outside_link)?;

        // Symlink at expected path fails closed via O_NOFOLLOW.
        let target = scratch.path.join("real.olean");
        fs::write(&target, b"real-olean-bytes")?;
        fs::remove_file(&expected)?;
        std::os::unix::fs::symlink(&target, &expected)?;
        assert!(read_single_isolated_olean(&out_dir, "ExpectedMod").is_err());
    }
    Ok(())
}

#[test]
#[cfg(unix)]
fn test_post_exit_background_child_reaped_and_frozen_dir_blocks_overwrite() -> Result<()> {
    use std::os::unix::fs::PermissionsExt;
    let scratch =
        PrivateScratchDir::create(&verified_private_temp_scratch_base()?, "turbo_bg_reap_test")?;
    let out_dir = scratch.path.join("out");
    fs::create_dir_all(&out_dir)?;
    let expected = out_dir.join("Mod.olean");
    let nonce = format!("reap-nonce-{}-{}", std::process::id(), pack::next_tmp_id());

    let mut cmd = Command::new("/bin/sh");
    cmd.env("TURBO_LEAN_PROBE_NONCE", &nonce)
            .env("OUT_DIR", &out_dir)
            .arg("-c")
            .arg(
                "printf 'clean-olean' > \"$OUT_DIR/Mod.olean\"; \
                 (sleep 0.35; printf 'forged' > \"$OUT_DIR/Mod.olean.new\" 2>/dev/null && mv \"$OUT_DIR/Mod.olean.new\" \"$OUT_DIR/Mod.olean\" 2>/dev/null; printf 'forged' > \"$OUT_DIR/Mod.olean\" 2>/dev/null) </dev/null >/dev/null 2>&1 & \
                 exit 0",
            );
    let out = crate::module_builder::run_command_with_timeout(
        &mut cmd,
        std::time::Duration::from_secs(10),
        false,
    )?;
    assert!(out.status.success());
    crate::zygote::reap_processes_with_nonce(&nonce);
    freeze_private_dir(&out_dir)?;
    fs::set_permissions(&expected, fs::Permissions::from_mode(0o400))?;

    std::thread::sleep(std::time::Duration::from_millis(500));
    let bytes = read_single_isolated_olean(&out_dir, "Mod")?;
    assert_eq!(bytes, b"clean-olean");
    Ok(())
}

#[test]
fn test_agent_step_rejects_unattested_or_mislabeled_cached_receipt_and_reattests() -> Result<()> {
    let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let dir =
        std::env::temp_dir().join(format!("turbo_agent_step_reattest_{}", pack::next_tmp_id()));
    let project = dir.join("project");
    let cache = dir.join("cache");
    fs::create_dir_all(&project)?;
    fs::write(
        project.join("lean-toolchain"),
        include_str!("../../../../lean/lean-toolchain"),
    )?;
    fs::write(
        project.join("lakefile.toml"),
        "name = \"reattest\"\nversion = \"0.1.0\"\n",
    )?;
    let file = project.join("Identity.lean");
    // Valid proof first: seed an unattested legacy receipt (no `kernel_type_hash` and short name).
    let valid_src = "namespace B\ntheorem same (n : Nat) : n = n := rfl\nend B\n";
    fs::write(&file, valid_src)?;
    let tc = detect_toolchain(&project);
    let split = split_lean_source(valid_src, &[]);
    let shard = &split.shards[0];
    let key = compute_shard_key(&tc, shard);
    let mut store = TurboStore::open(Some(&cache))?;
    let unattested_receipt = make_shard_receipt_bytes(
        &shard.name,
        &shard.prefix_env_hash,
        &shard.stmt_hash,
        &shard.proof_hash,
        db::now_unix(),
    )?;
    store.batch_publish_theorem_shards(
        &tc,
        "trusted",
        &[(key.clone(), shard.name.clone(), unattested_receipt, 1)],
    )?;
    // Untargeted (`None`) and `"auto"` must NOT accept the unattested receipt as a `stage0_cas_hit`:
    // they must invalidate it, run Stage-2 kernel verification, and write an attested receipt.
    let v_cold = crate::gpu_fastcheck::evaluate_agent_step_value(
        &mut store,
        &file,
        Some("auto"),
        Some(&project),
        false,
        false,
    )?;
    assert_eq!(v_cold["verified"], true, "{v_cold}");
    assert_eq!(
        v_cold["status"], "file_verified",
        "unattested cached receipt must not short-circuit as cached hit: {v_cold}"
    );
    assert_eq!(v_cold["shard_hits"], 0, "{v_cold}");
    // Subsequent untargeted call now hits the freshly attested receipt.
    let v_warm = crate::gpu_fastcheck::evaluate_agent_step_value(
        &mut store,
        &file,
        None,
        Some(&project),
        false,
        false,
    )?;
    assert_eq!(v_warm["verified"], true, "{v_warm}");
    assert_eq!(v_warm["status"], "all_shards_cached", "{v_warm}");
    assert_eq!(v_warm["decl"], "B.same", "{v_warm}");

    // Now poison the cache for a broken proof on a true statement (`True`) with an unattested
    // receipt: `agent-step` must NOT accept the unattested receipt as a cached hit (`verified: true`)
    // and must fail closed in Stage 2.
    let invalid_src = "namespace B\ntheorem broken : True := 0\nend B\n";
    fs::write(&file, invalid_src)?;
    let bad_split = split_lean_source(invalid_src, &[]);
    let bad_shard = &bad_split.shards[0];
    let bad_key = compute_shard_key(&tc, bad_shard);
    let forged_unattested = make_shard_receipt_bytes(
        bad_shard.decl_name(),
        &bad_shard.prefix_env_hash,
        &bad_shard.stmt_hash,
        &bad_shard.proof_hash,
        db::now_unix(),
    )?;
    store.batch_publish_theorem_shards(
        &tc,
        "trusted",
        &[(
            bad_key,
            bad_shard.decl_name().to_string(),
            forged_unattested,
            1,
        )],
    )?;
    assert!(crate::gpu_fastcheck::evaluate_agent_step_value(
        &mut store,
        &file,
        None,
        Some(&project),
        false,
        false,
    )
    .is_err());

    let _ = fs::remove_dir_all(&dir);
    Ok(())
}

#[test]
fn test_identity_probe_hardening_escaped_aux_inferred_module_werror_readonly_and_lean_path(
) -> Result<()> {
    let _env_guard = crate::pack::tests::env_test_lock()
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let dir = std::env::temp_dir().join(format!("turbo_id_hardening_{}", pack::next_tmp_id()));
    let ext_pkg = dir.join("ext_pkg");
    let project = dir.join("project");
    fs::create_dir_all(&ext_pkg)?;
    fs::create_dir_all(&project)?;
    let tc_text = include_str!("../../../../lean/lean-toolchain");
    fs::write(project.join("lean-toolchain"), tc_text)?;
    fs::write(
        project.join("lakefile.toml"),
        "name = \"idhard\"\nversion = \"0.1.0\"\nleanOptions = { warningAsError = true }\n",
    )?;

    // Build an external `.olean` outside `project` and expose it only via `LEAN_PATH`.
    let ext_src = ext_pkg.join("ExtIdDep.lean");
    let ext_olean = ext_pkg.join("ExtIdDep.olean");
    fs::write(&ext_src, "def ext_magic : Nat := 7\n")?;
    let base_env = crate::lake_build::spawn_lake_env(&project)?;
    let lean_bin = resolve_lean_bin(&project)?;
    let ext_out = Command::new(&lean_bin)
        .envs(&base_env)
        .arg(&ext_src)
        .arg("-R")
        .arg(&ext_pkg)
        .arg("-o")
        .arg(&ext_olean)
        .output()?;
    assert!(
        ext_out.status.success(),
        "failed to compile ExtIdDep.lean: {}",
        String::from_utf8_lossy(&ext_out.stderr)
    );
    let prev_lp = std::env::var("LEAN_PATH").ok();
    let new_lp = match &prev_lp {
        Some(p) if !p.is_empty() => format!("{}:{p}", ext_pkg.display()),
        _ => ext_pkg.display().to_string(),
    };
    std::env::set_var("LEAN_PATH", &new_lp);
    struct RestoreLeanPath(Option<String>);
    impl Drop for RestoreLeanPath {
        fn drop(&mut self) {
            match &self.0 {
                Some(v) => std::env::set_var("LEAN_PATH", v),
                None => std::env::remove_var("LEAN_PATH"),
            }
        }
    }
    let _restore_lp = RestoreLeanPath(prev_lp);

    // 1) Escaped names (`«foo»`), macro-generated auxiliary theorem in same command span,
    //    `warningAsError = true` with earlier theorem stubbed to `sorry`, body-inferred `def`
    //    (`def inferred_ty := ...`), external `LEAN_PATH` import, and read-only (`0o555`)
    //    source project directory.
    let src = "\
import ExtIdDep
macro \"declare_with_aux \" id:ident : command => `(
  theorem aux_generated_helper : True := True.intro
  theorem $id : ext_magic = 7 := rfl
)
theorem earlier_for_werror : ext_magic = 7 := rfl
namespace «EscNs»
theorem «foo» : ext_magic = 7 := rfl
end «EscNs»
declare_with_aux macro_primary
theorem after_macro : ext_magic = 7 := rfl
";
    let file = project.join("Hardening.lean");
    fs::write(&file, src)?;

    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&file, fs::Permissions::from_mode(0o444))?;
        fs::set_permissions(&project, fs::Permissions::from_mode(0o555))?;
    }

    let split = split_lean_source(src, &[]);
    // Shards in split: `earlier_for_werror`, `«EscNs».«foo»`, `after_macro`.
    let esc_idx = splitter::find_decl_shard_index(&split.shards, "EscNs.foo")?
        .expect("escaped shard resolved");
    let after_idx = splitter::find_decl_shard_index(&split.shards, "after_macro")?
        .expect("after_macro shard resolved");
    let shard_refs: Vec<&splitter::TheoremShard> = split.shards.iter().collect();
    let batch_atts =
        confirm_file_decl_identities_with_budget(src, &shard_refs, &project, &file, false, None)?;
    assert_eq!(batch_atts.len(), split.shards.len());
    assert_eq!(batch_atts[esc_idx].decl_name, "EscNs.foo");
    assert_eq!(batch_atts[after_idx].decl_name, "after_macro");

    // Equation-compiler / macro-elaborated theorem whose `signature_text` cannot elaborate
    // against `:= by sorry` falls back from stubbed probe to the declaration's original text in
    // `confirm_decl_identity_with_budget`.
    let eq_src = format!(
        "{src}theorem eqn_inferred : Nat → ext_magic = 7\n  | 0 => rfl\n  | _ + 1 => rfl\n"
    );
    let eq_split = split_lean_source(&eq_src, &[]);
    let mut eq_shard = eq_split
        .shards
        .iter()
        .find(|s| s.name == "eqn_inferred")
        .expect("eqn_inferred shard")
        .clone();
    // Simulate a header whose stubbed `:= by sorry` form fails elaboration, forcing full-body retry.
    eq_shard.signature_text = "theorem eqn_inferred : _".to_string();
    let inferred_att =
        confirm_decl_identity_with_budget(&eq_src, &eq_shard, &project, &file, false, None)?;
    assert_eq!(inferred_att.decl_name, "eqn_inferred");
    assert_eq!(inferred_att.kernel_type_hash.len(), 64);

    // Also test `match_expected_decl_identity` directly when auxiliary theorems share the probe span.
    let aux_entries = vec![
        OleanDeclEntry {
            decl_name: "aux_generated_helper".to_string(),
            kernel_type_hash: "1".repeat(64),
            line: Some(10),
        },
        OleanDeclEntry {
            decl_name: "«EscNs».«foo»".to_string(),
            kernel_type_hash: "2".repeat(64),
            line: Some(10),
        },
    ];
    let matched = match_expected_decl_identity("EscNs.foo", &aux_entries, Some((10, 11)))?;
    assert_eq!(matched.decl_name, "EscNs.foo");
    assert_eq!(matched.kernel_type_hash, "2".repeat(64));

    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&project, fs::Permissions::from_mode(0o755))?;
        fs::set_permissions(&file, fs::Permissions::from_mode(0o644))?;
    }

    // 2) Lean 4.35 `module` header emits `.olean`, `.olean.server`, `.olean.private`, `.ir`, `.ir.sig`.
    let mod_src = "module\npublic theorem pub_mod_thm : True := True.intro\ntheorem priv_mod_thm : (1 : Nat) = 1 := rfl\n";
    let mod_file = project.join("ModFile.lean");
    fs::write(&mod_file, mod_src)?;
    let mod_split = split_lean_source(mod_src, &[]);
    assert_eq!(mod_split.shards.len(), 2);
    let mod_refs: Vec<&splitter::TheoremShard> = mod_split.shards.iter().collect();
    let mod_atts = confirm_file_decl_identities_with_budget(
        mod_src, &mod_refs, &project, &mod_file, false, None,
    )?;
    assert_eq!(mod_atts.len(), 2);
    assert_eq!(mod_atts[0].decl_name, "pub_mod_thm");
    assert_eq!(mod_atts[1].decl_name, "priv_mod_thm");

    // Stage isolated module artifacts rejects unexpected files while accepting `.olean.{server,private}` and `.ir{,.sig}`.
    let iso =
        PrivateScratchDir::create(&verified_private_temp_scratch_base()?, "turbo_iso_mod_test")?;
    let out_m = iso.path.join("out");
    let rdr_m = iso.path.join("rdr");
    fs::create_dir_all(&out_m)?;
    fs::create_dir_all(&rdr_m)?;
    for suffix in [
        ".olean",
        ".olean.server",
        ".olean.private",
        ".ir",
        ".ir.sig",
    ] {
        fs::write(out_m.join(format!("M{suffix}")), b"artifact")?;
    }
    stage_isolated_module_artifacts(&out_m, &rdr_m, "M")?;
    assert!(rdr_m.join("M.olean").is_file());
    assert!(rdr_m.join("M.olean.server").is_file());
    assert!(rdr_m.join("M.olean.private").is_file());
    assert!(!rdr_m.join("M.ir").exists());
    fs::write(out_m.join("Forged.olean"), b"bad")?;
    assert!(stage_isolated_module_artifacts(&out_m, &rdr_m, "M").is_err());

    let _ = fs::remove_dir_all(&dir);
    Ok(())
}

#[test]
fn test_fission_subshard_rejects_legacy_v2_keys_and_unattested_v3_receipts() {
    let tmp_dir = std::env::temp_dir().join(format!(
        "turbo_fission_provenance_test_{}",
        crate::pack::next_tmp_id()
    ));
    let _ = fs::remove_dir_all(&tmp_dir);
    let (store_dir, proj_dir) = (tmp_dir.join("store"), tmp_dir.join("proj"));
    fs::create_dir_all(&store_dir).unwrap();
    fs::create_dir_all(&proj_dir).unwrap();

    let toolchain = "leanprover/lean4:v4.35.0";
    let f_key = compute_fission_store_key(toolchain, "pref_hash", "sub_hash");
    assert!(
        f_key.starts_with(&format!(
            "fission-v8:{}:{}:{}:pref_hash:sub_hash",
            crate::zygote::ZYGOTE_SCANNER_VERSION,
            crate::zygote::ZYGOTE_REPLAY_VERSION,
            toolchain
        )),
        "unexpected fission store key format: {f_key}"
    );

    fs::write(proj_dir.join("lean-toolchain"), format!("{toolchain}\n")).unwrap();
    let mut store = TurboStore::open(Some(&store_dir)).unwrap();
    let (env_vars, lean_bin) =
        crate::pack::resolve_server_lean_env_and_bin(&store, toolchain, "").unwrap();
    if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
        let _ = fs::remove_dir_all(&tmp_dir);
        return;
    }
    crate::zygote::ensure_zygote_binary(&store, &lean_bin, &env_vars).unwrap();

    // 1) `verify_subshards_out_of_core` treats unattested or version-mismatched rows as misses
    // and re-verifies before minting a current-provenance sub-shard receipt.
    let ooc_prefix = "namespace FissionProvenanceOoc\ndef idNat (n : Nat) : Nat := n\n";
    let ooc_step0 = (
        "prov_step_0".to_string(),
        "prov_ooc_key_0".to_string(),
        "theorem prov_step_0 (n : Nat) : idNat n = n := rfl\n".to_string(),
    );
    let ooc_step1 = (
        "prov_step_1".to_string(),
        "prov_ooc_key_1".to_string(),
        "theorem prov_step_1 : idNat 7 = 7 := rfl\n".to_string(),
    );
    store
        .put_theorem_shard(
            toolchain,
            &ooc_step0.1,
            &ooc_step0.0,
            br#"{"decl":"prov_step_0","verified_at":1}"#,
            1,
        )
        .unwrap();
    let stale_ooc_receipt = serde_json::to_vec(&serde_json::json!({
        "decl": ooc_step1.0,
        "verified_at": 1,
        "scanner_version": crate::zygote::ZYGOTE_SCANNER_VERSION.saturating_sub(1),
        "replay_version": crate::zygote::ZYGOTE_REPLAY_VERSION,
    }))
    .unwrap();
    store
        .put_theorem_shard(toolchain, &ooc_step1.1, &ooc_step1.0, &stale_ooc_receipt, 1)
        .unwrap();
    assert!(!store_has_provenanced_subshard(&store, &ooc_step0.1));
    assert!(!store_has_provenanced_subshard(&store, &ooc_step1.1));
    let (ooc_hits, ooc_verified) = verify_subshards_out_of_core(
        &mut store,
        toolchain,
        "",
        &env_vars,
        &lean_bin,
        ooc_prefix,
        &[ooc_step0.clone(), ooc_step1.clone()],
    )
    .unwrap();
    assert_eq!((ooc_hits, ooc_verified), (0, 2));
    assert!(store_has_provenanced_subshard(&store, &ooc_step0.1));
    assert!(store_has_provenanced_subshard(&store, &ooc_step1.1));

    // 2) Cut-fission in `check_single_decl` ignores both legacy `fission-v2:` keys and
    // `fission-v3:` rows lacking current scanner/replay provenance, refusing to skip
    // verification or mint an attested parent receipt from unattested sub-shards.
    let lean_file = proj_dir.join("FissionProvenanceTest.lean");
    let canon_proj = proj_dir.canonicalize().unwrap_or_else(|_| proj_dir.clone());
    let src = "def bump (n : Nat) : Nat := n + 1\ntheorem prov_cut_thm (a b : Nat) : (a + 1) + (b + 2) = a + b + 3 := by\n  have h1 : a + 1 = 1 + a := by\n    omega\n  have h2 : b + 2 = 2 + b := by\n    omega\n  omega\n";
    fs::write(&lean_file, src).unwrap();
    let canon_file = lean_file
        .canonicalize()
        .unwrap_or_else(|_| lean_file.clone());
    let mut split = split_lean_source(src, &[]);
    let shard = split.shards[0].clone();
    let subs = splitter::fission_theorem_have_blocks(
        &extract_decl_source_from_file(src, &shard),
        "prov_cut_thm",
    );
    assert_eq!(subs.len(), 3);

    // Poison legacy `fission-v2:` keys AND `fission-v3:` keys with unattested / stale-version
    // receipts (simulating a pre-upgrade forged sub-shard DB row).
    for (idx, sub) in subs.iter().enumerate() {
        let legacy_v2_key = format!(
            "fission-v2:{}:{}:{}",
            toolchain, shard.prefix_env_hash, sub.sub_shard_key
        );
        let forged_ok = serde_json::to_vec(&serde_json::json!({
            "decl": sub.step_label,
            "parent_decl": "prov_cut_thm",
            "sub_shard_key": sub.sub_shard_key,
            "prefix_env_hash": shard.prefix_env_hash,
            "verified_at": 1,
            "scanner_version": crate::zygote::ZYGOTE_SCANNER_VERSION,
            "replay_version": crate::zygote::ZYGOTE_REPLAY_VERSION,
        }))
        .unwrap();
        store
            .put_theorem_shard(toolchain, &legacy_v2_key, &sub.step_label, &forged_ok, 1)
            .unwrap();

        let v3_key =
            compute_fission_store_key(toolchain, &shard.prefix_env_hash, &sub.sub_shard_key);
        let unattested_v3 = if idx == 0 {
            serde_json::to_vec(&serde_json::json!({
                "decl": sub.step_label,
                "parent_decl": "prov_cut_thm",
                "sub_shard_key": sub.sub_shard_key,
                "prefix_env_hash": shard.prefix_env_hash,
                "verified_at": 1,
            }))
            .unwrap()
        } else {
            serde_json::to_vec(&serde_json::json!({
                "decl": sub.step_label,
                "parent_decl": "prov_cut_thm",
                "sub_shard_key": sub.sub_shard_key,
                "prefix_env_hash": shard.prefix_env_hash,
                "verified_at": 1,
                "scanner_version": crate::zygote::ZYGOTE_SCANNER_VERSION,
                "replay_version": crate::zygote::ZYGOTE_REPLAY_VERSION.saturating_sub(1),
            }))
            .unwrap()
        };
        store
            .put_theorem_shard(toolchain, &v3_key, &sub.step_label, &unattested_v3, 1)
            .unwrap();
        assert!(!store_has_provenanced_subshard(&store, &v3_key));
    }

    // Also confirm an invalid theorem whose `fission-v3:` sub-shards were forged WITHOUT
    // current provenance CANNOT mint a parent receipt and fails verification.
    let bad_src = src.replacen(
        "  have h2 : b + 2 = 2 + b := by\n    omega\n  omega\n",
        "  have h2 : b + 2 = 2 + b := by\n    omega\n  exact nonexistent_ident_xyz\n",
        1,
    );
    fs::write(&lean_file, &bad_src).unwrap();
    let mut bad_split = split_lean_source(&bad_src, &[]);
    let bad_shard = bad_split.shards[0].clone();
    let bad_subs = splitter::fission_theorem_have_blocks(
        &extract_decl_source_from_file(&bad_src, &bad_shard),
        "prov_cut_thm",
    );
    for sub in &bad_subs {
        let v3_key =
            compute_fission_store_key(toolchain, &bad_shard.prefix_env_hash, &sub.sub_shard_key);
        store
            .put_theorem_shard(
                toolchain,
                &v3_key,
                &sub.step_label,
                br#"{"decl":"forged_without_provenance","verified_at":1}"#,
                1,
            )
            .unwrap();
    }
    let test_kp = crate::kernel::resolve_kernel_engine(
        crate::kernel::KernelEngineSelection::Standard,
        toolchain,
    )
    .unwrap();
    let mut cb3 = None;
    let t0 = Instant::now();
    assert!(check_single_decl(
        &mut store,
        true,
        false,
        false,
        &test_kp,
        &t0,
        &lean_file,
        &lean_file,
        &canon_file,
        &canon_proj,
        toolchain,
        "prov_cut_thm",
        bad_src,
        &mut cb3,
        &mut bad_split,
        true,
        0,
        None,
        false,
    )
    .is_err());

    // Now verify the valid theorem: zero sub-shards may be counted as cached hits, and after
    // verification all `fission-v3:` sub-shard receipts carry current provenance.
    fs::write(&lean_file, src).unwrap();
    let mut cb3_ok = None;
    let t0_ok = Instant::now();
    let ok_json = check_single_decl(
        &mut store,
        true,
        false,
        false,
        &test_kp,
        &t0_ok,
        &lean_file,
        &lean_file,
        &canon_file,
        &canon_proj,
        toolchain,
        "prov_cut_thm",
        src.to_string(),
        &mut cb3_ok,
        &mut split,
        true,
        0,
        None,
        false,
    )
    .unwrap();
    assert_eq!(ok_json["status"], "theorem_verified");
    assert_eq!(ok_json["fission_cached_subshards"], 0);
    for sub in &subs {
        let v3_key =
            compute_fission_store_key(toolchain, &shard.prefix_env_hash, &sub.sub_shard_key);
        assert!(store_has_provenanced_subshard(&store, &v3_key));
    }

    let _ = fs::remove_dir_all(&tmp_dir);
}

#[test]
fn test_check_deferred_axiom_policy_single_file_cold_and_directory() {
    let _guard = crate::pack::tests::env_test_lock()
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let tmp_dir = std::env::temp_dir().join(format!(
        "turbo_check_deferred_policy_{}_{}",
        std::process::id(),
        pack::next_tmp_id()
    ));
    let _ = fs::remove_dir_all(&tmp_dir);
    let proj = tmp_dir.join("proj");
    fs::create_dir_all(proj.join("Mod")).unwrap();
    fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
    fs::write(
            proj.join("lakefile.toml"),
            "name = \"def_pol\"\ndefaultTargets = [\"Mod\"]\n[[lean_lib]]\nname = \"Mod\"\nglobs = [\"Mod.+\"]\n",
        )
        .unwrap();
    fs::write(
        proj.join("Mod/Ax.lean"),
        "axiom allowedDirAx : True\ntheorem ax_ok : True := allowedDirAx\n",
    )
    .unwrap();
    fs::write(
        proj.join("Mod/Clean.lean"),
        "theorem clean_ok : 1 + 1 = 2 := rfl\n",
    )
    .unwrap();

    let prev_ax = std::env::var_os(crate::splitter::ALLOWED_AXIOMS_ENV);
    std::env::set_var(crate::splitter::ALLOWED_AXIOMS_ENV, "allowedDirAx");
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        // 1. Cold single-file check on fresh `TurboStore` must defer to kernel gate and pass.
        let mut cold_store = TurboStore::open(Some(&tmp_dir.join("store_cold"))).unwrap();
        let file_res = evaluate_check_command_value(
            &mut cold_store,
            proj.join("Mod/Ax.lean"),
            None,
            proj.clone(),
        )
        .expect("cold single-file check should allow custom allowedDirAx");
        assert_eq!(file_res["status"], "file_verified");

        // 2. Directory check must defer `Mod/Ax.lean` to kernel gate and pass (both cold and warm).
        let mut dir_store = TurboStore::open(Some(&tmp_dir.join("store_dir"))).unwrap();
        let dir_res =
            evaluate_check_command_value(&mut dir_store, proj.join("Mod"), None, proj.clone())
                .expect("directory check should allow custom allowedDirAx");
        assert_eq!(dir_res["status"], "file_verified");
        let dir_warm =
            evaluate_check_command_value(&mut dir_store, proj.join("Mod"), None, proj.clone())
                .expect("warm directory check should re-audit deferred file and pass");
        assert_eq!(dir_warm["status"], "file_verified");

        // 3. Disallowed axiom in directory must still be rejected by the kernel gate.
        fs::write(
            proj.join("Mod/Ax.lean"),
            "axiom forbiddenDirAx : False\ntheorem ax_bad : False := forbiddenDirAx\n",
        )
        .unwrap();
        let bad_err =
            evaluate_check_command_value(&mut dir_store, proj.join("Mod"), None, proj.clone())
                .expect_err("directory check must reject unallowed axiom");
        assert!(
            format!("{bad_err:#}").contains("forbiddenDirAx"),
            "unexpected error: {bad_err:#}"
        );
    }));
    match prev_ax {
        Some(v) => std::env::set_var(crate::splitter::ALLOWED_AXIOMS_ENV, v),
        None => std::env::remove_var(crate::splitter::ALLOWED_AXIOMS_ENV),
    }
    let _ = fs::remove_dir_all(&tmp_dir);
    if let Err(p) = res {
        std::panic::resume_unwind(p);
    }
}

#[test]
fn test_check_single_file_remote_http_never_offloads_deferred_hygiene() {
    use std::io::{Read, Write};
    use std::net::TcpListener;
    use std::sync::{
        atomic::{AtomicBool, AtomicUsize, Ordering},
        Arc,
    };

    let _guard = crate::pack::tests::env_test_lock()
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let tmp_dir = std::env::temp_dir().join(format!(
        "turbo_check_remote_deferred_{}_{}",
        std::process::id(),
        pack::next_tmp_id()
    ));
    let _ = fs::remove_dir_all(&tmp_dir);
    let proj = tmp_dir.join("proj");
    fs::create_dir_all(proj.join("Mod")).unwrap();
    fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
    fs::write(
            proj.join("lakefile.toml"),
            "name = \"rem_def_pol\"\ndefaultTargets = [\"Mod\"]\n[[lean_lib]]\nname = \"Mod\"\nglobs = [\"Mod.+\"]\n",
        )
        .unwrap();

    // Bind a mock HTTP server that unconditionally returns `{"ok": true}` and counts hits.
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    listener.set_nonblocking(true).unwrap();
    let addr = listener.local_addr().unwrap();
    let remote_url = format!("http://{addr}");
    let hits = Arc::new(AtomicUsize::new(0));
    let stop = Arc::new(AtomicBool::new(false));
    let hits_bg = Arc::clone(&hits);
    let stop_bg = Arc::clone(&stop);
    let server_handle = std::thread::spawn(move || {
        while !stop_bg.load(Ordering::Acquire) {
            match listener.accept() {
                Ok((mut stream, _)) => {
                    let _ = stream.set_read_timeout(Some(std::time::Duration::from_millis(200)));
                    let mut buf = [0u8; 8192];
                    let _ = stream.read(&mut buf);
                    hits_bg.fetch_add(1, Ordering::SeqCst);
                    let body = r#"{"ok":true,"status":"shard_verified","cache_hit":false,"cache_hits":0,"verified_count":1,"stdout":"","stderr":"","verified_decl_types":{}}"#;
                    let resp = format!(
                            "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{}",
                            body.len(),
                            body
                        );
                    let _ = stream.write_all(resp.as_bytes());
                }
                Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                    std::thread::sleep(std::time::Duration::from_millis(5));
                }
                Err(_) => break,
            }
        }
    });

    let prev_ax = std::env::var_os(crate::splitter::ALLOWED_AXIOMS_ENV);
    std::env::set_var(crate::splitter::ALLOWED_AXIOMS_ENV, "allowedRemoteAx");
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        // 1. File with theorem + disallowed trailing axiom when custom policy is set:
        //    must NEVER hit `remote_http`, and must fail closed under local kernel gate!
        let bad_file = proj.join("Mod/BadTrailingAx.lean");
        fs::write(
            &bad_file,
            "theorem ok_thm : 1 + 1 = 2 := rfl\naxiom forbiddenRemoteAx : False\n",
        )
        .unwrap();
        let mut store = TurboStore::open(Some(&tmp_dir.join("store"))).unwrap();
        crate::module_builder::reset_lake_inputs_tag_memo();
        let bad_err = run_check_command_inner(
            &mut store,
            false,
            true,
            false,
            false,
            bad_file.clone(),
            None,
            proj.clone(),
            None,
            false,
            Some(remote_url.clone()),
            false,
        )
        .expect_err(
            "check_single_file --remote-http must reject disallowed trailing axiom locally",
        );
        assert_eq!(
            hits.load(Ordering::SeqCst),
            0,
            "remote HTTP server must receive 0 requests on deferred-hygiene file"
        );
        assert!(
            format!("{bad_err:#}").contains("forbiddenRemoteAx"),
            "unexpected error: {bad_err:#}"
        );

        // Also verify `check_single_decl` (`--decl ok_thm --remote-http`) refuses to offload
        // when the surrounding file has deferred hygiene!
        let decl_err = run_check_command_inner(
            &mut store,
            false,
            true,
            false,
            false,
            bad_file,
            Some("ok_thm".to_string()),
            proj.clone(),
            None,
            false,
            Some(remote_url.clone()),
            false,
        );
        assert_eq!(
                hits.load(Ordering::SeqCst),
                0,
                "check_single_decl --remote-http must also receive 0 remote HTTP requests on deferred-hygiene file"
            );
        let _ = decl_err;

        // 2. File with custom-allowed axiom must also receive 0 remote HTTP requests and
        //    succeed locally through the whole-file kernel gate.
        let ok_file = proj.join("Mod/AllowedAx.lean");
        fs::write(
            &ok_file,
            "axiom allowedRemoteAx : True\ntheorem ok_allowed : True := allowedRemoteAx\n",
        )
        .unwrap();
        crate::module_builder::reset_lake_inputs_tag_memo();
        let ok_val = run_check_command_inner(
            &mut store,
            false,
            true,
            false,
            false,
            ok_file,
            None,
            proj.clone(),
            None,
            false,
            Some(remote_url.clone()),
            false,
        )
        .expect("check_single_file --remote-http should pass locally for allowedRemoteAx");
        assert_eq!(ok_val["status"], "file_verified");
        assert_eq!(
            hits.load(Ordering::SeqCst),
            0,
            "remote HTTP server must receive 0 requests even when custom axiom is allowed"
        );
    }));

    stop.store(true, Ordering::Release);
    let _ = server_handle.join();
    match prev_ax {
        Some(v) => std::env::set_var(crate::splitter::ALLOWED_AXIOMS_ENV, v),
        None => std::env::remove_var(crate::splitter::ALLOWED_AXIOMS_ENV),
    }
    let _ = fs::remove_dir_all(&tmp_dir);
    if let Err(p) = res {
        std::panic::resume_unwind(p);
    }
}

#[test]
fn test_check_directory_allow_sorry_routes_sorry_files_and_rejects_forbidden_hygiene() {
    let _guard = crate::pack::tests::env_test_lock()
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let tmp_dir = std::env::temp_dir().join(format!(
        "turbo_check_dir_allow_sorry_{}_{}",
        std::process::id(),
        pack::next_tmp_id()
    ));
    let _ = fs::remove_dir_all(&tmp_dir);
    let proj = tmp_dir.join("proj");
    fs::create_dir_all(proj.join("Mod")).unwrap();
    fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
    fs::write(
            proj.join("lakefile.toml"),
            "name = \"dir_sorry\"\ndefaultTargets = [\"Mod\"]\n[[lean_lib]]\nname = \"Mod\"\nglobs = [\"Mod.+\"]\n",
        )
        .unwrap();
    fs::write(
        proj.join("Mod/Clean.lean"),
        "theorem clean_ok : 1 + 1 = 2 := rfl\n",
    )
    .unwrap();
    fs::write(
        proj.join("Mod/Wip.lean"),
        "theorem wip_thm : 1 + 1 = 2 := by sorry\n",
    )
    .unwrap();

    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut store = TurboStore::open(Some(&tmp_dir.join("store"))).unwrap();
        let strict_err = run_check_command_inner(
            &mut store,
            false,
            true,
            false,
            false,
            proj.join("Mod"),
            None,
            proj.clone(),
            None,
            false,
            None,
            false,
        )
        .expect_err("directory check without --allow-sorry must reject sorry");
        assert!(
            format!("{strict_err:#}").contains("sorry"),
            "expected sorry rejection, got: {strict_err:#}"
        );

        let allow_res = run_check_command_inner(
            &mut store,
            false,
            true,
            false,
            false,
            proj.join("Mod"),
            None,
            proj.clone(),
            None,
            false,
            None,
            true,
        )
        .expect("directory check with --allow-sorry must accept sorry-bearing file");
        assert_eq!(allow_res["status"], "verified_modulo_sorry");
        assert_eq!(allow_res["used_sorry"], true);

        let strict_after = run_check_command_inner(
            &mut store,
            false,
            true,
            false,
            false,
            proj.join("Mod"),
            None,
            proj.clone(),
            None,
            false,
            None,
            false,
        )
        .expect_err("directory check without --allow-sorry must not poison strict cache");
        assert!(
            format!("{strict_after:#}").contains("sorry"),
            "expected sorry rejection after --allow-sorry run, got: {strict_after:#}"
        );

        fs::write(
            proj.join("Mod/Wip.lean"),
            "theorem bad_nd : 1 + 1 = 2 := by native_decide\n",
        )
        .unwrap();
        let nd_err = run_check_command_inner(
            &mut store,
            false,
            true,
            false,
            false,
            proj.join("Mod"),
            None,
            proj.clone(),
            None,
            false,
            None,
            true,
        )
        .expect_err("directory check with --allow-sorry must still reject native_decide");
        assert!(
            format!("{nd_err:#}").contains("native_decide"),
            "expected native_decide rejection, got: {nd_err:#}"
        );
    }));
    crate::zygote::purge_snapshot_dir(&tmp_dir);
    if let Err(p) = res {
        std::panic::resume_unwind(p);
    }
}

#[test]
fn test_resolve_check_project_and_target_infers_nested_project_root_when_default_cwd() {
    let tmp_dir = std::env::temp_dir().join(format!(
        "turbo_resolve_check_proj_{}",
        crate::pack::next_tmp_id()
    ));
    let _ = fs::remove_dir_all(&tmp_dir);
    let outer = tmp_dir.join("outer");
    let nested_proj = outer.join("nested").join("proj");
    let nested_sub = nested_proj.join("Sub");
    fs::create_dir_all(&nested_sub).unwrap();
    fs::write(
        outer.join("lean-toolchain"),
        "leanprover/lean4:v4.0.0-outer\n",
    )
    .unwrap();
    fs::write(
        nested_proj.join("lean-toolchain"),
        "leanprover/lean4:v4.99.0-nested-test\n",
    )
    .unwrap();
    let sample_file = nested_proj.join("Sample.lean");
    fs::write(&sample_file, "theorem t : True := trivial\n").unwrap();

    let canon_outer = outer.canonicalize().unwrap();
    let canon_nested = nested_proj.canonicalize().unwrap();

    let (dir_abs, resolved_abs) = resolve_check_project_and_target(&sample_file, Path::new("."));
    assert_eq!(dir_abs, canon_nested);
    assert_eq!(resolved_abs, sample_file);
    assert_eq!(
        detect_toolchain(&dir_abs),
        "leanprover/lean4:v4.99.0-nested-test"
    );

    let missing_lean = nested_sub.join("Missing.lean");
    let (dir_missing, _) = resolve_check_project_and_target(&missing_lean, Path::new("."));
    assert_eq!(dir_missing, canon_nested);
    assert_eq!(
        detect_toolchain(&dir_missing),
        "leanprover/lean4:v4.99.0-nested-test"
    );

    let (dir_subdir, _) = resolve_check_project_and_target(&nested_sub, Path::new("."));
    assert_eq!(dir_subdir, canon_nested);

    let (dir_explicit, _) = resolve_check_project_and_target(&sample_file, &outer);
    assert_eq!(dir_explicit, canon_outer);
    assert_eq!(
        detect_toolchain(&dir_explicit),
        "leanprover/lean4:v4.0.0-outer"
    );

    let _ = fs::remove_dir_all(&tmp_dir);
}

#[test]
fn test_check_single_decl_after_multiline_comment_close_on_same_line() {
    let tmp_dir = std::env::temp_dir().join(format!(
        "turbo_post_comment_decl_check_{}",
        crate::pack::next_tmp_id()
    ));
    let _ = fs::remove_dir_all(&tmp_dir);
    let (store_dir, proj_dir) = (tmp_dir.join("store"), tmp_dir.join("proj"));
    fs::create_dir_all(&store_dir).unwrap();
    fs::create_dir_all(&proj_dir).unwrap();
    let toolchain = "leanprover/lean4:v4.35.0";
    fs::write(proj_dir.join("lean-toolchain"), format!("{toolchain}\n")).unwrap();
    let mut store = TurboStore::open(Some(&store_dir)).unwrap();
    let (_env_vars, lean_bin) =
        crate::pack::resolve_server_lean_env_and_bin(&store, toolchain, "").unwrap();
    if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
        let _ = fs::remove_dir_all(&tmp_dir);
        return;
    }
    let test_kp = crate::kernel::resolve_kernel_engine(
        crate::kernel::KernelEngineSelection::Standard,
        toolchain,
    )
    .unwrap();
    let lean_file = proj_dir.join("PostCommentClose.lean");
    let src =
            "def x := 0\n/- comment\n-/ theorem lost : x = 0 := rfl\n/- infer\n-/ theorem infer_lost : x = 0\n  | => rfl\ntheorem visible : x = 0 := lost\n";
    fs::write(&lean_file, src).unwrap();
    let canon_proj = proj_dir.canonicalize().unwrap_or_else(|_| proj_dir.clone());
    let canon_file = lean_file
        .canonicalize()
        .unwrap_or_else(|_| lean_file.clone());
    let mut split = split_lean_source(src, &[]);
    for sh in &split.shards {
        let att = confirm_decl_identity_with_extra_dirs(
            src,
            sh,
            &canon_proj,
            &canon_file,
            false,
            &[],
            None,
        )
        .unwrap();
        assert_eq!(att.decl_name, sh.decl_name());
    }
    let mut cb3 = None;
    let t0 = Instant::now();
    let ok_json = check_single_decl(
        &mut store,
        true,
        false,
        false,
        &test_kp,
        &t0,
        &lean_file,
        &lean_file,
        &canon_file,
        &canon_proj,
        toolchain,
        "lost",
        src.to_string(),
        &mut cb3,
        &mut split,
        false,
        0,
        None,
        false,
    )
    .unwrap();
    assert_eq!(ok_json["status"], "theorem_verified");
    assert_eq!(ok_json["decl"], "lost");

    // Also confirm full-file batched identity probe confirms all three declarations.
    let shard_refs: Vec<&splitter::TheoremShard> = split.shards.iter().collect();
    let confirmed = confirm_file_decl_identities_with_extra_dirs(
        src,
        &shard_refs,
        &canon_proj,
        &canon_file,
        false,
        &[],
        None,
    )
    .unwrap();
    assert_eq!(
        confirmed
            .iter()
            .map(|c| c.decl_name.as_str())
            .collect::<Vec<_>>(),
        vec!["lost", "infer_lost", "visible"]
    );

    let mutual_file = proj_dir.join("PostCommentMutual.lean");
    let mutual_src =
            "def x := 0\nmutual\n  theorem m1 : x = 0 := rfl\n  /- inner\n  -/ theorem m2 : x = 0 := m1\nend\n";
    fs::write(&mutual_file, mutual_src).unwrap();
    let canon_mut = mutual_file
        .canonicalize()
        .unwrap_or_else(|_| mutual_file.clone());
    let mut_split = split_lean_source(mutual_src, &[]);
    for sh in &mut_split.shards {
        let att = confirm_decl_identity_with_extra_dirs(
            mutual_src,
            sh,
            &canon_proj,
            &canon_mut,
            false,
            &[],
            None,
        )
        .unwrap();
        assert_eq!(att.decl_name, sh.decl_name());
    }

    let same_line_file = proj_dir.join("PostSameLineComment.lean");
    let same_line_src =
            "def y := 0\n/- c -/ theorem same_lost : True := trivial\ntheorem visible : True := trivial\n";
    fs::write(&same_line_file, same_line_src).unwrap();
    let canon_same = same_line_file
        .canonicalize()
        .unwrap_or_else(|_| same_line_file.clone());
    let mut same_split = split_lean_source(same_line_src, &[]);
    let mut same_cb3 = None;
    let same_ok = check_single_decl(
        &mut store,
        true,
        false,
        false,
        &test_kp,
        &t0,
        &same_line_file,
        &same_line_file,
        &canon_same,
        &canon_proj,
        toolchain,
        "same_lost",
        same_line_src.to_string(),
        &mut same_cb3,
        &mut same_split,
        false,
        0,
        None,
        false,
    )
    .unwrap();
    assert_eq!(same_ok["status"], "theorem_verified");
    assert_eq!(same_ok["decl"], "same_lost");

    let same_refs: Vec<&splitter::TheoremShard> = same_split.shards.iter().collect();
    let same_confirmed = confirm_file_decl_identities_with_extra_dirs(
        same_line_src,
        &same_refs,
        &canon_proj,
        &canon_same,
        false,
        &[],
        None,
    )
    .unwrap();
    assert_eq!(
        same_confirmed
            .iter()
            .map(|c| c.decl_name.as_str())
            .collect::<Vec<_>>(),
        vec!["same_lost", "visible"]
    );

    let _ = fs::remove_dir_all(&tmp_dir);
}

#[test]
fn test_cached_directory_check_does_not_require_local_toolchain_compiler() -> Result<()> {
    let tmp_dir = std::env::temp_dir().join(format!(
        "turbo_cached_dir_no_compiler_{}",
        crate::pack::next_tmp_id()
    ));
    let _ = fs::remove_dir_all(&tmp_dir);
    let proj = tmp_dir.join("proj");
    let store_root = tmp_dir.join("store");
    fs::create_dir_all(&proj)?;
    let missing_tc = "leanprover/lean4:v4.99.0-uninstalled-test";
    fs::write(proj.join("lean-toolchain"), format!("{missing_tc}\n"))?;
    let src = "theorem cached_dir_thm : True := trivial\n";
    fs::write(proj.join("Main.lean"), src)?;

    let split = split_lean_source(src, &[]);
    let shard = &split.shards[0];
    let shard_key = compute_shard_key_with_args(missing_tc, shard, &[]);
    let receipt = make_shard_receipt_bytes(
        shard.decl_name(),
        &shard.prefix_env_hash,
        &shard.stmt_hash,
        &shard.proof_hash,
        db::now_unix(),
    )?;

    let mut store = TurboStore::open(Some(&store_root))?;
    store.batch_put_theorem_shards(
        missing_tc,
        &[(shard_key, shard.decl_name().to_string(), receipt, 1)],
    )?;

    let res = run_check_command_inner(
        &mut store,
        true,
        true,
        false,
        false,
        proj.clone(),
        None,
        proj.clone(),
        Some(1),
        false,
        None,
        false,
    );
    match res {
        Ok(val) => {
            assert_eq!(val["status"], "all_shards_cached");
            assert_eq!(val["shard_hits"], 1);
        }
        Err(err) if crate::trusted_tools::git(&proj).is_err() => {
            let msg = format!("{:#}", err);
            assert!(
                msg.contains("has no Lake config: refusing to pass"),
                "cache hit must not resolve a local compiler before the Lake-less dependent gate: {msg}"
            );
            assert!(
                !msg.contains("Could not locate installed `lean` compiler binary"),
                "cache hit resolved a local compiler: {msg}"
            );
        }
        Err(err) => panic!("cached directory check must succeed without local compiler: {err:#}"),
    }

    let _ = fs::remove_dir_all(&tmp_dir);
    Ok(())
}

#[test]
fn test_deep_decl_auto_prefix_outline_olean_without_prebuilt_module() {
    let toolchain = "leanprover/lean4:v4.35.0";
    let tmp_dir = std::env::temp_dir().join(format!(
        "turbo_check_prefix_outline_{}_{}",
        std::process::id(),
        pack::next_tmp_id()
    ));
    let proj_dir = tmp_dir.join("proj");
    let cache_dir = tmp_dir.join("cache");
    fs::create_dir_all(&proj_dir).unwrap();
    fs::create_dir_all(&cache_dir).unwrap();
    fs::write(proj_dir.join("lean-toolchain"), format!("{toolchain}\n")).unwrap();
    fs::write(
        proj_dir.join("lakefile.toml"),
        "name = \"outline_pkg\"\ndefaultTargets = [\"DeepMod\"]\n",
    )
    .unwrap();
    let mut store = TurboStore::open(Some(&cache_dir)).unwrap();
    let Ok((_ev, lean_bin)) = crate::pack::resolve_server_lean_env_and_bin(&store, toolchain, "")
    else {
        let _ = fs::remove_dir_all(&tmp_dir);
        return;
    };
    if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
        let _ = fs::remove_dir_all(&tmp_dir);
        return;
    }
    let Ok(test_kp) = crate::kernel::resolve_kernel_engine(
        crate::kernel::KernelEngineSelection::Standard,
        toolchain,
    ) else {
        let _ = fs::remove_dir_all(&tmp_dir);
        return;
    };

    let mut src = String::from("namespace DeepNs\ndef step (n : Nat) : Nat := n + 1\n");
    for i in 0..18 {
        src.push_str(&format!("theorem pre_{i} : step {i} = {} := rfl\n", i + 1));
    }
    src.push_str("theorem deep_target_ok : step 41 = 42 ∧ pre_17 = pre_17 := ⟨rfl, rfl⟩\n");
    src.push_str("theorem deep_target_sorry : step 0 = 99 := by sorry\n");
    src.push_str("end DeepNs\n");

    let mod_file = proj_dir.join("DeepMod.lean");
    fs::write(&mod_file, &src).unwrap();
    let canon_proj = proj_dir.canonicalize().unwrap_or_else(|_| proj_dir.clone());
    let canon_file = mod_file.canonicalize().unwrap_or_else(|_| mod_file.clone());
    let t0 = Instant::now();
    let mut split = split_lean_source(&src, &[]);
    let mut cb3 = None;

    let plan =
        splitter::build_prefix_outline_plan_with_split(&src, &split, "DeepNs.deep_target_ok")
            .expect("deep declaration should produce a prefix outline plan");
    assert!(plan.outline_source.contains("theorem pre_0"));

    let out_ok = check_single_decl(
        &mut store,
        true,
        false,
        false,
        &test_kp,
        &t0,
        &mod_file,
        &mod_file,
        &canon_file,
        &canon_proj,
        toolchain,
        "DeepNs.deep_target_ok",
        src.clone(),
        &mut cb3,
        &mut split,
        false,
        0,
        None,
        false,
    )
    .expect("deep_target_ok should verify via prefix outline olean");
    assert_eq!(out_ok["status"], "theorem_verified");
    assert_eq!(out_ok["fast_olean_import"], true);

    // Stubbed prefix theorems from the outline must NEVER be published to TheoremProofCAS!
    let pre0_shard = split
        .shards
        .iter()
        .find(|s| s.qualified_name == "DeepNs.pre_0")
        .unwrap();
    let pre0_key = crate::lake_build::compute_shard_key(toolchain, pre0_shard);
    assert!(
        store
            .batch_get_theorem_shards(std::slice::from_ref(&pre0_key), "trusted")
            .unwrap()
            .is_empty(),
        "stubbed outline theorems must never be written to TheoremProofCAS"
    );

    // Sorry-backed target declaration must still fail closed even when importing `_TurboOutline_*`!
    let mut sorry_cb3 = None;
    let err = check_single_decl(
        &mut store,
        true,
        false,
        false,
        &test_kp,
        &t0,
        &mod_file,
        &mod_file,
        &canon_file,
        &canon_proj,
        toolchain,
        "DeepNs.deep_target_sorry",
        src.clone(),
        &mut sorry_cb3,
        &mut split,
        false,
        0,
        None,
        false,
    );
    assert!(
        err.is_err(),
        "sorry-backed target must fail closed under prefix outline import"
    );

    let _ = fs::remove_dir_all(&tmp_dir);
}

#[test]
fn test_remote_http_check_never_stages_cas_blobs_before_attestation_and_reuses_client_attested_receipts(
) -> Result<()> {
    use std::io::{Read, Write};
    use std::net::TcpListener;
    use std::sync::{
        atomic::{AtomicBool, Ordering},
        Arc, Mutex,
    };

    let _guard = crate::pack::tests::env_test_lock()
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let toolchain = include_str!("../../../../lean/lean-toolchain").trim();
    let tmp_dir = std::env::temp_dir().join(format!(
        "turbo_check_post_att_http_{}_{}",
        std::process::id(),
        pack::next_tmp_id()
    ));
    let _ = fs::remove_dir_all(&tmp_dir);
    let proj = tmp_dir.join("proj");
    fs::create_dir_all(proj.join("Mathlib"))?;
    fs::write(proj.join("lean-toolchain"), format!("{toolchain}\n"))?;
    fs::write(
            proj.join("lakefile.toml"),
            "name = \"post_att_pkg\"\ndefaultTargets = [\"Mathlib\", \"Mod\"]\n\n[[lean_lib]]\nname = \"Mathlib\"\nglobs = [\"Mathlib.+\"]\n\n[[lean_lib]]\nname = \"Mod\"\n",
        )?;
    fs::write(
        proj.join("Mathlib/Dummy.lean"),
        "def dummyMath : Nat := 1\n",
    )?;
    let src = "import Mathlib.Dummy\nnamespace PostAtt\ntheorem thm1 : 2 + 2 = 4 := rfl\ntheorem thm2 : 3 + 3 = 6 := rfl\nend PostAtt\n";
    let mod_file = proj.join("Mod.lean");
    fs::write(&mod_file, src)?;

    let probe_cache = tmp_dir.join("probe_cache");
    let mut probe_store = TurboStore::open(Some(&probe_cache))?;
    let Ok((_ev, lean_bin)) =
        crate::pack::resolve_server_lean_env_and_bin(&probe_store, toolchain, "")
    else {
        let _ = fs::remove_dir_all(&tmp_dir);
        return Ok(());
    };
    if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
        let _ = fs::remove_dir_all(&tmp_dir);
        return Ok(());
    }
    crate::module_builder::reset_lake_inputs_tag_memo();
    crate::lake_build::run_build_command(
        &mut probe_store,
        false,
        Vec::new(),
        proj.clone(),
        "trusted".to_string(),
        0,
        false,
    )?;
    assert!(
        proj.join(".lake/build/lib/lean/Mathlib/Dummy.olean")
            .is_file(),
        "Mathlib/Dummy.olean must exist after build"
    );
    drop(probe_store);

    let copy_dir_recursive = |from: &Path, to: &Path| -> Result<()> {
        let mut stack = vec![(from.to_path_buf(), to.to_path_buf())];
        while let Some((src_d, dst_d)) = stack.pop() {
            fs::create_dir_all(&dst_d)?;
            for ent in fs::read_dir(&src_d)? {
                let ent = ent?;
                let p = ent.path();
                let target = dst_d.join(ent.file_name());
                if p.is_dir() {
                    stack.push((p, target));
                } else if p.is_file() {
                    fs::copy(&p, &target)?;
                }
            }
        }
        Ok(())
    };

    let canon_proj = proj.canonicalize().unwrap_or_else(|_| proj.clone());
    let canon_file = mod_file.canonicalize().unwrap_or_else(|_| mod_file.clone());
    let local_lean_path = resolve_remote_lean_path(&canon_proj, None);
    let dep_hashes = compute_imported_olean_interface_hashes(
        src,
        &canon_proj,
        (!local_lean_path.is_empty()).then_some(local_lean_path.as_str()),
    );
    let split = split_lean_source(src, &dep_hashes);
    let shard_refs: Vec<&splitter::TheoremShard> = split.shards.iter().collect();
    let attested = confirm_file_decl_identities_with_budget(
        src,
        &shard_refs,
        &canon_proj,
        &canon_file,
        false,
        None,
    )?;
    assert_eq!(attested.len(), 2);
    let kth1 = attested[0].kernel_type_hash.clone();
    let kth2 = attested[1].kernel_type_hash.clone();
    let wrong_kth = "0".repeat(64);

    let count_blob_files = |root: &Path| -> usize {
        let blobs_dir = root.join("blobs");
        if !blobs_dir.exists() {
            return 0;
        }
        let mut n = 0usize;
        if let Ok(rd) = fs::read_dir(&blobs_dir) {
            for ent in rd.flatten() {
                let p = ent.path();
                if p.is_dir() {
                    if let Ok(sub) = fs::read_dir(&p) {
                        n += sub.flatten().filter(|f| f.path().is_file()).count();
                    }
                } else if p.is_file() {
                    n += 1;
                }
            }
        }
        n
    };
    let count_db_rows = |st: &TurboStore| -> (i64, i64) {
        let acts: i64 = st
            .conn
            .query_row("SELECT COUNT(*) FROM actions", [], |r| r.get(0))
            .unwrap_or(0);
        let blobs: i64 = st
            .conn
            .query_row("SELECT COUNT(*) FROM blobs", [], |r| r.get(0))
            .unwrap_or(0);
        (acts, blobs)
    };

    #[derive(Clone)]
    enum MockReply {
        CloseImmediately,
        StatusBody(u16, String),
    }

    let listener = TcpListener::bind("127.0.0.1:0")?;
    listener.set_nonblocking(true)?;
    let remote_url = format!("http://{}", listener.local_addr()?);
    let scripted: Arc<Mutex<std::collections::VecDeque<MockReply>>> =
        Arc::new(Mutex::new(std::collections::VecDeque::new()));
    let stop = Arc::new(AtomicBool::new(false));
    let scripted_bg = Arc::clone(&scripted);
    let stop_bg = Arc::clone(&stop);
    let server_handle = std::thread::spawn(move || {
        while !stop_bg.load(Ordering::Acquire) {
            match listener.accept() {
                Ok((mut stream, _)) => {
                    let _ = stream.set_read_timeout(Some(std::time::Duration::from_millis(250)));
                    let mut buf = [0u8; 16384];
                    let _ = stream.read(&mut buf);
                    let reply = scripted_bg
                        .lock()
                        .unwrap_or_else(|e| e.into_inner())
                        .pop_front()
                        .unwrap_or(MockReply::StatusBody(500, "unexpected".to_string()));
                    match reply {
                        MockReply::CloseImmediately => {
                            drop(stream);
                        }
                        MockReply::StatusBody(code, body) => {
                            let reason = if code == 200 {
                                "OK"
                            } else {
                                "Internal Server Error"
                            };
                            let resp = format!(
                                    "HTTP/1.1 {code} {reason}\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{body}",
                                    body.len()
                                );
                            let _ = stream.write_all(resp.as_bytes());
                        }
                    }
                }
                Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                    std::thread::sleep(std::time::Duration::from_millis(5));
                }
                Err(_) => break,
            }
        }
    });

    let test_res = (|| -> Result<()> {
        // 1) `try_stateless_remote_check` batch path: failed/malformed/unattested/mismatched responses
        //    must NOT write any new rows or blob files under `cache_root/blobs/`.
        let stateless_batch_cache = tmp_dir.join("stateless_batch_cache");
        copy_dir_recursive(&probe_cache, &stateless_batch_cache)?;
        let baseline_blobs = count_blob_files(&stateless_batch_cache);
        let baseline_rows = {
            let st = TurboStore::open(Some(&stateless_batch_cache))?;
            count_db_rows(&st)
        };
        {
            let mut q = scripted.lock().unwrap_or_else(|e| e.into_inner());
            q.push_back(MockReply::CloseImmediately);
            q.push_back(MockReply::StatusBody(500, r#"{"error":"boom"}"#.into()));
            q.push_back(MockReply::StatusBody(200, "not-json".into()));
            q.push_back(MockReply::StatusBody(
                    200,
                    r#"{"ok":false,"verified_count":0,"cache_hits":0,"elapsed_ms":1.0,"exit_code":1,"stdout":"","stderr":"bad","error":"bad","verified_decl_types":{}}"#.into(),
                ));
            q.push_back(MockReply::StatusBody(
                    200,
                    r#"{"ok":true,"verified_count":2,"cache_hits":0,"elapsed_ms":1.0,"exit_code":0,"stdout":"","stderr":"","error":null,"verified_decl_types":{}}"#.into(),
                ));
            q.push_back(MockReply::StatusBody(
                200,
                serde_json::json!({
                    "ok": true,
                    "verified_count": 2,
                    "cache_hits": 0,
                    "elapsed_ms": 1.0,
                    "exit_code": 0,
                    "stdout": "",
                    "stderr": "",
                    "error": null,
                    "verified_decl_types": {
                        "PostAtt.thm1": kth1,
                        "PostAtt.thm2": wrong_kth
                    }
                })
                .to_string(),
            ));
        }
        for attempt in 0..6 {
            let ok = try_stateless_remote_check(
                &stateless_batch_cache,
                false,
                &mod_file,
                None,
                &proj,
                Some(2),
                &remote_url,
            )?;
            assert!(!ok, "stateless batch attempt {attempt} must fall back");
            let st_check = TurboStore::open(Some(&stateless_batch_cache))?;
            assert_eq!(
                count_db_rows(&st_check),
                baseline_rows,
                "stateless batch attempt {attempt} must not insert DB rows before attestation"
            );
            drop(st_check);
            assert_eq!(
                count_blob_files(&stateless_batch_cache),
                baseline_blobs,
                "stateless batch attempt {attempt} must write 0 new CAS blob files"
            );
        }
        // Valid attested batch response publishes both receipts.
        scripted
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .push_back(MockReply::StatusBody(
                200,
                serde_json::json!({
                    "ok": true,
                    "verified_count": 2,
                    "cache_hits": 0,
                    "elapsed_ms": 4.0,
                    "exit_code": 0,
                    "stdout": "",
                    "stderr": "",
                    "error": null,
                    "verified_decl_types": {
                        "PostAtt.thm1": kth1,
                        "PostAtt.thm2": kth2
                    }
                })
                .to_string(),
            ));
        assert!(try_stateless_remote_check(
            &stateless_batch_cache,
            false,
            &mod_file,
            None,
            &proj,
            Some(2),
            &remote_url,
        )?);
        let st_batch = TurboStore::open(Some(&stateless_batch_cache))?;
        assert_eq!(
            count_db_rows(&st_batch),
            (baseline_rows.0 + 2, baseline_rows.1 + 2)
        );
        assert_eq!(count_blob_files(&stateless_batch_cache), baseline_blobs + 2);
        drop(st_batch);

        // 2) `try_stateless_remote_single_decl_check` (`decl = Some(...)`): zero new CAS artifacts before
        //    attestation, followed by publication on valid attested response (plus pure empty-cache check
        //    on a standalone `import Init` + `import Mathlib.Dummy` pruned module if needed).
        let stateless_decl_cache = tmp_dir.join("stateless_decl_cache");
        copy_dir_recursive(&probe_cache, &stateless_decl_cache)?;
        let decl_baseline_blobs = count_blob_files(&stateless_decl_cache);
        let decl_baseline_rows = {
            let st = TurboStore::open(Some(&stateless_decl_cache))?;
            count_db_rows(&st)
        };
        {
            let mut q = scripted.lock().unwrap_or_else(|e| e.into_inner());
            q.clear();
            q.push_back(MockReply::CloseImmediately);
            q.push_back(MockReply::StatusBody(500, "err".into()));
            q.push_back(MockReply::StatusBody(200, "{bad_json".into()));
            q.push_back(MockReply::StatusBody(
                200,
                r#"{"status":"remote_theorem_failed"}"#.into(),
            ));
            q.push_back(MockReply::StatusBody(
                200,
                r#"{"status":"remote_theorem_verified"}"#.into(),
            ));
            q.push_back(MockReply::StatusBody(
                200,
                serde_json::json!({
                    "status": "remote_theorem_verified",
                    "kernel_type_hash": wrong_kth
                })
                .to_string(),
            ));
        }
        for attempt in 0..6 {
            let ok = try_stateless_remote_check(
                &stateless_decl_cache,
                false,
                &mod_file,
                Some("PostAtt.thm1"),
                &proj,
                Some(1),
                &remote_url,
            )?;
            assert!(!ok, "stateless decl attempt {attempt} must fall back");
            let st_check = TurboStore::open(Some(&stateless_decl_cache))?;
            assert_eq!(
                count_db_rows(&st_check),
                decl_baseline_rows,
                "stateless decl attempt {attempt} must not insert DB rows before attestation"
            );
            drop(st_check);
            assert_eq!(
                count_blob_files(&stateless_decl_cache),
                decl_baseline_blobs,
                "stateless decl attempt {attempt} must write 0 new CAS blob files"
            );
        }
        scripted
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .push_back(MockReply::StatusBody(
                200,
                serde_json::json!({
                    "status": "remote_theorem_verified",
                    "kernel_type_hash": kth1,
                    "server_elapsed_ms": 3
                })
                .to_string(),
            ));
        assert!(try_stateless_remote_check(
            &stateless_decl_cache,
            false,
            &mod_file,
            Some("PostAtt.thm1"),
            &proj,
            Some(1),
            &remote_url,
        )?);
        let st_decl = TurboStore::open(Some(&stateless_decl_cache))?;
        assert_eq!(
            count_db_rows(&st_decl),
            (decl_baseline_rows.0 + 1, decl_baseline_rows.1 + 1)
        );
        assert_eq!(
            count_blob_files(&stateless_decl_cache),
            decl_baseline_blobs + 1
        );
        drop(st_decl);

        // 2b) Pure empty-cache stateless check (`import Init /- \nimport Mathlib -/`):
        //     `dep_hashes` is empty (`Init` only) while `pruned_imports_shard_source` succeeds,
        //     so `try_stateless_remote_check` needs NO `TurboStore` at all before attestation
        //     and must NOT create `state.db` or `blobs/` on any rejected HTTP reply!
        let pure_src = "import Init /-\nimport Mathlib -/\nnamespace PureAtt\ntheorem pthm1 : 5 + 5 = 10 := rfl\nend PureAtt\n";
        if splitter::build_pruned_imports_shard_source(
            pure_src,
            &HashSet::from(["_root_.PureAtt.pthm1".to_string()]),
        )
        .is_some()
        {
            let pure_file = proj.join("PureMod.lean");
            fs::write(&pure_file, pure_src)?;
            let empty_stateless_cache = tmp_dir.join("empty_stateless_cache");
            {
                let mut q = scripted.lock().unwrap_or_else(|e| e.into_inner());
                q.clear();
                q.push_back(MockReply::StatusBody(500, "boom".into()));
                q.push_back(MockReply::StatusBody(500, "boom".into()));
            }
            assert!(!try_stateless_remote_check(
                &empty_stateless_cache,
                false,
                &pure_file,
                None,
                &proj,
                Some(1),
                &remote_url,
            )?);
            assert!(
                !empty_stateless_cache.join("state.db").exists(),
                "empty stateless batch check must not create state.db before attestation"
            );
            assert!(!try_stateless_remote_check(
                &empty_stateless_cache,
                false,
                &pure_file,
                Some("PureAtt.pthm1"),
                &proj,
                Some(1),
                &remote_url,
            )?);
            assert!(
                !empty_stateless_cache.join("state.db").exists(),
                "empty stateless single-decl check must not create state.db before attestation"
            );
            let _ = fs::remove_file(&pure_file);
        }

        // 3) Warm `check_single_decl` (`run_check_command_inner` with `db_warm_on_open = true`):
        //    failed/malformed/mismatched HTTP responses (including fallback candidate attempts)
        //    leave 0 blobs and 0 actions in `TurboStore`.
        let warm_decl_cache = tmp_dir.join("warm_decl_cache");
        let mut warm_store = TurboStore::open(Some(&warm_decl_cache))?;
        for replies in [
            vec![MockReply::CloseImmediately, MockReply::CloseImmediately],
            vec![
                MockReply::StatusBody(200, "{not-json".into()),
                MockReply::StatusBody(200, "{not-json".into()),
            ],
            vec![
                MockReply::StatusBody(
                    200,
                    serde_json::json!({
                        "status": "remote_theorem_verified",
                        "kernel_type_hash": wrong_kth
                    })
                    .to_string(),
                ),
                MockReply::StatusBody(
                    200,
                    serde_json::json!({
                        "status": "remote_theorem_verified",
                        "kernel_type_hash": wrong_kth
                    })
                    .to_string(),
                ),
            ],
        ] {
            {
                let mut q = scripted.lock().unwrap_or_else(|e| e.into_inner());
                q.clear();
                q.extend(replies);
            }
            let err = run_check_command_inner(
                &mut warm_store,
                true,
                true,
                false,
                false,
                mod_file.clone(),
                Some("PostAtt.thm1".to_string()),
                proj.clone(),
                None,
                false,
                Some(remote_url.clone()),
                false,
            );
            assert!(
                err.is_err(),
                "warm check_single_decl must fail on bad remote reply"
            );
            assert_eq!(
                count_db_rows(&warm_store),
                (0, 0),
                "failed warm check_single_decl must insert 0 DB rows"
            );
            assert_eq!(
                count_blob_files(&warm_decl_cache),
                0,
                "failed warm check_single_decl must stage 0 CAS blob files"
            );
        }
        {
            let mut q = scripted.lock().unwrap_or_else(|e| e.into_inner());
            q.clear();
            q.push_back(MockReply::StatusBody(
                200,
                serde_json::json!({
                    "status": "remote_theorem_verified",
                    "decl_types": { "PostAtt.thm1": kth1 },
                    "server_elapsed_ms": 2
                })
                .to_string(),
            ));
        }
        let ok_decl_val = run_check_command_inner(
            &mut warm_store,
            true,
            true,
            false,
            false,
            mod_file.clone(),
            Some("PostAtt.thm1".to_string()),
            proj.clone(),
            None,
            false,
            Some(remote_url.clone()),
            false,
        )?;
        assert_eq!(ok_decl_val["status"], "remote_theorem_verified");
        assert_eq!(count_db_rows(&warm_store), (1, 1));
        assert_eq!(count_blob_files(&warm_decl_cache), 1);

        // 4) Warm `check_single_file` remote batch offload publishes `client-attested-v1:<shard_key>`
        //    and subsequent warm `check_single_file` + `check_single_decl` reuse it with 0 HTTP calls,
        //    while directory-level unattested `batch_get_theorem_shards(&raw_keys, "trusted")` stays empty!
        let batch_reuse_cache = tmp_dir.join("batch_reuse_cache");
        let mut reuse_store = TurboStore::open(Some(&batch_reuse_cache))?;
        {
            let mut q = scripted.lock().unwrap_or_else(|e| e.into_inner());
            q.clear();
            q.push_back(MockReply::StatusBody(
                200,
                serde_json::json!({
                    "ok": true,
                    "verified_count": 2,
                    "cache_hits": 0,
                    "elapsed_ms": 3.0,
                    "exit_code": 0,
                    "stdout": "",
                    "stderr": "",
                    "error": null,
                    "verified_decl_types": {
                        "PostAtt.thm1": kth1,
                        "PostAtt.thm2": kth2
                    }
                })
                .to_string(),
            ));
        }
        let first_file_val = run_check_command_inner(
            &mut reuse_store,
            true,
            true,
            false,
            false,
            mod_file.clone(),
            None,
            proj.clone(),
            Some(2),
            false,
            Some(remote_url.clone()),
            false,
        )?;
        assert_eq!(first_file_val["status"], "file_verified");
        assert_eq!(first_file_val["mode"], "remote_coalesced_shards");
        assert_eq!(first_file_val["shard_hits"], 0);
        assert_eq!(first_file_val["shard_misses"], 2);

        let raw_keys: Vec<String> = split
            .shards
            .iter()
            .map(|s| compute_shard_key_with_args(toolchain, s, &[]))
            .collect();
        assert!(
                reuse_store
                    .batch_get_theorem_shards(&raw_keys, "trusted")?
                    .is_empty(),
                "raw unattested shard keys must remain absent so unattested batch callers cannot trust them"
            );

        // Queue is empty: any HTTP call would hit default 500 and fail!
        scripted.lock().unwrap_or_else(|e| e.into_inner()).clear();
        let second_file_val = run_check_command_inner(
            &mut reuse_store,
            true,
            true,
            false,
            false,
            mod_file.clone(),
            None,
            proj.clone(),
            Some(2),
            false,
            Some(remote_url.clone()),
            false,
        )?;
        assert_eq!(second_file_val["status"], "all_shards_cached");
        assert_eq!(second_file_val["shard_hits"], 2);
        assert_eq!(second_file_val["shard_misses"], 0);

        let warm_remote_decl_hit = run_check_command_inner(
            &mut reuse_store,
            true,
            true,
            false,
            false,
            mod_file.clone(),
            Some("PostAtt.thm2".to_string()),
            proj.clone(),
            None,
            false,
            Some(remote_url.clone()),
            false,
        )?;
        assert_eq!(warm_remote_decl_hit["status"], "theorem_cache_hit");

        let warm_local_decl_hit = run_check_command_inner(
            &mut reuse_store,
            true,
            true,
            false,
            false,
            mod_file.clone(),
            Some("PostAtt.thm1".to_string()),
            proj.clone(),
            None,
            false,
            None,
            false,
        )?;
        assert_eq!(warm_local_decl_hit["status"], "theorem_cache_hit");

        Ok(())
    })();

    stop.store(true, Ordering::Release);
    let _ = server_handle.join();
    let _ = fs::remove_dir_all(&tmp_dir);
    test_res
}
