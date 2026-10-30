use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Command;

const TURBO_EXPORTS: &[&str] = &[
    "turbo_spec_is_closed_section_needed",
    "turbo_spec_precompute_min_needed_idx",
    "turbo_spec_can_fission_have",
    "turbo_spec_sanitize_phase_options",
    "turbo_spec_sanitize_warning_as_error",
    "turbo_spec_sanitize_forbid_sorry_ax",
    "turbo_spec_is_sound_decl_summary",
    "turbo_spec_check_statement_pinned",
    "turbo_spec_node_effective_cost",
    "turbo_spec_is_remote_eligible",
    "turbo_spec_should_switch_route",
    "turbo_spec_classify_compute_target",
    "turbo_spec_splitmix64",
    "turbo_spec_boundary_u256_limb",
    "turbo_spec_gen_u256_limb",
    "turbo_spec_u256_lt",
    "turbo_spec_eval_u64_binop",
    "turbo_spec_step_verdict_consistent",
    "turbo_spec_affine_step_budget",
    "turbo_spec_loop_step_budget",
    "turbo_spec_check_step_budget_le",
    "turbo_spec_riscv_div_u64",
    "turbo_spec_riscv_rem_u64",
    "turbo_spec_zygote_lca_reuse_safe",
    "turbo_spec_audit_witness_gate",
    "turbo_spec_effective_cone_job_cap",
    "turbo_spec_is_scope_isolated_for_fast_olean",
    "turbo_spec_matryoshka_tier_router",
    "turbo_spec_verify_dag_schedule_step",
    "turbo_spec_verify_module_cache_key",
    "turbo_spec_verify_module_artifact_set",
    "turbo_spec_verify_static_lake_config",
    "turbo_spec_verify_slice_pass_gate",
    "turbo_spec_verify_tlz1_token",
    "turbo_spec_verify_lexer_comment_guard",
    "turbo_spec_verify_farkas_step",
    "turbo_spec_verify_ident_bloom",
    "turbo_spec_verify_audit_materialize_gate",
    "turbo_spec_verify_pack_trust_admission",
    "turbo_spec_verify_hygiene_item_admitted",
    "turbo_spec_combined_step",
    "leansys_verify_slice_bounds",
    "leansys_verify_wal_frame",
    "leansys_verify_cas_digest",
    "leansys_check_http_bounds",
    "leansys_verify_jsonl_tape",
    "leansys_verify_ring_cursor",
    "leansys_verify_sst_block",
    "leansys_verify_poll_interest",
    "leansys_verify_rlimit_budget",
    "leansys_verify_composite_key_order",
    "leansys_verify_token_auth",
    "leansys_verify_log_window",
    "leansys_verify_jsonrpc_frame",
    "leansys_mix64_word",
    "leansys_gate_admit",
    "leansys_verify_par_chunk",
    "leansys_verify_arena_disjoint",
    "leansys_verify_snapshot_visibility",
    "leansys_verify_http_route_match",
    "leansys_verify_counterexample_triage",
    "leansys_verify_dag_wave_step",
    "leansys_verify_ios_jetsam_budget",
    "leansys_verify_worker_budget",
    "leansys_verify_page_aligned_buffer",
    "leansys_select_isa",
    "leansys_verify_isa_selection",
    "leannative_pack_slice_span_u64",
    "leannative_eval_u64_binop",
    "leannative_has_domain_hazard_u64",
    "leannative_fastcheck_rewrite_step",
    "leannative_certify_cex_witnesses",
    "leannative_verify_parfor_chunk_partition",
    "leannative_verify_rc_mode_safe",
    "leannative_verify_backend_choice",
    "lean_native_ntt_butterfly_fused_2layer_slice",
];

fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for &b in bytes {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

fn find_elan_tool(tool_name: &str) -> Option<PathBuf> {
    if tool_name == "lean" {
        if let Ok(explicit) = env::var("TURBO_LEAN_BIN") {
            let p = PathBuf::from(explicit);
            if p.is_file() {
                return Some(p);
            }
        }
    }
    if let Ok(path_var) = env::var("PATH") {
        for dir in env::split_paths(&path_var) {
            let cand = dir.join(tool_name);
            if cand.is_file() {
                return Some(cand);
            }
        }
    }
    let mut roots = Vec::new();
    if let Ok(elan_home) = env::var("ELAN_HOME") {
        roots.push(PathBuf::from(elan_home));
    }
    if let Ok(home) = env::var("HOME") {
        roots.push(PathBuf::from(home).join(".elan"));
    }
    roots.push(PathBuf::from("/var/lib/sandboxed-node/caches/elan"));

    for root in roots {
        let bin_cand = root.join("bin").join(tool_name);
        if bin_cand.is_file() {
            return Some(bin_cand);
        }
        let tc_dir = root.join("toolchains");
        if let Ok(entries) = fs::read_dir(&tc_dir) {
            let mut dirs: Vec<PathBuf> = entries.flatten().map(|e| e.path()).collect();
            dirs.sort();
            dirs.reverse();
            for dir in dirs {
                let cand = dir.join("bin").join(tool_name);
                if cand.is_file() {
                    return Some(cand);
                }
            }
        }
    }
    None
}

fn main() {
    println!("cargo:rerun-if-changed=../../lean/TurboLean/PolicyGates.lean");
    println!("cargo:rerun-if-changed=../../lean/TurboLean/Kernel.lean");
    println!("cargo:rerun-if-changed=../../lean/TurboLean/Spec.lean");
    println!("cargo:rerun-if-changed=../../lean/LeanNative/Spec.lean");
    println!("cargo:rerun-if-changed=../../lean/lean-toolchain");
    println!("cargo:rerun-if-changed=../../lean/lakefile.lean");
    println!("cargo:rerun-if-changed=build.rs");

    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let repo_root = manifest_dir
        .parent()
        .and_then(|p| p.parent())
        .unwrap_or(&manifest_dir);
    let lean_dir = repo_root.join("lean");
    let policy_gates_lean = lean_dir.join("TurboLean/PolicyGates.lean");
    let kernel_lean = lean_dir.join("TurboLean/Kernel.lean");
    let spec_lean = lean_dir.join("TurboLean/Spec.lean");
    let leannative_spec_lean = lean_dir.join("LeanNative/Spec.lean");
    let turbo_fastcheck_lean = lean_dir.join("TurboLean/FastCheck.lean");

    assert!(
        policy_gates_lean.is_file() && kernel_lean.is_file() && spec_lean.is_file() && leannative_spec_lean.is_file() && turbo_fastcheck_lean.is_file(),
        "missing TurboLean/PolicyGates.lean, TurboLean/Kernel.lean, TurboLean/Spec.lean, TurboLean/FastCheck.lean, or LeanNative/Spec.lean under {}",
        lean_dir.display()
    );
    let turbo_fc_src = fs::read_to_string(&turbo_fastcheck_lean).unwrap_or_default();
    assert!(
        turbo_fc_src.contains("import LeanNative.Backend.FastCheck") && !turbo_fc_src.contains("structure Word256"),
        "TurboLean/FastCheck.lean must import `LeanNative.Backend.FastCheck` and must not duplicate `structure Word256`"
    );

    let lean_bin = find_elan_tool("lean").unwrap_or_else(|| {
        panic!(
            "Lean 4 toolchain required to build turbo-lean C-ABI kernel (`lean` not found in TURBO_LEAN_BIN, PATH, ELAN_HOME, or ~/.elan)"
        )
    });

    let lean_build_dir = out_dir.join("lean_build");
    let turbo_olean_dir = lean_build_dir.join("TurboLean");
    fs::create_dir_all(&turbo_olean_dir).unwrap();
    let policy_gates_olean = turbo_olean_dir.join("PolicyGates.olean");
    let kernel_olean = turbo_olean_dir.join("Kernel.olean");
    let spec_olean = turbo_olean_dir.join("Spec.olean");
    let kernel_c_path = out_dir.join("TurboLean_Kernel_generated.c");

    let mut lean_sys_lib = lean_dir.join(".lake/packages/lean-sys/.lake/build/lib/lean");
    let lean_sys_spec_c = lean_dir.join(".lake/packages/lean-sys/.lake/build/ir/LeanSys/Spec.c");
    let leannative_spec_c = lean_dir.join(".lake/build/ir/LeanNative/Spec.c");
    let c_missing_expected_exports = |c_path: &std::path::Path, prefix: &str| -> bool {
        let Ok(src) = fs::read_to_string(c_path) else {
            return true;
        };
        TURBO_EXPORTS
            .iter()
            .filter(|sym| sym.starts_with(prefix))
            .any(|sym| !src.contains(sym))
    };
    if !lean_sys_lib.join("LeanSys.olean").is_file()
        || !lean_sys_lib.join("LeanSys/Gate.olean").is_file()
        || c_missing_expected_exports(&lean_sys_spec_c, "leansys_")
        || c_missing_expected_exports(&leannative_spec_c, "leannative_")
        || c_missing_expected_exports(&leannative_spec_c, "lean_native_")
    {
        if let Some(lake_bin) = find_elan_tool("lake") {
            let _ = Command::new(&lake_bin)
                .current_dir(&lean_dir)
                .args(["build", "LeanSys", "LeanNative.Spec"])
                .status();
        }
    }
    let lake_manifest_path = lean_dir.join("lake-manifest.json");
    if lake_manifest_path.is_file() {
        let manifest_text = fs::read_to_string(&lake_manifest_path).unwrap_or_default();
        assert!(
            manifest_text.contains("lean-sys"),
            "lean/lake-manifest.json missing `lean-sys` package pin"
        );
    }
    let lean_sys_olean = lean_sys_lib.join("LeanSys.olean");
    let lean_sys_gate_olean = lean_sys_lib.join("LeanSys/Gate.olean");
    if lean_sys_olean.is_file() && lean_sys_gate_olean.is_file() {
        let olean_bytes = fs::read(&lean_sys_olean).unwrap_or_default();
        let gate_bytes = fs::read(&lean_sys_gate_olean).unwrap_or_default();
        let digest = fnv1a64(&olean_bytes) ^ fnv1a64(&gate_bytes).rotate_left(13);
        assert!(
            !olean_bytes.is_empty() && !gate_bytes.is_empty() && digest != 0,
            "LeanSys.olean / LeanSys/Gate.olean digest verification failed"
        );
        println!("cargo:rustc-env=LEANSYS_OLEAN_DIGEST={digest:016x}");
    }
    let mut lean_path_dirs = vec![lean_build_dir.clone()];
    lean_sys_lib = lean_dir.join(".lake/packages/lean-sys/.lake/build/lib/lean");
    if lean_sys_lib.is_dir() {
        lean_path_dirs.push(lean_sys_lib);
    }
    let root_lib = lean_dir.join(".lake/build/lib/lean");
    if root_lib.is_dir() {
        lean_path_dirs.push(root_lib);
    }
    let spec_lean_path = env::join_paths(&lean_path_dirs).unwrap();

    let policy_status = Command::new(&lean_bin)
        .current_dir(&lean_dir)
        .arg("TurboLean/PolicyGates.lean")
        .arg("-o")
        .arg(&policy_gates_olean)
        .arg("-c")
        .arg(&kernel_c_path)
        .status()
        .unwrap_or_else(|e| panic!("failed to invoke lean on TurboLean/PolicyGates.lean: {e}"));
    assert!(
        policy_status.success() && kernel_c_path.is_file(),
        "lean failed to compile TurboLean/PolicyGates.lean to C"
    );

    let kernel_status = Command::new(&lean_bin)
        .current_dir(&lean_dir)
        .env("LEAN_PATH", &spec_lean_path)
        .arg("TurboLean/Kernel.lean")
        .arg("-o")
        .arg(&kernel_olean)
        .status()
        .unwrap_or_else(|e| panic!("failed to invoke lean on TurboLean/Kernel.lean: {e}"));
    assert!(
        kernel_status.success() && kernel_olean.is_file(),
        "lean failed to compile TurboLean/Kernel.lean"
    );

    let spec_status = Command::new(&lean_bin)
        .current_dir(&lean_dir)
        .env("LEAN_PATH", &spec_lean_path)
        .arg("TurboLean/Spec.lean")
        .arg("-o")
        .arg(&spec_olean)
        .status()
        .unwrap_or_else(|e| panic!("failed to invoke lean on TurboLean/Spec.lean: {e}"));
    assert!(
        spec_status.success() && spec_olean.is_file(),
        "lean failed to typecheck proofs in TurboLean/Spec.lean"
    );

    let c_text = fs::read_to_string(&kernel_c_path)
        .unwrap_or_else(|e| panic!("failed to read generated C file: {e}"));
    let leansys_c_text = fs::read_to_string(&lean_sys_spec_c)
        .unwrap_or_else(|e| panic!("failed to read LeanSys/Spec.c: {e}"));
    let leannative_c_text = fs::read_to_string(&leannative_spec_c)
        .unwrap_or_else(|e| panic!("failed to read LeanNative/Spec.c: {e}"));
    assert!(
        !c_text.lines().any(|l| {
            l.starts_with("LEAN_EXPORT ")
                && (l.contains("leansys_")
                    || l.contains("leannative_")
                    || l.contains("lean_native_"))
        }),
        "TurboLean/Kernel.lean must not redefine canonical `leansys_*`, `leannative_*`, or `lean_native_*` C-ABI exports"
    );
    for sym in TURBO_EXPORTS {
        let in_kernel = c_text.contains(sym);
        let in_leansys = leansys_c_text.contains(sym);
        let in_leannative = leannative_c_text.contains(sym);
        let owner_count = (in_kernel as u8) + (in_leansys as u8) + (in_leannative as u8);
        assert_eq!(
            owner_count, 1,
            "C-ABI symbol `{sym}` must have a single canonical owner (in_kernel={in_kernel}, in_leansys={in_leansys}, in_leannative={in_leannative})"
        );
    }
    let filter_exports = |src: &str| -> String {
        src.lines()
            .map(|line| {
                if let Some(rest) = line.strip_prefix("LEAN_EXPORT ") {
                    if !TURBO_EXPORTS.iter().any(|sym| rest.contains(sym)) {
                        return format!("static __attribute__((unused)) {rest}");
                    }
                }
                line.to_string()
            })
            .collect::<Vec<_>>()
            .join("\n")
            + "\n"
    };
    let filtered_c = filter_exports(&c_text);
    fs::write(&kernel_c_path, &filtered_c)
        .unwrap_or_else(|e| panic!("failed to write filtered C file: {e}"));
    let leansys_c_filtered_path = out_dir.join("LeanSys_Spec_generated.c");
    fs::write(&leansys_c_filtered_path, filter_exports(&leansys_c_text))
        .unwrap_or_else(|e| panic!("failed to write filtered LeanSys/Spec.c: {e}"));
    let leannative_c_filtered_path = out_dir.join("LeanNative_Spec_generated.c");
    fs::write(
        &leannative_c_filtered_path,
        filter_exports(&leannative_c_text),
    )
    .unwrap_or_else(|e| panic!("failed to write filtered LeanNative/Spec.c: {e}"));

    let lean_prefix = Command::new(&lean_bin)
        .current_dir(&lean_dir)
        .arg("--print-prefix")
        .output()
        .unwrap_or_else(|e| panic!("lean --print-prefix failed: {e}"));
    assert!(lean_prefix.status.success(), "lean --print-prefix failed");
    let prefix = String::from_utf8_lossy(&lean_prefix.stdout)
        .trim()
        .to_string();
    let include = PathBuf::from(&prefix).join("include");

    let raw_obj_path = out_dir.join("TurboLean_Kernel_raw.o");
    let leansys_raw_obj_path = out_dir.join("LeanSys_Spec_raw.o");
    let leannative_raw_obj_path = out_dir.join("LeanNative_Spec_raw.o");
    let gc_obj_path = out_dir.join("TurboLean_Kernel_gc.o");
    let lib_path = out_dir.join("libturbo_spec_cabi.a");

    let mut compiled = false;
    for compiler in ["cc", "clang", "gcc"] {
        let st1 = Command::new(compiler)
            .args([
                "-O3",
                "-fPIC",
                "-ffunction-sections",
                "-fdata-sections",
                "-c",
            ])
            .arg(format!("-I{}", include.display()))
            .arg(&kernel_c_path)
            .arg("-o")
            .arg(&raw_obj_path)
            .status();
        let st2 = Command::new(compiler)
            .args([
                "-O3",
                "-fPIC",
                "-ffunction-sections",
                "-fdata-sections",
                "-c",
            ])
            .arg(format!("-I{}", include.display()))
            .arg(&leansys_c_filtered_path)
            .arg("-o")
            .arg(&leansys_raw_obj_path)
            .status();
        let st3 = Command::new(compiler)
            .args([
                "-O3",
                "-fPIC",
                "-ffunction-sections",
                "-fdata-sections",
                "-c",
            ])
            .arg(format!("-I{}", include.display()))
            .arg(&leannative_c_filtered_path)
            .arg("-o")
            .arg(&leannative_raw_obj_path)
            .status();
        if let (Ok(s1), Ok(s2), Ok(s3)) = (st1, st2, st3) {
            if s1.success()
                && s2.success()
                && s3.success()
                && raw_obj_path.is_file()
                && leansys_raw_obj_path.is_file()
                && leannative_raw_obj_path.is_file()
            {
                compiled = true;
                break;
            }
        }
    }
    assert!(
        compiled,
        "failed to compile TurboLean/Kernel.c, LeanSys/Spec.c, and LeanNative/Spec.c with cc/clang/gcc"
    );

    if cfg!(target_os = "macos") {
        let ld_status = Command::new("ld")
            .args(["-r"])
            .arg(&raw_obj_path)
            .arg(&leansys_raw_obj_path)
            .arg(&leannative_raw_obj_path)
            .arg("-o")
            .arg(&gc_obj_path)
            .status()
            .unwrap_or_else(|e| panic!("ld -r failed: {e}"));
        assert!(ld_status.success() && gc_obj_path.is_file(), "ld -r failed");
        let strip_status = Command::new("strip")
            .args(["-x"])
            .arg(&gc_obj_path)
            .status()
            .unwrap_or_else(|e| panic!("strip -x failed: {e}"));
        assert!(strip_status.success(), "strip -x failed");
    } else {
        let mut ld_args = vec!["-r".to_string(), "--gc-sections".to_string()];
        for sym in TURBO_EXPORTS {
            ld_args.push("-u".to_string());
            ld_args.push((*sym).to_string());
        }
        ld_args.push(raw_obj_path.display().to_string());
        ld_args.push(leansys_raw_obj_path.display().to_string());
        ld_args.push(leannative_raw_obj_path.display().to_string());
        ld_args.push("-o".to_string());
        ld_args.push(gc_obj_path.display().to_string());

        let ld_status = Command::new("ld")
            .args(&ld_args)
            .status()
            .unwrap_or_else(|e| panic!("ld -r --gc-sections failed: {e}"));
        assert!(
            ld_status.success() && gc_obj_path.is_file(),
            "ld -r --gc-sections failed on TurboLean_Kernel_raw.o + LeanSys_Spec_raw.o"
        );

        let strip_status = Command::new("strip")
            .args(["--strip-unneeded"])
            .arg(&gc_obj_path)
            .status()
            .unwrap_or_else(|e| panic!("strip --strip-unneeded failed: {e}"));
        assert!(strip_status.success(), "strip --strip-unneeded failed");
    }

    let nm_undef = Command::new("nm")
        .args(["-P", "-u"])
        .arg(&gc_obj_path)
        .output()
        .unwrap_or_else(|e| panic!("nm -P -u failed: {e}"));
    assert!(nm_undef.status.success(), "nm -P -u failed");
    let undef_str = String::from_utf8_lossy(&nm_undef.stdout);
    assert!(
        undef_str.trim().is_empty(),
        "TurboLean_Kernel_gc.o contains undefined symbols:\n{undef_str}"
    );

    let mut nm_def_cmd = Command::new("nm");
    nm_def_cmd.arg("-P");
    if !cfg!(target_os = "macos") {
        nm_def_cmd.arg("--defined-only");
    }
    let nm_def = nm_def_cmd
        .arg(&gc_obj_path)
        .output()
        .unwrap_or_else(|e| panic!("nm -P failed: {e}"));
    assert!(nm_def.status.success(), "nm -P --defined-only failed");
    let def_str = String::from_utf8_lossy(&nm_def.stdout);
    for sym in TURBO_EXPORTS {
        let def_count = def_str
            .lines()
            .filter(|line| {
                let mut parts = line.split_whitespace();
                let name = parts.next().unwrap_or("");
                let kind = parts.next().unwrap_or("");
                (name == *sym || name.strip_prefix('_') == Some(*sym))
                    && (kind == "T" || kind == "t")
            })
            .count();
        assert_eq!(
            def_count, 1,
            "TurboLean_Kernel_gc.o must contain exactly 1 defined text symbol `{sym}`, found {def_count}:\n{def_str}"
        );
    }

    let _ = fs::remove_file(&lib_path);
    let ar_status = Command::new("ar")
        .args(["crs"])
        .arg(&lib_path)
        .arg(&gc_obj_path)
        .status()
        .unwrap_or_else(|e| panic!("ar crs failed: {e}"));
    assert!(
        ar_status.success() && lib_path.is_file(),
        "failed to create static library libturbo_spec_cabi.a"
    );

    println!("cargo:rustc-link-search=native={}", out_dir.display());
    println!("cargo:rustc-link-lib=static=turbo_spec_cabi");
}
