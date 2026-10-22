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
];

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
    println!("cargo:rerun-if-changed=../../lean/TurboLean/Kernel.lean");
    println!("cargo:rerun-if-changed=../../lean/TurboLean/Spec.lean");
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
    let kernel_lean = lean_dir.join("TurboLean/Kernel.lean");
    let spec_lean = lean_dir.join("TurboLean/Spec.lean");

    assert!(
        kernel_lean.is_file() && spec_lean.is_file(),
        "missing TurboLean/Kernel.lean or TurboLean/Spec.lean under {}",
        lean_dir.display()
    );

    let lean_bin = find_elan_tool("lean").unwrap_or_else(|| {
        panic!(
            "Lean 4 toolchain required to build turbo-lean C-ABI kernel (`lean` not found in TURBO_LEAN_BIN, PATH, ELAN_HOME, or ~/.elan)"
        )
    });

    let lean_build_dir = out_dir.join("lean_build");
    let turbo_olean_dir = lean_build_dir.join("TurboLean");
    fs::create_dir_all(&turbo_olean_dir).unwrap();
    let kernel_olean = turbo_olean_dir.join("Kernel.olean");
    let spec_olean = turbo_olean_dir.join("Spec.olean");
    let kernel_c_path = out_dir.join("TurboLean_Kernel_generated.c");

    let kernel_status = Command::new(&lean_bin)
        .current_dir(&lean_dir)
        .arg("TurboLean/Kernel.lean")
        .arg("-o")
        .arg(&kernel_olean)
        .arg("-c")
        .arg(&kernel_c_path)
        .status()
        .unwrap_or_else(|e| panic!("failed to invoke lean on TurboLean/Kernel.lean: {e}"));
    assert!(
        kernel_status.success() && kernel_c_path.is_file(),
        "lean failed to compile TurboLean/Kernel.lean to C"
    );

    let spec_status = Command::new(&lean_bin)
        .current_dir(&lean_dir)
        .env("LEAN_PATH", &lean_build_dir)
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
    for sym in TURBO_EXPORTS {
        assert!(
            c_text.contains(sym),
            "generated TurboLean/Kernel.c missing required export `{sym}`"
        );
    }

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
    let gc_obj_path = out_dir.join("TurboLean_Kernel_gc.o");
    let lib_path = out_dir.join("libturbo_spec_cabi.a");

    let mut compiled = false;
    for compiler in ["cc", "clang", "gcc"] {
        if let Ok(st) = Command::new(compiler)
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
            .status()
        {
            if st.success() && raw_obj_path.is_file() {
                compiled = true;
                break;
            }
        }
    }
    assert!(
        compiled,
        "failed to compile TurboLean/Kernel.c with cc/clang/gcc"
    );

    let mut ld_args = vec!["-r".to_string(), "--gc-sections".to_string()];
    for sym in TURBO_EXPORTS {
        ld_args.push("-u".to_string());
        ld_args.push((*sym).to_string());
    }
    ld_args.push(raw_obj_path.display().to_string());
    ld_args.push("-o".to_string());
    ld_args.push(gc_obj_path.display().to_string());

    let ld_status = Command::new("ld")
        .args(&ld_args)
        .status()
        .unwrap_or_else(|e| panic!("ld -r --gc-sections failed: {e}"));
    assert!(
        ld_status.success() && gc_obj_path.is_file(),
        "ld -r --gc-sections failed on TurboLean_Kernel_raw.o"
    );

    let strip_status = Command::new("strip")
        .args(["--strip-unneeded"])
        .arg(&gc_obj_path)
        .status()
        .unwrap_or_else(|e| panic!("strip --strip-unneeded failed: {e}"));
    assert!(strip_status.success(), "strip --strip-unneeded failed");

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

    let nm_def = Command::new("nm")
        .args(["-P", "--defined-only"])
        .arg(&gc_obj_path)
        .output()
        .unwrap_or_else(|e| panic!("nm -P --defined-only failed: {e}"));
    assert!(nm_def.status.success(), "nm -P --defined-only failed");
    let def_str = String::from_utf8_lossy(&nm_def.stdout);
    for sym in TURBO_EXPORTS {
        let found = def_str.lines().any(|line| {
            let mut parts = line.split_whitespace();
            let name = parts.next().unwrap_or("");
            let kind = parts.next().unwrap_or("");
            (name == *sym || name.strip_prefix('_') == Some(*sym)) && (kind == "T" || kind == "t")
        });
        assert!(
            found,
            "TurboLean_Kernel_gc.o missing defined text symbol `{sym}` in nm output:\n{def_str}"
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
