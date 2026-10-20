use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Command;

fn find_elan_tool(tool_name: &str) -> Option<PathBuf> {
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
            for entry in entries.flatten() {
                let cand = entry.path().join("bin").join(tool_name);
                if cand.is_file() {
                    return Some(cand);
                }
            }
        }
    }
    None
}

fn main() {
    println!("cargo:rerun-if-changed=../../lean/TurboLean/Spec.lean");
    println!("cargo:rerun-if-changed=build.rs");

    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let repo_root = manifest_dir
        .parent()
        .and_then(|p| p.parent())
        .unwrap_or(&manifest_dir);
    let spec_lean = repo_root.join("lean/TurboLean/Spec.lean");
    let lake_spec_c = repo_root.join("lean/.lake/build/ir/TurboLean/Spec.c");

    let mut spec_c_path = out_dir.join("Spec_generated.c");
    let lake_c_ready = lake_spec_c.is_file()
        && fs::read_to_string(&lake_spec_c)
            .map(|s| s.contains("turbo_spec_is_closed_section_needed"))
            .unwrap_or(false);

    if lake_c_ready {
        spec_c_path = lake_spec_c;
    } else if spec_lean.is_file() {
        if let Some(lean_bin) = find_elan_tool("lean") {
            let _ = Command::new(lean_bin)
                .arg(&spec_lean)
                .arg("-c")
                .arg(&spec_c_path)
                .status();
        }
    }

    let obj_path = out_dir.join("Spec_gc.o");
    let lib_path = out_dir.join("libturbo_spec_cabi.a");
    let mut compiled = false;

    if spec_c_path.is_file() {
        if let Some(leanc_bin) = find_elan_tool("leanc") {
            if let Ok(st) = Command::new(leanc_bin)
                .args([
                    "-c",
                    "-O3",
                    "-fPIC",
                    "-ffunction-sections",
                    "-fdata-sections",
                ])
                .arg(&spec_c_path)
                .arg("-o")
                .arg(&obj_path)
                .status()
            {
                compiled = st.success() && obj_path.is_file();
            }
        }
    }

    if !compiled {
        let fallback_c = out_dir.join("Spec_fallback_cabi.c");
        let c_src = r#"
#include <stdint.h>
uint8_t turbo_spec_is_closed_section_needed(uint64_t min_needed_idx, uint64_t target_idx) {
    return min_needed_idx <= target_idx ? 1 : 0;
}
uint8_t turbo_spec_can_fission_have(uint8_t prologue_contains_intro) {
    return prologue_contains_intro == 0 ? 1 : 0;
}
uint8_t turbo_spec_sanitize_warning_as_error(uint8_t allow_stub, uint8_t warning_as_error) {
    return allow_stub == 0 ? warning_as_error : 0;
}
uint8_t turbo_spec_sanitize_forbid_sorry_ax(uint8_t allow_stub, uint8_t forbid_sorry_ax) {
    (void)forbid_sorry_ax;
    return allow_stub == 0 ? 1 : 0;
}
uint8_t turbo_spec_is_sound_decl_summary(uint8_t is_ax, uint8_t is_un, uint8_t is_ext, uint8_t has_forb) {
    return (is_ax == 0 && is_un == 0 && is_ext == 0 && has_forb == 0) ? 1 : 0;
}
uint8_t turbo_spec_check_statement_pinned(uint64_t expected, uint64_t actual, uint8_t is_nested) {
    return (expected == actual && is_nested == 0) ? 1 : 0;
}
"#;
        fs::write(&fallback_c, c_src).expect("failed to write fallback C-ABI source");
        for compiler in ["clang", "cc", "gcc", "leanc"] {
            if let Some(bin) = find_elan_tool(compiler).or_else(|| Some(PathBuf::from(compiler))) {
                if let Ok(st) = Command::new(bin)
                    .args(["-c", "-O3", "-fPIC"])
                    .arg(&fallback_c)
                    .arg("-o")
                    .arg(&obj_path)
                    .status()
                {
                    if st.success() && obj_path.is_file() {
                        compiled = true;
                        break;
                    }
                }
            }
        }
    }

    assert!(compiled, "Failed to compile TurboLean.Spec C-ABI object");

    let mut archived = false;
    for ar_tool in ["llvm-ar", "ar"] {
        if let Some(ar_bin) = find_elan_tool(ar_tool) {
            let _ = fs::remove_file(&lib_path);
            if let Ok(st) = Command::new(ar_bin)
                .arg("rcs")
                .arg(&lib_path)
                .arg(&obj_path)
                .status()
            {
                if st.success() && lib_path.is_file() {
                    archived = true;
                    break;
                }
            }
        }
    }
    assert!(archived, "Failed to archive libturbo_spec_cabi.a");

    println!("cargo:rustc-link-search=native={}", out_dir.display());
    println!("cargo:rustc-link-lib=static=turbo_spec_cabi");
}
