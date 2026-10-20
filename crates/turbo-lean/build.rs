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
            .map(|s| {
                s.contains("turbo_spec_is_closed_section_needed")
                    && s.contains("turbo_spec_node_effective_cost")
                    && s.contains("turbo_spec_combined_step")
                    && s.contains("turbo_spec_affine_step_budget")
                    && s.contains("turbo_spec_yukon_score_improves")
                    && s.contains("turbo_spec_riscv_div_u64")
                    && s.contains("turbo_spec_tactic_beta_priority")
            })
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
            if let Ok(st) = Command::new(&leanc_bin)
                .args([
                    "-c",
                    "-O3",
                    "-march=native",
                    "-funroll-loops",
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
            if !compiled {
                if let Ok(st) = Command::new(&leanc_bin)
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
uint64_t turbo_spec_node_effective_cost(uint64_t rtt_us, uint64_t queue_depth, uint64_t ewma_exec_us, uint64_t concurrency) {
    uint64_t conc = concurrency == 0 ? 1 : concurrency;
    return rtt_us + ((queue_depth + 1) * ewma_exec_us) / conc;
}
uint8_t turbo_spec_is_remote_eligible(uint64_t ttl, uint8_t is_healthy, uint8_t supports_target) {
    return (ttl > 0 && is_healthy != 0 && supports_target != 0) ? 1 : 0;
}
uint8_t turbo_spec_should_switch_route(uint64_t best_cost, uint64_t cand_cost, uint8_t cand_eligible) {
    return (cand_eligible != 0 && cand_cost < best_cost) ? 1 : 0;
}
uint8_t turbo_spec_classify_compute_target(uint64_t trip_count, uint8_t is_256bit, uint8_t is_matrix_op, uint8_t has_tpu, uint8_t has_gpu) {
    if (trip_count < 4096) return 0;
    if (is_matrix_op != 0 && has_tpu != 0) return 2;
    if (is_256bit != 0 && has_gpu != 0) return 1;
    if (has_tpu != 0) return 2;
    if (has_gpu != 0) return 1;
    return 0;
}
uint64_t turbo_spec_splitmix64(uint64_t x) {
    uint64_t s = x + 0x9e3779b97f4a7c15ULL;
    uint64_t z1 = (s ^ (s >> 30)) * 0xbf58476d1ce4e5b9ULL;
    uint64_t z2 = (z1 ^ (z1 >> 27)) * 0x94d049bb133111ebULL;
    return z2 ^ (z2 >> 31);
}
uint64_t turbo_spec_boundary_u256_limb(uint64_t slot, uint64_t limb_idx) {
    uint64_t s = slot & 15ULL;
    uint64_t l = limb_idx & 3ULL;
    if (s == 0) return 0ULL;
    if (s == 1) return l == 0 ? 1ULL : 0ULL;
    if (s == 2) return 0xffffffffffffffffULL;
    if (s == 3) return l == 0 ? 0xfffffffffffffffeULL : 0xffffffffffffffffULL;
    if (s == 4) return 0x5555555555555555ULL;
    if (s == 5) return 0xaaaaaaaaaaaaaaaaULL;
    if (s == 6) return l < 2 ? 0xffffffffffffffffULL : 0ULL;
    if (s == 7) return l == 1 ? 1ULL : 0ULL;
    if (s == 8) return l == 2 ? 1ULL : 0ULL;
    if (s == 9) return l == 3 ? 1ULL : 0ULL;
    if (s == 10) return l == 3 ? 0x8000000000000000ULL : 0ULL;
    if (s == 11) return l == 0 ? 0xffffffffffffffffULL : 0ULL;
    if (s == 12) return l == 0 ? 2ULL : 0ULL;
    if (s == 13) return l == 0 ? 3ULL : (l == 1 ? 5ULL : (l == 2 ? 7ULL : 11ULL));
    if (s == 14) {
        if (l == 0) return 0x123456789abcdef0ULL;
        if (l == 1) return 0xfedcba9876543210ULL;
        if (l == 2) return 0x0f0f0f0f0f0f0f0fULL;
        return 0xf0f0f0f0f0f0f0f0ULL;
    }
    return 0x8000000000000000ULL;
}
uint64_t turbo_spec_gen_u256_limb(uint64_t idx, uint64_t seed, uint64_t param_id, uint64_t limb_idx) {
    if (idx < 4096ULL) {
        uint64_t shift = (4ULL * param_id) & 63ULL;
        return turbo_spec_boundary_u256_limb((idx >> shift) & 15ULL, limb_idx);
    }
    uint64_t base = (idx * 1315423911ULL) ^ (seed * 2654435761ULL) ^ (param_id * 0x9e3779b97f4a7c15ULL);
    return turbo_spec_splitmix64(base + (limb_idx & 3ULL));
}
uint8_t turbo_spec_u256_lt(uint64_t a0, uint64_t a1, uint64_t a2, uint64_t a3, uint64_t b0, uint64_t b1, uint64_t b2, uint64_t b3) {
    if (a3 != b3) return a3 < b3 ? 1 : 0;
    if (a2 != b2) return a2 < b2 ? 1 : 0;
    if (a1 != b1) return a1 < b1 ? 1 : 0;
    return a0 < b0 ? 1 : 0;
}
uint64_t turbo_spec_eval_u64_binop(uint8_t op, uint64_t lhs, uint64_t rhs) {
    switch (op) {
        case 0: return lhs + rhs;
        case 1: return lhs >= rhs ? lhs - rhs : 0ULL;
        case 2: return lhs * rhs;
        case 3: return rhs == 0ULL ? 0ULL : lhs / rhs;
        case 4: return rhs == 0ULL ? 0ULL : lhs % rhs;
        case 5: return lhs & rhs;
        case 6: return lhs | rhs;
        case 7: return lhs ^ rhs;
        case 8: return lhs << (rhs & 63ULL);
        case 9: return lhs >> (rhs & 63ULL);
        case 10: return lhs == rhs ? 1ULL : 0ULL;
        case 11: return lhs != rhs ? 1ULL : 0ULL;
        case 12: return lhs < rhs ? 1ULL : 0ULL;
        case 13: return lhs <= rhs ? 1ULL : 0ULL;
        case 14: return lhs > rhs ? 1ULL : 0ULL;
        case 15: return lhs >= rhs ? 1ULL : 0ULL;
        default: return lhs - rhs;
    }
}
uint8_t turbo_spec_step_verdict_consistent(uint8_t full_ok, uint8_t compact_ok) {
    return (full_ok == compact_ok) ? 1 : 0;
}
uint64_t turbo_spec_affine_step_budget(uint64_t scale, uint64_t offset, uint64_t steps) {
    return scale * steps + offset;
}
uint64_t turbo_spec_loop_step_budget(uint64_t init_steps, uint64_t fuel, uint64_t scale, uint64_t offset, uint64_t iter_steps) {
    return init_steps + fuel * (scale * iter_steps + offset);
}
uint8_t turbo_spec_check_step_budget_le(uint64_t actual_steps, uint64_t candidate_k) {
    return actual_steps <= candidate_k ? 1 : 0;
}
uint8_t turbo_spec_yukon_score_improves(uint64_t new_k, uint64_t new_verify_min, uint64_t old_k, uint64_t old_verify_min) {
    return (new_k * 10000ULL + new_verify_min < old_k * 10000ULL + old_verify_min) ? 1 : 0;
}
uint64_t turbo_spec_riscv_div_u64(uint64_t lhs, uint64_t rhs) {
    return rhs == 0ULL ? 0xffffffffffffffffULL : lhs / rhs;
}
uint64_t turbo_spec_riscv_rem_u64(uint64_t lhs, uint64_t rhs) {
    return rhs == 0ULL ? lhs : lhs % rhs;
}
uint64_t turbo_spec_tactic_beta_priority(uint64_t alpha0, uint64_t beta0, uint64_t successes, uint64_t failures, uint64_t speedup_permille) {
    uint64_t denom = alpha0 + beta0 + successes + failures;
    uint64_t post = denom == 0ULL ? 500ULL : ((alpha0 + successes) * 1000ULL) / denom;
    uint64_t spd = speedup_permille < 1000ULL ? 1000ULL : speedup_permille;
    return (post * spd) / 1000ULL;
}
uint64_t turbo_spec_combined_step(uint64_t i) {
    uint8_t needed = turbo_spec_is_closed_section_needed(i & 63ULL, 32ULL);
    uint8_t is_sound = turbo_spec_is_sound_decl_summary((i & 7ULL) == 7ULL ? 1 : 0, 0, 0, 0);
    uint64_t h = i ^ 0xA5A55A5AULL;
    uint8_t pinned = turbo_spec_check_statement_pinned(h, h, 0);
    uint64_t sm = turbo_spec_splitmix64(i);
    uint64_t cost = ((i & 15ULL) == 0ULL)
        ? 0xffffffffffffffffULL
        : turbo_spec_node_effective_cost((i & 1023ULL) / 1000ULL, i & 7ULL, 2ULL, 4ULL);
    uint8_t lt = turbo_spec_u256_lt(sm, i, sm ^ i, i & 3ULL, i, sm, i ^ 1ULL, (i + 1ULL) & 3ULL);
    return ((uint64_t)(needed != 0))
        ^ ((uint64_t)(is_sound != 0))
        ^ ((uint64_t)(pinned != 0))
        ^ sm
        ^ (cost & 0xFFFFULL)
        ^ ((uint64_t)(lt != 0))
        ^ ((i & 7ULL) == 7ULL ? 1ULL : 0ULL);
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
