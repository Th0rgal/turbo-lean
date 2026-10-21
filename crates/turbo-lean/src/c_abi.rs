//! Direct C-ABI Bindings to `TurboLean.Spec` (`libturbo_spec_cabi.a`) for `@[export]`
//! specification functions, `ClockedStepBudget` (`AffineStepBudget`, loop composition),
//! and RISC-V `rv64im` `DIVU`/`REMU`.
#![allow(dead_code)]

extern "C" {
    pub fn turbo_spec_is_closed_section_needed(min_needed_idx: u64, target_idx: u64) -> u8;
    pub fn turbo_spec_can_fission_have(prologue_contains_intro: u8) -> u8;
    pub fn turbo_spec_sanitize_warning_as_error(allow_stub: u8, warning_as_error: u8) -> u8;
    pub fn turbo_spec_sanitize_forbid_sorry_ax(allow_stub: u8, forbid_sorry_ax: u8) -> u8;
    pub fn turbo_spec_is_sound_decl_summary(is_axiom: u8, is_unsafe: u8, is_extern_or_implemented_by: u8, has_forbidden: u8) -> u8;
    pub fn turbo_spec_check_statement_pinned(expected_type_hash: u64, actual_type_hash: u64, is_nested_inductive: u8) -> u8;
    pub fn turbo_spec_node_effective_cost(rtt_us: u64, queue_depth: u64, ewma_exec_us: u64, concurrency: u64) -> u64;
    pub fn turbo_spec_is_remote_eligible(ttl: u64, is_healthy: u8, supports_target: u8) -> u8;
    pub fn turbo_spec_should_switch_route(best_cost: u64, cand_cost: u64, cand_eligible: u8) -> u8;
    pub fn turbo_spec_classify_compute_target(trip_count: u64, is_256bit: u8, is_matrix_op: u8, has_tpu: u8, has_gpu: u8) -> u8;
    pub fn turbo_spec_splitmix64(x: u64) -> u64;
    pub fn turbo_spec_boundary_u256_limb(slot: u64, limb_idx: u64) -> u64;
    pub fn turbo_spec_gen_u256_limb(idx: u64, seed: u64, param_id: u64, limb_idx: u64) -> u64;
    pub fn turbo_spec_u256_lt(a0: u64, a1: u64, a2: u64, a3: u64, b0: u64, b1: u64, b2: u64, b3: u64) -> u8;
    pub fn turbo_spec_eval_u64_binop(op: u8, lhs: u64, rhs: u64) -> u64;
    pub fn turbo_spec_step_verdict_consistent(full_ok: u8, compact_ok: u8) -> u8;
    pub fn turbo_spec_affine_step_budget(scale: u64, offset: u64, steps: u64) -> u64;
    pub fn turbo_spec_loop_step_budget(init_steps: u64, fuel: u64, scale: u64, offset: u64, iter_steps: u64) -> u64;
    pub fn turbo_spec_check_step_budget_le(actual_steps: u64, candidate_k: u64) -> u8;
    pub fn turbo_spec_riscv_div_u64(lhs: u64, rhs: u64) -> u64;
    pub fn turbo_spec_riscv_rem_u64(lhs: u64, rhs: u64) -> u64;
    pub fn turbo_spec_combined_step(i: u64) -> u64;
}

#[inline(always)]
pub fn affine_step_budget(scale: u64, offset: u64, steps: u64) -> u64 {
    unsafe { turbo_spec_affine_step_budget(scale, offset, steps) }
}

#[inline(always)]
pub fn loop_step_budget(init_steps: u64, fuel: u64, scale: u64, offset: u64, iter_steps: u64) -> u64 {
    unsafe { turbo_spec_loop_step_budget(init_steps, fuel, scale, offset, iter_steps) }
}

#[inline(always)]
pub fn check_step_budget_le(actual_steps: u64, candidate_k: u64) -> bool {
    unsafe { turbo_spec_check_step_budget_le(actual_steps, candidate_k) != 0 }
}

#[inline(always)]
pub fn riscv_div_u64(lhs: u64, rhs: u64) -> u64 {
    unsafe { turbo_spec_riscv_div_u64(lhs, rhs) }
}

#[inline(always)]
pub fn riscv_rem_u64(lhs: u64, rhs: u64) -> u64 {
    unsafe { turbo_spec_riscv_rem_u64(lhs, rhs) }
}

/// Verify a non-negative Farkas linear combination certificate over `u64` using 128-bit exact arithmetic:
/// checks (a) for every column `j < obj.len()`, `obj[j] <= sum_i weights[i] * matrix[i][j]`,
/// and (b) `sum_i weights[i] * rhs[i] <= bound`.
pub fn check_farkas_nat(
    weights: &[u64],
    matrix: &[Vec<u64>],
    rhs: &[u64],
    obj: &[u64],
    bound: u64,
) -> bool {
    for (j, &c_j) in obj.iter().enumerate() {
        let mut col_sum: u128 = 0;
        for (i, &w_i) in weights.iter().enumerate() {
            let a_ij = matrix
                .get(i)
                .and_then(|row| row.get(j))
                .copied()
                .unwrap_or(0);
            col_sum = col_sum.saturating_add((w_i as u128).saturating_mul(a_ij as u128));
        }
        if (c_j as u128) > col_sum {
            return false;
        }
    }
    let mut rhs_dot: u128 = 0;
    for (i, &w_i) in weights.iter().enumerate() {
        let b_i = rhs.get(i).copied().unwrap_or(0);
        rhs_dot = rhs_dot.saturating_add((w_i as u128).saturating_mul(b_i as u128));
    }
    rhs_dot <= (bound as u128)
}

/// Emit a self-contained Lean 4 snippet proving a linear bound via `LeanNative.Spec.checkFarkasNat_sound` and `by decide`.
pub fn format_farkas_lean4_certificate(
    weights: &[u64],
    matrix: &[Vec<u64>],
    rhs: &[u64],
    obj: &[u64],
    bound: u64,
) -> String {
    let fmt_list = |xs: &[u64]| -> String {
        format!(
            "[{}]",
            xs.iter()
                .map(|x| x.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    };
    let rows_str = matrix
        .iter()
        .map(|r| fmt_list(r))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "checkFarkasNat {} [{}] {} {} {} = true := by decide",
        fmt_list(weights),
        rows_str,
        fmt_list(rhs),
        fmt_list(obj),
        bound
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_c_abi_riscv_step_budget_and_div_by_zero_parity() {
        assert_eq!(affine_step_budget(1, 23132, 5000), 28132);
        assert_eq!(loop_step_budget(23132, 10, 2, 5, 100), 23132 + 10 * (2 * 100 + 5));
        assert!(check_step_budget_le(28127, 30000));
        assert!(!check_step_budget_le(30001, 30000));
        assert_eq!(riscv_div_u64(42, 0), u64::MAX);
        assert_eq!(riscv_rem_u64(42, 0), 42);
        assert_eq!(riscv_div_u64(100, 7), 14);
        assert_eq!(riscv_rem_u64(100, 7), 2);
    }

    #[test]
    fn test_farkas_certificate_verifier_and_lean4_codegen() {
        // System: x0 + 2*x1 <= 10, 3*x0 + x1 <= 15
        // Weights: [2, 1] -> (2*1 + 1*3)*x0 + (2*2 + 1*1)*x1 = 5*x0 + 5*x1 <= 2*10 + 1*15 = 35
        let weights = vec![2u64, 1u64];
        let matrix = vec![vec![1u64, 2u64], vec![3u64, 1u64]];
        let rhs = vec![10u64, 15u64];
        let obj = vec![5u64, 5u64];
        assert!(check_farkas_nat(&weights, &matrix, &rhs, &obj, 35));
        assert!(check_farkas_nat(&weights, &matrix, &rhs, &[4, 5], 35));
        // Invalid bound (34 < 35)
        assert!(!check_farkas_nat(&weights, &matrix, &rhs, &obj, 34));
        // Invalid column dominance (6 > 5)
        assert!(!check_farkas_nat(&weights, &matrix, &rhs, &[6, 5], 35));
        let snippet = format_farkas_lean4_certificate(&weights, &matrix, &rhs, &obj, 35);
        assert!(snippet.contains("checkFarkasNat [2, 1]"));
        assert!(snippet.contains(":= by decide"));
    }
}
