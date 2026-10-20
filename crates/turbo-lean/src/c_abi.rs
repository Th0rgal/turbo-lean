//! Direct C-ABI Bindings to `TurboLean.Spec` (`libturbo_spec_cabi.a`) for `ClockedStepBudget`
//! (`AffineStepBudget`, loop composition, Yukon score) and RISC-V `rv64im` `DIVU`/`REMU`.
#![allow(dead_code)]

extern "C" {
    pub fn turbo_spec_affine_step_budget(scale: u64, offset: u64, steps: u64) -> u64;
    pub fn turbo_spec_loop_step_budget(init_steps: u64, fuel: u64, scale: u64, offset: u64, iter_steps: u64) -> u64;
    pub fn turbo_spec_check_step_budget_le(actual_steps: u64, candidate_k: u64) -> u8;
    pub fn turbo_spec_yukon_score_improves(new_k: u64, new_verify_min: u64, old_k: u64, old_verify_min: u64) -> u8;
    pub fn turbo_spec_riscv_div_u64(lhs: u64, rhs: u64) -> u64;
    pub fn turbo_spec_riscv_rem_u64(lhs: u64, rhs: u64) -> u64;
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
pub fn yukon_score_improves(new_k: u64, new_verify_min: u64, old_k: u64, old_verify_min: u64) -> bool {
    unsafe { turbo_spec_yukon_score_improves(new_k, new_verify_min, old_k, old_verify_min) != 0 }
}

#[inline(always)]
pub fn riscv_div_u64(lhs: u64, rhs: u64) -> u64 {
    unsafe { turbo_spec_riscv_div_u64(lhs, rhs) }
}

#[inline(always)]
pub fn riscv_rem_u64(lhs: u64, rhs: u64) -> u64 {
    unsafe { turbo_spec_riscv_rem_u64(lhs, rhs) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_c_abi_riscv_step_budget_and_div_by_zero_parity() {
        assert_eq!(affine_step_budget(1, 23127, 5000), 28127);
        assert_eq!(loop_step_budget(23127, 10, 2, 5, 100), 23127 + 10 * (2 * 100 + 5));
        assert!(check_step_budget_le(28127, 30000));
        assert!(!check_step_budget_le(30001, 30000));
        assert!(yukon_score_improves(28000, 15, 29000, 10));
        assert!(yukon_score_improves(28000, 9, 28000, 10));
        assert!(!yukon_score_improves(28000, 10, 28000, 10));
        assert_eq!(riscv_div_u64(42, 0), u64::MAX);
        assert_eq!(riscv_rem_u64(42, 0), 42);
        assert_eq!(riscv_div_u64(100, 7), 14);
        assert_eq!(riscv_rem_u64(100, 7), 2);
    }
}
