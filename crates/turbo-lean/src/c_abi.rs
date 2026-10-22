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
    pub fn turbo_spec_zygote_lca_reuse_safe(ancestor_len: u64, prefix_len: u64) -> u8;
    pub fn turbo_spec_audit_witness_gate(pos_ok: u8, neg_refuted: u8) -> u8;
    pub fn turbo_spec_effective_cone_job_cap(total_uncached: u64, requested_max: u64) -> u64;
    pub fn turbo_spec_is_scope_isolated_for_fast_olean(open_section_depth: u8, has_section_local_var: u8) -> u8;
    pub fn turbo_spec_matryoshka_tier_router(
        surv_permille: u64,
        prune_floor_permille: u64,
        escalate_band_permille: u64,
        eps_tier_permille: u64,
        counterexample_found: u8,
        burned_at_equal_or_higher_budget: u8,
    ) -> u8;
    pub fn leansys_verify_slice_bounds(off: u64, len: u64, cap: u64) -> u8;
    pub fn leansys_verify_wal_frame(magic: u32, total_len: u32, avail_len: u64, expected_crc: u64, actual_crc: u64) -> u8;
    pub fn leansys_verify_cas_digest(expected_hash: u64, actual_hash: u64, has_path_traversal: u8) -> u8;
    pub fn leansys_check_http_bounds(headers_count: u32, content_len: u64, body_avail: u64, auth_ok: u8) -> u8;
    pub fn leansys_verify_jsonl_tape(key_off: u64, key_len: u64, val_off: u64, val_len: u64, buf_cap: u64, depth: u32) -> u8;
    pub fn leansys_verify_ring_cursor(head: u64, tail: u64, cap: u64, msg_len: u64) -> u8;
    pub fn leansys_verify_sst_block(magic: u32, num_entries: u32, index_off: u64, footer_off: u64, file_size: u64, bloom_mask: u64) -> u8;
    pub fn leansys_verify_poll_interest(active_conns: u32, max_conns: u32, keep_alive_reqs: u32, max_keep_alive: u32, idle_ms: u64, max_idle_ms: u64) -> u8;
    pub fn leansys_verify_rlimit_budget(rss_bytes: u64, max_rss_bytes: u64, elapsed_ms: u64, timeout_ms: u64, pipe_bytes: u64, max_pipe_bytes: u64) -> u8;
    pub fn leansys_verify_composite_key_order(a_hi: u64, a_lo: u64, a_seq: u64, b_hi: u64, b_lo: u64, b_seq: u64) -> u8;
    pub fn leansys_verify_token_auth(match_cur: u8, has_prev: u8, match_prev: u8, scope_ok: u8, now_epoch: u64, expires_at: u64) -> u8;
    pub fn leansys_verify_log_window(start_off: u64, next_off: u64, file_len: u64, max_chunk_bytes: u64) -> u8;
    pub fn leansys_verify_jsonrpc_frame(has_v2: u8, has_id: u8, method_len: u32, frame_bytes: u64) -> u8;
    pub fn leansys_mix64_word(acc: u64, word: u64) -> u64;
    pub fn turbo_spec_combined_step(i: u64) -> u64;
}

#[inline(always)]
pub fn verify_slice_bounds(off: u64, len: u64, cap: u64) -> bool {
    unsafe { leansys_verify_slice_bounds(off, len, cap) == 1 }
}

#[inline(always)]
pub fn verify_wal_frame(magic: u32, total_len: u32, avail_len: u64, expected_crc: u64, actual_crc: u64) -> bool {
    unsafe { leansys_verify_wal_frame(magic, total_len, avail_len, expected_crc, actual_crc) == 1 }
}

#[inline(always)]
pub fn verify_cas_digest(expected_hash: u64, actual_hash: u64, has_path_traversal: bool) -> bool {
    unsafe { leansys_verify_cas_digest(expected_hash, actual_hash, if has_path_traversal { 1 } else { 0 }) == 1 }
}

#[inline(always)]
pub fn check_http_bounds(headers_count: u32, content_len: u64, body_avail: u64, auth_ok: bool) -> bool {
    unsafe { leansys_check_http_bounds(headers_count, content_len, body_avail, if auth_ok { 1 } else { 0 }) == 1 }
}

#[inline(always)]
pub fn verify_jsonl_tape(key_off: u64, key_len: u64, val_off: u64, val_len: u64, buf_cap: u64, depth: u32) -> bool {
    unsafe { leansys_verify_jsonl_tape(key_off, key_len, val_off, val_len, buf_cap, depth) == 1 }
}

#[inline(always)]
pub fn verify_ring_cursor(head: u64, tail: u64, cap: u64, msg_len: u64) -> bool {
    unsafe { leansys_verify_ring_cursor(head, tail, cap, msg_len) == 1 }
}

#[inline(always)]
pub fn verify_sst_block(magic: u32, num_entries: u32, index_off: u64, footer_off: u64, file_size: u64, bloom_mask: u64) -> bool {
    unsafe { leansys_verify_sst_block(magic, num_entries, index_off, footer_off, file_size, bloom_mask) == 1 }
}

#[inline(always)]
pub fn verify_poll_interest(active_conns: u32, max_conns: u32, keep_alive_reqs: u32, max_keep_alive: u32, idle_ms: u64, max_idle_ms: u64) -> bool {
    unsafe { leansys_verify_poll_interest(active_conns, max_conns, keep_alive_reqs, max_keep_alive, idle_ms, max_idle_ms) == 1 }
}

#[inline(always)]
pub fn verify_rlimit_budget(rss_bytes: u64, max_rss_bytes: u64, elapsed_ms: u64, timeout_ms: u64, pipe_bytes: u64, max_pipe_bytes: u64) -> bool {
    unsafe { leansys_verify_rlimit_budget(rss_bytes, max_rss_bytes, elapsed_ms, timeout_ms, pipe_bytes, max_pipe_bytes) == 1 }
}

#[inline(always)]
pub fn verify_composite_key_order(a_hi: u64, a_lo: u64, a_seq: u64, b_hi: u64, b_lo: u64, b_seq: u64) -> bool {
    unsafe { leansys_verify_composite_key_order(a_hi, a_lo, a_seq, b_hi, b_lo, b_seq) == 1 }
}

#[inline(always)]
pub fn verify_token_auth(match_cur: bool, has_prev: bool, match_prev: bool, scope_ok: bool, now_epoch: u64, expires_at: u64) -> bool {
    unsafe { leansys_verify_token_auth(match_cur as u8, has_prev as u8, match_prev as u8, scope_ok as u8, now_epoch, expires_at) == 1 }
}

#[inline(always)]
pub fn verify_log_window(start_off: u64, next_off: u64, file_len: u64, max_chunk_bytes: u64) -> bool {
    unsafe { leansys_verify_log_window(start_off, next_off, file_len, max_chunk_bytes) == 1 }
}

#[inline(always)]
pub fn verify_jsonrpc_frame(has_v2: bool, has_id: bool, method_len: u32, frame_bytes: u64) -> bool {
    unsafe { leansys_verify_jsonrpc_frame(has_v2 as u8, has_id as u8, method_len, frame_bytes) == 1 }
}

#[inline(always)]
pub fn mix64_word(acc: u64, word: u64) -> u64 {
    unsafe { leansys_mix64_word(acc, word) }
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

#[inline(always)]
pub fn matryoshka_tier_router(
    surv_permille: u64,
    prune_floor_permille: u64,
    escalate_band_permille: u64,
    eps_tier_permille: u64,
    counterexample_found: bool,
    burned_at_equal_or_higher_budget: bool,
) -> u8 {
    unsafe {
        turbo_spec_matryoshka_tier_router(
            surv_permille,
            prune_floor_permille,
            escalate_band_permille,
            eps_tier_permille,
            counterexample_found as u8,
            burned_at_equal_or_higher_budget as u8,
        )
    }
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
        assert!(verify_slice_bounds(4, 8, 16));
        assert!(!verify_slice_bounds(12, 8, 16));
        assert!(verify_wal_frame(0x4C535953, 32, 32, 0x1234, 0x1234));
        assert!(!verify_wal_frame(0x4C535953, 32, 16, 0x1234, 0x1234));
        assert!(verify_cas_digest(0xABCD, 0xABCD, false));
        assert!(!verify_cas_digest(0xABCD, 0xABCD, true));
        assert!(check_http_bounds(4, 128, 128, true));
        assert!(!check_http_bounds(40, 128, 128, true));
        assert!(verify_jsonl_tape(2, 4, 8, 6, 32, 1));
        assert!(!verify_jsonl_tape(2, 10, 8, 6, 32, 1));
        assert!(verify_ring_cursor(10, 4, 64, 16));
        assert!(!verify_ring_cursor(60, 0, 64, 16));
        assert!(verify_sst_block(0x4C535354, 4, 64, 128, 152, 0x11));
        assert!(!verify_sst_block(0xDEADBEEF, 4, 64, 128, 152, 0x11));
        assert!(verify_poll_interest(4, 64, 2, 100, 50, 5000));
        assert!(!verify_poll_interest(64, 64, 2, 100, 50, 5000));
        assert!(verify_rlimit_budget(1024, 65536, 10, 1000, 128, 4096));
        assert!(!verify_rlimit_budget(100000, 65536, 10, 1000, 128, 4096));
        assert!(verify_composite_key_order(1, 2, 3, 1, 2, 4));
        assert!(!verify_composite_key_order(2, 0, 0, 1, 99, 99));
        assert!(verify_token_auth(false, true, true, true, 100, 200));
        assert!(!verify_token_auth(true, false, false, true, 300, 200));
        assert!(verify_log_window(10, 50, 100, 65536));
        assert!(!verify_log_window(50, 10, 100, 65536));
        assert!(verify_jsonrpc_frame(true, true, 12, 512));
        assert!(!verify_jsonrpc_frame(false, true, 12, 512));
        assert_ne!(mix64_word(0, 0), mix64_word(0, 1));
        assert_eq!(matryoshka_tier_router(880, 120, 380, 15, false, false), 0);
        assert_eq!(matryoshka_tier_router(50, 120, 380, 15, false, false), 1);
        assert_eq!(matryoshka_tier_router(110, 120, 380, 15, false, false), 2);
        assert_eq!(matryoshka_tier_router(900, 120, 380, 15, true, false), 1);
        assert_eq!(matryoshka_tier_router(900, 120, 380, 15, false, true), 2);
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
