//! Direct C-ABI Bindings to `TurboLean.Spec` (`libturbo_spec_cabi.a`) for `@[export]`
//! specification functions, `ClockedStepBudget` (`AffineStepBudget`, loop composition),
//! and RISC-V `rv64im` `DIVU`/`REMU`.
#![allow(dead_code)]

extern "C" {
    pub fn turbo_spec_is_closed_section_needed(min_needed_idx: u64, target_idx: u64) -> u8;
    pub fn turbo_spec_can_fission_have(prologue_contains_intro: u8) -> u8;
    pub fn turbo_spec_sanitize_warning_as_error(allow_stub: u8, warning_as_error: u8) -> u8;
    pub fn turbo_spec_sanitize_forbid_sorry_ax(allow_stub: u8, forbid_sorry_ax: u8) -> u8;
    pub fn turbo_spec_is_sound_decl_summary(
        is_axiom: u8,
        is_unsafe: u8,
        is_extern_or_implemented_by: u8,
        has_forbidden: u8,
    ) -> u8;
    pub fn turbo_spec_check_statement_pinned(
        expected_type_hash: u64,
        actual_type_hash: u64,
        is_nested_inductive: u8,
    ) -> u8;
    pub fn turbo_spec_node_effective_cost(
        rtt_us: u64,
        queue_depth: u64,
        ewma_exec_us: u64,
        concurrency: u64,
    ) -> u64;
    pub fn turbo_spec_is_remote_eligible(ttl: u64, is_healthy: u8, supports_target: u8) -> u8;
    pub fn turbo_spec_should_switch_route(best_cost: u64, cand_cost: u64, cand_eligible: u8) -> u8;
    pub fn turbo_spec_classify_compute_target(
        trip_count: u64,
        is_256bit: u8,
        is_matrix_op: u8,
        has_tpu: u8,
        has_gpu: u8,
    ) -> u8;
    pub fn turbo_spec_splitmix64(x: u64) -> u64;
    pub fn turbo_spec_boundary_u256_limb(slot: u64, limb_idx: u64) -> u64;
    pub fn turbo_spec_gen_u256_limb(idx: u64, seed: u64, param_id: u64, limb_idx: u64) -> u64;
    pub fn turbo_spec_u256_lt(
        a0: u64,
        a1: u64,
        a2: u64,
        a3: u64,
        b0: u64,
        b1: u64,
        b2: u64,
        b3: u64,
    ) -> u8;
    pub fn turbo_spec_eval_u64_binop(op: u8, lhs: u64, rhs: u64) -> u64;
    pub fn turbo_spec_step_verdict_consistent(full_ok: u8, compact_ok: u8) -> u8;
    pub fn turbo_spec_affine_step_budget(scale: u64, offset: u64, steps: u64) -> u64;
    pub fn turbo_spec_loop_step_budget(
        init_steps: u64,
        fuel: u64,
        scale: u64,
        offset: u64,
        iter_steps: u64,
    ) -> u64;
    pub fn turbo_spec_check_step_budget_le(actual_steps: u64, candidate_k: u64) -> u8;
    pub fn turbo_spec_riscv_div_u64(lhs: u64, rhs: u64) -> u64;
    pub fn turbo_spec_riscv_rem_u64(lhs: u64, rhs: u64) -> u64;
    pub fn turbo_spec_zygote_lca_reuse_safe(ancestor_len: u64, prefix_len: u64) -> u8;
    pub fn turbo_spec_audit_witness_gate(pos_ok: u8, neg_refuted: u8) -> u8;
    pub fn turbo_spec_effective_cone_job_cap(total_uncached: u64, requested_max: u64) -> u64;
    pub fn turbo_spec_is_scope_isolated_for_fast_olean(
        open_section_depth: u8,
        has_section_local_var: u8,
    ) -> u8;
    pub fn turbo_spec_matryoshka_tier_router(
        surv_permille: u64,
        prune_floor_permille: u64,
        escalate_band_permille: u64,
        eps_tier_permille: u64,
        counterexample_found: u8,
        burned_at_equal_or_higher_budget: u8,
    ) -> u8;
    pub fn turbo_spec_verify_dag_schedule_step(
        in_degree: u64,
        completed_deps: u64,
        total_deps: u64,
        visited_nodes: u64,
        total_nodes: u64,
    ) -> u8;
    pub fn turbo_spec_verify_module_cache_key(
        toolchain_match: u8,
        args_match: u8,
        src_match: u8,
        dep_oleans_match: u8,
        config_match: u8,
    ) -> u8;
    pub fn turbo_spec_verify_module_artifact_set(
        has_olean: u8,
        has_ilean: u8,
        is_module: u8,
        has_server_olean: u8,
        has_private_olean: u8,
        needs_c: u8,
        has_c: u8,
    ) -> u8;
    pub fn turbo_spec_verify_static_lake_config(
        has_config: u8,
        has_dynamic_script: u8,
        has_unbuilt_extern_dep: u8,
        has_unsupported_facet: u8,
    ) -> u8;
    pub fn turbo_spec_verify_slice_pass_gate(
        slice_len: u64,
        min_grain: u64,
        simd_width: u64,
        non_aliasing: u8,
        lazy_reduction_homomorphic: u8,
    ) -> u8;
    pub fn turbo_spec_verify_tlz1_token(
        is_match: u8,
        offset: u64,
        token_len: u64,
        out_len: u64,
        uncompressed_cap: u64,
    ) -> u8;
    pub fn turbo_spec_verify_lexer_comment_guard(
        in_string: u8,
        is_escaped: u8,
        two_bytes_avail: u8,
        block_depth: u64,
        max_depth: u64,
    ) -> u8;
    pub fn turbo_spec_verify_farkas_step(
        obj_coeff: u64,
        col_sum: u64,
        acc_cost: u64,
        weight_cost: u64,
        bound: u64,
    ) -> u8;
    pub fn turbo_spec_verify_ident_bloom(
        is_excluded_core: u8,
        cand_mask: u64,
        context_mask: u64,
    ) -> u8;
    pub fn leansys_verify_slice_bounds(off: u64, len: u64, cap: u64) -> u8;
    pub fn leansys_verify_wal_frame(
        magic: u32,
        total_len: u32,
        avail_len: u64,
        expected_crc: u64,
        actual_crc: u64,
    ) -> u8;
    pub fn leansys_verify_cas_digest(
        expected_hash: u64,
        actual_hash: u64,
        has_path_traversal: u8,
    ) -> u8;
    pub fn leansys_check_http_bounds(
        headers_count: u32,
        content_len: u64,
        body_avail: u64,
        auth_ok: u8,
    ) -> u8;
    pub fn leansys_verify_jsonl_tape(
        key_off: u64,
        key_len: u64,
        val_off: u64,
        val_len: u64,
        buf_cap: u64,
        depth: u32,
    ) -> u8;
    pub fn leansys_verify_ring_cursor(head: u64, tail: u64, cap: u64, msg_len: u64) -> u8;
    pub fn leansys_verify_sst_block(
        magic: u32,
        num_entries: u32,
        index_off: u64,
        footer_off: u64,
        file_size: u64,
        bloom_mask: u64,
    ) -> u8;
    pub fn leansys_verify_poll_interest(
        active_conns: u32,
        max_conns: u32,
        keep_alive_reqs: u32,
        max_keep_alive: u32,
        idle_ms: u32,
        max_idle_ms: u32,
    ) -> u8;
    pub fn leansys_verify_rlimit_budget(
        rss_bytes: u64,
        max_rss_bytes: u64,
        elapsed_ms: u64,
        timeout_ms: u64,
        pipe_bytes: u64,
        max_pipe_bytes: u64,
    ) -> u8;
    pub fn leansys_verify_composite_key_order(
        a_hi: u64,
        a_lo: u64,
        a_seq: u64,
        b_hi: u64,
        b_lo: u64,
        b_seq: u64,
    ) -> u8;
    pub fn leansys_verify_token_auth(
        match_cur: u8,
        has_prev: u8,
        match_prev: u8,
        scope_ok: u8,
        now_epoch: u64,
        expires_at: u64,
    ) -> u8;
    pub fn leansys_verify_log_window(
        start_off: u64,
        next_off: u64,
        file_len: u64,
        max_chunk_bytes: u64,
    ) -> u8;
    pub fn leansys_verify_jsonrpc_frame(
        has_v2: u8,
        has_id: u8,
        method_len: u32,
        frame_bytes: u64,
    ) -> u8;
    pub fn leansys_mix64_word(acc: u64, word: u64) -> u64;
    pub fn leansys_gate_admit(no_sorry_ax: u8, statement_pinned: u8, cert_verified: u8) -> u8;
    pub fn leansys_verify_par_chunk(
        chunk_start: u64,
        chunk_end: u64,
        total_len: u64,
        min_grain: u64,
    ) -> u8;
    pub fn leansys_verify_arena_disjoint(
        off_a: u64,
        len_a: u64,
        off_b: u64,
        len_b: u64,
        arena_cap: u64,
    ) -> u8;
    pub fn leansys_verify_snapshot_visibility(
        entry_seq: u64,
        max_snapshot_seq: u64,
        is_tombstone: u8,
    ) -> u8;
    pub fn leansys_verify_http_route_match(
        method_match: u8,
        path_match: u8,
        route_idx: u32,
        route_count: u32,
    ) -> u8;
    pub fn leansys_verify_counterexample_triage(
        has_violation: u8,
        has_missing_hyp_hint: u8,
        ref_disagrees_with_candidate: u8,
        triage_class: u8,
    ) -> u8;
    pub fn leansys_verify_dag_wave_step(
        in_degree_sum: u64,
        wave_size: u64,
        completed_tasks: u64,
        total_tasks: u64,
        active_workers: u64,
        max_workers: u64,
    ) -> u8;
    pub fn leansys_verify_ios_jetsam_budget(
        dirty_rss_bytes: u64,
        alloc_bytes: u64,
        max_jetsam_bytes: u64,
        page_align_mask: u64,
        is_app_extension: u8,
    ) -> u8;
    pub fn leansys_verify_worker_budget(
        active_workers: u64,
        max_workers: u64,
        micro_chunks: u64,
        total_len: u64,
        is_mobile_hetero: u8,
    ) -> u8;
    pub fn leannative_pack_slice_span_u64(start: u64, len: u64, kind: u64) -> u64;
    pub fn leannative_eval_u64_binop(op: u8, lhs: u64, rhs: u64) -> u64;
    pub fn leannative_has_domain_hazard_u64(op: u8, lhs: u64, rhs: u64) -> u8;
    pub fn leannative_fastcheck_rewrite_step(
        lhs_val: u64,
        rhs_val: u64,
        op_lhs: u8,
        op_rhs: u8,
        a: u64,
        b: u64,
        ref_disagrees: u8,
    ) -> u8;
    pub fn leannative_certify_cex_witnesses(x1: u64, dm_a0: u64, dm_b0: u64) -> u8;
    pub fn leannative_verify_parfor_chunk_partition(
        chunk_start: u64,
        chunk_end: u64,
        total_len: u64,
        min_grain: u64,
        active_workers: u64,
        max_workers: u64,
    ) -> u8;
    pub fn leannative_verify_rc_mode_safe(
        rc_mode: u8,
        has_heap_allocs: u8,
        is_multi_threaded: u8,
    ) -> u8;
    pub fn leannative_verify_backend_choice(
        trip_count: u64,
        is_control_heavy: u8,
        has_metal_gpu: u8,
        is_page_aligned: u8,
        chosen_backend: u8,
    ) -> u8;
    pub fn turbo_spec_combined_step(i: u64) -> u64;
}

#[inline(always)]
pub fn verify_slice_bounds(off: u64, len: u64, cap: u64) -> bool {
    unsafe { leansys_verify_slice_bounds(off, len, cap) == 1 }
}

#[inline(always)]
pub fn verify_wal_frame(
    magic: u32,
    total_len: u32,
    avail_len: u64,
    expected_crc: u64,
    actual_crc: u64,
) -> bool {
    unsafe { leansys_verify_wal_frame(magic, total_len, avail_len, expected_crc, actual_crc) == 1 }
}

#[inline(always)]
pub fn verify_cas_digest(expected_hash: u64, actual_hash: u64, has_path_traversal: bool) -> bool {
    unsafe {
        leansys_verify_cas_digest(
            expected_hash,
            actual_hash,
            if has_path_traversal { 1 } else { 0 },
        ) == 1
    }
}

#[inline(always)]
pub fn check_http_bounds(
    headers_count: u32,
    content_len: u64,
    body_avail: u64,
    auth_ok: bool,
) -> bool {
    unsafe {
        leansys_check_http_bounds(
            headers_count,
            content_len,
            body_avail,
            if auth_ok { 1 } else { 0 },
        ) == 1
    }
}

#[inline(always)]
pub fn verify_jsonl_tape(
    key_off: u64,
    key_len: u64,
    val_off: u64,
    val_len: u64,
    buf_cap: u64,
    depth: u32,
) -> bool {
    unsafe { leansys_verify_jsonl_tape(key_off, key_len, val_off, val_len, buf_cap, depth) == 1 }
}

#[inline(always)]
pub fn verify_ring_cursor(head: u64, tail: u64, cap: u64, msg_len: u64) -> bool {
    unsafe { leansys_verify_ring_cursor(head, tail, cap, msg_len) == 1 }
}

#[inline(always)]
pub fn verify_sst_block(
    magic: u32,
    num_entries: u32,
    index_off: u64,
    footer_off: u64,
    file_size: u64,
    bloom_mask: u64,
) -> bool {
    unsafe {
        leansys_verify_sst_block(
            magic,
            num_entries,
            index_off,
            footer_off,
            file_size,
            bloom_mask,
        ) == 1
    }
}

#[inline(always)]
pub fn verify_poll_interest(
    active_conns: u32,
    max_conns: u32,
    keep_alive_reqs: u32,
    max_keep_alive: u32,
    idle_ms: u64,
    max_idle_ms: u64,
) -> bool {
    unsafe {
        leansys_verify_poll_interest(
            active_conns,
            max_conns,
            keep_alive_reqs,
            max_keep_alive,
            idle_ms.min(u32::MAX as u64) as u32,
            max_idle_ms.min(u32::MAX as u64) as u32,
        ) == 1
    }
}

#[inline(always)]
pub fn verify_rlimit_budget(
    rss_bytes: u64,
    max_rss_bytes: u64,
    elapsed_ms: u64,
    timeout_ms: u64,
    pipe_bytes: u64,
    max_pipe_bytes: u64,
) -> bool {
    unsafe {
        leansys_verify_rlimit_budget(
            rss_bytes,
            max_rss_bytes,
            elapsed_ms,
            timeout_ms,
            pipe_bytes,
            max_pipe_bytes,
        ) == 1
    }
}

#[inline(always)]
pub fn verify_composite_key_order(
    a_hi: u64,
    a_lo: u64,
    a_seq: u64,
    b_hi: u64,
    b_lo: u64,
    b_seq: u64,
) -> bool {
    unsafe { leansys_verify_composite_key_order(a_hi, a_lo, a_seq, b_hi, b_lo, b_seq) == 1 }
}

#[inline(always)]
pub fn verify_token_auth(
    match_cur: bool,
    has_prev: bool,
    match_prev: bool,
    scope_ok: bool,
    now_epoch: u64,
    expires_at: u64,
) -> bool {
    unsafe {
        leansys_verify_token_auth(
            match_cur as u8,
            has_prev as u8,
            match_prev as u8,
            scope_ok as u8,
            now_epoch,
            expires_at,
        ) == 1
    }
}

#[inline(always)]
pub fn verify_log_window(
    start_off: u64,
    next_off: u64,
    file_len: u64,
    max_chunk_bytes: u64,
) -> bool {
    unsafe { leansys_verify_log_window(start_off, next_off, file_len, max_chunk_bytes) == 1 }
}

#[inline(always)]
pub fn verify_jsonrpc_frame(has_v2: bool, has_id: bool, method_len: u32, frame_bytes: u64) -> bool {
    unsafe {
        leansys_verify_jsonrpc_frame(has_v2 as u8, has_id as u8, method_len, frame_bytes) == 1
    }
}

#[inline(always)]
pub fn mix64_word(acc: u64, word: u64) -> u64 {
    unsafe { leansys_mix64_word(acc, word) }
}

#[inline(always)]
pub fn verify_gate_admit(no_sorry_ax: bool, statement_pinned: bool, cert_verified: bool) -> bool {
    unsafe {
        leansys_gate_admit(
            no_sorry_ax as u8,
            statement_pinned as u8,
            cert_verified as u8,
        ) == 1
    }
}

#[inline(always)]
pub fn affine_step_budget(scale: u64, offset: u64, steps: u64) -> u64 {
    unsafe { turbo_spec_affine_step_budget(scale, offset, steps) }
}

#[inline(always)]
pub fn loop_step_budget(
    init_steps: u64,
    fuel: u64,
    scale: u64,
    offset: u64,
    iter_steps: u64,
) -> u64 {
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

#[inline(always)]
pub fn verify_dag_schedule_step(
    in_degree: u64,
    completed_deps: u64,
    total_deps: u64,
    visited_nodes: u64,
    total_nodes: u64,
) -> bool {
    unsafe {
        turbo_spec_verify_dag_schedule_step(
            in_degree,
            completed_deps,
            total_deps,
            visited_nodes,
            total_nodes,
        ) != 0
    }
}

#[inline(always)]
pub fn verify_module_cache_key(
    toolchain_match: bool,
    args_match: bool,
    src_match: bool,
    dep_oleans_match: bool,
    config_match: bool,
) -> bool {
    unsafe {
        turbo_spec_verify_module_cache_key(
            toolchain_match as u8,
            args_match as u8,
            src_match as u8,
            dep_oleans_match as u8,
            config_match as u8,
        ) != 0
    }
}

#[inline(always)]
pub fn verify_module_artifact_set(
    has_olean: bool,
    has_ilean: bool,
    is_module: bool,
    has_server_olean: bool,
    has_private_olean: bool,
    needs_c: bool,
    has_c: bool,
) -> bool {
    unsafe {
        turbo_spec_verify_module_artifact_set(
            has_olean as u8,
            has_ilean as u8,
            is_module as u8,
            has_server_olean as u8,
            has_private_olean as u8,
            needs_c as u8,
            has_c as u8,
        ) != 0
    }
}

#[inline(always)]
pub fn verify_static_lake_config(
    has_config: bool,
    has_dynamic_script: bool,
    has_unbuilt_extern_dep: bool,
    has_unsupported_facet: bool,
) -> bool {
    unsafe {
        turbo_spec_verify_static_lake_config(
            has_config as u8,
            has_dynamic_script as u8,
            has_unbuilt_extern_dep as u8,
            has_unsupported_facet as u8,
        ) != 0
    }
}

#[inline(always)]
pub fn verify_slice_pass_gate(
    slice_len: u64,
    min_grain: u64,
    simd_width: u64,
    non_aliasing: bool,
    lazy_reduction_homomorphic: bool,
) -> bool {
    unsafe {
        turbo_spec_verify_slice_pass_gate(
            slice_len,
            min_grain,
            simd_width,
            non_aliasing as u8,
            lazy_reduction_homomorphic as u8,
        ) != 0
    }
}

#[inline(always)]
pub fn verify_par_chunk(
    chunk_start: u64,
    chunk_end: u64,
    total_len: u64,
    min_grain: u64,
) -> bool {
    unsafe { leansys_verify_par_chunk(chunk_start, chunk_end, total_len, min_grain) == 1 }
}

#[inline(always)]
pub fn verify_arena_disjoint(
    off_a: u64,
    len_a: u64,
    off_b: u64,
    len_b: u64,
    arena_cap: u64,
) -> bool {
    unsafe { leansys_verify_arena_disjoint(off_a, len_a, off_b, len_b, arena_cap) == 1 }
}

#[inline(always)]
pub fn verify_tlz1_token(
    is_match: bool,
    offset: u64,
    token_len: u64,
    out_len: u64,
    uncompressed_cap: u64,
) -> bool {
    unsafe {
        turbo_spec_verify_tlz1_token(
            is_match as u8,
            offset,
            token_len,
            out_len,
            uncompressed_cap,
        ) != 0
    }
}

#[inline(always)]
pub fn verify_lexer_comment_guard(
    in_string: bool,
    is_escaped: bool,
    two_bytes_avail: bool,
    block_depth: u64,
    max_depth: u64,
) -> bool {
    unsafe {
        turbo_spec_verify_lexer_comment_guard(
            in_string as u8,
            is_escaped as u8,
            two_bytes_avail as u8,
            block_depth,
            max_depth,
        ) != 0
    }
}

#[inline(always)]
pub fn verify_farkas_step(
    obj_coeff: u64,
    col_sum: u64,
    acc_cost: u64,
    weight_cost: u64,
    bound: u64,
) -> bool {
    unsafe {
        turbo_spec_verify_farkas_step(obj_coeff, col_sum, acc_cost, weight_cost, bound) != 0
    }
}

#[inline(always)]
pub fn verify_ident_bloom(is_excluded_core: bool, cand_mask: u64, context_mask: u64) -> bool {
    unsafe { turbo_spec_verify_ident_bloom(is_excluded_core as u8, cand_mask, context_mask) != 0 }
}

#[inline(always)]
pub fn verify_counterexample_triage(
    has_violation: bool,
    has_missing_hyp_hint: bool,
    ref_disagrees_with_candidate: bool,
    triage_class: u8,
) -> bool {
    unsafe {
        leansys_verify_counterexample_triage(
            has_violation as u8,
            has_missing_hyp_hint as u8,
            ref_disagrees_with_candidate as u8,
            triage_class,
        ) == 1
    }
}

#[inline(always)]
pub fn verify_snapshot_visibility(
    entry_seq: u64,
    max_snapshot_seq: u64,
    is_tombstone: bool,
) -> bool {
    unsafe {
        leansys_verify_snapshot_visibility(entry_seq, max_snapshot_seq, is_tombstone as u8) == 1
    }
}

#[inline(always)]
pub fn verify_http_route_match(
    method_match: bool,
    path_match: bool,
    route_idx: u32,
    route_count: u32,
) -> bool {
    unsafe {
        leansys_verify_http_route_match(
            method_match as u8,
            path_match as u8,
            route_idx,
            route_count,
        ) == 1
    }
}

#[inline(always)]
pub fn pack_slice_span_u64(start: u64, len: u64, kind: u64) -> u64 {
    unsafe { leannative_pack_slice_span_u64(start, len, kind) }
}

#[inline(always)]
pub fn leannative_eval_u64_binop_safe(op: u8, lhs: u64, rhs: u64) -> u64 {
    unsafe { leannative_eval_u64_binop(op, lhs, rhs) }
}

#[inline(always)]
pub fn leannative_has_domain_hazard_u64_safe(op: u8, lhs: u64, rhs: u64) -> bool {
    unsafe { leannative_has_domain_hazard_u64(op, lhs, rhs) == 1 }
}

#[inline(always)]
pub fn leannative_fastcheck_rewrite_step_safe(
    lhs_val: u64,
    rhs_val: u64,
    op_lhs: u8,
    op_rhs: u8,
    a: u64,
    b: u64,
    ref_disagrees: bool,
) -> u8 {
    unsafe {
        leannative_fastcheck_rewrite_step(
            lhs_val,
            rhs_val,
            op_lhs,
            op_rhs,
            a,
            b,
            ref_disagrees as u8,
        )
    }
}

#[inline(always)]
pub fn leannative_certify_cex_witnesses_safe(x1: u64, dm_a0: u64, dm_b0: u64) -> bool {
    unsafe { leannative_certify_cex_witnesses(x1, dm_a0, dm_b0) == 1 }
}

#[inline(always)]
pub fn verify_dag_wave_step(
    in_degree_sum: u64,
    wave_size: u64,
    completed_tasks: u64,
    total_tasks: u64,
    active_workers: u64,
    max_workers: u64,
) -> bool {
    unsafe {
        leansys_verify_dag_wave_step(
            in_degree_sum,
            wave_size,
            completed_tasks,
            total_tasks,
            active_workers,
            max_workers,
        ) == 1
    }
}

#[inline(always)]
pub fn verify_parfor_chunk_partition(
    chunk_start: u64,
    chunk_end: u64,
    total_len: u64,
    min_grain: u64,
    active_workers: u64,
    max_workers: u64,
) -> bool {
    unsafe {
        leannative_verify_parfor_chunk_partition(
            chunk_start,
            chunk_end,
            total_len,
            min_grain,
            active_workers,
            max_workers,
        ) == 1
    }
}

#[inline(always)]
pub fn verify_ios_jetsam_budget(
    dirty_rss_bytes: u64,
    alloc_bytes: u64,
    max_jetsam_bytes: u64,
    page_align_mask: u64,
    is_app_extension: bool,
) -> bool {
    unsafe {
        leansys_verify_ios_jetsam_budget(
            dirty_rss_bytes,
            alloc_bytes,
            max_jetsam_bytes,
            page_align_mask,
            is_app_extension as u8,
        ) == 1
    }
}

#[inline(always)]
pub fn verify_worker_budget(
    active_workers: u64,
    max_workers: u64,
    micro_chunks: u64,
    total_len: u64,
    is_mobile_hetero: bool,
) -> bool {
    unsafe {
        leansys_verify_worker_budget(
            active_workers,
            max_workers,
            micro_chunks,
            total_len,
            is_mobile_hetero as u8,
        ) == 1
    }
}

#[inline(always)]
pub fn verify_rc_mode_safe(
    rc_mode: u8,
    has_heap_allocs: bool,
    is_multi_threaded: bool,
) -> bool {
    unsafe {
        leannative_verify_rc_mode_safe(
            rc_mode,
            has_heap_allocs as u8,
            is_multi_threaded as u8,
        ) == 1
    }
}

#[inline(always)]
pub fn verify_backend_choice(
    trip_count: u64,
    is_control_heavy: bool,
    has_metal_gpu: bool,
    is_page_aligned: bool,
    chosen_backend: u8,
) -> bool {
    unsafe {
        leannative_verify_backend_choice(
            trip_count,
            is_control_heavy as u8,
            has_metal_gpu as u8,
            is_page_aligned as u8,
            chosen_backend,
        ) == 1
    }
}

/// Extract semantic `(has_missing_hyp, ref_disagrees)` booleans emitted by `lean-native-core`
/// inside a `counterexample_triage` JSON object.
pub fn extract_lean_native_triage_booleans(val: &serde_json::Value) -> Option<(bool, bool)> {
    let t = val.get("counterexample_triage").unwrap_or(val);
    let has_missing_hyp = t.get("has_missing_hyp").and_then(|v| v.as_bool())?;
    let ref_disagrees = t.get("ref_disagrees").and_then(|v| v.as_bool())?;
    Some((has_missing_hyp, ref_disagrees))
}

/// Build a `counterexample_triage` JSON object consuming only measured witness evaluation values
/// (`lhs_val`, `rhs_val`) and the semantic `(has_missing_hyp, ref_disagrees)` booleans from `lean-native-core`.
/// When `lhs_val`/`rhs_val` are absent or `semantic_triage` is unavailable, emits `"Unclassified"`.
pub fn build_counterexample_triage_json(
    lhs_val: Option<&str>,
    rhs_val: Option<&str>,
    semantic_triage: Option<(bool, bool)>,
) -> serde_json::Value {
    let vals_differ = match (lhs_val, rhs_val) {
        (Some(l), Some(r)) => {
            !l.trim().is_empty() && !r.trim().is_empty() && l.trim() != r.trim()
        }
        _ => false,
    };
    let (has_missing_hyp, ref_disagrees, code, label) = match semantic_triage {
        Some((missing_hyp, ref_dis)) if vals_differ => {
            let eff_ref_dis = !missing_hyp && ref_dis;
            let c = if missing_hyp {
                1u8
            } else if eff_ref_dis {
                2u8
            } else {
                3u8
            };
            let l = match c {
                1 => "SpecTooStrong",
                2 => "ReferenceDiscrepancy",
                _ => "CandidateBug",
            };
            (missing_hyp, eff_ref_dis, c, l)
        }
        _ => (false, false, 0u8, "Unclassified"),
    };
    let classification_consistent =
        verify_counterexample_triage(vals_differ, has_missing_hyp, ref_disagrees, code);
    serde_json::json!({
        "classification": label,
        "classification_code": code,
        "has_missing_hyp": has_missing_hyp,
        "ref_disagrees": ref_disagrees,
        "vals_differ": vals_differ,
        "lhs_value": lhs_val,
        "rhs_value": rhs_val,
        "classification_consistent": classification_consistent,
    })
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
        if !verify_farkas_step(c_j, col_sum.min(u64::MAX as u128) as u64, 0, 0, bound) {
            return false;
        }
    }
    let mut rhs_dot: u64 = 0;
    for (i, &w_i) in weights.iter().enumerate() {
        let b_i = rhs.get(i).copied().unwrap_or(0);
        let prod = (w_i as u128).saturating_mul(b_i as u128);
        if prod > bound as u128 || !verify_farkas_step(0, 0, rhs_dot, prod as u64, bound) {
            return false;
        }
        rhs_dot += prod as u64;
    }
    rhs_dot <= bound
}

/// Deterministic, zero-unsafe Farkas certificate synthesizer over `u64` (up to 8 rows).
/// Searches for small non-negative integer multipliers `weights` (`w_i in 0..=16`)
/// such that `check_farkas_nat(&weights, matrix, rhs, obj, bound)` holds, preferring
/// minimal L1 weight norm `sum_i w_i`. Every candidate is verified by `check_farkas_nat`.
pub fn synthesize_farkas_nat_weights(
    matrix: &[Vec<u64>],
    rhs: &[u64],
    obj: &[u64],
    bound: u64,
) -> Option<Vec<u64>> {
    let m = matrix.len();
    if m == 0 || m > 32 || rhs.len() < m {
        return None;
    }
    let n = obj.len();
    let zero_w = vec![0u64; m];
    if check_farkas_nat(&zero_w, matrix, rhs, obj, bound) {
        return Some(zero_w);
    }

    let binding_cols: Vec<usize> = (0..n).filter(|&j| obj[j] > 0).collect();
    let cand_rows: Vec<usize> = (0..m)
        .filter(|&i| {
            rhs[i] <= bound
                && binding_cols
                    .iter()
                    .any(|&j| matrix[i].get(j).copied().unwrap_or(0) > 0)
        })
        .collect();
    if cand_rows.is_empty() {
        return None;
    }

    let dominated_by = |i: usize, k: usize| -> bool {
        if k == i || rhs[k] > rhs[i] {
            return false;
        }
        let mut strict = rhs[k] < rhs[i];
        for &j in &binding_cols {
            let a = matrix[k].get(j).copied().unwrap_or(0);
            let b = matrix[i].get(j).copied().unwrap_or(0);
            if a < b {
                return false;
            }
            strict |= a > b;
        }
        strict || k < i
    };
    let mut active_idx: Vec<usize> = cand_rows
        .iter()
        .copied()
        .filter(|&i| !cand_rows.iter().any(|&k| dominated_by(i, k)))
        .collect();
    if active_idx.is_empty() || active_idx.len() > 12 {
        return None;
    }
    let coverage = |i: usize| -> u128 {
        binding_cols
            .iter()
            .map(|&j| matrix[i].get(j).copied().unwrap_or(0) as u128)
            .sum()
    };
    active_idx.sort_by(|&a, &b| {
        rhs[a]
            .cmp(&rhs[b])
            .then(coverage(b).cmp(&coverage(a)))
            .then(a.cmp(&b))
    });

    // 1. Unit vectors e_i and scaled unit vectors k * e_i (k in 1..=16)
    for k in 1..=16u64 {
        for &i in &active_idx {
            if k.saturating_mul(rhs[i]) > bound {
                continue;
            }
            let mut w = vec![0u64; m];
            w[i] = k;
            if check_farkas_nat(&w, matrix, rhs, obj, bound) {
                return Some(w);
            }
        }
    }

    // 2. Pairwise combinations k1 * e_i + k2 * e_j Ordered by L1 norm (k1 + k2 <= 16)
    for l1_sum in 2..=16u64 {
        for a_pos in 0..active_idx.len() {
            let i = active_idx[a_pos];
            for b_pos in (a_pos + 1)..active_idx.len() {
                let j = active_idx[b_pos];
                for k1 in 1..l1_sum {
                    let k2 = l1_sum - k1;
                    let cost = (k1 as u128)
                        .saturating_mul(rhs[i] as u128)
                        .saturating_add((k2 as u128).saturating_mul(rhs[j] as u128));
                    if cost > bound as u128 {
                        continue;
                    }
                    let mut w = vec![0u64; m];
                    w[i] = k1;
                    w[j] = k2;
                    if check_farkas_nat(&w, matrix, rhs, obj, bound) {
                        return Some(w);
                    }
                }
            }
        }
    }

    // 3. Bounded branch-and-bound / iterative deepening over active rows (up to L1 <= 16)
    let act_matrix: Vec<Vec<u64>> = active_idx.iter().map(|&i| matrix[i].clone()).collect();
    let act_rhs: Vec<u64> = active_idx.iter().map(|&i| rhs[i]).collect();
    let act_m = active_idx.len();

    fn dfs_farkas(
        idx: usize,
        m: usize,
        n: usize,
        rem_l1: u64,
        rem_bound: u128,
        cur_w: &mut [u64],
        col_sums: &mut [u128],
        matrix: &[Vec<u64>],
        rhs: &[u64],
        obj: &[u64],
        bound: u64,
    ) -> bool {
        if col_sums
            .iter()
            .zip(obj.iter())
            .all(|(&cs, &cj)| cs >= cj as u128)
        {
            return check_farkas_nat(cur_w, matrix, rhs, obj, bound);
        }
        if idx == m || rem_l1 == 0 {
            return false;
        }
        // Optimistic pruning: even if we put all `rem_l1` on the max coefficient in suffix `idx..m`, can we cover `obj[j]`?
        for j in 0..n {
            if col_sums[j] < obj[j] as u128 {
                let max_a = (idx..m)
                    .filter_map(|r| matrix.get(r).and_then(|row| row.get(j)).copied())
                    .max()
                    .unwrap_or(0);
                if col_sums[j].saturating_add((rem_l1 as u128).saturating_mul(max_a as u128))
                    < obj[j] as u128
                {
                    return false;
                }
            }
        }
        let b_i = rhs[idx] as u128;
        let max_wi_by_bound = if b_i == 0 {
            rem_l1
        } else {
            (rem_bound / b_i).min(rem_l1 as u128) as u64
        };
        let max_wi = max_wi_by_bound.min(16);
        let target_exact = idx + 1 == m;
        let start_wi = if target_exact { rem_l1 } else { 0 };
        if start_wi > max_wi {
            return false;
        }
        for wi in start_wi..=max_wi {
            cur_w[idx] = wi;
            if wi > 0 {
                for j in 0..n {
                    let a_ij = matrix[idx].get(j).copied().unwrap_or(0) as u128;
                    col_sums[j] = col_sums[j].saturating_add((wi as u128) * a_ij);
                }
            }
            let next_bound = rem_bound - (wi as u128) * b_i;
            if dfs_farkas(
                idx + 1,
                m,
                n,
                rem_l1 - wi,
                next_bound,
                cur_w,
                col_sums,
                matrix,
                rhs,
                obj,
                bound,
            ) {
                return true;
            }
            if wi > 0 {
                for j in 0..n {
                    let a_ij = matrix[idx].get(j).copied().unwrap_or(0) as u128;
                    col_sums[j] -= (wi as u128) * a_ij;
                }
            }
            cur_w[idx] = 0;
        }
        false
    }

    for total_l1 in 3..=16u64 {
        let mut act_w = vec![0u64; act_m];
        let mut col_sums = vec![0u128; n];
        if dfs_farkas(
            0,
            act_m,
            n,
            total_l1,
            bound as u128,
            &mut act_w,
            &mut col_sums,
            &act_matrix,
            &act_rhs,
            obj,
            bound,
        ) {
            let mut full_w = vec![0u64; m];
            for (pos, &orig_i) in active_idx.iter().enumerate() {
                full_w[orig_i] = act_w[pos];
            }
            if check_farkas_nat(&full_w, matrix, rhs, obj, bound) {
                return Some(full_w);
            }
        }
    }

    None
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
        assert_eq!(
            loop_step_budget(23132, 10, 2, 5, 100),
            23132 + 10 * (2 * 100 + 5)
        );
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
        assert!(!verify_poll_interest(65, 64, 2, 100, 50, 5000));
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
        assert!(verify_gate_admit(true, true, true));
        assert!(!verify_gate_admit(false, true, true));
        assert!(!verify_gate_admit(true, false, true));
        assert!(!verify_gate_admit(true, true, false));
        assert_eq!(matryoshka_tier_router(880, 120, 380, 15, false, false), 0);
        assert_eq!(matryoshka_tier_router(50, 120, 380, 15, false, false), 1);
        assert_eq!(matryoshka_tier_router(110, 120, 380, 15, false, false), 2);
        assert_eq!(matryoshka_tier_router(900, 120, 380, 15, true, false), 1);
        assert_eq!(matryoshka_tier_router(900, 120, 380, 15, false, true), 2);
        assert!(verify_slice_pass_gate(256, 64, 4, true, true));
        assert!(!verify_slice_pass_gate(256, 64, 4, false, true));
        assert!(verify_par_chunk(0, 64, 256, 64));
        assert!(!verify_par_chunk(0, 32, 256, 64));
        assert!(verify_arena_disjoint(0, 128, 128, 128, 256));
        assert!(!verify_arena_disjoint(0, 128, 64, 128, 256));
        assert!(verify_tlz1_token(true, 4, 8, 16, 64));
        assert!(!verify_tlz1_token(true, 0, 8, 16, 64));
        assert!(!verify_tlz1_token(false, 0, 50, 20, 64));
        assert!(verify_lexer_comment_guard(false, false, true, 1, 64));
        assert!(!verify_lexer_comment_guard(true, false, true, 1, 64));
        assert!(verify_farkas_step(5, 6, 20, 15, 35));
        assert!(!verify_farkas_step(5, 6, 20, 16, 35));
        assert!(verify_ident_bloom(false, 0x101, 0x301));
        assert!(!verify_ident_bloom(false, 0x100, 0x003));
        assert!(!verify_ident_bloom(true, 0x101, 0x301));
        assert!(verify_counterexample_triage(true, true, false, 1));
        assert!(!verify_counterexample_triage(true, true, false, 3));
        assert!(verify_counterexample_triage(true, false, true, 2));
        assert!(verify_counterexample_triage(true, false, false, 3));
        assert!(!verify_counterexample_triage(false, true, false, 1));
        assert!(verify_snapshot_visibility(5, 10, false));
        assert!(!verify_snapshot_visibility(15, 10, false));
        assert!(!verify_snapshot_visibility(5, 10, true));
        assert!(verify_http_route_match(true, true, 0, 2));
        assert!(!verify_http_route_match(false, true, 0, 2));
        assert!(!verify_http_route_match(true, true, 2, 2));
        assert_eq!(pack_slice_span_u64(10, 25, 3), 0x0000_000A_0000_1903);
        assert_eq!(leannative_eval_u64_binop_safe(0, 1_000_000, 42), 1_000_042);
        assert!(leannative_has_domain_hazard_u64_safe(3, 42, 0));
        assert!(!leannative_has_domain_hazard_u64_safe(0, 10, 20));
        assert_eq!(
            leannative_fastcheck_rewrite_step_safe(0, 1, 3, 0, 1, 0, false),
            1
        );
        assert_eq!(
            leannative_fastcheck_rewrite_step_safe(4, 3, 0, 0, 1, 2, true),
            2
        );
        assert_eq!(
            leannative_fastcheck_rewrite_step_safe(4, 3, 0, 0, 1, 2, false),
            3
        );
        assert!(leannative_certify_cex_witnesses_safe(
            1_000_000,
            0,
            u64::MAX
        ));
        assert!(verify_dag_wave_step(0, 4, 8, 16, 4, 4));
        assert!(!verify_dag_wave_step(1, 4, 8, 16, 4, 4));
        assert!(!verify_dag_wave_step(0, 0, 8, 16, 4, 4));
        assert!(verify_parfor_chunk_partition(0, 64, 256, 64, 4, 8));
        assert!(!verify_parfor_chunk_partition(64, 64, 256, 64, 4, 8));
        assert!(!verify_parfor_chunk_partition(0, 32, 256, 64, 4, 8));
        assert!(verify_ios_jetsam_budget(33_554_432, 33_554_432, 268_435_456, 16383, false));
        assert!(!verify_ios_jetsam_budget(200_000_000, 100_000_000, 268_435_456, 16383, false));
        assert!(!verify_ios_jetsam_budget(8_388_608, 8_388_608, 268_435_456, 16383, true));
        assert!(verify_ios_jetsam_budget(8_388_608, 8_388_608, 25_165_824, 16383, true));
        assert!(verify_rc_mode_safe(0, false, true));
        assert!(!verify_rc_mode_safe(0, true, false));
        assert!(!verify_rc_mode_safe(1, true, true));
        assert!(verify_rc_mode_safe(2, true, true));
        assert!(verify_worker_budget(4, 6, 24, 1024, true));
        assert!(!verify_worker_budget(4, 8, 24, 1024, true));
        assert!(!verify_worker_budget(0, 6, 24, 1024, true));
        assert!(verify_backend_choice(262_144, false, true, true, 1));
        assert!(!verify_backend_choice(65_536, false, true, true, 1));
        assert!(verify_backend_choice(65_536, false, true, true, 0));
        assert!(!verify_backend_choice(262_144, false, true, false, 1));
        let t1 = build_counterexample_triage_json(Some("0"), Some("1"), Some((true, false)));
        assert_eq!(t1["classification"], "SpecTooStrong");
        assert_eq!(t1["classification_consistent"], true);
        let t2 = build_counterexample_triage_json(Some("4"), Some("3"), Some((false, true)));
        assert_eq!(t2["classification"], "ReferenceDiscrepancy");
        assert_eq!(t2["classification_consistent"], true);
        let t3 = build_counterexample_triage_json(Some("4"), Some("3"), Some((false, false)));
        assert_eq!(t3["classification"], "CandidateBug");
        assert_eq!(t3["classification_consistent"], true);
        let t_same = build_counterexample_triage_json(Some("4"), Some("4"), Some((false, false)));
        assert_eq!(t_same["classification"], "Unclassified");
        assert_eq!(t_same["vals_differ"], false);
        assert_eq!(t_same["classification_consistent"], false);
        let t_none = build_counterexample_triage_json(None, None, Some((false, false)));
        assert_eq!(t_none["classification"], "Unclassified");
        assert_eq!(t_none["vals_differ"], false);
        assert_eq!(t_none["classification_consistent"], false);
        let t_unclass = build_counterexample_triage_json(Some("4"), Some("3"), None);
        assert_eq!(t_unclass["classification"], "Unclassified");
        assert_eq!(t_unclass["classification_consistent"], false);
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

        let synth = synthesize_farkas_nat_weights(&matrix, &rhs, &obj, 35)
            .expect("should synthesize weights");
        assert_eq!(synth, vec![2, 1]);
        assert!(check_farkas_nat(&synth, &matrix, &rhs, &obj, 35));
        assert!(synthesize_farkas_nat_weights(&matrix, &rhs, &obj, 34).is_none());

        // 3-row system: x0 + x1 <= 4, x1 + x2 <= 5, x0 + x2 <= 7 -> 2*x0 + 2*x1 + 2*x2 <= 16
        let m3 = vec![vec![1, 1, 0], vec![0, 1, 1], vec![1, 0, 1]];
        let r3 = vec![4, 5, 7];
        let o3 = vec![2, 2, 2];
        let w3 = synthesize_farkas_nat_weights(&m3, &r3, &o3, 16).expect("3-row farkas");
        assert_eq!(w3, vec![1, 1, 1]);
        assert!(check_farkas_nat(&w3, &m3, &r3, &o3, 16));
    }
}
