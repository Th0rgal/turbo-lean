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
    pub fn turbo_spec_verify_con_leche_shard(
        magic: u32,
        decl_count: u64,
        off_end: u64,
        byte_len: u64,
        all_decls_typed: u8,
    ) -> u8;
    pub fn turbo_spec_verify_elab_header_pin(
        decl_name_non_empty: u8,
        no_shadowed_consts: u8,
        ast_matches_pin: u8,
        cas_blob_magic_ok: u8,
        cas_off_end_matches: u8,
    ) -> u8;
    pub fn turbo_spec_verify_audit_materialize_gate(
        skeleton_clean: u8,
        stubbed_placeholder_count: u64,
        certified_shard_count: u64,
        distinct_covered_shard_count: u64,
        total_shard_count: u64,
        expected_interface_digest: u64,
        actual_interface_digest: u64,
        expected_olean_digest: u64,
        actual_olean_digest: u64,
        expected_ilean_digest: u64,
        actual_ilean_digest: u64,
        needs_c: u8,
        expected_c_digest: u64,
        actual_c_digest: u64,
        dep_trace_digest: u64,
        audited_artifact_digest: u64,
        kernel_audit_clean: u8,
    ) -> u8;
    pub fn turbo_spec_verify_pack_trust_admission(
        requested_untrusted: u8,
        has_trusted_pubkey: u8,
        has_attestation_fields: u8,
        sig_valid: u8,
        allow_unattested_trusted: u8,
    ) -> u8;
    pub fn turbo_spec_verify_hygiene_item_admitted(
        item_kind: u8,
        admits_native_decide: u8,
        admits_bv_decide: u8,
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
        topology_kind: u8,
    ) -> u8;
    pub fn leansys_verify_page_aligned_buffer(
        addr: u64,
        alloc_bytes: u64,
        capacity_bytes: u64,
        dirty_rss_bytes: u64,
        max_budget_bytes: u64,
        page_align_mask: u64,
    ) -> u8;
    pub fn leansys_select_isa(
        detected_hw_caps: u64,
        required_mask: u64,
        requested_variant_id: u8,
        max_variant_id: u8,
    ) -> u8;
    pub fn leansys_verify_isa_selection(
        detected_hw_caps: u64,
        required_mask: u64,
        selected_variant_id: u8,
        max_variant_id: u8,
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
    pub fn lean_native_ntt_butterfly_fused_2layer_slice(
        a_lo: u64,
        a_hi: u64,
        b_lo: u64,
        b_hi: u64,
        c_lo: u64,
        c_hi: u64,
        d_lo: u64,
        d_hi: u64,
        to_lo: u64,
        to_hi: u64,
        tia_lo: u64,
        tia_hi: u64,
        tib_lo: u64,
        tib_hi: u64,
        out_word: u64,
    ) -> u64;
    pub fn turbo_spec_combined_step(i: u64) -> u64;
}

#[inline(always)]
pub fn spec_audit_witness_gate(pos_ok: bool, neg_refuted: bool) -> bool {
    unsafe { turbo_spec_audit_witness_gate(u8::from(pos_ok), u8::from(neg_refuted)) != 0 }
}

#[inline(always)]
pub fn verify_con_leche_shard(
    magic: u32,
    decl_count: u64,
    off_end: u64,
    byte_len: u64,
    all_decls_typed: bool,
) -> bool {
    unsafe {
        turbo_spec_verify_con_leche_shard(
            magic,
            decl_count,
            off_end,
            byte_len,
            if all_decls_typed { 1 } else { 0 },
        ) == 1
    }
}

/// Universe level AST mirroring `ConLeche.Level` (`lean/TurboLean/ConLeche.lean`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConLecheLevel {
    Zero,
    Succ(Box<ConLecheLevel>),
    Max(Box<ConLecheLevel>, Box<ConLecheLevel>),
    IMax(Box<ConLecheLevel>, Box<ConLecheLevel>),
    Param(String),
}

impl ConLecheLevel {
    pub fn ast_size(&self) -> usize {
        match self {
            Self::Zero | Self::Param(_) => 1,
            Self::Succ(u) => u.ast_size() + 1,
            Self::Max(u, v) | Self::IMax(u, v) => u.ast_size() + v.ast_size() + 1,
        }
    }

    pub fn eval_with_param(&self, param_val: &dyn Fn(&str) -> usize) -> usize {
        match self {
            Self::Zero => 0,
            Self::Succ(u) => u.eval_with_param(param_val) + 1,
            Self::Max(u, v) => u.eval_with_param(param_val).max(v.eval_with_param(param_val)),
            Self::IMax(u, v) => {
                let ve = v.eval_with_param(param_val);
                if ve == 0 {
                    0
                } else {
                    u.eval_with_param(param_val).max(ve)
                }
            }
            Self::Param(p) => param_val(p),
        }
    }

    pub fn eval(&self) -> usize {
        self.eval_with_param(&|_| 1)
    }

    pub fn has_no_param(&self) -> bool {
        match self {
            Self::Zero => true,
            Self::Succ(u) => u.has_no_param(),
            Self::Max(u, v) | Self::IMax(u, v) => u.has_no_param() && v.has_no_param(),
            Self::Param(_) => false,
        }
    }

    pub fn level_def_eq(u1: &Self, u2: &Self) -> bool {
        u1 == u2 || (u1.has_no_param() && u2.has_no_param() && u1.eval() == u2.eval())
    }

    pub fn lookup_param(params: &[String], args: &[ConLecheLevel], name: &str) -> ConLecheLevel {
        for (p, a) in params.iter().zip(args.iter()) {
            if p == name {
                return a.clone();
            }
        }
        ConLecheLevel::Param(name.to_string())
    }

    pub fn subst_params(&self, params: &[String], args: &[ConLecheLevel]) -> ConLecheLevel {
        match self {
            Self::Zero => Self::Zero,
            Self::Succ(u) => Self::Succ(Box::new(u.subst_params(params, args))),
            Self::Max(u, v) => Self::Max(
                Box::new(u.subst_params(params, args)),
                Box::new(v.subst_params(params, args)),
            ),
            Self::IMax(u, v) => Self::IMax(
                Box::new(u.subst_params(params, args)),
                Box::new(v.subst_params(params, args)),
            ),
            Self::Param(name) => Self::lookup_param(params, args, name),
        }
    }
}

/// Dependent CIC expression AST mirroring `ConLeche.Expr` (`lean/TurboLean/ConLeche.lean`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConLecheExpr {
    BVar(usize),
    Sort(ConLecheLevel),
    Const(String, Vec<ConLecheLevel>),
    App(Box<ConLecheExpr>, Box<ConLecheExpr>),
    Lam(Box<ConLecheExpr>, Box<ConLecheExpr>),
    ForallE(Box<ConLecheExpr>, Box<ConLecheExpr>),
    LetE(Box<ConLecheExpr>, Box<ConLecheExpr>, Box<ConLecheExpr>),
}

impl ConLecheExpr {
    pub fn ast_size(&self) -> usize {
        match self {
            Self::BVar(_) | Self::Sort(_) | Self::Const(_, _) => 1,
            Self::App(f, a) | Self::Lam(f, a) | Self::ForallE(f, a) => {
                f.ast_size() + a.ast_size() + 1
            }
            Self::LetE(t, v, b) => t.ast_size() + v.ast_size() + b.ast_size() + 1,
        }
    }

    pub fn instantiate_level_params(
        &self,
        params: &[String],
        args: &[ConLecheLevel],
    ) -> ConLecheExpr {
        if params.is_empty() {
            return self.clone();
        }
        match self {
            Self::BVar(i) => Self::BVar(*i),
            Self::Sort(u) => Self::Sort(u.subst_params(params, args)),
            Self::Const(c, lvls) => Self::Const(
                c.clone(),
                lvls.iter().map(|u| u.subst_params(params, args)).collect(),
            ),
            Self::App(f, a) => Self::App(
                Box::new(f.instantiate_level_params(params, args)),
                Box::new(a.instantiate_level_params(params, args)),
            ),
            Self::Lam(d, b) => Self::Lam(
                Box::new(d.instantiate_level_params(params, args)),
                Box::new(b.instantiate_level_params(params, args)),
            ),
            Self::ForallE(d, b) => Self::ForallE(
                Box::new(d.instantiate_level_params(params, args)),
                Box::new(b.instantiate_level_params(params, args)),
            ),
            Self::LetE(t, v, b) => Self::LetE(
                Box::new(t.instantiate_level_params(params, args)),
                Box::new(v.instantiate_level_params(params, args)),
                Box::new(b.instantiate_level_params(params, args)),
            ),
        }
    }

    pub fn lift(&self, delta: usize, cutoff: usize) -> ConLecheExpr {
        match self {
            Self::BVar(idx) => {
                if *idx >= cutoff {
                    Self::BVar(*idx + delta)
                } else {
                    Self::BVar(*idx)
                }
            }
            Self::Sort(u) => Self::Sort(u.clone()),
            Self::Const(c, lvls) => Self::Const(c.clone(), lvls.clone()),
            Self::App(f, a) => {
                Self::App(Box::new(f.lift(delta, cutoff)), Box::new(a.lift(delta, cutoff)))
            }
            Self::Lam(d, b) => Self::Lam(
                Box::new(d.lift(delta, cutoff)),
                Box::new(b.lift(delta, cutoff + 1)),
            ),
            Self::ForallE(d, b) => Self::ForallE(
                Box::new(d.lift(delta, cutoff)),
                Box::new(b.lift(delta, cutoff + 1)),
            ),
            Self::LetE(t, v, b) => Self::LetE(
                Box::new(t.lift(delta, cutoff)),
                Box::new(v.lift(delta, cutoff)),
                Box::new(b.lift(delta, cutoff + 1)),
            ),
        }
    }

    pub fn subst(&self, s: &ConLecheExpr, k: usize) -> ConLecheExpr {
        match self {
            Self::BVar(idx) => {
                if *idx == k {
                    s.lift(k, 0)
                } else if *idx > k {
                    Self::BVar(*idx - 1)
                } else {
                    Self::BVar(*idx)
                }
            }
            Self::Sort(u) => Self::Sort(u.clone()),
            Self::Const(c, lvls) => Self::Const(c.clone(), lvls.clone()),
            Self::App(f, a) => Self::App(Box::new(f.subst(s, k)), Box::new(a.subst(s, k))),
            Self::Lam(d, b) => Self::Lam(Box::new(d.subst(s, k)), Box::new(b.subst(s, k + 1))),
            Self::ForallE(d, b) => {
                Self::ForallE(Box::new(d.subst(s, k)), Box::new(b.subst(s, k + 1)))
            }
            Self::LetE(t, v, b) => Self::LetE(
                Box::new(t.subst(s, k)),
                Box::new(v.subst(s, k)),
                Box::new(b.subst(s, k + 1)),
            ),
        }
    }

    pub fn inst0(arg: &ConLecheExpr, body: &ConLecheExpr) -> ConLecheExpr {
        body.subst(arg, 0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConLecheDecl {
    pub name: String,
    pub level_params: Vec<String>,
    pub ty: ConLecheExpr,
    pub val: ConLecheExpr,
    pub wf_tag: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConLecheRecRule {
    pub rec_name: String,
    pub ctor_name: String,
    pub level_params: Vec<String>,
    pub rhs_template: ConLecheExpr,
    pub arg_dom: ConLecheExpr,
    pub ind_ty: ConLecheExpr,
    pub result_cod: ConLecheExpr,
    pub is_dependent: bool,
}

impl ConLecheRecRule {
    pub fn ctor_expected_inst(&self, lvls: &[ConLecheLevel]) -> ConLecheExpr {
        let arg_dom_inst = self.arg_dom.instantiate_level_params(&self.level_params, lvls);
        let ind_ty_inst = self.ind_ty.instantiate_level_params(&self.level_params, lvls);
        ConLecheExpr::ForallE(Box::new(arg_dom_inst), Box::new(ind_ty_inst.lift(1, 0)))
    }

    pub fn rec_expected_inst(&self, lvls: &[ConLecheLevel]) -> ConLecheExpr {
        let ind_ty_inst = self.ind_ty.instantiate_level_params(&self.level_params, lvls);
        let res_cod_inst = self.result_cod.instantiate_level_params(&self.level_params, lvls);
        if self.is_dependent {
            ConLecheExpr::ForallE(
                Box::new(ind_ty_inst),
                Box::new(ConLecheExpr::App(
                    Box::new(res_cod_inst.lift(1, 0)),
                    Box::new(ConLecheExpr::BVar(0)),
                )),
            )
        } else {
            ConLecheExpr::ForallE(Box::new(ind_ty_inst), Box::new(res_cod_inst.lift(1, 0)))
        }
    }

    pub fn rhs_expected_inst(&self, lvls: &[ConLecheLevel]) -> ConLecheExpr {
        let arg_dom_inst = self.arg_dom.instantiate_level_params(&self.level_params, lvls);
        let res_cod_inst = self.result_cod.instantiate_level_params(&self.level_params, lvls);
        if self.is_dependent {
            ConLecheExpr::ForallE(
                Box::new(arg_dom_inst),
                Box::new(ConLecheExpr::App(
                    Box::new(res_cod_inst.lift(1, 0)),
                    Box::new(ConLecheExpr::App(
                        Box::new(ConLecheExpr::Const(self.ctor_name.clone(), lvls.to_vec())),
                        Box::new(ConLecheExpr::BVar(0)),
                    )),
                )),
            )
        } else {
            ConLecheExpr::ForallE(Box::new(arg_dom_inst), Box::new(res_cod_inst.lift(1, 0)))
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConLecheEnv {
    pub decls: Vec<ConLecheDecl>,
    pub rec_rules: Vec<ConLecheRecRule>,
    pub header_magic: u32,
}

impl ConLecheEnv {
    pub fn lookup(&self, name: &str) -> Option<&ConLecheDecl> {
        self.decls.iter().find(|d| d.name == name)
    }
}

pub fn eval_iota_step(rule: &ConLecheRecRule, e: &ConLecheExpr) -> Option<ConLecheExpr> {
    if let ConLecheExpr::App(r_fn, c_app) = e {
        if let (ConLecheExpr::Const(r_name, r_lvls), ConLecheExpr::App(c_fn, payload)) =
            (r_fn.as_ref(), c_app.as_ref())
        {
            if let ConLecheExpr::Const(c_name, c_lvls) = c_fn.as_ref() {
                if r_name == &rule.rec_name
                    && c_name == &rule.ctor_name
                    && r_lvls == c_lvls
                    && rule.level_params.len() == r_lvls.len()
                {
                    return Some(ConLecheExpr::App(
                        Box::new(
                            rule.rhs_template
                                .instantiate_level_params(&rule.level_params, r_lvls),
                        ),
                        payload.clone(),
                    ));
                }
            }
        }
    }
    None
}

pub fn apply_iota_rules(rules: &[ConLecheRecRule], e: &ConLecheExpr) -> Option<ConLecheExpr> {
    for r in rules {
        if let Some(red) = eval_iota_step(r, e) {
            return Some(red);
        }
    }
    None
}

pub fn con_leche_whnf(fuel: usize, env: &ConLecheEnv, e: &ConLecheExpr) -> ConLecheExpr {
    if fuel == 0 {
        return e.clone();
    }
    let f = fuel - 1;
    match e {
        ConLecheExpr::Const(name, lvls) => {
            if let Some(d) = env.lookup(name) {
                if d.wf_tag && d.level_params.len() == lvls.len() {
                    con_leche_whnf(f, env, &d.val.instantiate_level_params(&d.level_params, lvls))
                } else {
                    e.clone()
                }
            } else {
                e.clone()
            }
        }
        ConLecheExpr::App(fn_expr, arg_expr) => {
            if let Some(red) = apply_iota_rules(&env.rec_rules, e) {
                return con_leche_whnf(f, env, &red);
            }
            let fn_w = con_leche_whnf(f, env, fn_expr);
            match &fn_w {
                ConLecheExpr::Lam(_dom, body) => {
                    con_leche_whnf(f, env, &ConLecheExpr::inst0(arg_expr, body))
                }
                ConLecheExpr::Const(r_name, _)
                    if env.rec_rules.iter().any(|r| &r.rec_name == r_name) =>
                {
                    let arg_w = con_leche_whnf(f, env, arg_expr);
                    let cand = ConLecheExpr::App(Box::new(fn_w.clone()), Box::new(arg_w));
                    if let Some(red) = apply_iota_rules(&env.rec_rules, &cand) {
                        con_leche_whnf(f, env, &red)
                    } else {
                        ConLecheExpr::App(Box::new(fn_w), arg_expr.clone())
                    }
                }
                _ => ConLecheExpr::App(Box::new(fn_w), arg_expr.clone()),
            }
        }
        ConLecheExpr::LetE(_ty, val, body) => {
            con_leche_whnf(f, env, &ConLecheExpr::inst0(val, body))
        }
        _ => e.clone(),
    }
}

pub fn con_leche_is_def_eq(
    fuel: usize,
    env: &ConLecheEnv,
    e1: &ConLecheExpr,
    e2: &ConLecheExpr,
) -> bool {
    if e1 == e2 {
        return true;
    }
    if fuel == 0 {
        return false;
    }
    let f = fuel - 1;
    let w1 = con_leche_whnf(f, env, e1);
    let w2 = con_leche_whnf(f, env, e2);
    if w1 == w2 || &w1 == e2 || e1 == &w2 {
        return true;
    }
    match (&w1, &w2) {
        (ConLecheExpr::Sort(u1), ConLecheExpr::Sort(u2)) => ConLecheLevel::level_def_eq(u1, u2),
        (ConLecheExpr::App(f1, a1), ConLecheExpr::App(f2, a2)) => {
            con_leche_is_def_eq(f, env, f1, f2) && con_leche_is_def_eq(f, env, a1, a2)
        }
        (ConLecheExpr::Lam(d1, b1), ConLecheExpr::Lam(d2, b2))
        | (ConLecheExpr::ForallE(d1, b1), ConLecheExpr::ForallE(d2, b2)) => {
            con_leche_is_def_eq(f, env, d1, d2) && con_leche_is_def_eq(f, env, b1, b2)
        }
        (ConLecheExpr::LetE(t1, v1, b1), ConLecheExpr::LetE(t2, v2, b2)) => {
            con_leche_is_def_eq(f, env, t1, t2)
                && con_leche_is_def_eq(f, env, v1, v2)
                && con_leche_is_def_eq(f, env, b1, b2)
        }
        _ => false,
    }
}

pub fn con_leche_infer_type(
    fuel: usize,
    env: &ConLecheEnv,
    ctx: &[ConLecheExpr],
    e: &ConLecheExpr,
) -> Option<ConLecheExpr> {
    if fuel == 0 {
        return None;
    }
    let f = fuel - 1;
    match e {
        ConLecheExpr::BVar(idx) => ctx.get(*idx).map(|ty| ty.lift(*idx + 1, 0)),
        ConLecheExpr::Sort(u) => Some(ConLecheExpr::Sort(ConLecheLevel::Succ(Box::new(u.clone())))),
        ConLecheExpr::Const(name, lvls) => {
            let d = env.lookup(name)?;
            if d.wf_tag && d.level_params.len() == lvls.len() {
                Some(d.ty.instantiate_level_params(&d.level_params, lvls))
            } else {
                None
            }
        }
        ConLecheExpr::App(fn_e, arg_e) => {
            let fn_ty = con_leche_infer_type(f, env, ctx, fn_e)?;
            let arg_ty = con_leche_infer_type(f, env, ctx, arg_e)?;
            if let ConLecheExpr::ForallE(dom, body) = fn_ty {
                if &arg_ty == dom.as_ref() {
                    Some(ConLecheExpr::inst0(arg_e, &body))
                } else {
                    None
                }
            } else {
                None
            }
        }
        ConLecheExpr::Lam(dom, body) => {
            let ConLecheExpr::Sort(_) = con_leche_infer_type(f, env, ctx, dom)? else {
                return None;
            };
            let mut next_ctx = Vec::with_capacity(ctx.len() + 1);
            next_ctx.push((**dom).clone());
            next_ctx.extend_from_slice(ctx);
            let body_ty = con_leche_infer_type(f, env, &next_ctx, body)?;
            Some(ConLecheExpr::ForallE(dom.clone(), Box::new(body_ty)))
        }
        ConLecheExpr::ForallE(dom, body) => {
            let ConLecheExpr::Sort(u1) = con_leche_infer_type(f, env, ctx, dom)? else {
                return None;
            };
            let mut next_ctx = Vec::with_capacity(ctx.len() + 1);
            next_ctx.push((**dom).clone());
            next_ctx.extend_from_slice(ctx);
            let ConLecheExpr::Sort(u2) = con_leche_infer_type(f, env, &next_ctx, body)? else {
                return None;
            };
            Some(ConLecheExpr::Sort(ConLecheLevel::IMax(
                Box::new(u1),
                Box::new(u2),
            )))
        }
        ConLecheExpr::LetE(ty, val, body) => {
            let ConLecheExpr::Sort(_) = con_leche_infer_type(f, env, ctx, ty)? else {
                return None;
            };
            let val_ty = con_leche_infer_type(f, env, ctx, val)?;
            let mut next_ctx = Vec::with_capacity(ctx.len() + 1);
            next_ctx.push((**ty).clone());
            next_ctx.extend_from_slice(ctx);
            let body_ty = con_leche_infer_type(f, env, &next_ctx, body)?;
            if &val_ty == ty.as_ref() {
                Some(ConLecheExpr::inst0(val, &body_ty))
            } else {
                None
            }
        }
    }
}

pub fn con_leche_verify_decl(env: &ConLecheEnv, d: &ConLecheDecl) -> bool {
    if !d.wf_tag {
        return false;
    }
    let Some(ConLecheExpr::Sort(_)) = con_leche_infer_type(64, env, &[], &d.ty) else {
        return false;
    };
    let Some(val_ty) = con_leche_infer_type(64, env, &[], &d.val) else {
        return false;
    };
    con_leche_is_def_eq(64, env, &val_ty, &d.ty)
}

pub fn con_leche_verify_decls_prefix(prefix: &[ConLecheDecl], decls: &[ConLecheDecl]) -> bool {
    let Some((d, rest)) = decls.split_first() else {
        return true;
    };
    if prefix.iter().any(|p| p.name == d.name) {
        return false;
    }
    let prefix_env = ConLecheEnv {
        decls: prefix.to_vec(),
        rec_rules: Vec::new(),
        header_magic: 0x4F4C454E,
    };
    if !con_leche_verify_decl(&prefix_env, d) {
        return false;
    }
    let mut next_prefix = prefix.to_vec();
    next_prefix.push(d.clone());
    con_leche_verify_decls_prefix(&next_prefix, rest)
}

pub fn con_leche_verify_rec_rule_inst(
    env: &ConLecheEnv,
    ctx: &[ConLecheExpr],
    rule: &ConLecheRecRule,
    lvls: &[ConLecheLevel],
) -> bool {
    if rule.level_params.len() != lvls.len() {
        return false;
    }
    let rhs_inst = rule.rhs_template.instantiate_level_params(&rule.level_params, lvls);
    let Some(ctor_ty) = con_leche_infer_type(
        64,
        env,
        ctx,
        &ConLecheExpr::Const(rule.ctor_name.clone(), lvls.to_vec()),
    ) else {
        return false;
    };
    let Some(rec_ty) = con_leche_infer_type(
        64,
        env,
        ctx,
        &ConLecheExpr::Const(rule.rec_name.clone(), lvls.to_vec()),
    ) else {
        return false;
    };
    let Some(rhs_ty) = con_leche_infer_type(64, env, ctx, &rhs_inst) else {
        return false;
    };
    ctor_ty == rule.ctor_expected_inst(lvls)
        && rec_ty == rule.rec_expected_inst(lvls)
        && rhs_ty == rule.rhs_expected_inst(lvls)
}

pub fn con_leche_verify_rec_rule(env: &ConLecheEnv, rule: &ConLecheRecRule) -> bool {
    let lvls: Vec<ConLecheLevel> = rule
        .level_params
        .iter()
        .cloned()
        .map(ConLecheLevel::Param)
        .collect();
    con_leche_verify_rec_rule_inst(env, &[], rule, &lvls)
}

pub fn encode_con_leche_nat(mut n: usize, out: &mut Vec<u8>) {
    while n > 0 {
        out.push(1);
        n -= 1;
    }
    out.push(0);
}

pub fn decode_con_leche_nat(bytes: &[u8], off: &mut usize) -> Option<usize> {
    let mut acc = 0usize;
    loop {
        let b = *bytes.get(*off)?;
        *off += 1;
        if b == 0 {
            return Some(acc);
        } else if b == 1 {
            acc += 1;
        } else {
            return None;
        }
    }
}

pub fn encode_con_leche_string(s: &str, out: &mut Vec<u8>) {
    let bs = s.as_bytes();
    encode_con_leche_nat(bs.len(), out);
    out.extend_from_slice(bs);
}

pub fn decode_con_leche_string(bytes: &[u8], off: &mut usize) -> Option<String> {
    let len = decode_con_leche_nat(bytes, off)?;
    if *off + len > bytes.len() {
        return None;
    }
    let s = std::str::from_utf8(&bytes[*off..*off + len]).ok()?.to_string();
    *off += len;
    Some(s)
}

pub fn encode_con_leche_string_list(ss: &[String], out: &mut Vec<u8>) {
    encode_con_leche_nat(ss.len(), out);
    for s in ss {
        encode_con_leche_string(s, out);
    }
}

pub fn decode_con_leche_string_list(bytes: &[u8], off: &mut usize) -> Option<Vec<String>> {
    let count = decode_con_leche_nat(bytes, off)?;
    let mut res = Vec::with_capacity(count);
    for _ in 0..count {
        res.push(decode_con_leche_string(bytes, off)?);
    }
    Some(res)
}

fn encode_olean_level_aux(u: &ConLecheLevel, out: &mut Vec<u8>) {
    match u {
        ConLecheLevel::Zero => out.push(0),
        ConLecheLevel::Succ(u1) => {
            out.push(1);
            encode_olean_level_aux(u1, out);
        }
        ConLecheLevel::Max(u1, u2) => {
            out.push(2);
            encode_olean_level_aux(u1, out);
            encode_olean_level_aux(u2, out);
        }
        ConLecheLevel::IMax(u1, u2) => {
            out.push(3);
            encode_olean_level_aux(u1, out);
            encode_olean_level_aux(u2, out);
        }
        ConLecheLevel::Param(p) => {
            out.push(4);
            encode_con_leche_string(p, out);
        }
    }
}

fn decode_olean_level_aux(fuel: usize, bytes: &[u8], off: &mut usize) -> Option<ConLecheLevel> {
    if fuel == 0 {
        return None;
    }
    let f = fuel - 1;
    let tag = *bytes.get(*off)?;
    *off += 1;
    match tag {
        0 => Some(ConLecheLevel::Zero),
        1 => Some(ConLecheLevel::Succ(Box::new(decode_olean_level_aux(f, bytes, off)?))),
        2 => {
            let u1 = decode_olean_level_aux(f, bytes, off)?;
            let u2 = decode_olean_level_aux(f, bytes, off)?;
            Some(ConLecheLevel::Max(Box::new(u1), Box::new(u2)))
        }
        3 => {
            let u1 = decode_olean_level_aux(f, bytes, off)?;
            let u2 = decode_olean_level_aux(f, bytes, off)?;
            Some(ConLecheLevel::IMax(Box::new(u1), Box::new(u2)))
        }
        4 => Some(ConLecheLevel::Param(decode_con_leche_string(bytes, off)?)),
        _ => None,
    }
}

pub fn encode_olean_level(u: &ConLecheLevel, out: &mut Vec<u8>) {
    encode_con_leche_nat(u.ast_size(), out);
    encode_olean_level_aux(u, out);
}

pub fn decode_olean_level_stream(bytes: &[u8], off: &mut usize) -> Option<ConLecheLevel> {
    let fuel = decode_con_leche_nat(bytes, off)?;
    decode_olean_level_aux(fuel, bytes, off)
}

pub fn encode_olean_levels(us: &[ConLecheLevel], out: &mut Vec<u8>) {
    encode_con_leche_nat(us.len(), out);
    for u in us {
        encode_olean_level(u, out);
    }
}

pub fn decode_olean_levels_stream(bytes: &[u8], off: &mut usize) -> Option<Vec<ConLecheLevel>> {
    let n = decode_con_leche_nat(bytes, off)?;
    let mut res = Vec::with_capacity(n);
    for _ in 0..n {
        res.push(decode_olean_level_stream(bytes, off)?);
    }
    Some(res)
}

fn encode_olean_expr_aux(e: &ConLecheExpr, out: &mut Vec<u8>) {
    match e {
        ConLecheExpr::BVar(idx) => {
            out.push(0);
            encode_con_leche_nat(*idx, out);
        }
        ConLecheExpr::Sort(u) => {
            out.push(1);
            encode_olean_level(u, out);
        }
        ConLecheExpr::Const(name, lvls) => {
            out.push(2);
            encode_con_leche_string(name, out);
            encode_olean_levels(lvls, out);
        }
        ConLecheExpr::App(fn_e, a_e) => {
            out.push(3);
            encode_olean_expr_aux(fn_e, out);
            encode_olean_expr_aux(a_e, out);
        }
        ConLecheExpr::Lam(dom, body) => {
            out.push(4);
            encode_olean_expr_aux(dom, out);
            encode_olean_expr_aux(body, out);
        }
        ConLecheExpr::ForallE(dom, body) => {
            out.push(5);
            encode_olean_expr_aux(dom, out);
            encode_olean_expr_aux(body, out);
        }
        ConLecheExpr::LetE(ty, val, body) => {
            out.push(6);
            encode_olean_expr_aux(ty, out);
            encode_olean_expr_aux(val, out);
            encode_olean_expr_aux(body, out);
        }
    }
}

fn decode_olean_expr_aux(fuel: usize, bytes: &[u8], off: &mut usize) -> Option<ConLecheExpr> {
    if fuel == 0 {
        return None;
    }
    let f = fuel - 1;
    let tag = *bytes.get(*off)?;
    *off += 1;
    match tag {
        0 => Some(ConLecheExpr::BVar(decode_con_leche_nat(bytes, off)?)),
        1 => Some(ConLecheExpr::Sort(decode_olean_level_stream(bytes, off)?)),
        2 => {
            let name = decode_con_leche_string(bytes, off)?;
            let lvls = decode_olean_levels_stream(bytes, off)?;
            Some(ConLecheExpr::Const(name, lvls))
        }
        3 => {
            let fn_e = decode_olean_expr_aux(f, bytes, off)?;
            let a_e = decode_olean_expr_aux(f, bytes, off)?;
            Some(ConLecheExpr::App(Box::new(fn_e), Box::new(a_e)))
        }
        4 => {
            let dom = decode_olean_expr_aux(f, bytes, off)?;
            let body = decode_olean_expr_aux(f, bytes, off)?;
            Some(ConLecheExpr::Lam(Box::new(dom), Box::new(body)))
        }
        5 => {
            let dom = decode_olean_expr_aux(f, bytes, off)?;
            let body = decode_olean_expr_aux(f, bytes, off)?;
            Some(ConLecheExpr::ForallE(Box::new(dom), Box::new(body)))
        }
        6 => {
            let ty = decode_olean_expr_aux(f, bytes, off)?;
            let val = decode_olean_expr_aux(f, bytes, off)?;
            let body = decode_olean_expr_aux(f, bytes, off)?;
            Some(ConLecheExpr::LetE(Box::new(ty), Box::new(val), Box::new(body)))
        }
        _ => None,
    }
}

pub fn encode_olean_expr(e: &ConLecheExpr, out: &mut Vec<u8>) {
    encode_con_leche_nat(e.ast_size(), out);
    encode_olean_expr_aux(e, out);
}

pub fn decode_olean_expr_stream(bytes: &[u8], off: &mut usize) -> Option<ConLecheExpr> {
    let fuel = decode_con_leche_nat(bytes, off)?;
    decode_olean_expr_aux(fuel, bytes, off)
}

pub fn encode_olean_decl(d: &ConLecheDecl, out: &mut Vec<u8>) {
    encode_con_leche_string(&d.name, out);
    encode_con_leche_string_list(&d.level_params, out);
    out.push(if d.wf_tag { 1 } else { 0 });
    encode_olean_expr(&d.ty, out);
    encode_olean_expr(&d.val, out);
}

pub fn decode_olean_decl_stream(bytes: &[u8], off: &mut usize) -> Option<ConLecheDecl> {
    let name = decode_con_leche_string(bytes, off)?;
    let level_params = decode_con_leche_string_list(bytes, off)?;
    let wf_byte = *bytes.get(*off)?;
    *off += 1;
    if wf_byte != 0 && wf_byte != 1 {
        return None;
    }
    let ty = decode_olean_expr_stream(bytes, off)?;
    let val = decode_olean_expr_stream(bytes, off)?;
    Some(ConLecheDecl {
        name,
        level_params,
        ty,
        val,
        wf_tag: wf_byte == 1,
    })
}

pub fn encode_olean_rec_rule(r: &ConLecheRecRule, out: &mut Vec<u8>) {
    encode_con_leche_string(&r.rec_name, out);
    encode_con_leche_string(&r.ctor_name, out);
    encode_con_leche_string_list(&r.level_params, out);
    out.push(if r.is_dependent { 1 } else { 0 });
    encode_olean_expr(&r.rhs_template, out);
    encode_olean_expr(&r.arg_dom, out);
    encode_olean_expr(&r.ind_ty, out);
    encode_olean_expr(&r.result_cod, out);
}

pub fn decode_olean_rec_rule_stream(bytes: &[u8], off: &mut usize) -> Option<ConLecheRecRule> {
    let rec_name = decode_con_leche_string(bytes, off)?;
    let ctor_name = decode_con_leche_string(bytes, off)?;
    let level_params = decode_con_leche_string_list(bytes, off)?;
    let dep_byte = *bytes.get(*off)?;
    *off += 1;
    if dep_byte != 0 && dep_byte != 1 {
        return None;
    }
    let rhs_template = decode_olean_expr_stream(bytes, off)?;
    let arg_dom = decode_olean_expr_stream(bytes, off)?;
    let ind_ty = decode_olean_expr_stream(bytes, off)?;
    let result_cod = decode_olean_expr_stream(bytes, off)?;
    Some(ConLecheRecRule {
        rec_name,
        ctor_name,
        level_params,
        rhs_template,
        arg_dom,
        ind_ty,
        result_cod,
        is_dependent: dep_byte == 1,
    })
}

/// Losslessly encode a `ConLecheEnv` into the exact binary `.olean` shard format (`OLEN` v1)
/// matching `ConLeche.encodeOleanShard` in `lean/TurboLean/ConLeche.lean`.
pub fn encode_olean_shard(env: &ConLecheEnv) -> Vec<u8> {
    let mut out = vec![0x4F, 0x4C, 0x45, 0x4E];
    encode_con_leche_nat(env.decls.len(), &mut out);
    for d in &env.decls {
        encode_olean_decl(d, &mut out);
    }
    encode_con_leche_nat(env.rec_rules.len(), &mut out);
    for r in &env.rec_rules {
        encode_olean_rec_rule(r, &mut out);
    }
    out
}

/// Parse and kernel-verify a binary `.olean` shard (`OLEN` v1), matching `ConLeche.parseOleanShard`
/// in `lean/TurboLean/ConLeche.lean`.
pub fn parse_olean_shard(bytes: &[u8]) -> Result<(ConLecheEnv, usize), String> {
    if bytes.len() < 5 {
        return Err("olean shard truncated (< 5 bytes)".to_string());
    }
    if &bytes[0..4] != b"OLEN" {
        return Err("invalid olean shard magic (expected OLEN)".to_string());
    }
    let mut off = 4usize;
    let Some(decl_count) = decode_con_leche_nat(bytes, &mut off) else {
        return Err("malformed olean declaration count".to_string());
    };
    if decl_count == 0 {
        return Err("olean shard must contain at least 1 declaration".to_string());
    }
    let mut decls = Vec::with_capacity(decl_count);
    for _ in 0..decl_count {
        let Some(d) = decode_olean_decl_stream(bytes, &mut off) else {
            return Err("malformed olean declaration stream".to_string());
        };
        decls.push(d);
    }
    let Some(rule_count) = decode_con_leche_nat(bytes, &mut off) else {
        return Err("malformed olean recursor rule count".to_string());
    };
    let mut rec_rules = Vec::with_capacity(rule_count);
    for _ in 0..rule_count {
        let Some(r) = decode_olean_rec_rule_stream(bytes, &mut off) else {
            return Err("malformed olean recursor rule stream".to_string());
        };
        rec_rules.push(r);
    }
    if off != bytes.len() {
        return Err("trailing bytes in olean shard".to_string());
    }
    if !con_leche_verify_decls_prefix(&[], &decls) {
        return Err("olean shard failed acyclic prefix or duplicate-name verification".to_string());
    }
    let env = ConLecheEnv {
        decls,
        rec_rules,
        header_magic: 0x4F4C454E,
    };
    if !env.decls.iter().all(|d| con_leche_verify_decl(&env, d)) {
        return Err("olean shard declaration failed CIC kernel typecheck".to_string());
    }
    if !env.rec_rules.iter().all(|r| con_leche_verify_rec_rule(&env, r)) {
        return Err("olean shard recursor rule failed CIC kernel typecheck".to_string());
    }
    Ok((env, off))
}

/// Validate a binary `.olean` shard (`"OLEN"` magic + self-delimiting `encodeNat` stream) through
/// both `parse_olean_shard` (in-kernel CIC typechecking) and the `PolicyGates` C-ABI gate.
#[inline(always)]
pub fn validate_olean_shard_header_bytes(
    bytes: &[u8],
    off_end: usize,
    all_decls_typed: bool,
) -> bool {
    if bytes.len() < 5 {
        return verify_con_leche_shard(0, 0, off_end as u64, bytes.len() as u64, false);
    }
    let magic = u32::from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    match parse_olean_shard(bytes) {
        Ok((env, parsed_end)) => verify_con_leche_shard(
            magic,
            env.decls.len() as u64,
            parsed_end.min(off_end) as u64,
            bytes.len() as u64,
            all_decls_typed,
        ),
        Err(_) => verify_con_leche_shard(magic, 0, off_end as u64, bytes.len() as u64, false),
    }
}

/// Check that no constant in `e` is shadowed by `bound_names` or missing from `global_consts`,
/// matching `ElabAudit.checkNoShadowedConsts` (`lean/TurboLean/ElabAudit.lean`).
pub fn check_no_shadowed_consts(
    global_consts: &[String],
    bound_names: &[String],
    e: &ConLecheExpr,
) -> bool {
    match e {
        ConLecheExpr::BVar(_) | ConLecheExpr::Sort(_) => true,
        ConLecheExpr::Const(c, _) => {
            !bound_names.iter().any(|b| b == c) && global_consts.iter().any(|g| g == c)
        }
        ConLecheExpr::App(f, a) | ConLecheExpr::Lam(f, a) | ConLecheExpr::ForallE(f, a) => {
            check_no_shadowed_consts(global_consts, bound_names, f)
                && check_no_shadowed_consts(global_consts, bound_names, a)
        }
        ConLecheExpr::LetE(t, v, b) => {
            check_no_shadowed_consts(global_consts, bound_names, t)
                && check_no_shadowed_consts(global_consts, bound_names, v)
                && check_no_shadowed_consts(global_consts, bound_names, b)
        }
    }
}

/// Serialize a `ConLecheExpr` proof term into an `LNIR_EXPR_V1` (`"LNE1"`) CAS blob,
/// matching `ElabAudit.serializeExprV1` (`lean/TurboLean/ElabAudit.lean`).
pub fn serialize_expr_v1(e: &ConLecheExpr) -> Vec<u8> {
    let mut out = vec![0x4C, 0x4E, 0x45, 0x31];
    encode_olean_expr(e, &mut out);
    out
}

/// Parse an `LNIR_EXPR_V1` (`"LNE1"`) CAS blob into `(ConLecheExpr, off_end)`,
/// matching `ElabAudit.parseExprV1` (`lean/TurboLean/ElabAudit.lean`).
pub fn parse_expr_v1(blob: &[u8]) -> Option<(ConLecheExpr, usize)> {
    if blob.len() < 5 || &blob[0..4] != b"LNE1" {
        return None;
    }
    let mut off = 4usize;
    let prf = decode_olean_expr_stream(blob, &mut off)?;
    if off == blob.len() {
        Some((prf, off))
    } else {
        None
    }
}

/// Replay a cached `LNIR_EXPR_V1` (`"LNE1"`) CAS proof blob against `expected_ty` inside `ConLecheEnv`,
/// matching `ElabAudit.replayCASProofBlob` (`lean/TurboLean/ElabAudit.lean`).
pub fn replay_cas_proof_blob(
    env: &ConLecheEnv,
    blob: &[u8],
    expected_ty: &ConLecheExpr,
) -> Option<(ConLecheExpr, usize)> {
    let (prf, off_end) = parse_expr_v1(blob)?;
    let ConLecheExpr::Sort(_) = con_leche_infer_type(64, env, &[], expected_ty)? else {
        return None;
    };
    let prf_ty = con_leche_infer_type(64, env, &[], &prf)?;
    if con_leche_is_def_eq(64, env, &prf_ty, expected_ty) {
        Some((prf, off_end))
    } else {
        None
    }
}

#[inline(always)]
pub fn verify_elab_header_pin(
    decl_name_non_empty: bool,
    no_shadowed_consts: bool,
    ast_matches_pin: bool,
    cas_blob_magic_ok: bool,
    cas_off_end_matches: bool,
) -> bool {
    unsafe {
        turbo_spec_verify_elab_header_pin(
            if decl_name_non_empty { 1 } else { 0 },
            if no_shadowed_consts { 1 } else { 0 },
            if ast_matches_pin { 1 } else { 0 },
            if cas_blob_magic_ok { 1 } else { 0 },
            if cas_off_end_matches { 1 } else { 0 },
        ) == 1
    }
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
pub fn verify_par_chunk(chunk_start: u64, chunk_end: u64, total_len: u64, min_grain: u64) -> bool {
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
        turbo_spec_verify_tlz1_token(is_match as u8, offset, token_len, out_len, uncompressed_cap)
            != 0
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
    unsafe { turbo_spec_verify_farkas_step(obj_coeff, col_sum, acc_cost, weight_cost, bound) != 0 }
}

#[inline(always)]
pub fn verify_ident_bloom(is_excluded_core: bool, cand_mask: u64, context_mask: u64) -> bool {
    unsafe { turbo_spec_verify_ident_bloom(is_excluded_core as u8, cand_mask, context_mask) != 0 }
}

#[inline(always)]
pub fn verify_pack_trust_admission(
    requested_untrusted: bool,
    has_trusted_pubkey: bool,
    has_attestation_fields: bool,
    sig_valid: bool,
    allow_unattested_trusted: bool,
) -> bool {
    unsafe {
        turbo_spec_verify_pack_trust_admission(
            requested_untrusted as u8,
            has_trusted_pubkey as u8,
            has_attestation_fields as u8,
            sig_valid as u8,
            allow_unattested_trusted as u8,
        ) != 0
    }
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
    verify_worker_budget_topology(
        active_workers,
        max_workers,
        micro_chunks,
        total_len,
        is_mobile_hetero as u8,
    )
}

#[inline(always)]
pub fn verify_worker_budget_topology(
    active_workers: u64,
    max_workers: u64,
    micro_chunks: u64,
    total_len: u64,
    topology_kind: u8,
) -> bool {
    unsafe {
        leansys_verify_worker_budget(
            active_workers,
            max_workers,
            micro_chunks,
            total_len,
            topology_kind,
        ) == 1
    }
}

#[inline(always)]
pub fn verify_page_aligned_buffer(
    addr: u64,
    alloc_bytes: u64,
    capacity_bytes: u64,
    dirty_rss_bytes: u64,
    max_budget_bytes: u64,
    page_align_mask: u64,
) -> bool {
    unsafe {
        leansys_verify_page_aligned_buffer(
            addr,
            alloc_bytes,
            capacity_bytes,
            dirty_rss_bytes,
            max_budget_bytes,
            page_align_mask,
        ) == 1
    }
}

#[inline(always)]
pub fn select_isa(
    detected_hw_caps: u64,
    required_mask: u64,
    requested_variant_id: u8,
    max_variant_id: u8,
) -> u8 {
    unsafe {
        leansys_select_isa(
            detected_hw_caps,
            required_mask,
            requested_variant_id,
            max_variant_id,
        )
    }
}

#[inline(always)]
pub fn verify_isa_selection(
    detected_hw_caps: u64,
    required_mask: u64,
    selected_variant_id: u8,
    max_variant_id: u8,
) -> bool {
    unsafe {
        leansys_verify_isa_selection(
            detected_hw_caps,
            required_mask,
            selected_variant_id,
            max_variant_id,
        ) == 1
    }
}

#[inline(always)]
pub fn verify_rc_mode_safe(rc_mode: u8, has_heap_allocs: bool, is_multi_threaded: bool) -> bool {
    unsafe {
        leannative_verify_rc_mode_safe(rc_mode, has_heap_allocs as u8, is_multi_threaded as u8) == 1
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

#[allow(clippy::too_many_arguments)]
#[inline(always)]
pub fn verify_audit_materialize_gate(
    skeleton_clean: bool,
    stubbed_placeholder_count: u64,
    certified_shard_count: u64,
    distinct_covered_shard_count: u64,
    total_shard_count: u64,
    expected_interface_digest: u64,
    actual_interface_digest: u64,
    expected_olean_digest: u64,
    actual_olean_digest: u64,
    expected_ilean_digest: u64,
    actual_ilean_digest: u64,
    needs_c: bool,
    expected_c_digest: u64,
    actual_c_digest: u64,
    dep_trace_digest: u64,
    audited_artifact_digest: u64,
    kernel_audit_clean: bool,
) -> bool {
    unsafe {
        turbo_spec_verify_audit_materialize_gate(
            skeleton_clean as u8,
            stubbed_placeholder_count,
            certified_shard_count,
            distinct_covered_shard_count,
            total_shard_count,
            expected_interface_digest,
            actual_interface_digest,
            expected_olean_digest,
            actual_olean_digest,
            expected_ilean_digest,
            actual_ilean_digest,
            needs_c as u8,
            expected_c_digest,
            actual_c_digest,
            dep_trace_digest,
            audited_artifact_digest,
            kernel_audit_clean as u8,
        ) != 0
    }
}

/// Evaluate one fused 2-layer Radix-4 $\mathbb{F}_{2^{128}}$ butterfly quad via the compiled
/// `LeanNative.Spec` C-ABI export `lean_native_ntt_butterfly_fused_2layer_slice`.
#[inline]
pub fn ntt_butterfly_fused_2layer_lane(
    a: (u64, u64),
    b: (u64, u64),
    c: (u64, u64),
    d: (u64, u64),
    to: (u64, u64),
    tia: (u64, u64),
    tib: (u64, u64),
) -> [(u64, u64); 4] {
    let word = |w: u64| unsafe {
        lean_native_ntt_butterfly_fused_2layer_slice(
            a.0, a.1, b.0, b.1, c.0, c.1, d.0, d.1, to.0, to.1, tia.0, tia.1, tib.0, tib.1, w,
        )
    };
    [
        (word(0), word(1)),
        (word(2), word(3)),
        (word(4), word(5)),
        (word(6), word(7)),
    ]
}

/// In-place slice driver over 128-bit $\mathbb{F}_{2^{128}}$ lanes (`[u64; 2]` per lane) delegating
/// each lane exclusively to the verified `lean_native_ntt_butterfly_fused_2layer_slice` C-ABI symbol.
pub fn ntt_butterfly_fused_2layer_slice_in_place(
    a: &mut [(u64, u64)],
    b: &mut [(u64, u64)],
    c: &mut [(u64, u64)],
    d: &mut [(u64, u64)],
    to: (u64, u64),
    tia: (u64, u64),
    tib: (u64, u64),
) {
    let n = a.len().min(b.len()).min(c.len()).min(d.len());
    for i in 0..n {
        let [fa, fb, fc, fd] =
            ntt_butterfly_fused_2layer_lane(a[i], b[i], c[i], d[i], to, tia, tib);
        a[i] = fa;
        b[i] = fb;
        c[i] = fc;
        d[i] = fd;
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
        (Some(l), Some(r)) => !l.trim().is_empty() && !r.trim().is_empty() && l.trim() != r.trim(),
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
        assert!(verify_ios_jetsam_budget(
            33_554_432,
            33_554_432,
            268_435_456,
            16383,
            false
        ));
        assert!(!verify_ios_jetsam_budget(
            200_000_000,
            100_000_000,
            268_435_456,
            16383,
            false
        ));
        assert!(!verify_ios_jetsam_budget(
            8_388_608,
            8_388_608,
            268_435_456,
            16383,
            true
        ));
        assert!(verify_ios_jetsam_budget(
            8_388_608, 8_388_608, 25_165_824, 16383, true
        ));
        assert!(verify_rc_mode_safe(0, false, true));
        assert!(!verify_rc_mode_safe(0, true, false));
        assert!(!verify_rc_mode_safe(1, true, true));
        assert!(verify_rc_mode_safe(2, true, true));
        assert!(verify_worker_budget(4, 6, 24, 1024, true));
        assert!(!verify_worker_budget(4, 8, 24, 1024, true));
        assert!(!verify_worker_budget(0, 6, 24, 1024, true));
        assert!(verify_worker_budget_topology(6, 9, 54, 4096, 2));
        assert!(!verify_worker_budget_topology(6, 10, 54, 4096, 2));
        assert!(verify_page_aligned_buffer(
            0x10000,
            4096,
            16384,
            1_048_576,
            134_217_728,
            16383
        ));
        assert!(verify_page_aligned_buffer(
            0x11000,
            4096,
            4096,
            1_048_576,
            134_217_728,
            4095
        ));
        assert!(!verify_page_aligned_buffer(
            0x11000,
            4096,
            16384,
            1_048_576,
            134_217_728,
            16383
        ));
        assert!(!verify_page_aligned_buffer(
            0x10000,
            4096,
            16384,
            1_048_576,
            134_217_728,
            8191
        ));
        assert_eq!(select_isa(0x37F, 0x37F, 3, 3), 3);
        assert_eq!(select_isa(0x307, 0x37F, 3, 3), 0);
        assert_eq!(select_isa(0x37F, 0, 3, 3), 0);
        assert!(verify_isa_selection(0x37F, 0x37F, 3, 3));
        assert!(!verify_isa_selection(0x307, 0x37F, 3, 3));
        assert!(!verify_isa_selection(0x37F, 0, 3, 3));
        assert!(verify_backend_choice(262_144, false, true, true, 1));
        assert!(!verify_backend_choice(65_536, false, true, true, 1));
        assert!(verify_backend_choice(65_536, false, true, true, 0));
        assert!(!verify_backend_choice(262_144, false, true, false, 1));
        assert!(verify_con_leche_shard(0x4F4C454E, 4, 128, 128, true));
        assert!(!verify_con_leche_shard(0x4F4C454E, 4, 120, 128, true));
        assert!(!verify_con_leche_shard(0x4F4C454E, 1, 4, 4, true));
        assert!(!verify_con_leche_shard(0xDEAD_BEEF, 4, 128, 128, true));
        let valid_shard = encode_olean_shard(&ConLecheEnv {
            decls: vec![ConLecheDecl {
                name: "id_prop".to_string(),
                level_params: vec![],
                ty: ConLecheExpr::ForallE(
                    Box::new(ConLecheExpr::Sort(ConLecheLevel::Zero)),
                    Box::new(ConLecheExpr::ForallE(
                        Box::new(ConLecheExpr::BVar(0)),
                        Box::new(ConLecheExpr::BVar(1)),
                    )),
                ),
                val: ConLecheExpr::Lam(
                    Box::new(ConLecheExpr::Sort(ConLecheLevel::Zero)),
                    Box::new(ConLecheExpr::Lam(
                        Box::new(ConLecheExpr::BVar(0)),
                        Box::new(ConLecheExpr::BVar(0)),
                    )),
                ),
                wf_tag: true,
            }],
            rec_rules: vec![],
            header_magic: 0x4F4C454E,
        });
        assert!(validate_olean_shard_header_bytes(&valid_shard, valid_shard.len(), true));
        assert!(!validate_olean_shard_header_bytes(&[0x4F, 0x4C, 0x45, 0x4E], 4, true));
        assert!(!validate_olean_shard_header_bytes(&[0x4F, 0x4C, 0x45, 0x4E, 0, 0], 6, true));
        assert!(verify_elab_header_pin(true, true, true, true, true));
        assert!(!verify_elab_header_pin(true, false, true, true, true));
        assert!(!verify_elab_header_pin(false, true, true, true, true));
        assert!(verify_audit_materialize_gate(
            true, 0, 4, 4, 4, 0x11, 0x11, 0x22, 0x22, 0x33, 0x33, true, 0x44, 0x44, 0x55, 0x22,
            true
        ));
        assert!(!verify_audit_materialize_gate(
            true, 1, 4, 4, 4, 0x11, 0x11, 0x22, 0x22, 0x33, 0x33, true, 0x44, 0x44, 0x55, 0x22,
            true
        ));
        assert!(!verify_audit_materialize_gate(
            true, 0, 3, 4, 4, 0x11, 0x11, 0x22, 0x22, 0x33, 0x33, true, 0x44, 0x44, 0x55, 0x22,
            true
        ));
        assert!(!verify_audit_materialize_gate(
            true, 0, 4, 4, 4, 0x11, 0x11, 0x22, 0x99, 0x33, 0x33, true, 0x44, 0x44, 0x55, 0x99,
            true
        ));
        assert!(!verify_audit_materialize_gate(
            true, 0, 4, 4, 4, 0x11, 0x11, 0x22, 0x22, 0x33, 0x33, true, 0x44, 0x44, 0, 0x22, true
        ));
        assert!(!verify_audit_materialize_gate(
            true, 0, 4, 4, 4, 0x11, 0x11, 0x22, 0x22, 0x33, 0x33, true, 0x44, 0x44, 0x55, 0x77,
            true
        ));
        assert!(!verify_audit_materialize_gate(
            true, 0, 4, 4, 4, 0x11, 0x11, 0x22, 0x22, 0x33, 0x33, true, 0x44, 0x44, 0x55, 0x22,
            false
        ));
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

    #[test]
    fn test_ntt_butterfly_fused_2layer_slice_c_abi_matches_sequential_radix2() {
        fn gf128_mul_ref(a: (u64, u64), b: (u64, u64)) -> (u64, u64) {
            let x = (a.0 as u128) | ((a.1 as u128) << 64);
            let y = (b.0 as u128) | ((b.1 as u128) << 64);
            let mut cur = x;
            let mut res: u128 = 0;
            for bit in 0..128 {
                if ((y >> bit) & 1) != 0 {
                    res ^= cur;
                }
                let carry = (cur >> 127) & 1;
                cur <<= 1;
                if carry != 0 {
                    cur ^= 0x87;
                }
            }
            (res as u64, (res >> 64) as u64)
        }
        fn gf128_xor(a: (u64, u64), b: (u64, u64)) -> (u64, u64) {
            (a.0 ^ b.0, a.1 ^ b.1)
        }
        fn radix2_ref(u: (u64, u64), v: (u64, u64), tw: (u64, u64)) -> ((u64, u64), (u64, u64)) {
            let p = gf128_mul_ref(v, tw);
            let u1 = gf128_xor(u, p);
            let v1 = gf128_xor(u1, v);
            (u1, v1)
        }
        fn seq_2layer_ref(
            a: (u64, u64),
            b: (u64, u64),
            c: (u64, u64),
            d: (u64, u64),
            to: (u64, u64),
            tia: (u64, u64),
            tib: (u64, u64),
        ) -> [(u64, u64); 4] {
            let (na, nc) = radix2_ref(a, c, to);
            let (nb, nd) = radix2_ref(b, d, to);
            let (fa, fb) = radix2_ref(na, nb, tia);
            let (fc, fd) = radix2_ref(nc, nd, tib);
            [fa, fb, fc, fd]
        }

        let a = (0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210);
        let b = (0xdead_beef_cafe_babe, 0x1357_9bdf_2468_ace0);
        let c = (0x8000_0000_0000_0001, 0xc000_0000_0000_0087);
        let d = (0xffff_ffff_ffff_ffff, 0x9999_5555_aaaa_3333);

        // 1. Zero twiddles (`to = tia = tib = 0`)
        let zero_tw = ntt_butterfly_fused_2layer_lane(a, b, c, d, (0, 0), (0, 0), (0, 0));
        assert_eq!(zero_tw, seq_2layer_ref(a, b, c, d, (0, 0), (0, 0), (0, 0)));
        assert_eq!(zero_tw[0], a);
        assert_eq!(zero_tw[1], gf128_xor(a, b));

        // 2. Multiplicative identity twiddles (`to = tia = tib = 1`)
        let one_tw = ntt_butterfly_fused_2layer_lane(a, b, c, d, (1, 0), (1, 0), (1, 0));
        assert_eq!(one_tw, seq_2layer_ref(a, b, c, d, (1, 0), (1, 0), (1, 0)));

        // 3. Non-trivial full 128-bit GF(2^128) twiddles exercising high-bit 0x87 reduction
        let to = (0x9e37_79b9_7f4a_7c15, 0xd1b5_4a32_d192_ed03);
        let tia = (0xbf58_476d_1ce4_e5b9, 0x94d0_49bb_1331_11eb);
        let tib = (0x8000_0000_0000_0087, 0x8000_0000_0000_0001);
        let full_tw = ntt_butterfly_fused_2layer_lane(a, b, c, d, to, tia, tib);
        assert_eq!(full_tw, seq_2layer_ref(a, b, c, d, to, tia, tib));

        // 4. Multi-lane in-place slice helper
        let mut sa = [a, d];
        let mut sb = [b, c];
        let mut sc = [c, b];
        let mut sd = [d, a];
        ntt_butterfly_fused_2layer_slice_in_place(&mut sa, &mut sb, &mut sc, &mut sd, to, tia, tib);
        let exp0 = seq_2layer_ref(a, b, c, d, to, tia, tib);
        let exp1 = seq_2layer_ref(d, c, b, a, to, tia, tib);
        assert_eq!([sa[0], sb[0], sc[0], sd[0]], exp0);
        assert_eq!([sa[1], sb[1], sc[1], sd[1]], exp1);
    }

    #[test]
    fn test_verify_pack_trust_admission_c_abi_gate() {
        // Valid signed pack with configured pubkey -> admitted to trusted
        assert!(verify_pack_trust_admission(false, true, true, true, false));
        // Unsigned pack with configured pubkey + allow_unattested_trusted -> rejected from trusted
        assert!(!verify_pack_trust_admission(
            false, true, false, false, true
        ));
        // Signed pack with invalid signature + configured pubkey -> rejected from trusted
        assert!(!verify_pack_trust_admission(false, true, true, false, true));
        // Explicit untrusted domain -> never admitted to trusted even with valid signature
        assert!(!verify_pack_trust_admission(true, true, true, true, true));
        // No configured pubkey + allow_unattested_trusted -> admitted to trusted
        assert!(verify_pack_trust_admission(
            false, false, false, false, true
        ));
        // No configured pubkey + no override -> rejected from trusted
        assert!(!verify_pack_trust_admission(
            false, false, true, true, false
        ));
    }
}
