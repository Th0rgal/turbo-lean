import Lean
import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Spec
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.Proofs.PeepholeProofs
import LeanNative.Proofs.LoopOptProofs
import LeanNative.Proofs.RealLCNFBridgeProofs
import LeanNative.Proofs.BackendProofs
import LeanNative.Proofs.KernelElabProofs
import LeanNative.Proofs.SymbolicTV
import LeanNative.Proofs.SymbolicTVDenote
import LeanNative.Proofs.SymbolicTVSoundness
import LeanNative.Proofs.SymbolicTVCodeSoundness
import LeanNative.Proofs.SymbolicTVRefinesSoundness
import LeanNative.Proofs.SuperoptSoundness
import LeanNative.Proofs.CertChecker
import LeanNative.Proofs.MutantSuite
import LeanNative.Transform.EqSat
import LeanNative.Transform.LoopSchedule
import LeanNative.Transform.OwnershipRC
import LeanNative.Backend.FastCheck
import LeanNative.Proofs.HybridCAbiProofs
import LeanNative.Proofs.KernelFusionProofs
import LeanNative.Proofs.ClosureADTProofs
import LeanNative.Proofs.SliceViewProofs
import LeanNative.Proofs.UnboxedRegionProofs
import LeanNative.Proofs.HeapObjAbiProofs
import LeanNative.Proofs.LLVMLowerProofs
import LeanNative.Proofs.StableHLOLowerProofs
import LeanNative.Proofs.PTXLowerProofs
import LeanNative.Proofs.PTXMutantProofs
import LeanNative.Proofs.PTXDeclProofs
import LeanNative.Proofs.MetalLowerSpec
import LeanNative.Proofs.MetalLowerProofs
import LeanNative.Proofs.MetalMutantProofs
import LeanNative.Proofs.MetalDeclProofs
import LeanNative.Proofs.GPUEmitterMutantProofs
import LeanNative.Backend.LLVMAst
import LeanNative.Backend.PTXAst
import LeanNative.Backend.MetalAst
import LeanNative.Backend.StableHLOAst
import LeanNative.Transform.AsyncStateMachine
import LeanNative.Proofs.AsyncStateMachineProofs
import LeanNative.Proofs.ProofRetentionProofs

namespace LeanNative.Proofs

open Lean

/-- Standard mathematical axioms permitted in Lean 4 kernel proofs. -/
def allowedStandardAxioms : List Name :=
  [``propext, ``Quot.sound, ``Classical.choice]

/-- Explicitly forbidden axioms / soundness bypasses rejected by the in-kernel gate. -/
def forbiddenAxioms : List Name :=
  [ Name.mkSimple ("sor" ++ "ryAx")
  , Name.mkStr2 "Lean" ("ofReduce" ++ "Bool")
  , Name.mkStr2 "Lean" ("ofReduce" ++ "Nat")
  , Name.mkStr2 "Lean" ("trust" ++ "Compiler") ]

/-- Complete list of formal soundness & refinement theorems audited in `LeanNative`. -/
def auditedTheoremNames : List Name :=
  [ ``LeanNative.Semantics.ScalarExprEquiv.refl, ``LeanNative.Semantics.ScalarExprEquiv.symm
  , ``LeanNative.Semantics.ScalarExprEquiv.trans, ``LeanNative.Semantics.ExprRefines.refl
  , ``LeanNative.Semantics.ExprRefines.trans, ``LeanNative.Semantics.ExprRefines.of_scalar_equiv
  , ``LeanNative.Semantics.ExprEquiv.refl, ``LeanNative.Semantics.ExprEquiv.symm
  , ``LeanNative.Semantics.ExprEquiv.trans, ``LeanNative.Semantics.ExprEquiv.toRefines
  , ``LeanNative.Semantics.CodeRefines.refl, ``LeanNative.Semantics.CodeRefines.trans
  , ``LeanNative.Semantics.CodeRefines.letBind_congr, ``LeanNative.Semantics.CodeRefines.rawStore_congr
  , ``LeanNative.Semantics.CodeRefines.incRef_congr, ``LeanNative.Semantics.CodeRefines.decRef_congr
  , ``LeanNative.Semantics.CodeRefines.ite_congr, ``LeanNative.Semantics.CodeRefines.parFor_congr
  , ``LeanNative.Proofs.rewriteBinOpStep_sound, ``LeanNative.Proofs.rewriteSelectStep_sound
  , ``LeanNative.Proofs.rewriteScalarPeepholeStep_sound, ``LeanNative.Proofs.rewriteScalarPeephole_sound
  , ``LeanNative.Proofs.rewriteLNIRExpr_sound, ``LeanNative.Proofs.evalExpr_optimizeExpr_eq
  , ``LeanNative.Proofs.evalCode_rewriteCodePeephole_eq, ``LeanNative.Proofs.rewriteCodePeephole_refines
  , ``LeanNative.Proofs.unboxTupleProj0_sound, ``LeanNative.Proofs.unboxTupleProj1_sound
  , ``LeanNative.Proofs.unboxTupleProj_sound, ``LeanNative.Proofs.eval_unboxTupleSROA_refines
  , ``LeanNative.Proofs.unboxTupleLetChain_refines, ``LeanNative.Proofs.unboxTupleLetChain1_refines
  , ``LeanNative.Proofs.unboxTupleDeadElim_refines, ``LeanNative.Proofs.unboxNestedTupleDeadElim_refines
  , ``LeanNative.Proofs.hoistExclusivity_sound, ``LeanNative.Proofs.eval_hoistExclusivity_refines
  , ``LeanNative.Proofs.hoistExclusivityPreheader_refines, ``LeanNative.Proofs.unboxedLoopStep_sound
  , ``LeanNative.Proofs.unboxedLoopAccumulator_sim, ``LeanNative.Proofs.normSymExpr_constU64
  , ``LeanNative.Proofs.normSymExpr_constBool, ``LeanNative.Proofs.normSymExpr_const_sound
  , ``LeanNative.Proofs.checkSingleSample_of_codeRefines, ``LeanNative.Proofs.checkConcreteSamples_of_codeRefines
  , ``LeanNative.Proofs.sound_of_checkSingleSample_eq_true, ``LeanNative.Proofs.symbolicTV_refl_sound
  , ``LeanNative.IR.UInt256.bitAnd_self, ``LeanNative.IR.UInt256.bitOr_self
  , ``LeanNative.IR.UInt256.bitXor_zero, ``LeanNative.IR.UInt256.zero_bitXor
  , ``LeanNative.IR.UInt256.bitOr_zero, ``LeanNative.IR.UInt256.zero_bitOr
  , ``LeanNative.Semantics.StorageMapBuffer.lookupSlot_writeSlot_same
  , ``LeanNative.Semantics.StorageMapBuffer.lookupSlot_writeSlot_ne
  , ``LeanNative.Semantics.HeapState.storageLoad_after_storageStore_same
  , ``LeanNative.Semantics.HeapState.storageLoad_after_storageStore_ne
  , ``LeanNative.Semantics.HeapState.incRefObj_decRefObj_cancel
  , ``LeanNative.Proofs.evalBinOp_u256_and_self, ``LeanNative.Proofs.evalBinOp_u256_or_self
  , ``LeanNative.Proofs.evalBinOp_u256_xor_zero, ``LeanNative.Proofs.evalBinOp_u256_or_zero
  , ``LeanNative.Proofs.storageStore_load_same_sound, ``LeanNative.Proofs.storageStore_load_ne_sound
  , ``LeanNative.Proofs.evalBinOp_const_fold_sound, ``LeanNative.Proofs.rewriteConstFoldStep_sound
  , ``LeanNative.Proofs.rewriteScalarVerified_sound, ``LeanNative.Proofs.rewriteLNIRExprVerified_sound
  , ``LeanNative.Proofs.evalExpr_rewriteLNIRExprVerified_eq, ``LeanNative.Proofs.evalCode_rewriteCodeVerified_eq
  , ``LeanNative.Proofs.rewriteCodeVerified_refines
  , ``LeanNative.Backend.FastCheck.certifyCounterexample_no_false_positive
  , ``LeanNative.Backend.FastCheck.substScalarExpr_nil
  , ``LeanNative.Backend.FastCheck.substSingleConstraint_sound
  , ``LeanNative.Backend.FastCheck.propagatePrecondition_letBind_sound
  , ``LeanNative.Spec.untrusted_opt_plugin_tv_gate_sound, ``LeanNative.Spec.untrusted_opt_plugin_code_refines
  , ``LeanNative.Spec.untrusted_opt_plugin_timeout_fallback, ``LeanNative.Spec.untrusted_opt_plugin_reject_fallback
  , ``LeanNative.Spec.opt_pipeline_two_step_refines, ``LeanNative.Spec.opt_pipeline_chain_refines
  , ``LeanNative.Spec.fastcheck_rejects_vacuous_precondition, ``LeanNative.Spec.fastcheck_non_vacuous_tightness_law
  , ``LeanNative.Spec.c_abi_box_zero_eq_one, ``LeanNative.Spec.c_abi_unbox_box_zero
  , ``LeanNative.Spec.c_abi_unbox_box_one, ``LeanNative.Spec.pr_spec_pinning_blocks_spec_tampering
  , ``LeanNative.Spec.pr_spec_pinning_blocks_test_tampering, ``LeanNative.Spec.pr_spec_pinning_blocks_forbidden_axioms
  , ``LeanNative.Spec.pr_spec_pinning_gate_sound
  , ``LeanNative.Proofs.uint64_mul_sixteen, ``LeanNative.Proofs.uint64_mul_thirtytwo
  , ``LeanNative.Proofs.uint64_two_mul, ``LeanNative.Proofs.uint64_four_mul
  , ``LeanNative.Proofs.uint64_eight_mul, ``LeanNative.Proofs.uint64_div_two
  , ``LeanNative.Proofs.uint64_div_four, ``LeanNative.Proofs.uint64_div_eight
  , ``LeanNative.Proofs.uint64_add_self_shl_one, ``LeanNative.Proofs.uint64_add_assoc_const
  , ``LeanNative.Proofs.uint64_and_mask_coalesce, ``LeanNative.Proofs.uint64_or_mask_coalesce
  , ``LeanNative.Proofs.uint64_xor_mask_coalesce, ``LeanNative.Proofs.uint64_mul_add_distrib_const
  , ``LeanNative.Proofs.evalScalarExpr_add_self_u64, ``LeanNative.Proofs.evalScalarExpr_add_assoc_const_u64
  , ``LeanNative.Proofs.evalScalarExpr_and_mask_coalesce_u64, ``LeanNative.Proofs.evalScalarExpr_or_mask_coalesce_u64
  , ``LeanNative.Proofs.evalScalarExpr_xor_mask_coalesce_u64, ``LeanNative.Proofs.evalScalarExpr_mul_add_distrib_const_u64
  , ``LeanNative.Spec.meta_verified_contract_compose_sound, ``LeanNative.Spec.meta_validator_rejects_semantic_mutants
  , ``LeanNative.Spec.meta_limb256_mul_lo_homomorphism, ``LeanNative.Spec.meta_unbox_tuple_full_elim_sound
  , ``LeanNative.Spec.meta_double_shift_mask_and_fma_sound, ``LeanNative.Proofs.unboxTupleDeadElim_refines
  , ``LeanNative.Proofs.uint64_shr_shl_mask_collapse, ``LeanNative.Proofs.evalScalarExpr_shr_shl_mask_collapse_u64
  , ``LeanNative.Proofs.evalScalarExpr_fma_fusion_u64, ``LeanNative.Proofs.uint64_rotl_comm_or
  , ``LeanNative.Spec.small_trip_prefers_cpu_simd, ``LeanNative.Spec.matrix_contraction_prefers_tpu_mxu
  , ``LeanNative.Spec.federated_node_effective_cost_monotone_in_queue, ``LeanNative.Spec.composeAffineBudget_eval
  , ``LeanNative.Spec.affine_step_budget_monotone, ``LeanNative.Spec.bootstrap_shift_step_budget_sound
  , ``LeanNative.Spec.empirical_high_water_refutes_loose_bound, ``LeanNative.Spec.evalLoopStepBudget_monotone
  , ``LeanNative.Spec.riscv_div_by_zero_spec, ``LeanNative.Spec.zisk_csr_atomic_step_budget
  , ``LeanNative.Spec.evalPassChainBudget_cons, ``LeanNative.Spec.sptLookup_insert_same
  , ``LeanNative.Spec.pass_chain_two_passes_eval, ``LeanNative.Spec.spt_rom_fetch_deterministic
  , ``LeanNative.Spec.mulDivDown_le_mulDivUp, ``LeanNative.Spec.mulDivDown_zero_denom
  , ``LeanNative.Spec.dotNat_nil_left, ``LeanNative.Spec.dotNat_nil_right
  , ``LeanNative.Spec.dotNat_cons, ``LeanNative.Spec.dotNat_le_of_pointwise_le
  , ``LeanNative.Spec.farkas_weighted_rows_le, ``LeanNative.Spec.checkFarkasNat_sound
  , ``LeanNative.Spec.MetaGateSpec.rejects_unsafe, ``LeanNative.Spec.sampleMonotoneOffsets4_valid
  , ``LeanNative.Spec.sampleLoadFactorHalf_valid, ``LeanNative.Spec.subSliceView_valid
  , ``LeanNative.Spec.gpu_memory_headroom_gate_sound, ``LeanNative.Spec.gpu_oom_falls_back_to_cpu_simd
  , ``LeanNative.Spec.matryoshka_incremental_prefix_eq_full_eval
  , ``LeanNative.Spec.sarray_restrict_simd_gate_sound, ``LeanNative.Spec.sarray_escaping_closure_rejects_restrict_simd
  , ``LeanNative.Spec.nested_prod_while_sroa_gate_sound, ``LeanNative.Spec.escaping_pair_rejects_nested_prod_sroa
  , ``LeanNative.Spec.mulhi_u128_peephole_gate_sound, ``LeanNative.Spec.non32_mask_rejects_mulhi_u128_peephole
  , ``LeanNative.Spec.tuple_sarray_fill_gate_sound, ``LeanNative.Spec.non_sarray_tag_rejects_tuple_fill
  , ``LeanNative.Spec.nat_bool_while_sroa_gate_sound, ``LeanNative.Spec.escaping_nat_rejects_while_sroa
  , ``LeanNative.Spec.mixed_sarray_while_sroa_gate_sound, ``LeanNative.Spec.escaping_alias_rejects_mixed_while_sroa
  , ``LeanNative.Spec.nested_range_tuple_mut_gate_sound, ``LeanNative.Spec.non_unit_step_rejects_nested_range_mut
  , ``LeanNative.Spec.early_return_ctor_strip_gate_sound, ``LeanNative.Spec.escaping_ctor_rejects_early_return_strip
  , ``LeanNative.Spec.nested_2d_range_forin_gate_sound, ``LeanNative.Spec.non_scalar_inner_idx_rejects_2d_range_forin
  , ``LeanNative.Spec.inbody_range_forin_elision_gate_sound, ``LeanNative.Spec.escaping_range_rejects_inbody_elision
  , ``LeanNative.Spec.pingpong_sarray_swap_sroa_gate_sound, ``LeanNative.Spec.aliased_buffers_reject_pingpong_swap
  , ``LeanNative.Spec.sar64_return_diamond_peephole_gate_sound, ``LeanNative.Spec.wide_shift_rejects_sar64_diamond
  , ``LeanNative.Spec.multi_sarray_stack_sroa_gate_sound, ``LeanNative.Spec.escaping_sarray_rejects_stack_sroa
  , ``LeanNative.Spec.stack_promoted_range_elision_gate_sound, ``LeanNative.Spec.escaping_range_ctor_rejects_stack_promotion
  , ``LeanNative.Spec.repeatm_triple_sarray_sroa_gate_sound, ``LeanNative.Spec.uninlined_helper_rejects_triple_sarray_sroa
  , ``LeanNative.Spec.v2Nat_odd_zero, ``LeanNative.Spec.coxeter_braid_len
  , ``LeanNative.Spec.tropical_scan_head, ``LeanNative.Spec.sturm_tarski_bounds_gate_sound
  , ``LeanNative.Spec.root_crossing_rejects_sturm_tarski_bounds, ``LeanNative.Spec.reg_cut_feasible_sound
  , ``LeanNative.Spec.reg_cut_cost_monotone, ``LeanNative.Spec.fpga_lsc2_256bit_routing_sound
  , ``LeanNative.Spec.mathlib_cert_lowering_gate_sound, ``LeanNative.Spec.native_decide_rejects_mathlib_cert_lowering
  , ``LeanNative.Spec.cabi_slice_io_gate_sound, ``LeanNative.Spec.overflow_out_len_rejects_cabi_slice_io
  , ``LeanNative.Spec.wave15_to_18_structural_gate_sound, ``LeanNative.Spec.unguarded_entry_rejects_wave15_to_18_opt
  , ``LeanNative.Spec.no_runtime_slice_out_gate_sound, ``LeanNative.Spec.runtime_sym_rejects_slice_out
  , ``LeanNative.Spec.lazy_reduction_slice_gate_sound, ``LeanNative.Spec.non_linear_rejects_lazy_reduction_slice
  , ``LeanNative.Spec.radix4_ntt_fusion_gate_sound, ``LeanNative.Spec.misaligned_stride_rejects_radix4_ntt
  , ``LeanNative.Spec.gf128Elem_xor_comm
  , ``LeanNative.Spec.gf128_fused_2layer_butterfly_eq_sequential
  , ``LeanNative.Spec.ntt_butterfly_fused_2layer_slice_word0_eq
  , ``LeanNative.Spec.turbo_slice_scanner_sroa_gate_sound, ``LeanNative.Spec.escaping_tuple_or_oob_rejects_slice_scanner_sroa
  , ``LeanNative.Spec.parFor_chunk_partition_gate_sound, ``LeanNative.Spec.parFor_chunk_partition_rejects_invalid_or_overflow
  , ``LeanNative.Spec.rc_mode_safe_gate_sound, ``LeanNative.Spec.rc_mode_safe_rejects_invalid
  , ``LeanNative.Spec.backend_choice_gate_sound, ``LeanNative.Spec.backend_choice_rejects_misaligned_or_small_metal
  , ``LeanNative.Spec.low_twiddle_zmm_ntt_gate_sound, ``LeanNative.Spec.nonzero_tw_hi_rejects_low_twiddle_3clmul
  , ``LeanNative.Spec.trineon_fold_four_gate_sound, ``LeanNative.Spec.gpr_fmov_or_misaligned_rejects_trineon_fold_four
  , ``LeanNative.Spec.zero_copy_slice_io_gate_sound, ``LeanNative.Spec.overlap_or_overflow_rejects_zero_copy_slice_io
  , ``LeanNative.Proofs.evalParKernelLoop_append, ``LeanNative.Proofs.parFor_chunk_partition_sound
  , ``LeanNative.Semantics.HeapState.decRefBuf_one_frees_buffer
  , ``LeanNative.Semantics.HeapState.decRefBuf_none_error, ``LeanNative.Semantics.HeapState.incRefBuf_none_error
  , ``LeanNative.Proofs.applyExprRules_sound
  , ``LeanNative.Proofs.applyRewriteTable_sound
  , ``LeanNative.Transform.optimizeEqSatCode_sound
  , ``LeanNative.Transform.applyLoopScheduleAux_refines
  , ``LeanNative.Transform.scheduleStructuredLoop_sound
  , ``LeanNative.Transform.elideAndMutateRC_sound
  , ``LeanNative.Backend.Proofs.lowerScalarToMLIR_sound
  , ``LeanNative.Backend.Proofs.lowerToLeanMLIR_sound
  , ``LeanNative.Backend.Proofs.runArm64_butterflyStepInstrs_inv
  , ``LeanNative.Backend.Proofs.arm64_f128_kernel_refines_lnir
  , ``LeanNative.Backend.StableHLOAst.stablehlo_add_comm
  , ``LeanNative.Backend.StableHLOAst.stablehlo_add_assoc
  , ``LeanNative.Backend.StableHLOAst.evalOp_add_result_type
  , ``ConLeche.inferType_sound
  , ``ConLeche.con_leche_verify_decl_sound
  , ``ConLeche.olean_mmap_bridge_sound
  , ``TurboLean.ElabAudit.header_pin_prevents_statement_spoofing
  , ``TurboLean.ElabAudit.cas_proof_replay_sound
  , ``LeanNative.Proofs.mutant1_off_by_one_killed
  , ``LeanNative.Proofs.mutant2_exclusivity_violation_killed
  , ``LeanNative.Proofs.mutant3_algebraic_swap_killed
  , ``LeanNative.Proofs.all_three_mandatory_mutants_killed
  , ``LeanNative.Proofs.HybridCAbi.c99AlignUp_spec
  , ``LeanNative.Proofs.HybridCAbi.c99Scalar_align_pos
  , ``LeanNative.Proofs.HybridCAbi.c99Scalar_size_pos
  , ``LeanNative.Proofs.HybridCAbi.c99NatMax_ge
  , ``LeanNative.Proofs.HybridCAbi.placeC99Field_spec
  , ``LeanNative.Proofs.HybridCAbi.placeC99FieldsFrom_spec
  , ``LeanNative.Proofs.HybridCAbi.c99OccupiedEnd_ge
  , ``LeanNative.Proofs.HybridCAbi.computeC99StructLayout_sound
  , ``LeanNative.Proofs.HybridCAbi.computeC99StructLayout_field_align_dvd
  , ``LeanNative.Proofs.HybridCAbi.emitSliceStaticAsserts_fail_closed
  , ``LeanNative.Proofs.HybridCAbi.emitPinnedSliceStaticAsserts_fail_closed
  , ``LeanNative.Proofs.HybridCAbi.archWidth_addrLimit_pos
  , ``LeanNative.Proofs.HybridCAbi.checkedByteLen_no_overflow
  , ``LeanNative.Proofs.HybridCAbi.checkedStridedSpan_no_overflow
  , ``LeanNative.Proofs.HybridCAbi.strided_slot_in_bounds
  , ``LeanNative.Proofs.HybridCAbi.byteArray_splice_extract_id
  , ``LeanNative.Proofs.HybridCAbi.copyStridedElem_size
  , ``LeanNative.Proofs.HybridCAbi.marshalStridedGo_eq_append
  , ``LeanNative.Proofs.HybridCAbi.marshalStridedGo_empty_size
  , ``LeanNative.Proofs.HybridCAbi.byteArray_extract_mid
  , ``LeanNative.Proofs.HybridCAbi.marshalStridedGo_extract_slot
  , ``LeanNative.Proofs.HybridCAbi.unmarshalStridedGo_roundtrip
  , ``LeanNative.Proofs.HybridCAbi.marshal_unmarshal_byte_slice_roundtrip
  , ``LeanNative.Proofs.HybridCAbi.marshal_unmarshal_float_slice_roundtrip
  , ``LeanNative.Proofs.HybridCAbi.validateC99Slice_sound
  , ``LeanNative.Proofs.HybridCAbi.execValidatedSliceHostCall_id_roundtrip
  , ``LeanNative.Proofs.HybridCAbi.checkedBytes_spec
  , ``LeanNative.Proofs.HybridCAbi.elemByteAddr_in_addressInterval
  , ``LeanNative.Proofs.HybridCAbi.disjointBuffers_elemByteAddr_ne
  , ``LeanNative.Proofs.HybridCAbi.launchGeometryOk_sound
  , ``LeanNative.Proofs.HybridCAbi.bufferGeometryOk_sound
  , ``LeanNative.Proofs.HybridCAbi.bufferGeometryOk_of_geometryOk
  , ``LeanNative.Proofs.HybridCAbi.targetBufferGeometryOk_sound
  , ``LeanNative.Proofs.HybridCAbi.bufferOwnershipOk_sound
  , ``LeanNative.Proofs.HybridCAbi.buffersOwned_of_all
  , ``LeanNative.Proofs.HybridCAbi.bufferAliasPairOk_sound
  , ``LeanNative.Proofs.HybridCAbi.bufferAliasOk_sound
  , ``LeanNative.Proofs.HybridCAbi.find?_map_preserve_buf_id
  , ``LeanNative.Proofs.HybridCAbi.find?_setBufferExclusive
  , ``LeanNative.Proofs.HybridCAbi.find?_eq_some_id
  , ``LeanNative.Proofs.HybridCAbi.find?_filter_self_none
  , ``LeanNative.Proofs.HybridCAbi.find?_refCounts_filtered
  , ``LeanNative.Proofs.HybridCAbi.getBufRefCount_pos
  , ``LeanNative.Proofs.HybridCAbi.incRefBuf_decRefBuf_one_roundtrip
  , ``LeanNative.Proofs.HybridCAbi.transferModeCompatible_self
  , ``LeanNative.Proofs.HybridCAbi.execHybridTransferLifecycle_active_live
  , ``LeanNative.Proofs.HybridCAbi.execHybridTransferLifecycle_preserves_rc
  , ``LeanNative.Proofs.HybridCAbi.execHybridTransferLifecycle_exclusive_out
  , ``LeanNative.Proofs.HybridCAbi.ownershipOk_implies_rcConserved
  , ``LeanNative.Proofs.HybridCAbi.buffersOwned_implies_rcConserved
  , ``LeanNative.Proofs.HybridCAbi.globalThreadId_bijection
  , ``LeanNative.Proofs.HybridCAbi.validateHybridDispatch_sound
  , ``LeanNative.Proofs.HybridCAbi.validateZeroCopySliceIoCall_sound
  , ``LeanNative.Proofs.HybridCAbi.zeroCopySpanFitsU64_iff_addrLimit
  , ``LeanNative.Proofs.HybridCAbi.spliceOutputSlice_size
  , ``LeanNative.Proofs.HybridCAbi.spliceOutputSlice_extract_written
  , ``LeanNative.Proofs.HybridCAbi.spliceOutputSlice_preserves_prefix
  , ``LeanNative.Proofs.HybridCAbi.spliceOutputSlice_preserves_suffix_outside_cap
  , ``LeanNative.Proofs.HybridCAbi.execZeroCopySliceIoHostCall_failure_preserves_mem
  , ``LeanNative.Proofs.HybridCAbi.execZeroCopySliceIoHostCall_ok_sound
  , ``LeanNative.Proofs.contractKernelScalar_sound
  , ``LeanNative.Proofs.specializeKernelCode_refines
  , ``LeanNative.Proofs.fuseMapScaleAddPair_algebra
  , ``LeanNative.Proofs.fuseMapScaleAdd_loop_sound
  , ``LeanNative.Proofs.fuseParForKernels_sound
  , ``LeanNative.Proofs.fuseCustomScalar1_elem_sound
  , ``LeanNative.Proofs.fuseCustomScalar1_bool_coerced_elem_sound
  , ``LeanNative.Proofs.ctorTag_obj_sound
  , ``LeanNative.Proofs.ctorTag_tuple_sound
  , ``LeanNative.Proofs.ctorGetObj_sound
  , ``LeanNative.Proofs.lowerClosureAlloc_sound
  , ``LeanNative.Proofs.specializeKnownClosure_sound
  , ``LeanNative.Proofs.lowerClosureSeqFor_step1_sound
  , ``LeanNative.Proofs.adtMatchArm_taken
  , ``LeanNative.Proofs.adtMatchArm_fallthrough
  , ``LeanNative.Proofs.defunctionalizeClosure_sound
  , ``LeanNative.Proofs.lowerAdtMatch_sound
  , ``LeanNative.Proofs.checkedSubSlice_valid
  , ``LeanNative.Proofs.checkedSubSlice_oob_rejects
  , ``LeanNative.Proofs.subSliceBounds_no_oob
  , ``LeanNative.Proofs.lowerSliceGet_sound
  , ``LeanNative.Proofs.lowerSliceRawLoad_sound
  , ``LeanNative.Proofs.sliceFoldStep_sound
  , ``LeanNative.Proofs.sliceFoldLoop_sound
  , ``LeanNative.Proofs.lowerSliceFold_sound
  , ``LeanNative.Proofs.HeapObjAbi.unbox_box_id
  , ``LeanNative.Proofs.HeapObjAbi.unbox_box_eq_iff
  , ``LeanNative.Proofs.HeapObjAbi.box_ne_aligned_ptr
  , ``LeanNative.Proofs.HeapObjAbi.unpack_pack_header_id
  , ``LeanNative.Proofs.HeapObjAbi.pack_unpack_header_id
  , ``LeanNative.Proofs.HeapObjAbi.unique_dec_ref_triggers_free
  , ``LeanNative.Proofs.HeapObjAbi.shared_dec_ref_stays_live
  , ``LeanNative.Proofs.HeapObjAbi.cowWriteField_matches_pureClone_payload
  , ``LeanNative.Proofs.HeapObjAbi.cowWriteField_result_exclusive
  , ``LeanNative.Proofs.HeapObjAbi.cowWriteField_preserves_live_alias
  , ``LeanNative.Backend.LLVMAst.ppType_injective
  , ``LeanNative.Backend.LLVMAst.ppInstr_nonempty
  , ``LeanNative.Backend.LLVMAst.add_nsw_overflow_poison
  , ``LeanNative.Backend.LLVMAst.shl_overshift_poison
  , ``LeanNative.Backend.LLVMAst.udiv_zero_ub
  , ``LeanNative.Backend.LLVMAst.phi_parallel_swap
  , ``LeanNative.Backend.LLVMAst.load_after_alloca_store
  , ``LeanNative.Backend.LLVMAst.execFn_deterministic
  , ``LeanNative.Backend.LLVMAst.execFn_mono_fuel
  , ``LeanNative.Backend.PTXAst.st_shared_preserves_global
  , ``LeanNative.Backend.PTXAst.st_global_preserves_shared
  , ``LeanNative.Backend.PTXAst.bar_sync_uniform_converges
  , ``LeanNative.Backend.PTXAst.bar_sync_divergent_errors
  , ``LeanNative.Backend.PTXAst.runCTA_deterministic
  , ``LeanNative.Backend.PTXAst.ppPTXType_injective
  , ``LeanNative.Backend.PTXAst.ptx_div_zero_traps
  , ``LeanNative.Backend.PTXAst.ptx_sdiv64_min_neg1_traps
  , ``LeanNative.Backend.PTXAst.stepCTABarrier_allows_ret_exited_threads
  , ``LeanNative.Backend.PTXAst.stepCTABarrier_skipped_pred_ret_falloff_traps
  , ``LeanNative.Backend.PTXAst.stepCTABarrier_divergent_barriers_trap
  , ``LeanNative.Backend.PTXAst.stepCTABarrier_advances_generation_and_clears_epoch
  , ``LeanNative.Backend.PTXAst.sequentialCandidateOfEvents_consistent
  , ``LeanNative.Backend.PTXAst.sequentialCandidateOfEvents_multi_event_nonvacuous
  , ``LeanNative.Backend.PTXAst.ptx_relaxed_atom_add_co_no_lost_updates
  , ``LeanNative.Backend.PTXAst.ptx_relaxed_cross_cta_atom_add_commutes
  , ``LeanNative.Backend.PTXAst.ptx_relaxed_cross_cta_atom_add_exec
  , ``LeanNative.Backend.PTXAst.ptx_seq_kernel_global_write_visible
  , ``LeanNative.Backend.PTXAst.ptx_cta_barrier_gen_write_visible
  , ``LeanNative.Backend.MetalAst.exec_preserves_constant_buffers
  , ``LeanNative.Backend.MetalAst.constant_write_rejected
  , ``LeanNative.Backend.MetalAst.device_const_write_rejected
  , ``LeanNative.Backend.MetalAst.recordEpochAccess_disjoint_ok
  , ``LeanNative.Backend.MetalAst.recordEpochAccess_overlap_races
  , ``LeanNative.Backend.MetalAst.threadgroupBarrier_uniform_converges
  , ``LeanNative.Backend.MetalAst.threadgroupBarrier_divergent_errors
  , ``LeanNative.Backend.MetalAst.runGroup_mono_fuel
  , ``LeanNative.Backend.MetalAst.runGroup_deterministic
  , ``LeanNative.Proofs.lowerScalarExpr_sound
  , ``LeanNative.Proofs.lowerCode_sound
  , ``LeanNative.Proofs.lowerToLLVM_sound
  , ``LeanNative.Proofs.lowerToLLVM_nonvacuous
  , ``LeanNative.Proofs.mutant_m1_killed
  , ``LeanNative.Proofs.mutant_m2_killed
  , ``LeanNative.Proofs.mutant_m3_killed
  , ``LeanNative.Proofs.mutant_m4_killed
  , ``LeanNative.Proofs.mutant_m5_killed
  , ``LeanNative.Proofs.lowerHLOScalarExpr_post
  , ``LeanNative.Proofs.lowerScalarCode_post
  , ``LeanNative.Proofs.lowerParKernel_post
  , ``LeanNative.Proofs.lowerHLOCode_post
  , ``LeanNative.Proofs.bindHLOParams_post
  , ``LeanNative.Proofs.lowerToStableHLO_sound
  , ``LeanNative.Proofs.lowerModuleToStableHLO_singleton_sound
  , ``LeanNative.Proofs.lowerToStableHLO_scalar_nonvacuous
  , ``LeanNative.Proofs.lowerToStableHLO_pipeline_nonvacuous
  , ``LeanNative.Proofs.hlo_mutant_h1_killed
  , ``LeanNative.Proofs.hlo_mutant_h2_killed
  , ``LeanNative.Proofs.hlo_mutant_h3_killed
  , ``LeanNative.Proofs.PTXLowerProofs.lowerToPTX_evalPTXKernel_sound
  , ``LeanNative.Proofs.PTXMutantProofs.lowerToPTX_nonvacuous
  , ``LeanNative.Proofs.PTXMutantProofs.ptx_mutant_m7_killed
  , ``LeanNative.Proofs.PTXMutantProofs.ptx_mutant_m8_killed
  , ``LeanNative.Proofs.PTXDeclProofs.lowerToPTX_sound
  , ``LeanNative.Proofs.PTXDeclProofs.lowerToPTX_decl_nonvacuous
  , ``LeanNative.Proofs.PTXDeclProofs.ptx_dotProduct_atom_add_matches_lnir_fold
  , ``LeanNative.Proofs.PTXDeclProofs.ptx_seq_zipMul_then_atom_add_eq_dotProduct
  , ``LeanNative.Proofs.MetalLowerProofs.lowerScalar_inferExprType
  , ``LeanNative.Proofs.MetalLowerProofs.lowerScalar_eval_sound
  , ``LeanNative.Proofs.MetalLowerProofs.lowerToMetal_evalMSLKernel_sound
  , ``LeanNative.Proofs.MetalMutantProofs.lowerToMetal_nonvacuous
  , ``LeanNative.Proofs.MetalMutantProofs.metal_mutant_m9_killed
  , ``LeanNative.Proofs.MetalMutantProofs.metal_mutant_m10_killed
  , ``LeanNative.Proofs.MetalDeclProofs.lowerToMetal_sound
  , ``LeanNative.Proofs.MetalDeclProofs.lowerToMetal_decl_nonvacuous
  , ``LeanNative.Proofs.GPUEmitterMutantProofs.kill_emitter_mutant_M6
  , ``LeanNative.Proofs.GPUEmitterMutantProofs.kill_emitter_mutant_M7
  , ``LeanNative.Proofs.GPUEmitterMutantProofs.kill_emitter_mutant_M8
  , ``LeanNative.Proofs.GPUEmitterMutantProofs.kill_emitter_mutant_M9
  , ``LeanNative.Proofs.GPUEmitterMutantProofs.kill_emitter_mutant_M10
  , ``LeanNative.Proofs.GPUEmitterMutantProofs.production_decl_emitters_wired
  , ``LeanNative.Proofs.normSymBinOpStep_u64_denotes, ``LeanNative.Proofs.normSymExpr_pureU64_denotes
  , ``LeanNative.Proofs.symEvalScalarRes_pureU64_sound
  , ``LeanNative.Proofs.symExecCode_pureU64_denotes, ``LeanNative.Proofs.symExecCode_pureU64_eval_eq
  , ``LeanNative.Proofs.symExecCode_pureU64_codeRefines_on_u64Env
  , ``LeanNative.Proofs.symbolicCodeRefinesAux_sound, ``LeanNative.Proofs.symbolicCodeRefines_sound
  , ``LeanNative.Proofs.symbolicValidatedDeclOpt_sound
  , ``LeanNative.Proofs.validateTranslationDeclSound_of_passed
  , ``LeanNative.Proofs.checkSingleSample_sound
  , ``LeanNative.Proofs.checkSuperoptScalarVerified_sound
  , ``LeanNative.Proofs.superoptScalarExprCore_sound, ``LeanNative.Proofs.superoptScalarExpr_sound
  , ``LeanNative.Proofs.superoptCodeCore_sound, ``LeanNative.Proofs.superoptCode_sound
  , ``LeanNative.Proofs.superoptDeclCore_sound, ``LeanNative.Proofs.superoptDecl_sound
  , ``LeanNative.Proofs.superoptModuleCore_sound, ``LeanNative.Proofs.superoptModule_sound
  , ``LeanNative.Proofs.superoptModuleWithProfile_sound
  , ``LeanNative.Proofs.lowerLitValuePure_sound
  , ``LeanNative.Proofs.lowerScalarIntrinsicExpr_sound
  , ``LeanNative.Proofs.lowerBoolBinIntrinsic_sound
  , ``LeanNative.Proofs.lowerUnaryAndCast_sound
  , ``LeanNative.Proofs.lowerRealCtor_sound
  , ``LeanNative.Proofs.lowerCanonicalIntrinsicPure_sound
  , ``LeanNative.Proofs.lowerImpureLetValuePure_sound
  , ``LeanNative.Proofs.tag_branch_sound
  , ``LeanNative.Proofs.lowerRefOpPure_sound
  , ``LeanNative.Proofs.lowerStepInr_sound
  , ``LeanNative.Proofs.lowerImpureStepPure_sound
  , ``LeanNative.Proofs.lowerRealLCNFCode_sound
  , ``LeanNative.Proofs.lowerRealLCNFDecl_sound
  , ``LeanNative.Transform.evalSeqLoop_async_refines
  , ``LeanNative.Transform.optimizeAsyncStateMachine_refines
  , ``LeanNative.Proofs.lowerAsyncPollStep_ready_sound
  , ``LeanNative.Proofs.lowerAsyncPollStep_sound
  , ``LeanNative.Proofs.lowerAsyncPollStep_arm1_sound
  , ``LeanNative.Proofs.lowerAsyncPollStep_spec_sound
  , ``LeanNative.Proofs.lowerAsyncEventLoop_sound
  , ``LeanNative.Proofs.lowerAsyncEventLoop_threeStep_sound
  , ``LeanNative.Proofs.lowerAsyncAwaitChain_sound
  , ``LeanNative.Proofs.asyncStateMachinePass_sound
  , ``LeanNative.Proofs.checkNonEscapingAsync_rejects_closure
  , ``LeanNative.Proofs.asyncStateMachine_zeroAlloc_nonvacuous
  , ``LeanNative.Transform.elideMarkMtAndZeroRc_sound
  , ``LeanNative.Transform.optimizeThreadLocalOwnershipRC_sound
  , ``LeanNative.Transform.elideBorrowedAndThreadLocalRC_sound
  , ``LeanNative.Transform.evalIncRef_obj_uaf
  , ``LeanNative.Transform.evalDecRef_obj_uaf
  , ``LeanNative.Proofs.unboxedStructLayout_disjoint_aligned
  , ``LeanNative.Proofs.lowerUnboxedRegionRcFree_true
  , ``LeanNative.Proofs.lowerUnboxedRegionCode_sound
  , ``LeanNative.Proofs.borrowedSliceSub_valid
  , ``LeanNative.Proofs.evalBorrowedObjPair_cancel
  , ``LeanNative.Proofs.elideMarkMtAndZeroRc_preserves_nonEscape
  , ``LeanNative.Proofs.elideBorrowed_preserves_nonEscape
  , ``LeanNative.Proofs.threadLocalEscape_no_mark_mt_sound
  , ``LeanNative.Proofs.headerRc_atomic_threadLocal_inc_equiv
  , ``LeanNative.Proofs.headerRc_atomic_threadLocal_dec_equiv
  , ``LeanNative.Proofs.sendableTransfer_unique_sound
  , ``LeanNative.Proofs.portableSimdVec_lane_roundtrip_sound
  , ``LeanNative.Proofs.portableSimdVec_oob_poison
  , ``LeanNative.Proofs.disjoint_fields_storeInt_noninterference
  , ``LeanNative.Proofs.unboxedRegion_pipeline_nonvacuous
  , ``LeanNative.Proofs.rmw_subword_roundtrip_u64
  , ``LeanNative.Proofs.rmw_subword_disjoint_u64
  , ``LeanNative.Proofs.lowerBorrowedSliceLoad_unaligned_slice_none
  , ``LeanNative.Proofs.lowerBorrowedSliceLoad_unaligned_idx_traps
  , ``LeanNative.Proofs.lowerUnboxedFieldLoad_unaligned_idx_traps
  , ``LeanNative.Proofs.lowerUnboxedFieldStore_unaligned_idx_traps
  , ``LeanNative.Proofs.lowerUnboxedFieldStore_eval_subword
  , ``LeanNative.Proofs.lowerUnboxedFieldLoad_eval_subword
  , ``LeanNative.Proofs.lnir_packed_u32_pair_store_load_sound
  , ``LeanNative.Proofs.loadVal_storeTypedVal_same_scalar
  , ``LeanNative.Proofs.disjoint_fields_store_noninterference
  , ``LeanNative.Proofs.emitLLVMFieldStore_load_roundtrip_sound
  , ``LeanNative.Proofs.tlCheckNonEscaping_eq_checkThreadLocalNonEscaping
  , ``LeanNative.Proofs.checkThreadLocalNonEscaping_rejects_alias_escapes
  , ``LeanNative.Proofs.optimizeThreadLocalOwnershipRC_preserves_escaping_mark_mt
  , ``LeanNative.Proofs.optimizeThreadLocalOwnershipRC_mark_mt_nonvacuous
  , ``LeanNative.Proofs.sendableRecv_preserves_disjoint
  , ``LeanNative.Proofs.evalExpr_isExclusive_of_obj
  , ``LeanNative.Proofs.evalExpr_ensureExclusive_of_obj
  , ``LeanNative.Proofs.dischargeRetainedExclusivity_sound
  , ``LeanNative.Proofs.dischargeLocalExclusivity_refines
  , ``LeanNative.Proofs.llvmAlignedPtr_of_fact_sound
  , ``LeanNative.Proofs.llvmOverflowFlags_of_fact_sound
  , ``LeanNative.Proofs.llvmMulOverflowFlags_of_fact_sound
  , ``LeanNative.Proofs.llvmSubOverflowFlags_of_fact_sound
  , ``LeanNative.Proofs.add_nsw_poison_witness
  , ``LeanNative.Proofs.llvmNoAliasParam_of_disjoint_sound
  , ``LeanNative.Proofs.readBytesAt_disjoint_of_fact
  , ``LeanNative.Proofs.launchBoundsCert_gid_lt_len
  , ``LeanNative.Proofs.ptxBoundsFreeLoad_sound
  , ``LeanNative.Proofs.metalBoundsFreeLoad_sound
  , ``LeanNative.Proofs.proofRetention_pipeline_nonvacuous
  ]

/-- Per-theorem transitive axiom audit result from `Lean.collectAxioms`. -/
structure TheoremAxiomAudit where
  (theoremName : String) (existsInEnv : Bool) (axiomsUsed forbiddenFound nonStandardFound : List String) (passed : Bool)
  deriving Repr, DecidableEq, Inhabited, BEq, ToExpr

/-- Aggregate report of the in-kernel transitive axiom audit. -/
structure AxiomAuditReport where
  (passed : Bool) (theoremsAudited : Nat) (results : List TheoremAxiomAudit) (forbiddenAxiomsFound : List String)
  deriving Repr, DecidableEq, Inhabited, BEq, ToExpr

/-- Inspect a single theorem in `CoreM` using `Lean.collectAxioms`. -/
def auditTheoremInCoreM (declName : Name) : CoreM TheoremAxiomAudit := do
  let env ← getEnv
  if !env.contains declName then
    return { theoremName := declName.toString, existsInEnv := false, axiomsUsed := [],
             forbiddenFound := ["missing_declaration"], nonStandardFound := ["missing_declaration"], passed := false }
  let axList := (← Lean.collectAxioms declName).toList
  let forbidden := axList.filter (forbiddenAxioms.contains ·)
  let nonStd := axList.filter (!allowedStandardAxioms.contains ·)
  return { theoremName := declName.toString, existsInEnv := true, axiomsUsed := axList.map Name.toString,
           forbiddenFound := forbidden.map Name.toString, nonStandardFound := nonStd.map Name.toString,
           passed := forbidden.isEmpty && nonStd.isEmpty }

/-- Audit all soundness theorems in `LeanNative.Proofs` and `LeanNative.Semantics` in `CoreM`. -/
def auditAllProofsCoreM (names : List Name := auditedTheoremNames) : CoreM AxiomAuditReport := do
  let mut results : List TheoremAxiomAudit := []
  let mut allForbidden : List String := []
  for name in names do
    let res ← auditTheoremInCoreM name
    results := results ++ [res]
    for f in res.forbiddenFound ++ res.nonStandardFound do
      if !allForbidden.contains f then allForbidden := allForbidden ++ [f]
  return { passed := results.all (·.passed), theoremsAudited := results.length,
           results := results, forbiddenAxiomsFound := allForbidden }

/-- Elaboration-time kernel gate: runs `auditAllProofsCoreM` during compilation of `AxiomAudit.lean`,
    fails the build if any theorem depends on `sorryAx`, `trustCompiler`, or non-standard axioms,
    and binds `verifiedAxiomAuditReport` in the kernel environment to the exact `Lean.collectAxioms` result. -/
elab "#verify_lean_native_axioms" : command => do
  Elab.Command.liftCoreM do
    let report ← auditAllProofsCoreM auditedTheoremNames
    if !report.passed then
      throwError s!"[AxiomAudit] Kernel axiom audit FAILED! Forbidden/non-standard axioms found: {report.forbiddenAxiomsFound}"
    let arr := report.results.toArray
    let numChunks := (arr.size + 31) / 32
    let mut chunks : Array Expr := #[]
    for i in [:numChunks] do
      let chunk := (arr.extract (i * 32) (min arr.size ((i + 1) * 32))).toList
      chunks := chunks.push (toExpr chunk)
    while chunks.size > 1 do
      let mut next : Array Expr := #[]
      let pairs := chunks.size / 2
      for j in [:pairs] do
        let l := chunks[2 * j]!
        let r := chunks[2 * j + 1]!
        next := next.push (mkApp3 (mkConst ``List.append [Level.zero]) (mkConst ``TheoremAxiomAudit) l r)
      if chunks.size % 2 == 1 then
        next := next.push chunks[chunks.size - 1]!
      chunks := next
    let resultsExpr := chunks[0]?.getD (toExpr ([] : List TheoremAxiomAudit))
    let reportExpr := mkApp4 (mkConst ``AxiomAuditReport.mk) (toExpr report.passed) (toExpr report.theoremsAudited) resultsExpr (toExpr report.forbiddenAxiomsFound)
    addAndCompile (Declaration.defnDecl {
      name := `LeanNative.Proofs.verifiedAxiomAuditReport
      levelParams := []
      type := mkConst ``AxiomAuditReport
      value := reportExpr
      hints := ReducibilityHints.abbrev
      safety := DefinitionSafety.safe
    })

#verify_lean_native_axioms

abbrev escapeJsonStr := LeanNative.IR.jsonEscape

def TheoremAxiomAudit.toJson (t : TheoremAxiomAudit) : String :=
  let q (xs : List String) := String.intercalate "," (xs.map (fun a => s!"\"{escapeJsonStr a}\""))
  s!"\{\"theoremName\":\"{escapeJsonStr t.theoremName}\"," ++
  s!"\"existsInEnv\":{t.existsInEnv},\"passed\":{t.passed}," ++
  s!"\"axiomsUsed\":[{q t.axiomsUsed}],\"forbiddenFound\":[{q t.forbiddenFound}]," ++
  s!"\"nonStandardFound\":[{q t.nonStandardFound}]}"

def AxiomAuditReport.toJson (r : AxiomAuditReport) : String :=
  let resJson := String.intercalate "," (r.results.map TheoremAxiomAudit.toJson)
  let forbJson := String.intercalate "," (r.forbiddenAxiomsFound.map (fun a => s!"\"{escapeJsonStr a}\""))
  s!"\{\"passed\":{r.passed},\"theoremsAudited\":{r.theoremsAudited},\"forbiddenAxiomsFound\":[{forbJson}],\"results\":[{resJson}]}"

def AxiomAuditReport.formatSummary (r : AxiomAuditReport) : String :=
  let sAx := "sor" ++ "ryAx"
  let tComp := "trust" ++ "Compiler"
  let forbDesc :=
    if r.forbiddenAxiomsFound.isEmpty then s!"none (0 {sAx}, 0 {tComp})"
    else String.intercalate ", " r.forbiddenAxiomsFound
  let header := s!"=== LeanNative In-Kernel Transitive Axiom Audit ===\n" ++
                s!"Status: {if r.passed then "PASSED (L3 VerifiedKernelProof)" else "FAILED"}\n" ++
                s!"Theorems Audited: {r.theoremsAudited}\n" ++
                s!"Forbidden Axioms Found: {forbDesc}\n"
  let lines := r.results.map (fun t =>
    let status := if t.passed then "OK" else "FAIL"
    let axs := if t.axiomsUsed.isEmpty then "(pure kernel reduction)" else String.intercalate ", " t.axiomsUsed
    s!"  [{status}] {t.theoremName} -> [{axs}]")
  header ++ String.intercalate "\n" lines

end LeanNative.Proofs
