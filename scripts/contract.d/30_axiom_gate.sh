echo "=== [3/10] In-Kernel Transitive Axiom Gate (Lean.collectAxioms) ==="
"$CORE_BIN" audit-axioms --json | python3 -c "
import json, sys
d = json.load(sys.stdin)
assert d['passed'] is True, d
assert d['theoremsAudited'] >= 904, d
assert d['forbiddenAxiomsFound'] == [], d
names = {r['theoremName'] for r in d['results']}
required = [
    'LeanNative.Proofs.applyExprRules_sound',
    'LeanNative.Proofs.applyRewriteTable_sound',
    'LeanNative.Proofs.lowerRealLCNFCode_sound',
    'LeanNative.Proofs.lowerRealLCNFDecl_sound',
    'LeanNative.Proofs.H1.specLocked',
    'LeanNative.Proofs.H1.posWitness',
    'LeanNative.Proofs.H1.negWitnessInvertedBranch_killed',
    'LeanNative.Proofs.H1.negWitnessWrongReturn_killed',
    'LeanNative.Proofs.H1.negWitnessDroppedParam_killed',
    'LeanNative.Proofs.H1.negWitnessWrongScrutinee_killed',
    'LeanNative.Proofs.H1.letWitness',
    'LeanNative.Proofs.H1.negWitnessSwappedArith_killed',
    'LeanNative.Proofs.lowerRealLCNFDecl_sound_with',
    'LeanNative.Proofs.lowerLocalCall_sound',
    'LeanNative.Proofs.H1.callRefinement',
    'LeanNative.Proofs.H1.lowerRealLCNFModule_sound',
    'LeanNative.Proofs.H1.posWitnessCall',
    'LeanNative.Proofs.H1.negWitnessWrongCallTarget_killed',
    'LeanNative.Proofs.H1.negWitnessSwappedCallArgs_killed',
    'LeanNative.Proofs.H1.recRefinement',
    'LeanNative.Proofs.H1.lowerRealLCNFRecModule_sound',
    'LeanNative.Proofs.H1.posWitnessSelfRec',
    'LeanNative.Proofs.H1.posWitnessMutualRec',
    'LeanNative.Proofs.H1.posWitnessJoinPoint',
    'LeanNative.Proofs.H1.negWitnessBrokenRecStep_killed',
    'LeanNative.Proofs.H1.negWitnessSwappedMutualTargets_killed',
    'LeanNative.Proofs.H1.negWitnessWrongJoinArg_killed',
    'LeanNative.Transform.optimizeEqSatCode_sound',
    'LeanNative.Transform.scheduleStructuredLoop_sound',
    'LeanNative.Transform.elideAndMutateRC_sound',
    'LeanNative.Backend.Proofs.lowerToLeanMLIR_sound',
    'LeanNative.Backend.Proofs.arm64_f128_kernel_refines_lnir',
    'ConLeche.inferType_sound',
    'ConLeche.con_leche_verify_decl_sound',
    'ConLeche.olean_mmap_bridge_sound',
    'TurboLean.ElabAudit.header_pin_prevents_statement_spoofing',
    'TurboLean.ElabAudit.cas_proof_replay_sound',
    'LeanNative.Proofs.mutant1_off_by_one_killed',
    'LeanNative.Proofs.mutant2_exclusivity_violation_killed',
    'LeanNative.Proofs.mutant3_algebraic_swap_killed',
    'LeanNative.Proofs.all_three_mandatory_mutants_killed',
    'LeanNative.Proofs.llvm_sdiv64_min_neg1_ub',
    'LeanNative.Proofs.llvm_null_load_ub',
    'LeanNative.Proofs.llvm_null_store_ub',
    'LeanNative.Proofs.llvm_oob_gep_inbounds_load_ub',
    'LeanNative.Proofs.stablehlo_sdiv64_min_neg1_eq',
    'LeanNative.Proofs.stablehlo_srem64_min_neg1_zero',
    'LeanNative.Proofs.stablehlo_sdiv_zero_traps',
    'LeanNative.Proofs.stablehlo_clampStart_bounds',
    'LeanNative.Proofs.msl_shift_out_of_range_traps',
    'LeanNative.Proofs.ptx_rem_zero_traps',
    'LeanNative.Proofs.HeapObjMtAbi.mt_dec_ref_last_triggers_free',
    'LeanNative.Proofs.HeapObjMtAbi.mt_inc_ref_stays_mt_no_underflow',
    'LeanNative.Proofs.HeapObjMtAbi.sarray_elem_size_roundtrip_under_markLinear',
    'LeanNative.Proofs.HeapObjMtAbi.sarrayAllocWouldOverflow64_false_iff',
]
missing = [r for r in required if r not in names]
assert not missing, f'Missing mandatory theorems in AxiomAudit: {missing}'
print(f'  [OK] AxiomAudit: {d[\"theoremsAudited\"]} theorems verified in kernel (0 sorryAx, 0 trustCompiler)')
"
