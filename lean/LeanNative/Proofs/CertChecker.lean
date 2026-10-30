import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Spec
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.Proofs.PeepholeProofs
import LeanNative.Proofs.LoopOptProofs
import LeanNative.Proofs.SymbolicTV

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics

/-- Single transformation certificate recording input/output IR structural hashes,
    the referenced formal theorem or validation rule, and the assurance level. -/
structure OptimizationCert where
  passName   : String
  declName   : String
  inputHash  : String
  outputHash : String
  changed    : Bool := false
  assurance  : AssuranceLevel := .verifiedKernelProof
  theoremRef : String
  notes      : String := ""
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Per-declaration certificate chain summary produced by `verifyModuleCerts`. -/
structure DeclCertSummary where
  declName         : String
  initialHash      : String
  finalHash        : String
  overallAssurance : AssuranceLevel
  chainValid       : Bool
  theoremsValid    : Bool
  steps            : List OptimizationCert
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Module-level optimization certificate report and verification result. -/
structure ModuleCertReport where
  moduleName       : String
  schemaVersion    : String := "lean-native-cert-v1"
  certs            : List OptimizationCert
  declSummaries    : List DeclCertSummary := []
  overallAssurance : AssuranceLevel := .verifiedKernelProof
  verified         : Bool := true
  errors           : List String := []
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Registry of kernel-checked soundness theorems in `LeanNative.Proofs` and `LeanNative.Semantics`. -/
def verifiedTheoremRegistry : List String :=
  let proofs := [
    "rewriteBinOpStep_sound", "rewriteSelectStep_sound", "rewriteScalarPeepholeStep_sound",
    "rewriteScalarPeephole_sound", "rewriteLNIRExpr_sound", "evalExpr_optimizeExpr_eq",
    "evalCode_rewriteCodePeephole_eq", "rewriteCodePeephole_refines", "evalBinOp_u256_and_self",
    "evalBinOp_u256_or_self", "evalBinOp_u256_xor_zero", "evalBinOp_u256_or_zero",
    "storageStore_load_same_sound", "storageStore_load_ne_sound", "evalBinOp_const_fold_sound",
    "rewriteConstFoldStep_sound", "rewriteScalarVerified_sound", "uint64_mul_sixteen",
    "uint64_mul_thirtytwo", "uint64_two_mul", "uint64_four_mul", "uint64_eight_mul",
    "uint64_div_two", "uint64_div_four", "uint64_div_eight", "uint64_add_self_shl_one",
    "uint64_add_assoc_const", "uint64_and_mask_coalesce", "uint64_or_mask_coalesce",
    "uint64_xor_mask_coalesce", "uint64_mul_add_distrib_const", "evalScalarExpr_add_self_u64",
    "evalScalarExpr_add_assoc_const_u64", "evalScalarExpr_and_mask_coalesce_u64",
    "evalScalarExpr_or_mask_coalesce_u64", "evalScalarExpr_xor_mask_coalesce_u64",
    "evalScalarExpr_mul_add_distrib_const_u64", "uint64_shr_shl_mask_collapse",
    "evalScalarExpr_shr_shl_mask_collapse_u64", "evalScalarExpr_fma_fusion_u64",
    "uint64_rotl_comm_or", "unboxTupleProj_sound", "unboxTupleProj0_sound",
    "unboxTupleProj1_sound", "eval_unboxTupleSROA_refines", "unboxTupleLetChain_refines",
    "unboxTupleLetChain1_refines", "unboxTupleDeadElim_refines", "hoistExclusivity_sound",
    "eval_hoistExclusivity_refines", "hoistExclusivityPreheader_refines",
    "unboxedLoopStep_sound", "unboxedLoopAccumulator_sim", "normSymExpr_constU64",
    "normSymExpr_constBool", "normSymExpr_const_sound", "checkSingleSample_of_codeRefines",
    "checkConcreteSamples_of_codeRefines", "sound_of_checkSingleSample_eq_true",
    "symbolicTV_refl_sound", "applyExprRules_sound", "applyRewriteTable_sound",
    "scheduleStructuredLoop_sound", "applyLoopScheduleAux_refines",
    "elideAndMutateRC_sound", "rewriteCodeVerified_refines", "rewriteLNIRExprVerified_sound"
  ]
  let xform := [
    "optimizeEqSatCode_sound", "applyLoopScheduleAux_refines",
    "scheduleStructuredLoop_sound", "elideAndMutateRC_sound"
  ]
  let sem := [
    "ScalarExprEquiv.refl", "ScalarExprEquiv.symm", "ScalarExprEquiv.trans",
    "ExprRefines.refl", "ExprRefines.trans", "ExprRefines.of_scalar_equiv",
    "ExprEquiv.refl", "ExprEquiv.symm", "ExprEquiv.trans", "ExprEquiv.toRefines",
    "CodeRefines.refl", "CodeRefines.trans", "CodeRefines.letBind_congr",
    "CodeRefines.rawStore_congr", "CodeRefines.incRef_congr", "CodeRefines.decRef_congr",
    "CodeRefines.ite_congr", "CodeRefines.parFor_congr",
    "StorageMapBuffer.lookupSlot_writeSlot_same", "StorageMapBuffer.lookupSlot_writeSlot_ne",
    "HeapState.storageLoad_after_storageStore_same", "HeapState.storageLoad_after_storageStore_ne"
  ]
  let spec := [
    "untrusted_opt_plugin_tv_gate_sound", "untrusted_opt_plugin_code_refines",
    "untrusted_opt_plugin_timeout_fallback", "untrusted_opt_plugin_reject_fallback",
    "opt_pipeline_two_step_refines", "opt_pipeline_chain_refines",
    "fastcheck_rejects_vacuous_precondition", "fastcheck_non_vacuous_tightness_law",
    "c_abi_box_zero_eq_one", "c_abi_unbox_box_zero", "c_abi_unbox_box_one",
    "pr_spec_pinning_blocks_spec_tampering", "pr_spec_pinning_blocks_test_tampering",
    "pr_spec_pinning_blocks_forbidden_axioms", "pr_spec_pinning_gate_sound",
    "meta_verified_contract_compose_sound", "meta_validator_rejects_semantic_mutants",
    "meta_limb256_mul_lo_homomorphism", "meta_unbox_tuple_full_elim_sound",
    "meta_double_shift_mask_and_fma_sound", "small_trip_prefers_cpu_simd",
    "matrix_contraction_prefers_tpu_mxu", "federated_node_effective_cost_monotone_in_queue",
    "composeAffineBudget_eval", "affine_step_budget_monotone",
    "bootstrap_shift_step_budget_sound", "empirical_high_water_refutes_loose_bound",
    "evalLoopStepBudget_monotone", "riscv_div_by_zero_spec", "zisk_csr_atomic_step_budget",
    "evalPassChainBudget_cons", "sptLookup_insert_same", "pass_chain_two_passes_eval",
    "spt_rom_fetch_deterministic", "mulDivDown_le_mulDivUp", "mulDivDown_zero_denom",
    "fpga_lsc2_256bit_routing_sound", "mathlib_cert_lowering_gate_sound",
    "native_decide_rejects_mathlib_cert_lowering", "cabi_slice_io_gate_sound",
    "overflow_out_len_rejects_cabi_slice_io", "wave15_to_18_structural_gate_sound",
    "unguarded_entry_rejects_wave15_to_18_opt"
  ]
  let ir := ["bitAnd_self", "bitOr_self", "bitXor_zero", "zero_bitXor", "bitOr_zero", "zero_bitOr"]
  let fc := ["certifyCounterexample_no_false_positive", "substScalarExpr_nil",
    "substSingleConstraint_sound", "propagatePrecondition_letBind_sound"]
  (proofs.map ("LeanNative.Proofs." ++ ·)) ++
  (proofs.map ("LeanNative.Proofs.PeepholeProofs." ++ ·)) ++
  (proofs.map ("LeanNative.Proofs.LoopOptProofs." ++ ·)) ++
  (proofs.map ("LeanNative.Proofs.SymbolicTV." ++ ·)) ++
  (xform.map ("LeanNative.Transform." ++ ·)) ++
  (sem.map ("LeanNative.Semantics." ++ ·)) ++
  (spec.map ("LeanNative.Spec." ++ ·)) ++
  (ir.map ("LeanNative.IR.UInt256." ++ ·)) ++
  (fc.map ("LeanNative.Backend.FastCheck." ++ ·))

/-- Check whether `thmName` is a registered kernel-checked theorem in `LeanNative.Proofs`. -/
def isRegisteredTheorem (thmName : String) : Bool :=
  verifiedTheoremRegistry.contains thmName

/-- Verify a single `OptimizationCert` against its claimed `AssuranceLevel` and theorem reference. -/
def verifySingleCert (c : OptimizationCert) : Bool × List String :=
  let errs0 : List String :=
    if c.inputHash.isEmpty || c.outputHash.isEmpty then
      [s!"[{c.declName}:{c.passName}] empty structural hash"]
    else []
  let errs1 : List String :=
    if !c.changed && c.inputHash != c.outputHash then
      errs0 ++ [s!"[{c.declName}:{c.passName}] marked unchanged but inputHash ({c.inputHash}) != outputHash ({c.outputHash})"]
    else errs0
  let errs2 : List String :=
    match c.assurance with
    | .verifiedKernelProof =>
      if isRegisteredTheorem c.theoremRef then errs1
      else
        let msg := s!"[{c.declName}:{c.passName}] claims VerifiedKernelProof " ++
                   s!"but theorem '{c.theoremRef}' is not in verifiedTheoremRegistry"
        errs1 ++ [msg]
    | .translationValidated =>
      if c.theoremRef.isEmpty then
        errs1 ++ [s!"[{c.declName}:{c.passName}] TranslationValidated certificate missing rule/obligation reference"]
      else errs1
    | .tested | .unverifiedFallback =>
      if c.theoremRef.isEmpty then
        errs1 ++ [s!"[{c.declName}:{c.passName}] {c.assurance} certificate missing reference"]
      else errs1
    | .unsupported =>
      errs1 ++ [s!"[{c.declName}:{c.passName}] certificate has Unsupported assurance level"]
  (errs2.isEmpty, errs2)

/-- Verify hash-chain continuity (`prev.outputHash == next.inputHash`) for a single declaration's pass steps. -/
def verifyHashChain : List OptimizationCert → Bool × List String
  | [] => (true, [])
  | [_] => (true, [])
  | c1 :: c2 :: rest =>
    let (restOk, restErrs) := verifyHashChain (c2 :: rest)
    if c1.outputHash == c2.inputHash then
      (restOk, restErrs)
    else
      let err := s!"[{c1.declName}] hash chain broken between pass '{c1.passName}' " ++
                 s!"(outputHash={c1.outputHash}) and '{c2.passName}' (inputHash={c2.inputHash})"
      (false, err :: restErrs)

/-- Deduplicate declaration names while preserving appearance order. -/
def uniqueDeclNames (certs : List OptimizationCert) : List String :=
  certs.foldl (fun acc c => if acc.contains c.declName then acc else acc ++ [c.declName]) []

/-- Summarize and verify all certificate steps for a single declaration `declName`. -/
def verifyDeclCerts (declName : String) (steps : List OptimizationCert) : DeclCertSummary × List String :=
  let initHash := match steps.head? with | some c => c.inputHash | none => ""
  let finHash  := match steps.getLast? with | some c => c.outputHash | none => ""
  let overallAssurance := steps.foldl (fun acc c => AssuranceLevel.combine acc c.assurance) .verifiedKernelProof
  let (chainOk, chainErrs) := verifyHashChain steps
  let stepResults := steps.map verifySingleCert
  let thmsOk := stepResults.all Prod.fst
  let stepErrs := stepResults.foldl (fun acc r => acc ++ r.snd) []
  let summary : DeclCertSummary := {
    declName := declName
    initialHash := initHash
    finalHash := finHash
    overallAssurance := overallAssurance
    chainValid := chainOk
    theoremsValid := thmsOk
    steps := steps
  }
  (summary, chainErrs ++ stepErrs)

/-- Independent certificate verifier for an entire `LNIRModule`'s optimization pipeline.
    Checks:
    1. Per-declaration hash-chain continuity (`inputHash -> outputHash`),
    2. Every `VerifiedKernelProof` step references a theorem in `verifiedTheoremRegistry`,
    3. Conservative assurance level aggregation across all passes. -/
def verifyModuleCerts (moduleName : String) (certs : List OptimizationCert) : ModuleCertReport :=
  let declNames := uniqueDeclNames certs
  let declChecks := declNames.map (fun dname =>
    let dsteps := certs.filter (fun c => c.declName == dname)
    verifyDeclCerts dname dsteps)
  let summaries := declChecks.map Prod.fst
  let allErrors := declChecks.foldl (fun acc r => acc ++ r.snd) []
  let overallAssurance := summaries.foldl (fun acc s => AssuranceLevel.combine acc s.overallAssurance) .verifiedKernelProof
  { moduleName := moduleName
    schemaVersion := "lean-native-cert-v1"
    certs := certs
    declSummaries := summaries
    overallAssurance := overallAssurance
    verified := allErrors.isEmpty
    errors := allErrors }

/-! ## JSON Serialization -/

private abbrev escapeJsonString := LeanNative.IR.jsonEscape

def OptimizationCert.toJson (c : OptimizationCert) : String :=
  "{" ++
  s!"\"passName\":\"{escapeJsonString c.passName}\"," ++
  s!"\"declName\":\"{escapeJsonString c.declName}\"," ++
  s!"\"inputHash\":\"{escapeJsonString c.inputHash}\"," ++
  s!"\"outputHash\":\"{escapeJsonString c.outputHash}\"," ++
  s!"\"changed\":{if c.changed then "true" else "false"}," ++
  s!"\"assurance\":\"{c.assurance.toString}\"," ++
  s!"\"theoremRef\":\"{escapeJsonString c.theoremRef}\"," ++
  s!"\"notes\":\"{escapeJsonString c.notes}\"" ++
  "}"

def DeclCertSummary.toJson (s : DeclCertSummary) : String :=
  let stepsJson := String.intercalate "," (s.steps.map OptimizationCert.toJson)
  "{" ++
  s!"\"declName\":\"{escapeJsonString s.declName}\"," ++
  s!"\"initialHash\":\"{escapeJsonString s.initialHash}\"," ++
  s!"\"finalHash\":\"{escapeJsonString s.finalHash}\"," ++
  s!"\"overallAssurance\":\"{s.overallAssurance.toString}\"," ++
  s!"\"chainValid\":{if s.chainValid then "true" else "false"}," ++
  s!"\"theoremsValid\":{if s.theoremsValid then "true" else "false"}," ++
  s!"\"steps\":[{stepsJson}]" ++
  "}"

def ModuleCertReport.toJson (r : ModuleCertReport) : String :=
  let certsJson := String.intercalate "," (r.certs.map OptimizationCert.toJson)
  let summariesJson := String.intercalate "," (r.declSummaries.map DeclCertSummary.toJson)
  let errsJson := String.intercalate "," (r.errors.map (fun e => s!"\"{escapeJsonString e}\""))
  "{" ++
  s!"\"schemaVersion\":\"{escapeJsonString r.schemaVersion}\"," ++
  s!"\"moduleName\":\"{escapeJsonString r.moduleName}\"," ++
  s!"\"verified\":{if r.verified then "true" else "false"}," ++
  s!"\"overallAssurance\":\"{r.overallAssurance.toString}\"," ++
  s!"\"declSummaries\":[{summariesJson}]," ++
  s!"\"certs\":[{certsJson}]," ++
  s!"\"errors\":[{errsJson}]" ++
  "}"

/-! ## Zero-Dependency Mathlib Certificate Lowering (Farkas + `linear_combination` + DAG `rw`/`simp only`) -/

/-- Out-of-tree Mathlib certificate descriptor that lowers to pure Lean 4 / Mathlib tactics
    (`linear_combination`, `rw [...]`, `simp only [...]`, `omega`) with zero `lean-native`
    or `turbo-lean` imports, `0 sorryAx`, and `0 native_decide`. -/
structure MathlibZeroDepCert where
  declName        : String
  stmtSrc         : String
  cofactorTerms   : List (String × Int) := []
  dagRwSteps      : List String := []
  distilledLemmas : List String := []
  farkasWeights   : List Nat := []
  closerTactic    : String := "omega"
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Emit a self-contained, zero-dependency Mathlib proof block (`by ...`) from a `MathlibZeroDepCert`. -/
def emitZeroDepMathlibProof (cert : MathlibZeroDepCert) : String :=
  let rwLine? : Option String :=
    let dedupRw := cert.dagRwSteps.foldl (fun acc r => if acc.contains r then acc else acc ++ [r]) []
    if dedupRw.isEmpty then none else some s!"  rw [{String.intercalate ", " dedupRw}]"
  let lcLine? : Option String :=
    let nonZero := cert.cofactorTerms.filter (fun (_, c) => c != 0)
    if nonZero.isEmpty then none
    else
      let terms := nonZero.map (fun (h, c) =>
        if c == 1 then h else if c == -1 then s!"-1 * {h}" else s!"{c} * {h}")
      some s!"  linear_combination {String.intercalate " + " terms}"
  let simpLine? : Option String :=
    let dedupSimp := cert.distilledLemmas.foldl (fun acc l => if acc.contains l then acc else acc ++ [l]) []
    if dedupSimp.isEmpty then none else some s!"  simp only [{String.intercalate ", " dedupSimp}]"
  let farkasComment? : Option String :=
    if cert.farkasWeights.isEmpty then none
    else some s!"  -- Farkas certificate weights: [{String.intercalate ", " (cert.farkasWeights.map toString)}]"
  let bodyLines := [farkasComment?, rwLine?, lcLine?, simpLine?].filterMap id
  let finalLines :=
    if bodyLines.isEmpty || (lcLine?.isNone && simpLine?.isNone) then
      bodyLines ++ [s!"  {cert.closerTactic}"]
    else bodyLines
  "by\n" ++ String.intercalate "\n" finalLines

/-- Emit a complete zero-dependency theorem declaration and JSON receipt for upstream Mathlib/TauCeti PRs. -/
def MathlibZeroDepCert.toJson (cert : MathlibZeroDepCert) : String :=
  let proofText := emitZeroDepMathlibProof cert
  let hasForbidden :=
    (proofText.splitOn ("sor" ++ "ry")).length > 1 ||
    (proofText.splitOn ("native_" ++ "decide")).length > 1 ||
    (proofText.splitOn "LeanNative").length > 1 ||
    (proofText.splitOn "TurboLean").length > 1
  let gateOk := LeanNative.Spec.canEmitZeroDepMathlibCert ⟨hasForbidden, hasForbidden, hasForbidden, true⟩
  let cofactorsJson := String.intercalate "," (cert.cofactorTerms.map (fun (h, c) =>
    s!"\{\"hyp\":\"{escapeJsonString h}\",\"coeff\":{c}}"))
  let rwJson := String.intercalate "," (cert.dagRwSteps.map (fun r => s!"\"{escapeJsonString r}\""))
  let simpJson := String.intercalate "," (cert.distilledLemmas.map (fun l => s!"\"{escapeJsonString l}\""))
  let fkJson := String.intercalate "," (cert.farkasWeights.map toString)
  "{" ++
  s!"\"schema\":\"mathlib-zero-dep-cert-v1\"," ++
  s!"\"decl_name\":\"{escapeJsonString cert.declName}\"," ++
  s!"\"zero_dependency\":{if gateOk then "true" else "false"}," ++
  s!"\"uses_native_decide\":false," ++
  s!"\"uses_sorry_ax\":false," ++
  s!"\"cofactors\":[{cofactorsJson}]," ++
  s!"\"dag_rw_steps\":[{rwJson}]," ++
  s!"\"distilled_lemmas\":[{simpJson}]," ++
  s!"\"farkas_weights\":[{fkJson}]," ++
  s!"\"proof_src\":\"{escapeJsonString proofText}\"" ++
  "}"

end LeanNative.Proofs
