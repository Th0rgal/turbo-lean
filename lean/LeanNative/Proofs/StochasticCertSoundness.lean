import LeanNative.Transform.StochasticCert

namespace LeanNative.Proofs

open LeanNative.IR LeanNative.Semantics LeanNative.Transform

set_option autoImplicit false

theorem certifyScalarPair_sound (profile : HardwareCostProfile) (lhs rhs : ScalarExpr)
    (h : certifyScalarPair profile lhs rhs = true) :
    ExprRefines (.scalar lhs) (.scalar rhs) := by
  simp only [certifyScalarPair, Bool.and_eq_true] at h
  exact checkSuperoptScalarVerified_sound lhs rhs h.1.2

theorem applyCertifiedScalarRewrite_sound (profile : HardwareCostProfile)
    (candidate : StochasticCandidate) (e : LNIRExpr) :
    ExprRefines e (applyCertifiedScalarRewrite profile candidate e) :=
  (candidateToVerifiedRule profile candidate).sound e

theorem stochasticProposerGate_sound (profile : HardwareCostProfile)
    (proposer : ScalarExpr → Option ScalarExpr) (lhs : ScalarExpr) :
    ExprRefines (.scalar lhs) (.scalar (evalWithStochasticProposer profile proposer lhs)) := by
  unfold evalWithStochasticProposer
  cases h : proposer lhs with
  | none => exact ExprRefines.refl _
  | some rhs =>
    dsimp only
    split
    · rename_i hc
      exact certifyScalarPair_sound profile lhs rhs hc
    · exact ExprRefines.refl _

theorem applyCertifiedBundleCode_sound (bundle : CertifiedRuleBundle) (code : LNIRCode) :
    CodeRefines code (applyCertifiedBundleCode bundle code) :=
  applyRewriteTable_sound (certBundleToVerifiedRules bundle) code

theorem stochasticCert_kills_unsound_mutant (profile : HardwareCostProfile) :
    certifyScalarPair profile (.binOp .add (.var 0) (.constU64 1)) (.var 0) = false := by
  rfl

theorem stochasticCert_strict_cost_improvement (profile : HardwareCostProfile) (lhs rhs : ScalarExpr)
    (h : certifyScalarPair profile lhs rhs = true) :
    scalarExprCostWithProfile profile rhs < scalarExprCostWithProfile profile lhs := by
  simp only [certifyScalarPair, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem stochasticCert_nonvacuous_pipeline :
    applyCertifiedBundleCode cachedStochasticBundle stochasticCertWitnessCode =
      .letBind 1 .i64 (.scalar (.var 0)) (.ret 1) ∧
    applyCertifiedBundleCode cachedStochasticBundle stochasticCertWitnessCode ≠ stochasticCertWitnessCode ∧
    evalCode 8 (VarEnv.empty.bind 0 (.u64 42)) HeapState.empty
      (applyCertifiedBundleCode cachedStochasticBundle stochasticCertWitnessCode) =
      .ok (.u64 42, HeapState.empty) := by
  refine ⟨rfl, ?_, rfl⟩
  intro h
  change LNIRCode.letBind 1 .i64 (.scalar (.var 0)) (.ret 1) =
    LNIRCode.letBind 1 .i64 (.scalar (.binOp .add (.var 0) (.constU64 0))) (.ret 1) at h
  cases h

end LeanNative.Proofs
