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

theorem applyCertToScalar_sound (profile : HardwareCostProfile) (e : ScalarExpr)
    (cert : CertifiedRewriteCert) : ExprRefines (.scalar e) (.scalar (applyCertToScalar profile e cert)) := by
  unfold applyCertToScalar
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    have heq := ScalarExpr_eq_of_beq h.1
    subst e
    have hc := h.2
    simp only [validateCertifiedRewriteCert, Bool.and_eq_true] at hc
    exact certifyScalarPair_sound _ _ _ hc.2
  · exact ExprRefines.refl _

theorem foldCertifiedScalars_sound (profile : HardwareCostProfile) (certs : List CertifiedRewriteCert)
    (e : ScalarExpr) : ExprRefines (.scalar e) (.scalar (certs.foldl (applyCertToScalar profile) e)) := by
  induction certs generalizing e with
  | nil => exact ExprRefines.refl _
  | cons cert rest ih => exact (applyCertToScalar_sound profile e cert).trans (ih _)

theorem scalarRefines_eval {a b : ScalarExpr} (h : ExprRefines (.scalar a) (.scalar b))
    (env : VarEnv) (v : Val) (hv : evalScalarExpr env a = .ok v) : evalScalarExpr env b = .ok v :=
  ExprRefines.scalar_eval h env v hv

theorem scalarRefines_of_eval {a b : ScalarExpr}
    (h : ∀ env v, evalScalarExpr env a = .ok v → evalScalarExpr env b = .ok v) :
    ExprRefines (.scalar a) (.scalar b) := ExprRefines.scalar_of_eval h

theorem applyCertsToScalar_sound (profile : HardwareCostProfile) (certs : List CertifiedRewriteCert)
    (e : ScalarExpr) : ExprRefines (.scalar e) (.scalar (applyCertsToScalar profile certs e)) := by
  induction e with
  | constU64 _ | constBool _ | var _ => exact foldCertifiedScalars_sound _ _ _
  | binOp op a b iha ihb =>
    exact (ExprRefines.scalar_binOp_congr iha ihb).trans (foldCertifiedScalars_sound _ _ _)
  | unaryOp op a ih =>
    exact (ExprRefines.scalar_unaryOp_congr ih).trans (foldCertifiedScalars_sound _ _ _)
  | select c t f ihc iht ihf =>
    exact (ExprRefines.scalar_select_congr ihc iht ihf).trans (foldCertifiedScalars_sound _ _ _)
  | fma a b c iha ihb ihc =>
    exact (ExprRefines.scalar_fma_congr iha ihb ihc).trans (foldCertifiedScalars_sound _ _ _)

theorem applyCertifiedBundleCode_sound (bundle : CertifiedRuleBundle) (code : LNIRCode) :
    CodeRefines code (applyCertifiedBundleCode bundle code) := by
  induction code with
  | letBind dst ty val k ih =>
    cases val with
    | scalar se => exact CodeRefines.letBind_congr (applyCertsToScalar_sound _ _ se) ih
    | _ => exact CodeRefines.letBind_congr (ExprRefines.refl _) ih
  | rawStore pv iv vv ty k ih => exact CodeRefines.rawStore_congr ih
  | incRef v n k ih => exact CodeRefines.incRef_congr ih
  | decRef v n k ih => exact CodeRefines.decRef_congr ih
  | ite v t f iht ihf => exact CodeRefines.ite_congr iht ihf
  | seqFor _ _ _ _ _ _ _ _ ihs ihk => exact CodeRefines.seqFor_congr ihs ihk
  | parFor ov lv ins ty kern k ih =>
    cases kern with
    | customScalar iv vs body =>
      intro fuel env st v st' hsrc
      simp only [applyCertifiedBundleCode, evalCode] at hsrc ⊢
      cases hp : evalParFor fuel env st lv ins (.customScalar iv vs body) with
      | error err => simp [hp] at hsrc
      | ok pair =>
        rw [hp] at hsrc
        rw [evalParFor_customScalar_refines fuel env st lv ins iv vs body _ pair
          (applyCertsToScalar_sound _ _ _) hp]
        exact ih fuel (env.bind ov pair.1) pair.2 v st' hsrc
    | _ => exact CodeRefines.parFor_congr ih
  | ret _ | unreachable => exact CodeRefines.refl _

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
