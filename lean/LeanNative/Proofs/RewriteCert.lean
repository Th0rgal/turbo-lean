import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.Proofs.PeepholeProofs

/-!
# H3.5 Step 1: Proved Rewrite-Sequence Certificate Checker

An accelerator plugin (e-graph extractor, superoptimizer, external search) may propose a
rewrite *sequence* instead of a rewritten expression. The certificate is a list of rule
indices into a trusted table `rules : List VerifiedExprRule`. The checker `replayCert`
replays the sequence and fails closed (`none`) on any out-of-range index. Every accepted
replay is a kernel-checked refinement (`replayCert_sound`), and the lifted code pass
`applyRewriteCertCode` refines over all 9 `LNIRCode` constructors via
`applyRewriteTable_sound`.
-/

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics

/-- Rewrite-sequence certificate: indices into a trusted `List VerifiedExprRule` table. -/
structure RewriteCert where
  steps : List Nat
  deriving Repr, Inhabited, BEq, DecidableEq

/-- Replay a list of rule indices; `none` as soon as an index is out of range. -/
def replaySteps (rules : List VerifiedExprRule) : List Nat → LNIRExpr → Option LNIRExpr
  | [], e => some e
  | i :: is, e =>
    match rules[i]? with
    | none => none
    | some r => replaySteps rules is (r.apply e)

/-- Certificate checker: replay `cert.steps` against `rules`, failing closed on bad indices. -/
def replayCert (rules : List VerifiedExprRule) (cert : RewriteCert) (e : LNIRExpr) :
    Option LNIRExpr :=
  replaySteps rules cert.steps e

theorem replaySteps_sound (rules : List VerifiedExprRule) (steps : List Nat)
    (e e' : LNIRExpr) (h : replaySteps rules steps e = some e') : ExprRefines e e' := by
  induction steps generalizing e with
  | nil =>
    simp only [replaySteps, Option.some.injEq] at h
    subst h
    exact ExprRefines.refl e
  | cons i is ih =>
    simp only [replaySteps] at h
    cases hr : rules[i]? with
    | none =>
      rw [hr] at h
      contradiction
    | some r =>
      rw [hr] at h
      exact ExprRefines.trans (r.sound e) (ih (r.apply e) h)

/-- Soundness of the certificate checker: every accepted replay refines the source. -/
theorem replayCert_sound {rules : List VerifiedExprRule} {cert : RewriteCert}
    {e e' : LNIRExpr} (h : replayCert rules cert e = some e') : ExprRefines e e' :=
  replaySteps_sound rules cert.steps e e' h

theorem replaySteps_isSome_iff (rules : List VerifiedExprRule) (steps : List Nat)
    (e : LNIRExpr) :
    (replaySteps rules steps e).isSome = true ↔ ∀ i ∈ steps, i < rules.length := by
  induction steps generalizing e with
  | nil => simp [replaySteps]
  | cons i is ih =>
    simp only [replaySteps, List.mem_cons, forall_eq_or_imp]
    cases hr : rules[i]? with
    | none =>
      have hge : rules.length ≤ i := List.getElem?_eq_none_iff.mp hr
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
      intro hlt
      exact absurd hlt (Nat.not_lt.mpr hge)
    | some r =>
      have hlt : i < rules.length := (List.getElem?_eq_some_iff.mp hr).1
      simp only [ih (r.apply e), hlt, true_and]

/-- Fail-closed: a certificate is accepted iff every index is in range of the rule table. -/
theorem replayCert_isSome_iff (rules : List VerifiedExprRule) (cert : RewriteCert)
    (e : LNIRExpr) :
    (replayCert rules cert e).isSome = true ↔ ∀ i ∈ cert.steps, i < rules.length :=
  replaySteps_isSome_iff rules cert.steps e

/-- Fail-closed: any out-of-range index forces rejection, independent of the expression. -/
theorem replayCert_eq_none_of_oob {rules : List VerifiedExprRule} {cert : RewriteCert}
    {i : Nat} (hi : i ∈ cert.steps) (hoob : rules.length ≤ i) (e : LNIRExpr) :
    replayCert rules cert e = none := by
  cases h : replayCert rules cert e with
  | none => rfl
  | some e' =>
    have hs : (replayCert rules cert e).isSome = true := by
      rw [h]
      rfl
    have hlt := (replayCert_isSome_iff rules cert e).mp hs i hi
    exact absurd hlt (Nat.not_lt.mpr hoob)

/-- Lift a checked certificate to a `VerifiedExprRule`; a rejected replay leaves `e` unchanged. -/
def rewriteCertRule (rules : List VerifiedExprRule) (cert : RewriteCert) : VerifiedExprRule where
  name := "rewriteCert"
  apply := fun e => (replayCert rules cert e).getD e
  sound := by
    intro e
    cases h : replayCert rules cert e with
    | none => exact ExprRefines.refl e
    | some e' => exact replayCert_sound h

theorem rewriteCertRule_sound (rules : List VerifiedExprRule) (cert : RewriteCert)
    (e : LNIRExpr) : ExprRefines e ((rewriteCertRule rules cert).apply e) :=
  (rewriteCertRule rules cert).sound e

/-- Apply a checked rewrite certificate to every `letBind` RHS across an `LNIRCode` tree. -/
def applyRewriteCertCode (rules : List VerifiedExprRule) (cert : RewriteCert)
    (code : LNIRCode) : LNIRCode :=
  applyRewriteTable [rewriteCertRule rules cert] code

/-- Code-level soundness of certificate replay over all 9 `LNIRCode` constructors. -/
theorem applyRewriteCertCode_sound (rules : List VerifiedExprRule) (cert : RewriteCert)
    (code : LNIRCode) : CodeRefines code (applyRewriteCertCode rules cert code) :=
  applyRewriteTable_sound [rewriteCertRule rules cert] code

/-! ## Concrete witnesses -/

/-- Top-level single-step scalar peephole rule (one `rewriteScalarPeepholeStep` per use). -/
def peepholeStepRule : VerifiedExprRule where
  name := "peepholeStep"
  apply := fun
    | .scalar s => .scalar (rewriteScalarPeepholeStep s)
    | other => other
  sound := by
    intro e
    cases e with
    | scalar s => exact ExprRefines.of_scalar_equiv (rewriteScalarPeepholeStep_sound s)
    | _ => exact ExprRefines.refl _

/-- Full recursive scalar peephole rule. -/
def peepholeFullRule : VerifiedExprRule where
  name := "peepholeFull"
  apply := rewriteLNIRExpr
  sound := rewriteLNIRExpr_sound

def witnessRules : List VerifiedExprRule := [peepholeStepRule, peepholeFullRule]

/-- `(x * 1) + 0` -/
def witnessSrc : LNIRExpr :=
  .scalar (.binOp .add (.binOp .mul (.var 7) (.constU64 1)) (.constU64 0))

-- Valid two-step certificate: `(x * 1) + 0 → x * 1 → x`.
#guard replayCert witnessRules ⟨[0, 0]⟩ witnessSrc == some (.scalar (.var 7))
-- A single step only peels the outer `+ 0`.
#guard replayCert witnessRules ⟨[0]⟩ witnessSrc ==
  some (.scalar (.binOp .mul (.var 7) (.constU64 1)))
-- Mixed rule indices also replay.
#guard replayCert witnessRules ⟨[0, 1]⟩ witnessSrc == some (.scalar (.var 7))
-- Empty certificate is the identity.
#guard replayCert witnessRules ⟨[]⟩ witnessSrc == some witnessSrc
-- Out-of-range index fails closed, even after valid prefix steps.
#guard (replayCert witnessRules ⟨[0, 2]⟩ witnessSrc).isNone
#guard (replayCert witnessRules ⟨[5]⟩ witnessSrc).isNone
#guard (replayCert [] ⟨[0]⟩ witnessSrc).isNone
-- Code-level lift: rejected certificate leaves the code unchanged.
#guard match applyRewriteCertCode witnessRules ⟨[9]⟩ (.letBind 1 .i64 witnessSrc (.ret 1)) with
  | .letBind _ _ v _ => v == witnessSrc
  | _ => false
-- Code-level lift: accepted certificate rewrites the `letBind` RHS.
#guard match applyRewriteCertCode witnessRules ⟨[0, 0]⟩ (.letBind 1 .i64 witnessSrc (.ret 1)) with
  | .letBind _ _ v _ => v == .scalar (.var 7)
  | _ => false

end LeanNative.Proofs
