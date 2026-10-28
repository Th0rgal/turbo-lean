import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.IR.LCNF
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics

/-!
# Machine-Checked LCNF-to-LNIR Bridge Soundness (`LeanNative.Proofs.LCNFBridgeProofs`)

Milestone M4 (Item 1): Proves `lowerLCNFCode_sound` (`0 sorryAx`, `Contract V2`) establishing
that whenever `LCNF.lowerCode c = .ok lnirCode` and `EnvCorresponds lcnfEnv lnirEnv`,
evaluating `c` under the independent `LCNF.evalLCNF` operational semantics produces the
exact same `(Val × HeapState)` outcome (including UB traps) as `evalCode` on `lnirCode`.
-/

/-- Pointwise correspondence between an LCNF free-variable environment and an LNIR `VarEnv`. -/
def EnvCorresponds (lcnfEnv : LCNF.Env) (lnirEnv : VarEnv) : Prop :=
  ∀ x : VarId, lcnfEnv x = lnirEnv x

/-- Re-export `LCNF.lowerCode` and `LCNF.evalLCNF` in `LeanNative.Proofs` for roadmap contract compatibility. -/
abbrev lowerCode : LCNF.Code → Except String LNIRCode := LCNF.lowerCode
abbrev evalLCNF : LCNF.Env → HeapState → LCNF.Code → Nat → Except UBError (Val × HeapState) := LCNF.evalLCNF

/-- Observational equivalence of evaluation outcomes (`Except UBError (Val × HeapState)`). -/
def EvalOutcomeEquiv (r1 r2 : Except UBError (Val × HeapState)) : Prop :=
  r1 = r2

infix:50 " ≈ " => EvalOutcomeEquiv

theorem envCorresponds_eq {lcnfEnv : LCNF.Env} {lnirEnv : VarEnv}
    (h : EnvCorresponds lcnfEnv lnirEnv) : lcnfEnv = lnirEnv :=
  funext h

theorem envCorresponds_bind {lcnfEnv : LCNF.Env} {lnirEnv : VarEnv}
    (h : EnvCorresponds lcnfEnv lnirEnv) (x : VarId) (v : Val) :
    EnvCorresponds (LCNF.Env.bind lcnfEnv x v) (lnirEnv.bind x v) := by
  intro y
  simp [LCNF.Env.bind, VarEnv.bind, h y]

/-- Soundness of `LCNF.lowerLetValue` with respect to `LCNF.evalLetValue` and `evalExpr`. -/
theorem lowerLetValue_sound (val : LCNF.LetValue) (expr : LNIRExpr)
    (env : VarEnv) (st : HeapState)
    (h_lv : LCNF.lowerLetValue val = .ok expr) :
    LCNF.evalLetValue env st val = evalExpr env st expr := by
  cases val with
  | litU64 n =>
    injection h_lv with heq; subst heq
    rfl
  | litBool b =>
    injection h_lv with heq; subst heq
    rfl
  | litU256 w =>
    injection h_lv with heq; subst heq
    rfl
  | fvar x =>
    injection h_lv with heq; subst heq
    dsimp [LCNF.evalLetValue, evalExpr, evalScalarExpr]
    cases env x <;> rfl
  | binOp op aVar bVar =>
    injection h_lv with heq; subst heq
    dsimp [LCNF.evalLetValue, evalExpr, evalScalarExpr]
    cases env aVar with
    | none => rfl
    | some va =>
      cases env bVar with
      | none => rfl
      | some vb =>
        cases evalBinOp op va vb <;> rfl
  | unaryOp op aVar =>
    injection h_lv with heq; subst heq
    dsimp [LCNF.evalLetValue, evalExpr, evalScalarExpr]
    cases env aVar with
    | none => rfl
    | some va =>
      cases evalUnaryOp op va <;> rfl
  | mkPair aVar bVar =>
    injection h_lv with heq; subst heq
    dsimp [LCNF.evalLetValue, evalExpr, evalVarList]
    cases env aVar with
    | none => rfl
    | some va =>
      cases env bVar with
      | none => rfl
      | some vb => rfl
  | projTuple tupleVar idx =>
    injection h_lv with heq; subst heq
    rfl
  | sarrayLen arrVar =>
    injection h_lv with heq; subst heq
    rfl
  | sarrayGet arrVar idxVar elemTy =>
    injection h_lv with heq; subst heq
    rfl
  | sarraySet arrVar idxVar valVar elemTy =>
    injection h_lv with heq; subst heq
    rfl
  | unsupportedCall fnName =>
    simp [LCNF.lowerLetValue] at h_lv

/-- Milestone M4 (Item 1): Machine-checked LCNF-to-LNIR bridge soundness (`lowerLCNFCode_sound`).
    Proved by structural induction on `c : LCNF.Code` against the independent `LCNF.evalLCNF`
    operational semantics (`0 sorryAx`). -/
theorem lowerLCNFCode_sound (c : LCNF.Code) (lnirCode : LNIRCode)
    (lcnfEnv : LCNF.Env) (lnirEnv : VarEnv) (st : HeapState) (fuel : Nat)
    (h_env : EnvCorresponds lcnfEnv lnirEnv)
    (h_lower : lowerCode c = .ok lnirCode) :
    evalLCNF lcnfEnv st c fuel ≈ evalCode fuel lnirEnv st lnirCode := by
  unfold EvalOutcomeEquiv evalLCNF lowerCode at *
  induction c generalizing lnirCode lcnfEnv lnirEnv st with
  | letBind dst ty val k ih =>
    dsimp [LCNF.lowerCode] at h_lower
    cases hlv : LCNF.lowerLetValue val with
    | error err =>
      rw [hlv] at h_lower
      contradiction
    | ok expr =>
      rw [hlv] at h_lower
      cases hk : LCNF.lowerCode k with
      | error err =>
        rw [hk] at h_lower
        contradiction
      | ok k' =>
        rw [hk] at h_lower
        injection h_lower with heq
        subst heq
        have henv_eq := envCorresponds_eq h_env
        subst henv_eq
        dsimp [LCNF.evalLCNF, evalCode]
        rw [lowerLetValue_sound val expr lcnfEnv st hlv]
        cases evalExpr lcnfEnv st expr with
        | error _ => rfl
        | ok pair =>
          exact ih k' (LCNF.Env.bind lcnfEnv dst pair.1) (lcnfEnv.bind dst pair.1) pair.2
            (envCorresponds_bind h_env dst pair.1) hk
  | inc objVar count k ih =>
    dsimp [LCNF.lowerCode] at h_lower
    cases hk : LCNF.lowerCode k with
    | error err =>
      rw [hk] at h_lower
      contradiction
    | ok k' =>
      rw [hk] at h_lower
      injection h_lower with heq
      subst heq
      have henv_eq := envCorresponds_eq h_env
      subst henv_eq
      dsimp [LCNF.evalLCNF, evalCode]
      cases st.evalIncRef lcnfEnv objVar count with
      | error _ => rfl
      | ok st' => exact ih k' lcnfEnv lcnfEnv st' h_env hk
  | dec objVar count k ih =>
    dsimp [LCNF.lowerCode] at h_lower
    cases hk : LCNF.lowerCode k with
    | error err =>
      rw [hk] at h_lower
      contradiction
    | ok k' =>
      rw [hk] at h_lower
      injection h_lower with heq
      subst heq
      have henv_eq := envCorresponds_eq h_env
      subst henv_eq
      dsimp [LCNF.evalLCNF, evalCode]
      cases st.evalDecRef lcnfEnv objVar count with
      | error _ => rfl
      | ok st' => exact ih k' lcnfEnv lcnfEnv st' h_env hk
  | casesBool discr falseBranch trueBranch ihf iht =>
    dsimp [LCNF.lowerCode] at h_lower
    cases hfb : LCNF.lowerCode falseBranch with
    | error err =>
      rw [hfb] at h_lower
      contradiction
    | ok fb' =>
      rw [hfb] at h_lower
      cases htb : LCNF.lowerCode trueBranch with
      | error err =>
        rw [htb] at h_lower
        contradiction
      | ok tb' =>
        rw [htb] at h_lower
        injection h_lower with heq
        subst heq
        have henv_eq := envCorresponds_eq h_env
        subst henv_eq
        dsimp [LCNF.evalLCNF, evalCode]
        cases lcnfEnv discr with
        | none => rfl
        | some cval =>
          cases cval with
          | bool b =>
            cases b with
            | false => exact ihf fb' lcnfEnv lcnfEnv st h_env hfb
            | true => exact iht tb' lcnfEnv lcnfEnv st h_env htb
          | u64 n =>
            simp only
            split
            · exact iht tb' lcnfEnv lcnfEnv st h_env htb
            · exact ihf fb' lcnfEnv lcnfEnv st h_env hfb
          | u256 w =>
            simp only
            split
            · exact iht tb' lcnfEnv lcnfEnv st h_env htb
            · exact ihf fb' lcnfEnv lcnfEnv st h_env hfb
          | _ => rfl
  | «return» v =>
    dsimp [LCNF.lowerCode] at h_lower
    injection h_lower with heq
    subst heq
    have henv_eq := envCorresponds_eq h_env
    subst henv_eq
    rfl
  | unreach =>
    dsimp [LCNF.lowerCode] at h_lower
    injection h_lower with heq
    subst heq
    rfl

end LeanNative.Proofs
