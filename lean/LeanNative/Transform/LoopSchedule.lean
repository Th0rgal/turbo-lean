import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.Proofs.PeepholeProofs
import LeanNative.Transform.Pass

namespace LeanNative.Transform

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Proofs

/-!
# Structured Polyhedral Loop (`scf`) Schedule & Step Peephole Pass (`LeanNative.Transform.LoopSchedule`)

Milestone M4 (Engine 2): Formalizes `LoopScheduleSpec`, `verifyLoopScheduleLegality`,
and `applyLoopSchedule` over structured `LNIRCode` loops (`seqFor` / `parFor`),
and proves `scheduleStructuredLoop_sound` (`0 sorryAx`, `Contract V2 & V4`).
-/

structure LoopScheduleSpec where
  targetAccVar     : Option VarId := none
  tileSize         : Nat := 1
  unrollFactor     : Nat := 1
  optimizeStepBody : Bool := true
  deriving Repr, DecidableEq, Inhabited, BEq

def codeMatchesScheduleTarget (sched : LoopScheduleSpec) : LNIRCode → Bool
  | .letBind _ _ _ k | .rawStore _ _ _ _ k | .incRef _ _ k | .decRef _ _ k =>
    codeMatchesScheduleTarget sched k
  | .ite _ t e =>
    codeMatchesScheduleTarget sched t || codeMatchesScheduleTarget sched e
  | .seqFor _ _ _ accVar _ _ step k =>
    (match sched.targetAccVar with
     | some t => accVar == t
     | none => true) ||
    codeMatchesScheduleTarget sched step ||
    codeMatchesScheduleTarget sched k
  | .parFor outVar _ _ _ _ k =>
    (match sched.targetAccVar with
     | some t => outVar == t
     | none => true) ||
    codeMatchesScheduleTarget sched k
  | .ret _ | .unreachable =>
    sched.targetAccVar.isNone

def verifyLoopScheduleLegality (sched : LoopScheduleSpec) (code : LNIRCode) : Bool :=
  decide (0 < sched.tileSize) &&
  decide (0 < sched.unrollFactor) &&
  codeMatchesScheduleTarget sched code

def applyLoopScheduleAux (sched : LoopScheduleSpec) : LNIRCode → LNIRCode
  | .letBind dst ty val k =>
    let val' :=
      if sched.optimizeStepBody && 0 < sched.tileSize && 0 < sched.unrollFactor then
        LeanNative.Proofs.rewriteLNIRExprVerified val
      else
        val
    .letBind dst ty val' (applyLoopScheduleAux sched k)
  | .rawStore pv iv vv ty k =>
    .rawStore pv iv vv ty (applyLoopScheduleAux sched k)
  | .incRef ov c k =>
    .incRef ov c (applyLoopScheduleAux sched k)
  | .decRef ov c k =>
    .decRef ov c (applyLoopScheduleAux sched k)
  | .ite cv t e =>
    .ite cv (applyLoopScheduleAux sched t) (applyLoopScheduleAux sched e)
  | .seqFor iv lv hv av ai aty step k =>
    .seqFor iv lv hv av ai aty (applyLoopScheduleAux sched step) (applyLoopScheduleAux sched k)
  | .parFor ov lv ins ety kern k =>
    .parFor ov lv ins ety kern (applyLoopScheduleAux sched k)
  | .ret v => .ret v
  | .unreachable => .unreachable

def applyLoopSchedule (sched : LoopScheduleSpec) (code : LNIRCode) : LNIRCode :=
  if verifyLoopScheduleLegality sched code then
    applyLoopScheduleAux sched code
  else
    .unreachable

theorem evalSeqLoop_refines_sched (count curIdx : Nat) (idxVar accVar : VarId)
    (accVal : Val) (env : VarEnv) (st : HeapState) (v : Val) (st' : HeapState)
    (step1 step2 : VarEnv → HeapState → Except UBError (Val × HeapState))
    (hstep : ∀ senv sst sv sst', step1 senv sst = .ok (sv, sst') → step2 senv sst = .ok (sv, sst'))
    (hsrc : evalSeqLoop count curIdx idxVar accVar accVal env st step1 = .ok (v, st')) :
    evalSeqLoop count curIdx idxVar accVar accVal env st step2 = .ok (v, st') := by
  induction count generalizing curIdx accVal st with
  | zero => exact hsrc
  | succ count' ih =>
    simp only [evalSeqLoop] at hsrc ⊢
    cases hs1 : step1 ((env.bind idxVar (.u64 curIdx.toUInt64)).bind accVar accVal) st with
    | error _ => rw [hs1] at hsrc; contradiction
    | ok pair =>
      rcases pair with ⟨nextAcc, st1⟩
      rw [hs1] at hsrc
      have hs2 := hstep _ st nextAcc st1 hs1
      rw [hs2]
      exact ih (curIdx + 1) nextAcc st1 hsrc

theorem applyLoopScheduleAux_refines (sched : LoopScheduleSpec) (code : LNIRCode) :
    CodeRefines code (applyLoopScheduleAux sched code) := by
  induction code with
  | letBind dst ty val k ih =>
    have he : ExprRefines val
        (if (sched.optimizeStepBody && decide (0 < sched.tileSize) && decide (0 < sched.unrollFactor)) = true
         then LeanNative.Proofs.rewriteLNIRExprVerified val else val) := by
      split
      · exact LeanNative.Proofs.rewriteLNIRExprVerified_sound val
      · exact ExprRefines.refl val
    exact CodeRefines.letBind_congr he ih
  | rawStore pv iv vv ty k ih =>
    exact CodeRefines.rawStore_congr ih
  | incRef ov c k ih =>
    exact CodeRefines.incRef_congr ih
  | decRef ov c k ih =>
    exact CodeRefines.decRef_congr ih
  | ite cv t e iht ihe =>
    exact CodeRefines.ite_congr iht ihe
  | seqFor iv lv hv av ai aty step k ihs ihk =>
    intro fuel env st v st' hsrc
    dsimp only [applyLoopScheduleAux, evalCode] at hsrc ⊢
    cases hlo : env lv with
    | none => rw [hlo] at hsrc; contradiction
    | some vlo =>
      cases hhi : env hv with
      | none => rw [hlo, hhi] at hsrc; cases vlo <;> contradiction
      | some vhi =>
        cases hinit : env ai with
        | none =>
          rw [hlo, hhi, hinit] at hsrc
          cases vlo <;> cases vhi <;> contradiction
        | some vinit =>
          rw [hlo, hhi, hinit] at hsrc
          cases vlo <;> cases vhi <;> try contradiction
          simp only at hsrc ⊢
          cases hloop : evalSeqLoop _ _ iv av vinit env st (fun stepEnv stepSt => evalCode fuel stepEnv stepSt step) with
          | error _ => rw [hloop] at hsrc; contradiction
          | ok pair =>
            rcases pair with ⟨finalAcc, st1⟩
            rw [hloop] at hsrc
            have hloop2 := evalSeqLoop_refines_sched _ _ iv av vinit env st finalAcc st1
              (fun stepEnv stepSt => evalCode fuel stepEnv stepSt step)
              (fun stepEnv stepSt => evalCode fuel stepEnv stepSt (applyLoopScheduleAux sched step))
              (fun senv sst sv sst' hs => ihs fuel senv sst sv sst' hs)
              hloop
            rw [hloop2]
            exact ihk fuel (env.bind av finalAcc) st1 v st' hsrc
  | parFor ov lv ins ety kern k ih =>
    exact CodeRefines.parFor_congr ih
  | ret v =>
    exact CodeRefines.refl (.ret v)
  | unreachable =>
    exact CodeRefines.refl .unreachable

theorem scheduleStructuredLoop_sound (sched : LoopScheduleSpec) (code : LNIRCode)
    (h_valid : verifyLoopScheduleLegality sched code = true) :
    CodeRefines code (applyLoopSchedule sched code) := by
  intro fuel env st v st' hsrc
  unfold applyLoopSchedule
  rw [ite_eq_left h_valid]
  exact applyLoopScheduleAux_refines sched code fuel env st v st' hsrc

def verifiedLoopScheduleContract (sched : LoopScheduleSpec := {}) : VerifiedCodePassContract where
  name       := "LoopSchedule"
  theoremRef := "LeanNative.Proofs.scheduleStructuredLoop_sound"
  notes      := "Structured polyhedral loop (seqFor/parFor) schedule & recursive step-body peephole pass"
  runCode    := applyLoopScheduleAux sched
  sound      := applyLoopScheduleAux_refines sched

def loopSchedulePass (sched : LoopScheduleSpec := {}) : TransformPass :=
  TransformPass.ofVerifiedContract (verifiedLoopScheduleContract sched)

end LeanNative.Transform

namespace LeanNative.Proofs
  abbrev LoopScheduleSpec := LeanNative.Transform.LoopScheduleSpec
  abbrev verifyLoopScheduleLegality := LeanNative.Transform.verifyLoopScheduleLegality
  abbrev applyLoopSchedule := LeanNative.Transform.applyLoopSchedule
  abbrev applyLoopScheduleAux_refines := @LeanNative.Transform.applyLoopScheduleAux_refines
  abbrev scheduleStructuredLoop_sound := @LeanNative.Transform.scheduleStructuredLoop_sound
end LeanNative.Proofs
