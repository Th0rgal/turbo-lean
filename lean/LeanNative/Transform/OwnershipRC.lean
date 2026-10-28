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
# Ownership / Reference-Counting (`incRef`/`decRef`) Elision & Peephole Pass (`LeanNative.Transform.OwnershipRC`)

Milestone M4 (Engine 3): Formalizes `optimizeOwnershipRC`, proves that zero-delta reference-count
operations (`incRef v 0`, `decRef v 0`) preserve heap state whenever defined (while catching
`unboundVar` and `useAfterFree` in the source semantics), and proves `elideAndMutateRC_sound`
(`0 sorryAx`, `Contract V2`).
-/

theorem incRefBuf_zero_ok (st st1 : HeapState) (bufId : Nat)
    (h : st.incRefBuf bufId 0 = .ok st1) : st1 = st := by
  unfold HeapState.incRefBuf at h
  cases hfind : st.findBuffer bufId with
  | none =>
    rw [hfind] at h
    contradiction
  | some buf =>
    rw [hfind] at h
    injection h with heq
    exact heq.symm

theorem decRefBuf_zero_ok (st st1 : HeapState) (bufId : Nat)
    (h : st.decRefBuf bufId 0 = .ok st1) : st1 = st := by
  unfold HeapState.decRefBuf at h
  cases hfind : st.findBuffer bufId with
  | none =>
    rw [hfind] at h
    contradiction
  | some buf =>
    rw [hfind] at h
    injection h with heq
    exact heq.symm

theorem incRefObj_zero_ok (st st1 : HeapState) (objId : Nat)
    (h : st.incRefObj objId 0 = .ok st1) : st1 = st := by
  unfold HeapState.incRefObj at h
  dsimp only at h
  split at h
  · contradiction
  · injection h with heq
    exact heq.symm

theorem decRefObj_zero_ok (st st1 : HeapState) (objId : Nat)
    (h : st.decRefObj objId 0 = .ok st1) : st1 = st := by
  unfold HeapState.decRefObj at h
  dsimp only at h
  split at h
  · contradiction
  · injection h with heq
    exact heq.symm

theorem evalIncRef_zero_ok (st st1 : HeapState) (env : VarEnv) (objVar : VarId)
    (h : st.evalIncRef env objVar 0 = .ok st1) : st1 = st := by
  unfold HeapState.evalIncRef at h
  cases hv : env objVar with
  | none =>
    rw [hv] at h
    contradiction
  | some val =>
    rw [hv] at h
    cases val with
    | sarrayId bufId => exact incRefBuf_zero_ok st st1 bufId h
    | objPtr objId => exact incRefObj_zero_ok st st1 objId h
    | _ =>
      injection h with heq
      exact heq.symm

theorem evalDecRef_zero_ok (st st1 : HeapState) (env : VarEnv) (objVar : VarId)
    (h : st.evalDecRef env objVar 0 = .ok st1) : st1 = st := by
  unfold HeapState.evalDecRef at h
  cases hv : env objVar with
  | none =>
    rw [hv] at h
    contradiction
  | some val =>
    rw [hv] at h
    cases val with
    | sarrayId bufId => exact decRefBuf_zero_ok st st1 bufId h
    | objPtr objId => exact decRefObj_zero_ok st st1 objId h
    | _ =>
      injection h with heq
      exact heq.symm

def optimizeOwnershipRC : LNIRCode → LNIRCode
  | .letBind dst ty val k =>
    .letBind dst ty (LeanNative.Proofs.rewriteLNIRExprVerified val) (optimizeOwnershipRC k)
  | .rawStore pv iv vv ty k =>
    .rawStore pv iv vv ty (optimizeOwnershipRC k)
  | .incRef ov c k =>
    if c == 0 then
      optimizeOwnershipRC k
    else
      .incRef ov c (optimizeOwnershipRC k)
  | .decRef ov c k =>
    if c == 0 then
      optimizeOwnershipRC k
    else
      .decRef ov c (optimizeOwnershipRC k)
  | .ite cv t e =>
    .ite cv (optimizeOwnershipRC t) (optimizeOwnershipRC e)
  | .seqFor iv lv hv av ai aty step k =>
    .seqFor iv lv hv av ai aty (optimizeOwnershipRC step) (optimizeOwnershipRC k)
  | .parFor ov lv ins ety kern k =>
    .parFor ov lv ins ety kern (optimizeOwnershipRC k)
  | .ret v => .ret v
  | .unreachable => .unreachable

theorem evalSeqLoop_refines_rc (count curIdx : Nat) (idxVar accVar : VarId)
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

def CodeRefinesWithRC (src tgt : LNIRCode) : Prop :=
  CodeRefines src tgt

theorem elideAndMutateRC_sound (code : LNIRCode) :
    CodeRefinesWithRC code (optimizeOwnershipRC code) := by
  unfold CodeRefinesWithRC
  induction code with
  | letBind dst ty val k ih =>
    exact CodeRefines.letBind_congr (LeanNative.Proofs.rewriteLNIRExprVerified_sound val) ih
  | rawStore pv iv vv ty k ih =>
    exact CodeRefines.rawStore_congr ih
  | incRef ov c k ih =>
    dsimp only [optimizeOwnershipRC]
    by_cases hc : (c == 0) = true
    · rw [ite_eq_left hc]
      have hc0 : c = 0 := of_decide_eq_true hc
      subst hc0
      intro fuel env st v st' hsrc
      dsimp only [evalCode] at hsrc
      cases hinc : st.evalIncRef env ov 0 with
      | error _ => rw [hinc] at hsrc; contradiction
      | ok st1 =>
        rw [hinc] at hsrc
        have hst : st1 = st := evalIncRef_zero_ok st st1 env ov hinc
        subst hst
        exact ih fuel env st1 v st' hsrc
    · rw [ite_eq_right hc]
      exact CodeRefines.incRef_congr ih
  | decRef ov c k ih =>
    dsimp only [optimizeOwnershipRC]
    by_cases hc : (c == 0) = true
    · rw [ite_eq_left hc]
      have hc0 : c = 0 := of_decide_eq_true hc
      subst hc0
      intro fuel env st v st' hsrc
      dsimp only [evalCode] at hsrc
      cases hdec : st.evalDecRef env ov 0 with
      | error _ => rw [hdec] at hsrc; contradiction
      | ok st1 =>
        rw [hdec] at hsrc
        have hst : st1 = st := evalDecRef_zero_ok st st1 env ov hdec
        subst hst
        exact ih fuel env st1 v st' hsrc
    · rw [ite_eq_right hc]
      exact CodeRefines.decRef_congr ih
  | ite cv t e iht ihe =>
    exact CodeRefines.ite_congr iht ihe
  | seqFor iv lv hv av ai aty step k ihs ihk =>
    intro fuel env st v st' hsrc
    dsimp only [optimizeOwnershipRC, evalCode] at hsrc ⊢
    cases hlo : env lv with
    | none => rw [hlo] at hsrc; contradiction
    | some vlo =>
      cases hhi : env hv with
      | none => rw [hlo, hhi] at hsrc; cases vlo <;> contradiction
      | some vhi =>
        cases hinit : env ai with
        | none => rw [hlo, hhi, hinit] at hsrc; cases vlo <;> cases vhi <;> contradiction
        | some vinit =>
          rw [hlo, hhi, hinit] at hsrc
          cases vlo <;> cases vhi <;> try contradiction
          simp only at hsrc ⊢
          cases hloop : evalSeqLoop _ _ iv av vinit env st (fun stepEnv stepSt => evalCode fuel stepEnv stepSt step) with
          | error _ => rw [hloop] at hsrc; contradiction
          | ok pair =>
            rcases pair with ⟨finalAcc, st1⟩
            rw [hloop] at hsrc
            have hloop2 := evalSeqLoop_refines_rc _ _ iv av vinit env st finalAcc st1
              (fun stepEnv stepSt => evalCode fuel stepEnv stepSt step)
              (fun stepEnv stepSt => evalCode fuel stepEnv stepSt (optimizeOwnershipRC step))
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

def verifiedOwnershipRCContract : VerifiedCodePassContract where
  name       := "OwnershipRC"
  theoremRef := "LeanNative.Proofs.elideAndMutateRC_sound"
  notes      := "Zero-delta incRef/decRef elision & verified expression peephole pass"
  runCode    := optimizeOwnershipRC
  sound      := elideAndMutateRC_sound

def ownershipRCPass : TransformPass :=
  TransformPass.ofVerifiedContract verifiedOwnershipRCContract

end LeanNative.Transform

namespace LeanNative.Proofs
  abbrev CodeRefinesWithRC := LeanNative.Transform.CodeRefinesWithRC
  abbrev optimizeOwnershipRC := LeanNative.Transform.optimizeOwnershipRC
  abbrev elideAndMutateRC_sound := @LeanNative.Transform.elideAndMutateRC_sound
end LeanNative.Proofs
