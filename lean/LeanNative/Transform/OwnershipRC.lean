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
  unfold HeapState.decRefObj HeapState.decRefObjFuel at h
  by_cases h0 : st.getObjRefCount objId = 0 <;> simp_all

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

/-- Drop `incRef`/`decRef` on `v` and replace `lean_mark_mt` calls by a scalar zero.
    Sound only for environments where `v` is non-owning; the verified contract below keeps
    the unconditionally refining fragment (zero-delta RC plus `lean_mark_mt` deletion). -/
def elideBorrowedAndThreadLocalRC (v : VarId) (code : LNIRCode) : LNIRCode :=
  match code with
  | .letBind dst ty val k =>
    match val with
    | .call fn args rty ext =>
      if fn == "lean_mark_mt" then
        .letBind dst ty (.scalar (.constU64 0)) (elideBorrowedAndThreadLocalRC v k)
      else
        .letBind dst ty (.call fn args rty ext) (elideBorrowedAndThreadLocalRC v k)
    | other =>
      .letBind dst ty other (elideBorrowedAndThreadLocalRC v k)
  | .rawStore pv iv vv ty k =>
    .rawStore pv iv vv ty (elideBorrowedAndThreadLocalRC v k)
  | .incRef ov c k =>
    if ov == v || c == 0 then elideBorrowedAndThreadLocalRC v k
    else .incRef ov c (elideBorrowedAndThreadLocalRC v k)
  | .decRef ov c k =>
    if ov == v || c == 0 then elideBorrowedAndThreadLocalRC v k
    else .decRef ov c (elideBorrowedAndThreadLocalRC v k)
  | .ite cv t e =>
    .ite cv (elideBorrowedAndThreadLocalRC v t) (elideBorrowedAndThreadLocalRC v e)
  | .seqFor iv lv hv av ai aty step k =>
    .seqFor iv lv hv av ai aty (elideBorrowedAndThreadLocalRC v step) (elideBorrowedAndThreadLocalRC v k)
  | .parFor ov lv ins ety kern k =>
    .parFor ov lv ins ety kern (elideBorrowedAndThreadLocalRC v k)
  | .ret r => .ret r
  | .unreachable => .unreachable

/-- Unconditionally `CodeRefines` fragment: delete `lean_mark_mt` lets and zero-delta RC. -/
def elideMarkMtAndZeroRc (code : LNIRCode) : LNIRCode :=
  match code with
  | .letBind dst ty val k =>
    match val with
    | .call fn args rty ext =>
      if fn == "lean_mark_mt" then elideMarkMtAndZeroRc k
      else .letBind dst ty (.call fn args rty ext) (elideMarkMtAndZeroRc k)
    | other => .letBind dst ty other (elideMarkMtAndZeroRc k)
  | .rawStore pv iv vv ty k => .rawStore pv iv vv ty (elideMarkMtAndZeroRc k)
  | .incRef ov c k =>
    if c == 0 then elideMarkMtAndZeroRc k else .incRef ov c (elideMarkMtAndZeroRc k)
  | .decRef ov c k =>
    if c == 0 then elideMarkMtAndZeroRc k else .decRef ov c (elideMarkMtAndZeroRc k)
  | .ite cv t e => .ite cv (elideMarkMtAndZeroRc t) (elideMarkMtAndZeroRc e)
  | .seqFor iv lv hv av ai aty step k =>
    .seqFor iv lv hv av ai aty (elideMarkMtAndZeroRc step) (elideMarkMtAndZeroRc k)
  | .parFor ov lv ins ety kern k => .parFor ov lv ins ety kern (elideMarkMtAndZeroRc k)
  | .ret r => .ret r
  | .unreachable => .unreachable

theorem markMt_eval_error (env : VarEnv) (st : HeapState) (args : List VarId) (retTy : LNIRType)
    (ext : Bool) (vals : List Val) (hargs : evalVarList env args = .ok vals) :
    evalExpr env st (.call "lean_mark_mt" args retTy ext) = .error (.unsupportedCall "lean_mark_mt") := by
  simp only [evalExpr, hargs]
  have hbox : ("lean_mark_mt" == "lean_native_box_u64") = false := by decide
  have hunbox : ("lean_mark_mt" == "lean_native_unbox_u64") = false := by decide
  have hexcl : ("lean_mark_mt" == "lean_native_ensure_exclusive") = false := by decide
  have hlen : ("lean_mark_mt" == "lean_native_sarray_len") = false := by decide
  have hset : ("lean_mark_mt" == "lean_native_ctor_set") = false := by decide
  have hsets : ("lean_mark_mt" == "lean_native_ctor_set_scalar") = false := by decide
  have htag : ("lean_mark_mt" == "lean_native_ctor_set_tag") = false := by decide
  have hdel : ("lean_mark_mt" == "lean_native_del_obj") = false := by decide
  have hctag : ("lean_mark_mt" == "lean_native_ctor_tag") = false := by decide
  cases ext <;>
    simp [hbox, hunbox, hexcl, hlen, hset, hsets, htag, hdel, hctag]

theorem elideMarkMtAndZeroRc_sound (code : LNIRCode) :
    CodeRefines code (elideMarkMtAndZeroRc code) := by
  induction code with
  | letBind dst ty val k ih =>
    cases val with
    | call fn args retTy ext =>
      by_cases hmt : (fn == "lean_mark_mt") = true
      · have hfn : fn = "lean_mark_mt" := of_decide_eq_true hmt
        subst hfn
        intro fuel env st v st' hsrc
        dsimp only [elideMarkMtAndZeroRc]
        simp only [beq_self_eq_true, ↓reduceIte]
        dsimp only [evalCode] at hsrc
        cases hargs : evalVarList env args with
        | error err => simp [evalExpr, hargs] at hsrc
        | ok vals =>
          rw [markMt_eval_error env st args retTy ext vals hargs] at hsrc
          contradiction
      · dsimp only [elideMarkMtAndZeroRc]
        rw [ite_eq_right hmt]
        exact CodeRefines.letBind_congr (ExprRefines.refl _) ih
    | scalar e => exact CodeRefines.letBind_congr (ExprRefines.refl (.scalar e)) ih
    | constU256 w => exact CodeRefines.letBind_congr (ExprRefines.refl (.constU256 w)) ih
    | mulDivDown a b d => exact CodeRefines.letBind_congr (ExprRefines.refl (.mulDivDown a b d)) ih
    | mulDivUp a b d => exact CodeRefines.letBind_congr (ExprRefines.refl (.mulDivUp a b d)) ih
    | storageLoad a b => exact CodeRefines.letBind_congr (ExprRefines.refl (.storageLoad a b)) ih
    | storageStore a b c => exact CodeRefines.letBind_congr (ExprRefines.refl (.storageStore a b c)) ih
    | mkTuple fs => exact CodeRefines.letBind_congr (ExprRefines.refl (.mkTuple fs)) ih
    | projTuple a i => exact CodeRefines.letBind_congr (ExprRefines.refl (.projTuple a i)) ih
    | allocCtor t o s => exact CodeRefines.letBind_congr (ExprRefines.refl (.allocCtor t o s)) ih
    | ctorGetObj a i => exact CodeRefines.letBind_congr (ExprRefines.refl (.ctorGetObj a i)) ih
    | ctorGetScalar a i t => exact CodeRefines.letBind_congr (ExprRefines.refl (.ctorGetScalar a i t)) ih
    | isExclusive a => exact CodeRefines.letBind_congr (ExprRefines.refl (.isExclusive a)) ih
    | sarrayLen a => exact CodeRefines.letBind_congr (ExprRefines.refl (.sarrayLen a)) ih
    | sarrayDataPtr a t => exact CodeRefines.letBind_congr (ExprRefines.refl (.sarrayDataPtr a t)) ih
    | sarrayEnsureExclusive a t =>
      exact CodeRefines.letBind_congr (ExprRefines.refl (.sarrayEnsureExclusive a t)) ih
    | sarrayGet a i t => exact CodeRefines.letBind_congr (ExprRefines.refl (.sarrayGet a i t)) ih
    | sarraySet a i x t => exact CodeRefines.letBind_congr (ExprRefines.refl (.sarraySet a i x t)) ih
    | rawLoad a i t => exact CodeRefines.letBind_congr (ExprRefines.refl (.rawLoad a i t)) ih
    | boxScalar a t => exact CodeRefines.letBind_congr (ExprRefines.refl (.boxScalar a t)) ih
    | unboxScalar a t => exact CodeRefines.letBind_congr (ExprRefines.refl (.unboxScalar a t)) ih
  | rawStore pv iv vv ty k ih => exact CodeRefines.rawStore_congr ih
  | incRef ov c k ih =>
    dsimp only [elideMarkMtAndZeroRc]
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
    dsimp only [elideMarkMtAndZeroRc]
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
  | ite cv t e iht ihe => exact CodeRefines.ite_congr iht ihe
  | seqFor iv lv hv av ai aty step k ihs ihk =>
    intro fuel env st v st' hsrc
    dsimp only [elideMarkMtAndZeroRc, evalCode] at hsrc ⊢
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
          cases hloop : evalSeqLoop _ _ iv av vinit env st
              (fun stepEnv stepSt => evalCode fuel stepEnv stepSt step) with
          | error _ => rw [hloop] at hsrc; contradiction
          | ok pair =>
            rcases pair with ⟨finalAcc, st1⟩
            rw [hloop] at hsrc
            have hloop2 := evalSeqLoop_refines_rc _ _ iv av vinit env st finalAcc st1
              (fun stepEnv stepSt => evalCode fuel stepEnv stepSt step)
              (fun stepEnv stepSt => evalCode fuel stepEnv stepSt (elideMarkMtAndZeroRc step))
              (fun senv sst sv sst' hs => ihs fuel senv sst sv sst' hs) hloop
            rw [hloop2]
            exact ihk fuel (env.bind av finalAcc) st1 v st' hsrc
  | parFor ov lv ins ety kern k ih => exact CodeRefines.parFor_congr ih
  | ret r => exact CodeRefines.refl (.ret r)
  | unreachable => exact CodeRefines.refl .unreachable

def verifiedThreadLocalRCContract : VerifiedCodePassContract where
  name       := "ThreadLocalRC"
  theoremRef := "LeanNative.Proofs.elideMarkMtAndZeroRc_sound"
  notes      := "Delete unsupported lean_mark_mt and zero-delta incRef/decRef"
  runCode    := elideMarkMtAndZeroRc
  sound      := elideMarkMtAndZeroRc_sound

end LeanNative.Transform

namespace LeanNative.Proofs
  abbrev CodeRefinesWithRC := LeanNative.Transform.CodeRefinesWithRC
  abbrev optimizeOwnershipRC := LeanNative.Transform.optimizeOwnershipRC
  abbrev elideAndMutateRC_sound := @LeanNative.Transform.elideAndMutateRC_sound
  abbrev elideBorrowedAndThreadLocalRC := LeanNative.Transform.elideBorrowedAndThreadLocalRC
  abbrev elideMarkMtAndZeroRc := LeanNative.Transform.elideMarkMtAndZeroRc
  abbrev elideMarkMtAndZeroRc_sound := @LeanNative.Transform.elideMarkMtAndZeroRc_sound
end LeanNative.Proofs
