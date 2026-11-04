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

/-- Drop `incRef`/`decRef` on `v` and replace non-escaping `lean_mark_mt` calls by scalar zero.
    Sound on non-owning `v` (`elideBorrowedAndThreadLocalRC_sound`) and unconditionally `CodeRefines`
    on escape-gated `lean_mark_mt` + zero-delta RC (`optimizeThreadLocalOwnershipRC_sound`). -/
def valIsNonOwning (val : Val) : Bool :=
  match val with
  | .sarrayId _ | .objPtr _ => false
  | _ => true

def tlScalarMentions (aliases : List VarId) (se : ScalarExpr) : Bool :=
  match se with
  | .constU64 _ | .constBool _ => false
  | .var id => aliases.contains id
  | .binOp _ l r => tlScalarMentions aliases l || tlScalarMentions aliases r
  | .unaryOp _ a => tlScalarMentions aliases a
  | .select c t e =>
    tlScalarMentions aliases c || tlScalarMentions aliases t || tlScalarMentions aliases e
  | .fma a b c =>
    tlScalarMentions aliases a || tlScalarMentions aliases b || tlScalarMentions aliases c

def tlExprMayAlias (aliases : List VarId) (e : LNIRExpr) : Bool :=
  match e with
  | .scalar se => tlScalarMentions aliases se
  | .boxScalar v _ | .unboxScalar v _ | .projTuple v _ | .ctorGetObj v _
  | .ctorGetScalar v _ _ | .sarrayDataPtr v _ | .sarrayEnsureExclusive v _ =>
    aliases.contains v
  | .mkTuple vs => vs.any aliases.contains
  | .allocCtor _ os ss => os.any aliases.contains || ss.any aliases.contains
  | .sarraySet a _ v _ | .storageStore a _ v => aliases.contains a || aliases.contains v
  | .call fn args _ isExtern =>
    !isExtern &&
      (fn == "lean_native_ensure_exclusive" || fn == "lean_native_box_u64" ||
        fn == "lean_native_unbox_u64" || fn == "lean_native_ctor_set" ||
        fn == "lean_native_ctor_set_scalar") &&
      args.any aliases.contains
  | _ => false

def tlExprEscapesWith (aliases : List VarId) (e : LNIRExpr) : Bool :=
  match e with
  | .allocCtor _ os ss => os.any aliases.contains || ss.any aliases.contains
  | .sarraySet _ _ x _ | .storageStore _ _ x => aliases.contains x
  | .call fn args _ isExtern =>
    if !isExtern && (fn == "lean_mark_mt" || fn == "lean_native_sarray_len" ||
        fn == "lean_native_ctor_tag" || fn == "lean_native_ensure_exclusive" ||
        fn == "lean_native_box_u64" || fn == "lean_native_unbox_u64") then
      false
    else
      args.any aliases.contains
  | _ => false

def tlKernelMentions (aliases : List VarId) (kern : ParallelKernelKind) : Bool :=
  match kern with
  | .customScalar idxVar inVars body =>
    tlScalarMentions (aliases.filter (fun x => x != idxVar && !(inVars.contains x))) body
  | _ => false

def tlCodeEscapesWith (aliases : List VarId) (code : LNIRCode) : Bool :=
  match code with
  | .letBind dst _ val k =>
    let rest := aliases.filter (· != dst)
    let nextAliases := if tlExprMayAlias aliases val then dst :: rest else rest
    tlExprEscapesWith aliases val || tlCodeEscapesWith nextAliases k
  | .rawStore _ _ x _ k => aliases.contains x || tlCodeEscapesWith aliases k
  | .incRef _ _ k | .decRef _ _ k => tlCodeEscapesWith aliases k
  | .ite _ t e => tlCodeEscapesWith aliases t || tlCodeEscapesWith aliases e
  | .seqFor iv _ _ av init _ step k =>
    let stepAliases := aliases.filter (fun x => x != iv && x != av)
    let kAliases := aliases.filter (· != av)
    aliases.contains init || tlCodeEscapesWith stepAliases step || tlCodeEscapesWith kAliases k
  | .parFor ov lv ins _ kern k =>
    aliases.contains lv || ins.any aliases.contains || tlKernelMentions aliases kern ||
      tlCodeEscapesWith (aliases.filter (· != ov)) k
  | .ret r => aliases.contains r
  | .unreachable => false

def tlCheckNonEscaping (v : VarId) (code : LNIRCode) : Bool :=
  !(tlCodeEscapesWith [v] code)

def isMarkMtCall (e : LNIRExpr) : Bool :=
  match e with
  | .call fn _ _ isExtern => !isExtern && fn == "lean_mark_mt"
  | _ => false

def canElideMarkMt (e : LNIRExpr) (k : LNIRCode) : Bool :=
  match e with
  | .call fn [arg] _ false => fn == "lean_mark_mt" && tlCheckNonEscaping arg k
  | _ => false

/-- Escape-gated `lean_mark_mt` elision (replacing with scalar `0`) plus zero-delta RC elision. -/
def elideMarkMtAndZeroRc (code : LNIRCode) : LNIRCode :=
  match code with
  | .letBind dst ty val k =>
    let rhs := if canElideMarkMt val k then .scalar (.constU64 0) else val
    .letBind dst ty rhs (elideMarkMtAndZeroRc k)
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

/-- Scope-aware borrowed/non-owning RC elision on `v` plus escape-gated `lean_mark_mt` elision. -/
def elideBorrowedAndThreadLocalRC (v : VarId) (code : LNIRCode) : LNIRCode :=
  match code with
  | .letBind dst ty val k =>
    let rhs := if canElideMarkMt val k then .scalar (.constU64 0) else val
    let tail := if dst == v then elideMarkMtAndZeroRc k else elideBorrowedAndThreadLocalRC v k
    .letBind dst ty rhs tail
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
    let step' :=
      if iv == v || av == v then elideMarkMtAndZeroRc step
      else elideBorrowedAndThreadLocalRC v step
    let k' := if av == v then elideMarkMtAndZeroRc k else elideBorrowedAndThreadLocalRC v k
    .seqFor iv lv hv av ai aty step' k'
  | .parFor ov lv ins ety kern k =>
    let k' := if ov == v then elideMarkMtAndZeroRc k else elideBorrowedAndThreadLocalRC v k
    .parFor ov lv ins ety kern k'
  | .ret r => .ret r
  | .unreachable => .unreachable

theorem evalMarkMt_ok_eq (env : VarEnv) (st : HeapState) (e : LNIRExpr) (k : LNIRCode)
    (hcan : canElideMarkMt e k = true) (bound : Val) (st1 : HeapState)
    (he : evalExpr env st e = .ok (bound, st1)) :
    bound = .u64 0 ∧ st1 = st := by
  cases e with
  | call fn args retTy ext =>
    cases ext
    · cases args with
      | nil => simp [canElideMarkMt] at hcan
      | cons arg rest =>
        cases rest with
        | cons _ _ => simp [canElideMarkMt] at hcan
        | nil =>
          dsimp only [canElideMarkMt] at hcan
          have hfn : fn = "lean_mark_mt" := of_decide_eq_true ((Bool.and_eq_true _ _).mp hcan).1
          subst hfn
          have hbox : ("lean_mark_mt" == "lean_native_box_u64") = false := by decide
          have hunbox : ("lean_mark_mt" == "lean_native_unbox_u64") = false := by decide
          have hexcl : ("lean_mark_mt" == "lean_native_ensure_exclusive") = false := by decide
          have hlen : ("lean_mark_mt" == "lean_native_sarray_len") = false := by decide
          cases harg : env arg with
          | none => simp [evalExpr, evalVarList, harg] at he
          | some vArg =>
            simp only [evalExpr, evalVarList, harg, hbox, hunbox, hexcl, hlen,
              Bool.false_or, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true] at he
            cases vArg with
            | sarrayId bufId =>
              dsimp only at he
              cases hbuf : st.findBuffer bufId with
              | none => rw [hbuf] at he; contradiction
              | some _ =>
                rw [hbuf] at he
                injection he with hp
                exact ⟨(Prod.mk.inj hp).1.symm, (Prod.mk.inj hp).2.symm⟩
            | objPtr objId =>
              by_cases hrc : (st.getObjRefCount objId == 0) = true
              · simp [hrc] at he
              · simp only [hrc, Bool.false_eq_true, ↓reduceIte] at he
                injection he with hp
                exact ⟨(Prod.mk.inj hp).1.symm, (Prod.mk.inj hp).2.symm⟩
            | u64 _ | u256 _ | bool _ | unit | tuple _ | rawPtrId _ | storageMapId _ =>
              injection he with hp
              exact ⟨(Prod.mk.inj hp).1.symm, (Prod.mk.inj hp).2.symm⟩
    · simp [canElideMarkMt] at hcan
  | _ => simp [canElideMarkMt] at hcan

theorem evalMarkMt_obj_uaf (st : HeapState) (env : VarEnv) (arg : VarId) (objId : Nat)
    (retTy : LNIRType) (hv : env arg = some (.objPtr objId)) (hdead : st.getObjRefCount objId = 0) :
    evalExpr env st (.call "lean_mark_mt" [arg] retTy false) = .error (.useAfterFree objId) := by
  have hbox : ("lean_mark_mt" == "lean_native_box_u64") = false := by decide
  have hunbox : ("lean_mark_mt" == "lean_native_unbox_u64") = false := by decide
  have hexcl : ("lean_mark_mt" == "lean_native_ensure_exclusive") = false := by decide
  have hlen : ("lean_mark_mt" == "lean_native_sarray_len") = false := by decide
  simp [evalExpr, evalVarList, hv, hbox, hunbox, hexcl, hlen, hdead]

theorem elideMarkMtAndZeroRc_sound (code : LNIRCode) :
    CodeRefines code (elideMarkMtAndZeroRc code) := by
  induction code with
  | letBind dst ty val k ih =>
    dsimp only [elideMarkMtAndZeroRc]
    by_cases hcan : canElideMarkMt val k = true
    · rw [ite_eq_left hcan]
      intro fuel env st v st' hsrc
      dsimp only [evalCode] at hsrc ⊢
      cases he : evalExpr env st val with
      | error _ => rw [he] at hsrc; contradiction
      | ok pair =>
        rcases pair with ⟨bound, st1⟩
        rw [he] at hsrc
        have ⟨hb, hst⟩ := evalMarkMt_ok_eq env st val k hcan bound st1 he
        subst hb; subst hst
        exact ih fuel (env.bind dst (.u64 0)) st1 v st' hsrc
    · rw [ite_eq_right hcan]
      exact CodeRefines.letBind_congr (ExprRefines.refl val) ih
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

theorem evalIncRef_nonOwning (st : HeapState) (env : VarEnv) (v : VarId) (c : Nat)
    (val : Val) (hv : env v = some val) (hown : valIsNonOwning val = true) :
    st.evalIncRef env v c = .ok st := by
  unfold HeapState.evalIncRef
  rw [hv]
  cases val <;> simp_all [valIsNonOwning]

theorem evalDecRef_nonOwning (st : HeapState) (env : VarEnv) (v : VarId) (c : Nat)
    (val : Val) (hv : env v = some val) (hown : valIsNonOwning val = true) :
    st.evalDecRef env v c = .ok st := by
  unfold HeapState.evalDecRef
  rw [hv]
  cases val <;> simp_all [valIsNonOwning]

theorem evalIncRef_obj_uaf (st : HeapState) (env : VarEnv) (v : VarId) (objId c : Nat)
    (hv : env v = some (.objPtr objId)) (hdead : st.getObjRefCount objId = 0) :
    st.evalIncRef env v c = .error (.useAfterFree objId) := by
  unfold HeapState.evalIncRef HeapState.incRefObj
  rw [hv]
  simp [hdead]

theorem evalDecRef_obj_uaf (st : HeapState) (env : VarEnv) (v : VarId) (objId c : Nat)
    (hv : env v = some (.objPtr objId)) (hdead : st.getObjRefCount objId = 0) :
    st.evalDecRef env v c = .error (.useAfterFree objId) := by
  unfold HeapState.evalDecRef HeapState.decRefObj HeapState.decRefObjFuel
  rw [hv]
  simp [hdead]

theorem bind_other_eq {env : VarEnv} {v dst : VarId} {bound val : Val}
    (hshadow : ¬(dst == v) = true) (hv : env v = some val) :
    (env.bind dst bound) v = some val := by
  have hne : (v == dst) = false := by
    cases hvd : (v == dst) with
    | false => rfl
    | true =>
      have heq : v = dst := of_decide_eq_true hvd
      subst heq
      simp at hshadow
  simpa [VarEnv.bind, hne] using hv

theorem evalSeqLoop_borrowed_rc (count curIdx : Nat) (iv av v : VarId)
    (vinit val : Val) (env : VarEnv) (st : HeapState) (finalAcc : Val) (st1 : HeapState)
    (fuel : Nat) (step : LNIRCode) (hv : env v = some val)
    (hiv : ¬(iv == v) = true) (hav : ¬(av == v) = true)
    (ihs : ∀ senv sst, senv v = some val → ∀ outV st',
      evalCode fuel senv sst step = .ok (outV, st') →
      evalCode fuel senv sst (elideBorrowedAndThreadLocalRC v step) = .ok (outV, st'))
    (hloop : evalSeqLoop count curIdx iv av vinit env st
      (fun stepEnv stepSt => evalCode fuel stepEnv stepSt step) = .ok (finalAcc, st1)) :
    evalSeqLoop count curIdx iv av vinit env st
      (fun stepEnv stepSt => evalCode fuel stepEnv stepSt (elideBorrowedAndThreadLocalRC v step)) =
        .ok (finalAcc, st1) := by
  induction count generalizing curIdx vinit st with
  | zero => exact hloop
  | succ count' ih =>
    simp only [evalSeqLoop] at hloop ⊢
    cases hs1 : evalCode fuel ((env.bind iv (.u64 curIdx.toUInt64)).bind av vinit) st step with
    | error _ => rw [hs1] at hloop; contradiction
    | ok spair =>
      rcases spair with ⟨nextAcc, sst1⟩
      rw [hs1] at hloop
      have hvStep : ((env.bind iv (.u64 curIdx.toUInt64)).bind av vinit) v = some val :=
        bind_other_eq hav (bind_other_eq hiv hv)
      rw [ihs _ st hvStep nextAcc sst1 hs1]
      exact ih (curIdx + 1) nextAcc sst1 hloop

/-- Forward simulation for `elideBorrowedAndThreadLocalRC` whenever `v` is bound in `env`
    to a non-owning runtime value (such as a borrowed `.rawPtrId` region pointer or scalar). -/
theorem elideBorrowedAndThreadLocalRC_sound (v : VarId) (code : LNIRCode)
    (fuel : Nat) (env : VarEnv) (st : HeapState) (outV : Val) (st' : HeapState)
    (val : Val) (hv : env v = some val) (hown : valIsNonOwning val = true)
    (hsrc : evalCode fuel env st code = .ok (outV, st')) :
    evalCode fuel env st (elideBorrowedAndThreadLocalRC v code) = .ok (outV, st') := by
  induction code generalizing env st outV st' with
  | letBind dst ty expr k ih =>
    dsimp only [elideBorrowedAndThreadLocalRC, evalCode] at hsrc ⊢
    cases he : evalExpr env st expr with
    | error _ => rw [he] at hsrc; contradiction
    | ok pair =>
      rcases pair with ⟨bound, st1⟩
      rw [he] at hsrc
      have hrhs : evalExpr env st
          (if canElideMarkMt expr k then .scalar (.constU64 0) else expr) =
          .ok (bound, st1) := by
        by_cases hcan : canElideMarkMt expr k = true
        · rw [ite_eq_left hcan]
          have ⟨hb, hst⟩ := evalMarkMt_ok_eq env st expr k hcan bound st1 he
          subst hb; subst hst; rfl
        · rw [ite_eq_right hcan]; exact he
      rw [hrhs]
      by_cases hsh : (dst == v) = true
      · rw [ite_eq_left hsh]
        exact elideMarkMtAndZeroRc_sound k fuel (env.bind dst bound) st1 outV st' hsrc
      · rw [ite_eq_right hsh]
        exact ih (env.bind dst bound) st1 outV st' (bind_other_eq hsh hv) hsrc
  | rawStore pv iv vv ty k ih =>
    dsimp only [elideBorrowedAndThreadLocalRC, evalCode] at hsrc ⊢
    cases hp : env pv with
    | none => rw [hp] at hsrc; contradiction
    | some vp =>
      rw [hp] at hsrc
      cases hi : env iv with
      | none => rw [hi] at hsrc; cases vp <;> contradiction
      | some vi =>
        rw [hi] at hsrc
        cases hvv : env vv with
        | none =>
          rw [hvv] at hsrc
          cases vp <;> cases vi <;> contradiction
        | some vv1 =>
          rw [hvv] at hsrc
          cases vp <;> cases vi
          all_goals (cases vv1 <;> try contradiction)
          all_goals
            dsimp only at hsrc ⊢
            cases hw : st.writeElemExclusive _ _ _ with
            | error _ => rw [hw] at hsrc; contradiction
            | ok st1 =>
              rw [hw] at hsrc
              exact ih env st1 outV st' hv hsrc
  | incRef ov c k ih =>
    dsimp only [elideBorrowedAndThreadLocalRC]
    by_cases hdrop : (ov == v || c == 0) = true
    · rw [ite_eq_left hdrop]
      dsimp only [evalCode] at hsrc
      cases hov : (ov == v) with
      | true =>
        have heq : ov = v := of_decide_eq_true hov
        subst heq
        rw [evalIncRef_nonOwning st env ov c val hv hown] at hsrc
        exact ih env st outV st' hv hsrc
      | false =>
        have hc0 : c = 0 := by simpa [hov] using hdrop
        subst hc0
        cases hinc : st.evalIncRef env ov 0 with
        | error _ => rw [hinc] at hsrc; contradiction
        | ok st1 =>
          rw [hinc] at hsrc
          have hst : st1 = st := evalIncRef_zero_ok st st1 env ov hinc
          subst hst
          exact ih env st1 outV st' hv hsrc
    · rw [ite_eq_right hdrop]
      dsimp only [evalCode] at hsrc ⊢
      cases hinc : st.evalIncRef env ov c with
      | error _ => rw [hinc] at hsrc; contradiction
      | ok st1 =>
        rw [hinc] at hsrc
        exact ih env st1 outV st' hv hsrc
  | decRef ov c k ih =>
    dsimp only [elideBorrowedAndThreadLocalRC]
    by_cases hdrop : (ov == v || c == 0) = true
    · rw [ite_eq_left hdrop]
      dsimp only [evalCode] at hsrc
      cases hov : (ov == v) with
      | true =>
        have heq : ov = v := of_decide_eq_true hov
        subst heq
        rw [evalDecRef_nonOwning st env ov c val hv hown] at hsrc
        exact ih env st outV st' hv hsrc
      | false =>
        have hc0 : c = 0 := by simpa [hov] using hdrop
        subst hc0
        cases hdec : st.evalDecRef env ov 0 with
        | error _ => rw [hdec] at hsrc; contradiction
        | ok st1 =>
          rw [hdec] at hsrc
          have hst : st1 = st := evalDecRef_zero_ok st st1 env ov hdec
          subst hst
          exact ih env st1 outV st' hv hsrc
    · rw [ite_eq_right hdrop]
      dsimp only [evalCode] at hsrc ⊢
      cases hdec : st.evalDecRef env ov c with
      | error _ => rw [hdec] at hsrc; contradiction
      | ok st1 =>
        rw [hdec] at hsrc
        exact ih env st1 outV st' hv hsrc
  | ite cv t e iht ihe =>
    dsimp only [elideBorrowedAndThreadLocalRC, evalCode] at hsrc ⊢
    cases hc : env cv with
    | none => rw [hc] at hsrc; contradiction
    | some vc =>
      rw [hc] at hsrc
      cases vc with
      | bool b =>
        cases b
        · exact ihe env st outV st' hv hsrc
        · exact iht env st outV st' hv hsrc
      | u64 n =>
        dsimp only at hsrc ⊢
        by_cases hn : (n != 0) = true
        · rw [ite_eq_left hn] at hsrc ⊢; exact iht env st outV st' hv hsrc
        · rw [ite_eq_right hn] at hsrc ⊢; exact ihe env st outV st' hv hsrc
      | u256 w =>
        dsimp only at hsrc ⊢
        by_cases hw : (w != UInt256.zero) = true
        · rw [ite_eq_left hw] at hsrc ⊢; exact iht env st outV st' hv hsrc
        · rw [ite_eq_right hw] at hsrc ⊢; exact ihe env st outV st' hv hsrc
      | _ => contradiction
  | seqFor iv lv hi av ai aty step k ihs ihk =>
    dsimp only [elideBorrowedAndThreadLocalRC, evalCode] at hsrc ⊢
    cases hlo : env lv with
    | none => rw [hlo] at hsrc; contradiction
    | some vlo =>
      cases hhi : env hi with
      | none => rw [hlo, hhi] at hsrc; cases vlo <;> contradiction
      | some vhi =>
        cases hinit : env ai with
        | none =>
          rw [hlo, hhi, hinit] at hsrc
          cases vlo <;> cases vhi <;> contradiction
        | some vinit =>
          rw [hlo, hhi, hinit] at hsrc
          cases vlo with
          | u64 lo =>
            cases vhi with
            | u64 hiVal =>
              simp only at hsrc ⊢
              cases hloop : evalSeqLoop (hiVal.toNat - lo.toNat) lo.toNat iv av vinit env st
                  (fun stepEnv stepSt => evalCode fuel stepEnv stepSt step) with
              | error _ => rw [hloop] at hsrc; contradiction
              | ok pair =>
                rcases pair with ⟨finalAcc, st1⟩
                rw [hloop] at hsrc
                have hloop2 : evalSeqLoop (hiVal.toNat - lo.toNat) lo.toNat iv av vinit env st
                    (fun stepEnv stepSt => evalCode fuel stepEnv stepSt
                      (if iv == v || av == v then elideMarkMtAndZeroRc step
                       else elideBorrowedAndThreadLocalRC v step)) = .ok (finalAcc, st1) := by
                  by_cases hsh : (iv == v || av == v) = true
                  · simp only [hsh, ↓reduceIte]
                    exact evalSeqLoop_refines_rc (hiVal.toNat - lo.toNat) lo.toNat iv av vinit
                      env st finalAcc st1
                      (fun stepEnv stepSt => evalCode fuel stepEnv stepSt step)
                      (fun stepEnv stepSt =>
                        evalCode fuel stepEnv stepSt (elideMarkMtAndZeroRc step))
                      (fun senv sst sv sst' hs =>
                        elideMarkMtAndZeroRc_sound step fuel senv sst sv sst' hs)
                      hloop
                  · simp only [hsh, Bool.false_eq_true, ↓reduceIte]
                    have hiv : ¬(iv == v) = true := by intro h; simp [h] at hsh
                    have hav : ¬(av == v) = true := by intro h; simp [h] at hsh
                    exact evalSeqLoop_borrowed_rc (hiVal.toNat - lo.toNat) lo.toNat iv av v
                      vinit val env st finalAcc st1 fuel step hv hiv hav
                      (fun senv sst hvs sv sst' hs => ihs senv sst sv sst' hvs hs) hloop
                rw [hloop2]
                by_cases hav : (av == v) = true
                · rw [ite_eq_left hav]
                  exact elideMarkMtAndZeroRc_sound k fuel (env.bind av finalAcc) st1 outV st' hsrc
                · rw [ite_eq_right hav]
                  exact ihk (env.bind av finalAcc) st1 outV st' (bind_other_eq hav hv) hsrc
            | _ => contradiction
          | _ => cases vhi <;> contradiction
  | parFor ov lv ins ety kern k ih =>
    dsimp only [elideBorrowedAndThreadLocalRC, evalCode] at hsrc ⊢
    cases hpar : evalParFor fuel env st lv ins kern with
    | error _ => rw [hpar] at hsrc; contradiction
    | ok pair =>
      rcases pair with ⟨resVal, st1⟩
      rw [hpar] at hsrc
      by_cases hov : (ov == v) = true
      · rw [ite_eq_left hov]
        exact elideMarkMtAndZeroRc_sound k fuel (env.bind ov resVal) st1 outV st' hsrc
      · rw [ite_eq_right hov]
        exact ih (env.bind ov resVal) st1 outV st' (bind_other_eq hov hv) hsrc
  | ret r => exact hsrc
  | unreachable => exact hsrc

def optimizeThreadLocalOwnershipRC (code : LNIRCode) : LNIRCode :=
  optimizeOwnershipRC (elideMarkMtAndZeroRc code)

theorem optimizeThreadLocalOwnershipRC_sound (code : LNIRCode) :
    CodeRefines code (optimizeThreadLocalOwnershipRC code) :=
  CodeRefines.trans (elideMarkMtAndZeroRc_sound code)
    (elideAndMutateRC_sound (elideMarkMtAndZeroRc code))

def verifiedThreadLocalRCContract : VerifiedCodePassContract where
  name       := "ThreadLocalRC"
  theoremRef := "LeanNative.Proofs.optimizeThreadLocalOwnershipRC_sound"
  notes      := "Escape-gated lean_mark_mt elision and zero-delta incRef/decRef pass"
  runCode    := optimizeThreadLocalOwnershipRC
  sound      := optimizeThreadLocalOwnershipRC_sound

end LeanNative.Transform

namespace LeanNative.Proofs
  abbrev CodeRefinesWithRC := LeanNative.Transform.CodeRefinesWithRC
  abbrev optimizeOwnershipRC := LeanNative.Transform.optimizeOwnershipRC
  abbrev elideAndMutateRC_sound := @LeanNative.Transform.elideAndMutateRC_sound
  abbrev valIsNonOwning := LeanNative.Transform.valIsNonOwning
  abbrev elideBorrowedAndThreadLocalRC := LeanNative.Transform.elideBorrowedAndThreadLocalRC
  abbrev elideBorrowedAndThreadLocalRC_sound :=
    @LeanNative.Transform.elideBorrowedAndThreadLocalRC_sound
  abbrev elideMarkMtAndZeroRc := LeanNative.Transform.elideMarkMtAndZeroRc
  abbrev elideMarkMtAndZeroRc_sound := @LeanNative.Transform.elideMarkMtAndZeroRc_sound
  abbrev optimizeThreadLocalOwnershipRC := LeanNative.Transform.optimizeThreadLocalOwnershipRC
  abbrev optimizeThreadLocalOwnershipRC_sound :=
    @LeanNative.Transform.optimizeThreadLocalOwnershipRC_sound
  abbrev evalIncRef_obj_uaf := @LeanNative.Transform.evalIncRef_obj_uaf
  abbrev evalDecRef_obj_uaf := @LeanNative.Transform.evalDecRef_obj_uaf
  abbrev evalMarkMt_obj_uaf := @LeanNative.Transform.evalMarkMt_obj_uaf
end LeanNative.Proofs
