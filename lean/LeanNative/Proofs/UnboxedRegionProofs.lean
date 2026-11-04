import LeanNative.IR.UnboxedRegion
import LeanNative.Semantics.Refinement
import LeanNative.Transform.OwnershipRC
import LeanNative.Backend.LLVMAst.SemanticsProofs

set_option autoImplicit false

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend.TargetIR
open LeanNative.Backend.LLVMAst
open LeanNative.Transform

/-! Track D2 Soundness Proofs: zero `def`/`structure`/`inductive`, standard axioms only. -/

private theorem regionAlignUp_mod_zero (n a : Nat) (ha : 0 < a) :
    regionAlignUp n a % a = 0 := by
  unfold regionAlignUp
  rw [beq_false_of_ne (Nat.ne_of_gt ha)]
  exact Nat.mul_mod_right a ((n + (a - 1)) / a)

private theorem le_regionAlignUp (n a : Nat) : n ≤ regionAlignUp n a := by
  unfold regionAlignUp
  by_cases ha : a = 0
  · subst ha; simp
  · rw [beq_false_of_ne ha]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hdiv := Nat.div_add_mod (n + (a - 1)) a
    have hmod := Nat.mod_lt (n + (a - 1)) (Nat.pos_of_ne_zero ha)
    omega

private theorem scalarKind_byteSize_pos (k : UnboxedScalarKind) : 0 < k.byteSize := by
  cases k <;> decide

private theorem placeUnboxedFieldsFrom_align_pos (fields : List UnboxedField) (off maxA : Nat)
    (hmax : 0 < maxA) : 0 < (placeUnboxedFieldsFrom fields off maxA).2.2 := by
  induction fields generalizing off maxA with
  | nil => exact hmax
  | cons f fs ih =>
    exact ih _ _ (Nat.lt_of_lt_of_le hmax (Nat.le_max_left maxA f.kind.byteSize))

private theorem placeUnboxedFieldsFrom_bounds (fields : List UnboxedField) (off maxA : Nat) :
    off ≤ (placeUnboxedFieldsFrom fields off maxA).2.1 ∧
      ∀ g ∈ (placeUnboxedFieldsFrom fields off maxA).1,
        off ≤ g.offset ∧ fieldByteEnd g ≤ (placeUnboxedFieldsFrom fields off maxA).2.1 := by
  induction fields generalizing off maxA with
  | nil => exact ⟨Nat.le_refl off, fun _ hg => nomatch hg⟩
  | cons f fs ih =>
    unfold placeUnboxedFieldsFrom placeUnboxedField fieldByteEnd
    dsimp only
    have hoff := le_regionAlignUp off f.kind.byteSize
    have ⟨hrle, hrmem⟩ :=
      ih (regionAlignUp off f.kind.byteSize + f.kind.byteSize) (Nat.max maxA f.kind.byteSize)
    refine ⟨Nat.le_trans (Nat.le_trans hoff (Nat.le_add_right _ _)) hrle, fun g hg => ?_⟩
    rcases List.mem_cons.mp hg with rfl | htail
    · exact ⟨hoff, hrle⟩
    · exact ⟨Nat.le_trans (Nat.le_trans hoff (Nat.le_add_right _ _)) (hrmem g htail).1,
        (hrmem g htail).2⟩

private theorem placeUnboxedFieldsFrom_disjoint (fields : List UnboxedField) (off maxA : Nat) :
    layoutFieldsDisjoint (placeUnboxedFieldsFrom fields off maxA).1 = true := by
  induction fields generalizing off maxA with
  | nil => rfl
  | cons f fs ih =>
    unfold placeUnboxedFieldsFrom layoutFieldsDisjoint
    rw [Bool.and_eq_true]
    refine ⟨List.all_eq_true.mpr fun g hg => ?_,
      ih (placeUnboxedField off f).2 (Nat.max maxA f.kind.byteSize)⟩
    exact decide_eq_true ((placeUnboxedFieldsFrom_bounds fs (placeUnboxedField off f).2
      (Nat.max maxA f.kind.byteSize)).2 g hg).1

private theorem placeUnboxedFieldsFrom_aligned (fields : List UnboxedField) (off maxA : Nat) :
    layoutFieldsAligned (placeUnboxedFieldsFrom fields off maxA).1 = true := by
  induction fields generalizing off maxA with
  | nil => rfl
  | cons f fs ih =>
    unfold placeUnboxedFieldsFrom layoutFieldsAligned placeUnboxedField; dsimp only
    have hp := scalarKind_byteSize_pos f.kind
    have hm := regionAlignUp_mod_zero off f.kind.byteSize hp
    rw [List.all_cons, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨⟨⟨decide_eq_true hp, decide_eq_true hm⟩, decide_eq_true rfl⟩, decide_eq_true rfl⟩,
      ih _ _⟩

theorem unboxedStructLayout_disjoint_aligned (name : String) (fields : List UnboxedField) :
    layoutWellFormed (mkUnboxedStructLayout name fields) = true := by
  unfold mkUnboxedStructLayout layoutWellFormed
  have halign := placeUnboxedFieldsFrom_align_pos fields 0 1 (by decide)
  have hstride := regionAlignUp_mod_zero (placeUnboxedFieldsFrom fields 0 1).2.1 _ halign
  have ⟨_, hmem⟩ := placeUnboxedFieldsFrom_bounds fields 0 1
  have hfit : (placeUnboxedFieldsFrom fields 0 1).1.all
      (fun f => decide (fieldByteEnd f ≤
        regionAlignUp (placeUnboxedFieldsFrom fields 0 1).2.1
          (placeUnboxedFieldsFrom fields 0 1).2.2)) = true :=
    List.all_eq_true.mpr fun g hg =>
      decide_eq_true (Nat.le_trans (hmem g hg).2 (le_regionAlignUp _ _))
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨rfl, decide_eq_true halign⟩, decide_eq_true hstride⟩,
    placeUnboxedFieldsFrom_disjoint fields 0 1⟩,
    placeUnboxedFieldsFrom_aligned fields 0 1⟩, hfit⟩

private theorem evalScalar_preserves_heap (env : VarEnv) (st st' : HeapState)
    (se : ScalarExpr) (v : Val) (h : evalExpr env st (.scalar se) = .ok (v, st')) : st' = st := by
  dsimp only [evalExpr] at h
  cases hsc : evalScalarExpr env se with
  | error _ => rw [hsc] at h; contradiction
  | ok sv => rw [hsc] at h; exact (Prod.mk.inj (Except.ok.inj h)).2.symm

private theorem evalRawLoad_preserves_heap (env : VarEnv) (st st' : HeapState)
    (p i : VarId) (ty : LNIRType) (v : Val)
    (h : evalExpr env st (.rawLoad p i ty) = .ok (v, st')) : st' = st := by
  dsimp only [evalExpr] at h
  cases hp : env p with
  | none => rw [hp] at h; contradiction
  | some pv =>
    rw [hp] at h
    cases hi : env i with
    | none => rw [hi] at h; cases pv <;> contradiction
    | some iv =>
      rw [hi] at h
      cases pv <;> cases iv <;> try contradiction
      all_goals
        dsimp only at h
        cases hrd : st.readElem _ _ with
        | error _ => rw [hrd] at h; contradiction
        | ok w => rw [hrd] at h; exact (Prod.mk.inj (Except.ok.inj h)).2.symm

theorem lowerUnboxedRegionRcFree_true (dst posVar idxVar baseVar : VarId)
    (layout : UnboxedStructLayout) (slice : BorrowedRegionSlice) :
    lowerUnboxedRegionRcFree dst posVar idxVar layout slice baseVar = true := by
  cases layout with
  | mk name fields stride align header => cases fields <;> rfl

theorem lowerUnboxedRegionCode_sound (dst posVar idxVar baseVar : VarId)
    (layout : UnboxedStructLayout) (slice : BorrowedRegionSlice) (fuel : Nat) (env : VarEnv)
    (st : HeapState) (v : Val) (st' : HeapState)
    (h : evalCode fuel env st
      (lowerUnboxedRegionCode dst posVar idxVar layout slice baseVar (.ret dst)) = .ok (v, st')) :
    st' = st := by
  cases layout with
  | mk name fields stride align header =>
    cases fields with
    | nil =>
      unfold lowerUnboxedRegionCode lowerBorrowedSliceLoad at h
      simp only [evalCode] at h
      cases he1 : evalExpr env st (.scalar (.binOp .add
          (.constU64 (byteOffsetToWord slice.view.offset).toUInt64)
          (.binOp .shr (.var idxVar) (.constU64 3)))) with
      | error _ => rw [he1] at h; contradiction
      | ok p1 =>
        rcases p1 with ⟨v1, st1⟩; rw [he1] at h
        have hst1 := evalScalar_preserves_heap env st st1 _ v1 he1
        dsimp only at h
        cases he2 : evalExpr (env.bind posVar v1) st1 (.rawLoad slice.ptrVar posVar .i64) with
        | error _ => rw [he2] at h; contradiction
        | ok p2 =>
          rcases p2 with ⟨v2, st2⟩; rw [he2] at h
          have hst2 := evalRawLoad_preserves_heap (env.bind posVar v1) st1 st2
            slice.ptrVar posVar .i64 v2 he2
          simp only [VarEnv.bind_self] at h
          exact Eq.trans (Prod.mk.inj (Except.ok.inj h)).2.symm (Eq.trans hst2 hst1)
    | cons f fs =>
      unfold lowerUnboxedRegionCode lowerUnboxedFieldLoad at h
      simp only [evalCode] at h
      cases he1 : evalExpr env st (.scalar (.binOp .add (.binOp .shr (.var idxVar) (.constU64 3))
          (.constU64 (byteOffsetToWord f.offset).toUInt64))) with
      | error _ => rw [he1] at h; contradiction
      | ok p1 =>
        rcases p1 with ⟨v1, st1⟩; rw [he1] at h
        have hst1 := evalScalar_preserves_heap env st st1 _ v1 he1
        dsimp only at h
        cases he2 : evalExpr (env.bind posVar v1) st1
            (.rawLoad baseVar posVar f.field.kind.lnirType) with
        | error _ => rw [he2] at h; contradiction
        | ok p2 =>
          rcases p2 with ⟨v2, st2⟩; rw [he2] at h
          have hst2 := evalRawLoad_preserves_heap (env.bind posVar v1) st1 st2
            baseVar posVar f.field.kind.lnirType v2 he2
          simp only [VarEnv.bind_self] at h
          exact Eq.trans (Prod.mk.inj (Except.ok.inj h)).2.symm (Eq.trans hst2 hst1)

theorem borrowedSliceSub_valid (s sub : BorrowedRegionSlice) (subOff subLen : Nat)
    (h : borrowedSliceSub s subOff subLen = some sub) :
    borrowedSliceValid sub = true ∧ sub.view.offset = s.view.offset + subOff ∧
      sub.view.len = subLen := by
  unfold borrowedSliceSub at h
  by_cases hgate : borrowedSliceValid s && decide (subOff + subLen ≤ s.view.len)
  · simp only [hgate, ↓reduceIte] at h
    injection h with hsub
    subst hsub
    have hboth := (Bool.and_eq_true _ _).mp hgate
    have hslice := (Bool.and_eq_true _ _).mp hboth.1
    have hv := LeanNative.Spec.subSliceView_valid s.view subOff subLen
      hslice.1 (of_decide_eq_true hboth.2)
    exact ⟨by simp [borrowedSliceValid, hv, hslice.2], rfl, rfl⟩
  · simp [hgate] at h

theorem evalBorrowedObjPair_cancel (fuel : Nat) (env : VarEnv) (bufs : List ArrayBuffer)
    (nid objId c : Nat) (v : VarId) (k : LNIRCode) (hv : env v = some (.objPtr objId)) :
    let st0 : HeapState := { buffers := bufs, nextId := nid, refCounts := [(true, objId, 1)] }
    evalCode fuel env st0 (.incRef v c (.decRef v c k)) = evalCode fuel env st0 k := by
  intro st0
  have hcancel : (match st0.incRefObj objId c with
      | .ok st1 => st1.decRefObj objId c | .error e => .error e) = .ok st0 :=
    HeapState.incRefObj_decRefObj_cancel bufs nid objId c
  dsimp only [evalCode, HeapState.evalIncRef, HeapState.evalDecRef]
  rw [hv]; dsimp only
  cases hinc : st0.incRefObj objId c with
  | error err => rw [hinc] at hcancel; cases hcancel
  | ok st1 =>
    rw [hinc] at hcancel
    dsimp only at hcancel ⊢; rw [hcancel]

private theorem isMarkMtExpr_eq_call (e : LNIRExpr) : isMarkMtExpr e = isMarkMtCall e := by
  cases e <;> rfl

theorem elideMarkMtAndZeroRc_preserves_nonEscape (aliases : List VarId) (code : LNIRCode)
    (h : codeEscapesWith aliases code = false) :
    codeEscapesWith aliases (elideMarkMtAndZeroRc code) = false := by
  unfold elideMarkMtAndZeroRc
  induction code generalizing aliases with
  | letBind dst ty val k ih =>
    unfold codeEscapesWith at h
    unfold Transform.elideMarkMtAndZeroRc
    rw [← isMarkMtExpr_eq_call]
    by_cases hmt : isMarkMtExpr val = true
    · simp only [hmt, ↓reduceIte] at h ⊢; exact ih aliases h
    · simp only [hmt, Bool.false_eq_true, ↓reduceIte] at h ⊢
      unfold codeEscapesWith
      simp only [hmt, Bool.false_eq_true, ↓reduceIte]
      rw [Bool.or_eq_false_iff] at h ⊢
      exact ⟨h.1, ih _ h.2⟩
  | rawStore p i x ty k ih =>
    unfold codeEscapesWith at h
    dsimp only [Transform.elideMarkMtAndZeroRc, codeEscapesWith]
    rw [Bool.or_eq_false_iff] at h ⊢
    exact ⟨h.1, ih aliases h.2⟩
  | incRef ov c k ih =>
    unfold codeEscapesWith at h
    unfold Transform.elideMarkMtAndZeroRc
    by_cases hc : (c == 0) = true
    · rw [ite_eq_left hc]; exact ih aliases h
    · rw [ite_eq_right hc]; exact ih aliases h
  | decRef ov c k ih =>
    unfold codeEscapesWith at h
    unfold Transform.elideMarkMtAndZeroRc
    by_cases hc : (c == 0) = true
    · rw [ite_eq_left hc]; exact ih aliases h
    · rw [ite_eq_right hc]; exact ih aliases h
  | ite cv t e iht ihe =>
    unfold codeEscapesWith at h
    dsimp only [Transform.elideMarkMtAndZeroRc, codeEscapesWith]
    rw [Bool.or_eq_false_iff] at h ⊢
    exact ⟨iht aliases h.1, ihe aliases h.2⟩
  | seqFor iv lo hi av init aty step k ihs ihk =>
    unfold codeEscapesWith at h
    dsimp only [Transform.elideMarkMtAndZeroRc, codeEscapesWith]
    simp only [Bool.or_eq_false_iff] at h ⊢
    exact ⟨⟨h.1.1, ihs _ h.1.2⟩, ihk _ h.2⟩
  | parFor ov len ins ety kern k ih =>
    unfold codeEscapesWith at h
    dsimp only [Transform.elideMarkMtAndZeroRc, codeEscapesWith]
    rw [Bool.or_eq_false_iff] at h ⊢
    exact ⟨h.1, ih _ h.2⟩
  | ret r => exact h
  | unreachable => rfl

theorem elideBorrowed_preserves_nonEscape (v : VarId) (aliases : List VarId) (code : LNIRCode)
    (h : codeEscapesWith aliases code = false) :
    codeEscapesWith aliases (elideBorrowedAndThreadLocalRC v code) = false := by
  unfold elideBorrowedAndThreadLocalRC
  induction code generalizing aliases with
  | letBind dst ty val k ih =>
    unfold codeEscapesWith at h
    unfold Transform.elideBorrowedAndThreadLocalRC
    rw [← isMarkMtExpr_eq_call]
    by_cases hmt : isMarkMtExpr val = true
    · simp only [hmt, ↓reduceIte] at h ⊢
      by_cases hsh : (dst == v) = true
      · rw [ite_eq_left hsh]; exact elideMarkMtAndZeroRc_preserves_nonEscape aliases k h
      · rw [ite_eq_right hsh]; exact ih aliases h
    · simp only [hmt, Bool.false_eq_true, ↓reduceIte] at h ⊢
      unfold codeEscapesWith
      simp only [hmt, Bool.false_eq_true, ↓reduceIte]
      rw [Bool.or_eq_false_iff] at h ⊢
      refine ⟨h.1, ?_⟩
      by_cases hsh : (dst == v) = true
      · rw [ite_eq_left hsh]; exact elideMarkMtAndZeroRc_preserves_nonEscape _ k h.2
      · rw [ite_eq_right hsh]; exact ih _ h.2
  | rawStore p i x ty k ih =>
    unfold codeEscapesWith at h
    dsimp only [Transform.elideBorrowedAndThreadLocalRC, codeEscapesWith]
    rw [Bool.or_eq_false_iff] at h ⊢
    exact ⟨h.1, ih aliases h.2⟩
  | incRef ov c k ih =>
    unfold codeEscapesWith at h
    unfold Transform.elideBorrowedAndThreadLocalRC
    by_cases hc : (ov == v || c == 0) = true
    · rw [ite_eq_left hc]; exact ih aliases h
    · rw [ite_eq_right hc]; exact ih aliases h
  | decRef ov c k ih =>
    unfold codeEscapesWith at h
    unfold Transform.elideBorrowedAndThreadLocalRC
    by_cases hc : (ov == v || c == 0) = true
    · rw [ite_eq_left hc]; exact ih aliases h
    · rw [ite_eq_right hc]; exact ih aliases h
  | ite cv t e iht ihe =>
    unfold codeEscapesWith at h
    dsimp only [Transform.elideBorrowedAndThreadLocalRC, codeEscapesWith]
    rw [Bool.or_eq_false_iff] at h ⊢
    exact ⟨iht aliases h.1, ihe aliases h.2⟩
  | seqFor iv lo hi av init aty step k ihs ihk =>
    unfold codeEscapesWith at h
    dsimp only [Transform.elideBorrowedAndThreadLocalRC, codeEscapesWith]
    simp only [Bool.or_eq_false_iff] at h ⊢
    refine ⟨⟨h.1.1, ?_⟩, ?_⟩
    · by_cases hs : (iv == v || av == v) = true
      · rw [ite_eq_left hs]; exact elideMarkMtAndZeroRc_preserves_nonEscape _ step h.1.2
      · rw [ite_eq_right hs]; exact ihs _ h.1.2
    · by_cases hk : (av == v) = true
      · rw [ite_eq_left hk]; exact elideMarkMtAndZeroRc_preserves_nonEscape _ k h.2
      · rw [ite_eq_right hk]; exact ihk _ h.2
  | parFor ov len ins ety kern k ih =>
    unfold codeEscapesWith at h
    dsimp only [Transform.elideBorrowedAndThreadLocalRC, codeEscapesWith]
    rw [Bool.or_eq_false_iff] at h ⊢
    refine ⟨h.1, ?_⟩
    by_cases hk : (ov == v) = true
    · rw [ite_eq_left hk]; exact elideMarkMtAndZeroRc_preserves_nonEscape _ k h.2
    · rw [ite_eq_right hk]; exact ih _ h.2
  | ret r => exact h
  | unreachable => rfl

theorem threadLocalEscape_no_mark_mt_sound (v : VarId) (code : LNIRCode)
    (dst : RegName) (ptr : Operand) (h : checkThreadLocalNonEscaping v code = true) :
    codeEscapes v (elideBorrowedAndThreadLocalRC v code) = false ∧
      emitMarkMtHeader dst ptr v code = [] := by
  have hno : codeEscapes v code = false := by
    unfold checkThreadLocalNonEscaping at h; simpa using h
  exact ⟨elideBorrowed_preserves_nonEscape v [v] code hno, by simp [emitMarkMtHeader, h]⟩

private theorem accessCheck_read_of_write (m : ByteMem) (addr : BitVec 64) (sz align : Nat)
    (h : accessCheck m addr sz align true = none) : accessCheck m addr sz align false = none := by
  unfold accessCheck at h ⊢
  by_cases hnull : (addr == 0#64) = true
  · simp [hnull] at h
  · by_cases hp2 : (!isPow2 align) = true
    · simp [hnull, hp2] at h
    · by_cases hal : (!isAligned addr align) = true
      · simp [hnull, hp2, hal] at h
      · simp only [hnull, hp2, hal, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hx : m.accessInAlloc addr.toNat sz true
        · simp [hx] at h
        · simp [accessInAlloc_read_of_write m addr.toNat sz hx]

private theorem loadVal_i64_of_loadInt (m : ByteMem) (addr : BitVec 64)
    (rc : BitVec (.i64 : IntWidth).bits) (hload : m.loadInt? addr .i64 = some rc) :
    loadVal m addr (.int .i64) = .bits .i64 rc := by
  have htake : (m.readBytesAt addr.toNat 8).take 8 = m.readBytesAt addr.toNat 8 := by
    apply List.take_of_length_le; rw [ByteMem.readBytesAt_length]; exact Nat.le_refl 8
  have hbytes : ByteMem.bytesToBv? IntWidth.i64.bits ((m.readBytesAt addr.toNat 8).take 8) =
      some rc := by rw [htake]; exact hload
  simp [loadVal, deserializeVal, deserializeValAux, LLVMType.byteSize, IntWidth.byteSize, hbytes]

private theorem lookupReg_bindReg_same (st : ExecState) (r : RegName) (v : LLVMVal) :
    lookupReg (bindReg st r v) r = some v := by simp [lookupReg, bindReg]

private theorem lookupReg_bindReg_ne (st : ExecState) (r1 r2 : RegName) (v : LLVMVal) (hne : r1 ≠ r2) :
    lookupReg (bindReg st r2 v) r1 = lookupReg st r1 := by
  unfold lookupReg bindReg; dsimp only [List.lookup]; rw [beq_false_of_ne hne]

private theorem stepLoadI64_ok (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst ptrReg : RegName) (addr : BitVec 64) (rc : BitVec (.i64 : IntWidth).bits)
    (hptr : lookupReg st ptrReg = some (.ptr addr))
    (haccR : accessCheck st.mem addr 8 8 false = none)
    (hlv : loadVal st.mem addr (.int .i64) = .bits .i64 rc) :
    stepInstrWith (runCallWith mod_ fuel) st (.load dst false (.int .i64) (.reg ptrReg) 8) =
      .inr (bindReg st dst (.bits .i64 rc)) := by
  have heff : effectiveAlign (.int .i64) 8 = 8 := by decide
  simp [stepInstrWith, heff, evalOperand, hptr, LLVMType.byteSize, IntWidth.byteSize, haccR, hlv]

private theorem stepStoreI64_ok (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (valReg ptrReg : RegName) (addr : BitVec 64) (val : BitVec (.i64 : IntWidth).bits)
    (hval : lookupReg st valReg = some (.bits .i64 val))
    (hptr : lookupReg st ptrReg = some (.ptr addr))
    (hacc : accessCheck st.mem addr 8 8 true = none) :
    stepInstrWith (runCallWith mod_ fuel) st (.store false (.int .i64) (.reg valReg) (.reg ptrReg) 8) =
      .inr { st with mem := storeTypedVal st.mem addr (.int .i64) (.bits .i64 val) } := by
  have heff : effectiveAlign (.int .i64) 8 = 8 := by decide
  simp [stepInstrWith, heff, evalTypedOperand, evalOperand, hval, hptr, LLVMType.byteSize,
    IntWidth.byteSize, hacc]

theorem headerRc_atomic_threadLocal_inc_equiv (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (ptrReg dst tmp : RegName) (addr : BitVec 64) (rc : BitVec (.i64 : IntWidth).bits)
    (hpd : ptrReg ≠ dst) (hpt : ptrReg ≠ tmp) (hdt : dst ≠ tmp)
    (hptr : lookupReg st ptrReg = some (.ptr addr))
    (hacc : accessCheck st.mem addr 8 8 true = none)
    (hload : st.mem.loadInt? addr .i64 = some rc) :
    ∃ stAt stTl, stepInstr mod_ fuel st (emitAtomicRcInc dst (.reg ptrReg)) = .inr stAt ∧
      execInstrs mod_ fuel st (emitThreadLocalRcInc dst tmp (.reg ptrReg)) = .inr stTl ∧
      stAt.mem = stTl.mem ∧ lookupReg stAt dst = lookupReg stTl dst := by
  let one64 : BitVec (.i64 : IntWidth).bits := 1#64
  have hs1 := stepLoadI64_ok mod_ fuel st dst ptrReg addr rc hptr
    (accessCheck_read_of_write st.mem addr 8 8 hacc) (loadVal_i64_of_loadInt st.mem addr rc hload)
  let st1 := bindReg st dst (.bits .i64 rc)
  have hd1 : lookupReg st1 dst = some (.bits .i64 rc) := lookupReg_bindReg_same st dst _
  have hs2 : stepInstrWith (runCallWith mod_ fuel) st1
      (.add tmp .none .i64 (.reg dst) (.constInt .i64 one64)) =
      .inr (bindReg st1 tmp (.bits .i64 (rc + one64))) := by
    simp [stepInstrWith, evalOperand, hd1, binResult, flagsOverflow]
  let st2 := bindReg st1 tmp (.bits .i64 (rc + one64))
  have hp2 : lookupReg st2 ptrReg = some (.ptr addr) := by
    dsimp only [st2, st1]
    rw [lookupReg_bindReg_ne _ ptrReg tmp _ hpt, lookupReg_bindReg_ne _ ptrReg dst _ hpd]; exact hptr
  have hs3 := stepStoreI64_ok mod_ fuel st2 tmp ptrReg addr (rc + one64)
    (lookupReg_bindReg_same st1 tmp _) hp2 hacc
  let stAt := bindReg { st with mem := st.mem.storeInt addr .i64 (rc + one64) } dst (.bits .i64 rc)
  let stTl : ExecState :=
    { st2 with mem := storeTypedVal st.mem addr (.int .i64) (.bits .i64 (rc + one64)) }
  refine ⟨stAt, stTl, ?_, ?_, ?_, ?_⟩
  · have ha : (8 == 0) = false := by decide
    simp [emitAtomicRcInc, stepInstr, stepInstrWith, ha, evalOperand, hptr, IntWidth.byteSize,
      hacc, hload, evalRMWOp, stAt, one64]
  · dsimp only [emitThreadLocalRcInc, execInstrs, execInstrsWith]
    rw [hs1]; dsimp only
    rw [hs2]; dsimp only
    rw [hs3]; rfl
  · simp [stAt, stTl, bindReg, storeTypedVal, serializeTypedVal, serializeTypedValAux,
      ByteMem.storeInt]
  · dsimp only [stAt, stTl, st2]; rw [lookupReg_bindReg_same]
    let m1 := storeTypedVal st.mem addr (.int .i64) (.bits .i64 (rc + one64))
    have hmem : lookupReg { st2 with mem := m1 } dst = lookupReg st2 dst := rfl
    rw [hmem, lookupReg_bindReg_ne st1 dst tmp _ hdt, hd1]

theorem headerRc_atomic_threadLocal_dec_equiv (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (ptrReg dst tmp : RegName) (addr : BitVec 64) (rc : BitVec (.i64 : IntWidth).bits)
    (hpd : ptrReg ≠ dst) (hpt : ptrReg ≠ tmp) (hdt : dst ≠ tmp)
    (hptr : lookupReg st ptrReg = some (.ptr addr))
    (hacc : accessCheck st.mem addr 8 8 true = none)
    (hload : st.mem.loadInt? addr .i64 = some rc) :
    ∃ stAt stTl, stepInstr mod_ fuel st (emitAtomicRcDec dst (.reg ptrReg)) = .inr stAt ∧
      execInstrs mod_ fuel st (emitThreadLocalRcDec dst tmp (.reg ptrReg)) = .inr stTl ∧
      stAt.mem = stTl.mem ∧ lookupReg stAt dst = lookupReg stTl dst := by
  let one64 : BitVec (.i64 : IntWidth).bits := 1#64
  have hs1 := stepLoadI64_ok mod_ fuel st dst ptrReg addr rc hptr
    (accessCheck_read_of_write st.mem addr 8 8 hacc) (loadVal_i64_of_loadInt st.mem addr rc hload)
  let st1 := bindReg st dst (.bits .i64 rc)
  have hd1 : lookupReg st1 dst = some (.bits .i64 rc) := lookupReg_bindReg_same st dst _
  have hs2 : stepInstrWith (runCallWith mod_ fuel) st1
      (.sub tmp .none .i64 (.reg dst) (.constInt .i64 one64)) =
      .inr (bindReg st1 tmp (.bits .i64 (rc - one64))) := by
    simp [stepInstrWith, evalOperand, hd1, binResult, flagsOverflow]
  let st2 := bindReg st1 tmp (.bits .i64 (rc - one64))
  have hp2 : lookupReg st2 ptrReg = some (.ptr addr) := by
    dsimp only [st2, st1]
    rw [lookupReg_bindReg_ne _ ptrReg tmp _ hpt, lookupReg_bindReg_ne _ ptrReg dst _ hpd]; exact hptr
  have hs3 := stepStoreI64_ok mod_ fuel st2 tmp ptrReg addr (rc - one64)
    (lookupReg_bindReg_same st1 tmp _) hp2 hacc
  let stAt := bindReg { st with mem := st.mem.storeInt addr .i64 (rc - one64) } dst (.bits .i64 rc)
  let stTl : ExecState :=
    { st2 with mem := storeTypedVal st.mem addr (.int .i64) (.bits .i64 (rc - one64)) }
  refine ⟨stAt, stTl, ?_, ?_, ?_, ?_⟩
  · have ha : (8 == 0) = false := by decide
    simp [emitAtomicRcDec, stepInstr, stepInstrWith, ha, evalOperand, hptr, IntWidth.byteSize,
      hacc, hload, evalRMWOp, stAt, one64]
  · dsimp only [emitThreadLocalRcDec, execInstrs, execInstrsWith]
    rw [hs1]; dsimp only
    rw [hs2]; dsimp only
    rw [hs3]; rfl
  · simp [stAt, stTl, bindReg, storeTypedVal, serializeTypedVal, serializeTypedValAux,
      ByteMem.storeInt]
  · dsimp only [stAt, stTl, st2]; rw [lookupReg_bindReg_same]
    let m1 := storeTypedVal st.mem addr (.int .i64) (.bits .i64 (rc - one64))
    have hmem : lookupReg { st2 with mem := m1 } dst = lookupReg st2 dst := rfl
    rw [hmem, lookupReg_bindReg_ne st1 dst tmp _ hdt, hd1]

private theorem filter_ne_not_contains (xs : List Nat) (objId : Nat) :
    (xs.filter (· != objId)).contains objId = false := by
  rw [List.contains_eq_mem, decide_eq_false_iff_not]; intro hmem
  have hne := (List.mem_filter.mp hmem).2; simp at hne

private theorem idsDisjoint_filter_left (xs ys : List Nat) (p : Nat → Bool)
    (h : idsDisjoint xs ys = true) : idsDisjoint (xs.filter p) ys = true := by
  unfold idsDisjoint at h ⊢; rw [List.all_eq_true] at h ⊢
  exact fun x hx => h x (List.mem_filter.mp hx).1

private theorem idsDisjoint_cons_right (xs ys : List Nat) (objId : Nat)
    (h : idsDisjoint xs ys = true) (hnot : xs.contains objId = false) :
    idsDisjoint xs (objId :: ys) = true := by
  unfold idsDisjoint at h ⊢; rw [List.all_eq_true] at h ⊢; intro x hx
  have hne : objId ≠ x := by
    intro heq; subst heq
    rw [List.contains_eq_mem, decide_eq_false_iff_not] at hnot; exact hnot hx
  rw [List.contains_cons, beq_false_of_ne hne.symm, Bool.false_or]; exact h x hx

private theorem idsDisjoint_cons_left (xs ys : List Nat) (objId : Nat)
    (h : idsDisjoint xs ys = true) (hnot : ys.contains objId = false) :
    idsDisjoint (objId :: xs) ys = true := by
  unfold idsDisjoint at h ⊢; rw [List.all_cons, hnot]; exact h

theorem sendableTransfer_unique_sound (ch ch' : SendableChannelState) (objId : Nat)
    (v : VarId) (code : LNIRCode) (hdrRc : Int) (exclusive : Bool)
    (hdisj : channelDisjoint ch = true)
    (hsend : sendSlot ch objId v code hdrRc exclusive = some ch') :
    codeEscapes v code = false ∧ ch'.senderOwned.contains objId = false ∧
      ((hdrRc = 0 ∧ exclusive = true) ∨ 0 < hdrRc) ∧ channelDisjoint ch' = true := by
  unfold sendSlot at hsend
  by_cases hguard : (!checkThreadLocalNonEscaping v code || !(ch.senderOwned.contains objId) ||
      ch.inFlight.any (·.objId == objId) || ch.receiverOwned.contains objId) = true
  · rw [ite_eq_left hguard] at hsend; cases hsend
  · rw [ite_eq_right hguard] at hsend
    have hg1 := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hguard)
    have hg3 := Bool.or_eq_false_iff.mp (Bool.or_eq_false_iff.mp hg1.1).1
    have hcode : codeEscapes v code = false := by
      unfold checkThreadLocalNonEscaping at hg3
      cases hc : codeEscapes v code <;> simp_all
    unfold channelDisjoint at hdisj
    simp only [Bool.and_eq_true] at hdisj
    rcases hdisj with ⟨⟨⟨hsf, hsr⟩, hfr⟩, hwf⟩
    by_cases huniq : (hdrRc == 0 && exclusive) = true
    · rw [ite_eq_left huniq] at hsend
      injection hsend with hch; subst hch
      have hu := (Bool.and_eq_true _ _).mp huniq
      refine ⟨hcode, filter_ne_not_contains ch.senderOwned objId,
        Or.inl ⟨of_decide_eq_true hu.1, hu.2⟩, ?_⟩
      unfold channelDisjoint
      simp only [List.map_cons, List.all_cons, Bool.and_eq_true]
      exact ⟨⟨⟨idsDisjoint_cons_right _ _ objId (idsDisjoint_filter_left _ _ _ hsf)
        (filter_ne_not_contains ch.senderOwned objId), idsDisjoint_filter_left _ _ _ hsr⟩,
        idsDisjoint_cons_left _ _ objId hfr hg1.2⟩, ⟨rfl, hwf⟩⟩
    · rw [ite_eq_right huniq] at hsend
      by_cases hpos : decide (0 < hdrRc) = true
      · rw [ite_eq_left hpos] at hsend
        injection hsend with hch; subst hch
        have hlt : 0 < hdrRc := of_decide_eq_true hpos
        have hneg : decide (-hdrRc < 0) = true := decide_eq_true (by omega)
        refine ⟨hcode, filter_ne_not_contains ch.senderOwned objId, Or.inr hlt, ?_⟩
        unfold channelDisjoint
        simp only [List.map_cons, List.all_cons, Bool.and_eq_true]
        refine ⟨⟨⟨idsDisjoint_cons_right _ _ objId (idsDisjoint_filter_left _ _ _ hsf)
          (filter_ne_not_contains ch.senderOwned objId), idsDisjoint_filter_left _ _ _ hsr⟩,
          idsDisjoint_cons_left _ _ objId hfr hg1.2⟩, ⟨?_, hwf⟩⟩
        unfold slotWellFormed; rw [hneg]; rfl
      · rw [ite_eq_right hpos] at hsend; cases hsend

private theorem agg_toList (vs : List LLVMVal) : (LLVMVal.agg vs).toList? = some vs := by
  induction vs with
  | nil => rfl
  | cons v rest ih => unfold LLVMVal.agg at ih ⊢; simp [LLVMVal.toList?, ih]

private theorem agg_not_poison (vs : List LLVMVal) : isPoison (LLVMVal.agg vs) = false := by
  cases vs <;> rfl

private theorem simdLanes_lt_u32 (kind : PortableSimdKind) : kind.lanes < 2 ^ 32 := by
  cases kind <;> decide

theorem portableSimdVec_lane_roundtrip_sound (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (vecReg midReg outReg : RegName) (kind : PortableSimdKind) (vs : List LLVMVal)
    (elemOp : Operand) (lane : UInt64) (hvec : lookupReg st vecReg = some (LLVMVal.agg vs))
    (hlane : lane.toNat < kind.lanes) (hlen : lane.toNat < vs.length) :
    ∃ st', execInstrs mod_ fuel st
        [ lowerSimdInsertLane midReg kind (.reg vecReg) elemOp lane
        , lowerSimdExtractLane outReg kind (.reg midReg) lane ] = .inr st' ∧
      lookupReg st' outReg = some (evalTypedOperand st kind.llvmLaneType elemOp) := by
  let idxBv : BitVec IntWidth.i32.bits := BitVec.ofNat 32 lane.toNat
  have hb : idxBv.toNat = lane.toNat := by
    change (BitVec.ofNat 32 lane.toNat).toNat = lane.toNat; rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_trans hlane (simdLanes_lt_u32 kind))
  have hnotle : ¬kind.lanes ≤ lane.toNat := Nat.not_le_of_lt hlane
  let elemVal := evalTypedOperand st kind.llvmLaneType elemOp
  have hins : stepInstrWith (runCallWith mod_ fuel) st
      (lowerSimdInsertLane midReg kind (.reg vecReg) elemOp lane) =
      .inr (bindReg st midReg (LLVMVal.agg (vs.set lane.toNat elemVal))) := by
    change stepInstrWith (runCallWith mod_ fuel) st
        (.insertelement midReg kind.lanes kind.llvmLaneType (.reg vecReg) elemOp .i32
          (.constInt .i32 idxBv)) = .inr (bindReg st midReg (LLVMVal.agg (vs.set lane.toNat elemVal)))
    simp [stepInstrWith, evalOperand, evalTypedOperand, hb, hnotle, hvec, agg_not_poison,
      agg_toList, elemVal]
  let stMid := bindReg st midReg (LLVMVal.agg (vs.set lane.toNat elemVal))
  have hmid : lookupReg stMid midReg = some (LLVMVal.agg (vs.set lane.toNat elemVal)) :=
    lookupReg_bindReg_same st midReg _
  have hext : stepInstrWith (runCallWith mod_ fuel) stMid
      (lowerSimdExtractLane outReg kind (.reg midReg) lane) =
      .inr (bindReg stMid outReg elemVal) := by
    change stepInstrWith (runCallWith mod_ fuel) stMid
        (.extractelement outReg kind.lanes kind.llvmLaneType (.reg midReg) .i32
          (.constInt .i32 idxBv)) = .inr (bindReg stMid outReg elemVal)
    simp [stepInstrWith, evalOperand, evalTypedOperand, hb, hnotle, hmid, agg_not_poison,
      agg_toList, List.getD_eq_getElem?_getD, List.getElem?_set_self hlen]
  refine ⟨bindReg stMid outReg elemVal, ?_, lookupReg_bindReg_same _ outReg elemVal⟩
  dsimp only [execInstrs, execInstrsWith]; rw [hins]; dsimp only
  rw [hext]

theorem portableSimdVec_oob_poison (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (kind : PortableSimdKind) (vecOp : Operand) (lane : UInt64)
    (hoob : kind.lanes ≤ lane.toNat) (hu32 : lane.toNat < 4294967296) :
    stepInstr mod_ fuel st (lowerSimdExtractLane dst kind vecOp lane) =
      .inr (bindReg st dst .poison) := by
  let idxBv : BitVec IntWidth.i32.bits := BitVec.ofNat 32 lane.toNat
  have hb : idxBv.toNat = lane.toNat := by
    change (BitVec.ofNat 32 lane.toNat).toNat = lane.toNat; rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hu32
  change stepInstr mod_ fuel st
      (.extractelement dst kind.lanes kind.llvmLaneType vecOp .i32 (.constInt .i32 idxBv)) =
    .inr (bindReg st dst .poison)
  simp [stepInstr, stepInstrWith, evalOperand, hb, hoob]

theorem disjoint_fields_storeInt_noninterference (m : ByteMem) (base : BitVec 64)
    (f1 f2 : PlacedUnboxedField) (v1 v2 : BitVec 64) (hsz1 : f1.size = 8)
    (hdisj : fieldByteEnd f1 ≤ f2.offset) (hfit : base.toNat + f2.offset < 2 ^ 64) :
    let addr1 := BitVec.ofNat 64 (base.toNat + f1.offset)
    let addr2 := BitVec.ofNat 64 (base.toNat + f2.offset)
    let m' := (m.storeInt addr1 .i64 v1).storeInt addr2 .i64 v2
    m'.loadInt? addr1 .i64 = some v1 ∧ m'.loadInt? addr2 .i64 = some v2 := by
  intro addr1 addr2 m'; unfold fieldByteEnd at hdisj
  have ha1 : addr1.toNat = base.toNat + f1.offset := Nat.mod_eq_of_lt (by omega)
  have ha2 : addr2.toNat = base.toNat + f2.offset := Nat.mod_eq_of_lt hfit
  have hrd : rangesDisjoint addr2.toNat (IntWidth.i64).byteSize
      addr1.toNat (IntWidth.i64).byteSize = true := by
    unfold rangesDisjoint; simp only [IntWidth.byteSize, ha1, ha2]
    exact decide_eq_true (Or.inr (by omega))
  refine ⟨?_, ByteMem.loadInt?_storeInt_same _ addr2 .i64 v2⟩
  rw [ByteMem.loadInt?_storeInt_disjoint _ addr2 .i64 v2 addr1 .i64 hrd]
  exact ByteMem.loadInt?_storeInt_same m addr1 .i64 v1

theorem unboxedRegion_pipeline_nonvacuous (fuel : Nat) :
    let layout := mkUnboxedStructLayout "pair"
      [{ name := "x", kind := .u64 }, { name := "y", kind := .u64 }]
    let slice : BorrowedRegionSlice :=
      { ptrVar := 3, view := { backingLen := 16, offset := 0, len := 16 }, own := .borrowed }
    let env := (VarEnv.empty.bind 2 (.u64 8)).bind 4 (.rawPtrId 0)
    let st : HeapState :=
      { buffers := [{ id := 0, exclusive := true, data := #[10, 42, 99, 7, 5, 3, 2, 1, 8, 9] }]
        nextId := 1 }
    let code := elideMarkMtAndZeroRc (lowerUnboxedRegionCode 0 1 2 layout slice 4 (.ret 0))
    layoutWellFormed layout = true ∧
      lowerUnboxedRegionRcFree 0 1 2 layout slice 4 = true ∧
      evalCode fuel env st code = .ok (.u64 42, st) := by
  refine ⟨by decide, by decide, ?_⟩
  rfl

end LeanNative.Proofs
