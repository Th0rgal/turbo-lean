import LeanNative.IR.UnboxedRegion
import LeanNative.Semantics.Refinement
import LeanNative.Transform.OwnershipRC

set_option autoImplicit false

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend.LLVMAst
open LeanNative.Transform

/-! ## Track D2 Soundness Proofs: Unboxed Regions, Portable SIMD & Thread-Local RC

Zero `def`, zero `structure`, zero `inductive` in this file. Standard axioms only.
-/

private theorem regionAlignUp_mod_zero (n a : Nat) (ha : 0 < a) :
    regionAlignUp n a % a = 0 := by
  unfold regionAlignUp
  have hne : (a == 0) = false := beq_false_of_ne (Nat.ne_of_gt ha)
  rw [hne]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact Nat.mul_mod_right a ((n + (a - 1)) / a)

private theorem le_regionAlignUp (n a : Nat) :
    n ≤ regionAlignUp n a := by
  unfold regionAlignUp
  by_cases ha : a = 0
  · subst ha
    simp
  · have hpos : 0 < a := Nat.pos_of_ne_zero ha
    have hne : (a == 0) = false := beq_false_of_ne ha
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hdiv := Nat.div_add_mod (n + (a - 1)) a
    have hmod := Nat.mod_lt (n + (a - 1)) hpos
    omega

private theorem scalarKind_align_pos (k : UnboxedScalarKind) :
    0 < k.naturalAlign := by
  cases k <;> decide

private theorem scalarKind_size_eq_align (k : UnboxedScalarKind) :
    k.byteSize = k.naturalAlign := by
  cases k <;> rfl

private theorem placeUnboxedFieldsFrom_align_pos (fields : List UnboxedField) (off maxA : Nat)
    (hmax : 0 < maxA) :
    0 < (placeUnboxedFieldsFrom fields off maxA).2.2 := by
  induction fields generalizing off maxA with
  | nil => exact hmax
  | cons f fs ih =>
    unfold placeUnboxedFieldsFrom
    dsimp only
    exact ih _ _ (Nat.lt_of_lt_of_le hmax (Nat.le_max_left maxA f.kind.naturalAlign))

private theorem placeUnboxedFieldsFrom_bounds (fields : List UnboxedField) (off maxA : Nat) :
    off ≤ (placeUnboxedFieldsFrom fields off maxA).2.1 ∧
      ∀ g ∈ (placeUnboxedFieldsFrom fields off maxA).1,
        off ≤ g.offset ∧ fieldByteEnd g ≤ (placeUnboxedFieldsFrom fields off maxA).2.1 := by
  induction fields generalizing off maxA with
  | nil =>
    refine ⟨Nat.le_refl off, ?_⟩
    intro g hg
    cases hg
  | cons f fs ih =>
    unfold placeUnboxedFieldsFrom placeUnboxedField fieldByteEnd
    dsimp only
    have hoff : off ≤ regionAlignUp off f.kind.naturalAlign :=
      le_regionAlignUp off f.kind.naturalAlign
    have ⟨hrest_le, hrest_mem⟩ :=
      ih (regionAlignUp off f.kind.naturalAlign + f.kind.byteSize)
        (Nat.max maxA f.kind.naturalAlign)
    refine ⟨Nat.le_trans (Nat.le_trans hoff (Nat.le_add_right _ _)) hrest_le, ?_⟩
    intro g hg
    simp only [List.mem_cons] at hg
    cases hg with
    | inl hhead =>
      subst hhead
      exact ⟨hoff, hrest_le⟩
    | inr htail =>
      have ⟨hgoff, hgend⟩ := hrest_mem g htail
      exact ⟨Nat.le_trans (Nat.le_trans hoff (Nat.le_add_right _ _)) hgoff, hgend⟩

private theorem placeUnboxedFieldsFrom_disjoint (fields : List UnboxedField) (off maxA : Nat) :
    layoutFieldsDisjoint (placeUnboxedFieldsFrom fields off maxA).1 = true := by
  induction fields generalizing off maxA with
  | nil => rfl
  | cons f fs ih =>
    unfold placeUnboxedFieldsFrom layoutFieldsDisjoint
    rw [Bool.and_eq_true]
    refine ⟨?_, ih (placeUnboxedField off f).2 (Nat.max maxA f.kind.naturalAlign)⟩
    rw [List.all_eq_true]
    intro g hg
    have ⟨_, hmem⟩ :=
      placeUnboxedFieldsFrom_bounds fs (placeUnboxedField off f).2 (Nat.max maxA f.kind.naturalAlign)
    have ⟨hgoff, _⟩ := hmem g hg
    have hend : fieldByteEnd (placeUnboxedField off f).1 = (placeUnboxedField off f).2 := rfl
    exact decide_eq_true (hend ▸ hgoff)

private theorem placeUnboxedFieldsFrom_aligned (fields : List UnboxedField) (off maxA : Nat) :
    layoutFieldsAligned (placeUnboxedFieldsFrom fields off maxA).1 = true := by
  induction fields generalizing off maxA with
  | nil => rfl
  | cons f fs ih =>
    unfold placeUnboxedFieldsFrom layoutFieldsAligned
    dsimp only
    simp only [List.all_cons, Bool.and_eq_true]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · unfold placeUnboxedField
      exact decide_eq_true (scalarKind_align_pos f.kind)
    · unfold placeUnboxedField
      exact decide_eq_true (regionAlignUp_mod_zero off f.kind.naturalAlign (scalarKind_align_pos f.kind))
    · unfold placeUnboxedField
      exact decide_eq_true (scalarKind_size_eq_align f.kind)
    · exact ih (placeUnboxedField off f).2 (Nat.max maxA f.kind.naturalAlign)

/-- Every `mkUnboxedStructLayout` produces a zero-header, naturally aligned, pairwise-disjoint
    `repr(C)` layout whose stride is a multiple of the struct alignment. -/
theorem unboxedStructLayout_disjoint_aligned (name : String) (fields : List UnboxedField) :
    layoutWellFormed (mkUnboxedStructLayout name fields) = true := by
  unfold mkUnboxedStructLayout layoutWellFormed
  have halign : 0 < (placeUnboxedFieldsFrom fields 0 1).2.2 :=
    placeUnboxedFieldsFrom_align_pos fields 0 1 (by decide)
  have hstride :
      regionAlignUp (placeUnboxedFieldsFrom fields 0 1).2.1
          (placeUnboxedFieldsFrom fields 0 1).2.2 %
        (placeUnboxedFieldsFrom fields 0 1).2.2 = 0 :=
    regionAlignUp_mod_zero _ _ halign
  have hdisj := placeUnboxedFieldsFrom_disjoint fields 0 1
  have halgn := placeUnboxedFieldsFrom_aligned fields 0 1
  have ⟨_, hmem⟩ := placeUnboxedFieldsFrom_bounds fields 0 1
  have hfit :
      (placeUnboxedFieldsFrom fields 0 1).1.all
        (fun f => decide (fieldByteEnd f ≤
          regionAlignUp (placeUnboxedFieldsFrom fields 0 1).2.1
            (placeUnboxedFieldsFrom fields 0 1).2.2)) = true := by
    rw [List.all_eq_true]
    intro g hg
    have ⟨_, hgend⟩ := hmem g hg
    have hup := le_regionAlignUp (placeUnboxedFieldsFrom fields 0 1).2.1
      (placeUnboxedFieldsFrom fields 0 1).2.2
    exact decide_eq_true (Nat.le_trans hgend hup)
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨rfl, decide_eq_true halign⟩, decide_eq_true hstride⟩, hdisj⟩, halgn⟩, hfit⟩

/-- Lowered unboxed-region reads never emit `allocCtor`, `incRef`, or `decRef`. -/
theorem lowerUnboxedRegionRcFree_true
    (dst posVar idxVar baseVar : VarId) (layout : UnboxedStructLayout)
    (slice : BorrowedRegionSlice) :
    lowerUnboxedRegionRcFree dst posVar idxVar layout slice baseVar = true := by
  cases layout with
  | mk name fields stride align header =>
    cases fields <;> rfl

private theorem evalScalar_preserves_state (env : VarEnv) (st st' : HeapState)
    (se : ScalarExpr) (v : Val) (h : evalExpr env st (.scalar se) = .ok (v, st')) :
    st' = st := by
  dsimp only [evalExpr] at h
  cases hsc : evalScalarExpr env se with
  | error _ => rw [hsc] at h; contradiction
  | ok sv =>
    rw [hsc] at h
    exact (Prod.mk.inj (Except.ok.inj h)).2.symm

private theorem evalRawLoad_preserves_state (env : VarEnv) (st st' : HeapState)
    (p i : VarId) (ty : LNIRType) (v : Val) (h : evalExpr env st (.rawLoad p i ty) = .ok (v, st')) :
    st' = st := by
  dsimp only [evalExpr] at h
  cases hp : env p with
  | none => rw [hp] at h; contradiction
  | some pv =>
    rw [hp] at h
    cases pv with
    | rawPtrId bufId =>
      cases hi : env i with
      | none => rw [hi] at h; contradiction
      | some iv =>
        rw [hi] at h
        cases iv with
        | u64 idx =>
          dsimp only at h
          cases hrd : st.readElem bufId idx.toNat with
          | error _ => rw [hrd] at h; contradiction
          | ok w =>
            rw [hrd] at h
            exact (Prod.mk.inj (Except.ok.inj h)).2.symm
        | u256 _ | bool _ | tuple _ | objPtr _ | sarrayId _ | rawPtrId _ | storageMapId _ | unit =>
          contradiction
    | sarrayId bufId =>
      cases hi : env i with
      | none => rw [hi] at h; contradiction
      | some iv =>
        rw [hi] at h
        cases iv with
        | u64 idx =>
          dsimp only at h
          cases hrd : st.readElem bufId idx.toNat with
          | error _ => rw [hrd] at h; contradiction
          | ok w =>
            rw [hrd] at h
            exact (Prod.mk.inj (Except.ok.inj h)).2.symm
        | u256 _ | bool _ | tuple _ | objPtr _ | sarrayId _ | rawPtrId _ | storageMapId _ | unit =>
          contradiction
    | u64 _ | u256 _ | bool _ | tuple _ | objPtr _ | storageMapId _ | unit =>
      cases hi : env i with
      | none => rw [hi] at h; contradiction
      | some _ => rw [hi] at h; contradiction

/-- Evaluating a lowered unboxed-region load preserves the entire `HeapState` (`st' = st`,
    so `st'.nextId = st.nextId`, zero heap objects are allocated, and zero refcounts change). -/
theorem lowerUnboxedRegionCode_sound
    (dst posVar idxVar baseVar : VarId) (layout : UnboxedStructLayout)
    (slice : BorrowedRegionSlice) (fuel : Nat) (env : VarEnv) (st : HeapState)
    (v : Val) (st' : HeapState)
    (h : evalCode fuel env st
      (lowerUnboxedRegionCode dst posVar idxVar layout slice baseVar (.ret dst)) = .ok (v, st')) :
    st' = st ∧ st'.nextId = st.nextId := by
  have heq : st' = st := by
    revert h
    cases layout with
    | mk name fields stride align header =>
      cases fields with
      | nil =>
        intro h
        unfold lowerUnboxedRegionCode lowerBorrowedSliceLoad at h
        simp only [evalCode] at h
        cases he1 : evalExpr env st
            (.scalar (.binOp .add (.constU64 slice.view.offset.toUInt64) (.var idxVar))) with
        | error _ => rw [he1] at h; contradiction
        | ok p1 =>
          rcases p1 with ⟨v1, st1⟩
          rw [he1] at h
          have hst1 := evalScalar_preserves_state env st st1 _ v1 he1
          subst hst1
          dsimp only at h
          cases he2 : evalExpr (env.bind posVar v1) st1 (.rawLoad slice.ptrVar posVar .i64) with
          | error _ => rw [he2] at h; contradiction
          | ok p2 =>
            rcases p2 with ⟨v2, st2⟩
            rw [he2] at h
            have hst2 := evalRawLoad_preserves_state (env.bind posVar v1) st1 st2
              slice.ptrVar posVar .i64 v2 he2
            subst hst2
            simp only [VarEnv.bind_self] at h
            exact (Prod.mk.inj (Except.ok.inj h)).2.symm
      | cons f fs =>
        intro h
        unfold lowerUnboxedRegionCode lowerUnboxedFieldLoad at h
        simp only [evalCode] at h
        cases he1 : evalExpr env st
            (.scalar (.binOp .add (.var idxVar) (.constU64 f.offset.toUInt64))) with
        | error _ => rw [he1] at h; contradiction
        | ok p1 =>
          rcases p1 with ⟨v1, st1⟩
          rw [he1] at h
          have hst1 := evalScalar_preserves_state env st st1 _ v1 he1
          subst hst1
          dsimp only at h
          cases he2 : evalExpr (env.bind posVar v1) st1
              (.rawLoad baseVar posVar f.field.kind.lnirType) with
          | error _ => rw [he2] at h; contradiction
          | ok p2 =>
            rcases p2 with ⟨v2, st2⟩
            rw [he2] at h
            have hst2 := evalRawLoad_preserves_state (env.bind posVar v1) st1 st2
              baseVar posVar f.field.kind.lnirType v2 he2
            subst hst2
            simp only [VarEnv.bind_self] at h
            exact (Prod.mk.inj (Except.ok.inj h)).2.symm
  exact ⟨heq, heq ▸ rfl⟩

/-- Checked borrowed sub-slices preserve `borrowedSliceValid` and adjust `(offset, len)` in-place. -/
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
    refine ⟨?_, rfl, rfl⟩
    simp [borrowedSliceValid, hv, hslice.2]
  · simp only [hgate, Bool.false_eq_true, ↓reduceIte] at h
    cases h

private theorem shadow_and_false (cond a b : Bool) (h : (cond && a) = false)
    (hab : a = false → b = false) :
    (cond && b) = false := by
  cases cond with
  | false => rfl
  | true => exact hab h

private theorem elideBorrowed_preserves_nonEscape (v : VarId) (code : LNIRCode)
    (h : codeEscapes v code = false) :
    codeEscapes v (Transform.elideBorrowedAndThreadLocalRC v code) = false := by
  induction code with
  | letBind dst ty val k ih =>
    unfold codeEscapes at h
    rw [Bool.or_eq_false_iff] at h
    rcases h with ⟨hval, hk⟩
    have htail : (dst != v && codeEscapes v (Transform.elideBorrowedAndThreadLocalRC v k)) = false :=
      shadow_and_false (dst != v) _ _ hk ih
    cases val with
    | call fn args rty ext =>
      simp only [Transform.elideBorrowedAndThreadLocalRC]
      by_cases hfn : (fn == "lean_mark_mt") = true
      · rw [ite_eq_left hfn]
        simp only [codeEscapes, exprMentions, Bool.false_or]
        exact htail
      · rw [ite_eq_right hfn]
        simp only [codeEscapes, Bool.or_eq_false_iff]
        exact ⟨hval, htail⟩
    | scalar _ | constU256 _ | mulDivDown _ _ _ | mulDivUp _ _ _ | storageLoad _ _
    | storageStore _ _ _ | mkTuple _ | projTuple _ _ | allocCtor _ _ _ | ctorGetObj _ _
    | ctorGetScalar _ _ _ | isExclusive _ | sarrayLen _ | sarrayDataPtr _ _
    | sarrayEnsureExclusive _ _ | sarrayGet _ _ _ | sarraySet _ _ _ _ | rawLoad _ _ _
    | boxScalar _ _ | unboxScalar _ _ =>
      simp only [Transform.elideBorrowedAndThreadLocalRC, codeEscapes, Bool.or_eq_false_iff]
      exact ⟨hval, htail⟩
  | rawStore p i x ty k ih =>
    simp only [codeEscapes, Bool.or_eq_false_iff] at h
    simp only [Transform.elideBorrowedAndThreadLocalRC, codeEscapes, Bool.or_eq_false_iff]
    exact ⟨⟨⟨h.1.1.1, h.1.1.2⟩, h.1.2⟩, ih h.2⟩
  | incRef ov c k ih =>
    simp only [codeEscapes, Bool.or_eq_false_iff] at h
    simp only [Transform.elideBorrowedAndThreadLocalRC]
    by_cases hcond : (ov == v || c == 0) = true
    · rw [ite_eq_left hcond]
      exact ih h.2
    · rw [ite_eq_right hcond]
      simp only [codeEscapes, Bool.or_eq_false_iff]
      exact ⟨h.1, ih h.2⟩
  | decRef ov c k ih =>
    simp only [codeEscapes, Bool.or_eq_false_iff] at h
    simp only [Transform.elideBorrowedAndThreadLocalRC]
    by_cases hcond : (ov == v || c == 0) = true
    · rw [ite_eq_left hcond]
      exact ih h.2
    · rw [ite_eq_right hcond]
      simp only [codeEscapes, Bool.or_eq_false_iff]
      exact ⟨h.1, ih h.2⟩
  | ite c t e iht ihe =>
    simp only [codeEscapes, Bool.or_eq_false_iff] at h
    simp only [Transform.elideBorrowedAndThreadLocalRC, codeEscapes, Bool.or_eq_false_iff]
    exact ⟨⟨h.1.1, iht h.1.2⟩, ihe h.2⟩
  | seqFor iv lo hi av init aty step k ihs ihk =>
    simp only [codeEscapes, Bool.or_eq_false_iff] at h
    simp only [Transform.elideBorrowedAndThreadLocalRC, codeEscapes, Bool.or_eq_false_iff]
    exact ⟨⟨⟨⟨h.1.1.1.1, h.1.1.1.2⟩, h.1.1.2⟩, ihs h.1.2⟩, ihk h.2⟩
  | parFor ov len ins ety kern k ih =>
    simp only [codeEscapes, Bool.or_eq_false_iff] at h
    simp only [Transform.elideBorrowedAndThreadLocalRC, codeEscapes, Bool.or_eq_false_iff]
    exact ⟨⟨h.1.1, h.1.2⟩, ih h.2⟩
  | ret x =>
    simp only [Transform.elideBorrowedAndThreadLocalRC]
    exact h
  | unreachable =>
    rfl

/-- Thread-local single-owner escape soundness: when `checkThreadLocalNonEscaping v code = true`,
    `v` remains non-escaping after replacing `lean_mark_mt` and eliding RC on `v`. -/
theorem threadLocalEscape_no_mark_mt_sound (v : VarId) (code : LNIRCode)
    (h : checkThreadLocalNonEscaping v code = true) :
    codeEscapes v code = false ∧
      codeEscapes v (elideBorrowedAndThreadLocalRC v code) = false := by
  have hno : codeEscapes v code = false := by
    unfold checkThreadLocalNonEscaping at h
    simpa using h
  exact ⟨hno, elideBorrowed_preserves_nonEscape v code hno⟩

/-- Sendable unique ownership transfer soundness: `checkSendableTransfer` guarantees exclusive
    ownership (`rc = 1`) and zero syntactic escape of `v` in `code`. -/
theorem sendableTransfer_unique_sound (v : VarId) (code : LNIRCode) (rc : Nat)
    (h : checkSendableTransfer v code rc = true) :
    rc = 1 ∧ codeEscapes v code = false := by
  unfold checkSendableTransfer at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  exact h

/-- Portable SIMD lane round-trip soundness: inserting `elem` at in-bounds lane `i` and
    extracting lane `i` yields `some elem`. -/
theorem portableSimdVec_lane_roundtrip_sound (vs : List LLVMVal) (i : Nat) (elem : LLVMVal)
    (hlt : i < vs.length) :
    simdLaneGet (simdLaneSet vs i elem) i = some elem := by
  unfold simdLaneGet simdLaneSet
  exact List.getElem?_set_self hlt

/-- End-to-end non-vacuity witness: a concrete 2-field `repr(C)` struct layout and borrowed
    slice lower to RC-free `LNIRCode`, pass `elideMarkMtAndZeroRc`, and evaluate under `evalCode`
    to `.ok (.u64 42, st)` without incrementing `nextId` or mutating `HeapState`. -/
theorem unboxedRegion_pipeline_nonvacuous (fuel : Nat) :
    let layout := mkUnboxedStructLayout "pair"
      [{ name := "x", kind := .u64 }, { name := "y", kind := .u64 }]
    let slice : BorrowedRegionSlice :=
      { ptrVar := 3, view := { backingLen := 16, offset := 0, len := 16 }, own := .borrowed }
    let env := (VarEnv.empty.bind 2 (.u64 1)).bind 4 (.rawPtrId 0)
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
