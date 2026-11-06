import LeanNative.IR.UnboxedRegion
import LeanNative.Semantics.Eval
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

private theorem lowerBorrowedSliceLoad_no_rc (dst idxVar posVar : VarId)
    (s : BorrowedRegionSlice) (k code : LNIRCode)
    (hk : codeHasHeapRc k = false)
    (hl : lowerBorrowedSliceLoad dst idxVar posVar s k = some code) :
    codeHasHeapRc code = false := by
  unfold lowerBorrowedSliceLoad at hl
  split at hl
  · cases hl
    simp [codeHasHeapRc, hk]
  · cases hl

private theorem lowerUnboxedFieldLoad_no_rc (dst baseVar idxVar posVar : VarId)
    (field : PlacedUnboxedField) (k code : LNIRCode)
    (hk : codeHasHeapRc k = false)
    (hl : lowerUnboxedFieldLoad dst baseVar idxVar posVar field k = some code) :
    codeHasHeapRc code = false := by
  unfold lowerUnboxedFieldLoad at hl
  split at hl
  · cases hl
    by_cases hfull : (field.size == 8 && field.offset % 8 == 0) = true
    · simp [codeHasHeapRc, hk, hfull]
    · simp [codeHasHeapRc, hk, hfull]
  · cases hl

private theorem lowerUnboxedStructLoadsAux_no_rc (baseVar idxVar posVar : VarId)
    (fields : List PlacedUnboxedField) (dsts : List VarId) (k code : LNIRCode)
    (hk : codeHasHeapRc k = false)
    (hl : lowerUnboxedStructLoadsAux baseVar idxVar posVar fields dsts k = some code) :
    codeHasHeapRc code = false := by
  induction fields generalizing dsts k code with
  | nil =>
    cases dsts <;> simp [lowerUnboxedStructLoadsAux] at hl
    all_goals (subst hl; exact hk)
  | cons f fs ih =>
    cases dsts with
    | nil =>
      simp [lowerUnboxedStructLoadsAux] at hl
      subst hl
      exact hk
    | cons d ds =>
      unfold lowerUnboxedStructLoadsAux at hl
      cases htail : lowerUnboxedStructLoadsAux baseVar idxVar posVar fs ds k with
      | none => simp [htail] at hl
      | some tail =>
        rw [htail] at hl
        dsimp only [Bind.bind, Option.bind] at hl
        exact lowerUnboxedFieldLoad_no_rc d baseVar idxVar posVar f tail code
          (ih ds k tail hk htail) hl

theorem lowerUnboxedRegionRcFree_true (dst posVar idxVar baseVar : VarId)
    (layout : UnboxedStructLayout) (slice : BorrowedRegionSlice) (code : LNIRCode)
    (hl : lowerUnboxedRegionCode dst posVar idxVar layout slice baseVar (.ret dst) = some code) :
    lowerUnboxedRegionRcFree dst posVar idxVar layout slice baseVar = true := by
  have hrc : codeHasHeapRc code = false := by
    unfold lowerUnboxedRegionCode at hl
    cases hfields : layout.fields with
    | nil =>
      rw [hfields] at hl
      exact lowerBorrowedSliceLoad_no_rc dst idxVar posVar slice (.ret dst) code rfl hl
    | cons f fs =>
      rw [hfields] at hl
      unfold lowerUnboxedStructLoads at hl
      rw [hfields] at hl
      exact lowerUnboxedStructLoadsAux_no_rc baseVar idxVar posVar (f :: fs)
        ((List.range (f :: fs).length).map (fun i => dst + i)) (.ret dst) code rfl hl
  unfold lowerUnboxedRegionRcFree
  rw [hl]
  dsimp only
  rw [hrc]
  rfl

private theorem evalLetScalar_preserves_heap (fuel : Nat) (env : VarEnv) (st : HeapState)
    (dst : VarId) (ty : LNIRType) (se : ScalarExpr) (k : LNIRCode)
    (hk : ∀ env' v' st1, evalCode fuel env' st k = .ok (v', st1) → st1 = st) :
    ∀ v st', evalCode fuel env st (.letBind dst ty (.scalar se) k) = .ok (v, st') → st' = st := by
  intro v st' h
  dsimp only [evalCode] at h
  cases he : evalExpr env st (.scalar se) with
  | error _ => rw [he] at h; contradiction
  | ok pair =>
    rcases pair with ⟨bound, st1⟩
    rw [he] at h
    have hst1 := evalScalar_preserves_heap env st st1 se bound he
    subst hst1
    exact hk (env.bind dst bound) v st' h

private theorem evalLetRawLoad_preserves_heap (fuel : Nat) (env : VarEnv) (st : HeapState)
    (dst p i : VarId) (ty rty : LNIRType) (k : LNIRCode)
    (hk : ∀ env' v' st1, evalCode fuel env' st k = .ok (v', st1) → st1 = st) :
    ∀ v st', evalCode fuel env st (.letBind dst ty (.rawLoad p i rty) k) = .ok (v, st') →
      st' = st := by
  intro v st' h
  dsimp only [evalCode] at h
  cases he : evalExpr env st (.rawLoad p i rty) with
  | error _ => rw [he] at h; contradiction
  | ok pair =>
    rcases pair with ⟨bound, st1⟩
    rw [he] at h
    have hst1 := evalRawLoad_preserves_heap env st st1 p i rty bound he
    subst hst1
    exact hk (env.bind dst bound) v st' h

private theorem evalIte_unreachable_preserves_heap (fuel : Nat) (env : VarEnv) (st : HeapState)
    (c : VarId) (k : LNIRCode)
    (hk : ∀ env' v' st1, evalCode fuel env' st k = .ok (v', st1) → st1 = st) :
    ∀ v st', evalCode fuel env st (.ite c .unreachable k) = .ok (v, st') → st' = st := by
  intro v st' h
  dsimp only [evalCode] at h
  cases hc : env c with
  | none => rw [hc] at h; contradiction
  | some vc =>
    rw [hc] at h
    cases vc with
    | bool b =>
      cases b
      · exact hk env v st' h
      · contradiction
    | u64 n =>
      dsimp only at h
      by_cases hn : (n != 0) = true
      · rw [ite_eq_left hn] at h; contradiction
      · rw [ite_eq_right hn] at h; exact hk env v st' h
    | u256 w =>
      dsimp only at h
      by_cases hw : (w != UInt256.zero) = true
      · rw [ite_eq_left hw] at h; contradiction
      · rw [ite_eq_right hw] at h; exact hk env v st' h
    | _ => contradiction

private theorem lowerBorrowedSliceLoad_preserves_heap (dst idxVar posVar : VarId)
    (s : BorrowedRegionSlice) (k code : LNIRCode) (fuel : Nat) (env : VarEnv)
    (st : HeapState) (v : Val) (st' : HeapState)
    (hk : ∀ env' v' st1, evalCode fuel env' st k = .ok (v', st1) → st1 = st)
    (hl : lowerBorrowedSliceLoad dst idxVar posVar s k = some code)
    (h : evalCode fuel env st code = .ok (v, st')) :
    st' = st := by
  unfold lowerBorrowedSliceLoad at hl
  split at hl
  · cases hl
    refine evalLetScalar_preserves_heap fuel env st _ .i64 _ _ ?_ v st' h
    intro env1 v1 st1 h1
    refine evalIte_unreachable_preserves_heap fuel env1 st _ _ ?_ v1 st1 h1
    intro env2 v2 st2 h2
    refine evalLetScalar_preserves_heap fuel env2 st posVar .i64 _ _ ?_ v2 st2 h2
    intro env3 v3 st3 h3
    exact evalLetRawLoad_preserves_heap fuel env3 st dst s.ptrVar posVar .i64 .i64 k hk v3 st3 h3
  · cases hl

private theorem lowerUnboxedFieldLoad_preserves_heap (dst baseVar idxVar posVar : VarId)
    (field : PlacedUnboxedField) (k code : LNIRCode) (fuel : Nat) (env : VarEnv)
    (st : HeapState) (v : Val) (st' : HeapState)
    (hk : ∀ env' v' st1, evalCode fuel env' st k = .ok (v', st1) → st1 = st)
    (hl : lowerUnboxedFieldLoad dst baseVar idxVar posVar field k = some code)
    (h : evalCode fuel env st code = .ok (v, st')) :
    st' = st := by
  unfold lowerUnboxedFieldLoad at hl
  split at hl
  · cases hl
    refine evalLetScalar_preserves_heap fuel env st _ .i64 _ _ ?_ v st' h
    intro env1 v1 st1 h1
    refine evalIte_unreachable_preserves_heap fuel env1 st _ _ ?_ v1 st1 h1
    intro env2 v2 st2 h2
    refine evalLetScalar_preserves_heap fuel env2 st posVar .i64 _ _ ?_ v2 st2 h2
    intro env3 v3 st3 h3
    by_cases hfull : (field.size == 8 && field.offset % 8 == 0) = true
    · rw [ite_eq_left hfull] at h3
      exact evalLetRawLoad_preserves_heap fuel env3 st dst baseVar posVar
        field.field.kind.lnirType .i64 k hk v3 st3 h3
    · rw [ite_eq_right hfull] at h3
      refine evalLetRawLoad_preserves_heap fuel env3 st _ baseVar posVar .i64 .i64 _ ?_ v3 st3 h3
      intro env4 v4 st4 h4
      exact evalLetScalar_preserves_heap fuel env4 st dst field.field.kind.lnirType _ k hk v4 st4 h4
  · cases hl

private theorem lowerUnboxedStructLoadsAux_preserves_heap (baseVar idxVar posVar : VarId)
    (fields : List PlacedUnboxedField) (dsts : List VarId) (k code : LNIRCode)
    (fuel : Nat) (env : VarEnv) (st : HeapState) (v : Val) (st' : HeapState)
    (hk : ∀ env' v' st1, evalCode fuel env' st k = .ok (v', st1) → st1 = st)
    (hl : lowerUnboxedStructLoadsAux baseVar idxVar posVar fields dsts k = some code)
    (h : evalCode fuel env st code = .ok (v, st')) :
    st' = st := by
  induction fields generalizing dsts k code env v st' with
  | nil =>
    cases dsts <;> simp [lowerUnboxedStructLoadsAux] at hl
    all_goals (subst hl; exact hk env v st' h)
  | cons f fs ih =>
    cases dsts with
    | nil =>
      simp [lowerUnboxedStructLoadsAux] at hl
      subst hl
      exact hk env v st' h
    | cons d ds =>
      unfold lowerUnboxedStructLoadsAux at hl
      cases htail : lowerUnboxedStructLoadsAux baseVar idxVar posVar fs ds k with
      | none => simp [htail] at hl
      | some tail =>
        rw [htail] at hl
        dsimp only [Bind.bind, Option.bind] at hl
        exact lowerUnboxedFieldLoad_preserves_heap d baseVar idxVar posVar f tail code
          fuel env st v st' (fun env' v' st1 ht => ih ds k tail env' v' st1 hk htail ht) hl h

theorem lowerUnboxedRegionCode_sound (dst posVar idxVar baseVar : VarId)
    (layout : UnboxedStructLayout) (slice : BorrowedRegionSlice) (code : LNIRCode)
    (fuel : Nat) (env : VarEnv) (st : HeapState) (v : Val) (st' : HeapState)
    (hl : lowerUnboxedRegionCode dst posVar idxVar layout slice baseVar (.ret dst) = some code)
    (h : evalCode fuel env st code = .ok (v, st')) :
    st' = st := by
  have hret : ∀ env' v' st1, evalCode fuel env' st (.ret dst) = .ok (v', st1) → st1 = st := by
    intro env' v' st1 hr
    dsimp only [evalCode] at hr
    cases hd : env' dst with
    | none => rw [hd] at hr; contradiction
    | some vd => rw [hd] at hr; exact (Prod.mk.inj (Except.ok.inj hr)).2.symm
  unfold lowerUnboxedRegionCode at hl
  cases hfields : layout.fields with
  | nil =>
    rw [hfields] at hl
    exact lowerBorrowedSliceLoad_preserves_heap dst idxVar posVar slice (.ret dst) code
      fuel env st v st' hret hl h
  | cons f fs =>
    rw [hfields] at hl
    unfold lowerUnboxedStructLoads at hl
    rw [hfields] at hl
    exact lowerUnboxedStructLoadsAux_preserves_heap baseVar idxVar posVar (f :: fs)
      ((List.range (f :: fs).length).map (fun i => dst + i)) (.ret dst) code
      fuel env st v st' hret hl h

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

private theorem canElide_mark_call (e : LNIRExpr) (k : LNIRCode)
    (h : canElideMarkMt e k = true) :
    ∃ arg retTy, e = .call "lean_mark_mt" [arg] retTy false := by
  cases e with
  | call fn args retTy ext =>
    cases ext
    · cases args with
      | nil => simp [canElideMarkMt] at h
      | cons arg rest =>
        cases rest with
        | nil =>
          dsimp [canElideMarkMt] at h
          have hfn := of_decide_eq_true ((Bool.and_eq_true _ _).mp h).1
          subst hfn
          exact ⟨arg, retTy, rfl⟩
        | cons _ _ => simp [canElideMarkMt] at h
    · simp [canElideMarkMt] at h
  | _ => simp [canElideMarkMt] at h

private theorem exprMayAlias_mark_false (aliases : List VarId) (arg : VarId) (retTy : LNIRType) :
    exprMayAlias aliases (.call "lean_mark_mt" [arg] retTy false) = false := by
  simp [exprMayAlias]

private theorem exprEscapes_mark_false (aliases : List VarId) (arg : VarId) (retTy : LNIRType) :
    exprEscapesWith aliases (.call "lean_mark_mt" [arg] retTy false) = false := by
  simp [exprEscapesWith]

private theorem exprMayAlias_zero_false (aliases : List VarId) :
    exprMayAlias aliases (.scalar (.constU64 0)) = false := by
  simp [exprMayAlias, scalarMentions]

private theorem exprEscapes_zero_false (aliases : List VarId) :
    exprEscapesWith aliases (.scalar (.constU64 0)) = false := by
  simp [exprEscapesWith]

theorem elideMarkMtAndZeroRc_preserves_nonEscape (aliases : List VarId) (code : LNIRCode)
    (h : codeEscapesWith aliases code = false) :
    codeEscapesWith aliases (elideMarkMtAndZeroRc code) = false := by
  unfold elideMarkMtAndZeroRc
  induction code generalizing aliases with
  | letBind dst ty val k ih =>
    unfold codeEscapesWith at h
    dsimp only [Transform.elideMarkMtAndZeroRc]
    by_cases hcan : canElideMarkMt val k = true
    · rw [ite_eq_left hcan]
      rcases canElide_mark_call val k hcan with ⟨arg, retTy, hval⟩
      subst hval
      rw [exprEscapes_mark_false, exprMayAlias_mark_false, Bool.false_or] at h
      unfold codeEscapesWith
      rw [exprEscapes_zero_false, exprMayAlias_zero_false, Bool.false_or]
      exact ih _ h
    · rw [ite_eq_right hcan]
      unfold codeEscapesWith
      rw [Bool.or_eq_false_iff] at h ⊢
      exact ⟨h.1, ih _ h.2⟩
  | rawStore p i x ty k ih =>
    unfold codeEscapesWith at h
    dsimp only [Transform.elideMarkMtAndZeroRc, codeEscapesWith]
    rw [Bool.or_eq_false_iff] at h ⊢
    exact ⟨h.1, ih aliases h.2⟩
  | incRef ov c k ih =>
    unfold codeEscapesWith at h
    dsimp only [Transform.elideMarkMtAndZeroRc]
    by_cases hc : (c == 0) = true
    · rw [ite_eq_left hc]; exact ih aliases h
    · rw [ite_eq_right hc]; exact ih aliases h
  | decRef ov c k ih =>
    unfold codeEscapesWith at h
    dsimp only [Transform.elideMarkMtAndZeroRc]
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
    dsimp only [Transform.elideBorrowedAndThreadLocalRC]
    by_cases hcan : canElideMarkMt val k = true
    · rw [ite_eq_left hcan]
      rcases canElide_mark_call val k hcan with ⟨arg, retTy, hval⟩
      subst hval
      rw [exprEscapes_mark_false, exprMayAlias_mark_false, Bool.false_or] at h
      unfold codeEscapesWith
      rw [exprEscapes_zero_false, exprMayAlias_zero_false, Bool.false_or]
      by_cases hsh : (dst == v) = true
      · rw [ite_eq_left hsh]
        exact elideMarkMtAndZeroRc_preserves_nonEscape _ k h
      · rw [ite_eq_right hsh]
        exact ih _ h
    · rw [ite_eq_right hcan]
      unfold codeEscapesWith
      rw [Bool.or_eq_false_iff] at h ⊢
      refine ⟨h.1, ?_⟩
      by_cases hsh : (dst == v) = true
      · rw [ite_eq_left hsh]
        exact elideMarkMtAndZeroRc_preserves_nonEscape _ k h.2
      · rw [ite_eq_right hsh]
        exact ih _ h.2
  | rawStore p i x ty k ih =>
    unfold codeEscapesWith at h
    dsimp only [Transform.elideBorrowedAndThreadLocalRC, codeEscapesWith]
    rw [Bool.or_eq_false_iff] at h ⊢
    exact ⟨h.1, ih aliases h.2⟩
  | incRef ov c k ih =>
    unfold codeEscapesWith at h
    dsimp only [Transform.elideBorrowedAndThreadLocalRC]
    by_cases hc : (ov == v || c == 0) = true
    · rw [ite_eq_left hc]; exact ih aliases h
    · rw [ite_eq_right hc]; exact ih aliases h
  | decRef ov c k ih =>
    unfold codeEscapesWith at h
    dsimp only [Transform.elideBorrowedAndThreadLocalRC]
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
      · rw [ite_eq_left hs]
        exact elideMarkMtAndZeroRc_preserves_nonEscape _ step h.1.2
      · rw [ite_eq_right hs]
        exact ihs _ h.1.2
    · by_cases hk : (av == v) = true
      · rw [ite_eq_left hk]
        exact elideMarkMtAndZeroRc_preserves_nonEscape _ k h.2
      · rw [ite_eq_right hk]
        exact ihk _ h.2
  | parFor ov len ins ety kern k ih =>
    unfold codeEscapesWith at h
    dsimp only [Transform.elideBorrowedAndThreadLocalRC, codeEscapesWith]
    rw [Bool.or_eq_false_iff] at h ⊢
    refine ⟨h.1, ?_⟩
    by_cases hk : (ov == v) = true
    · rw [ite_eq_left hk]
      exact elideMarkMtAndZeroRc_preserves_nonEscape _ k h.2
    · rw [ite_eq_right hk]
      exact ih _ h.2
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


private theorem foldl_max_ge_base (b : Nat) (us : List VarId) : b ≤ us.foldl Nat.max b := by
  induction us generalizing b with
  | nil => exact Nat.le_refl b
  | cons u rest ih => exact Nat.le_trans (Nat.le_max_left b u) (ih (Nat.max b u))

private theorem freshAbove_gt_mem (base : Nat) (used : List VarId) (v : VarId) (hv : v ∈ used) :
    v < freshAbove base used := by
  unfold freshAbove
  suffices h : ∀ b (us : List VarId), v ∈ us → v ≤ us.foldl Nat.max b from
    Nat.lt_succ_of_le (h base used hv)
  intro b us hmem
  induction us generalizing b with
  | nil => cases hmem
  | cons u rest ih =>
    rcases List.mem_cons.mp hmem with rfl | htail
    · exact Nat.le_trans (Nat.le_max_right b v) (foldl_max_ge_base (Nat.max b v) rest)
    · exact ih (Nat.max b u) htail

private theorem freshAbove_gt_base (base : Nat) (used : List VarId) :
    base < freshAbove base used := by
  unfold freshAbove
  exact Nat.lt_succ_of_le (foldl_max_ge_base base used)

private theorem bind_ne_lookup (env : VarEnv) (k q : VarId) (v : Val) (hne : q ≠ k) :
    (env.bind k v) q = env q := by
  simp [VarEnv.bind, beq_false_of_ne hne]

private theorem bind_eq_lookup (env : VarEnv) (k : VarId) (v : Val) :
    (env.bind k v) k = some v := by
  simp [VarEnv.bind]

private theorem evalBinOp_bitOr_u64 (a b : UInt64) :
    evalBinOp .bitOr (.u64 a) (.u64 b) = .ok (.u64 (a ||| b)) := rfl

private theorem evalBinOp_shl_u64 (a b : UInt64) :
    evalBinOp .shl (.u64 a) (.u64 b) = .ok (.u64 (a <<< b)) := rfl

private theorem evalBinOp_shr_u64 (a b : UInt64) :
    evalBinOp .shr (.u64 a) (.u64 b) = .ok (.u64 (a >>> b)) := rfl

private theorem evalBinOp_bitAnd_u64 (a b : UInt64) :
    evalBinOp .bitAnd (.u64 a) (.u64 b) = .ok (.u64 (a &&& b)) := rfl

private theorem evalBinOp_add_u64 (a b : UInt64) :
    evalBinOp .add (.u64 a) (.u64 b) = .ok (.u64 (a + b)) := rfl

private theorem evalUnary_not_u64 (a : UInt64) :
    evalUnaryOp .not (.u64 a) = .ok (.u64 (~~~a)) := rfl

private theorem evalScalar_constU64 (env : VarEnv) (c : UInt64) :
    evalScalarExpr env (.constU64 c) = .ok (.u64 c) := rfl

private theorem evalScalar_var_some (env : VarEnv) (q : VarId) (v : Val) (h : env q = some v) :
    evalScalarExpr env (.var q) = .ok v := by simp [evalScalarExpr, h]

private theorem evalScalar_binOp_ok (env : VarEnv) (op : BinOp) (l r : ScalarExpr) (a b : Val)
    (hl : evalScalarExpr env l = .ok a) (hr : evalScalarExpr env r = .ok b) :
    evalScalarExpr env (.binOp op l r) = evalBinOp op a b := by
  simp [evalScalarExpr, hl, hr]

private theorem evalScalar_unary_ok (env : VarEnv) (op : UnaryOp) (a : ScalarExpr) (v : Val)
    (h : evalScalarExpr env a = .ok v) :
    evalScalarExpr env (.unaryOp op a) = evalUnaryOp op v := by
  simp [evalScalarExpr, h]

private theorem stepLetScalar (fuel : Nat) (env : VarEnv) (st : HeapState)
    (dst : VarId) (ty : LNIRType) (se : ScalarExpr) (v : Val) (k : LNIRCode)
    (h : evalScalarExpr env se = .ok v) :
    evalCode fuel env st (.letBind dst ty (.scalar se) k) =
      evalCode fuel (env.bind dst v) st k := by
  dsimp only [evalCode, evalExpr]
  rw [h]

private theorem stepLetRawLoad (fuel : Nat) (env : VarEnv) (st : HeapState)
    (dst p i : VarId) (ty : LNIRType) (bufId : Nat) (idx w : UInt64) (k : LNIRCode)
    (hp : env p = some (.rawPtrId bufId)) (hi : env i = some (.u64 idx))
    (hrd : st.readElem bufId idx.toNat = .ok w) :
    evalCode fuel env st (.letBind dst ty (.rawLoad p i .i64) k) =
      evalCode fuel (env.bind dst (.u64 w)) st k := by
  dsimp only [evalCode, evalExpr, maskElemVal]
  rw [hp, hi]
  dsimp only
  rw [hrd]

private theorem stepIteTrue (fuel : Nat) (env : VarEnv) (st : HeapState)
    (c : VarId) (n : UInt64) (t e : LNIRCode)
    (hc : env c = some (.u64 n)) (hn : (n != 0) = true) :
    evalCode fuel env st (.ite c t e) = evalCode fuel env st t := by
  dsimp only [evalCode]
  rw [hc]
  dsimp only
  rw [ite_eq_left hn]

private theorem stepIteFalse (fuel : Nat) (env : VarEnv) (st : HeapState)
    (c : VarId) (n : UInt64) (t e : LNIRCode)
    (hc : env c = some (.u64 n)) (hn : ¬((n != 0) = true)) :
    evalCode fuel env st (.ite c t e) = evalCode fuel env st e := by
  dsimp only [evalCode]
  rw [hc]
  dsimp only
  rw [ite_eq_right hn]

private theorem stepRawStore (fuel : Nat) (env : VarEnv) (st st' : HeapState)
    (p i v : VarId) (bufId : Nat) (idx val : UInt64) (k : LNIRCode)
    (hp : env p = some (.rawPtrId bufId)) (hi : env i = some (.u64 idx))
    (hv : env v = some (.u64 val))
    (hwr : st.writeElemExclusive bufId idx.toNat val = .ok st') :
    evalCode fuel env st (.rawStore p i v .i64 k) = evalCode fuel env st' k := by
  dsimp only [evalCode, maskElemVal]
  rw [hp, hi, hv]
  dsimp only
  rw [hwr]

private theorem findBuffer_map_preserve_id (bs : List ArrayBuffer) (bufId : Nat)
    (f : ArrayBuffer → ArrayBuffer) (hf : ∀ b, (f b).id = b.id) :
    (bs.map f).find? (fun b => b.id == bufId) =
      (bs.find? (fun b => b.id == bufId)).map f := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.map_cons, List.find?_cons]
    have hid : ((f b).id == bufId) = (b.id == bufId) := by rw [hf b]
    rw [hid]
    cases b.id == bufId <;> simp [ih]

private theorem writeElemExclusive_readElem_same (st st1 : HeapState)
    (bufId idx : Nat) (val : UInt64)
    (hw : st.writeElemExclusive bufId idx val = .ok st1) :
    st1.readElem bufId idx = .ok val ∧
      ∀ val2, ∃ st2, st1.writeElemExclusive bufId idx val2 = .ok st2 := by
  unfold HeapState.writeElemExclusive at hw
  cases hfb : st.findBuffer bufId with
  | none =>
    rw [hfb] at hw
    contradiction
  | some buf =>
    rw [hfb] at hw
    dsimp only at hw
    by_cases hexcl : (!buf.exclusive) = true
    · rw [ite_eq_left hexcl] at hw
      contradiction
    · rw [ite_eq_right hexcl] at hw
      by_cases hlt : idx < buf.data.size
      · rw [dite_eq_left hlt] at hw
        injection hw with hst1
        subst hst1
        let g : ArrayBuffer → ArrayBuffer := fun b =>
          if b.id == bufId then { b with data := b.data.set! idx val } else b
        have hg_id : ∀ b, (g b).id = b.id := by
          intro b
          dsimp only [g]
          by_cases hb : (b.id == bufId) = true
          · rw [ite_eq_left hb]
          · rw [ite_eq_right hb]
        have hbuf_id : (buf.id == bufId) = true := by
          unfold HeapState.findBuffer at hfb
          exact List.find?_some (p := fun b : ArrayBuffer => b.id == bufId) hfb
        have hfb1 : ({ st with buffers := st.buffers.map g }).findBuffer bufId =
            some { buf with data := buf.data.set! idx val } := by
          unfold HeapState.findBuffer at hfb ⊢
          rw [findBuffer_map_preserve_id st.buffers bufId g hg_id, hfb]
          dsimp only [Option.map, g]
          rw [ite_eq_left hbuf_id]
        have hsz1 : idx < (buf.data.set! idx val).size := by
          change idx < (buf.data.setIfInBounds idx val).size
          rw [Array.size_setIfInBounds]
          exact hlt
        refine ⟨?_, fun val2 => ?_⟩
        · unfold HeapState.readElem
          rw [hfb1]
          dsimp only
          rw [dite_eq_left hsz1]
          change Except.ok ((buf.data.setIfInBounds idx val)[idx]'hsz1) = .ok val
          exact congrArg Except.ok (Array.getElem_setIfInBounds_self hsz1)
        · let g2 : ArrayBuffer → ArrayBuffer := fun b =>
            if b.id == bufId then { b with data := b.data.set! idx val2 } else b
          refine ⟨{ st with buffers := (st.buffers.map g).map g2 }, ?_⟩
          unfold HeapState.writeElemExclusive
          rw [hfb1]
          dsimp only
          rw [ite_eq_right hexcl, dite_eq_left hsz1]
      · rw [dite_eq_right hlt] at hw
        contradiction

private theorem mask_bit (sz i : Nat) (hsz : sz ≤ 8) (hi : i < 64) :
    ((if 8 ≤ sz then (0xffffffffffffffff : UInt64)
      else ((1 : UInt64) <<< (sz * 8).toUInt64) - 1)).toBitVec[i] =
      decide (i < sz * 8) := by
  have hc : sz = 0 ∨ sz = 1 ∨ sz = 2 ∨ sz = 3 ∨ sz = 4 ∨ sz = 5 ∨ sz = 6 ∨ sz = 7 ∨ sz = 8 := by
    omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    revert hi
    revert i
    decide

private theorem bitOff_mod64 (f : PlacedUnboxedField) :
    (fieldBitOff f).toNat % 64 = (f.offset % 8) * 8 := by
  unfold fieldBitOff
  have hc : f.offset % 8 = 0 ∨ f.offset % 8 = 1 ∨ f.offset % 8 = 2 ∨ f.offset % 8 = 3 ∨
      f.offset % 8 = 4 ∨ f.offset % 8 = 5 ∨ f.offset % 8 = 6 ∨ f.offset % 8 = 7 := by
    omega
  rcases hc with h | h | h | h | h | h | h | h
  all_goals
    rw [h]
    decide

theorem rmw_subword_roundtrip_u64 (f : PlacedUnboxedField) (oldWord val : UInt64)
    (hfit : fieldFitsInWord f = true) :
    let mask := fieldMask f
    let sh := fieldBitOff f
    let newWord := (oldWord &&& ~~~(mask <<< sh)) ||| ((val &&& mask) <<< sh)
    ((newWord >>> sh) &&& mask) = (val &&& mask) := by
  intro mask sh newWord
  have hle : (f.offset % 8) + f.size ≤ 8 := of_decide_eq_true hfit
  have hsz : f.size ≤ 8 := by omega
  have hsh : sh.toNat % 64 = (f.offset % 8) * 8 := bitOff_mod64 f
  apply UInt64.eq_of_toBitVec_eq
  ext i hi
  have hml : mask.toBitVec[i] = decide (i < f.size * 8) := mask_bit f.size i hsz hi
  by_cases hlt : i < f.size * 8
  · have hi2 : (f.offset % 8) * 8 + i < 64 := by omega
    have hge : ¬((f.offset % 8) * 8 + i < (f.offset % 8) * 8) := by omega
    have hsub : (f.offset % 8) * 8 + i - (f.offset % 8) * 8 = i := by omega
    simp [newWord, UInt64.toBitVec_and, UInt64.toBitVec_or, UInt64.toBitVec_not,
      UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, hsh, hml, hlt, hi2, hge, hsub]
  · simp [newWord, UInt64.toBitVec_and, UInt64.toBitVec_or, UInt64.toBitVec_not,
      UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, hml, hlt]

theorem rmw_subword_disjoint_u64 (f g : PlacedUnboxedField) (oldWord val : UInt64)
    (hfitF : fieldFitsInWord f = true) (hfitG : fieldFitsInWord g = true)
    (hdisj : (f.offset % 8) + f.size ≤ g.offset % 8 ∨ (g.offset % 8) + g.size ≤ f.offset % 8) :
    let maskF := fieldMask f
    let shF := fieldBitOff f
    let newWord := (oldWord &&& ~~~(maskF <<< shF)) ||| ((val &&& maskF) <<< shF)
    ((newWord >>> fieldBitOff g) &&& fieldMask g) =
      ((oldWord >>> fieldBitOff g) &&& fieldMask g) := by
  intro maskF shF newWord
  have hleF : (f.offset % 8) + f.size ≤ 8 := of_decide_eq_true hfitF
  have hleG : (g.offset % 8) + g.size ≤ 8 := of_decide_eq_true hfitG
  have hszF : f.size ≤ 8 := by omega
  have hszG : g.size ≤ 8 := by omega
  have hshF : shF.toNat % 64 = (f.offset % 8) * 8 := bitOff_mod64 f
  have hshG : (fieldBitOff g).toNat % 64 = (g.offset % 8) * 8 := bitOff_mod64 g
  apply UInt64.eq_of_toBitVec_eq
  ext i hi
  have hmg : (fieldMask g).toBitVec[i] = decide (i < g.size * 8) := mask_bit g.size i hszG hi
  by_cases hltG : i < g.size * 8
  · have hi2 : (g.offset % 8) * 8 + i < 64 := by omega
    by_cases hlow : (g.offset % 8) * 8 + i < (f.offset % 8) * 8
    · simp [newWord, UInt64.toBitVec_and, UInt64.toBitVec_or, UInt64.toBitVec_not,
        UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, hshF, hshG, hmg, hltG, hi2, hlow]
    · have hsublt : (g.offset % 8) * 8 + i - (f.offset % 8) * 8 < 64 := by omega
      have hnltF : ¬((g.offset % 8) * 8 + i - (f.offset % 8) * 8 < f.size * 8) := by omega
      have hmf : maskF.toBitVec[(g.offset % 8) * 8 + i - (f.offset % 8) * 8]'hsublt =
          decide ((g.offset % 8) * 8 + i - (f.offset % 8) * 8 < f.size * 8) :=
        mask_bit f.size _ hszF hsublt
      simp [newWord, UInt64.toBitVec_and, UInt64.toBitVec_or, UInt64.toBitVec_not,
        UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, hshF, hshG, hmg, hmf,
        hltG, hi2, hlow, hnltF]
  · simp [newWord, UInt64.toBitVec_and, UInt64.toBitVec_or, UInt64.toBitVec_not,
      UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, hmg, hltG]

theorem lowerBorrowedSliceLoad_unaligned_slice_none (dst idxVar posVar : VarId)
    (s : BorrowedRegionSlice) (k : LNIRCode) (h : s.view.offset % 8 ≠ 0) :
    lowerBorrowedSliceLoad dst idxVar posVar s k = none := by
  unfold lowerBorrowedSliceLoad wordSliceValid
  simp [h]

theorem lowerBorrowedSliceLoad_unaligned_idx_traps (dst idxVar posVar : VarId)
    (s : BorrowedRegionSlice) (k code : LNIRCode) (fuel : Nat) (env : VarEnv)
    (st : HeapState) (idx : UInt64)
    (hl : lowerBorrowedSliceLoad dst idxVar posVar s k = some code)
    (hidx : env idxVar = some (.u64 idx))
    (hunalign : (idx &&& 7) != 0) :
    evalCode fuel env st code = .error (.typeError "reached unreachable code") := by
  unfold lowerBorrowedSliceLoad at hl
  split at hl
  · cases hl
    rw [stepLetScalar fuel env st _ .i64 _ (.u64 (idx &&& 7)) _
      (by rw [evalScalar_binOp_ok _ _ _ _ _ _ (evalScalar_var_some _ _ _ hidx)
            (evalScalar_constU64 _ _), evalBinOp_bitAnd_u64])]
    rw [stepIteTrue fuel _ st _ (idx &&& 7) _ _ (bind_eq_lookup _ _ _) hunalign]
    rfl
  · cases hl

theorem lowerUnboxedFieldLoad_unaligned_idx_traps (dst baseVar idxVar posVar : VarId)
    (field : PlacedUnboxedField) (k code : LNIRCode) (fuel : Nat) (env : VarEnv)
    (st : HeapState) (idx : UInt64)
    (hl : lowerUnboxedFieldLoad dst baseVar idxVar posVar field k = some code)
    (hidx : env idxVar = some (.u64 idx))
    (hunalign : (idx &&& 7) != 0) :
    evalCode fuel env st code = .error (.typeError "reached unreachable code") := by
  unfold lowerUnboxedFieldLoad at hl
  split at hl
  · cases hl
    rw [stepLetScalar fuel env st _ .i64 _ (.u64 (idx &&& 7)) _
      (by rw [evalScalar_binOp_ok _ _ _ _ _ _ (evalScalar_var_some _ _ _ hidx)
            (evalScalar_constU64 _ _), evalBinOp_bitAnd_u64])]
    rw [stepIteTrue fuel _ st _ (idx &&& 7) _ _ (bind_eq_lookup _ _ _) hunalign]
    rfl
  · cases hl

theorem lowerUnboxedFieldStore_unaligned_idx_traps (baseVar idxVar posVar valVar : VarId)
    (field : PlacedUnboxedField) (k code : LNIRCode) (fuel : Nat) (env : VarEnv)
    (st : HeapState) (idx : UInt64)
    (hl : lowerUnboxedFieldStore baseVar idxVar posVar valVar field k = some code)
    (hidx : env idxVar = some (.u64 idx))
    (hunalign : (idx &&& 7) != 0) :
    evalCode fuel env st code = .error (.typeError "reached unreachable code") := by
  unfold lowerUnboxedFieldStore at hl
  split at hl
  · cases hl
    rw [stepLetScalar fuel env st _ .i64 _ (.u64 (idx &&& 7)) _
      (by rw [evalScalar_binOp_ok _ _ _ _ _ _ (evalScalar_var_some _ _ _ hidx)
            (evalScalar_constU64 _ _), evalBinOp_bitAnd_u64])]
    rw [stepIteTrue fuel _ st _ (idx &&& 7) _ _ (bind_eq_lookup _ _ _) hunalign]
    rfl
  · cases hl

theorem lowerUnboxedFieldStore_eval_subword (baseVar idxVar posVar valVar : VarId)
    (field : PlacedUnboxedField) (k code : LNIRCode) (fuel : Nat) (env : VarEnv)
    (st st1 : HeapState) (bufId : Nat) (idx val oldWord : UInt64)
    (hbp : baseVar ≠ posVar) (hvp : valVar ≠ posVar)
    (hl : lowerUnboxedFieldStore baseVar idxVar posVar valVar field k = some code)
    (hsub : (field.size == 8 && field.offset % 8 == 0) = false)
    (hbase : env baseVar = some (.rawPtrId bufId))
    (hidx : env idxVar = some (.u64 idx))
    (hval : env valVar = some (.u64 val))
    (halign : (idx &&& 7) = 0)
    (hread : st.readElem bufId ((idx >>> 3) + (byteOffsetToWord field.offset).toUInt64).toNat =
      .ok oldWord)
    (hwrite : st.writeElemExclusive bufId
      ((idx >>> 3) + (byteOffsetToWord field.offset).toUInt64).toNat
      ((oldWord &&& ~~~(fieldMask field <<< fieldBitOff field)) |||
        ((val &&& fieldMask field) <<< fieldBitOff field)) = .ok st1) :
    ∃ env',
      evalCode fuel env st code = evalCode fuel env' st1 k ∧
      (∀ q, q < freshAbove (codeMaxVar k) [baseVar, idxVar, posVar, valVar] →
        q ≠ posVar → env' q = env q) := by
  unfold lowerUnboxedFieldStore at hl
  split at hl
  · cases hl
    let aTmp := freshAbove (codeMaxVar k) [baseVar, idxVar, posVar, valVar]
    have hb_lt : baseVar < aTmp := freshAbove_gt_mem _ _ baseVar (by simp)
    have hi_lt : idxVar < aTmp := freshAbove_gt_mem _ _ idxVar (by simp)
    have hp_lt : posVar < aTmp := freshAbove_gt_mem _ _ posVar (by simp)
    have hv_lt : valVar < aTmp := freshAbove_gt_mem _ _ valVar (by simp)
    have hnalign : ¬(((idx &&& 7) != 0) = true) := by rw [halign]; decide
    have hnsub : ¬((field.size == 8 && field.offset % 8 == 0) = true) := by simpa using hsub
    let wordIdx := (idx >>> 3) + (byteOffsetToWord field.offset).toUInt64
    let masked := val &&& fieldMask field
    let shifted := masked <<< fieldBitOff field
    let cleared := oldWord &&& ~~~(fieldMask field <<< fieldBitOff field)
    let newWord := cleared ||| shifted
    let env1 := env.bind aTmp (.u64 (idx &&& 7))
    let env2 := env1.bind posVar (.u64 wordIdx)
    let env3 := env2.bind (aTmp + 1) (.u64 oldWord)
    let env4 := env3.bind (aTmp + 2) (.u64 masked)
    let env5 := env4.bind (aTmp + 3) (.u64 shifted)
    let env6 := env5.bind (aTmp + 4) (.u64 cleared)
    let env7 := env6.bind (aTmp + 5) (.u64 newWord)
    have hidx1 : env1 idxVar = some (.u64 idx) := by
      dsimp only [env1]
      rw [bind_ne_lookup _ _ idxVar _ (Nat.ne_of_lt hi_lt)]
      exact hidx
    have hbase2 : env2 baseVar = some (.rawPtrId bufId) := by
      dsimp only [env2, env1]
      rw [bind_ne_lookup _ posVar baseVar _ hbp]
      rw [bind_ne_lookup _ _ baseVar _ (Nat.ne_of_lt hb_lt)]
      exact hbase
    have hval3 : env3 valVar = some (.u64 val) := by
      dsimp only [env3, env2, env1]
      rw [bind_ne_lookup _ _ valVar _ (Nat.ne_of_lt (Nat.lt_succ_of_lt hv_lt))]
      rw [bind_ne_lookup _ posVar valVar _ hvp]
      rw [bind_ne_lookup _ _ valVar _ (Nat.ne_of_lt hv_lt)]
      exact hval
    have hold5 : env5 (aTmp + 1) = some (.u64 oldWord) := by
      dsimp only [env5, env4, env3]
      have h13 : aTmp + 1 ≠ aTmp + 3 := by unfold VarId at *; omega
      have h12 : aTmp + 1 ≠ aTmp + 2 := by unfold VarId at *; omega
      rw [bind_ne_lookup _ _ (aTmp + 1) _ h13, bind_ne_lookup _ _ (aTmp + 1) _ h12]
      exact bind_eq_lookup _ _ _
    have hsh6 : env6 (aTmp + 3) = some (.u64 shifted) := by
      dsimp only [env6, env5]
      have h34 : aTmp + 3 ≠ aTmp + 4 := by unfold VarId at *; omega
      rw [bind_ne_lookup _ _ (aTmp + 3) _ h34]
      exact bind_eq_lookup _ _ _
    have hbase7 : env7 baseVar = some (.rawPtrId bufId) := by
      dsimp only [env7, env6, env5, env4, env3]
      rw [bind_ne_lookup _ _ baseVar _ (by unfold VarId at *; omega)]
      rw [bind_ne_lookup _ _ baseVar _ (by unfold VarId at *; omega)]
      rw [bind_ne_lookup _ _ baseVar _ (by unfold VarId at *; omega)]
      rw [bind_ne_lookup _ _ baseVar _ (by unfold VarId at *; omega)]
      rw [bind_ne_lookup _ _ baseVar _ (by unfold VarId at *; omega)]
      exact hbase2
    have hpos7 : env7 posVar = some (.u64 wordIdx) := by
      dsimp only [env7, env6, env5, env4, env3, env2]
      rw [bind_ne_lookup _ _ posVar _ (by unfold VarId at *; omega)]
      rw [bind_ne_lookup _ _ posVar _ (by unfold VarId at *; omega)]
      rw [bind_ne_lookup _ _ posVar _ (by unfold VarId at *; omega)]
      rw [bind_ne_lookup _ _ posVar _ (by unfold VarId at *; omega)]
      rw [bind_ne_lookup _ _ posVar _ (by unfold VarId at *; omega)]
      exact bind_eq_lookup _ _ _
    refine ⟨env7, ?_, ?_⟩
    · rw [stepLetScalar fuel env st aTmp .i64 _ (.u64 (idx &&& 7)) _
        (by rw [evalScalar_binOp_ok _ _ _ _ _ _ (evalScalar_var_some _ _ _ hidx)
              (evalScalar_constU64 _ _), evalBinOp_bitAnd_u64])]
      rw [stepIteFalse fuel env1 st aTmp (idx &&& 7) _ _ (bind_eq_lookup _ _ _) hnalign]
      rw [stepLetScalar fuel env1 st posVar .i64 _ (.u64 wordIdx) _
        (by rw [evalScalar_binOp_ok _ _ _ _ (.u64 (idx >>> 3)) _
              (by rw [evalScalar_binOp_ok _ _ _ _ _ _ (evalScalar_var_some _ _ _ hidx1)
                    (evalScalar_constU64 _ _), evalBinOp_shr_u64])
              (evalScalar_constU64 _ _), evalBinOp_add_u64])]
      rw [ite_eq_right hnsub]
      rw [stepLetRawLoad fuel env2 st (aTmp + 1) baseVar posVar .i64
        bufId wordIdx oldWord _ hbase2 (bind_eq_lookup _ _ _) hread]
      rw [stepLetScalar fuel env3 st (aTmp + 2) .i64 _ (.u64 masked) _
        (by rw [evalScalar_binOp_ok _ _ _ _ _ _ (evalScalar_var_some _ _ _ hval3)
              (evalScalar_constU64 _ _), evalBinOp_bitAnd_u64])]
      rw [stepLetScalar fuel env4 st (aTmp + 3) .i64 _ (.u64 shifted) _
        (by rw [evalScalar_binOp_ok _ _ _ _ _ _
              (evalScalar_var_some _ _ _ (bind_eq_lookup _ _ _))
              (evalScalar_constU64 _ _), evalBinOp_shl_u64])]
      rw [stepLetScalar fuel env5 st (aTmp + 4) .i64 _ (.u64 cleared) _
        (by rw [evalScalar_binOp_ok _ _ _ _ _ (.u64 (~~~(fieldMask field <<< fieldBitOff field)))
              (evalScalar_var_some _ _ _ hold5)
              (by rw [evalScalar_unary_ok _ _ _ (.u64 (fieldMask field <<< fieldBitOff field))
                    (by rw [evalScalar_binOp_ok _ _ _ _ _ _ (evalScalar_constU64 _ _)
                          (evalScalar_constU64 _ _), evalBinOp_shl_u64]), evalUnary_not_u64]),
              evalBinOp_bitAnd_u64])]
      rw [stepLetScalar fuel env6 st (aTmp + 5) .i64 _ (.u64 newWord) _
        (by rw [evalScalar_binOp_ok _ _ _ _ _ _
              (evalScalar_var_some _ _ _ (bind_eq_lookup _ _ _))
              (evalScalar_var_some _ _ _ hsh6), evalBinOp_bitOr_u64])]
      exact stepRawStore fuel env7 st st1 baseVar posVar (aTmp + 5)
        bufId wordIdx newWord k hbase7 hpos7 (bind_eq_lookup _ _ _) hwrite
    · intro q hq hqp
      dsimp only [env7, env6, env5, env4, env3, env2, env1]
      rw [bind_ne_lookup _ _ q _ (by unfold VarId at *; omega)]
      rw [bind_ne_lookup _ _ q _ (by unfold VarId at *; omega)]
      rw [bind_ne_lookup _ _ q _ (by unfold VarId at *; omega)]
      rw [bind_ne_lookup _ _ q _ (by unfold VarId at *; omega)]
      rw [bind_ne_lookup _ _ q _ (by unfold VarId at *; omega)]
      rw [bind_ne_lookup _ posVar q _ hqp]
      exact bind_ne_lookup _ _ q _ (Nat.ne_of_lt hq)
  · cases hl

theorem lowerUnboxedFieldLoad_eval_subword (dst baseVar idxVar posVar : VarId)
    (field : PlacedUnboxedField) (k code : LNIRCode) (fuel : Nat) (env : VarEnv)
    (st : HeapState) (bufId : Nat) (idx wordVal : UInt64)
    (hbp : baseVar ≠ posVar)
    (hl : lowerUnboxedFieldLoad dst baseVar idxVar posVar field k = some code)
    (hsub : (field.size == 8 && field.offset % 8 == 0) = false)
    (hbase : env baseVar = some (.rawPtrId bufId))
    (hidx : env idxVar = some (.u64 idx))
    (halign : (idx &&& 7) = 0)
    (hread : st.readElem bufId ((idx >>> 3) + (byteOffsetToWord field.offset).toUInt64).toNat =
      .ok wordVal) :
    ∃ env',
      evalCode fuel env st code = evalCode fuel env' st k ∧
      env' dst = some (.u64 ((wordVal >>> fieldBitOff field) &&& fieldMask field)) ∧
      (∀ q, q < freshAbove (codeMaxVar k) [dst, baseVar, idxVar, posVar] →
        q ≠ dst → q ≠ posVar → env' q = env q) := by
  unfold lowerUnboxedFieldLoad at hl
  split at hl
  · cases hl
    let aTmp := freshAbove (codeMaxVar k) [dst, baseVar, idxVar, posVar]
    have hb_lt : baseVar < aTmp := freshAbove_gt_mem _ _ baseVar (by simp)
    have hi_lt : idxVar < aTmp := freshAbove_gt_mem _ _ idxVar (by simp)
    have hnalign : ¬(((idx &&& 7) != 0) = true) := by rw [halign]; decide
    have hnsub : ¬((field.size == 8 && field.offset % 8 == 0) = true) := by simpa using hsub
    let wordIdx := (idx >>> 3) + (byteOffsetToWord field.offset).toUInt64
    let extracted := (wordVal >>> fieldBitOff field) &&& fieldMask field
    let env1 := env.bind aTmp (.u64 (idx &&& 7))
    let env2 := env1.bind posVar (.u64 wordIdx)
    let env3 := env2.bind (aTmp + 1) (.u64 wordVal)
    let env4 := env3.bind dst (.u64 extracted)
    have hidx1 : env1 idxVar = some (.u64 idx) := by
      dsimp only [env1]
      rw [bind_ne_lookup _ _ idxVar _ (Nat.ne_of_lt hi_lt)]
      exact hidx
    have hbase2 : env2 baseVar = some (.rawPtrId bufId) := by
      dsimp only [env2, env1]
      rw [bind_ne_lookup _ posVar baseVar _ hbp]
      rw [bind_ne_lookup _ _ baseVar _ (Nat.ne_of_lt hb_lt)]
      exact hbase
    refine ⟨env4, ?_, bind_eq_lookup _ _ _, ?_⟩
    · rw [stepLetScalar fuel env st aTmp .i64 _ (.u64 (idx &&& 7)) _
        (by rw [evalScalar_binOp_ok _ _ _ _ _ _ (evalScalar_var_some _ _ _ hidx)
              (evalScalar_constU64 _ _), evalBinOp_bitAnd_u64])]
      rw [stepIteFalse fuel env1 st aTmp (idx &&& 7) _ _ (bind_eq_lookup _ _ _) hnalign]
      rw [stepLetScalar fuel env1 st posVar .i64 _ (.u64 wordIdx) _
        (by rw [evalScalar_binOp_ok _ _ _ _ (.u64 (idx >>> 3)) _
              (by rw [evalScalar_binOp_ok _ _ _ _ _ _ (evalScalar_var_some _ _ _ hidx1)
                    (evalScalar_constU64 _ _), evalBinOp_shr_u64])
              (evalScalar_constU64 _ _), evalBinOp_add_u64])]
      rw [ite_eq_right hnsub]
      rw [stepLetRawLoad fuel env2 st (aTmp + 1) baseVar posVar .i64
        bufId wordIdx wordVal _ hbase2 (bind_eq_lookup _ _ _) hread]
      exact stepLetScalar fuel env3 st dst field.field.kind.lnirType _ (.u64 extracted) k
        (by rw [evalScalar_binOp_ok _ _ _ _ (.u64 (wordVal >>> fieldBitOff field)) _
              (by rw [evalScalar_binOp_ok _ _ _ _ _ _
                    (evalScalar_var_some _ _ _ (bind_eq_lookup _ _ _))
                    (evalScalar_constU64 _ _), evalBinOp_shr_u64])
              (evalScalar_constU64 _ _), evalBinOp_bitAnd_u64])
    · intro q hq hqd hqp
      dsimp only [env4, env3, env2, env1]
      rw [bind_ne_lookup _ dst q _ hqd]
      rw [bind_ne_lookup _ _ q _ (by unfold VarId at *; omega)]
      rw [bind_ne_lookup _ posVar q _ hqp]
      exact bind_ne_lookup _ _ q _ (Nat.ne_of_lt hq)
  · cases hl

theorem lnir_packed_u32_pair_store_load_sound (fuel : Nat) (env : VarEnv)
    (st st1 : HeapState) (bufId : Nat) (idx vx vy oldWord : UInt64)
    (hbase : env 0 = some (.rawPtrId bufId))
    (hidx : env 1 = some (.u64 idx))
    (hvx : env 3 = some (.u64 vx))
    (hvy : env 4 = some (.u64 vy))
    (halign : (idx &&& 7) = 0)
    (hread : st.readElem bufId (idx >>> 3).toNat = .ok oldWord)
    (hwrite : st.writeElemExclusive bufId (idx >>> 3).toNat
      ((oldWord &&& ~~~(((0xffffffff : UInt64) <<< 0))) |||
        (((vx &&& 0xffffffff) <<< 0))) = .ok st1) :
    let layout := mkUnboxedStructLayout "u32_pair"
      [{ name := "x", kind := .u32 }, { name := "y", kind := .u32 }]
    let kRet : LNIRCode := .letBind 7 .i64 (.mkTuple [5, 6]) (.ret 7)
    ∃ loadCode fullCode st2,
      lowerUnboxedStructLoads 0 1 2 layout [5, 6] kRet = some loadCode ∧
      lowerUnboxedStructStore 0 1 2 layout [3, 4] loadCode = some fullCode ∧
      evalCode fuel env st fullCode =
        .ok (.tuple [.u64 (vx &&& 0xffffffff), .u64 (vy &&& 0xffffffff)], st2) := by
  intro layout kRet
  let fx : PlacedUnboxedField :=
    { field := { name := "x", kind := .u32 }, offset := 0, size := 4, align := 4 }
  let fy : PlacedUnboxedField :=
    { field := { name := "y", kind := .u32 }, offset := 4, size := 4, align := 4 }
  have hfields : layout.fields = [fx, fy] := rfl
  have hl_y : ∃ loadY, lowerUnboxedFieldLoad 6 0 1 2 fy kRet = some loadY := by
    unfold lowerUnboxedFieldLoad
    have hf : fieldFitsInWord fy = true := by decide
    rw [ite_eq_left hf]
    exact ⟨_, rfl⟩
  rcases hl_y with ⟨loadY, hloadY⟩
  have hl_x : ∃ loadXY, lowerUnboxedFieldLoad 5 0 1 2 fx loadY = some loadXY := by
    unfold lowerUnboxedFieldLoad
    have hf : fieldFitsInWord fx = true := by decide
    rw [ite_eq_left hf]
    exact ⟨_, rfl⟩
  rcases hl_x with ⟨loadCode, hloadX⟩
  have hloads : lowerUnboxedStructLoads 0 1 2 layout [5, 6] kRet = some loadCode := by
    unfold lowerUnboxedStructLoads
    rw [hfields]
    dsimp only [lowerUnboxedStructLoadsAux, Bind.bind, Option.bind]
    rw [hloadY]
    dsimp only
    exact hloadX
  have hs_y : ∃ storeY, lowerUnboxedFieldStore 0 1 2 4 fy loadCode = some storeY := by
    unfold lowerUnboxedFieldStore
    have hf : fieldFitsInWord fy = true := by decide
    rw [ite_eq_left hf]
    exact ⟨_, rfl⟩
  rcases hs_y with ⟨storeY, hstoreY⟩
  have hs_x : ∃ storeXY, lowerUnboxedFieldStore 0 1 2 3 fx storeY = some storeXY := by
    unfold lowerUnboxedFieldStore
    have hf : fieldFitsInWord fx = true := by decide
    rw [ite_eq_left hf]
    exact ⟨_, rfl⟩
  rcases hs_x with ⟨fullCode, hstoreX⟩
  have hstores : lowerUnboxedStructStore 0 1 2 layout [3, 4] loadCode = some fullCode := by
    unfold lowerUnboxedStructStore
    rw [hfields]
    dsimp only [lowerUnboxedStructStoreAux, Bind.bind, Option.bind]
    rw [hstoreY]
    dsimp only
    exact hstoreX
  have hidx_zero : (idx >>> 3) + (byteOffsetToWord fx.offset).toUInt64 = idx >>> 3 := by
    have hz : (byteOffsetToWord fx.offset).toUInt64 = 0 := by decide
    rw [hz, UInt64.add_zero]
  have hidx_zero_y : (idx >>> 3) + (byteOffsetToWord fy.offset).toUInt64 = idx >>> 3 := by
    have hz : (byteOffsetToWord fy.offset).toUInt64 = 0 := by decide
    rw [hz, UInt64.add_zero]
  let w1 := (oldWord &&& ~~~(fieldMask fx <<< fieldBitOff fx)) |||
    ((vx &&& fieldMask fx) <<< fieldBitOff fx)
  have hw1_def : w1 = ((oldWord &&& ~~~(((0xffffffff : UInt64) <<< 0))) |||
      (((vx &&& 0xffffffff) <<< 0))) := by
    have hmx : fieldMask fx = 0xffffffff := by decide
    have hbx : fieldBitOff fx = 0 := by decide
    dsimp only [w1]
    rw [hmx, hbx]
  have hw1_write : st.writeElemExclusive bufId (idx >>> 3).toNat w1 = .ok st1 := by
    rw [hw1_def]
    exact hwrite
  have hw1_eq : st.writeElemExclusive bufId
      ((idx >>> 3) + (byteOffsetToWord fx.offset).toUInt64).toNat w1 = .ok st1 := by
    rw [hidx_zero]
    exact hw1_write
  have ⟨hrd1, hex2⟩ :=
    writeElemExclusive_readElem_same st st1 bufId (idx >>> 3).toNat w1 hw1_write
  let w2 := (w1 &&& ~~~(fieldMask fy <<< fieldBitOff fy)) |||
    ((vy &&& fieldMask fy) <<< fieldBitOff fy)
  rcases hex2 w2 with ⟨st2, hwrite2⟩
  have ⟨hrd2, _⟩ := writeElemExclusive_readElem_same st1 st2 bufId (idx >>> 3).toNat w2 hwrite2
  have ⟨envA, hevA, hpresA⟩ := lowerUnboxedFieldStore_eval_subword 0 1 2 3 fx storeY fullCode
    fuel env st st1 bufId idx vx oldWord (by decide) (by decide) hstoreX (by decide)
    hbase hidx hvx halign (by rw [hidx_zero]; exact hread) hw1_eq
  have hA0 : envA 0 = some (.rawPtrId bufId) := by
    rw [hpresA 0 (freshAbove_gt_mem _ _ 0 (by simp)) (by decide)]
    exact hbase
  have hA1 : envA 1 = some (.u64 idx) := by
    rw [hpresA 1 (freshAbove_gt_mem _ _ 1 (by simp)) (by decide)]
    exact hidx
  have hA4 : envA 4 = some (.u64 vy) := by
    have h4lt : 4 < freshAbove (codeMaxVar storeY) [0, 1, 2, 3] := by
      have hcm : 4 ≤ codeMaxVar storeY := by
        unfold lowerUnboxedFieldStore at hstoreY
        have hf : fieldFitsInWord fy = true := by decide
        rw [ite_eq_left hf] at hstoreY
        injection hstoreY with hsy
        rw [← hsy]
        have h4f : 4 < freshAbove (codeMaxVar loadCode) [0, 1, 2, 4] :=
          freshAbove_gt_mem _ _ 4 (by simp)
        have hle_max : freshAbove (codeMaxVar loadCode) [0, 1, 2, 4] ≤ codeMaxVar
            (.letBind (freshAbove (codeMaxVar loadCode) [0, 1, 2, 4]) .i64
              (.scalar (.binOp .bitAnd (.var 1) (.constU64 7)))
              (.ite (freshAbove (codeMaxVar loadCode) [0, 1, 2, 4]) .unreachable
                (.letBind 2 .i64
                  (.scalar (.binOp .add (.binOp .shr (.var 1) (.constU64 3))
                    (.constU64 (byteOffsetToWord fy.offset).toUInt64)))
                  (if fy.size == 8 && fy.offset % 8 == 0 then .rawStore 0 2 4 .i64 loadCode
                  else
                    .letBind (freshAbove (codeMaxVar loadCode) [0, 1, 2, 4] + 1) .i64
                      (.rawLoad 0 2 .i64)
                      (.letBind (freshAbove (codeMaxVar loadCode) [0, 1, 2, 4] + 2) .i64
                        (.scalar (.binOp .bitAnd (.var 4) (.constU64 (fieldMask fy))))
                        (.letBind (freshAbove (codeMaxVar loadCode) [0, 1, 2, 4] + 3) .i64
                          (.scalar (.binOp .shl
                            (.var (freshAbove (codeMaxVar loadCode) [0, 1, 2, 4] + 2))
                            (.constU64 (fieldBitOff fy))))
                          (.letBind (freshAbove (codeMaxVar loadCode) [0, 1, 2, 4] + 4) .i64
                            (.scalar (.binOp .bitAnd
                              (.var (freshAbove (codeMaxVar loadCode) [0, 1, 2, 4] + 1))
                              (.unaryOp .not (.binOp .shl (.constU64 (fieldMask fy))
                                (.constU64 (fieldBitOff fy))))))
                            (.letBind (freshAbove (codeMaxVar loadCode) [0, 1, 2, 4] + 5) .i64
                              (.scalar (.binOp .bitOr
                                (.var (freshAbove (codeMaxVar loadCode) [0, 1, 2, 4] + 4))
                                (.var (freshAbove (codeMaxVar loadCode) [0, 1, 2, 4] + 3))))
                              (.rawStore 0 2 (freshAbove (codeMaxVar loadCode) [0, 1, 2, 4] + 5)
                                .i64 loadCode))))))))) := Nat.le_max_left _ _
        exact Nat.le_trans (Nat.le_of_lt h4f) hle_max
      have hbase_lt := freshAbove_gt_base (codeMaxVar storeY) [0, 1, 2, 3]
      unfold VarId at *
      omega
    rw [hpresA 4 h4lt (by decide)]
    exact hvy
  have ⟨envB, hevB, hpresB⟩ := lowerUnboxedFieldStore_eval_subword 0 1 2 4 fy loadCode storeY
    fuel envA st1 st2 bufId idx vy w1 (by decide) (by decide) hstoreY (by decide)
    hA0 hA1 hA4 halign (by rw [hidx_zero_y]; exact hrd1) (by rw [hidx_zero_y]; exact hwrite2)
  have hB0 : envB 0 = some (.rawPtrId bufId) := by
    rw [hpresB 0 (freshAbove_gt_mem _ _ 0 (by simp)) (by decide)]
    exact hA0
  have hB1 : envB 1 = some (.u64 idx) := by
    rw [hpresB 1 (freshAbove_gt_mem _ _ 1 (by simp)) (by decide)]
    exact hA1
  have ⟨envC, hevC, hC5, hpresC⟩ := lowerUnboxedFieldLoad_eval_subword 5 0 1 2 fx loadY loadCode
    fuel envB st2 bufId idx w2 (by decide) hloadX (by decide)
    hB0 hB1 halign (by rw [hidx_zero]; exact hrd2)
  have hC0 : envC 0 = some (.rawPtrId bufId) := by
    rw [hpresC 0 (freshAbove_gt_mem _ _ 0 (by simp)) (by decide) (by decide)]
    exact hB0
  have hC1 : envC 1 = some (.u64 idx) := by
    rw [hpresC 1 (freshAbove_gt_mem _ _ 1 (by simp)) (by decide) (by decide)]
    exact hB1
  have ⟨envD, hevD, hD6, hpresD⟩ := lowerUnboxedFieldLoad_eval_subword 6 0 1 2 fy kRet loadY
    fuel envC st2 bufId idx w2 (by decide) hloadY (by decide)
    hC0 hC1 halign (by rw [hidx_zero_y]; exact hrd2)
  have h5lt : 5 < freshAbove (codeMaxVar kRet) [6, 0, 1, 2] := by
    have hcm : 5 ≤ codeMaxVar kRet := by decide
    have hb := freshAbove_gt_base (codeMaxVar kRet) [6, 0, 1, 2]
    unfold VarId at *
    omega
  have hD5 : envD 5 = some (.u64 ((w2 >>> fieldBitOff fx) &&& fieldMask fx)) := by
    rw [hpresD 5 h5lt (by decide) (by decide)]
    exact hC5
  have h_disj_yx : (fy.offset % 8) + fy.size ≤ fx.offset % 8 ∨
      (fx.offset % 8) + fx.size ≤ fy.offset % 8 := Or.inr (by decide)
  have h_vx_rec : ((w2 >>> fieldBitOff fx) &&& fieldMask fx) = (vx &&& 0xffffffff) := by
    have hd := rmw_subword_disjoint_u64 fy fx w1 vy (by decide) (by decide) h_disj_yx
    have hr := rmw_subword_roundtrip_u64 fx oldWord vx (by decide)
    have hmx : fieldMask fx = 0xffffffff := by decide
    calc ((w2 >>> fieldBitOff fx) &&& fieldMask fx)
      _ = ((w1 >>> fieldBitOff fx) &&& fieldMask fx) := hd
      _ = (vx &&& fieldMask fx) := hr
      _ = (vx &&& 0xffffffff) := by rw [hmx]
  have h_vy_rec : ((w2 >>> fieldBitOff fy) &&& fieldMask fy) = (vy &&& 0xffffffff) := by
    have hr := rmw_subword_roundtrip_u64 fy w1 vy (by decide)
    have hmy : fieldMask fy = 0xffffffff := by decide
    calc ((w2 >>> fieldBitOff fy) &&& fieldMask fy)
      _ = (vy &&& fieldMask fy) := hr
      _ = (vy &&& 0xffffffff) := by rw [hmy]
  rw [h_vx_rec] at hD5
  rw [h_vy_rec] at hD6
  refine ⟨loadCode, fullCode, st2, hloads, hstores, ?_⟩
  rw [hevA, hevB, hevC, hevD]
  dsimp only [kRet, evalCode, evalExpr, evalVarList]
  rw [hD5, hD6]
  dsimp only
  rw [bind_eq_lookup]

-- Defect A.2: Multi-width LLVMAst field store/load round-trip and general disjoint non-interference

private theorem serializeTypedVal_scalar_len (k : UnboxedScalarKind) (v : LLVMVal)
    (hm : fieldValMatchesKind k v = true) :
    (serializeTypedVal k.llvmType v).length = k.byteSize := by
  cases k <;> cases v
  all_goals try (dsimp [fieldValMatchesKind] at hm; contradiction)
  case u8.bits w bv =>
    cases w <;> try (dsimp [fieldValMatchesKind] at hm; contradiction)
    simp [UnboxedScalarKind.llvmType, UnboxedScalarKind.byteSize, serializeTypedVal,
      serializeTypedValAux, LLVMType.sizeOfType, ByteMem.initBytes_length, ByteMem.bvToLEBytes,
      ByteMem.natToLEBytes_length, IntWidth.byteSize]
  case u16.bits w bv =>
    cases w <;> try (dsimp [fieldValMatchesKind] at hm; contradiction)
    simp [UnboxedScalarKind.llvmType, UnboxedScalarKind.byteSize, serializeTypedVal,
      serializeTypedValAux, LLVMType.sizeOfType, ByteMem.initBytes_length, ByteMem.bvToLEBytes,
      ByteMem.natToLEBytes_length, IntWidth.byteSize]
  case u32.bits w bv =>
    cases w <;> try (dsimp [fieldValMatchesKind] at hm; contradiction)
    simp [UnboxedScalarKind.llvmType, UnboxedScalarKind.byteSize, serializeTypedVal,
      serializeTypedValAux, LLVMType.sizeOfType, ByteMem.initBytes_length, ByteMem.bvToLEBytes,
      ByteMem.natToLEBytes_length, IntWidth.byteSize]
  case u64.bits w bv =>
    cases w <;> try (dsimp [fieldValMatchesKind] at hm; contradiction)
    simp [UnboxedScalarKind.llvmType, UnboxedScalarKind.byteSize, serializeTypedVal,
      serializeTypedValAux, LLVMType.sizeOfType, ByteMem.initBytes_length, ByteMem.bvToLEBytes,
      ByteMem.natToLEBytes_length, IntWidth.byteSize]
  case f32.floatBits fw fb =>
    cases fw <;> try (dsimp [fieldValMatchesKind] at hm; contradiction)
    simp [UnboxedScalarKind.llvmType, UnboxedScalarKind.byteSize, serializeTypedVal,
      serializeTypedValAux, LLVMType.sizeOfType, ByteMem.initBytes_length, ByteMem.bvToLEBytes,
      ByteMem.natToLEBytes_length, FloatWidth.byteSize]
  case f64.floatBits fw fb =>
    cases fw <;> try (dsimp [fieldValMatchesKind] at hm; contradiction)
    simp [UnboxedScalarKind.llvmType, UnboxedScalarKind.byteSize, serializeTypedVal,
      serializeTypedValAux, LLVMType.sizeOfType, ByteMem.initBytes_length, ByteMem.bvToLEBytes,
      ByteMem.natToLEBytes_length, FloatWidth.byteSize]

private theorem scalarKind_llvm_byteSize (k : UnboxedScalarKind) :
    k.llvmType.byteSize = k.byteSize := by
  cases k <;> rfl

private theorem scalarKind_align_ne_zero (k : UnboxedScalarKind) :
    k.byteSize ≠ 0 := by
  cases k <;> decide

theorem loadVal_storeTypedVal_same_scalar (m : ByteMem) (addr : BitVec 64)
    (k : UnboxedScalarKind) (v : LLVMVal)
    (hm : fieldValMatchesKind k v = true) :
    loadVal (storeTypedVal m addr k.llvmType v) addr k.llvmType = v := by
  have hlen := serializeTypedVal_scalar_len k v hm
  have hty := scalarKind_llvm_byteSize k
  unfold loadVal storeTypedVal
  rw [hty, ← hlen, ByteMem.readBytesAt_writeBytesAt_same]
  cases k <;> cases v
  all_goals try (dsimp [fieldValMatchesKind] at hm; contradiction)
  case u8.bits w bv =>
    cases w <;> try (dsimp [fieldValMatchesKind] at hm; contradiction)
    have htake : (ByteMem.initBytes (ByteMem.bvToLEBytes IntWidth.i8.byteSize bv)).take
        IntWidth.i8.byteSize =
        ByteMem.initBytes (ByteMem.bvToLEBytes IntWidth.i8.byteSize bv) := by
      apply List.take_of_length_le
      rw [ByteMem.initBytes_length, ByteMem.bvToLEBytes, ByteMem.natToLEBytes_length]
      exact Nat.le_refl _
    simp [UnboxedScalarKind.llvmType, serializeTypedVal, serializeTypedValAux, deserializeVal,
      deserializeValAux, LLVMType.sizeOfType, htake, ByteMem.bytesToBv?_initBytes,
      ByteMem.bvFromLEBytes_bvToLEBytes IntWidth.i8.byteSize bv
        (ByteMem.bits_le_eight_mul_byteSize .i8)]
  case u16.bits w bv =>
    cases w <;> try (dsimp [fieldValMatchesKind] at hm; contradiction)
    have htake : (ByteMem.initBytes (ByteMem.bvToLEBytes IntWidth.i16.byteSize bv)).take
        IntWidth.i16.byteSize =
        ByteMem.initBytes (ByteMem.bvToLEBytes IntWidth.i16.byteSize bv) := by
      apply List.take_of_length_le
      rw [ByteMem.initBytes_length, ByteMem.bvToLEBytes, ByteMem.natToLEBytes_length]
      exact Nat.le_refl _
    simp [UnboxedScalarKind.llvmType, serializeTypedVal, serializeTypedValAux, deserializeVal,
      deserializeValAux, LLVMType.sizeOfType, htake, ByteMem.bytesToBv?_initBytes,
      ByteMem.bvFromLEBytes_bvToLEBytes IntWidth.i16.byteSize bv
        (ByteMem.bits_le_eight_mul_byteSize .i16)]
  case u32.bits w bv =>
    cases w <;> try (dsimp [fieldValMatchesKind] at hm; contradiction)
    have htake : (ByteMem.initBytes (ByteMem.bvToLEBytes IntWidth.i32.byteSize bv)).take
        IntWidth.i32.byteSize =
        ByteMem.initBytes (ByteMem.bvToLEBytes IntWidth.i32.byteSize bv) := by
      apply List.take_of_length_le
      rw [ByteMem.initBytes_length, ByteMem.bvToLEBytes, ByteMem.natToLEBytes_length]
      exact Nat.le_refl _
    simp [UnboxedScalarKind.llvmType, serializeTypedVal, serializeTypedValAux, deserializeVal,
      deserializeValAux, LLVMType.sizeOfType, htake, ByteMem.bytesToBv?_initBytes,
      ByteMem.bvFromLEBytes_bvToLEBytes IntWidth.i32.byteSize bv
        (ByteMem.bits_le_eight_mul_byteSize .i32)]
  case u64.bits w bv =>
    cases w <;> try (dsimp [fieldValMatchesKind] at hm; contradiction)
    have htake : (ByteMem.initBytes (ByteMem.bvToLEBytes IntWidth.i64.byteSize bv)).take
        IntWidth.i64.byteSize =
        ByteMem.initBytes (ByteMem.bvToLEBytes IntWidth.i64.byteSize bv) := by
      apply List.take_of_length_le
      rw [ByteMem.initBytes_length, ByteMem.bvToLEBytes, ByteMem.natToLEBytes_length]
      exact Nat.le_refl _
    simp [UnboxedScalarKind.llvmType, serializeTypedVal, serializeTypedValAux, deserializeVal,
      deserializeValAux, LLVMType.sizeOfType, htake, ByteMem.bytesToBv?_initBytes,
      ByteMem.bvFromLEBytes_bvToLEBytes IntWidth.i64.byteSize bv
        (ByteMem.bits_le_eight_mul_byteSize .i64)]
  case f32.floatBits fw fb =>
    cases fw <;> try (dsimp [fieldValMatchesKind] at hm; contradiction)
    have htake : (ByteMem.initBytes (ByteMem.bvToLEBytes FloatWidth.f32.byteSize fb)).take
        FloatWidth.f32.byteSize =
        ByteMem.initBytes (ByteMem.bvToLEBytes FloatWidth.f32.byteSize fb) := by
      apply List.take_of_length_le
      rw [ByteMem.initBytes_length, ByteMem.bvToLEBytes, ByteMem.natToLEBytes_length]
      exact Nat.le_refl _
    simp [UnboxedScalarKind.llvmType, serializeTypedVal, serializeTypedValAux, deserializeVal,
      deserializeValAux, LLVMType.sizeOfType, htake, ByteMem.bytesToBv?_initBytes,
      ByteMem.bvFromLEBytes_bvToLEBytes FloatWidth.f32.byteSize fb (by decide)]
  case f64.floatBits fw fb =>
    cases fw <;> try (dsimp [fieldValMatchesKind] at hm; contradiction)
    have htake : (ByteMem.initBytes (ByteMem.bvToLEBytes FloatWidth.f64.byteSize fb)).take
        FloatWidth.f64.byteSize =
        ByteMem.initBytes (ByteMem.bvToLEBytes FloatWidth.f64.byteSize fb) := by
      apply List.take_of_length_le
      rw [ByteMem.initBytes_length, ByteMem.bvToLEBytes, ByteMem.natToLEBytes_length]
      exact Nat.le_refl _
    simp [UnboxedScalarKind.llvmType, serializeTypedVal, serializeTypedValAux, deserializeVal,
      deserializeValAux, LLVMType.sizeOfType, htake, ByteMem.bytesToBv?_initBytes,
      ByteMem.bvFromLEBytes_bvToLEBytes FloatWidth.f64.byteSize fb (by decide)]

theorem disjoint_fields_store_noninterference (m : ByteMem) (base : BitVec 64)
    (f1 f2 : PlacedUnboxedField) (v1 v2 : LLVMVal)
    (hsz1 : f1.size = f1.field.kind.byteSize)
    (hsz2 : f2.size = f2.field.kind.byteSize)
    (hm1 : fieldValMatchesKind f1.field.kind v1 = true)
    (hm2 : fieldValMatchesKind f2.field.kind v2 = true)
    (hdisj : f1.offset + f1.size ≤ f2.offset ∨ f2.offset + f2.size ≤ f1.offset)
    (hfit1 : base.toNat + f1.offset < 2 ^ 64)
    (hfit2 : base.toNat + f2.offset < 2 ^ 64) :
    let addr1 := BitVec.ofNat 64 (base.toNat + f1.offset)
    let addr2 := BitVec.ofNat 64 (base.toNat + f2.offset)
    let m' := storeTypedVal (storeTypedVal m addr1 f1.field.kind.llvmType v1)
      addr2 f2.field.kind.llvmType v2
    loadVal m' addr1 f1.field.kind.llvmType = v1 ∧
      loadVal m' addr2 f2.field.kind.llvmType = v2 := by
  intro addr1 addr2 m'
  have ha1 : addr1.toNat = base.toNat + f1.offset := Nat.mod_eq_of_lt hfit1
  have ha2 : addr2.toNat = base.toNat + f2.offset := Nat.mod_eq_of_lt hfit2
  have hlen2 := serializeTypedVal_scalar_len f2.field.kind v2 hm2
  have hty1 := scalarKind_llvm_byteSize f1.field.kind
  have hrd : rangesDisjoint addr2.toNat (serializeTypedVal f2.field.kind.llvmType v2).length
      addr1.toNat f1.field.kind.llvmType.byteSize = true := by
    unfold rangesDisjoint
    rw [hlen2, hty1, ha1, ha2, ← hsz1, ← hsz2]
    exact decide_eq_true (by omega)
  refine ⟨?_, loadVal_storeTypedVal_same_scalar _ addr2 f2.field.kind v2 hm2⟩
  dsimp only [m', loadVal, storeTypedVal]
  rw [ByteMem.readBytesAt_writeBytesAt_disjoint _ addr2.toNat _ addr1.toNat _ hrd]
  exact loadVal_storeTypedVal_same_scalar m addr1 f1.field.kind v1 hm1

private theorem gep_i8_offset_ok (st : ExecState) (ptrReg : RegName) (base : BitVec 64) (off : Nat)
    (hoff : off < 2 ^ 63) :
    gepResult st ptrReg false (.int .i8) base [(.i64, .constInt .i64 (BitVec.ofNat 64 off))] =
      .inr (bindReg st ptrReg (.ptr (BitVec.ofNat 64 (base.toNat + off)))) := by
  have h2_64 : off < 2 ^ 64 := by omega
  have hbv : (BitVec.ofNat 64 off).toNat = off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2_64]
  have hsigned : gepIndexSigned .i64 (BitVec.ofNat 64 off) = Int.ofNat off := by
    unfold gepIndexSigned bvSigned
    change (if Int.ofNat (BitVec.ofNat 64 off).toNat < (2 : Int) ^ 63 then
        Int.ofNat (BitVec.ofNat 64 off).toNat
      else Int.ofNat (BitVec.ofNat 64 off).toNat - (2 : Int) ^ 64) = Int.ofNat off
    rw [hbv]
    have hlt : Int.ofNat off < (2 : Int) ^ 63 := by
      have hpow : (2 : Int) ^ 63 = (9223372036854775808 : Int) := by decide
      rw [hpow]
      exact Int.ofNat_lt.mpr (by simpa using hoff)
    rw [ite_eq_left hlt]
  have hres_nonneg : ¬((base.toNat : Int) + (off : Int) < 0) :=
    Int.not_lt.mpr (Int.add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
  have htonat : ((base.toNat : Int) + (off : Int)).toNat = base.toNat + off := by
    rw [← Int.natCast_add, Int.toNat_natCast]
  unfold gepResult
  simp [evalOperand, isPoison, gepOffset, LLVMType.byteSize, IntWidth.byteSize, hsigned]
  rw [ite_eq_right hres_nonneg, htonat]

private theorem accessCheck_writeBytesAt_eq (m : ByteMem) (addr : BitVec 64)
    (bs : List MemByte) (sz align : Nat) (needWrite : Bool) :
    accessCheck (m.writeBytesAt addr.toNat bs) addr sz align needWrite =
      accessCheck m addr sz align needWrite := by
  unfold accessCheck
  rw [accessInAlloc_writeBytesAt]

theorem emitLLVMFieldStore_load_roundtrip_sound (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (baseReg storePtrReg loadPtrReg valReg dstReg : RegName) (base : BitVec 64)
    (field : PlacedUnboxedField) (v : LLVMVal)
    (hb_sp : baseReg ≠ storePtrReg) (hv_sp : valReg ≠ storePtrReg)
    (hbase : lookupReg st baseReg = some (.ptr base))
    (hval : lookupReg st valReg = some v)
    (hm : fieldValMatchesKind field.field.kind v = true)
    (hsz : field.size = field.field.kind.byteSize)
    (hal : field.align = field.size)
    (hoff : field.offset < 2 ^ 63)
    (hacc : accessCheck st.mem (BitVec.ofNat 64 (base.toNat + field.offset))
      field.size field.align true = none) :
    ∃ st',
      execInstrs mod_ fuel st
        (emitLLVMFieldStore storePtrReg (.reg baseReg) field (.reg valReg) ++
          emitLLVMFieldLoad dstReg loadPtrReg (.reg baseReg) field) = .inr st' ∧
      lookupReg st' dstReg = some v := by
  let fAddr := BitVec.ofNat 64 (base.toNat + field.offset)
  have heff : effectiveAlign field.field.kind.llvmType field.align = field.align := by
    unfold effectiveAlign
    have hnz : field.align ≠ 0 := by
      rw [hal, hsz]
      exact scalarKind_align_ne_zero field.field.kind
    rw [beq_false_of_ne hnz]
    rfl
  have hty_sz : field.field.kind.llvmType.byteSize = field.size := by
    rw [scalarKind_llvm_byteSize, hsz]
  have hs1 : stepInstrWith (runCallWith mod_ fuel) st
      (.getelementptr storePtrReg false (.int .i8) (.reg baseReg)
        [(.i64, .constInt .i64 (BitVec.ofNat 64 field.offset))]) =
      .inr (bindReg st storePtrReg (.ptr fAddr)) := by
    dsimp only [stepInstrWith, evalOperand]
    rw [hbase]
    exact gep_i8_offset_ok st storePtrReg base field.offset hoff
  let st1 := bindReg st storePtrReg (.ptr fAddr)
  have hval1 : lookupReg st1 valReg = some v := by
    dsimp only [st1]
    rw [lookupReg_bindReg_ne st valReg storePtrReg _ hv_sp]
    exact hval
  have hsp1 : lookupReg st1 storePtrReg = some (.ptr fAddr) :=
    lookupReg_bindReg_same st storePtrReg _
  have hs2 : stepInstrWith (runCallWith mod_ fuel) st1
      (.store false field.field.kind.llvmType (.reg valReg) (.reg storePtrReg) field.align) =
      .inr { st1 with mem := storeTypedVal st.mem fAddr field.field.kind.llvmType v } := by
    dsimp only [stepInstrWith, evalTypedOperand, evalOperand]
    rw [hval1, hsp1, heff, hty_sz]
    change (match accessCheck st.mem fAddr field.size field.align true with
      | some "null pointer" => Sum.inl (ExecOutcome.ub "store to null pointer")
      | some "invalid alignment" => Sum.inl (ExecOutcome.ub "invalid alignment")
      | some "misaligned access" => Sum.inl (ExecOutcome.ub "misaligned store")
      | some _ => Sum.inl (ExecOutcome.ub "store out of bounds")
      | none => Sum.inr { st1 with mem := storeTypedVal st.mem fAddr field.field.kind.llvmType v }) = _
    rw [hacc]
  let st2 : ExecState := { st1 with mem := storeTypedVal st.mem fAddr field.field.kind.llvmType v }
  have hbase2 : lookupReg st2 baseReg = some (.ptr base) := by
    change lookupReg st1 baseReg = some (.ptr base)
    rw [lookupReg_bindReg_ne st baseReg storePtrReg _ hb_sp]
    exact hbase
  have hs3 : stepInstrWith (runCallWith mod_ fuel) st2
      (.getelementptr loadPtrReg false (.int .i8) (.reg baseReg)
        [(.i64, .constInt .i64 (BitVec.ofNat 64 field.offset))]) =
      .inr (bindReg st2 loadPtrReg (.ptr fAddr)) := by
    dsimp only [stepInstrWith, evalOperand]
    rw [hbase2]
    exact gep_i8_offset_ok st2 loadPtrReg base field.offset hoff
  let st3 := bindReg st2 loadPtrReg (.ptr fAddr)
  have hlp3 : lookupReg st3 loadPtrReg = some (.ptr fAddr) :=
    lookupReg_bindReg_same st2 loadPtrReg _
  have hacc3 : accessCheck st3.mem fAddr field.size field.align false = none := by
    change accessCheck (storeTypedVal st.mem fAddr field.field.kind.llvmType v)
      fAddr field.size field.align false = none
    unfold storeTypedVal
    rw [accessCheck_writeBytesAt_eq]
    exact accessCheck_read_of_write st.mem fAddr field.size field.align hacc
  have hs4 : stepInstrWith (runCallWith mod_ fuel) st3
      (.load dstReg false field.field.kind.llvmType (.reg loadPtrReg) field.align) =
      .inr (bindReg st3 dstReg v) := by
    dsimp only [stepInstrWith, evalOperand]
    rw [hlp3, heff, hty_sz]
    change (match accessCheck st3.mem fAddr field.size field.align false with
      | some "null pointer" => Sum.inl (ExecOutcome.ub "load from null pointer")
      | some "invalid alignment" => Sum.inl (ExecOutcome.ub "invalid alignment")
      | some "misaligned access" => Sum.inl (ExecOutcome.ub "misaligned load")
      | some _ => Sum.inl (ExecOutcome.ub "load out of bounds")
      | none => Sum.inr (bindReg st3 dstReg (loadVal st3.mem fAddr field.field.kind.llvmType))) = _
    rw [hacc3]
    change Sum.inr (bindReg st3 dstReg
      (loadVal (storeTypedVal st.mem fAddr field.field.kind.llvmType v)
        fAddr field.field.kind.llvmType)) = .inr (bindReg st3 dstReg v)
    rw [loadVal_storeTypedVal_same_scalar st.mem fAddr field.field.kind v hm]
  refine ⟨bindReg st3 dstReg v, ?_, lookupReg_bindReg_same st3 dstReg v⟩
  change execInstrsWith (runCallWith mod_ fuel) st
      ([ LLVMInstr.getelementptr storePtrReg false (.int .i8) (.reg baseReg)
           [(.i64, .constInt .i64 (BitVec.ofNat 64 field.offset))]
       , LLVMInstr.store false field.field.kind.llvmType (.reg valReg) (.reg storePtrReg) field.align
       , LLVMInstr.getelementptr loadPtrReg false (.int .i8) (.reg baseReg)
           [(.i64, .constInt .i64 (BitVec.ofNat 64 field.offset))]
       , LLVMInstr.load dstReg false field.field.kind.llvmType (.reg loadPtrReg) field.align ]) =
    Sum.inr (bindReg st3 dstReg v)
  dsimp only [execInstrsWith]
  rw [hs1]
  dsimp only
  rw [hs2]
  dsimp only
  rw [hs3]
  dsimp only
  rw [hs4]

-- Defect B: Escape equivalence, conservative rejection, and optimizeThreadLocalOwnershipRC non-vacuity

private theorem tlScalarMentions_eq (aliases : List VarId) (se : ScalarExpr) :
    tlScalarMentions aliases se = scalarMentions aliases se := by
  induction se with
  | constU64 _ | constBool _ | var _ => rfl
  | binOp _ l r ihl ihr => simp [tlScalarMentions, scalarMentions, ihl, ihr]
  | unaryOp _ a ih => simp [tlScalarMentions, scalarMentions, ih]
  | select c t e ihc iht ihe => simp [tlScalarMentions, scalarMentions, ihc, iht, ihe]
  | fma a b c iha ihb ihc => simp [tlScalarMentions, scalarMentions, iha, ihb, ihc]

private theorem tlExprMayAlias_eq (aliases : List VarId) (e : LNIRExpr) :
    tlExprMayAlias aliases e = exprMayAlias aliases e := by
  cases e with
  | scalar se => exact tlScalarMentions_eq aliases se
  | _ => rfl

private theorem tlExprEscapesWith_eq (aliases : List VarId) (e : LNIRExpr) :
    tlExprEscapesWith aliases e = exprEscapesWith aliases e := by
  cases e <;> rfl

private theorem tlKernelMentions_eq (aliases : List VarId) (kern : ParallelKernelKind) :
    tlKernelMentions aliases kern = kernelMentions aliases kern := by
  cases kern with
  | customScalar idxVar inVars body =>
    unfold tlKernelMentions kernelMentions
    exact tlScalarMentions_eq _ body
  | _ => rfl

private theorem tlCodeEscapesWith_eq (aliases : List VarId) (code : LNIRCode) :
    tlCodeEscapesWith aliases code = codeEscapesWith aliases code := by
  induction code generalizing aliases with
  | letBind dst ty val k ih =>
    dsimp only [tlCodeEscapesWith, codeEscapesWith]
    rw [tlExprMayAlias_eq, tlExprEscapesWith_eq, ih]
  | rawStore p i x ty k ih =>
    dsimp only [tlCodeEscapesWith, codeEscapesWith]
    rw [ih]
  | incRef ov c k ih =>
    dsimp only [tlCodeEscapesWith, codeEscapesWith]
    exact ih aliases
  | decRef ov c k ih =>
    dsimp only [tlCodeEscapesWith, codeEscapesWith]
    exact ih aliases
  | ite cv t e iht ihe =>
    dsimp only [tlCodeEscapesWith, codeEscapesWith]
    rw [iht, ihe]
  | seqFor iv lo hi av init aty step k ihs ihk =>
    dsimp only [tlCodeEscapesWith, codeEscapesWith]
    rw [ihs, ihk]
  | parFor ov lv ins ety kern k ih =>
    dsimp only [tlCodeEscapesWith, codeEscapesWith]
    rw [tlKernelMentions_eq, ih]
  | ret r => rfl
  | unreachable => rfl

theorem tlCheckNonEscaping_eq_checkThreadLocalNonEscaping (v : VarId) (code : LNIRCode) :
    tlCheckNonEscaping v code = checkThreadLocalNonEscaping v code := by
  unfold tlCheckNonEscaping checkThreadLocalNonEscaping codeEscapes
  rw [tlCodeEscapesWith_eq]

theorem checkThreadLocalNonEscaping_rejects_alias_escapes (p q : VarId) (idx tag : Nat) :
    checkThreadLocalNonEscaping p
      (.letBind q .objPtr (.call "lean_native_ensure_exclusive" [p] .objPtr false) (.ret q)) =
      false ∧
    checkThreadLocalNonEscaping p
      (.letBind q .objPtr (.projTuple p idx) (.ret q)) = false ∧
    checkThreadLocalNonEscaping p
      (.letBind q .objPtr (.allocCtor tag [p] []) (.ret 0)) = false ∧
    (p ≠ q → checkThreadLocalNonEscaping p
      (.letBind q .i64 (.sarrayLen p) (.ret q)) = true) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [checkThreadLocalNonEscaping, codeEscapes, codeEscapesWith, exprEscapesWith, exprMayAlias]
  · simp [checkThreadLocalNonEscaping, codeEscapes, codeEscapesWith, exprEscapesWith, exprMayAlias]
  · simp [checkThreadLocalNonEscaping, codeEscapes, codeEscapesWith, exprEscapesWith]
  · intro hpq
    simp [checkThreadLocalNonEscaping, codeEscapes, codeEscapesWith, exprEscapesWith,
      exprMayAlias, hpq.symm]

theorem optimizeThreadLocalOwnershipRC_preserves_escaping_mark_mt
    (dst arg : VarId) (retTy : LNIRType) (k : LNIRCode)
    (hesc : checkThreadLocalNonEscaping arg k = false) :
    optimizeThreadLocalOwnershipRC
      (.letBind dst retTy (.call "lean_mark_mt" [arg] retTy false) k) =
      .letBind dst retTy (.call "lean_mark_mt" [arg] retTy false)
        (optimizeThreadLocalOwnershipRC k) := by
  have htl : tlCheckNonEscaping arg k = false := by
    rw [tlCheckNonEscaping_eq_checkThreadLocalNonEscaping]
    exact hesc
  have hcan : canElideMarkMt (.call "lean_mark_mt" [arg] retTy false) k = false := by
    simp [canElideMarkMt, htl]
  dsimp only [optimizeThreadLocalOwnershipRC, Transform.optimizeThreadLocalOwnershipRC,
    Transform.elideMarkMtAndZeroRc]
  rw [ite_eq_right (by simpa using hcan)]
  rfl

theorem optimizeThreadLocalOwnershipRC_mark_mt_nonvacuous (fuel : Nat) :
    let src : LNIRCode :=
      .letBind 0 .i64 (.call "lean_mark_mt" [1] .i64 false)
        (.incRef 1 0 (.letBind 2 .i64 (.scalar (.constU64 42)) (.ret 2)))
    let env := VarEnv.empty.bind 1 (.objPtr 7)
    let st : HeapState := { buffers := [], nextId := 8, refCounts := [(true, 7, 1)] }
    src ≠ optimizeThreadLocalOwnershipRC src ∧
      evalCode fuel env st src = .ok (.u64 42, st) ∧
      evalCode fuel env st (optimizeThreadLocalOwnershipRC src) = .ok (.u64 42, st) := by
  intro src env st
  refine ⟨?_, rfl, rfl⟩
  intro h
  have hexpr : LNIRExpr.call "lean_mark_mt" [1] .i64 false = LNIRExpr.scalar (.constU64 0) := by
    change (match src with | .letBind _ _ e _ => e | _ => .scalar (.constU64 1)) =
      (match optimizeThreadLocalOwnershipRC src with
       | .letBind _ _ e _ => e
       | _ => .scalar (.constU64 1))
    rw [← h]
  cases hexpr

-- Defect C: recvSlot disjointness and well-formedness preservation

private theorem list_filter_map_objId_not_contains (slots : List SendableSlot) (objId : Nat) :
    ((slots.filter (·.objId != objId)).map (·.objId)).contains objId = false := by
  rw [List.contains_eq_mem, decide_eq_false_iff_not]
  intro hmem
  rcases List.mem_map.mp hmem with ⟨s, hs, hid⟩
  have hflt := (List.mem_filter.mp hs).2
  rw [hid] at hflt
  simp at hflt

private theorem idsDisjoint_filter_right_slots (xs : List Nat) (slots : List SendableSlot)
    (p : SendableSlot → Bool)
    (h : idsDisjoint xs (slots.map (·.objId)) = true) :
    idsDisjoint xs ((slots.filter p).map (·.objId)) = true := by
  unfold idsDisjoint at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro x hx
  have hnot := h x hx
  rw [Bool.not_eq_true'] at hnot ⊢
  rw [List.contains_eq_mem, decide_eq_false_iff_not] at hnot ⊢
  intro hmem
  rcases List.mem_map.mp hmem with ⟨s, hs, hid⟩
  exact hnot (List.mem_map.mpr ⟨s, (List.mem_filter.mp hs).1, hid⟩)

private theorem idsDisjoint_filter_left_slots (slots : List SendableSlot) (ys : List Nat)
    (p : SendableSlot → Bool)
    (h : idsDisjoint (slots.map (·.objId)) ys = true) :
    idsDisjoint ((slots.filter p).map (·.objId)) ys = true := by
  unfold idsDisjoint at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro x hx
  rcases List.mem_map.mp hx with ⟨s, hs, rfl⟩
  exact h s.objId (List.mem_map.mpr ⟨s, (List.mem_filter.mp hs).1, rfl⟩)

theorem sendableRecv_preserves_disjoint (ch ch' : SendableChannelState) (objId : Nat)
    (slot : SendableSlot)
    (hdisj : channelDisjoint ch = true)
    (hrecv : recvSlot ch objId = some (slot, ch')) :
    slot.objId = objId ∧
      slotWellFormed slot = true ∧
      ch'.inFlight.any (·.objId == objId) = false ∧
      ch'.receiverOwned.contains objId = true ∧
      channelDisjoint ch' = true := by
  unfold recvSlot at hrecv
  cases hfind : ch.inFlight.find? (·.objId == objId) with
  | none =>
    rw [hfind] at hrecv
    cases hrecv
  | some s =>
    rw [hfind] at hrecv
    dsimp only at hrecv
    by_cases hown : (ch.senderOwned.contains objId || ch.receiverOwned.contains objId) = true
    · rw [ite_eq_left hown] at hrecv
      cases hrecv
    · rw [ite_eq_right hown] at hrecv
      injection hrecv with hpair
      injection hpair with hs hch'
      subst hs
      subst hch'
      have hmem : s ∈ ch.inFlight := List.mem_of_find?_eq_some hfind
      have hid : s.objId = objId :=
        of_decide_eq_true (List.find?_some (p := fun x : SendableSlot => x.objId == objId) hfind)
      have hown_f := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hown)
      unfold channelDisjoint at hdisj
      simp only [Bool.and_eq_true] at hdisj
      rcases hdisj with ⟨⟨⟨hsf, hsr⟩, hfr⟩, hwf⟩
      have hslot_wf : slotWellFormed s = true := (List.all_eq_true.mp hwf) s hmem
      have hany_f : (ch.inFlight.filter (·.objId != objId)).any (·.objId == objId) = false := by
        rw [Bool.eq_false_iff]
        intro hany
        rcases List.any_eq_true.mp hany with ⟨x, hx, hxid⟩
        have hflt := (List.mem_filter.mp hx).2
        have hxeq : x.objId = objId := of_decide_eq_true hxid
        rw [hxeq] at hflt
        simp at hflt
      have hro_in : (objId :: ch.receiverOwned).contains objId = true := by simp
      refine ⟨hid, hslot_wf, hany_f, hro_in, ?_⟩
      unfold channelDisjoint
      simp only [Bool.and_eq_true]
      refine ⟨⟨⟨idsDisjoint_filter_right_slots _ _ _ hsf,
        idsDisjoint_cons_right _ _ objId hsr hown_f.1⟩,
        idsDisjoint_cons_right _ _ objId (idsDisjoint_filter_left_slots _ _ _ hfr)
          (list_filter_map_objId_not_contains ch.inFlight objId)⟩, ?_⟩
      rw [List.all_eq_true]
      intro x hx
      exact (List.all_eq_true.mp hwf) x (List.mem_filter.mp hx).1

theorem disjoint_fields_storeInt_noninterference (m : ByteMem) (base : BitVec 64)
    (f1 f2 : PlacedUnboxedField) (w1 w2 : IntWidth) (v1 : BitVec w1.bits) (v2 : BitVec w2.bits)
    (hsz1 : f1.size = w1.byteSize) (hsz2 : f2.size = w2.byteSize)
    (hdisj : f1.offset + f1.size ≤ f2.offset ∨ f2.offset + f2.size ≤ f1.offset)
    (hfit1 : base.toNat + f1.offset < 2 ^ 64) (hfit2 : base.toNat + f2.offset < 2 ^ 64) :
    let addr1 := BitVec.ofNat 64 (base.toNat + f1.offset)
    let addr2 := BitVec.ofNat 64 (base.toNat + f2.offset)
    let m' := (m.storeInt addr1 w1 v1).storeInt addr2 w2 v2
    m'.loadInt? addr1 w1 = some v1 ∧ m'.loadInt? addr2 w2 = some v2 := by
  intro addr1 addr2 m'
  have ha1 : addr1.toNat = base.toNat + f1.offset := Nat.mod_eq_of_lt hfit1
  have ha2 : addr2.toNat = base.toNat + f2.offset := Nat.mod_eq_of_lt hfit2
  have hrd : rangesDisjoint addr2.toNat w2.byteSize addr1.toNat w1.byteSize = true := by
    unfold rangesDisjoint
    rw [ha1, ha2, ← hsz1, ← hsz2]
    exact decide_eq_true (by omega)
  refine ⟨?_, ByteMem.loadInt?_storeInt_same _ addr2 w2 v2⟩
  rw [ByteMem.loadInt?_storeInt_disjoint _ addr2 w2 v2 addr1 w1 hrd]
  exact ByteMem.loadInt?_storeInt_same m addr1 w1 v1


theorem unboxedRegion_pipeline_nonvacuous (fuel : Nat) :
    let layout := mkUnboxedStructLayout "pair"
      [{ name := "x", kind := .u64 }, { name := "y", kind := .u64 }]
    let slice : BorrowedRegionSlice :=
      { ptrVar := 3, view := { backingLen := 16, offset := 0, len := 16 }, own := .borrowed }
    let env := (VarEnv.empty.bind 2 (.u64 8)).bind 4 (.rawPtrId 0)
    let st : HeapState :=
      { buffers := [{ id := 0, exclusive := true, data := #[10, 42, 99, 7, 5, 3, 2, 1, 8, 9] }]
        nextId := 1 }
    layoutWellFormed layout = true ∧
      lowerUnboxedRegionRcFree 0 10 2 layout slice 4 = true ∧
      ∃ rawCode,
        lowerUnboxedRegionCode 0 10 2 layout slice 4
          (.letBind 9 .i64 (.scalar (.binOp .add (.var 0) (.var 1))) (.ret 9)) = some rawCode ∧
        evalCode fuel env st (elideMarkMtAndZeroRc rawCode) = .ok (.u64 141, st) := by
  refine ⟨by decide, by decide, _, rfl, ?_⟩
  rfl

end LeanNative.Proofs
