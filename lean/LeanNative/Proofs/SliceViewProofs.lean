import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.IR.SliceView
import LeanNative.Spec

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics

/-! ## C8 Deliverable 3 Soundness Proofs: Zero-Copy Slice Views

Zero `def`, zero `structure`, zero `inductive` in this file. Standard axioms only.
-/

private theorem evalAddConst_u64 (env : VarEnv) (st : HeapState) (c : UInt64) (v : VarId)
    (b : UInt64) (hv : env v = some (.u64 b)) :
    evalExpr env st (.scalar (.binOp .add (.constU64 c) (.var v))) = .ok (.u64 (c + b), st) := by
  dsimp only [evalExpr, evalScalarExpr]
  rw [hv]
  rfl

private theorem evalAddVars_u64 (env : VarEnv) (st : HeapState) (v1 v2 : VarId)
    (a b : UInt64) (h1 : env v1 = some (.u64 a)) (h2 : env v2 = some (.u64 b)) :
    evalExpr env st (.scalar (.binOp .add (.var v1) (.var v2))) = .ok (.u64 (a + b), st) := by
  dsimp only [evalExpr, evalScalarExpr]
  rw [h1, h2]
  rfl

private theorem evalSarrayGet_ok (env : VarEnv) (st : HeapState) (arrVar idxVar : VarId)
    (ty : LNIRType) (bufId : Nat) (idx elem : UInt64)
    (harr : env arrVar = some (.sarrayId bufId)) (hidx : env idxVar = some (.u64 idx))
    (hread : st.readElem bufId idx.toNat = .ok elem) :
    evalExpr env st (.sarrayGet arrVar idxVar ty) = .ok (.u64 (maskElemVal ty elem), st) := by
  dsimp only [evalExpr]
  rw [harr, hidx]
  dsimp only
  rw [hread]

private theorem evalRawLoad_ok (env : VarEnv) (st : HeapState) (ptrVar idxVar : VarId)
    (ty : LNIRType) (bufId : Nat) (idx elem : UInt64)
    (hptr : env ptrVar = some (.rawPtrId bufId)) (hidx : env idxVar = some (.u64 idx))
    (hread : st.readElem bufId idx.toNat = .ok elem) :
    evalExpr env st (.rawLoad ptrVar idxVar ty) = .ok (.u64 (maskElemVal ty elem), st) := by
  dsimp only [evalExpr]
  rw [hptr, hidx]
  dsimp only
  rw [hread]

/-- A checked sub-slice is a valid view whose window is `[offset + subOff, subLen)` in the same buffer. -/
theorem checkedSubSlice_valid (s sub : TypedSliceView) (subOff subLen : Nat)
    (h : checkedSubSlice s subOff subLen = some sub) :
    checkSliceViewValid sub = true ∧ sub.view.backingLen = s.view.backingLen ∧
      sub.view.offset = s.view.offset + subOff ∧ sub.view.len = subLen := by
  unfold checkedSubSlice at h
  by_cases hgate : LeanNative.Spec.isValidByteSlice s.view && decide (subOff + subLen ≤ s.view.len)
  · simp only [hgate, ↓reduceIte] at h
    have hsub : sub = { s with view := LeanNative.Spec.subSliceView s.view subOff subLen } := by
      injection h with h'
      exact h'.symm
    have hboth := (Bool.and_eq_true _ _).mp hgate
    have hvalid := LeanNative.Spec.subSliceView_valid s.view subOff subLen
      hboth.1 (of_decide_eq_true hboth.2)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [checkSliceViewValid, hsub] using hvalid
    · simp [hsub, LeanNative.Spec.subSliceView]
    · simp [hsub, LeanNative.Spec.subSliceView]
    · simp [hsub, LeanNative.Spec.subSliceView]
  · simp only [hgate, Bool.false_eq_true, ↓reduceIte] at h
    cases h

/-- An out-of-window sub-slice is rejected by the checked gate. -/
theorem checkedSubSlice_oob_rejects (s : TypedSliceView) (subOff subLen : Nat)
    (hoob : s.view.len < subOff + subLen) :
    checkedSubSlice s subOff subLen = none := by
  unfold checkedSubSlice
  have hdec : decide (subOff + subLen ≤ s.view.len) = false := decide_eq_false (Nat.not_le.mpr hoob)
  simp [hdec]

/-- Sub-slice bounds theorem (`subSliceBounds_no_oob`): every index inside a checked sub-slice
    lands strictly inside the parent backing buffer, so the read is never `.outOfBounds`. -/
theorem subSliceBounds_no_oob (s sub : TypedSliceView) (subOff subLen idx : Nat)
    (st : HeapState) (bufId : Nat) (buf : ArrayBuffer)
    (hsub : checkedSubSlice s subOff subLen = some sub) (hidx : idx < sub.view.len)
    (hfind : st.findBuffer bufId = some buf) (hsize : s.view.backingLen ≤ buf.data.size) :
    (st.readElem bufId (sub.view.offset + idx)).isOk = true := by
  have ⟨hvalid, hback, _, _⟩ := checkedSubSlice_valid s sub subOff subLen hsub
  have hwin : sub.view.offset + sub.view.len ≤ sub.view.backingLen := by
    simpa [checkSliceViewValid, LeanNative.Spec.isValidByteSlice] using of_decide_eq_true hvalid
  have hlt : sub.view.offset + idx < buf.data.size := by omega
  simp only [HeapState.readElem, hfind, hlt, ↓reduceDIte]
  rfl

/-- Zero-copy indexed read: `lowerSliceGet` loads the masked element at `offset + idx`. -/
theorem lowerSliceGet_sound (fuel : Nat) (env : VarEnv) (st : HeapState)
    (dst posTmp idxVar : VarId) (s : TypedSliceView) (idx bufId : Nat) (buf : ArrayBuffer)
    (harr : env s.arrVar = some (.sarrayId bufId)) (hidx : env idxVar = some (.u64 idx.toUInt64))
    (hne : s.arrVar ≠ posTmp) (hvalid : checkSliceViewValid s = true) (hbound : idx < s.view.len)
    (hfind : st.findBuffer bufId = some buf) (hsize : s.view.backingLen ≤ buf.data.size)
    (hu64 : buf.data.size < UInt64.size) :
    evalCode fuel env st (lowerSliceGet dst posTmp s idxVar (.ret dst)) =
      .ok (.u64 (maskElemVal s.kind.lnirType (buf.data[s.view.offset + idx]?.getD 0)), st) := by
  have hwin : s.view.offset + s.view.len ≤ s.view.backingLen := by
    simpa [checkSliceViewValid, LeanNative.Spec.isValidByteSlice] using of_decide_eq_true hvalid
  have hpos : s.view.offset + idx < buf.data.size := by omega
  have hwrap : (s.view.offset.toUInt64 + idx.toUInt64).toNat = s.view.offset + idx := by
    have hlt64 : s.view.offset + idx < UInt64.size := Nat.lt_trans hpos hu64
    have hoff64 : s.view.offset < UInt64.size := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hlt64
    have hidx64 : idx < UInt64.size := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hlt64
    simp only [Nat.toUInt64, UInt64.toNat_add, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt hoff64, Nat.mod_eq_of_lt hidx64, Nat.mod_eq_of_lt hlt64]
  unfold lowerSliceGet
  rw [evalCode, evalAddConst_u64 env st s.view.offset.toUInt64 idxVar idx.toUInt64 hidx]
  dsimp only
  let env1 := env.bind posTmp (.u64 (s.view.offset.toUInt64 + idx.toUInt64))
  have harr' : env1 s.arrVar = some (.sarrayId bufId) := by simp [env1, beq_false_of_ne hne, harr]
  have hread : st.readElem bufId (s.view.offset.toUInt64 + idx.toUInt64).toNat =
      .ok buf.data[s.view.offset + idx] := by
    simp only [HeapState.readElem, hfind, hwrap, hpos, ↓reduceDIte]
  rw [evalCode, evalSarrayGet_ok env1 st s.arrVar posTmp s.kind.lnirType bufId _ _
    harr' (VarEnv.bind_self _ _ _) hread]
  dsimp only
  rw [evalCode]
  simp [hpos]

/-- Zero-copy raw-pointer load: `lowerSliceRawLoad` loads the masked element at `offset + idx`. -/
theorem lowerSliceRawLoad_sound (fuel : Nat) (env : VarEnv) (st : HeapState)
    (dst posTmp idxVar : VarId) (s : TypedSliceView) (idx bufId : Nat) (buf : ArrayBuffer)
    (harr : env s.arrVar = some (.rawPtrId bufId)) (hidx : env idxVar = some (.u64 idx.toUInt64))
    (hne : s.arrVar ≠ posTmp) (hvalid : checkSliceViewValid s = true) (hbound : idx < s.view.len)
    (hfind : st.findBuffer bufId = some buf) (hsize : s.view.backingLen ≤ buf.data.size)
    (hu64 : buf.data.size < UInt64.size) :
    evalCode fuel env st (lowerSliceRawLoad dst posTmp s idxVar (.ret dst)) =
      .ok (.u64 (maskElemVal s.kind.lnirType (buf.data[s.view.offset + idx]?.getD 0)), st) := by
  have hwin : s.view.offset + s.view.len ≤ s.view.backingLen := by
    simpa [checkSliceViewValid, LeanNative.Spec.isValidByteSlice] using of_decide_eq_true hvalid
  have hpos : s.view.offset + idx < buf.data.size := by omega
  have hwrap : (s.view.offset.toUInt64 + idx.toUInt64).toNat = s.view.offset + idx := by
    have hlt64 : s.view.offset + idx < UInt64.size := Nat.lt_trans hpos hu64
    have hoff64 : s.view.offset < UInt64.size := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hlt64
    have hidx64 : idx < UInt64.size := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hlt64
    simp only [Nat.toUInt64, UInt64.toNat_add, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt hoff64, Nat.mod_eq_of_lt hidx64, Nat.mod_eq_of_lt hlt64]
  unfold lowerSliceRawLoad
  rw [evalCode, evalAddConst_u64 env st s.view.offset.toUInt64 idxVar idx.toUInt64 hidx]
  dsimp only
  let env1 := env.bind posTmp (.u64 (s.view.offset.toUInt64 + idx.toUInt64))
  have harr' : env1 s.arrVar = some (.rawPtrId bufId) := by simp [env1, beq_false_of_ne hne, harr]
  have hread : st.readElem bufId (s.view.offset.toUInt64 + idx.toUInt64).toNat =
      .ok buf.data[s.view.offset + idx] := by
    simp only [HeapState.readElem, hfind, hwrap, hpos, ↓reduceDIte]
  rw [evalCode, evalRawLoad_ok env1 st s.arrVar posTmp s.kind.lnirType bufId _ _
    harr' (VarEnv.bind_self _ _ _) hread]
  dsimp only
  rw [evalCode]
  simp [hpos]

/-- One step of a zero-copy slice fold: accumulator `acc` grows by masked `buf.data[offset + curIdx]`. -/
theorem sliceFoldStep_sound (fuel : Nat) (env : VarEnv) (st : HeapState)
    (s : TypedSliceView) (idxVar accVar posTmp elemTmp nextAcc : VarId)
    (curIdx : Nat) (acc : UInt64) (bufId : Nat) (buf : ArrayBuffer)
    (harr : env s.arrVar = some (.sarrayId bufId))
    (hidx : env idxVar = some (.u64 curIdx.toUInt64))
    (hacc : env accVar = some (.u64 acc))
    (hne2 : s.arrVar ≠ posTmp) (hne5 : accVar ≠ elemTmp) (hne6 : accVar ≠ posTmp)
    (hvalid : checkSliceViewValid s = true) (hbound : curIdx < s.view.len)
    (hfind : st.findBuffer bufId = some buf) (hsize : s.view.backingLen ≤ buf.data.size)
    (hu64 : buf.data.size < UInt64.size) :
    evalCode fuel env st (sliceFoldStep s idxVar accVar posTmp elemTmp nextAcc) =
      .ok (.u64 (acc + maskElemVal s.kind.lnirType (buf.data[s.view.offset + curIdx]?.getD 0)), st) := by
  have hwin : s.view.offset + s.view.len ≤ s.view.backingLen := by
    simpa [checkSliceViewValid, LeanNative.Spec.isValidByteSlice] using of_decide_eq_true hvalid
  have hpos : s.view.offset + curIdx < buf.data.size := by omega
  have hwrap : (s.view.offset.toUInt64 + curIdx.toUInt64).toNat = s.view.offset + curIdx := by
    have hlt64 : s.view.offset + curIdx < UInt64.size := Nat.lt_trans hpos hu64
    have hoff64 : s.view.offset < UInt64.size := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hlt64
    have hidx64 : curIdx < UInt64.size := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hlt64
    simp only [Nat.toUInt64, UInt64.toNat_add, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt hoff64, Nat.mod_eq_of_lt hidx64, Nat.mod_eq_of_lt hlt64]
  unfold sliceFoldStep
  rw [evalCode, evalAddConst_u64 env st s.view.offset.toUInt64 idxVar curIdx.toUInt64 hidx]
  dsimp only
  let env1 := env.bind posTmp (.u64 (s.view.offset.toUInt64 + curIdx.toUInt64))
  have harr1 : env1 s.arrVar = some (.sarrayId bufId) := by simp [env1, beq_false_of_ne hne2, harr]
  have hread : st.readElem bufId (s.view.offset.toUInt64 + curIdx.toUInt64).toNat =
      .ok buf.data[s.view.offset + curIdx] := by
    simp only [HeapState.readElem, hfind, hwrap, hpos, ↓reduceDIte]
  rw [evalCode, evalSarrayGet_ok env1 st s.arrVar posTmp s.kind.lnirType bufId _ _
    harr1 (VarEnv.bind_self _ _ _) hread]
  dsimp only
  let env2 := env1.bind elemTmp (.u64 (maskElemVal s.kind.lnirType buf.data[s.view.offset + curIdx]))
  have hacc2 : env2 accVar = some (.u64 acc) := by
    simp [env2, env1, beq_false_of_ne hne5, beq_false_of_ne hne6, hacc]
  rw [evalCode, evalAddVars_u64 env2 st accVar elemTmp acc _ hacc2 (VarEnv.bind_self _ _ _)]
  dsimp only
  rw [evalCode]
  simp [hpos]

/-- Inductive loop invariant for `lowerSliceFold` over `count` remaining elements. -/
theorem sliceFoldLoop_sound (fuel : Nat) (env : VarEnv) (st : HeapState)
    (s : TypedSliceView) (idxVar accVar posTmp elemTmp nextAcc : VarId)
    (bufId : Nat) (buf : ArrayBuffer)
    (harr : env s.arrVar = some (.sarrayId bufId))
    (hne1 : idxVar ≠ accVar) (hne2 : s.arrVar ≠ posTmp) (hne3 : s.arrVar ≠ accVar)
    (hne4 : s.arrVar ≠ idxVar) (hne5 : accVar ≠ elemTmp) (hne6 : accVar ≠ posTmp)
    (hvalid : checkSliceViewValid s = true)
    (hfind : st.findBuffer bufId = some buf) (hsize : s.view.backingLen ≤ buf.data.size)
    (hu64 : buf.data.size < UInt64.size) :
    ∀ (count curIdx : Nat) (acc : UInt64),
      curIdx + count ≤ s.view.len →
      evalSeqLoop count curIdx idxVar accVar (.u64 acc) env st
        (fun stepEnv stepSt => evalCode fuel stepEnv stepSt
          (sliceFoldStep s idxVar accVar posTmp elemTmp nextAcc)) =
      .ok (.u64 (sumSliceFrom s.kind.lnirType buf.data (s.view.offset + curIdx) acc count), st) := by
  intro count
  induction count with
  | zero =>
    intro curIdx acc _
    simp [evalSeqLoop, sumSliceFrom]
  | succ count' ih =>
    intro curIdx acc hle
    have hwin : s.view.offset + s.view.len ≤ s.view.backingLen := by
      simpa [checkSliceViewValid, LeanNative.Spec.isValidByteSlice] using of_decide_eq_true hvalid
    have hbound : curIdx < s.view.len := by omega
    have hpos : s.view.offset + curIdx < buf.data.size := by omega
    let stepEnv := (env.bind idxVar (.u64 curIdx.toUInt64)).bind accVar (.u64 acc)
    have harrS : stepEnv s.arrVar = some (.sarrayId bufId) := by
      simp [stepEnv, beq_false_of_ne hne3, beq_false_of_ne hne4, harr]
    have hidxS : stepEnv idxVar = some (.u64 curIdx.toUInt64) := by
      simp [stepEnv, beq_false_of_ne hne1]
    have haccS : stepEnv accVar = some (.u64 acc) := VarEnv.bind_self _ _ _
    have hstep := sliceFoldStep_sound fuel stepEnv st s idxVar accVar posTmp elemTmp nextAcc
      curIdx acc bufId buf harrS hidxS haccS hne2 hne5 hne6 hvalid hbound hfind hsize hu64
    rw [evalSeqLoop, hstep]
    have hget : buf.data[s.view.offset + curIdx]?.getD 0 = buf.data[s.view.offset + curIdx] := by
      simp [hpos]
    rw [hget]
    dsimp only
    rw [ih (curIdx + 1) (acc + maskElemVal s.kind.lnirType buf.data[s.view.offset + curIdx]) (by omega)]
    have hshift : s.view.offset + (curIdx + 1) = s.view.offset + curIdx + 1 := by omega
    simp [sumSliceFrom, hpos, hshift]

/-- Zero-copy fold (`lowerSliceFold_sound`): folding `s` from `initVal` yields the pure
    left-to-right sum of the view and allocates nothing (`st` is unchanged). -/
theorem lowerSliceFold_sound (fuel : Nat) (env : VarEnv) (st : HeapState)
    (s : TypedSliceView) (initVal : UInt64)
    (loVar hiVar initVar idxVar accVar posTmp elemTmp nextAcc : VarId)
    (bufId : Nat) (buf : ArrayBuffer)
    (harr : env s.arrVar = some (.sarrayId bufId))
    (hfind : st.findBuffer bufId = some buf) (hsize : s.view.backingLen ≤ buf.data.size)
    (hu64 : buf.data.size < UInt64.size) (hvalid : checkSliceViewValid s = true)
    (hneA : s.arrVar ≠ loVar) (hneB : s.arrVar ≠ hiVar) (hneC : s.arrVar ≠ initVar)
    (hneD : loVar ≠ hiVar) (hneE : loVar ≠ initVar) (hneF : hiVar ≠ initVar)
    (hne1 : idxVar ≠ accVar) (hne2 : s.arrVar ≠ posTmp) (hne3 : s.arrVar ≠ accVar)
    (hne4 : s.arrVar ≠ idxVar) (hne5 : accVar ≠ elemTmp) (hne6 : accVar ≠ posTmp) :
    evalCode fuel env st (lowerSliceFold s initVal loVar hiVar initVar idxVar accVar posTmp elemTmp
        nextAcc (.ret accVar)) =
      .ok (.u64 (sumSliceFrom s.kind.lnirType buf.data s.view.offset initVal s.view.len), st) := by
  have hwin : s.view.offset + s.view.len ≤ s.view.backingLen := by
    simpa [checkSliceViewValid, LeanNative.Spec.isValidByteSlice] using of_decide_eq_true hvalid
  have hlen : s.view.len.toUInt64.toNat = s.view.len := by
    have hlen_le : s.view.len ≤ buf.data.size := by omega
    simp only [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hlen_le hu64)]
  unfold lowerSliceFold
  rw [evalCode]
  dsimp only [evalExpr, evalScalarExpr]
  rw [evalCode]
  dsimp only [evalExpr, evalScalarExpr]
  rw [evalCode]
  dsimp only [evalExpr, evalScalarExpr]
  let env3 := ((env.bind loVar (.u64 0)).bind hiVar (.u64 s.view.len.toUInt64)).bind initVar (.u64 initVal)
  change evalCode fuel env3 st
      (.seqFor idxVar loVar hiVar accVar initVar .i64
        (sliceFoldStep s idxVar accVar posTmp elemTmp nextAcc) (.ret accVar)) =
    .ok (.u64 (sumSliceFrom s.kind.lnirType buf.data s.view.offset initVal s.view.len), st)
  have hlo : env3 loVar = some (.u64 0) := by
    simp [env3, beq_false_of_ne hneD, beq_false_of_ne hneE]
  have hhi : env3 hiVar = some (.u64 s.view.len.toUInt64) := by
    simp [env3, beq_false_of_ne hneF]
  have hinit : env3 initVar = some (.u64 initVal) := VarEnv.bind_self _ _ _
  have harr3 : env3 s.arrVar = some (.sarrayId bufId) := by
    simp [env3, beq_false_of_ne hneA, beq_false_of_ne hneB, beq_false_of_ne hneC, harr]
  rw [evalCode]
  simp only [hlo, hhi, hinit, UInt64.toNat_zero, hlen, Nat.sub_zero]
  have hloop := sliceFoldLoop_sound fuel env3 st s idxVar accVar posTmp elemTmp nextAcc
    bufId buf harr3 hne1 hne2 hne3 hne4 hne5 hne6 hvalid hfind hsize hu64 s.view.len 0 initVal
    (by omega)
  simp only [Nat.add_zero] at hloop
  rw [hloop]
  dsimp only
  rw [evalCode]
  simp only [VarEnv.bind_self]

end LeanNative.Proofs
