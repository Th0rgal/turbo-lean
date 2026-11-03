import LeanNative.Backend.StableHLOLower
import LeanNative.Semantics.Eval
import LeanNative.Proofs.TargetBitVecProofs
import LeanNative.Proofs.LLVMScalarHelpersProofs

/-!
# StableHLO Scalar Helper Soundness (`LeanNative.Proofs.StableHLOScalarProofs`)

Mechanized semantics-preservation lemmas for 0-D `tensor<ui64>` scalar operations,
guarded division/remainder (`emitHLODivRem`), masked logical/arithmetic shifts
(`emitHLOShiftLogical`, `emitHLOSar`), and unsigned comparisons (`emitHLOCmp`).
-/

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend.TargetIR
open LeanNative.Backend.StableHLOAst
open LeanNative.Backend.StableHLOLower

/-! ## SSA Register Freshness & `Env` Lookup Lemmas -/

theorem hloTmpReg_injective {a b : Nat} (h : hloTmpReg a = hloTmpReg b) : a = b := by
  unfold hloTmpReg at h
  have h1 := congrArg String.toList h
  simp only [String.toList_append] at h1
  have h2 : ("t".toList ++ (ppInt a).toList).drop 1 = ("t".toList ++ (ppInt b).toList).drop 1 :=
    congrArg (List.drop 1) h1
  have ht : "t".toList = ['t'] := rfl
  rw [ht] at h2
  simp only [List.cons_append, List.drop_succ_cons, List.drop_zero] at h2
  exact ppInt_injective a b (String.ext_iff.mpr h2)

theorem hloTmpReg_ne_of_ne {a b : Nat} (h : a ≠ b) : hloTmpReg a ≠ hloTmpReg b :=
  fun heq => h (hloTmpReg_injective heq)

theorem hloVarReg_ne_hloTmpReg (v : VarId) (k : Nat) : hloVarReg v ≠ hloTmpReg k := by
  intro h
  unfold hloVarReg hloTmpReg at h
  have h1 := congrArg (fun s => s.toList.head?) h
  have hv : ("v" ++ ppInt v).toList.head? = some 'v' := by simp [String.toList_append]
  have ht : ("t" ++ ppInt k).toList.head? = some 't' := by simp [String.toList_append]
  rw [hv, ht] at h1
  cases h1

theorem env_bind_self (tenv : Env) (r : String) (v : TensorVal) :
    (tenv.bind r v) r = some v := by
  simp [Env.bind]

theorem env_bind_ne (tenv : Env) (r q : String) (v : TensorVal) (hne : q ≠ r) :
    (tenv.bind r v) q = tenv q := by
  have hb : (q == r) = false := beq_eq_false_iff_ne.mpr hne
  simp [Env.bind, hb]

theorem checkWellFormed_mkScUi64 (w : BitVec 64) :
    checkWellFormed (mkScUi64 w) = .ok () := rfl

theorem lookup_mkScUi64 (tenv : Env) (r : String) (w : BitVec 64)
    (h : tenv r = some (mkScUi64 w)) :
    lookup tenv r = .ok (mkScUi64 w) := by
  simp [lookup, h, checkWellFormed_mkScUi64, Bind.bind, Except.bind]

theorem lookup_scI64 (tenv : Env) (r : String) (w : BitVec 64)
    (h : tenv r = some { ty := scI64Ty, data := #[w] }) :
    lookup tenv r = .ok { ty := scI64Ty, data := #[w] } := by
  simp [lookup, h, checkWellFormed, TensorType.numElements, scI64Ty, Bind.bind, Except.bind]

theorem lookup_scI1 (tenv : Env) (r : String) (w : BitVec 64)
    (h : tenv r = some { ty := scI1Ty, data := #[w] }) :
    lookup tenv r = .ok { ty := scI1Ty, data := #[w] } := by
  simp [lookup, h, checkWellFormed, TensorType.numElements, scI1Ty, Bind.bind, Except.bind]

/-! ## `evalOps` Composition Lemmas -/

theorem evalOps_cons_nonReturn (tenv : Env) (op : StableHLOOp) (rest : List StableHLOOp)
    (hNonRet : isNonReturnOp op = true) :
    evalOps tenv (op :: rest) = (do let tenv' ← evalOp tenv op; evalOps tenv' rest) := by
  cases op <;> simp [isNonReturnOp] at hNonRet
  all_goals
    cases rest <;> rfl

theorem evalOps_append_nonReturn (ops1 ops2 : List StableHLOOp) (tenv tenv1 : Env)
    (hAll : ops1.all isNonReturnOp = true)
    (h1 : evalOps tenv ops1 = .ok tenv1) :
    evalOps tenv (ops1 ++ ops2) = evalOps tenv1 ops2 := by
  induction ops1 generalizing tenv with
  | nil =>
    simp [evalOps] at h1
    subst h1
    rfl
  | cons op rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hAll
    rw [evalOps_cons_nonReturn tenv op rest hAll.1] at h1
    simp only [List.cons_append]
    rw [evalOps_cons_nonReturn tenv op (rest ++ ops2) hAll.1]
    cases hOp : evalOp tenv op with
    | error e =>
      rw [hOp] at h1
      cases h1
    | ok tenvMid =>
      rw [hOp] at h1
      exact ih tenvMid hAll.2 h1

/-! ## 0-D Scalar `evalOp` Lemmas -/

theorem evalOp_constant_sc (tenv : Env) (d : String) (w : BitVec 64) :
    evalOp tenv (.constant d (mkScUi64 w)) = .ok (tenv.bind d (mkScUi64 w)) := rfl

theorem evalOp_add_sc (tenv : Env) (d a b : String) (wa wb : BitVec 64)
    (ha : tenv a = some (mkScUi64 wa)) (hb : tenv b = some (mkScUi64 wb)) :
    evalOp tenv (.add d a b) = .ok (tenv.bind d (mkScUi64 (wa + wb))) := by
  simp [evalOp, evalAdd, lookup_mkScUi64 _ _ _ ha, lookup_mkScUi64 _ _ _ hb,
    mkScUi64, scUi64Ty, isFloat, intBitWidth?, zipWithTotal, addAt, maskWidth,
    Bind.bind, Except.bind]

theorem evalOp_sub_sc (tenv : Env) (d a b : String) (wa wb : BitVec 64)
    (ha : tenv a = some (mkScUi64 wa)) (hb : tenv b = some (mkScUi64 wb)) :
    evalOp tenv (.subtract d a b) = .ok (tenv.bind d (mkScUi64 (wa - wb))) := by
  simp [evalOp, evalSub, binSame, lookup_mkScUi64 _ _ _ ha, lookup_mkScUi64 _ _ _ hb,
    mkScUi64, scUi64Ty, zipWithM, zipWithListM, elemBin, isFloat, intBitWidth?, maskWidth,
    Bind.bind, Except.bind]

theorem evalOp_mul_sc (tenv : Env) (d a b : String) (wa wb : BitVec 64)
    (ha : tenv a = some (mkScUi64 wa)) (hb : tenv b = some (mkScUi64 wb)) :
    evalOp tenv (.multiply d a b) = .ok (tenv.bind d (mkScUi64 (wa * wb))) := by
  simp [evalOp, evalMul, binSame, lookup_mkScUi64 _ _ _ ha, lookup_mkScUi64 _ _ _ hb,
    mkScUi64, scUi64Ty, zipWithM, zipWithListM, elemBin, isFloat, intBitWidth?, maskWidth,
    Bind.bind, Except.bind]

theorem evalOp_and_sc (tenv : Env) (d a b : String) (wa wb : BitVec 64)
    (ha : tenv a = some (mkScUi64 wa)) (hb : tenv b = some (mkScUi64 wb)) :
    evalOp tenv (.and d a b) = .ok (tenv.bind d (mkScUi64 (wa &&& wb))) := by
  simp [evalOp, evalAnd, binSame, lookup_mkScUi64 _ _ _ ha, lookup_mkScUi64 _ _ _ hb,
    mkScUi64, scUi64Ty, zipWithM, zipWithListM, elemBin, isFloat, intBitWidth?, maskWidth,
    Bind.bind, Except.bind]

theorem evalOp_or_sc (tenv : Env) (d a b : String) (wa wb : BitVec 64)
    (ha : tenv a = some (mkScUi64 wa)) (hb : tenv b = some (mkScUi64 wb)) :
    evalOp tenv (.or d a b) = .ok (tenv.bind d (mkScUi64 (wa ||| wb))) := by
  simp [evalOp, evalOr, binSame, lookup_mkScUi64 _ _ _ ha, lookup_mkScUi64 _ _ _ hb,
    mkScUi64, scUi64Ty, zipWithM, zipWithListM, elemBin, isFloat, intBitWidth?, maskWidth,
    Bind.bind, Except.bind]

theorem evalOp_xor_sc (tenv : Env) (d a b : String) (wa wb : BitVec 64)
    (ha : tenv a = some (mkScUi64 wa)) (hb : tenv b = some (mkScUi64 wb)) :
    evalOp tenv (.xor d a b) = .ok (tenv.bind d (mkScUi64 (wa ^^^ wb))) := by
  simp [evalOp, evalXor, binSame, lookup_mkScUi64 _ _ _ ha, lookup_mkScUi64 _ _ _ hb,
    mkScUi64, scUi64Ty, zipWithM, zipWithListM, elemBin, isFloat, intBitWidth?, maskWidth,
    Bind.bind, Except.bind]

theorem evalOp_div_sc (tenv : Env) (d a b : String) (wa wb : BitVec 64)
    (ha : tenv a = some (mkScUi64 wa)) (hb : tenv b = some (mkScUi64 wb))
    (hnz : wb ≠ 0#64) :
    evalOp tenv (.divide d a b) = .ok (tenv.bind d (mkScUi64 (wa.udiv wb))) := by
  simp [evalOp, evalDiv, binSame, lookup_mkScUi64 _ _ _ ha, lookup_mkScUi64 _ _ _ hb,
    mkScUi64, scUi64Ty, zipWithM, zipWithListM, isFloat, intBitWidth?, isSigned,
    maskWidth, hnz, Bind.bind, Except.bind]

theorem evalOp_rem_sc (tenv : Env) (d a b : String) (wa wb : BitVec 64)
    (ha : tenv a = some (mkScUi64 wa)) (hb : tenv b = some (mkScUi64 wb))
    (hnz : wb ≠ 0#64) :
    evalOp tenv (.remainder d a b) = .ok (tenv.bind d (mkScUi64 (wa % wb))) := by
  simp [evalOp, evalRem, binSame, lookup_mkScUi64 _ _ _ ha, lookup_mkScUi64 _ _ _ hb,
    mkScUi64, scUi64Ty, zipWithM, zipWithListM, isFloat, intBitWidth?, isSigned,
    maskWidth, hnz, Bind.bind, Except.bind]

theorem evalOp_shl_sc (tenv : Env) (d a b : String) (wa wb : BitVec 64)
    (ha : tenv a = some (mkScUi64 wa)) (hb : tenv b = some (mkScUi64 wb))
    (hlt : wb.toNat < 64) :
    evalOp tenv (.shiftLeft d a b) = .ok (tenv.bind d (mkScUi64 (wa <<< wb.toNat))) := by
  have hge : ¬(64 ≤ wb.toNat) := by omega
  simp [evalOp, evalShl, binSame, lookup_mkScUi64 _ _ _ ha, lookup_mkScUi64 _ _ _ hb,
    mkScUi64, scUi64Ty, zipWithM, zipWithListM, isFloat, intBitWidth?, maskWidth, hge,
    Bind.bind, Except.bind]

theorem evalOp_shr_sc (tenv : Env) (d a b : String) (wa wb : BitVec 64)
    (ha : tenv a = some (mkScUi64 wa)) (hb : tenv b = some (mkScUi64 wb))
    (hlt : wb.toNat < 64) :
    evalOp tenv (.shiftRightLogical d a b) = .ok (tenv.bind d (mkScUi64 (wa >>> wb.toNat))) := by
  have hge : ¬(64 ≤ wb.toNat) := by omega
  simp [evalOp, evalShrL, binSame, lookup_mkScUi64 _ _ _ ha, lookup_mkScUi64 _ _ _ hb,
    mkScUi64, scUi64Ty, zipWithM, zipWithListM, isFloat, intBitWidth?, maskWidth, hge,
    Bind.bind, Except.bind]

theorem ashrWidth_64_eq_sshiftRight (x amt : BitVec 64) (h : amt.toNat < 64) :
    ashrWidth 64 true x amt = x.sshiftRight amt.toNat := by
  let s := amt.toNat
  have hs_def : s = amt.toNat := rfl
  have hge : ¬(amt.toNat ≥ 64) := by omega
  unfold ashrWidth maskWidth
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, show (64 == 0) = false from rfl,
    Nat.le_refl, hge]
  rw [← hs_def]
  have hsb : ((x >>> 63) &&& 1#64 == 0#64) = !x.msb := by
    have h1 := bv64_signBit_eq_msb x
    have h2 : (x >>> 63) = (x >>> 63#64) := rfl
    rw [h2, ← h1]
    unfold bne
    simp
  rw [hsb]
  cases hmsb : x.msb
  · simp only [Bool.not_false, Bool.true_or, ↓reduceIte]
    ext i hi
    rw [BitVec.getElem_ushiftRight, BitVec.getElem_sshiftRight, hmsb]
    by_cases hsi : s + i < 64
    · simp [hsi, BitVec.getLsbD_eq_getElem]
    · simp [hsi, BitVec.getLsbD_of_ge x (s + i) (by omega)]
  · cases Nat.eq_zero_or_pos s with
    | inl hsz =>
      simp only [hsz, beq_self_eq_true, Bool.or_true, ↓reduceIte]
      ext i hi
      rw [BitVec.getElem_ushiftRight, BitVec.getElem_sshiftRight, hmsb]
      simp [hi, BitVec.getLsbD_eq_getElem]
    | inr hsp =>
      have hsne : (s == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
      simp only [Bool.not_true, hsne, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
      ext i hi
      rw [BitVec.getElem_or, BitVec.getElem_ushiftRight, BitVec.getElem_shiftLeft,
        BitVec.getElem_sshiftRight, hmsb]
      by_cases hsi : s + i < 64
      · have hlt : i < 64 - s := by omega
        simp [hsi, hlt, BitVec.getLsbD_eq_getElem]
      · have hge_sub : ¬(i < 64 - s) := by omega
        simp only [hsi, ↓reduceDIte, hge_sub]
        rw [BitVec.getElem_allOnes]
        simp

theorem evalOp_convert_ui64_i64_sc (tenv : Env) (d s : String) (w : BitVec 64)
    (hs : tenv s = some (mkScUi64 w)) :
    evalOp tenv (.convert d s .i64) = .ok (tenv.bind d { ty := scI64Ty, data := #[w] }) := by
  have he : (ElemType.i64 == ElemType.i1) = false := rfl
  simp [evalOp, evalConvert, lookup_mkScUi64 _ _ _ hs, mkScUi64, scUi64Ty, scI64Ty,
    isFloat, intBitWidth?, isSigned, maskWidth, he, Bind.bind, Except.bind]

theorem evalOp_convert_i64_ui64_sc (tenv : Env) (d s : String) (w : BitVec 64)
    (hs : tenv s = some { ty := scI64Ty, data := #[w] }) :
    evalOp tenv (.convert d s .ui64) = .ok (tenv.bind d (mkScUi64 w)) := by
  have he : (ElemType.ui64 == ElemType.i1) = false := rfl
  simp [evalOp, evalConvert, lookup_scI64 _ _ _ hs, mkScUi64, scUi64Ty, scI64Ty,
    isFloat, intBitWidth?, isSigned, maskWidth, he, Bind.bind, Except.bind]

theorem evalOp_convert_ui64_i1_sc (tenv : Env) (d s : String) (w : BitVec 64)
    (hs : tenv s = some (mkScUi64 w)) :
    evalOp tenv (.convert d s .i1) =
      .ok (tenv.bind d { ty := scI1Ty, data := #[if w == 0#64 then 0#64 else 1#64] }) := by
  have he : (ElemType.i1 == ElemType.i1) = true := rfl
  simp [evalOp, evalConvert, lookup_mkScUi64 _ _ _ hs, mkScUi64, scUi64Ty, scI1Ty,
    isFloat, intBitWidth?, maskWidth, he, Bind.bind, Except.bind]

theorem evalOp_convert_i1_ui64_sc (tenv : Env) (d s : String) (b : Bool)
    (hs : tenv s = some { ty := scI1Ty, data := #[if b then 1#64 else 0#64] }) :
    evalOp tenv (.convert d s .ui64) =
      .ok (tenv.bind d (mkScUi64 (if b then 1#64 else 0#64))) := by
  have he : (ElemType.ui64 == ElemType.i1) = false := rfl
  cases b <;>
    simp [evalOp, evalConvert, lookup_scI1 _ _ _ hs, mkScUi64, scUi64Ty, scI1Ty,
      isFloat, intBitWidth?, isSigned, maskWidth, he, Bind.bind, Except.bind]

theorem evalOp_sar_i64_sc (tenv : Env) (d a b : String) (wa wb : BitVec 64)
    (ha : tenv a = some { ty := scI64Ty, data := #[wa] })
    (hb : tenv b = some { ty := scI64Ty, data := #[wb] })
    (hlt : wb.toNat < 64) :
    evalOp tenv (.shiftRightArithmetic d a b) =
      .ok (tenv.bind d { ty := scI64Ty, data := #[wa.sshiftRight wb.toNat] }) := by
  simp [evalOp, evalShrA, binSame, lookup_scI64 _ _ _ ha, lookup_scI64 _ _ _ hb,
    scI64Ty, zipWithM, zipWithListM, isFloat, intBitWidth?, isSigned, maskWidth,
    ashrWidth_64_eq_sshiftRight wa wb hlt, Bind.bind, Except.bind]

/-- Expected boolean outcome of unsigned 64-bit `CompareDir` on `wa`, `wb`. -/
def cmpDirBool (dir : CompareDir) (wa wb : BitVec 64) : Bool :=
  match dir with
  | .eq => wa == wb
  | .ne => wa != wb
  | .lt => decide (wa.toNat < wb.toNat)
  | .le => decide (wa.toNat < wb.toNat) || (wa == wb)
  | .gt => decide (wb.toNat < wa.toNat)
  | .ge => decide (wb.toNat < wa.toNat) || (wa == wb)

theorem cmpDirBool_lt_eq_ult (a b : UInt64) :
    cmpDirBool .lt a.toBitVec b.toBitVec = decide (a < b) := rfl

theorem cmpDirBool_le_eq_ule (a b : UInt64) :
    cmpDirBool .le a.toBitVec b.toBitVec = decide (a ≤ b) := by
  change (decide (a.toNat < b.toNat) || (a.toBitVec == b.toBitVec)) = decide (a.toNat ≤ b.toNat)
  by_cases hlt : a.toNat < b.toNat
  · have hle : a.toNat ≤ b.toNat := Nat.le_of_lt hlt
    simp [hlt, hle]
  · by_cases heq : a.toBitVec = b.toBitVec
    · have hnat : a.toNat = b.toNat := congrArg BitVec.toNat heq
      simp [heq, hnat]
    · have hne : (a.toBitVec == b.toBitVec) = false := beq_eq_false_iff_ne.mpr heq
      have hnotle : ¬(a.toNat ≤ b.toNat) := by
        intro hle
        rcases Nat.lt_or_eq_of_le hle with h1 | h2
        · exact hlt h1
        · exact heq (BitVec.eq_of_toNat_eq h2)
      simp [hlt, hne, hnotle]

theorem evalOp_compare_sc (tenv : Env) (d a b : String) (dir : CompareDir) (wa wb : BitVec 64)
    (ha : tenv a = some (mkScUi64 wa)) (hb : tenv b = some (mkScUi64 wb)) :
    evalOp tenv (.compare d a b dir) =
      .ok (tenv.bind d { ty := scI1Ty, data := #[if cmpDirBool dir wa wb then 1#64 else 0#64] }) := by
  have hty : (({ shape := [], elem := ElemType.ui64 } : TensorType) !=
      { shape := [], elem := ElemType.ui64 }) = false := rfl
  cases dir <;>
    simp [evalOp, evalCompare, lookup_mkScUi64 _ _ _ ha, lookup_mkScUi64 _ _ _ hb,
      mkScUi64, scI1Ty, scUi64Ty, hty, isFloat, zipWithM, zipWithListM,
      intBitWidth?, isSigned, unsignedLt, maskWidth, cmpDirBool, Bind.bind, Except.bind]

theorem evalOp_select_sc (tenv : Env) (d p t e : String) (cond : Bool) (wt we : BitVec 64)
    (hp : tenv p = some { ty := scI1Ty, data := #[if cond then 1#64 else 0#64] })
    (ht : tenv t = some (mkScUi64 wt)) (he : tenv e = some (mkScUi64 we)) :
    evalOp tenv (.select d p t e) =
      .ok (tenv.bind d (mkScUi64 (if cond then wt else we))) := by
  have hty : (({ shape := [], elem := ElemType.ui64 } : TensorType) !=
      { shape := [], elem := ElemType.ui64 }) = false := rfl
  have hi1 : (ElemType.i1 != ElemType.i1) = false := rfl
  cases cond <;>
    simp [evalOp, evalSelect, lookup_scI1 _ _ _ hp, lookup_mkScUi64 _ _ _ ht,
      lookup_mkScUi64 _ _ _ he, mkScUi64, hty, hi1, scUi64Ty, scI1Ty, selectData,
      Bind.bind, Except.bind]

/-! ## Freshness & Multi-Op Sequence Correctness (`emitHLO*`) -/

/-- All temporary registers `hloTmpReg j` for `j ≥ k` are unbound in `tenv`. -/
def HLORegFresh (tenv : Env) (k : Nat) : Prop :=
  ∀ j, k ≤ j → tenv (hloTmpReg j) = none

theorem hloRegFresh_mono {tenv : Env} {k1 k2 : Nat} (h : HLORegFresh tenv k1) (hle : k1 ≤ k2) :
    HLORegFresh tenv k2 :=
  fun j hj => h j (Nat.le_trans hle hj)

theorem hloRegFresh_bind_lt {tenv : Env} {j k : Nat} (v : TensorVal)
    (h : HLORegFresh tenv j) (hlt : j < k) :
    HLORegFresh (tenv.bind (hloTmpReg j) v) k := by
  intro m hm
  rw [env_bind_ne _ _ _ _ (hloTmpReg_ne_of_ne (by omega))]
  exact h m (by omega)

theorem operand_ne_hloTmp_of_fresh {tenv : Env} {r : String} {tv : TensorVal} {k j : Nat}
    (h : tenv r = some tv) (hFr : HLORegFresh tenv k) (hj : k ≤ j) :
    r ≠ hloTmpReg j := by
  intro heq
  rw [heq, hFr j hj] at h
  cases h

theorem frame_hloTmp_range (e1 e2 e3 : Env) (k1 k2 k3 : Nat)
    (hle12 : k1 ≤ k2) (hle23 : k2 ≤ k3)
    (hf12 : ∀ q, (∀ j, k1 ≤ j → j < k2 → q ≠ hloTmpReg j) → e2 q = e1 q)
    (hf23 : ∀ q, (∀ j, k2 ≤ j → j < k3 → q ≠ hloTmpReg j) → e3 q = e2 q) :
    ∀ q, (∀ j, k1 ≤ j → j < k3 → q ≠ hloTmpReg j) → e3 q = e1 q := by
  intro q hq
  rw [hf23 q (fun j hlo hhi => hq j (Nat.le_trans hle12 hlo) hhi)]
  exact hf12 q (fun j hlo hhi => hq j hlo (Nat.lt_of_lt_of_le hhi hle23))

theorem emitHLODivRem_correct (tenv : Env) (k : Nat) (isRem : Bool) (ra rb : String)
    (na nb : UInt64)
    (ha : tenv ra = some (mkScUi64 na.toBitVec))
    (hb : tenv rb = some (mkScUi64 nb.toBitVec))
    (hFr : HLORegFresh tenv k) :
    let (res, k', ops) := emitHLODivRem k isRem ra rb
    k' = k + 6 ∧
    ops.all isNonReturnOp = true ∧
    ∃ tenv',
      evalOps tenv ops = .ok tenv' ∧
      tenv' res = some (mkScUi64 (if isRem then (na % nb).toBitVec else (na / nb).toBitVec)) ∧
      HLORegFresh tenv' k' ∧
      (∀ q, (∀ j, k ≤ j → j < k' → q ≠ hloTmpReg j) → tenv' q = tenv q) := by
  dsimp only [emitHLODivRem]
  refine ⟨rfl, by cases isRem <;> rfl, ?_⟩
  have ha0 := operand_ne_hloTmp_of_fresh ha hFr (j := k) (by omega)
  have ha1 := operand_ne_hloTmp_of_fresh ha hFr (j := k + 1) (by omega)
  have ha2 := operand_ne_hloTmp_of_fresh ha hFr (j := k + 2) (by omega)
  have ha3 := operand_ne_hloTmp_of_fresh ha hFr (j := k + 3) (by omega)
  have ha4 := operand_ne_hloTmp_of_fresh ha hFr (j := k + 4) (by omega)
  have hb0 := operand_ne_hloTmp_of_fresh hb hFr (j := k) (by omega)
  have hb1 := operand_ne_hloTmp_of_fresh hb hFr (j := k + 1) (by omega)
  have hb2 := operand_ne_hloTmp_of_fresh hb hFr (j := k + 2) (by omega)
  let e1 := tenv.bind (hloTmpReg k) (mkScUi64 0#64)
  let e2 := e1.bind (hloTmpReg (k + 1)) (mkScUi64 1#64)
  let isZ : Bool := nb.toBitVec == 0#64
  let tZ : TensorVal := { ty := scI1Ty, data := #[if isZ then 1#64 else 0#64] }
  let e3 := e2.bind (hloTmpReg (k + 2)) tZ
  let wSafe : BitVec 64 := if isZ then 1#64 else nb.toBitVec
  let e4 := e3.bind (hloTmpReg (k + 3)) (mkScUi64 wSafe)
  have hSafeNz : wSafe ≠ 0#64 := by
    by_cases hz : nb.toBitVec = 0#64
    · simp [wSafe, isZ, hz]
    · have hbf : isZ = false := beq_eq_false_iff_ne.mpr hz
      simp [wSafe, hbf, hz]
  let wRaw : BitVec 64 := if isRem then na.toBitVec % wSafe else na.toBitVec.udiv wSafe
  let e5 := e4.bind (hloTmpReg (k + 4)) (mkScUi64 wRaw)
  let wOut : BitVec 64 := if isZ then (if isRem then na.toBitVec else 0#64) else wRaw
  let e6 := e5.bind (hloTmpReg (k + 5)) (mkScUi64 wOut)
  refine ⟨e6, ?_, ?_, ?_, ?_⟩
  · have hs1 : evalOp tenv (.constant (hloTmpReg k) (mkScUi64 0#64)) = .ok e1 := rfl
    have hs2 : evalOp e1 (.constant (hloTmpReg (k + 1)) (mkScUi64 1#64)) = .ok e2 := rfl
    have he2_b : e2 rb = some (mkScUi64 nb.toBitVec) := by
      dsimp only [e2, e1]
      rw [env_bind_ne _ _ _ _ hb1, env_bind_ne _ _ _ _ hb0, hb]
    have he2_c0 : e2 (hloTmpReg k) = some (mkScUi64 0#64) := by
      dsimp only [e2, e1]
      rw [env_bind_ne _ _ _ _ (hloTmpReg_ne_of_ne (by omega)), env_bind_self]
    have hs3 : evalOp e2 (.compare (hloTmpReg (k + 2)) rb (hloTmpReg k) .eq) = .ok e3 :=
      evalOp_compare_sc e2 _ rb _ .eq nb.toBitVec 0#64 he2_b he2_c0
    have he3_z : e3 (hloTmpReg (k + 2)) = some tZ := env_bind_self _ _ _
    have he3_c1 : e3 (hloTmpReg (k + 1)) = some (mkScUi64 1#64) := by
      dsimp only [e3, e2]
      rw [env_bind_ne _ _ _ _ (hloTmpReg_ne_of_ne (by omega)), env_bind_self]
    have he3_b : e3 rb = some (mkScUi64 nb.toBitVec) := by
      dsimp only [e3]
      rw [env_bind_ne _ _ _ _ hb2, he2_b]
    have hs4 : evalOp e3 (.select (hloTmpReg (k + 3)) (hloTmpReg (k + 2))
        (hloTmpReg (k + 1)) rb) = .ok e4 :=
      evalOp_select_sc e3 _ _ _ rb isZ 1#64 nb.toBitVec he3_z he3_c1 he3_b
    have he4_a : e4 ra = some (mkScUi64 na.toBitVec) := by
      dsimp only [e4, e3, e2, e1]
      rw [env_bind_ne _ _ _ _ ha3, env_bind_ne _ _ _ _ ha2,
          env_bind_ne _ _ _ _ ha1, env_bind_ne _ _ _ _ ha0, ha]
    have he4_s : e4 (hloTmpReg (k + 3)) = some (mkScUi64 wSafe) := env_bind_self _ _ _
    have hs5 : evalOp e4 (if isRem then .remainder (hloTmpReg (k + 4)) ra (hloTmpReg (k + 3))
        else .divide (hloTmpReg (k + 4)) ra (hloTmpReg (k + 3))) = .ok e5 := by
      cases isRem
      · exact evalOp_div_sc e4 _ ra _ na.toBitVec wSafe he4_a he4_s hSafeNz
      · exact evalOp_rem_sc e4 _ ra _ na.toBitVec wSafe he4_a he4_s hSafeNz
    have he5_z : e5 (hloTmpReg (k + 2)) = some tZ := by
      dsimp only [e5, e4]
      rw [env_bind_ne _ _ _ _ (hloTmpReg_ne_of_ne (by omega)),
          env_bind_ne _ _ _ _ (hloTmpReg_ne_of_ne (by omega)), he3_z]
    have he5_fb : e5 (if isRem then ra else hloTmpReg k) =
        some (mkScUi64 (if isRem then na.toBitVec else 0#64)) := by
      cases isRem
      · dsimp only [e5, e4, e3]
        change ((e2.bind (hloTmpReg (k + 2)) tZ).bind (hloTmpReg (k + 3)) (mkScUi64 wSafe)).bind
            (hloTmpReg (k + 4)) (mkScUi64 wRaw) (hloTmpReg k) = some (mkScUi64 0#64)
        rw [env_bind_ne _ _ _ _ (hloTmpReg_ne_of_ne (by omega)),
            env_bind_ne _ _ _ _ (hloTmpReg_ne_of_ne (by omega)),
            env_bind_ne _ _ _ _ (hloTmpReg_ne_of_ne (by omega)), he2_c0]
      · dsimp only [e5]
        change (e4.bind (hloTmpReg (k + 4)) (mkScUi64 wRaw)) ra = some (mkScUi64 na.toBitVec)
        rw [env_bind_ne _ _ _ _ ha4, he4_a]
    have he5_raw : e5 (hloTmpReg (k + 4)) = some (mkScUi64 wRaw) := env_bind_self _ _ _
    have hs6 : evalOp e5 (.select (hloTmpReg (k + 5)) (hloTmpReg (k + 2))
        (if isRem then ra else hloTmpReg k) (hloTmpReg (k + 4))) = .ok e6 :=
      evalOp_select_sc e5 _ _ _ _ isZ _ wRaw he5_z he5_fb he5_raw
    rw [evalOps_cons_nonReturn _ _ _ rfl, hs1]
    change evalOps e1 _ = .ok e6
    rw [evalOps_cons_nonReturn _ _ _ rfl, hs2]
    change evalOps e2 _ = .ok e6
    rw [evalOps_cons_nonReturn _ _ _ rfl, hs3]
    change evalOps e3 _ = .ok e6
    rw [evalOps_cons_nonReturn _ _ _ rfl, hs4]
    change evalOps e4 _ = .ok e6
    have hDivNonRet : isNonReturnOp
        (if isRem then .remainder (hloTmpReg (k + 4)) ra (hloTmpReg (k + 3))
         else .divide (hloTmpReg (k + 4)) ra (hloTmpReg (k + 3))) = true := by
      cases isRem <;> rfl
    rw [evalOps_cons_nonReturn _ _ _ hDivNonRet, hs5]
    change evalOps e5 _ = .ok e6
    rw [evalOps_cons_nonReturn _ _ _ rfl, hs6]
    rfl
  · dsimp only [e6]
    rw [env_bind_self]
    congr 2
    cases isRem
    · simp only [Bool.false_eq_true, ↓reduceIte, wOut, wRaw, wSafe, isZ]
      exact u64_div_guarded_bv na nb
    · simp only [↓reduceIte, wOut, wRaw, wSafe, isZ]
      exact u64_mod_guarded_bv na nb
  · have hf1 := hloRegFresh_bind_lt (mkScUi64 0#64) hFr (k := k + 1) (by omega)
    have hf2 := hloRegFresh_bind_lt (mkScUi64 1#64) hf1 (k := k + 2) (by omega)
    have hf3 := hloRegFresh_bind_lt tZ hf2 (k := k + 3) (by omega)
    have hf4 := hloRegFresh_bind_lt (mkScUi64 wSafe) hf3 (k := k + 4) (by omega)
    have hf5 := hloRegFresh_bind_lt (mkScUi64 wRaw) hf4 (k := k + 5) (by omega)
    exact hloRegFresh_bind_lt (mkScUi64 wOut) hf5 (k := k + 6) (by omega)
  · intro q hq
    dsimp only [e6, e5, e4, e3, e2, e1]
    rw [env_bind_ne _ _ _ _ (hq (k + 5) (by omega) (by omega)),
        env_bind_ne _ _ _ _ (hq (k + 4) (by omega) (by omega)),
        env_bind_ne _ _ _ _ (hq (k + 3) (by omega) (by omega)),
        env_bind_ne _ _ _ _ (hq (k + 2) (by omega) (by omega)),
        env_bind_ne _ _ _ _ (hq (k + 1) (by omega) (by omega)),
        env_bind_ne _ _ _ _ (hq k (by omega) (by omega))]

theorem emitHLOShiftLogical_correct (tenv : Env) (k : Nat) (isRight : Bool) (ra rb : String)
    (na nb : UInt64)
    (ha : tenv ra = some (mkScUi64 na.toBitVec))
    (hb : tenv rb = some (mkScUi64 nb.toBitVec))
    (hFr : HLORegFresh tenv k) :
    let (res, k', ops) := emitHLOShiftLogical k isRight ra rb
    k' = k + 3 ∧
    ops.all isNonReturnOp = true ∧
    ∃ tenv',
      evalOps tenv ops = .ok tenv' ∧
      tenv' res = some (mkScUi64
        (if isRight then (na >>> nb).toBitVec else (na <<< nb).toBitVec)) ∧
      HLORegFresh tenv' k' ∧
      (∀ q, (∀ j, k ≤ j → j < k' → q ≠ hloTmpReg j) → tenv' q = tenv q) := by
  dsimp only [emitHLOShiftLogical]
  refine ⟨rfl, by cases isRight <;> rfl, ?_⟩
  have ha0 := operand_ne_hloTmp_of_fresh ha hFr (j := k) (by omega)
  have ha1 := operand_ne_hloTmp_of_fresh ha hFr (j := k + 1) (by omega)
  have hb0 := operand_ne_hloTmp_of_fresh hb hFr (j := k) (by omega)
  let e1 := tenv.bind (hloTmpReg k) (mkScUi64 63#64)
  let wAmt := nb.toBitVec &&& 63#64
  let e2 := e1.bind (hloTmpReg (k + 1)) (mkScUi64 wAmt)
  have hlt : wAmt.toNat < 64 := bv64_and_63_lt_64 nb.toBitVec
  let wOut := if isRight then na.toBitVec >>> wAmt.toNat else na.toBitVec <<< wAmt.toNat
  let e3 := e2.bind (hloTmpReg (k + 2)) (mkScUi64 wOut)
  refine ⟨e3, ?_, ?_, ?_, ?_⟩
  · have hs1 : evalOp tenv (.constant (hloTmpReg k) (mkScUi64 63#64)) = .ok e1 := rfl
    have he1_b : e1 rb = some (mkScUi64 nb.toBitVec) := by
      dsimp only [e1]
      rw [env_bind_ne _ _ _ _ hb0, hb]
    have hs2 : evalOp e1 (.and (hloTmpReg (k + 1)) rb (hloTmpReg k)) = .ok e2 :=
      evalOp_and_sc e1 _ rb _ nb.toBitVec 63#64 he1_b (env_bind_self _ _ _)
    have he2_a : e2 ra = some (mkScUi64 na.toBitVec) := by
      dsimp only [e2, e1]
      rw [env_bind_ne _ _ _ _ ha1, env_bind_ne _ _ _ _ ha0, ha]
    have he2_amt : e2 (hloTmpReg (k + 1)) = some (mkScUi64 wAmt) := env_bind_self _ _ _
    have hs3 : evalOp e2 (if isRight then .shiftRightLogical (hloTmpReg (k + 2)) ra (hloTmpReg (k + 1))
        else .shiftLeft (hloTmpReg (k + 2)) ra (hloTmpReg (k + 1))) = .ok e3 := by
      cases isRight
      · exact evalOp_shl_sc e2 _ ra _ na.toBitVec wAmt he2_a he2_amt hlt
      · exact evalOp_shr_sc e2 _ ra _ na.toBitVec wAmt he2_a he2_amt hlt
    have hShNonRet : isNonReturnOp
        (if isRight then .shiftRightLogical (hloTmpReg (k + 2)) ra (hloTmpReg (k + 1))
         else .shiftLeft (hloTmpReg (k + 2)) ra (hloTmpReg (k + 1))) = true := by
      cases isRight <;> rfl
    rw [evalOps_cons_nonReturn _ _ _ rfl, hs1]
    change evalOps e1 _ = .ok e3
    rw [evalOps_cons_nonReturn _ _ _ rfl, hs2]
    change evalOps e2 _ = .ok e3
    rw [evalOps_cons_nonReturn _ _ _ hShNonRet, hs3]
    rfl
  · dsimp only [e3]
    rw [env_bind_self]
    congr 2
    cases isRight
    · simp only [Bool.false_eq_true, ↓reduceIte, wOut, wAmt]
      rw [← BitVec.shiftLeft_eq', u64_shl_masked_bv]
    · simp only [↓reduceIte, wOut, wAmt]
      rw [← BitVec.ushiftRight_eq', u64_shr_masked_bv]
  · have hf1 := hloRegFresh_bind_lt (mkScUi64 63#64) hFr (k := k + 1) (by omega)
    have hf2 := hloRegFresh_bind_lt (mkScUi64 wAmt) hf1 (k := k + 2) (by omega)
    exact hloRegFresh_bind_lt (mkScUi64 wOut) hf2 (k := k + 3) (by omega)
  · intro q hq
    dsimp only [e3, e2, e1]
    rw [env_bind_ne _ _ _ _ (hq (k + 2) (by omega) (by omega)),
        env_bind_ne _ _ _ _ (hq (k + 1) (by omega) (by omega)),
        env_bind_ne _ _ _ _ (hq k (by omega) (by omega))]

theorem emitHLOSar_correct (tenv : Env) (k : Nat) (ra rb : String)
    (na nb : UInt64)
    (ha : tenv ra = some (mkScUi64 na.toBitVec))
    (hb : tenv rb = some (mkScUi64 nb.toBitVec))
    (hFr : HLORegFresh tenv k) :
    let (res, k', ops) := emitHLOSar k ra rb
    k' = k + 6 ∧
    ops.all isNonReturnOp = true ∧
    ∃ tenv',
      evalOps tenv ops = .ok tenv' ∧
      tenv' res = some (mkScUi64 (lnirSar64 na nb).toBitVec) ∧
      HLORegFresh tenv' k' ∧
      (∀ q, (∀ j, k ≤ j → j < k' → q ≠ hloTmpReg j) → tenv' q = tenv q) := by
  dsimp only [emitHLOSar]
  refine ⟨rfl, rfl, ?_⟩
  have ha0 := operand_ne_hloTmp_of_fresh ha hFr (j := k) (by omega)
  have ha1 := operand_ne_hloTmp_of_fresh ha hFr (j := k + 1) (by omega)
  have hb0 := operand_ne_hloTmp_of_fresh hb hFr (j := k) (by omega)
  let e1 := tenv.bind (hloTmpReg k) (mkScUi64 63#64)
  let wAmt := nb.toBitVec &&& 63#64
  let e2 := e1.bind (hloTmpReg (k + 1)) (mkScUi64 wAmt)
  let tLs : TensorVal := { ty := scI64Ty, data := #[na.toBitVec] }
  let e3 := e2.bind (hloTmpReg (k + 2)) tLs
  let tAs : TensorVal := { ty := scI64Ty, data := #[wAmt] }
  let e4 := e3.bind (hloTmpReg (k + 3)) tAs
  let wShift := na.toBitVec.sshiftRight wAmt.toNat
  let tRs : TensorVal := { ty := scI64Ty, data := #[wShift] }
  let e5 := e4.bind (hloTmpReg (k + 4)) tRs
  let e6 := e5.bind (hloTmpReg (k + 5)) (mkScUi64 wShift)
  have hlt : wAmt.toNat < 64 := bv64_and_63_lt_64 nb.toBitVec
  refine ⟨e6, ?_, ?_, ?_, ?_⟩
  · have hs1 : evalOp tenv (.constant (hloTmpReg k) (mkScUi64 63#64)) = .ok e1 := rfl
    have he1_b : e1 rb = some (mkScUi64 nb.toBitVec) := by
      dsimp only [e1]
      rw [env_bind_ne _ _ _ _ hb0, hb]
    have hs2 : evalOp e1 (.and (hloTmpReg (k + 1)) rb (hloTmpReg k)) = .ok e2 :=
      evalOp_and_sc e1 _ rb _ nb.toBitVec 63#64 he1_b (env_bind_self _ _ _)
    have he2_a : e2 ra = some (mkScUi64 na.toBitVec) := by
      dsimp only [e2, e1]
      rw [env_bind_ne _ _ _ _ ha1, env_bind_ne _ _ _ _ ha0, ha]
    have hs3 : evalOp e2 (.convert (hloTmpReg (k + 2)) ra .i64) = .ok e3 :=
      evalOp_convert_ui64_i64_sc e2 _ ra na.toBitVec he2_a
    have he3_amt : e3 (hloTmpReg (k + 1)) = some (mkScUi64 wAmt) := by
      dsimp only [e3, e2]
      rw [env_bind_ne _ _ _ _ (hloTmpReg_ne_of_ne (by omega)), env_bind_self]
    have hs4 : evalOp e3 (.convert (hloTmpReg (k + 3)) (hloTmpReg (k + 1)) .i64) = .ok e4 :=
      evalOp_convert_ui64_i64_sc e3 _ _ wAmt he3_amt
    have he4_ls : e4 (hloTmpReg (k + 2)) = some tLs := by
      dsimp only [e4, e3]
      rw [env_bind_ne _ _ _ _ (hloTmpReg_ne_of_ne (by omega)), env_bind_self]
    have hs5 : evalOp e4 (.shiftRightArithmetic (hloTmpReg (k + 4))
        (hloTmpReg (k + 2)) (hloTmpReg (k + 3))) = .ok e5 :=
      evalOp_sar_i64_sc e4 _ _ _ na.toBitVec wAmt he4_ls (env_bind_self _ _ _) hlt
    have hs6 : evalOp e5 (.convert (hloTmpReg (k + 5)) (hloTmpReg (k + 4)) .ui64) = .ok e6 :=
      evalOp_convert_i64_ui64_sc e5 _ _ wShift (env_bind_self _ _ _)
    rw [evalOps_cons_nonReturn _ _ _ rfl, hs1]
    change evalOps e1 _ = .ok e6
    rw [evalOps_cons_nonReturn _ _ _ rfl, hs2]
    change evalOps e2 _ = .ok e6
    rw [evalOps_cons_nonReturn _ _ _ rfl, hs3]
    change evalOps e3 _ = .ok e6
    rw [evalOps_cons_nonReturn _ _ _ rfl, hs4]
    change evalOps e4 _ = .ok e6
    rw [evalOps_cons_nonReturn _ _ _ rfl, hs5]
    change evalOps e5 _ = .ok e6
    rw [evalOps_cons_nonReturn _ _ _ rfl, hs6]
    rfl
  · dsimp only [e6]
    rw [env_bind_self]
    congr 2
    exact u64_ashr_masked_bv na nb
  · have hf1 := hloRegFresh_bind_lt (mkScUi64 63#64) hFr (k := k + 1) (by omega)
    have hf2 := hloRegFresh_bind_lt (mkScUi64 wAmt) hf1 (k := k + 2) (by omega)
    have hf3 := hloRegFresh_bind_lt tLs hf2 (k := k + 3) (by omega)
    have hf4 := hloRegFresh_bind_lt tAs hf3 (k := k + 4) (by omega)
    have hf5 := hloRegFresh_bind_lt tRs hf4 (k := k + 5) (by omega)
    exact hloRegFresh_bind_lt (mkScUi64 wShift) hf5 (k := k + 6) (by omega)
  · intro q hq
    dsimp only [e6, e5, e4, e3, e2, e1]
    rw [env_bind_ne _ _ _ _ (hq (k + 5) (by omega) (by omega)),
        env_bind_ne _ _ _ _ (hq (k + 4) (by omega) (by omega)),
        env_bind_ne _ _ _ _ (hq (k + 3) (by omega) (by omega)),
        env_bind_ne _ _ _ _ (hq (k + 2) (by omega) (by omega)),
        env_bind_ne _ _ _ _ (hq (k + 1) (by omega) (by omega)),
        env_bind_ne _ _ _ _ (hq k (by omega) (by omega))]

theorem emitHLOCmp_correct (tenv : Env) (k : Nat) (dir : CompareDir) (ra rb : String)
    (wa wb : BitVec 64)
    (ha : tenv ra = some (mkScUi64 wa))
    (hb : tenv rb = some (mkScUi64 wb))
    (hFr : HLORegFresh tenv k) :
    let (res, k', ops) := emitHLOCmp k dir ra rb
    k' = k + 2 ∧
    ops.all isNonReturnOp = true ∧
    ∃ tenv',
      evalOps tenv ops = .ok tenv' ∧
      tenv' res = some (mkScUi64 (if cmpDirBool dir wa wb then 1#64 else 0#64)) ∧
      HLORegFresh tenv' k' ∧
      (∀ q, (∀ j, k ≤ j → j < k' → q ≠ hloTmpReg j) → tenv' q = tenv q) := by
  dsimp only [emitHLOCmp]
  refine ⟨rfl, rfl, ?_⟩
  let bOut := cmpDirBool dir wa wb
  let tCmp : TensorVal := { ty := scI1Ty, data := #[if bOut then 1#64 else 0#64] }
  let e1 := tenv.bind (hloTmpReg k) tCmp
  let e2 := e1.bind (hloTmpReg (k + 1)) (mkScUi64 (if bOut then 1#64 else 0#64))
  refine ⟨e2, ?_, env_bind_self _ _ _, ?_, ?_⟩
  · have hs1 : evalOp tenv (.compare (hloTmpReg k) ra rb dir) = .ok e1 :=
      evalOp_compare_sc tenv _ ra rb dir wa wb ha hb
    have hs2 : evalOp e1 (.convert (hloTmpReg (k + 1)) (hloTmpReg k) .ui64) = .ok e2 :=
      evalOp_convert_i1_ui64_sc e1 _ _ bOut (env_bind_self _ _ _)
    rw [evalOps_cons_nonReturn _ _ _ rfl, hs1]
    change evalOps e1 _ = .ok e2
    rw [evalOps_cons_nonReturn _ _ _ rfl, hs2]
    rfl
  · have hf1 := hloRegFresh_bind_lt tCmp hFr (k := k + 1) (by omega)
    exact hloRegFresh_bind_lt (mkScUi64 (if bOut then 1#64 else 0#64)) hf1 (k := k + 2) (by omega)
  · intro q hq
    dsimp only [e2, e1]
    rw [env_bind_ne _ _ _ _ (hq (k + 1) (by omega) (by omega)),
        env_bind_ne _ _ _ _ (hq k (by omega) (by omega))]

end LeanNative.Proofs
