import LeanNative.Proofs.SymbolicTVUnarySoundness

namespace LeanNative.Proofs
set_option maxHeartbeats 40000

open LeanNative.IR
open LeanNative.Semantics

/-!
# Binary-Operator Normalization Soundness for `SymbolicTV` (`LeanNative.Proofs.SymbolicTVBinOpSoundness`)

Proves `normSymBinOpCore_u64_denotes`, `normSymBinOpStep_u64_denotes`, `normSymIteStep` lemmas,
`scalarToSymExpr_denotes`, and `normSymUnaryOpStep_sortU64` against `denoteSymExpr` / `evalScalarExpr`.
-/

theorem normSymBinOpCore_u64_denotes (ω : SymValuation) (op : BinOp) (l r : SymExpr)
    (w64 : Bool) (nl nr : UInt64)
    (hl : denoteSymExpr ω l = .ok (.u64 nl))
    (hr : denoteSymExpr ω r = .ok (.u64 nr)) :
    denoteSymExpr ω (normSymBinOpCore op l r w64) = evalBinOp op (.u64 nl) (.u64 nr) := by
  have deflt : denoteSymExpr ω (.binOp op l r) = evalBinOp op (.u64 nl) (.u64 nr) := by
    simp only [denoteSymExpr, hl, hr]
  cases op <;> dsimp only [normSymBinOpCore]
  case add =>
    split
    · cases hl; cases hr; rfl
    · cases hl
    · cases hr
    · cases hl
    · injection hr with h2; injection h2 with h2'; subst h2'
      rw [hl]; exact (evalBinOp_add_zero (.u64 nl)).symm
    · injection hl with h1; injection h1 with h1'; subst h1'
      rw [hr]; exact (evalBinOp_zero_add (.u64 nr)).symm
    · injection hr with h2; injection h2 with h2'; subst h2'
      rename_i x a b _
      cases hsub : subexprDefinitely64 w64 a x
      · exact deflt
      · simp only [↓reduceIte]
        obtain ⟨nx, hx, hnx⟩ := denote_binOp_constU64_u64 (Or.inl rfl) hl
        simp only [↓reduceIte] at hnx; subst hnx
        have hre := uint64_add_add_reassoc nx a b
        cases hs : (a + b == 0)
        · simp only [hs, Bool.false_eq_true, ↓reduceIte, denoteSymExpr, hx] at hre ⊢
          exact congrArg (Except.ok ∘ Val.u64) hre.symm
        · simp only [hs, ↓reduceIte] at hre ⊢
          rw [hx]; exact congrArg (Except.ok ∘ Val.u64) hre.symm
    · injection hr with h2; injection h2 with h2'; subst h2'
      rename_i x a b _
      cases hsub : subexprDefinitely64 w64 a x
      · exact deflt
      · simp only [↓reduceIte]
        obtain ⟨nx, hx, hnx⟩ := denote_binOp_constU64_u64 (Or.inr rfl) hl
        simp only [reduceCtorEq, ↓reduceIte] at hnx; subst hnx
        have hre := uint64_sub_add_reassoc nx a b
        cases hab : (a == b)
        · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hre ⊢
          by_cases hgt : b > a
          · simp only [hgt, decide_true, ↓reduceIte, denoteSymExpr, hx] at hre ⊢
            exact congrArg (Except.ok ∘ Val.u64) hre.symm
          · simp only [hgt, decide_false, Bool.false_eq_true, ↓reduceIte, denoteSymExpr, hx] at hre ⊢
            exact congrArg (Except.ok ∘ Val.u64) hre.symm
        · simp only [hab, ↓reduceIte] at hre ⊢
          rw [hx]; exact congrArg (Except.ok ∘ Val.u64) hre.symm
    · exact deflt
  case sub =>
    split
    · cases hl; cases hr; rfl
    · cases hl
    · cases hr
    · injection hr with h2; injection h2 with h2'; subst h2'
      rw [hl]; exact (evalBinOp_sub_zero (.u64 nl)).symm
    · injection hr with h2; injection h2 with h2'; subst h2'
      rename_i x a b _
      cases hsub : subexprDefinitely64 w64 a x
      · exact deflt
      · simp only [↓reduceIte]
        obtain ⟨nx, hx, hnx⟩ := denote_binOp_constU64_u64 (Or.inl rfl) hl
        simp only [↓reduceIte] at hnx; subst hnx
        have hre := uint64_add_sub_reassoc nx a b
        cases hab : (a == b)
        · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hre ⊢
          by_cases hgt : a > b
          · simp only [hgt, decide_true, ↓reduceIte, denoteSymExpr, hx] at hre ⊢
            exact congrArg (Except.ok ∘ Val.u64) hre.symm
          · simp only [hgt, decide_false, Bool.false_eq_true, ↓reduceIte, denoteSymExpr, hx] at hre ⊢
            exact congrArg (Except.ok ∘ Val.u64) hre.symm
        · simp only [hab, ↓reduceIte] at hre ⊢
          rw [hx]; exact congrArg (Except.ok ∘ Val.u64) hre.symm
    · injection hr with h2; injection h2 with h2'; subst h2'
      rename_i x a b _
      cases hsub : subexprDefinitely64 w64 a x
      · exact deflt
      · simp only [↓reduceIte]
        obtain ⟨nx, hx, hnx⟩ := denote_binOp_constU64_u64 (Or.inr rfl) hl
        simp only [reduceCtorEq, ↓reduceIte] at hnx; subst hnx
        have hre := uint64_sub_sub_reassoc nx a b
        cases hs : (a + b == 0)
        · simp only [hs, Bool.false_eq_true, ↓reduceIte, denoteSymExpr, hx] at hre ⊢
          exact congrArg (Except.ok ∘ Val.u64) hre.symm
        · simp only [hs, ↓reduceIte] at hre ⊢
          rw [hx]; exact congrArg (Except.ok ∘ Val.u64) hre.symm
    · cases hcond : ((w64 || exprDefinitely64 l) && (l == r))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases l with
        | constU256 _ => cases hl
        | _ => exact deflt
      · simp only [↓reduceIte]
        simp only [Bool.and_eq_true] at hcond
        have hlr := SymExpr_eq_of_beq hcond.2; subst hlr
        have hn : nl = nr := by rw [hl] at hr; injection hr with h1; injection h1 with h2
        subst hn
        change Except.ok (Val.u64 0) = Except.ok (Val.u64 (nl - nl))
        rw [UInt64.sub_self]
  case mul =>
    split
    · cases hl; cases hr; rfl
    · cases hl
    · cases hr
    · cases hl
    · injection hr with h2; injection h2 with h2'; subst h2'
      rw [hl]; exact (evalBinOp_mul_one (.u64 nl)).symm
    · injection hl with h1; injection h1 with h1'; subst h1'
      rw [hr]; exact (evalBinOp_one_mul (.u64 nr)).symm
    · injection hr with h2; injection h2 with h2'; subst h2'
      cases (w64 || exprDefinitely64 l)
      · exact deflt
      · change Except.ok (Val.u64 0) = Except.ok (Val.u64 (nl * 0)); rw [UInt64.mul_zero]
    · injection hl with h1; injection h1 with h1'; subst h1'
      cases (w64 || exprDefinitely64 r)
      · exact deflt
      · change Except.ok (Val.u64 0) = Except.ok (Val.u64 (0 * nr)); rw [UInt64.zero_mul]
    · injection hr with h2; injection h2 with h2'; subst h2'
      cases (w64 || exprDefinitely64 l)
      · exact deflt
      · simp only [↓reduceIte]
        split
        · rename_i k hk
          simp only [denoteSymExpr, hl]
          exact congrArg (Except.ok ∘ Val.u64) (pow2ShiftLog2_mul_right hk nl).symm
        · exact deflt
    · injection hl with h1; injection h1 with h1'; subst h1'
      cases (w64 || exprDefinitely64 r)
      · exact deflt
      · simp only [↓reduceIte]
        split
        · rename_i k hk
          simp only [denoteSymExpr, hr]
          exact congrArg (Except.ok ∘ Val.u64) (pow2ShiftLog2_mul_left hk nr).symm
        · exact deflt
    · exact deflt
  case div =>
    split
    · cases hl; cases hr; rfl
    · cases hr
    · injection hr with h2; injection h2 with h2'; subst h2'
      cases (w64 || exprDefinitely64 l)
      · exact deflt
      · change Except.ok (Val.u64 0) = Except.ok (Val.u64 (nl / 0))
        cases nl with | ofBitVec bv => exact congrArg (Except.ok ∘ Val.u64 ∘ UInt64.ofBitVec) BitVec.udiv_zero.symm
    · injection hr with h2; injection h2 with h2'; subst h2'
      rw [hl]
      change Except.ok (Val.u64 nl) = Except.ok (Val.u64 (nl / 1))
      cases nl with | ofBitVec bv => exact congrArg (Except.ok ∘ Val.u64 ∘ UInt64.ofBitVec) BitVec.udiv_one.symm
    · injection hr with h2; injection h2 with h2'; subst h2'
      cases (w64 || exprDefinitely64 l)
      · exact deflt
      · simp only [↓reduceIte]
        split
        · rename_i k hk
          simp only [denoteSymExpr, hl]
          exact congrArg (Except.ok ∘ Val.u64) (pow2ShiftLog2_div hk nl).symm
        · exact deflt
    · exact deflt
  case mod =>
    split
    · cases hl; cases hr; rfl
    · injection hr with h2; injection h2 with h2'; subst h2'
      cases (w64 || exprDefinitely64 l)
      · exact deflt
      · simp only [↓reduceIte, hl]
        change Except.ok (Val.u64 nl) = Except.ok (Val.u64 (nl % 0))
        cases nl with | ofBitVec bv => exact congrArg (Except.ok ∘ Val.u64 ∘ UInt64.ofBitVec) BitVec.umod_zero.symm
    · injection hr with h2; injection h2 with h2'; subst h2'
      cases (w64 || exprDefinitely64 l)
      · exact deflt
      · change Except.ok (Val.u64 0) = Except.ok (Val.u64 (nl % 1))
        cases nl with | ofBitVec bv => exact congrArg (Except.ok ∘ Val.u64 ∘ UInt64.ofBitVec) BitVec.umod_one.symm
    · injection hr with h2; injection h2 with h2'; subst h2'
      cases (w64 || exprDefinitely64 l)
      · exact deflt
      · simp only [↓reduceIte]
        split
        · rename_i k hk
          simp only [denoteSymExpr, hl]
          exact congrArg (Except.ok ∘ Val.u64) (pow2ShiftLog2_mod hk nl).symm
        · exact deflt
    · exact deflt
  case bitAnd =>
    split
    · cases hl; cases hr; rfl
    · cases hl
    · cases hr
    · cases hl
    · injection hr with h2; injection h2 with h2'; subst h2'
      cases (w64 || exprDefinitely64 l)
      · exact deflt
      · change Except.ok (Val.u64 0) = Except.ok (Val.u64 (nl &&& 0)); rw [UInt64.and_zero]
    · injection hl with h1; injection h1 with h1'; subst h1'
      cases (w64 || exprDefinitely64 r)
      · exact deflt
      · change Except.ok (Val.u64 0) = Except.ok (Val.u64 (0 &&& nr)); rw [UInt64.zero_and]
    · cases hxy : (l == r)
      · exact deflt
      · simp only [↓reduceIte]
        have hlr := SymExpr_eq_of_beq hxy; subst hlr
        have hn : nl = nr := by rw [hl] at hr; injection hr with h1; injection h1 with h2
        subst hn
        rw [hl]; exact (evalBinOp_and_self (.u64 nl)).symm
  case bitOr =>
    split
    · cases hl; cases hr; rfl
    · cases hl
    · cases hr
    · cases hl
    · injection hr with h2; injection h2 with h2'; subst h2'
      rw [hl]; exact (evalBinOp_or_zero (.u64 nl)).symm
    · injection hl with h1; injection h1 with h1'; subst h1'
      rw [hr]; exact (evalBinOp_zero_or (.u64 nr)).symm
    · cases hxy : (l == r)
      · exact deflt
      · simp only [↓reduceIte]
        have hlr := SymExpr_eq_of_beq hxy; subst hlr
        have hn : nl = nr := by rw [hl] at hr; injection hr with h1; injection h1 with h2
        subst hn
        rw [hl]; exact (evalBinOp_or_self (.u64 nl)).symm
  case bitXor =>
    split
    · cases hl; cases hr; rfl
    · cases hl
    · cases hr
    · cases hl
    · injection hr with h2; injection h2 with h2'; subst h2'
      rw [hl]; exact (evalBinOp_xor_zero (.u64 nl)).symm
    · injection hl with h1; injection h1 with h1'; subst h1'
      rw [hr]; exact (evalBinOp_zero_xor (.u64 nr)).symm
    · cases hcond : ((w64 || exprDefinitely64 l) && (l == r))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases l with
        | constU256 _ => cases hl
        | _ => exact deflt
      · simp only [↓reduceIte]
        simp only [Bool.and_eq_true] at hcond
        have hlr := SymExpr_eq_of_beq hcond.2; subst hlr
        have hn : nl = nr := by rw [hl] at hr; injection hr with h1; injection h1 with h2
        subst hn
        change Except.ok (Val.u64 0) = Except.ok (Val.u64 (nl ^^^ nl))
        rw [UInt64.xor_self]
  case shl =>
    split
    · cases hl; cases hr
      exact congrArg (Except.ok ∘ Val.u64) (uint64_shiftLeft_and_63 _ _)
    · cases hl
    · cases hr
    · injection hr with h2; injection h2 with h2'; subst h2'
      rw [hl]
      change Except.ok (Val.u64 nl) = Except.ok (Val.u64 (nl <<< 0))
      cases nl with | ofBitVec bv => exact congrArg (Except.ok ∘ Val.u64 ∘ UInt64.ofBitVec) (BitVec.shiftLeft_zero bv).symm
    · exact deflt
  case shr =>
    split
    · cases hl; cases hr
      exact congrArg (Except.ok ∘ Val.u64) (uint64_shiftRight_and_63 _ _)
    · cases hl
    · cases hr
    · injection hr with h2; injection h2 with h2'; subst h2'
      rw [hl]
      change Except.ok (Val.u64 nl) = Except.ok (Val.u64 (nl >>> 0))
      cases nl with | ofBitVec bv => exact congrArg (Except.ok ∘ Val.u64 ∘ UInt64.ofBitVec) (BitVec.ushiftRight_zero bv).symm
    · exact deflt
  case sar =>
    split
    · cases hl
    · cases hr
    · exact deflt
  case clmul64 =>
    split
    · cases hl; cases hr; rfl
    · exact deflt
  case clmul64Hi =>
    split
    · cases hl; cases hr; rfl
    · exact deflt
  case gf2Affine =>
    split
    · cases hl; cases hr; rfl
    · exact deflt
  case eor3 =>
    split
    · cases hl; cases hr; rfl
    · exact deflt
  case eq =>
    split
    · cases hl; cases hr; rfl
    · cases hl
    · cases hl
    · cases hr
    · cases hl
    · cases hr
    · cases hl
    · cases hr
    · cases hl
    · by_cases hxy : (l == r) = true
      · have hlr := SymExpr_eq_of_beq hxy; subst hlr
        have hn : nl = nr := by rw [hl] at hr; injection hr with h1; injection h1 with h2
        subst hn
        simp only [hxy, Bool.true_and]
        split
        · cases hl
        · split
          · change Except.ok (Val.bool true) = Except.ok (Val.bool (nl == nl)); simp
          · exact deflt
      · simp only [hxy, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; exact deflt
  case lt =>
    split
    · cases hl; cases hr; rfl
    · cases hl
    · by_cases hxy : (l == r) = true
      · have hlr := SymExpr_eq_of_beq hxy; subst hlr
        have hn : nl = nr := by rw [hl] at hr; injection hr with h1; injection h1 with h2
        subst hn
        simp only [hxy, Bool.true_and]
        split
        · cases hl
        · split
          · change Except.ok (Val.bool false) = Except.ok (Val.bool (decide (nl < nl)))
            have hirr : ¬ (nl < nl) := Nat.lt_irrefl nl.toNat
            simp [hirr]
          · exact deflt
      · simp only [hxy, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; exact deflt
  case le =>
    split
    · cases hl; cases hr; rfl
    · cases hl
    · by_cases hxy : (l == r) = true
      · have hlr := SymExpr_eq_of_beq hxy; subst hlr
        have hn : nl = nr := by rw [hl] at hr; injection hr with h1; injection h1 with h2
        subst hn
        simp only [hxy, Bool.true_and]
        split
        · cases hl
        · split
          · change Except.ok (Val.bool true) = Except.ok (Val.bool (decide (nl ≤ nl)))
            simp
          · exact deflt
      · simp only [hxy, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; exact deflt
  case addChecked256 => exact deflt
  case subChecked256 => exact deflt
  case mulChecked256 => exact deflt

/-- Single-step `normSymBinOpStep` on two 64-bit-denoting symbolic operands preserves concrete
    denotation for every binary operator. -/
theorem normSymBinOpStep_u64_denotes (ω : SymValuation) (op : BinOp) (l r : SymExpr)
    (w64Safe : Bool) (nl nr : UInt64)
    (hl : denoteSymExpr ω l = .ok (.u64 nl))
    (hr : denoteSymExpr ω r = .ok (.u64 nr)) :
    denoteSymExpr ω (normSymBinOpStep op l r w64Safe) = evalBinOp op (.u64 nl) (.u64 nr) := by
  unfold normSymBinOpStep
  cases hswap : (SymExpr.isCommutative op && decide (SymExpr.rank l > SymExpr.rank r))
  · exact normSymBinOpCore_u64_denotes ω op l r _ nl nr hl hr
  · simp only [↓reduceIte]
    simp only [Bool.and_eq_true] at hswap
    rw [normSymBinOpCore_u64_denotes ω op r l _ nr nl hr hl]
    exact evalBinOp_u64_comm hswap.1 nl nr

/-- A constant condition selects exactly one branch. -/
theorem normSymIteStep_constBool (t e : SymExpr) (b : Bool) :
    normSymIteStep (.constBool b) t e = if b then t else e := by
  cases b <;> rfl

/-- Identical branches collapse when the condition is definitely boolean and non-literal. -/
theorem normSymIteStep_same_branch (c t : SymExpr) :
    atomDefinitelyBool c = true → normSymIteStep c t t = t := by
  intro h
  cases c with
  | constBool b => cases b <;> rfl
  | binOp op l r => cases op <;> simp [normSymIteStep, atomDefinitelyBool] at h ⊢
  | ite c1 t1 e1 => simp [normSymIteStep, h]
  | _ => simp [atomDefinitelyBool] at h

/-- A pure 64-bit scalar expression denotes exactly what `evalScalarExpr` computes. -/
theorem scalarToSymExpr_denotes (env : VarEnv) (e : ScalarExpr) :
    isPureU64ScalarExpr e = true →
    denoteSymExpr (SymValuation.ofVarEnv env) (scalarToSymExpr e) = evalScalarExpr env e := by
  intro h
  induction e with
  | constU64 v => rfl
  | constBool b => simp [isPureU64ScalarExpr] at h
  | var id => rfl
  | binOp op l r ihl ihr =>
    simp only [isPureU64ScalarExpr, Bool.and_eq_true] at h
    rcases h with ⟨⟨hop, hl⟩, hr⟩
    simp only [scalarToSymExpr, denoteSymExpr, evalScalarExpr, ihl hl, ihr hr]
    cases evalScalarExpr env l <;> cases evalScalarExpr env r <;> rfl
  | unaryOp op a iha =>
    cases op <;> simp [isPureU64ScalarExpr] at h
    · simp only [scalarToSymExpr, denoteSymExpr, evalScalarExpr, iha h]
      cases evalScalarExpr env a <;> rfl
    · simp only [scalarToSymExpr, denoteSymExpr, evalScalarExpr, iha h]
      cases evalScalarExpr env a <;> rfl
  | select c t e ihc iht ihe => simp [isPureU64ScalarExpr] at h
  | fma a b c iha ihb ihc => simp [isPureU64ScalarExpr] at h

/-- `normSymUnaryOpStep` preserves `some sortU64` under `.not` and `.neg`. -/
theorem normSymUnaryOpStep_sortU64 (st : SymExecState) (op : UnaryOp) (a : SymExpr)
    (hop : op = .not ∨ op = .neg)
    (hsort : symExprScalarSort? st a = some sortU64) :
    symExprScalarSort? st (normSymUnaryOpStep op a) = some sortU64 := by
  rcases hop with rfl | rfl
  · rw [normSymUnaryOpStep.eq_def]
    cases a with
    | constBool _ => cases hsort
    | constU64 _ => rfl
    | constU256 _ => cases hsort
    | unaryOp op2 x =>
      cases op2 with
      | not =>
        dsimp only []
        simp only [symExprScalarSort?] at hsort
        cases x with
        | constU256 _ => cases hsort
        | _ => dsimp only []; split <;> exact hsort
      | neg | clz256 => exact hsort
    | _ => exact hsort
  · rw [normSymUnaryOpStep.eq_def]
    cases a with
    | constBool _ => cases hsort
    | constU64 _ => rfl
    | constU256 _ => cases hsort
    | unaryOp op2 x =>
      cases op2 with
      | neg =>
        dsimp only []
        simp only [symExprScalarSort?] at hsort
        split <;> exact hsort
      | not | clz256 => exact hsort
    | _ => exact hsort


end LeanNative.Proofs
