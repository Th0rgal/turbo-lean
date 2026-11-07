import LeanMLIR.Dialects.LLVM.Basic
import LeanNative.Backend.LLVMAst.Eval

/-!
# Stage 2C: `LLVMAst` ↔ `opencompl/lean-mlir` Formal Bisimulation

Proves `0-sorryAx` equivalence between `LeanNative.Backend.LLVMAst` (`stepInstr` / `execInstrs`)
and upstream `opencompl/lean-mlir` (`LLVM.IntW w := PoisonOr (BitVec w)`, `LLVM.*` instruction
semantics, and `InstCombine.Op.denote` over `LLVM.Op` / `MOp 0`).

Key semantic relations established:
1. Pure / poison-producing integer ALU (`add`, `sub`, `mul` with `nsw`/`nuw`, `and`, `or`, `xor`),
   shifts (`shl` with `nsw`/`nuw`, `lshr`/`ashr` with `exact` and overshift poison),
   comparisons (`icmp` across all 10 `ICmpPred` / `LLVM.IntPred` predicates),
   casts (`trunc`, `zext`, `sext` when target width constraints hold), and `select`
   (including non-strict non-selected branch preservation vs condition-poison propagation)
   commute bit-for-bit with `LLVM.*` and `InstCombine.Op.denote`.
2. Division and remainder (`udiv`, `sdiv`, `urem`, `srem`) state the exact UB-vs-poison boundary:
   `opencompl/lean-mlir`'s pure `LLVM.{udiv,sdiv,urem,srem}` models division by zero and signed
   `INT_MIN / -1` overflow as `.poison` inside the pure `InstCombine` dialect (`EffectKind.pure`),
   whereas `LLVMAst.stepInstr` raises immediate `.inl (.ub ...)` per the LLVM LangRef and coincides
   exactly with `toLLVMVal w (LLVM.{udiv,sdiv,urem,srem} ...)` whenever the non-UB precondition holds.
3. Straight-line `execInstrs` compositionally preserves valuation agreement across arbitrary
   instruction sequences.
-/

namespace LeanMLIRBridge

open LeanNative.Backend.TargetIR
open LeanNative.Backend.LLVMAst

/-- Embed an upstream `opencompl/lean-mlir` `LLVM.IntW w.bits` (`PoisonOr (BitVec w.bits)`)
into `LLVMAst.LLVMVal`. -/
def toLLVMVal (w : IntWidth) : LLVM.IntW w.bits → LLVMVal
  | .poison => .poison
  | .value bv => .bits w bv

/-- Partial inverse projecting a well-typed `LLVMVal` at width `w` to `LLVM.IntW w.bits`. -/
def ofLLVMVal? (w : IntWidth) : LLVMVal → Option (LLVM.IntW w.bits)
  | .poison => some .poison
  | .bits w' bv => if h : w' = w then some (.value (h ▸ bv)) else none
  | _ => none

@[simp]
theorem ofLLVMVal?_toLLVMVal (w : IntWidth) (x : LLVM.IntW w.bits) :
    ofLLVMVal? w (toLLVMVal w x) = some x := by
  cases x using PoisonOr.casesOn' <;> simp [toLLVMVal, ofLLVMVal?]

/-- Translate `LLVMAst.OverflowFlags` to `opencompl/lean-mlir`'s `LLVM.NoWrapFlags`. -/
def toNoWrapFlags : OverflowFlags → LLVM.NoWrapFlags
  | .none => { nsw := false, nuw := false }
  | .nsw => { nsw := true, nuw := false }
  | .nuw => { nsw := false, nuw := true }
  | .nswNuw => { nsw := true, nuw := true }

/-- Translate `LLVMAst.ICmpPred` to `opencompl/lean-mlir`'s `LLVM.IntPred`. -/
def toIntPred : ICmpPred → LLVM.IntPred
  | .eq => .eq
  | .ne => .ne
  | .ult => .ult
  | .ule => .ule
  | .ugt => .ugt
  | .uge => .uge
  | .slt => .slt
  | .sle => .sle
  | .sgt => .sgt
  | .sge => .sge

/-! ## Two's-Complement Bridge Lemmas (`bvSigned` / Overflow / `icmp` / Shifts / Division) -/

private theorem two_pow_eq_two_mul_pred (n : Nat) (hpos : 0 < n) :
    2 ^ n = 2 * 2 ^ (n - 1) := by
  cases n with
  | zero => omega
  | succ k => simp [Nat.pow_succ, Nat.mul_comm]

private theorem int_two_pow_eq_natCast (n : Nat) :
    ((2 : Int) ^ n) = ((2 ^ n : Nat) : Int) := by
  rw [Int.natCast_pow]
  rfl

theorem bvSigned_eq_toInt (w : IntWidth) (v : BitVec w.bits) :
    bvSigned w v = v.toInt := by
  have hpos : 0 < w.bits := w.bits_pos
  have h2w : 2 ^ w.bits = 2 * 2 ^ (w.bits - 1) := two_pow_eq_two_mul_pred w.bits hpos
  unfold bvSigned BitVec.toInt
  simp only [Int.ofNat_eq_natCast, int_two_pow_eq_natCast]
  split <;> split <;> omega

theorem addOverflowNSW_eq_saddOverflow (w : IntWidth) (a b : BitVec w.bits) :
    addOverflowNSW w a b = BitVec.saddOverflow a b := by
  have hpos : 0 < w.bits := w.bits_pos
  unfold addOverflowNSW BitVec.saddOverflow
  rw [bvSigned_eq_toInt, bvSigned_eq_toInt]
  cases hc : w.bits == 0
  · simp only [int_two_pow_eq_natCast]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Bool.or_eq_true]
    omega
  · simp at hc; omega

theorem subOverflowNSW_eq_ssubOverflow (w : IntWidth) (a b : BitVec w.bits) :
    subOverflowNSW w a b = BitVec.ssubOverflow a b := by
  have hpos : 0 < w.bits := w.bits_pos
  unfold subOverflowNSW BitVec.ssubOverflow
  rw [bvSigned_eq_toInt, bvSigned_eq_toInt]
  cases hc : w.bits == 0
  · simp only [int_two_pow_eq_natCast]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Bool.or_eq_true]
    omega
  · simp at hc; omega

theorem mulOverflowNSW_eq_smulOverflow (w : IntWidth) (a b : BitVec w.bits) :
    mulOverflowNSW w a b = BitVec.smulOverflow a b := by
  have hpos : 0 < w.bits := w.bits_pos
  unfold mulOverflowNSW BitVec.smulOverflow
  rw [bvSigned_eq_toInt, bvSigned_eq_toInt]
  cases hc : w.bits == 0
  · simp only [int_two_pow_eq_natCast]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Bool.or_eq_true]
    omega
  · simp at hc; omega

theorem addOverflowNUW_eq_uaddOverflow (w : IntWidth) (a b : BitVec w.bits) :
    addOverflowNUW w a b = BitVec.uaddOverflow a b := by
  unfold addOverflowNUW BitVec.uaddOverflow
  rfl

theorem subOverflowNUW_eq_usubOverflow (w : IntWidth) (a b : BitVec w.bits) :
    subOverflowNUW w a b = BitVec.usubOverflow a b := by
  unfold subOverflowNUW BitVec.usubOverflow
  rfl

theorem mulOverflowNUW_eq_umulOverflow (w : IntWidth) (a b : BitVec w.bits) :
    mulOverflowNUW w a b = BitVec.umulOverflow a b := by
  unfold mulOverflowNUW BitVec.umulOverflow
  rfl

theorem icmpEval_eq_mlir (p : ICmpPred) (w : IntWidth) (a b : BitVec w.bits) :
    icmpEval p w a b = LLVM.icmp' (toIntPred p) a b := by
  cases p <;> simp [icmpEval, toIntPred, LLVM.icmp', BitVec.ult, BitVec.ule,
    BitVec.slt, BitVec.sle, bvSigned_eq_toInt]

private theorem two_pow_pos_nat (k : Nat) : 0 < 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih => simp [Nat.pow_succ]; omega

theorem shlOverflowNSW_eq_mlir (w : IntWidth) (a amt : BitVec w.bits)
    (h_lt : amt.toNat < w.bits) :
    shlOverflowNSW w a amt = decide (((a <<< amt).sshiftRight' amt) ≠ a) := by
  unfold shlOverflowNSW
  rw [bvSigned_eq_toInt]
  have hpos : 0 < w.bits := w.bits_pos
  have h_round : ((a <<< amt).sshiftRight' amt = a) ↔
      (-((2 : Int) ^ (w.bits - 1)) ≤ a.toInt * (2 : Int) ^ amt.toNat ∧
       a.toInt * (2 : Int) ^ amt.toNat ≤ (2 : Int) ^ (w.bits - 1) - 1) := by
    have h_sh_def : (a <<< amt).sshiftRight' amt = (a <<< amt.toNat).sshiftRight amt.toNat := rfl
    rw [h_sh_def, ← BitVec.toInt_inj, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
    have h2pos_nat : 0 < 2 ^ amt.toNat := two_pow_pos_nat amt.toNat
    have h2pos : (0 : Int) < ((2 ^ amt.toNat : Nat) : Int) := Int.natCast_pos.mpr h2pos_nat
    have h_cast_amt : ((2 : Int) ^ amt.toNat) = ((2 ^ amt.toNat : Nat) : Int) :=
      int_two_pow_eq_natCast amt.toNat
    have h_half_nat : 2 ^ (w.bits - 1) = 2 ^ (w.bits - 1 - amt.toNat) * 2 ^ amt.toNat := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have h_half : ((2 : Int) ^ (w.bits - 1)) =
        ((2 ^ (w.bits - 1 - amt.toNat) : Nat) : Int) * ((2 ^ amt.toNat : Nat) : Int) := by
      rw [int_two_pow_eq_natCast, h_half_nat, Int.natCast_mul]
    have h_full_nat : 2 ^ w.bits = 2 * 2 ^ (w.bits - 1) := two_pow_eq_two_mul_pred w.bits hpos
    have h_toInt_shl : (a <<< amt.toNat).toInt =
        Int.bmod (a.toInt * ((2 ^ amt.toNat : Nat) : Int)) (2 ^ w.bits) := by
      rw [BitVec.toInt_shiftLeft, Nat.shiftLeft_eq, Int.natCast_mul,
        Int.mul_bmod, ← BitVec.toInt_eq_toNat_bmod,
        ← BitVec.toInt_bmod_cancel a, ← Int.mul_bmod, BitVec.toInt_bmod_cancel]
    constructor
    · intro heq
      have h_bds : (a <<< amt.toNat).toInt < ((2 ^ (w.bits - 1) : Nat) : Int) := by
        have hb0 : (a <<< amt.toNat).toInt < (2 : Int) ^ (w.bits - 1) := BitVec.toInt_lt
        rwa [int_two_pow_eq_natCast] at hb0
      have h_lo : -((2 ^ (w.bits - 1) : Nat) : Int) ≤ (a <<< amt.toNat).toInt := by
        have hl0 : -((2 : Int) ^ (w.bits - 1)) ≤ (a <<< amt.toNat).toInt := BitVec.le_toInt (a <<< amt.toNat)
        rwa [int_two_pow_eq_natCast] at hl0
      rw [h_half_nat, Int.natCast_mul] at h_bds h_lo
      have h_neg_mul : -(((2 ^ (w.bits - 1 - amt.toNat) : Nat) : Int) * ((2 ^ amt.toNat : Nat) : Int)) =
          (-((2 ^ (w.bits - 1 - amt.toNat) : Nat) : Int)) * ((2 ^ amt.toNat : Nat) : Int) := by
        rw [Int.neg_mul_eq_neg_mul]
      rw [h_neg_mul] at h_lo
      have h1 : -((2 ^ (w.bits - 1 - amt.toNat) : Nat) : Int) ≤
          (a <<< amt.toNat).toInt / ((2 ^ amt.toNat : Nat) : Int) :=
        Int.le_ediv_of_mul_le h2pos h_lo
      have h2 : (a <<< amt.toNat).toInt / ((2 ^ amt.toNat : Nat) : Int) <
          ((2 ^ (w.bits - 1 - amt.toNat) : Nat) : Int) :=
        Int.ediv_lt_of_lt_mul h2pos h_bds
      rw [heq] at h1 h2
      have h2' : a.toInt ≤ ((2 ^ (w.bits - 1 - amt.toNat) : Nat) : Int) - 1 := by omega
      have hlo_prod := Int.mul_le_mul_of_nonneg_right h1 (Int.le_of_lt h2pos)
      have hhi_prod := Int.mul_le_mul_of_nonneg_right h2' (Int.le_of_lt h2pos)
      rw [Int.sub_mul, Int.one_mul] at hhi_prod
      rw [h_cast_amt, h_half]
      omega
    · rintro ⟨hlo, hhi⟩
      rw [h_cast_amt, int_two_pow_eq_natCast] at hlo hhi
      have h_bmod_id : Int.bmod (a.toInt * ((2 ^ amt.toNat : Nat) : Int)) (2 ^ w.bits) =
          a.toInt * ((2 ^ amt.toNat : Nat) : Int) := by
        apply Int.bmod_eq_of_le
        · omega
        · omega
      rw [h_toInt_shl, h_bmod_id, Int.mul_ediv_cancel _ (Int.ne_of_gt h2pos)]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, ne_eq, h_round]
  omega

theorem shiftedOut_iff_ushift_roundtrip (w : IntWidth) (a amt : BitVec w.bits)
    (h_lt : amt.toNat < w.bits) :
    ((a <<< (w.bits - amt.toNat)) != 0#w.bits) = decide ((a >>> amt) <<< amt ≠ a) := by
  have h_sh_eq : ((a >>> amt) <<< amt) = ((a >>> amt.toNat) <<< amt.toNat) := rfl
  rw [h_sh_eq]
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
  apply Decidable.not_iff_not.mpr
  constructor
  · intro h_zero
    ext i hi
    rw [BitVec.getElem_shiftLeft hi]
    by_cases h_ge : i < amt.toNat
    · simp only [h_ge, decide_true, Bool.not_true, Bool.false_and]
      have h_idx : i + (w.bits - amt.toNat) < w.bits := by omega
      have hbit : (a <<< (w.bits - amt.toNat))[i + (w.bits - amt.toNat)] = (0#w.bits)[i + (w.bits - amt.toNat)] :=
        congrArg (fun bv => bv[i + (w.bits - amt.toNat)]'h_idx) h_zero
      rw [BitVec.getElem_shiftLeft h_idx, BitVec.getElem_zero] at hbit
      have h_not : ¬(i + (w.bits - amt.toNat) < w.bits - amt.toNat) := by omega
      have h_sub : i + (w.bits - amt.toNat) - (w.bits - amt.toNat) = i := by omega
      simp only [h_not, decide_false, Bool.not_false, Bool.true_and, h_sub] at hbit
      exact hbit.symm
    · have h_sub_lt : i - amt.toNat < w.bits := by omega
      have h_add : amt.toNat + (i - amt.toNat) = i := by omega
      simp only [h_ge, decide_false, Bool.not_false, Bool.true_and]
      rw [BitVec.getElem_ushiftRight a (i - amt.toNat) amt.toNat h_sub_lt]
      simp [BitVec.getLsbD_eq_getElem hi, h_add]
  · intro h_rt
    ext i hi
    rw [BitVec.getElem_shiftLeft hi, BitVec.getElem_zero]
    by_cases h_low : i < w.bits - amt.toNat
    · simp [h_low]
    · simp only [h_low, decide_false, Bool.not_false, Bool.true_and]
      have h_idx : i - (w.bits - amt.toNat) < w.bits := by omega
      have hbit : ((a >>> amt.toNat) <<< amt.toNat)[i - (w.bits - amt.toNat)] = a[i - (w.bits - amt.toNat)] :=
        congrArg (fun bv => bv[i - (w.bits - amt.toNat)]'h_idx) h_rt
      rw [BitVec.getElem_shiftLeft h_idx] at hbit
      have h_lt_amt : i - (w.bits - amt.toNat) < amt.toNat := by omega
      simp only [h_lt_amt, decide_true, Bool.not_true, Bool.false_and] at hbit
      exact hbit.symm

private theorem ofNat_cond_eq_ofInt (n : Nat) (z : Int) :
    (if 0 ≤ z then BitVec.ofNat n z.toNat
     else BitVec.ofNat n (2 ^ n - (-z).toNat % 2 ^ n)) = BitVec.ofInt n z := by
  by_cases hz : 0 ≤ z
  · simp only [hz, ↓reduceIte]
    have hz_eq : ((z.toNat : Nat) : Int) = z := Int.toNat_of_nonneg hz
    rw [← BitVec.ofInt_natCast, hz_eq]
  · simp only [hz, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_ofInt]
    let m := (-z).toNat
    have hm : z = -(m : Int) := by omega
    have hm_toNat : (-z).toNat = m := rfl
    rw [hm_toNat, hm]
    have hpos : 0 < 2 ^ n := two_pow_pos_nat n
    by_cases hrem : m % 2 ^ n = 0
    · simp only [hrem, Nat.sub_zero, Nat.mod_self]
      have hdvd : (2 ^ n) ∣ m := Nat.dvd_of_mod_eq_zero hrem
      rcases hdvd with ⟨k, hk⟩
      rw [hk]
      have hmul : -(((2 ^ n * k : Nat) : Int)) = ((2 ^ n : Nat) : Int) * (-(k : Int)) := by
        rw [Int.natCast_mul, Int.mul_neg]
      rw [hmul, Int.mul_emod_right]
      rfl
    · have hlt : m % 2 ^ n < 2 ^ n := Nat.mod_lt _ hpos
      have hle : m % 2 ^ n ≤ 2 ^ n := Nat.le_of_lt hlt
      have hsub_lt : 2 ^ n - m % 2 ^ n < 2 ^ n := by omega
      rw [Nat.mod_eq_of_lt hsub_lt]
      have hdiv : (m : Int) = ((2 ^ n : Nat) : Int) * ((m / 2 ^ n : Nat) : Int) + ((m % 2 ^ n : Nat) : Int) := by
        have hd := congrArg (Nat.cast (R := Int)) (Nat.div_add_mod m (2 ^ n)).symm
        simpa [Int.natCast_add, Int.natCast_mul] using hd
      have hsub_cast : (((2 ^ n - m % 2 ^ n : Nat) : Int)) =
          ((2 ^ n : Nat) : Int) - ((m % 2 ^ n : Nat) : Int) := Int.ofNat_sub hle
      have h_decomp : -(m : Int) =
          (((2 ^ n - m % 2 ^ n : Nat) : Int)) +
          ((2 ^ n : Nat) : Int) * (-((m / 2 ^ n : Nat) : Int) - 1) := by
        have hmul_exp :
            ((2 ^ n : Nat) : Int) * (-((m / 2 ^ n : Nat) : Int) - 1) =
              -(((2 ^ n : Nat) : Int) * ((m / 2 ^ n : Nat) : Int)) - ((2 ^ n : Nat) : Int) := by
          rw [Int.sub_eq_add_neg, Int.mul_add, Int.mul_neg, Int.mul_neg, Int.mul_one, ← Int.sub_eq_add_neg]
        omega
      have hlo : (0 : Int) ≤ ((2 ^ n - m % 2 ^ n : Nat) : Int) := Int.natCast_nonneg _
      have hhi : ((2 ^ n - m % 2 ^ n : Nat) : Int) < ((2 ^ n : Nat) : Int) :=
        Int.ofNat_lt.mpr hsub_lt
      rw [h_decomp, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hlo hhi, Int.toNat_natCast]

theorem bvSDiv_eq_sdiv (w : IntWidth) (a b : BitVec w.bits) :
    bvSDiv w a b = BitVec.sdiv a b := by
  unfold bvSDiv
  dsimp only []
  rw [bvSigned_eq_toInt, bvSigned_eq_toInt, ofNat_cond_eq_ofInt]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_ofInt, BitVec.toInt_sdiv]

theorem bvSRem_eq_srem (w : IntWidth) (a b : BitVec w.bits) :
    bvSRem w a b = BitVec.srem a b := by
  have hpos : 0 < w.bits := w.bits_pos
  have h2w : 2 ^ w.bits = 2 * 2 ^ (w.bits - 1) := two_pow_eq_two_mul_pred w.bits hpos
  unfold bvSRem
  dsimp only []
  rw [bvSigned_eq_toInt, bvSigned_eq_toInt, ofNat_cond_eq_ofInt]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_ofInt, BitVec.toInt_srem]
  have h := BitVec.toInt_srem a b
  have hlo : -((2 : Int) ^ (w.bits - 1)) ≤ (a.srem b).toInt := BitVec.le_toInt (a.srem b)
  have hhi : (a.srem b).toInt < (2 : Int) ^ (w.bits - 1) := BitVec.toInt_lt
  rw [h, int_two_pow_eq_natCast] at hlo hhi
  apply Int.bmod_eq_of_le <;> omega

/-! ## Instruction-Level Bisimulation (`stepInstr` ↔ `LLVM.*` & `InstCombine.Op.denote`) -/

@[simp]
private theorem intW_bind_poison {w₁ w₂ : Nat} (f : BitVec w₁ → LLVM.IntW w₂) :
    (PoisonOr.poison : LLVM.IntW w₁) >>= f = PoisonOr.poison := rfl

@[simp]
private theorem intW_bind_value {w₁ w₂ : Nat} (v : BitVec w₁) (f : BitVec w₁ → LLVM.IntW w₂) :
    (PoisonOr.value v : LLVM.IntW w₁) >>= f = f v := rfl

@[simp]
private theorem intW_mk_none {w : Nat} :
    ({ toOption := none } : LLVM.IntW w) = PoisonOr.poison := rfl

@[simp]
private theorem intW_mk_some {w : Nat} (v : BitVec w) :
    ({ toOption := some v } : LLVM.IntW w) = PoisonOr.value v := rfl

theorem stepInstr_add_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (flags : OverflowFlags) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.add dst flags w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w (LLVM.add xa xb (toNoWrapFlags flags)))) := by
  rcases xa with ⟨none | va⟩ <;> rcases xb with ⟨none | vb⟩ <;> cases flags
  all_goals
    simp only [intW_mk_none, intW_mk_some] at ha hb ⊢
    simp only [stepInstr, stepInstrWith, binResult, ha, hb, toLLVMVal, toNoWrapFlags,
      LLVM.add, LLVM.add?, intW_bind_poison, intW_bind_value, flagsOverflow,
      addOverflowNSW_eq_saddOverflow, addOverflowNUW_eq_uaddOverflow, ↓reduceDIte]
    try (by_cases hs : BitVec.saddOverflow va vb = true <;>
         by_cases hu : BitVec.uaddOverflow va vb = true <;>
         simp [hs, hu])

theorem stepInstr_sub_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (flags : OverflowFlags) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.sub dst flags w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w (LLVM.sub xa xb (toNoWrapFlags flags)))) := by
  rcases xa with ⟨none | va⟩ <;> rcases xb with ⟨none | vb⟩ <;> cases flags
  all_goals
    simp only [intW_mk_none, intW_mk_some] at ha hb ⊢
    simp only [stepInstr, stepInstrWith, binResult, ha, hb, toLLVMVal, toNoWrapFlags,
      LLVM.sub, LLVM.sub?, intW_bind_poison, intW_bind_value, flagsOverflow,
      subOverflowNSW_eq_ssubOverflow, subOverflowNUW_eq_usubOverflow, ↓reduceDIte]
    try (by_cases hs : BitVec.ssubOverflow va vb = true <;>
         by_cases hu : BitVec.usubOverflow va vb = true <;>
         simp [hs, hu])

theorem stepInstr_mul_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (flags : OverflowFlags) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.mul dst flags w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w (LLVM.mul xa xb (toNoWrapFlags flags)))) := by
  rcases xa with ⟨none | va⟩ <;> rcases xb with ⟨none | vb⟩ <;> cases flags
  all_goals
    simp only [intW_mk_none, intW_mk_some] at ha hb ⊢
    simp only [stepInstr, stepInstrWith, binResult, ha, hb, toLLVMVal, toNoWrapFlags,
      LLVM.mul, LLVM.mul?, intW_bind_poison, intW_bind_value, flagsOverflow,
      mulOverflowNSW_eq_smulOverflow, mulOverflowNUW_eq_umulOverflow, ↓reduceDIte]
    try (by_cases hs : BitVec.smulOverflow va vb = true <;>
         by_cases hu : BitVec.umulOverflow va vb = true <;>
         simp [hs, hu])

theorem stepInstr_and_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.and_ dst w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w (LLVM.and xa xb))) := by
  rcases xa with ⟨none | va⟩ <;> rcases xb with ⟨none | vb⟩ <;>
    simp [stepInstr, stepInstrWith, binResult, ha, hb, toLLVMVal, LLVM.and, LLVM.and?,
      flagsOverflow]

theorem stepInstr_or_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.or_ dst w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w (LLVM.or xa xb { disjoint := false }))) := by
  rcases xa with ⟨none | va⟩ <;> rcases xb with ⟨none | vb⟩ <;>
    simp [stepInstr, stepInstrWith, binResult, ha, hb, toLLVMVal, LLVM.or, LLVM.or?,
      flagsOverflow]

theorem stepInstr_xor_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.xor dst w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w (LLVM.xor xa xb))) := by
  rcases xa with ⟨none | va⟩ <;> rcases xb with ⟨none | vb⟩ <;>
    simp [stepInstr, stepInstrWith, binResult, ha, hb, toLLVMVal, LLVM.xor, LLVM.xor?,
      flagsOverflow]

theorem stepInstr_shl_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (flags : OverflowFlags) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.shl dst flags w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w (LLVM.shl xa xb (toNoWrapFlags flags)))) := by
  rcases xa with ⟨none | va⟩
  · rcases xb with ⟨none | vb⟩ <;>
      simp [stepInstr, stepInstrWith, shiftResult, ha, hb, toLLVMVal, LLVM.shl]
  · rcases xb with ⟨none | vb⟩
    · simp [stepInstr, stepInstrWith, shiftResult, ha, hb, toLLVMVal, LLVM.shl]
    · simp only [intW_mk_some] at ha hb ⊢
      have h_ge_iff : BitVec.ofNat w.bits w.bits ≤ vb ↔ w.bits ≤ vb.toNat := by
        have hw_lt : w.bits < 2 ^ w.bits := by
          have : ∀ k : Nat, k < 2 ^ k := fun k => by
            induction k with
            | zero => decide
            | succ m ihm => simp [Nat.pow_succ]; omega
          exact this w.bits
        simp [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]
      by_cases h_over : w.bits ≤ vb.toNat
      · have h_bv_ge : BitVec.ofNat w.bits w.bits ≤ vb := h_ge_iff.mpr h_over
        have h_shl? : LLVM.shl? va vb = .poison := by
          unfold LLVM.shl?
          change (if BitVec.ofNat w.bits w.bits ≤ vb then PoisonOr.poison else PoisonOr.value (va <<< vb)) = PoisonOr.poison
          simp [h_bv_ge]
        have h_mlir : LLVM.shl (.value va) (.value vb) (toNoWrapFlags flags) = .poison := by
          simp only [LLVM.shl, intW_bind_value, h_shl?, ite_self]
        cases flags <;>
          simp [stepInstr, stepInstrWith, shiftResult, ha, hb, toLLVMVal, h_mlir, h_over]
      · have h_lt : vb.toNat < w.bits := Nat.lt_of_not_ge h_over
        have h_not_ge : ¬(BitVec.ofNat w.bits w.bits ≤ vb) := fun hg => h_over (h_ge_iff.mp hg)
        have h_shl? : LLVM.shl? va vb = .value (va <<< vb) := by
          unfold LLVM.shl?
          change (if BitVec.ofNat w.bits w.bits ≤ vb then PoisonOr.poison else PoisonOr.value (va <<< vb)) = PoisonOr.value (va <<< vb)
          simp [h_not_ge]
        have h_nsw := shlOverflowNSW_eq_mlir w va vb h_lt
        cases flags <;>
          by_cases h1 : (va <<< vb.toNat).sshiftRight vb.toNat = va <;>
          by_cases h2 : (va <<< vb.toNat) >>> vb.toNat = va <;>
          simp [stepInstr, stepInstrWith, shiftResult, ha, hb, toLLVMVal, toNoWrapFlags,
            LLVM.shl, h_shl?, h_over, flagsOverflow, h_nsw, shlOverflowNUW, h1, h2]

theorem stepInstr_lshr_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (exact : Bool) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.lshr dst exact w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w (LLVM.lshr xa xb { exact := exact }))) := by
  rcases xa with ⟨none | va⟩
  · rcases xb with ⟨none | vb⟩ <;>
      simp [stepInstr, stepInstrWith, shiftResult, ha, hb, toLLVMVal, LLVM.lshr]
  · rcases xb with ⟨none | vb⟩
    · simp [stepInstr, stepInstrWith, shiftResult, ha, hb, toLLVMVal, LLVM.lshr]
    · simp only [intW_mk_some] at ha hb ⊢
      have h_ge_iff : BitVec.ofNat w.bits w.bits ≤ vb ↔ w.bits ≤ vb.toNat := by
        have hw_lt : w.bits < 2 ^ w.bits := by
          have : ∀ k : Nat, k < 2 ^ k := fun k => by
            induction k with
            | zero => decide
            | succ m ihm => simp [Nat.pow_succ]; omega
          exact this w.bits
        simp [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]
      by_cases h_over : w.bits ≤ vb.toNat
      · have h_bv_ge : BitVec.ofNat w.bits w.bits ≤ vb := h_ge_iff.mpr h_over
        have h_lshr? : LLVM.lshr? va vb = .poison := by
          unfold LLVM.lshr?
          change (if BitVec.ofNat w.bits w.bits ≤ vb then PoisonOr.poison else PoisonOr.value (va >>> vb)) = PoisonOr.poison
          simp [h_bv_ge]
        have h_mlir : LLVM.lshr (.value va) (.value vb) { exact := exact } = .poison := by
          simp only [LLVM.lshr, intW_bind_value, h_lshr?, ite_self]
        cases exact <;>
          simp [stepInstr, stepInstrWith, shiftResult, ha, hb, toLLVMVal, h_mlir, h_over]
      · have h_lt : vb.toNat < w.bits := Nat.lt_of_not_ge h_over
        have h_not_ge : ¬(BitVec.ofNat w.bits w.bits ≤ vb) := fun hg => h_over (h_ge_iff.mp hg)
        have h_lshr? : LLVM.lshr? va vb = .value (va >>> vb) := by
          unfold LLVM.lshr?
          change (if BitVec.ofNat w.bits w.bits ≤ vb then PoisonOr.poison else PoisonOr.value (va >>> vb)) = PoisonOr.value (va >>> vb)
          simp [h_not_ge]
        have h_ex := shiftedOut_iff_ushift_roundtrip w va vb h_lt
        cases exact <;>
          by_cases hrt : (va >>> vb.toNat) <<< vb.toNat = va <;>
          simp [stepInstr, stepInstrWith, shiftResult, ha, hb, toLLVMVal,
            LLVM.lshr, h_lshr?, h_over, flagsOverflow, h_ex, hrt]

theorem stepInstr_ashr_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (exact : Bool) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.ashr dst exact w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w (LLVM.ashr xa xb { exact := exact }))) := by
  rcases xa with ⟨none | va⟩
  · rcases xb with ⟨none | vb⟩ <;>
      simp [stepInstr, stepInstrWith, shiftResult, ha, hb, toLLVMVal, LLVM.ashr]
  · rcases xb with ⟨none | vb⟩
    · simp [stepInstr, stepInstrWith, shiftResult, ha, hb, toLLVMVal, LLVM.ashr]
    · simp only [intW_mk_some] at ha hb ⊢
      have h_ge_iff : BitVec.ofNat w.bits w.bits ≤ vb ↔ w.bits ≤ vb.toNat := by
        have hw_lt : w.bits < 2 ^ w.bits := by
          have : ∀ k : Nat, k < 2 ^ k := fun k => by
            induction k with
            | zero => decide
            | succ m ihm => simp [Nat.pow_succ]; omega
          exact this w.bits
        simp [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]
      by_cases h_over : w.bits ≤ vb.toNat
      · have h_bv_ge : BitVec.ofNat w.bits w.bits ≤ vb := h_ge_iff.mpr h_over
        have h_ashr? : LLVM.ashr? va vb = .poison := by
          unfold LLVM.ashr?
          change (if BitVec.ofNat w.bits w.bits ≤ vb then PoisonOr.poison else PoisonOr.value (va.sshiftRight' vb)) = PoisonOr.poison
          simp [h_bv_ge]
        have h_mlir : LLVM.ashr (.value va) (.value vb) { exact := exact } = .poison := by
          simp only [LLVM.ashr, intW_bind_value, h_ashr?, ite_self]
        cases exact <;>
          simp [stepInstr, stepInstrWith, shiftResult, ha, hb, toLLVMVal, h_mlir, h_over]
      · have h_lt : vb.toNat < w.bits := Nat.lt_of_not_ge h_over
        have h_not_ge : ¬(BitVec.ofNat w.bits w.bits ≤ vb) := fun hg => h_over (h_ge_iff.mp hg)
        have h_ashr? : LLVM.ashr? va vb = .value (va.sshiftRight vb.toNat) := by
          unfold LLVM.ashr?
          change (if BitVec.ofNat w.bits w.bits ≤ vb then PoisonOr.poison else PoisonOr.value (va.sshiftRight' vb)) = PoisonOr.value (va.sshiftRight vb.toNat)
          simp [h_not_ge, BitVec.sshiftRight_eq']
        have h_ex := shiftedOut_iff_ushift_roundtrip w va vb h_lt
        cases exact <;>
          by_cases hrt : (va >>> vb.toNat) <<< vb.toNat = va <;>
          simp [stepInstr, stepInstrWith, shiftResult, ha, hb, toLLVMVal,
            LLVM.ashr, h_ashr?, h_over, flagsOverflow, h_ex, hrt]

theorem stepInstr_icmp_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (pred : ICmpPred) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.icmp dst pred (.int w) aOp bOp) =
      .inr (bindReg st dst (toLLVMVal .i1 (LLVM.icmp (toIntPred pred) xa xb))) := by
  rcases xa with ⟨none | va⟩
  · rcases xb with ⟨none | vb⟩ <;>
      simp [stepInstr, stepInstrWith, ha, hb, toLLVMVal, LLVM.icmp]
  · rcases xb with ⟨none | vb⟩
    · simp [stepInstr, stepInstrWith, ha, hb, toLLVMVal, LLVM.icmp]
    · simp only [intW_mk_some] at ha hb ⊢
      simp only [stepInstr, stepInstrWith, ha, hb, toLLVMVal, LLVM.icmp, LLVM.icmp?,
        intW_bind_value, icmpEval_eq_mlir, ↓reduceDIte]
      cases LLVM.icmp' (toIntPred pred) va vb <;> rfl

theorem stepInstr_select_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (condOp : Operand) (w : IntWidth) (tOp eOp : Operand)
    (xc : LLVM.IntW 1) (xt xe : LLVM.IntW w.bits)
    (hc : evalOperand st condOp = toLLVMVal .i1 xc)
    (ht : evalTypedOperand st (.int w) tOp = toLLVMVal w xt)
    (he : evalTypedOperand st (.int w) eOp = toLLVMVal w xe) :
    stepInstr mod_ fuel st (.select dst condOp (.int w) tOp eOp) =
      .inr (bindReg st dst (toLLVMVal w (LLVM.select xc xt xe))) := by
  rcases xc with ⟨none | c⟩
  · simp [stepInstr, stepInstrWith, hc, toLLVMVal, LLVM.select]
  · simp only [intW_mk_some] at hc ⊢
    by_cases hc1 : c = 1#1
    · subst hc1
      simp [stepInstr, stepInstrWith, hc, ht, toLLVMVal, LLVM.select]
    · simp [stepInstr, stepInstrWith, hc, he, hc1, toLLVMVal, LLVM.select]

theorem stepInstr_zext_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (srcW dstW : IntWidth) (op : Operand)
    (x : LLVM.IntW srcW.bits)
    (h_le : srcW.bits ≤ dstW.bits)
    (hx : evalOperand st op = toLLVMVal srcW x) :
    stepInstr mod_ fuel st (.zext dst srcW op dstW) =
      .inr (bindReg st dst (toLLVMVal dstW (LLVM.zext dstW.bits x { nneg := false }))) := by
  rcases x with ⟨none | v⟩ <;>
    simp [stepInstr, stepInstrWith, hx, h_le, toLLVMVal, LLVM.zext, LLVM.zext?]

theorem stepInstr_sext_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (srcW dstW : IntWidth) (op : Operand)
    (x : LLVM.IntW srcW.bits)
    (h_le : srcW.bits ≤ dstW.bits)
    (hx : evalOperand st op = toLLVMVal srcW x) :
    stepInstr mod_ fuel st (.sext dst srcW op dstW) =
      .inr (bindReg st dst (toLLVMVal dstW (LLVM.sext dstW.bits x))) := by
  rcases x with ⟨none | v⟩ <;>
    simp [stepInstr, stepInstrWith, hx, h_le, toLLVMVal, LLVM.sext, LLVM.sext?]

theorem stepInstr_trunc_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (srcW dstW : IntWidth) (op : Operand)
    (x : LLVM.IntW srcW.bits)
    (h_le : dstW.bits ≤ srcW.bits)
    (hx : evalOperand st op = toLLVMVal srcW x) :
    stepInstr mod_ fuel st (.trunc dst srcW op dstW) =
      .inr (bindReg st dst (toLLVMVal dstW (LLVM.trunc dstW.bits x { nsw := false, nuw := false }))) := by
  rcases x with ⟨none | v⟩ <;>
    simp [stepInstr, stepInstrWith, hx, h_le, toLLVMVal, LLVM.trunc, LLVM.trunc?]

/-! ## Exact UB-vs-Poison Boundary for Division and Remainder -/

/-- `udiv`: `LLVMAst.stepInstr` raises `.ub` iff divisor is poison or `0`, and otherwise coincides
bit-for-bit with `opencompl/lean-mlir`'s `LLVM.udiv`. -/
theorem stepInstr_udiv_ub_or_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (exact : Bool) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    match xb with
    | .poison =>
      stepInstr mod_ fuel st (.udiv dst exact w aOp bOp) = .inl (.ub "division by poison")
    | .value vb =>
      if vb = 0#w.bits then
        stepInstr mod_ fuel st (.udiv dst exact w aOp bOp) = .inl (.ub "division by zero")
      else
        stepInstr mod_ fuel st (.udiv dst exact w aOp bOp) =
          .inr (bindReg st dst (toLLVMVal w (LLVM.udiv xa (.value vb) { exact := exact }))) := by
  rcases xb with ⟨none | vb⟩
  · simp [stepInstr, stepInstrWith, divOrRem, hb, toLLVMVal]
  · simp only [intW_mk_some] at hb ⊢
    by_cases h0 : vb = 0#w.bits
    · subst h0
      simp [stepInstr, stepInstrWith, divOrRem, hb, toLLVMVal]
    · simp only [h0, ↓reduceIte]
      rcases xa with ⟨none | va⟩
      · simp [stepInstr, stepInstrWith, divOrRem, ha, hb, h0, toLLVMVal, LLVM.udiv]
      · simp only [intW_mk_some] at ha ⊢
        have h_udiv? : LLVM.udiv? va vb = .value (va / vb) := by
          unfold LLVM.udiv?
          change (if vb = 0#w.bits then PoisonOr.poison else PoisonOr.value (va / vb)) = PoisonOr.value (va / vb)
          simp [h0]
        cases exact <;>
          by_cases hm : va % vb = 0#w.bits <;>
          simp [stepInstr, stepInstrWith, divOrRem, ha, hb, h0, toLLVMVal,
            LLVM.udiv, h_udiv?, BitVec.umod_eq, hm]

/-- `urem`: `LLVMAst.stepInstr` raises `.ub` iff divisor is poison or `0`, and otherwise coincides
bit-for-bit with `opencompl/lean-mlir`'s `LLVM.urem`. -/
theorem stepInstr_urem_ub_or_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    match xb with
    | .poison =>
      stepInstr mod_ fuel st (.urem dst w aOp bOp) = .inl (.ub "division by poison")
    | .value vb =>
      if vb = 0#w.bits then
        stepInstr mod_ fuel st (.urem dst w aOp bOp) = .inl (.ub "division by zero")
      else
        stepInstr mod_ fuel st (.urem dst w aOp bOp) =
          .inr (bindReg st dst (toLLVMVal w (LLVM.urem xa (.value vb)))) := by
  rcases xb with ⟨none | vb⟩
  · simp [stepInstr, stepInstrWith, divOrRem, hb, toLLVMVal]
  · simp only [intW_mk_some] at hb ⊢
    by_cases h0 : vb = 0#w.bits
    · subst h0
      simp [stepInstr, stepInstrWith, divOrRem, hb, toLLVMVal]
    · simp only [h0, ↓reduceIte]
      rcases xa with ⟨none | va⟩ <;>
        simp [stepInstr, stepInstrWith, divOrRem, ha, hb, h0, toLLVMVal, LLVM.urem, LLVM.urem?]

private theorem smod_eq_zero_iff_srem_eq_zero {n : Nat} (a b : BitVec n) :
    (a.smod b = 0#n) ↔ (a.srem b = 0#n) := by
  rw [← BitVec.toInt_inj, ← BitVec.toInt_inj, BitVec.toInt_smod, BitVec.toInt_srem,
    BitVec.toInt_zero, ← Int.dvd_iff_fmod_eq_zero, ← Int.dvd_iff_tmod_eq_zero]

/-- `sdiv` on concrete widths `w ≠ .i1` without UB (`vb ≠ 0` and not `INT_MIN / -1`) coincides
bit-for-bit with `opencompl/lean-mlir`'s `LLVM.sdiv`. -/
theorem stepInstr_sdiv_bisim_of_non_ub (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (exact : Bool) (w : IntWidth) (aOp bOp : Operand)
    (va vb : BitVec w.bits)
    (hw1 : w.bits ≠ 1)
    (hb0 : vb ≠ 0#w.bits)
    (hno_ov : sdivOverflow w va vb = false)
    (ha : evalOperand st aOp = .bits w va)
    (hb : evalOperand st bOp = .bits w vb) :
    stepInstr mod_ fuel st (.sdiv dst exact w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w (LLVM.sdiv (.value va) (.value vb) { exact := exact }))) := by
  have hpos : 0 < w.bits := w.bits_pos
  have hw2 : 1 < w.bits := by omega
  have h_intMin : ¬(va = BitVec.intMin w.bits ∧ vb = -1) := by
    rintro ⟨hmin, hm1⟩
    unfold sdivOverflow at hno_ov
    rw [bvSigned_eq_toInt, bvSigned_eq_toInt] at hno_ov
    have hva_int : va.toInt = -((2 : Int) ^ (w.bits - 1)) := by
      subst hmin
      have h2w : 2 ^ w.bits = 2 * 2 ^ (w.bits - 1) := two_pow_eq_two_mul_pred w.bits hpos
      have hp : 0 < 2 ^ (w.bits - 1) := two_pow_pos_nat (w.bits - 1)
      have hlt : 2 ^ (w.bits - 1) < 2 ^ w.bits := by omega
      rw [BitVec.toInt_intMin, Nat.mod_eq_of_lt hlt, int_two_pow_eq_natCast]
    have hvb_int : vb.toInt = -1 := by
      subst hm1
      have h2w : 2 ^ w.bits = 2 * 2 ^ (w.bits - 1) := two_pow_eq_two_mul_pred w.bits hpos
      have hp1 : 1 < 2 ^ (w.bits - 1) := by
        cases hwb : w.bits - 1 with
        | zero => omega
        | succ k =>
          have := two_pow_pos_nat k
          simp [Nat.pow_succ]; omega
      have hone : (1 : BitVec w.bits).toInt = 1 := BitVec.toInt_one hw2
      rw [BitVec.toInt_neg, hone]
      apply Int.bmod_eq_of_le <;> omega
    simp [hva_int, hvb_int] at hno_ov
  have h_sdiv? : LLVM.sdiv? va vb = .value (va.sdiv vb) := by
    unfold LLVM.sdiv?
    have hcond : (vb == 0 || (w.bits != 1 && va == BitVec.intMin w.bits && vb == -1)) = false := by
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, Bool.and_eq_false_iff,
        bne_eq_false_iff_eq]
      refine ⟨hb0, ?_⟩
      by_cases h1 : va = BitVec.intMin w.bits
      · right; intro h2; exact h_intMin ⟨h1, h2⟩
      · left; right; exact h1
    rw [hcond]
    rfl
  have h_smod_iff : (va.smod vb = 0#w.bits) ↔ (va.srem vb = 0#w.bits) :=
    smod_eq_zero_iff_srem_eq_zero va vb
  cases exact <;>
    by_cases hsr : va.srem vb = 0#w.bits <;>
    simp [stepInstr, stepInstrWith, divOrRem, ha, hb, hb0, hno_ov, toLLVMVal,
      LLVM.sdiv, h_sdiv?, bvSDiv_eq_sdiv, bvSRem_eq_srem, h_smod_iff, hsr]

/-! ## Dialect-Level Bridge (`InstCombine.Op.denote` over `LLVM.Op` / `MOp 0`) -/

/-- Direct bridge from `LLVMAst.stepInstr` to `InstCombine.Op.denote` in `opencompl/lean-mlir`'s
concrete `LLVM` dialect (`φ = 0`). -/
theorem stepInstr_add_eq_op_denote (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (flags : OverflowFlags) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.add dst flags w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w
        (InstCombine.Op.denote (InstCombine.LLVM.Op.add w.bits (toNoWrapFlags flags))
          (HVector.cons xa (HVector.cons xb HVector.nil))))) := by
  rw [stepInstr_add_bisim mod_ fuel st dst flags w aOp bOp xa xb ha hb]
  rfl

theorem stepInstr_icmp_eq_op_denote (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (pred : ICmpPred) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.icmp dst pred (.int w) aOp bOp) =
      .inr (bindReg st dst (toLLVMVal .i1
        (InstCombine.Op.denote (InstCombine.LLVM.Op.icmp (toIntPred pred) w.bits)
          (HVector.cons xa (HVector.cons xb HVector.nil))))) := by
  rw [stepInstr_icmp_bisim mod_ fuel st dst pred w aOp bOp xa xb ha hb]
  rfl

theorem stepInstr_select_eq_op_denote (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (condOp : Operand) (w : IntWidth) (tOp eOp : Operand)
    (xc : LLVM.IntW 1) (xt xe : LLVM.IntW w.bits)
    (hc : evalOperand st condOp = toLLVMVal .i1 xc)
    (ht : evalTypedOperand st (.int w) tOp = toLLVMVal w xt)
    (he : evalTypedOperand st (.int w) eOp = toLLVMVal w xe) :
    stepInstr mod_ fuel st (.select dst condOp (.int w) tOp eOp) =
      .inr (bindReg st dst (toLLVMVal w
        (InstCombine.Op.denote (InstCombine.LLVM.Op.select w.bits)
          (HVector.cons xc (HVector.cons xt (HVector.cons xe HVector.nil)))))) := by
  rw [stepInstr_select_bisim mod_ fuel st dst condOp w tOp eOp xc xt xe hc ht he]
  rfl

/-! ## Compositional Straight-Line Instruction-List Composition (`execInstrs`) -/

/-- Inductive straight-line SSA instruction-step trace composing per-instruction `LLVMAst.stepInstr`
bisimulation steps into `LLVMAst.execInstrs` (pure SSA straight-line blocks; CFG terminators, phi
wiring, and linear memory remain covered by Stages 2A/2B and `LLVMAst.Proofs`). -/
inductive StraightLineBisim (mod_ : LLVMModule) (fuel : Nat) :
    ExecState → List LLVMInstr → ExecState → Prop where
  | nil (st : ExecState) :
      StraightLineBisim mod_ fuel st [] st
  | cons {st st1 st2 : ExecState} {ins : LLVMInstr} {rest : List LLVMInstr}
      (h_step : stepInstr mod_ fuel st ins = .inr st1)
      (h_tail : StraightLineBisim mod_ fuel st1 rest st2) :
      StraightLineBisim mod_ fuel st (ins :: rest) st2

theorem execInstrs_of_straightLineBisim {mod_ : LLVMModule} {fuel : Nat}
    {st st' : ExecState} {is : List LLVMInstr}
    (h : StraightLineBisim mod_ fuel st is st') :
    execInstrs mod_ fuel st is = .inr st' := by
  induction h with
  | nil st => rfl
  | cons h_step _ ih =>
    unfold execInstrs at *
    simp only [execInstrsWith]
    unfold stepInstr at h_step
    rw [h_step]
    exact ih

end LeanMLIRBridge
