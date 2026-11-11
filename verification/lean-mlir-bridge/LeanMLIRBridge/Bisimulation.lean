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
private theorem sdivOverflow_eq_false_not_intMin_neg_one (w : IntWidth) (va vb : BitVec w.bits)
    (hw1 : w.bits ≠ 1) (hno_ov : sdivOverflow w va vb = false) :
    ¬(va = BitVec.intMin w.bits ∧ vb = -1) := by
  have hpos : 0 < w.bits := w.bits_pos
  have hw2 : 1 < w.bits := by omega
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

private theorem sdiv_mlir_guard_false_of_non_ub (w : IntWidth) (va vb : BitVec w.bits)
    (hw1 : w.bits ≠ 1) (hb0 : vb ≠ 0#w.bits) (hno_ov : sdivOverflow w va vb = false) :
    (vb == 0 || (w.bits != 1 && va == BitVec.intMin w.bits && vb == -1)) = false := by
  have h_intMin := sdivOverflow_eq_false_not_intMin_neg_one w va vb hw1 hno_ov
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, Bool.and_eq_false_iff,
    bne_eq_false_iff_eq]
  refine ⟨hb0, ?_⟩
  by_cases h1 : va = BitVec.intMin w.bits
  · right; intro h2; exact h_intMin ⟨h1, h2⟩
  · left; right; exact h1

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
  have h_sdiv? : LLVM.sdiv? va vb = .value (va.sdiv vb) := by
    unfold LLVM.sdiv?
    rw [sdiv_mlir_guard_false_of_non_ub w va vb hw1 hb0 hno_ov]
    rfl
  have h_smod_iff : (va.smod vb = 0#w.bits) ↔ (va.srem vb = 0#w.bits) :=
    smod_eq_zero_iff_srem_eq_zero va vb
  cases exact <;>
    by_cases hsr : va.srem vb = 0#w.bits <;>
    simp [stepInstr, stepInstrWith, divOrRem, ha, hb, hb0, hno_ov, toLLVMVal,
      LLVM.sdiv, h_sdiv?, bvSDiv_eq_sdiv, bvSRem_eq_srem, h_smod_iff, hsr]

/-- `srem` on concrete widths `w ≠ .i1` without UB (`vb ≠ 0` and not `INT_MIN / -1`) coincides
bit-for-bit with `opencompl/lean-mlir`'s `LLVM.srem`. -/
theorem stepInstr_srem_bisim_of_non_ub (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (w : IntWidth) (aOp bOp : Operand)
    (va vb : BitVec w.bits)
    (hw1 : w.bits ≠ 1)
    (hb0 : vb ≠ 0#w.bits)
    (hno_ov : sdivOverflow w va vb = false)
    (ha : evalOperand st aOp = .bits w va)
    (hb : evalOperand st bOp = .bits w vb) :
    stepInstr mod_ fuel st (.srem dst w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w (LLVM.srem (.value va) (.value vb)))) := by
  have h_srem? : LLVM.srem? va vb = .value (va.srem vb) := by
    unfold LLVM.srem?
    rw [sdiv_mlir_guard_false_of_non_ub w va vb hw1 hb0 hno_ov]
    rfl
  simp [stepInstr, stepInstrWith, divOrRem, ha, hb, hb0, hno_ov, toLLVMVal,
    LLVM.srem, h_srem?, bvSRem_eq_srem]

/-- At width `.i1`, `bvSigned .i1 1#1 = -1` and `-((2 : Int) ^ 0) = -1`, so `sdivOverflow .i1 va vb`
holds iff both operands are `1#1` (whereas `opencompl/lean-mlir` treats `i1` `-1 / -1` as `-1`). -/
private theorem bitvec_i1_cases (v : BitVec (IntWidth.i1.bits)) : v = 0#1 ∨ v = 1#1 := by
  rcases v with ⟨⟨n, hn⟩⟩
  change n < 2 at hn
  have : n = 0 ∨ n = 1 := by omega
  rcases this with rfl | rfl
  · left; rfl
  · right; rfl

theorem sdivOverflow_i1_iff (va vb : BitVec (IntWidth.i1.bits)) :
    sdivOverflow .i1 va vb = true ↔ va = 1#1 ∧ vb = 1#1 := by
  rcases bitvec_i1_cases va with rfl | rfl <;>
    rcases bitvec_i1_cases vb with rfl | rfl <;> decide

/-- Explicit `.i1` discrepancy characterization: for `va = 1#1, vb = 1#1`, `LLVMAst.stepInstr`
raises `.ub "signed division overflow"` on both `sdiv` and `srem`, while `opencompl/lean-mlir`
evaluates `LLVM.sdiv` to `.value 1#1` and `LLVM.srem` to `.value 0#1`. -/
theorem stepInstr_sdiv_srem_i1_allOnes_ub (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (exact : Bool) (aOp bOp : Operand)
    (ha : evalOperand st aOp = .bits .i1 1#1)
    (hb : evalOperand st bOp = .bits .i1 1#1) :
    stepInstr mod_ fuel st (.sdiv dst exact .i1 aOp bOp) = .inl (.ub "signed division overflow") ∧
    stepInstr mod_ fuel st (.srem dst .i1 aOp bOp) = .inl (.ub "signed division overflow") ∧
    LLVM.sdiv (.value 1#1) (.value 1#1) { exact := exact } = .value 1#1 ∧
    LLVM.srem (.value 1#1) (.value 1#1) = .value 0#1 := by
  have hov : sdivOverflow .i1 1#1 1#1 = true := by decide
  have hbeq0 : ((1#1 : BitVec (IntWidth.i1.bits)) == 0#(IntWidth.i1.bits)) = false := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [stepInstr, stepInstrWith, divOrRem, ha, hb, hbeq0, hov]
  · simp [stepInstr, stepInstrWith, divOrRem, ha, hb, hbeq0, hov]
  · cases exact <;> decide
  · decide

/-- `sdiv`: complete exact UB-vs-poison boundary across all `xa xb : LLVM.IntW w.bits`, `exact : Bool`,
and all widths `w : IntWidth` (including `w = .i1`). -/
theorem stepInstr_sdiv_ub_or_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (exact : Bool) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    match xb with
    | .poison =>
      stepInstr mod_ fuel st (.sdiv dst exact w aOp bOp) = .inl (.ub "division by poison")
    | .value vb =>
      if vb = 0#w.bits then
        stepInstr mod_ fuel st (.sdiv dst exact w aOp bOp) = .inl (.ub "division by zero")
      else
        match xa with
        | .poison =>
          if bvSigned w vb == -1 then
            stepInstr mod_ fuel st (.sdiv dst exact w aOp bOp) =
              .inl (.ub "signed division overflow")
          else
            stepInstr mod_ fuel st (.sdiv dst exact w aOp bOp) =
              .inr (bindReg st dst (toLLVMVal w (LLVM.sdiv .poison (.value vb) { exact := exact })))
        | .value va =>
          if sdivOverflow w va vb then
            stepInstr mod_ fuel st (.sdiv dst exact w aOp bOp) =
              .inl (.ub "signed division overflow")
          else
            stepInstr mod_ fuel st (.sdiv dst exact w aOp bOp) =
              .inr (bindReg st dst (toLLVMVal w (LLVM.sdiv (.value va) (.value vb) { exact := exact }))) := by
  rcases xb with ⟨none | vb⟩
  · simp [stepInstr, stepInstrWith, divOrRem, hb, toLLVMVal]
  · simp only [intW_mk_some] at hb ⊢
    by_cases h0 : vb = 0#w.bits
    · subst h0
      simp [stepInstr, stepInstrWith, divOrRem, hb, toLLVMVal]
    · simp only [h0, ↓reduceIte]
      rcases xa with ⟨none | va⟩
      · simp only [intW_mk_none] at ha ⊢
        by_cases hbm1 : (bvSigned w vb == -1) = true
        · simp [stepInstr, stepInstrWith, divOrRem, ha, hb, h0, hbm1, toLLVMVal]
        · simp [stepInstr, stepInstrWith, divOrRem, ha, hb, h0, hbm1, toLLVMVal, LLVM.sdiv]
      · simp only [intW_mk_some] at ha ⊢
        by_cases hov : sdivOverflow w va vb = true
        · simp [stepInstr, stepInstrWith, divOrRem, ha, hb, h0, hov, toLLVMVal]
        · simp only [Bool.not_eq_true] at hov
          simp only [hov, Bool.false_eq_true, ↓reduceIte]
          by_cases hw1 : w.bits = 1
          · have hw_i1 : w = .i1 := by cases w <;> simp_all [IntWidth.bits]
            subst hw_i1
            rcases bitvec_i1_cases vb with rfl | rfl
            · exact False.elim (h0 rfl)
            · rcases bitvec_i1_cases va with rfl | rfl
              · have hbeq0 : ((1#1 : BitVec (IntWidth.i1.bits)) == 0#(IntWidth.i1.bits)) = false := by decide
                have hlhs : stepInstr mod_ fuel st (.sdiv dst exact .i1 aOp bOp) =
                    .inr (bindReg st dst (.bits .i1 0#1)) := by
                  cases exact <;>
                    simp [stepInstr, stepInstrWith, divOrRem, ha, hb, toLLVMVal, hbeq0, hov] <;> rfl
                have hrhs : LLVM.sdiv (.value (0#1 : BitVec (IntWidth.i1.bits))) (.value 1#1)
                    { exact := exact } = .value 0#1 := by
                  cases exact <;> decide
                rw [hlhs, hrhs]
                rfl
              · have hov1 : sdivOverflow .i1 1#1 1#1 = true := by decide
                rw [hov] at hov1
                cases hov1
          · exact stepInstr_sdiv_bisim_of_non_ub mod_ fuel st dst exact w aOp bOp va vb
              hw1 h0 hov ha hb

/-- `srem`: complete exact UB-vs-poison boundary across all `xa xb : LLVM.IntW w.bits`
and all widths `w : IntWidth` (including `w = .i1`). -/
theorem stepInstr_srem_ub_or_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    match xb with
    | .poison =>
      stepInstr mod_ fuel st (.srem dst w aOp bOp) = .inl (.ub "division by poison")
    | .value vb =>
      if vb = 0#w.bits then
        stepInstr mod_ fuel st (.srem dst w aOp bOp) = .inl (.ub "division by zero")
      else
        match xa with
        | .poison =>
          if bvSigned w vb == -1 then
            stepInstr mod_ fuel st (.srem dst w aOp bOp) =
              .inl (.ub "signed division overflow")
          else
            stepInstr mod_ fuel st (.srem dst w aOp bOp) =
              .inr (bindReg st dst (toLLVMVal w (LLVM.srem .poison (.value vb))))
        | .value va =>
          if sdivOverflow w va vb then
            stepInstr mod_ fuel st (.srem dst w aOp bOp) =
              .inl (.ub "signed division overflow")
          else
            stepInstr mod_ fuel st (.srem dst w aOp bOp) =
              .inr (bindReg st dst (toLLVMVal w (LLVM.srem (.value va) (.value vb)))) := by
  rcases xb with ⟨none | vb⟩
  · simp [stepInstr, stepInstrWith, divOrRem, hb, toLLVMVal]
  · simp only [intW_mk_some] at hb ⊢
    by_cases h0 : vb = 0#w.bits
    · subst h0
      simp [stepInstr, stepInstrWith, divOrRem, hb, toLLVMVal]
    · simp only [h0, ↓reduceIte]
      rcases xa with ⟨none | va⟩
      · simp only [intW_mk_none] at ha ⊢
        by_cases hbm1 : (bvSigned w vb == -1) = true
        · simp [stepInstr, stepInstrWith, divOrRem, ha, hb, h0, hbm1, toLLVMVal]
        · simp [stepInstr, stepInstrWith, divOrRem, ha, hb, h0, hbm1, toLLVMVal, LLVM.srem]
      · simp only [intW_mk_some] at ha ⊢
        by_cases hov : sdivOverflow w va vb = true
        · simp [stepInstr, stepInstrWith, divOrRem, ha, hb, h0, hov, toLLVMVal]
        · simp only [Bool.not_eq_true] at hov
          simp only [hov, Bool.false_eq_true, ↓reduceIte]
          by_cases hw1 : w.bits = 1
          · have hw_i1 : w = .i1 := by cases w <;> simp_all [IntWidth.bits]
            subst hw_i1
            rcases bitvec_i1_cases vb with rfl | rfl
            · exact False.elim (h0 rfl)
            · rcases bitvec_i1_cases va with rfl | rfl
              · have hbeq0 : ((1#1 : BitVec (IntWidth.i1.bits)) == 0#(IntWidth.i1.bits)) = false := by decide
                have hlhs : stepInstr mod_ fuel st (.srem dst .i1 aOp bOp) =
                    .inr (bindReg st dst (.bits .i1 0#1)) := by
                  simp [stepInstr, stepInstrWith, divOrRem, ha, hb, toLLVMVal, hbeq0, hov]
                  rfl
                have hrhs : LLVM.srem (.value (0#1 : BitVec (IntWidth.i1.bits))) (.value 1#1) =
                    .value 0#1 := by decide
                rw [hlhs, hrhs]
                rfl
              · have hov1 : sdivOverflow .i1 1#1 1#1 = true := by decide
                rw [hov] at hov1
                cases hov1
          · exact stepInstr_srem_bisim_of_non_ub mod_ fuel st dst w aOp bOp va vb
              hw1 h0 hov ha hb

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

theorem stepInstr_sub_eq_op_denote (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (flags : OverflowFlags) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.sub dst flags w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w
        (InstCombine.Op.denote (InstCombine.LLVM.Op.sub w.bits (toNoWrapFlags flags))
          (HVector.cons xa (HVector.cons xb HVector.nil))))) := by
  rw [stepInstr_sub_bisim mod_ fuel st dst flags w aOp bOp xa xb ha hb]
  rfl

theorem stepInstr_mul_eq_op_denote (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (flags : OverflowFlags) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.mul dst flags w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w
        (InstCombine.Op.denote (InstCombine.LLVM.Op.mul w.bits (toNoWrapFlags flags))
          (HVector.cons xa (HVector.cons xb HVector.nil))))) := by
  rw [stepInstr_mul_bisim mod_ fuel st dst flags w aOp bOp xa xb ha hb]
  rfl

theorem stepInstr_and_eq_op_denote (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.and_ dst w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w
        (InstCombine.Op.denote (InstCombine.LLVM.Op.and w.bits)
          (HVector.cons xa (HVector.cons xb HVector.nil))))) := by
  rw [stepInstr_and_bisim mod_ fuel st dst w aOp bOp xa xb ha hb]
  rfl

theorem stepInstr_or_eq_op_denote (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.or_ dst w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w
        (InstCombine.Op.denote (InstCombine.LLVM.Op.or w.bits { disjoint := false })
          (HVector.cons xa (HVector.cons xb HVector.nil))))) := by
  rw [stepInstr_or_bisim mod_ fuel st dst w aOp bOp xa xb ha hb]
  rfl

theorem stepInstr_xor_eq_op_denote (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.xor dst w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w
        (InstCombine.Op.denote (InstCombine.LLVM.Op.xor w.bits)
          (HVector.cons xa (HVector.cons xb HVector.nil))))) := by
  rw [stepInstr_xor_bisim mod_ fuel st dst w aOp bOp xa xb ha hb]
  rfl

theorem stepInstr_shl_eq_op_denote (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (flags : OverflowFlags) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.shl dst flags w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w
        (InstCombine.Op.denote (InstCombine.LLVM.Op.shl w.bits (toNoWrapFlags flags))
          (HVector.cons xa (HVector.cons xb HVector.nil))))) := by
  rw [stepInstr_shl_bisim mod_ fuel st dst flags w aOp bOp xa xb ha hb]
  rfl

theorem stepInstr_lshr_eq_op_denote (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (exact : Bool) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.lshr dst exact w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w
        (InstCombine.Op.denote (InstCombine.LLVM.Op.lshr w.bits { exact := exact })
          (HVector.cons xa (HVector.cons xb HVector.nil))))) := by
  rw [stepInstr_lshr_bisim mod_ fuel st dst exact w aOp bOp xa xb ha hb]
  rfl

theorem stepInstr_ashr_eq_op_denote (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (exact : Bool) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.ashr dst exact w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w
        (InstCombine.Op.denote (InstCombine.LLVM.Op.ashr w.bits { exact := exact })
          (HVector.cons xa (HVector.cons xb HVector.nil))))) := by
  rw [stepInstr_ashr_bisim mod_ fuel st dst exact w aOp bOp xa xb ha hb]
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

theorem stepInstr_zext_eq_op_denote (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (srcW dstW : IntWidth) (op : Operand)
    (x : LLVM.IntW srcW.bits)
    (h_le : srcW.bits ≤ dstW.bits)
    (hx : evalOperand st op = toLLVMVal srcW x) :
    stepInstr mod_ fuel st (.zext dst srcW op dstW) =
      .inr (bindReg st dst (toLLVMVal dstW
        (InstCombine.Op.denote (InstCombine.LLVM.Op.zext srcW.bits dstW.bits { nneg := false })
          (HVector.cons x HVector.nil)))) := by
  rw [stepInstr_zext_bisim mod_ fuel st dst srcW dstW op x h_le hx]
  rfl

theorem stepInstr_sext_eq_op_denote (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (srcW dstW : IntWidth) (op : Operand)
    (x : LLVM.IntW srcW.bits)
    (h_le : srcW.bits ≤ dstW.bits)
    (hx : evalOperand st op = toLLVMVal srcW x) :
    stepInstr mod_ fuel st (.sext dst srcW op dstW) =
      .inr (bindReg st dst (toLLVMVal dstW
        (InstCombine.Op.denote (InstCombine.LLVM.Op.sext srcW.bits dstW.bits)
          (HVector.cons x HVector.nil)))) := by
  rw [stepInstr_sext_bisim mod_ fuel st dst srcW dstW op x h_le hx]
  rfl

theorem stepInstr_trunc_eq_op_denote (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (srcW dstW : IntWidth) (op : Operand)
    (x : LLVM.IntW srcW.bits)
    (h_le : dstW.bits ≤ srcW.bits)
    (hx : evalOperand st op = toLLVMVal srcW x) :
    stepInstr mod_ fuel st (.trunc dst srcW op dstW) =
      .inr (bindReg st dst (toLLVMVal dstW
        (InstCombine.Op.denote (InstCombine.LLVM.Op.trunc srcW.bits dstW.bits { nsw := false, nuw := false })
          (HVector.cons x HVector.nil)))) := by
  rw [stepInstr_trunc_bisim mod_ fuel st dst srcW dstW op x h_le hx]
  rfl

theorem stepInstr_udiv_eq_op_denote_of_nonzero (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (exact : Bool) (w : IntWidth) (aOp bOp : Operand)
    (xa : LLVM.IntW w.bits) (vb : BitVec w.bits)
    (hb0 : vb ≠ 0#w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = .bits w vb) :
    stepInstr mod_ fuel st (.udiv dst exact w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w
        (InstCombine.Op.denote (InstCombine.LLVM.Op.udiv w.bits { exact := exact })
          (HVector.cons xa (HVector.cons (.value vb) HVector.nil))))) := by
  have hb' : evalOperand st bOp = toLLVMVal w (.value vb) := hb
  have h := stepInstr_udiv_ub_or_bisim mod_ fuel st dst exact w aOp bOp xa (.value vb) ha hb'
  simp only [hb0, ↓reduceIte] at h
  exact h

theorem stepInstr_urem_eq_op_denote_of_nonzero (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (w : IntWidth) (aOp bOp : Operand)
    (xa : LLVM.IntW w.bits) (vb : BitVec w.bits)
    (hb0 : vb ≠ 0#w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = .bits w vb) :
    stepInstr mod_ fuel st (.urem dst w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w
        (InstCombine.Op.denote (InstCombine.LLVM.Op.urem w.bits)
          (HVector.cons xa (HVector.cons (.value vb) HVector.nil))))) := by
  have hb' : evalOperand st bOp = toLLVMVal w (.value vb) := hb
  have h := stepInstr_urem_ub_or_bisim mod_ fuel st dst w aOp bOp xa (.value vb) ha hb'
  simp only [hb0, ↓reduceIte] at h
  exact h

theorem stepInstr_sdiv_eq_op_denote_of_non_ub (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (exact : Bool) (w : IntWidth) (aOp bOp : Operand)
    (va vb : BitVec w.bits)
    (hw1 : w.bits ≠ 1)
    (hb0 : vb ≠ 0#w.bits)
    (hno_ov : sdivOverflow w va vb = false)
    (ha : evalOperand st aOp = .bits w va)
    (hb : evalOperand st bOp = .bits w vb) :
    stepInstr mod_ fuel st (.sdiv dst exact w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w
        (InstCombine.Op.denote (InstCombine.LLVM.Op.sdiv w.bits { exact := exact })
          (HVector.cons (.value va) (HVector.cons (.value vb) HVector.nil))))) := by
  rw [stepInstr_sdiv_bisim_of_non_ub mod_ fuel st dst exact w aOp bOp va vb hw1 hb0 hno_ov ha hb]
  rfl

theorem stepInstr_srem_eq_op_denote_of_non_ub (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (w : IntWidth) (aOp bOp : Operand)
    (va vb : BitVec w.bits)
    (hw1 : w.bits ≠ 1)
    (hb0 : vb ≠ 0#w.bits)
    (hno_ov : sdivOverflow w va vb = false)
    (ha : evalOperand st aOp = .bits w va)
    (hb : evalOperand st bOp = .bits w vb) :
    stepInstr mod_ fuel st (.srem dst w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w
        (InstCombine.Op.denote (InstCombine.LLVM.Op.srem w.bits)
          (HVector.cons (.value va) (HVector.cons (.value vb) HVector.nil))))) := by
  rw [stepInstr_srem_bisim_of_non_ub mod_ fuel st dst w aOp bOp va vb hw1 hb0 hno_ov ha hb]
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

theorem StraightLineBisim.append {mod_ : LLVMModule} {fuel : Nat}
    {st1 st2 st3 : ExecState} {is1 is2 : List LLVMInstr}
    (h1 : StraightLineBisim mod_ fuel st1 is1 st2)
    (h2 : StraightLineBisim mod_ fuel st2 is2 st3) :
    StraightLineBisim mod_ fuel st1 (is1 ++ is2) st3 := by
  induction h1 with
  | nil => exact h2
  | cons h_step _ ih => exact .cons h_step (ih h2)

theorem execInstrs_append_of_straightLineBisim {mod_ : LLVMModule} {fuel : Nat}
    {st1 st2 st3 : ExecState} {is1 is2 : List LLVMInstr}
    (h1 : StraightLineBisim mod_ fuel st1 is1 st2)
    (h2 : StraightLineBisim mod_ fuel st2 is2 st3) :
    execInstrs mod_ fuel st1 (is1 ++ is2) = .inr st3 :=
  execInstrs_of_straightLineBisim (h1.append h2)

/-! ## SSA Register-Valuation Lookup & Pure Straight-Line Frame Preservation -/

@[simp]
theorem evalOperand_reg_bindReg_same (st : ExecState) (r : RegName) (v : LLVMVal) :
    evalOperand (bindReg st r v) (.reg r) = v := by
  simp [evalOperand, lookupReg, bindReg]

@[simp]
theorem evalOperand_reg_bindReg_ne (st : ExecState) (r r' : RegName) (v : LLVMVal)
    (hne : r ≠ r') :
    evalOperand (bindReg st r' v) (.reg r) = evalOperand st (.reg r) := by
  have hbeq : (r == r') = false := beq_eq_false_iff_ne.mpr hne
  simp [evalOperand, lookupReg, bindReg, List.lookup_cons, hbeq]

@[simp]
theorem evalTypedOperand_int_reg (st : ExecState) (w : IntWidth) (r : RegName) :
    evalTypedOperand st (.int w) (.reg r) = evalOperand st (.reg r) := rfl

/-- SSA register valuation agreement between an `LLVMAst.ExecState` and an abstract valuation
`ρ : RegName → LLVMVal` on a finite live-register set `live`. -/
def RegValuationAgrees (st : ExecState) (ρ : RegName → LLVMVal) (live : List RegName) : Prop :=
  ∀ r, r ∈ live → evalOperand st (.reg r) = ρ r

theorem RegValuationAgrees.bind (st : ExecState) (ρ : RegName → LLVMVal) (live : List RegName)
    (dst : RegName) (v : LLVMVal)
    (h : RegValuationAgrees st ρ live) :
    RegValuationAgrees (bindReg st dst v) (fun r => if r = dst then v else ρ r) (dst :: live) := by
  intro r hr
  by_cases heq : r = dst
  · subst heq
    simp
  · rcases List.mem_cons.mp hr with rfl | hmem
    · exact False.elim (heq rfl)
    · simp [heq, evalOperand_reg_bindReg_ne st r dst v heq, h r hmem]

/-- Pure register-only SSA instructions (covering the entire `InstCombine.LLVM.Op` integer ALU,
shift, comparison, cast, select, and div/rem dialect fragment) never mutate linear memory,
global bindings, or predecessor block labels. -/
def isPureRegInstr : LLVMInstr → Bool
  | .add .. | .sub .. | .mul .. | .udiv .. | .sdiv .. | .urem .. | .srem ..
  | .and_ .. | .or_ .. | .xor .. | .shl .. | .lshr .. | .ashr ..
  | .icmp .. | .zext .. | .sext .. | .trunc .. | .select .. => true
  | _ => false

theorem stepInstr_pure_frame {mod_ : LLVMModule} {fuel : Nat} {st st' : ExecState}
    {ins : LLVMInstr}
    (hpure : isPureRegInstr ins = true)
    (hstep : stepInstr mod_ fuel st ins = .inr st') :
    st'.mem = st.mem ∧ st'.globals = st.globals ∧ st'.prevBlock = st.prevBlock := by
  have hbind : ∀ (dst : RegName) (v : LLVMVal),
      (.inr (bindReg st dst v) : ExecOutcome ⊕ ExecState) = .inr st' →
      st'.mem = st.mem ∧ st'.globals = st.globals ∧ st'.prevBlock = st.prevBlock := by
    intro dst v h
    injection h with h'
    subst h'
    exact ⟨rfl, rfl, rfl⟩
  have hite : ∀ (c : Prop) [Decidable c] {x y : ExecOutcome ⊕ ExecState},
      (x = .inr st' → st'.mem = st.mem ∧ st'.globals = st.globals ∧ st'.prevBlock = st.prevBlock) →
      (y = .inr st' → st'.mem = st.mem ∧ st'.globals = st.globals ∧ st'.prevBlock = st.prevBlock) →
      (if c then x else y) = .inr st' →
      st'.mem = st.mem ∧ st'.globals = st.globals ∧ st'.prevBlock = st.prevBlock := by
    intro c _ x y hx hy h
    by_cases hc : c
    · rw [if_pos hc] at h; exact hx h
    · rw [if_neg hc] at h; exact hy h
  have hub : ∀ (msg : String),
      (.inl (.ub msg) : ExecOutcome ⊕ ExecState) = .inr st' →
      st'.mem = st.mem ∧ st'.globals = st.globals ∧ st'.prevBlock = st.prevBlock := by
    intro msg h; nomatch h
  have hbin : ∀ (dst : RegName) (w : IntWidth) (fl : OverflowFlags) (a b : LLVMVal) (k : String),
      binResult dst st w fl a b k = .inr st' →
      st'.mem = st.mem ∧ st'.globals = st.globals ∧ st'.prevBlock = st.prevBlock := by
    intro dst w fl a b k h
    unfold binResult at h
    cases a with
    | poison => exact hbind _ _ h
    | ptr _ | floatBits _ _ | aggNil | aggCons _ _ =>
      cases b <;> first | exact hbind _ _ h | nomatch h
    | bits wa va =>
      cases b with
      | poison => exact hbind _ _ h
      | ptr _ | floatBits _ _ | aggNil | aggCons _ _ => nomatch h
      | bits wb vb =>
        dsimp only at h
        by_cases ha : wa = w
        · subst wa
          by_cases hb : wb = w
          · subst wb
            simp only [↓reduceDIte] at h
            exact hite _ (hbind _ _) (hbind _ _) h
          · simp [hb] at h
        · simp [ha] at h
  have hdiv : ∀ (dst : RegName) (w : IntWidth) (ex : Bool) (a b : LLVMVal) (sg ir : Bool),
      divOrRem dst st w ex a b sg ir = .inr st' →
      st'.mem = st.mem ∧ st'.globals = st.globals ∧ st'.prevBlock = st.prevBlock := by
    intro dst w ex a b sg ir h
    unfold divOrRem at h
    cases b with
    | poison | ptr _ | floatBits _ _ | aggNil | aggCons _ _ => nomatch h
    | bits wb vb =>
      dsimp only at h
      by_cases hb : wb = w
      · subst wb
        simp only [↓reduceDIte] at h
        refine hite _ (hub _) (fun h => ?_) h
        cases a with
        | ptr _ | floatBits _ _ | aggNil | aggCons _ _ => nomatch h
        | poison =>
          dsimp only at h
          exact hite _ (hub _) (hbind _ _) h
        | bits wa va =>
          dsimp only at h
          by_cases ha : wa = w
          · subst wa
            simp only [↓reduceDIte] at h
            exact hite _ (hub _) (hite _ (hbind _ _) (hbind _ _)) h
          · simp [ha] at h
      · simp [hb] at h
  have hshf : ∀ (dst : RegName) (w : IntWidth) (fl : OverflowFlags) (ex : Bool) (a b : LLVMVal) (k : String),
      shiftResult dst st w fl ex a b k = .inr st' →
      st'.mem = st.mem ∧ st'.globals = st.globals ∧ st'.prevBlock = st.prevBlock := by
    intro dst w fl ex a b k h
    unfold shiftResult at h
    cases a with
    | poison => exact hbind _ _ h
    | ptr _ | floatBits _ _ | aggNil | aggCons _ _ =>
      cases b <;> first | exact hbind _ _ h | nomatch h
    | bits wa va =>
      cases b with
      | poison => exact hbind _ _ h
      | ptr _ | floatBits _ _ | aggNil | aggCons _ _ => nomatch h
      | bits wb vb =>
        dsimp only at h
        by_cases ha : wa = w
        · subst wa
          by_cases hb : wb = w
          · subst wb
            simp only [↓reduceDIte] at h
            exact hite _ (hbind _ _) (hite _ (hbind _ _) (hite _ (hbind _ _) (hbind _ _))) h
          · simp [hb] at h
        · simp [ha] at h
  cases ins <;> simp [isPureRegInstr] at hpure
  case add dst fl w aOp bOp => exact hbin dst w fl _ _ "add" hstep
  case sub dst fl w aOp bOp => exact hbin dst w fl _ _ "sub" hstep
  case mul dst fl w aOp bOp => exact hbin dst w fl _ _ "mul" hstep
  case and_ dst w aOp bOp => exact hbin dst w .none _ _ "and" hstep
  case or_ dst w aOp bOp => exact hbin dst w .none _ _ "or" hstep
  case xor dst w aOp bOp => exact hbin dst w .none _ _ "xor" hstep
  case udiv dst ex w aOp bOp => exact hdiv dst w ex _ _ false false hstep
  case sdiv dst ex w aOp bOp => exact hdiv dst w ex _ _ true false hstep
  case urem dst w aOp bOp => exact hdiv dst w false _ _ false true hstep
  case srem dst w aOp bOp => exact hdiv dst w false _ _ true true hstep
  case shl dst fl w aOp bOp => exact hshf dst w fl false _ _ "shl" hstep
  case lshr dst ex w aOp bOp => exact hshf dst w .none ex _ _ "lshr" hstep
  case ashr dst ex w aOp bOp => exact hshf dst w .none ex _ _ "ashr" hstep
  case icmp dst pred ty aOp bOp =>
    unfold stepInstr at hstep
    dsimp only [stepInstrWith] at hstep
    cases ty with
    | void | float _ | array _ _ | vec _ _ | structFields _ _ => nomatch hstep
    | int w =>
      dsimp only at hstep
      cases ha0 : evalOperand st aOp with
      | poison => rw [ha0] at hstep; exact hbind _ _ hstep
      | ptr _ | floatBits _ _ | aggNil | aggCons _ _ =>
        rw [ha0] at hstep
        cases hb0 : evalOperand st bOp <;> rw [hb0] at hstep <;>
          first | exact hbind _ _ hstep | nomatch hstep
      | bits wa va =>
        rw [ha0] at hstep
        cases hb0 : evalOperand st bOp with
        | poison => rw [hb0] at hstep; exact hbind _ _ hstep
        | ptr _ | floatBits _ _ | aggNil | aggCons _ _ => rw [hb0] at hstep; nomatch hstep
        | bits wb vb =>
          rw [hb0] at hstep
          dsimp only at hstep
          by_cases ha : wa = w
          · subst wa
            by_cases hb : wb = w
            · subst wb
              simp only [↓reduceDIte] at hstep
              exact hbind _ _ hstep
            · simp [hb] at hstep
          · simp [ha] at hstep
    | ptr _ =>
      dsimp only at hstep
      cases ha0 : evalOperand st aOp <;> rw [ha0] at hstep <;>
        cases hb0 : evalOperand st bOp <;> rw [hb0] at hstep <;>
        first | exact hbind _ _ hstep | nomatch hstep
  case zext dst srcW op dstW =>
    unfold stepInstr at hstep
    dsimp only [stepInstrWith] at hstep
    cases hop : evalOperand st op with
    | poison => rw [hop] at hstep; exact hbind _ _ hstep
    | ptr _ | floatBits _ _ | aggNil | aggCons _ _ => rw [hop] at hstep; nomatch hstep
    | bits w v =>
      rw [hop] at hstep
      dsimp only at hstep
      by_cases hw : w = srcW
      · subst w
        simp only [↓reduceDIte] at hstep
        split at hstep
        · exact hbind _ _ hstep
        · nomatch hstep
      · simp [hw] at hstep
  case sext dst srcW op dstW =>
    unfold stepInstr at hstep
    dsimp only [stepInstrWith] at hstep
    cases hop : evalOperand st op with
    | poison => rw [hop] at hstep; exact hbind _ _ hstep
    | ptr _ | floatBits _ _ | aggNil | aggCons _ _ => rw [hop] at hstep; nomatch hstep
    | bits w v =>
      rw [hop] at hstep
      dsimp only at hstep
      by_cases hw : w = srcW
      · subst w
        simp only [↓reduceDIte] at hstep
        split at hstep
        · exact hbind _ _ hstep
        · nomatch hstep
      · simp [hw] at hstep
  case trunc dst srcW op dstW =>
    unfold stepInstr at hstep
    dsimp only [stepInstrWith] at hstep
    cases hop : evalOperand st op with
    | poison => rw [hop] at hstep; exact hbind _ _ hstep
    | ptr _ | floatBits _ _ | aggNil | aggCons _ _ => rw [hop] at hstep; nomatch hstep
    | bits w v =>
      rw [hop] at hstep
      dsimp only at hstep
      by_cases hw : w = srcW
      · subst w
        simp only [↓reduceDIte] at hstep
        split at hstep
        · exact hbind _ _ hstep
        · nomatch hstep
      · simp [hw] at hstep
  case select dst condOp ty tOp eOp =>
    unfold stepInstr at hstep
    dsimp only [stepInstrWith] at hstep
    cases hc : evalOperand st condOp with
    | poison => rw [hc] at hstep; exact hbind _ _ hstep
    | ptr _ | floatBits _ _ | aggNil | aggCons _ _ => rw [hc] at hstep; nomatch hstep
    | bits wc vc =>
      rw [hc] at hstep
      cases wc with
      | i8 | i16 | i32 | i64 | i128 | i256 | i512 => nomatch hstep
      | i1 =>
        dsimp only at hstep
        exact hite _ (hbind _ _) (hbind _ _) hstep

/-- Compositional frame preservation across any straight-line sequence of pure SSA instructions:
memory, globals, and predecessor block labels remain strictly invariant. -/
theorem StraightLineBisim.pure_frame {mod_ : LLVMModule} {fuel : Nat}
    {st st' : ExecState} {is : List LLVMInstr}
    (h : StraightLineBisim mod_ fuel st is st')
    (hpure : ∀ ins ∈ is, isPureRegInstr ins = true) :
    st'.mem = st.mem ∧ st'.globals = st.globals ∧ st'.prevBlock = st.prevBlock := by
  induction h with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | @cons st0 st1 st2 ins rest hstep _ ih =>
    have hp_head : isPureRegInstr ins = true := hpure ins (List.mem_cons_self ..)
    have hp_tail : ∀ i ∈ rest, isPureRegInstr i = true :=
      fun i hi => hpure i (List.mem_cons_of_mem _ hi)
    rcases stepInstr_pure_frame hp_head hstep with ⟨hm1, hg1, hp1⟩
    rcases ih hp_tail with ⟨hm2, hg2, hp2⟩
    exact ⟨hm2.trans hm1, hg2.trans hg1, hp2.trans hp1⟩

/-- Concrete non-vacuous 5-instruction straight-line SSA sequence exercising register-to-register
forwarding, overflow/shift/comparison/select poison propagation, and non-UB `srem` composition:
1. `sum = add flags w a b`
2. `sh  = lshr exact w sum b`
3. `cmp = icmp slt w sh a`
4. `sel = select cmp w sh sum`
5. `out = srem w a b`
Proved equivalent end-to-end (including `execInstrs`, output register lookup, live input register
preservation, and memory/globals frame invariance) to composed `InstCombine.Op.denote`. -/
def straightLineFusedPipeline (w : IntWidth) (flags : OverflowFlags) (exact : Bool)
    (rA rB rSum rSh rCmp rSel rOut : RegName) : List LLVMInstr :=
  [ .add rSum flags w (.reg rA) (.reg rB)
  , .lshr rSh exact w (.reg rSum) (.reg rB)
  , .icmp rCmp .slt (.int w) (.reg rSh) (.reg rA)
  , .select rSel (.reg rCmp) (.int w) (.reg rSh) (.reg rSum)
  , .srem rOut w (.reg rA) (.reg rB)
  ]

theorem execInstrs_straightLineFusedPipeline_eq_op_denote
    (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (w : IntWidth) (flags : OverflowFlags) (exact : Bool)
    (va vb : BitVec w.bits)
    (hw1 : w.bits ≠ 1)
    (hb0 : vb ≠ 0#w.bits)
    (hno_ov : sdivOverflow w va vb = false)
    (ha : evalOperand st (.reg "a") = .bits w va)
    (hb : evalOperand st (.reg "b") = .bits w vb) :
    let vSum := InstCombine.Op.denote (InstCombine.LLVM.Op.add w.bits (toNoWrapFlags flags))
      (HVector.cons (.value va) (HVector.cons (.value vb) HVector.nil))
    let vSh := InstCombine.Op.denote (InstCombine.LLVM.Op.lshr w.bits { exact := exact })
      (HVector.cons vSum (HVector.cons (.value vb) HVector.nil))
    let vCmp := InstCombine.Op.denote (InstCombine.LLVM.Op.icmp .slt w.bits)
      (HVector.cons vSh (HVector.cons (.value va) HVector.nil))
    let vSel := InstCombine.Op.denote (InstCombine.LLVM.Op.select w.bits)
      (HVector.cons vCmp (HVector.cons vSh (HVector.cons vSum HVector.nil)))
    let vRem := InstCombine.Op.denote (InstCombine.LLVM.Op.srem w.bits)
      (HVector.cons (.value va) (HVector.cons (.value vb) HVector.nil))
    ∃ st',
      execInstrs mod_ fuel st
        (straightLineFusedPipeline w flags exact "a" "b" "t_sum" "t_sh" "t_cmp" "t_sel" "t_out") =
          .inr st' ∧
      evalOperand st' (.reg "t_sel") = toLLVMVal w vSel ∧
      evalOperand st' (.reg "t_out") = toLLVMVal w vRem ∧
      evalOperand st' (.reg "a") = .bits w va ∧
      evalOperand st' (.reg "b") = .bits w vb ∧
      st'.mem = st.mem ∧ st'.globals = st.globals ∧ st'.prevBlock = st.prevBlock := by
  intro vSum vSh vCmp vSel vRem
  let st1 := bindReg st "t_sum" (toLLVMVal w vSum)
  let st2 := bindReg st1 "t_sh" (toLLVMVal w vSh)
  let st3 := bindReg st2 "t_cmp" (toLLVMVal .i1 vCmp)
  let st4 := bindReg st3 "t_sel" (toLLVMVal w vSel)
  let st5 := bindReg st4 "t_out" (toLLVMVal w vRem)
  have hs1 : stepInstr mod_ fuel st (.add "t_sum" flags w (.reg "a") (.reg "b")) = .inr st1 :=
    stepInstr_add_eq_op_denote mod_ fuel st "t_sum" flags w (.reg "a") (.reg "b")
      (.value va) (.value vb) ha hb
  have hb1 : evalOperand st1 (.reg "b") = .bits w vb := by
    rw [evalOperand_reg_bindReg_ne st "b" "t_sum" _ (by decide), hb]
  have hs2 : stepInstr mod_ fuel st1 (.lshr "t_sh" exact w (.reg "t_sum") (.reg "b")) = .inr st2 :=
    stepInstr_lshr_eq_op_denote mod_ fuel st1 "t_sh" exact w (.reg "t_sum") (.reg "b")
      vSum (.value vb) (evalOperand_reg_bindReg_same ..) hb1
  have ha2 : evalOperand st2 (.reg "a") = .bits w va := by
    rw [evalOperand_reg_bindReg_ne st1 "a" "t_sh" _ (by decide),
        evalOperand_reg_bindReg_ne st "a" "t_sum" _ (by decide), ha]
  have hs3 : stepInstr mod_ fuel st2 (.icmp "t_cmp" .slt (.int w) (.reg "t_sh") (.reg "a")) = .inr st3 :=
    stepInstr_icmp_eq_op_denote mod_ fuel st2 "t_cmp" .slt w (.reg "t_sh") (.reg "a")
      vSh (.value va) (evalOperand_reg_bindReg_same ..) ha2
  have hsh3 : evalTypedOperand st3 (.int w) (.reg "t_sh") = toLLVMVal w vSh := by
    rw [evalTypedOperand_int_reg,
        evalOperand_reg_bindReg_ne st2 "t_sh" "t_cmp" _ (by decide),
        evalOperand_reg_bindReg_same]
  have hsum3 : evalTypedOperand st3 (.int w) (.reg "t_sum") = toLLVMVal w vSum := by
    rw [evalTypedOperand_int_reg,
        evalOperand_reg_bindReg_ne st2 "t_sum" "t_cmp" _ (by decide),
        evalOperand_reg_bindReg_ne st1 "t_sum" "t_sh" _ (by decide),
        evalOperand_reg_bindReg_same]
  have hs4 : stepInstr mod_ fuel st3
      (.select "t_sel" (.reg "t_cmp") (.int w) (.reg "t_sh") (.reg "t_sum")) = .inr st4 :=
    stepInstr_select_eq_op_denote mod_ fuel st3 "t_sel" (.reg "t_cmp") w (.reg "t_sh") (.reg "t_sum")
      vCmp vSh vSum (evalOperand_reg_bindReg_same ..) hsh3 hsum3
  have ha4 : evalOperand st4 (.reg "a") = .bits w va := by
    rw [evalOperand_reg_bindReg_ne st3 "a" "t_sel" _ (by decide),
        evalOperand_reg_bindReg_ne st2 "a" "t_cmp" _ (by decide), ha2]
  have hb4 : evalOperand st4 (.reg "b") = .bits w vb := by
    rw [evalOperand_reg_bindReg_ne st3 "b" "t_sel" _ (by decide),
        evalOperand_reg_bindReg_ne st2 "b" "t_cmp" _ (by decide),
        evalOperand_reg_bindReg_ne st1 "b" "t_sh" _ (by decide), hb1]
  have hs5 : stepInstr mod_ fuel st4 (.srem "t_out" w (.reg "a") (.reg "b")) = .inr st5 :=
    stepInstr_srem_eq_op_denote_of_non_ub mod_ fuel st4 "t_out" w (.reg "a") (.reg "b")
      va vb hw1 hb0 hno_ov ha4 hb4
  have htrace1 : StraightLineBisim mod_ fuel st
      [ .add "t_sum" flags w (.reg "a") (.reg "b")
      , .lshr "t_sh" exact w (.reg "t_sum") (.reg "b") ] st2 :=
    .cons hs1 (.cons hs2 (.nil st2))
  have htrace2 : StraightLineBisim mod_ fuel st2
      [ .icmp "t_cmp" .slt (.int w) (.reg "t_sh") (.reg "a")
      , .select "t_sel" (.reg "t_cmp") (.int w) (.reg "t_sh") (.reg "t_sum")
      , .srem "t_out" w (.reg "a") (.reg "b") ] st5 :=
    .cons hs3 (.cons hs4 (.cons hs5 (.nil st5)))
  have htrace : StraightLineBisim mod_ fuel st
      (straightLineFusedPipeline w flags exact "a" "b" "t_sum" "t_sh" "t_cmp" "t_sel" "t_out") st5 :=
    htrace1.append htrace2
  have hframe := htrace.pure_frame (by
    intro ins hins
    simp only [straightLineFusedPipeline, List.mem_cons, List.not_mem_nil, or_false] at hins
    rcases hins with rfl | rfl | rfl | rfl | rfl <;> rfl)
  refine ⟨st5, execInstrs_of_straightLineBisim htrace, ?_, ?_, ?_, ?_, hframe⟩
  · rw [evalOperand_reg_bindReg_ne st4 "t_sel" "t_out" _ (by decide),
        evalOperand_reg_bindReg_same]
  · exact evalOperand_reg_bindReg_same ..
  · rw [evalOperand_reg_bindReg_ne st4 "a" "t_out" _ (by decide), ha4]
  · rw [evalOperand_reg_bindReg_ne st4 "b" "t_out" _ (by decide), hb4]

/-! ## Stage 2C.8: Integer Pointer Casts (`inttoptr`/`ptrtoint`), Inbounds Scalar GEP & Atomic RMW -/

/-- Exact complete case characterization of `LLVMAst.stepInstr` on `.inttoptr`:
1. `.poison` propagates to `.poison`;
2. `.bits srcW v` with matching width produces `.ptr (v.zeroExtend 64)` (agreeing with
   `LLVM.zext? 64 v = .value (v.zeroExtend 64)`);
3. integer width mismatch (`w ≠ srcW`) produces `.inl (.ub "inttoptr width mismatch")`;
4. any non-integer, non-poison value produces `.inl (.ub "inttoptr on non-integer")`. -/
theorem stepInstr_inttoptr_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (srcW : IntWidth) (op : Operand) (as_ : AddrSpace) :
    stepInstr mod_ fuel st (.inttoptr dst srcW op as_) =
      match evalOperand st op with
      | .poison => .inr (bindReg st dst .poison)
      | .bits w v =>
        if h : w = srcW then .inr (bindReg st dst (.ptr ((h ▸ v).zeroExtend 64)))
        else .inl (.ub "inttoptr width mismatch")
      | _ => .inl (.ub "inttoptr on non-integer") := by
  cases hop : evalOperand st op <;> simp [stepInstr, stepInstrWith, hop]

/-- Exact complete case characterization of `LLVMAst.stepInstr` on `.ptrtoint`:
1. `.poison` propagates to `.poison`;
2. `.ptr p` produces `.bits dstW (p.truncate dstW.bits)` (agreeing with
   `LLVM.trunc? dstW.bits p = .value (p.truncate dstW.bits)`);
3. any non-pointer, non-poison value produces `.inl (.ub "ptrtoint on non-pointer")`. -/
theorem stepInstr_ptrtoint_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (as_ : AddrSpace) (op : Operand) (dstW : IntWidth) :
    stepInstr mod_ fuel st (.ptrtoint dst as_ op dstW) =
      match evalOperand st op with
      | .poison => .inr (bindReg st dst .poison)
      | .ptr p => .inr (bindReg st dst (.bits dstW (p.truncate dstW.bits)))
      | _ => .inl (.ub "ptrtoint on non-pointer") := by
  cases hop : evalOperand st op <;> simp [stepInstr, stepInstrWith, hop]

/-- Exact 64-bit pointer-to-integer-to-pointer roundtrip: casting `p : BitVec 64` via
`ptrtoint ... to i64` followed by `inttoptr i64 ... to ptr` recovers `.ptr p` identically,
and preserves memory, globals, and predecessor block labels. -/
theorem stepInstr_ptrtoint_inttoptr_roundtrip (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (rInt rPtr : RegName) (as1 as2 : AddrSpace) (ptrOp : Operand) (p : BitVec 64)
    (hp : evalOperand st ptrOp = .ptr p) :
    let st1 := bindReg st rInt (.bits .i64 p)
    let st2 := bindReg st1 rPtr (.ptr p)
    stepInstr mod_ fuel st (.ptrtoint rInt as1 ptrOp .i64) = .inr st1 ∧
    stepInstr mod_ fuel st1 (.inttoptr rPtr .i64 (.reg rInt) as2) = .inr st2 ∧
    execInstrs mod_ fuel st
      [ .ptrtoint rInt as1 ptrOp .i64
      , .inttoptr rPtr .i64 (.reg rInt) as2 ] = .inr st2 ∧
    evalOperand st2 (.reg rPtr) = .ptr p ∧
    st2.mem = st.mem ∧ st2.globals = st.globals ∧ st2.prevBlock = st.prevBlock := by
  have htrunc : p.truncate (IntWidth.i64.bits) = p := BitVec.setWidth_eq p
  let st1 := bindReg st rInt (.bits .i64 p)
  let st2 := bindReg st1 rPtr (.ptr p)
  have hs1 : stepInstr mod_ fuel st (.ptrtoint rInt as1 ptrOp .i64) = .inr st1 := by
    rw [stepInstr_ptrtoint_bisim]
    simp [hp, htrunc, st1]
  have hs2 : stepInstr mod_ fuel st1 (.inttoptr rPtr .i64 (.reg rInt) as2) = .inr st2 := by
    rw [stepInstr_inttoptr_bisim]
    have hreg : evalOperand st1 (.reg rInt) = .bits .i64 p := evalOperand_reg_bindReg_same st rInt _
    rw [hreg]
    simp only [↓reduceDIte]
    change Sum.inr (bindReg st1 rPtr (.ptr (p.setWidth 64))) = Sum.inr st2
    rw [BitVec.setWidth_eq p]
  have htrace : StraightLineBisim mod_ fuel st
      [ .ptrtoint rInt as1 ptrOp .i64
      , .inttoptr rPtr .i64 (.reg rInt) as2 ] st2 :=
    .cons hs1 (.cons hs2 (.nil st2))
  exact ⟨hs1, hs2, execInstrs_of_straightLineBisim htrace,
    evalOperand_reg_bindReg_same .., rfl, rfl, rfl⟩

/-- Non-negative single-index scalar `gepOffset` and `inboundsInAlloc` verification:
when `idx` is non-negative (`bvSigned idxW idx ≥ 0`, equivalently `idx.msb = false`),
`gepIndexSigned idxW idx = Int.ofNat idx.toNat`, `gepOffset ty [(gepIndexSigned idxW idx, idxW)]`
equals `some (Int.ofNat (idx.toNat * ty.byteSize))`, and whenever an allocation block `blk` is
found for `base.toNat` containing both `base.toNat` and `base.toNat + idx.toNat * ty.byteSize`
with natural alignment (`isAligned base ty.abiAlign = true` and `(idx.toNat * ty.byteSize) % ty.abiAlign = 0`)
and 64-bit no-wrap (`base.toNat + idx.toNat * ty.byteSize < 2 ^ 64`), `inboundsInAlloc` holds and
the resulting pointer `BitVec.ofNat 64 (base.toNat + idx.toNat * ty.byteSize)` preserves alignment. -/
theorem gep_scalar_offset_inbounds (m : ByteMem) (ty : LLVMType) (base : BitVec 64)
    (idxW : IntWidth) (idx : BitVec idxW.bits) (blk : AllocBlock)
    (h_nonneg : 0 ≤ bvSigned idxW idx)
    (h_find : m.allocs.find? (fun b => b.base ≤ base.toNat && base.toNat ≤ b.base + b.size) = some blk)
    (h_base_lo : blk.base ≤ base.toNat)
    (h_end_hi : base.toNat + idx.toNat * ty.byteSize ≤ blk.base + blk.size)
    (h_fit : base.toNat + idx.toNat * ty.byteSize < 2 ^ 64)
    (h_align_base : isAligned base ty.abiAlign = true)
    (h_align_step : (idx.toNat * ty.byteSize) % ty.abiAlign = 0) :
    let resNat := base.toNat + idx.toNat * ty.byteSize
    let resAddr : Int := Int.ofNat base.toNat + Int.ofNat ty.byteSize * gepIndexSigned idxW idx
    gepIndexSigned idxW idx = Int.ofNat idx.toNat ∧
    gepOffset ty [(gepIndexSigned idxW idx, idxW)] = some (Int.ofNat (idx.toNat * ty.byteSize)) ∧
    resAddr = Int.ofNat resNat ∧
    m.inboundsInAlloc base.toNat resAddr = true ∧
    isAligned (BitVec.ofNat 64 resNat) ty.abiAlign = true := by
  have h_idx_eq : gepIndexSigned idxW idx = Int.ofNat idx.toNat := by
    unfold gepIndexSigned
    have hpos : 0 < idxW.bits := idxW.bits_pos
    have h2w : 2 ^ idxW.bits = 2 * 2 ^ (idxW.bits - 1) := two_pow_eq_two_mul_pred idxW.bits hpos
    have hlt_pow : idx.toNat < 2 ^ idxW.bits := idx.isLt
    unfold bvSigned at h_nonneg ⊢
    simp only [Int.ofNat_eq_natCast, int_two_pow_eq_natCast] at h_nonneg ⊢
    split at h_nonneg <;> split <;> omega
  have h_off : gepOffset ty [(gepIndexSigned idxW idx, idxW)] =
      some (Int.ofNat (idx.toNat * ty.byteSize)) := by
    simp only [gepOffset, h_idx_eq, Int.ofNat_eq_natCast]
    congr 1
    rw [Int.natCast_mul, Int.mul_comm]
  have h_res_eq : Int.ofNat base.toNat + Int.ofNat ty.byteSize * gepIndexSigned idxW idx =
      Int.ofNat (base.toNat + idx.toNat * ty.byteSize) := by
    rw [h_idx_eq]
    simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul]
    rw [Int.mul_comm]
  have h_inb : m.inboundsInAlloc base.toNat
      (Int.ofNat base.toNat + Int.ofNat ty.byteSize * gepIndexSigned idxW idx) = true := by
    rw [h_res_eq]
    unfold ByteMem.inboundsInAlloc
    have h_not_neg : ¬(Int.ofNat (base.toNat + idx.toNat * ty.byteSize) < 0) :=
      Int.not_lt.mpr (Int.natCast_nonneg _)
    have h_tonat : (Int.ofNat (base.toNat + idx.toNat * ty.byteSize)).toNat =
        base.toNat + idx.toNat * ty.byteSize := rfl
    simp only [h_not_neg, ↓reduceIte, h_tonat, h_find, Bool.and_eq_true, decide_eq_true_eq]
    omega
  have h_aligned_res : isAligned (BitVec.ofNat 64 (base.toNat + idx.toNat * ty.byteSize)) ty.abiAlign = true := by
    unfold isAligned at h_align_base ⊢
    rcases Bool.and_eq_true_iff.mp h_align_base with ⟨hp2, hmod_base⟩
    have hb0 : base.toNat % ty.abiAlign = 0 := beq_iff_eq.mp hmod_base
    apply Bool.and_eq_true_iff.mpr
    refine ⟨hp2, beq_iff_eq.mpr ?_⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_fit, Nat.add_mod, hb0, h_align_step, Nat.zero_add,
        Nat.zero_mod]
  exact ⟨h_idx_eq, h_off, h_res_eq, h_inb, h_aligned_res⟩

/-- Single-index `getelementptr inbounds` operational bisimulation:
for a non-poison scalar pointer `base` inside an allocated block `blk` (`blk.base ≤ base.toNat`,
`base.toNat + idx.toNat * elemW.byteSize ≤ blk.base + blk.size`) with non-negative index `idx`
of width `idxW`, natural element alignment `isAligned base elemW.naturalAlign = true`, and
64-bit address fit, `stepInstr` evaluates `.getelementptr dst true (.int elemW) baseOp [(idxW, idxOp)] as_`
to `.inr (bindReg st dst (.ptr (BitVec.ofNat 64 (base.toNat + idx.toNat * elemW.byteSize))))`
while preserving natural alignment and leaving memory, globals, and `prevBlock` untouched. -/
theorem stepInstr_getelementptr_inbounds_scalar_bisim
    (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (elemW idxW : IntWidth) (baseOp idxOp : Operand) (as_ : AddrSpace)
    (base : BitVec 64) (idx : BitVec idxW.bits) (blk : AllocBlock)
    (hbase : evalOperand st baseOp = .ptr base)
    (hidx : evalOperand st idxOp = .bits idxW idx)
    (h_nonneg : 0 ≤ bvSigned idxW idx)
    (h_find : st.mem.allocs.find? (fun b => b.base ≤ base.toNat && base.toNat ≤ b.base + b.size) = some blk)
    (h_base_lo : blk.base ≤ base.toNat)
    (h_end_hi : base.toNat + idx.toNat * elemW.byteSize ≤ blk.base + blk.size)
    (h_fit : base.toNat + idx.toNat * elemW.byteSize < 2 ^ 64)
    (h_align_base : isAligned base elemW.naturalAlign = true) :
    let resPtr := BitVec.ofNat 64 (base.toNat + idx.toNat * elemW.byteSize)
    stepInstr mod_ fuel st (.getelementptr dst true (.int elemW) baseOp [(idxW, idxOp)] as_) =
      .inr (bindReg st dst (.ptr resPtr)) ∧
    isAligned resPtr elemW.naturalAlign = true ∧
    (bindReg st dst (.ptr resPtr)).mem = st.mem ∧
    (bindReg st dst (.ptr resPtr)).globals = st.globals ∧
    (bindReg st dst (.ptr resPtr)).prevBlock = st.prevBlock := by
  have h_step_div : (idx.toNat * elemW.byteSize) % elemW.naturalAlign = 0 := by
    have hdvd : elemW.naturalAlign ∣ elemW.byteSize := by
      cases elemW <;> decide
    exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hdvd idx.toNat)
  have h_gep := gep_scalar_offset_inbounds st.mem (.int elemW) base idxW idx blk
    h_nonneg h_find h_base_lo h_end_hi h_fit h_align_base h_step_div
  rcases h_gep with ⟨h_idx_eq, h_off, h_res_eq, h_inb, h_aligned_res⟩
  refine ⟨?_, h_aligned_res, rfl, rfl, rfl⟩
  have h_res_nonneg : ¬(Int.ofNat (base.toNat + idx.toNat * elemW.byteSize) < 0) :=
    Int.not_lt.mpr (Int.natCast_nonneg _)
  have h_tonat : (Int.ofNat (base.toNat + idx.toNat * elemW.byteSize)).toNat =
      base.toNat + idx.toNat * elemW.byteSize := rfl
  have h_inb_nat : st.mem.inboundsInAlloc base.toNat
      (Int.ofNat (base.toNat + idx.toNat * elemW.byteSize)) = true := by
    rwa [h_res_eq] at h_inb
  unfold stepInstr stepInstrWith gepResult
  simp only [hbase, hidx, List.any_cons, List.any_nil, Bool.or_false, isPoison,
    Bool.false_eq_true, ↓reduceIte, List.mapM_cons, List.mapM_nil, Option.pure_def,
    Option.bind_eq_bind, Option.bind_some, ↓reduceDIte]
  change (match gepOffset (.int elemW) [(gepIndexSigned idxW idx, idxW)] with
    | none => (Sum.inl (.ub "getelementptr ill-typed index") : ExecOutcome ⊕ ExecState)
    | some off =>
      let resAddr : Int := Int.ofNat base.toNat + off
      if true && !st.mem.inboundsInAlloc base.toNat resAddr then
        Sum.inr (bindReg st dst .poison)
      else if resAddr < 0 then
        Sum.inl (.ub "getelementptr negative address")
      else
        Sum.inr (bindReg st dst (.ptr (BitVec.ofNat 64 resAddr.toNat)))) = _
  rw [h_off]
  dsimp only [LLVMType.byteSize]
  have heq_addr : Int.ofNat base.toNat + Int.ofNat (idx.toNat * elemW.byteSize) =
      Int.ofNat (base.toNat + idx.toNat * elemW.byteSize) := by
    simp [Int.ofNat_eq_natCast, Int.natCast_add]
  rw [heq_addr, h_inb_nat]
  simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte, h_res_nonneg, h_tonat]

/-- Algebraic and `LLVM.*` correspondence laws for `LLVMAst.evalRMWOp`:
1. `add`, `sub`, `and_`, `or_`, `xor` match the corresponding `BitVec` operations and
   upstream `opencompl/lean-mlir` `LLVM.{add?,sub?,and?,or?,xor?}` pure semantics;
2. `xchg old val = val`;
3. `and_`, `or_`, and `xor` satisfy exact commutativity and identity laws (`BitVec.allOnes w.bits`
   for `and_`, `0#w.bits` for `or_` and `xor`). -/
theorem atomic_rmw_eval_comm_and_id (w : IntWidth) (old val : BitVec w.bits) :
    evalRMWOp .add w old val = old + val ∧
    evalRMWOp .sub w old val = old - val ∧
    evalRMWOp .and_ w old val = (old &&& val) ∧
    evalRMWOp .or_ w old val = (old ||| val) ∧
    evalRMWOp .xor w old val = (old ^^^ val) ∧
    evalRMWOp .xchg w old val = val ∧
    (PoisonOr.value (evalRMWOp .add w old val) : LLVM.IntW w.bits) = LLVM.add? old val ∧
    (PoisonOr.value (evalRMWOp .sub w old val) : LLVM.IntW w.bits) = LLVM.sub? old val ∧
    (PoisonOr.value (evalRMWOp .and_ w old val) : LLVM.IntW w.bits) = LLVM.and? old val ∧
    (PoisonOr.value (evalRMWOp .or_ w old val) : LLVM.IntW w.bits) = LLVM.or? old val ∧
    (PoisonOr.value (evalRMWOp .xor w old val) : LLVM.IntW w.bits) = LLVM.xor? old val ∧
    evalRMWOp .and_ w old val = evalRMWOp .and_ w val old ∧
    evalRMWOp .or_ w old val = evalRMWOp .or_ w val old ∧
    evalRMWOp .xor w old val = evalRMWOp .xor w val old ∧
    evalRMWOp .and_ w old (BitVec.allOnes w.bits) = old ∧
    evalRMWOp .or_ w old 0#w.bits = old ∧
    evalRMWOp .xor w old 0#w.bits = old := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BitVec.and_comm old val
  · exact BitVec.or_comm old val
  · exact BitVec.xor_comm old val
  · exact BitVec.and_allOnes
  · exact BitVec.or_zero
  · exact BitVec.xor_zero

/-- Operational bisimulation and alignment/UB boundary for `LLVMAst.stepInstr` on `.atomicrmw`:
1. When `addr ≠ 0#64`, the effective alignment `effAlign := if align == 0 then w.byteSize else align`
   is a power of two, `isAligned addr effAlign = true`, `st.mem.accessInAlloc addr.toNat w.byteSize true = true`,
   `st.mem.loadInt? addr w = some old`, and `evalOperand st valOp = .bits w val`, `stepInstr` transitions to
   `bindReg { st with mem := st.mem.storeInt addr w (evalRMWOp op w old val) } dst (.bits w old)`,
   yielding `.bits w old` in `dst`, storing `evalRMWOp op w old val` at `addr` (readable via `loadInt?`),
   and preserving every other register `r ≠ dst`, `globals`, and `prevBlock`.
2. Conversely, when `addr ≠ 0#64` and `effAlign` is invalid (`isPow2 effAlign = false`), `stepInstr`
   returns `.inl (.ub "invalid alignment")`; and when `isPow2 effAlign = true` but `addr` is misaligned
   (`isAligned addr effAlign = false`), `stepInstr` returns `.inl (.ub "misaligned atomicrmw")`
   without performing a store. -/
theorem stepInstr_atomicrmw_aligned_bisim
    (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (op : AtomicRMWOp) (ptrOp valOp : Operand)
    (w : IntWidth) (ord : AtomicOrdering) (align : Nat) (as_ : AddrSpace)
    (addr : BitVec 64)
    (hptr : evalOperand st ptrOp = .ptr addr)
    (hnonnull : addr ≠ 0#64) :
    let effAlign := if align == 0 then w.byteSize else align
    ((isPow2 effAlign = false →
        stepInstr mod_ fuel st (.atomicrmw dst op ptrOp (.int w) valOp ord align as_) =
          .inl (.ub "invalid alignment")) ∧
     (isPow2 effAlign = true → isAligned addr effAlign = false →
        stepInstr mod_ fuel st (.atomicrmw dst op ptrOp (.int w) valOp ord align as_) =
          .inl (.ub "misaligned atomicrmw")) ∧
     (∀ (old val : BitVec w.bits),
        isPow2 effAlign = true →
        isAligned addr effAlign = true →
        st.mem.accessInAlloc addr.toNat w.byteSize true = true →
        st.mem.loadInt? addr w = some old →
        evalOperand st valOp = .bits w val →
        let st' := bindReg { st with mem := st.mem.storeInt addr w (evalRMWOp op w old val) } dst (.bits w old)
        stepInstr mod_ fuel st (.atomicrmw dst op ptrOp (.int w) valOp ord align as_) = .inr st' ∧
        evalOperand st' (.reg dst) = .bits w old ∧
        st'.mem.loadInt? addr w = some (evalRMWOp op w old val) ∧
        (∀ r, r ≠ dst → evalOperand st' (.reg r) = evalOperand st (.reg r)) ∧
        st'.globals = st.globals ∧
        st'.prevBlock = st.prevBlock)) := by
  dsimp only
  have hnull_beq : (addr == 0#64) = false := beq_eq_false_iff_ne.mpr hnonnull
  refine ⟨?_, ?_, ?_⟩
  · intro hpow_false
    have hacc : accessCheck st.mem addr w.byteSize (if align == 0 then w.byteSize else align) true =
        some "invalid alignment" := by
      unfold accessCheck
      rw [hnull_beq, hpow_false]
      rfl
    unfold stepInstr stepInstrWith
    simp only [hptr, hacc]
  · intro hpow_true hal_false
    have hacc : accessCheck st.mem addr w.byteSize (if align == 0 then w.byteSize else align) true =
        some "misaligned access" := by
      unfold accessCheck
      rw [hnull_beq, hpow_true, hal_false]
      rfl
    unfold stepInstr stepInstrWith
    simp only [hptr, hacc]
  · intro old val hpow_true hal_true hinb hload hval
    have hacc : accessCheck st.mem addr w.byteSize (if align == 0 then w.byteSize else align) true = none := by
      unfold accessCheck
      rw [hnull_beq, hpow_true, hal_true, hinb]
      rfl
    let st' := bindReg { st with mem := st.mem.storeInt addr w (evalRMWOp op w old val) } dst (.bits w old)
    have hstep : stepInstr mod_ fuel st (.atomicrmw dst op ptrOp (.int w) valOp ord align as_) = .inr st' := by
      unfold stepInstr stepInstrWith
      simp only [hptr, hacc, hval, ↓reduceDIte, hload, st']
    refine ⟨hstep, evalOperand_reg_bindReg_same .., ByteMem.loadInt?_storeInt_same .., ?_, rfl, rfl⟩
    intro r hr
    rw [evalOperand_reg_bindReg_ne _ r dst _ hr]
    rfl

/-- Exact memory and architectural frame law for any successful `stepInstr` on `.atomicrmw`:
every byte outside `[addr.toNat, addr.toNat + w.byteSize)` is unchanged (`readAt` and `readByte`),
every disjoint integer load (`rangesDisjoint`) is unchanged, allocation metadata (`allocs`, `nextAlloc`)
is unchanged, every register `r ≠ dst` is unchanged, and `globals` and `prevBlock` are unchanged. -/
theorem stepInstr_atomicrmw_frame
    {mod_ : LLVMModule} {fuel : Nat} {st st' : ExecState}
    {dst : RegName} {op : AtomicRMWOp} {ptrOp valOp : Operand}
    {w : IntWidth} {ord : AtomicOrdering} {align : Nat} {as_ : AddrSpace}
    {addr : BitVec 64}
    (hptr : evalOperand st ptrOp = .ptr addr)
    (hstep : stepInstr mod_ fuel st (.atomicrmw dst op ptrOp (.int w) valOp ord align as_) = .inr st') :
    (∀ q : Nat, (q < addr.toNat ∨ addr.toNat + w.byteSize ≤ q) →
      st'.mem.readAt q = st.mem.readAt q ∧ st'.mem.readByte q = st.mem.readByte q) ∧
    (∀ (a2 : BitVec 64) (w2 : IntWidth),
      rangesDisjoint addr.toNat w.byteSize a2.toNat w2.byteSize = true →
      st'.mem.loadInt? a2 w2 = st.mem.loadInt? a2 w2) ∧
    st'.mem.allocs = st.mem.allocs ∧
    st'.mem.nextAlloc = st.mem.nextAlloc ∧
    (∀ r : RegName, r ≠ dst → evalOperand st' (.reg r) = evalOperand st (.reg r)) ∧
    st'.globals = st.globals ∧
    st'.prevBlock = st.prevBlock := by
  have h_write_allocs : ∀ (m : ByteMem) (base : Nat) (bs : List MemByte),
      (m.writeBytesAt base bs).allocs = m.allocs ∧
      (m.writeBytesAt base bs).nextAlloc = m.nextAlloc := by
    intro m base bs
    induction bs generalizing m base with
    | nil => exact ⟨rfl, rfl⟩
    | cons b rest ih =>
      simp only [ByteMem.writeBytesAt]
      rcases ih (m.writeAt base b) (base + 1) with ⟨ha, hn⟩
      exact ⟨ha, hn⟩
  have h_extract : ∃ (bs : List MemByte) (vDst : LLVMVal),
      bs.length = w.byteSize ∧
      st' = bindReg { st with mem := st.mem.writeBytesAt addr.toNat bs } dst vDst := by
    unfold stepInstr stepInstrWith at hstep
    simp only [hptr] at hstep
    cases hacc : accessCheck st.mem addr w.byteSize (if align == 0 then w.byteSize else align) true with
    | some msg =>
      rw [hacc] at hstep
      by_cases hm1 : msg = "null pointer"
      · subst hm1; nomatch hstep
      · by_cases hm2 : msg = "invalid alignment"
        · subst hm2; simp at hstep
        · by_cases hm3 : msg = "misaligned access"
          · subst hm3; simp at hstep
          · simp at hstep
    | none =>
      rw [hacc] at hstep
      dsimp only at hstep
      cases hval : evalOperand st valOp with
      | poison =>
        rw [hval] at hstep
        injection hstep with hst'
        refine ⟨ByteMem.poisonBytes w.byteSize, .poison, ByteMem.poisonBytes_length w.byteSize, ?_⟩
        simpa [ByteMem.storePoison] using hst'.symm
      | ptr _ | floatBits _ _ | aggNil | aggCons _ _ =>
        rw [hval] at hstep
        nomatch hstep
      | bits wv vv =>
        rw [hval] at hstep
        dsimp only at hstep
        by_cases hw : wv = w
        · subst wv
          simp only [↓reduceDIte] at hstep
          cases hld : st.mem.loadInt? addr w with
          | none =>
            rw [hld] at hstep
            nomatch hstep
          | some old =>
            rw [hld] at hstep
            injection hstep with hst'
            let newBv := evalRMWOp op w old vv
            refine ⟨ByteMem.initBytes (ByteMem.bvToLEBytes w.byteSize newBv), .bits w old, ?_, ?_⟩
            · rw [ByteMem.initBytes_length, ByteMem.bvToLEBytes, ByteMem.natToLEBytes_length]
            · simpa [ByteMem.storeInt, newBv] using hst'.symm
        · simp [hw] at hstep
  rcases h_extract with ⟨bs, vDst, hlen, rfl⟩
  rcases h_write_allocs st.mem addr.toNat bs with ⟨hallocs, hnext⟩
  refine ⟨?_, ?_, hallocs, hnext, ?_, rfl, rfl⟩
  · intro q hq
    have hout : q < addr.toNat ∨ addr.toNat + bs.length ≤ q := by omega
    have hr := ByteMem.readAt_writeBytesAt_outside st.mem addr.toNat bs q hout
    refine ⟨hr, ?_⟩
    simp only [ByteMem.readByte, bindReg, hr]
  · intro a2 w2 hdisj
    simp only [ByteMem.loadInt?, bindReg]
    have hdisj' : rangesDisjoint addr.toNat bs.length a2.toNat w2.byteSize = true := by
      rwa [hlen]
    rw [ByteMem.readBytesAt_writeBytesAt_disjoint st.mem addr.toNat bs a2.toNat w2.byteSize hdisj']
  · intro r hr
    rw [evalOperand_reg_bindReg_ne _ r dst _ hr]
    rfl

end LeanMLIRBridge
