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
  cases x <;> simp [toLLVMVal, ofLLVMVal?]

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

theorem bvSigned_eq_toInt (w : IntWidth) (v : BitVec w.bits) :
    bvSigned w v = v.toInt := by
  have hpos : 0 < w.bits := w.bits_pos
  unfold bvSigned BitVec.toInt
  have hpow : (2 : Int) ^ w.bits = (2 : Int) * (2 : Int) ^ (w.bits - 1) := by
    conv_lhs => rw [show w.bits = (w.bits - 1) + 1 by omega]
    rw [Int.pow_succ]
    omega
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  split_ifs with h1 h2
  · rfl
  · exfalso; omega
  · exfalso; omega
  · rfl

theorem addOverflowNSW_eq_saddOverflow (w : IntWidth) (a b : BitVec w.bits) :
    addOverflowNSW w a b = BitVec.saddOverflow a b := by
  have hpos : 0 < w.bits := w.bits_pos
  unfold addOverflowNSW BitVec.saddOverflow
  rw [bvSigned_eq_toInt, bvSigned_eq_toInt]
  simp only [Nat.cast_pow, Nat.cast_ofNat, decide_eq_decide]
  omega

theorem subOverflowNSW_eq_ssubOverflow (w : IntWidth) (a b : BitVec w.bits) :
    subOverflowNSW w a b = BitVec.ssubOverflow a b := by
  have hpos : 0 < w.bits := w.bits_pos
  unfold subOverflowNSW BitVec.ssubOverflow
  rw [bvSigned_eq_toInt, bvSigned_eq_toInt]
  simp only [Nat.cast_pow, Nat.cast_ofNat, decide_eq_decide]
  omega

theorem mulOverflowNSW_eq_smulOverflow (w : IntWidth) (a b : BitVec w.bits) :
    mulOverflowNSW w a b = BitVec.smulOverflow a b := by
  have hpos : 0 < w.bits := w.bits_pos
  unfold mulOverflowNSW BitVec.smulOverflow
  rw [bvSigned_eq_toInt, bvSigned_eq_toInt]
  simp only [Nat.cast_pow, Nat.cast_ofNat, decide_eq_decide]
  omega

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

theorem shlOverflowNSW_eq_mlir (w : IntWidth) (a amt : BitVec w.bits)
    (h_lt : amt.toNat < w.bits) :
    shlOverflowNSW w a amt = decide (((a <<< amt).sshiftRight' amt) ≠ a) := by
  unfold shlOverflowNSW
  rw [bvSigned_eq_toInt]
  have hpos : 0 < w.bits := w.bits_pos
  -- Using `BitVec.toInt_sshiftRight` & `BitVec.toInt_shiftLeft`: shifting left by `k < w.bits`
  -- then arithmetic-shifting right by `k` recovers `a` iff `a.toInt * 2^k` fits in signed `w.bits`.
  have h_round : ((a <<< amt).sshiftRight' amt = a) ↔
      (-((2 : Int) ^ (w.bits - 1)) ≤ a.toInt * (2 : Int) ^ amt.toNat ∧
       a.toInt * (2 : Int) ^ amt.toNat ≤ (2 : Int) ^ (w.bits - 1) - 1) := by
    have hk : amt.toNat ≤ w.bits := Nat.le_of_lt h_lt
    have h_sh_def : (a <<< amt).sshiftRight' amt = (a <<< amt.toNat).sshiftRight amt.toNat := rfl
    rw [h_sh_def, ← BitVec.toInt_inj]
    have h_sdiv : ((a <<< amt.toNat).sshiftRight amt.toNat).toInt =
        (a <<< amt.toNat).toInt / (2 : Int) ^ amt.toNat := by
      rw [BitVec.toInt_sshiftRight_of_lt _ h_lt]
    rw [h_sdiv]
    have h2pos : (0 : Int) < (2 : Int) ^ amt.toNat := by positivity
    have h2w : (2 : Int) ^ w.bits = (2 : Int) ^ (w.bits - 1 + 1) := by
      congr 1; omega
    have h_rem : (2 : Int) ^ w.bits = ((2 : Int) ^ (w.bits - amt.toNat)) * ((2 : Int) ^ amt.toNat) := by
      rw [← Int.pow_add]
      congr 1
      omega
    have h_half : (2 : Int) ^ (w.bits - 1) =
        ((2 : Int) ^ (w.bits - 1 - amt.toNat)) * ((2 : Int) ^ amt.toNat) := by
      rw [← Int.pow_add]
      congr 1
      omega
    have h_toInt_shl : (a <<< amt.toNat).toInt =
        Int.bmod (a.toInt * (2 : Int) ^ amt.toNat) (2 ^ w.bits) := by
      rw [BitVec.toInt_shiftLeft]
      simp [Int.shiftLeft_eq, BitVec.toInt_bmod_cancel]
    constructor
    · intro heq
      have h_bds := BitVec.toInt_lt (a <<< amt.toNat)
      have h_lo := BitVec.le_toInt (a <<< amt.toNat)
      simp only [Nat.cast_pow, Nat.cast_ofNat] at h_bds h_lo
      have h_prod_lo : -((2 : Int) ^ (w.bits - 1)) ≤ a.toInt * (2 : Int) ^ amt.toNat := by
        -- Since `(x / 2^k) = a.toInt` and `x >= -2^(w-1)` with `2^k | 2^(w-1)`
        have h1 : -((2 : Int) ^ (w.bits - 1 - amt.toNat)) ≤ (a <<< amt.toNat).toInt / (2 : Int) ^ amt.toNat := by
          rw [h_half] at h_lo
          exact Int.le_ediv_of_mul_le h2pos h_lo
        rw [heq] at h1
        have := Int.mul_le_mul_of_nonneg_right h1 (le_of_lt h2pos)
        simpa [← h_half] using this
      have h_prod_hi : a.toInt * (2 : Int) ^ amt.toNat ≤ (2 : Int) ^ (w.bits - 1) - 1 := by
        have h1 : (a <<< amt.toNat).toInt / (2 : Int) ^ amt.toNat < (2 : Int) ^ (w.bits - 1 - amt.toNat) := by
          rw [h_half] at h_bds
          exact Int.ediv_lt_of_lt_mul h2pos h_bds
        rw [heq] at h1
        have h1' : a.toInt ≤ (2 : Int) ^ (w.bits - 1 - amt.toNat) - 1 := by omega
        have := Int.mul_le_mul_of_nonneg_right h1' (le_of_lt h2pos)
        rw [Int.sub_mul, one_mul, ← h_half] at this
        omega
      exact ⟨h_prod_lo, h_prod_hi⟩
    · rintro ⟨hlo, hhi⟩
      have h_bmod_id : Int.bmod (a.toInt * (2 : Int) ^ amt.toNat) (2 ^ w.bits) =
          a.toInt * (2 : Int) ^ amt.toNat := by
        apply Int.bmod_eq_of_le
        · simp only [Nat.cast_pow, Nat.cast_ofNat]; omega
        · simp only [Nat.cast_pow, Nat.cast_ofNat]; omega
      rw [h_toInt_shl, h_bmod_id, Int.mul_ediv_cancel _ (ne_of_gt h2pos)]
  simp only [decide_eq_decide]
  omega

theorem shiftedOut_iff_ushift_roundtrip (w : IntWidth) (a amt : BitVec w.bits)
    (h_lt : amt.toNat < w.bits) :
    ((a <<< (w.bits - amt.toNat)) != 0#w.bits) = decide ((a >>> amt) <<< amt ≠ a) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
  apply not_iff_not.mpr
  constructor
  · intro h_zero
    ext i hi
    simp only [BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight]
    by_cases h_ge : i < amt.toNat
    · simp [h_ge]
      have h_idx : i + (w.bits - amt.toNat) < w.bits := by omega
      have hbit := congrArg (fun bv => bv[i + (w.bits - amt.toNat)]'h_idx) h_zero
      simp only [BitVec.getElem_shiftLeft, BitVec.getElem_zero] at hbit
      have h_not : ¬(i + (w.bits - amt.toNat) < w.bits - amt.toNat) := by omega
      simp [h_not, show i + (w.bits - amt.toNat) - (w.bits - amt.toNat) = i by omega] at hbit
      exact hbit.symm
    · have h_le : amt.toNat ≤ i := by omega
      have h_sub : i - amt.toNat + amt.toNat = i := by omega
      simp [h_ge, h_sub]
  · intro h_rt
    ext i hi
    simp only [BitVec.getElem_shiftLeft, BitVec.getElem_zero]
    by_cases h_low : i < w.bits - amt.toNat
    · simp [h_low]
    · simp only [h_low, ↓reduceIte, Bool.not_false, Bool.true_and]
      have h_idx : i - (w.bits - amt.toNat) < w.bits := by omega
      have hbit := congrArg (fun bv => bv[i - (w.bits - amt.toNat)]'h_idx) h_rt
      simp only [BitVec.getElem_shiftLeft] at hbit
      have h_lt_amt : i - (w.bits - amt.toNat) < amt.toNat := by omega
      simp [h_lt_amt] at hbit
      exact hbit.symm

theorem bvSDiv_eq_sdiv (w : IntWidth) (a b : BitVec w.bits) :
    bvSDiv w a b = BitVec.sdiv a b := by
  unfold bvSDiv
  rw [bvSigned_eq_toInt, bvSigned_eq_toInt]
  -- Both `bvSDiv` and `BitVec.sdiv` compute two's-complement truncated signed division `Int.tdiv a.toInt b.toInt` modulo `2^w.bits`.
  have h_mod : (if 0 ≤ Int.tdiv a.toInt b.toInt then
      BitVec.ofNat w.bits (Int.tdiv a.toInt b.toInt).toNat
    else
      BitVec.ofNat w.bits (2 ^ w.bits - (-Int.tdiv a.toInt b.toInt).toNat % 2 ^ w.bits)) =
      BitVec.ofInt w.bits (Int.tdiv a.toInt b.toInt) := by
    set q := Int.tdiv a.toInt b.toInt
    by_cases hq : 0 ≤ q
    · simp only [hq, ↓reduceIte]
      have hq_eq : q = Int.ofNat q.toNat := (Int.toNat_of_nonneg hq).symm
      rw [hq_eq, BitVec.ofInt_ofNat]
    · simp only [hq, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, BitVec.toNat_ofInt]
      have hq_neg : q < 0 := by omega
      set n := (-q).toNat
      have hn : q = -(n : Int) := by omega
      rw [hn]
      have hpos : (0 : Nat) < 2 ^ w.bits := Nat.pos_of_ne_zero (by positivity)
      have hposZ : (0 : Int) < (2 ^ w.bits : Nat) := by exact_mod_cast hpos
      by_cases hrem : n % 2 ^ w.bits = 0
      · simp [hrem]
        have hdvd : ((2 ^ w.bits : Nat) : Int) ∣ (n : Int) := by
          exact_mod_cast Nat.dvd_of_mod_eq_zero hrem
        rcases hdvd with ⟨k, hk⟩
        rw [hk]
        simp [Int.neg_mul_eq_neg_mul]
      · have hlt : n % 2 ^ w.bits < 2 ^ w.bits := Nat.mod_lt _ hpos
        have hsub_lt : 2 ^ w.bits - n % 2 ^ w.bits < 2 ^ w.bits := by omega
        rw [Nat.mod_eq_of_lt hsub_lt]
        have h_emod : (-(n : Int)) % ((2 ^ w.bits : Nat) : Int) =
            ((2 ^ w.bits : Nat) : Int) - ((n % 2 ^ w.bits : Nat) : Int) := by
          have h1 : (n : Int) = ((2 ^ w.bits : Nat) : Int) * (n / 2 ^ w.bits : Nat) + (n % 2 ^ w.bits : Nat) := by
            exact_mod_cast (Nat.div_add_mod n (2 ^ w.bits)).symm
          have hrem_pos : (0 : Int) < (n % 2 ^ w.bits : Nat) := by
            exact_mod_cast Nat.pos_of_ne_zero hrem
          have hrem_lt : ((n % 2 ^ w.bits : Nat) : Int) < (2 ^ w.bits : Nat) := by
            exact_mod_cast hlt
          have h_decomp : -(n : Int) =
              (((2 ^ w.bits : Nat) : Int) - (n % 2 ^ w.bits : Nat)) +
              ((2 ^ w.bits : Nat) : Int) * (-((n / 2 ^ w.bits : Nat) : Int) - 1) := by
            linarith
          rw [h_decomp, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
        rw [h_emod]
        omega
  rw [h_mod]
  -- Now relate `BitVec.ofInt w.bits (Int.tdiv a.toInt b.toInt)` to `BitVec.sdiv a b`
  unfold BitVec.sdiv BitVec.udiv
  by_cases ha : 0 ≤ a.toInt <;> by_cases hb : 0 ≤ b.toInt
  · have h_msb_a : a.msb = false := BitVec.msb_eq_false_iff_two_mul_lt.mpr (by
      have := BitVec.toInt_eq_toNat_cond a; split_ifs at this <;> omega)
    have h_msb_b : b.msb = false := BitVec.msb_eq_false_iff_two_mul_lt.mpr (by
      have := BitVec.toInt_eq_toNat_cond b; split_ifs at this <;> omega)
    simp only [h_msb_a, h_msb_b]
    have ha_eq : a.toInt = a.toNat := by
      have := BitVec.toInt_eq_toNat_cond a; split_ifs at this <;> omega
    have hb_eq : b.toInt = b.toNat := by
      have := BitVec.toInt_eq_toNat_cond b; split_ifs at this <;> omega
    rw [ha_eq, hb_eq, Int.tdiv_ofNat, BitVec.ofInt_ofNat]
    rfl
  · have h_msb_a : a.msb = false := BitVec.msb_eq_false_iff_two_mul_lt.mpr (by
      have := BitVec.toInt_eq_toNat_cond a; split_ifs at this <;> omega)
    have h_msb_b : b.msb = true := by
      cases hm : b.msb
      · exfalso
        have := BitVec.msb_eq_false_iff_two_mul_lt.mp hm
        have hti := BitVec.toInt_eq_toNat_cond b; split_ifs at hti <;> omega
      · rfl
    simp only [h_msb_a, h_msb_b]
    have ha_eq : a.toInt = (a.toNat : Int) := by
      have := BitVec.toInt_eq_toNat_cond a; split_ifs at this <;> omega
    have hb_neg : b.toInt = -(((-b).toNat : Nat) : Int) := by
      have hti := BitVec.toInt_eq_toNat_cond b
      have hneg : (-b).toNat = 2 ^ w.bits - b.toNat := by
        have hb_nz : b.toNat ≠ 0 := by omega
        simp [BitVec.toNat_neg, Nat.mod_eq_of_lt (show 2 ^ w.bits - b.toNat < 2 ^ w.bits by omega)]
      split_ifs at hti <;> omega
    rw [ha_eq, hb_neg]
    cases hn : (-b).toNat with
    | zero => simp [Int.tdiv]
    | succ k =>
      have : -(((k + 1 : Nat) : Int)) = Int.negSucc k := rfl
      rw [this, Int.tdiv]
      simp only [BitVec.ofInt_neg, BitVec.ofInt_ofNat]
      rfl
  · have h_msb_a : a.msb = true := by
      cases hm : a.msb
      · exfalso
        have := BitVec.msb_eq_false_iff_two_mul_lt.mp hm
        have hti := BitVec.toInt_eq_toNat_cond a; split_ifs at hti <;> omega
      · rfl
    have h_msb_b : b.msb = false := BitVec.msb_eq_false_iff_two_mul_lt.mpr (by
      have := BitVec.toInt_eq_toNat_cond b; split_ifs at this <;> omega)
    simp only [h_msb_a, h_msb_b]
    have hb_eq : b.toInt = (b.toNat : Int) := by
      have := BitVec.toInt_eq_toNat_cond b; split_ifs at this <;> omega
    have ha_neg : a.toInt = -(((-a).toNat : Nat) : Int) := by
      have hti := BitVec.toInt_eq_toNat_cond a
      have hneg : (-a).toNat = 2 ^ w.bits - a.toNat := by
        have ha_nz : a.toNat ≠ 0 := by omega
        simp [BitVec.toNat_neg, Nat.mod_eq_of_lt (show 2 ^ w.bits - a.toNat < 2 ^ w.bits by omega)]
      split_ifs at hti <;> omega
    rw [ha_neg, hb_eq]
    cases hm : (-a).toNat with
    | zero => simp [Int.tdiv]
    | succ k =>
      have : -(((k + 1 : Nat) : Int)) = Int.negSucc k := rfl
      rw [this, Int.tdiv]
      simp only [BitVec.ofInt_neg, BitVec.ofInt_ofNat]
      rfl
  · have h_msb_a : a.msb = true := by
      cases hm : a.msb
      · exfalso
        have := BitVec.msb_eq_false_iff_two_mul_lt.mp hm
        have hti := BitVec.toInt_eq_toNat_cond a; split_ifs at hti <;> omega
      · rfl
    have h_msb_b : b.msb = true := by
      cases hm : b.msb
      · exfalso
        have := BitVec.msb_eq_false_iff_two_mul_lt.mp hm
        have hti := BitVec.toInt_eq_toNat_cond b; split_ifs at hti <;> omega
      · rfl
    simp only [h_msb_a, h_msb_b]
    have ha_neg : a.toInt = -(((-a).toNat : Nat) : Int) := by
      have hti := BitVec.toInt_eq_toNat_cond a
      have hneg : (-a).toNat = 2 ^ w.bits - a.toNat := by
        have ha_nz : a.toNat ≠ 0 := by omega
        simp [BitVec.toNat_neg, Nat.mod_eq_of_lt (show 2 ^ w.bits - a.toNat < 2 ^ w.bits by omega)]
      split_ifs at hti <;> omega
    have hb_neg : b.toInt = -(((-b).toNat : Nat) : Int) := by
      have hti := BitVec.toInt_eq_toNat_cond b
      have hneg : (-b).toNat = 2 ^ w.bits - b.toNat := by
        have hb_nz : b.toNat ≠ 0 := by omega
        simp [BitVec.toNat_neg, Nat.mod_eq_of_lt (show 2 ^ w.bits - b.toNat < 2 ^ w.bits by omega)]
      split_ifs at hti <;> omega
    rw [ha_neg, hb_neg]
    cases hm : (-a).toNat with
    | zero => simp [Int.tdiv]
    | succ ka =>
      cases hn : (-b).toNat with
      | zero => simp [Int.tdiv]
      | succ kb =>
        have ha' : -(((ka + 1 : Nat) : Int)) = Int.negSucc ka := rfl
        have hb' : -(((kb + 1 : Nat) : Int)) = Int.negSucc kb := rfl
        rw [ha', hb', Int.tdiv, BitVec.ofInt_ofNat]
        rfl

theorem bvSRem_eq_srem (w : IntWidth) (a b : BitVec w.bits) :
    bvSRem w a b = BitVec.srem a b := by
  unfold bvSRem
  rw [bvSigned_eq_toInt, bvSigned_eq_toInt]
  have h_mod : (if 0 ≤ Int.tmod a.toInt b.toInt then
      BitVec.ofNat w.bits (Int.tmod a.toInt b.toInt).toNat
    else
      BitVec.ofNat w.bits (2 ^ w.bits - (-Int.tmod a.toInt b.toInt).toNat % 2 ^ w.bits)) =
      BitVec.ofInt w.bits (Int.tmod a.toInt b.toInt) := by
    set r := Int.tmod a.toInt b.toInt
    by_cases hr : 0 ≤ r
    · simp only [hr, ↓reduceIte]
      have hr_eq : r = Int.ofNat r.toNat := (Int.toNat_of_nonneg hr).symm
      rw [hr_eq, BitVec.ofInt_ofNat]
    · simp only [hr, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, BitVec.toNat_ofInt]
      set n := (-r).toNat
      have hn : r = -(n : Int) := by omega
      rw [hn]
      have hpos : (0 : Nat) < 2 ^ w.bits := Nat.pos_of_ne_zero (by positivity)
      by_cases hrem : n % 2 ^ w.bits = 0
      · simp [hrem]
        have hdvd : ((2 ^ w.bits : Nat) : Int) ∣ (n : Int) := by
          exact_mod_cast Nat.dvd_of_mod_eq_zero hrem
        rcases hdvd with ⟨k, hk⟩
        rw [hk]
        simp [Int.neg_mul_eq_neg_mul]
      · have hlt : n % 2 ^ w.bits < 2 ^ w.bits := Nat.mod_lt _ hpos
        have hsub_lt : 2 ^ w.bits - n % 2 ^ w.bits < 2 ^ w.bits := by omega
        rw [Nat.mod_eq_of_lt hsub_lt]
        have h_emod : (-(n : Int)) % ((2 ^ w.bits : Nat) : Int) =
            ((2 ^ w.bits : Nat) : Int) - ((n % 2 ^ w.bits : Nat) : Int) := by
          have h1 : (n : Int) = ((2 ^ w.bits : Nat) : Int) * (n / 2 ^ w.bits : Nat) + (n % 2 ^ w.bits : Nat) := by
            exact_mod_cast (Nat.div_add_mod n (2 ^ w.bits)).symm
          have hrem_pos : (0 : Int) < (n % 2 ^ w.bits : Nat) := by
            exact_mod_cast Nat.pos_of_ne_zero hrem
          have hrem_lt : ((n % 2 ^ w.bits : Nat) : Int) < (2 ^ w.bits : Nat) := by
            exact_mod_cast hlt
          have h_decomp : -(n : Int) =
              (((2 ^ w.bits : Nat) : Int) - (n % 2 ^ w.bits : Nat)) +
              ((2 ^ w.bits : Nat) : Int) * (-((n / 2 ^ w.bits : Nat) : Int) - 1) := by
            linarith
          rw [h_decomp, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
        rw [h_emod]
        omega
  rw [h_mod]
  unfold BitVec.srem BitVec.urem
  by_cases ha : 0 ≤ a.toInt <;> by_cases hb : 0 ≤ b.toInt
  · have h_msb_a : a.msb = false := BitVec.msb_eq_false_iff_two_mul_lt.mpr (by
      have := BitVec.toInt_eq_toNat_cond a; split_ifs at this <;> omega)
    have h_msb_b : b.msb = false := BitVec.msb_eq_false_iff_two_mul_lt.mpr (by
      have := BitVec.toInt_eq_toNat_cond b; split_ifs at this <;> omega)
    simp only [h_msb_a, h_msb_b]
    have ha_eq : a.toInt = a.toNat := by
      have := BitVec.toInt_eq_toNat_cond a; split_ifs at this <;> omega
    have hb_eq : b.toInt = b.toNat := by
      have := BitVec.toInt_eq_toNat_cond b; split_ifs at this <;> omega
    rw [ha_eq, hb_eq, Int.tmod_ofNat, BitVec.ofInt_ofNat]
    rfl
  · have h_msb_a : a.msb = false := BitVec.msb_eq_false_iff_two_mul_lt.mpr (by
      have := BitVec.toInt_eq_toNat_cond a; split_ifs at this <;> omega)
    have h_msb_b : b.msb = true := by
      cases hm : b.msb
      · exfalso
        have := BitVec.msb_eq_false_iff_two_mul_lt.mp hm
        have hti := BitVec.toInt_eq_toNat_cond b; split_ifs at hti <;> omega
      · rfl
    simp only [h_msb_a, h_msb_b]
    have ha_eq : a.toInt = (a.toNat : Int) := by
      have := BitVec.toInt_eq_toNat_cond a; split_ifs at this <;> omega
    have hb_neg : b.toInt = -(((-b).toNat : Nat) : Int) := by
      have hti := BitVec.toInt_eq_toNat_cond b
      have hneg : (-b).toNat = 2 ^ w.bits - b.toNat := by
        have hb_nz : b.toNat ≠ 0 := by omega
        simp [BitVec.toNat_neg, Nat.mod_eq_of_lt (show 2 ^ w.bits - b.toNat < 2 ^ w.bits by omega)]
      split_ifs at hti <;> omega
    rw [ha_eq, hb_neg]
    cases hn : (-b).toNat with
    | zero => simp [Int.tmod]
    | succ k =>
      have : -(((k + 1 : Nat) : Int)) = Int.negSucc k := rfl
      rw [this, Int.tmod, BitVec.ofInt_ofNat]
      rfl
  · have h_msb_a : a.msb = true := by
      cases hm : a.msb
      · exfalso
        have := BitVec.msb_eq_false_iff_two_mul_lt.mp hm
        have hti := BitVec.toInt_eq_toNat_cond a; split_ifs at hti <;> omega
      · rfl
    have h_msb_b : b.msb = false := BitVec.msb_eq_false_iff_two_mul_lt.mpr (by
      have := BitVec.toInt_eq_toNat_cond b; split_ifs at this <;> omega)
    simp only [h_msb_a, h_msb_b]
    have hb_eq : b.toInt = (b.toNat : Int) := by
      have := BitVec.toInt_eq_toNat_cond b; split_ifs at this <;> omega
    have ha_neg : a.toInt = -(((-a).toNat : Nat) : Int) := by
      have hti := BitVec.toInt_eq_toNat_cond a
      have hneg : (-a).toNat = 2 ^ w.bits - a.toNat := by
        have ha_nz : a.toNat ≠ 0 := by omega
        simp [BitVec.toNat_neg, Nat.mod_eq_of_lt (show 2 ^ w.bits - a.toNat < 2 ^ w.bits by omega)]
      split_ifs at hti <;> omega
    rw [ha_neg, hb_eq]
    cases hm : (-a).toNat with
    | zero => simp [Int.tmod]
    | succ k =>
      have : -(((k + 1 : Nat) : Int)) = Int.negSucc k := rfl
      rw [this, Int.tmod]
      simp only [BitVec.ofInt_neg, BitVec.ofInt_ofNat]
      rfl
  · have h_msb_a : a.msb = true := by
      cases hm : a.msb
      · exfalso
        have := BitVec.msb_eq_false_iff_two_mul_lt.mp hm
        have hti := BitVec.toInt_eq_toNat_cond a; split_ifs at hti <;> omega
      · rfl
    have h_msb_b : b.msb = true := by
      cases hm : b.msb
      · exfalso
        have := BitVec.msb_eq_false_iff_two_mul_lt.mp hm
        have hti := BitVec.toInt_eq_toNat_cond b; split_ifs at hti <;> omega
      · rfl
    simp only [h_msb_a, h_msb_b]
    have ha_neg : a.toInt = -(((-a).toNat : Nat) : Int) := by
      have hti := BitVec.toInt_eq_toNat_cond a
      have hneg : (-a).toNat = 2 ^ w.bits - a.toNat := by
        have ha_nz : a.toNat ≠ 0 := by omega
        simp [BitVec.toNat_neg, Nat.mod_eq_of_lt (show 2 ^ w.bits - a.toNat < 2 ^ w.bits by omega)]
      split_ifs at hti <;> omega
    have hb_neg : b.toInt = -(((-b).toNat : Nat) : Int) := by
      have hti := BitVec.toInt_eq_toNat_cond b
      have hneg : (-b).toNat = 2 ^ w.bits - b.toNat := by
        have hb_nz : b.toNat ≠ 0 := by omega
        simp [BitVec.toNat_neg, Nat.mod_eq_of_lt (show 2 ^ w.bits - b.toNat < 2 ^ w.bits by omega)]
      split_ifs at hti <;> omega
    rw [ha_neg, hb_neg]
    cases hm : (-a).toNat with
    | zero => simp [Int.tmod]
    | succ ka =>
      cases hn : (-b).toNat with
      | zero => simp [Int.tmod]
      | succ kb =>
        have ha' : -(((ka + 1 : Nat) : Int)) = Int.negSucc ka := rfl
        have hb' : -(((kb + 1 : Nat) : Int)) = Int.negSucc kb := rfl
        rw [ha', hb', Int.tmod]
        simp only [BitVec.ofInt_neg, BitVec.ofInt_ofNat]
        rfl

/-! ## Instruction-Level Bisimulation (`stepInstr` ↔ `LLVM.*` & `InstCombine.Op.denote`) -/

theorem stepInstr_add_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (flags : OverflowFlags) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.add dst flags w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w (LLVM.add xa xb (toNoWrapFlags flags)))) := by
  cases xa <;> cases xb <;> cases flags
  all_goals
    simp [stepInstr, stepInstrWith, binResult, ha, hb, toLLVMVal, toNoWrapFlags,
      LLVM.add, LLVM.add?, PoisonOr.bind, Bind.bind, Pure.pure, flagsOverflow,
      addOverflowNSW_eq_saddOverflow, addOverflowNUW_eq_uaddOverflow]
    try split_ifs <;> simp_all [toLLVMVal]

theorem stepInstr_sub_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (flags : OverflowFlags) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.sub dst flags w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w (LLVM.sub xa xb (toNoWrapFlags flags)))) := by
  cases xa <;> cases xb <;> cases flags
  all_goals
    simp [stepInstr, stepInstrWith, binResult, ha, hb, toLLVMVal, toNoWrapFlags,
      LLVM.sub, LLVM.sub?, PoisonOr.bind, Bind.bind, Pure.pure, flagsOverflow,
      subOverflowNSW_eq_ssubOverflow, subOverflowNUW_eq_usubOverflow]
    try split_ifs <;> simp_all [toLLVMVal]

theorem stepInstr_mul_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (flags : OverflowFlags) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.mul dst flags w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w (LLVM.mul xa xb (toNoWrapFlags flags)))) := by
  cases xa <;> cases xb <;> cases flags
  all_goals
    simp [stepInstr, stepInstrWith, binResult, ha, hb, toLLVMVal, toNoWrapFlags,
      LLVM.mul, LLVM.mul?, PoisonOr.bind, Bind.bind, Pure.pure, flagsOverflow,
      mulOverflowNSW_eq_smulOverflow, mulOverflowNUW_eq_umulOverflow]
    try split_ifs <;> simp_all [toLLVMVal]

theorem stepInstr_and_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.and_ dst w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w (LLVM.and xa xb))) := by
  cases xa <;> cases xb <;>
    simp [stepInstr, stepInstrWith, binResult, ha, hb, toLLVMVal, LLVM.and, LLVM.and?,
      PoisonOr.bind, Bind.bind, flagsOverflow]

theorem stepInstr_or_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.or_ dst w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w (LLVM.or xa xb { disjoint := false }))) := by
  cases xa <;> cases xb <;>
    simp [stepInstr, stepInstrWith, binResult, ha, hb, toLLVMVal, LLVM.or, LLVM.or?,
      PoisonOr.bind, Bind.bind, flagsOverflow]

theorem stepInstr_xor_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.xor dst w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w (LLVM.xor xa xb))) := by
  cases xa <;> cases xb <;>
    simp [stepInstr, stepInstrWith, binResult, ha, hb, toLLVMVal, LLVM.xor, LLVM.xor?,
      PoisonOr.bind, Bind.bind, flagsOverflow]

theorem stepInstr_shl_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (flags : OverflowFlags) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.shl dst flags w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w (LLVM.shl xa xb (toNoWrapFlags flags)))) := by
  cases xa with
  | poison =>
    cases xb <;>
      simp [stepInstr, stepInstrWith, shiftResult, ha, hb, toLLVMVal, LLVM.shl,
        PoisonOr.bind, Bind.bind]
  | value va =>
    cases xb with
    | poison =>
      simp [stepInstr, stepInstrWith, shiftResult, ha, hb, toLLVMVal, LLVM.shl,
        PoisonOr.bind, Bind.bind]
    | value vb =>
      have h_ge_iff : (vb ≥ (w.bits : BitVec w.bits)) ↔ w.bits ≤ vb.toNat := by
        simp [BitVec.le_def, BitVec.toNat_ofNat]
      by_cases h_over : w.bits ≤ vb.toNat
      · have h_bv_ge : vb ≥ (w.bits : BitVec w.bits) := h_ge_iff.mpr h_over
        cases flags <;>
          simp [stepInstr, stepInstrWith, shiftResult, ha, hb, toLLVMVal, toNoWrapFlags,
            LLVM.shl, LLVM.shl?, PoisonOr.bind, Bind.bind, h_over, h_bv_ge] <;>
          split_ifs <;> rfl
      · have h_lt : vb.toNat < w.bits := Nat.lt_of_not_ge h_over
        have h_not_ge : ¬(vb ≥ (w.bits : BitVec w.bits)) := fun hg => h_over (h_ge_iff.mp hg)
        have h_nsw := shlOverflowNSW_eq_mlir w va vb h_lt
        have h_sh_eq : (va <<< vb : BitVec w.bits) = va <<< vb.toNat := rfl
        cases flags <;>
          simp [stepInstr, stepInstrWith, shiftResult, ha, hb, toLLVMVal, toNoWrapFlags,
            LLVM.shl, LLVM.shl?, PoisonOr.bind, Bind.bind, h_over, h_not_ge,
            flagsOverflow, h_nsw, shlOverflowNUW] <;>
          split_ifs <;> simp_all [toLLVMVal]

theorem stepInstr_lshr_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (exact : Bool) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.lshr dst exact w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w (LLVM.lshr xa xb { exact := exact }))) := by
  cases xa with
  | poison =>
    cases xb <;>
      simp [stepInstr, stepInstrWith, shiftResult, ha, hb, toLLVMVal, LLVM.lshr,
        PoisonOr.bind, Bind.bind]
  | value va =>
    cases xb with
    | poison =>
      simp [stepInstr, stepInstrWith, shiftResult, ha, hb, toLLVMVal, LLVM.lshr,
        PoisonOr.bind, Bind.bind]
    | value vb =>
      have h_ge_iff : (vb ≥ (w.bits : BitVec w.bits)) ↔ w.bits ≤ vb.toNat := by
        simp [BitVec.le_def, BitVec.toNat_ofNat]
      by_cases h_over : w.bits ≤ vb.toNat
      · have h_bv_ge : vb ≥ (w.bits : BitVec w.bits) := h_ge_iff.mpr h_over
        cases exact <;>
          simp [stepInstr, stepInstrWith, shiftResult, ha, hb, toLLVMVal,
            LLVM.lshr, LLVM.lshr?, PoisonOr.bind, Bind.bind, h_over, h_bv_ge] <;>
          split_ifs <;> rfl
      · have h_lt : vb.toNat < w.bits := Nat.lt_of_not_ge h_over
        have h_not_ge : ¬(vb ≥ (w.bits : BitVec w.bits)) := fun hg => h_over (h_ge_iff.mp hg)
        have h_ex := shiftedOut_iff_ushift_roundtrip w va vb h_lt
        cases exact <;>
          simp [stepInstr, stepInstrWith, shiftResult, ha, hb, toLLVMVal,
            LLVM.lshr, LLVM.lshr?, PoisonOr.bind, Bind.bind, h_over, h_not_ge,
            flagsOverflow, h_ex] <;>
          split_ifs <;> simp_all [toLLVMVal]

theorem stepInstr_ashr_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (exact : Bool) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.ashr dst exact w aOp bOp) =
      .inr (bindReg st dst (toLLVMVal w (LLVM.ashr xa xb { exact := exact }))) := by
  cases xa with
  | poison =>
    cases xb <;>
      simp [stepInstr, stepInstrWith, shiftResult, ha, hb, toLLVMVal, LLVM.ashr,
        PoisonOr.bind, Bind.bind]
  | value va =>
    cases xb with
    | poison =>
      simp [stepInstr, stepInstrWith, shiftResult, ha, hb, toLLVMVal, LLVM.ashr,
        PoisonOr.bind, Bind.bind]
    | value vb =>
      have h_ge_iff : (vb ≥ (w.bits : BitVec w.bits)) ↔ w.bits ≤ vb.toNat := by
        simp [BitVec.le_def, BitVec.toNat_ofNat]
      by_cases h_over : w.bits ≤ vb.toNat
      · have h_bv_ge : vb ≥ (w.bits : BitVec w.bits) := h_ge_iff.mpr h_over
        cases exact <;>
          simp [stepInstr, stepInstrWith, shiftResult, ha, hb, toLLVMVal,
            LLVM.ashr, LLVM.ashr?, PoisonOr.bind, Bind.bind, h_over, h_bv_ge] <;>
          split_ifs <;> rfl
      · have h_lt : vb.toNat < w.bits := Nat.lt_of_not_ge h_over
        have h_not_ge : ¬(vb ≥ (w.bits : BitVec w.bits)) := fun hg => h_over (h_ge_iff.mp hg)
        have h_ex := shiftedOut_iff_ushift_roundtrip w va vb h_lt
        have h_ashr_eq : va.sshiftRight vb.toNat = va.sshiftRight' vb := rfl
        cases exact <;>
          simp [stepInstr, stepInstrWith, shiftResult, ha, hb, toLLVMVal,
            LLVM.ashr, LLVM.ashr?, PoisonOr.bind, Bind.bind, h_over, h_not_ge,
            flagsOverflow, h_ex, h_ashr_eq] <;>
          split_ifs <;> simp_all [toLLVMVal]

theorem stepInstr_icmp_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (pred : ICmpPred) (w : IntWidth) (aOp bOp : Operand)
    (xa xb : LLVM.IntW w.bits)
    (ha : evalOperand st aOp = toLLVMVal w xa)
    (hb : evalOperand st bOp = toLLVMVal w xb) :
    stepInstr mod_ fuel st (.icmp dst pred (.int w) aOp bOp) =
      .inr (bindReg st dst (toLLVMVal .i1 (LLVM.icmp (toIntPred pred) xa xb))) := by
  cases xa with
  | poison =>
    cases xb <;>
      simp [stepInstr, stepInstrWith, ha, hb, toLLVMVal, LLVM.icmp, PoisonOr.bind, Bind.bind]
  | value va =>
    cases xb with
    | poison =>
      simp [stepInstr, stepInstrWith, ha, hb, toLLVMVal, LLVM.icmp, PoisonOr.bind, Bind.bind]
    | value vb =>
      simp [stepInstr, stepInstrWith, ha, hb, toLLVMVal, LLVM.icmp, LLVM.icmp?,
        PoisonOr.bind, Bind.bind, icmpEval_eq_mlir, IntWidth.bits]
      cases LLVM.icmp' (toIntPred pred) va vb <;> rfl

theorem stepInstr_select_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (condOp : Operand) (w : IntWidth) (tOp eOp : Operand)
    (xc : LLVM.IntW 1) (xt xe : LLVM.IntW w.bits)
    (hc : evalOperand st condOp = toLLVMVal .i1 xc)
    (ht : evalTypedOperand st (.int w) tOp = toLLVMVal w xt)
    (he : evalTypedOperand st (.int w) eOp = toLLVMVal w xe) :
    stepInstr mod_ fuel st (.select dst condOp (.int w) tOp eOp) =
      .inr (bindReg st dst (toLLVMVal w (LLVM.select xc xt xe))) := by
  cases xc with
  | poison =>
    simp [stepInstr, stepInstrWith, hc, toLLVMVal, LLVM.select, PoisonOr.bind, Bind.bind]
  | value c =>
    by_cases hc1 : c = 1#1
    · subst hc1
      simp [stepInstr, stepInstrWith, hc, ht, toLLVMVal, LLVM.select, PoisonOr.bind, Bind.bind]
    · simp [stepInstr, stepInstrWith, hc, he, hc1, toLLVMVal, LLVM.select, PoisonOr.bind, Bind.bind]

theorem stepInstr_zext_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (srcW dstW : IntWidth) (op : Operand)
    (x : LLVM.IntW srcW.bits)
    (h_le : srcW.bits ≤ dstW.bits)
    (hx : evalOperand st op = toLLVMVal srcW x) :
    stepInstr mod_ fuel st (.zext dst srcW op dstW) =
      .inr (bindReg st dst (toLLVMVal dstW (LLVM.zext dstW.bits x { nneg := false }))) := by
  cases x <;>
    simp [stepInstr, stepInstrWith, hx, h_le, toLLVMVal, LLVM.zext, LLVM.zext?,
      PoisonOr.bind, Bind.bind]

theorem stepInstr_sext_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (srcW dstW : IntWidth) (op : Operand)
    (x : LLVM.IntW srcW.bits)
    (h_le : srcW.bits ≤ dstW.bits)
    (hx : evalOperand st op = toLLVMVal srcW x) :
    stepInstr mod_ fuel st (.sext dst srcW op dstW) =
      .inr (bindReg st dst (toLLVMVal dstW (LLVM.sext dstW.bits x))) := by
  cases x <;>
    simp [stepInstr, stepInstrWith, hx, h_le, toLLVMVal, LLVM.sext, LLVM.sext?,
      PoisonOr.bind, Bind.bind]

theorem stepInstr_trunc_bisim (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst : RegName) (srcW dstW : IntWidth) (op : Operand)
    (x : LLVM.IntW srcW.bits)
    (h_le : dstW.bits ≤ srcW.bits)
    (hx : evalOperand st op = toLLVMVal srcW x) :
    stepInstr mod_ fuel st (.trunc dst srcW op dstW) =
      .inr (bindReg st dst (toLLVMVal dstW (LLVM.trunc dstW.bits x { nsw := false, nuw := false }))) := by
  cases x <;>
    simp [stepInstr, stepInstrWith, hx, h_le, toLLVMVal, LLVM.trunc, LLVM.trunc?,
      PoisonOr.bind, Bind.bind]

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
  cases xb with
  | poison =>
    simp [stepInstr, stepInstrWith, divOrRem, hb, toLLVMVal]
  | value vb =>
    by_cases h0 : vb = 0#w.bits
    · subst h0
      simp [stepInstr, stepInstrWith, divOrRem, hb, toLLVMVal]
    · simp only [h0, ↓reduceIte]
      cases xa with
      | poison =>
        simp [stepInstr, stepInstrWith, divOrRem, ha, hb, h0, toLLVMVal,
          LLVM.udiv, PoisonOr.bind, Bind.bind]
      | value va =>
        have h_umod : va.umod vb = va % vb := rfl
        cases exact <;>
          simp [stepInstr, stepInstrWith, divOrRem, ha, hb, h0, toLLVMVal,
            LLVM.udiv, LLVM.udiv?, PoisonOr.bind, Bind.bind, h_umod] <;>
          split_ifs <;> simp_all [toLLVMVal]

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
  cases xb with
  | poison =>
    simp [stepInstr, stepInstrWith, divOrRem, hb, toLLVMVal]
  | value vb =>
    by_cases h0 : vb = 0#w.bits
    · subst h0
      simp [stepInstr, stepInstrWith, divOrRem, hb, toLLVMVal]
    · simp only [h0, ↓reduceIte]
      cases xa <;>
        simp [stepInstr, stepInstrWith, divOrRem, ha, hb, h0, toLLVMVal,
          LLVM.urem, LLVM.urem?, PoisonOr.bind, Bind.bind]

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
  have h_intMin : ¬(va = BitVec.intMin w.bits ∧ vb = -1) := by
    rintro ⟨hmin, hm1⟩
    unfold sdivOverflow at hno_ov
    rw [bvSigned_eq_toInt, bvSigned_eq_toInt] at hno_ov
    have hpos : 1 < w.bits := by have := w.bits_pos; omega
    have hva_int : va.toInt = -((2 : Int) ^ (w.bits - 1)) := by
      subst hmin
      simpa using BitVec.toInt_intMin (w := w.bits)
    have hvb_int : vb.toInt = -1 := by
      subst hm1
      exact BitVec.toInt_neg_one (by omega)
    simp [hva_int, hvb_int] at hno_ov
  have h_smod : va.smod vb = BitVec.srem va vb := rfl
  have h_not_mlir_ov : (vb == 0 || (decide (w.bits ≠ 1) && va == BitVec.intMin w.bits && vb == -1)) = false := by
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, Bool.and_eq_false_iff,
      decide_eq_true_eq]
    refine ⟨hb0, ?_⟩
    by_cases h1 : va = BitVec.intMin w.bits
    · right; intro h2; exact h_intMin ⟨h1, h2⟩
    · left; right; exact h1
  cases exact <;>
    simp [stepInstr, stepInstrWith, divOrRem, ha, hb, hb0, hno_ov, toLLVMVal,
      LLVM.sdiv, LLVM.sdiv?, PoisonOr.bind, Bind.bind, bvSDiv_eq_sdiv, bvSRem_eq_srem,
      h_smod, h_not_mlir_ov] <;>
    split_ifs <;> simp_all [toLLVMVal]

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

/-! ## Compositional Straight-Line Block Bisimulation (`execInstrs`) -/

/-- Inductive straight-line SSA trace relating `LLVMAst.execInstrs` to a chain of `LLVM.IntW`
denotations in `opencompl/lean-mlir`. -/
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
    unfold execInstrs execInstrsWith at *
    unfold stepInstr at h_step
    rw [h_step]
    exact ih

end LeanMLIRBridge
