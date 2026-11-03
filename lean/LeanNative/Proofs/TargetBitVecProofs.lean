import LeanNative.Semantics.Eval
import LeanNative.Backend.TargetIR

/-!
# Shared 64-Bit Word & Target-IR Lemmas (`LeanNative.Proofs.TargetBitVecProofs`)

Shared zero-`ofReduceBool` `UInt64` ↔ `BitVec 64` semantic bridge lemmas (masked shifts,
sign-bit arithmetic right shift, zero-divisor-guarded unsigned division/remainder, bitwise
complement, boolean word encoding) and `TargetIR.ppInt` injectivity used by both
`LLVMLowerProofs` and `StableHLOLowerProofs`.
-/

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend.TargetIR

/-! ## 1. `ppInt` Injectivity -/

theorem ppInt_injective (a b : Nat) (h : ppInt a = ppInt b) : a = b := by
  have hlist : natDigits a = natDigits b := by
    simpa [ppInt] using congrArg String.toList h
  have hrd := congrArg (fun xs => (readDigits 0 xs).1) hlist
  simpa [readDigits_natDigits_eof] using hrd

/-! ## 2. 64-Bit Machine-Word Arithmetic & Shift Lemmas (Zero `ofReduceBool`) -/

theorem bv64_and_63_toNat (b : BitVec 64) : (b &&& 63#64).toNat = b.toNat % 64 := by
  rw [BitVec.toNat_and]
  have h63 : (63#64 : BitVec 64).toNat = 2 ^ 6 - 1 := rfl
  rw [h63, Nat.and_two_pow_sub_one_eq_mod]

theorem bv64_and_63_lt_64 (b : BitVec 64) : (b &&& 63#64).toNat < 64 := by
  rw [bv64_and_63_toNat]
  exact Nat.mod_lt b.toNat (by omega)

theorem bv64_and_63_eq_mod (b : BitVec 64) : (b &&& 63#64) = b % 64#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [bv64_and_63_toNat, BitVec.toNat_umod]
  rfl

theorem u64_shl_masked_bv (a b : UInt64) :
    a.toBitVec <<< (b.toBitVec &&& 63#64) = (a <<< b).toBitVec := by
  rw [bv64_and_63_eq_mod]
  rfl

theorem u64_shr_masked_bv (a b : UInt64) :
    a.toBitVec >>> (b.toBitVec &&& 63#64) = (a >>> b).toBitVec := by
  rw [bv64_and_63_eq_mod]
  rfl

/-- LNIR 64-bit arithmetic right shift value (`evalBinOp .sar (.u64 a) (.u64 b)`). -/
def lnirSar64 (a b : UInt64) : UInt64 :=
  let sh := b &&& 63
  let shifted := a >>> sh
  let signBit := (a >>> 63) &&& 1
  if signBit != 0 && sh != 0 then
    shifted ||| (0xffffffffffffffff <<< (64 - sh))
  else
    shifted

theorem bv64_signBit_eq_msb (x : BitVec 64) :
    (((x >>> 63#64) &&& 1#64) != 0#64) = x.msb := by
  rw [BitVec.msb_eq_toNat]
  have hxlt : x.toNat < 2 ^ 64 := x.isLt
  have hsh : ((x >>> 63#64) &&& 1#64).toNat = (x.toNat / 2 ^ 63) &&& 1 := by
    rw [BitVec.toNat_and, BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rfl
  by_cases hge : 2 ^ 63 ≤ x.toNat
  · have hdiv : x.toNat / 2 ^ 63 = 1 := by omega
    have hval : (x >>> 63#64) &&& 1#64 = 1#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [hsh, hdiv]
      rfl
    have hne : ((1#64 : BitVec 64) != 0#64) = true := by
      apply bne_iff_ne.mpr
      intro hc
      nomatch hc
    rw [hval, hne, decide_eq_true hge]
  · have hdiv : x.toNat / 2 ^ 63 = 0 := by omega
    have hval : (x >>> 63#64) &&& 1#64 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [hsh, hdiv]
      rfl
    rw [hval, bne_self_eq_false, decide_eq_false hge]

theorem u64_ashr_masked_bv (a b : UInt64) :
    a.toBitVec.sshiftRight (b.toBitVec &&& 63#64).toNat = (lnirSar64 a b).toBitVec := by
  let s := (b.toBitVec &&& 63#64).toNat
  have hs_def : s = (b.toBitVec &&& 63#64).toNat := rfl
  rw [← hs_def]
  unfold lnirSar64
  dsimp only
  have hs_lt : s < 64 := bv64_and_63_lt_64 b.toBitVec
  have hsh_bv : (b &&& 63).toBitVec = b.toBitVec &&& 63#64 := rfl
  have hsh_nz : ((b &&& 63) != 0) = decide (s ≠ 0) := by
    by_cases hsz : s = 0
    · have hbv_z : (b &&& 63) = 0 := by
        apply UInt64.eq_of_toBitVec_eq
        apply BitVec.eq_of_toNat_eq
        simpa [hsh_bv, ← hs_def] using hsz
      simp [hbv_z, hsz]
    · have hbv_nz : (b &&& 63) ≠ 0 := by
        intro hz
        apply hsz
        have : (b &&& 63).toBitVec.toNat = 0 := by simp [hz]
        simpa [hsh_bv, ← hs_def] using this
      simp [hbv_nz, hsz]
  have hsign : (((a >>> 63) &&& 1) != 0) = a.toBitVec.msb := by
    have hsb : (((a >>> 63) &&& 1) != 0) = (((a.toBitVec >>> 63#64) &&& 1#64) != 0#64) := rfl
    rw [hsb, bv64_signBit_eq_msb]
  have hshift_eq : (a >>> (b &&& 63)).toBitVec = a.toBitVec >>> s := by
    have hmod : (b &&& 63).toBitVec % 64#64 = b.toBitVec &&& 63#64 := by
      rw [hsh_bv, ← bv64_and_63_eq_mod]
      apply BitVec.eq_of_toNat_eq
      rw [bv64_and_63_toNat, bv64_and_63_toNat, Nat.mod_mod]
    change a.toBitVec >>> ((b &&& 63).toBitVec % 64#64) = a.toBitVec >>> s
    rw [hmod, BitVec.ushiftRight_eq', ← hs_def]
  rw [hsign, hsh_nz]
  cases hmsb : a.toBitVec.msb
  · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, hshift_eq]
    ext i hi
    rw [BitVec.getElem_sshiftRight, BitVec.getElem_ushiftRight, hmsb]
    by_cases hsi : s + i < 64
    · simp [hsi, BitVec.getLsbD_eq_getElem]
    · simp [hsi, BitVec.getLsbD_of_ge a.toBitVec (s + i) (by omega)]
  · cases Nat.eq_zero_or_pos s with
    | inl hsz =>
      simp only [hsz, ne_eq, not_true_eq_false, decide_false, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte, hshift_eq]
      ext i hi
      rw [BitVec.getElem_sshiftRight, BitVec.getElem_ushiftRight, hmsb]
      simp [hi, BitVec.getLsbD_eq_getElem]
    | inr hsp =>
      have hsne : decide (s ≠ 0) = true := decide_eq_true (by omega)
      simp only [Bool.true_and, hsne, ↓reduceIte]
      have hall : (0xffffffffffffffff : UInt64).toBitVec = BitVec.allOnes 64 := by
        apply BitVec.eq_of_toNat_eq
        rfl
      have hsub_mod : ((64 - (b &&& 63)).toBitVec % 64#64).toNat = 64 - s := by
        have h64s : (64 - (b &&& 63)).toBitVec.toNat = 64 - s := by
          change ((64#64 : BitVec 64) - (b &&& 63).toBitVec).toNat = 64 - s
          rw [hsh_bv, BitVec.toNat_sub_of_le]
          · change 64 - s = 64 - s; rfl
          · rw [BitVec.le_def]
            change s ≤ 64
            omega
        rw [BitVec.toNat_umod, h64s]
        change (64 - s) % 64 = 64 - s
        exact Nat.mod_eq_of_lt (by omega)
      have hmask : ((0xffffffffffffffff : UInt64) <<< (64 - (b &&& 63))).toBitVec =
          (BitVec.allOnes 64) <<< (64 - s) := by
        change (0xffffffffffffffff : UInt64).toBitVec <<< ((64 - (b &&& 63)).toBitVec % 64#64) = _
        rw [hall, BitVec.shiftLeft_eq', hsub_mod]
      change a.toBitVec.sshiftRight s =
        ((a >>> (b &&& 63)).toBitVec) ||| ((0xffffffffffffffff : UInt64) <<< (64 - (b &&& 63))).toBitVec
      rw [hshift_eq, hmask]
      ext i hi
      rw [BitVec.getElem_sshiftRight, hmsb, BitVec.getElem_or, BitVec.getElem_ushiftRight,
        BitVec.getElem_shiftLeft]
      by_cases hsi : s + i < 64
      · have hlt_sub : i < 64 - s := by omega
        simp [hsi, hlt_sub, BitVec.getLsbD_eq_getElem]
      · have hge_sub : ¬(i < 64 - s) := by omega
        simp only [hsi, ↓reduceDIte, hge_sub]
        rw [BitVec.getElem_allOnes]
        simp

theorem u64_not_xor_allOnes (a : UInt64) :
    a.toBitVec ^^^ (BitVec.ofNat 64 0xffffffffffffffff) = (~~~a).toBitVec := by
  change a.toBitVec ^^^ BitVec.ofNat 64 0xffffffffffffffff = ~~~a.toBitVec
  have hall : BitVec.ofNat 64 0xffffffffffffffff = BitVec.allOnes 64 := by
    apply BitVec.eq_of_toNat_eq
    rfl
  rw [hall]
  ext i hi
  rw [BitVec.getElem_xor, BitVec.getElem_allOnes, BitVec.getElem_not]
  simp

theorem u64_div_guarded_bv (a b : UInt64) :
    (if b.toBitVec == 0#64 then 0#64
     else a.toBitVec / (if b.toBitVec == 0#64 then 1#64 else b.toBitVec)) =
      (a / b).toBitVec := by
  by_cases hb : b = 0
  · subst hb
    change (if (0#64 : BitVec 64) == 0#64 then 0#64 else a.toBitVec / 1#64) = a.toBitVec / 0#64
    simp only [BEq.rfl, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp
  · have hbz : (b.toBitVec == 0#64) = false := by
      apply Bool.eq_false_iff.mpr
      intro heq
      apply hb
      exact UInt64.eq_of_toBitVec_eq (eq_of_beq heq)
    simp [hbz]

theorem u64_mod_guarded_bv (a b : UInt64) :
    (if b.toBitVec == 0#64 then a.toBitVec
     else a.toBitVec % (if b.toBitVec == 0#64 then 1#64 else b.toBitVec)) =
      (a % b).toBitVec := by
  by_cases hb : b = 0
  · subst hb
    change (if (0#64 : BitVec 64) == 0#64 then a.toBitVec else a.toBitVec % 1#64) =
      a.toBitVec % 0#64
    simp only [BEq.rfl, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp
  · have hbz : (b.toBitVec == 0#64) = false := by
      apply Bool.eq_false_iff.mpr
      intro heq
      apply hb
      exact UInt64.eq_of_toBitVec_eq (eq_of_beq heq)
    simp [hbz]

theorem zext_i1_to_i64 (c : Bool) :
    (if c then (1#1 : BitVec 1) else 0#1).zeroExtend 64 = (if c then 1#64 else 0#64) := by
  cases c <;> rfl

theorem bool_word_eq_iff (b1 b2 : Bool) :
    ((if b1 then (1#64 : BitVec 64) else 0#64) == (if b2 then 1#64 else 0#64)) = (b1 == b2) := by
  cases b1 <;> cases b2 <;> rfl

/-- Typed 64-bit word encoding of an LNIR scalar value (`Val`). -/
def encodeScalarTyped : LNIRType → Val → Option (BitVec 64)
  | .i64, .u64 n => some n.toBitVec
  | .i1,  .bool b => some (if b then 1#64 else 0#64)
  | _,    _       => none

/-- Untyped 64-bit word encoding of an LNIR scalar value (`Val`). -/
def encodeScalarVal : Val → Option (BitVec 64)
  | .u64 n => some n.toBitVec
  | .bool b => some (if b then 1#64 else 0#64)
  | _       => none

theorem encodeScalarVal_of_typed (ty : LNIRType) (v : Val) (w : BitVec 64)
    (h : encodeScalarTyped ty v = some w) :
    encodeScalarVal v = some w := by
  cases ty <;> cases v <;> simp [encodeScalarTyped, encodeScalarVal] at h ⊢
  all_goals exact h

theorem typed_i64_inv (v : Val) (w : BitVec 64) (h : encodeScalarTyped .i64 v = some w) :
    ∃ n : UInt64, v = .u64 n ∧ w = n.toBitVec := by
  cases v <;> simp [encodeScalarTyped] at h
  exact ⟨_, rfl, h.symm⟩

theorem typed_i1_inv (v : Val) (w : BitVec 64) (h : encodeScalarTyped .i1 v = some w) :
    ∃ b : Bool, v = .bool b ∧ w = (if b then 1#64 else 0#64) := by
  cases v <;> simp [encodeScalarTyped] at h
  exact ⟨_, rfl, h.symm⟩

end LeanNative.Proofs
