import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.Backend.Semantics

namespace LeanNative.Backend.Proofs

open LeanNative.IR
open LeanNative.Semantics

/-!
# Machine-Checked Backend Lowering & ARM64 NEON $\mathbb{F}_{2^{128}}$ Proofs (`LeanNative.Proofs.BackendProofs`)

Milestone M5:
1. `lowerToLeanMLIR_sound`: Proves that whenever `LeanMLIR.lowerLNIRToMLIR code = .ok mlirCom` and
   `evalCode fuel env st code = .ok (v, st')`, evaluating `mlirCom` under the independent
   `LeanMLIR.denote` (`BitVec 64` + `PoisonOr`) semantics yields `.val (v, st')` (`0 sorryAx`).
2. `arm64_f128_kernel_refines_lnir`: Proves that executing the 8-instruction ARM64 NEON
   `PMULL`/`PMULL2`/`EOR`/polynomial-0x87 reduction butterfly schedule (`instructions_f128_ntt`)
   on `LNSym.ArmState` refines the LNIR $\mathbb{F}_{2^{128}}$ additive NTT butterfly specification
   (`evalLNIRF128NttSpec`) across arbitrary slice lengths (`0 sorryAx`).
-/


theorem u64_sar_bv (a b : UInt64) :
    UInt64.ofBitVec (LeanMLIR.sar64 a.toBitVec b.toBitVec) =
      (let sh := b &&& 63
       let shifted := a >>> sh
       let signBit := (a >>> 63) &&& 1
       if signBit != 0 && sh != 0 then
         shifted ||| (0xffffffffffffffff <<< (64 - sh))
       else shifted) := by
  have hc :
      (a.toBitVec >>> 63#64 &&& 1#64 != 0#64 && b.toBitVec &&& 63#64 != 0#64) =
      ((a >>> 63) &&& 1 != 0 && b &&& 63 != 0) := rfl
  apply UInt64.eq_of_toBitVec_eq
  unfold LeanMLIR.sar64
  dsimp only
  rw [hc]
  cases ((a >>> 63) &&& 1 != 0 && b &&& 63 != 0) <;> rfl

theorem u256_toNat_lt (w : UInt256) : w.toNat < 2 ^ 256 := by
  unfold UInt256.toNat
  have h0 : w.lo0.toNat < 2 ^ 64 := w.lo0.toBitVec.isLt
  have h1 : w.lo1.toNat < 2 ^ 64 := w.lo1.toBitVec.isLt
  have h2 : w.hi0.toNat < 2 ^ 64 := w.hi0.toBitVec.isLt
  have h3 : w.hi1.toNat < 2 ^ 64 := w.hi1.toBitVec.isLt
  omega

theorem word256_toNat (w : UInt256) : (LeanMLIR.word256 w).toNat = w.toNat := by
  unfold LeanMLIR.word256
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (u256_toNat_lt w)

theorem u64_eq_of_toNat_mod (n : Nat) (x : UInt64) (h : n % 2 ^ 64 = x.toNat) :
    UInt64.ofNat n = x := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  change (BitVec.ofNat 64 n).toNat = x.toNat
  rw [BitVec.toNat_ofNat]
  exact h

theorem u256_ofNat_toNat (w : UInt256) : UInt256.ofNat w.toNat = w := by
  cases w with
  | mk l0 l1 h0 h1 =>
    have hl0 : l0.toNat < 2 ^ 64 := l0.toBitVec.isLt
    have hl1 : l1.toNat < 2 ^ 64 := l1.toBitVec.isLt
    have hh0 : h0.toNat < 2 ^ 64 := h0.toBitVec.isLt
    have hh1 : h1.toNat < 2 ^ 64 := h1.toBitVec.isLt
    unfold UInt256.ofNat UInt256.toNat UInt256.modulusNat
    dsimp only [Nat.toUInt64]
    congr 1 <;> apply u64_eq_of_toNat_mod <;> omega

theorem u256_add_bv (a b : UInt256) :
    LeanMLIR.ofWord256 (LeanMLIR.word256 a + LeanMLIR.word256 b) = UInt256.add a b := by
  have ha0 : a.lo0.toNat < 2 ^ 64 := a.lo0.toBitVec.isLt
  have ha1 : a.lo1.toNat < 2 ^ 64 := a.lo1.toBitVec.isLt
  have ha2 : a.hi0.toNat < 2 ^ 64 := a.hi0.toBitVec.isLt
  have ha3 : a.hi1.toNat < 2 ^ 64 := a.hi1.toBitVec.isLt
  have hb0 : b.lo0.toNat < 2 ^ 64 := b.lo0.toBitVec.isLt
  have hb1 : b.lo1.toNat < 2 ^ 64 := b.lo1.toBitVec.isLt
  have hb2 : b.hi0.toNat < 2 ^ 64 := b.hi0.toBitVec.isLt
  have hb3 : b.hi1.toNat < 2 ^ 64 := b.hi1.toBitVec.isLt
  unfold LeanMLIR.ofWord256 UInt256.ofNat UInt256.add UInt256.modulusNat
  rw [BitVec.toNat_add, word256_toNat, word256_toNat]
  unfold UInt256.toNat
  dsimp only [Nat.toUInt64]
  congr 1 <;> apply UInt64.eq_of_toBitVec_eq <;> apply BitVec.eq_of_toNat_eq <;>
    change (BitVec.ofNat 64 _).toNat = (BitVec.ofNat 64 _).toNat <;>
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] <;> omega

theorem u256_sub_bv (a b : UInt256) :
    LeanMLIR.ofWord256 (LeanMLIR.word256 a - LeanMLIR.word256 b) = UInt256.sub a b := by
  have hb := u256_toNat_lt b
  unfold LeanMLIR.ofWord256 UInt256.sub UInt256.modulusNat
  rw [BitVec.toNat_sub, word256_toNat, word256_toNat]
  congr 1
  omega

theorem u256_mul_bv (a b : UInt256) :
    LeanMLIR.ofWord256 (LeanMLIR.word256 a * LeanMLIR.word256 b) = UInt256.mul a b := by
  unfold LeanMLIR.ofWord256 UInt256.mul UInt256.modulusNat
  rw [BitVec.toNat_mul, word256_toNat, word256_toNat]

theorem u64_ne_iff_toNat (a b : UInt64) : (a != b) = decide (a.toNat ≠ b.toNat) := by
  cases h : a == b with
  | true =>
    have hab : a = b := eq_of_beq h
    subst hab
    simp
  | false =>
    have hne : a ≠ b := by
      intro hab; subst hab; simp at h
    have hnat : a.toNat ≠ b.toNat := by
      intro ht
      exact hne (UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq ht))
    simp [bne, h, hnat]

theorem u64_lt_iff_toNat (a b : UInt64) : decide (a < b) = decide (a.toNat < b.toNat) := rfl

theorem word_eq (a b : UInt256) :
    (LeanMLIR.word256 a == LeanMLIR.word256 b) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have hnat : (LeanMLIR.word256 a).toNat = (LeanMLIR.word256 b).toNat :=
      congrArg BitVec.toNat (eq_of_beq h)
    rw [word256_toNat, word256_toNat] at hnat
    have : UInt256.ofNat a.toNat = UInt256.ofNat b.toNat := congrArg UInt256.ofNat hnat
    rw [u256_ofNat_toNat, u256_ofNat_toNat] at this
    exact beq_iff_eq.mpr this
  · intro h
    exact beq_iff_eq.mpr (congrArg LeanMLIR.word256 (eq_of_beq h))

theorem word_lt (a b : UInt256) :
    decide (LeanMLIR.word256 a < LeanMLIR.word256 b) = UInt256.lt a b := by
  have hlt : (LeanMLIR.word256 a < LeanMLIR.word256 b) ↔ a.toNat < b.toNat := by
    rw [BitVec.lt_def, word256_toNat, word256_toNat]
  unfold UInt256.lt
  rw [u64_ne_iff_toNat, u64_ne_iff_toNat, u64_ne_iff_toNat,
      u64_lt_iff_toNat, u64_lt_iff_toNat, u64_lt_iff_toNat, u64_lt_iff_toNat]
  have ha0 : a.lo0.toNat < 2 ^ 64 := a.lo0.toBitVec.isLt
  have ha1 : a.lo1.toNat < 2 ^ 64 := a.lo1.toBitVec.isLt
  have ha2 : a.hi0.toNat < 2 ^ 64 := a.hi0.toBitVec.isLt
  have ha3 : a.hi1.toNat < 2 ^ 64 := a.hi1.toBitVec.isLt
  have hb0 : b.lo0.toNat < 2 ^ 64 := b.lo0.toBitVec.isLt
  have hb1 : b.lo1.toNat < 2 ^ 64 := b.lo1.toBitVec.isLt
  have hb2 : b.hi0.toNat < 2 ^ 64 := b.hi0.toBitVec.isLt
  have hb3 : b.hi1.toNat < 2 ^ 64 := b.hi1.toBitVec.isLt
  unfold UInt256.toNat at hlt
  rcases Decidable.em (a.hi1.toNat = b.hi1.toNat) with h3 | h3
  · rcases Decidable.em (a.hi0.toNat = b.hi0.toNat) with h2 | h2
    · rcases Decidable.em (a.lo1.toNat = b.lo1.toNat) with h1 | h1
      · simp [h3, h2, h1]; rw [hlt]; simp [h3, h2, h1]
      · simp [h3, h2, h1]; rw [hlt]; simp [h3, h2]; omega
    · simp [h3, h2]; rw [hlt]; simp [h3]; omega
  · simp [h3]; rw [hlt]; omega

theorem word_le (a b : UInt256) :
    decide (LeanMLIR.word256 a ≤ LeanMLIR.word256 b) = UInt256.le a b := by
  unfold UInt256.le
  rw [← word_eq, ← word_lt]
  have hle : (LeanMLIR.word256 a ≤ LeanMLIR.word256 b) ↔
      (LeanMLIR.word256 a = LeanMLIR.word256 b ∨ LeanMLIR.word256 a < LeanMLIR.word256 b) := by
    rw [BitVec.le_def, BitVec.lt_def, word256_toNat, word256_toNat]
    constructor
    · intro h
      rcases Nat.eq_or_lt_of_le h with heq | hlt
      · left; exact BitVec.eq_of_toNat_eq (by rw [word256_toNat, word256_toNat]; exact heq)
      · right; exact hlt
    · intro h
      rcases h with heq | hlt
      · have := congrArg BitVec.toNat heq; rw [word256_toNat, word256_toNat] at this; omega
      · omega
  by_cases he : LeanMLIR.word256 a = LeanMLIR.word256 b
  · simp [he]
  · have hbe : (LeanMLIR.word256 a == LeanMLIR.word256 b) = false := beq_false_of_ne he
    rw [hbe, Bool.false_or]
    by_cases hlt : LeanMLIR.word256 a < LeanMLIR.word256 b
    · have : LeanMLIR.word256 a ≤ LeanMLIR.word256 b := hle.mpr (Or.inr hlt)
      simp [this, hlt]
    · have : ¬(LeanMLIR.word256 a ≤ LeanMLIR.word256 b) := by
        intro h; rcases hle.mp h with h1 | h2; exact he h1; exact hlt h2
      simp [this, hlt]

theorem u256_shl_bv (a : UInt256) (s : Nat) :
    LeanMLIR.ofWord256 (LeanMLIR.word256 a <<< s) = UInt256.shl a s := by
  unfold LeanMLIR.ofWord256 UInt256.shl UInt256.modulusNat
  rw [BitVec.toNat_shiftLeft, word256_toNat, Nat.shiftLeft_eq]
  by_cases hs : s ≥ 256
  · simp only [hs, ↓reduceIte]
    have hk : 256 + (s - 256) = s := by omega
    have hpow : 2 ^ s = 2 ^ 256 * 2 ^ (s - 256) := by
      rw [← Nat.pow_add, hk]
    have hmod : (a.toNat * 2 ^ s) % 2 ^ 256 = 0 := by
      rw [hpow, ← Nat.mul_assoc, Nat.mul_comm a.toNat (2 ^ 256), Nat.mul_assoc]
      exact Nat.mul_mod_right (2 ^ 256) _
    rw [hmod]
    rfl
  · simp only [hs, ↓reduceIte]

theorem u256_shr_bv (a : UInt256) (s : Nat) :
    LeanMLIR.ofWord256 (LeanMLIR.word256 a >>> s) = UInt256.shr a s := by
  unfold LeanMLIR.ofWord256 UInt256.shr
  rw [BitVec.toNat_ushiftRight, word256_toNat, Nat.shiftRight_eq_div_pow]
  by_cases hs : s ≥ 256
  · simp [hs]
    have hlt := u256_toNat_lt a
    have hpow : 2 ^ 256 ≤ 2 ^ s := Nat.pow_le_pow_right (by omega) hs
    have hdiv : a.toNat / 2 ^ s = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hlt hpow)
    rw [hdiv]
    rfl
  · simp [hs]

theorem u64_msb_mask (h : UInt64) :
    ((h &&& 0x8000000000000000) != 0) = decide (2 ^ 63 ≤ h.toNat) := by
  have hh : h.toNat < 2 ^ 64 := h.toBitVec.isLt
  have hbit : (h &&& 0x8000000000000000).toNat = (h.toNat / 2 ^ 63) * 2 ^ 63 := by
    have hbv : (h &&& 0x8000000000000000).toBitVec =
        if 2 ^ 63 ≤ h.toNat then 9223372036854775808#64 else 0#64 := by
      change h.toBitVec &&& 9223372036854775808#64 =
        if 2 ^ 63 ≤ h.toNat then 9223372036854775808#64 else 0#64
      apply BitVec.eq_of_getElem_eq
      intro i hi
      by_cases hi63 : i = 63
      · subst hi63
        have hc : (9223372036854775808#64)[63] = true := by
          rw [BitVec.getElem_eq_testBit_toNat]
          rfl
        have hx : (h.toBitVec)[63] = decide (2 ^ 63 ≤ h.toNat) := by
          rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit, Nat.shiftRight_eq_div_pow]
          by_cases hge : 2 ^ 63 ≤ h.toNat
          · have hq : h.toNat / 2 ^ 63 = 1 := by omega
            simp [hge, hq]
          · have hq : h.toNat / 2 ^ 63 = 0 := by omega
            simp [hge, hq]
        by_cases hge : 2 ^ 63 ≤ h.toNat
        · simp [hge, hc, hx]
        · simp [hge, hc, hx]
      · have hc : (9223372036854775808#64)[i] = false := by
          rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit, Nat.shiftRight_eq_div_pow]
          have hlit : (9223372036854775808#64).toNat = 2 ^ 63 := rfl
          rw [hlit]
          have hpow : 2 ^ 63 / 2 ^ i = 2 ^ (63 - i) := by
            have hk : i + (63 - i) = 63 := by omega
            have := Nat.mul_div_cancel_left (2 ^ (63 - i)) (Nat.two_pow_pos i)
            rw [← Nat.pow_add, hk] at this
            exact this
          have hpos : 63 - i = (62 - i) + 1 := by omega
          rw [hpow, hpos, Nat.pow_succ, Nat.one_and_eq_mod_two]
          simp
        by_cases hge : 2 ^ 63 ≤ h.toNat <;> simp [hge, hc]
    have htn : (h &&& 0x8000000000000000).toNat =
        ((h &&& 0x8000000000000000).toBitVec).toNat := rfl
    rw [htn, hbv]
    by_cases hge : 2 ^ 63 ≤ h.toNat
    · have hq : h.toNat / 2 ^ 63 = 1 := by omega
      simp [hge, hq]
    · have hq : h.toNat / 2 ^ 63 = 0 := by omega
      simp [hge, hq]
  rw [u64_ne_iff_toNat]
  change decide ((h &&& 0x8000000000000000).toNat ≠ 0) = decide (2 ^ 63 ≤ h.toNat)
  rw [hbit]
  by_cases hge : 2 ^ 63 ≤ h.toNat
  · simp [hge]; omega
  · simp [hge]; omega

theorem u256_sar_bv (a : UInt256) (sh : Nat) :
    LeanMLIR.ofWord256 (LeanMLIR.sar256 (LeanMLIR.word256 a) sh) = UInt256.sar a sh := by
  have hneg : ((a.hi1 &&& 0x8000000000000000) != 0) = decide (2 ^ 255 ≤ a.toNat) := by
    rw [u64_msb_mask]
    unfold UInt256.toNat
    have h0 : a.lo0.toNat < 2 ^ 64 := a.lo0.toBitVec.isLt
    have h1 : a.lo1.toNat < 2 ^ 64 := a.lo1.toBitVec.isLt
    have h2 : a.hi0.toNat < 2 ^ 64 := a.hi0.toBitVec.isLt
    have h3 : a.hi1.toNat < 2 ^ 64 := a.hi1.toBitVec.isLt
    by_cases hg : 2 ^ 63 ≤ a.hi1.toNat
    · simp [hg]; omega
    · simp [hg]; omega
  unfold LeanMLIR.sar256 UInt256.sar
  dsimp only
  rw [word256_toNat, hneg]
  by_cases hge : sh ≥ 256
  · simp only [hge, ↓reduceIte]
    by_cases hsgn : 2 ^ 255 ≤ a.toNat
    · simp only [hsgn, decide_true, ↓reduceIte]; rfl
    · simp only [hsgn, decide_false, Bool.false_eq_true, ↓reduceIte]; rfl
  · simp only [hge, ↓reduceIte]
    by_cases h0 : sh = 0
    · subst h0
      simp only [beq_self_eq_true, ↓reduceIte, LeanMLIR.ofWord256, word256_toNat, u256_ofNat_toNat]
    · have h0b : (sh == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte]
      by_cases hsgn : 2 ^ 255 ≤ a.toNat
      · simp only [hsgn, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        unfold LeanMLIR.ofWord256 UInt256.modulusNat
        rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, word256_toNat, Nat.shiftRight_eq_div_pow,
            BitVec.toNat_shiftLeft, BitVec.toNat_allOnes, Nat.shiftLeft_eq]
        have hk : 256 - sh < 256 := by omega
        have hp_lt : 2 ^ (256 - sh) < 2 ^ 256 := Nat.pow_lt_pow_right (by omega) hk
        have hp_pos : 1 ≤ 2 ^ (256 - sh) := Nat.one_le_pow _ _ (by omega)
        have hones : ((2 ^ 256 - 1) * 2 ^ (256 - sh)) % 2 ^ 256 =
            (2 ^ 256 - 2 ^ (256 - sh)) % 2 ^ 256 := by
          have heq : (2 ^ 256 - 1) * 2 ^ (256 - sh) =
              (2 ^ 256 - 2 ^ (256 - sh)) + 2 ^ 256 * (2 ^ (256 - sh) - 1) := by
            have h1 : (2 ^ 256 - 1) * 2 ^ (256 - sh) = 2 ^ 256 * 2 ^ (256 - sh) - 2 ^ (256 - sh) :=
              Nat.sub_one_mul (2 ^ 256) (2 ^ (256 - sh))
            have h2 : 2 ^ 256 * (2 ^ (256 - sh) - 1) = 2 ^ 256 * 2 ^ (256 - sh) - 2 ^ 256 :=
              Nat.mul_sub_one (2 ^ 256) (2 ^ (256 - sh))
            omega
          rw [heq, Nat.add_mul_mod_self_left]
        unfold UInt256.ofNat UInt256.modulusNat
        have hsum :
            (a.toNat / 2 ^ sh + ((2 ^ 256 - 1) * 2 ^ (256 - sh)) % 2 ^ 256) % 2 ^ 256 =
            (a.toNat / 2 ^ sh + (2 ^ 256 - 2 ^ (256 - sh)) % 2 ^ 256) % 2 ^ 256 := by
          rw [hones]
        rw [hsum, Nat.mod_mod]
      · simp only [hsgn, decide_false, Bool.not_false, ↓reduceIte,
                   LeanMLIR.ofWord256, BitVec.toNat_ushiftRight, word256_toNat, Nat.shiftRight_eq_div_pow]

theorem ofU64_toNat (n : UInt64) : (UInt256.ofUInt64 n).toNat = n.toNat := by
  unfold UInt256.ofUInt64 UInt256.toNat
  have : n.toNat < 2 ^ 64 := n.toBitVec.isLt
  change n.toNat + 0 * 2 ^ 64 + 0 * 2 ^ 128 + 0 * 2 ^ 192 = n.toNat
  omega

theorem asWord256_eq (v : Val) :
    LeanMLIR.asWord256 v = v.toU256?.map LeanMLIR.word256 := by
  cases v with
  | u256 w => rfl
  | u64 n =>
    have hn : BitVec.ofNat 256 n.toBitVec.toNat = LeanMLIR.word256 (UInt256.ofUInt64 n) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, word256_toNat, ofU64_toNat]
      have : n.toNat < 2 ^ 64 := n.toBitVec.isLt
      exact Nat.mod_eq_of_lt (by omega : n.toNat < 2 ^ 256)
    exact congrArg some hn
  | _ => rfl

theorem word_eq_zero (b : UInt256) :
    (LeanMLIR.word256 b == 0#256) = (b.toNat == 0) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have hnat : (LeanMLIR.word256 b).toNat = (0#256).toNat := congrArg BitVec.toNat (eq_of_beq h)
    rw [word256_toNat] at hnat
    exact beq_iff_eq.mpr hnat
  · intro h
    have h0 : b.toNat = 0 := eq_of_beq h
    apply beq_iff_eq.mpr
    apply BitVec.eq_of_toNat_eq
    rw [word256_toNat, h0]
    rfl

theorem u256_div_bv (a b : UInt256) :
    LeanMLIR.ofWord256 (LeanMLIR.word256 a / LeanMLIR.word256 b) =
      UInt256.ofNat (a.toNat / b.toNat) := by
  unfold LeanMLIR.ofWord256
  rw [BitVec.toNat_udiv, word256_toNat, word256_toNat]

theorem u256_mod_bv (a b : UInt256) :
    LeanMLIR.ofWord256 (LeanMLIR.word256 a % LeanMLIR.word256 b) =
      UInt256.ofNat (a.toNat % b.toNat) := by
  unfold LeanMLIR.ofWord256
  rw [BitVec.toNat_umod, word256_toNat, word256_toNat]

theorem u256_div_opt (a b : UInt256) :
    (if LeanMLIR.word256 b == 0#256 then none
     else some (LeanMLIR.ofWord256 (LeanMLIR.word256 a / LeanMLIR.word256 b))) =
    UInt256.div a b := by
  rw [word_eq_zero, u256_div_bv]
  rfl

theorem u256_mod_opt (a b : UInt256) :
    (if LeanMLIR.word256 b == 0#256 then none
     else some (LeanMLIR.ofWord256 (LeanMLIR.word256 a % LeanMLIR.word256 b))) =
    UInt256.mod a b := by
  rw [word_eq_zero, u256_mod_bv]
  rfl

theorem opt_to_except {α ε β : Type} (c : Bool) (x : α) (e : ε) (f : α → β) :
    (if c then Except.error e else Except.ok (f x)) =
    (match (if c then none else some x) with
     | some q => Except.ok (f q)
     | none => Except.error e) := by
  cases c <;> rfl

theorem opt_to_poison {α β : Type} (c : Bool) (x : α) (msg : String) (f : α → β) :
    (if c then LeanMLIR.PoisonOr.poison msg else LeanMLIR.PoisonOr.val (f x)) =
    (match (if c then none else some x) with
     | some q => LeanMLIR.PoisonOr.val (f q)
     | none => LeanMLIR.PoisonOr.poison msg) := by
  cases c <;> rfl

theorem u256_addChecked_opt (a b : UInt256) :
    (if BitVec.uaddOverflow (LeanMLIR.word256 a) (LeanMLIR.word256 b) then none
     else some (LeanMLIR.ofWord256 (LeanMLIR.word256 a + LeanMLIR.word256 b))) =
    UInt256.addChecked a b := by
  have hov : BitVec.uaddOverflow (LeanMLIR.word256 a) (LeanMLIR.word256 b) =
      decide (a.toNat + b.toNat ≥ UInt256.modulusNat) := by
    unfold BitVec.uaddOverflow UInt256.modulusNat
    rw [word256_toNat, word256_toNat]
  rw [hov]
  unfold UInt256.addChecked
  dsimp only
  by_cases hge : a.toNat + b.toNat ≥ UInt256.modulusNat
  · simp only [hge, decide_true, ↓reduceIte]
  · simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    congr 1
    unfold LeanMLIR.ofWord256
    rw [BitVec.toNat_add, word256_toNat, word256_toNat]
    have hlt : a.toNat + b.toNat < 2 ^ 256 := by unfold UInt256.modulusNat at hge; omega
    rw [Nat.mod_eq_of_lt hlt]

theorem u256_subChecked_opt (a b : UInt256) :
    (if decide (LeanMLIR.word256 a < LeanMLIR.word256 b) then none
     else some (LeanMLIR.ofWord256 (LeanMLIR.word256 a - LeanMLIR.word256 b))) =
    UInt256.subChecked a b := by
  have hlt : decide (LeanMLIR.word256 a < LeanMLIR.word256 b) = decide (a.toNat < b.toNat) := by
    apply Bool.eq_iff_iff.mpr
    simp [BitVec.lt_def, word256_toNat]
  rw [hlt]
  unfold UInt256.subChecked
  by_cases hab : a.toNat < b.toNat
  · simp only [hab, decide_true, ↓reduceIte]
  · simp only [hab, decide_false, Bool.false_eq_true, ↓reduceIte]
    congr 1
    have ha := u256_toNat_lt a
    have hb := u256_toNat_lt b
    unfold LeanMLIR.ofWord256
    rw [BitVec.toNat_sub, word256_toNat, word256_toNat]
    have heq : 2 ^ 256 - b.toNat + a.toNat = (a.toNat - b.toNat) + 2 ^ 256 := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : a.toNat - b.toNat < 2 ^ 256)]

theorem u256_mulChecked_opt (a b : UInt256) :
    (if BitVec.umulOverflow (LeanMLIR.word256 a) (LeanMLIR.word256 b) then none
     else some (LeanMLIR.ofWord256 (LeanMLIR.word256 a * LeanMLIR.word256 b))) =
    UInt256.mulChecked a b := by
  have hov : BitVec.umulOverflow (LeanMLIR.word256 a) (LeanMLIR.word256 b) =
      decide (a.toNat * b.toNat ≥ UInt256.modulusNat) := by
    unfold BitVec.umulOverflow UInt256.modulusNat
    rw [word256_toNat, word256_toNat]
  rw [hov]
  unfold UInt256.mulChecked
  dsimp only
  by_cases hge : a.toNat * b.toNat ≥ UInt256.modulusNat
  · simp only [hge, decide_true, ↓reduceIte]
  · simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    congr 1
    unfold LeanMLIR.ofWord256
    rw [BitVec.toNat_mul, word256_toNat, word256_toNat]
    have hlt : a.toNat * b.toNat < 2 ^ 256 := by unfold UInt256.modulusNat at hge; omega
    rw [Nat.mod_eq_of_lt hlt]

theorem u64_or_bv (a b : UInt64) :
    UInt64.ofBitVec (a.toBitVec ||| b.toBitVec) = (a ||| b) := rfl

theorem u64_xor_bv (a b : UInt64) :
    UInt64.ofBitVec (a.toBitVec ^^^ b.toBitVec) = (a ^^^ b) := rfl

theorem u64_shl_bv (a b : UInt64) :
    UInt64.ofBitVec (a.toBitVec <<< (b.toBitVec % 64#64)) = (a <<< b) := rfl

theorem u64_shr_bv (a b : UInt64) :
    UInt64.ofBitVec (a.toBitVec >>> (b.toBitVec % 64#64)) = (a >>> b) := rfl

theorem u64_cases_01 (P : UInt64 → Prop)
    (h0 : ∀ (h : 0 < 2 ^ 64), P ⟨⟨⟨0, h⟩⟩⟩)
    (h1 : ∀ (h : 1 < 2 ^ 64), P ⟨⟨⟨1, h⟩⟩⟩)
    (h2 : ∀ (n : Nat) (h : n + 2 < 2 ^ 64), P ⟨⟨⟨n + 2, h⟩⟩⟩) :
    ∀ x : UInt64, P x
  | ⟨⟨⟨0, h⟩⟩⟩ => h0 h
  | ⟨⟨⟨1, h⟩⟩⟩ => h1 h
  | ⟨⟨⟨n + 2, h⟩⟩⟩ => h2 n h

theorem match9_eq (o : Option UInt256) (err : UBError) :
    evalBinOp.match_9 (fun _ => Except UBError Val) o
      (fun r => Except.ok (Val.u256 r)) (fun _ => Except.error err) =
    opt_to_except.match_1 (fun _ => Except UBError Val) o
      (fun v => Except.ok (Val.u256 v)) (fun _ => Except.error err) := by
  cases o <;> rfl

theorem match_11_u256 {α : Type} (a b : UInt256)
    (h1 : UInt64 → UInt64 → α) (h2 : Val → α)
    (h3 : UInt256 → UInt256 → α) (h4 : Val → Val → α) :
    evalBinOp.match_11 (fun _ _ => α) (.u256 a) (.u256 b) h1 h2 h3 h4 = h3 a b := rfl

theorem match_13_u256 {α : Type} (a b : UInt256)
    (h1 : UInt64 → UInt64 → α)
    (h3 : UInt256 → UInt256 → α) (h4 : Val → Val → α) :
    evalBinOp.match_13 (fun _ _ => α) (.u256 a) (.u256 b) h1 h3 h4 = h3 a b := rfl

theorem match_20_some {α : Type} (a b : UInt256)
    (h1 : UInt256 → UInt256 → α) (h2 : Option UInt256 → Option UInt256 → α) :
    evalBinOp.match_20 (fun _ _ => α) (some a) (some b) h1 h2 = h1 a b := rfl

theorem match_20_none_left {α : Type} (o : Option UInt256)
    (h1 : UInt256 → UInt256 → α) (h2 : Option UInt256 → Option UInt256 → α) :
    evalBinOp.match_20 (fun _ _ => α) none o h1 h2 = h2 none o := rfl

theorem match_20_none_right {α : Type} (a : UInt256)
    (h1 : UInt256 → UInt256 → α) (h2 : Option UInt256 → Option UInt256 → α) :
    evalBinOp.match_20 (fun _ _ => α) (some a) none h1 h2 = h2 (some a) none := rfl

theorem eval_div_step1 (v1 v2 : Val) :
    evalBinOp .div v1 v2 =
      evalBinOp.match_11
        (fun _ _ => Except UBError Val) v1 v2
        (fun a b => Except.ok (Val.u64 (a / b))) (fun v => Except.ok v)
        (fun a b =>
          evalBinOp.match_9 (fun _ => Except UBError Val)
            (a.div b) (fun q => Except.ok (Val.u256 q)) fun _ =>
            Except.error UBError.divisionByZero)
        (fun _ _ => Except.error (UBError.typeError "evalBinOp: invalid operand types")) := rfl

theorem eval_mod_step1 (v1 v2 : Val) :
    evalBinOp .mod v1 v2 =
      evalBinOp.match_13
        (fun _ _ => Except UBError Val) v1 v2
        (fun a b => Except.ok (Val.u64 (a % b)))
        (fun a b =>
          evalBinOp.match_9 (fun _ => Except UBError Val)
            (a.mod b) (fun r => Except.ok (Val.u256 r)) fun _ =>
            Except.error UBError.divisionByZero)
        (fun _ _ => Except.error (UBError.typeError "evalBinOp: invalid operand types")) := rfl

theorem eval_div_u256 (a b : UInt256) :
    evalBinOp .div (.u256 a) (.u256 b) =
      evalBinOp.match_9 (fun _ => Except UBError Val) (a.div b)
        (fun q => Except.ok (Val.u256 q))
        (fun _ => Except.error UBError.divisionByZero) :=
  @Eq.trans (Except UBError Val)
    (evalBinOp .div (.u256 a) (.u256 b))
    (evalBinOp.match_11 (fun _ _ => Except UBError Val) (.u256 a) (.u256 b)
      (fun a b => Except.ok (Val.u64 (a / b))) (fun v => Except.ok v)
      (fun a b =>
        evalBinOp.match_9 (fun _ => Except UBError Val)
          (a.div b) (fun q => Except.ok (Val.u256 q)) fun _ =>
          Except.error UBError.divisionByZero)
      (fun _ _ => Except.error (UBError.typeError "evalBinOp: invalid operand types")))
    (evalBinOp.match_9 (fun _ => Except UBError Val) (a.div b)
      (fun q => Except.ok (Val.u256 q))
      (fun _ => Except.error UBError.divisionByZero))
    (eval_div_step1 (.u256 a) (.u256 b))
    (@match_11_u256 (Except UBError Val) a b
      (fun a b => Except.ok (Val.u64 (a / b))) (fun v => Except.ok v)
      (fun a b =>
        evalBinOp.match_9 (fun _ => Except UBError Val)
          (a.div b) (fun q => Except.ok (Val.u256 q)) fun _ =>
          Except.error UBError.divisionByZero)
      (fun _ _ => Except.error (UBError.typeError "evalBinOp: invalid operand types")))

theorem eval_mod_u256 (a b : UInt256) :
    evalBinOp .mod (.u256 a) (.u256 b) =
      evalBinOp.match_9 (fun _ => Except UBError Val) (a.mod b)
        (fun r => Except.ok (Val.u256 r))
        (fun _ => Except.error UBError.divisionByZero) :=
  @Eq.trans (Except UBError Val)
    (evalBinOp .mod (.u256 a) (.u256 b))
    (evalBinOp.match_13 (fun _ _ => Except UBError Val) (.u256 a) (.u256 b)
      (fun a b => Except.ok (Val.u64 (a % b)))
      (fun a b =>
        evalBinOp.match_9 (fun _ => Except UBError Val)
          (a.mod b) (fun r => Except.ok (Val.u256 r)) fun _ =>
          Except.error UBError.divisionByZero)
      (fun _ _ => Except.error (UBError.typeError "evalBinOp: invalid operand types")))
    (evalBinOp.match_9 (fun _ => Except UBError Val) (a.mod b)
      (fun r => Except.ok (Val.u256 r))
      (fun _ => Except.error UBError.divisionByZero))
    (eval_mod_step1 (.u256 a) (.u256 b))
    (@match_13_u256 (Except UBError Val) a b
      (fun a b => Except.ok (Val.u64 (a % b)))
      (fun a b =>
        evalBinOp.match_9 (fun _ => Except UBError Val)
          (a.mod b) (fun r => Except.ok (Val.u256 r)) fun _ =>
          Except.error UBError.divisionByZero)
      (fun _ _ => Except.error (UBError.typeError "evalBinOp: invalid operand types")))

def optPairMatch (α : Type) (o1 o2 : Option UInt256)
    (h1 : UInt256 → UInt256 → α) (err : α) : α :=
  match o1, o2 with
  | some a, some b => h1 a b
  | _, _ => err

theorem match_20_checked (α : Type) (o1 o2 : Option UInt256)
    (h1 : UInt256 → UInt256 → α) (err : α) :
    evalBinOp.match_20 (fun _ _ => α) o1 o2 h1 (fun _ _ => err) =
      optPairMatch α o1 o2 h1 err := by
  cases o1 <;> cases o2 <;> rfl

theorem optPair_map_eq (α : Type) (o1 o2 : Option UInt256)
    (f : BitVec 256 → BitVec 256 → α)
    (g : UInt256 → UInt256 → α)
    (err : α)
    (hfg : ∀ a b, f (LeanMLIR.word256 a) (LeanMLIR.word256 b) = g a b) :
    (match o1.map LeanMLIR.word256, o2.map LeanMLIR.word256 with
     | some a, some b => f a b
     | _, _ => err) =
    optPairMatch α o1 o2 g err := by
  cases o1 <;> cases o2 <;> simp [optPairMatch, hfg]

theorem eval_addChecked_eq (v1 v2 : Val) :
    evalBinOp .addChecked256 v1 v2 =
      evalBinOp.match_20 (fun _ _ => Except UBError Val) v1.toU256? v2.toU256?
        (fun a b =>
          evalBinOp.match_9 (fun _ => Except UBError Val) (a.addChecked b)
            (fun res => Except.ok (Val.u256 res))
            (fun _ => Except.error (UBError.arithmeticOverflow "addChecked256 overflow")))
        (fun _ _ => Except.error (UBError.typeError "addChecked256 requires u256/u64 operands")) := rfl

theorem eval_subChecked_eq (v1 v2 : Val) :
    evalBinOp .subChecked256 v1 v2 =
      evalBinOp.match_20 (fun _ _ => Except UBError Val) v1.toU256? v2.toU256?
        (fun a b =>
          evalBinOp.match_9 (fun _ => Except UBError Val) (a.subChecked b)
            (fun res => Except.ok (Val.u256 res))
            (fun _ => Except.error (UBError.arithmeticOverflow "subChecked256 underflow")))
        (fun _ _ => Except.error (UBError.typeError "subChecked256 requires u256/u64 operands")) := rfl

theorem eval_mulChecked_eq (v1 v2 : Val) :
    evalBinOp .mulChecked256 v1 v2 =
      evalBinOp.match_20 (fun _ _ => Except UBError Val) v1.toU256? v2.toU256?
        (fun a b =>
          evalBinOp.match_9 (fun _ => Except UBError Val) (a.mulChecked b)
            (fun res => Except.ok (Val.u256 res))
            (fun _ => Except.error (UBError.arithmeticOverflow "mulChecked256 overflow")))
        (fun _ _ => Except.error (UBError.typeError "mulChecked256 requires u256/u64 operands")) := rfl

theorem eval_addChecked_pair (v1 v2 : Val) :
    evalBinOp .addChecked256 v1 v2 =
      optPairMatch (Except UBError Val) v1.toU256? v2.toU256?
        (fun a b =>
          evalBinOp.match_9 (fun _ => Except UBError Val) (a.addChecked b)
            (fun res => Except.ok (Val.u256 res))
            (fun _ => Except.error (UBError.arithmeticOverflow "addChecked256 overflow")))
        (Except.error (UBError.typeError "addChecked256 requires u256/u64 operands")) :=
  @Eq.trans (Except UBError Val)
    (evalBinOp .addChecked256 v1 v2)
    (evalBinOp.match_20 (fun _ _ => Except UBError Val) v1.toU256? v2.toU256?
      (fun a b =>
        evalBinOp.match_9 (fun _ => Except UBError Val) (a.addChecked b)
          (fun res => Except.ok (Val.u256 res))
          (fun _ => Except.error (UBError.arithmeticOverflow "addChecked256 overflow")))
      (fun _ _ => Except.error (UBError.typeError "addChecked256 requires u256/u64 operands")))
    (optPairMatch (Except UBError Val) v1.toU256? v2.toU256?
      (fun a b =>
        evalBinOp.match_9 (fun _ => Except UBError Val) (a.addChecked b)
          (fun res => Except.ok (Val.u256 res))
          (fun _ => Except.error (UBError.arithmeticOverflow "addChecked256 overflow")))
      (Except.error (UBError.typeError "addChecked256 requires u256/u64 operands")))
    (eval_addChecked_eq v1 v2)
    (match_20_checked (Except UBError Val) v1.toU256? v2.toU256?
      (fun a b =>
        evalBinOp.match_9 (fun _ => Except UBError Val) (a.addChecked b)
          (fun res => Except.ok (Val.u256 res))
          (fun _ => Except.error (UBError.arithmeticOverflow "addChecked256 overflow")))
      (Except.error (UBError.typeError "addChecked256 requires u256/u64 operands")))

theorem eval_subChecked_pair (v1 v2 : Val) :
    evalBinOp .subChecked256 v1 v2 =
      optPairMatch (Except UBError Val) v1.toU256? v2.toU256?
        (fun a b =>
          evalBinOp.match_9 (fun _ => Except UBError Val) (a.subChecked b)
            (fun res => Except.ok (Val.u256 res))
            (fun _ => Except.error (UBError.arithmeticOverflow "subChecked256 underflow")))
        (Except.error (UBError.typeError "subChecked256 requires u256/u64 operands")) :=
  @Eq.trans (Except UBError Val)
    (evalBinOp .subChecked256 v1 v2)
    (evalBinOp.match_20 (fun _ _ => Except UBError Val) v1.toU256? v2.toU256?
      (fun a b =>
        evalBinOp.match_9 (fun _ => Except UBError Val) (a.subChecked b)
          (fun res => Except.ok (Val.u256 res))
          (fun _ => Except.error (UBError.arithmeticOverflow "subChecked256 underflow")))
      (fun _ _ => Except.error (UBError.typeError "subChecked256 requires u256/u64 operands")))
    (optPairMatch (Except UBError Val) v1.toU256? v2.toU256?
      (fun a b =>
        evalBinOp.match_9 (fun _ => Except UBError Val) (a.subChecked b)
          (fun res => Except.ok (Val.u256 res))
          (fun _ => Except.error (UBError.arithmeticOverflow "subChecked256 underflow")))
      (Except.error (UBError.typeError "subChecked256 requires u256/u64 operands")))
    (eval_subChecked_eq v1 v2)
    (match_20_checked (Except UBError Val) v1.toU256? v2.toU256?
      (fun a b =>
        evalBinOp.match_9 (fun _ => Except UBError Val) (a.subChecked b)
          (fun res => Except.ok (Val.u256 res))
          (fun _ => Except.error (UBError.arithmeticOverflow "subChecked256 underflow")))
      (Except.error (UBError.typeError "subChecked256 requires u256/u64 operands")))

theorem eval_mulChecked_pair (v1 v2 : Val) :
    evalBinOp .mulChecked256 v1 v2 =
      optPairMatch (Except UBError Val) v1.toU256? v2.toU256?
        (fun a b =>
          evalBinOp.match_9 (fun _ => Except UBError Val) (a.mulChecked b)
            (fun res => Except.ok (Val.u256 res))
            (fun _ => Except.error (UBError.arithmeticOverflow "mulChecked256 overflow")))
        (Except.error (UBError.typeError "mulChecked256 requires u256/u64 operands")) :=
  @Eq.trans (Except UBError Val)
    (evalBinOp .mulChecked256 v1 v2)
    (evalBinOp.match_20 (fun _ _ => Except UBError Val) v1.toU256? v2.toU256?
      (fun a b =>
        evalBinOp.match_9 (fun _ => Except UBError Val) (a.mulChecked b)
          (fun res => Except.ok (Val.u256 res))
          (fun _ => Except.error (UBError.arithmeticOverflow "mulChecked256 overflow")))
      (fun _ _ => Except.error (UBError.typeError "mulChecked256 requires u256/u64 operands")))
    (optPairMatch (Except UBError Val) v1.toU256? v2.toU256?
      (fun a b =>
        evalBinOp.match_9 (fun _ => Except UBError Val) (a.mulChecked b)
          (fun res => Except.ok (Val.u256 res))
          (fun _ => Except.error (UBError.arithmeticOverflow "mulChecked256 overflow")))
      (Except.error (UBError.typeError "mulChecked256 requires u256/u64 operands")))
    (eval_mulChecked_eq v1 v2)
    (match_20_checked (Except UBError Val) v1.toU256? v2.toU256?
      (fun a b =>
        evalBinOp.match_9 (fun _ => Except UBError Val) (a.mulChecked b)
          (fun res => Except.ok (Val.u256 res))
          (fun _ => Except.error (UBError.arithmeticOverflow "mulChecked256 overflow")))
      (Except.error (UBError.typeError "mulChecked256 requires u256/u64 operands")))

theorem addChecked_inner_eq (a b : UInt256) :
    (if BitVec.uaddOverflow (LeanMLIR.word256 a) (LeanMLIR.word256 b) then
       Except.error (UBError.arithmeticOverflow "addChecked256 overflow")
     else Except.ok (Val.u256 (LeanMLIR.ofWord256 (LeanMLIR.word256 a + LeanMLIR.word256 b)))) =
    evalBinOp.match_9 (fun _ => Except UBError Val) (a.addChecked b)
      (fun res => Except.ok (Val.u256 res))
      (fun _ => Except.error (UBError.arithmeticOverflow "addChecked256 overflow")) := by
  rw [match9_eq, opt_to_except _ _ _ Val.u256, u256_addChecked_opt]

theorem subChecked_inner_eq (a b : UInt256) :
    (if decide (LeanMLIR.word256 a < LeanMLIR.word256 b) then
       Except.error (UBError.arithmeticOverflow "subChecked256 underflow")
     else Except.ok (Val.u256 (LeanMLIR.ofWord256 (LeanMLIR.word256 a - LeanMLIR.word256 b)))) =
    evalBinOp.match_9 (fun _ => Except UBError Val) (a.subChecked b)
      (fun res => Except.ok (Val.u256 res))
      (fun _ => Except.error (UBError.arithmeticOverflow "subChecked256 underflow")) := by
  rw [match9_eq, opt_to_except _ _ _ Val.u256, u256_subChecked_opt]

theorem mulChecked_inner_eq (a b : UInt256) :
    (if BitVec.umulOverflow (LeanMLIR.word256 a) (LeanMLIR.word256 b) then
       Except.error (UBError.arithmeticOverflow "mulChecked256 overflow")
     else Except.ok (Val.u256 (LeanMLIR.ofWord256 (LeanMLIR.word256 a * LeanMLIR.word256 b)))) =
    evalBinOp.match_9 (fun _ => Except UBError Val) (a.mulChecked b)
      (fun res => Except.ok (Val.u256 res))
      (fun _ => Except.error (UBError.arithmeticOverflow "mulChecked256 overflow")) := by
  rw [match9_eq, opt_to_except _ _ _ Val.u256, u256_mulChecked_opt]


theorem word256_zero : LeanMLIR.word256 UInt256.zero = 0#256 := by
  apply BitVec.eq_of_toNat_eq
  rw [word256_toNat]
  rfl

theorem ofWord_id (w : UInt256) : LeanMLIR.ofWord256 (LeanMLIR.word256 w) = w := by
  unfold LeanMLIR.ofWord256
  rw [word256_toNat, u256_ofNat_toNat]

theorem ofWord_ofU64 (n : UInt64) :
    LeanMLIR.ofWord256 (BitVec.ofNat 256 n.toBitVec.toNat) = UInt256.ofUInt64 n := by
  unfold LeanMLIR.ofWord256
  rw [BitVec.toNat_ofNat]
  have hlt : n.toBitVec.toNat < 2 ^ 64 := n.toBitVec.isLt
  have hnat : n.toBitVec.toNat = n.toNat := rfl
  rw [hnat] at hlt ⊢
  rw [Nat.mod_eq_of_lt (by omega : n.toNat < 2 ^ 256), ← ofU64_toNat, u256_ofNat_toNat]

theorem neg256_eq (w : UInt256) :
    LeanMLIR.ofWord256 (0#256 - LeanMLIR.word256 w) = UInt256.sub UInt256.zero w := by
  rw [← word256_zero, u256_sub_bv]

theorem primUnary_not_u64 (n : UInt64) :
    LeanMLIR.applyWordUnaryOp .not (.u64 n) = .val (.u64 (~~~n)) := rfl

theorem primUnary_not_u256 (w : UInt256) :
    LeanMLIR.applyWordUnaryOp .not (.u256 w) = .val (.u256 (UInt256.bitNot w)) := rfl

theorem primUnary_not_bool (b : Bool) :
    LeanMLIR.applyWordUnaryOp .not (.bool b) = .val (.bool (!b)) := rfl

theorem primUnary_neg_u64 (n : UInt64) :
    LeanMLIR.applyWordUnaryOp .neg (.u64 n) = .val (.u64 (0 - n)) := rfl

theorem primUnary_neg_u256 (w : UInt256) :
    LeanMLIR.applyWordUnaryOp .neg (.u256 w) = .val (.u256 (UInt256.sub UInt256.zero w)) := by
  have hL : LeanMLIR.applyWordUnaryOp .neg (.u256 w) =
      .val (.u256 (LeanMLIR.ofWord256 (0#256 - LeanMLIR.word256 w))) := rfl
  rw [hL, neg256_eq]

theorem primUnary_clz_u256 (w : UInt256) :
    LeanMLIR.applyWordUnaryOp .clz256 (.u256 w) = .val (.u256 (UInt256.clz w)) := by
  have hL : LeanMLIR.applyWordUnaryOp .clz256 (.u256 w) =
      .val (.u256 (UInt256.clz (LeanMLIR.ofWord256 (LeanMLIR.word256 w)))) := rfl
  rw [hL, ofWord_id]

theorem primUnary_clz_u64 (n : UInt64) :
    LeanMLIR.applyWordUnaryOp .clz256 (.u64 n) =
      .val (.u256 (UInt256.clz (UInt256.ofUInt64 n))) := by
  have hL : LeanMLIR.applyWordUnaryOp .clz256 (.u64 n) =
      .val (.u256 (UInt256.clz (LeanMLIR.ofWord256 (BitVec.ofNat 256 n.toBitVec.toNat)))) := rfl
  rw [hL, ofWord_ofU64]

theorem applyWordUnaryOp_eq_eval (op : UnaryOp) (v : Val) :
    LeanMLIR.applyWordUnaryOp op v =
      match evalUnaryOp op v with
      | .ok r => .val r
      | .error _ => .poison "unaryOp64 type" := by
  cases op with
  | not =>
    cases v with
    | u64 n => rw [primUnary_not_u64]; rfl
    | u256 w => rw [primUnary_not_u256]; rfl
    | bool b => rw [primUnary_not_bool]; rfl
    | _ => rfl
  | neg =>
    cases v with
    | u64 n => rw [primUnary_neg_u64]; rfl
    | u256 w => rw [primUnary_neg_u256]; rfl
    | _ => rfl
  | clz256 =>
    cases v with
    | u256 w => rw [primUnary_clz_u256]; rfl
    | u64 n => rw [primUnary_clz_u64]; rfl
    | _ => rfl

theorem applyWordUnaryOp_agrees (op : UnaryOp) (v r : Val)
    (h : evalUnaryOp op v = .ok r) :
    LeanMLIR.applyWordUnaryOp op v = .val r := by
  rw [applyWordUnaryOp_eq_eval, h]


def outcomeToPoison : Except UBError Val → LeanMLIR.PoisonOr Val
  | .ok v => .val v
  | .error .divisionByZero => .poison "binOp64 div0"
  | .error (.arithmeticOverflow msg) =>
    if msg == "subChecked256 underflow" then .poison "binOp64 underflow"
    else .poison "binOp64 overflow"
  | .error _ => .poison "binOp64 type"

theorem outcomeToPoison_ite (c : Bool) (e : UBError) (v : Val) :
    outcomeToPoison (if c then Except.error e else Except.ok v) =
      if c then outcomeToPoison (Except.error e) else LeanMLIR.PoisonOr.val v := by
  cases c <;> rfl

theorem mlir_add (v1 v2 : Val) :
    LeanMLIR.applyWordBinOp .add v1 v2 = outcomeToPoison (evalBinOp .add v1 v2) := by
  cases v1 with
  | u64 a =>
    cases v2 with
    | u64 b => rfl
    | _ =>
      exact u64_cases_01
        (fun a => LeanMLIR.applyWordBinOp .add (.u64 a) _ = outcomeToPoison (evalBinOp .add (.u64 a) _))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) a
  | u256 a =>
    cases v2 with
    | u64 b =>
      exact u64_cases_01
        (fun b => LeanMLIR.applyWordBinOp .add (.u256 a) (.u64 b) = outcomeToPoison (evalBinOp .add (.u256 a) (.u64 b)))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) b
    | u256 b => exact congrArg (fun w => LeanMLIR.PoisonOr.val (Val.u256 w)) (u256_add_bv a b)
    | _ => rfl
  | _ =>
    cases v2 with
    | u64 b =>
      exact u64_cases_01
        (fun b => LeanMLIR.applyWordBinOp .add _ (.u64 b) = outcomeToPoison (evalBinOp .add _ (.u64 b)))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) b
    | _ => rfl

theorem mlir_sub (v1 v2 : Val) :
    LeanMLIR.applyWordBinOp .sub v1 v2 = outcomeToPoison (evalBinOp .sub v1 v2) := by
  cases v1 with
  | u64 a =>
    cases v2 with
    | u64 b => rfl
    | _ => rfl
  | u256 a =>
    cases v2 with
    | u64 b =>
      exact u64_cases_01
        (fun b => LeanMLIR.applyWordBinOp .sub (.u256 a) (.u64 b) = outcomeToPoison (evalBinOp .sub (.u256 a) (.u64 b)))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) b
    | u256 b => exact congrArg (fun w => LeanMLIR.PoisonOr.val (Val.u256 w)) (u256_sub_bv a b)
    | _ => rfl
  | _ =>
    cases v2 with
    | u64 b =>
      exact u64_cases_01
        (fun b => LeanMLIR.applyWordBinOp .sub _ (.u64 b) = outcomeToPoison (evalBinOp .sub _ (.u64 b)))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) b
    | _ => rfl

theorem mlir_mul (v1 v2 : Val) :
    LeanMLIR.applyWordBinOp .mul v1 v2 = outcomeToPoison (evalBinOp .mul v1 v2) := by
  cases v1 with
  | u64 a =>
    cases v2 with
    | u64 b => rfl
    | _ =>
      exact u64_cases_01
        (fun a => LeanMLIR.applyWordBinOp .mul (.u64 a) _ = outcomeToPoison (evalBinOp .mul (.u64 a) _))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) a
  | u256 a =>
    cases v2 with
    | u64 b =>
      exact u64_cases_01
        (fun b => LeanMLIR.applyWordBinOp .mul (.u256 a) (.u64 b) = outcomeToPoison (evalBinOp .mul (.u256 a) (.u64 b)))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) b
    | u256 b => exact congrArg (fun w => LeanMLIR.PoisonOr.val (Val.u256 w)) (u256_mul_bv a b)
    | _ => rfl
  | _ =>
    cases v2 with
    | u64 b =>
      exact u64_cases_01
        (fun b => LeanMLIR.applyWordBinOp .mul _ (.u64 b) = outcomeToPoison (evalBinOp .mul _ (.u64 b)))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) b
    | _ => rfl

theorem mlir_div (v1 v2 : Val) :
    LeanMLIR.applyWordBinOp .div v1 v2 = outcomeToPoison (evalBinOp .div v1 v2) := by
  cases v1 with
  | u64 a =>
    cases v2 with
    | u64 b => rfl
    | _ => rfl
  | u256 a =>
    cases v2 with
    | u64 b =>
      exact u64_cases_01
        (fun b => LeanMLIR.applyWordBinOp .div (.u256 a) (.u64 b) = outcomeToPoison (evalBinOp .div (.u256 a) (.u64 b)))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) b
    | u256 b =>
      have hL : LeanMLIR.applyWordBinOp .div (.u256 a) (.u256 b) =
          (if LeanMLIR.word256 b == 0#256 then LeanMLIR.PoisonOr.poison "binOp64 div0"
           else LeanMLIR.PoisonOr.val (Val.u256 (LeanMLIR.ofWord256 (LeanMLIR.word256 a / LeanMLIR.word256 b)))) := rfl
      have hR : evalBinOp .div (.u256 a) (.u256 b) =
          (if LeanMLIR.word256 b == 0#256 then Except.error UBError.divisionByZero
           else Except.ok (Val.u256 (LeanMLIR.ofWord256 (LeanMLIR.word256 a / LeanMLIR.word256 b)))) := by
        rw [eval_div_u256, match9_eq, opt_to_except _ _ _ Val.u256, u256_div_opt]
      rw [hL, hR, outcomeToPoison_ite]
      rfl
    | _ => rfl
  | _ =>
    cases v2 with
    | u64 b =>
      exact u64_cases_01
        (fun b => LeanMLIR.applyWordBinOp .div _ (.u64 b) = outcomeToPoison (evalBinOp .div _ (.u64 b)))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) b
    | _ => rfl

theorem mlir_mod (v1 v2 : Val) :
    LeanMLIR.applyWordBinOp .mod v1 v2 = outcomeToPoison (evalBinOp .mod v1 v2) := by
  cases v1 with
  | u256 a =>
    cases v2 with
    | u256 b =>
      have hL : LeanMLIR.applyWordBinOp .mod (.u256 a) (.u256 b) =
          (if LeanMLIR.word256 b == 0#256 then LeanMLIR.PoisonOr.poison "binOp64 div0"
           else LeanMLIR.PoisonOr.val (Val.u256 (LeanMLIR.ofWord256 (LeanMLIR.word256 a % LeanMLIR.word256 b)))) := rfl
      have hR : evalBinOp .mod (.u256 a) (.u256 b) =
          (if LeanMLIR.word256 b == 0#256 then Except.error UBError.divisionByZero
           else Except.ok (Val.u256 (LeanMLIR.ofWord256 (LeanMLIR.word256 a % LeanMLIR.word256 b)))) := by
        rw [eval_mod_u256, match9_eq, opt_to_except _ _ _ Val.u256, u256_mod_opt]
      rw [hL, hR, outcomeToPoison_ite]
      rfl
    | _ => rfl
  | _ => cases v2 <;> rfl

theorem outcomeToPoison_sameVal (v1 v2 : Val) (msg : String) :
    (if LeanMLIR.sameVal v1 v2 then LeanMLIR.PoisonOr.val v1 else LeanMLIR.PoisonOr.poison "binOp64 type") =
    outcomeToPoison (if v1 == v2 then Except.ok v1 else Except.error (UBError.typeError msg)) := by
  unfold LeanMLIR.sameVal
  cases v1 == v2 <;> rfl

theorem mlir_bitAnd (v1 v2 : Val) :
    LeanMLIR.applyWordBinOp .bitAnd v1 v2 = outcomeToPoison (evalBinOp .bitAnd v1 v2) := by
  cases v1 with
  | u64 a =>
    cases v2 with
    | u64 b => rfl
    | _ => exact outcomeToPoison_sameVal _ _ _
  | u256 a =>
    cases v2 with
    | u256 b => rfl
    | _ => exact outcomeToPoison_sameVal _ _ _
  | _ =>
    cases v2 <;> exact outcomeToPoison_sameVal _ _ _

theorem mlir_bitOr (v1 v2 : Val) :
    LeanMLIR.applyWordBinOp .bitOr v1 v2 = outcomeToPoison (evalBinOp .bitOr v1 v2) := by
  cases v1 with
  | u64 a =>
    cases v2 with
    | u64 b => rfl
    | _ =>
      exact u64_cases_01
        (fun a => LeanMLIR.applyWordBinOp .bitOr (.u64 a) _ = outcomeToPoison (evalBinOp .bitOr (.u64 a) _))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) a
  | u256 a =>
    cases v2 with
    | u64 b =>
      exact u64_cases_01
        (fun b => LeanMLIR.applyWordBinOp .bitOr (.u256 a) (.u64 b) = outcomeToPoison (evalBinOp .bitOr (.u256 a) (.u64 b)))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) b
    | u256 b => rfl
    | _ => rfl
  | _ =>
    cases v2 with
    | u64 b =>
      exact u64_cases_01
        (fun b => LeanMLIR.applyWordBinOp .bitOr _ (.u64 b) = outcomeToPoison (evalBinOp .bitOr _ (.u64 b)))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) b
    | _ => exact outcomeToPoison_sameVal _ _ "bitOr requires u64 or u256"

theorem mlir_bitXor (v1 v2 : Val) :
    LeanMLIR.applyWordBinOp .bitXor v1 v2 = outcomeToPoison (evalBinOp .bitXor v1 v2) := by
  cases v1 with
  | u64 a =>
    cases v2 with
    | u64 b => rfl
    | _ =>
      exact u64_cases_01
        (fun a => LeanMLIR.applyWordBinOp .bitXor (.u64 a) _ = outcomeToPoison (evalBinOp .bitXor (.u64 a) _))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) a
  | _ =>
    cases v2 with
    | u64 b =>
      exact u64_cases_01
        (fun b => LeanMLIR.applyWordBinOp .bitXor _ (.u64 b) = outcomeToPoison (evalBinOp .bitXor _ (.u64 b)))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) b
    | _ => rfl

theorem mlir_shl (v1 v2 : Val) :
    LeanMLIR.applyWordBinOp .shl v1 v2 = outcomeToPoison (evalBinOp .shl v1 v2) := by
  cases v1 with
  | u64 a =>
    cases v2 with
    | u64 b => rfl
    | _ => rfl
  | u256 a =>
    cases v2 with
    | u64 b =>
      exact u64_cases_01
        (fun b => LeanMLIR.applyWordBinOp .shl (.u256 a) (.u64 b) = outcomeToPoison (evalBinOp .shl (.u256 a) (.u64 b)))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) b
    | u256 b =>
      have hL : LeanMLIR.applyWordBinOp .shl (.u256 a) (.u256 b) =
          LeanMLIR.PoisonOr.val (Val.u256 (LeanMLIR.ofWord256 (LeanMLIR.word256 a <<< (LeanMLIR.word256 b).toNat))) := rfl
      have hR : evalBinOp .shl (.u256 a) (.u256 b) =
          Except.ok (Val.u256 (UInt256.shl a b.toNat)) := rfl
      rw [hL, hR, word256_toNat, u256_shl_bv]
      rfl
    | _ => rfl
  | _ =>
    cases v2 with
    | u64 b =>
      exact u64_cases_01
        (fun b => LeanMLIR.applyWordBinOp .shl _ (.u64 b) = outcomeToPoison (evalBinOp .shl _ (.u64 b)))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) b
    | _ => rfl

theorem mlir_shr (v1 v2 : Val) :
    LeanMLIR.applyWordBinOp .shr v1 v2 = outcomeToPoison (evalBinOp .shr v1 v2) := by
  cases v1 with
  | u64 a =>
    cases v2 with
    | u64 b => rfl
    | _ => rfl
  | u256 a =>
    cases v2 with
    | u64 b =>
      exact u64_cases_01
        (fun b => LeanMLIR.applyWordBinOp .shr (.u256 a) (.u64 b) = outcomeToPoison (evalBinOp .shr (.u256 a) (.u64 b)))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) b
    | u256 b =>
      have hL : LeanMLIR.applyWordBinOp .shr (.u256 a) (.u256 b) =
          LeanMLIR.PoisonOr.val (Val.u256 (LeanMLIR.ofWord256 (LeanMLIR.word256 a >>> (LeanMLIR.word256 b).toNat))) := rfl
      have hR : evalBinOp .shr (.u256 a) (.u256 b) =
          Except.ok (Val.u256 (UInt256.shr a b.toNat)) := rfl
      rw [hL, hR, word256_toNat, u256_shr_bv]
      rfl
    | _ => rfl
  | _ =>
    cases v2 with
    | u64 b =>
      exact u64_cases_01
        (fun b => LeanMLIR.applyWordBinOp .shr _ (.u64 b) = outcomeToPoison (evalBinOp .shr _ (.u64 b)))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) b
    | _ => rfl

theorem mlir_sar (v1 v2 : Val) :
    LeanMLIR.applyWordBinOp .sar v1 v2 = outcomeToPoison (evalBinOp .sar v1 v2) := by
  cases v1 with
  | u64 a =>
    cases v2 with
    | u64 b =>
      have hL : LeanMLIR.applyWordBinOp .sar (.u64 a) (.u64 b) =
          LeanMLIR.PoisonOr.val (Val.u64 (UInt64.ofBitVec (LeanMLIR.sar64 a.toBitVec b.toBitVec))) := rfl
      rw [hL, u64_sar_bv]
      rfl
    | _ => rfl
  | u256 a =>
    cases v2 with
    | u256 b =>
      have hL : LeanMLIR.applyWordBinOp .sar (.u256 a) (.u256 b) =
          LeanMLIR.PoisonOr.val (Val.u256 (LeanMLIR.ofWord256 (LeanMLIR.sar256 (LeanMLIR.word256 a) (LeanMLIR.word256 b).toNat))) := rfl
      have hR : evalBinOp .sar (.u256 a) (.u256 b) =
          Except.ok (Val.u256 (UInt256.sar a b.toNat)) := rfl
      rw [hL, hR, word256_toNat, u256_sar_bv]
      rfl
    | _ => rfl
  | _ => cases v2 <;> rfl

theorem mlir_eq (v1 v2 : Val) :
    LeanMLIR.applyWordBinOp .eq v1 v2 = outcomeToPoison (evalBinOp .eq v1 v2) := by
  cases v1 with
  | u256 a =>
    cases v2 with
    | u256 b =>
      have hL : LeanMLIR.applyWordBinOp .eq (.u256 a) (.u256 b) =
          LeanMLIR.PoisonOr.val (Val.bool (LeanMLIR.word256 a == LeanMLIR.word256 b)) := rfl
      rw [hL, word_eq]
      rfl
    | _ => rfl
  | _ => cases v2 <;> rfl

theorem mlir_lt (v1 v2 : Val) :
    LeanMLIR.applyWordBinOp .lt v1 v2 = outcomeToPoison (evalBinOp .lt v1 v2) := by
  cases v1 with
  | u256 a =>
    cases v2 with
    | u256 b =>
      have hL : LeanMLIR.applyWordBinOp .lt (.u256 a) (.u256 b) =
          LeanMLIR.PoisonOr.val (Val.bool (decide (LeanMLIR.word256 a < LeanMLIR.word256 b))) := rfl
      rw [hL, word_lt]
      rfl
    | _ => rfl
  | _ => cases v2 <;> rfl

theorem mlir_le (v1 v2 : Val) :
    LeanMLIR.applyWordBinOp .le v1 v2 = outcomeToPoison (evalBinOp .le v1 v2) := by
  cases v1 with
  | u256 a =>
    cases v2 with
    | u256 b =>
      have hL : LeanMLIR.applyWordBinOp .le (.u256 a) (.u256 b) =
          LeanMLIR.PoisonOr.val (Val.bool (decide (LeanMLIR.word256 a ≤ LeanMLIR.word256 b))) := rfl
      rw [hL, word_le]
      rfl
    | _ => rfl
  | _ => cases v2 <;> rfl

theorem outcomeToPoison_optPair (o1 o2 : Option UInt256)
    (g : UInt256 → UInt256 → Except UBError Val) (err : Except UBError Val) :
    outcomeToPoison (optPairMatch (Except UBError Val) o1 o2 g err) =
      optPairMatch (LeanMLIR.PoisonOr Val) o1 o2 (fun a b => outcomeToPoison (g a b)) (outcomeToPoison err) := by
  cases o1 <;> cases o2 <;> rfl

theorem mlir_addChecked_inner (a b : UInt256) :
    (if BitVec.uaddOverflow (LeanMLIR.word256 a) (LeanMLIR.word256 b) then
       LeanMLIR.PoisonOr.poison "binOp64 overflow"
     else LeanMLIR.PoisonOr.val (Val.u256 (LeanMLIR.ofWord256 (LeanMLIR.word256 a + LeanMLIR.word256 b)))) =
    outcomeToPoison (evalBinOp.match_9 (fun _ => Except UBError Val) (a.addChecked b)
      (fun res => Except.ok (Val.u256 res))
      (fun _ => Except.error (UBError.arithmeticOverflow "addChecked256 overflow"))) := by
  rw [← addChecked_inner_eq, outcomeToPoison_ite]
  rfl

theorem mlir_subChecked_inner (a b : UInt256) :
    (if decide (LeanMLIR.word256 a < LeanMLIR.word256 b) then
       LeanMLIR.PoisonOr.poison "binOp64 underflow"
     else LeanMLIR.PoisonOr.val (Val.u256 (LeanMLIR.ofWord256 (LeanMLIR.word256 a - LeanMLIR.word256 b)))) =
    outcomeToPoison (evalBinOp.match_9 (fun _ => Except UBError Val) (a.subChecked b)
      (fun res => Except.ok (Val.u256 res))
      (fun _ => Except.error (UBError.arithmeticOverflow "subChecked256 underflow"))) := by
  rw [← subChecked_inner_eq, outcomeToPoison_ite]
  rfl

theorem mlir_mulChecked_inner (a b : UInt256) :
    (if BitVec.umulOverflow (LeanMLIR.word256 a) (LeanMLIR.word256 b) then
       LeanMLIR.PoisonOr.poison "binOp64 overflow"
     else LeanMLIR.PoisonOr.val (Val.u256 (LeanMLIR.ofWord256 (LeanMLIR.word256 a * LeanMLIR.word256 b)))) =
    outcomeToPoison (evalBinOp.match_9 (fun _ => Except UBError Val) (a.mulChecked b)
      (fun res => Except.ok (Val.u256 res))
      (fun _ => Except.error (UBError.arithmeticOverflow "mulChecked256 overflow"))) := by
  rw [← mulChecked_inner_eq, outcomeToPoison_ite]
  rfl

theorem mlir_addChecked (v1 v2 : Val) :
    LeanMLIR.applyWordBinOp .addChecked256 v1 v2 = outcomeToPoison (evalBinOp .addChecked256 v1 v2) := by
  have hL : LeanMLIR.applyWordBinOp .addChecked256 v1 v2 =
      (match (v1.toU256?).map LeanMLIR.word256, (v2.toU256?).map LeanMLIR.word256 with
       | some a, some b =>
         if BitVec.uaddOverflow a b then LeanMLIR.PoisonOr.poison "binOp64 overflow"
         else LeanMLIR.PoisonOr.val (Val.u256 (LeanMLIR.ofWord256 (a + b)))
       | _, _ => LeanMLIR.PoisonOr.poison "binOp64 type") := by
    have h0 : LeanMLIR.applyWordBinOp .addChecked256 v1 v2 =
      (match LeanMLIR.asWord256 v1, LeanMLIR.asWord256 v2 with
       | some a, some b =>
         if BitVec.uaddOverflow a b then LeanMLIR.PoisonOr.poison "binOp64 overflow"
         else LeanMLIR.PoisonOr.val (Val.u256 (LeanMLIR.ofWord256 (a + b)))
       | _, _ => LeanMLIR.PoisonOr.poison "binOp64 type") := rfl
    rw [h0, asWord256_eq v1, asWord256_eq v2]
  have hM := optPair_map_eq (LeanMLIR.PoisonOr Val) v1.toU256? v2.toU256?
    (fun a b =>
      if BitVec.uaddOverflow a b then LeanMLIR.PoisonOr.poison "binOp64 overflow"
      else LeanMLIR.PoisonOr.val (Val.u256 (LeanMLIR.ofWord256 (a + b))))
    (fun a b => outcomeToPoison (evalBinOp.match_9 (fun _ => Except UBError Val) (a.addChecked b)
      (fun res => Except.ok (Val.u256 res))
      (fun _ => Except.error (UBError.arithmeticOverflow "addChecked256 overflow"))))
    (outcomeToPoison (Except.error (UBError.typeError "addChecked256 requires u256/u64 operands")))
    mlir_addChecked_inner
  have hR1 : outcomeToPoison (evalBinOp .addChecked256 v1 v2) =
      outcomeToPoison (optPairMatch (Except UBError Val) v1.toU256? v2.toU256?
        (fun a b => evalBinOp.match_9 (fun _ => Except UBError Val) (a.addChecked b)
          (fun res => Except.ok (Val.u256 res))
          (fun _ => Except.error (UBError.arithmeticOverflow "addChecked256 overflow")))
        (Except.error (UBError.typeError "addChecked256 requires u256/u64 operands"))) :=
    congrArg outcomeToPoison (eval_addChecked_pair v1 v2)
  have hR2 := outcomeToPoison_optPair v1.toU256? v2.toU256?
    (fun a b => evalBinOp.match_9 (fun _ => Except UBError Val) (a.addChecked b)
      (fun res => Except.ok (Val.u256 res))
      (fun _ => Except.error (UBError.arithmeticOverflow "addChecked256 overflow")))
    (Except.error (UBError.typeError "addChecked256 requires u256/u64 operands"))
  exact @Eq.trans (LeanMLIR.PoisonOr Val) _ _ _ hL
    (@Eq.trans (LeanMLIR.PoisonOr Val) _ _ _ hM (Eq.symm (@Eq.trans (LeanMLIR.PoisonOr Val) _ _ _ hR1 hR2)))

theorem mlir_subChecked (v1 v2 : Val) :
    LeanMLIR.applyWordBinOp .subChecked256 v1 v2 = outcomeToPoison (evalBinOp .subChecked256 v1 v2) := by
  have hL : LeanMLIR.applyWordBinOp .subChecked256 v1 v2 =
      (match (v1.toU256?).map LeanMLIR.word256, (v2.toU256?).map LeanMLIR.word256 with
       | some a, some b =>
         if decide (a < b) then LeanMLIR.PoisonOr.poison "binOp64 underflow"
         else LeanMLIR.PoisonOr.val (Val.u256 (LeanMLIR.ofWord256 (a - b)))
       | _, _ => LeanMLIR.PoisonOr.poison "binOp64 type") := by
    have h0 : LeanMLIR.applyWordBinOp .subChecked256 v1 v2 =
      (match LeanMLIR.asWord256 v1, LeanMLIR.asWord256 v2 with
       | some a, some b =>
         if decide (a < b) then LeanMLIR.PoisonOr.poison "binOp64 underflow"
         else LeanMLIR.PoisonOr.val (Val.u256 (LeanMLIR.ofWord256 (a - b)))
       | _, _ => LeanMLIR.PoisonOr.poison "binOp64 type") := rfl
    rw [h0, asWord256_eq v1, asWord256_eq v2]
  have hM := optPair_map_eq (LeanMLIR.PoisonOr Val) v1.toU256? v2.toU256?
    (fun a b =>
      if decide (a < b) then LeanMLIR.PoisonOr.poison "binOp64 underflow"
      else LeanMLIR.PoisonOr.val (Val.u256 (LeanMLIR.ofWord256 (a - b))))
    (fun a b => outcomeToPoison (evalBinOp.match_9 (fun _ => Except UBError Val) (a.subChecked b)
      (fun res => Except.ok (Val.u256 res))
      (fun _ => Except.error (UBError.arithmeticOverflow "subChecked256 underflow"))))
    (outcomeToPoison (Except.error (UBError.typeError "subChecked256 requires u256/u64 operands")))
    mlir_subChecked_inner
  have hR1 : outcomeToPoison (evalBinOp .subChecked256 v1 v2) =
      outcomeToPoison (optPairMatch (Except UBError Val) v1.toU256? v2.toU256?
        (fun a b => evalBinOp.match_9 (fun _ => Except UBError Val) (a.subChecked b)
          (fun res => Except.ok (Val.u256 res))
          (fun _ => Except.error (UBError.arithmeticOverflow "subChecked256 underflow")))
        (Except.error (UBError.typeError "subChecked256 requires u256/u64 operands"))) :=
    congrArg outcomeToPoison (eval_subChecked_pair v1 v2)
  have hR2 := outcomeToPoison_optPair v1.toU256? v2.toU256?
    (fun a b => evalBinOp.match_9 (fun _ => Except UBError Val) (a.subChecked b)
      (fun res => Except.ok (Val.u256 res))
      (fun _ => Except.error (UBError.arithmeticOverflow "subChecked256 underflow")))
    (Except.error (UBError.typeError "subChecked256 requires u256/u64 operands"))
  exact @Eq.trans (LeanMLIR.PoisonOr Val) _ _ _ hL
    (@Eq.trans (LeanMLIR.PoisonOr Val) _ _ _ hM (Eq.symm (@Eq.trans (LeanMLIR.PoisonOr Val) _ _ _ hR1 hR2)))

theorem mlir_mulChecked (v1 v2 : Val) :
    LeanMLIR.applyWordBinOp .mulChecked256 v1 v2 = outcomeToPoison (evalBinOp .mulChecked256 v1 v2) := by
  have hL : LeanMLIR.applyWordBinOp .mulChecked256 v1 v2 =
      (match (v1.toU256?).map LeanMLIR.word256, (v2.toU256?).map LeanMLIR.word256 with
       | some a, some b =>
         if BitVec.umulOverflow a b then LeanMLIR.PoisonOr.poison "binOp64 overflow"
         else LeanMLIR.PoisonOr.val (Val.u256 (LeanMLIR.ofWord256 (a * b)))
       | _, _ => LeanMLIR.PoisonOr.poison "binOp64 type") := by
    have h0 : LeanMLIR.applyWordBinOp .mulChecked256 v1 v2 =
      (match LeanMLIR.asWord256 v1, LeanMLIR.asWord256 v2 with
       | some a, some b =>
         if BitVec.umulOverflow a b then LeanMLIR.PoisonOr.poison "binOp64 overflow"
         else LeanMLIR.PoisonOr.val (Val.u256 (LeanMLIR.ofWord256 (a * b)))
       | _, _ => LeanMLIR.PoisonOr.poison "binOp64 type") := rfl
    rw [h0, asWord256_eq v1, asWord256_eq v2]
  have hM := optPair_map_eq (LeanMLIR.PoisonOr Val) v1.toU256? v2.toU256?
    (fun a b =>
      if BitVec.umulOverflow a b then LeanMLIR.PoisonOr.poison "binOp64 overflow"
      else LeanMLIR.PoisonOr.val (Val.u256 (LeanMLIR.ofWord256 (a * b))))
    (fun a b => outcomeToPoison (evalBinOp.match_9 (fun _ => Except UBError Val) (a.mulChecked b)
      (fun res => Except.ok (Val.u256 res))
      (fun _ => Except.error (UBError.arithmeticOverflow "mulChecked256 overflow"))))
    (outcomeToPoison (Except.error (UBError.typeError "mulChecked256 requires u256/u64 operands")))
    mlir_mulChecked_inner
  have hR1 : outcomeToPoison (evalBinOp .mulChecked256 v1 v2) =
      outcomeToPoison (optPairMatch (Except UBError Val) v1.toU256? v2.toU256?
        (fun a b => evalBinOp.match_9 (fun _ => Except UBError Val) (a.mulChecked b)
          (fun res => Except.ok (Val.u256 res))
          (fun _ => Except.error (UBError.arithmeticOverflow "mulChecked256 overflow")))
        (Except.error (UBError.typeError "mulChecked256 requires u256/u64 operands"))) :=
    congrArg outcomeToPoison (eval_mulChecked_pair v1 v2)
  have hR2 := outcomeToPoison_optPair v1.toU256? v2.toU256?
    (fun a b => evalBinOp.match_9 (fun _ => Except UBError Val) (a.mulChecked b)
      (fun res => Except.ok (Val.u256 res))
      (fun _ => Except.error (UBError.arithmeticOverflow "mulChecked256 overflow")))
    (Except.error (UBError.typeError "mulChecked256 requires u256/u64 operands"))
  exact @Eq.trans (LeanMLIR.PoisonOr Val) _ _ _ hL
    (@Eq.trans (LeanMLIR.PoisonOr Val) _ _ _ hM (Eq.symm (@Eq.trans (LeanMLIR.PoisonOr Val) _ _ _ hR1 hR2)))

theorem mlir_clmul (v1 v2 : Val) :
    LeanMLIR.applyWordBinOp .clmul64 v1 v2 = outcomeToPoison (evalBinOp .clmul64 v1 v2) := by
  cases v1 <;> cases v2 <;> rfl

theorem mlir_clmulHi (v1 v2 : Val) :
    LeanMLIR.applyWordBinOp .clmul64Hi v1 v2 = outcomeToPoison (evalBinOp .clmul64Hi v1 v2) := by
  cases v1 <;> cases v2 <;> rfl

theorem mlir_gf2 (v1 v2 : Val) :
    LeanMLIR.applyWordBinOp .gf2Affine v1 v2 = outcomeToPoison (evalBinOp .gf2Affine v1 v2) := by
  cases v1 <;> cases v2 <;> rfl

theorem mlir_eor3 (v1 v2 : Val) :
    LeanMLIR.applyWordBinOp .eor3 v1 v2 = outcomeToPoison (evalBinOp .eor3 v1 v2) := by
  cases v1 <;> cases v2 <;> rfl

theorem applyWordBinOp_eq_eval (op : BinOp) (v1 v2 : Val) :
    LeanMLIR.applyWordBinOp op v1 v2 = outcomeToPoison (evalBinOp op v1 v2) := by
  cases op with
  | add => exact mlir_add v1 v2
  | sub => exact mlir_sub v1 v2
  | mul => exact mlir_mul v1 v2
  | div => exact mlir_div v1 v2
  | mod => exact mlir_mod v1 v2
  | bitAnd => exact mlir_bitAnd v1 v2
  | bitOr => exact mlir_bitOr v1 v2
  | bitXor => exact mlir_bitXor v1 v2
  | shl => exact mlir_shl v1 v2
  | shr => exact mlir_shr v1 v2
  | sar => exact mlir_sar v1 v2
  | eq => exact mlir_eq v1 v2
  | lt => exact mlir_lt v1 v2
  | le => exact mlir_le v1 v2
  | addChecked256 => exact mlir_addChecked v1 v2
  | subChecked256 => exact mlir_subChecked v1 v2
  | mulChecked256 => exact mlir_mulChecked v1 v2
  | clmul64 => exact mlir_clmul v1 v2
  | clmul64Hi => exact mlir_clmulHi v1 v2
  | gf2Affine => exact mlir_gf2 v1 v2
  | eor3 => exact mlir_eor3 v1 v2

theorem applyWordBinOp_agrees (op : BinOp) (v1 v2 v : Val)
    (h : evalBinOp op v1 v2 = .ok v) :
    LeanMLIR.applyWordBinOp op v1 v2 = .val v := by
  rw [applyWordBinOp_eq_eval, h]
  rfl


/-- Encode an LNIR `(VarEnv, HeapState)` pair into `LeanMLIR.EncodedMLIRState`. -/
def encodeState (env : VarEnv) (st : HeapState) : LeanMLIR.EncodedMLIRState :=
  { env := env, heap := st }

/-- Re-export `LeanMLIR.lowerLNIRToMLIR` in `LeanNative.Backend.Proofs`. -/
abbrev lowerLNIRToMLIR : LNIRCode → Except String LeanMLIR.LLVM.Com :=
  LeanMLIR.lowerLNIRToMLIR

/-- Soundness of `LeanMLIR.lowerScalarToMLIR` against `evalScalarExpr` and `LeanMLIR.denoteExpr`. -/
theorem lowerScalarToMLIR_sound (env : VarEnv) (se : ScalarExpr) (v : Val)
    (heval : evalScalarExpr env se = .ok v) :
    LeanMLIR.denoteExpr env (LeanMLIR.lowerScalarToMLIR se) = .val v := by
  induction se generalizing v with
  | constU64 n =>
    dsimp [evalScalarExpr] at heval
    injection heval with heq
    subst heq
    simp [LeanMLIR.lowerScalarToMLIR, LeanMLIR.denoteExpr]
  | constBool b =>
    dsimp [evalScalarExpr] at heval
    injection heval with heq
    subst heq
    rfl
  | var id =>
    dsimp [evalScalarExpr, LeanMLIR.lowerScalarToMLIR, LeanMLIR.denoteExpr] at heval ⊢
    cases h : env id with
    | none => simp [h] at heval
    | some val =>
      simp [h] at heval
      subst heval
      rfl
  | binOp op l r ihl ihr =>
    dsimp [evalScalarExpr, LeanMLIR.lowerScalarToMLIR, LeanMLIR.denoteExpr] at heval ⊢
    cases hl : evalScalarExpr env l with
    | error _ => simp [hl] at heval
    | ok vl =>
      cases hr : evalScalarExpr env r with
      | error _ => simp [hl, hr] at heval
      | ok vr =>
        simp only [hl, hr] at heval
        rw [ihl vl hl, ihr vr hr]
        dsimp only
        exact applyWordBinOp_agrees op vl vr v heval
  | unaryOp op a iha =>
    dsimp [evalScalarExpr, LeanMLIR.lowerScalarToMLIR, LeanMLIR.denoteExpr] at heval ⊢
    cases ha : evalScalarExpr env a with
    | error _ => simp [ha] at heval
    | ok va =>
      simp only [ha] at heval
      rw [iha va ha]
      dsimp only
      exact applyWordUnaryOp_agrees op va v heval
  | select c t e ihc iht ihe =>
    dsimp [evalScalarExpr, LeanMLIR.lowerScalarToMLIR, LeanMLIR.denoteExpr] at heval ⊢
    cases hc : evalScalarExpr env c with
    | error _ => simp [hc] at heval
    | ok vc =>
      simp only [hc] at heval
      rw [ihc vc hc]
      cases vc with
      | bool b =>
        cases b with
        | true => exact iht v heval
        | false => exact ihe v heval
      | u64 n =>
        dsimp only at heval ⊢
        split at heval <;> rename_i hcond <;> simp [hcond]
        · exact iht v heval
        · exact ihe v heval
      | u256 w =>
        dsimp only at heval ⊢
        split at heval <;> rename_i hcond <;> simp [hcond]
        · exact iht v heval
        · exact ihe v heval
      | _ => contradiction
  | fma a b c iha ihb ihc =>
    dsimp [evalScalarExpr, LeanMLIR.lowerScalarToMLIR, LeanMLIR.denoteExpr] at heval ⊢
    cases ha : evalScalarExpr env a with
    | error _ => simp [ha] at heval
    | ok va =>
      cases hb : evalScalarExpr env b with
      | error _ => simp [ha, hb] at heval
      | ok vb =>
        simp only [ha, hb] at heval
        rw [iha va ha, ihb vb hb]
        dsimp only
        cases hmul : evalBinOp .mul va vb with
        | error _ => simp [hmul] at heval
        | ok vab =>
          rw [applyWordBinOp_agrees .mul va vb vab hmul]
          cases hc : evalScalarExpr env c with
          | error _ => simp [hmul, hc] at heval
          | ok vc =>
            simp only [hmul, hc] at heval
            rw [ihc vc hc]
            dsimp only
            exact applyWordBinOp_agrees .add vab vc v heval

/-- Milestone M5 (Item 1): Machine-checked soundness of `lowerLNIRToMLIR` (`lowerToLeanMLIR_sound`)
    against `LeanMLIR.denote` (`BitVec 64` + `PoisonOr` semantics, `0 sorryAx`). -/
theorem lowerToLeanMLIR_sound (code : LNIRCode) (mlirCom : LeanMLIR.LLVM.Com)
    (fuel : Nat) (env : VarEnv) (st : HeapState) (v : Val) (st' : HeapState)
    (h_lower : lowerLNIRToMLIR code = .ok mlirCom)
    (h_eval : evalCode fuel env st code = .ok (v, st')) :
    LeanMLIR.denote mlirCom (encodeState env st) = .val (v, st') := by
  unfold lowerLNIRToMLIR at h_lower
  induction code generalizing mlirCom env st v st' with
  | letBind dst ty val k ih =>
    cases val with
    | scalar se =>
      dsimp [LeanMLIR.lowerLNIRToMLIR] at h_lower
      cases hk : LeanMLIR.lowerLNIRToMLIR k with
      | error _ => rw [hk] at h_lower; contradiction
      | ok k' =>
        rw [hk] at h_lower
        injection h_lower with heq
        subst heq
        dsimp [evalCode, evalExpr] at h_eval
        cases hse : evalScalarExpr env se with
        | error _ => rw [hse] at h_eval; contradiction
        | ok vse =>
          rw [hse] at h_eval
          dsimp [LeanMLIR.denote, encodeState]
          rw [lowerScalarToMLIR_sound env se vse hse]
          exact ih k' (env.bind dst vse) st v st' hk h_eval
    | _ =>
      simp [LeanMLIR.lowerLNIRToMLIR] at h_lower
  | ite condVar thenBranch elseBranch iht ihe =>
    dsimp [LeanMLIR.lowerLNIRToMLIR] at h_lower
    cases ht : LeanMLIR.lowerLNIRToMLIR thenBranch with
    | error _ => rw [ht] at h_lower; contradiction
    | ok t' =>
      rw [ht] at h_lower
      cases he : LeanMLIR.lowerLNIRToMLIR elseBranch with
      | error _ => rw [he] at h_lower; contradiction
      | ok e' =>
        rw [he] at h_lower
        injection h_lower with heq
        subst heq
        dsimp [evalCode] at h_eval
        dsimp [LeanMLIR.denote, encodeState]
        cases hc : env condVar with
        | none => rw [hc] at h_eval; contradiction
        | some vc =>
          rw [hc] at h_eval
          cases vc with
          | bool b =>
            cases b with
            | true => exact iht t' env st v st' ht h_eval
            | false => exact ihe e' env st v st' he h_eval
          | u64 n =>
            dsimp only at h_eval ⊢
            split at h_eval <;> rename_i hcond <;> simp [hcond]
            · exact iht t' env st v st' ht h_eval
            · exact ihe e' env st v st' he h_eval
          | u256 w =>
            dsimp only at h_eval ⊢
            split at h_eval <;> rename_i hcond <;> simp [hcond]
            · exact iht t' env st v st' ht h_eval
            · exact ihe e' env st v st' he h_eval
          | _ => contradiction
  | ret retVar =>
    dsimp [LeanMLIR.lowerLNIRToMLIR] at h_lower
    injection h_lower with heq
    subst heq
    dsimp [evalCode] at h_eval
    dsimp [LeanMLIR.denote, encodeState]
    cases hv : env retVar with
    | none => rw [hv] at h_eval; contradiction
    | some val =>
      rw [hv] at h_eval
      injection h_eval with hpair
      rw [← hpair]
  | unreachable =>
    dsimp [evalCode] at h_eval
    contradiction
  | _ =>
    simp [LeanMLIR.lowerLNIRToMLIR] at h_lower

/-- Generate the ARM64 NEON instruction sequence for an $\mathbb{F}_{2^{128}}$ NTT butterfly over `indices`. -/
def instructions_f128_ntt (indices : List Nat) : List LNSym.Arm64Instr :=
  indices.foldr (fun idx acc => LNSym.butterflyStepInstrs idx ++ acc) []

/-- Evaluate the LNIR $\mathbb{F}_{2^{128}}$ additive NTT butterfly specification over `indices`,
    accumulating into `(accU, accV)`. -/
def evalLNIRF128NttLoop (uSlice vSlice : List LNSym.QReg) (tw : LNSym.QReg)
    (accU accV : List LNSym.QReg) : List Nat → List LNSym.QReg × List LNSym.QReg
  | [] => (accU, accV)
  | idx :: rest =>
    let u := uSlice[idx]?.getD LNSym.QReg.zero
    let v := vSlice[idx]?.getD LNSym.QReg.zero
    let (u', v') := LNSym.gf128ButterflyLane u v tw
    evalLNIRF128NttLoop uSlice vSlice tw (accU ++ [u']) (accV ++ [v']) rest

/-- Top-level LNIR $\mathbb{F}_{2^{128}}$ butterfly slice specification starting from empty output slices. -/
def evalLNIRF128NttSpec (uSlice vSlice : List LNSym.QReg) (tw : LNSym.QReg)
    (indices : List Nat) : List LNSym.QReg × List LNSym.QReg :=
  evalLNIRF128NttLoop uSlice vSlice tw [] [] indices

/-- ABI invariant relating an `LNSym.ArmState` to input slices `(uSlice, vSlice)`, twiddle `tw` in `q0`,
    and accumulated outputs `(accU, accV)`. -/
def Arm64LoopStateInv (s : LNSym.ArmState) (uSlice vSlice : List LNSym.QReg)
    (tw : LNSym.QReg) (accU accV : List LNSym.QReg) : Prop :=
  s.validABI = true ∧
  s.sliceU = uSlice ∧
  s.sliceV = vSlice ∧
  s.readQ 0 = tw ∧
  s.outU = accU ∧
  s.outV = accV

/-- Entry ABI precondition for `arm64_f128_kernel_refines_lnir`. -/
def Arm64SliceABICorresponds (s0 : LNSym.ArmState) (uSlice vSlice : List LNSym.QReg)
    (tw : LNSym.QReg) : Prop :=
  Arm64LoopStateInv s0 uSlice vSlice tw [] []

/-- Symbolic execution lemma for one 8-instruction ARM64 NEON butterfly step (`butterflyStepInstrs idx`):
    proves that `PMULL`/`PMULL2`/`reducePoly0x87`/`VEOR` on registers `q0..q6` computes
    `LNSym.gf128ButterflyLane u v tw` and preserves `Arm64LoopStateInv`. -/
theorem runArm64_butterflyStepInstrs_inv (idx : Nat) (s : LNSym.ArmState)
    (uSlice vSlice : List LNSym.QReg) (tw : LNSym.QReg) (accU accV : List LNSym.QReg)
    (hinv : Arm64LoopStateInv s uSlice vSlice tw accU accV) :
    let u := uSlice[idx]?.getD LNSym.QReg.zero
    let v := vSlice[idx]?.getD LNSym.QReg.zero
    let (u', v') := LNSym.gf128ButterflyLane u v tw
    Arm64LoopStateInv (LNSym.runArm64 (LNSym.butterflyStepInstrs idx) s)
      uSlice vSlice tw (accU ++ [u']) (accV ++ [v']) := by
  rcases hinv with ⟨hvalid, hsu, hsv, hq0, houtU, houtV⟩
  dsimp [LNSym.butterflyStepInstrs, LNSym.runArm64, LNSym.execInstr,
         LNSym.ArmState.readQ, LNSym.ArmState.writeQ,
         LNSym.gf128ButterflyLane, LNSym.QReg.mulGF128,
         Arm64LoopStateInv] at hq0 ⊢
  simp [hvalid, hsu, hsv, hq0, houtU, houtV]

/-- Inductive loop invariant across arbitrary index lists `indices : List Nat`. -/
theorem runArm64_instructions_f128_ntt_loop (indices : List Nat) (s : LNSym.ArmState)
    (uSlice vSlice : List LNSym.QReg) (tw : LNSym.QReg) (accU accV : List LNSym.QReg)
    (hinv : Arm64LoopStateInv s uSlice vSlice tw accU accV) :
    LNSym.extractSlice (LNSym.runArm64 (instructions_f128_ntt indices) s) =
      evalLNIRF128NttLoop uSlice vSlice tw accU accV indices := by
  induction indices generalizing s accU accV with
  | nil =>
    rcases hinv with ⟨_, _, _, _, houtU, houtV⟩
    simp [instructions_f128_ntt, LNSym.runArm64, LNSym.extractSlice, evalLNIRF128NttLoop, houtU, houtV]
  | cons idx rest ih =>
    dsimp [instructions_f128_ntt, evalLNIRF128NttLoop]
    rw [LNSym.runArm64_append]
    have hstep := runArm64_butterflyStepInstrs_inv idx s uSlice vSlice tw accU accV hinv
    exact ih (LNSym.runArm64 (LNSym.butterflyStepInstrs idx) s)
      (accU ++ [(LNSym.gf128ButterflyLane (uSlice[idx]?.getD LNSym.QReg.zero) (vSlice[idx]?.getD LNSym.QReg.zero) tw).1])
      (accV ++ [(LNSym.gf128ButterflyLane (uSlice[idx]?.getD LNSym.QReg.zero) (vSlice[idx]?.getD LNSym.QReg.zero) tw).2])
      hstep

/-- Milestone M5 (Item 2): Machine-checked refinement of the 8-instruction ARM64 NEON
    $\mathbb{F}_{2^{128}}$ `PMULL`/`PMULL2`/polynomial-`0x87` butterfly kernel against `evalLNIRF128NttSpec`
    (`arm64_f128_kernel_refines_lnir`, `0 sorryAx`). -/
theorem arm64_f128_kernel_refines_lnir (s0 : LNSym.ArmState)
    (uSlice vSlice : List LNSym.QReg) (tw : LNSym.QReg) (indices : List Nat)
    (h_abi : Arm64SliceABICorresponds s0 uSlice vSlice tw) :
    LNSym.extractSlice (LNSym.runArm64 (instructions_f128_ntt indices) s0) =
      evalLNIRF128NttSpec uSlice vSlice tw indices :=
  runArm64_instructions_f128_ntt_loop indices s0 uSlice vSlice tw [] [] h_abi

end LeanNative.Backend.Proofs
