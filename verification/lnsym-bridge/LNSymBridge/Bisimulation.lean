import LNSymBridge.MirroredModel
import Arm.Exec
import Arm.Memory.MemoryProofs
import Tactics.Sym
import Tactics.StepThms
import Tactics.Aggregate
import Tactics.CSE
import Tactics.ClearNamed
import Arm.Memory.SeparateAutomation

namespace LNSymBridge

open BitVec
open LeanNative.IR
open LeanNative.Backend.Semantics

/-- Pack a `LNSym.QReg` (`(lo, hi)` of `UInt64`s) into a 128-bit `ArmState` SIMD register
    (`hi` in bits `[127:64]`, `lo` in bits `[63:0]`), matching `Vpart_read` lanes 0 and 1. -/
def qregToBv128 (q : LNSym.QReg) : BitVec 128 :=
  q.hi.toBitVec ++ q.lo.toBitVec

/-- Unpack a 128-bit `ArmState` SIMD register into a `LNSym.QReg`. -/
def bv128ToQReg (v : BitVec 128) : LNSym.QReg :=
  ⟨UInt64.ofBitVec (BitVec.extractLsb' 0 64 v), UInt64.ofBitVec (BitVec.extractLsb' 64 64 v)⟩

private theorem extractLsb'_0_64_append (hi lo : BitVec 64) :
    BitVec.extractLsb' 0 64 (hi ++ lo) = lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_extractLsb', Nat.zero_add, BitVec.getLsbD_append]
  simp [hk]

private theorem extractLsb'_64_64_append (hi lo : BitVec 64) :
    BitVec.extractLsb' 64 64 (hi ++ lo) = hi := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  have hlt : ¬(64 + k < 64) := by omega
  have hsub : 64 + k - 64 = k := by omega
  simp [hk, hlt, hsub]

private theorem append_extractLsb'_64_64_0_64 (v : BitVec 128) :
    BitVec.extractLsb' 64 64 v ++ BitVec.extractLsb' 0 64 v = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_append]
  by_cases hk64 : k < 64
  · simp [hk64]
  · have hsub : 64 + (k - 64) = k := by omega
    simp [hk64, show k - 64 < 64 by omega, hsub]

@[simp]
theorem bv128ToQReg_qregToBv128 (q : LNSym.QReg) :
    bv128ToQReg (qregToBv128 q) = q := by
  rcases q with ⟨lo, hi⟩
  simp [bv128ToQReg, qregToBv128, extractLsb'_0_64_append, extractLsb'_64_64_append]

@[simp]
theorem qregToBv128_bv128ToQReg (v : BitVec 128) :
    qregToBv128 (bv128ToQReg v) = v := by
  simp only [qregToBv128, bv128ToQReg, UInt64.toBitVec_ofBitVec]
  exact append_extractLsb'_64_64_0_64 v

theorem qregToBv128_xor (a b : LNSym.QReg) :
    qregToBv128 (LNSym.QReg.xor a b) = qregToBv128 a ^^^ qregToBv128 b := by
  rcases a with ⟨alo, ahi⟩
  rcases b with ⟨blo, bhi⟩
  simp only [qregToBv128, LNSym.QReg.xor, UInt64.toBitVec_xor]
  apply BitVec.eq_of_getLsbD_eq
  intro k _hk
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_xor]
  by_cases hk64 : k < 64 <;> simp [hk64]

private theorem extractLsb'_0_64_xor (x y : BitVec (64 + 64)) :
    BitVec.extractLsb' 0 64 (x ^^^ y) = BitVec.extractLsb' 0 64 x ^^^ BitVec.extractLsb' 0 64 y := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp [hk]

private theorem extractLsb'_64_64_xor (x y : BitVec (64 + 64)) :
    BitVec.extractLsb' 64 64 (x ^^^ y) = BitVec.extractLsb' 64 64 x ^^^ BitVec.extractLsb' 64 64 y := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp [hk]

private theorem uint64_shift_test_eq_lsb (b : UInt64) (i : Nat) (hi : i < 64) :
    (((b >>> i.toUInt64) &&& 1) == 1) = decide (lsb b.toBitVec i = 1#1) := by
  have hi_mod : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
  have h_shr : (b >>> i.toUInt64).toBitVec = b.toBitVec >>> i := by
    change b.toBitVec >>> (i.toUInt64.toBitVec % 64#64) = b.toBitVec >>> i
    have hmodbv : (i.toUInt64.toBitVec % 64#64).toNat = i := by
      simp [hi_mod, Nat.mod_eq_of_lt hi]
    rw [BitVec.ushiftRight_eq', hmodbv]
  have h_lhs : (((b >>> i.toUInt64) &&& 1) == 1) =
      decide (((b.toBitVec >>> i) &&& 1#64) = 1#64) := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq]
    constructor <;> intro h
    · have hbv := congrArg UInt64.toBitVec h
      simpa [UInt64.toBitVec_and, h_shr] using hbv
    · apply UInt64.eq_of_toBitVec_eq
      simpa [UInt64.toBitVec_and, h_shr] using h
  rw [h_lhs]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, decide_eq_true_eq]
  constructor <;> intro h
  · apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    have h0 := congrArg (fun v => v.getLsbD 0) h
    simpa [lsb, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, hi] using h0
  · apply BitVec.eq_of_getLsbD_eq
    intro k hk
    cases k with
    | zero =>
      have h0 := congrArg (fun v => v.getLsbD 0) h
      simpa [lsb, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, hi] using h0
    | succ k' =>
      have h1 : (1#64).getLsbD (k' + 1) = false := by
        rw [BitVec.getLsbD_ofNat]
        simp [hk, Nat.testBit_succ]
      simp [BitVec.getLsbD_and, h1]

private theorem uint64_shl_eq_extract_lo (a : UInt64) (i : Nat) (hi : i < 64) :
    (a <<< i.toUInt64).toBitVec =
      BitVec.extractLsb' 0 64 (BitVec.zeroExtend (64 + 64) a.toBitVec <<< i) := by
  have hi_mod : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
  have h_shl : (a <<< i.toUInt64).toBitVec = a.toBitVec <<< i := by
    change a.toBitVec <<< (i.toUInt64.toBitVec % 64#64) = a.toBitVec <<< i
    have hmodbv : (i.toUInt64.toBitVec % 64#64).toNat = i := by
      simp [hi_mod, Nat.mod_eq_of_lt hi]
    rw [BitVec.shiftLeft_eq', hmodbv]
  rw [h_shl]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb', Nat.zero_add,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases hki : k < i
  · simp [hk, hki]
  · have hsub : k - i < 64 + 64 := by omega
    simp [hk, hki, hsub, show k < 64 + 64 by omega]

private theorem uint64_shr_64_sub_eq_extract_hi (a : UInt64) (i : Nat) (_hi0 : 1 ≤ i) (hi : i < 64) :
    (a >>> (64 - i.toUInt64)).toBitVec =
      BitVec.extractLsb' 64 64 (BitVec.zeroExtend (64 + 64) a.toBitVec <<< i) := by
  have hsub_u64 : (64 : UInt64) - i.toUInt64 = (64 - i).toUInt64 := by
    apply UInt64.eq_of_toBitVec_eq
    apply BitVec.eq_of_toNat_eq
    simp [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 64 - i < 2 ^ 64 by omega)]
    omega
  have h_shr : (a >>> (64 - i.toUInt64)).toBitVec = a.toBitVec >>> (64 - i) := by
    rw [hsub_u64]
    change a.toBitVec >>> ((64 - i).toUInt64.toBitVec % 64#64) = a.toBitVec >>> (64 - i)
    have hlt : 64 - i < 64 := by omega
    have hmod : (64 - i) % 2 ^ 64 = 64 - i := Nat.mod_eq_of_lt (by omega)
    have hmodbv : ((64 - i).toUInt64.toBitVec % 64#64).toNat = 64 - i := by
      simp [hmod, Nat.mod_eq_of_lt hlt]
    rw [BitVec.ushiftRight_eq', hmodbv]
  rw [h_shr]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  have hidx : 64 - i + k = 64 + k - i := by omega
  have hsub : 64 + k - i < 64 + 64 := by omega
  have hnlt : ¬(64 + k < i) := by omega
  have hlt128 : 64 + k < 64 + 64 := by omega
  simp [hk, hidx, hsub, hnlt, hlt128]

private theorem clmul64_go_eq_poly_aux_lo (a b : UInt64) :
    ∀ (i : Nat) (_hi : i ≤ 64) (acc : BitVec (64 + 64)),
      clmul64.go a b i (UInt64.ofBitVec (BitVec.extractLsb' 0 64 acc)) =
        UInt64.ofBitVec (BitVec.extractLsb' 0 64
          (@DPSFP.polynomial_mult_aux 64 64 i acc b.toBitVec (BitVec.zeroExtend (64 + 64) a.toBitVec))) := by
  intro i hi
  induction hrem : 64 - i generalizing i with
  | zero =>
    have hi64 : i = 64 := by omega
    subst hi64
    intro acc
    unfold clmul64.go DPSFP.polynomial_mult_aux
    simp
  | succ rem ih =>
    have hlt : i < 64 := by omega
    intro acc
    unfold clmul64.go DPSFP.polynomial_mult_aux
    have hnge : ¬ (i ≥ 64) := by omega
    simp only [hlt, hnge, dite_true, dite_false]
    have hstep :
        (if ((b >>> i.toUInt64) &&& 1) == 1
         then UInt64.ofBitVec (BitVec.extractLsb' 0 64 acc) ^^^ (a <<< i.toUInt64)
         else UInt64.ofBitVec (BitVec.extractLsb' 0 64 acc)) =
        UInt64.ofBitVec (BitVec.extractLsb' 0 64
          (if lsb b.toBitVec i = 1#1
           then acc ^^^ (BitVec.zeroExtend (64 + 64) a.toBitVec <<< i)
           else acc)) := by
      rw [uint64_shift_test_eq_lsb b i hlt]
      by_cases hbit : lsb b.toBitVec i = 1#1
      · simp only [hbit, decide_true, ↓reduceIte]
        apply UInt64.eq_of_toBitVec_eq
        rw [UInt64.toBitVec_xor, UInt64.toBitVec_ofBitVec, UInt64.toBitVec_ofBitVec,
          uint64_shl_eq_extract_lo a i hlt, extractLsb'_0_64_xor]
      · simp [hbit]
    rw [hstep]
    exact ih (i + 1) (by omega) (by omega) _

private theorem clmul64Hi_go_eq_poly_aux_hi (a b : UInt64) :
    ∀ (i : Nat) (_hi0 : 1 ≤ i) (_hi : i ≤ 64) (acc : BitVec (64 + 64)),
      clmul64Hi.go a b i (UInt64.ofBitVec (BitVec.extractLsb' 64 64 acc)) =
        UInt64.ofBitVec (BitVec.extractLsb' 64 64
          (@DPSFP.polynomial_mult_aux 64 64 i acc b.toBitVec (BitVec.zeroExtend (64 + 64) a.toBitVec))) := by
  intro i hi0 hi
  induction hrem : 64 - i generalizing i with
  | zero =>
    have hi64 : i = 64 := by omega
    subst hi64
    intro acc
    unfold clmul64Hi.go DPSFP.polynomial_mult_aux
    simp
  | succ rem ih =>
    have hlt : i < 64 := by omega
    intro acc
    unfold clmul64Hi.go DPSFP.polynomial_mult_aux
    have hnge : ¬ (i ≥ 64) := by omega
    simp only [hlt, hnge, dite_true, dite_false]
    have hstep :
        (if ((b >>> i.toUInt64) &&& 1) == 1
         then UInt64.ofBitVec (BitVec.extractLsb' 64 64 acc) ^^^ (a >>> (64 - i.toUInt64))
         else UInt64.ofBitVec (BitVec.extractLsb' 64 64 acc)) =
        UInt64.ofBitVec (BitVec.extractLsb' 64 64
          (if lsb b.toBitVec i = 1#1
           then acc ^^^ (BitVec.zeroExtend (64 + 64) a.toBitVec <<< i)
           else acc)) := by
      rw [uint64_shift_test_eq_lsb b i hlt]
      by_cases hbit : lsb b.toBitVec i = 1#1
      · simp only [hbit, decide_true, ↓reduceIte]
        apply UInt64.eq_of_toBitVec_eq
        rw [UInt64.toBitVec_xor, UInt64.toBitVec_ofBitVec, UInt64.toBitVec_ofBitVec,
          uint64_shr_64_sub_eq_extract_hi a i hi0 hlt, extractLsb'_64_64_xor]
      · simp [hbit]
    rw [hstep]
    exact ih (i + 1) (by omega) (by omega) (by omega) _

/-- `clmul64 a b` equals the low 64 bits of `DPSFP.polynomial_mult b.toBitVec a.toBitVec`. -/
theorem clmul64_eq_polynomial_mult_lo (a b : UInt64) :
    (clmul64 a b).toBitVec =
      BitVec.extractLsb' 0 64 (DPSFP.polynomial_mult b.toBitVec a.toBitVec) := by
  have h0 : (0 : UInt64) = UInt64.ofBitVec (BitVec.extractLsb' 0 64 (0#(64 + 64))) := by decide
  have h := clmul64_go_eq_poly_aux_lo a b 0 (by omega) (0#(64 + 64))
  unfold clmul64 DPSFP.polynomial_mult
  rw [h0, h, UInt64.toBitVec_ofBitVec]

/-- `clmul64Hi a b` equals the high 64 bits of `DPSFP.polynomial_mult b.toBitVec a.toBitVec`. -/
theorem clmul64Hi_eq_polynomial_mult_hi (a b : UInt64) :
    (clmul64Hi a b).toBitVec =
      BitVec.extractLsb' 64 64 (DPSFP.polynomial_mult b.toBitVec a.toBitVec) := by
  unfold clmul64Hi DPSFP.polynomial_mult
  unfold DPSFP.polynomial_mult_aux
  simp only [show ¬(0 ≥ 64) by omega, dite_false, BitVec.shiftLeft_zero]
  let acc1 : BitVec (64 + 64) :=
    if lsb b.toBitVec 0 = 1#1 then 0#(64 + 64) ^^^ BitVec.zeroExtend (64 + 64) a.toBitVec else 0#(64 + 64)
  have hacc1_hi : BitVec.extractLsb' 64 64 acc1 = 0#64 := by
    dsimp [acc1]
    split
    · apply BitVec.eq_of_getLsbD_eq
      intro k hk
      rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_setWidth]
      have hlt : 64 + k < 64 + 64 := by omega
      simp [hk, hlt]
    · apply BitVec.eq_of_getLsbD_eq
      intro k hk
      simp [hk]
  have h0 : (0 : UInt64) = UInt64.ofBitVec (BitVec.extractLsb' 64 64 acc1) := by
    rw [hacc1_hi]; rfl
  have h := clmul64Hi_go_eq_poly_aux_hi a b 1 (by omega) (by omega) acc1
  change (clmul64Hi.go a b 1 0).toBitVec =
    BitVec.extractLsb' 64 64 (@DPSFP.polynomial_mult_aux 64 64 1 acc1 b.toBitVec (BitVec.zeroExtend (64 + 64) a.toBitVec))
  rw [h0, h, UInt64.toBitVec_ofBitVec]

/-- `qregToBv128 (QReg.pmull64 a b)` equals `DPSFP.polynomial_mult b.toBitVec a.toBitVec`. -/
theorem qregToBv128_pmull64_eq_polynomial_mult_swap (a b : UInt64) :
    qregToBv128 (LNSym.QReg.pmull64 a b) = DPSFP.polynomial_mult b.toBitVec a.toBitVec := by
  simp only [qregToBv128, LNSym.QReg.pmull64, clmul64_eq_polynomial_mult_lo,
    clmul64Hi_eq_polynomial_mult_hi]
  generalize DPSFP.polynomial_mult b.toBitVec a.toBitVec = p
  exact append_extractLsb'_64_64_0_64 p

theorem pmull_op_64_1_eq_polynomial_mult (x y : BitVec 64) :
    DPSFP.pmull_op 0 64 1 x y 0#128 = DPSFP.polynomial_mult x y := by
  unfold DPSFP.pmull_op
  simp (config := {ground := true}) only [minimal_theory]
  unfold DPSFP.pmull_op
  simp (config := {ground := true}) only [minimal_theory]
  simp only [state_simp_rules, bitvec_rules]

/-- Concrete 28-instruction AArch64 NEON machine-code program implementing
    `LNSym.butterflyStepInstrs idx` (`LDR Q1/Q2`, `PMULL`/`PMULL2`, `EXT`, `MOVI`, `EOR`, `STR Q1/Q2`):
    - `X0`: base pointer to `&sliceU[idx]` (16-byte `QReg`)
    - `X1`: base pointer to `&sliceV[idx]` (16-byte `QReg`)
    - `X2`: output pointer `&outU[0]` (16-byte `QReg`)
    - `X3`: output pointer `&outV[0]` (16-byte `QReg`)
    - `Q0`: twiddle factor `tw` -/
def gf128_butterfly_program : Program :=
  def_program
    [ (0x100000#64, 0x3dc00001#32), --  1: ldr q1, [x0]
      (0x100004#64, 0x3dc00022#32), --  2: ldr q2, [x1]
      (0x100008#64, 0x0ee2e003#32), --  3: pmull v3.1q, v0.1d, v2.1d
      (0x10000c#64, 0x6e004008#32), --  4: ext v8.16b, v0.16b, v0.16b, #8
      (0x100010#64, 0x0ee2e104#32), --  5: pmull v4.1q, v8.1d, v2.1d
      (0x100014#64, 0x4ee2e109#32), --  6: pmull2 v9.1q, v8.2d, v2.2d
      (0x100018#64, 0x6e291c84#32), --  7: eor v4.16b, v4.16b, v9.16b
      (0x10001c#64, 0x4ee2e005#32), --  8: pmull2 v5.1q, v0.2d, v2.2d
      (0x100020#64, 0x0f0404e7#32), --  9: movi v7.2s, #0x87
      (0x100024#64, 0x6f00e40a#32), -- 10: movi v10.2d, #0
      (0x100028#64, 0x6e0a20e7#32), -- 11: ext v7.16b, v7.16b, v10.16b, #4
      (0x10002c#64, 0x6e074148#32), -- 12: ext v8.16b, v10.16b, v7.16b, #8
      (0x100030#64, 0x6e281ce7#32), -- 13: eor v7.16b, v7.16b, v8.16b
      (0x100034#64, 0x6e044148#32), -- 14: ext v8.16b, v10.16b, v4.16b, #8
      (0x100038#64, 0x6e281c66#32), -- 15: eor v6.16b, v3.16b, v8.16b
      (0x10003c#64, 0x6e0a4089#32), -- 16: ext v9.16b, v4.16b, v10.16b, #8
      (0x100040#64, 0x6e291ca9#32), -- 17: eor v9.16b, v5.16b, v9.16b
      (0x100044#64, 0x0ee9e0e8#32), -- 18: pmull v8.1q, v7.1d, v9.1d
      (0x100048#64, 0x4ee9e0e9#32), -- 19: pmull2 v9.1q, v7.2d, v9.2d
      (0x10004c#64, 0x4ee9e0eb#32), -- 20: pmull2 v11.1q, v7.2d, v9.2d
      (0x100050#64, 0x6e094149#32), -- 21: ext v9.16b, v10.16b, v9.16b, #8
      (0x100054#64, 0x6e281cc6#32), -- 22: eor v6.16b, v6.16b, v8.16b
      (0x100058#64, 0x6e291cc6#32), -- 23: eor v6.16b, v6.16b, v9.16b
      (0x10005c#64, 0x6e2b1cc6#32), -- 24: eor v6.16b, v6.16b, v11.16b
      (0x100060#64, 0x6e261c21#32), -- 25: eor v1.16b, v1.16b, v6.16b
      (0x100064#64, 0x6e221c22#32), -- 26: eor v2.16b, v1.16b, v2.16b
      (0x100068#64, 0x3d800041#32), -- 27: str q1, [x2]
      (0x10006c#64, 0x3d800062#32)  -- 28: str q2, [x3]
    ]

#genStepEqTheorems gf128_butterfly_program

private theorem swap_lanes_ext8 (x : BitVec 128) :
    BitVec.extractLsb' 64 128 (x ++ x) =
      BitVec.extractLsb' 0 64 x ++ BitVec.extractLsb' 64 64 x := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and, BitVec.getLsbD_append]
  by_cases hk64 : k < 64
  · have h1' : 64 + k < 128 := by omega
    simp [hk64, h1']
  · have hge : ¬(64 + k < 128) := by omega
    have hlt2 : k - 64 < 64 := by omega
    have hsub : 64 + k - 128 = k - 64 := by omega
    simp [hk64, hge, hlt2, hsub]

private theorem hi_zero_shift_ext8 (x : BitVec 128) :
    BitVec.extractLsb' 64 128 (x ++ 0#128) =
      BitVec.extractLsb' 0 64 x ++ 0#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and, BitVec.getLsbD_append]
  by_cases hk64 : k < 64
  · have h1 : 64 + k < 128 := by omega
    simp [hk64, h1]
  · have hge : ¬(64 + k < 128) := by omega
    have hlt2 : k - 64 < 64 := by omega
    have hsub : 64 + k - 128 = k - 64 := by omega
    simp [hk64, hge, hlt2, hsub]

private theorem zero_lo_shift_ext8 (x : BitVec 128) :
    BitVec.extractLsb' 64 128 (0#128 ++ x) =
      0#64 ++ BitVec.extractLsb' 64 64 x := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and, BitVec.getLsbD_append]
  by_cases hk64 : k < 64
  · have h1 : 64 + k < 128 := by omega
    simp [hk64, h1]
  · have hge : ¬(64 + k < 128) := by omega
    have hsub : 64 + k - 128 = k - 64 := by omega
    simp [hk64, hge, hsub]

private theorem r2_arg_eq (twv_hi twv_ml twv_mh : BitVec 128) :
    BitVec.extractLsb' 0 64
      (twv_hi ^^^ (0#64 ++ BitVec.extractLsb' 64 64 (twv_ml ^^^ twv_mh))) =
    BitVec.extractLsb' 0 64 twv_hi ^^^
      (BitVec.extractLsb' 64 64 twv_ml ^^^ BitVec.extractLsb' 64 64 twv_mh) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_append,
    hk, decide_true, Bool.true_and, Nat.zero_add, ↓reduceIte]

private theorem r3_arg_eq (twv_hi twv_ml twv_mh : BitVec 128) :
    BitVec.extractLsb' 64 64
      (twv_hi ^^^ (0#64 ++ BitVec.extractLsb' 64 64 (twv_ml ^^^ twv_mh))) =
    BitVec.extractLsb' 64 64 twv_hi := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hge : ¬(64 + k < 64) := by omega
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_append,
    BitVec.getLsbD_zero, hk, hge, decide_true, Bool.true_and, ↓reduceIte, Bool.xor_false]

attribute [-state_simp_rules] read_mem_bytes_of_write_mem_bytes_same Memory.read_bytes_write_bytes_same

/-- Symbolic execution of all 28 AArch64 instructions of `gf128_butterfly_program` on upstream
    `ArmState`: proves error-free completion, PC advancement, twiddle-register preservation,
    and exact bit-level agreement of the two 16-byte output stores `(sf[X2, 16], sf[X3, 16])`
    with `LNSym.gf128ButterflyLane u v tw`. -/
theorem gf128_butterfly_program_run_28 (s0 sf : _root_.ArmState)
    (u v tw : LNSym.QReg)
    (h_s0_prog : s0.program = gf128_butterfly_program)
    (h_s0_err : read_err s0 = .None)
    (h_s0_pc : read_pc s0 = 0x100000#64)
    (h_tw : read_sfp 128 0#5 s0 = qregToBv128 tw)
    (h_u : read_mem_bytes 16 (read_gpr 64 0#5 s0) s0 = qregToBv128 u)
    (h_v : read_mem_bytes 16 (read_gpr 64 1#5 s0) s0 = qregToBv128 v)
    (h_mem_sep : Memory.Region.pairwiseSeparate
      [ (read_gpr 64 0#5 s0, 16),
        (read_gpr 64 1#5 s0, 16),
        (read_gpr 64 2#5 s0, 16),
        (read_gpr 64 3#5 s0, 16) ])
    (h_run : sf = run 28 s0) :
    read_err sf = .None ∧
    read_pc sf = 0x100070#64 ∧
    read_sfp 128 0#5 sf = qregToBv128 tw ∧
    read_mem_bytes 16 (read_gpr 64 2#5 s0) sf = qregToBv128 (LNSym.gf128ButterflyLane u v tw).1 ∧
    read_mem_bytes 16 (read_gpr 64 3#5 s0) sf = qregToBv128 (LNSym.gf128ButterflyLane u v tw).2 := by
  simp_all only [state_simp_rules, -h_run]
  sym_n 28
  simp only [Memory.State.read_mem_bytes_eq_mem_read_bytes,
    Memory.write_mem_bytes_eq_mem_write_bytes] at *
  sym_aggregate
  clear_named [h_s, stepi_]
  clear s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 s25 s26 s27
  clear h_run
  have h135 : (0x87 : UInt64).toBitVec = 135#64 := rfl
  let poly128 (x y : BitVec 64) : BitVec 128 := DPSFP.polynomial_mult x y
  have pmull_128 : ∀ (x y : BitVec 64),
      DPSFP.pmull_op 0 64 1 x y 0#128 = poly128 x y := pmull_op_64_1_eq_polynomial_mult
  have clmul_lo_128 : ∀ (a b : UInt64),
      (clmul64 a b).toBitVec = BitVec.extractLsb' 0 64 (poly128 b.toBitVec a.toBitVec) :=
    clmul64_eq_polynomial_mult_lo
  have clmul_hi_128 : ∀ (a b : UInt64),
      (clmul64Hi a b).toBitVec = BitVec.extractLsb' 64 64 (poly128 b.toBitVec a.toBitVec) :=
    clmul64Hi_eq_polynomial_mult_hi
  have hsep23 : mem_separate' (r (StateField.GPR 2#5) s0) 16 (r (StateField.GPR 3#5) s0) 16 :=
    h_mem_sep.get 2 3
  have hsub2 : mem_subset' (r (StateField.GPR 2#5) s0) 16 (r (StateField.GPR 2#5) s0) 16 :=
    mem_subset'_refl hsep23.ha
  have hsub3 : mem_subset' (r (StateField.GPR 3#5) s0) 16 (r (StateField.GPR 3#5) s0) 16 :=
    mem_subset'_refl hsep23.hb
  constructor
  · rw [Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate' hsep23,
      Memory.read_bytes_write_bytes_eq_of_mem_subset' hsub2,
      Nat.sub_self, BitVec.extractLsBytes_eq_self, BitVec.cast_eq]
    clear h_mem_sep hsep23 hsub2 hsub3
    rcases u with ⟨ulo, uhi⟩
    rcases v with ⟨vlo, vhi⟩
    rcases tw with ⟨twlo, twhi⟩
    simp only [qregToBv128, LNSym.gf128ButterflyLane,
      LNSym.QReg.mulGF128, LNSym.QReg.pmull64, LNSym.QReg.reduceGF128, LNSym.QReg.xor,
      pmull_128, clmul_lo_128, clmul_hi_128, UInt64.toBitVec_xor, h135,
      swap_lanes_ext8, hi_zero_shift_ext8, zero_lo_shift_ext8,
      extractLsb'_64_64_append, extractLsb'_0_64_append,
      r2_arg_eq, r3_arg_eq]
    generalize poly128 twlo.toBitVec vlo.toBitVec = twv_lo
    generalize poly128 twhi.toBitVec vlo.toBitVec = twv_ml
    generalize poly128 twlo.toBitVec vhi.toBitVec = twv_mh
    generalize poly128 twhi.toBitVec vhi.toBitVec = twv_hi
    generalize poly128 (135#64)
      (BitVec.extractLsb' 0 64 twv_hi ^^^
        (BitVec.extractLsb' 64 64 twv_ml ^^^ BitVec.extractLsb' 64 64 twv_mh)) = red2
    generalize poly128 (135#64) (BitVec.extractLsb' 64 64 twv_hi) = red3
    generalize poly128 (135#64) (BitVec.extractLsb' 64 64 red3) = fold
    apply BitVec.eq_of_getLsbD_eq
    intro k _hk
    by_cases hk64 : k < 64
    · simp only [BitVec.getLsbD_xor, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
        BitVec.getLsbD_zero, hk64, decide_true, Bool.true_and, Nat.zero_add, ↓reduceIte,
        Bool.xor_false]
    · have hsublt : k - 64 < 64 := by omega
      have h64sub : 64 + (k - 64) = k := by omega
      simp only [BitVec.getLsbD_xor, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
        hk64, hsublt, h64sub, decide_true, Bool.true_and, Nat.zero_add, ↓reduceIte]
  · rw [Memory.read_bytes_write_bytes_eq_of_mem_subset' hsub3,
      Nat.sub_self, BitVec.extractLsBytes_eq_self, BitVec.cast_eq]
    clear h_mem_sep hsep23 hsub2 hsub3
    rcases u with ⟨ulo, uhi⟩
    rcases v with ⟨vlo, vhi⟩
    rcases tw with ⟨twlo, twhi⟩
    simp only [qregToBv128, LNSym.gf128ButterflyLane,
      LNSym.QReg.mulGF128, LNSym.QReg.pmull64, LNSym.QReg.reduceGF128, LNSym.QReg.xor,
      pmull_128, clmul_lo_128, clmul_hi_128, UInt64.toBitVec_xor, h135,
      swap_lanes_ext8, hi_zero_shift_ext8, zero_lo_shift_ext8,
      extractLsb'_64_64_append, extractLsb'_0_64_append,
      r2_arg_eq, r3_arg_eq]
    generalize poly128 twlo.toBitVec vlo.toBitVec = twv_lo
    generalize poly128 twhi.toBitVec vlo.toBitVec = twv_ml
    generalize poly128 twlo.toBitVec vhi.toBitVec = twv_mh
    generalize poly128 twhi.toBitVec vhi.toBitVec = twv_hi
    generalize poly128 (135#64)
      (BitVec.extractLsb' 0 64 twv_hi ^^^
        (BitVec.extractLsb' 64 64 twv_ml ^^^ BitVec.extractLsb' 64 64 twv_mh)) = red2
    generalize poly128 (135#64) (BitVec.extractLsb' 64 64 twv_hi) = red3
    generalize poly128 (135#64) (BitVec.extractLsb' 64 64 red3) = fold
    apply BitVec.eq_of_getLsbD_eq
    intro k _hk
    by_cases hk64 : k < 64
    · simp only [BitVec.getLsbD_xor, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
        BitVec.getLsbD_zero, hk64, decide_true, Bool.true_and, Nat.zero_add, ↓reduceIte,
        Bool.xor_false]
    · have hsublt : k - 64 < 64 := by omega
      have h64sub : 64 + (k - 64) = k := by omega
      simp only [BitVec.getLsbD_xor, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
        hk64, hsublt, h64sub, decide_true, Bool.true_and, Nat.zero_add, ↓reduceIte]

/-- State correspondence between an abstract `LNSym.ArmState` (with empty `outU`/`outV` accumulators
    prior to step `idx`) and an upstream `leanprover/LNSym` AArch64 `ArmState` whose `X0..X3`
    registers address `&sliceU[idx]`, `&sliceV[idx]`, `&outU[0]`, `&outV[0]`. -/
def Arm64StepStateCorresponds (idx : Nat) (ms : LNSym.ArmState) (as0 : _root_.ArmState) : Prop :=
  ms.validABI = true ∧
  ms.outU = [] ∧
  ms.outV = [] ∧
  as0.program = gf128_butterfly_program ∧
  read_err as0 = .None ∧
  read_pc as0 = 0x100000#64 ∧
  read_sfp 128 0#5 as0 = qregToBv128 (ms.readQ 0) ∧
  read_mem_bytes 16 (read_gpr 64 0#5 as0) as0 = qregToBv128 (ms.sliceU[idx]?.getD LNSym.QReg.zero) ∧
  read_mem_bytes 16 (read_gpr 64 1#5 as0) as0 = qregToBv128 (ms.sliceV[idx]?.getD LNSym.QReg.zero) ∧
  Memory.Region.pairwiseSeparate
    [ (read_gpr 64 0#5 as0, 16),
      (read_gpr 64 1#5 as0, 16),
      (read_gpr 64 2#5 as0, 16),
      (read_gpr 64 3#5 as0, 16) ]

/-- End-to-end formal bisimulation between `LeanNative`'s mirrored `LNSym.runArm64 (butterflyStepInstrs idx)`
    model (which drives `arm64_f128_kernel_refines_lnir` in `BackendProofs.lean`) and 28-instruction
    machine-code execution `run 28 as0` in upstream `leanprover/LNSym`. -/
theorem runArm64_butterflyStepInstrs_bisim_lnsym (idx : Nat) (ms : LNSym.ArmState) (as0 : _root_.ArmState)
    (h_corr : Arm64StepStateCorresponds idx ms as0) :
    let asf := run 28 as0
    let (outU, outV) := LNSym.extractSlice (LNSym.runArm64 (LNSym.butterflyStepInstrs idx) ms)
    read_err asf = .None ∧
    read_pc asf = 0x100070#64 ∧
    read_sfp 128 0#5 asf = qregToBv128 (ms.readQ 0) ∧
    outU = [bv128ToQReg (read_mem_bytes 16 (read_gpr 64 2#5 as0) asf)] ∧
    outV = [bv128ToQReg (read_mem_bytes 16 (read_gpr 64 3#5 as0) asf)] := by
  rcases h_corr with ⟨h_valid, h_outU, h_outV, h_prog, h_err, h_pc, h_tw, h_u, h_v, h_sep⟩
  have h_sim := gf128_butterfly_program_run_28 as0 (run 28 as0)
    (ms.sliceU[idx]?.getD LNSym.QReg.zero)
    (ms.sliceV[idx]?.getD LNSym.QReg.zero)
    (ms.readQ 0)
    h_prog h_err h_pc h_tw h_u h_v h_sep rfl
  rcases h_sim with ⟨herr', hpc', htw', hu', hv'⟩
  have h_model :
      LNSym.extractSlice (LNSym.runArm64 (LNSym.butterflyStepInstrs idx) ms) =
        ([ (LNSym.gf128ButterflyLane (ms.sliceU[idx]?.getD LNSym.QReg.zero)
              (ms.sliceV[idx]?.getD LNSym.QReg.zero) (ms.readQ 0)).1 ],
         [ (LNSym.gf128ButterflyLane (ms.sliceU[idx]?.getD LNSym.QReg.zero)
              (ms.sliceV[idx]?.getD LNSym.QReg.zero) (ms.readQ 0)).2 ]) := by
    dsimp [LNSym.butterflyStepInstrs, LNSym.runArm64, LNSym.execInstr,
      LNSym.ArmState.readQ, LNSym.ArmState.writeQ, LNSym.extractSlice,
      LNSym.gf128ButterflyLane, LNSym.QReg.mulGF128]
    simp [h_valid, h_outU, h_outV]
  rw [h_model]
  refine ⟨herr', hpc', htw', ?_, ?_⟩
  · rw [hu', bv128ToQReg_qregToBv128]
  · rw [hv', bv128ToQReg_qregToBv128]

/-- Direct single-instruction bisimulation for `exec_pmull` (`Q = 0#1`, `PMULL Vd.1Q, Vn.1D, Vm.1D`)
    against `LNSym.execInstr (.pmullLow rd rm rn)`. -/
theorem exec_pmull_low_bisim (ms : LNSym.ArmState) (as0 : _root_.ArmState)
    (rd rn rm : BitVec 5)
    (h_valid : ms.validABI = true)
    (h_rn : read_sfp 128 rn as0 = qregToBv128 (ms.readQ rn.toNat))
    (h_rm : read_sfp 128 rm as0 = qregToBv128 (ms.readQ rm.toNat)) :
    let inst : Advanced_simd_three_different_cls :=
      { Q := 0#1, U := 0#1, size := 0b11#2, Rm := rm, opcode := 0b1110#4, Rn := rn, Rd := rd }
    let asf := DPSFP.exec_advanced_simd_three_different inst as0
    let msf := LNSym.execInstr (.pmullLow rd.toNat rm.toNat rn.toNat) ms
    read_sfp 128 rd asf = qregToBv128 (msf.readQ rd.toNat) := by
  dsimp [LNSym.execInstr, LNSym.ArmState.writeQ]
  rw [h_valid]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, LNSym.ArmState.readQ, beq_self_eq_true]
  simp only [state_simp_rules, bitvec_rules, minimal_theory] at h_rn h_rm ⊢
  change DPSFP.pmull_op 0 64 1 (BitVec.extractLsb' 0 64 (r (StateField.SFP rn) as0))
      (BitVec.extractLsb' 0 64 (r (StateField.SFP rm) as0)) 0#128 =
    qregToBv128 (LNSym.QReg.pmull64 (ms.qregs rm.toNat).lo (ms.qregs rn.toNat).lo)
  rw [pmull_op_64_1_eq_polynomial_mult, h_rn, h_rm, qregToBv128_pmull64_eq_polynomial_mult_swap]
  congr 1 <;> simp [qregToBv128, LNSym.ArmState.readQ, extractLsb'_0_64_append]

/-- Direct single-instruction bisimulation for `exec_pmull` (`Q = 1#1`, `PMULL2 Vd.1Q, Vn.2D, Vm.2D`)
    against `LNSym.execInstr (.pmullHigh rd rm rn)`. -/
theorem exec_pmull_high_bisim (ms : LNSym.ArmState) (as0 : _root_.ArmState)
    (rd rn rm : BitVec 5)
    (h_valid : ms.validABI = true)
    (h_rn : read_sfp 128 rn as0 = qregToBv128 (ms.readQ rn.toNat))
    (h_rm : read_sfp 128 rm as0 = qregToBv128 (ms.readQ rm.toNat)) :
    let inst : Advanced_simd_three_different_cls :=
      { Q := 1#1, U := 0#1, size := 0b11#2, Rm := rm, opcode := 0b1110#4, Rn := rn, Rd := rd }
    let asf := DPSFP.exec_advanced_simd_three_different inst as0
    let msf := LNSym.execInstr (.pmullHigh rd.toNat rm.toNat rn.toNat) ms
    read_sfp 128 rd asf = qregToBv128 (msf.readQ rd.toNat) := by
  dsimp [LNSym.execInstr, LNSym.ArmState.writeQ]
  rw [h_valid]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, LNSym.ArmState.readQ, beq_self_eq_true]
  simp only [state_simp_rules, bitvec_rules, minimal_theory] at h_rn h_rm ⊢
  change DPSFP.pmull_op 0 64 1 (BitVec.extractLsb' 64 64 (r (StateField.SFP rn) as0))
      (BitVec.extractLsb' 64 64 (r (StateField.SFP rm) as0)) 0#128 =
    qregToBv128 (LNSym.QReg.pmull64 (ms.qregs rm.toNat).hi (ms.qregs rn.toNat).hi)
  rw [pmull_op_64_1_eq_polynomial_mult, h_rn, h_rm, qregToBv128_pmull64_eq_polynomial_mult_swap]
  congr 1 <;> simp [qregToBv128, LNSym.ArmState.readQ, extractLsb'_64_64_append]

/-- Direct single-instruction bisimulation for `EOR Vd.16B, Vn.16B, Vm.16B`
    against `LNSym.execInstr (.veor128 rd rn rm)`. -/
theorem exec_eor_16b_bisim (ms : LNSym.ArmState) (as0 : _root_.ArmState)
    (rd rn rm : BitVec 5)
    (h_valid : ms.validABI = true)
    (h_rn : read_sfp 128 rn as0 = qregToBv128 (ms.readQ rn.toNat))
    (h_rm : read_sfp 128 rm as0 = qregToBv128 (ms.readQ rm.toNat)) :
    let inst : Advanced_simd_three_same_cls :=
      { Q := 1#1, U := 1#1, size := 0b00#2, Rm := rm, opcode := 0b00011#5, Rn := rn, Rd := rd }
    let asf := DPSFP.exec_advanced_simd_three_same inst as0
    let msf := LNSym.execInstr (.veor128 rd.toNat rn.toNat rm.toNat) ms
    read_sfp 128 rd asf = qregToBv128 (msf.readQ rd.toNat) := by
  dsimp [LNSym.execInstr, LNSym.ArmState.writeQ]
  rw [h_valid]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, LNSym.ArmState.readQ, beq_self_eq_true]
  simp only [state_simp_rules, bitvec_rules, minimal_theory] at h_rn h_rm ⊢
  rw [qregToBv128_xor, h_rn, h_rm]
  rfl

end LNSymBridge
