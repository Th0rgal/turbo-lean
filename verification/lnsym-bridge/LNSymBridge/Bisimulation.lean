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

/-! ## Stage 3D.2: $\mathbb{F}_{2^{128}}$ Modular Reduction Soundness, Ring Laws & Loop Bisimulation -/

private theorem bv_zero_getLsbD (w j : Nat) : (0#w).getLsbD j = false := by
  by_cases hj : j < w
  · simp [hj]
  · exact BitVec.getLsbD_of_ge 0#w j (by omega)

private theorem bv128_xor_zero (x : BitVec 128) : x ^^^ 0#128 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro k _; simp

private theorem bv128_zero_xor (x : BitVec 128) : 0#128 ^^^ x = x := by
  apply BitVec.eq_of_getLsbD_eq; intro k _; simp

private theorem bv128_xor_comm (x y : BitVec 128) : x ^^^ y = y ^^^ x := by
  apply BitVec.eq_of_getLsbD_eq; intro k _; simp [Bool.xor_comm]

private theorem bv128_xor_assoc (x y z : BitVec 128) : (x ^^^ y) ^^^ z = x ^^^ (y ^^^ z) := by
  apply BitVec.eq_of_getLsbD_eq; intro k _; simp

private theorem bv128_xor_self (x : BitVec 128) : x ^^^ x = 0#128 := by
  apply BitVec.eq_of_getLsbD_eq; intro k _; simp

private theorem zero128_append_zero128 : (0#128 : BitVec 128) ++ 0#128 = 0#256 := by
  apply BitVec.eq_of_getLsbD_eq; intro k _; rw [BitVec.getLsbD_append]; simp

private theorem zero64_append_zero64 : (0#64 : BitVec 64) ++ 0#64 = 0#128 := by
  apply BitVec.eq_of_getLsbD_eq; intro k _; rw [BitVec.getLsbD_append]; simp

private theorem zero64_64_append_zero128 : ((0#64 : BitVec 64) ++ 0#64) ++ 0#128 = 0#256 := by
  rw [zero64_append_zero64, zero128_append_zero128]

private theorem cond_true_eq {α : Type _} (x y : α) :
    (if true = true then x else y) = x := rfl

private theorem cond_false_eq {α : Type _} (x y : α) :
    (if false = true then x else y) = y := rfl

private theorem ite_xor_mask {w : Nat} (b1 b2 : Bool) (c : BitVec w) :
    (if xor b1 b2 then c else 0#w) =
      (if b1 then c else 0#w) ^^^ (if b2 then c else 0#w) := by
  cases b1 <;> cases b2 <;> apply BitVec.eq_of_getLsbD_eq <;> intro k _ <;> simp

private def gf2PrefixFold : (n : Nat) → (Nat → Bool) → Bool
  | 0, _ => false
  | n + 1, p => xor (gf2PrefixFold n p) (p n)

private theorem gf2PrefixFold_congr {n : Nat} {p q : Nat → Bool}
    (h : ∀ i, i < n → p i = q i) :
    gf2PrefixFold n p = gf2PrefixFold n q := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [gf2PrefixFold]
    rw [ih (fun i hi => h i (by omega)), h m (by omega)]

private theorem gf2PrefixFold_split (n m : Nat) (p : Nat → Bool)
    (hzero : ∀ i, m ≤ i → i < n → p i = false) (hmn : m ≤ n) :
    gf2PrefixFold n p = gf2PrefixFold m p := by
  induction n with
  | zero =>
    have hm0 : m = 0 := by omega
    subst hm0; rfl
  | succ k ih =>
    by_cases hmk : m = k + 1
    · subst hmk; rfl
    · have hle : m ≤ k := by omega
      simp only [gf2PrefixFold, hzero k hle (by omega), Bool.bne_false]
      exact ih (fun i hmi hik => hzero i hmi (by omega)) hle

private theorem gf2PrefixFold_add (a b : Nat) (p : Nat → Bool) :
    gf2PrefixFold (a + b) p =
      xor (gf2PrefixFold a p) (gf2PrefixFold b (fun j => p (a + j))) := by
  induction b with
  | zero => simp [gf2PrefixFold]
  | succ k ih =>
    rw [Nat.add_succ, gf2PrefixFold, ih, gf2PrefixFold, Bool.xor_assoc]

private theorem gf2PrefixFold_shift (k : Nat) (q : Nat → Bool) :
    xor (q 0) (gf2PrefixFold k (fun j => q (j + 1))) = gf2PrefixFold (k + 1) q := by
  induction k with
  | zero => simp [gf2PrefixFold]
  | succ l ihl =>
    rw [gf2PrefixFold, ← Bool.xor_assoc, ihl, ← gf2PrefixFold]

private theorem gf2PrefixFold_rev (m : Nat) (p : Nat → Bool) :
    gf2PrefixFold m p = gf2PrefixFold m (fun j => p (m - 1 - j)) := by
  induction m with
  | zero => rfl
  | succ n ih =>
    rw [gf2PrefixFold, ih]
    have hrhs : gf2PrefixFold (n + 1) (fun j => p (n + 1 - 1 - j)) =
        gf2PrefixFold (n + 1) (fun j => p (n - j)) := rfl
    rw [hrhs, ← gf2PrefixFold_shift n (fun j => p (n - j))]
    have h0 : n - 0 = n := by omega
    have htail : gf2PrefixFold n (fun j => p (n - 1 - j)) =
        gf2PrefixFold n (fun j => p (n - (j + 1))) :=
      gf2PrefixFold_congr (fun j _ => by congr 1; omega)
    rw [h0, htail, Bool.xor_comm]

private theorem gf2PrefixFold_zero (n : Nat) :
    gf2PrefixFold n (fun _ => false) = false := by
  induction n with
  | zero => rfl
  | succ k ih => simp [gf2PrefixFold, ih]

private theorem gf2PrefixFold_xor (n : Nat) (p q : Nat → Bool) :
    gf2PrefixFold n (fun i => xor (p i) (q i)) =
      xor (gf2PrefixFold n p) (gf2PrefixFold n q) := by
  induction n with
  | zero => simp [gf2PrefixFold]
  | succ k ih =>
    simp only [gf2PrefixFold, ih]
    cases gf2PrefixFold k p <;> cases gf2PrefixFold k q <;> cases p k <;> cases q k <;> rfl

private theorem lsb_eq_one_iff_getLsbD {w : Nat} (x : BitVec w) (i : Nat) :
    (lsb x i = 1#1) ↔ x.getLsbD i = true := by
  unfold lsb
  constructor
  · intro h
    have h0 := congrArg (fun v => v.getLsbD 0) h
    simpa [BitVec.getLsbD_extractLsb'] using h0
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simpa [BitVec.getLsbD_extractLsb'] using h

private theorem polynomial_mult_aux_getLsbD {m n : Nat} (op1 : BitVec m) (op2 : BitVec (m + n))
    (k : Nat) (hk : k < m + n) :
    ∀ (i : Nat) (_hi : i ≤ m) (acc : BitVec (m + n)),
      (@DPSFP.polynomial_mult_aux m n i acc op1 op2).getLsbD k =
        xor (acc.getLsbD k)
          (gf2PrefixFold (m - i) (fun d =>
            op1.getLsbD (i + d) && (!decide (k < i + d) && op2.getLsbD (k - (i + d))))) := by
  intro i hi
  induction hrem : m - i generalizing i with
  | zero =>
    have him : i = m := by omega
    subst him
    intro acc
    unfold DPSFP.polynomial_mult_aux
    simp [gf2PrefixFold]
  | succ rem ih =>
    have hlt : i < m := by omega
    have hnge : ¬(i ≥ m) := by omega
    intro acc
    unfold DPSFP.polynomial_mult_aux
    simp only [hnge, dite_false]
    change (@DPSFP.polynomial_mult_aux m n (i + 1)
      (if lsb op1 i = 1#1 then acc ^^^ (op2 <<< i) else acc) op1 op2).getLsbD k = _
    rw [ih (i + 1) (by omega) (by omega)]
    have hterm :
        (if lsb op1 i = 1#1 then acc ^^^ (op2 <<< i) else acc).getLsbD k =
          xor (acc.getLsbD k) (op1.getLsbD i && (!decide (k < i) && op2.getLsbD (k - i))) := by
      by_cases hbit : lsb op1 i = 1#1
      · have hb : op1.getLsbD i = true := (lsb_eq_one_iff_getLsbD op1 i).mp hbit
        simp only [hbit, ↓reduceIte, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft,
          hk, decide_true, Bool.true_and, hb]
      · have hb : op1.getLsbD i = false := by
          cases hgb : op1.getLsbD i with
          | false => rfl
          | true => exact False.elim (hbit ((lsb_eq_one_iff_getLsbD op1 i).mpr hgb))
        simp [hbit, hb]
    rw [hterm, Bool.xor_assoc]
    congr 1
    have hcong : gf2PrefixFold rem (fun d =>
        op1.getLsbD (i + 1 + d) && (!decide (k < i + 1 + d) && op2.getLsbD (k - (i + 1 + d)))) =
      gf2PrefixFold rem (fun d =>
        op1.getLsbD (i + (d + 1)) && (!decide (k < i + (d + 1)) && op2.getLsbD (k - (i + (d + 1))))) :=
      gf2PrefixFold_congr (fun d _ => by
        have h1 : i + 1 + d = i + (d + 1) := by omega
        rw [h1])
    rw [hcong]
    simpa [Nat.add_zero] using
      gf2PrefixFold_shift rem (fun d =>
        op1.getLsbD (i + d) && (!decide (k < i + d) && op2.getLsbD (k - (i + d))))

private theorem polynomial_mult_getLsbD {n : Nat} (x y : BitVec n) (k : Nat) (hk : k < n + n) :
    (DPSFP.polynomial_mult x y).getLsbD k =
      gf2PrefixFold (k + 1) (fun i => x.getLsbD i && y.getLsbD (k - i)) := by
  unfold DPSFP.polynomial_mult
  rw [polynomial_mult_aux_getLsbD x (BitVec.zeroExtend (n + n) y) k hk 0 (by omega) 0#(n + n)]
  simp only [Nat.sub_zero, Nat.zero_add, BitVec.getLsbD_zero, Bool.false_bne]
  by_cases hkn : k + 1 ≤ n
  · rw [gf2PrefixFold_split n (k + 1) _ (fun i hik _ => by
      have hlt : k < i := by omega
      simp [hlt]) hkn]
    exact gf2PrefixFold_congr (fun i _ => by
      have hnlt : ¬(k < i) := by omega
      have hlt : k - i < n + n := by omega
      simp [hnlt, hlt])
  · symm
    rw [gf2PrefixFold_split (k + 1) n _ (fun i hin _ => by
      rw [BitVec.getLsbD_of_ge x i hin]; simp) (by omega)]
    symm
    exact gf2PrefixFold_congr (fun i _ => by
      have hnlt : ¬(k < i) := by omega
      have hlt : k - i < n + n := by omega
      simp [hnlt, hlt])

theorem polynomial_mult_comm {n : Nat} (x y : BitVec n) :
    DPSFP.polynomial_mult x y = DPSFP.polynomial_mult y x := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [polynomial_mult_getLsbD x y k hk, polynomial_mult_getLsbD y x k hk, gf2PrefixFold_rev (k + 1)]
  exact gf2PrefixFold_congr (fun j _ => by
    have h1 : k + 1 - 1 - j = k - j := by omega
    have h2 : k - (k - j) = j := by omega
    rw [h1, h2, Bool.and_comm])

theorem polynomial_mult_xor_left {n : Nat} (x y z : BitVec n) :
    DPSFP.polynomial_mult (x ^^^ y) z =
      DPSFP.polynomial_mult x z ^^^ DPSFP.polynomial_mult y z := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_xor, polynomial_mult_getLsbD (x ^^^ y) z k hk,
    polynomial_mult_getLsbD x z k hk, polynomial_mult_getLsbD y z k hk,
    ← gf2PrefixFold_xor]
  exact gf2PrefixFold_congr (fun i _ => by
    rw [BitVec.getLsbD_xor]
    cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD (k - i) <;> rfl)

theorem polynomial_mult_xor_right {n : Nat} (x y z : BitVec n) :
    DPSFP.polynomial_mult x (y ^^^ z) =
      DPSFP.polynomial_mult x y ^^^ DPSFP.polynomial_mult x z := by
  rw [polynomial_mult_comm x (y ^^^ z), polynomial_mult_xor_left,
    polynomial_mult_comm y x, polynomial_mult_comm z x]

private theorem polynomial_mult_zero_left {n : Nat} (x : BitVec n) :
    DPSFP.polynomial_mult 0#n x = 0#(n + n) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [polynomial_mult_getLsbD 0#n x k hk]
  simp only [BitVec.getLsbD_zero, Bool.false_and, gf2PrefixFold_zero]

private theorem polynomial_mult_zero_right {n : Nat} (x : BitVec n) :
    DPSFP.polynomial_mult x 0#n = 0#(n + n) := by
  rw [polynomial_mult_comm, polynomial_mult_zero_left]

theorem clmul64_comm (a b : UInt64) : clmul64 a b = clmul64 b a := by
  apply UInt64.eq_of_toBitVec_eq
  rw [clmul64_eq_polynomial_mult_lo, clmul64_eq_polynomial_mult_lo, polynomial_mult_comm]

theorem clmul64Hi_comm (a b : UInt64) : clmul64Hi a b = clmul64Hi b a := by
  apply UInt64.eq_of_toBitVec_eq
  rw [clmul64Hi_eq_polynomial_mult_hi, clmul64Hi_eq_polynomial_mult_hi, polynomial_mult_comm]

private theorem one_shl_getLsbD {w : Nat} (p j : Nat) (hp : p < w) (hj : j < w) :
    (1#w <<< p).getLsbD j = decide (j = p) := by
  rw [BitVec.getLsbD_shiftLeft]
  by_cases hjp : j < p
  · have hne : j ≠ p := by omega
    simp [hj, hjp, hne]
  · cases hsub : j - p with
    | zero =>
      have heq : j = p := by omega
      subst heq
      simp [hj, hjp, show 0 < w by omega]
    | succ s =>
      have hne : j ≠ p := by omega
      have h1 : (1#w).getLsbD (s + 1) = false := by
        rw [BitVec.getLsbD_ofNat]
        simp [show s + 1 < w by omega, Nat.testBit_succ]
      simp [hj, hjp, hne, h1]

private def bitPrefixSum {w : Nat} (x : BitVec w) : Nat → BitVec w
  | 0 => 0#w
  | m + 1 => bitPrefixSum x m ^^^ (if x.getLsbD m then 1#w <<< m else 0#w)

private theorem bitPrefixSum_getLsbD {w : Nat} (x : BitVec w) (m j : Nat) (hm : m ≤ w) (hj : j < w) :
    (bitPrefixSum x m).getLsbD j = (decide (j < m) && x.getLsbD j) := by
  induction m with
  | zero => simp [bitPrefixSum]
  | succ k ih =>
    rw [bitPrefixSum, BitVec.getLsbD_xor, ih (by omega)]
    by_cases hjk : j = k
    · subst hjk
      have hlt1 : j < j + 1 := by omega
      have hnlt : ¬(j < j) := by omega
      cases x.getLsbD j <;> simp [hlt1, hnlt, one_shl_getLsbD j j hj hj]
    · have hiff : decide (j < k + 1) = decide (j < k) := by
        apply Bool.eq_iff_iff.mpr; simp; omega
      rw [hiff]
      cases x.getLsbD k
      · simp
      · simp [one_shl_getLsbD k j (by omega) hj, hjk]

private theorem bitPrefixSum_full {w : Nat} (x : BitVec w) :
    bitPrefixSum x w = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [bitPrefixSum_getLsbD x w j (by omega) hj]
  simp [hj]

private theorem polynomial_mult_one_shl_right {n : Nat} (a : BitVec n) (i : Nat) (hi : i < n) :
    DPSFP.polynomial_mult a (1#n <<< i) = BitVec.zeroExtend (n + n) a <<< i := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [polynomial_mult_getLsbD a (1#n <<< i) k hk, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases hki : k < i
  · simp only [hk, decide_true, Bool.true_and, hki, Bool.not_true, Bool.false_and]
    rw [gf2PrefixFold_congr (q := fun _ => false) (fun j _ => by
      have hlt : k - j < n := by omega
      rw [one_shl_getLsbD i (k - j) hi hlt]
      simp [show k - j ≠ i by omega]), gf2PrefixFold_zero]
  · have hsublt : k - i < n + n := by omega
    simp only [hk, decide_true, Bool.true_and, hki, hsublt]
    have hsplit1 : k + 1 = (k - i) + (i + 1) := by omega
    rw [hsplit1, gf2PrefixFold_add (k - i) (i + 1)]
    have hpre : gf2PrefixFold (k - i) (fun d => a.getLsbD d && (1#n <<< i).getLsbD (k - d)) = false := by
      rw [gf2PrefixFold_congr (q := fun _ => false) (fun d _ => by
        by_cases hkd : k - d < n
        · rw [one_shl_getLsbD i (k - d) hi hkd]
          simp [show k - d ≠ i by omega]
        · rw [BitVec.getLsbD_of_ge (1#n <<< i) (k - d) (by omega)]
          simp), gf2PrefixFold_zero]
    rw [hpre, Bool.false_xor, ← gf2PrefixFold_shift i]
    have htail : gf2PrefixFold i (fun j => a.getLsbD (k - i + (j + 1)) && (1#n <<< i).getLsbD (k - (k - i + (j + 1)))) = false := by
      rw [gf2PrefixFold_congr (q := fun _ => false) (fun j _ => by
        have hlt : k - (k - i + (j + 1)) < n := by omega
        rw [one_shl_getLsbD i (k - (k - i + (j + 1))) hi hlt]
        simp [show k - (k - i + (j + 1)) ≠ i by omega]), gf2PrefixFold_zero]
    rw [htail, Bool.xor_false, Nat.add_zero]
    have hmid : k - (k - i) = i := by omega
    rw [hmid, one_shl_getLsbD i i hi hi]
    simp

private theorem polynomial_mult_lo_lo (a0 b0 : BitVec 64) :
    DPSFP.polynomial_mult (0#64 ++ a0) (0#64 ++ b0) =
      0#128 ++ DPSFP.polynomial_mult a0 b0 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [polynomial_mult_getLsbD (0#64 ++ a0) (0#64 ++ b0) k hk, BitVec.getLsbD_append]
  by_cases hk128 : k < 128
  · rw [polynomial_mult_getLsbD a0 b0 k hk128]
    simp only [hk128, ↓reduceIte]
    exact gf2PrefixFold_congr (fun i _ => by
      rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
      by_cases hi64 : i < 64
      · by_cases hki64 : k - i < 64
        · simp [hi64, hki64]
        · rw [BitVec.getLsbD_of_ge b0 (k - i) (by omega)]
          simp [hi64, hki64]
      · rw [BitVec.getLsbD_of_ge a0 i (by omega)]
        simp [hi64])
  · simp only [hk128, ↓reduceIte, bv_zero_getLsbD]
    rw [gf2PrefixFold_congr (q := fun _ => false) (fun i _ => by
      rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
      by_cases hi64 : i < 64
      · have hn64 : ¬(k - i < 64) := by omega
        simp [hi64, hn64]
      · simp [hi64]), gf2PrefixFold_zero]

private theorem polynomial_mult_hi_lo (a1 b0 : BitVec 64) :
    DPSFP.polynomial_mult (a1 ++ 0#64) (0#64 ++ b0) =
      (0#64 ++ BitVec.extractLsb' 64 64 (DPSFP.polynomial_mult a1 b0)) ++
      (BitVec.extractLsb' 0 64 (DPSFP.polynomial_mult a1 b0) ++ 0#64) := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [polynomial_mult_getLsbD (a1 ++ 0#64) (0#64 ++ b0) k hk,
    BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_append]
  by_cases hk64 : k < 64
  · have hk128 : k < 128 := by omega
    simp only [hk128, hk64, ↓reduceIte, bv_zero_getLsbD]
    rw [gf2PrefixFold_congr (q := fun _ => false) (fun i _ => by
      rw [BitVec.getLsbD_append]; simp [show i < 64 by omega]), gf2PrefixFold_zero]
  · by_cases hk192 : k < 192
    · have hsplit : k + 1 = 64 + (k - 64 + 1) := by omega
      rw [hsplit, gf2PrefixFold_add 64 (k - 64 + 1)]
      have hpre : gf2PrefixFold 64 (fun i => (a1 ++ 0#64).getLsbD i && (0#64 ++ b0).getLsbD (k - i)) = false := by
        rw [gf2PrefixFold_congr (q := fun _ => false) (fun i hi => by
          rw [BitVec.getLsbD_append]; simp [hi]), gf2PrefixFold_zero]
      rw [hpre, Bool.false_xor]
      have hmid : gf2PrefixFold (k - 64 + 1) (fun j => (a1 ++ 0#64).getLsbD (64 + j) && (0#64 ++ b0).getLsbD (k - (64 + j))) =
          (DPSFP.polynomial_mult a1 b0).getLsbD (k - 64) := by
        rw [polynomial_mult_getLsbD a1 b0 (k - 64) (by omega)]
        exact gf2PrefixFold_congr (fun j _ => by
          rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
          have hn64 : ¬(64 + j < 64) := by omega
          have hsub : 64 + j - 64 = j := by omega
          have hsub2 : k - (64 + j) = k - 64 - j := by omega
          simp only [hn64, ↓reduceIte, hsub, hsub2]
          by_cases hksub : k - 64 - j < 64
          · simp [hksub]
          · rw [BitVec.getLsbD_of_ge b0 (k - 64 - j) (by omega)]
            simp [hksub])
      rw [hmid]
      by_cases hk128 : k < 128
      · simp [hk128, hk64, show k - 64 < 64 by omega]
      · have hlt : k - 128 < 64 := by omega
        have hadd : 64 + (k - 128) = k - 64 := by omega
        simp [hk128, hlt, hadd]
    · have hn128 : ¬(k < 128) := by omega
      have hn64 : ¬(k - 128 < 64) := by omega
      simp only [hn128, hn64, ↓reduceIte, bv_zero_getLsbD]
      rw [gf2PrefixFold_congr (q := fun _ => false) (fun i _ => by
        rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
        by_cases hi64 : i < 64
        · simp [hi64]
        · by_cases hi128 : i < 128
          · have hnki : ¬(k - i < 64) := by omega
            simp [hi64, hnki]
          · rw [BitVec.getLsbD_of_ge a1 (i - 64) (by omega)]; simp [hi64]), gf2PrefixFold_zero]

private theorem polynomial_mult_hi_hi (a1 b1 : BitVec 64) :
    DPSFP.polynomial_mult (a1 ++ 0#64) (b1 ++ 0#64) =
      DPSFP.polynomial_mult a1 b1 ++ 0#128 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [polynomial_mult_getLsbD (a1 ++ 0#64) (b1 ++ 0#64) k hk, BitVec.getLsbD_append]
  by_cases hk128 : k < 128
  · simp only [hk128, ↓reduceIte, bv_zero_getLsbD]
    rw [gf2PrefixFold_congr (q := fun _ => false) (fun i _ => by
      rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
      by_cases hi64 : i < 64
      · simp [hi64]
      · simp [hi64, show k - i < 64 by omega]), gf2PrefixFold_zero]
  · simp only [hk128, ↓reduceIte]
    have hsplit : k + 1 = 64 + (k - 64 + 1) := by omega
    rw [hsplit, gf2PrefixFold_add 64 (k - 64 + 1)]
    have hpre : gf2PrefixFold 64 (fun i => (a1 ++ 0#64).getLsbD i && (b1 ++ 0#64).getLsbD (k - i)) = false := by
      rw [gf2PrefixFold_congr (q := fun _ => false) (fun i hi => by
        rw [BitVec.getLsbD_append]; simp [hi]), gf2PrefixFold_zero]
    rw [hpre, Bool.false_xor]
    have hsplit2 : k - 64 + 1 = (k - 128 + 1) + 64 := by omega
    rw [hsplit2, gf2PrefixFold_add (k - 128 + 1) 64]
    have hpost : gf2PrefixFold 64 (fun j => (a1 ++ 0#64).getLsbD (64 + (k - 128 + 1 + j)) &&
        (b1 ++ 0#64).getLsbD (k - (64 + (k - 128 + 1 + j)))) = false := by
      rw [gf2PrefixFold_congr (q := fun _ => false) (fun j _ => by
        have hlt : k - (64 + (k - 128 + 1 + j)) < 64 := by omega
        have hb0 : (b1 ++ 0#64).getLsbD (k - (64 + (k - 128 + 1 + j))) = false := by
          rw [BitVec.getLsbD_append]; simp [hlt]
        rw [hb0, Bool.and_false]), gf2PrefixFold_zero]
    rw [hpost, Bool.xor_false, polynomial_mult_getLsbD a1 b1 (k - 128) (by omega)]
    exact gf2PrefixFold_congr (fun j _ => by
      rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
      have hn1 : ¬(64 + j < 64) := by omega
      have hs1 : 64 + j - 64 = j := by omega
      have hn2 : ¬(k - (64 + j) < 64) := by omega
      have hs2 : k - (64 + j) - 64 = k - 128 - j := by omega
      simp [hn1, hs1, hn2, hs2])

/-- Multiply a degree-$<128$ polynomial in $\mathbb{F}_2[x]$ by $x$ modulo
    $p(x) = x^{128} + x^7 + x^2 + x + 1$ (`0x87`). -/
def mulXMod128 (v : BitVec 128) : BitVec 128 :=
  (v <<< 1) ^^^ (if v.getLsbD 127 then 0x87#128 else 0#128)

/-- Iterated multiplication by $x^k$ modulo $p(x) = x^{128} + x^7 + x^2 + x + 1$. -/
def mulXKMod128 : Nat → BitVec 128 → BitVec 128
  | 0, v => v
  | k + 1, v => mulXMod128 (mulXKMod128 k v)

private def gf2PolyModStep (w : BitVec 256) : Nat → BitVec 128
  | 0 => 0#128
  | m + 1 =>
    mulXMod128 (gf2PolyModStep w m) ^^^ (if w.getLsbD (255 - m) then 1#128 else 0#128)

/-- Genuine 256-step Horner/Euclidean polynomial remainder modulo
    $p(x) = x^{128} + x^7 + x^2 + x + 1$ (`0x87`) on `BitVec 256`. -/
def gf2PolyMod128 (w : BitVec 256) : BitVec 128 :=
  gf2PolyModStep w 256

private def gf128MulSpecStep (a b : BitVec 128) : Nat → BitVec 128
  | 0 => 0#128
  | m + 1 =>
    mulXMod128 (gf128MulSpecStep a b m) ^^^ (if b.getLsbD (127 - m) then a else 0#128)

/-- Genuine 128-step Horner $\mathbb{F}_{2^{128}} \cong \mathbb{F}_2[x]/(x^{128} + x^7 + x^2 + x + 1)$
    field multiplication specification on `BitVec 128`. -/
def gf128MulSpec (a b : BitVec 128) : BitVec 128 :=
  gf128MulSpecStep a b 128

private theorem mulXMod128_zero : mulXMod128 0#128 = 0#128 := by
  unfold mulXMod128; apply BitVec.eq_of_getLsbD_eq; intro k hk; simp [hk]

theorem mulXMod128_xor (u v : BitVec 128) :
    mulXMod128 (u ^^^ v) = mulXMod128 u ^^^ mulXMod128 v := by
  unfold mulXMod128
  have hshl : (u ^^^ v) <<< 1 = (u <<< 1) ^^^ (v <<< 1) := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_xor, hk, decide_true, Bool.true_and]
    by_cases hk0 : k < 1 <;> simp [hk0]
  have hbit : (u ^^^ v).getLsbD 127 = xor (u.getLsbD 127) (v.getLsbD 127) :=
    BitVec.getLsbD_xor
  rw [hshl, hbit, ite_xor_mask]
  apply BitVec.eq_of_getLsbD_eq; intro k _
  simp only [BitVec.getLsbD_xor]
  cases (u <<< 1).getLsbD k <;> cases (v <<< 1).getLsbD k <;>
    cases (if u.getLsbD 127 then 0x87#128 else 0#128).getLsbD k <;>
    cases (if v.getLsbD 127 then 0x87#128 else 0#128).getLsbD k <;> rfl

private theorem mulXMod128_lt127 (v : BitVec 128) (h : v.getLsbD 127 = false) :
    mulXMod128 v = v <<< 1 := by
  unfold mulXMod128; rw [h, cond_false_eq, bv128_xor_zero]

private theorem mulXKMod128_zero (k : Nat) : mulXKMod128 k 0#128 = 0#128 := by
  induction k with
  | zero => rfl
  | succ m ih => simp only [mulXKMod128, ih, mulXMod128_zero]

private theorem mulXKMod128_xor (k : Nat) (u v : BitVec 128) :
    mulXKMod128 k (u ^^^ v) = mulXKMod128 k u ^^^ mulXKMod128 k v := by
  induction k with
  | zero => rfl
  | succ m ih => simp only [mulXKMod128, ih, mulXMod128_xor]

private theorem mulXKMod128_add (i j : Nat) (v : BitVec 128) :
    mulXKMod128 (i + j) v = mulXKMod128 i (mulXKMod128 j v) := by
  induction i with
  | zero => simp [mulXKMod128]
  | succ m ih => rw [Nat.succ_add, mulXKMod128, mulXKMod128, ih]

private theorem mulXKMod128_shl_small (k : Nat) (v : BitVec 128)
    (hhigh : ∀ j, 128 - k ≤ j → j < 128 → v.getLsbD j = false) (hk : k ≤ 128) :
    mulXKMod128 k v = v <<< k := by
  induction k with
  | zero => simp [mulXKMod128]
  | succ m ih =>
    have ihm := ih (fun j hj1 hj2 => hhigh j (by omega) hj2) (by omega)
    rw [mulXKMod128, ihm]
    have hmsb : (v <<< m).getLsbD 127 = false := by
      rw [BitVec.getLsbD_shiftLeft]
      by_cases hm : 127 < m
      · omega
      · have hge : 128 - (m + 1) ≤ 127 - m := by omega
        have hlt : 127 - m < 128 := by omega
        simp [hm, hhigh (127 - m) hge hlt]
    rw [mulXMod128_lt127 _ hmsb]
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft]
    by_cases hj0 : j < 1
    · have hjm : j < m + 1 := by omega
      simp [hj, hj0, hjm]
    · by_cases hjm : j < m + 1
      · have hj1m : j - 1 < m := by omega
        simp [hj, hj0, hjm, hj1m, show j - 1 < 128 by omega]
      · have hj1m : ¬(j - 1 < m) := by omega
        have hsub : j - 1 - m = j - (m + 1) := by omega
        simp [hj, hj0, hjm, hj1m, show j - 1 < 128 by omega, hsub]

theorem mulXKMod128_128_one : mulXKMod128 128 1#128 = 0x87#128 := by
  have h127 : mulXKMod128 127 1#128 = 1#128 <<< 127 :=
    mulXKMod128_shl_small 127 1#128 (fun j hj1 hj2 => by
      cases j with
      | zero => omega
      | succ s => rw [BitVec.getLsbD_ofNat]; simp [hj2, Nat.testBit_succ]) (by omega)
  change mulXMod128 (mulXKMod128 127 1#128) = 0x87#128
  rw [h127]; unfold mulXMod128
  have hmsb : (1#128 <<< 127).getLsbD 127 = true := by
    rw [one_shl_getLsbD 127 127 (by omega) (by omega)]; rfl
  have hshl0 : (1#128 <<< 127) <<< 1 = 0#128 := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    rw [BitVec.getLsbD_shiftLeft]
    by_cases hk0 : k < 1
    · simp [hk, hk0]
    · rw [one_shl_getLsbD 127 (k - 1) (by omega) (by omega)]
      simp [hk, hk0, show k - 1 ≠ 127 by omega]
  rw [hmsb, hshl0, cond_true_eq, bv128_zero_xor]

private theorem gf2PolyModStep_zero (m : Nat) : gf2PolyModStep 0#256 m = 0#128 := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [gf2PolyModStep, ih, mulXMod128_zero, bv_zero_getLsbD, cond_false_eq, bv128_xor_zero]

private theorem gf2PolyModStep_xor (u v : BitVec 256) (m : Nat) :
    gf2PolyModStep (u ^^^ v) m = gf2PolyModStep u m ^^^ gf2PolyModStep v m := by
  induction m with
  | zero => simp only [gf2PolyModStep, bv128_xor_zero]
  | succ k ih =>
    simp only [gf2PolyModStep, ih, mulXMod128_xor, BitVec.getLsbD_xor, ite_xor_mask]
    apply BitVec.eq_of_getLsbD_eq; intro j _
    simp only [BitVec.getLsbD_xor]
    cases (mulXMod128 (gf2PolyModStep u k)).getLsbD j <;>
      cases (mulXMod128 (gf2PolyModStep v k)).getLsbD j <;>
      cases (if u.getLsbD (255 - k) then 1#128 else 0#128).getLsbD j <;>
      cases (if v.getLsbD (255 - k) then 1#128 else 0#128).getLsbD j <;> rfl

private theorem gf2PolyMod128_zero : gf2PolyMod128 0#256 = 0#128 := gf2PolyModStep_zero 256

theorem gf2PolyMod128_xor (u v : BitVec 256) :
    gf2PolyMod128 (u ^^^ v) = gf2PolyMod128 u ^^^ gf2PolyMod128 v :=
  gf2PolyModStep_xor u v 256

private theorem gf2PolyModStep_single_bit_before (p m : Nat) (hp : p < 256) (hm : m ≤ 255 - p) :
    gf2PolyModStep (1#256 <<< p) m = 0#128 := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [gf2PolyModStep, ih (by omega), mulXMod128_zero]
    have hbit : (1#256 <<< p).getLsbD (255 - k) = false := by
      rw [one_shl_getLsbD p (255 - k) hp (by omega)]
      simp [show 255 - k ≠ p by omega]
    rw [hbit, cond_false_eq, bv128_xor_zero]

private theorem gf2PolyModStep_single_bit_after (p d : Nat) (hp : p < 256) (hd : d ≤ p) :
    gf2PolyModStep (1#256 <<< p) (256 - p + d) = mulXKMod128 d 1#128 := by
  induction d with
  | zero =>
    have hstep : 256 - p + 0 = (255 - p) + 1 := by omega
    rw [hstep, gf2PolyModStep, gf2PolyModStep_single_bit_before p (255 - p) hp (by omega),
      mulXMod128_zero]
    have hbit : (1#256 <<< p).getLsbD (255 - (255 - p)) = true := by
      rw [one_shl_getLsbD p (255 - (255 - p)) hp (by omega)]
      simp [show 255 - (255 - p) = p by omega]
    rw [hbit, cond_true_eq, bv128_zero_xor, mulXKMod128]
  | succ k ih =>
    have hstep : 256 - p + (k + 1) = (256 - p + k) + 1 := by omega
    rw [hstep, gf2PolyModStep, ih (by omega)]
    have hbit : (1#256 <<< p).getLsbD (255 - (256 - p + k)) = false := by
      rw [one_shl_getLsbD p (255 - (256 - p + k)) hp (by omega)]
      simp [show 255 - (256 - p + k) ≠ p by omega]
    rw [hbit, cond_false_eq, bv128_xor_zero, mulXKMod128]

private theorem gf2PolyMod128_single_bit (p : Nat) (hp : p < 256) :
    gf2PolyMod128 (1#256 <<< p) = mulXKMod128 p 1#128 := by
  unfold gf2PolyMod128
  have h := gf2PolyModStep_single_bit_after p p hp (by omega)
  have h256 : 256 - p + p = 256 := by omega
  rw [h256] at h
  exact h

private theorem zero128_append_eq_shl (p : Nat) (hp : p < 128) :
    0#128 ++ (1#128 <<< p) = 1#256 <<< p := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_append, one_shl_getLsbD p k (by omega) hk]
  by_cases hk128 : k < 128
  · rw [one_shl_getLsbD p k hp hk128]; simp [hk128]
  · simp [hk128, show k ≠ p by omega]

theorem gf2PolyMod128_low128 (v : BitVec 128) :
    gf2PolyMod128 (0#128 ++ v) = v := by
  suffices ∀ (m : Nat), m ≤ 128 → gf2PolyMod128 (0#128 ++ bitPrefixSum v m) = bitPrefixSum v m by
    have h128 := this 128 (by omega)
    rw [bitPrefixSum_full] at h128
    exact h128
  intro m hm
  induction m with
  | zero =>
    dsimp only [bitPrefixSum]
    rw [zero128_append_zero128, gf2PolyMod128_zero]
  | succ k ih =>
    have hsplit : 0#128 ++ bitPrefixSum v (k + 1) =
        (0#128 ++ bitPrefixSum v k) ^^^ (0#128 ++ (if v.getLsbD k then 1#128 <<< k else 0#128)) := by
      apply BitVec.eq_of_getLsbD_eq; intro j _
      rw [bitPrefixSum, BitVec.getLsbD_xor, BitVec.getLsbD_append, BitVec.getLsbD_append,
        BitVec.getLsbD_append, BitVec.getLsbD_xor]
      by_cases hj : j < 128 <;> simp [hj]
    rw [hsplit, gf2PolyMod128_xor, ih (by omega), bitPrefixSum]
    congr 1
    cases hv : v.getLsbD k
    · rw [cond_false_eq, zero128_append_zero128, gf2PolyMod128_zero]
    · rw [cond_true_eq, zero128_append_eq_shl k (by omega),
        gf2PolyMod128_single_bit k (by omega)]
      exact mulXKMod128_shl_small k 1#128 (fun j hj1 hj2 => by
        cases j with
        | zero => omega
        | succ s => rw [BitVec.getLsbD_ofNat]; simp [hj2, Nat.testBit_succ]) (by omega)

private theorem zeroExtend128_0x87 :
    BitVec.zeroExtend (64 + 64) 0x87#64 = 0x87#128 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_setWidth]
  by_cases hk64 : k < 64
  · rw [BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat]; simp [hk, hk64]
  · rw [BitVec.getLsbD_of_ge 0x87#64 k (by omega), BitVec.getLsbD_ofNat]
    have hlt : 135 < 2 ^ k := by
      have h8 : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    simp [hk, Nat.testBit_lt_two_pow hlt]

private theorem mid64_append_eq_shl (i : Nat) (hi : i < 64) :
    (0#64 ++ (1#64 <<< i)) ++ 0#128 = 1#256 <<< (128 + i) := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append, one_shl_getLsbD (128 + i) k (by omega) hk]
  by_cases hk128 : k < 128
  · simp [hk128, show k ≠ 128 + i by omega]
  · by_cases hk192 : k - 128 < 64
    · rw [one_shl_getLsbD i (k - 128) hi hk192]
      have hiff : decide (k - 128 = i) = decide (k = 128 + i) := by
        apply Bool.eq_iff_iff.mpr; simp; omega
      simp [hk128, hk192, hiff]
    · simp [hk128, hk192, show k ≠ 128 + i by omega]

private theorem mulXKMod128_64_single_hi (k : Nat) (hk : k < 64) :
    mulXKMod128 64 ((1#64 <<< k) ++ 0#64) = DPSFP.polynomial_mult 0x87#64 (1#64 <<< k) := by
  rw [polynomial_mult_one_shl_right 0x87#64 k hk, zeroExtend128_0x87]
  have hshl64 : (1#64 <<< k) ++ 0#64 = mulXKMod128 (64 + k) 1#128 := by
    rw [mulXKMod128_shl_small (64 + k) 1#128 (fun j hj1 hj2 => by
      cases j with
      | zero => omega
      | succ s => rw [BitVec.getLsbD_ofNat]; simp [hj2, Nat.testBit_succ]) (by omega)]
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    rw [BitVec.getLsbD_append, one_shl_getLsbD (64 + k) j (by omega) hj]
    by_cases hj64 : j < 64
    · simp [hj64, show j ≠ 64 + k by omega]
    · rw [one_shl_getLsbD k (j - 64) hk (by omega)]
      have hiff : decide (j - 64 = k) = decide (j = 64 + k) := by
        apply Bool.eq_iff_iff.mpr; simp; omega
      simp [hj64, hiff]
  rw [hshl64, ← mulXKMod128_add 64 (64 + k)]
  have h128k : 64 + (64 + k) = k + 128 := by omega
  rw [h128k, mulXKMod128_add k 128, mulXKMod128_128_one]
  exact mulXKMod128_shl_small k 0x87#128 (fun j hj1 hj2 => by
    rw [← zeroExtend128_0x87, BitVec.getLsbD_setWidth, BitVec.getLsbD_of_ge 0x87#64 j (by omega)]
    simp [hj2]) (by omega)

private theorem gf2PolyMod128_limb2_single (k : Nat) (hk : k < 64) :
    gf2PolyMod128 ((0#64 ++ (1#64 <<< k)) ++ 0#128) = DPSFP.polynomial_mult 0x87#64 (1#64 <<< k) := by
  rw [mid64_append_eq_shl k hk, gf2PolyMod128_single_bit (128 + k) (by omega),
    polynomial_mult_one_shl_right 0x87#64 k hk, zeroExtend128_0x87,
    Nat.add_comm 128 k, mulXKMod128_add k 128, mulXKMod128_128_one]
  exact mulXKMod128_shl_small k 0x87#128 (fun j hj1 hj2 => by
    rw [← zeroExtend128_0x87, BitVec.getLsbD_setWidth, BitVec.getLsbD_of_ge 0x87#64 j (by omega)]
    simp [hj2]) (by omega)

private theorem gf2PolyMod128_limb2 (r2 : BitVec 64) :
    gf2PolyMod128 ((0#64 ++ r2) ++ 0#128) = DPSFP.polynomial_mult 0x87#64 r2 := by
  suffices ∀ (m : Nat), m ≤ 64 →
      gf2PolyMod128 ((0#64 ++ bitPrefixSum r2 m) ++ 0#128) =
        DPSFP.polynomial_mult 0x87#64 (bitPrefixSum r2 m) by
    have h64 := this 64 (by omega)
    rw [bitPrefixSum_full] at h64
    exact h64
  intro m hm
  induction m with
  | zero =>
    dsimp only [bitPrefixSum]
    rw [zero64_64_append_zero128, gf2PolyMod128_zero, polynomial_mult_zero_right]
  | succ k ih =>
    have hsplit : (0#64 ++ bitPrefixSum r2 (k + 1)) ++ 0#128 =
        ((0#64 ++ bitPrefixSum r2 k) ++ 0#128) ^^^
        ((0#64 ++ (if r2.getLsbD k then 1#64 <<< k else 0#64)) ++ 0#128) := by
      apply BitVec.eq_of_getLsbD_eq; intro j _
      rw [bitPrefixSum, BitVec.getLsbD_xor, BitVec.getLsbD_append, BitVec.getLsbD_append,
        BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_append,
        BitVec.getLsbD_xor]
      by_cases hj1 : j < 128
      · simp [hj1]
      · by_cases hj2 : j - 128 < 64 <;> simp [hj1, hj2]
    rw [hsplit, gf2PolyMod128_xor, ih (by omega), bitPrefixSum, polynomial_mult_xor_right]
    congr 1
    cases hr : r2.getLsbD k
    · rw [cond_false_eq, zero64_64_append_zero128, gf2PolyMod128_zero, polynomial_mult_zero_right]
    · rw [cond_true_eq, gf2PolyMod128_limb2_single k (by omega)]

private theorem gf2PolyMod128_shift64 (v : BitVec 128) :
    mulXKMod128 64 v =
      (BitVec.extractLsb' 0 64 v ++ 0#64) ^^^
      DPSFP.polynomial_mult 0x87#64 (BitVec.extractLsb' 64 64 v) := by
  let lo := BitVec.extractLsb' 0 64 v
  let hi := BitVec.extractLsb' 64 64 v
  change mulXKMod128 64 v = (lo ++ 0#64) ^^^ DPSFP.polynomial_mult 0x87#64 hi
  have hv : v = (hi ++ 0#64) ^^^ (0#64 ++ lo) := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    rw [BitVec.getLsbD_xor, BitVec.getLsbD_append, BitVec.getLsbD_append]
    by_cases hk64 : k < 64
    · simp [lo, hk64]
    · have hsub : k - 64 < 64 := by omega
      have hadd : 64 + (k - 64) = k := by omega
      simp [hi, hk64, hsub, hadd]
  rw [hv, mulXKMod128_xor]
  have hlo : mulXKMod128 64 (0#64 ++ lo) = lo ++ 0#64 := by
    rw [mulXKMod128_shl_small 64 (0#64 ++ lo) (fun j hj1 _ => by
      rw [BitVec.getLsbD_append]; simp [show ¬(j < 64) by omega]) (by omega)]
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getLsbD_append]
    by_cases hk64 : k < 64
    · simp [hk, hk64]
    · simp [hk, hk64, show k - 64 < 64 by omega]
  have hhi : mulXKMod128 64 (hi ++ 0#64) = DPSFP.polynomial_mult 0x87#64 hi := by
    suffices ∀ (m : Nat), m ≤ 64 →
        mulXKMod128 64 (bitPrefixSum hi m ++ 0#64) = DPSFP.polynomial_mult 0x87#64 (bitPrefixSum hi m) by
      have h64 := this 64 (by omega)
      rw [bitPrefixSum_full] at h64
      exact h64
    intro m hm
    induction m with
    | zero =>
      dsimp only [bitPrefixSum]
      rw [zero64_append_zero64, mulXKMod128_zero, polynomial_mult_zero_right]
    | succ k ih =>
      have hsp : bitPrefixSum hi (k + 1) ++ 0#64 =
          (bitPrefixSum hi k ++ 0#64) ^^^ ((if hi.getLsbD k then 1#64 <<< k else 0#64) ++ 0#64) := by
        apply BitVec.eq_of_getLsbD_eq; intro j _
        rw [bitPrefixSum, BitVec.getLsbD_xor, BitVec.getLsbD_append, BitVec.getLsbD_append,
          BitVec.getLsbD_append, BitVec.getLsbD_xor]
        by_cases hj : j < 64 <;> simp [hj]
      rw [hsp, mulXKMod128_xor, ih (by omega), bitPrefixSum, polynomial_mult_xor_right]
      have hite :
          mulXKMod128 64 ((if hi.getLsbD k then 1#64 <<< k else 0#64) ++ 0#64) =
          DPSFP.polynomial_mult 0x87#64 (if hi.getLsbD k then 1#64 <<< k else 0#64) := by
        cases hh : hi.getLsbD k
        · rw [cond_false_eq, zero64_append_zero64, mulXKMod128_zero, polynomial_mult_zero_right]
        · rw [cond_true_eq, mulXKMod128_64_single_hi k (by omega)]
      rw [hite]
  rw [hhi, hlo, bv128_xor_comm]

private theorem hi64_append_eq_shl (i : Nat) (hi : i < 64) :
    ((1#64 <<< i) ++ 0#64) ++ 0#128 = 1#256 <<< (192 + i) := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append, one_shl_getLsbD (192 + i) k (by omega) hk]
  by_cases hk128 : k < 128
  · simp [hk128, show k ≠ 192 + i by omega]
  · by_cases hk192 : k - 128 < 64
    · simp [hk128, hk192, show k ≠ 192 + i by omega]
    · have hksub : k - 128 - 64 < 64 := by omega
      rw [one_shl_getLsbD i (k - 128 - 64) hi hksub]
      have hiff : decide (k - 128 - 64 = i) = decide (k = 192 + i) := by
        apply Bool.eq_iff_iff.mpr; simp; omega
      simp [hk128, hk192, hiff]

private theorem gf2PolyMod128_limb3 (r3 : BitVec 64) :
    gf2PolyMod128 ((r3 ++ 0#64) ++ 0#128) =
      let red3 := DPSFP.polynomial_mult 0x87#64 r3
      (BitVec.extractLsb' 0 64 red3 ++ 0#64) ^^^
      DPSFP.polynomial_mult 0x87#64 (BitVec.extractLsb' 64 64 red3) := by
  dsimp only
  rw [← gf2PolyMod128_shift64 (DPSFP.polynomial_mult 0x87#64 r3), ← gf2PolyMod128_limb2 r3]
  suffices ∀ (m : Nat), m ≤ 64 →
      gf2PolyMod128 ((bitPrefixSum r3 m ++ 0#64) ++ 0#128) =
        mulXKMod128 64 (gf2PolyMod128 ((0#64 ++ bitPrefixSum r3 m) ++ 0#128)) by
    have h64 := this 64 (by omega)
    rw [bitPrefixSum_full] at h64
    exact h64
  intro m hm
  induction m with
  | zero =>
    dsimp only [bitPrefixSum]
    rw [zero64_64_append_zero128, gf2PolyMod128_zero, mulXKMod128_zero]
  | succ k ih =>
    have hsp1 : (bitPrefixSum r3 (k + 1) ++ 0#64) ++ 0#128 =
        ((bitPrefixSum r3 k ++ 0#64) ++ 0#128) ^^^
        (((if r3.getLsbD k then 1#64 <<< k else 0#64) ++ 0#64) ++ 0#128) := by
      apply BitVec.eq_of_getLsbD_eq; intro j _
      rw [bitPrefixSum, BitVec.getLsbD_xor, BitVec.getLsbD_append, BitVec.getLsbD_append,
        BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_append,
        BitVec.getLsbD_xor]
      by_cases hj1 : j < 128
      · simp [hj1]
      · by_cases hj2 : j - 128 < 64 <;> simp [hj1, hj2]
    have hsp2 : (0#64 ++ bitPrefixSum r3 (k + 1)) ++ 0#128 =
        ((0#64 ++ bitPrefixSum r3 k) ++ 0#128) ^^^
        ((0#64 ++ (if r3.getLsbD k then 1#64 <<< k else 0#64)) ++ 0#128) := by
      apply BitVec.eq_of_getLsbD_eq; intro j _
      rw [bitPrefixSum, BitVec.getLsbD_xor, BitVec.getLsbD_append, BitVec.getLsbD_append,
        BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_append,
        BitVec.getLsbD_xor]
      by_cases hj1 : j < 128
      · simp [hj1]
      · by_cases hj2 : j - 128 < 64 <;> simp [hj1, hj2]
    rw [hsp1, hsp2, gf2PolyMod128_xor, gf2PolyMod128_xor, mulXKMod128_xor, ih (by omega)]
    congr 1
    cases hr : r3.getLsbD k
    · rw [cond_false_eq, zero64_64_append_zero128, gf2PolyMod128_zero, mulXKMod128_zero]
    · rw [cond_true_eq, hi64_append_eq_shl k (by omega), mid64_append_eq_shl k (by omega),
        gf2PolyMod128_single_bit (192 + k) (by omega),
        gf2PolyMod128_single_bit (128 + k) (by omega), ← mulXKMod128_add 64 (128 + k)]
      have hadd : 192 + k = 64 + (128 + k) := by omega
      rw [hadd]

/-- Assemble the three 128-bit partial products `(lowProd, midProd, highProd)` into the
    256-bit carryless polynomial product `(r3 : r2 : r1 : r0)` reduced by `QReg.reduceGF128`. -/
def karatsubaAssemble256 (lowProd midProd highProd : LNSym.QReg) : BitVec 256 :=
  ((highProd.hi.toBitVec ++ (highProd.lo ^^^ midProd.hi).toBitVec) ++
   ((lowProd.hi ^^^ midProd.lo).toBitVec ++ lowProd.lo.toBitVec))

/-- Soundness of `LNSym.QReg.reduceGF128` against genuine 256-bit polynomial modular reduction
    `gf2PolyMod128` modulo $p(x) = x^{128} + x^7 + x^2 + x + 1$ (`0x87`). -/
theorem qregToBv128_reduceGF128_eq_gf2PolyMod128 (lowProd midProd highProd : LNSym.QReg) :
    qregToBv128 (LNSym.QReg.reduceGF128 lowProd midProd highProd) =
      gf2PolyMod128 (karatsubaAssemble256 lowProd midProd highProd) := by
  let r0 := lowProd.lo.toBitVec
  let r1 := (lowProd.hi ^^^ midProd.lo).toBitVec
  let r2 := (highProd.lo ^^^ midProd.hi).toBitVec
  let r3 := highProd.hi.toBitVec
  have hdecomp : karatsubaAssemble256 lowProd midProd highProd =
      (0#128 ++ (r1 ++ r0)) ^^^ ((0#64 ++ r2) ++ 0#128) ^^^ ((r3 ++ 0#64) ++ 0#128) := by
    unfold karatsubaAssemble256
    apply BitVec.eq_of_getLsbD_eq; intro k _
    simp only [r0, r1, r2, r3, BitVec.getLsbD_xor, BitVec.getLsbD_append]
    by_cases hk128 : k < 128
    · by_cases hk64 : k < 64 <;> simp [hk128, hk64]
    · by_cases hk192 : k - 128 < 64 <;> simp [hk128, hk192]
  rw [hdecomp, gf2PolyMod128_xor, gf2PolyMod128_xor,
    gf2PolyMod128_low128, gf2PolyMod128_limb2, gf2PolyMod128_limb3]
  dsimp only [qregToBv128, LNSym.QReg.reduceGF128]
  have h135 : (0x87 : UInt64).toBitVec = 0x87#64 := rfl
  have hlhs :
      (((lowProd.hi ^^^ midProd.lo) ^^^ clmul64Hi (highProd.lo ^^^ midProd.hi) 0x87 ^^^
          clmul64 highProd.hi 0x87 ^^^ clmul64Hi (clmul64Hi highProd.hi 0x87) 0x87).toBitVec ++
       (lowProd.lo ^^^ clmul64 (highProd.lo ^^^ midProd.hi) 0x87 ^^^
          clmul64 (clmul64Hi highProd.hi 0x87) 0x87).toBitVec) =
      ((r1 ^^^ BitVec.extractLsb' 64 64 (DPSFP.polynomial_mult 0x87#64 r2) ^^^
          BitVec.extractLsb' 0 64 (DPSFP.polynomial_mult 0x87#64 r3) ^^^
          BitVec.extractLsb' 64 64 (DPSFP.polynomial_mult 0x87#64
            (BitVec.extractLsb' 64 64 (DPSFP.polynomial_mult 0x87#64 r3)))) ++
       (r0 ^^^ BitVec.extractLsb' 0 64 (DPSFP.polynomial_mult 0x87#64 r2) ^^^
          BitVec.extractLsb' 0 64 (DPSFP.polynomial_mult 0x87#64
            (BitVec.extractLsb' 64 64 (DPSFP.polynomial_mult 0x87#64 r3))))) := by
    simp only [r0, r1, r2, r3, UInt64.toBitVec_xor,
      clmul64_eq_polynomial_mult_lo, clmul64Hi_eq_polynomial_mult_hi, h135]
  change _ = ((r1 ++ r0) ^^^ DPSFP.polynomial_mult 0x87#64 r2) ^^^
      ((BitVec.extractLsb' 0 64 (DPSFP.polynomial_mult 0x87#64 r3) ++ 0#64) ^^^
       DPSFP.polynomial_mult 0x87#64 (BitVec.extractLsb' 64 64 (DPSFP.polynomial_mult 0x87#64 r3)))
  rw [hlhs]
  generalize DPSFP.polynomial_mult 0x87#64 r2 = red2
  generalize DPSFP.polynomial_mult 0x87#64 r3 = red3
  generalize DPSFP.polynomial_mult 0x87#64 (BitVec.extractLsb' 64 64 red3) = fold
  apply BitVec.eq_of_getLsbD_eq; intro k _
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_xor, BitVec.getLsbD_extractLsb', Nat.zero_add]
  by_cases hk64 : k < 64
  · simp only [hk64, ↓reduceIte, BitVec.getLsbD_zero, decide_true, Bool.true_and]
    cases r0.getLsbD k <;> cases red2.getLsbD k <;> cases fold.getLsbD k <;> rfl
  · have hsub : k - 64 < 64 := by omega
    have hadd : 64 + (k - 64) = k := by omega
    simp only [hk64, hsub, hadd, ↓reduceIte, decide_true, Bool.true_and]
    cases r1.getLsbD (k - 64) <;> cases red2.getLsbD k <;>
      cases red3.getLsbD (k - 64) <;> cases fold.getLsbD k <;> rfl

theorem karatsubaAssemble256_mul_eq_polynomial_mult (a b : LNSym.QReg) :
    karatsubaAssemble256
      (LNSym.QReg.pmull64 a.lo b.lo)
      (LNSym.QReg.xor (LNSym.QReg.pmull64 a.lo b.hi) (LNSym.QReg.pmull64 a.hi b.lo))
      (LNSym.QReg.pmull64 a.hi b.hi) =
      DPSFP.polynomial_mult (qregToBv128 a) (qregToBv128 b) := by
  let a0 := a.lo.toBitVec
  let a1 := a.hi.toBitVec
  let b0 := b.lo.toBitVec
  let b1 := b.hi.toBitVec
  have ha : qregToBv128 a = (a1 ++ 0#64) ^^^ (0#64 ++ a0) := by
    apply BitVec.eq_of_getLsbD_eq; intro k _
    simp only [qregToBv128, a0, a1, BitVec.getLsbD_xor, BitVec.getLsbD_append]
    by_cases hk64 : k < 64 <;> simp [hk64]
  have hb : qregToBv128 b = (b1 ++ 0#64) ^^^ (0#64 ++ b0) := by
    apply BitVec.eq_of_getLsbD_eq; intro k _
    simp only [qregToBv128, b0, b1, BitVec.getLsbD_xor, BitVec.getLsbD_append]
    by_cases hk64 : k < 64 <;> simp [hk64]
  rw [ha, hb, polynomial_mult_xor_left, polynomial_mult_xor_right, polynomial_mult_xor_right,
    polynomial_mult_hi_hi, polynomial_mult_hi_lo,
    polynomial_mult_comm (0#64 ++ a0) (b1 ++ 0#64), polynomial_mult_hi_lo,
    polynomial_mult_lo_lo,
    polynomial_mult_comm a1 b1, polynomial_mult_comm a1 b0,
    polynomial_mult_comm b1 a0, polynomial_mult_comm a0 b0]
  unfold karatsubaAssemble256
  simp only [LNSym.QReg.pmull64, LNSym.QReg.xor, UInt64.toBitVec_xor,
    clmul64_eq_polynomial_mult_lo, clmul64Hi_eq_polynomial_mult_hi]
  change _ =
    (((DPSFP.polynomial_mult b1 a1 ++ 0#128) ^^^
      ((0#64 ++ BitVec.extractLsb' 64 64 (DPSFP.polynomial_mult b0 a1)) ++
       (BitVec.extractLsb' 0 64 (DPSFP.polynomial_mult b0 a1) ++ 0#64))) ^^^
     (((0#64 ++ BitVec.extractLsb' 64 64 (DPSFP.polynomial_mult a0 b1)) ++
       (BitVec.extractLsb' 0 64 (DPSFP.polynomial_mult a0 b1) ++ 0#64)) ^^^
      (0#128 ++ DPSFP.polynomial_mult b0 a0)))
  rw [polynomial_mult_comm a0 b1]
  generalize DPSFP.polynomial_mult b0 a0 = p00
  generalize DPSFP.polynomial_mult b1 a0 = p01
  generalize DPSFP.polynomial_mult b0 a1 = p10
  generalize DPSFP.polynomial_mult b1 a1 = p11
  apply BitVec.eq_of_getLsbD_eq; intro k _
  by_cases hk128 : k < 128
  · by_cases hk64 : k < 64
    · simp only [BitVec.getLsbD_append, BitVec.getLsbD_xor, BitVec.getLsbD_extractLsb',
        BitVec.getLsbD_zero, hk128, hk64, ↓reduceIte, Nat.zero_add, decide_true, Bool.true_and,
        Bool.false_xor, Bool.xor_false]
    · have hsub : k - 64 < 64 := by omega
      have hadd : 64 + (k - 64) = k := by omega
      simp only [BitVec.getLsbD_append, BitVec.getLsbD_xor, BitVec.getLsbD_extractLsb',
        BitVec.getLsbD_zero, hk128, hk64, hsub, hadd, ↓reduceIte, Nat.zero_add, decide_true,
        Bool.true_and, Bool.false_xor]
      cases p00.getLsbD k <;> cases p01.getLsbD (k - 64) <;> cases p10.getLsbD (k - 64) <;> rfl
  · by_cases hk192 : k - 128 < 64
    · simp only [BitVec.getLsbD_append, BitVec.getLsbD_xor, BitVec.getLsbD_extractLsb',
        BitVec.getLsbD_zero, hk128, hk192, ↓reduceIte, Nat.zero_add, decide_true,
        Bool.true_and, Bool.xor_false]
      cases p11.getLsbD (k - 128) <;> cases p01.getLsbD (64 + (k - 128)) <;>
        cases p10.getLsbD (64 + (k - 128)) <;> rfl
    · have hsub : k - 128 - 64 < 64 := by omega
      have hadd : 64 + (k - 128 - 64) = k - 128 := by omega
      simp only [BitVec.getLsbD_append, BitVec.getLsbD_xor, BitVec.getLsbD_extractLsb',
        BitVec.getLsbD_zero, hk128, hk192, hsub, hadd, ↓reduceIte, decide_true,
        Bool.true_and, Bool.xor_false]

private theorem gf128MulSpecStep_zero_right (a : BitVec 128) (m : Nat) :
    gf128MulSpecStep a 0#128 m = 0#128 := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [gf128MulSpecStep, ih, mulXMod128_zero]
    have hb : (0#128).getLsbD (127 - k) = false := bv_zero_getLsbD 128 (127 - k)
    rw [hb, cond_false_eq, bv128_xor_zero]

private theorem gf128MulSpec_zero_right (a : BitVec 128) : gf128MulSpec a 0#128 = 0#128 :=
  gf128MulSpecStep_zero_right a 128

private theorem gf128MulSpecStep_zero_left (b : BitVec 128) (m : Nat) :
    gf128MulSpecStep 0#128 b m = 0#128 := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [gf128MulSpecStep, ih, mulXMod128_zero]
    cases hb : b.getLsbD (127 - k)
    · rw [cond_false_eq, bv128_xor_zero]
    · rw [cond_true_eq, bv128_xor_zero]

private theorem gf128MulSpec_zero_left (b : BitVec 128) : gf128MulSpec 0#128 b = 0#128 :=
  gf128MulSpecStep_zero_left b 128

private theorem gf128MulSpecStep_xor_right (a b c : BitVec 128) (m : Nat) :
    gf128MulSpecStep a (b ^^^ c) m = gf128MulSpecStep a b m ^^^ gf128MulSpecStep a c m := by
  induction m with
  | zero => simp only [gf128MulSpecStep, bv128_xor_zero]
  | succ k ih =>
    simp only [gf128MulSpecStep, ih, mulXMod128_xor, BitVec.getLsbD_xor, ite_xor_mask]
    apply BitVec.eq_of_getLsbD_eq; intro j _
    simp only [BitVec.getLsbD_xor]
    cases (mulXMod128 (gf128MulSpecStep a b k)).getLsbD j <;>
      cases (mulXMod128 (gf128MulSpecStep a c k)).getLsbD j <;>
      cases (if b.getLsbD (127 - k) then a else 0#128).getLsbD j <;>
      cases (if c.getLsbD (127 - k) then a else 0#128).getLsbD j <;> rfl

private theorem gf128MulSpec_xor_right (a b c : BitVec 128) :
    gf128MulSpec a (b ^^^ c) = gf128MulSpec a b ^^^ gf128MulSpec a c :=
  gf128MulSpecStep_xor_right a b c 128

private theorem gf128MulSpecStep_xor_left (a b c : BitVec 128) (m : Nat) :
    gf128MulSpecStep (a ^^^ b) c m = gf128MulSpecStep a c m ^^^ gf128MulSpecStep b c m := by
  induction m with
  | zero => simp only [gf128MulSpecStep, bv128_xor_zero]
  | succ k ih =>
    rw [gf128MulSpecStep, gf128MulSpecStep, gf128MulSpecStep, ih, mulXMod128_xor]
    have hite : (if c.getLsbD (127 - k) then a ^^^ b else 0#128) =
        (if c.getLsbD (127 - k) then a else 0#128) ^^^ (if c.getLsbD (127 - k) then b else 0#128) := by
      cases hc : c.getLsbD (127 - k)
      · rw [cond_false_eq, cond_false_eq, cond_false_eq, bv128_xor_zero]
      · rw [cond_true_eq, cond_true_eq, cond_true_eq]
    rw [hite]
    apply BitVec.eq_of_getLsbD_eq; intro j _
    simp only [BitVec.getLsbD_xor]
    cases (mulXMod128 (gf128MulSpecStep a c k)).getLsbD j <;>
      cases (mulXMod128 (gf128MulSpecStep b c k)).getLsbD j <;>
      cases (if c.getLsbD (127 - k) then a else 0#128).getLsbD j <;>
      cases (if c.getLsbD (127 - k) then b else 0#128).getLsbD j <;> rfl

private theorem gf128MulSpec_xor_left (a b c : BitVec 128) :
    gf128MulSpec (a ^^^ b) c = gf128MulSpec a c ^^^ gf128MulSpec b c :=
  gf128MulSpecStep_xor_left a b c 128

private theorem gf128MulSpecStep_single_bit_before (a : BitVec 128) (p m : Nat)
    (hp : p < 128) (hm : m ≤ 127 - p) :
    gf128MulSpecStep a (1#128 <<< p) m = 0#128 := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [gf128MulSpecStep, ih (by omega), mulXMod128_zero]
    have hb : (1#128 <<< p).getLsbD (127 - k) = false := by
      rw [one_shl_getLsbD p (127 - k) hp (by omega)]
      simp [show 127 - k ≠ p by omega]
    rw [hb, cond_false_eq, bv128_xor_zero]

private theorem gf128MulSpecStep_single_bit_after (a : BitVec 128) (p d : Nat)
    (hp : p < 128) (hd : d ≤ p) :
    gf128MulSpecStep a (1#128 <<< p) (128 - p + d) = mulXKMod128 d a := by
  induction d with
  | zero =>
    have hstep : 128 - p + 0 = (127 - p) + 1 := by omega
    rw [hstep, gf128MulSpecStep, gf128MulSpecStep_single_bit_before a p (127 - p) hp (by omega),
      mulXMod128_zero]
    have hb : (1#128 <<< p).getLsbD (127 - (127 - p)) = true := by
      rw [one_shl_getLsbD p (127 - (127 - p)) hp (by omega)]
      simp [show 127 - (127 - p) = p by omega]
    rw [hb, cond_true_eq, bv128_zero_xor, mulXKMod128]
  | succ k ih =>
    have hstep : 128 - p + (k + 1) = (128 - p + k) + 1 := by omega
    rw [hstep, gf128MulSpecStep, ih (by omega)]
    have hb : (1#128 <<< p).getLsbD (127 - (128 - p + k)) = false := by
      rw [one_shl_getLsbD p (127 - (128 - p + k)) hp (by omega)]
      simp [show 127 - (128 - p + k) ≠ p by omega]
    rw [hb, cond_false_eq, bv128_xor_zero, mulXKMod128]

private theorem gf128MulSpec_single_bit (a : BitVec 128) (p : Nat) (hp : p < 128) :
    gf128MulSpec a (1#128 <<< p) = mulXKMod128 p a := by
  unfold gf128MulSpec
  have h := gf128MulSpecStep_single_bit_after a p p hp (by omega)
  have h128 : 128 - p + p = 128 := by omega
  rw [h128] at h
  exact h

private theorem zeroExtend256_eq_zero128_append (a : BitVec 128) :
    BitVec.zeroExtend (128 + 128) a = 0#128 ++ a := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  by_cases hk128 : k < 128
  · simp [hk, hk128]
  · rw [BitVec.getLsbD_of_ge a k (by omega)]
    simp [hk, hk128]

private theorem gf2PolyMod128_shl128 (a : BitVec 128) (k : Nat) (hk : k < 128) :
    gf2PolyMod128 ((0#128 ++ a) <<< k) = mulXKMod128 k a := by
  suffices ∀ (m : Nat), m ≤ 128 →
      gf2PolyMod128 ((0#128 ++ bitPrefixSum a m) <<< k) = mulXKMod128 k (bitPrefixSum a m) by
    have h128 := this 128 (by omega)
    rw [bitPrefixSum_full] at h128
    exact h128
  intro m hm
  induction m with
  | zero =>
    dsimp only [bitPrefixSum]
    have hz : ((0#128 : BitVec 128) ++ 0#128) <<< k = 0#256 := by
      apply BitVec.eq_of_getLsbD_eq; intro j hj
      rw [BitVec.getLsbD_shiftLeft]
      by_cases hjk : j < k
      · simp [hj, hjk]
      · rw [BitVec.getLsbD_append]
          <;> by_cases hj128 : j - k < 128 <;> simp [hj, hjk, hj128]
    rw [hz, gf2PolyMod128_zero, mulXKMod128_zero]
  | succ i ih =>
    have hsp : ((0#128 ++ bitPrefixSum a (i + 1)) <<< k) =
        ((0#128 ++ bitPrefixSum a i) <<< k) ^^^
        ((0#128 ++ (if a.getLsbD i then 1#128 <<< i else 0#128)) <<< k) := by
      apply BitVec.eq_of_getLsbD_eq; intro j hj
      rw [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft,
        BitVec.getLsbD_shiftLeft]
      by_cases hjk : j < k
      · simp [hj, hjk]
      · rw [bitPrefixSum, BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_append,
          BitVec.getLsbD_xor]
        by_cases hj128 : j - k < 128 <;> simp [hj, hjk, hj128]
    rw [hsp, gf2PolyMod128_xor, ih (by omega), bitPrefixSum, mulXKMod128_xor]
    congr 1
    cases ha : a.getLsbD i
    · rw [cond_false_eq]
      have hz : ((0#128 : BitVec 128) ++ 0#128) <<< k = 0#256 := by
        apply BitVec.eq_of_getLsbD_eq; intro j hj
        rw [BitVec.getLsbD_shiftLeft]
        by_cases hjk : j < k
        · simp [hj, hjk]
        · rw [BitVec.getLsbD_append]
          by_cases hj128 : j - k < 128 <;> simp [hj, hjk, hj128]
      rw [hz, gf2PolyMod128_zero, mulXKMod128_zero]
    · rw [cond_true_eq]
      have h1 : ((0#128 ++ (1#128 <<< i)) <<< k) = 1#256 <<< (k + i) := by
        apply BitVec.eq_of_getLsbD_eq; intro j hj
        rw [BitVec.getLsbD_shiftLeft, one_shl_getLsbD (k + i) j (by omega) hj]
        by_cases hjk : j < k
        · simp [hj, hjk, show j ≠ k + i by omega]
        · rw [BitVec.getLsbD_append]
          by_cases hj128 : j - k < 128
          · rw [one_shl_getLsbD i (j - k) (by omega) hj128]
            have hiff : decide (j - k = i) = decide (j = k + i) := by
              apply Bool.eq_iff_iff.mpr; simp; omega
            simp [hj, hjk, hj128, hiff]
          · simp [hj, hjk, hj128, show j ≠ k + i by omega]
      have h2 : (1#128 <<< i) = gf2PolyMod128 (0#128 ++ (1#128 <<< i)) :=
        (gf2PolyMod128_low128 _).symm
      rw [h1, gf2PolyMod128_single_bit (k + i) (by omega),
        h2, zero128_append_eq_shl i (by omega), gf2PolyMod128_single_bit i (by omega),
        ← mulXKMod128_add k i]

/-- Equivalence of 256-bit carryless polynomial multiplication followed by `gf2PolyMod128`
    and the 128-step Horner $\mathbb{F}_{2^{128}}$ field multiplication specification `gf128MulSpec`. -/
theorem gf2PolyMod128_polynomial_mult_eq_gf128MulSpec (a b : BitVec 128) :
    gf2PolyMod128 (DPSFP.polynomial_mult a b) = gf128MulSpec a b := by
  suffices ∀ (m : Nat), m ≤ 128 →
      gf2PolyMod128 (DPSFP.polynomial_mult a (bitPrefixSum b m)) =
        gf128MulSpec a (bitPrefixSum b m) by
    have h128 := this 128 (by omega)
    rw [bitPrefixSum_full] at h128
    exact h128
  intro m hm
  induction m with
  | zero =>
    dsimp only [bitPrefixSum]
    rw [polynomial_mult_zero_right, gf2PolyMod128_zero, gf128MulSpec_zero_right]
  | succ k ih =>
    rw [bitPrefixSum, polynomial_mult_xor_right, gf2PolyMod128_xor,
      gf128MulSpec_xor_right, ih (by omega)]
    have hite :
        gf2PolyMod128 (DPSFP.polynomial_mult a (if b.getLsbD k then 1#128 <<< k else 0#128)) =
        gf128MulSpec a (if b.getLsbD k then 1#128 <<< k else 0#128) := by
      cases hb : b.getLsbD k
      · rw [cond_false_eq, polynomial_mult_zero_right, gf2PolyMod128_zero, gf128MulSpec_zero_right]
      · rw [cond_true_eq, polynomial_mult_one_shl_right a k (by omega),
          zeroExtend256_eq_zero128_append, gf2PolyMod128_shl128 a k (by omega),
          gf128MulSpec_single_bit a k (by omega)]
    rw [hite]

/-- End-to-end soundness of `LNSym.QReg.mulGF128` against `gf128MulSpec` over
    $\mathbb{F}_2[x]/(x^{128} + x^7 + x^2 + x + 1)$. -/
theorem qregToBv128_mulGF128_eq_gf128MulSpec (a b : LNSym.QReg) :
    qregToBv128 (LNSym.QReg.mulGF128 a b) = gf128MulSpec (qregToBv128 a) (qregToBv128 b) := by
  unfold LNSym.QReg.mulGF128
  rw [qregToBv128_reduceGF128_eq_gf2PolyMod128, karatsubaAssemble256_mul_eq_polynomial_mult,
    gf2PolyMod128_polynomial_mult_eq_gf128MulSpec]

private theorem gf128MulSpec_comm (a b : BitVec 128) :
    gf128MulSpec a b = gf128MulSpec b a := by
  rw [← gf2PolyMod128_polynomial_mult_eq_gf128MulSpec,
    ← gf2PolyMod128_polynomial_mult_eq_gf128MulSpec, polynomial_mult_comm]

private theorem gf128MulSpecStep_mulXMod128_left (a b : BitVec 128) (m : Nat) :
    gf128MulSpecStep (mulXMod128 a) b m = mulXMod128 (gf128MulSpecStep a b m) := by
  induction m with
  | zero => simp only [gf128MulSpecStep, mulXMod128_zero]
  | succ k ih =>
    rw [gf128MulSpecStep, gf128MulSpecStep, ih, mulXMod128_xor]
    have hite : (if b.getLsbD (127 - k) then mulXMod128 a else 0#128) =
        mulXMod128 (if b.getLsbD (127 - k) then a else 0#128) := by
      cases hb : b.getLsbD (127 - k)
      · rw [cond_false_eq, cond_false_eq, mulXMod128_zero]
      · rw [cond_true_eq, cond_true_eq]
    rw [hite]

private theorem gf128MulSpec_mulXMod128_left (a b : BitVec 128) :
    gf128MulSpec (mulXMod128 a) b = mulXMod128 (gf128MulSpec a b) :=
  gf128MulSpecStep_mulXMod128_left a b 128

private theorem gf128MulSpecStep_succ (a b : BitVec 128) (m : Nat) :
    gf128MulSpecStep a b (m + 1) =
      mulXMod128 (gf128MulSpecStep a b m) ^^^ (if b.getLsbD (127 - m) then a else 0#128) := rfl

private theorem gf128MulSpec_assoc_step (a b c : BitVec 128) (m : Nat) :
    gf128MulSpec (gf128MulSpecStep a b m) c = gf128MulSpecStep (gf128MulSpec a c) b m := by
  induction m with
  | zero =>
    dsimp only [gf128MulSpecStep]
    exact gf128MulSpec_zero_left c
  | succ k ih =>
    rw [gf128MulSpecStep_succ, gf128MulSpecStep_succ, gf128MulSpec_xor_left,
      gf128MulSpec_mulXMod128_left, ih]
    have hite : gf128MulSpec (if b.getLsbD (127 - k) then a else 0#128) c =
        (if b.getLsbD (127 - k) then gf128MulSpec a c else 0#128) := by
      cases hb : b.getLsbD (127 - k)
      · rw [cond_false_eq, cond_false_eq, gf128MulSpec_zero_left]
      · rw [cond_true_eq, cond_true_eq]
    rw [hite]

private theorem gf128MulSpec_assoc (a b c : BitVec 128) :
    gf128MulSpec (gf128MulSpec a b) c = gf128MulSpec a (gf128MulSpec b c) := by
  calc
    gf128MulSpec (gf128MulSpec a b) c
      = gf128MulSpec (gf128MulSpec b a) c := by rw [gf128MulSpec_comm a b]
    _ = gf128MulSpec (gf128MulSpec b c) a := gf128MulSpec_assoc_step b a c 128
    _ = gf128MulSpec a (gf128MulSpec b c) := gf128MulSpec_comm _ a

private theorem gf128MulSpec_one_right (a : BitVec 128) :
    gf128MulSpec a 1#128 = a := by
  have h1 : (1#128 : BitVec 128) = 1#128 <<< 0 := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk; simp [hk]
  rw [h1, gf128MulSpec_single_bit a 0 (by omega), mulXKMod128]

/-- Multiplicative identity `1` (`x^0`) in $\mathbb{F}_{2^{128}}$ on `LNSym.QReg`. -/
def qregOne : LNSym.QReg := ⟨1, 0⟩

private theorem qreg_eq_of_qregToBv128_eq {a b : LNSym.QReg}
    (h : qregToBv128 a = qregToBv128 b) : a = b := by
  rw [← bv128ToQReg_qregToBv128 a, ← bv128ToQReg_qregToBv128 b, h]

private theorem qregToBv128_zero : qregToBv128 LNSym.QReg.zero = 0#128 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  dsimp [qregToBv128, LNSym.QReg.zero]
  rw [BitVec.getLsbD_append]
  by_cases hk64 : k < 64 <;> simp [hk64, show k - 64 < 64 by omega]

private theorem qregToBv128_one : qregToBv128 qregOne = 1#128 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  dsimp [qregToBv128, qregOne]
  rw [BitVec.getLsbD_append]
  by_cases hk64 : k < 64
  · simp only [hk64, ↓reduceIte]
    change (1#64).getLsbD k = (1#128).getLsbD k
    rw [BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat]
    simp [hk64, hk]
  · simp only [hk64, ↓reduceIte]
    change (0#64).getLsbD (k - 64) = (1#128).getLsbD k
    rw [bv_zero_getLsbD, BitVec.getLsbD_ofNat]
    cases k with
    | zero => omega
    | succ s =>
      simp [hk, Nat.testBit_succ]

theorem qreg_xor_comm (a b : LNSym.QReg) :
    LNSym.QReg.xor a b = LNSym.QReg.xor b a := by
  apply qreg_eq_of_qregToBv128_eq
  rw [qregToBv128_xor, qregToBv128_xor, bv128_xor_comm]

theorem qreg_xor_assoc (a b c : LNSym.QReg) :
    LNSym.QReg.xor (LNSym.QReg.xor a b) c = LNSym.QReg.xor a (LNSym.QReg.xor b c) := by
  apply qreg_eq_of_qregToBv128_eq
  rw [qregToBv128_xor, qregToBv128_xor, qregToBv128_xor, qregToBv128_xor, bv128_xor_assoc]

theorem qreg_xor_zero (a : LNSym.QReg) :
    LNSym.QReg.xor a LNSym.QReg.zero = a := by
  apply qreg_eq_of_qregToBv128_eq
  rw [qregToBv128_xor, qregToBv128_zero, bv128_xor_zero]

theorem qreg_zero_xor (a : LNSym.QReg) :
    LNSym.QReg.xor LNSym.QReg.zero a = a := by
  rw [qreg_xor_comm, qreg_xor_zero]

theorem qreg_xor_self (a : LNSym.QReg) :
    LNSym.QReg.xor a a = LNSym.QReg.zero := by
  apply qreg_eq_of_qregToBv128_eq
  rw [qregToBv128_xor, qregToBv128_zero, bv128_xor_self]

theorem mulGF128_comm (a b : LNSym.QReg) :
    LNSym.QReg.mulGF128 a b = LNSym.QReg.mulGF128 b a := by
  apply qreg_eq_of_qregToBv128_eq
  rw [qregToBv128_mulGF128_eq_gf128MulSpec, qregToBv128_mulGF128_eq_gf128MulSpec, gf128MulSpec_comm]

theorem mulGF128_assoc (a b c : LNSym.QReg) :
    LNSym.QReg.mulGF128 (LNSym.QReg.mulGF128 a b) c =
      LNSym.QReg.mulGF128 a (LNSym.QReg.mulGF128 b c) := by
  apply qreg_eq_of_qregToBv128_eq
  rw [qregToBv128_mulGF128_eq_gf128MulSpec, qregToBv128_mulGF128_eq_gf128MulSpec,
    qregToBv128_mulGF128_eq_gf128MulSpec, qregToBv128_mulGF128_eq_gf128MulSpec, gf128MulSpec_assoc]

theorem mulGF128_zero_right (a : LNSym.QReg) :
    LNSym.QReg.mulGF128 a LNSym.QReg.zero = LNSym.QReg.zero := by
  apply qreg_eq_of_qregToBv128_eq
  rw [qregToBv128_mulGF128_eq_gf128MulSpec, qregToBv128_zero, gf128MulSpec_zero_right]

theorem mulGF128_zero_left (a : LNSym.QReg) :
    LNSym.QReg.mulGF128 LNSym.QReg.zero a = LNSym.QReg.zero := by
  rw [mulGF128_comm, mulGF128_zero_right]

theorem mulGF128_one_right (a : LNSym.QReg) :
    LNSym.QReg.mulGF128 a qregOne = a := by
  apply qreg_eq_of_qregToBv128_eq
  rw [qregToBv128_mulGF128_eq_gf128MulSpec, qregToBv128_one, gf128MulSpec_one_right]

theorem mulGF128_one_left (a : LNSym.QReg) :
    LNSym.QReg.mulGF128 qregOne a = a := by
  rw [mulGF128_comm, mulGF128_one_right]

theorem mulGF128_xor_distrib_left (a b c : LNSym.QReg) :
    LNSym.QReg.mulGF128 (LNSym.QReg.xor a b) c =
      LNSym.QReg.xor (LNSym.QReg.mulGF128 a c) (LNSym.QReg.mulGF128 b c) := by
  apply qreg_eq_of_qregToBv128_eq
  rw [qregToBv128_mulGF128_eq_gf128MulSpec, qregToBv128_xor, qregToBv128_xor,
    qregToBv128_mulGF128_eq_gf128MulSpec, qregToBv128_mulGF128_eq_gf128MulSpec,
    gf128MulSpec_xor_left]

theorem mulGF128_xor_distrib_right (a b c : LNSym.QReg) :
    LNSym.QReg.mulGF128 a (LNSym.QReg.xor b c) =
      LNSym.QReg.xor (LNSym.QReg.mulGF128 a b) (LNSym.QReg.mulGF128 a c) := by
  apply qreg_eq_of_qregToBv128_eq
  rw [qregToBv128_mulGF128_eq_gf128MulSpec, qregToBv128_xor, qregToBv128_xor,
    qregToBv128_mulGF128_eq_gf128MulSpec, qregToBv128_mulGF128_eq_gf128MulSpec,
    gf128MulSpec_xor_right]

/-- Algebraic soundness of `LNSym.gf128ButterflyLane` over $\mathbb{F}_{2^{128}}$ (`gf128MulSpec`). -/
theorem gf128ButterflyLane_algebraic (u v tw : LNSym.QReg) :
    qregToBv128 (LNSym.gf128ButterflyLane u v tw).1 =
      qregToBv128 u ^^^ gf128MulSpec (qregToBv128 v) (qregToBv128 tw) ∧
    qregToBv128 (LNSym.gf128ButterflyLane u v tw).2 =
      (qregToBv128 u ^^^ gf128MulSpec (qregToBv128 v) (qregToBv128 tw)) ^^^ qregToBv128 v := by
  dsimp [LNSym.gf128ButterflyLane]
  constructor
  · rw [qregToBv128_xor, qregToBv128_mulGF128_eq_gf128MulSpec]
  · rw [qregToBv128_xor, qregToBv128_xor, qregToBv128_mulGF128_eq_gf128MulSpec]

/-- Exact invertibility / recovery law for the additive NTT radix-2 butterfly lane:
    given `(u', v') = gf128ButterflyLane u v tw`, `u' ⊕ v' = v` and `u' ⊕ ((u' ⊕ v') * tw) = u`. -/
theorem gf128ButterflyLane_recover_uv (u v tw : LNSym.QReg) :
    let (u', v') := LNSym.gf128ButterflyLane u v tw
    LNSym.QReg.xor u' v' = v ∧
    LNSym.QReg.xor u' (LNSym.QReg.mulGF128 (LNSym.QReg.xor u' v') tw) = u := by
  dsimp [LNSym.gf128ButterflyLane]
  have hv : LNSym.QReg.xor (LNSym.QReg.xor u (LNSym.QReg.mulGF128 v tw))
      (LNSym.QReg.xor (LNSym.QReg.xor u (LNSym.QReg.mulGF128 v tw)) v) = v := by
    rw [← qreg_xor_assoc, qreg_xor_self, qreg_zero_xor]
  refine ⟨hv, ?_⟩
  rw [hv, qreg_xor_assoc, qreg_xor_self, qreg_xor_zero]

/-- Direct single-instruction bisimulation for `EXT Vd.16B, Vn.16B, Vm.16B, #8`
    (`Q = 1#1`, `op2 = 0#2`, `imm4 = 8#4`, 64-bit lane extract across `[Vm:Vn]`)
    against `⟨(ms.readQ rn.toNat).hi, (ms.readQ rm.toNat).lo⟩`. -/
theorem exec_ext_8_bisim (ms : LNSym.ArmState) (as0 : _root_.ArmState)
    (rd rn rm : BitVec 5)
    (h_rn : read_sfp 128 rn as0 = qregToBv128 (ms.readQ rn.toNat))
    (h_rm : read_sfp 128 rm as0 = qregToBv128 (ms.readQ rm.toNat)) :
    let inst : Advanced_simd_extract_cls :=
      { Q := 1#1, op2 := 0#2, Rm := rm, imm4 := 8#4, Rn := rn, Rd := rd }
    let asf := DPSFP.exec_advanced_simd_extract inst as0
    read_sfp 128 rd asf =
      qregToBv128 ⟨(ms.readQ rn.toNat).hi, (ms.readQ rm.toNat).lo⟩ := by
  simp only [state_simp_rules, bitvec_rules, minimal_theory] at h_rn h_rm ⊢
  change BitVec.extractLsb' 64 128 (r (StateField.SFP rm) as0 ++ r (StateField.SFP rn) as0) =
    qregToBv128 ⟨(ms.readQ rn.toNat).hi, (ms.readQ rm.toNat).lo⟩
  rw [h_rn, h_rm]
  dsimp only [qregToBv128]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and, BitVec.getLsbD_append]
  by_cases hk64 : k < 64
  · have hlt128 : 64 + k < 128 := by omega
    have hnlt64 : ¬(64 + k < 64) := by omega
    have hsub : 64 + k - 64 = k := by omega
    simp [hk64, hlt128, hnlt64, hsub]
  · have hnlt128 : ¬(64 + k < 128) := by omega
    have hlt64 : k - 64 < 64 := by omega
    have hsub : 64 + k - 128 = k - 64 := by omega
    simp [hk64, hnlt128, hlt64, hsub]

private theorem runArm64_butterflyStepInstrs_state (idx : Nat) (s : LNSym.ArmState)
    (hvalid : s.validABI = true) :
    let u := s.sliceU[idx]?.getD LNSym.QReg.zero
    let v := s.sliceV[idx]?.getD LNSym.QReg.zero
    (LNSym.runArm64 (LNSym.butterflyStepInstrs idx) s).validABI = true ∧
    (LNSym.runArm64 (LNSym.butterflyStepInstrs idx) s).sliceU = s.sliceU ∧
    (LNSym.runArm64 (LNSym.butterflyStepInstrs idx) s).sliceV = s.sliceV ∧
    (LNSym.runArm64 (LNSym.butterflyStepInstrs idx) s).readQ 0 = s.readQ 0 ∧
    (LNSym.runArm64 (LNSym.butterflyStepInstrs idx) s).outU =
      s.outU ++ [(LNSym.gf128ButterflyLane u v (s.readQ 0)).1] ∧
    (LNSym.runArm64 (LNSym.butterflyStepInstrs idx) s).outV =
      s.outV ++ [(LNSym.gf128ButterflyLane u v (s.readQ 0)).2] := by
  dsimp [LNSym.butterflyStepInstrs, LNSym.runArm64, LNSym.execInstr,
    LNSym.ArmState.readQ, LNSym.ArmState.writeQ, LNSym.gf128ButterflyLane, LNSym.QReg.mulGF128]
  simp [hvalid]

private theorem runArm64_butterflySliceLoop_indices (indices : List Nat) (ms : LNSym.ArmState)
    (hvalid : ms.validABI = true) :
    LNSym.extractSlice (LNSym.runArm64 (indices.flatMap LNSym.butterflyStepInstrs) ms) =
      (ms.outU ++ indices.map (fun idx =>
          (LNSym.gf128ButterflyLane (ms.sliceU[idx]?.getD LNSym.QReg.zero)
            (ms.sliceV[idx]?.getD LNSym.QReg.zero) (ms.readQ 0)).1),
       ms.outV ++ indices.map (fun idx =>
          (LNSym.gf128ButterflyLane (ms.sliceU[idx]?.getD LNSym.QReg.zero)
            (ms.sliceV[idx]?.getD LNSym.QReg.zero) (ms.readQ 0)).2)) := by
  induction indices generalizing ms with
  | nil => simp [LNSym.extractSlice]
  | cons idx rest ih =>
    rw [List.flatMap_cons, LNSym.runArm64_append]
    rcases runArm64_butterflyStepInstrs_state idx ms hvalid with
      ⟨hv', hsu', hsv', hq0', houtU', houtV'⟩
    rw [ih _ hv', hsu', hsv', hq0', houtU', houtV']
    simp [List.append_assoc]

/-- Multi-lane induction theorem: running `(List.range n).flatMap LNSym.butterflyStepInstrs`
    on a valid `LNSym.ArmState` with empty output accumulators computes the lane-wise
    `LNSym.gf128ButterflyLane` map across all `n` lanes. -/
theorem runArm64_butterflySliceLoop_eq_mapIdx (n : Nat) (ms : LNSym.ArmState)
    (hvalid : ms.validABI = true) (houtU : ms.outU = []) (houtV : ms.outV = []) :
    LNSym.extractSlice (LNSym.runArm64 ((List.range n).flatMap LNSym.butterflyStepInstrs) ms) =
      ((List.range n).map (fun idx =>
          (LNSym.gf128ButterflyLane (ms.sliceU[idx]?.getD LNSym.QReg.zero)
            (ms.sliceV[idx]?.getD LNSym.QReg.zero) (ms.readQ 0)).1),
       (List.range n).map (fun idx =>
          (LNSym.gf128ButterflyLane (ms.sliceU[idx]?.getD LNSym.QReg.zero)
            (ms.sliceV[idx]?.getD LNSym.QReg.zero) (ms.readQ 0)).2)) := by
  rw [runArm64_butterflySliceLoop_indices (List.range n) ms hvalid, houtU, houtV]
  simp

/-- End-to-end 28-instruction `leanprover/LNSym` machine-code butterfly theorem stated
    directly against the genuine polynomial field multiplication specification `gf128MulSpec`. -/
theorem gf128_butterfly_program_run_28_field_spec (s0 sf : _root_.ArmState)
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
    read_mem_bytes 16 (read_gpr 64 2#5 s0) sf =
      qregToBv128 u ^^^ gf128MulSpec (qregToBv128 v) (qregToBv128 tw) ∧
    read_mem_bytes 16 (read_gpr 64 3#5 s0) sf =
      (qregToBv128 u ^^^ gf128MulSpec (qregToBv128 v) (qregToBv128 tw)) ^^^ qregToBv128 v := by
  rcases gf128_butterfly_program_run_28 s0 sf u v tw
    h_s0_prog h_s0_err h_s0_pc h_tw h_u h_v h_mem_sep h_run with
    ⟨herr, hpc, htw', hu', hv'⟩
  rcases gf128ButterflyLane_algebraic u v tw with ⟨halg1, halg2⟩
  exact ⟨herr, hpc, htw', hu'.trans halg1, hv'.trans halg2⟩

end LNSymBridge
