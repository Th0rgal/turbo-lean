import SailRiscvBridge.MirroredModel
import Sail
import LeanRV64D.Defs
import LeanRV64D.Prelude
import LeanRV64D.Xlen
import LeanRV64D.Arith
import LeanRV64D.Arithmetic
import LeanRV64D.MextTypes
import LeanRV64D.MextInsts
import LeanRV64D.ZbkbInsts
import LeanRV64D.Regs

/-!
# Stage 3E / Milestone `M5` RV64 Formal Bisimulation against `opencompl/sail-riscv-lean`

Bridges `TurboLean.PolicyGates` (`riscvDivU64Spec`, `riscvRemU64Spec`) and
`LeanNative.IR` (`clmul64`, `clmul64Hi`) directly against upstream
`opencompl/sail-riscv-lean` (`Lean_RV64D` + `Sail`) on `leanprover/lean4:v4.29.0`,
avoiding monolithic `LeanRV64D.InstsEnd` / `LeanRV64D.Step` / `LeanRV64D.ZicsrInsts`
imports so incremental elaboration stays lightweight and axiom-clean.
-/

namespace SailRiscvBridge

open Sail
open Sail.ConcurrencyInterfaceV1
open LeanRV64D
open LeanRV64D.Functions
open TurboLean.PolicyGates
open LeanNative.IR

/-! ## 1. RV64 Architectural Width & Base Register File Semantics -/

/-- Upstream `LeanRV64D` configures architectural `xlen = 64`, `xlen_bytes = 8`, `log2_xlen = 6`. -/
theorem rv64_xlen_params :
    Functions.xlen = 64 ∧ Functions.xlen_bytes = 8 ∧ Functions.log2_xlen = 6 :=
  ⟨rfl, rfl, rfl⟩

/-- Reading `x0` (`zreg` / `Regno 0`) in `SailM` returns `0#64` without reading `s.regs` and
    leaves the sequential machine state unchanged. -/
theorem rX_bits_zreg (s : SequentialState RegisterType trivialChoiceSource) :
    (rX_bits zreg).run s = .ok 0#64 s := by
  rfl

/-- Writing any 64-bit value to `x0` (`zreg` / `Regno 0`) in `SailM` is a pure no-op on
    `SequentialState` (neither mutating registers nor firing write callbacks). -/
theorem wX_bits_zreg_noop (v : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource) :
    (wX_bits zreg v).run s = .ok () s := by
  rfl

/-- Writing `v` to architectural register `x1` (`Regidx 1#5`) and reading `x1` back in `SailM`
    yields `v`. -/
theorem wX_then_rX_x1 (v : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource) :
    ((do wX_bits (.Regidx 1#5) v; rX_bits (.Regidx 1#5)).run s) =
      .ok v { s with regs := s.regs.insert .x1 v } := by
  simp [wX_bits, rX_bits, wX, rX, regval_into_reg, regval_from_reg,
    xreg_write_callback, reg_name_forwards, encdec_reg_forwards_matches,
    encdec_reg_forwards, get_config_use_abi_names, LeanRV64D.Functions.not,
    reg_arch_name_raw_forwards, xreg_full_write_callback, zero_extend, Sail.BitVec.zeroExtend,
    Sail.BitVec.toNatInt, to_bits, get_slice_int,
    writeReg, PreSail.writeReg, readReg, PreSail.readReg,
    modify, modifyGet, MonadStateOf.modifyGet, get, getThe, MonadStateOf.get]
  dsimp [EStateM.modifyGet, EStateM.get, EStateM.pure, EStateM.run]
  simp [Std.ExtDHashMap.get?_insert_self]
  rfl

/-! ## 2. Upstream Sail `to_bits_truncate` Algebraic Bridge -/

/-- Upstream `LeanRV64D.Functions.to_bits_truncate` (`Sail.get_slice_int l n 0`) is propositionally
    equal to Lean's canonical `BitVec.ofInt l n` for every width `l` and integer `n`. -/
theorem to_bits_truncate_eq_ofInt (l : Nat) (n : Int) :
    to_bits_truncate (l := l) n = BitVec.ofInt l n := by
  unfold to_bits_truncate get_slice_int BitVec.extractLsb'
  rw [Nat.zero_add]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.shiftRight_zero, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  have hdvd : (2 ^ l : Int) ∣ (2 ^ (l + 1) : Int) := ⟨2, by rw [Int.pow_succ]⟩
  have hpos1 : 0 < 2 ^ (l + 1) := Nat.two_pow_pos _
  have hpos0 : 0 < 2 ^ l := Nat.two_pow_pos _
  have hnonneg1 : 0 ≤ n % (2 ^ (l + 1) : Nat) := Int.emod_nonneg n (by omega)
  have hnonneg0 : 0 ≤ n % (2 ^ l : Nat) := Int.emod_nonneg n (by omega)
  apply Int.ofNat.inj
  change (((n % (2 ^ (l + 1) : Nat)).toNat : Int) % (2 ^ l : Nat)) =
    ((n % (2 ^ l : Nat)).toNat : Int)
  rw [Int.toNat_of_nonneg hnonneg1, Int.toNat_of_nonneg hnonneg0]
  exact Int.emod_emod_of_dvd n hdvd

private theorem ofInt_ofNat_eq_ofNat (l a : Nat) :
    BitVec.ofInt l (Int.ofNat a) = BitVec.ofNat l a := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  rfl

/-! ## 3. RV64M `DIVU` / `REMU` & `MUL` / `MULHU` Bisimulation -/

/-- Exact upstream Sail `execute_DIV` (`is_unsigned = true`) functional core from `LeanRV64D`. -/
def sailDivU64Core (rs1_bits rs2_bits : BitVec 64) : BitVec 64 :=
  let rs1_int : Int := Sail.BitVec.toNatInt rs1_bits
  let rs2_int : Int := Sail.BitVec.toNatInt rs2_bits
  let quotient : Int := if (rs2_int == 0 : Bool) then -1 else Int.tdiv rs1_int rs2_int
  to_bits_truncate (l := 64) quotient

/-- Exact upstream Sail `execute_REM` (`is_unsigned = true`) functional core from `LeanRV64D`. -/
def sailRemU64Core (rs1_bits rs2_bits : BitVec 64) : BitVec 64 :=
  let rs1_int : Int := Sail.BitVec.toNatInt rs1_bits
  let rs2_int : Int := Sail.BitVec.toNatInt rs2_bits
  let remainder : Int := if (rs2_int == 0 : Bool) then rs1_int else Int.tmod rs1_int rs2_int
  to_bits_truncate (l := 64) remainder

/-- `TurboLean.PolicyGates.riscvDivU64Spec` matches the upstream Sail RV64M `DIVU` semantics
    bit-for-bit across all 64-bit unsigned inputs (including division-by-zero returning `2^64 - 1`). -/
theorem riscvDivU64Spec_bisim_sail (lhs rhs : UInt64) :
    (riscvDivU64Spec lhs rhs).toBitVec = sailDivU64Core lhs.toBitVec rhs.toBitVec := by
  unfold riscvDivU64Spec sailDivU64Core Sail.BitVec.toNatInt
  rw [to_bits_truncate_eq_ofInt]
  by_cases hr : rhs = 0
  · subst hr
    have h0 : ((Int.ofNat (UInt64.toBitVec 0).toNat == 0) : Bool) = true := rfl
    have h0' : ((0 : UInt64) == 0) = true := rfl
    rw [h0, h0']
    simp only [↓reduceIte]
    decide
  · have hr_beq : (rhs == 0) = false := beq_false_of_ne hr
    have hr_nat_ne : rhs.toBitVec.toNat ≠ 0 := by
      intro h0
      apply hr
      apply UInt64.eq_of_toBitVec_eq
      exact BitVec.eq_of_toNat_eq h0
    have hr_int_ne : Int.ofNat rhs.toBitVec.toNat ≠ 0 := by
      intro h0
      exact hr_nat_ne (Int.ofNat.inj h0)
    have hr_int_beq : ((Int.ofNat rhs.toBitVec.toNat == 0) : Bool) = false :=
      beq_false_of_ne hr_int_ne
    rw [hr_beq, hr_int_beq]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have htdiv : Int.tdiv (Int.ofNat lhs.toBitVec.toNat) (Int.ofNat rhs.toBitVec.toNat) =
        Int.ofNat (lhs.toBitVec.toNat / rhs.toBitVec.toNat) := rfl
    rw [htdiv, ofInt_ofNat_eq_ofNat]
    apply BitVec.eq_of_toNat_eq
    simp only [UInt64.toBitVec_div, BitVec.udiv_def, BitVec.toNat_ofNat]

/-- `TurboLean.PolicyGates.riscvRemU64Spec` matches the upstream Sail RV64M `REMU` semantics
    bit-for-bit across all 64-bit unsigned inputs (including division-by-zero returning `lhs`). -/
theorem riscvRemU64Spec_bisim_sail (lhs rhs : UInt64) :
    (riscvRemU64Spec lhs rhs).toBitVec = sailRemU64Core lhs.toBitVec rhs.toBitVec := by
  unfold riscvRemU64Spec sailRemU64Core Sail.BitVec.toNatInt
  rw [to_bits_truncate_eq_ofInt]
  by_cases hr : rhs = 0
  · subst hr
    have h0 : ((Int.ofNat (UInt64.toBitVec 0).toNat == 0) : Bool) = true := rfl
    have h0' : ((0 : UInt64) == 0) = true := rfl
    rw [h0, h0']
    simp only [↓reduceIte]
    rw [ofInt_ofNat_eq_ofNat]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lhs.toBitVec.isLt]
  · have hr_beq : (rhs == 0) = false := beq_false_of_ne hr
    have hr_nat_ne : rhs.toBitVec.toNat ≠ 0 := by
      intro h0
      apply hr
      apply UInt64.eq_of_toBitVec_eq
      exact BitVec.eq_of_toNat_eq h0
    have hr_int_ne : Int.ofNat rhs.toBitVec.toNat ≠ 0 := by
      intro h0
      exact hr_nat_ne (Int.ofNat.inj h0)
    have hr_int_beq : ((Int.ofNat rhs.toBitVec.toNat == 0) : Bool) = false :=
      beq_false_of_ne hr_int_ne
    rw [hr_beq, hr_int_beq]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have htmod : Int.tmod (Int.ofNat lhs.toBitVec.toNat) (Int.ofNat rhs.toBitVec.toNat) =
        Int.ofNat (lhs.toBitVec.toNat % rhs.toBitVec.toNat) := rfl
    rw [htmod, ofInt_ofNat_eq_ofNat]
    apply BitVec.eq_of_toNat_eq
    simp only [UInt64.toBitVec_mod, BitVec.umod_def, BitVec.toNat_ofNat]

/-- Architectural RV64M unsigned division-remainder Euclidean identity (`lhs = q * rhs + r`,
    wrapping naturally on `rhs = 0` because `0xffffffffffffffff * 0 + lhs = lhs`). -/
theorem riscvDivRemU64Spec_euclidean (lhs rhs : UInt64) :
    riscvDivU64Spec lhs rhs * rhs + riscvRemU64Spec lhs rhs = lhs := by
  unfold riscvDivU64Spec riscvRemU64Spec
  by_cases hr : rhs = 0
  · subst hr; simp
  · have hr_beq : (rhs == 0) = false := beq_false_of_ne hr
    rw [hr_beq]
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply UInt64.eq_of_toBitVec_eq
    apply BitVec.eq_of_toNat_eq
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_mul, UInt64.toBitVec_div, UInt64.toBitVec_mod,
      BitVec.toNat_add, BitVec.toNat_mul, BitVec.udiv_def, BitVec.umod_def, BitVec.toNat_ofNat]
    have hlt : lhs.toBitVec.toNat < 2 ^ 64 := lhs.toBitVec.isLt
    have hq_lt : lhs.toBitVec.toNat / rhs.toBitVec.toNat < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlt
    have hr_lt : lhs.toBitVec.toNat % rhs.toBitVec.toNat < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (Nat.mod_le _ _) hlt
    rw [Nat.mod_eq_of_lt hq_lt, Nat.mod_eq_of_lt hr_lt, Nat.mod_add_mod]
    have hdiv : (lhs.toBitVec.toNat / rhs.toBitVec.toNat) * rhs.toBitVec.toNat +
        lhs.toBitVec.toNat % rhs.toBitVec.toNat = lhs.toBitVec.toNat := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod lhs.toBitVec.toNat rhs.toBitVec.toNat
    rw [hdiv, Nat.mod_eq_of_lt hlt]

/-- Upstream `LeanRV64D.Functions.mult_to_bits_half` (used directly by `execute_MUL` for `MUL`)
    computes `(a * b).toBitVec` on the low 64-bit half. -/
theorem mult_to_bits_half_low_unsigned_eq_mul (a b : UInt64) :
    mult_to_bits_half (l := 64) .Unsigned .Unsigned a.toBitVec b.toBitVec .Low =
      (a * b).toBitVec := by
  unfold mult_to_bits_half Sail.BitVec.toNatInt Sail.BitVec.extractLsb
  change BitVec.extractLsb 63 0 (to_bits_truncate (l := 128) (Int.ofNat (a.toBitVec.toNat * b.toBitVec.toNat))) =
    (a * b).toBitVec
  rw [to_bits_truncate_eq_ofInt, ofInt_ofNat_eq_ofNat]
  apply BitVec.eq_of_toNat_eq
  unfold BitVec.extractLsb BitVec.extractLsb'
  rw [BitVec.toNat_ofNat, Nat.shiftRight_zero, BitVec.toNat_ofNat,
    UInt64.toBitVec_mul, BitVec.toNat_mul]
  have hdvd : 2 ^ 64 ∣ 2 ^ 128 := ⟨2 ^ 64, by decide⟩
  exact Nat.mod_mod_of_dvd _ hdvd

/-- Upstream `LeanRV64D.Functions.mult_to_bits_half` (used directly by `execute_MUL` for `MULHU`)
    computes the upper 64 bits `((a.toNat * b.toNat) / 2^64)` of the full 128-bit unsigned product. -/
theorem mult_to_bits_half_high_unsigned_toNat (a b : UInt64) :
    (mult_to_bits_half (l := 64) .Unsigned .Unsigned a.toBitVec b.toBitVec .High).toNat =
      (a.toBitVec.toNat * b.toBitVec.toNat) / 2 ^ 64 := by
  unfold mult_to_bits_half Sail.BitVec.toNatInt Sail.BitVec.extractLsb
  change (BitVec.extractLsb 127 64
      (to_bits_truncate (l := 128) (Int.ofNat (a.toBitVec.toNat * b.toBitVec.toNat)))).toNat =
    (a.toBitVec.toNat * b.toBitVec.toNat) / 2 ^ 64
  rw [to_bits_truncate_eq_ofInt, ofInt_ofNat_eq_ofNat]
  unfold BitVec.extractLsb BitVec.extractLsb'
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hprod_lt : a.toBitVec.toNat * b.toBitVec.toNat < 2 ^ 128 := by
    have ha := a.toBitVec.isLt
    have hb := b.toBitVec.isLt
    calc a.toBitVec.toNat * b.toBitVec.toNat
      _ < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hb
      _ = 2 ^ 128 := by decide
  rw [Nat.mod_eq_of_lt hprod_lt, Nat.shiftRight_eq_div_pow]
  have hdiv_lt : (a.toBitVec.toNat * b.toBitVec.toNat) / 2 ^ 64 < 2 ^ 64 := by
    omega
  exact Nat.mod_eq_of_lt hdiv_lt

/-- RV64M instruction encoder/decoder & mnemonic roundtrip across all four architectural
    `mul_op` modes (`MUL`, `MULH`, `MULHSU`, `MULHU`) in `LeanRV64D`. -/
theorem encdec_mul_op_roundtrip (code : BitVec 3)
    (hvalid : encdec_mul_op_backwards_matches code = true)
    (s : SequentialState RegisterType trivialChoiceSource) :
    ((do
        let op ← encdec_mul_op_backwards code
        let m ← mul_mnemonic_forwards op
        let op' ← mul_mnemonic_backwards m
        encdec_mul_op_forwards op').run s) = .ok code s := by
  rcases code with ⟨⟨val, hlt⟩⟩
  have h8 : val = 0 ∨ val = 1 ∨ val = 2 ∨ val = 3 ∨ val = 4 ∨ val = 5 ∨ val = 6 ∨ val = 7 := by omega
  rcases h8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [encdec_mul_op_backwards_matches] <;>
    rfl

/-! ## 4. RV64 Zbc (`CLMUL` / `CLMULH`) Bisimulation against `LeanRV64D.Functions.carryless_mul` -/

private theorem extractLsb'_0_64_xor128 (x y : BitVec 128) :
    BitVec.extractLsb' 0 64 (x ^^^ y) = BitVec.extractLsb' 0 64 x ^^^ BitVec.extractLsb' 0 64 y := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp [hk]

private theorem extractLsb'_64_64_xor128 (x y : BitVec 128) :
    BitVec.extractLsb' 64 64 (x ^^^ y) = BitVec.extractLsb' 64 64 x ^^^ BitVec.extractLsb' 64 64 y := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp [hk]

private theorem uint64_shift_test_eq_sail_access (x : UInt64) (i : Nat) (hi : i < 64) :
    (((x >>> i.toUInt64) &&& 1) == 1) = ((Sail.BitVec.access x.toBitVec i == 1#1) : Bool) := by
  have hi_mod : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
  have h_shr : (x >>> i.toUInt64).toBitVec = x.toBitVec >>> i := by
    change x.toBitVec >>> (i.toUInt64.toBitVec % 64#64) = x.toBitVec >>> i
    have hmodbv : (i.toUInt64.toBitVec % 64#64).toNat = i := by
      simp [hi_mod, Nat.mod_eq_of_lt hi]
    rw [BitVec.ushiftRight_eq', hmodbv]
  have h_lhs : (((x >>> i.toUInt64) &&& 1) == 1) = x.toBitVec.getLsbD i := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq]
    constructor
    · intro h
      have hbv := congrArg (fun u : UInt64 => u.toBitVec.getLsbD 0) h
      simpa [UInt64.toBitVec_and, h_shr, BitVec.getLsbD_ushiftRight, hi] using hbv
    · intro hbit
      apply UInt64.eq_of_toBitVec_eq
      rw [UInt64.toBitVec_and, h_shr]
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      cases k with
      | zero =>
        simpa [BitVec.getLsbD_ushiftRight, hi] using hbit
      | succ k' =>
        have h1 : (1#64).getLsbD (k' + 1) = false := by
          rw [BitVec.getLsbD_ofNat]
          simp [hk, Nat.testBit_succ]
        simp [BitVec.getLsbD_and, h1]
  have h_rhs : ((Sail.BitVec.access x.toBitVec i == 1#1) : Bool) = x.toBitVec.getLsbD i := by
    unfold Sail.BitVec.access
    have hget : x.toBitVec[i]! = x.toBitVec.getLsbD i := by
      simp [hi]
    rw [hget]
    cases x.toBitVec.getLsbD i <;> decide
  rw [h_lhs, h_rhs]

private theorem uint64_shl_eq_extract_lo128 (b : UInt64) (i : Nat) (hi : i < 64) :
    (b <<< i.toUInt64).toBitVec =
      BitVec.extractLsb' 0 64 (zero_extend (m := 128) b.toBitVec <<< (i : Int)) := by
  have hi_mod : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
  have h_shl : (b <<< i.toUInt64).toBitVec = b.toBitVec <<< i := by
    change b.toBitVec <<< (i.toUInt64.toBitVec % 64#64) = b.toBitVec <<< i
    have hmodbv : (i.toUInt64.toBitVec % 64#64).toNat = i := by
      simp [hi_mod, Nat.mod_eq_of_lt hi]
    rw [BitVec.shiftLeft_eq', hmodbv]
  rw [h_shl]
  change b.toBitVec <<< i = BitVec.extractLsb' 0 64 (BitVec.zeroExtend 128 b.toBitVec <<< i)
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb', Nat.zero_add,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases hki : k < i
  · simp [hk, hki]
  · have hsub : k - i < 128 := by omega
    simp [hk, hki, hsub, show k < 128 by omega]

private theorem uint64_shr_64_sub_eq_extract_hi128 (b : UInt64) (i : Nat) (_hi0 : 1 ≤ i) (hi : i < 64) :
    (b >>> (64 - i.toUInt64)).toBitVec =
      BitVec.extractLsb' 64 64 (zero_extend (m := 128) b.toBitVec <<< (i : Int)) := by
  have hsub_u64 : (64 : UInt64) - i.toUInt64 = (64 - i).toUInt64 := by
    apply UInt64.eq_of_toBitVec_eq
    apply BitVec.eq_of_toNat_eq
    simp [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 64 - i < 2 ^ 64 by omega)]
    omega
  have h_shr : (b >>> (64 - i.toUInt64)).toBitVec = b.toBitVec >>> (64 - i) := by
    rw [hsub_u64]
    change b.toBitVec >>> ((64 - i).toUInt64.toBitVec % 64#64) = b.toBitVec >>> (64 - i)
    have hlt : 64 - i < 64 := by omega
    have hmod : (64 - i) % 2 ^ 64 = 64 - i := Nat.mod_eq_of_lt (by omega)
    have hmodbv : ((64 - i).toUInt64.toBitVec % 64#64).toNat = 64 - i := by
      simp [hmod, Nat.mod_eq_of_lt hlt]
    rw [BitVec.ushiftRight_eq', hmodbv]
  rw [h_shr]
  change b.toBitVec >>> (64 - i) = BitVec.extractLsb' 64 64 (BitVec.zeroExtend 128 b.toBitVec <<< i)
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  have hidx : 64 - i + k = 64 + k - i := by omega
  have hsub : 64 + k - i < 128 := by omega
  have hnlt : ¬(64 + k < i) := by omega
  have hlt128 : 64 + k < 128 := by omega
  simp [hk, hidx, hsub, hnlt, hlt128]

/-- Pure recursive characterization of the `[0:63:1]i` `IntRange.forIn'` loop inside
    upstream `LeanRV64D.Functions.carryless_mul` at `k_n = 64`. -/
private def carrylessMulLoop64 (a b : BitVec 64) (i : Nat) (acc : BitVec 128) : BitVec 128 :=
  if _ : i < 64 then
    let acc' :=
      if (Sail.BitVec.access a i == 1#1 : Bool) then
        acc ^^^ (zero_extend (m := 128) b <<< (i : Int))
      else acc
    carrylessMulLoop64 a b (i + 1) acc'
  else acc

private theorem carryless_mul_64_eq_loop (a b : BitVec 64) :
    carryless_mul a b = carrylessMulLoop64 a b 0 0#128 := by
  let r : IntRange := [0:63:1]i
  let f : (i : Int) → i ∈ r → BitVec 128 → Id (ForInStep (BitVec 128)) :=
    fun i _ acc =>
      pure (.yield (if (Sail.BitVec.access a i.toNat == 1#1 : Bool) then
        acc ^^^ (zero_extend (m := 128) b <<< i)
      else acc))
  have hloop : ∀ (k : Nat) (hk : k ≤ 64) (acc : BitVec 128)
      (hs : ((k : Int) - r.start) % r.step = 0),
      IntRange.forIn'.loop (m := Id) r f acc (k : Int) hs = carrylessMulLoop64 a b k acc := by
    intro k hk
    induction hrem : 64 - k generalizing k with
    | zero =>
      have hk64 : k = 64 := by omega
      subst hk64
      intro acc hs
      have hnotmem : ¬((64 : Int) ∈ r) := by
        simp [r, Membership.mem]
      unfold IntRange.forIn'.loop carrylessMulLoop64
      simp [hnotmem]
      rfl
    | succ rem ih =>
      have hlt : k < 64 := by omega
      intro acc hs
      have hmem : (k : Int) ∈ r := by
        simp [r, Membership.mem]
        omega
      unfold IntRange.forIn'.loop carrylessMulLoop64
      simp only [hmem, hlt, dite_true]
      dsimp [f, r, Id.instMonad, Bind.bind, Pure.pure]
      have hcast : (k : Int) + 1 = ((k + 1 : Nat) : Int) := rfl
      simp only [hcast]
      exact ih (k + 1) (by omega) (by omega) _ _
  unfold carryless_mul
  change Id.run (do
    let mut loop_vars : BitVec 128 := 0#128
    for i in r do
      loop_vars := if (Sail.BitVec.access a i.toNat == 1#1 : Bool) then
        loop_vars ^^^ (zero_extend (m := 128) b <<< i)
      else loop_vars
    pure loop_vars) = carrylessMulLoop64 a b 0 0#128
  exact hloop 0 (by omega) 0#128 (by simp [r])

private theorem clmul64_go_eq_carrylessMulLoop64_lo (b a : UInt64) :
    ∀ (i : Nat) (_hi : i ≤ 64) (acc : BitVec 128),
      clmul64.go b a i (UInt64.ofBitVec (BitVec.extractLsb' 0 64 acc)) =
        UInt64.ofBitVec (BitVec.extractLsb' 0 64 (carrylessMulLoop64 a.toBitVec b.toBitVec i acc)) := by
  intro i hi
  induction hrem : 64 - i generalizing i with
  | zero =>
    have hi64 : i = 64 := by omega
    subst hi64
    intro acc
    unfold clmul64.go carrylessMulLoop64
    simp
  | succ rem ih =>
    have hlt : i < 64 := by omega
    intro acc
    unfold clmul64.go carrylessMulLoop64
    simp only [hlt, dite_true]
    rw [uint64_shift_test_eq_sail_access a i hlt]
    have hstep :
        (if (Sail.BitVec.access a.toBitVec i == 1#1 : Bool) then
          UInt64.ofBitVec (BitVec.extractLsb' 0 64 acc) ^^^ (b <<< i.toUInt64)
         else UInt64.ofBitVec (BitVec.extractLsb' 0 64 acc)) =
        UInt64.ofBitVec (BitVec.extractLsb' 0 64
          (if (Sail.BitVec.access a.toBitVec i == 1#1 : Bool) then
            acc ^^^ (zero_extend (m := 128) b.toBitVec <<< (i : Int))
           else acc)) := by
      cases hbit : (Sail.BitVec.access a.toBitVec i == 1#1 : Bool)
      · simp
      · simp only [↓reduceIte]
        apply UInt64.eq_of_toBitVec_eq
        rw [UInt64.toBitVec_xor, UInt64.toBitVec_ofBitVec, UInt64.toBitVec_ofBitVec,
          uint64_shl_eq_extract_lo128 b i hlt, extractLsb'_0_64_xor128]
    rw [hstep]
    exact ih (i + 1) (by omega) (by omega) _

private theorem clmul64Hi_go_eq_carrylessMulLoop64_hi (b a : UInt64) :
    ∀ (i : Nat) (_hi0 : 1 ≤ i) (_hi : i ≤ 64) (acc : BitVec 128),
      clmul64Hi.go b a i (UInt64.ofBitVec (BitVec.extractLsb' 64 64 acc)) =
        UInt64.ofBitVec (BitVec.extractLsb' 64 64 (carrylessMulLoop64 a.toBitVec b.toBitVec i acc)) := by
  intro i hi0 hi
  induction hrem : 64 - i generalizing i with
  | zero =>
    have hi64 : i = 64 := by omega
    subst hi64
    intro acc
    unfold clmul64Hi.go carrylessMulLoop64
    simp
  | succ rem ih =>
    have hlt : i < 64 := by omega
    intro acc
    unfold clmul64Hi.go carrylessMulLoop64
    simp only [hlt, dite_true]
    rw [uint64_shift_test_eq_sail_access a i hlt]
    have hstep :
        (if (Sail.BitVec.access a.toBitVec i == 1#1 : Bool) then
          UInt64.ofBitVec (BitVec.extractLsb' 64 64 acc) ^^^ (b >>> (64 - i.toUInt64))
         else UInt64.ofBitVec (BitVec.extractLsb' 64 64 acc)) =
        UInt64.ofBitVec (BitVec.extractLsb' 64 64
          (if (Sail.BitVec.access a.toBitVec i == 1#1 : Bool) then
            acc ^^^ (zero_extend (m := 128) b.toBitVec <<< (i : Int))
           else acc)) := by
      cases hbit : (Sail.BitVec.access a.toBitVec i == 1#1 : Bool)
      · simp
      · simp only [↓reduceIte]
        apply UInt64.eq_of_toBitVec_eq
        rw [UInt64.toBitVec_xor, UInt64.toBitVec_ofBitVec, UInt64.toBitVec_ofBitVec,
          uint64_shr_64_sub_eq_extract_hi128 b i hi0 hlt, extractLsb'_64_64_xor128]
    rw [hstep]
    exact ih (i + 1) (by omega) (by omega) (by omega) _

/-- `LeanNative.IR.clmul64 b a` matches the low 64-bit slice (`execute_CLMUL`) of upstream
    `LeanRV64D.Functions.carryless_mul a.toBitVec b.toBitVec`. -/
theorem clmul64_eq_sail_carryless_mul_lo (a b : UInt64) :
    (clmul64 b a).toBitVec =
      Sail.BitVec.extractLsb (carryless_mul a.toBitVec b.toBitVec) 63 0 := by
  have h0 : (0 : UInt64) = UInt64.ofBitVec (BitVec.extractLsb' 0 64 0#128) := by decide
  have h := clmul64_go_eq_carrylessMulLoop64_lo b a 0 (by omega) 0#128
  unfold clmul64 Sail.BitVec.extractLsb BitVec.extractLsb
  rw [carryless_mul_64_eq_loop, h0, h, UInt64.toBitVec_ofBitVec]

/-- `LeanNative.IR.clmul64Hi b a` matches the high 64-bit slice (`execute_CLMULH`) of upstream
    `LeanRV64D.Functions.carryless_mul a.toBitVec b.toBitVec`. -/
theorem clmul64Hi_eq_sail_carryless_mul_hi (a b : UInt64) :
    (clmul64Hi b a).toBitVec =
      Sail.BitVec.extractLsb (carryless_mul a.toBitVec b.toBitVec) 127 64 := by
  unfold clmul64Hi Sail.BitVec.extractLsb BitVec.extractLsb
  rw [carryless_mul_64_eq_loop]
  unfold carrylessMulLoop64
  simp only [show 0 < 64 by omega, dite_true, Nat.zero_add]
  let acc1 : BitVec 128 :=
    if (Sail.BitVec.access a.toBitVec 0 == 1#1 : Bool) then
      0#128 ^^^ (zero_extend (m := 128) b.toBitVec <<< (0 : Int))
    else 0#128
  have hacc1_hi : BitVec.extractLsb' 64 64 acc1 = 0#64 := by
    dsimp [acc1]
    split
    · change BitVec.extractLsb' 64 64 (0#128 ^^^ (BitVec.zeroExtend 128 b.toBitVec <<< (0 : Nat))) = 0#64
      rw [BitVec.shiftLeft_zero]
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_setWidth]
      have hlt : 64 + k < 128 := by omega
      simp [hk, hlt]
    · apply BitVec.eq_of_getLsbD_eq
      intro k hk
      simp [hk]
  have h0 : (0 : UInt64) = UInt64.ofBitVec (BitVec.extractLsb' 64 64 acc1) := by
    rw [hacc1_hi]; rfl
  have h := clmul64Hi_go_eq_carrylessMulLoop64_hi b a 1 (by omega) (by omega) acc1
  change (clmul64Hi.go b a 1 0).toBitVec =
    BitVec.extractLsb' 64 64 (carrylessMulLoop64 a.toBitVec b.toBitVec 1 acc1)
  rw [h0, h, UInt64.toBitVec_ofBitVec]

/-- Full 128-bit reconstruction: concatenating `(clmul64Hi b a).toBitVec` and `(clmul64 b a).toBitVec`
    via `(· +++ ·)` equals the complete 128-bit polynomial product
    `carryless_mul a.toBitVec b.toBitVec`. -/
theorem clmul64_pair_eq_sail_carryless_mul (a b : UInt64) :
    (clmul64Hi b a).toBitVec +++ (clmul64 b a).toBitVec =
      carryless_mul a.toBitVec b.toBitVec := by
  rw [clmul64_eq_sail_carryless_mul_lo, clmul64Hi_eq_sail_carryless_mul_hi]
  unfold Sail.BitVec.extractLsb BitVec.extractLsb
  generalize (carryless_mul a.toBitVec b.toBitVec : BitVec 128) = p
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_append]
  by_cases hk64 : k < 64
  · simp [hk64]
  · have hsub : 64 + (k - 64) = k := by omega
    simp [hk64, show k - 64 < 64 by omega, hsub]

end SailRiscvBridge
