import SailRiscvBridge.MirroredModel
import Sail
import LeanRV64D.Defs
import LeanRV64D.Prelude
import LeanRV64D.Xlen
import LeanRV64D.Arithmetic
import LeanRV64D.MextInsts
import LeanRV64D.Regs
import LeanRV64D.PcAccess

/-!
# Stage 3E / Milestone `M5` RV64 Formal Bisimulation against `opencompl/sail-riscv-lean`

Bridges `TurboLean.PolicyGates` (`riscvDivU64Spec`, `riscvRemU64Spec`), RV64M 64-bit & 32-bit
word multiplication/division/remainder (`MUL`, `MULH`, `MULHSU`, `MULHU`, `MULW`, `DIV`, `DIVU`,
`REM`, `REMU`, `DIVW`, `DIVUW`, `REMW`, `REMUW`), `LeanNative.IR` Zbc carryless multiplication
(`clmul64`, `clmul64Hi`, `CLMULR`, and $\mathbb{F}_2[x]$ commutativity), the RV64I base & `*W`
ALU/shift/`LUI`/`AUIPC`/branch/`JAL`/`JALR` fragment, and RV64 Zba/Zbb/Zbs bit-manipulation
instructions directly against upstream `opencompl/sail-riscv-lean` (`Lean_RV64D` + `Sail`) on
`leanprover/lean4:v4.29.0`, avoiding monolithic `LeanRV64D.InstsEnd` / `LeanRV64D.Step` /
`LeanRV64D.ZicsrInsts` / `LeanRV64D.RiscvExtras` imports so incremental elaboration stays
lightweight and axiom-clean.
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

/-! ## 5. Signed RV64M `DIV` / `REM` & `MULH` / `MULHSU` Bisimulation -/

/-- Pure `TurboLean`-side architectural RV64M signed division (`DIV`) specification over `BitVec 64`:
    division by `0` returns all-ones (`-1`), signed overflow `INT64_MIN / -1` (`BitVec.intMin 64 / -1`)
    returns `INT64_MIN`, and all other cases compute two's-complement truncating `BitVec.sdiv`. -/
def riscvDivS64Spec (lhs rhs : BitVec 64) : BitVec 64 :=
  if rhs == 0#64 then
    BitVec.allOnes 64
  else if lhs == BitVec.intMin 64 && rhs == BitVec.allOnes 64 then
    BitVec.intMin 64
  else
    BitVec.sdiv lhs rhs

/-- Pure `TurboLean`-side architectural RV64M signed remainder (`REM`) specification over `BitVec 64`:
    division by `0` returns `lhs`, signed overflow `INT64_MIN % -1` returns `0`, and all other cases
    compute two's-complement truncating `BitVec.srem`. -/
def riscvRemS64Spec (lhs rhs : BitVec 64) : BitVec 64 :=
  if rhs == 0#64 then
    lhs
  else if lhs == BitVec.intMin 64 && rhs == BitVec.allOnes 64 then
    0#64
  else
    BitVec.srem lhs rhs

/-- Exact upstream Sail `execute_DIV` (`is_unsigned = false`) functional core from
    `LeanRV64D/InstsEnd.lean` (lines 71434–71454). -/
def sailDivS64Core (rs1_bits rs2_bits : BitVec 64) : BitVec 64 :=
  let rs1_int : Int := BitVec.toInt rs1_bits
  let rs2_int : Int := BitVec.toInt rs2_bits
  let quotient : Int := if (rs2_int == 0 : Bool) then Neg.neg 1 else Int.tdiv rs1_int rs2_int
  let quotient : Int :=
    if (((LeanRV64D.Functions.not false) && (quotient ≥b (2 ^i (Functions.xlen -i 1)))) : Bool) then
      Neg.neg (2 ^i (Functions.xlen -i 1))
    else
      quotient
  to_bits_truncate (l := 64) quotient

/-- Exact upstream Sail `execute_REM` (`is_unsigned = false`) functional core from
    `LeanRV64D/InstsEnd.lean` (lines 68037–68053). -/
def sailRemS64Core (rs1_bits rs2_bits : BitVec 64) : BitVec 64 :=
  let rs1_int : Int := BitVec.toInt rs1_bits
  let rs2_int : Int := BitVec.toInt rs2_bits
  let remainder : Int := if (rs2_int == 0 : Bool) then rs1_int else Int.tmod rs1_int rs2_int
  to_bits_truncate (l := 64) remainder

private theorem toInt_eq_zero_iff (x : BitVec 64) : x.toInt = 0 ↔ x = 0#64 := by
  constructor
  · intro h
    exact BitVec.eq_of_toInt_eq (by simpa using h)
  · rintro rfl
    rfl

private theorem ofInt_neg_one_64 : BitVec.ofInt 64 (-1) = BitVec.allOnes 64 := by
  decide

private theorem neg_one_eq_allOnes_64 : (-1#64 : BitVec 64) = BitVec.allOnes 64 := by
  decide

private theorem tdiv_lt_two_pow_63_of_not_ovf (x y : BitVec 64)
    (hovf : ¬(x = BitVec.intMin 64 ∧ y = BitVec.allOnes 64)) :
    ¬((2 ^ 63 : Int) ≤ Int.tdiv x.toInt y.toInt) := by
  have hor : x ≠ BitVec.intMin 64 ∨ y ≠ -1#64 := by
    rw [neg_one_eq_allOnes_64]
    by_cases hx : x = BitVec.intMin 64
    · exact Or.inr (fun hy => hovf ⟨hx, hy⟩)
    · exact Or.inl hx
  rw [← BitVec.toInt_sdiv_of_ne_or_ne x y hor]
  have hlt : (x.sdiv y).toInt < 2 ^ (64 - 1) := @BitVec.toInt_lt 64 (x.sdiv y)
  have hp : (2 ^ (64 - 1) : Int) = (2 ^ 63 : Int) := by decide
  omega

/-- Signed RV64M `DIV` bisimulation: `riscvDivS64Spec` matches upstream Sail `execute_DIV`
    (`is_unsigned = false`) across all `BitVec 64` inputs, including division-by-zero (`-1`)
    and `INT64_MIN / -1` overflow (`INT64_MIN`). -/
theorem riscvDivS64Spec_bisim_sail (lhs rhs : BitVec 64) :
    riscvDivS64Spec lhs rhs = sailDivS64Core lhs rhs := by
  unfold riscvDivS64Spec sailDivS64Core
  rw [to_bits_truncate_eq_ofInt]
  have hxlen : (2 ^i (Functions.xlen -i 1) : Int) = (2 ^ 63 : Int) := by decide
  have hnot : LeanRV64D.Functions.not false = true := rfl
  simp only [hxlen, hnot, Bool.true_and]
  by_cases hr : rhs = 0#64
  · subst hr
    have hr0 : ((0#64).toInt == 0) = true := rfl
    have hb0 : (0#64 == 0#64) = true := rfl
    rw [hr0, hb0]
    simp only [↓reduceIte]
    decide
  · have hb_ne : (rhs == 0#64) = false := beq_false_of_ne hr
    have hr_int_ne : rhs.toInt ≠ 0 := fun h => hr ((toInt_eq_zero_iff rhs).mp h)
    have hr_int_beq : ((rhs.toInt == 0) : Bool) = false := beq_false_of_ne hr_int_ne
    rw [hb_ne, hr_int_beq]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hovf : lhs = BitVec.intMin 64 ∧ rhs = BitVec.allOnes 64
    · rcases hovf with ⟨rfl, rfl⟩
      decide
    · have hcond_false : (lhs == BitVec.intMin 64 && rhs == BitVec.allOnes 64) = false := by
        cases h1 : (lhs == BitVec.intMin 64) <;> cases h2 : (rhs == BitVec.allOnes 64) <;> simp_all
      have hge_false : (decide (Int.tdiv lhs.toInt rhs.toInt ≥ (2 ^ 63 : Int))) = false :=
        decide_eq_false (tdiv_lt_two_pow_63_of_not_ovf lhs rhs hovf)
      rw [hcond_false, hge_false]
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply BitVec.eq_of_toInt_eq
      rw [BitVec.toInt_sdiv, BitVec.toInt_ofInt]

/-- Signed RV64M `REM` bisimulation: `riscvRemS64Spec` matches upstream Sail `execute_REM`
    (`is_unsigned = false`) across all `BitVec 64` inputs, including division-by-zero (`lhs`)
    and `INT64_MIN % -1` overflow (`0`). -/
theorem riscvRemS64Spec_bisim_sail (lhs rhs : BitVec 64) :
    riscvRemS64Spec lhs rhs = sailRemS64Core lhs rhs := by
  unfold riscvRemS64Spec sailRemS64Core
  rw [to_bits_truncate_eq_ofInt]
  by_cases hr : rhs = 0#64
  · subst hr
    have hr0 : ((0#64).toInt == 0) = true := rfl
    have hb0 : (0#64 == 0#64) = true := rfl
    rw [hr0, hb0]
    simp only [↓reduceIte, BitVec.ofInt_toInt]
  · have hb_ne : (rhs == 0#64) = false := beq_false_of_ne hr
    have hr_int_ne : rhs.toInt ≠ 0 := fun h => hr ((toInt_eq_zero_iff rhs).mp h)
    have hr_int_beq : ((rhs.toInt == 0) : Bool) = false := beq_false_of_ne hr_int_ne
    rw [hb_ne, hr_int_beq]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hovf : lhs = BitVec.intMin 64 ∧ rhs = BitVec.allOnes 64
    · rcases hovf with ⟨rfl, rfl⟩
      decide
    · have hcond_false : (lhs == BitVec.intMin 64 && rhs == BitVec.allOnes 64) = false := by
        cases h1 : (lhs == BitVec.intMin 64) <;> cases h2 : (rhs == BitVec.allOnes 64) <;> simp_all
      rw [hcond_false]
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply BitVec.eq_of_toInt_eq
      rw [BitVec.toInt_srem, BitVec.toInt_ofInt, ← BitVec.toInt_srem, BitVec.toInt_bmod_cancel]

/-- Signed RV64M division-remainder wrapping Euclidean identity across all 64-bit inputs
    (including `rhs = 0`, where `(-1) * 0 + lhs = lhs`, and `INT64_MIN / -1`, where
    `INT64_MIN * (-1) + 0 = -INT64_MIN = INT64_MIN` modulo `2^64`). -/
theorem riscvDivRemS64Spec_euclidean (lhs rhs : BitVec 64) :
    riscvDivS64Spec lhs rhs * rhs + riscvRemS64Spec lhs rhs = lhs := by
  rw [riscvDivS64Spec_bisim_sail, riscvRemS64Spec_bisim_sail]
  unfold sailDivS64Core sailRemS64Core
  rw [to_bits_truncate_eq_ofInt, to_bits_truncate_eq_ofInt]
  have hxlen : (2 ^i (Functions.xlen -i 1) : Int) = (2 ^ 63 : Int) := by decide
  have hnot : LeanRV64D.Functions.not false = true := rfl
  simp only [hxlen, hnot, Bool.true_and]
  by_cases hr : rhs = 0#64
  · subst hr
    have hr0 : ((0#64).toInt == 0) = true := rfl
    rw [hr0]
    simp only [↓reduceIte, BitVec.mul_zero, BitVec.zero_add, BitVec.ofInt_toInt]
  · have hr_int_ne : rhs.toInt ≠ 0 := fun h => hr ((toInt_eq_zero_iff rhs).mp h)
    have hr_int_beq : ((rhs.toInt == 0) : Bool) = false := beq_false_of_ne hr_int_ne
    rw [hr_int_beq]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hovf : lhs = BitVec.intMin 64 ∧ rhs = BitVec.allOnes 64
    · rcases hovf with ⟨rfl, rfl⟩
      decide
    · have hge_false : (decide (Int.tdiv lhs.toInt rhs.toInt ≥ (2 ^ 63 : Int))) = false :=
        decide_eq_false (tdiv_lt_two_pow_63_of_not_ovf lhs rhs hovf)
      rw [hge_false]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have h_rhs : rhs = BitVec.ofInt 64 rhs.toInt := BitVec.ofInt_toInt.symm
      conv => lhs; arg 1; arg 2; rw [h_rhs]
      rw [← BitVec.ofInt_mul, ← BitVec.ofInt_add, Int.mul_comm, Int.mul_tdiv_add_tmod, BitVec.ofInt_toInt]

/-- Pure `TurboLean`-side architectural RV64M `MULH` specification (`Signed × Signed`, upper 64 bits
    of the 128-bit sign-extended product). -/
def riscvMulhSpec (a b : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb 127 64 (a.signExtend 128 * b.signExtend 128)

/-- Pure `TurboLean`-side architectural RV64M `MULHSU` specification (`Signed × Unsigned`, upper 64 bits
    of the 128-bit mixed-sign product). -/
def riscvMulhsuSpec (a b : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb 127 64 (a.signExtend 128 * b.zeroExtend 128)

/-- Upstream `LeanRV64D.Functions.mult_to_bits_half` for `MULH` (`Signed`, `Signed`, `High`)
    equals `riscvMulhSpec` (`BitVec.extractLsb 127 64 (a.signExtend 128 * b.signExtend 128)`)
    and has signed value `(a.toInt * b.toInt) / 2^64` (Euclidean floor division). -/
theorem mult_to_bits_half_high_signed_eq_mulh (a b : BitVec 64) :
    mult_to_bits_half (l := 64) .Signed .Signed a b .High = riscvMulhSpec a b := by
  unfold mult_to_bits_half riscvMulhSpec Sail.BitVec.extractLsb
  change BitVec.extractLsb 127 64 (to_bits_truncate (l := 128) (a.toInt * b.toInt)) =
    BitVec.extractLsb 127 64 (a.signExtend 128 * b.signExtend 128)
  rw [to_bits_truncate_eq_ofInt]
  congr 1
  have ha : BitVec.ofInt 128 a.toInt = a.signExtend 128 := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_signExtend_of_le (by omega), BitVec.toInt_ofInt_eq_self (by omega)]
    · have := @BitVec.le_toInt 64 a; omega
    · have := @BitVec.toInt_lt 64 a; omega
  have hb : BitVec.ofInt 128 b.toInt = b.signExtend 128 := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_signExtend_of_le (by omega), BitVec.toInt_ofInt_eq_self (by omega)]
    · have := @BitVec.le_toInt 64 b; omega
    · have := @BitVec.toInt_lt 64 b; omega
  rw [BitVec.ofInt_mul, ha, hb]

/-- Upstream `LeanRV64D.Functions.mult_to_bits_half` for `MULHSU` (`Signed`, `Unsigned`, `High`)
    equals `riscvMulhsuSpec` (`BitVec.extractLsb 127 64 (a.signExtend 128 * b.zeroExtend 128)`). -/
theorem mult_to_bits_half_high_signed_unsigned_eq_mulhsu (a b : BitVec 64) :
    mult_to_bits_half (l := 64) .Signed .Unsigned a b .High = riscvMulhsuSpec a b := by
  unfold mult_to_bits_half riscvMulhsuSpec Sail.BitVec.extractLsb Sail.BitVec.toNatInt
  change BitVec.extractLsb 127 64 (to_bits_truncate (l := 128) (a.toInt * Int.ofNat b.toNat)) =
    BitVec.extractLsb 127 64 (a.signExtend 128 * b.zeroExtend 128)
  rw [to_bits_truncate_eq_ofInt]
  congr 1
  have ha : BitVec.ofInt 128 a.toInt = a.signExtend 128 := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_signExtend_of_le (by omega), BitVec.toInt_ofInt_eq_self (by omega)]
    · have := @BitVec.le_toInt 64 a; omega
    · have := @BitVec.toInt_lt 64 a; omega
  have hb : BitVec.ofInt 128 (Int.ofNat b.toNat) = b.zeroExtend 128 := by
    rw [ofInt_ofNat_eq_ofNat]
    apply BitVec.eq_of_toNat_eq
    have hlt : b.toNat < 2 ^ 128 := by
      have := b.isLt; omega
    simp [Nat.mod_eq_of_lt hlt]
  rw [BitVec.ofInt_mul, ha, hb]

/-! ## 6. RV64 Zbc `CLMULR` & Polynomial Carryless Commutativity -/

/-- Pure `TurboLean`-side architectural RV64 Zbc `CLMULR` specification over `UInt64`,
    expressed directly from `LeanNative.IR.clmul64Hi` and `LeanNative.IR.clmul64`
    (bits `[126:63]` of the 128-bit polynomial product). -/
def clmul64RSpec (rs1 rs2 : UInt64) : UInt64 :=
  (clmul64Hi rs2 rs1 <<< 1) ||| (clmul64 rs2 rs1 >>> 63)

private theorem extractLsb'_63_64_xor128 (x y : BitVec 128) :
    BitVec.extractLsb' 63 64 (x ^^^ y) = BitVec.extractLsb' 63 64 x ^^^ BitVec.extractLsb' 63 64 y := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp [hk]

private def carrylessMulrLoop64 (a b : BitVec 64) (i : Nat) (acc : BitVec 64) : BitVec 64 :=
  if _ : i < 64 then
    let acc' :=
      if (Sail.BitVec.access a i == 1#1 : Bool) then
        acc ^^^ (b >>> ((64 : Int) -i (i : Int) -i 1))
      else acc
    carrylessMulrLoop64 a b (i + 1) acc'
  else acc

private theorem carryless_mulr_64_eq_loop (a b : BitVec 64) :
    carryless_mulr a b = carrylessMulrLoop64 a b 0 0#64 := by
  let r : IntRange := [0:63:1]i
  let f : (i : Int) → i ∈ r → BitVec 64 → Id (ForInStep (BitVec 64)) :=
    fun i _ acc =>
      pure (.yield (if (Sail.BitVec.access a i.toNat == 1#1 : Bool) then
        acc ^^^ (b >>> ((64 : Int) -i i -i 1))
      else acc))
  have hloop : ∀ (k : Nat) (hk : k ≤ 64) (acc : BitVec 64)
      (hs : ((k : Int) - r.start) % r.step = 0),
      IntRange.forIn'.loop (m := Id) r f acc (k : Int) hs = carrylessMulrLoop64 a b k acc := by
    intro k hk
    induction hrem : 64 - k generalizing k with
    | zero =>
      have hk64 : k = 64 := by omega
      subst hk64
      intro acc hs
      have hnotmem : ¬((64 : Int) ∈ r) := by
        simp [r, Membership.mem]
      unfold IntRange.forIn'.loop carrylessMulrLoop64
      simp [hnotmem]
      rfl
    | succ rem ih =>
      have hlt : k < 64 := by omega
      intro acc hs
      have hmem : (k : Int) ∈ r := by
        simp [r, Membership.mem]
        omega
      unfold IntRange.forIn'.loop carrylessMulrLoop64
      simp only [hmem, hlt, dite_true]
      dsimp [f, r, Id.instMonad, Bind.bind, Pure.pure]
      have hcast : (k : Int) + 1 = ((k + 1 : Nat) : Int) := rfl
      simp only [hcast]
      exact ih (k + 1) (by omega) (by omega) _ _
  unfold carryless_mulr
  change Id.run (do
    let mut loop_vars : BitVec 64 := 0#64
    for i in r do
      loop_vars := if (Sail.BitVec.access a i.toNat == 1#1 : Bool) then
        loop_vars ^^^ (b >>> ((64 : Int) -i i -i 1))
      else loop_vars
    pure loop_vars) = carrylessMulrLoop64 a b 0 0#64
  exact hloop 0 (by omega) 0#64 (by simp [r])

private theorem shr_63_sub_eq_extract_63_128 (b : BitVec 64) (i : Nat) (hi : i < 64) :
    (b >>> ((64 : Int) -i (i : Int) -i 1)) =
      BitVec.extractLsb' 63 64 (zero_extend (m := 128) b <<< (i : Int)) := by
  have hshift_int : ((64 : Int) -i (i : Int) -i 1) = Int.ofNat (63 - i) := by
    change (64 : Int) - (i : Int) - 1 = ((63 - i : Nat) : Int)
    omega
  rw [hshift_int]
  have hshr_int : (b >>> Int.ofNat (63 - i)) = b >>> (63 - i) := by
    change b <<< (-Int.ofNat (63 - i)) = b >>> (63 - i)
    cases h63 : 63 - i with
    | zero =>
      change b <<< (0 : Int) = b >>> 0
      change b <<< (0 : Nat) = b >>> 0
      simp
    | succ m =>
      change b <<< Int.negSucc m = b >>> (m + 1)
      rfl
  rw [hshr_int]
  change b >>> (63 - i) = BitVec.extractLsb' 63 64 (BitVec.zeroExtend 128 b <<< i)
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  have hidx : 63 - i + k = 63 + k - i := by omega
  have hsub : 63 + k - i < 128 := by omega
  have hnlt : ¬(63 + k < i) := by omega
  have hlt128 : 63 + k < 128 := by omega
  simp [hk, hidx, hsub, hnlt, hlt128]

private theorem carrylessMulrLoop64_eq_extract_carrylessMulLoop64 (a b : BitVec 64) :
    ∀ (i : Nat) (_hi : i ≤ 64) (acc : BitVec 128),
      carrylessMulrLoop64 a b i (BitVec.extractLsb' 63 64 acc) =
        BitVec.extractLsb' 63 64 (carrylessMulLoop64 a b i acc) := by
  intro i hi
  induction hrem : 64 - i generalizing i with
  | zero =>
    have hi64 : i = 64 := by omega
    subst hi64
    intro acc
    unfold carrylessMulrLoop64 carrylessMulLoop64
    simp
  | succ rem ih =>
    have hlt : i < 64 := by omega
    intro acc
    unfold carrylessMulrLoop64 carrylessMulLoop64
    simp only [hlt, dite_true]
    have hstep :
        (if (Sail.BitVec.access a i == 1#1 : Bool) then
          BitVec.extractLsb' 63 64 acc ^^^ (b >>> ((64 : Int) -i (i : Int) -i 1))
         else BitVec.extractLsb' 63 64 acc) =
        BitVec.extractLsb' 63 64
          (if (Sail.BitVec.access a i == 1#1 : Bool) then
            acc ^^^ (zero_extend (m := 128) b <<< (i : Int))
           else acc) := by
      cases (Sail.BitVec.access a i == 1#1 : Bool)
      · simp
      · simp only [↓reduceIte, shr_63_sub_eq_extract_63_128 b i hlt, extractLsb'_63_64_xor128]
    rw [hstep]
    exact ih (i + 1) (by omega) (by omega) _

/-- Upstream `LeanRV64D.Functions.carryless_mulr` (`execute_CLMULR`) is identically bits `[126:63]`
    of the 128-bit polynomial product `carryless_mul a b`. -/
theorem sail_carryless_mulr_eq_extract_carryless_mul (a b : BitVec 64) :
    carryless_mulr a b = Sail.BitVec.extractLsb (carryless_mul a b) 126 63 := by
  have h0 : (0#64 : BitVec 64) = BitVec.extractLsb' 63 64 0#128 := by decide
  unfold Sail.BitVec.extractLsb BitVec.extractLsb
  rw [carryless_mulr_64_eq_loop, carryless_mul_64_eq_loop, h0]
  exact carrylessMulrLoop64_eq_extract_carrylessMulLoop64 a b 0 (by omega) 0#128

/-- `clmul64RSpec rs1 rs2` (`(clmul64Hi rs2 rs1 <<< 1) ||| (clmul64 rs2 rs1 >>> 63)`) matches
    upstream Sail `execute_CLMULR` (`carryless_mulr rs1.toBitVec rs2.toBitVec`). -/
theorem clmul64RSpec_bisim_sail (rs1 rs2 : UInt64) :
    (clmul64RSpec rs1 rs2).toBitVec = carryless_mulr rs1.toBitVec rs2.toBitVec := by
  rw [sail_carryless_mulr_eq_extract_carryless_mul, ← clmul64_pair_eq_sail_carryless_mul]
  unfold clmul64RSpec Sail.BitVec.extractLsb BitVec.extractLsb
  have hshl : (clmul64Hi rs2 rs1 <<< 1).toBitVec = (clmul64Hi rs2 rs1).toBitVec <<< 1 := by
    change (clmul64Hi rs2 rs1).toBitVec <<< ((1 : UInt64).toBitVec % 64#64) =
      (clmul64Hi rs2 rs1).toBitVec <<< 1
    rw [BitVec.shiftLeft_eq']
    rfl
  have hshr : (clmul64 rs2 rs1 >>> 63).toBitVec = (clmul64 rs2 rs1).toBitVec >>> 63 := by
    change (clmul64 rs2 rs1).toBitVec >>> ((63 : UInt64).toBitVec % 64#64) =
      (clmul64 rs2 rs1).toBitVec >>> 63
    rw [BitVec.ushiftRight_eq']
    rfl
  rw [UInt64.toBitVec_or, hshl, hshr]
  generalize (clmul64Hi rs2 rs1).toBitVec = hi
  generalize (clmul64 rs2 rs1).toBitVec = lo
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  by_cases hk0 : k = 0
  · subst hk0
    simp
  · have hk1 : ¬(k < 1) := by omega
    have hlo_gt : ¬(63 + k < 64) := by omega
    have hsub : 63 + k - 64 = k - 1 := by omega
    have hlo_zero : lo.getLsbD (63 + k) = false := BitVec.getLsbD_of_ge lo (63 + k) (by omega)
    simp [hk, hk1, hlo_zero, hlo_gt, hsub, show k - 1 < 64 by omega]

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

private theorem sail_access_eq_getLsbD (x : BitVec 64) (i : Nat) (hi : i < 64) :
    (Sail.BitVec.access x i == 1#1 : Bool) = x.getLsbD i := by
  unfold Sail.BitVec.access
  have hget : x[i]! = x.getLsbD i := by simp [hi]
  rw [hget]
  cases x.getLsbD i <;> decide

private theorem carrylessMulLoop64_getLsbD (a b : BitVec 64) (k : Nat) (hk : k < 128) :
    ∀ (i : Nat) (_hi : i ≤ 64) (acc : BitVec 128),
      (carrylessMulLoop64 a b i acc).getLsbD k =
        xor (acc.getLsbD k)
          (gf2PrefixFold (64 - i) (fun d =>
            a.getLsbD (i + d) && (!decide (k < i + d) && b.getLsbD (k - (i + d))))) := by
  intro i hi
  induction hrem : 64 - i generalizing i with
  | zero =>
    have hi64 : i = 64 := by omega
    subst hi64
    intro acc
    unfold carrylessMulLoop64
    simp [gf2PrefixFold]
  | succ rem ih =>
    have hlt : i < 64 := by omega
    intro acc
    unfold carrylessMulLoop64
    simp only [hlt, dite_true]
    rw [sail_access_eq_getLsbD a i hlt]
    have hnext := ih (i + 1) (by omega) (by omega)
      (if a.getLsbD i = true then acc ^^^ (zero_extend (m := 128) b <<< (i : Int)) else acc)
    rw [hnext]
    have hterm :
        (if a.getLsbD i = true then acc ^^^ (zero_extend (m := 128) b <<< (i : Int)) else acc).getLsbD k =
          xor (acc.getLsbD k) (a.getLsbD i && (!decide (k < i) && b.getLsbD (k - i))) := by
      have hshl : (zero_extend (m := 128) b <<< (i : Int)).getLsbD k =
          (!decide (k < i) && b.getLsbD (k - i)) := by
        change (BitVec.zeroExtend 128 b <<< i).getLsbD k = (!decide (k < i) && b.getLsbD (k - i))
        rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
        by_cases hki : k < i
        · simp [hk, hki]
        · by_cases hkb : k - i < 64
          · simp [hk, hki, hkb, show k - i < 128 by omega]
          · have hb0 : b.getLsbD (k - i) = false := BitVec.getLsbD_of_ge b (k - i) (by omega)
            simp [hk, hki, hb0, show k - i < 128 by omega]
      cases ha : a.getLsbD i
      · simp
      · simp [BitVec.getLsbD_xor, hshl]
    rw [hterm, Bool.xor_assoc]
    congr 1
    have hcong : gf2PrefixFold rem (fun d =>
        a.getLsbD (i + 1 + d) && (!decide (k < i + 1 + d) && b.getLsbD (k - (i + 1 + d)))) =
      gf2PrefixFold rem (fun d =>
        a.getLsbD (i + (d + 1)) && (!decide (k < i + (d + 1)) && b.getLsbD (k - (i + (d + 1))))) :=
      gf2PrefixFold_congr (fun d _ => by
        have h1 : i + 1 + d = i + (d + 1) := by omega
        rw [h1])
    rw [hcong]
    simpa [Nat.add_zero] using
      gf2PrefixFold_shift rem (fun d =>
        a.getLsbD (i + d) && (!decide (k < i + d) && b.getLsbD (k - (i + d))))

/-- Polynomial multiplication over $\mathbb{F}_2[x]$ (`LeanRV64D.Functions.carryless_mul`)
    is commutative across all 64-bit operands. -/
theorem sail_carryless_mul_comm (a b : BitVec 64) :
    carryless_mul a b = carryless_mul b a := by
  rw [carryless_mul_64_eq_loop, carryless_mul_64_eq_loop]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [carrylessMulLoop64_getLsbD a b k hk 0 (by omega) 0#128,
    carrylessMulLoop64_getLsbD b a k hk 0 (by omega) 0#128]
  simp only [BitVec.getLsbD_zero, Bool.false_bne, Nat.sub_zero, Nat.zero_add]
  let m := min 64 (k + 1)
  have hm_le : m ≤ 64 := Nat.min_le_left _ _
  have hsplit_ab :
      gf2PrefixFold 64 (fun d => a.getLsbD d && (!decide (k < d) && b.getLsbD (k - d))) =
        gf2PrefixFold m (fun d => a.getLsbD d && b.getLsbD (k - d)) := by
    rw [gf2PrefixFold_split 64 m _ (fun d hmd hd64 => by
      by_cases hkd : k < d
      · simp [hkd]
      · omega) hm_le]
    exact gf2PrefixFold_congr (fun d hd => by
      have hkd : ¬(k < d) := by omega
      simp [hkd])
  have hsplit_ba :
      gf2PrefixFold 64 (fun d => b.getLsbD d && (!decide (k < d) && a.getLsbD (k - d))) =
        gf2PrefixFold m (fun d => b.getLsbD d && a.getLsbD (k - d)) := by
    rw [gf2PrefixFold_split 64 m _ (fun d hmd hd64 => by
      by_cases hkd : k < d
      · simp [hkd]
      · omega) hm_le]
    exact gf2PrefixFold_congr (fun d hd => by
      have hkd : ¬(k < d) := by omega
      simp [hkd])
  rw [hsplit_ab, hsplit_ba]
  by_cases hk64 : k < 64
  · have hm_eq : m = k + 1 := Nat.min_eq_right (by omega)
    rw [hm_eq, gf2PrefixFold_rev (k + 1)]
    exact gf2PrefixFold_congr (fun j hj => by
      have h1 : k + 1 - 1 - j = k - j := by omega
      have h2 : k - (k - j) = j := by omega
      rw [h1, h2, Bool.and_comm])
  · have hm_eq : m = 64 := Nat.min_eq_left (by omega)
    rw [hm_eq]
    let lo := k - 63
    have hlo_le : lo ≤ 64 := by omega
    -- Terms with `d < lo` have `k - d ≥ 64`, so `getLsbD (k - d) = false`.
    -- Reindex via `k - d` over `[0 .. 63]` directly by reversing `gf2PrefixFold (k + 1)`!
    -- Even cleaner: extend both from `64` up to `k + 1` because for `64 ≤ d < k + 1`, `getLsbD d = false`!
    have hext_ab :
        gf2PrefixFold 64 (fun d => a.getLsbD d && b.getLsbD (k - d)) =
          gf2PrefixFold (k + 1) (fun d => a.getLsbD d && b.getLsbD (k - d)) := by
      symm
      exact gf2PrefixFold_split (k + 1) 64 _ (fun d hd64 _ => by
        rw [BitVec.getLsbD_of_ge a d hd64]; simp) (by omega)
    have hext_ba :
        gf2PrefixFold 64 (fun d => b.getLsbD d && a.getLsbD (k - d)) =
          gf2PrefixFold (k + 1) (fun d => b.getLsbD d && a.getLsbD (k - d)) := by
      symm
      exact gf2PrefixFold_split (k + 1) 64 _ (fun d hd64 _ => by
        rw [BitVec.getLsbD_of_ge b d hd64]; simp) (by omega)
    rw [hext_ab, hext_ba, gf2PrefixFold_rev (k + 1)]
    exact gf2PrefixFold_congr (fun j hj => by
      have h1 : k + 1 - 1 - j = k - j := by omega
      have h2 : k - (k - j) = j := by omega
      rw [h1, h2, Bool.and_comm])

/-- `LeanNative.IR.clmul64` is commutative (`clmul64 a b = clmul64 b a`), so the operand order in
    `clmul64_eq_sail_carryless_mul_lo` (`clmul64 b a`) agrees identically with `clmul64 a b`. -/
theorem clmul64_comm (a b : UInt64) : clmul64 a b = clmul64 b a := by
  apply UInt64.eq_of_toBitVec_eq
  rw [clmul64_eq_sail_carryless_mul_lo b a, clmul64_eq_sail_carryless_mul_lo a b,
    sail_carryless_mul_comm]

/-- `LeanNative.IR.clmul64Hi` is commutative (`clmul64Hi a b = clmul64Hi b a`), matching
    `carryless_mul a.toBitVec b.toBitVec` high bits in either argument order. -/
theorem clmul64Hi_comm (a b : UInt64) : clmul64Hi a b = clmul64Hi b a := by
  apply UInt64.eq_of_toBitVec_eq
  rw [clmul64Hi_eq_sail_carryless_mul_hi b a, clmul64Hi_eq_sail_carryless_mul_hi a b,
    sail_carryless_mul_comm]

/-- Direct argument-order bisimulation for `clmul64 a b`, `clmul64Hi a b`, and `clmul64RSpec a b`
    against `carryless_mul` / `carryless_mulr` (via `sail_carryless_mul_comm`). -/
theorem clmul64_direct_order_bisim_sail (a b : UInt64) :
    (clmul64 a b).toBitVec = Sail.BitVec.extractLsb (carryless_mul a.toBitVec b.toBitVec) 63 0 ∧
      (clmul64Hi a b).toBitVec = Sail.BitVec.extractLsb (carryless_mul a.toBitVec b.toBitVec) 127 64 ∧
      clmul64RSpec a b = clmul64RSpec b a := by
  refine ⟨?_, ?_, ?_⟩
  · rw [clmul64_comm, clmul64_eq_sail_carryless_mul_lo]
  · rw [clmul64Hi_comm, clmul64Hi_eq_sail_carryless_mul_hi]
  · unfold clmul64RSpec
    rw [clmul64Hi_comm, clmul64_comm]

/-! ## 7. Base RV64I Fragment (`RTYPE`, `ITYPE`, `SHIFTIOP`, `UTYPE`, `BTYPE`) -/

/-- Exact upstream Sail `execute_RTYPE` functional core (`LeanRV64D/InstsEnd.lean`, lines 67773–67797). -/
def sailRtypeCore (op : rop) (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  match op with
  | .ADD => rs1_val + rs2_val
  | .SLT => zero_extend (m := 64) (bool_to_bit (zopz0zI_s rs1_val rs2_val))
  | .SLTU => zero_extend (m := 64) (bool_to_bit (zopz0zI_u rs1_val rs2_val))
  | .AND => rs1_val &&& rs2_val
  | .OR => rs1_val ||| rs2_val
  | .XOR => rs1_val ^^^ rs2_val
  | .SLL => shift_bits_left rs1_val (Sail.BitVec.extractLsb rs2_val (Functions.log2_xlen -i 1) 0)
  | .SRL => shift_bits_right rs1_val (Sail.BitVec.extractLsb rs2_val (Functions.log2_xlen -i 1) 0)
  | .SUB => rs1_val - rs2_val
  | .SRA => shift_bits_right_arith rs1_val (Sail.BitVec.extractLsb rs2_val (Functions.log2_xlen -i 1) 0)

/-- Pure `TurboLean`-side RV64I `RTYPE` ALU/shift specification (`ADD`, `SUB`, `AND`, `OR`, `XOR`,
    `SLT`, `SLTU`, `SLL`, `SRL`, `SRA`, masking shift amounts to the low 6 bits `rs2.toNat % 64`). -/
def rv64iRtypeSpec (op : rop) (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  match op with
  | .ADD => rs1_val + rs2_val
  | .SUB => rs1_val - rs2_val
  | .AND => rs1_val &&& rs2_val
  | .OR => rs1_val ||| rs2_val
  | .XOR => rs1_val ^^^ rs2_val
  | .SLT => if BitVec.slt rs1_val rs2_val then 1#64 else 0#64
  | .SLTU => if BitVec.ult rs1_val rs2_val then 1#64 else 0#64
  | .SLL => rs1_val <<< (rs2_val.toNat % 64)
  | .SRL => rs1_val >>> (rs2_val.toNat % 64)
  | .SRA => BitVec.sshiftRight rs1_val (rs2_val.toNat % 64)

/-- Exact upstream Sail `execute_ITYPE` functional core (`LeanRV64D/InstsEnd.lean`, lines 69267–69279). -/
def sailItypeCore (op : iop) (rs1_val : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  let immext : BitVec 64 := sign_extend (m := 64) imm
  match op with
  | .ADDI => rs1_val + immext
  | .SLTI => zero_extend (m := 64) (bool_to_bit (zopz0zI_s rs1_val immext))
  | .SLTIU => zero_extend (m := 64) (bool_to_bit (zopz0zI_u rs1_val immext))
  | .ANDI => rs1_val &&& immext
  | .ORI => rs1_val ||| immext
  | .XORI => rs1_val ^^^ immext

/-- Pure `TurboLean`-side RV64I `ITYPE` immediate ALU specification (`ADDI`, `SLTI`, `SLTIU`,
    `ANDI`, `ORI`, `XORI`) over 12-bit sign-extended immediates. -/
def rv64iItypeSpec (op : iop) (rs1_val : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  let immext := imm.signExtend 64
  match op with
  | .ADDI => rs1_val + immext
  | .SLTI => if BitVec.slt rs1_val immext then 1#64 else 0#64
  | .SLTIU => if BitVec.ult rs1_val immext then 1#64 else 0#64
  | .ANDI => rs1_val &&& immext
  | .ORI => rs1_val ||| immext
  | .XORI => rs1_val ^^^ immext

/-- Exact upstream Sail `execute_SHIFTIOP` functional core (`LeanRV64D/InstsEnd.lean`, lines 67611–67619). -/
def sailShiftIopCore (op : sop) (rs1_val : BitVec 64) (shamt : BitVec 6) : BitVec 64 :=
  let shamt' := Sail.BitVec.extractLsb shamt (Functions.log2_xlen -i 1) 0
  match op with
  | .SLLI => shift_bits_left rs1_val shamt'
  | .SRLI => shift_bits_right rs1_val shamt'
  | .SRAI => shift_bits_right_arith rs1_val shamt'

/-- Pure `TurboLean`-side RV64I `SHIFTIOP` immediate shift specification (`SLLI`, `SRLI`, `SRAI`). -/
def rv64iShiftIopSpec (op : sop) (rs1_val : BitVec 64) (shamt : BitVec 6) : BitVec 64 :=
  match op with
  | .SLLI => rs1_val <<< shamt.toNat
  | .SRLI => rs1_val >>> shamt.toNat
  | .SRAI => BitVec.sshiftRight rs1_val shamt.toNat

/-- Exact upstream Sail `execute_UTYPE` monadic body (`LeanRV64D/InstsEnd.lean`, lines 67326–67333),
    exercising `sign_extend (m := 64) (imm +++ 0x000#12)`, `get_arch_pc`, and `wX_bits`. -/
def sailUtypeExec (imm : BitVec 20) (rd : regidx) (op : uop) : SailM Unit := do
  let off : xlenbits := sign_extend (m := 64) (imm +++ 0x000#12)
  wX_bits rd (← do
    match op with
    | .LUI => pure off
    | .AUIPC => pure ((← get_arch_pc ()) + off))

/-- Pure `TurboLean`-side RV64I `UTYPE` (`LUI` / `AUIPC`) value specification: places the 20-bit
    immediate in bits `[31:12]`, zeroes bits `[11:0]`, sign-extends from bit 31 to 64 bits, and
    adds architectural `PC` for `AUIPC`. -/
def rv64iUtypeSpec (op : uop) (pc : BitVec 64) (imm : BitVec 20) : BitVec 64 :=
  let off := (imm.signExtend 64) <<< 12
  match op with
  | .LUI => off
  | .AUIPC => pc + off

/-- Exact upstream Sail `execute_BTYPE` branch-condition core (`LeanRV64D/InstsEnd.lean`, lines 71762–71769). -/
def sailBtypeTakenCore (op : bop) (rs1_val rs2_val : BitVec 64) : Bool :=
  match op with
  | .BEQ => rs1_val == rs2_val
  | .BNE => rs1_val != rs2_val
  | .BLT => zopz0zI_s rs1_val rs2_val
  | .BGE => zopz0zKzJ_s rs1_val rs2_val
  | .BLTU => zopz0zI_u rs1_val rs2_val
  | .BGEU => zopz0zKzJ_u rs1_val rs2_val

/-- Pure `TurboLean`-side RV64I `BTYPE` branch predicate specification (`BEQ`, `BNE`, `BLT`,
    `BGE`, `BLTU`, `BGEU`). -/
def rv64iBtypeTakenSpec (op : bop) (rs1_val rs2_val : BitVec 64) : Bool :=
  match op with
  | .BEQ => rs1_val == rs2_val
  | .BNE => rs1_val != rs2_val
  | .BLT => BitVec.slt rs1_val rs2_val
  | .BGE => !BitVec.slt rs1_val rs2_val
  | .BLTU => BitVec.ult rs1_val rs2_val
  | .BGEU => !BitVec.ult rs1_val rs2_val

private theorem zopz0zI_s_eq_slt (x y : BitVec 64) :
    zopz0zI_s x y = BitVec.slt x y := by
  unfold zopz0zI_s BitVec.slt
  rfl

private theorem zopz0zKzJ_s_eq_not_slt (x y : BitVec 64) :
    zopz0zKzJ_s x y = !BitVec.slt x y := by
  unfold zopz0zKzJ_s BitVec.slt
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
  omega

private theorem zopz0zI_u_eq_ult (x y : BitVec 64) :
    zopz0zI_u x y = BitVec.ult x y := by
  unfold zopz0zI_u Sail.BitVec.toNatInt BitVec.ult
  change decide ((x.toNat : Int) < (y.toNat : Int)) = decide (x.toNat < y.toNat)
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

private theorem zopz0zKzJ_u_eq_not_ult (x y : BitVec 64) :
    zopz0zKzJ_u x y = !BitVec.ult x y := by
  unfold zopz0zKzJ_u Sail.BitVec.toNatInt BitVec.ult
  change decide ((x.toNat : Int) ≥ (y.toNat : Int)) = !decide (x.toNat < y.toNat)
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
  omega

private theorem zero_extend_bool_to_bit_64 (c : Bool) :
    zero_extend (m := 64) (bool_to_bit c) = (if c then 1#64 else 0#64) := by
  cases c <;> rfl

private theorem extractLsb_5_0_toNat (x : BitVec 64) :
    (Sail.BitVec.extractLsb x (Functions.log2_xlen -i 1) 0).toNat = x.toNat % 64 := by
  change (BitVec.extractLsb 5 0 x).toNat = x.toNat % 64
  rw [BitVec.extractLsb_toNat, Nat.shiftRight_zero]

private theorem extractLsb_5_0_toNat_6 (shamt : BitVec 6) :
    (Sail.BitVec.extractLsb shamt (Functions.log2_xlen -i 1) 0).toNat = shamt.toNat := by
  change (BitVec.extractLsb 5 0 shamt).toNat = shamt.toNat
  rw [BitVec.extractLsb_toNat, Nat.shiftRight_zero]
  exact Nat.mod_eq_of_lt shamt.isLt

/-- RV64I `RTYPE` bisimulation across all 10 register-register operations (`ADD`, `SUB`, `AND`,
    `OR`, `XOR`, `SLT`, `SLTU`, `SLL`, `SRL`, `SRA`), verifying both ALU/comparison results and
    6-bit shift-amount masking (`extractLsb rs2 5 0`). -/
theorem rv64iRtypeSpec_bisim_sail (op : rop) (rs1_val rs2_val : BitVec 64) :
    rv64iRtypeSpec op rs1_val rs2_val = sailRtypeCore op rs1_val rs2_val := by
  cases op with
  | ADD | SUB | AND | OR | XOR => rfl
  | SLT =>
    dsimp only [rv64iRtypeSpec, sailRtypeCore]
    rw [zopz0zI_s_eq_slt, zero_extend_bool_to_bit_64]
  | SLTU =>
    dsimp only [rv64iRtypeSpec, sailRtypeCore]
    rw [zopz0zI_u_eq_ult, zero_extend_bool_to_bit_64]
  | SLL =>
    dsimp only [rv64iRtypeSpec, sailRtypeCore, shift_bits_left]
    rw [BitVec.shiftLeft_eq', extractLsb_5_0_toNat]
  | SRL =>
    dsimp only [rv64iRtypeSpec, sailRtypeCore, shift_bits_right]
    rw [BitVec.ushiftRight_eq', extractLsb_5_0_toNat]
  | SRA =>
    dsimp only [rv64iRtypeSpec, sailRtypeCore, shift_bits_right_arith, Sail.BitVec.toNatInt]
    change rs1_val.sshiftRight (rs2_val.toNat % 64) =
      rs1_val.sshiftRight (Sail.BitVec.extractLsb rs2_val (Functions.log2_xlen -i 1) 0).toNat
    rw [extractLsb_5_0_toNat]

/-- RV64I `ITYPE` bisimulation across all 6 register-immediate ALU operations (`ADDI`, `SLTI`,
    `SLTIU`, `ANDI`, `ORI`, `XORI`) with 12-to-64-bit sign extension. -/
theorem rv64iItypeSpec_bisim_sail (op : iop) (rs1_val : BitVec 64) (imm : BitVec 12) :
    rv64iItypeSpec op rs1_val imm = sailItypeCore op rs1_val imm := by
  cases op with
  | ADDI | ANDI | ORI | XORI => rfl
  | SLTI =>
    dsimp only [rv64iItypeSpec, sailItypeCore, sign_extend, Sail.BitVec.signExtend]
    rw [zopz0zI_s_eq_slt, zero_extend_bool_to_bit_64]
  | SLTIU =>
    dsimp only [rv64iItypeSpec, sailItypeCore, sign_extend, Sail.BitVec.signExtend]
    rw [zopz0zI_u_eq_ult, zero_extend_bool_to_bit_64]

/-- RV64I `SHIFTIOP` bisimulation across all 3 immediate shift operations (`SLLI`, `SRLI`, `SRAI`). -/
theorem rv64iShiftIopSpec_bisim_sail (op : sop) (rs1_val : BitVec 64) (shamt : BitVec 6) :
    rv64iShiftIopSpec op rs1_val shamt = sailShiftIopCore op rs1_val shamt := by
  cases op with
  | SLLI =>
    dsimp only [rv64iShiftIopSpec, sailShiftIopCore, shift_bits_left]
    rw [BitVec.shiftLeft_eq', extractLsb_5_0_toNat_6]
  | SRLI =>
    dsimp only [rv64iShiftIopSpec, sailShiftIopCore, shift_bits_right]
    rw [BitVec.ushiftRight_eq', extractLsb_5_0_toNat_6]
  | SRAI =>
    dsimp only [rv64iShiftIopSpec, sailShiftIopCore, shift_bits_right_arith, Sail.BitVec.toNatInt]
    change rs1_val.sshiftRight shamt.toNat =
      rs1_val.sshiftRight (Sail.BitVec.extractLsb shamt (Functions.log2_xlen -i 1) 0).toNat
    rw [extractLsb_5_0_toNat_6]

private theorem sign_extend_append_zero12_eq_shl12 (imm : BitVec 20) :
    sign_extend (m := 64) (imm +++ 0x000#12) = (imm.signExtend 64) <<< 12 := by
  change BitVec.signExtend 64 (imm +++ 0#12) = (imm.signExtend 64) <<< 12
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_signExtend, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_append]
  by_cases hk12 : k < 12
  · have hk32 : k < 32 := by omega
    simp [hk, hk32, hk12]
  · by_cases hk32 : k < 32
    · have hksub : k - 12 < 20 := by omega
      simp [hk, hk32, hk12, hksub, show k - 12 < 64 by omega]
    · have hksub : ¬(k - 12 < 20) := by omega
      have hmsb : (imm +++ 0#12).msb = imm.msb := by
        rw [BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_append]
        simp
      simp [hk, hk32, hk12, hksub, show k - 12 < 64 by omega, hmsb]

/-- Upstream `get_arch_pc` reads `Register.PC` from `SequentialState` without side effects
    when `PC` is initialized in `s.regs`. -/
theorem get_arch_pc_run (pc : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hpc : s.regs.get? .PC = some pc) :
    (get_arch_pc ()).run s = .ok pc s := by
  simp [get_arch_pc, readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
  dsimp [EStateM.get, EStateM.run]
  rw [hpc]
  rfl

/-- RV64I `UTYPE` (`LUI` and `AUIPC`) monadic bisimulation on `x1`: executing `sailUtypeExec`
    writes `rv64iUtypeSpec op pc imm` to `x1` (reading `PC` via `get_arch_pc` in the `AUIPC` arm). -/
theorem rv64iUtypeSpec_bisim_sail_x1 (op : uop) (pc : BitVec 64) (imm : BitVec 20)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hpc : s.regs.get? .PC = some pc) :
    (sailUtypeExec imm (.Regidx 1#5) op).run s =
      .ok () { s with regs := s.regs.insert .x1 (rv64iUtypeSpec op pc imm) } := by
  cases op with
  | LUI =>
    unfold sailUtypeExec rv64iUtypeSpec
    rw [sign_extend_append_zero12_eq_shl12]
    simp [wX_bits, wX, regval_into_reg, xreg_write_callback, reg_name_forwards,
      encdec_reg_forwards_matches, encdec_reg_forwards, get_config_use_abi_names,
      LeanRV64D.Functions.not, reg_arch_name_raw_forwards, xreg_full_write_callback,
      zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.toNatInt, to_bits, get_slice_int,
      writeReg, PreSail.writeReg, modify, modifyGet, MonadStateOf.modifyGet]
    rfl
  | AUIPC =>
    unfold sailUtypeExec rv64iUtypeSpec
    rw [sign_extend_append_zero12_eq_shl12]
    simp [get_arch_pc, readReg, PreSail.readReg, wX_bits, wX, regval_into_reg,
      xreg_write_callback, reg_name_forwards, encdec_reg_forwards_matches, encdec_reg_forwards,
      get_config_use_abi_names, LeanRV64D.Functions.not, reg_arch_name_raw_forwards,
      xreg_full_write_callback, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.toNatInt,
      to_bits, get_slice_int, writeReg, PreSail.writeReg,
      modify, modifyGet, MonadStateOf.modifyGet, get, getThe, MonadStateOf.get]
    dsimp [EStateM.bind, EStateM.get, EStateM.modifyGet, EStateM.pure, EStateM.run]
    rw [hpc]
    rfl

/-- RV64I `BTYPE` branch-condition bisimulation across all 6 branch opcodes (`BEQ`, `BNE`,
    `BLT`, `BGE`, `BLTU`, `BGEU`) plus complementary pair duality (`BNE = !BEQ`, `BGE = !BLT`,
    `BGEU = !BLTU`). -/
theorem rv64iBtypeTakenSpec_bisim_sail (op : bop) (rs1_val rs2_val : BitVec 64) :
    rv64iBtypeTakenSpec op rs1_val rs2_val = sailBtypeTakenCore op rs1_val rs2_val := by
  cases op with
  | BEQ | BNE => rfl
  | BLT => exact (zopz0zI_s_eq_slt rs1_val rs2_val).symm
  | BGE => exact (zopz0zKzJ_s_eq_not_slt rs1_val rs2_val).symm
  | BLTU => exact (zopz0zI_u_eq_ult rs1_val rs2_val).symm
  | BGEU => exact (zopz0zKzJ_u_eq_not_ult rs1_val rs2_val).symm

/-- Complementary duality of upstream Sail RV64I branch predicates (`BEQ`/`BNE`, `BLT`/`BGE`,
    `BLTU`/`BGEU`). -/
theorem sailBtypeTakenCore_complement (rs1_val rs2_val : BitVec 64) :
    sailBtypeTakenCore .BNE rs1_val rs2_val = !sailBtypeTakenCore .BEQ rs1_val rs2_val ∧
      sailBtypeTakenCore .BGE rs1_val rs2_val = !sailBtypeTakenCore .BLT rs1_val rs2_val ∧
      sailBtypeTakenCore .BGEU rs1_val rs2_val = !sailBtypeTakenCore .BLTU rs1_val rs2_val := by
  rw [← rv64iBtypeTakenSpec_bisim_sail, ← rv64iBtypeTakenSpec_bisim_sail,
    ← rv64iBtypeTakenSpec_bisim_sail, ← rv64iBtypeTakenSpec_bisim_sail,
    ← rv64iBtypeTakenSpec_bisim_sail, ← rv64iBtypeTakenSpec_bisim_sail]
  exact ⟨rfl, rfl, rfl⟩

/-! ## 8. RV64I 32-Bit Word ALU & Shift Fragment (`RTYPEW`, `ADDIW`, `SHIFTIWOP`) -/

/-- Exact upstream Sail `execute_RTYPEW` functional core (`LeanRV64D/InstsEnd.lean`, lines 67760–67771). -/
def sailRtypewCore (op : ropw) (rs1_full rs2_full : BitVec 64) : BitVec 64 :=
  let rs1_val : BitVec 32 := Sail.BitVec.extractLsb rs1_full 31 0
  let rs2_val : BitVec 32 := Sail.BitVec.extractLsb rs2_full 31 0
  let result : BitVec 32 :=
    match op with
    | .ADDW => rs1_val + rs2_val
    | .SUBW => rs1_val - rs2_val
    | .SLLW => shift_bits_left rs1_val (Sail.BitVec.extractLsb rs2_val 4 0)
    | .SRLW => shift_bits_right rs1_val (Sail.BitVec.extractLsb rs2_val 4 0)
    | .SRAW => shift_bits_right_arith rs1_val (Sail.BitVec.extractLsb rs2_val 4 0)
  sign_extend (m := 64) result

/-- Pure `TurboLean`-side RV64I `RTYPEW` specification (`ADDW`, `SUBW`, `SLLW`, `SRLW`, `SRAW`):
    truncates inputs to 32 bits, masks shift amounts to 5 bits (`% 32`), and sign-extends bit 31
    to 64 bits. -/
def rv64iRtypewSpec (op : ropw) (rs1_full rs2_full : BitVec 64) : BitVec 64 :=
  let rs1_val : BitVec 32 := rs1_full.truncate 32
  let rs2_val : BitVec 32 := rs2_full.truncate 32
  let res32 : BitVec 32 :=
    match op with
    | .ADDW => rs1_val + rs2_val
    | .SUBW => rs1_val - rs2_val
    | .SLLW => rs1_val <<< (rs2_full.toNat % 32)
    | .SRLW => rs1_val >>> (rs2_full.toNat % 32)
    | .SRAW => BitVec.sshiftRight rs1_val (rs2_full.toNat % 32)
  res32.signExtend 64

/-- Exact upstream Sail `execute_ADDIW` functional core (`LeanRV64D/InstsEnd.lean`, lines 72007–72010). -/
def sailAddiwCore (rs1_full : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  let result : BitVec 64 := rs1_full + sign_extend (m := 64) imm
  sign_extend (m := 64) (Sail.BitVec.extractLsb result 31 0)

/-- Pure `TurboLean`-side RV64I `ADDIW` specification: adds the 12-to-32-bit sign-extended
    immediate to the low 32 bits of `rs1` and sign-extends bit 31 to 64 bits. -/
def rv64iAddiwSpec (rs1_full : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  ((rs1_full.truncate 32) + imm.signExtend 32).signExtend 64

/-- Exact upstream Sail `execute_SHIFTIWOP` functional core (`LeanRV64D/InstsEnd.lean`, lines 67601–67609). -/
def sailShiftIwopCore (op : sopw) (rs1_full : BitVec 64) (shamt : BitVec 5) : BitVec 64 :=
  let rs1_val : BitVec 32 := Sail.BitVec.extractLsb rs1_full 31 0
  let result : BitVec 32 :=
    match op with
    | .SLLIW => shift_bits_left rs1_val shamt
    | .SRLIW => shift_bits_right rs1_val shamt
    | .SRAIW => shift_bits_right_arith rs1_val shamt
  sign_extend (m := 64) result

/-- Pure `TurboLean`-side RV64I `SHIFTIWOP` specification (`SLLIW`, `SRLIW`, `SRAIW`):
    operates on the low 32 bits with a 5-bit immediate shift and sign-extends bit 31 to 64 bits. -/
def rv64iShiftIwopSpec (op : sopw) (rs1_full : BitVec 64) (shamt : BitVec 5) : BitVec 64 :=
  let rs1_val : BitVec 32 := rs1_full.truncate 32
  let res32 : BitVec 32 :=
    match op with
    | .SLLIW => rs1_val <<< shamt.toNat
    | .SRLIW => rs1_val >>> shamt.toNat
    | .SRAIW => BitVec.sshiftRight rs1_val shamt.toNat
  res32.signExtend 64

private theorem extractLsb_31_0_eq_truncate32 (x : BitVec 64) :
    Sail.BitVec.extractLsb x 31 0 = x.truncate 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, hk]

private theorem truncate32_add (a b : BitVec 64) :
    (a + b).truncate 32 = a.truncate 32 + b.truncate 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  have hdvd : 2 ^ 32 ∣ 2 ^ 64 := ⟨2 ^ 32, by decide⟩
  rw [Nat.mod_mod_of_dvd _ hdvd, Nat.add_mod]

private theorem truncate32_signExtend64 (v : BitVec 32) :
    (v.signExtend 64).truncate 32 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend]
  simp [hk, show k < 64 by omega]

private theorem extractLsb_4_0_of_32_toNat (x : BitVec 64) :
    (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb x 31 0) 4 0).toNat = x.toNat % 32 := by
  change (BitVec.extractLsb 4 0 (BitVec.extractLsb 31 0 x)).toNat = x.toNat % 32
  rw [BitVec.extractLsb_toNat, BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.shiftRight_zero]
  have hdvd : 2 ^ 5 ∣ 2 ^ 32 := ⟨2 ^ 27, by decide⟩
  exact Nat.mod_mod_of_dvd _ hdvd

/-- RV64I `RTYPEW` bisimulation across all 5 word-width register-register operations
    (`ADDW`, `SUBW`, `SLLW`, `SRLW`, `SRAW`), verifying 32-bit truncation, 5-bit shift masking,
    and 32-to-64-bit sign extension. -/
theorem rv64iRtypewSpec_bisim_sail (op : ropw) (rs1_full rs2_full : BitVec 64) :
    rv64iRtypewSpec op rs1_full rs2_full = sailRtypewCore op rs1_full rs2_full := by
  cases op with
  | ADDW | SUBW =>
    dsimp only [rv64iRtypewSpec, sailRtypewCore, sign_extend, Sail.BitVec.signExtend]
    rw [extractLsb_31_0_eq_truncate32, extractLsb_31_0_eq_truncate32]
  | SLLW =>
    dsimp only [rv64iRtypewSpec, sailRtypewCore, sign_extend, Sail.BitVec.signExtend, shift_bits_left]
    rw [BitVec.shiftLeft_eq', extractLsb_4_0_of_32_toNat, extractLsb_31_0_eq_truncate32]
  | SRLW =>
    dsimp only [rv64iRtypewSpec, sailRtypewCore, sign_extend, Sail.BitVec.signExtend, shift_bits_right]
    rw [BitVec.ushiftRight_eq', extractLsb_4_0_of_32_toNat, extractLsb_31_0_eq_truncate32]
  | SRAW =>
    dsimp only [rv64iRtypewSpec, sailRtypewCore, sign_extend, Sail.BitVec.signExtend,
      shift_bits_right_arith, Sail.BitVec.toNatInt]
    congr 1
    change (rs1_full.truncate 32).sshiftRight (rs2_full.toNat % 32) =
      (Sail.BitVec.extractLsb rs1_full 31 0).sshiftRight
        (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb rs2_full 31 0) 4 0).toNat
    rw [extractLsb_4_0_of_32_toNat, extractLsb_31_0_eq_truncate32]

/-- RV64I `ADDIW` bisimulation: Sail's 64-bit sign-extended addition followed by `[31:0]` slice
    and 64-bit sign extension agrees bit-for-bit with 32-bit modular addition sign-extended to 64 bits. -/
theorem rv64iAddiwSpec_bisim_sail (rs1_full : BitVec 64) (imm : BitVec 12) :
    rv64iAddiwSpec rs1_full imm = sailAddiwCore rs1_full imm := by
  dsimp only [rv64iAddiwSpec, sailAddiwCore, sign_extend, Sail.BitVec.signExtend]
  rw [extractLsb_31_0_eq_truncate32, truncate32_add]
  congr 2
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, BitVec.getLsbD_signExtend]
  simp [hk, show k < 64 by omega]

/-- RV64I `SHIFTIWOP` bisimulation across all 3 immediate word-shift operations
    (`SLLIW`, `SRLIW`, `SRAIW`). -/
theorem rv64iShiftIwopSpec_bisim_sail (op : sopw) (rs1_full : BitVec 64) (shamt : BitVec 5) :
    rv64iShiftIwopSpec op rs1_full shamt = sailShiftIwopCore op rs1_full shamt := by
  cases op with
  | SLLIW =>
    dsimp only [rv64iShiftIwopSpec, sailShiftIwopCore, sign_extend, Sail.BitVec.signExtend, shift_bits_left]
    rw [BitVec.shiftLeft_eq', extractLsb_31_0_eq_truncate32]
  | SRLIW =>
    dsimp only [rv64iShiftIwopSpec, sailShiftIwopCore, sign_extend, Sail.BitVec.signExtend, shift_bits_right]
    rw [BitVec.ushiftRight_eq', extractLsb_31_0_eq_truncate32]
  | SRAIW =>
    dsimp only [rv64iShiftIwopSpec, sailShiftIwopCore, sign_extend, Sail.BitVec.signExtend,
      shift_bits_right_arith, Sail.BitVec.toNatInt]
    rw [extractLsb_31_0_eq_truncate32]
    rfl

/-! ## 9. RV64M 32-Bit Word Multiply / Divide / Remainder (`MULW`, `DIVW`, `DIVUW`, `REMW`, `REMUW`) -/

/-- Exact upstream Sail `execute_MULW` functional core (`LeanRV64D/InstsEnd.lean`, lines 68856–68863). -/
def sailMulwCore (rs1_full rs2_full : BitVec 64) : BitVec 64 :=
  let rs1_bits : BitVec 32 := Sail.BitVec.extractLsb rs1_full 31 0
  let rs2_bits : BitVec 32 := Sail.BitVec.extractLsb rs2_full 31 0
  let rs1_int : Int := BitVec.toInt rs1_bits
  let rs2_int : Int := BitVec.toInt rs2_bits
  let result32 : BitVec 32 := to_bits_truncate (l := 32) (rs1_int *i rs2_int)
  sign_extend (m := 64) result32

/-- Pure `TurboLean`-side RV64M `MULW` specification: multiplies the low 32 bits of `rs1` and `rs2`
    modulo `2^32` and sign-extends bit 31 to 64 bits. -/
def riscvMulwSpec (rs1_full rs2_full : BitVec 64) : BitVec 64 :=
  ((rs1_full.truncate 32) * (rs2_full.truncate 32)).signExtend 64

/-- Exact upstream Sail `execute_DIVW` functional core (`LeanRV64D/InstsEnd.lean`, lines 71411–71431),
    covering both `DIVW` (`is_unsigned = false`) and `DIVUW` (`is_unsigned = true`). -/
def sailDivwCore (is_unsigned : Bool) (rs1_full rs2_full : BitVec 64) : BitVec 64 :=
  let rs1_bits : BitVec 32 := Sail.BitVec.extractLsb rs1_full 31 0
  let rs2_bits : BitVec 32 := Sail.BitVec.extractLsb rs2_full 31 0
  let rs1_int : Int := if is_unsigned then Sail.BitVec.toNatInt rs1_bits else BitVec.toInt rs1_bits
  let rs2_int : Int := if is_unsigned then Sail.BitVec.toNatInt rs2_bits else BitVec.toInt rs2_bits
  let quotient : Int := if (rs2_int == 0 : Bool) then Neg.neg 1 else Int.tdiv rs1_int rs2_int
  let quotient : Int :=
    if (((LeanRV64D.Functions.not is_unsigned) && (quotient ≥b (2 ^i 31))) : Bool) then
      Neg.neg (2 ^i 31)
    else
      quotient
  sign_extend (m := 64) (to_bits_truncate (l := 32) quotient)

/-- Pure `TurboLean`-side RV64M signed 32-bit word division (`DIVW`) specification:
    operates on `[31:0]`, returning all-ones (`-1#64`) on `/ 0`, sign-extended `INT32_MIN`
    (`0xffffffff80000000#64`) on `-2^31 / -1`, and sign-extended `BitVec.sdiv` otherwise. -/
def riscvDivwSpec (rs1_full rs2_full : BitVec 64) : BitVec 64 :=
  let lhs : BitVec 32 := rs1_full.truncate 32
  let rhs : BitVec 32 := rs2_full.truncate 32
  let q32 : BitVec 32 :=
    if rhs == 0#32 then
      BitVec.allOnes 32
    else if lhs == BitVec.intMin 32 && rhs == BitVec.allOnes 32 then
      BitVec.intMin 32
    else
      BitVec.sdiv lhs rhs
  q32.signExtend 64

/-- Pure `TurboLean`-side RV64M unsigned 32-bit word division (`DIVUW`) specification:
    operates on `[31:0]`, returning sign-extended `0xffffffff#32` (`BitVec.allOnes 64`, i.e. `-1`)
    on `/ 0`, and sign-extended 32-bit unsigned quotient `(lhs / rhs).signExtend 64` otherwise
    (notably sign-extending bit 31 when `lhs >= 2^31` and `rhs = 1`). -/
def riscvDivuwSpec (rs1_full rs2_full : BitVec 64) : BitVec 64 :=
  let lhs : BitVec 32 := rs1_full.truncate 32
  let rhs : BitVec 32 := rs2_full.truncate 32
  let q32 : BitVec 32 := if rhs == 0#32 then BitVec.allOnes 32 else lhs / rhs
  q32.signExtend 64

/-- Exact upstream Sail `execute_REMW` functional core (`LeanRV64D/InstsEnd.lean`, lines 68018–68034),
    covering both `REMW` (`is_unsigned = false`) and `REMUW` (`is_unsigned = true`). -/
def sailRemwCore (is_unsigned : Bool) (rs1_full rs2_full : BitVec 64) : BitVec 64 :=
  let rs1_bits : BitVec 32 := Sail.BitVec.extractLsb rs1_full 31 0
  let rs2_bits : BitVec 32 := Sail.BitVec.extractLsb rs2_full 31 0
  let rs1_int : Int := if is_unsigned then Sail.BitVec.toNatInt rs1_bits else BitVec.toInt rs1_bits
  let rs2_int : Int := if is_unsigned then Sail.BitVec.toNatInt rs2_bits else BitVec.toInt rs2_bits
  let remainder : Int := if (rs2_int == 0 : Bool) then rs1_int else Int.tmod rs1_int rs2_int
  sign_extend (m := 64) (to_bits_truncate (l := 32) remainder)

/-- Pure `TurboLean`-side RV64M signed 32-bit word remainder (`REMW`) specification:
    operates on `[31:0]`, returning `lhs.signExtend 64` on `/ 0`, `0#64` on `-2^31 % -1`, and
    `(BitVec.srem lhs rhs).signExtend 64` otherwise. -/
def riscvRemwSpec (rs1_full rs2_full : BitVec 64) : BitVec 64 :=
  let lhs : BitVec 32 := rs1_full.truncate 32
  let rhs : BitVec 32 := rs2_full.truncate 32
  let r32 : BitVec 32 :=
    if rhs == 0#32 then
      lhs
    else if lhs == BitVec.intMin 32 && rhs == BitVec.allOnes 32 then
      0#32
    else
      BitVec.srem lhs rhs
  r32.signExtend 64

/-- Pure `TurboLean`-side RV64M unsigned 32-bit word remainder (`REMUW`) specification:
    operates on `[31:0]`, returning `lhs.signExtend 64` on `/ 0` and `(lhs % rhs).signExtend 64`
    otherwise. -/
def riscvRemuwSpec (rs1_full rs2_full : BitVec 64) : BitVec 64 :=
  let lhs : BitVec 32 := rs1_full.truncate 32
  let rhs : BitVec 32 := rs2_full.truncate 32
  let r32 : BitVec 32 := if rhs == 0#32 then lhs else lhs % rhs
  r32.signExtend 64

private theorem toInt_eq_zero_iff_32 (x : BitVec 32) : x.toInt = 0 ↔ x = 0#32 := by
  constructor
  · intro h
    exact BitVec.eq_of_toInt_eq (by simpa using h)
  · rintro rfl
    rfl

private theorem neg_one_eq_allOnes_32 : (-1#32 : BitVec 32) = BitVec.allOnes 32 := by
  decide

private theorem tdiv_lt_two_pow_31_of_not_ovf (x y : BitVec 32)
    (hovf : ¬(x = BitVec.intMin 32 ∧ y = BitVec.allOnes 32)) :
    ¬((2 ^ 31 : Int) ≤ Int.tdiv x.toInt y.toInt) := by
  have hor : x ≠ BitVec.intMin 32 ∨ y ≠ -1#32 := by
    rw [neg_one_eq_allOnes_32]
    by_cases hx : x = BitVec.intMin 32
    · exact Or.inr (fun hy => hovf ⟨hx, hy⟩)
    · exact Or.inl hx
  rw [← BitVec.toInt_sdiv_of_ne_or_ne x y hor]
  have hlt : (x.sdiv y).toInt < 2 ^ (32 - 1) := @BitVec.toInt_lt 32 (x.sdiv y)
  have hp : (2 ^ (32 - 1) : Int) = (2 ^ 31 : Int) := by decide
  omega

/-- RV64M `MULW` bisimulation: `riscvMulwSpec` matches upstream Sail `execute_MULW` across all
    64-bit register pairs. -/
theorem riscvMulwSpec_bisim_sail (rs1_full rs2_full : BitVec 64) :
    riscvMulwSpec rs1_full rs2_full = sailMulwCore rs1_full rs2_full := by
  dsimp only [riscvMulwSpec, sailMulwCore, sign_extend, Sail.BitVec.signExtend]
  rw [extractLsb_31_0_eq_truncate32, extractLsb_31_0_eq_truncate32, to_bits_truncate_eq_ofInt]
  congr 1
  change (rs1_full.truncate 32) * (rs2_full.truncate 32) =
    BitVec.ofInt 32 ((rs1_full.truncate 32).toInt * (rs2_full.truncate 32).toInt)
  rw [BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.ofInt_toInt]

/-- RV64M signed `DIVW` bisimulation (`is_unsigned = false`), including `/ 0` (`-1#64`) and
    `-2^31 / -1` (`0xffffffff80000000#64`, sign-extending 32-bit `INT32_MIN`). -/
theorem riscvDivwSpec_bisim_sail (rs1_full rs2_full : BitVec 64) :
    riscvDivwSpec rs1_full rs2_full = sailDivwCore false rs1_full rs2_full := by
  dsimp only [riscvDivwSpec, sailDivwCore, sign_extend, Sail.BitVec.signExtend]
  rw [extractLsb_31_0_eq_truncate32, extractLsb_31_0_eq_truncate32, to_bits_truncate_eq_ofInt]
  generalize rs1_full.truncate 32 = lhs
  generalize rs2_full.truncate 32 = rhs
  have hp31 : ((2 : Int) ^i (31 : Int)) = (2 ^ 31 : Int) := by decide
  have hnot : LeanRV64D.Functions.not false = true := rfl
  simp only [Bool.false_eq_true, ↓reduceIte, hp31, hnot, Bool.true_and]
  congr 1
  by_cases hr : rhs = 0#32
  · subst hr
    have hr0 : ((0#32).toInt == 0) = true := rfl
    have hb0 : (0#32 == 0#32) = true := rfl
    rw [hr0, hb0]
    simp only [↓reduceIte]
    decide
  · have hb_ne : (rhs == 0#32) = false := beq_false_of_ne hr
    have hr_int_ne : rhs.toInt ≠ 0 := fun h => hr ((toInt_eq_zero_iff_32 rhs).mp h)
    have hr_int_beq : ((rhs.toInt == 0) : Bool) = false := beq_false_of_ne hr_int_ne
    rw [hb_ne, hr_int_beq]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hovf : lhs = BitVec.intMin 32 ∧ rhs = BitVec.allOnes 32
    · rcases hovf with ⟨rfl, rfl⟩
      decide
    · have hcond_false : (lhs == BitVec.intMin 32 && rhs == BitVec.allOnes 32) = false := by
        cases h1 : (lhs == BitVec.intMin 32) <;> cases h2 : (rhs == BitVec.allOnes 32) <;> simp_all
      have hge_false : (decide (Int.tdiv lhs.toInt rhs.toInt ≥ (2 ^ 31 : Int))) = false :=
        decide_eq_false (tdiv_lt_two_pow_31_of_not_ovf lhs rhs hovf)
      rw [hcond_false, hge_false]
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply BitVec.eq_of_toInt_eq
      rw [BitVec.toInt_sdiv, BitVec.toInt_ofInt]

/-- RV64M unsigned `DIVUW` bisimulation (`is_unsigned = true`), including `/ 0` (`-1#64`) and
    sign-extension of bit 31 into `[63:32]`. -/
theorem riscvDivuwSpec_bisim_sail (rs1_full rs2_full : BitVec 64) :
    riscvDivuwSpec rs1_full rs2_full = sailDivwCore true rs1_full rs2_full := by
  dsimp only [riscvDivuwSpec, sailDivwCore, sign_extend, Sail.BitVec.signExtend, Sail.BitVec.toNatInt]
  rw [extractLsb_31_0_eq_truncate32, extractLsb_31_0_eq_truncate32, to_bits_truncate_eq_ofInt]
  generalize rs1_full.truncate 32 = lhs
  generalize rs2_full.truncate 32 = rhs
  have hnot : LeanRV64D.Functions.not true = false := rfl
  simp only [↓reduceIte, hnot, Bool.false_and]
  congr 1
  by_cases hr : rhs = 0#32
  · subst hr
    have hr0 : ((Int.ofNat (0#32).toNat == 0) : Bool) = true := rfl
    have hb0 : (0#32 == 0#32) = true := rfl
    rw [hr0, hb0]
    simp only [↓reduceIte]
    decide
  · have hb_ne : (rhs == 0#32) = false := beq_false_of_ne hr
    have hr_nat_ne : rhs.toNat ≠ 0 := fun h => hr (BitVec.eq_of_toNat_eq h)
    have hr_int_ne : Int.ofNat rhs.toNat ≠ 0 := fun h => hr_nat_ne (Int.ofNat.inj h)
    have hr_int_beq : ((Int.ofNat rhs.toNat == 0) : Bool) = false := beq_false_of_ne hr_int_ne
    rw [hb_ne, hr_int_beq]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have htdiv : Int.tdiv (Int.ofNat lhs.toNat) (Int.ofNat rhs.toNat) = Int.ofNat (lhs.toNat / rhs.toNat) := rfl
    rw [htdiv, ofInt_ofNat_eq_ofNat]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.udiv_def, BitVec.toNat_ofNat]

/-- RV64M signed `REMW` bisimulation (`is_unsigned = false`), including `/ 0` (`lhs.signExtend 64`)
    and `-2^31 % -1` (`0#64`). -/
theorem riscvRemwSpec_bisim_sail (rs1_full rs2_full : BitVec 64) :
    riscvRemwSpec rs1_full rs2_full = sailRemwCore false rs1_full rs2_full := by
  dsimp only [riscvRemwSpec, sailRemwCore, sign_extend, Sail.BitVec.signExtend]
  rw [extractLsb_31_0_eq_truncate32, extractLsb_31_0_eq_truncate32, to_bits_truncate_eq_ofInt]
  generalize rs1_full.truncate 32 = lhs
  generalize rs2_full.truncate 32 = rhs
  simp only [Bool.false_eq_true, ↓reduceIte]
  congr 1
  by_cases hr : rhs = 0#32
  · subst hr
    have hr0 : ((0#32).toInt == 0) = true := rfl
    have hb0 : (0#32 == 0#32) = true := rfl
    rw [hr0, hb0]
    simp only [↓reduceIte, BitVec.ofInt_toInt]
  · have hb_ne : (rhs == 0#32) = false := beq_false_of_ne hr
    have hr_int_ne : rhs.toInt ≠ 0 := fun h => hr ((toInt_eq_zero_iff_32 rhs).mp h)
    have hr_int_beq : ((rhs.toInt == 0) : Bool) = false := beq_false_of_ne hr_int_ne
    rw [hb_ne, hr_int_beq]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hovf : lhs = BitVec.intMin 32 ∧ rhs = BitVec.allOnes 32
    · rcases hovf with ⟨rfl, rfl⟩
      decide
    · have hcond_false : (lhs == BitVec.intMin 32 && rhs == BitVec.allOnes 32) = false := by
        cases h1 : (lhs == BitVec.intMin 32) <;> cases h2 : (rhs == BitVec.allOnes 32) <;> simp_all
      rw [hcond_false]
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply BitVec.eq_of_toInt_eq
      rw [BitVec.toInt_srem, BitVec.toInt_ofInt, ← BitVec.toInt_srem, BitVec.toInt_bmod_cancel]

/-- RV64M unsigned `REMUW` bisimulation (`is_unsigned = true`), including `/ 0` (`lhs.signExtend 64`). -/
theorem riscvRemuwSpec_bisim_sail (rs1_full rs2_full : BitVec 64) :
    riscvRemuwSpec rs1_full rs2_full = sailRemwCore true rs1_full rs2_full := by
  dsimp only [riscvRemuwSpec, sailRemwCore, sign_extend, Sail.BitVec.signExtend, Sail.BitVec.toNatInt]
  rw [extractLsb_31_0_eq_truncate32, extractLsb_31_0_eq_truncate32, to_bits_truncate_eq_ofInt]
  generalize rs1_full.truncate 32 = lhs
  generalize rs2_full.truncate 32 = rhs
  simp only [↓reduceIte]
  congr 1
  by_cases hr : rhs = 0#32
  · subst hr
    have hr0 : ((Int.ofNat (0#32).toNat == 0) : Bool) = true := rfl
    have hb0 : (0#32 == 0#32) = true := rfl
    rw [hr0, hb0]
    simp only [↓reduceIte]
    rw [ofInt_ofNat_eq_ofNat]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lhs.isLt]
  · have hb_ne : (rhs == 0#32) = false := beq_false_of_ne hr
    have hr_nat_ne : rhs.toNat ≠ 0 := fun h => hr (BitVec.eq_of_toNat_eq h)
    have hr_int_ne : Int.ofNat rhs.toNat ≠ 0 := fun h => hr_nat_ne (Int.ofNat.inj h)
    have hr_int_beq : ((Int.ofNat rhs.toNat == 0) : Bool) = false := beq_false_of_ne hr_int_ne
    rw [hb_ne, hr_int_beq]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have htmod : Int.tmod (Int.ofNat lhs.toNat) (Int.ofNat rhs.toNat) = Int.ofNat (lhs.toNat % rhs.toNat) := rfl
    rw [htmod, ofInt_ofNat_eq_ofNat]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.umod_def, BitVec.toNat_ofNat]

/-- RV64M 32-bit word Euclidean division-remainder laws for both signed (`DIVW`/`REMW` via
    `riscvMulwSpec`) and unsigned (`DIVUW`/`REMUW` via `riscvMulwSpec`) across all 64-bit inputs. -/
theorem riscvDivRemW_euclidean (rs1_full rs2_full : BitVec 64) :
    ((riscvMulwSpec (riscvDivwSpec rs1_full rs2_full) rs2_full +
        riscvRemwSpec rs1_full rs2_full).truncate 32).signExtend 64 =
      (rs1_full.truncate 32).signExtend 64 ∧
    ((riscvMulwSpec (riscvDivuwSpec rs1_full rs2_full) rs2_full +
        riscvRemuwSpec rs1_full rs2_full).truncate 32).signExtend 64 =
      (rs1_full.truncate 32).signExtend 64 := by
  constructor
  · rw [truncate32_add, riscvMulwSpec, truncate32_signExtend64]
    dsimp only [riscvDivwSpec, riscvRemwSpec]
    rw [truncate32_signExtend64, truncate32_signExtend64]
    congr 1
    generalize rs1_full.truncate 32 = lhs
    generalize rs2_full.truncate 32 = rhs
    by_cases hr : rhs = 0#32
    · subst hr; simp
    · have hb_ne : (rhs == 0#32) = false := beq_false_of_ne hr
      rw [hb_ne]
      simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hovf : lhs = BitVec.intMin 32 ∧ rhs = BitVec.allOnes 32
      · rcases hovf with ⟨rfl, rfl⟩; decide
      · have hcond_false : (lhs == BitVec.intMin 32 && rhs == BitVec.allOnes 32) = false := by
          cases h1 : (lhs == BitVec.intMin 32) <;> cases h2 : (rhs == BitVec.allOnes 32) <;> simp_all
        rw [hcond_false]
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hsdiv : lhs.sdiv rhs = BitVec.ofInt 32 (Int.tdiv lhs.toInt rhs.toInt) := by
          apply BitVec.eq_of_toInt_eq
          rw [BitVec.toInt_sdiv, BitVec.toInt_ofInt]
        have hsrem : lhs.srem rhs = BitVec.ofInt 32 (Int.tmod lhs.toInt rhs.toInt) := by
          apply BitVec.eq_of_toInt_eq
          rw [BitVec.toInt_srem, BitVec.toInt_ofInt, ← BitVec.toInt_srem, BitVec.toInt_bmod_cancel]
        rw [hsdiv, hsrem]
        have h_rhs : rhs = BitVec.ofInt 32 rhs.toInt := BitVec.ofInt_toInt.symm
        conv => lhs; arg 1; arg 2; rw [h_rhs]
        rw [← BitVec.ofInt_mul, ← BitVec.ofInt_add, Int.mul_comm, Int.mul_tdiv_add_tmod, BitVec.ofInt_toInt]
  · rw [truncate32_add, riscvMulwSpec, truncate32_signExtend64]
    dsimp only [riscvDivuwSpec, riscvRemuwSpec]
    rw [truncate32_signExtend64, truncate32_signExtend64]
    congr 1
    generalize rs1_full.truncate 32 = lhs
    generalize rs2_full.truncate 32 = rhs
    by_cases hr : rhs = 0#32
    · subst hr; simp
    · have hb_ne : (rhs == 0#32) = false := beq_false_of_ne hr
      rw [hb_ne]
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.udiv_def, BitVec.umod_def, BitVec.toNat_ofNat]
      have hlt : lhs.toNat < 2 ^ 32 := lhs.isLt
      have hq_lt : lhs.toNat / rhs.toNat < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlt
      have hr_lt : lhs.toNat % rhs.toNat < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.mod_le _ _) hlt
      rw [Nat.mod_eq_of_lt hq_lt, Nat.mod_eq_of_lt hr_lt, Nat.mod_add_mod]
      have hdiv : (lhs.toNat / rhs.toNat) * rhs.toNat + lhs.toNat % rhs.toNat = lhs.toNat := by
        rw [Nat.mul_comm]
        exact Nat.div_add_mod lhs.toNat rhs.toNat
      rw [hdiv, Nat.mod_eq_of_lt hlt]

/-! ## 10. RV64I Unconditional Control Flow (`JAL`, `JALR`, and `PcAccess` State Transitions) -/

/-- Exact upstream Sail `execute_JAL` link/target core (`LeanRV64D/InstsEnd.lean`, lines 69258–69265),
    returning `(link_address, target)` for a non-compressed 32-bit instruction at `pc`
    (`nextPC = pc + 4#64`). -/
def sailJalCore (pc : BitVec 64) (imm : BitVec 21) : BitVec 64 × BitVec 64 :=
  let link_address : BitVec 64 := pc + 4#64
  let target : BitVec 64 := pc + sign_extend (m := 64) imm
  (link_address, target)

/-- Pure `TurboLean`-side RV64I `JAL` specification: `(pc + 4, pc + sext(imm))`. -/
def rv64iJalSpec (pc : BitVec 64) (imm : BitVec 21) : BitVec 64 × BitVec 64 :=
  (pc + 4#64, pc + imm.signExtend 64)

/-- Exact upstream Sail `execute_JALR` link/target core (`LeanRV64D/InstsEnd.lean`, lines 69247–69256),
    returning `(link_address, BitVec.update target 0 0#1)` for a non-compressed 32-bit instruction
    at `pc` (`nextPC = pc + 4#64`). -/
def sailJalrCore (pc rs1_val : BitVec 64) (imm : BitVec 12) : BitVec 64 × BitVec 64 :=
  let link_address : BitVec 64 := pc + 4#64
  let target : BitVec 64 := rs1_val + sign_extend (m := 64) imm
  (link_address, Sail.BitVec.update target 0 0#1)

/-- Pure `TurboLean`-side RV64I `JALR` specification: `(pc + 4, (rs1_val + sext(imm)) &&& ~1)`,
    masking bit 0 of the computed target address to zero per the RISC-V unprivileged ISA. -/
def rv64iJalrSpec (pc rs1_val : BitVec 64) (imm : BitVec 12) : BitVec 64 × BitVec 64 :=
  (pc + 4#64, (rs1_val + imm.signExtend 64) &&& ~~~1#64)

/-- Exact upstream Sail `jump_to` target-alignment check (`LeanRV64D/BaseInsts.lean`, lines 260–270):
    succeeds (without raising `Fetch_Addr_Align` / `Misaligned_Fetch`) iff bit 0 is `0#1` and
    either `Ext_Zca` is enabled or bit 1 is `0#1`. -/
def sailJumpToAlignedCore (zca_enabled : Bool) (target : BitVec 64) : Bool :=
  !(Sail.BitVec.access target 0 != 0#1) &&
    !((Sail.BitVec.access target 1 != 0#1) && LeanRV64D.Functions.not zca_enabled)

/-- Pure `TurboLean`-side jump-target alignment specification: 2-byte aligned (`% 2 == 0`) when
    `Zca` is enabled, and 4-byte aligned (`% 4 == 0`) when `Zca` is disabled. -/
def rv64iJumpTargetAlignedSpec (zca_enabled : Bool) (target : BitVec 64) : Bool :=
  if zca_enabled then target.toNat % 2 == 0 else target.toNat % 4 == 0

/-- RV64I `JAL` pure link-and-target bisimulation against `sailJalCore`. -/
theorem rv64iJalSpec_bisim_sail (pc : BitVec 64) (imm : BitVec 21) :
    rv64iJalSpec pc imm = sailJalCore pc imm :=
  rfl

/-- RV64I `JALR` pure link-and-target bisimulation against `sailJalrCore`, proving that Sail's
    `Sail.BitVec.update target 0 0#1` equals `(rs1_val + imm.signExtend 64) &&& ~~~1#64` and
    unconditionally clears bit 0 of the target address. -/
theorem rv64iJalrSpec_bisim_sail (pc rs1_val : BitVec 64) (imm : BitVec 12) :
    rv64iJalrSpec pc rs1_val imm = sailJalrCore pc rs1_val imm ∧
      (sailJalrCore pc rs1_val imm).2.getLsbD 0 = false := by
  have hupd : ∀ (t : BitVec 64), Sail.BitVec.update t 0 0#1 = t &&& ~~~1#64 := by
    intro t
    unfold Sail.BitVec.update Sail.BitVec.updateSubrange'
    have hmask : ~~~(BitVec.zeroExtend 64 (BitVec.allOnes 1) <<< 0) = ~~~1#64 := by decide
    have hz : BitVec.zeroExtend 64 0#1 <<< 0 = 0#64 := by decide
    rw [hmask, hz, BitVec.or_zero, BitVec.and_comm]
  constructor
  · dsimp only [rv64iJalrSpec, sailJalrCore, sign_extend, Sail.BitVec.signExtend]
    rw [hupd]
  · dsimp only [sailJalrCore, sign_extend, Sail.BitVec.signExtend]
    rw [hupd]
    simp

/-- RV64I `jump_to` target-alignment bisimulation: Sail's bit-level `access target 0` and
    `access target 1` guards match `target.toNat % 2 == 0` (`Zca` enabled) and
    `target.toNat % 4 == 0` (`Zca` disabled). -/
theorem rv64iJumpTargetAlignedSpec_bisim_sail (zca_enabled : Bool) (target : BitVec 64) :
    rv64iJumpTargetAlignedSpec zca_enabled target = sailJumpToAlignedCore zca_enabled target := by
  unfold rv64iJumpTargetAlignedSpec sailJumpToAlignedCore Sail.BitVec.access LeanRV64D.Functions.not
  have hget0 : target[0]! = target.toNat.testBit 0 := by
    change target.getLsbD 0 = target.toNat.testBit 0
    rfl
  have hget1 : target[1]! = target.toNat.testBit 1 := by
    change target.getLsbD 1 = target.toNat.testBit 1
    rfl
  rw [hget0, hget1, Nat.testBit_zero, Nat.testBit_succ, Nat.testBit_zero]
  have hmod2 : target.toNat % 2 = 0 ∨ target.toNat % 2 = 1 := by omega
  have hdiv2 : (target.toNat / 2) % 2 = 0 ∨ (target.toNat / 2) % 2 = 1 := by omega
  cases zca_enabled <;> rcases hmod2 with h0 | h0 <;> rcases hdiv2 with h1 | h1
  all_goals
    have hmod4 : (target.toNat % 4 == 0) = decide (target.toNat % 2 = 0 ∧ (target.toNat / 2) % 2 = 0) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq]
      omega
    try rw [hmod4]
    simp [h0, h1]

private theorem estate_pure_def {ε σ α : Type} (a : α) (s : σ) :
    (EStateM.pure (ε := ε) a) s = .ok a s := rfl

/-- Monadic `LeanRV64D.PcAccess` redirect-and-tick law: calling `set_next_pc target` followed by
    `tick_pc ()` updates both `nextPC` and `PC` in `SequentialState` so `get_arch_pc ()` returns `target`. -/
theorem pcAccess_redirect_and_tick_bisim (target : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource) :
    ((do
        set_next_pc target
        tick_pc ()
        get_arch_pc ()).run s) =
      .ok target { s with regs := (s.regs.insert .nextPC target).insert .PC target } := by
  simp [set_next_pc, tick_pc, get_arch_pc, redirect_callback, pc_write_callback,
    writeReg, PreSail.writeReg, readReg, PreSail.readReg,
    modify, modifyGet, MonadStateOf.modifyGet, get, getThe, MonadStateOf.get]
  dsimp [EStateM.modifyGet, EStateM.get, EStateM.pure, EStateM.run]
  simp [Std.ExtDHashMap.get?_insert_self, Pure.pure, estate_pure_def]

/-- End-to-end `SailM` state-transition bisimulation for `JAL x1, imm`: starting with `.PC = pc`
    and non-compressed fetch fallthrough `.nextPC = pc + 4#64`, reading link/PC, redirecting to
    `target`, writing link to `x1`, and ticking `PC` yields `(rX_bits x1, get_arch_pc ()) = rv64iJalSpec pc imm`. -/
theorem jal_x1_state_bisim_sail (pc : BitVec 64) (imm : BitVec 21)
    (s : SequentialState RegisterType trivialChoiceSource) :
    ((do
        writeReg .PC pc
        set_next_pc (pc + 4#64)
        let link_address ← get_next_pc ()
        let target := (← get_arch_pc ()) + sign_extend (m := 64) imm
        set_next_pc target
        wX_bits (.Regidx 1#5) link_address
        tick_pc ()
        let ra ← rX_bits (.Regidx 1#5)
        let pc' ← get_arch_pc ()
        pure (ra, pc')).run s) =
      .ok (rv64iJalSpec pc imm)
        { s with regs := (((((s.regs.insert .PC pc).insert .nextPC (pc + 4#64)).insert
            .nextPC (pc + imm.signExtend 64)).insert .x1 (pc + 4#64)).insert
            .PC (pc + imm.signExtend 64)) } := by
  simp [rv64iJalSpec, set_next_pc, get_next_pc, get_arch_pc, tick_pc,
    redirect_callback, pc_write_callback,
    wX_bits, rX_bits, wX, rX, regval_into_reg, regval_from_reg,
    xreg_write_callback, reg_name_forwards, encdec_reg_forwards_matches,
    encdec_reg_forwards, get_config_use_abi_names, LeanRV64D.Functions.not,
    reg_arch_name_raw_forwards, xreg_full_write_callback,
    sign_extend, Sail.BitVec.signExtend, zero_extend, Sail.BitVec.zeroExtend,
    Sail.BitVec.toNatInt, to_bits, get_slice_int,
    writeReg, PreSail.writeReg, readReg, PreSail.readReg,
    modify, modifyGet, MonadStateOf.modifyGet, get, getThe, MonadStateOf.get]
  dsimp [EStateM.modifyGet, EStateM.get, EStateM.pure, EStateM.map, EStateM.run, Functor.map]
  simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self, Pure.pure, estate_pure_def]

/-- End-to-end `SailM` state-transition bisimulation for `JALR x1, x1, imm` (`rd = rs1 = x1`):
    proves Sail reads the pre-call `x1` value (`rs1_val`) to compute the LSB-cleared jump target
    before overwriting `x1` with the return address `pc + 4#64`. -/
theorem jalr_same_reg_x1_state_bisim_sail (pc rs1_val : BitVec 64) (imm : BitVec 12)
    (s : SequentialState RegisterType trivialChoiceSource) :
    ((do
        writeReg .PC pc
        wX_bits (.Regidx 1#5) rs1_val
        set_next_pc (pc + 4#64)
        let link_address ← get_next_pc ()
        let target := (← rX_bits (.Regidx 1#5)) + sign_extend (m := 64) imm
        set_next_pc (Sail.BitVec.update target 0 0#1)
        wX_bits (.Regidx 1#5) link_address
        tick_pc ()
        let ra ← rX_bits (.Regidx 1#5)
        let pc' ← get_arch_pc ()
        pure (ra, pc')).run s) =
      .ok (rv64iJalrSpec pc rs1_val imm)
        { s with regs := ((((((s.regs.insert .PC pc).insert .x1 rs1_val).insert .nextPC (pc + 4#64)).insert
            .nextPC (Sail.BitVec.update (rs1_val + imm.signExtend 64) 0 0#1)).insert
            .x1 (pc + 4#64)).insert
            .PC (Sail.BitVec.update (rs1_val + imm.signExtend 64) 0 0#1)) } := by
  have hpair := (rv64iJalrSpec_bisim_sail pc rs1_val imm).1
  rw [hpair]
  simp [sailJalrCore, set_next_pc, get_next_pc, get_arch_pc, tick_pc,
    redirect_callback, pc_write_callback,
    wX_bits, rX_bits, wX, rX, regval_into_reg, regval_from_reg,
    xreg_write_callback, reg_name_forwards, encdec_reg_forwards_matches,
    encdec_reg_forwards, get_config_use_abi_names, LeanRV64D.Functions.not,
    reg_arch_name_raw_forwards, xreg_full_write_callback,
    sign_extend, Sail.BitVec.signExtend, zero_extend, Sail.BitVec.zeroExtend,
    Sail.BitVec.toNatInt, to_bits, get_slice_int,
    writeReg, PreSail.writeReg, readReg, PreSail.readReg,
    modify, modifyGet, MonadStateOf.modifyGet, get, getThe, MonadStateOf.get]
  dsimp [EStateM.modifyGet, EStateM.get, EStateM.pure, EStateM.map, EStateM.run, Functor.map]
  simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self, Pure.pure, estate_pure_def]

/-! ## 11. RV64 Bit-Manipulation Extensions (`Zba`, `Zbs`, and `Zbb`) -/

/-- Exact upstream Sail `execute_ZBA_RTYPE` functional core (`LeanRV64D/InstsEnd.lean`, lines 62569–62572),
    covering `SH1ADD` (`shamt = 1#2`), `SH2ADD` (`shamt = 2#2`), and `SH3ADD` (`shamt = 3#2`). -/
def sailZbaRtypeCore (shamt : BitVec 2) (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  (rs1_val <<< shamt) + rs2_val

/-- Pure `TurboLean`-side RV64 Zba `SH1ADD`/`SH2ADD`/`SH3ADD` specification. -/
def rv64ZbaRtypeSpec (shamt : BitVec 2) (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  (rs1_val <<< shamt.toNat) + rs2_val

/-- Exact upstream Sail `execute_ZBA_RTYPEUW` functional core (`LeanRV64D/InstsEnd.lean`, lines 62563–62567),
    covering `ADD.UW` (`0#2`), `SH1ADD.UW` (`1#2`), `SH2ADD.UW` (`2#2`), and `SH3ADD.UW` (`3#2`). -/
def sailZbaRtypeuwCore (shamt : BitVec 2) (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  ((zero_extend (m := 64) (Sail.BitVec.extractLsb rs1_val 31 0)) <<< shamt) + rs2_val

/-- Pure `TurboLean`-side RV64 Zba `ADD.UW`/`SH1ADD.UW`/`SH2ADD.UW`/`SH3ADD.UW` specification. -/
def rv64ZbaRtypeuwSpec (shamt : BitVec 2) (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  ((rs1_val.truncate 32).zeroExtend 64 <<< shamt.toNat) + rs2_val

/-- Exact upstream Sail `execute_SLLIUW` functional core (`LeanRV64D/InstsEnd.lean`, lines 67593–67596),
    covering `SLLI.UW`. -/
def sailSlliuwCore (shamt : BitVec 6) (rs1_val : BitVec 64) : BitVec 64 :=
  (zero_extend (m := 64) (Sail.BitVec.extractLsb rs1_val 31 0)) <<< shamt

/-- Pure `TurboLean`-side RV64 Zba `SLLI.UW` specification. -/
def rv64ZbaSlliuwSpec (shamt : BitVec 6) (rs1_val : BitVec 64) : BitVec 64 :=
  (rs1_val.truncate 32).zeroExtend 64 <<< shamt.toNat

/-- RV64 Zba bisimulation across `ZBA_RTYPE` (`SH1ADD`/`SH2ADD`/`SH3ADD`),
    `ZBA_RTYPEUW` (`ADD.UW`/`SH1ADD.UW`/`SH2ADD.UW`/`SH3ADD.UW`), and `SLLI.UW`. -/
theorem rv64Zba_bisim_sail (shamt2 : BitVec 2) (shamt6 : BitVec 6) (rs1_val rs2_val : BitVec 64) :
    rv64ZbaRtypeSpec shamt2 rs1_val rs2_val = sailZbaRtypeCore shamt2 rs1_val rs2_val ∧
      rv64ZbaRtypeuwSpec shamt2 rs1_val rs2_val = sailZbaRtypeuwCore shamt2 rs1_val rs2_val ∧
      rv64ZbaSlliuwSpec shamt6 rs1_val = sailSlliuwCore shamt6 rs1_val := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [rv64ZbaRtypeSpec, sailZbaRtypeCore]
    rw [BitVec.shiftLeft_eq']
  · dsimp only [rv64ZbaRtypeuwSpec, sailZbaRtypeuwCore, zero_extend, Sail.BitVec.zeroExtend]
    rw [BitVec.shiftLeft_eq', extractLsb_31_0_eq_truncate32]
  · dsimp only [rv64ZbaSlliuwSpec, sailSlliuwCore, zero_extend, Sail.BitVec.zeroExtend]
    rw [BitVec.shiftLeft_eq', extractLsb_31_0_eq_truncate32]

/-- Exact upstream Sail `execute_ZBS_RTYPE` functional core (`LeanRV64D/InstsEnd.lean`, lines 62465–62477),
    covering `BCLR`, `BEXT`, `BINV`, and `BSET`. -/
def sailZbsRtypeCore (op : brop_zbs) (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  let mask : BitVec 64 :=
    shift_bits_left (zero_extend (m := 64) 1#1) (Sail.BitVec.extractLsb rs2_val (Functions.log2_xlen -i 1) 0)
  match op with
  | .BCLR => rs1_val &&& ~~~mask
  | .BEXT => zero_extend (m := 64) (bool_bit_forwards ((rs1_val &&& mask) != zeros (n := 64)))
  | .BINV => rs1_val ^^^ mask
  | .BSET => rs1_val ||| mask

/-- Pure `TurboLean`-side RV64 Zbs `ZBS_RTYPE` specification (`BCLR`, `BEXT` via direct bit-test
    `getLsbD`, `BINV`, `BSET`). -/
def rv64ZbsRtypeSpec (op : brop_zbs) (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  let idx : Nat := rs2_val.toNat % 64
  match op with
  | .BCLR => rs1_val &&& ~~~(1#64 <<< idx)
  | .BEXT => if rs1_val.getLsbD idx then 1#64 else 0#64
  | .BINV => rs1_val ^^^ (1#64 <<< idx)
  | .BSET => rs1_val ||| (1#64 <<< idx)

/-- Exact upstream Sail `execute_ZBS_IOP` functional core (`LeanRV64D/InstsEnd.lean`, lines 62479–62489),
    covering `BCLRI`, `BEXTI`, `BINVI`, and `BSETI`. -/
def sailZbsIopCore (op : biop_zbs) (rs1_val : BitVec 64) (shamt : BitVec 6) : BitVec 64 :=
  let mask : BitVec 64 := shift_bits_left (zero_extend (m := 64) 1#1) shamt
  match op with
  | .BCLRI => rs1_val &&& ~~~mask
  | .BEXTI => zero_extend (m := 64) (bool_bit_forwards ((rs1_val &&& mask) != zeros (n := 64)))
  | .BINVI => rs1_val ^^^ mask
  | .BSETI => rs1_val ||| mask

/-- Pure `TurboLean`-side RV64 Zbs `ZBS_IOP` specification (`BCLRI`, `BEXTI` via direct bit-test
    `getLsbD`, `BINVI`, `BSETI`). -/
def rv64ZbsIopSpec (op : biop_zbs) (rs1_val : BitVec 64) (shamt : BitVec 6) : BitVec 64 :=
  let idx : Nat := shamt.toNat
  match op with
  | .BCLRI => rs1_val &&& ~~~(1#64 <<< idx)
  | .BEXTI => if rs1_val.getLsbD idx then 1#64 else 0#64
  | .BINVI => rs1_val ^^^ (1#64 <<< idx)
  | .BSETI => rs1_val ||| (1#64 <<< idx)

private theorem mask_and_bne_zero_eq_getLsbD (x : BitVec 64) (idx : Nat) (hidx : idx < 64) :
    ((x &&& (1#64 <<< idx)) != 0#64) = x.getLsbD idx := by
  have hone_bit : ∀ k, k < 64 → (1#64 <<< idx).getLsbD k = decide (k = idx) := by
    intro k hk
    rw [BitVec.getLsbD_shiftLeft]
    by_cases hlt : k < idx
    · simp [hk, hlt, show k ≠ idx by omega]
    · by_cases heq : k = idx
      · subst heq; simp [hk]
      · have hgt : k - idx > 0 := by omega
        cases hm : k - idx with
        | zero => omega
        | succ m =>
          rw [BitVec.getLsbD_ofNat]
          simp [hk, hlt, heq, Nat.testBit_succ]
  cases hbit : x.getLsbD idx with
  | false =>
    have hzero : x &&& (1#64 <<< idx) = 0#64 := by
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      rw [BitVec.getLsbD_and, hone_bit k hk]
      by_cases heq : k = idx
      · subst heq; simp [hbit]
      · simp [heq]
    simp [hzero]
  | true =>
    have hne : x &&& (1#64 <<< idx) ≠ 0#64 := by
      intro h0
      have hidx_bit := congrArg (fun v : BitVec 64 => v.getLsbD idx) h0
      dsimp only at hidx_bit
      rw [BitVec.getLsbD_and, hone_bit idx hidx] at hidx_bit
      simp [hbit] at hidx_bit
    exact bne_iff_ne.mpr hne

/-- RV64 Zbs register (`BCLR`/`BEXT`/`BINV`/`BSET`) and immediate (`BCLRI`/`BEXTI`/`BINVI`/`BSETI`)
    bisimulation against upstream `execute_ZBS_RTYPE` and `execute_ZBS_IOP`. -/
theorem rv64Zbs_bisim_sail (rop : brop_zbs) (iop : biop_zbs)
    (rs1_val rs2_val : BitVec 64) (shamt : BitVec 6) :
    rv64ZbsRtypeSpec rop rs1_val rs2_val = sailZbsRtypeCore rop rs1_val rs2_val ∧
      rv64ZbsIopSpec iop rs1_val shamt = sailZbsIopCore iop rs1_val shamt := by
  have hz1 : zero_extend (m := 64) 1#1 = 1#64 := by decide
  have hz64 : zeros (n := 64) = 0#64 := rfl
  have hextr6 : (Sail.BitVec.extractLsb rs2_val (Functions.log2_xlen -i 1) 0).toNat = rs2_val.toNat % 64 := by
    change (BitVec.extractLsb 5 0 rs2_val).toNat = rs2_val.toNat % 64
    rw [BitVec.extractLsb_toNat, Nat.shiftRight_zero]
  constructor
  · cases rop with
    | BCLR | BINV | BSET =>
      dsimp only [rv64ZbsRtypeSpec, sailZbsRtypeCore, shift_bits_left]
      rw [hz1, BitVec.shiftLeft_eq', hextr6]
    | BEXT =>
      dsimp only [rv64ZbsRtypeSpec, sailZbsRtypeCore, shift_bits_left]
      rw [hz1, hz64, BitVec.shiftLeft_eq', hextr6,
        mask_and_bne_zero_eq_getLsbD rs1_val (rs2_val.toNat % 64) (Nat.mod_lt _ (by decide))]
      cases rs1_val.getLsbD (rs2_val.toNat % 64) <;> decide
  · cases iop with
    | BCLRI | BINVI | BSETI =>
      dsimp only [rv64ZbsIopSpec, sailZbsIopCore, shift_bits_left]
      rw [hz1, BitVec.shiftLeft_eq']
    | BEXTI =>
      dsimp only [rv64ZbsIopSpec, sailZbsIopCore, shift_bits_left]
      rw [hz1, hz64, BitVec.shiftLeft_eq', mask_and_bne_zero_eq_getLsbD rs1_val shamt.toNat shamt.isLt]
      cases rs1_val.getLsbD shamt.toNat <;> decide

/-- Exact upstream Sail `execute_ZBB_RTYPE` functional core (`LeanRV64D/InstsEnd.lean`, lines 62524–62551),
    covering `ANDN`, `ORN`, `XNOR`, `MAX`, `MAXU`, `MIN`, `MINU`, `ROL`, and `ROR`. -/
def sailZbbRtypeCore (op : brop_zbb) (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  match op with
  | .ANDN => rs1_val &&& ~~~rs2_val
  | .ORN => rs1_val ||| ~~~rs2_val
  | .XNOR => ~~~(rs1_val ^^^ rs2_val)
  | .MAX => if ((BitVec.toInt rs1_val >b BitVec.toInt rs2_val) : Bool) then rs1_val else rs2_val
  | .MAXU => if ((Sail.BitVec.toNatInt rs1_val >b Sail.BitVec.toNatInt rs2_val) : Bool) then rs1_val else rs2_val
  | .MIN => if ((BitVec.toInt rs1_val <b BitVec.toInt rs2_val) : Bool) then rs1_val else rs2_val
  | .MINU => if ((Sail.BitVec.toNatInt rs1_val <b Sail.BitVec.toNatInt rs2_val) : Bool) then rs1_val else rs2_val
  | .ROL => BitVec.rotateLeft rs1_val (BitVec.toNat (Sail.BitVec.extractLsb rs2_val (Functions.log2_xlen -i 1) 0))
  | .ROR => BitVec.rotateRight rs1_val (BitVec.toNat (Sail.BitVec.extractLsb rs2_val (Functions.log2_xlen -i 1) 0))

/-- Pure `TurboLean`-side RV64 Zbb `ZBB_RTYPE` specification using native `BitVec.slt`, `BitVec.ult`,
    and `% 64` rotation amounts. -/
def rv64ZbbRtypeSpec (op : brop_zbb) (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  match op with
  | .ANDN => rs1_val &&& ~~~rs2_val
  | .ORN => rs1_val ||| ~~~rs2_val
  | .XNOR => ~~~(rs1_val ^^^ rs2_val)
  | .MAX => if BitVec.slt rs2_val rs1_val then rs1_val else rs2_val
  | .MAXU => if BitVec.ult rs2_val rs1_val then rs1_val else rs2_val
  | .MIN => if BitVec.slt rs1_val rs2_val then rs1_val else rs2_val
  | .MINU => if BitVec.ult rs1_val rs2_val then rs1_val else rs2_val
  | .ROL => BitVec.rotateLeft rs1_val (rs2_val.toNat % 64)
  | .ROR => BitVec.rotateRight rs1_val (rs2_val.toNat % 64)

/-- Exact upstream Sail `execute_ZBB_RTYPEW` functional core (`LeanRV64D/InstsEnd.lean`, lines 62514–62522),
    covering `ROLW` and `RORW`. -/
def sailZbbRtypewCore (op : bropw_zbb) (rs1_full rs2_full : BitVec 64) : BitVec 64 :=
  let rs1_val : BitVec 32 := Sail.BitVec.extractLsb rs1_full 31 0
  let shamt : BitVec 5 := Sail.BitVec.extractLsb rs2_full 4 0
  let result : BitVec 32 :=
    match op with
    | .ROLW => BitVec.rotateLeft rs1_val (BitVec.toNat shamt)
    | .RORW => BitVec.rotateRight rs1_val (BitVec.toNat shamt)
  sign_extend (m := 64) result

/-- Pure `TurboLean`-side RV64 Zbb `ROLW` / `RORW` specification. -/
def rv64ZbbRtypewSpec (op : bropw_zbb) (rs1_full rs2_full : BitVec 64) : BitVec 64 :=
  let rs1_val : BitVec 32 := rs1_full.truncate 32
  let res32 : BitVec 32 :=
    match op with
    | .ROLW => BitVec.rotateLeft rs1_val (rs2_full.toNat % 32)
    | .RORW => BitVec.rotateRight rs1_val (rs2_full.toNat % 32)
  res32.signExtend 64

/-- Exact upstream Sail `execute_RORI` (`InstsEnd.lean`, lines 67805–67809) and `execute_RORIW`
    (`InstsEnd.lean`, lines 67799–67803) functional cores. -/
def sailRoriCore (shamt : BitVec 6) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.rotateRight rs1_val (BitVec.toNat shamt)

def sailRoriwCore (shamt : BitVec 5) (rs1_full : BitVec 64) : BitVec 64 :=
  let rs1_val : BitVec 32 := Sail.BitVec.extractLsb rs1_full 31 0
  sign_extend (m := 64) (BitVec.rotateRight rs1_val (BitVec.toNat shamt))

/-- Pure `TurboLean`-side RV64 Zbb `RORI` and `RORIW` specifications. -/
def rv64ZbbRoriSpec (shamt : BitVec 6) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.rotateRight rs1_val shamt.toNat

def rv64ZbbRoriwSpec (shamt : BitVec 5) (rs1_full : BitVec 64) : BitVec 64 :=
  (BitVec.rotateRight (rs1_full.truncate 32) shamt.toNat).signExtend 64

/-- Exact upstream Sail `execute_ZBB_EXTOP` functional core (`LeanRV64D/InstsEnd.lean`, lines 62553–62561),
    covering `SEXT.B`, `SEXT.H`, and `ZEXT.H`. -/
def sailZbbExtopCore (op : extop_zbb) (rs1_val : BitVec 64) : BitVec 64 :=
  match op with
  | .SEXTB => sign_extend (m := 64) (Sail.BitVec.extractLsb rs1_val 7 0)
  | .SEXTH => sign_extend (m := 64) (Sail.BitVec.extractLsb rs1_val 15 0)
  | .ZEXTH => zero_extend (m := 64) (Sail.BitVec.extractLsb rs1_val 15 0)

/-- Pure `TurboLean`-side RV64 Zbb `SEXT.B`, `SEXT.H`, and `ZEXT.H` specification. -/
def rv64ZbbExtopSpec (op : extop_zbb) (rs1_val : BitVec 64) : BitVec 64 :=
  match op with
  | .SEXTB => (rs1_val.truncate 8).signExtend 64
  | .SEXTH => (rs1_val.truncate 16).signExtend 64
  | .ZEXTH => (rs1_val.truncate 16).zeroExtend 64

/-- RV64 Zbb ALU/min-max/rotate/extend bisimulation covering `ZBB_RTYPE` (`ANDN`, `ORN`, `XNOR`,
    `MAX`, `MAXU`, `MIN`, `MINU`, `ROL`, `ROR`), `ZBB_RTYPEW` (`ROLW`, `RORW`), `RORI`, `RORIW`,
    and `ZBB_EXTOP` (`SEXT.B`, `SEXT.H`, `ZEXT.H`). -/
theorem rv64ZbbAluRotExt_bisim_sail (op : brop_zbb) (wop : bropw_zbb) (eop : extop_zbb)
    (rs1_val rs2_val : BitVec 64) (shamt6 : BitVec 6) (shamt5 : BitVec 5) :
    rv64ZbbRtypeSpec op rs1_val rs2_val = sailZbbRtypeCore op rs1_val rs2_val ∧
      rv64ZbbRtypewSpec wop rs1_val rs2_val = sailZbbRtypewCore wop rs1_val rs2_val ∧
      rv64ZbbRoriSpec shamt6 rs1_val = sailRoriCore shamt6 rs1_val ∧
      rv64ZbbRoriwSpec shamt5 rs1_val = sailRoriwCore shamt5 rs1_val ∧
      rv64ZbbExtopSpec eop rs1_val = sailZbbExtopCore eop rs1_val := by
  have hextr6 : (Sail.BitVec.extractLsb rs2_val (Functions.log2_xlen -i 1) 0).toNat = rs2_val.toNat % 64 := by
    change (BitVec.extractLsb 5 0 rs2_val).toNat = rs2_val.toNat % 64
    rw [BitVec.extractLsb_toNat, Nat.shiftRight_zero]
  have hextr5 : (Sail.BitVec.extractLsb rs2_val 4 0).toNat = rs2_val.toNat % 32 := by
    change (BitVec.extractLsb 4 0 rs2_val).toNat = rs2_val.toNat % 32
    rw [BitVec.extractLsb_toNat, Nat.shiftRight_zero]
  refine ⟨?_, ?_, rfl, ?_, ?_⟩
  · cases op with
    | ANDN | ORN | XNOR => rfl
    | MAX | MIN =>
      dsimp only [rv64ZbbRtypeSpec, sailZbbRtypeCore, BitVec.slt]
      rfl
    | MAXU =>
      unfold rv64ZbbRtypeSpec sailZbbRtypeCore BitVec.ult Sail.BitVec.toNatInt
      dsimp only
      have hcmp : decide ((Int.ofNat rs2_val.toNat) < (Int.ofNat rs1_val.toNat)) =
          decide (rs2_val.toNat < rs1_val.toNat) :=
        decide_eq_decide.mpr Int.ofNat_lt
      change (if decide (rs2_val.toNat < rs1_val.toNat) = true then rs1_val else rs2_val) =
        (if decide ((Int.ofNat rs2_val.toNat) < (Int.ofNat rs1_val.toNat)) = true then rs1_val else rs2_val)
      rw [hcmp]
    | MINU =>
      unfold rv64ZbbRtypeSpec sailZbbRtypeCore BitVec.ult Sail.BitVec.toNatInt
      dsimp only
      have hcmp : decide ((Int.ofNat rs1_val.toNat) < (Int.ofNat rs2_val.toNat)) =
          decide (rs1_val.toNat < rs2_val.toNat) :=
        decide_eq_decide.mpr Int.ofNat_lt
      change (if decide (rs1_val.toNat < rs2_val.toNat) = true then rs1_val else rs2_val) =
        (if decide ((Int.ofNat rs1_val.toNat) < (Int.ofNat rs2_val.toNat)) = true then rs1_val else rs2_val)
      rw [hcmp]
    | ROL | ROR =>
      dsimp only [rv64ZbbRtypeSpec, sailZbbRtypeCore]
      rw [hextr6]
  · cases wop <;>
    (dsimp only [rv64ZbbRtypewSpec, sailZbbRtypewCore, sign_extend, Sail.BitVec.signExtend];
     rw [hextr5, extractLsb_31_0_eq_truncate32])
  · dsimp only [rv64ZbbRoriwSpec, sailRoriwCore, sign_extend, Sail.BitVec.signExtend]
    rw [extractLsb_31_0_eq_truncate32]
  · cases eop with
    | SEXTB =>
      dsimp only [rv64ZbbExtopSpec, sailZbbExtopCore, sign_extend, Sail.BitVec.signExtend,
        Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb', Nat.shiftRight_zero,
        BitVec.truncate_eq_setWidth]
      exact congrArg (BitVec.signExtend 64) (BitVec.setWidth_eq _).symm
    | SEXTH =>
      dsimp only [rv64ZbbExtopSpec, sailZbbExtopCore, sign_extend, Sail.BitVec.signExtend,
        Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb', Nat.shiftRight_zero,
        BitVec.truncate_eq_setWidth]
      exact congrArg (BitVec.signExtend 64) (BitVec.setWidth_eq _).symm
    | ZEXTH =>
      dsimp only [rv64ZbbExtopSpec, sailZbbExtopCore, zero_extend, Sail.BitVec.zeroExtend,
        Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb', Nat.shiftRight_zero,
        BitVec.truncate_eq_setWidth]
      exact congrArg (BitVec.setWidth 64) (BitVec.setWidth_eq _).symm

private theorem getLsbD_updateSubrange' {w : Nat} (x : BitVec w) (start len : Nat) (y : BitVec len)
    (k : Nat) (hk : k < w) :
    (Sail.BitVec.updateSubrange' x start len y).getLsbD k =
      if start ≤ k ∧ k < start + len then y.getLsbD (k - start) else x.getLsbD k := by
  unfold Sail.BitVec.updateSubrange'
  dsimp only
  rw [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth]
  by_cases hlo : k < start
  · have hcond : ¬(start ≤ k ∧ k < start + len) := by omega
    simp [hk, hlo, hcond]
  · have hsub_lt_w : k - start < w := by omega
    by_cases hhi : k < start + len
    · have hcond : start ≤ k ∧ k < start + len := by omega
      have hsub_lt_len : k - start < len := by omega
      simp [hk, hlo, hcond, hsub_lt_w, hsub_lt_len]
    · have hcond : ¬(start ≤ k ∧ k < start + len) := by omega
      have hsub_ge_len : ¬(k - start < len) := by omega
      have hy_out : y.getLsbD (k - start) = false := BitVec.getLsbD_of_ge y (k - start) (by omega)
      simp [hk, hlo, hcond, hsub_lt_w, BitVec.getLsbD_allOnes, hsub_ge_len, hy_out]

/-- Pure `TurboLean`-side RV64 Zbb `REV8` byte-swap specification: reverses the 8 bytes of a
    64-bit word (`byte j ↦ byte (7 - j)`). -/
def rv64ZbbRev8Spec (x : BitVec 64) : BitVec 64 :=
  ((x.extractLsb' 0 8).zeroExtend 64 <<< 56) |||
  ((x.extractLsb' 8 8).zeroExtend 64 <<< 48) |||
  ((x.extractLsb' 16 8).zeroExtend 64 <<< 40) |||
  ((x.extractLsb' 24 8).zeroExtend 64 <<< 32) |||
  ((x.extractLsb' 32 8).zeroExtend 64 <<< 24) |||
  ((x.extractLsb' 40 8).zeroExtend 64 <<< 16) |||
  ((x.extractLsb' 48 8).zeroExtend 64 <<< 8) |||
  (x.extractLsb' 56 8).zeroExtend 64

private theorem rv64ZbbRev8Spec_getLsbD (x : BitVec 64) (k : Nat) (hk : k < 64) :
    (rv64ZbbRev8Spec x).getLsbD k = x.getLsbD ((7 - k / 8) * 8 + k % 8) := by
  unfold rv64ZbbRev8Spec
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and]
  have hbyte : k / 8 = 0 ∨ k / 8 = 1 ∨ k / 8 = 2 ∨ k / 8 = 3 ∨
      k / 8 = 4 ∨ k / 8 = 5 ∨ k / 8 = 6 ∨ k / 8 = 7 := by omega
  rcases hbyte with hb | hb | hb | hb | hb | hb | hb | hb
  · have hlt8 : k < 8 := by omega
    have hidx : (7 - k / 8) * 8 + k % 8 = 56 + k := by omega
    simp [hidx, hlt8,
      show k < 16 by omega, show k < 24 by omega, show k < 32 by omega,
      show k < 40 by omega, show k < 48 by omega, show k < 56 by omega]
  · have h8 : ¬(k < 8) := by omega
    have h16 : k < 16 := by omega
    have hsub : k - 8 < 8 := by omega
    have hidx : (7 - k / 8) * 8 + k % 8 = 48 + (k - 8) := by omega
    simp [hidx, h8, h16, hsub, show k - 8 < 64 by omega,
      show k < 24 by omega, show k < 32 by omega, show k < 40 by omega,
      show k < 48 by omega, show k < 56 by omega]
  · have h8 : ¬(k < 8) := by omega
    have h16 : ¬(k < 16) := by omega
    have h24 : k < 24 := by omega
    have hsub16 : k - 16 < 8 := by omega
    have hsub8 : ¬(k - 8 < 8) := by omega
    have hidx : (7 - k / 8) * 8 + k % 8 = 40 + (k - 16) := by omega
    simp [hidx, h8, h16, h24, hsub16, hsub8,
      show k - 8 < 64 by omega, show k - 16 < 64 by omega,
      show k < 32 by omega, show k < 40 by omega, show k < 48 by omega, show k < 56 by omega]
  · have h8 : ¬(k < 8) := by omega
    have h16 : ¬(k < 16) := by omega
    have h24 : ¬(k < 24) := by omega
    have h32 : k < 32 := by omega
    have hsub24 : k - 24 < 8 := by omega
    have hsub16 : ¬(k - 16 < 8) := by omega
    have hsub8 : ¬(k - 8 < 8) := by omega
    have hidx : (7 - k / 8) * 8 + k % 8 = 32 + (k - 24) := by omega
    simp [hidx, h8, h16, h24, h32, hsub24, hsub16, hsub8,
      show k - 8 < 64 by omega, show k - 16 < 64 by omega, show k - 24 < 64 by omega,
      show k < 40 by omega, show k < 48 by omega, show k < 56 by omega]
  · have h8 : ¬(k < 8) := by omega
    have h16 : ¬(k < 16) := by omega
    have h24 : ¬(k < 24) := by omega
    have h32 : ¬(k < 32) := by omega
    have h40 : k < 40 := by omega
    have hsub32 : k - 32 < 8 := by omega
    have hsub24 : ¬(k - 24 < 8) := by omega
    have hsub16 : ¬(k - 16 < 8) := by omega
    have hsub8 : ¬(k - 8 < 8) := by omega
    have hidx : (7 - k / 8) * 8 + k % 8 = 24 + (k - 32) := by omega
    simp [hidx, h8, h16, h24, h32, h40, hsub32, hsub24, hsub16, hsub8,
      show k - 8 < 64 by omega, show k - 16 < 64 by omega, show k - 24 < 64 by omega, show k - 32 < 64 by omega,
      show k < 48 by omega, show k < 56 by omega]
  · have h8 : ¬(k < 8) := by omega
    have h16 : ¬(k < 16) := by omega
    have h24 : ¬(k < 24) := by omega
    have h32 : ¬(k < 32) := by omega
    have h40 : ¬(k < 40) := by omega
    have h48 : k < 48 := by omega
    have hsub40 : k - 40 < 8 := by omega
    have hsub32 : ¬(k - 32 < 8) := by omega
    have hsub24 : ¬(k - 24 < 8) := by omega
    have hsub16 : ¬(k - 16 < 8) := by omega
    have hsub8 : ¬(k - 8 < 8) := by omega
    have hidx : (7 - k / 8) * 8 + k % 8 = 16 + (k - 40) := by omega
    simp [hidx, h8, h16, h24, h32, h40, h48, hsub40, hsub32, hsub24, hsub16, hsub8,
      show k - 8 < 64 by omega, show k - 16 < 64 by omega, show k - 24 < 64 by omega,
      show k - 32 < 64 by omega, show k - 40 < 64 by omega, show k < 56 by omega]
  · have h8 : ¬(k < 8) := by omega
    have h16 : ¬(k < 16) := by omega
    have h24 : ¬(k < 24) := by omega
    have h32 : ¬(k < 32) := by omega
    have h40 : ¬(k < 40) := by omega
    have h48 : ¬(k < 48) := by omega
    have h56 : k < 56 := by omega
    have hsub48 : k - 48 < 8 := by omega
    have hsub40 : ¬(k - 40 < 8) := by omega
    have hsub32 : ¬(k - 32 < 8) := by omega
    have hsub24 : ¬(k - 24 < 8) := by omega
    have hsub16 : ¬(k - 16 < 8) := by omega
    have hsub8 : ¬(k - 8 < 8) := by omega
    have hidx : (7 - k / 8) * 8 + k % 8 = 8 + (k - 48) := by omega
    simp [hidx, h8, h16, h24, h32, h40, h48, h56, hsub48, hsub40, hsub32, hsub24, hsub16, hsub8,
      show k - 8 < 64 by omega, show k - 16 < 64 by omega, show k - 24 < 64 by omega,
      show k - 32 < 64 by omega, show k - 40 < 64 by omega, show k - 48 < 64 by omega]
  · have h8 : ¬(k < 8) := by omega
    have h16 : ¬(k < 16) := by omega
    have h24 : ¬(k < 24) := by omega
    have h32 : ¬(k < 32) := by omega
    have h40 : ¬(k < 40) := by omega
    have h48 : ¬(k < 48) := by omega
    have h56 : ¬(k < 56) := by omega
    have hsub56 : k - 56 < 8 := by omega
    have hsub48 : ¬(k - 48 < 8) := by omega
    have hsub40 : ¬(k - 40 < 8) := by omega
    have hsub32 : ¬(k - 32 < 8) := by omega
    have hsub24 : ¬(k - 24 < 8) := by omega
    have hsub16 : ¬(k - 16 < 8) := by omega
    have hsub8 : ¬(k - 8 < 8) := by omega
    have hidx : (7 - k / 8) * 8 + k % 8 = 0 + (k - 56) := by omega
    simp [hidx, h8, h16, h24, h32, h40, h48, h56, hsub56, hsub48, hsub40, hsub32, hsub24, hsub16, hsub8,
      show k - 8 < 64 by omega, show k - 16 < 64 by omega, show k - 24 < 64 by omega,
      show k - 32 < 64 by omega, show k - 40 < 64 by omega, show k - 48 < 64 by omega, show k - 56 < 64 by omega]

/-- RV64 Zbb `REV8` bisimulation against upstream `LeanRV64D.Functions.rev8` (`execute_REV8`,
    `LeanRV64D/InstsEnd.lean`, lines 68013–68015), plus involutivity `rev8 (rev8 x) = x`. -/
theorem rv64ZbbRev8Spec_bisim_sail (x : BitVec 64) :
    rv64ZbbRev8Spec x = rev8 x ∧ rev8 (rev8 x) = x := by
  have heq : ∀ y : BitVec 64, rv64ZbbRev8Spec y = rev8 y := by
    intro y
    have hunroll : rev8 y =
        Sail.BitVec.updateSubrange'
          (Sail.BitVec.updateSubrange'
            (Sail.BitVec.updateSubrange'
              (Sail.BitVec.updateSubrange'
                (Sail.BitVec.updateSubrange'
                  (Sail.BitVec.updateSubrange'
                    (Sail.BitVec.updateSubrange'
                      (Sail.BitVec.updateSubrange' 0#64 0 8 (BitVec.extractLsb' 56 8 y))
                      8 8 (BitVec.extractLsb' 48 8 y))
                    16 8 (BitVec.extractLsb' 40 8 y))
                  24 8 (BitVec.extractLsb' 32 8 y))
                32 8 (BitVec.extractLsb' 24 8 y))
              40 8 (BitVec.extractLsb' 16 8 y))
            48 8 (BitVec.extractLsb' 8 8 y))
          56 8 (BitVec.extractLsb' 0 8 y) := by
      unfold rev8 zeros Sail.BitVec.length
      dsimp only [ForIn.forIn, ForIn'.forIn', IntRange.forIn', Id.run, Id.instMonad, Bind.bind, Pure.pure]
      iterate 9 (unfold IntRange.forIn'.loop; simp only [Membership.mem]; dsimp only [Bind.bind, Pure.pure])
      rfl
    rw [hunroll]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [rv64ZbbRev8Spec_getLsbD y k hk]
    repeat rw [getLsbD_updateSubrange' _ _ _ _ k hk]
    simp only [BitVec.getLsbD_extractLsb']
    have hbyte : k / 8 = 0 ∨ k / 8 = 1 ∨ k / 8 = 2 ∨ k / 8 = 3 ∨
        k / 8 = 4 ∨ k / 8 = 5 ∨ k / 8 = 6 ∨ k / 8 = 7 := by omega
    rcases hbyte with hb | hb | hb | hb | hb | hb | hb | hb
    · simp [show ¬(56 ≤ k ∧ k < 56 + 8) by omega, show ¬(48 ≤ k ∧ k < 48 + 8) by omega,
        show ¬(40 ≤ k ∧ k < 40 + 8) by omega, show ¬(32 ≤ k ∧ k < 32 + 8) by omega,
        show ¬(24 ≤ k ∧ k < 24 + 8) by omega, show ¬(16 ≤ k ∧ k < 16 + 8) by omega,
        show ¬(8 ≤ k ∧ k < 8 + 8) by omega, show 0 ≤ k ∧ k < 0 + 8 by omega,
        show (7 - k / 8) * 8 + k % 8 = 56 + k by omega]
    · simp [show ¬(56 ≤ k ∧ k < 56 + 8) by omega, show ¬(48 ≤ k ∧ k < 48 + 8) by omega,
        show ¬(40 ≤ k ∧ k < 40 + 8) by omega, show ¬(32 ≤ k ∧ k < 32 + 8) by omega,
        show ¬(24 ≤ k ∧ k < 24 + 8) by omega, show ¬(16 ≤ k ∧ k < 16 + 8) by omega,
        show 8 ≤ k ∧ k < 8 + 8 by omega, show k - 8 < 8 by omega,
        show (7 - k / 8) * 8 + k % 8 = 48 + (k - 8) by omega]
    · simp [show ¬(56 ≤ k ∧ k < 56 + 8) by omega, show ¬(48 ≤ k ∧ k < 48 + 8) by omega,
        show ¬(40 ≤ k ∧ k < 40 + 8) by omega, show ¬(32 ≤ k ∧ k < 32 + 8) by omega,
        show ¬(24 ≤ k ∧ k < 24 + 8) by omega, show 16 ≤ k ∧ k < 16 + 8 by omega,
        show k - 16 < 8 by omega, show (7 - k / 8) * 8 + k % 8 = 40 + (k - 16) by omega]
    · simp [show ¬(56 ≤ k ∧ k < 56 + 8) by omega, show ¬(48 ≤ k ∧ k < 48 + 8) by omega,
        show ¬(40 ≤ k ∧ k < 40 + 8) by omega, show ¬(32 ≤ k ∧ k < 32 + 8) by omega,
        show 24 ≤ k ∧ k < 24 + 8 by omega, show k - 24 < 8 by omega,
        show (7 - k / 8) * 8 + k % 8 = 32 + (k - 24) by omega]
    · simp [show ¬(56 ≤ k ∧ k < 56 + 8) by omega, show ¬(48 ≤ k ∧ k < 48 + 8) by omega,
        show ¬(40 ≤ k ∧ k < 40 + 8) by omega, show 32 ≤ k ∧ k < 32 + 8 by omega,
        show k - 32 < 8 by omega, show (7 - k / 8) * 8 + k % 8 = 24 + (k - 32) by omega]
    · simp [show ¬(56 ≤ k ∧ k < 56 + 8) by omega, show ¬(48 ≤ k ∧ k < 48 + 8) by omega,
        show 40 ≤ k ∧ k < 40 + 8 by omega, show k - 40 < 8 by omega,
        show (7 - k / 8) * 8 + k % 8 = 16 + (k - 40) by omega]
    · simp [show ¬(56 ≤ k ∧ k < 56 + 8) by omega, show 48 ≤ k ∧ k < 48 + 8 by omega,
        show k - 48 < 8 by omega, show (7 - k / 8) * 8 + k % 8 = 8 + (k - 48) by omega]
    · simp [show 56 ≤ k ∧ k < 56 + 8 by omega, show k - 56 < 8 by omega,
        show (7 - k / 8) * 8 + k % 8 = 0 + (k - 56) by omega]
  refine ⟨heq x, ?_⟩
  rw [← heq (rev8 x), ← heq x]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hk' : (7 - k / 8) * 8 + k % 8 < 64 := by omega
  rw [rv64ZbbRev8Spec_getLsbD _ k hk, rv64ZbbRev8Spec_getLsbD x _ hk']
  congr 1
  omega

/-- Exact upstream Sail `execute_ORCB` functional core (`LeanRV64D/InstsEnd.lean`, lines 68058–68070). -/
def sailOrcbCore (rs1_val : BitVec 64) : BitVec 64 := Id.run do
  let output : BitVec 64 := zeros (n := 64)
  let loop_i_lower := 0
  let loop_i_upper := 64 -i 8
  let mut loop_vars := output
  for i in [loop_i_lower:loop_i_upper:8]i do
    let output := loop_vars
    loop_vars :=
      let inputchar : BitVec 8 := Sail.BitVec.extractLsb rs1_val (i.toNat + 7) i.toNat
      let outputchar : BitVec 8 := if (inputchar == zeros (n := 8) : Bool) then 0x00#8 else 0xff#8
      Sail.BitVec.updateSubrange output (i.toNat + 7) i.toNat outputchar
  pure loop_vars

/-- Pure `TurboLean`-side RV64 Zbb `ORC.B` (bitwise OR-combine within each byte) specification:
    sets every bit of byte `j` (`0 ≤ j < 8`) to `1` iff the corresponding input byte is non-zero. -/
def rv64ZbbOrcbSpec (x : BitVec 64) : BitVec 64 :=
  let b (off : Nat) : BitVec 64 :=
    if x.extractLsb' off 8 == 0#8 then 0#64 else (0xff#64 <<< off)
  b 0 ||| b 8 ||| b 16 ||| b 24 ||| b 32 ||| b 40 ||| b 48 ||| b 56

/-- RV64 Zbb `ORC.B` bisimulation against `sailOrcbCore`. -/
theorem rv64ZbbOrcbSpec_bisim_sail (x : BitVec 64) :
    rv64ZbbOrcbSpec x = sailOrcbCore x := by
  have hunroll : sailOrcbCore x =
      Sail.BitVec.updateSubrange'
        (Sail.BitVec.updateSubrange'
          (Sail.BitVec.updateSubrange'
            (Sail.BitVec.updateSubrange'
              (Sail.BitVec.updateSubrange'
                (Sail.BitVec.updateSubrange'
                  (Sail.BitVec.updateSubrange'
                    (Sail.BitVec.updateSubrange' 0#64 0 8 (if BitVec.extractLsb' 0 8 x == 0#8 then 0x00#8 else 0xff#8))
                    8 8 (if BitVec.extractLsb' 8 8 x == 0#8 then 0x00#8 else 0xff#8))
                  16 8 (if BitVec.extractLsb' 16 8 x == 0#8 then 0x00#8 else 0xff#8))
                24 8 (if BitVec.extractLsb' 24 8 x == 0#8 then 0x00#8 else 0xff#8))
              32 8 (if BitVec.extractLsb' 32 8 x == 0#8 then 0x00#8 else 0xff#8))
            40 8 (if BitVec.extractLsb' 40 8 x == 0#8 then 0x00#8 else 0xff#8))
          48 8 (if BitVec.extractLsb' 48 8 x == 0#8 then 0x00#8 else 0xff#8))
        56 8 (if BitVec.extractLsb' 56 8 x == 0#8 then 0x00#8 else 0xff#8) := by
    unfold sailOrcbCore zeros
    dsimp only [ForIn.forIn, ForIn'.forIn', IntRange.forIn', Id.run, Id.instMonad, Bind.bind, Pure.pure]
    iterate 9 (unfold IntRange.forIn'.loop; simp only [Membership.mem]; dsimp only [Bind.bind, Pure.pure])
    rfl
  rw [hunroll]
  unfold rv64ZbbOrcbSpec
  dsimp only
  have hff : ∀ (off k : Nat), k < 64 → (0xff#64 <<< off).getLsbD k = decide (off ≤ k ∧ k < off + 8) := by
    intro off k hk
    rw [BitVec.getLsbD_shiftLeft]
    by_cases hlo : k < off
    · simp [hk, hlo, show ¬(off ≤ k) by omega]
    · by_cases hhi : k < off + 8
      · have hsub : k - off < 8 := by omega
        have hbit : (0xff#64).getLsbD (k - off) = true := by
          have h8 : k - off = 0 ∨ k - off = 1 ∨ k - off = 2 ∨ k - off = 3 ∨
              k - off = 4 ∨ k - off = 5 ∨ k - off = 6 ∨ k - off = 7 := by omega
          rcases h8 with h | h | h | h | h | h | h | h <;> rw [h] <;> decide
        simp [hk, hlo, hbit, show off ≤ k ∧ k < off + 8 by omega]
      · have hbit : (0xff#64).getLsbD (k - off) = false := by
          rw [BitVec.getLsbD_ofNat]
          have hge : 8 ≤ k - off := by omega
          have hdiv : 255 / 2 ^ (k - off) = 0 :=
            Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (by decide : 255 < 2 ^ 8) (Nat.pow_le_pow_right (by decide) hge))
          simp [show k - off < 64 by omega, Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
        simp [hk, hlo, hbit, show ¬(off ≤ k ∧ k < off + 8) by omega]
  have hterm : ∀ (c : Bool) (off k : Nat), k < 64 →
      (if c then 0#64 else 0xff#64 <<< off).getLsbD k = (!c && decide (off ≤ k ∧ k < off + 8)) := by
    intro c off k hk
    cases c
    · simp [hff off k hk]
    · simp
  have hbyte_iff : ∀ (c : Bool) (d : Nat), d < 8 →
      (if c then 0x00#8 else 0xff#8).getLsbD d = !c := by
    intro c d hd
    cases c
    · have h8 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 := by omega
      rcases h8 with h | h | h | h | h | h | h | h <;> rw [h] <;> decide
    · simp
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_or, hterm _ _ k hk]
  repeat rw [getLsbD_updateSubrange' _ _ _ _ k hk]
  have hbyte : k / 8 = 0 ∨ k / 8 = 1 ∨ k / 8 = 2 ∨ k / 8 = 3 ∨
      k / 8 = 4 ∨ k / 8 = 5 ∨ k / 8 = 6 ∨ k / 8 = 7 := by omega
  rcases hbyte with hb | hb | hb | hb | hb | hb | hb | hb
  · have h56 : ¬(56 ≤ k ∧ k < 56 + 8) := by omega
    have h48 : ¬(48 ≤ k ∧ k < 48 + 8) := by omega
    have h40 : ¬(40 ≤ k ∧ k < 40 + 8) := by omega
    have h32 : ¬(32 ≤ k ∧ k < 32 + 8) := by omega
    have h24 : ¬(24 ≤ k ∧ k < 24 + 8) := by omega
    have h16 : ¬(16 ≤ k ∧ k < 16 + 8) := by omega
    have h8 : ¬(8 ≤ k ∧ k < 8 + 8) := by omega
    have h0 : 0 ≤ k ∧ k < 0 + 8 := by omega
    simp only [h56, h48, h40, h32, h24, h16, h8, h0, and_self, ↓reduceIte, decide_true, decide_false,
      Bool.and_true, Bool.and_false, Bool.or_false, Nat.sub_zero]
    rw [hbyte_iff _ k (by omega)]
  · have h56 : ¬(56 ≤ k ∧ k < 56 + 8) := by omega
    have h48 : ¬(48 ≤ k ∧ k < 48 + 8) := by omega
    have h40 : ¬(40 ≤ k ∧ k < 40 + 8) := by omega
    have h32 : ¬(32 ≤ k ∧ k < 32 + 8) := by omega
    have h24 : ¬(24 ≤ k ∧ k < 24 + 8) := by omega
    have h16 : ¬(16 ≤ k ∧ k < 16 + 8) := by omega
    have h8 : 8 ≤ k ∧ k < 8 + 8 := by omega
    have h0 : ¬(0 ≤ k ∧ k < 0 + 8) := by omega
    simp only [h56, h48, h40, h32, h24, h16, h8, h0, and_self, ↓reduceIte, decide_true, decide_false,
      Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or]
    rw [hbyte_iff _ (k - 8) (by omega)]
  · have h56 : ¬(56 ≤ k ∧ k < 56 + 8) := by omega
    have h48 : ¬(48 ≤ k ∧ k < 48 + 8) := by omega
    have h40 : ¬(40 ≤ k ∧ k < 40 + 8) := by omega
    have h32 : ¬(32 ≤ k ∧ k < 32 + 8) := by omega
    have h24 : ¬(24 ≤ k ∧ k < 24 + 8) := by omega
    have h16 : 16 ≤ k ∧ k < 16 + 8 := by omega
    have h8 : ¬(8 ≤ k ∧ k < 8 + 8) := by omega
    have h0 : ¬(0 ≤ k ∧ k < 0 + 8) := by omega
    simp only [h56, h48, h40, h32, h24, h16, h8, h0, and_self, ↓reduceIte, decide_true, decide_false,
      Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or]
    rw [hbyte_iff _ (k - 16) (by omega)]
  · have h56 : ¬(56 ≤ k ∧ k < 56 + 8) := by omega
    have h48 : ¬(48 ≤ k ∧ k < 48 + 8) := by omega
    have h40 : ¬(40 ≤ k ∧ k < 40 + 8) := by omega
    have h32 : ¬(32 ≤ k ∧ k < 32 + 8) := by omega
    have h24 : 24 ≤ k ∧ k < 24 + 8 := by omega
    have h16 : ¬(16 ≤ k ∧ k < 16 + 8) := by omega
    have h8 : ¬(8 ≤ k ∧ k < 8 + 8) := by omega
    have h0 : ¬(0 ≤ k ∧ k < 0 + 8) := by omega
    simp only [h56, h48, h40, h32, h24, h16, h8, h0, and_self, ↓reduceIte, decide_true, decide_false,
      Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or]
    rw [hbyte_iff _ (k - 24) (by omega)]
  · have h56 : ¬(56 ≤ k ∧ k < 56 + 8) := by omega
    have h48 : ¬(48 ≤ k ∧ k < 48 + 8) := by omega
    have h40 : ¬(40 ≤ k ∧ k < 40 + 8) := by omega
    have h32 : 32 ≤ k ∧ k < 32 + 8 := by omega
    have h24 : ¬(24 ≤ k ∧ k < 24 + 8) := by omega
    have h16 : ¬(16 ≤ k ∧ k < 16 + 8) := by omega
    have h8 : ¬(8 ≤ k ∧ k < 8 + 8) := by omega
    have h0 : ¬(0 ≤ k ∧ k < 0 + 8) := by omega
    simp only [h56, h48, h40, h32, h24, h16, h8, h0, and_self, ↓reduceIte, decide_true, decide_false,
      Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or]
    rw [hbyte_iff _ (k - 32) (by omega)]
  · have h56 : ¬(56 ≤ k ∧ k < 56 + 8) := by omega
    have h48 : ¬(48 ≤ k ∧ k < 48 + 8) := by omega
    have h40 : 40 ≤ k ∧ k < 40 + 8 := by omega
    have h32 : ¬(32 ≤ k ∧ k < 32 + 8) := by omega
    have h24 : ¬(24 ≤ k ∧ k < 24 + 8) := by omega
    have h16 : ¬(16 ≤ k ∧ k < 16 + 8) := by omega
    have h8 : ¬(8 ≤ k ∧ k < 8 + 8) := by omega
    have h0 : ¬(0 ≤ k ∧ k < 0 + 8) := by omega
    simp only [h56, h48, h40, h32, h24, h16, h8, h0, and_self, ↓reduceIte, decide_true, decide_false,
      Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or]
    rw [hbyte_iff _ (k - 40) (by omega)]
  · have h56 : ¬(56 ≤ k ∧ k < 56 + 8) := by omega
    have h48 : 48 ≤ k ∧ k < 48 + 8 := by omega
    have h40 : ¬(40 ≤ k ∧ k < 40 + 8) := by omega
    have h32 : ¬(32 ≤ k ∧ k < 32 + 8) := by omega
    have h24 : ¬(24 ≤ k ∧ k < 24 + 8) := by omega
    have h16 : ¬(16 ≤ k ∧ k < 16 + 8) := by omega
    have h8 : ¬(8 ≤ k ∧ k < 8 + 8) := by omega
    have h0 : ¬(0 ≤ k ∧ k < 0 + 8) := by omega
    simp only [h56, h48, h40, h32, h24, h16, h8, h0, and_self, ↓reduceIte, decide_true, decide_false,
      Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or]
    rw [hbyte_iff _ (k - 48) (by omega)]
  · have h56 : 56 ≤ k ∧ k < 56 + 8 := by omega
    have h48 : ¬(48 ≤ k ∧ k < 48 + 8) := by omega
    have h40 : ¬(40 ≤ k ∧ k < 40 + 8) := by omega
    have h32 : ¬(32 ≤ k ∧ k < 32 + 8) := by omega
    have h24 : ¬(24 ≤ k ∧ k < 24 + 8) := by omega
    have h16 : ¬(16 ≤ k ∧ k < 16 + 8) := by omega
    have h8 : ¬(8 ≤ k ∧ k < 8 + 8) := by omega
    have h0 : ¬(0 ≤ k ∧ k < 0 + 8) := by omega
    simp only [h56, h48, h40, h32, h24, h16, h8, h0, and_self, ↓reduceIte, decide_true, decide_false,
      Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or]
    rw [hbyte_iff _ (k - 56) (by omega)]

/-- Exact upstream Sail `execute_CLZ` / `execute_CLZW` / `execute_CTZ` / `execute_CTZW`
    functional cores (`LeanRV64D/InstsEnd.lean`, lines 71712–71745). -/
def sailClzCore (rs1_val : BitVec 64) : BitVec 64 :=
  to_bits_truncate (l := 64) (Int.ofNat (Sail.BitVec.countLeadingZeros rs1_val))

def sailClzwCore (rs1_val : BitVec 64) : BitVec 64 :=
  to_bits_truncate (l := 64) (Int.ofNat (Sail.BitVec.countLeadingZeros (Sail.BitVec.extractLsb rs1_val 31 0)))

def sailCtzCore (rs1_val : BitVec 64) : BitVec 64 :=
  to_bits_truncate (l := 64) (Int.ofNat (Sail.BitVec.countTrailingZeros rs1_val))

def sailCtzwCore (rs1_val : BitVec 64) : BitVec 64 :=
  to_bits_truncate (l := 64) (Int.ofNat (Sail.BitVec.countTrailingZeros (Sail.BitVec.extractLsb rs1_val 31 0)))

/-- Pure `TurboLean`-side RV64 Zbb `CLZ`, `CLZW`, `CTZ`, and `CTZW` specifications. -/
def rv64ZbbClzSpec (x : BitVec 64) : BitVec 64 := x.clz
def rv64ZbbClzwSpec (x : BitVec 64) : BitVec 64 := ((x.truncate 32).clz).zeroExtend 64
def rv64ZbbCtzSpec (x : BitVec 64) : BitVec 64 := x.reverse.clz
def rv64ZbbCtzwSpec (x : BitVec 64) : BitVec 64 := ((x.truncate 32).reverse.clz).zeroExtend 64

/-- RV64 Zbb `CLZ` / `CLZW` / `CTZ` / `CTZW` bisimulation against upstream Sail cores. -/
theorem rv64ZbbClzCtz_bisim_sail (x : BitVec 64) :
    rv64ZbbClzSpec x = sailClzCore x ∧
      rv64ZbbClzwSpec x = sailClzwCore x ∧
      rv64ZbbCtzSpec x = sailCtzCore x ∧
      rv64ZbbCtzwSpec x = sailCtzwCore x := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold rv64ZbbClzSpec sailClzCore Sail.BitVec.countLeadingZeros
    rw [to_bits_truncate_eq_ofInt, ofInt_ofNat_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · unfold rv64ZbbClzwSpec sailClzwCore Sail.BitVec.countLeadingZeros
    rw [extractLsb_31_0_eq_truncate32, to_bits_truncate_eq_ofInt, ofInt_ofNat_eq_ofNat]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans (x.truncate 32).clz.isLt (by decide : 2 ^ 32 < 2 ^ 64))]
  · unfold rv64ZbbCtzSpec sailCtzCore Sail.BitVec.countTrailingZeros Sail.BitVec.countLeadingZeros
    rw [to_bits_truncate_eq_ofInt, ofInt_ofNat_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · unfold rv64ZbbCtzwSpec sailCtzwCore Sail.BitVec.countTrailingZeros Sail.BitVec.countLeadingZeros
    rw [extractLsb_31_0_eq_truncate32, to_bits_truncate_eq_ofInt, ofInt_ofNat_eq_ofNat]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans (x.truncate 32).reverse.clz.isLt (by decide : 2 ^ 32 < 2 ^ 64))]

/-- Pure recursive bit-counting loop matching `LeanRV64D.Functions.count_ones` across width `w`. -/
def rv64PopcountLoop {w : Nat} (x : BitVec w) (i : Nat) (acc : Nat) : Nat :=
  if _ : i < w then
    rv64PopcountLoop x (i + 1) (if x.getLsbD i then acc + 1 else acc)
  else
    acc

/-- Pure `TurboLean`-side RV64 Zbb `CPOP` (`64`-bit) and `CPOPW` (`32`-bit) specifications. -/
def rv64ZbbCpopSpec (x : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (rv64PopcountLoop x 0 0)

def rv64ZbbCpopwSpec (x : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (rv64PopcountLoop (x.truncate 32) 0 0)

private theorem count_ones_run_eq_popcountLoop {w : Nat} (hw : 0 < w) (x : BitVec w)
    (s : SequentialState RegisterType trivialChoiceSource) :
    (count_ones x).run s = .ok (rv64PopcountLoop x 0 0) s := by
  let r : IntRange := [0 : (w : Int) -i 1 : 1]i
  let body : (i : Int) → i ∈ r → Nat → SailM (ForInStep Nat) :=
    fun i _ count =>
      if (Sail.BitVec.access x i.toNat == 1#1 : Bool) = true then
        EStateM.bind
          (EStateM.bind (assert (((count : Int) + 1) ≤b (w : Int)) "core/arithmetic.sail:85.28-85.29")
            fun _ => EStateM.pure ((count : Int) + 1))
          fun y => EStateM.bind (EStateM.pure PUnit.unit) fun _ => EStateM.pure (ForInStep.yield y.toNat)
      else
        EStateM.bind (EStateM.pure count) fun y =>
          EStateM.bind (EStateM.pure PUnit.unit) fun _ => EStateM.pure (ForInStep.yield y)
  have hloop : ∀ (k : Nat) (_hk : k ≤ w) (acc : Nat) (_hacc : acc ≤ k)
      (hs : ((k : Int) - r.start) % r.step = 0),
      (IntRange.forIn'.loop (m := SailM) r body acc (k : Int) hs).run s =
        .ok (rv64PopcountLoop x k acc) s := by
    intro k hk
    induction hrem : w - k generalizing k with
    | zero =>
      have hkw : k = w := by omega
      intro acc _ hs
      have hnotmem : ¬((k : Int) ∈ r) := by
        simp [r, Membership.mem, hkw]
        omega
      unfold IntRange.forIn'.loop rv64PopcountLoop
      have hnlt : ¬(k < w) := by omega
      simp only [hnotmem, hnlt, dite_false]
      rfl
    | succ rem ih =>
      have hlt : k < w := by omega
      intro acc hacc hs
      have hmem : (k : Int) ∈ r := by
        simp [r, Membership.mem]
        omega
      have haccess : (Sail.BitVec.access x k == 1#1 : Bool) = x.getLsbD k := by
        unfold Sail.BitVec.access
        have hget : x[k]! = x.getLsbD k := by simp [hlt]
        rw [hget]
        cases x.getLsbD k <;> decide
      have hle : (((acc : Int) + 1) ≤b (w : Int)) = true := by
        change decide ((acc : Int) + 1 ≤ (w : Int)) = true
        exact decide_eq_true (by omega)
      unfold IntRange.forIn'.loop rv64PopcountLoop
      simp only [hmem, hlt, dite_true]
      dsimp [body, r, PreSail.assert]
      have hcast : (k : Int) + 1 = ((k + 1 : Nat) : Int) := rfl
      cases hbit : x.getLsbD k
      · have hacc_f : (Sail.BitVec.access x k == 1#1 : Bool) = false := by
          rw [haccess, hbit]
        simp only [hacc_f, Bool.false_eq_true, ↓reduceIte, hcast]
        dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run]
        exact ih (k + 1) (by omega) (by omega) acc (by omega) _
      · have hacc_t : (Sail.BitVec.access x k == 1#1 : Bool) = true := by
          rw [haccess, hbit]
        simp only [hacc_t, ↓reduceIte, hle, hcast]
        dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run]
        exact ih (k + 1) (by omega) (by omega) (acc + 1) (by omega) _
  have h0 := hloop 0 (by omega) 0 (by omega) (by simp [r])
  unfold count_ones Sail.BitVec.length
  dsimp only [ForIn.forIn, ForIn'.forIn', IntRange.forIn']
  dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at h0 ⊢
  rw [h0]

/-- RV64 Zbb `CPOP` and `CPOPW` monadic bisimulation against upstream `LeanRV64D.Functions.count_ones`
    (`execute_CPOP` and `execute_CPOPW`, `LeanRV64D/InstsEnd.lean`, lines 71729–71736), proving
    both bit-exact agreement and assertion-freedom across all 64-bit inputs and states. -/
theorem rv64ZbbCpop_bisim_sail (rs1_val : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource) :
    ((do
        let result ← count_ones rs1_val
        pure (to_bits_truncate (l := 64) (Int.ofNat result))).run s) =
      .ok (rv64ZbbCpopSpec rs1_val) s ∧
    ((do
        let result ← count_ones (Sail.BitVec.extractLsb rs1_val 31 0)
        pure (to_bits_truncate (l := 64) (Int.ofNat result))).run s) =
      .ok (rv64ZbbCpopwSpec rs1_val) s := by
  have h64 := count_ones_run_eq_popcountLoop (by decide : 0 < 64) rs1_val s
  have h32 := count_ones_run_eq_popcountLoop (by decide : 0 < 32) (rs1_val.truncate 32) s
  rw [extractLsb_31_0_eq_truncate32]
  constructor
  · dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at h64 ⊢
    rw [h64]
    dsimp [rv64ZbbCpopSpec]
    rw [to_bits_truncate_eq_ofInt, BitVec.ofInt_natCast]
  · dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at h32 ⊢
    rw [h32]
    dsimp [rv64ZbbCpopwSpec]
    rw [to_bits_truncate_eq_ofInt, BitVec.ofInt_natCast]

end SailRiscvBridge
