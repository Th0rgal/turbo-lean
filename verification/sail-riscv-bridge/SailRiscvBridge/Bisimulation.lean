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

Bridges `TurboLean.PolicyGates` (`riscvDivU64Spec`, `riscvRemU64Spec`), signed RV64M
(`DIV`, `REM`, `MULH`, `MULHSU`), `LeanNative.IR` Zbc carryless multiplication
(`clmul64`, `clmul64Hi`, `CLMULR`, and $\mathbb{F}_2[x]$ commutativity), and the base
RV64I ALU/shift/`LUI`/`AUIPC`/branch fragment directly against upstream
`opencompl/sail-riscv-lean` (`Lean_RV64D` + `Sail`) on `leanprover/lean4:v4.29.0`,
avoiding monolithic `LeanRV64D.InstsEnd` / `LeanRV64D.Step` / `LeanRV64D.ZicsrInsts` /
`LeanRV64D.RiscvExtras` imports so incremental elaboration stays lightweight and axiom-clean.
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

end SailRiscvBridge
