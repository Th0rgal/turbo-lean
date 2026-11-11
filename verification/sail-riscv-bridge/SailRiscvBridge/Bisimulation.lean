import SailRiscvBridge.MirroredModel
import Sail
import LeanRV64D.Defs
import LeanRV64D.Prelude
import LeanRV64D.Xlen
import LeanRV64D.Arithmetic
import LeanRV64D.MextInsts
import LeanRV64D.Regs
import LeanRV64D.PcAccess
import LeanRV64D.Types
import LeanRV64D.AddrChecks
import LeanRV64D.SplitAccessUtils
import LeanRV64D.PhysMemInterface
import LeanRV64D.Arith
import LeanRV64D.AextTypes
import LeanRV64D.ZaamoInsts
import LeanRV64D.ZicsrTypes
import LeanRV64D.IsaVersion
import LeanRV64D.MemAddrtype
import LeanRV64D.SysRegs
import LeanRV64D.SysControl
import LeanRV64D.VmemTypes
import LeanRV64D.VmemPte
import LeanRV64D.VmemPtw
import LeanRV64D.VmemTlb
import LeanRV64D.Mem
import LeanRV64D.Vmem
import LeanRV64D.PmpRegs
import LeanRV64D.PmpControl
import LeanRV64D.Pma
import LeanRV64D.RangeUtil
import LeanRV64D.Platform
import LeanRV64D.PlatformConfig
import LeanRV64D.SysExceptions
import LeanRV64D.InterruptRegs
import LeanRV64D.ZicfilpRegs
import LeanRV64D.FdextRegs
import LeanRV64D.Classify
import LeanRV64D.FloatClassify
import LeanRV64D.FextInsts
import LeanRV64D.DextInsts
import LeanRV64D.ZfhInsts
import LeanRV64D.Callbacks
import LeanRV64D.Callbacks0

/-!
# Stage 3E / Milestone `M5` RV64 Formal Bisimulation against `opencompl/sail-riscv-lean`

Bridges `TurboLean.PolicyGates` (`riscvDivU64Spec`, `riscvRemU64Spec`), RV64M 64-bit & 32-bit
word multiplication/division/remainder (`MUL`, `MULH`, `MULHSU`, `MULHU`, `MULW`, `DIV`, `DIVU`,
`REM`, `REMU`, `DIVW`, `DIVUW`, `REMW`, `REMUW`), `LeanNative.IR` Zbc carryless multiplication
(`clmul64`, `clmul64Hi`, `CLMULR`, and $\mathbb{F}_2[x]$ commutativity), the RV64I base & `*W`
ALU/shift/`LUI`/`AUIPC`/branch/`JAL`/`JALR` fragment, RV64 Zba/Zbb/Zbs bit-manipulation
instructions, RV64I Load/Store memory (`LB`/`LBU`/`LH`/`LHU`/`LW`/`LWU`/`LD` & `SB`/`SH`/`SW`/`SD`),
RVC compressed (`Zca` / `Zcb` / RV64C) instructions, and RV64A (`Zaamo` / `Zacas` / `Zalrsc`),
`Zicsr` / privileged-mode checks, `Sv39` / `Sv48` virtual-memory PTE/SATP/TLB + full multi-level
`ptw_step` / `translateAddr` page-table walk, M/S trap/interrupt delegation + `MRET` / `SRET`
trap-return, and RV64F / RV64D floating-point state, IEEE-754 classification, rounding/exception
flags, and pure `SailM` instruction semantics directly
against upstream `opencompl/sail-riscv-lean` (`Lean_RV64D` + `Sail`) on `leanprover/lean4:v4.29.0`,
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

/-! ## 12. RV64I Load/Store Memory Fragment (`LB`/`LBU`/`LH`/`LHU`/`LW`/`LWU`/`LD` & `SB`/`SH`/`SW`/`SD`) -/

/-- Pure `TurboLean`-side RV64I effective data address calculation (`rs1_val + sext(imm12)`). -/
def rv64iEffectiveAddrSpec (rs1_val : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  rs1_val + imm.signExtend 64

/-- Pure `TurboLean`-side natural alignment predicate for RV64I memory accesses. -/
def rv64iAlignedAddrSpec (addr : BitVec 64) (width : Nat) : Bool :=
  addr.toNat % width == 0

/-- Exact upstream Sail `extend_value` functional core (`LeanRV64D/BaseInsts.lean`, lines 496–499):
    zero-extends when `is_unsigned = true` (`LBU`/`LHU`/`LWU`) and sign-extends otherwise
    (`LB`/`LH`/`LW`/`LD`). -/
def sailExtendValueCore {w : Nat} (is_unsigned : Bool) (value : BitVec w) : BitVec 64 :=
  if is_unsigned then zero_extend (m := 64) value else sign_extend (m := 64) value

/-- Pure `TurboLean`-side RV64I load extension specification across any bit-width `w`. -/
def rv64iLoadExtendSpec {w : Nat} (is_unsigned : Bool) (value : BitVec w) : BitVec 64 :=
  if is_unsigned then value.zeroExtend 64 else value.signExtend 64

/-- Exact upstream Sail `execute_STORE` data-slicing core (`LeanRV64D/InstsEnd.lean`, line 67367)
    specialized to any positive byte-width `width`: `Sail.BitVec.extractLsb rs2_val ((width *i 8) -i 1) 0`. -/
def sailStoreDataCore (width : Nat) (hw : 0 < width) (rs2_val : BitVec 64) : BitVec (8 * width) :=
  have hlen : (((Int.ofNat width *i 8) -i 1) -i 0 +i 1).toNat = 8 * width := by
    change (((width : Int) * 8 - 1) - 0 + 1).toNat = 8 * width
    omega
  hlen ▸ Sail.BitVec.extractLsb rs2_val ((Int.ofNat width *i 8) -i 1) 0

/-- Pure `TurboLean`-side RV64I store-data truncation specification (`rs2_val.truncate (8 * width)`). -/
def rv64iStoreTruncateSpec (width : Nat) (rs2_val : BitVec 64) : BitVec (8 * width) :=
  rs2_val.truncate (8 * width)

/-- Pure little-endian assembly of `width` consecutive bytes starting at `addr.toNat` in
    `SequentialState.mem`, matching `Sail.ConcurrencyInterfaceV1.PreSail.readBytes`. -/
def rv64ReadMemBytesSpec : (width : Nat) → Nat → Std.ExtHashMap Nat (BitVec 8) → Option (BitVec (8 * width))
  | 0, _, _ => some 0#0
  | 1, addr, mem =>
    match mem[addr]? with
    | some b =>
      have h : 8 * 1 = 8 := rfl
      some (h ▸ b)
    | none => none
  | n + 1, addr, mem =>
    match mem[addr]?, rv64ReadMemBytesSpec n (addr + 1) mem with
    | some b, some hi =>
      have h : 8 * n + 8 = 8 * (n + 1) := by omega
      some (h ▸ hi.append b)
    | _, _ => none

/-- Pure little-endian decomposition writing `width` bytes of `data` into `mem` at `addr .. addr + width - 1`. -/
def rv64WriteMemBytesSpec (width : Nat) (addr : Nat) (data : BitVec (8 * width))
    (mem : Std.ExtHashMap Nat (BitVec 8)) : Std.ExtHashMap Nat (BitVec 8) :=
  (List.ofFn (fun i : Fin width => (addr + i.val, data.extractLsb' (8 * i.val) 8))).foldl
    (fun m (a, v) => m.insert a v) mem

/-- Exact upstream Sail `execute_LOAD` monadic pipeline (`LeanRV64D/InstsEnd.lean`, lines 69237–69245)
    over flat physical RAM (`ext_data_get_addr` → `read_ram Read_plain` → `extend_value` → `wX_bits`). -/
def sailLoadRamExec (imm : BitVec 12) (rs1 rd : regidx) (is_unsigned : Bool) (width : Nat) :
    SailM ExecutionResult := do
  let offset : xlenbits := sign_extend (m := 64) imm
  PreSail.assert (width ≤b Functions.xlen_bytes) "extensions/I/base_insts.sail:289.28-289.29"
  match (← ext_data_get_addr rs1 offset (.Load .Data) width) with
  | .Ext_DataAddr_OK (.Virtaddr vaddr) =>
    let (data, _) ← LeanRV64D.Functions.read_ram .Read_plain (.Physaddr vaddr) width false
    wX_bits rd (sailExtendValueCore is_unsigned data)
    pure (.Retire_Success ())
  | .Ext_DataAddr_Error e => pure (.Ext_DataAddr_Check_Failure e)

/-- Exact upstream Sail `execute_STORE` monadic pipeline (`LeanRV64D/InstsEnd.lean`, lines 67364–67370)
    over flat physical RAM (`ext_data_get_addr` → `extractLsb` → `write_ram Write_plain`). -/
def sailStoreRamExec (imm : BitVec 12) (rs2 rs1 : regidx) (width : Nat) (hw : 0 < width) :
    SailM ExecutionResult := do
  let offset : xlenbits := sign_extend (m := 64) imm
  PreSail.assert (width ≤b Functions.xlen_bytes) "extensions/I/base_insts.sail:320.28-320.29"
  let data : BitVec (8 * width) := sailStoreDataCore width hw (← rX_bits rs2)
  match (← ext_data_get_addr rs1 offset (.Store .Data) width) with
  | .Ext_DataAddr_OK (.Virtaddr vaddr) =>
    let _ ← LeanRV64D.Functions.write_ram .Write_plain (.Physaddr vaddr) width data ()
    pure (.Retire_Success ())
  | .Ext_DataAddr_Error e => pure (.Ext_DataAddr_Check_Failure e)

/-- Monadic bisimulation for upstream `LeanRV64D.Functions.ext_data_get_addr` (`AddrChecks.lean`,
    lines 228–230) on `x2` (`sp`): computes `Ext_DataAddr_OK (Virtaddr (rs1_val + sext(imm12)))`
    without mutating machine state. -/
theorem rv64iEffectiveAddr_ext_data_get_addr_bisim (rs1_val : BitVec 64) (imm : BitVec 12)
    (acc : MemoryAccessType mem_payload) (width : Nat)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : s.regs.get? .x2 = some rs1_val) :
    (ext_data_get_addr sp (sign_extend (m := 64) imm) acc width).run s =
      .ok (.Ext_DataAddr_OK (.Virtaddr (rv64iEffectiveAddrSpec rs1_val imm))) s := by
  unfold ext_data_get_addr rv64iEffectiveAddrSpec sp
  simp [rX_bits, rX, regval_from_reg, zero_extend, Sail.BitVec.zeroExtend,
    sign_extend, Sail.BitVec.signExtend, Sail.BitVec.toNatInt,
    readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
  dsimp [EStateM.bind, EStateM.get, EStateM.pure, EStateM.run]
  rw [hrs1]
  rfl

/-- Upstream `is_aligned_vaddr` and `is_aligned_paddr` (`SplitAccessUtils.lean`, lines 220–228)
    and `width_enc_backwards` (`Types.lean`, lines 888–894) agree with `addr.toNat % width == 0`
    across every access width (in particular all RV64I widths `1, 2, 4, 8`). -/
theorem rv64iAlignedAddr_bisim_sail (addr : BitVec 64) (width : Nat) :
    is_aligned_vaddr (.Virtaddr addr) width = rv64iAlignedAddrSpec addr width ∧
      is_aligned_paddr (.Physaddr addr) width = rv64iAlignedAddrSpec addr width ∧
      width_enc_backwards 0b00#2 = 1 ∧
      width_enc_backwards 0b01#2 = 2 ∧
      width_enc_backwards 0b10#2 = 4 ∧
      width_enc_backwards 0b11#2 = 8 := by
  have halign : ((Int.tmod (Sail.BitVec.toNatInt addr) (Int.ofNat width)) == 0) =
      (addr.toNat % width == 0) := by
    unfold Sail.BitVec.toNatInt
    have htmod : Int.tmod (Int.ofNat addr.toNat) (Int.ofNat width) = Int.ofNat (addr.toNat % width) := rfl
    rw [htmod]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact ⟨Int.ofNat.inj, congrArg Int.ofNat⟩
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
  · unfold is_aligned_vaddr rv64iAlignedAddrSpec
    exact halign
  · unfold is_aligned_paddr rv64iAlignedAddrSpec
    exact halign

/-- RV64I load-extension bisimulation (`LB`/`LBU`, `LH`/`LHU`, `LW`/`LWU`, `LD`) plus 64-bit
    `LD` identity (`extend_value false v64 = v64` and `extend_value true v64 = v64`). -/
theorem rv64iLoadExtend_bisim_sail (is_unsigned : Bool)
    (b8 : BitVec 8) (b16 : BitVec 16) (b32 : BitVec 32) (b64 : BitVec 64) :
    rv64iLoadExtendSpec is_unsigned b8 = sailExtendValueCore is_unsigned b8 ∧
      rv64iLoadExtendSpec is_unsigned b16 = sailExtendValueCore is_unsigned b16 ∧
      rv64iLoadExtendSpec is_unsigned b32 = sailExtendValueCore is_unsigned b32 ∧
      rv64iLoadExtendSpec is_unsigned b64 = b64 ∧
      sailExtendValueCore is_unsigned b64 = b64 := by
  cases is_unsigned <;> simp [rv64iLoadExtendSpec, sailExtendValueCore,
    zero_extend, Sail.BitVec.zeroExtend, sign_extend, Sail.BitVec.signExtend]

/-- RV64I store-truncation bisimulation across `SB` (`width = 1`), `SH` (`width = 2`),
    `SW` (`width = 4`), and `SD` (`width = 8`): Sail's `extractLsb rs2_val ((width *i 8) -i 1) 0`
    equals `rs2_val.truncate (8 * width)`. -/
theorem rv64iStoreTruncate_bisim_sail (rs2_val : BitVec 64) :
    rv64iStoreTruncateSpec 1 rs2_val = sailStoreDataCore 1 (by decide) rs2_val ∧
      rv64iStoreTruncateSpec 2 rs2_val = sailStoreDataCore 2 (by decide) rs2_val ∧
      rv64iStoreTruncateSpec 4 rs2_val = sailStoreDataCore 4 (by decide) rs2_val ∧
      rv64iStoreTruncateSpec 8 rs2_val = sailStoreDataCore 8 (by decide) rs2_val := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · unfold rv64iStoreTruncateSpec sailStoreDataCore Sail.BitVec.extractLsb
    dsimp only
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp [BitVec.extractLsb]

private theorem writeBytes_run_eq_spec {n : Nat} (addr : Nat) (val : BitVec (8 * n))
    (s : SequentialState RegisterType trivialChoiceSource) :
    ((PreSail.writeBytes addr val : SailM Bool).run s) =
      .ok true { s with mem := rv64WriteMemBytesSpec n addr val s.mem } := by
  unfold PreSail.writeBytes rv64WriteMemBytesSpec
  generalize (List.ofFn (fun i : Fin n => (addr + i.val, val.extractLsb' (8 * i.val) 8))) = pairs
  induction pairs generalizing s with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    dsimp [List.forM, List.foldl, PreSail.writeByte, modify, modifyGet, MonadStateOf.modifyGet,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.modifyGet, EStateM.pure, EStateM.run]
    exact ih { s with mem := s.mem.insert a b }

private theorem readByte_run_of_get? (addr : Nat) (b : BitVec 8)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hm : s.mem[addr]? = some b) :
    ((PreSail.readByte addr : SailM (BitVec 8)).run s) = .ok b s := by
  unfold PreSail.readByte
  dsimp [get, getThe, MonadStateOf.get, Bind.bind, Pure.pure,
    EStateM.bind, EStateM.get, EStateM.pure, EStateM.throw, EStateM.run]
  rw [hm]
  rfl

private theorem readBytes_run_of_spec_some :
    ∀ (n addr : Nat) (s : SequentialState RegisterType trivialChoiceSource) (bytes : BitVec (8 * n)),
      rv64ReadMemBytesSpec n addr s.mem = some bytes →
      ((PreSail.readBytes n addr : SailM (BitVec (8 * n) × Option Bool)).run s) = .ok (bytes, none) s
  | 0, addr, s, bytes, h => by
    simp only [rv64ReadMemBytesSpec, Option.some.injEq] at h
    subst h
    rfl
  | 1, addr, s, bytes, h => by
    simp only [rv64ReadMemBytesSpec] at h
    cases hm : s.mem[addr]? with
    | none => simp [hm] at h
    | some b =>
      simp only [hm, Option.some.injEq] at h
      subst h
      have hb := readByte_run_of_get? addr b s hm
      unfold PreSail.readBytes
      dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at hb ⊢
      rw [hb]
  | n + 2, addr, s, bytes, h => by
    simp only [rv64ReadMemBytesSpec] at h
    cases hm : s.mem[addr]? with
    | none => simp [hm] at h
    | some b =>
      cases hr : rv64ReadMemBytesSpec (n + 1) (addr + 1) s.mem with
      | none => simp [hm, hr] at h
      | some hi =>
        simp only [hm, hr, Option.some.injEq] at h
        subst h
        have ih := readBytes_run_of_spec_some (n + 1) (addr + 1) s hi hr
        have hb := readByte_run_of_get? addr b s hm
        change (EStateM.bind (PreSail.readByte addr) fun b' =>
          EStateM.bind (PreSail.readBytes (n + 1) (addr + 1)) fun __discr =>
            EStateM.pure (__discr.fst +++ b', __discr.snd)) s = .ok (hi +++ b, none) s
        dsimp [EStateM.bind, EStateM.pure, EStateM.run] at hb ih ⊢
        rw [hb]
        dsimp only
        rw [ih]

/-- Monadic bisimulation for upstream `LeanRV64D.Functions.write_ram` (`PhysMemInterface.lean`,
    lines 303–338) in `.Write_plain` mode: updates `SequentialState.mem` in little-endian byte order
    via `rv64WriteMemBytesSpec` and returns `true`. -/
theorem write_ram_plain_bisim_sail (width : Nat) (paddr : BitVec 64) (data : BitVec (8 * width))
    (s : SequentialState RegisterType trivialChoiceSource) :
    (LeanRV64D.Functions.write_ram .Write_plain (.Physaddr paddr) width data ()).run s =
      .ok true { s with mem := rv64WriteMemBytesSpec width paddr.toNat data s.mem } := by
  have hw := writeBytes_run_eq_spec paddr.toNat data s
  unfold LeanRV64D.Functions.write_ram LeanRV64D.ConcurrencyInterfaceV1.sail_mem_write
    PreSail.sail_mem_write __WriteRAM_Meta
  dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at hw ⊢
  rw [hw]
  rfl

/-- Monadic bisimulation for upstream `LeanRV64D.Functions.read_ram` (`PhysMemInterface.lean`,
    lines 346–381) in `.Read_plain` mode: reassembles `width` little-endian bytes from
    `SequentialState.mem` without mutating state whenever all target byte addresses are mapped. -/
theorem read_ram_plain_bisim_sail (width : Nat) (paddr : BitVec 64) (bytes : BitVec (8 * width))
    (s : SequentialState RegisterType trivialChoiceSource)
    (hmem : rv64ReadMemBytesSpec width paddr.toNat s.mem = some bytes) :
    (LeanRV64D.Functions.read_ram .Read_plain (.Physaddr paddr) width false).run s =
      .ok (bytes, ()) s := by
  have hr := readBytes_run_of_spec_some width paddr.toNat s bytes hmem
  unfold LeanRV64D.Functions.read_ram LeanRV64D.ConcurrencyInterfaceV1.sail_mem_read
    PreSail.sail_mem_read default_meta
  dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at hr ⊢
  rw [hr]
  rfl

private theorem wX_bits_ra_run (val : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource) :
    (wX_bits ra val).run s = .ok () { s with regs := s.regs.insert .x1 val } := by
  unfold ra
  simp [wX_bits, wX, regval_into_reg, xreg_write_callback, reg_name_forwards,
    encdec_reg_forwards_matches, encdec_reg_forwards, get_config_use_abi_names,
    LeanRV64D.Functions.not, reg_arch_name_raw_forwards, xreg_full_write_callback,
    zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.toNatInt, to_bits, get_slice_int,
    writeReg, PreSail.writeReg, modify, modifyGet, MonadStateOf.modifyGet]
  rfl

private theorem rX_bits_ra_run (val : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hx1 : s.regs.get? .x1 = some val) :
    (rX_bits ra).run s = .ok val s := by
  unfold ra
  simp [rX_bits, rX, regval_from_reg, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.toNatInt,
    readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
  dsimp [EStateM.bind, EStateM.get, EStateM.pure, EStateM.run]
  rw [hx1]
  rfl

/-- End-to-end `SailM` bisimulation for RV64I `execute_STORE` (`SB`/`SH`/`SW`/`SD`) over flat
    physical RAM (`rs1 = sp`, `rs2 = ra`): truncates `rs2_val` to `8 * width` bits and commits
    little-endian bytes at `rs1_val + sext(imm)` without mutating architectural registers. -/
theorem sailStoreRamExec_sp_ra_bisim (imm : BitVec 12) (width : Nat)
    (hw : 0 < width) (hmax : (width ≤b Functions.xlen_bytes) = true)
    (rs1_val rs2_val : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : s.regs.get? .x2 = some rs1_val)
    (hrs2 : s.regs.get? .x1 = some rs2_val) :
    (sailStoreRamExec imm ra sp width hw).run s =
      .ok (.Retire_Success ())
        { s with mem := (rv64WriteMemBytesSpec width
            (BitVec.toNat (rv64iEffectiveAddrSpec rs1_val imm))
            (sailStoreDataCore width hw rs2_val) s.mem) } := by
  have hassert : (PreSail.assert (width ≤b Functions.xlen_bytes)
      "extensions/I/base_insts.sail:320.28-320.29" : SailM Unit).run s = .ok () s := by
    unfold PreSail.assert
    rw [hmax]
    rfl
  have hr2 := rX_bits_ra_run rs2_val s hrs2
  have haddr := rv64iEffectiveAddr_ext_data_get_addr_bisim rs1_val imm (.Store .Data) width s hrs1
  have hwrite := write_ram_plain_bisim_sail width (rv64iEffectiveAddrSpec rs1_val imm)
    (sailStoreDataCore width hw rs2_val) s
  unfold sailStoreRamExec
  dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at hassert hr2 haddr hwrite ⊢
  rw [hassert]
  dsimp only
  rw [hr2]
  dsimp only
  rw [haddr]
  dsimp [EStateM.bind]
  rw [hwrite]
  rfl

/-- End-to-end `SailM` bisimulation for RV64I `execute_LOAD` (`LB`/`LBU`/`LH`/`LHU`/`LW`/`LWU`/`LD`)
    over flat physical RAM (`rs1 = sp`, `rd = ra`): reads `width` little-endian bytes from
    `rs1_val + sext(imm)` and writes `rv64iLoadExtendSpec is_unsigned bytes` into `x1`. -/
theorem sailLoadRamExec_sp_ra_bisim (imm : BitVec 12) (is_unsigned : Bool) (width : Nat)
    (hmax : (width ≤b Functions.xlen_bytes) = true)
    (rs1_val : BitVec 64) (bytes : BitVec (8 * width))
    (s : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : s.regs.get? .x2 = some rs1_val)
    (hmem : rv64ReadMemBytesSpec width (BitVec.toNat (rv64iEffectiveAddrSpec rs1_val imm)) s.mem = some bytes) :
    (sailLoadRamExec imm sp ra is_unsigned width).run s =
      .ok (.Retire_Success ())
        ({ s with regs := s.regs.insert .x1 (rv64iLoadExtendSpec is_unsigned bytes) }) := by
  have hassert : (PreSail.assert (width ≤b Functions.xlen_bytes)
      "extensions/I/base_insts.sail:289.28-289.29" : SailM Unit).run s = .ok () s := by
    unfold PreSail.assert
    rw [hmax]
    rfl
  have haddr := rv64iEffectiveAddr_ext_data_get_addr_bisim rs1_val imm (.Load .Data) width s hrs1
  have hread := read_ram_plain_bisim_sail width (rv64iEffectiveAddrSpec rs1_val imm) bytes s hmem
  have hext : sailExtendValueCore is_unsigned bytes = rv64iLoadExtendSpec is_unsigned bytes := by
    cases is_unsigned <;> simp [sailExtendValueCore, rv64iLoadExtendSpec,
      zero_extend, Sail.BitVec.zeroExtend, sign_extend, Sail.BitVec.signExtend]
  have hw1 := wX_bits_ra_run (rv64iLoadExtendSpec is_unsigned bytes) s
  unfold sailLoadRamExec
  dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at hassert haddr hread hw1 ⊢
  rw [hassert]
  dsimp only
  rw [haddr]
  dsimp [EStateM.bind]
  rw [hread]
  dsimp only
  rw [hext, hw1]
  rfl

/-- Little-endian byte roundtrip for `SB` (`width = 1`): reading 1 byte after writing 1 byte at the
    same address recovers the exact stored byte. -/
theorem rv64StoreLoadBytes_roundtrip_1 (addr : Nat) (b : BitVec 8)
    (mem : Std.ExtHashMap Nat (BitVec 8)) :
    rv64ReadMemBytesSpec 1 addr (rv64WriteMemBytesSpec 1 addr b mem) = some b := by
  have hb : b.extractLsb' 0 8 = b := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi]
  simp [rv64WriteMemBytesSpec, rv64ReadMemBytesSpec, hb]

private theorem extHashMap_getElem?_insert_ne (m : Std.ExtHashMap Nat (BitVec 8))
    (k k' : Nat) (v : BitVec 8) (hne : k ≠ k') :
    (m.insert k v)[k']? = m[k']? := by
  rw [Std.ExtHashMap.getElem?_insert, beq_false_of_ne hne]
  rfl

/-- Little-endian byte roundtrip for `SH` (`width = 2`): reading 2 bytes after writing 2 bytes at
    `addr .. addr + 1` reassembles the exact 16-bit halfword. -/
theorem rv64StoreLoadBytes_roundtrip_2 (addr : Nat) (val : BitVec 16)
    (mem : Std.ExtHashMap Nat (BitVec 8)) :
    rv64ReadMemBytesSpec 2 addr (rv64WriteMemBytesSpec 2 addr val mem) = some val := by
  simp only [rv64WriteMemBytesSpec, rv64ReadMemBytesSpec, List.ofFn, Fin.foldr, Fin.foldr.loop,
    List.foldl, Nat.add_zero]
  rw [extHashMap_getElem?_insert_ne _ _ _ _ (by omega),
    Std.ExtHashMap.getElem?_insert_self, Std.ExtHashMap.getElem?_insert_self]
  dsimp only
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.append_eq, BitVec.getLsbD_append]
  by_cases h8 : i < 8
  · simp [h8]
  · have hlt : i - 8 < 8 := by omega
    have hadd : 8 * 1 + (i - 8) = i := by omega
    simp [h8, hlt, hadd]

/-- Little-endian byte roundtrip for `SW` (`width = 4`): reading 4 bytes after writing 4 bytes at
    `addr .. addr + 3` reassembles the exact 32-bit word. -/
theorem rv64StoreLoadBytes_roundtrip_4 (addr : Nat) (val : BitVec 32)
    (mem : Std.ExtHashMap Nat (BitVec 8)) :
    rv64ReadMemBytesSpec 4 addr (rv64WriteMemBytesSpec 4 addr val mem) = some val := by
  simp only [rv64WriteMemBytesSpec, rv64ReadMemBytesSpec, List.ofFn, Fin.foldr, Fin.foldr.loop,
    List.foldl, Nat.add_zero, Nat.add_assoc]
  repeat first
    | rw [Std.ExtHashMap.getElem?_insert_self]
    | rw [extHashMap_getElem?_insert_ne _ _ _ _ (by omega)]
  dsimp only
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.append_eq, BitVec.getLsbD_append]
  rcases (show i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) by omega) with
    h | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩
  · simp [h]
  · have h0 : ¬(i < 8) := by omega
    have h1 : i - 8 < 8 := by omega
    have ha : 8 * 1 + (i - 8) = i := by omega
    simp [h0, h1, ha]
  · have h0 : ¬(i < 8) := by omega
    have h1 : ¬(i - 8 < 8) := by omega
    have h2 : i - 8 - 8 < 8 := by omega
    have ha : 8 * 2 + (i - 8 - 8) = i := by omega
    simp [h0, h1, h2, ha]
  · have h0 : ¬(i < 8) := by omega
    have h1 : ¬(i - 8 < 8) := by omega
    have h2 : ¬(i - 8 - 8 < 8) := by omega
    have h3 : i - 8 - 8 - 8 < 8 := by omega
    have ha : 8 * 3 + (i - 8 - 8 - 8) = i := by omega
    simp [h0, h1, h2, h3, ha]

/-- Little-endian byte roundtrip for `SD` (`width = 8`): reading 8 bytes after writing 8 bytes at
    `addr .. addr + 7` reassembles the exact 64-bit doubleword. -/
theorem rv64StoreLoadBytes_roundtrip_8 (addr : Nat) (val : BitVec 64)
    (mem : Std.ExtHashMap Nat (BitVec 8)) :
    rv64ReadMemBytesSpec 8 addr (rv64WriteMemBytesSpec 8 addr val mem) = some val := by
  simp only [rv64WriteMemBytesSpec, rv64ReadMemBytesSpec, List.ofFn, Fin.foldr, Fin.foldr.loop,
    List.foldl, Nat.add_zero, Nat.add_assoc]
  repeat first
    | rw [Std.ExtHashMap.getElem?_insert_self]
    | rw [extHashMap_getElem?_insert_ne _ _ _ _ (by omega)]
  dsimp only
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.append_eq, BitVec.getLsbD_append]
  rcases (show i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨
      (32 ≤ i ∧ i < 40) ∨ (40 ≤ i ∧ i < 48) ∨ (48 ≤ i ∧ i < 56) ∨ (56 ≤ i ∧ i < 64) by omega) with
    h | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩
  · simp [h]
  · have h0 : ¬(i < 8) := by omega
    have h1 : i - 8 < 8 := by omega
    have ha : 8 * 1 + (i - 8) = i := by omega
    simp [h0, h1, ha]
  · have h0 : ¬(i < 8) := by omega
    have h1 : ¬(i - 8 < 8) := by omega
    have h2 : i - 8 - 8 < 8 := by omega
    have ha : 8 * 2 + (i - 8 - 8) = i := by omega
    simp [h0, h1, h2, ha]
  · have h0 : ¬(i < 8) := by omega
    have h1 : ¬(i - 8 < 8) := by omega
    have h2 : ¬(i - 8 - 8 < 8) := by omega
    have h3 : i - 8 - 8 - 8 < 8 := by omega
    have ha : 8 * 3 + (i - 8 - 8 - 8) = i := by omega
    simp [h0, h1, h2, h3, ha]
  · have h0 : ¬(i < 8) := by omega
    have h1 : ¬(i - 8 < 8) := by omega
    have h2 : ¬(i - 8 - 8 < 8) := by omega
    have h3 : ¬(i - 8 - 8 - 8 < 8) := by omega
    have h4 : i - 8 - 8 - 8 - 8 < 8 := by omega
    have ha : 8 * 4 + (i - 8 - 8 - 8 - 8) = i := by omega
    simp [h0, h1, h2, h3, h4, ha]
  · have h0 : ¬(i < 8) := by omega
    have h1 : ¬(i - 8 < 8) := by omega
    have h2 : ¬(i - 8 - 8 < 8) := by omega
    have h3 : ¬(i - 8 - 8 - 8 < 8) := by omega
    have h4 : ¬(i - 8 - 8 - 8 - 8 < 8) := by omega
    have h5 : i - 8 - 8 - 8 - 8 - 8 < 8 := by omega
    have ha : 8 * 5 + (i - 8 - 8 - 8 - 8 - 8) = i := by omega
    simp [h0, h1, h2, h3, h4, h5, ha]
  · have h0 : ¬(i < 8) := by omega
    have h1 : ¬(i - 8 < 8) := by omega
    have h2 : ¬(i - 8 - 8 < 8) := by omega
    have h3 : ¬(i - 8 - 8 - 8 < 8) := by omega
    have h4 : ¬(i - 8 - 8 - 8 - 8 < 8) := by omega
    have h5 : ¬(i - 8 - 8 - 8 - 8 - 8 < 8) := by omega
    have h6 : i - 8 - 8 - 8 - 8 - 8 - 8 < 8 := by omega
    have ha : 8 * 6 + (i - 8 - 8 - 8 - 8 - 8 - 8) = i := by omega
    simp [h0, h1, h2, h3, h4, h5, h6, ha]
  · have h0 : ¬(i < 8) := by omega
    have h1 : ¬(i - 8 < 8) := by omega
    have h2 : ¬(i - 8 - 8 < 8) := by omega
    have h3 : ¬(i - 8 - 8 - 8 < 8) := by omega
    have h4 : ¬(i - 8 - 8 - 8 - 8 < 8) := by omega
    have h5 : ¬(i - 8 - 8 - 8 - 8 - 8 < 8) := by omega
    have h6 : ¬(i - 8 - 8 - 8 - 8 - 8 - 8 < 8) := by omega
    have h7 : i - 8 - 8 - 8 - 8 - 8 - 8 - 8 < 8 := by omega
    have ha : 8 * 7 + (i - 8 - 8 - 8 - 8 - 8 - 8 - 8) = i := by omega
    simp [h0, h1, h2, h3, h4, h5, h6, h7, ha]

/-- End-to-end `SailM` store-then-load roundtrip theorem across `SB`→`LB`/`LBU`, `SH`→`LH`/`LHU`,
    `SW`→`LW`/`LWU`, and `SD`→`LD`: storing `rs2_val` via `sailStoreRamExec` and immediately
    reloading via `sailLoadRamExec` at the same `(sp, imm)` effective address writes the exact
    signed/unsigned extended truncation into `x1` (and for `SD`→`LD`, recovers `rs2_val` verbatim). -/
theorem rv64StoreThenLoad_roundtrip_bisim (imm : BitVec 12) (is_unsigned : Bool)
    (rs1_val rs2_val : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : s.regs.get? .x2 = some rs1_val)
    (hrs2 : s.regs.get? .x1 = some rs2_val) :
    ((do
        let _ ← sailStoreRamExec imm ra sp 1 (by decide)
        let _ ← sailLoadRamExec imm sp ra is_unsigned 1
        rX_bits ra).run s =
      .ok (rv64iLoadExtendSpec is_unsigned (rs2_val.truncate 8))
        { s with
            mem := (rv64WriteMemBytesSpec 1 (BitVec.toNat (rv64iEffectiveAddrSpec rs1_val imm))
              (rs2_val.truncate 8) s.mem),
            regs := s.regs.insert .x1 (rv64iLoadExtendSpec is_unsigned (rs2_val.truncate 8)) }) ∧
    ((do
        let _ ← sailStoreRamExec imm ra sp 2 (by decide)
        let _ ← sailLoadRamExec imm sp ra is_unsigned 2
        rX_bits ra).run s =
      .ok (rv64iLoadExtendSpec is_unsigned (rs2_val.truncate 16))
        { s with
            mem := (rv64WriteMemBytesSpec 2 (BitVec.toNat (rv64iEffectiveAddrSpec rs1_val imm))
              (rs2_val.truncate 16) s.mem),
            regs := s.regs.insert .x1 (rv64iLoadExtendSpec is_unsigned (rs2_val.truncate 16)) }) ∧
    ((do
        let _ ← sailStoreRamExec imm ra sp 4 (by decide)
        let _ ← sailLoadRamExec imm sp ra is_unsigned 4
        rX_bits ra).run s =
      .ok (rv64iLoadExtendSpec is_unsigned (rs2_val.truncate 32))
        { s with
            mem := (rv64WriteMemBytesSpec 4 (BitVec.toNat (rv64iEffectiveAddrSpec rs1_val imm))
              (rs2_val.truncate 32) s.mem),
            regs := s.regs.insert .x1 (rv64iLoadExtendSpec is_unsigned (rs2_val.truncate 32)) }) ∧
    ((do
        let _ ← sailStoreRamExec imm ra sp 8 (by decide)
        let _ ← sailLoadRamExec imm sp ra false 8
        rX_bits ra).run s =
      .ok rs2_val
        { s with
            mem := (rv64WriteMemBytesSpec 8 (BitVec.toNat (rv64iEffectiveAddrSpec rs1_val imm))
              rs2_val s.mem),
            regs := s.regs.insert .x1 rs2_val }) := by
  rcases rv64iStoreTruncate_bisim_sail rs2_val with ⟨ht1, ht2, ht4, ht8⟩
  have htr64 : rs2_val.truncate 64 = rs2_val := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hst := sailStoreRamExec_sp_ra_bisim imm 1 (by decide) (by decide) rs1_val rs2_val s hrs1 hrs2
    rw [← ht1] at hst
    let s1 : SequentialState RegisterType trivialChoiceSource :=
      { s with mem := (rv64WriteMemBytesSpec 1
          (BitVec.toNat (rv64iEffectiveAddrSpec rs1_val imm))
          (rs2_val.truncate 8) s.mem) }
    have hld := sailLoadRamExec_sp_ra_bisim imm is_unsigned 1 (by decide) rs1_val (rs2_val.truncate 8) s1
      hrs1 (rv64StoreLoadBytes_roundtrip_1 _ _ _)
    let s2 : SequentialState RegisterType trivialChoiceSource :=
      { s1 with regs := s.regs.insert .x1 (rv64iLoadExtendSpec is_unsigned (rs2_val.truncate 8)) }
    have hrd := rX_bits_ra_run (rv64iLoadExtendSpec is_unsigned (rs2_val.truncate 8)) s2
      (by simp [s2, Std.ExtDHashMap.get?_insert_self])
    dsimp [rv64iStoreTruncateSpec] at hst
    dsimp [Bind.bind, EStateM.bind, EStateM.run, s1, s2] at hst hld hrd ⊢
    rw [hst]; dsimp only; rw [hld]; dsimp only; exact hrd
  · have hst := sailStoreRamExec_sp_ra_bisim imm 2 (by decide) (by decide) rs1_val rs2_val s hrs1 hrs2
    rw [← ht2] at hst
    let s1 : SequentialState RegisterType trivialChoiceSource :=
      { s with mem := (rv64WriteMemBytesSpec 2
          (BitVec.toNat (rv64iEffectiveAddrSpec rs1_val imm))
          (rs2_val.truncate 16) s.mem) }
    have hld := sailLoadRamExec_sp_ra_bisim imm is_unsigned 2 (by decide) rs1_val (rs2_val.truncate 16) s1
      hrs1 (rv64StoreLoadBytes_roundtrip_2 _ _ _)
    let s2 : SequentialState RegisterType trivialChoiceSource :=
      { s1 with regs := s.regs.insert .x1 (rv64iLoadExtendSpec is_unsigned (rs2_val.truncate 16)) }
    have hrd := rX_bits_ra_run (rv64iLoadExtendSpec is_unsigned (rs2_val.truncate 16)) s2
      (by simp [s2, Std.ExtDHashMap.get?_insert_self])
    dsimp [rv64iStoreTruncateSpec] at hst
    dsimp [Bind.bind, EStateM.bind, EStateM.run, s1, s2] at hst hld hrd ⊢
    rw [hst]; dsimp only; rw [hld]; dsimp only; exact hrd
  · have hst := sailStoreRamExec_sp_ra_bisim imm 4 (by decide) (by decide) rs1_val rs2_val s hrs1 hrs2
    rw [← ht4] at hst
    let s1 : SequentialState RegisterType trivialChoiceSource :=
      { s with mem := (rv64WriteMemBytesSpec 4
          (BitVec.toNat (rv64iEffectiveAddrSpec rs1_val imm))
          (rs2_val.truncate 32) s.mem) }
    have hld := sailLoadRamExec_sp_ra_bisim imm is_unsigned 4 (by decide) rs1_val (rs2_val.truncate 32) s1
      hrs1 (rv64StoreLoadBytes_roundtrip_4 _ _ _)
    let s2 : SequentialState RegisterType trivialChoiceSource :=
      { s1 with regs := s.regs.insert .x1 (rv64iLoadExtendSpec is_unsigned (rs2_val.truncate 32)) }
    have hrd := rX_bits_ra_run (rv64iLoadExtendSpec is_unsigned (rs2_val.truncate 32)) s2
      (by simp [s2, Std.ExtDHashMap.get?_insert_self])
    dsimp [rv64iStoreTruncateSpec] at hst
    dsimp [Bind.bind, EStateM.bind, EStateM.run, s1, s2] at hst hld hrd ⊢
    rw [hst]; dsimp only; rw [hld]; dsimp only; exact hrd
  · have hst := sailStoreRamExec_sp_ra_bisim imm 8 (by decide) (by decide) rs1_val rs2_val s hrs1 hrs2
    rw [← ht8] at hst
    change (sailStoreRamExec imm ra sp 8 (by decide)).run s = .ok (.Retire_Success ())
      { s with mem := (rv64WriteMemBytesSpec 8
          (BitVec.toNat (rv64iEffectiveAddrSpec rs1_val imm))
          (rs2_val.truncate 64) s.mem) } at hst
    rw [htr64] at hst
    let s1 : SequentialState RegisterType trivialChoiceSource :=
      { s with mem := (rv64WriteMemBytesSpec 8
          (BitVec.toNat (rv64iEffectiveAddrSpec rs1_val imm))
          rs2_val s.mem) }
    have hld := sailLoadRamExec_sp_ra_bisim imm false 8 (by decide) rs1_val rs2_val s1
      hrs1 (rv64StoreLoadBytes_roundtrip_8 _ _ _)
    have hextId : rv64iLoadExtendSpec false rs2_val = rs2_val := by simp [rv64iLoadExtendSpec]
    rw [hextId] at hld
    let s2 : SequentialState RegisterType trivialChoiceSource :=
      { s1 with regs := s.regs.insert .x1 rs2_val }
    have hrd := rX_bits_ra_run rs2_val s2 (by simp [s2, Std.ExtDHashMap.get?_insert_self])
    dsimp [Bind.bind, EStateM.bind, EStateM.run, s1, s2] at hst hld hrd ⊢
    rw [hst]; dsimp only; rw [hld]; dsimp only; exact hrd

/-! ## 13. RVC Compressed Instruction Fragment (`Zca` / `Zcb` / RV64C) -/

/-- Pure `TurboLean`-side RVC 3-bit compressed register index decoding (`creg2reg_idx`,
    `LeanRV64D/Types.lean`, lines 223–225): maps `i : BitVec 3` (`0..7`) to architectural
    register index `x8..x15` (`8#5 + i.zeroExtend 5`). -/
def rvcRegIdxSpec (i : BitVec 3) : regidx :=
  .Regidx (8#5 + i.zeroExtend 5)

/-- RVC compressed register index decoding (`creg2reg_idx`) bisimulation: proves `creg2reg_idx`
    matches `rvcRegIdxSpec`, yields architectural indices in `[8, 15]`, and never aliases `zreg` (`x0`). -/
theorem rvcRegIdx_creg2reg_idx_bisim (i : BitVec 3) :
    regidx_bits (creg2reg_idx (.Cregidx i)) = regidx_bits (rvcRegIdxSpec i) ∧
      creg2reg_idx (.Cregidx i) = rvcRegIdxSpec i ∧
      8 ≤ (regidx_bits (creg2reg_idx (.Cregidx i))).toNat ∧
      (regidx_bits (creg2reg_idx (.Cregidx i))).toNat < 16 ∧
      creg2reg_idx (.Cregidx i) ≠ zreg := by
  have hbits : regidx_bits (creg2reg_idx (.Cregidx i)) = regidx_bits (rvcRegIdxSpec i) := by
    revert i; decide
  have hlo : 8 ≤ (regidx_bits (creg2reg_idx (.Cregidx i))).toNat := by
    revert i; decide
  have hhi : (regidx_bits (creg2reg_idx (.Cregidx i))).toNat < 16 := by
    revert i; decide
  have hreg : creg2reg_idx (.Cregidx i) = rvcRegIdxSpec i := by
    unfold creg2reg_idx rvcRegIdxSpec
    exact congrArg regidx.Regidx hbits
  have hnz : creg2reg_idx (.Cregidx i) ≠ zreg := by
    intro h
    have hz : (regidx_bits (creg2reg_idx (.Cregidx i))).toNat = (regidx_bits zreg).toNat :=
      congrArg (fun r => (regidx_bits r).toNat) h
    have hz0 : (regidx_bits zreg).toNat = 0 := by decide
    omega
  exact ⟨hbits, hreg, hlo, hhi, hnz⟩

/-- Exact upstream Sail RVC no-op / illegal functional cores (`LeanRV64D/InstsEnd.lean`,
    lines 71546–71555, 71627–71628). -/
def sailCNopExec (_imm : BitVec 6) : ExecutionResult :=
  .Retire_Success ()

def sailCNtlExec (_ntl : ntl_type) : ExecutionResult :=
  .Retire_Success ()

def sailCIllegalExec (_s : BitVec 16) : ExecutionResult :=
  .Illegal_Instruction ()

/-- RVC `C.NOP`, `C.NTL`, and `C.ILLEGAL` dispatch bisimulation: `C.NOP` and `C.NTL` retire
    directly as `.Retire_Success ()` without architectural side effects, while `C.ILLEGAL`
    always produces `.Illegal_Instruction ()`. -/
theorem rvcNopIllegal_bisim_sail (imm : BitVec 6) (ntl : ntl_type) (enc : BitVec 16) :
    sailCNopExec imm = .Retire_Success () ∧
      sailCNtlExec ntl = .Retire_Success () ∧
      sailCIllegalExec enc = .Illegal_Instruction () := by
  exact ⟨rfl, rfl, rfl⟩

/-- Exact upstream Sail RVC stack-pointer & immediate `ExecuteAs` expansions
    (`LeanRV64D/InstsEnd.lean`, lines 71579–71586, 71696–71707). -/
def sailCAddi4spnExec (rdc : cregidx) (nzimm : BitVec 8) : ExecutionResult :=
  let imm : BitVec 12 := (0b00#2 +++ (nzimm +++ 0b00#2))
  let rd := creg2reg_idx rdc
  .ExecuteAs (.ITYPE (imm, sp, rd, .ADDI))

def sailCAddi16spExec (imm : BitVec 6) : ExecutionResult :=
  let imm : BitVec 12 := sign_extend (m := 12) (imm +++ 0x0#4)
  .ExecuteAs (.ITYPE (imm, sp, sp, .ADDI))

def sailCLiExec (imm : BitVec 6) (rd : regidx) : ExecutionResult :=
  let imm : BitVec 12 := sign_extend (m := 12) imm
  .ExecuteAs (.ITYPE (imm, zreg, rd, .ADDI))

def sailCLuiExec (imm : BitVec 6) (rd : regidx) : ExecutionResult :=
  let res : BitVec 20 := sign_extend (m := 20) imm
  .ExecuteAs (.UTYPE (res, rd, .LUI))

/-- RVC `C.ADDI4SPN` and `C.ADDI16SP` stack-pointer arithmetic bisimulation: proves `C.ADDI4SPN`
    expands to `ADDI rd', sp, zext(nzimm) * 4` (4-byte aligned non-negative offset) and
    `C.ADDI16SP` expands to `ADDI sp, sp, sext(imm) * 16` (16-byte aligned signed offset). -/
theorem rvcStackPointerAddi_bisim_sail (i : BitVec 3) (nzimm : BitVec 8)
    (imm6 : BitVec 6) (sp_val : BitVec 64) :
    sailCAddi4spnExec (.Cregidx i) nzimm =
      .ExecuteAs (.ITYPE ((nzimm.zeroExtend 12) <<< 2, sp, rvcRegIdxSpec i, .ADDI)) ∧
    sailItypeCore .ADDI sp_val (0b00#2 +++ (nzimm +++ 0b00#2)) =
      sp_val + ((nzimm.zeroExtend 64) <<< 2) ∧
    sailCAddi16spExec imm6 =
      .ExecuteAs (.ITYPE ((imm6.signExtend 12) <<< 4, sp, sp, .ADDI)) ∧
    sailItypeCore .ADDI sp_val (sign_extend (m := 12) (imm6 +++ 0x0#4)) =
      sp_val + ((imm6.signExtend 64) <<< 4) := by
  have himm4 : (0b00#2 +++ (nzimm +++ 0b00#2) : BitVec 12) = (nzimm.zeroExtend 12) <<< 2 := by
    revert nzimm; decide
  have himm4_64 : sign_extend (m := 64) (0b00#2 +++ (nzimm +++ 0b00#2) : BitVec 12) =
      (nzimm.zeroExtend 64) <<< 2 := by
    revert nzimm; decide
  have himm16 : sign_extend (m := 12) (imm6 +++ 0x0#4) = (imm6.signExtend 12) <<< 4 := by
    revert imm6; decide
  have himm16_64 : sign_extend (m := 64) (sign_extend (m := 12) (imm6 +++ 0x0#4)) =
      (imm6.signExtend 64) <<< 4 := by
    revert imm6; decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [sailCAddi4spnExec, himm4, (rvcRegIdx_creg2reg_idx_bisim i).2.1]
  · dsimp only [sailItypeCore]
    rw [himm4_64]
  · simp [sailCAddi16spExec, himm16]
  · dsimp only [sailItypeCore]
    rw [himm16_64]

/-- RVC `C.LI` and `C.LUI` immediate generation bisimulation: proves `C.LI` expands to
    `ADDI rd, x0, sext(imm6)` yielding `imm6.signExtend 64`, and `C.LUI` expands to
    `LUI rd, sext20(imm6)` yielding `(imm6.signExtend 64) <<< 12`. -/
theorem rvcLiLui_bisim_sail (imm6 : BitVec 6) (rd : regidx) :
    sailCLiExec imm6 rd = .ExecuteAs (.ITYPE (imm6.signExtend 12, zreg, rd, .ADDI)) ∧
    sailItypeCore .ADDI 0#64 (sign_extend (m := 12) imm6) = imm6.signExtend 64 ∧
    sailCLuiExec imm6 rd = .ExecuteAs (.UTYPE (imm6.signExtend 20, rd, .LUI)) ∧
    rv64iUtypeSpec .LUI 0#64 (sign_extend (m := 20) imm6) = (imm6.signExtend 64) <<< 12 := by
  have hli12 : sign_extend (m := 12) imm6 = imm6.signExtend 12 := rfl
  have hli64 : sign_extend (m := 64) (sign_extend (m := 12) imm6) = imm6.signExtend 64 := by
    revert imm6; decide
  have hlui20 : sign_extend (m := 20) imm6 = imm6.signExtend 20 := rfl
  have hlui64 : rv64iUtypeSpec .LUI 0#64 (sign_extend (m := 20) imm6) = (imm6.signExtend 64) <<< 12 := by
    revert imm6; decide
  refine ⟨by simp [sailCLiExec, hli12], ?_, by simp [sailCLuiExec, hlui20], hlui64⟩
  dsimp only [sailItypeCore]
  rw [hli64]
  simp

/-- Exact upstream Sail RVC immediate/shift ALU `ExecuteAs` expansions
    (`LeanRV64D/InstsEnd.lean`, lines 71500–71510, 71679–71681, 71693–71694, 71705–71707). -/
def sailCAddiExec (imm : BitVec 6) (rsd : regidx) : ExecutionResult :=
  let imm : BitVec 12 := sign_extend (m := 12) imm
  .ExecuteAs (.ITYPE (imm, rsd, rsd, .ADDI))

def sailCAddiwExec (imm : BitVec 6) (rsd : regidx) : ExecutionResult :=
  .ExecuteAs (.ADDIW (sign_extend (m := 12) imm, rsd, rsd))

def sailCAndiExec (imm : BitVec 6) (rsd : cregidx) : ExecutionResult :=
  let rsd := creg2reg_idx rsd
  .ExecuteAs (.ITYPE (sign_extend (m := 12) imm, rsd, rsd, .ANDI))

def sailCSlliExec (shamt : BitVec 6) (rsd : regidx) : ExecutionResult :=
  .ExecuteAs (.SHIFTIOP (shamt, rsd, rsd, .SLLI))

def sailCSrliExec (shamt : BitVec 6) (rsd : cregidx) : ExecutionResult :=
  let rsd := creg2reg_idx rsd
  .ExecuteAs (.SHIFTIOP (shamt, rsd, rsd, .SRLI))

def sailCSraiExec (shamt : BitVec 6) (rsd : cregidx) : ExecutionResult :=
  let rsd := creg2reg_idx rsd
  .ExecuteAs (.SHIFTIOP (shamt, rsd, rsd, .SRAI))

/-- RVC `C.ADDI`, `C.ADDIW`, `C.ANDI`, `C.SLLI`, `C.SRLI`, and `C.SRAI` canonical expansion and
    value bisimulation against RV64I `ITYPE` / `ADDIW` / `SHIFTIOP` specifications. -/
theorem rvcAluImmShift_bisim_sail (imm6 shamt6 : BitVec 6) (rsd : regidx) (i : BitVec 3)
    (rsd_val : BitVec 64) :
    sailCAddiExec imm6 rsd = .ExecuteAs (.ITYPE (imm6.signExtend 12, rsd, rsd, .ADDI)) ∧
    sailItypeCore .ADDI rsd_val (sign_extend (m := 12) imm6) = rsd_val + imm6.signExtend 64 ∧
    sailCAddiwExec imm6 rsd = .ExecuteAs (.ADDIW (imm6.signExtend 12, rsd, rsd)) ∧
    sailAddiwCore rsd_val (sign_extend (m := 12) imm6) =
      (rsd_val.truncate 32 + imm6.signExtend 32).signExtend 64 ∧
    sailCAndiExec imm6 (.Cregidx i) =
      .ExecuteAs (.ITYPE (imm6.signExtend 12, rvcRegIdxSpec i, rvcRegIdxSpec i, .ANDI)) ∧
    sailItypeCore .ANDI rsd_val (sign_extend (m := 12) imm6) = rsd_val &&& imm6.signExtend 64 ∧
    sailCSlliExec shamt6 rsd = .ExecuteAs (.SHIFTIOP (shamt6, rsd, rsd, .SLLI)) ∧
    sailCSrliExec shamt6 (.Cregidx i) =
      .ExecuteAs (.SHIFTIOP (shamt6, rvcRegIdxSpec i, rvcRegIdxSpec i, .SRLI)) ∧
    sailCSraiExec shamt6 (.Cregidx i) =
      .ExecuteAs (.SHIFTIOP (shamt6, rvcRegIdxSpec i, rvcRegIdxSpec i, .SRAI)) := by
  have hc := (rvcRegIdx_creg2reg_idx_bisim i).2.1
  have sext64 : sign_extend (m := 64) (sign_extend (m := 12) imm6) = imm6.signExtend 64 := by
    revert imm6; decide
  have sext32 : (imm6.signExtend 12).signExtend 32 = imm6.signExtend 32 := by
    revert imm6; decide
  refine ⟨rfl, ?_, rfl, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · dsimp only [sailItypeCore]
    rw [sext64]
  · change sailAddiwCore rsd_val (imm6.signExtend 12) = _
    rw [← rv64iAddiwSpec_bisim_sail rsd_val (imm6.signExtend 12)]
    dsimp only [rv64iAddiwSpec]
    rw [sext32]
  · simp [sailCAndiExec, sign_extend, Sail.BitVec.signExtend, hc]
  · dsimp only [sailItypeCore]
    rw [sext64]
  · simp [sailCSrliExec, hc]
  · simp [sailCSraiExec, hc]

/-- Exact upstream Sail RVC register-register ALU `ExecuteAs` expansions
    (`LeanRV64D/InstsEnd.lean`, lines 71469–71472, 71484–71492, 71541–71544, 71557–71558,
    71683–71691, 71709–71710). -/
def sailCMvExec (rd rs2 : regidx) : ExecutionResult :=
  .ExecuteAs (.RTYPE (rs2, zreg, rd, .ADD))

def sailCAddExec (rsd rs2 : regidx) : ExecutionResult :=
  .ExecuteAs (.RTYPE (rs2, rsd, rsd, .ADD))

def sailCSubExec (rsd rs2 : cregidx) : ExecutionResult :=
  .ExecuteAs (.RTYPE (creg2reg_idx rs2, creg2reg_idx rsd, creg2reg_idx rsd, .SUB))

def sailCXorExec (rsd rs2 : cregidx) : ExecutionResult :=
  .ExecuteAs (.RTYPE (creg2reg_idx rs2, creg2reg_idx rsd, creg2reg_idx rsd, .XOR))

def sailCOrExec (rsd rs2 : cregidx) : ExecutionResult :=
  .ExecuteAs (.RTYPE (creg2reg_idx rs2, creg2reg_idx rsd, creg2reg_idx rsd, .OR))

def sailCAndExec (rsd rs2 : cregidx) : ExecutionResult :=
  .ExecuteAs (.RTYPE (creg2reg_idx rs2, creg2reg_idx rsd, creg2reg_idx rsd, .AND))

def sailCAddwExec (rsd rs2 : cregidx) : ExecutionResult :=
  .ExecuteAs (.RTYPEW (creg2reg_idx rs2, creg2reg_idx rsd, creg2reg_idx rsd, .ADDW))

def sailCSubwExec (rsd rs2 : cregidx) : ExecutionResult :=
  .ExecuteAs (.RTYPEW (creg2reg_idx rs2, creg2reg_idx rsd, creg2reg_idx rsd, .SUBW))

/-- RVC register-register ALU (`C.MV`, `C.ADD`, `C.SUB`, `C.XOR`, `C.OR`, `C.AND`, `C.ADDW`, `C.SUBW`)
    canonical expansion and value bisimulation against RV64I `RTYPE` and `RTYPEW`. -/
theorem rvcAluReg_bisim_sail (rd rs2 : regidx) (i1 i2 : BitVec 3) (v1 v2 : BitVec 64) :
    sailCMvExec rd rs2 = .ExecuteAs (.RTYPE (rs2, zreg, rd, .ADD)) ∧
    sailRtypeCore .ADD 0#64 v2 = v2 ∧
    sailCAddExec rd rs2 = .ExecuteAs (.RTYPE (rs2, rd, rd, .ADD)) ∧
    sailRtypeCore .ADD v1 v2 = v1 + v2 ∧
    sailCSubExec (.Cregidx i1) (.Cregidx i2) =
      .ExecuteAs (.RTYPE (rvcRegIdxSpec i2, rvcRegIdxSpec i1, rvcRegIdxSpec i1, .SUB)) ∧
    sailCXorExec (.Cregidx i1) (.Cregidx i2) =
      .ExecuteAs (.RTYPE (rvcRegIdxSpec i2, rvcRegIdxSpec i1, rvcRegIdxSpec i1, .XOR)) ∧
    sailCOrExec (.Cregidx i1) (.Cregidx i2) =
      .ExecuteAs (.RTYPE (rvcRegIdxSpec i2, rvcRegIdxSpec i1, rvcRegIdxSpec i1, .OR)) ∧
    sailCAndExec (.Cregidx i1) (.Cregidx i2) =
      .ExecuteAs (.RTYPE (rvcRegIdxSpec i2, rvcRegIdxSpec i1, rvcRegIdxSpec i1, .AND)) ∧
    sailCAddwExec (.Cregidx i1) (.Cregidx i2) =
      .ExecuteAs (.RTYPEW (rvcRegIdxSpec i2, rvcRegIdxSpec i1, rvcRegIdxSpec i1, .ADDW)) ∧
    sailCSubwExec (.Cregidx i1) (.Cregidx i2) =
      .ExecuteAs (.RTYPEW (rvcRegIdxSpec i2, rvcRegIdxSpec i1, rvcRegIdxSpec i1, .SUBW)) := by
  have hc1 := (rvcRegIdx_creg2reg_idx_bisim i1).2.1
  have hc2 := (rvcRegIdx_creg2reg_idx_bisim i2).2.1
  refine ⟨rfl, by simp [sailRtypeCore], rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [sailCSubExec, sailCXorExec, sailCOrExec, sailCAndExec, sailCAddwExec, sailCSubwExec, hc1, hc2]

/-- Exact upstream Sail RVC compressed load `ExecuteAs` expansions (`LeanRV64D/InstsEnd.lean`,
    lines 71569–71577, 71587–71613), covering `C.LWSP`, `C.LDSP`, `C.LW`, `C.LD`, `C.LBU`, `C.LH`, `C.LHU`. -/
def sailCLwspExec (uimm : BitVec 6) (rd : regidx) : ExecutionResult :=
  .ExecuteAs (.LOAD (zero_extend (m := 12) (uimm +++ 0b00#2), sp, rd, false, 4))

def sailCLdspExec (uimm : BitVec 6) (rd : regidx) : ExecutionResult :=
  .ExecuteAs (.LOAD (zero_extend (m := 12) (uimm +++ 0b000#3), sp, rd, false, 8))

def sailCLwExec (uimm : BitVec 5) (rsc rdc : cregidx) : ExecutionResult :=
  .ExecuteAs (.LOAD (zero_extend (m := 12) (uimm +++ 0b00#2), creg2reg_idx rsc, creg2reg_idx rdc, false, 4))

def sailCLdExec (uimm : BitVec 5) (rsc rdc : cregidx) : ExecutionResult :=
  .ExecuteAs (.LOAD (zero_extend (m := 12) (uimm +++ 0b000#3), creg2reg_idx rsc, creg2reg_idx rdc, false, 8))

def sailCLbuExec (uimm : BitVec 2) (rdc rsc1 : cregidx) : ExecutionResult :=
  .ExecuteAs (.LOAD (zero_extend (m := 12) uimm, creg2reg_idx rsc1, creg2reg_idx rdc, true, 1))

def sailCLhExec (uimm : BitVec 2) (rdc rsc1 : cregidx) : ExecutionResult :=
  .ExecuteAs (.LOAD (zero_extend (m := 12) uimm, creg2reg_idx rsc1, creg2reg_idx rdc, false, 2))

def sailCLhuExec (uimm : BitVec 2) (rdc rsc1 : cregidx) : ExecutionResult :=
  .ExecuteAs (.LOAD (zero_extend (m := 12) uimm, creg2reg_idx rsc1, creg2reg_idx rdc, true, 2))

/-- RVC compressed load (`C.LWSP`, `C.LDSP`, `C.LW`, `C.LD`, `C.LBU`, `C.LH`, `C.LHU`) canonical
    expansion and scaled non-negative effective-address bisimulation (`base + zext(uimm) * scale`). -/
theorem rvcLoad_bisim_sail (uimm6 : BitVec 6) (uimm5 : BitVec 5) (uimm2 : BitVec 2)
    (rd : regidx) (ic1 ic2 : BitVec 3) (base : BitVec 64) :
    sailCLwspExec uimm6 rd =
      .ExecuteAs (.LOAD ((uimm6.zeroExtend 12) <<< 2, sp, rd, false, 4)) ∧
    rv64iEffectiveAddrSpec base (zero_extend (m := 12) (uimm6 +++ 0b00#2)) =
      base + ((uimm6.zeroExtend 64) <<< 2) ∧
    sailCLdspExec uimm6 rd =
      .ExecuteAs (.LOAD ((uimm6.zeroExtend 12) <<< 3, sp, rd, false, 8)) ∧
    rv64iEffectiveAddrSpec base (zero_extend (m := 12) (uimm6 +++ 0b000#3)) =
      base + ((uimm6.zeroExtend 64) <<< 3) ∧
    sailCLwExec uimm5 (.Cregidx ic1) (.Cregidx ic2) =
      .ExecuteAs (.LOAD ((uimm5.zeroExtend 12) <<< 2, rvcRegIdxSpec ic1, rvcRegIdxSpec ic2, false, 4)) ∧
    sailCLdExec uimm5 (.Cregidx ic1) (.Cregidx ic2) =
      .ExecuteAs (.LOAD ((uimm5.zeroExtend 12) <<< 3, rvcRegIdxSpec ic1, rvcRegIdxSpec ic2, false, 8)) ∧
    sailCLbuExec uimm2 (.Cregidx ic2) (.Cregidx ic1) =
      .ExecuteAs (.LOAD (uimm2.zeroExtend 12, rvcRegIdxSpec ic1, rvcRegIdxSpec ic2, true, 1)) ∧
    sailCLhExec uimm2 (.Cregidx ic2) (.Cregidx ic1) =
      .ExecuteAs (.LOAD (uimm2.zeroExtend 12, rvcRegIdxSpec ic1, rvcRegIdxSpec ic2, false, 2)) ∧
    sailCLhuExec uimm2 (.Cregidx ic2) (.Cregidx ic1) =
      .ExecuteAs (.LOAD (uimm2.zeroExtend 12, rvcRegIdxSpec ic1, rvcRegIdxSpec ic2, true, 2)) := by
  have hc1 := (rvcRegIdx_creg2reg_idx_bisim ic1).2.1
  have hc2 := (rvcRegIdx_creg2reg_idx_bisim ic2).2.1
  have hw6 : zero_extend (m := 12) (uimm6 +++ 0b00#2) = (uimm6.zeroExtend 12) <<< 2 := by
    revert uimm6; decide
  have hw6_64 : (zero_extend (m := 12) (uimm6 +++ 0b00#2)).signExtend 64 = (uimm6.zeroExtend 64) <<< 2 := by
    revert uimm6; decide
  have hd6 : zero_extend (m := 12) (uimm6 +++ 0b000#3) = (uimm6.zeroExtend 12) <<< 3 := by
    revert uimm6; decide
  have hd6_64 : (zero_extend (m := 12) (uimm6 +++ 0b000#3)).signExtend 64 = (uimm6.zeroExtend 64) <<< 3 := by
    revert uimm6; decide
  have hw5 : zero_extend (m := 12) (uimm5 +++ 0b00#2) = (uimm5.zeroExtend 12) <<< 2 := by
    revert uimm5; decide
  have hd5 : zero_extend (m := 12) (uimm5 +++ 0b000#3) = (uimm5.zeroExtend 12) <<< 3 := by
    revert uimm5; decide
  have hb2 : zero_extend (m := 12) uimm2 = uimm2.zeroExtend 12 := rfl
  refine ⟨by simp [sailCLwspExec, hw6], ?_, by simp [sailCLdspExec, hd6], ?_,
    by simp [sailCLwExec, hw5, hc1, hc2], by simp [sailCLdExec, hd5, hc1, hc2],
    by simp [sailCLbuExec, hb2, hc1, hc2], by simp [sailCLhExec, hb2, hc1, hc2],
    by simp [sailCLhuExec, hb2, hc1, hc2]⟩
  · simp [rv64iEffectiveAddrSpec, hw6_64]
  · simp [rv64iEffectiveAddrSpec, hd6_64]

/-- Exact upstream Sail RVC compressed store `ExecuteAs` expansions (`LeanRV64D/InstsEnd.lean`,
    lines 71474–71482, 71511–71515, 71525–71539), covering `C.SWSP`, `C.SDSP`, `C.SW`, `C.SD`, `C.SB`, `C.SH`. -/
def sailCSwspExec (uimm : BitVec 6) (rs2 : regidx) : ExecutionResult :=
  .ExecuteAs (.STORE (zero_extend (m := 12) (uimm +++ 0b00#2), rs2, sp, 4))

def sailCSdspExec (uimm : BitVec 6) (rs2 : regidx) : ExecutionResult :=
  .ExecuteAs (.STORE (zero_extend (m := 12) (uimm +++ 0b000#3), rs2, sp, 8))

def sailCSwExec (uimm : BitVec 5) (rsc1 rsc2 : cregidx) : ExecutionResult :=
  .ExecuteAs (.STORE (zero_extend (m := 12) (uimm +++ 0b00#2), creg2reg_idx rsc2, creg2reg_idx rsc1, 4))

def sailCSdExec (uimm : BitVec 5) (rsc1 rsc2 : cregidx) : ExecutionResult :=
  .ExecuteAs (.STORE (zero_extend (m := 12) (uimm +++ 0b000#3), creg2reg_idx rsc2, creg2reg_idx rsc1, 8))

def sailCSbExec (uimm : BitVec 2) (rsc1 rsc2 : cregidx) : ExecutionResult :=
  .ExecuteAs (.STORE (zero_extend (m := 12) uimm, creg2reg_idx rsc2, creg2reg_idx rsc1, 1))

def sailCShExec (uimm : BitVec 2) (rsc1 rsc2 : cregidx) : ExecutionResult :=
  .ExecuteAs (.STORE (zero_extend (m := 12) uimm, creg2reg_idx rsc2, creg2reg_idx rsc1, 2))

/-- RVC compressed store (`C.SWSP`, `C.SDSP`, `C.SW`, `C.SD`, `C.SB`, `C.SH`) canonical expansion
    and scaled effective-address bisimulation. -/
theorem rvcStore_bisim_sail (uimm6 : BitVec 6) (uimm5 : BitVec 5) (uimm2 : BitVec 2)
    (rs2 : regidx) (ic1 ic2 : BitVec 3) (base : BitVec 64) :
    sailCSwspExec uimm6 rs2 =
      .ExecuteAs (.STORE ((uimm6.zeroExtend 12) <<< 2, rs2, sp, 4)) ∧
    sailCSdspExec uimm6 rs2 =
      .ExecuteAs (.STORE ((uimm6.zeroExtend 12) <<< 3, rs2, sp, 8)) ∧
    sailCSwExec uimm5 (.Cregidx ic1) (.Cregidx ic2) =
      .ExecuteAs (.STORE ((uimm5.zeroExtend 12) <<< 2, rvcRegIdxSpec ic2, rvcRegIdxSpec ic1, 4)) ∧
    rv64iEffectiveAddrSpec base (zero_extend (m := 12) (uimm5 +++ 0b00#2)) =
      base + ((uimm5.zeroExtend 64) <<< 2) ∧
    sailCSdExec uimm5 (.Cregidx ic1) (.Cregidx ic2) =
      .ExecuteAs (.STORE ((uimm5.zeroExtend 12) <<< 3, rvcRegIdxSpec ic2, rvcRegIdxSpec ic1, 8)) ∧
    rv64iEffectiveAddrSpec base (zero_extend (m := 12) (uimm5 +++ 0b000#3)) =
      base + ((uimm5.zeroExtend 64) <<< 3) ∧
    sailCSbExec uimm2 (.Cregidx ic1) (.Cregidx ic2) =
      .ExecuteAs (.STORE (uimm2.zeroExtend 12, rvcRegIdxSpec ic2, rvcRegIdxSpec ic1, 1)) ∧
    sailCShExec uimm2 (.Cregidx ic1) (.Cregidx ic2) =
      .ExecuteAs (.STORE (uimm2.zeroExtend 12, rvcRegIdxSpec ic2, rvcRegIdxSpec ic1, 2)) := by
  have hc1 := (rvcRegIdx_creg2reg_idx_bisim ic1).2.1
  have hc2 := (rvcRegIdx_creg2reg_idx_bisim ic2).2.1
  have hw6 : zero_extend (m := 12) (uimm6 +++ 0b00#2) = (uimm6.zeroExtend 12) <<< 2 := by
    revert uimm6; decide
  have hd6 : zero_extend (m := 12) (uimm6 +++ 0b000#3) = (uimm6.zeroExtend 12) <<< 3 := by
    revert uimm6; decide
  have hw5 : zero_extend (m := 12) (uimm5 +++ 0b00#2) = (uimm5.zeroExtend 12) <<< 2 := by
    revert uimm5; decide
  have hw5_64 : (zero_extend (m := 12) (uimm5 +++ 0b00#2)).signExtend 64 = (uimm5.zeroExtend 64) <<< 2 := by
    revert uimm5; decide
  have hd5 : zero_extend (m := 12) (uimm5 +++ 0b000#3) = (uimm5.zeroExtend 12) <<< 3 := by
    revert uimm5; decide
  have hd5_64 : (zero_extend (m := 12) (uimm5 +++ 0b000#3)).signExtend 64 = (uimm5.zeroExtend 64) <<< 3 := by
    revert uimm5; decide
  have hb2 : zero_extend (m := 12) uimm2 = uimm2.zeroExtend 12 := rfl
  refine ⟨by simp [sailCSwspExec, hw6], by simp [sailCSdspExec, hd6],
    by simp [sailCSwExec, hw5, hc1, hc2], ?_, by simp [sailCSdExec, hd5, hc1, hc2], ?_,
    by simp [sailCSbExec, hb2, hc1, hc2], by simp [sailCShExec, hb2, hc1, hc2]⟩
  · simp [rv64iEffectiveAddrSpec, hw5_64]
  · simp [rv64iEffectiveAddrSpec, hd5_64]

/-- Exact upstream Sail RVC branch & jump `ExecuteAs` expansions (`LeanRV64D/InstsEnd.lean`,
    lines 71615–71625, 71673–71677), covering `C.BEQZ`, `C.BNEZ`, `C.J`, `C.JAL`, `C.JR`, `C.JALR`. -/
def sailCBeqzExec (imm : BitVec 8) (rs : cregidx) : ExecutionResult :=
  .ExecuteAs (.BTYPE (sign_extend (m := 13) (imm +++ 0#1), zreg, creg2reg_idx rs, .BEQ))

def sailCBnezExec (imm : BitVec 8) (rs : cregidx) : ExecutionResult :=
  .ExecuteAs (.BTYPE (sign_extend (m := 13) (imm +++ 0#1), zreg, creg2reg_idx rs, .BNE))

def sailCJExec (imm : BitVec 11) : ExecutionResult :=
  .ExecuteAs (.JAL (sign_extend (m := 21) (imm +++ 0#1), zreg))

def sailCJalExec (imm : BitVec 11) : ExecutionResult :=
  .ExecuteAs (.JAL (sign_extend (m := 21) (imm +++ 0#1), ra))

def sailCJrExec (rs1 : regidx) : ExecutionResult :=
  .ExecuteAs (.JALR (zeros (n := 12), rs1, zreg))

def sailCJalrExec (rs1 : regidx) : ExecutionResult :=
  .ExecuteAs (.JALR (zeros (n := 12), rs1, ra))

/-- Pure `TurboLean`-side RVC compressed branch (`C.BEQZ` / `C.BNEZ`) next-PC specification:
    compressed instructions have 2-byte fallthrough `pc + 2#64`, and branch to
    `pc + ((imm8.signExtend 64) <<< 1)` when `rs_val == 0#64` (`C.BEQZ`) or `rs_val != 0#64` (`C.BNEZ`). -/
def rvcBranchNextPcSpec (is_bnez : Bool) (pc rs_val : BitVec 64) (imm8 : BitVec 8) : BitVec 64 :=
  let taken := if is_bnez then rs_val != 0#64 else rs_val == 0#64
  if taken then pc + ((imm8.signExtend 64) <<< 1) else pc + 2#64

/-- RVC compressed branch (`C.BEQZ` / `C.BNEZ`) canonical expansion and 2-byte fallthrough
    next-PC bisimulation: proves `C.BEQZ`/`C.BNEZ` expand to `BEQ`/`BNE` against `zreg` (`0#64`)
    with 2-byte-aligned target offset `(imm8.signExtend 64) <<< 1` and untaken fallthrough `pc + 2#64`. -/
theorem rvcBranch_bisim_sail (imm8 : BitVec 8) (ic : BitVec 3) (pc rs_val : BitVec 64) :
    sailCBeqzExec imm8 (.Cregidx ic) =
      .ExecuteAs (.BTYPE ((imm8.signExtend 13) <<< 1, zreg, rvcRegIdxSpec ic, .BEQ)) ∧
    sailCBnezExec imm8 (.Cregidx ic) =
      .ExecuteAs (.BTYPE ((imm8.signExtend 13) <<< 1, zreg, rvcRegIdxSpec ic, .BNE)) ∧
    (if sailBtypeTakenCore .BEQ rs_val 0#64
      then pc + sign_extend (m := 64) (sign_extend (m := 13) (imm8 +++ 0#1))
      else pc + 2#64) = rvcBranchNextPcSpec false pc rs_val imm8 ∧
    (if sailBtypeTakenCore .BNE rs_val 0#64
      then pc + sign_extend (m := 64) (sign_extend (m := 13) (imm8 +++ 0#1))
      else pc + 2#64) = rvcBranchNextPcSpec true pc rs_val imm8 := by
  have hc := (rvcRegIdx_creg2reg_idx_bisim ic).2.1
  have himm13 : sign_extend (m := 13) (imm8 +++ 0#1) = (imm8.signExtend 13) <<< 1 := by
    revert imm8; decide
  have himm64 : sign_extend (m := 64) (sign_extend (m := 13) (imm8 +++ 0#1)) =
      (imm8.signExtend 64) <<< 1 := by
    revert imm8; decide
  refine ⟨by simp [sailCBeqzExec, himm13, hc], by simp [sailCBnezExec, himm13, hc], ?_, ?_⟩
  · simp [rvcBranchNextPcSpec, sailBtypeTakenCore, himm64]
  · simp [rvcBranchNextPcSpec, sailBtypeTakenCore, himm64]

/-- RVC compressed jump (`C.J`, `C.JAL`, `C.JR`, `C.JALR`) canonical expansion bisimulation. -/
theorem rvcJumpExpand_bisim_sail (imm11 : BitVec 11) (rs1 : regidx) :
    sailCJExec imm11 = .ExecuteAs (.JAL ((imm11.signExtend 21) <<< 1, zreg)) ∧
    sailCJalExec imm11 = .ExecuteAs (.JAL ((imm11.signExtend 21) <<< 1, ra)) ∧
    sailCJrExec rs1 = .ExecuteAs (.JALR (0#12, rs1, zreg)) ∧
    sailCJalrExec rs1 = .ExecuteAs (.JALR (0#12, rs1, ra)) := by
  have himm21 : sign_extend (m := 21) (imm11 +++ 0#1) = (imm11.signExtend 21) <<< 1 := by
    revert imm11; decide
  exact ⟨by simp [sailCJExec, himm21], by simp [sailCJalExec, himm21], rfl, rfl⟩

/-- End-to-end `SailM` 2-byte compressed `C.JALR` (`rd = ra = x1`, `rs1 = x1`) state-transition
    bisimulation (`Step.lean` lines 369–373 + `execute_C_JALR` → `execute_JALR`):
    compressed fetch sets `nextPC := BitVec.addInt PC 2` (`pc + 2#64`), so `C.JALR x1` reads the
    pre-call `x1` value (`rs1_val`), clears target bit 0 (`rs1_val &&& ~~~1#64`), writes the 2-byte
    return link `pc + 2#64` into `x1`, and ticks `PC` to the aligned target. -/
theorem rvcJalr_x1_state_bisim_sail (pc rs1_val : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource) :
    ((do
        writeReg .PC pc
        wX_bits ra rs1_val
        writeReg .nextPC (BitVec.addInt (← readReg .PC) 2)
        let link_address ← get_next_pc ()
        let target := (← rX_bits ra) + sign_extend (m := 64) (zeros (n := 12))
        set_next_pc (Sail.BitVec.update target 0 0#1)
        wX_bits ra link_address
        tick_pc ()
        let link_out ← rX_bits ra
        let pc_out ← get_arch_pc ()
        pure (link_out, pc_out)).run s) =
      .ok (pc + 2#64, rs1_val &&& ~~~1#64)
        { s with regs := ((((((s.regs.insert .PC pc).insert .x1 rs1_val).insert .nextPC (pc + 2#64)).insert
            .nextPC (Sail.BitVec.update rs1_val 0 0#1)).insert
            .x1 (pc + 2#64)).insert
            .PC (Sail.BitVec.update rs1_val 0 0#1)) } := by
  have hadd2 : BitVec.addInt pc 2 = pc + 2#64 := by
    simp [BitVec.addInt]
  have hclr : Sail.BitVec.update rs1_val 0 0#1 = rs1_val &&& ~~~1#64 := by
    have h0 := (rv64iJalrSpec_bisim_sail pc rs1_val 0#12).1
    simpa [rv64iJalrSpec, sailJalrCore, sign_extend, Sail.BitVec.signExtend] using
      (congrArg Prod.snd h0).symm
  rw [← hclr]
  simp [ra, set_next_pc, get_next_pc, get_arch_pc, tick_pc,
    redirect_callback, pc_write_callback,
    wX_bits, rX_bits, wX, rX, regval_into_reg, regval_from_reg,
    xreg_write_callback, reg_name_forwards, encdec_reg_forwards_matches,
    encdec_reg_forwards, get_config_use_abi_names, LeanRV64D.Functions.not,
    reg_arch_name_raw_forwards, xreg_full_write_callback,
    zeros, sign_extend, Sail.BitVec.signExtend, zero_extend, Sail.BitVec.zeroExtend,
    Sail.BitVec.toNatInt, to_bits, get_slice_int,
    writeReg, PreSail.writeReg, readReg, PreSail.readReg,
    modify, modifyGet, MonadStateOf.modifyGet, get, getThe, MonadStateOf.get]
  dsimp [EStateM.modifyGet, EStateM.get, EStateM.pure, EStateM.map, EStateM.run, Functor.map]
  simp [hadd2, Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self,
    Pure.pure, estate_pure_def]

/-- Exact upstream Sail `Zcb` compressed bit/multiply instructions (`LeanRV64D/InstsEnd.lean`,
    lines 71456–71467, 71517–71523, 71549–71552, 71560–71567):
    - `C.ZEXT.B` and `C.NOT` execute directly in `SailM`
    - `C.SEXT.B`, `C.SEXT.H`, `C.ZEXT.H`, `C.ZEXT.W`, `C.MUL` expand via `ExecuteAs` -/
def sailCZextBExec (rsdc : cregidx) : SailM ExecutionResult := do
  let rsd := creg2reg_idx rsdc
  wX_bits rsd (zero_extend (m := 64) (Sail.BitVec.extractLsb (← rX_bits rsd) 7 0))
  pure (.Retire_Success ())

def sailCNotExec (rsdc : cregidx) : SailM ExecutionResult := do
  let r := creg2reg_idx rsdc
  wX_bits r (Complement.complement (← rX_bits r))
  pure (.Retire_Success ())

def sailCSextBExec (rsdc : cregidx) : ExecutionResult :=
  let rsd := creg2reg_idx rsdc
  .ExecuteAs (.ZBB_EXTOP (rsd, rsd, .SEXTB))

def sailCSextHExec (rsdc : cregidx) : ExecutionResult :=
  let rsd := creg2reg_idx rsdc
  .ExecuteAs (.ZBB_EXTOP (rsd, rsd, .SEXTH))

def sailCZextHExec (rsdc : cregidx) : ExecutionResult :=
  let rsd := creg2reg_idx rsdc
  .ExecuteAs (.ZBB_EXTOP (rsd, rsd, .ZEXTH))

def sailCZextWExec (rsdc : cregidx) : ExecutionResult :=
  let rsd := creg2reg_idx rsdc
  .ExecuteAs (.ZBA_RTYPEUW (zreg, rsd, rsd, 0b00#2))

def sailCMulExec (rsdc rsc2 : cregidx) : ExecutionResult :=
  let rd := creg2reg_idx rsdc
  let rs := creg2reg_idx rsc2
  .ExecuteAs (.MUL (rs, rd, rd, { result_part := .Low, signed_rs1 := .Signed, signed_rs2 := .Signed }))

/-- `Zcb` `ExecuteAs` extensions (`C.SEXT.B`, `C.SEXT.H`, `C.ZEXT.H`, `C.ZEXT.W`, `C.MUL`)
    canonical expansion and value bisimulation: proves `C.ZEXT.W` (`ADD.UW rsd, rsd, x0`) zero-extends
    the low 32 bits `(x.truncate 32).zeroExtend 64`, `C.SEXT.B`/`C.SEXT.H`/`C.ZEXT.H` match `ZBB_EXTOP`,
    and `C.MUL` matches 64-bit `x * y`. -/
theorem rvcZcbExpand_bisim_sail (ic1 ic2 : BitVec 3) (x : BitVec 64) :
    sailCSextBExec (.Cregidx ic1) =
      .ExecuteAs (.ZBB_EXTOP (rvcRegIdxSpec ic1, rvcRegIdxSpec ic1, .SEXTB)) ∧
    sailCSextHExec (.Cregidx ic1) =
      .ExecuteAs (.ZBB_EXTOP (rvcRegIdxSpec ic1, rvcRegIdxSpec ic1, .SEXTH)) ∧
    sailCZextHExec (.Cregidx ic1) =
      .ExecuteAs (.ZBB_EXTOP (rvcRegIdxSpec ic1, rvcRegIdxSpec ic1, .ZEXTH)) ∧
    sailCZextWExec (.Cregidx ic1) =
      .ExecuteAs (.ZBA_RTYPEUW (zreg, rvcRegIdxSpec ic1, rvcRegIdxSpec ic1, 0b00#2)) ∧
    sailZbaRtypeuwCore 0b00#2 x 0#64 = (x.truncate 32).zeroExtend 64 ∧
    sailCMulExec (.Cregidx ic1) (.Cregidx ic2) =
      .ExecuteAs (.MUL (rvcRegIdxSpec ic2, rvcRegIdxSpec ic1, rvcRegIdxSpec ic1,
        { result_part := .Low, signed_rs1 := .Signed, signed_rs2 := .Signed })) := by
  have hc1 := (rvcRegIdx_creg2reg_idx_bisim ic1).2.1
  have hc2 := (rvcRegIdx_creg2reg_idx_bisim ic2).2.1
  have hzextw : sailZbaRtypeuwCore 0b00#2 x 0#64 = (x.truncate 32).zeroExtend 64 := by
    rw [← (rv64Zba_bisim_sail 0b00#2 0#6 x 0#64).2.1]
    simp [rv64ZbaRtypeuwSpec]
  exact ⟨by simp [sailCSextBExec, hc1], by simp [sailCSextHExec, hc1],
    by simp [sailCZextHExec, hc1], by simp [sailCZextWExec, hc1],
    hzextw, by simp [sailCMulExec, hc1, hc2]⟩

/-- Direct `SailM` bisimulation for `Zcb` `execute_C_ZEXT_B` and `execute_C_NOT` (`cregidx = 0#3`,
    architectural register `x8` / `s0`): proves `C.ZEXT.B` masks to `(val.truncate 8).zeroExtend 64`
    (`val &&& 0xff#64`), `C.NOT` bitwise-inverts `~~~val`, and `C.NOT` is involutive in `SailM`. -/
theorem rvcZcbDirectSailM_x8_bisim (val : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hx8 : s.regs.get? .x8 = some val) :
    (sailCZextBExec (.Cregidx 0#3)).run s =
      .ok (.Retire_Success ())
        { s with regs := s.regs.insert .x8 ((val.truncate 8).zeroExtend 64) } ∧
    (val.truncate 8).zeroExtend 64 = val &&& 0xff#64 ∧
    (sailCNotExec (.Cregidx 0#3)).run s =
      .ok (.Retire_Success ())
        { s with regs := s.regs.insert .x8 (~~~val) } ∧
    ((do
        let _ ← sailCNotExec (.Cregidx 0#3)
        let _ ← sailCNotExec (.Cregidx 0#3)
        rX_bits (creg2reg_idx (.Cregidx 0#3))).run s) =
      .ok val { s with regs := (s.regs.insert .x8 (~~~val)).insert .x8 val } := by
  have hzext8 : zero_extend (m := 64) (Sail.BitVec.extractLsb val 7 0) =
      (val.truncate 8).zeroExtend 64 := by
    dsimp only [zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb,
      BitVec.extractLsb, BitVec.extractLsb', Nat.shiftRight_zero, BitVec.truncate_eq_setWidth]
    exact congrArg (BitVec.setWidth 64) (BitVec.setWidth_eq _).symm
  have hmask8 : (val.truncate 8).zeroExtend 64 = val &&& 0xff#64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have h255 : (0xff#64).getLsbD k = decide (k < 8) := by
      rw [BitVec.getLsbD_eq_getElem hk]
      revert k hk
      decide
    dsimp only [BitVec.zeroExtend_eq_setWidth, BitVec.truncate_eq_setWidth]
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_and, h255]
    by_cases h8 : k < 8 <;> simp [hk, h8]
  have hr8 : (rX_bits (creg2reg_idx (.Cregidx 0#3))).run s = .ok val s := by
    simp [creg2reg_idx, rX_bits, rX, regval_from_reg, zero_extend, Sail.BitVec.zeroExtend,
      Sail.BitVec.toNatInt, readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
    dsimp [EStateM.bind, EStateM.get, EStateM.pure, EStateM.run]
    rw [hx8]
    rfl
  have hw8 : ∀ (v : BitVec 64) (st : SequentialState RegisterType trivialChoiceSource),
      (wX_bits (creg2reg_idx (.Cregidx 0#3)) v).run st =
        .ok () { st with regs := st.regs.insert .x8 v } := by
    intro v st
    simp [creg2reg_idx, wX_bits, wX, regval_into_reg, xreg_write_callback, reg_name_forwards,
      encdec_reg_forwards_matches, encdec_reg_forwards, get_config_use_abi_names,
      LeanRV64D.Functions.not, reg_arch_name_raw_forwards,
      xreg_full_write_callback, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.toNatInt,
      to_bits, get_slice_int,
      writeReg, PreSail.writeReg, modify, modifyGet, MonadStateOf.modifyGet]
    rfl
  refine ⟨?_, hmask8, ?_, ?_⟩
  · unfold sailCZextBExec
    dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at hr8 hw8 ⊢
    rw [hr8]
    dsimp only
    rw [hzext8, hw8]
  · unfold sailCNotExec
    dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at hr8 hw8 ⊢
    rw [hr8]
    dsimp only
    change (match wX_bits (creg2reg_idx (.Cregidx 0#3)) (~~~val) s with
      | .ok _ s' => EStateM.Result.ok (ExecutionResult.Retire_Success ()) s'
      | .error e s' => EStateM.Result.error e s') = _
    rw [hw8]
  · have hn1 : (sailCNotExec (.Cregidx 0#3)).run s =
        .ok (.Retire_Success ()) { s with regs := s.regs.insert .x8 (~~~val) } := by
      unfold sailCNotExec
      dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at hr8 hw8 ⊢
      rw [hr8]
      dsimp only
      change (match wX_bits (creg2reg_idx (.Cregidx 0#3)) (~~~val) s with
        | .ok _ s' => EStateM.Result.ok (ExecutionResult.Retire_Success ()) s'
        | .error e s' => EStateM.Result.error e s') = _
      rw [hw8]
    let s1 : SequentialState RegisterType trivialChoiceSource :=
      { s with regs := s.regs.insert .x8 (~~~val) }
    have hr8_s1 : (rX_bits (creg2reg_idx (.Cregidx 0#3))).run s1 = .ok (~~~val) s1 := by
      simp [s1, creg2reg_idx, rX_bits, rX, regval_from_reg, zero_extend, Sail.BitVec.zeroExtend,
        Sail.BitVec.toNatInt, readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
      dsimp [EStateM.bind, EStateM.get, EStateM.pure, EStateM.run]
      simp [Std.ExtDHashMap.get?_insert_self]
      rfl
    have hn2 : (sailCNotExec (.Cregidx 0#3)).run s1 =
        .ok (.Retire_Success ()) { s1 with regs := s1.regs.insert .x8 val } := by
      unfold sailCNotExec
      dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at hr8_s1 hw8 ⊢
      rw [hr8_s1]
      dsimp only
      change (match wX_bits (creg2reg_idx (.Cregidx 0#3)) (~~~~~~val) s1 with
        | .ok _ s' => EStateM.Result.ok (ExecutionResult.Retire_Success ()) s'
        | .error e s' => EStateM.Result.error e s') = _
      rw [BitVec.not_not, hw8]
    let s2 : SequentialState RegisterType trivialChoiceSource :=
      { s1 with regs := s1.regs.insert .x8 val }
    have hr8_s2 : (rX_bits (creg2reg_idx (.Cregidx 0#3))).run s2 = .ok val s2 := by
      simp [s2, creg2reg_idx, rX_bits, rX, regval_from_reg, zero_extend, Sail.BitVec.zeroExtend,
        Sail.BitVec.toNatInt, readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
      dsimp [EStateM.bind, EStateM.get, EStateM.pure, EStateM.run]
      simp [Std.ExtDHashMap.get?_insert_self]
      rfl
    dsimp [Bind.bind, EStateM.bind, EStateM.run, s1, s2] at hn1 hn2 hr8_s2 ⊢
    rw [hn1]; dsimp only; rw [hn2]; dsimp only; exact hr8_s2

/-! ## 9. RV64A (`Zaamo` / `Zacas` / `Zalrsc`), `Zicsr` / Privileged, & `Sv39` / `Sv48` VMem Bisimulation (Stage 3E.6) -/

/-- Pure reference ALU core for `Zaamo` / `Zacas` (`AMOSWAP`, `AMOADD`, `AMOXOR`, `AMOAND`, `AMOOR`,
    `AMOMIN`, `AMOMAX`, `AMOMINU`, `AMOMAXU`, `AMOCAS`) over arbitrary bit-width `n`. -/
def rv64AmoAluSpec {n : Nat} (op : amoop) (rs2_val loaded : BitVec n) : BitVec n :=
  match op with
  | .AMOSWAP => rs2_val
  | .AMOADD => rs2_val + loaded
  | .AMOXOR => rs2_val ^^^ loaded
  | .AMOAND => rs2_val &&& loaded
  | .AMOOR => rs2_val ||| loaded
  | .AMOMIN => if BitVec.slt rs2_val loaded then rs2_val else loaded
  | .AMOMAX => if BitVec.slt loaded rs2_val then rs2_val else loaded
  | .AMOMINU => if BitVec.ult rs2_val loaded then rs2_val else loaded
  | .AMOMAXU => if BitVec.ult loaded rs2_val then rs2_val else loaded
  | .AMOCAS => rs2_val

/-- Exact mirror of the ALU computation in upstream `LeanRV64D.Functions.execute_AMO`
    (`InstsEnd.lean`, lines 71839–71862, SHA-256 pinned in `scripts/check_sail_riscv_bridge_sync.py`). -/
def sailAmoAluCore {width : Nat} (op : amoop) (rs2_val loaded : BitVec (width * 8)) :
    BitVec (width * 8) :=
  match op with
  | .AMOSWAP => rs2_val
  | .AMOADD => rs2_val + loaded
  | .AMOXOR => rs2_val ^^^ loaded
  | .AMOAND => rs2_val &&& loaded
  | .AMOOR => rs2_val ||| loaded
  | .AMOMIN => if zopz0zI_s rs2_val loaded then rs2_val else loaded
  | .AMOMAX => if zopz0zK_s rs2_val loaded then rs2_val else loaded
  | .AMOMINU => if zopz0zI_u rs2_val loaded then rs2_val else loaded
  | .AMOMAXU => if zopz0zK_u rs2_val loaded then rs2_val else loaded
  | .AMOCAS => rs2_val

/-- `Zaamo` / `Zacas` opcode encoding (`encdec_amoop_forwards` / `encdec_amoop_backwards` /
    `encdec_amoop_backwards_matches`) and memory-access classification (`is_amo_access`,
    `is_load_store`, `is_store_conditional`) bisimulation in `SailM`. -/
theorem rv64ZaamoEncdec_bisim_sail (op : amoop) (aq rl : Bool)
    (s : SequentialState RegisterType trivialChoiceSource) :
    encdec_amoop_forwards_matches op = true ∧
    encdec_amoop_backwards_matches (encdec_amoop_forwards op) = true ∧
    (encdec_amoop_backwards (encdec_amoop_forwards op)).run s = .ok op s ∧
    is_amo_access (.Atomic (op, aq, rl, .Data, .Data)) = true ∧
    is_load_store (.Atomic (op, aq, rl, mem_payload.Data, mem_payload.Data)) = true ∧
    is_store_conditional (.Atomic (op, aq, rl, mem_payload.Data, mem_payload.Data)) = false := by
  cases op <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `Zaamo` / `Zacas` ALU value bisimulation against upstream `execute_AMO`: proves exact bit-level
    agreement across all 10 `amoop` variants (`width = 1, 2, 4, 8, 16`, i.e., `.B`/`.H`/`.W`/`.D`/`.Q`)
    and commutativity of `AMOADD`/`AMOXOR`/`AMOAND`/`AMOOR`. -/
theorem rv64ZaamoAlu_bisim_sail {width : Nat} (op : amoop)
    (rs2_val loaded : BitVec (width * 8)) :
    sailAmoAluCore op rs2_val loaded = rv64AmoAluSpec op rs2_val loaded ∧
    sailAmoAluCore .AMOADD rs2_val loaded = sailAmoAluCore .AMOADD loaded rs2_val ∧
    sailAmoAluCore .AMOXOR rs2_val loaded = sailAmoAluCore .AMOXOR loaded rs2_val ∧
    sailAmoAluCore .AMOAND rs2_val loaded = sailAmoAluCore .AMOAND loaded rs2_val ∧
    sailAmoAluCore .AMOOR rs2_val loaded = sailAmoAluCore .AMOOR loaded rs2_val := by
  have hslt : ∀ a b : BitVec (width * 8), zopz0zI_s a b = BitVec.slt a b := by
    intro a b
    rfl
  have hsgt : ∀ a b : BitVec (width * 8), zopz0zK_s a b = BitVec.slt b a := by
    intro a b
    unfold zopz0zK_s BitVec.slt
    rfl
  have hult : ∀ a b : BitVec (width * 8), zopz0zI_u a b = BitVec.ult a b := by
    intro a b
    unfold zopz0zI_u Sail.BitVec.toNatInt BitVec.ult
    change decide ((a.toNat : Int) < (b.toNat : Int)) = decide (a.toNat < b.toNat)
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  have hugt : ∀ a b : BitVec (width * 8), zopz0zK_u a b = BitVec.ult b a := by
    intro a b
    unfold zopz0zK_u Sail.BitVec.toNatInt BitVec.ult
    change decide ((a.toNat : Int) > (b.toNat : Int)) = decide (b.toNat < a.toNat)
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases op <;> simp [sailAmoAluCore, rv64AmoAluSpec, hslt, hsgt, hult, hugt]
  · simp [sailAmoAluCore, BitVec.add_comm]
  · simp [sailAmoAluCore, BitVec.xor_comm]
  · simp [sailAmoAluCore, BitVec.and_comm]
  · simp [sailAmoAluCore, BitVec.or_comm]

/-- Direct `SailM` bisimulation for RV64 `Zacas` 128-bit register-pair accessors (`rX_pair_bits` /
    `wX_pair_bits` in `Regs.lean`, lines 720–732): proves `zreg` (`x0`) reads `0#128` and ignores
    pair writes, while even register pair `(x2, x3)` (`sp`, `gp`) packs `hi +++ lo` and unpacks
    `data[63:0]` / `data[127:64]` with exact roundtrip in `SailM`. -/
theorem rv64ZacasRegPair_bisim_sail (lo hi : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hlo : s.regs.get? .x2 = some lo)
    (hhi : s.regs.get? .x3 = some hi) :
    (rX_pair_bits zreg).run s = .ok (0#(64 * 2)) s ∧
    (wX_pair_bits zreg (hi +++ lo)).run s = .ok () s ∧
    (rX_pair_bits sp).run s = .ok (hi +++ lo) s ∧
    (wX_pair_bits sp (hi +++ lo)).run s =
      .ok () { s with regs := (s.regs.insert .x2 lo).insert .x3 hi } := by
  have hr2 : (rX_bits sp).run s = .ok lo s := by
    unfold sp rX_bits rX regval_from_reg zero_extend Sail.BitVec.zeroExtend Sail.BitVec.toNatInt
    simp [readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
    dsimp [EStateM.bind, EStateM.get, EStateM.pure, EStateM.run]
    rw [hlo]; rfl
  have hreg3 : regidx_offset_range sp 1 = .Regidx 3#5 := by
    unfold sp regidx_offset_range
    rfl
  have hr3 : (rX_bits (regidx_offset_range sp 1)).run s = .ok hi s := by
    rw [hreg3]
    unfold rX_bits rX regval_from_reg Sail.BitVec.toNatInt
    simp [readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
    dsimp [EStateM.bind, EStateM.get, EStateM.pure, EStateM.run]
    rw [hhi]; rfl
  have hlo_ext : Sail.BitVec.extractLsb (hi +++ lo) (Functions.xlen -i 1) 0 = lo := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    change (BitVec.extractLsb 63 0 (hi +++ lo)).getLsbD k = lo.getLsbD k
    have hk' : k < 64 := hk
    rw [BitVec.getLsbD_extractLsb]
    simp only [Nat.zero_add, Nat.sub_zero, BitVec.getLsbD_append]
    simp [hk']
  have hhi_ext : Sail.BitVec.extractLsb (hi +++ lo) ((Functions.xlen *i 2) -i 1) Functions.xlen = hi := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    change (BitVec.extractLsb 127 64 (hi +++ lo)).getLsbD k = hi.getLsbD k
    have hk' : k < 64 := hk
    have hk64 : ¬(64 + k < 64) := by omega
    have hsub : 64 + k - 64 = k := by omega
    rw [BitVec.getLsbD_extractLsb]
    simp only [show 127 - 64 + 1 = 64 by decide, BitVec.getLsbD_append]
    simp [hk', hk64, hsub]
  have hw2 : ∀ (v : BitVec 64) (st : SequentialState RegisterType trivialChoiceSource),
      (wX_bits sp v).run st = .ok () { st with regs := st.regs.insert .x2 v } := by
    intro v st
    unfold sp
    simp [wX_bits, wX, regval_into_reg, xreg_write_callback, reg_name_forwards,
      encdec_reg_forwards_matches, encdec_reg_forwards, get_config_use_abi_names,
      LeanRV64D.Functions.not, reg_arch_name_raw_forwards, xreg_full_write_callback,
      zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.toNatInt, to_bits, get_slice_int,
      writeReg, PreSail.writeReg, modify, modifyGet, MonadStateOf.modifyGet]
    rfl
  have hw3 : ∀ (v : BitVec 64) (st : SequentialState RegisterType trivialChoiceSource),
      (wX_bits (regidx_offset_range sp 1) v).run st = .ok () { st with regs := st.regs.insert .x3 v } := by
    intro v st
    rw [hreg3]
    simp [wX_bits, wX, regval_into_reg, xreg_write_callback, reg_name_forwards,
      encdec_reg_forwards_matches, encdec_reg_forwards, get_config_use_abi_names,
      LeanRV64D.Functions.not, reg_arch_name_raw_forwards, xreg_full_write_callback,
      zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.toNatInt, to_bits, get_slice_int,
      writeReg, PreSail.writeReg, modify, modifyGet, MonadStateOf.modifyGet]
    rfl
  refine ⟨rfl, rfl, ?_, ?_⟩
  · unfold rX_pair_bits
    have hbne : bne sp zreg = true := rfl
    rw [hbne]
    dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at hr2 hr3 ⊢
    rw [hr3]; dsimp only; rw [hr2]
  · unfold wX_pair_bits
    have hbne : bne sp zreg = true := rfl
    rw [hbne]
    dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at hw2 hw3 ⊢
    rw [hlo_ext, hhi_ext, hw2]; dsimp only; rw [hw3]

/-- Physical-RAM execution core of upstream `execute_AMO` (`InstsEnd.lean`, lines 71793–71888) for
    64-bit (`width = 8`, `.D`) `Zaamo` / `Zacas` operations over aligned flat physical RAM. -/
def sailAmo64RamExec (op : amoop) (rs2 rs1 rd : regidx) : SailM ExecutionResult := do
  let vaddr ← match ← ext_data_get_addr rs1 (zeros (n := 64)) (.Atomic (op, false, false, .Data, .Data)) 8 with
    | .Ext_DataAddr_Error e => pure (ExecutionResult.Ext_DataAddr_Check_Failure e)
    | .Ext_DataAddr_OK (.Virtaddr va) => do
      let (loaded_le, _) ← LeanRV64D.Functions.read_ram .Read_plain (.Physaddr va) 8 false
      let loaded : BitVec (8 * 8) := loaded_le
      let rs2_val : BitVec (8 * 8) := trunc (m := 64) (← rX_bits rs2)
      let result : BitVec (8 * 8) := sailAmoAluCore (width := 8) op rs2_val loaded
      let rd_cmp : BitVec (8 * 8) := trunc (m := 64) (← rX_bits rd)
      if (op == .AMOCAS) && (loaded != rd_cmp) then
        wX_bits rd (sign_extend (m := 64) loaded)
        pure (.Retire_Success ())
      else
        let ok ← LeanRV64D.Functions.write_ram .Write_plain (.Physaddr va) 8
          (sign_extend (m := 64) result) ()
        if ok then
          wX_bits rd (sign_extend (m := 64) loaded)
          pure (.Retire_Success ())
        else
          internal_error "extensions/A/zaamo_insts.sail" 153 "AMO got false from mem_write_value"
  pure vaddr

/-- End-to-end `SailM` bisimulation for 64-bit `Zaamo` & `Zacas` (`AMOCAS.D` match vs. mismatch and
    all 9 `Zaamo` RMW operations) over flat physical RAM (`rs1 = sp`, `rs2 = gp`, `rd = ra`):
    proves `Zaamo` and matching `AMOCAS.D` atomically write `rv64AmoAluSpec op rs2_val loaded` to
    memory while writing the old `loaded` value to `rd`, whereas mismatching `AMOCAS.D` leaves RAM
    untouched and still updates `rd` with `loaded`. -/
theorem sailAmo64RamExec_bisim_sail (op : amoop) (addr rs2_val rd_old : BitVec 64)
    (loaded : BitVec (8 * 8))
    (s : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : s.regs.get? .x2 = some addr)
    (hrs2 : s.regs.get? .x3 = some rs2_val)
    (hrd : s.regs.get? .x1 = some rd_old)
    (hmem : rv64ReadMemBytesSpec 8 addr.toNat s.mem = some loaded) :
    (sailAmo64RamExec op (.Regidx 0b00011#5) sp ra).run s =
      .ok (.Retire_Success ())
        (if op == .AMOCAS && loaded != rd_old then
          { s with regs := s.regs.insert .x1 loaded }
        else
          { s with
            mem := rv64WriteMemBytesSpec 8 addr.toNat (rv64AmoAluSpec op rs2_val loaded) s.mem
            regs := s.regs.insert .x1 loaded }) := by
  have haddr := rv64iEffectiveAddr_ext_data_get_addr_bisim addr 0#12
    (.Atomic (op, false, false, .Data, .Data)) 8 s hrs1
  have hz : rv64iEffectiveAddrSpec addr 0#12 = addr := by
    simp [rv64iEffectiveAddrSpec]
  rw [hz] at haddr
  have hread := read_ram_plain_bisim_sail 8 addr loaded s hmem
  have hr3 : (rX_bits (.Regidx 0b00011#5)).run s = .ok rs2_val s := by
    unfold rX_bits rX regval_from_reg Sail.BitVec.toNatInt
    simp [readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
    dsimp [EStateM.bind, EStateM.get, EStateM.pure, EStateM.run]
    rw [hrs2]; rfl
  have hr1 := rX_bits_ra_run rd_old s hrd
  have halu : sailAmoAluCore (width := 8) op rs2_val loaded = rv64AmoAluSpec op rs2_val loaded :=
    (rv64ZaamoAlu_bisim_sail (width := 8) op rs2_val loaded).1
  have hsext_ld : sign_extend (m := 64) loaded = loaded := by
    simp [sign_extend, Sail.BitVec.signExtend]
  have hsext_res : sign_extend (m := 64) (rv64AmoAluSpec op rs2_val loaded) =
      rv64AmoAluSpec op rs2_val loaded := by
    simp [sign_extend, Sail.BitVec.signExtend]
  have htrunc64 : ∀ v : BitVec 64, trunc (m := 64) v = v := by
    intro v
    simp [trunc, Sail.BitVec.truncate]
  unfold sailAmo64RamExec
  have hzero64 : zeros (n := 64) = sign_extend (m := 64) 0#12 := rfl
  rw [hzero64]
  dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at haddr hread hr3 hr1 ⊢
  rw [haddr]; dsimp [EStateM.bind]
  rw [hread]; dsimp [EStateM.bind]
  rw [hr3]; dsimp [EStateM.bind]
  rw [hr1]; dsimp [EStateM.bind]
  rw [htrunc64, htrunc64, halu]
  cases hcas : (op == .AMOCAS && loaded != rd_old)
  · dsimp [EStateM.bind, EStateM.pure]
    have hwrite := write_ram_plain_bisim_sail 8 addr (rv64AmoAluSpec op rs2_val loaded) s
    dsimp [EStateM.run] at hwrite
    rw [hsext_res, hwrite]; dsimp [EStateM.bind, EStateM.pure]
    have hw1 := wX_bits_ra_run loaded
      { s with mem := rv64WriteMemBytesSpec 8 addr.toNat (rv64AmoAluSpec op rs2_val loaded) s.mem }
    dsimp [EStateM.run] at hw1
    rw [hsext_ld, hw1]
  · dsimp [EStateM.bind, EStateM.pure]
    have hw1 := wX_bits_ra_run loaded s
    dsimp [EStateM.run] at hw1
    rw [hsext_ld, hw1]

/-- `Zalrsc` memory ordering flag mapping (`read_kind_of_flags`, `write_kind_of_flags` in `Mem.lean`,
    lines 232–267) and RV64 width gate (`lrsc_width_valid` in `PlatformConfig.lean`, lines 6650–6654)
    bisimulation in `SailM`. -/
theorem rv64ZalrscFlagsAndWidths_bisim_sail
    (s : SequentialState RegisterType trivialChoiceSource) :
    lrsc_width_valid 4 = true ∧
    lrsc_width_valid 8 = true ∧
    lrsc_width_valid 1 = false ∧
    lrsc_width_valid 2 = false ∧
    (read_kind_of_flags false false false).run s = .ok .Read_plain s ∧
    (read_kind_of_flags false false true).run s = .ok .Read_RISCV_reserved s ∧
    (read_kind_of_flags true false true).run s = .ok .Read_RISCV_reserved_acquire s ∧
    (read_kind_of_flags true true true).run s = .ok .Read_RISCV_reserved_strong_acquire s ∧
    (write_kind_of_flags false false false).run s = .ok .Write_plain s ∧
    (write_kind_of_flags false false true).run s = .ok .Write_RISCV_conditional s ∧
    (write_kind_of_flags false true true).run s = .ok .Write_RISCV_conditional_release s ∧
    (write_kind_of_flags true true true).run s = .ok .Write_RISCV_conditional_strong_release s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Monadic bisimulation for upstream `read_ram` and `write_ram` (`PhysMemInterface.lean`,
    lines 303–381) under `Zalrsc` reserved/conditional access kinds (`Read_RISCV_reserved*` and
    `Write_RISCV_conditional*`), plus the exact `execute_STORECON` (`InstsEnd.lean`, line 67358)
    destination status encoding (`0#64` on success `b = true`, `1#64` on failure `b = false`). -/
theorem rv64ZalrscRamAndScStatus_bisim_sail (width : Nat) (paddr : BitVec 64)
    (bytes data : BitVec (8 * width)) (b : Bool)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hmem : rv64ReadMemBytesSpec width paddr.toNat s.mem = some bytes) :
    (LeanRV64D.Functions.read_ram .Read_RISCV_reserved (.Physaddr paddr) width false).run s =
      .ok (bytes, ()) s ∧
    (LeanRV64D.Functions.read_ram .Read_RISCV_reserved_acquire (.Physaddr paddr) width false).run s =
      .ok (bytes, ()) s ∧
    (LeanRV64D.Functions.write_ram .Write_RISCV_conditional (.Physaddr paddr) width data ()).run s =
      .ok true { s with mem := rv64WriteMemBytesSpec width paddr.toNat data s.mem } ∧
    (LeanRV64D.Functions.write_ram .Write_RISCV_conditional_release (.Physaddr paddr) width data ()).run s =
      .ok true { s with mem := rv64WriteMemBytesSpec width paddr.toNat data s.mem } ∧
    zero_extend (m := 64) (bool_bit_forwards (!b)) = (if b then 0#64 else 1#64) := by
  have hr := readBytes_run_of_spec_some width paddr.toNat s bytes hmem
  have hw := writeBytes_run_eq_spec paddr.toNat data s
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold LeanRV64D.Functions.read_ram LeanRV64D.ConcurrencyInterfaceV1.sail_mem_read
      PreSail.sail_mem_read default_meta
    dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at hr ⊢
    rw [hr]; rfl
  · unfold LeanRV64D.Functions.read_ram LeanRV64D.ConcurrencyInterfaceV1.sail_mem_read
      PreSail.sail_mem_read default_meta
    dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at hr ⊢
    rw [hr]; rfl
  · unfold LeanRV64D.Functions.write_ram LeanRV64D.ConcurrencyInterfaceV1.sail_mem_write
      PreSail.sail_mem_write __WriteRAM_Meta
    dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at hw ⊢
    rw [hw]; rfl
  · unfold LeanRV64D.Functions.write_ram LeanRV64D.ConcurrencyInterfaceV1.sail_mem_write
      PreSail.sail_mem_write __WriteRAM_Meta
    dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at hw ⊢
    rw [hw]; rfl
  · cases b <;> rfl

/-- Exact mirror of `csr_access_type` (`ZicsrInsts.lean`, lines 259–266; used by `execute_CSRReg` /
    `execute_CSRImm` in `InstsEnd.lean`, lines 71721–71727) and the `doCSR` (`ZicsrInsts.lean`,
    lines 22268–22272) bitwise update rule. -/
def sailCsrAccessType (op : csrop) (rd_is_x0 rs1_imm_is_zero : Bool) : CSRAccessType :=
  match (op, rd_is_x0, rs1_imm_is_zero) with
  | (.CSRRW, true, _) => .CSRWrite
  | (.CSRRW, false, _) => .CSRReadWrite
  | (.CSRRS, _, true) => .CSRRead
  | (.CSRRC, _, true) => .CSRRead
  | (.CSRRS, _, false) => .CSRReadWrite
  | (.CSRRC, _, false) => .CSRReadWrite

def sailCsrWriteValCore (op : csrop) (read_val rs1_val : BitVec 64) : BitVec 64 :=
  match op with
  | .CSRRW => rs1_val
  | .CSRRS => read_val ||| rs1_val
  | .CSRRC => read_val &&& ~~~rs1_val

/-- `Zicsr` opcode encoding (`encdec_csrop_forwards`, `csrop_of_num`/`num_of_csrop`), access-type
    dispatch (`CSRRW x0` suppresses CSR read; `CSRRS`/`CSRRC` with zero `rs1`/`uimm` suppresses CSR
    write), and bitwise CSR update algebra (`CSRRS`/`CSRRC` zero identity, idempotence, and clear). -/
theorem rv64ZicsrOpAndAccess_bisim_sail (op : csrop) (rd_x0 : Bool) (csr_val mask : BitVec 64) :
    encdec_csrop_forwards .CSRRW = 0b01#2 ∧
    encdec_csrop_forwards .CSRRS = 0b10#2 ∧
    encdec_csrop_forwards .CSRRC = 0b11#2 ∧
    sailCsrAccessType .CSRRW true false = .CSRWrite ∧
    sailCsrAccessType .CSRRW false true = .CSRReadWrite ∧
    sailCsrAccessType .CSRRS rd_x0 true = .CSRRead ∧
    sailCsrAccessType .CSRRC rd_x0 true = .CSRRead ∧
    sailCsrAccessType .CSRRS rd_x0 false = .CSRReadWrite ∧
    sailCsrAccessType .CSRRC rd_x0 false = .CSRReadWrite ∧
    sailCsrWriteValCore .CSRRW csr_val mask = mask ∧
    sailCsrWriteValCore .CSRRS csr_val 0#64 = csr_val ∧
    sailCsrWriteValCore .CSRRC csr_val 0#64 = csr_val ∧
    sailCsrWriteValCore .CSRRS (sailCsrWriteValCore .CSRRS csr_val mask) mask =
      sailCsrWriteValCore .CSRRS csr_val mask ∧
    (sailCsrWriteValCore .CSRRC csr_val mask) &&& mask = 0#64 ∧
    (op = .CSRRW ∨ op = .CSRRS ∨ op = .CSRRC) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [sailCsrWriteValCore]
  · have hones64 : ~~~(0#64) = BitVec.allOnes 64 := by decide
    unfold sailCsrWriteValCore
    rw [hones64, BitVec.and_allOnes]
  · simp [sailCsrWriteValCore, BitVec.or_assoc]
  · simp [sailCsrWriteValCore, BitVec.and_assoc]
  · cases op <;> simp

/-- `Zicsr` privilege-field extraction, read-only address check (`csrAccess`, `csrPriv`,
    `check_CSR_access` in `SysControl.lean`, lines 238–261), and `SailM` execution core of
    `execute_CSRReg` / `execute_CSRImm` (`InstsEnd.lean`, lines 71721–71728; `doCSR` in
    `ZicsrInsts.lean`, lines 22241–22279): proves CSR bits `[11:10] = 0b11` reject writes
    (`CSRWrite` / `CSRReadWrite`) while allowing `CSRRead`, CSR bits `[9:8]` compare against
    privilege bits (`0b00`, `0b01`, `0b11`) via `zopz0zKzJ_u`, and `SailM` `mscratch` (`0x340`)
    execution atomically updates `.mscratch` and `rd` on `CSRRW`/`CSRRS`/`CSRRC` while leaving
    `.mscratch` untouched on `CSRRead` (`rs1 = x0`). -/
def sailCsrMscratchExec (csr : BitVec 12) (rs1 rd : regidx) (op : csrop) : SailM ExecutionResult := do
  let access_type := sailCsrAccessType op (rd == zreg) (rs1 == zreg)
  let priv ← readReg .cur_privilege
  let priv_bits : BitVec 2 := match priv with
    | .User | .VirtualUser => 0b00#2
    | .Supervisor | .VirtualSupervisor => 0b01#2
    | .Machine => 0b11#2
  if !(check_CSR_access csr access_type && zopz0zKzJ_u priv_bits (csrPriv csr)) then
    pure (.Illegal_Instruction ())
  else
    let read_val ← if bne access_type .CSRWrite then readReg .mscratch else pure (zeros (n := 64))
    if access_type == .CSRRead then
      wX_bits rd read_val
      pure (.Retire_Success ())
    else
      let rs1_val ← rX_bits rs1
      let write_val := sailCsrWriteValCore op read_val rs1_val
      writeReg .mscratch write_val
      wX_bits rd read_val
      pure (.Retire_Success ())

theorem rv64ZicsrPrivAndReadOnlyCheck_bisim_sail (csr : BitVec 12)
    (op : csrop) (old_csr rs1_val : BitVec 64)
    (sM sU : SequentialState RegisterType trivialChoiceSource)
    (hprivM : sM.regs.get? .cur_privilege = some .Machine)
    (hmscratch : sM.regs.get? .mscratch = some old_csr)
    (hrs1 : sM.regs.get? .x2 = some rs1_val)
    (hprivU : sU.regs.get? .cur_privilege = some .User) :
    csrAccess csr = csr.extractLsb 11 10 ∧
    csrPriv csr = csr.extractLsb 9 8 ∧
    check_CSR_access csr .CSRRead = true ∧
    check_CSR_access csr .CSRWrite = (csr.extractLsb 11 10 != 0b11#2) ∧
    check_CSR_access csr .CSRReadWrite = (csr.extractLsb 11 10 != 0b11#2) ∧
    zopz0zKzJ_u 0b11#2 (csrPriv csr) = true ∧
    zopz0zKzJ_u 0b01#2 (csrPriv csr) = BitVec.ule (csr.extractLsb 9 8) 0b01#2 ∧
    zopz0zKzJ_u 0b00#2 (csrPriv csr) = (csr.extractLsb 9 8 == 0b00#2) ∧
    (sailCsrMscratchExec 0x340#12 sp ra .CSRRS).run sU = .ok (.Illegal_Instruction ()) sU ∧
    (sailCsrMscratchExec 0xF11#12 sp ra .CSRRW).run sM = .ok (.Illegal_Instruction ()) sM ∧
    (sailCsrMscratchExec 0x340#12 zreg ra .CSRRS).run sM =
      .ok (.Retire_Success ()) { sM with regs := sM.regs.insert .x1 old_csr } ∧
    (sailCsrMscratchExec 0x340#12 sp ra op).run sM =
      .ok (.Retire_Success ())
        { sM with regs := (sM.regs.insert .mscratch (sailCsrWriteValCore op old_csr rs1_val)).insert .x1 old_csr } := by
  have hge_m : zopz0zKzJ_u 0b11#2 (csrPriv csr) = true := by
    unfold zopz0zKzJ_u Sail.BitVec.toNatInt
    change decide ((3 : Int) ≥ ((csrPriv csr).toNat : Int)) = true
    rw [decide_eq_true_eq]
    have hlt := (csrPriv csr).isLt
    omega
  have hge_s : zopz0zKzJ_u 0b01#2 (csrPriv csr) = BitVec.ule (csr.extractLsb 9 8) 0b01#2 := by
    unfold zopz0zKzJ_u csrPriv Sail.BitVec.extractLsb Sail.BitVec.toNatInt BitVec.ule
    change decide ((1 : Int) ≥ ((csr.extractLsb 9 8).toNat : Int)) =
      decide ((csr.extractLsb 9 8).toNat ≤ 1)
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  have hge_u : zopz0zKzJ_u 0b00#2 (csrPriv csr) = (csr.extractLsb 9 8 == 0b00#2) := by
    unfold zopz0zKzJ_u csrPriv Sail.BitVec.extractLsb Sail.BitVec.toNatInt
    change decide ((0 : Int) ≥ ((csr.extractLsb 9 8).toNat : Int)) =
      (csr.extractLsb 9 8 == 0b00#2)
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, beq_iff_eq]
    constructor
    · intro h
      apply BitVec.eq_of_toNat_eq
      change (csr.extractLsb 9 8).toNat = 0
      omega
    · intro h
      rw [h]
      decide
  have hr2 : ∀ (st : SequentialState RegisterType trivialChoiceSource),
      st.regs.get? .x2 = some rs1_val → (rX_bits sp).run st = .ok rs1_val st := by
    intro st hst
    unfold sp rX_bits rX regval_from_reg zero_extend Sail.BitVec.zeroExtend Sail.BitVec.toNatInt
    simp [readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
    dsimp [EStateM.bind, EStateM.get, EStateM.pure, EStateM.run]
    rw [hst]; rfl
  refine ⟨rfl, rfl, rfl, ?_, ?_, hge_m, hge_s, hge_u, ?_, ?_, ?_, ?_⟩
  · unfold check_CSR_access LeanRV64D.Functions.not csrAccess Sail.BitVec.extractLsb
    change (!((true || false) && (BitVec.extractLsb 11 10 csr == 3#2))) =
      (!(BitVec.extractLsb 11 10 csr == 3#2))
    simp
  · unfold check_CSR_access LeanRV64D.Functions.not csrAccess Sail.BitVec.extractLsb
    change (!((false || true) && (BitVec.extractLsb 11 10 csr == 3#2))) =
      (!(BitVec.extractLsb 11 10 csr == 3#2))
    simp
  · unfold sailCsrMscratchExec
    simp [sailCsrAccessType, check_CSR_access, LeanRV64D.Functions.not, csrAccess, csrPriv,
      zopz0zKzJ_u, Sail.BitVec.extractLsb, Sail.BitVec.toNatInt,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.get, EStateM.pure, EStateM.run, hprivU]
  · have hra : (ra == zreg) = false := rfl
    have hsp : (sp == zreg) = false := rfl
    unfold sailCsrMscratchExec
    simp [hra, hsp, sailCsrAccessType, check_CSR_access, LeanRV64D.Functions.not, csrAccess, csrPriv,
      zopz0zKzJ_u, Sail.BitVec.extractLsb, Sail.BitVec.toNatInt,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.get, EStateM.pure, EStateM.run, hprivM]
    rfl
  · have hw1 := wX_bits_ra_run old_csr sM
    dsimp [EStateM.run] at hw1
    unfold sailCsrMscratchExec
    have hacc : sailCsrAccessType .CSRRS (ra == zreg) (zreg == zreg) = .CSRRead := rfl
    have hchk : (!(check_CSR_access 0x340#12 .CSRRead && zopz0zKzJ_u 0b11#2 (csrPriv 0x340#12))) = false := by decide
    have hbne : bne CSRAccessType.CSRRead .CSRWrite = true := rfl
    rw [hacc]
    simp only [readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
    dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.get, EStateM.pure, EStateM.run]
    rw [hprivM]; dsimp [EStateM.bind, EStateM.get, EStateM.pure]
    rw [hchk]; dsimp [EStateM.bind, EStateM.get, EStateM.pure]
    rw [hbne]; dsimp [EStateM.bind, EStateM.get, EStateM.pure]
    rw [hmscratch]; dsimp [EStateM.bind, EStateM.get, EStateM.pure]
    have hbeqr : (CSRAccessType.CSRRead == .CSRRead) = true := rfl
    rw [hbeqr]; dsimp [EStateM.bind, EStateM.pure]
    rw [hw1]
  · have hr_sp := hr2 sM hrs1
    dsimp [EStateM.run] at hr_sp
    unfold sailCsrMscratchExec
    have hacc : sailCsrAccessType op (ra == zreg) (sp == zreg) = .CSRReadWrite := by
      cases op <;> rfl
    have hchk : (!(check_CSR_access 0x340#12 .CSRReadWrite && zopz0zKzJ_u 0b11#2 (csrPriv 0x340#12))) = false := by decide
    have hbne : bne CSRAccessType.CSRReadWrite .CSRWrite = true := rfl
    have hbeqr : (CSRAccessType.CSRReadWrite == .CSRRead) = false := rfl
    rw [hacc]
    simp only [readReg, PreSail.readReg, writeReg, PreSail.writeReg,
      modify, modifyGet, MonadStateOf.modifyGet, get, getThe, MonadStateOf.get]
    dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.get, EStateM.modifyGet, EStateM.pure, EStateM.run]
    rw [hprivM]; dsimp [EStateM.bind, EStateM.get, EStateM.modifyGet, EStateM.pure]
    rw [hchk]; dsimp [EStateM.bind, EStateM.get, EStateM.modifyGet, EStateM.pure]
    rw [hbne]; dsimp [EStateM.bind, EStateM.get, EStateM.modifyGet, EStateM.pure]
    rw [hmscratch]; dsimp [EStateM.bind, EStateM.get, EStateM.modifyGet, EStateM.pure]
    rw [hbeqr]; dsimp [EStateM.bind, EStateM.get, EStateM.modifyGet, EStateM.pure]
    rw [hr_sp]; dsimp [EStateM.bind, EStateM.get, EStateM.modifyGet, EStateM.pure]
    have hw1 := wX_bits_ra_run old_csr
      { sM with regs := sM.regs.insert .mscratch (sailCsrWriteValCore op old_csr rs1_val) }
    dsimp [EStateM.run] at hw1
    rw [hw1]

/-- Privileged architecture, `mstatus` VM-control fields (`MPRV`/`MPP`/`TVM`/`MXR`/`SUM`), and
    synchronous trap formation (`privLevel_bits_backwards` / `privLevel_bits_forwards`,
    `effectivePrivilege`, and `make_sync_exception` in `Types.lean`, `SysRegs.lean`, and
    `SysControl.lean`): proves `privLevel` roundtrips in `SailM`, `MPRV = 1` overrides data-access
    privilege to `MPP` (`Supervisor` / `User`) while leaving `InstructionFetch` at `cur_privilege`,
    `mstatus` bits `[20:18]` extract `TVM`/`MXR`/`SUM`, and `make_sync_exception` populates `xtval`
    for page faults while clearing `xtval` (`none`) on `ECALL`. -/
theorem rv64PrivEffectiveAndTvm_bisim_sail (p : Privilege) (mstatus_val vaddr : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource) :
    (privLevel_bits_forwards (privLevel_bits_backwards p)).run s = .ok p s ∧
    (effectivePrivilege (.InstructionFetch ()) mstatus_val p).run s = .ok p s ∧
    (_get_Mstatus_MPRV mstatus_val = 0#1 →
      (effectivePrivilege (.Load .Data) mstatus_val p).run s = .ok p s) ∧
    (_get_Mstatus_MPRV mstatus_val = 1#1 → _get_Mstatus_MPP mstatus_val = 0b01#2 →
      (effectivePrivilege (.Load .Data) mstatus_val .Machine).run s = .ok .Supervisor s) ∧
    (_get_Mstatus_MPRV mstatus_val = 1#1 → _get_Mstatus_MPP mstatus_val = 0b00#2 →
      (effectivePrivilege (.Store .Data) mstatus_val .Machine).run s = .ok .User s) ∧
    _get_Mstatus_TVM mstatus_val = mstatus_val.extractLsb 20 20 ∧
    _get_Mstatus_MXR mstatus_val = mstatus_val.extractLsb 19 19 ∧
    _get_Mstatus_SUM mstatus_val = mstatus_val.extractLsb 18 18 ∧
    make_sync_exception (.E_U_EnvCall ()) vaddr =
      { trap := .E_U_EnvCall (), excinfo := none, ext := none } ∧
    make_sync_exception (.E_Load_Page_Fault ()) vaddr =
      { trap := .E_Load_Page_Fault (), excinfo := some vaddr, ext := none } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · cases p <;> rfl
  · unfold effectivePrivilege
    have hne : bne (MemoryAccessType.InstructionFetch (k_a := mem_payload) ())
        (MemoryAccessType.InstructionFetch (k_a := mem_payload) ()) = false := rfl
    rw [hne]; rfl
  · intro hmprv
    unfold effectivePrivilege
    rw [hmprv]; simp
  · intro hmprv hmpp
    unfold effectivePrivilege
    have hne : bne (MemoryAccessType.Load mem_payload.Data)
        (MemoryAccessType.InstructionFetch (k_a := mem_payload) ()) = true := rfl
    rw [hne, hmprv, hmpp]; rfl
  · intro hmprv hmpp
    unfold effectivePrivilege
    have hne : bne (MemoryAccessType.Store mem_payload.Data)
        (MemoryAccessType.InstructionFetch (k_a := mem_payload) ()) = true := rfl
    rw [hne, hmprv, hmpp]; rfl

/-- RV64 `satp` CSR layout (`Mode` `[63:60]`, `ASID` `[59:44]`, `PPN` `[43:0]`), `SATPMode` decoding
    (`Bare = 0`, `Sv39 = 8`, `Sv48 = 9`, `Sv57 = 10`; `Sv32 = 1` rejected on `RV64`), and virtual
    address width (`satp_mode_width_forwards` / `satp_mode_width_backwards`) bisimulation. -/
theorem rv64Satp64ModeDecode_bisim_sail (mode : BitVec 4) (asid : BitVec 16) (ppn : BitVec 44)
    (s : SequentialState RegisterType trivialChoiceSource) :
    Functions.asidlen = 16 ∧
    Functions.pagesize_bits = 12 ∧
    Functions.physaddr_bits = 56 ∧
    _get_Satp64_Mode (mode +++ (asid +++ ppn)) = mode ∧
    _get_Satp64_Asid (mode +++ (asid +++ ppn)) = asid ∧
    _get_Satp64_PPN (mode +++ (asid +++ ppn)) = ppn ∧
    satpMode_of_bits .RV64 0x0#4 = some .Bare ∧
    satpMode_of_bits .RV64 0x1#4 = none ∧
    satpMode_of_bits .RV64 0x8#4 = some .Sv39 ∧
    satpMode_of_bits .RV64 0x9#4 = some .Sv48 ∧
    satpMode_of_bits .RV64 0xA#4 = some .Sv57 ∧
    (satp_mode_width_forwards .Sv39).run s = .ok 39 s ∧
    (satp_mode_width_forwards .Sv48).run s = .ok 48 s ∧
    satp_mode_width_backwards 39 = .Sv39 ∧
    satp_mode_width_backwards 48 = .Sv48 := by
  have hmode : _get_Satp64_Mode (mode +++ (asid +++ ppn)) = mode := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    change (BitVec.extractLsb 63 60 (mode +++ (asid +++ ppn))).getLsbD k = mode.getLsbD k
    have hk' : k < 4 := hk
    have hk60 : ¬(60 + k < 60) := by omega
    have hsub : 60 + k - 60 = k := by omega
    rw [BitVec.getLsbD_extractLsb]
    simp only [show 63 - 60 + 1 = 4 by decide, BitVec.getLsbD_append]
    simp [hk', hk60, hsub]
  have hasid : _get_Satp64_Asid (mode +++ (asid +++ ppn)) = asid := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    change (BitVec.extractLsb 59 44 (mode +++ (asid +++ ppn))).getLsbD k = asid.getLsbD k
    have hk' : k < 16 := hk
    have hk60 : 44 + k < 60 := by omega
    have hk44 : ¬(44 + k < 44) := by omega
    have hsub : 44 + k - 44 = k := by omega
    rw [BitVec.getLsbD_extractLsb]
    simp only [show 59 - 44 + 1 = 16 by decide, BitVec.getLsbD_append]
    simp [hk', hk60, hk44, hsub]
  have hppn : _get_Satp64_PPN (mode +++ (asid +++ ppn)) = ppn := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    change (BitVec.extractLsb 43 0 (mode +++ (asid +++ ppn))).getLsbD k = ppn.getLsbD k
    have hk' : k < 44 := hk
    have hk60 : k < 60 := by omega
    rw [BitVec.getLsbD_extractLsb]
    simp only [Nat.zero_add, show 43 - 0 + 1 = 44 by decide, BitVec.getLsbD_append]
    simp [hk', hk60]
  exact ⟨rfl, rfl, rfl, hmode, hasid, hppn, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `Sv39` (39-bit) and `Sv48` (48-bit) canonical sign-extended virtual address check from upstream
    `translateAddr` (`Vmem.lean`, lines 537–539): proves `vaddr == sign_extend 64 (vaddr[sv_width-1:0])`
    accepts canonical user (`0x0000_0000_8000_1000`) and kernel-high (`0xFFFF_FFC0_0000_0000` for
    `Sv39`, `0xFFFF_8000_0000_0000` for `Sv48`) addresses while rejecting non-canonical hole
    addresses (`0x0000_0040_0000_0000` in `Sv39`, `0x0000_8000_0000_0000` in `Sv48`). -/
def rv64SvCanonicalVaddrSpec (sv_width : Nat) (vaddr : BitVec 64) : Bool :=
  vaddr == sign_extend (m := 64) (Sail.BitVec.extractLsb vaddr ((Int.ofNat sv_width) -i 1) 0)

theorem rv64Sv39Sv48CanonicalVaddr_bisim_sail (lo38 : BitVec 38) (lo47 : BitVec 47) :
    rv64SvCanonicalVaddrSpec 39 (0#26 +++ lo38) = true ∧
    rv64SvCanonicalVaddrSpec 39 (BitVec.allOnes 26 +++ lo38) = true ∧
    rv64SvCanonicalVaddrSpec 39 0x0000004000000000#64 = false ∧
    rv64SvCanonicalVaddrSpec 48 (0#17 +++ lo47) = true ∧
    rv64SvCanonicalVaddrSpec 48 (BitVec.allOnes 17 +++ lo47) = true ∧
    rv64SvCanonicalVaddrSpec 48 0x0000800000000000#64 = false := by
  have hsv39_pos : rv64SvCanonicalVaddrSpec 39 (0#26 +++ lo38) = true := by
    simp only [rv64SvCanonicalVaddrSpec, beq_iff_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    change (0#26 +++ lo38).getLsbD k =
      ((BitVec.extractLsb 38 0 (0#26 +++ lo38)).signExtend 64).getLsbD k
    rw [BitVec.getLsbD_signExtend]
    have hk64 : k < 64 := hk
    simp only [hk64, decide_true, Bool.true_and]
    by_cases hk39 : k < 39
    · rw [if_pos hk39, BitVec.getLsbD_extractLsb]
      simp [hk39]
    · rw [if_neg hk39]
      have hmsb : (BitVec.extractLsb 38 0 (0#26 +++ lo38)).msb = false := by
        rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_extractLsb]
        simp only [Nat.zero_add, show 38 - 0 + 1 - 1 = 38 by decide, show 38 - 0 + 1 = 39 by decide,
          BitVec.getLsbD_append]
        simp
      have hk38 : ¬(k < 38) := by omega
      rw [hmsb]
      simp only [BitVec.getLsbD_append]
      simp [hk38]
  have hsv39_neg : rv64SvCanonicalVaddrSpec 39 (BitVec.allOnes 26 +++ lo38) = true := by
    simp only [rv64SvCanonicalVaddrSpec, beq_iff_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    change (BitVec.allOnes 26 +++ lo38).getLsbD k =
      ((BitVec.extractLsb 38 0 (BitVec.allOnes 26 +++ lo38)).signExtend 64).getLsbD k
    rw [BitVec.getLsbD_signExtend]
    have hk64 : k < 64 := hk
    simp only [hk64, decide_true, Bool.true_and]
    by_cases hk39 : k < 39
    · rw [if_pos hk39, BitVec.getLsbD_extractLsb]
      simp [hk39]
    · rw [if_neg hk39]
      have hmsb : (BitVec.extractLsb 38 0 (BitVec.allOnes 26 +++ lo38)).msb = true := by
        rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_extractLsb]
        simp only [Nat.zero_add, show 38 - 0 + 1 - 1 = 38 by decide, show 38 - 0 + 1 = 39 by decide,
          BitVec.getLsbD_append]
        simp
      have hk38 : ¬(k < 38) := by omega
      have hk26 : k - 38 < 26 := by omega
      rw [hmsb]
      simp only [BitVec.getLsbD_append]
      rw [if_neg hk38]
      exact BitVec.getLsbD_allOnes.trans (decide_eq_true hk26)
  have hsv48_pos : rv64SvCanonicalVaddrSpec 48 (0#17 +++ lo47) = true := by
    simp only [rv64SvCanonicalVaddrSpec, beq_iff_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    change (0#17 +++ lo47).getLsbD k =
      ((BitVec.extractLsb 47 0 (0#17 +++ lo47)).signExtend 64).getLsbD k
    rw [BitVec.getLsbD_signExtend]
    have hk64 : k < 64 := hk
    simp only [hk64, decide_true, Bool.true_and]
    by_cases hk48 : k < 48
    · rw [if_pos hk48, BitVec.getLsbD_extractLsb]
      simp [hk48]
    · rw [if_neg hk48]
      have hmsb : (BitVec.extractLsb 47 0 (0#17 +++ lo47)).msb = false := by
        rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_extractLsb]
        simp only [Nat.zero_add, show 47 - 0 + 1 - 1 = 47 by decide, show 47 - 0 + 1 = 48 by decide,
          BitVec.getLsbD_append]
        simp
      have hk47 : ¬(k < 47) := by omega
      rw [hmsb]
      simp only [BitVec.getLsbD_append]
      simp [hk47]
  have hsv48_neg : rv64SvCanonicalVaddrSpec 48 (BitVec.allOnes 17 +++ lo47) = true := by
    simp only [rv64SvCanonicalVaddrSpec, beq_iff_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    change (BitVec.allOnes 17 +++ lo47).getLsbD k =
      ((BitVec.extractLsb 47 0 (BitVec.allOnes 17 +++ lo47)).signExtend 64).getLsbD k
    rw [BitVec.getLsbD_signExtend]
    have hk64 : k < 64 := hk
    simp only [hk64, decide_true, Bool.true_and]
    by_cases hk48 : k < 48
    · rw [if_pos hk48, BitVec.getLsbD_extractLsb]
      simp [hk48]
    · rw [if_neg hk48]
      have hmsb : (BitVec.extractLsb 47 0 (BitVec.allOnes 17 +++ lo47)).msb = true := by
        rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_extractLsb]
        simp only [Nat.zero_add, show 47 - 0 + 1 - 1 = 47 by decide, show 47 - 0 + 1 = 48 by decide,
          BitVec.getLsbD_append]
        simp
      have hk47 : ¬(k < 47) := by omega
      have hk17 : k - 47 < 17 := by omega
      rw [hmsb]
      simp only [BitVec.getLsbD_append]
      rw [if_neg hk47]
      exact BitVec.getLsbD_allOnes.trans (decide_eq_true hk17)
  exact ⟨hsv39_pos, hsv39_neg, by decide, hsv48_pos, hsv48_neg, by decide⟩

/-- `Sv39` / `Sv48` 64-bit Page Table Entry (`PTE`) extraction (`ext_bits_of_PTE` `[63:54]`,
    `PPN_of_PTE` `[53:10]`, `pte_is_non_leaf`), permission check (`check_PTE_permission` in
    `VmemPte.lean`, lines 292–377: `Atomic` requires `R ∧ W`, `SUM` governs `Supervisor` access to
    `U = 1` pages, `MXR` makes `X = 1` pages readable), and dirty/accessed bit updates
    (`update_PTE_Bits`, lines 379–401). -/
theorem rv64SvPtePermissionsAndDirtyBits_bisim_sail
    (ext : BitVec 10) (ppn : BitVec 44) (rsw : BitVec 2) (op : amoop)
    (s : SequentialState RegisterType trivialChoiceSource) :
    ext_bits_of_PTE (ext +++ (ppn +++ (rsw +++ 0b00000001#8))) = ext ∧
    PPN_of_PTE (ext +++ (ppn +++ (rsw +++ 0b00000001#8))) = ppn ∧
    pte_is_non_leaf 0b00000001#8 = true ∧
    pte_is_non_leaf 0b00000011#8 = false ∧
    (check_PTE_permission (.Atomic (op, false, false, .Data, .Data)) .User false false
      0b00010111#8 0#10 ()).run s = .ok (.PTE_Check_Success ()) s ∧
    (check_PTE_permission (.Atomic (op, false, false, .Data, .Data)) .User false false
      0b00010011#8 0#10 ()).run s = .ok (.PTE_Check_Failure ((), .PTE_No_Permission ())) s ∧
    (check_PTE_permission (.Load .Data) .Supervisor false false
      0b00010011#8 0#10 ()).run s = .ok (.PTE_Check_Failure ((), .PTE_No_Permission ())) s ∧
    (check_PTE_permission (.Load .Data) .Supervisor false true
      0b00010011#8 0#10 ()).run s = .ok (.PTE_Check_Success ()) s ∧
    (check_PTE_permission (.Load .Data) .User true false
      0b00011001#8 0#10 ()).run s = .ok (.PTE_Check_Success ()) s ∧
    update_PTE_Bits (0#56 +++ 0b00010111#8) (.Load .Data) = some (0#56 +++ 0b01010111#8) ∧
    update_PTE_Bits (0#56 +++ 0b00010111#8) (.Atomic (op, false, false, .Data, .Data)) =
      some (0#56 +++ 0b11010111#8) ∧
    update_PTE_Bits (0#56 +++ 0b11010111#8) (.Store .Data) = none := by
  have hext : ext_bits_of_PTE (ext +++ (ppn +++ (rsw +++ 0b00000001#8))) = ext := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    change (BitVec.extractLsb 63 54 (ext +++ (ppn +++ (rsw +++ 0b00000001#8)))).getLsbD k = ext.getLsbD k
    have hk' : k < 10 := hk
    have hk54 : ¬(54 + k < 54) := by omega
    have hsub : 54 + k - 54 = k := by omega
    rw [BitVec.getLsbD_extractLsb]
    simp only [show 63 - 54 + 1 = 10 by decide, BitVec.getLsbD_append]
    simp [hk', hk54, hsub]
  have hppn : PPN_of_PTE (ext +++ (ppn +++ (rsw +++ 0b00000001#8))) = ppn := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    change (BitVec.extractLsb 53 10 (ext +++ (ppn +++ (rsw +++ 0b00000001#8)))).getLsbD k = ppn.getLsbD k
    have hk' : k < 44 := by simpa using hk
    have hk54 : 10 + k < 54 := by omega
    have hk10 : ¬(10 + k < 10) := by omega
    have hsub : 10 + k - 10 = k := by omega
    rw [BitVec.getLsbD_extractLsb]
    simp only [show 53 - 10 + 1 = 44 by decide, BitVec.getLsbD_append]
    simp [hk', hk54, hk10, hsub]
  refine ⟨hext, hppn, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · decide
  · simp [update_PTE_Bits, is_prefetch_access]
    decide
  · decide

/-- `Sv39` / `Sv48` page-table-walk fault mapping (`translationException` in `VmemPtw.lean`,
    lines 223–266): proves `PTW_No_Access` yields Access Faults while `PTW_Invalid_PTE` /
    `PTW_No_Permission` / `PTW_Misaligned` / `PTW_PTE_Needs_Update` yield Page Faults across
    `InstructionFetch`, `Load`, `LoadReserved`, `Store`, `StoreConditional`, and `Atomic`. -/
theorem rv64TranslationException_bisim_sail (op : amoop) (aq rl : Bool)
    (s : SequentialState RegisterType trivialChoiceSource) :
    (translationException (.InstructionFetch ()) (.PTW_No_Access ())).run s =
      .ok (.E_Fetch_Access_Fault ()) s ∧
    (translationException (.InstructionFetch ()) (.PTW_Invalid_PTE ())).run s =
      .ok (.E_Fetch_Page_Fault ()) s ∧
    (translationException (.Load .Data) (.PTW_No_Access ())).run s =
      .ok (.E_Load_Access_Fault ()) s ∧
    (translationException (.LoadReserved (aq, rl, .Data)) (.PTW_No_Permission ())).run s =
      .ok (.E_Load_Page_Fault ()) s ∧
    (translationException (.Store .Data) (.PTW_Invalid_PTE ())).run s =
      .ok (.E_SAMO_Page_Fault ()) s ∧
    (translationException (.StoreConditional (aq, rl, .Data)) (.PTW_No_Access ())).run s =
      .ok (.E_SAMO_Access_Fault ()) s ∧
    (translationException (.StoreConditional (aq, rl, .Data)) (.PTW_No_Permission ())).run s =
      .ok (.E_SAMO_Page_Fault ()) s ∧
    (translationException (.Atomic (op, aq, rl, .Data, .Data)) (.PTW_No_Access ())).run s =
      .ok (.E_SAMO_Access_Fault ()) s ∧
    (translationException (.Atomic (op, aq, rl, .Data, .Data)) (.PTW_PTE_Needs_Update ())).run s =
      .ok (.E_SAMO_Page_Fault ()) s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `Sv39` / `Sv48` TLB entry matching (`match_TLB_Entry`), superpage PPN reconstruction
    (`tlb_get_ppn` with `levelMask`), and `SFENCE.VMA` selective/full invalidation predicate
    (`flush_TLB_Entry` in `VmemTlb.lean`, lines 232–289): proves `global = true` entries match any
    `ASID` and survive ASID-scoped flushes (`flush_TLB_Entry ent (some asid) none = false`), whereas
    `SFENCE.VMA x0, x0` (`asid = none, vaddr = none`) flushes every TLB entry including global ones,
    and 4 KiB (`levelMask = 0`) pages return `ent.ppn` directly. -/
theorem rv64TlbMatchPpnAndSfence_bisim_sail (asid other_asid : BitVec 16) (vpn39 : BitVec 27)
    (ppn : BitVec 44) (pte : BitVec 64) (pa : physaddr) :
    let entGlobal : TLB_Entry :=
      { asid := asid, global := true, pte := pte, pteAddr := pa,
        levelMask := 0#45, vpn := sign_extend (m := 45) vpn39, ppn := ppn }
    let entLocal : TLB_Entry :=
      { asid := asid, global := false, pte := pte, pteAddr := pa,
        levelMask := 0#45, vpn := sign_extend (m := 45) vpn39, ppn := ppn }
    match_TLB_Entry entGlobal other_asid (sign_extend (m := 45) vpn39) = true ∧
    match_TLB_Entry entLocal other_asid (sign_extend (m := 45) vpn39) = (asid == other_asid) ∧
    tlb_get_ppn 39 entLocal vpn39 = ppn ∧
    flush_TLB_Entry entGlobal none none = true ∧
    flush_TLB_Entry entLocal none none = true ∧
    flush_TLB_Entry entGlobal (some asid) none = false ∧
    flush_TLB_Entry entLocal (some other_asid) none = (asid == other_asid) := by
  dsimp only
  have hones45 : (Complement.complement (0#45)) = BitVec.allOnes 45 := by decide
  have hppn : tlb_get_ppn 39
      { asid := asid, global := false, pte := pte, pteAddr := pa,
        levelMask := 0#45, vpn := sign_extend (m := 45) vpn39, ppn := ppn } vpn39 = ppn := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have hk' : k < 44 := by simpa using hk
    unfold tlb_get_ppn trunc Sail.BitVec.truncate zero_extend Sail.BitVec.zeroExtend
    dsimp only
    change (BitVec.truncate 44 (BitVec.zeroExtend 64 ppn ||| (sign_extend (m := 64) vpn39 &&& 0#64))).getLsbD k =
      ppn.getLsbD k
    simp [hk']
  refine ⟨?_, ?_, hppn, rfl, rfl, ?_, ?_⟩
  · unfold match_TLB_Entry
    dsimp only
    rw [hones45, BitVec.and_allOnes]
    simp
  · unfold match_TLB_Entry
    dsimp only
    rw [hones45, BitVec.and_allOnes]
    simp only [Bool.false_or, beq_self_eq_true, Bool.and_true]
    rfl
  · unfold flush_TLB_Entry LeanRV64D.Functions.not
    simp
  · unfold flush_TLB_Entry LeanRV64D.Functions.not
    simp only [Bool.not_false, Bool.and_true]
    rfl

/-- Direct `SailM` bisimulation for `execute_SFENCE_VMA` (`InstsEnd.lean`, lines 67724–67749) and
    `reset_TLB` / `add_to_TLB` / `lookup_TLB` (`VmemTlb.lean`, lines 266–329): proves `User`-mode and
    `mstatus.TVM = 1` `Supervisor`-mode `SFENCE.VMA` trap with `Illegal_Instruction ()`, while
    adding an `Sv39` 4 KiB entry (`level = 0`) to a freshly reset TLB hits on `lookup_TLB 39` at
    `tlb_hash 39 vpn` in `SailM`. -/
def sailSfenceVmaPrivCheckExec (rs1 rs2 : regidx) : SailM ExecutionResult := do
  let addr ← if bne rs1 zreg then pure (some (← rX_bits rs1)) else pure none
  let asid ← if bne rs2 zreg then pure (some (Sail.BitVec.extractLsb (← rX_bits rs2) (Functions.asidlen -i 1) 0)) else pure none
  match ← readReg .cur_privilege with
  | .User => pure (.Illegal_Instruction ())
  | .Supervisor =>
    match _get_Mstatus_TVM (← readReg .mstatus) with
    | 1 => pure (.Illegal_Instruction ())
    | _ => do flush_TLB asid addr; pure (.Retire_Success ())
  | .Machine => do flush_TLB asid addr; pure (.Retire_Success ())
  | .VirtualUser => pure (.Virtual_Instruction ())
  | .VirtualSupervisor => internal_error "extensions/I/base_insts.sail" 692 "Hypervisor extension not supported"

theorem rv64SfenceVmaAndTlbLookup_bisim_sail (asid : BitVec 16) (vpn : BitVec 27)
    (ppn : BitVec 44) (pte : BitVec 64) (pa : physaddr)
    (sU sTvm sM : SequentialState RegisterType trivialChoiceSource)
    (hprivU : sU.regs.get? .cur_privilege = some .User)
    (hprivS : sTvm.regs.get? .cur_privilege = some .Supervisor)
    (hmstatusTvm : sTvm.regs.get? .mstatus = some (1#64 <<< 20)) :
    (sailSfenceVmaPrivCheckExec zreg zreg).run sU = .ok (.Illegal_Instruction ()) sU ∧
    (sailSfenceVmaPrivCheckExec zreg zreg).run sTvm = .ok (.Illegal_Instruction ()) sTvm ∧
    (match ((do
        reset_TLB ()
        add_to_TLB 39 asid vpn ppn pte pa 0 false
        let hit ← lookup_TLB 39 asid vpn
        pure hit.isSome).run sM) with
      | .ok b _ => b
      | .error _ _ => false) = true := by
  refine ⟨?_, ?_, ?_⟩
  · unfold sailSfenceVmaPrivCheckExec
    have hbne : bne zreg zreg = false := rfl
    rw [hbne]
    simp [readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
    dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.get, EStateM.pure, EStateM.run]
    rw [hprivU]; rfl
  · unfold sailSfenceVmaPrivCheckExec
    have hbne : bne zreg zreg = false := rfl
    rw [hbne]
    simp only [readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
    dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.get, EStateM.pure, EStateM.run]
    rw [hprivS]; dsimp [EStateM.bind, EStateM.get, EStateM.pure]
    rw [hmstatusTvm]; dsimp [EStateM.bind, EStateM.pure]
    rfl
  · have hidx : tlb_hash 39 vpn < 64 := by
      unfold tlb_hash Functions.num_tlb_entries_exp Sail.BitVec.toNatInt Sail.BitVec.extractLsb
      exact (BitVec.extractLsb 5 0 vpn).isLt
    have hvec : ∀ (e : TLB_Entry),
        ((vectorUpdate (vectorInit (n := 64) (none : Option TLB_Entry)) (tlb_hash 39 vpn) (some e))[tlb_hash 39 vpn]!) =
        some e := by
      intro e
      unfold vectorUpdate vectorInit Vector.set!
      simp [GetElem?.getElem!, decidableGetElem?, hidx]
    unfold reset_TLB add_to_TLB lookup_TLB
    simp [writeReg, PreSail.writeReg, readReg, PreSail.readReg,
      modify, modifyGet, MonadStateOf.modifyGet, get, getThe, MonadStateOf.get,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.get,
      EStateM.modifyGet, EStateM.pure, EStateM.run, hvec, match_TLB_Entry]
    rw [if_pos ?_]
    · rfl
    · apply BitVec.eq_of_getLsbD_eq
      intro k hk
      have hk45 : k < 45 := by simpa using hk
      unfold zero_extend sign_extend Sail.BitVec.zeroExtend Sail.BitVec.signExtend ones sail_ones
      simp [hk45]

/-! ## Section 14: PMP/PMA Checks, PTE Read/Write/Update, Multi-Level `Sv39`/`Sv48` Page-Table Walk, TLB Hit/Miss & `translateAddr` -/

def rv64DefaultRamPma : PMA :=
  { mem_type := .MainMemory
    cacheable := true
    coherent := true
    executable := true
    readable := true
    writable := true
    read_idempotent := true
    write_idempotent := true
    misaligned_exceptions :=
      { load_store := none
        vector := none
        amo := .AlignmentException }
    atomic_support := .AMOCASD
    reservability := .RsrvEventual
    supports_cbo_zero := true
    supports_pte_read := true
    supports_pte_write := true
    misaligned_atomicity_granule_size_exp := 0
    vector_misaligned_atomicity_granule_size_exp := 0 }

def rv64HighRamRegion : PMA_Region :=
  { base := 0x80000000#64
    size := 0x80000000#64
    attributes := rv64DefaultRamPma
    include_in_device_tree := true }

def rv64StandardPtwRegs (s : SequentialState RegisterType trivialChoiceSource)
    (adue : BitVec 1) : Prop :=
  s.regs.get? .pma_regions = some [rv64HighRamRegion] ∧
  s.regs.get? .pmpcfg_n =
    some (vectorUpdate (vectorInit (n := 64) 0#8) 0 0b00011111#8) ∧
  s.regs.get? .pmpaddr_n =
    some (vectorUpdate (vectorInit (n := 64) 0#64) 0 (BitVec.allOnes 64)) ∧
  s.regs.get? .htif_tohost_base = some none ∧
  s.regs.get? .misa = some ((0b10#64 <<< 62) ||| (1#64 <<< 18) ||| (1#64 <<< 20)) ∧
  s.regs.get? .menvcfg = some (if adue == 1#1 then (1#64 <<< 61) else 0#64)

private theorem matching_pma_high_ram_eight (paddr : BitVec 64)
    (hlo : 0x80000000 ≤ paddr.toNat) (hhi : paddr.toNat + 8 ≤ 0x100000000) :
    matching_pma_region [rv64HighRamRegion] (.Physaddr paddr) 8 = some rv64HighRamRegion := by
  have hr : range_subset paddr 8#64 0x80000000#64 0x80000000#64 = true := by
    unfold range_subset zopz0zIzJ_u Sail.BitVec.toNatInt
    have hsub1 : (paddr - 0x80000000#64).toNat = paddr.toNat - 0x80000000 := by
      rw [BitVec.toNat_sub_of_le]
      · simp
      · rw [BitVec.le_def]; simpa using hlo
    have hsub2 : (paddr + 8#64 - 0x80000000#64).toNat = paddr.toNat + 8 - 0x80000000 := by
      have hpadd : (paddr + 8#64).toNat = paddr.toNat + 8 := by
        rw [BitVec.toNat_add]
        simp only [BitVec.toNat_ofNat]
        omega
      rw [BitVec.toNat_sub_of_le]
      · simp [hpadd]
      · rw [BitVec.le_def, hpadd]; simp; omega
    have hb : (0x80000000#64 + 0x80000000#64 - 0x80000000#64 : BitVec 64).toNat = 0x80000000 := by decide
    simp only [Int.ofNat_eq_natCast, Bool.and_eq_true, decide_eq_true_eq, hsub1, hsub2, hb]
    omega
  unfold matching_pma_region matching_pma_region_bits_range bits_of_physaddr rv64HighRamRegion
    zero_extend Sail.BitVec.zeroExtend
  dsimp only [BitVec.zeroExtend]
  have htb : to_bits (l := 64) 8 = 8#64 := by decide
  rw [if_pos (by simpa [BitVec.setWidth_eq, htb] using hr)]

private theorem pmpCheck_high_ram_supervisor (paddr : BitVec 64) (width : Nat)
    (hw : width = 8) (hhi : paddr.toNat + 8 ≤ 0x100000000)
    (access : MemoryAccessType mem_payload)
    (hacc : access = .Load .PageTableEntry ∨ access = .Store .PageTableEntry)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hpmpcfg : s.regs.get? .pmpcfg_n =
      some (vectorUpdate (vectorInit (n := 64) 0#8) 0 0b00011111#8))
    (hpmpaddr : s.regs.get? .pmpaddr_n =
      some (vectorUpdate (vectorInit (n := 64) 0#64) 0 (BitVec.allOnes 64))) :
    (pmpCheck (.Physaddr paddr) width access .Supervisor).run s = .ok none s := by
  subst hw
  have hcfg0 : (vectorUpdate (vectorInit (n := 64) 0#8) 0 0b00011111#8)[0]! = 0b00011111#8 := by decide
  have haddr0 : (vectorUpdate (vectorInit (n := 64) 0#64) 0 (BitVec.allOnes 64))[0]! = BitVec.allOnes 64 := by decide
  have hmatch : (pmpMatchAddr (.Physaddr paddr) 8#64 0b00011111#8 (BitVec.allOnes 64) 0#64).run s =
      .ok .PMP_Match s := by
    unfold pmpMatchAddr
    have hmtype : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A 0b00011111#8) = .NAPOT := rfl
    rw [hmtype]
    dsimp only [Pure.pure, EStateM.pure, EStateM.run]
    have hbegNat : (BitVec.toNatInt
        (BitVec.allOnes 64 &&& Complement.complement (BitVec.allOnes 64 ^^^ BitVec.addInt (BitVec.allOnes 64) 1)) * 4).toNat = 0 := by decide
    have hendNat : ((BitVec.toNatInt
        (BitVec.allOnes 64 &&& Complement.complement (BitVec.allOnes 64 ^^^ BitVec.addInt (BitVec.allOnes 64) 1)) +
          BitVec.toNatInt (BitVec.allOnes 64 ^^^ BitVec.addInt (BitVec.allOnes 64) 1) + 1) * 4).toNat = 73786976294838206464 := by decide
    have hwNat : (BitVec.toNatInt 8#64).toNat = 8 := by decide
    rw [hbegNat, hendNat, hwNat]
    unfold pmpRangeMatch
    congr 1
    simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast]
    have hhiPhys : (CoeT.coe paddr : physaddrbits).toNat + 8 ≤ 0x100000000 := by
      dsimp only [CoeT.coe]
      have hw64 : 2 ^ (if decide (64 = 32) = true then 34 else 64) = 2 ^ 64 := rfl
      rw [BitVec.toNat_setWidth, hw64, Nat.mod_eq_of_lt paddr.isLt]
      exact hhi
    have hcPow : (2 ^ if decide (64 = 32) = true then 34 else 64) = 18446744073709551616 := by decide
    rw [if_neg (by
          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]
          omega),
        if_pos (by
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          omega)]
  have hrwx : (pmpCheckRWX 0b00011111#8 access).run s = .ok true s := by
    rcases hacc with rfl | rfl <;> rfl
  unfold pmpCheck sys_pmp_count pmpReadAddrReg sys_pmp_grain
  have hsc0 : ((16 : Int) == 0) = false := by decide
  rw [if_neg (by simp [hsc0])]
  dsimp only
  have htb8 : to_bits (l := 64) 8 = 8#64 := by decide
  rw [htb8]
  dsimp only [ForIn.forIn, ForIn'.forIn', IntRange.forIn']
  unfold IntRange.forIn'.loop
  simp only [Membership.mem]
  have hmem0 : (if (1 : Int) > 0 then (0 : Int) ≤ 0 ∧ (0 : Int) ≤ (16 : Int) -i 1 else (16 : Int) -i 1 ≤ 0 ∧ (0 : Int) ≤ 0) ∧
      ((0 : Int) - 0) % 1 = 0 := by decide
  rw [dif_pos hmem0]
  rw [if_neg (by decide)]
  dsimp only [SailME.run, PreSail.PreSailME.run, SailME.throw, PreSail.PreSailME.throw,
    MonadExceptOf.throw, MonadExcept.throw, ExceptT.run, ExceptT.mk,
    ExceptT.bind, ExceptT.pure, ExceptT.lift, ExceptT.bindCont,
    MonadLift.monadLift, liftM, monadLift, Functor.map, EStateM.map,
    Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
    readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
  rw [hpmpcfg]
  dsimp only [EStateM.pure, EStateM.bind, EStateM.map, EStateM.get, ExceptT.bindCont]
  rw [hpmpcfg]
  dsimp only [EStateM.pure, EStateM.bind, EStateM.get]
  rw [hpmpaddr]
  dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
  have hi0 : Int.toNat 0 = 0 := rfl
  have hget0 : (vectorUpdate (vectorInit (n := 64) 0#8) 0 0b00011111#8)[(0 : Int)]! = 0b00011111#8 := hcfg0
  simp only [hi0, hcfg0, haddr0, hget0]
  have hb1 : BitVec.access (_get_Pmpcfg_ent_A 0b00011111#8) 1 = 1#1 := by decide
  have hz64 : zeros (n := 64) = 0#64 := rfl
  have hge2 : ((0 : Nat) ≥b 2) = false := by decide
  rw [hb1, hz64, hge2, if_neg (by decide)]
  simp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
  dsimp only [EStateM.run] at hmatch hrwx
  rw [hmatch]
  dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
  rw [hrwx]
  rfl

private theorem within_mmio_high_ram_width_false (paddr : BitVec 64) (width : Nat)
    (hlo : 0x80000000 ≤ paddr.toNat)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hhtif : s.regs.get? .htif_tohost_base = some none) :
    (within_clint (.Physaddr paddr) width).run s = .ok false s ∧
    (within_sig (.Physaddr paddr) width).run s = .ok false s ∧
    (within_htif_writable (.Physaddr paddr) width).run s = .ok false s ∧
    (within_mmio_readable (.Physaddr paddr) width).run s = .ok false s ∧
    (within_mmio_writable (.Physaddr paddr) width).run s = .ok false s := by
  have hp : BitVec.toNatInt ((physaddr.Physaddr paddr).1) = (paddr.toNat : Int) := rfl
  have hclint : (within_clint (.Physaddr paddr) width).run s = .ok false s := by
    unfold within_clint plat_have_clint LeanRV64D.Functions.not
    have hcb : BitVec.toNatInt plat_clint_base = 33554432 := by decide
    have hcs : BitVec.toNatInt plat_clint_size = 786432 := by decide
    dsimp only [Pure.pure, EStateM.pure, EStateM.run]
    rw [if_neg (by decide), hcb, hcs, hp]; congr 1
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; right; omega
  have hsig : (within_sig (.Physaddr paddr) width).run s = .ok false s := by
    unfold within_sig plat_have_sig LeanRV64D.Functions.not
    have hsb : BitVec.toNatInt plat_sig_base = 201326592 := by decide
    have hss : BitVec.toNatInt plat_sig_size = 32 := by decide
    dsimp only [Pure.pure, EStateM.pure, EStateM.run]
    rw [if_neg (by decide), hsb, hss, hp]; congr 1
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; right; omega
  have hhtif_w : (within_htif_writable (.Physaddr paddr) width).run s = .ok false s := by
    unfold within_htif_writable
    simp [readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
    dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.get, EStateM.pure, EStateM.run]
    rw [hhtif]; rfl
  refine ⟨hclint, hsig, hhtif_w, ?_, ?_⟩
  · unfold within_mmio_readable within_htif_readable get_config_rvfi
    dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at hclint hsig hhtif_w ⊢
    rw [hclint]; dsimp only; rw [hsig]; dsimp only; rw [hhtif_w]; rfl
  · unfold within_mmio_writable get_config_rvfi
    dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at hclint hsig hhtif_w ⊢
    rw [hclint]; dsimp only; rw [hsig]; dsimp only; rw [hhtif_w]; rfl

private theorem within_mmio_high_ram_false (paddr : BitVec 64)
    (hlo : 0x80000000 ≤ paddr.toNat)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hhtif : s.regs.get? .htif_tohost_base = some none) :
    (within_mmio_readable (.Physaddr paddr) 8).run s = .ok false s ∧
    (within_mmio_writable (.Physaddr paddr) 8).run s = .ok false s :=
  let ⟨_, _, _, hr, hw⟩ := within_mmio_high_ram_width_false paddr 8 hlo s hhtif; ⟨hr, hw⟩

theorem rv64PmpAndPmaCheck_bisim_sail (paddr : BitVec 64) (adue : BitVec 1)
    (hlo : 0x80000000 ≤ paddr.toNat) (hhi : paddr.toNat + 8 ≤ 0x100000000)
    (halign : paddr.toNat % 8 = 0)
    (s sEmpty : SequentialState RegisterType trivialChoiceSource)
    (hstd : rv64StandardPtwRegs s adue)
    (hempty : sEmpty.regs.get? .pma_regions = some []) :
    pmpRangeMatch 0x80000000 0x80001000 0x80000000 8 = .PMP_Match ∧
    pmpRangeMatch 0x80000000 0x80001000 0x80000ffc 8 = .PMP_PartialMatch ∧
    pmpRangeMatch 0x80000000 0x80001000 0x80001000 8 = .PMP_NoMatch ∧
    (pmaCheck (.Physaddr paddr) 8 (.Load .PageTableEntry) .PBMT_PMA false).run sEmpty =
      .ok (.Err (.E_Load_Access_Fault ())) sEmpty ∧
    (phys_access_check (.Load .PageTableEntry) .PBMT_PMA .Supervisor (.Physaddr paddr) 8 false).run s =
      .ok (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }) s ∧
    (check_pma_with_pmp_priority (.Store .PageTableEntry) .PBMT_PMA .Supervisor (.Physaddr paddr) 8 false).run s =
      .ok (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }) s := by
  rcases hstd with ⟨hpma, hpmpcfg, hpmpaddr, _, _, _⟩
  have hpmaMatch := matching_pma_high_ram_eight paddr hlo hhi
  have hal : is_aligned_paddr (.Physaddr paddr) 8 = true := by
    unfold is_aligned_paddr Sail.BitVec.toNatInt
    rw [beq_iff_eq]
    have hdiv : (paddr.toNat : Int) % 8 = 0 := by omega
    simpa [Int.tmod_eq_emod_of_nonneg (Int.natCast_nonneg _)] using hdiv
  have hpmaLoad : (pmaCheck (.Physaddr paddr) 8 (.Load .PageTableEntry) .PBMT_PMA false).run s =
      .ok (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }) s := by
    unfold pmaCheck mag_pma_check is_mag_applicable_access override_PMA LeanRV64D.Functions.not
    dsimp only [SailME.run, PreSail.PreSailME.run, SailME.throw, PreSail.PreSailME.throw,
      MonadExceptOf.throw, MonadExcept.throw, ExceptT.run, ExceptT.mk,
      ExceptT.bind, ExceptT.pure, ExceptT.lift, ExceptT.bindCont,
      MonadLift.monadLift, liftM, monadLift, Functor.map, EStateM.map,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.get, EStateM.pure, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get, assert, PreSail.assert]
    rw [hpma]
    dsimp only [EStateM.pure]
    rw [hpmaMatch]
    dsimp only [rv64HighRamRegion, rv64DefaultRamPma, EStateM.pure, EStateM.bind, ExceptT.bindCont, Bool.not_false, Bool.not_true]
    rw [hal]
    rfl
  have hpmaStore : (pmaCheck (.Physaddr paddr) 8 (.Store .PageTableEntry) .PBMT_PMA false).run s =
      .ok (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }) s := by
    unfold pmaCheck mag_pma_check is_mag_applicable_access override_PMA LeanRV64D.Functions.not
    dsimp only [SailME.run, PreSail.PreSailME.run, SailME.throw, PreSail.PreSailME.throw,
      MonadExceptOf.throw, MonadExcept.throw, ExceptT.run, ExceptT.mk,
      ExceptT.bind, ExceptT.pure, ExceptT.lift, ExceptT.bindCont,
      MonadLift.monadLift, liftM, monadLift, Functor.map, EStateM.map,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.get, EStateM.pure, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get, assert, PreSail.assert]
    rw [hpma]
    dsimp only [EStateM.pure]
    rw [hpmaMatch]
    dsimp only [rv64HighRamRegion, rv64DefaultRamPma, EStateM.pure, EStateM.bind, ExceptT.bindCont, Bool.not_false, Bool.not_true]
    rw [hal]
    rfl
  have hr1 : pmpRangeMatch 0x80000000 0x80001000 0x80000000 8 = .PMP_Match := rfl
  have hr2 : pmpRangeMatch 0x80000000 0x80001000 0x80000ffc 8 = .PMP_PartialMatch := rfl
  have hr3 : pmpRangeMatch 0x80000000 0x80001000 0x80001000 8 = .PMP_NoMatch := rfl
  refine ⟨hr1, hr2, hr3, ?_, ?_, ?_⟩
  · unfold pmaCheck matching_pma_region matching_pma_region_bits_range accessFaultFromAccessType
    dsimp only [SailME.run, PreSail.PreSailME.run, SailME.throw, PreSail.PreSailME.throw,
      MonadExceptOf.throw, MonadExcept.throw, ExceptT.run, ExceptT.mk,
      ExceptT.bind, ExceptT.pure, ExceptT.lift, ExceptT.bindCont,
      MonadLift.monadLift, liftM, monadLift, Functor.map, EStateM.map,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.get, EStateM.pure, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
    rw [hempty]
    rfl
  · have hpmp := pmpCheck_high_ram_supervisor paddr 8 rfl hhi (.Load .PageTableEntry) (.inl rfl) s hpmpcfg hpmpaddr
    unfold phys_access_check
    dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at hpmp hpmaLoad ⊢
    rw [hpmp]; dsimp only; exact hpmaLoad
  · unfold check_pma_with_pmp_priority
    dsimp [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at hpmaStore ⊢
    rw [hpmaStore]; rfl

private theorem currentlyEnabled_ptw_std_run (adue : BitVec 1)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hstd : rv64StandardPtwRegs s adue) :
    (currentlyEnabled .Ext_Svadu).run s = .ok true s ∧
    (currentlyEnabled .Ext_Svade).run s = .ok true s ∧
    (currentlyEnabled .Ext_Svpbmt).run s = .ok true s ∧
    (currentlyEnabled .Ext_Svnapot).run s = .ok true s ∧
    (currentlyEnabled .Ext_Svrsw60t59b).run s = .ok true s := by
  rcases hstd with ⟨_, _, _, _, hmisa, _⟩
  have hzicsr : (currentlyEnabled .Ext_Zicsr).run s = .ok true s := by
    unfold currentlyEnabled hartSupports; rfl
  have hs : (currentlyEnabled .Ext_S).run s = .ok true s := by
    unfold currentlyEnabled hartSupports
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get,
      EStateM.run, readReg, PreSail.readReg, get, getThe, MonadStateOf.get, Bool.true_and]
    rw [hmisa]
    dsimp only [EStateM.pure]
    dsimp only [EStateM.run] at hzicsr
    rw [hzicsr]
    have hmS : (_get_Misa_S ((0b10#64 <<< 62) ||| (1#64 <<< 18) ||| (1#64 <<< 20)) == 1#1) = true := by decide
    rw [hmS]; rfl
  have hsv39 : (currentlyEnabled .Ext_Sv39).run s = .ok true s := by
    unfold currentlyEnabled hartSupports
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run, Bool.true_and]
    dsimp only [EStateM.run] at hs
    rw [hs]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold currentlyEnabled hartSupports; rfl
  · unfold currentlyEnabled hartSupports; rfl
  · unfold currentlyEnabled hartSupports
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run, Bool.true_and]
    dsimp only [EStateM.run] at hsv39; rw [hsv39]; rfl
  · unfold currentlyEnabled hartSupports
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run, Bool.true_and]
    dsimp only [EStateM.run] at hsv39; rw [hsv39]; rfl
  · unfold currentlyEnabled hartSupports
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run, Bool.true_and]
    dsimp only [EStateM.run] at hsv39; rw [hsv39]; rfl

private theorem write_pte_std_run (paddr : BitVec 64) (pte : BitVec 64) (adue : BitVec 1)
    (hlo : 0x80000000 ≤ paddr.toNat) (hhi : paddr.toNat + 8 ≤ 0x100000000)
    (halign : paddr.toNat % 8 = 0)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hstd : rv64StandardPtwRegs s adue) :
    (write_pte (.Physaddr paddr) 8 pte).run s =
      .ok (.Ok true) { s with mem := rv64WriteMemBytesSpec 8 paddr.toNat pte s.mem } := by
  rcases hstd with ⟨hpma, hpmpcfg, hpmpaddr, hhtif, _, _⟩
  have hpmaMatch := matching_pma_high_ram_eight paddr hlo hhi
  have hal : is_aligned_paddr (.Physaddr paddr) 8 = true := by
    unfold is_aligned_paddr Sail.BitVec.toNatInt
    rw [beq_iff_eq]
    have hdiv : (paddr.toNat : Int) % 8 = 0 := by omega
    simpa [Int.tmod_eq_emod_of_nonneg (Int.natCast_nonneg _)] using hdiv
  have hmmio := within_mmio_high_ram_false paddr hlo s hhtif
  have hpmaStore : (check_pma_with_pmp_priority (.Store .PageTableEntry) .PBMT_PMA .Supervisor (.Physaddr paddr) 8 false).run s =
      .ok (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }) s := by
    unfold check_pma_with_pmp_priority pmaCheck mag_pma_check is_mag_applicable_access override_PMA LeanRV64D.Functions.not
    dsimp only [SailME.run, PreSail.PreSailME.run, SailME.throw, PreSail.PreSailME.throw,
      MonadExceptOf.throw, MonadExcept.throw, ExceptT.run, ExceptT.mk,
      ExceptT.bind, ExceptT.pure, ExceptT.lift, ExceptT.bindCont,
      MonadLift.monadLift, liftM, monadLift, Functor.map, EStateM.map,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.get, EStateM.pure, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get, assert, PreSail.assert]
    rw [hpma]
    dsimp only [EStateM.pure]
    rw [hpmaMatch]
    dsimp only [rv64HighRamRegion, rv64DefaultRamPma, EStateM.pure, EStateM.bind, ExceptT.bindCont, Bool.not_false, Bool.not_true]
    rw [hal]; rfl
  have hsplit : (split_misaligned (.Physaddr paddr) 8 0 .CannotSplit).run s = .ok (1, 8) s := by
    unfold split_misaligned
    dsimp [Pure.pure, EStateM.pure, EStateM.run]
    rfl
  have hpmpStore := pmpCheck_high_ram_supervisor paddr 8 rfl hhi (.Store .PageTableEntry) (.inr rfl) s hpmpcfg hpmpaddr
  have hramWrite := write_ram_plain_bisim_sail 8 paddr pte s
  have hpadd0 : physaddr.Physaddr (@BitVec.addInt (if decide (64 = 32) = true then 34 else 64) paddr 0) = physaddr.Physaddr paddr := by
    unfold Sail.BitVec.addInt
    congr 1
    exact BitVec.add_zero paddr
  unfold write_pte mem_write_value_priv mem_write_value_priv_meta checked_mem_write
    misaligned_order sys_misaligned_order_decreasing write_kind_of_flags bits_of_physaddr
    untilFuelM untilFuelM.go mem_write_callback default_meta
  dsimp only [SailME.run, PreSail.PreSailME.run, SailME.throw, PreSail.PreSailME.throw,
    MonadExceptOf.throw, MonadExcept.throw, ExceptT.run, ExceptT.mk,
    ExceptT.bind, ExceptT.pure, ExceptT.lift, ExceptT.bindCont,
    MonadLift.monadLift, liftM, monadLift, Functor.map, EStateM.map,
    Bind.bind, Pure.pure, EStateM.bind, EStateM.get, EStateM.pure, EStateM.run,
    assert, PreSail.assert]
  dsimp only [EStateM.run] at hpmaStore hsplit hpmpStore hmmio hramWrite
  rw [hpmaStore]
  dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
  rw [hsplit]
  have htoNat0 : Int.toNat 0 = 0 := rfl
  have htoNat1 : Int.toNat 1 = 1 := rfl
  have htoNat8 : Int.toNat 8 = 8 := rfl
  simp only [Bool.false_eq_true, ite_false, htoNat0, htoNat1, htoNat8, untilFuelM.go, if_true]
  dsimp only [ExceptT.bind, ExceptT.pure, ExceptT.lift, ExceptT.bindCont,
    EStateM.bind, EStateM.pure, EStateM.map, BitVec.setWidth_eq]
  have hmul0 : ((0 : Nat) : Int) * 8 = 0 := rfl
  rw [hmul0, hpadd0, hpmpStore]
  dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
  rw [hmmio.2]
  simp only [Bool.false_eq_true, ite_false]
  dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
  have hfst0 : (if false = true then ((1 : Int) - 1, (0 : Int), (-1 : Int)) else (0, 1 - 1, 1)).fst = 0 := rfl
  have hidxHi : (8 * (((0 : Nat) : Int) + 1) * 8 - 1).toNat = 63 := rfl
  have hidxLo : (8 * ((0 : Nat) : Int) * 8).toNat = 0 := rfl
  have hext : BitVec.setWidth (8 * 8)
      (Sail.BitVec.extractLsb (BitVec.setWidth (8 * 8) pte) 63 0) = pte := by
    unfold Sail.BitVec.extractLsb
    ext j hj
    simp [BitVec.extractLsb]
  rw [hfst0, htoNat0, hidxHi, hidxLo, htoNat8, hext, hramWrite]
  dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont, Bool.true_and]
  rfl

private theorem read_pte_std_run (paddr : BitVec 64) (pte : BitVec 64) (adue : BitVec 1)
    (hlo : 0x80000000 ≤ paddr.toNat) (hhi : paddr.toNat + 8 ≤ 0x100000000)
    (halign : paddr.toNat % 8 = 0)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hstd : rv64StandardPtwRegs s adue)
    (hmem : rv64ReadMemBytesSpec 8 paddr.toNat s.mem = some pte) :
    (read_pte (.Physaddr paddr) 8).run s = .ok (.Ok pte) s := by
  rcases hstd with ⟨hpma, hpmpcfg, hpmpaddr, hhtif, _, _⟩
  have hpmaMatch := matching_pma_high_ram_eight paddr hlo hhi
  have hal : is_aligned_paddr (.Physaddr paddr) 8 = true := by
    unfold is_aligned_paddr Sail.BitVec.toNatInt
    rw [beq_iff_eq]
    have hdiv : (paddr.toNat : Int) % 8 = 0 := by omega
    simpa [Int.tmod_eq_emod_of_nonneg (Int.natCast_nonneg _)] using hdiv
  have hmmio := within_mmio_high_ram_false paddr hlo s hhtif
  have hpmaLoad : (check_pma_with_pmp_priority (.Load .PageTableEntry) .PBMT_PMA .Supervisor (.Physaddr paddr) 8 false).run s =
      .ok (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }) s := by
    unfold check_pma_with_pmp_priority pmaCheck mag_pma_check is_mag_applicable_access override_PMA LeanRV64D.Functions.not
    dsimp only [SailME.run, PreSail.PreSailME.run, SailME.throw, PreSail.PreSailME.throw,
      MonadExceptOf.throw, MonadExcept.throw, ExceptT.run, ExceptT.mk,
      ExceptT.bind, ExceptT.pure, ExceptT.lift, ExceptT.bindCont,
      MonadLift.monadLift, liftM, monadLift, Functor.map, EStateM.map,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.get, EStateM.pure, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get, assert, PreSail.assert]
    rw [hpma]
    dsimp only [EStateM.pure]
    rw [hpmaMatch]
    dsimp only [rv64HighRamRegion, rv64DefaultRamPma, EStateM.pure, EStateM.bind, ExceptT.bindCont, Bool.not_false, Bool.not_true]
    rw [hal]; rfl
  have hsplit : (split_misaligned (.Physaddr paddr) 8 0 .CannotSplit).run s = .ok (1, 8) s := by
    unfold split_misaligned
    dsimp [Pure.pure, EStateM.pure, EStateM.run]
    rfl
  have hpmpLoad := pmpCheck_high_ram_supervisor paddr 8 rfl hhi (.Load .PageTableEntry) (.inl rfl) s hpmpcfg hpmpaddr
  have hramRead := read_ram_plain_bisim_sail 8 paddr pte s hmem
  have hpadd0 : physaddr.Physaddr (@BitVec.addInt (if decide (64 = 32) = true then 34 else 64) paddr 0) = physaddr.Physaddr paddr := by
    unfold Sail.BitVec.addInt
    congr 1
    exact BitVec.add_zero paddr
  unfold read_pte mem_read_priv mem_read_priv_meta checked_mem_read MemoryOpResult_drop_meta
    misaligned_order sys_misaligned_order_decreasing read_kind_of_flags bits_of_physaddr
    untilFuelM untilFuelM.go mem_read_callback default_meta
  dsimp only [SailME.run, PreSail.PreSailME.run, SailME.throw, PreSail.PreSailME.throw,
    MonadExceptOf.throw, MonadExcept.throw, ExceptT.run, ExceptT.mk,
    ExceptT.bind, ExceptT.pure, ExceptT.lift, ExceptT.bindCont,
    MonadLift.monadLift, liftM, monadLift, Functor.map, EStateM.map,
    Bind.bind, Pure.pure, EStateM.bind, EStateM.get, EStateM.pure, EStateM.run,
    assert, PreSail.assert]
  dsimp only [EStateM.run] at hpmaLoad hsplit hpmpLoad hmmio hramRead
  rw [hpmaLoad]
  dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
  rw [hsplit]
  have htoNat0 : Int.toNat 0 = 0 := rfl
  have htoNat1 : Int.toNat 1 = 1 := rfl
  have htoNat8 : Int.toNat 8 = 8 := rfl
  simp only [Bool.false_eq_true, ite_false, htoNat0, htoNat1, htoNat8, untilFuelM.go, if_true]
  dsimp only [ExceptT.bind, ExceptT.pure, ExceptT.lift, ExceptT.bindCont,
    EStateM.bind, EStateM.pure, EStateM.map, BitVec.setWidth_eq]
  have hmul0 : ((0 : Nat) : Int) * 8 = 0 := rfl
  rw [hmul0, hpadd0, hpmpLoad]
  dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
  rw [hmmio.1]
  simp only [Bool.false_eq_true, ite_false]
  dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
  have hfst0 : (if false = true then ((1 : Int) - 1, (0 : Int), (-1 : Int)) else (0, 1 - 1, 1)).fst = 0 := rfl
  have hsub0 : ((1 : Int) - 1).toNat = 0 := rfl
  have hidxHi : (8 * (((0 : Nat) : Int) + 1) * 8 - 1).toNat = 63 := rfl
  have hidxLo : (8 * ((0 : Nat) : Int) * 8).toNat = 0 := rfl
  have hw64 : (8 * 1 * 8 : Int).toNat = 64 := rfl
  rw [hfst0, htoNat0, htoNat8, hramRead]
  dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
  have heq0 : ((0 : Nat) == 0) = true := rfl
  rw [hsub0, heq0, if_pos rfl]
  dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
  have hupd : BitVec.setWidth 64
      (BitVec.updateSubrange (BitVec.setWidth 64 (zeros (n := 64)))
        63 0 (BitVec.setWidth (63 - 0 + 1) pte)) = pte := by
    unfold Sail.BitVec.updateSubrange Sail.BitVec.updateSubrange' zeros
    ext j hj
    simp
  rw [htoNat1, hw64, hidxHi, hidxLo, hupd]
  rfl

theorem rv64ReadWritePte_bisim_sail (paddr : BitVec 64) (pte : BitVec 64) (adue : BitVec 1)
    (hlo : 0x80000000 ≤ paddr.toNat) (hhi : paddr.toNat + 8 ≤ 0x100000000)
    (halign : paddr.toNat % 8 = 0)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hstd : rv64StandardPtwRegs s adue)
    (hmem : rv64ReadMemBytesSpec 8 paddr.toNat s.mem = some pte) :
    (read_pte (.Physaddr paddr) 8).run s = .ok (.Ok pte) s ∧
    (write_pte (.Physaddr paddr) 8 pte).run s =
      .ok (.Ok true) { s with mem := rv64WriteMemBytesSpec 8 paddr.toNat pte s.mem } :=
  ⟨read_pte_std_run paddr pte adue hlo hhi halign s hstd hmem,
   write_pte_std_run paddr pte adue hlo hhi halign s hstd⟩

theorem rv64UpdateAndWritePte_bisim_sail (paddr : BitVec 64)
    (hlo : 0x80000000 ≤ paddr.toNat) (hhi : paddr.toNat + 8 ≤ 0x100000000)
    (halign : paddr.toNat % 8 = 0)
    (s0 s1 : SequentialState RegisterType trivialChoiceSource)
    (hstd0 : rv64StandardPtwRegs s0 0#1)
    (hstd1 : rv64StandardPtwRegs s1 1#1) :
    (update_and_write_pte (.Physaddr paddr) 8 0x00000000200000c7#64 (.Store .Data)).run s0 =
      .ok (.Ok none) s0 ∧
    (update_and_write_pte (.Physaddr paddr) 8 0x0000000020000007#64 (.Store .Data)).run s0 =
      .ok (.Err (.PTW_PTE_Needs_Update ())) s0 ∧
    (update_and_write_pte (.Physaddr paddr) 8 0x0000000020000007#64 (.Store .Data)).run s1 =
      .ok (.Ok (some 0x00000000200000c7#64))
        { s1 with mem := rv64WriteMemBytesSpec 8 paddr.toNat 0x00000000200000c7#64 s1.mem } ∧
    (update_and_write_pte (.Physaddr paddr) 8 0x0000000020000007#64 (.Load .Data)).run s1 =
      .ok (.Ok (some 0x0000000020000047#64))
        { s1 with mem := rv64WriteMemBytesSpec 8 paddr.toNat 0x0000000020000047#64 s1.mem } := by
  have hc0 := (currentlyEnabled_ptw_std_run 0#1 s0 hstd0).1
  have hc0e := (currentlyEnabled_ptw_std_run 0#1 s0 hstd0).2.1
  have hc1 := (currentlyEnabled_ptw_std_run 1#1 s1 hstd1).1
  have hc1e := (currentlyEnabled_ptw_std_run 1#1 s1 hstd1).2.1
  have hm0 := hstd0.2.2.2.2.2
  have hm1 := hstd1.2.2.2.2.2
  have hu_none : update_PTE_Bits 0x00000000200000c7#64 (.Store .Data) = none := by decide
  have hu_store : update_PTE_Bits 0x0000000020000007#64 (.Store .Data) = some 0x00000000200000c7#64 := by decide
  have hu_load : update_PTE_Bits 0x0000000020000007#64 (.Load .Data) = some 0x0000000020000047#64 := by decide
  have hwStore := write_pte_std_run paddr 0x00000000200000c7#64 1#1 hlo hhi halign s1 hstd1
  have hwLoad := write_pte_std_run paddr 0x0000000020000047#64 1#1 hlo hhi halign s1 hstd1
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold update_and_write_pte
    rw [hu_none]; rfl
  · unfold update_and_write_pte LeanRV64D.Functions.not
    rw [hu_store]
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get] at hc0 hc0e ⊢
    rw [hc0]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.get]
    rw [hm0]
    dsimp only [EStateM.pure]
    rw [hc0]
    dsimp only
    rw [hc0e]
    have hadue0 : (_get_MEnvcfg_ADUE (if (0#1 == 1#1) = true then 1#64 <<< 61 else 0#64) == 1#1) = false := by decide
    rw [hadue0]
    rfl
  · unfold update_and_write_pte LeanRV64D.Functions.not
    rw [hu_store]
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get] at hc1 hc1e hwStore ⊢
    rw [hc1]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.get]
    rw [hm1]
    dsimp only [EStateM.pure]
    rw [hc1]
    dsimp only
    rw [hc1e]
    have hadue1 : (_get_MEnvcfg_ADUE (if (1#1 == 1#1) = true then 1#64 <<< 61 else 0#64) == 1#1) = true := by decide
    rw [hadue1]
    simp only [Bool.and_self, Bool.not_true, Bool.or_false, ite_true, EStateM.bind]
    rw [hwStore]; rfl
  · unfold update_and_write_pte LeanRV64D.Functions.not
    rw [hu_load]
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get] at hc1 hc1e hwLoad ⊢
    rw [hc1]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.get]
    rw [hm1]
    dsimp only [EStateM.pure]
    rw [hc1]
    dsimp only
    rw [hc1e]
    have hadue1 : (_get_MEnvcfg_ADUE (if (1#1 == 1#1) = true then 1#64 <<< 61 else 0#64) == 1#1) = true := by decide
    rw [hadue1]
    simp only [Bool.and_self, Bool.not_true, Bool.or_false, ite_true, EStateM.bind]
    rw [hwLoad]; rfl

private def pteIsInvalidStdSpec (pte_flags : BitVec 8) (pte_ext : BitVec 10) : Bool :=
  ((_get_PTE_Flags_V pte_flags) == 0#1) ||
    ((((_get_PTE_Flags_R pte_flags) == 0#1) &&
      (((_get_PTE_Flags_W pte_flags) == 1#1) &&
        (((_get_PTE_Flags_X pte_flags) == 0#1) && true))) ||
    ((((_get_PTE_Flags_R pte_flags) == 0#1) &&
      (((_get_PTE_Flags_W pte_flags) == 1#1) && ((_get_PTE_Flags_X pte_flags) == 1#1))) ||
    (((LeanRV64D.Functions.not (page_based_mem_type_forwards_matches (_get_PTE_Ext_PBMT pte_ext))) && true) ||
    (pte_reserved_bits_must_be_zero &&
      (((pte_is_non_leaf pte_flags) &&
        (((_get_PTE_Flags_A pte_flags) == 1#1) ||
          (((_get_PTE_Flags_D pte_flags) == 1#1) ||
            (((_get_PTE_Flags_U pte_flags) == 1#1) || (pte_ext != (zeros (n := 10))))))) ||
      ((((_get_PTE_Ext_N pte_ext) != (zeros (n := 1))) && (LeanRV64D.Functions.not true)) ||
        ((((_get_PTE_Ext_PBMT pte_ext) != (zeros (n := 2))) &&
          (true || (LeanRV64D.Functions.not (page_based_mem_type_forwards_matches (_get_PTE_Ext_PBMT pte_ext))))) ||
        ((((_get_PTE_Ext_RSW_60t59b pte_ext) != (zeros (n := 2))) && (LeanRV64D.Functions.not true)) ||
          ((_get_PTE_Ext_reserved pte_ext) != (zeros (n := 5)))))))))))

private theorem pte_is_invalid_std_run (pte_flags : BitVec 8) (pte_ext : BitVec 10) (adue : BitVec 1)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hstd : rv64StandardPtwRegs s adue) :
    (pte_is_invalid pte_flags pte_ext).run s = .ok (pteIsInvalidStdSpec pte_flags pte_ext) s := by
  have hce := currentlyEnabled_ptw_std_run adue s hstd
  rcases hce with ⟨_, _, hpbmt, hnapot, hrsw⟩
  have hm := hstd.2.2.2.2.2
  have hsse : (_get_MEnvcfg_SSE (if (adue == 1#1) = true then 1#64 <<< 61 else 0#64) == 0#1) = true := by
    cases (adue == 1#1) <;> decide
  have hpbmte : (_get_MEnvcfg_PBMTE (if (adue == 1#1) = true then 1#64 <<< 61 else 0#64) == 0#1) = true := by
    cases (adue == 1#1) <;> decide
  unfold pte_is_invalid pteIsInvalidStdSpec
  dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
    readReg, PreSail.readReg, get, getThe, MonadStateOf.get] at hpbmt hnapot hrsw ⊢
  rw [hm]
  dsimp only [EStateM.pure]
  rw [hpbmt]
  dsimp only
  rw [hnapot]
  dsimp only
  rw [hm]
  dsimp only [EStateM.pure]
  rw [hrsw]
  simp only [hsse, hpbmte]

private theorem read_pte_pow_std_run (sv_width : Nat) (hsv : sv_width = 39 ∨ sv_width = 48)
    (paddr : BitVec 64) (pte : BitVec 64) (adue : BitVec 1)
    (hlo : 0x80000000 ≤ paddr.toNat) (hhi : paddr.toNat + 8 ≤ 0x100000000)
    (halign : paddr.toNat % 8 = 0)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hstd : rv64StandardPtwRegs s adue)
    (hmem : rv64ReadMemBytesSpec 8 paddr.toNat s.mem = some pte) :
    (read_pte (.Physaddr paddr)
      (Int.toNat ((2 : Int) ^ (↑(if (sv_width == 32 : Bool) then (2 : Nat) else 3) : Int)))).run s =
      .ok (.Ok (@BitVec.setWidth 64
        (8 * Int.toNat ((2 : Int) ^ (↑(if (sv_width == 32 : Bool) then (2 : Nat) else 3) : Int))) pte)) s := by
  rcases hsv with rfl | rfl <;> exact read_pte_std_run paddr pte adue hlo hhi halign s hstd hmem

theorem pt_walk_nonleaf_step (sv_width : Nat) (hsv : sv_width = 39 ∨ sv_width = 48)
    (vpn : BitVec (sv_width - 12)) (access : MemoryAccessType mem_payload)
    (priv : Privilege) (mxr do_sum : Bool)
    (pt_base : BitVec (if (sv_width = 32 : Bool) then 22 else 44))
    (level : Nat) (hlev : (level >b 0) = true)
    (global : Bool) (paddr : BitVec 64) (pte : BitVec 64) (adue : BitVec 1)
    (hpaddr : zero_extend (m := 64)
      (pt_base +++ (Sail.BitVec.extractLsb vpn
        ((((level : Int) + 1) * (if (sv_width == 32 : Bool) then 10 else 9) - 1).toNat)
        (((level : Int) * (if (sv_width == 32 : Bool) then 10 else 9)).toNat) +++
        zeros (n := if (sv_width == 32 : Bool) then 2 else 3))) = paddr)
    (hlo : 0x80000000 ≤ paddr.toNat) (hhi : paddr.toNat + 8 ≤ 0x100000000)
    (halign : paddr.toNat % 8 = 0)
    (hinv : pteIsInvalidStdSpec (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0)) (ext_bits_of_PTE pte) = false)
    (hnonleaf : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0)) = true)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hstd : rv64StandardPtwRegs s adue)
    (hmem : rv64ReadMemBytesSpec 8 paddr.toNat s.mem = some pte) :
    (pt_walk sv_width vpn access priv mxr do_sum pt_base level global ()).run s =
      (pt_walk sv_width vpn access priv mxr do_sum
        (BitVec.setWidth (if (sv_width = 32 : Bool) then 22 else 44) (PPN_of_PTE pte))
        (level -i 1).toNat
        (global || (_get_PTE_Flags_G (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0)) == 1#1)) ()).run s := by
  have hread := read_pte_pow_std_run sv_width hsv paddr pte adue hlo hhi halign s hstd hmem
  have hinvRun := pte_is_invalid_std_run (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0)) (ext_bits_of_PTE pte) adue s hstd
  rw [hinv] at hinvRun
  rcases hsv with rfl | rfl
  · rw [pt_walk.eq_1]
    have hxlen : ((39 == 32 : Bool) || (LeanRV64D.Functions.xlen == 64)) = true := by decide
    have hfl : Sail.BitVec.extractLsb (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (39 == 32 : Bool) then (2 : Nat) else 3) : Int))) pte) 7 0 = Sail.BitVec.extractLsb pte 7 0 := rfl
    have hextb : ext_bits_of_PTE (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (39 == 32 : Bool) then (2 : Nat) else 3) : Int))) pte) = ext_bits_of_PTE pte := rfl
    have hppnb : @BitVec.setWidth _ (if decide (39 = 32) = true then 22 else 44)
        (PPN_of_PTE (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (39 == 32 : Bool) then (2 : Nat) else 3) : Int))) pte)) =
        @BitVec.setWidth _ (if decide (39 = 32) = true then 22 else 44) (PPN_of_PTE pte) := rfl
    dsimp only [ptw_start_callback, ptw_step_callback,
      SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.mk,
      ExceptT.bind, ExceptT.pure, ExceptT.lift, ExceptT.bindCont,
      MonadLift.monadLift, liftM, monadLift, Functor.map, EStateM.map,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run,
      assert, PreSail.assert]
    simp only [hxlen, ite_true]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    dsimp only [EStateM.run] at hread hinvRun ⊢
    rw [hpaddr, hread]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [hfl, hextb, hinvRun]
    simp only [Bool.false_eq_true, ite_false, hnonleaf, ite_true, hlev, hppnb]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    cases hrec : pt_walk 39 vpn access priv mxr do_sum
      (BitVec.setWidth (if decide (39 = 32) = true then 22 else 44) (PPN_of_PTE pte)) ((level : Int) - 1).toNat
      (global || (_get_PTE_Flags_G (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0)) == 1#1)) () s <;> rfl
  · rw [pt_walk.eq_1]
    have hxlen : ((48 == 32 : Bool) || (LeanRV64D.Functions.xlen == 64)) = true := by decide
    have hfl : Sail.BitVec.extractLsb (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (48 == 32 : Bool) then (2 : Nat) else 3) : Int))) pte) 7 0 = Sail.BitVec.extractLsb pte 7 0 := rfl
    have hextb : ext_bits_of_PTE (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (48 == 32 : Bool) then (2 : Nat) else 3) : Int))) pte) = ext_bits_of_PTE pte := rfl
    have hppnb : @BitVec.setWidth _ (if decide (48 = 32) = true then 22 else 44)
        (PPN_of_PTE (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (48 == 32 : Bool) then (2 : Nat) else 3) : Int))) pte)) =
        @BitVec.setWidth _ (if decide (48 = 32) = true then 22 else 44) (PPN_of_PTE pte) := rfl
    dsimp only [ptw_start_callback, ptw_step_callback,
      SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.mk,
      ExceptT.bind, ExceptT.pure, ExceptT.lift, ExceptT.bindCont,
      MonadLift.monadLift, liftM, monadLift, Functor.map, EStateM.map,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run,
      assert, PreSail.assert]
    simp only [hxlen, ite_true]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    dsimp only [EStateM.run] at hread hinvRun ⊢
    rw [hpaddr, hread]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [hfl, hextb, hinvRun]
    simp only [Bool.false_eq_true, ite_false, hnonleaf, ite_true, hlev, hppnb]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    cases hrec : pt_walk 48 vpn access priv mxr do_sum
      (BitVec.setWidth (if decide (48 = 32) = true then 22 else 44) (PPN_of_PTE pte)) ((level : Int) - 1).toNat
      (global || (_get_PTE_Flags_G (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0)) == 1#1)) () s <;> rfl

theorem pt_walk_leaf0_step (sv_width : Nat) (hsv : sv_width = 39 ∨ sv_width = 48)
    (vpn : BitVec (sv_width - 12)) (access : MemoryAccessType mem_payload)
    (priv : Privilege) (mxr do_sum : Bool)
    (pt_base : BitVec (if (sv_width = 32 : Bool) then 22 else 44))
    (global : Bool) (paddr : BitVec 64) (pte : BitVec 64) (adue : BitVec 1)
    (hpaddr : zero_extend (m := 64)
      (pt_base +++ (Sail.BitVec.extractLsb vpn
        (((((0 : Nat) : Int) + 1) * (if (sv_width == 32 : Bool) then 10 else 9) - 1).toNat)
        ((((0 : Nat) : Int) * (if (sv_width == 32 : Bool) then 10 else 9)).toNat) +++
        zeros (n := if (sv_width == 32 : Bool) then 2 else 3))) = paddr)
    (hlo : 0x80000000 ≤ paddr.toNat) (hhi : paddr.toNat + 8 ≤ 0x100000000)
    (halign : paddr.toNat % 8 = 0)
    (hinv : pteIsInvalidStdSpec (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0)) (ext_bits_of_PTE pte) = false)
    (hleaf : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0)) = false)
    (hn0 : (_get_PTE_Ext_N (ext_bits_of_PTE pte) == 1#1) = false)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hstd : rv64StandardPtwRegs s adue)
    (hmem : rv64ReadMemBytesSpec 8 paddr.toNat s.mem = some pte)
    (hperm : (check_PTE_permission access priv mxr do_sum (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0))
      (ext_bits_of_PTE pte) ()).run s = .ok (.PTE_Check_Success ()) s) :
    (pt_walk sv_width vpn access priv mxr do_sum pt_base 0 global ()).run s =
      .ok (.Ok ({
        ppn := BitVec.setWidth (if (sv_width = 32 : Bool) then 22 else 44) (PPN_of_PTE pte)
        pte := BitVec.setWidth (if (sv_width = 32 : Bool) then 32 else 64) pte
        pteAddr := .Physaddr paddr
        level := 0
        pbmt := .PBMT_PMA
        global := global || (_get_PTE_Flags_G (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0)) == 1#1)
      }, ())) s := by
  have hread := read_pte_pow_std_run sv_width hsv paddr pte adue hlo hhi halign s hstd hmem
  have hinvRun := pte_is_invalid_std_run (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0)) (ext_bits_of_PTE pte) adue s hstd
  rw [hinv] at hinvRun
  have hnapot := (currentlyEnabled_ptw_std_run adue s hstd).2.2.2.1
  have hm := hstd.2.2.2.2.2
  have hpbmte : (_get_MEnvcfg_PBMTE (if (adue == 1#1) = true then 1#64 <<< 61 else 0#64) == 0#1) = true := by
    cases (adue == 1#1) <;> decide
  have hlev0 : ¬ (((0 : Nat) >b 0) = true) := by decide
  rcases hsv with rfl | rfl
  · rw [pt_walk.eq_1]
    have hxlen : ((39 == 32 : Bool) || (LeanRV64D.Functions.xlen == 64)) = true := by decide
    have hfl : Sail.BitVec.extractLsb (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (39 == 32 : Bool) then (2 : Nat) else 3) : Int))) pte) 7 0 = Sail.BitVec.extractLsb pte 7 0 := rfl
    have hextb : ext_bits_of_PTE (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (39 == 32 : Bool) then (2 : Nat) else 3) : Int))) pte) = ext_bits_of_PTE pte := rfl
    have hppn_raw : PPN_of_PTE (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (39 == 32 : Bool) then (2 : Nat) else 3) : Int))) pte) =
        @BitVec.setWidth _ (if decide (8 * Int.toNat ((2 : Int) ^ (↑(if (39 == 32 : Bool) then (2 : Nat) else 3) : Int)) = 32) = true then 22 else 44) (PPN_of_PTE pte) := rfl
    have hpteb : @BitVec.setWidth (8 * Int.toNat ((2 : Int) ^ (↑(if (39 == 32 : Bool) then (2 : Nat) else 3) : Int))) (if decide (39 = 32) = true then 32 else 64) (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (39 == 32 : Bool) then (2 : Nat) else 3) : Int))) pte) = @BitVec.setWidth 64 (if decide (39 = 32) = true then 32 else 64) pte := rfl
    dsimp only [ptw_start_callback, ptw_step_callback, ptw_success_callback,
      SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.mk,
      ExceptT.bind, ExceptT.pure, ExceptT.lift, ExceptT.bindCont,
      MonadLift.monadLift, liftM, monadLift, Functor.map, EStateM.map,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get,
      assert, PreSail.assert]
    simp only [hxlen, ite_true]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    dsimp only [EStateM.run] at hread hinvRun hperm hnapot ⊢
    rw [hpaddr, hread]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [hfl, hextb, hinvRun]
    simp only [Bool.false_eq_true, ite_false, hleaf]
    rw [if_neg hlev0]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [hperm]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [if_neg hlev0]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [hnapot]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, EStateM.get, ExceptT.bindCont]
    simp only [hn0, Bool.and_false, Bool.false_eq_true, ite_false]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, EStateM.get, ExceptT.bindCont]
    rw [hm]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    simp only [hpbmte, ite_true, hpteb]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [hppn_raw]
    exact congrArg (fun p : BitVec (if decide (39 = 32) = true then 22 else 44) =>
      (EStateM.Result.ok (Ok ({
        ppn := p
        pte := @BitVec.setWidth 64 (if decide (39 = 32) = true then 32 else 64) pte
        pteAddr := .Physaddr paddr
        level := 0
        pbmt := .PBMT_PMA
        global := global || (_get_PTE_Flags_G (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0)) == 1#1)
      }, ())) s : EStateM.Result (Error exception) (SequentialState RegisterType trivialChoiceSource)
        (Result (PTW_Output 39 × Unit) (PTW_Error × Unit)))) (by
      have hlen1 : (if decide (8 * ((2 : Int) ^ (↑(if (39 == 32 : Bool) = true then (2 : Nat) else 3) : Int)).toNat = 32) = true then 22 else 44) = 44 := by decide
      have hlen2 : (if decide (39 = 32) = true then 22 else 44) = 44 := by decide
      ext j hj
      simp only [BitVec.getElem_setWidth, BitVec.getLsbD_setWidth]
      have hj44 : j < 44 := by omega
      have hjB : j < (if decide (8 * ((2 : Int) ^ (↑(if (39 == 32 : Bool) = true then (2 : Nat) else 3) : Int)).toNat = 32) = true then 22 else 44) := by omega
      rw [decide_eq_true hjB, Bool.true_and, Bool.and_eq_right_iff_imp]
      intro _
      simp only [Sail.BitVec.length, BitVec.length, decide_eq_true_eq]
      have hlenNat : (if 8 * ((2 : Int) ^ (↑(if (39 == 32 : Bool) = true then (2 : Nat) else 3) : Int)).toNat = 32 then (22 : Nat) else 44) = 44 := by decide
      rw [hlenNat]
      omega)
  · rw [pt_walk.eq_1]
    have hxlen : ((48 == 32 : Bool) || (LeanRV64D.Functions.xlen == 64)) = true := by decide
    have hfl : Sail.BitVec.extractLsb (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (48 == 32 : Bool) then (2 : Nat) else 3) : Int))) pte) 7 0 = Sail.BitVec.extractLsb pte 7 0 := rfl
    have hextb : ext_bits_of_PTE (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (48 == 32 : Bool) then (2 : Nat) else 3) : Int))) pte) = ext_bits_of_PTE pte := rfl
    have hppn_raw : PPN_of_PTE (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (48 == 32 : Bool) then (2 : Nat) else 3) : Int))) pte) =
        @BitVec.setWidth _ (if decide (8 * Int.toNat ((2 : Int) ^ (↑(if (48 == 32 : Bool) then (2 : Nat) else 3) : Int)) = 32) = true then 22 else 44) (PPN_of_PTE pte) := rfl
    have hpteb : @BitVec.setWidth (8 * Int.toNat ((2 : Int) ^ (↑(if (48 == 32 : Bool) then (2 : Nat) else 3) : Int))) (if decide (48 = 32) = true then 32 else 64) (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (48 == 32 : Bool) then (2 : Nat) else 3) : Int))) pte) = @BitVec.setWidth 64 (if decide (48 = 32) = true then 32 else 64) pte := rfl
    dsimp only [ptw_start_callback, ptw_step_callback, ptw_success_callback,
      SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.mk,
      ExceptT.bind, ExceptT.pure, ExceptT.lift, ExceptT.bindCont,
      MonadLift.monadLift, liftM, monadLift, Functor.map, EStateM.map,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get,
      assert, PreSail.assert]
    simp only [hxlen, ite_true]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    dsimp only [EStateM.run] at hread hinvRun hperm hnapot ⊢
    rw [hpaddr, hread]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [hfl, hextb, hinvRun]
    simp only [Bool.false_eq_true, ite_false, hleaf]
    rw [if_neg hlev0]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [hperm]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [if_neg hlev0]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [hnapot]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, EStateM.get, ExceptT.bindCont]
    simp only [hn0, Bool.and_false, Bool.false_eq_true, ite_false]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, EStateM.get, ExceptT.bindCont]
    rw [hm]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    simp only [hpbmte, ite_true, hpteb]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [hppn_raw]
    exact congrArg (fun p : BitVec (if decide (48 = 32) = true then 22 else 44) =>
      (EStateM.Result.ok (Ok ({
        ppn := p
        pte := @BitVec.setWidth 64 (if decide (48 = 32) = true then 32 else 64) pte
        pteAddr := .Physaddr paddr
        level := 0
        pbmt := .PBMT_PMA
        global := global || (_get_PTE_Flags_G (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0)) == 1#1)
      }, ())) s : EStateM.Result (Error exception) (SequentialState RegisterType trivialChoiceSource)
        (Result (PTW_Output 48 × Unit) (PTW_Error × Unit)))) (by
      have hlen1 : (if decide (8 * ((2 : Int) ^ (↑(if (48 == 32 : Bool) = true then (2 : Nat) else 3) : Int)).toNat = 32) = true then 22 else 44) = 44 := by decide
      have hlen2 : (if decide (48 = 32) = true then 22 else 44) = 44 := by decide
      ext j hj
      simp only [BitVec.getElem_setWidth, BitVec.getLsbD_setWidth]
      have hj44 : j < 44 := by omega
      have hjB : j < (if decide (8 * ((2 : Int) ^ (↑(if (48 == 32 : Bool) = true then (2 : Nat) else 3) : Int)).toNat = 32) = true then 22 else 44) := by omega
      rw [decide_eq_true hjB, Bool.true_and, Bool.and_eq_right_iff_imp]
      intro _
      simp only [Sail.BitVec.length, BitVec.length, decide_eq_true_eq]
      have hlenNat : (if 8 * ((2 : Int) ^ (↑(if (48 == 32 : Bool) = true then (2 : Nat) else 3) : Int)).toNat = 32 then (22 : Nat) else 44) = 44 := by decide
      rw [hlenNat]
      omega)

private theorem pt_walk_sv39_4k_std_run (adue : BitVec 1)
    (s4k : SequentialState RegisterType trivialChoiceSource)
    (hstd4k : rv64StandardPtwRegs s4k adue)
    (h4k_l2 : rv64ReadMemBytesSpec 8 0x80001008 s4k.mem = some 0x0000000020000801#64)
    (h4k_l1 : rv64ReadMemBytesSpec 8 0x80002010 s4k.mem = some 0x0000000020000c01#64)
    (h4k_l0 : rv64ReadMemBytesSpec 8 0x80003018 s4k.mem = some 0x00000000200400c7#64) :
    (pt_walk 39 0x0040403#27 (.Load .Data) .Supervisor false false 0x00000080001#44 2 false ()).run s4k =
      .ok (.Ok ({
        ppn := 0x00000080100#44
        pte := 0x00000000200400c7#64
        pteAddr := .Physaddr 0x0000000080003018#64
        level := 0
        pbmt := .PBMT_PMA
        global := false
      }, ())) s4k := by
  have hs2 := pt_walk_nonleaf_step 39 (.inl rfl) 0x0040403#27 (.Load .Data) .Supervisor false false
    0x00000080001#44 2 (by decide) false 0x0000000080001008#64 0x0000000020000801#64 adue
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s4k hstd4k h4k_l2
  have hs1 := pt_walk_nonleaf_step 39 (.inl rfl) 0x0040403#27 (.Load .Data) .Supervisor false false
    (@BitVec.setWidth 44 (if (39 = 32 : Bool) then 22 else 44) 0x00000080002#44) 1 (by decide) false 0x0000000080002010#64 0x0000000020000c01#64 adue
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s4k hstd4k h4k_l1
  have hs0 := pt_walk_leaf0_step 39 (.inl rfl) 0x0040403#27 (.Load .Data) .Supervisor false false
    (@BitVec.setWidth 44 (if (39 = 32 : Bool) then 22 else 44) 0x00000080003#44) false 0x0000000080003018#64 0x00000000200400c7#64 adue
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s4k hstd4k h4k_l0 rfl
  have hppn2 : @BitVec.setWidth _ (if (39 = 32 : Bool) then 22 else 44) (PPN_of_PTE 0x0000000020000801#64) =
      @BitVec.setWidth 44 (if (39 = 32 : Bool) then 22 else 44) 0x00000080002#44 := by decide
  have hppn1 : @BitVec.setWidth _ (if (39 = 32 : Bool) then 22 else 44) (PPN_of_PTE 0x0000000020000c01#64) =
      @BitVec.setWidth 44 (if (39 = 32 : Bool) then 22 else 44) 0x00000080003#44 := by decide
  have hppn0 : @BitVec.setWidth _ (if (39 = 32 : Bool) then 22 else 44) (PPN_of_PTE 0x00000000200400c7#64) =
      (0x00000080100#44 : BitVec (if (39 = 32 : Bool) then 22 else 44)) := by decide
  have hpte0 : @BitVec.setWidth _ (if (39 = 32 : Bool) then 32 else 64) 0x00000000200400c7#64 =
      (0x00000000200400c7#64 : BitVec (if (39 = 32 : Bool) then 32 else 64)) := by decide
  have hg1 : (false || (_get_PTE_Flags_G (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x0000000020000801#64 7 0)) == 1#1)) = false := by decide
  have hg2 : (false || (_get_PTE_Flags_G (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x0000000020000c01#64 7 0)) == 1#1)) = false := by decide
  have hg3 : (false || (_get_PTE_Flags_G (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x00000000200400c7#64 7 0)) == 1#1)) = false := by decide
  have hl2 : ((2 : Nat) -i 1).toNat = 1 := rfl
  have hl1 : ((1 : Nat) -i 1).toNat = 0 := rfl
  rw [hs2, hppn2, hl2, hg1, hs1, hppn1, hl1, hg2, hs0, hppn0, hpte0, hg3]
  rfl

theorem rv64PtWalkSv39_bisim_sail (adue : BitVec 1)
    (s4k sMega sMis sInv sNoPerm : SequentialState RegisterType trivialChoiceSource)
    (hstd4k : rv64StandardPtwRegs s4k adue)
    (hstdMega : rv64StandardPtwRegs sMega adue)
    (hstdMis : rv64StandardPtwRegs sMis adue)
    (hstdInv : rv64StandardPtwRegs sInv adue)
    (hstdNoPerm : rv64StandardPtwRegs sNoPerm adue)
    (h4k_l2 : rv64ReadMemBytesSpec 8 0x80001008 s4k.mem = some 0x0000000020000801#64)
    (h4k_l1 : rv64ReadMemBytesSpec 8 0x80002010 s4k.mem = some 0x0000000020000c01#64)
    (h4k_l0 : rv64ReadMemBytesSpec 8 0x80003018 s4k.mem = some 0x00000000200400c7#64)
    (hmega_l2 : rv64ReadMemBytesSpec 8 0x80001008 sMega.mem = some 0x0000000020000801#64)
    (hmega_l1 : rv64ReadMemBytesSpec 8 0x80002010 sMega.mem = some 0x00000000200800c7#64)
    (hmis_l2 : rv64ReadMemBytesSpec 8 0x80001008 sMis.mem = some 0x0000000020000801#64)
    (hmis_l1 : rv64ReadMemBytesSpec 8 0x80002010 sMis.mem = some 0x00000000200804c7#64)
    (hinv_l2 : rv64ReadMemBytesSpec 8 0x80001008 sInv.mem = some 0x0000000000000000#64)
    (hnop_l0 : rv64ReadMemBytesSpec 8 0x80003018 sNoPerm.mem = some 0x00000000200400d7#64) :
    (pt_walk 39 0x0040403#27 (.Load .Data) .Supervisor false false 0x00000080001#44 2 false ()).run s4k =
      .ok (.Ok ({
        ppn := 0x00000080100#44
        pte := 0x00000000200400c7#64
        pteAddr := .Physaddr 0x0000000080003018#64
        level := 0
        pbmt := .PBMT_PMA
        global := false
      }, ())) s4k ∧
    (pt_walk 39 0x0040403#27 (.Load .Data) .Supervisor false false 0x00000080001#44 2 false ()).run sMega =
      .ok (.Ok ({
        ppn := 0x00000080203#44
        pte := 0x00000000200800c7#64
        pteAddr := .Physaddr 0x0000000080002010#64
        level := 1
        pbmt := .PBMT_PMA
        global := false
      }, ())) sMega ∧
    (pt_walk 39 0x0040403#27 (.Load .Data) .Supervisor false false 0x00000080001#44 2 false ()).run sMis =
      .ok (.Err (.PTW_Misaligned (), ())) sMis ∧
    (pt_walk 39 0x0040403#27 (.Load .Data) .Supervisor false false 0x00000080001#44 2 false ()).run sInv =
      .ok (.Err (.PTW_Invalid_PTE (), ())) sInv ∧
    (pt_walk 39 0x0040403#27 (.Load .Data) .Supervisor false false 0x00000080003#44 0 false ()).run sNoPerm =
      .ok (.Err (.PTW_No_Permission (), ())) sNoPerm := by
  have hxlen : ((39 == 32 : Bool) || (LeanRV64D.Functions.xlen == 64)) = true := by decide
  refine ⟨pt_walk_sv39_4k_std_run adue s4k hstd4k h4k_l2 h4k_l1 h4k_l0, ?_, ?_, ?_, ?_⟩
  · have hs2 := pt_walk_nonleaf_step 39 (.inl rfl) 0x0040403#27 (.Load .Data) .Supervisor false false
      0x00000080001#44 2 (by decide) false 0x0000000080001008#64 0x0000000020000801#64 adue
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) sMega hstdMega hmega_l2
    have hppn2 : @BitVec.setWidth _ (if (39 = 32 : Bool) then 22 else 44) (PPN_of_PTE 0x0000000020000801#64) =
        @BitVec.setWidth 44 (if (39 = 32 : Bool) then 22 else 44) 0x00000080002#44 := by decide
    have hg1 : (false || (_get_PTE_Flags_G (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x0000000020000801#64 7 0)) == 1#1)) = false := by decide
    have hl2 : ((2 : Nat) -i 1).toNat = 1 := rfl
    rw [hs2, hppn2, hl2, hg1]
    have hread1 := read_pte_pow_std_run 39 (.inl rfl) 0x0000000080002010#64 0x00000000200800c7#64 adue
      (by decide) (by decide) (by decide) sMega hstdMega hmega_l1
    have hinv1 := pte_is_invalid_std_run (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x00000000200800c7#64 7 0))
      (ext_bits_of_PTE 0x00000000200800c7#64) adue sMega hstdMega
    have hinvVal : pteIsInvalidStdSpec (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x00000000200800c7#64 7 0))
      (ext_bits_of_PTE 0x00000000200800c7#64) = false := by decide
    rw [hinvVal] at hinv1
    have hm := hstdMega.2.2.2.2.2
    have hpbmte : (_get_MEnvcfg_PBMTE (if (adue == 1#1) = true then 1#64 <<< 61 else 0#64) == 0#1) = true := by
      cases (adue == 1#1) <;> decide
    rw [pt_walk.eq_1]
    have hfl : Sail.BitVec.extractLsb (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (39 == 32 : Bool) then (2 : Nat) else 3) : Int))) 0x00000000200800c7#64) 7 0 = Sail.BitVec.extractLsb 0x00000000200800c7#64 7 0 := rfl
    have hextb : ext_bits_of_PTE (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (39 == 32 : Bool) then (2 : Nat) else 3) : Int))) 0x00000000200800c7#64) = ext_bits_of_PTE 0x00000000200800c7#64 := rfl
    have hpteb : @BitVec.setWidth (8 * Int.toNat ((2 : Int) ^ (↑(if (39 == 32 : Bool) then (2 : Nat) else 3) : Int))) (if decide (39 = 32) = true then 32 else 64) (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (39 == 32 : Bool) then (2 : Nat) else 3) : Int))) 0x00000000200800c7#64) = @BitVec.setWidth 64 (if decide (39 = 32) = true then 32 else 64) 0x00000000200800c7#64 := rfl
    have hpaddr1 : zero_extend (m := 64)
      (@BitVec.setWidth (if decide (39 = 32) = true then 22 else 44) (if decide (39 = 32) = true then 22 else 44)
        (@BitVec.setWidth 44 (if decide (39 = 32) = true then 22 else 44) 0x00000080002#44) +++ (Sail.BitVec.extractLsb 0x0040403#27
        (((((1 : Nat) : Int) + 1) * (if (39 == 32 : Bool) then 10 else 9) - 1).toNat)
        ((((1 : Nat) : Int) * (if (39 == 32 : Bool) then 10 else 9)).toNat) +++
        zeros (n := if (39 == 32 : Bool) then 2 else 3))) = 0x0000000080002010#64 := by decide
    have hleaf1 : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x00000000200800c7#64 7 0)) = false := by decide
    have hlev1 : ((1 : Nat) >b 0) = true := by decide
    have halignMega : (Sail.BitVec.extractLsb (PPN_of_PTE (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (39 == 32 : Bool) then (2 : Nat) else 3) : Int))) 0x00000000200800c7#64))
        (((if (39 == 32 : Bool) then 10 else 9) * ((1 : Nat) : Int) - 1).toNat) 0 !=
        BitVec.setWidth (((if (39 == 32 : Bool) then 10 else 9) * ((1 : Nat) : Int) - 1).toNat - 0 + 1)
          (zeros (n := (((((if (39 == 32 : Bool) then 10 else 9) *i (1 : Nat)) -i 1) -i 0) +i 1).toNat))) = false := by decide
    have hperm1 : (check_PTE_permission (.Load .Data) .Supervisor false false
        (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x00000000200800c7#64 7 0))
        (ext_bits_of_PTE 0x00000000200800c7#64) ()).run sMega = .ok (.PTE_Check_Success ()) sMega := rfl
    have hn1 : ((_get_PTE_Ext_N (ext_bits_of_PTE 0x00000000200800c7#64) == 1#1) && pte_reserved_bits_must_be_zero) = false := by decide
    have hsplice : @BitVec.setWidth _ (if (39 = 32 : Bool) then 22 else 44)
        (Sail.BitVec.extractLsb (PPN_of_PTE (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (39 == 32 : Bool) then (2 : Nat) else 3) : Int))) 0x00000000200800c7#64))
          ((BitVec.length (PPN_of_PTE (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (39 == 32 : Bool) then (2 : Nat) else 3) : Int))) 0x00000000200800c7#64)) : Int) - 1).toNat
          ((if (39 == 32 : Bool) then 10 else 9) * ((1 : Nat) : Int)).toNat +++
          Sail.BitVec.extractLsb 0x0040403#27 (((if (39 == 32 : Bool) then 10 else 9) * ((1 : Nat) : Int) - 1).toNat) 0) =
        (0x00000080203#44 : BitVec (if (39 = 32 : Bool) then 22 else 44)) := by decide
    have hpteMega : @BitVec.setWidth _ (if (39 = 32 : Bool) then 32 else 64) 0x00000000200800c7#64 =
        (0x00000000200800c7#64 : BitVec (if (39 = 32 : Bool) then 32 else 64)) := by decide
    have hgMega : (false || (_get_PTE_Flags_G (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x00000000200800c7#64 7 0)) == 1#1)) = false := by decide
    dsimp only [ptw_start_callback, ptw_step_callback, ptw_success_callback,
      SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.mk,
      ExceptT.bind, ExceptT.pure, ExceptT.lift, ExceptT.bindCont,
      MonadLift.monadLift, liftM, monadLift, Functor.map, EStateM.map,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get,
      assert, PreSail.assert]
    simp only [hxlen, ite_true]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    dsimp only [EStateM.run] at hread1 hinv1 hperm1 ⊢
    rw [hpaddr1, hread1]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [hfl, hextb, hinv1]
    simp only [Bool.false_eq_true, ite_false, hleaf1, hlev1, ite_true, hpteb, halignMega]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [hperm1]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    simp only [hn1, Bool.false_eq_true, ite_false]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, EStateM.get, ExceptT.bindCont]
    rw [hm]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    simp only [hpbmte, ite_true]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [hsplice, hpteMega, hgMega]
    rfl
  · have hs2 := pt_walk_nonleaf_step 39 (.inl rfl) 0x0040403#27 (.Load .Data) .Supervisor false false
      0x00000080001#44 2 (by decide) false 0x0000000080001008#64 0x0000000020000801#64 adue
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) sMis hstdMis hmis_l2
    have hppn2 : @BitVec.setWidth _ (if (39 = 32 : Bool) then 22 else 44) (PPN_of_PTE 0x0000000020000801#64) =
        @BitVec.setWidth 44 (if (39 = 32 : Bool) then 22 else 44) 0x00000080002#44 := by decide
    have hg1 : (false || (_get_PTE_Flags_G (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x0000000020000801#64 7 0)) == 1#1)) = false := by decide
    have hl2 : ((2 : Nat) -i 1).toNat = 1 := rfl
    rw [hs2, hppn2, hl2, hg1]
    have hread1 := read_pte_pow_std_run 39 (.inl rfl) 0x0000000080002010#64 0x00000000200804c7#64 adue
      (by decide) (by decide) (by decide) sMis hstdMis hmis_l1
    have hinv1 := pte_is_invalid_std_run (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x00000000200804c7#64 7 0))
      (ext_bits_of_PTE 0x00000000200804c7#64) adue sMis hstdMis
    have hinvVal : pteIsInvalidStdSpec (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x00000000200804c7#64 7 0))
      (ext_bits_of_PTE 0x00000000200804c7#64) = false := by decide
    rw [hinvVal] at hinv1
    rw [pt_walk.eq_1]
    have hfl : Sail.BitVec.extractLsb (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (39 == 32 : Bool) then (2 : Nat) else 3) : Int))) 0x00000000200804c7#64) 7 0 = Sail.BitVec.extractLsb 0x00000000200804c7#64 7 0 := rfl
    have hextb : ext_bits_of_PTE (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (39 == 32 : Bool) then (2 : Nat) else 3) : Int))) 0x00000000200804c7#64) = ext_bits_of_PTE 0x00000000200804c7#64 := rfl
    have hpaddr1 : zero_extend (m := 64)
      (@BitVec.setWidth (if decide (39 = 32) = true then 22 else 44) (if decide (39 = 32) = true then 22 else 44)
        (@BitVec.setWidth 44 (if decide (39 = 32) = true then 22 else 44) 0x00000080002#44) +++ (Sail.BitVec.extractLsb 0x0040403#27
        (((((1 : Nat) : Int) + 1) * (if (39 == 32 : Bool) then 10 else 9) - 1).toNat)
        ((((1 : Nat) : Int) * (if (39 == 32 : Bool) then 10 else 9)).toNat) +++
        zeros (n := if (39 == 32 : Bool) then 2 else 3))) = 0x0000000080002010#64 := by decide
    have hleaf1 : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x00000000200804c7#64 7 0)) = false := by decide
    have hlev1 : ((1 : Nat) >b 0) = true := by decide
    have hmis : (Sail.BitVec.extractLsb (PPN_of_PTE (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (39 == 32 : Bool) then (2 : Nat) else 3) : Int))) 0x00000000200804c7#64))
        (((if (39 == 32 : Bool) then 10 else 9) * ((1 : Nat) : Int) - 1).toNat) 0 !=
        BitVec.setWidth (((if (39 == 32 : Bool) then 10 else 9) * ((1 : Nat) : Int) - 1).toNat - 0 + 1)
          (zeros (n := (((((if (39 == 32 : Bool) then 10 else 9) *i (1 : Nat)) -i 1) -i 0) +i 1).toNat))) = true := by decide
    dsimp only [ptw_start_callback, ptw_step_callback, ptw_fail_callback,
      SailME.run, PreSail.PreSailME.run, SailME.throw, PreSail.PreSailME.throw,
      MonadExceptOf.throw, MonadExcept.throw, ExceptT.run, ExceptT.mk,
      ExceptT.bind, ExceptT.pure, ExceptT.lift, ExceptT.bindCont,
      MonadLift.monadLift, liftM, monadLift, Functor.map, EStateM.map,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run,
      assert, PreSail.assert]
    simp only [hxlen, ite_true]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    dsimp only [EStateM.run] at hread1 hinv1 ⊢
    rw [hpaddr1, hread1]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [hfl, hextb, hinv1]
    simp only [Bool.false_eq_true, ite_false, hleaf1, hlev1, ite_true, hmis]
    rfl
  · have hread2 := read_pte_pow_std_run 39 (.inl rfl) 0x0000000080001008#64 0x0000000000000000#64 adue
      (by decide) (by decide) (by decide) sInv hstdInv hinv_l2
    have hinv2 := pte_is_invalid_std_run (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x0000000000000000#64 7 0))
      (ext_bits_of_PTE 0x0000000000000000#64) adue sInv hstdInv
    have hinvVal : pteIsInvalidStdSpec (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x0000000000000000#64 7 0))
      (ext_bits_of_PTE 0x0000000000000000#64) = true := by decide
    rw [hinvVal] at hinv2
    rw [pt_walk.eq_1]
    have hfl : Sail.BitVec.extractLsb (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (39 == 32 : Bool) then (2 : Nat) else 3) : Int))) 0x0000000000000000#64) 7 0 = Sail.BitVec.extractLsb 0x0000000000000000#64 7 0 := rfl
    have hextb : ext_bits_of_PTE (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (39 == 32 : Bool) then (2 : Nat) else 3) : Int))) 0x0000000000000000#64) = ext_bits_of_PTE 0x0000000000000000#64 := rfl
    have hpaddr2 : zero_extend (m := 64)
      ((let b : BitVec (if decide (39 = 32) = true then 22 else 44) := 0x00000080001#44; b) +++ (Sail.BitVec.extractLsb 0x0040403#27
        (((((2 : Nat) : Int) + 1) * (if (39 == 32 : Bool) then 10 else 9) - 1).toNat)
        ((((2 : Nat) : Int) * (if (39 == 32 : Bool) then 10 else 9)).toNat) +++
        zeros (n := if (39 == 32 : Bool) then 2 else 3))) = 0x0000000080001008#64 := by decide
    dsimp only [ptw_start_callback, ptw_step_callback, ptw_fail_callback,
      SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.mk,
      ExceptT.bind, ExceptT.pure, ExceptT.lift, ExceptT.bindCont,
      MonadLift.monadLift, liftM, monadLift, Functor.map, EStateM.map,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run,
      assert, PreSail.assert]
    simp only [hxlen, ite_true]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    dsimp only [EStateM.run] at hread2 hinv2 ⊢
    rw [hpaddr2, hread2]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [hfl, hextb, hinv2]
    rfl
  · have hread0 := read_pte_pow_std_run 39 (.inl rfl) 0x0000000080003018#64 0x00000000200400d7#64 adue
      (by decide) (by decide) (by decide) sNoPerm hstdNoPerm hnop_l0
    have hinv0 := pte_is_invalid_std_run (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x00000000200400d7#64 7 0))
      (ext_bits_of_PTE 0x00000000200400d7#64) adue sNoPerm hstdNoPerm
    have hinvVal : pteIsInvalidStdSpec (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x00000000200400d7#64 7 0))
      (ext_bits_of_PTE 0x00000000200400d7#64) = false := by decide
    rw [hinvVal] at hinv0
    rw [pt_walk.eq_1]
    have hfl : Sail.BitVec.extractLsb (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (39 == 32 : Bool) then (2 : Nat) else 3) : Int))) 0x00000000200400d7#64) 7 0 = Sail.BitVec.extractLsb 0x00000000200400d7#64 7 0 := rfl
    have hextb : ext_bits_of_PTE (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (39 == 32 : Bool) then (2 : Nat) else 3) : Int))) 0x00000000200400d7#64) = ext_bits_of_PTE 0x00000000200400d7#64 := rfl
    have hpaddr0 : zero_extend (m := 64)
      ((let b : BitVec (if decide (39 = 32) = true then 22 else 44) := 0x00000080003#44; b) +++ (Sail.BitVec.extractLsb 0x0040403#27
        (((((0 : Nat) : Int) + 1) * (if (39 == 32 : Bool) then 10 else 9) - 1).toNat)
        ((((0 : Nat) : Int) * (if (39 == 32 : Bool) then 10 else 9)).toNat) +++
        zeros (n := if (39 == 32 : Bool) then 2 else 3))) = 0x0000000080003018#64 := by decide
    have hleaf0 : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x00000000200400d7#64 7 0)) = false := by decide
    have hlev0 : ((0 : Nat) >b 0) = false := by decide
    have hpermFail : (check_PTE_permission (.Load .Data) .Supervisor false false
        (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x00000000200400d7#64 7 0))
        (ext_bits_of_PTE 0x00000000200400d7#64) ()).run sNoPerm =
        .ok (.PTE_Check_Failure ((), .PTE_No_Permission ())) sNoPerm := rfl
    dsimp only [ptw_start_callback, ptw_step_callback, ptw_fail_callback,
      SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.mk,
      ExceptT.bind, ExceptT.pure, ExceptT.lift, ExceptT.bindCont,
      MonadLift.monadLift, liftM, monadLift, Functor.map, EStateM.map,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run,
      assert, PreSail.assert]
    simp only [hxlen, ite_true]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    dsimp only [EStateM.run] at hread0 hinv0 hpermFail ⊢
    rw [hpaddr0, hread0]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [hfl, hextb, hinv0]
    simp only [Bool.false_eq_true, ite_false, hleaf0, hlev0]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [hpermFail]
    rfl

theorem rv64PtWalkSv48_bisim_sail (adue : BitVec 1)
    (s4k sInv : SequentialState RegisterType trivialChoiceSource)
    (hstd4k : rv64StandardPtwRegs s4k adue)
    (hstdInv : rv64StandardPtwRegs sInv adue)
    (h4k_l3 : rv64ReadMemBytesSpec 8 0x80000020 s4k.mem = some 0x0000000020000401#64)
    (h4k_l2 : rv64ReadMemBytesSpec 8 0x80001008 s4k.mem = some 0x0000000020000801#64)
    (h4k_l1 : rv64ReadMemBytesSpec 8 0x80002010 s4k.mem = some 0x0000000020000c01#64)
    (h4k_l0 : rv64ReadMemBytesSpec 8 0x80003018 s4k.mem = some 0x00000000200400c7#64)
    (hinv_l3 : rv64ReadMemBytesSpec 8 0x80000020 sInv.mem = some 0x0000000000000000#64) :
    (pt_walk 48 0x020040403#36 (.Load .Data) .Supervisor false false 0x00000080000#44 3 false ()).run s4k =
      .ok (.Ok ({
        ppn := 0x00000080100#44
        pte := 0x00000000200400c7#64
        pteAddr := .Physaddr 0x0000000080003018#64
        level := 0
        pbmt := .PBMT_PMA
        global := false
      }, ())) s4k ∧
    (pt_walk 48 0x020040403#36 (.Load .Data) .Supervisor false false 0x00000080000#44 3 false ()).run sInv =
      .ok (.Err (.PTW_Invalid_PTE (), ())) sInv := by
  refine ⟨?_, ?_⟩
  · have hs3 := pt_walk_nonleaf_step 48 (.inr rfl) 0x020040403#36 (.Load .Data) .Supervisor false false
      0x00000080000#44 3 (by decide) false 0x0000000080000020#64 0x0000000020000401#64 adue
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s4k hstd4k h4k_l3
    have hs2 := pt_walk_nonleaf_step 48 (.inr rfl) 0x020040403#36 (.Load .Data) .Supervisor false false
      (@BitVec.setWidth 44 (if (48 = 32 : Bool) then 22 else 44) 0x00000080001#44) 2 (by decide) false 0x0000000080001008#64 0x0000000020000801#64 adue
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s4k hstd4k h4k_l2
    have hs1 := pt_walk_nonleaf_step 48 (.inr rfl) 0x020040403#36 (.Load .Data) .Supervisor false false
      (@BitVec.setWidth 44 (if (48 = 32 : Bool) then 22 else 44) 0x00000080002#44) 1 (by decide) false 0x0000000080002010#64 0x0000000020000c01#64 adue
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s4k hstd4k h4k_l1
    have hs0 := pt_walk_leaf0_step 48 (.inr rfl) 0x020040403#36 (.Load .Data) .Supervisor false false
      (@BitVec.setWidth 44 (if (48 = 32 : Bool) then 22 else 44) 0x00000080003#44) false 0x0000000080003018#64 0x00000000200400c7#64 adue
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s4k hstd4k h4k_l0 rfl
    have hppn3 : @BitVec.setWidth _ (if (48 = 32 : Bool) then 22 else 44) (PPN_of_PTE 0x0000000020000401#64) =
        @BitVec.setWidth 44 (if (48 = 32 : Bool) then 22 else 44) 0x00000080001#44 := by decide
    have hppn2 : @BitVec.setWidth _ (if (48 = 32 : Bool) then 22 else 44) (PPN_of_PTE 0x0000000020000801#64) =
        @BitVec.setWidth 44 (if (48 = 32 : Bool) then 22 else 44) 0x00000080002#44 := by decide
    have hppn1 : @BitVec.setWidth _ (if (48 = 32 : Bool) then 22 else 44) (PPN_of_PTE 0x0000000020000c01#64) =
        @BitVec.setWidth 44 (if (48 = 32 : Bool) then 22 else 44) 0x00000080003#44 := by decide
    have hppn0 : @BitVec.setWidth _ (if (48 = 32 : Bool) then 22 else 44) (PPN_of_PTE 0x00000000200400c7#64) =
        (0x00000080100#44 : BitVec (if (48 = 32 : Bool) then 22 else 44)) := by decide
    have hpte0 : @BitVec.setWidth _ (if (48 = 32 : Bool) then 32 else 64) 0x00000000200400c7#64 =
        (0x00000000200400c7#64 : BitVec (if (48 = 32 : Bool) then 32 else 64)) := by decide
    have hg0 : (false || (_get_PTE_Flags_G (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x0000000020000401#64 7 0)) == 1#1)) = false := by decide
    have hg1 : (false || (_get_PTE_Flags_G (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x0000000020000801#64 7 0)) == 1#1)) = false := by decide
    have hg2 : (false || (_get_PTE_Flags_G (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x0000000020000c01#64 7 0)) == 1#1)) = false := by decide
    have hg3 : (false || (_get_PTE_Flags_G (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x00000000200400c7#64 7 0)) == 1#1)) = false := by decide
    have hl3 : ((3 : Nat) -i 1).toNat = 2 := rfl
    have hl2 : ((2 : Nat) -i 1).toNat = 1 := rfl
    have hl1 : ((1 : Nat) -i 1).toNat = 0 := rfl
    rw [hs3, hppn3, hl3, hg0, hs2, hppn2, hl2, hg1, hs1, hppn1, hl1, hg2, hs0, hppn0, hpte0, hg3]
    rfl
  · have hread3 := read_pte_pow_std_run 48 (.inr rfl) 0x0000000080000020#64 0x0000000000000000#64 adue
      (by decide) (by decide) (by decide) sInv hstdInv hinv_l3
    have hinv3 := pte_is_invalid_std_run (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x0000000000000000#64 7 0))
      (ext_bits_of_PTE 0x0000000000000000#64) adue sInv hstdInv
    have hinvVal : pteIsInvalidStdSpec (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x0000000000000000#64 7 0))
      (ext_bits_of_PTE 0x0000000000000000#64) = true := by decide
    rw [hinvVal] at hinv3
    rw [pt_walk.eq_1]
    have hxlen : ((48 == 32 : Bool) || (LeanRV64D.Functions.xlen == 64)) = true := by decide
    have hfl : Sail.BitVec.extractLsb (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (48 == 32 : Bool) then (2 : Nat) else 3) : Int))) 0x0000000000000000#64) 7 0 = Sail.BitVec.extractLsb 0x0000000000000000#64 7 0 := rfl
    have hextb : ext_bits_of_PTE (@BitVec.setWidth 64 (8 * Int.toNat ((2 : Int) ^ (↑(if (48 == 32 : Bool) then (2 : Nat) else 3) : Int))) 0x0000000000000000#64) = ext_bits_of_PTE 0x0000000000000000#64 := rfl
    have hpaddr3 : zero_extend (m := 64)
      ((let b : BitVec (if decide (48 = 32) = true then 22 else 44) := 0x00000080000#44; b) +++ (Sail.BitVec.extractLsb 0x020040403#36
        (((((3 : Nat) : Int) + 1) * (if (48 == 32 : Bool) then 10 else 9) - 1).toNat)
        ((((3 : Nat) : Int) * (if (48 == 32 : Bool) then 10 else 9)).toNat) +++
        zeros (n := if (48 == 32 : Bool) then 2 else 3))) = 0x0000000080000020#64 := by decide
    dsimp only [ptw_start_callback, ptw_step_callback, ptw_fail_callback,
      SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.mk,
      ExceptT.bind, ExceptT.pure, ExceptT.lift, ExceptT.bindCont,
      MonadLift.monadLift, liftM, monadLift, Functor.map, EStateM.map,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run,
      assert, PreSail.assert]
    simp only [hxlen, ite_true]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    dsimp only [EStateM.run] at hread3 hinv3 ⊢
    rw [hpaddr3, hread3]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [hfl, hextb, hinv3]
    rfl

def rv64Sv39TlbEntry4k (asid : BitVec 16) (pte : BitVec 64) : TLB_Entry :=
  { asid := asid
    global := false
    pte := pte
    pteAddr := .Physaddr 0x0000000080003018#64
    levelMask := 0#45
    vpn := sign_extend (m := 45) 0x0040403#27
    ppn := 0x00000080100#44 }

theorem rv64TranslateTlbHitAndMiss_bisim_sail
    (sEmpty sHitClean sHitDirty sMiss : SequentialState RegisterType trivialChoiceSource)
    (htlbEmpty : sEmpty.regs.get? .tlb = some (vectorInit (n := 64) none))
    (htlbHit : sHitClean.regs.get? .tlb =
      some (vectorUpdate (vectorInit (n := 64) none) 3 (some (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64))))
    (hstdHitDirty : rv64StandardPtwRegs sHitDirty 1#1)
    (htlbDirty : sHitDirty.regs.get? .tlb =
      some (vectorUpdate (vectorInit (n := 64) none) 3 (some (rv64Sv39TlbEntry4k 0x0001#16 0x0000000020040007#64))))
    (hstdMiss : rv64StandardPtwRegs sMiss 0#1)
    (htlbMiss : sMiss.regs.get? .tlb = some (vectorInit (n := 64) none))
    (hmiss_l2 : rv64ReadMemBytesSpec 8 0x80001008 sMiss.mem = some 0x0000000020000801#64)
    (hmiss_l1 : rv64ReadMemBytesSpec 8 0x80002010 sMiss.mem = some 0x0000000020000c01#64)
    (hmiss_l0 : rv64ReadMemBytesSpec 8 0x80003018 sMiss.mem = some 0x00000000200400c7#64) :
    (lookup_TLB 39 0x0001#16 0x0040403#27).run sEmpty = .ok none sEmpty ∧
    (lookup_TLB 39 0x0001#16 0x0040403#27).run sHitClean =
      .ok (some (3, rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64)) sHitClean ∧
    (lookup_TLB 39 0x0002#16 0x0040403#27).run sHitClean = .ok none sHitClean ∧
    (translate_TLB_hit 39 0x0001#16 0x0040403#27 (.Load .Data) .Supervisor false false () 3
        (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64)).run sHitClean =
      .ok (.Ok (0x00000080100#44, .PBMT_PMA, ())) sHitClean ∧
    (translate_TLB_hit 39 0x0001#16 0x0040403#27 (.Load .Data) .Supervisor false false () 3
        (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400d7#64)).run sHitClean =
      .ok (.Err (.PTW_No_Permission (), ())) sHitClean ∧
    (let sAfterWrite := { sHitDirty with mem := rv64WriteMemBytesSpec 8 0x80003018 0x00000000200400c7#64 sHitDirty.mem }
     let tlbUpdated := vectorUpdate (vectorUpdate (vectorInit (n := 64) none) 3
       (some (rv64Sv39TlbEntry4k 0x0001#16 0x0000000020040007#64))) 3
       (some (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64))
     (translate_TLB_hit 39 0x0001#16 0x0040403#27 (.Store .Data) .Supervisor false false () 3
        (rv64Sv39TlbEntry4k 0x0001#16 0x0000000020040007#64)).run sHitDirty =
      .ok (.Ok (0x00000080100#44, .PBMT_PMA, ())) { sAfterWrite with regs := sAfterWrite.regs.insert .tlb tlbUpdated }) ∧
    (let tlbFilled := vectorUpdate (vectorInit (n := 64) none) 3
       (some (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64))
     (translate_TLB_miss 39 0x0001#16 0x00000080001#44 0x0040403#27 (.Load .Data) .Supervisor false false ()).run sMiss =
      .ok (.Ok (0x00000080100#44, .PBMT_PMA, ()))
        { sMiss with regs := (sMiss.regs.insert .tlb tlbFilled) }) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold lookup_TLB
    have hidx : tlb_hash 39 0x0040403#27 = 3 := by decide
    have hget : (vectorInit (n := 64) (none : Option TLB_Entry))[3]! = none := by
      unfold vectorInit; simp
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
    rw [htlbEmpty]
    dsimp only [EStateM.pure]
    rw [hidx, hget]
    rfl
  · unfold lookup_TLB
    have hidx : tlb_hash 39 0x0040403#27 = 3 := by decide
    have hget : (vectorUpdate (vectorInit (n := 64) (none : Option TLB_Entry)) 3
        (some (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64)))[3]! =
        some (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64) := by
      unfold vectorUpdate vectorInit Vector.set!
      simp [GetElem?.getElem!, decidableGetElem?]
    have hmatch : match_TLB_Entry (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64) 0x0001#16
        (sign_extend (m := (57 -i 12)) 0x0040403#27) = true := by decide
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
    rw [htlbHit]
    dsimp only [EStateM.pure]
    rw [hidx, hget]
    dsimp only
    rw [hmatch]
    rfl
  · unfold lookup_TLB
    have hidx : tlb_hash 39 0x0040403#27 = 3 := by decide
    have hget : (vectorUpdate (vectorInit (n := 64) (none : Option TLB_Entry)) 3
        (some (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64)))[3]! =
        some (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64) := by
      unfold vectorUpdate vectorInit Vector.set!
      simp [GetElem?.getElem!, decidableGetElem?]
    have hmatch : match_TLB_Entry (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64) 0x0002#16
        (sign_extend (m := (57 -i 12)) 0x0040403#27) = false := by decide
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
    rw [htlbHit]
    dsimp only [EStateM.pure]
    rw [hidx, hget]
    dsimp only
    rw [hmatch]
    rfl
  · unfold translate_TLB_hit update_and_write_pte
    have hsz : (if (39 == 32 : Bool) then 4 else 8) = 8 := rfl
    have hpte : tlb_get_pte 8 (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64) = 0x00000000200400c7#64 := by decide
    have hperm : (check_PTE_permission (.Load .Data) .Supervisor false false
        (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x00000000200400c7#64 7 0))
        (ext_bits_of_PTE 0x00000000200400c7#64) ()).run sHitClean = .ok (.PTE_Check_Success ()) sHitClean := rfl
    have hnone : update_PTE_Bits 0x00000000200400c7#64 (.Load .Data) = none := by decide
    have hppn : tlb_get_ppn 39 (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64) 0x0040403#27 = 0x00000080100#44 := by decide
    have hpbmt : (tlb_get_pbmt (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64)).run sHitClean = .ok .PBMT_PMA sHitClean := rfl
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at hperm hpbmt ⊢
    rw [hsz, hpte, hperm]
    dsimp only [EStateM.bind, EStateM.pure]
    rw [hnone]
    dsimp only [EStateM.bind, EStateM.pure]
    rw [hpbmt, hppn]
  · unfold translate_TLB_hit
    have hsz : (if (39 == 32 : Bool) then 4 else 8) = 8 := rfl
    have hpte : tlb_get_pte 8 (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400d7#64) = 0x00000000200400d7#64 := by decide
    have hperm : (check_PTE_permission (.Load .Data) .Supervisor false false
        (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x00000000200400d7#64 7 0))
        (ext_bits_of_PTE 0x00000000200400d7#64) ()).run sHitClean =
        .ok (.PTE_Check_Failure ((), .PTE_No_Permission ())) sHitClean := rfl
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at hperm ⊢
    rw [hsz, hpte, hperm]
    rfl
  · dsimp only
    have hupd : (update_and_write_pte (.Physaddr 0x0000000080003018#64) 8 0x0000000020040007#64 (.Store .Data)).run sHitDirty =
        .ok (.Ok (some 0x00000000200400c7#64))
          { sHitDirty with mem := rv64WriteMemBytesSpec 8 0x80003018 0x00000000200400c7#64 sHitDirty.mem } := by
      have hc1 := (currentlyEnabled_ptw_std_run 1#1 sHitDirty hstdHitDirty).1
      have hc1e := (currentlyEnabled_ptw_std_run 1#1 sHitDirty hstdHitDirty).2.1
      have hm1 := hstdHitDirty.2.2.2.2.2
      have hu_store : update_PTE_Bits 0x0000000020040007#64 (.Store .Data) = some 0x00000000200400c7#64 := by decide
      have hwStore := write_pte_std_run 0x0000000080003018#64 0x00000000200400c7#64 1#1
        (by decide) (by decide) (by decide) sHitDirty hstdHitDirty
      unfold update_and_write_pte LeanRV64D.Functions.not
      rw [hu_store]
      dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
        readReg, PreSail.readReg, get, getThe, MonadStateOf.get] at hc1 hc1e hwStore ⊢
      rw [hc1]; dsimp only [EStateM.pure, EStateM.bind, EStateM.get]
      rw [hm1]; dsimp only [EStateM.pure]
      rw [hc1]; dsimp only
      rw [hc1e]
      have hadue1 : (_get_MEnvcfg_ADUE (if (1#1 == 1#1) = true then 1#64 <<< 61 else 0#64) == 1#1) = true := by decide
      rw [hadue1]
      simp only [Bool.and_self, Bool.not_true, Bool.or_false, ite_true, EStateM.bind]
      rw [hwStore]; rfl
    unfold translate_TLB_hit write_TLB
    have hsz : (if (39 == 32 : Bool) then 4 else 8) = 8 := rfl
    have hpte : tlb_get_pte 8 (rv64Sv39TlbEntry4k 0x0001#16 0x0000000020040007#64) = 0x0000000020040007#64 := by decide
    have hperm : (check_PTE_permission (.Store .Data) .Supervisor false false
        (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x0000000020040007#64 7 0))
        (ext_bits_of_PTE 0x0000000020040007#64) ()).run sHitDirty = .ok (.PTE_Check_Success ()) sHitDirty := rfl
    have hset : tlb_set_pte (rv64Sv39TlbEntry4k 0x0001#16 0x0000000020040007#64) (k_n := 8) 0x00000000200400c7#64 =
        rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64 := rfl
    have hpaddrEnt : (rv64Sv39TlbEntry4k 0x0001#16 0x0000000020040007#64).pteAddr = .Physaddr 0x0000000080003018#64 := rfl
    have hppn : tlb_get_ppn 39 (rv64Sv39TlbEntry4k 0x0001#16 0x0000000020040007#64) 0x0040403#27 = 0x00000080100#44 := by decide
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet, EStateM.run,
      readReg, writeReg, PreSail.readReg, PreSail.writeReg,
      get, getThe, MonadStateOf.get, modifyGet, MonadStateOf.modifyGet] at hupd hperm ⊢
    rw [hsz, hpte, hperm]
    dsimp only [EStateM.bind]
    rw [hpaddrEnt, hupd]
    dsimp only [EStateM.bind, EStateM.get, EStateM.modifyGet, modify]
    rw [htlbDirty, hset]
    dsimp only [EStateM.pure]
    unfold tlb_get_pbmt page_based_mem_type_forwards
    have hpbmt0 : _get_PTE_Ext_PBMT (ext_bits_of_PTE (rv64Sv39TlbEntry4k 0x0001#16 0x0000000020040007#64).pte) = 0b00#2 := by decide
    rw [hpbmt0, hppn]
    rfl
  · dsimp only
    have hwalk := pt_walk_sv39_4k_std_run 0#1 sMiss hstdMiss hmiss_l2 hmiss_l1 hmiss_l0
    unfold translate_TLB_miss add_to_TLB update_and_write_pte
    have hlvl : (if (39 == 32 : Bool) then 1 else if (39 == 39 : Bool) then 2 else if (39 == 48 : Bool) then 3 else 4) = 2 := rfl
    have hsz : (if (39 == 32 : Bool) then 4 else 8) = 8 := rfl
    have hidx : tlb_hash 39 0x0040403#27 = 3 := by decide
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet, EStateM.run,
      readReg, writeReg, PreSail.readReg, PreSail.writeReg, tlb_add_callback,
      get, getThe, MonadStateOf.get, modifyGet, MonadStateOf.modifyGet] at hwalk ⊢
    rw [hlvl, hsz, hwalk]
    dsimp only [EStateM.bind]
    have hnone8 : update_PTE_Bits
        (@BitVec.setWidth (if decide (39 = 32) = true then 32 else 64) (8 * 8)
          (let p : BitVec (if decide (39 = 32) = true then 32 else 64) := 0x00000000200400c7#64; p))
        (.Load .Data) = none := by decide
    rw [hnone8]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.get, EStateM.modifyGet, modify]
    rw [htlbMiss, hidx]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.get, EStateM.modifyGet, modifyGet]
    let p_ppn : BitVec (if decide (39 = 32) = true then 22 else 44) := 0x00000080100#44
    let p_pte : BitVec (if decide (39 = 32) = true then 32 else 64) := 0x00000000200400c7#64
    have h_vpn : sign_extend (m := (57 -i 12))
        (0x0040403#27 &&& BitVec.setWidth (39 - 12) (Complement.complement (zero_extend (m := (39 -i 12)) (ones (n := ((0 : Nat) *i (if (39 == 32 : Bool) then 10 else 9))))))) =
        (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64).vpn := by decide
    have h_lmask : zero_extend (m := (57 -i 12)) (ones (n := ((0 : Nat) *i (if (39 == 32 : Bool) then 10 else 9)))) =
        (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64).levelMask := by decide
    have h_ppn : zero_extend (m := 44)
        (HAnd.hAnd (α := BitVec (if decide (39 = 32) = true then 22 else 44))
          (β := BitVec (if (39 == 32 : Bool) then 22 else 44))
          p_ppn
          (Complement.complement (zero_extend (m := (if (39 == 32 : Bool) then 22 else 44)) (ones (n := ((0 : Nat) *i (if (39 == 32 : Bool) then 10 else 9))))))) =
        (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64).ppn := by decide
    have h_pte : zero_extend (m := 64) p_pte =
        (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64).pte := by decide
    have hins : vectorUpdate (vectorInit (n := 64) none) 3
        (some ({
          asid := 0x0001#16
          global := false
          pte := zero_extend (m := 64) p_pte
          pteAddr := .Physaddr 0x0000000080003018#64
          levelMask := zero_extend (m := (57 -i 12)) (ones (n := ((0 : Nat) *i (if (39 == 32 : Bool) then 10 else 9))))
          vpn := sign_extend (m := (57 -i 12))
            (0x0040403#27 &&& BitVec.setWidth (39 - 12) (Complement.complement (zero_extend (m := (39 -i 12)) (ones (n := ((0 : Nat) *i (if (39 == 32 : Bool) then 10 else 9)))))))
          ppn := zero_extend (m := 44)
            (HAnd.hAnd (α := BitVec (if decide (39 = 32) = true then 22 else 44))
              (β := BitVec (if (39 == 32 : Bool) then 22 else 44))
              p_ppn
              (Complement.complement (zero_extend (m := (if (39 == 32 : Bool) then 22 else 44)) (ones (n := ((0 : Nat) *i (if (39 == 32 : Bool) then 10 else 9)))))))
        } : TLB_Entry)) =
        vectorUpdate (vectorInit (n := 64) none) 3
          (some (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64)) := by
      rw [h_vpn, h_lmask, h_ppn, h_pte]
      rfl
    rw [hins]
    dsimp only [modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.bind, EStateM.pure]
    have hgetAfter : (sMiss.regs.insert .tlb (vectorUpdate (vectorInit (n := 64) none) 3
        (some (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64)))).get? .tlb =
        some (vectorUpdate (vectorInit (n := 64) none) 3
          (some (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64))) := by
      exact Std.ExtDHashMap.get?_insert_self
    rw [hgetAfter]
    rfl

def rv64SupervisorSv39Mstatus : BitVec 64 :=
  (0b10#64 <<< 34) ||| (0b10#64 <<< 32)

def rv64SupervisorSv39Satp : BitVec 64 :=
  (0x8#64 <<< 60) ||| (0x0001#64 <<< 44) ||| 0x00000080001#64

theorem rv64TranslateAndTranslateAddr_bisim_sail
    (sHit sMach sSup : SequentialState RegisterType trivialChoiceSource)
    (htlbHit : sHit.regs.get? .tlb =
      some (vectorUpdate (vectorInit (n := 64) none) 3 (some (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64))))
    (hmachPriv : sMach.regs.get? .cur_privilege = some .Machine)
    (hmachMstatus : sMach.regs.get? .mstatus = some rv64SupervisorSv39Mstatus)
    (hstdSup : rv64StandardPtwRegs sSup 0#1)
    (hsupPriv : sSup.regs.get? .cur_privilege = some .Supervisor)
    (hsupMstatus : sSup.regs.get? .mstatus = some rv64SupervisorSv39Mstatus)
    (hsupSatp : sSup.regs.get? .satp = some rv64SupervisorSv39Satp)
    (hsupTlb : sSup.regs.get? .tlb = some (vectorInit (n := 64) none))
    (hsup_l2 : rv64ReadMemBytesSpec 8 0x80001008 sSup.mem = some 0x0000000020000801#64)
    (hsup_l1 : rv64ReadMemBytesSpec 8 0x80002010 sSup.mem = some 0x0000000020000c01#64)
    (hsup_l0 : rv64ReadMemBytesSpec 8 0x80003018 sSup.mem = some 0x00000000200400c7#64) :
    (translate 39 0x0001#16 0x00000080001#44 0x0040403#27 (.Load .Data) .Supervisor false false ()).run sHit =
      .ok (.Ok (0x00000080100#44, .PBMT_PMA, ())) sHit ∧
    (translateAddr (.Virtaddr 0x0001000000000000#64) (.Load .Data)).run sMach =
      .ok (.Ok (.Physaddr 0x0001000000000000#64, .PBMT_PMA, ())) sMach ∧
    (translateAddr (.Virtaddr 0x0001000000000000#64) (.Load .Data)).run sSup =
      .ok (.Err (.E_Load_Page_Fault (), ())) sSup ∧
    (translateAddr (.Virtaddr 0x0001000000000000#64) (.Store .Data)).run sSup =
      .ok (.Err (.E_SAMO_Page_Fault (), ())) sSup ∧
    (translateAddr (.Virtaddr 0x0001000000000000#64) (.InstructionFetch ())).run sSup =
      .ok (.Err (.E_Fetch_Page_Fault (), ())) sSup ∧
    (let tlbFilled := vectorUpdate (vectorInit (n := 64) none) 3
       (some (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64))
     (translateAddr (.Virtaddr 0x0000000040403abc#64) (.Load .Data)).run sSup =
      .ok (.Ok (.Physaddr 0x0000000080100abc#64, .PBMT_PMA, ()))
        { sSup with regs := sSup.regs.insert .tlb tlbFilled }) := by
  have hmodeSup : (translationMode .Supervisor).run sSup = .ok .Sv39 sSup := by
    unfold translationMode architecture architecture_bits_backwards satpMode_of_bits
    have hprivF : (Privilege.Supervisor == Privilege.Machine) = false := by decide
    have hsxl : _get_Mstatus_SXL rv64SupervisorSv39Mstatus = 0b10#2 := by decide
    have hxlen : (LeanRV64D.Functions.xlen ≥b 64) = true := by decide
    have hmode : _get_Satp64_Mode (Mk_Satp64 rv64SupervisorSv39Satp) = 0x8#4 := by decide
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get, assert, PreSail.assert]
    simp only [hprivF, Bool.false_eq_true, ite_false]
    dsimp only [EStateM.bind, EStateM.get]
    rw [hsupMstatus]
    dsimp only [EStateM.pure, EStateM.bind]
    rw [hsxl]
    simp only [hxlen, ite_true]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.get]
    rw [hsupSatp]
    dsimp only [EStateM.pure]
    rw [hmode]
    rfl
  have hgetSatp39 : (get_satp 39).run sSup =
      .ok (@BitVec.setWidth 64 (if decide (39 = 32) = true then 32 else 64) rv64SupervisorSv39Satp) sSup := by
    unfold get_satp
    have h39_32 : (39 == 32 : Bool) = false := by decide
    have hxlen64 : (false || (LeanRV64D.Functions.xlen == 64)) = true := by decide
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get, assert, PreSail.assert]
    simp only [h39_32, hxlen64, ite_true, Bool.false_eq_true, ite_false]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.get]
    rw [hsupSatp]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold translate lookup_TLB translate_TLB_hit update_and_write_pte
    have hidx : tlb_hash 39 0x0040403#27 = 3 := by decide
    have hget : (vectorUpdate (vectorInit (n := 64) (none : Option TLB_Entry)) 3
        (some (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64)))[3]! =
        some (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64) := by
      unfold vectorUpdate vectorInit Vector.set!
      simp [GetElem?.getElem!, decidableGetElem?]
    have hmatch : match_TLB_Entry (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64) 0x0001#16
        (sign_extend (m := (57 -i 12)) 0x0040403#27) = true := by decide
    have hsz : (if (39 == 32 : Bool) then 4 else 8) = 8 := rfl
    have hpte : tlb_get_pte 8 (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64) = 0x00000000200400c7#64 := by decide
    have hperm : (check_PTE_permission (.Load .Data) .Supervisor false false
        (Mk_PTE_Flags (Sail.BitVec.extractLsb 0x00000000200400c7#64 7 0))
        (ext_bits_of_PTE 0x00000000200400c7#64) ()).run sHit = .ok (.PTE_Check_Success ()) sHit := rfl
    have hnone : update_PTE_Bits 0x00000000200400c7#64 (.Load .Data) = none := by decide
    have hppn : tlb_get_ppn 39 (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64) 0x0040403#27 = 0x00000080100#44 := by decide
    have hpbmt : (tlb_get_pbmt (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64)).run sHit = .ok .PBMT_PMA sHit := rfl
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get] at hperm hpbmt ⊢
    rw [htlbHit]
    dsimp only [EStateM.pure]
    rw [hidx, hget]
    dsimp only
    rw [hmatch]
    simp only [ite_true]
    dsimp only [EStateM.pure, EStateM.bind]
    rw [hsz, hpte, hperm]
    dsimp only [EStateM.bind, EStateM.pure]
    rw [hnone]
    dsimp only [EStateM.pure, EStateM.bind]
    rw [hpbmt, hppn]
  · unfold translateAddr effectivePrivilege translationMode is_shadow_stack_access bits_of_virtaddr
    have hmprv : (_get_Mstatus_MPRV rv64SupervisorSv39Mstatus == 1#1) = false := by decide
    dsimp only [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.mk,
      ExceptT.bind, ExceptT.pure, ExceptT.lift, ExceptT.bindCont,
      MonadLift.monadLift, liftM, monadLift, Functor.map, EStateM.map,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
    rw [hmachMstatus]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, EStateM.get, ExceptT.bindCont]
    rw [hmachPriv]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    simp only [hmprv]
    rfl
  · unfold translateAddr effectivePrivilege is_shadow_stack_access
      satp_mode_width_forwards translationException bits_of_virtaddr
    have hmprv : (_get_Mstatus_MPRV rv64SupervisorSv39Mstatus == 1#1) = false := by decide
    have hbareF : (SATPMode.Sv39 == SATPMode.Bare) = false := by decide
    have hxlen : (((39 : Int) == 32 : Bool) || (LeanRV64D.Functions.xlen == 64)) = true := by decide
    have hnoncanon : (0x0001000000000000#64 !=
        sign_extend (m := 64) (Sail.BitVec.extractLsb 0x0001000000000000#64 ((39 : Int) -i 1) 0)) = true := by decide
    dsimp only [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.mk,
      ExceptT.bind, ExceptT.pure, ExceptT.lift, ExceptT.bindCont,
      MonadLift.monadLift, liftM, monadLift, Functor.map, EStateM.map,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get,
      assert, PreSail.assert] at hmodeSup hgetSatp39 ⊢
    rw [hsupMstatus]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, EStateM.get, ExceptT.bindCont]
    rw [hsupPriv]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    simp only [hmprv, Bool.and_false, Bool.false_eq_true, ite_false]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [hmodeSup]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont, Int.toNat]
    simp only [hbareF, Bool.false_eq_true, ite_false]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont, Int.toNat]
    rw [hgetSatp39]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    simp only [hxlen, ite_true]
    rfl
  · unfold translateAddr effectivePrivilege is_shadow_stack_access
      satp_mode_width_forwards translationException bits_of_virtaddr
    have hmprv : (_get_Mstatus_MPRV rv64SupervisorSv39Mstatus == 1#1) = false := by decide
    have hbareF : (SATPMode.Sv39 == SATPMode.Bare) = false := by decide
    have hxlen : (((39 : Int) == 32 : Bool) || (LeanRV64D.Functions.xlen == 64)) = true := by decide
    dsimp only [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.mk,
      ExceptT.bind, ExceptT.pure, ExceptT.lift, ExceptT.bindCont,
      MonadLift.monadLift, liftM, monadLift, Functor.map, EStateM.map,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get,
      assert, PreSail.assert] at hmodeSup hgetSatp39 ⊢
    rw [hsupMstatus]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, EStateM.get, ExceptT.bindCont]
    rw [hsupPriv]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    simp only [hmprv, Bool.and_false, Bool.false_eq_true, ite_false]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [hmodeSup]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont, Int.toNat]
    simp only [hbareF, Bool.false_eq_true, ite_false]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont, Int.toNat]
    rw [hgetSatp39]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    simp only [hxlen, ite_true]
    rfl
  · unfold translateAddr effectivePrivilege is_shadow_stack_access
      satp_mode_width_forwards translationException bits_of_virtaddr
    have hmprv : (((MemoryAccessType.InstructionFetch () : MemoryAccessType mem_payload) != MemoryAccessType.InstructionFetch ()) &&
        (_get_Mstatus_MPRV rv64SupervisorSv39Mstatus == 1#1)) = false := by decide
    have hbareF : (SATPMode.Sv39 == SATPMode.Bare) = false := by decide
    have hxlen : (((39 : Int) == 32 : Bool) || (LeanRV64D.Functions.xlen == 64)) = true := by decide
    dsimp only [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.mk,
      ExceptT.bind, ExceptT.pure, ExceptT.lift, ExceptT.bindCont,
      MonadLift.monadLift, liftM, monadLift, Functor.map, EStateM.map,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get,
      assert, PreSail.assert] at hmodeSup hgetSatp39 ⊢
    rw [hsupMstatus]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, EStateM.get, ExceptT.bindCont]
    rw [hsupPriv]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    simp only [hmprv, Bool.false_eq_true, ite_false]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [hmodeSup]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont, Int.toNat]
    simp only [hbareF, Bool.false_eq_true, ite_false]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont, Int.toNat]
    rw [hgetSatp39]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    simp only [hxlen, ite_true]
    rfl
  · dsimp only
    let tlbFilled : RegisterType .tlb :=
      vectorUpdate (vectorInit (n := 64) none) 3 (some (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64))
    have hmissRun : (translate_TLB_miss 39 0x0001#16 0x00000080001#44 0x0040403#27 (.Load .Data) .Supervisor false false ()).run sSup =
        .ok (.Ok (0x00000080100#44, .PBMT_PMA, ())) { sSup with regs := sSup.regs.insert .tlb tlbFilled } := by
      have hwalk := pt_walk_sv39_4k_std_run 0#1 sSup hstdSup hsup_l2 hsup_l1 hsup_l0
      unfold translate_TLB_miss add_to_TLB update_and_write_pte
      have hlvl : (if (39 == 32 : Bool) then 1 else if (39 == 39 : Bool) then 2 else if (39 == 48 : Bool) then 3 else 4) = 2 := rfl
      have hsz : (if (39 == 32 : Bool) then 4 else 8) = 8 := rfl
      have hnone8 : update_PTE_Bits
          (@BitVec.setWidth (if decide (39 = 32) = true then 32 else 64) (8 * 8)
            (let p : BitVec (if decide (39 = 32) = true then 32 else 64) := 0x00000000200400c7#64; p))
          (.Load .Data) = none := by decide
      have hidx : tlb_hash 39 0x0040403#27 = 3 := by decide
      dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet, EStateM.run,
        readReg, writeReg, PreSail.readReg, PreSail.writeReg, tlb_add_callback,
        get, getThe, MonadStateOf.get, modifyGet, MonadStateOf.modifyGet] at hwalk ⊢
      rw [hlvl, hsz, hwalk]
      dsimp only [EStateM.bind]
      rw [hnone8]
      dsimp only [EStateM.pure, EStateM.bind, EStateM.get, EStateM.modifyGet, modify]
      rw [hsupTlb, hidx]
      dsimp only [EStateM.pure, EStateM.bind, EStateM.get, EStateM.modifyGet, modifyGet]
      let p_ppn : BitVec (if decide (39 = 32) = true then 22 else 44) := 0x00000080100#44
      let p_pte : BitVec (if decide (39 = 32) = true then 32 else 64) := 0x00000000200400c7#64
      have h_vpn : sign_extend (m := (57 -i 12))
          (0x0040403#27 &&& BitVec.setWidth (39 - 12) (Complement.complement (zero_extend (m := (39 -i 12)) (ones (n := ((0 : Nat) *i (if (39 == 32 : Bool) then 10 else 9))))))) =
          (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64).vpn := by decide
      have h_lmask : zero_extend (m := (57 -i 12)) (ones (n := ((0 : Nat) *i (if (39 == 32 : Bool) then 10 else 9)))) =
          (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64).levelMask := by decide
      have h_ppn : zero_extend (m := 44)
          (HAnd.hAnd (α := BitVec (if decide (39 = 32) = true then 22 else 44))
            (β := BitVec (if (39 == 32 : Bool) then 22 else 44))
            p_ppn
            (Complement.complement (zero_extend (m := (if (39 == 32 : Bool) then 22 else 44)) (ones (n := ((0 : Nat) *i (if (39 == 32 : Bool) then 10 else 9))))))) =
          (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64).ppn := by decide
      have h_pte : zero_extend (m := 64) p_pte =
          (rv64Sv39TlbEntry4k 0x0001#16 0x00000000200400c7#64).pte := by decide
      have hins : vectorUpdate (vectorInit (n := 64) none) 3
          (some ({
            asid := 0x0001#16
            global := false
            pte := zero_extend (m := 64) p_pte
            pteAddr := .Physaddr 0x0000000080003018#64
            levelMask := zero_extend (m := (57 -i 12)) (ones (n := ((0 : Nat) *i (if (39 == 32 : Bool) then 10 else 9))))
            vpn := sign_extend (m := (57 -i 12))
              (0x0040403#27 &&& BitVec.setWidth (39 - 12) (Complement.complement (zero_extend (m := (39 -i 12)) (ones (n := ((0 : Nat) *i (if (39 == 32 : Bool) then 10 else 9)))))))
            ppn := zero_extend (m := 44)
              (HAnd.hAnd (α := BitVec (if decide (39 = 32) = true then 22 else 44))
                (β := BitVec (if (39 == 32 : Bool) then 22 else 44))
                p_ppn
                (Complement.complement (zero_extend (m := (if (39 == 32 : Bool) then 22 else 44)) (ones (n := ((0 : Nat) *i (if (39 == 32 : Bool) then 10 else 9)))))))
          } : TLB_Entry)) = tlbFilled := by
        unfold tlbFilled
        rw [h_vpn, h_lmask, h_ppn, h_pte]
        rfl
      rw [hins]
      dsimp only [modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.bind, EStateM.pure]
      have hgetAfter : (sSup.regs.insert .tlb tlbFilled).get? .tlb = some tlbFilled :=
        Std.ExtDHashMap.get?_insert_self
      rw [hgetAfter]
      rfl
    have htrRun : (translate 39
        (zero_extend (m := 16)
          (satp_to_asid (@BitVec.setWidth 64 (if decide (39 = 32) = true then 32 else 64) rv64SupervisorSv39Satp)))
        (@satp_to_ppn (if decide (39 = 32) = true then 32 else 64)
          (@BitVec.setWidth 64 (if decide (39 = 32) = true then 32 else 64) rv64SupervisorSv39Satp))
        (Sail.BitVec.extractLsb
          (Sail.BitVec.extractLsb 0x0000000040403abc#64 ((39 : Int) -i 1) 0)
          ((39 : Int) -i 1) LeanRV64D.Functions.pagesize_bits)
        (.Load .Data) .Supervisor false false init_ext_ptw).run sSup =
        .ok (.Ok (0x00000080100#44, .PBMT_PMA, ())) { sSup with regs := sSup.regs.insert .tlb tlbFilled } := by
      unfold translate lookup_TLB init_ext_ptw
      have h_asid16 : ((zero_extend (m := 16)
          (satp_to_asid (@BitVec.setWidth 64 (if decide (39 = 32) = true then 32 else 64) rv64SupervisorSv39Satp))) :
          BitVec (if decide (64 = 32) = true then 9 else 16)) =
          0x0001#16 := by decide
      have h_ppn44 : (@satp_to_ppn (if decide (39 = 32) = true then 32 else 64)
          (@BitVec.setWidth 64 (if decide (39 = 32) = true then 32 else 64) rv64SupervisorSv39Satp) :
          BitVec (if decide (39 = 32) = true then 22 else 44)) =
          0x00000080001#44 := by decide
      have h_vpn27 : ((Sail.BitVec.extractLsb
          (Sail.BitVec.extractLsb 0x0000000040403abc#64 ((39 : Int) -i 1) 0)
          ((39 : Int) -i 1) LeanRV64D.Functions.pagesize_bits) : BitVec (39 - 12)) =
          0x0040403#27 := by decide
      rw [h_asid16, h_ppn44, h_vpn27]
      have hidx : tlb_hash 39 0x0040403#27 = 3 := by decide
      have hget : (vectorInit (n := 64) (none : Option TLB_Entry))[3]! = none := by
        unfold vectorInit; simp
      dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
        readReg, PreSail.readReg, get, getThe, MonadStateOf.get] at hmissRun ⊢
      rw [hsupTlb]
      dsimp only [EStateM.pure]
      rw [hidx, hget]
      exact hmissRun
    unfold translateAddr effectivePrivilege is_shadow_stack_access
      satp_mode_width_forwards bits_of_virtaddr
    have hmprv : (_get_Mstatus_MPRV rv64SupervisorSv39Mstatus == 1#1) = false := by decide
    have hbareF : (SATPMode.Sv39 == SATPMode.Bare) = false := by decide
    have hmxr : (_get_Mstatus_MXR rv64SupervisorSv39Mstatus == 1#1) = false := by decide
    have hsum : (_get_Mstatus_SUM rv64SupervisorSv39Mstatus == 1#1) = false := by decide
    dsimp only [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.mk,
      ExceptT.bind, ExceptT.pure, ExceptT.lift, ExceptT.bindCont,
      MonadLift.monadLift, liftM, monadLift, Functor.map, EStateM.map,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get,
      assert, PreSail.assert] at hmodeSup hgetSatp39 htrRun ⊢
    rw [hsupMstatus]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, EStateM.get, ExceptT.bindCont]
    rw [hsupPriv]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    simp only [hmprv, Bool.and_false, Bool.false_eq_true, ite_false]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [hmodeSup]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    simp only [hbareF, Bool.false_eq_true, ite_false]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    have hgetSatp39' : get_satp ((39 : Int) : Nat) sSup =
        EStateM.Result.ok (BitVec.setWidth (if decide (((39 : Int) : Nat) = 32) = true then 32 else 64) rv64SupervisorSv39Satp) sSup :=
      hgetSatp39
    have htrRun' : (translate ((39 : Int) : Nat)
        (zero_extend (m := 16)
          (satp_to_asid (@BitVec.setWidth 64 (if decide (((39 : Int) : Nat) = 32) = true then 32 else 64) rv64SupervisorSv39Satp)))
        (BitVec.setWidth (if decide (Int.toNat 39 = 32) = true then 22 else 44)
          (@satp_to_ppn (if decide (((39 : Int) : Nat) = 32) = true then 32 else 64)
            (@BitVec.setWidth 64 (if decide (((39 : Int) : Nat) = 32) = true then 32 else 64) rv64SupervisorSv39Satp)))
        (BitVec.setWidth (Int.toNat 39 - 12)
          (Sail.BitVec.extractLsb
            (Sail.BitVec.extractLsb 0x0000000040403abc#64 ((39 : Int) -i 1) 0)
            ((39 : Int) -i 1) LeanRV64D.Functions.pagesize_bits))
        (.Load .Data) .Supervisor false false init_ext_ptw).run sSup =
        .ok (.Ok (0x00000080100#44, .PBMT_PMA, ())) { sSup with regs := sSup.regs.insert .tlb tlbFilled } :=
      htrRun
    dsimp only [EStateM.run, CoeT.coe] at hgetSatp39' htrRun' ⊢
    rw [hgetSatp39']
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [if_pos (by decide)]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont]
    rw [if_neg (by decide)]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, EStateM.get, ExceptT.bindCont]
    rw [hsupMstatus]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, EStateM.get, ExceptT.bindCont]
    rw [hsupMstatus]
    dsimp only [EStateM.pure, EStateM.bind, EStateM.map, ExceptT.bindCont, CoeT.coe] at htrRun' ⊢
    rw [hmxr, hsum, htrRun']
    dsimp only [EStateM.pure, CoeT.coe]
    unfold LeanRV64D.Functions.pagesize_bits tlbFilled
    rfl

/-! ## Section 15: Trap Vectoring, Exception Delegation, Interrupt Priority & Dispatch, Trap Entry, `MRET` & `SRET` -/

def rv64StandardMisaSU : BitVec 64 :=
  (0b10#64 <<< 62) ||| (1#64 <<< 18) ||| (1#64 <<< 20)

def rv64StandardMisaSUC : BitVec 64 :=
  rv64StandardMisaSU ||| (1#64 <<< 2)

def rv64TvecAddrSpec (tvec cause : BitVec 64) : Option (BitVec 64) :=
  let base := Sail.BitVec.extractLsb tvec 63 2 +++ 0b00#2
  match Sail.BitVec.extractLsb tvec 1 0 with
  | 0b00#2 => some base
  | 0b01#2 =>
    if Sail.BitVec.extractLsb cause 63 63 == 1#1 then
      some (base + (BitVec.zeroExtend 64 (Sail.BitVec.extractLsb cause 62 0) <<< 2))
    else
      some base
  | _ => none

private theorem hartSupports_Ext_S : hartSupports .Ext_S = true := by
  rw [hartSupports.eq_def]

private theorem hartSupports_Ext_U : hartSupports .Ext_U = true := by
  rw [hartSupports.eq_def]

private theorem hartSupports_Ext_Zicsr : hartSupports .Ext_Zicsr = true := by
  rw [hartSupports.eq_def]

private theorem hartSupports_Ext_F : hartSupports .Ext_F = true := by
  rw [hartSupports.eq_def]

private theorem hartSupports_Ext_D : hartSupports .Ext_D = true := by
  rw [hartSupports.eq_def]
  rw [hartSupports_Ext_F]
  rfl

private theorem hartSupports_Ext_Zca : hartSupports .Ext_Zca = true := by
  rw [hartSupports.eq_def]

private theorem hartSupports_Ext_Zcd : hartSupports .Ext_Zcd = true := by
  rw [hartSupports.eq_def]

private theorem hartSupports_Ext_Zcf : hartSupports .Ext_Zcf = false := by
  rw [hartSupports.eq_def]; decide

private theorem hartSupports_Ext_C : hartSupports .Ext_C = true := by
  rw [hartSupports.eq_def]
  simp only [hartSupports_Ext_Zca, hartSupports_Ext_Zcf, hartSupports_Ext_F,
    hartSupports_Ext_Zcd, hartSupports_Ext_D]
  decide

private theorem hartSupports_Ext_Zicfilp : hartSupports .Ext_Zicfilp = true := by
  rw [hartSupports.eq_def]

private theorem currentlyEnabled_Ext_S_standard (s : SequentialState RegisterType trivialChoiceSource)
    (misaVal : BitVec 64) (hmisa : s.regs.get? .misa = some misaVal)
    (hs : _get_Misa_S misaVal = 1#1) :
    (currentlyEnabled .Ext_S).run s = .ok true s := by
  rw [currentlyEnabled.eq_def]
  dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
    readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
  rw [currentlyEnabled.eq_def]
  dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run]
  rw [hmisa]
  dsimp only [EStateM.bind, EStateM.pure]
  rw [hs, hartSupports_Ext_S, hartSupports_Ext_Zicsr]
  rfl

private theorem currentlyEnabled_Ext_U_standard (s : SequentialState RegisterType trivialChoiceSource)
    (misaVal : BitVec 64) (hmisa : s.regs.get? .misa = some misaVal)
    (hu : _get_Misa_U misaVal = 1#1) :
    (currentlyEnabled .Ext_U).run s = .ok true s := by
  rw [currentlyEnabled.eq_def]
  dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
    readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
  rw [currentlyEnabled.eq_def]
  dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run]
  rw [hmisa]
  dsimp only [EStateM.bind, EStateM.pure]
  rw [hu, hartSupports_Ext_U, hartSupports_Ext_Zicsr]
  rfl

private theorem currentlyEnabled_Ext_Zca_of_misa_C (s : SequentialState RegisterType trivialChoiceSource)
    (misaVal : BitVec 64) (hmisa : s.regs.get? .misa = some misaVal) :
    (currentlyEnabled .Ext_Zca).run s = .ok (_get_Misa_C misaVal == 1#1) s := by
  rw [currentlyEnabled.eq_def]
  dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
    readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
  rw [currentlyEnabled.eq_def]
  dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
    readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
  rw [hmisa]
  dsimp only [EStateM.bind, EStateM.pure]
  rw [hartSupports_Ext_Zca, hartSupports_Ext_C]
  cases (_get_Misa_C misaVal == 1#1) <;> rfl

/-- Direct `SailM` & pure bisimulation for `tvec_addr`, `legalize_xepc`, `align_pc`, `get_xepc`,
    `set_xepc`, `prepare_xret_target`, and `prepare_trap_vector` (`SysRegs.lean` lines 1296–1315,
    `SysExceptions.lean` lines 227–266):
    1. `tvec_addr tvec cause = rv64TvecAddrSpec tvec cause` across Direct (`0b00`), Vectored (`0b01`,
       adding `4 * cause[62:0]` iff `IsInterrupt = 1` and leaving synchronous exceptions unshifted),
       and Reserved (`0b10` / `0b11` -> `none`) modes;
    2. `legalize_xepc v = BitVec.update v 0 0#1` (since `hartSupports Ext_Zca = true`), while
       `align_pc addr` clears bit `0` when `misa.C = 1` (`Ext_Zca` enabled) and clears bits `[1:0]`
       when `misa.C = 0` (`Ext_Zca` disabled);
    3. `set_xepc` writes `legalize_xepc value` to `mepc`/`sepc`, `prepare_xret_target` (= `get_xepc`)
       reads `mepc`/`sepc` through `align_pc`, and `prepare_trap_vector` computes the trap PC from
       `mtvec`/`stvec` on Direct/Vectored modes. -/
theorem rv64TrapVectorAndXepc_bisim_sail (tvec cause v : BitVec 64)
    (sZca sNoC : SequentialState RegisterType trivialChoiceSource)
    (hmisaZca : sZca.regs.get? .misa = some rv64StandardMisaSUC)
    (hmisaNoC : sNoC.regs.get? .misa = some rv64StandardMisaSU)
    (hmtvec : sZca.regs.get? .mtvec = some 0x0000000080001001#64)
    (hstvec : sNoC.regs.get? .stvec = some 0x0000000080002000#64) :
    tvec_addr tvec cause = rv64TvecAddrSpec tvec cause ∧
    legalize_xepc v = BitVec.update v 0 0#1 ∧
    (align_pc v).run sZca = .ok (BitVec.update v 0 0#1) sZca ∧
    (align_pc v).run sNoC = .ok (Sail.BitVec.updateSubrange v 1 0 0b00#2) sNoC ∧
    ((do
        let _ ← set_xepc .Machine 0x0000000080000103#64
        prepare_xret_target .Machine).run sZca) =
      .ok 0x0000000080000102#64 { sZca with regs := sZca.regs.insert .mepc 0x0000000080000102#64 } ∧
    ((do
        let _ ← set_xepc .Supervisor 0x0000000080000102#64
        prepare_xret_target .Supervisor).run sNoC) =
      .ok 0x0000000080000100#64 { sNoC with regs := sNoC.regs.insert .sepc 0x0000000080000102#64 } ∧
    (prepare_trap_vector .Machine ((1#64 <<< 63) ||| 7#64)).run sZca =
      .ok 0x000000008000101c#64 sZca ∧
    (prepare_trap_vector .Supervisor 2#64).run sNoC =
      .ok 0x0000000080002000#64 sNoC := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold tvec_addr rv64TvecAddrSpec _get_Mtvec_Base _get_Mtvec_Mode
      trapVectorMode_forwards _get_Mcause_IsInterrupt _get_Mcause_Cause
      zero_extend Sail.BitVec.zeroExtend
    dsimp only [CoeT.coe]
    rcases hp : Sail.BitVec.extractLsb tvec 1 0 with ⟨⟨m, hm⟩⟩
    have hm4 : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
    rcases hm4 with rfl | rfl | rfl | rfl <;> rfl
  · unfold legalize_xepc
    rw [hartSupports_Ext_Zca]; rfl
  · have hce := currentlyEnabled_Ext_Zca_of_misa_C sZca rv64StandardMisaSUC hmisaZca
    have hc1 : (_get_Misa_C rv64StandardMisaSUC == 1#1) = true := by decide
    unfold align_pc
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run] at hce ⊢
    rw [hce, hc1]
    rfl
  · have hce := currentlyEnabled_Ext_Zca_of_misa_C sNoC rv64StandardMisaSU hmisaNoC
    have hc0 : (_get_Misa_C rv64StandardMisaSU == 1#1) = false := by decide
    unfold align_pc zeros
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.run, CoeT.coe] at hce ⊢
    rw [hce, hc0]
    rfl
  · have hmepcEq : legalize_xepc 0x0000000080000103#64 = 0x0000000080000102#64 := by
      unfold legalize_xepc; rw [hartSupports_Ext_Zca]; decide
    let sZca' := { sZca with regs := sZca.regs.insert .mepc 0x0000000080000102#64 }
    have hmisa' : sZca'.regs.get? .misa = some rv64StandardMisaSUC := by
      simpa [sZca', Std.ExtDHashMap.get?_insert] using hmisaZca
    have hce := currentlyEnabled_Ext_Zca_of_misa_C sZca' rv64StandardMisaSUC hmisa'
    have hc1 : (_get_Misa_C rv64StandardMisaSUC == 1#1) = true := by decide
    unfold set_xepc prepare_xret_target get_xepc align_pc
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet,
      EStateM.run, writeReg, PreSail.writeReg, readReg, PreSail.readReg,
      modify, modifyGet, MonadStateOf.modifyGet, get, getThe, MonadStateOf.get] at hce ⊢
    rw [hmepcEq]
    simp only [Std.ExtDHashMap.get?_insert_self]
    dsimp only [EStateM.pure]
    rw [hce, hc1]; dsimp only []; rw [if_pos rfl]
    have hupd : BitVec.update 0x0000000080000102#64 0 0#1 = 0x0000000080000102#64 := by decide
    rw [hupd]; rfl
  · have hsepcEq : legalize_xepc 0x0000000080000102#64 = 0x0000000080000102#64 := by
      unfold legalize_xepc; rw [hartSupports_Ext_Zca]; decide
    let sNoC' := { sNoC with regs := sNoC.regs.insert .sepc 0x0000000080000102#64 }
    have hmisa' : sNoC'.regs.get? .misa = some rv64StandardMisaSU := by
      simpa [sNoC', Std.ExtDHashMap.get?_insert] using hmisaNoC
    have hce := currentlyEnabled_Ext_Zca_of_misa_C sNoC' rv64StandardMisaSU hmisa'
    have hc0 : (_get_Misa_C rv64StandardMisaSU == 1#1) = false := by decide
    unfold set_xepc prepare_xret_target get_xepc align_pc
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet,
      EStateM.run, writeReg, PreSail.writeReg, readReg, PreSail.readReg,
      modify, modifyGet, MonadStateOf.modifyGet, get, getThe, MonadStateOf.get] at hce ⊢
    rw [hsepcEq]
    simp only [Std.ExtDHashMap.get?_insert_self]
    dsimp only [EStateM.pure]
    rw [hce, hc0]; dsimp only []; rw [if_neg Bool.false_ne_true]
    have hupd : Sail.BitVec.updateSubrange 0x0000000080000102#64 1 0 (zeros (n := 1 -i (0 -i 1))) =
        0x0000000080000100#64 := by decide
    rw [hupd]; rfl
  · unfold prepare_trap_vector
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
    rw [hmtvec]
    have htv : tvec_addr 0x0000000080001001#64 ((1#64 <<< 63) ||| 7#64) =
        some 0x000000008000101c#64 := by decide
    dsimp only [EStateM.bind, EStateM.pure]
    rw [htv]
    rfl
  · unfold prepare_trap_vector
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
    rw [hstvec]
    have htv : tvec_addr 0x0000000080002000#64 2#64 = some 0x0000000080002000#64 := by decide
    dsimp only [EStateM.bind, EStateM.pure]
    rw [htv]
    rfl

/-- Direct `SailM` & pure bisimulation for `exception_delegatee`, `xtval_exception_value`,
    `make_sync_exception`, and `tval` (`SysControl.lean`, lines 556–566, 622–626, 725–760):
    1. `exception_delegatee e .Machine` never delegates downward (`Machine`), regardless of `medeleg`;
    2. `exception_delegatee e .User` and `exception_delegatee e .Supervisor` delegate to `Supervisor`
       when `Ext_S` is enabled and `medeleg[cause] = 1`, and trap to `Machine` when `medeleg[cause] = 0`;
    3. `make_sync_exception` populates `excinfo = some xtval` for fault/illegal/breakpoint exceptions
       (`E_Illegal_Instr`, `E_Load_Page_Fault`, `E_SAMO_Page_Fault`, `E_Fetch_Page_Fault`) and
       `excinfo = none` for environment calls (`E_U_EnvCall`, `E_S_EnvCall`, `E_M_EnvCall`), while
       `tval` unwraps `Option (BitVec 64)` with `0#64` default. -/
theorem rv64ExceptionDelegateeAndSyncExc_bisim_sail (xtval : BitVec 64)
    (sDeleg sNoDeleg : SequentialState RegisterType trivialChoiceSource)
    (hmisaD : sDeleg.regs.get? .misa = some rv64StandardMisaSU)
    (hmisaN : sNoDeleg.regs.get? .misa = some rv64StandardMisaSU)
    (hmedelegD : sDeleg.regs.get? .medeleg = some ((1#64 <<< 8) ||| (1#64 <<< 13)))
    (hmedelegN : sNoDeleg.regs.get? .medeleg = some 0#64) :
    (exception_delegatee (.E_U_EnvCall ()) .Machine).run sDeleg = .ok .Machine sDeleg ∧
    (exception_delegatee (.E_U_EnvCall ()) .User).run sDeleg = .ok .Supervisor sDeleg ∧
    (exception_delegatee (.E_Load_Page_Fault ()) .Supervisor).run sDeleg = .ok .Supervisor sDeleg ∧
    (exception_delegatee (.E_U_EnvCall ()) .User).run sNoDeleg = .ok .Machine sNoDeleg ∧
    make_sync_exception (.E_Load_Page_Fault ()) xtval =
      { trap := .E_Load_Page_Fault (), excinfo := some xtval, ext := none } ∧
    make_sync_exception (.E_Illegal_Instr ()) xtval =
      { trap := .E_Illegal_Instr (), excinfo := some xtval, ext := none } ∧
    make_sync_exception (.E_U_EnvCall ()) xtval =
      { trap := .E_U_EnvCall (), excinfo := none, ext := none } ∧
    make_sync_exception (.E_M_EnvCall ()) xtval =
      { trap := .E_M_EnvCall (), excinfo := none, ext := none } ∧
    tval (some xtval) = xtval ∧
    tval none = 0#64 := by
  have hceD := currentlyEnabled_Ext_S_standard sDeleg rv64StandardMisaSU hmisaD (by decide)
  have hceN := currentlyEnabled_Ext_S_standard sNoDeleg rv64StandardMisaSU hmisaN (by decide)
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · unfold exception_delegatee
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get] at hceD ⊢
    rw [hmedelegD]
    dsimp only [EStateM.bind, EStateM.pure]
    rw [hceD]
    dsimp only []
    have hc : (true && bit_to_bool (BitVec.access (1#64 <<< 8 ||| 1#64 <<< 13)
        (Sail.BitVec.toNatInt (exceptionType_bits_forwards (.E_U_EnvCall ()))).toNat)) = true := by decide
    have hlt : zopz0zI_u (privLevel_to_bits .Supervisor) (privLevel_to_bits .Machine) = true := by decide
    rw [hc, if_pos rfl]
    dsimp only [EStateM.bind, EStateM.pure]
    rw [hlt]; rfl
  · unfold exception_delegatee
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get] at hceD ⊢
    rw [hmedelegD]
    dsimp only [EStateM.bind, EStateM.pure]
    rw [hceD]
    dsimp only []
    have hc : (true && bit_to_bool (BitVec.access (1#64 <<< 8 ||| 1#64 <<< 13)
        (Sail.BitVec.toNatInt (exceptionType_bits_forwards (.E_U_EnvCall ()))).toNat)) = true := by decide
    have hlt : zopz0zI_u (privLevel_to_bits .Supervisor) (privLevel_to_bits .User) = false := by decide
    rw [hc, if_pos rfl]
    dsimp only [EStateM.bind, EStateM.pure]
    rw [hlt]; rfl
  · unfold exception_delegatee
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get] at hceD ⊢
    rw [hmedelegD]
    dsimp only [EStateM.bind, EStateM.pure]
    rw [hceD]
    dsimp only []
    have hc : (true && bit_to_bool (BitVec.access (1#64 <<< 8 ||| 1#64 <<< 13)
        (Sail.BitVec.toNatInt (exceptionType_bits_forwards (.E_Load_Page_Fault ()))).toNat)) = true := by decide
    have hlt : zopz0zI_u (privLevel_to_bits .Supervisor) (privLevel_to_bits .Supervisor) = false := by decide
    rw [hc, if_pos rfl]
    dsimp only [EStateM.bind, EStateM.pure]
    rw [hlt]; rfl
  · unfold exception_delegatee
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get] at hceN ⊢
    rw [hmedelegN]
    dsimp only [EStateM.bind, EStateM.pure]
    rw [hceN]
    dsimp only []
    have hc : (true && bit_to_bool (BitVec.access 0#64
        (Sail.BitVec.toNatInt (exceptionType_bits_forwards (.E_U_EnvCall ()))).toNat)) = false := by decide
    have hlt : zopz0zI_u (privLevel_to_bits .Machine) (privLevel_to_bits .User) = false := by decide
    rw [hc, if_neg Bool.false_ne_true]
    dsimp only [EStateM.bind, EStateM.pure]
    rw [hlt]; rfl

/-- Direct `SailM` & pure bisimulation for RISC-V interrupt priority order (`findPendingInterrupt`)
    and privilege-aware interrupt arbitration (`external_interrupts_pending`, `read_mip`,
    `getPendingSet`, `dispatchInterrupt`; `InterruptRegs.lean` lines 673–686, `SysControl.lean`
    lines 567–621):
    1. Proves the exact architectural priority cascade
       `MEI (11) > MSI (3) > MTI (7) > SEI (9) > SSI (1) > STI (5) > LCOFI (13) > none`;
    2. Proves `dispatchInterrupt` dispatches non-delegated `MTI` to `Machine` when `mstatus.MIE = 1`
       in M-mode, masks non-delegated interrupts in M-mode when `mstatus.MIE = 0`, and dispatches
       `mideleg`-delegated `STI` (or external `sig_seip` `SEI`) to `Supervisor` when executing in
       `Supervisor` (`mstatus.SIE = 1`) or `User` mode. -/
theorem rv64InterruptPriorityAndDispatch_bisim_sail
    (sMOn sMOff sSup : SequentialState RegisterType trivialChoiceSource)
    (hmisaOn : sMOn.regs.get? .misa = some rv64StandardMisaSU)
    (hmidelegOn : sMOn.regs.get? .mideleg = some (1#64 <<< 5))
    (hmipOn : sMOn.regs.get? .mip = some ((1#64 <<< 7) ||| (1#64 <<< 5)))
    (hmieOn : sMOn.regs.get? .mie = some ((1#64 <<< 7) ||| (1#64 <<< 5)))
    (hmeipOn : sMOn.regs.get? .sig_meip = some 0#1)
    (hseipOn : sMOn.regs.get? .sig_seip = some 0#1)
    (hmstatusOn : sMOn.regs.get? .mstatus = some (1#64 <<< 3))
    (hmisaOff : sMOff.regs.get? .misa = some rv64StandardMisaSU)
    (hmidelegOff : sMOff.regs.get? .mideleg = some (1#64 <<< 5))
    (hmipOff : sMOff.regs.get? .mip = some (1#64 <<< 7))
    (hmieOff : sMOff.regs.get? .mie = some (1#64 <<< 7))
    (hmeipOff : sMOff.regs.get? .sig_meip = some 0#1)
    (hseipOff : sMOff.regs.get? .sig_seip = some 0#1)
    (hmstatusOff : sMOff.regs.get? .mstatus = some 0#64)
    (hmisaSup : sSup.regs.get? .misa = some rv64StandardMisaSU)
    (hmidelegSup : sSup.regs.get? .mideleg = some ((1#64 <<< 9) ||| (1#64 <<< 5)))
    (hmipSup : sSup.regs.get? .mip = some (1#64 <<< 5))
    (hmieSup : sSup.regs.get? .mie = some ((1#64 <<< 9) ||| (1#64 <<< 5)))
    (hmeipSup : sSup.regs.get? .sig_meip = some 0#1)
    (hseipSup : sSup.regs.get? .sig_seip = some 1#1)
    (hmstatusSup : sSup.regs.get? .mstatus = some (1#64 <<< 1)) :
    findPendingInterrupt ((1#64 <<< 11) ||| (1#64 <<< 3) ||| (1#64 <<< 7)) = some .I_M_External ∧
    findPendingInterrupt ((1#64 <<< 3) ||| (1#64 <<< 7) ||| (1#64 <<< 9)) = some .I_M_Software ∧
    findPendingInterrupt ((1#64 <<< 7) ||| (1#64 <<< 9) ||| (1#64 <<< 1)) = some .I_M_Timer ∧
    findPendingInterrupt ((1#64 <<< 9) ||| (1#64 <<< 1) ||| (1#64 <<< 5)) = some .I_S_External ∧
    findPendingInterrupt ((1#64 <<< 1) ||| (1#64 <<< 5) ||| (1#64 <<< 13)) = some .I_S_Software ∧
    findPendingInterrupt ((1#64 <<< 5) ||| (1#64 <<< 13)) = some .I_S_Timer ∧
    findPendingInterrupt (1#64 <<< 13) = some .I_COF ∧
    findPendingInterrupt 0#64 = none ∧
    (dispatchInterrupt .Machine).run sMOn = .ok (some (.I_M_Timer, .Machine)) sMOn ∧
    (dispatchInterrupt .Machine).run sMOff = .ok none sMOff ∧
    (dispatchInterrupt .Supervisor).run sSup = .ok (some (.I_S_External, .Supervisor)) sSup := by
  have hceOn := currentlyEnabled_Ext_S_standard sMOn rv64StandardMisaSU hmisaOn (by decide)
  have hceOff := currentlyEnabled_Ext_S_standard sMOff rv64StandardMisaSU hmisaOff (by decide)
  have hceSup := currentlyEnabled_Ext_S_standard sSup rv64StandardMisaSU hmisaSup (by decide)
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · unfold dispatchInterrupt getPendingSet read_mip external_interrupts_pending
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get] at hceOn ⊢
    rw [hceOn]; dsimp only []; rw [if_pos rfl]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
    rw [hmidelegOn]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
    rw [hmipOn]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
    rw [hmeipOn]; dsimp only [EStateM.bind, EStateM.pure]
    rw [hceOn]; dsimp only []; rw [if_pos rfl]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
    rw [hseipOn]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
    rw [hmieOn]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
    rw [hmieOn]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
    rw [hmstatusOn]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
    rw [hmstatusOn]
    rfl
  · unfold dispatchInterrupt getPendingSet read_mip external_interrupts_pending
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get] at hceOff ⊢
    rw [hceOff]; dsimp only []; rw [if_pos rfl]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
    rw [hmidelegOff]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
    rw [hmipOff]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
    rw [hmeipOff]; dsimp only [EStateM.bind, EStateM.pure]
    rw [hceOff]; dsimp only []; rw [if_pos rfl]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
    rw [hseipOff]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
    rw [hmieOff]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
    rw [hmieOff]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
    rw [hmstatusOff]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
    rw [hmstatusOff]
    rfl
  · unfold dispatchInterrupt getPendingSet read_mip external_interrupts_pending
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get] at hceSup ⊢
    rw [hceSup]; dsimp only []; rw [if_pos rfl]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
    rw [hmidelegSup]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
    rw [hmipSup]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
    rw [hmeipSup]; dsimp only [EStateM.bind, EStateM.pure]
    rw [hceSup]; dsimp only []; rw [if_pos rfl]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
    rw [hseipSup]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
    rw [hmieSup]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
    rw [hmieSup]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
    rw [hmstatusSup]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
    rw [hmstatusSup]
    rfl

private theorem get_xLPE_Supervisor (s : SequentialState RegisterType trivialChoiceSource)
    (menv : BitVec 64) (hmenv : s.regs.get? .menvcfg = some menv) :
    (get_xLPE .Supervisor).run s = .ok (bool_bit_backwards (_get_MEnvcfg_LPE menv)) s := by
  rw [get_xLPE.eq_def]
  dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
    readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
  rw [hmenv]
  rfl

private theorem get_xLPE_Machine (s : SequentialState RegisterType trivialChoiceSource)
    (mseccfgVal : BitVec 64) (hmsec : s.regs.get? .mseccfg = some mseccfgVal) :
    (get_xLPE .Machine).run s = .ok (bool_bit_backwards (_get_Seccfg_MLPE mseccfgVal)) s := by
  rw [get_xLPE.eq_def]
  dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
    readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
  rw [hmsec]
  rfl

private theorem get_xLPE_User_Ext_S (s : SequentialState RegisterType trivialChoiceSource)
    (misaVal menv senv : BitVec 64)
    (hmisa : s.regs.get? .misa = some misaVal)
    (hs : _get_Misa_S misaVal = 1#1)
    (hmenv : s.regs.get? .menvcfg = some menv)
    (hsenv : s.regs.get? .senvcfg = some senv) :
    (get_xLPE .User).run s = .ok (bool_bit_backwards (_get_SEnvcfg_LPE
      (_update_SEnvcfg_SSE senv (_get_MEnvcfg_SSE menv &&& _get_SEnvcfg_SSE senv)))) s := by
  have hce := currentlyEnabled_Ext_S_standard s misaVal hmisa hs
  rw [get_xLPE.eq_def]
  unfold read_senvcfg
  dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
    readReg, PreSail.readReg, get, getThe, MonadStateOf.get] at hce ⊢
  rw [hce]; dsimp only []; rw [if_pos rfl]
  dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
  rw [hsenv]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
  rw [hmenv]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
  rw [hsenv]
  rfl

private theorem csr_name_write_callback_mstatus_raw (v : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource) :
    long_csr_write_callback "mstatus" "mstatush" v s = EStateM.Result.ok () s := rfl

private theorem csr_name_write_callback_mcause_raw (v : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource) :
    csr_name_write_callback "mcause" v s = EStateM.Result.ok () s := rfl

private theorem csr_name_write_callback_mtval_raw (v : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource) :
    csr_name_write_callback "mtval" v s = EStateM.Result.ok () s := rfl

private theorem csr_name_write_callback_mepc_raw (v : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource) :
    csr_name_write_callback "mepc" v s = EStateM.Result.ok () s := rfl

private theorem csr_name_write_callback_scause_raw (v : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource) :
    csr_name_write_callback "scause" v s = EStateM.Result.ok () s := rfl

private theorem csr_name_write_callback_stval_raw (v : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource) :
    csr_name_write_callback "stval" v s = EStateM.Result.ok () s := rfl

private theorem csr_name_write_callback_sepc_raw (v : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource) :
    csr_name_write_callback "sepc" v s = EStateM.Result.ok () s := rfl

private theorem track_trap_Machine_noop (is_int : Bool) (cause : BitVec 6)
    (s : SequentialState RegisterType trivialChoiceSource)
    (vms vmc vmt vme : BitVec 64)
    (hms : s.regs.get? .mstatus = some vms)
    (hmc : s.regs.get? .mcause = some vmc)
    (hmt : s.regs.get? .mtval = some vmt)
    (hme : s.regs.get? .mepc = some vme) :
    (track_trap .Machine is_int cause).run s = .ok () s := by
  unfold track_trap trap_callback
  dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
    readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
  rw [hms]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
  rw [csr_name_write_callback_mstatus_raw]; dsimp only []
  rw [hmc]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
  rw [csr_name_write_callback_mcause_raw]; dsimp only []
  rw [hmt]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
  rw [csr_name_write_callback_mtval_raw]; dsimp only []
  rw [hme]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
  rw [csr_name_write_callback_mepc_raw]

private theorem track_trap_Supervisor_noop (is_int : Bool) (cause : BitVec 6)
    (s : SequentialState RegisterType trivialChoiceSource)
    (vms vsc vst vse : BitVec 64)
    (hms : s.regs.get? .mstatus = some vms)
    (hsc : s.regs.get? .scause = some vsc)
    (hst : s.regs.get? .stval = some vst)
    (hse : s.regs.get? .sepc = some vse) :
    (track_trap .Supervisor is_int cause).run s = .ok () s := by
  unfold track_trap trap_callback
  dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
    readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
  rw [hms]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
  rw [csr_name_write_callback_mstatus_raw]; dsimp only []
  rw [hsc]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
  rw [csr_name_write_callback_scause_raw]; dsimp only []
  rw [hst]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
  rw [csr_name_write_callback_stval_raw]; dsimp only []
  rw [hse]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get]
  rw [csr_name_write_callback_sepc_raw]

/-- Direct end-to-end `SailM` bisimulation for `trap_handler`, `exception_handler`, and
    `handle_exception` (`SysControl.lean` lines 647–764; `ZicfilpRegs.lean` lines 270–282):
    1. Proves `handle_exception` in `Supervisor` mode on non-delegated `E_S_EnvCall` traps to
       `Machine` mode, preserving `elp` in `mstatus.MPELP` (`[41]`) and resetting `elp := 0`,
       writing `mcause := 9` (`IsInterrupt = 0`, `Cause = 9`), `mstatus.MPIE := mstatus.MIE`,
       `mstatus.MIE := 0`, `mstatus.MPP := 0b01` (`Supervisor`), `mtval := 0`, `mepc := PC`,
       `cur_privilege := .Machine`, and redirecting `nextPC` to `mtvec` (`0x8000_1000`);
    2. Proves `handle_exception` in `User` mode on `medeleg`-delegated `E_Load_Page_Fault` (`13`)
       with faulting `vaddr = 0x0000_003F_FFFF_F008` traps to `Supervisor` mode, preserving `elp`
       in `mstatus.SPELP` (`[23]`), writing `scause := 13`, `mstatus.SPIE := mstatus.SIE`,
       `mstatus.SIE := 0`, `mstatus.SPP := 0` (`User`), `stval := vaddr`, `sepc := PC`,
       `cur_privilege := .Supervisor`, and redirecting `nextPC` to `stvec` (`0x8000_2000`);
    3. Proves `trap_handler .Machine (.Interrupt .I_M_Timer)` writes `mcause := (1 <<< 63) ||| 7`
       and computes the vectored handler PC `base + 4 * 7` (`0x8000_101C`). -/
theorem rv64TrapHandlerMachineAndSupervisor_bisim_sail
    (sMach sSup sInt : SequentialState RegisterType trivialChoiceSource)
    (hprivMach : sMach.regs.get? .cur_privilege = some .Supervisor)
    (hpcMach : sMach.regs.get? .PC = some 0x0000000080200040#64)
    (hmisaMach : sMach.regs.get? .misa = some rv64StandardMisaSU)
    (hmedelegMach : sMach.regs.get? .medeleg = some 0#64)
    (helpMach : sMach.regs.get? .elp = some 1#1)
    (hmstatusMach : sMach.regs.get? .mstatus = some (1#64 <<< 3))
    (hmcauseMach : sMach.regs.get? .mcause = some 0#64)
    (hmtvecMach : sMach.regs.get? .mtvec = some 0x0000000080001000#64)
    (hprivSup : sSup.regs.get? .cur_privilege = some .User)
    (hpcSup : sSup.regs.get? .PC = some 0x0000000000010080#64)
    (hmisaSup : sSup.regs.get? .misa = some rv64StandardMisaSU)
    (hmedelegSup : sSup.regs.get? .medeleg = some (1#64 <<< 13))
    (helpSup : sSup.regs.get? .elp = some 1#1)
    (hmstatusSup : sSup.regs.get? .mstatus = some (1#64 <<< 1))
    (hscauseSup : sSup.regs.get? .scause = some 0#64)
    (hstvecSup : sSup.regs.get? .stvec = some 0x0000000080002000#64)
    (hprivInt : sInt.regs.get? .cur_privilege = some .Supervisor)
    (helpInt : sInt.regs.get? .elp = some 0#1)
    (hmstatusInt : sInt.regs.get? .mstatus = some (1#64 <<< 3))
    (hmcauseInt : sInt.regs.get? .mcause = some 0#64)
    (hmtvecInt : sInt.regs.get? .mtvec = some 0x0000000080001001#64) :
    let mstatusMachAfter : BitVec 64 := (1#64 <<< 41) ||| (0b01#64 <<< 11) ||| (1#64 <<< 7)
    let regsMachAfter := (((((((sMach.regs.insert .mstatus (1#64 <<< 41 ||| 1#64 <<< 3)).insert .elp 0#1).insert
        .mcause 0#64).insert .mcause 9#64).insert .mstatus ((1#64 <<< 41) ||| (1#64 <<< 7) ||| (1#64 <<< 3))).insert
        .mstatus ((1#64 <<< 41) ||| (1#64 <<< 7))).insert .mstatus mstatusMachAfter |>.insert
        .mtval 0#64 |>.insert .mepc 0x0000000080200040#64 |>.insert .cur_privilege .Machine |>.insert
        .nextPC 0x0000000080001000#64)
    let mstatusSupAfter : BitVec 64 := (1#64 <<< 23) ||| (1#64 <<< 5)
    let regsSupAfter := (((((((sSup.regs.insert .mstatus (1#64 <<< 23 ||| 1#64 <<< 1)).insert .elp 0#1).insert
        .scause 0#64).insert .scause 13#64).insert .mstatus ((1#64 <<< 23) ||| (1#64 <<< 5) ||| (1#64 <<< 1))).insert
        .mstatus mstatusSupAfter).insert .mstatus mstatusSupAfter |>.insert
        .stval 0x0000003ffffff008#64 |>.insert .sepc 0x0000000000010080#64 |>.insert
        .cur_privilege .Supervisor |>.insert .nextPC 0x0000000080002000#64)
    let mcauseIntAfter : BitVec 64 := (1#64 <<< 63) ||| 7#64
    let mstatusIntAfter : BitVec 64 := (0b01#64 <<< 11) ||| (1#64 <<< 7)
    let regsIntAfter := (((((((sInt.regs.insert .mstatus (1#64 <<< 3)).insert .elp 0#1).insert
        .mcause (1#64 <<< 63)).insert .mcause mcauseIntAfter).insert .mstatus ((1#64 <<< 7) ||| (1#64 <<< 3))).insert
        .mstatus (1#64 <<< 7)).insert .mstatus mstatusIntAfter |>.insert
        .mtval 0#64 |>.insert .mepc 0x0000000080200044#64 |>.insert .cur_privilege .Machine)
    (handle_exception 0xdeadbeef#64 (.E_S_EnvCall ())).run sMach =
      .ok () { sMach with regs := regsMachAfter } ∧
    regsMachAfter.get? .mcause = some 9#64 ∧
    regsMachAfter.get? .mstatus = some mstatusMachAfter ∧
    regsMachAfter.get? .mtval = some 0#64 ∧
    regsMachAfter.get? .mepc = some 0x0000000080200040#64 ∧
    regsMachAfter.get? .nextPC = some 0x0000000080001000#64 ∧
    (handle_exception 0x0000003ffffff008#64 (.E_Load_Page_Fault ())).run sSup =
      .ok () { sSup with regs := regsSupAfter } ∧
    regsSupAfter.get? .scause = some 13#64 ∧
    regsSupAfter.get? .mstatus = some mstatusSupAfter ∧
    regsSupAfter.get? .stval = some 0x0000003ffffff008#64 ∧
    regsSupAfter.get? .sepc = some 0x0000000000010080#64 ∧
    regsSupAfter.get? .nextPC = some 0x0000000080002000#64 ∧
    (trap_handler .Machine (.Interrupt .I_M_Timer) 0x0000000080200044#64 none none).run sInt =
      .ok 0x000000008000101c#64 { sInt with regs := regsIntAfter } := by
  have hceMach := currentlyEnabled_Ext_S_standard sMach rv64StandardMisaSU hmisaMach (by decide)
  have hceSup := currentlyEnabled_Ext_S_standard sSup rv64StandardMisaSU hmisaSup (by decide)
  let sSup2 := { sSup with regs := (sSup.regs.insert .mstatus (1#64 <<< 23 ||| 1#64 <<< 1)).insert .elp 0#1 }
  have hmisaSup2 : sSup2.regs.get? .misa = some rv64StandardMisaSU := by
    simpa [sSup2, Std.ExtDHashMap.get?_insert] using hmisaSup
  have hceSup2 := currentlyEnabled_Ext_S_standard sSup2 rv64StandardMisaSU hmisaSup2 (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold handle_exception exception_handler exception_delegatee make_sync_exception
      xtval_exception_value trap_handler zicfilp_preserve_elp_on_trap reset_elp
      prepare_trap_vector set_next_pc get_config_print_exception get_config_print_interrupt
      tval handle_trap_extension redirect_callback sail_branch_announce
    rw [hartSupports_Ext_Zicfilp]
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet,
      EStateM.run, readReg, PreSail.readReg, writeReg, PreSail.writeReg,
      modify, modifyGet, MonadStateOf.modifyGet, get, getThe, MonadStateOf.get] at hceMach ⊢
    rw [hprivMach]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hpcMach]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hmedelegMach]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hceMach]; dsimp only []
    have hc0 : (true && bit_to_bool (BitVec.access 0#64
        (Sail.BitVec.toNatInt (exceptionType_bits_forwards (.E_S_EnvCall ()))).toNat)) = false := by decide
    have hlt0 : zopz0zI_u (privLevel_to_bits .Machine) (privLevel_to_bits .Supervisor) = false := by decide
    rw [hc0, if_neg Bool.false_ne_true]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hlt0, if_neg Bool.false_ne_true]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    have hf0 : (false || false) = false := rfl
    rw [if_neg Bool.false_ne_true]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hf0, if_neg Bool.false_ne_true]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [if_pos rfl]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hmstatusMach]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [helpMach]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    have hu1 : Sail.BitVec.updateSubrange (1#64 <<< 3) 41 41 1#1 = (1#64 <<< 41 ||| 1#64 <<< 3) := by decide
    have hu2 : landing_pad_bits_backwards .NO_LP_EXPECTED = 0#1 := rfl
    rw [hu1, hu2]
    have hmcRead : (((sMach.regs.insert Register.mstatus (1#64 <<< 41 ||| 1#64 <<< 3)).insert Register.elp 0#1).get?
        Register.mcause) = some 0#64 := by
      simp [Std.ExtDHashMap.get?_insert, hmcauseMach]
    rw [hmcRead]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    have hu3 : Sail.BitVec.updateSubrange 0#64 (64 -i 1) (64 -i 1)
        (bool_to_bit (trapCause_is_interrupt (.Exception (.E_S_EnvCall ())))) = 0#64 := by decide
    have hu4 : Sail.BitVec.updateSubrange 0#64 (64 -i 2) 0
        (zero_extend (m := 64 -i 1) (trapCause_bits_forwards (.Exception (.E_S_EnvCall ())))) = 9#64 := by decide
    have hu5 : Sail.BitVec.updateSubrange (1#64 <<< 41 ||| 1#64 <<< 3) 7 7
        (_get_Mstatus_MIE (1#64 <<< 41 ||| 1#64 <<< 3)) =
        ((1#64 <<< 41) ||| (1#64 <<< 7) ||| (1#64 <<< 3)) := by decide
    have hu6 : Sail.BitVec.updateSubrange ((1#64 <<< 41) ||| (1#64 <<< 7) ||| (1#64 <<< 3)) 3 3 0#1 =
        ((1#64 <<< 41) ||| (1#64 <<< 7)) := by decide
    have hu7 : Sail.BitVec.updateSubrange ((1#64 <<< 41) ||| (1#64 <<< 7)) 12 11
        (privLevel_to_bits .Supervisor) =
        ((1#64 <<< 41) ||| (0b01#64 <<< 11) ||| (1#64 <<< 7)) := by decide
    have hu8 : zeros (n := 64) = 0#64 := rfl
    rw [hu3]
    have hmcRead0M : ((((sMach.regs.insert Register.mstatus (1#64 <<< 41 ||| 1#64 <<< 3)).insert Register.elp 0#1).insert
        Register.mcause 0#64).get? Register.mcause) = some 0#64 := by
      simp [Std.ExtDHashMap.get?_insert_self]
    rw [hmcRead0M]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hu4]
    have hmsRead1 : (((((sMach.regs.insert Register.mstatus (1#64 <<< 41 ||| 1#64 <<< 3)).insert Register.elp 0#1).insert
        Register.mcause 0#64).insert Register.mcause 9#64).get? Register.mstatus) =
        some (1#64 <<< 41 ||| 1#64 <<< 3) := by
      simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
    rw [hmsRead1]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hmsRead1]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hu5]
    have hmsRead2M : ((((((sMach.regs.insert Register.mstatus (1#64 <<< 41 ||| 1#64 <<< 3)).insert Register.elp 0#1).insert
        Register.mcause 0#64).insert Register.mcause 9#64).insert
        Register.mstatus (1#64 <<< 41 ||| 1#64 <<< 7 ||| 1#64 <<< 3)).get? Register.mstatus) =
        some (1#64 <<< 41 ||| 1#64 <<< 7 ||| 1#64 <<< 3) := by
      simp [Std.ExtDHashMap.get?_insert_self]
    rw [hmsRead2M]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hu6]
    have hmsRead3M : (((((((sMach.regs.insert Register.mstatus (1#64 <<< 41 ||| 1#64 <<< 3)).insert Register.elp 0#1).insert
        Register.mcause 0#64).insert Register.mcause 9#64).insert
        Register.mstatus (1#64 <<< 41 ||| 1#64 <<< 7 ||| 1#64 <<< 3)).insert
        Register.mstatus (1#64 <<< 41 ||| 1#64 <<< 7)).get? Register.mstatus) =
        some (1#64 <<< 41 ||| 1#64 <<< 7) := by
      simp [Std.ExtDHashMap.get?_insert_self]
    rw [hmsRead3M]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    have hprivRead : (((((((sMach.regs.insert Register.mstatus (1#64 <<< 41 ||| 1#64 <<< 3)).insert Register.elp 0#1).insert
        Register.mcause 0#64).insert Register.mcause 9#64).insert
        Register.mstatus ((1#64 <<< 41) ||| (1#64 <<< 7) ||| (1#64 <<< 3))).insert
        Register.mstatus ((1#64 <<< 41) ||| (1#64 <<< 7))).get? Register.cur_privilege) =
        some .Supervisor := by
      simp [Std.ExtDHashMap.get?_insert, hprivMach]
    rw [hprivRead]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [if_neg Bool.false_ne_true]
    dsimp only []
    rw [hu7, hu8]
    let stM := { sMach with regs := (((((((sMach.regs.insert .mstatus (1#64 <<< 41 ||| 1#64 <<< 3)).insert .elp 0#1).insert
        .mcause 0#64).insert .mcause 9#64).insert .mstatus ((1#64 <<< 41) ||| (1#64 <<< 7) ||| (1#64 <<< 3))).insert
        .mstatus ((1#64 <<< 41) ||| (1#64 <<< 7))).insert .mstatus ((1#64 <<< 41) ||| (0b01#64 <<< 11) ||| (1#64 <<< 7)) |>.insert
        .mtval 0#64 |>.insert .mepc 0x0000000080200040#64 |>.insert .cur_privilege .Machine) }
    have htt := track_trap_Machine_noop (trapCause_is_interrupt (.Exception (.E_S_EnvCall ())))
      (trapCause_bits_forwards (.Exception (.E_S_EnvCall ()))) stM
      ((1#64 <<< 41) ||| (0b01#64 <<< 11) ||| (1#64 <<< 7)) 9#64 0#64 0x0000000080200040#64
      (by simp [stM, Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self])
      (by simp [stM, Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self])
      (by simp [stM, Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self])
      (by simp [stM, Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self])
    dsimp only [EStateM.run] at htt
    rw [htt]
    dsimp only []
    have hmcPostM : stM.regs.get? .mcause = some 9#64 := by
      simp [stM, Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
    have hmtvPostM : stM.regs.get? .mtvec = some 0x0000000080001000#64 := by
      simp [stM, Std.ExtDHashMap.get?_insert, hmtvecMach]
    rw [hmcPostM]; dsimp only [EStateM.pure]
    rw [hmtvPostM]; dsimp only [EStateM.pure]
    have hu9 : tvec_addr 0x0000000080001000#64 9#64 = some 0x0000000080001000#64 := by decide
    rw [hu9]; rfl
  · simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
  · simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
  · simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
  · simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
  · simp [Std.ExtDHashMap.get?_insert_self]
  · unfold handle_exception exception_handler exception_delegatee make_sync_exception
      xtval_exception_value trap_handler zicfilp_preserve_elp_on_trap reset_elp
      prepare_trap_vector set_next_pc get_config_print_exception get_config_print_interrupt
      tval handle_trap_extension redirect_callback sail_branch_announce
      load_page_fault_writes_xtval assert
    rw [hartSupports_Ext_Zicfilp]
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet,
      EStateM.run, readReg, PreSail.readReg, writeReg, PreSail.writeReg,
      modify, modifyGet, MonadStateOf.modifyGet, get, getThe, MonadStateOf.get] at hceSup hceSup2 ⊢
    rw [hprivSup]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hpcSup]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hmedelegSup]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hceSup]; dsimp only []
    have hc1 : (true && bit_to_bool (BitVec.access (1#64 <<< 13)
        (Sail.BitVec.toNatInt (exceptionType_bits_forwards (.E_Load_Page_Fault ()))).toNat)) = true := by decide
    have hlt1 : zopz0zI_u (privLevel_to_bits .Supervisor) (privLevel_to_bits .User) = false := by decide
    rw [hc1, if_pos rfl]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hlt1, if_neg Bool.false_ne_true]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    have hf0 : (false || false) = false := rfl
    rw [if_neg Bool.false_ne_true]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hf0, if_neg Bool.false_ne_true]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [if_pos rfl]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hmstatusSup]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [helpSup]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    have hu1 : Sail.BitVec.updateSubrange (1#64 <<< 1) 23 23 1#1 = (1#64 <<< 23 ||| 1#64 <<< 1) := by decide
    have hu2 : landing_pad_bits_backwards .NO_LP_EXPECTED = 0#1 := rfl
    rw [hu1, hu2]
    rw [hceSup2]
    dsimp only []; rw [if_pos rfl]
    dsimp only [PreSail.assert]; rw [if_pos rfl]
    dsimp only [Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    have hscRead : sSup2.regs.get? Register.scause = some 0#64 := by
      simp [sSup2, Std.ExtDHashMap.get?_insert, hscauseSup]
    rw [hscRead]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    have hu3 : Sail.BitVec.updateSubrange 0#64 (64 -i 1) (64 -i 1)
        (bool_to_bit (trapCause_is_interrupt (.Exception (.E_Load_Page_Fault ())))) = 0#64 := by decide
    have hu4 : Sail.BitVec.updateSubrange 0#64 (64 -i 2) 0
        (zero_extend (m := 64 -i 1) (trapCause_bits_forwards (.Exception (.E_Load_Page_Fault ())))) = 13#64 := by decide
    have hu5 : Sail.BitVec.updateSubrange (1#64 <<< 23 ||| 1#64 <<< 1) 5 5
        (_get_Mstatus_SIE (1#64 <<< 23 ||| 1#64 <<< 1)) =
        ((1#64 <<< 23) ||| (1#64 <<< 5) ||| (1#64 <<< 1)) := by decide
    have hu6 : Sail.BitVec.updateSubrange ((1#64 <<< 23) ||| (1#64 <<< 5) ||| (1#64 <<< 1)) 1 1 0#1 =
        ((1#64 <<< 23) ||| (1#64 <<< 5)) := by decide
    have hu7 : Sail.BitVec.updateSubrange ((1#64 <<< 23) ||| (1#64 <<< 5)) 8 8 0#1 =
        ((1#64 <<< 23) ||| (1#64 <<< 5)) := by decide
    rw [hu3]
    have hscRead0S : ((sSup2.regs.insert Register.scause 0#64).get? Register.scause) = some 0#64 := by
      simp [Std.ExtDHashMap.get?_insert_self]
    rw [hscRead0S]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hu4]
    have hmsRead1 : (((sSup2.regs.insert Register.scause 0#64).insert Register.scause 13#64).get?
        Register.mstatus) = some (1#64 <<< 23 ||| 1#64 <<< 1) := by
      simp [sSup2, Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
    rw [hmsRead1]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hmsRead1]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hu5]
    have hmsRead2S : ((((sSup2.regs.insert Register.scause 0#64).insert Register.scause 13#64).insert
        Register.mstatus (1#64 <<< 23 ||| 1#64 <<< 5 ||| 1#64 <<< 1)).get? Register.mstatus) =
        some (1#64 <<< 23 ||| 1#64 <<< 5 ||| 1#64 <<< 1) := by
      simp [Std.ExtDHashMap.get?_insert_self]
    rw [hmsRead2S]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hu6]
    have hmsRead3S : (((((sSup2.regs.insert Register.scause 0#64).insert Register.scause 13#64).insert
        Register.mstatus (1#64 <<< 23 ||| 1#64 <<< 5 ||| 1#64 <<< 1)).insert
        Register.mstatus (1#64 <<< 23 ||| 1#64 <<< 5)).get? Register.mstatus) =
        some (1#64 <<< 23 ||| 1#64 <<< 5) := by
      simp [Std.ExtDHashMap.get?_insert_self]
    rw [hmsRead3S]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    have hprivRead : ((((((sSup2.regs.insert Register.scause 0#64).insert Register.scause 13#64).insert
        Register.mstatus ((1#64 <<< 23) ||| (1#64 <<< 5) ||| (1#64 <<< 1))).insert
        Register.mstatus ((1#64 <<< 23) ||| (1#64 <<< 5))).get? Register.cur_privilege)) =
        some .User := by
      simp [sSup2, Std.ExtDHashMap.get?_insert, hprivSup]
    rw [hprivRead]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hu7]
    let stS := { sSup2 with regs := ((((((sSup2.regs.insert .scause 0#64).insert .scause 13#64).insert
        .mstatus ((1#64 <<< 23) ||| (1#64 <<< 5) ||| (1#64 <<< 1))).insert
        .mstatus ((1#64 <<< 23) ||| (1#64 <<< 5))).insert .mstatus ((1#64 <<< 23) ||| (1#64 <<< 5))) |>.insert
        .stval 0x0000003ffffff008#64 |>.insert .sepc 0x0000000000010080#64 |>.insert .cur_privilege .Supervisor) }
    have htt := track_trap_Supervisor_noop (trapCause_is_interrupt (.Exception (.E_Load_Page_Fault ())))
      (trapCause_bits_forwards (.Exception (.E_Load_Page_Fault ()))) stS
      ((1#64 <<< 23) ||| (1#64 <<< 5)) 13#64 0x0000003ffffff008#64 0x0000000000010080#64
      (by simp [stS, sSup2, Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self])
      (by simp [stS, sSup2, Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self])
      (by simp [stS, sSup2, Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self])
      (by simp [stS, sSup2, Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self])
    dsimp only [EStateM.run] at htt
    rw [htt]
    dsimp only []
    have hscPostS : stS.regs.get? .scause = some 13#64 := by
      simp [stS, sSup2, Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
    have hstvPostS : stS.regs.get? .stvec = some 0x0000000080002000#64 := by
      simp [stS, sSup2, Std.ExtDHashMap.get?_insert, hstvecSup]
    rw [hscPostS]; dsimp only [EStateM.pure]
    rw [hstvPostS]; dsimp only [EStateM.pure]
    have hu9 : tvec_addr 0x0000000080002000#64 13#64 = some 0x0000000080002000#64 := by decide
    rw [hu9]; rfl
  · simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
  · simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
  · simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
  · simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
  · simp [Std.ExtDHashMap.get?_insert_self]
  · unfold trap_handler zicfilp_preserve_elp_on_trap reset_elp
      prepare_trap_vector get_config_print_exception get_config_print_interrupt
      tval handle_trap_extension
    rw [hartSupports_Ext_Zicfilp]
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet,
      EStateM.run, readReg, PreSail.readReg, writeReg, PreSail.writeReg,
      modify, modifyGet, MonadStateOf.modifyGet, get, getThe, MonadStateOf.get]
    have hf0 : (false || false) = false := rfl
    rw [hf0, if_neg Bool.false_ne_true]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [if_pos rfl]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hmstatusInt]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [helpInt]; dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    have hu1 : Sail.BitVec.updateSubrange (1#64 <<< 3) 41 41 0#1 = (1#64 <<< 3) := by decide
    have hu2 : landing_pad_bits_backwards .NO_LP_EXPECTED = 0#1 := rfl
    rw [hu1, hu2]
    have hmcRead : (((sInt.regs.insert Register.mstatus (1#64 <<< 3)).insert Register.elp 0#1).get?
        Register.mcause) = some 0#64 := by
      simp [Std.ExtDHashMap.get?_insert, hmcauseInt]
    rw [hmcRead]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    have hu3 : Sail.BitVec.updateSubrange 0#64 (64 -i 1) (64 -i 1)
        (bool_to_bit (trapCause_is_interrupt (.Interrupt .I_M_Timer))) = (1#64 <<< 63) := by decide
    have hu4 : Sail.BitVec.updateSubrange (1#64 <<< 63) (64 -i 2) 0
        (zero_extend (m := 64 -i 1) (trapCause_bits_forwards (.Interrupt .I_M_Timer))) =
        ((1#64 <<< 63) ||| 7#64) := by decide
    have hu5 : Sail.BitVec.updateSubrange (1#64 <<< 3) 7 7 (_get_Mstatus_MIE (1#64 <<< 3)) =
        ((1#64 <<< 7) ||| (1#64 <<< 3)) := by decide
    have hu6 : Sail.BitVec.updateSubrange ((1#64 <<< 7) ||| (1#64 <<< 3)) 3 3 0#1 =
        (1#64 <<< 7) := by decide
    have hu7 : Sail.BitVec.updateSubrange (1#64 <<< 7) 12 11 (privLevel_to_bits .Supervisor) =
        ((0b01#64 <<< 11) ||| (1#64 <<< 7)) := by decide
    have hu8 : zeros (n := 64) = 0#64 := rfl
    rw [hu3]
    have hmcRead0I : ((((sInt.regs.insert Register.mstatus (1#64 <<< 3)).insert Register.elp 0#1).insert
        Register.mcause (1#64 <<< 63)).get? Register.mcause) = some (1#64 <<< 63) := by
      simp [Std.ExtDHashMap.get?_insert_self]
    rw [hmcRead0I]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hu4]
    have hmsRead1 : (((((sInt.regs.insert Register.mstatus (1#64 <<< 3)).insert Register.elp 0#1).insert
        Register.mcause (1#64 <<< 63)).insert Register.mcause ((1#64 <<< 63) ||| 7#64)).get?
        Register.mstatus) = some (1#64 <<< 3) := by
      simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
    rw [hmsRead1]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hmsRead1]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hu5]
    have hmsRead2I : ((((((sInt.regs.insert Register.mstatus (1#64 <<< 3)).insert Register.elp 0#1).insert
        Register.mcause (1#64 <<< 63)).insert Register.mcause (1#64 <<< 63 ||| 7#64)).insert
        Register.mstatus (1#64 <<< 7 ||| 1#64 <<< 3)).get? Register.mstatus) =
        some (1#64 <<< 7 ||| 1#64 <<< 3) := by
      simp [Std.ExtDHashMap.get?_insert_self]
    rw [hmsRead2I]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hu6]
    have hmsRead3I : (((((((sInt.regs.insert Register.mstatus (1#64 <<< 3)).insert Register.elp 0#1).insert
        Register.mcause (1#64 <<< 63)).insert Register.mcause (1#64 <<< 63 ||| 7#64)).insert
        Register.mstatus (1#64 <<< 7 ||| 1#64 <<< 3)).insert
        Register.mstatus (1#64 <<< 7)).get? Register.mstatus) =
        some (1#64 <<< 7) := by
      simp [Std.ExtDHashMap.get?_insert_self]
    rw [hmsRead3I]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    have hprivRead : (((((((sInt.regs.insert Register.mstatus (1#64 <<< 3)).insert Register.elp 0#1).insert
        Register.mcause (1#64 <<< 63)).insert Register.mcause ((1#64 <<< 63) ||| 7#64)).insert
        Register.mstatus ((1#64 <<< 7) ||| (1#64 <<< 3))).insert
        Register.mstatus (1#64 <<< 7)).get? Register.cur_privilege) =
        some .Supervisor := by
      simp [Std.ExtDHashMap.get?_insert, hprivInt]
    rw [hprivRead]
    dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet]
    rw [hu7, hu8]
    let stI := { sInt with regs := (((((((sInt.regs.insert .mstatus (1#64 <<< 3)).insert .elp 0#1).insert
        .mcause (1#64 <<< 63)).insert .mcause ((1#64 <<< 63) ||| 7#64)).insert .mstatus ((1#64 <<< 7) ||| (1#64 <<< 3))).insert
        .mstatus (1#64 <<< 7)).insert .mstatus ((0b01#64 <<< 11) ||| (1#64 <<< 7)) |>.insert
        .mtval 0#64 |>.insert .mepc 0x0000000080200044#64 |>.insert .cur_privilege .Machine) }
    have htt := track_trap_Machine_noop (trapCause_is_interrupt (.Interrupt .I_M_Timer))
      (trapCause_bits_forwards (.Interrupt .I_M_Timer)) stI
      ((0b01#64 <<< 11) ||| (1#64 <<< 7)) ((1#64 <<< 63) ||| 7#64) 0#64 0x0000000080200044#64
      (by simp [stI, Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self])
      (by simp [stI, Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self])
      (by simp [stI, Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self])
      (by simp [stI, Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self])
    dsimp only [EStateM.run] at htt
    rw [htt]
    dsimp only []
    have hmcPostI : stI.regs.get? .mcause = some ((1#64 <<< 63) ||| 7#64) := by
      simp [stI, Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
    have hmtvPostI : stI.regs.get? .mtvec = some 0x0000000080001001#64 := by
      simp [stI, Std.ExtDHashMap.get?_insert, hmtvecInt]
    rw [hmcPostI]; dsimp only [EStateM.pure]
    rw [hmtvPostI]; dsimp only [EStateM.pure]
    have hu9 : tvec_addr 0x0000000080001001#64 ((1#64 <<< 63) ||| 7#64) =
        some 0x000000008000101c#64 := by decide
    rw [hu9]; rfl

private theorem regs_get?_insert_self
    (m : Std.ExtDHashMap Register RegisterType) (k : Register) (v : RegisterType k) :
    (m.insert k v).get? k = some v := by
  simp only [Std.ExtDHashMap.get?_insert_self]

private theorem regs_get?_insert_ne
    (m : Std.ExtDHashMap Register RegisterType) (k1 k2 : Register) (v : RegisterType k1)
    (hne : (k1 == k2) = false) :
    (m.insert k1 v).get? k2 = m.get? k2 := by
  rw [Std.ExtDHashMap.get?_insert]
  exact dif_neg (by rw [hne]; exact Bool.false_ne_true)

/-- Exact mirror of upstream `execute_MRET` (`LeanRV64D/InstsEnd.lean`, lines 68873–68910;
    SHA-256 snippet-pinned in `scripts/check_sail_riscv_bridge_sync.py`) over `SailM`. -/
noncomputable def sailExecuteMret (_ : Unit) : SailM ExecutionResult := do
  if ((bne (← readReg .cur_privilege) .Machine) : Bool)
  then pure (.Illegal_Instruction ())
  else
    if ((LeanRV64D.Functions.not (ext_check_xret_priv .Machine)) : Bool)
    then pure (.Ext_XRET_Priv_Failure ())
    else
      let prev_priv ← readReg .cur_privilege
      writeReg .mstatus (Sail.BitVec.updateSubrange (← readReg .mstatus) 3 3
        (_get_Mstatus_MPIE (← readReg .mstatus)))
      writeReg .mstatus (Sail.BitVec.updateSubrange (← readReg .mstatus) 7 7 1#1)
      writeReg .cur_privilege (← privLevel_bits_forwards
        (_get_Mstatus_MPP (← readReg .mstatus), 0#1))
      writeReg .mstatus (Sail.BitVec.updateSubrange (← readReg .mstatus) 12 11
        (privLevel_to_bits (← do
          if ((← currentlyEnabled .Ext_U) : Bool)
          then pure .User
          else pure .Machine)))
      if ((bne (← readReg .cur_privilege) .Machine) : Bool)
      then writeReg .mstatus (Sail.BitVec.updateSubrange (← readReg .mstatus) 17 17 0#1)
      else pure ()
      if ((hartSupports .Ext_Zicfilp) : Bool)
      then zicfilp_restore_elp_on_xret .mRET (← readReg .cur_privilege)
      else pure ()
      long_csr_write_callback "mstatus" "mstatush" (← readReg .mstatus)
      if ((get_config_print_exception ()) : Bool)
      then
        pure (print_endline
          (HAppend.hAppend "ret-ing from "
            (HAppend.hAppend (← privLevel_to_str prev_priv)
              (HAppend.hAppend " to " (← privLevel_to_str (← readReg .cur_privilege))))))
      else pure ()
      set_next_pc (← prepare_xret_target .Machine)
      let _ : Unit := xret_callback true
      pure (.Retire_Success ())


/-- Exact mirror of upstream `execute_SRET` (`LeanRV64D/InstsEnd.lean`, lines 67504–67549;
    SHA-256 snippet-pinned in `scripts/check_sail_riscv_bridge_sync.py`) over `SailM`. -/
noncomputable def sailExecuteSret (_ : Unit) : SailM ExecutionResult := do
  let sret_illegal ← (( do
    match (← readReg .cur_privilege) with
    | .User => pure true
    | .Supervisor =>
      pure ((LeanRV64D.Functions.not (← currentlyEnabled .Ext_S)) ||
        ((_get_Mstatus_TSR (← readReg .mstatus)) == 1#1))
    | .Machine => pure (LeanRV64D.Functions.not (← currentlyEnabled .Ext_S))
    | .VirtualUser =>
      internal_error "extensions/I/base_insts.sail" 607 "Hypervisor extension not supported"
    | .VirtualSupervisor =>
      internal_error "extensions/I/base_insts.sail" 608 "Hypervisor extension not supported" ) :
    SailM Bool )
  if (sret_illegal : Bool)
  then pure (.Illegal_Instruction ())
  else
    if ((LeanRV64D.Functions.not (ext_check_xret_priv .Supervisor)) : Bool)
    then pure (.Ext_XRET_Priv_Failure ())
    else
      let prev_priv ← readReg .cur_privilege
      writeReg .mstatus (Sail.BitVec.updateSubrange (← readReg .mstatus) 1 1
        (_get_Mstatus_SPIE (← readReg .mstatus)))
      writeReg .mstatus (Sail.BitVec.updateSubrange (← readReg .mstatus) 5 5 1#1)
      writeReg .cur_privilege (← do
        if (((_get_Mstatus_SPP (← readReg .mstatus)) == 1#1) : Bool)
        then pure .Supervisor
        else pure .User)
      writeReg .mstatus (Sail.BitVec.updateSubrange (← readReg .mstatus) 8 8 0#1)
      if ((bne (← readReg .cur_privilege) .Machine) : Bool)
      then writeReg .mstatus (Sail.BitVec.updateSubrange (← readReg .mstatus) 17 17 0#1)
      else pure ()
      if ((hartSupports .Ext_Zicfilp) : Bool)
      then zicfilp_restore_elp_on_xret .sRET (← readReg .cur_privilege)
      else pure ()
      long_csr_write_callback "mstatus" "mstatush" (← readReg .mstatus)
      if ((get_config_print_exception ()) : Bool)
      then
        pure (print_endline
          (HAppend.hAppend "ret-ing from "
            (HAppend.hAppend (← privLevel_to_str prev_priv)
              (HAppend.hAppend " to " (← privLevel_to_str (← readReg .cur_privilege))))))
      else pure ()
      set_next_pc (← prepare_xret_target .Supervisor)
      let _ : Unit := xret_callback false
      pure (.Retire_Success ())


private theorem run_bind_ok {α β : Type} (m : SailM α) (f : α → SailM β)
    (s s' : SequentialState RegisterType trivialChoiceSource) (a : α)
    (hm : m.run s = .ok a s') :
    (m >>= f).run s = (f a).run s' := by
  dsimp only [Bind.bind, EStateM.bind, EStateM.run] at hm ⊢
  rw [hm]

private theorem readReg_run_ok (r : Register) (v : RegisterType r)
    (s : SequentialState RegisterType trivialChoiceSource)
    (h : s.regs.get? r = some v) :
    (readReg r).run s = .ok v s := by
  dsimp only [readReg, PreSail.readReg, EStateM.run, get, getThe, MonadStateOf.get,
    EStateM.get, EStateM.bind, Bind.bind, Pure.pure, EStateM.pure]
  rw [h]; rfl

private theorem writeReg_run_ok (r : Register) (v : RegisterType r)
    (s : SequentialState RegisterType trivialChoiceSource) :
    (writeReg r v).run s = .ok () { s with regs := s.regs.insert r v } := rfl

private theorem zicfilp_restore_mRET_run
    (p : Privilege) (s : SequentialState RegisterType trivialChoiceSource)
    (ms : BitVec 64) (lpe : Bool)
    (hms : s.regs.get? .mstatus = some ms)
    (hlpe : (get_xLPE p).run { s with regs := s.regs.insert .mstatus (Sail.BitVec.updateSubrange ms 41 41 0#1) } =
      .ok lpe { s with regs := s.regs.insert .mstatus (Sail.BitVec.updateSubrange ms 41 41 0#1) }) :
    (zicfilp_restore_elp_on_xret .mRET p).run s =
      .ok () { s with regs := ((s.regs.insert .mstatus (Sail.BitVec.updateSubrange ms 41 41 0#1)).insert
        .elp (if lpe then _get_Mstatus_MPELP ms else 0#1)) } := by
  unfold zicfilp_restore_elp_on_xret landing_pad_bits_backwards
  dsimp only []
  rw [run_bind_ok _ _ _ _ _ (by
    rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hms)]
    rw [run_bind_ok _ _ _ _ _ (by rfl : (pure (_get_Mstatus_MPELP ms) : SailM _).run s = .ok _ s)]
    rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hms)]
    rw [run_bind_ok _ _ _ _ _ (writeReg_run_ok _ _ _)]
    rfl)]
  rw [run_bind_ok _ _ _ _ (if lpe then _get_Mstatus_MPELP ms else 0#1) (by
    rw [run_bind_ok _ _ _ _ _ hlpe]
    cases lpe <;> rfl)]
  rw [writeReg_run_ok]

private theorem zicfilp_restore_sRET_run
    (p : Privilege) (s : SequentialState RegisterType trivialChoiceSource)
    (ms : BitVec 64) (lpe : Bool)
    (hms : s.regs.get? .mstatus = some ms)
    (hlpe : (get_xLPE p).run { s with regs := s.regs.insert .mstatus (Sail.BitVec.updateSubrange ms 23 23 0#1) } =
      .ok lpe { s with regs := s.regs.insert .mstatus (Sail.BitVec.updateSubrange ms 23 23 0#1) }) :
    (zicfilp_restore_elp_on_xret .sRET p).run s =
      .ok () { s with regs := ((s.regs.insert .mstatus (Sail.BitVec.updateSubrange ms 23 23 0#1)).insert
        .elp (if lpe then _get_Mstatus_SPELP ms else 0#1)) } := by
  unfold zicfilp_restore_elp_on_xret landing_pad_bits_backwards
  dsimp only []
  rw [run_bind_ok _ _ _ _ _ (by
    rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hms)]
    rw [run_bind_ok _ _ _ _ _ (by rfl : (pure (_get_Mstatus_SPELP ms) : SailM _).run s = .ok _ s)]
    rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hms)]
    rw [run_bind_ok _ _ _ _ _ (writeReg_run_ok _ _ _)]
    rfl)]
  rw [run_bind_ok _ _ _ _ (if lpe then _get_Mstatus_SPELP ms else 0#1) (by
    rw [run_bind_ok _ _ _ _ _ hlpe]
    cases lpe <;> rfl)]
  rw [writeReg_run_ok]

private theorem prepare_xret_target_Machine_run
    (s : SequentialState RegisterType trivialChoiceSource) (mepcVal : BitVec 64) (zca : Bool)
    (hmepc : s.regs.get? .mepc = some mepcVal)
    (hzca : (currentlyEnabled .Ext_Zca).run s = .ok zca s) :
    (prepare_xret_target .Machine).run s =
      .ok (if zca then BitVec.update mepcVal 0 0#1
           else Sail.BitVec.updateSubrange mepcVal 1 0 (zeros (n := 1 -i (0 -i 1)))) s := by
  unfold prepare_xret_target get_xepc align_pc
  dsimp only []
  rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hmepc)]
  rw [run_bind_ok _ _ _ _ _ hzca]
  cases zca <;> rfl

private theorem prepare_xret_target_Supervisor_run
    (s : SequentialState RegisterType trivialChoiceSource) (sepcVal : BitVec 64) (zca : Bool)
    (hsepc : s.regs.get? .sepc = some sepcVal)
    (hzca : (currentlyEnabled .Ext_Zca).run s = .ok zca s) :
    (prepare_xret_target .Supervisor).run s =
      .ok (if zca then BitVec.update sepcVal 0 0#1
           else Sail.BitVec.updateSubrange sepcVal 1 0 (zeros (n := 1 -i (0 -i 1)))) s := by
  unfold prepare_xret_target get_xepc align_pc
  dsimp only []
  rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hsepc)]
  rw [run_bind_ok _ _ _ _ _ hzca]
  cases zca <;> rfl

/-- Pure state-map update helpers for `execute_MRET` and `execute_SRET` symbolic `SailM` transitions. -/
abbrev mretRegsPreElp (regs : Std.ExtDHashMap Register RegisterType)
    (ms0 : BitVec 64) (nextPriv : Privilege) (extU : Bool) :
    Std.ExtDHashMap Register RegisterType × BitVec 64 :=
  let ms1 := Sail.BitVec.updateSubrange ms0 3 3 (_get_Mstatus_MPIE ms0)
  let ms2 := Sail.BitVec.updateSubrange ms1 7 7 1#1
  let ms3 := Sail.BitVec.updateSubrange ms2 12 11 (privLevel_to_bits (if extU then Privilege.User else Privilege.Machine))
  let regs3 := (((regs.insert .mstatus ms1).insert .mstatus ms2).insert .cur_privilege nextPriv).insert .mstatus ms3
  let ms4 := if bne nextPriv .Machine then Sail.BitVec.updateSubrange ms3 17 17 0#1 else ms3
  let regs4 := if bne nextPriv .Machine then regs3.insert .mstatus ms4 else regs3
  (regs4.insert .mstatus (Sail.BitVec.updateSubrange ms4 41 41 0#1), ms4)

abbrev sretRegsPreElp (regs : Std.ExtDHashMap Register RegisterType) (ms0 : BitVec 64) :
    Std.ExtDHashMap Register RegisterType × BitVec 64 × Privilege :=
  let ms1 := Sail.BitVec.updateSubrange ms0 1 1 (_get_Mstatus_SPIE ms0)
  let ms2 := Sail.BitVec.updateSubrange ms1 5 5 1#1
  let nextPriv := if _get_Mstatus_SPP ms2 == 1#1 then Privilege.Supervisor else Privilege.User
  let ms3 := Sail.BitVec.updateSubrange ms2 8 8 0#1
  let ms4 := Sail.BitVec.updateSubrange ms3 17 17 0#1
  let regs4 := ((((regs.insert .mstatus ms1).insert .mstatus ms2).insert .cur_privilege nextPriv).insert .mstatus ms3).insert .mstatus ms4
  (regs4.insert .mstatus (Sail.BitVec.updateSubrange ms4 23 23 0#1), ms4, nextPriv)

theorem sailExecuteMret_Machine_run
    (s : SequentialState RegisterType trivialChoiceSource)
    (ms0 : BitVec 64) (nextPriv : Privilege) (extU lpe zca : Bool) (mepcVal : BitVec 64)
    (hpriv : s.regs.get? .cur_privilege = some .Machine)
    (hms : s.regs.get? .mstatus = some ms0)
    (hpbf : privLevel_bits_forwards (_get_Mstatus_MPP
      (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange ms0 3 3 (_get_Mstatus_MPIE ms0)) 7 7 1#1), 0#1) =
      EStateM.pure nextPriv)
    (hceU : (currentlyEnabled .Ext_U).run
      { s with regs := (((s.regs.insert .mstatus (Sail.BitVec.updateSubrange ms0 3 3 (_get_Mstatus_MPIE ms0))).insert .mstatus
          (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange ms0 3 3 (_get_Mstatus_MPIE ms0)) 7 7 1#1)).insert .cur_privilege nextPriv) } =
      .ok extU
      { s with regs := (((s.regs.insert .mstatus (Sail.BitVec.updateSubrange ms0 3 3 (_get_Mstatus_MPIE ms0))).insert .mstatus
          (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange ms0 3 3 (_get_Mstatus_MPIE ms0)) 7 7 1#1)).insert .cur_privilege nextPriv) })
    (hlpe : (get_xLPE nextPriv).run { s with regs := (mretRegsPreElp s.regs ms0 nextPriv extU).1 } =
      .ok lpe { s with regs := (mretRegsPreElp s.regs ms0 nextPriv extU).1 })
    (hmepc : s.regs.get? .mepc = some mepcVal)
    (hzca : (let p := mretRegsPreElp s.regs ms0 nextPriv extU
      (currentlyEnabled .Ext_Zca).run { s with regs := p.1.insert .elp (if lpe then _get_Mstatus_MPELP p.2 else 0#1) } =
      .ok zca { s with regs := p.1.insert .elp (if lpe then _get_Mstatus_MPELP p.2 else 0#1) })) :
    (sailExecuteMret ()).run s =
      .ok (.Retire_Success ())
      (let p := mretRegsPreElp s.regs ms0 nextPriv extU
       let target := if zca then BitVec.update mepcVal 0 0#1 else Sail.BitVec.updateSubrange mepcVal 1 0 (zeros (n := 1 -i (0 -i 1)))
       { s with regs := (p.1.insert .elp (if lpe then _get_Mstatus_MPELP p.2 else 0#1)).insert .nextPC target }) := by
  unfold sailExecuteMret
  have hbneM : bne Privilege.Machine .Machine = false := rfl
  have hchkM : LeanRV64D.Functions.not (ext_check_xret_priv .Machine) = false := rfl
  rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hpriv), hbneM, if_neg Bool.false_ne_true, hchkM, if_neg Bool.false_ne_true,
      run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hpriv), run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hms),
      run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hms), run_bind_ok _ _ _ _ _ (writeReg_run_ok _ _ _)]
  let ms1 := Sail.BitVec.updateSubrange ms0 3 3 (_get_Mstatus_MPIE ms0)
  have hms1 : (s.regs.insert .mstatus ms1).get? .mstatus = some ms1 := regs_get?_insert_self _ _ _
  rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hms1), run_bind_ok _ _ _ _ _ (writeReg_run_ok _ _ _)]
  let ms2 := Sail.BitVec.updateSubrange ms1 7 7 1#1
  have hms2 : ((s.regs.insert .mstatus ms1).insert .mstatus ms2).get? .mstatus = some ms2 := regs_get?_insert_self _ _ _
  rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hms2), run_bind_ok _ _ _ _ nextPriv (by rw [hpbf]; rfl),
      run_bind_ok _ _ _ _ _ (writeReg_run_ok _ _ _)]
  have hms2_priv : (((s.regs.insert .mstatus ms1).insert .mstatus ms2).insert .cur_privilege nextPriv).get? .mstatus = some ms2 := by
    rw [regs_get?_insert_ne _ _ _ _ rfl, regs_get?_insert_self]
  rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hms2_priv),
      run_bind_ok _ _ _ _ (if extU then Privilege.User else Privilege.Machine) (by rw [run_bind_ok _ _ _ _ _ hceU]; cases extU <;> rfl),
      run_bind_ok _ _ _ _ _ (writeReg_run_ok _ _ _)]
  let ms3 := Sail.BitVec.updateSubrange ms2 12 11 (privLevel_to_bits (if extU then Privilege.User else Privilege.Machine))
  let regs3 := (((s.regs.insert .mstatus ms1).insert .mstatus ms2).insert .cur_privilege nextPriv).insert .mstatus ms3
  have hcp3 : regs3.get? .cur_privilege = some nextPriv := by dsimp only [regs3]; rw [regs_get?_insert_ne _ _ _ _ rfl, regs_get?_insert_self]
  have hms3 : regs3.get? .mstatus = some ms3 := regs_get?_insert_self _ _ _
  rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hcp3)]
  let ms4 := if bne nextPriv .Machine then Sail.BitVec.updateSubrange ms3 17 17 0#1 else ms3
  let regs4 := if bne nextPriv .Machine then regs3.insert .mstatus ms4 else regs3
  have hstepMprv : ∀ (jp : PUnit → SailM ExecutionResult),
      (if (bne nextPriv .Machine) = true then do
          let v ← readReg .mstatus; let y ← writeReg .mstatus (Sail.BitVec.updateSubrange v 17 17 0#1); jp y
        else do let y ← pure (); jp y).run { s with regs := regs3 } = (jp ()).run { s with regs := regs4 } := by
    intro jp; dsimp only [regs4, ms4]
    cases bne nextPriv .Machine
    · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]; rfl
    · rw [if_pos rfl, if_pos rfl, if_pos rfl, run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hms3), run_bind_ok _ _ _ _ _ (writeReg_run_ok _ _ _)]
  rw [hstepMprv]; dsimp only []
  have hcp4 : regs4.get? .cur_privilege = some nextPriv := by
    dsimp only [regs4]; cases bne nextPriv .Machine
    · exact hcp3
    · rw [if_pos rfl, regs_get?_insert_ne _ _ _ _ rfl]; exact hcp3
  have hms4 : regs4.get? .mstatus = some ms4 := by
    dsimp only [regs4, ms4]; cases bne nextPriv .Machine
    · exact hms3
    · rw [if_pos rfl, if_pos rfl]; exact regs_get?_insert_self _ _ _
  rw [hartSupports_Ext_Zicfilp, if_pos rfl, run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hcp4),
      run_bind_ok _ _ _ _ _ (zicfilp_restore_mRET_run nextPriv { s with regs := regs4 } ms4 lpe hms4 hlpe)]; dsimp only []
  let regs5 := (regs4.insert .mstatus (Sail.BitVec.updateSubrange ms4 41 41 0#1)).insert .elp (if lpe then _get_Mstatus_MPELP ms4 else 0#1)
  have hms5 : regs5.get? .mstatus = some (Sail.BitVec.updateSubrange ms4 41 41 0#1) := by
    dsimp only [regs5]; rw [regs_get?_insert_ne _ _ _ _ rfl, regs_get?_insert_self]
  have hprt : get_config_print_exception () = false := rfl
  rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hms5), run_bind_ok _ _ _ _ () (by rfl),
      hprt, if_neg Bool.false_ne_true, run_bind_ok _ _ _ _ () (by rfl)]; dsimp only []
  have hmepc5 : regs5.get? .mepc = some mepcVal := by
    dsimp only [regs5, regs4, regs3]; cases bne nextPriv .Machine <;> simp [Std.ExtDHashMap.get?_insert, hmepc]
  rw [run_bind_ok _ _ _ _ _ (prepare_xret_target_Machine_run { s with regs := regs5 } mepcVal zca hmepc5 hzca)]; rfl

theorem sailExecuteSret_legal_run
    (s : SequentialState RegisterType trivialChoiceSource)
    (prevPriv : Privilege) (ms0 : BitVec 64) (lpe zca : Bool) (sepcVal : BitVec 64)
    (hillegal : (do
      match (← readReg .cur_privilege) with
      | .User => pure true
      | .Supervisor => pure ((LeanRV64D.Functions.not (← currentlyEnabled .Ext_S)) || ((_get_Mstatus_TSR (← readReg .mstatus)) == 1#1))
      | .Machine => pure (LeanRV64D.Functions.not (← currentlyEnabled .Ext_S))
      | .VirtualUser => internal_error "extensions/I/base_insts.sail" 607 "Hypervisor extension not supported"
      | .VirtualSupervisor => internal_error "extensions/I/base_insts.sail" 608 "Hypervisor extension not supported").run s = .ok false s)
    (hpriv : s.regs.get? .cur_privilege = some prevPriv)
    (hms : s.regs.get? .mstatus = some ms0)
    (hlpe : (let p := sretRegsPreElp s.regs ms0
       (get_xLPE p.2.2).run { s with regs := p.1 } = .ok lpe { s with regs := p.1 }))
    (hsepc : s.regs.get? .sepc = some sepcVal)
    (hzca : (let p := sretRegsPreElp s.regs ms0
       (currentlyEnabled .Ext_Zca).run { s with regs := p.1.insert .elp (if lpe then _get_Mstatus_SPELP p.2.1 else 0#1) } =
       .ok zca { s with regs := p.1.insert .elp (if lpe then _get_Mstatus_SPELP p.2.1 else 0#1) })) :
    (sailExecuteSret ()).run s =
      .ok (.Retire_Success ())
      (let p := sretRegsPreElp s.regs ms0
       let target := if zca then BitVec.update sepcVal 0 0#1 else Sail.BitVec.updateSubrange sepcVal 1 0 (zeros (n := 1 -i (0 -i 1)))
       { s with regs := (p.1.insert .elp (if lpe then _get_Mstatus_SPELP p.2.1 else 0#1)).insert .nextPC target }) := by
  unfold sailExecuteSret
  have hchkS : LeanRV64D.Functions.not (ext_check_xret_priv .Supervisor) = false := rfl
  rw [run_bind_ok _ _ _ _ _ hillegal, if_neg Bool.false_ne_true, hchkS, if_neg Bool.false_ne_true,
      run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hpriv), run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hms),
      run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hms), run_bind_ok _ _ _ _ _ (writeReg_run_ok _ _ _)]
  let ms1 := Sail.BitVec.updateSubrange ms0 1 1 (_get_Mstatus_SPIE ms0)
  have hms1 : (s.regs.insert .mstatus ms1).get? .mstatus = some ms1 := regs_get?_insert_self _ _ _
  rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hms1), run_bind_ok _ _ _ _ _ (writeReg_run_ok _ _ _)]
  let ms2 := Sail.BitVec.updateSubrange ms1 5 5 1#1
  have hms2 : ((s.regs.insert .mstatus ms1).insert .mstatus ms2).get? .mstatus = some ms2 := regs_get?_insert_self _ _ _
  let nextPriv := if _get_Mstatus_SPP ms2 == 1#1 then Privilege.Supervisor else Privilege.User
  rw [run_bind_ok _ _ _ _ nextPriv (by rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hms2)]; dsimp only [nextPriv]; cases (_get_Mstatus_SPP ms2 == 1#1) <;> rfl),
      run_bind_ok _ _ _ _ _ (writeReg_run_ok _ _ _)]
  have hms2_priv : (((s.regs.insert .mstatus ms1).insert .mstatus ms2).insert .cur_privilege nextPriv).get? .mstatus = some ms2 := by
    rw [regs_get?_insert_ne _ _ _ _ rfl, regs_get?_insert_self]
  rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hms2_priv), run_bind_ok _ _ _ _ _ (writeReg_run_ok _ _ _)]
  let ms3 := Sail.BitVec.updateSubrange ms2 8 8 0#1
  let regs3 := (((s.regs.insert .mstatus ms1).insert .mstatus ms2).insert .cur_privilege nextPriv).insert .mstatus ms3
  have hcp3 : regs3.get? .cur_privilege = some nextPriv := by dsimp only [regs3]; rw [regs_get?_insert_ne _ _ _ _ rfl, regs_get?_insert_self]
  have hms3 : regs3.get? .mstatus = some ms3 := regs_get?_insert_self _ _ _
  have hbneNext : bne nextPriv .Machine = true := by dsimp only [nextPriv]; cases (_get_Mstatus_SPP ms2 == 1#1) <;> rfl
  rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hcp3), hbneNext, if_pos rfl,
      run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hms3), run_bind_ok _ _ _ _ _ (writeReg_run_ok _ _ _)]; dsimp only []
  let ms4 := Sail.BitVec.updateSubrange ms3 17 17 0#1
  let regs4 := regs3.insert .mstatus ms4
  have hcp4 : regs4.get? .cur_privilege = some nextPriv := by dsimp only [regs4]; rw [regs_get?_insert_ne _ _ _ _ rfl]; exact hcp3
  have hms4 : regs4.get? .mstatus = some ms4 := regs_get?_insert_self _ _ _
  rw [hartSupports_Ext_Zicfilp, if_pos rfl, run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hcp4),
      run_bind_ok _ _ _ _ _ (zicfilp_restore_sRET_run nextPriv { s with regs := regs4 } ms4 lpe hms4 hlpe)]; dsimp only []
  let regs5 := (regs4.insert .mstatus (Sail.BitVec.updateSubrange ms4 23 23 0#1)).insert .elp (if lpe then _get_Mstatus_SPELP ms4 else 0#1)
  have hms5 : regs5.get? .mstatus = some (Sail.BitVec.updateSubrange ms4 23 23 0#1) := by
    dsimp only [regs5]; rw [regs_get?_insert_ne _ _ _ _ rfl, regs_get?_insert_self]
  have hprt : get_config_print_exception () = false := rfl
  rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hms5), run_bind_ok _ _ _ _ () (by rfl),
      hprt, if_neg Bool.false_ne_true, run_bind_ok _ _ _ _ () (by rfl)]; dsimp only []
  have hsepc5 : regs5.get? .sepc = some sepcVal := by
    simp [regs5, regs4, regs3, Std.ExtDHashMap.get?_insert, hsepc]
  rw [run_bind_ok _ _ _ _ _ (prepare_xret_target_Supervisor_run { s with regs := regs5 } sepcVal zca hsepc5 hzca)]; rfl

/-- End-to-end `SailM` bisimulation for `execute_MRET` (`InstsEnd.lean` lines 68873–68910,
    mirrored as `sailExecuteMret` and SHA-256 snippet-pinned):
    1. Proves `MRET` traps with `Illegal_Instruction ()` in `User` and `Supervisor` modes;
    2. Proves `MRET` from `Machine` mode with `mstatus.MPP = 0b01` (`Supervisor`), `MPIE = 1`,
       `MPRV = 1`, and `MPELP = 1` (`menvcfg.LPE = 1`) restores `MIE := 1`, sets `MPIE := 1`,
       lowers `cur_privilege := .Supervisor`, resets `MPP := 0b00` (`User`, since `Ext_U` is
       enabled), clears `MPRV := 0` (`cur_privilege ≠ .Machine`), restores `elp := 1` while
       clearing `MPELP := 0`, and sets `nextPC` to `prepare_xret_target .Machine` (`mepc` aligned);
    3. Proves `MRET` from `Machine` mode with `mstatus.MPP = 0b11` (`Machine`) and `MPRV = 1`
       retains `MPRV = 1` (`cur_privilege == .Machine`) while resetting `MPP := 0b00` (`User`). -/
theorem rv64Mret_bisim_sail
    (sU sS sMtoS sMtoM : SequentialState RegisterType trivialChoiceSource)
    (hprivU : sU.regs.get? .cur_privilege = some .User)
    (hprivS : sS.regs.get? .cur_privilege = some .Supervisor)
    (hprivMS : sMtoS.regs.get? .cur_privilege = some .Machine)
    (hmisaMS : sMtoS.regs.get? .misa = some rv64StandardMisaSUC)
    (hmstatusMS : sMtoS.regs.get? .mstatus =
      some ((1#64 <<< 41) ||| (1#64 <<< 17) ||| (0b01#64 <<< 11) ||| (1#64 <<< 7)))
    (hmenvMS : sMtoS.regs.get? .menvcfg = some (1#64 <<< 2))
    (hmepcMS : sMtoS.regs.get? .mepc = some 0x0000000080200042#64)
    (hprivMM : sMtoM.regs.get? .cur_privilege = some .Machine)
    (hmisaMM : sMtoM.regs.get? .misa = some rv64StandardMisaSU)
    (hmstatusMM : sMtoM.regs.get? .mstatus =
      some ((1#64 <<< 17) ||| (0b11#64 <<< 11) ||| (1#64 <<< 7)))
    (hmsecMM : sMtoM.regs.get? .mseccfg = some 0#64)
    (hmepcMM : sMtoM.regs.get? .mepc = some 0x0000000080200082#64) :
    let mstatusMSInit : BitVec 64 :=
      (1#64 <<< 41) ||| (1#64 <<< 17) ||| (0b01#64 <<< 11) ||| (1#64 <<< 7)
    let mstatusMSFinal : BitVec 64 := (1#64 <<< 7) ||| (1#64 <<< 3)
    let regsMSAfter := ((((((((sMtoS.regs.insert .mstatus (mstatusMSInit ||| (1#64 <<< 3))).insert
        .mstatus (mstatusMSInit ||| (1#64 <<< 3))).insert .cur_privilege .Supervisor).insert
        .mstatus ((1#64 <<< 41) ||| (1#64 <<< 17) ||| (1#64 <<< 7) ||| (1#64 <<< 3))).insert
        .mstatus ((1#64 <<< 41) ||| (1#64 <<< 7) ||| (1#64 <<< 3))).insert
        .mstatus mstatusMSFinal).insert .elp 1#1).insert .nextPC 0x0000000080200042#64)
    let mstatusMMInit : BitVec 64 := (1#64 <<< 17) ||| (0b11#64 <<< 11) ||| (1#64 <<< 7)
    let mstatusMMFinal : BitVec 64 := (1#64 <<< 17) ||| (1#64 <<< 7) ||| (1#64 <<< 3)
    let regsMMAfter := (((((((sMtoM.regs.insert .mstatus (mstatusMMInit ||| (1#64 <<< 3))).insert
        .mstatus (mstatusMMInit ||| (1#64 <<< 3))).insert .cur_privilege .Machine).insert
        .mstatus mstatusMMFinal).insert .mstatus mstatusMMFinal).insert
        .elp 0#1).insert .nextPC 0x0000000080200080#64)
    (sailExecuteMret ()).run sU = .ok (.Illegal_Instruction ()) sU ∧
    (sailExecuteMret ()).run sS = .ok (.Illegal_Instruction ()) sS ∧
    (sailExecuteMret ()).run sMtoS = .ok (.Retire_Success ()) { sMtoS with regs := regsMSAfter } ∧
    regsMSAfter.get? .mstatus = some mstatusMSFinal ∧
    regsMSAfter.get? .cur_privilege = some .Supervisor ∧
    regsMSAfter.get? .elp = some 1#1 ∧
    regsMSAfter.get? .nextPC = some 0x0000000080200042#64 ∧
    (sailExecuteMret ()).run sMtoM = .ok (.Retire_Success ()) { sMtoM with regs := regsMMAfter } ∧
    regsMMAfter.get? .mstatus = some mstatusMMFinal ∧
    regsMMAfter.get? .cur_privilege = some .Machine ∧
    regsMMAfter.get? .nextPC = some 0x0000000080200080#64 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold sailExecuteMret; rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hprivU)]; rfl
  · unfold sailExecuteMret; rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hprivS)]; rfl
  · let ms0 : BitVec 64 := (1#64 <<< 41) ||| (1#64 <<< 17) ||| (0b01#64 <<< 11) ||| (1#64 <<< 7)
    have hpbf : privLevel_bits_forwards (_get_Mstatus_MPP
        (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange ms0 3 3 (_get_Mstatus_MPIE ms0)) 7 7 1#1), 0#1) =
        EStateM.pure .Supervisor := by
      have h : _get_Mstatus_MPP (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange ms0 3 3 (_get_Mstatus_MPIE ms0)) 7 7 1#1) = 0b01#2 := by decide
      rw [h]; rfl
    have hceU := currentlyEnabled_Ext_U_standard
      { sMtoS with regs := (((sMtoS.regs.insert .mstatus (Sail.BitVec.updateSubrange ms0 3 3 (_get_Mstatus_MPIE ms0))).insert .mstatus
          (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange ms0 3 3 (_get_Mstatus_MPIE ms0)) 7 7 1#1)).insert .cur_privilege .Supervisor) }
      rv64StandardMisaSUC (by simp [Std.ExtDHashMap.get?_insert, hmisaMS]) (by decide)
    have hlpe := by
      have hbneS : bne Privilege.Supervisor .Machine = true := rfl
      have h := get_xLPE_Supervisor { sMtoS with regs := (mretRegsPreElp sMtoS.regs ms0 .Supervisor true).1 } (1#64 <<< 2)
        (by dsimp only [mretRegsPreElp]; rw [hbneS, if_pos rfl]; simp [Std.ExtDHashMap.get?_insert, hmenvMS])
      have hb : bool_bit_backwards (_get_MEnvcfg_LPE (1#64 <<< 2)) = true := by decide
      rw [hb] at h; exact h
    have hzca := by
      have hbneS : bne Privilege.Supervisor .Machine = true := rfl
      let p := mretRegsPreElp sMtoS.regs ms0 .Supervisor true
      have h := currentlyEnabled_Ext_Zca_of_misa_C
        { sMtoS with regs := p.1.insert .elp (if true then _get_Mstatus_MPELP p.2 else 0#1) } rv64StandardMisaSUC
        (by dsimp only [p, mretRegsPreElp]; rw [hbneS, if_pos rfl]; simp [Std.ExtDHashMap.get?_insert, hmisaMS])
      have hc : (_get_Misa_C rv64StandardMisaSUC == 1#1) = true := by decide
      rw [hc] at h; exact h
    rw [sailExecuteMret_Machine_run sMtoS ms0 .Supervisor true true true 0x0000000080200042#64 hprivMS hmstatusMS hpbf hceU hlpe hmepcMS hzca]
    have hb1 : Sail.BitVec.updateSubrange ms0 3 3 (_get_Mstatus_MPIE ms0) = (ms0 ||| (1#64 <<< 3)) := by decide
    have hb2 : Sail.BitVec.updateSubrange (ms0 ||| (1#64 <<< 3)) 7 7 1#1 = (ms0 ||| (1#64 <<< 3)) := by decide
    have hb3 : Sail.BitVec.updateSubrange (ms0 ||| (1#64 <<< 3)) 12 11 (privLevel_to_bits .User) =
      ((1#64 <<< 41) ||| (1#64 <<< 17) ||| (1#64 <<< 7) ||| (1#64 <<< 3)) := by decide
    have hb4 : Sail.BitVec.updateSubrange ((1#64 <<< 41) ||| (1#64 <<< 17) ||| (1#64 <<< 7) ||| (1#64 <<< 3)) 17 17 0#1 =
      ((1#64 <<< 41) ||| (1#64 <<< 7) ||| (1#64 <<< 3)) := by decide
    have hb5 : Sail.BitVec.updateSubrange ((1#64 <<< 41) ||| (1#64 <<< 7) ||| (1#64 <<< 3)) 41 41 0#1 = ((1#64 <<< 7) ||| (1#64 <<< 3)) := by decide
    have hb6 : _get_Mstatus_MPELP ((1#64 <<< 41) ||| (1#64 <<< 7) ||| (1#64 <<< 3)) = 1#1 := by decide
    have hb7 : BitVec.update 0x0000000080200042#64 0 0#1 = 0x0000000080200042#64 := by decide
    have hbneS : bne Privilege.Supervisor .Machine = true := rfl
    dsimp only [mretRegsPreElp]
    rw [hbneS, if_pos rfl, if_pos rfl, if_pos rfl, if_pos rfl, if_pos rfl, hb1, hb2, hb3, hb4, hb5, hb6, hb7]
  · simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
  · simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
  · simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
  · exact regs_get?_insert_self _ _ _
  · let ms0 : BitVec 64 := (1#64 <<< 17) ||| (0b11#64 <<< 11) ||| (1#64 <<< 7)
    have hpbf : privLevel_bits_forwards (_get_Mstatus_MPP
        (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange ms0 3 3 (_get_Mstatus_MPIE ms0)) 7 7 1#1), 0#1) =
        EStateM.pure .Machine := by
      have h : _get_Mstatus_MPP (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange ms0 3 3 (_get_Mstatus_MPIE ms0)) 7 7 1#1) = 0b11#2 := by decide
      rw [h]; rfl
    have hceU := currentlyEnabled_Ext_U_standard
      { sMtoM with regs := (((sMtoM.regs.insert .mstatus (Sail.BitVec.updateSubrange ms0 3 3 (_get_Mstatus_MPIE ms0))).insert .mstatus
          (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange ms0 3 3 (_get_Mstatus_MPIE ms0)) 7 7 1#1)).insert .cur_privilege .Machine) }
      rv64StandardMisaSU (by simp [Std.ExtDHashMap.get?_insert, hmisaMM]) (by decide)
    have hlpe := by
      have hbneM : bne Privilege.Machine .Machine = false := rfl
      have h := get_xLPE_Machine { sMtoM with regs := (mretRegsPreElp sMtoM.regs ms0 .Machine true).1 } 0#64
        (by dsimp only [mretRegsPreElp]; rw [hbneM, if_neg Bool.false_ne_true]; simp [Std.ExtDHashMap.get?_insert, hmsecMM])
      have hb : bool_bit_backwards (_get_Seccfg_MLPE 0#64) = false := by decide
      rw [hb] at h; exact h
    have hzca := by
      have hbneM : bne Privilege.Machine .Machine = false := rfl
      let p := mretRegsPreElp sMtoM.regs ms0 .Machine true
      have h := currentlyEnabled_Ext_Zca_of_misa_C
        { sMtoM with regs := p.1.insert .elp (if false then _get_Mstatus_MPELP p.2 else 0#1) } rv64StandardMisaSU
        (by dsimp only [p, mretRegsPreElp]; rw [hbneM, if_neg Bool.false_ne_true]; simp [Std.ExtDHashMap.get?_insert, hmisaMM])
      have hc : (_get_Misa_C rv64StandardMisaSU == 1#1) = false := by decide
      rw [hc] at h; exact h
    rw [sailExecuteMret_Machine_run sMtoM ms0 .Machine true false false 0x0000000080200082#64 hprivMM hmstatusMM hpbf hceU hlpe hmepcMM hzca]
    have hb1 : Sail.BitVec.updateSubrange ms0 3 3 (_get_Mstatus_MPIE ms0) = (ms0 ||| (1#64 <<< 3)) := by decide
    have hb2 : Sail.BitVec.updateSubrange (ms0 ||| (1#64 <<< 3)) 7 7 1#1 = (ms0 ||| (1#64 <<< 3)) := by decide
    have hb3 : Sail.BitVec.updateSubrange (ms0 ||| (1#64 <<< 3)) 12 11 (privLevel_to_bits .User) =
      ((1#64 <<< 17) ||| (1#64 <<< 7) ||| (1#64 <<< 3)) := by decide
    have hb5 : Sail.BitVec.updateSubrange ((1#64 <<< 17) ||| (1#64 <<< 7) ||| (1#64 <<< 3)) 41 41 0#1 =
      ((1#64 <<< 17) ||| (1#64 <<< 7) ||| (1#64 <<< 3)) := by decide
    have hb7 : Sail.BitVec.updateSubrange 0x0000000080200082#64 1 0 (zeros (n := 1 -i (0 -i 1))) = 0x0000000080200080#64 := by decide
    have hbneM : bne Privilege.Machine .Machine = false := rfl
    dsimp only [mretRegsPreElp]
    rw [hbneM, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, if_pos rfl,
        if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, hb1, hb2, hb3, hb5, hb7]
  · simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
  · simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
  · exact regs_get?_insert_self _ _ _


/-- End-to-end `SailM` bisimulation for `execute_SRET` (`InstsEnd.lean` lines 67504–67549,
    mirrored as `sailExecuteSret` and SHA-256 snippet-pinned):
    1. Proves `SRET` traps with `Illegal_Instruction ()` in `User` mode, in `Supervisor` mode
       when `mstatus.TSR = 1` (`[22]`), and in `Machine` mode when `misa.S = 0` (`Ext_S` disabled);
    2. Proves `SRET` from `Supervisor` mode (`TSR = 0`) with `SPP = 0` (`User`), `SPIE = 1`,
       `MPRV = 1`, and `SPELP = 1` (`senvcfg.LPE = 1`) restores `SIE := 1`, sets `SPIE := 1`,
       lowers `cur_privilege := .User`, clears `SPP := 0`, clears `MPRV := 0`, restores `elp := 1`
       while clearing `SPELP := 0` (`[23]`), and sets `nextPC` to `prepare_xret_target .Supervisor`;
    3. Proves `SRET` from `Machine` mode (`misa.S = 1`) with `SPP = 1` (`Supervisor`) succeeds even
       when `mstatus.TSR = 1`, lowering `cur_privilege := .Supervisor`, clearing `SPP := 0` and
       `MPRV := 0`, and jumping to `sepc`. -/
theorem rv64Sret_bisim_sail
    (sU sTsr sNoS sStoU sMtoS : SequentialState RegisterType trivialChoiceSource)
    (hprivU : sU.regs.get? .cur_privilege = some .User)
    (hprivTsr : sTsr.regs.get? .cur_privilege = some .Supervisor)
    (hmisaTsr : sTsr.regs.get? .misa = some rv64StandardMisaSU)
    (hmstatusTsr : sTsr.regs.get? .mstatus = some (1#64 <<< 22))
    (hprivNoS : sNoS.regs.get? .cur_privilege = some .Machine)
    (hmisaNoS : sNoS.regs.get? .misa = some (0b10#64 <<< 62 ||| (1#64 <<< 20)))
    (hprivSU : sStoU.regs.get? .cur_privilege = some .Supervisor)
    (hmisaSU : sStoU.regs.get? .misa = some rv64StandardMisaSUC)
    (hmstatusSU : sStoU.regs.get? .mstatus =
      some ((1#64 <<< 23) ||| (1#64 <<< 17) ||| (1#64 <<< 5)))
    (hmenvSU : sStoU.regs.get? .menvcfg = some 0#64)
    (hsenvSU : sStoU.regs.get? .senvcfg = some (1#64 <<< 2))
    (hsepcSU : sStoU.regs.get? .sepc = some 0x0000000000010082#64)
    (hprivMS : sMtoS.regs.get? .cur_privilege = some .Machine)
    (hmisaMS : sMtoS.regs.get? .misa = some rv64StandardMisaSU)
    (hmstatusMS : sMtoS.regs.get? .mstatus =
      some ((1#64 <<< 22) ||| (1#64 <<< 17) ||| (1#64 <<< 8) ||| (1#64 <<< 5)))
    (hmenvMS : sMtoS.regs.get? .menvcfg = some 0#64)
    (hsepcMS : sMtoS.regs.get? .sepc = some 0x0000000080200102#64) :
    let mstatusSUInit : BitVec 64 := (1#64 <<< 23) ||| (1#64 <<< 17) ||| (1#64 <<< 5)
    let mstatusSUFinal : BitVec 64 := (1#64 <<< 5) ||| (1#64 <<< 1)
    let regsSUAfter := ((((((((sStoU.regs.insert .mstatus (mstatusSUInit ||| (1#64 <<< 1))).insert
        .mstatus (mstatusSUInit ||| (1#64 <<< 1))).insert .cur_privilege .User).insert
        .mstatus (mstatusSUInit ||| (1#64 <<< 1))).insert
        .mstatus ((1#64 <<< 23) ||| (1#64 <<< 5) ||| (1#64 <<< 1))).insert
        .mstatus mstatusSUFinal).insert .elp 1#1).insert .nextPC 0x0000000000010082#64)
    let mstatusMSInit : BitVec 64 :=
      (1#64 <<< 22) ||| (1#64 <<< 17) ||| (1#64 <<< 8) ||| (1#64 <<< 5)
    let mstatusMSFinal : BitVec 64 := (1#64 <<< 22) ||| (1#64 <<< 5) ||| (1#64 <<< 1)
    let regsMSAfter := ((((((((sMtoS.regs.insert .mstatus (mstatusMSInit ||| (1#64 <<< 1))).insert
        .mstatus (mstatusMSInit ||| (1#64 <<< 1))).insert .cur_privilege .Supervisor).insert
        .mstatus ((1#64 <<< 22) ||| (1#64 <<< 17) ||| (1#64 <<< 5) ||| (1#64 <<< 1))).insert
        .mstatus mstatusMSFinal).insert .mstatus mstatusMSFinal).insert
        .elp 0#1).insert .nextPC 0x0000000080200100#64)
    (sailExecuteSret ()).run sU = .ok (.Illegal_Instruction ()) sU ∧
    (sailExecuteSret ()).run sTsr = .ok (.Illegal_Instruction ()) sTsr ∧
    (sailExecuteSret ()).run sNoS = .ok (.Illegal_Instruction ()) sNoS ∧
    (sailExecuteSret ()).run sStoU = .ok (.Retire_Success ()) { sStoU with regs := regsSUAfter } ∧
    regsSUAfter.get? .mstatus = some mstatusSUFinal ∧
    regsSUAfter.get? .cur_privilege = some .User ∧
    regsSUAfter.get? .elp = some 1#1 ∧
    regsSUAfter.get? .nextPC = some 0x0000000000010082#64 ∧
    (sailExecuteSret ()).run sMtoS = .ok (.Retire_Success ()) { sMtoS with regs := regsMSAfter } ∧
    regsMSAfter.get? .mstatus = some mstatusMSFinal ∧
    regsMSAfter.get? .cur_privilege = some .Supervisor ∧
    regsMSAfter.get? .nextPC = some 0x0000000080200100#64 := by
  have hceTsr := currentlyEnabled_Ext_S_standard sTsr rv64StandardMisaSU hmisaTsr (by decide)
  have hceNoS : (currentlyEnabled .Ext_S).run sNoS = .ok false sNoS := by
    rw [currentlyEnabled.eq_def]
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run,
      readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
    rw [currentlyEnabled.eq_def]
    dsimp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.run]
    rw [hmisaNoS]
    dsimp only [EStateM.bind, EStateM.pure]
    rw [hartSupports_Ext_S, hartSupports_Ext_Zicsr]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold sailExecuteSret
    rw [run_bind_ok _ _ _ _ true (by rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hprivU)]; rfl)]
    rfl
  · unfold sailExecuteSret
    rw [run_bind_ok _ _ _ _ true (by
      rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hprivTsr)]
      dsimp only []
      rw [run_bind_ok _ _ _ _ _ hceTsr]
      rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hmstatusTsr)]
      have htsr : (LeanRV64D.Functions.not true || (_get_Mstatus_TSR (1#64 <<< 22) == 1#1)) = true := by decide
      rw [htsr]; rfl)]
    rfl
  · unfold sailExecuteSret
    rw [run_bind_ok _ _ _ _ true (by
      rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hprivNoS)]
      dsimp only []
      rw [run_bind_ok _ _ _ _ _ hceNoS]; rfl)]
    rfl
  · let ms0 : BitVec 64 := (1#64 <<< 23) ||| (1#64 <<< 17) ||| (1#64 <<< 5)
    have hceSU := currentlyEnabled_Ext_S_standard sStoU rv64StandardMisaSUC hmisaSU (by decide)
    have hillegal : (do
      match (← readReg .cur_privilege) with
      | .User => pure true
      | .Supervisor =>
        pure ((LeanRV64D.Functions.not (← currentlyEnabled .Ext_S)) ||
          ((_get_Mstatus_TSR (← readReg .mstatus)) == 1#1))
      | .Machine => pure (LeanRV64D.Functions.not (← currentlyEnabled .Ext_S))
      | .VirtualUser =>
        internal_error "extensions/I/base_insts.sail" 607 "Hypervisor extension not supported"
      | .VirtualSupervisor =>
        internal_error "extensions/I/base_insts.sail" 608 "Hypervisor extension not supported").run sStoU =
        .ok false sStoU := by
      rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hprivSU)]
      dsimp only []
      rw [run_bind_ok _ _ _ _ _ hceSU]
      rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hmstatusSU)]
      have htsr0 : (LeanRV64D.Functions.not true || (_get_Mstatus_TSR ms0 == 1#1)) = false := by decide
      rw [htsr0]; rfl
    have hspp0 : (_get_Mstatus_SPP
      (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange ms0 1 1 (_get_Mstatus_SPIE ms0)) 5 5 1#1) == 1#1) = false := by decide
    have hlpe := by
      let p := sretRegsPreElp sStoU.regs ms0
      have hnp : p.2.2 = .User := by dsimp only [p, sretRegsPreElp]; rw [hspp0, if_neg Bool.false_ne_true]
      have h := get_xLPE_User_Ext_S { sStoU with regs := p.1 } rv64StandardMisaSUC 0#64 (1#64 <<< 2)
        (by simp [p, Std.ExtDHashMap.get?_insert, hmisaSU]) (by decide)
        (by simp [p, Std.ExtDHashMap.get?_insert, hmenvSU])
        (by simp [p, Std.ExtDHashMap.get?_insert, hsenvSU])
      have hb : bool_bit_backwards (_get_SEnvcfg_LPE (_update_SEnvcfg_SSE (1#64 <<< 2) (_get_MEnvcfg_SSE 0#64 &&& _get_SEnvcfg_SSE (1#64 <<< 2)))) = true := by decide
      rw [hb, ← hnp] at h; exact h
    have hzca := by
      let p := sretRegsPreElp sStoU.regs ms0
      have h := currentlyEnabled_Ext_Zca_of_misa_C
        { sStoU with regs := p.1.insert .elp (if true then _get_Mstatus_SPELP p.2.1 else 0#1) } rv64StandardMisaSUC
        (by simp [p, Std.ExtDHashMap.get?_insert, hmisaSU])
      have hc : (_get_Misa_C rv64StandardMisaSUC == 1#1) = true := by decide
      rw [hc] at h; exact h
    rw [sailExecuteSret_legal_run sStoU .Supervisor ms0 true true 0x0000000000010082#64 hillegal hprivSU hmstatusSU hlpe hsepcSU hzca]
    have hb1 : Sail.BitVec.updateSubrange ms0 1 1 (_get_Mstatus_SPIE ms0) = (ms0 ||| (1#64 <<< 1)) := by decide
    have hb2 : Sail.BitVec.updateSubrange (ms0 ||| (1#64 <<< 1)) 5 5 1#1 = (ms0 ||| (1#64 <<< 1)) := by decide
    have hb3 : Sail.BitVec.updateSubrange (ms0 ||| (1#64 <<< 1)) 8 8 0#1 = (ms0 ||| (1#64 <<< 1)) := by decide
    have hb4 : Sail.BitVec.updateSubrange (ms0 ||| (1#64 <<< 1)) 17 17 0#1 = ((1#64 <<< 23) ||| (1#64 <<< 5) ||| (1#64 <<< 1)) := by decide
    have hb5 : Sail.BitVec.updateSubrange ((1#64 <<< 23) ||| (1#64 <<< 5) ||| (1#64 <<< 1)) 23 23 0#1 = ((1#64 <<< 5) ||| (1#64 <<< 1)) := by decide
    have hb6 : _get_Mstatus_SPELP ((1#64 <<< 23) ||| (1#64 <<< 5) ||| (1#64 <<< 1)) = 1#1 := by decide
    have hb7 : BitVec.update 0x0000000000010082#64 0 0#1 = 0x0000000000010082#64 := by decide
    dsimp only [sretRegsPreElp]
    rw [hspp0, if_neg Bool.false_ne_true, if_pos rfl, if_pos rfl, hb1, hb2, hb3, hb4, hb5, hb6, hb7]
  · simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
  · simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
  · simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
  · exact regs_get?_insert_self _ _ _
  · let ms0 : BitVec 64 := (1#64 <<< 22) ||| (1#64 <<< 17) ||| (1#64 <<< 8) ||| (1#64 <<< 5)
    have hceMS := currentlyEnabled_Ext_S_standard sMtoS rv64StandardMisaSU hmisaMS (by decide)
    have hillegal : (do
      match (← readReg .cur_privilege) with
      | .User => pure true
      | .Supervisor => pure ((LeanRV64D.Functions.not (← currentlyEnabled .Ext_S)) || ((_get_Mstatus_TSR (← readReg .mstatus)) == 1#1))
      | .Machine => pure (LeanRV64D.Functions.not (← currentlyEnabled .Ext_S))
      | .VirtualUser => internal_error "extensions/I/base_insts.sail" 607 "Hypervisor extension not supported"
      | .VirtualSupervisor => internal_error "extensions/I/base_insts.sail" 608 "Hypervisor extension not supported").run sMtoS = .ok false sMtoS := by
      rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hprivMS)]; dsimp only []; rw [run_bind_ok _ _ _ _ _ hceMS]; rfl
    have hspp1 : (_get_Mstatus_SPP
      (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange ms0 1 1 (_get_Mstatus_SPIE ms0)) 5 5 1#1) == 1#1) = true := by decide
    have hlpe := by
      let p := sretRegsPreElp sMtoS.regs ms0
      have hnp : p.2.2 = .Supervisor := by dsimp only [p, sretRegsPreElp]; rw [hspp1, if_pos rfl]
      have h := get_xLPE_Supervisor { sMtoS with regs := p.1 } 0#64
        (by simp [p, Std.ExtDHashMap.get?_insert, hmenvMS])
      have hb : bool_bit_backwards (_get_MEnvcfg_LPE 0#64) = false := by decide
      rw [hb, ← hnp] at h; exact h
    have hzca := by
      let p := sretRegsPreElp sMtoS.regs ms0
      have h := currentlyEnabled_Ext_Zca_of_misa_C
        { sMtoS with regs := p.1.insert .elp (if false then _get_Mstatus_SPELP p.2.1 else 0#1) } rv64StandardMisaSU
        (by simp [p, Std.ExtDHashMap.get?_insert, hmisaMS])
      have hc : (_get_Misa_C rv64StandardMisaSU == 1#1) = false := by decide
      rw [hc] at h; exact h
    rw [sailExecuteSret_legal_run sMtoS .Machine ms0 false false 0x0000000080200102#64 hillegal hprivMS hmstatusMS hlpe hsepcMS hzca]
    have hb1 : Sail.BitVec.updateSubrange ms0 1 1 (_get_Mstatus_SPIE ms0) = (ms0 ||| (1#64 <<< 1)) := by decide
    have hb2 : Sail.BitVec.updateSubrange (ms0 ||| (1#64 <<< 1)) 5 5 1#1 = (ms0 ||| (1#64 <<< 1)) := by decide
    have hb3 : Sail.BitVec.updateSubrange (ms0 ||| (1#64 <<< 1)) 8 8 0#1 = ((1#64 <<< 22) ||| (1#64 <<< 17) ||| (1#64 <<< 5) ||| (1#64 <<< 1)) := by decide
    have hb4 : Sail.BitVec.updateSubrange ((1#64 <<< 22) ||| (1#64 <<< 17) ||| (1#64 <<< 5) ||| (1#64 <<< 1)) 17 17 0#1 = ((1#64 <<< 22) ||| (1#64 <<< 5) ||| (1#64 <<< 1)) := by decide
    have hb5 : Sail.BitVec.updateSubrange ((1#64 <<< 22) ||| (1#64 <<< 5) ||| (1#64 <<< 1)) 23 23 0#1 = ((1#64 <<< 22) ||| (1#64 <<< 5) ||| (1#64 <<< 1)) := by decide
    have hb7 : Sail.BitVec.updateSubrange 0x0000000080200102#64 1 0 (zeros (n := 1 -i (0 -i 1))) = 0x0000000080200100#64 := by decide
    dsimp only [sretRegsPreElp]
    rw [hspp1, if_pos rfl, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, hb1, hb2, hb3, hb4, hb5, hb7]
  · simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
  · simp [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
  · exact regs_get?_insert_self _ _ _

private theorem hartSupports_Ext_Zfinx : hartSupports .Ext_Zfinx = false := by
  rw [hartSupports.eq_def]

-- ============================================================================
-- Section 16: RV64F / RV64D Floating-Point State, IEEE-754 Classification,
--             Rounding / Exception Flags & Pure SailM Instruction Bisimulation
--             (Stage 3E.7 — zero RiscvExtras axioms)
-- ============================================================================
-- Note on upstream `opencompl/sail-riscv-lean` (`Lean_RV64D`) codegen:
-- In `LeanRV64D/Defs.lean`, `abbrev flenbits := BitVec (if true then 8 else 4 * 8)` evaluates
-- to `BitVec 8` on architectural `.f0 .. .f31` registers (an upstream Sail-to-Lean codegen
-- artifact), whereas `Functions.flen = 64`, `Functions.flen_bytes = 8`, `nan_box`/`nan_unbox`,
-- `fsplit_S`/`fmake_S`, `fsplit_D`/`fmake_D`, `float_classify`, `feq_quiet_*`/`flt_*`/`fle_*`,
-- and `Zfinx` `x`-register paths operate at full 32-bit / 64-bit IEEE-754 widths. Theorems 2 &
-- 6–8 below state exact `.f0` updates against upstream `flenbits` (`BitVec.setWidth 8`), while
-- Theorem 1 and `rv64FpFullWidth64NanBoxAndExec_bisim_sail` certify full-width 32/64-bit IEEE-754
-- NaN-boxing roundtrip and lossless `Zfinx` `x`-register execution without 8-bit truncation.

/-- Pure RV64F/D/Zfh IEEE-754 canonical NaN constants (`0x7e00` half, `0x7fc0_0000` single,
    `0x7ff8_0000_0000_0000` double) and 64-bit `FLEN = 64` NaN-boxing / NaN-unboxing specs. -/
def rv64CanonicalNaNHSpec : BitVec 16 := 0x7e00#16
def rv64CanonicalNaNSSpec : BitVec 32 := 0x7fc00000#32
def rv64CanonicalNaNDSpec : BitVec 64 := 0x7ff8000000000000#64

def rv64NanBoxSSpec (x : BitVec 32) : BitVec 64 :=
  BitVec.allOnes 32 +++ x

def rv64NanBoxHSpec (x : BitVec 16) : BitVec 64 :=
  BitVec.allOnes 48 +++ x

def rv64NanUnboxSSpec (x : BitVec 64) : BitVec 32 :=
  if x.extractLsb 63 32 == BitVec.allOnes 32 then
    x.extractLsb 31 0
  else
    rv64CanonicalNaNSSpec

def rv64NanUnboxHSpec (x : BitVec 64) : BitVec 16 :=
  if x.extractLsb 63 16 == BitVec.allOnes 48 then
    x.extractLsb 15 0
  else
    rv64CanonicalNaNHSpec

private theorem nan_box_32_eq (x : BitVec 32) : nan_box (n := 64) x = rv64NanBoxSSpec x := by
  unfold nan_box rv64NanBoxSSpec ones sail_ones Sail.BitVec.length
  change BitVec.setWidth 64 (~~~BitVec.zero 32 +++ x) = BitVec.allOnes 32 +++ x
  have hc : ~~~BitVec.zero 32 = BitVec.allOnes 32 := rfl
  rw [hc]
  exact BitVec.setWidth_eq _

private theorem nan_box_16_eq (x : BitVec 16) : nan_box (n := 64) x = rv64NanBoxHSpec x := by
  unfold nan_box rv64NanBoxHSpec ones sail_ones Sail.BitVec.length
  change BitVec.setWidth 64 (~~~BitVec.zero 48 +++ x) = BitVec.allOnes 48 +++ x
  have hc : ~~~BitVec.zero 48 = BitVec.allOnes 48 := rfl
  rw [hc]
  exact BitVec.setWidth_eq _

private theorem nan_box_64_eq (x : BitVec 64) : nan_box (n := 64) x = x := by
  unfold nan_box ones sail_ones Sail.BitVec.length
  simp [HAppend.hAppend, BitVec.append]
  exact BitVec.zero_or

private theorem nan_unbox_32_eq (x : BitVec 64) : nan_unbox (m := 32) x = rv64NanUnboxSSpec x := by
  unfold nan_unbox rv64NanUnboxSSpec canonical_NaN Sail.BitVec.extractLsb Sail.BitVec.length
    ones sail_ones zeros rv64CanonicalNaNSSpec
  have hc1 : (64 == 32) = false := rfl
  rw [hc1, if_neg Bool.false_ne_true]
  change (if (BitVec.extractLsb 63 32 x == BitVec.setWidth 32 (~~~BitVec.zero 32)) = true then
      BitVec.setWidth 32 (BitVec.extractLsb 31 0 x)
    else 0#1 +++ (~~~BitVec.zero 8 +++ (1#1 +++ BitVec.zero 22))) =
    (if (BitVec.extractLsb 63 32 x == BitVec.allOnes 32) = true then BitVec.extractLsb 31 0 x
    else 0x7fc00000#32)
  have hc2 : BitVec.setWidth 32 (~~~BitVec.zero 32) = BitVec.allOnes 32 := rfl
  have hc3 : (0#1 +++ (~~~BitVec.zero 8 +++ (1#1 +++ BitVec.zero 22))) = 0x7fc00000#32 := rfl
  rw [hc2, hc3]
  simp only [BitVec.setWidth_eq]

private theorem nan_unbox_16_eq (x : BitVec 64) : nan_unbox (m := 16) x = rv64NanUnboxHSpec x := by
  unfold nan_unbox rv64NanUnboxHSpec canonical_NaN Sail.BitVec.extractLsb Sail.BitVec.length
    ones sail_ones zeros rv64CanonicalNaNHSpec
  have hc1 : (64 == 16) = false := rfl
  rw [hc1, if_neg Bool.false_ne_true]
  change (if (BitVec.extractLsb 63 16 x == BitVec.setWidth 48 (~~~BitVec.zero 48)) = true then
      BitVec.setWidth 16 (BitVec.extractLsb 15 0 x)
    else 0#1 +++ (~~~BitVec.zero 5 +++ (1#1 +++ BitVec.zero 9))) =
    (if (BitVec.extractLsb 63 16 x == BitVec.allOnes 48) = true then BitVec.extractLsb 15 0 x
    else 0x7e00#16)
  have hc2 : BitVec.setWidth 48 (~~~BitVec.zero 48) = BitVec.allOnes 48 := rfl
  have hc3 : (0#1 +++ (~~~BitVec.zero 5 +++ (1#1 +++ BitVec.zero 9))) = 0x7e00#16 := rfl
  rw [hc2, hc3]
  simp only [BitVec.setWidth_eq]

private theorem nan_unbox_64_eq (x : BitVec 64) : nan_unbox (m := 64) x = x := by
  unfold nan_unbox Sail.BitVec.length
  have hc : (64 == 64) = true := rfl
  rw [hc, if_pos rfl]
  exact BitVec.setWidth_eq x

private theorem extractLsb_append_hi_32 (hi lo : BitVec 32) :
    BitVec.extractLsb 63 32 (hi +++ lo) = hi :=
  BitVec.extractLsb'_append_eq_left

private theorem extractLsb_append_hi_16 (hi : BitVec 48) (lo : BitVec 16) :
    BitVec.extractLsb 63 16 (hi +++ lo) = hi :=
  BitVec.extractLsb'_append_eq_left

private theorem extractLsb_append_lo_32 (hi lo : BitVec 32) :
    BitVec.extractLsb 31 0 (hi +++ lo) = lo :=
  BitVec.extractLsb'_append_eq_right

private theorem extractLsb_append_lo_16 (hi : BitVec 48) (lo : BitVec 16) :
    BitVec.extractLsb 15 0 (hi +++ lo) = lo :=
  BitVec.extractLsb'_append_eq_right

/-- Theorem 1 (Section 16): RV64F/D enablement (`misa.F`/`misa.D` + `mstatus.FS != 0b00`),
    load/store width gating (`4` and `8` bytes), `FLEN = 64`, IEEE-754 canonical NaNs, and
    64-bit NaN-boxing / NaN-unboxing roundtrip & unboxed canonical fallback. -/
theorem rv64FpEnablementAndNanBoxing_bisim_sail
    (x32 : BitVec 32) (x16 : BitVec 16) (x64 misaVal mstatusVal : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hmisa : s.regs.get? .misa = some misaVal)
    (hmstatus : s.regs.get? .mstatus = some mstatusVal) :
    Functions.flen = 64 ∧
    Functions.flen_bytes = 8 ∧
    canonical_NaN_H () = rv64CanonicalNaNHSpec ∧
    canonical_NaN_S () = rv64CanonicalNaNSSpec ∧
    canonical_NaN_D () = rv64CanonicalNaNDSpec ∧
    nan_box (n := 64) x32 = rv64NanBoxSSpec x32 ∧
    nan_box (n := 64) x16 = rv64NanBoxHSpec x16 ∧
    nan_box (n := 64) x64 = x64 ∧
    nan_unbox (m := 32) x64 = rv64NanUnboxSSpec x64 ∧
    nan_unbox (m := 16) x64 = rv64NanUnboxHSpec x64 ∧
    nan_unbox (m := 64) x64 = x64 ∧
    nan_unbox (m := 32) (nan_box (n := 64) x32) = x32 ∧
    nan_unbox (m := 16) (nan_box (n := 64) x16) = x16 ∧
    nan_unbox (m := 32) ((0#1 +++ BitVec.allOnes 31) +++ x32) = rv64CanonicalNaNSSpec ∧
    nan_unbox (m := 16) ((0#1 +++ BitVec.allOnes 47) +++ x16) = rv64CanonicalNaNHSpec ∧
    (currentlyEnabled .Ext_F).run s =
      .ok ((_get_Misa_F misaVal == 1#1) && (_get_Mstatus_FS mstatusVal != 0b00#2)) s ∧
    (currentlyEnabled .Ext_D).run s =
      .ok ((_get_Misa_D misaVal == 1#1) && (_get_Mstatus_FS mstatusVal != 0b00#2)) s ∧
    (float_load_store_width_supported 4).run s =
      .ok ((_get_Misa_F misaVal == 1#1) && (_get_Mstatus_FS mstatusVal != 0b00#2)) s ∧
    (float_load_store_width_supported 8).run s =
      .ok ((_get_Misa_D misaVal == 1#1) && (_get_Mstatus_FS mstatusVal != 0b00#2)) s := by
  have hceF : (currentlyEnabled .Ext_F).run s =
      .ok ((_get_Misa_F misaVal == 1#1) && (_get_Mstatus_FS mstatusVal != 0b00#2)) s := by
    rw [currentlyEnabled.eq_def]
    rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hmisa)]
    rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hmstatus)]
    have hzicsr : (currentlyEnabled .Ext_Zicsr).run s = .ok true s := by
      rw [currentlyEnabled.eq_def]
      dsimp only [Pure.pure, EStateM.pure, EStateM.run]
      rw [hartSupports_Ext_Zicsr]
    rw [run_bind_ok _ _ _ _ _ hzicsr]
    dsimp only [Pure.pure, EStateM.pure, EStateM.run]
    rw [hartSupports_Ext_F]
    simp only [Bool.true_and, Bool.and_true]
  have hceD : (currentlyEnabled .Ext_D).run s =
      .ok ((_get_Misa_D misaVal == 1#1) && (_get_Mstatus_FS mstatusVal != 0b00#2)) s := by
    rw [currentlyEnabled.eq_def]
    rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hmisa)]
    rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hmstatus)]
    have hzicsr : (currentlyEnabled .Ext_Zicsr).run s = .ok true s := by
      rw [currentlyEnabled.eq_def]
      dsimp only [Pure.pure, EStateM.pure, EStateM.run]
      rw [hartSupports_Ext_Zicsr]
    rw [run_bind_ok _ _ _ _ _ hzicsr]
    dsimp only [Pure.pure, EStateM.pure, EStateM.run]
    have hflen : (Functions.flen ≥b 64) = true := rfl
    rw [hartSupports_Ext_D, hflen]
    simp only [Bool.true_and, Bool.and_true]
  refine ⟨rfl, rfl, rfl, rfl, rfl,
    nan_box_32_eq x32, nan_box_16_eq x16, nan_box_64_eq x64,
    nan_unbox_32_eq x64, nan_unbox_16_eq x64, nan_unbox_64_eq x64,
    ?_, ?_, ?_, ?_, hceF, hceD, ?_, ?_⟩
  · rw [nan_box_32_eq, nan_unbox_32_eq]; unfold rv64NanUnboxSSpec rv64NanBoxSSpec
    rw [extractLsb_append_hi_32, extractLsb_append_lo_32]; rfl
  · rw [nan_box_16_eq, nan_unbox_16_eq]; unfold rv64NanUnboxHSpec rv64NanBoxHSpec
    rw [extractLsb_append_hi_16, extractLsb_append_lo_16]; rfl
  · rw [nan_unbox_32_eq]; unfold rv64NanUnboxSSpec
    rw [extractLsb_append_hi_32]
    have hne : ((0#1 +++ BitVec.allOnes 31) == BitVec.allOnes 32) = false := rfl
    rw [hne]; rfl
  · rw [nan_unbox_16_eq]; unfold rv64NanUnboxHSpec
    rw [extractLsb_append_hi_16]
    have hne : ((0#1 +++ BitVec.allOnes 47) == BitVec.allOnes 48) = false := rfl
    rw [hne]; rfl
  · unfold float_load_store_width_supported; exact hceF
  · unfold float_load_store_width_supported; exact hceD

/-- Pure `TurboLean`-side specification for `dirty_fd_context` (`FdextRegs.lean` lines 298–304):
    sets `mstatus.FS` (`[14:13]`) to `Dirty` (`0b11`) and `mstatus.SD` (`[63]`) to `1`. -/
def rv64DirtyFdMstatusSpec (mstatusVal : BitVec 64) : BitVec 64 :=
  Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange mstatusVal 14 13 0b11#2) 63 63 1#1

private theorem dirty_fd_context_run
    (s : SequentialState RegisterType trivialChoiceSource)
    (mstatusVal : BitVec 64)
    (hmstatus : s.regs.get? .mstatus = some mstatusVal) :
    ∃ regs', (dirty_fd_context ()).run s = .ok () { s with regs := regs' } ∧
      regs'.get? .mstatus = some (rv64DirtyFdMstatusSpec mstatusVal) ∧
      (∀ r, (Register.mstatus == r) = false → regs'.get? r = s.regs.get? r) := by
  let ms1 := Sail.BitVec.updateSubrange mstatusVal 14 13 (extStatus_map_forwards .Dirty)
  let ms2 := Sail.BitVec.updateSubrange ms1 (64 -i 1) (64 -i 1) 1#1
  let regs' := (s.regs.insert .mstatus ms1).insert .mstatus ms2
  refine ⟨regs', ?_, ?_, ?_⟩
  · unfold dirty_fd_context
    have ha : (PreSail.assert (hartSupports .Ext_F)
        "extensions/FD/fdext_regs.sail:111.28-111.29" : SailM Unit).run s = .ok () s := by
      unfold PreSail.assert; rw [hartSupports_Ext_F]; rfl
    rw [run_bind_ok _ _ _ _ _ ha]
    rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hmstatus)]
    rw [run_bind_ok _ _ _ _ _ (writeReg_run_ok _ _ _)]
    have hms1 : (s.regs.insert .mstatus ms1).get? .mstatus = some ms1 := regs_get?_insert_self _ _ _
    rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hms1)]
    rw [run_bind_ok _ _ _ _ _ (writeReg_run_ok _ _ _)]
    have hms2 : regs'.get? .mstatus = some ms2 := regs_get?_insert_self _ _ _
    rw [run_bind_ok _ _ _ _ _ (readReg_run_ok _ _ _ hms2)]
    rfl
  · exact regs_get?_insert_self _ _ _
  · intro r hne
    dsimp only [regs']
    rw [regs_get?_insert_ne _ _ _ _ hne, regs_get?_insert_ne _ _ _ _ hne]

private theorem dirty_fd_context_if_present_run
    (s : SequentialState RegisterType trivialChoiceSource)
    (mstatusVal : BitVec 64)
    (hmstatus : s.regs.get? .mstatus = some mstatusVal) :
    ∃ regs', (dirty_fd_context_if_present ()).run s = .ok () { s with regs := regs' } ∧
      regs'.get? .mstatus = some (rv64DirtyFdMstatusSpec mstatusVal) ∧
      (∀ r, (Register.mstatus == r) = false → regs'.get? r = s.regs.get? r) := by
  unfold dirty_fd_context_if_present
  have ha : (PreSail.assert (neq_bool (hartSupports .Ext_F) (hartSupports .Ext_Zfinx))
      "extensions/FD/fdext_regs.sail:118.55-118.56" : SailM Unit).run s = .ok () s := by
    unfold PreSail.assert neq_bool
    rw [hartSupports_Ext_F, hartSupports_Ext_Zfinx]; rfl
  rw [run_bind_ok _ _ _ _ _ ha]
  rw [hartSupports_Ext_F, if_pos rfl]
  exact dirty_fd_context_run s mstatusVal hmstatus

private theorem nan_unbox_flenbits_32 (v : flenbits) :
    nan_unbox (m := 32) v = BitVec.setWidth 32 v := by
  let b : BitVec 8 := v
  suffices h : nan_unbox (m := 32) b = BitVec.setWidth 32 b from h
  unfold nan_unbox Sail.BitVec.extractLsb Sail.BitVec.length ones sail_ones
  have hc1 : (8 == 32) = false := rfl
  rw [hc1, if_neg Bool.false_ne_true]
  change (if (BitVec.extractLsb 7 32 b == 0#1) = true then
      BitVec.setWidth 32 (BitVec.extractLsb 31 0 b)
    else canonical_NaN (n := 32)) = BitVec.setWidth 32 b
  have h1 : BitVec.extractLsb 7 32 b = 0#1 := by
    apply BitVec.eq_of_toNat_eq
    have hb : b.toNat < 256 := b.isLt
    simp [BitVec.extractLsb, BitVec.extractLsb']; omega
  rw [h1, beq_self_eq_true, if_pos rfl]
  ext i hi; simp [BitVec.extractLsb, BitVec.extractLsb']

private theorem setWidth_flenbits_nan_box_32 (x : BitVec 32) :
    BitVec.setWidth (if true = true then 8 else 4 * 8) (nan_box (n := 8 *i 8) x) =
      (BitVec.setWidth 8 x : flenbits) := by
  change BitVec.setWidth 8 (nan_box (n := 64) x) = BitVec.setWidth 8 x
  rw [nan_box_32_eq]; unfold rv64NanBoxSSpec
  ext i hi
  have hi32 : i < 32 := by omega
  simp only [BitVec.getElem_setWidth]
  rw [BitVec.getLsbD_append, if_pos hi32]

private theorem setWidth_flenbits_nan_box_64 (x : BitVec 64) :
    BitVec.setWidth (if true = true then 8 else 4 * 8) (nan_box (n := 8 *i 8) x) =
      (BitVec.setWidth 8 x : flenbits) := by
  change BitVec.setWidth 8 (nan_box (n := 64) x) = BitVec.setWidth 8 x
  rw [nan_box_64_eq]

private theorem rF_bits_f0_run (val : flenbits)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hf0 : s.regs.get? .f0 = some val) :
    (rF_bits (.Fregidx 0#5)).run s = .ok val s := by
  unfold rF_bits rF
  have ha : (PreSail.assert (hartSupports .Ext_F) "extensions/FD/fdext_regs.sail:123.28-123.29" : SailM Unit).run s = .ok () s := by
    unfold PreSail.assert; rw [hartSupports_Ext_F]; rfl
  rw [run_bind_ok _ _ _ _ _ ha]; dsimp only [Sail.BitVec.toNatInt]
  change (do let v ← readReg .f0; pure (fregval_from_freg v)).run s = .ok val s
  rw [run_bind_ok _ _ _ _ _ (readReg_run_ok .f0 val s hf0)]; rfl

private theorem rF_bits_f1_run (val : flenbits)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hf1 : s.regs.get? .f1 = some val) :
    (rF_bits (.Fregidx 1#5)).run s = .ok val s := by
  unfold rF_bits rF
  have ha : (PreSail.assert (hartSupports .Ext_F) "extensions/FD/fdext_regs.sail:123.28-123.29" : SailM Unit).run s = .ok () s := by
    unfold PreSail.assert; rw [hartSupports_Ext_F]; rfl
  rw [run_bind_ok _ _ _ _ _ ha]; dsimp only [Sail.BitVec.toNatInt]
  change (do let v ← readReg .f1; pure (fregval_from_freg v)).run s = .ok val s
  rw [run_bind_ok _ _ _ _ _ (readReg_run_ok .f1 val s hf1)]; rfl

private theorem wF_bits_f0_run (val : flenbits) (mstatusVal : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hmstatus : s.regs.get? .mstatus = some mstatusVal) :
    ∃ regs', (wF_bits (.Fregidx 0#5) val).run s = .ok () { s with regs := regs' } ∧
      regs'.get? .f0 = some val ∧
      regs'.get? .mstatus = some (rv64DirtyFdMstatusSpec mstatusVal) ∧
      (∀ r, (Register.f0 == r) = false → (Register.mstatus == r) = false →
        regs'.get? r = s.regs.get? r) := by
  have hms' : (s.regs.insert .f0 val).get? .mstatus = some mstatusVal := by
    rw [regs_get?_insert_ne _ _ _ _ rfl]; exact hmstatus
  obtain ⟨regs', hdirty, hmsOut, hother⟩ :=
    dirty_fd_context_run { s with regs := s.regs.insert .f0 val } mstatusVal hms'
  refine ⟨regs', ?_, by rw [hother .f0 rfl, regs_get?_insert_self], hmsOut,
    fun r hnef0 hnems => by rw [hother r hnems, regs_get?_insert_ne _ _ _ _ hnef0]⟩
  unfold wF_bits wF
  have ha : (PreSail.assert (hartSupports .Ext_F) "extensions/FD/fdext_regs.sail:164.28-164.29" : SailM Unit).run s = .ok () s := by
    unfold PreSail.assert; rw [hartSupports_Ext_F]; rfl
  rw [run_bind_ok _ _ _ _ _ ha]; dsimp only [Sail.BitVec.toNatInt, fregval_into_freg]
  change (do writeReg .f0 val; dirty_fd_context ()).run s = _
  rw [run_bind_ok _ _ _ _ _ (writeReg_run_ok .f0 val s)]; exact hdirty

private theorem rF_or_X_S_of_rF_bits (idx : fregidx) (val : flenbits)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hr : (rF_bits idx).run s = .ok val s) :
    (rF_or_X_S idx).run s = .ok (BitVec.setWidth 32 val) s := by
  unfold rF_or_X_S
  have ha1 : (PreSail.assert (Functions.flen ≥b 32) "extensions/FD/fdext_regs.sail:276.19-276.20" : SailM Unit).run s = .ok () s := rfl
  have ha2 : (PreSail.assert (neq_bool (hartSupports .Ext_F) (hartSupports .Ext_Zfinx))
      "extensions/FD/fdext_regs.sail:277.55-277.56" : SailM Unit).run s = .ok () s := by
    unfold PreSail.assert neq_bool; rw [hartSupports_Ext_F, hartSupports_Ext_Zfinx]; rfl
  rw [run_bind_ok _ _ _ _ _ ha1, run_bind_ok _ _ _ _ _ ha2, hartSupports_Ext_F, if_pos rfl]
  unfold rF_S
  have ha3 : (PreSail.assert (Functions.flen ≥b 32) "extensions/FD/fdext_regs.sail:239.19-239.20" : SailM Unit).run s = .ok () s := rfl
  have ha4 : (PreSail.assert (hartSupports .Ext_F && LeanRV64D.Functions.not (hartSupports .Ext_Zfinx))
      "extensions/FD/fdext_regs.sail:240.59-240.60" : SailM Unit).run s = .ok () s := by
    unfold PreSail.assert LeanRV64D.Functions.not; rw [hartSupports_Ext_F, hartSupports_Ext_Zfinx]; rfl
  rw [run_bind_ok _ _ _ _ _ ha3, run_bind_ok _ _ _ _ _ ha4, run_bind_ok _ _ _ _ _ hr]
  dsimp only [Pure.pure, EStateM.pure, EStateM.run]; rw [nan_unbox_flenbits_32]

private theorem rF_or_X_D_of_rF_bits (idx : fregidx) (val : flenbits)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hr : (rF_bits idx).run s = .ok val s) :
    (rF_or_X_D idx).run s = .ok (BitVec.setWidth 64 val) s := by
  unfold rF_or_X_D
  have ha1 : (PreSail.assert (Functions.flen ≥b 64) "extensions/FD/fdext_regs.sail:284.19-284.20" : SailM Unit).run s = .ok () s := rfl
  have ha2 : (PreSail.assert (neq_bool (hartSupports .Ext_F) (hartSupports .Ext_Zfinx))
      "extensions/FD/fdext_regs.sail:285.55-285.56" : SailM Unit).run s = .ok () s := by
    unfold PreSail.assert neq_bool; rw [hartSupports_Ext_F, hartSupports_Ext_Zfinx]; rfl
  rw [run_bind_ok _ _ _ _ _ ha1, run_bind_ok _ _ _ _ _ ha2, hartSupports_Ext_F, if_pos rfl]
  unfold rF_D
  have ha3 : (PreSail.assert (Functions.flen ≥b 64) "extensions/FD/fdext_regs.sail:251.19-251.20" : SailM Unit).run s = .ok () s := rfl
  have ha4 : (PreSail.assert (hartSupports .Ext_F && LeanRV64D.Functions.not (hartSupports .Ext_Zfinx))
      "extensions/FD/fdext_regs.sail:252.59-252.60" : SailM Unit).run s = .ok () s := by
    unfold PreSail.assert LeanRV64D.Functions.not; rw [hartSupports_Ext_F, hartSupports_Ext_Zfinx]; rfl
  rw [run_bind_ok _ _ _ _ _ ha3, run_bind_ok _ _ _ _ _ ha4, run_bind_ok _ _ _ _ _ hr]; rfl

private theorem rF_or_X_S_f0_run (val : flenbits)
    (s : SequentialState RegisterType trivialChoiceSource) (hf0 : s.regs.get? .f0 = some val) :
    (rF_or_X_S (.Fregidx 0#5)).run s = .ok (BitVec.setWidth 32 val) s :=
  rF_or_X_S_of_rF_bits (.Fregidx 0#5) val s (rF_bits_f0_run val s hf0)

private theorem rF_or_X_S_f1_run (val : flenbits)
    (s : SequentialState RegisterType trivialChoiceSource) (hf1 : s.regs.get? .f1 = some val) :
    (rF_or_X_S (.Fregidx 1#5)).run s = .ok (BitVec.setWidth 32 val) s :=
  rF_or_X_S_of_rF_bits (.Fregidx 1#5) val s (rF_bits_f1_run val s hf1)

private theorem rF_or_X_D_f0_run (val : flenbits)
    (s : SequentialState RegisterType trivialChoiceSource) (hf0 : s.regs.get? .f0 = some val) :
    (rF_or_X_D (.Fregidx 0#5)).run s = .ok (BitVec.setWidth 64 val) s :=
  rF_or_X_D_of_rF_bits (.Fregidx 0#5) val s (rF_bits_f0_run val s hf0)

private theorem rF_or_X_D_f1_run (val : flenbits)
    (s : SequentialState RegisterType trivialChoiceSource) (hf1 : s.regs.get? .f1 = some val) :
    (rF_or_X_D (.Fregidx 1#5)).run s = .ok (BitVec.setWidth 64 val) s :=
  rF_or_X_D_of_rF_bits (.Fregidx 1#5) val s (rF_bits_f1_run val s hf1)

private theorem wF_or_X_S_f0_run (val32 : BitVec 32) (mstatusVal : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hmstatus : s.regs.get? .mstatus = some mstatusVal) :
    ∃ regs', (wF_or_X_S (.Fregidx 0#5) val32).run s = .ok () { s with regs := regs' } ∧
      regs'.get? .f0 = some (BitVec.setWidth 8 val32 : flenbits) ∧
      regs'.get? .mstatus = some (rv64DirtyFdMstatusSpec mstatusVal) ∧
      (∀ r, (Register.f0 == r) = false → (Register.mstatus == r) = false →
        regs'.get? r = s.regs.get? r) := by
  unfold wF_or_X_S
  have ha1 : (PreSail.assert (Functions.flen ≥b 32) "extensions/FD/fdext_regs.sail:306.19-306.20" : SailM Unit).run s = .ok () s := rfl
  have ha2 : (PreSail.assert (neq_bool (hartSupports .Ext_F) (hartSupports .Ext_Zfinx))
      "extensions/FD/fdext_regs.sail:307.55-307.56" : SailM Unit).run s = .ok () s := by
    unfold PreSail.assert neq_bool; rw [hartSupports_Ext_F, hartSupports_Ext_Zfinx]; rfl
  rw [run_bind_ok _ _ _ _ _ ha1, run_bind_ok _ _ _ _ _ ha2, hartSupports_Ext_F, if_pos rfl]
  unfold wF_S
  have ha3 : (PreSail.assert (Functions.flen ≥b 32) "extensions/FD/fdext_regs.sail:245.19-245.20" : SailM Unit).run s = .ok () s := rfl
  have ha4 : (PreSail.assert (hartSupports .Ext_F && LeanRV64D.Functions.not (hartSupports .Ext_Zfinx))
      "extensions/FD/fdext_regs.sail:246.59-246.60" : SailM Unit).run s = .ok () s := by
    unfold PreSail.assert LeanRV64D.Functions.not; rw [hartSupports_Ext_F, hartSupports_Ext_Zfinx]; rfl
  rw [run_bind_ok _ _ _ _ _ ha3, run_bind_ok _ _ _ _ _ ha4, setWidth_flenbits_nan_box_32]
  exact wF_bits_f0_run (BitVec.setWidth 8 val32) mstatusVal s hmstatus

private theorem wF_or_X_D_f0_run (val64 mstatusVal : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hmstatus : s.regs.get? .mstatus = some mstatusVal) :
    ∃ regs', (wF_or_X_D (.Fregidx 0#5) val64).run s = .ok () { s with regs := regs' } ∧
      regs'.get? .f0 = some (BitVec.setWidth 8 val64 : flenbits) ∧
      regs'.get? .mstatus = some (rv64DirtyFdMstatusSpec mstatusVal) ∧
      (∀ r, (Register.f0 == r) = false → (Register.mstatus == r) = false →
        regs'.get? r = s.regs.get? r) := by
  unfold wF_or_X_D
  have ha1 : (PreSail.assert (Functions.flen ≥b 64) "extensions/FD/fdext_regs.sail:314.20-314.21" : SailM Unit).run s = .ok () s := rfl
  have ha2 : (PreSail.assert (neq_bool (hartSupports .Ext_F) (hartSupports .Ext_Zfinx))
      "extensions/FD/fdext_regs.sail:315.55-315.56" : SailM Unit).run s = .ok () s := by
    unfold PreSail.assert neq_bool; rw [hartSupports_Ext_F, hartSupports_Ext_Zfinx]; rfl
  rw [run_bind_ok _ _ _ _ _ ha1, run_bind_ok _ _ _ _ _ ha2, hartSupports_Ext_F, if_pos rfl]
  unfold wF_D
  have ha3 : (PreSail.assert (Functions.flen ≥b 64) "extensions/FD/fdext_regs.sail:257.19-257.20" : SailM Unit).run s = .ok () s := rfl
  have ha4 : (PreSail.assert (hartSupports .Ext_F && LeanRV64D.Functions.not (hartSupports .Ext_Zfinx))
      "extensions/FD/fdext_regs.sail:258.59-258.60" : SailM Unit).run s = .ok () s := by
    unfold PreSail.assert LeanRV64D.Functions.not; rw [hartSupports_Ext_F, hartSupports_Ext_Zfinx]; rfl
  rw [run_bind_ok _ _ _ _ _ ha3, run_bind_ok _ _ _ _ _ ha4]
  exact wF_bits_f0_run (BitVec.setWidth 8 val64) mstatusVal s hmstatus

/-- Theorem 2 (Section 16): Floating-point register file (`rF_bits`, `wF_bits`, `rF_S`, `rF_D`,
    `rF_or_X_S`, `rF_or_X_D`, `wF_or_X_S`, `wF_or_X_D` over upstream `flenbits = BitVec 8`),
    compressed index decoding (`cfregidx_to_fregidx`: `f8..f15`), and `dirty_fd_context`
    (`mstatus.FS := 0b11`, `SD := 1`). -/
theorem rv64FpRegsAndDirtyContext_bisim_sail
    (f0Val : flenbits) (val64 mstatusVal : BitVec 64) (val32 : BitVec 32) (cidx : BitVec 3)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hf0 : s.regs.get? .f0 = some f0Val)
    (hmstatus : s.regs.get? .mstatus = some mstatusVal) :
    cfregidx_to_fregidx (.Cfregidx cidx) = .Fregidx (0b01#2 +++ cidx) ∧
    (rF_bits (.Fregidx 0#5)).run s = .ok f0Val s ∧
    (rF_or_X_S (.Fregidx 0#5)).run s = .ok (BitVec.setWidth 32 f0Val) s ∧
    (rF_or_X_D (.Fregidx 0#5)).run s = .ok (BitVec.setWidth 64 f0Val) s ∧
    (∃ regsS, (wF_or_X_S (.Fregidx 0#5) val32).run s = .ok () { s with regs := regsS } ∧
      regsS.get? .f0 = some (BitVec.setWidth 8 val32 : flenbits) ∧
      regsS.get? .mstatus = some (rv64DirtyFdMstatusSpec mstatusVal)) ∧
    (∃ regsD, (wF_or_X_D (.Fregidx 0#5) val64).run s = .ok () { s with regs := regsD } ∧
      regsD.get? .f0 = some (BitVec.setWidth 8 val64 : flenbits) ∧
      regsD.get? .mstatus = some (rv64DirtyFdMstatusSpec mstatusVal)) := by
  obtain ⟨regsS, hwS, hf0S, hmsS, _⟩ := wF_or_X_S_f0_run val32 mstatusVal s hmstatus
  obtain ⟨regsD, hwD, hf0D, hmsD, _⟩ := wF_or_X_D_f0_run val64 mstatusVal s hmstatus
  exact ⟨rfl, rF_bits_f0_run f0Val s hf0, rF_or_X_S_f0_run f0Val s hf0,
    rF_or_X_D_f0_run f0Val s hf0, ⟨regsS, hwS, hf0S, hmsS⟩, ⟨regsD, hwD, hf0D, hmsD⟩⟩


/-- Pure `TurboLean`-side specification for `select_instr_or_fcsr_rm` (`FextInsts.lean`, lines 286–302):
    static instruction rounding modes (`RNE`/`RTZ`/`RDN`/`RUP`/`RMM`) pass through directly;
    `RM_DYN` (`0b111`) decodes `fcsr.FRM` (`[7:5]`) and returns `none` on reserved `0b101`, `0b110`,
    or `0b111` under `fcsr_rm_reserved_behavior = .Fcsr_RM_Illegal`. -/
def rv64SelectRmSpec (instrRm : rounding_mode) (fcsrVal : BitVec 32) : Option rounding_mode :=
  match instrRm with
  | .RM_DYN =>
    match Sail.BitVec.extractLsb fcsrVal 7 5 with
    | 0b000#3 => some .RM_RNE
    | 0b001#3 => some .RM_RTZ
    | 0b010#3 => some .RM_RDN
    | 0b011#3 => some .RM_RUP
    | 0b100#3 => some .RM_RMM
    | _ => none
  | rm => some rm

/-- Pure `TurboLean`-side specification for `write_fcsr` (`FdextRegs.lean`, lines 902–905):
    updates `fcsr.FRM` (`[7:5]`) and `fcsr.FFLAGS` (`[4:0]`) and marks `mstatus.FS` dirty. -/
def rv64WriteFcsrSpec (fcsrVal : BitVec 32) (frm : BitVec 3) (fflags : BitVec 5) : BitVec 32 :=
  Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange fcsrVal 7 5 frm) 4 0 fflags

/-- Pure `TurboLean`-side specification for `accrue_fflags` (`FdextRegs.lean`, lines 907–920):
    ORs `flags` into `fcsr.FFLAGS` (`[4:0]`). -/
def rv64AccrueFflagsFcsrSpec (fcsrVal : BitVec 32) (flags : BitVec 5) : BitVec 32 :=
  Sail.BitVec.updateSubrange fcsrVal 4 0 (_get_Fcsr_FFLAGS fcsrVal ||| flags)

private theorem csr_name_write_callback_fflags_run (val : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource) :
    (csr_name_write_callback "fflags" val).run s = .ok () s := rfl

private theorem csr_name_write_callback_fcsr_run (val : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource) :
    (csr_name_write_callback "fcsr" val).run s = .ok () s := rfl

private theorem accrue_fflags_run (fcsrVal : BitVec 32) (mstatusVal : BitVec 64) (flags : BitVec 5)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hfcsr : s.regs.get? .fcsr = some fcsrVal)
    (hmstatus : s.regs.get? .mstatus = some mstatusVal) :
    ∃ regs', (accrue_fflags flags).run s = .ok () { s with regs := regs' } ∧
      regs'.get? .fcsr = some (rv64AccrueFflagsFcsrSpec fcsrVal flags) ∧
      regs'.get? .mstatus =
        some (if _get_Fcsr_FFLAGS fcsrVal != (_get_Fcsr_FFLAGS fcsrVal ||| flags) then
            rv64DirtyFdMstatusSpec mstatusVal
          else mstatusVal) ∧
      (∀ r, (Register.fcsr == r) = false → (Register.mstatus == r) = false →
        regs'.get? r = s.regs.get? r) := by
  let newFcsr := rv64AccrueFflagsFcsrSpec fcsrVal flags
  let s1 := { s with regs := s.regs.insert .fcsr newFcsr }
  have hms1 : s1.regs.get? .mstatus = some mstatusVal := by
    dsimp only [s1]; rw [regs_get?_insert_ne _ _ _ _ rfl]; exact hmstatus
  have hfcsr1 : s1.regs.get? .fcsr = some newFcsr := regs_get?_insert_self _ _ _
  have hcb (st : SequentialState RegisterType trivialChoiceSource)
      (hfc : st.regs.get? .fcsr = some newFcsr) :
      (do
        let v1 ← readReg .fcsr
        csr_name_write_callback "fflags" (zero_extend (m := 64) (_get_Fcsr_FFLAGS v1))
        let v2 ← readReg .fcsr
        csr_name_write_callback "fcsr" (zero_extend (m := 64) v2)).run st = .ok () st := by
    rw [run_bind_ok _ _ _ _ _ (readReg_run_ok .fcsr newFcsr st hfc),
        run_bind_ok _ _ _ _ _ (csr_name_write_callback_fflags_run _ st),
        run_bind_ok _ _ _ _ _ (readReg_run_ok .fcsr newFcsr st hfc)]
    exact csr_name_write_callback_fcsr_run _ st
  have hpre (stOut : SequentialState RegisterType trivialChoiceSource)
      (htail : (do
        if (_get_Fcsr_FFLAGS fcsrVal != (_get_Fcsr_FFLAGS fcsrVal ||| flags)) = true then do
          dirty_fd_context_if_present ()
          let v1 ← readReg .fcsr
          csr_name_write_callback "fflags" (zero_extend (m := 64) (_get_Fcsr_FFLAGS v1))
          let v2 ← readReg .fcsr
          csr_name_write_callback "fcsr" (zero_extend (m := 64) v2)
        else do
          pure ()
          let v1 ← readReg .fcsr
          csr_name_write_callback "fflags" (zero_extend (m := 64) (_get_Fcsr_FFLAGS v1))
          let v2 ← readReg .fcsr
          csr_name_write_callback "fcsr" (zero_extend (m := 64) v2)).run s1 = .ok () stOut) :
      (accrue_fflags flags).run s = .ok () stOut := by
    unfold accrue_fflags fflags_dirty_policy
    rw [run_bind_ok _ _ _ _ _ (readReg_run_ok .fcsr fcsrVal s hfcsr)]
    dsimp only [Pure.pure, EStateM.pure, Bind.bind, EStateM.bind]
    change (do
      let __do_lift ← readReg Register.fcsr
      let y_1 ← pure (_get_Fcsr_FFLAGS __do_lift != (_get_Fcsr_FFLAGS fcsrVal ||| flags))
      let __do_lift ← readReg Register.fcsr
      writeReg Register.fcsr (Sail.BitVec.updateSubrange __do_lift 4 0 (_get_Fcsr_FFLAGS fcsrVal ||| flags))
      if y_1 = true then do
        dirty_fd_context_if_present ()
        let v1 ← readReg .fcsr
        csr_name_write_callback "fflags" (zero_extend (m := 64) (_get_Fcsr_FFLAGS v1))
        let v2 ← readReg .fcsr
        csr_name_write_callback "fcsr" (zero_extend (m := 64) v2)
      else do
        pure ()
        let v1 ← readReg .fcsr
        csr_name_write_callback "fflags" (zero_extend (m := 64) (_get_Fcsr_FFLAGS v1))
        let v2 ← readReg .fcsr
        csr_name_write_callback "fcsr" (zero_extend (m := 64) v2)).run s = .ok () stOut
    rw [run_bind_ok _ _ _ _ _ (readReg_run_ok .fcsr fcsrVal s hfcsr)]
    change (do
      let __do_lift ← readReg Register.fcsr
      writeReg Register.fcsr (Sail.BitVec.updateSubrange __do_lift 4 0 (_get_Fcsr_FFLAGS fcsrVal ||| flags))
      if (_get_Fcsr_FFLAGS fcsrVal != (_get_Fcsr_FFLAGS fcsrVal ||| flags)) = true then do
        dirty_fd_context_if_present ()
        let v1 ← readReg .fcsr
        csr_name_write_callback "fflags" (zero_extend (m := 64) (_get_Fcsr_FFLAGS v1))
        let v2 ← readReg .fcsr
        csr_name_write_callback "fcsr" (zero_extend (m := 64) v2)
      else do
        pure ()
        let v1 ← readReg .fcsr
        csr_name_write_callback "fflags" (zero_extend (m := 64) (_get_Fcsr_FFLAGS v1))
        let v2 ← readReg .fcsr
        csr_name_write_callback "fcsr" (zero_extend (m := 64) v2)).run s = .ok () stOut
    rw [run_bind_ok _ _ _ _ _ (readReg_run_ok .fcsr fcsrVal s hfcsr)]
    change (do writeReg Register.fcsr newFcsr; _).run s = .ok () stOut
    rw [run_bind_ok _ _ _ _ _ (writeReg_run_ok .fcsr newFcsr s)]
    exact htail
  cases hchg : (_get_Fcsr_FFLAGS fcsrVal != (_get_Fcsr_FFLAGS fcsrVal ||| flags))
  · refine ⟨s1.regs, hpre s1 ?_, hfcsr1, hms1, fun r hnefcsr _ => regs_get?_insert_ne _ _ _ _ hnefcsr⟩
    rw [hchg, if_neg Bool.false_ne_true]
    dsimp only [Pure.pure, EStateM.pure, Bind.bind, EStateM.bind]
    change (do
      let v1 ← readReg .fcsr
      csr_name_write_callback "fflags" (zero_extend (m := 64) (_get_Fcsr_FFLAGS v1))
      let v2 ← readReg .fcsr
      csr_name_write_callback "fcsr" (zero_extend (m := 64) v2)).run s1 = .ok () s1
    exact hcb s1 hfcsr1
  · obtain ⟨regs', hdirty, hmsOut, hother⟩ := dirty_fd_context_if_present_run s1 mstatusVal hms1
    have hfcsr' : regs'.get? .fcsr = some newFcsr := by rw [hother .fcsr rfl]; exact hfcsr1
    refine ⟨regs', hpre { s with regs := regs' } ?_, hfcsr', hmsOut, fun r hnefcsr hnems => by
      rw [hother r hnems]; exact regs_get?_insert_ne _ _ _ _ hnefcsr⟩
    rw [hchg, if_pos rfl, run_bind_ok _ _ _ _ _ hdirty]; exact hcb { s with regs := regs' } hfcsr'

/-- Theorem 3 (Section 16): `fcsr` field decoding (`FFLAGS`/`FRM`), `write_fcsr`, IEEE-754
    exception flag masks (`NX`/`UF`/`OF`/`DZ`/`NV`), `select_instr_or_fcsr_rm` (static modes,
    dynamic `fcsr.FRM` resolution, and reserved `0b101`/`0b110`/`0b111` illegal-instruction
    rejection), and `accrue_fflags` under `Fflags_Dirty_Precise` (`mstatus.FS` untouched when
    no new flags accrue, marked `Dirty` when new flags accrue). -/
theorem rv64FcsrRoundingAndAccrueFflags_bisim_sail
    (fcsrVal : BitVec 32) (mstatusVal : BitVec 64) (frm : BitVec 3) (flags : BitVec 5)
    (instrRm : rounding_mode)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hfcsr : s.regs.get? .fcsr = some fcsrVal)
    (hmstatus : s.regs.get? .mstatus = some mstatusVal) :
    _get_Fcsr_FFLAGS fcsrVal = Sail.BitVec.extractLsb fcsrVal 4 0 ∧
    _get_Fcsr_FRM fcsrVal = Sail.BitVec.extractLsb fcsrVal 7 5 ∧
    nxFlag () = 0b00001#5 ∧ ufFlag () = 0b00010#5 ∧ ofFlag () = 0b00100#5 ∧
    dzFlag () = 0b01000#5 ∧ nvFlag () = 0b10000#5 ∧
    valid_rounding_mode frm = ((frm != 0b101#3) && (frm != 0b110#3)) ∧
    (select_instr_or_fcsr_rm instrRm).run s = .ok (rv64SelectRmSpec instrRm fcsrVal) s ∧
    (∃ regsW, (write_fcsr frm flags).run s = .ok () { s with regs := regsW } ∧
      regsW.get? .fcsr = some (rv64WriteFcsrSpec fcsrVal frm flags) ∧
      regsW.get? .mstatus = some (rv64DirtyFdMstatusSpec mstatusVal)) ∧
    (∃ regsA, (accrue_fflags flags).run s = .ok () { s with regs := regsA } ∧
      regsA.get? .fcsr = some (rv64AccrueFflagsFcsrSpec fcsrVal flags) ∧
      regsA.get? .mstatus =
        some (if _get_Fcsr_FFLAGS fcsrVal != (_get_Fcsr_FFLAGS fcsrVal ||| flags) then
            rv64DirtyFdMstatusSpec mstatusVal
          else mstatusVal)) ∧
    ((accrue_fflags 0#5).run s =
      .ok () { s with regs := s.regs.insert .fcsr (rv64AccrueFflagsFcsrSpec fcsrVal 0#5) }) := by
  have hsel : (select_instr_or_fcsr_rm instrRm).run s = .ok (rv64SelectRmSpec instrRm fcsrVal) s := by
    cases instrRm with
    | RM_RNE | RM_RTZ | RM_RDN | RM_RUP | RM_RMM =>
      unfold select_instr_or_fcsr_rm rv64SelectRmSpec; rfl
    | RM_DYN =>
      unfold select_instr_or_fcsr_rm rv64SelectRmSpec
      have hdyn : (rounding_mode.RM_DYN == rounding_mode.RM_DYN) = true := rfl
      rw [hdyn, if_pos rfl]
      rw [run_bind_ok _ _ _ _ _ (readReg_run_ok .fcsr fcsrVal s hfcsr)]
      dsimp only [Pure.pure, EStateM.pure, EStateM.run, Bind.bind, EStateM.bind, _get_Fcsr_FRM]
      revert hfcsr
      generalize (Sail.BitVec.extractLsb fcsrVal 7 5 : BitVec 3) = fcsrRm
      intro _
      rcases fcsrRm with ⟨⟨v, hv⟩⟩
      match v with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl
      | n + 8 => omega
  have hwFcsr : ∃ regsW, (write_fcsr frm flags).run s = .ok () { s with regs := regsW } ∧
      regsW.get? .fcsr = some (rv64WriteFcsrSpec fcsrVal frm flags) ∧
      regsW.get? .mstatus = some (rv64DirtyFdMstatusSpec mstatusVal) := by
    let fc1 := Sail.BitVec.updateSubrange fcsrVal 7 5 frm
    let fc2 := Sail.BitVec.updateSubrange fc1 4 0 flags
    let r2 := (s.regs.insert .fcsr fc1).insert .fcsr fc2
    have hms2 : r2.get? .mstatus = some mstatusVal := by
      dsimp only [r2]; rw [regs_get?_insert_ne _ _ _ _ rfl, regs_get?_insert_ne _ _ _ _ rfl]
      exact hmstatus
    obtain ⟨regsW, hdirty, hmsW, hotherW⟩ :=
      dirty_fd_context_if_present_run { s with regs := r2 } mstatusVal hms2
    refine ⟨regsW, ?_, ?_, hmsW⟩
    · unfold write_fcsr
      rw [run_bind_ok _ _ _ _ _ (readReg_run_ok .fcsr fcsrVal s hfcsr)]
      rw [run_bind_ok _ _ _ _ _ (writeReg_run_ok .fcsr fc1 s)]
      have hfc1 : (s.regs.insert .fcsr fc1).get? .fcsr = some fc1 := regs_get?_insert_self _ _ _
      rw [run_bind_ok _ _ _ _ _ (readReg_run_ok .fcsr fc1 _ hfc1)]
      rw [run_bind_ok _ _ _ _ _ (writeReg_run_ok .fcsr fc2 _)]
      exact hdirty
    · rw [hotherW .fcsr rfl]; exact regs_get?_insert_self _ _ _
  obtain ⟨regsA, hacc, hfcA, hmsA, _⟩ := accrue_fflags_run fcsrVal mstatusVal flags s hfcsr hmstatus
  have hacc0 : (accrue_fflags 0#5).run s =
      .ok () { s with regs := s.regs.insert .fcsr (rv64AccrueFflagsFcsrSpec fcsrVal 0#5) } := by
    have h0 : (_get_Fcsr_FFLAGS fcsrVal != (_get_Fcsr_FFLAGS fcsrVal ||| 0#5)) = false := by
      rw [BitVec.or_zero]; exact bne_self_eq_false _
    let s1 := { s with regs := s.regs.insert .fcsr (rv64AccrueFflagsFcsrSpec fcsrVal 0#5) }
    have hfc1 : s1.regs.get? .fcsr = some (rv64AccrueFflagsFcsrSpec fcsrVal 0#5) :=
      regs_get?_insert_self _ _ _
    unfold accrue_fflags fflags_dirty_policy
    rw [run_bind_ok _ _ _ _ _ (readReg_run_ok .fcsr fcsrVal s hfcsr)]
    dsimp only [Pure.pure, EStateM.pure, Bind.bind, EStateM.bind]
    change (do
      let __do_lift ← readReg Register.fcsr
      let y_1 ← pure (_get_Fcsr_FFLAGS __do_lift != (_get_Fcsr_FFLAGS fcsrVal ||| 0#5))
      let __do_lift ← readReg Register.fcsr
      writeReg Register.fcsr (Sail.BitVec.updateSubrange __do_lift 4 0 (_get_Fcsr_FFLAGS fcsrVal ||| 0#5))
      if y_1 = true then do
        dirty_fd_context_if_present ()
        let __do_lift ← readReg Register.fcsr
        csr_name_write_callback "fflags" (zero_extend (m := 64) (_get_Fcsr_FFLAGS __do_lift))
        let __do_lift ← readReg Register.fcsr
        csr_name_write_callback "fcsr" (zero_extend (m := 64) __do_lift)
      else do
        pure ()
        let __do_lift ← readReg Register.fcsr
        csr_name_write_callback "fflags" (zero_extend (m := 64) (_get_Fcsr_FFLAGS __do_lift))
        let __do_lift ← readReg Register.fcsr
        csr_name_write_callback "fcsr" (zero_extend (m := 64) __do_lift)).run s = .ok () s1
    rw [run_bind_ok _ _ _ _ _ (readReg_run_ok .fcsr fcsrVal s hfcsr)]
    change (do
      let __do_lift ← readReg Register.fcsr
      writeReg Register.fcsr (Sail.BitVec.updateSubrange __do_lift 4 0 (_get_Fcsr_FFLAGS fcsrVal ||| 0#5))
      if (_get_Fcsr_FFLAGS fcsrVal != (_get_Fcsr_FFLAGS fcsrVal ||| 0#5)) = true then do
        dirty_fd_context_if_present ()
        let __do_lift ← readReg Register.fcsr
        csr_name_write_callback "fflags" (zero_extend (m := 64) (_get_Fcsr_FFLAGS __do_lift))
        let __do_lift ← readReg Register.fcsr
        csr_name_write_callback "fcsr" (zero_extend (m := 64) __do_lift)
      else do
        pure ()
        let __do_lift ← readReg Register.fcsr
        csr_name_write_callback "fflags" (zero_extend (m := 64) (_get_Fcsr_FFLAGS __do_lift))
        let __do_lift ← readReg Register.fcsr
        csr_name_write_callback "fcsr" (zero_extend (m := 64) __do_lift)).run s = .ok () s1
    rw [run_bind_ok _ _ _ _ _ (readReg_run_ok .fcsr fcsrVal s hfcsr)]
    change (do writeReg Register.fcsr (rv64AccrueFflagsFcsrSpec fcsrVal 0#5); _).run s = .ok () s1
    rw [run_bind_ok _ _ _ _ _ (writeReg_run_ok .fcsr (rv64AccrueFflagsFcsrSpec fcsrVal 0#5) s),
        h0, if_neg Bool.false_ne_true]
    dsimp only [Pure.pure, EStateM.pure, Bind.bind, EStateM.bind]
    change (do
      let v1 ← readReg .fcsr
      csr_name_write_callback "fflags" (zero_extend (m := 64) (_get_Fcsr_FFLAGS v1))
      let v2 ← readReg .fcsr
      csr_name_write_callback "fcsr" (zero_extend (m := 64) v2)).run s1 = .ok () s1
    rw [run_bind_ok _ _ _ _ _ (readReg_run_ok .fcsr _ s1 hfc1),
        run_bind_ok _ _ _ _ _ (csr_name_write_callback_fflags_run _ s1),
        run_bind_ok _ _ _ _ _ (readReg_run_ok .fcsr _ s1 hfc1)]
    exact csr_name_write_callback_fcsr_run _ s1
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hsel, hwFcsr, ⟨regsA, hacc, hfcA, hmsA⟩, hacc0⟩

/-- Pure `TurboLean`-side IEEE-754 single-precision classification (`float_classify` on `BitVec 32`). -/
def rv64FloatClassify32Spec (f : BitVec 32) : float_class :=
  let sign := Sail.BitVec.extractLsb f 31 31
  let exp := Sail.BitVec.extractLsb f 30 23
  let mant := Sail.BitVec.extractLsb f 22 0
  if exp == BitVec.allOnes 8 then
    if mant == 0#23 then
      if sign == 0#1 then .float_class_positive_inf else .float_class_negative_inf
    else if BitVec.access mant 22 == 0#1 then
      .float_class_snan
    else
      .float_class_qnan
  else if exp == 0#8 then
    if mant == 0#23 then
      if sign == 0#1 then .float_class_positive_zero else .float_class_negative_zero
    else
      if sign == 0#1 then .float_class_positive_subnormal else .float_class_negative_subnormal
  else
    if sign == 0#1 then .float_class_positive_normal else .float_class_negative_normal

/-- Pure `TurboLean`-side IEEE-754 double-precision classification (`float_classify` on `BitVec 64`). -/
def rv64FloatClassify64Spec (f : BitVec 64) : float_class :=
  let sign := Sail.BitVec.extractLsb f 63 63
  let exp := Sail.BitVec.extractLsb f 62 52
  let mant := Sail.BitVec.extractLsb f 51 0
  if exp == BitVec.allOnes 11 then
    if mant == 0#52 then
      if sign == 0#1 then .float_class_positive_inf else .float_class_negative_inf
    else if BitVec.access mant 51 == 0#1 then
      .float_class_snan
    else
      .float_class_qnan
  else if exp == 0#11 then
    if mant == 0#52 then
      if sign == 0#1 then .float_class_positive_zero else .float_class_negative_zero
    else
      if sign == 0#1 then .float_class_positive_subnormal else .float_class_negative_subnormal
  else
    if sign == 0#1 then .float_class_positive_normal else .float_class_negative_normal

private theorem bitvec_1_cases (b : BitVec 1) : b = 0#1 ∨ b = 1#1 := by
  rcases b with ⟨⟨v, hv⟩⟩
  match v with
  | 0 => exact .inl rfl
  | 1 => exact .inr rfl
  | n + 2 => omega

private theorem access_msb_eq_extractLsb_32 (f : BitVec 32) :
    BitVec.access f 31 = Sail.BitVec.extractLsb f 31 31 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases Nat.lt_one_iff.mp hi with rfl
  simp [BitVec.access, Sail.BitVec.extractLsb]

private theorem access_msb_eq_extractLsb_64 (f : BitVec 64) :
    BitVec.access f 63 = Sail.BitVec.extractLsb f 63 63 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases Nat.lt_one_iff.mp hi with rfl
  simp [BitVec.access, Sail.BitVec.extractLsb]

private theorem sail_ones_8 : sail_ones 8 = BitVec.allOnes 8 := by decide
private theorem sail_ones_11 : sail_ones 11 = BitVec.allOnes 11 := by decide

private theorem float_is_nan_32_eq (f : BitVec 32) :
    float_is_nan f =
      ((Sail.BitVec.extractLsb f 30 23 == BitVec.allOnes 8) &&
       !(Sail.BitVec.extractLsb f 22 0 == 0#23)) := by
  change ((Sail.BitVec.extractLsb f 30 23 == sail_ones 8) &&
    !(Sail.BitVec.extractLsb f 22 0 == 0#23)) = _
  rw [sail_ones_8]

private theorem float_is_snan_32_eq (f : BitVec 32) :
    float_is_snan f =
      ((Sail.BitVec.extractLsb f 30 23 == BitVec.allOnes 8) &&
       !(Sail.BitVec.extractLsb f 22 0 == 0#23) &&
       (BitVec.access (Sail.BitVec.extractLsb f 22 0) 22 == 0#1)) := by
  unfold float_is_snan
  rw [float_is_nan_32_eq]
  rfl

private theorem float_is_qnan_32_eq (f : BitVec 32) :
    float_is_qnan f =
      ((Sail.BitVec.extractLsb f 30 23 == BitVec.allOnes 8) &&
       !(Sail.BitVec.extractLsb f 22 0 == 0#23) &&
       (BitVec.access (Sail.BitVec.extractLsb f 22 0) 22 == 1#1)) := by
  unfold float_is_qnan
  rw [float_is_nan_32_eq]
  rfl

private theorem float_is_zero_32_eq (f : BitVec 32) :
    float_is_zero f =
      ((Sail.BitVec.extractLsb f 30 23 == 0#8) &&
       (Sail.BitVec.extractLsb f 22 0 == 0#23)) := rfl

private theorem float_is_subnormal_32_eq (f : BitVec 32) :
    float_is_subnormal f =
      ((Sail.BitVec.extractLsb f 30 23 == 0#8) &&
       !(Sail.BitVec.extractLsb f 22 0 == 0#23)) := rfl

private theorem float_is_normal_32_eq (f : BitVec 32) :
    float_is_normal f =
      (!(Sail.BitVec.extractLsb f 30 23 == BitVec.allOnes 8) &&
       !(Sail.BitVec.extractLsb f 30 23 == 0#8)) := by
  change (!(Sail.BitVec.extractLsb f 30 23 == sail_ones 8) &&
    !(Sail.BitVec.extractLsb f 30 23 == 0#8)) = _
  rw [sail_ones_8]

private theorem float_is_inf_32_eq (f : BitVec 32) :
    float_is_inf f =
      ((Sail.BitVec.extractLsb f 30 23 == BitVec.allOnes 8) &&
       (Sail.BitVec.extractLsb f 22 0 == 0#23)) := by
  change ((Sail.BitVec.extractLsb f 30 23 == sail_ones 8) &&
    (Sail.BitVec.extractLsb f 22 0 == 0#23)) = _
  rw [sail_ones_8]

private theorem float_is_positive_32_eq (f : BitVec 32) :
    float_is_positive f = (Sail.BitVec.extractLsb f 31 31 == 0#1) := by
  unfold float_is_positive is_highest_zero
  change (BitVec.access f 31 == 0#1) = (Sail.BitVec.extractLsb f 31 31 == 0#1)
  rw [access_msb_eq_extractLsb_32 f]

private theorem float_classify_32_run (f : BitVec 32)
    (s : SequentialState RegisterType trivialChoiceSource) :
    (float_classify f).run s = .ok (rv64FloatClassify32Spec f) s := by
  unfold float_classify rv64FloatClassify32Spec
  dsimp only []
  rw [float_is_snan_32_eq, float_is_qnan_32_eq, float_is_zero_32_eq,
      float_is_subnormal_32_eq, float_is_normal_32_eq, float_is_inf_32_eq,
      float_is_positive_32_eq]
  generalize Sail.BitVec.extractLsb f 31 31 = sign
  generalize Sail.BitVec.extractLsb f 30 23 = exp
  generalize Sail.BitVec.extractLsb f 22 0 = mant
  generalize BitVec.access mant 22 = m22
  rcases bitvec_1_cases sign with rfl | rfl <;>
    rcases bitvec_1_cases m22 with rfl | rfl
  all_goals
    by_cases he1 : (exp == BitVec.allOnes 8) = true
    · have he0 : (exp == 0#8) = false := by
        rw [beq_iff_eq] at he1; subst he1; decide
      rw [he1, he0]
      cases hm0 : (mant == 0#23) <;> rfl
    · simp only [Bool.not_eq_true] at he1
      rw [he1]
      cases he0 : (exp == 0#8) <;> cases hm0 : (mant == 0#23) <;> rfl

private theorem float_is_nan_64_eq (f : BitVec 64) :
    float_is_nan f =
      ((Sail.BitVec.extractLsb f 62 52 == BitVec.allOnes 11) &&
       !(Sail.BitVec.extractLsb f 51 0 == 0#52)) := by
  change ((Sail.BitVec.extractLsb f 62 52 == sail_ones 11) &&
    !(Sail.BitVec.extractLsb f 51 0 == 0#52)) = _
  rw [sail_ones_11]

private theorem float_is_snan_64_eq (f : BitVec 64) :
    float_is_snan f =
      ((Sail.BitVec.extractLsb f 62 52 == BitVec.allOnes 11) &&
       !(Sail.BitVec.extractLsb f 51 0 == 0#52) &&
       (BitVec.access (Sail.BitVec.extractLsb f 51 0) 51 == 0#1)) := by
  unfold float_is_snan
  rw [float_is_nan_64_eq]
  rfl

private theorem float_is_qnan_64_eq (f : BitVec 64) :
    float_is_qnan f =
      ((Sail.BitVec.extractLsb f 62 52 == BitVec.allOnes 11) &&
       !(Sail.BitVec.extractLsb f 51 0 == 0#52) &&
       (BitVec.access (Sail.BitVec.extractLsb f 51 0) 51 == 1#1)) := by
  unfold float_is_qnan
  rw [float_is_nan_64_eq]
  rfl

private theorem float_is_zero_64_eq (f : BitVec 64) :
    float_is_zero f =
      ((Sail.BitVec.extractLsb f 62 52 == 0#11) &&
       (Sail.BitVec.extractLsb f 51 0 == 0#52)) := rfl

private theorem float_is_subnormal_64_eq (f : BitVec 64) :
    float_is_subnormal f =
      ((Sail.BitVec.extractLsb f 62 52 == 0#11) &&
       !(Sail.BitVec.extractLsb f 51 0 == 0#52)) := rfl

private theorem float_is_normal_64_eq (f : BitVec 64) :
    float_is_normal f =
      (!(Sail.BitVec.extractLsb f 62 52 == BitVec.allOnes 11) &&
       !(Sail.BitVec.extractLsb f 62 52 == 0#11)) := by
  change (!(Sail.BitVec.extractLsb f 62 52 == sail_ones 11) &&
    !(Sail.BitVec.extractLsb f 62 52 == 0#11)) = _
  rw [sail_ones_11]

private theorem float_is_inf_64_eq (f : BitVec 64) :
    float_is_inf f =
      ((Sail.BitVec.extractLsb f 62 52 == BitVec.allOnes 11) &&
       (Sail.BitVec.extractLsb f 51 0 == 0#52)) := by
  change ((Sail.BitVec.extractLsb f 62 52 == sail_ones 11) &&
    (Sail.BitVec.extractLsb f 51 0 == 0#52)) = _
  rw [sail_ones_11]

private theorem float_is_positive_64_eq (f : BitVec 64) :
    float_is_positive f = (Sail.BitVec.extractLsb f 63 63 == 0#1) := by
  unfold float_is_positive is_highest_zero
  change (BitVec.access f 63 == 0#1) = (Sail.BitVec.extractLsb f 63 63 == 0#1)
  rw [access_msb_eq_extractLsb_64 f]

private theorem float_classify_64_run (f : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource) :
    (float_classify f).run s = .ok (rv64FloatClassify64Spec f) s := by
  unfold float_classify rv64FloatClassify64Spec
  dsimp only []
  rw [float_is_snan_64_eq, float_is_qnan_64_eq, float_is_zero_64_eq,
      float_is_subnormal_64_eq, float_is_normal_64_eq, float_is_inf_64_eq,
      float_is_positive_64_eq]
  generalize Sail.BitVec.extractLsb f 63 63 = sign
  generalize Sail.BitVec.extractLsb f 62 52 = exp
  generalize Sail.BitVec.extractLsb f 51 0 = mant
  generalize BitVec.access mant 51 = m51
  rcases bitvec_1_cases sign with rfl | rfl <;>
    rcases bitvec_1_cases m51 with rfl | rfl
  all_goals
    by_cases he1 : (exp == BitVec.allOnes 11) = true
    · have he0 : (exp == 0#11) = false := by
        rw [beq_iff_eq] at he1; subst he1; decide
      rw [he1, he0]
      cases hm0 : (mant == 0#52) <;> rfl
    · simp only [Bool.not_eq_true] at he1
      rw [he1]
      cases he0 : (exp == 0#11) <;> cases hm0 : (mant == 0#52) <;> rfl

private theorem fsplit_S_fmake_S (s : BitVec 1) (e : BitVec 8) (m : BitVec 23) :
    fsplit_S (fmake_S s e m) = (s, e, m) := by
  unfold fsplit_S fmake_S
  have ha : BitVec.extractLsb' 0 (8 + 23) (s ++ (e ++ m)) = e ++ m := BitVec.extractLsb'_append_eq_right
  have h1 : Sail.BitVec.extractLsb (s ++ (e ++ m)) 31 31 = s := by
    change BitVec.extractLsb' (8 + 23) 1 (s ++ (e ++ m)) = s; exact BitVec.extractLsb'_append_eq_left
  have h2 : Sail.BitVec.extractLsb (s ++ (e ++ m)) 30 23 = e := by
    have hb : BitVec.extractLsb' 23 8 (BitVec.extractLsb' 0 31 (s ++ (e ++ m))) =
        Sail.BitVec.extractLsb (s ++ (e ++ m)) 30 23 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [Sail.BitVec.extractLsb, BitVec.extractLsb, hi]
    rw [← hb, ha]; exact BitVec.extractLsb'_append_eq_left
  have h3 : Sail.BitVec.extractLsb (s ++ (e ++ m)) 22 0 = m := by
    have hb : BitVec.extractLsb' 0 23 (BitVec.extractLsb' 0 31 (s ++ (e ++ m))) =
        Sail.BitVec.extractLsb (s ++ (e ++ m)) 22 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [Sail.BitVec.extractLsb, BitVec.extractLsb, hi]
    rw [← hb, ha]; exact BitVec.extractLsb'_append_eq_right
  exact Prod.ext h1 (Prod.ext h2 h3)

private theorem fsplit_D_fmake_D (s : BitVec 1) (e : BitVec 11) (m : BitVec 52) :
    fsplit_D (fmake_D s e m) = (s, e, m) := by
  unfold fsplit_D fmake_D
  have ha : BitVec.extractLsb' 0 (11 + 52) (s ++ (e ++ m)) = e ++ m := BitVec.extractLsb'_append_eq_right
  have h1 : Sail.BitVec.extractLsb (s ++ (e ++ m)) 63 63 = s := by
    change BitVec.extractLsb' (11 + 52) 1 (s ++ (e ++ m)) = s; exact BitVec.extractLsb'_append_eq_left
  have h2 : Sail.BitVec.extractLsb (s ++ (e ++ m)) 62 52 = e := by
    have hb : BitVec.extractLsb' 52 11 (BitVec.extractLsb' 0 63 (s ++ (e ++ m))) =
        Sail.BitVec.extractLsb (s ++ (e ++ m)) 62 52 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [Sail.BitVec.extractLsb, BitVec.extractLsb, hi]
    rw [← hb, ha]; exact BitVec.extractLsb'_append_eq_left
  have h3 : Sail.BitVec.extractLsb (s ++ (e ++ m)) 51 0 = m := by
    have hb : BitVec.extractLsb' 0 52 (BitVec.extractLsb' 0 63 (s ++ (e ++ m))) =
        Sail.BitVec.extractLsb (s ++ (e ++ m)) 51 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [Sail.BitVec.extractLsb, BitVec.extractLsb, hi]
    rw [← hb, ha]; exact BitVec.extractLsb'_append_eq_right
  exact Prod.ext h1 (Prod.ext h2 h3)

private theorem fmake_D_fsplit_D (x : BitVec 64) :
    (let (s, e, m) := fsplit_D x; fmake_D s e m) = x := by
  unfold fsplit_D fmake_D; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, Nat.sub_zero,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h52 : i < 52
  · simp [h52, show ¬ (63 ≤ i) by omega]
  · by_cases h63 : i - 52 < 11
    · simp [h52, h63, show 52 + (i - 52) = i by omega, show ¬ (63 ≤ i) by omega]
    · obtain rfl : i = 63 := by omega
      simp

private theorem fmake_S_fsplit_S (x : BitVec 32) :
    (let (s, e, m) := fsplit_S x; fmake_S s e m) = x := by
  unfold fsplit_S fmake_S; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, Nat.sub_zero,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h23 : i < 23
  · simp [h23, show ¬ (31 ≤ i) by omega]
  · by_cases h31 : i - 23 < 8
    · simp [h23, h31, show 23 + (i - 23) = i by omega, show ¬ (31 ≤ i) by omega]
    · obtain rfl : i = 31 := by omega
      simp

/-- Theorem 4 (Section 16): IEEE-754 single-precision (`FextInsts.lean`) and double-precision
    (`DextInsts.lean`) split/compose/negate helpers, NaN/zero predicates, and quiet/signaling
    ordered comparisons (`feq_quiet_S`/`D`, `flt_S`/`D`, `fle_S`/`D`), including `-0.0 == +0.0`,
    signed magnitude ordering, `QNaN` quiet suppression vs signaling `nvFlag = 0b10000#5`, and
    `SNaN` invalid-operation flag raising. -/
theorem rv64FpSplitPredicatesAndCompare_bisim_sail
    (s32 : BitVec 1) (e32 : BitVec 8) (m32 : BitVec 23) (x32 : BitVec 32)
    (s64 : BitVec 1) (e64 : BitVec 11) (m64 : BitVec 52) (x64 : BitVec 64) :
    fsplit_S (fmake_S s32 e32 m32) = (s32, e32, m32) ∧
    (let (s, e, m) := fsplit_S x32; fmake_S s e m = x32) ∧
    negate_S (negate_S x32) = x32 ∧
    fsplit_D (fmake_D s64 e64 m64) = (s64, e64, m64) ∧
    (let (s, e, m) := fsplit_D x64; fmake_D s e m = x64) ∧
    negate_D (negate_D x64) = x64 ∧
    feq_quiet_S 0x80000000#32 0x00000000#32 = (true, 0#5) ∧
    feq_quiet_S (canonical_NaN_S ()) 0x3f800000#32 = (false, 0#5) ∧
    feq_quiet_S 0x7f800001#32 0x3f800000#32 = (false, 0b10000#5) ∧
    flt_S 0xbf800000#32 0x3f800000#32 false = (true, 0#5) ∧
    flt_S 0x80000000#32 0x00000000#32 false = (true, 0#5) ∧
    fle_S 0x00000000#32 0x80000000#32 true = (true, 0#5) ∧
    fle_S (canonical_NaN_S ()) 0x3f800000#32 true = (false, 0#5) ∧
    fle_S (canonical_NaN_S ()) 0x3f800000#32 false = (false, 0b10000#5) ∧
    fle_S 0x7f800001#32 0x3f800000#32 true = (false, 0b10000#5) ∧
    feq_quiet_D 0x8000000000000000#64 0x0000000000000000#64 = (true, 0#5) ∧
    feq_quiet_D (canonical_NaN_D ()) 0x3ff0000000000000#64 = (false, 0#5) ∧
    feq_quiet_D 0x7ff0000000000001#64 0x3ff0000000000000#64 = (false, 0b10000#5) ∧
    flt_D 0xbff0000000000000#64 0x3ff0000000000000#64 false = (true, 0#5) ∧
    fle_D 0x0000000000000000#64 0x8000000000000000#64 true = (true, 0#5) ∧
    fle_D (canonical_NaN_D ()) 0x3ff0000000000000#64 true = (false, 0#5) ∧
    fle_D (canonical_NaN_D ()) 0x3ff0000000000000#64 false = (false, 0b10000#5) ∧
    fle_D 0x7ff0000000000001#64 0x3ff0000000000000#64 true = (false, 0b10000#5) := by
  have hneg32 : negate_S (negate_S x32) = x32 := by
    unfold negate_S
    have hmk := fmake_S_fsplit_S x32
    rcases hsp : fsplit_S x32 with ⟨sx, ex, mx⟩
    rw [hsp] at hmk
    rw [fsplit_S_fmake_S]
    rcases bitvec_1_cases sx with rfl | rfl <;> exact hmk
  have hneg64 : negate_D (negate_D x64) = x64 := by
    unfold negate_D
    have hmk := fmake_D_fsplit_D x64
    rcases hsp : fsplit_D x64 with ⟨sx, ex, mx⟩
    rw [hsp] at hmk
    rw [fsplit_D_fmake_D]
    rcases bitvec_1_cases sx with rfl | rfl <;> exact hmk
  refine ⟨fsplit_S_fmake_S s32 e32 m32, fmake_S_fsplit_S x32, hneg32,
    fsplit_D_fmake_D s64 e64 m64, fmake_D_fsplit_D x64, hneg64, ?_⟩
  decide

/-- Theorem 5 (Section 16): Universal 32-bit and 64-bit `float_classify` (`Classify.lean`)
    bisimulation against `rv64FloatClassify32Spec` / `rv64FloatClassify64Spec` (never taking the
    unreachable `Error.Exit` branch), plus all 10 IEEE-754 class witnesses and 10-bit one-hot mask
    encodings (`float_class_onehot_bits_forwards`, `FloatClassify.lean`) for `FCLASS.S`/`FCLASS.D`. -/
theorem rv64FloatClassifyAndOnehot_bisim_sail
    (f32 : BitVec 32) (f64 : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource) :
    (float_classify f32).run s = .ok (rv64FloatClassify32Spec f32) s ∧
    (float_classify f64).run s = .ok (rv64FloatClassify64Spec f64) s ∧
    float_class_onehot_bits_forwards (rv64FloatClassify32Spec 0xff800000#32) = 0b0000000001#10 ∧
    float_class_onehot_bits_forwards (rv64FloatClassify32Spec 0xbf800000#32) = 0b0000000010#10 ∧
    float_class_onehot_bits_forwards (rv64FloatClassify32Spec 0x80000001#32) = 0b0000000100#10 ∧
    float_class_onehot_bits_forwards (rv64FloatClassify32Spec 0x80000000#32) = 0b0000001000#10 ∧
    float_class_onehot_bits_forwards (rv64FloatClassify32Spec 0x00000000#32) = 0b0000010000#10 ∧
    float_class_onehot_bits_forwards (rv64FloatClassify32Spec 0x00000001#32) = 0b0000100000#10 ∧
    float_class_onehot_bits_forwards (rv64FloatClassify32Spec 0x3f800000#32) = 0b0001000000#10 ∧
    float_class_onehot_bits_forwards (rv64FloatClassify32Spec 0x7f800000#32) = 0b0010000000#10 ∧
    float_class_onehot_bits_forwards (rv64FloatClassify32Spec 0x7f800001#32) = 0b0100000000#10 ∧
    float_class_onehot_bits_forwards (rv64FloatClassify32Spec 0x7fc00000#32) = 0b1000000000#10 ∧
    float_class_onehot_bits_forwards (rv64FloatClassify64Spec 0xfff0000000000000#64) = 0b0000000001#10 ∧
    float_class_onehot_bits_forwards (rv64FloatClassify64Spec 0xbff0000000000000#64) = 0b0000000010#10 ∧
    float_class_onehot_bits_forwards (rv64FloatClassify64Spec 0x8000000000000001#64) = 0b0000000100#10 ∧
    float_class_onehot_bits_forwards (rv64FloatClassify64Spec 0x8000000000000000#64) = 0b0000001000#10 ∧
    float_class_onehot_bits_forwards (rv64FloatClassify64Spec 0x0000000000000000#64) = 0b0000010000#10 ∧
    float_class_onehot_bits_forwards (rv64FloatClassify64Spec 0x0000000000000001#64) = 0b0000100000#10 ∧
    float_class_onehot_bits_forwards (rv64FloatClassify64Spec 0x3ff0000000000000#64) = 0b0001000000#10 ∧
    float_class_onehot_bits_forwards (rv64FloatClassify64Spec 0x7ff0000000000000#64) = 0b0010000000#10 ∧
    float_class_onehot_bits_forwards (rv64FloatClassify64Spec 0x7ff0000000000001#64) = 0b0100000000#10 ∧
    float_class_onehot_bits_forwards (rv64FloatClassify64Spec 0x7ff8000000000000#64) = 0b1000000000#10 := by
  refine ⟨float_classify_32_run f32 s, float_classify_64_run f64 s, ?_⟩
  decide

/-! ### Theorems 6–8: RV64F/D Compressed Expanders, Flat-RAM Load/Store, Move/Classify, and Sign-Inject/Min/Max -/


/-- Exact upstream Sail `execute_C_FSWSP` (`InstsEnd.lean`, lines 71630–71632). -/
def sailExecuteCFswsp (uimm : BitVec 6) (rs2 : fregidx) : ExecutionResult :=
  let imm : BitVec 12 := zero_extend (m := 12) (uimm +++ 0b00#2)
  .ExecuteAs (.STORE_FP (imm, rs2, sp, 4))

/-- Exact upstream Sail `execute_C_FSW` (`InstsEnd.lean`, lines 71634–71638). -/
def sailExecuteCFsw (uimm : BitVec 5) (rsc1 : cregidx) (rsc2 : cfregidx) : ExecutionResult :=
  let imm : BitVec 12 := zero_extend (m := 12) (uimm +++ 0b00#2)
  let rs1 := creg2reg_idx rsc1
  let rs2 := cfregidx_to_fregidx rsc2
  .ExecuteAs (.STORE_FP (imm, rs2, rs1, 4))

/-- Exact upstream Sail `execute_C_FSDSP` (`InstsEnd.lean`, lines 71640–71642). -/
def sailExecuteCFsdsp (uimm : BitVec 6) (rs2 : fregidx) : ExecutionResult :=
  let imm : BitVec 12 := zero_extend (m := 12) (uimm +++ 0b000#3)
  .ExecuteAs (.STORE_FP (imm, rs2, sp, 8))

/-- Exact upstream Sail `execute_C_FSD` (`InstsEnd.lean`, lines 71644–71648). -/
def sailExecuteCFsd (uimm : BitVec 5) (rsc1 : cregidx) (rsc2 : cfregidx) : ExecutionResult :=
  let imm : BitVec 12 := zero_extend (m := 12) (uimm +++ 0b000#3)
  let rs1 := creg2reg_idx rsc1
  let rs2 := cfregidx_to_fregidx rsc2
  .ExecuteAs (.STORE_FP (imm, rs2, rs1, 8))

/-- Exact upstream Sail `execute_C_FLWSP` (`InstsEnd.lean`, lines 71650–71652). -/
def sailExecuteCFlwsp (imm : BitVec 6) (rd : fregidx) : ExecutionResult :=
  let imm : BitVec 12 := zero_extend (m := 12) (imm +++ 0b00#2)
  .ExecuteAs (.LOAD_FP (imm, sp, rd, 4))

/-- Exact upstream Sail `execute_C_FLW` (`InstsEnd.lean`, lines 71654–71658). -/
def sailExecuteCFlw (uimm : BitVec 5) (rsc : cregidx) (rdc : cfregidx) : ExecutionResult :=
  let imm : BitVec 12 := zero_extend (m := 12) (uimm +++ 0b00#2)
  let rd := cfregidx_to_fregidx rdc
  let rs := creg2reg_idx rsc
  .ExecuteAs (.LOAD_FP (imm, rs, rd, 4))

/-- Exact upstream Sail `execute_C_FLDSP` (`InstsEnd.lean`, lines 71660–71662). -/
def sailExecuteCFldsp (uimm : BitVec 6) (rd : fregidx) : ExecutionResult :=
  let imm : BitVec 12 := zero_extend (m := 12) (uimm +++ 0b000#3)
  .ExecuteAs (.LOAD_FP (imm, sp, rd, 8))

/-- Exact upstream Sail `execute_C_FLD` (`InstsEnd.lean`, lines 71664–71668). -/
def sailExecuteCFld (uimm : BitVec 5) (rsc : cregidx) (rdc : cfregidx) : ExecutionResult :=
  let imm : BitVec 12 := zero_extend (m := 12) (uimm +++ 0b000#3)
  let rd := cfregidx_to_fregidx rdc
  let rs := creg2reg_idx rsc
  .ExecuteAs (.LOAD_FP (imm, rs, rd, 8))

/-- Exact upstream Sail `execute_STORE_FP` data-slicing core (`InstsEnd.lean`, line 67343):
    `Sail.BitVec.extractLsb fval ((width *i 8) -i 1) 0`. -/
def sailStoreFpDataCore (width : Nat) (hw : 0 < width) (fval : flenbits) : BitVec (8 * width) :=
  have hlen : (((Int.ofNat width *i 8) -i 1) -i 0 +i 1).toNat = 8 * width := by
    change (((width : Int) * 8 - 1) - 0 + 1).toNat = 8 * width
    omega
  hlen ▸ Sail.BitVec.extractLsb fval ((Int.ofNat width *i 8) -i 1) 0

/-- Exact upstream Sail `execute_LOAD_FP` (`InstsEnd.lean`, lines 69216–69224) over flat physical
    RAM (`ext_data_get_addr` → `read_ram Read_plain` → `nan_box (8 *i 8)` → `wF_bits`). -/
noncomputable def sailLoadFpRamExec (imm : BitVec 12) (rs1 : regidx) (rd : fregidx) (width : Nat)
    (_hwle : width ≤ 8) : SailM ExecutionResult := do
  PreSail.assert (width ≤b Functions.flen_bytes) "extensions/FD/fext_insts.sail:282.28-282.29"
  let offset : xlenbits := sign_extend (m := 64) imm
  match (← ext_data_get_addr rs1 offset (.Load .Data) width) with
  | .Ext_DataAddr_OK (.Virtaddr vaddr) =>
    let (result, _) ← LeanRV64D.Functions.read_ram .Read_plain (.Physaddr vaddr) width false
    wF_bits rd (BitVec.setWidth (if (true : Bool) then 8 else 4 * 8) (nan_box (n := (8 *i 8)) result))
    pure (.Retire_Success ())
  | .Ext_DataAddr_Error e => pure (.Ext_DataAddr_Check_Failure e)

/-- Exact upstream Sail `execute_STORE_FP` (`InstsEnd.lean`, lines 67340–67348) over flat physical
    RAM (`rF_bits` → `extractLsb` → `ext_data_get_addr` → `write_ram Write_plain`). -/
noncomputable def sailStoreFpRamExec (imm : BitVec 12) (rs2 : fregidx) (rs1 : regidx) (width : Nat)
    (hw : 0 < width) : SailM ExecutionResult := do
  PreSail.assert (width ≤b Functions.flen_bytes) "extensions/FD/fext_insts.sail:318.28-318.29"
  let offset : xlenbits := sign_extend (m := 64) imm
  let data : BitVec (8 * width) := sailStoreFpDataCore width hw (← rF_bits rs2)
  match (← ext_data_get_addr rs1 offset (.Store .Data) width) with
  | .Ext_DataAddr_OK (.Virtaddr vaddr) =>
    let ok ← LeanRV64D.Functions.write_ram .Write_plain (.Physaddr vaddr) width data ()
    if ok then pure (.Retire_Success ())
    else internal_error "extensions/FD/fext_insts.sail" 324 "store got false from vmem_write"
  | .Ext_DataAddr_Error e => pure (.Ext_DataAddr_Check_Failure e)

private theorem sailStoreFpDataCore_eq_setWidth_4 (fval : flenbits) :
    sailStoreFpDataCore 4 (by decide) fval = BitVec.setWidth 32 fval := by
  unfold sailStoreFpDataCore Sail.BitVec.extractLsb
  dsimp only []
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp [BitVec.extractLsb]

private theorem sailStoreFpDataCore_eq_setWidth_8 (fval : flenbits) :
    sailStoreFpDataCore 8 (by decide) fval = BitVec.setWidth 64 fval := by
  unfold sailStoreFpDataCore Sail.BitVec.extractLsb
  dsimp only []
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp [BitVec.extractLsb]

/-- Theorem 6 (Section 16): RVC floating-point load/store compressed expanders (`C.FLW`, `C.FLWSP`,
    `C.FLD`, `C.FLDSP`, `C.FSW`, `C.FSWSP`, `C.FSD`, `C.FSDSP`) and end-to-end `SailM` flat-RAM
    execution of `FLW`/`FLD` (`execute_LOAD_FP`) and `FSW`/`FSD` (`execute_STORE_FP`), including
    `nan_box` followed by upstream `flenbits` (`BitVec 8`) `.f0` update, `dirty_fd_context`, and
    little-endian byte memory transitions. -/
theorem rv64FpLoadStoreAndRvcExec_bisim_sail
    (uimm6 : BitVec 6) (uimm5 : BitVec 5) (rsc : BitVec 3) (fsc : BitVec 3)
    (rdF : fregidx) (imm12 : BitVec 12)
    (spVal mstatusVal : BitVec 64) (f0Val : flenbits)
    (bytes4 : BitVec 32) (bytes8 : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hsp : s.regs.get? .x2 = some spVal)
    (hf0 : s.regs.get? .f0 = some f0Val)
    (hmstatus : s.regs.get? .mstatus = some mstatusVal)
    (hmem4 : rv64ReadMemBytesSpec 4 (BitVec.toNat (rv64iEffectiveAddrSpec spVal imm12)) s.mem = some bytes4)
    (hmem8 : rv64ReadMemBytesSpec 8 (BitVec.toNat (rv64iEffectiveAddrSpec spVal imm12)) s.mem = some bytes8) :
    sailExecuteCFswsp uimm6 rdF =
      .ExecuteAs (.STORE_FP (BitVec.zeroExtend 12 (uimm6 ++ 0b00#2), rdF, sp, 4)) ∧
    sailExecuteCFsw uimm5 (.Cregidx rsc) (.Cfregidx fsc) =
      .ExecuteAs (.STORE_FP (BitVec.zeroExtend 12 (uimm5 ++ 0b00#2), .Fregidx (0b01#2 ++ fsc), .Regidx (0b01#2 ++ rsc), 4)) ∧
    sailExecuteCFsdsp uimm6 rdF =
      .ExecuteAs (.STORE_FP (BitVec.zeroExtend 12 (uimm6 ++ 0b000#3), rdF, sp, 8)) ∧
    sailExecuteCFsd uimm5 (.Cregidx rsc) (.Cfregidx fsc) =
      .ExecuteAs (.STORE_FP (BitVec.zeroExtend 12 (uimm5 ++ 0b000#3), .Fregidx (0b01#2 ++ fsc), .Regidx (0b01#2 ++ rsc), 8)) ∧
    sailExecuteCFlwsp uimm6 rdF =
      .ExecuteAs (.LOAD_FP (BitVec.zeroExtend 12 (uimm6 ++ 0b00#2), sp, rdF, 4)) ∧
    sailExecuteCFlw uimm5 (.Cregidx rsc) (.Cfregidx fsc) =
      .ExecuteAs (.LOAD_FP (BitVec.zeroExtend 12 (uimm5 ++ 0b00#2), .Regidx (0b01#2 ++ rsc), .Fregidx (0b01#2 ++ fsc), 4)) ∧
    sailExecuteCFldsp uimm6 rdF =
      .ExecuteAs (.LOAD_FP (BitVec.zeroExtend 12 (uimm6 ++ 0b000#3), sp, rdF, 8)) ∧
    sailExecuteCFld uimm5 (.Cregidx rsc) (.Cfregidx fsc) =
      .ExecuteAs (.LOAD_FP (BitVec.zeroExtend 12 (uimm5 ++ 0b000#3), .Regidx (0b01#2 ++ rsc), .Fregidx (0b01#2 ++ fsc), 8)) ∧
    (sailStoreFpRamExec imm12 (.Fregidx 0#5) sp 4 (by decide)).run s =
      .ok (.Retire_Success ()) ({ s with mem := rv64WriteMemBytesSpec 4 (BitVec.toNat (rv64iEffectiveAddrSpec spVal imm12)) (BitVec.setWidth 32 f0Val) s.mem }) ∧
    (sailStoreFpRamExec imm12 (.Fregidx 0#5) sp 8 (by decide)).run s =
      .ok (.Retire_Success ()) ({ s with mem := rv64WriteMemBytesSpec 8 (BitVec.toNat (rv64iEffectiveAddrSpec spVal imm12)) (BitVec.setWidth 64 f0Val) s.mem }) ∧
    (∃ regs4,
      (sailLoadFpRamExec imm12 sp (.Fregidx 0#5) 4 (by decide)).run s =
        .ok (.Retire_Success ()) ({ s with regs := regs4 }) ∧
      regs4.get? .f0 = some (BitVec.setWidth 8 bytes4 : flenbits) ∧
      regs4.get? .mstatus = some (rv64DirtyFdMstatusSpec mstatusVal) ∧
      (∀ r, (Register.f0 == r) = false → (Register.mstatus == r) = false →
        regs4.get? r = s.regs.get? r)) ∧
    (∃ regs8,
      (sailLoadFpRamExec imm12 sp (.Fregidx 0#5) 8 (by decide)).run s =
        .ok (.Retire_Success ()) ({ s with regs := regs8 }) ∧
      regs8.get? .f0 = some (BitVec.setWidth 8 bytes8 : flenbits) ∧
      regs8.get? .mstatus = some (rv64DirtyFdMstatusSpec mstatusVal) ∧
      (∀ r, (Register.f0 == r) = false → (Register.mstatus == r) = false →
        regs8.get? r = s.regs.get? r)) := by
  have hst4 : (sailStoreFpRamExec imm12 (.Fregidx 0#5) sp 4 (by decide)).run s =
      .ok (.Retire_Success ()) ({ s with mem := rv64WriteMemBytesSpec 4 (BitVec.toNat (rv64iEffectiveAddrSpec spVal imm12)) (BitVec.setWidth 32 f0Val) s.mem }) := by
    unfold sailStoreFpRamExec
    have ha : (PreSail.assert (4 ≤b Functions.flen_bytes)
        "extensions/FD/fext_insts.sail:318.28-318.29" : SailM Unit).run s = .ok () s := rfl
    rw [run_bind_ok _ _ _ _ _ ha]
    rw [run_bind_ok _ _ _ _ _ (rF_bits_f0_run f0Val s hf0)]
    rw [run_bind_ok _ _ _ _ _ (rv64iEffectiveAddr_ext_data_get_addr_bisim spVal imm12 (.Store .Data) 4 s hsp)]
    dsimp only []
    rw [sailStoreFpDataCore_eq_setWidth_4]
    rw [run_bind_ok _ _ _ _ _ (write_ram_plain_bisim_sail 4 (rv64iEffectiveAddrSpec spVal imm12) (BitVec.setWidth 32 f0Val) s)]
    rfl
  have hst8 : (sailStoreFpRamExec imm12 (.Fregidx 0#5) sp 8 (by decide)).run s =
      .ok (.Retire_Success ()) ({ s with mem := rv64WriteMemBytesSpec 8 (BitVec.toNat (rv64iEffectiveAddrSpec spVal imm12)) (BitVec.setWidth 64 f0Val) s.mem }) := by
    unfold sailStoreFpRamExec
    have ha : (PreSail.assert (8 ≤b Functions.flen_bytes)
        "extensions/FD/fext_insts.sail:318.28-318.29" : SailM Unit).run s = .ok () s := rfl
    rw [run_bind_ok _ _ _ _ _ ha]
    rw [run_bind_ok _ _ _ _ _ (rF_bits_f0_run f0Val s hf0)]
    rw [run_bind_ok _ _ _ _ _ (rv64iEffectiveAddr_ext_data_get_addr_bisim spVal imm12 (.Store .Data) 8 s hsp)]
    dsimp only []
    rw [sailStoreFpDataCore_eq_setWidth_8]
    rw [run_bind_ok _ _ _ _ _ (write_ram_plain_bisim_sail 8 (rv64iEffectiveAddrSpec spVal imm12) (BitVec.setWidth 64 f0Val) s)]
    rfl
  obtain ⟨regs4, hw4, hf04, hms4, hoth4⟩ :=
    wF_bits_f0_run (BitVec.setWidth 8 bytes4) mstatusVal s hmstatus
  have hld4 : (sailLoadFpRamExec imm12 sp (.Fregidx 0#5) 4 (by decide)).run s =
      .ok (.Retire_Success ()) ({ s with regs := regs4 }) := by
    unfold sailLoadFpRamExec
    have ha : (PreSail.assert (4 ≤b Functions.flen_bytes)
        "extensions/FD/fext_insts.sail:282.28-282.29" : SailM Unit).run s = .ok () s := rfl
    rw [run_bind_ok _ _ _ _ _ ha]
    rw [run_bind_ok _ _ _ _ _ (rv64iEffectiveAddr_ext_data_get_addr_bisim spVal imm12 (.Load .Data) 4 s hsp)]
    dsimp only []
    rw [run_bind_ok _ _ _ _ _ (read_ram_plain_bisim_sail 4 (rv64iEffectiveAddrSpec spVal imm12) bytes4 s hmem4)]
    rw [setWidth_flenbits_nan_box_32]
    rw [run_bind_ok _ _ _ _ _ hw4]
    rfl
  obtain ⟨regs8, hw8, hf08, hms8, hoth8⟩ :=
    wF_bits_f0_run (BitVec.setWidth 8 bytes8) mstatusVal s hmstatus
  have hld8 : (sailLoadFpRamExec imm12 sp (.Fregidx 0#5) 8 (by decide)).run s =
      .ok (.Retire_Success ()) ({ s with regs := regs8 }) := by
    unfold sailLoadFpRamExec
    have ha : (PreSail.assert (8 ≤b Functions.flen_bytes)
        "extensions/FD/fext_insts.sail:282.28-282.29" : SailM Unit).run s = .ok () s := rfl
    rw [run_bind_ok _ _ _ _ _ ha]
    rw [run_bind_ok _ _ _ _ _ (rv64iEffectiveAddr_ext_data_get_addr_bisim spVal imm12 (.Load .Data) 8 s hsp)]
    dsimp only []
    rw [run_bind_ok _ _ _ _ _ (read_ram_plain_bisim_sail 8 (rv64iEffectiveAddrSpec spVal imm12) bytes8 s hmem8)]
    rw [setWidth_flenbits_nan_box_64]
    rw [run_bind_ok _ _ _ _ _ hw8]
    rfl
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hst4, hst8,
    ⟨regs4, hld4, hf04, hms4, hoth4⟩,
    ⟨regs8, hld8, hf08, hms8, hoth8⟩⟩

/-- Exact upstream Sail `execute_F_UN_X_TYPE_D` (`InstsEnd.lean`, lines 69300–69313) covering
    `FCLASS.D` and `FMV.X.D`. -/
noncomputable def sailExecuteFUnXTypeD (arg0 : fregidx) (arg1 : regidx) (arg2 : f_un_x_op_D) : SailM ExecutionResult := do
  let merge_var := (arg0, arg1, arg2)
  match merge_var with
  | (rs1, rd, .FCLASS_D) =>
    do
      let rs1_val ← rF_or_X_D rs1
      wX_bits rd (zero_extend (m := 64) (float_class_onehot_bits_forwards (← float_classify rs1_val)))
      pure (.Retire_Success ())
  | (rs1, rd, .FMV_X_D) =>
    do
      PreSail.assert ((Functions.xlen ≥b 64) && (Functions.flen ≥b 64))
        "extensions/FD/dext_insts.sail:853.32-853.33"
      wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb (← rF_bits rs1) 63 0))
      pure (.Retire_Success ())

/-- Exact upstream Sail `execute_F_UN_TYPE_X_S` (`InstsEnd.lean`, lines 69315–69327) covering
    `FCLASS.S` and `FMV.X.W`. -/
noncomputable def sailExecuteFUnTypeXS (arg0 : fregidx) (arg1 : regidx) (arg2 : f_un_op_x_S) : SailM ExecutionResult := do
  let merge_var := (arg0, arg1, arg2)
  match merge_var with
  | (rs1, rd, .FCLASS_S) =>
    do
      let rs1_val ← rF_or_X_S rs1
      wX_bits rd (zero_extend (m := 64) (float_class_onehot_bits_forwards (← float_classify rs1_val)))
      pure (.Retire_Success ())
  | (rs1, rd, .FMV_X_W) =>
    do
      wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb (← rF_bits rs1) 31 0))
      pure (.Retire_Success ())

/-- Exact upstream Sail `execute_F_UN_TYPE_F_S` (`InstsEnd.lean`, lines 69329–69331) covering
    `FMV.W.X`. -/
noncomputable def sailExecuteFUnTypeFS (rs1 : regidx) (rd : fregidx) (_op : f_un_op_f_S) : SailM ExecutionResult := do
  wF_bits rd (BitVec.setWidth (if (true : Bool) then 8 else 4 * 8)
    (nan_box (n := (8 *i 8)) (Sail.BitVec.extractLsb (← rX_bits rs1) 31 0)))
  pure (.Retire_Success ())

/-- Exact upstream Sail `execute_F_UN_F_TYPE_D` (`InstsEnd.lean`, lines 69779–69782) covering
    `FMV.D.X`. -/
noncomputable def sailExecuteFUnFTypeD (rs1 : regidx) (rd : fregidx) (_op : f_un_f_op_D) : SailM ExecutionResult := do
  PreSail.assert ((Functions.xlen ≥b 64) && (Functions.flen ≥b 64))
    "extensions/FD/dext_insts.sail:859.32-859.33"
  wF_bits rd (BitVec.setWidth (if (true : Bool) then 8 else 4 * 8)
    (nan_box (n := (8 *i 8)) (Sail.BitVec.extractLsb (← rX_bits rs1) 63 0)))
  pure (.Retire_Success ())

/-- Theorem 7 (Section 16): RV64F/D bitwise FP↔integer moves and IEEE-754 class instructions
    (`FMV.X.W`, `FMV.W.X`, `FMV.X.D`, `FMV.D.X`, `FCLASS.S`, `FCLASS.D`):
    - `FMV.X.W` / `FMV.X.D` / `FCLASS.S` / `FCLASS.D` write `rd` (`ra`/`x1`) without dirtying
      `mstatus.FS` or touching `fcsr`;
    - `FMV.W.X` / `FMV.D.X` apply `nan_box` and write the upstream `flenbits` (`BitVec 8`) slice to
      `f0` while marking `mstatus.FS := 0b11, SD := 1`. -/
theorem rv64FpMoveAndClassifyExec_bisim_sail
    (f0Val : flenbits) (raVal mstatusVal : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hf0 : s.regs.get? .f0 = some f0Val)
    (hra : s.regs.get? .x1 = some raVal)
    (hmstatus : s.regs.get? .mstatus = some mstatusVal) :
    (sailExecuteFUnTypeXS (.Fregidx 0#5) ra .FCLASS_S).run s =
      .ok (.Retire_Success ()) ({ s with regs := s.regs.insert .x1 (BitVec.zeroExtend 64 (float_class_onehot_bits_forwards (rv64FloatClassify32Spec (BitVec.setWidth 32 f0Val)))) }) ∧
    (sailExecuteFUnTypeXS (.Fregidx 0#5) ra .FMV_X_W).run s =
      .ok (.Retire_Success ()) ({ s with regs := s.regs.insert .x1 (BitVec.signExtend 64 (Sail.BitVec.extractLsb f0Val 31 0)) }) ∧
    (sailExecuteFUnXTypeD (.Fregidx 0#5) ra .FCLASS_D).run s =
      .ok (.Retire_Success ()) ({ s with regs := s.regs.insert .x1 (BitVec.zeroExtend 64 (float_class_onehot_bits_forwards (rv64FloatClassify64Spec (BitVec.setWidth 64 f0Val)))) }) ∧
    (sailExecuteFUnXTypeD (.Fregidx 0#5) ra .FMV_X_D).run s =
      .ok (.Retire_Success ()) ({ s with regs := s.regs.insert .x1 (BitVec.signExtend 64 (Sail.BitVec.extractLsb f0Val 63 0)) }) ∧
    (∃ regsW,
      (sailExecuteFUnTypeFS ra (.Fregidx 0#5) .FMV_W_X).run s =
        .ok (.Retire_Success ()) ({ s with regs := regsW }) ∧
      regsW.get? .f0 = some (BitVec.setWidth 8 (Sail.BitVec.extractLsb raVal 31 0) : flenbits) ∧
      regsW.get? .mstatus = some (rv64DirtyFdMstatusSpec mstatusVal) ∧
      (∀ r, (Register.f0 == r) = false → (Register.mstatus == r) = false →
        regsW.get? r = s.regs.get? r)) ∧
    (∃ regsD,
      (sailExecuteFUnFTypeD ra (.Fregidx 0#5) .FMV_D_X).run s =
        .ok (.Retire_Success ()) ({ s with regs := regsD }) ∧
      regsD.get? .f0 = some (BitVec.setWidth 8 (Sail.BitVec.extractLsb raVal 63 0) : flenbits) ∧
      regsD.get? .mstatus = some (rv64DirtyFdMstatusSpec mstatusVal) ∧
      (∀ r, (Register.f0 == r) = false → (Register.mstatus == r) = false →
        regsD.get? r = s.regs.get? r)) := by
  obtain ⟨regsW, hwW, hf0W, hmsW, hothW⟩ :=
    wF_bits_f0_run (BitVec.setWidth 8 (Sail.BitVec.extractLsb raVal 31 0)) mstatusVal s hmstatus
  have hmvWX : (sailExecuteFUnTypeFS ra (.Fregidx 0#5) .FMV_W_X).run s =
      .ok (.Retire_Success ()) { s with regs := regsW } := by
    unfold sailExecuteFUnTypeFS
    rw [run_bind_ok _ _ _ _ _ (rX_bits_ra_run raVal s hra)]
    rw [setWidth_flenbits_nan_box_32]
    rw [run_bind_ok _ _ _ _ _ hwW]
    rfl
  obtain ⟨regsD, hwD, hf0D, hmsD, hothD⟩ :=
    wF_bits_f0_run (BitVec.setWidth 8 (Sail.BitVec.extractLsb raVal 63 0)) mstatusVal s hmstatus
  have hmvDX : (sailExecuteFUnFTypeD ra (.Fregidx 0#5) .FMV_D_X).run s =
      .ok (.Retire_Success ()) { s with regs := regsD } := by
    unfold sailExecuteFUnFTypeD
    have ha : (PreSail.assert ((Functions.xlen ≥b 64) && (Functions.flen ≥b 64))
        "extensions/FD/dext_insts.sail:859.32-859.33" : SailM Unit).run s = .ok () s := rfl
    rw [run_bind_ok _ _ _ _ _ ha]
    rw [run_bind_ok _ _ _ _ _ (rX_bits_ra_run raVal s hra)]
    rw [setWidth_flenbits_nan_box_64]
    rw [run_bind_ok _ _ _ _ _ hwD]
    rfl
  refine ⟨?_, ?_, ?_, ?_,
    ⟨regsW, hmvWX, hf0W, hmsW, hothW⟩,
    ⟨regsD, hmvDX, hf0D, hmsD, hothD⟩⟩
  · unfold sailExecuteFUnTypeXS
    dsimp only []
    rw [run_bind_ok _ _ _ _ _ (rF_or_X_S_f0_run f0Val s hf0)]
    rw [run_bind_ok _ _ _ _ _ (float_classify_32_run (BitVec.setWidth 32 f0Val) s)]
    rw [run_bind_ok _ _ _ _ _ (wX_bits_ra_run _ s)]
    rfl
  · unfold sailExecuteFUnTypeXS
    dsimp only []
    rw [run_bind_ok _ _ _ _ _ (rF_bits_f0_run f0Val s hf0)]
    rw [run_bind_ok _ _ _ _ _ (wX_bits_ra_run _ s)]
    rfl
  · unfold sailExecuteFUnXTypeD
    dsimp only []
    rw [run_bind_ok _ _ _ _ _ (rF_or_X_D_f0_run f0Val s hf0)]
    rw [run_bind_ok _ _ _ _ _ (float_classify_64_run (BitVec.setWidth 64 f0Val) s)]
    rw [run_bind_ok _ _ _ _ _ (wX_bits_ra_run _ s)]
    rfl
  · unfold sailExecuteFUnXTypeD
    dsimp only []
    have ha : (PreSail.assert ((Functions.xlen ≥b 64) && (Functions.flen ≥b 64))
        "extensions/FD/dext_insts.sail:853.32-853.33" : SailM Unit).run s = .ok () s := rfl
    rw [run_bind_ok _ _ _ _ _ ha]
    rw [run_bind_ok _ _ _ _ _ (rF_bits_f0_run f0Val s hf0)]
    rw [run_bind_ok _ _ _ _ _ (wX_bits_ra_run _ s)]
    rfl

/-- Pure `TurboLean`-side IEEE-754-2008 `minNum`/`maxNum` selector for RV64F `FMIN.S` / `FMAX.S`
    (matching `execute_F_BIN_TYPE_F_S`, `InstsEnd.lean`, lines 69963–70010). -/
def rv64FpMinMaxSSpec (isMax : Bool) (v1 v2 : BitVec 32) : BitVec 32 × BitVec 5 :=
  if isMax then
    let (v2_le_v1, fflags) := fle_S v2 v1 true
    let res :=
      if f_is_NaN_S v1 && f_is_NaN_S v2 then canonical_NaN_S ()
      else if f_is_NaN_S v1 then v2
      else if f_is_NaN_S v2 then v1
      else if f_is_neg_zero_S v1 && f_is_pos_zero_S v2 then v2
      else if f_is_neg_zero_S v2 && f_is_pos_zero_S v1 then v1
      else if v2_le_v1 then v1 else v2
    (res, fflags)
  else
    let (v1_le_v2, fflags) := fle_S v1 v2 true
    let res :=
      if f_is_NaN_S v1 && f_is_NaN_S v2 then canonical_NaN_S ()
      else if f_is_NaN_S v1 then v2
      else if f_is_NaN_S v2 then v1
      else if f_is_neg_zero_S v1 && f_is_pos_zero_S v2 then v1
      else if f_is_neg_zero_S v2 && f_is_pos_zero_S v1 then v2
      else if v1_le_v2 then v1 else v2
    (res, fflags)

/-- Pure `TurboLean`-side IEEE-754-2008 `minNum`/`maxNum` selector for RV64D `FMIN.D` / `FMAX.D`
    (matching `execute_F_BIN_F_TYPE_D`, `InstsEnd.lean`, lines 70191–70238). -/
def rv64FpMinMaxDSpec (isMax : Bool) (v1 v2 : BitVec 64) : BitVec 64 × BitVec 5 :=
  if isMax then
    let (v2_le_v1, fflags) := fle_D v2 v1 true
    let res :=
      if f_is_NaN_D v1 && f_is_NaN_D v2 then canonical_NaN_D ()
      else if f_is_NaN_D v1 then v2
      else if f_is_NaN_D v2 then v1
      else if f_is_neg_zero_D v1 && f_is_pos_zero_D v2 then v2
      else if f_is_neg_zero_D v2 && f_is_pos_zero_D v1 then v1
      else if v2_le_v1 then v1 else v2
    (res, fflags)
  else
    let (v1_le_v2, fflags) := fle_D v1 v2 true
    let res :=
      if f_is_NaN_D v1 && f_is_NaN_D v2 then canonical_NaN_D ()
      else if f_is_NaN_D v1 then v2
      else if f_is_NaN_D v2 then v1
      else if f_is_neg_zero_D v1 && f_is_pos_zero_D v2 then v1
      else if f_is_neg_zero_D v2 && f_is_pos_zero_D v1 then v2
      else if v1_le_v2 then v1 else v2
    (res, fflags)

/-- Exact upstream Sail `execute_F_BIN_TYPE_F_S` (`InstsEnd.lean`, lines 69928–70013) covering
    `FSGNJ.S`, `FSGNJN.S`, `FSGNJX.S`, `FMIN.S`, and `FMAX.S`. -/
noncomputable def sailExecuteFBinTypeFS (arg0 arg1 arg2 : fregidx) (arg3 : f_bin_op_f_S) : SailM ExecutionResult := do
  let merge_var := (arg0, arg1, arg2, arg3)
  match merge_var with
  | (rs2, rs1, rd, .FSGNJ_S) =>
    do
      let rs1_val_S ← rF_or_X_S rs1
      let rs2_val_S ← rF_or_X_S rs2
      let (_, e1, m1) := fsplit_S rs1_val_S
      let (s2, _, _) := fsplit_S rs2_val_S
      let rd_val_S := fmake_S s2 e1 m1
      wF_or_X_S rd rd_val_S
      pure (.Retire_Success ())
  | (rs2, rs1, rd, .FSGNJN_S) =>
    do
      let rs1_val_S ← rF_or_X_S rs1
      let rs2_val_S ← rF_or_X_S rs2
      let (_, e1, m1) := fsplit_S rs1_val_S
      let (s2, _, _) := fsplit_S rs2_val_S
      let rd_val_S := fmake_S (1#1 ^^^ s2) e1 m1
      wF_or_X_S rd rd_val_S
      pure (.Retire_Success ())
  | (rs2, rs1, rd, .FSGNJX_S) =>
    do
      let rs1_val_S ← rF_or_X_S rs1
      let rs2_val_S ← rF_or_X_S rs2
      let (s1, e1, m1) := fsplit_S rs1_val_S
      let (s2, _, _) := fsplit_S rs2_val_S
      let rd_val_S := fmake_S (s1 ^^^ s2) e1 m1
      wF_or_X_S rd rd_val_S
      pure (.Retire_Success ())
  | (rs2, rs1, rd, .FMIN_S) =>
    do
      let rs1_val_S ← rF_or_X_S rs1
      let rs2_val_S ← rF_or_X_S rs2
      let is_quiet := true
      let (rs1_lt_rs2, fflags) := fle_S rs1_val_S rs2_val_S is_quiet
      let rd_val_S :=
        if (f_is_NaN_S rs1_val_S && f_is_NaN_S rs2_val_S : Bool) then canonical_NaN_S ()
        else if (f_is_NaN_S rs1_val_S : Bool) then rs2_val_S
        else if (f_is_NaN_S rs2_val_S : Bool) then rs1_val_S
        else if (f_is_neg_zero_S rs1_val_S && f_is_pos_zero_S rs2_val_S : Bool) then rs1_val_S
        else if (f_is_neg_zero_S rs2_val_S && f_is_pos_zero_S rs1_val_S : Bool) then rs2_val_S
        else if (rs1_lt_rs2 : Bool) then rs1_val_S else rs2_val_S
      accrue_fflags fflags
      wF_or_X_S rd rd_val_S
      pure (.Retire_Success ())
  | (rs2, rs1, rd, .FMAX_S) =>
    do
      let rs1_val_S ← rF_or_X_S rs1
      let rs2_val_S ← rF_or_X_S rs2
      let is_quiet := true
      let (rs2_lt_rs1, fflags) := fle_S rs2_val_S rs1_val_S is_quiet
      let rd_val_S :=
        if (f_is_NaN_S rs1_val_S && f_is_NaN_S rs2_val_S : Bool) then canonical_NaN_S ()
        else if (f_is_NaN_S rs1_val_S : Bool) then rs2_val_S
        else if (f_is_NaN_S rs2_val_S : Bool) then rs1_val_S
        else if (f_is_neg_zero_S rs1_val_S && f_is_pos_zero_S rs2_val_S : Bool) then rs2_val_S
        else if (f_is_neg_zero_S rs2_val_S && f_is_pos_zero_S rs1_val_S : Bool) then rs1_val_S
        else if (rs2_lt_rs1 : Bool) then rs1_val_S else rs2_val_S
      accrue_fflags fflags
      wF_or_X_S rd rd_val_S
      pure (.Retire_Success ())

/-- Exact upstream Sail `execute_F_BIN_F_TYPE_D` (`InstsEnd.lean`, lines 70156–70241) covering
    `FSGNJ.D`, `FSGNJN.D`, `FSGNJX.D`, `FMIN.D`, and `FMAX.D`. -/
noncomputable def sailExecuteFBinFTypeD (arg0 arg1 arg2 : fregidx) (arg3 : f_bin_f_op_D) : SailM ExecutionResult := do
  let merge_var := (arg0, arg1, arg2, arg3)
  match merge_var with
  | (rs2, rs1, rd, .FSGNJ_D) =>
    do
      let rs1_val_D ← rF_or_X_D rs1
      let rs2_val_D ← rF_or_X_D rs2
      let (_, e1, m1) := fsplit_D rs1_val_D
      let (s2, _, _) := fsplit_D rs2_val_D
      let rd_val_D := fmake_D s2 e1 m1
      wF_or_X_D rd rd_val_D
      pure (.Retire_Success ())
  | (rs2, rs1, rd, .FSGNJN_D) =>
    do
      let rs1_val_D ← rF_or_X_D rs1
      let rs2_val_D ← rF_or_X_D rs2
      let (_, e1, m1) := fsplit_D rs1_val_D
      let (s2, _, _) := fsplit_D rs2_val_D
      let rd_val_D := fmake_D (1#1 ^^^ s2) e1 m1
      wF_or_X_D rd rd_val_D
      pure (.Retire_Success ())
  | (rs2, rs1, rd, .FSGNJX_D) =>
    do
      let rs1_val_D ← rF_or_X_D rs1
      let rs2_val_D ← rF_or_X_D rs2
      let (s1, e1, m1) := fsplit_D rs1_val_D
      let (s2, _, _) := fsplit_D rs2_val_D
      let rd_val_D := fmake_D (s1 ^^^ s2) e1 m1
      wF_or_X_D rd rd_val_D
      pure (.Retire_Success ())
  | (rs2, rs1, rd, .FMIN_D) =>
    do
      let rs1_val_D ← rF_or_X_D rs1
      let rs2_val_D ← rF_or_X_D rs2
      let is_quiet := true
      let (rs1_lt_rs2, fflags) := fle_D rs1_val_D rs2_val_D is_quiet
      let rd_val_D :=
        if (f_is_NaN_D rs1_val_D && f_is_NaN_D rs2_val_D : Bool) then canonical_NaN_D ()
        else if (f_is_NaN_D rs1_val_D : Bool) then rs2_val_D
        else if (f_is_NaN_D rs2_val_D : Bool) then rs1_val_D
        else if (f_is_neg_zero_D rs1_val_D && f_is_pos_zero_D rs2_val_D : Bool) then rs1_val_D
        else if (f_is_neg_zero_D rs2_val_D && f_is_pos_zero_D rs1_val_D : Bool) then rs2_val_D
        else if (rs1_lt_rs2 : Bool) then rs1_val_D else rs2_val_D
      accrue_fflags fflags
      wF_or_X_D rd rd_val_D
      pure (.Retire_Success ())
  | (rs2, rs1, rd, .FMAX_D) =>
    do
      let rs1_val_D ← rF_or_X_D rs1
      let rs2_val_D ← rF_or_X_D rs2
      let is_quiet := true
      let (rs2_lt_rs1, fflags) := fle_D rs2_val_D rs1_val_D is_quiet
      let rd_val_D :=
        if (f_is_NaN_D rs1_val_D && f_is_NaN_D rs2_val_D : Bool) then canonical_NaN_D ()
        else if (f_is_NaN_D rs1_val_D : Bool) then rs2_val_D
        else if (f_is_NaN_D rs2_val_D : Bool) then rs1_val_D
        else if (f_is_neg_zero_D rs1_val_D && f_is_pos_zero_D rs2_val_D : Bool) then rs2_val_D
        else if (f_is_neg_zero_D rs2_val_D && f_is_pos_zero_D rs1_val_D : Bool) then rs1_val_D
        else if (rs2_lt_rs1 : Bool) then rs1_val_D else rs2_val_D
      accrue_fflags fflags
      wF_or_X_D rd rd_val_D
      pure (.Retire_Success ())

private theorem sailExecMinMaxS_f1_f0_run (isMax : Bool)
    (f0Val f1Val : flenbits) (fcsrVal : BitVec 32) (mstatusVal : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hf0 : s.regs.get? .f0 = some f0Val)
    (hf1 : s.regs.get? .f1 = some f1Val)
    (hfcsr : s.regs.get? .fcsr = some fcsrVal)
    (hmstatus : s.regs.get? .mstatus = some mstatusVal) :
    let out := rv64FpMinMaxSSpec isMax (BitVec.setWidth 32 f0Val) (BitVec.setWidth 32 f1Val)
    ∃ regs,
      (sailExecuteFBinTypeFS (.Fregidx 1#5) (.Fregidx 0#5) (.Fregidx 0#5)
        (if isMax then .FMAX_S else .FMIN_S)).run s =
        .ok (.Retire_Success ()) { s with regs := regs } ∧
      regs.get? .f0 = some (BitVec.setWidth 8 out.1 : flenbits) ∧
      regs.get? .fcsr = some (rv64AccrueFflagsFcsrSpec fcsrVal out.2) := by
  let out := rv64FpMinMaxSSpec isMax (BitVec.setWidth 32 f0Val) (BitVec.setWidth 32 f1Val)
  obtain ⟨regsA, hacc, hfcA, hmsA, _⟩ := accrue_fflags_run fcsrVal mstatusVal out.2 s hfcsr hmstatus
  obtain ⟨regsB, hw, hf0B, _, hothB⟩ := wF_or_X_S_f0_run out.1 _ { s with regs := regsA } hmsA
  refine ⟨regsB, ?_, hf0B, ?_⟩
  · cases isMax
    · rw [if_neg Bool.false_ne_true]; unfold sailExecuteFBinTypeFS; dsimp only []
      rw [run_bind_ok _ _ _ _ _ (rF_or_X_S_f0_run f0Val s hf0),
          run_bind_ok _ _ _ _ _ (rF_or_X_S_f1_run f1Val s hf1)]
      change (do accrue_fflags out.2; wF_or_X_S (.Fregidx 0#5) out.1
                 pure (ExecutionResult.Retire_Success ()) : SailM ExecutionResult).run s = _
      rw [run_bind_ok _ _ _ _ _ hacc, run_bind_ok _ _ _ _ _ hw]; rfl
    · rw [if_pos rfl]; unfold sailExecuteFBinTypeFS; dsimp only []
      rw [run_bind_ok _ _ _ _ _ (rF_or_X_S_f0_run f0Val s hf0),
          run_bind_ok _ _ _ _ _ (rF_or_X_S_f1_run f1Val s hf1)]
      change (do accrue_fflags out.2; wF_or_X_S (.Fregidx 0#5) out.1
                 pure (ExecutionResult.Retire_Success ()) : SailM ExecutionResult).run s = _
      rw [run_bind_ok _ _ _ _ _ hacc, run_bind_ok _ _ _ _ _ hw]; rfl
  · rw [hothB .fcsr rfl rfl]; exact hfcA

private theorem sailExecMinMaxD_f1_f0_run (isMax : Bool)
    (f0Val f1Val : flenbits) (fcsrVal : BitVec 32) (mstatusVal : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hf0 : s.regs.get? .f0 = some f0Val)
    (hf1 : s.regs.get? .f1 = some f1Val)
    (hfcsr : s.regs.get? .fcsr = some fcsrVal)
    (hmstatus : s.regs.get? .mstatus = some mstatusVal) :
    let out := rv64FpMinMaxDSpec isMax (BitVec.setWidth 64 f0Val) (BitVec.setWidth 64 f1Val)
    ∃ regs,
      (sailExecuteFBinFTypeD (.Fregidx 1#5) (.Fregidx 0#5) (.Fregidx 0#5)
        (if isMax then .FMAX_D else .FMIN_D)).run s =
        .ok (.Retire_Success ()) { s with regs := regs } ∧
      regs.get? .f0 = some (BitVec.setWidth 8 out.1 : flenbits) ∧
      regs.get? .fcsr = some (rv64AccrueFflagsFcsrSpec fcsrVal out.2) := by
  let out := rv64FpMinMaxDSpec isMax (BitVec.setWidth 64 f0Val) (BitVec.setWidth 64 f1Val)
  obtain ⟨regsA, hacc, hfcA, hmsA, _⟩ := accrue_fflags_run fcsrVal mstatusVal out.2 s hfcsr hmstatus
  obtain ⟨regsB, hw, hf0B, _, hothB⟩ := wF_or_X_D_f0_run out.1 _ { s with regs := regsA } hmsA
  refine ⟨regsB, ?_, hf0B, ?_⟩
  · cases isMax
    · rw [if_neg Bool.false_ne_true]; unfold sailExecuteFBinFTypeD; dsimp only []
      rw [run_bind_ok _ _ _ _ _ (rF_or_X_D_f0_run f0Val s hf0),
          run_bind_ok _ _ _ _ _ (rF_or_X_D_f1_run f1Val s hf1)]
      change (do accrue_fflags out.2; wF_or_X_D (.Fregidx 0#5) out.1
                 pure (ExecutionResult.Retire_Success ()) : SailM ExecutionResult).run s = _
      rw [run_bind_ok _ _ _ _ _ hacc, run_bind_ok _ _ _ _ _ hw]; rfl
    · rw [if_pos rfl]; unfold sailExecuteFBinFTypeD; dsimp only []
      rw [run_bind_ok _ _ _ _ _ (rF_or_X_D_f0_run f0Val s hf0),
          run_bind_ok _ _ _ _ _ (rF_or_X_D_f1_run f1Val s hf1)]
      change (do accrue_fflags out.2; wF_or_X_D (.Fregidx 0#5) out.1
                 pure (ExecutionResult.Retire_Success ()) : SailM ExecutionResult).run s = _
      rw [run_bind_ok _ _ _ _ _ hacc, run_bind_ok _ _ _ _ _ hw]; rfl
  · rw [hothB .fcsr rfl rfl]; exact hfcA

/-- Theorem 8 (Section 16): RV64F/D sign-injection (`FSGNJ.S`/`D`, `FSGNJN.S`/`D`, `FSGNJX.S`/`D`)
    and IEEE-754-2008 minimum/maximum (`FMIN.S`/`D`, `FMAX.S`/`D`) execution bisimulation against
    `execute_F_BIN_TYPE_F_S` and `execute_F_BIN_F_TYPE_D` (updating `.f0` via upstream `flenbits =
    BitVec 8`), including NaN canonicalization, single-NaN operand selection, `-0.0` vs `+0.0`
    tie-breaking, and `accrue_fflags` + `wF_or_X_*` state transitions. -/
theorem rv64FpSignInjectAndMinMaxExec_bisim_sail
    (f0Val f1Val : flenbits) (fcsrVal : BitVec 32) (mstatusVal : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hf0 : s.regs.get? .f0 = some f0Val)
    (hf1 : s.regs.get? .f1 = some f1Val)
    (hfcsr : s.regs.get? .fcsr = some fcsrVal)
    (hmstatus : s.regs.get? .mstatus = some mstatusVal) :
    let v0S := BitVec.setWidth 32 f0Val
    let v1S := BitVec.setWidth 32 f1Val
    let (s0S, e0S, m0S) := fsplit_S v0S
    let (s1S, _, _) := fsplit_S v1S
    let v0D := BitVec.setWidth 64 f0Val
    let v1D := BitVec.setWidth 64 f1Val
    let (s0D, e0D, m0D) := fsplit_D v0D
    let (s1D, _, _) := fsplit_D v1D
    (∃ regs, (sailExecuteFBinTypeFS (.Fregidx 1#5) (.Fregidx 0#5) (.Fregidx 0#5) .FSGNJ_S).run s =
        .ok (.Retire_Success ()) { s with regs := regs } ∧
      regs.get? .f0 = some (BitVec.setWidth 8 (fmake_S s1S e0S m0S) : flenbits) ∧
      regs.get? .mstatus = some (rv64DirtyFdMstatusSpec mstatusVal) ∧
      regs.get? .fcsr = some fcsrVal) ∧
    (∃ regs, (sailExecuteFBinTypeFS (.Fregidx 1#5) (.Fregidx 0#5) (.Fregidx 0#5) .FSGNJN_S).run s =
        .ok (.Retire_Success ()) { s with regs := regs } ∧
      regs.get? .f0 = some (BitVec.setWidth 8 (fmake_S (1#1 ^^^ s1S) e0S m0S) : flenbits) ∧
      regs.get? .mstatus = some (rv64DirtyFdMstatusSpec mstatusVal) ∧
      regs.get? .fcsr = some fcsrVal) ∧
    (∃ regs, (sailExecuteFBinTypeFS (.Fregidx 1#5) (.Fregidx 0#5) (.Fregidx 0#5) .FSGNJX_S).run s =
        .ok (.Retire_Success ()) { s with regs := regs } ∧
      regs.get? .f0 = some (BitVec.setWidth 8 (fmake_S (s0S ^^^ s1S) e0S m0S) : flenbits) ∧
      regs.get? .mstatus = some (rv64DirtyFdMstatusSpec mstatusVal) ∧
      regs.get? .fcsr = some fcsrVal) ∧
    (∃ regs, (sailExecuteFBinTypeFS (.Fregidx 1#5) (.Fregidx 0#5) (.Fregidx 0#5) .FMIN_S).run s =
        .ok (.Retire_Success ()) { s with regs := regs } ∧
      regs.get? .f0 = some (BitVec.setWidth 8 (rv64FpMinMaxSSpec false v0S v1S).1 : flenbits) ∧
      regs.get? .fcsr = some (rv64AccrueFflagsFcsrSpec fcsrVal (rv64FpMinMaxSSpec false v0S v1S).2)) ∧
    (∃ regs, (sailExecuteFBinTypeFS (.Fregidx 1#5) (.Fregidx 0#5) (.Fregidx 0#5) .FMAX_S).run s =
        .ok (.Retire_Success ()) { s with regs := regs } ∧
      regs.get? .f0 = some (BitVec.setWidth 8 (rv64FpMinMaxSSpec true v0S v1S).1 : flenbits) ∧
      regs.get? .fcsr = some (rv64AccrueFflagsFcsrSpec fcsrVal (rv64FpMinMaxSSpec true v0S v1S).2)) ∧
    (∃ regs, (sailExecuteFBinFTypeD (.Fregidx 1#5) (.Fregidx 0#5) (.Fregidx 0#5) .FSGNJ_D).run s =
        .ok (.Retire_Success ()) { s with regs := regs } ∧
      regs.get? .f0 = some (BitVec.setWidth 8 (fmake_D s1D e0D m0D) : flenbits) ∧
      regs.get? .mstatus = some (rv64DirtyFdMstatusSpec mstatusVal) ∧
      regs.get? .fcsr = some fcsrVal) ∧
    (∃ regs, (sailExecuteFBinFTypeD (.Fregidx 1#5) (.Fregidx 0#5) (.Fregidx 0#5) .FSGNJN_D).run s =
        .ok (.Retire_Success ()) { s with regs := regs } ∧
      regs.get? .f0 = some (BitVec.setWidth 8 (fmake_D (1#1 ^^^ s1D) e0D m0D) : flenbits) ∧
      regs.get? .mstatus = some (rv64DirtyFdMstatusSpec mstatusVal) ∧
      regs.get? .fcsr = some fcsrVal) ∧
    (∃ regs, (sailExecuteFBinFTypeD (.Fregidx 1#5) (.Fregidx 0#5) (.Fregidx 0#5) .FSGNJX_D).run s =
        .ok (.Retire_Success ()) { s with regs := regs } ∧
      regs.get? .f0 = some (BitVec.setWidth 8 (fmake_D (s0D ^^^ s1D) e0D m0D) : flenbits) ∧
      regs.get? .mstatus = some (rv64DirtyFdMstatusSpec mstatusVal) ∧
      regs.get? .fcsr = some fcsrVal) ∧
    (∃ regs, (sailExecuteFBinFTypeD (.Fregidx 1#5) (.Fregidx 0#5) (.Fregidx 0#5) .FMIN_D).run s =
        .ok (.Retire_Success ()) { s with regs := regs } ∧
      regs.get? .f0 = some (BitVec.setWidth 8 (rv64FpMinMaxDSpec false v0D v1D).1 : flenbits) ∧
      regs.get? .fcsr = some (rv64AccrueFflagsFcsrSpec fcsrVal (rv64FpMinMaxDSpec false v0D v1D).2)) ∧
    (∃ regs, (sailExecuteFBinFTypeD (.Fregidx 1#5) (.Fregidx 0#5) (.Fregidx 0#5) .FMAX_D).run s =
        .ok (.Retire_Success ()) { s with regs := regs } ∧
      regs.get? .f0 = some (BitVec.setWidth 8 (rv64FpMinMaxDSpec true v0D v1D).1 : flenbits) ∧
      regs.get? .fcsr = some (rv64AccrueFflagsFcsrSpec fcsrVal (rv64FpMinMaxDSpec true v0D v1D).2)) ∧
    rv64FpMinMaxSSpec false (canonical_NaN_S ()) (canonical_NaN_S ()) = (canonical_NaN_S (), 0#5) ∧
    rv64FpMinMaxSSpec false 0x7f800001#32 0x3f800000#32 = (0x3f800000#32, 0b10000#5) ∧
    rv64FpMinMaxSSpec false 0x80000000#32 0x00000000#32 = (0x80000000#32, 0#5) ∧
    rv64FpMinMaxSSpec true 0x80000000#32 0x00000000#32 = (0x00000000#32, 0#5) ∧
    rv64FpMinMaxDSpec false (canonical_NaN_D ()) (canonical_NaN_D ()) = (canonical_NaN_D (), 0#5) ∧
    rv64FpMinMaxDSpec false 0x7ff0000000000001#64 0x3ff0000000000000#64 = (0x3ff0000000000000#64, 0b10000#5) ∧
    rv64FpMinMaxDSpec false 0x8000000000000000#64 0x0000000000000000#64 = (0x8000000000000000#64, 0#5) ∧
    rv64FpMinMaxDSpec true 0x8000000000000000#64 0x0000000000000000#64 = (0x0000000000000000#64, 0#5) := by
  dsimp only []
  let v0S := BitVec.setWidth 32 f0Val
  let v1S := BitVec.setWidth 32 f1Val
  let v0D := BitVec.setWidth 64 f0Val
  let v1D := BitVec.setWidth 64 f1Val
  have hsgnjS : ∃ regs,
      (sailExecuteFBinTypeFS (.Fregidx 1#5) (.Fregidx 0#5) (.Fregidx 0#5) .FSGNJ_S).run s =
        .ok (.Retire_Success ()) { s with regs := regs } ∧
      regs.get? .f0 = some (BitVec.setWidth 8 (fmake_S (fsplit_S v1S).1 (fsplit_S v0S).2.1 (fsplit_S v0S).2.2) : flenbits) ∧
      regs.get? .mstatus = some (rv64DirtyFdMstatusSpec mstatusVal) ∧
      regs.get? .fcsr = some fcsrVal := by
    obtain ⟨regs, hw, hf0', hms', hoth⟩ := wF_or_X_S_f0_run (fmake_S (fsplit_S v1S).1 (fsplit_S v0S).2.1 (fsplit_S v0S).2.2) mstatusVal s hmstatus
    refine ⟨regs, ?_, hf0', hms', ?_⟩
    · unfold sailExecuteFBinTypeFS; dsimp only []
      rw [run_bind_ok _ _ _ _ _ (rF_or_X_S_f0_run f0Val s hf0), run_bind_ok _ _ _ _ _ (rF_or_X_S_f1_run f1Val s hf1)]
      change (do wF_or_X_S (.Fregidx 0#5) (fmake_S (fsplit_S v1S).1 (fsplit_S v0S).2.1 (fsplit_S v0S).2.2); pure (.Retire_Success ()) : SailM ExecutionResult).run s = _
      rw [run_bind_ok _ _ _ _ _ hw]; rfl
    · rw [hoth .fcsr rfl rfl]; exact hfcsr
  have hsgnjnS : ∃ regs,
      (sailExecuteFBinTypeFS (.Fregidx 1#5) (.Fregidx 0#5) (.Fregidx 0#5) .FSGNJN_S).run s =
        .ok (.Retire_Success ()) { s with regs := regs } ∧
      regs.get? .f0 = some (BitVec.setWidth 8 (fmake_S (1#1 ^^^ (fsplit_S v1S).1) (fsplit_S v0S).2.1 (fsplit_S v0S).2.2) : flenbits) ∧
      regs.get? .mstatus = some (rv64DirtyFdMstatusSpec mstatusVal) ∧
      regs.get? .fcsr = some fcsrVal := by
    obtain ⟨regs, hw, hf0', hms', hoth⟩ := wF_or_X_S_f0_run (fmake_S (1#1 ^^^ (fsplit_S v1S).1) (fsplit_S v0S).2.1 (fsplit_S v0S).2.2) mstatusVal s hmstatus
    refine ⟨regs, ?_, hf0', hms', ?_⟩
    · unfold sailExecuteFBinTypeFS; dsimp only []
      rw [run_bind_ok _ _ _ _ _ (rF_or_X_S_f0_run f0Val s hf0), run_bind_ok _ _ _ _ _ (rF_or_X_S_f1_run f1Val s hf1)]
      change (do wF_or_X_S (.Fregidx 0#5) (fmake_S (1#1 ^^^ (fsplit_S v1S).1) (fsplit_S v0S).2.1 (fsplit_S v0S).2.2); pure (.Retire_Success ()) : SailM ExecutionResult).run s = _
      rw [run_bind_ok _ _ _ _ _ hw]; rfl
    · rw [hoth .fcsr rfl rfl]; exact hfcsr
  have hsgnjxS : ∃ regs,
      (sailExecuteFBinTypeFS (.Fregidx 1#5) (.Fregidx 0#5) (.Fregidx 0#5) .FSGNJX_S).run s =
        .ok (.Retire_Success ()) { s with regs := regs } ∧
      regs.get? .f0 = some (BitVec.setWidth 8 (fmake_S ((fsplit_S v0S).1 ^^^ (fsplit_S v1S).1) (fsplit_S v0S).2.1 (fsplit_S v0S).2.2) : flenbits) ∧
      regs.get? .mstatus = some (rv64DirtyFdMstatusSpec mstatusVal) ∧
      regs.get? .fcsr = some fcsrVal := by
    obtain ⟨regs, hw, hf0', hms', hoth⟩ := wF_or_X_S_f0_run (fmake_S ((fsplit_S v0S).1 ^^^ (fsplit_S v1S).1) (fsplit_S v0S).2.1 (fsplit_S v0S).2.2) mstatusVal s hmstatus
    refine ⟨regs, ?_, hf0', hms', ?_⟩
    · unfold sailExecuteFBinTypeFS; dsimp only []
      rw [run_bind_ok _ _ _ _ _ (rF_or_X_S_f0_run f0Val s hf0), run_bind_ok _ _ _ _ _ (rF_or_X_S_f1_run f1Val s hf1)]
      change (do wF_or_X_S (.Fregidx 0#5) (fmake_S ((fsplit_S v0S).1 ^^^ (fsplit_S v1S).1) (fsplit_S v0S).2.1 (fsplit_S v0S).2.2); pure (.Retire_Success ()) : SailM ExecutionResult).run s = _
      rw [run_bind_ok _ _ _ _ _ hw]; rfl
    · rw [hoth .fcsr rfl rfl]; exact hfcsr
  have hsgnjD : ∃ regs,
      (sailExecuteFBinFTypeD (.Fregidx 1#5) (.Fregidx 0#5) (.Fregidx 0#5) .FSGNJ_D).run s =
        .ok (.Retire_Success ()) { s with regs := regs } ∧
      regs.get? .f0 = some (BitVec.setWidth 8 (fmake_D (fsplit_D v1D).1 (fsplit_D v0D).2.1 (fsplit_D v0D).2.2) : flenbits) ∧
      regs.get? .mstatus = some (rv64DirtyFdMstatusSpec mstatusVal) ∧
      regs.get? .fcsr = some fcsrVal := by
    obtain ⟨regs, hw, hf0', hms', hoth⟩ := wF_or_X_D_f0_run (fmake_D (fsplit_D v1D).1 (fsplit_D v0D).2.1 (fsplit_D v0D).2.2) mstatusVal s hmstatus
    refine ⟨regs, ?_, hf0', hms', ?_⟩
    · unfold sailExecuteFBinFTypeD; dsimp only []
      rw [run_bind_ok _ _ _ _ _ (rF_or_X_D_f0_run f0Val s hf0), run_bind_ok _ _ _ _ _ (rF_or_X_D_f1_run f1Val s hf1)]
      change (do wF_or_X_D (.Fregidx 0#5) (fmake_D (fsplit_D v1D).1 (fsplit_D v0D).2.1 (fsplit_D v0D).2.2); pure (.Retire_Success ()) : SailM ExecutionResult).run s = _
      rw [run_bind_ok _ _ _ _ _ hw]; rfl
    · rw [hoth .fcsr rfl rfl]; exact hfcsr
  have hsgnjnD : ∃ regs,
      (sailExecuteFBinFTypeD (.Fregidx 1#5) (.Fregidx 0#5) (.Fregidx 0#5) .FSGNJN_D).run s =
        .ok (.Retire_Success ()) { s with regs := regs } ∧
      regs.get? .f0 = some (BitVec.setWidth 8 (fmake_D (1#1 ^^^ (fsplit_D v1D).1) (fsplit_D v0D).2.1 (fsplit_D v0D).2.2) : flenbits) ∧
      regs.get? .mstatus = some (rv64DirtyFdMstatusSpec mstatusVal) ∧
      regs.get? .fcsr = some fcsrVal := by
    obtain ⟨regs, hw, hf0', hms', hoth⟩ := wF_or_X_D_f0_run (fmake_D (1#1 ^^^ (fsplit_D v1D).1) (fsplit_D v0D).2.1 (fsplit_D v0D).2.2) mstatusVal s hmstatus
    refine ⟨regs, ?_, hf0', hms', ?_⟩
    · unfold sailExecuteFBinFTypeD; dsimp only []
      rw [run_bind_ok _ _ _ _ _ (rF_or_X_D_f0_run f0Val s hf0), run_bind_ok _ _ _ _ _ (rF_or_X_D_f1_run f1Val s hf1)]
      change (do wF_or_X_D (.Fregidx 0#5) (fmake_D (1#1 ^^^ (fsplit_D v1D).1) (fsplit_D v0D).2.1 (fsplit_D v0D).2.2); pure (.Retire_Success ()) : SailM ExecutionResult).run s = _
      rw [run_bind_ok _ _ _ _ _ hw]; rfl
    · rw [hoth .fcsr rfl rfl]; exact hfcsr
  have hsgnjxD : ∃ regs,
      (sailExecuteFBinFTypeD (.Fregidx 1#5) (.Fregidx 0#5) (.Fregidx 0#5) .FSGNJX_D).run s =
        .ok (.Retire_Success ()) { s with regs := regs } ∧
      regs.get? .f0 = some (BitVec.setWidth 8 (fmake_D ((fsplit_D v0D).1 ^^^ (fsplit_D v1D).1) (fsplit_D v0D).2.1 (fsplit_D v0D).2.2) : flenbits) ∧
      regs.get? .mstatus = some (rv64DirtyFdMstatusSpec mstatusVal) ∧
      regs.get? .fcsr = some fcsrVal := by
    obtain ⟨regs, hw, hf0', hms', hoth⟩ := wF_or_X_D_f0_run (fmake_D ((fsplit_D v0D).1 ^^^ (fsplit_D v1D).1) (fsplit_D v0D).2.1 (fsplit_D v0D).2.2) mstatusVal s hmstatus
    refine ⟨regs, ?_, hf0', hms', ?_⟩
    · unfold sailExecuteFBinFTypeD; dsimp only []
      rw [run_bind_ok _ _ _ _ _ (rF_or_X_D_f0_run f0Val s hf0), run_bind_ok _ _ _ _ _ (rF_or_X_D_f1_run f1Val s hf1)]
      change (do wF_or_X_D (.Fregidx 0#5) (fmake_D ((fsplit_D v0D).1 ^^^ (fsplit_D v1D).1) (fsplit_D v0D).2.1 (fsplit_D v0D).2.2); pure (.Retire_Success ()) : SailM ExecutionResult).run s = _
      rw [run_bind_ok _ _ _ _ _ hw]; rfl
    · rw [hoth .fcsr rfl rfl]; exact hfcsr
  refine ⟨hsgnjS, hsgnjnS, hsgnjxS,
    sailExecMinMaxS_f1_f0_run false f0Val f1Val fcsrVal mstatusVal s hf0 hf1 hfcsr hmstatus,
    sailExecMinMaxS_f1_f0_run true f0Val f1Val fcsrVal mstatusVal s hf0 hf1 hfcsr hmstatus,
    hsgnjD, hsgnjnD, hsgnjxD,
    sailExecMinMaxD_f1_f0_run false f0Val f1Val fcsrVal mstatusVal s hf0 hf1 hfcsr hmstatus,
    sailExecMinMaxD_f1_f0_run true f0Val f1Val fcsrVal mstatusVal s hf0 hf1 hfcsr hmstatus, ?_⟩
  decide

private theorem rX_bits_sp_run (val : BitVec 64)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hx2 : s.regs.get? .x2 = some val) :
    (rX_bits sp).run s = .ok val s := by
  unfold sp
  simp [rX_bits, rX, regval_from_reg, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.toNatInt,
    readReg, PreSail.readReg, get, getThe, MonadStateOf.get]
  dsimp [EStateM.bind, EStateM.get, EStateM.pure, EStateM.run]
  rw [hx2]; rfl

/-- Exact `Zfinx`-mode (`Ext_F = false`, `Ext_Zfinx = true`) `x`-register path of upstream
    `rF_or_X_S` / `rF_or_X_D` / `wF_or_X_S` / `wF_or_X_D` (`FdextRegs.lean:448–481`), operating
    over architectural 64-bit general-purpose registers without `flenbits = BitVec 8` truncation. -/
noncomputable def sailZfinxReadS (i : fregidx) : SailM (BitVec 32) := do
  pure (Sail.BitVec.extractLsb (← rX_bits (fregidx_to_regidx i)) 31 0)

noncomputable def sailZfinxReadD (i : fregidx) : SailM (BitVec 64) := do
  pure (Sail.BitVec.extractLsb (← rX_bits (fregidx_to_regidx i)) 63 0)

noncomputable def sailZfinxWriteS (i : fregidx) (data : BitVec 32) : SailM Unit :=
  wX_bits (fregidx_to_regidx i) (sign_extend (m := 64) data)

noncomputable def sailZfinxWriteD (i : fregidx) (data : BitVec 64) : SailM Unit :=
  wX_bits (fregidx_to_regidx i) (sign_extend (m := 64) data)

/-- Exact full-width `Zfinx` (`x`-register) RV64F/Zfinx execution of `FSGNJ.S`, `FSGNJN.S`,
    `FSGNJX.S`, `FMIN.S`, and `FMAX.S` (`FdextRegs.lean:448–475` + `InstsEnd.lean:69928–70013`). -/
noncomputable def sailZfinxExecBinS (rs2 rs1 rd : fregidx) (op : f_bin_op_f_S) : SailM ExecutionResult := do
  let v1 ← sailZfinxReadS rs1
  let v2 ← sailZfinxReadS rs2
  match op with
  | .FSGNJ_S =>
    let (_, e1, m1) := fsplit_S v1; let (s2, _, _) := fsplit_S v2
    sailZfinxWriteS rd (fmake_S s2 e1 m1); pure (.Retire_Success ())
  | .FSGNJN_S =>
    let (_, e1, m1) := fsplit_S v1; let (s2, _, _) := fsplit_S v2
    sailZfinxWriteS rd (fmake_S (1#1 ^^^ s2) e1 m1); pure (.Retire_Success ())
  | .FSGNJX_S =>
    let (s1, e1, m1) := fsplit_S v1; let (s2, _, _) := fsplit_S v2
    sailZfinxWriteS rd (fmake_S (s1 ^^^ s2) e1 m1); pure (.Retire_Success ())
  | .FMIN_S =>
    let (res, fflags) := rv64FpMinMaxSSpec false v1 v2
    accrue_fflags fflags; sailZfinxWriteS rd res; pure (.Retire_Success ())
  | .FMAX_S =>
    let (res, fflags) := rv64FpMinMaxSSpec true v1 v2
    accrue_fflags fflags; sailZfinxWriteS rd res; pure (.Retire_Success ())

/-- Exact full-width `Zfinx`/`Zdinx` (`x`-register) 64-bit IEEE-754 execution of `FSGNJ.D`,
    `FSGNJN.D`, `FSGNJX.D`, `FMIN.D`, and `FMAX.D` (`FdextRegs.lean:455–481` +
    `InstsEnd.lean:70156–70241`). -/
noncomputable def sailZfinxExecBinD (rs2 rs1 rd : fregidx) (op : f_bin_f_op_D) : SailM ExecutionResult := do
  let v1 ← sailZfinxReadD rs1
  let v2 ← sailZfinxReadD rs2
  match op with
  | .FSGNJ_D =>
    let (_, e1, m1) := fsplit_D v1; let (s2, _, _) := fsplit_D v2
    sailZfinxWriteD rd (fmake_D s2 e1 m1); pure (.Retire_Success ())
  | .FSGNJN_D =>
    let (_, e1, m1) := fsplit_D v1; let (s2, _, _) := fsplit_D v2
    sailZfinxWriteD rd (fmake_D (1#1 ^^^ s2) e1 m1); pure (.Retire_Success ())
  | .FSGNJX_D =>
    let (s1, e1, m1) := fsplit_D v1; let (s2, _, _) := fsplit_D v2
    sailZfinxWriteD rd (fmake_D (s1 ^^^ s2) e1 m1); pure (.Retire_Success ())
  | .FMIN_D =>
    let (res, fflags) := rv64FpMinMaxDSpec false v1 v2
    accrue_fflags fflags; sailZfinxWriteD rd res; pure (.Retire_Success ())
  | .FMAX_D =>
    let (res, fflags) := rv64FpMinMaxDSpec true v1 v2
    accrue_fflags fflags; sailZfinxWriteD rd res; pure (.Retire_Success ())

/-- Theorem 9 (Section 16): Dead-branch platform axiom justification for `Lean_RV64D`.
    Proves that on all bridged RV64 architectural extensions (`Ext_M`, `Ext_A`, `Ext_F`, `Ext_D`,
    `Ext_B`, `Ext_S`, `Ext_U`, `Ext_Zicsr`, `Ext_Zca`, `Ext_Zcb`, `Ext_Zcd`, `Ext_Zcf`, `Ext_C`,
    `Ext_Zicfilp`, `Ext_Zfinx`, `Ext_Zdinx`, `Ext_Sv39`, `Ext_Sv48`, `Ext_Svadu`, `Ext_Svnapot`),
    `hartSupports` reduces to concrete `Bool` constants without evaluating the experimental-extension
    axiom `sys_enable_experimental_extensions` (which lives only in `.Ext_Zibi` / `.Ext_Zvabd`), and
    that across standard high physical RAM (`0x80000000 ≤ paddr.toNat`, `htif_tohost_base = none`)
    `within_mmio_readable`, `within_mmio_writable`, `mmio_read`, and `mmio_write` never enter the
    HTIF branch that references `plat_term_write`. -/
theorem rv64DeadBranchPlatformAxiomsUnreached_bisim_sail
    (paddr : BitVec 64) (width : Nat) (data : BitVec (8 * width))
    (hlo : 0x80000000 ≤ paddr.toNat)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hhtif : s.regs.get? .htif_tohost_base = some none) :
    hartSupports .Ext_M = true ∧
    hartSupports .Ext_A = true ∧
    hartSupports .Ext_F = true ∧
    hartSupports .Ext_D = true ∧
    hartSupports .Ext_B = true ∧
    hartSupports .Ext_S = true ∧
    hartSupports .Ext_U = true ∧
    hartSupports .Ext_Zicsr = true ∧
    hartSupports .Ext_Zca = true ∧
    hartSupports .Ext_Zcb = true ∧
    hartSupports .Ext_Zcd = true ∧
    hartSupports .Ext_Zcf = false ∧
    hartSupports .Ext_C = true ∧
    hartSupports .Ext_Zicfilp = true ∧
    hartSupports .Ext_Zfinx = false ∧
    hartSupports .Ext_Zdinx = false ∧
    hartSupports .Ext_Sv39 = true ∧
    hartSupports .Ext_Sv48 = true ∧
    hartSupports .Ext_Svadu = true ∧
    hartSupports .Ext_Svnapot = true ∧
    (within_mmio_readable (.Physaddr paddr) width).run s = .ok false s ∧
    (within_mmio_writable (.Physaddr paddr) width).run s = .ok false s ∧
    (mmio_read (.Load .Data) (.Physaddr paddr) width).run s =
      .ok (.Err (.Physaddr paddr, .E_Load_Access_Fault ())) s ∧
    (mmio_write (.Physaddr paddr) width data).run s =
      .ok (.Err (.Physaddr paddr, .E_SAMO_Access_Fault ())) s := by
  obtain ⟨hclint, hsig, hhtif_w, hmr, hmw⟩ := within_mmio_high_ram_width_false paddr width hlo s hhtif
  have hmread : (mmio_read (.Load .Data) (.Physaddr paddr) width).run s =
      .ok (.Err (.Physaddr paddr, .E_Load_Access_Fault ())) s := by
    unfold mmio_read within_htif_readable accessFaultFromAccessType
    rw [run_bind_ok _ _ _ _ _ hclint, if_neg Bool.false_ne_true,
        run_bind_ok _ _ _ _ _ hsig, if_neg Bool.false_ne_true,
        run_bind_ok _ _ _ _ _ hhtif_w, if_neg Bool.false_ne_true]; rfl
  have hmwrite : (mmio_write (.Physaddr paddr) width data).run s =
      .ok (.Err (.Physaddr paddr, .E_SAMO_Access_Fault ())) s := by
    unfold mmio_write
    rw [run_bind_ok _ _ _ _ _ hclint, if_neg Bool.false_ne_true,
        run_bind_ok _ _ _ _ _ hsig, if_neg Bool.false_ne_true,
        run_bind_ok _ _ _ _ _ hhtif_w, if_neg Bool.false_ne_true]; rfl
  refine ⟨by rw [hartSupports.eq_def], by rw [hartSupports.eq_def], hartSupports_Ext_F,
    hartSupports_Ext_D, by rw [hartSupports.eq_def], hartSupports_Ext_S, hartSupports_Ext_U,
    hartSupports_Ext_Zicsr, hartSupports_Ext_Zca, by rw [hartSupports.eq_def], hartSupports_Ext_Zcd,
    hartSupports_Ext_Zcf, hartSupports_Ext_C, hartSupports_Ext_Zicfilp, hartSupports_Ext_Zfinx,
    by rw [hartSupports.eq_def], by rw [hartSupports.eq_def]; decide,
    by rw [hartSupports.eq_def]; decide, by rw [hartSupports.eq_def],
    by rw [hartSupports.eq_def]; decide, hmr, hmw, hmread, hmwrite⟩

/-- Theorem 10 (Section 16): Full-width 32/64-bit IEEE-754 NaN-boxing (`FLEN = 64`) and lossless
    64-bit `Zfinx`/`Zdinx` `x`-register execution bisimulation (without `flenbits = BitVec 8`
    truncation). Certifies:
    - Exact 64-bit NaN-boxing (`nan_box (n := 64)`) and NaN-unboxing (`nan_unbox (m := 16/32/64)`)
      iff characterization: `nan_unbox (m := 32) x64` preserves `x64[31:0]` when `x64[63:32] =
      allOnes 32` and returns canonical single `QNaN` (`0x7fc0_0000`) otherwise;
    - Lossless 32-bit and full 64-bit `FSGNJ*`, `FMIN*`, `FMAX*`, and `FCLASS*` execution over
      64-bit general-purpose registers (`ra`/`x1` and `sp`/`x2`) with `accrue_fflags` updates. -/
theorem rv64FpFullWidth64NanBoxAndExec_bisim_sail
    (x1Val x2Val mstatusVal : BitVec 64) (fcsrVal : BitVec 32) (isMax : Bool)
    (s : SequentialState RegisterType trivialChoiceSource)
    (hx1 : s.regs.get? .x1 = some x1Val)
    (hx2 : s.regs.get? .x2 = some x2Val)
    (hfcsr : s.regs.get? .fcsr = some fcsrVal)
    (hmstatus : s.regs.get? .mstatus = some mstatusVal) :
    let v1S := Sail.BitVec.extractLsb x1Val 31 0
    let v2S := Sail.BitVec.extractLsb x2Val 31 0
    let (s1S, e1S, m1S) := fsplit_S v1S
    let (s2S, _, _) := fsplit_S v2S
    let (s1D, e1D, m1D) := fsplit_D x1Val
    let (s2D, _, _) := fsplit_D x2Val
    let outS := rv64FpMinMaxSSpec isMax v1S v2S
    let outD := rv64FpMinMaxDSpec isMax x1Val x2Val
    nan_unbox (m := 32) (nan_box (n := 64) v1S) = v1S ∧
    nan_unbox (m := 64) (nan_box (n := 64) x1Val) = x1Val ∧
    (BitVec.extractLsb 63 32 x1Val ≠ BitVec.allOnes 32 →
      nan_unbox (m := 32) x1Val = canonical_NaN_S ()) ∧
    (float_classify v1S).run s = .ok (rv64FloatClassify32Spec v1S) s ∧
    (float_classify x1Val).run s = .ok (rv64FloatClassify64Spec x1Val) s ∧
    (sailZfinxExecBinS (.Fregidx 2#5) (.Fregidx 1#5) (.Fregidx 1#5) .FSGNJ_S).run s =
      .ok (.Retire_Success ()) { s with regs := s.regs.insert .x1 (BitVec.signExtend 64 (fmake_S s2S e1S m1S)) } ∧
    (sailZfinxExecBinS (.Fregidx 2#5) (.Fregidx 1#5) (.Fregidx 1#5) .FSGNJN_S).run s =
      .ok (.Retire_Success ()) { s with regs := s.regs.insert .x1 (BitVec.signExtend 64 (fmake_S (1#1 ^^^ s2S) e1S m1S)) } ∧
    (sailZfinxExecBinS (.Fregidx 2#5) (.Fregidx 1#5) (.Fregidx 1#5) .FSGNJX_S).run s =
      .ok (.Retire_Success ()) { s with regs := s.regs.insert .x1 (BitVec.signExtend 64 (fmake_S (s1S ^^^ s2S) e1S m1S)) } ∧
    (sailZfinxExecBinD (.Fregidx 2#5) (.Fregidx 1#5) (.Fregidx 1#5) .FSGNJ_D).run s =
      .ok (.Retire_Success ()) { s with regs := s.regs.insert .x1 (fmake_D s2D e1D m1D) } ∧
    (sailZfinxExecBinD (.Fregidx 2#5) (.Fregidx 1#5) (.Fregidx 1#5) .FSGNJN_D).run s =
      .ok (.Retire_Success ()) { s with regs := s.regs.insert .x1 (fmake_D (1#1 ^^^ s2D) e1D m1D) } ∧
    (sailZfinxExecBinD (.Fregidx 2#5) (.Fregidx 1#5) (.Fregidx 1#5) .FSGNJX_D).run s =
      .ok (.Retire_Success ()) { s with regs := s.regs.insert .x1 (fmake_D (s1D ^^^ s2D) e1D m1D) } ∧
    (∃ regs,
      (sailZfinxExecBinS (.Fregidx 2#5) (.Fregidx 1#5) (.Fregidx 1#5)
        (if isMax then .FMAX_S else .FMIN_S)).run s =
        .ok (.Retire_Success ()) { s with regs := regs } ∧
      regs.get? .x1 = some (BitVec.signExtend 64 outS.1) ∧
      regs.get? .fcsr = some (rv64AccrueFflagsFcsrSpec fcsrVal outS.2)) ∧
    (∃ regs,
      (sailZfinxExecBinD (.Fregidx 2#5) (.Fregidx 1#5) (.Fregidx 1#5)
        (if isMax then .FMAX_D else .FMIN_D)).run s =
        .ok (.Retire_Success ()) { s with regs := regs } ∧
      regs.get? .x1 = some outD.1 ∧
      regs.get? .fcsr = some (rv64AccrueFflagsFcsrSpec fcsrVal outD.2)) := by
  dsimp only []
  let v1S := Sail.BitVec.extractLsb x1Val 31 0
  let v2S := Sail.BitVec.extractLsb x2Val 31 0
  have hfr1 : fregidx_to_regidx (.Fregidx 1#5) = ra := rfl
  have hfr2 : fregidx_to_regidx (.Fregidx 2#5) = sp := rfl
  have hrS1 : (sailZfinxReadS (.Fregidx 1#5)).run s = .ok v1S s := by
    unfold sailZfinxReadS; rw [hfr1, run_bind_ok _ _ _ _ _ (rX_bits_ra_run x1Val s hx1)]; rfl
  have hrS2 : (sailZfinxReadS (.Fregidx 2#5)).run s = .ok v2S s := by
    unfold sailZfinxReadS; rw [hfr2, run_bind_ok _ _ _ _ _ (rX_bits_sp_run x2Val s hx2)]; rfl
  have hext64 (v : BitVec 64) : Sail.BitVec.extractLsb v 63 0 = v := by
    ext i; simp [Sail.BitVec.extractLsb, BitVec.extractLsb]
  have hrD1 : (sailZfinxReadD (.Fregidx 1#5)).run s = .ok x1Val s := by
    unfold sailZfinxReadD; rw [hfr1, run_bind_ok _ _ _ _ _ (rX_bits_ra_run x1Val s hx1)]
    dsimp only [Pure.pure, EStateM.pure, EStateM.run]; rw [hext64]
  have hrD2 : (sailZfinxReadD (.Fregidx 2#5)).run s = .ok x2Val s := by
    unfold sailZfinxReadD; rw [hfr2, run_bind_ok _ _ _ _ _ (rX_bits_sp_run x2Val s hx2)]
    dsimp only [Pure.pure, EStateM.pure, EStateM.run]; rw [hext64]
  have hwS (res : BitVec 32) (st : SequentialState RegisterType trivialChoiceSource) :
      (sailZfinxWriteS (.Fregidx 1#5) res).run st =
        .ok () { st with regs := st.regs.insert .x1 (BitVec.signExtend 64 res) } := by
    unfold sailZfinxWriteS; rw [hfr1]; exact wX_bits_ra_run (BitVec.signExtend 64 res) st
  have hwD (res : BitVec 64) (st : SequentialState RegisterType trivialChoiceSource) :
      (sailZfinxWriteD (.Fregidx 1#5) res).run st =
        .ok () { st with regs := st.regs.insert .x1 res } := by
    unfold sailZfinxWriteD; rw [hfr1]
    have hse : sign_extend (m := 64) res = res := BitVec.signExtend_eq res
    rw [hse]; exact wX_bits_ra_run res st
  have hboxS : nan_unbox (m := 32) (nan_box (n := 64) v1S) = v1S := by
    rw [nan_box_32_eq, nan_unbox_32_eq]; unfold rv64NanUnboxSSpec rv64NanBoxSSpec
    rw [extractLsb_append_hi_32, extractLsb_append_lo_32]; rfl
  have hboxD : nan_unbox (m := 64) (nan_box (n := 64) x1Val) = x1Val := by
    rw [nan_box_64_eq, nan_unbox_64_eq]
  have hunboxBad (hne : BitVec.extractLsb 63 32 x1Val ≠ BitVec.allOnes 32) :
      nan_unbox (m := 32) x1Val = canonical_NaN_S () := by
    rw [nan_unbox_32_eq]; unfold rv64NanUnboxSSpec
    have hbeq : (BitVec.extractLsb 63 32 x1Val == BitVec.allOnes 32) = false :=
      beq_eq_false_iff_ne.mpr hne
    rw [hbeq]; rfl
  have hmmS : ∃ regs,
      (sailZfinxExecBinS (.Fregidx 2#5) (.Fregidx 1#5) (.Fregidx 1#5)
        (if isMax then .FMAX_S else .FMIN_S)).run s =
        .ok (.Retire_Success ()) { s with regs := regs } ∧
      regs.get? .x1 = some (BitVec.signExtend 64 (rv64FpMinMaxSSpec isMax v1S v2S).1) ∧
      regs.get? .fcsr = some (rv64AccrueFflagsFcsrSpec fcsrVal (rv64FpMinMaxSSpec isMax v1S v2S).2) := by
    let out := rv64FpMinMaxSSpec isMax v1S v2S
    obtain ⟨regsA, hacc, hfcA, _, _⟩ := accrue_fflags_run fcsrVal mstatusVal out.2 s hfcsr hmstatus
    refine ⟨regsA.insert .x1 (BitVec.signExtend 64 out.1), ?_, regs_get?_insert_self _ _ _, ?_⟩
    · cases isMax
      · rw [if_neg Bool.false_ne_true]; unfold sailZfinxExecBinS; dsimp only []
        rw [run_bind_ok _ _ _ _ _ hrS1, run_bind_ok _ _ _ _ _ hrS2,
            run_bind_ok _ _ _ _ _ hacc, run_bind_ok _ _ _ _ _ (hwS out.1 { s with regs := regsA })]; rfl
      · rw [if_pos rfl]; unfold sailZfinxExecBinS; dsimp only []
        rw [run_bind_ok _ _ _ _ _ hrS1, run_bind_ok _ _ _ _ _ hrS2,
            run_bind_ok _ _ _ _ _ hacc, run_bind_ok _ _ _ _ _ (hwS out.1 { s with regs := regsA })]; rfl
    · rw [regs_get?_insert_ne _ _ _ _ rfl]; exact hfcA
  have hmmD : ∃ regs,
      (sailZfinxExecBinD (.Fregidx 2#5) (.Fregidx 1#5) (.Fregidx 1#5)
        (if isMax then .FMAX_D else .FMIN_D)).run s =
        .ok (.Retire_Success ()) { s with regs := regs } ∧
      regs.get? .x1 = some (rv64FpMinMaxDSpec isMax x1Val x2Val).1 ∧
      regs.get? .fcsr = some (rv64AccrueFflagsFcsrSpec fcsrVal (rv64FpMinMaxDSpec isMax x1Val x2Val).2) := by
    let out := rv64FpMinMaxDSpec isMax x1Val x2Val
    obtain ⟨regsA, hacc, hfcA, _, _⟩ := accrue_fflags_run fcsrVal mstatusVal out.2 s hfcsr hmstatus
    refine ⟨regsA.insert .x1 out.1, ?_, regs_get?_insert_self _ _ _, ?_⟩
    · cases isMax
      · rw [if_neg Bool.false_ne_true]; unfold sailZfinxExecBinD; dsimp only []
        rw [run_bind_ok _ _ _ _ _ hrD1, run_bind_ok _ _ _ _ _ hrD2,
            run_bind_ok _ _ _ _ _ hacc, run_bind_ok _ _ _ _ _ (hwD out.1 { s with regs := regsA })]; rfl
      · rw [if_pos rfl]; unfold sailZfinxExecBinD; dsimp only []
        rw [run_bind_ok _ _ _ _ _ hrD1, run_bind_ok _ _ _ _ _ hrD2,
            run_bind_ok _ _ _ _ _ hacc, run_bind_ok _ _ _ _ _ (hwD out.1 { s with regs := regsA })]; rfl
    · rw [regs_get?_insert_ne _ _ _ _ rfl]; exact hfcA
  refine ⟨hboxS, hboxD, hunboxBad, float_classify_32_run v1S s, float_classify_64_run x1Val s,
    ?_, ?_, ?_, ?_, ?_, ?_, hmmS, hmmD⟩
  · unfold sailZfinxExecBinS; dsimp only []
    rw [run_bind_ok _ _ _ _ _ hrS1, run_bind_ok _ _ _ _ _ hrS2, run_bind_ok _ _ _ _ _ (hwS _ s)]; rfl
  · unfold sailZfinxExecBinS; dsimp only []
    rw [run_bind_ok _ _ _ _ _ hrS1, run_bind_ok _ _ _ _ _ hrS2, run_bind_ok _ _ _ _ _ (hwS _ s)]; rfl
  · unfold sailZfinxExecBinS; dsimp only []
    rw [run_bind_ok _ _ _ _ _ hrS1, run_bind_ok _ _ _ _ _ hrS2, run_bind_ok _ _ _ _ _ (hwS _ s)]; rfl
  · unfold sailZfinxExecBinD; dsimp only []
    rw [run_bind_ok _ _ _ _ _ hrD1, run_bind_ok _ _ _ _ _ hrD2, run_bind_ok _ _ _ _ _ (hwD _ s)]; rfl
  · unfold sailZfinxExecBinD; dsimp only []
    rw [run_bind_ok _ _ _ _ _ hrD1, run_bind_ok _ _ _ _ _ hrD2, run_bind_ok _ _ _ _ _ (hwD _ s)]; rfl
  · unfold sailZfinxExecBinD; dsimp only []
    rw [run_bind_ok _ _ _ _ _ hrD1, run_bind_ok _ _ _ _ _ hrD2, run_bind_ok _ _ _ _ _ (hwD _ s)]; rfl

end SailRiscvBridge
