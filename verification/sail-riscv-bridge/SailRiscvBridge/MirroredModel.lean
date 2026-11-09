/-!
# Stage 3E / Milestone `M5` Mirrored `TurboLean` & `LeanNative` RV64 Scalar/Zbc Model

This module contains exact, byte-synchronized slices of:
1. `TurboLean.PolicyGates.riscvDivU64Spec` and `TurboLean.PolicyGates.riscvRemU64Spec`
   (`lean/TurboLean/PolicyGates.lean`)
2. `LeanNative.IR.clmul64` and `LeanNative.IR.clmul64Hi`
   (`lean/LeanNative/IR/Types.lean`)

Enforced byte-for-byte against the root `turbo-lean` repository by
`scripts/check_sail_riscv_bridge_sync.py`.
-/

namespace TurboLean.PolicyGates

-- BEGIN MIRRORED SLICE: lean/TurboLean/PolicyGates.lean
@[inline]
def riscvDivU64Spec (lhs rhs : UInt64) : UInt64 := if rhs == 0 then 0xffffffffffffffff else lhs / rhs

@[inline]
def riscvRemU64Spec (lhs rhs : UInt64) : UInt64 := if rhs == 0 then lhs else lhs % rhs
-- END MIRRORED SLICE: lean/TurboLean/PolicyGates.lean

end TurboLean.PolicyGates

namespace LeanNative.IR

-- BEGIN MIRRORED SLICE: lean/LeanNative/IR/Types.lean
/-- Carryless product, low 64 bits. One definition for Eval, LLVM, Metal and PTX. -/
def clmul64 (a b : UInt64) : UInt64 :=
  let rec go (i : Nat) (acc : UInt64) : UInt64 :=
    if _ : i < 64 then let iu := i.toUInt64; go (i + 1) (if ((b >>> iu) &&& 1) == 1 then acc ^^^ (a <<< iu) else acc) else acc
  go 0 0
/-- Carryless product, high 64 bits of the 128-bit polynomial product. -/
def clmul64Hi (a b : UInt64) : UInt64 :=
  let rec go (i : Nat) (acc : UInt64) : UInt64 :=
    if _ : i < 64 then let iu := i.toUInt64; go (i + 1) (if ((b >>> iu) &&& 1) == 1 then acc ^^^ (a >>> (64 - iu)) else acc) else acc
  go 1 0
-- END MIRRORED SLICE: lean/LeanNative/IR/Types.lean

end LeanNative.IR
