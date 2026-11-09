import SailRiscvBridge.Bisimulation
import Lean

/-!
# `SailRiscvBridge` Root & Kernel Axiom Audit

Verifies at compile time that every Stage 3E / Milestone `M5` RV64 bisimulation theorem
against upstream `opencompl/sail-riscv-lean` depends ONLY on standard Lean foundational
axioms (`propext`, `Classical.choice`, `Quot.sound`) with `0 sorryAx`,
`0 Lean.ofReduceBool`, `0 Lean.trustCompiler`, and `0` upstream `RiscvExtras` axioms.
-/

namespace SailRiscvBridge.Audit

open Lean Elab Command

def bridgedTheorems : List Name :=
  [ ``SailRiscvBridge.rv64_xlen_params
  , ``SailRiscvBridge.rX_bits_zreg
  , ``SailRiscvBridge.wX_bits_zreg_noop
  , ``SailRiscvBridge.wX_then_rX_x1
  , ``SailRiscvBridge.to_bits_truncate_eq_ofInt
  , ``SailRiscvBridge.riscvDivU64Spec_bisim_sail
  , ``SailRiscvBridge.riscvRemU64Spec_bisim_sail
  , ``SailRiscvBridge.riscvDivRemU64Spec_euclidean
  , ``SailRiscvBridge.mult_to_bits_half_low_unsigned_eq_mul
  , ``SailRiscvBridge.mult_to_bits_half_high_unsigned_toNat
  , ``SailRiscvBridge.encdec_mul_op_roundtrip
  , ``SailRiscvBridge.clmul64_eq_sail_carryless_mul_lo
  , ``SailRiscvBridge.clmul64Hi_eq_sail_carryless_mul_hi
  , ``SailRiscvBridge.clmul64_pair_eq_sail_carryless_mul
  ]

def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

elab "#verify_sail_riscv_bridge_axioms" : command => do
  let env ← getEnv
  if bridgedTheorems.length < 10 then
    throwError "Expected at least 10 bridged theorems, found {bridgedTheorems.length}"
  for thm in bridgedTheorems do
    let some _ := env.find? thm
      | throwError "Missing bridged theorem {thm}"
    let axs ← liftCoreM <| Lean.collectAxioms thm
    for ax in axs do
      if !allowedAxioms.contains ax then
        throwError "Forbidden axiom {ax} in theorem {thm} (found {axs})"
  logInfo m!"[sail-riscv-bridge] Verified {bridgedTheorems.length} RV64 bisimulation theorems (zero non-standard axioms)"

#verify_sail_riscv_bridge_axioms

end SailRiscvBridge.Audit
