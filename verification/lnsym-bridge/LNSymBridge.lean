import LNSymBridge.Bisimulation
import Lean

/-!
# `LNSymBridge` Root & Kernel Axiom Audit

Verifies at compile time that every Stage 3D bisimulation theorem against upstream
`leanprover/LNSym` depends ONLY on standard Lean foundational axioms (`propext`,
`Classical.choice`, `Quot.sound`) with `0 sorryAx`, `0 Lean.ofReduceBool`, and
`0 Lean.trustCompiler`.
-/

namespace LNSymBridge.Audit

open Lean Elab Command

def bridgedTheorems : List Name :=
  [ ``LNSymBridge.bv128ToQReg_qregToBv128
  , ``LNSymBridge.qregToBv128_bv128ToQReg
  , ``LNSymBridge.qregToBv128_xor
  , ``LNSymBridge.clmul64_eq_polynomial_mult_lo
  , ``LNSymBridge.clmul64Hi_eq_polynomial_mult_hi
  , ``LNSymBridge.qregToBv128_pmull64_eq_polynomial_mult_swap
  , ``LNSymBridge.pmull_op_64_1_eq_polynomial_mult
  , ``LNSymBridge.gf128_butterfly_program_run_28
  , ``LNSymBridge.runArm64_butterflyStepInstrs_bisim_lnsym
  , ``LNSymBridge.exec_pmull_low_bisim
  , ``LNSymBridge.exec_pmull_high_bisim
  , ``LNSymBridge.exec_eor_16b_bisim
  ]

def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

elab "#verify_lnsym_bridge_axioms" : command => do
  let env ← getEnv
  for thm in bridgedTheorems do
    let some _ := env.find? thm
      | throwError "Missing bridged theorem {thm}"
    let axs ← liftCoreM <| Lean.collectAxioms thm
    for ax in axs do
      if !allowedAxioms.contains ax then
        throwError "Forbidden axiom {ax} in theorem {thm} (found {axs})"
  logInfo m!"[lnsym-bridge] Verified {bridgedTheorems.length} bisimulation theorems (zero non-standard axioms)"

#verify_lnsym_bridge_axioms

end LNSymBridge.Audit
