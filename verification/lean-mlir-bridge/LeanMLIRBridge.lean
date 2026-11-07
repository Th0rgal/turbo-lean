import LeanMLIRBridge.Bisimulation
import Lean

/-!
# `LeanMLIRBridge` Root & Kernel Axiom Audit

Verifies at compile time that every Stage 2C bisimulation theorem depends ONLY on standard Lean
foundational axioms (`propext`, `Classical.choice`, `Quot.sound`) with `0 sorryAx`,
`0 Lean.ofReduceBool`, and `0 Lean.trustCompiler`.
-/

namespace LeanMLIRBridge.Audit

open Lean Elab Command

def bridgedTheorems : List Name :=
  [ ``LeanMLIRBridge.ofLLVMVal?_toLLVMVal
  , ``LeanMLIRBridge.bvSigned_eq_toInt
  , ``LeanMLIRBridge.addOverflowNSW_eq_saddOverflow
  , ``LeanMLIRBridge.subOverflowNSW_eq_ssubOverflow
  , ``LeanMLIRBridge.mulOverflowNSW_eq_smulOverflow
  , ``LeanMLIRBridge.addOverflowNUW_eq_uaddOverflow
  , ``LeanMLIRBridge.subOverflowNUW_eq_usubOverflow
  , ``LeanMLIRBridge.mulOverflowNUW_eq_umulOverflow
  , ``LeanMLIRBridge.icmpEval_eq_mlir
  , ``LeanMLIRBridge.shlOverflowNSW_eq_mlir
  , ``LeanMLIRBridge.shiftedOut_iff_ushift_roundtrip
  , ``LeanMLIRBridge.bvSDiv_eq_sdiv
  , ``LeanMLIRBridge.bvSRem_eq_srem
  , ``LeanMLIRBridge.stepInstr_add_bisim
  , ``LeanMLIRBridge.stepInstr_sub_bisim
  , ``LeanMLIRBridge.stepInstr_mul_bisim
  , ``LeanMLIRBridge.stepInstr_and_bisim
  , ``LeanMLIRBridge.stepInstr_or_bisim
  , ``LeanMLIRBridge.stepInstr_xor_bisim
  , ``LeanMLIRBridge.stepInstr_shl_bisim
  , ``LeanMLIRBridge.stepInstr_lshr_bisim
  , ``LeanMLIRBridge.stepInstr_ashr_bisim
  , ``LeanMLIRBridge.stepInstr_icmp_bisim
  , ``LeanMLIRBridge.stepInstr_select_bisim
  , ``LeanMLIRBridge.stepInstr_zext_bisim
  , ``LeanMLIRBridge.stepInstr_sext_bisim
  , ``LeanMLIRBridge.stepInstr_trunc_bisim
  , ``LeanMLIRBridge.stepInstr_udiv_ub_or_bisim
  , ``LeanMLIRBridge.stepInstr_urem_ub_or_bisim
  , ``LeanMLIRBridge.stepInstr_sdiv_bisim_of_non_ub
  , ``LeanMLIRBridge.stepInstr_add_eq_op_denote
  , ``LeanMLIRBridge.stepInstr_icmp_eq_op_denote
  , ``LeanMLIRBridge.stepInstr_select_eq_op_denote
  , ``LeanMLIRBridge.execInstrs_of_straightLineBisim
  ]

def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

elab "#verify_lean_mlir_bridge_axioms" : command => do
  let env ← getEnv
  for thm in bridgedTheorems do
    let some _ := env.find? thm
      | throwError "Missing bridged theorem {thm}"
    let axs ← liftCoreM <| Lean.collectAxioms thm
    for ax in axs do
      if !allowedAxioms.contains ax then
        throwError "Forbidden axiom {ax} in theorem {thm} (found {axs})"
  logInfo m!"[lean-mlir-bridge] Verified {bridgedTheorems.length} bisimulation theorems (zero non-standard axioms)"

#verify_lean_mlir_bridge_axioms

end LeanMLIRBridge.Audit
