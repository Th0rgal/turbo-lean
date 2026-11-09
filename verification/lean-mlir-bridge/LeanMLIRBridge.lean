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
  , ``LeanMLIRBridge.stepInstr_srem_bisim_of_non_ub
  , ``LeanMLIRBridge.sdivOverflow_i1_iff
  , ``LeanMLIRBridge.stepInstr_sdiv_srem_i1_allOnes_ub
  , ``LeanMLIRBridge.stepInstr_sdiv_ub_or_bisim
  , ``LeanMLIRBridge.stepInstr_srem_ub_or_bisim
  , ``LeanMLIRBridge.stepInstr_add_eq_op_denote
  , ``LeanMLIRBridge.stepInstr_sub_eq_op_denote
  , ``LeanMLIRBridge.stepInstr_mul_eq_op_denote
  , ``LeanMLIRBridge.stepInstr_and_eq_op_denote
  , ``LeanMLIRBridge.stepInstr_or_eq_op_denote
  , ``LeanMLIRBridge.stepInstr_xor_eq_op_denote
  , ``LeanMLIRBridge.stepInstr_shl_eq_op_denote
  , ``LeanMLIRBridge.stepInstr_lshr_eq_op_denote
  , ``LeanMLIRBridge.stepInstr_ashr_eq_op_denote
  , ``LeanMLIRBridge.stepInstr_icmp_eq_op_denote
  , ``LeanMLIRBridge.stepInstr_select_eq_op_denote
  , ``LeanMLIRBridge.stepInstr_zext_eq_op_denote
  , ``LeanMLIRBridge.stepInstr_sext_eq_op_denote
  , ``LeanMLIRBridge.stepInstr_trunc_eq_op_denote
  , ``LeanMLIRBridge.stepInstr_udiv_eq_op_denote_of_nonzero
  , ``LeanMLIRBridge.stepInstr_urem_eq_op_denote_of_nonzero
  , ``LeanMLIRBridge.stepInstr_sdiv_eq_op_denote_of_non_ub
  , ``LeanMLIRBridge.stepInstr_srem_eq_op_denote_of_non_ub
  , ``LeanMLIRBridge.execInstrs_of_straightLineBisim
  , ``LeanMLIRBridge.StraightLineBisim.append
  , ``LeanMLIRBridge.execInstrs_append_of_straightLineBisim
  , ``LeanMLIRBridge.evalOperand_reg_bindReg_same
  , ``LeanMLIRBridge.evalOperand_reg_bindReg_ne
  , ``LeanMLIRBridge.evalTypedOperand_int_reg
  , ``LeanMLIRBridge.RegValuationAgrees.bind
  , ``LeanMLIRBridge.stepInstr_pure_frame
  , ``LeanMLIRBridge.StraightLineBisim.pure_frame
  , ``LeanMLIRBridge.execInstrs_straightLineFusedPipeline_eq_op_denote
  ]

def minAuditedTheorems : Nat := 63

theorem bridgedTheorems_nodup : bridgedTheorems.Nodup := by
  decide

theorem bridgedTheorems_length_ge : minAuditedTheorems ≤ bridgedTheorems.length := by
  decide

def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

elab "#verify_lean_mlir_bridge_axioms" : command => do
  let env ← getEnv
  if bridgedTheorems.length < minAuditedTheorems then
    throwError "Expected at least {minAuditedTheorems} bridged theorems, found {bridgedTheorems.length}"
  let mut seen : List Name := []
  for thm in bridgedTheorems do
    if seen.contains thm then
      throwError "Duplicate bridged theorem {thm} in bridgedTheorems"
    seen := thm :: seen
    let some _ := env.find? thm
      | throwError "Missing bridged theorem {thm}"
    let axs ← liftCoreM <| Lean.collectAxioms thm
    for ax in axs do
      if !allowedAxioms.contains ax then
        throwError "Forbidden axiom {ax} in theorem {thm} (found {axs})"
  logInfo m!"[lean-mlir-bridge] Verified {bridgedTheorems.length} bisimulation theorems (zero non-standard axioms)"

#verify_lean_mlir_bridge_axioms

end LeanMLIRBridge.Audit
