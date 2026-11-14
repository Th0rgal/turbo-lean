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
  , ``LNSymBridge.polynomial_mult_comm
  , ``LNSymBridge.polynomial_mult_xor_left
  , ``LNSymBridge.polynomial_mult_xor_right
  , ``LNSymBridge.clmul64_comm
  , ``LNSymBridge.clmul64Hi_comm
  , ``LNSymBridge.mulXMod128_xor
  , ``LNSymBridge.mulXKMod128_128_one
  , ``LNSymBridge.gf2PolyMod128_xor
  , ``LNSymBridge.gf2PolyMod128_low128
  , ``LNSymBridge.qregToBv128_reduceGF128_eq_gf2PolyMod128
  , ``LNSymBridge.karatsubaAssemble256_mul_eq_polynomial_mult
  , ``LNSymBridge.gf2PolyMod128_polynomial_mult_eq_gf128MulSpec
  , ``LNSymBridge.qregToBv128_mulGF128_eq_gf128MulSpec
  , ``LNSymBridge.qreg_xor_comm
  , ``LNSymBridge.qreg_xor_assoc
  , ``LNSymBridge.qreg_xor_zero
  , ``LNSymBridge.qreg_zero_xor
  , ``LNSymBridge.qreg_xor_self
  , ``LNSymBridge.mulGF128_comm
  , ``LNSymBridge.mulGF128_assoc
  , ``LNSymBridge.mulGF128_zero_right
  , ``LNSymBridge.mulGF128_zero_left
  , ``LNSymBridge.mulGF128_one_right
  , ``LNSymBridge.mulGF128_one_left
  , ``LNSymBridge.mulGF128_xor_distrib_left
  , ``LNSymBridge.mulGF128_xor_distrib_right
  , ``LNSymBridge.gf128ButterflyLane_algebraic
  , ``LNSymBridge.gf128ButterflyLane_recover_uv
  , ``LNSymBridge.exec_ext_8_bisim
  , ``LNSymBridge.runArm64_butterflySliceLoop_eq_mapIdx
  , ``LNSymBridge.gf128_butterfly_program_run_28_field_spec
  , ``LNSymBridge.sha512_k_eq_fips
  , ``LNSymBridge.sha512_h0_eq_fips
  , ``LNSymBridge.aes_sbox_eq_fips
  , ``LNSymBridge.aes_sbox_injective
  , ``LNSymBridge.aes_rcon_eq_fips
  , ``LNSymBridge.gcm_r_eq_nist_sp800_38d
  , ``LNSymBridge.gf128_butterfly_twiddle_sha_lane
  ]

theorem bridgedTheorems_nodup : bridgedTheorems.Nodup := by
  decide

def minAuditedTheorems : Nat := 50

theorem bridgedTheorems_length_ge : bridgedTheorems.length >= minAuditedTheorems := by
  decide

def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

elab "#verify_lnsym_bridge_axioms" : command => do
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
  logInfo m!"[lnsym-bridge] Verified {bridgedTheorems.length} bisimulation theorems (zero non-standard axioms)"

#verify_lnsym_bridge_axioms

end LNSymBridge.Audit
