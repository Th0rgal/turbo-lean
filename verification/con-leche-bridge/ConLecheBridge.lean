import ConLecheBridge.Soundness
import Lean

namespace ConLecheBridge.Audit

open Lean Elab Command

def bridgedTheorems : List Name :=
  [ ``ConLecheBridge.checkDecls_verified_model_exists
  , ``ConLecheBridge.ndjson_false_declaration_rejected
  , ``ConLecheBridge.driver_ndjson_false_never_exits_zero
  , ``ConLecheBridge.driver_oleans_false_never_exits_zero
  , ``ConLecheBridge.driver_ndjson_exit_zero_model_exists
  , ``ConLecheBridge.driver_olean_exit_zero_model_exists
  , ``ConLecheBridge.checkError_exitCode_in_arena_band
  , ``ConLecheBridge.checkError_exitCode_never_accept
  , ``ConLecheBridge.parseArgs_verified_olean_invariants
  ]

def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

elab "#verify_con_leche_bridge_axioms" : command => do
  let env ← getEnv
  for thm in bridgedTheorems do
    let some _ := env.find? thm
      | throwError "Missing bridged theorem {thm}"
    let axs ← liftCoreM <| Lean.collectAxioms thm
    for ax in axs do
      if !allowedAxioms.contains ax then
        throwError "Forbidden axiom {ax} in theorem {thm} (found {axs})"
  logInfo m!"[con-leche-bridge] Verified {bridgedTheorems.length} soundness theorems (zero non-standard axioms)"

#verify_con_leche_bridge_axioms

end ConLecheBridge.Audit
