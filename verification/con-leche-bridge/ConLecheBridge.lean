import ConLecheBridge.Soundness
import Lean

namespace ConLecheBridge.Audit

open Lean Elab Command

def bridgedTheorems : List Name :=
  [ ``ConLecheBridge.checkDecls_verified_model_exists
  , ``ConLecheBridge.checkDecls_empty_stream_accepts_with_model
  , ``ConLecheBridge.checkDecls_jobs_accepts_streamEnv_with_model
  , ``ConLecheBridge.checkDecls_verified_no_Empty_constant
  , ``ConLecheBridge.checkDecls_verified_no_False_constant
  , ``ConLecheBridge.checkDecls_verified_no_Empty_theorem_accepted
  , ``ConLecheBridge.checkDecls_thmDecl_const_inhabited_in_model
  , ``ConLecheBridge.model_stored_eq_theorem_denotes_equal
  , ``ConLecheBridge.prepareD_preserves_and_extends_with_prelude
  , ``ConLecheBridge.ndjson_false_declaration_rejected
  , ``ConLecheBridge.checkError_exitCode_in_arena_band
  , ``ConLecheBridge.checkError_exitCode_never_accept
  , ``ConLecheBridge.checkError_exitCode_classification
  , ``ConLecheBridge.verdictG_exit_zero_iff_ok
  , ``ConLecheBridge.sparse_decoder_matches_region_spec
  , ``ConLecheBridge.fillDecl_preserves_index_and_installs_unique_value
  , ``ConLecheBridge.readOleans_closure_merge_and_filled_spec
  , ``ConLecheBridge.readOleans_closure_thm_in_prepared_filled_stream
  , ``ConLecheBridge.checkOleansG_verified_accept_model_exists
  , ``ConLecheBridge.checkMainG_ndjson_verified_exit_zero_model_exists
  , ``ConLecheBridge.checkMainG_oleans_verified_exit_zero_model_exists
  , ``ConLecheBridge.parseArgs_verified_olean_invariants
  , ``ConLecheBridge.parseArgs_turbo_ndjson_invocation
  , ``ConLecheBridge.parseArgs_turbo_olean_invocation
  , ``ConLecheBridge.driver_ndjson_false_never_exits_zero
  , ``ConLecheBridge.driver_oleans_false_never_exits_zero
  , ``ConLecheBridge.driver_ndjson_exit_zero_model_exists
  , ``ConLecheBridge.driver_olean_exit_zero_model_exists
  , ``ConLecheBridge.driver_turbo_ndjson_exit_zero_model_exists
  , ``ConLecheBridge.driver_turbo_olean_exit_zero_model_exists
  , ``ConLecheBridge.driver_turbo_olean_false_never_exits_zero
  ]

def minAuditedTheorems : Nat := 31

theorem bridgedTheorems_nodup : bridgedTheorems.Nodup := by
  decide

theorem bridgedTheorems_length_ge : minAuditedTheorems ≤ bridgedTheorems.length := by
  decide

def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

elab "#verify_con_leche_bridge_axioms" : command => do
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
  logInfo m!"[con-leche-bridge] Verified {bridgedTheorems.length} soundness theorems (zero non-standard axioms)"

#verify_con_leche_bridge_axioms

end ConLecheBridge.Audit
