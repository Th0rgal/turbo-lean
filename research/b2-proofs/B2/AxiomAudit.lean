import Lean
import B2.Lowering
import B2.Division
import B2.Kernel
import B2.Smoke
import B2.CollatzSource
import B2.CollatzClif
import B2.RunSafety
import B2.CallFree
import B2.BackendLower
import B2.BackendAlloc
import B2.Artifacts
import B2.BackendEntry
import B2.BackendScope
import B2.BackendContracts

/-! A build-failing transitive axiom audit of the results claimed by B2-status.md.
Historical draft statements are intentionally outside the active root. -/
open Lean Elab Command

run_cmd do
  liftCoreM do
    let allowed := [`propext, `Quot.sound, `Classical.choice]
    for name in [``B2.Lowering.lower_in_subsetE, ``B2.Lowering.lower_sig,
        ``B2.Lowering.lower_declarations, ``B2.Division.total_div_agrees,
        ``B2.Division.total_mod_agrees, ``B2.Division.safe_div_executes,
        ``B2.Kernel.collatz_in_F, ``B2.Kernel.collatz_eval_3_5,
        ``B2.Smoke.collatz_lowered, ``B2.Smoke.collatz_3_5,
        ``B2.Smoke.collatz_zero_steps, ``B2.Smoke.div_zero, ``B2.Smoke.mod_zero,
        ``B2.Smoke.div_nonzero, ``B2.Smoke.mod_nonzero, ``B2.Smoke.nested_shadowing,
        ``B2.Smoke.bool_not_true, ``B2.Smoke.rejects_mixed,
        ``B2.CollatzSource.collatz_eval, ``B2.CollatzClif.generated_blocks,
        ``B2.CollatzClif.generated_sig, ``B2.CollatzClif.div_two,
        ``B2.CollatzClif.after_iteration_live, ``B2.CollatzClif.header_test,
        ``B2.CollatzClif.header_branch, ``B2.CollatzClif.header_taken,
        ``B2.CollatzClif.body_backedge, ``B2.CollatzClif.iteration,
        ``B2.CollatzClif.header_finished, ``B2.CollatzClif.loop_returns,
        ``B2.CollatzClif.entry_advance, ``B2.CollatzClif.from_entry,
        ``B2.CollatzClif.generated_entry, ``B2.CollatzClif.generated_slots,
        ``B2.CollatzClif.enter_function, ``B2.CollatzClif.run_with,
        ``B2.CollatzClif.source_simulation, ``B2.RunSafety.collatz_prefix,
        ``B2.CollatzClif.slotless_leave, ``B2.RunSafety.collatz_run_prefix,
        ``B2.CallFree.declarations, ``B2.CallFree.try_free, ``B2.CallFree.no_indirect_stmt,
        ``B2.CallFree.no_indirect_sigs, ``B2.CallFree.no_tls,
        ``B2.RunSafety.of_returned, ``B2.Artifacts.input_eq,
        ``B2.Artifacts.verifiable, ``B2.Artifacts.lower,
        ``B2.BackendEval.runTerm_of_apply,
        ``B2.Artifacts.prepared, ``B2.Artifacts.spill_alloc,
        ``B2.Artifacts.allocation_checked, ``B2.Artifacts.allocated,
        ``B2.Artifacts.emitted, ``B2.Artifacts.laid_out,
        ``B2.BackendEntry.xholds_cv_iff, ``B2.BackendEntry.entry_eq, ``B2.BackendEntry.returns,
        ``B2.BackendEntry.reachable_step_safe, ``B2.BackendEntry.traps_explicit,
        ``B2.BackendContracts.lookup_insertIfNew, ``B2.BackendContracts.lookup_method_empty,
        ``B2.BackendContracts.subset, ``B2.BackendContracts.dominated,
        ``B2.BackendContracts.scope, ``B2.BackendContracts.prepared_call_free,
        ``B2.BackendContracts.no_call_site, ``B2.BackendContracts.callee_ok,
        ``B2.BackendContracts.try_contract, ``B2.BackendContracts.tls_contract,
        ``B2.BackendContracts.extern_contract, ``B2.BackendContracts.indirect_contract] do
      let axs ← Lean.collectAxioms name
      let rejected := axs.filter fun a => !allowed.contains a
      unless rejected.isEmpty do
        throwError "B2 axiom audit rejected {name}: {rejected}"
      logInfo m!"B2 axiom audit: {name}: {axs}"
