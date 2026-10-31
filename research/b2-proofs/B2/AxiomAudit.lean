import Lean
import B2.Lowering
import B2.Division
import B2.Kernel
import B2.Smoke
import B2.CollatzSource
import B2.CollatzClif
import B2.RunSafety

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
        ``B2.RunSafety.of_returned] do
      let axs ← Lean.collectAxioms name
      let rejected := axs.filter fun a => !allowed.contains a
      unless rejected.isEmpty do
        throwError "B2 axiom audit rejected {name}: {rejected}"
      logInfo m!"B2 axiom audit: {name}: {axs}"
