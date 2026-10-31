import B2.CollatzClif
import FV.Backend.InputScope

/-! Structural O6 facts about the real generated Collatz function. -/
namespace B2.CallFree
open Clif

theorem declarations : B2.Smoke.collatz.externs = [] ∧
    B2.Smoke.collatz.sigDecls = [] ∧ B2.Smoke.collatz.globals = [] ∧
    B2.Smoke.collatz.slots = [] :=
  B2.Lowering.lower_declarations _ _ B2.Smoke.collatz_lowered

theorem try_free : ∀ B ∈ B2.Smoke.collatz.blocks, B.term.isTry = false := by
  have h : B2.Smoke.collatz.blocks.all (fun B => !B.term.isTry) = true := by decide +kernel
  intro B hB
  exact Bool.eq_false_iff.mpr (by simpa using List.all_eq_true.mp h B hB)

theorem no_indirect_stmt : ∀ B ∈ B2.Smoke.collatz.blocks, ∀ st ∈ B.body,
    ∀ sig callee args, st.inst ≠ .callIndirect sig callee args := by
  have h : B2.Smoke.collatz.blocks.all (fun B => B.body.all (fun st =>
    match st.inst with | .callIndirect .. => false | _ => true)) = true := by decide +kernel
  intro B hB st hst sig callee args hi
  have hst' := List.all_eq_true.mp (List.all_eq_true.mp h B hB) st hst
  rw [hi] at hst'
  cases hst'

theorem no_indirect_sigs : Backend.indSigs B2.Smoke.collatz = [] := by decide +kernel

theorem no_tls : Backend.hasTls B2.Smoke.collatz = false := by decide +kernel

#print axioms try_free
#print axioms no_indirect_stmt
#print axioms no_indirect_sigs
#print axioms no_tls
end B2.CallFree
