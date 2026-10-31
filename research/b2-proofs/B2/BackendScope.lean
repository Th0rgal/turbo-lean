import B2.BackendLower
import B2.CallFree
import FV.E2E.Statement
import FV.Backend.Proof.LowerDecide
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

/-! Exact input predicates consumed by clifv's final backend theorem. -/
namespace B2.BackendContracts
open Backend Backend.Proof Backend.Proof.Driver E2E
attribute [local irreducible] B2.Smoke.collatz
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option cbv.maxSteps 1000000
set_option Elab.async false

/-- Keep lookup conditions Boolean while preserving the actual HashMap operation. -/
theorem lookup_insertIfNew {α β : Type} [BEq α] [Hashable α] [EquivBEq α]
    [LawfulHashable α] (m : Std.HashMap α β) (k a : α) (v : β) :
    (m.insertIfNew k v).get? a =
      if k == a && !m.contains k then some v else m.get? a := by
  change (m.insertIfNew k v)[a]? = _
  rw [Std.HashMap.getElem?_insertIfNew]
  simp [Bool.and_eq_true]

theorem lookup_method_empty {α β : Type} [BEq α] [Hashable α]
    (a : α) (capacity : Nat) :
    (Std.HashMap.emptyWithCapacity capacity : Std.HashMap α β).get? a = none := by
  exact Std.HashMap.getElem?_emptyWithCapacity

attribute [local cbv_opaque] Std.HashMap.get?
attribute [-cbv_eval] Std.HashSet.ofList_eq_insertMany_empty
attribute [local cbv_opaque] Std.HashMap.insertIfNew Std.HashSet.ofList
attribute [local cbv_eval] lookup_insertIfNew lookup_method_empty Std.HashMap.contains_insertIfNew
  Std.HashSet.contains_ofList


/-- Normalize folded containers before observing them. -/
open Lean Meta Sym.Simp in
cbv_simproc ↓ normalizeLookup (_) := fun e => do
  let some n := e.getAppFn.constName? | return .rfl
  unless n == ``Std.HashMap.get? || n == ``Std.HashMap.contains ||
      n == ``Std.HashSet.contains do return .rfl
  return ← simpAppArgRange e 0 e.getAppNumArgs

theorem subset (p : Clif.Program) : InSubset p B2.Smoke.collatz := by
  refine ⟨B2.Lowering.lower_in_subsetE _ _ B2.Smoke.collatz_lowered, ?_, ?_, ?_, ?_⟩
  · intro b hb st hst fn args hi e he
    simp [Clif.Function.extern?, B2.CallFree.declarations.1] at he
  · intro b hb fn args et hi e he
    simp [Clif.Function.extern?, B2.CallFree.declarations.1] at he
  · constructor
    · rw [B2.CollatzClif.generated_sig]
      decide
    · simp [B2.CallFree.declarations.1]
  · simp [B2.CallFree.no_indirect_sigs]

theorem dominated : dominatedB B2.Smoke.collatz = true := by
  rw [← B2.Artifacts.input_eq]
  cbv

theorem scope : lowerScopeB B2.Smoke.collatz = true := by
  rw [← B2.Artifacts.input_eq]
  decide +kernel

attribute [cbv_eval] Std.HashSet.ofList_eq_insertMany_empty

#print axioms lookup_insertIfNew
#print axioms lookup_method_empty
#print axioms subset
#print axioms dominated
#print axioms scope
end B2.BackendContracts
