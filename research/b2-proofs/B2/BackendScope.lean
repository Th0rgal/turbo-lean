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

/-- Boolean conditions avoid repeatedly transporting the lookup's decidable instance. -/
theorem lookup_insertIfNew {α β : Type} [BEq α] [Hashable α] [EquivBEq α]
    [LawfulHashable α] (m : Std.HashMap α β) (k a : α) (v : β) :
    (m.insertIfNew k v)[a]? =
      if k == a && !m.contains k then some v else m[a]? := by
  rw [Std.HashMap.getElem?_insertIfNew]
  simp [Bool.and_eq_true]

attribute [local cbv_opaque] Std.HashMap.insertIfNew Std.HashSet.ofList
attribute [local cbv_eval] lookup_insertIfNew Std.HashMap.contains_insertIfNew
  Std.HashSet.contains_ofList

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

#print axioms lookup_insertIfNew
#print axioms subset
#print axioms dominated
#print axioms scope
end B2.BackendContracts
