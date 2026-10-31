import B2.BackendEval
import FV.Backend.Regalloc
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

/-! Unfold the pinned spill allocator's definitions directly before cbv equation
 generation. Lean's array-pattern equation generator rejects the generated singleton
 matcher. Each step supplies reflexivity, checked against the original definition. -/
namespace B2.AllocationEval
attribute [cbv_opaque] Std.HashMap.size
attribute [cbv_eval] Std.HashMap.size_emptyWithCapacity
@[cbv_eval] theorem size_insert_bool {α β : Type} [BEq α] [Hashable α] [EquivBEq α]
    [LawfulHashable α] (m : Std.HashMap α β) (k : α) (v : β) :
    (m.insert k v).size = if m.contains k then m.size else m.size + 1 := by
  simpa only [Std.HashMap.contains_iff_mem] using (Std.HashMap.size_insert (m := m) (k := k) (v := v))

open Lean Meta Sym.Simp in
cbv_simproc ↓ spillDefinition (_) := fun e => do
  let .const n _ := e.getAppFn | return .rfl
  let name := n.toString
  unless name.startsWith "Backend.spillEntryStores" ||
      name.startsWith "Backend.spillAlloc" do return .rfl
  let unfold : Simproc := fun e => do
    let .const n levels := e.getAppFn | return .rfl
    let .defnInfo d ← getConstInfo n | return .rfl
    let r := mkAppN (d.value.instantiateLevelParams d.levelParams levels) e.getAppArgs |>.headBeta
    if r == e then return .rfl
    return .step (← Lean.Meta.Sym.share r) (← mkEqRefl e)
  return ← ((simpAppArgRange · 0 e.getAppNumArgs) >> unfold) e

end B2.AllocationEval
