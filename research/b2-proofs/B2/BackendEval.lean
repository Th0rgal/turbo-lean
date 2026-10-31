import Lean
import FV.Backend.Isel

/-! Proof-producing reduction of the pinned backend's table lookups.

Keep the generated program opaque to `cbv`, which otherwise normalizes every rule
before selecting an entry. The lookup procedures only perform definitional reduction
and return reflexivity proofs; Lean's kernel checks every conversion. Explicit
unfolding equations also avoid equation generation expanding the large table.
-/
namespace B2.BackendEval
set_option maxRecDepth 20000

open Lean Meta Sym.Simp in
private meta def tableLookup : Simproc := fun e => do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then return .rfl
  let r ← Lean.Meta.Sym.share (← withTransparency .all <| reduce e)
  if r == e then return .rfl
  return .step r (← mkEqRefl e)

cbv_simproc ↓ programTermLookup (Isle.Program.term? _ _) := tableLookup
cbv_simproc ↓ programTypeLookup (Isle.Program.type? _ _) := tableLookup
cbv_simproc ↓ programRulesLookup (Isle.Program.rulesOf _ _) := tableLookup
cbv_simproc ↓ programNameLookup (Isle.Program.termByName? _ _) := tableLookup

attribute [cbv_opaque] Isle.Aarch64.program

@[cbv_eval] theorem mkVariant_eval (ty : Isle.TypeId) (name : String) (fs : List Backend.V) :
    Backend.mkVariant ty name fs =
      match Backend.variantIdx ty name with
      | some k => .data ty k fs
      | none => .op .unit := rfl

@[cbv_eval] theorem variantNames_eval (ty : Isle.TypeId) :
    Backend.variantNames ty =
      match Isle.Aarch64.program.type? ty with
      | some ⟨_, _, .enum _ vs, _⟩ => vs.map (·.name)
      | _ => [] := rfl

@[cbv_eval] theorem runTerm_eval (ctx : Backend.Ctx) (term : String)
    (args : List Backend.V) (st : Backend.LState) :
    Backend.runTerm ctx term args st =
      match Isle.Interp.run Isle.Aarch64.program (Backend.sem ctx) {} term args st with
      | .ok r => .ok (r.value, r.state, r.trace)
      | .error e => .error s!"ISLE {term}: {repr e}" := rfl

attribute [cbv_opaque] Backend.externCtor Backend.externExtract

open Lean Meta Sym.Simp in
private meta def unfoldHead : Simproc := fun e => do
  let .const n ls := e.getAppFn | return .rfl
  let info ← getConstInfoDefn n
  let r ← Lean.Meta.Sym.share <|
    (info.value.instantiateLevelParams info.levelParams ls).beta e.getAppArgs
  return .step r (← mkEqRefl e)

cbv_simproc ↓ ctorApply (Backend.externCtor _ _ _ _) := unfoldHead
cbv_simproc ↓ extractApply (Backend.externExtract _ _ _ _) := unfoldHead

theorem opcode_lookup : Backend.opcodeV "Iconst" = .data 151 57 [] := by cbv
#print axioms opcode_lookup
end B2.BackendEval
