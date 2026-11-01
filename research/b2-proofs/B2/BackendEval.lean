import Lean
import FV.Backend.Proof.IselContract
import B2.IsleFuel

/-! Proof-producing reduction for the pinned backend. Concrete ISLE calls are certified
at smaller fuel, then transferred to the unchanged default execution by `runTerm_of_apply`.
Every cached conversion is checked by Lean's kernel. -/
namespace B2.BackendEval
set_option maxRecDepth 20000

open Lean Meta Sym.Simp in
private meta def tableLookup : Simproc := fun e => do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then return .rfl
  let r ← Lean.Meta.Sym.share (← withTransparency .all <| reduce e)
  if r == e then return .rfl
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then return .rfl
  let name ← mkAuxLemma [] (← mkEq e r) (← mkEqRefl e) (kind? := some `_b2_eval)
  return .step r (mkConst name)

cbv_simproc ↓ programTermLookup (Isle.Program.term? _ _) := tableLookup
cbv_simproc ↓ programTypeLookup (Isle.Program.type? _ _) := tableLookup

attribute [cbv_opaque] Isle.Aarch64.program

open Lean Elab Command in
run_cmd do
  for (n, _) in (← getEnv).constants.toList do
    let name := n.toString
    if name.startsWith "Backend.Proof.program_term_" ||
        name.startsWith "Backend.Proof.program_rulesOf_" ||
        name == "Backend.Proof.program_termByName_lower" ||
        name == "Backend.Proof.program_termByName_lower_branch" then
      elabCommand (← `(attribute [cbv_eval] $(mkIdent n)))



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
  let r ← Lean.Meta.Sym.share (← withTransparency .all <| whnf e)
  if r == e then return .rfl
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then return .rfl
  let name ← mkAuxLemma [] (← mkEq e r) (← mkEqRefl e) (kind? := some `_b2_eval)
  return .step r (mkConst name)

cbv_simproc ↓ normIntApply (Backend.normInt _ _) := unfoldHead
cbv_simproc ↓ ctorApply (Backend.externCtor _ _ _ _) := unfoldHead
cbv_simproc ↓ extractApply (Backend.externExtract _ _ _ _) := unfoldHead

open Backend Isle
attribute [cbv_opaque] Backend.runTerm

open Lean Meta Sym.Simp in
cbv_simproc cbv_eval certifyRunTerm (Backend.runTerm _ _ _ _) := fun e => do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then return .rfl
  let as := e.getAppArgs
  let some term := Lean.Meta.getStringValue? as[1]! | return .rfl
  let htName ← match term with
    | "lower" => pure ``Backend.Proof.program_termByName_lower
    | "lower_branch" => pure ``Backend.Proof.program_termByName_lower_branch
    | _ => return .rfl
  let ht := mkConst htName
  let htType ← inferType ht
  let_expr Eq _ _ rhs := htType | return .rfl
  let_expr Option.some _ t := rhs | return .rfl
  let sem ← mkAppM ``Backend.sem #[as[0]!]
  let cfg := mkApp2 (mkConst ``Isle.Config.mk) (mkConst ``Bool.false) (mkNatLit 1000000)
  let ret ← mkAppM ``Isle.Term.ret #[t]
  let tid ← mkAppM ``Isle.Term.id #[t]
  let call ← mkAppM ``Isle.Interp.applyTerm
    #[mkConst ``Isle.Aarch64.program, sem, cfg, mkNatLit 1024, ret, tid, as[2]!]
  let tr := mkApp (mkConst ``Array.empty [0]) (mkConst ``Nat)
  let state ← mkAppM ``Prod.mk #[as[3]!, tr]
  let low := mkApp call state
  let .step out proof _ _ ← Lean.Meta.Tactic.Cbv.cbvEntry low | return .rfl
  let_expr Except.ok _ _ _ := out | throwError "small ISLE run did not return successfully"
  let final ← mkAppM ``runTerm_of_apply #[ht, proof]
  let finalType ← inferType final
  let_expr Eq _ _ result := finalType | return .rfl
  let name ← mkAuxLemma [] finalType final (kind? := some `_b2_isel)
  return .step (← Lean.Meta.Sym.share result) (mkConst name)

theorem opcode_lookup : Backend.opcodeV "Iconst" = .data 151 57 [] := by cbv
#print axioms opcode_lookup
end B2.BackendEval
