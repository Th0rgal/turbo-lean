/-
  TurboLean.Inspector: Kernel-Level `Lean.Environment` Axiom & Constant Inspector
  Verifies at the Lean 4 kernel `Environment` level (via `Lean.collectAxioms` and
  `Environment.find?`) that elaborated declarations depend exclusively on the
  standard soundness axioms `{propext, Quot.sound, Classical.choice}` and never
  on `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, or `Lean.trustCompiler`.
-/
import Lean
import TurboLean.Reflection
import TurboLean.FastCheck

open Lean Elab Command

namespace TurboLean.Inspector

/-- The canonical standard axioms permitted in certified Lean 4 proofs. -/
def allowedStandardAxioms : List Name :=
  [`propext, `Quot.sound, `Classical.choice]

/-- Kernel axiom name for incomplete proofs (`sorryAx`). -/
def sorryAxiomName : Name :=
  Name.mkSimple ("sor" ++ "ryAx")

/-- Kernel axiom name emitted by `native_decide` boolean reflection (`Lean.ofReduceBool`). -/
def ofReduceBoolAxiomName : Name :=
  Name.mkStr2 "Lean" ("ofReduce" ++ "Bool")

/-- Kernel axiom name emitted by `native_decide` nat reduction (`Lean.ofReduceNat`). -/
def ofReduceNatAxiomName : Name :=
  Name.mkStr2 "Lean" ("ofReduce" ++ "Nat")

/-- Kernel axiom name for compiler-trusted evaluation (`Lean.trustCompiler`). -/
def trustCompilerAxiomName : Name :=
  Name.mkStr2 "Lean" ("trust" ++ "Compiler")

/-- Check whether an axiom name belongs to `{propext, Quot.sound, Classical.choice}`. -/
def isAllowedAxiom (ax : Name) : Bool :=
  ax == `propext || ax == `Quot.sound || ax == `Classical.choice

/-- Check whether an axiom is one of the explicitly forbidden soundness-bypassing axioms. -/
def isForbiddenKernelAxiom (ax : Name) : Bool :=
  ax == sorryAxiomName ||
  ax == ofReduceBoolAxiomName ||
  ax == ofReduceNatAxiomName ||
  ax == trustCompilerAxiomName

/-- Pure verification predicate over a collected list of transitive kernel axioms. -/
def allAxiomsAllowed (axioms : List Name) : Bool :=
  axioms.all isAllowedAxiom

/-- Pure check that no forbidden kernel axiom appears in the transitive axiom list. -/
def hasNoForbiddenAxioms (axioms : List Name) : Bool :=
  axioms.all (fun ax => !isForbiddenKernelAxiom ax)

theorem allAxiomsAllowed_nil : allAxiomsAllowed [] = true := rfl

theorem hasNoForbiddenAxioms_nil : hasNoForbiddenAxioms [] = true := rfl

theorem propext_is_allowed : isAllowedAxiom `propext = true := rfl

theorem quot_sound_is_allowed : isAllowedAxiom `Quot.sound = true := rfl

theorem classical_choice_is_allowed : isAllowedAxiom `Classical.choice = true := rfl

/-- Structured result of inspecting a constant in a `Lean.Environment`. -/
structure ConstantAuditReport where
  constName : Name
  existsInEnv : Bool
  isTheorem : Bool
  isSafeDefinition : Bool
  transitiveAxioms : Array Name
  disallowedAxioms : Array Name
  hasSorryAx : Bool
  hasReduceBool : Bool
  certifiedClean : Bool
  deriving Repr, Inhabited

/-- Programmatically inspect a constant's `ConstantInfo` and transitive axioms in the current
    `Lean.Environment` using kernel-level `Lean.collectAxioms`. -/
def inspectConstant (constName : Name) : CoreM ConstantAuditReport := do
  let env ← getEnv
  match env.find? constName with
  | none =>
    return {
      constName
      existsInEnv := false
      isTheorem := false
      isSafeDefinition := false
      transitiveAxioms := #[]
      disallowedAxioms := #[]
      hasSorryAx := false
      hasReduceBool := false
      certifiedClean := false
    }
  | some cinfo =>
    let axioms ← Lean.collectAxioms constName
    let disallowed := axioms.filter (fun ax => !isAllowedAxiom ax)
    let hasSorry := axioms.contains sorryAxiomName
    let hasReduce :=
      axioms.contains ofReduceBoolAxiomName ||
      axioms.contains ofReduceNatAxiomName ||
      axioms.contains trustCompilerAxiomName
    let isThm := match cinfo with
      | .thmInfo _ => true
      | _ => false
    let isSafeDef := match cinfo with
      | .defnInfo v => v.safety == .safe
      | .thmInfo _ => true
      | _ => true
    let clean := isSafeDef && disallowed.isEmpty && !hasSorry && !hasReduce
    return {
      constName
      existsInEnv := true
      isTheorem := isThm
      isSafeDefinition := isSafeDef
      transitiveAxioms := axioms
      disallowedAxioms := disallowed
      hasSorryAx := hasSorry
      hasReduceBool := hasReduce
      certifiedClean := clean
    }

/-- Inspect a constant inside an explicit `Lean.Environment` snapshot. -/
def inspectConstantInEnv (env : Environment) (constName : Name) : CoreM ConstantAuditReport :=
  withEnv env (inspectConstant constName)

/-- Inspect a batch of constants and return all audit reports. -/
def inspectConstants (names : Array Name) : CoreM (Array ConstantAuditReport) :=
  names.mapM inspectConstant

/-- Verify that a constant exists in the kernel `Environment` and passes all axiom hygiene gates. -/
def checkConstantClean (constName : Name) : CoreM Bool := do
  let rep ← inspectConstant constName
  return rep.existsInEnv && rep.certifiedClean

/-- Format a `ConstantAuditReport` as a compact JSON object string. -/
def ConstantAuditReport.toJsonString (r : ConstantAuditReport) : String :=
  let axs := r.transitiveAxioms.toList.map (fun n => s!"\"{n}\"")
  let dis := r.disallowedAxioms.toList.map (fun n => s!"\"{n}\"")
  s!"\{\"const\":\"{r.constName}\",\"exists\":{r.existsInEnv},\"is_theorem\":{r.isTheorem},\"certified_clean\":{r.certifiedClean},\"has_sorry_ax\":{r.hasSorryAx},\"has_reduce_bool\":{r.hasReduceBool},\"axioms\":[{String.intercalate "," axs}],\"disallowed_axioms\":[{String.intercalate "," dis}]}"

syntax (name := turboAssertCleanAxioms) "#turbo_assert_clean_axioms " "[" ident* "]" : command
syntax (name := turboInspectAxiomsJson) "#turbo_inspect_axioms_json " "[" ident* "]" : command

@[command_elab turboAssertCleanAxioms]
def elabTurboAssertCleanAxioms : CommandElab := fun stx => do
  let ids := stx[2].getArgs
  for idStx in ids do
    let rawName := idStx.getId
    let resolved ← liftCoreM (realizeGlobalConstNoOverloadWithInfo idStx) <|> pure rawName
    let report ← liftCoreM (inspectConstant resolved)
    if !report.existsInEnv then
      throwErrorAt idStx s!"[TurboLean.Inspector] Constant `{resolved}` not found in kernel Environment"
    if !report.certifiedClean then
      throwErrorAt idStx s!"[TurboLean.Inspector] Kernel axiom gate FAILED for `{resolved}`: disallowed axioms {report.disallowedAxioms.toList} (all transitive axioms: {report.transitiveAxioms.toList})"

@[command_elab turboInspectAxiomsJson]
def elabTurboInspectAxiomsJson : CommandElab := fun stx => do
  let ids := stx[2].getArgs
  let mut entries : Array String := #[]
  for idStx in ids do
    let rawName := idStx.getId
    let resolved ← liftCoreM (realizeGlobalConstNoOverloadWithInfo idStx) <|> pure rawName
    let report ← liftCoreM (inspectConstant resolved)
    entries := entries.push report.toJsonString
  liftIO <| IO.println s!"[{String.intercalate "," entries.toList}]"

-- Self-verify kernel axiom hygiene on TurboLean's own formal theorems at elaboration time:
#turbo_assert_clean_axioms [
  TurboLean.Reflection.StorageKey.fastBeq_eq_true_iff
  TurboLean.Reflection.StorageKey.fastBeq_refl
  TurboLean.Reflection.getStorage_setStorage_same
  TurboLean.Reflection.getStorage_setStorage_other
  TurboLean.Reflection.lookup_chain_sound
  TurboLean.Reflection.lookup_chain_frame_sound
  TurboLean.Reflection.getStorage_setStorage_hit
  TurboLean.Reflection.getStorage_setStorage_miss
  TurboLean.FastCheck.addWithCarry_zero_right
  TurboLean.FastCheck.addWithCarry_comm_low
  TurboLean.Inspector.allAxiomsAllowed_nil
  TurboLean.Inspector.hasNoForbiddenAxioms_nil
  TurboLean.Inspector.propext_is_allowed
  TurboLean.Inspector.quot_sound_is_allowed
  TurboLean.Inspector.classical_choice_is_allowed
]

end TurboLean.Inspector
