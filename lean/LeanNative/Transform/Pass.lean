import LeanNative.IR.Types
import LeanNative.IR.AST

namespace LeanNative.Transform

open LeanNative.IR

/-- Per-declaration transformation step certificate emitted by an optimization pass. -/
structure PassStepCert where
  passName   : String
  declName   : String
  inputHash  : String
  outputHash : String
  changed    : Bool
  assurance  : AssuranceLevel
  theoremRef : String
  notes      : String
  deriving Repr, DecidableEq, Inhabited, BEq

/-- A compiler transformation pass operating on LNIR declarations and modules. -/
structure TransformPass where
  name       : String
  assurance  : AssuranceLevel
  theoremRef : String
  runDecl    : LNIRDecl → LNIRDecl × PassStepCert

namespace TransformPass

/-- Helper to construct a `TransformPass` from a declaration body transformation function. -/
def ofCodeTransform (name : String) (assurance : AssuranceLevel) (theoremRef : String)
    (defaultNotes : String) (f : LNIRDecl → LNIRCode × Option String) : TransformPass where
  name := name
  assurance := assurance
  theoremRef := theoremRef
  runDecl := fun d =>
    let inHash := d.structuralHash
    let (body', customNote) := f d
    let d' : LNIRDecl := {
      d with
      body := body'
      assurance := AssuranceLevel.combine d.assurance assurance
    }
    let outHash := d'.structuralHash
    let changed := inHash != outHash || d.body != body'
    let cert : PassStepCert := {
      passName := name
      declName := d.name
      inputHash := inHash
      outputHash := outHash
      changed := changed
      assurance := assurance
      theoremRef := theoremRef
      notes := customNote.getD defaultNotes
    }
    (d', cert)

/-- Run a single pass over all declarations in an `LNIRModule`. -/
def runModule (pass : TransformPass) (m : LNIRModule) : LNIRModule × List PassStepCert :=
  let results := m.decls.map pass.runDecl
  let decls' := results.map Prod.fst
  let certs := results.map Prod.snd
  ({ m with decls := decls' }, certs)

end TransformPass

/-- Run a sequence of passes on a single `LNIRDecl`. -/
def runPassPipelineDecl (passes : List TransformPass) (d : LNIRDecl) : LNIRDecl × List PassStepCert :=
  passes.foldl (fun (curDecl, certs) pass =>
    let (nextDecl, cert) := pass.runDecl curDecl
    (nextDecl, certs ++ [cert])
  ) (d, [])

/-- Run a sequence of passes on an `LNIRModule`. -/
def runPassPipeline (passes : List TransformPass) (m : LNIRModule) : LNIRModule × List PassStepCert :=
  passes.foldl (fun (curMod, certs) pass =>
    let (nextMod, stepCerts) := pass.runModule curMod
    (nextMod, certs ++ stepCerts)
  ) (m, [])

end LeanNative.Transform
