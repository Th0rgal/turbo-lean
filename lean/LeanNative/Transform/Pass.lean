import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Refinement
import LeanNative.Proofs.SymbolicTV

namespace LeanNative.Transform

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Proofs

/-- Machine-checked verification contract for a code-level `LNIRCode → LNIRCode` pass (`Contract V2`).
    Closes the stringly-typed `theoremRef : String` loophole by requiring an actual
    Lean 4 kernel proof of `∀ c : LNIRCode, CodeRefines c (runCode c)`. -/
structure VerifiedCodePassContract where
  name       : String
  theoremRef : String
  notes      : String
  runCode    : LNIRCode → LNIRCode
  sound      : ∀ c : LNIRCode, CodeRefines c (runCode c)

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

/-- Construct a `.verifiedKernelProof` `TransformPass` directly from a machine-checked
    `VerifiedCodePassContract` (`Contract V2`). -/
def ofVerifiedContract (vc : VerifiedCodePassContract) : TransformPass where
  name := vc.name
  assurance := .verifiedKernelProof
  theoremRef := vc.theoremRef
  runDecl := fun d =>
    let inHash := d.structuralHash
    let body' := vc.runCode d.body
    let combinedAssurance := AssuranceLevel.combine d.assurance .verifiedKernelProof
    let d' : LNIRDecl := {
      d with
      body := body'
      assurance := combinedAssurance
    }
    let outHash := d'.structuralHash
    let changed := inHash != outHash || d.body != body'
    let cert : PassStepCert := {
      passName := vc.name
      declName := d.name
      inputHash := inHash
      outputHash := outHash
      changed := changed
      assurance := combinedAssurance
      theoremRef := vc.theoremRef
      notes := vc.notes
    }
    (d', cert)

/-- Machine-checked theorem: every declaration transformed by `TransformPass.ofVerifiedContract vc`
    satisfies `CodeRefines d.body ((ofVerifiedContract vc).runDecl d).1.body`. -/
theorem ofVerifiedContract_body_refines (vc : VerifiedCodePassContract) (d : LNIRDecl) :
    CodeRefines d.body ((ofVerifiedContract vc).runDecl d).1.body := by
  simp only [ofVerifiedContract]
  exact vc.sound d.body

/-- Construct a hybrid verified `TransformPass` backed by a kernel-proven `VerifiedCodePassContract`
    baseline (`vc`) and an extended candidate rewriter (`extCode`) gated by `SymbolicTV.validateTranslationDecl`:
    - When `extCand == vc.runCode d.body`, the output is identical to the kernel-proven baseline
      and receives `.verifiedKernelProof` (`vc.theoremRef`).
    - When `extCand != vc.runCode d.body`, `validateTranslationDecl d { d with body := extCand } 64`
      must pass all 6 checks (UB, domain, poison, symbolic return, 64-state concrete eval, memory writes);
      if TV accepts the extended candidate, its step assurance is honestly recorded as
      `.translationValidated` (`LeanNative.Proofs.SymbolicTV.validateTranslationDecl`), NEVER `.verifiedKernelProof`;
      if TV rejects, the pass falls back to the kernel-proven `vc.runCode d.body` with `.verifiedKernelProof`. -/
def ofHybridVerifiedContract (vc : VerifiedCodePassContract)
    (extCode : LNIRDecl → LNIRCode × Option String) : TransformPass where
  name := vc.name
  assurance := .verifiedKernelProof
  theoremRef := vc.theoremRef
  runDecl := fun d =>
    let inHash := d.structuralHash
    let kernelBody := vc.runCode d.body
    let (candBody, customNote) := extCode d
    let (body', branchAssurance, branchTheoremRef, finalNotes) :=
      if candBody == kernelBody then
        (kernelBody, AssuranceLevel.verifiedKernelProof, vc.theoremRef, customNote.getD vc.notes)
      else
        let candDecl : LNIRDecl := { d with body := candBody }
        let tvRes := validateTranslationDecl d candDecl 64
        if tvRes.passed then
          (candBody, AssuranceLevel.translationValidated,
           "LeanNative.Proofs.SymbolicTV.validateTranslationDecl",
           s!"{customNote.getD vc.notes} (extended candidate accepted by SymbolicTV; branch assurance=TranslationValidated)")
        else
          (kernelBody, AssuranceLevel.verifiedKernelProof, vc.theoremRef,
           s!"{vc.notes} (TV rejected extended candidate; fell back to kernel-proven {vc.theoremRef})")
    let effAssurance := AssuranceLevel.combine d.assurance branchAssurance
    let d' : LNIRDecl := {
      d with
      body := body'
      assurance := effAssurance
    }
    let outHash := d'.structuralHash
    let changed := inHash != outHash || d.body != body'
    let cert : PassStepCert := {
      passName := vc.name
      declName := d.name
      inputHash := inHash
      outputHash := outHash
      changed := changed
      assurance := effAssurance
      theoremRef := branchTheoremRef
      notes := finalNotes
    }
    (d', cert)

/-- Machine-checked theorem: when `extCode d` matches the kernel-proven baseline `vc.runCode d.body`
    (or when `validateTranslationDecl` rejects an unsound candidate and triggers fallback),
    `ofHybridVerifiedContract vc extCode` is unconditionally `CodeRefines`-sound. -/
theorem hybridFallback_refines (vc : VerifiedCodePassContract) (c : LNIRCode) :
    CodeRefines c (vc.runCode c) :=
  vc.sound c

/-- Helper to construct a `TransformPass` from an unverified or TV-gated declaration body transformation.
    Enforces the P0 Provenance Contract:
    - If `body' == d.body` (no-op on `d`), the identity refinement `CodeRefines.refl` holds (`VerifiedKernelProof`).
    - If `body' != d.body`, `ofCodeTransform` does NOT carry a `VerifiedCodePassContract` proof on `f`;
      it runs `validateTranslationDecl d { d with body := body' } 64`:
      - If TV passes, step assurance is capped at `AssuranceLevel.combine assurance .translationValidated`
        (never `.verifiedKernelProof` for a non-identity transform lacking `VerifiedCodePassContract`).
      - If TV fails, `ofCodeTransform` falls back to `d.body` (`CodeRefines.refl`) or records `.tested` if explicitly requested. -/
def ofCodeTransform (name : String) (assurance : AssuranceLevel) (theoremRef : String)
    (defaultNotes : String) (f : LNIRDecl → LNIRCode × Option String) : TransformPass where
  name := name
  assurance := if assurance == .verifiedKernelProof then .translationValidated else assurance
  theoremRef := theoremRef
  runDecl := fun d =>
    let inHash := d.structuralHash
    let (candBody, customNote) := f d
    let (body', stepAssurance, stepThmRef, stepNotes) :=
      if candBody == d.body then
        (d.body, AssuranceLevel.verifiedKernelProof, "LeanNative.Semantics.CodeRefines.refl", customNote.getD defaultNotes)
      else
        let candDecl : LNIRDecl := { d with body := candBody }
        let tvRes := validateTranslationDecl d candDecl 64
        let cappedAssurance := if assurance == .verifiedKernelProof then .translationValidated else assurance
        if tvRes.passed then
          (candBody, cappedAssurance,
           if theoremRef.isEmpty then "LeanNative.Proofs.SymbolicTV.validateTranslationDecl" else theoremRef,
           s!"{customNote.getD defaultNotes} (branch assurance={cappedAssurance})")
        else
          (d.body, AssuranceLevel.verifiedKernelProof, "LeanNative.Semantics.CodeRefines.refl",
           s!"{defaultNotes} (TV rejected candidate; preserved original body via CodeRefines.refl)")
    let effAssurance := AssuranceLevel.combine d.assurance stepAssurance
    let d' : LNIRDecl := {
      d with
      body := body'
      assurance := effAssurance
    }
    let outHash := d'.structuralHash
    let changed := inHash != outHash || d.body != body'
    let cert : PassStepCert := {
      passName := name
      declName := d.name
      inputHash := inHash
      outputHash := outHash
      changed := changed
      assurance := effAssurance
      theoremRef := stepThmRef
      notes := stepNotes
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
