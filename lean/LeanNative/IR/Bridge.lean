import LeanNative.IR.BridgeHelpers

namespace LeanNative.IR

open Lean
open Lean.Compiler.LCNF

/-!
L1 (`roadmap/HORIZONS.md` rung L1, w-l1): this file used to hold a second, unproved lowering —
the `partial def lowerPureCode` / `lowerPureAlts` family with its `BridgeM` call, branch and
let-value helpers, the generic `ingestLCNFDeclGenericWithState` ingest it ran under, and
caller-less `BridgeM` re-export wrappers. They are deleted: the one `LCNF → LNIR` lowering
callee is `RealLCNFBridge.lowerRealLCNFDecl` (`lowerRealLCNFDecl_sound`,
`lowerRealLCNFDecl_driver_sound`), reached through `ingestImpureDeclViaReal`. An explicitly
requested declaration with compiled code but no local impure LCNF form makes the whole
module ingest throw, naming the declaration (L1 r2, review 47512851 F4); constants with no
compiled code are skipped.
-/

/-- Ingest one real `Lean.Compiler.LCNF.Decl .impure` through the single proved lowering path. -/
def ingestLCNFImpureDecl (decl : Lean.Compiler.LCNF.Decl .impure)
    (localDeclNames : Array Lean.Name := #[]) (arch : TargetArch := .x86_64)
    (allowRcAdt : Bool := false) : Lean.CoreM LNIRDecl :=
  ingestImpureDeclViaReal decl localDeclNames arch allowRcAdt

/-- Ingest the named declarations that have a local impure LCNF form. A requested name with
    compiled code but no such form makes the whole call throw, naming the declaration
    (imported names get their own message); constants with no compiled code are skipped. -/
def ingestModuleDecls (declNames : Array Lean.Name) (moduleName : String := "LeanNative.Ingested")
    (arch : TargetArch := .x86_64) (allowRcAdt : Bool := false) : Lean.CoreM LNIRModule :=
  ingestModuleDeclsWith (fun d ns a => ingestLCNFImpureDecl d ns a allowRcAdt) declNames moduleName arch

/-- Ingest every local declaration with an impure LCNF form in the current environment.
    L1 r1 (review a094d3a9 F8): the sweep no longer collects non-impure environment
    constants — they only fed the deleted mono lowering arm. -/
def ingestAllLocalDecls (moduleName : String := "LeanNative.Ingested")
    (arch : TargetArch := .x86_64) (allowRcAdt : Bool := false) : Lean.CoreM LNIRModule := do
  let impureNames ← Lean.Compiler.LCNF.getLocalImpureDecls
  let env ← getEnv
  ingestModuleDecls (impureNames.filter (fun n => !isCompilerGeneratedAuxDecl env n)) moduleName arch allowRcAdt

end LeanNative.IR
