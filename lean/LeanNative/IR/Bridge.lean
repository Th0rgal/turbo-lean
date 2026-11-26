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
`lowerRealLCNFDecl_driver_sound`), reached through `ingestImpureDeclViaReal`. A declaration
the proved path does not cover — including one with no impure LCNF form — is `Unsupported`
and stays with the stock Lean backend.
-/

/-- Ingest one real `Lean.Compiler.LCNF.Decl .impure` through the single proved lowering path. -/
def ingestLCNFImpureDecl (decl : Lean.Compiler.LCNF.Decl .impure)
    (localDeclNames : Array Lean.Name := #[]) (arch : TargetArch := .x86_64)
    (allowRcAdt : Bool := false) : Lean.CoreM LNIRDecl :=
  ingestImpureDeclViaReal decl localDeclNames arch allowRcAdt

/-- Ingest the named declarations that have an impure LCNF form; the rest are `Unsupported`
    on the proved path and are left to the stock backend. -/
def ingestModuleDecls (declNames : Array Lean.Name) (moduleName : String := "LeanNative.Ingested")
    (arch : TargetArch := .x86_64) (allowRcAdt : Bool := false) : Lean.CoreM LNIRModule :=
  ingestModuleDeclsWith (fun d ns a => ingestLCNFImpureDecl d ns a allowRcAdt) declNames moduleName arch

/-- Ingest every local declaration with an impure LCNF form in the current environment. -/
def ingestAllLocalDecls (moduleName : String := "LeanNative.Ingested")
    (arch : TargetArch := .x86_64) (allowRcAdt : Bool := false) : Lean.CoreM LNIRModule := do
  let impureNames ← Lean.Compiler.LCNF.getLocalImpureDecls
  let env ← getEnv
  let filteredImpure := impureNames.filter (fun n => !isCompilerGeneratedAuxDecl env n)
  let extraNames := env.constants.map₂.foldl (fun acc name _ =>
    if impureNames.contains name || isCompilerGeneratedAuxDecl env name then acc else acc.push name) #[]
  ingestModuleDecls (filteredImpure ++ extraNames) moduleName arch allowRcAdt

end LeanNative.IR
