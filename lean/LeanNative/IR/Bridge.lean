import LeanNative.IR.BridgeHelpers

set_option autoImplicit true

namespace LeanNative.IR

open Lean
open Lean.Compiler.LCNF

def canonicalScalarBinOpTypedTable : List (Lean.Name × LNIRType × BinOp) :=
  RealLCNFBridge.canonicalScalarBinOpTypedTable

def canonicalScalarBinOpTable : List (Lean.Name × BinOp) :=
  RealLCNFBridge.canonicalScalarBinOpTable

def lookupCanonicalTypedBinOp? (fnName : Lean.Name) : Option (LNIRType × BinOp) :=
  RealLCNFBridge.lookupCanonicalTypedBinOp? fnName

def lookupCanonicalBinOp? (fnName : Lean.Name) : Option BinOp :=
  RealLCNFBridge.lookupCanonicalBinOp? fnName

def canonicalUIntCastMask? (fnName : Lean.Name) (argTys : List LNIRType) (retTy : LNIRType)
    (arch : TargetArch := .x86_64) : Option UInt64 :=
  RealLCNFBridge.canonicalUIntCastMask? fnName argTys retTy arch

def tryLowerIntrinsicCall (env : Lean.Environment) (fnName : Lean.Name) (argVars : List VarId)
    (retTy : LNIRType) (argTys : List LNIRType := []) (isLocal : Bool := false)
    (arch : TargetArch := .x86_64) : Option LNIRExpr :=
  (RealLCNFBridge.lowerSliceIntrinsicPure? fnName argVars retTy argTys isLocal arch).orElse fun _ =>
    match argVars with
    | [_, _] =>
      (tryLowerGfSimdIntrinsic env fnName argVars retTy argTys).orElse fun _ =>
        RealLCNFBridge.lowerCanonicalIntrinsicPure? fnName argVars retTy argTys isLocal arch
    | _ => RealLCNFBridge.lowerCanonicalIntrinsicPure? fnName argVars retTy argTys isLocal arch

def ingestLCNFImpureDecl (decl : Lean.Compiler.LCNF.Decl .impure)
    (localDeclNames : Array Lean.Name := #[]) (arch : TargetArch := .x86_64) (allowRcAdt : Bool := false) : Lean.CoreM LNIRDecl :=
  ingestImpureDeclViaReal decl localDeclNames arch allowRcAdt

def ingestModuleDecls (declNames : Array Lean.Name) (moduleName : String := "LeanNative.Ingested")
    (arch : TargetArch := .x86_64) (allowRcAdt : Bool := false) : Lean.CoreM LNIRModule :=
  ingestModuleDeclsWith (fun d ns a => ingestLCNFImpureDecl d ns a allowRcAdt) declNames moduleName arch

def ingestAllLocalDecls (moduleName : String := "LeanNative.Ingested")
    (arch : TargetArch := .x86_64) (allowRcAdt : Bool := false) : Lean.CoreM LNIRModule := do
  let impureNames ← Lean.Compiler.LCNF.getLocalImpureDecls
  let env ← getEnv
  let filteredImpure := impureNames.filter (fun n => !isCompilerGeneratedAuxDecl env n)
  let extraNames := env.constants.map₂.foldl (fun acc name _ =>
    if impureNames.contains name || isCompilerGeneratedAuxDecl env name then acc else acc.push name) #[]
  ingestModuleDecls (filteredImpure ++ extraNames) moduleName arch allowRcAdt

end LeanNative.IR
