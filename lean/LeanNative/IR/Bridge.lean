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
  match argVars with
  | [_, _] =>
    (tryLowerGfSimdIntrinsic env fnName argVars retTy argTys).orElse fun _ =>
      RealLCNFBridge.lowerCanonicalIntrinsicPure? fnName argVars retTy argTys isLocal arch
  | _ => RealLCNFBridge.lowerCanonicalIntrinsicPure? fnName argVars retTy argTys isLocal arch

def lowerNamedCall (fnName : Lean.Name) (args : Array (Lean.Compiler.LCNF.Arg pu)) (retTy : LNIRType) : BridgeM LNIRExpr := do
  let env ← getEnv
  let st ← get
  let isLocal := st.localDeclNames.contains fnName || fnName == st.selfDeclName
  let argVars ← args.toList.mapM (lowerArg · isLocal)
  let argTys ← argVars.mapM getVarType
  match tryLowerIntrinsicCall env fnName argVars retTy argTys isLocal st.arch with
  | some intrinsicExpr => return intrinsicExpr
  | none =>
    if !isLocal || Lean.isExtern env fnName then
      Lean.throwError s!"[lean-native] Unsupported external or non-scalar call `{fnName}` in Stage 1B"
    return .call (mangleDeclNameInEnv env fnName) argVars retTy false

def lowerFVarCall (fvarId : Lean.FVarId) (args : Array (Lean.Compiler.LCNF.Arg pu)) (_retTy : LNIRType) : BridgeM LNIRExpr := do
  if !args.isEmpty then
    Lean.throwError "[lean-native] unsupported higher-order fvar call"
  if (← get).localFunMap.contains fvarId then
    Lean.throwError "[lean-native] Unsupported escaping local function value"
  return .scalar (.var (← internFVar fvarId))

def lowerImpureLetValue (lv : Lean.Compiler.LCNF.LetValue .impure) (retTy : LNIRType) : BridgeM LNIRExpr :=
  lowerImpureLetValueViaRealM lv retTy

def lowerTagBranch (condVar : VarId) (cidx : Nat) (isBool : Bool) (yes no : LNIRCode) : BridgeM LNIRCode := do
  let condTy ← getVarType condVar
  if isBool || condTy == .i1 then
    return (RealLCNFBridge.lowerTagBranchPure condVar condTy cidx isBool 0 yes no).1
  let cmpVar ← freshBridgeVar .i1
  return (RealLCNFBridge.lowerTagBranchPure condVar condTy cidx isBool cmpVar yes no).1

def lowerImpureCode (code : Lean.Compiler.LCNF.Code .impure) : BridgeM LNIRCode :=
  lowerImpureCodeViaRealM code

def lowerPureLetValue (lv : Lean.Compiler.LCNF.LetValue .pure) (retTy : LNIRType) : BridgeM LNIRExpr := do
  match lv with
  | .lit litVal => lowerLitValueM litVal retTy
  | .erased => return .scalar (.constU64 0)
  | .proj _ idx fvarId _ => lowerTupleProj fvarId idx retTy false
  | .const declName _ args _ =>
    let env ← getEnv
    match env.find? declName with
    | some (.ctorInfo cval) => lowerTupleOrEnumCtor declName cval.cidx args retTy
    | _ => lowerNamedCall declName args retTy
  | .fvar fvarId args => lowerFVarCall fvarId args retTy

mutual
partial def lowerPureAlts (condVar : VarId) (isBool : Bool) (idx : Nat) (alts : List (Lean.Compiler.LCNF.Alt .pure)) : BridgeM LNIRCode := do
  let emitTagBranch (cidx : Nat) (code : Lean.Compiler.LCNF.Code .pure) (rest : List (Lean.Compiler.LCNF.Alt .pure)) : BridgeM LNIRCode := do
    lowerTagBranch condVar cidx isBool (← lowerPureCode code) (← lowerPureAlts condVar isBool (idx + 1) rest)
  match alts with
  | [] => return .unreachable
  | [singleAlt] =>
    if let .alt ctorName params code _ := singleAlt then
      if !params.isEmpty then
        return ← lowerTuplePatternAlt condVar ctorName params code lowerPureCode
    lowerPureCode singleAlt.getCode
  | alt :: rest =>
    match alt with
    | .alt ctorName params code _ =>
      if !params.isEmpty then
        Lean.throwError s!"[lean-native] unsupported constructor payload pattern in {ctorName}"
      emitTagBranch (← lookupCtorIdx ctorName idx) code rest
    | .ctorAlt info code _ => emitTagBranch info.cidx code rest
    | .default code => lowerPureCode code

partial def lowerPureCode (code : Lean.Compiler.LCNF.Code .pure) : BridgeM LNIRCode := do
  match code with
  | .let decl k =>
    let ty ← lowerBridgeType decl.type
    if ty != .unit then checkBridgeType s!"let binding `{decl.binderName}`" decl.type ty
    if let .fvar fvarId args := decl.value then
      if let some (pIds, fBody) := (← get).localFunMap[fvarId]? then
        if args.size != pIds.length then
          Lean.throwError "[lean-native] Unsupported partial application of local function"
        let argVars ← args.toList.mapM lowerArg
        let dst ← internFVar decl.fvarId ty true
        let kCode ← lowerPureCode k
        let ren := (pIds.zip argVars).foldl (fun m (o, n) => m.insert o n) ({} : Std.HashMap VarId VarId)
        return ← inlineLocalFunCode ren dst ty kCode fBody
    let rhs ← lowerPureLetValue decl.value ty
    return .letBind (← internFVar decl.fvarId ty true) ty rhs (← lowerPureCode k)
  | .fun decl k _ => lowerLocalFunDecl decl k lowerPureCode
  | .jp decl k => lowerJoinPoint decl k lowerPureCode
  | .jmp fvarId args => lowerJmpInstr fvarId args
  | .cases c =>
    let condVar ← internFVar c.discr
    let condTy ← getVarType condVar
    if !isSupportedStage1BScalarOrTuple condTy (← get).arch then
      Lean.throwError s!"[lean-native] Unsupported cases scrutinee type `{c.typeName}`"
    lowerPureAlts condVar (c.typeName == ``Bool) 0 (orderAlts c.alts.toList)
  | .return fvarId =>
    if (← get).localFunMap.contains fvarId then
      Lean.throwError "[lean-native] Unsupported returning local closure"
    return .ret (← internFVar fvarId)
  | .unreach _ => return .unreachable
end

def ingestLCNFDeclGeneric {pu} (decl : Lean.Compiler.LCNF.Decl pu)
    (lowerCodeFn : Lean.Compiler.LCNF.Code pu → BridgeM LNIRCode)
    (localDeclNames : Array Lean.Name := #[]) (arch : TargetArch := .x86_64)
    (allowInternalObj : Bool := false) (allowRcAdt : Bool := false) : Lean.CoreM LNIRDecl := do
  let env ← getEnv
  if ← declUsesSignedScalarTransitively decl then
    Lean.throwError s!"[lean-native] Unsupported signed integer type (`Int*` / `ISize`) in `{decl.name}`"
  let metaInfo := getLCNFDeclMetadata env decl.name
  let isDeclExtern := metaInfo.isExtern
  if isDeclExtern then
    Lean.throwError s!"[lean-native] Unsupported `@[extern]` declaration `{decl.name}` in Stage 1B"
  let isExported := (Lean.getExportNameFor? env decl.name).isSome
  checkEnvConstSignatureM env decl.name arch isExported
  -- C4: Stage 1D heap lowering is opt-in (`--allow-rc-adt`); by default heap ADTs fail closed
  let isStage1DHeap := allowRcAdt && allowInternalObj && !isExported && declQualifiesForStage1DHeap env decl.name arch
  let initSt : BridgeState := {
    mangledSymbol := metaInfo.mangledSymbol, isSimpleGround := metaInfo.isSimpleGround,
    selfDeclName := decl.name, localDeclNames := localDeclNames, arch := arch,
    allowStage1DHeap := isStage1DHeap }
  let action : BridgeM LNIRDecl := do
    let envParamTys := collectEnvExplicitParamTypes env decl.name
    let mut lnirParams : List LNIRParam := []
    let mut pIdx : Nat := 0
    for p in decl.params do
      let rawPTy ← lowerBridgeType p.type
      let pTy :=
        if !isStage1DHeap && (rawPTy == .objPtr || rawPTy == .taggedPtr) then
          match envParamTys[pIdx]? with
          | some (.tuple fs) => .tuple fs
          | _ => rawPTy
        else rawPTy
      checkBridgeType s!"parameter `{p.binderName}` of `{decl.name}`" p.type pTy allowInternalObj
      let vid ← internFVar p.fvarId pTy true
      lnirParams := lnirParams ++ [{ id := vid, name := p.binderName.toString, ty := pTy, borrow := p.borrow }]
      pIdx := pIdx + 1
    let retTy ← lowerBridgeType decl.type
    checkBridgeType s!"return type of `{decl.name}`" decl.type retTy allowInternalObj
    match decl.value with
    | .code c =>
      let env ← getEnv
      let body ←
        if let some intrExpr := tryLowerGfSimdIntrinsic env decl.name (lnirParams.map (·.id)) retTy (lnirParams.map (·.ty)) then do
          let retVar ← freshBridgeVar retTy
          pure (.letBind retVar retTy intrExpr (.ret retVar))
        else if codeHasSelfTailCall decl.name c then
          Lean.throwError s!"[lean-native] unsupported self-tail recursion in {decl.name}: no qualified loop lowering"
        else
          lowerCodeFn c >>= compressScalarCode
      let effRetTy := match inferReturnedType body with | some (.tuple fs) => .tuple fs | _ => retTy
      return {
        name := metaInfo.mangledSymbol, params := lnirParams, retTy := effRetTy, body := body,
        assurance := .tested,
        isGpuCand := lnirParams.all (fun p => p.ty.isGpuCompatible) && effRetTy.isGpuCompatible }
    | .extern _ =>
      Lean.throwError s!"[lean-native] Unsupported `@[extern]` declaration `{decl.name}` in Stage 1B"
  Prod.fst <$> action.run initSt

def ingestLCNFImpureDecl (decl : Lean.Compiler.LCNF.Decl .impure)
    (localDeclNames : Array Lean.Name := #[]) (arch : TargetArch := .x86_64) (allowRcAdt : Bool := false) : Lean.CoreM LNIRDecl :=
  ingestImpureDeclViaReal decl localDeclNames arch allowRcAdt

def ingestLCNFMonoDecl (decl : Lean.Compiler.LCNF.Decl .pure)
    (localDeclNames : Array Lean.Name := #[]) (arch : TargetArch := .x86_64) : Lean.CoreM LNIRDecl :=
  ingestLCNFDeclGeneric decl lowerPureCode localDeclNames arch false

def ingestModuleDecls (declNames : Array Lean.Name) (moduleName : String := "LeanNative.Ingested")
    (arch : TargetArch := .x86_64) (allowRcAdt : Bool := false) : Lean.CoreM LNIRModule :=
  ingestModuleDeclsWith (fun d ns a => ingestLCNFImpureDecl d ns a allowRcAdt) (fun d ns a => ingestLCNFMonoDecl d ns a) declNames moduleName arch

def ingestAllLocalDecls (moduleName : String := "LeanNative.Ingested")
    (arch : TargetArch := .x86_64) (allowRcAdt : Bool := false) : Lean.CoreM LNIRModule := do
  let impureNames ← Lean.Compiler.LCNF.getLocalImpureDecls
  let env ← getEnv
  let filteredImpure := impureNames.filter (fun n => !isCompilerGeneratedAuxDecl env n)
  let extraNames := env.constants.map₂.foldl (fun acc name _ =>
    if impureNames.contains name || isCompilerGeneratedAuxDecl env name then acc else acc.push name) #[]
  ingestModuleDecls (filteredImpure ++ extraNames) moduleName arch allowRcAdt

end LeanNative.IR
