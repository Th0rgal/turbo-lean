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

def lowerImpureLetValue (lv : Lean.Compiler.LCNF.LetValue .impure) (retTy : LNIRType) : BridgeM LNIRExpr := do
  match lv with
  | .lit litVal => lowerLitValueM litVal retTy true
  | .erased => return .scalar (.constU64 0)
  | .fvar fvarId args => lowerFVarCall fvarId args retTy
  | .ctor ctorInfo args _ =>
    lowerTupleOrEnumCtor ctorInfo.name ctorInfo.cidx args retTy
  | .reuse slotFVar ctorInfo _ args _ =>
    if isUnboxedScalarOrTuple (← getVarType (← internFVar slotFVar)) then
      return ← lowerTupleOrEnumCtor ctorInfo.name ctorInfo.cidx args retTy
    Lean.throwError "[lean-native] Unsupported legacy heap reuse instruction in Stage 1B"
  | .oproj idx fvarId _ => lowerTupleProj fvarId idx retTy true
  | .uproj idx fvarId _ => lowerScalarProjM fvarId true idx 0 retTy
  | .sproj n off fvarId _ => lowerScalarProjM fvarId false n off retTy
  | .fap fnName args _ => lowerNamedCall fnName args retTy
  | .pap fnName _ _ => Lean.throwError s!"[lean-native] Unsupported partial application (`pap {fnName}`) in Stage 1B"
  | .box _ fvarId _ | .unbox fvarId _ =>
    let v ← internFVar fvarId
    let vt ← getVarType v
    if isUnboxedScalarOrTuple vt || vt == .objPtr || vt == .taggedPtr then return .scalar (.var v)
    else Lean.throwError s!"[lean-native] Unsupported boxing/unboxing of `{reprStr vt}` in Stage 1B"
  | .isShared fvarId _ =>
    let v ← internFVar fvarId
    let vt ← getVarType v
    if isUnboxedScalarOrTuple vt then return .scalar (.constBool true)
    if (← get).allowStage1DHeap && (vt == .objPtr || vt == .taggedPtr) then return .isExclusive v
    Lean.throwError "[lean-native] internal bridge error: unintercepted isShared"
  | .reset _ fvarId _ =>
    let v ← internFVar fvarId
    if isUnboxedScalarOrTuple (← getVarType v) then return .scalar (.var v)
    Lean.throwError "[lean-native] Unsupported heap reset instruction in Stage 1B"

def lowerTagBranch (condVar : VarId) (cidx : Nat) (isBool : Bool) (yes no : LNIRCode) : BridgeM LNIRCode := do
  let condTy ← getVarType condVar
  if isBool || condTy == .i1 then
    return (RealLCNFBridge.lowerTagBranchPure condVar condTy cidx isBool 0 yes no).1
  let cmpVar ← freshBridgeVar .i1
  return (RealLCNFBridge.lowerTagBranchPure condVar condTy cidx isBool cmpVar yes no).1

mutual
partial def lowerImpureAlts (condVar : VarId) (isBool : Bool) (idx : Nat) (alts : List (Lean.Compiler.LCNF.Alt .impure))
    (discr? : Option VarId := none) : BridgeM LNIRCode := do
  -- C1.2: inside a heap `cases` alt the scrutinee's ctor (hence its `getCtorLayout` slots) is known
  match alts with
  | [] => return .unreachable
  | [.alt ctorName params code _] =>
    if !params.isEmpty then Lean.throwError s!"[lean-native] unsupported constructor payload pattern in {ctorName}"
    lowerImpureCode code
  | [.ctorAlt info code _] => withActiveCtor? discr? info.name (lowerImpureCode code)
  | [.default code] => lowerImpureCode code
  | alt :: rest =>
    match alt with
    | .ctorAlt info code _ =>
      lowerTagBranch condVar info.cidx isBool (← withActiveCtor? discr? info.name (lowerImpureCode code))
        (← lowerImpureAlts condVar isBool (idx + 1) rest discr?)
    | .default code => lowerImpureCode code
    | .alt ctorName params code _ =>
      if !params.isEmpty then
        Lean.throwError s!"[lean-native] unsupported constructor payload pattern in {ctorName}"
      let cidx ← lookupCtorIdx ctorName idx
      lowerTagBranch condVar cidx isBool (← lowerImpureCode code) (← lowerImpureAlts condVar isBool (idx + 1) rest)

partial def lowerImpureCode (code : Lean.Compiler.LCNF.Code .impure) : BridgeM LNIRCode := do
  match code with
  | .let decl k =>
    if let .ctor info args _ := decl.value then
      if (← get).allowStage1DHeap && (info.usize > 0 || info.ssize > 0) then
        return ← lowerRcCtorWithScalarsM decl.fvarId info.name args k lowerImpureCode
    let rawDeclTy ← lowerBridgeType decl.type
    if rawDeclTy != .unit then checkBridgeType s!"let binding `{decl.binderName}`" decl.type rawDeclTy true
    let rhs ← lowerImpureLetValue decl.value rawDeclTy
    let isBox := match decl.value with | .box _ _ _ => true | _ => false
    let ty ← inferImpureRhsType rhs rawDeclTy isBox
    let dst ← internFVar decl.fvarId ty true
    match rhs with
    | .isExclusive _ =>
      let exclVar ← freshBridgeVar .i1
      let kCode ← lowerImpureCode k
      return .letBind exclVar .i1 rhs (.letBind dst .i1 (.scalar (.unaryOp .not (.var exclVar))) kCode)
    | _ =>
      return .letBind dst ty rhs (← lowerImpureCode k)
  | .jp decl k => lowerJoinPoint decl k lowerImpureCode
  | .jmp fvarId args => lowerJmpInstr fvarId args
  | .inc fvarId n _ _ k _ => lowerRefOp true fvarId n (← lowerImpureCode k)
  | .dec fvarId n _ _ _ k _ => lowerRefOp false fvarId n (← lowerImpureCode k)
  | .del fvarId k _ => lowerDelM fvarId k lowerImpureCode
  | .setTag fvarId cidx k _ => lowerSetTagM fvarId cidx k lowerImpureCode
  | .oset fvarId idx y k _ => lowerOsetInstr fvarId idx y k lowerImpureCode
  | .uset fvarId i y k _ => lowerScalarSetM fvarId true i 0 y k lowerImpureCode
  | .sset fvarId n off y _ k _ => lowerScalarSetM fvarId false n off y k lowerImpureCode
  | .cases c =>
    let condVar ← internFVar c.discr
    let condTy ← getVarType condVar
    let st ← get
    if st.allowStage1DHeap && c.typeName != ``Bool && (condTy == .objPtr || condTy == .taggedPtr) then
      let tagVar ← freshBridgeVar .i64
      let altsCode ← lowerImpureAlts tagVar false 0 (orderAlts c.alts.toList) (some condVar)
      return .letBind tagVar .i64 (.call "lean_native_ctor_tag" [condVar] .i64 false) altsCode
    else if !isSupportedStage1BScalarType condTy st.arch &&
        !(c.typeName == ``Bool && st.inJoinPointBody && (condTy == .objPtr || condTy == .taggedPtr)) then
      Lean.throwError s!"[lean-native] Unsupported cases scrutinee type `{c.typeName}`"
    else
      lowerImpureAlts condVar (c.typeName == ``Bool) 0 (orderAlts c.alts.toList)
  | .return fvarId =>
    if (← get).localFunMap.contains fvarId then
      Lean.throwError "[lean-native] Unsupported returning local closure"
    return .ret (← internFVar fvarId)
  | .unreach _ => return .unreachable
end

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
  ingestLCNFDeclGeneric decl (fun c => do modify ({ · with fvarCtor := collectFVarCtors c }); lowerImpureCode c)
    localDeclNames arch true allowRcAdt

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
