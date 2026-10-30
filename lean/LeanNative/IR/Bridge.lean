import LeanNative.IR.BridgeHelpers

set_option autoImplicit true

namespace LeanNative.IR

open Lean
open Lean.Compiler.LCNF

/-- Canonical `Lean.Name` lookup table with explicit operand width (`LNIRType`).
    Runtime `Nat` is excluded so unbounded integer operations fail closed. -/
def canonicalScalarBinOpTypedTable : List (Lean.Name × LNIRType × BinOp) := [
  (``UInt64.add, .i64, .add), (``UInt64.sub, .i64, .sub), (``UInt64.mul, .i64, .mul), (``UInt64.div, .i64, .div), (``UInt64.mod, .i64, .mod),
  (``UInt64.land, .i64, .bitAnd), (``UInt64.lor, .i64, .bitOr), (``UInt64.xor, .i64, .bitXor), (``UInt64.shiftLeft, .i64, .shl), (``UInt64.shiftRight, .i64, .shr),
  (``UInt64.decEq, .i64, .eq), (`UInt64.beq, .i64, .eq), (``UInt64.decLt, .i64, .lt), (`UInt64.blt, .i64, .lt), (``UInt64.decLe, .i64, .le), (`UInt64.ble, .i64, .le),
  (``UInt32.add, .i32, .add), (``UInt32.sub, .i32, .sub), (``UInt32.mul, .i32, .mul), (``UInt32.div, .i32, .div), (``UInt32.mod, .i32, .mod),
  (``UInt32.land, .i32, .bitAnd), (``UInt32.lor, .i32, .bitOr), (``UInt32.xor, .i32, .bitXor), (``UInt32.shiftLeft, .i32, .shl), (``UInt32.shiftRight, .i32, .shr),
  (``UInt32.decEq, .i32, .eq), (`UInt32.beq, .i32, .eq), (``UInt32.decLt, .i32, .lt), (`UInt32.blt, .i32, .lt), (``UInt32.decLe, .i32, .le), (`UInt32.ble, .i32, .le),
  (``UInt16.add, .i16, .add), (``UInt16.sub, .i16, .sub), (``UInt16.mul, .i16, .mul), (``UInt16.div, .i16, .div), (``UInt16.mod, .i16, .mod),
  (``UInt16.land, .i16, .bitAnd), (``UInt16.lor, .i16, .bitOr), (``UInt16.xor, .i16, .bitXor), (``UInt16.shiftLeft, .i16, .shl), (``UInt16.shiftRight, .i16, .shr),
  (``UInt16.decEq, .i16, .eq), (`UInt16.beq, .i16, .eq), (``UInt16.decLt, .i16, .lt), (`UInt16.blt, .i16, .lt), (``UInt16.decLe, .i16, .le), (`UInt16.ble, .i16, .le),
  (``UInt8.add, .i8, .add), (``UInt8.sub, .i8, .sub), (``UInt8.mul, .i8, .mul), (``UInt8.div, .i8, .div), (``UInt8.mod, .i8, .mod),
  (``UInt8.land, .i8, .bitAnd), (``UInt8.lor, .i8, .bitOr), (``UInt8.xor, .i8, .bitXor), (``UInt8.shiftLeft, .i8, .shl), (``UInt8.shiftRight, .i8, .shr),
  (``UInt8.decEq, .i8, .eq), (`UInt8.beq, .i8, .eq), (``UInt8.decLt, .i8, .lt), (`UInt8.blt, .i8, .lt), (``UInt8.decLe, .i8, .le), (`UInt8.ble, .i8, .le),
  (``USize.add, .usize, .add), (``USize.sub, .usize, .sub), (``USize.mul, .usize, .mul), (``USize.div, .usize, .div), (``USize.mod, .usize, .mod),
  (``USize.land, .usize, .bitAnd), (``USize.lor, .usize, .bitOr), (``USize.xor, .usize, .bitXor), (``USize.shiftLeft, .usize, .shl), (``USize.shiftRight, .usize, .shr),
  (``USize.decEq, .usize, .eq), (`USize.beq, .usize, .eq), (``USize.decLt, .usize, .lt), (`USize.blt, .usize, .lt), (``USize.decLe, .usize, .le), (`USize.ble, .usize, .le)
]

def canonicalScalarBinOpTable : List (Lean.Name × BinOp) :=
  canonicalScalarBinOpTypedTable.map fun (n, _, op) => (n, op)

def lookupCanonicalTypedBinOp? (fnName : Lean.Name) : Option (LNIRType × BinOp) :=
  (canonicalScalarBinOpTypedTable.find? (fun (n, _, _) => n == fnName)).map Prod.snd

def lookupCanonicalBinOp? (fnName : Lean.Name) : Option BinOp :=
  (lookupCanonicalTypedBinOp? fnName).map Prod.snd

/-- Exact primitive names and types only: unsigned narrowing truncates low bits;
    widening masks by `min srcMask dstMask` to clamp any unmasked i64 representation. -/
def canonicalUIntCastMask? (fnName : Lean.Name) (argTys : List LNIRType) (retTy : LNIRType)
    (arch : TargetArch := .x86_64) : Option UInt64 := do
  let usizeEntry : List (Lean.Name × LNIRType × UInt64) :=
    if archSupportsUSize arch then [(``USize, .usize, archUSizeMask arch)] else []
  let types : List (Lean.Name × LNIRType × UInt64) :=
    [(``UInt8, .i8, 255), (``UInt16, .i16, 65535),
     (``UInt32, .i32, 4294967295), (``UInt64, .i64, 18446744073709551615)] ++ usizeEntry
  types.findSome? fun (src, srcTy, srcMask) => types.findSome? fun (dst, dstTy, dstMask) =>
    if src != dst && fnName == Lean.Name.str src ("to" ++ dst.toString) &&
        argTys == [srcTy] && retTy == dstTy then
      some (min srcMask dstMask)
    else none

def tryLowerIntrinsicCall (env : Lean.Environment) (fnName : Lean.Name) (argVars : List VarId)
    (retTy : LNIRType) (argTys : List LNIRType := []) (isLocal : Bool := false)
    (arch : TargetArch := .x86_64) : Option LNIRExpr :=
  match argVars with
  | [lhs, rhs] =>
    match tryLowerGfSimdIntrinsic env fnName argVars retTy argTys with
    | some intr => some intr
    | none =>
      if isLocal then none
      else match lookupCanonicalTypedBinOp? fnName with
        | some (opTy, op) =>
          if argTys != [opTy, opTy] then none
          else .scalar <$> lowerScalarIntrinsicExpr? op lhs rhs opTy retTy arch
        | none => lowerBoolBinIntrinsic? fnName lhs rhs argTys retTy
  | [arg] =>
    if isLocal then none else
    match canonicalUIntCastMask? fnName argTys retTy arch with
    | some effMask => some (.scalar (.binOp .bitAnd (.var arg) (.constU64 effMask)))
    | none => lowerUnaryScalarIntrinsic? fnName arg argTys retTy arch
  | _ => none

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
  | .ctor ctorInfo args _ | .reuse _ ctorInfo _ args _ =>
    lowerTupleOrEnumCtor ctorInfo.name ctorInfo.cidx args retTy
  | .oproj idx fvarId _ => lowerTupleProj fvarId idx retTy true
  | .uproj idx fvarId _ => lowerTupleProj fvarId idx .usize false
  | .sproj offset _ fvarId _ => lowerTupleProj fvarId offset retTy false
  | .fap fnName args _ => lowerNamedCall fnName args retTy
  | .pap fnName _ _ => Lean.throwError s!"[lean-native] Unsupported partial application (`pap {fnName}`) in Stage 1B"
  | .box _ fvarId _ | .unbox fvarId _ =>
    let v ← internFVar fvarId
    let vt ← getVarType v
    if isUnboxedScalarOrTuple vt || vt == .objPtr || vt == .taggedPtr then return .scalar (.var v)
    else Lean.throwError s!"[lean-native] Unsupported boxing/unboxing of `{reprStr vt}` in Stage 1B"
  | .isShared _ _ => Lean.throwError "[lean-native] internal bridge error: unintercepted isShared"
  | .reset .. => Lean.throwError "[lean-native] Unsupported heap reset instruction in Stage 1B"

def lowerTagBranch (condVar : VarId) (cidx : Nat) (isBool : Bool) (yes no : LNIRCode) : BridgeM LNIRCode := do
  let condTy ← getVarType condVar
  if isBool || condTy == .i1 then
    return if cidx == 0 then .ite condVar no yes else if cidx == 1 then .ite condVar yes no else no
  let cmpVar ← freshBridgeVar .i1
  return .letBind cmpVar .i1 (.scalar (.binOp .eq (.var condVar) (.constU64 cidx.toUInt64))) (.ite cmpVar yes no)

mutual
partial def lowerImpureAlts (discr : Lean.FVarId) (typeName : Lean.Name) (condVar : VarId)
    (isBool : Bool) (idx : Nat) (alts : List (Lean.Compiler.LCNF.Alt .impure)) : BridgeM LNIRCode := do
  match alts with
  | [] => return .unreachable
  | [singleAlt] =>
    let cidx ← match singleAlt with
      | .ctorAlt info _ _ => pure info.cidx
      | .alt ctorName params _ _ =>
        if !params.isEmpty then Lean.throwError s!"[lean-native] unsupported constructor payload pattern in {ctorName}"
        lookupCtorIdx ctorName idx
      | .default _ => pure idx
    let saved ← recordActiveCtorForDiscr discr typeName cidx
    let res ← lowerImpureCode singleAlt.getCode
    restoreActiveCtorForDiscr saved
    return res
  | alt :: rest =>
    match alt with
    | .ctorAlt info code _ =>
      let saved ← recordActiveCtorForDiscr discr typeName info.cidx
      let yes ← lowerImpureCode code
      restoreActiveCtorForDiscr saved
      lowerTagBranch condVar info.cidx isBool yes (← lowerImpureAlts discr typeName condVar isBool (idx + 1) rest)
    | .default code => lowerImpureCode code
    | .alt ctorName params code _ =>
      if !params.isEmpty then
        Lean.throwError s!"[lean-native] unsupported constructor payload pattern in {ctorName}"
      let cidx ← lookupCtorIdx ctorName idx
      let saved ← recordActiveCtorForDiscr discr typeName cidx
      let yes ← lowerImpureCode code
      restoreActiveCtorForDiscr saved
      lowerTagBranch condVar cidx isBool yes (← lowerImpureAlts discr typeName condVar isBool (idx + 1) rest)

partial def lowerImpureCode (code : Lean.Compiler.LCNF.Code .impure) : BridgeM LNIRCode := do
  match code with
  | .let decl k =>
    if let .isShared srcFv _ := decl.value then
      return (← lowerIsSharedLet decl.fvarId srcFv k lowerImpureCode)
    let rawDeclTy ← lowerBridgeType decl.type
    if rawDeclTy != .unit then checkBridgeType s!"let binding `{decl.binderName}`" decl.type rawDeclTy true
    let rhs ← lowerImpureLetValue decl.value rawDeclTy
    let isBox := match decl.value with | .box _ _ _ => true | _ => false
    let ty ← inferImpureRhsType rhs rawDeclTy isBox
    let dst ← internFVar decl.fvarId ty true
    recordImpureLetAdtInfo dst decl.value
    return .letBind dst ty rhs (← lowerImpureCode k)
  | .jp decl k =>
    if (← get).allowRcAdt then
      registerRawJoinPoint decl k
      lowerImpureCode k
    else
      lowerJoinPoint decl k lowerImpureCode
  | .jmp fvarId args =>
    if let some spliced ← spliceRawJoinPoint fvarId args lowerImpureCode then return spliced
    lowerJmpInstr fvarId args
  | .inc fvarId n _ _ k _ => lowerRefOp true fvarId n (← lowerImpureCode k)
  | .dec fvarId n _ _ _ k _ => lowerRefOp false fvarId n (← lowerImpureCode k)
  | .del fvarId k _ => lowerRefOp false fvarId 1 (← lowerImpureCode k)
  | .setTag _ _ _ _ => Lean.throwError "[lean-native] unsupported constructor tag mutation"
  | .oset fvarId idx arg k _ => lowerOsetInstr fvarId idx arg k lowerImpureCode
  | .uset .. | .sset .. => Lean.throwError "[lean-native] Unsupported heap field mutation in Stage 1B"
  | .cases c =>
    let (condVar, isBool, adtObjVar?, effTypeName) ← prepareCasesDiscr c.discr c.typeName c.alts
    let altsCode ← lowerImpureAlts c.discr effTypeName condVar isBool 0 (orderAlts c.alts.toList)
    return match adtObjVar? with
      | some objVar => .letBind condVar .i64 (.projTuple objVar 0) altsCode
      | none => altsCode
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
  if metaInfo.isExtern then
    Lean.throwError s!"[lean-native] Unsupported `@[extern]` declaration `{decl.name}` in Stage 1B"
  let isExported := (Lean.getExportNameFor? env decl.name).isSome
  checkEnvConstSignatureM env decl.name arch isExported allowRcAdt
  let initSt : BridgeState := {
    mangledSymbol := metaInfo.mangledSymbol, isSimpleGround := metaInfo.isSimpleGround,
    selfDeclName := decl.name, localDeclNames := localDeclNames, arch := arch, allowRcAdt := allowRcAdt }
  let action : BridgeM LNIRDecl := do
    let (lnirParams, refineRet) ← internSignatureParams decl.name decl.params allowInternalObj isExported
    let rawRetTy ← lowerBridgeType decl.type
    let retTy ← refineRet rawRetTy
    checkBridgeType s!"return type of `{decl.name}`" decl.type retTy (allowInternalObj || allowRcAdt)
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
    (localDeclNames : Array Lean.Name := #[]) (arch : TargetArch := .x86_64)
    (allowRcAdt : Bool := false) : Lean.CoreM LNIRDecl :=
  ingestLCNFDeclGeneric decl lowerImpureCode localDeclNames arch true allowRcAdt

def ingestLCNFMonoDecl (decl : Lean.Compiler.LCNF.Decl .pure)
    (localDeclNames : Array Lean.Name := #[]) (arch : TargetArch := .x86_64)
    (allowRcAdt : Bool := false) : Lean.CoreM LNIRDecl :=
  ingestLCNFDeclGeneric decl lowerPureCode localDeclNames arch false allowRcAdt

def ingestModuleDecls (declNames : Array Lean.Name) (moduleName : String := "LeanNative.Ingested")
    (arch : TargetArch := .x86_64) (allowRcAdt : Bool := false) : Lean.CoreM LNIRModule := do
  let env ← getEnv
  let mut callGraph : Std.HashMap Lean.Name (List Lean.Name) := {}
  let mut decls : List LNIRDecl := []
  let mut rawPairs : List (Lean.Name × String) := []
  for name in declNames do
    if let some impureDecl ← Lean.Compiler.LCNF.getLocalImpureDecl? name then
      if let .code c := impureDecl.value then
        callGraph := callGraph.insert name (collectCodeLocalCallees declNames c)
      let d ← ingestLCNFImpureDecl impureDecl declNames arch allowRcAdt
      decls := decls ++ [d]
      rawPairs := rawPairs ++ [(name, d.name)]
    else if let some monoDecl ← Lean.Compiler.LCNF.getMonoDecl? name then
      if let .code c := monoDecl.value then
        callGraph := callGraph.insert name (collectCodeLocalCallees declNames c)
      let d ← ingestLCNFMonoDecl monoDecl declNames arch allowRcAdt
      decls := decls ++ [d]
      rawPairs := rawPairs ++ [(name, d.name)]
  if declsHaveMutualCycle callGraph then
    Lean.throwError s!"[lean-native] unsupported self-tail recursion / mutual recursion in {moduleName}: no qualified loop lowering"
  let rawMod : LNIRModule := { moduleName := moduleName, decls := decls }
  validateIngestedModule rawMod
  let inlined := normalizeAndInlineLocalDefs rawMod allowRcAdt
  filterNonInternalHelperDecls env rawPairs arch inlined allowRcAdt

def ingestAllLocalDecls (moduleName : String := "LeanNative.Ingested")
    (arch : TargetArch := .x86_64) (allowRcAdt : Bool := false) : Lean.CoreM LNIRModule := do
  let impureNames ← Lean.Compiler.LCNF.getLocalImpureDecls
  let env ← getEnv
  let filteredImpure := impureNames.filter (fun n => !isCompilerGeneratedAuxDecl env n)
  let extraNames := env.constants.map₂.foldl (fun acc name _ =>
    if impureNames.contains name || isCompilerGeneratedAuxDecl env name then acc else acc.push name) #[]
  ingestModuleDecls (filteredImpure ++ extraNames) moduleName arch allowRcAdt

end LeanNative.IR
