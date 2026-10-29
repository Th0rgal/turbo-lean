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
  ( lookupCanonicalTypedBinOp? fnName ).map Prod.snd

def canonicalUIntCastMask? (fnName : Lean.Name) (argTys : List LNIRType) (retTy : LNIRType)
    (arch : TargetArch := .x86_64) : Option UInt64 := do
  let usizeEntry : List (Lean.Name × LNIRType × UInt64) :=
    if archSupportsUSize arch then [(``USize, .usize, archUSizeMask arch)] else []
  let types : List (Lean.Name × LNIRType × UInt64) :=
    [(``UInt8, .i8, 255), (``UInt16, .i16, 65535),
     (``UInt32, .i32, 4294967295), (``UInt64, .i64, 18446744073709551615)] ++ usizeEntry
  types.findSome? fun (src, srcTy, _) => types.findSome? fun (dst, dstTy, dstMask) =>
    if src != dst && fnName == Lean.Name.str src ("to" ++ dst.toString) &&
        argTys == [srcTy] && retTy == dstTy then
      some dstMask
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
          if !argTys.isEmpty && argTys != [opTy, opTy] then none
          else .scalar <$> lowerScalarIntrinsicExpr? op lhs rhs opTy retTy arch
        | none => lowerBoolBinIntrinsic? fnName lhs rhs argTys retTy
  | [arg] =>
    if isLocal then none else
    match canonicalUIntCastMask? fnName argTys retTy arch with
    | some dstMask =>
      let srcMask := match argTys with
        | [sTy] => (scalarWidthMask? sTy arch).getD 0xFFFFFFFFFFFFFFFF
        | _ => 0xFFFFFFFFFFFFFFFF
      let effMask := if srcMask < dstMask then srcMask else dstMask
      some (.scalar (.binOp .bitAnd (.var arg) (.constU64 effMask)))
    | none => lowerUnaryScalarIntrinsic? fnName arg argTys retTy arch
  | _ => none

def lowerNamedCall (fnName : Lean.Name) (args : Array (Lean.Compiler.LCNF.Arg pu)) (retTy : LNIRType) : BridgeM LNIRExpr := do
  let argVars ← args.toList.mapM lowerArg
  let argTys ← argVars.mapM getVarType
  let env ← getEnv
  let st ← get
  let isLocal := st.localDeclNames.contains fnName || fnName == st.selfDeclName
  match tryLowerIntrinsicCall env fnName argVars retTy argTys isLocal st.arch with
  | some intrinsicExpr => return intrinsicExpr
  | none =>
    if !isLocal || Lean.isExtern env fnName then
      Lean.throwError s!"[lean-native] Unsupported external or non-scalar call `{fnName}` in Stage 1B"
    return .call (mangleDeclNameInEnv env fnName) argVars retTy false

def lowerCtorScalarValue (ctorName : Lean.Name) (cidx : Nat) (args : Array (Lean.Compiler.LCNF.Arg pu))
    (retTy : LNIRType) : BridgeM LNIRExpr := do
  if !args.isEmpty then
    Lean.throwError s!"[lean-native] Unsupported payload-carrying constructor `{ctorName}` in Stage 1B scalar subset"
  if ctorName == ``Bool.false then
    return .scalar (if retTy == .i1 then .constBool false else .constU64 0)
  if ctorName == ``Bool.true then
    return .scalar (if retTy == .i1 then .constBool true else .constU64 1)
  if ctorName == ``Unit.unit || ctorName == ``PUnit.unit then
    return .scalar (.constU64 0)
  let env ← getEnv
  match env.find? ctorName with
  | some (.ctorInfo cval) =>
    if cval.numFields == 0 && (retTy == .i8 || retTy == .i16 || retTy == .i1) then
      return .scalar (if retTy == .i1 then .constBool (cidx != 0) else .constU64 cidx.toUInt64)
    Lean.throwError s!"[lean-native] Unsupported constructor `{ctorName}`"
  | _ => Lean.throwError s!"[lean-native] Unknown constructor `{ctorName}`"

def lowerImpureLetValue (lv : Lean.Compiler.LCNF.LetValue .impure) (retTy : LNIRType) : BridgeM LNIRExpr := do
  match lv with
  | .lit litVal => lowerLitValueM litVal retTy
  | .erased => return .scalar (.constU64 0)
  | .fvar fvarId args =>
    if !args.isEmpty then
      Lean.throwError "[lean-native] Unsupported indirect / higher-order function call"
    if (← get).localFunMap.contains fvarId then
      Lean.throwError "[lean-native] Unsupported escaping local function value"
    let v ← internFVar fvarId
    return .scalar (.var v)
  | .ctor ctorInfo args _ => lowerCtorScalarValue ctorInfo.name ctorInfo.cidx args retTy
  | .fap fnName args _ => lowerNamedCall fnName args retTy
  | .pap fnName _ _ => Lean.throwError s!"[lean-native] Unsupported partial application (`pap {fnName}`) in Stage 1B"
  | .reuse .. | .reset .. | .box .. | .unbox .. | .isShared .. | .oproj .. | .uproj .. | .sproj .. =>
    Lean.throwError "[lean-native] Unsupported heap object / boxing / projection instruction in Stage 1B"

def lowerTagBranch (condVar : VarId) (cidx : Nat) (yes no : LNIRCode) : BridgeM LNIRCode := do
  let condTy ← getVarType condVar
  if condTy == .i1 then
    return if cidx == 0 then .ite condVar no yes else if cidx == 1 then .ite condVar yes no else no
  let cmpVar ← freshBridgeVar .i1
  return .letBind cmpVar .i1 (.scalar (.binOp .eq (.var condVar) (.constU64 cidx.toUInt64))) (.ite cmpVar yes no)

mutual
partial def lowerImpureAlts (condVar : VarId) (alts : List (Lean.Compiler.LCNF.Alt .impure)) : BridgeM LNIRCode := do
  match alts with
  | [] => return .unreachable
  | [singleAlt] =>
    if let .alt ctorName _ _ _ := singleAlt then
      Lean.throwError s!"[lean-native] Unsupported payload constructor case `{ctorName}` in Stage 1B"
    lowerImpureCode singleAlt.getCode
  | alt :: rest =>
    match alt with
    | .ctorAlt info code _ =>
      lowerTagBranch condVar info.cidx (← lowerImpureCode code) (← lowerImpureAlts condVar rest)
    | .default code => lowerImpureCode code
    | .alt ctorName _ _ _ =>
      Lean.throwError s!"[lean-native] Unsupported payload constructor case `{ctorName}` in Stage 1B"

partial def lowerImpureCode (code : Lean.Compiler.LCNF.Code .impure) : BridgeM LNIRCode := do
  match code with
  | .let decl k =>
    let ty ← lowerBridgeType decl.type
    if ty != .unit then checkBridgeType s!"let binding `{decl.binderName}`" decl.type ty
    let val ← lowerImpureLetValue decl.value ty
    let dst ← internFVar decl.fvarId ty
    return .letBind dst ty val (← lowerImpureCode k)
  | .jp decl k => lowerJoinPoint decl k lowerImpureCode
  | .jmp fvarId args => lowerJmpInstr fvarId args
  | .cases c =>
    let condVar ← internFVar c.discr
    let condTy ← getVarType condVar
    if !isSupportedStage1BScalarType condTy (← get).arch then
      Lean.throwError s!"[lean-native] Unsupported cases scrutinee type `{c.typeName}`"
    lowerImpureAlts condVar (orderAlts c.alts.toList)
  | .return fvarId =>
    if (← get).localFunMap.contains fvarId then
      Lean.throwError "[lean-native] Unsupported returning local closure"
    return .ret (← internFVar fvarId)
  | .unreach _ => return .unreachable
  | .inc .. | .dec .. | .del .. | .oset .. | .uset .. | .sset .. | .setTag .. =>
    Lean.throwError "[lean-native] Unsupported heap RC / mutation / setTag instruction in Stage 1B"
end

def lowerPureLetValue (lv : Lean.Compiler.LCNF.LetValue .pure) (retTy : LNIRType) : BridgeM LNIRExpr := do
  match lv with
  | .lit litVal => lowerLitValueM litVal retTy
  | .erased => return .scalar (.constU64 0)
  | .proj typeName _ _ _ => Lean.throwError s!"[lean-native] Unsupported struct projection on `{typeName}` in Stage 1B"
  | .const declName _ args _ =>
    let env ← getEnv
    match env.find? declName with
    | some (.ctorInfo cval) => lowerCtorScalarValue declName cval.cidx args retTy
    | _ => lowerNamedCall declName args retTy
  | .fvar fvarId args =>
    if args.isEmpty then
      if (← get).localFunMap.contains fvarId then
        Lean.throwError "[lean-native] Unsupported escaping local function value"
      return .scalar (.var (← internFVar fvarId))
    else
      Lean.throwError "[lean-native] Unsupported indirect / higher-order function call"

def lookupCtorIdx (ctorName : Lean.Name) (fallbackIdx : Nat) : BridgeM Nat := do
  match (← getEnv).find? ctorName with
  | some (.ctorInfo cval) => return cval.cidx
  | _ => return fallbackIdx

mutual
partial def lowerPureAlts (condVar : VarId) (idx : Nat) (alts : List (Lean.Compiler.LCNF.Alt .pure)) : BridgeM LNIRCode := do
  let emitTagBranch (cidx : Nat) (code : Lean.Compiler.LCNF.Code .pure) (rest : List (Lean.Compiler.LCNF.Alt .pure)) : BridgeM LNIRCode := do
    lowerTagBranch condVar cidx (← lowerPureCode code) (← lowerPureAlts condVar (idx + 1) rest)
  match alts with
  | [] => return .unreachable
  | [singleAlt] =>
    if let .alt ctorName params _ _ := singleAlt then
      if !params.isEmpty then
        Lean.throwError s!"[lean-native] Unsupported payload constructor case `{ctorName}` in Stage 1B"
    lowerPureCode singleAlt.getCode
  | alt :: rest =>
    match alt with
    | .alt ctorName params code _ =>
      if !params.isEmpty then
        Lean.throwError s!"[lean-native] Unsupported payload constructor case `{ctorName}` in Stage 1B"
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
        let dst ← internFVar decl.fvarId ty
        let kCode ← lowerPureCode k
        return ← inlineLocalFunCode (pIds.zip argVars) dst ty kCode fBody
    let val ← lowerPureLetValue decl.value ty
    let dst ← internFVar decl.fvarId ty
    return .letBind dst ty val (← lowerPureCode k)
  | .fun decl k _ => lowerLocalFunDecl decl k lowerPureCode
  | .jp decl k => lowerJoinPoint decl k lowerPureCode
  | .jmp fvarId args => lowerJmpInstr fvarId args
  | .cases c =>
    let condVar ← internFVar c.discr
    let condTy ← getVarType condVar
    if !isSupportedStage1BScalarType condTy (← get).arch then
      Lean.throwError s!"[lean-native] Unsupported cases scrutinee type `{c.typeName}`"
    lowerPureAlts condVar 0 (orderAlts c.alts.toList)
  | .return fvarId =>
    if (← get).localFunMap.contains fvarId then
      Lean.throwError "[lean-native] Unsupported returning local closure"
    return .ret (← internFVar fvarId)
  | .unreach _ => return .unreachable
end

def ingestLCNFDeclGeneric {pu} (decl : Lean.Compiler.LCNF.Decl pu)
    (lowerCodeFn : Lean.Compiler.LCNF.Code pu → BridgeM LNIRCode)
    (localDeclNames : Array Lean.Name := #[])
    (arch : TargetArch := .x86_64) : Lean.CoreM LNIRDecl := do
  let env ← getEnv
  if let some cinfo := env.find? decl.name then
    if exprUsesSignedScalarType cinfo.type || (cinfo.value?.any exprUsesSignedScalarType) then
      Lean.throwError s!"[lean-native] Unsupported signed integer type (`Int*` / `ISize`) in `{decl.name}`"
  let metaInfo := getLCNFDeclMetadata env decl.name
  let isDeclExtern := metaInfo.isExtern
  if isDeclExtern then
    Lean.throwError s!"[lean-native] Unsupported `@[extern]` declaration `{decl.name}` in Stage 1B"
  let initSt : BridgeState := {
    mangledSymbol := metaInfo.mangledSymbol
    isSimpleGround := metaInfo.isSimpleGround
    selfDeclName := decl.name
    localDeclNames := localDeclNames
    arch := arch }
  let action : BridgeM LNIRDecl := do
    let mut lnirParams : List LNIRParam := []
    for p in decl.params do
      let pTy ← lowerBridgeType p.type
      checkBridgeType s!"parameter `{p.binderName}` of `{decl.name}`" p.type pTy
      let vid ← internFVar p.fvarId pTy
      lnirParams := lnirParams ++ [{ id := vid, name := p.binderName.toString, ty := pTy, borrow := p.borrow }]
    let retTy ← lowerBridgeType decl.type
    checkBridgeType s!"return type of `{decl.name}`" decl.type retTy
    match decl.value with
    | .code c =>
      let env ← getEnv
      let body ←
        if let some intrExpr := tryLowerGfSimdIntrinsic env decl.name (lnirParams.map (·.id)) retTy (lnirParams.map (·.ty)) then do
          let retVar ← freshBridgeVar retTy
          pure (.letBind retVar retTy intrExpr (.ret retVar))
        else
          lowerCodeFn c
      return {
        name := metaInfo.mangledSymbol
        params := lnirParams
        retTy := retTy
        body := body
        assurance := .tested
        isGpuCand := lnirParams.all (fun p => p.ty.isGpuCompatible) && retTy.isGpuCompatible }
    | .extern _ =>
      Lean.throwError s!"[lean-native] Unsupported `@[extern]` declaration `{decl.name}` in Stage 1B"
  Prod.fst <$> action.run initSt

def ingestLCNFImpureDecl (decl : Lean.Compiler.LCNF.Decl .impure)
    (localDeclNames : Array Lean.Name := #[]) (arch : TargetArch := .x86_64) : Lean.CoreM LNIRDecl :=
  ingestLCNFDeclGeneric decl lowerImpureCode localDeclNames arch

def ingestLCNFMonoDecl (decl : Lean.Compiler.LCNF.Decl .pure)
    (localDeclNames : Array Lean.Name := #[]) (arch : TargetArch := .x86_64) : Lean.CoreM LNIRDecl :=
  ingestLCNFDeclGeneric decl lowerPureCode localDeclNames arch

def ingestModuleDecls (declNames : Array Lean.Name) (moduleName : String := "LeanNative.Ingested")
    (arch : TargetArch := .x86_64) : Lean.CoreM LNIRModule := do
  let env ← getEnv
  let mut decls : List LNIRDecl := []
  let mut rawPairs : List (Lean.Name × String) := []
  for name in declNames do
    if let some impureDecl ← Lean.Compiler.LCNF.getLocalImpureDecl? name then
      let d ← ingestLCNFImpureDecl impureDecl declNames arch
      decls := decls ++ [d]
      rawPairs := rawPairs ++ [(name, d.name)]
    else if let some monoDecl ← Lean.Compiler.LCNF.getMonoDecl? name then
      let d ← ingestLCNFMonoDecl monoDecl declNames arch
      decls := decls ++ [d]
      rawPairs := rawPairs ++ [(name, d.name)]
  let rawMod : LNIRModule := { moduleName := moduleName, decls := decls }
  validateIngestedModule rawMod
  let inlined := normalizeAndInlineLocalDefs rawMod
  return filterNonInternalHelperDecls env rawPairs inlined

def ingestAllLocalDecls (moduleName : String := "LeanNative.Ingested")
    (arch : TargetArch := .x86_64) : Lean.CoreM LNIRModule := do
  let impureNames ← Lean.Compiler.LCNF.getLocalImpureDecls
  let env ← getEnv
  let filteredImpure := impureNames.filter (fun n => !isCompilerGeneratedAuxDecl env n)
  let extraNames := env.constants.map₂.foldl (fun acc name _ =>
    if impureNames.contains name || isCompilerGeneratedAuxDecl env name then acc else acc.push name) #[]
  ingestModuleDecls (filteredImpure ++ extraNames) moduleName arch

end LeanNative.IR
