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

def lowerNamedCall (fnName : Lean.Name) (args : Array (Lean.Compiler.LCNF.Arg pu)) (retTy : LNIRType) : BridgeM LNIRExpr := do
  let env ← getEnv
  let st ← get
  if fnName == ``leanNativeKeepEffect && args.size >= 4 then
    match args[3]! with
    | .fvar valId => return .scalar (.var (← internFVar valId))
    | _ => return .scalar (.constU64 0)
  match fnName with
  | .str _ leaf =>
    if leaf == "readU8" || leaf == "readMutU8" || leaf == "readU32" || leaf == "readMutU16" then
      if args.size >= 2 then
        let elemTy : LNIRType := if leaf == "readU32" then .i32 else if leaf == "readMutU16" then .i16 else .i8
        let pVar ← lowerArg args[args.size - 2]!
        let idxVar ← lowerArg args[args.size - 1]!
        return .rawLoad pVar idxVar elemTy
  | _ => pure ()
  let isLocal := st.localDeclNames.contains fnName || fnName == st.selfDeclName
  let isCanonicalSliceCall :=
    !isLocal &&
    (fnName == ``ByteArray.usize || fnName == ``FloatArray.usize ||
     fnName == ``ByteArray.uget || fnName == ``FloatArray.uget ||
     (st.arch.isFreestandingEmbedded && fnName == ``ByteArray.get!))
  let argVars ← args.toList.mapM (fun a => do
    match a with
    | .fvar fvarId =>
      if ((← get).localFunMap.contains fvarId) then
        Lean.throwError "[lean-native] Unsupported higher-order / escaping local function value"
      let vid ← internFVar fvarId
      let vTy ← getVarType vid
      if !(isSupportedParamOrRetType vTy (← get).arch (isLocal || isCanonicalSliceCall) || vTy == .unit ||
           (isLocal && (vTy == .objPtr || vTy == .taggedPtr))) then
        Lean.throwError s!"[lean-native] Unsupported non-scalar argument of type `{reprStr vTy}`"
      return vid
    | .erased => freshBridgeVar .unit
    | .type .. => freshBridgeVar .unit)
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

partial def normalizeUnitLoopStep (dummyAccVar : VarId) : LNIRCode → LNIRCode
  | .letBind d t v k => .letBind d t v (normalizeUnitLoopStep dummyAccVar k)
  | .rawStore pv iv vv et k => .rawStore pv iv vv et (normalizeUnitLoopStep dummyAccVar k)
  | .incRef ov c k => .incRef ov c (normalizeUnitLoopStep dummyAccVar k)
  | .decRef ov c k => .decRef ov c (normalizeUnitLoopStep dummyAccVar k)
  | .ite cv t e => .ite cv (normalizeUnitLoopStep dummyAccVar t) (normalizeUnitLoopStep dummyAccVar e)
  | .seqFor iv lv hv av ai aty s k => .seqFor iv lv hv av ai aty s (normalizeUnitLoopStep dummyAccVar k)
  | .parFor ov lv ins et kern k => .parFor ov lv ins et kern (normalizeUnitLoopStep dummyAccVar k)
  | .ret _ => .ret dummyAccVar
  | .unreachable => .unreachable

/-- Pointer of the mutable buffer value given to a buffer loop. -/
def trackedBuf (leaf : String) : Lean.Compiler.LCNF.Arg .pure → BridgeM VarId
  | .fvar f => do
    let some v := (← get).bufPtr[f]?
      | Lean.throwError s!"[lean-native] `{leaf}` buffer argument is not a tracked mutable buffer value"
    return v
  | _ => Lean.throwError s!"[lean-native] `{leaf}` buffer argument must be a variable"

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

/-- Lower a loop step. `loopArgs` are the variables given to the step parameters after the index
    (the buffer pointer and/or the accumulator); `dummyAcc?` is set for a loop without accumulator. -/
partial def lowerForRangeStepM (stepFVar : Lean.FVarId) (idxVar : VarId) (loopArgs : List VarId)
    (dummyAcc? : Option VarId) : BridgeM LNIRCode := do
  let st ← get
  let idx32Var ← freshBridgeVar .i32
  let maskIdx (body : LNIRCode) : LNIRCode :=
    .letBind idx32Var .i32 (.scalar (.binOp .bitAnd (.var idxVar) (.constU64 0xFFFFFFFF))) body
  let stepArgs := idx32Var :: loopArgs
  let rawStep ←
    if let some (pIds, fBody) := st.localFunMap[stepFVar]? then do
      if pIds.length != stepArgs.length then
        Lean.throwError s!"[lean-native] Invalid `forRange` step closure arity: expected {stepArgs.length}, got {pIds.length}"
      freshenJoinPointCode ((pIds.zip stepArgs).foldl (fun m (o, n) => m.insert o n) {}) fBody
    else if let some (lamName, capArgs) := st.liftedClosureMap[stepFVar]? then do
      let some lamDecl ← Lean.Compiler.LCNF.getMonoDecl? lamName
        | Lean.throwError s!"[lean-native] Missing mono declaration for lifted loop closure `{lamName}`"
      let .code lamBody := lamDecl.value
        | Lean.throwError s!"[lean-native] Unsupported extern lifted loop closure `{lamName}`"
      if capArgs.size + stepArgs.length != lamDecl.params.size then
        Lean.throwError s!"[lean-native] Lifted loop closure `{lamName}` parameter mismatch ({capArgs.size} + {stepArgs.length} vs {lamDecl.params.size})"
      let capVars ← capArgs.toList.mapM lowerArg
      for (lp, mv) in lamDecl.params.toList.zip (capVars ++ stepArgs) do
        modify fun s => { s with fvarToVar := s.fvarToVar.insert lp.fvarId mv }
      lowerPureCode lamBody
    else
      Lean.throwError s!"[lean-native] Unsupported `forRange` step argument `{stepFVar.name}` (must be an inline lambda or non-escaping closure)"
  let masked := maskIdx rawStep
  return match dummyAcc? with
    | some dummy => normalizeUnitLoopStep dummy masked
    | none => masked

partial def lowerPureCode (code : Lean.Compiler.LCNF.Code .pure) : BridgeM LNIRCode := do
  match code with
  | .let decl k =>
    let rawLetTy ← lowerBridgeType decl.type
    let envCur ← getEnv
    let ty :=
      if rawLetTy == .usize then
        match decl.value with
        | .const fnName _ _ _ =>
          match envCur.find? fnName with
          | some cinfo =>
            match lowerImpureType cinfo.type.getForallBody (some envCur) with
            | .rawPtr et => .rawPtr et
            | _ => rawLetTy
          | none => rawLetTy
        | _ => rawLetTy
      else rawLetTy
    if let .const fnName _ args _ := decl.value then
      if fnName == ``leanNativeKeepEffect && args.size >= 4 then
        if let .fvar valId := args[3]! then
          let valVar ← internFVar valId
          modify fun st => { st with
            fvarToVar := st.fvarToVar.insert decl.fvarId valVar
            bufPtr := match st.bufPtr[valId]? with
              | some b => st.bufPtr.insert decl.fvarId b
              | none => st.bufPtr }
          return ← lowerPureCode k
        else
          let zv ← internFVar decl.fvarId .unit true
          return .letBind zv .unit (.scalar (.constU64 0)) (← lowerPureCode k)
      match fnName with
      | .str _ leaf =>
        if (leaf == "writeU8" || leaf == "writeU16") && args.size >= 3 then
          let elemTy : LNIRType := if leaf == "writeU16" then .i16 else .i8
          let pVar ← lowerArg args[args.size - 3]!
          let idxVar ← lowerArg args[args.size - 2]!
          let valVar ← lowerArg args[args.size - 1]!
          modify fun st => { st with
            fvarToVar := st.fvarToVar.insert decl.fvarId pVar, bufPtr := st.bufPtr.insert decl.fvarId pVar }
          return .rawStore pVar idxVar valVar elemTy (← lowerPureCode k)
        if (leaf == "forRangeU64" || leaf == "forRangeU32") && args.size >= 4 then
          let accTy : LNIRType := if leaf == "forRangeU32" then .i32 else .i64
          let loVar ← lowerArg args[args.size - 4]!
          let hiVar ← lowerArg args[args.size - 3]!
          let initVar ← lowerArg args[args.size - 2]!
          let .fvar stepFVar := args[args.size - 1]!
            | Lean.throwError s!"[lean-native] `{leaf}` step argument must be a function variable"
          let idxVar ← freshBridgeVar .i64
          let accVar ← internFVar decl.fvarId accTy true
          let stepCode ← lowerForRangeStepM stepFVar idxVar [accVar] none
          let kCode ← lowerPureCode k
          return .seqFor idxVar loVar hiVar accVar initVar accTy stepCode kCode
        if leaf == "forRangeUnit" && args.size >= 3 then
          let loVar ← lowerArg args[args.size - 3]!
          let hiVar ← lowerArg args[args.size - 2]!
          let .fvar stepFVar := args[args.size - 1]!
            | Lean.throwError s!"[lean-native] `forRangeUnit` step argument must be a function variable"
          let initVar ← freshBridgeVar .i64
          let idxVar ← freshBridgeVar .i64
          let accVar ← freshBridgeVar .i64
          let _ ← internFVar decl.fvarId .unit true
          modify fun st => { st with fvarToVar := st.fvarToVar.insert decl.fvarId accVar }
          let stepCode ← lowerForRangeStepM stepFVar idxVar [] (some initVar)
          let kCode ← lowerPureCode k
          return .letBind initVar .i64 (.scalar (.constU64 0))
            (.seqFor idxVar loVar hiVar accVar initVar .i64 stepCode kCode)
        -- Loop carrying a mutable buffer: the buffer is the caller's pointer on every
        -- iteration, so the loop carries no value for it.
        if (leaf == "forRangeBytes" || leaf == "forRangeU16s") && args.size >= 4 then
          let loVar ← lowerArg args[args.size - 4]!
          let hiVar ← lowerArg args[args.size - 3]!
          let bufVar ← trackedBuf leaf args[args.size - 2]!
          let .fvar stepFVar := args[args.size - 1]!
            | Lean.throwError s!"[lean-native] `{leaf}` step argument must be a function variable"
          let initVar ← freshBridgeVar .i64
          let idxVar ← freshBridgeVar .i64
          let accVar ← freshBridgeVar .i64
          modify fun st => { st with
            fvarToVar := st.fvarToVar.insert decl.fvarId bufVar, bufPtr := st.bufPtr.insert decl.fvarId bufVar }
          let stepCode ← lowerForRangeStepM stepFVar idxVar [bufVar] (some initVar)
          let kCode ← lowerPureCode k
          return .letBind initVar .i64 (.scalar (.constU64 0))
            (.seqFor idxVar loVar hiVar accVar initVar .i64 stepCode kCode)
        -- Loop carrying a mutable buffer and a scalar: only the scalar is a loop value.
        if (leaf == "forRangeBytesU32" || leaf == "forRangeBytesU64") && args.size >= 5 then
          let accTy : LNIRType := if leaf == "forRangeBytesU32" then .i32 else .i64
          let loVar ← lowerArg args[args.size - 5]!
          let hiVar ← lowerArg args[args.size - 4]!
          let bufVar ← trackedBuf leaf args[args.size - 3]!
          let initVar ← lowerArg args[args.size - 2]!
          let .fvar stepFVar := args[args.size - 1]!
            | Lean.throwError s!"[lean-native] `{leaf}` step argument must be a function variable"
          let idxVar ← freshBridgeVar .i64
          let accVar ← internFVar decl.fvarId accTy true
          modify fun st => { st with bufPtr := st.bufPtr.insert decl.fvarId bufVar }
          let stepCode ← lowerForRangeStepM stepFVar idxVar [bufVar, accVar] none
          let kCode ← lowerPureCode k
          return .seqFor idxVar loVar hiVar accVar initVar accTy stepCode kCode
      | _ => pure ()
      -- `(buffer, scalar)`: the pair is the scalar; the buffer is the caller's pointer.
      if fnName == ``Prod.mk && mutBufKindOf decl.type == .pair && args.size >= 4 then
        if let (.fvar bufId, .fvar valId) := (args[2]!, args[3]!) then
          let bufVar ← internFVar bufId
          let valVar ← internFVar valId
          modify fun st => { st with
            fvarToVar := st.fvarToVar.insert decl.fvarId valVar, bufPtr := st.bufPtr.insert decl.fvarId bufVar }
          return ← lowerPureCode k
        Lean.throwError s!"[lean-native] unsupported `(buffer, value)` pair `{decl.binderName}`: both components must be variables"
      -- Call of a function that returns its buffer: the callee returns nothing for it.
      if mutBufKindOf decl.type != .none then
        let bufPtr := (← get).bufPtr
        let some bufVar := args.findSome? fun
            | .fvar f => bufPtr[f]?
            | _ => none
          | Lean.throwError s!"[lean-native] `{fnName}` returns a mutable buffer it was not given"
        modify fun st => { st with bufPtr := st.bufPtr.insert decl.fvarId bufVar }
        if mutBufKindOf decl.type == .buf then
          let rhs ← lowerNamedCall fnName args .unit
          modify fun st => { st with fvarToVar := st.fvarToVar.insert decl.fvarId bufVar }
          return .letBind (← freshBridgeVar .unit) .unit rhs (← lowerPureCode k)
      if isClosureOrRuntimeNatExpr decl.type then
        if let some lamDecl ← Lean.Compiler.LCNF.getMonoDecl? fnName then
          if args.size <= lamDecl.params.size then
            modify fun st => { st with liftedClosureMap := st.liftedClosureMap.insert decl.fvarId (fnName, args) }
            return ← lowerPureCode k
    -- Projection or copy of a buffer value: `p.1` is the caller's pointer, `p.2` the scalar.
    let srcBuf? : Option (Lean.FVarId × Bool) := match decl.value with
      | .proj _ idx f _ => some (f, idx == 0)
      | .fvar f args => if args.isEmpty then some (f, mutBufKindOf decl.type == .buf) else none
      | _ => none
    if let some (f, takeBuf) := srcBuf? then
      if let some bufVar := (← get).bufPtr[f]? then
        let v ← if takeBuf then pure bufVar else internFVar f
        modify fun st => { st with
          fvarToVar := st.fvarToVar.insert decl.fvarId v
          bufPtr := if mutBufKindOf decl.type == .none then st.bufPtr else st.bufPtr.insert decl.fvarId bufVar }
        return ← lowerPureCode k
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
    if (← get).retBufUnit then
      let u ← freshBridgeVar .unit
      return .letBind u .unit (.scalar (.constU64 0)) (.ret u)
    return .ret (← internFVar fvarId)
  | .unreach _ => return .unreachable
end

def ingestLCNFDeclGenericWithState {pu} (decl : Lean.Compiler.LCNF.Decl pu)
    (lowerCodeFn : Lean.Compiler.LCNF.Code pu → BridgeM LNIRCode)
    (localDeclNames : Array Lean.Name := #[]) (arch : TargetArch := .x86_64)
    (allowInternalObj : Bool := false) (allowRcAdt : Bool := false) : Lean.CoreM (LNIRDecl × BridgeState) := do
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
    let envParamTys ← collectDeclExplicitParamTypesM env decl.name
    let mut lnirParams : List LNIRParam := []
    let mut pIdx : Nat := 0
    for p in decl.params do
      let rawPTy ← lowerBridgeType p.type
      let pTy :=
        if !isStage1DHeap && (rawPTy == .objPtr || rawPTy == .taggedPtr) then
          match envParamTys[pIdx]? with
          | some (.tuple fs) => .tuple fs
          | some (.sarray .i8) => .sarray .i8
          | some (.sarray .f64) => .sarray .f64
          | _ => rawPTy
        else if rawPTy == .usize then
          match envParamTys[pIdx]? with
          | some (.rawPtr et) => .rawPtr et
          | _ => rawPTy
        else rawPTy
      checkBridgeType s!"parameter `{p.binderName}` of `{decl.name}`" p.type pTy allowInternalObj (!isExported || arch.isFreestandingEmbedded)
      let vid ← internFVar p.fvarId pTy true
      if mutBufKindOf p.type == .buf then
        modify fun st => { st with bufPtr := st.bufPtr.insert p.fvarId vid }
      lnirParams := lnirParams ++ [{ id := vid, name := p.binderName.toString, ty := pTy, borrow := p.borrow || isSupportedSliceType pTy }]
      pIdx := pIdx + 1
    let rawRetTy ← lowerBridgeType (decl.type.getForallBody)
    let retsBuf := mutBufKindOf decl.type.getForallBody == .buf
    modify fun st => { st with retBufUnit := retsBuf }
    let retTy :=
      if retsBuf then .unit
      else if rawRetTy == .usize then
        match env.find? decl.name with
        | some cinfo =>
          match lowerImpureType cinfo.type.getForallBody (some env) with
          | .rawPtr et => .rawPtr et
          | _ => rawRetTy
        | none => rawRetTy
      else rawRetTy
    if retTy != .unit then
      checkBridgeType s!"return type of `{decl.name}`" (decl.type.getForallBody) retTy allowInternalObj
    match decl.value with
    | .code c =>
      let env ← getEnv
      let body ←
        if let some intrExpr := tryLowerGfSimdIntrinsic env decl.name (lnirParams.map (·.id)) retTy (lnirParams.map (·.ty)) then do
          let retVar ← freshBridgeVar retTy
          pure (.letBind retVar retTy intrExpr (.ret retVar))
        else if codeHasSelfTailCall decl.name c then
          Lean.throwError s!"[lean-native] unsupported self-tail recursion in {decl.name}: no qualified loop lowering"
        else do
          let rawBody ← lowerCodeFn c
          let candBody ← compressScalarCode rawBody
          let rawRetTy := match inferReturnedType rawBody with | some (.tuple fs) => .tuple fs | _ => retTy
          let candRetTy := match inferReturnedType candBody with | some (.tuple fs) => .tuple fs | _ => retTy
          let baseDecl : LNIRDecl := { name := metaInfo.mangledSymbol, params := lnirParams, retTy := rawRetTy, body := rawBody }
          let candDecl : LNIRDecl := { baseDecl with retTy := candRetTy, body := candBody }
          if candBody != rawBody && (LeanNative.Proofs.validateTranslationDecl baseDecl candDecl 64).passed then
            pure candBody
          else
            pure rawBody
      let effRetTy := match inferReturnedType body with | some (.tuple fs) => .tuple fs | _ => retTy
      return {
        name := metaInfo.mangledSymbol, params := lnirParams, retTy := effRetTy, body := body,
        assurance := .tested,
        isGpuCand := lnirParams.all (fun p => p.ty.isGpuCompatible) && effRetTy.isGpuCompatible }
    | .extern _ =>
      Lean.throwError s!"[lean-native] Unsupported `@[extern]` declaration `{decl.name}` in Stage 1B"
  action.run initSt

def ingestLCNFDeclGeneric (decl : Lean.Compiler.LCNF.Decl pu) (lowerCodeFn : Lean.Compiler.LCNF.Code pu → BridgeM LNIRCode)
    (localDeclNames : Array Lean.Name := #[]) (arch : TargetArch := .x86_64)
    (allowInternalObj : Bool := false) (allowRcAdt : Bool := false) : Lean.CoreM LNIRDecl :=
  Prod.fst <$> ingestLCNFDeclGenericWithState decl lowerCodeFn localDeclNames arch allowInternalObj allowRcAdt

def ingestLCNFImpureDecl (decl : Lean.Compiler.LCNF.Decl .impure)
    (localDeclNames : Array Lean.Name := #[]) (arch : TargetArch := .x86_64) (allowRcAdt : Bool := false) : Lean.CoreM LNIRDecl :=
  ingestImpureDeclViaReal decl localDeclNames arch allowRcAdt

def ingestLCNFMonoDecl (decl : Lean.Compiler.LCNF.Decl .pure)
    (localDeclNames : Array Lean.Name := #[]) (arch : TargetArch := .x86_64) : Lean.CoreM LNIRDecl := do
  let (d, endSt) ← ingestLCNFDeclGenericWithState decl lowerPureCode localDeclNames arch false
  attachBaseDeclFactsM decl.name (extractPureDeclFactsWithBridgeState decl endSt d)

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
