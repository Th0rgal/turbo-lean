import Lean
import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.Passes
import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.ToImpureType
import Lean.Compiler.LCNF.SimpleGroundExpr
import Lean.Compiler.NameMangling
import Lean.Compiler.ExternAttr
import Std.Data.HashSet
import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.IR.Codec
import LeanNative.IR.LCNF
import LeanNative.IR.RealLCNFBridge
import LeanNative.Transform.EqSat
import LeanNative.Frontend.ProofRetention

set_option autoImplicit true

namespace LeanNative.IR

open Lean
open Lean.Compiler.LCNF

def hasSimpleGroundDecl (env : Lean.Environment) (declName : Lean.Name) : Bool :=
  Lean.Compiler.LCNF.isSimpleGroundDecl env declName

def mangleDeclName (declName : Lean.Name) : String :=
  if declName == `main then "_lean_main" else declName.mangle

def mangleDeclNameInEnv (env : Lean.Environment) (declName : Lean.Name) : String :=
  match Lean.getExportNameFor? env declName with
  | some exportName => exportName.toString
  | none => mangleDeclName declName

structure LCNFDeclMetadata where
  declName       : Lean.Name
  mangledSymbol  : String
  isSimpleGround : Bool
  isExtern       : Bool
  deriving Repr, DecidableEq, Inhabited, BEq

def getLCNFDeclMetadata (env : Lean.Environment) (declName : Lean.Name) : LCNFDeclMetadata := {
  declName       := declName
  mangledSymbol  := mangleDeclNameInEnv env declName
  isSimpleGround := hasSimpleGroundDecl env declName
  isExtern       := Lean.isExtern env declName
}

partial def isSignedScalarTypeExpr (e : Lean.Expr) : Bool :=
  match e.getAppFn with
  | .const declName _ =>
    declName == ``Int8 || declName == ``Int16 || declName == ``Int32 ||
    declName == ``Int64 || declName == ``ISize || declName == ``Int ||
    (match declName with
     | .str p _ => p == ``Int8 || p == ``Int16 || p == ``Int32 || p == ``Int64 || p == ``ISize || p == ``Int
     | _ => false)
  | _ => false

partial def exprUsesSignedScalarType : Lean.Expr → Bool
  | .forallE _ d b _ => exprUsesSignedScalarType d || exprUsesSignedScalarType b
  | .lam _ d b _ => exprUsesSignedScalarType d || exprUsesSignedScalarType b
  | .letE _ t v b _ => exprUsesSignedScalarType t || exprUsesSignedScalarType v || exprUsesSignedScalarType b
  | .app f a => isSignedScalarTypeExpr (Lean.Expr.app f a) || exprUsesSignedScalarType f || exprUsesSignedScalarType a
  | .mdata _ b => exprUsesSignedScalarType b
  | .proj _ _ b => exprUsesSignedScalarType b
  | e => isSignedScalarTypeExpr e

private def argUsesSigned : Lean.Compiler.LCNF.Arg pu → Bool
  | .type e _ => exprUsesSignedScalarType e
  | _ => false

private partial def codeSignedScan (code : Lean.Compiler.LCNF.Code pu) : StateT Lean.NameSet Lean.CoreM Bool := do
  let paramsSigned (ps : Array (Lean.Compiler.LCNF.Param pu)) := ps.any (exprUsesSignedScalarType ·.type)
  match code with
  | .let d k =>
    if exprUsesSignedScalarType d.type then return true
    let valSigned ← match d.value with
      | .const n _ args _ => if args.any argUsesSigned then pure true else declSignedScan n
      | .fvar _ args => pure (args.any argUsesSigned)
      | .fap n args _ | .pap n args _ => if args.any argUsesSigned then pure true else declSignedScan n
      | _ => pure false
    if valSigned then return true
    codeSignedScan k
  | .fun d k _ | .jp d k =>
    if paramsSigned d.params || exprUsesSignedScalarType d.type then return true
    if ← codeSignedScan d.value then return true
    codeSignedScan k
  | .cases c =>
    if exprUsesSignedScalarType c.resultType then return true
    c.alts.anyM fun alt => do
      let ps := match alt with | .alt _ ps _ _ => ps | _ => #[]
      if paramsSigned ps then return true
      codeSignedScan alt.getCode
  | .jmp _ args => return args.any argUsesSigned
  | .unreach t => return exprUsesSignedScalarType t
  | .return _ => return false
  | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ | .setTag _ _ k _
  | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _ => codeSignedScan k
where
  declSignedScan (n : Lean.Name) : StateT Lean.NameSet Lean.CoreM Bool := do
    if (← get).contains n then return false
    modify (·.insert n)
    match ← Lean.Compiler.LCNF.getBaseDecl? n with
    | some d =>
      if exprUsesSignedScalarType d.type || d.params.any (exprUsesSignedScalarType ·.type) then return true
      match d.value with
      | .code c => codeSignedScan c
      | .extern _ => return false
    | none =>
      if !(← getEnv).contains n then return false
      try return exprUsesSignedScalarType (← Lean.Compiler.LCNF.getOtherDeclBaseType n [])
      catch _ => return true

def declUsesSignedScalarTransitively (decl : Lean.Compiler.LCNF.Decl pu) : Lean.CoreM Bool := do
  if let some cinfo := (← getEnv).find? decl.name then
    if exprUsesSignedScalarType cinfo.type || cinfo.value?.any exprUsesSignedScalarType then return true
  if exprUsesSignedScalarType decl.type || decl.params.any (exprUsesSignedScalarType ·.type) then return true
  match decl.value with
  | .code c => (codeSignedScan c).run' (Lean.NameSet.empty.insert decl.name)
  | .extern _ => return false

partial def nullaryEnumScalarType? (env : Lean.Environment) (e : Lean.Expr) : Option LNIRType :=
  match e.getAppFn with
  | .const declName _ =>
    match env.find? declName with
    | some (.inductInfo ival) =>
      let n := ival.ctors.length
      if !ival.isRec && n >= 2 && n ≤ 65535 && (ival.ctors.all fun cName =>
        match env.find? cName with
        | some (.ctorInfo cval) => cval.numFields == 0
        | _ => false) then
        some (if n ≤ 255 then .i8 else .i16)
      else none
    | _ => none
  | _ => none

def isClosureOrRuntimeNatExpr (e : Lean.Expr) : Bool :=
  if e == ImpureType.tobject || e == ImpureType.tagged then true
  else match e.getAppFn with
    | .const declName _ => declName == ``Nat
    | .forallE .. | .lam .. => true
    | _ => false

export LeanNative.IR.RealLCNFBridge (
  archSupportsUSize archUSizeMask archUSizeShiftMask
  scalarWidthMask? scalarShiftMask?
  isSupportedStage1BScalarType isSupportedStage1BScalarOrTuple
  isFlatUnboxedScalar isUnboxedScalarOrTuple isSupportedSliceType
)

def isSupportedScalarOrFloat (ty : LNIRType) (arch : TargetArch) : Bool :=
  isSupportedStage1BScalarType ty arch || ty == .f64

def isSupportedParamOrRetType (ty : LNIRType) (arch : TargetArch) (allowSlice : Bool := false) : Bool :=
  isSupportedStage1BScalarOrTuple ty arch || ty == .f64 || (allowSlice && isSupportedSliceType ty)

def exprCodomainIsProp (env? : Option Lean.Environment) (e : Lean.Expr) : Bool :=
  let fn := e.getAppFn
  match fn with
  | .const declName _ =>
    if declName == ``LT.lt || declName == ``LE.le || declName == ``GT.gt || declName == ``GE.ge ||
       declName == ``Eq || declName == ``Ne || declName == ``Dvd.dvd ||
       declName == ``And || declName == ``Or || declName == ``Not || declName == ``Iff ||
       declName == ``True || declName == ``False then true
    else match env?.bind (·.find? declName) with
      | some cinfo =>
        let rec returnsProp : Lean.Expr → Bool
          | .forallE _ _ b _ => returnsProp b
          | .sort u => u.isZero
          | _ => false
        returnsProp cinfo.type
      | none => false
  | _ => false

partial def lowerImpureType (e : Lean.Expr) (env? : Option Lean.Environment := none) : LNIRType :=
  let e := e.consumeMData
  if e == ImpureType.uint8 then .i8
  else if e == ImpureType.uint16 then .i16
  else if e == ImpureType.uint32 then .i32
  else if e == ImpureType.uint64 then .i64
  else if e == ImpureType.usize then .usize
  else if e == ImpureType.float32 then .f32
  else if e == ImpureType.float then .f64
  else if e == ImpureType.object then .objPtr
  else if e == ImpureType.tagged || e == ImpureType.tobject then .taggedPtr
  else if e == ImpureType.erased || e == ImpureType.void then .unit
  else if exprCodomainIsProp env? e then .unit
  else if isSignedScalarTypeExpr e then .objPtr
  else
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .const declName _ =>
      if declName == ``UInt8 then .i8
      else if declName == ``UInt16 then .i16
      else if declName == ``UInt32 then .i32
      else if declName == ``UInt64 then .i64
      else if declName == ``Nat then .taggedPtr
      else if declName == ``LeanNative.IR.UInt256 || (match declName with | .str _ "UInt256" | .str _ "U256" => true | _ => false) then .u256
      else if (match declName with | .str _ "StorageMap" => true | _ => false) then .storageMap
      else if declName == ``USize then .usize
      else if declName == ``Float32 then .f32
      else if declName == ``Float then .f64
      else if declName == ``Bool then .i1
      else if declName == ``Unit || declName == ``PUnit || declName == ``lcErased || declName == ``lcVoid then .unit
      else if declName == ``ByteArray then .sarray .i8
      else if declName == ``FloatArray then .sarray .f64
      else if declName == ``Array then .sarray (args[0]?.map (lowerImpureType · env?) |>.getD .taggedPtr)
      else if declName == ``Prod || declName == ``MProd || declName == ``PProd then
        match args[0]?, args[1]? with
        | some a, some b =>
          let ta := lowerImpureType a env?
          let tb := lowerImpureType b env?
          if isFlatUnboxedScalar ta && isFlatUnboxedScalar tb then .tuple [ta, tb] else .objPtr
        | _, _ => .objPtr
      else if let some env := env? then
        if let some enumTy := nullaryEnumScalarType? env e then enumTy
        else match env.find? declName with
          | some (.inductInfo ival) =>
            if !ival.isRec && ival.numIndices == 0 && ival.ctors.length == 1 then
              match ival.ctors.head?.bind env.find? with
              | some (.ctorInfo cval) =>
                let rec collectFields (k : Nat) (t : Lean.Expr) : List LNIRType :=
                  match k, t with
                  | 0, _ => []
                  | k + 1, .forallE _ dom body _ => lowerImpureType dom env? :: collectFields k body
                  | _, _ => [.objPtr]
                let rec dropParams (k : Nat) (t : Lean.Expr) : Lean.Expr :=
                  match k, t with
                  | 0, rest => rest
                  | k + 1, .forallE _ _ body _ => dropParams k body
                  | _, rest => rest
                let fTys := collectFields cval.numFields (dropParams cval.numParams cval.type)
                if !fTys.isEmpty && fTys.length ≤ 8 && fTys.all isFlatUnboxedScalar then .tuple fTys else .objPtr
              | _ => .objPtr
            else .objPtr
          | _ => .objPtr
      else .objPtr
    | _ => .objPtr

partial def tyContainsUSize : LNIRType → Bool
  | .usize => true
  | .tuple fs => fs.any tyContainsUSize
  | _ => false

def instantiateInductExprParams (paramArgs : List Lean.Expr) : Nat → Lean.Expr → Lean.Expr
  | 0, rest => rest
  | k + 1, .forallE _ _ body _ =>
    let arg := paramArgs[0]?.getD (Lean.mkConst ``Unit)
    instantiateInductExprParams (paramArgs.drop 1) k (body.instantiate1 arg)
  | _, rest => rest

def isStage1DHeapObjectFieldExpr (env : Lean.Environment) (arch : TargetArch) (e : Lean.Expr) : Bool :=
  if isClosureOrRuntimeNatExpr e || isSignedScalarTypeExpr e then false
  else
    let ty := lowerImpureType e (some env)
    if tyContainsUSize ty && !archSupportsUSize arch then false
    else match ty with
      | .tuple fs => !fs.isEmpty && fs.length ≤ 8 && fs.all (isSupportedStage1BScalarType · arch)
      | _ => false

def isStage1DHeapFieldExpr (env : Lean.Environment) (arch : TargetArch) (e : Lean.Expr) : Bool :=
  if isClosureOrRuntimeNatExpr e || isSignedScalarTypeExpr e then false
  else
    let ty := lowerImpureType e (some env)
    if tyContainsUSize ty && !archSupportsUSize arch then false
    else isSupportedStage1BScalarOrTuple ty arch

def isSupportedStage1DHeapAdtExpr (env : Lean.Environment) (arch : TargetArch) (e : Lean.Expr) : Bool :=
  if isClosureOrRuntimeNatExpr e || isSignedScalarTypeExpr e then false
  else
    let fn := e.getAppFn
    let args := e.getAppArgs.toList
    match fn with
    | .const declName _ =>
      if (nullaryEnumScalarType? env e).isSome ||
         declName == ``Prod || declName == ``MProd || declName == ``PProd ||
         declName == ``Bool || declName == ``Unit || declName == ``PUnit || declName == ``Nat ||
         declName == ``String || declName == ``ByteArray || declName == ``FloatArray || declName == ``Array then
        false
      else
        match env.find? declName with
        | some (.inductInfo ival) =>
          if ival.isRec || ival.numIndices != 0 || ival.ctors.length < 2 || ival.ctors.length > 255 ||
             args.length != ival.numParams then
            false
          else
            let rec checkCtorFields (k : Nat) (t : Lean.Expr) : Bool :=
              match k, t with
              | 0, _ => true
              | k + 1, .forallE _ dom body _ =>
                !dom.hasLooseBVars && checkCtorFields k body &&
                  (isStage1DHeapObjectFieldExpr env arch dom ||
                   -- C1.2: direct `UIntN`/`USize` fields live in `scalarFields` (`getCtorLayout` usize/scalar slots)
                   (isStage1DHeapFieldExpr env arch dom &&
                    [LNIRType.i8, .i16, .i32, .i64, .usize].contains (lowerImpureType dom (some env))))
              | _, _ => false
            let hasPayload := ival.ctors.any fun cName =>
              match env.find? cName with
              | some (.ctorInfo cval) => cval.numFields ≥ 1
              | _ => false
            hasPayload && ival.ctors.all fun cName =>
              match env.find? cName with
              | some (.ctorInfo cval) =>
                cval.numFields ≤ 8 &&
                checkCtorFields cval.numFields (instantiateInductExprParams args cval.numParams cval.type)
              | _ => false
        | _ => false
    | _ => false

def declQualifiesForStage1DHeap (env : Lean.Environment) (declName : Lean.Name) (arch : TargetArch) : Bool :=
  if (Lean.getExportNameFor? env declName).isSome || Lean.isExtern env declName then false
  else
    match env.find? declName with
    | none => false
    | some cinfo =>
      let rec go (hasAdt : Bool) (t : Lean.Expr) : Bool :=
        match t with
        | .forallE _ dom body bi =>
          if dom.isSort || bi == .instImplicit || bi == .implicit then
            go hasAdt body
          else if dom.hasLooseBVars then
            false
          else if isSupportedStage1DHeapAdtExpr env arch dom then
            go true body
          else if isStage1DHeapFieldExpr env arch dom then
            go hasAdt body
          else
            false
        | retExpr =>
          if retExpr.hasLooseBVars then false
          else if isSupportedStage1DHeapAdtExpr env arch retExpr then true
          else if isStage1DHeapFieldExpr env arch retExpr then hasAdt
          else false
      go false cinfo.type

def validateSupportedTypeM (ctx : String) (rawTy : Lean.Expr) (ty : LNIRType) (arch : TargetArch)
    (allowInternalObj : Bool := false) (allowSlice : Bool := false) (allowFloat : Bool := true) : Lean.CoreM Unit := do
  if isClosureOrRuntimeNatExpr rawTy && !(allowInternalObj && (rawTy == ImpureType.tobject || rawTy == ImpureType.tagged)) then
    Lean.throwError s!"[lean-native] Unsupported {ctx} type `{rawTy}` (runtime Nat, tagged object, or function/closure type)"
  if tyContainsUSize ty && !archSupportsUSize arch then
    Lean.throwError s!"[lean-native] Unsupported USize in {ctx} on target `{reprStr arch}`"
  let scalarTupleSliceOk :=
    isSupportedStage1BScalarOrTuple ty arch || (allowFloat && ty == .f64) ||
      (allowSlice && !arch.isWasm && isSupportedSliceType ty)
  if !(scalarTupleSliceOk || (allowInternalObj && (ty == .objPtr || ty == .taggedPtr))) then
    Lean.throwError s!"[lean-native] Unsupported non-scalar {ctx} type `{rawTy}` (lowered as `{reprStr ty}`)"

abbrev RcCtorLayoutSpec := LeanNative.IR.RealLCNFBridge.RcCtorLayoutSpec

def getRcCtorLayoutSpecM (ctorName : Lean.Name) : Lean.CoreM RcCtorLayoutSpec := do
  let env ← getEnv
  let lay ← Lean.Compiler.LCNF.getCtorLayout ctorName
  let scalars := lay.fieldInfo.filterMap fun
    | .scalar _ off irTy => some (off, lowerImpureType irTy (some env))
    | _ => none
  return { ctorName, cidx := lay.ctorInfo.cidx, objSlots := lay.ctorInfo.size, usizeSlots := lay.ctorInfo.usize
           scalarSlots := (List.replicate lay.ctorInfo.usize (none, .usize)) ++
             (scalars.qsort (·.1 < ·.1)).toList.map fun (off, ty) => (some off, ty) }

def checkEnvConstSignatureM (env : Lean.Environment) (declName : Lean.Name) (arch : TargetArch)
    (isExported : Bool) : Lean.CoreM Unit := do
  let some cinfo := env.find? declName | return ()
  let isStage1D := !isExported && declQualifiesForStage1DHeap env declName arch
  let rec go (idx : Nat) (t : Lean.Expr) : Lean.CoreM Unit := do
    match t with
    | .forallE pName dom body bi =>
      if dom.isSort || bi == .instImplicit || bi == .implicit then
        go idx body
      else
        let dTy := lowerImpureType dom (some env)
        if isExported then
          validateSupportedTypeM s!"exported parameter `{pName}` of `{declName}`" dom dTy arch false (dTy == .sarray .i8) false
          if dTy matches (.tuple _) then
            Lean.throwError s!"[lean-native] Unsupported exported tuple parameter `{pName}` in `{declName}`"
        else if !(isStage1D && isSupportedStage1DHeapAdtExpr env arch dom) then
          validateSupportedTypeM s!"parameter `{pName}` of `{declName}`" dom dTy arch false true true
        go (idx + 1) body
    | retExpr =>
      if !retExpr.hasLooseBVars then
        let rTy := lowerImpureType retExpr (some env)
        if isExported then
          validateSupportedTypeM s!"exported return type of `{declName}`" retExpr rTy arch false (rTy == .sarray .i8) false
          if rTy matches (.tuple _) then
            Lean.throwError s!"[lean-native] Unsupported exported tuple return type in `{declName}`"
        else if !(isStage1D && isSupportedStage1DHeapAdtExpr env arch retExpr) then
          validateSupportedTypeM s!"return type of `{declName}`" retExpr rTy arch false (rTy == .sarray .i8) true
  go 0 cinfo.type

def collectEnvExplicitParamTypes (env : Lean.Environment) (declName : Lean.Name) : List LNIRType :=
  match env.find? declName with
  | none => []
  | some cinfo =>
    let rec go (acc : List LNIRType) (t : Lean.Expr) : List LNIRType :=
      match t with
      | .forallE _ dom body bi =>
        if dom.isSort || bi == .instImplicit || bi == .implicit then go acc body
        else go (acc ++ [lowerImpureType dom (some env)]) body
      | _ => acc
    go [] cinfo.type

def collectDeclExplicitParamTypesM (env : Lean.Environment) (declName : Lean.Name) : Lean.CoreM (List LNIRType) := do
  let fromEnv := collectEnvExplicitParamTypes env declName
  if !fromEnv.isEmpty then return fromEnv
  match ← Lean.Compiler.LCNF.getMonoDecl? declName with
  | some md => return md.params.toList.map (fun p => lowerImpureType p.type (some env))
  | none => return []

structure BridgeState where
  fvarToVar        : Std.HashMap Lean.FVarId VarId := {}
  varTypes         : Std.HashMap VarId LNIRType := {}
  jpMap            : Std.HashMap Lean.FVarId (Array (Lean.Compiler.LCNF.Param .impure) × LNIRCode) := {}
  jpIndexMap       : Std.HashMap Lean.FVarId Nat := {}
  localFunMap      : Std.HashMap Lean.FVarId (List VarId × LNIRCode) := {}
  nextVarId        : VarId := 0
  hasExtern        : Bool := false
  mangledSymbol    : String := ""
  isSimpleGround   : Bool := false
  selfDeclName     : Lean.Name := .anonymous
  localDeclNames   : Array Lean.Name := #[]
  arch             : TargetArch := .x86_64
  allowStage1DHeap : Bool := false
  inJoinPointBody  : Bool := false
  /-- C1.2: constructor known for a heap var (fresh `allocCtor` or enclosing `cases` alt). -/
  activeCtor       : Std.HashMap VarId Lean.Name := {}
  /-- C1.2: statically known ctor of `let x := ctor …` binders and reset/reuse join-point params (`collectFVarCtors`). -/
  fvarCtor         : Std.HashMap Lean.FVarId Lean.Name := {}
  deriving Inhabited

abbrev BridgeM := StateRefT BridgeState Lean.CoreM

def lowerBridgeType (e : Lean.Expr) : BridgeM LNIRType := do
  return lowerImpureType e (some (← getEnv))

def checkBridgeType (ctx : String) (rawTy : Lean.Expr) (ty : LNIRType)
    (allowInternalObj : Bool := false) (allowSlice : Bool := false) : BridgeM Unit := do
  validateSupportedTypeM ctx rawTy ty (← get).arch allowInternalObj allowSlice true

def internFVar (fvarId : Lean.FVarId) (ty : LNIRType := .objPtr) (authoritative : Bool := false) : BridgeM VarId := do
  let st ← get
  match st.fvarToVar[fvarId]? with
  | some vid =>
    if authoritative then
      set { st with varTypes := st.varTypes.insert vid ty }
    return vid
  | none =>
    let vid := st.nextVarId
    set { st with
      fvarToVar := st.fvarToVar.insert fvarId vid
      varTypes := st.varTypes.insert vid ty
      nextVarId := vid + 1 }
    return vid

def freshBridgeVar (ty : LNIRType) : BridgeM VarId := do
  let st ← get
  let vid := st.nextVarId
  set { st with varTypes := st.varTypes.insert vid ty, nextVarId := vid + 1 }
  return vid

def getVarType (vid : VarId) : BridgeM LNIRType := do
  return (← get).varTypes.getD vid .objPtr

def lowerArg (arg : Lean.Compiler.LCNF.Arg pu) (allowInternalObj : Bool := false) : BridgeM VarId := do
  match arg with
  | .fvar fvarId =>
    if ((← get).localFunMap.contains fvarId) then
      Lean.throwError "[lean-native] Unsupported higher-order / escaping local function value"
    let vid ← internFVar fvarId
    let vTy ← getVarType vid
    if !(isSupportedParamOrRetType vTy (← get).arch true || (allowInternalObj && (vTy == .objPtr || vTy == .taggedPtr))) then
      Lean.throwError s!"[lean-native] Unsupported non-scalar argument of type `{reprStr vTy}`"
    return vid
  | .erased => freshBridgeVar .unit
  | .type .. => freshBridgeVar .unit

def toImpureParams (params : Array (Lean.Compiler.LCNF.Param pu)) : Array (Lean.Compiler.LCNF.Param .impure) :=
  params.map fun p => { fvarId := p.fvarId, binderName := p.binderName, type := p.type, borrow := p.borrow }

partial def codeHasRecursiveJmp (targetFVar : Lean.FVarId) (code : Lean.Compiler.LCNF.Code pu) : Bool :=
  match code with
  | .let _ k | .fun _ k _ | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _
  | .del _ k _ | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ | .setTag _ _ k _ =>
    codeHasRecursiveJmp targetFVar k
  | .jp decl k => codeHasRecursiveJmp targetFVar decl.value || codeHasRecursiveJmp targetFVar k
  | .jmp fvarId _ => fvarId == targetFVar
  | .cases c => c.alts.any (fun alt => codeHasRecursiveJmp targetFVar alt.getCode)
  | .return _ | .unreach _ => false

def letValueCallsTarget {pu} (targetName : Lean.Name) (lv : Lean.Compiler.LCNF.LetValue pu) : Bool :=
  match lv with
  | .fap fn _ _ | .pap fn _ _ | .const fn _ _ _ => fn == targetName
  | _ => false

partial def codeHasSelfTailCall {pu} (targetName : Lean.Name) (code : Lean.Compiler.LCNF.Code pu) : Bool :=
  match code with
  | .let decl k => letValueCallsTarget targetName decl.value || codeHasSelfTailCall targetName k
  | .fun decl k _ | .jp decl k => codeHasSelfTailCall targetName decl.value || codeHasSelfTailCall targetName k
  | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _
  | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ | .setTag _ _ k _ =>
    codeHasSelfTailCall targetName k
  | .cases c => c.alts.any (fun alt => codeHasSelfTailCall targetName alt.getCode)
  | .jmp _ _ | .return _ | .unreach _ => false

partial def declsHaveMutualCycle (declMap : Std.HashMap Lean.Name (List Lean.Name)) : Bool :=
  let rec reaches (target : Lean.Name) (visited : List Lean.Name) (frontier : List Lean.Name) : Bool :=
    match frontier with
    | [] => false
    | cur :: rest =>
      if cur == target then true
      else if visited.contains cur then reaches target visited rest
      else reaches target (cur :: visited) ((declMap.getD cur []) ++ rest)
  declMap.toList.any fun (name, callees) => reaches name [] callees

def collectCodeLocalCallees {pu} (localSet : Array Lean.Name) (code : Lean.Compiler.LCNF.Code pu) : List Lean.Name :=
  (localSet.toList).filter (fun n => codeHasSelfTailCall n code)

/-- Discover generated and imported helper names directly from the LCNF tree;
    they need not appear in the environment's source-level constant table. -/
partial def collectNamedCallees {pu} : Lean.Compiler.LCNF.Code pu → List Lean.Name
  | .let d k =>
    let direct := match d.value with
      | .fap n _ _ | .pap n _ _ | .const n _ _ _ => [n]
      | _ => []
    direct ++ collectNamedCallees k
  | .fun d k _ | .jp d k => collectNamedCallees d.value ++ collectNamedCallees k
  | .cases c => c.alts.toList.flatMap (fun alt => collectNamedCallees alt.getCode)
  | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _
  | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ | .setTag _ _ k _ => collectNamedCallees k
  | .jmp _ _ | .return _ | .unreach _ => []

partial def codeReferencesFVar (targetFVar : Lean.FVarId) (code : Lean.Compiler.LCNF.Code pu) : Bool :=
  let argHas (a : Lean.Compiler.LCNF.Arg pu) : Bool :=
    match a with | .fvar id => id == targetFVar | _ => false
  match code with
  | .let decl k =>
    let inVal := match decl.value with
      | .fvar id args => id == targetFVar || args.any argHas
      | .fap _ args _ | .pap _ args _ | .ctor _ args _ | .reuse _ _ _ args _ => args.any argHas
      | .const _ _ args _ => args.any argHas
      | .proj _ _ id _ | .oproj _ id _ | .uproj _ id _ | .sproj _ _ id _
      | .reset _ id _ | .box _ id _ | .unbox id _ | .isShared id _ => id == targetFVar
      | .lit _ | .erased => false
    inVal || codeReferencesFVar targetFVar k
  | .fun decl k _ | .jp decl k =>
    codeReferencesFVar targetFVar decl.value || codeReferencesFVar targetFVar k
  | .jmp fvarId args => fvarId == targetFVar || args.any argHas
  | .cases c => c.discr == targetFVar || c.alts.any (fun alt => codeReferencesFVar targetFVar alt.getCode)
  | .return fvarId => fvarId == targetFVar
  | .inc id _ _ _ k _ | .dec id _ _ _ _ k _ | .del id k _ | .setTag id _ k _ =>
    id == targetFVar || codeReferencesFVar targetFVar k
  | .oset id _ arg k _ => id == targetFVar || argHas arg || codeReferencesFVar targetFVar k
  | .uset id _ vid k _ | .sset id _ _ vid _ k _ => id == targetFVar || vid == targetFVar || codeReferencesFVar targetFVar k
  | .unreach _ => false

def substScalarExprVars (subst : Std.HashMap VarId VarId) : ScalarExpr → ScalarExpr
  | .constU64 v => .constU64 v
  | .constBool b => .constBool b
  | .var id => .var (subst.getD id id)
  | .binOp op l r => .binOp op (substScalarExprVars subst l) (substScalarExprVars subst r)
  | .unaryOp op a => .unaryOp op (substScalarExprVars subst a)
  | .select c t e => .select (substScalarExprVars subst c) (substScalarExprVars subst t) (substScalarExprVars subst e)
  | .fma a b c => .fma (substScalarExprVars subst a) (substScalarExprVars subst b) (substScalarExprVars subst c)

def substLNIRExprVars (subst : Std.HashMap VarId VarId) (varTypes : Std.HashMap VarId LNIRType) : LNIRExpr → LNIRExpr
  | .scalar e => .scalar (substScalarExprVars subst e)
  | .constU256 v => .constU256 v
  | .mulDivDown a b d => .mulDivDown (subst.getD a a) (subst.getD b b) (subst.getD d d)
  | .mulDivUp a b d => .mulDivUp (subst.getD a a) (subst.getD b b) (subst.getD d d)
  | .storageLoad m s => .storageLoad (subst.getD m m) (subst.getD s s)
  | .storageStore m s v => .storageStore (subst.getD m m) (subst.getD s s) (subst.getD v v)
  | .mkTuple fs => .mkTuple (fs.map (fun v => subst.getD v v))
  | .projTuple tv idx => .projTuple (subst.getD tv tv) idx
  | .allocCtor tag ofs sfs => .allocCtor tag (ofs.map (fun v => subst.getD v v)) (sfs.map (fun v => subst.getD v v))
  | .ctorGetObj cv idx =>
    let cv' := subst.getD cv cv
    match varTypes[cv']? with
    | some (.tuple _) => .projTuple cv' idx
    | _ => .ctorGetObj cv' idx
  | .ctorGetScalar cv idx ty => .ctorGetScalar (subst.getD cv cv) idx ty
  | .isExclusive ov => .isExclusive (subst.getD ov ov)
  | .sarrayLen av => .sarrayLen (subst.getD av av)
  | .sarrayDataPtr av et => .sarrayDataPtr (subst.getD av av) et
  | .sarrayEnsureExclusive av et => .sarrayEnsureExclusive (subst.getD av av) et
  | .sarrayGet av iv et => .sarrayGet (subst.getD av av) (subst.getD iv iv) et
  | .sarraySet av iv vv et => .sarraySet (subst.getD av av) (subst.getD iv iv) (subst.getD vv vv) et
  | .rawLoad pv iv et => .rawLoad (subst.getD pv pv) (subst.getD iv iv) et
  | .boxScalar vv ty => .boxScalar (subst.getD vv vv) ty
  | .unboxScalar bv ty => .unboxScalar (subst.getD bv bv) ty
  | .call fn args rty ext => .call fn (args.map (fun v => subst.getD v v)) rty ext

partial def freshenJoinPointCode (subst : Std.HashMap VarId VarId) (code : LNIRCode) : BridgeM LNIRCode := do
  match code with
  | .letBind dst ty val k =>
    let val0 := substLNIRExprVars subst (← get).varTypes val
    let val' ← match val0 with
      | .scalar (.binOp .eq (.var cv) (.constU64 cidx)) =>
        if (← getVarType cv) == .i1 then
          pure (.scalar (if cidx == 0 then .unaryOp .not (.var cv) else if cidx == 1 then .var cv else .constBool false))
        else pure val0
      | _ => pure val0
    match val' with
    | .call "lean_native_ctor_set" (objVid :: _) _ false =>
      if !(← get).allowStage1DHeap && isUnboxedScalarOrTuple (← getVarType objVid) then
        return ← freshenJoinPointCode subst k
    | _ => pure ()
    let ty' ← match val' with
      | .scalar (.var sv) =>
        let sTy ← getVarType sv
        pure (if isUnboxedScalarOrTuple sTy && (ty == .objPtr || ty == .taggedPtr) then sTy else ty)
      | .mkTuple fs => pure (.tuple (← fs.mapM getVarType))
      | .projTuple tv idx =>
        match (← getVarType tv) with
        | .tuple fs => pure (fs[idx]?.getD .i64)
        | _ => pure ty
      | _ => pure ty
    let freshDst ← freshBridgeVar ty'
    return .letBind freshDst ty' val' (← freshenJoinPointCode (subst.insert dst freshDst) k)
  | .rawStore pv iv vv et k =>
    return .rawStore (subst.getD pv pv) (subst.getD iv iv) (subst.getD vv vv) et (← freshenJoinPointCode subst k)
  | .incRef ov n k =>
    let ov' := subst.getD ov ov; let vt ← getVarType ov'
    if isUnboxedScalarOrTuple vt then freshenJoinPointCode subst k
    else return .incRef ov' n (← freshenJoinPointCode subst k)
  | .decRef ov n k =>
    let ov' := subst.getD ov ov; let vt ← getVarType ov'
    if isUnboxedScalarOrTuple vt then freshenJoinPointCode subst k
    else return .decRef ov' n (← freshenJoinPointCode subst k)
  | .ite cv t e =>
    return .ite (subst.getD cv cv) (← freshenJoinPointCode subst t) (← freshenJoinPointCode subst e)
  | .seqFor iv lv hv av ai aty step k =>
    let freshIv ← freshBridgeVar .i64
    let freshAv ← freshBridgeVar aty
    let stepSubst := (subst.insert iv freshIv).insert av freshAv
    let kSubst := subst.insert av freshAv
    return .seqFor freshIv (subst.getD lv lv) (subst.getD hv hv) freshAv (subst.getD ai ai) aty
      (← freshenJoinPointCode stepSubst step) (← freshenJoinPointCode kSubst k)
  | .parFor ov lv ins et kern k =>
    let freshOv ← freshBridgeVar (.sarray et)
    let kern' ← match kern with
      | .customScalar idxVar inVars body => do
        let freshIdx ← freshBridgeVar .i64
        let freshIns ← inVars.mapM (fun _ => freshBridgeVar et)
        let kSubst := (inVars.zip freshIns).foldl (fun m (o, n) => m.insert o n) (subst.insert idxVar freshIdx)
        pure (.customScalar freshIdx freshIns (substScalarExprVars kSubst body))
      | other => pure other
    return .parFor freshOv (subst.getD lv lv) (ins.map (fun v => subst.getD v v)) et kern'
      (← freshenJoinPointCode (subst.insert ov freshOv) k)
  | .ret v => return .ret (subst.getD v v)
  | .unreachable => return .unreachable

def spliceJoinPointJmp {pu} (jpParams : Array (Lean.Compiler.LCNF.Param .impure)) (jpBody : LNIRCode)
    (args : Array (Lean.Compiler.LCNF.Arg pu)) : BridgeM LNIRCode := do
  if jpParams.size != args.size then
    Lean.throwError s!"[lean-native] join point arity mismatch: expected {jpParams.size}, got {args.size}"
  let mut preBinds : List (VarId × LNIRType × LNIRExpr) := []
  let mut subst : Std.HashMap VarId VarId := {}
  for (p, arg) in jpParams.toList.zip args.toList do
    let pTy ← lowerBridgeType p.type
    let origParamVid ← internFVar p.fvarId pTy
    let argVar ← match arg with
      | .erased | .type .. =>
        let zTy := if pTy == .unit then .i64 else pTy
        let zv ← freshBridgeVar zTy
        preBinds := preBinds ++ [(zv, zTy, .scalar (.constU64 0))]
        pure zv
      | _ => lowerArg arg true
    subst := subst.insert origParamVid argVar
  let body' ← freshenJoinPointCode subst jpBody
  return preBinds.foldr (fun (dst, ty, val) acc => .letBind dst ty val acc) body'

def orderAlts (alts : List (Lean.Compiler.LCNF.Alt pu)) : List (Lean.Compiler.LCNF.Alt pu) :=
  RealLCNFBridge.orderAltsPure alts

def lowerLitValueM (lit : Lean.Compiler.LCNF.LitValue) (retTy : LNIRType := .i64)
    (allowInternalObj : Bool := false) : BridgeM LNIRExpr := do
  let arch := (← get).arch
  match RealLCNFBridge.lowerLitValuePure lit retTy arch allowInternalObj with
  | .ok expr => return expr
  | .error msg => Lean.throwError msg

def lowerLitValue (lit : Lean.Compiler.LCNF.LitValue) : BridgeM LNIRExpr :=
  lowerLitValueM lit .i64

partial def eraseBinderNamesAndPrefix (fnName : Lean.Name) : Lean.Expr → Lean.Expr
  | .const n ls => if fnName.isPrefixOf n then .const (n.replacePrefix fnName `canonical_intrinsic) ls else .const n ls
  | .app f a => .app (eraseBinderNamesAndPrefix fnName f) (eraseBinderNamesAndPrefix fnName a)
  | .lam _ t b bi => .lam `_ (eraseBinderNamesAndPrefix fnName t) (eraseBinderNamesAndPrefix fnName b) bi
  | .forallE _ t b bi => .forallE `_ (eraseBinderNamesAndPrefix fnName t) (eraseBinderNamesAndPrefix fnName b) bi
  | .letE _ t v b nd => .letE `_ (eraseBinderNamesAndPrefix fnName t) (eraseBinderNamesAndPrefix fnName v) (eraseBinderNamesAndPrefix fnName b) nd
  | .mdata _ e => eraseBinderNamesAndPrefix fnName e
  | .proj t i e => .proj t i (eraseBinderNamesAndPrefix fnName e)
  | e => e

def normalizeIntrinsicDecl (fnName : Lean.Name) (e : Lean.Expr) : String :=
  toString (repr (eraseBinderNamesAndPrefix fnName e))

elab "canon_decl_repr% " base:ident " : " target:ident : term => do
  let env ← Lean.getEnv
  let some (.defnInfo d) := env.find? target.getId | Lean.throwError "missing {target.getId}"
  return Lean.toExpr (normalizeIntrinsicDecl base.getId d.value)

def altClmul64 (a b : UInt64) : UInt64 :=
  let rec go (i : Nat) (acc : UInt64) : UInt64 :=
    if _h : i < 64 then
      let sh := i.toUInt64
      go (i + 1) (if ((b >>> sh) &&& 1) == 1 then acc ^^^ (a <<< sh) else acc)
    else acc
  termination_by 64 - i
  decreasing_by exact Nat.sub_lt_sub_left _h (Nat.lt_succ_self i)
  go 0 0

def altClmul64Hi (a b : UInt64) : UInt64 :=
  let rec go (i : Nat) (acc : UInt64) : UInt64 :=
    if _h : i < 64 then
      let sh := i.toUInt64
      go (i + 1) (if ((b >>> sh) &&& 1) == 1 then acc ^^^ (a >>> (64 - sh)) else acc)
    else acc
  termination_by 64 - i
  decreasing_by exact Nat.sub_lt_sub_left _h (Nat.lt_succ_self i)
  go 1 0

def canonClmul64Repr : String := canon_decl_repr% LeanNative.IR.clmul64 : LeanNative.IR.clmul64
def canonClmul64GoRepr : String := canon_decl_repr% LeanNative.IR.clmul64 : LeanNative.IR.clmul64.go._unary
def canonAltClmul64Repr : String := canon_decl_repr% LeanNative.IR.altClmul64 : LeanNative.IR.altClmul64
def canonAltClmul64GoRepr : String := canon_decl_repr% LeanNative.IR.altClmul64 : LeanNative.IR.altClmul64.go._unary
def canonClmul64HiRepr : String := canon_decl_repr% LeanNative.IR.clmul64Hi : LeanNative.IR.clmul64Hi
def canonClmul64HiGoRepr : String := canon_decl_repr% LeanNative.IR.clmul64Hi : LeanNative.IR.clmul64Hi.go._unary
def canonAltClmul64HiRepr : String := canon_decl_repr% LeanNative.IR.altClmul64Hi : LeanNative.IR.altClmul64Hi
def canonAltClmul64HiGoRepr : String := canon_decl_repr% LeanNative.IR.altClmul64Hi : LeanNative.IR.altClmul64Hi.go._unary
def canonGf2AffineRepr : String := canon_decl_repr% LeanNative.IR.gf2Affine : LeanNative.IR.gf2Affine
def canonGf2AffineGoRepr : String := canon_decl_repr% LeanNative.IR.gf2Affine : LeanNative.IR.gf2Affine.go._unary
def canonEor3Repr : String := canon_decl_repr% LeanNative.IR.eor3 : LeanNative.IR.eor3

private def intrinsicConstNames : Lean.Expr → List Lean.Name
  | .const n _ => [n]
  | .app f a => intrinsicConstNames f ++ intrinsicConstNames a
  | .lam _ t b _ | .forallE _ t b _ => intrinsicConstNames t ++ intrinsicConstNames b
  | .letE _ t v b _ => intrinsicConstNames t ++ intrinsicConstNames v ++ intrinsicConstNames b
  | .mdata _ e | .proj _ _ e => intrinsicConstNames e
  | _ => []

/-- Capture canonical graphs at compiler-build time. Target programs need not
    import LeanNative in order to be recognized. -/
def canonicalIntrinsicGraph (env : Lean.Environment) (root scope : Lean.Name) :
    Option (List (String × String × String × String)) :=
  let rec collect (fuel : Nat) (seen : List Lean.Name) (todo : List Lean.Name)
      (out : List (String × String × String × String)) :=
    match todo, fuel with
    | [], _ => some out
    | _ :: _, 0 => none
    | n :: rest, fuel + 1 =>
      if seen.contains n then collect fuel seen rest out
      else do
        let some (.defnInfo d) := env.find? n | none
        guard (!Lean.isExtern env n)
        let entry := ((n.replacePrefix scope .anonymous).toString,
          normalizeIntrinsicDecl scope d.type, normalizeIntrinsicDecl scope d.value,
          s!"{repr d.safety}/{repr d.levelParams}")
        collect fuel (n :: seen)
          (((intrinsicConstNames d.value).filter scope.isPrefixOf).eraseDups ++ rest) (out ++ [entry])
  collect 256 [] [root] []

elab "canon_intrinsic_graph% " scope:ident " : " root:ident : term => do
  let env ← Lean.getEnv
  let some graph := canonicalIntrinsicGraph env root.getId scope.getId
    | Lean.throwError "cannot capture canonical intrinsic graph for {root.getId}"
  return Lean.toExpr graph

def canonUgetGraph := canon_intrinsic_graph% LeanNative.IR.uget64LE : LeanNative.IR.uget64LE
def canonUsetGraph := canon_intrinsic_graph% LeanNative.IR.uset64LE : LeanNative.IR.uset64LE
def canonAffine64Graph := canon_intrinsic_graph% LeanNative.IR.gf2Affine64 : LeanNative.IR.gf2Affine64
def canonTernaryGraph := canon_intrinsic_graph% LeanNative.IR.ternaryLogic64 : LeanNative.IR.ternaryLogic64
def canonMaskedLoGraph := canon_intrinsic_graph% LeanNative.IR.MaskedClmul : LeanNative.IR.MaskedClmul.nativeClmulLo
def canonMaskedHiGraph := canon_intrinsic_graph% LeanNative.IR.MaskedClmul : LeanNative.IR.MaskedClmul.nativeClmulHi

/-- Compare complete bodies and generated helpers against frozen canonical
    graphs. Names, borrowed metadata and binder spelling alone confer no trust. -/
def matchesCanonicalIntrinsic (env : Lean.Environment) (actual reference : Lean.Name)
    (namespaceScope : Bool := false) : Bool := Id.run do
  let expected := if reference == ``LeanNative.IR.uget64LE then canonUgetGraph
    else if reference == ``LeanNative.IR.uset64LE then canonUsetGraph
    else if reference == ``LeanNative.IR.gf2Affine64 then canonAffine64Graph
    else if reference == ``LeanNative.IR.ternaryLogic64 then canonTernaryGraph
    else if reference == ``LeanNative.IR.MaskedClmul.nativeClmulLo then canonMaskedLoGraph
    else if reference == ``LeanNative.IR.MaskedClmul.nativeClmulHi then canonMaskedHiGraph
    else []
  if expected.isEmpty then return false
  let scope := if namespaceScope then actual.getPrefix else actual
  return canonicalIntrinsicGraph env actual scope == some expected


def trustedGfSimdIntrinsicOp (env : Lean.Environment) (fnName : Lean.Name) : Option BinOp := do
  if let some (op, reference) := (match fnName with
      | .str _ "nativeClmulLo" => some (BinOp.clmul64, ``LeanNative.IR.MaskedClmul.nativeClmulLo)
      | .str _ "nativeClmulHi" => some (BinOp.clmul64Hi, ``LeanNative.IR.MaskedClmul.nativeClmulHi)
      | _ => none) then
    guard (matchesCanonicalIntrinsic env fnName reference true)
    return op
  let (op, variants) ← match fnName with
    | .str _ "clmul64Hi" =>
      some (BinOp.clmul64Hi, [(canonClmul64HiRepr, some canonClmul64HiGoRepr),
                              (canonAltClmul64HiRepr, some canonAltClmul64HiGoRepr)])
    | .str _ "clmul64" =>
      some (BinOp.clmul64, [(canonClmul64Repr, some canonClmul64GoRepr),
                            (canonAltClmul64Repr, some canonAltClmul64GoRepr)])
    | .str _ "gf2Affine" => some (BinOp.gf2Affine, [(canonGf2AffineRepr, some canonGf2AffineGoRepr)])
    | .str _ "eor3"      => some (BinOp.eor3, [(canonEor3Repr, none)])
    | _ => none
  let .defnInfo decl ← env.find? fnName | none
  let u64 := Lean.mkConst ``UInt64
  let sig := Lean.Expr.forallE `a u64 (Lean.Expr.forallE `b u64 u64 .default) .default
  guard (decl.levelParams.isEmpty && decl.safety == .safe && decl.type.eqv sig && !Lean.isExtern env fnName)
  let normBody := normalizeIntrinsicDecl fnName decl.value
  let matchesVariant (v : String × Option String) : Bool :=
    let (expBody, expGoOpt) := v
    if normBody != expBody then false
    else match expGoOpt with
      | none => true
      | some expGo =>
        match env.find? (fnName ++ `go._unary) with
        | some (.defnInfo goDecl) => normalizeIntrinsicDecl fnName goDecl.value == expGo
        | _ => false
  guard (variants.any matchesVariant)
  return op

def tryLowerGfSimdIntrinsic (env : Lean.Environment) (fnName : Lean.Name) (argVars : List VarId)
    (retTy : LNIRType := .i64) (argTys : List LNIRType := []) : Option LNIRExpr :=
  match argVars with
  | [lhs, rhs] =>
    if retTy == .i64 && (argTys.isEmpty || argTys == [.i64, .i64]) then
      (trustedGfSimdIntrinsicOp env fnName).map fun op => .scalar (.binOp op (.var lhs) (.var rhs))
    else none
  | _ => none


def trustedG0IntrinsicCall? (env : Lean.Environment) (fnName : Lean.Name) : Option String := do
  let (reference, symbol) ← match fnName with
    | .str _ "uget64LE" => some (``LeanNative.IR.uget64LE, "lean_native_sarray_uget64_le")
    | .str _ "uset64LE" => some (``LeanNative.IR.uset64LE, "lean_native_sarray_uset64_le")
    | .str _ "gf2Affine64" => some (``LeanNative.IR.gf2Affine64, "lean_native_gf2_affine64")
    | .str _ "ternaryLogic64" => some (``LeanNative.IR.ternaryLogic64, "lean_native_ternary_logic64")
    | _ => none
  guard (matchesCanonicalIntrinsic env fnName reference)
  return symbol

def collectEnvExplicitReturnType? (env : Lean.Environment) (name : Lean.Name) : Option LNIRType := do
  let info ← env.find? name
  let rec result : Lean.Expr → Lean.Expr
    | .forallE _ _ body _ => result body
    | e => e
  return lowerImpureType (result info.type) (some env)

/-- Recover ByteArray results erased to `lcObj` by impure conversion. Restore
    types at each call site, without treating every object as a byte array. -/
partial def rewriteImpureUset64LETypes (env : Lean.Environment) :
    Lean.Compiler.LCNF.Code .impure → Lean.Compiler.LCNF.Code .impure
  | .let d k =>
    let d := match d.value with
      | .fap n _ _ =>
        if collectEnvExplicitReturnType? env n == some (.sarray .i8) then
          { d with type := Lean.mkConst ``ByteArray }
        else d
      | _ => d
    .let d (rewriteImpureUset64LETypes env k)
  | .jp d k => .jp (d.updateCore d.type d.params (rewriteImpureUset64LETypes env d.value))
      (rewriteImpureUset64LETypes env k)
  | .fun d k h => .fun (d.updateCore d.type d.params (rewriteImpureUset64LETypes env d.value))
      (rewriteImpureUset64LETypes env k) h
  | .cases c => .cases (c.updateAlts (c.alts.map fun alt => match alt with
      | .alt n ps b h => .alt n ps (rewriteImpureUset64LETypes env b) h
      | .ctorAlt info b h => .ctorAlt info (rewriteImpureUset64LETypes env b) h
      | .default b => .default (rewriteImpureUset64LETypes env b)))
  | .inc v n c p k h => .inc v n c p (rewriteImpureUset64LETypes env k) h
  | .dec v n c p q k h => .dec v n c p q (rewriteImpureUset64LETypes env k) h
  | other => other

def internParams {pu} (params : Array (Lean.Compiler.LCNF.Param pu)) (allowInternalObj : Bool := false) : BridgeM Unit := do
  for p in params do
    let pTy ← lowerBridgeType p.type
    checkBridgeType "parameter" p.type pTy allowInternalObj (pTy == .sarray .i8)
    let _ ← internFVar p.fvarId pTy true

def lowerRefOp (isInc : Bool) (fvarId : Lean.FVarId) (n : Nat) (kCode : LNIRCode) : BridgeM LNIRCode := do
  let v ← internFVar fvarId
  let vt ← getVarType v
  match RealLCNFBridge.lowerRefOpPure isInc v vt n kCode with
  | .ok code => return code
  | .error msg => Lean.throwError msg

def inferImpureRhsType (rhs : LNIRExpr) (declTy : LNIRType) (isBox : Bool) : BridgeM LNIRType := do
  if isBox then
    match rhs with
    | .scalar (.var sv) =>
      let sty ← getVarType sv
      return if isUnboxedScalarOrTuple sty then sty else .i64
    | _ => return .i64
  match rhs with
  | .allocCtor .. => return .objPtr
  | .isExclusive .. => return .i1
  | .scalar (.var sv) =>
    let sty ← getVarType sv
    return if isUnboxedScalarOrTuple declTy then declTy
      else if isUnboxedScalarOrTuple sty then sty else declTy
  | .scalar _ => return if isUnboxedScalarOrTuple declTy then declTy else .i64
  | .mkTuple argVars => return .tuple (← argVars.mapM getVarType)
  | .projTuple tv idx =>
    match (← getVarType tv) with
    | .tuple fs => return if isUnboxedScalarOrTuple declTy then declTy else fs[idx]?.getD .i64
    | _ => return declTy
  | _ => return declTy

def lookupCtorIdx (ctorName : Lean.Name) (fallbackIdx : Nat) : BridgeM Nat := do
  match (← getEnv).find? ctorName with
  | some (.ctorInfo cval) => return cval.cidx
  | _ => return fallbackIdx

def isScalarJoinParamType : LNIRType → Bool
  | .i1 | .i8 | .i16 | .i32 | .i64 | .usize => true
  | _ => false

partial def isTotalScalarExpr : ScalarExpr → Bool
  | .constU64 _ | .constBool _ | .var _ => true
  | .binOp .div _ _ | .binOp .mod _ _
  | .binOp .addChecked256 _ _ | .binOp .subChecked256 _ _ | .binOp .mulChecked256 _ _ => false
  | .binOp _ l r => isTotalScalarExpr l && isTotalScalarExpr r
  | .unaryOp _ a => isTotalScalarExpr a
  | .select c t e | .fma c t e => isTotalScalarExpr c && isTotalScalarExpr t && isTotalScalarExpr e

structure JpDagOutcome where
  retExpr? : Option ScalarExpr := none
  jmpTargets : List (Nat × ScalarExpr × List ScalarExpr) := []
  deriving Inhabited

def mergeJpTargets (condVar : VarId)
    (tTargets eTargets : List (Nat × ScalarExpr × List ScalarExpr)) :
    BridgeM (Option (Array (VarId × LNIRType × ScalarExpr) × List (Nat × ScalarExpr × List ScalarExpr))) := do
  let mut binds : Array (VarId × LNIRType × ScalarExpr) := #[]
  let mut keys : List Nat := []
  for (id, _, _) in tTargets ++ eTargets do
    if !keys.contains id then keys := keys ++ [id]
  let mut out : List (Nat × ScalarExpr × List ScalarExpr) := []
  for id in keys do
    let tEntry? := tTargets.find? (fun (k, _, _) => k == id)
    let eEntry? := eTargets.find? (fun (k, _, _) => k == id)
    match tEntry?, eEntry? with
    | some (_, tReach, tArgs), some (_, eReach, eArgs) =>
      if tArgs.length != eArgs.length then return none
      let reachExpr ←
        if tReach == eReach then pure tReach
        else do
          let rv ← freshBridgeVar .i1
          binds := binds.push (rv, .i1, .select (.var condVar) tReach eReach)
          pure (.var rv)
      let mut mergedArgs : List ScalarExpr := []
      for (ta, ea) in tArgs.zip eArgs do
        if ta == ea then mergedArgs := mergedArgs ++ [ta]
        else
          let av ← freshBridgeVar .i64
          binds := binds.push (av, .i64, .select (.var condVar) ta ea)
          mergedArgs := mergedArgs ++ [.var av]
      out := out ++ [(id, reachExpr, mergedArgs)]
    | some (_, tReach, tArgs), none =>
      let rv ← freshBridgeVar .i1
      binds := binds.push (rv, .i1, .select (.var condVar) tReach (.constBool false))
      out := out ++ [(id, .var rv, tArgs)]
    | none, some (_, eReach, eArgs) =>
      let rv ← freshBridgeVar .i1
      binds := binds.push (rv, .i1, .select (.var condVar) (.constBool false) eReach)
      out := out ++ [(id, .var rv, eArgs)]
    | none, none => pure ()
  return some (binds, out)

partial def collectDagOutcome (accBinds : Array (VarId × LNIRType × ScalarExpr)) (seen : Std.HashSet VarId)
    (code : LNIRCode) : BridgeM (Option (Array (VarId × LNIRType × ScalarExpr) × Std.HashSet VarId × JpDagOutcome)) := do
  match code with
  | .ret rv =>
    let rTy ← getVarType rv
    return if isScalarJoinParamType rTy then some (accBinds, seen, { retExpr? := some (.var rv), jmpTargets := [] }) else none
  | .letBind markerDst .unit (.scalar (.constU64 tagIdx))
      (.letBind tupDst (.tuple (.unit :: _)) (.mkTuple (mv :: argVids)) (.ret rv)) =>
    if markerDst == mv && tupDst == rv then
      return some (accBinds, seen, { retExpr? := none, jmpTargets := [(tagIdx.toNat, .constBool true, argVids.map .var)] })
    else return none
  | .letBind dst ty (.scalar se) rest =>
    if isScalarJoinParamType ty && isTotalScalarExpr se && !seen.contains dst then
      collectDagOutcome (accBinds.push (dst, ty, se)) (seen.insert dst) rest
    else return none
  | .ite cv t e =>
    let some (acc1, seen1, tOut) ← collectDagOutcome accBinds seen t | return none
    let some (acc2, seen2, eOut) ← collectDagOutcome acc1 seen1 e | return none
    let mut curBinds := acc2
    let mut curSeen := seen2
    let mergedRet? ← match tOut.retExpr?, eOut.retExpr? with
      | none, none => pure none
      | some tr, none => pure (some tr)
      | none, some er => pure (some er)
      | some tr, some er =>
        if tr == er then pure (some tr)
        else do
          let rv ← freshBridgeVar .i64
          curBinds := curBinds.push (rv, .i64, .select (.var cv) tr er)
          curSeen := curSeen.insert rv
          pure (some (.var rv))
    let some (mBinds, mTargets) ← mergeJpTargets cv tOut.jmpTargets eOut.jmpTargets | return none
    for b in mBinds do
      curBinds := curBinds.push b
      curSeen := curSeen.insert b.1
    return some (curBinds, curSeen, { retExpr? := mergedRet?, jmpTargets := mTargets })
  | _ => return none

def branchOnReach (reachExpr : ScalarExpr) (jmpBranch elseCode : LNIRCode) : BridgeM LNIRCode := do
  if elseCode == .unreachable || reachExpr == .constBool true then return jmpBranch
  match reachExpr with
  | .constBool false => return elseCode
  | .var cv => return .ite cv jmpBranch elseCode
  | _ =>
    let cv ← freshBridgeVar .i1
    return .letBind cv .i1 (.scalar reachExpr) (.ite cv jmpBranch elseCode)

def mkTagJumpStub (tagIdx : Nat) (argVids : List VarId) (argTys : List LNIRType) : BridgeM LNIRCode := do
  let markerVid ← freshBridgeVar .unit
  let tupTys := LNIRType.unit :: argTys
  let tupVid ← freshBridgeVar (.tuple tupTys)
  return .letBind markerVid .unit (.scalar (.constU64 tagIdx.toUInt64))
    (.letBind tupVid (.tuple tupTys) (.mkTuple (markerVid :: argVids)) (.ret tupVid))

def mkTagJumpFromExprs (tagIdx : Nat) (argExprs : List ScalarExpr) : BridgeM LNIRCode := do
  let mut argVids : List VarId := []
  let mut argBinds : List (VarId × LNIRType × ScalarExpr) := []
  for ae in argExprs do
    match ae with
    | .var av => argVids := argVids ++ [av]
    | _ =>
      let av ← freshBridgeVar .i64
      argBinds := argBinds ++ [(av, .i64, ae)]
      argVids := argVids ++ [av]
  let stub ← mkTagJumpStub tagIdx argVids (argVids.map fun _ => .i64)
  return argBinds.foldr (fun (d, t, s) acc => .letBind d t (.scalar s) acc) stub

def reifyDagOutcome (binds : Array (VarId × LNIRType × ScalarExpr)) (out : JpDagOutcome) : BridgeM LNIRCode := do
  let rec go (targets : List (Nat × ScalarExpr × List ScalarExpr)) : BridgeM LNIRCode := do
    match targets with
    | [] =>
      match out.retExpr? with
      | some (.var rv) => return .ret rv
      | some rExpr =>
        let rv ← freshBridgeVar .i64
        return .letBind rv .i64 (.scalar rExpr) (.ret rv)
      | none => return .unreachable
    | (tagIdx, reachExpr, argExprs) :: rest =>
      let jmpLeaf ← mkTagJumpFromExprs tagIdx argExprs
      if rest.isEmpty && out.retExpr?.isNone && reachExpr == .constBool true then return jmpLeaf
      branchOnReach reachExpr jmpLeaf (← go rest)
  let tail ← go out.jmpTargets
  return binds.foldr (fun (dst, ty, se) acc => .letBind dst ty (.scalar se) acc) tail

def substituteJpTargetInOutcome
    (jpTag : Nat) (jpParamVids : List VarId) (jpParamTys : List LNIRType)
    (jpBinds : Array (VarId × LNIRType × ScalarExpr)) (jpOutcome : JpDagOutcome)
    (kOutcome : JpDagOutcome) :
    BridgeM (Option (Array (VarId × LNIRType × ScalarExpr) × JpDagOutcome)) := do
  match kOutcome.jmpTargets.find? (fun (id, _, _) => id == jpTag) with
  | none =>
    return some (#[], kOutcome)
  | some (_, jpReach, jpArgExprs) =>
    if jpArgExprs.length != jpParamVids.length then return none
    let mut binds : Array (VarId × LNIRType × ScalarExpr) := #[]
    let mut tmpVars : List VarId := []
    for (pTy, aExpr) in jpParamTys.zip jpArgExprs do
      let tv ← freshBridgeVar pTy
      binds := binds.push (tv, pTy, aExpr)
      tmpVars := tmpVars ++ [tv]
    let mut subst : Std.HashMap VarId VarId := {}
    for (pVid, tVid) in jpParamVids.zip tmpVars do
      let pTy ← getVarType pVid
      let freshPVid ← freshBridgeVar pTy
      binds := binds.push (freshPVid, pTy, .var tVid)
      subst := subst.insert pVid freshPVid
    for (bDst, bTy, bSe) in jpBinds do
      let bSe' := substScalarExprVars subst bSe
      let freshBDst ← freshBridgeVar bTy
      binds := binds.push (freshBDst, bTy, bSe')
      subst := subst.insert bDst freshBDst
    let jpRet' := jpOutcome.retExpr?.map (substScalarExprVars subst)
    let jpTargets' := jpOutcome.jmpTargets.map fun (tId, tReach, tArgs) =>
      (tId, substScalarExprVars subst tReach, tArgs.map (substScalarExprVars subst))
    let restTargets := kOutcome.jmpTargets.filter (fun (id, _, _) => id != jpTag)
    let reachVar ← match jpReach with
      | .var rv => pure rv
      | _ =>
        let rv ← freshBridgeVar .i1
        binds := binds.push (rv, .i1, jpReach)
        pure rv
    let mergedRet? ← match jpRet', kOutcome.retExpr? with
      | none, none => pure none
      | some jr, none => pure (some jr)
      | none, some kr => pure (some kr)
      | some jr, some kr =>
        if jr == kr then pure (some jr)
        else do
          let rv ← freshBridgeVar .i64
          binds := binds.push (rv, .i64, .select (.var reachVar) jr kr)
          pure (some (.var rv))
    let mut scaledJpTargets : List (Nat × ScalarExpr × List ScalarExpr) := []
    for (tId, tReach, tArgs) in jpTargets' do
      let effReach ←
        if tReach == .constBool true then pure (.var reachVar)
        else do
          let rv ← freshBridgeVar .i1
          binds := binds.push (rv, .i1, .select (.var reachVar) tReach (.constBool false))
          pure (.var rv)
      scaledJpTargets := scaledJpTargets ++ [(tId, effReach, tArgs)]
    let mut combinedTargets := restTargets
    for (tId, jReach, jArgs) in scaledJpTargets do
      match combinedTargets.find? (fun (id, _, _) => id == tId) with
      | none =>
        combinedTargets := combinedTargets ++ [(tId, jReach, jArgs)]
      | some (_, kReach, kArgs) =>
        if jArgs.length != kArgs.length then return none
        let mReach ← do
          let rv ← freshBridgeVar .i1
          binds := binds.push (rv, .i1, .select (.var reachVar) jReach kReach)
          pure (.var rv)
        let mut mArgs : List ScalarExpr := []
        for (ja, ka) in jArgs.zip kArgs do
          if ja == ka then mArgs := mArgs ++ [ja]
          else
            let av ← freshBridgeVar .i64
            binds := binds.push (av, .i64, .select (.var reachVar) ja ka)
            mArgs := mArgs ++ [.var av]
        combinedTargets := (combinedTargets.filter (fun (id, _, _) => id != tId)) ++ [(tId, mReach, mArgs)]
    return some (binds, { retExpr? := mergedRet?, jmpTargets := combinedTargets })

partial def collectScalarCodeRev (accBinds : Array (VarId × LNIRType × ScalarExpr)) (seen : Std.HashSet VarId)
    (code : LNIRCode) : BridgeM (Option (LNIRType × Array (VarId × LNIRType × ScalarExpr) × Std.HashSet VarId × ScalarExpr)) := do
  match code with
  | .ret rv =>
    let rTy ← getVarType rv
    return if isScalarJoinParamType rTy then some (rTy, accBinds, seen, .var rv) else none
  | .letBind dst ty (.scalar se) rest =>
    if isScalarJoinParamType ty && isTotalScalarExpr se && !seen.contains dst then
      collectScalarCodeRev (accBinds.push (dst, ty, se)) (seen.insert dst) rest
    else return none
  | .ite cv t e =>
    let some (tTy, acc1, seen1, tExpr) ← collectScalarCodeRev accBinds seen t | return none
    let some (eTy, acc2, seen2, eExpr) ← collectScalarCodeRev acc1 seen1 e | return none
    let outTy := if tTy == eTy then tTy else .i64
    let selVid ← freshBridgeVar outTy
    return some (outTy, acc2.push (selVid, outTy, .select (.var cv) tExpr eExpr), seen2.insert selVid, .var selVid)
  | _ => return none

partial def collectTupleCodeRev (accBinds : Array (VarId × LNIRType × ScalarExpr)) (seen : Std.HashSet VarId)
    (code : LNIRCode) : BridgeM (Option (List LNIRType × Array (VarId × LNIRType × ScalarExpr) × Std.HashSet VarId × List ScalarExpr)) := do
  match code with
  | .letBind dst (.tuple fTys) (.mkTuple fVars) (.ret rv) =>
    if dst == rv && !fTys.isEmpty && fTys.length == fVars.length && fTys.all isScalarJoinParamType then
      return some (fTys, accBinds, seen, fVars.map .var)
    else return none
  | .letBind dst ty (.scalar se) rest =>
    if isScalarJoinParamType ty && isTotalScalarExpr se && !seen.contains dst then
      collectTupleCodeRev (accBinds.push (dst, ty, se)) (seen.insert dst) rest
    else return none
  | .ite cv t e =>
    let some (tTys, acc1, seen1, tExprs) ← collectTupleCodeRev accBinds seen t | return none
    let some (eTys, acc2, seen2, eExprs) ← collectTupleCodeRev acc1 seen1 e | return none
    if tTys.length != eTys.length || tExprs.length != eExprs.length then return none
    let outTys := (tTys.zip eTys).map fun (tt, et) => if tt == et then tt else .i64
    let mut curBinds := acc2
    let mut curSeen := seen2
    let mut selExprs : List ScalarExpr := []
    for ((oTy, te), ee) in (outTys.zip tExprs).zip eExprs do
      let sv ← freshBridgeVar oTy
      curBinds := curBinds.push (sv, oTy, .select (.var cv) te ee)
      curSeen := curSeen.insert sv
      selExprs := selExprs ++ [.var sv]
    return some (outTys, curBinds, curSeen, selExprs)
  | _ => return none

partial def codeContainsTupleOp : LNIRCode → Bool
  | .letBind _ _ (.mkTuple _) _ | .letBind _ _ (.projTuple _ _) _ => true
  | .letBind _ _ _ k | .rawStore _ _ _ _ k | .incRef _ _ k | .decRef _ _ k | .parFor _ _ _ _ _ k =>
    codeContainsTupleOp k
  | .ite _ t e | .seqFor _ _ _ _ _ _ t e => codeContainsTupleOp t || codeContainsTupleOp e
  | .ret _ | .unreachable => false

private def initialSeenVarsForCode (st : BridgeState) (code : LNIRCode) : Std.HashSet VarId :=
  let initFromState := st.varTypes.fold (fun s k _ => s.insert k) ({} : Std.HashSet VarId)
  (freeVarsInCode [] [] code).foldl (fun s v => s.insert v) initFromState

def gateCodeWithSymbolicTV (code cand : LNIRCode) (st : BridgeState) (retTy : LNIRType) : LNIRCode :=
  if cand == code then code
  else
    let fvIds := (freeVarsInCode [] [] code).mergeSort (· < ·)
    let synParams : List LNIRParam := fvIds.map fun vid =>
      { id := vid, name := s!"v_{vid}", ty := st.varTypes.getD vid .i64 }
    let srcDecl : LNIRDecl := { name := "_tv_gate", params := synParams, retTy := retTy, body := code }
    let candDecl : LNIRDecl := { srcDecl with body := cand }
    if (LeanNative.Proofs.validateTranslationDecl srcDecl candDecl 64).passed then cand else code

def compressScalarCode (code : LNIRCode) : BridgeM LNIRCode := do
  if codeContainsTupleOp code then
    return code
  let st0 ← get
  let initSeen := initialSeenVarsForCode st0 code
  match ← collectScalarCodeRev #[] initSeen code with
  | some (outTy, binds, _, resExpr) =>
    let cand ← match resExpr with
      | .var rv =>
        pure (binds.foldr (fun (dst, ty, se) acc => .letBind dst ty (.scalar se) acc) (.ret rv))
      | _ =>
        let resVar ← freshBridgeVar outTy
        let tail := LNIRCode.letBind resVar outTy (.scalar resExpr) (.ret resVar)
        pure (binds.foldr (fun (dst, ty, se) acc => .letBind dst ty (.scalar se) acc) tail)
    return gateCodeWithSymbolicTV code cand (← get) outTy
  | none =>
    match ← collectTupleCodeRev #[] initSeen code with
    | some (outTys, binds, _, resExprs) =>
      let mut curBinds := binds
      let mut fieldVars : List VarId := []
      for (fTy, fExpr) in outTys.zip resExprs do
        match fExpr with
        | .var fv => fieldVars := fieldVars ++ [fv]
        | _ =>
          let fv ← freshBridgeVar fTy
          curBinds := curBinds.push (fv, fTy, fExpr)
          fieldVars := fieldVars ++ [fv]
      let tupVar ← freshBridgeVar (.tuple outTys)
      let tail := LNIRCode.letBind tupVar (.tuple outTys) (.mkTuple fieldVars) (.ret tupVar)
      let cand := curBinds.foldr (fun (dst, ty, se) acc => .letBind dst ty (.scalar se) acc) tail
      return gateCodeWithSymbolicTV code cand (← get) (.tuple outTys)
    | none => return code

def bindScalarParamsBefore (paramVids : List VarId) (paramTys : List LNIRType)
    (finalExprs : List ScalarExpr) (body : LNIRCode) : BridgeM LNIRCode := do
  if paramVids.isEmpty then return body
  if paramVids.length == 1 then
    return .letBind paramVids[0]! paramTys[0]! (.scalar finalExprs[0]!) body
  let tmpPairs ← (paramTys.zip finalExprs).mapM fun (pty, expr) => do
    return (← freshBridgeVar pty, pty, expr)
  let copyToParams := ((paramVids.zip paramTys).zip tmpPairs).foldr
    (fun ((pVid, pTy), (tVid, _, _)) acc => .letBind pVid pTy (.scalar (.var tVid)) acc) body
  return tmpPairs.foldr (fun (tVid, pTy, expr) acc => .letBind tVid pTy (.scalar expr) acc) copyToParams

partial def codeIsPureScalarDag {pu} (code : Lean.Compiler.LCNF.Code pu) : Bool :=
  match code with
  | .let _ k => codeIsPureScalarDag k
  | .jp d2 k2 => codeIsPureScalarDag d2.value && codeIsPureScalarDag k2
  | .cases c => !c.alts.isEmpty && c.alts.all (fun alt => codeIsPureScalarDag alt.getCode)
  | .jmp _ _ | .return _ => true
  | _ => false

partial def codeHasJpArityMismatch {pu} (targetFVar : Lean.FVarId) (expectedArity : Nat) (code : Lean.Compiler.LCNF.Code pu) : Bool :=
  match code with
  | .let _ k | .fun _ k _ | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _
  | .del _ k _ | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ | .setTag _ _ k _ =>
    codeHasJpArityMismatch targetFVar expectedArity k
  | .jp d2 k2 => codeHasJpArityMismatch targetFVar expectedArity d2.value || codeHasJpArityMismatch targetFVar expectedArity k2
  | .cases c => c.alts.any (fun alt => codeHasJpArityMismatch targetFVar expectedArity alt.getCode)
  | .jmp fvarId args => fvarId == targetFVar && args.size != expectedArity
  | .return _ | .unreach _ => false

def lowerJoinPoint {pu} (decl : Lean.Compiler.LCNF.FunDecl pu) (k : Lean.Compiler.LCNF.Code pu)
    (lowerCodeFn : Lean.Compiler.LCNF.Code pu → BridgeM LNIRCode) : BridgeM LNIRCode := do
  if codeHasRecursiveJmp decl.fvarId decl.value then
    Lean.throwError s!"[lean-native] unsupported recursive join point `{decl.fvarId.name}`: no qualified loop lowering"
  let jpTy ← lowerBridgeType decl.type
  checkBridgeType "join-point result" decl.type jpTy true (jpTy == .sarray .i8)
  let _ ← internFVar decl.fvarId jpTy
  internParams decl.params true
  let impParams := toImpureParams decl.params
  let paramTys ← impParams.toList.mapM (fun p => lowerBridgeType p.type)
  if paramTys.all isScalarJoinParamType && codeIsPureScalarDag decl.value && codeIsPureScalarDag k && !codeHasJpArityMismatch decl.fvarId impParams.size k then
    let paramVids ← (impParams.toList.zip paramTys).mapM fun (p, pTy) => internFVar p.fvarId pTy true
    let savedSt ← get
    let mut tagMap := savedSt.jpIndexMap
    let mut jpTag : Nat := 0
    match tagMap[decl.fvarId]? with
    | some t => jpTag := t
    | none =>
      jpTag := tagMap.size + 1
      tagMap := tagMap.insert decl.fvarId jpTag
    let mut outerStubs : Std.HashMap Lean.FVarId (Array (Lean.Compiler.LCNF.Param .impure) × LNIRCode) := {}
    let mut canStubAll := true
    for (oId, (oParams, _)) in savedSt.jpMap.toList do
      let oTys ← oParams.toList.mapM (fun p => lowerBridgeType p.type)
      if oTys.all isScalarJoinParamType then
        let mut oTag : Nat := 0
        match tagMap[oId]? with
        | some t => oTag := t
        | none =>
          oTag := tagMap.size + 1
          tagMap := tagMap.insert oId oTag
        let oParamVids ← (oParams.toList.zip oTys).mapM fun (p, oTy) => internFVar p.fvarId oTy
        let oStub ← mkTagJumpStub oTag oParamVids oTys
        outerStubs := outerStubs.insert oId (oParams, oStub)
      else
        canStubAll := false
    if canStubAll then
      let selfStub ← mkTagJumpStub jpTag paramVids paramTys
      let dagRes? ← try
        modify fun st => { st with jpMap := outerStubs, jpIndexMap := tagMap }
        let jpRaw ← lowerCodeFn decl.value
        let jpInitSeen := initialSeenVarsForCode (← get) jpRaw
        match ← collectDagOutcome #[] jpInitSeen jpRaw with
        | none => pure none
        | some (jpBinds, _, jpOut) =>
          modify fun st => { st with jpMap := outerStubs.insert decl.fvarId (impParams, selfStub) }
          let kRaw ← lowerCodeFn k
          let kInitSeen := initialSeenVarsForCode (← get) kRaw
          match ← collectDagOutcome #[] kInitSeen kRaw with
          | none => pure none
          | some (kBinds, _, kOut) =>
            match ← substituteJpTargetInOutcome jpTag paramVids paramTys jpBinds jpOut kOut with
            | none => pure none
            | some (subBinds, finalOut) =>
              modify fun st => { st with jpMap := savedSt.jpMap, jpIndexMap := savedSt.jpIndexMap }
              if finalOut.jmpTargets.isEmpty then
                some <$> reifyDagOutcome (kBinds ++ subBinds) finalOut
              else
                let mut curCode : LNIRCode := ← reifyDagOutcome #[] { retExpr? := finalOut.retExpr?, jmpTargets := [] }
                let mut okOuter := true
                for (tTag, reachExpr, argExprs) in finalOut.jmpTargets.reverse do
                  match tagMap.toList.find? (fun (_, tg) => tg == tTag) with
                  | some (targetFVar, _) =>
                    match savedSt.jpMap[targetFVar]? with
                    | some (oParams, oBody) =>
                      let jmpBranch ←
                        if oBody matches (.letBind _ .unit (.scalar (.constU64 _)) (.letBind _ (.tuple (.unit :: _)) (.mkTuple _) (.ret _))) then
                          mkTagJumpFromExprs tTag argExprs
                        else do
                          let oParamTys ← oParams.toList.mapM (fun p => lowerBridgeType p.type)
                          let oParamVids ← (oParams.toList.zip oParamTys).mapM fun (p, oTy) => internFVar p.fvarId oTy
                          let freshOBody ← freshenJoinPointCode {} oBody
                          bindScalarParamsBefore oParamVids oParamTys argExprs freshOBody
                      curCode ← branchOnReach reachExpr jmpBranch curCode
                    | none => okOuter := false
                  | none => okOuter := false
                if okOuter then
                  let fullCode := (kBinds ++ subBinds).foldr (fun (dst, ty, se) acc => .letBind dst ty (.scalar se) acc) curCode
                  some <$> (if savedSt.jpIndexMap.isEmpty then compressScalarCode fullCode else pure fullCode)
                else
                  pure none
      catch _ =>
        set savedSt
        pure none
      if let some res := dagRes? then
        return res
      set savedSt
    else
      set savedSt
  let prevInJp := (← get).inJoinPointBody
  modify fun st => { st with inJoinPointBody := true }
  let jpBody ← compressScalarCode (← lowerCodeFn decl.value)
  modify fun st => { st with inJoinPointBody := prevInJp, jpMap := st.jpMap.insert decl.fvarId (impParams, jpBody) }
  compressScalarCode (← lowerCodeFn k)

def lowerJmpInstr {pu} (fvarId : Lean.FVarId) (args : Array (Lean.Compiler.LCNF.Arg pu)) : BridgeM LNIRCode := do
  match (← get).jpMap[fvarId]? with
  | some (jpParams, jpBody) =>
    spliceJoinPointJmp jpParams jpBody args
  | none =>
    Lean.throwError s!"[lean-native] unsupported unmapped join point `{fvarId.name}`"

def lowerLocalFunDecl {pu} (decl : Lean.Compiler.LCNF.FunDecl pu) (k : Lean.Compiler.LCNF.Code pu)
    (lowerCodeFn : Lean.Compiler.LCNF.Code pu → BridgeM LNIRCode) : BridgeM LNIRCode := do
  if codeReferencesFVar decl.fvarId decl.value then
    Lean.throwError s!"[lean-native] Unsupported recursive local function `{decl.binderName}`"
  let mut pIds : List VarId := []
  for p in decl.params do
    let pTy ← lowerBridgeType p.type
    checkBridgeType "local function parameter" p.type pTy
    let pid ← internFVar p.fvarId pTy true
    pIds := pIds ++ [pid]
  let fBody ← lowerCodeFn decl.value
  modify fun st => { st with localFunMap := st.localFunMap.insert decl.fvarId (pIds, fBody) }
  lowerCodeFn k

partial def inlineLocalFunCode (ren : Std.HashMap VarId VarId) (dst : VarId) (dstTy : LNIRType)
    (cont : LNIRCode) : LNIRCode → BridgeM LNIRCode
  | .letBind bDst bTy val k => do
    let val' := substLNIRExprVars ren (← get).varTypes val
    let freshDst ← freshBridgeVar bTy
    let k' ← inlineLocalFunCode (ren.insert bDst freshDst) dst dstTy cont k
    return .letBind freshDst bTy val' k'
  | .ite cv t e => do
    let t' ← inlineLocalFunCode ren dst dstTy cont t
    let e' ← inlineLocalFunCode ren dst dstTy (← freshenJoinPointCode {} cont) e
    return .ite (ren.getD cv cv) t' e'
  | .ret rv => return .letBind dst dstTy (.scalar (.var (ren.getD rv rv))) cont
  | .unreachable => return .unreachable
  | _ => Lean.throwError "[lean-native] Unsupported non-scalar instruction inside local function body"

export LeanNative.IR.RealLCNFBridge (
  lowerScalarIntrinsicExpr? lowerBoolBinIntrinsic? lowerUnaryScalarIntrinsic?
)

def lowerTupleOrEnumCtor (ctorName : Lean.Name) (cidx : Nat) (args : Array (Lean.Compiler.LCNF.Arg pu))
    (retTy : LNIRType) : BridgeM LNIRExpr := do
  let env ← getEnv
  let st ← get
  if args.isEmpty then
    if ctorName == ``Bool.false then
      return .scalar (if retTy == .i1 then .constBool false else .constU64 0)
    if ctorName == ``Bool.true then
      return .scalar (if retTy == .i1 then .constBool true else .constU64 1)
    if ctorName == ``Unit.unit || ctorName == ``PUnit.unit then
      return .scalar (.constU64 0)
    match env.find? ctorName with
    | some (.ctorInfo cval) =>
      if cval.numFields == 0 &&
         (retTy == .i8 || retTy == .i16 || retTy == .i1 ||
          (st.allowStage1DHeap && (retTy == .objPtr || retTy == .taggedPtr))) then
        return .scalar (if retTy == .i1 then .constBool (cidx != 0) else .constU64 cidx.toUInt64)
      Lean.throwError s!"[lean-native] Unsupported constructor `{ctorName}`"
    | _ => Lean.throwError s!"[lean-native] Unknown constructor `{ctorName}`"
  if st.allowStage1DHeap then
    match env.find? ctorName with
    | some (.ctorInfo cval) =>
      if cval.numFields ≥ 1 && cval.numFields ≤ 8 then
        let spec ← getRcCtorLayoutSpecM ctorName
        if !spec.scalarSlots.isEmpty then
          -- C1.2: scalar slots are only built by the layout-driven impure lowering (`lowerRcCtorWithScalarsM`)
          Lean.throwError s!"[lean-native] Unsupported scalar-slot constructor `{ctorName}` outside the impure layout lowering"
        let dropCnt := if args.size > cval.numFields then args.size - cval.numFields else 0
        let fieldArgs := args.toList.drop dropCnt
        let argVars ← fieldArgs.mapM (lowerArg · true)
        let argTys ← argVars.mapM getVarType
        if !argVars.isEmpty && argTys.all (fun t => isSupportedStage1BScalarOrTuple t st.arch || t == .objPtr || t == .taggedPtr) then
          return .allocCtor cidx argVars []
    | _ => pure ()
  let isProd := ctorName == ``Prod.mk || ctorName == ``MProd.mk || ctorName == ``PProd.mk
  let fieldStartIdx? : Option Nat :=
    if isProd then some (if args.size > 2 then args.size - 2 else 0)
    else match env.find? ctorName with
      | some (.ctorInfo cval) =>
        match env.find? cval.induct with
        | some (.inductInfo ival) =>
          if ival.ctors.length == 1 && !ival.isRec && ival.numIndices == 0 && cval.numFields ≥ 1 && cval.numFields ≤ 8 then
            some (if args.size > cval.numFields then args.size - cval.numFields else 0)
          else none
        | _ => none
      | _ => none
  match fieldStartIdx? with
  | some dropCnt =>
    let fieldArgs := (args.toList.drop dropCnt)
    let argVars ← fieldArgs.mapM (lowerArg · true)
    let argTys ← argVars.mapM getVarType
    let arch := (← get).arch
    if argVars.isEmpty || !(argTys.all fun t => isSupportedStage1BScalarType t arch || t == .objPtr || t == .taggedPtr) then
      Lean.throwError s!"[lean-native] Unsupported non-scalar or nested tuple/constructor fields in `{ctorName}`"
    return .mkTuple argVars
  | none =>
    Lean.throwError s!"[lean-native] Unsupported payload-carrying constructor `{ctorName}` in Stage 1B"

def lowerTupleProj (fvarId : Lean.FVarId) (idx : Nat) (_retTy : LNIRType) (allowObjAlias : Bool := false) : BridgeM LNIRExpr := do
  let v ← internFVar fvarId
  let vt ← getVarType v
  match vt with
  | .tuple _ => return .projTuple v idx
  | .objPtr | .taggedPtr =>
    if allowObjAlias then return .ctorGetObj v idx
    else Lean.throwError "[lean-native] Unsupported projection on non-tuple heap object in Stage 1B"
  | _ => Lean.throwError s!"[lean-native] Unsupported projection on `{reprStr vt}` in Stage 1B"

def lowerTuplePatternAlt (condVar : VarId) (ctorName : Lean.Name)
    (params : Array (Lean.Compiler.LCNF.Param .pure)) (code : Lean.Compiler.LCNF.Code .pure)
    (lowerPureFn : Lean.Compiler.LCNF.Code .pure → BridgeM LNIRCode) : BridgeM LNIRCode := do
  let env ← getEnv
  let isProd := ctorName == ``Prod.mk || ctorName == ``MProd.mk || ctorName == ``PProd.mk
  let isTupleStruct := match env.find? ctorName with
    | some (.ctorInfo cval) =>
      match env.find? cval.induct with
      | some (.inductInfo ival) => ival.ctors.length == 1 && !ival.isRec && ival.numIndices == 0 && cval.numFields ≤ 8
      | _ => false
    | _ => false
  let condTy ← getVarType condVar
  if (isProd || isTupleStruct) && condTy matches (.tuple _) then
    for p in params do
      let pTy ← lowerBridgeType p.type
      checkBridgeType "tuple pattern parameter" p.type pTy
      let _ ← internFVar p.fvarId pTy true
    let bodyCode ← lowerPureFn code
    let binds ← (params.toList.zip (List.range params.size)).mapM fun (p, pIdx) => do
      let pTy ← lowerBridgeType p.type
      return (← internFVar p.fvarId pTy, pTy, pIdx)
    return binds.foldr (fun (pVid, pTy, pIdx) acc => .letBind pVid pTy (.projTuple condVar pIdx) acc) bodyCode
  Lean.throwError s!"[lean-native] unsupported constructor payload pattern in {ctorName}"

def isClosedConstHelperName : Lean.Name → Bool
  | .str p s =>
    s == "_boxed_const" || (s.splitOn "_boxed_const_").length > 1 ||
    s == "_closed" || (s.splitOn "_closed_").length > 1 ||
    isClosedConstHelperName p
  | .num p _ => isClosedConstHelperName p
  | .anonymous => false

def nameHasCompilerAuxComponent : Lean.Name → Bool
  | .str p s =>
    s == "_boxed" || s == "ctorIdx" || s == "ctorElim" || s == "ctorElimType" ||
    s == "noConfusion" || s == "noConfusionType" || s == "recOn" || s == "casesOn" ||
    s == "brecOn" || s == "below" || s == "ibelow" || s == "elim" ||
    (s.splitOn "___closed__").length > 1 || (s.splitOn "instRepr").length > 1 ||
    (s.splitOn "_cstage").length > 1 || (s.splitOn "_sparseCasesOn_").length > 1 ||
    (s.splitOn "_sizeOf_").length > 1 || s == "sizeOf_spec" ||
    nameHasCompilerAuxComponent p
  | .num p _ => nameHasCompilerAuxComponent p
  | .anonymous => false

def isCompilerGeneratedAuxDecl (env : Lean.Environment) (name : Lean.Name) : Bool :=
  if isClosedConstHelperName name then false
  else Lean.isAuxRecursor env name || Lean.isNoConfusion env name || nameHasCompilerAuxComponent name

private def isBuiltinLNIRRuntimeCall (fn : String) : Bool :=
  fn == "lean_native_ctor_tag" || fn == "lean_native_ctor_set" ||
  fn == "lean_native_ctor_set_scalar" || fn == "lean_native_ctor_set_tag" || fn == "lean_native_del_obj" ||
  fn == "lean_native_box_u64" || fn == "lean_native_unbox_u64" ||
  fn == "lean_native_ensure_exclusive" || fn == "lean_native_sarray_len" ||
  fn == "lean_native_sarray_uget64_le" || fn == "lean_native_sarray_uset64_le" ||
  fn == "lean_native_gf2_affine64" || fn == "lean_native_ternary_logic64"

partial def collectDirectCallees : LNIRCode → List String
  | .letBind _ _ (.call fn _ _ isExt) k =>
    if isExt || isBuiltinLNIRRuntimeCall fn then collectDirectCallees k else fn :: collectDirectCallees k
  | .letBind _ _ _ k | .rawStore _ _ _ _ k | .incRef _ _ k | .decRef _ _ k | .parFor _ _ _ _ _ k =>
    collectDirectCallees k
  | .ite _ t e | .seqFor _ _ _ _ _ _ t e => collectDirectCallees t ++ collectDirectCallees e
  | .ret _ | .unreachable => []

private partial def reachesDeclInCallGraph (edges : List (String × List String))
    (target : String) (fuel : Nat) (visited : List String) (frontier : List String) : Bool :=
  match fuel, frontier with
  | 0, _ => true
  | _, [] => false
  | fuel + 1, cur :: rest =>
    if cur == target then true
    else if visited.contains cur then
      reachesDeclInCallGraph edges target (fuel + 1) visited rest
    else
      let nexts := ((edges.lookup cur).getD []).eraseDups
      reachesDeclInCallGraph edges target fuel (cur :: visited) (nexts ++ rest)

def validateIngestedModule (mod : LNIRModule) : Lean.CoreM Unit := do
  let knownNames := mod.decls.map (·.name)
  let edges := mod.decls.map fun d => (d.name, (collectDirectCallees d.body).eraseDups)
  for d in mod.decls do
    let callees := (edges.lookup d.name).getD []
    for c in callees do
      if !knownNames.contains c then
        Lean.throwError s!"[lean-native] Unsupported unresolved call `{c}` in `{d.name}`"
    if reachesDeclInCallGraph edges d.name (mod.decls.length + 2) [] callees then
      Lean.throwError s!"[lean-native] Unsupported self-tail recursion / mutual recursion involving `{d.name}`"

partial def codeHasResidualHeapOrTupleAbiOp : LNIRCode → Bool
  | .letBind _ ty val k =>
    (ty == .objPtr || ty == .taggedPtr) ||
    (match val with
      | .allocCtor .. | .ctorGetObj .. | .ctorGetScalar .. | .boxScalar .. | .unboxScalar .. | .isExclusive .. => true
      | .call "lean_native_ctor_set" .. | .call "lean_native_ctor_tag" .. => true
      | .call "lean_native_ctor_set_scalar" .. | .call "lean_native_ctor_set_tag" .. | .call "lean_native_del_obj" .. => true
      | _ => false) ||
    codeHasResidualHeapOrTupleAbiOp k
  | .incRef .. | .decRef .. => true
  | .rawStore _ _ _ _ k | .parFor _ _ _ _ _ k => codeHasResidualHeapOrTupleAbiOp k
  | .ite _ t e | .seqFor _ _ _ _ _ _ t e => codeHasResidualHeapOrTupleAbiOp t || codeHasResidualHeapOrTupleAbiOp e
  | .ret _ | .unreachable => false

def filterNonInternalHelperDecls (env : Lean.Environment) (rawPairs : List (Lean.Name × String))
    (arch : TargetArch) (mod : LNIRModule) : Lean.CoreM LNIRModule := do
  let stage1DMangled : List String := rawPairs.filterMap fun (origName, mangled) =>
    if declQualifiesForStage1DHeap env origName arch then some mangled else none
  let isStage1DParamOrRet (ty : LNIRType) : Bool :=
    isSupportedStage1BScalarOrTuple ty arch || ty == .objPtr || ty == .taggedPtr
  let keepNames : List String ← rawPairs.filterMapM fun (origName, mangled) => do
    let isExported := (Lean.getExportNameFor? env origName).isSome
    let isUserConst := (env.find? origName).isSome && !origName.isInternalDetail && !isClosedConstHelperName origName
    if !(isExported || isUserConst) then
      return none
    match mod.decls.find? (·.name == mangled) with
    | none => return none
    | some d =>
      let hasExportedNonScalarSig :=
        d.params.any (fun p => !isSupportedStage1BScalarType p.ty arch) ||
        !isSupportedStage1BScalarType d.retTy arch ||
        (inferReturnedType d.body |>.any (fun rt => !isSupportedStage1BScalarType rt arch))
      let hasUserUnsupportedSig :=
        d.params.any (fun p => !(isSupportedScalarOrFloat p.ty arch || (p.borrow && isSupportedSliceType p.ty))) ||
        !isSupportedScalarOrFloat d.retTy arch ||
        (inferReturnedType d.body |>.any (fun rt => !isSupportedScalarOrFloat rt arch))
      if isExported then
        if hasExportedNonScalarSig || codeHasResidualHeapOrTupleAbiOp d.body then
          Lean.throwError s!"[lean-native] Exported function `{origName}` has unsupported non-scalar signature or unlowered tuple/heap operations"
        return some mangled
      else if stage1DMangled.contains mangled then
        if d.params.any (fun p => !isStage1DParamOrRet p.ty) || !isStage1DParamOrRet d.retTy then
          Lean.throwError s!"[lean-native] Stage 1D helper `{origName}` has unsupported signature"
        return some mangled
      else if hasUserUnsupportedSig then
        return none
      else
        if codeHasResidualHeapOrTupleAbiOp d.body then
          Lean.throwError s!"[lean-native] Function `{origName}` contains unlowered heap/object operations after helper inlining"
        return some mangled
  let edges := mod.decls.map fun d => (d.name, collectDirectCallees d.body)
  let neededBy (roots : List String) : List String :=
    let step (acc : List String) : List String :=
      acc.foldl (fun cur nm =>
        let cs := (edges.lookup nm).getD []
        cs.foldl (fun a c => if a.contains c then a else c :: a) cur) acc
    (List.range (mod.decls.length + 1)).foldl (fun acc _ => step acc) roots
  let liveNames := neededBy keepNames
  if keepNames.isEmpty && !rawPairs.isEmpty then
    Lean.throwError "[lean-native] Module contains no Stage 1B scalar functions after filtering non-scalar helpers"
  let filteredDecls := mod.decls.filter (fun d => liveNames.contains d.name)
  for d in filteredDecls do
    if stage1DMangled.contains d.name then
      if d.params.any (fun p => !isStage1DParamOrRet p.ty) || !isStage1DParamOrRet d.retTy then
        Lean.throwError s!"[lean-native] Live Stage 1D declaration `{d.name}` has unsupported signature"
    else if d.params.any (fun p => !(isSupportedScalarOrFloat p.ty arch || (p.borrow && isSupportedSliceType p.ty))) ||
       !isSupportedScalarOrFloat d.retTy arch ||
       codeHasResidualHeapOrTupleAbiOp d.body then
      Lean.throwError s!"[lean-native] Live declaration `{d.name}` retains non-scalar signature or unlowered object operations"
  return { mod with decls := filteredDecls }

def lowerOsetInstr (fvarId : Lean.FVarId) (idx : Nat) (y : Lean.Compiler.LCNF.Arg .impure)
    (k : Lean.Compiler.LCNF.Code .impure) (lowerK : Lean.Compiler.LCNF.Code .impure → BridgeM LNIRCode) : BridgeM LNIRCode := do
  let st ← get
  let objVid ← internFVar fvarId
  let objTy ← getVarType objVid
  if (st.allowStage1DHeap || st.inJoinPointBody) && (objTy == .objPtr || objTy == .taggedPtr) then
    let valVid ← lowerArg y true
    let idxVid ← freshBridgeVar .i64
    let unitVid ← freshBridgeVar .unit
    let kCode ← lowerK k
    return .letBind idxVid .i64 (.scalar (.constU64 idx.toUInt64))
      (.letBind unitVid .unit (.call "lean_native_ctor_set" [objVid, idxVid, valVid] .unit false) kCode)
  else if isUnboxedScalarOrTuple objTy then
    lowerK k
  else
    Lean.throwError "[lean-native] Unsupported heap field mutation in Stage 1B"

/-- One round of the C1.2 ctor pre-pass over impure LCNF. `ctx` holds the fvars whose ctor is known at this
    point (`let x := ctor`, a `cases` alt's scrutinee, a known join-point param); each `jmp` records, per
    join-point param, the ctor of every non-erased argument (`none` = unknown). -/
partial def collectJmpArgCtors (known : Std.HashMap Lean.FVarId Lean.Name) (ctx : Std.HashMap Lean.FVarId Lean.Name)
    (jpParams : Std.HashMap Lean.FVarId (Array Lean.FVarId))
    (acc : Std.HashMap Lean.FVarId (List (Option Lean.Name))) :
    Lean.Compiler.LCNF.Code .impure → Std.HashMap Lean.FVarId (List (Option Lean.Name))
  | .let decl k =>
    let ctx' := match decl.value with
      | .ctor info _ _ => ctx.insert decl.fvarId info.name
      | _ => ctx
    collectJmpArgCtors known ctx' jpParams acc k
  | .jp decl k =>
    let jpParams' := jpParams.insert decl.fvarId (decl.params.map (·.fvarId))
    let ctxJp := decl.params.foldl (fun c p => match known[p.fvarId]? with | some n => c.insert p.fvarId n | none => c) ctx
    let acc' := collectJmpArgCtors known ctxJp jpParams' acc decl.value
    collectJmpArgCtors known ctx jpParams' acc' k
  | .jmp fvarId args =>
    match jpParams[fvarId]? with
    | some ps =>
      (ps.toList.zip args.toList).foldl (fun a (p, arg) =>
        match arg with
        | .erased => a
        | .fvar x => a.insert p (ctx[x]? :: a.getD p [])
        | _ => a.insert p (none :: a.getD p [])) acc
    | none => acc
  | .cases c =>
    c.alts.foldl (fun a alt =>
      match alt with
      | .ctorAlt info code _ => collectJmpArgCtors known (ctx.insert c.discr info.name) jpParams a code
      | _ => collectJmpArgCtors known ctx jpParams a alt.getCode) acc
  | .setTag x _ k _ => collectJmpArgCtors known (ctx.erase x) jpParams acc k
  | .fun _ k _ | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _ | .oset _ _ _ k _ | .uset _ _ _ k _
  | .sset _ _ _ _ _ k _ => collectJmpArgCtors known ctx jpParams acc k
  | .return _ | .unreach _ => acc

/-- `let x := ctor` binders anywhere in the body (fvars are unique, so this is scope-independent). -/
partial def collectLetCtors (acc : Std.HashMap Lean.FVarId Lean.Name) : Lean.Compiler.LCNF.Code .impure → Std.HashMap Lean.FVarId Lean.Name
  | .let decl k =>
    collectLetCtors (match decl.value with | .ctor info _ _ => acc.insert decl.fvarId info.name | _ => acc) k
  | .jp decl k => collectLetCtors (collectLetCtors acc decl.value) k
  | .cases c => c.alts.foldl (fun a alt => collectLetCtors a alt.getCode) acc
  | .fun _ k _ | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _ | .oset _ _ _ k _ | .uset _ _ _ k _
  | .sset _ _ _ _ _ k _ | .setTag _ _ k _ => collectLetCtors acc k
  | .jmp .. | .return _ | .unreach _ => acc

/-- C1.2 ctor pre-pass: a join-point param's ctor is known iff every non-erased `jmp` argument has the same
    known ctor (fixpoint over nested reset/reuse join points). Anything else stays unknown (fail closed). -/
def collectFVarCtors (code : Lean.Compiler.LCNF.Code .impure) : Std.HashMap Lean.FVarId Lean.Name := Id.run do
  let lets := collectLetCtors {} code
  let mut known : Std.HashMap Lean.FVarId Lean.Name := {}
  for _ in [0:8] do
    let obs := collectJmpArgCtors known {} {} {} code
    let next := obs.fold (fun m p vs =>
      match vs with
      | some n :: rest => if rest.all (· == some n) then m.insert p n else m
      | _ => m) ({} : Std.HashMap Lean.FVarId Lean.Name)
    if next.size == known.size then break
    known := next
  return lets.fold (fun m k v => m.insert k v) known

/-- Run `act` with `v`'s constructor known to be `ctorName` (C1.2 slot resolution inside a `cases` alt). -/
def withActiveCtor {α} (v : VarId) (ctorName : Lean.Name) (act : BridgeM α) : BridgeM α := do
  let old := (← get).activeCtor
  modify fun s => { s with activeCtor := s.activeCtor.insert v ctorName }
  let r ← act
  modify fun s => { s with activeCtor := old }
  return r

/-- `withActiveCtor` when the `cases` scrutinee is a heap var (`some v`), else `act` unchanged. -/
def withActiveCtor? {α} (v? : Option VarId) (ctorName : Lean.Name) (act : BridgeM α) : BridgeM α :=
  match v? with | some v => withActiveCtor v ctorName act | none => act

/-- C1.2 layout of the heap var `v` (= `fvarId`), from the enclosing `cases` alt / `setTag`, else the
    `collectFVarCtors` pre-pass (`let x := ctor`, reset/reuse join-point params); fails closed. -/
def heapCtorLayoutOfM (v : VarId) (fvarId : Lean.FVarId) (what : String) : BridgeM RcCtorLayoutSpec := do
  let st ← get
  let vt ← getVarType v
  if !(st.allowStage1DHeap && (vt == .objPtr || vt == .taggedPtr)) then
    Lean.throwError s!"[lean-native] Unsupported {what} on `{reprStr vt}` in Stage 1B"
  let some ctorName := st.activeCtor[v]? <|> st.fvarCtor[fvarId]?
    | Lean.throwError s!"[lean-native] Unsupported {what}: constructor of the heap object is not statically known (C1.2)"
  getRcCtorLayoutSpecM ctorName

/-- LCNF `uproj i x` / `sproj n off x` → `ctorGetScalar x slot ty` at the C1.2 `scalarFields` slot. -/
def lowerScalarProjM (fvarId : Lean.FVarId) (isUsize : Bool) (i off : Nat) (retTy : LNIRType) : BridgeM LNIRExpr := do
  let v ← internFVar fvarId
  match ← getVarType v with
  | .tuple _ => return .projTuple v (if isUsize then i else off)
  | _ =>
    let spec ← heapCtorLayoutOfM v fvarId "scalar projection"
    let some (slot, ty) := if isUsize then spec.usizeSlot? i else spec.scalarSlot? i off
      | Lean.throwError s!"[lean-native] Unsupported scalar projection [{i},{off}] of `{spec.ctorName}`: no C1.2 slot"
    if !isUsize && retTy != ty then
      Lean.throwError s!"[lean-native] Scalar projection type `{reprStr retTy}` ≠ slot type `{reprStr ty}` of `{spec.ctorName}` (C1.2)"
    return .ctorGetScalar v slot ty

/-- `let x := ctor info objArgs` for a ctor with `usize`/scalar slots: `allocCtor cidx objs zeros`; Lean fills
    the scalar area afterwards with `uset`/`sset` (C1.2, `getCtorLayout`). -/
def lowerRcCtorWithScalarsM (dstFVar : Lean.FVarId) (ctorName : Lean.Name) (args : Array (Lean.Compiler.LCNF.Arg .impure))
    (k : Lean.Compiler.LCNF.Code .impure) (lowerK : Lean.Compiler.LCNF.Code .impure → BridgeM LNIRCode) : BridgeM LNIRCode := do
  let spec ← getRcCtorLayoutSpecM ctorName
  if args.size != spec.objSlots then
    Lean.throwError s!"[lean-native] Unsupported constructor `{ctorName}`: {args.size} args for {spec.objSlots} object slots (C1.2)"
  let objVars ← args.toList.mapM (lowerArg · true)
  for ov in objVars do
    let t ← getVarType ov
    if !(isSupportedStage1BScalarOrTuple t (← get).arch || t == .objPtr || t == .taggedPtr) then
      Lean.throwError s!"[lean-native] Unsupported object field of `{ctorName}` (`{reprStr t}`)"
  let zeros ← spec.scalarSlots.mapM fun (_, ty) => do return (← freshBridgeVar ty, ty)
  let dst ← internFVar dstFVar .objPtr true
  modify fun s => { s with activeCtor := s.activeCtor.insert dst ctorName }
  let kCode ← lowerK k
  let body : LNIRCode := .letBind dst .objPtr (.allocCtor spec.cidx objVars (zeros.map (·.1))) kCode
  return zeros.foldr (fun (z, ty) acc => .letBind z ty (.scalar (.constU64 0)) acc) body

/-- LCNF `uset x i y` / `sset x n off y` → `lean_native_ctor_set_scalar x slot y` (C1.2 / C4.2). -/
def lowerScalarSetM (fvarId : Lean.FVarId) (isUsize : Bool) (i off : Nat) (y : Lean.FVarId)
    (k : Lean.Compiler.LCNF.Code .impure) (lowerK : Lean.Compiler.LCNF.Code .impure → BridgeM LNIRCode) : BridgeM LNIRCode := do
  let objVid ← internFVar fvarId
  if isUnboxedScalarOrTuple (← getVarType objVid) || !(← get).allowStage1DHeap then
    Lean.throwError "[lean-native] Unsupported heap field mutation in Stage 1B"
  let spec ← heapCtorLayoutOfM objVid fvarId "scalar field mutation"
  let some (slot, _) := if isUsize then spec.usizeSlot? i else spec.scalarSlot? i off
    | Lean.throwError s!"[lean-native] Unsupported scalar mutation [{i},{off}] of `{spec.ctorName}`: no C1.2 slot"
  let valVid ← internFVar y
  let idxVid ← freshBridgeVar .i64
  let unitVid ← freshBridgeVar .unit
  let kCode ← lowerK k
  return .letBind idxVid .i64 (.scalar (.constU64 slot.toUInt64))
    (.letBind unitVid .unit (.call "lean_native_ctor_set_scalar" [objVid, idxVid, valVid] .unit false) kCode)

/-- LCNF `setTag x cidx` → `lean_native_ctor_set_tag x cidx`; `x`'s known ctor becomes the `cidx` sibling. -/
def lowerSetTagM (fvarId : Lean.FVarId) (cidx : Nat)
    (k : Lean.Compiler.LCNF.Code .impure) (lowerK : Lean.Compiler.LCNF.Code .impure → BridgeM LNIRCode) : BridgeM LNIRCode := do
  let objVid ← internFVar fvarId
  let vt ← getVarType objVid
  if !((← get).allowStage1DHeap && (vt == .objPtr || vt == .taggedPtr)) then
    Lean.throwError "[lean-native] unsupported constructor tag mutation"
  let env ← getEnv
  if let some cur := (← get).activeCtor[objVid]? <|> (← get).fvarCtor[fvarId]? then
    if let some (.ctorInfo cval) := env.find? cur then
      if let some (.inductInfo ival) := env.find? cval.induct then
        match ival.ctors[cidx]? with
        | some next => modify fun s => { s with activeCtor := s.activeCtor.insert objVid next }
        | none => Lean.throwError s!"[lean-native] setTag {cidx} out of range for `{cval.induct}`"
  let tagVid ← freshBridgeVar .i64
  let unitVid ← freshBridgeVar .unit
  let kCode ← lowerK k
  return .letBind tagVid .i64 (.scalar (.constU64 cidx.toUInt64))
    (.letBind unitVid .unit (.call "lean_native_ctor_set_tag" [objVid, tagVid] .unit false) kCode)

/-- LCNF `del x` → `lean_native_del_obj x` (free the shell, fields untouched: C4.2); legacy `decRef` otherwise. -/
def lowerDelM (fvarId : Lean.FVarId) (k : Lean.Compiler.LCNF.Code .impure)
    (lowerK : Lean.Compiler.LCNF.Code .impure → BridgeM LNIRCode) : BridgeM LNIRCode := do
  let objVid ← internFVar fvarId
  let vt ← getVarType objVid
  if (← get).allowStage1DHeap && (vt == .objPtr || vt == .taggedPtr) then
    let unitVid ← freshBridgeVar .unit
    return .letBind unitVid .unit (.call "lean_native_del_obj" [objVid] .unit false) (← lowerK k)
  lowerRefOp false fvarId 1 (← lowerK k)

/-- Count AST nodes in `Lean.Compiler.LCNF.Code .impure` to size fuel generously for `RealLCNFBridge`. -/
partial def codeAstFuel (code : Lean.Compiler.LCNF.Code .impure) : Nat :=
  match code with
  | .let _ k | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _
  | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ | .setTag _ _ k _ =>
    codeAstFuel k + 2
  | .fun d k _ => codeAstFuel d.value + codeAstFuel k + 4
  | .jp d k =>
    let dFuel := codeAstFuel d.value + 4
    let kFuel := codeAstFuel k + 4
    dFuel * kFuel + dFuel + kFuel + 8
  | .cases c =>
    c.alts.foldl (fun acc alt => acc + codeAstFuel alt.getCode + 4) (c.alts.size + 4)
  | .jmp _ _ | .return _ | .unreach _ => 4

private def collectArgFVarsImpure (acc : List Lean.FVarId) : Lean.Compiler.LCNF.Arg .impure → List Lean.FVarId
  | .fvar id => if acc.contains id then acc else acc ++ [id]
  | _ => acc

/-- Collect operand `FVarId`s referenced in `LetValue .impure` (for standalone `BridgeM` callers). -/
def collectLetValueFVarsImpure (acc : List Lean.FVarId) (lv : Lean.Compiler.LCNF.LetValue .impure) : List Lean.FVarId :=
  let add (xs : List Lean.FVarId) (id : Lean.FVarId) := if xs.contains id then xs else xs ++ [id]
  match lv with
  | .lit _ | .erased | .pap .. => acc
  | .fvar id args => args.foldl collectArgFVarsImpure (add acc id)
  | .ctor _ args _ | .fap _ args _ => args.foldl collectArgFVarsImpure acc
  | .reuse slot _ _ args _ => args.foldl collectArgFVarsImpure (add acc slot)
  | .oproj _ id _ | .uproj _ id _ | .sproj _ _ id _ | .box _ id _ | .unbox id _
  | .isShared id _ | .reset _ id _ => add acc id

/-- Collect free operand `FVarId`s in `Code .impure` (excluding `.jmp` join-point targets and locally bound vars). -/
partial def collectFreeCodeFVarsImpure (bound : Std.HashSet Lean.FVarId) (acc : List Lean.FVarId)
    (code : Lean.Compiler.LCNF.Code .impure) : List Lean.FVarId :=
  let addIfFree (xs : List Lean.FVarId) (id : Lean.FVarId) :=
    if bound.contains id || xs.contains id then xs else xs ++ [id]
  let addArg (xs : List Lean.FVarId) : Lean.Compiler.LCNF.Arg .impure → List Lean.FVarId
    | .fvar id => addIfFree xs id
    | _ => xs
  match code with
  | .let decl k =>
    let acc1 := (collectLetValueFVarsImpure [] decl.value).foldl addIfFree acc
    collectFreeCodeFVarsImpure (bound.insert decl.fvarId) acc1 k
  | .jp decl k =>
    let boundJp := decl.params.foldl (fun s p => s.insert p.fvarId) (bound.insert decl.fvarId)
    let acc1 := collectFreeCodeFVarsImpure boundJp acc decl.value
    collectFreeCodeFVarsImpure (bound.insert decl.fvarId) acc1 k
  | .fun decl k _ =>
    let boundFn := decl.params.foldl (fun s p => s.insert p.fvarId) (bound.insert decl.fvarId)
    let acc1 := collectFreeCodeFVarsImpure boundFn acc decl.value
    collectFreeCodeFVarsImpure (bound.insert decl.fvarId) acc1 k
  | .jmp _ args => args.foldl addArg acc
  | .inc id _ _ _ k _ | .dec id _ _ _ _ k _ | .del id k _ | .setTag id _ k _ =>
    collectFreeCodeFVarsImpure bound (addIfFree acc id) k
  | .oset id _ y k _ =>
    collectFreeCodeFVarsImpure bound (addArg (addIfFree acc id) y) k
  | .uset id _ y k _ | .sset id _ _ y _ k _ =>
    collectFreeCodeFVarsImpure bound (addIfFree (addIfFree acc id) y) k
  | .cases c =>
    let acc1 := addIfFree acc c.discr
    c.alts.foldl (fun a alt =>
      let bAlt := match alt with
        | .alt _ ps _ _ => ps.foldl (fun s p => s.insert p.fvarId) bound
        | _ => bound
      collectFreeCodeFVarsImpure bAlt a alt.getCode) acc1
  | .return id => addIfFree acc id
  | .unreach _ => acc

private partial def collectCodeTypeExprs (acc : List Lean.Expr) (code : Lean.Compiler.LCNF.Code .impure) : List Lean.Expr :=
  let addExpr (xs : List Lean.Expr) (e : Lean.Expr) := if xs.contains e then xs else xs ++ [e]
  match code with
  | .let decl k => collectCodeTypeExprs (addExpr acc decl.type) k
  | .jp decl k | .fun decl k _ =>
    let acc1 := decl.params.foldl (fun a p => addExpr a p.type) (addExpr acc decl.type)
    collectCodeTypeExprs (collectCodeTypeExprs acc1 decl.value) k
  | .cases c =>
    c.alts.foldl (fun a alt =>
      let a1 := match alt with
        | .alt _ ps _ _ => ps.foldl (fun s p => addExpr s p.type) a
        | _ => a
      collectCodeTypeExprs a1 alt.getCode) (addExpr acc c.resultType)
  | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _
  | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ | .setTag _ _ k _ =>
    collectCodeTypeExprs acc k
  | .jmp _ _ | .return _ | .unreach _ => acc

private def collectLetValueCtorAndCalleeNames (ctors callees : List Lean.Name)
    (lv : Lean.Compiler.LCNF.LetValue .impure) : List Lean.Name × List Lean.Name :=
  let add (xs : List Lean.Name) (n : Lean.Name) := if xs.contains n then xs else xs ++ [n]
  match lv with
  | .ctor info _ _ | .reuse _ info _ _ _ => (add ctors info.name, callees)
  | .fap fn _ _ | .pap fn _ _ => (ctors, add callees fn)
  | _ => (ctors, callees)

private partial def collectCodeCtorAndCalleeNames (ctors callees : List Lean.Name)
    (code : Lean.Compiler.LCNF.Code .impure) : List Lean.Name × List Lean.Name :=
  let add (xs : List Lean.Name) (n : Lean.Name) := if xs.contains n then xs else xs ++ [n]
  match code with
  | .let decl k =>
    let (c1, f1) := collectLetValueCtorAndCalleeNames ctors callees decl.value
    collectCodeCtorAndCalleeNames c1 f1 k
  | .jp decl k | .fun decl k _ =>
    let (c1, f1) := collectCodeCtorAndCalleeNames ctors callees decl.value
    collectCodeCtorAndCalleeNames c1 f1 k
  | .cases c =>
    c.alts.foldl (fun (cs, fs) alt =>
      let cs' := match alt with
        | .ctorAlt info _ _ => add cs info.name
        | .alt cname _ _ _ => add cs cname
        | .default _ => cs
      collectCodeCtorAndCalleeNames cs' fs alt.getCode) (ctors, callees)
  | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _
  | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ | .setTag _ _ k _ =>
    collectCodeCtorAndCalleeNames ctors callees k
  | .jmp _ _ | .return _ | .unreach _ => (ctors, callees)

/-- Pre-validate `LetDecl .impure` binder types recursively before delegating to `RealLCNFBridge`. -/
partial def checkImpureLetTypesM (code : Lean.Compiler.LCNF.Code .impure) : BridgeM Unit := do
  match code with
  | .let decl k =>
    let allowHeap := (← get).allowStage1DHeap
    let hasStage1DScalarLayout := match decl.value with
      | .ctor info _ _ => allowHeap && (info.usize > 0 || info.ssize > 0)
      | _ => false
    if !hasStage1DScalarLayout then
      let rawDeclTy ← lowerBridgeType decl.type
      if rawDeclTy != .unit then checkBridgeType s!"let binding `{decl.binderName}`" decl.type rawDeclTy true (rawDeclTy == .sarray .i8)
    checkImpureLetTypesM k
  | .jp decl k =>
    let jpTy ← lowerBridgeType decl.type
    checkBridgeType "join-point result" decl.type jpTy true (jpTy == .sarray .i8)
    for p in decl.params do
      let pTy ← lowerBridgeType p.type
      checkBridgeType "parameter" p.type pTy true (pTy == .sarray .i8)
    checkImpureLetTypesM decl.value
    checkImpureLetTypesM k
  | .cases c =>
    for alt in c.alts do
      checkImpureLetTypesM alt.getCode
  | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _
  | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ | .setTag _ _ k _ =>
    checkImpureLetTypesM k
  | .fun _ _ _ | .jmp _ _ | .return _ | .unreach _ => pure ()

/-- Build a pure `RealBridgeCtx` from `Lean.Environment` and `BridgeState` for `RealLCNFBridge`. -/
def buildRealBridgeCtxM (typeExprs : List Lean.Expr) (ctorSeeds calleeSeeds : List Lean.Name)
    (paramTypeMap : List (Lean.FVarId × LNIRType) := [])
    (knownFVarCtors : List (Lean.FVarId × Lean.Name) := []) : BridgeM RealLCNFBridge.RealBridgeCtx := do
  let env ← getEnv
  let st ← get
  let mut allCtors : List Lean.Name := []
  let mut ctorSiblings : List (Lean.Name × Nat × Lean.Name) := []
  for seed in ctorSeeds do
    if !allCtors.contains seed then allCtors := allCtors ++ [seed]
    if let some (.ctorInfo cval) := env.find? seed then
      if let some (.inductInfo ival) := env.find? cval.induct then
        for sib in ival.ctors do
          if !allCtors.contains sib then allCtors := allCtors ++ [sib]
        for (sib, idx) in ival.ctors.zipIdx do
          if !ctorSiblings.any (fun (c, i, _) => c == seed && i == idx) then
            ctorSiblings := ctorSiblings ++ [(seed, idx, sib)]
  let mut ctorLayouts : List (Lean.Name × RcCtorLayoutSpec) := []
  let mut nullaryCtors : List (Lean.Name × Nat) := []
  let mut tupleStructCtors : List (Lean.Name × Nat) := []
  for cname in allCtors do
    if let some (.ctorInfo cval) := env.find? cname then
      if cval.numFields == 0 then
        nullaryCtors := nullaryCtors ++ [(cname, cval.cidx)]
      if let some (.inductInfo ival) := env.find? cval.induct then
        if ival.ctors.length == 1 && !ival.isRec && ival.numIndices == 0 && cval.numFields ≥ 1 && cval.numFields ≤ 8 then
          tupleStructCtors := tupleStructCtors ++ [(cname, cval.numFields)]
      if st.allowStage1DHeap && cval.numFields ≥ 1 && cval.numFields ≤ 8 then
        if let some spec ← (try some <$> getRcCtorLayoutSpecM cname catch _ => pure none) then
          ctorLayouts := ctorLayouts ++ [(cname, spec)]
  let mut typeOverrides : List (Lean.Expr × LNIRType) := []
  for e in typeExprs do
    let tyEnv := lowerImpureType e (some env)
    let tyPure := RealLCNFBridge.lowerGroundImpureType e
    if tyEnv != tyPure then
      typeOverrides := typeOverrides ++ [(e, tyEnv)]
  let localNames := (st.localDeclNames.push st.selfDeclName).toList.filter (· != .anonymous)
  let mut gfSimdIntrinsics : List (Lean.Name × BinOp) := []
  for fn in calleeSeeds do
    if let some op := trustedGfSimdIntrinsicOp env fn then
      if !gfSimdIntrinsics.any (fun (n, _) => n == fn) then
        gfSimdIntrinsics := gfSimdIntrinsics ++ [(fn, op)]
  let mut localCallees : List (Lean.Name × String) := []
  for fn in calleeSeeds do
    if let some symbol := trustedG0IntrinsicCall? env fn then
      localCallees := localCallees ++ [(fn, symbol)]
  for fn in localNames do
    if !Lean.isExtern env fn && (trustedG0IntrinsicCall? env fn).isNone &&
       (RealLCNFBridge.lowerCanonicalIntrinsicPure? fn [0, 1] .i64 [.i64, .i64] true st.arch gfSimdIntrinsics).isNone &&
       (trustedGfSimdIntrinsicOp env fn).isNone then
      if !localCallees.any (fun (n, _) => n == fn) then
        localCallees := localCallees ++ [(fn, mangleDeclNameInEnv env fn)]
  return {
    arch := st.arch
    allowStage1DHeap := st.allowStage1DHeap
    ctorLayouts := ctorLayouts
    nullaryCtors := nullaryCtors
    tupleStructCtors := tupleStructCtors
    ctorSiblings := ctorSiblings
    typeOverrides := typeOverrides
    paramTypeMap := paramTypeMap
    localCallees := localCallees
    gfSimdIntrinsics := gfSimdIntrinsics
    knownFVarCtors := knownFVarCtors
  }

/-- Convert current `BridgeState` to `RealBridgeState`, pre-interning any free `FVarId`s in `freeFVars`. -/
def bridgeStateToRealM (freeFVars : List Lean.FVarId) : BridgeM RealLCNFBridge.RealBridgeState := do
  for fv in freeFVars do
    if !(← get).localFunMap.contains fv then
      let _ ← internFVar fv
  let st ← get
  return {
    fvarMap := st.fvarToVar.toList
    varTypes := st.varTypes.toList
    activeCtor := st.activeCtor.toList
    jpDecls := []
    nextVarId := st.nextVarId
  }

/-- Synchronize allocated `VarId` counter and bindings back from `RealBridgeState` into `BridgeState`. -/
def syncRealToBridgeStateM (rst : RealLCNFBridge.RealBridgeState) : BridgeM Unit := do
  modify fun st => {
    st with
    fvarToVar := rst.fvarMap.foldl (fun m (f, v) => m.insert f v) st.fvarToVar
    varTypes := rst.varTypes.foldl (fun m (v, t) => m.insert v t) st.varTypes
    activeCtor := rst.activeCtor.foldl (fun m (v, c) => m.insert v c) {}
    nextVarId := max st.nextVarId rst.nextVarId
  }

/-- Delegate `LetValue .impure` lowering directly to `RealLCNFBridge.lowerImpureLetValuePure`. -/
def lowerImpureLetValueViaRealM (lv : Lean.Compiler.LCNF.LetValue .impure) (retTy : LNIRType) : BridgeM LNIRExpr := do
  if let .fvar fvarId args := lv then
    if args.isEmpty && (← get).localFunMap.contains fvarId then
      Lean.throwError "[lean-native] Unsupported escaping local function value"
  let freeFVars := collectLetValueFVarsImpure [] lv
  let (ctors, callees) := collectLetValueCtorAndCalleeNames [] [] lv
  let st ← get
  let ctx ← buildRealBridgeCtxM [] (ctors ++ st.fvarCtor.toList.map Prod.snd ++ st.activeCtor.toList.map Prod.snd)
    callees [] st.fvarCtor.toList
  let rst ← bridgeStateToRealM freeFVars
  match RealLCNFBridge.lowerImpureLetValuePure ctx rst lv retTy with
  | .ok (expr, rst') =>
    syncRealToBridgeStateM rst'
    return expr
  | .error msg => Lean.throwError msg

/-- Delegate `Code .impure` lowering directly to `RealLCNFBridge.lowerRealLCNFCode`. -/
def lowerImpureCodeViaRealM (code : Lean.Compiler.LCNF.Code .impure) : BridgeM LNIRCode := do
  checkImpureLetTypesM code
  let freeFVars := collectFreeCodeFVarsImpure {} [] code
  for fv in freeFVars do
    if (← get).localFunMap.contains fv then
      Lean.throwError "[lean-native] Unsupported higher-order / escaping local function value"
  let typeExprs := collectCodeTypeExprs [] code
  let (ctors, callees) := collectCodeCtorAndCalleeNames [] [] code
  let st ← get
  let knownCtors := (collectFVarCtors code).fold (fun m k v => m.insert k v) st.fvarCtor
  let ctx ← buildRealBridgeCtxM typeExprs
    (ctors ++ knownCtors.toList.map Prod.snd ++ st.activeCtor.toList.map Prod.snd)
    callees [] knownCtors.toList
  let rst ← bridgeStateToRealM freeFVars
  let fuel := codeAstFuel code + 64
  match RealLCNFBridge.lowerRealLCNFCode fuel ctx rst code with
  | .ok (lnir, rst') =>
    syncRealToBridgeStateM rst'
    return lnir
  | .error msg => Lean.throwError msg

mutual
/-- Typed ByteArray frontend extension: use the existing real bridge for each
    scalar/call binding, preserving slice RC rather than erasing ownership. -/
partial def lowerImpureSliceCode (code : Lean.Compiler.LCNF.Code .impure) : BridgeM LNIRCode := do
  match code with
  | .let d k =>
    let segment ← lowerImpureCodeViaRealM (.let d (.return d.fvarId))
    let continuation ← lowerImpureSliceCode k
    let rec append : LNIRCode → Option LNIRCode
      | .letBind v ty rhs rest => .letBind v ty rhs <$> append rest
      | .ret _ => some continuation
      | _ => none
    let some body := append segment
      | Lean.throwError "[lean-native] unsupported non-linear slice binding"
    return body
  | .jp d k => lowerJoinPoint d k lowerImpureSliceCode
  | .jmp id args => lowerJmpInstr id args
  | .cases c =>
    let v ← internFVar c.discr
    let ty ← getVarType v
    if !isSupportedStage1BScalarType ty (← get).arch then
      Lean.throwError "[lean-native] non-scalar slice-loop condition"
    lowerImpureSliceAlts v (c.typeName == ``Bool || ty == .i1) 0 (orderAlts c.alts.toList)
  | .inc fv n _ _ k _ =>
    let v ← internFVar fv
    let rest ← lowerImpureSliceCode k
    if (← getVarType v) == .sarray .i8 then return .incRef v n rest
    lowerRefOp true fv n rest
  | .dec fv n _ _ _ k _ =>
    let v ← internFVar fv
    let rest ← lowerImpureSliceCode k
    if (← getVarType v) == .sarray .i8 then return .decRef v n rest
    lowerRefOp false fv n rest
  | .return fv => return .ret (← internFVar fv)
  | .unreach _ => return .unreachable
  | _ => Lean.throwError "[lean-native] unsupported slice-loop object operation"

partial def lowerImpureSliceAlts (v : VarId) (isBool : Bool) (idx : Nat)
    (alts : List (Lean.Compiler.LCNF.Alt .impure)) : BridgeM LNIRCode := do
  match alts with
  | [] => return .unreachable
  | .default b :: _ => lowerImpureSliceCode b
  | .ctorAlt info b _ :: rest =>
    let ty ← getVarType v
    let cmp ← freshBridgeVar .i1
    return (RealLCNFBridge.lowerTagBranchPure v ty info.cidx isBool cmp
      (← lowerImpureSliceCode b) (← lowerImpureSliceAlts v isBool (idx + 1) rest)).1
  | .alt n ps b _ :: rest =>
    unless ps.isEmpty do Lean.throwError "[lean-native] unsupported slice-loop payload case"
    let ty ← getVarType v
    let cmp ← freshBridgeVar .i1
    return (RealLCNFBridge.lowerTagBranchPure v ty (← lookupCtorIdx n idx) isBool cmp
      (← lowerImpureSliceCode b) (← lowerImpureSliceAlts v isBool (idx + 1) rest)).1
end

partial def pureCodeAstFuel : Lean.Compiler.LCNF.Code .pure → Nat
  | .let _ k => 1 + pureCodeAstFuel k
  | .fun d k _ | .jp d k => 1 + pureCodeAstFuel d.value + pureCodeAstFuel k
  | .cases c => 1 + c.alts.foldl (fun acc a => acc + pureCodeAstFuel a.getCode) 0
  | .return _ | .jmp .. | .unreach _ => 1

def isWordFactTy : LNIRType → Bool
  | .i64 | .usize => true
  | _ => false

def isRawPtrFactTy : LNIRType → Bool
  | .rawPtr _ => true
  | _ => false

def isExclFactTy : LNIRType → Bool
  | .sarray _ | .objPtr => true
  | _ => false

def factVarsInScope (varTys : List (VarId × LNIRType)) : RetainedFact → Bool
  | .idxLt i n =>
    match varTys.lookup i, varTys.lookup n with
    | some ti, some tn => isWordFactTy ti && isWordFactTy tn
    | _, _ => false
  | .noOverflowAdd a b _ _ | .noOverflowSub a b _ _ | .noOverflowMul a b _ _ =>
    match varTys.lookup a, varTys.lookup b with
    | some ta, some tb => isWordFactTy ta && isWordFactTy tb
    | _, _ => false
  | .alignedPtr p _ =>
    match varTys.lookup p with
    | some tp => isRawPtrFactTy tp || isWordFactTy tp
    | none => false
  | .disjointSlices a b la lb =>
    match varTys.lookup a, varTys.lookup b, varTys.lookup la, varTys.lookup lb with
    | some ta, some tb, some tla, some tlb =>
      isRawPtrFactTy ta && isRawPtrFactTy tb && isWordFactTy tla && isWordFactTy tlb
    | _, _, _, _ => false
  | .exclusiveObj o =>
    match varTys.lookup o with
    | some to => isExclFactTy to
    | none => false

partial def collectDeclVarTys (acc : List (VarId × LNIRType)) : LNIRCode → List (VarId × LNIRType)
  | .letBind dst ty _ k => collectDeclVarTys ((dst, ty) :: acc) k
  | .rawStore _ _ _ _ k | .incRef _ _ k | .decRef _ _ k => collectDeclVarTys acc k
  | .ite _ t e => collectDeclVarTys (collectDeclVarTys acc t) e
  | .seqFor idx _ _ accV _ accTy body k =>
    collectDeclVarTys (collectDeclVarTys ((idx, .i64) :: (accV, accTy) :: acc) body) k
  | .parFor out _ _ elemTy _ k => collectDeclVarTys ((out, .sarray elemTy) :: acc) k
  | .ret _ | .unreachable => acc

def attachBaseDeclFactsM (declName : Lean.Name) (d : LNIRDecl) : Lean.CoreM LNIRDecl := do
  let env ← getEnv
  let paramVars := d.params.map (·.id)
  let paramTys := d.params.map fun p => (p.id, p.ty)
  let nextVar := paramVars.foldl max 0 + 64
  let sigFacts := match env.find? declName with
    | none => []
    | some cinfo =>
      (LeanNative.Frontend.ProofRetention.retainedForallParamFacts paramVars nextVar cinfo.type).filter
        (factVarsInScope paramTys)
  let baseFacts ← match ← Lean.Compiler.LCNF.getBaseDecl? declName with
    | none => pure []
    | some baseDecl =>
      let paramSeed :=
        if baseDecl.params.size == d.params.length then
          (baseDecl.params.toList.zip d.params).map fun (bp, lp) => (bp.fvarId, lp.id)
        else []
      if paramSeed.isEmpty then pure []
      else
        let fuel := baseDecl.params.size +
          (match baseDecl.value with | .code c => pureCodeAstFuel c | .extern _ => 0) + 128
        let rawFacts := LeanNative.Frontend.ProofRetention.retainedPureDeclFactsWithSeed
          fuel paramSeed nextVar baseDecl
        pure (rawFacts.filter (factVarsInScope paramTys))
  let merged := (sigFacts ++ baseFacts).foldl LeanNative.IR.consFact d.retainedFacts
  return { d with retainedFacts := merged }

def extractPureDeclFactsWithBridgeState (decl : Lean.Compiler.LCNF.Decl .pure)
    (st : BridgeState) (d : LNIRDecl) : LNIRDecl :=
  let seedMap := st.fvarToVar.toList
  let fuel := decl.params.size +
    (match decl.value with | .code c => pureCodeAstFuel c | .extern _ => 0) + 128
  let liveVarTys := collectDeclVarTys (d.params.map fun p => (p.id, p.ty)) d.body
  let facts := (LeanNative.Frontend.ProofRetention.retainedPureDeclFactsWithSeed
    fuel seedMap st.nextVarId decl).filter (factVarsInScope liveVarTys)
  let merged := facts.foldl LeanNative.IR.consFact d.retainedFacts
  { d with retainedFacts := merged }

private def peelTailLets : LNIRCode → List (VarId × LNIRType × LNIRExpr) × LNIRCode
  | .letBind v ty rhs k =>
    let (bs, tail) := peelTailLets k
    ((v, ty, rhs) :: bs, tail)
  | c => ([], c)

private def resolveTailScalar (bindings : List (VarId × LNIRType × LNIRExpr)) :
    Nat → ScalarExpr → ScalarExpr
  | 0, e => e
  | fuel + 1, .var v =>
    match bindings.reverse.find? (fun (dst, _, _) => dst == v) with
    | some (_, _, .scalar e) => resolveTailScalar bindings fuel e
    | _ => .var v
  | fuel + 1, .binOp op a b => .binOp op (resolveTailScalar bindings fuel a) (resolveTailScalar bindings fuel b)
  | fuel + 1, .unaryOp op a => .unaryOp op (resolveTailScalar bindings fuel a)
  | fuel + 1, .select c t e => .select (resolveTailScalar bindings fuel c)
      (resolveTailScalar bindings fuel t) (resolveTailScalar bindings fuel e)
  | _, e => e

/-- Recognize only a unit-step unsigned bounded loop with one carried value.
    All other parameters must be invariant and the recursive call must be the
    returned value. This frontend extension has Tested assurance. -/
def tryLowerBoundedTailRecBody? (d : LNIRDecl) : Option LNIRCode := do
  let (header, branch) := peelTailLets d.body
  guard (header.all fun (_, _, rhs) => match rhs with | .scalar _ => true | _ => false)
  let .ite cond t e := branch | none
  let resolved := resolveTailScalar header (header.length + 4) (.var cond)
  let (idx, bound, stepThen) ← match resolved with
    | .binOp .lt (.var i) (.var n) => some (i, n, true)
    | .binOp .eq (.select (.binOp .lt (.var i) (.var n)) (.constU64 1) (.constU64 0)) (.constU64 0) =>
      some (i, n, false)
    | .binOp .eq (.select (.binOp .le (.var n) (.var i)) (.constU64 1) (.constU64 0)) (.constU64 0) =>
      some (i, n, true)
    | .unaryOp .not (.binOp .lt (.var i) (.var n)) => some (i, n, false)
    | _ => none
  guard (idx != bound)
  let ip ← d.params.find? (·.id == idx)
  let np ← d.params.find? (·.id == bound)
  guard ((ip.ty == .i64 || ip.ty == .usize) && np.ty == ip.ty)
  let rawStep := if stepThen then t else e
  let exit := if stepThen then e else t
  -- Impure Bool cases may retain the complementary constructor check followed
  -- by unreachable. On the selected path its truth value is already fixed.
  let (stepHeader, stepBranch) := peelTailLets rawStep
  let step ← match stepBranch with
    | .ite innerCond body .unreachable => do
      let test := resolveTailScalar (header ++ stepHeader)
        (header.length + stepHeader.length + 4) (.var innerCond)
      guard (test == .binOp .eq (.select (.binOp .lt (.var idx) (.var bound))
        (.constU64 1) (.constU64 0)) (.constU64 1))
      some (stepHeader.foldr (fun (v, ty, rhs) k => .letBind v ty rhs k) body)
    | _ => some rawStep
  let rec exitReturn? : LNIRCode → Option VarId
    | .ret v => some v
    | .letBind _ _ (.scalar _) k | .incRef _ _ k | .decRef _ _ k => exitReturn? k
    | _ => none
  let exitVar ← exitReturn? exit
  let (exitBinds, _) := peelTailLets exit
  let .var acc := resolveTailScalar exitBinds (exitBinds.length + 2) (.var exitVar) | none
  let ap ← d.params.find? (·.id == acc)
  guard (acc != idx && acc != bound && ap.ty == d.retTy)
  let (stepBinds, stepTail) := peelTailLets step
  let .ret retVar := stepTail | none
  let (retBind :: revBinds) := stepBinds.reverse | none
  let (dst, _, .call self args _ false) := retBind | none
  guard (self == d.name && dst == retVar && args.length == d.params.length)
  let binds := revBinds.reverse
  let env := header ++ binds
  let mut nextAcc := acc
  for (p, a) in d.params.zip args do
    if p.id == idx then
      let next := resolveTailScalar env (env.length + 4) (.var a)
      guard (next == .binOp .add (.var idx) (.constU64 1) ||
             next == .binOp .add (.constU64 1) (.var idx))
    else if p.id == acc then nextAcc := a
    else guard (a == p.id)
  let stepBody := (header ++ binds).foldr
    (fun (v, ty, rhs) k => .letBind v ty rhs k) (.ret nextAcc)
  return .seqFor idx idx bound acc acc ap.ty stepBody exit

/-- Delegate the supported impure fragment to RealLCNFBridge, with explicitly
    labeled frontend extensions for canonical intrinsics and bounded loops. -/
def ingestImpureDeclViaReal (decl : Lean.Compiler.LCNF.Decl .impure)
    (localDeclNames : Array Lean.Name := #[]) (arch : TargetArch := .x86_64)
    (allowRcAdt : Bool := false) : Lean.CoreM LNIRDecl := do
  let env ← getEnv
  let decl := if collectEnvExplicitReturnType? env decl.name == some (.sarray .i8) then
    { decl with
      type := Lean.mkConst ``ByteArray
      value := decl.value.mapCode (rewriteImpureUset64LETypes env) }
    else { decl with value := decl.value.mapCode (rewriteImpureUset64LETypes env) }
  if ← declUsesSignedScalarTransitively decl then
    Lean.throwError s!"[lean-native] Unsupported signed integer type (`Int*` / `ISize`) in `{decl.name}`"
  let metaInfo := getLCNFDeclMetadata env decl.name
  if metaInfo.isExtern then
    Lean.throwError s!"[lean-native] Unsupported `@[extern]` declaration `{decl.name}` in Stage 1B"
  let isExported := (Lean.getExportNameFor? env decl.name).isSome
  checkEnvConstSignatureM env decl.name arch isExported
  let isStage1DHeap := allowRcAdt && !isExported && declQualifiesForStage1DHeap env decl.name arch
  let initSt : BridgeState := {
    mangledSymbol := metaInfo.mangledSymbol, isSimpleGround := metaInfo.isSimpleGround,
    selfDeclName := decl.name, localDeclNames := localDeclNames, arch := arch,
    allowStage1DHeap := isStage1DHeap }
  let action : BridgeM LNIRDecl := do
    let envParamTys ← collectDeclExplicitParamTypesM env decl.name
    let mut paramTypeMap : List (Lean.FVarId × LNIRType) := []
    let mut paramTypesList : List LNIRType := []
    let mut paramIds : List VarId := []
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
        else rawPTy
      if isSupportedSliceType pTy && pTy != .sarray .i8 && !p.borrow then
        Lean.throwError s!"[lean-native] Non-borrowed slice parameter `{p.binderName}` in `{decl.name}` requires borrow (@&)"
      checkBridgeType s!"parameter `{p.binderName}` of `{decl.name}`" p.type pTy true (!isExported || pTy == .sarray .i8)
      let vid ← internFVar p.fvarId pTy true
      paramTypeMap := paramTypeMap ++ [(p.fvarId, pTy)]
      paramTypesList := paramTypesList ++ [pTy]
      paramIds := paramIds ++ [vid]
      pIdx := pIdx + 1
    let retTy ← lowerBridgeType decl.type
    checkBridgeType s!"return type of `{decl.name}`" decl.type retTy true (retTy == .sarray .i8)
    match decl.value with
    | .extern _ =>
      Lean.throwError s!"[lean-native] Unsupported `@[extern]` declaration `{decl.name}` in Stage 1B"
    | .code c =>
      if let some symbol := trustedG0IntrinsicCall? env decl.name then
        let retVar ← freshBridgeVar retTy
        let lnirParams := (decl.params.toList.zip (paramIds.zip paramTypesList)).map fun (p, (vid, pTy)) =>
          { id := vid, name := p.binderName.toString, ty := pTy, borrow := p.borrow : LNIRParam }
        return {
          name := metaInfo.mangledSymbol
          params := lnirParams
          retTy := retTy
          body := .letBind retVar retTy (.call symbol paramIds retTy false) (.ret retVar)
          assurance := .tested }
      if let some intrExpr := tryLowerGfSimdIntrinsic env decl.name paramIds retTy paramTypesList then
        let retVar ← freshBridgeVar retTy
        let lnirParams := (decl.params.toList.zip (paramIds.zip paramTypesList)).map fun (p, (vid, pTy)) =>
          { id := vid, name := p.binderName.toString, ty := pTy, borrow := p.borrow : LNIRParam }
        return {
          name := metaInfo.mangledSymbol, params := lnirParams, retTy := retTy,
          body := .letBind retVar retTy intrExpr (.ret retVar), assurance := .tested,
          isGpuCand := lnirParams.all (fun p => p.ty.isGpuCompatible) && retTy.isGpuCompatible }
      checkImpureLetTypesM c
      let knownCtors := collectFVarCtors c
      let typeExprs := decl.type :: (decl.params.toList.map (·.type) ++ collectCodeTypeExprs [] c)
      let (ctors, callees) := collectCodeCtorAndCalleeNames [] [] c
      let ctx ← buildRealBridgeCtxM typeExprs (ctors ++ knownCtors.toList.map Prod.snd)
        callees paramTypeMap knownCtors.toList
      let fuel := codeAstFuel c + decl.params.size + 64
      let lowered ← if paramTypesList.any isSupportedSliceType || retTy == .sarray .i8 then do
        let body ← lowerImpureSliceCode c
        let params := (decl.params.toList.zip (paramIds.zip paramTypesList)).map fun (p, (vid, pTy)) =>
          { id := vid, name := p.binderName.toString, ty := pTy, borrow := p.borrow : LNIRParam }
        pure (.ok { name := metaInfo.mangledSymbol, params, retTy, body, assurance := .tested } : Except String LNIRDecl)
      else pure (RealLCNFBridge.lowerRealLCNFDecl fuel ctx decl metaInfo.mangledSymbol)
      match lowered with
      | .ok d =>
        let d ← if codeHasSelfTailCall decl.name c then do
          if (← IO.getEnv "LEAN_NATIVE_TRACE_LOOPS") == some "1" then
            IO.eprintln s!"[lean-native] loop candidate {d.name}: {repr d}"
          let some body := tryLowerBoundedTailRecBody? d
            | Lean.throwError s!"[lean-native] unsupported self-tail recursion in {decl.name}: no qualified loop lowering"
          pure { d with body, assurance := .tested }
        else pure d
        let rstAfter := (RealLCNFBridge.internRealParams ctx {} decl.params.toList).2
        let (nextAfter, endVarTypes) := match RealLCNFBridge.lowerRealLCNFCode fuel ctx rstAfter c with
          | .ok (_, rstEnd) => (rstEnd.nextVarId, rstEnd.varTypes)
          | .error _ => (d.params.length + 16, rstAfter.varTypes)
        modify fun s => {
          s with
          varTypes := endVarTypes.foldl (fun m (v, t) => m.insert v t) s.varTypes
          nextVarId := max s.nextVarId (nextAfter + 4) }
        let compressedCand ← compressScalarCode d.body
        let candRetTy := match inferReturnedType compressedCand with | some (.tuple fs) => .tuple fs | _ => d.retTy
        let baseRetTy := match inferReturnedType d.body with | some (.tuple fs) => .tuple fs | _ => d.retTy
        let baseDecl : LNIRDecl := { d with retTy := baseRetTy }
        let candDecl : LNIRDecl := { d with body := compressedCand, retTy := candRetTy }
        let useCompressed :=
          compressedCand != d.body && (LeanNative.Proofs.validateTranslationDecl baseDecl candDecl 64).passed
        let finalBody := if useCompressed then compressedCand else d.body
        let effRetTy := if useCompressed then candRetTy else baseRetTy
        let effAssurance :=
          if useCompressed then AssuranceLevel.combine d.assurance .translationValidated else d.assurance
        let dOut : LNIRDecl := { d with
          body := finalBody
          retTy := effRetTy
          assurance := effAssurance
          isGpuCand := d.params.all (fun p => p.ty.isGpuCompatible) && effRetTy.isGpuCompatible }
        attachBaseDeclFactsM decl.name dOut
      | .error msg => Lean.throwError msg
  Prod.fst <$> action.run initSt

def expandCompilerAuxDecls (declNames : Array Lean.Name) : Lean.CoreM (Array Lean.Name) := do
  let mut out := declNames
  for name in declNames do
    let red := Lean.Name.str name "_redArg"
    if !out.contains red then
      if (← Lean.Compiler.LCNF.getLocalImpureDecl? red).isSome || (← Lean.Compiler.LCNF.getMonoDecl? red).isSome then
        out := out.push red
  return out

def ingestModuleDeclsWith (ingestImpure : Lean.Compiler.LCNF.Decl .impure → Array Lean.Name → TargetArch → Lean.CoreM LNIRDecl)
    (ingestMono : Lean.Compiler.LCNF.Decl .pure → Array Lean.Name → TargetArch → Lean.CoreM LNIRDecl)
    (rawDeclNames : Array Lean.Name) (moduleName : String := "LeanNative.Ingested")
    (arch : TargetArch := .x86_64) : Lean.CoreM LNIRModule := do
  let declNames ← expandCompilerAuxDecls rawDeclNames
  let env ← getEnv
  let mut callGraph : Std.HashMap Lean.Name (List Lean.Name) := {}
  let mut decls : List LNIRDecl := []
  let mut rawPairs : List (Lean.Name × String) := []
  for name in declNames do
    if let some impureDecl ← Lean.Compiler.LCNF.getLocalImpureDecl? name then
      if let .code c := impureDecl.value then
        callGraph := callGraph.insert name (collectCodeLocalCallees declNames c)
      let d ← ingestImpure impureDecl declNames arch
      decls := decls ++ [d]
      rawPairs := rawPairs ++ [(name, d.name)]
    else if let some monoDecl ← Lean.Compiler.LCNF.getMonoDecl? name then
      if let .code c := monoDecl.value then
        callGraph := callGraph.insert name (collectCodeLocalCallees declNames c)
      let d ← ingestMono monoDecl declNames arch
      decls := decls ++ [d]
      rawPairs := rawPairs ++ [(name, d.name)]
  if declsHaveMutualCycle callGraph then
    Lean.throwError s!"[lean-native] unsupported self-tail recursion / mutual recursion in {moduleName}: no qualified loop lowering"
  let rawMod : LNIRModule := { moduleName := moduleName, decls := decls }
  validateIngestedModule rawMod
  filterNonInternalHelperDecls env rawPairs arch (normalizeAndInlineLocalDefs rawMod)

private def diamondCallGraphRegMod : LNIRModule where
  moduleName := "diamond_call_graph_regression"
  decls := [
    { name := "f", params := [{ id := 0, name := "x", ty := .i64 }], retTy := .i64,
      body :=
        .letBind 1 .i64 (.call "g" [0] .i64)
          (.letBind 2 .i64 (.call "h" [0] .i64)
            (.letBind 3 .i64 (.call "g" [1] .i64)
              (.letBind 4 .i64 (.call "h" [2] .i64)
                (.ret 4)))) },
    { name := "g", params := [{ id := 0, name := "x", ty := .i64 }], retTy := .i64,
      body :=
        .letBind 1 .i64 (.call "k" [0] .i64)
          (.letBind 2 .i64 (.call "k" [1] .i64)
            (.ret 2)) },
    { name := "h", params := [{ id := 0, name := "x", ty := .i64 }], retTy := .i64,
      body :=
        .letBind 1 .i64 (.call "k" [0] .i64)
          (.letBind 2 .i64 (.call "k" [1] .i64)
            (.ret 2)) },
    { name := "k", params := [{ id := 0, name := "x", ty := .i64 }], retTy := .i64,
      body := .ret 0 }
  ]

private def visitedFuelRegMod : LNIRModule where
  moduleName := "visited_fuel_regression"
  decls := [
    { name := "f", params := [{ id := 0, name := "x", ty := .i64 }], retTy := .i64,
      body :=
        .letBind 1 .i64 (.call "g" [0] .i64)
          (.letBind 2 .i64 (.call "h" [1] .i64)
            (.letBind 3 .i64 (.call "k" [2] .i64)
              (.ret 3))) },
    { name := "g", params := [{ id := 0, name := "x", ty := .i64 }], retTy := .i64,
      body :=
        .letBind 1 .i64 (.call "h" [0] .i64)
          (.letBind 2 .i64 (.call "k" [1] .i64)
            (.ret 2)) },
    { name := "h", params := [{ id := 0, name := "x", ty := .i64 }], retTy := .i64,
      body := .letBind 1 .i64 (.call "k" [0] .i64) (.ret 1) },
    { name := "k", params := [{ id := 0, name := "x", ty := .i64 }], retTy := .i64,
      body := .ret 0 }
  ]

#guard
  let edges := diamondCallGraphRegMod.decls.map fun d => (d.name, (collectDirectCallees d.body).eraseDups)
  !(reachesDeclInCallGraph edges "f" (diamondCallGraphRegMod.decls.length + 2) [] ["g", "h"])
#guard
  let edges := visitedFuelRegMod.decls.map fun d => (d.name, (collectDirectCallees d.body).eraseDups)
  !(reachesDeclInCallGraph edges "f" (visitedFuelRegMod.decls.length + 2) [] ((edges.lookup "f").getD []))
#eval validateIngestedModule diamondCallGraphRegMod
#eval validateIngestedModule visitedFuelRegMod

end LeanNative.IR
