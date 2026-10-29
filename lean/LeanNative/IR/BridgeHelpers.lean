import Lean
import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.Passes
import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.ToImpureType
import Lean.Compiler.LCNF.SimpleGroundExpr
import Lean.Compiler.NameMangling
import Lean.Compiler.ExternAttr
import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.IR.Codec
import LeanNative.IR.LCNF
import LeanNative.Transform.EqSat

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

partial def lowerImpureType (e : Lean.Expr) (env? : Option Lean.Environment := none) : LNIRType :=
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
        | some a, some b => .tuple [lowerImpureType a env?, lowerImpureType b env?]
        | _, _ => .objPtr
      else if let some env := env? then
        (nullaryEnumScalarType? env e).getD .objPtr
      else .objPtr
    | _ => .objPtr

def archSupportsUSize (arch : TargetArch) : Bool :=
  match arch with
  | .nvptx64 | .hybridCpuGpu => false
  | _ => true

def archUSizeMask (arch : TargetArch) : UInt64 :=
  match arch with
  | .wasm32 => 0xFFFFFFFF
  | _ => 0xFFFFFFFFFFFFFFFF

def archUSizeShiftMask (arch : TargetArch) : UInt64 :=
  match arch with
  | .wasm32 => 31
  | _ => 63

def scalarWidthMask? (ty : LNIRType) (arch : TargetArch := .x86_64) : Option UInt64 :=
  match ty with
  | .i8 => some 0xFF
  | .i16 => some 0xFFFF
  | .i32 => some 0xFFFFFFFF
  | .i64 => some 0xFFFFFFFFFFFFFFFF
  | .usize => if archSupportsUSize arch then some (archUSizeMask arch) else none
  | _ => none

def scalarShiftMask? (ty : LNIRType) (arch : TargetArch := .x86_64) : Option UInt64 :=
  match ty with
  | .i8 => some 7
  | .i16 => some 15
  | .i32 => some 31
  | .i64 => some 63
  | .usize => if archSupportsUSize arch then some (archUSizeShiftMask arch) else none
  | _ => none

def isSupportedStage1BScalarType (ty : LNIRType) (arch : TargetArch) : Bool :=
  match ty with
  | .i1 | .i8 | .i16 | .i32 | .i64 | .unit => true
  | .usize => archSupportsUSize arch
  | _ => false

def validateSupportedTypeM (ctx : String) (rawTy : Lean.Expr) (ty : LNIRType) (arch : TargetArch) : Lean.CoreM Unit := do
  if isClosureOrRuntimeNatExpr rawTy then
    Lean.throwError s!"[lean-native] Unsupported {ctx} type `{rawTy}` (runtime Nat, tagged object, or function/closure type)"
  if ty == .usize && !archSupportsUSize arch then
    Lean.throwError s!"[lean-native] Unsupported USize in {ctx} on target `{reprStr arch}`"
  if !isSupportedStage1BScalarType ty arch then
    Lean.throwError s!"[lean-native] Unsupported non-scalar {ctx} type `{rawTy}` (lowered as `{reprStr ty}`)"

structure BridgeState where
  fvarToVar      : Std.HashMap Lean.FVarId VarId := {}
  varTypes       : Std.HashMap VarId LNIRType := {}
  jpMap          : Std.HashMap Lean.FVarId (Array (Lean.Compiler.LCNF.Param .impure) × LNIRCode) := {}
  localFunMap    : Std.HashMap Lean.FVarId (List VarId × LNIRCode) := {}
  nextVarId      : VarId := 0
  hasExtern      : Bool := false
  mangledSymbol  : String := ""
  isSimpleGround : Bool := false
  selfDeclName   : Lean.Name := .anonymous
  localDeclNames : Array Lean.Name := #[]
  arch           : TargetArch := .x86_64
  deriving Inhabited

abbrev BridgeM := StateRefT BridgeState Lean.CoreM

def lowerBridgeType (e : Lean.Expr) : BridgeM LNIRType := do
  return lowerImpureType e (some (← getEnv))

def checkBridgeType (ctx : String) (rawTy : Lean.Expr) (ty : LNIRType) : BridgeM Unit := do
  validateSupportedTypeM ctx rawTy ty (← get).arch

def internFVar (fvarId : Lean.FVarId) (ty : LNIRType := .objPtr) : BridgeM VarId := do
  let st ← get
  match st.fvarToVar[fvarId]? with
  | some vid => return vid
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

def lowerArg (arg : Lean.Compiler.LCNF.Arg pu) : BridgeM VarId := do
  match arg with
  | .fvar fvarId =>
    if ((← get).localFunMap.contains fvarId) then
      Lean.throwError "[lean-native] Unsupported higher-order / escaping local function value"
    let vid ← internFVar fvarId
    let vTy ← getVarType vid
    if !isSupportedStage1BScalarType vTy (← get).arch then
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

private def remapVar (ren : List (VarId × VarId)) (v : VarId) : VarId :=
  (ren.lookup v).getD v

private def remapScalarExpr (ren : List (VarId × VarId)) : ScalarExpr → ScalarExpr
  | .constU64 v => .constU64 v
  | .constBool b => .constBool b
  | .var id => .var (remapVar ren id)
  | .binOp op l r => .binOp op (remapScalarExpr ren l) (remapScalarExpr ren r)
  | .unaryOp op a => .unaryOp op (remapScalarExpr ren a)
  | .select c t f => .select (remapScalarExpr ren c) (remapScalarExpr ren t) (remapScalarExpr ren f)
  | .fma a b c => .fma (remapScalarExpr ren a) (remapScalarExpr ren b) (remapScalarExpr ren c)

private def remapLNIRExpr (ren : List (VarId × VarId)) : LNIRExpr → LNIRExpr
  | .scalar se => .scalar (remapScalarExpr ren se)
  | .constU256 l => .constU256 l
  | .mkTuple vs => .mkTuple (vs.map (remapVar ren))
  | .projTuple tv i => .projTuple (remapVar ren tv) i
  | .allocCtor t os ss => .allocCtor t (os.map (remapVar ren)) (ss.map (remapVar ren))
  | .ctorGetObj cv i => .ctorGetObj (remapVar ren cv) i
  | .ctorGetScalar cv i ty => .ctorGetScalar (remapVar ren cv) i ty
  | .isExclusive ov => .isExclusive (remapVar ren ov)
  | .sarrayLen av => .sarrayLen (remapVar ren av)
  | .sarrayDataPtr av ty => .sarrayDataPtr (remapVar ren av) ty
  | .sarrayEnsureExclusive av ty => .sarrayEnsureExclusive (remapVar ren av) ty
  | .sarrayGet av iv ty => .sarrayGet (remapVar ren av) (remapVar ren iv) ty
  | .sarraySet av iv vv ty => .sarraySet (remapVar ren av) (remapVar ren iv) (remapVar ren vv) ty
  | .rawLoad pv iv ty => .rawLoad (remapVar ren pv) (remapVar ren iv) ty
  | .boxScalar vv ty => .boxScalar (remapVar ren vv) ty
  | .unboxScalar bv ty => .unboxScalar (remapVar ren bv) ty
  | .mulDivDown a b c => .mulDivDown (remapVar ren a) (remapVar ren b) (remapVar ren c)
  | .mulDivUp a b c => .mulDivUp (remapVar ren a) (remapVar ren b) (remapVar ren c)
  | .storageLoad m s => .storageLoad (remapVar ren m) (remapVar ren s)
  | .storageStore m s v => .storageStore (remapVar ren m) (remapVar ren s) (remapVar ren v)
  | .call fn args rty ext => .call fn (args.map (remapVar ren)) rty ext

partial def freshenLNIRCode (ren : List (VarId × VarId)) : LNIRCode → BridgeM LNIRCode
  | .letBind dst ty val k => do
    let freshDst ← freshBridgeVar ty
    let val' := remapLNIRExpr ren val
    let k' ← freshenLNIRCode ((dst, freshDst) :: ren) k
    return .letBind freshDst ty val' k'
  | .rawStore pv iv vv ty k => do
    return .rawStore (remapVar ren pv) (remapVar ren iv) (remapVar ren vv) ty (← freshenLNIRCode ren k)
  | .incRef ov c k => return .incRef (remapVar ren ov) c (← freshenLNIRCode ren k)
  | .decRef ov c k => return .decRef (remapVar ren ov) c (← freshenLNIRCode ren k)
  | .ite cv t e => return .ite (remapVar ren cv) (← freshenLNIRCode ren t) (← freshenLNIRCode ren e)
  | .seqFor iv lv hv av ai aty step k => do
    let freshIv ← freshBridgeVar .i64
    let freshAv ← freshBridgeVar aty
    let renStep := (iv, freshIv) :: (av, freshAv) :: ren
    let step' ← freshenLNIRCode renStep step
    let k' ← freshenLNIRCode ((av, freshAv) :: ren) k
    return .seqFor freshIv (remapVar ren lv) (remapVar ren hv) freshAv (remapVar ren ai) aty step' k'
  | .parFor ov lv ins ety kern k => do
    return .parFor (remapVar ren ov) (remapVar ren lv) (ins.map (remapVar ren)) ety kern (← freshenLNIRCode ren k)
  | .ret v => return .ret (remapVar ren v)
  | .unreachable => return .unreachable

def spliceJoinPointJmp (jpParams : Array (Lean.Compiler.LCNF.Param .impure)) (jpBody : LNIRCode)
    (args : Array (Lean.Compiler.LCNF.Arg pu)) : BridgeM LNIRCode := do
  if args.size != jpParams.size then
    Lean.throwError s!"[lean-native] Join-point arity mismatch: expected {jpParams.size}, got {args.size}"
  let argVars ← args.toList.mapM lowerArg
  let mut ren : List (VarId × VarId) := []
  let mut binds : List (VarId × LNIRType × VarId) := []
  for (p, argVar) in jpParams.toList.zip argVars do
    let pTy ← lowerBridgeType p.type
    checkBridgeType "join-point parameter" p.type pTy
    let origPid ← internFVar p.fvarId pTy
    let freshPid ← freshBridgeVar pTy
    ren := (origPid, freshPid) :: ren
    binds := binds ++ [(freshPid, pTy, argVar)]
  let freshBody ← freshenLNIRCode ren jpBody
  return binds.foldr (fun (pid, pTy, argVar) acc => .letBind pid pTy (.scalar (.var argVar)) acc) freshBody

def orderAlts (alts : List (Lean.Compiler.LCNF.Alt pu)) : List (Lean.Compiler.LCNF.Alt pu) :=
  alts.filter (fun | .default _ => false | _ => true) ++ alts.filter (fun | .default _ => true | _ => false)

def lowerLitValueM (lit : Lean.Compiler.LCNF.LitValue) (retTy : LNIRType) : BridgeM LNIRExpr := do
  let arch := (← get).arch
  if retTy == .usize && !archSupportsUSize arch then
    Lean.throwError s!"[lean-native] Unsupported USize literal on target `{reprStr arch}`"
  let raw : UInt64 ← match lit with
    | .nat n =>
      if retTy == .taggedPtr || retTy == .objPtr then
        Lean.throwError "[lean-native] Unsupported runtime Nat literal"
      let m := (scalarWidthMask? retTy arch).getD 0xFFFFFFFFFFFFFFFF
      pure ((n % (2 ^ 64)).toUInt64 &&& m)
    | .uint8 v => pure v.toUInt64
    | .uint16 v => pure v.toUInt64
    | .uint32 v => pure v.toUInt64
    | .uint64 v => pure v
    | .usize v =>
      if !archSupportsUSize arch then
        Lean.throwError s!"[lean-native] Unsupported USize literal on target `{reprStr arch}`"
      pure (v &&& archUSizeMask arch)
    | .str _ => Lean.throwError "[lean-native] Unsupported String literal in Stage 1B scalar subset"
  let masked := match scalarWidthMask? retTy arch with
    | some m => raw &&& m
    | none => raw
  if retTy == .i1 then
    return .scalar (.constBool (masked != 0))
  return .scalar (.constU64 masked)

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

def canonClmul64Repr : String := canon_decl_repr% LeanNative.IR.clmul64 : LeanNative.IR.clmul64
def canonClmul64GoRepr : String := canon_decl_repr% LeanNative.IR.clmul64 : LeanNative.IR.clmul64.go._unary
def canonClmul64HiRepr : String := canon_decl_repr% LeanNative.IR.clmul64Hi : LeanNative.IR.clmul64Hi
def canonClmul64HiGoRepr : String := canon_decl_repr% LeanNative.IR.clmul64Hi : LeanNative.IR.clmul64Hi.go._unary
def canonGf2AffineRepr : String := canon_decl_repr% LeanNative.IR.gf2Affine : LeanNative.IR.gf2Affine
def canonGf2AffineGoRepr : String := canon_decl_repr% LeanNative.IR.gf2Affine : LeanNative.IR.gf2Affine.go._unary
def canonEor3Repr : String := canon_decl_repr% LeanNative.IR.eor3 : LeanNative.IR.eor3

def trustedGfSimdIntrinsicOp (env : Lean.Environment) (fnName : Lean.Name) : Option BinOp := do
  let (op, expBody, expGoOpt) ← match fnName with
    | .str _ "clmul64Hi" => some (BinOp.clmul64Hi, canonClmul64HiRepr, some canonClmul64HiGoRepr)
    | .str _ "clmul64"   => some (BinOp.clmul64, canonClmul64Repr, some canonClmul64GoRepr)
    | .str _ "gf2Affine" => some (BinOp.gf2Affine, canonGf2AffineRepr, some canonGf2AffineGoRepr)
    | .str _ "eor3"      => some (BinOp.eor3, canonEor3Repr, none)
    | _ => none
  let .defnInfo decl ← env.find? fnName | none
  let u64 := Lean.mkConst ``UInt64
  let sig := Lean.Expr.forallE `a u64 (Lean.Expr.forallE `b u64 u64 .default) .default
  guard (decl.levelParams.isEmpty && decl.safety == .safe && decl.type.eqv sig && !Lean.isExtern env fnName)
  guard (normalizeIntrinsicDecl fnName decl.value == expBody)
  if let some expGo := expGoOpt then
    let .defnInfo goDecl ← env.find? (fnName ++ `go._unary) | none
    guard (normalizeIntrinsicDecl fnName goDecl.value == expGo)
  return op

def tryLowerGfSimdIntrinsic (env : Lean.Environment) (fnName : Lean.Name) (argVars : List VarId)
    (retTy : LNIRType := .i64) (argTys : List LNIRType := []) : Option LNIRExpr :=
  match argVars with
  | [lhs, rhs] =>
    if retTy == .i64 && (argTys.isEmpty || argTys == [.i64, .i64]) then
      (trustedGfSimdIntrinsicOp env fnName).map fun op => .scalar (.binOp op (.var lhs) (.var rhs))
    else none
  | _ => none

def internParams {pu} (params : Array (Lean.Compiler.LCNF.Param pu)) : BridgeM Unit := do
  for p in params do
    let pTy ← lowerBridgeType p.type
    checkBridgeType "parameter" p.type pTy
    let _ ← internFVar p.fvarId pTy

def lowerJoinPoint {pu} (decl : Lean.Compiler.LCNF.FunDecl pu) (k : Lean.Compiler.LCNF.Code pu)
    (lowerCodeFn : Lean.Compiler.LCNF.Code pu → BridgeM LNIRCode) : BridgeM LNIRCode := do
  if codeHasRecursiveJmp decl.fvarId decl.value then
    Lean.throwError s!"[lean-native] Unsupported recursive join point `{decl.binderName}` in Stage 1B scalar subset"
  let jpTy ← lowerBridgeType decl.type
  checkBridgeType "join-point result" decl.type jpTy
  let _ ← internFVar decl.fvarId jpTy
  internParams decl.params
  let impParams := toImpureParams decl.params
  let jpBody ← lowerCodeFn decl.value
  modify fun st => { st with jpMap := st.jpMap.insert decl.fvarId (impParams, jpBody) }
  lowerCodeFn k

def lowerJmpInstr {pu} (fvarId : Lean.FVarId) (args : Array (Lean.Compiler.LCNF.Arg pu)) : BridgeM LNIRCode := do
  match (← get).jpMap[fvarId]? with
  | some (jpParams, jpBody) =>
    spliceJoinPointJmp jpParams jpBody args
  | none =>
    Lean.throwError "[lean-native] Unsupported jump to unknown or out-of-scope join point"

def lowerLocalFunDecl {pu} (decl : Lean.Compiler.LCNF.FunDecl pu) (k : Lean.Compiler.LCNF.Code pu)
    (lowerCodeFn : Lean.Compiler.LCNF.Code pu → BridgeM LNIRCode) : BridgeM LNIRCode := do
  if codeReferencesFVar decl.fvarId decl.value then
    Lean.throwError s!"[lean-native] Unsupported recursive local function `{decl.binderName}`"
  let mut pIds : List VarId := []
  for p in decl.params do
    let pTy ← lowerBridgeType p.type
    checkBridgeType "local function parameter" p.type pTy
    let pid ← internFVar p.fvarId pTy
    pIds := pIds ++ [pid]
  let fBody ← lowerCodeFn decl.value
  modify fun st => { st with localFunMap := st.localFunMap.insert decl.fvarId (pIds, fBody) }
  lowerCodeFn k

partial def inlineLocalFunCode (ren : List (VarId × VarId)) (dst : VarId) (dstTy : LNIRType)
    (cont : LNIRCode) : LNIRCode → BridgeM LNIRCode
  | .letBind bDst bTy val k => do
    let freshDst ← freshBridgeVar bTy
    let val' := remapLNIRExpr ren val
    let k' ← inlineLocalFunCode ((bDst, freshDst) :: ren) dst dstTy cont k
    return .letBind freshDst bTy val' k'
  | .ite cv t e => do
    let t' ← inlineLocalFunCode ren dst dstTy cont t
    let e' ← inlineLocalFunCode ren dst dstTy cont e
    return .ite (remapVar ren cv) t' e'
  | .ret rv => return .letBind dst dstTy (.scalar (.var (remapVar ren rv))) cont
  | .unreachable => return .unreachable
  | _ => Lean.throwError "[lean-native] Unsupported non-scalar instruction inside local function body"

def lowerScalarIntrinsicExpr? (op : BinOp) (lhs rhs : VarId) (operandTy retTy : LNIRType)
    (arch : TargetArch) : Option ScalarExpr := do
  if (operandTy == .usize || retTy == .usize) && !archSupportsUSize arch then none else
  let wrapBool (cmp : ScalarExpr) : Option ScalarExpr :=
    if retTy == .i8 then some (.select cmp (.constU64 1) (.constU64 0))
    else if retTy == .i1 then some cmp
    else none
  if operandTy == .i1 then
    let bL : ScalarExpr := .var lhs
    let bR : ScalarExpr := .var rhs
    match op with
    | .bitAnd => wrapBool (.select bL bR (.constBool false))
    | .bitOr  => wrapBool (.select bL (.constBool true) bR)
    | .bitXor => wrapBool (.unaryOp .not (.binOp .eq bL bR))
    | .eq     => wrapBool (.binOp .eq bL bR)
    | _       => none
  else
    let mask ← scalarWidthMask? operandTy arch
    let sMask ← scalarShiftMask? operandTy arch
    let lMasked : ScalarExpr := if mask == 0xFFFFFFFFFFFFFFFF then .var lhs else .binOp .bitAnd (.var lhs) (.constU64 mask)
    let rMasked : ScalarExpr := if mask == 0xFFFFFFFFFFFFFFFF then .var rhs else .binOp .bitAnd (.var rhs) (.constU64 mask)
    match op with
    | .add | .sub | .mul =>
      if retTy != operandTy then none
      else
        let raw := ScalarExpr.binOp op (.var lhs) (.var rhs)
        some (if mask == 0xFFFFFFFFFFFFFFFF then raw else .binOp .bitAnd raw (.constU64 mask))
    | .div | .mod =>
      if retTy != operandTy then none
      else some (.binOp op lMasked rMasked)
    | .bitAnd | .bitOr | .bitXor =>
      if retTy != operandTy then none
      else
        let raw := ScalarExpr.binOp op (.var lhs) (.var rhs)
        some (if mask == 0xFFFFFFFFFFFFFFFF then raw else .binOp .bitAnd raw (.constU64 mask))
    | .shl =>
      if retTy != operandTy then none
      else
        let shAmt : ScalarExpr := if sMask == 63 then .var rhs else .binOp .bitAnd (.var rhs) (.constU64 sMask)
        let raw := ScalarExpr.binOp .shl lMasked shAmt
        some (if mask == 0xFFFFFFFFFFFFFFFF then raw else .binOp .bitAnd raw (.constU64 mask))
    | .shr =>
      if retTy != operandTy then none
      else
        let shAmt : ScalarExpr := if sMask == 63 then .var rhs else .binOp .bitAnd (.var rhs) (.constU64 sMask)
        some (.binOp .shr lMasked shAmt)
    | .eq | .lt | .le =>
      wrapBool (.binOp op lMasked rMasked)
    | _ => none

def lowerBoolBinIntrinsic? (fnName : Lean.Name) (lhs rhs : VarId) (argTys : List LNIRType)
    (retTy : LNIRType) : Option LNIRExpr := do
  let toCond (v : VarId) (t : LNIRType) : Option ScalarExpr :=
    if t == .i1 then some (.var v)
    else if t == .i8 then some (.unaryOp .not (.binOp .eq (.binOp .bitAnd (.var v) (.constU64 1)) (.constU64 0)))
    else none
  let wrapOut (bExpr : ScalarExpr) : Option LNIRExpr :=
    if retTy == .i1 then some (.scalar bExpr)
    else if retTy == .i8 then some (.scalar (.select bExpr (.constU64 1) (.constU64 0)))
    else none
  let [tL, tR] := argTys | none
  let cL ← toCond lhs tL
  let cR ← toCond rhs tR
  if fnName == ``Bool.and then wrapOut (.select cL cR (.constBool false))
  else if fnName == ``Bool.or then wrapOut (.select cL (.constBool true) cR)
  else if fnName == ``Bool.xor || fnName == `Bool.bne || fnName == `bne then wrapOut (.unaryOp .not (.binOp .eq cL cR))
  else if fnName == ``Bool.beq then wrapOut (.binOp .eq cL cR)
  else none

def lowerUnaryScalarIntrinsic? (fnName : Lean.Name) (arg : VarId) (argTys : List LNIRType)
    (retTy : LNIRType) (arch : TargetArch) : Option LNIRExpr := do
  let [srcTy] := argTys | none
  if fnName == ``Bool.not then
    if srcTy == .i1 && retTy == .i1 then
      return .scalar (.unaryOp .not (.var arg))
    else if srcTy == .i8 && retTy == .i8 then
      let isZero := ScalarExpr.binOp .eq (.binOp .bitAnd (.var arg) (.constU64 1)) (.constU64 0)
      return .scalar (.select isZero (.constU64 1) (.constU64 0))
    else none
  else if fnName == ``Bool.toUInt8 || fnName == ``Bool.toUInt16 ||
          fnName == ``Bool.toUInt32 || fnName == ``Bool.toUInt64 || fnName == ``Bool.toUSize then
    let expectedRet : LNIRType :=
      if fnName == ``Bool.toUInt8 then .i8
      else if fnName == ``Bool.toUInt16 then .i16
      else if fnName == ``Bool.toUInt32 then .i32
      else if fnName == ``Bool.toUInt64 then .i64
      else .usize
    guard ((srcTy == .i1 || srcTy == .i8) && retTy == expectedRet && isSupportedStage1BScalarType expectedRet arch)
    if srcTy == .i1 then
      return .scalar (.select (.var arg) (.constU64 1) (.constU64 0))
    else
      return .scalar (.binOp .bitAnd (.var arg) (.constU64 1))
  else
    let (expectedTy, isNeg) ←
      if fnName == ``UInt8.complement then some (LNIRType.i8, false)
      else if fnName == ``UInt16.complement then some (.i16, false)
      else if fnName == ``UInt32.complement then some (.i32, false)
      else if fnName == ``UInt64.complement then some (.i64, false)
      else if fnName == ``USize.complement then some (.usize, false)
      else if fnName == ``UInt8.neg then some (.i8, true)
      else if fnName == ``UInt16.neg then some (.i16, true)
      else if fnName == ``UInt32.neg then some (.i32, true)
      else if fnName == ``UInt64.neg then some (.i64, true)
      else if fnName == ``USize.neg then some (.usize, true)
      else none
    guard (srcTy == expectedTy && retTy == expectedTy)
    let mask ← scalarWidthMask? expectedTy arch
    let raw := if isNeg then ScalarExpr.binOp .sub (.constU64 0) (.var arg) else ScalarExpr.unaryOp .not (.var arg)
    return .scalar (if mask == 0xFFFFFFFFFFFFFFFF then raw else .binOp .bitAnd raw (.constU64 mask))

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
  Lean.isAuxRecursor env name || Lean.isNoConfusion env name || nameHasCompilerAuxComponent name

private partial def collectDirectCallees : LNIRCode → List String
  | .letBind _ _ (.call fn _ _ isExt) k =>
    if isExt then collectDirectCallees k else fn :: collectDirectCallees k
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
      reachesDeclInCallGraph edges target fuel visited rest
    else
      let nexts := (edges.lookup cur).getD []
      reachesDeclInCallGraph edges target fuel (cur :: visited) (nexts ++ rest)

def validateIngestedModule (mod : LNIRModule) : Lean.CoreM Unit := do
  let knownNames := mod.decls.map (·.name)
  let edges := mod.decls.map fun d => (d.name, collectDirectCallees d.body)
  for d in mod.decls do
    let callees := (edges.lookup d.name).getD []
    for c in callees do
      if !knownNames.contains c then
        Lean.throwError s!"[lean-native] Unsupported unresolved call `{c}` in `{d.name}`"
    if reachesDeclInCallGraph edges d.name (mod.decls.length + 2) [] callees then
      Lean.throwError s!"[lean-native] Unsupported direct or mutual recursion involving `{d.name}`"

def filterNonInternalHelperDecls (env : Lean.Environment) (rawPairs : List (Lean.Name × String))
    (mod : LNIRModule) : LNIRModule :=
  let keepNames : List String := rawPairs.filterMap fun (origName, mangled) =>
    let isExported := (Lean.getExportNameFor? env origName).isSome
    let isUserConst := (env.find? origName).isSome && !origName.isInternalDetail
    if isExported || isUserConst then some mangled else none
  let neededBy (roots : List String) : List String :=
    let edges := mod.decls.map fun d => (d.name, collectDirectCallees d.body)
    let step (acc : List String) : List String :=
      acc.foldl (fun cur nm =>
        let cs := (edges.lookup nm).getD []
        cs.foldl (fun a c => if a.contains c then a else c :: a) cur) acc
    (List.range (mod.decls.length + 1)).foldl (fun acc _ => step acc) roots
  let liveNames := neededBy keepNames
  { mod with decls := mod.decls.filter (fun d => liveNames.contains d.name) }

end LeanNative.IR
