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

def isSupportedStage1BScalarOrTuple (ty : LNIRType) (arch : TargetArch) : Bool :=
  if isSupportedStage1BScalarType ty arch then true
  else match ty with
    | .tuple fs => !fs.isEmpty && fs.length ≤ 8 && fs.all (isSupportedStage1BScalarType · arch)
    | _ => false

def isFlatUnboxedScalar : LNIRType → Bool
  | .i1 | .i8 | .i16 | .i32 | .i64 | .usize | .u256 | .i256 => true
  | _ => false

def isUnboxedScalarOrTuple : LNIRType → Bool
  | .tuple fs => !fs.isEmpty && fs.all isFlatUnboxedScalar
  | ty => isFlatUnboxedScalar ty

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

def validateSupportedTypeM (ctx : String) (rawTy : Lean.Expr) (ty : LNIRType) (arch : TargetArch)
    (allowInternalObj : Bool := false) : Lean.CoreM Unit := do
  if isClosureOrRuntimeNatExpr rawTy && !(allowInternalObj && (rawTy == ImpureType.tobject || rawTy == ImpureType.tagged)) then
    Lean.throwError s!"[lean-native] Unsupported {ctx} type `{rawTy}` (runtime Nat, tagged object, or function/closure type)"
  if tyContainsUSize ty && !archSupportsUSize arch then
    Lean.throwError s!"[lean-native] Unsupported USize in {ctx} on target `{reprStr arch}`"
  if !(isSupportedStage1BScalarOrTuple ty arch || (allowInternalObj && (ty == .objPtr || ty == .taggedPtr))) then
    Lean.throwError s!"[lean-native] Unsupported non-scalar {ctx} type `{rawTy}` (lowered as `{reprStr ty}`)"

def checkEnvConstSignatureM (env : Lean.Environment) (declName : Lean.Name) (arch : TargetArch)
    (isExported : Bool) : Lean.CoreM Unit := do
  let some cinfo := env.find? declName | return ()
  let rec go (idx : Nat) (t : Lean.Expr) : Lean.CoreM Unit := do
    match t with
    | .forallE pName dom body bi =>
      if dom.isSort || bi == .instImplicit || bi == .implicit then
        go idx body
      else
        let dTy := lowerImpureType dom (some env)
        if isExported then
          validateSupportedTypeM s!"exported parameter `{pName}` of `{declName}`" dom dTy arch false
          if dTy matches (.tuple _) then
            Lean.throwError s!"[lean-native] Unsupported exported tuple parameter `{pName}` in `{declName}`"
        else
          validateSupportedTypeM s!"parameter `{pName}` of `{declName}`" dom dTy arch false
        go (idx + 1) body
    | retExpr =>
      if !retExpr.hasLooseBVars then
        let rTy := lowerImpureType retExpr (some env)
        if isExported then
          validateSupportedTypeM s!"exported return type of `{declName}`" retExpr rTy arch false
          if rTy matches (.tuple _) then
            Lean.throwError s!"[lean-native] Unsupported exported tuple return type in `{declName}`"
        else
          validateSupportedTypeM s!"return type of `{declName}`" retExpr rTy arch false
  go 0 cinfo.type

structure BridgeState where
  fvarToVar      : Std.HashMap Lean.FVarId VarId := {}
  varTypes       : Std.HashMap VarId LNIRType := {}
  jpMap          : Std.HashMap Lean.FVarId (Array (Lean.Compiler.LCNF.Param .impure) × LNIRCode) := {}
  jpIndexMap     : Std.HashMap Lean.FVarId Nat := {}
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

def checkBridgeType (ctx : String) (rawTy : Lean.Expr) (ty : LNIRType) (allowInternalObj : Bool := false) : BridgeM Unit := do
  validateSupportedTypeM ctx rawTy ty (← get).arch allowInternalObj

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
    if !(isSupportedStage1BScalarOrTuple vTy (← get).arch || (allowInternalObj && (vTy == .objPtr || vTy == .taggedPtr))) then
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
    let val' := substLNIRExprVars subst (← get).varTypes val
    let ty' ← match val' with
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
  let argVars ← args.toList.mapM (lowerArg · true)
  let mut subst : Std.HashMap VarId VarId := {}
  for (p, argVar) in jpParams.toList.zip argVars do
    let pTy ← lowerBridgeType p.type
    let origParamVid ← internFVar p.fvarId pTy
    subst := subst.insert origParamVid argVar
  freshenJoinPointCode subst jpBody

def orderAlts (alts : List (Lean.Compiler.LCNF.Alt pu)) : List (Lean.Compiler.LCNF.Alt pu) :=
  alts.filter (fun | .default _ => false | _ => true) ++ alts.filter (fun | .default _ => true | _ => false)

def lowerLitValueM (lit : Lean.Compiler.LCNF.LitValue) (retTy : LNIRType := .i64)
    (allowInternalObj : Bool := false) : BridgeM LNIRExpr := do
  let arch := (← get).arch
  if retTy == .usize && !archSupportsUSize arch then
    Lean.throwError s!"[lean-native] Unsupported USize literal on target `{reprStr arch}`"
  let raw : UInt64 ← match lit with
    | .nat n =>
      if (retTy == .taggedPtr || retTy == .objPtr) && !allowInternalObj then
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
    | .str _ => Lean.throwError "[lean-native] unsupported string literal"
  let masked := match scalarWidthMask? retTy arch with
    | some m => raw &&& m
    | none => raw
  if retTy == .i1 then
    return .scalar (.constBool (masked != 0))
  return .scalar (.constU64 masked)

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

def internParams {pu} (params : Array (Lean.Compiler.LCNF.Param pu)) (allowInternalObj : Bool := false) : BridgeM Unit := do
  for p in params do
    let pTy ← lowerBridgeType p.type
    checkBridgeType "parameter" p.type pTy allowInternalObj
    let _ ← internFVar p.fvarId pTy true

def lowerRefOp (isInc : Bool) (fvarId : Lean.FVarId) (_n : Nat) (kCode : LNIRCode) : BridgeM LNIRCode := do
  let v ← internFVar fvarId
  let vt ← getVarType v
  if isUnboxedScalarOrTuple vt then return kCode
  else if vt == .objPtr || vt == .taggedPtr then return if isInc then .incRef v _n kCode else .decRef v _n kCode
  else Lean.throwError s!"[lean-native] Unsupported heap RC instruction on `{reprStr vt}` in Stage 1B"

def inferImpureRhsType (rhs : LNIRExpr) (declTy : LNIRType) (isBox : Bool) : BridgeM LNIRType := do
  if isBox then
    match rhs with
    | .scalar (.var sv) =>
      let sty ← getVarType sv
      return if isUnboxedScalarOrTuple sty then sty else .i64
    | _ => return .i64
  match rhs with
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

def compressScalarCode (code : LNIRCode) : BridgeM LNIRCode := do
  match ← collectScalarCodeRev #[] {} code with
  | some (outTy, binds, _, resExpr) =>
    match resExpr with
    | .var rv =>
      return binds.foldr (fun (dst, ty, se) acc => .letBind dst ty (.scalar se) acc) (.ret rv)
    | _ =>
      let resVar ← freshBridgeVar outTy
      let tail := LNIRCode.letBind resVar outTy (.scalar resExpr) (.ret resVar)
      return binds.foldr (fun (dst, ty, se) acc => .letBind dst ty (.scalar se) acc) tail
  | none =>
    match ← collectTupleCodeRev #[] {} code with
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
      return curBinds.foldr (fun (dst, ty, se) acc => .letBind dst ty (.scalar se) acc) tail
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
  checkBridgeType "join-point result" decl.type jpTy true
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
        match ← collectDagOutcome #[] {} jpRaw with
        | none => pure none
        | some (jpBinds, _, jpOut) =>
          modify fun st => { st with jpMap := outerStubs.insert decl.fvarId (impParams, selfStub) }
          let kRaw ← lowerCodeFn k
          match ← collectDagOutcome #[] {} kRaw with
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
  let jpBody ← compressScalarCode (← lowerCodeFn decl.value)
  modify fun st => { st with jpMap := st.jpMap.insert decl.fvarId (impParams, jpBody) }
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
        let raw := ScalarExpr.binOp op lMasked rMasked
        some (if mask == 0xFFFFFFFFFFFFFFFF then raw else .binOp .bitAnd raw (.constU64 mask))
    | .div =>
      if retTy != operandTy then none
      else some (.select (.binOp .eq rMasked (.constU64 0)) (.constU64 0) (.binOp .div lMasked rMasked))
    | .mod =>
      if retTy != operandTy then none
      else some (.select (.binOp .eq rMasked (.constU64 0)) lMasked (.binOp .mod lMasked rMasked))
    | .bitAnd | .bitOr | .bitXor =>
      if retTy != operandTy then none
      else
        let raw := ScalarExpr.binOp op lMasked rMasked
        some (if mask == 0xFFFFFFFFFFFFFFFF then raw else .binOp .bitAnd raw (.constU64 mask))
    | .shl =>
      if retTy != operandTy then none
      else
        let shAmt : ScalarExpr := if sMask == 63 then rMasked else .binOp .bitAnd rMasked (.constU64 sMask)
        let raw := ScalarExpr.binOp .shl lMasked shAmt
        some (if mask == 0xFFFFFFFFFFFFFFFF then raw else .binOp .bitAnd raw (.constU64 mask))
    | .shr =>
      if retTy != operandTy then none
      else
        let shAmt : ScalarExpr := if sMask == 63 then rMasked else .binOp .bitAnd rMasked (.constU64 sMask)
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

def lowerTupleOrEnumCtor (ctorName : Lean.Name) (cidx : Nat) (args : Array (Lean.Compiler.LCNF.Arg pu))
    (retTy : LNIRType) : BridgeM LNIRExpr := do
  let env ← getEnv
  if args.isEmpty then
    if ctorName == ``Bool.false then
      return .scalar (if retTy == .i1 then .constBool false else .constU64 0)
    if ctorName == ``Bool.true then
      return .scalar (if retTy == .i1 then .constBool true else .constU64 1)
    if ctorName == ``Unit.unit || ctorName == ``PUnit.unit then
      return .scalar (.constU64 0)
    match env.find? ctorName with
    | some (.ctorInfo cval) =>
      if cval.numFields == 0 && (retTy == .i8 || retTy == .i16 || retTy == .i1) then
        return .scalar (if retTy == .i1 then .constBool (cidx != 0) else .constU64 cidx.toUInt64)
      Lean.throwError s!"[lean-native] Unsupported constructor `{ctorName}`"
    | _ => Lean.throwError s!"[lean-native] Unknown constructor `{ctorName}`"
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
      | _ => false) ||
    codeHasResidualHeapOrTupleAbiOp k
  | .incRef .. | .decRef .. => true
  | .rawStore _ _ _ _ k | .parFor _ _ _ _ _ k => codeHasResidualHeapOrTupleAbiOp k
  | .ite _ t e | .seqFor _ _ _ _ _ _ t e => codeHasResidualHeapOrTupleAbiOp t || codeHasResidualHeapOrTupleAbiOp e
  | .ret _ | .unreachable => false

def filterNonInternalHelperDecls (env : Lean.Environment) (rawPairs : List (Lean.Name × String))
    (arch : TargetArch) (mod : LNIRModule) : Lean.CoreM LNIRModule := do
  let keepNames : List String ← rawPairs.filterMapM fun (origName, mangled) => do
    let isExported := (Lean.getExportNameFor? env origName).isSome
    let isUserConst := (env.find? origName).isSome && !origName.isInternalDetail && !isClosedConstHelperName origName
    if !(isExported || isUserConst) then
      return none
    match mod.decls.find? (·.name == mangled) with
    | none => return none
    | some d =>
      let hasObjOrTupleSig :=
        d.params.any (fun p => !isSupportedStage1BScalarType p.ty arch) ||
        !isSupportedStage1BScalarType d.retTy arch ||
        (inferReturnedType d.body |>.any (fun rt => !isSupportedStage1BScalarType rt arch))
      if isExported then
        if hasObjOrTupleSig || codeHasResidualHeapOrTupleAbiOp d.body then
          Lean.throwError s!"[lean-native] Exported function `{origName}` has unsupported non-scalar signature or unlowered tuple/heap operations"
        return some mangled
      else if hasObjOrTupleSig then
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
    if d.params.any (fun p => !isSupportedStage1BScalarType p.ty arch) ||
       !isSupportedStage1BScalarType d.retTy arch ||
       codeHasResidualHeapOrTupleAbiOp d.body then
      Lean.throwError s!"[lean-native] Live declaration `{d.name}` retains non-scalar signature or unlowered object operations"
  return { mod with decls := filteredDecls }

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
