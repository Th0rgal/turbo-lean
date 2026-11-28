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
  let e := e.consumeMData
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
  let e := e.consumeMData
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

def exprCodomainIsProp (env? : Option Lean.Environment) (e : Lean.Expr) : Bool :=
  let e := e.consumeMData
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
          validateSupportedTypeM s!"exported parameter `{pName}` of `{declName}`" dom dTy arch false arch.isFreestandingEmbedded false
          if dTy matches (.tuple _) then
            Lean.throwError s!"[lean-native] Unsupported exported tuple parameter `{pName}` in `{declName}`"
        else if !(isStage1D && isSupportedStage1DHeapAdtExpr env arch dom) then
          validateSupportedTypeM s!"parameter `{pName}` of `{declName}`" dom dTy arch false true true
        go (idx + 1) body
    | retExpr =>
      if !retExpr.hasLooseBVars then
        let rTy := lowerImpureType retExpr (some env)
        if isExported then
          validateSupportedTypeM s!"exported return type of `{declName}`" retExpr rTy arch false false false
          if rTy matches (.tuple _) then
            Lean.throwError s!"[lean-native] Unsupported exported tuple return type in `{declName}`"
        else if !(isStage1D && isSupportedStage1DHeapAdtExpr env arch retExpr) then
          validateSupportedTypeM s!"return type of `{declName}`" retExpr rTy arch false false true
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

end LeanNative.IR
