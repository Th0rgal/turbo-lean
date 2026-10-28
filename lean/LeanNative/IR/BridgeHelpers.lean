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

partial def lowerImpureType (e : Lean.Expr) : LNIRType :=
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
  else
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .const declName _ =>
      if declName == ``UInt8 then .i8
      else if declName == ``UInt16 then .i16
      else if declName == ``UInt32 then .i32
      else if declName == ``UInt64 || declName == ``Nat then .i64
      else if declName == ``LeanNative.IR.UInt256 || (match declName with | .str _ "UInt256" | .str _ "U256" => true | _ => false) then .u256
      else if (match declName with | .str _ "StorageMap" => true | _ => false) then .storageMap
      else if declName == ``USize then .usize
      else if declName == ``Float32 then .f32
      else if declName == ``Float then .f64
      else if declName == ``Bool then .i1
      else if declName == ``Unit || declName == ``PUnit || declName == ``lcErased || declName == ``lcVoid then .unit
      else if declName == ``ByteArray then .sarray .i8
      else if declName == ``FloatArray then .sarray .f64
      else if declName == ``Array then .sarray (args[0]?.map lowerImpureType |>.getD .taggedPtr)
      else if declName == ``Prod || declName == ``MProd || declName == ``PProd then
        match args[0]?, args[1]? with
        | some a, some b => .tuple [lowerImpureType a, lowerImpureType b]
        | _, _ => .objPtr
      else .objPtr
    | .forallE _ _ body _ => lowerImpureType body
    | _ => .objPtr

structure BridgeState where
  fvarToVar      : Std.HashMap Lean.FVarId VarId := {}
  varTypes       : Std.HashMap VarId LNIRType := {}
  jpMap          : Std.HashMap Lean.FVarId (Array (Lean.Compiler.LCNF.Param .impure) × LNIRCode) := {}
  nextVarId      : VarId := 0
  hasExtern      : Bool := false
  mangledSymbol  : String := ""
  isSimpleGround : Bool := false
  selfDeclName   : Lean.Name := .anonymous
  selfLoopAccVar : Option VarId := none
  selfParams     : Array (Lean.Compiler.LCNF.Param .impure) := #[]
  localDeclNames : Array Lean.Name := #[]
  deriving Inhabited

abbrev BridgeM := StateRefT BridgeState Lean.CoreM

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
  | .fvar fvarId => internFVar fvarId
  | _ => freshBridgeVar .unit

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

partial def codeHasSelfTailCall (targetName : Lean.Name) (code : Lean.Compiler.LCNF.Code pu) : Bool :=
  match code with
  | .let decl (.return retFVar) =>
    decl.fvarId == retFVar && (match decl.value with | .fap fn _ _ | .const fn _ _ _ => fn == targetName | _ => false)
  | .let _ k | .fun _ k _ | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _
  | .del _ k _ | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ | .setTag _ _ k _ =>
    codeHasSelfTailCall targetName k
  | .jp decl k => codeHasSelfTailCall targetName decl.value || codeHasSelfTailCall targetName k
  | .cases c => c.alts.any (fun alt => codeHasSelfTailCall targetName alt.getCode)
  | .jmp _ _ | .return _ | .unreach _ => false

def spliceJoinPointJmp (jpParams : Array (Lean.Compiler.LCNF.Param .impure)) (jpBody : LNIRCode)
    (args : Array (Lean.Compiler.LCNF.Arg pu)) : BridgeM LNIRCode := do
  let argVars ← args.toList.mapM lowerArg
  (jpParams.toList.zip argVars).foldrM (fun (p, argVar) accCode => do
    let pTy := lowerImpureType p.type
    return .letBind (← internFVar p.fvarId pTy) pTy (.scalar (.var argVar)) accCode) jpBody

def orderAlts (alts : List (Lean.Compiler.LCNF.Alt pu)) : List (Lean.Compiler.LCNF.Alt pu) :=
  alts.filter (fun | .default _ => false | _ => true) ++ alts.filter (fun | .default _ => true | _ => false)

def lowerLitValue (lit : Lean.Compiler.LCNF.LitValue) : LNIRExpr :=
  match lit with
  | .nat n => .scalar (.constU64 n.toUInt64)
  | .uint8 v => .scalar (.constU64 v.toUInt64)
  | .uint16 v => .scalar (.constU64 v.toUInt64)
  | .uint32 v => .scalar (.constU64 v.toUInt64)
  | .uint64 v | .usize v => .scalar (.constU64 v)
  | .str s => .scalar (.constU64 s.length.toUInt64)

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
    let _ ← internFVar p.fvarId (lowerImpureType p.type)

def lowerJoinPoint {pu} (decl : Lean.Compiler.LCNF.FunDecl pu) (k : Lean.Compiler.LCNF.Code pu)
    (lowerCodeFn : Lean.Compiler.LCNF.Code pu → BridgeM LNIRCode) : BridgeM LNIRCode := do
  let _ ← internFVar decl.fvarId (lowerImpureType decl.type)
  internParams decl.params
  let impParams := toImpureParams decl.params
  if codeHasRecursiveJmp decl.fvarId decl.value then
    let (idxVar, accVar, accTy) ←
      if h2 : decl.params.size ≥ 2 then do
        let p0 := decl.params[0]
        let p1 := decl.params[1]
        let aTy := lowerImpureType p1.type
        pure (← internFVar p0.fvarId .i64, ← internFVar p1.fvarId aTy, aTy)
      else if h1 : decl.params.size = 1 then do
        let p0 := decl.params[0]
        let aTy := lowerImpureType p0.type
        pure (← freshBridgeVar .i64, ← internFVar p0.fvarId aTy, aTy)
      else
        pure (← freshBridgeVar .i64, ← freshBridgeVar .i64, .i64)
    let loVar ← freshBridgeVar .i64
    let hiVar ← freshBridgeVar .i64
    let accInit ← freshBridgeVar accTy
    modify fun st => { st with jpMap := st.jpMap.insert decl.fvarId (impParams, .ret accVar) }
    let stepBody ← lowerCodeFn decl.value
    let kCode ← lowerCodeFn k
    return .letBind loVar .i64 (.scalar (.constU64 0))
      (.letBind hiVar .i64 (.scalar (.constU64 1))
        (.letBind accInit accTy (.scalar (.constU64 0))
          (.seqFor idxVar loVar hiVar accVar accInit accTy stepBody kCode)))
  else
    let jpBody ← lowerCodeFn decl.value
    modify fun st => { st with jpMap := st.jpMap.insert decl.fvarId (impParams, jpBody) }
    lowerCodeFn k

def lowerJmpInstr {pu} (fvarId : Lean.FVarId) (args : Array (Lean.Compiler.LCNF.Arg pu)) : BridgeM LNIRCode := do
  match (← get).jpMap[fvarId]? with
  | some (jpParams, jpBody) =>
    spliceJoinPointJmp jpParams jpBody args
  | none =>
    match args.toList with
    | arg0 :: _ => return .ret (← lowerArg arg0)
    | [] => return .ret (← internFVar fvarId)

def lowerIndexedSet (fvarId : Lean.FVarId) (idx : Nat) (valVar : VarId) (elemTy : LNIRType) (kCode : LNIRCode) : BridgeM LNIRCode := do
  let arrVar ← internFVar fvarId
  let idxVar ← freshBridgeVar .i64
  let dstVar ← freshBridgeVar .objPtr
  return .letBind idxVar .i64 (.scalar (.constU64 idx.toUInt64))
    (.letBind dstVar .objPtr (.sarraySet arrVar idxVar valVar elemTy) kCode)

end LeanNative.IR
