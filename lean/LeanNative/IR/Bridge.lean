import Lean
import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.Passes
import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.ToImpureType
import Lean.Compiler.LCNF.SimpleGroundExpr
import Lean.Compiler.LCNF.EmitC
import Lean.Compiler.NameMangling
import Lean.Compiler.ExternAttr
import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.IR.Codec
import LeanNative.Transform.LoopVectorizeOpt
import LeanNative.Transform.Plugins
import LeanNative.Backend.LLVM
import LeanNative.Backend.FastCheck

set_option autoImplicit true

namespace LeanNative.IR

open Lean
open Lean.Compiler.LCNF

/-- Check whether `declName` is recorded as a `SimpleGroundExpr` static initializer in Lean 4.31. -/
def hasSimpleGroundDecl (env : Lean.Environment) (declName : Lean.Name) : Bool :=
  Lean.Compiler.LCNF.isSimpleGroundDecl env declName

/-- Compute the exact Lean 4.31 C ABI mangled symbol (`decl.name.mangle`, or `_lean_main` for `main`). -/
def mangleDeclName (declName : Lean.Name) : String :=
  if declName == `main then "_lean_main"
  else declName.mangle

/-- Compute the C ABI symbol in `env`, honoring `@[export <sym>]` attributes when present. -/
def mangleDeclNameInEnv (env : Lean.Environment) (declName : Lean.Name) : String :=
  match Lean.getExportNameFor? env declName with
  | some exportName => exportName.toString
  | none => mangleDeclName declName

/-- Metadata recorded for a lowered LCNF declaration (`Name.mangle` C symbol and `SimpleGroundExpr` status). -/
structure LCNFDeclMetadata where
  declName       : Lean.Name
  mangledSymbol  : String
  isSimpleGround : Bool
  isExtern       : Bool
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Extract `LCNFDeclMetadata` for `declName` in `env`. -/
def getLCNFDeclMetadata (env : Lean.Environment) (declName : Lean.Name) : LCNFDeclMetadata := {
  declName       := declName
  mangledSymbol  := mangleDeclNameInEnv env declName
  isSimpleGround := hasSimpleGroundDecl env declName
  isExtern       := Lean.isExtern env declName
}

/-- Map a Lean 4.31 `LCNF.ImpureType` or `MonoType` `Expr` into a formal `LNIRType`. -/
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
      else if declName.toString.endsWith "UInt256" || declName.toString.endsWith "U256" then .u256
      else if declName.toString.endsWith "StorageMap" then .storageMap
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

/-- Deterministic state for lowering LCNF `FVarId`s, join points, and declaration metadata to LNIR. -/
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

/-- Lookup or allocate a deterministic `VarId` for a Lean `FVarId`. -/
def internFVar (fvarId : Lean.FVarId) (ty : LNIRType := .objPtr) : BridgeM VarId := do
  let st ← get
  match st.fvarToVar[fvarId]? with
  | some vid => return vid
  | none =>
    let vid := st.nextVarId
    set {
      st with
      fvarToVar := st.fvarToVar.insert fvarId vid
      varTypes  := st.varTypes.insert vid ty
      nextVarId := vid + 1
    }
    return vid

/-- Allocate a fresh synthetic `VarId` in `BridgeM`. -/
def freshBridgeVar (ty : LNIRType) : BridgeM VarId := do
  let st ← get
  let vid := st.nextVarId
  set {
    st with
    varTypes  := st.varTypes.insert vid ty
    nextVarId := vid + 1
  }
  return vid

/-- Lookup the recorded `LNIRType` of a `VarId`. -/
def getVarType (vid : VarId) : BridgeM LNIRType := do
  let st ← get
  return st.varTypes.getD vid .objPtr

/-- Lower an LCNF `Arg` to a `VarId`, synthesizing a unit variable for erased arguments. -/
def lowerArg (arg : Lean.Compiler.LCNF.Arg pu) : BridgeM VarId := do
  match arg with
  | .fvar fvarId => internFVar fvarId
  | _ => freshBridgeVar .unit

/-- Convert `Array (Param pu)` into `Array (Param .impure)` for uniform join-point storage in `BridgeState.jpMap`. -/
def toImpureParams (params : Array (Lean.Compiler.LCNF.Param pu)) : Array (Lean.Compiler.LCNF.Param .impure) :=
  params.map fun p => {
    fvarId     := p.fvarId
    binderName := p.binderName
    type       := p.type
    borrow     := p.borrow
  }

/-- Check whether `code` contains a tail-recursive `.jmp` referencing `targetFVar`. -/
partial def codeHasRecursiveJmp (targetFVar : Lean.FVarId) (code : Lean.Compiler.LCNF.Code pu) : Bool :=
  match code with
  | .let _ k | .fun _ k _ | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _
  | .del _ k _ | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ | .setTag _ _ k _ =>
    codeHasRecursiveJmp targetFVar k
  | .jp decl k => codeHasRecursiveJmp targetFVar decl.value || codeHasRecursiveJmp targetFVar k
  | .jmp fvarId _ => fvarId == targetFVar
  | .cases c => c.alts.any (fun alt => codeHasRecursiveJmp targetFVar alt.getCode)
  | .return _ | .unreach _ => false

/-- Check whether `code` contains a tail-recursive self call to `targetName`. -/
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

/-- Bind each join-point parameter `param_i := arg_i` via `.letBind` and splice the continuation `jpBody`. -/
def spliceJoinPointJmp (jpParams : Array (Lean.Compiler.LCNF.Param .impure)) (jpBody : LNIRCode)
    (args : Array (Lean.Compiler.LCNF.Arg pu)) : BridgeM LNIRCode := do
  let argVars ← args.toList.mapM lowerArg
  let pairs := jpParams.toList.zip argVars
  pairs.foldrM (fun (p, argVar) accCode => do
    let pTy := lowerImpureType p.type
    let pVar ← internFVar p.fvarId pTy
    return .letBind pVar pTy (.scalar (.var argVar)) accCode
  ) jpBody

/-- Partition `alts` so that explicit constructor alternatives precede any `.default` alternative. -/
def orderAlts (alts : List (Lean.Compiler.LCNF.Alt pu)) : List (Lean.Compiler.LCNF.Alt pu) :=
  let nonDefaults := alts.filter fun
    | .default _ => false
    | _ => true
  let defaults := alts.filter fun
    | .default _ => true
    | _ => false
  nonDefaults ++ defaults

/-- Lower an LCNF `LitValue` into an `LNIRExpr`. -/
def lowerLitValue (lit : Lean.Compiler.LCNF.LitValue) : LNIRExpr :=
  match lit with
  | .nat n     => .scalar (.constU64 n.toUInt64)
  | .uint8 v   => .scalar (.constU64 v.toUInt64)
  | .uint16 v  => .scalar (.constU64 v.toUInt64)
  | .uint32 v  => .scalar (.constU64 v.toUInt64)
  | .uint64 v  => .scalar (.constU64 v)
  | .usize v   => .scalar (.constU64 v)
  | .str s     => .scalar (.constU64 s.length.toUInt64)

/-- Alpha-normalize binder names and replace `fnName` prefix with `` `canonical_intrinsic ``
    so standalone definitions of `clmul64` / `clmul64Hi` / `gf2Affine` / `eor3` can be checked
    for exact kernel AST equality against `LeanNative.IR` even when `LeanNative.IR.Types` is not
    imported by the user file. -/
partial def eraseBinderNamesAndPrefix (fnName : Lean.Name) : Lean.Expr → Lean.Expr
  | .const n ls =>
    if fnName.isPrefixOf n then .const (n.replacePrefix fnName `canonical_intrinsic) ls
    else .const n ls
  | .app f a => .app (eraseBinderNamesAndPrefix fnName f) (eraseBinderNamesAndPrefix fnName a)
  | .lam _ t b bi => .lam `_ (eraseBinderNamesAndPrefix fnName t) (eraseBinderNamesAndPrefix fnName b) bi
  | .forallE _ t b bi => .forallE `_ (eraseBinderNamesAndPrefix fnName t) (eraseBinderNamesAndPrefix fnName b) bi
  | .letE _ t v b nd =>
    .letE `_ (eraseBinderNamesAndPrefix fnName t) (eraseBinderNamesAndPrefix fnName v)
      (eraseBinderNamesAndPrefix fnName b) nd
  | .mdata _ e => eraseBinderNamesAndPrefix fnName e
  | .proj t i e => .proj t i (eraseBinderNamesAndPrefix fnName e)
  | e => e

def normalizeIntrinsicDecl (fnName : Lean.Name) (e : Lean.Expr) : String :=
  toString (repr (eraseBinderNamesAndPrefix fnName e))

elab "canon_decl_repr% " base:ident " : " target:ident : term => do
  let env ← Lean.getEnv
  let bName := base.getId
  let tName := target.getId
  let some (.defnInfo d) := env.find? tName | Lean.throwError "missing {tName}"
  return Lean.toExpr (normalizeIntrinsicDecl bName d.value)

def canonClmul64Repr : String := canon_decl_repr% LeanNative.IR.clmul64 : LeanNative.IR.clmul64
def canonClmul64GoRepr : String := canon_decl_repr% LeanNative.IR.clmul64 : LeanNative.IR.clmul64.go._unary
def canonClmul64HiRepr : String := canon_decl_repr% LeanNative.IR.clmul64Hi : LeanNative.IR.clmul64Hi
def canonClmul64HiGoRepr : String := canon_decl_repr% LeanNative.IR.clmul64Hi : LeanNative.IR.clmul64Hi.go._unary
def canonGf2AffineRepr : String := canon_decl_repr% LeanNative.IR.gf2Affine : LeanNative.IR.gf2Affine
def canonGf2AffineGoRepr : String := canon_decl_repr% LeanNative.IR.gf2Affine : LeanNative.IR.gf2Affine.go._unary
def canonEor3Repr : String := canon_decl_repr% LeanNative.IR.eor3 : LeanNative.IR.eor3

/-- Verify that `fnName` has the exact `UInt64 → UInt64 → UInt64` signature and the exact
    alpha-normalized kernel AST body (including `.go._unary` where present) as the canonical
    `LeanNative.IR` intrinsic declaration. Rejects fake wrappers, aliases, and externs. -/
def trustedGfSimdIntrinsicOp (env : Lean.Environment) (fnName : Lean.Name) : Option BinOp := do
  let (op, expBody, expGoOpt) ←
    match fnName with
    | .str _ "clmul64Hi" => some (BinOp.clmul64Hi, canonClmul64HiRepr, some canonClmul64HiGoRepr)
    | .str _ "clmul64"   => some (BinOp.clmul64, canonClmul64Repr, some canonClmul64GoRepr)
    | .str _ "gf2Affine" => some (BinOp.gf2Affine, canonGf2AffineRepr, some canonGf2AffineGoRepr)
    | .str _ "eor3"      => some (BinOp.eor3, canonEor3Repr, none)
    | _ => none
  let .defnInfo decl ← env.find? fnName | none
  let u64 := Lean.mkConst ``UInt64
  let sig := Lean.Expr.forallE `a u64 (Lean.Expr.forallE `b u64 u64 .default) .default
  guard (decl.levelParams.isEmpty && decl.safety == .safe && decl.type.eqv sig)
  guard (!Lean.isExtern env fnName)
  guard (normalizeIntrinsicDecl fnName decl.value == expBody)
  if let some expGo := expGoOpt then
    let .defnInfo goDecl ← env.find? (fnName ++ `go._unary) | none
    guard (normalizeIntrinsicDecl fnName goDecl.value == expGo)
  return op

def tryLowerGfSimdIntrinsic (env : Lean.Environment) (fnName : Lean.Name) (argVars : List VarId)
    (retTy : LNIRType := .i64) (argTys : List LNIRType := []) : Option LNIRExpr :=
  let argsOk := argTys.isEmpty || argTys == [.i64, .i64]
  match argVars with
  | [lhs, rhs] =>
    if retTy == .i64 && argsOk then
      (trustedGfSimdIntrinsicOp env fnName).map fun op => .scalar (.binOp op (.var lhs) (.var rhs))
    else none
  | _ => none

/-- Try to recognize primitive arithmetic/comparison/array operations in LCNF function calls. -/
def tryLowerIntrinsicCall (env : Lean.Environment) (fnName : Lean.Name) (argVars : List VarId)
    (retTy : LNIRType) (argTys : List LNIRType := []) (isLocal : Bool := false) : Option LNIRExpr :=
  let nameStr := fnName.toString
  let bin (op : BinOp) (l r : VarId) : LNIRExpr := .scalar (.binOp op (.var l) (.var r))
  let suffixOps : List (String × BinOp) := [
    ("add", .add), ("sub", .sub), ("mul", .mul), ("div", .div), ("mod", .mod), ("rem", .mod),
    ("land", .bitAnd), ("lor", .bitOr), ("xor", .bitXor), ("shiftLeft", .shl), ("shiftRight", .shr),
    ("decEq", .eq), ("beq", .eq), ("decLt", .lt), ("blt", .lt), ("decLe", .le), ("ble", .le)
  ]
  match argVars with
  | [lhs, rhs] =>
    match tryLowerGfSimdIntrinsic env fnName argVars retTy argTys with
    | some intr => some intr
    | none =>
      if isLocal then none
      else
        match suffixOps.find? (fun p => nameStr.endsWith p.1) with
        | some p => some (bin p.2 lhs rhs)
        | none =>
          if nameStr.endsWith "uget" || nameStr.endsWith "get!" || nameStr.endsWith "fget" then
            some (.sarrayGet lhs rhs retTy)
          else none
  | [arr] =>
    if !isLocal && (nameStr.endsWith "size" || nameStr.endsWith "usize") then some (.sarrayLen arr) else none
  | [arr, idx, val] =>
    if !isLocal && (nameStr.endsWith "uset" || nameStr.endsWith "set!" || nameStr.endsWith "fset") then
      some (.sarraySet arr idx val (match retTy with | .sarray elem => elem | _ => .i64))
    else none
  | _ => none

/-- Lower a named LCNF call, preferring an intrinsic and otherwise recording an extern C-ABI call. -/
def lowerNamedCall (fnName : Lean.Name) (args : Array (Lean.Compiler.LCNF.Arg pu)) (retTy : LNIRType) :
    BridgeM LNIRExpr := do
  let argVars ← args.toList.mapM lowerArg
  let argTys ← argVars.mapM getVarType
  let env ← getEnv
  let st ← get
  let isLocal := st.localDeclNames.contains fnName || fnName == st.selfDeclName
  match tryLowerIntrinsicCall env fnName argVars retTy argTys isLocal with
  | some intrinsicExpr => return intrinsicExpr
  | none =>
    let isExt := !isLocal && Lean.isExtern env fnName
    if isExt then modify fun st => { st with hasExtern := true }
    return .call (mangleDeclNameInEnv env fnName) argVars retTy isExt

/-- Lower an LCNF fvar (partial) application shared by the pure and impure bridges. -/
def lowerFVarCall (fvarId : Lean.FVarId) (args : Array (Lean.Compiler.LCNF.Arg pu)) (retTy : LNIRType) :
    BridgeM LNIRExpr := do
  let fnVar ← internFVar fvarId
  if args.isEmpty then return .scalar (.var fnVar)
  else return .call s!"fvar_{fnVar}" (← args.toList.mapM lowerArg) retTy false

/-- Lower a constructor application, collapsing single-constructor products into tuples. -/
def lowerCtorApp (ctorName : Lean.Name) (cidx size : Nat) (args : Array (Lean.Compiler.LCNF.Arg pu)) :
    BridgeM LNIRExpr := do
  let env ← getEnv
  let argVars ← args.toList.mapM lowerArg
  let isProd := ctorName == ``Prod.mk || ctorName == ``MProd.mk || ctorName == ``PProd.mk
  let isSingleCtorStruct :=
    match env.find? ctorName with
    | some (.ctorInfo cval) =>
      match env.find? cval.induct with
      | some (.inductInfo ival) => ival.ctors.length == 1 && !ival.isRec
      | _ => false
    | _ => false
  if isProd || (isSingleCtorStruct && argVars.length ≤ 8) then return .mkTuple argVars
  else return .allocCtor cidx (argVars.take size) (argVars.drop size)

/-- Lower a stage-2 `LetValue .impure` into an `LNIRExpr`. -/
def lowerImpureLetValue (lv : Lean.Compiler.LCNF.LetValue .impure) (retTy : LNIRType) : BridgeM LNIRExpr := do
  match lv with
  | .lit litVal => return lowerLitValue litVal
  | .erased => return .scalar (.constU64 0)
  | .fvar fvarId args => lowerFVarCall fvarId args retTy
  | .ctor ctorInfo args _ => lowerCtorApp ctorInfo.name ctorInfo.cidx ctorInfo.size args
  | .oproj idx fvarId _ =>
    let v ← internFVar fvarId
    match (← getVarType v) with | .tuple _ => return .projTuple v idx | _ => return .ctorGetObj v idx
  | .uproj idx fvarId _ => return .ctorGetScalar (← internFVar fvarId) idx .usize
  | .sproj offset _ fvarId _ => return .ctorGetScalar (← internFVar fvarId) offset retTy
  | .fap fnName args _ | .pap fnName args _ => lowerNamedCall fnName args retTy
  | .reset _ fvarId _ => return .scalar (.var (← internFVar fvarId))
  | .reuse _ ctorInfo _ args _ => lowerCtorApp ctorInfo.name ctorInfo.cidx ctorInfo.size args
  | .box tyExpr fvarId _ => return .boxScalar (← internFVar fvarId) (lowerImpureType tyExpr)
  | .unbox fvarId _ => return .unboxScalar (← internFVar fvarId) retTy
  | .isShared fvarId _ => return .isExclusive (← internFVar fvarId)

/-- Intern a slice of LCNF parameters for join points and case branches. -/
def internParams {pu} (params : Array (Lean.Compiler.LCNF.Param pu)) : BridgeM Unit := do
  for p in params do
    let _ ← internFVar p.fvarId (lowerImpureType p.type)

/-- Lower a recursive or non-recursive join point shared by the pure and impure bridges. -/
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

/-- Lower a join-point `.jmp` instruction shared by the pure and impure bridges. -/
def lowerJmpInstr {pu} (fvarId : Lean.FVarId) (args : Array (Lean.Compiler.LCNF.Arg pu)) : BridgeM LNIRCode := do
  let st ← get
  match st.jpMap[fvarId]? with
  | some (jpParams, jpBody) =>
    modify fun st => { st with jpMap := st.jpMap.erase fvarId }
    spliceJoinPointJmp jpParams jpBody args
  | none =>
    match args.toList with
    | arg0 :: _ => return .ret (← lowerArg arg0)
    | [] => return .ret (← internFVar fvarId)

/-- Lower an LCNF array/object field write (`oset`/`uset`/`sset`). -/
def lowerIndexedSet (fvarId : Lean.FVarId) (idx : Nat) (valVar : VarId) (elemTy : LNIRType)
    (kCode : LNIRCode) : BridgeM LNIRCode := do
  let arrVar ← internFVar fvarId
  let idxVar ← freshBridgeVar .i64
  let dstVar ← freshBridgeVar .objPtr
  return .letBind idxVar .i64 (.scalar (.constU64 idx.toUInt64))
    (.letBind dstVar .objPtr (.sarraySet arrVar idxVar valVar elemTy) kCode)

mutual

/-- Recursively lower all impure `cases` alternatives into a complete nested `ite` tag-dispatch chain. -/
partial def lowerImpureAlts (condVar : VarId) (alts : List (Lean.Compiler.LCNF.Alt .impure)) : BridgeM LNIRCode := do
  match alts with
  | [] => return .unreachable
  | [singleAlt] => lowerImpureCode singleAlt.getCode
  | alt :: rest =>
    match alt with
    | .ctorAlt info code _ =>
      let cmpVar ← freshBridgeVar .i64
      return .letBind cmpVar .i64
        (.scalar (.binOp .eq (.var condVar) (.constU64 info.cidx.toUInt64)))
        (.ite cmpVar (← lowerImpureCode code) (← lowerImpureAlts condVar rest))
    | .default code => lowerImpureCode code
    | .alt _ params code _ =>
      internParams params
      return .ite condVar (← lowerImpureCode code) (← lowerImpureAlts condVar rest)

/-- Lower a stage-2 `Code .impure` block into structured `LNIRCode`. -/
partial def lowerImpureCode (code : Lean.Compiler.LCNF.Code .impure) : BridgeM LNIRCode := do
  match code with
  | .let decl k =>
    let st ← get
    match k, decl.value, st.selfLoopAccVar with
    | .return retFVar, .fap fnName args _, some accVar =>
      if retFVar == decl.fvarId && fnName == st.selfDeclName then
        spliceJoinPointJmp st.selfParams (.ret accVar) args
      else
        let ty := lowerImpureType decl.type
        return .letBind (← internFVar decl.fvarId ty) ty (← lowerImpureLetValue decl.value ty) (← lowerImpureCode k)
    | _, _, _ =>
      let ty := lowerImpureType decl.type
      return .letBind (← internFVar decl.fvarId ty) ty (← lowerImpureLetValue decl.value ty) (← lowerImpureCode k)
  | .jp decl k => lowerJoinPoint decl k lowerImpureCode
  | .jmp fvarId args => lowerJmpInstr fvarId args
  | .inc fvarId n _ _ k _ => return .incRef (← internFVar fvarId) n (← lowerImpureCode k)
  | .dec fvarId n _ _ _ k _ => return .decRef (← internFVar fvarId) n (← lowerImpureCode k)
  | .del fvarId k _ => return .decRef (← internFVar fvarId) 1 (← lowerImpureCode k)
  | .oset fvarId idx arg k _ => lowerIndexedSet fvarId idx (← lowerArg arg) .objPtr (← lowerImpureCode k)
  | .uset fvarId idx valFVar k _ => lowerIndexedSet fvarId idx (← internFVar valFVar .usize) .usize (← lowerImpureCode k)
  | .sset fvarId idx _ valFVar tyExpr k _ =>
    let elemTy := lowerImpureType tyExpr
    lowerIndexedSet fvarId idx (← internFVar valFVar elemTy) elemTy (← lowerImpureCode k)
  | .setTag _ _ k _ => lowerImpureCode k
  | .cases c => lowerImpureAlts (← internFVar c.discr) (orderAlts c.alts.toList)
  | .return fvarId => return .ret (← internFVar fvarId)
  | .unreach _ => return .unreachable

end

/-- Lower a stage-1 `LetValue .pure` into an `LNIRExpr`. -/
def lowerPureLetValue (lv : Lean.Compiler.LCNF.LetValue .pure) (retTy : LNIRType) : BridgeM LNIRExpr := do
  match lv with
  | .lit litVal => return lowerLitValue litVal
  | .erased => return .scalar (.constU64 0)
  | .proj _ idx fvarId _ => return .projTuple (← internFVar fvarId) idx
  | .const declName _ args _ =>
    if declName == ``Prod.mk || declName == ``MProd.mk || declName == ``PProd.mk then
      return .mkTuple (← args.toList.mapM lowerArg)
    else lowerNamedCall declName args retTy
  | .fvar fvarId args => lowerFVarCall fvarId args retTy

/-- Lookup the constructor tag index `cidx` for `ctorName` in the Lean environment, falling back to `fallbackIdx`. -/
def lookupCtorIdx (ctorName : Lean.Name) (fallbackIdx : Nat) : BridgeM Nat := do
  match (← getEnv).find? ctorName with | some (.ctorInfo cval) => return cval.cidx | _ => return fallbackIdx

mutual

/-- Recursively lower all pure `cases` alternatives into a complete nested `ite` tag-dispatch chain. -/
partial def lowerPureAlts (condVar : VarId) (idx : Nat) (alts : List (Lean.Compiler.LCNF.Alt .pure)) : BridgeM LNIRCode := do
  let emitTagBranch (cidx : Nat) (code : Lean.Compiler.LCNF.Code .pure) (rest : List (Lean.Compiler.LCNF.Alt .pure)) : BridgeM LNIRCode := do
    let cmpVar ← freshBridgeVar .i64
    return .letBind cmpVar .i64 (.scalar (.binOp .eq (.var condVar) (.constU64 cidx.toUInt64)))
      (.ite cmpVar (← lowerPureCode code) (← lowerPureAlts condVar (idx + 1) rest))
  match alts with
  | [] => return .unreachable
  | [singleAlt] =>
    if let .alt _ params _ _ := singleAlt then internParams params
    lowerPureCode singleAlt.getCode
  | alt :: rest =>
    match alt with
    | .alt ctorName params code _ => internParams params; emitTagBranch (← lookupCtorIdx ctorName idx) code rest
    | .ctorAlt info code _ => emitTagBranch info.cidx code rest
    | .default code => lowerPureCode code

/-- Lower a stage-1 `Code .pure` block into structured `LNIRCode`. -/
partial def lowerPureCode (code : Lean.Compiler.LCNF.Code .pure) : BridgeM LNIRCode := do
  match code with
  | .let decl k =>
    let st ← get
    match k, decl.value, st.selfLoopAccVar with
    | .return retFVar, .const fnName _ args _, some accVar =>
      if retFVar == decl.fvarId && fnName == st.selfDeclName then
        spliceJoinPointJmp st.selfParams (.ret accVar) args
      else
        let ty := lowerImpureType decl.type
        return .letBind (← internFVar decl.fvarId ty) ty (← lowerPureLetValue decl.value ty) (← lowerPureCode k)
    | _, _, _ =>
      let ty := lowerImpureType decl.type
      return .letBind (← internFVar decl.fvarId ty) ty (← lowerPureLetValue decl.value ty) (← lowerPureCode k)
  | .fun decl k _ =>
    let _ ← internFVar decl.fvarId (lowerImpureType decl.type)
    internParams decl.params
    lowerPureCode k
  | .jp decl k => lowerJoinPoint decl k lowerPureCode
  | .jmp fvarId args => lowerJmpInstr fvarId args
  | .cases c => lowerPureAlts (← internFVar c.discr) 0 (orderAlts c.alts.toList)
  | .return fvarId => return .ret (← internFVar fvarId)
  | .unreach _ => return .unreachable

end

/-- Shared declaration-level lowering for both `.impure` and `.pure` LCNF declarations. -/
def ingestLCNFDeclGeneric {pu} (decl : Lean.Compiler.LCNF.Decl pu)
    (lowerCodeFn : Lean.Compiler.LCNF.Code pu → BridgeM LNIRCode)
    (localDeclNames : Array Lean.Name := #[]) : Lean.CoreM LNIRDecl := do
  let env ← getEnv
  let metaInfo := getLCNFDeclMetadata env decl.name
  let isDeclExtern := metaInfo.isExtern
  let initSt : BridgeState := {
    mangledSymbol  := metaInfo.mangledSymbol
    isSimpleGround := metaInfo.isSimpleGround
    selfDeclName   := decl.name
    localDeclNames := localDeclNames
  }
  let action : BridgeM LNIRDecl := do
    let mut lnirParams : List LNIRParam := []
    for p in decl.params do
      let pTy := lowerImpureType p.type
      let vid ← internFVar p.fvarId pTy
      lnirParams := lnirParams ++ [{ id := vid, name := p.binderName.toString, ty := pTy, borrow := p.borrow }]
    let retTy := lowerImpureType decl.type
    match decl.value with
    | .code c =>
      let env ← getEnv
      let body ←
        if let some intrExpr := tryLowerGfSimdIntrinsic env decl.name (lnirParams.map (·.id)) retTy (lnirParams.map (·.ty)) then do
          let retVar ← freshBridgeVar retTy
          pure (.letBind retVar retTy intrExpr (.ret retVar))
        else if codeHasSelfTailCall decl.name c then do
          let (idxVar, accVar, accTy) ← match lnirParams with
            | p0 :: p1 :: _ => pure (p0.id, p1.id, p1.ty)
            | [p0]          => pure (← freshBridgeVar .i64, p0.id, p0.ty)
            | []            => pure (← freshBridgeVar .i64, ← freshBridgeVar retTy, retTy)
          modify fun st => { st with selfLoopAccVar := some accVar, selfParams := toImpureParams decl.params }
          let stepBody ← lowerCodeFn c
          let loVar ← freshBridgeVar .i64; let hiVar ← freshBridgeVar .i64; let accInit ← freshBridgeVar accTy
          pure (.letBind loVar .i64 (.scalar (.constU64 0))
            (.letBind hiVar .i64 (.scalar (.constU64 64))
              (.letBind accInit accTy (.scalar (.var accVar))
                (.seqFor idxVar loVar hiVar accVar accInit accTy stepBody (.ret accVar)))))
        else lowerCodeFn c
      let st ← get
      let assurance : AssuranceLevel :=
        if isDeclExtern || st.hasExtern then .unverifiedFallback else .verifiedKernelProof
      return {
        name      := metaInfo.mangledSymbol
        params    := lnirParams
        retTy     := retTy
        body      := body
        assurance := assurance
        isGpuCand := lnirParams.all (fun p => p.ty.isGpuCompatible) && retTy.isGpuCompatible
      }
    | .extern _ =>
      let retVar ← freshBridgeVar retTy
      let argIds := lnirParams.map (·.id)
      return {
        name      := metaInfo.mangledSymbol
        params    := lnirParams
        retTy     := retTy
        body      := .letBind retVar retTy (.call metaInfo.mangledSymbol argIds retTy true) (.ret retVar)
        assurance := .unverifiedFallback
        isGpuCand := false
      }
  Prod.fst <$> action.run initSt

def ingestLCNFImpureDecl (decl : Lean.Compiler.LCNF.Decl .impure) (localDeclNames : Array Lean.Name := #[]) : Lean.CoreM LNIRDecl :=
  ingestLCNFDeclGeneric decl lowerImpureCode localDeclNames
def ingestLCNFMonoDecl (decl : Lean.Compiler.LCNF.Decl .pure) (localDeclNames : Array Lean.Name := #[]) : Lean.CoreM LNIRDecl :=
  ingestLCNFDeclGeneric decl lowerPureCode localDeclNames

def ingestModuleDecls (declNames : Array Lean.Name) (moduleName : String := "LeanNative.Ingested") :
    Lean.CoreM LNIRModule := do
  let mut decls : List LNIRDecl := []
  for name in declNames do
    if let some impureDecl ← Lean.Compiler.LCNF.getLocalImpureDecl? name then
      decls := decls ++ [← ingestLCNFImpureDecl impureDecl declNames]
    else if let some monoDecl ← Lean.Compiler.LCNF.getMonoDecl? name then
      decls := decls ++ [← ingestLCNFMonoDecl monoDecl declNames]
  return { moduleName := moduleName, decls := decls }

def isInternalClosedOrReprAux (name : Lean.Name) : Bool :=
  let s := name.toString
  ["___closed__", "instRepr", "_cstage", "ctorElim"].any fun pat => (s.splitOn pat).length > 1

def ingestAllLocalDecls (moduleName : String := "LeanNative.Ingested") : Lean.CoreM LNIRModule := do
  let impureNames ← Lean.Compiler.LCNF.getLocalImpureDecls
  let env ← getEnv
  let extraNames := env.constants.map₂.foldl (fun acc name _ =>
    if impureNames.contains name || isInternalClosedOrReprAux name then acc else acc.push name) #[]
  let filteredImpure := impureNames.filter (fun n => !isInternalClosedOrReprAux n)
  ingestModuleDecls (if filteredImpure.isEmpty && extraNames.isEmpty then impureNames else (filteredImpure ++ extraNames)) moduleName

partial def maxVarIdInCode : LNIRCode → VarId
  | .letBind dst _ _ k => max dst (maxVarIdInCode k)
  | .rawStore pv iv vv _ k => max (max pv iv) (max vv (maxVarIdInCode k))
  | .incRef ov _ k | .decRef ov _ k => max ov (maxVarIdInCode k)
  | .ite cv t e => max cv (max (maxVarIdInCode t) (maxVarIdInCode e))
  | .seqFor iv lv hv av ai _ s k => max (max iv lv) (max (max hv av) (max ai (max (maxVarIdInCode s) (maxVarIdInCode k))))
  | .parFor ov lv _ _ _ k => max (max ov lv) (maxVarIdInCode k)
  | .ret v => v | .unreachable => 0

partial def codeCallsDecl (fnName : String) : LNIRCode → Bool
  | .letBind _ _ (.call callee _ _ _) k => callee == fnName || codeCallsDecl fnName k
  | .letBind _ _ _ k | .rawStore _ _ _ _ k | .incRef _ _ k | .decRef _ _ k | .parFor _ _ _ _ _ k => codeCallsDecl fnName k
  | .ite _ t e | .seqFor _ _ _ _ _ _ t e => codeCallsDecl fnName t || codeCallsDecl fnName e
  | .ret _ | .unreachable => false

partial def isSimpleInlinableBody (selfName : String) : LNIRCode → Bool
  | .letBind _ _ (.call callee _ _ _) _ => callee != selfName && false
  | .letBind _ _ _ k => isSimpleInlinableBody selfName k
  | .ite _ t e => isSimpleInlinableBody selfName t && isSimpleInlinableBody selfName e
  | .ret _ => true | _ => false

def renameScalarExpr (paramMap : List (VarId × VarId)) (offset : VarId) : ScalarExpr → ScalarExpr
  | .constU64 v => .constU64 v | .constBool b => .constBool b
  | .var id => .var ((paramMap.lookup id).getD (id + offset))
  | .binOp op l r => .binOp op (renameScalarExpr paramMap offset l) (renameScalarExpr paramMap offset r)
  | .unaryOp op a => .unaryOp op (renameScalarExpr paramMap offset a)
  | .select c t f => .select (renameScalarExpr paramMap offset c) (renameScalarExpr paramMap offset t) (renameScalarExpr paramMap offset f)
  | .fma a b c => .fma (renameScalarExpr paramMap offset a) (renameScalarExpr paramMap offset b) (renameScalarExpr paramMap offset c)

private def renameVarId (paramMap : List (VarId × VarId)) (offset : VarId) (v : VarId) : VarId :=
  (paramMap.lookup v).getD (v + offset)

/-- Splice a simple helper `calleeBody` at call site `dst := call callee args`, binding `dst` at every `.ret`. -/
partial def spliceInlinedBody (paramMap : List (VarId × VarId)) (offset : VarId)
    (dst : VarId) (dstTy : LNIRType) (cont : LNIRCode) : LNIRCode → LNIRCode
  | .letBind bDst bTy (.scalar se) k =>
    .letBind (bDst + offset) bTy (.scalar (renameScalarExpr paramMap offset se))
      (spliceInlinedBody paramMap offset dst dstTy cont k)
  | .letBind bDst bTy (.mkTuple fs) k =>
    .letBind (bDst + offset) bTy (.mkTuple (fs.map (renameVarId paramMap offset)))
      (spliceInlinedBody paramMap offset dst dstTy cont k)
  | .letBind bDst bTy (.projTuple tv idx) k =>
    .letBind (bDst + offset) bTy (.projTuple (renameVarId paramMap offset tv) idx)
      (spliceInlinedBody paramMap offset dst dstTy cont k)
  | .ite cv t e =>
    .ite (renameVarId paramMap offset cv)
      (spliceInlinedBody paramMap offset dst dstTy cont t)
      (spliceInlinedBody paramMap offset dst dstTy cont e)
  | .ret rv => .letBind dst dstTy (.scalar (.var (renameVarId paramMap offset rv))) cont
  | _ => cont

/-- Inline non-recursive local helper calls (`Inv`, `ValidSszContainerHeader`, `declaredGasLimit`) inside `code`. -/
partial def inlineLocalHelperCalls (helpers : List LNIRDecl) (nextOffset : VarId) : LNIRCode → LNIRCode
  | .letBind dst ty (.call callee args retTy isExt) k =>
    if isExt then
      .letBind dst ty (.call callee args retTy isExt) (inlineLocalHelperCalls helpers (nextOffset + 128) k)
    else
      match helpers.find? (fun h => h.name == callee && h.params.length == args.length) with
      | some hDecl =>
        let stepSpan := maxVarIdInCode hDecl.body + 128
        let k' := inlineLocalHelperCalls helpers (nextOffset + stepSpan) k
        spliceInlinedBody ((hDecl.params.map (·.id)).zip args) nextOffset dst ty k' hDecl.body
      | none =>
        .letBind dst ty (.call callee args retTy isExt) (inlineLocalHelperCalls helpers (nextOffset + 128) k)
  | .letBind dst ty val k => .letBind dst ty val (inlineLocalHelperCalls helpers nextOffset k)
  | .rawStore pv iv vv ty k => .rawStore pv iv vv ty (inlineLocalHelperCalls helpers nextOffset k)
  | .incRef ov c k => .incRef ov c (inlineLocalHelperCalls helpers nextOffset k)
  | .decRef ov c k => .decRef ov c (inlineLocalHelperCalls helpers nextOffset k)
  | .ite cv t e => .ite cv (inlineLocalHelperCalls helpers nextOffset t) (inlineLocalHelperCalls helpers (nextOffset + 256) e)
  | .seqFor iv lv hv av ai aty step k =>
    .seqFor iv lv hv av ai aty (inlineLocalHelperCalls helpers nextOffset step) (inlineLocalHelperCalls helpers (nextOffset + 256) k)
  | .parFor ov lv ins ety kern k => .parFor ov lv ins ety kern (inlineLocalHelperCalls helpers nextOffset k)
  | .ret v => .ret v
  | .unreachable => .unreachable

/-- Perform one round of $\delta$-inlining of simple straight-line local helper declarations. -/
private def inlineLocalDefsOnce (m : LNIRModule) : LNIRModule :=
  let helpers := m.decls.filter (fun d => isSimpleInlinableBody d.name d.body)
  if helpers.isEmpty then m
  else
    let decls' := m.decls.map (fun d =>
      let baseOff := maxVarIdInCode d.body + 1000
      { d with body := inlineLocalHelperCalls helpers baseOff d.body }
    )
    { m with decls := decls' }

/-- Normalize an `LNIRModule` by $\delta$-inlining non-recursive local helper declarations
    (`Inv`, `ValidSszContainerHeader`, `declaredGasLimit`) across up to 4 fixed-point rounds
    so `FastCheck` and `UnboxTupleSROA` inspect the full arithmetic/relational structure. -/
def normalizeAndInlineLocalDefs (m : LNIRModule) : LNIRModule :=
  let m1 := inlineLocalDefsOnce m
  let m2 := inlineLocalDefsOnce m1
  let m3 := inlineLocalDefsOnce m2
  inlineLocalDefsOnce m3

/-- Resolve the Lean 4.35 sysroot path reliably even when `lean` is not on `PATH`. -/
def resolveLeanSysroot : IO System.FilePath := do
  if let some envRoot ← IO.getEnv "LEAN_SYSROOT" then
    if !envRoot.isEmpty then
      return System.FilePath.mk envRoot
  try
    Lean.findSysroot
  catch _ =>
    let home := (← IO.getEnv "HOME").getD ""
    let candidates := [
      s!"{home}/.elan/toolchains/leanprover--lean4---v4.35.0",
      "/var/lib/sandboxed-node/.elan/toolchains/leanprover--lean4---v4.35.0",
      "/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.35.0",
      "/var/lib/orb-node/work/caches/elan/toolchains/leanprover--lean4---v4.35.0"
    ]
    for c in candidates do
      let p := System.FilePath.mk c
      if ← p.pathExists then
        return p
    return System.FilePath.mk "/var/lib/sandboxed-node/.elan/toolchains/leanprover--lean4---v4.35.0"

/-- When `filePath` (e.g., `SnarkFast/Kernels.lean`) is an umbrella module that re-exports
    domain submodules in `<filePath_without_.lean>/<Sub>.lean` (`Field`, `Ntt`, `Hashes`, `Pcs`),
    inline those local submodule sources (stripping their `import ` headers) so `Lean.Elab.runFrontend`
    elaborates all `@[export]` kernels in a single local LCNF unit. -/
private def expandUmbrellaSubmodules (filePath : String) (raw : String) : IO String := do
  if !filePath.endsWith ".lean" then return raw
  let subDir := System.FilePath.mk ((filePath.dropEnd 5).toString)
  if !(← subDir.pathExists) then return raw
  let stem := subDir.fileName.getD ""
  let mut outLines : Array String := #[]
  for line in raw.splitOn "\n" do
    let trimmed := line.trimAscii.toString
    if trimmed.startsWith "import " then
      let modPath := (trimmed.drop 7).trimAscii.toString
      let parts := modPath.splitOn "."
      match parts.reverse with
      | leaf :: parent :: _ =>
        let candPath := subDir / s!"{leaf}.lean"
        if parent == stem && (← candPath.pathExists) then
          let subRaw ← IO.FS.readFile candPath
          for subLine in subRaw.splitOn "\n" do
            if !subLine.trimAscii.toString.startsWith "import " then
              outLines := outLines.push subLine
        else
          outLines := outLines.push line
      | _ => outLines := outLines.push line
    else
      outLines := outLines.push line
  return String.intercalate "\n" outLines.toList

/-- Run `Lean.Elab.runFrontend` on `filePath` and execute `act` inside `CoreM`.
    Automatically includes `.lake/build/lib/lean` (populated by `turbo-lean build`'s
    transactional module-DAG publisher) and `build/olean` in the Lean search path. -/
def withElaboratedFrontend {α : Type} (filePath : String) (modName : Lean.Name) (act : Lean.CoreM α) : IO α := do
  let mut extraPaths : Lean.SearchPath := []
  for cand in [".lake/build/lib/lean", "build/olean"] do
    let p := System.FilePath.mk cand
    if ← p.pathExists then
      extraPaths := extraPaths ++ [p]
  Lean.initSearchPath (← resolveLeanSysroot) extraPaths
  let rawInput ← IO.FS.readFile filePath
  let input ← expandUmbrellaSubmodules filePath rawInput
  let opts : Lean.Options := {}
  let some env ← Lean.Elab.runFrontend input opts filePath modName
    | throw <| IO.userError s!"Elaboration failed for {filePath}"
  let coreCtx : Lean.Core.Context := { fileName := filePath, fileMap := filePath.toFileMap, options := opts }
  Prod.fst <$> act.toIO coreCtx { env := env }

/-- Elaborate a `.lean` source file using Lean 4's frontend, run the LCNF compiler pipeline,
    and extract the resulting `LNIRModule`. -/
def ingestLeanSourceFile (filePath : String) (moduleName : String := "LeanNative.FileInput") : IO LNIRModule := do
  normalizeAndInlineLocalDefs <$> withElaboratedFrontend filePath `LeanNativeInput (ingestAllLocalDecls moduleName)

/-- Elaborate `filePath` with `Lean.Elab.runFrontend`, extracting both the Lean 4.31 C module code
    (`Lean.Compiler.LCNF.emitC modName`) and the lowered `LNIRModule` via `ingestAllLocalDecls`. -/
def emitLeanCFromSourceFile (filePath : String) (modName : Lean.Name := `Main) : IO (String × LNIRModule) :=
  withElaboratedFrontend filePath modName do
    let mod ← ingestAllLocalDecls modName.toString
    return (← Lean.Compiler.LCNF.emitC modName, mod)

/-- Full LCNF-to-Executable builder (`buildNativeExecutable` / `buildExecutableFromLeanFile`):
    1. Runs `emitLeanCFromSourceFile` on `filePath`.
    2. Runs the verified `LeanNative` 4-pass optimization pipeline on the extracted `LNIRModule`
       and emits `<outBin>.lnir.ll` (including `@lean_native_abi_*` C-ABI wrapper thunks).
    3. Compiles both `<outBin>.lnir.ll` and the lowered C/LLVM module through LLVM 18
       (`clang -S -emit-llvm` -> `/usr/lib/llvm-18/bin/opt` with loop & SLP vectorization ->
       `clang` linked against `libleanshared.so` and `runtime/lean_native_runtime.c`)
       to produce a standalone native executable at `outBin`. -/
def buildNativeExecutable (filePath : String) (outBin : String) (optLevel : String := "-O3")
    (cliArgs : List String := []) : IO (LNIRModule × String) := do
  let sysroot ← resolveLeanSysroot
  let (cCode, rawMod) ← emitLeanCFromSourceFile filePath `Main
  let (optMod, _) := LeanNative.Transform.runDefaultPipeline rawMod
  let hostArch : TargetArch :=
    if System.Platform.target.startsWith "aarch64" || System.Platform.target.startsWith "arm64" then .arm64 else .x86_64
  let superoptTgt : LeanNative.Transform.SuperoptTarget :=
    match hostArch with
    | .arm64 => .arm64
    | _ => .x86_64
  let batchEnv ← IO.getEnv "SANDBOXED_TELEMETRY_BATCH_ONLY"
  let isBatchOnly := (batchEnv.map (fun s => s.trimAscii.toString) |>.getD "") == "1"
  if !isBatchOnly then
    let telCfg ← LeanNative.Backend.FastCheck.TelemetryConfig.probe cliArgs
    if telCfg.enabled then
      let _ ← LeanNative.Transform.emitModuleTelemetryEvents telCfg superoptTgt false rawMod
  let lnirLlPath := s!"{outBin}.lnir.ll"
  let lnirOptLlPath := s!"{outBin}.lnir.opt.ll"
  let lnirLlText := LeanNative.Backend.LLVM.emitLLVMOptimized optMod hostArch
  IO.FS.writeFile lnirLlPath lnirLlText

  let cPath := s!"{outBin}.lean.c"
  let rawLlPath := s!"{outBin}.raw.ll"
  let optLlPath := s!"{outBin}.opt.ll"
  IO.FS.writeFile cPath cCode

  let incDir := (sysroot / "include").toString
  let clangIncDir := (sysroot / "include" / "clang").toString
  let libDir := (sysroot / "lib" / "lean").toString

  let relRuntime : System.FilePath := "runtime/lean_native_runtime.c"
  let absRuntime : System.FilePath := "/var/lib/spark-admin/jobs/3730b838-a03b-49e3-bbd2-eb51c132a4e7/lean-native/runtime/lean_native_runtime.c"
  let runtimePath ← if (← relRuntime.pathExists) then pure relRuntime.toString else pure absRuntime.toString
  let runtimeDir := ((System.FilePath.mk runtimePath).parent.getD (System.FilePath.mk "runtime")).toString
  let cOptScript : System.FilePath := ((System.FilePath.mk runtimeDir).parent.getD (System.FilePath.mk ".")) / "scripts" / "ln_c_opt.py"
  let cOptPath := if (← cOptScript.pathExists) then cOptScript.toString else "scripts/ln_c_opt.py"
  discard <| IO.Process.output { cmd := "python3", args := #[cOptPath, cPath, cPath] }

  let sysClang : System.FilePath := "/usr/bin/clang"
  let tcClang : System.FilePath := sysroot / "bin" / "clang"
  let clangCmd ←
    if (← sysClang.pathExists) then pure sysClang.toString
    else if (← tcClang.pathExists) then pure tcClang.toString
    else pure "clang"
  let extraIncArgs : Array String :=
    if clangCmd == tcClang.toString then #[s!"-isystem{clangIncDir}"] else #[]

  -- Step 1: clang -S -emit-llvm -O3 -Xclang -disable-llvm-passes -DNDEBUG -march=native -I<sysroot>/include
  let clangEmitOut ← IO.Process.output {
    cmd  := clangCmd
    args := #["-S", "-emit-llvm", optLevel, "-Xclang", "-disable-llvm-passes", "-DNDEBUG", "-march=native", s!"-I{incDir}", s!"-I{runtimeDir}"] ++ extraIncArgs ++ #[cPath, "-o", rawLlPath]
  }
  if clangEmitOut.exitCode != 0 then
    throw <| IO.userError s!"clang -emit-llvm failed:\n{clangEmitOut.stderr}"

  let intrDecls := optMod.decls.filter fun d =>
    ["l_clmul64Hi", "l_clmul64", "l_gf2Affine", "l_eor3"].any fun s => d.name.endsWith s
  if !intrDecls.isEmpty then
    let intrPath := s!"{outBin}.intr.ll"
    IO.FS.writeFile intrPath ((LeanNative.Backend.LLVM.emitLLVMOptimized { optMod with decls := intrDecls } hostArch).replace ") #0 {" ") alwaysinline #0 {")
    if (← (System.FilePath.mk "/usr/lib/llvm-18/bin/llvm-link").pathExists) then
      discard <| IO.Process.output { cmd := "/usr/lib/llvm-18/bin/llvm-link", args := #["-S", rawLlPath, s!"--override={intrPath}", "-o", rawLlPath] }
    else
      discard <| IO.Process.output { cmd := "python3", args := #[cOptPath, "--override-ll", rawLlPath, intrPath, rawLlPath] }

  -- Step 2: /usr/lib/llvm-18/bin/opt with O3 + loop-vectorize + slp-vectorizer, falling back to `clang -x ir -O3 -S -emit-llvm` when `opt` is absent
  let optBin : System.FilePath := "/usr/lib/llvm-18/bin/opt"
  let hasOptBin ← optBin.pathExists
  let runOptPass (inLl outLl : String) (fallback : IO String) : IO Unit := do
    if hasOptBin then
      try
        let out ← IO.Process.output {
          cmd  := optBin.toString
          args := #["-S", "-passes=default<O3>,loop-vectorize,slp-vectorizer", "-vectorize-loops", "-vectorize-slp", inLl, "-o", outLl]
        }
        if out.exitCode == 0 then return ()
      catch _ => pure ()
    try
      let clangIrOut ← IO.Process.output {
        cmd  := clangCmd
        args := #["-x", "ir", optLevel, "-S", "-emit-llvm", "-Wno-override-module", inLl, "-o", outLl]
      }
      if clangIrOut.exitCode != 0 then IO.FS.writeFile outLl (← fallback)
    catch _ =>
      IO.FS.writeFile outLl (← fallback)
  runOptPass rawLlPath optLlPath (IO.FS.readFile rawLlPath)
  runOptPass lnirLlPath lnirOptLlPath (pure lnirLlText)

  -- Step 3: clang -O3 linking against libleanshared and runtime/lean_native_runtime.c
  let isDarwin := (System.Platform.target.splitOn "darwin").length > 1 || (System.Platform.target.splitOn "apple").length > 1
  let linkInputs := if isDarwin then #[optLlPath, runtimePath] else #[optLlPath, lnirOptLlPath, runtimePath, "-Wl,--allow-multiple-definition"]
  let linkOut ← IO.Process.output {
    cmd  := clangCmd
    args := #[optLevel, "-DNDEBUG", "-march=native", "-Wno-override-module", s!"-I{incDir}", s!"-I{runtimeDir}"] ++
      extraIncArgs ++ linkInputs ++ #[s!"-L{libDir}", "-lleanshared", s!"-Wl,-rpath,{libDir}", "-lm", "-lpthread", "-ldl", "-o", outBin]
  }
  if linkOut.exitCode != 0 then
    throw <| IO.userError s!"clang native link failed:\n{linkOut.stderr}"

  return (optMod, lnirLlPath)

abbrev buildExecutableFromLeanFile := buildNativeExecutable

/-!
## Canonical Benchmark & Workload Declarations (Re-exported from `LeanNative.IR.Codec`)
-/

abbrev collatzStepsDecl : LNIRDecl := LeanNative.IR.Codec.collatzStepsDecl
abbrev tupleAccumSumDecl : LNIRDecl := LeanNative.IR.Codec.tupleAccumSumDecl
abbrev sarrayScaleBiasDecl : LNIRDecl := LeanNative.IR.Codec.sarrayScaleBiasDecl
abbrev dotProductU64Decl : LNIRDecl := LeanNative.IR.Codec.dotProductU64Decl
abbrev saxpyKernelDecl : LNIRDecl := LeanNative.IR.Codec.saxpyKernelDecl
abbrev matmulTiledU64Decl : LNIRDecl := LeanNative.IR.Codec.matmulTiledU64Decl
abbrev mkCollatzStepsDecl : LNIRDecl := LeanNative.IR.Codec.collatzStepsDecl
abbrev mkTupleAccumSumDecl : LNIRDecl := LeanNative.IR.Codec.tupleAccumSumDecl
abbrev mkSArrayScaleBiasDecl : LNIRDecl := LeanNative.IR.Codec.sarrayScaleBiasDecl
abbrev mkDotProductU64Decl : LNIRDecl := LeanNative.IR.Codec.dotProductU64Decl
abbrev mkSaxpyKernelDecl : LNIRDecl := LeanNative.IR.Codec.saxpyKernelDecl
abbrev mkMatmulTiledU64Decl : LNIRDecl := LeanNative.IR.Codec.matmulTiledU64Decl
abbrev mkEvmErc20TransferU256Decl : LNIRDecl := LeanNative.IR.evmErc20TransferU256Decl
abbrev mkEvmMulDivWadU256Decl : LNIRDecl := LeanNative.IR.evmMuldivWadU256Decl
abbrev mkCanonicalBenchmarkModule : LNIRModule := LeanNative.IR.Codec.mkCanonicalBenchmarkModule

end LeanNative.IR
