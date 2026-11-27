import LeanNative.IR.BridgeHelpers.TypesAndSigs

set_option autoImplicit true

namespace LeanNative.IR

open Lean
open Lean.Compiler.LCNF

/-!
L1 (`roadmap/HORIZONS.md` rung L1): the `BridgeM` lowering utilities that lived here
(`lowerArg`, `toImpureParams`, `codeHasRecursiveJmp`, `codeReferencesFVar`,
`substLNIRExprVars`, `freshenJoinPointCode`, `spliceJoinPointJmp`, `orderAlts`,
`lowerLitValueM`, `lowerLitValue`, `internParams`, `lowerRefOp`, `inferImpureRhsType`,
`lookupCtorIdx`) served only the deleted second lowering (`lowerPureCode`) and are deleted
with it. The same cleanup also deleted the compression producer's state:
the `jpMap`, `jpIndexMap`, `localFunMap`, `inJoinPointBody`, `activeCtor`, `fvarCtor`,
`hasExtern`, `mangledSymbol` and `isSimpleGround` fields were read by nothing once the
post-pass was removed. What stays: the slimmed `BridgeState`/`BridgeM` (the driver's
ingest state), the self-call and mutual-cycle detectors the driver and module ingest use,
`substScalarExprVars` (used by `Transform/EqSat`), and the trusted GF-SIMD intrinsic
recognizers.
-/

structure BridgeState where
  fvarToVar        : Std.HashMap Lean.FVarId VarId := {}
  varTypes         : Std.HashMap VarId LNIRType := {}
  nextVarId        : VarId := 0
  selfDeclName     : Lean.Name := .anonymous
  localDeclNames   : Array Lean.Name := #[]
  arch             : TargetArch := .x86_64
  allowStage1DHeap : Bool := false
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

def substScalarExprVars (subst : Std.HashMap VarId VarId) : ScalarExpr → ScalarExpr
  | .constU64 v => .constU64 v
  | .constBool b => .constBool b
  | .var id => .var (subst.getD id id)
  | .binOp op l r => .binOp op (substScalarExprVars subst l) (substScalarExprVars subst r)
  | .unaryOp op a => .unaryOp op (substScalarExprVars subst a)
  | .select c t e => .select (substScalarExprVars subst c) (substScalarExprVars subst t) (substScalarExprVars subst e)
  | .fma a b c => .fma (substScalarExprVars subst a) (substScalarExprVars subst b) (substScalarExprVars subst c)

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

end LeanNative.IR
