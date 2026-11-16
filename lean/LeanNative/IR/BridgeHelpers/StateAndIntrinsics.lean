import LeanNative.IR.BridgeHelpers.TypesAndSigs

set_option autoImplicit true

namespace LeanNative.IR

open Lean
open Lean.Compiler.LCNF

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

end LeanNative.IR
