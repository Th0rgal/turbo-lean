import LeanNative.IR.BridgeHelpers.ScalarDagAndJoinPoints

set_option autoImplicit true

namespace LeanNative.IR

open Lean
open Lean.Compiler.LCNF

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

end LeanNative.IR
