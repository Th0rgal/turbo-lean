import LeanNative.IR.BridgeHelpers.StateAndIntrinsics

set_option autoImplicit true

namespace LeanNative.IR

open Lean
open Lean.Compiler.LCNF

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

end LeanNative.IR
