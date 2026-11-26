import LeanNative.IR.BridgeHelpers.StateAndIntrinsics

set_option autoImplicit true

namespace LeanNative.IR

open Lean
open Lean.Compiler.LCNF

/-!
L1 (`roadmap/HORIZONS.md` rung L1, w-l1): the join-point DAG machinery that lived here
(`JpDagOutcome`, `mergeJpTargets`, `collectDagOutcome`, `branchOnReach`, `mkTagJumpStub`,
`mkTagJumpFromExprs`, `reifyDagOutcome`, `substituteJpTargetInOutcome`, `bindScalarParamsBefore`,
`codeIsPureScalarDag`, `codeHasJpArityMismatch`, `lowerJoinPoint`, `lowerJmpInstr`,
`lowerLocalFunDecl`, `inlineLocalFunCode`) served only the deleted second lowering
(`lowerPureCode`) and is deleted with it. What stays is the scalar-compression candidate
producer used by the driver post-pass (`applyValidatedCompression`).
-/

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

end LeanNative.IR
