import LeanNative.Proofs.SymbolicTVExprEval

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics

/-! ## Diamond Branch State Refinement & Merge (`LeanNative.Proofs.SymbolicTVMerge`) -/

def symExecItePrepare (st : SymExecState) (cExpr : SymExpr) : SymExecState × SymExecState :=
  match cExpr with
  | .unaryOp .not (.binOp .eq (.rcSym rcEp rootId) (.constU64 1))
  | .binOp .eq (.unaryOp .not (.binOp .eq (.rcSym rcEp rootId) (.constU64 1))) (.constU64 1)
  | .binOp .eq (.binOp .eq (.rcSym rcEp rootId) (.constU64 1)) (.constU64 0) =>
    if st.lookupRcExpr rootId == .rcSym rcEp rootId then (st, st.markExclusive rootId) else (st, st)
  | .binOp .eq (.rcSym rcEp rootId) (.constU64 1)
  | .binOp .eq (.unaryOp .not (.binOp .eq (.rcSym rcEp rootId) (.constU64 1))) (.constU64 0)
  | .binOp .eq (.binOp .eq (.rcSym rcEp rootId) (.constU64 1)) (.constU64 1) =>
    if st.lookupRcExpr rootId == .rcSym rcEp rootId then (st.markExclusive rootId, st) else (st, st)
  | .binOp .eq (.ctorTag tagEpoch rootId) (.constU64 tagVal) =>
    let curSv := st.lookupVar rootId
    if tagEpoch == st.heapStepEpoch then
      match curSv.expr with
      | .symVar _ =>
        -- C1.1: object slots 0..7 then scalar slots (synthetic roots 8..15), split recorded in `ctorObjCounts`
        let symFields := (List.range 16).map fun i =>
          SymExpr.symVar (SymExecState.projFieldRootId st.synVarBase st.heapStepEpoch rootId i)
        let stK : SymExecState := { st with ctorObjCounts := (rootId, 8) :: st.ctorObjCounts.filter (·.1 != rootId) }
        (stK.bindVar rootId { curSv with expr := .tuple (.constU64 tagVal :: symFields) }, st)
      | _ => (st, st)
    else (st, st)
  | _ => (st, st)

def symExecIteMerge (st : SymExecState) (condSv : SymStateVal) (cExpr : SymExpr)
    (stT : SymExecState) (retT : SymExpr) (stE : SymExecState) (retE : SymExpr) :
    SymExecState × SymExpr :=
  let mergedVars : List (VarId × SymStateVal) :=
    ((stT.vars ++ stE.vars).map Prod.fst).eraseDups.map fun vid =>
      let svT := stT.lookupVar vid
      let svE := stE.lookupVar vid
      let mExpr :=
        match svT.expr, svE.expr with
        | .tuple fsT, .tuple fsE =>
          if fsT.length == fsE.length then
            .tuple ((fsT.zip fsE).map fun (a, b) => normSymIteStep cExpr (normSymExpr a) (normSymExpr b))
          else
            normSymIteStep cExpr (normSymExpr svT.expr) (normSymExpr svE.expr)
        | _, _ => normSymIteStep cExpr (normSymExpr svT.expr) (normSymExpr svE.expr)
      (vid, {
        expr := mExpr
        nonPoison := (!stT.reachable || svT.nonPoison) && (!stE.reachable || svE.nonPoison)
        noUB := (!stT.reachable || svT.noUB) && (!stE.reachable || svE.noUB)
      })
  let mergedExcl :=
    if !stT.reachable then stE.exclusiveBufs
    else if !stE.reachable then stT.exclusiveBufs
    else stT.exclusiveBufs.filter (fun b => stE.exclusiveBufs.contains b)
  let mergedAlloc :=
    if !stT.reachable then stE.allocRoots
    else if !stE.reachable then stT.allocRoots
    else (stT.allocRoots ++ stE.allocRoots).eraseDups
  let mergedTypedTuples :=
    if !stT.reachable then stE.typedTuples
    else if !stE.reachable then stT.typedTuples
    else stT.typedTuples.filter (fun b => stE.typedTuples.contains b)
  let mergedBoolVars :=
    if !stT.reachable then stE.boolVars
    else if !stE.reachable then stT.boolVars
    else (stT.boolVars ++ stE.boolVars).eraseDups.filter fun v =>
      !(stT.u64Vars.contains v || stE.u64Vars.contains v || stT.u256Vars.contains v || stE.u256Vars.contains v)
  let mergedU64Vars :=
    if !stT.reachable then stE.u64Vars
    else if !stE.reachable then stT.u64Vars
    else (stT.u64Vars ++ stE.u64Vars).eraseDups.filter fun v =>
      !(stT.boolVars.contains v || stE.boolVars.contains v || stT.u256Vars.contains v || stE.u256Vars.contains v)
  let mergedU256Vars :=
    if !stT.reachable then stE.u256Vars
    else if !stE.reachable then stT.u256Vars
    else (stT.u256Vars ++ stE.u256Vars).eraseDups.filter fun v =>
      !(stT.boolVars.contains v || stE.boolVars.contains v || stT.u64Vars.contains v || stE.u64Vars.contains v)
  let mergedSarrayVars :=
    if !stT.reachable then stE.sarrayVars
    else if !stE.reachable then stT.sarrayVars
    else stT.sarrayVars.filter (fun v => stE.sarrayVars.contains v)
  let mergedObjPtrVars :=
    if !stT.reachable then stE.objPtrVars
    else if !stE.reachable then stT.objPtrVars
    else stT.objPtrVars.filter (fun v => stE.objPtrVars.contains v)
  let mergedRefs :=
    if !stT.reachable then stE.refCounts
    else if !stE.reachable then stT.refCounts
    else stT.refCounts.filter (fun p => stE.refCounts.lookup p.1 == some p.2)
  let mergedExtSeen :=
    if !stT.reachable then stE.extSeenRoots
    else if !stE.reachable then stT.extSeenRoots
    else (stT.extSeenRoots ++ stE.extSeenRoots).eraseDups
  let mergedRcExprs : List (VarId × SymExpr) :=
    if !stT.reachable then stE.rcExprs
    else if !stE.reachable then stT.rcExprs
    else
      let allRcRoots := ((stT.refCounts.map Prod.fst ++ stE.refCounts.map Prod.fst ++
        stT.rcExprs.map Prod.fst ++ stE.rcExprs.map Prod.fst ++ mergedExtSeen)).eraseDups
      allRcRoots.map fun r =>
        (r, normSymIteStep cExpr (stT.lookupRcExpr r) (stE.lookupRcExpr r))
  let mergedAliases :=
    if !stT.reachable then stE.bufAliases
    else if !stE.reachable then stT.bufAliases
    else stT.bufAliases.filter (fun p => stE.bufAliases.lookup p.1 == some p.2)
  let mergedExtDeltas : List (VarId × SymExpr) :=
    if !stT.reachable then stE.extRcDeltas
    else if !stE.reachable then stT.extRcDeltas
    else
      let allDeltaRoots := ((stT.extRcDeltas.map Prod.fst) ++ (stE.extRcDeltas.map Prod.fst)).eraseDups
      allDeltaRoots.filterMap fun r =>
        let m := normSymExpr (normSymIteStep cExpr (stT.lookupExtRcDeltaExpr r) (stE.lookupExtRcDeltaExpr r))
        if m == .constU64 0 then none else some (r, m)
  let mergedExtDeltaBounds : List (VarId × Nat) :=
    if !stT.reachable then stE.extRcDeltaBounds
    else if !stE.reachable then stT.extRcDeltaBounds
    else
      let allBoundRoots := ((stT.extRcDeltaBounds.map Prod.fst) ++ (stE.extRcDeltaBounds.map Prod.fst)).eraseDups
      allBoundRoots.map fun r =>
        (r, Nat.max (stT.lookupExtRcDeltaBound r) (stE.lookupExtRcDeltaBound r))
  let mergedWrites :=
    if !stT.reachable then stE.memWrites
    else if !stE.reachable then stT.memWrites
    else
      let normWrites (ws : List (MemWriteSpace × VarId × SymExpr × SymExpr)) :=
        ws.foldl (fun acc (sp, r, idx, _) =>
          if acc.any (fun (sp2, r2, i2) => sp2 == sp && r2 == r && i2 == idx) then acc
          else acc ++ [(sp, r, idx)]) []
      (normWrites (stT.memWrites ++ stE.memWrites)).map fun (sp, root, idx) =>
        (sp, root, idx, normSymIteStep cExpr
          (stT.expandHeapExpr 16 (stT.readBufSym sp root idx))
          (stE.expandHeapExpr 16 (stE.readBufSym sp root idx)))
  let mergedReachCond : SymExpr :=
    if !stT.reachable && !stE.reachable then .constBool false
    else if !stT.reachable then
      normSymIteStep cExpr (.constBool false) stE.reachCond
    else if !stE.reachable then
      normSymIteStep cExpr stT.reachCond (.constBool false)
    else
      normSymIteStep cExpr stT.reachCond stE.reachCond
  let branchUbT : SymExpr := stT.ubCond
  let branchUbE : SymExpr := stE.ubCond
  let mergedUbCond : SymExpr :=
    if st.ubCond == .constBool false then .constBool false
    else if !stT.reachable && !stE.reachable then st.ubCond
    else if !stT.reachable then SymExecState.conjoinUbCond st.ubCond branchUbE
    else if !stE.reachable then SymExecState.conjoinUbCond st.ubCond branchUbT
    else normSymIteStep cExpr branchUbT branchUbE
  let mergedEpoch :=
    if !stT.reachable then stE.heapStepEpoch
    else if !stE.reachable then stT.heapStepEpoch
    else Nat.max stT.heapStepEpoch stE.heapStepEpoch
  let mergedFreeEpoch :=
    if !stT.reachable then stE.extFreeEpoch
    else if !stE.reachable then stT.extFreeEpoch
    else Nat.max stT.extFreeEpoch stE.extFreeEpoch
  let mergedDynAllocIdx :=
    if !stT.reachable then stE.nextDynAllocIdx
    else if !stE.reachable then stT.nextDynAllocIdx
    else Nat.max stT.nextDynAllocIdx stE.nextDynAllocIdx
  let mergedExtLive :=
    if !stT.reachable then stE.extLivenessRoots
    else if !stE.reachable then stT.extLivenessRoots
    else stT.extLivenessRoots.filter (fun b => stE.extLivenessRoots.contains b)
  let mergedState : SymExecState := {
    vars := mergedVars
    bufAliases := mergedAliases
    exclusiveBufs := mergedExcl
    allocRoots := mergedAlloc
    ctorObjCounts :=
      if !stT.reachable then stE.ctorObjCounts
      else if !stE.reachable then stT.ctorObjCounts
      else (stT.ctorObjCounts ++ stE.ctorObjCounts.filter fun (r, n) =>
        (stT.ctorObjCounts.lookup r).isNone || stT.ctorObjCounts.lookup r == some n).filter fun (r, n) =>
          (stE.ctorObjCounts.lookup r).isNone || stE.ctorObjCounts.lookup r == some n
    typedTuples := mergedTypedTuples
    boolVars := mergedBoolVars
    u64Vars := mergedU64Vars
    u256Vars := mergedU256Vars
    sarrayVars := mergedSarrayVars
    objPtrVars := mergedObjPtrVars
    extSeenRoots := mergedExtSeen
    extLivenessRoots := mergedExtLive
    extRcDeltas := mergedExtDeltas
    extRcDeltaBounds := mergedExtDeltaBounds
    refCounts := mergedRefs
    rcExprs := mergedRcExprs
    heapStepEpoch := mergedEpoch
    extFreeEpoch := mergedFreeEpoch
    nextDynAllocIdx := mergedDynAllocIdx
    synVarBase := st.synVarBase
    reachCond := mergedReachCond
    ubCond := mergedUbCond
    noUB := st.noUB && condSv.noUB && (!stT.reachable || stT.noUB) && (!stE.reachable || stE.noUB)
    nonPoison := st.nonPoison && condSv.nonPoison && (!stT.reachable || stT.nonPoison) && (!stE.reachable || stE.nonPoison)
    reachable := stT.reachable || stE.reachable
    symUnsupported := st.symUnsupported || (stT.reachable && stT.symUnsupported) || (stE.reachable && stE.symUnsupported)
    symExhausted := st.symExhausted || stT.symExhausted || stE.symExhausted
    memWrites := mergedWrites
  }
  let mergedRet :=
    if !stT.reachable then normSymExpr retE
    else if !stE.reachable then normSymExpr retT
    else normSymIteStep cExpr (normSymExpr retT) (normSymExpr retE)
  (mergedState, mergedRet)

end LeanNative.Proofs
