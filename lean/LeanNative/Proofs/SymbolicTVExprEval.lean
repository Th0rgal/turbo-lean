import LeanNative.Proofs.SymbolicTVCall

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics

/-! ## `LNIRExpr` Symbolic Evaluation (`LeanNative.Proofs.SymbolicTVExprEval`) -/

/-- Symbolically evaluate an `LNIRExpr` and update `SymExecState`. -/
def symEvalExpr (st : SymExecState) (dst : VarId) (dstTy : LNIRType := .i64) (e : LNIRExpr) : SymExecState :=
  match e with
  | .scalar se =>
    let isPtrDest := callSlotKind dstTy == some true
    let (root?, rNonPoison, rNoUB, rUnsupp) := resolveScalarRoot? st se
    match root? with
    | some root =>
      if rUnsupp then
        ((st.clearAlias dst).markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
      else
        let rootSv := st.lookupVar root
        let st1 :=
          if root != dst && (isPtrDest || st.isDefinitelyHeapRoot root) then st.aliasBuf dst root
          else if !isPtrDest && !(st.isDefinitelyHeapRoot root) then st.clearAlias dst
          else st
        let rootSort := symExprScalarSort? st rootSv.expr
        let stSort :=
          if !isPtrDest && !(st1.isDefinitelyHeapRoot root) then
            match rootSort with
            | some 0 => st1.markBoolVar dst
            | some 1 => st1.markU64Var dst
            | some 2 => st1.markU256Var dst
            | _ => st1
          else st1
        let stTuple :=
          if st.typedTuples.contains root then
            stSort.markTypedTuple dst
          else
            stSort.unmarkTypedTuple dst
        let boundExpr :=
          if stTuple.isHeapObjectRoot root || isPtrDest then
            if stTuple.isImmediateScalarObj root && !stTuple.allocRoots.contains root then rootSv.expr
            else .symVar root
          else rootSv.expr
        stTuple.bindVar dst {
          expr := boundExpr
          nonPoison := rootSv.nonPoison && rNonPoison
          noUB := rootSv.noUB && rNoUB }
    | none =>
      let sr := symEvalScalarRes st se
      let actualExprSort := symExprScalarSort? st sr.val.expr
      let markNonTupleDst (cur : SymExecState) : SymExecState :=
        let c0 := cur.clearAlias dst
        let c1 :=
          match actualExprSort with
          | some 0 => c0.markBoolVar dst
          | some 1 => c0.markU64Var dst
          | some 2 => c0.markU256Var dst
          | _ => c0
        match sr.val.expr with
        | .tuple _ => c1.markTypedTuple dst
        | _ => c1.unmarkTypedTuple dst
      if sr.unsupported then
        ((st.clearAlias dst).markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
      else if isPtrDest || scalarExprMentionsHeapRoot st se then
        if isImmediateScalarExpr st se && !(scalarExprMentionsHeapRoot st se) then
          let stReq := (markNonTupleDst st).requireUbCond sr.ubCond
          let stB := stReq.bindVar dst { sr.val with noUB := true }
          { stB with ubCond := stReq.ubCond, noUB := stReq.noUB && sr.val.noUB }
        else
          -- Symbolic `.select` or arithmetic mixing unresolved heap pointers cannot collapse to a
          -- single alias root: mark symbolic execution unsupported so TV fails closed even in `src`!
          ((st.clearAlias dst).markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
      else
        let stReq := (markNonTupleDst st).requireUbCond sr.ubCond
        let stB := stReq.bindVar dst { sr.val with noUB := true }
        { stB with ubCond := stReq.ubCond, noUB := stReq.noUB && sr.val.noUB }
  | .constU256 val =>
    ((st.clearAlias dst).unmarkTypedTuple dst).markU256Var dst |>.bindVar dst
      { expr := .constU256 val, nonPoison := true, noUB := true }
  | .mulDivDown aVar bVar denomVar | .mulDivUp aVar bVar denomVar =>
    let sa := st.lookupVar aVar
    let sb := st.lookupVar bVar
    let sd := st.lookupVar denomVar
    let isUp := match e with | .mulDivUp _ _ _ => true | _ => false
    let toW256? : SymExpr → Option UInt256
      | .constU256 w => some w
      | .constU64 x => some (UInt256.ofUInt64 x)
      | _ => none
    let lift256 (x : SymExpr) : SymExpr := match x with | .constU64 u => .constU256 (UInt256.ofUInt64 u) | _ => x
    let sortA := symExprScalarSort? st sa.expr
    let sortB := symExprScalarSort? st sb.expr
    let sortD := symExprScalarSort? st sd.expr
    if sortA == some sortBool || sortB == some sortBool || sortD == some sortBool || !sa.noUB || !sb.noUB || !sd.noUB then
      ((st.clearAlias dst).unmarkTypedTuple dst).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    else if sortA.isNone || sortB.isNone || sortD.isNone then
      (((st.clearAlias dst).unmarkTypedTuple dst).markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    else
      match toW256? sa.expr, toW256? sb.expr, toW256? sd.expr with
      | some wa, some wb, some wd =>
        let qOpt := if isUp then UInt256.mulDivUp wa wb wd else UInt256.mulDivDown wa wb wd
        match qOpt with
        | some qw =>
          (((st.clearAlias dst).unmarkTypedTuple dst).markU256Var dst).bindVar dst
            { expr := .constU256 qw, nonPoison := sa.nonPoison && sb.nonPoison && sd.nonPoison, noUB := true }
        | none =>
          ((st.clearAlias dst).unmarkTypedTuple dst).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
      | _, _, _ =>
        let la := lift256 sa.expr
        let lb := lift256 sb.expr
        let ld := lift256 sd.expr
        let nzCond := normSymUnaryOpStep .not (normSymBinOpStep .eq ld (.constU256 UInt256.zero))
        let mdExpr := SymExpr.mulDiv256 isUp la lb ld
        let ovfCond := SymExpr.binOp .le mdExpr (.constU256 UInt256.max)
        let stReq := (((st.clearAlias dst).unmarkTypedTuple dst).markU256Var dst).requireUbCond
          (SymExecState.conjoinUbCond nzCond ovfCond)
        let stB := stReq.bindVar dst {
          expr := mdExpr
          nonPoison := sa.nonPoison && sb.nonPoison && sd.nonPoison
          noUB := true }
        { stB with ubCond := stReq.ubCond, noUB := false }
  | .storageLoad mapVar slotVar | .sarrayGet mapVar slotVar _ | .rawLoad mapVar slotVar _ =>
    let slotSv := st.lookupVar slotVar
    let isStorage := match e with | .storageLoad _ _ => true | _ => false
    let slotExpr := if isStorage then (match slotSv.expr with | .constU64 u => .constU256 (UInt256.ofUInt64 u) | x => x) else slotSv.expr
    let elemExpr := st.readBufSym .sarray mapVar slotExpr
    let stSorted :=
      let c0 := (st.clearAlias dst).unmarkTypedTuple dst
      if isStorage then c0.markU256Var dst else c0.markU64Var dst
    stSorted.bindVar dst { expr := elemExpr, nonPoison := slotSv.nonPoison, noUB := slotSv.noUB }
  | .storageStore mapVar slotVar valVar =>
    let root := st.resolveBuf mapVar
    let slotSv := st.lookupVar slotVar
    let valSv := st.lookupVar valVar
    let slotExpr := match slotSv.expr with | .constU64 u => .constU256 (UInt256.ofUInt64 u) | x => x
    let valExpr := match valSv.expr with | .constU64 u => .constU256 (UInt256.ofUInt64 u) | x => x
    let st1 := ((st.markU256Var root).writeBufSym .sarray root slotExpr valExpr false).aliasBuf dst root
    st1.bindVar dst { expr := .symVar root, nonPoison := slotSv.nonPoison && valSv.nonPoison, noUB := slotSv.noUB && valSv.noUB }
  | .mkTuple fields =>
    let svs := fields.map st.lookupVar
    let fieldExprs := fields.map fun v =>
      let root := st.resolveBuf v
      let rv := st.lookupVar root
      if st.allocRoots.contains root || (st.refCounts.lookup root).isSome ||
         (st.rcExprs.lookup root).isSome || st.exclusiveBufs.contains root ||
         st.extSeenRoots.contains root then
        .symVar root
      else match rv.expr with
        | .symVar rId => .symVar (st.resolveBuf rId)
        | .tuple _ =>
          if st.typedTuples.contains root then rv.expr else .symVar root
        | e => e
    (st.markTypedTuple dst).bindVar dst { expr := .tuple fieldExprs, nonPoison := svs.all (·.nonPoison), noUB := svs.all (·.noUB) }
  | .projTuple tupleVar idx =>
    let root := st.resolveBuf tupleVar
    let tv := st.lookupVar root
    if st.isDefinitelyHeapRoot root || st.boolVars.contains root || st.u64Vars.contains root || st.u256Vars.contains root ||
       st.isImmediateScalarObj root then
      ((st.clearAlias dst).unmarkTypedTuple dst).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    else
      match tv.expr with
      | .tuple fs =>
        if st.typedTuples.contains root then
          match fs[idx]? with
          | some fExpr =>
            let st' :=
              match fExpr with
              | .symVar fId =>
                let eff := st.resolveBuf fId
                let isScalarLeaf := st.boolVars.contains eff || st.u64Vars.contains eff || st.u256Vars.contains eff
                if !isScalarLeaf then st.aliasBuf dst eff
                else st.clearAlias dst
              | _ => st.clearAlias dst
            let isTypedSubTuple :=
              match fExpr with
              | .tuple _ => true
              | .symVar fId => st.typedTuples.contains (st.resolveBuf fId)
              | _ => false
            let stSort :=
              if isTypedSubTuple then st'.markTypedTuple dst
              else
                let stU := st'.unmarkTypedTuple dst
                match symExprScalarSort? stU fExpr with
                | some 0 => stU.markBoolVar dst
                | some 1 => stU.markU64Var dst
                | some 2 => stU.markU256Var dst
                | _ =>
                  match fExpr with
                  | .symVar fId =>
                    let eff := stU.resolveBuf fId
                    if stU.objPtrVars.contains eff || stU.allocRoots.contains eff then stU.markObjPtrVar dst
                    else if stU.sarrayVars.contains eff then stU.markSarrayVar dst
                    else stU
                  | _ => stU
            stSort.bindVar dst { expr := fExpr, nonPoison := tv.nonPoison, noUB := tv.noUB }
          | none => ((st.clearAlias dst).unmarkTypedTuple dst).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
        else
          ((st.clearAlias dst).unmarkTypedTuple dst).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
      | _ =>
        -- Projected field from an unresolved non-tuple or conditional `.ite` tuple:
        -- mark symbolic execution unsupported so TV fails closed even in `src`!
        (((st.clearAlias dst).unmarkTypedTuple dst).markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
  | .allocCtor tag objFields scalarFields =>
    if tag > 0xFFFFFFFFFFFFFFFF then
      -- Concrete `HeapObj.tag : Nat` retains unbounded tags whereas `SymExpr.constU64` is 64-bit:
      -- fail closed (`symUnsupported`) rather than truncating `tag.toUInt64`!
      (((st.clearAlias dst).unmarkTypedTuple dst).markUnsupported).bindVar dst
        { expr := .unit, nonPoison := false, noUB := false }
    else if objFields.isEmpty && scalarFields.isEmpty then
      -- C1.1: a fieldless ctor is the immediate `.tuple [tag]` (`Eval.lean` `allocCtor tag [] []`), never an
      -- RC-managed root: RC ops are no-ops and `isExclusive` is `true` (typed-tuple paths of
      -- `updateRefCountFuel` / `.isExclusive`), exactly as `evalIncRef`/`evalDecRef` treat a non-heap value.
      ((st.clearVarSortTags dst).clearAlias dst |>.markTypedTuple dst).bindVar dst
        { expr := .tuple [.constU64 tag.toUInt64], nonPoison := true, noUB := true }
    else
      let svs := (objFields ++ scalarFields).map st.lookupVar
      let encodeCtorField (v : VarId) : SymExpr :=
        let root := st.resolveBuf v
        let rv := st.lookupVar root
        if st.isHeapObjectRoot root then .symVar root
        else match rv.expr with
          | .symVar rId => .symVar (st.resolveBuf rId)
          | e => e
      let objectExprs := objFields.map encodeCtorField
      let scalarExprs := scalarFields.map encodeCtorField
      let allocId := SymExecState.dynAllocRootId st.synVarBase st.nextDynAllocIdx
      let st0 := { st with nextDynAllocIdx := st.nextDynAllocIdx + 1 }
      let st1a := (st0.markAllocated allocId).markObjPtrVar allocId
      -- C1.1: record `|objFields|` so `ctorGetScalar i` / `ctor_set_scalar i` index `scalarFields[i]`
      let st1 : SymExecState :=
        { st1a with ctorObjCounts := (allocId, objFields.length) :: st1a.ctorObjCounts.filter (·.1 != allocId) }
      let st2 := st1.bindVar allocId {
        expr := .tuple (.constU64 tag.toUInt64 :: objectExprs ++ scalarExprs)
        nonPoison := svs.all (·.nonPoison)
        noUB := svs.all (·.noUB)
      }
      (((st2.clearVarSortTags dst).aliasBuf dst allocId).markObjPtrVar dst).bindVar dst {
        expr := .symVar allocId
        nonPoison := svs.all (·.nonPoison)
        noUB := svs.all (·.noUB)
      }
  | .ctorGetObj ctorVar idx | .ctorGetScalar ctorVar idx _ =>
        let isScalarProj :=
          match e with
          | .ctorGetScalar _ _ _ => true
          | _ => callSlotKind dstTy == some false
    let rootVar := st.resolveBuf ctorVar
    if st.sarrayVars.contains rootVar ||
       st.boolVars.contains rootVar || st.u64Vars.contains rootVar || st.u256Vars.contains rootVar then
      ((st.clearAlias dst).unmarkTypedTuple dst).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    else if st.typedTuples.contains rootVar then
      let tv := st.lookupVar rootVar
      match tv.expr with
      | .tuple (_tag :: fs) =>
        -- Concrete `evalExpr` (`Semantics/Eval.lean:289-293,306-310`) treats `.tuple (_tag :: vals)` as
        -- a constructor tuple (skipping element 0 and projecting `vals[idx]?` without heap RC checks).
        match fs[idx]? with
        | some fExpr =>
          let st' :=
            match fExpr with
            | .symVar fId =>
              let eff := st.resolveBuf fId
              let isScalarLeaf := st.boolVars.contains eff || st.u64Vars.contains eff || st.u256Vars.contains eff
              if !isScalarLeaf then st.aliasBuf dst eff
              else st.clearAlias dst
            | _ => st.clearAlias dst
          let isTypedSubTuple :=
            match fExpr with
            | .tuple _ => true
            | .symVar fId => st.typedTuples.contains (st.resolveBuf fId)
            | _ => false
          let stSort :=
            if isTypedSubTuple then st'.markTypedTuple dst
            else
              let stU := st'.unmarkTypedTuple dst
              match symExprScalarSort? stU fExpr with
              | some 0 => stU.markBoolVar dst
              | some 1 => stU.markU64Var dst
              | some 2 => stU.markU256Var dst
              | _ =>
                match fExpr with
                | .symVar fId =>
                  let eff := stU.resolveBuf fId
                  if stU.objPtrVars.contains eff || stU.allocRoots.contains eff then stU.markObjPtrVar dst
                  else if stU.sarrayVars.contains eff then stU.markSarrayVar dst
                  else stU
                | _ => stU
          stSort.bindVar dst { expr := fExpr, nonPoison := tv.nonPoison, noUB := tv.noUB }
        | none => ((st.clearAlias dst).unmarkTypedTuple dst).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
      | .tuple [] =>
        ((st.clearAlias dst).unmarkTypedTuple dst).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
      | _ =>
        (((st.clearAlias dst).unmarkTypedTuple dst).markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    else
    let liveOk := st.isBufLive rootVar
    let stLive := (st.requireUbCond (st.liveRcCond rootVar)).noteExtLiveRoot rootVar
    let cv := stLive.lookupVar rootVar
    let isScalarSlot := match e with | .ctorGetScalar _ _ _ => true | _ => false
    -- C1.1 separate index spaces: a scalar read is at `|objFields| + idx` of the `tag :: objs ++ scalars`
    -- snapshot; an unknown split fails closed (`none`).
    let flatIdx? : Option Nat :=
      if isScalarSlot then (stLive.ctorObjCounts.lookup rootVar).map (· + idx)
      -- an object read past `|objFields|` must never land in the scalar space (OOB / out of window)
      else match stLive.ctorObjCounts.lookup rootVar with
        | some n => if idx < n then some idx else some (2 ^ 64)
        | none => some idx
    match cv.expr with
    | .tuple (_tag :: fs) =>
      let stBounds :=
        if stLive.allocRoots.contains rootVar then stLive
        else stLive.requireUbCond (.binOp .lt (.constU64 idx.toUInt64) (.ctorLen isScalarSlot stLive.extFreeEpoch rootVar))
      match flatIdx?.bind (fs[·]?) with
      | some fExpr =>
        let stClear := stBounds.clearAlias dst
        let st' :=
          match fExpr with
          | .symVar fId =>
            let effFId := stBounds.resolveBuf fId
            if stBounds.typedTuples.contains effFId then
              if isScalarProj then stClear.markTypedTuple dst else (stBounds.aliasBuf dst effFId).markTypedTuple dst
            else
              match symExprScalarSort? stBounds fExpr with
              | some 0 => stClear.markBoolVar dst
              | some 1 => stClear.markU64Var dst
              | some 2 => stClear.markU256Var dst
              | _ =>
                if stBounds.isNeverScalarRef effFId then
                  let stA := stBounds.aliasBuf dst effFId
                  if stBounds.objPtrVars.contains effFId || stBounds.allocRoots.contains effFId then stA.markObjPtrVar dst
                  else if stBounds.sarrayVars.contains effFId then stA.markSarrayVar dst
                  else stA
                else
                  stBounds.aliasBuf dst effFId
          | .tuple _ => stClear.markTypedTuple dst
          | _ =>
            match symExprScalarSort? stBounds fExpr with
            | some 0 => stClear.markBoolVar dst
            | some 1 => stClear.markU64Var dst
            | some 2 => stClear.markU256Var dst
            | _ => stClear
        let stBound := st'.bindVar dst { expr := fExpr, nonPoison := cv.nonPoison && liveOk, noUB := cv.noUB && liveOk }
        { stBound with noUB := stBound.noUB && st.liveRcCond rootVar == .constBool true &&
            (stLive.allocRoots.contains rootVar || stBounds.ubCond == .constBool true) }
      | none =>
        if flatIdx?.isNone then
          -- C1.1: unknown object/scalar split for a scalar read fails closed
          (stBounds.markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
        else if stLive.allocRoots.contains rootVar then
          stBounds.bindVar dst { expr := .unit, nonPoison := false, noUB := false }
        else
          -- External input/projected constructor cached at the 8-field modeling window may have >= 9 concrete fields!
          (stBounds.markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    | .symVar rootId =>
      if !(st.objPtrVars.contains rootVar || st.allocRoots.contains rootVar ||
           (st.refCounts.lookup rootVar).isSome || (st.rcExprs.lookup rootVar).isSome ||
           st.exclusiveBufs.contains rootVar) then
        -- `.taggedPtr` or untyped projected child may hold an immediate scalar (`typeError`),
        -- an unboxed tuple (`.tuple (_ :: _)`), or a heap `.objPtr`!
        (stLive.markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
      else if idx ≥ 8 then
        -- Concrete `evalExpr` permits arbitrary `obj.fields` lengths on `.objPtr`: mark `idx >= 8`
        -- unsupported (`symUnsupported`) rather than assuming definite source UB!
        (stLive.markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
      else
        let effRoot := stLive.resolveBuf rootId
        let stBounds := stLive.requireUbCond (.binOp .lt (.constU64 idx.toUInt64) (.ctorLen isScalarSlot stLive.extFreeEpoch effRoot))
        -- C1.1: scalar slot `i` of an external root is a distinct synthetic root (`8 + i`), never object slot `i`
        let spaceIdx := if isScalarSlot then 8 + idx else idx
        let fieldRoot := SymExecState.projFieldRootId stBounds.synVarBase stBounds.heapStepEpoch effRoot spaceIdx
        let stBase := (stBounds.noteExtLiveRoot effRoot).noteExtRoot fieldRoot
        let stBound := (stBase.aliasBuf dst fieldRoot).bindVar dst
          { expr := .symVar fieldRoot, nonPoison := cv.nonPoison && liveOk, noUB := cv.noUB && liveOk }
        { stBound with noUB := false }
    | .constU64 _ | .constU256 _ | .constBool _ | .unit =>
      -- Projecting a constructor field from an immediate scalar is concrete UB (`typeError`)!
      stLive.bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    | _ =>
      (stLive.markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
  | .isExclusive objVar =>
    let rootVar := st.resolveBuf objVar
    let stOut := st.markBoolVar dst
    if st.isImmediateScalarObj rootVar || st.typedTuples.contains rootVar ||
       st.boolVars.contains rootVar || st.u64Vars.contains rootVar || st.u256Vars.contains rootVar then
      let cv := st.lookupVar rootVar
      stOut.bindVar dst { expr := .constBool true, nonPoison := cv.nonPoison, noUB := cv.noUB }
    else if st.isNeverScalarRef rootVar then
      let stNoted := st.noteExtRoot rootVar
      let liveOk := stNoted.isBufLive rootVar
      let liveC := stNoted.liveRcCond rootVar
      let stLive := ((stNoted.requireUbCond liveC).noteExtLiveRoot rootVar).markBoolVar dst
      let exclExpr : SymExpr :=
        if stLive.isBufExclusive rootVar then .constBool true
        else normSymBinOpStep .eq (stLive.lookupRcExpr rootVar) (.constU64 1)
      let cv := stLive.lookupVar rootVar
      let stBound := stLive.bindVar dst { expr := exclExpr, nonPoison := cv.nonPoison && liveOk, noUB := cv.noUB && liveOk }
      { stBound with noUB := stBound.noUB && liveC == .constBool true }
    else
      (stOut.markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
  | .sarrayLen arrVar =>
    let root := st.resolveBuf arrVar
    let sa := st.lookupVar arrVar
    let stOut := st.markU64Var dst
    if st.isImmediateScalarObj root || st.typedTuples.contains root ||
       st.boolVars.contains root || st.u64Vars.contains root || st.u256Vars.contains root ||
       st.objPtrVars.contains root ||
       (st.allocRoots.contains root && !(st.sarrayVars.contains root)) then
      stOut.bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    else if st.sarrayVars.contains root then
      let liveC := st.liveRcCond root
      let stLive := (((st.noteExtRoot root).requireUbCond liveC).noteExtLiveRoot root).markU64Var dst
      let stBound := stLive.bindVar dst { expr := .sarrayLen root, nonPoison := sa.nonPoison, noUB := sa.noUB }
      { stBound with noUB := stBound.noUB && liveC == .constBool true }
    else
      (stOut.markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
  | .sarrayDataPtr arrVar _elemTy =>
    let root := st.resolveBuf arrVar
    let arrSv := st.lookupVar arrVar
    if st.isImmediateScalarObj root || st.typedTuples.contains root ||
       st.boolVars.contains root || st.u64Vars.contains root || st.u256Vars.contains root ||
       st.objPtrVars.contains root ||
       (st.allocRoots.contains root && !(st.sarrayVars.contains root)) then
      ((st.clearAlias dst).unmarkTypedTuple dst).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    else
      let exclOk := st.isBufExclusive root
      let stExcl := st.requireUbCond (st.exclRcCond root)
      let stBound := (stExcl.aliasBuf dst root).bindVar dst { expr := .symVar root, nonPoison := arrSv.nonPoison, noUB := arrSv.noUB }
      { stBound with ubCond := if arrSv.noUB then stExcl.ubCond else .constBool false, noUB := stBound.noUB && exclOk }
  | .sarrayEnsureExclusive arrVar _elemTy =>
    let root := st.resolveBuf arrVar
    let arrSv := st.lookupVar arrVar
    if st.isImmediateScalarObj root || st.typedTuples.contains root ||
       st.boolVars.contains root || st.u64Vars.contains root || st.u256Vars.contains root ||
       st.objPtrVars.contains root ||
       (st.allocRoots.contains root && !(st.sarrayVars.contains root)) then
      ((st.clearAlias dst).unmarkTypedTuple dst).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    else if st.sarrayVars.contains root then
      let liveC := st.liveRcCond root
      let stLive := ((st.noteExtRoot root).requireUbCond liveC).noteExtLiveRoot root
      let stBound := (((stLive.markExclusive root).aliasBuf dst root).markSarrayVar dst).bindVar dst
        { expr := .symVar root, nonPoison := arrSv.nonPoison, noUB := arrSv.noUB }
      { stBound with noUB := stBound.noUB && liveC == .constBool true }
    else
      (((st.clearAlias dst).unmarkTypedTuple dst).markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
  | .sarraySet arrVar idxVar valVar _elemTy =>
    let root := st.resolveBuf arrVar
    let arrSv := st.lookupVar arrVar
    let idxSv := st.lookupVar idxVar
    let valSv := st.lookupVar valVar
    if st.isImmediateScalarObj root || st.typedTuples.contains root ||
       st.boolVars.contains root || st.u64Vars.contains root || st.u256Vars.contains root ||
       st.objPtrVars.contains root ||
       (st.allocRoots.contains root && !(st.sarrayVars.contains root)) then
      ((st.clearAlias dst).unmarkTypedTuple dst).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    else if st.sarrayVars.contains root then
      let liveC := st.liveRcCond root
      let stLive := ((st.noteExtRoot root).requireUbCond liveC).noteExtLiveRoot root
      let st3 := (((stLive.markExclusive root).writeBufSym .sarray root idxSv.expr valSv.expr true).aliasBuf dst root).markSarrayVar dst
      let stBound := st3.bindVar dst {
        expr := .symVar root
        nonPoison := arrSv.nonPoison && idxSv.nonPoison && valSv.nonPoison
        noUB := arrSv.noUB && idxSv.noUB && valSv.noUB }
      { stBound with noUB := stBound.noUB && liveC == .constBool true }
    else
      (((st.clearAlias dst).unmarkTypedTuple dst).markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
  | .unboxScalar valVar _ =>
    let r := st.resolveBuf valVar
    let rVal := st.lookupVar r
    let st1 := if valVar != dst && st.isHeapObjectRoot r then st.aliasBuf dst r else st.clearAlias dst
    let st2 :=
      if st1.isNeverScalarRef r then st1
      else if st1.typedTuples.contains r || (match rVal.expr with | .tuple _ => true | _ => false) then st1.markTypedTuple dst
      else
        match symExprScalarSort? st1 rVal.expr with
        | some 0 => (st1.unmarkTypedTuple dst).markBoolVar dst
        | some 1 => (st1.unmarkTypedTuple dst).markU64Var dst
        | some 2 => (st1.unmarkTypedTuple dst).markU256Var dst
        | _ => st1.unmarkTypedTuple dst
    st2.bindVar dst rVal
  | .boxScalar valVar _ =>
    let r := st.resolveBuf valVar
    let rVal := st.lookupVar r
    let st1 := if valVar != dst && st.isHeapObjectRoot r then st.aliasBuf dst r else st.clearAlias dst
    let st2 :=
      if st1.isNeverScalarRef r then st1
      else if st1.typedTuples.contains r || (match rVal.expr with | .tuple _ => true | _ => false) then st1.markTypedTuple dst
      else
        match symExprScalarSort? st1 rVal.expr with
        | some 0 => (st1.unmarkTypedTuple dst).markBoolVar dst
        | some 1 => (st1.unmarkTypedTuple dst).markU64Var dst
        | some 2 => (st1.unmarkTypedTuple dst).markU256Var dst
        | _ => st1.unmarkTypedTuple dst
    st2.bindVar dst rVal
  | .call fnName args retTy isExt =>
    symEvalCallRuntime st dst fnName args retTy isExt

end LeanNative.Proofs
