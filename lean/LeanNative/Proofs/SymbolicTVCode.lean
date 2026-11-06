import LeanNative.Proofs.SymbolicTVMerge

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics

/-! ## Code & Declaration Symbolic Execution (`LeanNative.Proofs.SymbolicTVCode`) -/

/-- Summary produced by symbolic execution of an `LNIRDecl`. -/
structure SymExecSummary where
  declName       : String
  reachable      : Bool
  reachCond      : SymExpr
  ubCond         : SymExpr
  noUB           : Bool
  nonPoison      : Bool
  symUnsupported : Bool
  symExhausted   : Bool
  synVarBase       : VarId
  retVal           : SymExpr
  jointHeap        : SymExpr
  rcDeltas         : List (VarId × SymExpr)
  memWrites        : List (MemWriteSpace × VarId × SymExpr × SymExpr)
  deriving Repr, Inhabited, BEq

def symExprMentionsHeapRoot (st : SymExecState) : SymExpr → Bool
  | .symVar id => st.isHeapObjectRoot id
  | .ite _ a b => symExprMentionsHeapRoot st a || symExprMentionsHeapRoot st b
  | _ => false

/-- Unroll a `seqFor` loop body `unrollCount` times symbolically. -/
def symExecLoopUnroll (unrollCount : Nat) (curIdx : Nat) (idxVar accVar : VarId)
    (st : SymExecState) (execBody : SymExecState → SymExecState × SymExpr) : SymExecState :=
  match unrollCount with
  | 0 => st
  | n + 1 =>
    let stIdx := st.bindVar idxVar { expr := .constU64 curIdx.toUInt64, nonPoison := true, noUB := true }
    let (stAfter, retExpr) := execBody stIdx
    let normRet := normSymExpr retExpr
    let stepDefinitelyUB := normSymExpr stAfter.ubCond == .constBool false
    let accValNoUB := !stepDefinitelyUB
    let stCleared := stAfter.clearVarSortTags accVar
    let stNext :=
      match normRet with
      | .symVar r =>
        let eff := stCleared.resolveBuf r
        let stAlias := if accVar != eff then stCleared.aliasBuf accVar eff else stCleared.clearAlias accVar
        let stSort :=
          if stAlias.typedTuples.contains eff then stAlias.markTypedTuple accVar
          else if stAlias.allocRoots.contains eff || stAlias.objPtrVars.contains eff then stAlias.markObjPtrVar accVar
          else if stAlias.sarrayVars.contains eff then stAlias.markSarrayVar accVar
          else
            match symExprScalarSort? stAlias normRet with
            | some 0 => stAlias.markBoolVar accVar
            | some 1 => stAlias.markU64Var accVar
            | some 2 => stAlias.markU256Var accVar
            | _ => stAlias
        if accVar == eff then
          { stSort with
              ubCond := if stepDefinitelyUB then .constBool false else stSort.ubCond
              noUB := stSort.noUB && stAfter.noUB && accValNoUB
              nonPoison := stSort.nonPoison && stAfter.nonPoison }
        else
          let stB := stSort.bindVar accVar {
            expr := normRet
            nonPoison := stAfter.nonPoison
            noUB := accValNoUB
          }
          { stB with ubCond := stAfter.ubCond, noUB := stB.noUB && stAfter.noUB }
      | .tuple _ =>
        let stB := ((stCleared.clearAlias accVar).markTypedTuple accVar).bindVar accVar {
          expr := normRet
          nonPoison := stAfter.nonPoison
          noUB := accValNoUB
        }
        { stB with ubCond := stAfter.ubCond, noUB := stB.noUB && stAfter.noUB }
      | _ =>
        if symExprMentionsHeapRoot stCleared normRet then
          ((stCleared.clearAlias accVar).markUnsupported).bindVar accVar {
            expr := .unit
            nonPoison := false
            noUB := false
          }
        else
          let stSort :=
            match symExprScalarSort? stCleared normRet with
            | some 0 => (stCleared.clearAlias accVar).markBoolVar accVar
            | some 1 => (stCleared.clearAlias accVar).markU64Var accVar
            | some 2 => (stCleared.clearAlias accVar).markU256Var accVar
            | _ => stCleared.clearAlias accVar
          let stB := stSort.bindVar accVar {
            expr := normRet
            nonPoison := stAfter.nonPoison
            noUB := accValNoUB
          }
          { stB with ubCond := stAfter.ubCond, noUB := stB.noUB && stAfter.noUB }
    symExecLoopUnroll n (curIdx + 1) idxVar accVar stNext execBody

/-- Fuel-bounded symbolic execution of `LNIRCode` (`expandRetHeap = true` at declaration exit,
    `false` inside `seqFor` step bodies so returned heap roots stay as unexpanded `.symVar`s). -/
def symExecCode (fuel : Nat) (unrollBound : Nat) (st : SymExecState) (code : LNIRCode)
    (expandRetHeap : Bool := true) : SymExecState × SymExpr :=
  match fuel with
  | 0 => (st.markExhausted, .unit)
  | fuel' + 1 =>
    let loopBound := unrollBound
    let retExpand := expandRetHeap
    match code with
    | .letBind dst ty val k =>
      match val with
      | .scalar (.select cond tExp eExp) =>
        let (root?, _, _, _) := resolveScalarRoot? st (.select cond tExp eExp)
        let rcPre := symEvalScalarRes st cond
        let rtPre := symEvalScalarRes st tExp
        let rePre := symEvalScalarRes st eExp
        let isImmSelect := isImmediateScalarExpr st (.select cond tExp eExp) &&
          !(scalarExprMentionsHeapRoot st tExp || scalarExprMentionsHeapRoot st eExp) &&
          !rcPre.unsupported && !rtPre.unsupported && !rePre.unsupported &&
          (rtPre.ubCond == rePre.ubCond) && (rtPre.val.noUB == rePre.val.noUB)
        let selectBranchesMentionRoot :=
          let mentionsAny : ScalarExpr → Bool
            | .var id => st.isHeapObjectRoot id || st.typedTuples.contains (st.resolveBuf id)
            | .select _ a b =>
              let checkSub (x : ScalarExpr) := match x with
                | .var v => st.isHeapObjectRoot v || st.typedTuples.contains (st.resolveBuf v)
                | _ => false
              checkSub a || checkSub b
            | _ => false
          mentionsAny tExp || mentionsAny eExp
        let needsBranchDesugar :=
          !rcPre.unsupported &&
          (rtPre.unsupported || rePre.unsupported || rtPre.ubCond != rePre.ubCond || rtPre.val.noUB != rePre.val.noUB ||
           callSlotKind ty == some true || scalarExprMentionsHeapRoot st tExp ||
           scalarExprMentionsHeapRoot st eExp || selectBranchesMentionRoot ||
           (match rtPre.val.expr, rePre.val.expr with | .tuple _, _ | _, .tuple _ => true | _, _ => false))
        if root?.isNone && !isImmSelect && needsBranchDesugar then
          -- Desugar conditional `ScalarExpr.select cond tExp eExp` into an exact symbolic `.ite`
          -- diamond so branch-conditional UB, typed-tuple provenance, and heap-root aliases stay exact!
          let condTmp : VarId := SymExecState.desugarTmpBase st.synVarBase fuel'
          let condSort := symExprScalarSort? st rcPre.val.expr
          let condIsTypedTuple :=
            match cond with
            | .var cid => st.typedTuples.contains (st.resolveBuf cid)
            | _ => match rcPre.val.expr with | .tuple _ => true | _ => false
          let condIsHeapPtr :=
            match cond with
            | .var cid => st.isDefinitelyHeapRoot cid && !(st.isImmediateScalarObj cid)
            | _ => false
          let condBadSort := condSort.isNone && !condIsTypedTuple && !condIsHeapPtr
          if condIsTypedTuple || condIsHeapPtr || rcPre.ubCond == .constBool false then
            let stBad := ((st.clearAlias dst).unmarkTypedTuple dst).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
            symExecCode fuel' unrollBound stBad k expandRetHeap
          else
            let stBase0 := if rcPre.unsupported || condBadSort then st.markUnsupported else st
            let stBase := stBase0.requireUbCond rcPre.ubCond
            let cExprNorm : SymExpr :=
              if condSort == some sortU64 then normSymUnaryOpStep .not (normSymBinOpStep .eq rcPre.val.expr (.constU64 0))
              else if condSort == some sortU256 then normSymUnaryOpStep .not (normSymBinOpStep .eq rcPre.val.expr (.constU256 UInt256.zero))
              else rcPre.val.expr
            let stCond := ((stBase.clearAlias condTmp).markBoolVar condTmp).bindVar condTmp
              { rcPre.val with expr := cExprNorm, noUB := true }
            let stCondFinal := { stCond with ubCond := stBase.ubCond, noUB := stBase.noUB && rcPre.val.noUB }
            symExecCode fuel' unrollBound stCondFinal
              (.ite condTmp (.letBind dst ty (.scalar tExp) k) (.letBind dst ty (.scalar eExp) k)) expandRetHeap
        else
          let st0 := if callSlotKind ty == some false && root?.isNone then st.clearAlias dst else st
          let st1 := symEvalExpr st0 dst ty val
          symExecCode fuel' unrollBound st1 k expandRetHeap
      | .projTuple tupleVar idx =>
        let tRoot := st.resolveBuf tupleVar
        let tv := st.lookupVar tRoot
        if !(st.typedTuples.contains tRoot) || st.isDefinitelyHeapRoot tRoot then
          let st1 := symEvalExpr st dst ty val
          symExecCode fuel' unrollBound st1 k expandRetHeap
        else
        match tv.expr with
        | .tuple fs =>
          match fs[idx]? with
          | some (.ite cond tBranch eBranch) =>
            if callSlotKind ty == some true || symExprMentionsHeapRoot st tBranch || symExprMentionsHeapRoot st eBranch then
              let condTmp : VarId := SymExecState.desugarTmpBase st.synVarBase fuel'
              let tTmp : VarId := condTmp + 1
              let eTmp : VarId := condTmp + 2
              let mkBranchBind (tmpId : VarId) (bExpr : SymExpr) ( curSt : SymExecState ) : SymExecState × LNIRCode :=
                match bExpr with
                | .symVar rId =>
                  let eff := curSt.resolveBuf rId
                  (curSt, .letBind dst ty (.scalar (.var eff)) k)
                | _ =>
                  let s1 := (curSt.clearAlias tmpId).bindVar tmpId { expr := .tuple [bExpr], nonPoison := tv.nonPoison, noUB := tv.noUB }
                  let s2 := s1.markTypedTuple tmpId
                  (s2, .letBind dst ty (.projTuple tmpId 0) k)
              let stCond := ((st.clearAlias condTmp).markBoolVar condTmp).bindVar condTmp
                { expr := cond, nonPoison := tv.nonPoison, noUB := tv.noUB }
              let (stWithT, codeT) := mkBranchBind tTmp tBranch stCond
              let (stWithTE, codeE) := mkBranchBind eTmp eBranch stWithT
              symExecCode fuel' unrollBound stWithTE (.ite condTmp codeT codeE) expandRetHeap
            else
              let st1 := symEvalExpr st dst ty val
              symExecCode fuel' unrollBound st1 k expandRetHeap
          | _ =>
            let st1 := symEvalExpr st dst ty val
            symExecCode fuel' unrollBound st1 k expandRetHeap
        | _ =>
          let st1 := symEvalExpr st dst ty val
          symExecCode fuel' unrollBound st1 k expandRetHeap
      | .ctorGetObj ctorVar idx | .ctorGetScalar ctorVar idx _ =>
        let rootVar := st.resolveBuf ctorVar
        let cv := st.lookupVar rootVar
        if st.typedTuples.contains rootVar then
          match cv.expr with
          | .tuple (_ :: fs) =>
            match fs[idx]? with
            | some (.ite cond tBranch eBranch) =>
              if callSlotKind ty == some true || symExprMentionsHeapRoot st tBranch || symExprMentionsHeapRoot st eBranch then
                let condTmp : VarId := SymExecState.desugarTmpBase st.synVarBase fuel'
                let tTmp : VarId := condTmp + 1
                let eTmp : VarId := condTmp + 2
                let mkBranchBind (tmpId : VarId) (bExpr : SymExpr) (curSt : SymExecState) : SymExecState × LNIRCode :=
                  match bExpr with
                  | .symVar rId =>
                    let eff := curSt.resolveBuf rId
                    (curSt, .letBind dst ty (.scalar (.var eff)) k)
                  | _ =>
                    let s1 := (curSt.clearAlias tmpId).bindVar tmpId { expr := .tuple [bExpr], nonPoison := cv.nonPoison, noUB := cv.noUB }
                    let s2 := s1.markTypedTuple tmpId
                    (s2, .letBind dst ty (.projTuple tmpId 0) k)
                let stCond := ((st.clearAlias condTmp).markBoolVar condTmp).bindVar condTmp
                  { expr := cond, nonPoison := cv.nonPoison, noUB := cv.noUB }
                let (stWithT, codeT) := mkBranchBind tTmp tBranch stCond
                let (stWithTE, codeE) := mkBranchBind eTmp eBranch stWithT
                symExecCode fuel' unrollBound stWithTE (.ite condTmp codeT codeE) expandRetHeap
              else
                let st1 := symEvalExpr st dst ty val
                symExecCode fuel' unrollBound st1 k expandRetHeap
            | _ =>
              let st1 := symEvalExpr st dst ty val
              symExecCode fuel' unrollBound st1 k expandRetHeap
          | _ =>
            let st1 := symEvalExpr st dst ty val
            symExecCode fuel' unrollBound st1 k expandRetHeap
        else if st.sarrayVars.contains rootVar ||
           st.boolVars.contains rootVar || st.u64Vars.contains rootVar || st.u256Vars.contains rootVar then
          let st1 := symEvalExpr st dst ty val
          symExecCode fuel' unrollBound st1 k expandRetHeap
        else
        let isScalarSlot := match val with | .ctorGetScalar _ _ _ => true | _ => false
        let flatIdx? : Option Nat :=
          if isScalarSlot then (st.ctorObjCounts.lookup rootVar).map (· + idx)
          else match st.ctorObjCounts.lookup rootVar with
            | some n => if idx < n then some idx else some (2 ^ 64)
            | none => some idx
        match cv.expr with
        | .tuple (_tag :: fs) =>
          match flatIdx?.bind (fs[·]?) with
          | some (.ite cond tBranch eBranch) =>
            let liveOk := st.isBufLive rootVar
            let stLive0 := (st.requireUbCond (st.liveRcCond rootVar)).noteExtLiveRoot rootVar
            let stLive :=
              if stLive0.allocRoots.contains rootVar then stLive0
              else stLive0.requireUbCond (.binOp .lt (.constU64 idx.toUInt64) (.ctorLen isScalarSlot stLive0.extFreeEpoch rootVar))
            let condTmp : VarId := SymExecState.desugarTmpBase stLive.synVarBase fuel'
            let tTmp : VarId := condTmp + 1
            let eTmp : VarId := condTmp + 2
            let mkBranchBind (tmpId : VarId) (bExpr : SymExpr) (curSt : SymExecState) : SymExecState × LNIRCode :=
              match bExpr with
              | .symVar rId =>
                let eff := curSt.resolveBuf rId
                (curSt, .letBind dst ty (.scalar (.var eff)) k)
              | _ =>
                let s1 := (curSt.clearAlias tmpId).bindVar tmpId
                  { expr := .tuple [bExpr], nonPoison := cv.nonPoison && liveOk, noUB := cv.noUB && liveOk }
                let s2 := s1.markTypedTuple tmpId
                (s2, .letBind dst ty (.projTuple tmpId 0) k)
            let stCond := ((stLive.clearAlias condTmp).markBoolVar condTmp).bindVar condTmp
              { expr := cond, nonPoison := cv.nonPoison && liveOk, noUB := cv.noUB && liveOk }
            let (stWithT, codeT) := mkBranchBind tTmp tBranch stCond
            let (stWithTE, codeE) := mkBranchBind eTmp eBranch stWithT
            symExecCode fuel' unrollBound stWithTE (.ite condTmp codeT codeE) expandRetHeap
          | _ =>
            let st1 := symEvalExpr st dst ty val
            symExecCode fuel' unrollBound st1 k expandRetHeap
        | _ =>
          let st1 := symEvalExpr st dst ty val
          symExecCode fuel' unrollBound st1 k expandRetHeap
      | _ =>
        let st0 :=
          match val with
          | .scalar (.var _) => st
          | _ => if callSlotKind ty == some false then st.clearAlias dst else st
        let st1 := symEvalExpr st0 dst ty val
        symExecCode fuel' unrollBound st1 k expandRetHeap
    | .rawStore ptrVar idxVar valVar elemTy k =>
      let idxSv := st.lookupVar idxVar
      let valSv := st.lookupVar valVar
      let maskedVal : SymExpr :=
        match elemTy with
        | .i1 | .i8 => normSymBinOpStep .bitAnd valSv.expr (.constU64 0xff)
        | .i16 => normSymBinOpStep .bitAnd valSv.expr (.constU64 0xffff)
        | .i32 | .f32 => normSymBinOpStep .bitAnd valSv.expr (.constU64 0xffffffff)
        | _ => valSv.expr
      let st1 := st.writeBufSym .sarray ptrVar idxSv.expr maskedVal true
      let st2 := { st1 with
        ubCond := if idxSv.noUB && valSv.noUB then st1.ubCond else .constBool false
        noUB := st1.noUB && idxSv.noUB && valSv.noUB
        nonPoison := st1.nonPoison && idxSv.nonPoison && valSv.nonPoison }
      symExecCode fuel' unrollBound st2 k expandRetHeap
    | .incRef v count k =>
      symExecCode fuel' unrollBound (st.updateRefCount v count true) k expandRetHeap
    | .decRef v count k =>
      symExecCode fuel' unrollBound (st.updateRefCount v count false) k expandRetHeap
    | .ite condVar thenBranch elseBranch =>
      let condSv := st.lookupVar condVar
      match condSv.expr with
      | .constBool true => symExecCode fuel' unrollBound st thenBranch expandRetHeap
      | .constBool false => symExecCode fuel' unrollBound st elseBranch expandRetHeap
      | .constU64 v =>
        if v != 0 then symExecCode fuel' unrollBound st thenBranch expandRetHeap
        else symExecCode fuel' unrollBound st elseBranch expandRetHeap
      | .constU256 w =>
        if w != UInt256.zero then symExecCode fuel' unrollBound st thenBranch expandRetHeap
        else symExecCode fuel' unrollBound st elseBranch expandRetHeap
      | cExprRaw =>
        let condSort := symExprScalarSort? st cExprRaw
        let condIsTypedTuple :=
          st.typedTuples.contains (st.resolveBuf condVar) ||
          (match cExprRaw with | .tuple _ => true | _ => false)
        let condIsHeapPtr :=
          st.isDefinitelyHeapRoot condVar && !(st.isImmediateScalarObj condVar)
        if condIsTypedTuple || condIsHeapPtr || st.ubCond == .constBool false then
          ({ st with noUB := false, nonPoison := false, ubCond := .constBool false }, .unit)
        else if condSort.isNone then
          (st.markUnsupported, .unit)
        else
          let cExpr : SymExpr :=
            if condSort == some sortU64 then normSymUnaryOpStep .not (normSymBinOpStep .eq cExprRaw (.constU64 0))
            else if condSort == some sortU256 then normSymUnaryOpStep .not (normSymBinOpStep .eq cExprRaw (.constU256 UInt256.zero))
            else cExprRaw
          let (stForT, stForE) := symExecItePrepare st cExpr
          let (stT, retT) := symExecCode fuel' unrollBound stForT thenBranch expandRetHeap
          let stEIn := { stForE with nextDynAllocIdx := Nat.max stForE.nextDynAllocIdx stT.nextDynAllocIdx }
          let (stE, retE) := symExecCode fuel' unrollBound stEIn elseBranch expandRetHeap
          symExecIteMerge st condSv cExpr stT retT stE retE
    | .seqFor idxVar _loVar _hiVar accVar accInit _accTy stepBody k =>
      let initRoot := st.resolveBuf accInit
      let initSv := st.lookupVar initRoot
      let stClearAcc := st.clearVarSortTags accVar
      let stInit0 :=
        if accVar == initRoot then stClearAcc
        else (stClearAcc.aliasBuf accVar initRoot).bindVar accVar {
          expr := if stClearAcc.isHeapObjectRoot initRoot then .symVar initRoot else initSv.expr
          nonPoison := initSv.nonPoison
          noUB := initSv.noUB }
      let stInit :=
        if stInit0.isNeverScalarRef initRoot then
          if stInit0.allocRoots.contains initRoot || stInit0.objPtrVars.contains initRoot then stInit0.markObjPtrVar accVar
          else if stInit0.sarrayVars.contains initRoot then stInit0.markSarrayVar accVar
          else stInit0
        else if stInit0.typedTuples.contains initRoot || (match initSv.expr with | .tuple _ => true | _ => false) then
          stInit0.markTypedTuple accVar
        else
          match symExprScalarSort? stInit0 initSv.expr with
          | some 0 => stInit0.markBoolVar accVar
          | some 1 => stInit0.markU64Var accVar
          | some 2 => stInit0.markU256Var accVar
          | _ => stInit0
      let stAfterLoop := symExecLoopUnroll loopBound 0 idxVar accVar ((stInit.clearVarSortTags idxVar).markU64Var idxVar)
        (fun s => symExecCode fuel' loopBound s stepBody false)
      symExecCode fuel' loopBound stAfterLoop k retExpand
    | .parFor outVar _lenVar inputs _elemTy _kernel k =>
      let stInputs := inputs.foldl (fun cur iv =>
        let r := cur.resolveBuf iv
        let liveC := cur.liveRcCond r
        let c1 := ((cur.noteExtRoot r).requireUbCond liveC).noteExtLiveRoot r
        { c1 with noUB := c1.noUB && liveC == .constBool true }) st
      let allocId := SymExecState.dynAllocRootId stInputs.synVarBase stInputs.nextDynAllocIdx
      let st0 := { stInputs with nextDynAllocIdx := stInputs.nextDynAllocIdx + 1 }
      let st1 := (st0.markAllocated allocId).markSarrayVar allocId
      let st2 := (((st1.clearVarSortTags outVar).aliasBuf outVar allocId).markSarrayVar outVar).bindVar outVar
        { expr := .symVar allocId, nonPoison := true, noUB := true }
      symExecCode fuel' unrollBound st2 k expandRetHeap
    | .ret v =>
      let rRoot := st.resolveBuf v
      let rSv := st.lookupVar rRoot
      let retSeed : SymExpr :=
        if st.allocRoots.contains rRoot || (!expandRetHeap && st.isHeapObjectRoot rRoot) then
          .symVar rRoot
        else match rSv.expr with
          | .tuple _ =>
            if !(st.typedTuples.contains rRoot) then
              .symVar rRoot
            else
              rSv.expr
          | _ => rSv.expr
      let finalExpr :=
        if expandRetHeap then normSymExpr (st.expandHeapExpr 16 retSeed)
        else normSymExpr retSeed
      ({ st with
          noUB := st.noUB && rSv.noUB
          nonPoison := st.nonPoison && rSv.nonPoison }, finalExpr)
    | .unreachable =>
      ({ st with reachable := false, reachCond := .constBool false }, .unit)

/-- Compute an upper bound on all SSA variable IDs occurring in `LNIRDecl` so synthetic
    projected-field and desugared-diamond IDs never collide with user SSA `VarId`s. -/
def maxScalarExprVarId : ScalarExpr → VarId
  | .constU64 _ | .constBool _ => 0
  | .var id => id
  | .binOp _ l r => Nat.max (maxScalarExprVarId l) (maxScalarExprVarId r)
  | .unaryOp _ a => maxScalarExprVarId a
  | .select c t e | .fma c t e =>
    Nat.max (maxScalarExprVarId c) (Nat.max (maxScalarExprVarId t) (maxScalarExprVarId e))

def maxLNIRExprVarId : LNIRExpr → VarId
  | .scalar se => maxScalarExprVarId se
  | .constU256 _ => 0
  | .mulDivDown a b c | .mulDivUp a b c | .storageStore a b c | .sarraySet a b c _ =>
    Nat.max a (Nat.max b c)
  | .storageLoad a b | .sarrayGet a b _ | .rawLoad a b _ => Nat.max a b
  | .mkTuple fs => fs.foldl Nat.max 0
  | .projTuple v _ | .ctorGetObj v _ | .ctorGetScalar v _ _ | .isExclusive v
  | .sarrayLen v | .sarrayDataPtr v _ | .sarrayEnsureExclusive v _
  | .boxScalar v _ | .unboxScalar v _ => v
  | .allocCtor _ os ss => (os ++ ss).foldl Nat.max 0
  | .call _ args _ _ => args.foldl Nat.max 0

def maxLNIRCodeVarId : LNIRCode → VarId
  | .letBind dst _ val k => Nat.max dst (Nat.max (maxLNIRExprVarId val) (maxLNIRCodeVarId k))
  | .rawStore p i v _ k => Nat.max p (Nat.max i (Nat.max v (maxLNIRCodeVarId k)))
  | .incRef v _ k | .decRef v _ k => Nat.max v (maxLNIRCodeVarId k)
  | .ite c t e => Nat.max c (Nat.max (maxLNIRCodeVarId t) (maxLNIRCodeVarId e))
  | .seqFor idx lo hi acc init _ step k =>
    Nat.max idx (Nat.max lo (Nat.max hi (Nat.max acc (Nat.max init
      (Nat.max (maxLNIRCodeVarId step) (maxLNIRCodeVarId k))))))
  | .parFor out len ins _ _ k =>
    Nat.max out (Nat.max len (Nat.max (ins.foldl Nat.max 0) (maxLNIRCodeVarId k)))
  | .ret v => v
  | .unreachable => 0

def declSynVarBase (d : LNIRDecl) : VarId :=
  let paramMax := d.params.foldl (fun acc p => Nat.max acc p.id) 0
  let codeMax := maxLNIRCodeVarId d.body
  Nat.max 30000 (Nat.max paramMax codeMax + 1024)

def initTupleParamExpr (d : Nat) (nextSubId : VarId) (ty : LNIRType) :
    SymExpr × VarId × List VarId × List VarId × List VarId :=
  match ty, d with
  | .i1, _ => (.symVar nextSubId, nextSubId + 1, [nextSubId], [], [])
  | .u256, _ | .i256, _ => (.symVar nextSubId, nextSubId + 1, [], [], [nextSubId])
  | .i8, _ | .i16, _ | .i32, _ | .i64, _ | .usize, _ | .f32, _ | .f64, _ =>
    (.symVar nextSubId, nextSubId + 1, [], [nextSubId], [])
  | .tuple _, 0 => (.symVar nextSubId, nextSubId + 1, [], [], [])
  | .tuple fs, d' + 1 =>
    let (fExprs, curId, bs, us, ws) := fs.foldl (fun (accE, cid, accB, accU, accW) fTy =>
      let (fe, cid', b', u', w') := initTupleParamExpr d' cid fTy
      (accE ++ [fe], cid', accB ++ b', accU ++ u', accW ++ w')) ([], nextSubId, [], [], [])
    (.tuple fExprs, curId, bs, us, ws)
  | _, _ => (.symVar nextSubId, nextSubId + 1, [], [], [])

/-- Run symbolic execution on an `LNIRDecl` with initial symbolic parameters. -/
def symExecDecl (loopUnrollBound : Nat := 4) (d : LNIRDecl) (synBaseOverride? : Option VarId := none) : SymExecSummary :=
  let synBase := synBaseOverride?.getD (declSynVarBase d)
  let initTupleBase : VarId := synBase + 256
  let (paramState, tupleEnd) : SymExecState × VarId := d.params.foldl (fun (acc, curSubId) p =>
    match p.ty with
    | .rawPtr _ =>
      ((acc.bindVar p.id { expr := .symVar p.id, nonPoison := true, noUB := true }).markExclusive p.id, curSubId)
    | .sarray _ =>
      ((acc.bindVar p.id { expr := .symVar p.id, nonPoison := true, noUB := true }).markSarrayVar p.id, curSubId)
    | .objPtr =>
      ((acc.bindVar p.id { expr := .symVar p.id, nonPoison := true, noUB := true }).markObjPtrVar p.id, curSubId)
    | .i1 =>
      ((acc.bindVar p.id { expr := .symVar p.id, nonPoison := true, noUB := true }).markBoolVar p.id, curSubId)
    | .u256 | .i256 =>
      ((acc.bindVar p.id { expr := .symVar p.id, nonPoison := true, noUB := true }).markU256Var p.id, curSubId)
    | .storageMap =>
      ((acc.bindVar p.id { expr := .symVar p.id, nonPoison := true, noUB := true }).markU256Var p.id, curSubId)
    | .i8 | .i16 | .i32 | .i64 | .usize | .f32 | .f64 =>
      ((acc.bindVar p.id { expr := .symVar p.id, nonPoison := true, noUB := true }).markU64Var p.id, curSubId)
    | .tuple _ =>
      let (tExpr, nextSubId, bIds, uIds, wIds) := initTupleParamExpr 8 curSubId p.ty
      let stT := (acc.markTypedTuple p.id).bindVar p.id { expr := tExpr, nonPoison := true, noUB := true }
      let stB := bIds.foldl (fun s bid => s.markBoolVar bid) stT
      let stU := uIds.foldl (fun s uid => s.markU64Var uid) stB
      let stW := wIds.foldl (fun s wid => s.markU256Var wid) stU
      (stW, nextSubId)
    | _ =>
      (acc.bindVar p.id { expr := .symVar p.id, nonPoison := true, noUB := true }, curSubId)
  ) ({ synVarBase := synBase + 4096 }, initTupleBase)
  let initState :=
    let base := { paramState with synVarBase := Nat.max (synBase + 4096) tupleEnd }
    if d.checkElemTypes.isSome then base.markUnsupported else base
  let (finalSt, retExpr) := symExecCode 256 loopUnrollBound initState d.body true
  let rawWrites :=
    (finalSt.memWrites.filter fun (_, r, _, _) => !(finalSt.allocRoots.contains r)).mergeSort
      (fun (sp1, r1, i1, _) (sp2, r2, i2, _) =>
        sp1.ord < sp2.ord || (sp1 == sp2 && (r1 < r2 || (r1 == r2 && reprStr i1 ≤ reprStr i2))))
  let expandedWriteExprs := rawWrites.map fun (_, _, _, val) => normSymExpr (finalSt.expandHeapExpr 16 val)
  let liveAllocRc : List SymExpr :=
    (finalSt.allocRoots.mergeSort (· < ·)).filterMap fun r =>
      let rcE := normSymExpr (finalSt.lookupRcExpr r)
      if rcE == .constU64 0 then none
      else some (normSymExpr (finalSt.expandHeapExpr 16 (.symVar r)))
  let paramRootIds : List VarId :=
    d.params.filterMap fun p =>
      match p.ty with
      | .objPtr | .taggedPtr | .sarray _ => some p.id
      | _ => none
  let externalRcRoots : List VarId :=
    ((paramRootIds ++ finalSt.extSeenRoots ++ finalSt.extRcDeltas.map Prod.fst).filter
      fun r => !(finalSt.allocRoots.contains r)).eraseDups.mergeSort (· < ·)
  let nonAllocRcDeltas : List (VarId × SymExpr) :=
    externalRcRoots.filterMap fun r =>
      let d := normSymExpr (finalSt.lookupExtRcDeltaExpr r)
      if d == .constU64 0 then none else some (r, d)
  -- Alpha-rename freshly allocated heap-root identities jointly across `(retVal, memWrites, liveAllocRc)` per
  -- feasible path (`hoistIteTupleFuel`) so cross-alias relationships between returns and escaping heap writes
  -- as well as leaked/live reference counts are preserved across every branch!
  let keyedWriteExprs := (rawWrites.zip expandedWriteExprs).map fun ((sp, r, idx, _), wVal) =>
    SymExpr.tuple [.constU64 sp.ord.toUInt64, .constU64 r.toUInt64, normSymExpr idx, wVal]
  let combinedRaw := SymExpr.tuple [normSymExpr retExpr, SymExpr.tuple keyedWriteExprs, SymExpr.tuple liveAllocRc]
  let jointHeapSummary := normSymExpr (finalSt.alphaRenameAllocTags
    (SymExecState.pruneDeadLiveAllocEntries (SymExecState.hoistIteTupleFuel 64 combinedRaw)))
  let expandedWrites := (rawWrites.zip expandedWriteExprs).map fun ((sp, r, idx, _), wVal) =>
    (sp, r, normSymExpr idx, normSymExpr (finalSt.alphaRenameAllocTags (SymExecState.hoistIteTupleFuel 16 wVal)))
  let canonRet := normSymExpr (finalSt.alphaRenameAllocTags (SymExecState.hoistIteTupleFuel 16 (normSymExpr retExpr)))
  let finalUbCond : SymExpr :=
    normSymExpr (SymExecState.hoistIteTupleFuel 16 (normSymExpr finalSt.ubCond))
  { declName := d.name
    reachable := finalSt.reachable
    reachCond := normSymExpr finalSt.reachCond
    ubCond := finalUbCond
    noUB := finalSt.noUB
    nonPoison := finalSt.nonPoison
    symUnsupported := finalSt.symUnsupported
    symExhausted := finalSt.symExhausted
    synVarBase := initState.synVarBase
    retVal := canonRet
    jointHeap := jointHeapSummary
    rcDeltas := nonAllocRcDeltas
    memWrites := expandedWrites }


end LeanNative.Proofs
