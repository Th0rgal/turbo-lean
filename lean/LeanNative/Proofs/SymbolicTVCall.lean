import LeanNative.Proofs.SymbolicTVScalar

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics

/-! ## Reference-Count & Runtime Call Symbolic Evaluation (`LeanNative.Proofs.SymbolicTVCall`) -/

namespace SymExecState

def updateRefCountFuel : Nat → SymExecState → Nat → Nat → Bool → SymExecState
  | 0, st, _, _, _ => st.markExhausted
  | fuel + 1, st, v, count, inc =>
    let root := st.resolveBuf v
    if st.isImmediateScalarObj root || st.typedTuples.contains root ||
       st.boolVars.contains root || st.u64Vars.contains root || st.u256Vars.contains root then
      st
    else if count > 0x7FFFFFFFFFFFFFFF ||
        (match st.refCounts.lookup root with
         | some rc => rc > 0x7FFFFFFFFFFFFFFF || (inc && rc + count > 0x7FFFFFFFFFFFFFFF)
         | none => false) then
      st.markUnsupported
    else if count == 0 then
      -- Concrete `incRefObj`/`decRefObjFuel`/`incRefBuf`/`decRefBuf` check heap liveness BEFORE
      -- treating `count == 0` as a no-op!
      let curRc : Option Nat :=
        match st.refCounts.lookup root with
        | some rc => some rc
        | none => if st.exclusiveBufs.contains root then some 1 else none
      match curRc with
      | some rc =>
        if rc == 0 then
          { st with noUB := false, nonPoison := false, ubCond := .constBool false, exclusiveBufs := st.exclusiveBufs.filter (· != root) }
        else st
      | none =>
        if st.isNeverScalarRef root then
          let liveC := st.liveRcCond root
          let st1 := (st.requireUbCond liveC).noteExtLiveRoot root
          { st1 with noUB := st1.noUB && liveC == .constBool true }
        else
          -- `.taggedPtr` or untyped projected child with unknown RC: may be immediate scalar (`ok`) or dead `.objPtr` (`error`)
          st.markUnsupported
    else if !(st.isNeverScalarRef root) then
      -- Non-zero RC op on `.taggedPtr` or untyped root whose scalar-vs-heap tag is not statically known
      st.markUnsupported
    else
      let curRc : Option Nat :=
        match st.refCounts.lookup root with
        | some rc => some rc
        | none => if st.exclusiveBufs.contains root then some 1 else none
      match curRc with
      | some rc =>
        if rc == 0 || (!inc && count > rc) then
          { st with noUB := false, nonPoison := false, ubCond := .constBool false, exclusiveBufs := st.exclusiveBufs.filter (· != root) }
        else
          let next := if inc then rc + count else rc - count
          let st1 : SymExecState := { st with
            refCounts := (root, next) :: st.refCounts.filter (fun (id, _) => id != root)
            rcExprs := (root, .constU64 next.toUInt64) :: st.rcExprs.filter (fun (id, _) => id != root)
            exclusiveBufs := if next == 1 then root :: st.exclusiveBufs.filter (· != root)
              else st.exclusiveBufs.filter (· != root) }
          if !inc && next == 0 then
            let st1' := (st1.bumpExternalHeapEpoch root true).addExtRcDelta root count inc
            let objCount? := st1'.ctorObjCounts.lookup root
            let childRoots : List VarId :=
              match (st1'.lookupVar root).expr with
              | .tuple (_tag :: fs) =>
                let objFs := match objCount? with | some n => fs.take n | none => fs
                objFs.filterMap fun f =>
                  match f with
                  | .symVar cid =>
                    let cRoot := st1'.resolveBuf cid
                    if st1'.allocRoots.contains cRoot || (st1'.refCounts.lookup cRoot).isSome ||
                       (st1'.rcExprs.lookup cRoot).isSome || st1'.exclusiveBufs.contains cRoot ||
                       cRoot ≥ st1'.synVarBase then
                      some cRoot
                    else match (st1'.lookupVar cRoot).expr with
                      | .symVar _ => some cRoot
                      | _ => none
                  | _ => none
              | _ => []
            childRoots.foldl (fun cur cRoot => updateRefCountFuel fuel cur cRoot 1 false) st1'
          else
            let st1' := (st1.bumpExternalHeapEpoch root false).addExtRcDelta root count inc
            if next > 0 && !st1'.allocRoots.contains root then st1'.noteExtLiveRoot root else st1'
      | none =>
        let baseExpr := st.lookupRcExpr root
        let deltaExpr := .constU64 count.toUInt64
        if inc then
          -- Concrete `HeapState.incRefObj` / `incRefBuf` check only `rc > 0` (storing unbounded `Nat`).
          -- Never narrow source `ubCond` with a synthetic 64-bit `noWrapC`; instead `addExtRcDelta`
          -- tracks cumulative external RC delta magnitude and marks `symUnsupported` if it exceeds `2^63 - 1`.
          let liveC := st.liveRcCond root
          let nextExpr := normSymBinOpStep .add baseExpr deltaExpr
          -- Snapshot `baseExpr` before bumping `heapStepEpoch` so balanced `incRef`/`decRef` on the
          -- SAME `root` still cancels in `rcExprs`, while other external roots advance to the new epoch!
          let st1 := (((st.requireUbCond liveC).noteExtLiveRoot root).bumpExternalHeapEpoch root false).addExtRcDelta root count true
          { st1 with
            noUB := st1.noUB && liveC == .constBool true
            rcExprs := (root, nextExpr) :: st1.rcExprs.filter (fun (id, _) => id != root)
            exclusiveBufs := st1.exclusiveBufs.filter (· != root) }
        else
          -- Check if `baseExpr = prev + k` with `k >= count` and `prev` live (`mayFree = false`).
          -- Otherwise `baseExpr == count` frees `root` (dropping uninspected children / borrows),
          -- which only `.sarray` buffers can model (`count <= baseExpr`, `mayFree = true`);
          -- unknown-RC freeing of `.objPtr` constructors marks `symUnsupported` (fail closed).
          let strictlyRetainsLive : Bool :=
            match baseExpr with
            | .binOp .add prev (.constU64 k) | .binOp .add (.constU64 k) prev =>
              decide (count.toUInt64 ≤ k) &&
              (st.extLivenessRoots.contains root ||
               normSymExpr (normSymIteStep st.ubCond (normSymBinOpStep .lt (.constU64 0) prev) (.constBool true)) == .constBool true)
            | _ => false
          if strictlyRetainsLive then
            let nextExpr := normSymBinOpStep .sub baseExpr deltaExpr
            let st1 := ((st.noteExtLiveRoot root).bumpExternalHeapEpoch root false).addExtRcDelta root count false
            { st1 with
              rcExprs := (root, nextExpr) :: st1.rcExprs.filter (fun (id, _) => id != root)
              exclusiveBufs := st1.exclusiveBufs.filter (· != root) }
          else if st.sarrayVars.contains root then
            let stepSafeCond := normSymBinOpStep .le deltaExpr baseExpr
            let nextExpr := normSymBinOpStep .sub baseExpr deltaExpr
            let st1 := ((st.requireUbCond stepSafeCond).bumpExternalHeapEpoch root true).addExtRcDelta root count false
            { st1 with
              noUB := st1.noUB && stepSafeCond == .constBool true
              rcExprs := (root, nextExpr) :: st1.rcExprs.filter (fun (id, _) => id != root)
              exclusiveBufs := st1.exclusiveBufs.filter (· != root) }
          else
            st.markUnsupported

def updateRefCount (st : SymExecState) (v count : Nat) (inc : Bool) : SymExecState :=
  updateRefCountFuel 32 st v count inc


end SymExecState

/-- Symbolically evaluate an `LNIRExpr.call` intrinsic or external runtime call. -/
def symEvalCallRuntime (st : SymExecState) (dst : VarId)
    (fnName : String) (args : List VarId) (retTy : LNIRType) (isExt : Bool) : SymExecState :=
    let ptrRet := callSlotKind retTy == some true
    let i64Ret := callSlotKind retTy == some false
    match isExt, args with
    | false, [a] =>
      if (fnName == "lean_native_box_u64" && ptrRet) || (fnName == "lean_native_unbox_u64" && i64Ret) then
        let r := st.resolveBuf a
        let rVal := st.lookupVar r
        let st1 :=
          if a != dst && (ptrRet || st.isHeapObjectRoot r) then st.aliasBuf dst r
          else if !ptrRet && !(st.isHeapObjectRoot r) then st.clearAlias dst
          else st
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
      else if fnName == "lean_native_ensure_exclusive" && ptrRet then
        let root := st.resolveBuf a
        let rVal := st.lookupVar root
        if st.sarrayVars.contains root then
          let liveC := st.liveRcCond root
          let stLive := ((st.noteExtRoot root).requireUbCond liveC).noteExtLiveRoot root
          let stBound := (((stLive.markExclusive root).aliasBuf dst root).markSarrayVar dst).bindVar dst
            { expr := .symVar root, nonPoison := rVal.nonPoison, noUB := rVal.noUB }
          { stBound with noUB := stBound.noUB && liveC == .constBool true }
        else if st.objPtrVars.contains root || (st.allocRoots.contains root && !(st.sarrayVars.contains root)) then
          let stA := (if a != dst then st.aliasBuf dst root else st).markObjPtrVar dst
          stA.bindVar dst { expr := .symVar root, nonPoison := rVal.nonPoison, noUB := rVal.noUB }
        else if st.typedTuples.contains root || (match rVal.expr with | .tuple _ => true | _ => false) then
          (st.clearAlias dst).markTypedTuple dst |>.bindVar dst rVal
        else if st.isImmediateScalarObj root || st.boolVars.contains root ||
                st.u64Vars.contains root || st.u256Vars.contains root then
          let stClear := (st.clearAlias dst).unmarkTypedTuple dst
          let stSorted :=
            match symExprScalarSort? stClear rVal.expr with
            | some 0 => stClear.markBoolVar dst
            | some 1 => stClear.markU64Var dst
            | some 2 => stClear.markU256Var dst
            | _ => stClear
          stSorted.bindVar dst rVal
        else
          (((st.clearAlias dst).unmarkTypedTuple dst).markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
      else if fnName == "lean_native_sarray_len" && i64Ret then
        let root := st.resolveBuf a
        let sa := st.lookupVar a
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
      else if fnName == "lean_native_ctor_tag" && i64Ret then
        let root := st.resolveBuf a
        let sa0 := st.lookupVar root
        let stOut := st.markU64Var dst
        if st.u256Vars.contains root || st.sarrayVars.contains root then
          stOut.bindVar dst { expr := .unit, nonPoison := false, noUB := false }
        else if st.u64Vars.contains root then
          stOut.bindVar dst { expr := sa0.expr, nonPoison := sa0.nonPoison, noUB := sa0.noUB }
        else if st.boolVars.contains root then
          let bExpr := normSymIteStep sa0.expr (.constU64 1) (.constU64 0)
          stOut.bindVar dst { expr := bExpr, nonPoison := sa0.nonPoison, noUB := sa0.noUB }
        else if st.isImmediateScalarObj root then
          match sa0.expr with
          | .constU64 tag =>
            stOut.bindVar dst { expr := .constU64 tag, nonPoison := sa0.nonPoison, noUB := sa0.noUB }
          | .constBool b =>
            stOut.bindVar dst { expr := .constU64 (if b then 1 else 0), nonPoison := sa0.nonPoison, noUB := sa0.noUB }
          | .constU256 _ | .unit =>
            -- Concrete `evalExpr` rejects `.u256` and `.unit` in `lean_native_ctor_tag` (`typeError`)!
            stOut.bindVar dst { expr := .unit, nonPoison := false, noUB := false }
          | _ =>
            (stOut.markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
        else
          match sa0.expr with
          | .tuple [] =>
            stOut.bindVar dst { expr := .unit, nonPoison := false, noUB := false }
          | .tuple (tag :: _) =>
            if st.typedTuples.contains root then
              match symExprScalarSort? st tag with
              | some 1 =>
                stOut.bindVar dst { expr := tag, nonPoison := sa0.nonPoison, noUB := sa0.noUB }
              | some 0 | some 2 =>
                stOut.bindVar dst { expr := .unit, nonPoison := false, noUB := false }
              | _ =>
                (stOut.markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
            else
              let liveOk := st.isBufLive root
              let liveC := st.liveRcCond root
              let stLive := ((st.requireUbCond liveC).noteExtLiveRoot root).markU64Var dst
              let sa := stLive.lookupVar root
              let stBound := stLive.bindVar dst { expr := tag, nonPoison := sa.nonPoison && liveOk, noUB := sa.noUB && liveOk }
              { stBound with noUB := stBound.noUB && liveC == .constBool true }
          | .symVar rootId =>
            if st.objPtrVars.contains root || st.allocRoots.contains root ||
               (st.refCounts.lookup root).isSome || (st.rcExprs.lookup root).isSome ||
               st.exclusiveBufs.contains root then
              let liveOk := st.isBufLive root
              let liveC := st.liveRcCond root
              let stLive := ((st.requireUbCond liveC).noteExtLiveRoot root).markU64Var dst
              let sa := stLive.lookupVar root
              let eff := stLive.resolveBuf rootId
              let stBound := stLive.bindVar dst {
                expr := .ctorTag stLive.heapStepEpoch eff
                nonPoison := sa.nonPoison && liveOk, noUB := sa.noUB && liveOk }
              { stBound with noUB := stBound.noUB && liveC == .constBool true }
            else
              -- `.taggedPtr` or untyped projected child may hold an immediate scalar tag or a heap `.objPtr`!
              (stOut.markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
          | _ =>
            (stOut.markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
      else (st.markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    | false, [objVar, tagVar] =>
      if fnName == "lean_native_ctor_set_tag" && retTy == .unit then
        let root := st.resolveBuf objVar
        let tagRoot := st.resolveBuf tagVar
        let objSv := st.lookupVar root
        let tagSv := st.lookupVar tagVar
        let tagSort := symExprScalarSort? st tagSv.expr
        if st.typedTuples.contains root || st.sarrayVars.contains root ||
           st.boolVars.contains root || st.u64Vars.contains root || st.u256Vars.contains root ||
           st.typedTuples.contains tagRoot || st.isDefinitelyHeapRoot tagRoot ||
           st.boolVars.contains tagRoot || st.u256Vars.contains tagRoot ||
           tagSort == some sortBool || tagSort == some sortU256 then
          ((st.clearAlias dst).unmarkTypedTuple dst).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
        else if !(st.objPtrVars.contains root || st.allocRoots.contains root ||
                  (st.refCounts.lookup root).isSome || (st.rcExprs.lookup root).isSome ||
                  st.exclusiveBufs.contains root) || tagSort != some sortU64 then
          (((st.clearAlias dst).unmarkTypedTuple dst).markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
        else
          let exclOk := st.isBufExclusive root
          let stExcl := st.requireUbCond (st.exclRcCond root)
          let operandsOk := objSv.noUB && tagSv.noUB
          let (updatedState, tagOk) : SymExecState × Bool :=
            match objSv.expr with
            | .tuple [] =>
              ({ stExcl with noUB := false, nonPoison := false, ubCond := .constBool false }, false)
            | .tuple (_oldTag :: fs) =>
              let sb := stExcl.bindVar root {
                expr := .tuple (tagSv.expr :: fs)
                nonPoison := objSv.nonPoison && tagSv.nonPoison
                noUB := operandsOk }
              ({ sb with ubCond := if operandsOk then stExcl.ubCond else .constBool false }, true)
            | .symVar rootId =>
              let effRoot := stExcl.resolveBuf rootId
              let prevFields := (List.range 16).map fun i =>
                SymExpr.symVar (SymExecState.projFieldRootId stExcl.synVarBase stExcl.heapStepEpoch effRoot i)
              let stBnd : SymExecState :=
                { stExcl with ctorObjCounts := (root, 8) :: stExcl.ctorObjCounts.filter (·.1 != root) }
              let sb := stBnd.bindVar root {
                expr := .tuple (tagSv.expr :: prevFields)
                nonPoison := objSv.nonPoison && tagSv.nonPoison
                noUB := operandsOk }
              ({ sb with ubCond := if operandsOk then stBnd.ubCond else .constBool false }, true)
            | .constU64 _ | .constU256 _ | .constBool _ | .unit =>
              ({ stExcl with noUB := false, nonPoison := false, ubCond := .constBool false }, false)
            | _ =>
              (stExcl.markUnsupported, false)
          let stAfterEpoch :=
            if tagOk && !updatedState.allocRoots.contains root then
              let nextEp := updatedState.heapStepEpoch + 1
              let refreshedVars :=
                let keepVar (vid : VarId) : Bool :=
                  vid == root || updatedState.allocRoots.contains vid ||
                  updatedState.typedTuples.contains vid || vid < updatedState.synVarBase
                (updatedState.vars.filter (keepVar ·.1)).map fun (vid, sv) =>
                    if vid == root || updatedState.allocRoots.contains vid || updatedState.typedTuples.contains vid then (vid, sv)
                    else match sv.expr with
                      | .tuple _ => (vid, { sv with expr := .symVar vid })
                      | _ => (vid, sv)
              { (updatedState.bumpExternalHeapEpoch root false) with heapStepEpoch := nextEp, vars := refreshedVars }
            else updatedState
          let stWithWrite :=
            if tagOk then stAfterEpoch.writeBufSym .ctorTag root (.constU64 0) tagSv.expr true
            else stAfterEpoch
          let stDone := (stWithWrite.clearAlias dst).unmarkTypedTuple dst |>.bindVar dst {
            expr := .unit
            nonPoison := objSv.nonPoison && tagSv.nonPoison && tagOk
            noUB := operandsOk && tagOk }
          { stDone with
            ubCond := if operandsOk && tagOk then stWithWrite.ubCond else .constBool false
            noUB := stDone.noUB && exclOk }
      else (st.markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    | false, [objVar, idxVar, valVar] =>
      if (fnName == "lean_native_ctor_set" || fnName == "lean_native_ctor_set_scalar") && retTy == .unit then
        let root := st.resolveBuf objVar
        let idxRoot := st.resolveBuf idxVar
        if st.typedTuples.contains root || st.sarrayVars.contains root ||
           st.boolVars.contains root || st.u64Vars.contains root || st.u256Vars.contains root ||
           st.typedTuples.contains idxRoot || st.isDefinitelyHeapRoot idxRoot ||
           st.boolVars.contains idxRoot || st.u256Vars.contains idxRoot then
          ((st.clearAlias dst).unmarkTypedTuple dst).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
        else if !(st.objPtrVars.contains root || st.allocRoots.contains root ||
                  (st.refCounts.lookup root).isSome || (st.rcExprs.lookup root).isSome ||
                  st.exclusiveBufs.contains root) then
          (((st.clearAlias dst).unmarkTypedTuple dst).markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
        else
        -- C1.1/C4.2: `ctor_set_scalar i` writes `scalarFields[i]` = flat slot `|objFields| + i`; unknown split fails closed
        let isScalarSet := fnName == "lean_native_ctor_set_scalar"
        let writeSpace : MemWriteSpace := if isScalarSet then .ctorScalar else .ctorObj
        let shift? : Option Nat := if isScalarSet then st.ctorObjCounts.lookup root else some 0
        let objSv := st.lookupVar root
        let idxSv := st.lookupVar idxVar
        let valRoot := st.resolveBuf valVar
        let valSvRaw := st.lookupVar valVar
        -- C5.2: `writeHeapObjFieldExclusive` rejects object-slot values whose `Val.wfField` is false (owning tuples);
        -- fail closed if a typed tuple could carry an owning edge or unresolved runtime value.
        let valWfUncertain : Bool :=
          !isScalarSet && (st.typedTuples.contains valRoot || (match valSvRaw.expr with | .tuple _ => true | _ => false))
        if valWfUncertain then
          (((st.clearAlias dst).unmarkTypedTuple dst).markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
        else
        let storedValExpr : SymExpr :=
          if st.isHeapObjectRoot valRoot then .symVar valRoot
          else match (st.lookupVar valRoot).expr with
            | .symVar rId => .symVar (st.resolveBuf rId)
            | _ => valSvRaw.expr
        let valSv := { valSvRaw with expr := storedValExpr }
        let exclOk := st.isBufExclusive root
        let stExcl := st.requireUbCond (st.exclRcCond root)
        let operandsOk := objSv.noUB && idxSv.noUB && valSv.noUB
        let (updatedState, inBoundsOk) : SymExecState × Bool :=
          match objSv.expr, idxSv.expr with
          | .tuple (tag :: fs), .constU64 idxU64 =>
            let idx := (shift?.getD 0) + idxU64.toNat
            -- an object write past `|objFields|` must never land in the scalar space
            let objLimit := if isScalarSet then fs.length else (st.ctorObjCounts.lookup root).getD fs.length
            if shift?.isNone then (stExcl.markUnsupported, false)
            else if idx < fs.length && idx < objLimit then
              let stBnd :=
                if stExcl.allocRoots.contains root then stExcl
                else stExcl.requireUbCond (.binOp .lt (.constU64 idxU64) (.ctorLen isScalarSet stExcl.extFreeEpoch root))
              let sb := stBnd.bindVar root {
                expr := .tuple (tag :: fs.set idx valSv.expr)
                nonPoison := objSv.nonPoison && idxSv.nonPoison && valSv.nonPoison
                noUB := operandsOk }
              ({ sb with ubCond := if operandsOk then stBnd.ubCond else .constBool false }, true)
            else if stExcl.allocRoots.contains root then
              ({ stExcl with noUB := false, nonPoison := false, ubCond := .constBool false }, false)
            else
              (stExcl.markUnsupported, false)
          | .symVar rootId, .constU64 idxU64 =>
            let idx := idxU64.toNat
            if idx < 8 then
              let effRoot := stExcl.resolveBuf rootId
              let stBnd := stExcl.requireUbCond (.binOp .lt (.constU64 idxU64) (.ctorLen isScalarSet stExcl.extFreeEpoch effRoot))
              -- external-root snapshot: object slots 0..7, then scalar slots at 8..15 (same synthetic roots as
              -- `ctorGetScalar` on a `.symVar` root), recorded via `ctorObjCounts root = 8` (C1.1 separate spaces)
              let target := if isScalarSet then 8 + idx else idx
              let prevFields := (List.range 16).map fun i =>
                if i == target then valSv.expr
                else .symVar (SymExecState.projFieldRootId stBnd.synVarBase stBnd.heapStepEpoch effRoot i)
              let stBnd : SymExecState :=
                { stBnd with ctorObjCounts := (root, 8) :: stBnd.ctorObjCounts.filter (·.1 != root) }
              let sb := stBnd.bindVar root {
                expr := .tuple (.ctorTag stBnd.heapStepEpoch effRoot :: prevFields)
                nonPoison := objSv.nonPoison && idxSv.nonPoison && valSv.nonPoison
                noUB := operandsOk }
              ({ sb with ubCond := if operandsOk then stBnd.ubCond else .constBool false }, true)
            else
              (stExcl.markUnsupported, false)
          | .constU64 _, _ | .constU256 _, _ | .constBool _, _ | .unit, _ =>
            -- Definite non-heap immediate passed to `lean_native_ctor_set`: concrete UB (`typeError`)!
            ({ stExcl with noUB := false, nonPoison := false, ubCond := .constBool false }, false)
          | _, _ =>
            (stExcl.markUnsupported, false)
        let stAfterEpoch :=
          if inBoundsOk && !updatedState.allocRoots.contains root then
            let nextEp := updatedState.heapStepEpoch + 1
            -- Also reset cached `.tuple` constructor snapshots on OTHER non-allocated roots (`vid < synVarBase`)
            -- back to `.symVar vid`, because another input/projected object may alias `root`!
            let refreshedVars :=
              let keepVar (vid : VarId) : Bool :=
                vid == root || updatedState.allocRoots.contains vid ||
                updatedState.typedTuples.contains vid || vid < updatedState.synVarBase
              (updatedState.vars.filter (keepVar ·.1)).map fun (vid, sv) =>
                  if vid == root || updatedState.allocRoots.contains vid || updatedState.typedTuples.contains vid then (vid, sv)
                  else match sv.expr with
                    | .tuple _ => (vid, { sv with expr := .symVar vid })
                    | _ => (vid, sv)
            -- Note: `writeHeapObjFieldExclusive` (`Semantics/Value.lean:353`) overwrites `o.objFields[idx]` or
            -- `o.scalarFields[idx]` in place WITHOUT decrementing or freeing any heap object (`mayFree = false`;
            -- LCNF emits an explicit `decRef` for the old field before `ctor_set`).
            { (updatedState.bumpExternalHeapEpoch root false) with heapStepEpoch := nextEp, vars := refreshedVars }
          else updatedState
        let stWithWrite :=
          if inBoundsOk then stAfterEpoch.writeBufSym writeSpace root idxSv.expr valSv.expr true
          else stAfterEpoch
        let stDone := (stWithWrite.clearAlias dst).unmarkTypedTuple dst |>.bindVar dst {
          expr := .unit
          nonPoison := objSv.nonPoison && idxSv.nonPoison && valSv.nonPoison && inBoundsOk
          noUB := operandsOk && inBoundsOk }
        { stDone with ubCond := if operandsOk && inBoundsOk then stWithWrite.ubCond else .constBool false, noUB := stDone.noUB && exclOk }
      else (st.markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    | _, _ => (st.markUnsupported).bindVar dst { expr := .unit, nonPoison := false, noUB := false }

end LeanNative.Proofs
