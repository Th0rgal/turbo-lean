import LeanNative.Proofs.SymbolicTVState

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics

/-! ## Scalar Symbolic Evaluation & Sort Tracking (`LeanNative.Proofs.SymbolicTVScalar`) -/

/-- Exact scalar value sort in `Val` (`0` = `.bool`, `1` = `.u64`, `2` = `.u256`)
    so width-sensitive arithmetic (64-bit vs 256-bit) and mixed-width `evalBinOp` checks are exact! -/
def sortBool : Nat := 0
def sortU64  : Nat := 1
def sortU256 : Nat := 2

def symExprScalarSort? (st : SymExecState) : SymExpr → Option Nat
  | .constBool _ => some sortBool
  | .constU64 _ | .rcSym _ _ | .ctorTag _ _ | .ctorLen _ _ _ | .sarrayLen _ => some sortU64
  | .constU256 _ | .mulDiv256 _ _ _ _ => some sortU256
  | .bufElem .sarray b _ => if st.u256Vars.contains b then some sortU256 else some sortU64
  | .bufElem .ctorScalar _ _ | .bufElem .ctorTag _ _ => some sortU64
  | .bufElem .ctorObj _ _ => none
  | .symVar id =>
    if st.boolVars.contains id then some sortBool
    else if st.u64Vars.contains id then some sortU64
    else if st.u256Vars.contains id then some sortU256
    else none
  | .binOp op l r =>
    if op == .eq || op == .lt || op == .le then some sortBool
    else if op == .addChecked256 || op == .subChecked256 || op == .mulChecked256 then some sortU256
    else if op == .clmul64 || op == .clmul64Hi || op == .gf2Affine || op == .eor3 then some sortU64
    else
      match symExprScalarSort? st l, symExprScalarSort? st r with
      | some 2, _ | _, some 2 => some sortU256
      | some 1, some 1 => some sortU64
      | _, _ => none
  | .unaryOp .not a => symExprScalarSort? st a
  | .unaryOp .neg a => symExprScalarSort? st a
  | .unaryOp .clz256 _ => some sortU256
  | .ite _ t e =>
    let stT := symExprScalarSort? st t
    let stE := symExprScalarSort? st e
    if stT == stE then stT else none
  | _ => none

/-- Result of pure `ScalarExpr` symbolic evaluation, tracking `unsupported` and `ubCond` separately from `noUB`. -/
structure SymScalarRes where
  val         : SymStateVal
  ubCond      : SymExpr := .constBool true
  unsupported : Bool := false
  deriving Repr, Inhabited, BEq

/-- Honor `evalBinOp`'s exact concrete identity/idempotence cases before sort-based UB checks. -/
def symBinOpIdentityShortCircuit? (op : BinOp) (l r : SymExpr) : Option SymExpr :=
  match op, l, r with
  | .add, x, .constU64 0 | .add, .constU64 0, x
  | .sub, x, .constU64 0
  | .mul, x, .constU64 1 | .mul, .constU64 1, x
  | .div, x, .constU64 1
  | .bitOr, x, .constU64 0 | .bitOr, .constU64 0, x
  | .bitXor, x, .constU64 0 | .bitXor, .constU64 0, x
  | .shl, x, .constU64 0
  | .shr, x, .constU64 0 => some x
  | .bitAnd, x, y | .bitOr, x, y => if x == y then some x else none
  | _, _, _ => none

/-- Symbolically evaluate a pure `ScalarExpr` with full sort & width tracking (`SymScalarRes`). -/
def symEvalScalarRes (st : SymExecState) : ScalarExpr → SymScalarRes
  | .constU64 v => { val := { expr := .constU64 v, nonPoison := true, noUB := true } }
  | .constBool b => { val := { expr := .constBool b, nonPoison := true, noUB := true } }
  | .var id =>
    let sv := st.lookupVar id
    { val := sv, ubCond := if sv.noUB then .constBool true else .constBool false }
  | .binOp op lhs rhs =>
    let rl := symEvalScalarRes st lhs
    let rr := symEvalScalarRes st rhs
    let sl := rl.val
    let sr := rr.val
    let baseUbCond := SymExecState.conjoinUbCond rl.ubCond rr.ubCond
    let mkOk (e : SymExpr) (extraUb : SymExpr := .constBool true) (extraNoUB : Bool := true) : SymScalarRes :=
      let okNoUB := sl.noUB && sr.noUB && extraNoUB
      { val := { expr := e, nonPoison := sl.nonPoison && sr.nonPoison, noUB := okNoUB }
        ubCond := SymExecState.conjoinUbCond baseUbCond extraUb }
    if rl.unsupported || rr.unsupported then
      { val := { expr := .unit, nonPoison := false, noUB := false }, ubCond := .constBool false, unsupported := true }
    else if rl.ubCond == .constBool false || rr.ubCond == .constBool false then
      { val := { expr := .unit, nonPoison := false, noUB := false }, ubCond := .constBool false }
    else
      match symBinOpIdentityShortCircuit? op sl.expr sr.expr with
      | some idExpr => mkOk idExpr
      | none =>
        let sortL := symExprScalarSort? st sl.expr
        let sortR := symExprScalarSort? st sr.expr
        let isConstLiteral : SymExpr → Bool
          | .constU64 _ | .constU256 _ | .constBool _ => true
          | _ => false
        let mayMatchIdentityRuntime : Bool :=
          match op with
          | .add | .bitOr | .bitXor =>
            (sortL != sortR || sortL == some sortBool) &&
            ((sortR == some sortU64 && !isConstLiteral sr.expr) ||
             (sortL == some sortU64 && !isConstLiteral sl.expr))
          | .sub | .shl | .shr =>
            (sortL != sortR || sortL == some sortBool) &&
            (sortR == some sortU64 && !isConstLiteral sr.expr)
          | .mul =>
            (sortL != sortR || sortL == some sortBool) &&
            ((sortR == some sortU64 && !isConstLiteral sr.expr) ||
             (sortL == some sortU64 && !isConstLiteral sl.expr))
          | .div =>
            (sortL != sortR || sortL == some sortBool) &&
            (sortR == some sortU64 && !isConstLiteral sr.expr)
          | .bitAnd =>
            sortL.isSome && sortR.isSome &&
            !(sortL == some sortU64 && sortR == some sortU64) &&
            !(sortL == some sortU256 && sortR == some sortU256) &&
            sortL == sortR && (!isConstLiteral sl.expr || !isConstLiteral sr.expr)
          | _ => false
        let mayMatchBoolBitOrRuntime : Bool :=
          op == .bitOr && sortL.isSome && sortR.isSome &&
          !(sortL == some sortU64 && sortR == some sortU64) &&
          !(sortL == some sortU256 && sortR == some sortU256) &&
          sortL == sortR && (!isConstLiteral sl.expr || !isConstLiteral sr.expr)
        let isChecked256Op := op == .addChecked256 || op == .subChecked256 || op == .mulChecked256
        let isU64OnlyIntrinsic := op == .clmul64 || op == .clmul64Hi || op == .gf2Affine || op == .eor3
        if isChecked256Op then
          -- `addChecked256`/`subChecked256`/`mulChecked256` accept `.u64`/`.u256`, reject `.bool`, and trap on 256-bit overflow/underflow!
          if sortL == some sortBool || sortR == some sortBool then
            { val := { expr := .unit, nonPoison := false, noUB := false }, ubCond := .constBool false }
          else if sortL.isNone || sortR.isNone then
            { val := { expr := .unit, nonPoison := false, noUB := false }, ubCond := .constBool false, unsupported := true }
          else
            let toW256? : SymExpr → Option UInt256
              | .constU256 w => some w
              | .constU64 x => some (UInt256.ofUInt64 x)
              | _ => none
            match toW256? sl.expr, toW256? sr.expr with
            | some wa, some wb =>
              let checkedOpt :=
                match op with
                | .addChecked256 => UInt256.addChecked wa wb
                | .subChecked256 => UInt256.subChecked wa wb
                | _ => UInt256.mulChecked wa wb
              match checkedOpt with
              | some resW => mkOk (.constU256 resW)
              | none => { val := { expr := .unit, nonPoison := false, noUB := false }, ubCond := .constBool false }
            | _, _ =>
              -- Promote `.constU64` operands to `.constU256` in symbolic checked256 expressions and record overflow guard in `ubCond`!
              let lift256 (e : SymExpr) : SymExpr := match e with | .constU64 x => .constU256 (UInt256.ofUInt64 x) | _ => e
              let l256 := lift256 sl.expr
              let r256 := lift256 sr.expr
              let ovfCond : SymExpr :=
                match op with
                | .subChecked256 => normSymBinOpStep .le r256 l256
                | .addChecked256 => normSymBinOpStep .le l256 (normSymBinOpStep .sub (.constU256 UInt256.max) r256)
                | _ => .binOp .le (.binOp .mulChecked256 l256 r256) (.constU256 UInt256.max)
              mkOk (normSymBinOpStep op l256 r256 false) ovfCond false
        else if isU64OnlyIntrinsic then
          if sortL == some sortU64 && sortR == some sortU64 then
            mkOk (normSymBinOpStep op sl.expr sr.expr true)
          else if sortL.isNone || sortR.isNone then
            { val := { expr := .unit, nonPoison := false, noUB := false }, ubCond := .constBool false, unsupported := true }
          else
            { val := { expr := .unit, nonPoison := false, noUB := false }, ubCond := .constBool false }
        else
          -- Standard `evalBinOp` operators (`.eq`, `.lt`, `.le`, `.add`, `.sub`, `.mul`, `.div`, `.mod`,
          -- `.shl`, `.shr`, `.sar`, `.bitAnd`, `.bitOr`, `.bitXor`) require identical operand sorts
          -- (`u64 == u64`, `u256 == u256`, and `bool == bool` only for `.eq`) once identity short-circuits fail!
          let definiteTypeUB : Bool :=
            !mayMatchIdentityRuntime && !mayMatchBoolBitOrRuntime &&
            ((sortL.isSome && sortR.isSome && sortL != sortR) ||
             (op != .eq && (sortL == some sortBool || sortR == some sortBool)))
          let uncertainType : Bool :=
            mayMatchIdentityRuntime || mayMatchBoolBitOrRuntime ||
            (!definiteTypeUB && (sortL.isNone || sortR.isNone))
          if uncertainType then
            { val := { expr := .unit, nonPoison := false, noUB := false }, ubCond := .constBool false, unsupported := true }
          else if definiteTypeUB then
            { val := { expr := .unit, nonPoison := false, noUB := false }, ubCond := .constBool false }
          else if sortL == some sortU256 && (op == .div || op == .mod) then
            -- `evalBinOp` on `.u256` traps (`.divisionByZero`) when `rhs == 0`!
            match sl.expr, sr.expr with
            | _, .constU256 w =>
              if w == UInt256.zero then
                { val := { expr := .unit, nonPoison := false, noUB := false }, ubCond := .constBool false }
              else
                match sl.expr with
                | .constU256 wa =>
                  let qOpt := if op == .div then UInt256.div wa w else UInt256.mod wa w
                  match qOpt with
                  | some qw => mkOk (.constU256 qw)
                  | none => { val := { expr := .unit, nonPoison := false, noUB := false }, ubCond := .constBool false }
                | _ => mkOk (normSymBinOpStep op sl.expr sr.expr false)
            | _, _ =>
              let nzCond := normSymUnaryOpStep .not (normSymBinOpStep .eq sr.expr (.constU256 UInt256.zero))
              mkOk (normSymBinOpStep op sl.expr sr.expr false) nzCond false
          else
            let w64Safe := sortL == some sortU64 && sortR == some sortU64
            mkOk (normSymBinOpStep op sl.expr sr.expr w64Safe)
  | .unaryOp op arg =>
    let ra := symEvalScalarRes st arg
    let sa := ra.val
    let sortA := symExprScalarSort? st sa.expr
    let definiteNegUB := (op == .neg || op == .clz256) && sortA == some sortBool
    let uncertainUnary := (op == .neg || op == .not || op == .clz256) && sortA.isNone
    if ra.unsupported || uncertainUnary then
      { val := { expr := .unit, nonPoison := false, noUB := false }, ubCond := .constBool false, unsupported := true }
    else if ra.ubCond == .constBool false || definiteNegUB then
      { val := { expr := .unit, nonPoison := false, noUB := false }, ubCond := .constBool false }
    else
      { val := { expr := normSymUnaryOpStep op sa.expr
                 nonPoison := sa.nonPoison
                 noUB := sa.noUB }
        ubCond := ra.ubCond }
  | .select cond t e =>
    let rc := symEvalScalarRes st cond
    let rt := symEvalScalarRes st t
    let re := symEvalScalarRes st e
    let sc := rc.val
    let sthen := rt.val
    let selse := re.val
    let mkBranch (r : SymScalarRes) : SymScalarRes :=
      if rc.unsupported || r.unsupported then
        { val := { expr := .unit, nonPoison := false, noUB := false }, ubCond := .constBool false, unsupported := true }
      else
        { val := { expr := r.val.expr, nonPoison := sc.nonPoison && r.val.nonPoison, noUB := sc.noUB && r.val.noUB }
          ubCond := SymExecState.conjoinUbCond rc.ubCond r.ubCond }
    match sc.expr with
    | .constBool true => mkBranch rt
    | .constBool false => mkBranch re
    | .constU64 n => if n != 0 then mkBranch rt else mkBranch re
    | .constU256 w => if w != UInt256.zero then mkBranch rt else mkBranch re
    | _ =>
      let condSort := symExprScalarSort? st sc.expr
      let condIsTypedTuple :=
        match cond with
        | .var cid => st.typedTuples.contains (st.resolveBuf cid)
        | _ => match sc.expr with | .tuple _ => true | _ => false
      let condIsHeapPtr :=
        match cond with
        | .var cid => st.isDefinitelyHeapRoot cid && !(st.isImmediateScalarObj cid)
        | _ => false
      let condBadSort := condSort.isNone && !condIsTypedTuple && !condIsHeapPtr
      if rc.unsupported || rt.unsupported || re.unsupported || condBadSort then
        { val := { expr := .unit, nonPoison := false, noUB := false }, ubCond := .constBool false, unsupported := true }
      else if rc.ubCond == .constBool false || condIsTypedTuple || condIsHeapPtr then
        -- `evalScalarExpr` rejects `.tuple` and `.objPtr`/`.sarrayId` as `select` conditions (`typeError`)!
        { val := { expr := .unit, nonPoison := false, noUB := false }, ubCond := .constBool false }
      else if rt.ubCond == .constBool false && re.ubCond == .constBool false then
        { val := { expr := .unit, nonPoison := false, noUB := false }, ubCond := .constBool false }
      else
        let cPred : SymExpr :=
          if condSort == some sortU64 then normSymUnaryOpStep .not (normSymBinOpStep .eq sc.expr (.constU64 0))
          else if condSort == some sortU256 then normSymUnaryOpStep .not (normSymBinOpStep .eq sc.expr (.constU256 UInt256.zero))
          else sc.expr
        let selUb := SymExecState.conjoinUbCond rc.ubCond (normSymIteStep cPred rt.ubCond re.ubCond)
        { val := { expr := normSymIteStep cPred sthen.expr selse.expr
                   nonPoison := sc.nonPoison && sthen.nonPoison && selse.nonPoison
                   noUB := sc.noUB && sthen.noUB && selse.noUB }
          ubCond := selUb }
  | .fma a b c =>
    -- Canonicalize FMA `a * b + c` through the checked symbolic `mul`/`add` handlers so concrete
    -- identity cases (`true * 1 + 0 -> true`), 64-bit vs 256-bit widths, and sort mismatches stay exact!
    let aRes := symEvalScalarRes st a
    let bRes := symEvalScalarRes st b
    let cRes := symEvalScalarRes st c
    let isConstLit : SymExpr → Bool
      | .constU64 _ | .constU256 _ | .constBool _ => true
      | _ => false
    if aRes.unsupported || bRes.unsupported || cRes.unsupported then
      { val := { expr := .unit, nonPoison := false, noUB := false }, ubCond := .constBool false, unsupported := true }
    else if aRes.ubCond == .constBool false || bRes.ubCond == .constBool false || cRes.ubCond == .constBool false then
      { val := { expr := .unit, nonPoison := false, noUB := false }, ubCond := .constBool false }
    else
      let baseUb := SymExecState.conjoinUbCond aRes.ubCond (SymExecState.conjoinUbCond bRes.ubCond cRes.ubCond)
      let baseNoUB := aRes.val.noUB && bRes.val.noUB && cRes.val.noUB
      let sa := aRes.val.expr
      let sb := bRes.val.expr
      let sc := cRes.val.expr
      let sortA := symExprScalarSort? st sa
      let sortB := symExprScalarSort? st sb
      let sortC := symExprScalarSort? st sc
      let mulIdentL := sa == .constU64 1
      let mulIdentR := sb == .constU64 1
      let mulIdent := mulIdentL || mulIdentR
      let mulMayMatchRuntime :=
        !mulIdent && (sortA != sortB || sortA == some sortBool) &&
        ((sortB == some sortU64 && !isConstLit sb) || (sortA == some sortU64 && !isConstLit sa))
      let mulDefUB :=
        !mulIdent && !mulMayMatchRuntime &&
        ((sortA.isSome && sortB.isSome && sortA != sortB) || sortA == some sortBool || sortB == some sortBool)
      let mulUncertain := !mulIdent && !mulDefUB && (mulMayMatchRuntime || sortA.isNone || sortB.isNone)
      if mulUncertain then
        { val := { expr := .unit, nonPoison := false, noUB := false }, ubCond := .constBool false, unsupported := true }
      else if mulDefUB then
        { val := { expr := .unit, nonPoison := false, noUB := false }, ubCond := .constBool false }
      else
        let mulW64 := sortA == some sortU64 && sortB == some sortU64
        let mulExpr := if mulIdentL then sb else if mulIdentR then sa else normSymBinOpStep .mul sa sb mulW64
        let mulSort := if mulIdentL then sortB else if mulIdentR then sortA else sortA
        let addIdentL := mulExpr == .constU64 0
        let addIdentR := sc == .constU64 0
        let addIdent := addIdentL || addIdentR
        let addMayMatchRuntime :=
          !addIdent && (mulSort != sortC || mulSort == some sortBool) &&
          ((sortC == some sortU64 && !isConstLit sc) || (mulSort == some sortU64 && !isConstLit mulExpr))
        let addDefUB :=
          !addIdent && !addMayMatchRuntime &&
          ((mulSort.isSome && sortC.isSome && mulSort != sortC) || mulSort == some sortBool || sortC == some sortBool)
        let addUncertain := !addIdent && !addDefUB && (addMayMatchRuntime || mulSort.isNone || sortC.isNone)
        if addUncertain then
          { val := { expr := .unit, nonPoison := false, noUB := false }, ubCond := .constBool false, unsupported := true }
        else if addDefUB then
          { val := { expr := .unit, nonPoison := false, noUB := false }, ubCond := .constBool false }
        else
          let addW64 := mulSort == some sortU64 && sortC == some sortU64
          let addExpr := if addIdentL then sc else if addIdentR then mulExpr else normSymBinOpStep .add mulExpr sc addW64
          { val := { expr := addExpr
                     nonPoison := aRes.val.nonPoison && bRes.val.nonPoison && cRes.val.nonPoison
                     noUB := baseNoUB }
            ubCond := baseUb }

/-- Symbolically evaluate a pure `ScalarExpr` in `SymExecState`. -/
def symEvalScalar (st : SymExecState) (se : ScalarExpr) : SymStateVal :=
  (symEvalScalarRes st se).val

/-- Resolve a `ScalarExpr` to `(chosenRoot?, nonPoison, noUB)` when it is a direct variable or
    resolved `.select` chain choosing an existing SSA variable; returns `(none, _, _)` if a
    symbolic `.select` condition cannot be statically resolved to a single root. -/
def resolveScalarRoot? (st : SymExecState) : ScalarExpr → Option VarId × Bool × Bool × Bool
  | .var src =>
    let sv := st.lookupVar src
    (some (st.resolveBuf src), sv.nonPoison, sv.noUB, false)
  | .select cond t e =>
    let rc0 := symEvalScalarRes st cond
    let safety := normSymExpr rc0.ubCond
    let rc : SymScalarRes := { rc0 with unsupported := rc0.unsupported ||
      (safety != SymExpr.constBool true && safety != SymExpr.constBool false) }
    let sc := rc.val
    let (rt, pt, ut, unsT) := resolveScalarRoot? st t
    let (re, pe, ue, unsE) := resolveScalarRoot? st e
    match sc.expr with
    | .constBool true => (rt, sc.nonPoison && pt, sc.noUB && ut, rc.unsupported || unsT)
    | .constBool false => (re, sc.nonPoison && pe, sc.noUB && ue, rc.unsupported || unsE)
    | .constU64 n =>
      if n != 0 then (rt, sc.nonPoison && pt, sc.noUB && ut, rc.unsupported || unsT)
      else (re, sc.nonPoison && pe, sc.noUB && ue, rc.unsupported || unsE)
    | .constU256 w =>
      if w != UInt256.zero then (rt, sc.nonPoison && pt, sc.noUB && ut, rc.unsupported || unsT)
      else (re, sc.nonPoison && pe, sc.noUB && ue, rc.unsupported || unsE)
    | _ =>
      let condSort := symExprScalarSort? st sc.expr
      let condIsTypedTuple :=
        match cond with
        | .var cid => st.typedTuples.contains (st.resolveBuf cid)
        | _ => match sc.expr with | .tuple _ => true | _ => false
      let condIsHeapPtr :=
        match cond with
        | .var cid => st.isDefinitelyHeapRoot cid && !(st.isImmediateScalarObj cid)
        | _ => false
      let condBadSort := condSort.isNone && !condIsTypedTuple && !condIsHeapPtr
      let branchUbMismatch := ut != ue
      if condIsTypedTuple || condIsHeapPtr then
        (none, false, false, false)
      else if rt.isSome && rt == re && !branchUbMismatch && !condBadSort then
        (rt, sc.nonPoison && pt && pe, sc.noUB && ut && ue, rc.unsupported || unsT || unsE)
      else
        (none, sc.nonPoison && pt && pe, sc.noUB && ut && ue, rc.unsupported || unsT || unsE || branchUbMismatch || condBadSort)
  | _ => (none, true, true, false)

def scalarExprMentionsHeapRoot (st : SymExecState) : ScalarExpr → Bool
  | .var id => st.isDefinitelyHeapRoot id
  | .binOp _ l r => scalarExprMentionsHeapRoot st l || scalarExprMentionsHeapRoot st r
  | .unaryOp _ a => scalarExprMentionsHeapRoot st a
  | .select c t e | .fma c t e =>
    scalarExprMentionsHeapRoot st c || scalarExprMentionsHeapRoot st t || scalarExprMentionsHeapRoot st e
  | .constU64 _ | .constBool _ => false

/-- Check whether `se` is a pure immediate constant / select tree over immediate constants. -/
def isImmediateScalarExpr (st : SymExecState) : ScalarExpr → Bool
  | .constU64 _ | .constBool _ => true
  | .var id => st.isImmediateScalarObj id
  | .select _ t e => isImmediateScalarExpr st t && isImmediateScalarExpr st e
  | _ => false

def callSlotKind : LNIRType → Option Bool
  | .objPtr | .taggedPtr | .sarray _ | .rawPtr _ | .storageMap => some true
  | .u256 | .i256 | .tuple _ => none
  | _ => some false


end LeanNative.Proofs
