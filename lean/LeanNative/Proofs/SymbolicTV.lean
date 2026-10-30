import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.Proofs.PeepholeProofs
import LeanNative.Proofs.LoopOptProofs

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics

/-!
# Alive2-Style Symbolic Translation Validator (`LeanNative.Proofs.SymbolicTV`)

Provides an independent, execution- and symbolic-normalization-based translation
validation engine for `LNIRDecl` and `LNIRModule` transformations, inspired by Alive2
(Lopes et al., PLDI 2021).

For every pair of source and target declarations `(src, tgt)`, the validator checks
Alive2's 6 refinement obligations:
1. **UB Refinement** (`src.noUB → tgt.noUB`): target introduces no new undefined behavior
   (division/modulo by zero, non-exclusive buffer mutation, out-of-bounds tuple projection).
2. **Return Domain / Reachability Equivalence**: target reaches a valid return iff source does.
3. **Poison Refinement** (`src.nonPoison → tgt.nonPoison`): target introduces no new shift/arith poison.
4. **Symbolic Return Equivalence**: canonical algebraic normal forms of return expressions match
   (`normSymExpr src.retVal == normSymExpr tgt.retVal`).
5. **Multi-Point Concrete Refinement**: bounded operational evaluation via `LeanNative.Semantics.Eval.evalCode`
   across 64 boundary + SplitMix64 deterministic environments confirms forward simulation.
6. **Memory / Buffer Write Refinement**: normalized symbolic buffer write logs match after
   canonicalizing preheader vs. in-loop `sarrayEnsureExclusive` placement.
-/

/-- Symbolic value expression in the Alive2-style translation validation domain. -/
inductive SymExpr where
  | constU64  (val : UInt64)
  | constBool (val : Bool)
  | symVar    (id : VarId)
  | binOp     (op : BinOp) (lhs rhs : SymExpr)
  | unaryOp   (op : UnaryOp) (arg : SymExpr)
  | ite       (cond thenVal elseVal : SymExpr)
  | tuple     (fields : List SymExpr)
  | bufElem   (bufVar : VarId) (idx : SymExpr)
  | unit
  deriving Repr, Inhabited, BEq

namespace SymExpr

/-- Deterministic structural rank used to canonicalize commutative binary operators.
    Constants receive the highest rank so they are pushed to the right-hand side (`x + c`). -/
def rank : SymExpr → Nat
  | .symVar id       => 10 + id
  | .bufElem b _     => 1000 + b
  | .unaryOp _ a     => 2000 + rank a
  | .binOp _ l r     => 3000 + rank l + rank r
  | .ite c t e       => 4000 + rank c + rank t + rank e
  | .tuple fs        => 5000 + fs.length
  | .constBool false => 900000
  | .constBool true  => 900001
  | .constU64 v      => 1000000 + (v % 65536).toNat
  | .unit            => 2000000

/-- Check whether `op` is commutative in `SymExpr`. -/
def isCommutative : BinOp → Bool
  | .add | .mul | .bitAnd | .bitOr | .bitXor | .eq | .clmul64 | .clmul64Hi => true
  | _ => false

end SymExpr

/-- Alive2-style symbolic value paired with `nonPoison` and `noUB` validity conditions. -/
structure SymStateVal where
  expr      : SymExpr
  nonPoison : Bool := true
  noUB      : Bool := true
  deriving Repr, Inhabited, BEq

private def pow2ShiftLog2 : UInt64 → Option UInt64
  | 2 => some 1 | 4 => some 2 | 8 => some 3
  | 16 => some 4 | 32 => some 5 | 64 => some 6
  | _ => none

/-- Single-step algebraic & strength-reduction normalizer on `SymExpr`. -/
def normSymBinOpStep (op : BinOp) (lhs rhs : SymExpr) : SymExpr :=
  -- Canonicalize operand order for commutative operators so constants migrate right
  let (l, r) :=
    if SymExpr.isCommutative op && SymExpr.rank lhs > SymExpr.rank rhs then
      (rhs, lhs)
    else
      (lhs, rhs)
  match op, l, r with
  -- Constant folding on UInt64
  | .add, .constU64 a, .constU64 b => .constU64 (a + b)
  | .sub, .constU64 a, .constU64 b => .constU64 (a - b)
  | .mul, .constU64 a, .constU64 b => .constU64 (a * b)
  | .clmul64, .constU64 a, .constU64 b => .constU64 (clmul64 a b)
  | .clmul64Hi, .constU64 a, .constU64 b => .constU64 (clmul64Hi a b)
  | .gf2Affine, .constU64 a, .constU64 b => .constU64 (gf2Affine a b) | .eor3, .constU64 a, .constU64 b => .constU64 (eor3 a b)
  | .div, .constU64 a, .constU64 b => .constU64 (a / b)
  | .mod, .constU64 a, .constU64 b => .constU64 (a % b)
  | .bitAnd, .constU64 a, .constU64 b => .constU64 (a &&& b)
  | .bitOr,  .constU64 a, .constU64 b => .constU64 (a ||| b)
  | .bitXor, .constU64 a, .constU64 b => .constU64 (a ^^^ b)
  | .shl,    .constU64 a, .constU64 b => .constU64 (a <<< (b &&& 63))
  | .shr,    .constU64 a, .constU64 b => .constU64 (a >>> (b &&& 63))
  | .eq,     .constU64 a, .constU64 b => .constBool (a == b)
  | .lt,     .constU64 a, .constU64 b => .constBool (decide (a < b))
  | .le,     .constU64 a, .constU64 b => .constBool (decide (a ≤ b))
  | .eq,     .constBool a, .constBool b => .constBool (a == b)

  -- Additive identities
  | .add, x, .constU64 0 | .add, .constU64 0, x | .sub, x, .constU64 0 => x
  | .sub, x, y => if x == y then .constU64 0 else .binOp .sub x y

  -- Multiplicative identities & strength reduction (* 2^k -> <<< k)
  | .mul, x, .constU64 1 | .mul, .constU64 1, x => x
  | .mul, _, .constU64 0 | .mul, .constU64 0, _ => .constU64 0
  | .mul, x, .constU64 c =>
    match pow2ShiftLog2 c with
    | some k => .binOp .shl x (.constU64 k)
    | none => .binOp .mul x (.constU64 c)
  | .mul, .constU64 c, x =>
    match pow2ShiftLog2 c with
    | some k => .binOp .shl x (.constU64 k)
    | none => .binOp .mul (.constU64 c) x

  -- Division & modulo identities & strength reduction (/ 2^k -> >>> k, % 2^k -> &&& (2^k - 1))
  | .div, _, .constU64 0 => .constU64 0
  | .div, x, .constU64 1 => x
  | .div, x, .constU64 c =>
    match pow2ShiftLog2 c with
    | some k => .binOp .shr x (.constU64 k)
    | none => .binOp .div x (.constU64 c)
  | .mod, x, .constU64 0 => x
  | .mod, _, .constU64 1 => .constU64 0
  | .mod, x, .constU64 c =>
    match pow2ShiftLog2 c with
    | some _ => .binOp .bitAnd x (.constU64 (c - 1))
    | none => .binOp .mod x (.constU64 c)

  -- Bitwise & shift identities & idempotence
  | .bitXor, x, .constU64 0 | .bitXor, .constU64 0, x => x
  | .bitXor, x, y => if x == y then .constU64 0 else .binOp .bitXor x y
  | .bitOr,  x, .constU64 0 | .bitOr,  .constU64 0, x => x
  | .bitOr,  x, y => if x == y then x else .binOp .bitOr x y
  | .bitAnd, _, .constU64 0 | .bitAnd, .constU64 0, _ => .constU64 0
  | .bitAnd, x, y => if x == y then x else .binOp .bitAnd x y
  | .shl, x, .constU64 0 | .shr, x, .constU64 0 => x

  -- Reflexive comparisons
  | .eq, x, y => if x == y then .constBool true else .binOp .eq x y
  | .lt, x, y => if x == y then .constBool false else .binOp .lt x y
  | .le, x, y => if x == y then .constBool true else .binOp .le x y

  | _, _, _ => .binOp op l r

/-- Single-step unary normalizer on `SymExpr`. -/
def normSymUnaryOpStep (op : UnaryOp) (arg : SymExpr) : SymExpr :=
  match op, arg with
  | .not, .constBool b => .constBool (!b)
  | .not, .unaryOp .not x => x
  | .neg, .constU64 a => .constU64 (0 - a)
  | .neg, .unaryOp .neg x => x
  | _, _ => .unaryOp op arg

/-- Single-step `ite` normalizer on `SymExpr`. -/
def normSymIteStep (cond thenVal elseVal : SymExpr) : SymExpr :=
  match cond with
  | .constBool true => thenVal
  | .constBool false => elseVal
  | .constU64 c => if c != 0 then thenVal else elseVal
  | _ => if thenVal == elseVal then thenVal else .ite cond thenVal elseVal

mutual
  /-- Canonical bottom-up algebraic normalizer on `SymExpr`. -/
  def normSymExpr : SymExpr → SymExpr
    | .constU64 v => .constU64 v
    | .constBool b => .constBool b
    | .symVar id => .symVar id
    | .binOp op l r => normSymBinOpStep op (normSymExpr l) (normSymExpr r)
    | .unaryOp op a => normSymUnaryOpStep op (normSymExpr a)
    | .ite c t e => normSymIteStep (normSymExpr c) (normSymExpr t) (normSymExpr e)
    | .tuple fs => .tuple (normSymExprList fs)
    | .bufElem b idx => .bufElem b (normSymExpr idx)
    | .unit => .unit

  def normSymExprList : List SymExpr → List SymExpr
    | [] => []
    | e :: es => normSymExpr e :: normSymExprList es
end

/-! ## Symbolic Execution of `ScalarExpr`, `LNIRExpr`, `LNIRCode`, and `LNIRDecl` -/

/-- Symbolic execution state tracking variable bindings, buffer aliases, exclusivity,
    normalized memory writes, and Alive2 `noUB` / `nonPoison` flags. -/
structure SymExecState where
  vars          : List (VarId × SymStateVal) := []
  bufAliases    : List (VarId × VarId) := []
  exclusiveBufs : List VarId := []
  memWrites     : List (VarId × SymExpr × SymExpr) := []
  noUB          : Bool := true
  nonPoison     : Bool := true
  reachable     : Bool := true
  deriving Repr, Inhabited, BEq

namespace SymExecState

def lookupVar (st : SymExecState) (v : VarId) : SymStateVal :=
  match st.vars.lookup v with
  | some sv => sv
  | none => { expr := .symVar v, nonPoison := true, noUB := true }

def bindVar (st : SymExecState) (v : VarId) (sv : SymStateVal) : SymExecState :=
  { st with
    vars := (v, sv) :: st.vars.filter (fun (id, _) => id != v)
    noUB := st.noUB && sv.noUB
    nonPoison := st.nonPoison && sv.nonPoison }

def resolveBuf (st : SymExecState) (v : VarId) : VarId :=
  match st.bufAliases.lookup v with
  | some root => root
  | none => v

def aliasBuf (st : SymExecState) (dst src : VarId) : SymExecState :=
  let root := st.resolveBuf src
  { st with bufAliases := (dst, root) :: st.bufAliases.filter (fun (id, _) => id != dst) }

def markExclusive (st : SymExecState) (bufVar : VarId) : SymExecState :=
  let root := st.resolveBuf bufVar
  if st.exclusiveBufs.contains root then st
  else { st with exclusiveBufs := root :: st.exclusiveBufs }

def isBufExclusive (st : SymExecState) (bufVar : VarId) : Bool :=
  let root := st.resolveBuf bufVar
  st.exclusiveBufs.contains root

def readBufSym (st : SymExecState) (bufVar : VarId) (idx : SymExpr) : SymExpr :=
  let root := st.resolveBuf bufVar
  let nidx := normSymExpr idx
  match st.memWrites.find? (fun (b, i, _) => b == root && i == nidx) with
  | some (_, _, val) => val
  | none => .bufElem root nidx

def writeBufSym (st : SymExecState) (bufVar : VarId) (idx val : SymExpr) (requireExcl : Bool) : SymExecState :=
  let root := st.resolveBuf bufVar
  let nidx := normSymExpr idx
  let nval := normSymExpr val
  let exclOk := if requireExcl then st.isBufExclusive root else true
  let filtered := st.memWrites.filter (fun (b, i, _) => !(b == root && i == nidx))
  { st with
    memWrites := (root, nidx, nval) :: filtered
    noUB := st.noUB && exclOk }

end SymExecState

/-- Symbolically evaluate a pure `ScalarExpr` in `SymExecState`. -/
def symEvalScalar (st : SymExecState) : ScalarExpr → SymStateVal
  | .constU64 v => { expr := .constU64 v, nonPoison := true, noUB := true }
  | .constBool b => { expr := .constBool b, nonPoison := true, noUB := true }
  | .var id => st.lookupVar id
  | .binOp op lhs rhs =>
    let sl := symEvalScalar st lhs
    let sr := symEvalScalar st rhs
    { expr := normSymBinOpStep op sl.expr sr.expr
      nonPoison := sl.nonPoison && sr.nonPoison
      noUB := sl.noUB && sr.noUB }
  | .unaryOp op arg =>
    let sa := symEvalScalar st arg
    { expr := normSymUnaryOpStep op sa.expr
      nonPoison := sa.nonPoison
      noUB := sa.noUB }
  | .select cond t e =>
    let sc := symEvalScalar st cond
    let sthen := symEvalScalar st t
    let selse := symEvalScalar st e
    let mkBranch (sv : SymStateVal) : SymStateVal :=
      { expr := sv.expr, nonPoison := sc.nonPoison && sv.nonPoison, noUB := sc.noUB && sv.noUB }
    match sc.expr with
    | .constBool true => mkBranch sthen
    | .constBool false => mkBranch selse
    | .constU64 n => if n != 0 then mkBranch sthen else mkBranch selse
    | _ =>
      { expr := normSymIteStep sc.expr sthen.expr selse.expr
        nonPoison := sc.nonPoison && sthen.nonPoison && selse.nonPoison
        noUB := sc.noUB && sthen.noUB && selse.noUB }
  | .fma a b c =>
    -- Canonicalize FMA `a * b + c` to `add (mul a b) c` so FMA contraction validates against uncontracted IR
    let sa := symEvalScalar st a
    let sb := symEvalScalar st b
    let sc := symEvalScalar st c
    let mulExpr := normSymBinOpStep .mul sa.expr sb.expr
    let addExpr := normSymBinOpStep .add mulExpr sc.expr
    { expr := addExpr
      nonPoison := sa.nonPoison && sb.nonPoison && sc.nonPoison
      noUB := sa.noUB && sb.noUB && sc.noUB }

def callSlotKind : LNIRType → Option Bool
  | .objPtr | .taggedPtr | .sarray _ | .rawPtr _ | .storageMap => some true
  | .u256 | .i256 | .tuple _ => none
  | _ => some false

/-- Symbolically evaluate an `LNIRExpr` and update `SymExecState`. -/
def symEvalExpr (st : SymExecState) (dst : VarId) (e : LNIRExpr) : SymExecState :=
  match e with
  | .scalar se =>
    let sv := symEvalScalar st se
    let st' :=
      match se with
      | .var src => if src != dst then st.aliasBuf dst src else st
      | _ => st
    st'.bindVar dst sv
  | .constU256 val =>
    let symVal : SymExpr :=
      if val.lo1 == 0 && val.hi0 == 0 && val.hi1 == 0 then
        .constU64 val.lo0
      else
        .tuple [.constU64 val.lo0, .constU64 val.lo1, .constU64 val.hi0, .constU64 val.hi1]
    st.bindVar dst { expr := symVal, nonPoison := true, noUB := true }
  | .mulDivDown aVar bVar denomVar | .mulDivUp aVar bVar denomVar =>
    let sa := st.lookupVar aVar
    let sb := st.lookupVar bVar
    let sd := st.lookupVar denomVar
    let divZero := sd.expr == .constU64 0
    let mulExpr := normSymBinOpStep .mul sa.expr sb.expr
    let numExpr :=
      match e with
      | .mulDivUp _ _ _ => normSymBinOpStep .add mulExpr (normSymBinOpStep .sub sd.expr (.constU64 1))
      | _ => mulExpr
    st.bindVar dst {
      expr := normSymBinOpStep .div numExpr sd.expr
      nonPoison := sa.nonPoison && sb.nonPoison && sd.nonPoison
      noUB := sa.noUB && sb.noUB && sd.noUB && !divZero
    }
  | .storageLoad mapVar slotVar | .sarrayGet mapVar slotVar _ | .rawLoad mapVar slotVar _ =>
    let slotSv := st.lookupVar slotVar
    let elemExpr := st.readBufSym mapVar slotSv.expr
    st.bindVar dst { expr := elemExpr, nonPoison := slotSv.nonPoison, noUB := slotSv.noUB }
  | .storageStore mapVar slotVar valVar =>
    let root := st.resolveBuf mapVar
    let slotSv := st.lookupVar slotVar
    let valSv := st.lookupVar valVar
    let st1 := (st.writeBufSym root slotSv.expr valSv.expr false).aliasBuf dst root
    st1.bindVar dst { expr := .symVar root, nonPoison := slotSv.nonPoison && valSv.nonPoison, noUB := slotSv.noUB && valSv.noUB }
  | .mkTuple fields =>
    let svs := fields.map st.lookupVar
    st.bindVar dst { expr := .tuple (svs.map (·.expr)), nonPoison := svs.all (·.nonPoison), noUB := svs.all (·.noUB) }
  | .projTuple tupleVar idx =>
    let tv := st.lookupVar tupleVar
    match tv.expr with
    | .tuple fs =>
      match fs[idx]? with
      | some fExpr => st.bindVar dst { expr := fExpr, nonPoison := tv.nonPoison, noUB := tv.noUB }
      | none => st.bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    | _ => st.bindVar dst { expr := .symVar dst, nonPoison := tv.nonPoison, noUB := tv.noUB }
  | .allocCtor tag objFields scalarFields =>
    let svs := (objFields ++ scalarFields).map st.lookupVar
    (st.markExclusive dst).bindVar dst
      { expr := .tuple (.constU64 tag.toUInt64 :: svs.map (·.expr)), nonPoison := svs.all (·.nonPoison), noUB := svs.all (·.noUB) }
  | .ctorGetObj ctorVar idx | .ctorGetScalar ctorVar idx _ =>
    let cv := st.lookupVar ctorVar
    match cv.expr with
    | .tuple (_tag :: fs) =>
      match fs[idx]? with
      | some fExpr => st.bindVar dst { expr := fExpr, nonPoison := cv.nonPoison, noUB := cv.noUB }
      | none => st.bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    | .symVar rootId =>
      let fieldRoot := 30000 + rootId * 16 + idx
      st.bindVar dst { expr := .symVar fieldRoot, nonPoison := cv.nonPoison, noUB := cv.noUB }
    | _ => st.bindVar dst { expr := .symVar dst, nonPoison := cv.nonPoison, noUB := cv.noUB }
  | .isExclusive objVar =>
    let cv := st.lookupVar objVar
    let exclExpr : SymExpr :=
      match cv.expr with
      | .symVar rootId =>
        if st.isBufExclusive objVar then .constBool true
        else .binOp .eq (.symVar (25000 + st.resolveBuf rootId)) (.constU64 1)
      | _ => .constBool (st.isBufExclusive objVar)
    st.bindVar dst { expr := exclExpr, nonPoison := cv.nonPoison, noUB := cv.noUB }
  | .sarrayLen arrVar =>
    let root := st.resolveBuf arrVar
    st.bindVar dst { expr := .symVar (9000 + root), nonPoison := true, noUB := true }
  | .sarrayDataPtr arrVar _elemTy =>
    let root := st.resolveBuf arrVar
    let exclOk := st.isBufExclusive root
    (st.aliasBuf dst root).bindVar dst { expr := .symVar root, nonPoison := true, noUB := exclOk }
  | .sarrayEnsureExclusive arrVar _elemTy =>
    let root := st.resolveBuf arrVar
    ((st.markExclusive root).aliasBuf dst root).bindVar dst { expr := .symVar root, nonPoison := true, noUB := true }
  | .sarraySet arrVar idxVar valVar _elemTy =>
    let root := st.resolveBuf arrVar
    let idxSv := st.lookupVar idxVar
    let valSv := st.lookupVar valVar
    let st3 := ((st.markExclusive root).writeBufSym root idxSv.expr valSv.expr true).aliasBuf dst root
    st3.bindVar dst { expr := .symVar root, nonPoison := idxSv.nonPoison && valSv.nonPoison, noUB := idxSv.noUB && valSv.noUB }
  | .boxScalar valVar _ | .unboxScalar valVar _ =>
    st.bindVar dst (st.lookupVar valVar)
  | .call fnName args retTy isExt =>
    let ptrRet := callSlotKind retTy == some true
    let i64Ret := callSlotKind retTy == some false
    match isExt, args with
    | false, [a] =>
      if (fnName == "lean_native_box_u64" && ptrRet) || (fnName == "lean_native_unbox_u64" && i64Ret) then
        st.bindVar dst (st.lookupVar a)
      else if fnName == "lean_native_ensure_exclusive" && ptrRet then
        let root := st.resolveBuf a
        ((st.markExclusive root).aliasBuf dst root).bindVar dst (st.lookupVar a)
      else if fnName == "lean_native_sarray_len" && i64Ret then
        let sa := st.lookupVar a
        st.bindVar dst { expr := .symVar (9000 + st.resolveBuf a), nonPoison := sa.nonPoison, noUB := sa.noUB }
      else if fnName == "lean_native_ctor_tag" && i64Ret then
        let sa := st.lookupVar a
        let tagExpr : SymExpr :=
          match sa.expr with
          | .tuple (tag :: _) => tag
          | .constU64 tag => .constU64 tag
          | .symVar rootId => .symVar (24000 + st.resolveBuf rootId)
          | _ => .symVar dst
        st.bindVar dst { expr := tagExpr, nonPoison := sa.nonPoison, noUB := sa.noUB }
      else st.bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    | false, [objVar, idxVar, valVar] =>
      if fnName == "lean_native_ctor_set" && retTy == .unit then
        let root := st.resolveBuf objVar
        let objSv := st.lookupVar root
        let idxSv := st.lookupVar idxVar
        let valSv := st.lookupVar valVar
        let exclOk := st.isBufExclusive root
        let updatedState : SymExecState :=
          match objSv.expr, idxSv.expr with
          | .tuple (tag :: fs), .constU64 idxU64 =>
            let idx := idxU64.toNat
            if idx < fs.length then
              st.bindVar root {
                expr := .tuple (tag :: fs.set idx valSv.expr)
                nonPoison := objSv.nonPoison && idxSv.nonPoison && valSv.nonPoison
                noUB := objSv.noUB && idxSv.noUB && valSv.noUB && exclOk }
            else
              { st with noUB := false, nonPoison := false }
          | .symVar rootId, .constU64 idxU64 =>
            let idx := idxU64.toNat
            let prevFields := (List.range 8).map fun i =>
              if i == idx then valSv.expr else .symVar (30000 + rootId * 16 + i)
            st.bindVar root {
              expr := .tuple (.symVar (24000 + rootId) :: prevFields)
              nonPoison := objSv.nonPoison && idxSv.nonPoison && valSv.nonPoison
              noUB := objSv.noUB && idxSv.noUB && valSv.noUB && exclOk }
          | _, _ =>
            { st with noUB := false, nonPoison := false }
        updatedState.bindVar dst {
          expr := .unit
          nonPoison := objSv.nonPoison && idxSv.nonPoison && valSv.nonPoison
          noUB := objSv.noUB && idxSv.noUB && valSv.noUB && exclOk }
      else st.bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    | _, _ => st.bindVar dst { expr := .unit, nonPoison := false, noUB := false }

/-- Summary produced by symbolic execution of an `LNIRDecl`. -/
structure SymExecSummary where
  declName   : String
  reachable  : Bool
  noUB       : Bool
  nonPoison  : Bool
  retVal     : SymExpr
  memWrites  : List (VarId × SymExpr × SymExpr)
  deriving Repr, Inhabited, BEq

/-- Unroll a `seqFor` loop body `unrollCount` times symbolically. -/
def symExecLoopUnroll (unrollCount : Nat) (curIdx : Nat) (idxVar accVar : VarId)
    (st : SymExecState) (execBody : SymExecState → SymExecState × SymExpr) : SymExecState :=
  match unrollCount with
  | 0 => st
  | n + 1 =>
    let stIdx := st.bindVar idxVar { expr := .constU64 curIdx.toUInt64, nonPoison := true, noUB := true }
    let (stAfter, retExpr) := execBody stIdx
    let stNext :=
      match retExpr with
      | .symVar r => stAfter.aliasBuf accVar r
      | _ => stAfter
    let stNextBound := stNext.bindVar accVar {
      expr := normSymExpr retExpr
      nonPoison := stAfter.nonPoison
      noUB := stAfter.noUB
    }
    symExecLoopUnroll n (curIdx + 1) idxVar accVar stNextBound execBody

/-- Fuel-bounded symbolic execution of `LNIRCode`. -/
def symExecCode (fuel : Nat) (unrollBound : Nat) (st : SymExecState) (code : LNIRCode) :
    SymExecState × SymExpr :=
  match fuel with
  | 0 => (st, .unit)
  | fuel' + 1 =>
    match code with
    | .letBind dst _ty val k =>
      let st1 := symEvalExpr st dst val
      symExecCode fuel' unrollBound st1 k
    | .rawStore ptrVar idxVar valVar _elemTy k =>
      let idxSv := st.lookupVar idxVar
      let valSv := st.lookupVar valVar
      let st1 := st.writeBufSym ptrVar idxSv.expr valSv.expr true
      let st2 := { st1 with
        noUB := st1.noUB && idxSv.noUB && valSv.noUB
        nonPoison := st1.nonPoison && idxSv.nonPoison && valSv.nonPoison }
      symExecCode fuel' unrollBound st2 k
    | .incRef _ _ k =>
      symExecCode fuel' unrollBound st k
    | .decRef _ _ k =>
      symExecCode fuel' unrollBound st k
    | .ite condVar thenBranch elseBranch =>
      let condSv := st.lookupVar condVar
      match condSv.expr with
      | .constBool true => symExecCode fuel' unrollBound st thenBranch
      | .constBool false => symExecCode fuel' unrollBound st elseBranch
      | .constU64 v =>
        if v != 0 then symExecCode fuel' unrollBound st thenBranch
        else symExecCode fuel' unrollBound st elseBranch
      | cExpr =>
        let (stForT, stForE) : SymExecState × SymExecState :=
          match cExpr with
          | .unaryOp .not (.binOp .eq (.symVar rcSym) (.constU64 1)) =>
            if rcSym ≥ 25000 then (st, st.markExclusive (rcSym - 25000)) else (st, st)
          | .binOp .eq (.symVar rcSym) (.constU64 1) =>
            if rcSym ≥ 25000 then (st.markExclusive (rcSym - 25000), st) else (st, st)
          | .binOp .eq (.symVar tagSym) (.constU64 tagVal) =>
            if tagSym ≥ 24000 && tagSym < 25000 then
              let rootId := tagSym - 24000
              let curSv := st.lookupVar rootId
              match curSv.expr with
              | .symVar _ =>
                let symFields := (List.range 8).map (fun i => SymExpr.symVar (30000 + rootId * 16 + i))
                (st.bindVar rootId { curSv with expr := .tuple (.constU64 tagVal :: symFields) }, st)
              | _ => (st, st)
            else (st, st)
          | _ => (st, st)
        let (stT, retT) := symExecCode fuel' unrollBound stForT thenBranch
        let (stE, retE) := symExecCode fuel' unrollBound stForE elseBranch
        let mergedState : SymExecState := {
          st with
          noUB := st.noUB && condSv.noUB && stT.noUB && stE.noUB
          nonPoison := st.nonPoison && condSv.nonPoison && stT.nonPoison && stE.nonPoison
          reachable := stT.reachable || stE.reachable
          memWrites := if stT.memWrites == stE.memWrites then stT.memWrites else st.memWrites
        }
        (mergedState, normSymIteStep cExpr (normSymExpr retT) (normSymExpr retE))
    | .seqFor idxVar _loVar _hiVar accVar accInit _accTy stepBody k =>
      let initSv := st.lookupVar accInit
      let stInit := (st.aliasBuf accVar accInit).bindVar accVar initSv
      let stAfterLoop := symExecLoopUnroll unrollBound 0 idxVar accVar stInit
        (fun s => symExecCode fuel' unrollBound s stepBody)
      symExecCode fuel' unrollBound stAfterLoop k
    | .parFor outVar _lenVar inputs _elemTy _kernel k =>
      let baseBuf := match inputs.head? with | some i => st.resolveBuf i | none => outVar
      let st1 := (st.markExclusive baseBuf).aliasBuf outVar baseBuf
      let st2 := st1.bindVar outVar { expr := .symVar baseBuf, nonPoison := true, noUB := true }
      symExecCode fuel' unrollBound st2 k
    | .ret v =>
      let rSv := st.lookupVar v
      let finalExpr := normSymExpr rSv.expr
      ({ st with
          noUB := st.noUB && rSv.noUB
          nonPoison := st.nonPoison && rSv.nonPoison }, finalExpr)
    | .unreachable =>
      ({ st with reachable := false }, .unit)

/-- Run symbolic execution on an `LNIRDecl` with initial symbolic parameters. -/
def symExecDecl (loopUnrollBound : Nat := 4) (d : LNIRDecl) : SymExecSummary :=
  let initState : SymExecState := d.params.foldl (fun acc p =>
    let st1 := acc.bindVar p.id { expr := .symVar p.id, nonPoison := true, noUB := true }
    match p.ty with
    | .rawPtr _ => st1.markExclusive p.id
    | _ => st1
  ) {}
  let (finalSt, retExpr) := symExecCode 256 loopUnrollBound initState d.body
  { declName := d.name
    reachable := finalSt.reachable
    noUB := finalSt.noUB
    nonPoison := finalSt.nonPoison
    retVal := normSymExpr retExpr
    memWrites := finalSt.memWrites }

/-! ## Multi-Point Concrete Refinement Evaluator (64 Boundary + SplitMix64 Samples) -/

/-- Deterministic SplitMix64 step for reproducible test input generation. -/
def splitMix64Next (state : UInt64) : UInt64 × UInt64 :=
  let s' := state + 0x9e3779b97f4a7c15
  let z1 := (s' ^^^ (s' >>> 30)) * 0xbf58476d1ce4e5b9
  let z2 := (z1 ^^^ (z1 >>> 27)) * 0x94d049bb133111eb
  let out := z2 ^^^ (z2 >>> 31)
  (out, s')

/-- Construct a concrete `Val` and update `HeapState` for a parameter of type `LNIRType`.
    Scalar inputs are drawn from `{1, ..., 8}` so loop bounds and array indices stay within
    the 16-element test buffers while exercising multi-iteration loops and arithmetic paths. -/
def mkSampleParamVal (seed : UInt64) (paramIdx : Nat) (ty : LNIRType) (st : HeapState) :
    Val × HeapState :=
  let (r, _) := splitMix64Next (seed + paramIdx.toUInt64 * 31)
  let smallU64 : UInt64 := (r % 8) + 1
  match ty with
  | .i1 => (.bool (r % 2 == 1), st)
  | .i8 =>
    let v : UInt64 :=
      match paramIdx + (r % 5).toNat with
      | 0 => 0 | 1 => 255 | _ => r &&& 0xFF
    (.u64 v, st)
  | .i16 =>
    let v : UInt64 :=
      match paramIdx + (r % 5).toNat with
      | 0 => 0 | 1 => 65535 | _ => r &&& 0xFFFF
    (.u64 v, st)
  | .i32 =>
    let v : UInt64 :=
      match paramIdx + (r % 5).toNat with
      | 0 => 0 | 1 => 0xFFFFFFFF | _ => r &&& 0xFFFFFFFF
    (.u64 v, st)
  | .u256 | .i256 =>
    let (r1, _) := splitMix64Next (r + 1)
    let (r2, _) := splitMix64Next (r + 2)
    let (r3, _) := splitMix64Next (r + 3)
    let w256 : UInt256 :=
      match r % 8 with
      | 0 => UInt256.zero
      | 1 => UInt256.ofUInt64 smallU64
      | 2 => ⟨0xffffffffffffffff, 0, 0, 0⟩
      | 3 => ⟨0xffffffffffffffff, 0xffffffffffffffff, 0, 0⟩
      | 4 => ⟨0, 0, 0, 0x8000000000000000⟩
      | 5 => UInt256.max
      | _ => ⟨r, r1, r2, r3 &&& 0x7fffffffffffffff⟩
    (.u256 w256, st)
  | .storageMap =>
    let mapId := st.nextId + 1
    let initEntries : List (UInt256 × UInt256) :=
      if r % 2 == 0 then
        let seededVal : UInt256 := ⟨0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0x7fffffffffffffff⟩
        [ (UInt256.zero, seededVal)
        , (UInt256.ofUInt64 1, seededVal)
        , (UInt256.ofUInt64 2, seededVal)
        , (UInt256.ofUInt64 3, seededVal)
        , (UInt256.ofUInt64 4, seededVal)
        , (UInt256.ofUInt64 5, seededVal)
        , (UInt256.ofUInt64 6, seededVal)
        , (UInt256.ofUInt64 7, seededVal)
        , (UInt256.ofUInt64 8, seededVal) ]
      else []
    let mapBuf : StorageMapBuffer := { id := mapId, entries := initEntries }
    (.storageMapId mapId, { st with nextId := mapId, storageMaps := mapBuf :: st.storageMaps })
  | .sarray _ =>
    let bufId := st.nextId + 1
    let elems := (List.range 16).map (fun i => ((splitMix64Next (r + i.toUInt64)).1 % 64) + 1)
    let buf : ArrayBuffer := { id := bufId, exclusive := (r % 2 == 0), data := elems.toArray }
    (.sarrayId bufId, { st with buffers := buf :: st.buffers, nextId := bufId })
  | .rawPtr _ =>
    let bufId := st.nextId + 1
    let elems := (List.range 16).map (fun i => ((splitMix64Next (r + i.toUInt64)).1 % 64) + 1)
    let buf : ArrayBuffer := { id := bufId, exclusive := true, data := elems.toArray }
    (.rawPtrId bufId, { st with buffers := buf :: st.buffers, nextId := bufId })
  | .tuple fs =>
    let vals := fs.mapIdx (fun idx _ => Val.u64 (((splitMix64Next (r + idx.toUInt64 * 17)).1 % 16) + 1))
    (.tuple vals, st)
  | .objPtr | .taggedPtr =>
    match r % 5 with
    | 0 => (.u64 1, st)
    | _ =>
      let mkLeaf (s : HeapState) (salt : UInt64) (sharedLeaf : Bool) : Val × HeapState :=
        let f0 := Val.u64 (((splitMix64Next (r + salt)).1 % 16) + 1)
        let f1 := Val.u64 (((splitMix64Next (r + salt + 7)).1 % 16) + 1)
        let (cid, s1) := s.allocHeapCtor 0 [f0, f1]
        if sharedLeaf then
          match s1.incRefObj cid 1 with
          | .ok s2 => (.objPtr cid, s2)
          | .error _ => (.objPtr cid, s1)
        else (.objPtr cid, s1)
      let sharedRoot := (r % 2 == 0)
      let sharedKids := (r % 3 == 0)
      let (c0, st1) := mkLeaf st 101 sharedKids
      let (c1, st2) := mkLeaf st1 203 sharedKids
      let (oid, st3) := st2.allocHeapCtor 0 [c0, c1]
      if sharedRoot then
        match st3.incRefObj oid 1 with
        | .ok st4 => (.objPtr oid, st4)
        | .error _ => (.objPtr oid, st3)
      else (.objPtr oid, st3)
  | .unit => (.unit, st)
  | _ => (.u64 smallU64, st)

/-- Build a single sample `(VarEnv × HeapState)` for declaration `d` from `sampleIdx ∈ 0..63`. -/
def buildDeclSample (d : LNIRDecl) (sampleIdx : Nat) : VarEnv × HeapState :=
  let seed : UInt64 := (sampleIdx.toUInt64 + 1) * 0x9e3779b97f4a7c15
  let (env, st, _) := d.params.foldl (fun (curEnv, curSt, idx) p =>
    let (v, nextSt) := mkSampleParamVal seed idx p.ty curSt
    (curEnv.bind p.id v, nextSt, idx + 1)
  ) (VarEnv.empty, HeapState.empty, 0)
  (env, st)

/-- Check concrete forward simulation on a single `(VarEnv, HeapState)` sample:
    whenever `src` evaluates without UB to `.ok (vSrc, stSrc)`, `tgt` must evaluate
    without UB to `.ok (vTgt, stTgt)` with `vSrc == vTgt` and `stSrc = stTgt`. -/
def checkSingleSample (fuel : Nat) (env : VarEnv) (st : HeapState) (src tgt : LNIRCode) : Bool :=
  match evalCode fuel env st src with
  | .error _ => true
  | .ok (vSrc, stSrc) =>
    match evalCode fuel env st tgt with
    | .ok (vTgt, stTgt) => (vSrc == vTgt) && decide (stSrc = stTgt)
    | .error _ => false

/-- Check concrete forward simulation across a list of `(VarEnv × HeapState)` samples. -/
def checkConcreteSamples (fuel : Nat) (samples : List (VarEnv × HeapState)) (src tgt : LNIRCode) : Bool :=
  samples.all (fun (env, st) => checkSingleSample fuel env st src tgt)

/-- Evaluate `src` and `tgt` declarations across `numSamples` (default 64) concrete input states. -/
def checkDeclConcreteRefinement (src tgt : LNIRDecl) (numSamples : Nat := 64) (fuel : Nat := 128) :
    Bool × Nat :=
  let effFuel := Nat.max fuel 256
  let samples := (List.range numSamples).map (buildDeclSample src)
  let (passedCount, nonVacuousCount) := samples.foldl (fun (acc, okSrc) (env, st) =>
    let srcOk := match evalCode effFuel env st src.body with | .ok _ => true | .error _ => false
    let stepOk := checkSingleSample effFuel env st src.body tgt.body
    (if stepOk then acc + 1 else acc, if srcOk && stepOk then okSrc + 1 else okSrc)) (0, 0)
  (passedCount == numSamples && (numSamples == 0 || nonVacuousCount > 0), nonVacuousCount)

/-! ## Alive2 6-Part Translation Validation Result & Module Report -/

/-- Per-declaration Alive2-style 6-part translation validation verdict. -/
structure TVDeclResult where
  declName           : String
  srcHash            : String
  tgtHash            : String
  ubRefines          : Bool
  domainEquiv        : Bool
  poisonRefines      : Bool
  symRetEquiv        : Bool
  concreteRefines    : Bool
  concreteSamplesOk  : Nat
  concreteSamplesTot : Nat
  memWritesEquiv     : Bool
  passed             : Bool
  srcRetSummary      : String
  tgtRetSummary      : String
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Module-level translation validation report across all declarations. -/
structure TVModuleReport where
  moduleName    : String
  schemaVersion : String := "lean-native-symbolic-tv-v2"
  totalDecls    : Nat
  passedDecls   : Nat
  allPassed     : Bool
  declResults   : List TVDeclResult
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Validate translation refinement `(src ⊑ tgt)` for a single declaration using Alive2's 6 obligations. -/
def validateTranslationDecl (src tgt : LNIRDecl) (numSamples : Nat := 64) : TVDeclResult :=
  let sSrc := symExecDecl 4 src
  let sTgt := symExecDecl 4 tgt
  -- 1. UB refinement: src.noUB -> tgt.noUB
  let ubRefines := !sSrc.noUB || sTgt.noUB
  -- 2. Return domain / reachability equivalence
  let domainEquiv := sSrc.reachable == sTgt.reachable
  -- 3. Poison refinement: src.nonPoison -> tgt.nonPoison
  let poisonRefines := !sSrc.nonPoison || sTgt.nonPoison
  -- 4. Symbolic return expression equivalence (after canonical normalization)
  let symRetEquiv := normSymExpr sSrc.retVal == normSymExpr sTgt.retVal
  -- 5. Multi-point concrete refinement across 64 deterministic input states (fail closed when all samples are UB)
  let (concreteOk, passedSamples) := checkDeclConcreteRefinement src tgt numSamples 128
  -- 6. Memory / buffer write log equivalence
  let memWritesEquiv := sSrc.memWrites == sTgt.memWrites
  let allOk :=
    ubRefines && domainEquiv && poisonRefines && symRetEquiv && concreteOk && memWritesEquiv
  { declName := src.name
    srcHash := src.structuralHash
    tgtHash := tgt.structuralHash
    ubRefines := ubRefines
    domainEquiv := domainEquiv
    poisonRefines := poisonRefines
    symRetEquiv := symRetEquiv
    concreteRefines := concreteOk
    concreteSamplesOk := passedSamples
    concreteSamplesTot := numSamples
    memWritesEquiv := memWritesEquiv
    passed := allOk
    srcRetSummary := reprStr sSrc.retVal
    tgtRetSummary := reprStr sTgt.retVal }

/-- Validate an entire optimized `LNIRModule` against its unoptimized source `LNIRModule`. -/
def validateTranslationModule (srcMod tgtMod : LNIRModule) (numSamples : Nat := 64) : TVModuleReport :=
  let results := srcMod.decls.filterMap (fun srcDecl =>
    match tgtMod.decls.find? (fun d => d.name == srcDecl.name) with
    | some tgtDecl => some (validateTranslationDecl srcDecl tgtDecl numSamples)
    | none => none)
  let passedCount := (results.filter (·.passed)).length
  { moduleName := srcMod.moduleName
    schemaVersion := "lean-native-symbolic-tv-v2"
    totalDecls := results.length
    passedDecls := passedCount
    allPassed := passedCount == results.length && results.length == srcMod.decls.length
    declResults := results }

/-! ## Machine-Checked Soundness Theorems for `SymbolicTV` -/

/-- Canonical normalization of `.constU64` is a fixed point. -/
theorem normSymExpr_constU64 (n : UInt64) :
    normSymExpr (.constU64 n) = .constU64 n := rfl

/-- Canonical normalization of `.constBool` is a fixed point. -/
theorem normSymExpr_constBool (b : Bool) :
    normSymExpr (.constBool b) = .constBool b := rfl

/-- Canonical normalization of `constU64 a + constU64 b` matches exact `UInt64` addition in `evalScalarExpr`. -/
theorem normSymExpr_const_sound (env : VarEnv) (a b : UInt64) :
    evalScalarExpr env (.binOp .add (.constU64 a) (.constU64 b)) =
    evalScalarExpr env (.constU64 (a + b)) := rfl

/-- Completeness of `checkSingleSample` with respect to `CodeRefines`:
    any `src` and `tgt` related by kernel-checked `CodeRefines src tgt` always pass `checkSingleSample`. -/
theorem checkSingleSample_of_codeRefines (fuel : Nat) (env : VarEnv) (st : HeapState)
    (src tgt : LNIRCode) (href : CodeRefines src tgt) :
    checkSingleSample fuel env st src tgt = true := by
  unfold checkSingleSample
  cases hsrc : evalCode fuel env st src with
  | error _ => rfl
  | ok pair =>
    rcases pair with ⟨v, st'⟩
    have htgt := href fuel env st v st' hsrc
    rw [htgt]
    simp [Val.beq_self]

/-- Completeness of `checkConcreteSamples` with respect to `CodeRefines`:
    any `src` and `tgt` related by `CodeRefines src tgt` pass `checkConcreteSamples` on all sample suites. -/
theorem checkConcreteSamples_of_codeRefines (fuel : Nat) (samples : List (VarEnv × HeapState))
    (src tgt : LNIRCode) (href : CodeRefines src tgt) :
    checkConcreteSamples fuel samples src tgt = true := by
  unfold checkConcreteSamples
  induction samples with
  | nil => rfl
  | cons s rest ih =>
    rcases s with ⟨env, st⟩
    simp only [List.all_cons, checkSingleSample_of_codeRefines fuel env st src tgt href,
      Bool.true_and, ih]

/-- Soundness of `checkSingleSample`: whenever `checkSingleSample fuel env st src tgt = true`
    and `src` evaluates without UB to `.ok (v, st')`, `tgt` also evaluates without UB to `.ok (vTgt, st')`
    with `(v == vTgt) = true` and identical heap state `st'`. -/
theorem sound_of_checkSingleSample_eq_true (fuel : Nat) (env : VarEnv) (st : HeapState)
    (src tgt : LNIRCode) (v : Val) (st' : HeapState)
    (hcheck : checkSingleSample fuel env st src tgt = true)
    (hsrc : evalCode fuel env st src = .ok (v, st')) :
    ∃ vTgt, evalCode fuel env st tgt = .ok (vTgt, st') ∧ (v == vTgt) = true := by
  unfold checkSingleSample at hcheck; rw [hsrc] at hcheck
  cases htgt : evalCode fuel env st tgt with
  | error _ => rw [htgt] at hcheck; contradiction
  | ok pair =>
    rcases pair with ⟨vTgt, stTgt⟩; rw [htgt] at hcheck
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
    exact ⟨vTgt, hcheck.2 ▸ rfl, hcheck.1⟩

/-- Reflexive soundness of symbolic translation validation (`symbolicTV_refl_sound`). -/
theorem symbolicTV_refl_sound (c : LNIRCode) (fuel : Nat) (samples : List (VarEnv × HeapState)) :
    CodeRefines c c ∧ checkConcreteSamples fuel samples c c = true :=
  ⟨CodeRefines.refl c, checkConcreteSamples_of_codeRefines fuel samples c c (CodeRefines.refl c)⟩

namespace SymbolicTV
  abbrev normSymExpr_constU64 := @LeanNative.Proofs.normSymExpr_constU64
  abbrev normSymExpr_constBool := @LeanNative.Proofs.normSymExpr_constBool
  abbrev normSymExpr_const_sound := @LeanNative.Proofs.normSymExpr_const_sound
  abbrev checkSingleSample_of_codeRefines := @LeanNative.Proofs.checkSingleSample_of_codeRefines
  abbrev checkConcreteSamples_of_codeRefines := @LeanNative.Proofs.checkConcreteSamples_of_codeRefines
  abbrev sound_of_checkSingleSample_eq_true := @LeanNative.Proofs.sound_of_checkSingleSample_eq_true
  abbrev symbolicTV_refl_sound := @LeanNative.Proofs.symbolicTV_refl_sound
end SymbolicTV

private def symCallNoUB (fn : String) (args : List VarId) (ty : LNIRType) (ext : Bool := false) : Bool :=
  (symEvalExpr {} 9 (.call fn args ty ext)).noUB

#guard symCallNoUB "lean_native_box_u64" [1] .objPtr
#guard !symCallNoUB "lean_native_box_u64" [1] .i64
#guard !symCallNoUB "lean_native_box_u64" [1, 2] .objPtr
#guard !symCallNoUB "lean_native_unbox_u64" [] .i64
#guard !symCallNoUB "lean_native_unbox_u64" [1] .u256
#guard !symCallNoUB "lean_native_ensure_exclusive" [1] .i64
#guard !symCallNoUB "lean_native_sarray_len" [1] .objPtr
#guard !symCallNoUB "lean_native_sarray_len" [1] .i64 true
#guard !symCallNoUB "lean_native_unknown" [1] .i64
#guard (symEvalExpr {} 9 (.call "lean_native_unbox_u64" [1] .i64)).lookupVar 9 == (({} : SymExecState).lookupVar 1)
#guard ((symEvalExpr {} 9 (.call "lean_native_ensure_exclusive" [1] (.sarray .i64))).isBufExclusive 9)
#guard (symEvalExpr {} 9 (.call "lean_native_sarray_len" [1] .i64)).lookupVar 9 ==
  (symEvalExpr {} 9 (.sarrayLen 1)).lookupVar 9

/-! ## JSON & Human-Readable Formatting for `TVModuleReport` -/

private abbrev escapeJsonTV := LeanNative.IR.jsonEscape

def TVDeclResult.toJson (r : TVDeclResult) : String :=
  "{" ++
  s!"\"declName\":\"{escapeJsonTV r.declName}\"," ++
  s!"\"srcHash\":\"{escapeJsonTV r.srcHash}\"," ++
  s!"\"tgtHash\":\"{escapeJsonTV r.tgtHash}\"," ++
  s!"\"passed\":{if r.passed then "true" else "false"}," ++
  s!"\"ubRefines\":{if r.ubRefines then "true" else "false"}," ++
  s!"\"domainEquiv\":{if r.domainEquiv then "true" else "false"}," ++
  s!"\"poisonRefines\":{if r.poisonRefines then "true" else "false"}," ++
  s!"\"symRetEquiv\":{if r.symRetEquiv then "true" else "false"}," ++
  s!"\"concreteRefines\":{if r.concreteRefines then "true" else "false"}," ++
  s!"\"concreteSamplesOk\":{r.concreteSamplesOk}," ++
  s!"\"concreteSamplesTot\":{r.concreteSamplesTot}," ++
  s!"\"memWritesEquiv\":{if r.memWritesEquiv then "true" else "false"}" ++
  "}"

def TVModuleReport.toJson (r : TVModuleReport) : String :=
  let declsJson := String.intercalate "," (r.declResults.map TVDeclResult.toJson)
  "{" ++
  s!"\"schemaVersion\":\"{escapeJsonTV r.schemaVersion}\"," ++
  s!"\"moduleName\":\"{escapeJsonTV r.moduleName}\"," ++
  s!"\"allPassed\":{if r.allPassed then "true" else "false"}," ++
  s!"\"totalDecls\":{r.totalDecls}," ++
  s!"\"passedDecls\":{r.passedDecls}," ++
  s!"\"declResults\":[{declsJson}]" ++
  "}"

def TVModuleReport.formatSummary (r : TVModuleReport) : String :=
  let header :=
    s!"=== Alive2-Style Symbolic Translation Validation Report ===\n" ++
    s!"Module: {r.moduleName} ({r.schemaVersion})\n" ++
    s!"Status: {if r.allPassed then "PASSED" else "FAILED"} ({r.passedDecls}/{r.totalDecls} declarations refined)\n"
  let lines := r.declResults.map (fun d =>
    let st := if d.passed then "PASS" else "FAIL"
    s!"  [{st}] {d.declName} ({d.srcHash} -> {d.tgtHash}): " ++
    s!"noUB={d.ubRefines}, dom={d.domainEquiv}, nonPoison={d.poisonRefines}, " ++
    s!"symRet={d.symRetEquiv}, concrete={d.concreteSamplesOk}/{d.concreteSamplesTot}, mem={d.memWritesEquiv}")
  header ++ String.intercalate "\n" lines

end LeanNative.Proofs
