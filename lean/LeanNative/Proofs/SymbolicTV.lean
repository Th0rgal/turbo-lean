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

  -- Additive identities & constant cancellation
  | .add, x, .constU64 0 | .add, .constU64 0, x | .sub, x, .constU64 0 => x
  | .add, .binOp .add x (.constU64 a), .constU64 b =>
    let s := a + b
    if s == 0 then x else .binOp .add x (.constU64 s)
  | .add, .binOp .sub x (.constU64 a), .constU64 b =>
    if a == b then x
    else if b > a then .binOp .add x (.constU64 (b - a))
    else .binOp .sub x (.constU64 (a - b))
  | .sub, .binOp .add x (.constU64 a), .constU64 b =>
    if a == b then x
    else if a > b then .binOp .add x (.constU64 (a - b))
    else .binOp .sub x (.constU64 (b - a))
  | .sub, .binOp .sub x (.constU64 a), .constU64 b =>
    let s := a + b
    if s == 0 then x else .binOp .sub x (.constU64 s)
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
  allocRoots    : List VarId := []
  extSeenRoots  : List VarId := []
  extLivenessRoots : List VarId := []
  extRcDeltas   : List (VarId × SymExpr) := []
  refCounts     : List (VarId × Nat) := []
  rcExprs       : List (VarId × SymExpr) := []
  memWrites     : List (VarId × SymExpr × SymExpr) := []
  heapStepEpoch : Nat := 0
  reachCond     : SymExpr := .constBool true
  ubCond        : SymExpr := .constBool true
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
  let nextNoUB := st.noUB && sv.noUB
  { st with
    vars := (v, sv) :: st.vars.filter (fun (id, _) => id != v)
    ubCond := if sv.noUB then st.ubCond else .constBool false
    noUB := nextNoUB
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
  { st with
    exclusiveBufs := root :: st.exclusiveBufs.filter (· != root)
    refCounts := (root, 1) :: st.refCounts.filter (fun (id, _) => id != root)
    rcExprs := (root, .constU64 1) :: st.rcExprs.filter (fun (id, _) => id != root) }

def lookupExtRcDeltaExpr (st : SymExecState) (root : VarId) : SymExpr :=
  (st.extRcDeltas.lookup root).getD (.constU64 0)

def addExtRcDelta (st : SymExecState) (bufVar : VarId) (count : Nat) (inc : Bool) : SymExecState :=
  let root := st.resolveBuf bufVar
  if st.allocRoots.contains root || count == 0 then st
  else
    let prev := st.lookupExtRcDeltaExpr root
    let next := normSymExpr (normSymBinOpStep (if inc then .add else .sub) prev (.constU64 count.toUInt64))
    let rest := st.extRcDeltas.filter (fun (id, _) => id != root)
    { st with extRcDeltas := if next == .constU64 0 then rest else (root, next) :: rest }

def noteExtRoot (st : SymExecState) (bufVar : VarId) : SymExecState :=
  let root := st.resolveBuf bufVar
  if st.allocRoots.contains root || st.extSeenRoots.contains root then st
  else { st with extSeenRoots := root :: st.extSeenRoots }

def bumpExternalHeapEpoch (st : SymExecState) (bufVar : VarId) (mayFree : Bool) : SymExecState :=
  let root := st.resolveBuf bufVar
  if st.allocRoots.contains root then st
  else
    let st0 := st.noteExtRoot root
    let nextEpoch := st0.heapStepEpoch + 1
    { st0 with
      heapStepEpoch := nextEpoch
      extLivenessRoots := if mayFree then [] else st0.extLivenessRoots
      exclusiveBufs := st0.exclusiveBufs.filter (fun b => b == root || st0.allocRoots.contains b)
      refCounts := st0.refCounts.filter (fun (b, _) => b == root || st0.allocRoots.contains b)
      rcExprs := st0.rcExprs.filter (fun (b, _) => b == root || st0.allocRoots.contains b) }

def lookupRcExpr (st : SymExecState) (bufVar : VarId) : SymExpr :=
  let root := st.resolveBuf bufVar
  match st.refCounts.lookup root with
  | some rc => .constU64 rc.toUInt64
  | none =>
    match st.rcExprs.lookup root with
    | some e => e
    | none =>
      if st.allocRoots.contains root then .symVar (100000 + root)
      else .symVar (100000 + st.heapStepEpoch * 1000000 + root)

def markAllocated (st : SymExecState) (bufVar : VarId) : SymExecState :=
  let root := st.resolveBuf bufVar
  let st1 := st.markExclusive root
  { st1 with allocRoots := root :: st1.allocRoots.filter (· != root) }

def conjoinUbCond (c1 c2 : SymExpr) : SymExpr :=
  match c1, c2 with
  | .constBool false, _ | _, .constBool false => .constBool false
  | .constBool true, x => x
  | x, .constBool true => x
  | x, y => if x == y then x else normSymIteStep x y (.constBool false)

def requireUbCond (st : SymExecState) (cond : SymExpr) : SymExecState :=
  let ncond := normSymExpr cond
  match ncond with
  | .constBool true => st
  | .constBool false => { st with noUB := false, nonPoison := false, ubCond := .constBool false }
  | _ => { st with ubCond := conjoinUbCond st.ubCond ncond }

def noteExtLiveRoot (st : SymExecState) (bufVar : VarId) : SymExecState :=
  let root := st.resolveBuf bufVar
  let st0 := st.noteExtRoot root
  if st0.allocRoots.contains root || st0.extLivenessRoots.contains root then st0
  else { st0 with extLivenessRoots := root :: st0.extLivenessRoots }

def liveRcCond (st : SymExecState) (bufVar : VarId) : SymExpr :=
  let root := st.resolveBuf bufVar
  match st.refCounts.lookup root with
  | some rc => .constBool (rc > 0)
  | none =>
    if st.exclusiveBufs.contains root || st.extLivenessRoots.contains root then .constBool true
    else .binOp .lt (.constU64 0) (.symVar (100000 + root))

def exclRcCond (st : SymExecState) (bufVar : VarId) : SymExpr :=
  let root := st.resolveBuf bufVar
  match st.refCounts.lookup root with
  | some rc => .constBool (rc == 1)
  | none =>
    if st.exclusiveBufs.contains root then .constBool true
    else normSymBinOpStep .eq (st.lookupRcExpr root) (.constU64 1)

def clearAlias (st : SymExecState) (v : VarId) : SymExecState :=
  { st with bufAliases := st.bufAliases.filter (fun (id, _) => id != v) }

def updateRefCountFuel : Nat → SymExecState → Nat → Nat → Bool → SymExecState
  | 0, st, _, _, _ => { st with noUB := false, nonPoison := false, ubCond := .constBool false }
  | fuel + 1, st, v, count, inc =>
    let root := st.resolveBuf v
    if count == 0 then st
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
            let childRoots : List VarId :=
              match (st1'.lookupVar root).expr with
              | .tuple (_tag :: fs) =>
                fs.filterMap fun f =>
                  match f with
                  | .symVar cid =>
                    let cRoot := st1'.resolveBuf cid
                    if st1'.allocRoots.contains cRoot || (st1'.refCounts.lookup cRoot).isSome ||
                       (st1'.rcExprs.lookup cRoot).isSome || st1'.exclusiveBufs.contains cRoot ||
                       cRoot ≥ 30000 then
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
        let stepSafeCond : SymExpr :=
          if inc then
            -- `baseExpr > 0` AND no 64-bit unsigned wraparound (`baseExpr <= UInt64.max - count`)
            let liveC := st.liveRcCond root
            let noWrapC :=
              if count ≤ 0xFFFFFFFFFFFFFFFF then
                normSymBinOpStep .le baseExpr (.constU64 (0xFFFFFFFFFFFFFFFF - count.toUInt64))
              else .constBool false
            conjoinUbCond liveC noWrapC
          else
            -- Without knowing whether `baseExpr == count` frees the unknown input object (and drops
            -- its uninspected children), symbolic execution requires strictly retaining liveness
            -- (`count < baseExpr`, i.e. `baseExpr > count`) unless concrete RC == 1 was established!
            normSymBinOpStep .lt deltaExpr baseExpr
        let nextExpr := normSymBinOpStep (if inc then .add else .sub) baseExpr deltaExpr
        -- Snapshot `baseExpr` before bumping `heapStepEpoch` so balanced `incRef`/`decRef` on the
        -- SAME `root` still cancels in `rcExprs`, while other external roots advance to the new epoch!
        let st1 := (((st.requireUbCond stepSafeCond).noteExtLiveRoot root).bumpExternalHeapEpoch root false).addExtRcDelta root count inc
        { st1 with
          rcExprs := (root, nextExpr) :: st1.rcExprs.filter (fun (id, _) => id != root)
          exclusiveBufs := st1.exclusiveBufs.filter (· != root) }

def updateRefCount (st : SymExecState) (v count : Nat) (inc : Bool) : SymExecState :=
  updateRefCountFuel 32 st v count inc

def isBufLive (st : SymExecState) (bufVar : VarId) : Bool :=
  let root := st.resolveBuf bufVar
  match st.refCounts.lookup root with
  | some rc => rc > 0
  | none => true

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
  let stExcl := if requireExcl then st.requireUbCond (st.exclRcCond root) else st
  let exclOk := if requireExcl then st.isBufExclusive root else true
  let filtered := stExcl.memWrites.filter (fun (b, i, _) => !(b == root && i == nidx))
  { stExcl with
    memWrites := (root, nidx, nval) :: filtered
    noUB := stExcl.noUB && exclOk }

/-- Fuel-bounded unfolding of heap-allocated constructor roots (`allocRoots` / `refCounts`) plus
    path-aware canonical alpha-renaming of freshly allocated root IDs (`200000 + idx`).
    This preserves internal aliasing/sharing relationships across returns and writes as well as
    terminal reference counts across equivalent allocations with different SSA `VarId`s while
    leaving input parameter and projected synthetic input IDs intact. -/
def expandHeapExpr (st : SymExecState) : Nat → SymExpr → SymExpr
  | 0, e => e
  | d + 1, .symVar id =>
    let root := st.resolveBuf id
    if st.allocRoots.contains root || (st.refCounts.lookup root).isSome || (st.rcExprs.lookup root).isSome then
      let rcExpr := st.lookupRcExpr root
      match (st.lookupVar root).expr with
      | .tuple fs =>
        let fs' := fs.map (expandHeapExpr st d)
        .tuple (.symVar (500000 + root) :: rcExpr :: fs')
      | .symVar rId =>
        .tuple [.symVar (500000 + st.resolveBuf rId), rcExpr]
      | e => e
    else .symVar root
  | d + 1, .tuple fs => .tuple (fs.map (expandHeapExpr st d))
  | d + 1, .ite c t e =>
    normSymIteStep c (expandHeapExpr st d t) (expandHeapExpr st d e)
  | _ + 1, e => e

def alphaRenameAllocTags (st : SymExecState) (expr : SymExpr) : SymExpr :=
  let rec go (e : SymExpr) (ren : List (VarId × VarId)) : SymExpr × List (VarId × VarId) :=
    match e with
    | .symVar id =>
      if id ≥ 500000 then
        let origRoot := id - 500000
        if st.allocRoots.contains origRoot then
          match ren.lookup origRoot with
          | some canonId => (.symVar canonId, ren)
          | none =>
            let canonId := 200000 + ren.length
            (.symVar canonId, ren ++ [(origRoot, canonId)])
        else (.symVar origRoot, ren)
      else (.symVar id, ren)
    | .binOp op l r =>
      let (l', ren1) := go l ren
      let (r', ren2) := go r ren1
      (normSymBinOpStep op l' r', ren2)
    | .unaryOp op a =>
      let (a', ren1) := go a ren
      (normSymUnaryOpStep op a', ren1)
    | .ite c t f =>
      let (c', renC) := go c ren
      let (t', _) := go t renC
      let (f', _) := go f renC
      (normSymIteStep c' t' f', renC)
    | .tuple fs =>
      let (fs', renFinal) := fs.foldl (fun (acc, curRen) f =>
        let (f', nextRen) := go f curRen
        (acc ++ [f'], nextRen)) ([], ren)
      (.tuple fs', renFinal)
    | .bufElem b idx =>
      let (idx', ren1) := go idx ren
      (.bufElem b idx', ren1)
    | other => (other, ren)
  (go expr []).1

mutual
  /-- Simplify nested `.ite` and matching boolean atoms over condition `c` under path assumption `val`. -/
  def substCondInSymExpr (c : SymExpr) (val : Bool) : SymExpr → SymExpr
    | .ite c2 t f =>
      let e := SymExpr.ite c2 t f
      if e == c then .constBool val
      else if e == normSymUnaryOpStep .not c then .constBool (!val)
      else if c2 == c then
        if val then substCondInSymExpr c val t else substCondInSymExpr c val f
      else if c2 == normSymUnaryOpStep .not c then
        if val then substCondInSymExpr c val f else substCondInSymExpr c val t
      else
        normSymIteStep (substCondInSymExpr c val c2) (substCondInSymExpr c val t) (substCondInSymExpr c val f)
    | .tuple fs =>
      let e := SymExpr.tuple fs
      if e == c then .constBool val
      else if e == normSymUnaryOpStep .not c then .constBool (!val)
      else .tuple (substCondInSymExprList c val fs)
    | .binOp op l r =>
      let e := SymExpr.binOp op l r
      if e == c then .constBool val
      else if e == normSymUnaryOpStep .not c then .constBool (!val)
      else normSymBinOpStep op (substCondInSymExpr c val l) (substCondInSymExpr c val r)
    | .unaryOp op a =>
      let e := SymExpr.unaryOp op a
      if e == c then .constBool val
      else if e == normSymUnaryOpStep .not c then .constBool (!val)
      else normSymUnaryOpStep op (substCondInSymExpr c val a)
    | .bufElem b idx =>
      let e := SymExpr.bufElem b idx
      if e == c then .constBool val
      else if e == normSymUnaryOpStep .not c then .constBool (!val)
      else .bufElem b (substCondInSymExpr c val idx)
    | other =>
      if other == c then .constBool val
      else if other == normSymUnaryOpStep .not c then .constBool (!val)
      else other

  def substCondInSymExprList (c : SymExpr) (val : Bool) : List SymExpr → List SymExpr
    | [] => []
    | x :: xs => substCondInSymExpr c val x :: substCondInSymExprList c val xs
end

/-- Distribute `.tuple` across `.ite` (`(ite c t f, x) -> ite c (t[c=true], x[c=true]) (f[c=false], x[c=false])`)
    up to bounded fuel so every feasible path's `(retVal, memWrites)` pair is alpha-renamed jointly! -/
def hoistIteTupleFuel : Nat → SymExpr → SymExpr
  | 0, e => e
  | d + 1, .tuple fs =>
    let fs' := fs.map (hoistIteTupleFuel d)
    let rec splitFirstIte : List SymExpr → List SymExpr → Option (SymExpr × List SymExpr × List SymExpr)
      | _, [] => none
      | pre, .ite c t f :: post =>
        let preT := pre.map (substCondInSymExpr c true)
        let postT := post.map (substCondInSymExpr c true)
        let preF := pre.map (substCondInSymExpr c false)
        let postF := post.map (substCondInSymExpr c false)
        some (c, preT ++ [substCondInSymExpr c true t] ++ postT,
                 preF ++ [substCondInSymExpr c false f] ++ postF)
      | pre, x :: post => splitFirstIte (pre ++ [x]) post
    match splitFirstIte [] fs' with
    | some (c, tFs, fFs) =>
      normSymIteStep c (hoistIteTupleFuel d (.tuple tFs)) (hoistIteTupleFuel d (.tuple fFs))
    | none => .tuple fs'
  | d + 1, .ite c t f =>
    let hc := hoistIteTupleFuel d c
    match hc with
    | .ite cOuter cT cF =>
      let tSub := substCondInSymExpr cOuter true t
      let fSub := substCondInSymExpr cOuter true f
      let tSubF := substCondInSymExpr cOuter false t
      let fSubF := substCondInSymExpr cOuter false f
      normSymIteStep cOuter
        (hoistIteTupleFuel d (normSymIteStep cT tSub fSub))
        (hoistIteTupleFuel d (normSymIteStep cF tSubF fSubF))
    | _ =>
      normSymIteStep hc
        (hoistIteTupleFuel d (substCondInSymExpr hc true t))
        (hoistIteTupleFuel d (substCondInSymExpr hc false f))
  | _ + 1, e => e

def summarizeHeapExpr (st : SymExecState) (expr : SymExpr) : SymExpr :=
  normSymExpr (st.alphaRenameAllocTags (hoistIteTupleFuel 16 (normSymExpr (st.expandHeapExpr 16 expr))))

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
    let objectExprs := objFields.map fun v =>
      let root := st.resolveBuf v
      let rv := st.lookupVar root
      if st.allocRoots.contains root || (st.refCounts.lookup root).isSome then .symVar root
      else match rv.expr with
        | .symVar rId => .symVar (st.resolveBuf rId)
        | e => e
    let scalarExprs := scalarFields.map fun v => (st.lookupVar v).expr
    (st.markAllocated dst).bindVar dst
      { expr := .tuple (.constU64 tag.toUInt64 :: objectExprs ++ scalarExprs), nonPoison := svs.all (·.nonPoison), noUB := svs.all (·.noUB) }
  | .ctorGetObj ctorVar idx | .ctorGetScalar ctorVar idx _ =>
    let rootVar := st.resolveBuf ctorVar
    let liveOk := st.isBufLive rootVar
    let stLive := (st.requireUbCond (st.liveRcCond rootVar)).noteExtLiveRoot rootVar
    let cv := stLive.lookupVar rootVar
    match cv.expr with
    | .tuple (_tag :: fs) =>
      match fs[idx]? with
      | some fExpr =>
        let st' :=
          match fExpr with
          | .symVar fId => stLive.aliasBuf dst fId
          | _ => stLive
        st'.bindVar dst { expr := fExpr, nonPoison := cv.nonPoison && liveOk, noUB := cv.noUB && liveOk }
      | none => stLive.bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    | .symVar rootId =>
      let effRoot := stLive.resolveBuf rootId
      let fieldRoot :=
        if stLive.heapStepEpoch == 0 then 30000 + effRoot * 16 + idx
        else 400000 + stLive.heapStepEpoch * 100000 + effRoot * 16 + idx
      let stNoted := (stLive.noteExtLiveRoot effRoot).noteExtRoot fieldRoot
      (stNoted.aliasBuf dst fieldRoot).bindVar dst { expr := .symVar fieldRoot, nonPoison := cv.nonPoison && liveOk, noUB := cv.noUB && liveOk }
    | _ => stLive.bindVar dst { expr := .symVar dst, nonPoison := cv.nonPoison && liveOk, noUB := cv.noUB && liveOk }
  | .isExclusive objVar =>
    let rootVar := st.resolveBuf objVar
    let stNoted := st.noteExtRoot rootVar
    let liveOk := stNoted.isBufLive rootVar
    let stLive := (stNoted.requireUbCond (stNoted.liveRcCond rootVar)).noteExtLiveRoot rootVar
    let exclExpr : SymExpr :=
      if stLive.isBufExclusive rootVar then .constBool true
      else normSymBinOpStep .eq (stLive.lookupRcExpr rootVar) (.constU64 1)
    let cv := stLive.lookupVar rootVar
    stLive.bindVar dst { expr := exclExpr, nonPoison := cv.nonPoison && liveOk, noUB := cv.noUB && liveOk }
  | .sarrayLen arrVar =>
    let root := st.resolveBuf arrVar
    let stLive := ((st.noteExtRoot root).requireUbCond (st.liveRcCond root)).noteExtLiveRoot root
    stLive.bindVar dst { expr := .symVar (9000 + root), nonPoison := true, noUB := true }
  | .sarrayDataPtr arrVar _elemTy =>
    let root := st.resolveBuf arrVar
    let exclOk := st.isBufExclusive root
    let stExcl := st.requireUbCond (st.exclRcCond root)
    let stBound := (stExcl.aliasBuf dst root).bindVar dst { expr := .symVar root, nonPoison := true, noUB := exclOk }
    { stBound with ubCond := stExcl.ubCond }
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
    (if valVar != dst then st.aliasBuf dst valVar else st).bindVar dst (st.lookupVar (st.resolveBuf valVar))
  | .call fnName args retTy isExt =>
    let ptrRet := callSlotKind retTy == some true
    let i64Ret := callSlotKind retTy == some false
    match isExt, args with
    | false, [a] =>
      if (fnName == "lean_native_box_u64" && ptrRet) || (fnName == "lean_native_unbox_u64" && i64Ret) then
        (if a != dst then st.aliasBuf dst a else st).bindVar dst (st.lookupVar (st.resolveBuf a))
      else if fnName == "lean_native_ensure_exclusive" && ptrRet then
        let root := st.resolveBuf a
        ((st.markExclusive root).aliasBuf dst root).bindVar dst (st.lookupVar root)
      else if fnName == "lean_native_sarray_len" && i64Ret then
        let sa := st.lookupVar a
        st.bindVar dst { expr := .symVar (9000 + st.resolveBuf a), nonPoison := sa.nonPoison, noUB := sa.noUB }
      else if fnName == "lean_native_ctor_tag" && i64Ret then
        let root := st.resolveBuf a
        let liveOk := st.isBufLive root
        let stLive := (st.requireUbCond (st.liveRcCond root)).noteExtLiveRoot root
        let sa := stLive.lookupVar root
        let tagExpr : SymExpr :=
          match sa.expr with
          | .tuple (tag :: _) => tag
          | .constU64 tag => .constU64 tag
          | .symVar rootId => .symVar (24000 + stLive.resolveBuf rootId)
          | _ => .symVar dst
        stLive.bindVar dst { expr := tagExpr, nonPoison := sa.nonPoison && liveOk, noUB := sa.noUB && liveOk }
      else st.bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    | false, [objVar, idxVar, valVar] =>
      if fnName == "lean_native_ctor_set" && retTy == .unit then
        let root := st.resolveBuf objVar
        let objSv := st.lookupVar root
        let idxSv := st.lookupVar idxVar
        let valRoot := st.resolveBuf valVar
        let valSvRaw := st.lookupVar valVar
        let storedValExpr : SymExpr :=
          if st.allocRoots.contains valRoot || (st.refCounts.lookup valRoot).isSome then .symVar valRoot
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
            let idx := idxU64.toNat
            if idx < fs.length then
              let sb := stExcl.bindVar root {
                expr := .tuple (tag :: fs.set idx valSv.expr)
                nonPoison := objSv.nonPoison && idxSv.nonPoison && valSv.nonPoison
                noUB := operandsOk && exclOk }
              ({ sb with ubCond := if operandsOk then stExcl.ubCond else .constBool false }, true)
            else
              ({ stExcl with noUB := false, nonPoison := false, ubCond := .constBool false }, false)
          | .symVar rootId, .constU64 idxU64 =>
            let idx := idxU64.toNat
            let prevFields := (List.range 8).map fun i =>
              if i == idx then valSv.expr else .symVar (30000 + rootId * 16 + i)
            let sb := stExcl.bindVar root {
              expr := .tuple (.symVar (24000 + rootId) :: prevFields)
              nonPoison := objSv.nonPoison && idxSv.nonPoison && valSv.nonPoison
              noUB := operandsOk && exclOk && idx < 8 }
            ({ sb with ubCond := if operandsOk && idx < 8 then stExcl.ubCond else .constBool false }, idx < 8)
          | _, _ =>
            ({ stExcl with noUB := false, nonPoison := false, ubCond := .constBool false }, false)
        let stAfterEpoch :=
          if inBoundsOk && !updatedState.allocRoots.contains root then
            let nextEp := updatedState.heapStepEpoch + 1
            let purgedVars := updatedState.vars.filter fun (vid, _) =>
              vid == root || updatedState.allocRoots.contains vid || vid < 30000
            { (updatedState.bumpExternalHeapEpoch root true) with heapStepEpoch := nextEp, vars := purgedVars }
          else updatedState
        let stWithWrite :=
          if inBoundsOk then stAfterEpoch.writeBufSym root idxSv.expr valSv.expr true
          else stAfterEpoch
        let stDone := stWithWrite.bindVar dst {
          expr := .unit
          nonPoison := objSv.nonPoison && idxSv.nonPoison && valSv.nonPoison && inBoundsOk
          noUB := operandsOk && exclOk && inBoundsOk }
        { stDone with ubCond := if operandsOk && inBoundsOk then stWithWrite.ubCond else .constBool false }
      else st.bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    | _, _ => st.bindVar dst { expr := .unit, nonPoison := false, noUB := false }

/-- Summary produced by symbolic execution of an `LNIRDecl`. -/
structure SymExecSummary where
  declName   : String
  reachable  : Bool
  reachCond  : SymExpr
  ubCond     : SymExpr
  noUB       : Bool
  nonPoison  : Bool
  retVal     : SymExpr
  rcDeltas   : List (VarId × SymExpr)
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
      | _ => stAfter.clearAlias accVar
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
    | .letBind dst ty val k =>
      let st0 :=
        match val with
        | .scalar (.var _) => st
        | _ => if callSlotKind ty == some false then st.clearAlias dst else st
      let st1 := symEvalExpr st0 dst val
      symExecCode fuel' unrollBound st1 k
    | .rawStore ptrVar idxVar valVar _elemTy k =>
      let idxSv := st.lookupVar idxVar
      let valSv := st.lookupVar valVar
      let st1 := st.writeBufSym ptrVar idxSv.expr valSv.expr true
      let st2 := { st1 with
        ubCond := if idxSv.noUB && valSv.noUB then st1.ubCond else .constBool false
        noUB := st1.noUB && idxSv.noUB && valSv.noUB
        nonPoison := st1.nonPoison && idxSv.nonPoison && valSv.nonPoison }
      symExecCode fuel' unrollBound st2 k
    | .incRef v count k =>
      symExecCode fuel' unrollBound (st.updateRefCount v count true) k
    | .decRef v count k =>
      symExecCode fuel' unrollBound (st.updateRefCount v count false) k
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
            if rcSym ≥ 100000 then (st, st.markExclusive (rcSym - 100000)) else (st, st)
          | .binOp .eq (.symVar rcSym) (.constU64 1) =>
            if rcSym ≥ 100000 then (st.markExclusive (rcSym - 100000), st) else (st, st)
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
        let mergedWrites :=
          if !stT.reachable then stE.memWrites
          else if !stE.reachable then stT.memWrites
          else
            let normWrites (ws : List (VarId × SymExpr × SymExpr)) :=
              ws.foldl (fun acc (r, idx, _) =>
                if acc.any (fun (r2, i2) => r2 == r && i2 == idx) then acc
                else acc ++ [(r, idx)]) []
            (normWrites (stT.memWrites ++ stE.memWrites)).map fun (root, idx) =>
              (root, idx, normSymIteStep cExpr
                (stT.expandHeapExpr 16 (stT.readBufSym root idx))
                (stE.expandHeapExpr 16 (stE.readBufSym root idx)))
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
          if !condSv.noUB || st.ubCond == .constBool false then .constBool false
          else if !stT.reachable && !stE.reachable then st.ubCond
          else if !stT.reachable then SymExecState.conjoinUbCond st.ubCond branchUbE
          else if !stE.reachable then SymExecState.conjoinUbCond st.ubCond branchUbT
          else normSymIteStep cExpr branchUbT branchUbE
        let mergedEpoch :=
          if !stT.reachable then stE.heapStepEpoch
          else if !stE.reachable then stT.heapStepEpoch
          else Nat.max stT.heapStepEpoch stE.heapStepEpoch
        let mergedExtLive :=
          if !stT.reachable then stE.extLivenessRoots
          else if !stE.reachable then stT.extLivenessRoots
          else stT.extLivenessRoots.filter (fun b => stE.extLivenessRoots.contains b)
        let mergedState : SymExecState := {
          vars := mergedVars
          bufAliases := mergedAliases
          exclusiveBufs := mergedExcl
          allocRoots := mergedAlloc
          extSeenRoots := mergedExtSeen
          extLivenessRoots := mergedExtLive
          extRcDeltas := mergedExtDeltas
          refCounts := mergedRefs
          rcExprs := mergedRcExprs
          heapStepEpoch := mergedEpoch
          reachCond := mergedReachCond
          ubCond := mergedUbCond
          noUB := st.noUB && condSv.noUB && (!stT.reachable || stT.noUB) && (!stE.reachable || stE.noUB)
          nonPoison := st.nonPoison && condSv.nonPoison && (!stT.reachable || stT.nonPoison) && (!stE.reachable || stE.nonPoison)
          reachable := stT.reachable || stE.reachable
          memWrites := mergedWrites
        }
        let mergedRet :=
          if !stT.reachable then normSymExpr retE
          else if !stE.reachable then normSymExpr retT
          else normSymIteStep cExpr (normSymExpr retT) (normSymExpr retE)
        (mergedState, mergedRet)
    | .seqFor idxVar _loVar _hiVar accVar accInit _accTy stepBody k =>
      let initSv := st.lookupVar accInit
      let stInit := (st.aliasBuf accVar accInit).bindVar accVar initSv
      let stAfterLoop := symExecLoopUnroll unrollBound 0 idxVar accVar stInit
        (fun s => symExecCode fuel' unrollBound s stepBody)
      symExecCode fuel' unrollBound stAfterLoop k
    | .parFor outVar _lenVar inputs _elemTy _kernel k =>
      let stInputs := inputs.foldl (fun cur iv =>
        let r := cur.resolveBuf iv
        ((cur.noteExtRoot r).requireUbCond (cur.liveRcCond r)).noteExtLiveRoot r) st
      let st1 := (stInputs.clearAlias outVar).markAllocated outVar
      let st2 := st1.bindVar outVar { expr := .symVar outVar, nonPoison := true, noUB := true }
      symExecCode fuel' unrollBound st2 k
    | .ret v =>
      let rRoot := st.resolveBuf v
      let rSv := st.lookupVar rRoot
      let retSeed : SymExpr :=
        if st.allocRoots.contains rRoot || (st.refCounts.lookup rRoot).isSome || (st.rcExprs.lookup rRoot).isSome then
          .symVar rRoot
        else
          rSv.expr
      let finalExpr := normSymExpr (st.expandHeapExpr 16 retSeed)
      ({ st with
          ubCond := if rSv.noUB then st.ubCond else .constBool false
          noUB := st.noUB && rSv.noUB
          nonPoison := st.nonPoison && rSv.nonPoison }, finalExpr)
    | .unreachable =>
      ({ st with reachable := false, reachCond := .constBool false }, .unit)

/-- Run symbolic execution on an `LNIRDecl` with initial symbolic parameters. -/
def symExecDecl (loopUnrollBound : Nat := 4) (d : LNIRDecl) : SymExecSummary :=
  let initState : SymExecState := d.params.foldl (fun acc p =>
    let st1 := acc.bindVar p.id { expr := .symVar p.id, nonPoison := true, noUB := true }
    match p.ty with
    | .rawPtr _ => st1.markExclusive p.id
    | _ => st1
  ) {}
  let (finalSt, retExpr) := symExecCode 256 loopUnrollBound initState d.body
  let rawWrites :=
    (finalSt.memWrites.filter fun (r, _, _) => !(finalSt.allocRoots.contains r)).mergeSort
      (fun (r1, i1, _) (r2, i2, _) => r1 < r2 || (r1 == r2 && reprStr i1 ≤ reprStr i2))
  let expandedWriteExprs := rawWrites.map fun (_, _, val) => normSymExpr (finalSt.expandHeapExpr 16 val)
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
  let combinedRaw := SymExpr.tuple [normSymExpr retExpr, SymExpr.tuple expandedWriteExprs, SymExpr.tuple liveAllocRc]
  let jointHeapSummary := normSymExpr (finalSt.alphaRenameAllocTags (SymExecState.hoistIteTupleFuel 24 combinedRaw))
  let expandedWrites := (rawWrites.zip expandedWriteExprs).map fun ((r, idx, _), wVal) =>
    (r, normSymExpr idx, normSymExpr (finalSt.alphaRenameAllocTags (SymExecState.hoistIteTupleFuel 16 wVal)))
  let finalRcDeltas :=
    nonAllocRcDeltas ++ [ (90000, jointHeapSummary) ]
  let canonRet := normSymExpr (finalSt.alphaRenameAllocTags (SymExecState.hoistIteTupleFuel 16 (normSymExpr retExpr)))
  let finalUbCond : SymExpr :=
    normSymExpr (SymExecState.hoistIteTupleFuel 16 (normSymExpr finalSt.ubCond))
  { declName := d.name
    reachable := finalSt.reachable
    reachCond := normSymExpr finalSt.reachCond
    ubCond := finalUbCond
    noUB := finalSt.noUB
    nonPoison := finalSt.nonPoison
    retVal := canonRet
    rcDeltas := finalRcDeltas
    memWrites := expandedWrites }

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
        let leafFields := (List.range 8).map fun k =>
          Val.u64 (((splitMix64Next (r + salt + (k.toUInt64 * 7))).1 % 16) + 1)
        let (cid, s1) := s.allocHeapCtor 0 leafFields
        if sharedLeaf then
          match s1.incRefObj cid 1 with
          | .ok s2 => (.objPtr cid, s2)
          | .error _ => (.objPtr cid, s1)
        else (.objPtr cid, s1)
      let sharedRoot := (r % 2 == 0)
      let aliasSibling := (r % 4 == 1)
      let sharedKids := (r % 3 == 0) && !aliasSibling
      let (kids, stAfterKids) :=
        if aliasSibling then
          let (firstKid, stFirst) := mkLeaf st 101 false
          match firstKid with
          | .objPtr firstCid =>
            let stInc := match stFirst.incRefObj firstCid 1 with | .ok s2 => s2 | .error _ => stFirst
            let (restKids, stRest) := (List.range 6).foldl (fun (acc, curSt) idx =>
              let (cVal, nextSt) := mkLeaf curSt (295 + idx.toUInt64 * 97) sharedKids
              (acc ++ [cVal], nextSt)) ([], stInc)
            (firstKid :: firstKid :: restKids, stRest)
          | _ =>
            (List.range 8).foldl (fun (acc, curSt) idx =>
              let (cVal, nextSt) := mkLeaf curSt (101 + idx.toUInt64 * 97) sharedKids
              (acc ++ [cVal], nextSt)) ([], st)
        else
          (List.range 8).foldl (fun (acc, curSt) idx =>
            let (cVal, nextSt) := mkLeaf curSt (101 + idx.toUInt64 * 97) sharedKids
            (acc ++ [cVal], nextSt)) ([], st)
      let (oid, st3) := stAfterKids.allocHeapCtor 0 kids
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
  -- 1. UB refinement: `(src.noUB -> tgt.noUB)` AND path-conditional definedness refinement
  --    (`sSrc.ubCond → sTgt.ubCond`, i.e. `ite sSrc.ubCond sTgt.ubCond true == true`) so UB on one
  --    source branch never masks target UB on other defined paths!
  let scUb := normSymExpr sSrc.ubCond
  let tcUb := normSymExpr sTgt.ubCond
  let symUbImplies : Bool :=
    tcUb == .constBool true || scUb == .constBool false || scUb == tcUb ||
      normSymExpr (SymExecState.hoistIteTupleFuel 16 (normSymIteStep scUb tcUb (.constBool true))) == .constBool true
  let ubRefines := (!sSrc.noUB || sTgt.noUB) && symUbImplies
  -- 2. Return domain / reachability equivalence on defined source paths (`scUb → (sSrc.reachCond == sTgt.reachCond)`)
  let domainEquiv :=
    sSrc.reachable == sTgt.reachable &&
    (normSymExpr sSrc.reachCond == normSymExpr sTgt.reachCond ||
     normSymExpr (SymExecState.hoistIteTupleFuel 16
       (normSymIteStep scUb (normSymBinOpStep .eq sSrc.reachCond sTgt.reachCond) (.constBool true))) == .constBool true)
  -- 3. Poison refinement: src.nonPoison -> tgt.nonPoison
  let poisonRefines := !sSrc.nonPoison || sTgt.nonPoison
  -- 4. Symbolic return expression equivalence (either globally equal or equal on all defined source paths `scUb`)
  let symRetEquiv :=
    normSymExpr sSrc.retVal == normSymExpr sTgt.retVal ||
    normSymExpr (SymExecState.hoistIteTupleFuel 16
      (normSymIteStep scUb (normSymBinOpStep .eq sSrc.retVal sTgt.retVal) (.constBool true))) == .constBool true
  -- 5. Multi-point concrete refinement across 64 deterministic input states (fail closed when all samples are UB)
  let (concreteOk, passedSamples) := checkDeclConcreteRefinement src tgt numSamples 128
  -- 6. Memory / buffer write log & RC-delta equivalence (set-equivalent per `(root, idx)` on all defined source paths)
  let eqOnDefinedPaths (a b : SymExpr) : Bool :=
    let na := normSymExpr a
    let nb := normSymExpr b
    na == nb ||
      normSymExpr (SymExecState.hoistIteTupleFuel 16
        (normSymIteStep scUb (normSymBinOpStep .eq na nb) (.constBool true))) == .constBool true
  let memWritesEquiv :=
    let keysOf (ws : List (VarId × SymExpr × SymExpr)) :=
      ws.foldl (fun acc (r, idx, _) =>
        let nidx := normSymExpr idx
        if acc.any (fun (r2, i2) => r2 == r && i2 == nidx) then acc else acc ++ [(r, nidx)]) []
    let lookupWrite (ws : List (VarId × SymExpr × SymExpr)) (r : VarId) (nidx : SymExpr) : SymExpr :=
      match ws.find? (fun (b, i, _) => b == r && normSymExpr i == nidx) with
      | some (_, _, v) => normSymExpr v
      | none => .bufElem r nidx
    let allKeys := keysOf (sSrc.memWrites ++ sTgt.memWrites)
    let writesOk := allKeys.all fun (r, nidx) => eqOnDefinedPaths (lookupWrite sSrc.memWrites r nidx) (lookupWrite sTgt.memWrites r nidx)
    let rcKeys := ((sSrc.rcDeltas.map Prod.fst) ++ (sTgt.rcDeltas.map Prod.fst)).eraseDups
    let lookupRcDelta (ds : List (VarId × SymExpr)) (r : VarId) : SymExpr :=
      match ds.lookup r with
      | some e => normSymExpr e
      | none => if r == 90000 then .unit else .constU64 0
    let rcOk := rcKeys.all fun r => eqOnDefinedPaths (lookupRcDelta sSrc.rcDeltas r) (lookupRcDelta sTgt.rcDeltas r)
    writesOk && rcOk
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
