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
  | ctorObj   (tag : UInt64) (objs : List SymExpr) (scalars : List SymExpr)
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
  | .ctorObj _ os ss => 5500 + os.length + ss.length
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
    | .ctorObj tag os ss => .ctorObj tag (normSymExprList os) (normSymExprList ss)
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
  rootRc        : List (VarId × Nat × Option Nat) := []
  objRoots      : List (VarId × List (Option VarId)) := []
  tupleRoots    : List (VarId × List (Option VarId)) := []
  nextAllocSeq  : Nat := 0
  rcEpoch       : Nat := 0
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

def setRootRc (st : SymExecState) (root : VarId) (minRc : Nat) (exactRc? : Option Nat) : SymExecState :=
  let restExcl := st.exclusiveBufs.filter (· != root)
  let excl' := if exactRc? == some 1 then root :: restExcl else restExcl
  let rc' := if st.rootRc.any (fun (id, _) => id == root) then
    st.rootRc.map (fun (id, m, ex?) => if id == root then (root, minRc, exactRc?) else (id, m, ex?))
  else
    st.rootRc ++ [(root, minRc, exactRc?)]
  { st with rootRc := rc', exclusiveBufs := excl' }

def getRootRc (st : SymExecState) (bufVar : VarId) : Nat × Option Nat :=
  let root := st.resolveBuf bufVar
  match st.rootRc.lookup root with
  | some rcInfo => rcInfo
  | none => if st.exclusiveBufs.contains root then (1, some 1) else (1, none)

def markExclusive (st : SymExecState) (bufVar : VarId) : SymExecState :=
  st.setRootRc (st.resolveBuf bufVar) 1 (some 1)

def isBufExclusive (st : SymExecState) (bufVar : VarId) : Bool :=
  let (_, exactRc?) := st.getRootRc bufVar
  exactRc? == some 1

def incRootRc (st : SymExecState) (objVar : VarId) (count : Nat) : SymExecState :=
  let root := st.resolveBuf objVar
  let sv := st.lookupVar root
  match sv.expr with
  | .constU64 _ | .constBool _ | .unit | .tuple _ => st
  | _ =>
    let (minRc, exactRc?) := st.getRootRc root
    if minRc == 0 || exactRc? == some 0 then { st with noUB := false }
    else if count == 0 then st
    else
      let st1 := st.setRootRc root (minRc + count) (exactRc?.map (· + count))
      { st1 with rcEpoch := st1.rcEpoch + 1 }

private def dedupIds (xs : List VarId) : List VarId :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

def mergeBranches (base stT stE : SymExecState) (cExpr : SymExpr) (condNoUB condNonPoison : Bool) : SymExecState :=
  let rcKeys := dedupIds (base.rootRc.map (·.1) ++ stT.rootRc.map (·.1) ++ stE.rootRc.map (·.1) ++
    base.exclusiveBufs ++ stT.exclusiveBufs ++ stE.exclusiveBufs)
  let mergedRc := rcKeys.map fun r =>
    let (mT, eT) := stT.getRootRc r
    let (mE, eE) := stE.getRootRc r
    (r, Nat.min mT mE, if eT == eE then eT else none)
  let mergedExcl := mergedRc.filterMap fun (r, _, ex) => if ex == some 1 then some r else none
  let aliasKeys := dedupIds (base.bufAliases.map (·.1) ++ stT.bufAliases.map (·.1) ++ stE.bufAliases.map (·.1))
  let mergedAliases := aliasKeys.filterMap fun v =>
    let rT := stT.resolveBuf v
    let rE := stE.resolveBuf v
    if rT == rE && rT != v then some (v, rT) else none
  let varKeys := dedupIds (base.vars.map (·.1) ++ stT.vars.map (·.1) ++ stE.vars.map (·.1))
  let mergedVars := varKeys.map fun v =>
    let svT := stT.lookupVar v
    let svE := stE.lookupVar v
    let expr := if svT.expr == svE.expr then svT.expr else normSymIteStep cExpr svT.expr svE.expr
    (v, { expr := expr, nonPoison := svT.nonPoison && svE.nonPoison, noUB := svT.noUB && svE.noUB })
  let objKeys := dedupIds (base.objRoots.map (·.1) ++ stT.objRoots.map (·.1) ++ stE.objRoots.map (·.1))
  let mergedObjRoots := objKeys.filterMap fun r =>
    match stT.objRoots.lookup r, stE.objRoots.lookup r with
    | some fsT, some fsE => if fsT == fsE then some (r, fsT) else none
    | _, _ => none
  let tupKeys := dedupIds (base.tupleRoots.map (·.1) ++ stT.tupleRoots.map (·.1) ++ stE.tupleRoots.map (·.1))
  let mergedTupleRoots := tupKeys.filterMap fun v =>
    match stT.tupleRoots.lookup v, stE.tupleRoots.lookup v with
    | some fsT, some fsE => if fsT == fsE then some (v, fsT) else none
    | _, _ => none
  { vars := mergedVars
    bufAliases := mergedAliases
    exclusiveBufs := mergedExcl
    rootRc := mergedRc
    objRoots := mergedObjRoots
    tupleRoots := mergedTupleRoots
    nextAllocSeq := Nat.max base.nextAllocSeq (Nat.max stT.nextAllocSeq stE.nextAllocSeq)
    rcEpoch :=
      let ep := Nat.max base.rcEpoch (Nat.max stT.rcEpoch stE.rcEpoch)
      if stT.rcEpoch == stE.rcEpoch then ep else ep + 1
    memWrites := if stT.memWrites == stE.memWrites then stT.memWrites else base.memWrites
    noUB := base.noUB && condNoUB && stT.noUB && stE.noUB
    nonPoison := base.nonPoison && condNonPoison && stT.nonPoison && stE.nonPoison
    reachable := stT.reachable || stE.reachable }

def hasHeapTuple (st : SymExecState) : Nat → VarId → Bool
  | 0, _ => false
  | d + 1, r =>
    match st.tupleRoots.lookup r with
    | some fs => fs.any fun
      | some cr => (st.rootRc.lookup cr).isSome || st.exclusiveBufs.contains cr || st.hasHeapTuple d cr
      | none => false
    | none => false

mutual
  def decRootRcFuel : Nat → Bool → SymExecState → VarId → Nat → SymExecState
    | 0, fromCtor, st, objVar, count =>
      if count == 0 then st
      else
        let root := st.resolveBuf objVar
        match (st.lookupVar root).expr with
        | .constU64 _ | .constBool _ | .unit => st
        | .tuple _ =>
          if !fromCtor then st
          else if st.hasHeapTuple 16 root || (st.tupleRoots.lookup root).isNone then { st with noUB := false }
          else st
        | _ => { st with noUB := false }
    | fuel + 1, fromCtor, st, objVar, count =>
      let root := st.resolveBuf objVar
      let sv := st.lookupVar root
      match sv.expr with
      | .constU64 _ | .constBool _ | .unit => st
      | .tuple _ =>
        if !fromCtor then st
        else if count == 0 then st
        else
          match st.tupleRoots.lookup root with
          | some fs => decRootListFuel fuel true st (fs.filterMap id) count
          | none => { st with noUB := false }
      | _ =>
        let (minRc, exactRc?) := st.getRootRc root
        match exactRc? with
        | some r =>
          if r == 0 || count > r then { st with noUB := false }
          else if count == 0 then st
          else
            let r' := r - count
            let st1 := st.setRootRc root r' (some r')
            if r' == 0 then
              let children := ((st1.objRoots.lookup root).getD []).filterMap id
              let st2 := { st1 with objRoots := st1.objRoots.filter (fun (id, _) => id != root) }
              decRootListFuel fuel true st2 children 1
            else st1
        | none =>
          if minRc == 0 then { st with noUB := false }
          else if count == 0 then st
          else
            let stShared := st.setRootRc root (minRc - count) none
            if minRc <= count then
              let children := ((st.objRoots.lookup root).getD []).filterMap id
              let stFreed0 :=
                { (st.setRootRc root 0 (some 0)) with objRoots := st.objRoots.filter (fun (id, _) => id != root) }
              let stFreed := decRootListFuel fuel true stFreed0 children 1
              mergeBranches st stShared stFreed (.symVar (500000 + root)) true true
            else stShared

  def decRootListFuel : Nat → Bool → SymExecState → List VarId → Nat → SymExecState
    | _, _, st, [], _ => st
    | 0, _, st, _ :: _, _ => { st with noUB := false }
    | fuel + 1, fromCtor, st, c :: cs, count =>
      decRootListFuel fuel fromCtor (decRootRcFuel fuel fromCtor st c count) cs count
end

def decRootRc (st : SymExecState) (objVar : VarId) (count : Nat) : SymExecState :=
  let objEdgeBudget := st.objRoots.foldl (fun acc (_, fs) => acc + fs.length + 2) 0
  let tupEdgeBudget := st.tupleRoots.foldl (fun acc (_, fs) => acc + fs.length + 2) 0
  let st1 := decRootRcFuel ((objEdgeBudget + tupEdgeBudget + 16) * (tupEdgeBudget + 1)) false st objVar count
  if count == 0 || st1.rootRc == st.rootRc then st1 else { st1 with rcEpoch := st1.rcEpoch + 1 }

def delRootShell (st : SymExecState) (objVar : VarId) : SymExecState :=
  let root := st.resolveBuf objVar
  let sv := st.lookupVar root
  match sv.expr with
  | .constU64 _ | .constBool _ | .unit | .tuple _ => st
  | _ =>
    let (_, exactRc?) := st.getRootRc root
    if exactRc? != some 1 then { st with noUB := false }
    else
      { (st.setRootRc root 0 (some 0)) with
        objRoots := st.objRoots.filter (fun (id, _) => id != root)
        rcEpoch := st.rcEpoch + 1 }

def bindObjRoots (st : SymExecState) (root : VarId) (fields : List (Option VarId)) : SymExecState :=
  { st with objRoots := (root, fields) :: st.objRoots.filter (fun (id, _) => id != root) }

def lookupObjRootField (st : SymExecState) (ctorVar : VarId) (idx : Nat) : Option VarId :=
  let root := st.resolveBuf ctorVar
  match st.objRoots.lookup root with
  | some fs => (fs[idx]?).join
  | none => none

def bindTupleRoots (st : SymExecState) (v : VarId) (fields : List (Option VarId)) : SymExecState :=
  { st with tupleRoots := (v, fields) :: st.tupleRoots.filter (fun (id, _) => id != v) }

def lookupTupleRootField (st : SymExecState) (tupleVar : VarId) (idx : Nat) : Option VarId :=
  match st.tupleRoots.lookup (st.resolveBuf tupleVar) with
  | some fs => (fs[idx]?).join
  | none => none

def trackedTupleParamRoots : Nat → UInt64 → LNIRType → SymExecState → Option VarId × SymExecState
  | 0, _, _, st => (none, st)
  | depth + 1, path, ty, st =>
    match ty with
    | .rawPtr _ =>
      let r := (150000 + path.toNat : VarId)
      (some r, st.markExclusive r)
    | .objPtr | .taggedPtr | .sarray _ | .storageMap =>
      let r := (150000 + path.toNat : VarId)
      (some r, st.setRootRc r 1 none)
    | .tuple fs =>
      let r := (150000 + path.toNat : VarId)
      let (childRoots, st1, _) := fs.foldl (fun (acc, curSt, idx) fty =>
        let (cr?, nextSt) := trackedTupleParamRoots depth (path * 16 + idx.toUInt64 + 1) fty curSt
        (acc ++ [cr?], nextSt, idx + 1)) ([], st, 0)
      let st2 := (st1.bindTupleRoots r childRoots).bindVar r
        { expr := .tuple ((List.range fs.length).map (fun i =>
            match (childRoots[i]?).join with
            | some cr =>
              let csv := st1.lookupVar cr
              if csv.expr matches .tuple _ then csv.expr
              else if (st1.rootRc.lookup cr).isSome || st1.exclusiveBufs.contains cr then .symVar cr
              else .symVar (100000 + r * 16 + i)
            | none => .symVar (100000 + r * 16 + i))) }
      (some r, st2)
    | .u256 | .i256 =>
      let r := (150000 + path.toNat : VarId)
      let st2 := (st.bindTupleRoots r [none, none, none, none]).bindVar r
        { expr := .tuple ((List.range 4).map (fun i => .symVar (100000 + r * 16 + i))) }
      (some r, st2)
    | _ => (none, st)

def isHeapish (st : SymExecState) (v : VarId) : Bool :=
  let root := st.resolveBuf v
  let sv := st.lookupVar root
  match sv.expr with
  | .constU64 _ | .constBool _ | .unit => false
  | .tuple _ => st.hasHeapTuple 16 root
  | .ctorObj .. => true
  | .symVar _ =>
    if (st.tupleRoots.lookup root).isSome then st.hasHeapTuple 16 root else true
  | _ => (st.rootRc.lookup root).isSome

def trackedRoot? (st : SymExecState) (v : VarId) : Option VarId :=
  let r := st.resolveBuf v
  let hasTup := (st.tupleRoots.lookup r).isSome
  if (st.bufAliases.lookup v).isSome || (st.rootRc.lookup r).isSome || st.exclusiveBufs.contains r || hasTup then
    some r
  else
    none

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

def clearDstTracking (st : SymExecState) (dst : VarId) : SymExecState :=
  { st with
    bufAliases := st.bufAliases.filter (fun (id, _) => id != dst)
    tupleRoots := st.tupleRoots.filter (fun (id, _) => id != dst) }

def allocFresh (st : SymExecState) : VarId × SymExecState :=
  (170000 + st.nextAllocSeq, { st with nextAllocSeq := st.nextAllocSeq + 1 })

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
    let st0 := st.clearDstTracking dst
    let st1 := match se with
      | .var src => match st.trackedRoot? src with | some r => st0.aliasBuf dst r | none => st0
      | _ => st0
    let sv' := match se with
      | .var src =>
        match st.trackedRoot? src with
        | some r =>
          if st.isHeapish src then
            match sv.expr with
            | .symVar _ => { sv with expr := .symVar r }
            | _ => sv
          else sv
        | none => sv
      | _ => sv
    st1.bindVar dst sv'
  | .constU256 val =>
    let st0 := st.clearDstTracking dst
    let symVal : SymExpr :=
      if val.lo1 == 0 && val.hi0 == 0 && val.hi1 == 0 then
        .constU64 val.lo0
      else
        .tuple [.constU64 val.lo0, .constU64 val.lo1, .constU64 val.hi0, .constU64 val.hi1]
    let st1 := if symVal matches .tuple _ then st0.bindTupleRoots dst [none, none, none, none] else st0
    st1.bindVar dst { expr := symVal, nonPoison := true, noUB := true }
  | .mulDivDown aVar bVar denomVar | .mulDivUp aVar bVar denomVar =>
    let st0 := st.clearDstTracking dst
    let sa := st.lookupVar aVar
    let sb := st.lookupVar bVar
    let sd := st.lookupVar denomVar
    let divZero := sd.expr == .constU64 0
    let mulExpr := normSymBinOpStep .mul sa.expr sb.expr
    let numExpr :=
      match e with
      | .mulDivUp _ _ _ => normSymBinOpStep .add mulExpr (normSymBinOpStep .sub sd.expr (.constU64 1))
      | _ => mulExpr
    st0.bindVar dst {
      expr := normSymBinOpStep .div numExpr sd.expr
      nonPoison := sa.nonPoison && sb.nonPoison && sd.nonPoison
      noUB := sa.noUB && sb.noUB && sd.noUB && !divZero
    }
  | .storageLoad mapVar slotVar | .sarrayGet mapVar slotVar _ | .rawLoad mapVar slotVar _ =>
    let st0 := st.clearDstTracking dst
    let slotSv := st.lookupVar slotVar
    let elemExpr := st.readBufSym mapVar slotSv.expr
    st0.bindVar dst { expr := elemExpr, nonPoison := slotSv.nonPoison, noUB := slotSv.noUB }
  | .storageStore mapVar slotVar valVar =>
    let root := st.resolveBuf mapVar
    let slotSv := st.lookupVar slotVar
    let valSv := st.lookupVar valVar
    let st1 := ((st.clearDstTracking dst).writeBufSym root slotSv.expr valSv.expr false).aliasBuf dst root
    st1.bindVar dst { expr := .symVar root, nonPoison := slotSv.nonPoison && valSv.nonPoison, noUB := slotSv.noUB && valSv.noUB }
  | .mkTuple fields =>
    let svs := fields.map st.lookupVar
    let roots := fields.map fun f => st.trackedRoot? f
    let tupSv : SymStateVal :=
      { expr := .tuple (svs.map (·.expr)), nonPoison := svs.all (·.nonPoison), noUB := svs.all (·.noUB) }
    let (freshTupId, stSeq) := st.allocFresh
    let st0 := stSeq.clearDstTracking dst
    let st1 := ((st0.bindTupleRoots freshTupId roots).bindVar freshTupId tupSv).aliasBuf dst freshTupId
    st1.bindVar dst tupSv
  | .projTuple tupleVar idx =>
    let tv := st.lookupVar tupleVar
    let fieldRoot? := st.lookupTupleRootField tupleVar idx
    let st0 := st.clearDstTracking dst
    let stA := match fieldRoot? with
      | some r => st0.aliasBuf dst r
      | none => st0
    match tv.expr with
    | .tuple fs =>
      match fs[idx]? with
      | some fExpr =>
        let fExpr' := match fieldRoot?, fExpr with
          | some r, .symVar _ => if (st.rootRc.lookup r).isSome || st.exclusiveBufs.contains r then .symVar r else fExpr
          | _, _ => fExpr
        stA.bindVar dst { expr := fExpr', nonPoison := tv.nonPoison, noUB := tv.noUB }
      | none => st0.bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    | .ctorObj tag _ _ =>
      let (minRc, exactRc?) := st.getRootRc tupleVar
      let liveOk := minRc > 0 && exactRc? != some 0
      if idx == 0 then st0.bindVar dst { expr := .constU64 tag, nonPoison := tv.nonPoison, noUB := tv.noUB && liveOk }
      else st0.bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    | .symVar base =>
      let r := match fieldRoot? with
        | some known => known
        | none => 100000 + base * 16 + idx
      let curFs := st.tupleRoots.lookup (st.resolveBuf tupleVar)
      let st1 := match fieldRoot?, curFs with
        | none, none =>
          let stR := if (st0.rootRc.lookup r).isSome then st0 else st0.setRootRc r 1 none
          stR.aliasBuf dst r
        | _, _ => stA
      let outExpr := match fieldRoot? with
        | some kr =>
          let ksv := st.lookupVar kr
          if ksv.expr matches .tuple _ then ksv.expr
          else if (st.rootRc.lookup kr).isSome || st.exclusiveBufs.contains kr then .symVar kr
          else .symVar (100000 + base * 16 + idx)
        | none => .symVar (100000 + base * 16 + idx)
      st1.bindVar dst { expr := outExpr, nonPoison := tv.nonPoison, noUB := tv.noUB }
    | _ =>
      let outExpr := match fieldRoot? with | some r => .symVar r | none => .symVar dst
      stA.bindVar dst { expr := outExpr, nonPoison := tv.nonPoison, noUB := tv.noUB }
  | .allocCtor tag objFields scalarFields =>
    let osvs := objFields.map st.lookupVar
    let ssvs := scalarFields.map st.lookupVar
    let allSvs := osvs ++ ssvs
    let (freshId, stSeq) := st.allocFresh
    let childRoots := objFields.map fun f =>
      if st.isHeapish f then some (st.trackedRoot? f |>.getD (st.resolveBuf f)) else none
    let st0 := stSeq.clearDstTracking dst
    let ctorSv : SymStateVal := {
      expr := .ctorObj tag.toUInt64 (osvs.map (·.expr)) (ssvs.map (·.expr))
      nonPoison := allSvs.all (·.nonPoison)
      noUB := allSvs.all (·.noUB) }
    let st1 := ((st0.setRootRc freshId 1 (some 1)).bindObjRoots freshId childRoots).aliasBuf dst freshId
    (st1.bindVar freshId ctorSv).bindVar dst ctorSv
  | .ctorGetObj ctorVar idx =>
    let cv := st.lookupVar ctorVar
    let ctorRoot := st.resolveBuf ctorVar
    let (minRc, exactRc?) := st.getRootRc ctorRoot
    let liveOk := minRc > 0 && exactRc? != some 0
    let stBase := st.clearDstTracking dst
    match cv.expr with
    | .ctorObj _ os _ =>
      let stA := match st.lookupObjRootField ctorRoot idx with
        | some r => stBase.aliasBuf dst r
        | none => stBase
      match os[idx]? with
      | some fExpr => stA.bindVar dst { expr := fExpr, nonPoison := cv.nonPoison, noUB := cv.noUB && liveOk }
      | none => stBase.bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    | .symVar base =>
      let r := match st.lookupObjRootField ctorRoot idx with
        | some known => known
        | none => 200000 + base * 16 + idx
      let curFs := (st.objRoots.lookup ctorRoot).getD []
      let st0 := if (stBase.rootRc.lookup r).isSome then stBase else stBase.setRootRc r 1 none
      let padded := curFs ++ List.replicate (idx - curFs.length) none
      let nextFs := if idx < padded.length then padded.set idx (some r) else padded ++ [some r]
      let st1 := st0.bindObjRoots ctorRoot nextFs
      (st1.aliasBuf dst r).bindVar dst
        { expr := .symVar r, nonPoison := cv.nonPoison, noUB := cv.noUB && liveOk }
    | _ =>
      let r := match st.lookupObjRootField ctorRoot idx with
        | some known => known
        | none => 250000 + dst
      let stA := if (stBase.rootRc.lookup r).isSome then stBase else stBase.setRootRc r 1 none
      (stA.aliasBuf dst r).bindVar dst { expr := .symVar r, nonPoison := cv.nonPoison, noUB := cv.noUB && liveOk }
  | .ctorGetScalar ctorVar idx _ =>
    let cv := st.lookupVar ctorVar
    let (minRc, exactRc?) := st.getRootRc ctorVar
    let liveOk := minRc > 0 && exactRc? != some 0
    let st0 := st.clearDstTracking dst
    match cv.expr with
    | .ctorObj _ _ ss =>
      match ss[idx]? with
      | some fExpr => st0.bindVar dst { expr := fExpr, nonPoison := cv.nonPoison, noUB := cv.noUB && liveOk }
      | none => st0.bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    | .symVar base =>
      st0.bindVar dst
        { expr := .symVar (300000 + base * 16 + idx), nonPoison := cv.nonPoison, noUB := cv.noUB && liveOk }
    | _ => st0.bindVar dst { expr := .symVar dst, nonPoison := cv.nonPoison, noUB := cv.noUB && liveOk }
  | .isExclusive objVar =>
    let ov := st.lookupVar objVar
    let root := st.resolveBuf objVar
    let st0 := st.clearDstTracking dst
    let (minRc, exactRc?) := st.getRootRc root
    if minRc == 0 || exactRc? == some 0 then
      st0.bindVar dst { expr := .constBool false, nonPoison := ov.nonPoison, noUB := false }
    else
      let expr :=
        if exactRc? == some 1 then .constBool true
        else if minRc >= 2 then .constBool false
        else match ov.expr with
          | .ctorObj .. => .symVar (400000 + root)
          | .symVar _ =>
            if root >= 170000 && root < 200000 then .symVar (400000 + root)
            else .symVar (400000 + st.rcEpoch * 8192 + (root % 8192))
          | _ => .constBool true
      st0.bindVar dst { expr := expr, nonPoison := ov.nonPoison, noUB := ov.noUB }
  | .sarrayLen arrVar =>
    let root := st.resolveBuf arrVar
    let st0 := st.clearDstTracking dst
    st0.bindVar dst { expr := .symVar (9000 + root), nonPoison := true, noUB := true }
  | .sarrayDataPtr arrVar _elemTy =>
    let root := st.resolveBuf arrVar
    let exclOk := st.isBufExclusive root
    ((st.clearDstTracking dst).aliasBuf dst root).bindVar dst { expr := .symVar root, nonPoison := true, noUB := exclOk }
  | .sarrayEnsureExclusive arrVar _elemTy =>
    let root := st.resolveBuf arrVar
    let st1 := (((st.clearDstTracking dst).markExclusive root).aliasBuf dst root).bindVar dst
      { expr := .symVar root, nonPoison := true, noUB := true }
    { st1 with rcEpoch := st1.rcEpoch + 1 }
  | .sarraySet arrVar idxVar valVar _elemTy =>
    let root := st.resolveBuf arrVar
    let idxSv := st.lookupVar idxVar
    let valSv := st.lookupVar valVar
    let st3 := (((st.clearDstTracking dst).markExclusive root).writeBufSym root idxSv.expr valSv.expr true).aliasBuf dst root
    let st4 := st3.bindVar dst { expr := .symVar root, nonPoison := idxSv.nonPoison && valSv.nonPoison, noUB := idxSv.noUB && valSv.noUB }
    { st4 with rcEpoch := st4.rcEpoch + 1 }
  | .boxScalar valVar _ | .unboxScalar valVar _ =>
    let sv := st.lookupVar valVar
    let st0 := st.clearDstTracking dst
    let st1 := match st.trackedRoot? valVar with | some r => st0.aliasBuf dst r | none => st0
    let sv' := match st.trackedRoot? valVar, sv.expr with
      | some r, .symVar _ => { sv with expr := .symVar r }
      | _, _ => sv
    st1.bindVar dst sv'
  | .call fnName args retTy isExt =>
    let ptrRet := callSlotKind retTy == some true
    let i64Ret := callSlotKind retTy == some false
    let st0 := st.clearDstTracking dst
    match isExt, args with
    | false, [a] =>
      if (fnName == "lean_native_box_u64" && ptrRet) || (fnName == "lean_native_unbox_u64" && i64Ret) then
        let sv := st.lookupVar a
        let st1 := match st.trackedRoot? a with | some r => st0.aliasBuf dst r | none => st0
        let sv' := match st.trackedRoot? a, sv.expr with
          | some r, .symVar _ => { sv with expr := .symVar r }
          | _, _ => sv
        st1.bindVar dst sv'
      else if fnName == "lean_native_ensure_exclusive" && ptrRet then
        let root := st.resolveBuf a
        let st1 := ((st0.markExclusive root).aliasBuf dst root).bindVar dst (st.lookupVar a)
        { st1 with rcEpoch := st1.rcEpoch + 1 }
      else if fnName == "lean_native_sarray_len" && i64Ret then
        let sa := st.lookupVar a
        st0.bindVar dst { expr := .symVar (9000 + st.resolveBuf a), nonPoison := sa.nonPoison, noUB := sa.noUB }
      else if fnName == "lean_native_del_obj" && retTy == .unit then
        let sa := st.lookupVar a
        let st1 := st0.delRootShell a
        st1.bindVar dst { expr := .unit, nonPoison := sa.nonPoison, noUB := sa.noUB }
      else st0.bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    | _, _ => st0.bindVar dst { expr := .unit, nonPoison := false, noUB := false }

/-- Summary produced by symbolic execution of an `LNIRDecl`. -/
structure SymExecSummary where
  declName   : String
  reachable  : Bool
  noUB       : Bool
  nonPoison  : Bool
  retVal     : SymExpr
  memWrites  : List (VarId × SymExpr × SymExpr)
  liveRc     : List (VarId × Nat × Option Nat) := []
  deriving Repr, Inhabited, BEq

/-- Unroll a `seqFor` loop body `unrollCount` times symbolically. -/
def symExecLoopUnroll (unrollCount : Nat) (curIdx : Nat) (idxVar accVar : VarId)
    (st : SymExecState) (execBody : SymExecState → SymExecState × SymExpr × Option VarId) : SymExecState :=
  match unrollCount with
  | 0 => st
  | n + 1 =>
    let stIdx := (st.clearDstTracking idxVar).bindVar idxVar { expr := .constU64 curIdx.toUInt64, nonPoison := true, noUB := true }
    let (stAfter, retExpr, retRoot?) := execBody stIdx
    let stCleared := stAfter.clearDstTracking accVar
    let stNext :=
      match retRoot? with
      | some r => stCleared.aliasBuf accVar r
      | none => stCleared
    let stNextBound := stNext.bindVar accVar {
      expr := normSymExpr retExpr
      nonPoison := stAfter.nonPoison
      noUB := stAfter.noUB
    }
    symExecLoopUnroll n (curIdx + 1) idxVar accVar stNextBound execBody

private def symExecCodeAux (fuel : Nat) (unrollBound : Nat) (st : SymExecState) (code : LNIRCode) :
    SymExecState × SymExpr × Option VarId :=
  match fuel with
  | 0 => (st, .unit, none)
  | fuel' + 1 =>
    match code with
    | .letBind dst _ty val k =>
      let st1 := symEvalExpr st dst val
      symExecCodeAux fuel' unrollBound st1 k
    | .rawStore ptrVar idxVar valVar _elemTy k =>
      let idxSv := st.lookupVar idxVar
      let valSv := st.lookupVar valVar
      let st1 := st.writeBufSym ptrVar idxSv.expr valSv.expr true
      let st2 := { st1 with
        noUB := st1.noUB && idxSv.noUB && valSv.noUB
        nonPoison := st1.nonPoison && idxSv.nonPoison && valSv.nonPoison }
      symExecCodeAux fuel' unrollBound st2 k
    | .incRef objVar count k =>
      symExecCodeAux fuel' unrollBound (st.incRootRc objVar count) k
    | .decRef objVar count k =>
      symExecCodeAux fuel' unrollBound (st.decRootRc objVar count) k
    | .ite condVar thenBranch elseBranch =>
      let condSv := st.lookupVar condVar
      match condSv.expr with
      | .constBool true => symExecCodeAux fuel' unrollBound st thenBranch
      | .constBool false => symExecCodeAux fuel' unrollBound st elseBranch
      | .constU64 v =>
        if v != 0 then symExecCodeAux fuel' unrollBound st thenBranch
        else symExecCodeAux fuel' unrollBound st elseBranch
      | cExpr =>
        let (stT, retT, rootT?) := symExecCodeAux fuel' unrollBound st thenBranch
        let (stE, retE, rootE?) := symExecCodeAux fuel' unrollBound st elseBranch
        let mergedState := SymExecState.mergeBranches st stT stE cExpr condSv.noUB condSv.nonPoison
        let mergedRoot? := if rootT? == rootE? then rootT? else none
        (mergedState, normSymIteStep cExpr (normSymExpr retT) (normSymExpr retE), mergedRoot?)
    | .seqFor idxVar _loVar _hiVar accVar accInit _accTy stepBody k =>
      let initSv := st.lookupVar accInit
      let stCleared := st.clearDstTracking accVar
      let stAliased := match st.trackedRoot? accInit with
        | some r => stCleared.aliasBuf accVar r
        | none => stCleared
      let stInit := stAliased.bindVar accVar initSv
      let stAfterLoop := symExecLoopUnroll unrollBound 0 idxVar accVar stInit
        (fun s => symExecCodeAux fuel' unrollBound s stepBody)
      symExecCodeAux fuel' unrollBound stAfterLoop k
    | .parFor outVar _lenVar _inputs _elemTy _kernel k =>
      let st0 := st.clearDstTracking outVar
      let st1 := (st0.markExclusive outVar).bindVar outVar { expr := .symVar outVar, nonPoison := true, noUB := true }
      symExecCodeAux fuel' unrollBound st1 k
    | .ret v =>
      let rSv := st.lookupVar v
      let finalExpr := normSymExpr rSv.expr
      ({ st with
          noUB := st.noUB && rSv.noUB
          nonPoison := st.nonPoison && rSv.nonPoison }, finalExpr, st.trackedRoot? v)
    | .unreachable =>
      ({ st with reachable := false }, .unit, none)

def symExecCode (fuel : Nat) (unrollBound : Nat) (st : SymExecState) (code : LNIRCode) :
    SymExecState × SymExpr :=
  let (st', expr, _) := symExecCodeAux fuel unrollBound st code
  (st', expr)

/-- Run symbolic execution on an `LNIRDecl` with initial symbolic parameters. -/
def symExecDecl (loopUnrollBound : Nat := 4) (d : LNIRDecl) : SymExecSummary :=
  let initState : SymExecState := d.params.foldl (fun acc p =>
    let st1 := acc.bindVar p.id { expr := .symVar p.id, nonPoison := true, noUB := true }
    match p.ty with
    | .rawPtr _ => st1.markExclusive p.id
    | .objPtr | .taggedPtr | .sarray _ | .storageMap => st1.setRootRc p.id 1 none
    | .tuple fs =>
      let (childRoots, st2, _) := fs.foldl (fun (rs, curSt, idx) fty =>
        let (cr?, nextSt) := SymExecState.trackedTupleParamRoots 8 ((p.id + 1).toUInt64 * 256 + idx.toUInt64 + 1) fty curSt
        (rs ++ [cr?], nextSt, idx + 1)) ([], st1, 0)
      st2.bindTupleRoots p.id childRoots
    | .u256 | .i256 => st1.bindTupleRoots p.id [none, none, none, none]
    | _ => st1
  ) {}
  let (finalSt, retExpr) := symExecCode 4096 loopUnrollBound initState d.body
  let paramIds := d.params.map (·.id)
  let rawLive := finalSt.rootRc.filterMap fun (rid, m, ex?) =>
    let defaultUnknown := ((rid >= 100000 && rid < 170000) || (rid >= 200000 && rid < 300000)) && (m, ex?) == (1, none)
    if paramIds.contains rid || ex? == some 0 || defaultUnknown then none else some (rid, m, ex?)
  let canonLiveRc := paramIds.filterMap (fun pid =>
    let (m, ex?) := finalSt.getRootRc pid
    let initDefault := (initState.rootRc.lookup pid).getD (1, none)
    if (m, ex?) == initDefault then none else some (pid, m, ex?)) ++
    (rawLive.zipIdx.map fun ((rid, m, ex?), idx) =>
      (if rid >= 170000 && rid < 200000 then 170000 + idx else rid, m, ex?))
  { declName := d.name
    reachable := finalSt.reachable
    noUB := finalSt.noUB
    nonPoison := finalSt.nonPoison
    retVal := normSymExpr retExpr
    memWrites := finalSt.memWrites
    liveRc := canonLiveRc }

/-! ## Multi-Point Concrete Refinement Evaluator (64 Boundary + SplitMix64 Samples) -/

/-- Deterministic SplitMix64 step for reproducible test input generation. -/
def splitMix64Next (state : UInt64) : UInt64 × UInt64 :=
  let s' := state + 0x9e3779b97f4a7c15
  let z1 := (s' ^^^ (s' >>> 30)) * 0xbf58476d1ce4e5b9
  let z2 := (z1 ^^^ (z1 >>> 27)) * 0x94d049bb133111eb
  let out := z2 ^^^ (z2 >>> 31)
  (out, s')

def mkSampleObjPayload (base : UInt64) : List Val :=
  (List.range 8).map fun i =>
    if i == 0 then .u64 (((splitMix64Next (base + 7)).1 % 8) + 1)
    else .u64 (((splitMix64Next (base + (i * 19 + 11).toUInt64)).1 % 16) + 1)

def mkSampleObjTree : Nat → UInt64 → HeapState → Val × HeapState
  | 0, base, curSt => curSt.allocCtor 0 [] (mkSampleObjPayload base)
  | d + 1, base, curSt =>
    let (c0, stA) := mkSampleObjTree d (base + 97) curSt
    let useObjSlot1 := (splitMix64Next (base + 53)).1 % 2 == 0
    let (s1, stB) :=
      if useObjSlot1 then mkSampleObjTree d (base + 193) stA
      else (.u64 (((splitMix64Next (base + 42)).1 % 16) + 1), stA)
    let childSlots : List Val :=
      (List.range 8).map fun j =>
        if j == 0 then c0
        else if j == 1 then s1
        else .u64 (((splitMix64Next (base + (j * 29 + 13).toUInt64)).1 % 16) + 1)
    let tag := ((splitMix64Next (base + 71)).1 % 2).toNat
    stB.allocCtor tag childSlots (mkSampleObjPayload (base + 211))

/-- Construct a concrete `Val` and update `HeapState` for a parameter of type `LNIRType`.
    Scalar inputs are drawn from `{1, ..., 8}` so loop bounds and array indices stay within
    the 16-element test buffers while exercising multi-iteration loops and arithmetic paths. -/
def mkSampleParamValAux : Nat → UInt64 → Nat → LNIRType → HeapState → Val × HeapState
  | 0, _, _, _, st => (.u64 1, st)
  | depth + 1, seed, paramIdx, ty, st =>
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
      let (vals, st') := fs.foldl (fun (acc, curSt) fty =>
        let (fv, nextSt) := mkSampleParamValAux depth (seed + acc.length.toUInt64 * 97) (paramIdx + acc.length + 1) fty curSt
        (acc ++ [fv], nextSt)) ([], st)
      (.tuple vals, st')
    | .objPtr | .taggedPtr =>
      let (rootVal, st3) := mkSampleObjTree (Nat.min depth 2) (r + 101) st
      let rootId := st3.nextId
      let st4 :=
        if r % 3 == 0 then
          match st3.incRefObj rootId 1 with
          | .ok s' => s'
          | .error _ => st3
        else st3
      (rootVal, st4)
    | .unit => (.unit, st)
    | _ => (.u64 smallU64, st)

def mkSampleParamVal (seed : UInt64) (paramIdx : Nat) (ty : LNIRType) (st : HeapState) :
    Val × HeapState :=
  mkSampleParamValAux 8 seed paramIdx ty st

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
def checkDeclConcreteRefinement (src tgt : LNIRDecl) (numSamples : Nat := 64) (fuel : Nat := 1024) :
    Bool × Nat :=
  let samples := (List.range numSamples).map (buildDeclSample src)
  let (passedCount, nonVacuousCount) := samples.foldl (fun (acc, okSrc) (env, st) =>
    let srcOk := match evalCode fuel env st src.body with | .ok _ => true | .error _ => false
    let stepOk := checkSingleSample fuel env st src.body tgt.body
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
  let (concreteOk, passedSamples) := checkDeclConcreteRefinement src tgt numSamples 1024
  let memWritesEquiv := sSrc.memWrites == sTgt.memWrites && sSrc.liveRc == sTgt.liveRc
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

#guard (symEvalExpr {} 9 (.call "lean_native_box_u64" [1] .objPtr)).noUB
#guard !(symEvalExpr {} 9 (.call "lean_native_box_u64" [1] .i64)).noUB
#guard !(symEvalExpr {} 9 (.call "lean_native_box_u64" [1, 2] .objPtr)).noUB
#guard !(symEvalExpr {} 9 (.call "lean_native_unbox_u64" [] .i64)).noUB
#guard !(symEvalExpr {} 9 (.call "lean_native_unbox_u64" [1] .u256)).noUB
#guard !(symEvalExpr {} 9 (.call "lean_native_ensure_exclusive" [1] .i64)).noUB
#guard !(symEvalExpr {} 9 (.call "lean_native_sarray_len" [1] .objPtr)).noUB
#guard !(symEvalExpr {} 9 (.call "lean_native_sarray_len" [1] .i64 true)).noUB
#guard !(symEvalExpr {} 9 (.call "lean_native_unknown" [1] .i64)).noUB
#guard (symEvalExpr {} 9 (.call "lean_native_unbox_u64" [1] .i64)).lookupVar 9 == (({} : SymExecState).lookupVar 1)
#guard ((symEvalExpr {} 9 (.call "lean_native_ensure_exclusive" [1] (.sarray .i64))).isBufExclusive 9)
#guard (symEvalExpr {} 9 (.call "lean_native_sarray_len" [1] .i64)).lookupVar 9 ==
  (symEvalExpr {} 9 (.sarrayLen 1)).lookupVar 9

private def mkExclTestDecl (name : String) (body : LNIRCode) : LNIRDecl :=
  { name := name
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body := body }

private def exclDirectSrc : LNIRDecl :=
  mkExclTestDecl "excl_direct" <|
    .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
    .incRef 1 1 <|
    .letBind 2 .i1 (.isExclusive 1) <|
    .decRef 1 2 (.ret 2)

private def exclConstTrueTgt : LNIRDecl :=
  mkExclTestDecl "excl_direct" <|
    .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
    .incRef 1 1 <|
    .letBind 2 .i1 (.scalar (.constBool true)) <|
    .decRef 1 2 (.ret 2)

private def exclAliasSrc : LNIRDecl :=
  mkExclTestDecl "excl_alias" <|
    .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
    .letBind 2 .objPtr (.scalar (.var 1)) <|
    .letBind 3 (.tuple [.objPtr, .i64]) (.mkTuple [2, 0]) <|
    .letBind 4 .objPtr (.projTuple 3 0) <|
    .incRef 4 1 <|
    .letBind 5 .i1 (.isExclusive 1) <|
    .decRef 4 2 (.ret 5)

private def exclAliasTgt : LNIRDecl :=
  mkExclTestDecl "excl_alias" <|
    .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
    .letBind 2 .objPtr (.scalar (.var 1)) <|
    .letBind 3 (.tuple [.objPtr, .i64]) (.mkTuple [2, 0]) <|
    .letBind 4 .objPtr (.projTuple 3 0) <|
    .incRef 4 1 <|
    .letBind 5 .i1 (.scalar (.constBool true)) <|
    .decRef 4 2 (.ret 5)

private def exclBranchSrc : LNIRDecl :=
  mkExclTestDecl "excl_branch" <|
    .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
    .letBind 2 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
    .ite 2
      (.incRef 1 1 (.letBind 3 .i1 (.isExclusive 1) (.decRef 1 2 (.ret 3))))
      (.letBind 3 .i1 (.isExclusive 1) (.decRef 1 1 (.ret 3)))

private def exclBranchTgt : LNIRDecl :=
  mkExclTestDecl "excl_branch" <|
    .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
    .letBind 2 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
    .ite 2
      (.incRef 1 1 (.letBind 3 .i1 (.scalar (.constBool true)) (.decRef 1 2 (.ret 3))))
      (.letBind 3 .i1 (.scalar (.constBool true)) (.decRef 1 1 (.ret 3)))

private def exclPostMergeSrc : LNIRDecl :=
  mkExclTestDecl "excl_post_merge" <|
    .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
    .letBind 2 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
    .ite 2
      (.incRef 1 1 (.letBind 4 .i1 (.isExclusive 1) (.decRef 1 2 (.ret 4))))
      (.letBind 4 .i1 (.isExclusive 1) (.decRef 1 1 (.ret 4)))

private def exclLoopUnknownSrc : LNIRDecl :=
  mkExclTestDecl "excl_loop_unknown" <|
    .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
    .letBind 2 .i64 (.scalar (.constU64 0)) <|
    .letBind 3 .i64 (.scalar (.constU64 1)) <|
    .seqFor 4 2 3 5 2 .i64
      (.letBind 6 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100)))
        (.ite 6 (.incRef 1 1 (.ret 5)) (.ret 5)))
      (.letBind 7 .i1 (.isExclusive 1) (.ret 7))

private def exclLoopConstTrueTgt : LNIRDecl :=
  mkExclTestDecl "excl_loop_unknown" <|
    .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
    .letBind 2 .i64 (.scalar (.constU64 0)) <|
    .letBind 3 .i64 (.scalar (.constU64 1)) <|
    .seqFor 4 2 3 5 2 .i64
      (.letBind 6 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100)))
        (.ite 6 (.incRef 1 1 (.ret 5)) (.ret 5)))
      (.letBind 7 .i1 (.scalar (.constBool true)) (.ret 7))

private def childDecRefSrc : LNIRDecl :=
  mkExclTestDecl "child_decref_uaf" <|
    .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
    .letBind 2 .objPtr (.allocCtor 1 [1] [0]) <|
    .decRef 2 1 <|
    .letBind 3 .i1 (.scalar (.constBool true)) (.ret 3)

private def childDecRefUafTgt : LNIRDecl :=
  mkExclTestDecl "child_decref_uaf" <|
    .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
    .letBind 2 .objPtr (.allocCtor 1 [1] [0]) <|
    .decRef 2 1 <|
    .letBind 3 .i64 (.ctorGetScalar 1 0 .i64) <|
    .letBind 4 .i1 (.scalar (.constBool true)) (.ret 4)

private def delShellPreservesChildDecl : LNIRDecl :=
  mkExclTestDecl "del_shell_preserves_child" <|
    .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
    .letBind 2 .objPtr (.allocCtor 1 [1] [0]) <|
    .letBind 3 .objPtr (.ctorGetObj 2 0) <|
    .letBind 4 .unit (.call "lean_native_del_obj" [2] .unit false) <|
    .letBind 5 .i1 (.isExclusive 3) <|
    .decRef 3 1 (.ret 5)

private def delShellLeakTgt : LNIRDecl :=
  mkExclTestDecl "del_shell_preserves_child" <|
    .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
    .letBind 2 .objPtr (.allocCtor 1 [1] [0]) <|
    .letBind 3 .objPtr (.ctorGetObj 2 0) <|
    .letBind 4 .unit (.call "lean_native_del_obj" [2] .unit false) <|
    .letBind 5 .i1 (.isExclusive 3) (.ret 5)

private def childReleaseExclBranchSrc : LNIRDecl :=
  mkExclTestDecl "child_release_excl_branch" <|
    .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
    .incRef 1 1 <|
    .letBind 2 .objPtr (.allocCtor 1 [1] [0]) <|
    .letBind 3 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
    .ite 3
      (.decRef 2 1 (.letBind 4 .i1 (.isExclusive 1) (.decRef 1 1 (.ret 4))))
      (.decRef 2 1 (.decRef 1 1 (.letBind 4 .i1 (.scalar (.constBool false)) (.ret 4))))

private def childReleaseExclBranchFalseTgt : LNIRDecl :=
  mkExclTestDecl "child_release_excl_branch" <|
    .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
    .incRef 1 1 <|
    .letBind 2 .objPtr (.allocCtor 1 [1] [0]) <|
    .letBind 3 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
    .ite 3
      (.decRef 2 1 (.letBind 4 .i1 (.scalar (.constBool false)) (.decRef 1 1 (.ret 4))))
      (.decRef 2 1 (.decRef 1 1 (.letBind 4 .i1 (.scalar (.constBool false)) (.ret 4))))

private def tupleDecRefNoOpSrc : LNIRDecl :=
  mkExclTestDecl "tuple_decref_noop" <|
    .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
    .incRef 1 1 <|
    .letBind 2 (.tuple [.objPtr]) (.mkTuple [1]) <|
    .letBind 3 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
    .ite 3
      (.decRef 2 1 (.letBind 4 .i1 (.isExclusive 1) (.decRef 1 2 (.ret 4))))
      (.decRef 1 2 (.letBind 4 .i1 (.scalar (.constBool false)) (.ret 4)))

private def tupleDecRefTrueTgt : LNIRDecl :=
  mkExclTestDecl "tuple_decref_noop" <|
    .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
    .incRef 1 1 <|
    .letBind 2 (.tuple [.objPtr]) (.mkTuple [1]) <|
    .letBind 3 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
    .ite 3
      (.decRef 2 1 (.letBind 4 .i1 (.scalar (.constBool true)) (.decRef 1 2 (.ret 4))))
      (.decRef 1 2 (.letBind 4 .i1 (.scalar (.constBool false)) (.ret 4)))

private def paramProjCopySrc : LNIRDecl :=
  { name := "param_proj_copy"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false },
               { id := 1, name := "p", ty := .objPtr, borrow := false }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 2 .objPtr (.ctorGetObj 1 0) <|
      .letBind 3 .objPtr (.scalar (.var 2)) <|
      .letBind 4 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 4
        (.incRef 3 1 (.letBind 5 .i1 (.isExclusive 2) (.decRef 3 1 (.ret 5))))
        (.letBind 5 .i1 (.scalar (.constBool false)) (.ret 5)) }

private def paramProjCopyReorderedTgt : LNIRDecl :=
  { paramProjCopySrc with
    body :=
      .letBind 2 .objPtr (.ctorGetObj 1 0) <|
      .letBind 3 .objPtr (.scalar (.var 2)) <|
      .letBind 4 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 4
        (.letBind 5 .i1 (.isExclusive 2) (.incRef 3 1 (.decRef 3 1 (.ret 5))))
        (.letBind 5 .i1 (.scalar (.constBool false)) (.ret 5)) }

private def nestedTupleReleaseSrc : LNIRDecl :=
  mkExclTestDecl "nested_tuple_release" <|
    .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
    .incRef 1 1 <|
    .letBind 2 (.tuple [.objPtr]) (.mkTuple [1]) <|
    .letBind 3 (.tuple [.tuple [.objPtr]]) (.mkTuple [2]) <|
    .letBind 4 .objPtr (.allocCtor 1 [3] []) <|
    .letBind 5 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
    .ite 5
      (.decRef 4 1 (.letBind 6 .i1 (.isExclusive 1) (.decRef 1 1 (.ret 6))))
      (.decRef 4 1 (.decRef 1 1 (.letBind 6 .i1 (.scalar (.constBool false)) (.ret 6))))

private def nestedTupleReleaseFalseTgt : LNIRDecl :=
  mkExclTestDecl "nested_tuple_release" <|
    .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
    .incRef 1 1 <|
    .letBind 2 (.tuple [.objPtr]) (.mkTuple [1]) <|
    .letBind 3 (.tuple [.tuple [.objPtr]]) (.mkTuple [2]) <|
    .letBind 4 .objPtr (.allocCtor 1 [3] []) <|
    .letBind 5 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
    .ite 5
      (.decRef 4 1 (.letBind 6 .i1 (.scalar (.constBool false)) (.decRef 1 1 (.ret 6))))
      (.decRef 4 1 (.decRef 1 1 (.letBind 6 .i1 (.scalar (.constBool false)) (.ret 6))))

private def tupleParamProjCopySrc : LNIRDecl :=
  { name := "tuple_param_proj_copy"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false },
               { id := 1, name := "tp", ty := .tuple [.objPtr], borrow := false }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 2 .objPtr (.projTuple 1 0) <|
      .letBind 3 .objPtr (.scalar (.var 2)) <|
      .letBind 4 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 4
        (.incRef 3 1 (.letBind 5 .i1 (.isExclusive 2) (.decRef 3 1 (.ret 5))))
        (.letBind 5 .i1 (.scalar (.constBool false)) (.ret 5)) }

private def tupleParamProjCopyReorderedTgt : LNIRDecl :=
  { tupleParamProjCopySrc with
    body :=
      .letBind 2 .objPtr (.projTuple 1 0) <|
      .letBind 3 .objPtr (.scalar (.var 2)) <|
      .letBind 4 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 4
        (.letBind 5 .i1 (.isExclusive 2) (.incRef 3 1 (.decRef 3 1 (.ret 5))))
        (.letBind 5 .i1 (.scalar (.constBool false)) (.ret 5)) }

private def selfRebindCtorSrc : LNIRDecl :=
  mkExclTestDecl "self_rebind_ctor" <|
    .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
    .incRef 1 1 <|
    .letBind 1 .objPtr (.allocCtor 1 [1] []) <|
    .decRef 1 1 <|
    .letBind 2 .i1 (.scalar (.constBool true)) (.ret 2)

private def selfRebindCtorDropIncTgt : LNIRDecl :=
  mkExclTestDecl "self_rebind_ctor" <|
    .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
    .letBind 1 .objPtr (.allocCtor 1 [1] []) <|
    .decRef 1 1 <|
    .letBind 2 .i1 (.scalar (.constBool true)) (.ret 2)

private def selfRebindTupleSrc : LNIRDecl :=
  mkExclTestDecl "self_rebind_tuple" <|
    .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
    .incRef 1 1 <|
    .letBind 2 (.tuple [.objPtr]) (.mkTuple [1]) <|
    .letBind 2 (.tuple [.tuple [.objPtr]]) (.mkTuple [2]) <|
    .letBind 3 .objPtr (.allocCtor 1 [2] []) <|
    .letBind 4 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
    .ite 4
      (.decRef 3 1 (.letBind 5 .i1 (.isExclusive 1) (.decRef 1 1 (.ret 5))))
      (.decRef 3 1 (.decRef 1 1 (.letBind 5 .i1 (.scalar (.constBool false)) (.ret 5))))

private def selfRebindTupleFalseTgt : LNIRDecl :=
  mkExclTestDecl "self_rebind_tuple" <|
    .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
    .incRef 1 1 <|
    .letBind 2 (.tuple [.objPtr]) (.mkTuple [1]) <|
    .letBind 2 (.tuple [.tuple [.objPtr]]) (.mkTuple [2]) <|
    .letBind 3 .objPtr (.allocCtor 1 [2] []) <|
    .letBind 4 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
    .ite 4
      (.decRef 3 1 (.letBind 5 .i1 (.scalar (.constBool false)) (.decRef 1 1 (.ret 5))))
      (.decRef 3 1 (.decRef 1 1 (.letBind 5 .i1 (.scalar (.constBool false)) (.ret 5))))

private def tupleScalarNestedSrc : LNIRDecl :=
  { name := "tuple_scalar_nested"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false },
               { id := 1, name := "tp", ty := .tuple [.i64, .tuple [.objPtr]], borrow := false }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 2 (.tuple [.objPtr]) (.projTuple 1 1) <|
      .letBind 3 .objPtr (.allocCtor 0 [2] []) <|
      .letBind 4 .objPtr (.projTuple 2 0) <|
      .letBind 5 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 5
        (.incRef 4 1 (.decRef 3 1 (.letBind 6 .i1 (.isExclusive 4) (.ret 6))))
        (.letBind 6 .i1 (.scalar (.constBool false)) (.ret 6)) }

private def tupleScalarNestedFalseTgt : LNIRDecl :=
  { tupleScalarNestedSrc with
    body :=
      .letBind 2 (.tuple [.objPtr]) (.projTuple 1 1) <|
      .letBind 3 .objPtr (.allocCtor 0 [2] []) <|
      .letBind 4 .objPtr (.projTuple 2 0) <|
      .letBind 5 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 5
        (.incRef 4 1 (.decRef 3 1 (.letBind 6 .i1 (.scalar (.constBool false)) (.ret 6))))
        (.letBind 6 .i1 (.scalar (.constBool false)) (.ret 6)) }

#guard !(validateTranslationDecl exclDirectSrc exclConstTrueTgt).passed
#guard !(validateTranslationDecl exclAliasSrc exclAliasTgt).passed
#guard !(validateTranslationDecl exclBranchSrc exclBranchTgt).passed
#guard !(validateTranslationDecl exclBranchSrc exclBranchTgt).symRetEquiv
#guard !(validateTranslationDecl exclLoopUnknownSrc exclLoopConstTrueTgt).symRetEquiv
#guard !(validateTranslationDecl exclLoopUnknownSrc exclLoopConstTrueTgt).passed
#guard (validateTranslationDecl exclPostMergeSrc exclPostMergeSrc).passed
#guard (symExecDecl 4 childDecRefSrc).noUB
#guard !(symExecDecl 4 childDecRefUafTgt).noUB
#guard !(validateTranslationDecl childDecRefSrc childDecRefUafTgt).ubRefines
#guard !(validateTranslationDecl childDecRefSrc childDecRefUafTgt).passed
#guard (symExecDecl 4 delShellPreservesChildDecl).noUB
#guard (symExecDecl 4 delShellPreservesChildDecl).retVal == .constBool true
#guard !(validateTranslationDecl delShellPreservesChildDecl delShellLeakTgt).memWritesEquiv
#guard !(validateTranslationDecl delShellPreservesChildDecl delShellLeakTgt).passed
#guard !(validateTranslationDecl childReleaseExclBranchSrc childReleaseExclBranchFalseTgt).symRetEquiv
#guard !(validateTranslationDecl childReleaseExclBranchSrc childReleaseExclBranchFalseTgt).passed
#guard (let s0 := (symEvalExpr {} 1 (.allocCtor 0 [] [])).incRootRc 1 1;
  let s1 := symEvalExpr s0 2 (.allocCtor 1 [1] []);
  let (s2, _) := symExecCode 16 4 s1 (.ite 0 (.incRef 2 1 (.ret 2)) (.ret 2));
  let s3 := s2.decRootRc 2 1;
  let s4 := symEvalExpr s3 4 (.isExclusive 1);
  s4.lookupVar 4 |>.expr) == .symVar (400000 + (symEvalExpr {} 1 (.allocCtor 0 [] [])).resolveBuf 1)
#guard !(let s0 := symEvalExpr {} 1 (.allocCtor 0 [] []);
  let (s1, _) := symExecCode 16 4 s0 (.ite 0 (.incRef 1 1 (.ret 1)) (.ret 1));
  let s2 := s1.decRootRc 1 1;
  let s3 := symEvalExpr s2 4 (.isExclusive 1);
  s3.noUB)
#guard (let s0 := symEvalExpr {} 1 (.allocCtor 0 [] []);
  let (s1, _) := symExecCode 16 4 s0 (.ite 0 (.incRef 1 1 (.ret 1)) (.ret 1));
  let s2 := symEvalExpr s1 2 (.isExclusive 1);
  (s2.lookupVar 2 |>.expr) == .symVar (400000 + s0.resolveBuf 1))
#guard !(let s0 := symEvalExpr {} 1 (.allocCtor 0 [] []);
  s0.decRootRcFuel 0 false 1 1).noUB
#guard !(validateTranslationDecl tupleDecRefNoOpSrc tupleDecRefTrueTgt).symRetEquiv
#guard !(validateTranslationDecl tupleDecRefNoOpSrc tupleDecRefTrueTgt).passed
#guard !(validateTranslationDecl paramProjCopySrc paramProjCopyReorderedTgt).symRetEquiv
#guard !(validateTranslationDecl paramProjCopySrc paramProjCopyReorderedTgt).passed
#guard !(validateTranslationDecl nestedTupleReleaseSrc nestedTupleReleaseFalseTgt).symRetEquiv
#guard !(validateTranslationDecl nestedTupleReleaseSrc nestedTupleReleaseFalseTgt).passed
#guard !(validateTranslationDecl tupleParamProjCopySrc tupleParamProjCopyReorderedTgt).symRetEquiv
#guard !(validateTranslationDecl tupleParamProjCopySrc tupleParamProjCopyReorderedTgt).passed
#guard !(validateTranslationDecl selfRebindCtorSrc selfRebindCtorDropIncTgt).memWritesEquiv
#guard !(validateTranslationDecl selfRebindCtorSrc selfRebindCtorDropIncTgt).passed
#guard !(validateTranslationDecl selfRebindTupleSrc selfRebindTupleFalseTgt).symRetEquiv
#guard !(validateTranslationDecl selfRebindTupleSrc selfRebindTupleFalseTgt).passed
#guard !(validateTranslationDecl tupleScalarNestedSrc tupleScalarNestedFalseTgt).symRetEquiv
#guard !(validateTranslationDecl tupleScalarNestedSrc tupleScalarNestedFalseTgt).passed
private def sparseFieldProjSrc : LNIRDecl :=
  { name := "sparse_field_proj"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false },
               { id := 1, name := "p", ty := .objPtr, borrow := false }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 2 .objPtr (.ctorGetObj 1 1) <|
      .letBind 3 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 3
        (.incRef 2 1 (.decRef 1 1 (.letBind 4 .i1 (.isExclusive 2) (.ret 4))))
        (.letBind 4 .i1 (.scalar (.constBool false)) (.ret 4)) }

private def sparseFieldProjFalseTgt : LNIRDecl :=
  { sparseFieldProjSrc with
    body :=
      .letBind 2 .objPtr (.ctorGetObj 1 1) <|
      .letBind 3 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 3
        (.incRef 2 1 (.decRef 1 1 (.letBind 4 .i1 (.scalar (.constBool false)) (.ret 4))))
        (.letBind 4 .i1 (.scalar (.constBool false)) (.ret 4)) }

private def aliasParamSrc : LNIRDecl :=
  { name := "alias_heap_params"
    params := [{ id := 0, name := "p", ty := .objPtr, borrow := true },
               { id := 1, name := "q", ty := .objPtr, borrow := true }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body := .incRef 0 1 (.letBind 2 .i1 (.isExclusive 1) (.decRef 0 1 (.ret 2))) }

private def aliasParamReorderedTgt : LNIRDecl :=
  { aliasParamSrc with
    body := .letBind 2 .i1 (.isExclusive 1) (.incRef 0 1 (.decRef 0 1 (.ret 2))) }

#guard !(validateTranslationDecl sparseFieldProjSrc sparseFieldProjFalseTgt).symRetEquiv
#guard !(validateTranslationDecl sparseFieldProjSrc sparseFieldProjFalseTgt).passed
#guard (validateTranslationDecl aliasParamSrc aliasParamSrc).passed
#guard !(validateTranslationDecl aliasParamSrc aliasParamReorderedTgt).symRetEquiv
#guard !(validateTranslationDecl aliasParamSrc aliasParamReorderedTgt).passed
#guard (let s0 := symEvalExpr {} 1 (.allocCtor 0 [] []);
  let s1 := s0.incRootRc 1 34;
  let s2 := symEvalExpr s1 2 (.allocCtor 0 (List.replicate 34 1) []);
  let s3 := s2.decRootRc 2 1;
  s3.noUB && s3.getRootRc 1 == (1, some 1) && s3.isBufExclusive 1)

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
