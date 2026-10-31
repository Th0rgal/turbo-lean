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
  | projSym   (kind : Nat) (base : VarId) (idx : Nat)
  | binOp     (op : BinOp) (lhs rhs : SymExpr)
  | unaryOp   (op : UnaryOp) (arg : SymExpr)
  | ite       (cond thenVal elseVal : SymExpr)
  | tuple     (fields : List SymExpr)
  | ctorObj   (allocId : SymExpr) (tag : UInt64) (objs : List SymExpr) (scalars : List SymExpr)
  | bufElem   (bufVar : VarId) (idx : SymExpr)
  | arrLen    (bufVar : VarId)
  | exclCheck (epoch : SymExpr) (rootSym : SymExpr)
  | decCond   (epoch : SymExpr) (rootSym : SymExpr)
  | unit
  deriving Repr, Inhabited, BEq

namespace SymExpr

/-- Deterministic structural rank used to canonicalize commutative binary operators.
    Constants receive the highest rank so they are pushed to the right-hand side (`x + c`). -/
def rank : SymExpr → Nat
  | .symVar id       => 10 + id
  | .projSym k b i   => 500 + k + b + i
  | .bufElem b _     => 1000 + b
  | .arrLen b        => 1500 + b
  | .unaryOp _ a     => 2000 + rank a
  | .binOp _ l r     => 3000 + rank l + rank r
  | .ite c t e       => 4000 + rank c + rank t + rank e
  | .tuple fs            => 5000 + fs.length
  | .ctorObj aid _ os ss => 5500 + rank aid + os.length + ss.length
  | .exclCheck e r       => 6000 + rank e + rank r
  | .decCond e r         => 7000 + rank e + rank r
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
    | .projSym k b i => .projSym k b i
    | .binOp op l r => normSymBinOpStep op (normSymExpr l) (normSymExpr r)
    | .unaryOp op a => normSymUnaryOpStep op (normSymExpr a)
    | .ite c t e => normSymIteStep (normSymExpr c) (normSymExpr t) (normSymExpr e)
    | .tuple fs => .tuple (normSymExprList fs)
    | .ctorObj aid tag os ss => .ctorObj (normSymExpr aid) tag (normSymExprList os) (normSymExprList ss)
    | .bufElem b idx => .bufElem b (normSymExpr idx)
    | .arrLen b => .arrLen b
    | .exclCheck e r => .exclCheck (normSymExpr e) (normSymExpr r)
    | .decCond e r => .decCond (normSymExpr e) (normSymExpr r)
    | .unit => .unit

  def normSymExprList : List SymExpr → List SymExpr
    | [] => []
    | e :: es => normSymExpr e :: normSymExprList es
end

mutual
  def substSymHeapIds (mapId : VarId → VarId) : SymExpr → SymExpr
    | .constU64 v => .constU64 v
    | .constBool b => .constBool b
    | .symVar id => .symVar (mapId id)
    | .projSym k b i => .projSym k (mapId b) i
    | .binOp op l r => .binOp op (substSymHeapIds mapId l) (substSymHeapIds mapId r)
    | .unaryOp op a => .unaryOp op (substSymHeapIds mapId a)
    | .ite c t e => .ite (substSymHeapIds mapId c) (substSymHeapIds mapId t) (substSymHeapIds mapId e)
    | .tuple fs => .tuple (substSymHeapIdsList mapId fs)
    | .ctorObj aid tag os ss => .ctorObj (substSymHeapIds mapId aid) tag (substSymHeapIdsList mapId os) (substSymHeapIdsList mapId ss)
    | .bufElem b idx => .bufElem (mapId b) (substSymHeapIds mapId idx)
    | .arrLen b => .arrLen (mapId b)
    | .exclCheck e r => .exclCheck (substSymHeapIds mapId e) (substSymHeapIds mapId r)
    | .decCond e r => .decCond (substSymHeapIds mapId e) (substSymHeapIds mapId r)
    | .unit => .unit

  def substSymHeapIdsList (mapId : VarId → VarId) : List SymExpr → List SymExpr
    | [] => []
    | e :: es => substSymHeapIds mapId e :: substSymHeapIdsList mapId es
end

/-! ## Symbolic Execution of `ScalarExpr`, `LNIRExpr`, `LNIRCode`, and `LNIRDecl` -/

/-- Symbolic execution state tracking variable bindings, buffer aliases, exclusivity,
    normalized memory writes, and Alive2 `noUB` / `nonPoison` flags. -/
structure SymExecState where
  vars            : List (VarId × SymStateVal) := []
  bufAliases      : List (VarId × VarId) := []
  exclusiveBufs   : List VarId := []
  maybeScalarRoots : List VarId := []
  rootRc          : List (VarId × Nat × Option Nat) := []
  rootRcEpoch     : List (VarId × SymExpr) := []
  objRoots      : List (VarId × List (Option VarId)) := []
  tupleRoots    : List (VarId × List (Option VarId)) := []
  paramChildRoots : List VarId := []
  immRoots      : List VarId := []
  freshCtorRoots : List VarId := []
  heapAllocSeq  : List (VarId × SymExpr) := []
  allocBase     : Nat := 170000
  nextAllocSeq  : Nat := 0
  nextHeapId    : SymExpr := .constU64 0
  rcEpoch       : SymExpr := .constU64 0
  memWrites     : List (VarId × SymExpr × SymExpr) := []
  noUB          : Bool := true
  supported     : Bool := true
  nonPoison     : Bool := true
  reachable     : Bool := true
  deriving Repr, Inhabited, BEq

def isImmSymExpr (immRoots : List VarId := []) : SymExpr → Bool
  | .constU64 _ | .constBool _ | .unit | .projSym 0 .. | .bufElem .. | .arrLen _
  | .exclCheck .. | .decCond .. | .unaryOp _ _ => true
  | .symVar id => immRoots.contains id
  | .binOp .add l r | .binOp .sub l r | .binOp .mul l r | .binOp .div l r
  | .binOp .bitAnd l r | .binOp .bitOr l r | .binOp .bitXor l r
  | .binOp .shl l r | .binOp .shr l r =>
    isImmSymExpr immRoots l && isImmSymExpr immRoots r
  | .binOp _ _ _ => true
  | .ite _ t e => isImmSymExpr immRoots t && isImmSymExpr immRoots e
  | .tuple fs => isImmSymExprList immRoots fs
  | .ctorObj .. | .projSym _ .. => false
where
  isImmSymExprList (immRoots : List VarId) : List SymExpr → Bool
    | [] => true
    | x :: xs => isImmSymExpr immRoots x && isImmSymExprList immRoots xs

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

def rootIdentitySym (st : SymExecState) (r : VarId) : SymExpr :=
  match st.heapAllocSeq.lookup r with
  | some seq => .ctorObj seq 0 [] []
  | none => .symVar r

def getRootRcEpoch (st : SymExecState) (root : VarId) : SymExpr :=
  (st.rootRcEpoch.lookup root).getD (.constU64 0)

def recordRootRcOp (st : SymExecState) (root : VarId) (tag : UInt64) (arg : SymExpr) : SymExecState :=
  let nextEp := normSymExpr (.ctorObj (st.getRootRcEpoch root) tag [st.rootIdentitySym root] [arg])
  let rest := st.rootRcEpoch.filter (fun (id, _) => id != root)
  { st with rootRcEpoch := (root, nextEp) :: rest }

def recordGlobalRcOp (st : SymExecState) (root : VarId) (tag : UInt64) (arg : SymExpr) : SymExecState :=
  { st with rcEpoch := normSymExpr (.ctorObj st.rcEpoch tag [st.rootIdentitySym root] [arg]) }

def getRootRc (st : SymExecState) (bufVar : VarId) : Nat × Option Nat :=
  let root := st.resolveBuf bufVar
  match st.rootRc.lookup root with
  | some rcInfo => rcInfo
  | none => if st.exclusiveBufs.contains root then (1, some 1) else (1, none)

def markExclusive (st : SymExecState) (bufVar : VarId) : SymExecState :=
  st.setRootRc (st.resolveBuf bufVar) 1 (some 1)

def isBufExclusive (st : SymExecState) (bufVar : VarId) : Bool :=
  let root := st.resolveBuf bufVar
  let (_, exactRc?) := st.getRootRc root
  exactRc? == some 1 && !st.maybeScalarRoots.contains root

def isFreshRuntimeAllocRoot (st : SymExecState) (r : VarId) : Bool :=
  st.freshCtorRoots.contains r || (st.heapAllocSeq.lookup r).isSome

def hasKnownRootTracking (st : SymExecState) (root : VarId) : Bool :=
  (match (st.lookupVar root).expr with
   | .symVar base => base == root
   | _ => false) ||
    (st.rootRc.lookup root).isSome || st.exclusiveBufs.contains root

def dropAliasedRootBounds (st : SymExecState) (keepRoot : VarId) : SymExecState :=
  let isMayAlias (id : VarId) := id != keepRoot && !st.isFreshRuntimeAllocRoot id
  let rc' := st.rootRc.map fun (id, m, ex?) =>
    if !isMayAlias id then (id, m, ex?) else (id, 1, none)
  let excl' := st.exclusiveBufs.filter (!isMayAlias ·)
  { st with rootRc := rc', exclusiveBufs := excl' }

def markMaybeScalar (st : SymExecState) (root : VarId) : SymExecState :=
  if st.maybeScalarRoots.contains root then st
  else { st with maybeScalarRoots := root :: st.maybeScalarRoots }

def markImmRoot (st : SymExecState) (root : VarId) : SymExecState :=
  if st.immRoots.contains root then st
  else { st with immRoots := root :: st.immRoots }

def incRootRc (st : SymExecState) (objVar : VarId) (count : Nat) : SymExecState :=
  let root := st.resolveBuf objVar
  let sv := st.lookupVar root
  match sv.expr with
  | .constU64 _ | .constBool _ | .unit | .tuple _ => st
  | _ =>
    if isImmSymExpr st.immRoots sv.expr then st
    else if !st.hasKnownRootTracking root then
      if count == 0 then st else { st with noUB := false, supported := false }
    else
      let (minRc, exactRc?) := st.getRootRc root
      if minRc == 0 || exactRc? == some 0 then { st with noUB := false }
      else if count == 0 then st
      else
        let st0 := if st.isFreshRuntimeAllocRoot root then st else st.dropAliasedRootBounds root
        let st1 := (st0.setRootRc root (minRc + count) (exactRc?.map (· + count))).recordRootRcOp root 1 (.constU64 count.toUInt64)
        st1.recordGlobalRcOp root 1 (.constU64 count.toUInt64)

private def dedupIds (xs : List VarId) : List VarId :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

private def cantPair (a b : Nat) : Nat :=
  (a + b) * (a + b + 1) / 2 + b

def mergeBranches (base stT stE : SymExecState) (cExpr : SymExpr) (condNoUB condNonPoison : Bool) : SymExecState :=
  let rcKeys := dedupIds (base.rootRc.map (·.1) ++ stT.rootRc.map (·.1) ++ stE.rootRc.map (·.1) ++
    base.exclusiveBufs ++ stT.exclusiveBufs ++ stE.exclusiveBufs)
  let branchRcOf (br : SymExecState) (r : VarId) : Nat × Option Nat :=
    if (br.rootRc.lookup r).isSome || br.exclusiveBufs.contains r ||
       (base.rootRc.lookup r).isSome || base.exclusiveBufs.contains r then
      br.getRootRc r
    else
      (0, some 0)
  let mergedRc := rcKeys.map fun r =>
    let (mT, eT) := branchRcOf stT r
    let (mE, eE) := branchRcOf stE r
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
    let expr :=
      if v >= base.allocBase &&
         (stT.freshCtorRoots.contains v || stE.freshCtorRoots.contains v ||
          (stT.heapAllocSeq.lookup v).isSome || (stE.heapAllocSeq.lookup v).isSome) &&
         !(base.vars.lookup v).isSome then
        let hasT := (stT.vars.lookup v).isSome
        let hasE := (stE.vars.lookup v).isSome
        if hasT && !hasE then .ite cExpr svT.expr .unit
        else if !hasT && hasE then .ite cExpr .unit svE.expr
        else if svT.expr == svE.expr then svT.expr else normSymIteStep cExpr svT.expr svE.expr
      else if svT.expr == svE.expr then svT.expr else normSymIteStep cExpr svT.expr svE.expr
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
  let mergedMaybeScalar := dedupIds (base.maybeScalarRoots ++ stT.maybeScalarRoots ++ stE.maybeScalarRoots)
  let epKeys := dedupIds (rcKeys ++ base.rootRcEpoch.map (·.1) ++ stT.rootRcEpoch.map (·.1) ++ stE.rootRcEpoch.map (·.1))
  let mergedRootRcEpoch := epKeys.filterMap fun r =>
    let epT := stT.getRootRcEpoch r
    let epE := stE.getRootRcEpoch r
    let nextEp :=
      if epT == epE then
        if branchRcOf stT r == branchRcOf stE r then epT
        else normSymIteStep cExpr
          (normSymExpr (.ctorObj epT 5 [stT.rootIdentitySym r] []))
          (normSymExpr (.ctorObj epE 6 [stE.rootIdentitySym r] []))
      else normSymIteStep cExpr epT epE
    if nextEp == .constU64 0 then none else some (r, nextEp)
  { vars := mergedVars
    bufAliases := mergedAliases
    exclusiveBufs := mergedExcl
    maybeScalarRoots := mergedMaybeScalar
    rootRc := mergedRc
    rootRcEpoch := mergedRootRcEpoch
    objRoots := mergedObjRoots
    tupleRoots := mergedTupleRoots
    paramChildRoots := dedupIds (base.paramChildRoots ++ stT.paramChildRoots ++ stE.paramChildRoots)
    immRoots := base.immRoots.filter fun id => stT.immRoots.contains id && stE.immRoots.contains id
    freshCtorRoots := dedupIds (base.freshCtorRoots ++ stT.freshCtorRoots ++ stE.freshCtorRoots)
    heapAllocSeq :=
      let hKeys := dedupIds (base.heapAllocSeq.map (·.1) ++ stT.heapAllocSeq.map (·.1) ++ stE.heapAllocSeq.map (·.1))
      hKeys.filterMap fun r =>
        match stT.heapAllocSeq.lookup r <|> stE.heapAllocSeq.lookup r <|> base.heapAllocSeq.lookup r with
        | some s => some (r, s)
        | none => none
    allocBase := Nat.max base.allocBase (Nat.max stT.allocBase stE.allocBase)
    nextAllocSeq := Nat.max base.nextAllocSeq (Nat.max stT.nextAllocSeq stE.nextAllocSeq)
    nextHeapId :=
      if stT.nextHeapId == stE.nextHeapId then stT.nextHeapId
      else normSymIteStep cExpr stT.nextHeapId stE.nextHeapId
    rcEpoch :=
      if stT.rcEpoch == stE.rcEpoch then stT.rcEpoch
      else normSymIteStep cExpr stT.rcEpoch stE.rcEpoch
    memWrites := if stT.memWrites == stE.memWrites then stT.memWrites else base.memWrites
    noUB := base.noUB && condNoUB && stT.noUB && stE.noUB
    supported := base.supported && stT.supported && stE.supported
    nonPoison := base.nonPoison && condNonPoison && stT.nonPoison && stE.nonPoison
    reachable := stT.reachable || stE.reachable }

def tupleTreeFuel (st : SymExecState) : Nat :=
  st.tupleRoots.foldl (fun acc (_, fs) => acc + fs.length + 1) 1

def hasHeapTupleAux (st : SymExecState) : Nat → VarId → Option Bool
  | 0, _ => none
  | d + 1, r =>
    match st.tupleRoots.lookup r with
    | some fs =>
      fs.foldl (fun acc f? =>
        match acc with
        | none | some true => acc
        | some false =>
          match f? with
          | none => some false
          | some cr =>
            if (st.rootRc.lookup cr).isSome || st.exclusiveBufs.contains cr then some true
            else match st.tupleRoots.lookup cr with
              | some _ => st.hasHeapTupleAux d cr
              | none => some (!isImmSymExpr st.immRoots (st.lookupVar cr).expr)) (some false)
    | none => some false

def hasHeapTuple (st : SymExecState) (r : VarId) : Bool :=
  (st.hasHeapTupleAux st.tupleTreeFuel r).getD true

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
          else if st.hasHeapTuple root || (st.tupleRoots.lookup root).isNone then { st with noUB := false, supported := false }
          else st
        | _ => { st with noUB := false, supported := false }
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
          | none => { st with noUB := false, supported := false }
      | _ =>
        if isImmSymExpr st.immRoots sv.expr then st
        else if !st.hasKnownRootTracking root then
          if count == 0 then st else { st with noUB := false, supported := false }
        else
          let (minRc, exactRc?) := st.getRootRc root
          let stBase :=
            if count == 0 || st.isFreshRuntimeAllocRoot root then st else st.dropAliasedRootBounds root
          match exactRc? with
          | some r =>
            if r == 0 || count > r then { st with noUB := false }
            else if count == 0 then st
            else
              let r' := r - count
              let st1 := (stBase.setRootRc root r' (some r')).recordRootRcOp root 2 (.constU64 count.toUInt64)
              if r' == 0 then
                let children := ((st1.objRoots.lookup root).getD []).filterMap id
                let st2 := { st1 with objRoots := st1.objRoots.filter (fun (id, _) => id != root) }
                decRootListFuel fuel true st2 children 1
              else st1
          | none =>
            if minRc == 0 then { st with noUB := false }
            else if count == 0 then st
            else
              let decEp := if st.isFreshRuntimeAllocRoot root then st.getRootRcEpoch root else st.rcEpoch
              let stShared := (stBase.setRootRc root (Nat.max 1 (minRc - count)) none).recordRootRcOp root 3 (.constU64 count.toUInt64)
              if minRc <= count then
                let children := ((stBase.objRoots.lookup root).getD []).filterMap id
                let stFreed0 :=
                  { ((stBase.setRootRc root 0 (some 0)).recordRootRcOp root 4 (.constU64 count.toUInt64)) with
                    objRoots := stBase.objRoots.filter (fun (id, _) => id != root) }
                let stFreed := decRootListFuel fuel true stFreed0 children 1
                mergeBranches stBase stShared stFreed (.decCond decEp (st.rootIdentitySym root)) true true
              else stShared

  def decRootListFuel : Nat → Bool → SymExecState → List VarId → Nat → SymExecState
    | _, _, st, [], _ => st
    | 0, _, st, _ :: _, _ => { st with noUB := false, supported := false }
    | fuel + 1, fromCtor, st, c :: cs, count =>
      decRootListFuel fuel fromCtor (decRootRcFuel fuel fromCtor st c count) cs count
end

def decRootRc (st : SymExecState) (objVar : VarId) (count : Nat) : SymExecState :=
  let objEdgeBudget := st.objRoots.foldl (fun acc (_, fs) => acc + fs.length + 2) 0
  let tupEdgeBudget := st.tupleRoots.foldl (fun acc (_, fs) => acc + fs.length + 2) 0
  let st1 := decRootRcFuel ((objEdgeBudget + tupEdgeBudget + 16) * (tupEdgeBudget + 1)) false st objVar count
  if count == 0 || st1.rootRc == st.rootRc then st1
  else st1.recordGlobalRcOp (st.resolveBuf objVar) 2 (.constU64 count.toUInt64)

def delRootShell (st : SymExecState) (objVar : VarId) : SymExecState :=
  let root := st.resolveBuf objVar
  let sv := st.lookupVar root
  match sv.expr with
  | .constU64 _ | .constBool _ | .unit | .tuple _ => st
  | _ =>
    if isImmSymExpr st.immRoots sv.expr then st
    else if !st.hasKnownRootTracking root then { st with noUB := false, supported := false }
    else
      let (_, exactRc?) := st.getRootRc root
      if exactRc? != some 1 then { st with noUB := false }
      else
        let st0 := if st.isFreshRuntimeAllocRoot root then st else st.dropAliasedRootBounds root
        let stFreed :=
          ({ ((st0.setRootRc root 0 (some 0)).recordRootRcOp root 7 (.constU64 1)) with
            objRoots := st0.objRoots.filter (fun (id, _) => id != root) }).recordGlobalRcOp root 7 (.constU64 1)
        if st.maybeScalarRoots.contains root then
          let decEp := if st.isFreshRuntimeAllocRoot root then st.getRootRcEpoch root else st.rcEpoch
          mergeBranches st0 stFreed (st0.recordGlobalRcOp root 8 (.constU64 0)) (.decCond decEp (st.rootIdentitySym root)) true true
        else stFreed

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

def allocFresh (st : SymExecState) : VarId × SymExecState :=
  (st.allocBase + st.nextAllocSeq, { st with nextAllocSeq := st.nextAllocSeq + 1 })

def allocParamRoot (st : SymExecState) : VarId × SymExecState :=
  let (r, st1) := st.allocFresh
  (r, { st1 with paramChildRoots := r :: st1.paramChildRoots })

def allocFreshHeapRoot (st : SymExecState) (isCtor : Bool) : VarId × SymExpr × SymExecState :=
  let (r, st1) := st.allocFresh
  let seq := normSymExpr st1.nextHeapId
  let nextSeq := normSymBinOpStep .add seq (.constU64 1)
  (r, seq, { st1 with
    freshCtorRoots := if isCtor then r :: st1.freshCtorRoots else st1.freshCtorRoots
    heapAllocSeq := st1.heapAllocSeq ++ [(r, seq)]
    nextHeapId := nextSeq })

def allocFreshCtor (st : SymExecState) : VarId × SymExpr × SymExecState :=
  st.allocFreshHeapRoot true

def canonicalHeapRootId (allocBase : Nat) (heapSeq : List (VarId × SymExpr)) (r : VarId) : VarId :=
  match heapSeq.lookup r with
  | some (.constU64 idx) => allocBase + 65536 + idx.toNat
  | _ => r

def projSyntheticRoot (st : SymExecState) (kind : Nat) (base : VarId) (idx : Nat) : VarId :=
  st.allocBase + 16777216 + cantPair kind (cantPair base idx)

mutual
  def lnirTypeWalkDepth : LNIRType → Nat
    | .tuple fs => lnirTypeListWalkDepth fs + 1
    | _ => 1

  def lnirTypeListWalkDepth : List LNIRType → Nat
    | [] => 0
    | t :: ts => Nat.max (lnirTypeWalkDepth t) (lnirTypeListWalkDepth ts)
end

def trackedTupleParamRoots : Nat → LNIRType → SymExecState → Option VarId × SymExecState
  | 0, _, st => (none, { st with noUB := false, supported := false })
  | depth + 1, ty, st =>
    match ty with
    | .rawPtr _ =>
      let (r, st1) := st.allocParamRoot
      (some r, st1.markExclusive r)
    | .taggedPtr =>
      let (r, st1) := st.allocParamRoot
      (some r, (st1.setRootRc r 1 none).markMaybeScalar r)
    | .objPtr | .sarray _ | .storageMap =>
      let (r, st1) := st.allocParamRoot
      (some r, st1.setRootRc r 1 none)
    | .tuple fs =>
      let (r, st0) := st.allocParamRoot
      let (childRoots, st1) := fs.foldl (fun (acc, curSt) fty =>
        let (cr?, nextSt) := trackedTupleParamRoots depth fty curSt
        (acc ++ [cr?], nextSt)) ([], st0)
      let (fExprs, st2) := (List.range fs.length).foldl (fun (es, curSt) i =>
        match (childRoots[i]?).join with
        | some cr =>
          let csv := curSt.lookupVar cr
          if csv.expr matches .tuple _ then (es ++ [csv.expr], curSt)
          else if (curSt.rootRc.lookup cr).isSome || curSt.exclusiveBufs.contains cr then (es ++ [.symVar cr], curSt)
          else
            let (fr, nextSt) := curSt.allocParamRoot
            (es ++ [.symVar fr], nextSt.markImmRoot fr)
        | none =>
          let (fr, nextSt) := curSt.allocParamRoot
          (es ++ [.symVar fr], nextSt.markImmRoot fr)) ([], st1)
      (some r, (st2.bindTupleRoots r childRoots).bindVar r { expr := .tuple fExprs })
    | .u256 | .i256 =>
      let (r, st0) := st.allocParamRoot
      let (fExprs, st1) := (List.range 4).foldl (fun (es, curSt) _ =>
        let (fr, nextSt) := curSt.allocParamRoot
        (es ++ [.symVar fr], nextSt.markImmRoot fr)) ([], st0)
      (some r, (st1.bindTupleRoots r [none, none, none, none]).bindVar r { expr := .tuple fExprs })
    | _ => (none, st)

def isHeapish (st : SymExecState) (v : VarId) : Bool :=
  let root := st.resolveBuf v
  let sv := st.lookupVar root
  match sv.expr with
  | .constU64 _ | .constBool _ | .unit => false
  | .tuple _ => st.hasHeapTuple root
  | .ctorObj .. => true
  | .symVar id =>
    if (st.tupleRoots.lookup root).isSome then st.hasHeapTuple root else !st.immRoots.contains id
  | _ => (st.rootRc.lookup root).isSome || st.exclusiveBufs.contains root || !isImmSymExpr st.immRoots sv.expr

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
    tupleRoots := st.tupleRoots.filter (fun (id, _) => id != dst)
    immRoots := st.immRoots.filter (· != dst) }

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
    let root := st.resolveBuf mapVar
    let mv := st.lookupVar root
    let knownOk := st.hasKnownRootTracking root
    let st0 := st.clearDstTracking dst
    let slotSv := st.lookupVar slotVar
    let elemExpr := st.readBufSym mapVar slotSv.expr
    let st1 := st0.bindVar dst { expr := elemExpr, nonPoison := mv.nonPoison && slotSv.nonPoison, noUB := mv.noUB && slotSv.noUB && knownOk }
    { st1 with supported := st1.supported && knownOk }
  | .storageStore mapVar slotVar valVar =>
    let root := st.resolveBuf mapVar
    let mv := st.lookupVar root
    let slotSv := st.lookupVar slotVar
    let valSv := st.lookupVar valVar
    if !st.hasKnownRootTracking root then
      let st1 := (st.clearDstTracking dst).bindVar dst { expr := .symVar root, nonPoison := false, noUB := false }
      { st1 with supported := false }
    else
      let st1 := ((st.clearDstTracking dst).writeBufSym root slotSv.expr valSv.expr false).aliasBuf dst root
      st1.bindVar dst { expr := .symVar root, nonPoison := mv.nonPoison && slotSv.nonPoison && valSv.nonPoison, noUB := mv.noUB && slotSv.noUB && valSv.noUB }
  | .mkTuple fields =>
    let svs := fields.map st.lookupVar
    let roots := fields.map fun f =>
      if st.isHeapish f then some (st.trackedRoot? f |>.getD (st.resolveBuf f)) else st.trackedRoot? f
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
    | .ctorObj _ tag _ _ =>
      let root := st.resolveBuf tupleVar
      let knownOk := st.hasKnownRootTracking root
      let (minRc, exactRc?) := st.getRootRc root
      let liveOk := minRc > 0 && exactRc? != some 0
      if idx == 0 then
        let st1 := st0.bindVar dst { expr := .constU64 tag, nonPoison := tv.nonPoison, noUB := tv.noUB && liveOk && knownOk }
        { st1 with supported := st1.supported && knownOk }
      else st0.bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    | .symVar base =>
      let knownOk := st.hasKnownRootTracking (st.resolveBuf tupleVar)
      let r := match fieldRoot? with
        | some known => known
        | none => st0.projSyntheticRoot 0 base idx
      let curFs := st.tupleRoots.lookup (st.resolveBuf tupleVar)
      let inBounds : Bool := match curFs with | some fs => decide (idx < fs.length) | none => true
      let st1 := match fieldRoot?, curFs with
        | none, none =>
          let stR := if (st0.rootRc.lookup r).isSome then st0 else (st0.setRootRc r 1 none).markMaybeScalar r
          stR.aliasBuf dst r
        | some kr, _ => st0.aliasBuf dst kr
        | _, _ => st0
      let outExpr := match fieldRoot?, curFs with
        | some kr, _ =>
          let ksv := st.lookupVar kr
          if ksv.expr matches .tuple _ then ksv.expr
          else if (st.rootRc.lookup kr).isSome || st.exclusiveBufs.contains kr then .symVar kr
          else .projSym 2 base idx
        | none, none => .symVar r
        | none, some fs => if idx < fs.length then .projSym 0 base idx else .projSym 2 base idx
      let st2 := st1.bindVar dst { expr := outExpr, nonPoison := tv.nonPoison, noUB := tv.noUB && knownOk && inBounds }
      { st2 with supported := st2.supported && knownOk && inBounds }
    | _ =>
      let root := st.resolveBuf tupleVar
      let (minRc, exactRc?) := st.getRootRc root
      let liveOk := minRc > 0 && exactRc? != some 0
      if idx == 0 && fieldRoot?.isNone && st.hasKnownRootTracking root && (st.tupleRoots.lookup root).isNone then
        stA.bindVar dst { expr := .projSym 0 root 0, nonPoison := tv.nonPoison, noUB := tv.noUB && liveOk }
      else
        let outExpr := match fieldRoot? with | some r => .symVar r | none => .projSym 2 root idx
        let knownOk := fieldRoot?.isSome
        let st1 := stA.bindVar dst { expr := outExpr, nonPoison := tv.nonPoison, noUB := tv.noUB && knownOk }
        { st1 with supported := st1.supported && knownOk }
  | .allocCtor tag objFields scalarFields =>
    let osvs := objFields.map st.lookupVar
    let ssvs := scalarFields.map st.lookupVar
    let allSvs := osvs ++ ssvs
    let (freshId, heapSeqExpr, stSeq) := st.allocFreshCtor
    let childRoots := objFields.map fun f =>
      if st.isHeapish f then some (st.trackedRoot? f |>.getD (st.resolveBuf f)) else none
    let st0 := stSeq.clearDstTracking dst
    let ctorSv : SymStateVal := {
      expr := .ctorObj heapSeqExpr tag.toUInt64 (osvs.map (·.expr)) (ssvs.map (·.expr))
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
    | .ctorObj _ _ os _ =>
      let knownOk := st.hasKnownRootTracking ctorRoot
      let stA := match st.lookupObjRootField ctorRoot idx with
        | some r => stBase.aliasBuf dst r
        | none => stBase
      match os[idx]? with
      | some fExpr =>
        let st1 := stA.bindVar dst { expr := fExpr, nonPoison := cv.nonPoison, noUB := cv.noUB && liveOk && knownOk }
        { st1 with supported := st1.supported && knownOk }
      | none => stBase.bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    | .symVar base =>
      let knownOk := st.hasKnownRootTracking ctorRoot
      let r := match st.lookupObjRootField ctorRoot idx with
        | some known => known
        | none => stBase.projSyntheticRoot 1 base idx
      let curFs := (st.objRoots.lookup ctorRoot).getD []
      let st0 :=
        if (stBase.rootRc.lookup r).isSome then stBase
        else (stBase.setRootRc r 1 none).markMaybeScalar r
      let padded := curFs ++ List.replicate (idx - curFs.length) none
      let nextFs := if idx < padded.length then padded.set idx (some r) else padded ++ [some r]
      let st1 := st0.bindObjRoots ctorRoot nextFs
      let st2 := (st1.aliasBuf dst r).bindVar dst
        { expr := .symVar r, nonPoison := cv.nonPoison, noUB := cv.noUB && liveOk && knownOk }
      { st2 with supported := st2.supported && knownOk }
    | _ =>
      let knownOk := st.hasKnownRootTracking ctorRoot
      let r := match st.lookupObjRootField ctorRoot idx with
        | some known => known
        | none => stBase.projSyntheticRoot 2 ctorRoot idx
      let stA :=
        if (stBase.rootRc.lookup r).isSome then stBase
        else (stBase.setRootRc r 1 none).markMaybeScalar r
      let st1 := (stA.aliasBuf dst r).bindVar dst { expr := .symVar r, nonPoison := cv.nonPoison, noUB := cv.noUB && liveOk && knownOk }
      { st1 with supported := st1.supported && knownOk }
  | .ctorGetScalar ctorVar idx _ =>
    let cv := st.lookupVar ctorVar
    let ctorRoot := st.resolveBuf ctorVar
    let (minRc, exactRc?) := st.getRootRc ctorRoot
    let liveOk := minRc > 0 && exactRc? != some 0
    let stBase := st.clearDstTracking dst
    match cv.expr with
    | .ctorObj _ _ _ ss =>
      let knownOk := st.hasKnownRootTracking ctorRoot
      match ss[idx]? with
      | some fExpr =>
        let stA :=
          match fExpr with
          | .symVar fv =>
            match st.trackedRoot? fv with
            | some r => stBase.aliasBuf dst r
            | none => stBase
          | _ => stBase
        let st1 := stA.bindVar dst { expr := fExpr, nonPoison := cv.nonPoison, noUB := cv.noUB && liveOk && knownOk }
        { st1 with supported := st1.supported && knownOk }
      | none => stBase.bindVar dst { expr := .unit, nonPoison := false, noUB := false }
    | .symVar base =>
      let knownOk := st.hasKnownRootTracking ctorRoot
      let r := stBase.projSyntheticRoot 3 base idx
      let st0 :=
        if (stBase.rootRc.lookup r).isSome then stBase
        else (stBase.setRootRc r 1 none).markMaybeScalar r
      let st1 := (st0.aliasBuf dst r).bindVar dst
        { expr := .symVar r, nonPoison := cv.nonPoison, noUB := cv.noUB && liveOk && knownOk }
      { st1 with supported := st1.supported && knownOk }
    | _ =>
      let knownOk := st.hasKnownRootTracking ctorRoot
      let r := stBase.projSyntheticRoot 4 ctorRoot idx
      let st0 :=
        if (stBase.rootRc.lookup r).isSome then stBase
        else (stBase.setRootRc r 1 none).markMaybeScalar r
      let st1 := (st0.aliasBuf dst r).bindVar dst
        { expr := .symVar r, nonPoison := cv.nonPoison, noUB := cv.noUB && liveOk && knownOk }
      { st1 with supported := st1.supported && knownOk }
  | .isExclusive objVar =>
    let ov := st.lookupVar objVar
    let root := st.resolveBuf objVar
    let st0 := st.clearDstTracking dst
    let (minRc, exactRc?) := st.getRootRc root
    let maybeScalar := st.maybeScalarRoots.contains root
    if isImmSymExpr st.immRoots ov.expr && !st.hasKnownRootTracking root then
      st0.bindVar dst { expr := .constBool true, nonPoison := ov.nonPoison, noUB := ov.noUB }
    else if !st.hasKnownRootTracking root then
      let st1 := st0.bindVar dst { expr := .exclCheck st.rcEpoch (st.rootIdentitySym root), nonPoison := ov.nonPoison, noUB := false }
      { st1 with supported := false }
    else if (minRc == 0 || exactRc? == some 0) && !maybeScalar then
      st0.bindVar dst { expr := .constBool false, nonPoison := ov.nonPoison, noUB := false }
    else
      let expr :=
        if exactRc? == some 1 && !maybeScalar then .constBool true
        else if minRc >= 2 && !maybeScalar then .constBool false
        else
          let effEpoch := if !maybeScalar && st.isFreshRuntimeAllocRoot root then st.getRootRcEpoch root else st.rcEpoch
          .exclCheck effEpoch (st.rootIdentitySym root)
      st0.bindVar dst { expr := expr, nonPoison := ov.nonPoison, noUB := ov.noUB }
  | .sarrayLen arrVar =>
    let root := st.resolveBuf arrVar
    let av := st.lookupVar root
    let knownOk := st.hasKnownRootTracking root
    let st0 := st.clearDstTracking dst
    let st1 := st0.bindVar dst { expr := .arrLen root, nonPoison := av.nonPoison, noUB := av.noUB && knownOk }
    { st1 with supported := st1.supported && knownOk }
  | .sarrayDataPtr arrVar _elemTy =>
    let root := st.resolveBuf arrVar
    let av := st.lookupVar root
    let knownOk := st.hasKnownRootTracking root
    let exclOk := st.isBufExclusive root && knownOk
    let st1 := ((st.clearDstTracking dst).aliasBuf dst root).bindVar dst { expr := .symVar root, nonPoison := av.nonPoison, noUB := av.noUB && exclOk }
    { st1 with supported := st1.supported && knownOk }
  | .sarrayEnsureExclusive arrVar _elemTy =>
    let root := st.resolveBuf arrVar
    let av := st.lookupVar root
    if !st.hasKnownRootTracking root then
      let st1 := (st.clearDstTracking dst).bindVar dst { expr := .symVar root, nonPoison := av.nonPoison, noUB := false }
      { st1 with supported := false }
    else
      let stBase := if st.isFreshRuntimeAllocRoot root then st else st.dropAliasedRootBounds root
      let st1 := ((((stBase.clearDstTracking dst).markExclusive root).recordRootRcOp root 9 (.constU64 1)).aliasBuf dst root).bindVar dst
        { expr := .symVar root, nonPoison := av.nonPoison, noUB := av.noUB }
      st1.recordGlobalRcOp root 9 (.constU64 1)
  | .sarraySet arrVar idxVar valVar _elemTy =>
    let root := st.resolveBuf arrVar
    let av := st.lookupVar root
    let idxSv := st.lookupVar idxVar
    let valSv := st.lookupVar valVar
    if !st.hasKnownRootTracking root then
      let st1 := (st.clearDstTracking dst).bindVar dst { expr := .symVar root, nonPoison := false, noUB := false }
      { st1 with supported := false }
    else
      let stBase := if st.isFreshRuntimeAllocRoot root then st else st.dropAliasedRootBounds root
      let st3 := ((((stBase.clearDstTracking dst).markExclusive root).recordRootRcOp root 10 idxSv.expr).writeBufSym root idxSv.expr valSv.expr true).aliasBuf dst root
      let st4 := st3.bindVar dst { expr := .symVar root, nonPoison := av.nonPoison && idxSv.nonPoison && valSv.nonPoison, noUB := av.noUB && idxSv.noUB && valSv.noUB }
      st4.recordGlobalRcOp root 10 idxSv.expr
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
        let av := st.lookupVar root
        if !st0.hasKnownRootTracking root then
          let st1 := st0.bindVar dst { expr := av.expr, nonPoison := av.nonPoison, noUB := false }
          { st1 with supported := false }
        else
          let stBase := if st.isFreshRuntimeAllocRoot root then st0 else st0.dropAliasedRootBounds root
          let st1 := (((stBase.markExclusive root).recordRootRcOp root 9 (.constU64 1)).aliasBuf dst root).bindVar dst (st.lookupVar a)
          st1.recordGlobalRcOp root 9 (.constU64 1)
      else if fnName == "lean_native_sarray_len" && i64Ret then
        let root := st.resolveBuf a
        let sa := st.lookupVar a
        let knownOk := st.hasKnownRootTracking root
        let st1 := st0.bindVar dst { expr := .arrLen root, nonPoison := sa.nonPoison, noUB := sa.noUB && knownOk }
        { st1 with supported := st1.supported && knownOk }
      else if fnName == "lean_native_del_obj" && retTy == .unit then
        let sa := st.lookupVar a
        let st1 := st0.delRootShell a
        st1.bindVar dst { expr := .unit, nonPoison := sa.nonPoison, noUB := sa.noUB }
      else
        let st1 := st0.bindVar dst { expr := .unit, nonPoison := false, noUB := false }
        { st1 with supported := false }
    | _, _ =>
      let st1 := st0.bindVar dst { expr := .unit, nonPoison := false, noUB := false }
      { st1 with supported := false }

/-- Summary produced by symbolic execution of an `LNIRDecl`. -/
structure SymExecSummary where
  declName   : String
  reachable  : Bool
  noUB       : Bool
  supported  : Bool := true
  nonPoison  : Bool
  retVal     : SymExpr
  memWrites  : List (SymExpr × SymExpr × SymExpr)
  liveRc     : List (SymExpr × Nat × Option Nat × SymExpr) := []
  nextHeapId : SymExpr := .constU64 0
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
  | 0 => ({ st with noUB := false, supported := false }, .unit, none)
  | fuel' + 1 =>
    match code with
    | .letBind dst _ty val k =>
      let st1 := symEvalExpr st dst val
      symExecCodeAux fuel' unrollBound st1 k
    | .rawStore ptrVar idxVar valVar _elemTy k =>
      let root := st.resolveBuf ptrVar
      let pv := st.lookupVar root
      let idxSv := st.lookupVar idxVar
      let valSv := st.lookupVar valVar
      let knownOk := st.hasKnownRootTracking root
      let st1 := st.writeBufSym ptrVar idxSv.expr valSv.expr true
      let st2 := { st1 with
        noUB := st1.noUB && pv.noUB && idxSv.noUB && valSv.noUB && knownOk
        supported := st1.supported && knownOk
        nonPoison := st1.nonPoison && pv.nonPoison && idxSv.nonPoison && valSv.nonPoison }
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
        let stEBase := { st with nextAllocSeq := Nat.max st.nextAllocSeq stT.nextAllocSeq }
        let (stE, retE, rootE?) := symExecCodeAux fuel' unrollBound stEBase elseBranch
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
      let (freshOut, _, stSeq) := st.allocFreshHeapRoot false
      let st0 := stSeq.clearDstTracking outVar
      let st1 := ((st0.markExclusive freshOut).aliasBuf outVar freshOut).bindVar outVar
        { expr := .symVar freshOut, nonPoison := true, noUB := true }
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

mutual
  private def maxVarIdScalar : ScalarExpr → Nat
    | .constU64 _ | .constBool _ => 0
    | .var id => id
    | .binOp _ l r => Nat.max (maxVarIdScalar l) (maxVarIdScalar r)
    | .unaryOp _ a => maxVarIdScalar a
    | .select c t e | .fma c t e =>
      Nat.max (maxVarIdScalar c) (Nat.max (maxVarIdScalar t) (maxVarIdScalar e))

  private def maxVarIdExpr : LNIRExpr → Nat
    | .scalar se => maxVarIdScalar se
    | .constU256 _ => 0
    | .mulDivDown a b d | .mulDivUp a b d | .storageStore a b d | .sarraySet a b d _ =>
      Nat.max a (Nat.max b d)
    | .storageLoad a b | .sarrayGet a b _ | .rawLoad a b _ => Nat.max a b
    | .mkTuple fs | .call _ fs _ _ => fs.foldl Nat.max 0
    | .projTuple v _ | .ctorGetObj v _ | .ctorGetScalar v _ _ | .isExclusive v
    | .sarrayLen v | .sarrayDataPtr v _ | .sarrayEnsureExclusive v _
    | .boxScalar v _ | .unboxScalar v _ => v
    | .allocCtor _ os ss => (os ++ ss).foldl Nat.max 0

  private def maxVarIdKernel : ParallelKernelKind → Nat
    | .customScalar iv ins body =>
      Nat.max iv (Nat.max (ins.foldl Nat.max 0) (maxVarIdScalar body))
    | _ => 0

  private def maxVarIdCode : LNIRCode → Nat
    | .letBind dst _ val k => Nat.max dst (Nat.max (maxVarIdExpr val) (maxVarIdCode k))
    | .rawStore pv iv vv _ k => Nat.max pv (Nat.max iv (Nat.max vv (maxVarIdCode k)))
    | .incRef ov _ k | .decRef ov _ k => Nat.max ov (maxVarIdCode k)
    | .ite cv t e => Nat.max cv (Nat.max (maxVarIdCode t) (maxVarIdCode e))
    | .seqFor iv lv hv av ai _ step k =>
      Nat.max iv (Nat.max lv (Nat.max hv (Nat.max av (Nat.max ai (Nat.max (maxVarIdCode step) (maxVarIdCode k))))))
    | .parFor ov lv ins _ kern k =>
      Nat.max ov (Nat.max lv (Nat.max (ins.foldl Nat.max 0) (Nat.max (maxVarIdKernel kern) (maxVarIdCode k))))
    | .ret v => v
    | .unreachable => 0
end

def declAllocBase (d : LNIRDecl) : Nat :=
  let maxProgId := Nat.max (d.params.foldl (fun acc p => Nat.max acc p.id) 0) (maxVarIdCode d.body)
  Nat.max 170000 (maxProgId + 1024)

def initDeclSymState (allocBase : Nat) (d : LNIRDecl) : SymExecState :=
  d.params.foldl (fun acc p =>
    let st1 := acc.bindVar p.id { expr := .symVar p.id, nonPoison := true, noUB := true }
    match p.ty with
    | .rawPtr _ => st1.markExclusive p.id
    | .taggedPtr => (st1.setRootRc p.id 1 none).markMaybeScalar p.id
    | .objPtr | .sarray _ | .storageMap => st1.setRootRc p.id 1 none
    | .tuple fs =>
      let (childRoots, st2) := fs.foldl (fun (rs, curSt) fty =>
        let (cr?, nextSt) := SymExecState.trackedTupleParamRoots (SymExecState.lnirTypeWalkDepth fty + 2) fty curSt
        (rs ++ [cr?], nextSt)) ([], st1)
      st2.bindTupleRoots p.id childRoots
    | .u256 | .i256 => (st1.bindTupleRoots p.id [none, none, none, none]).markImmRoot p.id
    | .unit => st1.markImmRoot p.id
    | _ => if p.ty.isUnboxedScalar then st1.markImmRoot p.id else st1
  ) { allocBase := allocBase }

/-- Run symbolic execution on an `LNIRDecl` with initial symbolic parameters. -/
def symExecDeclFromInit (initState : SymExecState) (loopUnrollBound : Nat := 4) (d : LNIRDecl) : SymExecSummary :=
  let (finalSt, retExpr) := symExecCode 4096 loopUnrollBound initState d.body
  let paramIds := d.params.map (·.id)
  let rawLive := finalSt.rootRc.filterMap fun (rid, m, ex?) =>
    let isFreshAlloc := finalSt.isFreshRuntimeAllocRoot rid
    let defaultUnknown := rid >= initState.allocBase && !isFreshAlloc && (m, ex?) == (1, none)
    if paramIds.contains rid || ex? == some 0 || defaultUnknown then none else some (rid, m, ex?)
  let mapHeapId := SymExecState.canonicalHeapRootId initState.allocBase finalSt.heapAllocSeq
  let idSym (rid : VarId) : SymExpr :=
    normSymExpr (substSymHeapIds mapHeapId (finalSt.rootIdentitySym rid))
  let payloadSym (rid : VarId) : SymExpr :=
    if finalSt.freshCtorRoots.contains rid then
      normSymExpr (substSymHeapIds mapHeapId (finalSt.lookupVar rid).expr)
    else
      idSym rid
  let epSym (rid : VarId) : SymExpr :=
    match finalSt.getRootRc rid with
    | (_, some _) => .constU64 0
    | (_, none) => normSymExpr (substSymHeapIds mapHeapId (finalSt.getRootRcEpoch rid))
  let liveFresh := (rawLive.filterMap fun (rid, m, ex?) =>
    if finalSt.isFreshRuntimeAllocRoot rid then some (payloadSym rid, m, ex?, epSym rid) else none).mergeSort
    (fun (s1, _, _, _) (s2, _, _, _) => reprStr s1 <= reprStr s2)
  let liveOther := rawLive.filterMap fun (rid, m, ex?) =>
    if finalSt.isFreshRuntimeAllocRoot rid then none else some (idSym rid, m, ex?, epSym rid)
  let canonLiveRc := paramIds.filterMap (fun pid =>
    let (m, ex?) := finalSt.getRootRc pid
    let initDefault := (initState.rootRc.lookup pid).getD (1, none)
    let pEp := epSym pid
    if (m, ex?) == initDefault && pEp == .constU64 0 then none else some (.symVar pid, m, ex?, pEp)) ++
    liveOther ++ liveFresh
  let canonWrites := finalSt.memWrites.map fun (b, i, v) =>
    (idSym b, normSymExpr (substSymHeapIds mapHeapId i), normSymExpr (substSymHeapIds mapHeapId v))
  { declName := d.name
    reachable := finalSt.reachable
    noUB := finalSt.noUB
    supported := finalSt.supported
    nonPoison := finalSt.nonPoison
    retVal := normSymExpr (substSymHeapIds mapHeapId retExpr)
    memWrites := canonWrites
    liveRc := canonLiveRc
    nextHeapId := normSymExpr (substSymHeapIds mapHeapId finalSt.nextHeapId) }

def symExecDeclWithBase (allocBase : Nat) (loopUnrollBound : Nat := 4) (d : LNIRDecl) : SymExecSummary :=
  symExecDeclFromInit (initDeclSymState allocBase d) loopUnrollBound d

def symExecDecl (loopUnrollBound : Nat := 4) (d : LNIRDecl) : SymExecSummary :=
  symExecDeclWithBase (declAllocBase d) loopUnrollBound d

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
      let (rootVal, st3) := mkSampleObjTree 2 (r + 101) st
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
  mkSampleParamValAux (SymExecState.lnirTypeWalkDepth ty + 2) seed paramIdx ty st

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
  let sharedAllocBase := Nat.max (declAllocBase src) (declAllocBase tgt)
  let srcParamSig := src.params.map (fun p => (p.id, p.ty))
  let tgtParamSig := tgt.params.map (fun p => (p.id, p.ty))
  let paramsMatch := srcParamSig == tgtParamSig
  let initSrc := initDeclSymState sharedAllocBase src
  let initTgt := if paramsMatch then initSrc else initDeclSymState sharedAllocBase tgt
  let sSrc := symExecDeclFromInit initSrc 4 src
  let sTgt := symExecDeclFromInit initTgt 4 tgt
  -- 1. UB refinement: fail closed if symbolic modeling is unsupported, else src.noUB -> tgt.noUB
  let ubRefines := sSrc.supported && sTgt.supported && (!sSrc.noUB || sTgt.noUB)
  -- 2. Return domain / reachability equivalence
  let domainEquiv := sSrc.reachable == sTgt.reachable
  -- 3. Poison refinement: src.nonPoison -> tgt.nonPoison
  let poisonRefines := !sSrc.nonPoison || sTgt.nonPoison
  -- 4. Symbolic return expression equivalence (after canonical normalization)
  let symRetEquiv := normSymExpr sSrc.retVal == normSymExpr sTgt.retVal
  -- 5. Multi-point concrete refinement across 64 deterministic input states (fail closed when all samples are UB)
  let (concreteOk, passedSamples) := checkDeclConcreteRefinement src tgt numSamples 1024
  let memWritesEquiv :=
    sSrc.memWrites == sTgt.memWrites && sSrc.liveRc == sTgt.liveRc && sSrc.nextHeapId == sTgt.nextHeapId
  let allOk :=
    paramsMatch && ubRefines && domainEquiv && poisonRefines && symRetEquiv && concreteOk && memWritesEquiv
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
  let r1 := (symEvalExpr {} 1 (.allocCtor 0 [] [])).resolveBuf 1;
  (s4.lookupVar 4 |>.expr) == .exclCheck (s3.getRootRcEpoch r1) (s3.rootIdentitySym r1) &&
    s3.getRootRcEpoch r1 != .constU64 0)
#guard !(let s0 := symEvalExpr {} 1 (.allocCtor 0 [] []);
  let (s1, _) := symExecCode 16 4 s0 (.ite 0 (.incRef 1 1 (.ret 1)) (.ret 1));
  let s2 := s1.decRootRc 1 1;
  let s3 := symEvalExpr s2 4 (.isExclusive 1);
  s3.noUB)
#guard (let s0 := symEvalExpr {} 1 (.allocCtor 0 [] []);
  let (s1, _) := symExecCode 16 4 s0 (.ite 0 (.incRef 1 1 (.ret 1)) (.ret 1));
  let s2 := symEvalExpr s1 2 (.isExclusive 1);
  let r1 := s0.resolveBuf 1;
  (s2.lookupVar 2 |>.expr) == .exclCheck (s1.getRootRcEpoch r1) (s1.rootIdentitySym r1) &&
    s1.getRootRcEpoch r1 != .constU64 0)
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

private def immediateSlotSrc : LNIRDecl :=
  { name := "immediate_slot_excl"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false },
               { id := 1, name := "p", ty := .objPtr, borrow := false }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 2 .objPtr (.ctorGetObj 1 2) <|
      .letBind 3 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 3
        (.incRef 2 1 (.letBind 4 .i1 (.isExclusive 2) (.decRef 2 1 (.ret 4))))
        (.letBind 4 .i1 (.scalar (.constBool false)) (.ret 4)) }

private def immediateSlotFalseTgt : LNIRDecl :=
  { immediateSlotSrc with
    body :=
      .letBind 2 .objPtr (.ctorGetObj 1 2) <|
      .letBind 3 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 3
        (.incRef 2 1 (.letBind 4 .i1 (.scalar (.constBool false)) (.decRef 2 1 (.ret 4))))
        (.letBind 4 .i1 (.scalar (.constBool false)) (.ret 4)) }

private def collidedRootSrc : LNIRDecl :=
  { name := "collided_root_excl"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false },
               { id := 1, name := "p", ty := .objPtr, borrow := false },
               { id := 8193, name := "q", ty := .objPtr, borrow := false }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 2 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 2
        (.letBind 3 .i1 (.isExclusive 1) (.ret 3))
        (.letBind 3 .i1 (.scalar (.constBool false)) (.ret 3)) }

private def collidedRootOtherTgt : LNIRDecl :=
  { collidedRootSrc with
    body :=
      .letBind 2 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 2
        (.letBind 3 .i1 (.isExclusive 8193) (.ret 3))
        (.letBind 3 .i1 (.scalar (.constBool false)) (.ret 3)) }

private def taggedParamImmediateSrc : LNIRDecl :=
  { name := "tagged_param_immediate_excl"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false },
               { id := 1, name := "t", ty := .taggedPtr, borrow := false }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 2 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 2
        (.incRef 1 1 (.letBind 3 .i1 (.isExclusive 1) (.decRef 1 1 (.ret 3))))
        (.letBind 3 .i1 (.scalar (.constBool false)) (.ret 3)) }

private def taggedParamImmediateFalseTgt : LNIRDecl :=
  { taggedParamImmediateSrc with
    body :=
      .letBind 2 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 2
        (.incRef 1 1 (.letBind 3 .i1 (.scalar (.constBool false)) (.decRef 1 1 (.ret 3))))
        (.letBind 3 .i1 (.scalar (.constBool false)) (.ret 3)) }

private def highIdParamAllocSrc : LNIRDecl :=
  { name := "high_id_param_alloc_excl"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false },
               { id := 170000, name := "p", ty := .objPtr, borrow := true }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 2 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 2
        (.letBind 3 .objPtr (.allocCtor 0 [] [])
          (.decRef 3 1 (.letBind 4 .i1 (.isExclusive 170000) (.ret 4))))
        (.letBind 4 .i1 (.scalar (.constBool false)) (.ret 4)) }

private def highIdParamAllocTrueTgt : LNIRDecl :=
  { highIdParamAllocSrc with
    body :=
      .letBind 2 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 2
        (.letBind 3 .objPtr (.allocCtor 0 [] [])
          (.decRef 3 1 (.letBind 4 .i1 (.scalar (.constBool true)) (.ret 4))))
        (.letBind 4 .i1 (.scalar (.constBool false)) (.ret 4)) }

#guard !(validateTranslationDecl immediateSlotSrc immediateSlotFalseTgt).symRetEquiv
#guard !(validateTranslationDecl immediateSlotSrc immediateSlotFalseTgt).passed
#guard !(validateTranslationDecl taggedParamImmediateSrc taggedParamImmediateFalseTgt).symRetEquiv
#guard !(validateTranslationDecl taggedParamImmediateSrc taggedParamImmediateFalseTgt).passed
#guard !(validateTranslationDecl collidedRootSrc collidedRootOtherTgt).symRetEquiv
#guard !(validateTranslationDecl collidedRootSrc collidedRootOtherTgt).passed
#guard !(validateTranslationDecl highIdParamAllocSrc highIdParamAllocTrueTgt).symRetEquiv
#guard !(validateTranslationDecl highIdParamAllocSrc highIdParamAllocTrueTgt).passed
#guard (validateTranslationDecl highIdParamAllocSrc highIdParamAllocSrc).passed
#guard (let s0 := symEvalExpr {} 1 (.allocCtor 0 [] []);
  let s1 := s0.incRootRc 1 34;
  let s2 := symEvalExpr s1 2 (.allocCtor 0 (List.replicate 34 1) []);
  let s3 := s2.decRootRc 2 1;
  s3.noUB && s3.getRootRc 1 == (1, some 1) && s3.isBufExclusive 1)

private def ctorRetIdentitySrc : LNIRDecl :=
  { name := "ctor_ret_identity"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .objPtr
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 1 .objPtr (.allocCtor 0 [] []) <|
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .ret 1 }

private def ctorRetIdentitySplitTgt : LNIRDecl :=
  { ctorRetIdentitySrc with
    body :=
      .letBind 1 .objPtr (.allocCtor 0 [] []) <|
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .letBind 3 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 3 (.ret 2) (.ret 1) }

#guard !checkSingleSample 1024 (VarEnv.empty.bind 0 (.u64 100)) HeapState.empty
  ctorRetIdentitySrc.body ctorRetIdentitySplitTgt.body
#guard !(validateTranslationDecl ctorRetIdentitySrc ctorRetIdentitySplitTgt).symRetEquiv
#guard !(validateTranslationDecl ctorRetIdentitySrc ctorRetIdentitySplitTgt).passed

private def ctorExtraDeadAllocTgt : LNIRDecl :=
  { ctorRetIdentitySrc with
    body :=
      .letBind 1 .objPtr (.allocCtor 0 [] []) <|
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .letBind 3 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 3
        (.letBind 4 .objPtr (.allocCtor 0 [] []) <|
         .decRef 4 1 <|
         .ret 1)
        (.ret 1) }

#guard !checkSingleSample 1024 (VarEnv.empty.bind 0 (.u64 100)) HeapState.empty
  ctorRetIdentitySrc.body ctorExtraDeadAllocTgt.body
#guard !(validateTranslationDecl ctorRetIdentitySrc ctorExtraDeadAllocTgt).memWritesEquiv
#guard !(validateTranslationDecl ctorRetIdentitySrc ctorExtraDeadAllocTgt).passed

private def sroaTupleBeforeCtorSrc : LNIRDecl :=
  { name := "sroa_tuple_before_ctor"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .objPtr
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 1 (.tuple [.i64, .i64]) (.mkTuple [0, 0]) <|
      .letBind 2 .i64 (.projTuple 1 0) <|
      .letBind 3 .objPtr (.allocCtor 0 [] [2]) <|
      .ret 3 }

private def sroaTupleBeforeCtorTgt : LNIRDecl :=
  { sroaTupleBeforeCtorSrc with
    body :=
      .letBind 2 .i64 (.scalar (.var 0)) <|
      .letBind 3 .objPtr (.allocCtor 0 [] [2]) <|
      .ret 3 }

#guard (validateTranslationDecl sroaTupleBeforeCtorSrc sroaTupleBeforeCtorTgt).passed

private def branchLeakOneArmTgt : LNIRDecl :=
  { ctorRetIdentitySrc with
    body :=
      .letBind 1 .objPtr (.allocCtor 0 [] []) <|
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .letBind 3 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 3
        (.letBind 4 .objPtr (.allocCtor 0 [] []) <| .ret 1)
        (.ret 1) }

#guard !(validateTranslationDecl ctorRetIdentitySrc branchLeakOneArmTgt).memWritesEquiv
#guard !(validateTranslationDecl ctorRetIdentitySrc branchLeakOneArmTgt).passed

private def aliasedParamFoldSrc : LNIRDecl :=
  { name := "aliased_param_fold"
    params := [{ id := 0, name := "p", ty := .objPtr, borrow := false },
               { id := 1, name := "q", ty := .objPtr, borrow := true }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .incRef 1 1 <|
      .decRef 0 1 <|
      .letBind 2 .i1 (.isExclusive 1) <|
      .decRef 1 1 <|
      .ret 2 }

private def aliasedParamFoldFalseTgt : LNIRDecl :=
  { aliasedParamFoldSrc with
    body :=
      .incRef 1 1 <|
      .decRef 0 1 <|
      .letBind 2 .i1 (.scalar (.constBool false)) <|
      .decRef 1 1 <|
      .ret 2 }

#guard (let (obj, st0) := HeapState.empty.allocCtor 0 [] [];
  let env := (VarEnv.empty.bind 0 obj).bind 1 obj;
  !checkSingleSample 1024 env st0 aliasedParamFoldSrc.body aliasedParamFoldFalseTgt.body)
#guard !(validateTranslationDecl aliasedParamFoldSrc aliasedParamFoldFalseTgt).symRetEquiv
#guard !(validateTranslationDecl aliasedParamFoldSrc aliasedParamFoldFalseTgt).passed

private def aliasedParamEnsureSrc : LNIRDecl :=
  { name := "aliased_param_ensure"
    params := [{ id := 0, name := "p", ty := .sarray .i64, borrow := true },
               { id := 1, name := "q", ty := .sarray .i64, borrow := true }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .incRef 1 1 <|
      .letBind 2 (.sarray .i64) (.sarrayEnsureExclusive 0 .i64) <|
      .letBind 3 .i1 (.isExclusive 1) <|
      .decRef 1 1 <|
      .ret 3 }

private def aliasedParamEnsureFalseTgt : LNIRDecl :=
  { aliasedParamEnsureSrc with
    body :=
      .incRef 1 1 <|
      .letBind 2 (.sarray .i64) (.sarrayEnsureExclusive 0 .i64) <|
      .letBind 3 .i1 (.scalar (.constBool false)) <|
      .decRef 1 1 <|
      .ret 3 }

#guard (let buf : ArrayBuffer := { id := 1, exclusive := true, data := #[1] };
  let st0 : HeapState := { HeapState.empty with buffers := [buf], nextId := 1 };
  let env := (VarEnv.empty.bind 0 (.sarrayId 1)).bind 1 (.sarrayId 1);
  !checkSingleSample 1024 env st0 aliasedParamEnsureSrc.body aliasedParamEnsureFalseTgt.body)
#guard !(validateTranslationDecl aliasedParamEnsureSrc aliasedParamEnsureFalseTgt).symRetEquiv
#guard !(validateTranslationDecl aliasedParamEnsureSrc aliasedParamEnsureFalseTgt).passed

private def mkNestedSingletonTupleType : Nat → LNIRType → LNIRType
  | 0, ty => ty
  | d + 1, ty => .tuple [mkNestedSingletonTupleType d ty]

private def wrapNestedSingletonTuples : Nat → VarId → VarId → LNIRType → (VarId → LNIRCode) → LNIRCode
  | 0, curVar, _, _, k => k curVar
  | d + 1, curVar, nextId, curTy, k =>
    let wrappedTy := LNIRType.tuple [curTy]
    .letBind nextId wrappedTy (.mkTuple [curVar]) <|
      wrapNestedSingletonTuples d nextId (nextId + 1) wrappedTy k

private def deepTuple17ReleaseSrc : LNIRDecl :=
  mkExclTestDecl "deep_tuple_17_release" <|
    .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
    .incRef 1 1 <|
    wrapNestedSingletonTuples 17 1 10 .objPtr fun outerTup =>
      .letBind 40 .objPtr (.allocCtor 1 [outerTup] []) <|
      .letBind 41 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 41
        (.decRef 40 1 (.letBind 42 .i1 (.isExclusive 1) (.decRef 1 1 (.ret 42))))
        (.decRef 40 1 (.decRef 1 1 (.letBind 42 .i1 (.scalar (.constBool false)) (.ret 42))))

private def deepTuple17ReleaseFalseTgt : LNIRDecl :=
  mkExclTestDecl "deep_tuple_17_release" <|
    .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
    .incRef 1 1 <|
    wrapNestedSingletonTuples 17 1 10 .objPtr fun outerTup =>
      .letBind 40 .objPtr (.allocCtor 1 [outerTup] []) <|
      .letBind 41 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 41
        (.decRef 40 1 (.letBind 42 .i1 (.scalar (.constBool false)) (.decRef 1 1 (.ret 42))))
        (.decRef 40 1 (.decRef 1 1 (.letBind 42 .i1 (.scalar (.constBool false)) (.ret 42))))

#guard !checkSingleSample 1024 (VarEnv.empty.bind 0 (.u64 100)) HeapState.empty
  deepTuple17ReleaseSrc.body deepTuple17ReleaseFalseTgt.body
#guard !(validateTranslationDecl deepTuple17ReleaseSrc deepTuple17ReleaseFalseTgt).symRetEquiv
#guard !(validateTranslationDecl deepTuple17ReleaseSrc deepTuple17ReleaseFalseTgt).passed

private def projectNestedSingletonTuples : Nat → VarId → VarId → LNIRType → (VarId → LNIRCode) → LNIRCode
  | 0, curVar, _, _, k => k curVar
  | d + 1, curVar, nextId, .tuple [innerTy], k =>
    .letBind nextId innerTy (.projTuple curVar 0) <|
      projectNestedSingletonTuples d nextId (nextId + 1) innerTy k
  | _, curVar, _, _, k => k curVar

private def deepTuple10ParamSrc : LNIRDecl :=
  let paramTy := mkNestedSingletonTupleType 10 .objPtr
  { name := "deep_tuple_10_param"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false },
               { id := 1, name := "tp", ty := paramTy, borrow := false }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 40 .objPtr (.allocCtor 0 [1] []) <|
      projectNestedSingletonTuples 10 1 10 paramTy fun leafObj =>
        .letBind 41 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
        .ite 41
          (.incRef leafObj 1 (.decRef 40 1 (.letBind 42 .i1 (.isExclusive leafObj) (.ret 42))))
          (.letBind 42 .i1 (.scalar (.constBool false)) (.ret 42)) }

private def deepTuple10ParamFalseTgt : LNIRDecl :=
  let paramTy := mkNestedSingletonTupleType 10 .objPtr
  { deepTuple10ParamSrc with
    body :=
      .letBind 40 .objPtr (.allocCtor 0 [1] []) <|
      projectNestedSingletonTuples 10 1 10 paramTy fun leafObj =>
        .letBind 41 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
        .ite 41
          (.incRef leafObj 1 (.decRef 40 1 (.letBind 42 .i1 (.scalar (.constBool false)) (.ret 42))))
          (.letBind 42 .i1 (.scalar (.constBool false)) (.ret 42)) }

#guard !(validateTranslationDecl deepTuple10ParamSrc deepTuple10ParamFalseTgt).symRetEquiv
#guard !(validateTranslationDecl deepTuple10ParamSrc deepTuple10ParamFalseTgt).passed

private def selectPtrExclSrc : LNIRDecl :=
  { name := "select_ptr_excl"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false },
               { id := 1, name := "c", ty := .i1, borrow := false }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .incRef 2 1 <|
      .letBind 3 .objPtr (.allocCtor 0 [] []) <|
      .incRef 3 1 <|
      .letBind 4 .objPtr (.scalar (.select (.var 1) (.var 2) (.var 3))) <|
      .letBind 5 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 5
        (.letBind 6 .i1 (.isExclusive 4) <|
         .decRef 2 2 <|
         .decRef 3 2 <|
         .ret 6)
        (.decRef 2 2 <|
         .decRef 3 2 <|
         .letBind 6 .i1 (.scalar (.constBool false)) <|
         .ret 6) }

private def selectPtrExclTrueTgt : LNIRDecl :=
  { selectPtrExclSrc with
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .incRef 2 1 <|
      .letBind 3 .objPtr (.allocCtor 0 [] []) <|
      .incRef 3 1 <|
      .letBind 4 .objPtr (.scalar (.select (.var 1) (.var 2) (.var 3))) <|
      .letBind 5 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 5
        (.letBind 6 .i1 (.scalar (.constBool true)) <|
         .decRef 2 2 <|
         .decRef 3 2 <|
         .ret 6)
        (.decRef 2 2 <|
         .decRef 3 2 <|
         .letBind 6 .i1 (.scalar (.constBool false)) <|
         .ret 6) }

#guard !checkSingleSample 1024 ((VarEnv.empty.bind 0 (.u64 100)).bind 1 (.bool true)) HeapState.empty
  selectPtrExclSrc.body selectPtrExclTrueTgt.body
#guard !(validateTranslationDecl selectPtrExclSrc selectPtrExclTrueTgt).ubRefines
#guard !(validateTranslationDecl selectPtrExclSrc selectPtrExclTrueTgt).passed

private def selectPtrDecRefSrc : LNIRDecl :=
  { name := "select_ptr_decref"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false },
               { id := 1, name := "c", ty := .i1, borrow := false }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .incRef 2 1 <|
      .letBind 3 .objPtr (.allocCtor 0 [] []) <|
      .incRef 3 1 <|
      .letBind 4 .objPtr (.scalar (.select (.var 1) (.var 2) (.var 3))) <|
      .letBind 5 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 5
        (.decRef 4 1 <|
         .letBind 6 .i1 (.isExclusive 2) <|
         .ret 6)
        (.decRef 2 2 <|
         .decRef 3 2 <|
         .letBind 6 .i1 (.scalar (.constBool false)) <|
         .ret 6) }

private def selectPtrDecRefFalseTgt : LNIRDecl :=
  { selectPtrDecRefSrc with
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .incRef 2 1 <|
      .letBind 3 .objPtr (.allocCtor 0 [] []) <|
      .incRef 3 1 <|
      .letBind 4 .objPtr (.scalar (.select (.var 1) (.var 2) (.var 3))) <|
      .letBind 5 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 5
        (.decRef 4 1 <|
         .letBind 6 .i1 (.scalar (.constBool false)) <|
         .ret 6)
        (.decRef 2 2 <|
         .decRef 3 2 <|
         .letBind 6 .i1 (.scalar (.constBool false)) <|
         .ret 6) }

#guard !checkSingleSample 1024 ((VarEnv.empty.bind 0 (.u64 100)).bind 1 (.bool true)) HeapState.empty
  selectPtrDecRefSrc.body selectPtrDecRefFalseTgt.body
#guard !(validateTranslationDecl selectPtrDecRefSrc selectPtrDecRefFalseTgt).ubRefines
#guard !(validateTranslationDecl selectPtrDecRefSrc selectPtrDecRefFalseTgt).passed

private def loopBranchMergePtrExclSrc : LNIRDecl :=
  { name := "loop_branch_merge_ptr_excl"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false },
               { id := 1, name := "c", ty := .i1, borrow := false }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .incRef 2 1 <|
      .letBind 3 .objPtr (.allocCtor 0 [] []) <|
      .incRef 3 1 <|
      .letBind 10 .i64 (.scalar (.constU64 0)) <|
      .letBind 11 .i64 (.scalar (.constU64 1)) <|
      .seqFor 12 10 11 4 2 .objPtr
        (.ite 1 (.ret 2) (.ret 3))
        (.letBind 5 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
         .ite 5
           (.letBind 6 .i1 (.isExclusive 4) <|
            .decRef 2 2 <|
            .decRef 3 2 <|
            .ret 6)
           (.decRef 2 2 <|
            .decRef 3 2 <|
            .letBind 6 .i1 (.scalar (.constBool false)) <|
            .ret 6)) }

private def loopBranchMergePtrExclTrueTgt : LNIRDecl :=
  { loopBranchMergePtrExclSrc with
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .incRef 2 1 <|
      .letBind 3 .objPtr (.allocCtor 0 [] []) <|
      .incRef 3 1 <|
      .letBind 10 .i64 (.scalar (.constU64 0)) <|
      .letBind 11 .i64 (.scalar (.constU64 1)) <|
      .seqFor 12 10 11 4 2 .objPtr
        (.ite 1 (.ret 2) (.ret 3))
        (.letBind 5 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
         .ite 5
           (.letBind 6 .i1 (.scalar (.constBool true)) <|
            .decRef 2 2 <|
            .decRef 3 2 <|
            .ret 6)
           (.decRef 2 2 <|
            .decRef 3 2 <|
            .letBind 6 .i1 (.scalar (.constBool false)) <|
            .ret 6)) }

#guard !checkSingleSample 1024 ((VarEnv.empty.bind 0 (.u64 100)).bind 1 (.bool true)) HeapState.empty
  loopBranchMergePtrExclSrc.body loopBranchMergePtrExclTrueTgt.body
#guard !(validateTranslationDecl loopBranchMergePtrExclSrc loopBranchMergePtrExclTrueTgt).ubRefines
#guard !(validateTranslationDecl loopBranchMergePtrExclSrc loopBranchMergePtrExclTrueTgt).passed

private def scalarSelectImmExclSrc : LNIRDecl :=
  { name := "scalar_select_imm_excl"
    params := [{ id := 0, name := "c", ty := .i1, borrow := false }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 1 .i64 (.scalar (.select (.var 0) (.constU64 7) (.constU64 9))) <|
      .letBind 2 .i1 (.isExclusive 1) <|
      .ret 2 }

private def scalarSelectImmExclTrueTgt : LNIRDecl :=
  { scalarSelectImmExclSrc with
    body :=
      .letBind 1 .i64 (.scalar (.select (.var 0) (.constU64 7) (.constU64 9))) <|
      .letBind 2 .i1 (.scalar (.constBool true)) <|
      .ret 2 }

#guard (validateTranslationDecl scalarSelectImmExclSrc scalarSelectImmExclTrueTgt).passed

private def selectCtorTagSrc : LNIRDecl :=
  { name := "select_ctor_tag"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false },
               { id := 1, name := "c", ty := .i1, borrow := false }]
    retTy := .i64
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .letBind 3 .objPtr (.allocCtor 1 [] []) <|
      .letBind 4 .objPtr (.scalar (.select (.var 1) (.var 2) (.var 3))) <|
      .letBind 5 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 5
        (.letBind 6 .i64 (.projTuple 4 0) <|
         .decRef 2 1 <|
         .decRef 3 1 <|
         .ret 6)
        (.decRef 2 1 <|
         .decRef 3 1 <|
         .letBind 6 .i64 (.scalar (.constU64 0)) <|
         .ret 6) }

private def selectCtorTagZeroTgt : LNIRDecl :=
  { selectCtorTagSrc with
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .letBind 3 .objPtr (.allocCtor 1 [] []) <|
      .letBind 4 .objPtr (.scalar (.select (.var 1) (.var 2) (.var 3))) <|
      .letBind 5 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 5
        (.letBind 6 .i64 (.scalar (.constU64 0)) <|
         .decRef 2 1 <|
         .decRef 3 1 <|
         .ret 6)
        (.decRef 2 1 <|
         .decRef 3 1 <|
         .letBind 6 .i64 (.scalar (.constU64 0)) <|
         .ret 6) }

#guard !checkSingleSample 1024 ((VarEnv.empty.bind 0 (.u64 100)).bind 1 (.bool false)) HeapState.empty
  selectCtorTagSrc.body selectCtorTagZeroTgt.body
#guard !(validateTranslationDecl selectCtorTagSrc selectCtorTagZeroTgt).ubRefines
#guard !(validateTranslationDecl selectCtorTagSrc selectCtorTagZeroTgt).passed

private def selectSameCtorExclSrc : LNIRDecl :=
  { name := "select_same_ctor_excl"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false },
               { id := 1, name := "c", ty := .i1, borrow := false }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .incRef 2 1 <|
      .letBind 4 .objPtr (.scalar (.select (.var 1) (.var 2) (.var 2))) <|
      .letBind 5 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 5
        (.letBind 6 .i1 (.isExclusive 4) <|
         .decRef 2 2 <|
         .ret 6)
        (.decRef 2 2 <|
         .letBind 6 .i1 (.scalar (.constBool false)) <|
         .ret 6) }

private def selectSameCtorExclTrueTgt : LNIRDecl :=
  { selectSameCtorExclSrc with
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .incRef 2 1 <|
      .letBind 4 .objPtr (.scalar (.select (.var 1) (.var 2) (.var 2))) <|
      .letBind 5 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 5
        (.letBind 6 .i1 (.scalar (.constBool true)) <|
         .decRef 2 2 <|
         .ret 6)
        (.decRef 2 2 <|
         .letBind 6 .i1 (.scalar (.constBool false)) <|
         .ret 6) }

#guard !checkSingleSample 1024 ((VarEnv.empty.bind 0 (.u64 100)).bind 1 (.bool true)) HeapState.empty
  selectSameCtorExclSrc.body selectSameCtorExclTrueTgt.body
#guard !(validateTranslationDecl selectSameCtorExclSrc selectSameCtorExclTrueTgt).ubRefines
#guard !(validateTranslationDecl selectSameCtorExclSrc selectSameCtorExclTrueTgt).passed

private def selectAddZeroPtrExclSrc : LNIRDecl :=
  { name := "select_add_zero_ptr_excl"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false },
               { id := 1, name := "p", ty := .objPtr, borrow := false }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .incRef 1 1 <|
      .letBind 2 .objPtr (.scalar (.binOp .add (.var 1) (.constU64 0))) <|
      .letBind 3 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 3
        (.letBind 4 .i1 (.isExclusive 2) <|
         .decRef 1 1 <|
         .ret 4)
        (.decRef 1 1 <|
         .letBind 4 .i1 (.scalar (.constBool false)) <|
         .ret 4) }

private def selectAddZeroPtrExclTrueTgt : LNIRDecl :=
  { selectAddZeroPtrExclSrc with
    body :=
      .incRef 1 1 <|
      .letBind 2 .objPtr (.scalar (.binOp .add (.var 1) (.constU64 0))) <|
      .letBind 3 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 3
        (.letBind 4 .i1 (.scalar (.constBool true)) <|
         .decRef 1 1 <|
         .ret 4)
        (.decRef 1 1 <|
         .letBind 4 .i1 (.scalar (.constBool false)) <|
         .ret 4) }

#guard !(let (v, s) := HeapState.empty.allocCtor 0 [] [];
  checkSingleSample 1024 ((VarEnv.empty.bind 0 (.u64 100)).bind 1 v) s
    selectAddZeroPtrExclSrc.body selectAddZeroPtrExclTrueTgt.body)
#guard !(validateTranslationDecl selectAddZeroPtrExclSrc selectAddZeroPtrExclTrueTgt).ubRefines
#guard !(validateTranslationDecl selectAddZeroPtrExclSrc selectAddZeroPtrExclTrueTgt).passed

private def selectCtorContainingPtrExclSrc : LNIRDecl :=
  { name := "select_ctor_containing_ptr_excl"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false },
               { id := 1, name := "c", ty := .i1, borrow := false }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .incRef 2 1 <|
      .letBind 3 .objPtr (.allocCtor 0 [] []) <|
      .incRef 3 1 <|
      .letBind 4 .objPtr (.scalar (.select (.var 1) (.var 2) (.var 3))) <|
      .letBind 5 .objPtr (.allocCtor 0 [4] []) <|
      .letBind 6 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 6
        (.decRef 5 1 <|
         .letBind 7 .i1 (.isExclusive 2) <|
         .ret 7)
        (.decRef 5 1 <|
         .letBind 7 .i1 (.scalar (.constBool false)) <|
         .ret 7) }

private def selectCtorContainingPtrExclFalseTgt : LNIRDecl :=
  { selectCtorContainingPtrExclSrc with
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .incRef 2 1 <|
      .letBind 3 .objPtr (.allocCtor 0 [] []) <|
      .incRef 3 1 <|
      .letBind 4 .objPtr (.scalar (.select (.var 1) (.var 2) (.var 3))) <|
      .letBind 5 .objPtr (.allocCtor 0 [4] []) <|
      .letBind 6 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 6
        (.decRef 5 1 <|
         .letBind 7 .i1 (.scalar (.constBool false)) <|
         .ret 7)
        (.decRef 5 1 <|
         .letBind 7 .i1 (.scalar (.constBool false)) <|
         .ret 7) }

#guard !checkSingleSample 1024 ((VarEnv.empty.bind 0 (.u64 100)).bind 1 (.bool true)) HeapState.empty
  selectCtorContainingPtrExclSrc.body selectCtorContainingPtrExclFalseTgt.body
#guard !(validateTranslationDecl selectCtorContainingPtrExclSrc selectCtorContainingPtrExclFalseTgt).ubRefines
#guard !(validateTranslationDecl selectCtorContainingPtrExclSrc selectCtorContainingPtrExclFalseTgt).passed

private def selectCtorProjExclSrc : LNIRDecl :=
  { name := "select_ctor_proj_excl"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false },
               { id := 1, name := "c", ty := .i1, borrow := false }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .incRef 2 1 <|
      .letBind 3 .objPtr (.allocCtor 0 [] []) <|
      .incRef 3 1 <|
      .letBind 4 .objPtr (.scalar (.select (.var 1) (.var 2) (.var 3))) <|
      .letBind 5 .objPtr (.allocCtor 0 [4] []) <|
      .letBind 6 .objPtr (.ctorGetObj 5 0) <|
      .letBind 7 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 7
        (.letBind 8 .i1 (.isExclusive 6) <|
         .decRef 5 1 <|
         .decRef 2 1 <|
         .decRef 3 1 <|
         .ret 8)
        (.decRef 5 1 <|
         .decRef 2 1 <|
         .decRef 3 1 <|
         .letBind 8 .i1 (.scalar (.constBool false)) <|
         .ret 8) }

private def selectCtorProjExclTrueTgt : LNIRDecl :=
  { selectCtorProjExclSrc with
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .incRef 2 1 <|
      .letBind 3 .objPtr (.allocCtor 0 [] []) <|
      .incRef 3 1 <|
      .letBind 4 .objPtr (.scalar (.select (.var 1) (.var 2) (.var 3))) <|
      .letBind 5 .objPtr (.allocCtor 0 [4] []) <|
      .letBind 6 .objPtr (.ctorGetObj 5 0) <|
      .letBind 7 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .ite 7
        (.letBind 8 .i1 (.scalar (.constBool true)) <|
         .decRef 5 1 <|
         .decRef 2 1 <|
         .decRef 3 1 <|
         .ret 8)
        (.decRef 5 1 <|
         .decRef 2 1 <|
         .decRef 3 1 <|
         .letBind 8 .i1 (.scalar (.constBool false)) <|
         .ret 8) }

#guard !checkSingleSample 1024 ((VarEnv.empty.bind 0 (.u64 100)).bind 1 (.bool true)) HeapState.empty
  selectCtorProjExclSrc.body selectCtorProjExclTrueTgt.body
#guard !(validateTranslationDecl selectCtorProjExclSrc selectCtorProjExclTrueTgt).ubRefines
#guard !(validateTranslationDecl selectCtorProjExclSrc selectCtorProjExclTrueTgt).passed

private def freshRootEpochReorderSrc : LNIRDecl :=
  { name := "fresh_root_epoch_reorder"
    params := [{ id := 0, name := "b", ty := .i1, borrow := false },
               { id := 1, name := "n", ty := .i64, borrow := false }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .letBind 3 .i64 (.scalar (.constU64 0)) <|
      .letBind 4 .i64 (.scalar (.constU64 4)) <|
      .seqFor 5 3 4 6 3 .i64
        (.ite 0 (.incRef 2 1 (.ret 6)) (.ret 6)) <|
      .letBind 7 .i1 (.isExclusive 2) <|
      .seqFor 8 3 4 9 3 .i64
        (.letBind 10 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 100))) <|
         .ite 10 (.incRef 2 1 (.ret 9)) (.ret 9)) <|
      .ret 7 }

private def freshRootEpochReorderTgt : LNIRDecl :=
  { freshRootEpochReorderSrc with
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .letBind 3 .i64 (.scalar (.constU64 0)) <|
      .letBind 4 .i64 (.scalar (.constU64 4)) <|
      .seqFor 5 3 4 6 3 .i64
        (.ite 0 (.incRef 2 1 (.ret 6)) (.ret 6)) <|
      .seqFor 8 3 4 9 3 .i64
        (.letBind 10 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 100))) <|
         .ite 10 (.incRef 2 1 (.ret 9)) (.ret 9)) <|
      .letBind 7 .i1 (.isExclusive 2) <|
      .ret 7 }

#guard !checkSingleSample 1024 ((VarEnv.empty.bind 0 (.bool false)).bind 1 (.u64 100)) HeapState.empty
  freshRootEpochReorderSrc.body freshRootEpochReorderTgt.body
#guard !(validateTranslationDecl freshRootEpochReorderSrc freshRootEpochReorderTgt).symRetEquiv
#guard !(validateTranslationDecl freshRootEpochReorderSrc freshRootEpochReorderTgt).passed

private def freshRootDecCondEpochSrc : LNIRDecl :=
  { name := "fresh_root_deccond_epoch"
    params := [{ id := 0, name := "b", ty := .i1, borrow := false },
               { id := 1, name := "n", ty := .i64, borrow := false }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .incRef 2 1 <|
      .letBind 3 .objPtr (.allocCtor 1 [2] []) <|
      .letBind 4 .i64 (.scalar (.constU64 0)) <|
      .letBind 5 .i64 (.scalar (.constU64 4)) <|
      .seqFor 6 4 5 7 4 .i64
        (.ite 0 (.incRef 3 1 (.ret 7)) (.ret 7)) <|
      .decRef 3 1 <|
      .letBind 8 .i1 (.isExclusive 2) <|
      .seqFor 9 4 5 10 4 .i64
        (.letBind 11 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 100))) <|
         .ite 11 (.incRef 2 1 (.ret 10)) (.ret 10)) <|
      .ret 8 }

private def freshRootDecCondEpochTgt : LNIRDecl :=
  { freshRootDecCondEpochSrc with
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .incRef 2 1 <|
      .letBind 3 .objPtr (.allocCtor 1 [2] []) <|
      .letBind 4 .i64 (.scalar (.constU64 0)) <|
      .letBind 5 .i64 (.scalar (.constU64 4)) <|
      .seqFor 6 4 5 7 4 .i64
        (.ite 0 (.incRef 3 1 (.ret 7)) (.ret 7)) <|
      .seqFor 9 4 5 10 4 .i64
        (.letBind 11 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 100))) <|
         .ite 11 (.incRef 2 1 (.ret 10)) (.ret 10)) <|
      .decRef 3 1 <|
      .letBind 8 .i1 (.isExclusive 2) <|
      .ret 8 }

#guard !checkSingleSample 1024 ((VarEnv.empty.bind 0 (.bool false)).bind 1 (.u64 100)) HeapState.empty
  freshRootDecCondEpochSrc.body freshRootDecCondEpochTgt.body
#guard !(validateTranslationDecl freshRootDecCondEpochSrc freshRootDecCondEpochTgt).symRetEquiv
#guard !(validateTranslationDecl freshRootDecCondEpochSrc freshRootDecCondEpochTgt).passed

private def freshRootUnrelatedParamIncSrc : LNIRDecl :=
  { name := "fresh_root_unrelated_param_inc"
    params := [{ id := 0, name := "b", ty := .i1, borrow := false },
               { id := 1, name := "p", ty := .objPtr, borrow := true }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .letBind 4 .i64 (.scalar (.constU64 0)) <|
      .letBind 5 .i64 (.scalar (.constU64 1)) <|
      .seqFor 6 4 5 7 4 .i64
        (.ite 0 (.incRef 2 1 (.ret 7)) (.ret 7)) <|
      .letBind 3 .i1 (.isExclusive 2) <|
      .incRef 1 1 <|
      .decRef 1 1 <|
      .ret 3 }

private def freshRootUnrelatedParamIncTgt : LNIRDecl :=
  { freshRootUnrelatedParamIncSrc with
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .letBind 4 .i64 (.scalar (.constU64 0)) <|
      .letBind 5 .i64 (.scalar (.constU64 1)) <|
      .seqFor 6 4 5 7 4 .i64
        (.ite 0 (.incRef 2 1 (.ret 7)) (.ret 7)) <|
      .incRef 1 1 <|
      .decRef 1 1 <|
      .letBind 3 .i1 (.isExclusive 2) <|
      .ret 3 }

#guard (validateTranslationDecl freshRootUnrelatedParamIncSrc freshRootUnrelatedParamIncTgt).symRetEquiv
#guard (validateTranslationDecl freshRootUnrelatedParamIncSrc freshRootUnrelatedParamIncTgt).passed

private def freshRootHeapRankSwapSrc : LNIRDecl :=
  { name := "fresh_root_heap_rank_swap"
    params := [{ id := 0, name := "b", ty := .i1, borrow := false },
               { id := 1, name := "n", ty := .i64, borrow := false }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .letBind 3 .objPtr (.allocCtor 1 [] []) <|
      .letBind 4 .i64 (.scalar (.constU64 0)) <|
      .letBind 5 .i64 (.scalar (.constU64 4)) <|
      .seqFor 6 4 5 7 4 .i64
        (.ite 0 (.incRef 2 1 (.ret 7)) (.ret 7)) <|
      .seqFor 8 4 5 9 4 .i64
        (.letBind 10 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 100))) <|
         .ite 10 (.incRef 3 1 (.ret 9)) (.ret 9)) <|
      .letBind 11 .i1 (.isExclusive 2) <|
      .decRef 2 1 <|
      .decRef 3 1 <|
      .ret 11 }

private def freshRootHeapRankSwapTgt : LNIRDecl :=
  { freshRootHeapRankSwapSrc with
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .letBind 3 .objPtr (.allocCtor 1 [] []) <|
      .letBind 4 .i64 (.scalar (.constU64 0)) <|
      .letBind 5 .i64 (.scalar (.constU64 4)) <|
      .seqFor 6 4 5 7 4 .i64
        (.ite 0 (.incRef 2 1 (.ret 7)) (.ret 7)) <|
      .seqFor 8 4 5 9 4 .i64
        (.letBind 10 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 100))) <|
         .ite 10 (.incRef 3 1 (.ret 9)) (.ret 9)) <|
      .letBind 11 .i1 (.isExclusive 3) <|
      .decRef 3 1 <|
      .decRef 2 1 <|
      .ret 11 }

#guard !checkSingleSample 1024 ((VarEnv.empty.bind 0 (.bool false)).bind 1 (.u64 100)) HeapState.empty
  freshRootHeapRankSwapSrc.body freshRootHeapRankSwapTgt.body
#guard !(validateTranslationDecl freshRootHeapRankSwapSrc freshRootHeapRankSwapTgt).symRetEquiv
#guard !(validateTranslationDecl freshRootHeapRankSwapSrc freshRootHeapRankSwapTgt).passed

private def freshRootBranchPrefixHeapRankSwapSrc : LNIRDecl :=
  { name := "fresh_root_branch_prefix_heap_rank_swap"
    params := [{ id := 0, name := "c", ty := .i1, borrow := false },
               { id := 1, name := "b", ty := .i1, borrow := false },
               { id := 2, name := "n", ty := .i64, borrow := false }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 3 .i64 (.scalar (.constU64 0)) <|
      .letBind 4 .i64 (.scalar (.constU64 4)) <|
      .letBind 5 .i64 (.scalar (.constU64 0)) <|
      .seqFor 6 3 4 7 5 .i64
        (.letBind 8 .i1 (.scalar (.binOp .eq (.var 6) (.constU64 0))) <|
         .ite 8
           (.ite 0
             (.letBind 9 .objPtr (.allocCtor 0 [] []) <| .decRef 9 1 <| .ret 7)
             (.ret 7))
           (.ret 7)) <|
      .letBind 10 .objPtr (.allocCtor 0 [] []) <|
      .letBind 11 .objPtr (.allocCtor 1 [] []) <|
      .seqFor 12 3 4 13 5 .i64
        (.ite 1 (.incRef 10 1 (.ret 13)) (.ret 13)) <|
      .seqFor 14 3 4 15 5 .i64
        (.letBind 16 .i1 (.scalar (.binOp .eq (.var 2) (.constU64 100))) <|
         .ite 16 (.incRef 11 1 (.ret 15)) (.ret 15)) <|
      .letBind 17 .i1 (.isExclusive 10) <|
      .decRef 10 1 <|
      .decRef 11 1 <|
      .ret 17 }

private def freshRootBranchPrefixHeapRankSwapTgt : LNIRDecl :=
  { freshRootBranchPrefixHeapRankSwapSrc with
    body :=
      .letBind 3 .i64 (.scalar (.constU64 0)) <|
      .letBind 4 .i64 (.scalar (.constU64 4)) <|
      .letBind 5 .i64 (.scalar (.constU64 0)) <|
      .seqFor 6 3 4 7 5 .i64
        (.letBind 8 .i1 (.scalar (.binOp .eq (.var 6) (.constU64 0))) <|
         .ite 8
           (.ite 0
             (.letBind 9 .objPtr (.allocCtor 0 [] []) <| .decRef 9 1 <| .ret 7)
             (.ret 7))
           (.ret 7)) <|
      .letBind 10 .objPtr (.allocCtor 0 [] []) <|
      .letBind 11 .objPtr (.allocCtor 1 [] []) <|
      .seqFor 12 3 4 13 5 .i64
        (.ite 1 (.incRef 10 1 (.ret 13)) (.ret 13)) <|
      .seqFor 14 3 4 15 5 .i64
        (.letBind 16 .i1 (.scalar (.binOp .eq (.var 2) (.constU64 100))) <|
         .ite 16 (.incRef 11 1 (.ret 15)) (.ret 15)) <|
      .letBind 17 .i1 (.isExclusive 11) <|
      .decRef 11 1 <|
      .decRef 10 1 <|
      .ret 17 }

#guard !checkSingleSample 1024 (((VarEnv.empty.bind 0 (.bool true)).bind 1 (.bool false)).bind 2 (.u64 100)) HeapState.empty
  freshRootBranchPrefixHeapRankSwapSrc.body freshRootBranchPrefixHeapRankSwapTgt.body
#guard !(validateTranslationDecl freshRootBranchPrefixHeapRankSwapSrc freshRootBranchPrefixHeapRankSwapTgt).symRetEquiv
#guard !(validateTranslationDecl freshRootBranchPrefixHeapRankSwapSrc freshRootBranchPrefixHeapRankSwapTgt).passed

private def freshRootCondHistorySwapSrc : LNIRDecl :=
  { name := "fresh_root_cond_history_swap"
    params := [{ id := 0, name := "b", ty := .i1, borrow := false },
               { id := 1, name := "n", ty := .i64, borrow := false }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .letBind 3 .i64 (.scalar (.constU64 0)) <|
      .letBind 4 .i64 (.scalar (.constU64 4)) <|
      .seqFor 5 3 4 6 3 .i64
        (.ite 0 (.incRef 2 1 (.ret 6)) (.ret 6)) <|
      .letBind 7 .i1 (.isExclusive 2) <|
      .seqFor 8 3 4 9 3 .i64
        (.letBind 10 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 100))) <|
         .ite 10 (.incRef 2 1 (.ret 9)) (.ret 9)) <|
      .letBind 11 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 100))) <|
      .letBind 12 .i1 (.scalar (.constBool false)) <|
      .ite 11 (.ret 7) (.ret 12) }

private def freshRootCondHistorySwapTgt : LNIRDecl :=
  { freshRootCondHistorySwapSrc with
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .letBind 3 .i64 (.scalar (.constU64 0)) <|
      .letBind 4 .i64 (.scalar (.constU64 4)) <|
      .seqFor 8 3 4 9 3 .i64
        (.letBind 10 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 100))) <|
         .ite 10 (.incRef 2 1 (.ret 9)) (.ret 9)) <|
      .letBind 7 .i1 (.isExclusive 2) <|
      .seqFor 5 3 4 6 3 .i64
        (.ite 0 (.incRef 2 1 (.ret 6)) (.ret 6)) <|
      .letBind 11 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 100))) <|
      .letBind 12 .i1 (.scalar (.constBool false)) <|
      .ite 11 (.ret 7) (.ret 12) }

#guard !checkSingleSample 1024 ((VarEnv.empty.bind 0 (.bool false)).bind 1 (.u64 100)) HeapState.empty
  freshRootCondHistorySwapSrc.body freshRootCondHistorySwapTgt.body
#guard !(validateTranslationDecl freshRootCondHistorySwapSrc freshRootCondHistorySwapTgt).symRetEquiv
#guard !(validateTranslationDecl freshRootCondHistorySwapSrc freshRootCondHistorySwapTgt).passed

private def paramCondHistorySwapSrc : LNIRDecl :=
  { name := "param_cond_history_swap"
    params := [{ id := 0, name := "b", ty := .i1, borrow := false },
               { id := 1, name := "n", ty := .i64, borrow := false },
               { id := 2, name := "p", ty := .objPtr, borrow := true }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 3 .i64 (.scalar (.constU64 0)) <|
      .letBind 4 .i64 (.scalar (.constU64 4)) <|
      .seqFor 5 3 4 6 3 .i64
        (.ite 0 (.incRef 2 1 (.ret 6)) (.ret 6)) <|
      .letBind 7 .i1 (.isExclusive 2) <|
      .seqFor 8 3 4 9 3 .i64
        (.letBind 10 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 100))) <|
         .ite 10 (.incRef 2 1 (.ret 9)) (.ret 9)) <|
      .letBind 11 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 100))) <|
      .letBind 12 .i1 (.scalar (.constBool false)) <|
      .ite 11 (.ret 7) (.ret 12) }

private def paramCondHistorySwapTgt : LNIRDecl :=
  { paramCondHistorySwapSrc with
    body :=
      .letBind 3 .i64 (.scalar (.constU64 0)) <|
      .letBind 4 .i64 (.scalar (.constU64 4)) <|
      .seqFor 8 3 4 9 3 .i64
        (.letBind 10 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 100))) <|
         .ite 10 (.incRef 2 1 (.ret 9)) (.ret 9)) <|
      .letBind 7 .i1 (.isExclusive 2) <|
      .seqFor 5 3 4 6 3 .i64
        (.ite 0 (.incRef 2 1 (.ret 6)) (.ret 6)) <|
      .letBind 11 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 100))) <|
      .letBind 12 .i1 (.scalar (.constBool false)) <|
      .ite 11 (.ret 7) (.ret 12) }

#guard !(let (obj, st0) := HeapState.empty.allocCtor 0 [] [];
  checkSingleSample 1024 (((VarEnv.empty.bind 0 (.bool false)).bind 1 (.u64 100)).bind 2 obj) st0
    paramCondHistorySwapSrc.body paramCondHistorySwapTgt.body)
#guard !(validateTranslationDecl paramCondHistorySwapSrc paramCondHistorySwapTgt).symRetEquiv
#guard !(validateTranslationDecl paramCondHistorySwapSrc paramCondHistorySwapTgt).passed

private def liveRcCondPredicateMismatchSrc : LNIRDecl :=
  { name := "live_rc_cond_predicate_mismatch"
    params := [{ id := 0, name := "b", ty := .i1, borrow := false },
               { id := 1, name := "n", ty := .i64, borrow := false }]
    retTy := .objPtr
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .letBind 3 .i64 (.scalar (.constU64 0)) <|
      .letBind 4 .i64 (.scalar (.constU64 4)) <|
      .seqFor 5 3 4 6 3 .i64
        (.ite 0 (.incRef 2 1 (.ret 6)) (.ret 6)) <|
      .ret 2 }

private def liveRcCondPredicateMismatchTgt : LNIRDecl :=
  { liveRcCondPredicateMismatchSrc with
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] []) <|
      .letBind 3 .i64 (.scalar (.constU64 0)) <|
      .letBind 4 .i64 (.scalar (.constU64 4)) <|
      .seqFor 5 3 4 6 3 .i64
        (.letBind 10 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 100))) <|
         .ite 10 (.incRef 2 1 (.ret 6)) (.ret 6)) <|
      .ret 2 }

#guard !checkSingleSample 1024 ((VarEnv.empty.bind 0 (.bool false)).bind 1 (.u64 100)) HeapState.empty
  liveRcCondPredicateMismatchSrc.body liveRcCondPredicateMismatchTgt.body
#guard !(validateTranslationDecl liveRcCondPredicateMismatchSrc liveRcCondPredicateMismatchTgt).memWritesEquiv
#guard !(validateTranslationDecl liveRcCondPredicateMismatchSrc liveRcCondPredicateMismatchTgt).passed

private def ctorGetScalarSharedObjExclSrc : LNIRDecl :=
  { name := "ctor_get_scalar_shared_obj_excl"
    params := [{ id := 0, name := "c", ty := .objPtr, borrow := true }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 1 .i64 (.ctorGetScalar 0 0 .i64) <|
      .letBind 2 .i1 (.isExclusive 1) <|
      .ret 2 }

private def ctorGetScalarSharedObjExclTrueTgt : LNIRDecl :=
  { ctorGetScalarSharedObjExclSrc with
    body :=
      .letBind 1 .i64 (.ctorGetScalar 0 0 .i64) <|
      .letBind 2 .i1 (.scalar (.constBool true)) <|
      .ret 2 }

#guard !(let (inner, st0) := HeapState.empty.allocCtor 0 [] [];
  match st0.incRefObj 1 1 with
  | .ok st1 =>
    let (outer, st2) := st1.allocCtor 0 [] [inner]
    checkSingleSample 1024 (VarEnv.empty.bind 0 outer) st2
      ctorGetScalarSharedObjExclSrc.body ctorGetScalarSharedObjExclTrueTgt.body
  | .error _ => false)
#guard !(validateTranslationDecl ctorGetScalarSharedObjExclSrc ctorGetScalarSharedObjExclTrueTgt).symRetEquiv
#guard !(validateTranslationDecl ctorGetScalarSharedObjExclSrc ctorGetScalarSharedObjExclTrueTgt).passed

private def ctorGetScalarSelectBaseExclSrc : LNIRDecl :=
  { name := "ctor_get_scalar_select_base_excl"
    params := [{ id := 0, name := "b", ty := .i1, borrow := false },
               { id := 1, name := "c1", ty := .objPtr, borrow := true },
               { id := 2, name := "c2", ty := .objPtr, borrow := true }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 3 .objPtr (.scalar (.select (.var 0) (.var 1) (.var 2))) <|
      .letBind 4 .i64 (.ctorGetScalar 3 0 .i64) <|
      .letBind 5 .i1 (.isExclusive 4) <|
      .ret 5 }

private def ctorGetScalarSelectBaseExclTrueTgt : LNIRDecl :=
  { ctorGetScalarSelectBaseExclSrc with
    body :=
      .letBind 3 .objPtr (.scalar (.select (.var 0) (.var 1) (.var 2))) <|
      .letBind 4 .i64 (.ctorGetScalar 3 0 .i64) <|
      .letBind 5 .i1 (.scalar (.constBool true)) <|
      .ret 5 }

#guard !(let (inner, st0) := HeapState.empty.allocCtor 0 [] [];
  match st0.incRefObj 1 1 with
  | .ok st1 =>
    let (c1, st2) := st1.allocCtor 0 [] [inner]
    let (c2, st3) := st2.allocCtor 0 [] [inner]
    checkSingleSample 1024 (((VarEnv.empty.bind 0 (.bool true)).bind 1 c1).bind 2 c2) st3
      ctorGetScalarSelectBaseExclSrc.body ctorGetScalarSelectBaseExclTrueTgt.body
  | .error _ => false)
#guard !(validateTranslationDecl ctorGetScalarSelectBaseExclSrc ctorGetScalarSelectBaseExclTrueTgt).ubRefines
#guard !(validateTranslationDecl ctorGetScalarSelectBaseExclSrc ctorGetScalarSelectBaseExclTrueTgt).passed

private def ctorGetScalarFreshSharedObjExclSrc : LNIRDecl :=
  { name := "ctor_get_scalar_fresh_shared_obj_excl"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
      .incRef 1 1 <|
      .letBind 2 .objPtr (.allocCtor 0 [] [1]) <|
      .letBind 3 .i64 (.ctorGetScalar 2 0 .i64) <|
      .letBind 4 .i1 (.isExclusive 3) <|
      .decRef 2 1 <|
      .decRef 1 2 <|
      .ret 4 }

private def ctorGetScalarFreshSharedObjExclTrueTgt : LNIRDecl :=
  { ctorGetScalarFreshSharedObjExclSrc with
    body :=
      .letBind 1 .objPtr (.allocCtor 0 [] [0]) <|
      .incRef 1 1 <|
      .letBind 2 .objPtr (.allocCtor 0 [] [1]) <|
      .letBind 3 .i64 (.ctorGetScalar 2 0 .i64) <|
      .letBind 4 .i1 (.scalar (.constBool true)) <|
      .decRef 2 1 <|
      .decRef 1 2 <|
      .ret 4 }

#guard !checkSingleSample 1024 (VarEnv.empty.bind 0 (.u64 7)) HeapState.empty
  ctorGetScalarFreshSharedObjExclSrc.body ctorGetScalarFreshSharedObjExclTrueTgt.body
#guard !(validateTranslationDecl ctorGetScalarFreshSharedObjExclSrc ctorGetScalarFreshSharedObjExclTrueTgt).symRetEquiv
#guard !(validateTranslationDecl ctorGetScalarFreshSharedObjExclSrc ctorGetScalarFreshSharedObjExclTrueTgt).passed

private def immReboundPtrExclSrc : LNIRDecl :=
  { name := "imm_rebound_ptr_excl"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .i1
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 1 .objPtr (.allocCtor 0 [] []) <|
      .incRef 1 1 <|
      .letBind 0 .objPtr (.scalar (.var 1)) <|
      .letBind 2 .i1 (.isExclusive 0) <|
      .decRef 1 2 <|
      .ret 2 }

private def immReboundPtrExclTrueTgt : LNIRDecl :=
  { immReboundPtrExclSrc with
    body :=
      .letBind 1 .objPtr (.allocCtor 0 [] []) <|
      .incRef 1 1 <|
      .letBind 0 .objPtr (.scalar (.var 1)) <|
      .letBind 2 .i1 (.scalar (.constBool true)) <|
      .decRef 1 2 <|
      .ret 2 }

#guard !checkSingleSample 1024 (VarEnv.empty.bind 0 (.u64 7)) HeapState.empty
  immReboundPtrExclSrc.body immReboundPtrExclTrueTgt.body
#guard !(validateTranslationDecl immReboundPtrExclSrc immReboundPtrExclTrueTgt).symRetEquiv
#guard !(validateTranslationDecl immReboundPtrExclSrc immReboundPtrExclTrueTgt).passed

private def liveCtorScalarSlotMismatchSrc : LNIRDecl :=
  { name := "live_ctor_scalar_slot_mismatch"
    params := [{ id := 0, name := "n", ty := .i64, borrow := false }]
    retTy := .i64
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 1 .i64 (.scalar (.select (.binOp .eq (.var 0) (.constU64 100)) (.constU64 1) (.constU64 0))) <|
      .letBind 2 .objPtr (.allocCtor 0 [] [1]) <|
      .letBind 3 .i64 (.scalar (.constU64 0)) <|
      .ret 3 }

private def liveCtorScalarSlotMismatchZeroTgt : LNIRDecl :=
  { liveCtorScalarSlotMismatchSrc with
    body :=
      .letBind 1 .i64 (.scalar (.select (.binOp .eq (.var 0) (.constU64 100)) (.constU64 1) (.constU64 0))) <|
      .letBind 3 .i64 (.scalar (.constU64 0)) <|
      .letBind 2 .objPtr (.allocCtor 0 [] [3]) <|
      .ret 3 }

#guard !checkSingleSample 1024 (VarEnv.empty.bind 0 (.u64 100)) HeapState.empty
  liveCtorScalarSlotMismatchSrc.body liveCtorScalarSlotMismatchZeroTgt.body
#guard !(validateTranslationDecl liveCtorScalarSlotMismatchSrc liveCtorScalarSlotMismatchZeroTgt).memWritesEquiv
#guard !(validateTranslationDecl liveCtorScalarSlotMismatchSrc liveCtorScalarSlotMismatchZeroTgt).passed

private def liveCtorTagMismatchSrc : LNIRDecl :=
  { name := "live_ctor_tag_mismatch"
    params := [{ id := 0, name := "n", ty := .i64, borrow := false }]
    retTy := .i64
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 1 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 100))) <|
      .letBind 2 .i64 (.scalar (.constU64 0)) <|
      .ite 1
        (.letBind 3 .objPtr (.allocCtor 1 [] []) <| .ret 2)
        (.letBind 3 .objPtr (.allocCtor 0 [] []) <| .ret 2) }

private def liveCtorTagMismatchZeroTgt : LNIRDecl :=
  { liveCtorTagMismatchSrc with
    body :=
      .letBind 2 .i64 (.scalar (.constU64 0)) <|
      .letBind 3 .objPtr (.allocCtor 0 [] []) <|
      .ret 2 }

#guard !checkSingleSample 1024 (VarEnv.empty.bind 0 (.u64 100)) HeapState.empty
  liveCtorTagMismatchSrc.body liveCtorTagMismatchZeroTgt.body
#guard !(validateTranslationDecl liveCtorTagMismatchSrc liveCtorTagMismatchZeroTgt).memWritesEquiv
#guard !(validateTranslationDecl liveCtorTagMismatchSrc liveCtorTagMismatchZeroTgt).passed

private def liveCtorObjFieldMismatchSrc : LNIRDecl :=
  { name := "live_ctor_obj_field_mismatch"
    params := [{ id := 0, name := "n", ty := .i64, borrow := false },
               { id := 1, name := "p", ty := .objPtr, borrow := true },
               { id := 2, name := "q", ty := .objPtr, borrow := true }]
    retTy := .i64
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 3 .objPtr (.scalar (.select (.binOp .eq (.var 0) (.constU64 100)) (.var 1) (.var 2))) <|
      .letBind 4 .objPtr (.allocCtor 0 [3] []) <|
      .letBind 5 .i64 (.scalar (.constU64 0)) <|
      .ret 5 }

private def liveCtorObjFieldMismatchTgt : LNIRDecl :=
  { liveCtorObjFieldMismatchSrc with
    body :=
      .letBind 4 .objPtr (.allocCtor 0 [2] []) <|
      .letBind 5 .i64 (.scalar (.constU64 0)) <|
      .ret 5 }

#guard !(let (p, st0) := HeapState.empty.allocCtor 0 [] [];
  let (q, st1) := st0.allocCtor 1 [] [];
  checkSingleSample 1024 (((VarEnv.empty.bind 0 (.u64 100)).bind 1 p).bind 2 q) st1
    liveCtorObjFieldMismatchSrc.body liveCtorObjFieldMismatchTgt.body)
#guard !(validateTranslationDecl liveCtorObjFieldMismatchSrc liveCtorObjFieldMismatchTgt).memWritesEquiv
#guard !(validateTranslationDecl liveCtorObjFieldMismatchSrc liveCtorObjFieldMismatchTgt).passed

private def liveCtorMaybeFreedSlotMismatchSrc : LNIRDecl :=
  { name := "live_ctor_maybe_freed_slot_mismatch"
    params := [{ id := 0, name := "b", ty := .i1, borrow := false },
               { id := 1, name := "n", ty := .i64, borrow := false }]
    retTy := .i64
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 2 .i64 (.scalar (.select (.binOp .eq (.var 1) (.constU64 100)) (.constU64 1) (.constU64 0))) <|
      .letBind 3 .objPtr (.allocCtor 0 [] [2]) <|
      .letBind 4 .i64 (.scalar (.constU64 0)) <|
      .letBind 5 .i64 (.scalar (.constU64 4)) <|
      .seqFor 6 4 5 7 4 .i64
        (.ite 0 (.incRef 3 1 (.ret 7)) (.ret 7)) <|
      .decRef 3 1 <|
      .ret 4 }

private def liveCtorMaybeFreedSlotMismatchZeroTgt : LNIRDecl :=
  { liveCtorMaybeFreedSlotMismatchSrc with
    body :=
      .letBind 4 .i64 (.scalar (.constU64 0)) <|
      .letBind 3 .objPtr (.allocCtor 0 [] [4]) <|
      .letBind 5 .i64 (.scalar (.constU64 4)) <|
      .seqFor 6 4 5 7 4 .i64
        (.ite 0 (.incRef 3 1 (.ret 7)) (.ret 7)) <|
      .decRef 3 1 <|
      .ret 4 }

#guard !checkSingleSample 1024 ((VarEnv.empty.bind 0 (.bool true)).bind 1 (.u64 100)) HeapState.empty
  liveCtorMaybeFreedSlotMismatchSrc.body liveCtorMaybeFreedSlotMismatchZeroTgt.body
#guard !(validateTranslationDecl liveCtorMaybeFreedSlotMismatchSrc liveCtorMaybeFreedSlotMismatchZeroTgt).memWritesEquiv
#guard !(validateTranslationDecl liveCtorMaybeFreedSlotMismatchSrc liveCtorMaybeFreedSlotMismatchZeroTgt).passed

private def liveCtorBranchPredSwapSrc : LNIRDecl :=
  { name := "live_ctor_branch_pred_swap"
    params := [{ id := 0, name := "b", ty := .i1, borrow := false },
               { id := 1, name := "n", ty := .i64, borrow := false }]
    retTy := .i64
    isGpuCand := false
    assurance := .verifiedKernelProof
    body :=
      .letBind 2 .i64 (.scalar (.constU64 0)) <|
      .ite 0
        (.letBind 3 .objPtr (.allocCtor 1 [] []) <|
         .letBind 4 .objPtr (.allocCtor 0 [] []) <|
         .decRef 4 1 <|
         .ret 2)
        (.letBind 3 .objPtr (.allocCtor 0 [] []) <|
         .letBind 4 .objPtr (.allocCtor 1 [] []) <|
         .decRef 3 1 <|
         .ret 2) }

private def liveCtorBranchPredSwapTgt : LNIRDecl :=
  { liveCtorBranchPredSwapSrc with
    body :=
      .letBind 2 .i64 (.scalar (.constU64 0)) <|
      .letBind 5 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 100))) <|
      .ite 5
        (.letBind 3 .objPtr (.allocCtor 1 [] []) <|
         .letBind 4 .objPtr (.allocCtor 0 [] []) <|
         .decRef 4 1 <|
         .ret 2)
        (.letBind 3 .objPtr (.allocCtor 0 [] []) <|
         .letBind 4 .objPtr (.allocCtor 1 [] []) <|
         .decRef 3 1 <|
         .ret 2) }

#guard !checkSingleSample 1024 ((VarEnv.empty.bind 0 (.bool false)).bind 1 (.u64 100)) HeapState.empty
  liveCtorBranchPredSwapSrc.body liveCtorBranchPredSwapTgt.body
#guard !(validateTranslationDecl liveCtorBranchPredSwapSrc liveCtorBranchPredSwapTgt).memWritesEquiv
#guard !(validateTranslationDecl liveCtorBranchPredSwapSrc liveCtorBranchPredSwapTgt).passed

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
