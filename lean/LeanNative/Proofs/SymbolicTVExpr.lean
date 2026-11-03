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
# Symbolic Expression AST & Canonical Normalizer (`LeanNative.Proofs.SymbolicTVExpr`)

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

/-- Disjoint heap/buffer write and slot spaces (C1.1 / C4.2): buffer elements (`0`: `sarray`/`storageMap`/`rawPtr`),
    constructor object fields (`1`: `objFields`), constructor scalar fields (`2`: `scalarFields`), and constructor tags (`3`: `tag`). -/
abbrev MemWriteSpace := UInt8

namespace MemWriteSpace

@[inline] def sarray     : MemWriteSpace := 0
@[inline] def ctorObj    : MemWriteSpace := 1
@[inline] def ctorScalar : MemWriteSpace := 2
@[inline] def ctorTag    : MemWriteSpace := 3

@[inline] def ord (sp : MemWriteSpace) : Nat := sp.toNat

end MemWriteSpace

/-- Symbolic value expression in the Alive2-style translation validation domain. -/
inductive SymExpr where
  | constU64  (val : UInt64)
  | constU256 (val : UInt256)
  | constBool (val : Bool)
  | symVar    (id : VarId)
  | allocTag  (root : VarId)
  | rcSym     (epoch : Nat) (root : VarId)
  | ctorTag   (epoch : Nat) (root : VarId)
  | ctorLen   (isScalar : Bool) (epoch : Nat) (root : VarId)
  | sarrayLen (root : VarId)
  | mulDiv256 (isUp : Bool) (a b denom : SymExpr)
  | binOp     (op : BinOp) (lhs rhs : SymExpr)
  | unaryOp   (op : UnaryOp) (arg : SymExpr)
  | ite       (cond thenVal elseVal : SymExpr)
  | tuple     (fields : List SymExpr)
  | bufElem   (space : MemWriteSpace) (bufVar : VarId) (idx : SymExpr)
  | unit
  deriving Repr, Inhabited

namespace SymExpr

mutual
  def beq : SymExpr → SymExpr → Bool
    | .constU64 a, .constU64 b => a == b
    | .constU256 a, .constU256 b => a == b
    | .constBool a, .constBool b => a == b
    | .symVar a, .symVar b => a == b
    | .allocTag a, .allocTag b => a == b
    | .rcSym ea a, .rcSym eb b => ea == eb && a == b
    | .ctorTag ea a, .ctorTag eb b => ea == eb && a == b
    | .ctorLen sa ea a, .ctorLen sb eb b => sa == sb && ea == eb && a == b
    | .sarrayLen a, .sarrayLen b => a == b
    | .mulDiv256 ua a1 b1 d1, .mulDiv256 ub a2 b2 d2 =>
      ua == ub && beq a1 a2 && beq b1 b2 && beq d1 d2
    | .binOp oa l1 r1, .binOp ob l2 r2 =>
      oa == ob && beq l1 l2 && beq r1 r2
    | .unaryOp oa a1, .unaryOp ob a2 =>
      oa == ob && beq a1 a2
    | .ite c1 t1 e1, .ite c2 t2 e2 =>
      beq c1 c2 && beq t1 t2 && beq e1 e2
    | .tuple fs1, .tuple fs2 => beqList fs1 fs2
    | .bufElem sp1 b1 i1, .bufElem sp2 b2 i2 =>
      sp1 == sp2 && b1 == b2 && beq i1 i2
    | .unit, .unit => true
    | _, _ => false

  def beqList : List SymExpr → List SymExpr → Bool
    | [], [] => true
    | a :: as, b :: bs => beq a b && beqList as bs
    | _, _ => false
end

instance : BEq SymExpr := ⟨SymExpr.beq⟩

/-- Deterministic structural rank used to canonicalize commutative binary operators.
    Constants receive the highest rank so they are pushed to the right-hand side (`x + c`). -/
def rank : SymExpr → Nat
  | .symVar id       => 10 + id
  | .allocTag id     => 500 + id
  | .rcSym ep id     => 600 + ep * 16 + id
  | .ctorTag ep id   => 650 + ep * 16 + id
  | .ctorLen sc ep id => 700 + (if sc then 8 else 0) + ep * 16 + id
  | .sarrayLen id    => 800 + id
  | .bufElem sp b _  => 1000 + sp.ord * 256 + b
  | .unaryOp _ a     => 2000 + rank a
  | .mulDiv256 _ a b d => 2500 + rank a + rank b + rank d
  | .binOp _ l r     => 3000 + rank l + rank r
  | .ite c t e       => 4000 + rank c + rank t + rank e
  | .tuple fs        => 5000 + fs.length
  | .constBool false => 900000
  | .constBool true  => 900001
  | .constU64 v      => 1000000 + (v % 65536).toNat
  | .constU256 w     => 1500000 + (w.lo0 % 65536).toNat
  | .unit            => 2000000

/-- Check whether `op` is commutative in `SymExpr`. -/
def isCommutative : BinOp → Bool
  | .add | .mul | .bitAnd | .bitOr | .bitXor | .eq => true
  | _ => false

end SymExpr

/-- Alive2-style symbolic value paired with `nonPoison` and `noUB` validity conditions. -/
structure SymStateVal where
  expr      : SymExpr
  nonPoison : Bool := true
  noUB      : Bool := true
  deriving Repr, Inhabited, BEq

def pow2ShiftLog2 : UInt64 → Option UInt64
  | 2 => some 1 | 4 => some 2 | 8 => some 3
  | 16 => some 4 | 32 => some 5
  | _ => none

def exprDefinitely64 (e : SymExpr) : Bool :=
  match e with
  | .constU64 _ | .rcSym _ _ | .ctorTag _ _ | .ctorLen _ _ _ | .sarrayLen _ => true
  | _ => false

/-- Check whether `e` is syntactically guaranteed to evaluate to a `.u64` whenever `w64` holds
    on an enclosing `.binOp` over `(e ± constU64 a)`: whenever `a != 0`, `evalBinOp (.add/.sub) vx (.u64 a)`
    succeeds ONLY when `vx` is `.u64`! -/
def subexprDefinitely64 (w64 : Bool) (a : UInt64) (e : SymExpr) : Bool :=
  (w64 && (a != 0)) || exprDefinitely64 e

def atomDefinitelyBool : SymExpr → Bool
  | .constBool _ | .binOp .eq _ _ | .binOp .lt _ _ | .binOp .le _ _ => true
  | .ite c t (.constBool false) => atomDefinitelyBool c && atomDefinitelyBool t
  | _ => false

/-- Extract core body of `normSymBinOpStep` after commutativity ordering (`l`, `r`) and width flag (`w64`),
    dispatching on `op` first so each operator's matcher stays compact. -/
def normSymBinOpCore (op : BinOp) (l r : SymExpr) (w64 : Bool) : SymExpr :=
  match op with
  | .add =>
    match l, r with
    | .constU64 a, .constU64 b => .constU64 (a + b)
    | .constU256 a, .constU256 b => .constU256 (UInt256.add a b)
    | x, .constU256 w | .constU256 w, x =>
      if w == UInt256.zero then x else .binOp .add l r
    | x, .constU64 0 | .constU64 0, x => x
    | .binOp .add x (.constU64 a), .constU64 b =>
      if subexprDefinitely64 w64 a x then
        let s := a + b
        if s == 0 then x else .binOp .add x (.constU64 s)
      else .binOp .add l r
    | .binOp .sub x (.constU64 a), .constU64 b =>
      if subexprDefinitely64 w64 a x then
        if a == b then x
        else if b > a then .binOp .add x (.constU64 (b - a))
        else .binOp .sub x (.constU64 (a - b))
      else .binOp .add l r
    | _, _ => .binOp .add l r
  | .sub =>
    match l, r with
    | .constU64 a, .constU64 b => .constU64 (a - b)
    | .constU256 a, .constU256 b => .constU256 (UInt256.sub a b)
    | x, .constU256 w =>
      if w == UInt256.zero then x else .binOp .sub l r
    | x, .constU64 0 => x
    | .binOp .add x (.constU64 a), .constU64 b =>
      if subexprDefinitely64 w64 a x then
        if a == b then x
        else if a > b then .binOp .add x (.constU64 (a - b))
        else .binOp .sub x (.constU64 (b - a))
      else .binOp .sub l r
    | .binOp .sub x (.constU64 a), .constU64 b =>
      if subexprDefinitely64 w64 a x then
        let s := a + b
        if s == 0 then x else .binOp .sub x (.constU64 s)
      else .binOp .sub l r
    | x, y =>
      if (w64 || exprDefinitely64 x) && x == y then .constU64 0
      else match x with
        | .constU256 _ => if x == y then .constU256 UInt256.zero else .binOp .sub x y
        | _ => .binOp .sub x y
  | .mul =>
    match l, r with
    | .constU64 a, .constU64 b => .constU64 (a * b)
    | .constU256 a, .constU256 b => .constU256 (UInt256.mul a b)
    | x, .constU256 w | .constU256 w, x =>
      if w == UInt256.zero then .constU256 UInt256.zero
      else if w == UInt256.ofUInt64 1 then x
      else .binOp .mul l r
    | x, .constU64 1 | .constU64 1, x => x
    | x, .constU64 0 =>
      if w64 || exprDefinitely64 x then .constU64 0 else .binOp .mul x (.constU64 0)
    | .constU64 0, x =>
      if w64 || exprDefinitely64 x then .constU64 0 else .binOp .mul (.constU64 0) x
    | x, .constU64 c =>
      if w64 || exprDefinitely64 x then
        match pow2ShiftLog2 c with
        | some k => .binOp .shl x (.constU64 k)
        | none => .binOp .mul x (.constU64 c)
      else .binOp .mul x (.constU64 c)
    | .constU64 c, x =>
      if w64 || exprDefinitely64 x then
        match pow2ShiftLog2 c with
        | some k => .binOp .shl x (.constU64 k)
        | none => .binOp .mul (.constU64 c) x
      else .binOp .mul (.constU64 c) x
    | _, _ => .binOp .mul l r
  | .div =>
    match l, r with
    | .constU64 a, .constU64 b => .constU64 (a / b)
    | x, .constU256 w =>
      if w == UInt256.ofUInt64 1 then x else .binOp .div l r
    | x, .constU64 0 =>
      if w64 || exprDefinitely64 x then .constU64 0 else .binOp .div x (.constU64 0)
    | x, .constU64 1 => x
    | x, .constU64 c =>
      if w64 || exprDefinitely64 x then
        match pow2ShiftLog2 c with
        | some k => .binOp .shr x (.constU64 k)
        | none => .binOp .div x (.constU64 c)
      else .binOp .div x (.constU64 c)
    | _, _ => .binOp .div l r
  | .mod =>
    match l, r with
    | .constU64 a, .constU64 b => .constU64 (a % b)
    | x, .constU64 0 =>
      if w64 || exprDefinitely64 x then x else .binOp .mod x (.constU64 0)
    | x, .constU64 1 =>
      if w64 || exprDefinitely64 x then .constU64 0 else .binOp .mod x (.constU64 1)
    | x, .constU64 c =>
      if w64 || exprDefinitely64 x then
        match pow2ShiftLog2 c with
        | some _ => .binOp .bitAnd x (.constU64 (c - 1))
        | none => .binOp .mod x (.constU64 c)
      else .binOp .mod x (.constU64 c)
    | _, _ => .binOp .mod l r
  | .bitAnd =>
    match l, r with
    | .constU64 a, .constU64 b => .constU64 (a &&& b)
    | .constU256 a, .constU256 b => .constU256 (UInt256.bitAnd a b)
    | _, .constU256 w | .constU256 w, _ =>
      if w == UInt256.zero then .constU256 UInt256.zero else .binOp .bitAnd l r
    | x, .constU64 0 =>
      if w64 || exprDefinitely64 x then .constU64 0 else .binOp .bitAnd x (.constU64 0)
    | .constU64 0, x =>
      if w64 || exprDefinitely64 x then .constU64 0 else .binOp .bitAnd (.constU64 0) x
    | x, y => if x == y then x else .binOp .bitAnd x y
  | .bitOr =>
    match l, r with
    | .constU64 a, .constU64 b => .constU64 (a ||| b)
    | .constU256 a, .constU256 b => .constU256 (UInt256.bitOr a b)
    | x, .constU256 w | .constU256 w, x =>
      if w == UInt256.zero then x else .binOp .bitOr l r
    | x, .constU64 0 | .constU64 0, x => x
    | x, y => if x == y then x else .binOp .bitOr x y
  | .bitXor =>
    match l, r with
    | .constU64 a, .constU64 b => .constU64 (a ^^^ b)
    | .constU256 a, .constU256 b => .constU256 (UInt256.bitXor a b)
    | x, .constU256 w | .constU256 w, x =>
      if w == UInt256.zero then x else .binOp .bitXor l r
    | x, .constU64 0 | .constU64 0, x => x
    | x, y =>
      if (w64 || exprDefinitely64 x) && x == y then .constU64 0
      else match x with
        | .constU256 _ => if x == y then .constU256 UInt256.zero else .binOp .bitXor x y
        | _ => .binOp .bitXor x y
  | .shl =>
    match l, r with
    | .constU64 a, .constU64 b => .constU64 (a <<< (b &&& 63))
    | .constU256 a, .constU256 b => .constU256 (UInt256.shl a b.toNat)
    | x, .constU256 w =>
      if w == UInt256.zero then x else .binOp .shl l r
    | x, .constU64 0 => x
    | _, _ => .binOp .shl l r
  | .shr =>
    match l, r with
    | .constU64 a, .constU64 b => .constU64 (a >>> (b &&& 63))
    | .constU256 a, .constU256 b => .constU256 (UInt256.shr a b.toNat)
    | x, .constU256 w =>
      if w == UInt256.zero then x else .binOp .shr l r
    | x, .constU64 0 => x
    | _, _ => .binOp .shr l r
  | .sar =>
    match l, r with
    | .constU256 a, .constU256 b => .constU256 (UInt256.sar a b.toNat)
    | x, .constU256 w =>
      if w == UInt256.zero then x else .binOp .sar l r
    | _, _ => .binOp .sar l r
  | .clmul64 =>
    match l, r with
    | .constU64 a, .constU64 b => .constU64 (clmul64 a b)
    | _, _ => .binOp .clmul64 l r
  | .clmul64Hi =>
    match l, r with
    | .constU64 a, .constU64 b => .constU64 (clmul64Hi a b)
    | _, _ => .binOp .clmul64Hi l r
  | .gf2Affine =>
    match l, r with
    | .constU64 a, .constU64 b => .constU64 (gf2Affine a b)
    | _, _ => .binOp .gf2Affine l r
  | .eor3 =>
    match l, r with
    | .constU64 a, .constU64 b => .constU64 (eor3 a b)
    | _, _ => .binOp .eor3 l r
  | .eq =>
    match l, r with
    | .constU64 a, .constU64 b => .constBool (a == b)
    | .constBool a, .constBool b => .constBool (a == b)
    | .constU256 a, .constU256 b => .constBool (a == b)
    | x, .constBool true | .constBool true, x =>
      if atomDefinitelyBool x then x else .binOp .eq l r
    | .unaryOp .not x, .constBool false | .constBool false, .unaryOp .not x =>
      if atomDefinitelyBool x then x else .binOp .eq l r
    | x, .constBool false | .constBool false, x =>
      if atomDefinitelyBool x then .unaryOp .not x else .binOp .eq l r
    | x, y =>
      if x == y && (w64 || exprDefinitely64 x || atomDefinitelyBool x ||
          (match x with | .constU256 _ => true | _ => false)) then .constBool true
      else .binOp .eq x y
  | .lt =>
    match l, r with
    | .constU64 a, .constU64 b => .constBool (decide (a < b))
    | .constU256 a, .constU256 b => .constBool (UInt256.lt a b)
    | x, y =>
      if x == y && (w64 || exprDefinitely64 x ||
          (match x with | .constU256 _ => true | _ => false)) then .constBool false
      else .binOp .lt x y
  | .le =>
    match l, r with
    | .constU64 a, .constU64 b => .constBool (decide (a ≤ b))
    | .constU256 a, .constU256 b => .constBool (UInt256.le a b)
    | x, y =>
      if x == y && (w64 || exprDefinitely64 x ||
          (match x with | .constU256 _ => true | _ => false)) then .constBool true
      else .binOp .le x y
  | .addChecked256 | .subChecked256 | .mulChecked256 => .binOp op l r

/-- Single-step algebraic & strength-reduction normalizer on `SymExpr`. -/
def normSymBinOpStep (op : BinOp) (lhs rhs : SymExpr) (width64Safe : Bool := false) : SymExpr :=
  let (l, r) :=
    if SymExpr.isCommutative op && SymExpr.rank lhs > SymExpr.rank rhs then
      (rhs, lhs)
    else
      (lhs, rhs)
  let w64 := width64Safe || (exprDefinitely64 l && exprDefinitely64 r)
  normSymBinOpCore op l r w64

/-- Single-step unary normalizer on `SymExpr`. -/
def normSymUnaryOpStep (op : UnaryOp) (arg : SymExpr) : SymExpr :=
  match op, arg with
  | .not, .constBool b => .constBool (!b)
  | .not, .constU64 a => .constU64 (~~~a)
  | .not, .constU256 w => .constU256 (UInt256.bitNot w)
  | .not, .unaryOp .not x =>
    if exprDefinitely64 x || atomDefinitelyBool x ||
       (match x with | .constU256 _ => true | _ => false) then x
    else .unaryOp .not (.unaryOp .not x)
  | .neg, .constU64 a => .constU64 (0 - a)
  | .neg, .constU256 w => .constU256 (UInt256.sub UInt256.zero w)
  | .neg, .unaryOp .neg x =>
    if exprDefinitely64 x then x
    else .unaryOp .neg (.unaryOp .neg x)
  | .clz256, .constU64 a => .constU256 (UInt256.clz (UInt256.ofUInt64 a))
  | .clz256, .constU256 w => .constU256 (UInt256.clz w)
  | _, _ => .unaryOp op arg

def flattenConjAtoms : SymExpr → List SymExpr
  | .ite c t (.constBool false) => flattenConjAtoms c ++ flattenConjAtoms t
  | e => [e]

def insertSortedConjAtom (x : SymExpr) : List SymExpr → List SymExpr
  | [] => [x]
  | y :: ys =>
    if x == y then y :: ys
    else if SymExpr.rank x < SymExpr.rank y || (SymExpr.rank x == SymExpr.rank y && reprStr x ≤ reprStr y) then
      x :: y :: ys
    else y :: insertSortedConjAtom x ys

def foldSortedConj : List SymExpr → SymExpr
  | [] => .constBool true
  | [x] => x
  | x :: xs => .ite x (foldSortedConj xs) (.constBool false)

/-- Single-step `ite` normalizer on `SymExpr`. -/
def normSymIteStep (cond thenVal elseVal : SymExpr) : SymExpr :=
  match cond with
  | .constBool true => thenVal
  | .constBool false => elseVal
  | .constU64 c => if c != 0 then thenVal else elseVal
  | .constU256 w => if w != UInt256.zero then thenVal else elseVal
  | _ =>
    if thenVal == elseVal && atomDefinitelyBool cond then thenVal
    else if elseVal == .constBool false && atomDefinitelyBool cond && atomDefinitelyBool thenVal then
      let atoms := (flattenConjAtoms cond ++ flattenConjAtoms thenVal).filter (· != .constBool true)
      if atoms.contains (.constBool false) then .constBool false
      else foldSortedConj (atoms.foldr insertSortedConjAtom [])
    else .ite cond thenVal elseVal

mutual
  /-- Canonical bottom-up algebraic normalizer on `SymExpr`. -/
  def normSymExpr : SymExpr → SymExpr
    | .constU64 v => .constU64 v
    | .constU256 w => .constU256 w
    | .constBool b => .constBool b
    | .symVar id => .symVar id
    | .allocTag id => .allocTag id
    | .rcSym ep id => .rcSym ep id
    | .ctorTag ep id => .ctorTag ep id
    | .ctorLen sc ep id => .ctorLen sc ep id
    | .sarrayLen id => .sarrayLen id
    | .mulDiv256 isUp a b d => .mulDiv256 isUp (normSymExpr a) (normSymExpr b) (normSymExpr d)
    | .binOp op l r => normSymBinOpStep op (normSymExpr l) (normSymExpr r)
    | .unaryOp op a => normSymUnaryOpStep op (normSymExpr a)
    | .ite c t e => normSymIteStep (normSymExpr c) (normSymExpr t) (normSymExpr e)
    | .tuple fs => .tuple (normSymExprList fs)
    | .bufElem sp b idx => .bufElem sp b (normSymExpr idx)
    | .unit => .unit

  def normSymExprList : List SymExpr → List SymExpr
    | [] => []
    | e :: es => normSymExpr e :: normSymExprList es
end


end LeanNative.Proofs
