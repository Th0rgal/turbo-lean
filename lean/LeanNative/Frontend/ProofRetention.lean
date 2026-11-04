import Lean.Compiler.LCNF.Basic
import LeanNative.IR.AST
import LeanNative.Transform.Pass
import LeanNative.Backend.LLVMAst.Syntax
import LeanNative.Backend.LLVMAst.Eval
import LeanNative.Backend.PTXAst.Syntax
import LeanNative.Backend.MetalAst.Syntax

/-!
# D1 proof-carrying LCNF (`LeanNative.Frontend.ProofRetention`)

Facts retained from pre-erasure `Lean.Compiler.LCNF.Code .pure` before `.mono` proof erasure,
and the verified specializations they justify on `LNIRCode`, `LLVMAst`, `PTXAst`, and `MetalAst`.
-/

namespace LeanNative.Frontend.ProofRetention

open LeanNative.IR
open LeanNative.Backend.TargetIR
open LeanNative.Backend.LLVMAst
open LeanNative.Backend.PTXAst
open LeanNative.Backend.MetalAst

export LeanNative.IR (RetainedFact FactEnv factMember consFact)

set_option autoImplicit false

/-- Mapping from LCNF `FVarId`s to LNIR `VarId`s threaded during pure-phase fact extraction. -/
structure RetentionState where
  fvarMap : List (Lean.FVarId × VarId) := []
  nextVar : VarId := 0
  facts : FactEnv := []
  branchFacts : FactEnv := []
  deriving Inhabited

def internFVar (st : RetentionState) (fv : Lean.FVarId) : VarId × RetentionState :=
  match st.fvarMap.find? (fun p => p.1 == fv) with
  | some (_, vid) => (vid, st)
  | none =>
    let vid := st.nextVar
    (vid, { st with fvarMap := (fv, vid) :: st.fvarMap, nextVar := vid + 1 })

def internParams (st : RetentionState)
    (ps : List (Lean.Compiler.LCNF.Param .pure)) : RetentionState :=
  match ps with
  | [] => st
  | p :: rest =>
    let (_, st1) := internFVar st p.fvarId
    internParams st1 rest

def pushFactOpt (st : RetentionState) (opt : Option RetainedFact) : RetentionState :=
  match opt with
  | some f => { st with facts := consFact st.facts f }
  | none => st

def pushBranchFact (st : RetentionState) (opt : Option RetainedFact) : RetentionState :=
  match opt with
  | some f => { st with branchFacts := consFact st.branchFacts f }
  | none => st

/-- Byte ranges `[a, a+lenA)` and `[b, b+lenB)` are in range and disjoint. -/
def SlicesDisjoint (a lenA b lenB : Nat) : Prop :=
  a + lenA ≤ 2 ^ 64 ∧ b + lenB ≤ 2 ^ 64 ∧ (a + lenA ≤ b ∨ b + lenB ≤ a)

abbrev slicesDisjoint := SlicesDisjoint

def fvarsOfArgs (args : List (Lean.Compiler.LCNF.Arg .pure)) : List Lean.FVarId :=
  match args with
  | [] => []
  | .fvar x :: rest => x :: fvarsOfArgs rest
  | .erased :: rest => fvarsOfArgs rest
  | .type _ _ :: rest => fvarsOfArgs rest

def internFVarList (st : RetentionState) (fvs : List Lean.FVarId) :
    List VarId × RetentionState :=
  match fvs with
  | [] => ([], st)
  | fv :: rest =>
    let (v, st1) := internFVar st fv
    let (vs, st2) := internFVarList st1 rest
    (v :: vs, st2)

def litNat? (e : Lean.Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ => none

/-- Peel `Fin.val` / `UInt64.toNat` / `USize.toNat` with explicit structural fuel. -/
def unwrapOperandAux (fuel : Nat) (e : Lean.Expr) : Lean.Expr :=
  match fuel with
  | 0 => e
  | fuel + 1 =>
    match e.getAppFnArgs with
    | (``Fin.val, #[_, x]) => unwrapOperandAux fuel x
    | (``UInt64.toNat, #[x]) => unwrapOperandAux fuel x
    | (``USize.toNat, #[x]) => unwrapOperandAux fuel x
    | _ => e

def unwrapOperand (e : Lean.Expr) : Lean.Expr :=
  unwrapOperandAux 8 e

/-- `true` exactly when the expression is `Sort 0` (`Prop`), never via `Expr.isProp`. -/
def isSortZero (e : Lean.Expr) : Bool :=
  e == .sort .zero

/-- A retained fact is a comparison, divisibility, equality, or conjunction, never `Sort 0`. -/
def isRetainedPropHead (n : Lean.Name) : Bool :=
  n == ``LT.lt || n == ``Nat.lt || n == ``UInt64.lt ||
  n == ``LE.le || n == ``Nat.le || n == ``UInt64.le ||
  n == ``Dvd.dvd || n == ``Eq ||
  n == ``And || n == ``SlicesDisjoint

def isPropType (ty : Lean.Expr) : Bool :=
  isRetainedPropHead (ty.getAppFnArgs).1

/-- A fvar operand, or a literal `Nat` interned as a fresh variable. -/
def operandVar? (st : RetentionState) (e : Lean.Expr) : Option (VarId × RetentionState) :=
  match unwrapOperand e with
  | .fvar fv => some (internFVar st fv)
  | .lit (.natVal n) => some (internFVar st { name := .num `lit n })
  | _ => none

def twoOperands (st : RetentionState) (a b : Lean.Expr) :
    Option (VarId × VarId × RetentionState) :=
  match operandVar? st a with
  | none => none
  | some (va, st1) =>
    match operandVar? st1 b with
    | none => none
    | some (vb, st2) => some (va, vb, st2)

/-- `a + b` or `a * b` as a pair of operands, unwrapping `Fin.val` / `UInt64.toNat`. -/
def binApp? (e : Lean.Expr) (add : Bool) : Option (Lean.Expr × Lean.Expr) :=
  match (unwrapOperand e).getAppFnArgs with
  | (n, args) =>
    if add then
      if (n == ``HAdd.hAdd || n == ``Nat.add) && args.size >= 2 then
        some (args[args.size - 2]!, args[args.size - 1]!)
      else none
    else if (n == ``HMul.hMul || n == ``Nat.mul) && args.size >= 2 then
      some (args[args.size - 2]!, args[args.size - 1]!)
    else none

/-- `n` is `2^63` or `2^64`. -/
def isWidthBound (n : Nat) : Bool :=
  n == 2 ^ 63 || n == 2 ^ 64

/-- `(a + b < 2^63 | 2^64)` or `(a * b < 2^63 | 2^64)`. -/
def overflowFact? (st : RetentionState) (lhs bound : Lean.Expr) : Option (RetainedFact × RetentionState) :=
  match litNat? (unwrapOperand bound) with
  | none => none
  | some n =>
    if !isWidthBound n then none
    else
      match binApp? lhs true with
      | some (a, b) =>
        match twoOperands st a b with
        | some (va, vb, st2) => some (.noOverflowAdd va vb true true, st2)
        | none => none
      | none =>
        match binApp? lhs false with
        | some (a, b) =>
          match twoOperands st a b with
          | some (va, vb, st2) => some (.noOverflowMul va vb true true, st2)
          | none => none
        | none => none

/-- `b ≤ a` as a no-underflow subtraction fact. -/
def subFact? (st : RetentionState) (b a : Lean.Expr) : Option (RetainedFact × RetentionState) :=
  match twoOperands st b a with
  | some (vb, va, st2) => some (.noOverflowSub va vb false true, st2)
  | none => none

/-- Power-of-two alignment carried by a modulus or a `Dvd` divisor. -/
def alignBytesOf (e : Lean.Expr) : Nat :=
  match litNat? (unwrapOperand e) with
  | some n => if isPow2 n then n else 0
  | none => 0

/-- `align ∣ p` or `p % align = 0` with `align` a power of two. -/
def alignedFact? (st : RetentionState) (ptr align : Lean.Expr) : Option (RetainedFact × RetentionState) :=
  let al := alignBytesOf align
  if al == 0 then none
  else
    match operandVar? st ptr with
    | some (vp, st2) => some (.alignedPtr vp al, st2)
    | none => none

/-- `p + len ≤ 2^64` as a pointer and a length. -/
def sliceEnd? (st : RetentionState) (e : Lean.Expr) : Option (VarId × VarId × RetentionState) :=
  match (unwrapOperand e).getAppFnArgs with
  | (n, args) =>
    if (n == ``LE.le || n == ``Nat.le) && args.size >= 2 then
      match litNat? (unwrapOperand (args[args.size - 1]!)) with
      | some m =>
        if m != 2 ^ 64 then none
        else
          match binApp? (args[args.size - 2]!) true with
          | some (p, len) =>
            match twoOperands st p len with
            | some (vp, vl, st2) => some (vp, vl, st2)
            | none => none
          | none => none
      | none => none
    else none

/-- `a + lenA ≤ b` or `b + lenB ≤ a` as the two pointers and their lengths. -/
def sliceOrder? (st : RetentionState) (e : Lean.Expr) :
    Option (VarId × VarId × VarId × VarId × RetentionState) :=
  match (unwrapOperand e).getAppFnArgs with
  | (n, args) =>
    if (n == ``LE.le || n == ``Nat.le) && args.size >= 2 then
      match binApp? (args[args.size - 2]!) true with
      | some (p, len) =>
        match twoOperands st p len with
        | some (vp, vl, st1) =>
          match operandVar? st1 (args[args.size - 1]!) with
          | some (vq, st2) => some (vp, vl, vq, 0, st2)
          | none => none
        | none => none
      | none => none
    else none

/-- `` `SlicesDisjoint `` is `a+lenA ≤ 2^64 ∧ b+lenB ≤ 2^64 ∧ (a+lenA ≤ b ∨ b+lenB ≤ a)`. -/
def disjointFact? (st : RetentionState) (e : Lean.Expr) : Option (RetainedFact × RetentionState) :=
  match (unwrapOperand e).getAppFnArgs with
  | (``SlicesDisjoint, #[pa, la, pb, lb]) =>
    match twoOperands st pa pb with
    | none => none
    | some (va, vb, st1) =>
      match twoOperands st1 la lb with
      | some (vla, vlb, st2) => some (.disjointSlices va vb vla vlb, st2)
      | none => none
  | (``And, #[endA, rest]) =>
    match (unwrapOperand rest).getAppFnArgs with
    | (``And, #[endB, disj]) =>
      match (unwrapOperand disj).getAppFnArgs with
      | (``Or, #[ab, ba]) =>
        match sliceEnd? st endA with
        | none => none
        | some (pa, la, st1) =>
          match sliceEnd? st1 endB with
          | none => none
          | some (pb, lb, st2) =>
            match sliceOrder? st2 ab with
            | some (pa', la', pb', _, st3) =>
              if pa' == pa && la' == la && pb' == pb then
                match sliceOrder? st3 ba with
                | some (pb'', lb', pa'', _, st4) =>
                  if pb'' == pb && lb' == lb && pa'' == pa then
                    some (.disjointSlices pa pb la lb, st4)
                  else none
                | none => none
              else none
            | none => none
      | _ => none
    | _ => none
  | _ => none

/-- A fact justified by a `Prop` type, matched on the kernel constant's exact `Name`. -/
def factOfType (st : RetentionState) (ty : Lean.Expr) : Option (RetainedFact × RetentionState) :=
  if !isPropType ty then none
  else
    match ty.getAppFnArgs with
    | (n, args) =>
      if (n == ``LT.lt || n == ``Nat.lt || n == ``UInt64.lt) && args.size >= 2 then
        let lhs := args[args.size - 2]!
        let rhs := args[args.size - 1]!
        match overflowFact? st lhs rhs with
        | some r => some r
        | none =>
          match twoOperands st lhs rhs with
          | some (a, b, st2) => some (.idxLt a b, st2)
          | none => none
      else if (n == ``LE.le || n == ``Nat.le || n == ``UInt64.le) && args.size >= 2 then
        subFact? st (args[args.size - 2]!) (args[args.size - 1]!)
      else if n == ``Dvd.dvd && args.size >= 2 then
        alignedFact? st (args[args.size - 1]!) (args[args.size - 2]!)
      else if n == ``Eq && args.size >= 3 then
        let (m, margs) := (unwrapOperand (args[args.size - 2]!)).getAppFnArgs
        if (m == ``HMod.hMod || m == ``Nat.mod) && margs.size >= 2 then
          let ptr := margs[margs.size - 2]!
          let al := margs[margs.size - 1]!
          match litNat? (unwrapOperand (args[args.size - 1]!)) with
          | some 0 => alignedFact? st ptr al
          | _ => none
        else none
      else if n == ``And || n == ``SlicesDisjoint then disjointFact? st ty
      else none

def extractParamFacts (st : RetentionState)
    (ps : List (Lean.Compiler.LCNF.Param .pure)) : RetentionState :=
  match ps with
  | [] => st
  | p :: rest =>
    let st1 :=
      match factOfType st p.type with
      | some (f, s) => pushFactOpt s (some f)
      | none => st
    extractParamFacts st1 rest

def extractLetFact (st : RetentionState) (ty : Lean.Expr)
    (lv : Lean.Compiler.LCNF.LetValue .pure) (dst : VarId) : RetentionState :=
  let _ := dst
  match lv with
  | .const .. | .proj .. | .fvar .. =>
    match factOfType st ty with
    | some (f, st1) => pushFactOpt st1 (some f)
    | none => st
  | _ => st

/-- A recognized `Bool`-producing test: `Nat.blt`, `UInt64.decLt`, `lean_is_exclusive`,
or `Decidable.decide` whose proposition is a retained fact. -/
def testOfLet (st : RetentionState) (lv : Lean.Compiler.LCNF.LetValue .pure) :
    Option (Option RetainedFact × RetentionState) :=
  match lv with
  | .const fnName _ args _ =>
    if fnName == ``Nat.blt || fnName == ``UInt64.decLt then
      let (vids, st1) := internFVarList st (fvarsOfArgs args.toList)
      match vids with
      | a :: b :: _ => some (some (.idxLt a b), st1)
      | _ => some (none, st1)
    else if fnName == `lean_is_exclusive then
      let (vids, st1) := internFVarList st (fvarsOfArgs args.toList)
      match vids with
      | a :: _ => some (some (.exclusiveObj a), st1)
      | _ => some (none, st1)
    else if fnName == ``Decidable.decide then
      match args.toList with
      | .type prop _ :: _ =>
        match factOfType st prop with
        | some (f, st1) => some (some f, st1)
        | none => some (none, st)
      | _ => none
    else none
  | _ => none

def altIsTrue (alt : Lean.Compiler.LCNF.Alt .pure) : Bool :=
  match alt with
  | .alt ctor _ _ _ => ctor == ``Bool.true
  | _ => false

def altIsUnreach (alt : Lean.Compiler.LCNF.Alt .pure) : Bool :=
  match alt.getCode with
  | .unreach _ => true
  | _ => false

def onlyTrueReachable (alts : List (Lean.Compiler.LCNF.Alt .pure)) : Bool :=
  alts.any altIsTrue && alts.all fun a => altIsTrue a || altIsUnreach a

/-- Facts contributed by the `true` arm of a recognized test. -/
def trueArmFact (fact : Option RetainedFact) (alt : Lean.Compiler.LCNF.Alt .pure) :
    Option RetainedFact :=
  if altIsTrue alt then fact else none

def collectPureStep (fuel : Nat) (st : RetentionState)
    (work : Lean.Compiler.LCNF.Code .pure ⊕ List (Lean.Compiler.LCNF.Alt .pure)) :
    RetentionState :=
  match fuel with
  | 0 => st
  | fuel + 1 =>
    match work with
    | .inl (.let decl k) =>
      let (dst, st1) := internFVar st decl.fvarId
      let st2 := extractLetFact st1 decl.type decl.value dst
      collectPureStep fuel st2 (.inl k)
    | .inl (.fun decl k _) =>
      let st1 := internParams st decl.params.toList
      let _ := collectPureStep fuel st1 (.inl decl.value)
      collectPureStep fuel st (.inl k)
    | .inl (.jp decl k) =>
      let st1 := internParams st decl.params.toList
      let _ := collectPureStep fuel st1 (.inl decl.value)
      collectPureStep fuel st (.inl k)
    | .inl (.cases c) =>
      let (_, st1) := internFVar st c.discr
      collectPureStep fuel st1 (.inr c.alts.toList)
    | .inl (.return fv) => (internFVar st fv).2
    | .inl (.jmp fv args) =>
      let (_, st1) := internFVar st fv
      (internFVarList st1 (fvarsOfArgs args.toList)).2
    | .inl (.unreach _) => st
    | .inr [] => st
    | .inr (alt :: rest) =>
      let st1 := internParams st alt.getParams.toList
      let st2 := collectPureStep fuel st1 (.inl alt.getCode)
      collectPureStep fuel st2 (.inr rest)

/-- Like `collectPureStep`, but a `Bool` cases on a recognized test records the `true`
arm. The fact is global only when every other arm is `.unreach`; otherwise it stays
in `branchFacts` and does not leak into the continuation. -/
def collectBranchStep (fuel : Nat) (st : RetentionState)
    (known : List (Lean.FVarId × Option RetainedFact))
    (work : Lean.Compiler.LCNF.Code .pure ⊕ List (Lean.Compiler.LCNF.Alt .pure)) :
    RetentionState :=
  match fuel with
  | 0 => st
  | fuel + 1 =>
    match work with
    | .inl (.let decl k) =>
      let (dst, st1) := internFVar st decl.fvarId
      let st2 := extractLetFact st1 decl.type decl.value dst
      let known' :=
        match testOfLet st2 decl.value with
        | some (fact, st3) => ((decl.fvarId, fact) :: known, st3)
        | none => (known, st2)
      collectBranchStep fuel known'.2 known'.1 (.inl k)
    | .inl (.fun decl k _) =>
      let st1 := internParams st decl.params.toList
      let stSub := collectBranchStep fuel st1 known (.inl decl.value)
      collectBranchStep fuel { st with branchFacts := stSub.branchFacts } known (.inl k)
    | .inl (.jp decl k) =>
      let st1 := internParams st decl.params.toList
      let stSub := collectBranchStep fuel st1 known (.inl decl.value)
      collectBranchStep fuel { st with branchFacts := stSub.branchFacts } known (.inl k)
    | .inl (.cases c) =>
      let (_, st1) := internFVar st c.discr
      let extra :=
        match known.find? (fun e => e.1 == c.discr) with
        | some (_, fact) => c.alts.toList.filterMap (trueArmFact fact)
        | none => []
      let reachable := c.alts.toList.filter fun a => !altIsUnreach a
      let promote := reachable.length <= 1
      let st2 := extra.foldl (fun acc f =>
        if promote then pushFactOpt acc (some f) else pushBranchFact acc (some f)) st1
      if promote then
        collectBranchStep fuel st2 known (.inr c.alts.toList)
      else
        let stArms := collectBranchStep fuel { st2 with facts := [] } known (.inr c.alts.toList)
        { st2 with branchFacts := stArms.facts ++ stArms.branchFacts }
    | .inl (.return fv) => (internFVar st fv).2
    | .inl (.jmp fv args) =>
      let (_, st1) := internFVar st fv
      (internFVarList st1 (fvarsOfArgs args.toList)).2
    | .inl (.unreach _) => st
    | .inr [] => st
    | .inr (alt :: rest) =>
      let st1 := internParams st alt.getParams.toList
      let st2 := collectBranchStep fuel st1 known (.inl alt.getCode)
      collectBranchStep fuel st2 known (.inr rest)

def retainedPureFactsWithParams (fuel : Nat)
    (params : List (Lean.Compiler.LCNF.Param .pure))
    (code : Lean.Compiler.LCNF.Code .pure) : FactEnv :=
  let st0 := internParams {} params
  let st1 := extractParamFacts st0 params
  (collectBranchStep fuel st1 [] (.inl code)).facts

def retainedPureDeclFacts (fuel : Nat) (decl : Lean.Compiler.LCNF.Decl .pure) : FactEnv :=
  match decl.value with
  | .code c => retainedPureFactsWithParams fuel decl.params.toList c
  | .extern _ =>
    let st0 := internParams {} decl.params.toList
    (extractParamFacts st0 decl.params.toList).facts

def retainedPureFacts (fuel : Nat) (code : Lean.Compiler.LCNF.Code .pure) : FactEnv :=
  (collectBranchStep fuel {} [] (.inl code)).facts

/-- Facts recorded only inside a reachable branch, never promoted to the continuation. -/
def retainedBranchFacts (fuel : Nat) (code : Lean.Compiler.LCNF.Code .pure) : FactEnv :=
  (collectBranchStep fuel {} [] (.inl code)).branchFacts

/-- Variables an expression reads. Used to drop facts whose subject is redefined. -/
def exprVars (e : LNIRExpr) : List VarId :=
  match e with
  | .scalar s => scalarVars s
  | .constU256 _ => []
  | .mulDivDown a b d | .mulDivUp a b d => [a, b, d]
  | .storageLoad m s => [m, s]
  | .storageStore m s v => [m, s, v]
  | .mkTuple fs => fs
  | .projTuple t _ => [t]
  | .allocCtor _ os ss => os ++ ss
  | .ctorGetObj c _ | .ctorGetScalar c _ _ | .isExclusive c | .sarrayLen c => [c]
  | .sarrayDataPtr a _ | .sarrayEnsureExclusive a _ => [a]
  | .sarrayGet a i _ | .rawLoad a i _ => [a, i]
  | .sarraySet a i v _ => [a, i, v]
  | .boxScalar v _ | .unboxScalar v _ => [v]
  | .call _ args _ _ => args
where
  scalarVars : ScalarExpr → List VarId
    | .constU64 _ | .constBool _ => []
    | .var v => [v]
    | .binOp _ l r => scalarVars l ++ scalarVars r
    | .unaryOp _ a => scalarVars a
    | .select c t e => scalarVars c ++ scalarVars t ++ scalarVars e
    | .fma a b c => scalarVars a ++ scalarVars b ++ scalarVars c

/-- `true` when evaluating `e` cannot change the heap. Pure runtime calls
(`box` / `unbox` / `sarray_len` / `ctor_tag`) are included; mutating calls are not. -/
def exprPreservesHeap (e : LNIRExpr) : Bool :=
  match e with
  | .scalar _ | .constU256 _ | .mulDivDown _ _ _ | .mulDivUp _ _ _ | .storageLoad _ _
  | .mkTuple _ | .projTuple _ _ | .ctorGetObj _ _ | .ctorGetScalar _ _ _
  | .isExclusive _ | .sarrayLen _ | .sarrayGet _ _ _ | .sarrayDataPtr _ _
  | .rawLoad _ _ _ | .boxScalar _ _ | .unboxScalar _ _ => true
  | .call fn _ _ _ =>
    fn == "lean_native_box_u64" || fn == "lean_native_unbox_u64" ||
    fn == "lean_native_sarray_len" || fn == "lean_native_ctor_tag"
  | .storageStore _ _ _ | .allocCtor _ _ _ | .sarrayEnsureExclusive _ _
  | .sarraySet _ _ _ _ => false

/-- `true` when `e` neither redefines `v` nor mutates the heap. -/
def exprKeeps (v : VarId) (e : LNIRExpr) : Bool :=
  exprPreservesHeap e && !(exprVars e).contains v

def exprPreservesExcl (facts : FactEnv) (e : LNIRExpr) : Bool :=
  match e with
  | .sarrayEnsureExclusive objVar _ => factMember facts (.exclusiveObj objVar)
  | _ => exprPreservesHeap e

/-- `true` when `f` mentions variable `v`. -/
def factMentions (v : VarId) (f : RetainedFact) : Bool :=
  match f with
  | .idxLt i n => i == v || n == v
  | .noOverflowAdd a b _ _ | .noOverflowSub a b _ _ | .noOverflowMul a b _ _ => a == v || b == v
  | .alignedPtr p _ => p == v
  | .disjointSlices a b la lb => a == v || b == v || la == v || lb == v
  | .exclusiveObj o => o == v

/-- Drop every fact that mentions `v` (SSA redefinition of `v`). -/
def killVarFacts (v : VarId) (facts : FactEnv) : FactEnv :=
  facts.filter fun f => !factMentions v f

/-- Drop every heap-object fact. Heap-mutating ops and loop bodies invalidate them. -/
def clearHeapFacts (facts : FactEnv) : FactEnv :=
  facts.filter fun f =>
    match f with
    | .exclusiveObj _ => false
    | _ => true

def specializeExclExpr (facts : FactEnv) (val : LNIRExpr) : LNIRExpr :=
  match val with
  | .isExclusive objVar =>
    if factMember facts (.exclusiveObj objVar) then .scalar (.constBool true) else val
  | .sarrayEnsureExclusive objVar _ =>
    if factMember facts (.exclusiveObj objVar) then .scalar (.var objVar) else val
  | _ => val

/-- Facts learned from binding the result of `val`. An allocating constructor and a
successful `sarrayEnsureExclusive` both yield a fresh exclusive object. -/
def introExprFact (dst : VarId) (val : LNIRExpr) (facts : FactEnv) : FactEnv :=
  match val with
  | .sarrayEnsureExclusive _ _ => consFact facts (.exclusiveObj dst)
  | .allocCtor _ _ _ => consFact facts (.exclusiveObj dst)
  | _ => facts

/-- Replace a retained `lean_is_exclusive` test by `true` and elide redundant
`sarrayEnsureExclusive`, killing facts on shadowing or heap-mutating ops. -/
def dischargeRetainedExclusivity (facts : FactEnv) (code : LNIRCode) : LNIRCode :=
  match code with
  | .letBind dst ty val k =>
    let val' := specializeExclExpr facts val
    let kept :=
      if exprPreservesExcl facts val then killVarFacts dst facts
      else killVarFacts dst (clearHeapFacts facts)
    let facts' := introExprFact dst val kept
    .letBind dst ty val' (dischargeRetainedExclusivity facts' k)
  | .rawStore p i v ty k =>
    .rawStore p i v ty (dischargeRetainedExclusivity (clearHeapFacts facts) k)
  | .incRef v n k => .incRef v n (dischargeRetainedExclusivity (clearHeapFacts facts) k)
  | .decRef v n k => .decRef v n (dischargeRetainedExclusivity (clearHeapFacts facts) k)
  | .ite c t e =>
    .ite c (dischargeRetainedExclusivity facts t) (dischargeRetainedExclusivity facts e)
  | .seqFor idx lo hi acc init ty body k =>
    .seqFor idx lo hi acc init ty
      (dischargeRetainedExclusivity [] body)
      (dischargeRetainedExclusivity (killVarFacts acc (clearHeapFacts facts)) k)
  | .parFor out len ins ty ker k =>
    .parFor out len ins ty ker
      (dischargeRetainedExclusivity (killVarFacts out (clearHeapFacts facts)) k)
  | .ret v => .ret v
  | .unreachable => .unreachable

/-- Local discharge: no facts are assumed at entry, so every specialization it performs
was justified by a fact the pass itself introduced. -/
def dischargeLocalExclusivity (code : LNIRCode) : LNIRCode :=
  dischargeRetainedExclusivity [] code

def overflowFlagsOf (nsw nuw : Bool) : OverflowFlags :=
  if nsw && nuw then .nswNuw else if nsw then .nsw else if nuw then .nuw else .none

/-- Flags for an `add`/`mul` whose *register operands* are exactly `v{a}` and `v{b}`. -/
def overflowOf (facts : FactEnv) (isMul : Bool) (a b : VarId) : OverflowFlags :=
  match facts with
  | [] => .none
  | .noOverflowAdd l r nsw nuw :: rest =>
    if !isMul && l == a && r == b then overflowFlagsOf nsw nuw
    else overflowOf rest isMul a b
  | .noOverflowMul l r nsw nuw :: rest =>
    if isMul && l == a && r == b then overflowFlagsOf nsw nuw
    else overflowOf rest isMul a b
  | _ :: rest => overflowOf rest isMul a b

/-- Flags for a `sub` justified by a matching `noOverflowSub` fact. -/
def subFlagsOf (facts : FactEnv) (a b : VarId) : OverflowFlags :=
  match facts with
  | [] => .none
  | .noOverflowSub l r nsw nuw :: rest =>
    if l == a && r == b then overflowFlagsOf nsw nuw else subFlagsOf rest a b
  | _ :: rest => subFlagsOf rest a b

/-- SSA register name of LNIR variable `v` (`"v"` + its decimal digits). -/
def llvmRegOf (v : VarId) : String := "v" ++ ppInt v

/-- Merge a fact's flags into flags the instruction already carries. -/
def mergeFlags (old fresh : OverflowFlags) : OverflowFlags :=
  match old, fresh with
  | .none, f => f
  | f, .none => f
  | .nsw, .nuw | .nuw, .nsw | .nswNuw, _ | _, .nswNuw => .nswNuw
  | .nsw, .nsw => .nsw
  | .nuw, .nuw => .nuw

/-- Attach `nsw`/`nuw` to an `.i64` `add`/`sub`/`mul` only when both operands are the
registers named by the matching fact. -/
def attachOverflow (facts : FactEnv) (ins : LLVMInstr) : LLVMInstr :=
  match ins with
  | .add dst old .i64 (.reg x) (.reg y) =>
    match factOperands facts x y with
    | some (a, b) => .add dst (mergeFlags old (overflowOf facts false a b)) .i64 (.reg x) (.reg y)
    | none => ins
  | .sub dst old .i64 (.reg x) (.reg y) =>
    match factOperands facts x y with
    | some (a, b) => .sub dst (mergeFlags old (subFlagsOf facts a b)) .i64 (.reg x) (.reg y)
    | none => ins
  | .mul dst old .i64 (.reg x) (.reg y) =>
    match factOperands facts x y with
    | some (a, b) => .mul dst (mergeFlags old (overflowOf facts true a b)) .i64 (.reg x) (.reg y)
    | none => ins
  | _ => ins
where
  factOperands (facts : FactEnv) (x y : String) : Option (VarId × VarId) :=
    match facts with
    | [] => none
    | .noOverflowAdd a b _ _ :: rest | .noOverflowSub a b _ _ :: rest
    | .noOverflowMul a b _ _ :: rest =>
      if x == llvmRegOf a && y == llvmRegOf b then some (a, b)
      else factOperands rest x y
    | _ :: rest => factOperands rest x y

/-- The alignment a fact gives `ptrVar`, raised only when it strictly dominates `fallback`
and `fallback` divides it. -/
def alignOfFact (facts : FactEnv) (ptrVar : VarId) (ty : LLVMType) (fallback : Nat) : Nat :=
  match facts with
  | [] => fallback
  | .alignedPtr p n :: rest =>
    let eff := effectiveAlign ty fallback
    if p == ptrVar && isPow2 n && isPow2 eff && eff < n && n % eff == 0 then n
    else alignOfFact rest ptrVar ty fallback
  | _ :: rest => alignOfFact rest ptrVar ty fallback

/-- Raise a load/store alignment when its pointer operand is exactly `v{ptrVar}`. -/
def attachLoadStoreAlign (facts : FactEnv) (ptrVar : VarId) (ins : LLVMInstr) : LLVMInstr :=
  match ins with
  | .load dst vol ty (.reg r) al as_ =>
    if r == llvmRegOf ptrVar then .load dst vol ty (.reg r) (alignOfFact facts ptrVar ty al) as_
    else ins
  | .store vol ty valOp (.reg r) al as_ =>
    if r == llvmRegOf ptrVar then .store vol ty valOp (.reg r) (alignOfFact facts ptrVar ty al) as_
    else ins
  | other => other

def emitVerifiedLLVMWithFacts (facts : FactEnv) (a b : VarId)
    (insns : List LLVMInstr) (ptrVar : VarId := 0) : List LLVMInstr :=
  match insns with
  | [] => []
  | ins :: rest =>
    attachLoadStoreAlign facts ptrVar (attachOverflow facts ins) ::
      emitVerifiedLLVMWithFacts facts a b rest ptrVar

def withNoAlias (disjoint : Bool) (p : LLVMParam) : LLVMParam :=
  if !disjoint then p
  else if p.attrs.contains .noalias then p
  else { p with attrs := .noalias :: p.attrs }

/-- Add `noalias` only to `.ptr` parameters whose name is `v{ptrA}` or `v{ptrB}`. -/
def noaliasParams (facts : FactEnv) (ptrA ptrB : VarId) (lenA lenB : Nat)
    (ps : List LLVMParam) : List LLVMParam :=
  if !factMember facts (.disjointSlices ptrA ptrB lenA lenB) then ps
  else ps.map fun p =>
    match p.ty with
    | .ptr _ =>
      if p.name == llvmRegOf ptrA || p.name == llvmRegOf ptrB then withNoAlias true p else p
    | _ => p

def emitVerifiedLLVMFnWithFacts (facts : FactEnv) (ptrA ptrB : VarId) (lenA lenB : Nat)
    (a b : VarId) (fn : LLVMFn) (ptrVar : VarId := 0) : LLVMFn :=
  { fn with
    params := noaliasParams facts ptrA ptrB lenA lenB fn.params
    blocks := fn.blocks.map fun blk =>
      { blk with body := emitVerifiedLLVMWithFacts facts a b blk.body ptrVar } }

/-- A bounds check stays unless `idxLt` was retained. The unchecked form is sound
for states in which `idxLt` holds. -/
def lowerBoundsFreePTXLoad (facts : FactEnv) (idxVar lenVar : VarId) (ty : PTXType)
    (dst : String) (addr : PTXAddr) : List PTXStmt :=
  if factMember facts (.idxLt idxVar lenVar) then
    [.instr none (.ldGlobal ty dst addr)]
  else
    [ .instr none (.setp .ge .u64 "%p0" (.reg s!"%v{idxVar}") (.reg s!"%v{lenVar}"))
    , .instr (some { predReg := "%p0", negated := false }) (.bra "$L_done")
    , .instr none (.ldGlobal ty dst addr)
    , .label "$L_done" ]

def lowerBoundsFreeMetalLoad (facts : FactEnv) (idxVar lenVar : VarId)
    (buf : String) : List MSLStmt :=
  let idx := MSLExpr.var s!"v{idxVar}"
  let len := MSLExpr.var s!"v{lenVar}"
  let load := MSLStmt.assign "loaded" (.index buf idx)
  if factMember facts (.idxLt idxVar lenVar) then [load]
  else [.ifElse (.lt idx len) (.cons load .nil) .nil]

/-- 64-bit byte length of one element. -/
def elemBytes : Nat := 8

/-- A 1-D SIMT kernel: every launched lane `gid = ctaid.x * ntid.x + tid.x` that
satisfies `gid < len` loads `buf[gid]` (8 bytes) and stores it. When `idxLt` is
retained the per-lane guard is dropped; the launch contract is `grid.x * block.x ≤ len`. -/
def boundsFreePTXKernel (facts : FactEnv) (idxVar lenVar : VarId) : PTXKernel :=
  let lenReg := s!"%v{lenVar}"
  let guarded := !factMember facts (.idxLt idxVar lenVar)
  let gid : List PTXStmt :=
    [ .instr none (.mov .u32 "%r0" (.sreg .ctaidX))
    , .instr none (.mov .u32 "%r1" (.sreg .ntidX))
    , .instr none (.mov .u32 "%r2" (.sreg .tidX))
    , .instr none (.mul .wide .u32 "%rd0" (.reg "%r0") (.reg "%r1"))
    , .instr none (.cvt .none .u64 .u32 "%rd1" (.reg "%r2"))
    , .instr none (.add .none .u64 "%rd2" (.reg "%rd0") (.reg "%rd1")) ]
  let guard : List PTXStmt :=
    if guarded then
      [ .instr none (.ldParam .u64 lenReg "param_len")
      , .instr none (.setp .ge .u64 "%p0" (.reg "%rd2") (.reg lenReg))
      , .instr (some { predReg := "%p0", negated := false }) (.bra "$L_done") ]
    else []
  let body : List PTXStmt :=
    [ .instr none (.ldParam .u64 "%addr" "param_addr")
    , .instr none (.ldParam .u64 "%out" "param_out")
    , .instr none (.shl .b64 "%rd5" (.reg "%rd2") (.immU64 (BitVec.ofNat 64 3)))
    , .instr none (.add .none .u64 "%rd6" (.reg "%addr") (.reg "%rd5"))
    , .instr none (.ldGlobal .u64 "%dst" (.regOffset "%rd6" 0))
    , .instr none (.add .none .u64 "%rd7" (.reg "%out") (.reg "%rd5"))
    , .instr none (.stGlobal .u64 (.regOffset "%rd7" 0) (.reg "%dst"))
    , .label "$L_done"
    , .instr none .ret ]
  { name := "ln_bounds_free_load"
  , params :=
      [ { ty := .u64, name := "param_len" }, { ty := .u64, name := "param_addr" }
      , { ty := .u64, name := "param_out" } ]
  , regDecls :=
      [ { ty := .pred, prefixName := "%p", count := 1 }
      , { ty := .u32, prefixName := "%r", count := 3 }
      , { ty := .u64, prefixName := "%rd", count := 8 }
      , { ty := .u64, prefixName := "%addr", count := 0 }
      , { ty := .u64, prefixName := "%out", count := 0 }
      , { ty := .u64, prefixName := "%dst", count := 0 }
      , { ty := .u64, prefixName := lenReg, count := 0 } ]
  , body := gid ++ guard ++ body }

/-- The Metal twin of `boundsFreePTXKernel`: one thread per `gid`, guarded unless the
retained `idxLt` covers every launched lane. -/
def boundsFreeMetalKernel (facts : FactEnv) (idxVar lenVar : VarId) : MSLKernelDecl :=
  let guarded := !factMember facts (.idxLt idxVar lenVar)
  let load := MSLStmt.indexAssign "out" (.var "gid") (.index "buf" (.var "gid"))
  let inner := if guarded then
      [.ifElse (.lt (.cast .ulong (.var "gid")) (.var "len")) (.cons load .nil) .nil]
    else [load]
  { name := "ln_bounds_free_load"
  , params :=
      [ { ty := .pointer .device true .ulong, name := "buf", attr := some (.buffer 0) }
      , { ty := .pointer .device false .ulong, name := "out", attr := some (.buffer 1) }
      , { ty := .ref .constant .ulong, name := "len", attr := some (.buffer 2) }
      , { ty := .uint, name := "gid", attr := some .threadPositionInGrid } ]
  , body := inner ++ [.returnStmt] }

/-- Build the `VerifiedCodePassContract` from the kernel proof in `ProofRetentionProofs`. -/
def verifiedProofRetentionContract
    (h : ∀ c : LNIRCode, LeanNative.Semantics.CodeRefines c (dischargeLocalExclusivity c)) :
    LeanNative.Transform.VerifiedCodePassContract where
  name := "ProofRetention"
  theoremRef := "LeanNative.Proofs.dischargeLocalExclusivity_refines"
  notes := "Discharge local exclusivity facts retained from pre-erasure LCNF"
  runCode := dischargeLocalExclusivity
  sound := h

end LeanNative.Frontend.ProofRetention
