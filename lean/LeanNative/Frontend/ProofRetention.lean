import Lean.Compiler.LCNF.Basic
import LeanNative.IR.AST
import LeanNative.Transform.Pass
import LeanNative.Backend.GPUIR
import LeanNative.Backend.LLVMLower
import LeanNative.Backend.PTXAst.Syntax
import LeanNative.Backend.MetalAst.Syntax

/-!
# D1 proof-carrying LCNF (`LeanNative.Frontend.ProofRetention`)

Facts retained from pre-erasure `Lean.Compiler.LCNF.Code .pure` before `.mono` proof erasure,
and the verified specializations they justify on `LNIRCode`, `LLVMAst`, `PTXAst`, and `MetalAst`.
-/

namespace LeanNative.Frontend.ProofRetention

open LeanNative.IR
open LeanNative.Backend.GPUIR
open LeanNative.Backend.TargetIR
open LeanNative.Backend.LLVMAst
open LeanNative.Backend.PTXAst
open LeanNative.Backend.MetalAst

export LeanNative.IR (RetainedFact FactEnv factMember consFact)
export LeanNative.Backend.GPUIR (LaunchBoundsCert launchCertCovers)

set_option autoImplicit false

/-- Mapping from LCNF `FVarId`s to LNIR `VarId`s threaded during pure-phase fact extraction. -/
structure RetentionState where
  fvarMap : List (Lean.FVarId × VarId) := []
  fvarTypes : List (Lean.FVarId × Lean.Expr) := []
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

def noteFVarType (st : RetentionState) (fv : Lean.FVarId) (ty : Lean.Expr) : RetentionState :=
  match st.fvarTypes.find? (fun p => p.1 == fv) with
  | some _ => st
  | none => { st with fvarTypes := (fv, ty) :: st.fvarTypes }

def internTypedFVar (st : RetentionState) (fv : Lean.FVarId) (ty : Lean.Expr) :
    VarId × RetentionState :=
  let (vid, st1) := internFVar st fv
  (vid, noteFVarType st1 fv ty)

def internParams (st : RetentionState)
    (ps : List (Lean.Compiler.LCNF.Param .pure)) : RetentionState :=
  match ps with
  | [] => st
  | p :: rest =>
    let (_, st1) := internTypedFVar st p.fvarId p.type
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

def isCanonicalHPowInst (inst : Lean.Expr) : Bool :=
  inst == Lean.mkApp
    (Lean.mkApp
      (Lean.mkApp (Lean.mkConst ``instHPow [Lean.Level.zero, Lean.Level.zero]) (Lean.mkConst ``Nat))
      (Lean.mkConst ``Nat))
    (Lean.mkApp
      (Lean.mkApp (Lean.mkConst ``instPowNat [Lean.Level.zero]) (Lean.mkConst ``Nat))
      (Lean.mkConst ``instNatPowNat))

/-- `OfNat.ofNat` on `Nat` (`instOfNatNat n`), a non-wrapping `UInt64.instOfNat` /
`USize.instOfNat` (`n < 2^64` / `n < 2^32`), or a bare nat literal.
A custom `OfNat` instance, or `2^64` elaborated as `UInt64` (which wraps to `0`), is rejected. -/
def litNat? (e : Lean.Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ =>
    match e.getAppFnArgs with
    | (``OfNat.ofNat, #[t, .lit (.natVal n), inst]) =>
      if t == Lean.mkConst ``Nat &&
          inst == Lean.mkApp (Lean.mkConst ``instOfNatNat) (.lit (.natVal n)) then
        some n
      else if t == Lean.mkConst ``UInt64 &&
          inst == Lean.mkApp (Lean.mkConst ``UInt64.instOfNat) (.lit (.natVal n)) &&
          n < 2 ^ 64 then
        some n
      else if t == Lean.mkConst ``USize &&
          inst == Lean.mkApp (Lean.mkConst ``USize.instOfNat) (.lit (.natVal n)) &&
          n < 2 ^ 32 then
        some n
      else none
    | (``HPow.hPow, #[t1, t2, t3, inst, .lit (.natVal b), .lit (.natVal k)]) =>
      if t1 == Lean.mkConst ``Nat && t2 == Lean.mkConst ``Nat && t3 == Lean.mkConst ``Nat &&
          isCanonicalHPowInst inst && b == 2 && (k == 63 || k == 64) then
        some (2 ^ k)
      else none
    | (``HPow.hPow, #[t1, t2, t3, inst, base, exp]) =>
      if t1 == Lean.mkConst ``Nat && t2 == Lean.mkConst ``Nat && t3 == Lean.mkConst ``Nat &&
          isCanonicalHPowInst inst then
        match base.getAppFnArgs, exp.getAppFnArgs with
        | (``OfNat.ofNat, #[tb, .lit (.natVal b), ib]), (``OfNat.ofNat, #[te, .lit (.natVal k), ie]) =>
          if tb == Lean.mkConst ``Nat && te == Lean.mkConst ``Nat &&
              ib == Lean.mkApp (Lean.mkConst ``instOfNatNat) (.lit (.natVal b)) &&
              ie == Lean.mkApp (Lean.mkConst ``instOfNatNat) (.lit (.natVal k)) &&
              b == 2 && (k == 63 || k == 64) then
            some (2 ^ k)
          else none
        | _, _ => none
      else none
    | _ => none

/-- Peel `UInt64.toNat` / `USize.toNat` with explicit structural fuel. -/
def unwrapOperandAux (fuel : Nat) (e : Lean.Expr) : Lean.Expr :=
  match fuel with
  | 0 => e
  | fuel + 1 =>
    match e.getAppFnArgs with
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
  n == ``LT.lt || n == ``Nat.lt || n == ``UInt64.lt || n == ``USize.lt ||
  n == ``LE.le || n == ``Nat.le || n == ``UInt64.le || n == ``USize.le ||
  n == ``Dvd.dvd || n == ``Eq ||
  n == ``And || n == ``SlicesDisjoint

def isPropType (ty : Lean.Expr) : Bool :=
  isRetainedPropHead (ty.getAppFnArgs).1

/-- Unboxed machine-word carriers (`UInt64`, `USize`). Runtime `Nat` / `Fin` (tagged pointers),
signed integers, `BitVec`, and custom structures are rejected. -/
def isOperandCarrier (n : Lean.Name) : Bool :=
  n == ``UInt64 || n == ``USize

def isOperandTy (e : Lean.Expr) : Bool :=
  match e.getAppFn.constName? with
  | some n => isOperandCarrier n
  | none => false

/-- A machine-word fvar operand, or a literal `Nat` interned as a fresh variable.
When `fv` has a recorded type in `st.fvarTypes`, that type must be `UInt64` or `USize`;
when `fv` has no recorded type, `UInt64.toNat` / `USize.toNat` must have been peeled. -/
def operandVar? (st : RetentionState) (e : Lean.Expr) : Option (VarId × RetentionState) :=
  match litNat? (unwrapOperand e) with
  | some n => some (internFVar st { name := .num `lit n })
  | none =>
    let peeled := unwrapOperand e != e
    match unwrapOperand e with
    | .fvar fv =>
      let ok := match st.fvarTypes.find? (fun p => p.1 == fv) with
        | some (_, ty) => isOperandTy ty
        | none => peeled
      if ok then some (internFVar st fv) else none
    | _ => none

def twoOperands (st : RetentionState) (a b : Lean.Expr) :
    Option (VarId × VarId × RetentionState) :=
  match operandVar? st a with
  | none => none
  | some (va, st1) =>
    match operandVar? st1 b with
    | none => none
    | some (vb, st2) => some (va, vb, st2)

/-- `@instHAdd Nat instAddNat`, or the bare `instAddNat` instance. -/
def isCanonicalNatAddInst (inst : Lean.Expr) : Bool :=
  inst == Lean.mkConst ``instAddNat ||
    inst.getAppFnArgs == (``instHAdd, #[Lean.mkConst ``Nat, Lean.mkConst ``instAddNat])

/-- `@instHMul Nat instMulNat`, or the bare `instMulNat` instance. -/
def isCanonicalNatMulInst (inst : Lean.Expr) : Bool :=
  inst == Lean.mkConst ``instMulNat ||
    inst.getAppFnArgs == (``instHMul, #[Lean.mkConst ``Nat, Lean.mkConst ``instMulNat])

/-- `a + b` or `a * b` on `Nat` with the standard-library instance.
Heterogeneous `HAdd`/`HMul` (e.g. `UInt64`) and custom instances are rejected:
`UInt64.toNat` around a wrapping add is never peeled. -/
def binApp? (e : Lean.Expr) (add : Bool) : Option (Lean.Expr × Lean.Expr) :=
  match e.getAppFnArgs with
  | (``Nat.add, #[a, b]) => if add then some (a, b) else none
  | (``Nat.mul, #[a, b]) => if add then none else some (a, b)
  | (``HAdd.hAdd, #[t1, t2, t3, inst, a, b]) =>
    if add && t1 == Lean.mkConst ``Nat && t2 == Lean.mkConst ``Nat && t3 == Lean.mkConst ``Nat &&
        isCanonicalNatAddInst inst then some (a, b) else none
  | (``HMul.hMul, #[t1, t2, t3, inst, a, b]) =>
    if !add && t1 == Lean.mkConst ``Nat && t2 == Lean.mkConst ``Nat && t3 == Lean.mkConst ``Nat &&
        isCanonicalNatMulInst inst then some (a, b) else none
  | _ => none

/-- A canonical `<` or `≤` on `Nat`, `UInt64`, or `USize`. Custom instances and every other
carrier (`Int`, `BitVec`, structures) are rejected. -/
def isCanonicalRelApp? (e : Lean.Expr) (wantLt : Bool) : Option (Lean.Name × Lean.Expr × Lean.Expr) :=
  match e.getAppFnArgs with
  | (``Nat.lt, #[lhs, rhs]) => if wantLt then some (``Nat, lhs, rhs) else none
  | (``UInt64.lt, #[lhs, rhs]) => if wantLt then some (``UInt64, lhs, rhs) else none
  | (``USize.lt, #[lhs, rhs]) => if wantLt then some (``USize, lhs, rhs) else none
  | (``Nat.le, #[lhs, rhs]) => if wantLt then none else some (``Nat, lhs, rhs)
  | (``UInt64.le, #[lhs, rhs]) => if wantLt then none else some (``UInt64, lhs, rhs)
  | (``USize.le, #[lhs, rhs]) => if wantLt then none else some (``USize, lhs, rhs)
  | (``LT.lt, #[ty, inst, lhs, rhs]) =>
    if !wantLt then none
    else if ty == Lean.mkConst ``Nat && inst == Lean.mkConst ``instLTNat then some (``Nat, lhs, rhs)
    else if ty == Lean.mkConst ``UInt64 && inst == Lean.mkConst ``instLTUInt64 then some (``UInt64, lhs, rhs)
    else if ty == Lean.mkConst ``USize && inst == Lean.mkConst ``instLTUSize then some (``USize, lhs, rhs)
    else none
  | (``LE.le, #[ty, inst, lhs, rhs]) =>
    if wantLt then none
    else if ty == Lean.mkConst ``Nat && inst == Lean.mkConst ``instLENat then some (``Nat, lhs, rhs)
    else if ty == Lean.mkConst ``UInt64 && inst == Lean.mkConst ``instLEUInt64 then some (``UInt64, lhs, rhs)
    else if ty == Lean.mkConst ``USize && inst == Lean.mkConst ``instLEUSize then some (``USize, lhs, rhs)
    else none
  | _ => none

/-- `@instHMod Nat Nat.instMod`, or the bare `Nat.instMod`. -/
def isCanonicalNatModInst (inst : Lean.Expr) : Bool :=
  inst == Lean.mkConst ``Nat.instMod ||
    inst.getAppFnArgs == (``instHMod, #[Lean.mkConst ``Nat, Lean.mkConst ``Nat.instMod])

/-- `@instHMod UInt64 instModUInt64`, or the bare `instModUInt64`. -/
def isCanonicalUInt64ModInst (inst : Lean.Expr) : Bool :=
  inst == Lean.mkConst ``instModUInt64 ||
    inst.getAppFnArgs == (``instHMod, #[Lean.mkConst ``UInt64, Lean.mkConst ``instModUInt64])

/-- `@instHMod USize instModUSize`, or the bare `instModUSize`. -/
def isCanonicalUSizeModInst (inst : Lean.Expr) : Bool :=
  inst == Lean.mkConst ``instModUSize ||
    inst.getAppFnArgs == (``instHMod, #[Lean.mkConst ``USize, Lean.mkConst ``instModUSize])

/-- `n` is `2^63` or `2^64`. -/
def isWidthBound (n : Nat) : Bool :=
  n == 2 ^ 63 || n == 2 ^ 64

/-- `(a + b < 2^63 | 2^64)` or `(a * b < 2^63 | 2^64)`.
`2^63` justifies `nsw` (and `nuw`); `2^64` justifies `nuw` only. -/
def overflowFact? (st : RetentionState) (lhs bound : Lean.Expr) : Option (RetainedFact × RetentionState) :=
  match litNat? (unwrapOperand bound) with
  | none => none
  | some n =>
    if !isWidthBound n then none
    else
      let nsw := n == 2 ^ 63
      match binApp? lhs true with
      | some (a, b) =>
        match twoOperands st a b with
        | some (va, vb, st2) => some (.noOverflowAdd va vb nsw true, st2)
        | none => none
      | none =>
        match binApp? lhs false with
        | some (a, b) =>
          match twoOperands st a b with
          | some (va, vb, st2) => some (.noOverflowMul va vb nsw true, st2)
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

/-- `p + len ≤ 2^64` as a pointer and a length, on the canonical `Nat` order. -/
def sliceEnd? (st : RetentionState) (e : Lean.Expr) : Option (VarId × VarId × RetentionState) :=
  match isCanonicalRelApp? (unwrapOperand e) false with
  | some (``Nat, lhs, rhs) =>
    match litNat? (unwrapOperand rhs) with
    | some m =>
      if m != 2 ^ 64 then none
      else
        match binApp? lhs true with
        | some (p, len) =>
          match twoOperands st p len with
          | some (vp, vl, st2) => some (vp, vl, st2)
          | none => none
        | none => none
    | none => none
  | _ => none

/-- `a + lenA ≤ b` or `b + lenB ≤ a` as the two pointers and their lengths,
on the canonical `Nat` order. -/
def sliceOrder? (st : RetentionState) (e : Lean.Expr) :
    Option (VarId × VarId × VarId × VarId × RetentionState) :=
  match isCanonicalRelApp? (unwrapOperand e) false with
  | some (``Nat, lhs, rhs) =>
    match binApp? lhs true with
    | some (p, len) =>
      match twoOperands st p len with
      | some (vp, vl, st1) =>
        match operandVar? st1 rhs with
        | some (vq, st2) => some (vp, vl, vq, 0, st2)
        | none => none
      | none => none
    | none => none
  | _ => none

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

/-- A modulus on a canonical `Nat`/`UInt64`/`USize` instance. -/
def modApp? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  match e.getAppFnArgs with
  | (``Nat.mod, #[ptr, al]) => some (ptr, al)
  | (``UInt64.mod, #[ptr, al]) => some (ptr, al)
  | (``USize.mod, #[ptr, al]) => some (ptr, al)
  | (``HMod.hMod, #[t1, t2, t3, inst, ptr, al]) =>
    let ok :=
      (t1 == Lean.mkConst ``Nat && t2 == Lean.mkConst ``Nat && t3 == Lean.mkConst ``Nat &&
        isCanonicalNatModInst inst) ||
      (t1 == Lean.mkConst ``UInt64 && t2 == Lean.mkConst ``UInt64 && t3 == Lean.mkConst ``UInt64 &&
        isCanonicalUInt64ModInst inst) ||
      (t1 == Lean.mkConst ``USize && t2 == Lean.mkConst ``USize && t3 == Lean.mkConst ``USize &&
        isCanonicalUSizeModInst inst)
    if ok then some (ptr, al) else none
  | _ => none

/-- A fact justified by a `Prop` type, matched on the kernel constant's exact `Name`
and its canonical standard-library instance. -/
def factOfType (st : RetentionState) (ty : Lean.Expr) : Option (RetainedFact × RetentionState) :=
  if !isPropType ty then none
  else
    match isCanonicalRelApp? ty true with
    | some (_, lhs, rhs) =>
      match overflowFact? st lhs rhs with
      | some r => some r
      | none =>
        match twoOperands st lhs rhs with
        | some (a, b, st2) => some (.idxLt a b, st2)
        | none => none
    | none =>
      match isCanonicalRelApp? ty false with
      | some (_, lhs, rhs) => subFact? st lhs rhs
      | none =>
        match ty.getAppFnArgs with
        | (``Dvd.dvd, #[ty, inst, align, ptr]) =>
          if ty == Lean.mkConst ``Nat && inst == Lean.mkConst ``Nat.instDvd then
            alignedFact? st ptr align
          else none
        | (``Eq, #[eqTy, lhs, rhs]) =>
          if eqTy == Lean.mkConst ``Nat || eqTy == Lean.mkConst ``UInt64 ||
              eqTy == Lean.mkConst ``USize then
            match modApp? (unwrapOperand lhs) with
            | some (ptr, al) =>
              match litNat? (unwrapOperand rhs) with
              | some 0 => alignedFact? st ptr al
              | _ => none
            | none => none
          else none
        | (n, _) => if n == ``And || n == ``SlicesDisjoint then disjointFact? st ty else none

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

/-- A recognized `Bool`-producing test: `UInt64.decLt`, `USize.decLt`, `lean_is_exclusive`,
or `Decidable.decide` whose proposition is a retained fact. -/
def testOfLet (st : RetentionState) (lv : Lean.Compiler.LCNF.LetValue .pure) :
    Option (Option RetainedFact × RetentionState) :=
  match lv with
  | .const fnName _ args _ =>
    if fnName == ``UInt64.decLt || fnName == ``USize.decLt then
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
      let (dst, st1) := internTypedFVar st decl.fvarId decl.type
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
      let (dst, st1) := internTypedFVar st decl.fvarId decl.type
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

/-- Extract parameter facts from a kernel `forallE` telescope before LCNF `lcErased` erasure.
LCNF lowers every leading `forallE` binder 1-to-1 to a parameter in `d.params` (with `.unit`
for erased `Sort`/`Prop` binders), so each binder consumes one `VarId` in `paramVars` (or a
fresh `nextVar` slot once `paramVars` is exhausted) and records its kernel binder type. -/
def retainedForallParamFactsAux (fuel : Nat) (st : RetentionState) (paramVars : List VarId)
    (ty : Lean.Expr) : RetentionState :=
  match fuel, ty with
  | 0, _ => st
  | fuel + 1, .forallE _ dom body _ =>
    let fv : Lean.FVarId := { name := .num `_sig_param fuel }
    let (st1, restVars) := match paramVars with
      | v :: vs => (noteFVarType { st with fvarMap := (fv, v) :: st.fvarMap } fv dom, vs)
      | [] =>
        let (_, s) := internTypedFVar st fv dom
        (s, [])
    let st2 := match factOfType st1 dom with
      | some (f, s) => pushFactOpt s (some f)
      | none => st1
    retainedForallParamFactsAux fuel st2 restVars (body.instantiate1 (.fvar fv))
  | _, _ => st

def retainedForallParamFacts (paramVars : List VarId) (nextVar : VarId) (ty : Lean.Expr) : FactEnv :=
  (retainedForallParamFactsAux (paramVars.length + 32) { nextVar := nextVar } paramVars ty).facts

def retainedPureFactsWithSeed (fuel : Nat) (seedMap : List (Lean.FVarId × VarId))
    (nextVar : VarId) (params : List (Lean.Compiler.LCNF.Param .pure))
    (code : Lean.Compiler.LCNF.Code .pure) : FactEnv :=
  let st0 := internParams { fvarMap := seedMap, nextVar := nextVar } params
  let st1 := extractParamFacts st0 params
  (collectBranchStep fuel st1 [] (.inl code)).facts

def retainedPureDeclFactsWithSeed (fuel : Nat) (seedMap : List (Lean.FVarId × VarId))
    (nextVar : VarId) (decl : Lean.Compiler.LCNF.Decl .pure) : FactEnv :=
  match decl.value with
  | .code c => retainedPureFactsWithSeed fuel seedMap nextVar decl.params.toList c
  | .extern _ =>
    let st0 := internParams { fvarMap := seedMap, nextVar := nextVar } decl.params.toList
    (extractParamFacts st0 decl.params.toList).facts

def retainedPureFactsWithParams (fuel : Nat)
    (params : List (Lean.Compiler.LCNF.Param .pure))
    (code : Lean.Compiler.LCNF.Code .pure) : FactEnv :=
  retainedPureFactsWithSeed fuel [] 0 params code

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

export LeanNative.Backend.LLVMLower (
  overflowFlagsOf overflowOf subFlagsOf llvmRegOf mergeFlags attachOverflow
  alignOfFact attachLoadStoreAlign instrDstReg? factVarIds killRegFacts
  immutableParamFacts entryIsStraight emitVerifiedLLVMWithFacts emitBlockBodyWithFacts
  withNoAlias isCertifiedPtrParam noaliasParams emitVerifiedLLVMFnWithFacts applyRetainedFactsLLVMFn
)

/-- Intra-kernel scalar array load bounds-check elimination on PTX: inside a thread body,
a retained `idxLt idxVar lenVar` directly discharges the scalar `setp.ge %v{idxVar}, %v{lenVar}`
check before `ld.global`. Distinct from SIMT lane-guard specialization, which additionally
requires a host `LaunchBoundsCert` certifying `gridDim.x * blockDim.x ≤ len`. -/
def lowerBoundsFreePTXLoad (facts : FactEnv) (idxVar lenVar : VarId) (ty : PTXType)
    (dst : String) (addr : PTXAddr) : List PTXStmt :=
  if factMember facts (.idxLt idxVar lenVar) then
    [.instr none (.ldGlobal ty dst addr)]
  else
    [ .instr none (.setp .ge .u64 "%p0" (.reg s!"%v{idxVar}") (.reg s!"%v{lenVar}"))
    , .instr (some { predReg := "%p0", negated := false }) (.bra "$L_done")
    , .instr none (.ldGlobal ty dst addr)
    , .label "$L_done" ]

/-- Intra-kernel scalar array load bounds-check elimination on Metal MSL: inside a thread body,
a retained `idxLt idxVar lenVar` directly discharges `if (v{idxVar} < v{lenVar})` before indexing
`buf[v{idxVar}]`. Distinct from SIMT lane-guard specialization (`boundsFreeMetalKernel`). -/
def lowerBoundsFreeMetalLoad (facts : FactEnv) (idxVar lenVar : VarId)
    (buf : String) : List MSLStmt :=
  let idx := MSLExpr.var s!"v{idxVar}"
  let len := MSLExpr.var s!"v{lenVar}"
  let load := MSLStmt.assign "loaded" (.index buf idx)
  if factMember facts (.idxLt idxVar lenVar) then [load]
  else [.ifElse (.lt idx len) (.cons load .nil) .nil]

/-- 64-bit byte length of one element. -/
def elemBytes : Nat := 8

/-- Launch-geometry-certified 1-D SIMT PTX kernel: every launched lane
`gid = ctaid.x * ntid.x + tid.x` satisfying `gid < len` loads `buf[gid]` and stores it.
Dropping the per-lane `setp.ge.u64` / `@%p0 bra` guard requires BOTH an explicit `LaunchBoundsCert`
certifying `gridDim.x * blockDim.x ≤ len` for `(idxVar, lenVar)` AND a retained `idxLt`. -/
def boundsFreePTXKernel (facts : FactEnv) (idxVar lenVar : VarId)
    (launch? : Option LaunchBoundsCert := none) : PTXKernel :=
  let lenReg := s!"%v{lenVar}"
  let guarded := !(launchCertCovers launch? idxVar lenVar && factMember facts (.idxLt idxVar lenVar))
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

/-- Launch-geometry-certified Metal twin of `boundsFreePTXKernel`: one thread per `gid`,
retaining `if ((ulong)gid < len)` unless both an explicit `LaunchBoundsCert` certifying
`gridDim.x * blockDim.x ≤ len` for `(idxVar, lenVar)` and a retained `idxLt` are present. -/
def boundsFreeMetalKernel (facts : FactEnv) (idxVar lenVar : VarId)
    (launch? : Option LaunchBoundsCert := none) : MSLKernelDecl :=
  let guarded := !(launchCertCovers launch? idxVar lenVar && factMember facts (.idxLt idxVar lenVar))
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
