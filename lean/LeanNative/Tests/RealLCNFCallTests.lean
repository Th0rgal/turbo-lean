import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.ToImpureType
import LeanNative.IR.RealLCNFBridge
import LeanNative.IR.RealLCNFCallSemantics
import LeanNative.Semantics.Eval

/-!
# L2 (roadmap/HORIZONS.md rung L2 "Calls"): executable guards for the call semantics

Contract: `lean/LeanNative/Proofs/LowerCalls.lean` (acceptance section). Families:

1. A two-declaration environment where the caller's result is WRONG unless the callee
   body actually runs — kills call-as-noop mutants of `evalCodeF` / `evalStepF`.
2. A call-arity mismatch errors on the LNIR side (review F4; `bindParams` is strict on
   the source side).
3. Per-entry context and fuel (review F1): a nested chain whose middle declaration
   resolves its own callee only under ITS entry context, with a caller-context negative
   control; and a callee that exhausts its own entry fuel while the ambient fuel is ample.
4. A self-call falls to the old `.unsupportedCall` behavior under pairwise-fresh
   environments (stratification: the callee body runs under the STRICT SUFFIX).
5. `Δ = [] / Φ = []` runs agree with the old evaluators (`exceptAgrees` compares
   ok-payloads exactly and errors by shape, since `UBError` carries no `BEq`; the kernel
   theorems `evalCodeF_nil` / `evalStepF_nil` carry the full equality).

Plus the end-to-end instance: lowering caller and callee with `lowerRealLCNFDecl` and
evaluating the lowered caller under the lowered environment produces the source result —
the executable shape of `lowerRealLCNFDecl_soundF`.
-/

namespace LeanNative.Tests.RealLCNFCallTests

open Lean
open Lean.Compiler.LCNF
open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

/-- Result agreement: ok-payloads compared exactly; errors by shape (`UBError` has no
    `BEq`); the kernel conservativity theorems carry the full equality. -/
private def exceptAgrees : Except UBError (Val × HeapState) → Except UBError (Val × HeapState) → Bool
  | .ok (v1, h1), .ok (v2, h2) => v1 == v2 && h1 == h2
  | .error _, .error _ => true
  | _, _ => false

/-! ### LNIR side (`evalCodeF`) -/

/-- Callee `f_sym x = x + 1` (call-free body). -/
private def calleeL : LNIRDecl :=
  { name := "f_sym"
    params := [{ id := 0, name := "x", ty := .i64 }]
    retTy := .i64
    body := .letBind 1 .i64 (.scalar (.binOp .add (.var 0) (.constU64 1))) (.ret 1) }

/-- Caller body `g x = f_sym x + x` — value-sensitive in the callee's result. -/
private def callerBodyL : LNIRCode :=
  .letBind 1 .i64 (.call "f_sym" [0] .i64 false)
    (.letBind 2 .i64 (.scalar (.binOp .add (.var 1) (.var 0))) (.ret 2))

private def runCodeF (Φ : FuncEnv) (body : LNIRCode) (arg : Val) : Except UBError (Val × HeapState) :=
  evalCodeF Φ 32 (VarEnv.empty.bind 0 arg) HeapState.empty body

-- 1. The callee body must actually run: g 5 = (5+1) + 5 = 11.
#guard (match runCodeF [(calleeL, 32)] callerBodyL (.u64 5) with
        | .ok (v, hst) => v == .u64 11 && hst == HeapState.empty
        | .error _ => false)

-- 2. Arity mismatch errors (reviews F4/F3): TWO arguments to a 1-parameter callee.
--    A too-many pin on purpose: an empty argument list errors through the unbound
--    parameter either way, so a deleted arity check would survive it.
#guard (runCodeF [(calleeL, 32)]
  (.letBind 1 .i64 (.call "f_sym" [0, 0] .i64 false) (.ret 1)) (.u64 5)).isOk == false

-- 3. Per-entry fuel: the callee runs at ITS entry's fuel. With entry fuel 32 the chain
--    succeeds (guard 1); the LNIR fuel is pass-through (loops only), so the per-entry
--    fuel pin lives on the source side below.

-- 4. Stratified self-call, depth-1: `g_self` IS the single entry, so evaluating its
--    body under the full Φ resolves the self-call ONCE against its own entry; the
--    unrolled body runs under the strict suffix ([]), where the nested self-call
--    misses and falls to `evalExpr`, which errors on the unknown symbol.
private def selfL : LNIRDecl :=
  { name := "g_self"
    params := [{ id := 0, name := "x", ty := .i64 }]
    retTy := .i64
    body := .letBind 1 .i64 (.call "g_self" [0] .i64 false) (.ret 1) }

#guard (runCodeF [(selfL, 32)] selfL.body (.u64 5)).isOk == false

-- 5. Φ = [] agrees with the old evaluator: on a call-free body (both ok, same value) and
--    on a call-bearing body (both error).
#guard exceptAgrees (runCodeF [] calleeL.body (.u64 5))
  (evalCode 32 (VarEnv.empty.bind 0 (.u64 5)) HeapState.empty calleeL.body)
#guard (evalCode 32 (VarEnv.empty.bind 0 (.u64 5)) HeapState.empty calleeL.body).isOk == true
#guard exceptAgrees (runCodeF [] callerBodyL (.u64 5))
  (evalCode 32 (VarEnv.empty.bind 0 (.u64 5)) HeapState.empty callerBodyL)
#guard (evalCode 32 (VarEnv.empty.bind 0 (.u64 5)) HeapState.empty callerBodyL).isOk == false

-- `callFreeCode` classifies the fixtures.
#guard callFreeCode calleeL.body == true
#guard callFreeCode callerBodyL == false

/-! ### Source side (`evalStepF` / `evalRealLCNFDeclF`) over real LCNF declarations -/

private def fv (n : Nat) : FVarId := { name := .num `x n }

private def mkParam (n : Nat) (ty : Expr) (borrow : Bool := false) : Param .impure :=
  { fvarId := fv n, binderName := .num `p n, type := ty, borrow := borrow }

private def mkLet (n : Nat) (ty : Expr) (val : LetValue .impure) : LetDecl .impure :=
  { fvarId := fv n, binderName := .num `v n, type := ty, value := val }

private def mkDecl (name : Name) (params : Array (Param .impure)) (retTy : Expr)
    (body : Code .impure) : Decl .impure :=
  { name := name
    levelParams := []
    type := retTy
    params := params
    value := .code body
    inlineAttr? := none }

/-- Source callee `l2_callee x = x + 1`. -/
private def calleeS : Decl .impure :=
  let u64 := ImpureType.uint64
  mkDecl `l2_callee #[mkParam 10 u64] u64 <|
    .let (mkLet 11 u64 (.lit (.uint64 1))) <|
    .let (mkLet 12 u64 (.fap ``UInt64.add #[.fvar (fv 10), .fvar (fv 11)] rfl)) <|
    .return (fv 12)

/-- Source caller `l2_caller x = l2_callee x + x`. -/
private def callerS : Decl .impure :=
  let u64 := ImpureType.uint64
  mkDecl `l2_caller #[mkParam 1 u64] u64 <|
    .let (mkLet 3 u64 (.fap `l2_callee #[.fvar (fv 1)] rfl)) <|
    .let (mkLet 4 u64 (.fap ``UInt64.add #[.fvar (fv 3), .fvar (fv 1)] rfl)) <|
    .return (fv 4)

private def ctxS : RealBridgeCtx :=
  { arch := .x86_64, localCallees := [(`l2_callee, "f_sym")] }

private def declProducesF (Δ : DeclEnv) (ctx : RealBridgeCtx) (d : Decl .impure)
    (args : List Val) (expected : Val) : Bool :=
  match evalRealLCNFDeclF Δ 32 ctx d args with
  | .ok (v, hst) => v == expected && hst == HeapState.empty
  | .error _ => false

-- 1. The callee body must actually run: l2_caller 5 = (5+1) + 5 = 11.
#guard declProducesF [(calleeS, ctxS, 32)] ctxS callerS [.u64 5] (.u64 11)

-- The old semantics deliberately errors on the same program (the vacuity L2 closes).
#guard (evalRealLCNFDecl 32 ctxS callerS [.u64 5]).isOk == false

-- 3a. Per-entry FUEL: the callee runs at ITS entry's fuel — entry fuel 1 exhausts inside
--     the callee body while the ambient fuel (32) is ample.
#guard (evalRealLCNFDeclF [(calleeS, ctxS, 1)] 32 ctxS callerS [.u64 5]).isOk == false

-- 3b. Per-entry CONTEXT (review F1's fix, pinned): a → b → c where only b's OWN entry
--     context maps c. Under per-entry contexts the chain computes a 5 = (5+1+5)+5 = 16;
--     with b's entry carrying the TOP context instead (the pre-F1 caller-context
--     semantics), b's call to c cannot resolve and the run errors.
private def declC : Decl .impure :=
  let u64 := ImpureType.uint64
  mkDecl `l2_c #[mkParam 50 u64] u64 <|
    .let (mkLet 51 u64 (.lit (.uint64 1))) <|
    .let (mkLet 52 u64 (.fap ``UInt64.add #[.fvar (fv 50), .fvar (fv 51)] rfl)) <|
    .return (fv 52)

private def declB : Decl .impure :=
  let u64 := ImpureType.uint64
  mkDecl `l2_b #[mkParam 30 u64] u64 <|
    .let (mkLet 31 u64 (.fap `l2_c #[.fvar (fv 30)] rfl)) <|
    .let (mkLet 32 u64 (.fap ``UInt64.add #[.fvar (fv 31), .fvar (fv 30)] rfl)) <|
    .return (fv 32)

private def declA : Decl .impure :=
  let u64 := ImpureType.uint64
  mkDecl `l2_a #[mkParam 40 u64] u64 <|
    .let (mkLet 41 u64 (.fap `l2_b #[.fvar (fv 40)] rfl)) <|
    .let (mkLet 42 u64 (.fap ``UInt64.add #[.fvar (fv 41), .fvar (fv 40)] rfl)) <|
    .return (fv 42)

private def ctxTop : RealBridgeCtx := { arch := .x86_64, localCallees := [(`l2_b, "b_sym")] }
private def ctxB : RealBridgeCtx := { arch := .x86_64, localCallees := [(`l2_c, "c_sym")] }
private def ctxC : RealBridgeCtx := { arch := .x86_64 }

#guard declProducesF [(declB, ctxB, 32), (declC, ctxC, 32)] ctxTop declA [.u64 5] (.u64 16)
#guard (evalRealLCNFDeclF [(declB, ctxTop, 32), (declC, ctxC, 32)] 32 ctxTop declA [.u64 5]).isOk == false

-- 3c. Per-entry CONTEXT, `ctorLayouts` clause (review F1's cited failure, pinned): the
--     callee `uset`s/`uproj`s a constructor only ITS entry's `ctorLayouts` knows. With
--     the layout, logical index 1 (= objSlots) resolves to usize slot 0 and the run
--     returns the written value; with the callee entry carrying a context that knows
--     the constructor NAME but no layout (the pre-F1 caller-context shape), the slot
--     lookup misses `findLayout?` and falls back to the raw index 1, which is out of
--     bounds for the 1-scalar-slot object, so the run errors.
private def boxSpec : RcCtorLayoutSpec :=
  { ctorName := `l2_box, cidx := 0, objSlots := 1, usizeSlots := 1, scalarSlots := [] }

/-- `l2_u o y`: write `y` into `o`'s usize slot (logical index 1), read it back. -/
private def calleeU : Decl .impure :=
  let u64 := ImpureType.uint64
  mkDecl `l2_u #[mkParam 60 u64, mkParam 61 u64] u64 <|
    .uset (fv 60) 1 (fv 61) (
      .let (mkLet 62 u64 (.uproj 1 (fv 60) rfl)) <|
      .return (fv 62)) rfl

private def callerU : Decl .impure :=
  let u64 := ImpureType.uint64
  mkDecl `l2_uc #[mkParam 65 u64, mkParam 66 u64] u64 <|
    .let (mkLet 67 u64 (.fap `l2_u #[.fvar (fv 65), .fvar (fv 66)] rfl)) <|
    .return (fv 67)

private def ctxUTop : RealBridgeCtx := { arch := .x86_64, localCallees := [(`l2_u, "u_sym")] }
/-- The callee's OWN context: the layout plus the known-constructor binding for its param. -/
private def ctxU : RealBridgeCtx :=
  { arch := .x86_64, ctorLayouts := [(`l2_box, boxSpec)], knownFVarCtors := [(fv 60, `l2_box)] }
/-- Negative control: the constructor NAME is known but no layout — `findLayout?` misses. -/
private def ctxUNoLayout : RealBridgeCtx :=
  { arch := .x86_64, knownFVarCtors := [(fv 60, `l2_box)] }

/-- One heap constructor with 1 object field and 1 scalar slot, allocated up front. -/
private def heapU : Nat × HeapState := HeapState.empty.allocHeapCtor 0 [.u64 7] [.u64 0]

#guard (match evalRealLCNFDeclF [(calleeU, ctxU, 32)] 32 ctxUTop callerU
          [.objPtr heapU.1, .u64 42] heapU.2 with
        | .ok (v, _) => v == .u64 42
        | .error _ => false)
#guard (evalRealLCNFDeclF [(calleeU, ctxUNoLayout, 32)] 32 ctxUTop callerU
          [.objPtr heapU.1, .u64 42] heapU.2).isOk == false

-- 4. Stratified self-call, depth-1: `l2_self` is in Δ, so the top-level run resolves
--    its self-call once against its own entry; the unrolled body runs under the strict
--    suffix ([]), where the nested call misses and keeps the old `.unsupportedCall`
--    error, which propagates out through the resolved outer call.
private def selfS : Decl .impure :=
  let u64 := ImpureType.uint64
  mkDecl `l2_self #[mkParam 20 u64] u64 <|
    .let (mkLet 21 u64 (.fap `l2_self #[.fvar (fv 20)] rfl)) <|
    .return (fv 21)

private def ctxSelf : RealBridgeCtx :=
  { arch := .x86_64, localCallees := [(`l2_self, "l2_self_sym")] }

#guard (evalRealLCNFDeclF [(selfS, ctxSelf, 32)] 32 ctxSelf selfS [.u64 5]).isOk == false

-- 5. Δ = [] agrees with the old evaluator on the same inputs (caller errors both ways;
--    callee succeeds both ways with the same payload).
#guard exceptAgrees (evalRealLCNFDeclF [] 32 ctxS callerS [.u64 5])
  (evalRealLCNFDecl 32 ctxS callerS [.u64 5])
#guard exceptAgrees (evalRealLCNFDeclF [] 32 ctxS calleeS [.u64 5])
  (evalRealLCNFDecl 32 ctxS calleeS [.u64 5])
#guard (evalRealLCNFDecl 32 ctxS calleeS [.u64 5]).isOk == true

/-! ### End to end: the executable shape of `lowerRealLCNFDecl_soundF` -/

private def loweredPair? : Option (LNIRDecl × LNIRDecl) :=
  match lowerRealLCNFDecl 32 ctxS calleeS "f_sym", lowerRealLCNFDecl 32 ctxS callerS "g_sym" with
  | .ok fL, .ok gL => some (fL, gL)
  | _, _ => none

/-- Lower both declarations, then run the LOWERED caller under the LOWERED environment
    with the declaration-entry binding convention — must produce the source result. -/
private def e2eCallSound : Bool :=
  match loweredPair? with
  | some (fL, gL) =>
    let venv := (gL.params.zip [Val.u64 5]).foldl (fun acc (p, val) => acc.bind p.id val) VarEnv.empty
    match evalCodeF [(fL, 32)] 32 venv HeapState.empty gL.body with
    | .ok (v, hst) => v == .u64 11 && hst == HeapState.empty
    | .error _ => false
  | none => false

#guard e2eCallSound == true

end LeanNative.Tests.RealLCNFCallTests
