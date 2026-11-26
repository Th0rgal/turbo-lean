import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.ToImpureType
import LeanNative.IR.RealLCNFBridge
import LeanNative.IR.RealLCNFRecSemantics
import LeanNative.Semantics.EvalRec

/-!
# L3 (roadmap/HORIZONS.md rung L3 "Recursion and loops"): executable guards for the
# fuel-indexed recursion semantics

Contract: `lean/LeanNative/Proofs/LowerRec.lean` (Part I, "Executable guards"). Families:

1. A self-recursive declaration (countdown-accumulate, `sum n acc`) whose
   `evalRealLCNFDeclR` result is wrong unless the callee body re-enters: kills
   call-as-noop mutants of `evalStepR`.
2. The same declaration at too small a step budget ends in `.error .fuelExhausted`,
   never a wrong `.ok`.
3. A two-declaration MUTUAL pair (even/odd) evaluating through `Δ`, with both orders of
   `Δ`, each callee under its OWN paired context.
4. `Δ = [] / Φ = []` runs agree with the old evaluators on a call-bearing body
   (`exceptAgrees` compares ok-payloads exactly and errors by shape, since `UBError`
   carries no `BEq`; the kernel theorems `evalStepR_nil` / `evalCodeR_nil` carry the full
   equality).
5. An `evalCodeR` run of the LOWERED self-call body under `Φ = [d]` produces the source
   result; the LNIR call budget counts call DEPTH, so too little fuel is
   `.error .fuelExhausted` and the empty environment keeps the old refusal.
-/

namespace LeanNative.Tests.RealLCNFRecTests

open Lean
open Lean.Compiler.LCNF
open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

/-- Result agreement: ok-payloads compared exactly; errors by shape. -/
private def exceptAgrees : Except UBError (Val × HeapState) → Except UBError (Val × HeapState) → Bool
  | .ok (v1, h1), .ok (v2, h2) => v1 == v2 && h1 == h2
  | .error _, .error _ => true
  | _, _ => false

/-- The run ended on the evaluator budget, not on a value or on source UB. -/
private def isFuelExhausted : Except UBError (Val × HeapState) → Bool
  | .error .fuelExhausted => true
  | _ => false

private def okValue? : Except UBError (Val × HeapState) → Option Val
  | .ok (v, _) => some v
  | .error _ => none

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

private def falseCtor : CtorInfo := { name := ``Bool.false, cidx := 0, size := 0, usize := 0, ssize := 0 }
private def trueCtor : CtorInfo := { name := ``Bool.true, cidx := 1, size := 0, usize := 0, ssize := 0 }

/-! ### 1-2. Self recursion: `l3_sum n acc = if n == 0 then acc else l3_sum (n - 1) (acc + n)` -/

private def sumDecl : Decl .impure :=
  let u64 := ImpureType.uint64
  let bTy := mkConst ``Bool
  let recur : Code .impure :=
    .let (mkLet 5 u64 (.lit (.uint64 1))) <|
    .let (mkLet 6 u64 (.fap ``UInt64.sub #[.fvar (fv 1), .fvar (fv 5)] rfl)) <|
    .let (mkLet 7 u64 (.fap ``UInt64.add #[.fvar (fv 2), .fvar (fv 1)] rfl)) <|
    .let (mkLet 8 u64 (.fap `l3_sum #[.fvar (fv 6), .fvar (fv 7)] rfl)) <|
    .return (fv 8)
  mkDecl `l3_sum #[mkParam 1 u64, mkParam 2 u64] u64 <|
    .let (mkLet 3 u64 (.lit (.uint64 0))) <|
    .let (mkLet 4 bTy (.fap `UInt64.beq #[.fvar (fv 1), .fvar (fv 3)] rfl)) <|
    .cases (Cases.mk ``Bool u64 (fv 4) #[.ctorAlt falseCtor recur rfl, .ctorAlt trueCtor (.return (fv 2)) rfl])

/-- The driver's per-declaration context maps the declaration's OWN name. -/
private def ctxSum : RealBridgeCtx :=
  { arch := .x86_64, localCallees := [(`l3_sum, "l3_sum_sym")] }

private def runSum (fuel : Nat) (n acc : UInt64) : Except UBError (Val × HeapState) :=
  evalRealLCNFDeclR [(sumDecl, ctxSum)] fuel ctxSum sumDecl [.u64 n, .u64 acc]

-- 1. The callee body must re-enter: sum 4 0 = 4 + 3 + 2 + 1 = 10 (a call-as-noop mutant
--    returns no value at the call site, a single unrolling returns 4).
#guard (match runSum 256 4 0 with
        | .ok (v, hst) => v == .u64 10 && hst == HeapState.empty
        | .error _ => false)
#guard okValue? (runSum 256 0 7) == some (.u64 7)
#guard okValue? (runSum 256 10 5) == some (.u64 60)

-- 2. Too small a step budget exhausts fuel (the callee runs at the decremented fuel), and
--    every budget either exhausts or produces the right value: no wrong `.ok`.
#guard isFuelExhausted (runSum 8 4 0)
#guard isFuelExhausted (runSum 0 4 0)
#guard (List.range 64).all fun f =>
  isFuelExhausted (runSum f 4 0) || okValue? (runSum f 4 0) == some (.u64 10)
#guard (List.range 64).any fun f => okValue? (runSum f 4 0) == some (.u64 10)

/-! ### 3. Mutual recursion: `l3_even` / `l3_odd`, each under its own context -/

private def parityDecl (name other : Name) (base : UInt64) : Decl .impure :=
  let u64 := ImpureType.uint64
  let bTy := mkConst ``Bool
  let recur : Code .impure :=
    .let (mkLet 5 u64 (.lit (.uint64 1))) <|
    .let (mkLet 6 u64 (.fap ``UInt64.sub #[.fvar (fv 1), .fvar (fv 5)] rfl)) <|
    .let (mkLet 7 u64 (.fap other #[.fvar (fv 6)] rfl)) <|
    .return (fv 7)
  mkDecl name #[mkParam 1 u64] u64 <|
    .let (mkLet 3 u64 (.lit (.uint64 0))) <|
    .let (mkLet 4 bTy (.fap `UInt64.beq #[.fvar (fv 1), .fvar (fv 3)] rfl)) <|
    .cases (Cases.mk ``Bool u64 (fv 4) #[
      .ctorAlt falseCtor recur rfl,
      .ctorAlt trueCtor (.let (mkLet 8 u64 (.lit (.uint64 base))) (.return (fv 8))) rfl])

/-- `l3_even n`: 1 when `n` is even, 0 otherwise. -/
private def evenDecl : Decl .impure := parityDecl `l3_even `l3_odd 1
/-- `l3_odd n`: 1 when `n` is odd, 0 otherwise. -/
private def oddDecl : Decl .impure := parityDecl `l3_odd `l3_even 0

/-- Each declaration's OWN context knows only its partner (the driver's per-declaration
    `localCallees`); neither context knows its own name. -/
private def ctxEven : RealBridgeCtx := { arch := .x86_64, localCallees := [(`l3_odd, "odd_sym")] }
private def ctxOdd : RealBridgeCtx := { arch := .x86_64, localCallees := [(`l3_even, "even_sym")] }

private def envEO : List (Decl .impure × RealBridgeCtx) := [(evenDecl, ctxEven), (oddDecl, ctxOdd)]
private def envOE : List (Decl .impure × RealBridgeCtx) := [(oddDecl, ctxOdd), (evenDecl, ctxEven)]

#guard okValue? (evalRealLCNFDeclR envEO 256 ctxEven evenDecl [.u64 6]) == some (.u64 1)
#guard okValue? (evalRealLCNFDeclR envEO 256 ctxEven evenDecl [.u64 7]) == some (.u64 0)
#guard okValue? (evalRealLCNFDeclR envEO 256 ctxOdd oddDecl [.u64 7]) == some (.u64 1)
#guard okValue? (evalRealLCNFDeclR envOE 256 ctxEven evenDecl [.u64 6]) == some (.u64 1)
#guard okValue? (evalRealLCNFDeclR envOE 256 ctxEven evenDecl [.u64 7]) == some (.u64 0)
#guard okValue? (evalRealLCNFDeclR envOE 256 ctxOdd oddDecl [.u64 7]) == some (.u64 1)

-- Per-entry context, negative control: with `l3_odd` paired with `ctxEven` (which does not
-- map `l3_even`), the callee's own call is not `ctx`-local, so it falls to
-- `evalLetValue`, which has no rule for the name: the run errors instead of resolving.
#guard (evalRealLCNFDeclR [(evenDecl, ctxEven), (oddDecl, ctxEven)] 256 ctxEven evenDecl
          [.u64 6]).isOk == false

/-! ### 4. The empty environment is the old semantics on a call-bearing body -/

#guard exceptAgrees (evalRealLCNFDeclR [] 256 ctxSum sumDecl [.u64 4, .u64 0])
  (evalRealLCNFDecl 256 ctxSum sumDecl [.u64 4, .u64 0])
#guard (evalRealLCNFDecl 256 ctxSum sumDecl [.u64 4, .u64 0]).isOk == false
#guard exceptAgrees (evalRealLCNFDeclR [] 256 ctxSum sumDecl [.u64 0, .u64 7])
  (evalRealLCNFDecl 256 ctxSum sumDecl [.u64 0, .u64 7])
#guard (evalRealLCNFDecl 256 ctxSum sumDecl [.u64 0, .u64 7]).isOk == true
-- A lookup MISS under a `ctx`-local name keeps the old refusal (`evalStepR_localCall_miss`).
#guard (evalRealLCNFDeclR [(evenDecl, ctxEven)] 256 ctxSum sumDecl [.u64 4, .u64 0]).isOk == false

/-! ### 5. LNIR side: the lowered self-call body under `Φ = [d]` -/

private def loweredSum? : Option LNIRDecl :=
  match lowerRealLCNFDecl 256 ctxSum sumDecl "l3_sum_sym" with
  | .ok d => some d
  | .error _ => none

private def runLoweredSum (Φ : List LNIRDecl) (fuel : Nat) (d : LNIRDecl) (n acc : UInt64) :
    Except UBError (Val × HeapState) :=
  let venv := (d.params.zip [Val.u64 n, Val.u64 acc]).foldl
    (fun acc (p, val) => acc.bind p.id val) VarEnv.empty
  evalCodeR Φ fuel venv HeapState.empty d.body

#guard loweredSum?.isSome
-- The lowered body calls its own symbol, and under `Φ = [d]` it computes the source value.
#guard (match loweredSum? with
        | some d =>
          (match runLoweredSum [d] 16 d 4 0 with
           | .ok (v, hst) => v == .u64 10 && hst == HeapState.empty
           | .error _ => false)
        | none => false)
-- Fuel counts call DEPTH: `sum 4 0` nests four resolved calls, so fuel 4 suffices and
-- fuel 3 exhausts at the innermost call (`evalCodeR_call_fuel_zero`).
#guard (match loweredSum? with
        | some d => okValue? (runLoweredSum [d] 4 d 4 0) == some (.u64 10)
        | none => false)
#guard (match loweredSum? with
        | some d => isFuelExhausted (runLoweredSum [d] 3 d 4 0)
        | none => false)
-- `Φ = []` is `evalCode`, which refuses the unknown symbol.
#guard (match loweredSum? with
        | some d =>
          exceptAgrees (runLoweredSum [] 16 d 4 0)
            (evalCode 16 ((d.params.zip [Val.u64 4, Val.u64 0]).foldl
              (fun acc (p, val) => acc.bind p.id val) VarEnv.empty) HeapState.empty d.body) &&
          (runLoweredSum [] 16 d 4 0).isOk == false
        | none => false)

end LeanNative.Tests.RealLCNFRecTests
