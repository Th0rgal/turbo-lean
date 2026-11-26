import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.ToImpureType
import LeanNative.IR.RealLCNFBridge
import LeanNative.IR.RealLCNFRecSemantics
import LeanNative.IR.RealLCNFCallSemantics
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
   `Δ`, each callee under its OWN paired context; a callee paired with the wrong context
   ends on the exact old refusal.
4. `Δ = [] / Φ = []` runs agree EXACTLY with the old evaluators on a call-bearing body
   (`exceptAgrees` compares values, heaps and errors with their own `BEq`; the kernel
   theorems `evalStepR_nil` / `evalCodeR_nil` carry the same equality for every input),
   and a lookup miss ends on the old `.unsupportedCall` refusal by name.
5. An `evalCodeR` run of the LOWERED self-call body under `Φ = [d]` produces the source
   result; the LNIR call budget counts call DEPTH, so too little fuel is
   `.error .fuelExhausted`, an argument-count mismatch in either direction ends on the
   exact arity error (strict arity, as L2's `evalCodeF`), and the empty environment keeps
   the old refusal.
6. A HEAP-typed local-call result (contract amendment 3): a callee returns a fresh
   object, the caller `dec`s it. The source R-run, L2's F-run and the lowered LNIR run
   agree exactly on value and heap, so the object is freed on every side. Under the
   pre-amendment rule, which stored the result at `.i64`, the source `dec` was a no-op
   and these guards failed with the object live.
7. Repeated names: with two LNIR entries named `f`, L2's strict-suffix lookup resolves
   the nested call to the second entry and returns its value, while the full-environment
   lookup re-resolves to the first entry and ends on the call budget at every fuel —
   why the F-to-R embedding the contract states for the fold needs distinct names.
8. Entry fuel: L2 runs a callee at its entry's own fuel, R at the caller's remaining step
   budget, so at a budget that fits the caller's steps and not the callee's, the F-run
   succeeds and the R-run ends on the budget — why that embedding needs a fuel bound.
-/

namespace LeanNative.Tests.RealLCNFRecTests

open Lean
open Lean.Compiler.LCNF
open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

/-- Exact result agreement: values, heaps and errors each compared with their own `BEq`
    (`UBError` derives it). -/
private def exceptAgrees : Except UBError (Val × HeapState) → Except UBError (Val × HeapState) → Bool
  | .ok (v1, h1), .ok (v2, h2) => v1 == v2 && h1 == h2
  | .error e1, .error e2 => e1 == e2
  | _, _ => false

/-- The run ended on the old semantics' refusal of an unresolved call to `fn`. -/
private def isUnsupportedCall (fn : String) : Except UBError (Val × HeapState) → Bool
  | .error (.unsupportedCall s) => s == fn
  | _ => false

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
-- `evalLetValue`, which refuses the name: the run ends on that refusal instead of
-- resolving.
#guard isUnsupportedCall "l3_even"
  (evalRealLCNFDeclR [(evenDecl, ctxEven), (oddDecl, ctxEven)] 256 ctxEven evenDecl [.u64 6])

/-! ### 4. The empty environment is the old semantics on a call-bearing body -/

#guard exceptAgrees (evalRealLCNFDeclR [] 256 ctxSum sumDecl [.u64 4, .u64 0])
  (evalRealLCNFDecl 256 ctxSum sumDecl [.u64 4, .u64 0])
#guard isUnsupportedCall "l3_sum" (evalRealLCNFDecl 256 ctxSum sumDecl [.u64 4, .u64 0])
#guard exceptAgrees (evalRealLCNFDeclR [] 256 ctxSum sumDecl [.u64 0, .u64 7])
  (evalRealLCNFDecl 256 ctxSum sumDecl [.u64 0, .u64 7])
#guard (evalRealLCNFDecl 256 ctxSum sumDecl [.u64 0, .u64 7]).isOk == true
-- A lookup MISS under a `ctx`-local name keeps the old refusal (`evalStepR_localCall_miss`).
#guard isUnsupportedCall "l3_sum"
  (evalRealLCNFDeclR [(evenDecl, ctxEven)] 256 ctxSum sumDecl [.u64 4, .u64 0])

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
-- Strict arity, as L2's `evalCodeF`, pinned in both directions with the exact error.
-- Too many: TWO arguments to a one-parameter callee error instead of the extra one being
-- dropped.
private def idL : LNIRDecl :=
  { name := "id_sym", params := [{ id := 0, name := "x", ty := .i64 }], retTy := .i64,
    body := .ret 0 }
#guard (match evalCodeR [idL] 8 (VarEnv.empty.bind 0 (.u64 5)) HeapState.empty
          (.letBind 1 .i64 (.call "id_sym" [0, 0] .i64 false) (.ret 1)) with
        | .error (.typeError s) => s == "call arity mismatch"
        | _ => false)
#guard okValue? (evalCodeR [idL] 8 (VarEnv.empty.bind 0 (.u64 5)) HeapState.empty
          (.letBind 1 .i64 (.call "id_sym" [0] .i64 false) (.ret 1))) == some (.u64 5)
-- Too few: ONE argument to a two-parameter callee whose body reads only the first one
-- errors too. The callee would succeed with the second parameter unbound, so this case
-- pins the check where a callee reading its only parameter cannot (that one errors on
-- the unbound variable either way), and it kills a `≤` mutant the too-many case passes.
private def fstL : LNIRDecl :=
  { name := "fst_sym",
    params := [{ id := 0, name := "x", ty := .i64 }, { id := 1, name := "y", ty := .i64 }],
    retTy := .i64, body := .ret 0 }
#guard (match evalCodeR [fstL] 8 (VarEnv.empty.bind 0 (.u64 5)) HeapState.empty
          (.letBind 1 .i64 (.call "fst_sym" [0] .i64 false) (.ret 1)) with
        | .error (.typeError s) => s == "call arity mismatch"
        | _ => false)
#guard okValue? (evalCodeR [fstL] 8 (VarEnv.empty.bind 0 (.u64 5)) HeapState.empty
          (.letBind 1 .i64 (.call "fst_sym" [0, 0] .i64 false) (.ret 1))) == some (.u64 5)
-- `Φ = []` is `evalCode`, which refuses the unknown symbol.
#guard (match loweredSum? with
        | some d =>
          exceptAgrees (runLoweredSum [] 16 d 4 0)
            (evalCode 16 ((d.params.zip [Val.u64 4, Val.u64 0]).foldl
              (fun acc (p, val) => acc.bind p.id val) VarEnv.empty) HeapState.empty d.body) &&
          (runLoweredSum [] 16 d 4 0).isOk == false
        | none => false)

/-! ### 6. A heap-typed local-call result: every run frees the object the caller drops -/

/-- `l3_mk x = ObjBox.left (box x)`: returns a fresh heap object. -/
private def mkHeapDecl : Decl .impure :=
  let obj := ImpureType.object
  let u64 := ImpureType.uint64
  let ci : CtorInfo := { name := `ObjBox.left, cidx := 0, size := 1, usize := 0, ssize := 0 }
  mkDecl `l3_mk #[mkParam 1 u64] obj <|
    .let (mkLet 3 obj (.box u64 (fv 1) rfl)) <|
    .let (mkLet 4 obj (.ctor ci #[.fvar (fv 3)] rfl)) <|
    .return (fv 4)

/-- `l3_use x = let o := l3_mk x; dec o; 0`: the caller drops the object it received. -/
private def useHeapDecl : Decl .impure :=
  let obj := ImpureType.object
  let u64 := ImpureType.uint64
  mkDecl `l3_use #[mkParam 1 u64] u64 <|
    .let (mkLet 2 obj (.fap `l3_mk #[.fvar (fv 1)] rfl)) <|
    .dec (fv 2) 1 true false none (
      .let (mkLet 5 u64 (.lit (.uint64 0))) <|
      .return (fv 5)) rfl

private def boxLayout : RcCtorLayoutSpec :=
  { ctorName := `ObjBox.left, cidx := 0, objSlots := 1, usizeSlots := 0, scalarSlots := [] }

/-- One context for both declarations: heap lowering on, the constructor's layout, and
    the callee mapped as local. -/
private def ctxHeap : RealBridgeCtx :=
  { arch := .x86_64, allowStage1DHeap := true, ctorLayouts := [(`ObjBox.left, boxLayout)],
    localCallees := [(`l3_mk, "mk_sym")] }

/-- The source run under the recursion-capable semantics, the callee in `Δ`. -/
private def heapRunR : Except UBError (Val × HeapState) :=
  evalRealLCNFDeclR [(mkHeapDecl, ctxHeap)] 64 ctxHeap useHeapDecl [.u64 5]

/-- The same module under L2's `evalStepF` (the callee's entry carries its fuel). -/
private def heapRunF : Except UBError (Val × HeapState) :=
  evalRealLCNFDeclF [(mkHeapDecl, ctxHeap, 64)] 64 ctxHeap useHeapDecl [.u64 5]

/-- The lowered caller under `Φ = [the lowered callee]`, entered with the same argument. -/
private def heapRunLowered : Except UBError (Val × HeapState) :=
  match lowerRealLCNFDecl 64 ctxHeap mkHeapDecl "mk_sym",
        lowerRealLCNFDecl 64 ctxHeap useHeapDecl "use_sym" with
  | .ok dm, .ok du =>
    evalCodeR [dm] 64 ((du.params.zip [Val.u64 5]).foldl
      (fun acc (p, val) => acc.bind p.id val) VarEnv.empty) HeapState.empty du.body
  | _, _ => .error (.typeError "fixture lowering failed")

-- The caller's `dec` frees the object it received, so the source run ends with no live
-- heap object. Before amendment 3 the local-call rule stored the result at `.i64`, the
-- `dec` was a no-op on a non-heap variable, and this guard failed with the object live.
#guard (match heapRunR with
        | .ok (v, hst) => v == .u64 0 && hst.heapObjs.isEmpty
        | .error _ => false)
-- The lowered run frees it too, and agrees with the source run exactly (value and heap);
-- so does L2's run of the same module.
#guard heapRunLowered.isOk
#guard exceptAgrees heapRunR heapRunLowered
#guard exceptAgrees heapRunR heapRunF

/-! ### 7. Repeated names: why the F-to-R embedding needs distinct names -/

/-- Two LNIR entries with ONE name `f`: the first calls `f`, the second returns 7. -/
private def fOuter : LNIRDecl :=
  { name := "f", params := [], retTy := .i64,
    body := .letBind 0 .i64 (.call "f" [] .i64 false) (.ret 0) }
private def fInner : LNIRDecl :=
  { name := "f", params := [], retTy := .i64,
    body := .letBind 0 .i64 (.scalar (.constU64 7)) (.ret 0) }
private def callF : LNIRCode := .letBind 1 .i64 (.call "f" [] .i64 false) (.ret 1)

-- L2's strict-suffix lookup resolves the outer entry's nested call to the inner entry.
#guard okValue? (evalCodeF [(fOuter, 8), (fInner, 8)] 8 VarEnv.empty HeapState.empty callF)
  == some (.u64 7)
-- The full-environment lookup re-resolves every nested call to the first entry, so no
-- budget reproduces the F result: every run ends on the call budget.
#guard (List.range 40).all fun f =>
  isFuelExhausted (evalCodeR [fOuter, fInner] f VarEnv.empty HeapState.empty callF)

/-! ### 8. Entry fuel: why the F-to-R embedding needs a fuel bound -/

/-- `l3_inc3 x = x + 1 + 1 + 1`: five steps, no calls. -/
private def inc3Decl : Decl .impure :=
  let u64 := ImpureType.uint64
  mkDecl `l3_inc3 #[mkParam 1 u64] u64 <|
    .let (mkLet 2 u64 (.lit (.uint64 1))) <|
    .let (mkLet 3 u64 (.fap ``UInt64.add #[.fvar (fv 1), .fvar (fv 2)] rfl)) <|
    .let (mkLet 4 u64 (.fap ``UInt64.add #[.fvar (fv 3), .fvar (fv 2)] rfl)) <|
    .let (mkLet 5 u64 (.fap ``UInt64.add #[.fvar (fv 4), .fvar (fv 2)] rfl)) <|
    .return (fv 5)

/-- `l3_top x = l3_inc3 x`: two steps of its own around one local call. -/
private def topDecl : Decl .impure :=
  let u64 := ImpureType.uint64
  mkDecl `l3_top #[mkParam 1 u64] u64 <|
    .let (mkLet 6 u64 (.fap `l3_inc3 #[.fvar (fv 1)] rfl)) <|
    .return (fv 6)

private def ctxTop : RealBridgeCtx :=
  { arch := .x86_64, localCallees := [(`l3_inc3, "inc3_sym")] }
private def ctxInc3 : RealBridgeCtx := { arch := .x86_64 }

-- At step budget 3 the caller's own steps fit and the callee's do not: L2 runs the callee
-- at its entry fuel (64) and succeeds; R runs it at the caller's remaining budget and ends
-- on it. With budget to spare R computes the same value.
#guard okValue? (evalRealLCNFDeclF [(inc3Decl, ctxInc3, 64)] 3 ctxTop topDecl [.u64 5])
  == some (.u64 8)
#guard isFuelExhausted (evalRealLCNFDeclR [(inc3Decl, ctxInc3)] 3 ctxTop topDecl [.u64 5])
#guard okValue? (evalRealLCNFDeclR [(inc3Decl, ctxInc3)] 64 ctxTop topDecl [.u64 5])
  == some (.u64 8)

end LeanNative.Tests.RealLCNFRecTests
