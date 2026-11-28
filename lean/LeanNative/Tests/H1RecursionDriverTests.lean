import LeanNative.IR.Bridge
import LeanNative.IR.RealLCNFSemantics
import LeanNative.Semantics.Eval
import LeanNative.Transform.LoopVectorizeOpt
import LeanNative.Backend.LLVM

/-!
# H1-WIRE: the production driver ingests recursive modules

`ingestModuleDecls` used to reject any call cycle. Its call-graph gate now checks only what
`H1.ModuleCallees` needs: every callee is a module symbol and symbols are unique. A mutually
recursive module therefore reaches `lowerRealLCNFModule`, which `H1.recRefinement` proves at every
call depth. Each run below goes through elaboration, the compiler's LCNF pipeline, the driver, and
the `LNIR` call table `recFuncTable`. The optimized module must also emit mutually calling
LLVM functions.

Direct self-recursion is still refused per declaration by `codeHasSelfTailCall` in
`ingestImpureDeclViaReal` (`BridgeHelpers/RealBridgeCtxAndSlices.lean`). `checkSelfRecGate` pins
that refusal, so lifting it flips this test.
-/

namespace LeanNative.Tests.H1RecursionDriver

open Lean Lean.Compiler.LCNF
open LeanNative.IR LeanNative.Semantics
open LeanNative.IR.RealLCNFBridge LeanNative.IR.RealLCNFSemantics

/-- Non-tail self-recursion: `w1dSumDown n = n + (n - 1) + ... + 1`. -/
@[noinline] partial def w1dSumDown (x : UInt64) : UInt64 :=
  if x == 0 then 0 else x + w1dSumDown (x - 1)

mutual
/-- Mutual recursion between two declarations, each tail-calling the other. -/
@[noinline] partial def w1dIsEven (x : UInt64) : UInt64 :=
  if x == 0 then 1 else w1dIsOdd (x - 1)

@[noinline] partial def w1dIsOdd (x : UInt64) : UInt64 :=
  if x == 0 then 0 else w1dIsEven (x - 1)
end

def hasSubstr (s pat : String) : Bool := (s.splitOn pat).length > 1

/-- Run the declaration whose symbol contains `pat` in the lowered module's depth-`depth` table. -/
def runIngested (m : LNIRModule) (pat : String) (depth : Nat) (args : List Val) : Option Val :=
  match m.decls.find? (hasSubstr ·.name pat) with
  | none => none
  | some d =>
    match evalDeclWith 256 (recFuncTable 256 m.decls depth) d args .empty with
    | .ok (v, _) => some v
    | .error _ => none

def checkRecursiveDriver : CoreM Unit := do
  let m ← ingestModuleDecls #[``w1dIsEven, ``w1dIsOdd] "H1RecursionDriver"
  let runs := [
    (runIngested m "w1dIsEven" 16 [.u64 4], some (Val.u64 1)),
    (runIngested m "w1dIsEven" 16 [.u64 7], some (Val.u64 0)),
    (runIngested m "w1dIsOdd" 16 [.u64 7], some (Val.u64 1)),
    -- depth-indexed: a run needing more nested calls than the depth fails instead of looping
    (runIngested m "w1dIsEven" 2 [.u64 64], none)]
  for (got, want) in runs do
    unless got == want do
      throwError s!"recursive driver run: got {repr got}, expected {repr want}"
  let (opt, _) := LeanNative.Transform.runDefaultPipeline m
  let ir := LeanNative.Backend.LLVM.emitLLVMModule true opt
  let sym (pat : String) := (opt.decls.find? (hasSubstr ·.name pat)).map (·.name)
  let (some ev, some od) := (sym "w1dIsEven", sym "w1dIsOdd")
    | throwError "optimized module lost a mutually recursive declaration"
  for (caller, callee) in [(ev, od), (od, ev)] do
    let defined := hasSubstr ir s!"define dso_local i64 @{caller}("
    unless defined && hasSubstr ir s!"call i64 @{callee}(" do
      throwError s!"LLVM module lacks `{caller}` calling `{callee}`"

def checkSelfRecGate : CoreM Unit := do
  let r ← tryCatch (some <$> ingestModuleDecls #[``w1dSumDown] "H1SelfRec") fun _ => pure none
  if r.isSome then throwError "self-recursion now ingests: replace this pin with a run"

#eval checkSelfRecGate

#eval checkRecursiveDriver

/-! ## Source semantics: a recursive join point unfolds once per jump, spending fuel -/

def fv (n : Nat) : FVarId := ⟨.num `w1d n⟩

def u64Param (n : Nat) : Param .impure :=
  { fvarId := fv n, binderName := .num `p n, type := ImpureType.uint64, borrow := false }

/-- `jp loop (y) := jmp loop y` then `jmp loop x`, rejected by the lowerer, run by the semantics -/
def loopDecl : Decl .impure :=
  { name := `w1d_loop, levelParams := [], type := ImpureType.uint64, inlineAttr? := none
    params := #[u64Param 1]
    value := .code <| .jp ⟨fv 10, `loop, #[u64Param 11], ImpureType.uint64,
      .jmp (fv 10) #[.fvar (fv 11)]⟩ (.jmp (fv 10) #[.fvar (fv 1)]) }

def loopCtx : RealBridgeCtx := { paramTypeMap := [(fv 1, .i64)] }

-- The lowerer still fails closed on the recursive join point.
#guard (lowerRealLCNFDecl 64 loopCtx loopDecl "w1d_loop").isOk == false

def isFuelExhausted : Except UBError (Val × HeapState) → Bool
  | .error .fuelExhausted => true
  | _ => false

-- The source semantics runs it: the non-terminating loop spends all its fuel.
#guard isFuelExhausted (evalRealLCNFDecl 64 loopCtx loopDecl [.u64 3] .empty)

def u64Let (n : Nat) (value : LetValue .impure) : LetDecl .impure :=
  { fvarId := fv n, binderName := .num `v n, type := ImpureType.uint64, value }

def boolAlt (cidx : Nat) (k : Code .impure) : Alt .impure :=
  let name := if cidx == 0 then ``Bool.false else ``Bool.true
  .ctorAlt { name, cidx, size := 0, usize := 0, ssize := 0 } k rfl

/-- `jp loop (y acc) := if y == 0 then acc else jmp loop (y - 1) (acc + 2)` then `jmp loop x x`. -/
def countDecl : Decl .impure :=
  let isZero : LetDecl .impure :=
    { fvarId := fv 13, binderName := `c, type := mkConst ``Bool
      value := .fap ``UInt64.decEq #[.fvar (fv 11), .fvar (fv 14)] rfl }
  let step : Code .impure :=
    .let (u64Let 15 (.lit (.uint64 1))) <|
    .let (u64Let 16 (.fap ``UInt64.sub #[.fvar (fv 11), .fvar (fv 15)] rfl)) <|
    .let (u64Let 17 (.lit (.uint64 2))) <|
    .let (u64Let 18 (.fap ``UInt64.add #[.fvar (fv 12), .fvar (fv 17)] rfl)) <|
    .jmp (fv 10) #[.fvar (fv 16), .fvar (fv 18)]
  let body : Code .impure :=
    .let (u64Let 14 (.lit (.uint64 0))) <| .let isZero <|
    .cases (Cases.mk ``Bool ImpureType.uint64 (fv 13)
      #[boolAlt 0 step, boolAlt 1 (.return (fv 12))])
  { name := `w1d_count, levelParams := [], type := ImpureType.uint64, inlineAttr? := none
    params := #[u64Param 1]
    value := .code <| .jp ⟨fv 10, `loop, #[u64Param 11, u64Param 12], ImpureType.uint64, body⟩
      (.jmp (fv 10) #[.fvar (fv 1), .fvar (fv 1)]) }

-- A terminating recursive join point: three unfoldings give `3 + 2 * 3 = 9`.
#guard match evalRealLCNFDecl 64 loopCtx countDecl [.u64 3] .empty with
  | .ok (v, st) => v == .u64 9 && st == .empty
  | .error _ => false

-- Too little fuel for the same loop fails with `fuelExhausted`, never a partial `.ok`.
#guard isFuelExhausted (evalRealLCNFDecl 8 loopCtx countDecl [.u64 3] .empty)

-- The lowerer still rejects the terminating loop too.
#guard (lowerRealLCNFDecl 64 loopCtx countDecl "w1d_count").isOk == false

end LeanNative.Tests.H1RecursionDriver
