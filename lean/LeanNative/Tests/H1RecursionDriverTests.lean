import LeanNative.IR.Bridge
import LeanNative.IR.RealLCNFSemantics
import LeanNative.Semantics.Eval

/-!
# H1-WIRE: the production driver ingests recursive modules

`ingestModuleDecls` used to reject any call cycle. Its call-graph gate now checks only what
`H1.ModuleCallees` needs: every callee is a module symbol and symbols are unique. A mutually
recursive module therefore reaches `lowerRealLCNFModule`, which `H1.recRefinement` proves at every
call depth. Each run below goes through elaboration, the compiler's LCNF pipeline, the driver, and
the `LNIR` call table `recFuncTable`.

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

-- The source semantics no longer rejects it up front: the loop runs until fuel is exhausted.
#guard match evalRealLCNFDecl 64 loopCtx loopDecl [.u64 3] .empty with
  | .error (.unsupportedCall msg) => !hasSubstr msg "recursive join point"
  | _ => true

end LeanNative.Tests.H1RecursionDriver
