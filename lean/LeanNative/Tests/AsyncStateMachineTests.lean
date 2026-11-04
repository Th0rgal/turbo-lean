import LeanNative.Core

set_option autoImplicit false

namespace LeanNative.Tests.AsyncStateMachineTests

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Transform

/-- Helper checking whether an `LNIRCode` tree contains any `.mkTuple` allocation. -/
def codeHasMkTuple : LNIRCode → Bool
  | .letBind _ _ (.mkTuple _) _ => true
  | .letBind _ _ _ k => codeHasMkTuple k
  | .ret _ => false
  | .incRef _ _ k => codeHasMkTuple k
  | .decRef _ _ k => codeHasMkTuple k
  | .ite _ t e => codeHasMkTuple t || codeHasMkTuple e
  | .rawStore _ _ _ _ k => codeHasMkTuple k
  | .seqFor _ _ _ _ _ _ s k => codeHasMkTuple s || codeHasMkTuple k
  | .parFor _ _ _ _ _ k => codeHasMkTuple k
  | .unreachable => false

/-- Check whether `evalCode` succeeded with exact value `v` and heap state `st`. -/
def evalOkEq (res : Except UBError (Val × HeapState)) (v : Val) (st : HeapState) : Bool :=
  match res with
  | .ok (v', st') => v' == v && st' == st
  | .error _ => false

/-- Non-escaping async frame declaration eligible for scalar register unboxing. -/
def nonEscapingFrameDecl : LNIRDecl := {
  name := "d5_unbox_frame"
  params := [{ id := 0, name := "seed", ty := .i64, borrow := false }]
  retTy := .i64
  assurance := .verifiedKernelProof
  isGpuCand := false
  body :=
    .letBind 1 .i64 (.scalar (.constU64 1))
      (.letBind 2 .i64 (.scalar (.constU64 3))
        (.letBind 3 .i64 (.scalar (.binOp .add (.var 0) (.constU64 21)))
          (.letBind 4 (.tuple [.i64, .i64, .i64]) (.mkTuple [1, 2, 3])
            (.letBind 5 .i64 (.projTuple 4 0)
              (.letBind 6 .i64 (.projTuple 4 1)
                (.letBind 7 .i64 (.projTuple 4 2)
                  (.letBind 8 .i64 (.scalar (.binOp .add (.var 5) (.var 6)))
                    (.letBind 9 .i64 (.scalar (.binOp .add (.var 8) (.var 7)))
                      (.ret 9)))))))))
}

/-- Escaping async frame declaration whose continuation returns the frame tuple directly. -/
def escapingRetFrameDecl : LNIRDecl := {
  name := "d5_escape_ret_frame"
  params := [{ id := 0, name := "seed", ty := .i64, borrow := false }]
  retTy := .tuple [.i64, .i64, .i64]
  assurance := .verifiedKernelProof
  isGpuCand := false
  body :=
    .letBind 1 .i64 (.scalar (.constU64 0))
      (.letBind 2 .i64 (.scalar (.constU64 1))
        (.letBind 3 (.tuple [.i64, .i64, .i64]) (.mkTuple [1, 2, 0])
          (.ret 3)))
}

/-- Escaping async frame declaration that projects fields 0..2 AND boxes the frame into a closure. -/
def escapingClosureFrameDecl : LNIRDecl := {
  name := "d5_escape_closure_frame"
  params := [{ id := 0, name := "seed", ty := .i64, borrow := false }]
  retTy := .objPtr
  assurance := .verifiedKernelProof
  isGpuCand := false
  body :=
    .letBind 1 .i64 (.scalar (.constU64 0))
      (.letBind 2 .i64 (.scalar (.constU64 1))
        (.letBind 3 (.tuple [.i64, .i64, .i64]) (.mkTuple [1, 2, 0])
          (.letBind 4 .i64 (.projTuple 3 0)
            (.letBind 5 .i64 (.projTuple 3 1)
              (.letBind 6 .i64 (.projTuple 3 2)
                (.letBind 7 .objPtr (.allocCtor 0 [3] [])
                  (.ret 7)))))))
}

/-- Lowered 3-await coroutine chain produced by `lowerAsyncAwaitChain`; contains intermediate
`(tag, state, payload)` `.mkTuple` frames across suspension points that `asyncStateMachinePass`
unboxes to zero `.mkTuple` allocations (`changed == true`). -/
def loweredAsyncChainDecl : LNIRDecl := {
  name := "d5_lowered_async_chain"
  params := [{ id := 0, name := "seed", ty := .i64, borrow := false }]
  retTy := .i64
  assurance := .verifiedKernelProof
  isGpuCand := false
  body := lowerAsyncAwaitChain (mkThreeStepAsyncSpec 0 10 16 5 7 9)
}

/-- Lowered bounded event-loop coroutine produced by `lowerAsyncEventLoop`; `asyncStateMachinePass`
forwards the initial `.mkTuple` frame binding directly into the `seqFor` accumulator (`changed == true`). -/
def loweredAsyncLoopDecl : LNIRDecl := {
  name := "d5_lowered_async_loop"
  params := [{ id := 0, name := "seed", ty := .i64, borrow := false }]
  retTy := .tuple [.i64, .i64, .i64]
  assurance := .verifiedKernelProof
  isGpuCand := false
  body := lowerAsyncEventLoop (mkThreeStepAsyncSpec 0 10 16 5 7 9)
}

/-- Arbitrary 4-step non-hardcoded `AsyncCoroutineSpec` testing `runSpecPolls` equivalence. -/
def fourStepCustomSpec : AsyncCoroutineSpec := {
  inputVar := 0
  initState := 10
  pollBudget := 6
  regBase := 20
  steps :=
    [ { fromState := 10, toState := 20, stepDelta := 3, outcome := .Pending }
    , { fromState := 20, toState := 30, stepDelta := 11, outcome := .Pending }
    , { fromState := 30, toState := 40, stepDelta := 13, outcome := .Pending }
    , { fromState := 40, toState := 50, stepDelta := 17, outcome := .Ready } ]
}

-- 1. Multi-yield `Pending → Pending → Ready` transitions via `evalCode 64`:
#guard evalOkEq
  (evalCode 64 (VarEnv.empty.bind 0 (.u64 10)) HeapState.empty
    (lowerAsyncEventLoop (mkThreeStepAsyncSpec 0 10 1 5 7 9)))
  (.tuple [.u64 0, .u64 1, .u64 15]) HeapState.empty

#guard evalOkEq
  (evalCode 64 (VarEnv.empty.bind 0 (.u64 10)) HeapState.empty
    (lowerAsyncEventLoop (mkThreeStepAsyncSpec 0 10 2 5 7 9)))
  (.tuple [.u64 0, .u64 2, .u64 22]) HeapState.empty

#guard evalOkEq
  (evalCode 64 (VarEnv.empty.bind 0 (.u64 10)) HeapState.empty
    (lowerAsyncEventLoop (mkThreeStepAsyncSpec 0 10 3 5 7 9)))
  (.tuple [.u64 1, .u64 3, .u64 31]) HeapState.empty

#guard evalOkEq
  (evalCode 64 (VarEnv.empty.bind 0 (.tuple [.u64 1, .u64 3, .u64 31])) HeapState.empty
    (lowerAsyncPollStep 0 10 (mkThreeStepAsyncSpec 0 10 3 5 7 9).steps))
  (.tuple [.u64 1, .u64 3, .u64 31]) HeapState.empty

-- 2. Bounded `lean-sys`-style poll loops (16+ polls) with `nextId = 0` vs heap closure `nextId > 0`:
#guard (match evalCode 64 (VarEnv.empty.bind 0 (.u64 10)) HeapState.empty
          (lowerAsyncEventLoop (mkThreeStepAsyncSpec 0 10 16 5 7 9)) with
  | .ok (.tuple [.u64 1, .u64 3, .u64 31], st) => st.nextId == 0 && st == HeapState.empty
  | _ => false)

#guard (match evalCode 64 (VarEnv.empty.bind 0 (.u64 10)) HeapState.empty
          (lowerAsyncEventLoop (mkThreeStepAsyncSpec 0 10 24 5 7 9)) with
  | .ok (.tuple [.u64 1, .u64 3, .u64 31], st) => st.nextId == 0 && st == HeapState.empty
  | _ => false)

#guard (match evalCode 64 (VarEnv.empty.bind 0 (.u64 10)) HeapState.empty
          (lowerHeapClosureAsync3 0 10 5 7 9) with
  | .ok (.u64 31, st) => st.nextId > 0 && st.nextId == 3
  | _ => false)

-- 3. `checkNonEscapingAsync` rejects escaping continuations and accepts `.projTuple`:
#guard checkNonEscapingAsync 4 (.ret 4) == false
#guard checkNonEscapingAsync 4 (.letBind 5 .objPtr (.allocCtor 0 [4] []) (.ret 5)) == false
#guard checkNonEscapingAsync 4 (.letBind 5 .i64 (.call "spawn_task" [4] .i64) (.ret 5)) == false
#guard checkNonEscapingAsync 4
    (.letBind 5 (.tuple [.i64, .i64]) (.mkTuple [4, 0]) (.ret 5)) == false
#guard checkNonEscapingAsync 4
    (.letBind 5 .i64 (.projTuple 4 0)
      (.letBind 6 .i64 (.projTuple 4 2)
        (.letBind 7 .i64 (.scalar (.binOp .add (.var 5) (.var 6)))
          (.ret 7)))) == true

-- 4. `optimizeAsyncStateMachine` / `asyncStateMachinePass` unbox non-escaping 3-tuple frames:
#guard codeHasMkTuple nonEscapingFrameDecl.body == true
#guard codeHasMkTuple (optimizeAsyncStateMachine nonEscapingFrameDecl.body) == false
#guard (let (d', cert) := asyncStateMachinePass.runDecl nonEscapingFrameDecl
        cert.changed == true && codeHasMkTuple d'.body == false &&
        evalOkEq (evalCode 64 (VarEnv.empty.bind 0 (.u64 10)) HeapState.empty d'.body)
          (.u64 35) HeapState.empty &&
        evalOkEq (evalCode 64 (VarEnv.empty.bind 0 (.u64 10)) HeapState.empty
          nonEscapingFrameDecl.body) (.u64 35) HeapState.empty)

#guard (let (d', cert) := asyncStateMachinePass.runDecl escapingRetFrameDecl
        cert.changed == false && d'.body == escapingRetFrameDecl.body)

#guard (let (d', cert) := asyncStateMachinePass.runDecl escapingClosureFrameDecl
        cert.changed == false && d'.body == escapingClosureFrameDecl.body)

-- 5. The verified kernel contract is registered and its emitted certificate verifies:
#guard LeanNative.Proofs.isRegisteredTheorem verifiedAsyncStateMachineContract.theoremRef == true
#guard LeanNative.Proofs.isRegisteredTheorem "LeanNative.Proofs.asyncStateMachinePass_sound" == true
#guard (LeanNative.Proofs.verifySingleCert
  { passName := "AsyncStateMachine", declName := "d5_unbox_frame",
    inputHash := "h1", outputHash := "h2", changed := true,
    assurance := .verifiedKernelProof,
    theoremRef := "LeanNative.Proofs.unregistered_fake_theorem", notes := "" }).1 == false

#guard (let (d', cert) := asyncStateMachinePass.runDecl nonEscapingFrameDecl
        let optCert : LeanNative.Proofs.OptimizationCert := {
          passName := cert.passName, declName := cert.declName,
          inputHash := cert.inputHash, outputHash := cert.outputHash,
          changed := cert.changed, assurance := cert.assurance,
          theoremRef := cert.theoremRef, notes := cert.notes }
        let res := LeanNative.Proofs.verifySingleCert optCert
        cert.changed == true && codeHasMkTuple d'.body == false &&
          res.1 == true && res.2 == [])

#guard (let (m', stepCerts) := runVerifiedKernelPipeline
          { moduleName := "d5_async_pipeline_test", decls := [nonEscapingFrameDecl] }
        let optCerts := stepCerts.map fun c => ({
          passName := c.passName, declName := c.declName,
          inputHash := c.inputHash, outputHash := c.outputHash,
          changed := c.changed, assurance := c.assurance,
          theoremRef := c.theoremRef, notes := c.notes } : LeanNative.Proofs.OptimizationCert)
        let rep := LeanNative.Proofs.verifyModuleCerts "d5_async_pipeline_test" optCerts
        rep.verified == true && rep.errors == [] &&
          rep.overallAssurance == .verifiedKernelProof &&
          optCerts.any (fun c => c.passName == "AsyncStateMachine" && c.changed == true) &&
          (match m'.decls with | [d'] => codeHasMkTuple d'.body == false | _ => false))

-- 6. `asyncStateMachinePass` genuinely fires (`changed == true`) on lowered async coroutines/chains:
#guard codeHasMkTuple loweredAsyncChainDecl.body == true
#guard (asyncStateMachinePass.runDecl loweredAsyncChainDecl).2.changed == true
#guard (let (d', cert) := asyncStateMachinePass.runDecl loweredAsyncChainDecl
        let optCert : LeanNative.Proofs.OptimizationCert := {
          passName := cert.passName, declName := cert.declName,
          inputHash := cert.inputHash, outputHash := cert.outputHash,
          changed := cert.changed, assurance := cert.assurance,
          theoremRef := cert.theoremRef, notes := cert.notes }
        let res := LeanNative.Proofs.verifySingleCert optCert
        cert.changed == true && codeHasMkTuple d'.body == false &&
          res.1 == true && res.2 == [] &&
          evalOkEq (evalCode 64 (VarEnv.empty.bind 0 (.u64 10)) HeapState.empty d'.body)
            (.u64 31) HeapState.empty &&
          evalOkEq (evalCode 64 (VarEnv.empty.bind 0 (.u64 10)) HeapState.empty
            loweredAsyncChainDecl.body) (.u64 31) HeapState.empty)

#guard (asyncStateMachinePass.runDecl loweredAsyncLoopDecl).2.changed == true
#guard (let (d', cert) := asyncStateMachinePass.runDecl loweredAsyncLoopDecl
        let optCert : LeanNative.Proofs.OptimizationCert := {
          passName := cert.passName, declName := cert.declName,
          inputHash := cert.inputHash, outputHash := cert.outputHash,
          changed := cert.changed, assurance := cert.assurance,
          theoremRef := cert.theoremRef, notes := cert.notes }
        let res := LeanNative.Proofs.verifySingleCert optCert
        cert.changed == true && res.1 == true && res.2 == [] &&
          evalOkEq (evalCode 64 (VarEnv.empty.bind 0 (.u64 10)) HeapState.empty d'.body)
            (.tuple [.u64 1, .u64 3, .u64 31]) HeapState.empty)

-- 7. General `lowerAsyncEventLoop` matches `asyncFrameVal (runSpecPolls ...)` on arbitrary 4-step spec:
#guard evalOkEq
  (evalCode 64 (VarEnv.empty.bind 0 (.u64 100)) HeapState.empty
    (lowerAsyncEventLoop fourStepCustomSpec))
  (asyncFrameVal (runSpecPolls fourStepCustomSpec fourStepCustomSpec.pollBudget 100))
  HeapState.empty
#guard asyncFrameVal (runSpecPolls fourStepCustomSpec fourStepCustomSpec.pollBudget 100) ==
  .tuple [.u64 1, .u64 50, .u64 144]

-- 8. All new/updated D5 theorems are registered in `verifiedTheoremRegistry`:
#guard LeanNative.Proofs.isRegisteredTheorem "LeanNative.Proofs.lowerAsyncEventLoop_sound" == true
#guard LeanNative.Proofs.isRegisteredTheorem "LeanNative.Proofs.lowerAsyncEventLoop_threeStep_sound" == true
#guard LeanNative.Proofs.isRegisteredTheorem "LeanNative.Proofs.lowerAsyncPollStep_spec_sound" == true
#guard LeanNative.Proofs.isRegisteredTheorem "LeanNative.Proofs.lowerAsyncAwaitChain_sound" == true
#guard LeanNative.Proofs.isRegisteredTheorem "LeanNative.Transform.optimizeAsyncStateMachine_refines" == true

end LeanNative.Tests.AsyncStateMachineTests
