import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.Transform.Pass
import LeanNative.Transform.UnboxTupleSROA
import LeanNative.Proofs.SymbolicTVRefinesDeadSoundness

set_option autoImplicit false

namespace LeanNative.Transform

open LeanNative.IR
open LeanNative.Semantics

/-! ## D5: Zero-Alloc Stackless Async State Machine

A coroutine is a non-escaping `(pollTag, stateWord, payloadWord)` triple.
`lowerAsyncPollStep` dispatches on the state word with `ite`; `Ready` (`tag = 1`)
is idempotent. `lowerAsyncEventLoop` wraps that step in a bounded `seqFor`.
The heap-closure baseline `.allocCtor`s once per poll. `optimizeAsyncStateMachine`
unboxes a non-escaping 3-tuple frame into three scalar bindings.
-/

/-- Outcome of one stackless poll (`Pending = 0`, `Ready = 1`). -/
inductive AsyncPollResult where
  | Pending
  | Ready
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Unboxed `u64` tag (`0` = `Pending`, `1` = `Ready`). -/
def AsyncPollResult.tagBits (r : AsyncPollResult) : UInt64 :=
  match r with
  | .Pending => 0
  | .Ready => 1

/-- One yield arm: when `Pending` at `fromState`, advance to `toState`,
add `stepDelta` into the payload, and yield `outcome`. -/
structure AsyncStep where
  fromState : Nat
  toState : Nat
  stepDelta : UInt64
  outcome : AsyncPollResult
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Non-escaping coroutine: payload lives in `inputVar`, SSA scratch starts at
`regBase`, and `steps` run for at most `pollBudget` polls from `initState`. -/
structure AsyncCoroutineSpec where
  inputVar : VarId
  initState : Nat
  pollBudget : Nat
  regBase : VarId
  steps : List AsyncStep
  deriving Repr, DecidableEq, Inhabited, BEq

/-- True when `cont` is stored, returned, aliased, or passed to a call.
A `.projTuple` of `cont` is a local read and does not escape. -/
def asyncExprEscapes (cont : VarId) (e : LNIRExpr) : Bool :=
  match e with
  | .projTuple _ _ => false
  | _ => exprUsesVar cont e

/-- True when `cont` escapes `code` (including through a binding of `cont`). -/
def asyncCodeEscapes (cont : VarId) : LNIRCode → Bool
  | .letBind _ _ val k => asyncExprEscapes cont val || asyncCodeEscapes cont k
  | .ret r => r == cont
  | .incRef o _ k => o == cont || asyncCodeEscapes cont k
  | .decRef o _ k => o == cont || asyncCodeEscapes cont k
  | .ite c t e => c == cont || asyncCodeEscapes cont t || asyncCodeEscapes cont e
  | .rawStore p i x _ k =>
    p == cont || i == cont || x == cont || asyncCodeEscapes cont k
  | .seqFor iv lo hi acc init _ s k =>
    lo == cont || hi == cont || init == cont ||
      (iv != cont && acc != cont && asyncCodeEscapes cont s) ||
      (acc != cont && asyncCodeEscapes cont k)
  | .parFor ov len ins _ kern k =>
    len == cont || ins.contains cont || kernelUsesVar cont kern ||
      (ov != cont && asyncCodeEscapes cont k)
  | .unreachable => false

/-- Accept `code` only when continuation `cont` never escapes. -/
def checkNonEscapingAsync (cont : VarId) (code : LNIRCode) : Bool :=
  !asyncCodeEscapes cont code

/-- Nested state dispatch. `fallback` runs when no arm matches `stV`. -/
def lowerAsyncStepArms (stV valV armBase : VarId) (steps : List AsyncStep)
    (fallback : LNIRCode) : LNIRCode :=
  match steps with
  | [] => fallback
  | step :: rest =>
    let condV := armBase
    let nTagV := armBase + 1
    let nStV := armBase + 2
    let nValV := armBase + 3
    let outFrmV := armBase + 4
    .letBind condV .i1
      (.scalar (.binOp .eq (.var stV) (.constU64 step.fromState.toUInt64)))
      (.ite condV
        (.letBind nTagV .i64 (.scalar (.constU64 step.outcome.tagBits))
          (.letBind nStV .i64 (.scalar (.constU64 step.toState.toUInt64))
            (.letBind nValV .i64
              (.scalar (.binOp .add (.var valV) (.constU64 step.stepDelta)))
              (.letBind outFrmV (.tuple [.i64, .i64, .i64])
                (.mkTuple [nTagV, nStV, nValV])
                (.ret outFrmV)))))
        (lowerAsyncStepArms stV valV (armBase + 5) rest fallback))

/-- One poll of the flat machine. `frameVar` holds `(tag, state, payload)`.
When `tag = 1` the frame is returned unchanged (`Ready` is idempotent).
Scratch starts at `base`; every bound id is `≥ base`. -/
def lowerAsyncPollStep (frameVar base : VarId) (steps : List AsyncStep) : LNIRCode :=
  let tagV := base
  let stV := base + 1
  let valV := base + 2
  let doneV := base + 3
  .letBind tagV .i64 (.projTuple frameVar 0)
    (.letBind stV .i64 (.projTuple frameVar 1)
      (.letBind valV .i64 (.projTuple frameVar 2)
        (.letBind doneV .i1
          (.scalar (.binOp .eq (.var tagV) (.constU64 1)))
          (.ite doneV (.ret frameVar)
            (lowerAsyncStepArms stV valV (base + 4) steps (.ret frameVar))))))

/-- Bounded lean-sys poll loop. Returns the final `(tag, state, payload)` tuple.
Scratch starts at `spec.regBase`; the loop accumulator is `regBase + 6`. -/
def lowerAsyncEventLoop (spec : AsyncCoroutineSpec) : LNIRCode :=
  let b := spec.regBase
  let loVar := b
  let hiVar := b + 1
  let initTagV := b + 2
  let initStV := b + 3
  let initFrmV := b + 4
  let idxVar := b + 5
  let accVar := b + 6
  .letBind loVar .i64 (.scalar (.constU64 0))
    (.letBind hiVar .i64 (.scalar (.constU64 spec.pollBudget.toUInt64))
      (.letBind initTagV .i64 (.scalar (.constU64 (AsyncPollResult.Pending.tagBits)))
        (.letBind initStV .i64 (.scalar (.constU64 spec.initState.toUInt64))
          (.letBind initFrmV (.tuple [.i64, .i64, .i64])
            (.mkTuple [initTagV, initStV, spec.inputVar])
            (.seqFor idxVar loVar hiVar accVar initFrmV (.tuple [.i64, .i64, .i64])
              (lowerAsyncPollStep accVar (b + 7) spec.steps)
              (.ret accVar))))))

/-- Three-step `Pending → Pending → Ready` coroutine used by the zero-alloc witness. -/
def mkThreeStepAsyncSpec (inputVar regBase pollBudget : Nat)
    (d0 d1 d2 : UInt64) : AsyncCoroutineSpec :=
  { inputVar := inputVar
  , initState := 0
  , pollBudget := pollBudget
  , regBase := regBase
  , steps :=
      [ { fromState := 0, toState := 1, stepDelta := d0, outcome := .Pending }
      , { fromState := 1, toState := 2, stepDelta := d1, outcome := .Pending }
      , { fromState := 2, toState := 3, stepDelta := d2, outcome := .Ready } ] }

/-- Heap-closure baseline: one `.allocCtor` plus `.decRef` per poll.
Three polls allocate three objects and return the same payload sum. -/
def lowerHeapClosureAsync3 (initVar base : VarId) (d0 d1 d2 : UInt64) : LNIRCode :=
  let c0 := base
  let p0 := base + 1
  let v0 := base + 2
  let c1 := base + 3
  let p1 := base + 4
  let v1 := base + 5
  let c2 := base + 6
  let p2 := base + 7
  let v2 := base + 8
  .letBind c0 .objPtr (.allocCtor 0 [initVar] [])
    (.letBind p0 .i64 (.ctorGetObj c0 0)
      (.decRef c0 1
        (.letBind v0 .i64 (.scalar (.binOp .add (.var p0) (.constU64 d0)))
          (.letBind c1 .objPtr (.allocCtor 1 [v0] [])
            (.letBind p1 .i64 (.ctorGetObj c1 0)
              (.decRef c1 1
                (.letBind v1 .i64 (.scalar (.binOp .add (.var p1) (.constU64 d1)))
                  (.letBind c2 .objPtr (.allocCtor 2 [v1] [])
                    (.letBind p2 .i64 (.ctorGetObj c2 0)
                      (.decRef c2 1
                        (.letBind v2 .i64
                          (.scalar (.binOp .add (.var p2) (.constU64 d2)))
                          (.ret v2))))))))))))

/-- Guard for replacing a 3-tuple async frame by three scalar copies. -/
def canUnboxAsyncFrame3 (dst stV valV dstTag dstState dstVal : VarId)
    (tail : LNIRCode) : Bool :=
  !(dstTag == dst) && !(dstState == dst) && !(dstVal == dst) &&
    !(dstTag == stV) && !(dstTag == valV) && !(dstState == valV) &&
    checkNonEscapingAsync dst tail && !codeUsesVar dst tail

/-- Replace `.letBind dst ty (.mkTuple [tagV, stV, valV]) k` by three scalar copies
when `k` immediately projects `0, 1, 2` out of `dst` and never escapes `dst`. -/
def unboxAsyncFrameHead (dst : VarId) (ty : LNIRType) (val : LNIRExpr)
    (k : LNIRCode) : LNIRCode :=
  match val with
  | .mkTuple [tagV, stV, valV] =>
    match k with
    | .letBind dstTag tyTag (.projTuple d0 0)
        (.letBind dstState tyState (.projTuple d1 1)
          (.letBind dstVal tyVal (.projTuple d2 2) tail)) =>
      if d0 == dst && d1 == dst && d2 == dst &&
          canUnboxAsyncFrame3 dst stV valV dstTag dstState dstVal tail then
        .letBind dstTag tyTag (.scalar (.var tagV))
          (.letBind dstState tyState (.scalar (.var stV))
            (.letBind dstVal tyVal (.scalar (.var valV)) tail))
      else
        .letBind dst ty (.mkTuple [tagV, stV, valV]) k
    | _ => .letBind dst ty (.mkTuple [tagV, stV, valV]) k
  | _ => .letBind dst ty val k

/-- Unbox every eligible async frame, bottom-up. Ineligible code is unchanged. -/
def optimizeAsyncStateMachine : LNIRCode → LNIRCode
  | .letBind dst ty val k =>
    unboxAsyncFrameHead dst ty val (optimizeAsyncStateMachine k)
  | .rawStore p i v ty k => .rawStore p i v ty (optimizeAsyncStateMachine k)
  | .incRef o n k => .incRef o n (optimizeAsyncStateMachine k)
  | .decRef o n k => .decRef o n (optimizeAsyncStateMachine k)
  | .ite cond t e => .ite cond (optimizeAsyncStateMachine t) (optimizeAsyncStateMachine e)
  | .seqFor iv lv hv av ai aty step k =>
    .seqFor iv lv hv av ai aty (optimizeAsyncStateMachine step) (optimizeAsyncStateMachine k)
  | .parFor ov lv ins ety kern k =>
    .parFor ov lv ins ety kern (optimizeAsyncStateMachine k)
  | .ret r => .ret r
  | .unreachable => .unreachable

/-- Step congruence for `evalSeqLoop` under `CodeRefines`. -/
theorem evalSeqLoop_async_refines (count curIdx : Nat) (idxVar accVar : VarId)
    (accVal : Val) (env : VarEnv) (st : HeapState) (v : Val) (st' : HeapState)
    (step1 step2 : VarEnv → HeapState → Except UBError (Val × HeapState))
    (hstep : ∀ senv sst sv sst',
      step1 senv sst = .ok (sv, sst') → step2 senv sst = .ok (sv, sst'))
    (hsrc : evalSeqLoop count curIdx idxVar accVar accVal env st step1 = .ok (v, st')) :
    evalSeqLoop count curIdx idxVar accVar accVal env st step2 = .ok (v, st') := by
  induction count generalizing curIdx accVal st with
  | zero => exact hsrc
  | succ count' ih =>
    simp only [evalSeqLoop] at hsrc ⊢
    cases hs1 : step1 ((env.bind idxVar (.u64 curIdx.toUInt64)).bind accVar accVal) st with
    | error _ => rw [hs1] at hsrc; contradiction
    | ok pair =>
      rcases pair with ⟨nextAcc, st1⟩
      rw [hs1] at hsrc
      rw [hstep _ st nextAcc st1 hs1]
      exact ih (curIdx + 1) nextAcc st1 hsrc

/-- `unboxAsyncFrameHead` refines `.letBind dst ty val k`. -/
theorem unboxAsyncFrameHead_refines (dst : VarId) (ty : LNIRType)
    (val : LNIRExpr) (k : LNIRCode) :
    CodeRefines (.letBind dst ty val k) (unboxAsyncFrameHead dst ty val k) := by
  unfold unboxAsyncFrameHead
  split
  · next tagV stV valV =>
    split
    · next dstTag tyTag d0 dstState tyState d1 dstVal tyVal d2 tail =>
      split
      · next hcond =>
        simp only [Bool.and_eq_true, beq_iff_eq, canUnboxAsyncFrame3,
          Bool.not_eq_true'] at hcond
        rcases hcond with
          ⟨⟨⟨d0eq, d1eq⟩, d2eq⟩,
            ⟨⟨⟨⟨⟨⟨htd, hsd⟩, hvd⟩, ht1⟩, ht2⟩, hs2⟩, _⟩, hdead⟩
        rw [d0eq, d1eq, d2eq]
        intro fuel env st v st' hsrc
        dsimp only [evalCode, evalExpr, evalVarList, evalScalarExpr] at hsrc ⊢
        cases htag : env tagV with
        | none =>
          rw [htag] at hsrc
          contradiction
        | some vt =>
          cases hst : env stV with
          | none =>
            rw [htag, hst] at hsrc
            contradiction
          | some vs =>
            cases hval : env valV with
            | none =>
              rw [htag, hst, hval] at hsrc
              contradiction
            | some vv =>
              rw [htag, hst, hval] at hsrc
              dsimp only [evalCode, evalExpr, evalVarList, evalScalarExpr] at hsrc ⊢
              rw [VarEnv.bind_self] at hsrc
              simp only [List.getElem?_cons_zero, List.getElem?_cons_succ] at hsrc
              have hne_td : dst ≠ dstTag :=
                Ne.symm (beq_eq_false_iff_ne.mp htd)
              have hne_sd : dst ≠ dstState :=
                Ne.symm (beq_eq_false_iff_ne.mp hsd)
              have hne_vd : dst ≠ dstVal :=
                Ne.symm (beq_eq_false_iff_ne.mp hvd)
              have hproj1 :
                  ((env.bind dst (.tuple [vt, vs, vv])).bind dstTag vt) dst =
                    some (.tuple [vt, vs, vv]) := by
                rw [VarEnv.bind_apply, beq_eq_false_iff_ne.mpr hne_td,
                  if_neg Bool.noConfusion, VarEnv.bind_self]
              rw [hproj1] at hsrc
              simp only [List.getElem?_cons_zero, List.getElem?_cons_succ] at hsrc
              have hproj2 :
                  (((env.bind dst (.tuple [vt, vs, vv])).bind dstTag vt).bind dstState vs) dst =
                    some (.tuple [vt, vs, vv]) := by
                rw [VarEnv.bind_apply, beq_eq_false_iff_ne.mpr hne_sd,
                  if_neg Bool.noConfusion, hproj1]
              rw [hproj2] at hsrc
              simp only [List.getElem?_cons_zero, List.getElem?_cons_succ] at hsrc
              have henvSrc :
                  (((env.bind dst (.tuple [vt, vs, vv])).bind dstTag vt).bind dstState vs).bind
                    dstVal vv =
                  (((env.bind dstTag vt).bind dstState vs).bind dstVal vv).bind dst
                    (.tuple [vt, vs, vv]) := by
                rw [LeanNative.Proofs.VarEnv.bind_comm env dst dstTag
                  (.tuple [vt, vs, vv]) vt hne_td]
                rw [LeanNative.Proofs.VarEnv.bind_comm (env.bind dstTag vt) dst dstState
                  (.tuple [vt, vs, vv]) vs hne_sd]
                rw [LeanNative.Proofs.VarEnv.bind_comm
                  ((env.bind dstTag vt).bind dstState vs) dst dstVal
                  (.tuple [vt, vs, vv]) vv hne_vd]
              rw [henvSrc] at hsrc
              rw [LeanNative.Proofs.evalCode_bind_not_uses fuel tail _ st dst _ hdead] at hsrc
              have hstRead : (env.bind dstTag vt) stV = some vs := by
                rw [VarEnv.bind_apply]
                have hsw : (stV == dstTag) = false :=
                  beq_eq_false_iff_ne.mpr (Ne.symm (beq_eq_false_iff_ne.mp ht1))
                rw [hsw]
                exact hst
              have hvalRead : ((env.bind dstTag vt).bind dstState vs) valV = some vv := by
                rw [VarEnv.bind_apply]
                have hsw1 : (valV == dstState) = false :=
                  beq_eq_false_iff_ne.mpr (Ne.symm (beq_eq_false_iff_ne.mp hs2))
                rw [hsw1, if_neg Bool.noConfusion, VarEnv.bind_apply]
                have hsw2 : (valV == dstTag) = false :=
                  beq_eq_false_iff_ne.mpr (Ne.symm (beq_eq_false_iff_ne.mp ht2))
                rw [hsw2]
                exact hval
              rw [hstRead]
              dsimp only
              rw [hvalRead]
              dsimp only
              exact hsrc
      · exact CodeRefines.refl _
    · exact CodeRefines.refl _
  · exact CodeRefines.refl _

/-- `optimizeAsyncStateMachine` refines every program. -/
theorem optimizeAsyncStateMachine_refines (c : LNIRCode) :
    CodeRefines c (optimizeAsyncStateMachine c) := by
  induction c with
  | letBind dst ty val k ih =>
    exact CodeRefines.trans
      (CodeRefines.letBind_congr (ExprRefines.refl val) ih)
      (unboxAsyncFrameHead_refines dst ty val (optimizeAsyncStateMachine k))
  | rawStore p i v ty k ih =>
    exact CodeRefines.rawStore_congr ih
  | incRef o n k ih =>
    exact CodeRefines.incRef_congr ih
  | decRef o n k ih =>
    exact CodeRefines.decRef_congr ih
  | ite cond t e iht ihe =>
    exact CodeRefines.ite_congr iht ihe
  | seqFor iv lv hv av ai aty step k ihs ihk =>
    intro fuel env st v st' hsrc
    dsimp only [optimizeAsyncStateMachine, evalCode] at hsrc ⊢
    cases hlo : env lv with
    | none =>
      rw [hlo] at hsrc
      contradiction
    | some vlo =>
      cases hhi : env hv with
      | none =>
        rw [hlo, hhi] at hsrc
        cases vlo <;> contradiction
      | some vhi =>
        cases hinit : env ai with
        | none =>
          rw [hlo, hhi, hinit] at hsrc
          cases vlo <;> cases vhi <;> contradiction
        | some vinit =>
          rw [hlo, hhi, hinit] at hsrc
          cases vlo <;> cases vhi <;> try contradiction
          simp only at hsrc ⊢
          cases hloop : evalSeqLoop _ _ iv av vinit env st
              (fun stepEnv stepSt => evalCode fuel stepEnv stepSt step) with
          | error _ =>
            rw [hloop] at hsrc
            contradiction
          | ok pair =>
            rcases pair with ⟨finalAcc, st1⟩
            rw [hloop] at hsrc
            have hloop2 := evalSeqLoop_async_refines _ _ iv av vinit env st finalAcc st1
              (fun stepEnv stepSt => evalCode fuel stepEnv stepSt step)
              (fun stepEnv stepSt =>
                evalCode fuel stepEnv stepSt (optimizeAsyncStateMachine step))
              (fun senv sst sv sst' hs => ihs fuel senv sst sv sst' hs)
              hloop
            rw [hloop2]
            exact ihk fuel (env.bind av finalAcc) st1 v st' hsrc
  | parFor ov lv ins ety kern k ih =>
    exact CodeRefines.parFor_congr ih
  | ret r =>
    exact CodeRefines.refl (.ret r)
  | unreachable =>
    exact CodeRefines.refl .unreachable

/-- Machine-checked contract: unbox non-escaping async frames. -/
def verifiedAsyncStateMachineContract : VerifiedCodePassContract where
  name := "AsyncStateMachine"
  theoremRef := "LeanNative.Proofs.asyncStateMachinePass_sound"
  notes := "Unbox non-escaping (tag, state, payload) async frames; 0 allocCtor per poll"
  runCode := optimizeAsyncStateMachine
  sound := optimizeAsyncStateMachine_refines

/-- Verified pass built from `verifiedAsyncStateMachineContract`. -/
def asyncStateMachinePass : TransformPass :=
  TransformPass.ofVerifiedContract verifiedAsyncStateMachineContract

end LeanNative.Transform
