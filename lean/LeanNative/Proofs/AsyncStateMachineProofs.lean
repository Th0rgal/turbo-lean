import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.Transform.AsyncStateMachine
import LeanNative.Transform.Pass

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Transform

/-! ## D5 Soundness: Zero-Alloc Stackless Async State Machine

Zero `def`, zero `structure`, zero `inductive`. Every theorem is proved against
`LeanNative.Semantics.evalCode` using standard axioms only.
-/

private theorem bindSkip (x y : Nat) (hne : x ≠ y) (e : VarEnv) (v : Val) :
    (e.bind y v) x = e x := by
  rw [VarEnv.bind_apply, beq_eq_false_iff_ne.mpr hne]
  rfl

private theorem evalEqU64 (env : VarEnv) (st : HeapState) (x : Nat) (a b : UInt64)
    (h : env x = some (.u64 a)) :
    evalExpr env st (.scalar (.binOp .eq (.var x) (.constU64 b))) =
      .ok (.bool (a == b), st) := by
  simp only [evalExpr, evalScalarExpr, h]
  rfl

private theorem evalProj3_0 (env : VarEnv) (st : HeapState) (t : Nat)
    (a b c : Val) (h : env t = some (.tuple [a, b, c])) :
    evalExpr env st (.projTuple t 0) = .ok (a, st) := by
  simp only [evalExpr, h, List.getElem?_cons_zero]

private theorem evalProj3_1 (env : VarEnv) (st : HeapState) (t : Nat)
    (a b c : Val) (h : env t = some (.tuple [a, b, c])) :
    evalExpr env st (.projTuple t 1) = .ok (b, st) := by
  simp only [evalExpr, h, List.getElem?_cons_succ, List.getElem?_cons_zero]

private theorem evalProj3_2 (env : VarEnv) (st : HeapState) (t : Nat)
    (a b c : Val) (h : env t = some (.tuple [a, b, c])) :
    evalExpr env st (.projTuple t 2) = .ok (c, st) := by
  simp only [evalExpr, h, List.getElem?_cons_succ, List.getElem?_cons_zero]

private theorem stepArms_match (fuel : Nat) (env : VarEnv) (st : HeapState)
    (stV valV armBase : Nat) (step : AsyncStep) (rest : List AsyncStep)
    (fallback : LNIRCode) (payload : UInt64)
    (h2 : valV < armBase)
    (hst : env stV = some (.u64 step.fromState.toUInt64))
    (hval : env valV = some (.u64 payload)) :
    evalCode fuel env st
      (lowerAsyncStepArms stV valV armBase (step :: rest) fallback) =
      .ok (.tuple [.u64 step.outcome.tagBits, .u64 step.toState.toUInt64,
        .u64 (payload + step.stepDelta)], st) := by
  unfold lowerAsyncStepArms
  rw [evalCode, evalEqU64 env st stV step.fromState.toUInt64 step.fromState.toUInt64 hst]
  dsimp only
  rw [evalCode, VarEnv.bind_self, beq_self_eq_true]
  dsimp only
  rw [evalCode]
  dsimp only [evalExpr, evalScalarExpr]
  rw [evalCode]
  dsimp only [evalExpr, evalScalarExpr]
  rw [evalCode]
  have hv : (((env.bind armBase (.bool true)).bind (armBase + 1)
      (.u64 step.outcome.tagBits)).bind (armBase + 2)
      (.u64 step.toState.toUInt64)) valV = some (.u64 payload) := by
    rw [bindSkip valV (armBase + 2) (by omega)]
    rw [bindSkip valV (armBase + 1) (by omega)]
    rw [bindSkip valV armBase (by omega)]
    exact hval
  dsimp only [evalExpr, evalScalarExpr]
  rw [hv]
  dsimp only [evalBinOp]
  rw [evalCode]
  dsimp only [evalExpr, evalVarList]
  have ht : ((((env.bind armBase (.bool true)).bind (armBase + 1)
      (.u64 step.outcome.tagBits)).bind (armBase + 2)
      (.u64 step.toState.toUInt64)).bind (armBase + 3)
      (.u64 (payload + step.stepDelta))) (armBase + 1) =
      some (.u64 step.outcome.tagBits) := by
    rw [bindSkip (armBase + 1) (armBase + 3) (by omega)]
    rw [bindSkip (armBase + 1) (armBase + 2) (by omega)]
    exact VarEnv.bind_self _ _ _
  have hs : ((((env.bind armBase (.bool true)).bind (armBase + 1)
      (.u64 step.outcome.tagBits)).bind (armBase + 2)
      (.u64 step.toState.toUInt64)).bind (armBase + 3)
      (.u64 (payload + step.stepDelta))) (armBase + 2) =
      some (.u64 step.toState.toUInt64) := by
    rw [bindSkip (armBase + 2) (armBase + 3) (by omega)]
    exact VarEnv.bind_self _ _ _
  rw [ht, hs, VarEnv.bind_self]
  dsimp only
  rw [evalCode, VarEnv.bind_self]

private theorem stepArms_skip (fuel : Nat) (env : VarEnv) (st : HeapState)
    (stV valV armBase : Nat) (step : AsyncStep) (rest : List AsyncStep)
    (fallback : LNIRCode) (curSt : UInt64)
    (hst : env stV = some (.u64 curSt))
    (hne : (curSt == step.fromState.toUInt64) = false) :
    evalCode fuel env st
      (lowerAsyncStepArms stV valV armBase (step :: rest) fallback) =
      evalCode fuel (env.bind armBase (.bool false)) st
        (lowerAsyncStepArms stV valV (armBase + 5) rest fallback) := by
  rw [lowerAsyncStepArms.eq_2]
  rw [evalCode, evalEqU64 env st stV curSt step.fromState.toUInt64 hst, hne]
  dsimp only
  rw [evalCode, VarEnv.bind_self]

/-- A `Ready` frame (`tag = 1`) is returned unchanged and allocates nothing. -/
theorem lowerAsyncPollStep_ready_sound (fuel : Nat) (env : VarEnv) (st : HeapState)
    (frameVar base : Nat) (steps : List AsyncStep) (cur payload : UInt64)
    (hfresh : frameVar < base)
    (hframe : env frameVar = some (.tuple [.u64 1, .u64 cur, .u64 payload])) :
    evalCode fuel env st (lowerAsyncPollStep frameVar base steps) =
      .ok (.tuple [.u64 1, .u64 cur, .u64 payload], st) := by
  unfold lowerAsyncPollStep
  rw [evalCode, evalProj3_0 env st frameVar (.u64 1) (.u64 cur) (.u64 payload) hframe]
  dsimp only
  have hf1 : (env.bind base (.u64 1)) frameVar =
      some (.tuple [.u64 1, .u64 cur, .u64 payload]) := by
    rw [bindSkip frameVar base (by omega)]
    exact hframe
  rw [evalCode, evalProj3_1 _ st frameVar (.u64 1) (.u64 cur) (.u64 payload) hf1]
  dsimp only
  have hf2 : ((env.bind base (.u64 1)).bind (base + 1) (.u64 cur)) frameVar =
      some (.tuple [.u64 1, .u64 cur, .u64 payload]) := by
    rw [bindSkip frameVar (base + 1) (by omega)]
    exact hf1
  rw [evalCode, evalProj3_2 _ st frameVar (.u64 1) (.u64 cur) (.u64 payload) hf2]
  dsimp only
  have htag : (((env.bind base (.u64 1)).bind (base + 1) (.u64 cur)).bind (base + 2)
      (.u64 payload)) base = some (.u64 1) := by
    rw [bindSkip base (base + 2) (by omega), bindSkip base (base + 1) (by omega)]
    exact VarEnv.bind_self _ _ _
  rw [evalCode, evalEqU64 _ st base 1 1 htag]
  dsimp only
  have h11 : ((1 : UInt64) == 1) = true := rfl
  rw [h11, evalCode, VarEnv.bind_self]
  dsimp only
  rw [evalCode]
  rw [bindSkip frameVar (base + 3) (by omega), bindSkip frameVar (base + 2) (by omega)]
  rw [hf2]

/-- Polling a `Pending` frame (`tag = 0`) at `step.fromState` advances the state
word, adds `step.stepDelta`, and leaves `HeapState` untouched. -/
theorem lowerAsyncPollStep_sound (fuel : Nat) (env : VarEnv) (st : HeapState)
    (frameVar base : Nat) (step : AsyncStep) (rest : List AsyncStep) (payload : UInt64)
    (hfresh : frameVar < base)
    (hframe : env frameVar =
      some (.tuple [.u64 0, .u64 step.fromState.toUInt64, .u64 payload])) :
    evalCode fuel env st (lowerAsyncPollStep frameVar base (step :: rest)) =
      .ok (.tuple [.u64 step.outcome.tagBits, .u64 step.toState.toUInt64,
        .u64 (payload + step.stepDelta)], st) := by
  unfold lowerAsyncPollStep
  rw [evalCode, evalProj3_0 env st frameVar (.u64 0) (.u64 step.fromState.toUInt64)
    (.u64 payload) hframe]
  dsimp only
  have hf1 : (env.bind base (.u64 0)) frameVar =
      some (.tuple [.u64 0, .u64 step.fromState.toUInt64, .u64 payload]) := by
    rw [bindSkip frameVar base (by omega)]
    exact hframe
  rw [evalCode, evalProj3_1 _ st frameVar (.u64 0) (.u64 step.fromState.toUInt64)
    (.u64 payload) hf1]
  dsimp only
  have hf2 : ((env.bind base (.u64 0)).bind (base + 1)
      (.u64 step.fromState.toUInt64)) frameVar =
      some (.tuple [.u64 0, .u64 step.fromState.toUInt64, .u64 payload]) := by
    rw [bindSkip frameVar (base + 1) (by omega)]
    exact hf1
  rw [evalCode, evalProj3_2 _ st frameVar (.u64 0) (.u64 step.fromState.toUInt64)
    (.u64 payload) hf2]
  dsimp only
  have htag : (((env.bind base (.u64 0)).bind (base + 1)
      (.u64 step.fromState.toUInt64)).bind (base + 2) (.u64 payload)) base =
      some (.u64 0) := by
    rw [bindSkip base (base + 2) (by omega), bindSkip base (base + 1) (by omega)]
    exact VarEnv.bind_self _ _ _
  rw [evalCode, evalEqU64 _ st base 0 1 htag]
  dsimp only
  have h01 : ((0 : UInt64) == 1) = false := rfl
  rw [h01, evalCode, VarEnv.bind_self]
  dsimp only
  refine stepArms_match fuel _ st (base + 1) (base + 2) (base + 4) step rest
    (.ret frameVar) payload (by omega) ?_ ?_
  · rw [bindSkip (base + 1) (base + 3) (by omega)]
    rw [bindSkip (base + 1) (base + 2) (by omega)]
    exact VarEnv.bind_self _ _ _
  · rw [bindSkip (base + 2) (base + 3) (by omega)]
    exact VarEnv.bind_self _ _ _

/-- Polling a `Pending` frame at the second arm's `fromState` skips arm 0 and
executes arm 1 without touching `HeapState`. -/
theorem lowerAsyncPollStep_arm1_sound (fuel : Nat) (env : VarEnv) (st : HeapState)
    (frameVar base : Nat) (s0 s1 : AsyncStep) (rest : List AsyncStep) (payload : UInt64)
    (hfresh : frameVar < base)
    (hne : (s1.fromState.toUInt64 == s0.fromState.toUInt64) = false)
    (hframe : env frameVar =
      some (.tuple [.u64 0, .u64 s1.fromState.toUInt64, .u64 payload])) :
    evalCode fuel env st (lowerAsyncPollStep frameVar base (s0 :: s1 :: rest)) =
      .ok (.tuple [.u64 s1.outcome.tagBits, .u64 s1.toState.toUInt64,
        .u64 (payload + s1.stepDelta)], st) := by
  unfold lowerAsyncPollStep
  rw [evalCode, evalProj3_0 env st frameVar (.u64 0) (.u64 s1.fromState.toUInt64)
    (.u64 payload) hframe]
  dsimp only
  have hf1 : (env.bind base (.u64 0)) frameVar =
      some (.tuple [.u64 0, .u64 s1.fromState.toUInt64, .u64 payload]) := by
    rw [bindSkip frameVar base (by omega)]
    exact hframe
  rw [evalCode, evalProj3_1 _ st frameVar (.u64 0) (.u64 s1.fromState.toUInt64)
    (.u64 payload) hf1]
  dsimp only
  have hf2 : ((env.bind base (.u64 0)).bind (base + 1)
      (.u64 s1.fromState.toUInt64)) frameVar =
      some (.tuple [.u64 0, .u64 s1.fromState.toUInt64, .u64 payload]) := by
    rw [bindSkip frameVar (base + 1) (by omega)]
    exact hf1
  rw [evalCode, evalProj3_2 _ st frameVar (.u64 0) (.u64 s1.fromState.toUInt64)
    (.u64 payload) hf2]
  dsimp only
  have htag : (((env.bind base (.u64 0)).bind (base + 1)
      (.u64 s1.fromState.toUInt64)).bind (base + 2) (.u64 payload)) base =
      some (.u64 0) := by
    rw [bindSkip base (base + 2) (by omega), bindSkip base (base + 1) (by omega)]
    exact VarEnv.bind_self _ _ _
  rw [evalCode, evalEqU64 _ st base 0 1 htag]
  dsimp only
  have h01 : ((0 : UInt64) == 1) = false := rfl
  rw [h01, evalCode, VarEnv.bind_self]
  dsimp only
  have hst0 : ((((env.bind base (.u64 0)).bind (base + 1)
      (.u64 s1.fromState.toUInt64)).bind (base + 2) (.u64 payload)).bind
      (base + 3) (.bool false)) (base + 1) = some (.u64 s1.fromState.toUInt64) := by
    rw [bindSkip (base + 1) (base + 3) (by omega)]
    rw [bindSkip (base + 1) (base + 2) (by omega)]
    exact VarEnv.bind_self _ _ _
  rw [stepArms_skip fuel _ st (base + 1) (base + 2) (base + 4) s0 (s1 :: rest)
    (.ret frameVar) s1.fromState.toUInt64 hst0 hne]
  refine stepArms_match fuel _ st (base + 1) (base + 2) (base + 4 + 5) s1 rest
    (.ret frameVar) payload (by omega) ?_ ?_
  · rw [bindSkip (base + 1) (base + 4) (by omega)]
    exact hst0
  · rw [bindSkip (base + 2) (base + 4) (by omega)]
    rw [bindSkip (base + 2) (base + 3) (by omega)]
    exact VarEnv.bind_self _ _ _

private theorem lowerAsyncPollStep_arm2_sound (fuel : Nat) (env : VarEnv) (st : HeapState)
    (frameVar base : Nat) (s0 s1 s2 : AsyncStep) (rest : List AsyncStep) (payload : UInt64)
    (hfresh : frameVar < base)
    (hne0 : (s2.fromState.toUInt64 == s0.fromState.toUInt64) = false)
    (hne1 : (s2.fromState.toUInt64 == s1.fromState.toUInt64) = false)
    (hframe : env frameVar =
      some (.tuple [.u64 0, .u64 s2.fromState.toUInt64, .u64 payload])) :
    evalCode fuel env st (lowerAsyncPollStep frameVar base (s0 :: s1 :: s2 :: rest)) =
      .ok (.tuple [.u64 s2.outcome.tagBits, .u64 s2.toState.toUInt64,
        .u64 (payload + s2.stepDelta)], st) := by
  unfold lowerAsyncPollStep
  rw [evalCode, evalProj3_0 env st frameVar (.u64 0) (.u64 s2.fromState.toUInt64)
    (.u64 payload) hframe]
  dsimp only
  have hf1 : (env.bind base (.u64 0)) frameVar =
      some (.tuple [.u64 0, .u64 s2.fromState.toUInt64, .u64 payload]) := by
    rw [bindSkip frameVar base (by omega)]
    exact hframe
  rw [evalCode, evalProj3_1 _ st frameVar (.u64 0) (.u64 s2.fromState.toUInt64)
    (.u64 payload) hf1]
  dsimp only
  have hf2 : ((env.bind base (.u64 0)).bind (base + 1)
      (.u64 s2.fromState.toUInt64)) frameVar =
      some (.tuple [.u64 0, .u64 s2.fromState.toUInt64, .u64 payload]) := by
    rw [bindSkip frameVar (base + 1) (by omega)]
    exact hf1
  rw [evalCode, evalProj3_2 _ st frameVar (.u64 0) (.u64 s2.fromState.toUInt64)
    (.u64 payload) hf2]
  dsimp only
  have htag : (((env.bind base (.u64 0)).bind (base + 1)
      (.u64 s2.fromState.toUInt64)).bind (base + 2) (.u64 payload)) base =
      some (.u64 0) := by
    rw [bindSkip base (base + 2) (by omega), bindSkip base (base + 1) (by omega)]
    exact VarEnv.bind_self _ _ _
  rw [evalCode, evalEqU64 _ st base 0 1 htag]
  dsimp only
  have h01 : ((0 : UInt64) == 1) = false := rfl
  rw [h01, evalCode, VarEnv.bind_self]
  dsimp only
  have hst0 : ((((env.bind base (.u64 0)).bind (base + 1)
      (.u64 s2.fromState.toUInt64)).bind (base + 2) (.u64 payload)).bind
      (base + 3) (.bool false)) (base + 1) = some (.u64 s2.fromState.toUInt64) := by
    rw [bindSkip (base + 1) (base + 3) (by omega)]
    rw [bindSkip (base + 1) (base + 2) (by omega)]
    exact VarEnv.bind_self _ _ _
  rw [stepArms_skip fuel _ st (base + 1) (base + 2) (base + 4) s0 (s1 :: s2 :: rest)
    (.ret frameVar) s2.fromState.toUInt64 hst0 hne0]
  have hst1 : (((((env.bind base (.u64 0)).bind (base + 1)
      (.u64 s2.fromState.toUInt64)).bind (base + 2) (.u64 payload)).bind
      (base + 3) (.bool false)).bind (base + 4) (.bool false)) (base + 1) =
      some (.u64 s2.fromState.toUInt64) := by
    rw [bindSkip (base + 1) (base + 4) (by omega)]
    exact hst0
  rw [stepArms_skip fuel _ st (base + 1) (base + 2) (base + 4 + 5) s1 (s2 :: rest)
    (.ret frameVar) s2.fromState.toUInt64 hst1 hne1]
  refine stepArms_match fuel _ st (base + 1) (base + 2) (base + 4 + 5 + 5) s2 rest
    (.ret frameVar) payload (by omega) ?_ ?_
  · rw [bindSkip (base + 1) (base + 4 + 5) (by omega)]
    exact hst1
  · rw [bindSkip (base + 2) (base + 4 + 5) (by omega)]
    rw [bindSkip (base + 2) (base + 4) (by omega)]
    rw [bindSkip (base + 2) (base + 3) (by omega)]
    exact VarEnv.bind_self _ _ _

private theorem evalSeqLoop_ready_tail (extra curIdx : Nat) (fuel : Nat)
    (idxVar accVar base : Nat) (steps : List AsyncStep) (cur payload : UInt64)
    (env : VarEnv) (st : HeapState) (hfresh : accVar < base) :
    evalSeqLoop extra curIdx idxVar accVar (.tuple [.u64 1, .u64 cur, .u64 payload])
      env st (fun stepEnv stepSt =>
        evalCode fuel stepEnv stepSt (lowerAsyncPollStep accVar base steps)) =
      .ok (.tuple [.u64 1, .u64 cur, .u64 payload], st) := by
  induction extra generalizing curIdx with
  | zero => rfl
  | succ n ih =>
    simp only [evalSeqLoop]
    rw [lowerAsyncPollStep_ready_sound fuel _ st accVar base steps cur payload hfresh
      (VarEnv.bind_self _ _ _)]
    exact ih (curIdx + 1)

/-- Full event-loop soundness: a 3-poll `Pending → Pending → Ready` coroutine
with `3 + extraPolls` poll budget reaches `Ready` at state `3` with payload
`initVal + d0 + d1 + d2` and zero heap allocations (`st` unchanged). -/
theorem lowerAsyncEventLoop_sound (fuel : Nat) (env : VarEnv) (st : HeapState)
    (inputVar regBase extraPolls : Nat) (initVal d0 d1 d2 : UInt64)
    (hreg : inputVar < regBase)
    (hbudget : 3 + extraPolls < UInt64.size)
    (hinput : env inputVar = some (.u64 initVal)) :
    evalCode fuel env st
      (lowerAsyncEventLoop (mkThreeStepAsyncSpec inputVar regBase (3 + extraPolls) d0 d1 d2)) =
      .ok (.tuple [.u64 1, .u64 3, .u64 (initVal + d0 + d1 + d2)], st) := by
  unfold lowerAsyncEventLoop mkThreeStepAsyncSpec
  have hz0 : (0 : Nat).toUInt64 = 0 := rfl
  rw [evalCode]
  dsimp only [evalExpr, evalScalarExpr]
  rw [evalCode]
  dsimp only [evalExpr, evalScalarExpr]
  rw [evalCode]
  dsimp only [evalExpr, evalScalarExpr, AsyncPollResult.tagBits]
  rw [evalCode]
  dsimp only [evalExpr, evalScalarExpr]
  rw [hz0, evalCode]
  dsimp only [evalExpr, evalVarList]
  have hin : ((((env.bind regBase (.u64 0)).bind (regBase + 1)
      (.u64 (3 + extraPolls).toUInt64)).bind (regBase + 2) (.u64 0)).bind
      (regBase + 3) (.u64 0)) inputVar = some (.u64 initVal) := by
    rw [bindSkip inputVar (regBase + 3) (by omega)]
    rw [bindSkip inputVar (regBase + 2) (by omega)]
    rw [bindSkip inputVar (regBase + 1) (by omega)]
    rw [bindSkip inputVar regBase (by omega)]
    exact hinput
  have ht0 : ((((env.bind regBase (.u64 0)).bind (regBase + 1)
      (.u64 (3 + extraPolls).toUInt64)).bind (regBase + 2) (.u64 0)).bind
      (regBase + 3) (.u64 0)) (regBase + 2) = some (.u64 0) := by
    rw [bindSkip (regBase + 2) (regBase + 3) (by omega)]
    exact VarEnv.bind_self _ _ _
  rw [ht0, VarEnv.bind_self, hin]
  dsimp only
  let env5 := ((((env.bind regBase (.u64 0)).bind (regBase + 1)
    (.u64 (3 + extraPolls).toUInt64)).bind (regBase + 2) (.u64 0)).bind
    (regBase + 3) (.u64 0)).bind (regBase + 4)
    (.tuple [.u64 0, .u64 0, .u64 initVal])
  change evalCode fuel env5 st _ = _
  have hlo : env5 regBase = some (.u64 0) := by
    dsimp only [env5]
    rw [bindSkip regBase (regBase + 4) (by omega)]
    rw [bindSkip regBase (regBase + 3) (by omega)]
    rw [bindSkip regBase (regBase + 2) (by omega)]
    rw [bindSkip regBase (regBase + 1) (by omega)]
    exact VarEnv.bind_self _ _ _
  have hhi : env5 (regBase + 1) = some (.u64 (3 + extraPolls).toUInt64) := by
    dsimp only [env5]
    rw [bindSkip (regBase + 1) (regBase + 4) (by omega)]
    rw [bindSkip (regBase + 1) (regBase + 3) (by omega)]
    rw [bindSkip (regBase + 1) (regBase + 2) (by omega)]
    exact VarEnv.bind_self _ _ _
  have hinit : env5 (regBase + 4) =
      some (.tuple [.u64 0, .u64 0, .u64 initVal]) :=
    VarEnv.bind_self _ _ _
  rw [evalCode, hlo, hhi, hinit]
  dsimp only
  have hcnt : (3 + extraPolls).toUInt64.toNat - (0 : UInt64).toNat = extraPolls + 3 := by
    simp [Nat.toUInt64, Nat.mod_eq_of_lt hbudget]
    omega
  rw [hcnt]
  dsimp only [evalSeqLoop]
  have hp0 := lowerAsyncPollStep_sound fuel
    ((env5.bind (regBase + 5) (.u64 (0 : UInt64).toNat.toUInt64)).bind (regBase + 6)
      (.tuple [.u64 0, .u64 (0 : Nat).toUInt64, .u64 initVal]))
    st (regBase + 6) (regBase + 7)
    { fromState := 0, toState := 1, stepDelta := d0, outcome := .Pending }
    [ { fromState := 1, toState := 2, stepDelta := d1, outcome := .Pending }
    , { fromState := 2, toState := 3, stepDelta := d2, outcome := .Ready } ]
    initVal (by omega) (VarEnv.bind_self _ _ _)
  rw [hz0] at hp0
  rw [hp0]
  dsimp only [evalSeqLoop, AsyncPollResult.tagBits]
  have hp1 := lowerAsyncPollStep_arm1_sound fuel
    ((env5.bind (regBase + 5) (.u64 ((0 : UInt64).toNat + 1).toUInt64)).bind (regBase + 6)
      (.tuple [.u64 0, .u64 (1 : Nat).toUInt64, .u64 (initVal + d0)]))
    st (regBase + 6) (regBase + 7)
    { fromState := 0, toState := 1, stepDelta := d0, outcome := .Pending }
    { fromState := 1, toState := 2, stepDelta := d1, outcome := .Pending }
    [ { fromState := 2, toState := 3, stepDelta := d2, outcome := .Ready } ]
    (initVal + d0) (by omega) rfl (VarEnv.bind_self _ _ _)
  rw [hp1]
  dsimp only [evalSeqLoop, AsyncPollResult.tagBits]
  have hp2 := lowerAsyncPollStep_arm2_sound fuel
    ((env5.bind (regBase + 5) (.u64 ((0 : UInt64).toNat + 1 + 1).toUInt64)).bind (regBase + 6)
      (.tuple [.u64 0, .u64 (2 : Nat).toUInt64, .u64 (initVal + d0 + d1)]))
    st (regBase + 6) (regBase + 7)
    { fromState := 0, toState := 1, stepDelta := d0, outcome := .Pending }
    { fromState := 1, toState := 2, stepDelta := d1, outcome := .Pending }
    { fromState := 2, toState := 3, stepDelta := d2, outcome := .Ready }
    [] (initVal + d0 + d1) (by omega) rfl rfl (VarEnv.bind_self _ _ _)
  rw [hp2]
  dsimp only [AsyncPollResult.tagBits]
  rw [evalSeqLoop_ready_tail extraPolls ((0 : UInt64).toNat + 1 + 1 + 1) fuel
    (regBase + 5) (regBase + 6) (regBase + 7) _ (3 : Nat).toUInt64
    (initVal + d0 + d1 + d2) env5 st (by omega)]
  dsimp only
  rw [evalCode, VarEnv.bind_self]
  rfl

/-- `asyncStateMachinePass` refines every declaration body (`Contract V2`). -/
theorem asyncStateMachinePass_sound (d : LNIRDecl) :
    CodeRefines d.body ((asyncStateMachinePass.runDecl d).1.body) :=
  TransformPass.ofVerifiedContract_body_refines verifiedAsyncStateMachineContract d

/-- Capturing a continuation in a heap constructor is rejected by escape analysis. -/
theorem checkNonEscapingAsync_rejects_closure (cont dst : VarId) (tag : Nat)
    (k : LNIRCode) :
    checkNonEscapingAsync cont
      (.letBind dst .objPtr (.allocCtor tag [cont] []) k) = false := by
  unfold checkNonEscapingAsync asyncCodeEscapes asyncExprEscapes exprUsesVar
  simp

/-- Non-vacuous zero-alloc witness over `Pending → Pending → Ready`:
polls 1 and 2 yield `Pending` (`tag = 0`), poll 3 and a 16-poll loop yield
`Ready` (`tag = 1`, payload `31 = 10 + 5 + 7 + 9`, `nextId = 0`), while the
heap-closure baseline allocates 3 objects (`nextId = 3`). -/
theorem asyncStateMachine_zeroAlloc_nonvacuous (fuel : Nat) :
    evalCode fuel (VarEnv.empty.bind 0 (.u64 10)) HeapState.empty
      (lowerAsyncEventLoop (mkThreeStepAsyncSpec 0 10 1 5 7 9)) =
      .ok (.tuple [.u64 0, .u64 1, .u64 15], HeapState.empty) ∧
    evalCode fuel (VarEnv.empty.bind 0 (.u64 10)) HeapState.empty
      (lowerAsyncEventLoop (mkThreeStepAsyncSpec 0 10 2 5 7 9)) =
      .ok (.tuple [.u64 0, .u64 2, .u64 22], HeapState.empty) ∧
    evalCode fuel (VarEnv.empty.bind 0 (.u64 10)) HeapState.empty
      (lowerAsyncEventLoop (mkThreeStepAsyncSpec 0 10 16 5 7 9)) =
      .ok (.tuple [.u64 1, .u64 3, .u64 31], HeapState.empty) ∧
    evalCode fuel (VarEnv.empty.bind 0 (.u64 10)) HeapState.empty
      (lowerHeapClosureAsync3 0 10 5 7 9) =
      .ok (.u64 31, { HeapState.empty with nextId := 3 }) :=
  ⟨rfl, rfl, rfl, rfl⟩

end LeanNative.Proofs
