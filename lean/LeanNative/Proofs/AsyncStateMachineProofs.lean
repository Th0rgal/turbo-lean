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

private theorem stepArms_spec_sound (fuel : Nat) (env : VarEnv) (st : HeapState)
    (stV valV retVar armBase : Nat) (steps : List AsyncStep)
    (tag cur payload : UInt64)
    (hst_lt : stV < armBase) (hval_lt : valV < armBase) (hret_lt : retVar < armBase)
    (hst : env stV = some (.u64 cur))
    (hval : env valV = some (.u64 payload))
    (hret : env retVar = some (.tuple [.u64 tag, .u64 cur, .u64 payload])) :
    evalCode fuel env st (lowerAsyncStepArms stV valV armBase steps (.ret retVar)) =
      .ok (match steps.find? (fun s => cur == s.fromState.toUInt64) with
        | some s => .tuple [.u64 s.outcome.tagBits, .u64 s.toState.toUInt64,
            .u64 (payload + s.stepDelta)]
        | none => .tuple [.u64 tag, .u64 cur, .u64 payload], st) := by
  induction steps generalizing env armBase with
  | nil =>
    unfold lowerAsyncStepArms
    simp only [List.find?]
    rw [evalCode, hret]
  | cons step rest ih =>
    cases hmatch : (cur == step.fromState.toUInt64) with
    | true =>
      have hcur_eq : cur = step.fromState.toUInt64 := of_decide_eq_true hmatch
      simp only [List.find?, hmatch]
      rw [hcur_eq] at hst
      exact stepArms_match fuel env st stV valV armBase step rest (.ret retVar)
        payload hval_lt hst hval
    | false =>
      simp only [List.find?, hmatch]
      rw [stepArms_skip fuel env st stV valV armBase step rest (.ret retVar) cur hst hmatch]
      refine ih (env.bind armBase (.bool false)) (armBase + 5)
        (by omega) (by omega) (by omega) ?_ ?_ ?_
      · rw [bindSkip stV armBase (by omega)]
        exact hst
      · rw [bindSkip valV armBase (by omega)]
        exact hval
      · rw [bindSkip retVar armBase (by omega)]
        exact hret

/-- General single-poll soundness for arbitrary `steps : List AsyncStep`:
polling any `(tag, cur, payload)` frame matches `stepSpecPoll` and preserves `st` unchanged. -/
theorem lowerAsyncPollStep_spec_sound (fuel : Nat) (env : VarEnv) (st : HeapState)
    (frameVar base : Nat) (steps : List AsyncStep) (tag cur payload : UInt64)
    (hfresh : frameVar < base)
    (hframe : env frameVar = some (.tuple [.u64 tag, .u64 cur, .u64 payload])) :
    evalCode fuel env st (lowerAsyncPollStep frameVar base steps) =
      .ok (asyncFrameVal (stepSpecPoll steps tag cur payload), st) := by
  cases htag : (tag == 1) with
  | true =>
    have htag1 : tag = 1 := of_decide_eq_true htag
    subst htag1
    unfold stepSpecPoll asyncFrameVal
    have h11 : ((1 : UInt64) == 1) = true := rfl
    rw [h11, ite_eq_left rfl]
    exact lowerAsyncPollStep_ready_sound fuel env st frameVar base steps cur payload hfresh hframe
  | false =>
    unfold lowerAsyncPollStep stepSpecPoll
    rw [htag, ite_eq_right Bool.noConfusion]
    rw [evalCode, evalProj3_0 env st frameVar (.u64 tag) (.u64 cur) (.u64 payload) hframe]
    dsimp only
    have hf1 : (env.bind base (.u64 tag)) frameVar =
        some (.tuple [.u64 tag, .u64 cur, .u64 payload]) := by
      rw [bindSkip frameVar base (by omega)]
      exact hframe
    rw [evalCode, evalProj3_1 _ st frameVar (.u64 tag) (.u64 cur) (.u64 payload) hf1]
    dsimp only
    have hf2 : ((env.bind base (.u64 tag)).bind (base + 1) (.u64 cur)) frameVar =
        some (.tuple [.u64 tag, .u64 cur, .u64 payload]) := by
      rw [bindSkip frameVar (base + 1) (by omega)]
      exact hf1
    rw [evalCode, evalProj3_2 _ st frameVar (.u64 tag) (.u64 cur) (.u64 payload) hf2]
    dsimp only
    have htagEnv : (((env.bind base (.u64 tag)).bind (base + 1) (.u64 cur)).bind
        (base + 2) (.u64 payload)) base = some (.u64 tag) := by
      rw [bindSkip base (base + 2) (by omega), bindSkip base (base + 1) (by omega)]
      exact VarEnv.bind_self _ _ _
    rw [evalCode, evalEqU64 _ st base tag 1 htagEnv, htag]
    dsimp only
    rw [evalCode, VarEnv.bind_self]
    dsimp only
    have herest := stepArms_spec_sound fuel
      ((((env.bind base (.u64 tag)).bind (base + 1) (.u64 cur)).bind
        (base + 2) (.u64 payload)).bind (base + 3) (.bool false))
      st (base + 1) (base + 2) frameVar (base + 4) steps tag cur payload
      (by omega) (by omega) (by omega)
      (by rw [bindSkip (base + 1) (base + 3) (by omega),
              bindSkip (base + 1) (base + 2) (by omega)]
          exact VarEnv.bind_self _ _ _)
      (by rw [bindSkip (base + 2) (base + 3) (by omega)]
          exact VarEnv.bind_self _ _ _)
      (by rw [bindSkip frameVar (base + 3) (by omega),
              bindSkip frameVar (base + 2) (by omega)]
          exact hf2)
    rw [herest]
    cases steps.find? (fun s => cur == s.fromState.toUInt64) <;> rfl

private theorem evalSeqLoop_spec_sound (fuel : Nat) (env : VarEnv) (st : HeapState)
    (count curIdx : Nat) (idxVar accVar base : Nat) (steps : List AsyncStep)
    (tag cur payload : UInt64) (hfresh : accVar < base) :
    evalSeqLoop count curIdx idxVar accVar (.tuple [.u64 tag, .u64 cur, .u64 payload])
      env st (fun stepEnv stepSt =>
        evalCode fuel stepEnv stepSt (lowerAsyncPollStep accVar base steps)) =
      .ok (asyncFrameVal (runSpecPollsLoop steps count tag cur payload), st) := by
  induction count generalizing curIdx tag cur payload with
  | zero =>
    unfold runSpecPollsLoop asyncFrameVal
    rfl
  | succ n ih =>
    simp only [evalSeqLoop, runSpecPollsLoop]
    rw [lowerAsyncPollStep_spec_sound fuel _ st accVar base steps tag cur payload hfresh
      (VarEnv.bind_self _ _ _)]
    rcases hstep : stepSpecPoll steps tag cur payload with ⟨nt, ns, np⟩
    dsimp only [asyncFrameVal]
    exact ih (curIdx + 1) nt ns np

private theorem runSpecPollsLoop_ready_tail (extra : Nat) (steps : List AsyncStep)
    (cur payload : UInt64) :
    runSpecPollsLoop steps extra 1 cur payload = (1, cur, payload) := by
  induction extra with
  | zero => rfl
  | succ n ih =>
    simp only [runSpecPollsLoop, stepSpecPoll]
    have h11 : ((1 : UInt64) == 1) = true := rfl
    rw [h11, ite_eq_left rfl]
    exact ih

/-- General multi-poll soundness of `lowerAsyncEventLoop spec` over an arbitrary
well-formed `spec : AsyncCoroutineSpec`: running `spec.pollBudget` polls from `Pending`
at `spec.initState.toUInt64` with payload `initVal` equals `asyncFrameVal (runSpecPolls spec spec.pollBudget initVal)`
and allocates zero heap objects (`st` unchanged, hence `st'.nextId = st.nextId` and `st'.objs = st.objs`). -/
theorem lowerAsyncEventLoop_sound (fuel : Nat) (env : VarEnv) (st : HeapState)
    (spec : AsyncCoroutineSpec) (initVal : UInt64)
    (hreg : spec.inputVar < spec.regBase)
    (hbudget : spec.pollBudget < UInt64.size)
    (hinput : env spec.inputVar = some (.u64 initVal)) :
    evalCode fuel env st (lowerAsyncEventLoop spec) =
      .ok (asyncFrameVal (runSpecPolls spec spec.pollBudget initVal), st) := by
  unfold lowerAsyncEventLoop runSpecPolls
  rw [evalCode]
  dsimp only [evalExpr, evalScalarExpr]
  rw [evalCode]
  dsimp only [evalExpr, evalScalarExpr]
  rw [evalCode]
  dsimp only [evalExpr, evalScalarExpr, AsyncPollResult.tagBits]
  rw [evalCode]
  dsimp only [evalExpr, evalScalarExpr]
  rw [evalCode]
  dsimp only [evalExpr, evalVarList]
  have hin : ((((env.bind spec.regBase (.u64 0)).bind (spec.regBase + 1)
      (.u64 spec.pollBudget.toUInt64)).bind (spec.regBase + 2) (.u64 0)).bind
      (spec.regBase + 3) (.u64 spec.initState.toUInt64)) spec.inputVar =
      some (.u64 initVal) := by
    rw [bindSkip spec.inputVar (spec.regBase + 3) (Nat.ne_of_lt (Nat.lt_add_right 3 hreg))]
    rw [bindSkip spec.inputVar (spec.regBase + 2) (Nat.ne_of_lt (Nat.lt_add_right 2 hreg))]
    rw [bindSkip spec.inputVar (spec.regBase + 1) (Nat.ne_of_lt (Nat.lt_add_right 1 hreg))]
    rw [bindSkip spec.inputVar spec.regBase (Nat.ne_of_lt hreg)]
    exact hinput
  have ht0 : ((((env.bind spec.regBase (.u64 0)).bind (spec.regBase + 1)
      (.u64 spec.pollBudget.toUInt64)).bind (spec.regBase + 2) (.u64 0)).bind
      (spec.regBase + 3) (.u64 spec.initState.toUInt64)) (spec.regBase + 2) =
      some (.u64 0) := by
    rw [bindSkip (spec.regBase + 2) (spec.regBase + 3) (by omega)]
    exact VarEnv.bind_self _ _ _
  have hs0 : ((((env.bind spec.regBase (.u64 0)).bind (spec.regBase + 1)
      (.u64 spec.pollBudget.toUInt64)).bind (spec.regBase + 2) (.u64 0)).bind
      (spec.regBase + 3) (.u64 spec.initState.toUInt64)) (spec.regBase + 3) =
      some (.u64 spec.initState.toUInt64) :=
    VarEnv.bind_self _ _ _
  rw [ht0, hs0, hin]
  dsimp only
  let env5 := ((((env.bind spec.regBase (.u64 0)).bind (spec.regBase + 1)
    (.u64 spec.pollBudget.toUInt64)).bind (spec.regBase + 2) (.u64 0)).bind
    (spec.regBase + 3) (.u64 spec.initState.toUInt64)).bind (spec.regBase + 4)
    (.tuple [.u64 0, .u64 spec.initState.toUInt64, .u64 initVal])
  change evalCode fuel env5 st _ = _
  have hlo : env5 spec.regBase = some (.u64 0) := by
    dsimp only [env5]
    rw [bindSkip spec.regBase (spec.regBase + 4) (by omega)]
    rw [bindSkip spec.regBase (spec.regBase + 3) (by omega)]
    rw [bindSkip spec.regBase (spec.regBase + 2) (by omega)]
    rw [bindSkip spec.regBase (spec.regBase + 1) (by omega)]
    exact VarEnv.bind_self _ _ _
  have hhi : env5 (spec.regBase + 1) = some (.u64 spec.pollBudget.toUInt64) := by
    dsimp only [env5]
    rw [bindSkip (spec.regBase + 1) (spec.regBase + 4) (by omega)]
    rw [bindSkip (spec.regBase + 1) (spec.regBase + 3) (by omega)]
    rw [bindSkip (spec.regBase + 1) (spec.regBase + 2) (by omega)]
    exact VarEnv.bind_self _ _ _
  have hinit : env5 (spec.regBase + 4) =
      some (.tuple [.u64 0, .u64 spec.initState.toUInt64, .u64 initVal]) :=
    VarEnv.bind_self _ _ _
  rw [evalCode, hlo, hhi, hinit]
  dsimp only
  have hcnt : spec.pollBudget.toUInt64.toNat - (0 : UInt64).toNat = spec.pollBudget := by
    simp [Nat.toUInt64, Nat.mod_eq_of_lt hbudget]
  rw [hcnt]
  rw [evalSeqLoop_spec_sound fuel env5 st spec.pollBudget (0 : UInt64).toNat
    (spec.regBase + 5) (spec.regBase + 6) (spec.regBase + 7)
    spec.steps 0 spec.initState.toUInt64 initVal (by omega)]
  dsimp only [asyncFrameVal]
  rw [evalCode, VarEnv.bind_self]

/-- Concrete 3-poll `Pending → Pending → Ready` instantiation of `lowerAsyncEventLoop_sound`:
with `3 + extraPolls` poll budget the coroutine reaches `Ready` at state `3` with payload
`initVal + d0 + d1 + d2` and zero heap allocations (`st` unchanged). -/
theorem lowerAsyncEventLoop_threeStep_sound (fuel : Nat) (env : VarEnv) (st : HeapState)
    (inputVar regBase extraPolls : Nat) (initVal d0 d1 d2 : UInt64)
    (hreg : inputVar < regBase)
    (hbudget : 3 + extraPolls < UInt64.size)
    (hinput : env inputVar = some (.u64 initVal)) :
    evalCode fuel env st
      (lowerAsyncEventLoop (mkThreeStepAsyncSpec inputVar regBase (3 + extraPolls) d0 d1 d2)) =
      .ok (.tuple [.u64 1, .u64 3, .u64 (initVal + d0 + d1 + d2)], st) := by
  have hbud' : extraPolls + 3 < UInt64.size := by omega
  have heq : 3 + extraPolls = extraPolls + 3 := by omega
  rw [heq]
  have hspec := lowerAsyncEventLoop_sound fuel env st
    (mkThreeStepAsyncSpec inputVar regBase (extraPolls + 3) d0 d1 d2) initVal
    (by dsimp [mkThreeStepAsyncSpec]; exact hreg)
    (by dsimp [mkThreeStepAsyncSpec]; exact hbud')
    (by dsimp [mkThreeStepAsyncSpec]; exact hinput)
  rw [hspec]
  dsimp only [mkThreeStepAsyncSpec, runSpecPolls, runSpecPollsLoop, stepSpecPoll,
    AsyncPollResult.tagBits, List.find?]
  change Except.ok (asyncFrameVal (runSpecPollsLoop
    [ { fromState := 0, toState := 1, stepDelta := d0, outcome := .Pending }
    , { fromState := 1, toState := 2, stepDelta := d1, outcome := .Pending }
    , { fromState := 2, toState := 3, stepDelta := d2, outcome := .Ready } ]
    extraPolls 1 3 (initVal + d0 + d1 + d2)), st) = _
  rw [runSpecPollsLoop_ready_tail]
  rfl

private theorem lowerAsyncAwaitSteps_sound (fuel : Nat) (env : VarEnv) (st : HeapState)
    (tagV stV valV base : Nat) (steps : List AsyncStep) (tag cur payload : UInt64)
    (ht_lt : tagV < base) (hs_lt : stV < base) (hv_lt : valV < base)
    (ht : env tagV = some (.u64 tag))
    (hs : env stV = some (.u64 cur))
    (hv : env valV = some (.u64 payload)) :
    evalCode fuel env st (lowerAsyncAwaitSteps tagV stV valV base steps) =
      .ok (.u64 (runAwaitStepsPayload steps tag cur payload), st) := by
  induction steps generalizing env tagV stV valV base tag cur payload with
  | nil =>
    unfold lowerAsyncAwaitSteps runAwaitStepsPayload
    rw [evalCode, hv]
  | cons step rest ih =>
    unfold lowerAsyncAwaitSteps runAwaitStepsPayload
    rw [evalCode, evalEqU64 env st tagV tag 1 ht]
    dsimp only
    cases hdone : (tag == 1) with
    | true =>
      rw [ite_eq_left rfl, evalCode, VarEnv.bind_self]
      dsimp only
      rw [evalCode]
      dsimp only [evalExpr, evalVarList]
      have ht1 : (env.bind base (.bool true)) tagV = some (.u64 tag) := by
        rw [bindSkip tagV base (Nat.ne_of_lt ht_lt)]; exact ht
      have hs1 : (env.bind base (.bool true)) stV = some (.u64 cur) := by
        rw [bindSkip stV base (Nat.ne_of_lt hs_lt)]; exact hs
      have hv1 : (env.bind base (.bool true)) valV = some (.u64 payload) := by
        rw [bindSkip valV base (Nat.ne_of_lt hv_lt)]; exact hv
      rw [ht1, hs1, hv1]
      dsimp only
      let eFrm := (env.bind base (.bool true)).bind (base + 8)
        (.tuple [.u64 tag, .u64 cur, .u64 payload])
      change evalCode fuel eFrm st _ = _
      have hfrm0 : eFrm (base + 8) = some (.tuple [.u64 tag, .u64 cur, .u64 payload]) :=
        VarEnv.bind_self _ _ _
      rw [evalCode, evalProj3_0 eFrm st (base + 8) (.u64 tag) (.u64 cur) (.u64 payload) hfrm0]
      dsimp only
      have hfrm1 : (eFrm.bind (base + 9) (.u64 tag)) (base + 8) =
          some (.tuple [.u64 tag, .u64 cur, .u64 payload]) := by
        rw [bindSkip (base + 8) (base + 9) (by omega)]; exact hfrm0
      rw [evalCode, evalProj3_1 _ st (base + 8) (.u64 tag) (.u64 cur) (.u64 payload) hfrm1]
      dsimp only
      have hfrm2 : ((eFrm.bind (base + 9) (.u64 tag)).bind (base + 10) (.u64 cur)) (base + 8) =
          some (.tuple [.u64 tag, .u64 cur, .u64 payload]) := by
        rw [bindSkip (base + 8) (base + 10) (by omega)]; exact hfrm1
      rw [evalCode, evalProj3_2 _ st (base + 8) (.u64 tag) (.u64 cur) (.u64 payload) hfrm2]
      dsimp only
      refine ih _ (base + 9) (base + 10) (base + 11) (base + 12) tag cur payload
        (by omega) (by omega) (by omega) ?_ ?_ (VarEnv.bind_self _ _ _)
      · rw [bindSkip (base + 9) (base + 11) (by omega),
            bindSkip (base + 9) (base + 10) (by omega)]
        exact VarEnv.bind_self _ _ _
      · rw [bindSkip (base + 10) (base + 11) (by omega)]
        exact VarEnv.bind_self _ _ _
    | false =>
      rw [ite_eq_right Bool.noConfusion, evalCode, VarEnv.bind_self]
      dsimp only
      have hs1 : (env.bind base (.bool false)) stV = some (.u64 cur) := by
        rw [bindSkip stV base (Nat.ne_of_lt hs_lt)]; exact hs
      rw [evalCode, evalEqU64 _ st stV cur step.fromState.toUInt64 hs1]
      dsimp only
      cases hmatch : (cur == step.fromState.toUInt64) with
      | true =>
        rw [ite_eq_left rfl, evalCode, VarEnv.bind_self]
        dsimp only
        rw [evalCode]
        dsimp only [evalExpr, evalScalarExpr]
        rw [evalCode]
        dsimp only [evalExpr, evalScalarExpr]
        rw [evalCode]
        dsimp only [evalExpr, evalScalarExpr]
        have hv2 : ((((env.bind base (.bool false)).bind (base + 1) (.bool true)).bind
            (base + 2) (.u64 step.outcome.tagBits)).bind (base + 3)
            (.u64 step.toState.toUInt64)) valV = some (.u64 payload) := by
          rw [bindSkip valV (base + 3) (Nat.ne_of_lt (Nat.lt_add_right 3 hv_lt))]
          rw [bindSkip valV (base + 2) (Nat.ne_of_lt (Nat.lt_add_right 2 hv_lt))]
          rw [bindSkip valV (base + 1) (Nat.ne_of_lt (Nat.lt_add_right 1 hv_lt))]
          rw [bindSkip valV base (Nat.ne_of_lt hv_lt)]
          exact hv
        rw [hv2]
        dsimp only [evalBinOp]
        rw [evalCode]
        dsimp only [evalExpr, evalVarList]
        have hrt : (((((env.bind base (.bool false)).bind (base + 1) (.bool true)).bind
            (base + 2) (.u64 step.outcome.tagBits)).bind (base + 3)
            (.u64 step.toState.toUInt64)).bind (base + 4) (.u64 (payload + step.stepDelta)))
            (base + 2) = some (.u64 step.outcome.tagBits) := by
          rw [bindSkip (base + 2) (base + 4) (by omega),
              bindSkip (base + 2) (base + 3) (by omega)]
          exact VarEnv.bind_self _ _ _
        have hrs : (((((env.bind base (.bool false)).bind (base + 1) (.bool true)).bind
            (base + 2) (.u64 step.outcome.tagBits)).bind (base + 3)
            (.u64 step.toState.toUInt64)).bind (base + 4) (.u64 (payload + step.stepDelta)))
            (base + 3) = some (.u64 step.toState.toUInt64) := by
          rw [bindSkip (base + 3) (base + 4) (by omega)]
          exact VarEnv.bind_self _ _ _
        rw [hrt, hrs, VarEnv.bind_self]
        dsimp only
        let eFrm := (((((env.bind base (.bool false)).bind (base + 1) (.bool true)).bind
          (base + 2) (.u64 step.outcome.tagBits)).bind (base + 3)
          (.u64 step.toState.toUInt64)).bind (base + 4) (.u64 (payload + step.stepDelta))).bind
          (base + 8) (.tuple [.u64 step.outcome.tagBits, .u64 step.toState.toUInt64,
            .u64 (payload + step.stepDelta)])
        change evalCode fuel eFrm st _ = _
        have hfrm0 : eFrm (base + 8) =
            some (.tuple [.u64 step.outcome.tagBits, .u64 step.toState.toUInt64,
              .u64 (payload + step.stepDelta)]) := VarEnv.bind_self _ _ _
        rw [evalCode, evalProj3_0 eFrm st (base + 8) _ _ _ hfrm0]
        dsimp only
        have hfrm1 : (eFrm.bind (base + 9) (.u64 step.outcome.tagBits)) (base + 8) =
            some (.tuple [.u64 step.outcome.tagBits, .u64 step.toState.toUInt64,
              .u64 (payload + step.stepDelta)]) := by
          rw [bindSkip (base + 8) (base + 9) (by omega)]; exact hfrm0
        rw [evalCode, evalProj3_1 _ st (base + 8) _ _ _ hfrm1]
        dsimp only
        have hfrm2 : ((eFrm.bind (base + 9) (.u64 step.outcome.tagBits)).bind (base + 10)
            (.u64 step.toState.toUInt64)) (base + 8) =
            some (.tuple [.u64 step.outcome.tagBits, .u64 step.toState.toUInt64,
              .u64 (payload + step.stepDelta)]) := by
          rw [bindSkip (base + 8) (base + 10) (by omega)]; exact hfrm1
        rw [evalCode, evalProj3_2 _ st (base + 8) _ _ _ hfrm2]
        dsimp only
        refine ih _ (base + 9) (base + 10) (base + 11) (base + 12)
          step.outcome.tagBits step.toState.toUInt64 (payload + step.stepDelta)
          (by omega) (by omega) (by omega) ?_ ?_ (VarEnv.bind_self _ _ _)
        · rw [bindSkip (base + 9) (base + 11) (by omega),
              bindSkip (base + 9) (base + 10) (by omega)]
          exact VarEnv.bind_self _ _ _
        · rw [bindSkip (base + 10) (base + 11) (by omega)]
          exact VarEnv.bind_self _ _ _
      | false =>
        rw [ite_eq_right Bool.noConfusion, evalCode, VarEnv.bind_self]
        dsimp only
        have ht2 : ((env.bind base (.bool false)).bind (base + 1) (.bool false)) tagV =
            some (.u64 tag) := by
          rw [bindSkip tagV (base + 1) (Nat.ne_of_lt (Nat.lt_add_right 1 ht_lt)),
              bindSkip tagV base (Nat.ne_of_lt ht_lt)]
          exact ht
        rw [evalCode]
        dsimp only [evalExpr, evalScalarExpr]
        rw [ht2]
        dsimp only
        have hs2 : (((env.bind base (.bool false)).bind (base + 1) (.bool false)).bind
            (base + 5) (.u64 tag)) stV = some (.u64 cur) := by
          rw [bindSkip stV (base + 5) (Nat.ne_of_lt (Nat.lt_add_right 5 hs_lt)),
              bindSkip stV (base + 1) (Nat.ne_of_lt (Nat.lt_add_right 1 hs_lt)),
              bindSkip stV base (Nat.ne_of_lt hs_lt)]
          exact hs
        rw [evalCode]
        dsimp only [evalExpr, evalScalarExpr]
        rw [hs2]
        dsimp only
        have hv2 : ((((env.bind base (.bool false)).bind (base + 1) (.bool false)).bind
            (base + 5) (.u64 tag)).bind (base + 6) (.u64 cur)) valV = some (.u64 payload) := by
          rw [bindSkip valV (base + 6) (Nat.ne_of_lt (Nat.lt_add_right 6 hv_lt)),
              bindSkip valV (base + 5) (Nat.ne_of_lt (Nat.lt_add_right 5 hv_lt)),
              bindSkip valV (base + 1) (Nat.ne_of_lt (Nat.lt_add_right 1 hv_lt)),
              bindSkip valV base (Nat.ne_of_lt hv_lt)]
          exact hv
        rw [evalCode]
        dsimp only [evalExpr, evalScalarExpr]
        rw [hv2]
        dsimp only
        rw [evalCode]
        dsimp only [evalExpr, evalVarList]
        have hnt : (((((env.bind base (.bool false)).bind (base + 1) (.bool false)).bind
            (base + 5) (.u64 tag)).bind (base + 6) (.u64 cur)).bind (base + 7) (.u64 payload))
            (base + 5) = some (.u64 tag) := by
          rw [bindSkip (base + 5) (base + 7) (by omega),
              bindSkip (base + 5) (base + 6) (by omega)]
          exact VarEnv.bind_self _ _ _
        have hns : (((((env.bind base (.bool false)).bind (base + 1) (.bool false)).bind
            (base + 5) (.u64 tag)).bind (base + 6) (.u64 cur)).bind (base + 7) (.u64 payload))
            (base + 6) = some (.u64 cur) := by
          rw [bindSkip (base + 6) (base + 7) (by omega)]
          exact VarEnv.bind_self _ _ _
        rw [hnt, hns, VarEnv.bind_self]
        dsimp only
        let eFrm := (((((env.bind base (.bool false)).bind (base + 1) (.bool false)).bind
          (base + 5) (.u64 tag)).bind (base + 6) (.u64 cur)).bind (base + 7) (.u64 payload)).bind
          (base + 8) (.tuple [.u64 tag, .u64 cur, .u64 payload])
        change evalCode fuel eFrm st _ = _
        have hfrm0 : eFrm (base + 8) = some (.tuple [.u64 tag, .u64 cur, .u64 payload]) :=
          VarEnv.bind_self _ _ _
        rw [evalCode, evalProj3_0 eFrm st (base + 8) _ _ _ hfrm0]
        dsimp only
        have hfrm1 : (eFrm.bind (base + 9) (.u64 tag)) (base + 8) =
            some (.tuple [.u64 tag, .u64 cur, .u64 payload]) := by
          rw [bindSkip (base + 8) (base + 9) (by omega)]; exact hfrm0
        rw [evalCode, evalProj3_1 _ st (base + 8) _ _ _ hfrm1]
        dsimp only
        have hfrm2 : ((eFrm.bind (base + 9) (.u64 tag)).bind (base + 10) (.u64 cur)) (base + 8) =
            some (.tuple [.u64 tag, .u64 cur, .u64 payload]) := by
          rw [bindSkip (base + 8) (base + 10) (by omega)]; exact hfrm1
        rw [evalCode, evalProj3_2 _ st (base + 8) _ _ _ hfrm2]
        dsimp only
        refine ih _ (base + 9) (base + 10) (base + 11) (base + 12) tag cur payload
          (by omega) (by omega) (by omega) ?_ ?_ (VarEnv.bind_self _ _ _)
        · rw [bindSkip (base + 9) (base + 11) (by omega),
              bindSkip (base + 9) (base + 10) (by omega)]
          exact VarEnv.bind_self _ _ _
        · rw [bindSkip (base + 10) (base + 11) (by omega)]
          exact VarEnv.bind_self _ _ _

/-- General soundness of `lowerAsyncAwaitChain spec` AND its `optimizeAsyncStateMachine`-unboxed
form over arbitrary well-formed `spec : AsyncCoroutineSpec`: both evaluate to
`.u64 (runAwaitChainPayload spec initVal)` with zero heap allocations (`st` unchanged). -/
theorem lowerAsyncAwaitChain_sound (fuel : Nat) (env : VarEnv) (st : HeapState)
    (spec : AsyncCoroutineSpec) (initVal : UInt64)
    (hreg : spec.inputVar < spec.regBase)
    (hinput : env spec.inputVar = some (.u64 initVal)) :
    evalCode fuel env st (optimizeAsyncStateMachine (lowerAsyncAwaitChain spec)) =
      .ok (.u64 (runAwaitChainPayload spec initVal), st) := by
  have hsrc : evalCode fuel env st (lowerAsyncAwaitChain spec) =
      .ok (.u64 (runAwaitChainPayload spec initVal), st) := by
    unfold lowerAsyncAwaitChain runAwaitChainPayload
    rw [evalCode]
    dsimp only [evalExpr, evalScalarExpr, AsyncPollResult.tagBits]
    rw [evalCode]
    dsimp only [evalExpr, evalScalarExpr]
    rw [evalCode]
    dsimp only [evalExpr, evalVarList]
    have ht0 : ((env.bind spec.regBase (.u64 0)).bind (spec.regBase + 1)
        (.u64 spec.initState.toUInt64)) spec.regBase = some (.u64 0) := by
      rw [bindSkip spec.regBase (spec.regBase + 1) (by omega)]
      exact VarEnv.bind_self _ _ _
    have hs0 : ((env.bind spec.regBase (.u64 0)).bind (spec.regBase + 1)
        (.u64 spec.initState.toUInt64)) (spec.regBase + 1) =
        some (.u64 spec.initState.toUInt64) := VarEnv.bind_self _ _ _
    have hin : ((env.bind spec.regBase (.u64 0)).bind (spec.regBase + 1)
        (.u64 spec.initState.toUInt64)) spec.inputVar = some (.u64 initVal) := by
      rw [bindSkip spec.inputVar (spec.regBase + 1) (Nat.ne_of_lt (Nat.lt_add_right 1 hreg))]
      rw [bindSkip spec.inputVar spec.regBase (Nat.ne_of_lt hreg)]
      exact hinput
    rw [ht0, hs0, hin]
    dsimp only
    let eFrm := ((env.bind spec.regBase (.u64 0)).bind (spec.regBase + 1)
      (.u64 spec.initState.toUInt64)).bind (spec.regBase + 2)
      (.tuple [.u64 0, .u64 spec.initState.toUInt64, .u64 initVal])
    change evalCode fuel eFrm st _ = _
    have hf0 : eFrm (spec.regBase + 2) =
        some (.tuple [.u64 0, .u64 spec.initState.toUInt64, .u64 initVal]) :=
      VarEnv.bind_self _ _ _
    rw [evalCode, evalProj3_0 eFrm st (spec.regBase + 2) _ _ _ hf0]
    dsimp only
    have hf1 : (eFrm.bind (spec.regBase + 3) (.u64 0)) (spec.regBase + 2) =
        some (.tuple [.u64 0, .u64 spec.initState.toUInt64, .u64 initVal]) := by
      rw [bindSkip (spec.regBase + 2) (spec.regBase + 3) (by omega)]; exact hf0
    rw [evalCode, evalProj3_1 _ st (spec.regBase + 2) _ _ _ hf1]
    dsimp only
    have hf2 : ((eFrm.bind (spec.regBase + 3) (.u64 0)).bind (spec.regBase + 4)
        (.u64 spec.initState.toUInt64)) (spec.regBase + 2) =
        some (.tuple [.u64 0, .u64 spec.initState.toUInt64, .u64 initVal]) := by
      rw [bindSkip (spec.regBase + 2) (spec.regBase + 4) (by omega)]; exact hf1
    rw [evalCode, evalProj3_2 _ st (spec.regBase + 2) _ _ _ hf2]
    dsimp only
    refine lowerAsyncAwaitSteps_sound fuel _ st
      (spec.regBase + 3) (spec.regBase + 4) (spec.regBase + 5) (spec.regBase + 6)
      spec.steps 0 spec.initState.toUInt64 initVal
      (by omega) (by omega) (by omega) ?_ ?_ (VarEnv.bind_self _ _ _)
    · rw [bindSkip (spec.regBase + 3) (spec.regBase + 5) (by omega),
          bindSkip (spec.regBase + 3) (spec.regBase + 4) (by omega)]
      exact VarEnv.bind_self _ _ _
    · rw [bindSkip (spec.regBase + 4) (spec.regBase + 5) (by omega)]
      exact VarEnv.bind_self _ _ _
  exact optimizeAsyncStateMachine_refines (lowerAsyncAwaitChain spec) fuel env st _ st hsrc

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
