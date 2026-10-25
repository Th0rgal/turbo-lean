import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics

/-! ## 1. Tuple Unboxing / SROA Soundness (`unboxTupleProj_sound`) -/

/-- Projecting field 0 from a constructed 2-tuple `mkTuple [v0, v1]` bound to `tVar`
    produces the exact same value and heap state as reading `v0` directly in registers. -/
theorem unboxTupleProj0_sound (env : VarEnv) (st : HeapState)
    (tVar v0 v1 : VarId) (val0 val1 : Val)
    (hv0 : env v0 = some val0) (hv1 : env v1 = some val1) :
    (match evalExpr env st (.mkTuple [v0, v1]) with
     | .ok (tVal, st1) => evalExpr (env.bind tVar tVal) st1 (.projTuple tVar 0)
     | .error err => .error err) =
    evalExpr env st (.scalar (.var v0)) := by
  simp [evalExpr, evalVarList, evalScalarExpr, hv0, hv1]

/-- Projecting field 1 from a constructed 2-tuple `mkTuple [v0, v1]` bound to `tVar`
    produces the exact same value and heap state as reading `v1` directly in registers. -/
theorem unboxTupleProj1_sound (env : VarEnv) (st : HeapState)
    (tVar v0 v1 : VarId) (val0 val1 : Val)
    (hv0 : env v0 = some val0) (hv1 : env v1 = some val1) :
    (match evalExpr env st (.mkTuple [v0, v1]) with
     | .ok (tVal, st1) => evalExpr (env.bind tVar tVal) st1 (.projTuple tVar 1)
     | .error err => .error err) =
    evalExpr env st (.scalar (.var v1)) := by
  simp [evalExpr, evalVarList, evalScalarExpr, hv0, hv1]

/-- General Tuple Unboxing / SROA theorem (`unboxTupleProj_sound`):
    For either field `idx ∈ {0, 1}` of a constructed tuple `mkTuple [v0, v1]` in `VarEnv`,
    allocating the tuple and projecting field `idx` equals reading the scalar register `v_idx` directly. -/
theorem unboxTupleProj_sound (env : VarEnv) (st : HeapState)
    (tVar v0 v1 : VarId) (val0 val1 : Val) (b : Bool)
    (hv0 : env v0 = some val0) (hv1 : env v1 = some val1) :
    let idx := if b then 1 else 0
    let targetVar := if b then v1 else v0
    (match evalExpr env st (.mkTuple [v0, v1]) with
     | .ok (tVal, st1) => evalExpr (env.bind tVar tVal) st1 (.projTuple tVar idx)
     | .error err => .error err) =
    evalExpr env st (.scalar (.var targetVar)) := by
  cases b
  · exact unboxTupleProj0_sound env st tVar v0 v1 val0 val1 hv0 hv1
  · exact unboxTupleProj1_sound env st tVar v0 v1 val0 val1 hv0 hv1

/-- Code-level refinement for Tuple Unboxing / SROA (`eval_unboxTupleSROA_refines`). -/
theorem eval_unboxTupleSROA_refines (env : VarEnv) (st : HeapState)
    (tVar v0 : VarId) (val0 val1 : Val)
    (hv0 : env v0 = some val0) :
    evalExpr (env.bind tVar (.tuple [val0, val1])) st (.projTuple tVar 0) =
    evalExpr env st (.scalar (.var v0)) := by
  simp [evalExpr, evalScalarExpr, hv0]

/-! ## 2. Exclusive Array Base-Pointer & Exclusivity Hoisting (`hoistExclusivity_sound`) -/

/-- Predicate stating that every buffer in `bs` with `b.id == bufId` is already marked `exclusive = true`. -/
def BuffersExclusiveFor (bs : List ArrayBuffer) (bufId : Nat) : Prop :=
  ∀ b ∈ bs, (b.id == bufId) = true → b.exclusive = true

theorem map_ensureExclusive_establishes (bs : List ArrayBuffer) (bufId : Nat) :
    BuffersExclusiveFor (bs.map (fun b => if b.id == bufId then { b with exclusive := true } else b)) bufId := by
  intro b hb hid; rw [List.mem_map] at hb; rcases hb with ⟨b0, _, rfl⟩
  by_cases h : (b0.id == bufId) = true
  · simp [h]
  · simp [Bool.eq_false_iff.mpr h] at hid

theorem map_ensureExclusive_idempotent (bs : List ArrayBuffer) (bufId : Nat)
    (hexcl : BuffersExclusiveFor bs bufId) :
    bs.map (fun b => if b.id == bufId then { b with exclusive := true } else b) = bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    have hhead : (if b.id == bufId then { b with exclusive := true } else b) = b := by
      by_cases h : (b.id == bufId) = true
      · have he := hexcl b (List.mem_cons_self ..) h; cases b; simp only at he; simp [h, he]
      · simp [Bool.eq_false_iff.mpr h]
    have hrest : BuffersExclusiveFor rest bufId := fun x hx => hexcl x (List.mem_cons_of_mem b hx)
    simp only [List.map, hhead, ih hrest]

theorem find?_map_preserve_id (bs : List ArrayBuffer) (bufId : Nat) (f : ArrayBuffer → ArrayBuffer)
    (hid : ∀ b, (f b).id = b.id) :
    (bs.map f).find? (fun b => b.id == bufId) = (bs.find? (fun b => b.id == bufId)).map f := by
  induction bs with
  | nil => rfl
  | cons b rest ih => simp only [List.map, List.find?, hid b]; cases b.id == bufId <;> simp [ih]

theorem map_write_preserves_BuffersExclusiveFor (bs : List ArrayBuffer) (bufId : Nat) (idx : Nat) (val : UInt64)
    (hexcl : BuffersExclusiveFor bs bufId) :
    BuffersExclusiveFor (bs.map (fun b => if b.id == bufId then { b with data := b.data.set! idx val } else b)) bufId := by
  intro b hb hid; rw [List.mem_map] at hb; rcases hb with ⟨b0, hb0, rfl⟩
  by_cases h : (b0.id == bufId) = true
  · simp [h, hexcl b0 hb0 h]
  · simp [Bool.eq_false_iff.mpr h] at hid

/-- Ensuring exclusivity on a `HeapState` where `bufId` is present and already exclusive is a no-op. -/
theorem ensureExclusive_of_exclusive (st : HeapState) (bufId : Nat) (buf : ArrayBuffer)
    (hfind : st.findBuffer bufId = some buf)
    (hexcl : BuffersExclusiveFor st.buffers bufId) :
    st.ensureExclusive bufId = .ok st := by
  unfold HeapState.ensureExclusive; rw [hfind]; simp only
  have hmap := map_ensureExclusive_idempotent st.buffers bufId hexcl
  cases st; simp only [hmap]

/-- If `st.ensureExclusive bufId = .ok st1`, then `st1` satisfies `BuffersExclusiveFor` and `findBuffer` succeeds. -/
theorem ensureExclusive_post (st st1 : HeapState) (bufId : Nat)
    (h : st.ensureExclusive bufId = .ok st1) :
    BuffersExclusiveFor st1.buffers bufId ∧ (∃ buf1, st1.findBuffer bufId = some buf1) := by
  unfold HeapState.ensureExclusive at h
  cases hfind : st.findBuffer bufId with
  | none => rw [hfind] at h; contradiction
  | some buf =>
    rw [hfind] at h; injection h with hst1; subst hst1
    refine ⟨map_ensureExclusive_establishes st.buffers bufId, ?_⟩
    unfold HeapState.findBuffer at hfind ⊢
    have hid : ∀ b : ArrayBuffer, (if b.id == bufId then { b with exclusive := true } else b).id = b.id :=
      fun b => by by_cases hb : (b.id == bufId) = true <;> simp [hb]
    rw [find?_map_preserve_id st.buffers bufId _ hid, hfind]; exact ⟨_, rfl⟩

/-- If `st` already satisfies `BuffersExclusiveFor st.buffers bufId`, then `writeElemExclusive` preserves it. -/
theorem writeElemExclusive_preserves (st st' : HeapState) (bufId idx : Nat) (val : UInt64)
    (hexcl : BuffersExclusiveFor st.buffers bufId)
    (hw : st.writeElemExclusive bufId idx val = .ok st') :
    BuffersExclusiveFor st'.buffers bufId ∧ (∃ buf', st'.findBuffer bufId = some buf') := by
  unfold HeapState.writeElemExclusive at hw
  cases hfind : st.findBuffer bufId with
  | none => rw [hfind] at hw; contradiction
  | some buf =>
    rw [hfind] at hw; simp only at hw
    by_cases hex : (!buf.exclusive) = true
    · rw [ite_eq_left hex] at hw; contradiction
    · rw [ite_eq_right hex] at hw
      by_cases hlt : idx < buf.data.size
      · rw [dite_eq_left hlt] at hw; injection hw with hst'; subst hst'
        refine ⟨map_write_preserves_BuffersExclusiveFor st.buffers bufId idx val hexcl, ?_⟩
        unfold HeapState.findBuffer at hfind ⊢
        have hid : ∀ b : ArrayBuffer, (if b.id == bufId then { b with data := b.data.set! idx val } else b).id = b.id :=
          fun b => by by_cases hb : (b.id == bufId) = true <;> simp [hb]
        rw [find?_map_preserve_id st.buffers bufId _ hid, hfind]; exact ⟨_, rfl⟩
      · rw [dite_eq_right hlt] at hw; contradiction

/-- Unoptimized sequence of array writes: checks `ensureExclusive` on every single write step. -/
def applyWritesUnopt (st : HeapState) (bufId : Nat) : List (Nat × UInt64) → Except UBError HeapState
  | [] => st.ensureExclusive bufId
  | (idx, val) :: rest =>
    match st.ensureExclusive bufId with
    | .ok st1 =>
      match st1.writeElemExclusive bufId idx val with
      | .ok st2 => applyWritesUnopt st2 bufId rest
      | .error err => .error err
    | .error err => .error err

/-- Hoisted inner loop of array writes: performs direct `writeElemExclusive` (`rawStore`) without re-checking exclusivity. -/
def applyWritesHoistedLoop (st : HeapState) (bufId : Nat) : List (Nat × UInt64) → Except UBError HeapState
  | [] => .ok st
  | (idx, val) :: rest =>
    match st.writeElemExclusive bufId idx val with
    | .ok st1 => applyWritesHoistedLoop st1 bufId rest
    | .error err => .error err

/-- Hoisted array write sequence: checks `ensureExclusive` ONCE in the loop preheader, then runs `applyWritesHoistedLoop`. -/
def applyWritesHoisted (st : HeapState) (bufId : Nat) (writes : List (Nat × UInt64)) : Except UBError HeapState :=
  match st.ensureExclusive bufId with
  | .ok st1 => applyWritesHoistedLoop st1 bufId writes
  | .error err => .error err

theorem applyWritesUnopt_eq_hoistedLoop (st : HeapState) (bufId : Nat) (writes : List (Nat × UInt64))
    (hexcl : BuffersExclusiveFor st.buffers bufId)
    (hfind : ∃ buf, st.findBuffer bufId = some buf) :
    applyWritesUnopt st bufId writes = applyWritesHoistedLoop st bufId writes := by
  induction writes generalizing st with
  | nil =>
    rcases hfind with ⟨buf, hbuf⟩
    exact ensureExclusive_of_exclusive st bufId buf hbuf hexcl
  | cons w rest ih =>
    rcases w, hfind with ⟨⟨idx, val⟩, ⟨buf, hbuf⟩⟩
    simp only [applyWritesUnopt, applyWritesHoistedLoop, ensureExclusive_of_exclusive st bufId buf hbuf hexcl]
    cases hw : st.writeElemExclusive bufId idx val with
    | error _ => rfl
    | ok st2 =>
      rcases writeElemExclusive_preserves st st2 bufId idx val hexcl hw with ⟨hexcl2, hfind2⟩
      exact ih st2 hexcl2 hfind2

/-- Machine-checked Exclusivity Hoisting theorem (`hoistExclusivity_sound`):
    Ensuring array exclusivity once before a sequence of in-place writes produces the exact
    same `HeapState` (and error behavior) as checking exclusivity before every write! -/
theorem hoistExclusivity_sound (st : HeapState) (bufId : Nat) (writes : List (Nat × UInt64)) :
    applyWritesUnopt st bufId writes = applyWritesHoisted st bufId writes := by
  cases writes with
  | nil => simp only [applyWritesUnopt, applyWritesHoisted, applyWritesHoistedLoop]; cases st.ensureExclusive bufId <;> rfl
  | cons w rest =>
    rcases w with ⟨idx, val⟩
    simp only [applyWritesUnopt, applyWritesHoisted, applyWritesHoistedLoop]
    cases hens : st.ensureExclusive bufId with
    | error _ => rfl
    | ok st1 =>
      simp only; cases hw : st1.writeElemExclusive bufId idx val with
      | error _ => rfl
      | ok st2 =>
        rcases ensureExclusive_post st st1 bufId hens with ⟨hexcl1, _⟩
        rcases writeElemExclusive_preserves st1 st2 bufId idx val hexcl1 hw with ⟨hexcl2, hfind2⟩
        exact applyWritesUnopt_eq_hoistedLoop st2 bufId rest hexcl2 hfind2

/-- Alias for `hoistExclusivity_sound` referenced in architecture documentation (`eval_hoistExclusivity_refines`). -/
theorem eval_hoistExclusivity_refines (st : HeapState) (bufId : Nat) (writes : List (Nat × UInt64)) :
    applyWritesUnopt st bufId writes = applyWritesHoisted st bufId writes :=
  hoistExclusivity_sound st bufId writes

/-! ## 3. Unboxed Loop Accumulator / Induction Equivalence (`unboxedLoopStep_sound`) -/

/-- Machine-checked Unboxed Loop Accumulator & Induction Equivalence theorem (`unboxedLoopStep_sound`):
    If an optimized unboxed loop step body `evalStepTgt` agrees with `evalStepSrc` across all loop states,
    then `evalSeqLoop` over `count` iterations produces the exact same final accumulator value and `HeapState`. -/
theorem unboxedLoopStep_sound (count curIdx : Nat) (idxVar accVar : VarId)
    (accVal : Val) (env : VarEnv) (st : HeapState)
    (evalStepSrc evalStepTgt : VarEnv → HeapState → Except UBError (Val × HeapState))
    (hstep : ∀ stepEnv stepSt, evalStepSrc stepEnv stepSt = evalStepTgt stepEnv stepSt) :
    evalSeqLoop count curIdx idxVar accVar accVal env st evalStepSrc =
    evalSeqLoop count curIdx idxVar accVar accVal env st evalStepTgt := by
  induction count generalizing curIdx accVal st with
  | zero => rfl
  | succ count' ih =>
    simp only [evalSeqLoop, hstep]
    cases evalStepTgt ((env.bind idxVar (.u64 curIdx.toUInt64)).bind accVar accVal) st with
    | error err => rfl
    | ok pair =>
      rcases pair with ⟨nextAcc, st'⟩
      exact ih (curIdx + 1) nextAcc st'

/-- Simulation / refinement form of `unboxedLoopStep_sound`:
    When a boxed loop step wraps its scalar accumulator `acc : UInt64` in a 1-field tuple `.tuple [.u64 acc]`
    and the unboxed loop step keeps `.u64 acc` directly in registers via `stepFn : Nat → UInt64 → HeapState → Except UBError (UInt64 × HeapState)`,
    running `count` iterations of the unboxed loop and wrapping at exit equals running the boxed loop. -/
theorem unboxedLoopAccumulator_sim (count curIdx : Nat) (idxVar accVar : VarId)
    (acc : UInt64) (env : VarEnv) (st : HeapState)
    (stepFn : Nat → UInt64 → HeapState → Except UBError (UInt64 × HeapState)) :
    let evalBoxedStep : VarEnv → HeapState → Except UBError (Val × HeapState) :=
      fun senv sst =>
        match senv idxVar, senv accVar with
        | some (.u64 i), some (.tuple [.u64 a]) =>
          match stepFn i.toNat a sst with
          | .ok (a', sst') => .ok (.tuple [.u64 a'], sst')
          | .error err => .error err
        | _, _ => .error (.typeError "boxed step type mismatch")
    let evalUnboxedStep : VarEnv → HeapState → Except UBError (Val × HeapState) :=
      fun senv sst =>
        match senv idxVar, senv accVar with
        | some (.u64 i), some (.u64 a) =>
          match stepFn i.toNat a sst with
          | .ok (a', sst') => .ok (.u64 a', sst')
          | .error err => .error err
        | _, _ => .error (.typeError "unboxed step type mismatch")
    idxVar ≠ accVar →
    evalSeqLoop count curIdx idxVar accVar (.tuple [.u64 acc]) env st evalBoxedStep =
      match evalSeqLoop count curIdx idxVar accVar (.u64 acc) env st evalUnboxedStep with
      | .ok (v, st') => .ok (.tuple [v], st')
      | .error err => .error err := by
  intro evalBoxedStep evalUnboxedStep hne
  induction count generalizing curIdx acc st with
  | zero => rfl
  | succ count' ih =>
    have hne_beq : (idxVar == accVar) = false := beq_false_of_ne hne
    have hidx : ∀ v, (((env.bind idxVar (.u64 curIdx.toUInt64)).bind accVar v) idxVar) =
        some (.u64 curIdx.toUInt64) := fun _ => by simp [VarEnv.bind, hne_beq]
    have hacc : ∀ v, (((env.bind idxVar (.u64 curIdx.toUInt64)).bind accVar v) accVar) =
        some v := fun _ => by simp [VarEnv.bind]
    simp only [evalSeqLoop, evalBoxedStep, evalUnboxedStep, hidx, hacc]
    cases stepFn curIdx.toUInt64.toNat acc st with
    | error err => rfl
    | ok pair => exact ih (curIdx + 1) pair.1 pair.2

/-! ## 4. End-to-End `CodeRefines` Theorems for Tuple SROA & Preheader Exclusivity Hoisting -/

private theorem unboxTupleLetChain_gen
    (tVar dst v0 v1 targetVar : VarId) (idx : Nat) (tupTy dstTy : LNIRType) (k : LNIRCode)
    (hstep : ∀ (env : VarEnv) (st : HeapState) (val0 val1 : Val),
      env v0 = some val0 → env v1 = some val1 →
      evalExpr (env.bind tVar (.tuple [val0, val1])) st (.projTuple tVar idx) =
      evalExpr (env.bind tVar (.tuple [val0, val1])) st (.scalar (.var targetVar))) :
    CodeRefines
      (.letBind tVar tupTy (.mkTuple [v0, v1]) (.letBind dst dstTy (.projTuple tVar idx) k))
      (.letBind tVar tupTy (.mkTuple [v0, v1]) (.letBind dst dstTy (.scalar (.var targetVar)) k)) := by
  intro fuel env st v st' hsrc
  cases hv0 : env v0
  · simp only [evalCode, evalExpr, evalVarList, hv0] at hsrc; contradiction
  · cases hv1 : env v1
    · simp only [evalCode, evalExpr, evalVarList, hv0, hv1] at hsrc; contradiction
    · rename_i val0 val1
      simp only [evalCode] at hsrc ⊢
      have hmk : evalExpr env st (.mkTuple [v0, v1]) = .ok (.tuple [val0, val1], st) := by
        simp only [evalExpr, evalVarList, hv0, hv1]
      rw [hmk] at hsrc ⊢; simp only at hsrc ⊢
      rw [← hstep env st val0 val1 hv0 hv1]; exact hsrc

/-- End-to-end `CodeRefines` theorem for Tuple Unboxing / SROA on field 0 in a `letBind` chain (`unboxTupleLetChain_refines`). -/
theorem unboxTupleLetChain_refines
    (tVar dst v0 v1 : VarId) (tupTy dstTy : LNIRType) (k : LNIRCode)
    (hne : (v0 == tVar) = false) :
    CodeRefines
      (.letBind tVar tupTy (.mkTuple [v0, v1]) (.letBind dst dstTy (.projTuple tVar 0) k))
      (.letBind tVar tupTy (.mkTuple [v0, v1]) (.letBind dst dstTy (.scalar (.var v0)) k)) :=
  unboxTupleLetChain_gen tVar dst v0 v1 v0 0 tupTy dstTy k fun env _ val0 _ hv0 _ => by
    simp only [evalExpr, evalScalarExpr, VarEnv.bind_self, VarEnv.bind_ne _ _ _ _ hne, hv0]; rfl

/-- End-to-end `CodeRefines` theorem for Tuple Unboxing / SROA on field 1 in a `letBind` chain (`unboxTupleLetChain1_refines`). -/
theorem unboxTupleLetChain1_refines
    (tVar dst v0 v1 : VarId) (tupTy dstTy : LNIRType) (k : LNIRCode)
    (hne : (v1 == tVar) = false) :
    CodeRefines
      (.letBind tVar tupTy (.mkTuple [v0, v1]) (.letBind dst dstTy (.projTuple tVar 1) k))
      (.letBind tVar tupTy (.mkTuple [v0, v1]) (.letBind dst dstTy (.scalar (.var v1)) k)) :=
  unboxTupleLetChain_gen tVar dst v0 v1 v1 1 tupTy dstTy k fun env _ _ val1 _ hv1 => by
    simp only [evalExpr, evalScalarExpr, VarEnv.bind_self, VarEnv.bind_ne _ _ _ _ hne, hv1]; rfl

/-- Full Tuple SROA Dead-Allocation Elimination (`unboxTupleDeadElim_refines`):
    because `evalCode` recurses structurally on `LNIRCode` without `fuel = 0` truncation,
    eliminating the intermediate `.letBind tVar tupTy (.mkTuple [v0, v1])` allocation altogether
    when projecting field 0 and returning `dst` refines the original code. -/
theorem unboxTupleDeadElim_refines
    (tVar dst v0 v1 : VarId) (tupTy dstTy : LNIRType) :
    CodeRefines
      (.letBind tVar tupTy (.mkTuple [v0, v1])
        (.letBind dst dstTy (.projTuple tVar 0) (.ret dst)))
      (.letBind dst dstTy (.scalar (.var v0)) (.ret dst)) := by
  intro fuel env st v st' hsrc
  simp only [evalCode, evalExpr, evalVarList] at hsrc ⊢
  cases hv0 : env v0 <;> cases hv1 : env v1 <;>
    simp only [hv0, hv1, evalScalarExpr, VarEnv.bind_self] at hsrc ⊢ <;> first | contradiction | exact hsrc

/-- Nested 2-Level Tuple SROA Dead-Allocation Elimination (`unboxNestedTupleDeadElim_refines`):
    eliminating both an inner tuple `tInner := mkTuple [v1, v2]` and an outer tuple
    `tOuter := mkTuple [v0, tInner]` along with the chained projections `pInner := projTuple tOuter 1`
    and `dst := projTuple pInner 0` refines directly to reading scalar register `v1`. -/
theorem unboxNestedTupleDeadElim_refines
    (tInner tOuter pInner dst v0 v1 v2 : VarId) (innerTy outerTy dstTy : LNIRType)
    (hne0 : (tInner == v0) = false) :
    CodeRefines
      (.letBind tInner innerTy (.mkTuple [v1, v2])
        (.letBind tOuter outerTy (.mkTuple [v0, tInner])
          (.letBind pInner innerTy (.projTuple tOuter 1)
            (.letBind dst dstTy (.projTuple pInner 0) (.ret dst)))))
      (.letBind dst dstTy (.scalar (.var v1)) (.ret dst)) := by
  intro fuel env st v st' hsrc
  simp only [evalCode, evalExpr, evalVarList] at hsrc ⊢
  cases hv1 : env v1 <;> cases hv2 : env v2 <;> try (simp only [hv1, hv2] at hsrc; contradiction)
  rename_i val1 val2
  have hv0_bind : (env.bind tInner (.tuple [val1, val2])) v0 = env v0 :=
    VarEnv.bind_ne env tInner v0 _ (by rw [Bool.beq_comm]; exact hne0)
  cases hv0 : env v0 <;> simp only [hv0, hv1, hv2, hv0_bind, VarEnv.bind_self, evalScalarExpr] at hsrc ⊢ <;>
    first | contradiction | exact hsrc

theorem varEnv_bind_idem (env : VarEnv) (x : VarId) (v : Val) :
    (env.bind x v).bind x v = env.bind x v := by
  funext y; simp only [VarEnv.bind]; cases y == x <;> rfl

/-- End-to-end `CodeRefines` theorem for Preheader Exclusivity Hoisting (`hoistExclusivityPreheader_refines`):
    Once `sarrayEnsureExclusive arrVar elemTy` is bound to `exclVar` in the loop preheader,
    replacing an in-place `.letBind exclVar (.sarray elemTy) (.sarraySet exclVar idxVar valVar elemTy) k`
    with a direct unboxed `.rawStore exclVar idxVar valVar elemTy k` refines the original `LNIRCode` block
    for any continuation `k : LNIRCode`. -/
theorem hoistExclusivityPreheader_refines
    (arrVar exclVar idxVar valVar : VarId) (elemTy : LNIRType) (k : LNIRCode) :
    CodeRefines
      (.letBind exclVar (.sarray elemTy) (.sarrayEnsureExclusive arrVar elemTy)
        (.letBind exclVar (.sarray elemTy) (.sarraySet exclVar idxVar valVar elemTy) k))
      (.letBind exclVar (.sarray elemTy) (.sarrayEnsureExclusive arrVar elemTy)
        (.rawStore exclVar idxVar valVar elemTy k)) := by
  intro fuel env st v st' hsrc
  simp only [evalCode, evalExpr] at hsrc ⊢
  cases harr : env arrVar with
  | none => simp only [harr] at hsrc; contradiction
  | some aval =>
    cases aval <;> try (simp only [harr] at hsrc; contradiction)
    rename_i bufId; simp only [harr] at hsrc ⊢
    cases hens : st.ensureExclusive bufId with
    | error _ => simp only [hens] at hsrc; contradiction
    | ok st1 =>
      rcases ensureExclusive_post st st1 bufId hens with ⟨hexcl1, ⟨buf1, hfind1⟩⟩
      have hens1 := ensureExclusive_of_exclusive st1 bufId buf1 hfind1 hexcl1
      simp only [hens, VarEnv.bind_self] at hsrc ⊢
      cases hidx : (env.bind exclVar (.sarrayId bufId)) idxVar with
      | none => simp only [hidx] at hsrc; contradiction
      | some ival =>
        cases hval : (env.bind exclVar (.sarrayId bufId)) valVar with
        | none => simp only [hidx, hval] at hsrc; contradiction
        | some vval =>
          cases ival <;> cases vval <;> try (simp only [hidx, hval] at hsrc; contradiction)
          simp only [hidx, hval, hens1] at hsrc ⊢
          cases hw : st1.writeElemExclusive _ _ _ <;> simp only [hw, varEnv_bind_idem] at hsrc ⊢ <;> exact hsrc

namespace LoopOptProofs
  abbrev unboxTupleProj0_sound := @LeanNative.Proofs.unboxTupleProj0_sound
  abbrev unboxTupleProj1_sound := @LeanNative.Proofs.unboxTupleProj1_sound
  abbrev unboxTupleProj_sound := @LeanNative.Proofs.unboxTupleProj_sound
  abbrev eval_unboxTupleSROA_refines := @LeanNative.Proofs.eval_unboxTupleSROA_refines
  abbrev unboxTupleLetChain_refines := @LeanNative.Proofs.unboxTupleLetChain_refines
  abbrev unboxTupleLetChain1_refines := @LeanNative.Proofs.unboxTupleLetChain1_refines
  abbrev unboxTupleDeadElim_refines := @LeanNative.Proofs.unboxTupleDeadElim_refines
  abbrev unboxNestedTupleDeadElim_refines := @LeanNative.Proofs.unboxNestedTupleDeadElim_refines
  abbrev hoistExclusivity_sound := @LeanNative.Proofs.hoistExclusivity_sound
  abbrev eval_hoistExclusivity_refines := @LeanNative.Proofs.eval_hoistExclusivity_refines
  abbrev hoistExclusivityPreheader_refines := @LeanNative.Proofs.hoistExclusivityPreheader_refines
  abbrev unboxedLoopStep_sound := @LeanNative.Proofs.unboxedLoopStep_sound
  abbrev unboxedLoopAccumulator_sim := @LeanNative.Proofs.unboxedLoopAccumulator_sim
end LoopOptProofs

end LeanNative.Proofs
