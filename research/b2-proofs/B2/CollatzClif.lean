import B2.Smoke
import B2.CollatzSource

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace B2.CollatzClif
open Clif

/-- Inspected block shapes, checked equal to the output of the real lowerDecl below. -/
def entryBlock : Block :=
  { id := 0, params := [(0, .i64), (1, .i64)]
    body := [⟨[2], .iconst .i64 0#64⟩], term := .jump ⟨1, [2, 0]⟩ }

def headerBlock : Block :=
  { id := 1, params := [(3, .i64), (4, .i64)]
    body := [⟨[5], .icmp .ult .i64 3 1⟩], term := .brif 5 ⟨2, []⟩ ⟨3, []⟩ }

def bodyBlock : Block :=
  { id := 2
    body := [⟨[6], .iconst .i64 2#64⟩, ⟨[7], .binary .imul .i64 4 6⟩,
      ⟨[8], .binary .iadd .i64 7 4⟩, ⟨[9], .iconst .i64 1#64⟩,
      ⟨[10], .binary .iadd .i64 8 9⟩, ⟨[11], .iconst .i64 2#64⟩,
      ⟨[12], .iconst .i64 1#64⟩, ⟨[13], .binary .ushr .i64 10 12⟩,
      ⟨[14], .iconst .i64 0#64⟩, ⟨[15], .binary .iadd .i64 13 14⟩,
      ⟨[16], .iconst .i64 1#64⟩, ⟨[17], .binary .iadd .i64 3 16⟩]
    term := .jump ⟨1, [17, 15]⟩ }

def exitBlock : Block := { id := 3, term := .ret [4] }

theorem generated_blocks :
    B2.Smoke.collatz.blocks = [entryBlock, headerBlock, bodyBlock, exitBlock] := by decide +kernel

theorem generated_sig : B2.Smoke.collatz.sig =
    { params := [⟨.i64, .none, .normal⟩, ⟨.i64, .none, .normal⟩]
      returns := [⟨.i64, .none, .normal⟩] } := by decide +kernel

def cv (n : UInt64) : Clif.Val := ⟨.i64, n.toBitVec⟩

theorem div_two (x : UInt64) :
    (x / 2).toBitVec = Clif.Sem.ushr x.toBitVec 1#64 := by
  rw [UInt64.toBitVec_div]
  simpa [Clif.Sem.ushr, Clif.Sem.shiftAmt, BitVec.twoPow] using
    (BitVec.udiv_twoPow_eq_of_lt (x := x.toBitVec) (k := 1) (by decide))

def headerState (r : Regs) (m : Mem) : State :=
  { frame := { func := B2.Smoke.collatz, regs := r, slots := []
               body := headerBlock.body, term := headerBlock.term }
    callers := [], mem := m }

def afterIteration (r : Regs) (i x : UInt64) : Regs :=
  [(5, Val.ofBool true), (6, cv 2), (7, cv (x * 2)), (8, cv (x * 2 + x)),
    (9, cv 1), (10, cv (x * 2 + x + 1)), (11, cv 2), (12, cv 1),
    (13, cv ((x * 2 + x + 1) / 2)), (14, cv 0), (15, cv (B2.CollatzSource.step x)),
    (16, cv 1), (17, cv (i + 1)), (3, cv (i + 1)), (4, cv (B2.CollatzSource.step x))].foldl
      (fun regs (id, val) => regs.set id val) r

theorem after_iteration_live (r : Regs) (i x : UInt64) :
    afterIteration r i x 1 = r 1 ∧
    afterIteration r i x 3 = some (cv (i + 1)) ∧
    afterIteration r i x 4 = some (cv (B2.CollatzSource.step x)) := by
  simp [afterIteration, Regs.set]

def bodyState (r : Regs) (m : Mem) : State :=
  { frame := { func := B2.Smoke.collatz, regs := r, slots := []
               body := bodyBlock.body, term := bodyBlock.term }
    callers := [], mem := m }

def testedState (r : Regs) (m : Mem) (flag : Bool := true) : State :=
  { frame := { func := B2.Smoke.collatz, regs := r.set 5 (Val.ofBool flag), slots := []
               body := [], term := headerBlock.term }
    callers := [], mem := m }

set_option backward.isDefEq.respectTransparency false in
theorem header_compare (env : Clif.Env) (p : Program) (r : Regs) (m : Mem)
    (i bound : UInt64) (h1 : r 1 = some (cv bound)) (h3 : r 3 = some (cv i)) :
    Clif.step env p (headerState r m) =
      .next (testedState r m (i.toBitVec.ult bound.toBitVec)) := by
  simp [headerState, headerBlock, testedState, Clif.step, evalInst,
    Frame.getAs, Frame.get, Val.as?, StepResult.ofRes, Res.ofOption, bind, Res.bind,
    continueWith, Regs.setMany, Sem.icmp, Sem.intcc, Sem.bool8, h1, h3, cv, Val.ofBool]

theorem header_test (env : Clif.Env) (p : Program) (r : Regs) (m : Mem)
    (i bound : UInt64) (hi : i < bound)
    (h1 : r 1 = some (cv bound)) (h3 : r 3 = some (cv i)) :
    Clif.step env p (headerState r m) = .next (testedState r m) := by
  have hlt : i.toBitVec.ult bound.toBitVec = true := by exact decide_eq_true hi
  simpa only [hlt] using header_compare env p r m i bound h1 h3

theorem header_branch (env : Clif.Env) (p : Program) (r : Regs) (m : Mem) :
    Clif.step env p (testedState r m) = .next (bodyState (r.set 5 (Val.ofBool true)) m) := by
  simp [Ty.width, testedState, headerBlock, Clif.step, stepTerm, Frame.get, Regs.set,
    Sem.truthy, enterBlock, Function.block?, generated_blocks, bodyBlock, entryBlock,
    exitBlock, checkTys, Res.check, bind, Res.bind, Res.ofOption, StepResult.ofRes,
    bodyState, Frame.getMany, Regs.setMany, Val.ofBool, List.find?]

theorem header_taken (env : Clif.Env) (p : Program) (r : Regs) (m : Mem)
    (i bound : UInt64) (hi : i < bound)
    (h1 : r 1 = some (cv bound)) (h3 : r 3 = some (cv i)) (fuel : Nat) :
    runLoop env p (fuel + 2) (headerState r m) =
      runLoop env p fuel (bodyState (r.set 5 (Val.ofBool true)) m) := by
  rw [show fuel + 2 = (fuel + 1) + 1 from rfl, runLoop_succ,
    header_test env p r m i bound hi h1 h3]
  change runLoop env p (fuel + 1) (testedState r m) = _
  rw [runLoop_succ, header_branch]

-- Let simp compare dependent widths such as Ty.i64.width with 64; kernel checking is unchanged.
set_option backward.isDefEq.respectTransparency false in
theorem body_backedge (env : Clif.Env) (p : Program) (r : Regs) (m : Mem)
    (i x : UInt64) (h3 : r 3 = some (cv i)) (h4 : r 4 = some (cv x)) (fuel : Nat) :
    runLoop env p (fuel + 13) (bodyState (r.set 5 (Val.ofBool true)) m) =
      runLoop env p fuel (headerState (afterIteration r i x) m) := by
  simp [-Nat.succ_eq_add_one, Nat.add_succ, Nat.add_zero, runLoop_succ, Ty.width,
    bodyState, headerState, bodyBlock, headerBlock, entryBlock, exitBlock,
    Clif.step, stepTerm, evalInst, Frame.getAs, Frame.get, Frame.getMany,
    Val.as?, StepResult.ofRes, Res.ofOption, bind, Res.bind,
    enterBlock, Function.block?, generated_blocks, continueWith,
    Regs.setMany, Regs.set, checkTys, Res.check, BinaryOp.isShift,
    Sem.binary, Sem.shift, Sem.iadd, Sem.imul, Sem.ushr, Sem.shiftAmt,
    afterIteration, cv, B2.CollatzSource.step, List.find?, h3, h4,
    UInt64.toBitVec_add, UInt64.toBitVec_mul, BitVec.add_zero, -UInt64.toBitVec_div, div_two]

theorem iteration (env : Clif.Env) (p : Program) (r : Regs) (m : Mem)
    (i x bound : UInt64) (hi : i < bound)
    (h1 : r 1 = some (cv bound)) (h3 : r 3 = some (cv i)) (h4 : r 4 = some (cv x))
    (fuel : Nat) :
    runLoop env p (fuel + 15) (headerState r m) =
      runLoop env p fuel (headerState (afterIteration r i x) m) := by
  rw [show fuel + 15 = (fuel + 13) + 2 by omega,
    header_taken env p r m i bound hi h1 h3]
  exact body_backedge env p r m i x h3 h4 fuel

def exitState (r : Regs) (m : Mem) : State :=
  { frame := { func := B2.Smoke.collatz, regs := r, slots := []
               body := [], term := exitBlock.term }
    callers := [], mem := m }

set_option backward.isDefEq.respectTransparency false in
theorem header_exit_branch (env : Clif.Env) (p : Program) (r : Regs) (m : Mem) :
    Clif.step env p (testedState r m false) =
      .next (exitState (r.set 5 (Val.ofBool false)) m) := by
  simp [Ty.width, testedState, headerBlock, Clif.step, stepTerm, Frame.get, Regs.set,
    Sem.truthy, enterBlock, Function.block?, generated_blocks, bodyBlock, entryBlock,
    exitBlock, checkTys, Res.check, bind, Res.bind, Res.ofOption, StepResult.ofRes,
    exitState, Frame.getMany, Regs.setMany, Val.ofBool, List.find?]

set_option backward.isDefEq.respectTransparency false in
theorem exit_return (env : Clif.Env) (p : Program) (r : Regs) (m : Mem)
    (x : UInt64) (h4 : r 4 = some (cv x)) :
    Clif.step env p (exitState r m) = .done [cv x] m.leave := by
  simp [exitState, exitBlock, Clif.step, stepTerm, returnValues,
    Frame.getMany, Frame.get, h4, cv, StepResult.ofRes, Res.ofOption,
    bind, Res.bind, checkTys, Res.check, generated_sig, AbiParam.tys, Mem.free]
  rw [show m.allocs.filter (fun _ => true) = m.allocs from
    List.filter_eq_self.mpr (fun _ _ => rfl)]

theorem header_finished (env : Clif.Env) (p : Program) (r : Regs) (m : Mem)
    (i x bound : UInt64) (hi : ¬ i < bound)
    (h1 : r 1 = some (cv bound)) (h3 : r 3 = some (cv i)) (h4 : r 4 = some (cv x)) :
    runLoop env p 3 (headerState r m) = .returned [cv x] m.leave := by
  have hlt : i.toBitVec.ult bound.toBitVec = false := by exact decide_eq_false hi
  rw [show 3 = 2 + 1 from rfl, runLoop_succ, header_compare env p r m i bound h1 h3, hlt]
  change runLoop env p 2 (testedState r m false) = _
  rw [show 2 = 1 + 1 from rfl, runLoop_succ, header_exit_branch]
  change runLoop env p 1 (exitState (r.set 5 (Val.ofBool false)) m) = _
  rw [show 1 = 0 + 1 from rfl, runLoop_succ, exit_return env p _ m x (by simpa [Regs.set] using h4)]

theorem loop_returns (env : Clif.Env) (p : Program) (m : Mem) (count : Nat)
    (r : Regs) (i x bound : UInt64) (hcount : i.toNat + count = bound.toNat)
    (h1 : r 1 = some (cv bound)) (h3 : r 3 = some (cv i)) (h4 : r 4 = some (cv x)) :
    runLoop env p (15 * count + 3) (headerState r m) =
      .returned [cv (Nat.repeat B2.CollatzSource.step count x)] m.leave := by
  induction count generalizing r i x with
  | zero =>
    have eq : i = bound := UInt64.toNat_inj.mp (by simpa using hcount)
    simpa only [Nat.mul_zero, Nat.zero_add, Nat.repeat] using
      header_finished env p r m i x bound (by simp [eq]) h1 h3 h4
  | succ count ih =>
    have hi : i < bound := by
      rw [UInt64.lt_iff_toNat_lt]
      omega
    have hnext : (i + 1).toNat + count = bound.toNat := by
      have hmax := bound.toNat_lt_size
      have hsmall : i.toNat + 1 < 2^64 := by
        change bound.toNat < 2^64 at hmax
        omega
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat, Nat.reduceMod]
      rw [Nat.mod_eq_of_lt hsmall]
      omega
    rw [show 15 * (count + 1) + 3 = (15 * count + 3) + 15 by omega,
      iteration env p r m i x bound hi h1 h3 h4]
    have live := after_iteration_live r i x
    simpa only [Nat.repeat, B2.CollatzSource.repeat_step] using
      ih (afterIteration r i x) (i + 1) (B2.CollatzSource.step x) hnext
        (live.1.trans h1) live.2.1 live.2.2

def entryState (r : Regs) (m : Mem) : State :=
  { frame := { func := B2.Smoke.collatz, regs := r, slots := []
               body := entryBlock.body, term := entryBlock.term }
    callers := [], mem := m }

def afterEntry (r : Regs) (n : UInt64) : Regs :=
  ((r.set 2 (cv 0)).set 3 (cv 0)).set 4 (cv n)

set_option backward.isDefEq.respectTransparency false in
theorem entry_advance (env : Clif.Env) (p : Program) (r : Regs) (m : Mem)
    (n : UInt64) (h0 : r 0 = some (cv n)) (fuel : Nat) :
    runLoop env p (fuel + 2) (entryState r m) =
      runLoop env p fuel (headerState (afterEntry r n) m) := by
  simp [-Nat.succ_eq_add_one, Nat.add_succ, Nat.add_zero, runLoop_succ, Ty.width,
    entryState, entryBlock, headerState, headerBlock, bodyBlock, exitBlock,
    Clif.step, stepTerm, evalInst, Frame.getMany, Frame.get, StepResult.ofRes,
    Res.ofOption, bind, Res.bind, enterBlock, Function.block?, generated_blocks,
    continueWith, Regs.setMany, Regs.set, checkTys, Res.check, afterEntry, cv, List.find?, h0]

theorem from_entry (env : Clif.Env) (p : Program) (r : Regs) (m : Mem)
    (n steps : UInt64) (h0 : r 0 = some (cv n)) (h1 : r 1 = some (cv steps)) :
    runLoop env p (15 * steps.toNat + 5) (entryState r m) =
      .returned [cv (Nat.repeat B2.CollatzSource.step steps.toNat n)] m.leave := by
  rw [show 15 * steps.toNat + 5 = (15 * steps.toNat + 3) + 2 by omega,
    entry_advance env p r m n h0]
  exact loop_returns env p m steps.toNat (afterEntry r n) 0 n steps (by simp)
    (by simpa [afterEntry, Regs.set] using h1)
    (by simp [afterEntry, Regs.set]) (by simp [afterEntry, Regs.set])

theorem generated_entry : B2.Smoke.collatz.entry? = some entryBlock := by decide +kernel

theorem generated_slots : B2.Smoke.collatz.slots = [] := by decide +kernel

def argumentRegs (n steps : UInt64) : Regs :=
  (Regs.empty.set 0 (cv n)).set 1 (cv steps)

theorem entered_slots (m : Mem) : (enterSlots B2.Smoke.collatz m).1 = [] := by
  simp only [enterSlots, generated_slots]
  split
  · rfl
  · split <;> simp [bumpSlots, placeSlots]

theorem enter_function (n steps : UInt64) (m : Mem) :
    enterFunc B2.Smoke.collatz [cv n, cv steps] m =
      .ok ((entryState (argumentRegs n steps) (enterSlots B2.Smoke.collatz m).2).frame,
        (enterSlots B2.Smoke.collatz m).2) := by
  simp [enterFunc, generated_sig, generated_entry, entered_slots, AbiParam.tys,
    checkTys, Res.check, bind, Res.bind, Res.ofOption, entryBlock,
    Regs.setMany, argumentRegs, entryState, cv]

theorem run_with (env : Clif.Env) (p : Program) (m : Mem) (n steps : UInt64)
    (hp : p.func? B2.Smoke.collatz.name = some B2.Smoke.collatz) :
    runWith env p B2.Smoke.collatz.name [cv n, cv steps] m (15 * steps.toNat + 5) =
      .returned [cv (Nat.repeat B2.CollatzSource.step steps.toNat n)]
        (enterSlots B2.Smoke.collatz m).2.leave := by
  simp only [runWith, initState, hp, Res.ofOption, bind, Res.bind, enter_function]
  exact from_entry env p (argumentRegs n steps) _ n steps
    (by simp [argumentRegs, Regs.set]) (by simp [argumentRegs, Regs.set])

/-- O3 for the actual LNIR declaration and actual CLIF run, for every UInt64 argument pair. -/
theorem source_simulation (env : Clif.Env) (p : Program) (m : Mem) (n steps : UInt64)
    (hp : p.func? B2.Smoke.collatz.name = some B2.Smoke.collatz)
    (fuel : Nat) (st st' : LeanNative.Semantics.HeapState) (v : LeanNative.Semantics.Val)
    (hev : LeanNative.Semantics.evalCode fuel
      (B2.entryEnv LeanNative.IR.Codec.collatzStepsDecl [.u64 n, .u64 steps]) st
      LeanNative.IR.Codec.collatzStepsDecl.body = .ok (v, st')) :
    ∃ rv, B2.ValRel v rv ∧
      runWith env p B2.Smoke.collatz.name [cv n, cv steps] m (15 * steps.toNat + 5) =
        .returned [rv] (enterSlots B2.Smoke.collatz m).2.leave := by
  rw [B2.CollatzSource.collatz_eval] at hev
  cases hev
  exact ⟨_, rfl, run_with env p m n steps hp⟩

#print axioms generated_blocks
#print axioms div_two
#print axioms header_taken
#print axioms body_backedge
#print axioms iteration
#print axioms header_finished
#print axioms loop_returns
#print axioms from_entry
end B2.CollatzClif
