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

def testedState (r : Regs) (m : Mem) : State :=
  { frame := { func := B2.Smoke.collatz, regs := r.set 5 (Val.ofBool true), slots := []
               body := [], term := headerBlock.term }
    callers := [], mem := m }

theorem header_test (env : Clif.Env) (p : Program) (r : Regs) (m : Mem)
    (i bound : UInt64) (hi : i < bound)
    (h1 : r 1 = some (cv bound)) (h3 : r 3 = some (cv i)) :
    Clif.step env p (headerState r m) = .next (testedState r m) := by
  have hlt : i.toBitVec.ult bound.toBitVec = true := by exact decide_eq_true hi
  simp [headerState, headerBlock, testedState, Clif.step, evalInst,
    Frame.getAs, Frame.get, Val.as?, StepResult.ofRes, Res.ofOption, bind, Res.bind, continueWith, Regs.setMany,
    Sem.icmp, Sem.intcc, Sem.bool8, h1, h3, cv, Val.ofBool]
  change r.set 5 (Val.ofBool (i.toBitVec.ult bound.toBitVec)) = r.set 5 (Val.ofBool true)
  rw [hlt]

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

#print axioms generated_blocks
#print axioms div_two
#print axioms header_taken
end B2.CollatzClif
