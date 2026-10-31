import B2.RunSafety
import B2.CallFree
import FV.E2E.Statement

/-! O3/O4 in the exact entry/reachability contracts consumed by clifv's backend theorem. -/
namespace B2.BackendEntry
open Clif B2.CollatzClif Backend.Proof.Driver
attribute [local irreducible] B2.Smoke.collatz
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem xholds_cv_iff (n : UInt64) (x : BitVec 64) :
    E2E.XHolds (cv n) x ↔ x = n.toBitVec := by
  simpa [cv, Clif.Ty.width] using
    (E2E.XHolds_iff (v := cv n) (x := x) (Nat.le_refl 64))

theorem entry_eq (n steps : UInt64) (cs : State)
    (hcs : E2E.ClifEntry B2.Smoke.collatz [cv n, cv steps] cs) :
    cs = entryState (argumentRegs n steps) cs.mem := by
  obtain ⟨b, hb, hbody, hterm, _, hregs⟩ := hcs.entry
  rw [generated_entry] at hb
  cases Option.some.inj hb
  have hr : cs.frame.regs = argumentRegs n steps := by
    simpa only [entryBlock, List.map_cons, List.map_nil, Regs.setMany_cons,
      Regs.setMany_nil, argumentRegs, Option.some.injEq] using hregs.symm
  have hslots : cs.frame.slots = [] := by
    simpa only [generated_slots, List.map_nil, List.map_eq_nil_iff] using hcs.slotIds
  have hf := hcs.func
  have hc := hcs.callers
  rcases cs with ⟨⟨func, regs, slots, body, term⟩, callers, mem⟩
  simp_all [entryState]

theorem returns (env : Clif.Env) (p : Program) (n steps : UInt64) (cs : State)
    (hcs : E2E.ClifEntry B2.Smoke.collatz [cv n, cv steps] cs) :
    runLoop env p (15 * steps.toNat + 5) cs =
      .returned [cv (Nat.repeat B2.CollatzSource.step steps.toNat n)] cs.mem.leave := by
  rw [entry_eq n steps cs hcs]
  exact from_entry env p _ _ n steps
    (by simp [argumentRegs, Regs.set]) (by simp [argumentRegs, Regs.set])

/-- Termination transfers along the upstream reachability relation. -/
theorem returning_reach {env : Clif.Env} {p : Program} {cs s : State}
    (hr : Reach env p cs s) {fuel : Nat} {vs : List Clif.Val} {m : Mem}
    (h : runLoop env p fuel cs = .returned vs m) :
    ∃ fuel', runLoop env p fuel' s = .returned vs m := by
  induction hr generalizing fuel with
  | refl => exact ⟨fuel, h⟩
  | step hs _ ih =>
    cases fuel with
    | zero => cases h
    | succ fuel => exact ih (by simpa only [runLoop_succ, hs] using h)

theorem reachable_step_safe {env : Clif.Env} {p : Program} {cs s : State}
    (hr : Reach env p cs s) {fuel : Nat} {vs : List Clif.Val} {m : Mem}
    (h : runLoop env p fuel cs = .returned vs m) :
    (∀ c, Clif.step env p s ≠ .trapped c) ∧
    (∀ msg, Clif.step env p s ≠ .stuck msg) := by
  obtain ⟨fuel', h'⟩ := returning_reach hr h
  have safe := B2.RunSafety.of_returned env p fuel' s vs m h' 1
  constructor
  · intro c hc
    exact safe.1 c (by simp [runLoop, hc])
  · intro msg hm
    exact safe.2 msg (by simp [runLoop, hm])

theorem traps_explicit (env : Clif.Env) (p : Program) (n steps : UInt64) (cs : State)
    (hcs : E2E.ClifEntry B2.Smoke.collatz [cv n, cv steps] cs) :
    E2E.TrapsExplicit env p cs := by
  apply E2E.TrapsExplicit.of_tryFree
  · rw [hcs.func]
    exact B2.CallFree.try_free
  · rw [hcs.func]
    exact B2.CallFree.no_indirect_stmt
  · intro s c st rest hr ht _
    exact ((reachable_step_safe hr (returns env p n steps cs hcs)).1 c ht).elim

#print axioms xholds_cv_iff
#print axioms entry_eq
#print axioms returns
#print axioms reachable_step_safe
#print axioms traps_explicit
end B2.BackendEntry
