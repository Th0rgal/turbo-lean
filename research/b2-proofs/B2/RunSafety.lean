import B2.CollatzClif

namespace B2.RunSafety

/-- A terminating CLIF run excludes trap/stuck outcomes at every fuel, including prefixes.
This is a generic fact about the upstream executable semantics, for use after O3. -/
theorem of_returned (env : Clif.Env) (p : Clif.Program)
    (n : Nat) (s : Clif.State) (vs : List Clif.Val) (m : Clif.Mem)
    (h : Clif.runLoop env p n s = .returned vs m) (fuel : Nat) :
    (∀ c, Clif.runLoop env p fuel s ≠ .trapped c) ∧
    (∀ msg, Clif.runLoop env p fuel s ≠ .stuck msg) := by
  induction fuel generalizing n s with
  | zero => simp [Clif.runLoop]
  | succ fuel ih =>
    cases n with
    | zero => simp [Clif.runLoop] at h
    | succ n =>
      cases hs : Clif.step env p s with
      | next t =>
        simp only [Clif.runLoop_succ, hs] at h ⊢
        exact ih n t h
      | done vals mem => simp [Clif.runLoop_succ, hs]
      | trapped c => simp [Clif.runLoop_succ, hs] at h
      | stuck msg => simp [Clif.runLoop_succ, hs] at h

theorem collatz_prefix (env : Clif.Env) (p : Clif.Program) (m : Clif.Mem)
    (n steps : UInt64) (fuel : Nat) :
    let s := B2.CollatzClif.entryState (B2.CollatzClif.argumentRegs n steps) m
    (∀ c, Clif.runLoop env p fuel s ≠ .trapped c) ∧
    (∀ msg, Clif.runLoop env p fuel s ≠ .stuck msg) := by
  apply of_returned env p (15 * steps.toNat + 5)
  exact B2.CollatzClif.from_entry env p _ m n steps
    (by simp [B2.CollatzClif.argumentRegs, Clif.Regs.set])
    (by simp [B2.CollatzClif.argumentRegs, Clif.Regs.set])

#print axioms collatz_prefix
#print axioms of_returned
end B2.RunSafety
