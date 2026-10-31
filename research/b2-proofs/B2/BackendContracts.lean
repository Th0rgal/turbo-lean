import B2.Artifacts
import B2.CallFree
import FV.E2E.Statement
import FV.E2E.RegLevelCall
import FV.E2E.RegLevelDriverSem
import FV.Backend.Proof.LowerDecide

/-! O5 scope and O6 contracts for the actual backend pipeline. The backend's unconditional
hook/program-preservation clauses remain explicit; absence of call sites discharges `os`. -/
namespace B2.BackendContracts
open Backend Backend.Proof Backend.Proof.Driver E2E
attribute [local irreducible] B2.Smoke.collatz

theorem subset (p : Clif.Program) : InSubset p B2.Smoke.collatz := by
  refine ⟨B2.Lowering.lower_in_subsetE _ _ B2.Smoke.collatz_lowered, ?_, ?_, ?_, ?_⟩
  · intro b hb st hst fn args hi e he
    simp [Clif.Function.extern?, B2.CallFree.declarations.1] at he
  · intro b hb fn args et hi e he
    simp [Clif.Function.extern?, B2.CallFree.declarations.1] at he
  · constructor
    · rw [B2.CollatzClif.generated_sig]
      decide
    · simp [B2.CallFree.declarations.1]
  · simp [B2.CallFree.no_indirect_sigs]

theorem dominated : dominatedB B2.Smoke.collatz = true := by
  rw [← B2.Artifacts.input_eq]
  decide +kernel

theorem scope : lowerScopeB B2.Smoke.collatz = true := by
  rw [← B2.Artifacts.input_eq]
  decide +kernel

theorem prepared_call_free : B2.Artifacts.vcp.blocks.all (fun vb => vb.insts.all
    (fun i => match i with | .call .. | .tryCall .. => false | _ => true)) = true := by
  decide +kernel

theorem no_call_site (info : CallInfo) : ¬ B2.Artifacts.vcp.CallSite info := by
  intro ⟨b, vb, k, hb, hi⟩
  have hblock := Array.all_eq_true'.mp prepared_call_free vb (Array.mem_of_getElem? hb)
  rcases hi with hc | ⟨ti, hc⟩
  · have h := Array.all_eq_true'.mp hblock _ (Array.mem_of_getElem? hc)
    cases h
  · have h := Array.all_eq_true'.mp hblock _ (Array.mem_of_getElem? hc)
    cases h

theorem callee_ok (F : BitVec 64 → Prop) (K : Nat) (X : ExtSem) (H : ArmHooks)
    (hpc : ∀ d s, Arm.r .ERR s = .None → Arm.CheckSPAlignment s →
      Arm.r .PC (H.call d s) = Arm.r .PC s + 4)
    (hext : ∀ d uses w outs w', X.call d uses w = some (outs, w') →
      Arm.r .ERR w = .None → Arm.r .ERR w' = .None ∧ w'.program = w.program) :
    CalleeOk F K X H B2.Artifacts.vcp.CallSite :=
  ⟨fun _ info hi => (no_call_site info hi).elim, hpc, hext⟩

theorem try_contract (Q : Prop) :
    (∃ B ∈ B2.Smoke.collatz.blocks, B.term.isTry = true) → Q := by
  intro ⟨B, hb, ht⟩
  rw [B2.CallFree.try_free B hb] at ht
  cases ht

theorem tls_contract (Q : Prop) : Backend.hasTls B2.Smoke.collatz = true → Q := by
  rw [B2.CallFree.no_tls]
  intro h
  cases h

theorem extern_contract (env : Clif.Env) (MR : MemRelT) (X : ExtSem) :
    XCallsOk env (B2.Smoke.collatz.externs.map (·.2)) MR X := by
  simp [XCallsOk, B2.CallFree.declarations.1]

theorem indirect_contract (env : Clif.Env) (MR : MemRelT) (X : ExtSem) :
    XCallsIndOk env (indSigs B2.Smoke.collatz) MR X := by
  rw [B2.CallFree.no_indirect_sigs]
  exact xCallsIndOk_nil env MR X

end B2.BackendContracts
