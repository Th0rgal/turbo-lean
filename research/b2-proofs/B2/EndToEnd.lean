import B2.BackendEntry
import B2.BackendContracts
import FV.E2E.FinalDirect

/-! LNIR result to AArch64 x0 for collatz_steps, through the real shared lowering and
clifv pipeline. Machine-entry/memory contracts and the backend's unconditional hook
clauses stay explicit; compilation, safety and absent-call obligations are discharged. -/
namespace B2.EndToEnd
open LeanNative.Semantics Backend Backend.Proof Backend.Proof.Driver E2E B2.Artifacts

theorem collatz_to_arm {p : Clif.Program}
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat}
    (hpc : ∀ d s, Arm.r .ERR s = .None → Arm.CheckSPAlignment s →
      Arm.r .PC (H.call d s) = Arm.r .PC s + 4)
    (hext : ∀ d uses w outs w', X.call d uses w = some (outs, w') →
      Arm.r .ERR w = .None → Arm.r .ERR w' = .None ∧ w'.program = w.program)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {cs : Clif.State}
    (n steps : UInt64)
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn B2.Smoke.collatz.sig [B2.CollatzClif.cv n, B2.CollatzClif.cv steps] s)
    (hcs : ClifEntry B2.Smoke.collatz [B2.CollatzClif.cv n, B2.CollatzClif.cv steps] cs)
    (hrel : Rel.holds
      ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
        syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ B2.Smoke.collatz
      cs.frame.slots cs.mem w₀)
    (fuel : Nat) (v : LeanNative.Semantics.Val) (st₀ st₁ : HeapState)
    (hev : evalCode fuel
      (B2.entryEnv LeanNative.IR.Codec.collatzStepsDecl [.u64 n, .u64 steps]) st₀
      LeanNative.IR.Codec.collatzStepsDecl.body = .ok (v, st₁)) :
    ∃ count rv, ArmRet ra s (runX (ArmStepX X H fa) count s) ∧
      B2.ValRel v rv ∧ XHolds rv (xreg 0 (runX (ArmStepX X H fa) count s)) := by
  have hr := backend_correct_final_of_lower (B2.BackendContracts.subset p)
    B2.BackendContracts.dominated B2.BackendContracts.scope
    B2.Artifacts.lower B2.Artifacts.prepared B2.Artifacts.allocation_checked
    B2.Artifacts.allocated B2.Artifacts.emitted B2.Artifacts.laid_out
    (fun _ => B2.BackendContracts.callee_ok _ K X H hpc hext)
    (B2.BackendContracts.try_contract _) (B2.BackendContracts.tls_contract _)
    (fun _ => B2.BackendContracts.extern_contract Clif.Env.empty _ _)
    (fun _ => B2.BackendContracts.indirect_contract Clif.Env.empty _ _)
    hsym hslot hent hres hbe hargs hcs hrel
    (B2.BackendEntry.traps_explicit Clif.Env.empty p n steps cs hcs) (15 * steps.toNat + 5)
  rw [B2.BackendEntry.returns _ p n steps cs hcs] at hr
  obtain ⟨count, hret, hregs, _⟩ := hr
  rw [B2.CollatzSource.collatz_eval] at hev
  cases hev
  exact ⟨count, _, hret, rfl, hregs 0 _ rfl⟩

#print axioms collatz_to_arm
end B2.EndToEnd
