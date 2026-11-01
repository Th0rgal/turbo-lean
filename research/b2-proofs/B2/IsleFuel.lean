import FV.Backend.Proof.IselPrgMono
import FV.Backend.Isel

/-! Transfer successful bounded runs to the real backend's default ISLE fuel.
No change to the executable interpreter or its configuration is needed. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace B2.BackendEval
open Backend Isle

theorem applyTerm_mono {V σ : Type} {p : Program} {sem : Sem V σ} {cfg : Config}
    {n n' : Nat} (hn : n ≤ n') {ty t : Nat} {args : List V}
    {s : σ × Array RuleId} {r : Option V × (σ × Array RuleId)}
    (h : (Interp.applyTerm p sem cfg n ty t args).run s = .ok r) :
    (Interp.applyTerm p sem cfg n' ty t args).run s = .ok r := by
  induction hn with
  | refl => exact h
  | step _ ih => exact (Interp.monoAt _).apply _ _ _ _ _ ih

theorem runTerm_of_apply {ctx : Backend.Ctx} {term : String} {args : List Backend.V}
    {st : Backend.LState} {T : Isle.Term} {r : Option Backend.V × (Backend.LState × Array RuleId)}
    (hT : Isle.Aarch64.program.termByName? term = some T)
    (h : (Interp.applyTerm Isle.Aarch64.program (Backend.sem ctx) {} 1024 T.ret T.id args).run
      (st, #[]) = .ok r) :
    Backend.runTerm ctx term args st = .ok (r.1, r.2.1, r.2.2.toList) := by
  have hbig := applyTerm_mono (by decide : 1024 ≤ 1000000) h
  unfold Backend.runTerm Interp.run
  simp only [hT, bind, Except.bind, hbig, pure, Except.pure]

#print axioms applyTerm_mono
#print axioms runTerm_of_apply
end B2.BackendEval
