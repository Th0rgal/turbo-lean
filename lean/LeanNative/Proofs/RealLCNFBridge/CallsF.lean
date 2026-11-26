import LeanNative.Proofs.RealLCNFBridge.StepCases
import LeanNative.IR.RealLCNFCallSemantics

/-!
# L2 helpers: environment-aware mirrors of the step-level L1 lemmas

Contract: `lean/LeanNative/Proofs/LowerCalls.lean` ("Expected helper lemmas landing with
the proofs"). `evalCodeF` and `evalStepF` mirror `evalCode`/`evalStep` clause for clause
with one new rule each, so every lemma here mirrors its L1 original with the environment
threaded through; the call rule itself is handled where the proofs consume these through
hypothesis parameters, so a sibling (L3) can instantiate the mechanical cases with its
own call rule. `evalCodeF` is well-founded-recursive (lexicographic `(Φ.length, code)`)
and its `.letBind` arm holds a dependent matcher (`match hc : FuncEnv.callTarget? …`), so
the mirrors go through the plain-match unfolding equations below instead of `dsimp`.
-/

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

/-- `evalCodeF` on a `.letBind`, as a plain (non-dependent) match on
    `FuncEnv.callTarget?` — the dependent `hc` binder in the definition exists only for
    termination, so the two forms agree. -/
theorem evalCodeF_letBind (Φ : FuncEnv) (fuel : Nat) (env : VarEnv) (st : HeapState)
    (dst : VarId) (ty : LNIRType) (val : LNIRExpr) (k : LNIRCode) :
    evalCodeF Φ fuel env st (.letBind dst ty val k) =
      match FuncEnv.callTarget? Φ val with
      | some ((ld, fuelD), Φ', args) =>
        match evalVarList env args with
        | .ok vals =>
          if vals.length = ld.params.length then
            match evalCodeF Φ' fuelD
                ((ld.params.zip vals).foldl (fun acc (p, val) => acc.bind p.id val) VarEnv.empty)
                st ld.body with
            | .ok (v, st') => evalCodeF Φ fuel (env.bind dst v) st' k
            | .error err => .error err
          else .error (.typeError "call arity mismatch")
        | .error err => .error err
      | none =>
        match evalExpr env st val with
        | .ok (v, st') => evalCodeF Φ fuel (env.bind dst v) st' k
        | .error err => .error err := by
  -- `rw [eq_def]` unfolds ONLY the left-hand application (the right-hand occurrences
  -- carry different arguments, so the instantiated pattern leaves them alone; a bare
  -- `unfold` would rewrite them too and the fold-back pattern never matches).
  rw [evalCodeF.eq_def]
  try simp only []
  split <;> rename_i heq <;> simp only [heq] <;> try rfl

/-- The non-call instance of `evalCodeF_letBind`: with the environment lookup a miss the
    arm is `evalCode`'s byte for byte (modulo the recursive occurrence). -/
theorem evalCodeF_letBind_evalExpr {Φ : FuncEnv} {val : LNIRExpr}
    (hnc : FuncEnv.callTarget? Φ val = none)
    (fuel : Nat) (env : VarEnv) (st : HeapState) (dst : VarId) (ty : LNIRType)
    (k : LNIRCode) :
    evalCodeF Φ fuel env st (.letBind dst ty val k) =
      match evalExpr env st val with
      | .ok (v, st') => evalCodeF Φ fuel (env.bind dst v) st' k
      | .error err => .error err := by
  rw [evalCodeF_letBind, hnc]

/-- Mirror of `evalCode_fuel_mono_step` (contract-named helper): the LNIR fuel is
    pass-through except for loop bounds, and a resolved call runs the callee at ITS
    entry's fuel, which does not move with the ambient fuel. -/
theorem evalCodeF_fuel_mono_step (Φ : FuncEnv) (f : Nat) :
    ∀ (c : LNIRCode) (venv : VarEnv) (hst : HeapState) (v : Val) (hst' : HeapState),
    evalCodeF Φ f venv hst c = .ok (v, hst') → evalCodeF Φ (f + 1) venv hst c = .ok (v, hst')
  | .letBind dst ty val k, venv, hst, v, hst', h => by
    rw [evalCodeF_letBind] at h ⊢
    cases hcc : FuncEnv.callTarget? Φ val with
    | none =>
      -- `cases hcc` substituted the discriminant in the goal already; reduce the
      -- resulting ground matchers on both sides.
      rw [hcc] at h
      simp only at h ⊢
      cases he : evalExpr venv hst val with
      | error _ => rw [he] at h; exact nomatch h
      | ok p =>
        rw [he] at h
        exact evalCodeF_fuel_mono_step Φ f k (venv.bind dst p.1) p.2 v hst' h
    | some pt =>
      rcases pt with ⟨⟨ld, fuelD⟩, Φ', args⟩
      rw [hcc] at h
      simp only at h ⊢
      cases hvl : evalVarList venv args with
      | error _ => rw [hvl] at h; exact nomatch h
      | ok vals =>
        rw [hvl] at h
        simp only at h ⊢
        by_cases hlen : vals.length = ld.params.length
        · rw [ite_eq_left hlen] at h ⊢
          cases hcal : evalCodeF Φ' fuelD
              ((ld.params.zip vals).foldl (fun acc (p, val) => acc.bind p.id val) VarEnv.empty)
              hst ld.body with
          | error _ => rw [hcal] at h; exact nomatch h
          | ok pr =>
            rw [hcal] at h
            exact evalCodeF_fuel_mono_step Φ f k (venv.bind dst pr.1) pr.2 v hst' h
        · rw [ite_eq_right hlen] at h; exact nomatch h
  | .rawStore pv iv vv elemTy k, venv, hst, v, hst', h => by
    unfold evalCodeF at h ⊢
    cases hp : venv pv <;> cases hi : venv iv <;>
      cases hv : venv vv <;> simp only [hp, hi, hv] at h <;> try contradiction
    rename_i vp vi vv0
    cases vp <;> cases vi <;>
      cases vv0 <;> simp only at h ⊢ <;> try contradiction
    all_goals (
      rename_i bufId idx val
      cases hw : hst.writeElemExclusive bufId idx.toNat (maskElemVal elemTy val) <;> simp only [hw] at h ⊢
      · contradiction
      · rename_i hst1; exact evalCodeF_fuel_mono_step Φ f k venv hst1 v hst' h)
  | .incRef ov cnt k, venv, hst, v, hst', h => by
    unfold evalCodeF at h ⊢
    cases he : hst.evalIncRef venv ov cnt with
    | error _ => rw [he] at h; exact nomatch h
    | ok hst1 => rw [he] at h; exact evalCodeF_fuel_mono_step Φ f k venv hst1 v hst' h
  | .decRef ov cnt k, venv, hst, v, hst', h => by
    unfold evalCodeF at h ⊢
    cases he : hst.evalDecRef venv ov cnt with
    | error _ => rw [he] at h; exact nomatch h
    | ok hst1 => rw [he] at h; exact evalCodeF_fuel_mono_step Φ f k venv hst1 v hst' h
  | .ite cv t e, venv, hst, v, hst', h => by
    unfold evalCodeF at h ⊢
    cases hc : venv cv <;> rw [hc] at h
    · exact nomatch h
    · rename_i vc; cases vc with
      | bool b => cases b <;> exact evalCodeF_fuel_mono_step Φ f _ venv hst v hst' h
      | u64 n => by_cases hn : n != 0 <;> simp only [hn, ↓reduceIte, Bool.false_eq_true] at h ⊢ <;>
          exact evalCodeF_fuel_mono_step Φ f _ venv hst v hst' h
      | u256 w => by_cases hw : w != UInt256.zero <;> simp only [hw, ↓reduceIte, Bool.false_eq_true] at h ⊢ <;>
          exact evalCodeF_fuel_mono_step Φ f _ venv hst v hst' h
      | _ => exact nomatch h
  | .seqFor idxVar loVar hiVar accVar accInit _ stepBody k, venv, hst, v, hst', h => by
    unfold evalCodeF at h ⊢
    cases hlo : venv loVar <;> cases hhi : venv hiVar <;>
      cases hain : venv accInit <;> simp only [hlo, hhi, hain] at h <;> try contradiction
    rename_i vlo vhi initVal
    cases vlo <;> cases vhi <;>
      simp only at h ⊢ <;> try contradiction
    rename_i lo hi
    have hloop : ∀ cnt cur acc env0 st0 r,
        evalSeqLoop cnt cur idxVar accVar acc env0 st0 (fun se ss => evalCodeF Φ f se ss stepBody) = .ok r →
        evalSeqLoop cnt cur idxVar accVar acc env0 st0 (fun se ss => evalCodeF Φ (f + 1) se ss stepBody) = .ok r := by
      intro cnt; induction cnt with
      | zero => intro _ _ _ _ _ hr; exact hr
      | succ cnt' ihc =>
        intro cur acc env0 st0 r hr; dsimp only [evalSeqLoop] at hr ⊢
        cases hs : evalCodeF Φ f ((env0.bind idxVar (.u64 cur.toUInt64)).bind accVar acc) st0 stepBody with
        | error _ => rw [hs] at hr; exact nomatch hr
        | ok pr =>
          rw [hs] at hr
          rw [evalCodeF_fuel_mono_step Φ f stepBody _ st0 pr.1 pr.2 hs]
          exact ihc (cur + 1) pr.1 env0 pr.2 r hr
    cases hl : evalSeqLoop (hi.toNat - lo.toNat) lo.toNat idxVar accVar initVal venv hst
        (fun se ss => evalCodeF Φ f se ss stepBody) with
    | error _ => rw [hl] at h; exact nomatch h
    | ok pr =>
      rw [hl] at h; rw [hloop _ _ _ _ _ pr hl]
      exact evalCodeF_fuel_mono_step Φ f k (venv.bind accVar pr.1) pr.2 v hst' h
  | .parFor outVar lenVar inputs elemTy kernel k, venv, hst, v, hst', h => by
    unfold evalCodeF at h ⊢
    have hpf : ∀ r, evalParFor f venv hst lenVar inputs kernel elemTy = .ok r →
        evalParFor (f + 1) venv hst lenVar inputs kernel elemTy = .ok r := by
      intro r hp; unfold evalParFor at hp ⊢
      cases hl : venv lenVar <;> rw [hl] at hp
      · exact nomatch hp
      · rename_i vl
        cases vl with
        | u64 n =>
          dsimp only at hp ⊢
          by_cases hgt : n.toNat > f
          · simp only [hgt, ↓reduceIte] at hp; exact nomatch hp
          · have hgt' : ¬(n.toNat > f + 1) := by omega
            simp only [hgt, hgt', ↓reduceIte] at hp ⊢; exact hp
        | _ => exact nomatch hp
    cases hp : evalParFor f venv hst lenVar inputs kernel elemTy with
    | error _ => rw [hp] at h; exact nomatch h
    | ok pr =>
      rw [hp] at h; rw [hpf pr hp]
      exact evalCodeF_fuel_mono_step Φ f k (venv.bind outVar pr.1) pr.2 v hst' h
  | .ret x, venv, hst, v, hst', h => by
    unfold evalCodeF at h ⊢; exact h
  | .unreachable, venv, hst, v, hst', h => by
    unfold evalCodeF at h ⊢; exact h

end LeanNative.Proofs
