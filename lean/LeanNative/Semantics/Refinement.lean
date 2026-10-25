import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval

namespace LeanNative.Semantics

open LeanNative.IR

/-- Denotational equivalence of pure scalar expressions across all variable environments. -/
def ScalarExprEquiv (e1 e2 : ScalarExpr) : Prop :=
  ∀ env, evalScalarExpr env e1 = evalScalarExpr env e2

namespace ScalarExprEquiv

theorem refl (e : ScalarExpr) : ScalarExprEquiv e e :=
  fun _ => rfl

theorem symm {e1 e2 : ScalarExpr} (h : ScalarExprEquiv e1 e2) : ScalarExprEquiv e2 e1 :=
  fun env => (h env).symm

theorem trans {e1 e2 e3 : ScalarExpr}
    (h12 : ScalarExprEquiv e1 e2) (h23 : ScalarExprEquiv e2 e3) :
    ScalarExprEquiv e1 e3 :=
  fun env => Eq.trans (h12 env) (h23 env)

end ScalarExprEquiv

/-- Forward simulation / refinement relation on right-hand side LNIR expressions (`LNIRExpr`):
    whenever `src` evaluates without UB to `(v, st')`, `tgt` evaluates to the exact same `(v, st')`. -/
def ExprRefines (src tgt : LNIRExpr) : Prop :=
  ∀ env st v st', evalExpr env st src = .ok (v, st') → evalExpr env st tgt = .ok (v, st')

namespace ExprRefines

theorem refl (e : LNIRExpr) : ExprRefines e e :=
  fun _ _ _ _ h => h

theorem trans {e1 e2 e3 : LNIRExpr}
    (h12 : ExprRefines e1 e2) (h23 : ExprRefines e2 e3) :
    ExprRefines e1 e3 :=
  fun env st v st' h1 => h23 env st v st' (h12 env st v st' h1)

theorem of_scalar_equiv {s1 s2 : ScalarExpr} (h : ScalarExprEquiv s1 s2) :
    ExprRefines (.scalar s1) (.scalar s2) := by
  intro env st v st' heval
  simp only [evalExpr, ← h env]
  exact heval

end ExprRefines

/-- Strong denotational equivalence on `LNIRExpr`. -/
def ExprEquiv (e1 e2 : LNIRExpr) : Prop :=
  ∀ env st, evalExpr env st e1 = evalExpr env st e2

namespace ExprEquiv

theorem refl (e : LNIRExpr) : ExprEquiv e e :=
  fun _ _ => rfl

theorem symm {e1 e2 : LNIRExpr} (h : ExprEquiv e1 e2) : ExprEquiv e2 e1 :=
  fun env st => (h env st).symm

theorem trans {e1 e2 e3 : LNIRExpr}
    (h12 : ExprEquiv e1 e2) (h23 : ExprEquiv e2 e3) :
    ExprEquiv e1 e3 :=
  fun env st => Eq.trans (h12 env st) (h23 env st)

theorem toRefines {e1 e2 : LNIRExpr} (h : ExprEquiv e1 e2) : ExprRefines e1 e2 := by
  intro env st v st' heval
  rw [← h env st]
  exact heval

end ExprEquiv

/-- Forward simulation / refinement relation on structured `LNIRCode` blocks:
    whenever `src` evaluates in `fuel` steps without UB to `(v, st')`, `tgt` evaluates to `(v, st')`. -/
def CodeRefines (src tgt : LNIRCode) : Prop :=
  ∀ fuel env st v st', evalCode fuel env st src = .ok (v, st') → evalCode fuel env st tgt = .ok (v, st')

namespace CodeRefines

theorem refl (c : LNIRCode) : CodeRefines c c :=
  fun _ _ _ _ _ h => h

theorem trans {c1 c2 c3 : LNIRCode}
    (h12 : CodeRefines c1 c2) (h23 : CodeRefines c2 c3) :
    CodeRefines c1 c3 :=
  fun fuel env st v st' h1 => h23 fuel env st v st' (h12 fuel env st v st' h1)

theorem letBind_congr {dst : VarId} {ty : LNIRType} {e1 e2 : LNIRExpr} {k1 k2 : LNIRCode}
    (he : ExprRefines e1 e2) (hk : CodeRefines k1 k2) :
    CodeRefines (.letBind dst ty e1 k1) (.letBind dst ty e2 k2) := by
  intro fuel env st v st' hsrc
  rw [evalCode] at hsrc ⊢
  cases heval : evalExpr env st e1 with
  | error err =>
    rw [heval] at hsrc
    contradiction
  | ok pair =>
    rcases pair with ⟨val, st1⟩
    rw [heval] at hsrc
    have heval2 := he env st val st1 heval
    rw [heval2]
    exact hk fuel (env.bind dst val) st1 v st' hsrc

theorem rawStore_congr {ptrVar idxVar valVar : VarId} {elemTy : LNIRType} {k1 k2 : LNIRCode}
    (hk : CodeRefines k1 k2) :
    CodeRefines (.rawStore ptrVar idxVar valVar elemTy k1) (.rawStore ptrVar idxVar valVar elemTy k2) := by
  intro fuel env st v st' hsrc
  rw [evalCode] at hsrc ⊢
  cases hptr : env ptrVar with
  | none => simp only [hptr] at hsrc ⊢; exact hsrc
  | some pval =>
    cases hidx : env idxVar with
    | none => simp only [hptr, hidx] at hsrc ⊢; exact hsrc
    | some ival =>
      cases hval : env valVar with
      | none => simp only [hptr, hidx, hval] at hsrc ⊢; exact hsrc
      | some vval =>
        simp only [hptr, hidx, hval] at hsrc ⊢
        cases pval <;> cases ival <;> cases vval <;> try exact hsrc
        all_goals
          simp only at hsrc ⊢
          cases hw : st.writeElemExclusive _ _ _ with
          | error err => rw [hw] at hsrc; exact hsrc
          | ok st1 =>
            rw [hw] at hsrc
            exact hk fuel env st1 v st' hsrc

theorem incRef_congr {objVar : VarId} {count : Nat} {k1 k2 : LNIRCode}
    (hk : CodeRefines k1 k2) :
    CodeRefines (.incRef objVar count k1) (.incRef objVar count k2) := by
  intro fuel env st v st' hsrc
  rw [evalCode] at hsrc ⊢
  cases hinc : st.evalIncRef env objVar count with
  | error _ => rw [hinc] at hsrc; contradiction
  | ok st1 => rw [hinc] at hsrc; exact hk fuel env st1 v st' hsrc

theorem decRef_congr {objVar : VarId} {count : Nat} {k1 k2 : LNIRCode}
    (hk : CodeRefines k1 k2) :
    CodeRefines (.decRef objVar count k1) (.decRef objVar count k2) := by
  intro fuel env st v st' hsrc
  rw [evalCode] at hsrc ⊢
  cases hdec : st.evalDecRef env objVar count with
  | error _ => rw [hdec] at hsrc; contradiction
  | ok st1 => rw [hdec] at hsrc; exact hk fuel env st1 v st' hsrc

theorem ite_congr {condVar : VarId} {t1 t2 e1 e2 : LNIRCode}
    (ht : CodeRefines t1 t2) (he : CodeRefines e1 e2) :
    CodeRefines (.ite condVar t1 e1) (.ite condVar t2 e2) := by
  intro fuel env st v st' hsrc
  rw [evalCode] at hsrc ⊢
  cases hc : env condVar with
  | none => rw [hc] at hsrc; contradiction
  | some cval =>
    rw [hc] at hsrc
    cases cval with
    | bool b =>
      cases b with
      | true => exact ht fuel env st v st' hsrc
      | false => exact he fuel env st v st' hsrc
    | u64 n =>
      simp only at hsrc ⊢
      by_cases hn : (n != 0) = true
      · rw [ite_eq_left hn] at hsrc ⊢
        exact ht fuel env st v st' hsrc
      · rw [ite_eq_right hn] at hsrc ⊢
        exact he fuel env st v st' hsrc
    | u256 w =>
      simp only at hsrc ⊢
      by_cases hw : (w != UInt256.zero) = true
      · rw [ite_eq_left hw] at hsrc ⊢
        exact ht fuel env st v st' hsrc
      · rw [ite_eq_right hw] at hsrc ⊢
        exact he fuel env st v st' hsrc
    | _ => contradiction

theorem parFor_congr {outVar lenVar : VarId} {inputs : List VarId} {elemTy : LNIRType}
    {kernel : ParallelKernelKind} {k1 k2 : LNIRCode}
    (hk : CodeRefines k1 k2) :
    CodeRefines (.parFor outVar lenVar inputs elemTy kernel k1)
                (.parFor outVar lenVar inputs elemTy kernel k2) := by
  intro fuel env st v st' hsrc
  rw [evalCode] at hsrc ⊢
  cases hpar : evalParFor fuel env st lenVar inputs kernel with
  | error _ => rw [hpar] at hsrc; contradiction
  | ok pair => rw [hpar] at hsrc; exact hk fuel (env.bind outVar pair.1) pair.2 v st' hsrc

end CodeRefines

end LeanNative.Semantics
