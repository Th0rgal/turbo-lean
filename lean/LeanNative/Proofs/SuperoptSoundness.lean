import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.Proofs.PeepholeProofs
import LeanNative.Proofs.SymbolicTV
import LeanNative.Proofs.SymbolicTVDenote
import LeanNative.Proofs.SymbolicTVSoundness
import LeanNative.Transform.Superopt

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Transform

/-!
# Kernel-Checked Soundness of the Enumerative Superoptimizer (`LeanNative.Proofs.SuperoptSoundness`)

Every rewrite accepted by `LeanNative.Transform.checkSuperoptScalarVerified` refines the original
scalar expression under the locked operational semantics `evalScalarExpr` / `evalExpr`, and the
module-level passes `superoptCodeCore`, `superoptDecl`, and `superoptModule` therefore refine whole
`LNIRCode` blocks, declarations, and modules (`CodeRefines`).
-/

theorem BinOp_eq_of_beq : ∀ {a b : BinOp}, (a == b) = true → a = b := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

theorem UnaryOp_eq_of_beq : ∀ {a b : UnaryOp}, (a == b) = true → a = b := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

theorem ScalarExpr_eq_of_beq : ∀ {a b : ScalarExpr}, (a == b) = true → a = b
  | .constU64 x, .constU64 y, h => by
    simp only [BEq.beq] at h
    exact congrArg ScalarExpr.constU64 (eq_of_beq h)
  | .constBool x, .constBool y, h => by
    simp only [BEq.beq] at h
    exact congrArg ScalarExpr.constBool (eq_of_beq h)
  | .var x, .var y, h => by
    simp only [BEq.beq] at h
    exact congrArg ScalarExpr.var (eq_of_beq h)
  | .binOp o1 l1 r1, .binOp o2 l2 r2, h => by
    have h' : ((o1 == o2) && ((l1 == l2) && (r1 == r2))) = true := h
    simp only [Bool.and_eq_true] at h'
    rcases h' with ⟨ho, hl, hr⟩
    rw [BinOp_eq_of_beq ho, ScalarExpr_eq_of_beq hl, ScalarExpr_eq_of_beq hr]
  | .unaryOp o1 a1, .unaryOp o2 a2, h => by
    have h' : ((o1 == o2) && (a1 == a2)) = true := h
    simp only [Bool.and_eq_true] at h'
    rcases h' with ⟨ho, ha⟩
    rw [UnaryOp_eq_of_beq ho, ScalarExpr_eq_of_beq ha]
  | .select c1 t1 f1, .select c2 t2 f2, h => by
    have h' : ((c1 == c2) && ((t1 == t2) && (f1 == f2))) = true := h
    simp only [Bool.and_eq_true] at h'
    rcases h' with ⟨hc, ht, hf⟩
    rw [ScalarExpr_eq_of_beq hc, ScalarExpr_eq_of_beq ht, ScalarExpr_eq_of_beq hf]
  | .fma a1 b1 c1, .fma a2 b2 c2, h => by
    have h' : ((a1 == a2) && ((b1 == b2) && (c1 == c2))) = true := h
    simp only [Bool.and_eq_true] at h'
    rcases h' with ⟨ha, hb, hc⟩
    rw [ScalarExpr_eq_of_beq ha, ScalarExpr_eq_of_beq hb, ScalarExpr_eq_of_beq hc]
  | .constU64 _, .constBool _, h | .constU64 _, .var _, h | .constU64 _, .binOp _ _ _, h
  | .constU64 _, .unaryOp _ _, h | .constU64 _, .select _ _ _, h | .constU64 _, .fma _ _ _, h
  | .constBool _, .constU64 _, h | .constBool _, .var _, h | .constBool _, .binOp _ _ _, h
  | .constBool _, .unaryOp _ _, h | .constBool _, .select _ _ _, h | .constBool _, .fma _ _ _, h
  | .var _, .constU64 _, h | .var _, .constBool _, h | .var _, .binOp _ _ _, h
  | .var _, .unaryOp _ _, h | .var _, .select _ _ _, h | .var _, .fma _ _ _, h
  | .binOp _ _ _, .constU64 _, h | .binOp _ _ _, .constBool _, h | .binOp _ _ _, .var _, h
  | .binOp _ _ _, .unaryOp _ _, h | .binOp _ _ _, .select _ _ _, h | .binOp _ _ _, .fma _ _ _, h
  | .unaryOp _ _, .constU64 _, h | .unaryOp _ _, .constBool _, h | .unaryOp _ _, .var _, h
  | .unaryOp _ _, .binOp _ _ _, h | .unaryOp _ _, .select _ _ _, h | .unaryOp _ _, .fma _ _ _, h
  | .select _ _ _, .constU64 _, h | .select _ _ _, .constBool _, h | .select _ _ _, .var _, h
  | .select _ _ _, .binOp _ _ _, h | .select _ _ _, .unaryOp _ _, h | .select _ _ _, .fma _ _ _, h
  | .fma _ _ _, .constU64 _, h | .fma _ _ _, .constBool _, h | .fma _ _ _, .var _, h
  | .fma _ _ _, .binOp _ _ _, h | .fma _ _ _, .unaryOp _ _, h | .fma _ _ _, .select _ _ _, h => by
    cases h

theorem evalBinOp_const_right_forces_u64 (op : BinOp) (vv : Val) (c : UInt64) (val : Val) :
    evalBinOp op vv (.u64 c) = .ok val →
    (match op with
     | .add | .bitOr | .bitXor | .sub | .shl | .shr => c != 0
     | .mul | .div => c != 1
     | .mod | .sar | .eq | .lt | .le | .bitAnd | .clmul64 | .clmul64Hi | .gf2Affine | .eor3 => true
     | .addChecked256 | .subChecked256 | .mulChecked256 => false) = true →
    ∃ n : UInt64, vv = .u64 n := by
  intro heval hc
  cases vv with
  | u64 n => exact ⟨n, rfl⟩
  | u256 _ | bool _ | sarrayId _ | rawPtrId _ | objPtr _ | storageMapId _ | tuple _ | unit =>
    cases op with
    | addChecked256 | subChecked256 | mulChecked256 => cases hc
    | add | bitXor | sub | shl | shr =>
      by_cases hc0 : c = 0
      · subst hc0; simp at hc
      · unfold evalBinOp at heval; simp [hc0] at heval
    | bitOr =>
      by_cases hc0 : c = 0
      · subst hc0; simp at hc
      · unfold evalBinOp at heval; simp [hc0, (· == ·), Val.beq] at heval
    | mul | div =>
      by_cases hc1 : c = 1
      · subst hc1; simp at hc
      · unfold evalBinOp at heval; simp [hc1] at heval
    | bitAnd =>
      unfold evalBinOp at heval; simp [(· == ·), Val.beq] at heval
    | mod | sar | eq | lt | le | clmul64 | clmul64Hi | gf2Affine | eor3 =>
      unfold evalBinOp at heval; simp at heval

theorem evalBinOp_const_left_forces_u64 (op : BinOp) (c : UInt64) (vv : Val) (val : Val) :
    evalBinOp op (.u64 c) vv = .ok val →
    (match op with
     | .add | .bitOr | .bitXor => c != 0
     | .mul => c != 1
     | .sub | .shl | .shr | .div | .mod | .sar | .eq | .lt | .le
     | .bitAnd | .clmul64 | .clmul64Hi | .gf2Affine | .eor3 => true
     | .addChecked256 | .subChecked256 | .mulChecked256 => false) = true →
    ∃ n : UInt64, vv = .u64 n := by
  intro heval hc
  cases vv with
  | u64 n => exact ⟨n, rfl⟩
  | u256 _ | bool _ | sarrayId _ | rawPtrId _ | objPtr _ | storageMapId _ | tuple _ | unit =>
    cases op with
    | addChecked256 | subChecked256 | mulChecked256 => cases hc
    | add | bitXor =>
      by_cases hc0 : c = 0
      · subst hc0; simp at hc
      · unfold evalBinOp at heval; simp [hc0] at heval
    | bitOr =>
      by_cases hc0 : c = 0
      · subst hc0; simp at hc
      · unfold evalBinOp at heval; simp [hc0, (· == ·), Val.beq] at heval
    | mul =>
      by_cases hc1 : c = 1
      · subst hc1; simp at hc
      · unfold evalBinOp at heval; simp [hc1] at heval
    | bitAnd =>
      unfold evalBinOp at heval; simp [(· == ·), Val.beq] at heval
    | sub | shl | shr | div | mod | sar | eq | lt | le | clmul64 | clmul64Hi | gf2Affine | eor3 =>
      unfold evalBinOp at heval; simp at heval

theorem evalBinOp_clmul_left_u64 (op : BinOp) (vl vr val : Val) :
    (op = .clmul64 ∨ op = .clmul64Hi ∨ op = .gf2Affine ∨ op = .eor3) →
    evalBinOp op vl vr = .ok val →
    ∃ n : UInt64, vl = .u64 n := by
  intro hop heval
  cases vl with
  | u64 n => exact ⟨n, rfl⟩
  | u256 _ | bool _ | sarrayId _ | rawPtrId _ | objPtr _ | storageMapId _ | tuple _ | unit =>
    rcases hop with rfl | rfl | rfl | rfl <;> (unfold evalBinOp at heval; simp at heval)

theorem evalBinOp_clmul_right_u64 (op : BinOp) (vl vr val : Val) :
    (op = .clmul64 ∨ op = .clmul64Hi ∨ op = .gf2Affine ∨ op = .eor3) →
    evalBinOp op vl vr = .ok val →
    ∃ n : UInt64, vr = .u64 n := by
  intro hop heval
  cases vr with
  | u64 n => exact ⟨n, rfl⟩
  | u256 _ | bool _ | sarrayId _ | rawPtrId _ | objPtr _ | storageMapId _ | tuple _ | unit =>
    rcases hop with rfl | rfl | rfl | rfl <;>
      (cases vl <;> unfold evalBinOp at heval <;> simp at heval)

theorem varForcedU64_sound (v : VarId) (e : ScalarExpr) (env : VarEnv) (val : Val) :
    varForcedU64 v e = true →
    evalScalarExpr env e = .ok val →
    ∃ n : UInt64, env v = some (Val.u64 n) := by
  intro hforce heval
  induction e generalizing val with
  | constU64 _ | constBool _ | var _ =>
    simp [varForcedU64] at hforce
  | unaryOp op a iha =>
    simp only [varForcedU64] at hforce
    simp only [evalScalarExpr] at heval
    cases ha : evalScalarExpr env a with
    | error err => simp [ha] at heval
    | ok va => exact iha va hforce ha
  | select c t f ihc _ _ =>
    simp only [varForcedU64] at hforce
    simp only [evalScalarExpr] at heval
    cases hc : evalScalarExpr env c with
    | error err => simp [hc] at heval
    | ok vc => exact ihc vc hforce hc
  | fma a b c iha ihb ihc =>
    simp only [varForcedU64, Bool.or_eq_true] at hforce
    simp only [evalScalarExpr] at heval
    cases ha : evalScalarExpr env a with
    | error err => simp [ha] at heval
    | ok va =>
      rw [ha] at heval
      cases hb : evalScalarExpr env b with
      | error err => simp [hb] at heval
      | ok vb =>
        rw [hb] at heval
        cases hc : evalScalarExpr env c with
        | error err =>
          cases hmul : evalBinOp .mul va vb <;> simp [hmul, hc] at heval
        | ok vc =>
          rcases hforce with (hforce | hforce) | hforce
          · exact iha va hforce ha
          · exact ihb vb hforce hb
          · exact ihc vc hforce hc
  | binOp op l r ihl ihr =>
    simp only [varForcedU64, Bool.or_eq_true] at hforce
    simp only [evalScalarExpr] at heval
    cases hl : evalScalarExpr env l with
    | error err => simp [hl] at heval
    | ok vl =>
      rw [hl] at heval
      cases hr : evalScalarExpr env r with
      | error err => simp [hr] at heval
      | ok vr =>
        rw [hr] at heval
        dsimp only [] at heval
        rcases hforce with (htop | hsub) | hsub
        · generalize hop : op = op0 at htop heval
          cases op0
          case addChecked256 | subChecked256 | mulChecked256 =>
            simp at htop
          case clmul64 | clmul64Hi | gf2Affine | eor3 =>
            simp only [Bool.or_eq_true] at htop
            rcases htop with hbeq | hbeq
            · have hleft := ScalarExpr_eq_of_beq hbeq
              subst hleft
              simp only [evalScalarExpr] at hl
              cases hvl : env v with
              | none => simp [hvl] at hl
              | some vv =>
                simp only [hvl] at hl
                injection hl with hvv; subst hvv
                obtain ⟨n, rfl⟩ := evalBinOp_clmul_left_u64 _ vv vr val
                  (by first
                    | exact Or.inl rfl
                    | exact Or.inr (Or.inl rfl)
                    | exact Or.inr (Or.inr (Or.inl rfl))
                    | exact Or.inr (Or.inr (Or.inr rfl))) heval
                exact ⟨n, rfl⟩
            · have hright := ScalarExpr_eq_of_beq hbeq
              subst hright
              simp only [evalScalarExpr] at hr
              cases hvr : env v with
              | none => simp [hvr] at hr
              | some vv =>
                simp only [hvr] at hr
                injection hr with hvv; subst hvv
                obtain ⟨n, rfl⟩ := evalBinOp_clmul_right_u64 _ vl vv val
                  (by first
                    | exact Or.inl rfl
                    | exact Or.inr (Or.inl rfl)
                    | exact Or.inr (Or.inr (Or.inl rfl))
                    | exact Or.inr (Or.inr (Or.inr rfl))) heval
                exact ⟨n, rfl⟩
          all_goals
            simp only [Bool.or_eq_true, Bool.and_eq_true] at htop
            rcases htop with ⟨hbeq, hconst⟩ | ⟨hbeq, hconst⟩
            · have hleft := ScalarExpr_eq_of_beq hbeq
              subst hleft
              simp only [evalScalarExpr] at hl
              cases hvl : env v with
              | none => simp [hvl] at hl
              | some vv =>
                simp only [hvl] at hl
                injection hl with hvv; subst hvv
                cases r with
                | constU64 c =>
                  simp only [evalScalarExpr] at hr
                  injection hr with hvr; subst hvr
                  obtain ⟨n, rfl⟩ := evalBinOp_const_right_forces_u64 _ vv c val heval hconst
                  exact ⟨n, rfl⟩
                | _ => nomatch hconst
            · have hright := ScalarExpr_eq_of_beq hbeq
              subst hright
              simp only [evalScalarExpr] at hr
              cases hvr : env v with
              | none => simp [hvr] at hr
              | some vv =>
                simp only [hvr] at hr
                injection hr with hvv; subst hvv
                cases l with
                | constU64 c =>
                  simp only [evalScalarExpr] at hl
                  injection hl with hvl; subst hvl
                  obtain ⟨n, rfl⟩ := evalBinOp_const_left_forces_u64 _ c vv val heval hconst
                  exact ⟨n, rfl⟩
                | _ => nomatch hconst
        · exact ihl vl hsub hl
        · exact ihr vr hsub hr

/-- Monotonicity of `isPureU64SymExprIn` with respect to variable-set inclusion. -/
theorem isPureU64SymExprIn_mono (xs ys : List VarId) :
    (∀ id : VarId, xs.contains id = true → ys.contains id = true) →
    ∀ (s : SymExpr), isPureU64SymExprIn xs s = true → isPureU64SymExprIn ys s = true
  | hsub, .constU64 _, _ => rfl
  | hsub, .symVar id, hp => hsub id hp
  | hsub, .unaryOp op a, hp => by
    cases op with
    | clz256 => simp [isPureU64SymExprIn] at hp
    | not | neg =>
      simp only [isPureU64SymExprIn] at hp ⊢
      exact isPureU64SymExprIn_mono xs ys hsub a hp
  | hsub, .binOp op l r, hp => by
    simp only [isPureU64SymExprIn, Bool.and_eq_true] at hp ⊢
    rcases hp with ⟨⟨hop, hl⟩, hr⟩
    exact ⟨⟨hop, isPureU64SymExprIn_mono xs ys hsub l hl⟩, isPureU64SymExprIn_mono xs ys hsub r hr⟩
  | _, .constU256 _, hp | _, .constBool _, hp | _, .allocTag _, hp | _, .rcSym _ _, hp
  | _, .ctorTag _ _, hp | _, .ctorLen _ _ _, hp | _, .sarrayLen _, hp
  | _, .mulDiv256 _ _ _ _, hp | _, .ite _ _ _, hp | _, .tuple _, hp
  | _, .bufElem _ _ _, hp | _, .unit, hp => by
    simp [isPureU64SymExprIn] at hp
termination_by _ s => sizeOf s

/-- Left inclusion into `unionVars`. -/
theorem unionVars_contains_left (xs ys : List VarId) (id : VarId) :
    xs.contains id = true → (unionVars xs ys).contains id = true := by
  intro hx
  rw [List.contains_iff_mem] at hx ⊢
  simp only [unionVars, List.mem_append]
  exact Or.inl hx

/-- Right inclusion into `unionVars`. -/
theorem unionVars_contains_right (xs ys : List VarId) (id : VarId) :
    ys.contains id = true → (unionVars xs ys).contains id = true := by
  intro hy
  simp only [unionVars, List.contains_append, Bool.or_eq_true]
  by_cases hx : xs.contains id = true
  · exact Or.inl hx
  · right
    rw [List.contains_iff_mem] at hy ⊢
    rw [List.mem_filter]
    refine ⟨hy, ?_⟩
    cases hxc : xs.contains id with
    | false => rfl
    | true => exact False.elim (hx hxc)

/-- Every variable collected from a pure 64-bit scalar expression lies in `isPureU64SymExprIn`. -/
theorem collectScalarVars_pureU64_mem (e : ScalarExpr) :
    isPureU64ScalarExpr e = true →
    isPureU64SymExprIn (collectScalarVars e) (scalarToSymExpr e) = true := by
  intro hp
  induction e with
  | constU64 _ => rfl
  | var id => simp [collectScalarVars, scalarToSymExpr, isPureU64SymExprIn]
  | constBool _ | select _ _ _ | fma _ _ _ =>
    simp [isPureU64ScalarExpr] at hp
  | unaryOp op a iha =>
    cases op with
    | clz256 => simp [isPureU64ScalarExpr] at hp
    | not | neg =>
      simp only [isPureU64ScalarExpr] at hp
      exact iha hp
  | binOp op l r ihl ihr =>
    simp only [isPureU64ScalarExpr, Bool.and_eq_true] at hp
    rcases hp with ⟨⟨hop, hl⟩, hr⟩
    simp only [scalarToSymExpr, isPureU64SymExprIn, collectScalarVars, hop, Bool.true_and, Bool.and_eq_true]
    exact ⟨
      isPureU64SymExprIn_mono _ _ (unionVars_contains_left _ _) _ (ihl hl),
      isPureU64SymExprIn_mono _ _ (unionVars_contains_right _ _) _ (ihr hr)
    ⟩

/-- Canonical symbolic normalization of two pure 64-bit scalar expressions that agree after
    `normSymExpr` preserves concrete evaluation whenever all referenced variables are `.u64`. -/
theorem normSymExpr_pureU64_scalar_refines (e cand : ScalarExpr) (env : VarEnv) (v : Val) :
    isPureU64ScalarExpr e = true →
    isPureU64ScalarExpr cand = true →
    (∀ id : VarId, (unionVars (collectScalarVars e) (collectScalarVars cand)).contains id = true →
      ∃ n : UInt64, env id = some (Val.u64 n)) →
    normSymExpr (scalarToSymExpr e) = normSymExpr (scalarToSymExpr cand) →
    evalScalarExpr env e = .ok v →
    evalScalarExpr env cand = .ok v := by
  intro he hc hvars hnorm heval
  have hdenE := scalarToSymExpr_denotes env e he
  have hdenC := scalarToSymExpr_denotes env cand hc
  have hscopeE :=
    isPureU64SymExprIn_mono (collectScalarVars e)
      (unionVars (collectScalarVars e) (collectScalarVars cand))
      (unionVars_contains_left (collectScalarVars e) (collectScalarVars cand))
      (scalarToSymExpr e) (collectScalarVars_pureU64_mem e he)
  have hscopeC :=
    isPureU64SymExprIn_mono (collectScalarVars cand)
      (unionVars (collectScalarVars e) (collectScalarVars cand))
      (unionVars_contains_right (collectScalarVars e) (collectScalarVars cand))
      (scalarToSymExpr cand) (collectScalarVars_pureU64_mem cand hc)
  obtain ⟨nE, hdE, hdnE⟩ :=
    normSymExpr_pureU64_denotes _ (SymValuation.ofVarEnv env) (scalarToSymExpr e) hscopeE hvars
  obtain ⟨nC, hdC, hdnC⟩ :=
    normSymExpr_pureU64_denotes _ (SymValuation.ofVarEnv env) (scalarToSymExpr cand) hscopeC hvars
  rw [hdenE, heval] at hdE
  rw [hnorm, hdnC] at hdnE
  injection hdnE with hEqVal
  rw [← hdenC, hdC, hEqVal, ← hdE]

/-- Kernel decision procedure soundness: `checkSuperoptScalarVerified e cand = true` implies
    `ExprRefines (.scalar e) (.scalar cand)`. -/
theorem checkSuperoptScalarVerified_sound :
    ∀ (e cand : ScalarExpr),
      checkSuperoptScalarVerified e cand = true →
      ExprRefines (.scalar e) (.scalar cand)
  | e, cand, hcheck => by
    unfold checkSuperoptScalarVerified at hcheck
    by_cases heq : (cand == e) = true
    · have heq' := ScalarExpr_eq_of_beq heq
      subst heq'
      exact ExprRefines.refl _
    · rw [ite_eq_right heq] at hcheck
      by_cases hpeep : (cand == rewriteScalarPeephole e) = true
      · have hpeep' := ScalarExpr_eq_of_beq hpeep
        subst hpeep'
        exact ExprRefines.of_scalar_equiv (rewriteScalarPeephole_sound e)
      · rw [ite_eq_right hpeep] at hcheck
        by_cases hver : (cand == rewriteScalarVerified e) = true
        · have hver' := ScalarExpr_eq_of_beq hver
          subst hver'
          exact ExprRefines.of_scalar_equiv (rewriteScalarVerified_sound e)
        · rw [ite_eq_right hver] at hcheck
          dsimp only [] at hcheck
          by_cases hpure :
              (isPureU64ScalarExpr e &&
               isPureU64ScalarExpr cand &&
               (unionVars (collectScalarVars e) (collectScalarVars cand)).all (fun v => varForcedU64 v e) &&
               (normSymExpr (scalarToSymExpr e) == normSymExpr (scalarToSymExpr cand))) = true
          · simp only [Bool.and_eq_true] at hpure
            rcases hpure with ⟨⟨⟨he, hc⟩, hall⟩, hbeq⟩
            have hnorm := SymExpr_eq_of_beq hbeq
            intro env st v st' heval
            simp only [evalExpr] at heval ⊢
            cases hse : evalScalarExpr env e with
            | error err => simp [hse] at heval
            | ok sv =>
              rw [hse] at heval
              injection heval with hpair
              injection hpair with hv hst
              subst hv; subst hst
              have hvars : ∀ id : VarId,
                  (unionVars (collectScalarVars e) (collectScalarVars cand)).contains id = true →
                  ∃ n : UInt64, env id = some (Val.u64 n) := by
                intro id hid
                rw [List.contains_iff_mem] at hid
                rw [List.all_eq_true] at hall
                exact varForcedU64_sound id e env sv (hall id hid) hse
              have hsc := normSymExpr_pureU64_scalar_refines e cand env sv he hc hvars hnorm hse
              rw [hsc]
          · rw [ite_eq_right hpure] at hcheck
            cases e with
            | constU64 _ | constBool _ | var _ => cases hcheck
            | binOp op l r =>
              cases cand with
              | constU64 _ | constBool _ | var _ | unaryOp _ _ | select _ _ _ =>
                cases op <;> cases l <;> try cases hcheck
                rename_i op1 _ _; cases op1 <;> cases hcheck
              | binOp op' l' r' =>
                simp only [Bool.and_eq_true] at hcheck
                rcases hcheck with ⟨⟨hop, hl⟩, hr⟩
                have hop' := BinOp_eq_of_beq hop
                subst hop'
                have ihl := checkSuperoptScalarVerified_sound l l' hl
                have ihr := checkSuperoptScalarVerified_sound r r' hr
                intro env st v st' heval
                simp only [evalExpr, evalScalarExpr] at heval ⊢
                cases hel : evalScalarExpr env l with
                | error _ => simp [hel] at heval
                | ok vl =>
                  rw [hel] at heval
                  have hel' : evalExpr env st (.scalar l') = .ok (vl, st) :=
                    ihl env st vl st (by simp [evalExpr, hel])
                  simp only [evalExpr] at hel'
                  cases hl' : evalScalarExpr env l' with
                  | error _ => simp [hl'] at hel'
                  | ok vl' =>
                    rw [hl'] at hel'
                    injection hel' with hpl
                    injection hpl with hvl
                    subst vl'
                    cases her : evalScalarExpr env r with
                    | error _ => simp [her] at heval
                    | ok vr =>
                      rw [her] at heval
                      have her' : evalExpr env st (.scalar r') = .ok (vr, st) :=
                        ihr env st vr st (by simp [evalExpr, her])
                      simp only [evalExpr] at her'
                      cases hr' : evalScalarExpr env r' with
                      | error _ => simp [hr'] at her'
                      | ok vr' =>
                        rw [hr'] at her'
                        injection her' with hpr
                        injection hpr with hvr
                        subst vr'
                        exact heval
              | fma a' b' c' =>
                cases op with
                | add =>
                  cases l with
                  | binOp op1 l1 r1 =>
                    cases op1 with
                    | mul =>
                      simp only [Bool.and_eq_true] at hcheck
                      rcases hcheck with ⟨⟨hl1, hr1⟩, hr⟩
                      have ihl1 := checkSuperoptScalarVerified_sound l1 a' hl1
                      have ihr1 := checkSuperoptScalarVerified_sound r1 b' hr1
                      have ihr := checkSuperoptScalarVerified_sound r c' hr
                      intro env st v st' heval
                      simp only [evalExpr, evalScalarExpr] at heval ⊢
                      cases hel1 : evalScalarExpr env l1 with
                      | error _ => simp [hel1] at heval
                      | ok vl1 =>
                        rw [hel1] at heval
                        have ha' : evalExpr env st (.scalar a') = .ok (vl1, st) :=
                          ihl1 env st vl1 st (by simp [evalExpr, hel1])
                        simp only [evalExpr] at ha'
                        cases ha'' : evalScalarExpr env a' with
                        | error _ => simp [ha''] at ha'
                        | ok va' =>
                          rw [ha''] at ha'
                          injection ha' with hpa
                          injection hpa with hva
                          subst va'
                          cases her1 : evalScalarExpr env r1 with
                          | error _ => simp [her1] at heval
                          | ok vr1 =>
                            rw [her1] at heval
                            have hb' : evalExpr env st (.scalar b') = .ok (vr1, st) :=
                              ihr1 env st vr1 st (by simp [evalExpr, her1])
                            simp only [evalExpr] at hb'
                            cases hb'' : evalScalarExpr env b' with
                            | error _ => simp [hb''] at hb'
                            | ok vb' =>
                              rw [hb''] at hb'
                              injection hb' with hpb
                              injection hpb with hvb
                              subst vb'
                              cases hmul : evalBinOp .mul vl1 vr1 with
                              | error err => simp [hmul] at heval
                              | ok vab =>
                                simp [hmul] at heval ⊢
                                cases her : evalScalarExpr env r with
                                | error _ => simp [her] at heval
                                | ok vr =>
                                  rw [her] at heval
                                  have hc' : evalExpr env st (.scalar c') = .ok (vr, st) :=
                                    ihr env st vr st (by simp [evalExpr, her])
                                  simp only [evalExpr] at hc'
                                  cases hc'' : evalScalarExpr env c' with
                                  | error _ => simp [hc''] at hc'
                                  | ok vc' =>
                                    rw [hc''] at hc'
                                    injection hc' with hpc
                                    injection hpc with hvc
                                    subst vc'
                                    exact heval
                    | _ => cases hcheck
                  | _ => cases hcheck
                | _ => cases hcheck
            | unaryOp op a =>
              cases cand with
              | unaryOp op' a' =>
                simp only [Bool.and_eq_true] at hcheck
                rcases hcheck with ⟨hop, ha⟩
                have hop' := UnaryOp_eq_of_beq hop
                subst hop'
                have iha := checkSuperoptScalarVerified_sound a a' ha
                intro env st v st' heval
                simp only [evalExpr, evalScalarExpr] at heval ⊢
                cases hea : evalScalarExpr env a with
                | error _ => simp [hea] at heval
                | ok va =>
                  rw [hea] at heval
                  have hea' : evalExpr env st (.scalar a') = .ok (va, st) :=
                    iha env st va st (by simp [evalExpr, hea])
                  simp only [evalExpr] at hea'
                  cases ha' : evalScalarExpr env a' with
                  | error _ => simp [ha'] at hea'
                  | ok va' =>
                    rw [ha'] at hea'
                    injection hea' with hpa
                    injection hpa with hva
                    subst va'
                    exact heval
              | _ => cases hcheck
            | select c t f =>
              cases cand with
              | select c' t' f' =>
                simp only [Bool.and_eq_true] at hcheck
                rcases hcheck with ⟨⟨hc, ht⟩, hf⟩
                have ihc := checkSuperoptScalarVerified_sound c c' hc
                have iht := checkSuperoptScalarVerified_sound t t' ht
                have ihf := checkSuperoptScalarVerified_sound f f' hf
                intro env st v st' heval
                simp only [evalExpr, evalScalarExpr] at heval ⊢
                cases hec : evalScalarExpr env c with
                | error _ => simp [hec] at heval
                | ok vc =>
                  rw [hec] at heval
                  have hec' : evalExpr env st (.scalar c') = .ok (vc, st) :=
                    ihc env st vc st (by simp [evalExpr, hec])
                  simp only [evalExpr] at hec'
                  cases hc' : evalScalarExpr env c' with
                  | error _ => simp [hc'] at hec'
                  | ok vc' =>
                    rw [hc'] at hec'
                    injection hec' with hpc
                    injection hpc with hvc
                    subst vc'
                    cases vc with
                    | bool b =>
                      cases b
                      · exact ihf env st v st' (by simpa [evalExpr] using heval)
                      · exact iht env st v st' (by simpa [evalExpr] using heval)
                    | u64 n =>
                      by_cases hn : (n != 0) = true
                      · simp only [hn, ↓reduceIte] at heval ⊢
                        exact iht env st v st' (by simpa [evalExpr] using heval)
                      · simp only [hn, Bool.false_eq_true, ↓reduceIte] at heval ⊢
                        exact ihf env st v st' (by simpa [evalExpr] using heval)
                    | u256 w =>
                      by_cases hw : (w != UInt256.zero) = true
                      · simp only [hw, ↓reduceIte] at heval ⊢
                        exact iht env st v st' (by simpa [evalExpr] using heval)
                      · simp only [hw, Bool.false_eq_true, ↓reduceIte] at heval ⊢
                        exact ihf env st v st' (by simpa [evalExpr] using heval)
                    | _ => exact heval
              | _ => cases hcheck
            | fma a b c =>
              cases cand with
              | fma a' b' c' =>
                simp only [Bool.and_eq_true] at hcheck
                rcases hcheck with ⟨⟨ha, hb⟩, hc⟩
                have iha := checkSuperoptScalarVerified_sound a a' ha
                have ihb := checkSuperoptScalarVerified_sound b b' hb
                have ihc := checkSuperoptScalarVerified_sound c c' hc
                intro env st v st' heval
                simp only [evalExpr, evalScalarExpr] at heval ⊢
                cases hea : evalScalarExpr env a with
                | error _ => simp [hea] at heval
                | ok va =>
                  rw [hea] at heval
                  have hea' : evalExpr env st (.scalar a') = .ok (va, st) :=
                    iha env st va st (by simp [evalExpr, hea])
                  simp only [evalExpr] at hea'
                  cases ha' : evalScalarExpr env a' with
                  | error _ => simp [ha'] at hea'
                  | ok va' =>
                    rw [ha'] at hea'
                    injection hea' with hpa
                    injection hpa with hva
                    subst va'
                    cases heb : evalScalarExpr env b with
                    | error _ => simp [heb] at heval
                    | ok vb =>
                      rw [heb] at heval
                      have heb' : evalExpr env st (.scalar b') = .ok (vb, st) :=
                        ihb env st vb st (by simp [evalExpr, heb])
                      simp only [evalExpr] at heb'
                      cases hb' : evalScalarExpr env b' with
                      | error _ => simp [hb'] at heb'
                      | ok vb' =>
                        rw [hb'] at heb'
                        injection heb' with hpb
                        injection hpb with hvb
                        subst vb'
                        cases hmul : evalBinOp .mul va vb with
                        | error err => simp [hmul] at heval
                        | ok vab =>
                          simp [hmul] at heval ⊢
                          cases hec : evalScalarExpr env c with
                          | error _ => simp [hec] at heval
                          | ok vc =>
                            rw [hec] at heval
                            have hec' : evalExpr env st (.scalar c') = .ok (vc, st) :=
                              ihc env st vc st (by simp [evalExpr, hec])
                            simp only [evalExpr] at hec'
                            cases hc' : evalScalarExpr env c' with
                            | error _ => simp [hc'] at hec'
                            | ok vc' =>
                              rw [hc'] at hec'
                              injection hec' with hpc
                              injection hpc with hvc
                              subst vc'
                              exact heval
              | binOp op l r =>
                cases op with
                | add =>
                  cases l with
                  | binOp op1 l1 r1 =>
                    cases op1 with
                    | mul =>
                      simp only [Bool.and_eq_true] at hcheck
                      rcases hcheck with ⟨⟨ha, hb⟩, hc⟩
                      have iha := checkSuperoptScalarVerified_sound a l1 ha
                      have ihb := checkSuperoptScalarVerified_sound b r1 hb
                      have ihc := checkSuperoptScalarVerified_sound c r hc
                      intro env st v st' heval
                      simp only [evalExpr, evalScalarExpr] at heval ⊢
                      cases hea : evalScalarExpr env a with
                      | error _ => simp [hea] at heval
                      | ok va =>
                        rw [hea] at heval
                        have hl1 : evalExpr env st (.scalar l1) = .ok (va, st) :=
                          iha env st va st (by simp [evalExpr, hea])
                        simp only [evalExpr] at hl1
                        cases hl1' : evalScalarExpr env l1 with
                        | error _ => simp [hl1'] at hl1
                        | ok vl1 =>
                          rw [hl1'] at hl1
                          injection hl1 with hpl1
                          injection hpl1 with hvl1
                          subst vl1
                          cases heb : evalScalarExpr env b with
                          | error _ => simp [heb] at heval
                          | ok vb =>
                            rw [heb] at heval
                            have hr1 : evalExpr env st (.scalar r1) = .ok (vb, st) :=
                              ihb env st vb st (by simp [evalExpr, heb])
                            simp only [evalExpr] at hr1
                            cases hr1' : evalScalarExpr env r1 with
                            | error _ => simp [hr1'] at hr1
                            | ok vr1 =>
                              rw [hr1'] at hr1
                              injection hr1 with hpr1
                              injection hpr1 with hvr1
                              subst vr1
                              cases hmul : evalBinOp .mul va vb with
                              | error err => simp [hmul] at heval
                              | ok vab =>
                                simp [hmul] at heval ⊢
                                cases hec : evalScalarExpr env c with
                                | error _ => simp [hec] at heval
                                | ok vc =>
                                  rw [hec] at heval
                                  have hr : evalExpr env st (.scalar r) = .ok (vc, st) :=
                                    ihc env st vc st (by simp [evalExpr, hec])
                                  simp only [evalExpr] at hr
                                  cases hr' : evalScalarExpr env r with
                                  | error _ => simp [hr'] at hr
                                  | ok vr =>
                                    rw [hr'] at hr
                                    injection hr with hpr
                                    injection hpr with hvr
                                    subst vr
                                    exact heval
                    | _ => cases hcheck
                  | _ => cases hcheck
                | _ => cases hcheck
              | _ => cases hcheck
termination_by e cand => sizeOf e + sizeOf cand


/-- Fold over synthesized candidates preserves `ExprRefines` relative to root `e0`. -/
theorem foldl_superopt_cands_sound (e0 : ScalarExpr) (p : HardwareCostProfile)
    (cands : List ScalarExpr) (acc : ScalarExpr)
    (hacc : ExprRefines (.scalar e0) (.scalar acc)) :
    ExprRefines (.scalar e0) (.scalar (cands.foldl (fun a cand =>
      let cCost := scalarExprCostWithProfile p cand
      let checksOk :=
        checkSuperoptScalarVerified e0 cand &&
        fastCheckScalarEquiv e0 cand &&
        symCheckScalarEquiv e0 cand
      if checksOk && cCost < scalarExprCostWithProfile p a then cand else a) acc)) := by
  induction cands generalizing acc with
  | nil => exact hacc
  | cons cand rest ih =>
    simp only [List.foldl]
    by_cases hcond :
        ((checkSuperoptScalarVerified e0 cand &&
          fastCheckScalarEquiv e0 cand &&
          symCheckScalarEquiv e0 cand) &&
         decide (scalarExprCostWithProfile p cand < scalarExprCostWithProfile p acc)) = true
    · have hv : checkSuperoptScalarVerified e0 cand = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        exact hcond.1.1.1
      rw [ite_eq_left hcond]
      exact ih cand (checkSuperoptScalarVerified_sound e0 cand hv)
    · rw [ite_eq_right hcond]
      exact ih acc hacc

/-- Core superoptimizer preserves scalar expression semantics. -/
theorem superoptScalarExprCore_sound (p : HardwareCostProfile) (targetLabel declName : String) (e : ScalarExpr) :
    ExprRefines (.scalar e) (.scalar (superoptScalarExprCore p targetLabel declName e).1) := by
  unfold superoptScalarExprCore
  simp only []
  let cands := synthesizeCandidates p.target e
  let bestCand := cands.foldl (fun acc cand =>
      let cCost := scalarExprCostWithProfile p cand
      let checksOk :=
        checkSuperoptScalarVerified e cand &&
        fastCheckScalarEquiv e cand &&
        symCheckScalarEquiv e cand
      if checksOk && cCost < scalarExprCostWithProfile p acc then cand else acc) e
  have hbest := foldl_superopt_cands_sound e p cands e (ExprRefines.refl _)
  change ExprRefines (.scalar e) (.scalar bestCand) at hbest
  split
  · exact hbest
  · exact ExprRefines.refl _

theorem superoptScalarExpr_sound (target : SuperoptTarget) (declName : String) (e : ScalarExpr) :
    ExprRefines (.scalar e) (.scalar (superoptScalarExpr target declName e).1) :=
  superoptScalarExprCore_sound (HardwareCostProfile.forTarget target) target.toString declName e

theorem superoptScalarExprWithProfile_sound (p : HardwareCostProfile) (declName : String) (e : ScalarExpr) :
    ExprRefines (.scalar e) (.scalar (superoptScalarExprWithProfile p declName e).1) :=
  superoptScalarExprCore_sound p s!"{p.target.toString}:{p.profileId}" declName e

/-- Custom scalar `parFor` kernel element forward refinement. -/
theorem evalParKernelElem_customScalar_refines (env : VarEnv) (st : HeapState)
    (inputs : List VarId) (len : Nat) (idxVar : VarId) (inVars : List VarId)
    (body body' : ScalarExpr) (i : Nat) (out : UInt64)
    (href : ExprRefines (.scalar body) (.scalar body'))
    (hsrc : evalParKernelElem env st inputs len (.customScalar idxVar inVars body) i = .ok out) :
    evalParKernelElem env st inputs len (.customScalar idxVar inVars body') i = .ok out := by
  unfold evalParKernelElem at hsrc ⊢
  cases hbind : bindCustomParInputs env st inputs i (env.bind idxVar (.u64 i.toUInt64)) 0 inVars with
  | error err => simp [hbind] at hsrc
  | ok kEnv =>
    simp only [hbind] at hsrc ⊢
    cases hbody : evalScalarExpr kEnv body with
    | error err => simp [hbody] at hsrc
    | ok v =>
      have htgt := href kEnv st v st (by simp [evalExpr, hbody])
      simp only [evalExpr] at htgt
      cases hbody' : evalScalarExpr kEnv body' with
      | error err => simp [hbody'] at htgt
      | ok v' =>
        rw [hbody'] at htgt
        injection htgt with hpair
        injection hpair with hv _
        subst hv
        rw [hbody] at hsrc
        exact hsrc

/-- Custom scalar `parFor` kernel loop forward refinement. -/
theorem evalParKernelLoop_customScalar_refines (env : VarEnv) (st : HeapState)
    (inputs : List VarId) (len : Nat) (idxVar : VarId) (inVars : List VarId)
    (body body' : ScalarExpr) (is : List Nat) (elems : List UInt64)
    (href : ExprRefines (.scalar body) (.scalar body'))
    (hsrc : evalParKernelLoop env st inputs len (.customScalar idxVar inVars body) is = .ok elems) :
    evalParKernelLoop env st inputs len (.customScalar idxVar inVars body') is = .ok elems := by
  induction is generalizing elems with
  | nil =>
    simp only [evalParKernelLoop] at hsrc ⊢
    exact hsrc
  | cons i rest ih =>
    simp only [evalParKernelLoop] at hsrc ⊢
    cases helem : evalParKernelElem env st inputs len (.customScalar idxVar inVars body) i with
    | error err => simp [helem] at hsrc
    | ok x =>
      cases hrest : evalParKernelLoop env st inputs len (.customScalar idxVar inVars body) rest with
      | error err => simp [helem, hrest] at hsrc
      | ok xs =>
        rw [helem, hrest] at hsrc
        have helem' :=
          evalParKernelElem_customScalar_refines env st inputs len idxVar inVars body body' i x href helem
        have hrest' := ih xs hrest
        rw [helem', hrest']
        exact hsrc

/-- Custom scalar `parFor` forward refinement. -/
theorem evalParFor_customScalar_refines (fuel : Nat) (env : VarEnv) (st : HeapState)
    (lenVar : VarId) (inputs : List VarId) (idxVar : VarId) (inVars : List VarId)
    (body body' : ScalarExpr) (pair : Val × HeapState)
    (href : ExprRefines (.scalar body) (.scalar body'))
    (hsrc : evalParFor fuel env st lenVar inputs (.customScalar idxVar inVars body) = .ok pair) :
    evalParFor fuel env st lenVar inputs (.customScalar idxVar inVars body') = .ok pair := by
  unfold evalParFor at hsrc ⊢
  cases hlen : env lenVar with
  | none => simp [hlen] at hsrc
  | some v =>
    rw [hlen] at hsrc
    cases v with
    | u64 n =>
      dsimp only [] at hsrc ⊢
      by_cases hfuel : (n.toNat > fuel)
      · simp [hfuel] at hsrc
      · simp only [hfuel, ↓reduceIte] at hsrc ⊢
        cases hvars : evalVarList env inputs with
        | error err => simp [hvars] at hsrc
        | ok vs =>
          rw [hvars] at hsrc
          cases hloop :
              evalParKernelLoop env st inputs n.toNat (.customScalar idxVar inVars body)
                (List.range n.toNat) with
          | error err => simp [hloop] at hsrc
          | ok elems =>
            rw [hloop] at hsrc
            have hloop' :=
              evalParKernelLoop_customScalar_refines env st inputs n.toNat idxVar inVars
                body body' (List.range n.toNat) elems href hloop
            rw [hloop']
            exact hsrc
    | _ => simp at hsrc

/-- Bounded sequential loop (`evalSeqLoop`) forward refinement. -/
theorem evalSeqLoop_refines (count curIdx : Nat) (idxVar accVar : VarId)
    (accVal : Val) (env : VarEnv) (st : HeapState)
    (step1 step2 : VarEnv → HeapState → Except UBError (Val × HeapState))
    (pair : Val × HeapState)
    (hstep : ∀ sEnv sSt v sSt', step1 sEnv sSt = .ok (v, sSt') → step2 sEnv sSt = .ok (v, sSt'))
    (hsrc : evalSeqLoop count curIdx idxVar accVar accVal env st step1 = .ok pair) :
    evalSeqLoop count curIdx idxVar accVar accVal env st step2 = .ok pair := by
  induction count generalizing curIdx accVal st with
  | zero =>
    simp only [evalSeqLoop] at hsrc ⊢
    exact hsrc
  | succ count' ih =>
    simp only [evalSeqLoop] at hsrc ⊢
    cases hs1 : step1 ((env.bind idxVar (.u64 curIdx.toUInt64)).bind accVar accVal) st with
    | error err => simp [hs1] at hsrc
    | ok p1 =>
      rcases p1 with ⟨nextAcc, st1⟩
      rw [hs1] at hsrc
      have hs2 :=
        hstep ((env.bind idxVar (.u64 curIdx.toUInt64)).bind accVar accVal) st nextAcc st1 hs1
      rw [hs2]
      exact ih (curIdx + 1) nextAcc st1 hsrc

/-- Code-level superoptimizer preserves operational semantics (`CodeRefines`). -/
theorem superoptCodeCore_sound (p : HardwareCostProfile) (targetLabel declName : String)
    (code : LNIRCode) :
    CodeRefines code (superoptCodeCore p targetLabel declName code).1 := by
  induction code with
  | letBind dst ty val k ih =>
    cases val with
    | scalar se =>
      simp only [superoptCodeCore]
      exact CodeRefines.letBind_congr (superoptScalarExprCore_sound p targetLabel declName se) ih
    | _ =>
      simp only [superoptCodeCore]
      exact CodeRefines.letBind_congr (ExprRefines.refl _) ih
  | rawStore pv iv vv ety k ih =>
    simp only [superoptCodeCore]
    exact CodeRefines.rawStore_congr ih
  | incRef ov c k ih =>
    simp only [superoptCodeCore]
    exact CodeRefines.incRef_congr ih
  | decRef ov c k ih =>
    simp only [superoptCodeCore]
    exact CodeRefines.decRef_congr ih
  | ite cv t e iht ihe =>
    simp only [superoptCodeCore]
    exact CodeRefines.ite_congr iht ihe
  | seqFor iv lv hv av ai aty step k ihs ihk =>
    intro fuel env st v st' hsrc
    simp only [superoptCodeCore, evalCode] at hsrc ⊢
    cases hlo : env lv with
    | none => simp [hlo] at hsrc
    | some vlo =>
      cases hhi : env hv with
      | none => simp [hlo, hhi] at hsrc
      | some vhi =>
        cases hinit : env ai with
        | none => simp [hlo, hhi, hinit] at hsrc
        | some vinit =>
          simp only [hlo, hhi, hinit] at hsrc ⊢
          cases vlo <;> cases vhi <;> try simp at hsrc
          rename_i lo hi
          dsimp only [] at hsrc ⊢
          cases hloop :
              evalSeqLoop (hi.toNat - lo.toNat) lo.toNat iv av vinit env st
                (fun stepEnv stepSt => evalCode fuel stepEnv stepSt step) with
          | error err => simp [hloop] at hsrc
          | ok pair =>
            rw [hloop] at hsrc
            have hloop' :=
              evalSeqLoop_refines (hi.toNat - lo.toNat) lo.toNat iv av vinit env st
                (fun stepEnv stepSt => evalCode fuel stepEnv stepSt step)
                (fun stepEnv stepSt =>
                  evalCode fuel stepEnv stepSt (superoptCodeCore p targetLabel declName step).1)
                pair (fun sEnv sSt sv sSt' hs => ihs fuel sEnv sSt sv sSt' hs) hloop
            rw [hloop']
            exact ihk fuel (env.bind av pair.1) pair.2 v st' hsrc
  | parFor ov lv ins ety kern k ih =>
    cases kern with
    | customScalar idxVar inVars body =>
      intro fuel env st v st' hsrc
      simp only [superoptCodeCore, evalCode] at hsrc ⊢
      cases hpar : evalParFor fuel env st lv ins (.customScalar idxVar inVars body) with
      | error err => simp [hpar] at hsrc
      | ok pair =>
        rw [hpar] at hsrc
        have hbody := superoptScalarExprCore_sound p targetLabel declName body
        have hpar' :=
          evalParFor_customScalar_refines fuel env st lv ins idxVar inVars body
            (superoptScalarExprCore p targetLabel declName body).1 pair hbody hpar
        rw [hpar']
        exact ih fuel (env.bind ov pair.1) pair.2 v st' hsrc
    | _ =>
      simp only [superoptCodeCore]
      exact CodeRefines.parFor_congr ih
  | ret _ =>
    simp only [superoptCodeCore]
    exact CodeRefines.refl _
  | unreachable =>
    simp only [superoptCodeCore]
    exact CodeRefines.refl _

theorem superoptCode_sound (target : SuperoptTarget) (declName : String) (code : LNIRCode) :
    CodeRefines code (superoptCode target declName code).1 :=
  superoptCodeCore_sound (HardwareCostProfile.forTarget target) target.toString declName code

theorem superoptDeclCore_sound (p : HardwareCostProfile) (targetLabel : String) (d : LNIRDecl) :
    CodeRefines d.body (superoptDeclCore p targetLabel d).1.body := by
  unfold superoptDeclCore
  simp only []
  exact superoptCodeCore_sound p targetLabel d.name d.body

/-- Declaration-level superoptimizer soundness (`superoptDecl_sound`). -/
theorem superoptDecl_sound (target : SuperoptTarget) (d : LNIRDecl) :
    CodeRefines d.body (superoptDecl target d).1.body :=
  superoptDeclCore_sound (HardwareCostProfile.forTarget target) target.toString d

theorem foldl_decls_mem_acc (p : HardwareCostProfile) (targetLabel : String)
    (ds : List LNIRDecl) (dAcc : List LNIRDecl) (rAcc : List SuperoptRewriteRecord)
    (x : LNIRDecl) (hx : x ∈ dAcc) :
    x ∈ (ds.foldl (fun (accD, accR) d =>
      let (d', recs) := superoptDeclCore p targetLabel d
      (accD ++ [d'], accR ++ recs)) (dAcc, rAcc)).1 := by
  induction ds generalizing dAcc rAcc with
  | nil => exact hx
  | cons d0 rest ih =>
    simp only [List.foldl]
    exact ih (dAcc ++ [(superoptDeclCore p targetLabel d0).1])
      (rAcc ++ (superoptDeclCore p targetLabel d0).2) (List.mem_append_left _ hx)

theorem foldl_decls_refines (p : HardwareCostProfile) (targetLabel : String)
    (ds : List LNIRDecl) (dAcc : List LNIRDecl) (rAcc : List SuperoptRewriteRecord) :
    ∀ d ∈ ds, ∃ d' ∈ (ds.foldl (fun (accD, accR) d =>
      let (d', recs) := superoptDeclCore p targetLabel d
      (accD ++ [d'], accR ++ recs)) (dAcc, rAcc)).1, CodeRefines d.body d'.body := by
  intro d hd
  induction ds generalizing dAcc rAcc with
  | nil => cases hd
  | cons d0 rest ih =>
    simp only [List.foldl, List.mem_cons] at hd ⊢
    cases hd with
    | inl heq =>
      subst d
      refine ⟨(superoptDeclCore p targetLabel d0).1, ?_, superoptDeclCore_sound p targetLabel d0⟩
      exact foldl_decls_mem_acc p targetLabel rest
        (dAcc ++ [(superoptDeclCore p targetLabel d0).1])
        (rAcc ++ (superoptDeclCore p targetLabel d0).2)
        (superoptDeclCore p targetLabel d0).1
        (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    | inr hmem =>
      exact ih (dAcc ++ [(superoptDeclCore p targetLabel d0).1])
        (rAcc ++ (superoptDeclCore p targetLabel d0).2) hmem

/-- Module-level superoptimizer soundness (`superoptModuleCore_sound`). -/
theorem superoptModuleCore_sound (p : HardwareCostProfile) (targetLabel : String) (m : LNIRModule) :
    ∀ d ∈ m.decls, ∃ d' ∈ (superoptModuleCore p targetLabel m).1.decls,
      CodeRefines d.body d'.body := by
  intro d hd
  unfold superoptModuleCore
  exact foldl_decls_refines p targetLabel m.decls [] [] d hd

/-- Module-level superoptimizer soundness (`superoptModule_sound`). -/
theorem superoptModule_sound (target : SuperoptTarget) (m : LNIRModule) :
    ∀ d ∈ m.decls, ∃ d' ∈ (superoptModule target m).1.decls, CodeRefines d.body d'.body :=
  superoptModuleCore_sound (HardwareCostProfile.forTarget target) target.toString m

/-- Profile-guided module-level superoptimizer soundness (`superoptModuleWithProfile_sound`). -/
theorem superoptModuleWithProfile_sound (p : HardwareCostProfile) (m : LNIRModule) :
    ∀ d ∈ m.decls, ∃ d' ∈ (superoptModuleWithProfile p m).1.decls, CodeRefines d.body d'.body :=
  superoptModuleCore_sound p s!"{p.target.toString}:{p.profileId}" m

end LeanNative.Proofs
