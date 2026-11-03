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
# Superoptimizer Structural & Pure-U64 Helper Lemmas (`LeanNative.Proofs.SuperoptHelpersSoundness`)

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


end LeanNative.Proofs
