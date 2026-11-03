import LeanNative.Proofs.SymbolicTVSoundness

namespace LeanNative.Proofs
set_option maxHeartbeats 40000

open LeanNative.IR
open LeanNative.Semantics

/-!
# Pure 64-Bit Symbolic Normalization & Scalar Evaluation Helpers (`LeanNative.Proofs.SymbolicTVCodeHelpers`)

Proves purity preservation (`isPureU64SymExprIn`) across `normSymUnaryOpStep`, `normSymBinOpCore`,
`normSymBinOpStep`, `normSymExpr`, and `symBinOpIdentityShortCircuit?`, together with concrete
scalar denotation soundness (`symEvalScalarRes_ssaPureU64_sound`) for `SymbolicTVCodeSoundness`.
-/

theorem symExprScalarSort_of_isPureU64SymExprIn (st : SymExecState) (params : List VarId)
    (hbool : st.boolVars = [])
    (hpar : ∀ p : VarId, params.contains p = true → st.u64Vars.contains p = true) :
    ∀ (s : SymExpr), isPureU64SymExprIn params s = true → symExprScalarSort? st s = some sortU64
  | .constU64 _, _ => rfl
  | .symVar id, hp => by
    have hu64 := hpar id hp
    unfold symExprScalarSort?
    rw [hbool, hu64]
    rfl
  | .unaryOp .not a, hp => by
    simp only [isPureU64SymExprIn] at hp
    exact symExprScalarSort_of_isPureU64SymExprIn st params hbool hpar a hp
  | .unaryOp .neg a, hp => by
    simp only [isPureU64SymExprIn] at hp
    exact symExprScalarSort_of_isPureU64SymExprIn st params hbool hpar a hp
  | .unaryOp .clz256 _, hp => by simp [isPureU64SymExprIn] at hp
  | .binOp op l r, hp => by
    simp only [isPureU64SymExprIn, Bool.and_eq_true] at hp
    rcases hp with ⟨⟨hop, hl⟩, hr⟩
    exact symExprScalarSort_pureU64_binOp st op l r hop
      (symExprScalarSort_of_isPureU64SymExprIn st params hbool hpar l hl)
      (symExprScalarSort_of_isPureU64SymExprIn st params hbool hpar r hr)
  | .constU256 _, hp | .constBool _, hp | .allocTag _, hp | .rcSym _ _, hp
  | .ctorTag _ _, hp | .ctorLen _ _ _, hp | .sarrayLen _, hp
  | .mulDiv256 _ _ _ _, hp | .ite _ _ _, hp | .tuple _, hp
  | .bufElem _ _ _, hp | .unit, hp => by
    simp [isPureU64SymExprIn] at hp
termination_by s => sizeOf s

theorem isPureU64SymExprIn_not_tuple {vars : List VarId} {s : SymExpr}
    (hp : isPureU64SymExprIn vars s = true) :
    isTupleSymExpr s = false := by
  cases s <;> try rfl
  simp [isPureU64SymExprIn] at hp

theorem isPureU64SymExprIn_binOp_constU64_sub {vars : List VarId} {op : BinOp} {x : SymExpr} {a : UInt64}
    (hop : op = .add ∨ op = .sub)
    (h : isPureU64SymExprIn vars (.binOp op x (.constU64 a)) = true) :
    isPureU64SymExprIn vars x = true := by
  rcases hop with rfl | rfl <;>
  · simp only [isPureU64SymExprIn, Bool.and_eq_true] at h
    exact h.1.2

theorem normSymUnaryOpStep_pureU64In (vars : List VarId) (op : UnaryOp) (a : SymExpr)
    (hop : op = .not ∨ op = .neg)
    (ha : isPureU64SymExprIn vars a = true) :
    isPureU64SymExprIn vars (normSymUnaryOpStep op a) = true := by
  rcases hop with rfl | rfl
  · cases a with
    | constU64 _ => rfl
    | symVar _ | binOp _ _ _ => exact ha
    | unaryOp op2 x =>
      cases op2 <;> try exact ha
      have hx : isPureU64SymExprIn vars x = true := ha
      rw [normSymUnaryOpStep.eq_def]
      dsimp only []
      cases x with
      | constU64 _ => exact hx
      | symVar _ | unaryOp _ _ => exact ha
      | binOp _ _ _ => cases atomDefinitelyBool _ <;> exact hx
      | constU256 _ | constBool _ | allocTag _ | rcSym _ _ | ctorTag _ _ | ctorLen _ _ _
      | sarrayLen _ | mulDiv256 _ _ _ _ | ite _ _ _ | tuple _ | bufElem _ _ _ | unit =>
        simp [isPureU64SymExprIn] at hx
    | constU256 _ | constBool _ | allocTag _ | rcSym _ _ | ctorTag _ _ | ctorLen _ _ _
    | sarrayLen _ | mulDiv256 _ _ _ _ | ite _ _ _ | tuple _ | bufElem _ _ _ | unit =>
      simp [isPureU64SymExprIn] at ha
  · cases a with
    | constU64 _ => rfl
    | symVar _ | binOp _ _ _ => exact ha
    | unaryOp op2 x =>
      cases op2 <;> try exact ha
      have hx : isPureU64SymExprIn vars x = true := ha
      rw [normSymUnaryOpStep.eq_def]
      dsimp only []
      cases exprDefinitely64 x <;> exact hx
    | constU256 _ | constBool _ | allocTag _ | rcSym _ _ | ctorTag _ _ | ctorLen _ _ _
    | sarrayLen _ | mulDiv256 _ _ _ _ | ite _ _ _ | tuple _ | bufElem _ _ _ | unit =>
      simp [isPureU64SymExprIn] at ha

theorem normSymBinOpCore_pureU64In (vars : List VarId) (op : BinOp) (l r : SymExpr) (w64 : Bool)
    (hop : (match op with
            | .add | .sub | .mul | .div | .mod | .bitAnd | .bitOr | .bitXor
            | .shl | .shr | .clmul64 | .clmul64Hi | .gf2Affine | .eor3 => true
            | .sar | .eq | .lt | .le | .addChecked256 | .subChecked256 | .mulChecked256 => false) = true)
    (hl : isPureU64SymExprIn vars l = true)
    (hr : isPureU64SymExprIn vars r = true) :
    isPureU64SymExprIn vars (normSymBinOpCore op l r w64) = true := by
  have deflt : isPureU64SymExprIn vars (.binOp op l r) = true := by
    simp only [isPureU64SymExprIn, Bool.and_eq_true]
    exact ⟨⟨hop, hl⟩, hr⟩
  cases op <;> dsimp only [normSymBinOpCore]
  case add =>
    split
    · rfl
    · simp [isPureU64SymExprIn] at hl
    · simp [isPureU64SymExprIn] at hr
    · simp [isPureU64SymExprIn] at hl
    · exact hl
    · exact hr
    · have hx := isPureU64SymExprIn_binOp_constU64_sub (Or.inl rfl) hl
      split
      · split
        · exact hx
        · simp [isPureU64SymExprIn, hx]
      · simp [isPureU64SymExprIn, hx]
    · have hx := isPureU64SymExprIn_binOp_constU64_sub (Or.inr rfl) hl
      split
      · split
        · exact hx
        · split <;> simp [isPureU64SymExprIn, hx]
      · simp [isPureU64SymExprIn, hx]
    · exact deflt
  case sub =>
    split
    · rfl
    · simp [isPureU64SymExprIn] at hl
    · simp [isPureU64SymExprIn] at hr
    · exact hl
    · have hx := isPureU64SymExprIn_binOp_constU64_sub (Or.inl rfl) hl
      split
      · split
        · exact hx
        · split <;> simp [isPureU64SymExprIn, hx]
      · simp [isPureU64SymExprIn, hx]
    · have hx := isPureU64SymExprIn_binOp_constU64_sub (Or.inr rfl) hl
      split
      · split
        · exact hx
        · simp [isPureU64SymExprIn, hx]
      · simp [isPureU64SymExprIn, hx]
    · split
      · rfl
      · cases l with
        | constU256 _ => simp [isPureU64SymExprIn] at hl
        | _ => exact deflt
  case mul =>
    split
    · rfl
    · simp [isPureU64SymExprIn] at hl
    · simp [isPureU64SymExprIn] at hr
    · simp [isPureU64SymExprIn] at hl
    · exact hl
    · exact hr
    · split
      · rfl
      · simp [isPureU64SymExprIn, hl]
    · split
      · rfl
      · simp [isPureU64SymExprIn, hr]
    · split
      · split <;> simp [isPureU64SymExprIn, hl]
      · simp [isPureU64SymExprIn, hl]
    · split
      · split <;> simp [isPureU64SymExprIn, hr]
      · simp [isPureU64SymExprIn, hr]
    · exact deflt
  case div =>
    split
    · rfl
    · simp [isPureU64SymExprIn] at hr
    · split
      · rfl
      · simp [isPureU64SymExprIn, hl]
    · exact hl
    · split
      · split <;> simp [isPureU64SymExprIn, hl]
      · simp [isPureU64SymExprIn, hl]
    · exact deflt
  case mod =>
    split
    · rfl
    · split
      · exact hl
      · simp [isPureU64SymExprIn, hl]
    · split
      · rfl
      · simp [isPureU64SymExprIn, hl]
    · split
      · split <;> simp [isPureU64SymExprIn, hl]
      · simp [isPureU64SymExprIn, hl]
    · exact deflt
  case bitAnd =>
    split
    · rfl
    · simp [isPureU64SymExprIn] at hl
    · simp [isPureU64SymExprIn] at hr
    · simp [isPureU64SymExprIn] at hl
    · split
      · rfl
      · simp [isPureU64SymExprIn, hl]
    · split
      · rfl
      · simp [isPureU64SymExprIn, hr]
    · split
      · exact hl
      · exact deflt
  case bitOr =>
    split
    · rfl
    · simp [isPureU64SymExprIn] at hl
    · simp [isPureU64SymExprIn] at hr
    · simp [isPureU64SymExprIn] at hl
    · exact hl
    · exact hr
    · split
      · exact hl
      · exact deflt
  case bitXor =>
    split
    · rfl
    · simp [isPureU64SymExprIn] at hl
    · simp [isPureU64SymExprIn] at hr
    · simp [isPureU64SymExprIn] at hl
    · exact hl
    · exact hr
    · split
      · rfl
      · cases l with
        | constU256 _ => simp [isPureU64SymExprIn] at hl
        | _ => exact deflt
  case shl =>
    split
    · rfl
    · simp [isPureU64SymExprIn] at hl
    · simp [isPureU64SymExprIn] at hr
    · exact hl
    · exact deflt
  case shr =>
    split
    · rfl
    · simp [isPureU64SymExprIn] at hl
    · simp [isPureU64SymExprIn] at hr
    · exact hl
    · exact deflt
  case clmul64 => split <;> simp [isPureU64SymExprIn, hl, hr]
  case clmul64Hi => split <;> simp [isPureU64SymExprIn, hl, hr]
  case gf2Affine => split <;> simp [isPureU64SymExprIn, hl, hr]
  case eor3 => split <;> simp [isPureU64SymExprIn, hl, hr]
  case sar | eq | lt | le | addChecked256 | subChecked256 | mulChecked256 => cases hop

theorem normSymBinOpStep_pureU64In (vars : List VarId) (op : BinOp) (l r : SymExpr) (w64 : Bool)
    (hop : (match op with
            | .add | .sub | .mul | .div | .mod | .bitAnd | .bitOr | .bitXor
            | .shl | .shr | .clmul64 | .clmul64Hi | .gf2Affine | .eor3 => true
            | .sar | .eq | .lt | .le | .addChecked256 | .subChecked256 | .mulChecked256 => false) = true)
    (hl : isPureU64SymExprIn vars l = true)
    (hr : isPureU64SymExprIn vars r = true) :
    isPureU64SymExprIn vars (normSymBinOpStep op l r w64) = true := by
  unfold normSymBinOpStep
  cases (SymExpr.isCommutative op && decide (SymExpr.rank l > SymExpr.rank r))
  · exact normSymBinOpCore_pureU64In vars op l r _ hop hl hr
  · exact normSymBinOpCore_pureU64In vars op r l _ hop hr hl

theorem normSymExpr_pureU64In (vars : List VarId) :
    ∀ (s : SymExpr), isPureU64SymExprIn vars s = true → isPureU64SymExprIn vars (normSymExpr s) = true
  | .constU64 _, _ => rfl
  | .symVar _, hp => hp
  | .unaryOp .not a, hp => by
    simp only [isPureU64SymExprIn] at hp
    rw [normSymExpr.eq_def]; dsimp only []
    exact normSymUnaryOpStep_pureU64In vars .not _ (Or.inl rfl) (normSymExpr_pureU64In vars a hp)
  | .unaryOp .neg a, hp => by
    simp only [isPureU64SymExprIn] at hp
    rw [normSymExpr.eq_def]; dsimp only []
    exact normSymUnaryOpStep_pureU64In vars .neg _ (Or.inr rfl) (normSymExpr_pureU64In vars a hp)
  | .unaryOp .clz256 _, hp => by simp [isPureU64SymExprIn] at hp
  | .binOp op l r, hp => by
    simp only [isPureU64SymExprIn, Bool.and_eq_true] at hp
    rcases hp with ⟨⟨hop, hl⟩, hr⟩
    rw [normSymExpr.eq_def]; dsimp only []
    exact normSymBinOpStep_pureU64In vars op _ _ false hop
      (normSymExpr_pureU64In vars l hl) (normSymExpr_pureU64In vars r hr)
  | .constU256 _, hp | .constBool _, hp | .allocTag _, hp | .rcSym _ _, hp
  | .ctorTag _ _, hp | .ctorLen _ _ _, hp | .sarrayLen _, hp
  | .mulDiv256 _ _ _ _, hp | .ite _ _ _, hp | .tuple _, hp
  | .bufElem _ _ _, hp | .unit, hp => by
    simp [isPureU64SymExprIn] at hp
termination_by s => sizeOf s

theorem symBinOpIdentityShortCircuit_pureU64In {vars : List VarId} {op : BinOp} {l r idExpr : SymExpr}
    (hl : isPureU64SymExprIn vars l = true)
    (hr : isPureU64SymExprIn vars r = true)
    (hid : symBinOpIdentityShortCircuit? op l r = some idExpr) :
    isPureU64SymExprIn vars idExpr = true := by
  unfold symBinOpIdentityShortCircuit? at hid
  split at hid
  · cases hid; exact hl
  · cases hid; exact hr
  · cases hid; exact hl
  · cases hid; exact hl
  · cases hid; exact hr
  · cases hid; exact hl
  · cases hid; exact hl
  · cases hid; exact hr
  · cases hid; exact hl
  · cases hid; exact hr
  · cases hid; exact hl
  · cases hid; exact hl
  · by_cases hlr : (l == r) = true <;> simp [hlr] at hid
    subst hid
    exact hl
  · by_cases hlr : (l == r) = true <;> simp [hlr] at hid
    subst hid
    exact hl
  · cases hid

theorem symEvalScalarRes_ssaPureU64_sound
    {ω0 : SymValuation} {params bound : List VarId} {st : SymExecState} {env : VarEnv}
    (hst : PureU64SymState ω0 params bound st env) :
    ∀ (e : ScalarExpr),
      isPureU64ScalarExpr e = true →
      scalarExprAllBound bound e = true →
      ∃ n : UInt64,
        evalScalarExpr env e = .ok (.u64 n) ∧
        (symEvalScalarRes st e).unsupported = false ∧
        (symEvalScalarRes st e).ubCond = .constBool true ∧
        (symEvalScalarRes st e).val.noUB = true ∧
        isPureU64SymExprIn params (symEvalScalarRes st e).val.expr = true ∧
        symExprScalarSort? st (symEvalScalarRes st e).val.expr = some sortU64 ∧
        denoteSymExpr ω0 (symEvalScalarRes st e).val.expr = .ok (.u64 n) := by
  rcases hst with ⟨_, _, _, _, _, _, _, _, _, hbool, _, _, _, _, _, _, hpar, hbound⟩
  have hparSort : ∀ p : VarId, params.contains p = true → st.u64Vars.contains p = true :=
    fun p hp => (hpar p hp).1
  intro e hpure hall
  induction e with
  | constU64 v =>
    exact ⟨v, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | constBool _ | select _ _ _ _ _ _ | fma _ _ _ _ _ _ =>
    simp [isPureU64ScalarExpr] at hpure
  | var id =>
    simp only [scalarExprAllBound] at hall
    obtain ⟨n, henv, hnoub, hpIn, hden⟩ := hbound id hall
    have hsort := symExprScalarSort_of_isPureU64SymExprIn st params hbool hparSort _ hpIn
    refine ⟨n, ?_, rfl, ?_, hnoub, hpIn, hsort, hden⟩
    · simp [evalScalarExpr, henv]
    · simp [symEvalScalarRes, hnoub]
  | unaryOp op a iha =>
    have hfalse : (SymExpr.constBool true == SymExpr.constBool false) = false := rfl
    cases op with
    | clz256 => simp [isPureU64ScalarExpr] at hpure
    | not =>
      simp only [isPureU64ScalarExpr] at hpure
      simp only [scalarExprAllBound] at hall
      obtain ⟨na, heval, hunsup, hub, hnoub, hpIn, hsort, hden⟩ := iha hpure hall
      have hpIn' := normSymUnaryOpStep_pureU64In params .not _ (Or.inl rfl) hpIn
      refine ⟨~~~na, ?_, ?_⟩
      · simp [evalScalarExpr, heval, evalUnaryOp]
      · rw [symEvalScalarRes.eq_def]
        dsimp only []
        rw [hunsup, hub, hsort, hfalse]
        exact ⟨rfl, rfl, hnoub, hpIn',
          symExprScalarSort_of_isPureU64SymExprIn st params hbool hparSort _ hpIn',
          by
            change denoteSymExpr ω0 (normSymUnaryOpStep .not (symEvalScalarRes st a).val.expr) = _
            rw [normSymUnaryOpStep_denotes_eq]; simp only [denoteSymExpr, hden]; rfl⟩
    | neg =>
      simp only [isPureU64ScalarExpr] at hpure
      simp only [scalarExprAllBound] at hall
      obtain ⟨na, heval, hunsup, hub, hnoub, hpIn, hsort, hden⟩ := iha hpure hall
      have hpIn' := normSymUnaryOpStep_pureU64In params .neg _ (Or.inr rfl) hpIn
      refine ⟨0 - na, ?_, ?_⟩
      · simp [evalScalarExpr, heval, evalUnaryOp]
      · rw [symEvalScalarRes.eq_def]
        dsimp only []
        rw [hunsup, hub, hsort, hfalse]
        exact ⟨rfl, rfl, hnoub, hpIn',
          symExprScalarSort_of_isPureU64SymExprIn st params hbool hparSort _ hpIn',
          by
            change denoteSymExpr ω0 (normSymUnaryOpStep .neg (symEvalScalarRes st a).val.expr) = _
            rw [normSymUnaryOpStep_denotes_eq]; simp only [denoteSymExpr, hden]; rfl⟩
  | binOp op l r ihl ihr =>
    simp only [isPureU64ScalarExpr, Bool.and_eq_true] at hpure
    simp only [scalarExprAllBound, Bool.and_eq_true] at hall
    rcases hpure with ⟨⟨hop, hlPure⟩, hrPure⟩
    rcases hall with ⟨hlAll, hrAll⟩
    obtain ⟨nl, hlEval, hlUnsup, hlUb, hlNoUb, hlIn, hlSort, hlDen⟩ := ihl hlPure hlAll
    obtain ⟨nr, hrEval, hrUnsup, hrUb, hrNoUb, hrIn, hrSort, hrDen⟩ := ihr hrPure hrAll
    have hevalU64 : ∃ n : UInt64, evalBinOp op (.u64 nl) (.u64 nr) = .ok (.u64 n) := by
      cases op <;> simp at hop <;> exact ⟨_, rfl⟩
    obtain ⟨n, hn⟩ := hevalU64
    refine ⟨n, ?_, ?_⟩
    · simp only [evalScalarExpr, hlEval, hrEval, hn]
    · rw [symEvalScalarRes.eq_def]
      dsimp only []
      have hfalse : (SymExpr.constBool true == SymExpr.constBool false) = false := rfl
      rw [hlUnsup, hrUnsup, hlUb, hrUb, hfalse]
      dsimp only [Bool.false_or, ↓reduceIte, SymExecState.conjoinUbCond]
      cases hid : symBinOpIdentityShortCircuit? op (symEvalScalarRes st l).val.expr (symEvalScalarRes st r).val.expr with
      | some idExpr =>
        dsimp only [SymExecState.conjoinUbCond]
        obtain ⟨hIdSort, hIdDen⟩ :=
          symBinOpIdentityShortCircuit_u64 st ω0 op _ _ idExpr nl nr hlSort hrSort hlDen hrDen hid
        exact ⟨rfl, rfl, by simp [hlNoUb, hrNoUb],
          symBinOpIdentityShortCircuit_pureU64In hlIn hrIn hid, hIdSort, hIdDen.trans hn⟩
      | none =>
        rw [hlSort, hrSort]
        have hstepIn := normSymBinOpStep_pureU64In params op _ _ true hop hlIn hrIn
        have hstepSort := normSymBinOpStep_sortU64 st op _ _ true hop hlSort hrSort
        have hstepDen := (normSymBinOpStep_u64_denotes ω0 op _ _ true nl nr hlDen hrDen).trans hn
        have hno : ((symEvalScalarRes st l).val.noUB && (symEvalScalarRes st r).val.noUB && true) = true := by
          simp [hlNoUb, hrNoUb]
        cases op <;> simp at hop <;> exact ⟨rfl, rfl, hno, hstepIn, hstepSort, hstepDen⟩

end LeanNative.Proofs
