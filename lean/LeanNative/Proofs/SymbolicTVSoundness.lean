import LeanNative.Proofs.SymbolicTVBinOpSoundness

namespace LeanNative.Proofs
set_option maxHeartbeats 40000

open LeanNative.IR
open LeanNative.Semantics

/-!
# Kernel-Checked Soundness of `SymbolicTV` (`LeanNative.Proofs.SymbolicTVSoundness`)

Proves sort preservation, `symEvalScalarRes_pureU64_sound`, `normSymExpr_pureU64_denotes`,
and end-to-end `validateTranslationDeclSound_of_passed` / `checkSingleSample_sound`.
-/

/-- Subexpression sort extraction for `(x ± constU64 a)` when its `symExprScalarSort?` is `some sortU64`. -/
theorem symExprScalarSort_binOp_constU64_u64 (st : SymExecState) (op : BinOp) (x : SymExpr) (a : UInt64)
    (hop : op = .add ∨ op = .sub)
    (hsort : symExprScalarSort? st (.binOp op x (.constU64 a)) = some sortU64) :
    symExprScalarSort? st x = some sortU64 := by
  rcases hop with rfl | rfl <;>
  · dsimp only [symExprScalarSort?] at hsort
    change (match symExprScalarSort? st x, some sortU64 with
      | some 2, _ | _, some 2 => some sortU256
      | some 1, some 1 => some sortU64
      | _, _ => none) = some sortU64 at hsort
    cases hx : symExprScalarSort? st x with
    | none => rw [hx] at hsort; cases hsort
    | some k =>
      rw [hx] at hsort
      match k with
      | 1 => rfl
      | 2 => cases hsort
      | 0 => cases hsort
      | n + 3 => cases hsort

/-- Helper: pure-U64 binary operators preserve `some sortU64` on `.binOp op l r`. -/
theorem symExprScalarSort_pureU64_binOp (st : SymExecState) (op : BinOp) (l r : SymExpr)
    (hop : (match op with
            | .add | .sub | .mul | .div | .mod | .bitAnd | .bitOr | .bitXor
            | .shl | .shr | .clmul64 | .clmul64Hi | .gf2Affine | .eor3 => true
            | .sar | .eq | .lt | .le | .addChecked256 | .subChecked256 | .mulChecked256 => false) = true)
    (hl : symExprScalarSort? st l = some sortU64)
    (hr : symExprScalarSort? st r = some sortU64) :
    symExprScalarSort? st (.binOp op l r) = some sortU64 := by
  have hl1 : symExprScalarSort? st l = some 1 := hl
  have hr1 : symExprScalarSort? st r = some 1 := hr
  cases op <;> try (cases hop; done)
  all_goals try (dsimp only [symExprScalarSort?]; rw [hl1, hr1]; rfl)
  all_goals rfl

/-- `normSymBinOpCore` preserves `some sortU64` for every pure-U64 binary operator. -/
theorem normSymBinOpCore_sortU64 (st : SymExecState) (op : BinOp) (l r : SymExpr) (w64 : Bool)
    (hop : (match op with
            | .add | .sub | .mul | .div | .mod | .bitAnd | .bitOr | .bitXor
            | .shl | .shr | .clmul64 | .clmul64Hi | .gf2Affine | .eor3 => true
            | .sar | .eq | .lt | .le | .addChecked256 | .subChecked256 | .mulChecked256 => false) = true)
    (hl : symExprScalarSort? st l = some sortU64)
    (hr : symExprScalarSort? st r = some sortU64) :
    symExprScalarSort? st (normSymBinOpCore op l r w64) = some sortU64 := by
  have deflt : symExprScalarSort? st (.binOp op l r) = some sortU64 :=
    symExprScalarSort_pureU64_binOp st op l r hop hl hr
  have hl1 : symExprScalarSort? st l = some 1 := hl
  have hr1 : symExprScalarSort? st r = some 1 := hr
  cases op <;> dsimp only [normSymBinOpCore]
  case add =>
    split
    · rfl
    · cases hl1
    · cases hr1
    · cases hl1
    · exact hl
    · exact hr
    · split
      · have hx := symExprScalarSort_binOp_constU64_u64 st .add _ _ (Or.inl rfl) hl
        split
        · exact hx
        · exact symExprScalarSort_pureU64_binOp st .add _ _ rfl hx rfl
      · exact deflt
    · split
      · have hx := symExprScalarSort_binOp_constU64_u64 st .sub _ _ (Or.inr rfl) hl
        split
        · exact hx
        · split
          · exact symExprScalarSort_pureU64_binOp st .add _ _ rfl hx rfl
          · exact symExprScalarSort_pureU64_binOp st .sub _ _ rfl hx rfl
      · exact deflt
    · exact deflt
  case sub =>
    split
    · rfl
    · cases hl1
    · cases hr1
    · exact hl
    · split
      · have hx := symExprScalarSort_binOp_constU64_u64 st .add _ _ (Or.inl rfl) hl
        split
        · exact hx
        · split
          · exact symExprScalarSort_pureU64_binOp st .add _ _ rfl hx rfl
          · exact symExprScalarSort_pureU64_binOp st .sub _ _ rfl hx rfl
      · exact deflt
    · split
      · have hx := symExprScalarSort_binOp_constU64_u64 st .sub _ _ (Or.inr rfl) hl
        split
        · exact hx
        · exact symExprScalarSort_pureU64_binOp st .sub _ _ rfl hx rfl
      · exact deflt
    · split
      · rfl
      · cases l with
        | constU256 _ => cases hl1
        | _ => exact deflt
  case mul =>
    split
    · rfl
    · cases hl1
    · cases hr1
    · cases hl1
    · exact hl
    · exact hr
    · split
      · rfl
      · exact deflt
    · split
      · rfl
      · exact deflt
    · split
      · split
        · exact symExprScalarSort_pureU64_binOp st .shl _ _ rfl hl rfl
        · exact deflt
      · exact deflt
    · split
      · split
        · exact symExprScalarSort_pureU64_binOp st .shl _ _ rfl hr rfl
        · exact deflt
      · exact deflt
    · exact deflt
  case div =>
    split
    · rfl
    · cases hr1
    · split
      · rfl
      · exact deflt
    · exact hl
    · split
      · split
        · exact symExprScalarSort_pureU64_binOp st .shr _ _ rfl hl rfl
        · exact deflt
      · exact deflt
    · exact deflt
  case mod =>
    split
    · rfl
    · split
      · exact hl
      · exact deflt
    · split
      · rfl
      · exact deflt
    · split
      · split
        · exact symExprScalarSort_pureU64_binOp st .bitAnd _ _ rfl hl rfl
        · exact deflt
      · exact deflt
    · exact deflt
  case bitAnd =>
    split
    · rfl
    · cases hl1
    · cases hr1
    · cases hl1
    · split
      · rfl
      · exact deflt
    · split
      · rfl
      · exact deflt
    · split
      · exact hl
      · exact deflt
  case bitOr =>
    split
    · rfl
    · cases hl1
    · cases hr1
    · cases hl1
    · exact hl
    · exact hr
    · split
      · exact hl
      · exact deflt
  case bitXor =>
    split
    · rfl
    · cases hl1
    · cases hr1
    · cases hl1
    · exact hl
    · exact hr
    · split
      · rfl
      · cases l with
        | constU256 _ => cases hl1
        | _ => exact deflt
  case shl =>
    split
    · rfl
    · cases hl1
    · cases hr1
    · exact hl
    · exact deflt
  case shr =>
    split
    · rfl
    · cases hl1
    · cases hr1
    · exact hl
    · exact deflt
  case sar => cases hop
  case clmul64 =>
    split
    · rfl
    · exact deflt
  case clmul64Hi =>
    split
    · rfl
    · exact deflt
  case gf2Affine =>
    split
    · rfl
    · exact deflt
  case eor3 =>
    split
    · rfl
    · exact deflt
  case eq => cases hop
  case lt => cases hop
  case le => cases hop
  case addChecked256 => cases hop
  case subChecked256 => cases hop
  case mulChecked256 => cases hop

theorem symBinOpIdentityShortCircuit_u64 (st : SymExecState) (ω : SymValuation)
    (op : BinOp) (l r idExpr : SymExpr) (nl nr : UInt64)
    (hlSort : symExprScalarSort? st l = some sortU64)
    (hrSort : symExprScalarSort? st r = some sortU64)
    (hlDen : denoteSymExpr ω l = .ok (.u64 nl))
    (hrDen : denoteSymExpr ω r = .ok (.u64 nr))
    (hid : symBinOpIdentityShortCircuit? op l r = some idExpr) :
    symExprScalarSort? st idExpr = some sortU64 ∧
      denoteSymExpr ω idExpr = evalBinOp op (.u64 nl) (.u64 nr) := by
  unfold symBinOpIdentityShortCircuit? at hid
  split at hid
  · cases hid
    injection hrDen with h1; injection h1 with h2; subst h2
    exact ⟨hlSort, by rw [hlDen]; exact (evalBinOp_add_zero (.u64 nl)).symm⟩
  · cases hid
    injection hlDen with h1; injection h1 with h2; subst h2
    exact ⟨hrSort, by rw [hrDen]; exact (evalBinOp_zero_add (.u64 nr)).symm⟩
  · cases hid
    injection hrDen with h1; injection h1 with h2; subst h2
    exact ⟨hlSort, by rw [hlDen]; exact (evalBinOp_sub_zero (.u64 nl)).symm⟩
  · cases hid
    injection hrDen with h1; injection h1 with h2; subst h2
    exact ⟨hlSort, by rw [hlDen]; exact (evalBinOp_mul_one (.u64 nl)).symm⟩
  · cases hid
    injection hlDen with h1; injection h1 with h2; subst h2
    exact ⟨hrSort, by rw [hrDen]; exact (evalBinOp_one_mul (.u64 nr)).symm⟩
  · cases hid
    injection hrDen with h1; injection h1 with h2; subst h2
    refine ⟨hlSort, ?_⟩
    rw [hlDen]
    change Except.ok (Val.u64 nl) = Except.ok (Val.u64 (nl / 1))
    cases nl with | ofBitVec bv => exact congrArg (Except.ok ∘ Val.u64 ∘ UInt64.ofBitVec) BitVec.udiv_one.symm
  · cases hid
    injection hrDen with h1; injection h1 with h2; subst h2
    exact ⟨hlSort, by rw [hlDen]; exact (evalBinOp_or_zero (.u64 nl)).symm⟩
  · cases hid
    injection hlDen with h1; injection h1 with h2; subst h2
    exact ⟨hrSort, by rw [hrDen]; exact (evalBinOp_zero_or (.u64 nr)).symm⟩
  · cases hid
    injection hrDen with h1; injection h1 with h2; subst h2
    exact ⟨hlSort, by rw [hlDen]; exact (evalBinOp_xor_zero (.u64 nl)).symm⟩
  · cases hid
    injection hlDen with h1; injection h1 with h2; subst h2
    exact ⟨hrSort, by rw [hrDen]; exact (evalBinOp_zero_xor (.u64 nr)).symm⟩
  · cases hid
    injection hrDen with h1; injection h1 with h2; subst h2
    refine ⟨hlSort, ?_⟩
    rw [hlDen]
    change Except.ok (Val.u64 nl) = Except.ok (Val.u64 (nl <<< 0))
    cases nl with | ofBitVec bv => exact congrArg (Except.ok ∘ Val.u64 ∘ UInt64.ofBitVec) (BitVec.shiftLeft_zero bv).symm
  · cases hid
    injection hrDen with h1; injection h1 with h2; subst h2
    refine ⟨hlSort, ?_⟩
    rw [hlDen]
    change Except.ok (Val.u64 nl) = Except.ok (Val.u64 (nl >>> 0))
    cases nl with | ofBitVec bv => exact congrArg (Except.ok ∘ Val.u64 ∘ UInt64.ofBitVec) (BitVec.ushiftRight_zero bv).symm
  -- 13: bitAnd l r (if l == r)
  · split at hid
    · rename_i hxy
      cases hid
      have hlr := SymExpr_eq_of_beq hxy; subst hlr
      have hn : nl = nr := by rw [hlDen] at hrDen; injection hrDen with h1; injection h1 with h2
      subst hn
      exact ⟨hlSort, by rw [hlDen]; exact (evalBinOp_and_self (.u64 nl)).symm⟩
    · cases hid
  -- 14: bitOr l r (if l == r)
  · split at hid
    · rename_i hxy
      cases hid
      have hlr := SymExpr_eq_of_beq hxy; subst hlr
      have hn : nl = nr := by rw [hlDen] at hrDen; injection hrDen with h1; injection h1 with h2
      subst hn
      exact ⟨hlSort, by rw [hlDen]; exact (evalBinOp_or_self (.u64 nl)).symm⟩
    · cases hid
  -- 15: default none
  · cases hid

theorem normSymBinOpStep_sortU64 (st : SymExecState) (op : BinOp) (l r : SymExpr) (w64Safe : Bool)
    (hop : (match op with
            | .add | .sub | .mul | .div | .mod | .bitAnd | .bitOr | .bitXor
            | .shl | .shr | .clmul64 | .clmul64Hi | .gf2Affine | .eor3 => true
            | .sar | .eq | .lt | .le | .addChecked256 | .subChecked256 | .mulChecked256 => false) = true)
    (hl : symExprScalarSort? st l = some sortU64)
    (hr : symExprScalarSort? st r = some sortU64) :
    symExprScalarSort? st (normSymBinOpStep op l r w64Safe) = some sortU64 := by
  unfold normSymBinOpStep
  cases (SymExpr.isCommutative op && decide (SymExpr.rank l > SymExpr.rank r))
  · exact normSymBinOpCore_sortU64 st op l r _ hop hl hr
  · exact normSymBinOpCore_sortU64 st op r l _ hop hr hl

/-- Symbolic evaluation of a pure 64-bit scalar agrees with the locked evaluator and preserves sort `sortU64`. -/
theorem symEvalScalarRes_pureU64_sound (st : SymExecState) (env : VarEnv) (e : ScalarExpr) :
    isPureU64ScalarExpr e = true → envBindsVarsU64 env e → stateAgreesU64 st env →
    ∃ n : UInt64, evalScalarExpr env e = .ok (.u64 n) ∧
      (symEvalScalarRes st e).unsupported = false ∧
      (symEvalScalarRes st e).ubCond = .constBool true ∧
      symExprScalarSort? st (symEvalScalarRes st e).val.expr = some sortU64 ∧
      denoteSymExpr (SymValuation.ofVarEnv env) (symEvalScalarRes st e).val.expr = .ok (.u64 n) := by
  intro hpure hbind hagree
  induction e with
  | constU64 v =>
    exact ⟨v, rfl, rfl, rfl, rfl, rfl⟩
  | constBool _ => simp [isPureU64ScalarExpr] at hpure
  | select _ _ _ _ _ _ => simp [isPureU64ScalarExpr] at hpure
  | fma _ _ _ _ _ _ => simp [isPureU64ScalarExpr] at hpure
  | var id =>
    obtain ⟨n, henv⟩ := hbind
    obtain ⟨n', hv, hnoub, hden, hsort⟩ := hagree id (.u64 n) henv
    injection hv with hnn; subst hnn
    refine ⟨n, ?_, rfl, ?_, hsort, hden⟩
    · simp [evalScalarExpr, henv]
    · simp [symEvalScalarRes, hnoub]
  | unaryOp op a iha =>
    have hfalse : (SymExpr.constBool true == SymExpr.constBool false) = false := rfl
    cases op with
    | clz256 => simp [isPureU64ScalarExpr] at hpure
    | not =>
      simp only [isPureU64ScalarExpr] at hpure
      obtain ⟨na, heval, hunsup, hub, hsort, hden⟩ := iha hpure hbind
      refine ⟨~~~na, ?_, ?_⟩
      · simp [evalScalarExpr, heval, evalUnaryOp]
      · rw [symEvalScalarRes.eq_def]
        dsimp only []
        rw [hunsup, hub, hsort, hfalse]
        exact ⟨rfl, rfl,
          normSymUnaryOpStep_sortU64 st .not _ (Or.inl rfl) hsort,
          by
            change denoteSymExpr (SymValuation.ofVarEnv env) (normSymUnaryOpStep .not (symEvalScalarRes st a).val.expr) = _
            rw [normSymUnaryOpStep_denotes_eq]; simp only [denoteSymExpr, hden]; rfl⟩
    | neg =>
      simp only [isPureU64ScalarExpr] at hpure
      obtain ⟨na, heval, hunsup, hub, hsort, hden⟩ := iha hpure hbind
      refine ⟨0 - na, ?_, ?_⟩
      · simp [evalScalarExpr, heval, evalUnaryOp]
      · rw [symEvalScalarRes.eq_def]
        dsimp only []
        rw [hunsup, hub, hsort, hfalse]
        exact ⟨rfl, rfl,
          normSymUnaryOpStep_sortU64 st .neg _ (Or.inr rfl) hsort,
          by
            change denoteSymExpr (SymValuation.ofVarEnv env) (normSymUnaryOpStep .neg (symEvalScalarRes st a).val.expr) = _
            rw [normSymUnaryOpStep_denotes_eq]; simp only [denoteSymExpr, hden]; rfl⟩
  | binOp op l r ihl ihr =>
    simp only [isPureU64ScalarExpr, Bool.and_eq_true] at hpure
    rcases hpure with ⟨⟨hop, hlPure⟩, hrPure⟩
    rcases hbind with ⟨hlBind, hrBind⟩
    obtain ⟨nl, hlEval, hlUnsup, hlUb, hlSort, hlDen⟩ := ihl hlPure hlBind
    obtain ⟨nr, hrEval, hrUnsup, hrUb, hrSort, hrDen⟩ := ihr hrPure hrBind
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
          symBinOpIdentityShortCircuit_u64 st (SymValuation.ofVarEnv env)
            op _ _ idExpr nl nr hlSort hrSort hlDen hrDen hid
        exact ⟨rfl, rfl, hIdSort, hIdDen.trans hn⟩
      | none =>
        rw [hlSort, hrSort]
        have hstepSort := normSymBinOpStep_sortU64 st op _ _ true hop hlSort hrSort
        have hstepDen := (normSymBinOpStep_u64_denotes (SymValuation.ofVarEnv env) op _ _ true nl nr hlDen hrDen).trans hn
        cases op <;> simp at hop <;> exact ⟨rfl, rfl, hstepSort, hstepDen⟩

/-- Recursive bottom-up `normSymExpr` preserves exact 64-bit concrete denotation across
    `isPureU64SymExprIn vars` whenever every variable in `vars` is bound to `.u64` in `ω`. -/
theorem normSymExpr_pureU64_denotes (vars : List VarId) (ω : SymValuation) :
    ∀ (s : SymExpr),
      isPureU64SymExprIn vars s = true →
      (∀ id : VarId, vars.contains id = true → ∃ n : UInt64, ω.varVal id = some (Val.u64 n)) →
      ∃ n : UInt64, denoteSymExpr ω s = .ok (Val.u64 n) ∧
        denoteSymExpr ω (normSymExpr s) = .ok (Val.u64 n)
  | .constU64 v, _, _ => ⟨v, rfl, rfl⟩
  | .symVar id, hp, hvars =>
    let ⟨n, hn⟩ := hvars id hp
    ⟨n, by simp [denoteSymExpr, hn], by simp [normSymExpr, denoteSymExpr, hn]⟩
  | .unaryOp op a, hp, hvars => by
    cases op with
    | clz256 => simp [isPureU64SymExprIn] at hp
    | not =>
      simp only [isPureU64SymExprIn] at hp
      obtain ⟨na, hda, hdna⟩ := normSymExpr_pureU64_denotes vars ω a hp hvars
      refine ⟨~~~na, ?_, ?_⟩
      · simp [denoteSymExpr, hda, evalUnaryOp]
      · rw [normSymExpr.eq_def]
        dsimp only []
        rw [normSymUnaryOpStep_denotes_eq]
        simp [denoteSymExpr, hdna, evalUnaryOp]
    | neg =>
      simp only [isPureU64SymExprIn] at hp
      obtain ⟨na, hda, hdna⟩ := normSymExpr_pureU64_denotes vars ω a hp hvars
      refine ⟨0 - na, ?_, ?_⟩
      · simp [denoteSymExpr, hda, evalUnaryOp]
      · rw [normSymExpr.eq_def]
        dsimp only []
        rw [normSymUnaryOpStep_denotes_eq]
        simp [denoteSymExpr, hdna, evalUnaryOp]
  | .binOp op l r, hp, hvars => by
    simp only [isPureU64SymExprIn, Bool.and_eq_true] at hp
    rcases hp with ⟨⟨hop, hl⟩, hr⟩
    obtain ⟨nl, hdl, hdnl⟩ := normSymExpr_pureU64_denotes vars ω l hl hvars
    obtain ⟨nr, hdr, hdnr⟩ := normSymExpr_pureU64_denotes vars ω r hr hvars
    have hev : ∃ n : UInt64, evalBinOp op (Val.u64 nl) (Val.u64 nr) = .ok (Val.u64 n) := by
      cases op <;> simp at hop <;> exact ⟨_, rfl⟩
    obtain ⟨n, hn⟩ := hev
    refine ⟨n, ?_, ?_⟩
    · simp [denoteSymExpr, hdl, hdr, hn]
    · rw [normSymExpr.eq_def]
      dsimp only []
      rw [normSymBinOpStep_u64_denotes ω op (normSymExpr l) (normSymExpr r) false nl nr hdnl hdnr]
      exact hn
  | .constU256 _, hp, _ | .constBool _, hp, _ | .allocTag _, hp, _ | .rcSym _ _, hp, _
  | .ctorTag _ _, hp, _ | .ctorLen _ _ _, hp, _ | .sarrayLen _, hp, _
  | .mulDiv256 _ _ _ _, hp, _ | .ite _ _ _, hp, _ | .tuple _, hp, _
  | .bufElem _ _ _, hp, _ | .unit, hp, _ => by
    simp [isPureU64SymExprIn] at hp
termination_by s => sizeOf s

/-- Passing translation validation implies the recorded concrete and symbolic invariants hold. -/
theorem validateTranslationDeclSound_of_passed (src tgt : LNIRDecl) (numSamples : Nat) :
    validateTranslationDeclSound src tgt numSamples := by
  intro h
  have h1 : (validateTranslationDecl src tgt numSamples).passed = true := h
  dsimp only [validateTranslationDecl] at h1
  simp only [Bool.and_eq_true] at h1
  rcases h1 with ⟨⟨⟨⟨⟨⟨hSymOk, hUbRef⟩, hDom⟩, hPoison⟩, _⟩, hConc⟩, _⟩
  rcases hSymOk with ⟨⟨⟨_, hExSrc⟩, hExTgt⟩, hSupp⟩
  rcases hUbRef with ⟨⟨_, hNoUb⟩, _⟩
  rcases hDom with ⟨hReach, _⟩
  have hExSrc' : (symExecDecl 4 src (some (Nat.max (declSynVarBase src) (declSynVarBase tgt)))).symExhausted = false := by
    simpa using hExSrc
  have hExTgt' : (symExecDecl 4 tgt (some (Nat.max (declSynVarBase src) (declSynVarBase tgt)))).symExhausted = false := by
    simpa using hExTgt
  refine ⟨hExSrc', hExTgt', ?_, hNoUb, hPoison, eq_of_beq hReach, ?_⟩
  · generalize hb : (src.params == tgt.params && src.retTy == tgt.retTy && src.body == tgt.body) = b at hSupp ⊢
    cases b
    · simp only [Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at hSupp
      rcases hSupp with ⟨hu1, hu2⟩
      simp [hu1, hu2]
    · rfl
  · exact hConc

/-- Concrete sample checking is reflexive: every declaration step refines itself. -/
theorem checkSingleSample_refl (fuel : Nat) (env : VarEnv) (st : HeapState) (c : LNIRCode) :
    checkSingleSample fuel env st c c = true := by
  unfold checkSingleSample
  cases evalCode fuel env st c with
  | error _ => rfl
  | ok pair =>
    obtain ⟨v, st'⟩ := pair
    simp [Val.beq_self]

/-- Whenever `checkSingleSample` passes and the source evaluation succeeds without UB,
    the target evaluation succeeds with the exact same return value and heap state. -/
theorem checkSingleSample_sound (fuel : Nat) (env : VarEnv) (st stSrc : HeapState)
    (src tgt : LNIRCode) (vSrc : Val) :
    checkSingleSample fuel env st src tgt = true →
    evalCode fuel env st src = .ok (vSrc, stSrc) →
    ∃ vTgt : Val, evalCode fuel env st tgt = .ok (vTgt, stSrc) ∧ (vSrc == vTgt) = true := by
  intro hchk heval
  unfold checkSingleSample at hchk
  rw [heval] at hchk
  cases hTgt : evalCode fuel env st tgt with
  | error err =>
    rw [hTgt] at hchk
    cases hchk
  | ok pair =>
    obtain ⟨vTgt, stTgt⟩ := pair
    rw [hTgt] at hchk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    rcases hchk with ⟨hv, hst⟩
    subst hst
    exact ⟨vTgt, rfl, hv⟩

end LeanNative.Proofs
