import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.Proofs.PeepholeProofs
import LeanNative.Proofs.SymbolicTV
import LeanNative.Proofs.SymbolicTVDenote

namespace LeanNative.Proofs
set_option maxHeartbeats 40000

open LeanNative.IR
open LeanNative.Semantics

/-!
# Kernel-Checked Soundness of `SymbolicTV` (`LeanNative.Proofs.SymbolicTVSoundness`)

Every theorem below is stated against the concrete denotation `denoteSymExpr` and the locked
operational evaluator `evalScalarExpr`, so a passing `validateTranslationDecl` is no longer an
uninterpreted `TranslationValidated` claim.
-/

mutual
  theorem SymExpr_beq_refl : ∀ (e : SymExpr), SymExpr.beq e e = true
    | .constU64 a => by simp [SymExpr.beq]
    | .constU256 a => by simp [SymExpr.beq]
    | .constBool a => by simp [SymExpr.beq]
    | .symVar a => by simp [SymExpr.beq]
    | .allocTag a => by simp [SymExpr.beq]
    | .rcSym ea a => by simp [SymExpr.beq]
    | .ctorTag ea a => by simp [SymExpr.beq]
    | .ctorLen sa ea a => by simp [SymExpr.beq]
    | .sarrayLen a => by simp [SymExpr.beq]
    | .mulDiv256 u a b d => by simp [SymExpr.beq, SymExpr_beq_refl a, SymExpr_beq_refl b, SymExpr_beq_refl d]
    | .binOp op l r => by
      have hop : (op == op) = true := by cases op <;> rfl
      simp [SymExpr.beq, hop, SymExpr_beq_refl l, SymExpr_beq_refl r]
    | .unaryOp op a => by
      have hop : (op == op) = true := by cases op <;> rfl
      simp [SymExpr.beq, hop, SymExpr_beq_refl a]
    | .ite c t e => by simp [SymExpr.beq, SymExpr_beq_refl c, SymExpr_beq_refl t, SymExpr_beq_refl e]
    | .tuple fs => by simp [SymExpr.beq, SymExpr_beqList_refl fs]
    | .bufElem sp b i => by simp [SymExpr.beq, SymExpr_beq_refl i]
    | .unit => rfl

  theorem SymExpr_beqList_refl : ∀ (es : List SymExpr), SymExpr.beqList es es = true
    | [] => rfl
    | e :: es => by simp [SymExpr.beqList, SymExpr_beq_refl e, SymExpr_beqList_refl es]
end

@[simp]
theorem SymExpr_beq_self (e : SymExpr) : (e == e) = true :=
  SymExpr_beq_refl e

mutual
  theorem SymExpr_eq_of_beq : ∀ {a b : SymExpr}, SymExpr.beq a b = true → a = b
    | .constU64 a, .constU64 b, h => by simp [SymExpr.beq] at h; subst h; rfl
    | .constU256 a, .constU256 b, h => by simp [SymExpr.beq] at h; subst h; rfl
    | .constBool a, .constBool b, h => by simp [SymExpr.beq] at h; subst h; rfl
    | .symVar a, .symVar b, h => by simp [SymExpr.beq] at h; subst h; rfl
    | .allocTag a, .allocTag b, h => by simp [SymExpr.beq] at h; subst h; rfl
    | .rcSym ea a, .rcSym eb b, h => by simp [SymExpr.beq] at h; rcases h with ⟨rfl, rfl⟩; rfl
    | .ctorTag ea a, .ctorTag eb b, h => by simp [SymExpr.beq] at h; rcases h with ⟨rfl, rfl⟩; rfl
    | .ctorLen sa ea a, .ctorLen sb eb b, h => by
      simp [SymExpr.beq] at h; rcases h with ⟨⟨rfl, rfl⟩, rfl⟩; rfl
    | .sarrayLen a, .sarrayLen b, h => by simp [SymExpr.beq] at h; subst h; rfl
    | .mulDiv256 u1 a1 b1 d1, .mulDiv256 u2 a2 b2 d2, h => by
      simp [SymExpr.beq] at h
      rcases h with ⟨⟨⟨rfl, ha⟩, hb⟩, hd⟩
      rw [SymExpr_eq_of_beq ha, SymExpr_eq_of_beq hb, SymExpr_eq_of_beq hd]
    | .binOp o1 l1 r1, .binOp o2 l2 r2, h => by
      simp [SymExpr.beq] at h
      rcases h with ⟨⟨ho, hl⟩, hr⟩
      have ho' : o1 = o2 := by cases o1 <;> cases o2 <;> first | rfl | cases ho
      rw [ho', SymExpr_eq_of_beq hl, SymExpr_eq_of_beq hr]
    | .unaryOp o1 a1, .unaryOp o2 a2, h => by
      simp [SymExpr.beq] at h
      rcases h with ⟨ho, ha⟩
      have ho' : o1 = o2 := by cases o1 <;> cases o2 <;> first | rfl | cases ho
      rw [ho', SymExpr_eq_of_beq ha]
    | .ite c1 t1 e1, .ite c2 t2 e2, h => by
      simp [SymExpr.beq] at h
      rcases h with ⟨⟨hc, ht⟩, he⟩
      rw [SymExpr_eq_of_beq hc, SymExpr_eq_of_beq ht, SymExpr_eq_of_beq he]
    | .tuple fs1, .tuple fs2, h => by
      simp [SymExpr.beq] at h
      rw [SymExpr_list_eq_of_beq h]
    | .bufElem s1 b1 i1, .bufElem s2 b2 i2, h => by
      simp [SymExpr.beq] at h
      rcases h with ⟨⟨rfl, rfl⟩, hi⟩
      rw [SymExpr_eq_of_beq hi]
    | .unit, .unit, _ => rfl

  theorem SymExpr_list_eq_of_beq : ∀ {as bs : List SymExpr}, SymExpr.beqList as bs = true → as = bs
    | [], [], _ => rfl
    | a :: as, b :: bs, h => by
      simp [SymExpr.beqList] at h
      rcases h with ⟨ha, hbs⟩
      rw [SymExpr_eq_of_beq ha, SymExpr_list_eq_of_beq hbs]
end

theorem SymExpr_beq_eq_true (a b : SymExpr) : (a == b) = true ↔ a = b :=
  ⟨SymExpr_eq_of_beq, fun h => h ▸ SymExpr_beq_self a⟩

/-- `exprDefinitely64` is exactly the fragment that denotes a `.u64` under every valuation. -/
theorem exprDefinitely64_denotesU64 (e : SymExpr) :
    exprDefinitely64 e = true → denotesU64 e := by
  intro h ω v hv
  cases e <;> simp [exprDefinitely64] at h <;> simp only [denoteSymExpr] at hv
  · cases hv; exact ⟨_, rfl⟩
  · revert hv
    cases ω.rcVal _ _ <;> intro hv <;> cases hv
    exact ⟨_, rfl⟩
  · revert hv
    cases ω.ctorTagVal _ _ <;> intro hv <;> cases hv
    exact ⟨_, rfl⟩
  · revert hv
    cases ω.ctorLenVal _ _ _ <;> intro hv <;> cases hv
    exact ⟨_, rfl⟩
  · revert hv
    cases ω.sarrayLenVal _ <;> intro hv <;> cases hv
    exact ⟨_, rfl⟩

/-- A boolean literal is its own boolean denotation. -/
theorem denote_constBool (ω : SymValuation) (b : Bool) :
    denoteSymExpr ω (.constBool b) = .ok (.bool b) := rfl

/-- A 64-bit literal is its own `.u64` denotation. -/
theorem denote_constU64 (ω : SymValuation) (n : UInt64) :
    denoteSymExpr ω (.constU64 n) = .ok (.u64 n) := rfl

/-- A 256-bit literal is its own `.u256` denotation. -/
theorem denote_constU256 (ω : SymValuation) (w : UInt256) :
    denoteSymExpr ω (.constU256 w) = .ok (.u256 w) := rfl

/-- Constant folding of `.not` on a boolean literal is exact. -/
theorem normSymUnaryOpStep_not_constBool (b : Bool) :
    normSymUnaryOpStep .not (.constBool b) = .constBool (!b) := rfl

/-- Constant folding of `.not` on a 64-bit literal is exact. -/
theorem normSymUnaryOpStep_not_constU64 (n : UInt64) :
    normSymUnaryOpStep .not (.constU64 n) = .constU64 (~~~n) := rfl

/-- Constant folding of `.not` on a 256-bit literal is exact. -/
theorem normSymUnaryOpStep_not_constU256 (w : UInt256) :
    normSymUnaryOpStep .not (.constU256 w) = .constU256 (UInt256.bitNot w) := rfl

/-- Constant folding of `.neg` on a 64-bit literal is exact. -/
theorem normSymUnaryOpStep_neg_constU64 (n : UInt64) :
    normSymUnaryOpStep .neg (.constU64 n) = .constU64 (0 - n) := rfl

/-- Constant folding of `.neg` on a 256-bit literal is exact. -/
theorem normSymUnaryOpStep_neg_constU256 (w : UInt256) :
    normSymUnaryOpStep .neg (.constU256 w) = .constU256 (UInt256.sub UInt256.zero w) := rfl

/-- Constant folding of `.clz256` on a 256-bit literal is exact. -/
theorem normSymUnaryOpStep_clz256_constU256 (w : UInt256) :
    normSymUnaryOpStep .clz256 (.constU256 w) = .constU256 (UInt256.clz w) := rfl

/-- Constant folding of `.clz256` on a 64-bit literal is exact. -/
theorem normSymUnaryOpStep_clz256_constU64 (n : UInt64) :
    normSymUnaryOpStep .clz256 (.constU64 n) = .constU256 (UInt256.clz (UInt256.ofUInt64 n)) := rfl

/-- Double bitwise negation cancels when `x` is definitely 64-bit or boolean. -/
theorem normSymUnaryOpStep_not_not (x : SymExpr) :
    (exprDefinitely64 x || atomDefinitelyBool x) = true →
    normSymUnaryOpStep .not (.unaryOp .not x) = x := by
  intro h
  simp only [normSymUnaryOpStep]
  rw [Bool.or_eq_true] at h
  cases h with
  | inl h64 => simp [h64]
  | inr hb => simp [hb]

/-- Double negation cancels when `x` is definitely 64-bit. -/
theorem normSymUnaryOpStep_neg_neg (x : SymExpr) :
    exprDefinitely64 x = true →
    normSymUnaryOpStep .neg (.unaryOp .neg x) = x := by
  intro h
  simp [normSymUnaryOpStep, h]

/-- Helper: comparison ops (`eq`, `lt`, `le`) always return `.bool` whenever defined. -/
theorem evalBinOp_cmp_isBool {op : BinOp} (hop : op = .eq ∨ op = .lt ∨ op = .le)
    {vl vr v : Val} (hv : evalBinOp op vl vr = .ok v) : ∃ b, v = .bool b := by
  rcases hop with rfl | rfl | rfl
  · cases vl <;> cases vr
    all_goals try (cases hv; done)
    all_goals (dsimp only [evalBinOp] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)
  · cases vl <;> cases vr
    all_goals try (cases hv; done)
    all_goals (dsimp only [evalBinOp] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)
  · cases vl <;> cases vr
    all_goals try (cases hv; done)
    all_goals (dsimp only [evalBinOp] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)

/-- `atomDefinitelyBool` guarantees that every defined concrete denotation is `.bool`. -/
theorem atomDefinitelyBool_denotesBool (e : SymExpr) (h : atomDefinitelyBool e = true) :
    denotesBool e := by
  match e with
  | .constBool b =>
    intro _ _ hv
    cases hv
    exact ⟨b, rfl⟩
  | .binOp op l r =>
    have hop : op = .eq ∨ op = .lt ∨ op = .le := by
      cases op <;> simp [atomDefinitelyBool] at h
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    intro ω v hv
    simp only [denoteSymExpr] at hv
    cases hl : denoteSymExpr ω l with
    | error _ => rw [hl] at hv; cases hv
    | ok vl =>
      rw [hl] at hv
      cases hr : denoteSymExpr ω r with
      | error _ => rw [hr] at hv; cases hv
      | ok vr =>
        rw [hr] at hv
        exact evalBinOp_cmp_isBool hop hv
  | .ite c t f =>
    cases f with
    | constBool bf =>
      cases bf with
      | false =>
        simp only [atomDefinitelyBool, Bool.and_eq_true] at h
        rcases h with ⟨hc, ht⟩
        have ihc := atomDefinitelyBool_denotesBool c hc
        have iht := atomDefinitelyBool_denotesBool t ht
        intro ω v hv
        simp only [denoteSymExpr] at hv
        cases hdc : denoteSymExpr ω c with
        | error _ => simp [hdc] at hv
        | ok vc =>
          simp only [hdc] at hv
          obtain ⟨bc, rfl⟩ := ihc ω vc hdc
          cases bc
          · cases hv; exact ⟨false, rfl⟩
          · exact iht ω v hv
      | true => cases (by simp [atomDefinitelyBool] at h : False)
    | constU64 _ | constU256 _ | symVar _ | allocTag _ | rcSym _ _ | ctorTag _ _
    | ctorLen _ _ _ | sarrayLen _ | mulDiv256 _ _ _ _ | binOp _ _ _ | unaryOp _ _
    | ite _ _ _ | tuple _ | bufElem _ _ _ | unit =>
      cases (by simp [atomDefinitelyBool] at h : False)
  | .constU64 _ | .constU256 _ | .symVar _ | .allocTag _ | .rcSym _ _ | .ctorTag _ _
  | .ctorLen _ _ _ | .sarrayLen _ | .mulDiv256 _ _ _ _ | .unaryOp _ _ | .tuple _
  | .bufElem _ _ _ | .unit =>
    cases (by simp [atomDefinitelyBool] at h : False)
termination_by sizeOf e

/-- Single-step unary normalization preserves concrete denotation on all expressions. -/
theorem normSymUnaryOpStep_denotes_eq (ω : SymValuation) (op : UnaryOp) (a : SymExpr) :
    denoteSymExpr ω (normSymUnaryOpStep op a) = denoteSymExpr ω (.unaryOp op a) := by
  cases op with
  | not =>
    cases a with
    | constBool b => rfl
    | constU64 n => rfl
    | constU256 w => rfl
    | unaryOp op2 x =>
      cases op2 <;> try rfl
      change denoteSymExpr ω
        (if (exprDefinitely64 x || atomDefinitelyBool x ||
            match x with | .constU256 _ => true | _ => false) = true
         then x else .unaryOp .not (.unaryOp .not x)) = _
      cases hcond : (exprDefinitely64 x || atomDefinitelyBool x ||
          match x with | .constU256 _ => true | _ => false)
      · simp
      · simp only [↓reduceIte]
        rcases Bool.or_eq_true _ _ |>.mp hcond with h1 | h256
        · rcases Bool.or_eq_true _ _ |>.mp h1 with h64 | hb
          · simp only [denoteSymExpr]
            cases hx : denoteSymExpr ω x with
            | error _ => rfl
            | ok vx =>
              obtain ⟨n, rfl⟩ := exprDefinitely64_denotesU64 x h64 ω vx hx
              simp only [evalUnaryOp]
              have hnn : ~~~(~~~n) = n := by
                cases n; exact congrArg UInt64.ofBitVec BitVec.not_not
              rw [hnn]
          · simp only [denoteSymExpr]
            cases hx : denoteSymExpr ω x with
            | error _ => rfl
            | ok vx =>
              obtain ⟨b, rfl⟩ := atomDefinitelyBool_denotesBool x hb ω vx hx
              simp [evalUnaryOp]
        · cases x <;> simp at h256
          rename_i w
          simp only [denoteSymExpr, evalUnaryOp]
          cases w
          have h64 : ∀ u : UInt64, ~~~(~~~u) = u := fun u => by
            cases u; exact congrArg UInt64.ofBitVec BitVec.not_not
          simp [UInt256.bitNot, h64]
    | _ => rfl
  | neg =>
    cases a with
    | constU64 n => rfl
    | constU256 w => rfl
    | unaryOp op2 x =>
      cases op2 <;> try rfl
      change denoteSymExpr ω
        (if exprDefinitely64 x = true then x else .unaryOp .neg (.unaryOp .neg x)) = _
      cases h64 : exprDefinitely64 x
      · simp
      · simp only [↓reduceIte, denoteSymExpr]
        cases hx : denoteSymExpr ω x with
        | error _ => rfl
        | ok vx =>
          obtain ⟨n, rfl⟩ := exprDefinitely64_denotesU64 x h64 ω vx hx
          simp only [evalUnaryOp]
          have hnn : (0 : UInt64) - ((0 : UInt64) - n) = n := by
            cases n; exact congrArg UInt64.ofBitVec (by change 0#64 - (0#64 - _) = _; simp)
          rw [hnn]
    | _ => rfl
  | clz256 =>
    cases a <;> rfl

/-- Single-step unary normalization refines concrete denotation on all expressions. -/
theorem normSymUnaryOpStep_refines (op : UnaryOp) (a : SymExpr) :
    SymExprDenoteRefines (.unaryOp op a) (normSymUnaryOpStep op a) := by
  intro ω v hv
  rw [normSymUnaryOpStep_denotes_eq]
  exact hv

/-- Constant folding of 64-bit addition is exact. -/
theorem normSymBinOpStep_add_const (a b : UInt64) :
    normSymBinOpStep .add (.constU64 a) (.constU64 b) = .constU64 (a + b) := by
  unfold normSymBinOpStep
  cases (SymExpr.isCommutative .add && decide (SymExpr.rank (.constU64 a) > SymExpr.rank (.constU64 b)))
  · rfl
  · change SymExpr.constU64 (b + a) = SymExpr.constU64 (a + b); rw [UInt64.add_comm]

/-- Constant folding of 64-bit multiplication is exact. -/
theorem normSymBinOpStep_mul_const (a b : UInt64) :
    normSymBinOpStep .mul (.constU64 a) (.constU64 b) = .constU64 (a * b) := by
  unfold normSymBinOpStep
  cases (SymExpr.isCommutative .mul && decide (SymExpr.rank (.constU64 a) > SymExpr.rank (.constU64 b)))
  · rfl
  · change SymExpr.constU64 (b * a) = SymExpr.constU64 (a * b); rw [UInt64.mul_comm]

/-- Constant folding of 64-bit bitwise and is exact. -/
theorem normSymBinOpStep_and_const (a b : UInt64) :
    normSymBinOpStep .bitAnd (.constU64 a) (.constU64 b) = .constU64 (a &&& b) := by
  unfold normSymBinOpStep
  cases (SymExpr.isCommutative .bitAnd && decide (SymExpr.rank (.constU64 a) > SymExpr.rank (.constU64 b)))
  · rfl
  · change SymExpr.constU64 (b &&& a) = SymExpr.constU64 (a &&& b); rw [UInt64.and_comm]

/-- Constant folding of 64-bit bitwise or is exact. -/
theorem normSymBinOpStep_or_const (a b : UInt64) :
    normSymBinOpStep .bitOr (.constU64 a) (.constU64 b) = .constU64 (a ||| b) := by
  unfold normSymBinOpStep
  cases (SymExpr.isCommutative .bitOr && decide (SymExpr.rank (.constU64 a) > SymExpr.rank (.constU64 b)))
  · rfl
  · change SymExpr.constU64 (b ||| a) = SymExpr.constU64 (a ||| b); rw [UInt64.or_comm]

/-- Constant folding of 64-bit bitwise xor is exact. -/
theorem normSymBinOpStep_xor_const (a b : UInt64) :
    normSymBinOpStep .bitXor (.constU64 a) (.constU64 b) = .constU64 (a ^^^ b) := by
  unfold normSymBinOpStep
  cases (SymExpr.isCommutative .bitXor && decide (SymExpr.rank (.constU64 a) > SymExpr.rank (.constU64 b)))
  · rfl
  · change SymExpr.constU64 (b ^^^ a) = SymExpr.constU64 (a ^^^ b); rw [UInt64.xor_comm]

/-- Constant folding of 64-bit subtraction is exact. -/
theorem normSymBinOpStep_sub_const (a b : UInt64) :
    normSymBinOpStep .sub (.constU64 a) (.constU64 b) = .constU64 (a - b) := rfl

/-- Constant folding of 64-bit division is exact. -/
theorem normSymBinOpStep_div_const (a b : UInt64) :
    normSymBinOpStep .div (.constU64 a) (.constU64 b) = .constU64 (a / b) := rfl

/-- Constant folding of 64-bit remainder is exact. -/
theorem normSymBinOpStep_mod_const (a b : UInt64) :
    normSymBinOpStep .mod (.constU64 a) (.constU64 b) = .constU64 (a % b) := rfl

/-- Constant folding of a masked 64-bit left shift is exact. -/
theorem normSymBinOpStep_shl_const (a b : UInt64) :
    normSymBinOpStep .shl (.constU64 a) (.constU64 b) = .constU64 (a <<< (b &&& 63)) := rfl

/-- Constant folding of a masked 64-bit logical right shift is exact. -/
theorem normSymBinOpStep_shr_const (a b : UInt64) :
    normSymBinOpStep .shr (.constU64 a) (.constU64 b) = .constU64 (a >>> (b &&& 63)) := rfl

/-- Constant folding of carryless multiplication (low half) is exact. -/
theorem normSymBinOpStep_clmul64_const (a b : UInt64) :
    normSymBinOpStep .clmul64 (.constU64 a) (.constU64 b) = .constU64 (clmul64 a b) := rfl

/-- Constant folding of carryless multiplication (high half) is exact. -/
theorem normSymBinOpStep_clmul64Hi_const (a b : UInt64) :
    normSymBinOpStep .clmul64Hi (.constU64 a) (.constU64 b) = .constU64 (clmul64Hi a b) := rfl

/-- Constant folding of the GF(2^8) affine map is exact. -/
theorem normSymBinOpStep_gf2Affine_const (a b : UInt64) :
    normSymBinOpStep .gf2Affine (.constU64 a) (.constU64 b) = .constU64 (gf2Affine a b) := rfl

/-- Constant folding of three-input xor is exact. -/
theorem normSymBinOpStep_eor3_const (a b : UInt64) :
    normSymBinOpStep .eor3 (.constU64 a) (.constU64 b) = .constU64 (eor3 a b) := rfl

/-- Constant folding of 64-bit equality is exact. -/
theorem normSymBinOpStep_eq_const (a b : UInt64) :
    normSymBinOpStep .eq (.constU64 a) (.constU64 b) = .constBool (a == b) := by
  unfold normSymBinOpStep
  cases (SymExpr.isCommutative .eq && decide (SymExpr.rank (.constU64 a) > SymExpr.rank (.constU64 b)))
  · rfl
  · change SymExpr.constBool (b == a) = SymExpr.constBool (a == b); rw [BEq.comm]

/-- Constant folding of 64-bit strict order is exact. -/
theorem normSymBinOpStep_lt_const (a b : UInt64) :
    normSymBinOpStep .lt (.constU64 a) (.constU64 b) = .constBool (decide (a < b)) := rfl

/-- Constant folding of 64-bit non-strict order is exact. -/
theorem normSymBinOpStep_le_const (a b : UInt64) :
    normSymBinOpStep .le (.constU64 a) (.constU64 b) = .constBool (decide (a ≤ b)) := rfl

/-- Power-of-two multiplication/division/modulo strength reduction on `UInt64` whenever `pow2ShiftLog2 c = some k`. -/
theorem pow2ShiftLog2_mul_right {c k : UInt64} (hk : pow2ShiftLog2 c = some k) (a : UInt64) :
    a * c = a <<< k := by
  unfold pow2ShiftLog2 at hk
  split at hk
  · cases hk; exact uint64_mul_two a
  · cases hk; exact uint64_mul_four a
  · cases hk; exact uint64_mul_eight a
  · cases hk; exact uint64_mul_sixteen a
  · cases hk; exact uint64_mul_thirtytwo a
  · cases hk

theorem pow2ShiftLog2_mul_left {c k : UInt64} (hk : pow2ShiftLog2 c = some k) (a : UInt64) :
    c * a = a <<< k := by
  rw [UInt64.mul_comm, pow2ShiftLog2_mul_right hk]

theorem pow2ShiftLog2_div {c k : UInt64} (hk : pow2ShiftLog2 c = some k) (a : UInt64) :
    a / c = a >>> k := by
  unfold pow2ShiftLog2 at hk
  split at hk
  · cases hk; exact uint64_div_two a
  · cases hk; exact uint64_div_four a
  · cases hk; exact uint64_div_eight a
  · cases hk
    cases a with | ofBitVec bv =>
      rcases bv with ⟨n, _⟩
      exact congrArg UInt64.ofBitVec (BitVec.eq_of_toNat_eq (by change n / 16 = n >>> 4; rw [Nat.shiftRight_eq_div_pow]))
  · cases hk
    cases a with | ofBitVec bv =>
      rcases bv with ⟨n, _⟩
      exact congrArg UInt64.ofBitVec (BitVec.eq_of_toNat_eq (by change n / 32 = n >>> 5; rw [Nat.shiftRight_eq_div_pow]))
  · cases hk

theorem pow2ShiftLog2_mod {c k : UInt64} (hk : pow2ShiftLog2 c = some k) (a : UInt64) :
    a % c = a &&& (c - 1) := by
  unfold pow2ShiftLog2 at hk
  split at hk
  · cases hk
    cases a with | ofBitVec bv =>
      rcases bv with ⟨n, _⟩
      exact congrArg UInt64.ofBitVec (BitVec.eq_of_toNat_eq (by
        change n % 2 = n &&& 1
        exact (Nat.and_two_pow_sub_one_eq_mod n 1).symm))
  · cases hk
    cases a with | ofBitVec bv =>
      rcases bv with ⟨n, _⟩
      exact congrArg UInt64.ofBitVec (BitVec.eq_of_toNat_eq (by
        change n % 4 = n &&& 3
        exact (Nat.and_two_pow_sub_one_eq_mod n 2).symm))
  · cases hk
    cases a with | ofBitVec bv =>
      rcases bv with ⟨n, _⟩
      exact congrArg UInt64.ofBitVec (BitVec.eq_of_toNat_eq (by
        change n % 8 = n &&& 7
        exact (Nat.and_two_pow_sub_one_eq_mod n 3).symm))
  · cases hk
    cases a with | ofBitVec bv =>
      rcases bv with ⟨n, _⟩
      exact congrArg UInt64.ofBitVec (BitVec.eq_of_toNat_eq (by
        change n % 16 = n &&& 15
        exact (Nat.and_two_pow_sub_one_eq_mod n 4).symm))
  · cases hk
    cases a with | ofBitVec bv =>
      rcases bv with ⟨n, _⟩
      exact congrArg UInt64.ofBitVec (BitVec.eq_of_toNat_eq (by
        change n % 32 = n &&& 31
        exact (Nat.and_two_pow_sub_one_eq_mod n 5).symm))
  · cases hk

/-- Commutativity of `evalBinOp` on 64-bit operands when `SymExpr.isCommutative op = true`. -/
theorem evalBinOp_u64_comm {op : BinOp} (h : SymExpr.isCommutative op = true) (a b : UInt64) :
    evalBinOp op (.u64 b) (.u64 a) = evalBinOp op (.u64 a) (.u64 b) := by
  match op with
  | .add => exact congrArg (Except.ok ∘ Val.u64) (UInt64.add_comm b a)
  | .mul => exact congrArg (Except.ok ∘ Val.u64) (UInt64.mul_comm b a)
  | .bitAnd => exact congrArg (Except.ok ∘ Val.u64) (UInt64.and_comm b a)
  | .bitOr => exact congrArg (Except.ok ∘ Val.u64) (UInt64.or_comm b a)
  | .bitXor => exact congrArg (Except.ok ∘ Val.u64) (UInt64.xor_comm b a)
  | .eq =>
    change Except.ok (Val.bool (b == a)) = Except.ok (Val.bool (a == b))
    exact congrArg (Except.ok ∘ Val.bool) (BEq.comm (a := b) (b := a))
  | .sub | .clmul64 | .clmul64Hi | .gf2Affine | .eor3 | .div | .mod
  | .shl | .shr | .sar | .lt | .le
  | .addChecked256 | .subChecked256 | .mulChecked256 => cases h

theorem evalBinOp_add_u64_right_inv {vx : Val} {a nl : UInt64}
    (h : evalBinOp .add vx (.u64 a) = .ok (.u64 nl)) :
    ∃ nx : UInt64, vx = .u64 nx ∧ nx + a = nl := by
  by_cases ha : a = 0
  · subst ha
    rw [evalBinOp_add_zero] at h
    injection h with h'; subst h'
    exact ⟨nl, rfl, UInt64.add_zero nl⟩
  · cases vx with
    | u64 nx =>
      injection h with h'; injection h' with h''
      exact ⟨nx, rfl, h''⟩
    | u256 _ | bool _ | tuple _ | objPtr _ | sarrayId _ | rawPtrId _ | storageMapId _ | unit =>
      cases a with | ofBitVec bv =>
        rcases bv with ⟨k, hk⟩
        cases k with
        | zero => exact absurd rfl ha
        | succ k' => cases h

theorem evalBinOp_sub_u64_right_inv {vx : Val} {a nl : UInt64}
    (h : evalBinOp .sub vx (.u64 a) = .ok (.u64 nl)) :
    ∃ nx : UInt64, vx = .u64 nx ∧ nx - a = nl := by
  by_cases ha : a = 0
  · subst ha
    rw [evalBinOp_sub_zero] at h
    injection h with h'; subst h'
    exact ⟨nl, rfl, UInt64.sub_zero nl⟩
  · cases vx with
    | u64 nx =>
      injection h with h'; injection h' with h''
      exact ⟨nx, rfl, h''⟩
    | u256 _ | bool _ | tuple _ | objPtr _ | sarrayId _ | rawPtrId _ | storageMapId _ | unit =>
      cases a with | ofBitVec bv =>
        rcases bv with ⟨k, hk⟩
        cases k with
        | zero => exact absurd rfl ha
        | succ k' => cases h

/-- Helper: when `denoteSymExpr ω (.binOp op x (.constU64 a)) = .ok (.u64 nl)` for `op = .add` or `.sub`,
    `x` denotes a `.u64`. -/
theorem denote_binOp_constU64_u64 {ω : SymValuation} {op : BinOp} {x : SymExpr} {a nl : UInt64}
    (hop : op = .add ∨ op = .sub)
    (hl : denoteSymExpr ω (.binOp op x (.constU64 a)) = .ok (.u64 nl)) :
    ∃ nx : UInt64, denoteSymExpr ω x = .ok (.u64 nx) ∧
      (if op = .add then nx + a = nl else nx - a = nl) := by
  simp only [denoteSymExpr] at hl
  cases hx : denoteSymExpr ω x with
  | error e => rw [hx] at hl; cases hl
  | ok vx =>
    rw [hx] at hl
    change evalBinOp op vx (.u64 a) = .ok (.u64 nl) at hl
    rcases hop with rfl | rfl
    · obtain ⟨nx, rfl, hadd⟩ := evalBinOp_add_u64_right_inv hl
      exact ⟨nx, rfl, hadd⟩
    · obtain ⟨nx, rfl, hsub'⟩ := evalBinOp_sub_u64_right_inv hl
      exact ⟨nx, rfl, hsub'⟩

/-- Algebraic identities on `UInt64` used by `normSymBinOpCore` additive reassociation. -/
theorem uint64_add_add_reassoc (nx a b : UInt64) :
    (nx + a) + b = if (a + b == 0) = true then nx else nx + (a + b) := by
  by_cases hs : (a + b == 0) = true
  · simp only [hs, ↓reduceIte]
    have hab : a + b = 0 := eq_of_beq hs
    rw [UInt64.add_assoc, hab, UInt64.add_zero]
  · simp [hs, UInt64.add_assoc]

theorem uint64_sub_add_reassoc (nx a b : UInt64) :
    (nx - a) + b =
      if (a == b) = true then nx
      else if decide (b > a) = true then nx + (b - a)
      else nx - (a - b) := by
  have h1 : (nx - a) + b = nx + (b - a) := by
    cases nx; cases a; cases b
    exact congrArg UInt64.ofBitVec (by
      change (_ - _) + _ = _ + (_ - _)
      rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      congr 1; exact BitVec.add_comm _ _)
  have h2 : (nx - a) + b = nx - (a - b) := by
    rw [h1]
    cases nx with | ofBitVec x => cases a with | ofBitVec ya => cases b with | ofBitVec yb =>
      exact congrArg UInt64.ofBitVec (by
        change x + (yb - ya) = x - (ya - yb)
        have hzero : (ya - yb) + (yb - ya) = 0#64 := by
          rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]
          have : -yb + (yb + -ya) = -ya := by
            rw [← BitVec.add_assoc, BitVec.add_left_neg, BitVec.zero_add]
          rw [this, BitVec.add_right_neg]
        have hneg : -(ya - yb) = yb - ya := by
          have h0 : -(ya - yb) + ((ya - yb) + (yb - ya)) = -(ya - yb) + 0#64 :=
            congrArg (-(ya - yb) + ·) hzero
          rw [← BitVec.add_assoc, BitVec.add_left_neg, BitVec.zero_add, BitVec.add_zero] at h0
          exact h0.symm
        rw [← hneg, ← BitVec.sub_eq_add_neg])
  by_cases hab : (a == b) = true
  · simp only [hab, ↓reduceIte]
    have e := eq_of_beq hab; subst e
    rw [h1, UInt64.sub_self, UInt64.add_zero]
  · simp only [hab, Bool.false_eq_true, ↓reduceIte]
    by_cases hgt : decide (b > a) = true
    · simp [hgt, h1]
    · simp [hgt, h2]

theorem uint64_add_sub_reassoc (nx a b : UInt64) :
    (nx + a) - b =
      if (a == b) = true then nx
      else if decide (a > b) = true then nx + (a - b)
      else nx - (b - a) := by
  have h1 : (nx + a) - b = nx + (a - b) := by
    cases nx; cases a; cases b
    exact congrArg UInt64.ofBitVec (by
      change (_ + _) - _ = _ + (_ - _)
      rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc])
  have h2 : (nx + a) - b = nx - (b - a) := by
    rw [h1]
    cases nx with | ofBitVec x => cases a with | ofBitVec ya => cases b with | ofBitVec yb =>
      exact congrArg UInt64.ofBitVec (by
        change x + (ya - yb) = x - (yb - ya)
        have hzero : (yb - ya) + (ya - yb) = 0#64 := by
          rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]
          have : -ya + (ya + -yb) = -yb := by
            rw [← BitVec.add_assoc, BitVec.add_left_neg, BitVec.zero_add]
          rw [this, BitVec.add_right_neg]
        have hneg : -(yb - ya) = ya - yb := by
          have h0 : -(yb - ya) + ((yb - ya) + (ya - yb)) = -(yb - ya) + 0#64 :=
            congrArg (-(yb - ya) + ·) hzero
          rw [← BitVec.add_assoc, BitVec.add_left_neg, BitVec.zero_add, BitVec.add_zero] at h0
          exact h0.symm
        rw [← hneg, ← BitVec.sub_eq_add_neg])
  by_cases hab : (a == b) = true
  · simp only [hab, ↓reduceIte]
    have e := eq_of_beq hab; subst e
    rw [h1, UInt64.sub_self, UInt64.add_zero]
  · simp only [hab, Bool.false_eq_true, ↓reduceIte]
    by_cases hgt : decide (a > b) = true
    · simp [hgt, h1]
    · simp [hgt, h2]

theorem uint64_sub_sub_reassoc (nx a b : UInt64) :
    (nx - a) - b = if (a + b == 0) = true then nx else nx - (a + b) := by
  have hss : (nx - a) - b = nx - (a + b) := by
    cases nx; cases a; cases b
    exact congrArg UInt64.ofBitVec (BitVec.sub_sub ..)
  by_cases hs : (a + b == 0) = true
  · simp only [hs, ↓reduceIte]
    have hab : a + b = 0 := eq_of_beq hs
    rw [hss, hab, UInt64.sub_zero]
  · simp [hs, hss]

theorem normSymBinOpCore_u64_denotes (ω : SymValuation) (op : BinOp) (l r : SymExpr)
    (w64 : Bool) (nl nr : UInt64)
    (hl : denoteSymExpr ω l = .ok (.u64 nl))
    (hr : denoteSymExpr ω r = .ok (.u64 nr)) :
    denoteSymExpr ω (normSymBinOpCore op l r w64) = evalBinOp op (.u64 nl) (.u64 nr) := by
  have deflt : denoteSymExpr ω (.binOp op l r) = evalBinOp op (.u64 nl) (.u64 nr) := by
    simp only [denoteSymExpr, hl, hr]
  cases op <;> dsimp only [normSymBinOpCore]
  case add =>
    split
    · cases hl; cases hr; rfl
    · cases hl
    · cases hr
    · cases hl
    · injection hr with h2; injection h2 with h2'; subst h2'
      rw [hl]; exact (evalBinOp_add_zero (.u64 nl)).symm
    · injection hl with h1; injection h1 with h1'; subst h1'
      rw [hr]; exact (evalBinOp_zero_add (.u64 nr)).symm
    · injection hr with h2; injection h2 with h2'; subst h2'
      rename_i x a b _
      cases hsub : subexprDefinitely64 w64 a x
      · exact deflt
      · simp only [↓reduceIte]
        obtain ⟨nx, hx, hnx⟩ := denote_binOp_constU64_u64 (Or.inl rfl) hl
        simp only [↓reduceIte] at hnx; subst hnx
        have hre := uint64_add_add_reassoc nx a b
        cases hs : (a + b == 0)
        · simp only [hs, Bool.false_eq_true, ↓reduceIte, denoteSymExpr, hx] at hre ⊢
          exact congrArg (Except.ok ∘ Val.u64) hre.symm
        · simp only [hs, ↓reduceIte] at hre ⊢
          rw [hx]; exact congrArg (Except.ok ∘ Val.u64) hre.symm
    · injection hr with h2; injection h2 with h2'; subst h2'
      rename_i x a b _
      cases hsub : subexprDefinitely64 w64 a x
      · exact deflt
      · simp only [↓reduceIte]
        obtain ⟨nx, hx, hnx⟩ := denote_binOp_constU64_u64 (Or.inr rfl) hl
        simp only [reduceCtorEq, ↓reduceIte] at hnx; subst hnx
        have hre := uint64_sub_add_reassoc nx a b
        cases hab : (a == b)
        · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hre ⊢
          by_cases hgt : b > a
          · simp only [hgt, decide_true, ↓reduceIte, denoteSymExpr, hx] at hre ⊢
            exact congrArg (Except.ok ∘ Val.u64) hre.symm
          · simp only [hgt, decide_false, Bool.false_eq_true, ↓reduceIte, denoteSymExpr, hx] at hre ⊢
            exact congrArg (Except.ok ∘ Val.u64) hre.symm
        · simp only [hab, ↓reduceIte] at hre ⊢
          rw [hx]; exact congrArg (Except.ok ∘ Val.u64) hre.symm
    · exact deflt
  case sub =>
    split
    · cases hl; cases hr; rfl
    · cases hl
    · cases hr
    · injection hr with h2; injection h2 with h2'; subst h2'
      rw [hl]; exact (evalBinOp_sub_zero (.u64 nl)).symm
    · injection hr with h2; injection h2 with h2'; subst h2'
      rename_i x a b _
      cases hsub : subexprDefinitely64 w64 a x
      · exact deflt
      · simp only [↓reduceIte]
        obtain ⟨nx, hx, hnx⟩ := denote_binOp_constU64_u64 (Or.inl rfl) hl
        simp only [↓reduceIte] at hnx; subst hnx
        have hre := uint64_add_sub_reassoc nx a b
        cases hab : (a == b)
        · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hre ⊢
          by_cases hgt : a > b
          · simp only [hgt, decide_true, ↓reduceIte, denoteSymExpr, hx] at hre ⊢
            exact congrArg (Except.ok ∘ Val.u64) hre.symm
          · simp only [hgt, decide_false, Bool.false_eq_true, ↓reduceIte, denoteSymExpr, hx] at hre ⊢
            exact congrArg (Except.ok ∘ Val.u64) hre.symm
        · simp only [hab, ↓reduceIte] at hre ⊢
          rw [hx]; exact congrArg (Except.ok ∘ Val.u64) hre.symm
    · injection hr with h2; injection h2 with h2'; subst h2'
      rename_i x a b _
      cases hsub : subexprDefinitely64 w64 a x
      · exact deflt
      · simp only [↓reduceIte]
        obtain ⟨nx, hx, hnx⟩ := denote_binOp_constU64_u64 (Or.inr rfl) hl
        simp only [reduceCtorEq, ↓reduceIte] at hnx; subst hnx
        have hre := uint64_sub_sub_reassoc nx a b
        cases hs : (a + b == 0)
        · simp only [hs, Bool.false_eq_true, ↓reduceIte, denoteSymExpr, hx] at hre ⊢
          exact congrArg (Except.ok ∘ Val.u64) hre.symm
        · simp only [hs, ↓reduceIte] at hre ⊢
          rw [hx]; exact congrArg (Except.ok ∘ Val.u64) hre.symm
    · cases hcond : ((w64 || exprDefinitely64 l) && (l == r))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases l with
        | constU256 _ => cases hl
        | _ => exact deflt
      · simp only [↓reduceIte]
        simp only [Bool.and_eq_true] at hcond
        have hlr := SymExpr_eq_of_beq hcond.2; subst hlr
        have hn : nl = nr := by rw [hl] at hr; injection hr with h1; injection h1 with h2
        subst hn
        change Except.ok (Val.u64 0) = Except.ok (Val.u64 (nl - nl))
        rw [UInt64.sub_self]
  case mul =>
    split
    · cases hl; cases hr; rfl
    · cases hl
    · cases hr
    · cases hl
    · injection hr with h2; injection h2 with h2'; subst h2'
      rw [hl]; exact (evalBinOp_mul_one (.u64 nl)).symm
    · injection hl with h1; injection h1 with h1'; subst h1'
      rw [hr]; exact (evalBinOp_one_mul (.u64 nr)).symm
    · injection hr with h2; injection h2 with h2'; subst h2'
      cases (w64 || exprDefinitely64 l)
      · exact deflt
      · change Except.ok (Val.u64 0) = Except.ok (Val.u64 (nl * 0)); rw [UInt64.mul_zero]
    · injection hl with h1; injection h1 with h1'; subst h1'
      cases (w64 || exprDefinitely64 r)
      · exact deflt
      · change Except.ok (Val.u64 0) = Except.ok (Val.u64 (0 * nr)); rw [UInt64.zero_mul]
    · injection hr with h2; injection h2 with h2'; subst h2'
      cases (w64 || exprDefinitely64 l)
      · exact deflt
      · simp only [↓reduceIte]
        split
        · rename_i k hk
          simp only [denoteSymExpr, hl]
          exact congrArg (Except.ok ∘ Val.u64) (pow2ShiftLog2_mul_right hk nl).symm
        · exact deflt
    · injection hl with h1; injection h1 with h1'; subst h1'
      cases (w64 || exprDefinitely64 r)
      · exact deflt
      · simp only [↓reduceIte]
        split
        · rename_i k hk
          simp only [denoteSymExpr, hr]
          exact congrArg (Except.ok ∘ Val.u64) (pow2ShiftLog2_mul_left hk nr).symm
        · exact deflt
    · exact deflt
  case div =>
    split
    · cases hl; cases hr; rfl
    · cases hr
    · injection hr with h2; injection h2 with h2'; subst h2'
      cases (w64 || exprDefinitely64 l)
      · exact deflt
      · change Except.ok (Val.u64 0) = Except.ok (Val.u64 (nl / 0))
        cases nl with | ofBitVec bv => exact congrArg (Except.ok ∘ Val.u64 ∘ UInt64.ofBitVec) BitVec.udiv_zero.symm
    · injection hr with h2; injection h2 with h2'; subst h2'
      rw [hl]
      change Except.ok (Val.u64 nl) = Except.ok (Val.u64 (nl / 1))
      cases nl with | ofBitVec bv => exact congrArg (Except.ok ∘ Val.u64 ∘ UInt64.ofBitVec) BitVec.udiv_one.symm
    · injection hr with h2; injection h2 with h2'; subst h2'
      cases (w64 || exprDefinitely64 l)
      · exact deflt
      · simp only [↓reduceIte]
        split
        · rename_i k hk
          simp only [denoteSymExpr, hl]
          exact congrArg (Except.ok ∘ Val.u64) (pow2ShiftLog2_div hk nl).symm
        · exact deflt
    · exact deflt
  case mod =>
    split
    · cases hl; cases hr; rfl
    · injection hr with h2; injection h2 with h2'; subst h2'
      cases (w64 || exprDefinitely64 l)
      · exact deflt
      · simp only [↓reduceIte, hl]
        change Except.ok (Val.u64 nl) = Except.ok (Val.u64 (nl % 0))
        cases nl with | ofBitVec bv => exact congrArg (Except.ok ∘ Val.u64 ∘ UInt64.ofBitVec) BitVec.umod_zero.symm
    · injection hr with h2; injection h2 with h2'; subst h2'
      cases (w64 || exprDefinitely64 l)
      · exact deflt
      · change Except.ok (Val.u64 0) = Except.ok (Val.u64 (nl % 1))
        cases nl with | ofBitVec bv => exact congrArg (Except.ok ∘ Val.u64 ∘ UInt64.ofBitVec) BitVec.umod_one.symm
    · injection hr with h2; injection h2 with h2'; subst h2'
      cases (w64 || exprDefinitely64 l)
      · exact deflt
      · simp only [↓reduceIte]
        split
        · rename_i k hk
          simp only [denoteSymExpr, hl]
          exact congrArg (Except.ok ∘ Val.u64) (pow2ShiftLog2_mod hk nl).symm
        · exact deflt
    · exact deflt
  case bitAnd =>
    split
    · cases hl; cases hr; rfl
    · cases hl
    · cases hr
    · cases hl
    · injection hr with h2; injection h2 with h2'; subst h2'
      cases (w64 || exprDefinitely64 l)
      · exact deflt
      · change Except.ok (Val.u64 0) = Except.ok (Val.u64 (nl &&& 0)); rw [UInt64.and_zero]
    · injection hl with h1; injection h1 with h1'; subst h1'
      cases (w64 || exprDefinitely64 r)
      · exact deflt
      · change Except.ok (Val.u64 0) = Except.ok (Val.u64 (0 &&& nr)); rw [UInt64.zero_and]
    · cases hxy : (l == r)
      · exact deflt
      · simp only [↓reduceIte]
        have hlr := SymExpr_eq_of_beq hxy; subst hlr
        have hn : nl = nr := by rw [hl] at hr; injection hr with h1; injection h1 with h2
        subst hn
        rw [hl]; exact (evalBinOp_and_self (.u64 nl)).symm
  case bitOr =>
    split
    · cases hl; cases hr; rfl
    · cases hl
    · cases hr
    · cases hl
    · injection hr with h2; injection h2 with h2'; subst h2'
      rw [hl]; exact (evalBinOp_or_zero (.u64 nl)).symm
    · injection hl with h1; injection h1 with h1'; subst h1'
      rw [hr]; exact (evalBinOp_zero_or (.u64 nr)).symm
    · cases hxy : (l == r)
      · exact deflt
      · simp only [↓reduceIte]
        have hlr := SymExpr_eq_of_beq hxy; subst hlr
        have hn : nl = nr := by rw [hl] at hr; injection hr with h1; injection h1 with h2
        subst hn
        rw [hl]; exact (evalBinOp_or_self (.u64 nl)).symm
  case bitXor =>
    split
    · cases hl; cases hr; rfl
    · cases hl
    · cases hr
    · cases hl
    · injection hr with h2; injection h2 with h2'; subst h2'
      rw [hl]; exact (evalBinOp_xor_zero (.u64 nl)).symm
    · injection hl with h1; injection h1 with h1'; subst h1'
      rw [hr]; exact (evalBinOp_zero_xor (.u64 nr)).symm
    · cases hcond : ((w64 || exprDefinitely64 l) && (l == r))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases l with
        | constU256 _ => cases hl
        | _ => exact deflt
      · simp only [↓reduceIte]
        simp only [Bool.and_eq_true] at hcond
        have hlr := SymExpr_eq_of_beq hcond.2; subst hlr
        have hn : nl = nr := by rw [hl] at hr; injection hr with h1; injection h1 with h2
        subst hn
        change Except.ok (Val.u64 0) = Except.ok (Val.u64 (nl ^^^ nl))
        rw [UInt64.xor_self]
  case shl =>
    split
    · cases hl; cases hr
      exact congrArg (Except.ok ∘ Val.u64) (uint64_shiftLeft_and_63 _ _)
    · cases hl
    · cases hr
    · injection hr with h2; injection h2 with h2'; subst h2'
      rw [hl]
      change Except.ok (Val.u64 nl) = Except.ok (Val.u64 (nl <<< 0))
      cases nl with | ofBitVec bv => exact congrArg (Except.ok ∘ Val.u64 ∘ UInt64.ofBitVec) (BitVec.shiftLeft_zero bv).symm
    · exact deflt
  case shr =>
    split
    · cases hl; cases hr
      exact congrArg (Except.ok ∘ Val.u64) (uint64_shiftRight_and_63 _ _)
    · cases hl
    · cases hr
    · injection hr with h2; injection h2 with h2'; subst h2'
      rw [hl]
      change Except.ok (Val.u64 nl) = Except.ok (Val.u64 (nl >>> 0))
      cases nl with | ofBitVec bv => exact congrArg (Except.ok ∘ Val.u64 ∘ UInt64.ofBitVec) (BitVec.ushiftRight_zero bv).symm
    · exact deflt
  case sar =>
    split
    · cases hl
    · cases hr
    · exact deflt
  case clmul64 =>
    split
    · cases hl; cases hr; rfl
    · exact deflt
  case clmul64Hi =>
    split
    · cases hl; cases hr; rfl
    · exact deflt
  case gf2Affine =>
    split
    · cases hl; cases hr; rfl
    · exact deflt
  case eor3 =>
    split
    · cases hl; cases hr; rfl
    · exact deflt
  case eq =>
    split
    · cases hl; cases hr; rfl
    · cases hl
    · cases hl
    · cases hr
    · cases hl
    · cases hr
    · cases hl
    · cases hr
    · cases hl
    · by_cases hxy : (l == r) = true
      · have hlr := SymExpr_eq_of_beq hxy; subst hlr
        have hn : nl = nr := by rw [hl] at hr; injection hr with h1; injection h1 with h2
        subst hn
        simp only [hxy, Bool.true_and]
        split
        · cases hl
        · split
          · change Except.ok (Val.bool true) = Except.ok (Val.bool (nl == nl)); simp
          · exact deflt
      · simp only [hxy, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; exact deflt
  case lt =>
    split
    · cases hl; cases hr; rfl
    · cases hl
    · by_cases hxy : (l == r) = true
      · have hlr := SymExpr_eq_of_beq hxy; subst hlr
        have hn : nl = nr := by rw [hl] at hr; injection hr with h1; injection h1 with h2
        subst hn
        simp only [hxy, Bool.true_and]
        split
        · cases hl
        · split
          · change Except.ok (Val.bool false) = Except.ok (Val.bool (decide (nl < nl)))
            have hirr : ¬ (nl < nl) := Nat.lt_irrefl nl.toNat
            simp [hirr]
          · exact deflt
      · simp only [hxy, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; exact deflt
  case le =>
    split
    · cases hl; cases hr; rfl
    · cases hl
    · by_cases hxy : (l == r) = true
      · have hlr := SymExpr_eq_of_beq hxy; subst hlr
        have hn : nl = nr := by rw [hl] at hr; injection hr with h1; injection h1 with h2
        subst hn
        simp only [hxy, Bool.true_and]
        split
        · cases hl
        · split
          · change Except.ok (Val.bool true) = Except.ok (Val.bool (decide (nl ≤ nl)))
            simp
          · exact deflt
      · simp only [hxy, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; exact deflt
  case addChecked256 => exact deflt
  case subChecked256 => exact deflt
  case mulChecked256 => exact deflt

/-- Single-step `normSymBinOpStep` on two 64-bit-denoting symbolic operands preserves concrete
    denotation for every binary operator. -/
theorem normSymBinOpStep_u64_denotes (ω : SymValuation) (op : BinOp) (l r : SymExpr)
    (w64Safe : Bool) (nl nr : UInt64)
    (hl : denoteSymExpr ω l = .ok (.u64 nl))
    (hr : denoteSymExpr ω r = .ok (.u64 nr)) :
    denoteSymExpr ω (normSymBinOpStep op l r w64Safe) = evalBinOp op (.u64 nl) (.u64 nr) := by
  unfold normSymBinOpStep
  cases hswap : (SymExpr.isCommutative op && decide (SymExpr.rank l > SymExpr.rank r))
  · exact normSymBinOpCore_u64_denotes ω op l r _ nl nr hl hr
  · simp only [↓reduceIte]
    simp only [Bool.and_eq_true] at hswap
    rw [normSymBinOpCore_u64_denotes ω op r l _ nr nl hr hl]
    exact evalBinOp_u64_comm hswap.1 nl nr

/-- A constant condition selects exactly one branch. -/
theorem normSymIteStep_constBool (t e : SymExpr) (b : Bool) :
    normSymIteStep (.constBool b) t e = if b then t else e := by
  cases b <;> rfl

/-- Identical branches collapse when the condition is definitely boolean and non-literal. -/
theorem normSymIteStep_same_branch (c t : SymExpr) :
    atomDefinitelyBool c = true → normSymIteStep c t t = t := by
  intro h
  cases c with
  | constBool b => cases b <;> rfl
  | binOp op l r => cases op <;> simp [normSymIteStep, atomDefinitelyBool] at h ⊢
  | ite c1 t1 e1 => simp [normSymIteStep, h]
  | _ => simp [atomDefinitelyBool] at h

/-- A pure 64-bit scalar expression denotes exactly what `evalScalarExpr` computes. -/
theorem scalarToSymExpr_denotes (env : VarEnv) (e : ScalarExpr) :
    isPureU64ScalarExpr e = true →
    denoteSymExpr (SymValuation.ofVarEnv env) (scalarToSymExpr e) = evalScalarExpr env e := by
  intro h
  induction e with
  | constU64 v => rfl
  | constBool b => simp [isPureU64ScalarExpr] at h
  | var id => rfl
  | binOp op l r ihl ihr =>
    simp only [isPureU64ScalarExpr, Bool.and_eq_true] at h
    rcases h with ⟨⟨hop, hl⟩, hr⟩
    simp only [scalarToSymExpr, denoteSymExpr, evalScalarExpr, ihl hl, ihr hr]
    cases evalScalarExpr env l <;> cases evalScalarExpr env r <;> rfl
  | unaryOp op a iha =>
    cases op <;> simp [isPureU64ScalarExpr] at h
    · simp only [scalarToSymExpr, denoteSymExpr, evalScalarExpr, iha h]
      cases evalScalarExpr env a <;> rfl
    · simp only [scalarToSymExpr, denoteSymExpr, evalScalarExpr, iha h]
      cases evalScalarExpr env a <;> rfl
  | select c t e ihc iht ihe => simp [isPureU64ScalarExpr] at h
  | fma a b c iha ihb ihc => simp [isPureU64ScalarExpr] at h

/-- `normSymUnaryOpStep` preserves `some sortU64` under `.not` and `.neg`. -/
theorem normSymUnaryOpStep_sortU64 (st : SymExecState) (op : UnaryOp) (a : SymExpr)
    (hop : op = .not ∨ op = .neg)
    (hsort : symExprScalarSort? st a = some sortU64) :
    symExprScalarSort? st (normSymUnaryOpStep op a) = some sortU64 := by
  rcases hop with rfl | rfl
  · rw [normSymUnaryOpStep.eq_def]
    cases a with
    | constBool _ => cases hsort
    | constU64 _ => rfl
    | constU256 _ => cases hsort
    | unaryOp op2 x =>
      cases op2 with
      | not =>
        dsimp only []
        simp only [symExprScalarSort?] at hsort
        cases x with
        | constU256 _ => cases hsort
        | _ => dsimp only []; split <;> exact hsort
      | neg | clz256 => exact hsort
    | _ => exact hsort
  · rw [normSymUnaryOpStep.eq_def]
    cases a with
    | constBool _ => cases hsort
    | constU64 _ => rfl
    | constU256 _ => cases hsort
    | unaryOp op2 x =>
      cases op2 with
      | neg =>
        dsimp only []
        simp only [symExprScalarSort?] at hsort
        split <;> exact hsort
      | not | clz256 => exact hsort
    | _ => exact hsort

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
  rcases hSymOk with ⟨⟨hExSrc, hExTgt⟩, hSupp⟩
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
