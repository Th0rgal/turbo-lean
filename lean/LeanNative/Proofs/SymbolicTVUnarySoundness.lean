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
# Unary & Constant-Reassociation Soundness for `SymbolicTV` (`LeanNative.Proofs.SymbolicTVUnarySoundness`)

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


end LeanNative.Proofs
