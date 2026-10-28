import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics

/-! ## Kernel-Checked Bitvector & UInt64 Algebraic Identities -/

theorem uint64_add_zero (a : UInt64) : a + (0 : UInt64) = a := UInt64.add_zero a
theorem uint64_zero_add (a : UInt64) : (0 : UInt64) + a = a := UInt64.zero_add a
theorem uint64_sub_zero (a : UInt64) : a - (0 : UInt64) = a := UInt64.sub_zero a
theorem uint64_mul_one (a : UInt64) : a * (1 : UInt64) = a := UInt64.mul_one a
theorem uint64_one_mul (a : UInt64) : (1 : UInt64) * a = a := UInt64.one_mul a
theorem uint64_xor_zero (a : UInt64) : a ^^^ (0 : UInt64) = a := UInt64.xor_zero
theorem uint64_zero_xor (a : UInt64) : (0 : UInt64) ^^^ a = a := UInt64.zero_xor
theorem uint64_and_self (a : UInt64) : a &&& a = a := UInt64.and_self
theorem uint64_or_self (a : UInt64) : a ||| a = a := UInt64.or_self
theorem uint64_or_zero (a : UInt64) : a ||| (0 : UInt64) = a := UInt64.or_zero
theorem uint64_zero_or (a : UInt64) : (0 : UInt64) ||| a = a := UInt64.zero_or

theorem uint64_mul_two (a : UInt64) : a * (2 : UInt64) = a <<< (1 : UInt64) := by cases a with | ofBitVec bv => exact congrArg UInt64.ofBitVec (by change bv * 2#64 = bv <<< 1; rw [BitVec.shiftLeft_eq_mul_twoPow]; rfl)
theorem uint64_mul_four (a : UInt64) : a * (4 : UInt64) = a <<< (2 : UInt64) := by cases a with | ofBitVec bv => exact congrArg UInt64.ofBitVec (by change bv * 4#64 = bv <<< 2; rw [BitVec.shiftLeft_eq_mul_twoPow]; rfl)
theorem uint64_mul_eight (a : UInt64) : a * (8 : UInt64) = a <<< (3 : UInt64) := by cases a with | ofBitVec bv => exact congrArg UInt64.ofBitVec (by change bv * 8#64 = bv <<< 3; rw [BitVec.shiftLeft_eq_mul_twoPow]; rfl)
theorem uint64_mul_sixteen (a : UInt64) : a * (16 : UInt64) = a <<< (4 : UInt64) := by cases a with | ofBitVec bv => exact congrArg UInt64.ofBitVec (by change bv * 16#64 = bv <<< 4; rw [BitVec.shiftLeft_eq_mul_twoPow]; rfl)
theorem uint64_mul_thirtytwo (a : UInt64) : a * (32 : UInt64) = a <<< (5 : UInt64) := by cases a with | ofBitVec bv => exact congrArg UInt64.ofBitVec (by change bv * 32#64 = bv <<< 5; rw [BitVec.shiftLeft_eq_mul_twoPow]; rfl)
theorem uint64_two_mul (a : UInt64) : (2 : UInt64) * a = a <<< (1 : UInt64) := by rw [UInt64.mul_comm, uint64_mul_two]
theorem uint64_four_mul (a : UInt64) : (4 : UInt64) * a = a <<< (2 : UInt64) := by rw [UInt64.mul_comm, uint64_mul_four]
theorem uint64_eight_mul (a : UInt64) : (8 : UInt64) * a = a <<< (3 : UInt64) := by rw [UInt64.mul_comm, uint64_mul_eight]
theorem uint64_div_two (a : UInt64) : a / (2 : UInt64) = a >>> (1 : UInt64) := by cases a with | ofBitVec bv => rcases bv with ⟨n, _⟩; exact congrArg UInt64.ofBitVec (BitVec.eq_of_toNat_eq (by change n / 2 = n >>> 1; rw [Nat.shiftRight_eq_div_pow]))
theorem uint64_div_four (a : UInt64) : a / (4 : UInt64) = a >>> (2 : UInt64) := by cases a with | ofBitVec bv => rcases bv with ⟨n, _⟩; exact congrArg UInt64.ofBitVec (BitVec.eq_of_toNat_eq (by change n / 4 = n >>> 2; rw [Nat.shiftRight_eq_div_pow]))
theorem uint64_div_eight (a : UInt64) : a / (8 : UInt64) = a >>> (3 : UInt64) := by cases a with | ofBitVec bv => rcases bv with ⟨n, _⟩; exact congrArg UInt64.ofBitVec (BitVec.eq_of_toNat_eq (by change n / 8 = n >>> 3; rw [Nat.shiftRight_eq_div_pow]))
theorem uint64_add_self_shl_one (a : UInt64) : a + a = a <<< (1 : UInt64) := by rw [← uint64_mul_two]; cases a with | ofBitVec bv => exact congrArg UInt64.ofBitVec (by change bv + bv = bv * 2#64; rw [BitVec.mul_two])
theorem uint64_add_assoc_const (a c1 c2 : UInt64) : (a + c1) + c2 = a + (c1 + c2) := UInt64.add_assoc a c1 c2
theorem uint64_and_mask_coalesce (a m1 m2 : UInt64) : (a &&& m1) &&& m2 = a &&& (m1 &&& m2) := by cases a; cases m1; cases m2; exact congrArg UInt64.ofBitVec (BitVec.and_assoc ..)
theorem uint64_or_mask_coalesce (a m1 m2 : UInt64) : (a ||| m1) ||| m2 = a ||| (m1 ||| m2) := by cases a; cases m1; cases m2; exact congrArg UInt64.ofBitVec (BitVec.or_assoc ..)
theorem uint64_xor_mask_coalesce (a m1 m2 : UInt64) : (a ^^^ m1) ^^^ m2 = a ^^^ (m1 ^^^ m2) := by cases a; cases m1; cases m2; exact congrArg UInt64.ofBitVec (BitVec.xor_assoc ..)
theorem uint64_mul_add_distrib_const (a b c : UInt64) : a * b + a * c = a * (b + c) := by cases a; cases b; cases c; exact congrArg UInt64.ofBitVec BitVec.mul_add.symm

/-! ## Semantic Lemmas for `evalBinOp` -/

@[simp] theorem evalBinOp_add_zero (v : Val) : evalBinOp .add v (.u64 0) = .ok v := by unfold evalBinOp; cases v <;> simp
@[simp] theorem evalBinOp_zero_add (v : Val) : evalBinOp .add (.u64 0) v = .ok v := by unfold evalBinOp; cases v <;> simp
@[simp] theorem evalBinOp_sub_zero (v : Val) : evalBinOp .sub v (.u64 0) = .ok v := by unfold evalBinOp; cases v <;> simp
@[simp] theorem evalBinOp_mul_one (v : Val) : evalBinOp .mul v (.u64 1) = .ok v := by unfold evalBinOp; cases v <;> simp
@[simp] theorem evalBinOp_one_mul (v : Val) : evalBinOp .mul (.u64 1) v = .ok v := by unfold evalBinOp; cases v <;> simp
@[simp] theorem evalBinOp_xor_zero (v : Val) : evalBinOp .bitXor v (.u64 0) = .ok v := by unfold evalBinOp; cases v <;> simp
@[simp] theorem evalBinOp_zero_xor (v : Val) : evalBinOp .bitXor (.u64 0) v = .ok v := by unfold evalBinOp; cases v <;> simp
@[simp] theorem evalBinOp_or_zero (v : Val) : evalBinOp .bitOr v (.u64 0) = .ok v := by unfold evalBinOp; cases v <;> simp
@[simp] theorem evalBinOp_zero_or (v : Val) : evalBinOp .bitOr (.u64 0) v = .ok v := by unfold evalBinOp; cases v <;> simp
@[simp] theorem evalBinOp_and_self (v : Val) : evalBinOp .bitAnd v v = .ok v := by unfold evalBinOp; cases v <;> simp [Val.beq_self]
@[simp] theorem evalBinOp_or_self (v : Val) : evalBinOp .bitOr v v = .ok v := by unfold evalBinOp; cases v <;> simp [Val.beq_self]

theorem evalBinOp_mul_two (v : Val) : evalBinOp .mul v (.u64 2) = evalBinOp .shl v (.u64 1) := by unfold evalBinOp; cases v with | u64 _ => simp [uint64_mul_two] | _ => rfl
theorem evalBinOp_mul_four (v : Val) : evalBinOp .mul v (.u64 4) = evalBinOp .shl v (.u64 2) := by unfold evalBinOp; cases v with | u64 _ => simp [uint64_mul_four] | _ => rfl
theorem evalBinOp_mul_eight (v : Val) : evalBinOp .mul v (.u64 8) = evalBinOp .shl v (.u64 3) := by unfold evalBinOp; cases v with | u64 _ => simp [uint64_mul_eight] | _ => rfl
theorem evalBinOp_mul_sixteen (v : Val) : evalBinOp .mul v (.u64 16) = evalBinOp .shl v (.u64 4) := by unfold evalBinOp; cases v with | u64 _ => simp [uint64_mul_sixteen] | _ => rfl
theorem evalBinOp_mul_thirtytwo (v : Val) : evalBinOp .mul v (.u64 32) = evalBinOp .shl v (.u64 5) := by unfold evalBinOp; cases v with | u64 _ => simp [uint64_mul_thirtytwo] | _ => rfl
theorem evalBinOp_two_mul (v : Val) : evalBinOp .mul (.u64 2) v = evalBinOp .shl v (.u64 1) := by unfold evalBinOp; cases v with | u64 _ => simp [uint64_two_mul] | _ => rfl
theorem evalBinOp_four_mul (v : Val) : evalBinOp .mul (.u64 4) v = evalBinOp .shl v (.u64 2) := by unfold evalBinOp; cases v with | u64 _ => simp [uint64_four_mul] | _ => rfl
theorem evalBinOp_eight_mul (v : Val) : evalBinOp .mul (.u64 8) v = evalBinOp .shl v (.u64 3) := by unfold evalBinOp; cases v with | u64 _ => simp [uint64_eight_mul] | _ => rfl
@[simp] theorem evalBinOp_div_one (v : Val) : evalBinOp .div v (.u64 1) = .ok v := by unfold evalBinOp; cases v <;> simp
theorem evalBinOp_div_two (v : Val) : evalBinOp .div v (.u64 2) = evalBinOp .shr v (.u64 1) := by unfold evalBinOp; cases v with | u64 _ => simp [uint64_div_two] | _ => rfl
theorem evalBinOp_div_four (v : Val) : evalBinOp .div v (.u64 4) = evalBinOp .shr v (.u64 2) := by unfold evalBinOp; cases v with | u64 _ => simp [uint64_div_four] | _ => rfl
theorem evalBinOp_div_eight (v : Val) : evalBinOp .div v (.u64 8) = evalBinOp .shr v (.u64 3) := by unfold evalBinOp; cases v with | u64 _ => simp [uint64_div_eight] | _ => rfl
@[simp] theorem evalBinOp_shl_zero (v : Val) : evalBinOp .shl v (.u64 0) = .ok v := by unfold evalBinOp; cases v <;> simp
@[simp] theorem evalBinOp_shr_zero (v : Val) : evalBinOp .shr v (.u64 0) = .ok v := by unfold evalBinOp; cases v <;> simp

/-! ## Verified Scalar Peephole Rewriter -/

/-- Verified algebraic rewrite step for binary scalar operations. -/
def rewriteBinOpStep (op : BinOp) (lhs rhs : ScalarExpr) : ScalarExpr :=
  match op with
  | .add =>
    if rhs = .constU64 0 then lhs
    else if lhs = .constU64 0 then rhs
    else .binOp .add lhs rhs
  | .sub =>
    if rhs = .constU64 0 then lhs
    else .binOp .sub lhs rhs
  | .mul =>
    if rhs = .constU64 1 then lhs
    else if lhs = .constU64 1 then rhs
    else if rhs = .constU64 2 then .binOp .shl lhs (.constU64 1)
    else if rhs = .constU64 4 then .binOp .shl lhs (.constU64 2)
    else if rhs = .constU64 8 then .binOp .shl lhs (.constU64 3)
    else if rhs = .constU64 16 then .binOp .shl lhs (.constU64 4)
    else if rhs = .constU64 32 then .binOp .shl lhs (.constU64 5)
    else if lhs = .constU64 2 then .binOp .shl rhs (.constU64 1)
    else if lhs = .constU64 4 then .binOp .shl rhs (.constU64 2)
    else if lhs = .constU64 8 then .binOp .shl rhs (.constU64 3)
    else .binOp .mul lhs rhs
  | .div =>
    if rhs = .constU64 1 then lhs
    else if rhs = .constU64 2 then .binOp .shr lhs (.constU64 1)
    else if rhs = .constU64 4 then .binOp .shr lhs (.constU64 2)
    else if rhs = .constU64 8 then .binOp .shr lhs (.constU64 3)
    else .binOp .div lhs rhs
  | .shl =>
    if rhs = .constU64 0 then lhs
    else .binOp .shl lhs rhs
  | .shr =>
    if rhs = .constU64 0 then lhs
    else .binOp .shr lhs rhs
  | .bitXor =>
    if rhs = .constU64 0 then lhs
    else if lhs = .constU64 0 then rhs
    else .binOp .bitXor lhs rhs
  | .bitAnd =>
    if lhs = rhs then lhs
    else .binOp .bitAnd lhs rhs
  | .bitOr =>
    if lhs = rhs then lhs
    else if rhs = .constU64 0 then lhs
    else if lhs = .constU64 0 then rhs
    else .binOp .bitOr lhs rhs
  | _ => .binOp op lhs rhs

/-- Verified branch-folding step for `select`. -/
def rewriteSelectStep (cond thenVal elseVal : ScalarExpr) : ScalarExpr :=
  if cond = .constBool true then thenVal
  else if cond = .constBool false then elseVal
  else .select cond thenVal elseVal

/-- Single-step verified peephole rewrite on `ScalarExpr`. -/
def rewriteScalarPeepholeStep : ScalarExpr → ScalarExpr
  | .binOp op lhs rhs => rewriteBinOpStep op lhs rhs
  | .select cond thenVal elseVal => rewriteSelectStep cond thenVal elseVal
  | .fma a b c => .binOp .add (.binOp .mul a b) c
  | other => other

/-- Recursive verified scalar peephole optimizer on `ScalarExpr`. -/
def rewriteScalarPeephole : ScalarExpr → ScalarExpr
  | .constU64 val => .constU64 val
  | .constBool val => .constBool val
  | .var id => .var id
  | .binOp op lhs rhs =>
    rewriteScalarPeepholeStep (.binOp op (rewriteScalarPeephole lhs) (rewriteScalarPeephole rhs))
  | .unaryOp op arg =>
    rewriteScalarPeepholeStep (.unaryOp op (rewriteScalarPeephole arg))
  | .select cond thenVal elseVal =>
    rewriteScalarPeepholeStep (.select (rewriteScalarPeephole cond) (rewriteScalarPeephole thenVal) (rewriteScalarPeephole elseVal))
  | .fma a b c =>
    rewriteScalarPeepholeStep (.fma (rewriteScalarPeephole a) (rewriteScalarPeephole b) (rewriteScalarPeephole c))

/-- Lift `rewriteScalarPeephole` to `LNIRExpr`. -/
def rewriteLNIRExpr : LNIRExpr → LNIRExpr
  | .scalar e => .scalar (rewriteScalarPeephole e)
  | other => other

/-! ## Machine-Checked Soundness Proofs via Generic Lifting Combinators -/

private theorem liftBinOpIdR (op : BinOp) (c : UInt64)
    (h : ∀ v, evalBinOp op v (.u64 c) = .ok v) (env : VarEnv) (lhs : ScalarExpr) :
    evalScalarExpr env (.binOp op lhs (.constU64 c)) = evalScalarExpr env lhs := by
  simp only [evalScalarExpr]; cases evalScalarExpr env lhs with | error _ => rfl | ok v => exact h v

private theorem liftBinOpIdL (op : BinOp) (c : UInt64)
    (h : ∀ v, evalBinOp op (.u64 c) v = .ok v) (env : VarEnv) (rhs : ScalarExpr) :
    evalScalarExpr env (.binOp op (.constU64 c) rhs) = evalScalarExpr env rhs := by
  simp only [evalScalarExpr]; cases evalScalarExpr env rhs with | error _ => rfl | ok v => exact h v

private theorem liftBinOpShiftR (op1 op2 : BinOp) (c k : UInt64)
    (h : ∀ v, evalBinOp op1 v (.u64 c) = evalBinOp op2 v (.u64 k)) (env : VarEnv) (lhs : ScalarExpr) :
    evalScalarExpr env (.binOp op1 lhs (.constU64 c)) = evalScalarExpr env (.binOp op2 lhs (.constU64 k)) := by
  simp only [evalScalarExpr]; cases evalScalarExpr env lhs with | error _ => rfl | ok v => exact h v

private theorem liftBinOpShiftL (op1 op2 : BinOp) (c k : UInt64)
    (h : ∀ v, evalBinOp op1 (.u64 c) v = evalBinOp op2 v (.u64 k)) (env : VarEnv) (rhs : ScalarExpr) :
    evalScalarExpr env (.binOp op1 (.constU64 c) rhs) = evalScalarExpr env (.binOp op2 rhs (.constU64 k)) := by
  simp only [evalScalarExpr]; cases evalScalarExpr env rhs with | error _ => rfl | ok v => exact h v

private theorem liftBinOpIdem (op : BinOp)
    (h : ∀ v, evalBinOp op v v = .ok v) (env : VarEnv) (lhs : ScalarExpr) :
    evalScalarExpr env (.binOp op lhs lhs) = evalScalarExpr env lhs := by
  simp only [evalScalarExpr]; cases evalScalarExpr env lhs with | error _ => rfl | ok v => exact h v

theorem rewriteBinOpStep_sound (op : BinOp) (lhs rhs : ScalarExpr) :
    ScalarExprEquiv (.binOp op lhs rhs) (rewriteBinOpStep op lhs rhs) := by
  intro env
  have h1 := liftBinOpIdR .add 0 evalBinOp_add_zero env lhs
  have h2 := liftBinOpIdL .add 0 evalBinOp_zero_add env rhs
  have h3 := liftBinOpIdR .sub 0 evalBinOp_sub_zero env lhs
  have h4 := liftBinOpIdR .mul 1 evalBinOp_mul_one env lhs
  have h5 := liftBinOpIdL .mul 1 evalBinOp_one_mul env rhs
  have h6 := liftBinOpShiftR .mul .shl 2 1 evalBinOp_mul_two env lhs
  have h7 := liftBinOpShiftR .mul .shl 4 2 evalBinOp_mul_four env lhs
  have h8 := liftBinOpShiftR .mul .shl 8 3 evalBinOp_mul_eight env lhs
  have h9 := liftBinOpShiftR .mul .shl 16 4 evalBinOp_mul_sixteen env lhs
  have h10 := liftBinOpShiftR .mul .shl 32 5 evalBinOp_mul_thirtytwo env lhs
  have h11 := liftBinOpShiftL .mul .shl 2 1 evalBinOp_two_mul env rhs
  have h12 := liftBinOpShiftL .mul .shl 4 2 evalBinOp_four_mul env rhs
  have h13 := liftBinOpShiftL .mul .shl 8 3 evalBinOp_eight_mul env rhs
  have h14 := liftBinOpIdR .div 1 evalBinOp_div_one env lhs
  have h15 := liftBinOpShiftR .div .shr 2 1 evalBinOp_div_two env lhs
  have h16 := liftBinOpShiftR .div .shr 4 2 evalBinOp_div_four env lhs
  have h17 := liftBinOpShiftR .div .shr 8 3 evalBinOp_div_eight env lhs
  have h18 := liftBinOpIdR .shl 0 evalBinOp_shl_zero env lhs
  have h19 := liftBinOpIdR .shr 0 evalBinOp_shr_zero env lhs
  have h20 := liftBinOpIdR .bitXor 0 evalBinOp_xor_zero env lhs
  have h21 := liftBinOpIdL .bitXor 0 evalBinOp_zero_xor env rhs
  have h22 := liftBinOpIdem .bitAnd evalBinOp_and_self env lhs
  have h23 := liftBinOpIdem .bitOr evalBinOp_or_self env lhs
  have h24 := liftBinOpIdR .bitOr 0 evalBinOp_or_zero env lhs
  have h25 := liftBinOpIdL .bitOr 0 evalBinOp_zero_or env rhs
  cases op <;> simp only [rewriteBinOpStep] <;>
    repeat (first | rfl | (split <;> first | (subst ‹_›; assumption) | skip))

theorem rewriteSelectStep_sound (cond thenVal elseVal : ScalarExpr) :
    ScalarExprEquiv (.select cond thenVal elseVal) (rewriteSelectStep cond thenVal elseVal) := by
  intro env; unfold rewriteSelectStep; split <;> first | (subst ‹_›; simp [evalScalarExpr]) | (split <;> first | (subst ‹_›; simp [evalScalarExpr]) | rfl)

theorem rewriteScalarPeepholeStep_sound (e : ScalarExpr) :
    ScalarExprEquiv e (rewriteScalarPeepholeStep e) := by
  intro env
  cases e with
  | constU64 _ | constBool _ | var _ | unaryOp _ _ => rfl
  | binOp op lhs rhs => exact rewriteBinOpStep_sound op lhs rhs env
  | select cond thenVal elseVal => exact rewriteSelectStep_sound cond thenVal elseVal env
  | fma a b c =>
    simp only [rewriteScalarPeepholeStep, evalScalarExpr]
    cases evalScalarExpr env a <;> cases evalScalarExpr env b <;> rfl

/-- Machine-checked soundness theorem for `rewriteScalarPeephole`:
    recursive algebraic & strength-reduction peephole optimization preserves exact scalar semantics. -/
theorem rewriteScalarPeephole_sound (e : ScalarExpr) :
    ScalarExprEquiv e (rewriteScalarPeephole e) := by
  intro env
  induction e with
  | constU64 _ | constBool _ | var _ => rfl
  | binOp op lhs rhs ihl ihr =>
    rw [rewriteScalarPeephole, ← rewriteScalarPeepholeStep_sound _ env]
    simp only [evalScalarExpr, ← ihl, ← ihr]
  | unaryOp op arg iha =>
    rw [rewriteScalarPeephole, ← rewriteScalarPeepholeStep_sound _ env]
    simp only [evalScalarExpr, ← iha]
  | select cond thenVal elseVal ihc iht ihe =>
    rw [rewriteScalarPeephole, ← rewriteScalarPeepholeStep_sound _ env]
    simp only [evalScalarExpr, ← ihc, ← iht, ← ihe]
  | fma a b c iha ihb ihc =>
    rw [rewriteScalarPeephole, ← rewriteScalarPeepholeStep_sound _ env]
    simp only [evalScalarExpr, ← iha, ← ihb, ← ihc]

/-- Machine-checked soundness theorem for `rewriteLNIRExpr`:
    rewriting scalar expressions inside `LNIRExpr` refines the original expression. -/
theorem rewriteLNIRExpr_sound (e : LNIRExpr) :
    ExprRefines e (rewriteLNIRExpr e) := by
  cases e with
  | scalar se => exact ExprRefines.of_scalar_equiv (rewriteScalarPeephole_sound se)
  | _ => exact ExprRefines.refl _

/-- Equality form of `rewriteLNIRExpr_sound` (`evalExpr_optimizeExpr_eq`). -/
theorem evalExpr_optimizeExpr_eq (env : VarEnv) (st : HeapState) (e : LNIRExpr) :
    evalExpr env st (rewriteLNIRExpr e) = evalExpr env st e := by
  cases e with
  | scalar se => simp only [rewriteLNIRExpr, evalExpr, ← rewriteScalarPeephole_sound se env]
  | _ => rfl

/-- Recursive verified code-level peephole optimizer on `LNIRCode`.
    Applies `rewriteLNIRExpr` to every `.letBind` and recurses through `.rawStore`,
    `.incRef`, `.decRef`, `.ite`, `.seqFor`, `.parFor`, `.ret`, and `.unreachable`. -/
def rewriteCodePeephole : LNIRCode → LNIRCode
  | .letBind dst ty val k =>
    .letBind dst ty (rewriteLNIRExpr val) (rewriteCodePeephole k)
  | .rawStore ptrVar idxVar valVar elemTy k =>
    .rawStore ptrVar idxVar valVar elemTy (rewriteCodePeephole k)
  | .incRef objVar count k =>
    .incRef objVar count (rewriteCodePeephole k)
  | .decRef objVar count k =>
    .decRef objVar count (rewriteCodePeephole k)
  | .ite condVar thenBranch elseBranch =>
    .ite condVar (rewriteCodePeephole thenBranch) (rewriteCodePeephole elseBranch)
  | .seqFor idxVar loVar hiVar accVar accInit accTy stepBody k =>
    .seqFor idxVar loVar hiVar accVar accInit accTy (rewriteCodePeephole stepBody) (rewriteCodePeephole k)
  | .parFor outVar lenVar inputs elemTy kernel k =>
    .parFor outVar lenVar inputs elemTy kernel (rewriteCodePeephole k)
  | .ret v => .ret v
  | .unreachable => .unreachable

/-- Exact operational evaluation equality for recursive `rewriteCodePeephole` across `LNIRCode`. -/
theorem evalCode_rewriteCodePeephole_eq (c : LNIRCode) :
    ∀ (fuel : Nat) (env : VarEnv) (st : HeapState),
      evalCode fuel env st (rewriteCodePeephole c) = evalCode fuel env st c := by
  induction c with
  | letBind dst ty val k ih =>
    intro fuel env st; rw [rewriteCodePeephole, evalCode, evalCode, evalExpr_optimizeExpr_eq]
    cases evalExpr env st val with | error _ => rfl | ok pair => exact ih fuel (env.bind dst pair.1) pair.2
  | rawStore ptrVar idxVar valVar elemTy k ih =>
    intro fuel env st; rw [rewriteCodePeephole, evalCode, evalCode]
    cases env ptrVar with | none => rfl | some pval =>
      cases env idxVar with | none => cases pval <;> rfl | some ival =>
        cases env valVar with | none => cases pval <;> cases ival <;> rfl | some vval =>
          cases pval <;> cases ival <;> cases vval <;> try rfl
          all_goals (simp only; cases st.writeElemExclusive _ _ _ with | error _ => rfl | ok st1 => exact ih fuel env st1)
  | incRef objVar count k ih =>
    intro fuel env st; rw [rewriteCodePeephole, evalCode, evalCode]
    cases st.evalIncRef env objVar count with
    | error _ => rfl
    | ok st1 => exact ih fuel env st1
  | decRef objVar count k ih =>
    intro fuel env st; rw [rewriteCodePeephole, evalCode, evalCode]
    cases st.evalDecRef env objVar count with
    | error _ => rfl
    | ok st1 => exact ih fuel env st1
  | ite condVar thenBranch elseBranch iht ihe =>
    intro fuel env st
    simp only [rewriteCodePeephole, evalCode, iht fuel env st, ihe fuel env st]
  | seqFor idxVar loVar hiVar accVar accInit accTy stepBody k ihs ihk =>
    intro fuel env st; rw [rewriteCodePeephole, evalCode, evalCode]
    have hstep : (fun stepEnv stepSt => evalCode fuel stepEnv stepSt (rewriteCodePeephole stepBody)) =
                 (fun stepEnv stepSt => evalCode fuel stepEnv stepSt stepBody) := by
      funext stepEnv stepSt; exact ihs fuel stepEnv stepSt
    rw [hstep]
    cases env loVar with | none => rfl | some loval =>
      cases env hiVar with | none => cases loval <;> rfl | some hival =>
        cases env accInit with | none => cases loval <;> cases hival <;> rfl | some initVal =>
          cases loval <;> cases hival <;> try rfl
          simp only; cases evalSeqLoop _ _ idxVar accVar initVal env st _ with
          | error _ => rfl | ok pair => exact ihk fuel (env.bind accVar pair.1) pair.2
  | parFor outVar lenVar inputs elemTy kernel k ih =>
    intro fuel env st; rw [rewriteCodePeephole, evalCode, evalCode]
    cases evalParFor fuel env st lenVar inputs kernel with
    | error _ => rfl
    | ok pair => exact ih fuel (env.bind outVar pair.1) pair.2
  | ret _ => intro _ _ _; rfl
  | unreachable => intro _ _ _; rfl

/-- End-to-end recursive `LNIRCode` pass refinement theorem (`rewriteCodePeephole_refines`):
    applying `rewriteCodePeephole` across an entire `LNIRCode` block refines the original code. -/
theorem rewriteCodePeephole_refines (c : LNIRCode) :
    CodeRefines c (rewriteCodePeephole c) := by
  intro fuel env st v st' hsrc
  rw [evalCode_rewriteCodePeephole_eq c fuel env st]
  exact hsrc

/-! ## 256-Bit (`UInt256` / `EVMWord`) & EVM Storage Map Soundness Theorems -/

theorem evalBinOp_u256_and_self (w : UInt256) : evalBinOp .bitAnd (.u256 w) (.u256 w) = .ok (.u256 w) := by unfold evalBinOp; simp
theorem evalBinOp_u256_or_self (w : UInt256) : evalBinOp .bitOr (.u256 w) (.u256 w) = .ok (.u256 w) := by unfold evalBinOp; simp
theorem evalBinOp_u256_xor_zero (w : UInt256) : evalBinOp .bitXor (.u256 w) (.u256 UInt256.zero) = .ok (.u256 w) := by unfold evalBinOp; simp
theorem evalBinOp_u256_or_zero (w : UInt256) : evalBinOp .bitOr (.u256 w) (.u256 UInt256.zero) = .ok (.u256 w) := by unfold evalBinOp; simp

/-- EVM `SLOAD` after `SSTORE` to the same 256-bit slot returns the stored `UInt256` value (`storageStore_load_same_sound`). -/
theorem storageStore_load_same_sound (env : VarEnv) (st : HeapState)
    (mapVar slotVar valVar : VarId) (mapId : Nat) (slot val : UInt256)
    (hmap : env mapVar = some (.storageMapId mapId))
    (hslot : env slotVar = some (.u256 slot))
    (hval : env valVar = some (.u256 val)) :
    (match evalExpr env st (.storageStore mapVar slotVar valVar) with
     | .ok (_, st1) => evalExpr env st1 (.storageLoad mapVar slotVar)
     | .error err => .error err) =
    .ok (.u256 val, st.storageStore mapId slot val) := by
  unfold evalExpr; simp [Val.toU256?, hmap, hslot, hval]

/-- EVM `SLOAD` after `SSTORE` to a distinct 256-bit slot preserves the prior slot value (`storageStore_load_ne_sound`). -/
theorem storageStore_load_ne_sound (env : VarEnv) (st : HeapState)
    (mapVar slot1Var slot2Var valVar : VarId) (mapId : Nat) (slot1 slot2 val : UInt256)
    (hmap : env mapVar = some (.storageMapId mapId))
    (hslot1 : env slot1Var = some (.u256 slot1))
    (hslot2 : env slot2Var = some (.u256 slot2))
    (hval : env valVar = some (.u256 val))
    (hne : (slot1 == slot2) = false) :
    (match evalExpr env st (.storageStore mapVar slot1Var valVar) with
     | .ok (_, st1) => evalExpr env st1 (.storageLoad mapVar slot2Var)
     | .error err => .error err) =
    .ok (.u256 (st.storageLoad mapId slot2), st.storageStore mapId slot1 val) := by
  unfold evalExpr
  simp [Val.toU256?, hmap, hslot1, hslot2, hval, HeapState.storageLoad_after_storageStore_ne st mapId slot1 slot2 val hne]

/-! ## Verified Binary Constant Folding (`rewriteConstFoldBinOp`) -/

theorem uint64_and_63_mod_64 (b : UInt64) : (b &&& 63).mod 64 = b.mod 64 := by
  cases b with | ofBitVec bv =>
    rcases bv with ⟨n, _⟩
    exact congrArg UInt64.ofBitVec (BitVec.eq_of_toNat_eq (by
      change (n &&& (2 ^ 6 - 1)) % 64 = n % 64
      rw [Nat.and_two_pow_sub_one_eq_mod n 6, Nat.mod_mod]))

@[simp] theorem uint64_shiftLeft_and_63 (a b : UInt64) : a <<< (b &&& 63) = a <<< b := by
  change UInt64.shiftLeft a (b &&& 63) = UInt64.shiftLeft a b; unfold UInt64.shiftLeft; rw [uint64_and_63_mod_64]

@[simp] theorem uint64_shiftRight_and_63 (a b : UInt64) : a >>> (b &&& 63) = a >>> b := by
  change UInt64.shiftRight a (b &&& 63) = UInt64.shiftRight a b; unfold UInt64.shiftRight; rw [uint64_and_63_mod_64]

/-- Verified binary constant folding on `UInt64` scalar literals. -/
def rewriteConstFoldBinOp (op : BinOp) (a b : UInt64) : ScalarExpr :=
  match op with
  | .add => .constU64 (a + b)
  | .sub => .constU64 (a - b)
  | .mul => .constU64 (a * b)
  | .bitAnd => .constU64 (a &&& b)
  | .bitOr => .constU64 (a ||| b)
  | .bitXor => .constU64 (a ^^^ b)
  | .shl => .constU64 (a <<< (b &&& 63))
  | .shr => .constU64 (a >>> (b &&& 63))
  | .eq => .constBool (a == b)
  | .lt => .constBool (a < b)
  | .le => .constBool (a ≤ b)
  | .clmul64 => .constU64 (clmul64 a b) | .clmul64Hi => .constU64 (clmul64Hi a b)
  | .gf2Affine => .constU64 (gf2Affine a b) | .eor3 => .constU64 (eor3 a b)
  | other => .binOp other (.constU64 a) (.constU64 b)

/-- Machine-checked soundness theorem for `rewriteConstFoldBinOp`:
    constant folding on `UInt64` binary operations preserves exact scalar evaluation semantics. -/
theorem evalBinOp_const_fold_sound (op : BinOp) (a b : UInt64) (env : VarEnv) :
    evalScalarExpr env (rewriteConstFoldBinOp op a b) =
    evalScalarExpr env (.binOp op (.constU64 a) (.constU64 b)) := by
  cases op <;> unfold rewriteConstFoldBinOp evalScalarExpr evalBinOp <;> try (unfold evalScalarExpr; simp)

/-- Single-step verified constant-folding wrapper on `ScalarExpr`. -/
def rewriteConstFoldStep : ScalarExpr → ScalarExpr
  | .binOp op (.constU64 a) (.constU64 b) => rewriteConstFoldBinOp op a b
  | other => other

theorem rewriteConstFoldStep_sound (e : ScalarExpr) :
    ScalarExprEquiv e (rewriteConstFoldStep e) := by
  intro env
  cases e with
  | binOp op lhs rhs =>
    cases lhs <;> cases rhs <;> try rfl
    case constU64.constU64 a b =>
      simp only [rewriteConstFoldStep]
      exact (evalBinOp_const_fold_sound op a b env).symm
  | _ => rfl

/-- Composed verified scalar peephole + binary constant-folding rewriter. -/
def rewriteScalarVerified (e : ScalarExpr) : ScalarExpr :=
  rewriteConstFoldStep (rewriteScalarPeephole e)

/-- Machine-checked soundness theorem for `rewriteScalarVerified`. -/
theorem rewriteScalarVerified_sound (e : ScalarExpr) :
    ScalarExprEquiv e (rewriteScalarVerified e) :=
  ScalarExprEquiv.trans
    (rewriteScalarPeephole_sound e)
    (rewriteConstFoldStep_sound (rewriteScalarPeephole e))

/-- Lift `rewriteScalarVerified` (peephole + binary constant folding) to `LNIRExpr`. -/
def rewriteLNIRExprVerified : LNIRExpr → LNIRExpr
  | .scalar se => .scalar (rewriteScalarVerified se)
  | other      => other

theorem rewriteLNIRExprVerified_sound (e : LNIRExpr) :
    ExprRefines e (rewriteLNIRExprVerified e) := by
  cases e with
  | scalar se => exact ExprRefines.of_scalar_equiv (rewriteScalarVerified_sound se)
  | _ => exact ExprRefines.refl _

theorem evalExpr_rewriteLNIRExprVerified_eq (env : VarEnv) (st : HeapState) (e : LNIRExpr) :
    evalExpr env st (rewriteLNIRExprVerified e) = evalExpr env st e := by
  cases e with
  | scalar se => simp only [rewriteLNIRExprVerified, evalExpr, ← rewriteScalarVerified_sound se env]
  | _ => rfl

/-- Recursive verified code-level optimizer on `LNIRCode` combining peephole identities
    and binary constant folding (`rewriteScalarVerified`). -/
def rewriteCodeVerified : LNIRCode → LNIRCode
  | .letBind dst ty val k =>
    .letBind dst ty (rewriteLNIRExprVerified val) (rewriteCodeVerified k)
  | .rawStore ptrVar idxVar valVar elemTy k =>
    .rawStore ptrVar idxVar valVar elemTy (rewriteCodeVerified k)
  | .incRef objVar count k =>
    .incRef objVar count (rewriteCodeVerified k)
  | .decRef objVar count k =>
    .decRef objVar count (rewriteCodeVerified k)
  | .ite condVar thenBranch elseBranch =>
    .ite condVar (rewriteCodeVerified thenBranch) (rewriteCodeVerified elseBranch)
  | .seqFor idxVar loVar hiVar accVar accInit accTy stepBody k =>
    .seqFor idxVar loVar hiVar accVar accInit accTy (rewriteCodeVerified stepBody) (rewriteCodeVerified k)
  | .parFor outVar lenVar inputs elemTy kernel k =>
    .parFor outVar lenVar inputs elemTy kernel (rewriteCodeVerified k)
  | .ret v => .ret v
  | .unreachable => .unreachable

/-- Exact operational evaluation equality for recursive `rewriteCodeVerified` across `LNIRCode`. -/
theorem evalCode_rewriteCodeVerified_eq (c : LNIRCode) :
    ∀ (fuel : Nat) (env : VarEnv) (st : HeapState),
      evalCode fuel env st (rewriteCodeVerified c) = evalCode fuel env st c := by
  induction c with
  | letBind dst ty val k ih =>
    intro fuel env st; rw [rewriteCodeVerified, evalCode, evalCode, evalExpr_rewriteLNIRExprVerified_eq]
    cases evalExpr env st val with | error _ => rfl | ok pair => exact ih fuel (env.bind dst pair.1) pair.2
  | rawStore ptrVar idxVar valVar elemTy k ih =>
    intro fuel env st; rw [rewriteCodeVerified, evalCode, evalCode]
    cases env ptrVar with | none => rfl | some pval =>
      cases env idxVar with | none => cases pval <;> rfl | some ival =>
        cases env valVar with | none => cases pval <;> cases ival <;> rfl | some vval =>
          cases pval <;> cases ival <;> cases vval <;> try rfl
          all_goals (simp only; cases st.writeElemExclusive _ _ _ with | error _ => rfl | ok st1 => exact ih fuel env st1)
  | incRef objVar count k ih =>
    intro fuel env st; rw [rewriteCodeVerified, evalCode, evalCode]
    cases st.evalIncRef env objVar count with
    | error _ => rfl
    | ok st1 => exact ih fuel env st1
  | decRef objVar count k ih =>
    intro fuel env st; rw [rewriteCodeVerified, evalCode, evalCode]
    cases st.evalDecRef env objVar count with
    | error _ => rfl
    | ok st1 => exact ih fuel env st1
  | ite condVar thenBranch elseBranch iht ihe =>
    intro fuel env st
    simp only [rewriteCodeVerified, evalCode, iht fuel env st, ihe fuel env st]
  | seqFor idxVar loVar hiVar accVar accInit accTy stepBody k ihs ihk =>
    intro fuel env st; rw [rewriteCodeVerified, evalCode, evalCode]
    have hstep : (fun stepEnv stepSt => evalCode fuel stepEnv stepSt (rewriteCodeVerified stepBody)) =
                 (fun stepEnv stepSt => evalCode fuel stepEnv stepSt stepBody) := by
      funext stepEnv stepSt; exact ihs fuel stepEnv stepSt
    rw [hstep]
    cases env loVar with | none => rfl | some loval =>
      cases env hiVar with | none => cases loval <;> rfl | some hival =>
        cases env accInit with | none => cases loval <;> cases hival <;> rfl | some initVal =>
          cases loval <;> cases hival <;> try rfl
          simp only; cases evalSeqLoop _ _ idxVar accVar initVal env st _ with
          | error _ => rfl | ok pair => exact ihk fuel (env.bind accVar pair.1) pair.2
  | parFor outVar lenVar inputs elemTy kernel k ih =>
    intro fuel env st; rw [rewriteCodeVerified, evalCode, evalCode]
    cases evalParFor fuel env st lenVar inputs kernel with
    | error _ => rfl
    | ok pair => exact ih fuel (env.bind outVar pair.1) pair.2
  | ret _ => intro _ _ _; rfl
  | unreachable => intro _ _ _; rfl

/-- End-to-end recursive `LNIRCode` pass refinement theorem (`rewriteCodeVerified_refines`):
    applying `rewriteCodeVerified` across an entire `LNIRCode` block refines the original code. -/
theorem rewriteCodeVerified_refines (c : LNIRCode) :
    CodeRefines c (rewriteCodeVerified c) := by
  intro fuel env st v st' hsrc
  rw [evalCode_rewriteCodeVerified_eq c fuel env st]
  exact hsrc

/-! ## Superoptimizer Multi-Node Template Soundness Theorems (`evalScalarExpr`) -/

theorem evalScalarExpr_add_self_u64 (env : VarEnv) (x : ScalarExpr) (a : UInt64) (hx : evalScalarExpr env x = .ok (.u64 a)) :
    evalScalarExpr env (.binOp .add x x) = evalScalarExpr env (.binOp .shl x (.constU64 1)) := by
  simp only [evalScalarExpr, hx]; exact congrArg (Except.ok ∘ Val.u64) (uint64_add_self_shl_one a)
theorem evalScalarExpr_add_assoc_const_u64 (env : VarEnv) (x : ScalarExpr) (a c1 c2 : UInt64) (hx : evalScalarExpr env x = .ok (.u64 a)) :
    evalScalarExpr env (.binOp .add (.binOp .add x (.constU64 c1)) (.constU64 c2)) = evalScalarExpr env (.binOp .add x (.constU64 (c1 + c2))) := by
  simp only [evalScalarExpr, hx]; exact congrArg (Except.ok ∘ Val.u64) (uint64_add_assoc_const a c1 c2)
theorem evalScalarExpr_and_mask_coalesce_u64 (env : VarEnv) (x : ScalarExpr) (a m1 m2 : UInt64) (hx : evalScalarExpr env x = .ok (.u64 a)) :
    evalScalarExpr env (.binOp .bitAnd (.binOp .bitAnd x (.constU64 m1)) (.constU64 m2)) = evalScalarExpr env (.binOp .bitAnd x (.constU64 (m1 &&& m2))) := by
  simp only [evalScalarExpr, hx]; exact congrArg (Except.ok ∘ Val.u64) (uint64_and_mask_coalesce a m1 m2)
theorem evalScalarExpr_or_mask_coalesce_u64 (env : VarEnv) (x : ScalarExpr) (a m1 m2 : UInt64) (hx : evalScalarExpr env x = .ok (.u64 a)) :
    evalScalarExpr env (.binOp .bitOr (.binOp .bitOr x (.constU64 m1)) (.constU64 m2)) = evalScalarExpr env (.binOp .bitOr x (.constU64 (m1 ||| m2))) := by
  simp only [evalScalarExpr, hx]; exact congrArg (Except.ok ∘ Val.u64) (uint64_or_mask_coalesce a m1 m2)
theorem evalScalarExpr_xor_mask_coalesce_u64 (env : VarEnv) (x : ScalarExpr) (a m1 m2 : UInt64) (hx : evalScalarExpr env x = .ok (.u64 a)) :
    evalScalarExpr env (.binOp .bitXor (.binOp .bitXor x (.constU64 m1)) (.constU64 m2)) = evalScalarExpr env (.binOp .bitXor x (.constU64 (m1 ^^^ m2))) := by
  simp only [evalScalarExpr, hx]; exact congrArg (Except.ok ∘ Val.u64) (uint64_xor_mask_coalesce a m1 m2)
theorem evalScalarExpr_mul_add_distrib_const_u64 (env : VarEnv) (x : ScalarExpr) (v a b : UInt64) (hx : evalScalarExpr env x = .ok (.u64 v)) :
    evalScalarExpr env (.binOp .add (.binOp .mul x (.constU64 a)) (.binOp .mul x (.constU64 b))) = evalScalarExpr env (.binOp .mul x (.constU64 (a + b))) := by
  simp only [evalScalarExpr, hx]; exact congrArg (Except.ok ∘ Val.u64) (uint64_mul_add_distrib_const v a b)

theorem bitvec64_allOnes_getLsbD (j : Nat) (hj : j < 64) : (0xffffffffffffffff#64).getLsbD j = true := by
  have h1 : (0xffffffffffffffff#64) = BitVec.allOnes 64 := rfl
  rw [h1, BitVec.getLsbD_allOnes]; exact decide_eq_true hj
theorem bitvec64_shr_shl_mask_collapse (bvx : BitVec 64) (s : Nat) :
    (bvx >>> s) <<< s = bvx &&& ((0xffffffffffffffff#64) <<< s) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
  by_cases hlt : i < s
  · simp [hi, hlt]
  · simp [hi, hlt, Nat.add_sub_of_le (Nat.le_of_not_lt hlt), bitvec64_allOnes_getLsbD (i - s) (Nat.lt_of_le_of_lt (Nat.sub_le i s) hi)]
theorem uint64_shr_shl_mask_collapse (x k : UInt64) : (x >>> k) <<< k = x &&& (0xffffffffffffffff <<< k) := by
  cases x with | ofBitVec bvx => cases k with | ofBitVec bvk =>
    exact congrArg UInt64.ofBitVec (bitvec64_shr_shl_mask_collapse bvx (bvk % 64#64).toNat)
theorem evalScalarExpr_shr_shl_mask_collapse_u64 (env : VarEnv) (x : ScalarExpr) (v k : UInt64) (hx : evalScalarExpr env x = .ok (.u64 v)) :
    evalScalarExpr env (.binOp .shl (.binOp .shr x (.constU64 k)) (.constU64 k)) = evalScalarExpr env (.binOp .bitAnd x (.constU64 (0xffffffffffffffff <<< k))) := by
  simp only [evalScalarExpr, hx]; exact congrArg (Except.ok ∘ Val.u64) (uint64_shr_shl_mask_collapse v k)
theorem evalScalarExpr_fma_fusion_u64 (env : VarEnv) (a b c : ScalarExpr) (va vb vc : UInt64)
    (ha : evalScalarExpr env a = .ok (.u64 va)) (hb : evalScalarExpr env b = .ok (.u64 vb)) (hc : evalScalarExpr env c = .ok (.u64 vc)) :
    evalScalarExpr env (.binOp .add (.binOp .mul a b) c) = evalScalarExpr env (.fma a b c) := by
  simp only [evalScalarExpr, ha, hb, hc]
theorem uint64_rotl_comm_or (x k : UInt64) : (x <<< k) ||| (x >>> (64 - k)) = (x >>> (64 - k)) ||| (x <<< k) := by
  cases x with | ofBitVec bvx => cases k with | ofBitVec bvk => exact congrArg UInt64.ofBitVec (BitVec.or_comm _ _)

namespace PeepholeProofs
  abbrev rewriteScalarPeephole_sound := @LeanNative.Proofs.rewriteScalarPeephole_sound
  abbrev rewriteLNIRExpr_sound := @LeanNative.Proofs.rewriteLNIRExpr_sound
  abbrev evalExpr_optimizeExpr_eq := @LeanNative.Proofs.evalExpr_optimizeExpr_eq
  abbrev evalCode_rewriteCodePeephole_eq := @LeanNative.Proofs.evalCode_rewriteCodePeephole_eq
  abbrev rewriteCodePeephole_refines := @LeanNative.Proofs.rewriteCodePeephole_refines
  abbrev evalBinOp_u256_and_self := @LeanNative.Proofs.evalBinOp_u256_and_self
  abbrev evalBinOp_u256_or_self := @LeanNative.Proofs.evalBinOp_u256_or_self
  abbrev evalBinOp_u256_xor_zero := @LeanNative.Proofs.evalBinOp_u256_xor_zero
  abbrev evalBinOp_u256_or_zero := @LeanNative.Proofs.evalBinOp_u256_or_zero
  abbrev storageStore_load_same_sound := @LeanNative.Proofs.storageStore_load_same_sound
  abbrev storageStore_load_ne_sound := @LeanNative.Proofs.storageStore_load_ne_sound
  abbrev evalBinOp_const_fold_sound := @LeanNative.Proofs.evalBinOp_const_fold_sound
  abbrev rewriteConstFoldStep_sound := @LeanNative.Proofs.rewriteConstFoldStep_sound
  abbrev rewriteScalarVerified_sound := @LeanNative.Proofs.rewriteScalarVerified_sound
  abbrev rewriteLNIRExprVerified_sound := @LeanNative.Proofs.rewriteLNIRExprVerified_sound
  abbrev evalExpr_rewriteLNIRExprVerified_eq := @LeanNative.Proofs.evalExpr_rewriteLNIRExprVerified_eq
  abbrev evalCode_rewriteCodeVerified_eq := @LeanNative.Proofs.evalCode_rewriteCodeVerified_eq
  abbrev rewriteCodeVerified_refines := @LeanNative.Proofs.rewriteCodeVerified_refines
  abbrev uint64_shr_shl_mask_collapse := @LeanNative.Proofs.uint64_shr_shl_mask_collapse
  abbrev evalScalarExpr_shr_shl_mask_collapse_u64 := @LeanNative.Proofs.evalScalarExpr_shr_shl_mask_collapse_u64
  abbrev evalScalarExpr_fma_fusion_u64 := @LeanNative.Proofs.evalScalarExpr_fma_fusion_u64
  abbrev uint64_rotl_comm_or := @LeanNative.Proofs.uint64_rotl_comm_or
end PeepholeProofs

end LeanNative.Proofs
