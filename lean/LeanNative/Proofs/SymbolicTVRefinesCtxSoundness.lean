import LeanNative.Proofs.SymbolicTVRefinesDefs
import LeanNative.Proofs.SuperoptSoundness

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Transform

theorem pureSymExprEq_sound : ∀ (s1 s2 : SymExpr), pureSymExprEq s1 s2 = true → s1 = s2
  | .constU64 a, .constU64 b, h => by simp [pureSymExprEq] at h; exact congrArg SymExpr.constU64 h
  | .constBool a, .constBool b, h => by simp [pureSymExprEq] at h; exact congrArg SymExpr.constBool h
  | .symVar a, .symVar b, h => by simp [pureSymExprEq] at h; exact congrArg SymExpr.symVar h
  | .binOp op1 l1 r1, .binOp op2 l2 r2, h => by
    simp only [pureSymExprEq, Bool.and_eq_true] at h
    rcases h with ⟨⟨hop, hl⟩, hr⟩
    rw [BinOp_eq_of_beq hop, pureSymExprEq_sound l1 l2 hl, pureSymExprEq_sound r1 r2 hr]
  | .unaryOp op1 a1, .unaryOp op2 a2, h => by
    simp only [pureSymExprEq, Bool.and_eq_true] at h
    rcases h with ⟨hop, ha⟩
    rw [UnaryOp_eq_of_beq hop, pureSymExprEq_sound a1 a2 ha]
  | .ite c1 t1 e1, .ite c2 t2 e2, h => by
    simp only [pureSymExprEq, Bool.and_eq_true] at h
    rcases h with ⟨⟨hc, ht⟩, he⟩
    rw [pureSymExprEq_sound c1 c2 hc, pureSymExprEq_sound t1 t2 ht, pureSymExprEq_sound e1 e2 he]
  | .constU64 _, .constBool _, h | .constU64 _, .symVar _, h | .constU64 _, .binOp _ _ _, h
  | .constU64 _, .unaryOp _ _, h | .constU64 _, .ite _ _ _, h | .constU64 _, .constU256 _, h
  | .constU64 _, .allocTag _, h | .constU64 _, .rcSym _ _, h | .constU64 _, .ctorTag _ _, h
  | .constU64 _, .ctorLen _ _ _, h | .constU64 _, .sarrayLen _, h | .constU64 _, .mulDiv256 _ _ _ _, h
  | .constU64 _, .tuple _, h | .constU64 _, .bufElem _ _ _, h | .constU64 _, .unit, h => by
    simp [pureSymExprEq] at h
  | .constBool _, .constU64 _, h | .constBool _, .symVar _, h | .constBool _, .binOp _ _ _, h
  | .constBool _, .unaryOp _ _, h | .constBool _, .ite _ _ _, h | .constBool _, .constU256 _, h
  | .constBool _, .allocTag _, h | .constBool _, .rcSym _ _, h | .constBool _, .ctorTag _ _, h
  | .constBool _, .ctorLen _ _ _, h | .constBool _, .sarrayLen _, h | .constBool _, .mulDiv256 _ _ _ _, h
  | .constBool _, .tuple _, h | .constBool _, .bufElem _ _ _, h | .constBool _, .unit, h => by
    simp [pureSymExprEq] at h
  | .symVar _, .constU64 _, h | .symVar _, .constBool _, h | .symVar _, .binOp _ _ _, h
  | .symVar _, .unaryOp _ _, h | .symVar _, .ite _ _ _, h | .symVar _, .constU256 _, h
  | .symVar _, .allocTag _, h | .symVar _, .rcSym _ _, h | .symVar _, .ctorTag _ _, h
  | .symVar _, .ctorLen _ _ _, h | .symVar _, .sarrayLen _, h | .symVar _, .mulDiv256 _ _ _ _, h
  | .symVar _, .tuple _, h | .symVar _, .bufElem _ _ _, h | .symVar _, .unit, h => by
    simp [pureSymExprEq] at h
  | .binOp _ _ _, .constU64 _, h | .binOp _ _ _, .constBool _, h | .binOp _ _ _, .symVar _, h
  | .binOp _ _ _, .unaryOp _ _, h | .binOp _ _ _, .ite _ _ _, h | .binOp _ _ _, .constU256 _, h
  | .binOp _ _ _, .allocTag _, h | .binOp _ _ _, .rcSym _ _, h | .binOp _ _ _, .ctorTag _ _, h
  | .binOp _ _ _, .ctorLen _ _ _, h | .binOp _ _ _, .sarrayLen _, h | .binOp _ _ _, .mulDiv256 _ _ _ _, h
  | .binOp _ _ _, .tuple _, h | .binOp _ _ _, .bufElem _ _ _, h | .binOp _ _ _, .unit, h => by
    simp [pureSymExprEq] at h
  | .unaryOp _ _, .constU64 _, h | .unaryOp _ _, .constBool _, h | .unaryOp _ _, .symVar _, h
  | .unaryOp _ _, .binOp _ _ _, h | .unaryOp _ _, .ite _ _ _, h | .unaryOp _ _, .constU256 _, h
  | .unaryOp _ _, .allocTag _, h | .unaryOp _ _, .rcSym _ _, h | .unaryOp _ _, .ctorTag _ _, h
  | .unaryOp _ _, .ctorLen _ _ _, h | .unaryOp _ _, .sarrayLen _, h | .unaryOp _ _, .mulDiv256 _ _ _ _, h
  | .unaryOp _ _, .tuple _, h | .unaryOp _ _, .bufElem _ _ _, h | .unaryOp _ _, .unit, h => by
    simp [pureSymExprEq] at h
  | .ite _ _ _, .constU64 _, h | .ite _ _ _, .constBool _, h | .ite _ _ _, .symVar _, h
  | .ite _ _ _, .binOp _ _ _, h | .ite _ _ _, .unaryOp _ _, h | .ite _ _ _, .constU256 _, h
  | .ite _ _ _, .allocTag _, h | .ite _ _ _, .rcSym _ _, h | .ite _ _ _, .ctorTag _ _, h
  | .ite _ _ _, .ctorLen _ _ _, h | .ite _ _ _, .sarrayLen _, h | .ite _ _ _, .mulDiv256 _ _ _ _, h
  | .ite _ _ _, .tuple _, h | .ite _ _ _, .bufElem _ _ _, h | .ite _ _ _, .unit, h => by
    simp [pureSymExprEq] at h
  | .constU256 _, _, h | .allocTag _, _, h | .rcSym _ _, _, h | .ctorTag _ _, _, h
  | .ctorLen _ _ _, _, h | .sarrayLen _, _, h | .mulDiv256 _ _ _ _, _, h | .tuple _, _, h
  | .bufElem _ _ _, _, h | .unit, _, h => by simp [pureSymExprEq] at h
termination_by s1 => sizeOf s1

theorem varIdListEq_sound (xs ys : List VarId) (h : varIdListEq xs ys = true) :
    xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [varIdListEq] at h; rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp [varIdListEq] at h
    | cons y ys =>
      simp only [varIdListEq, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1, ih ys h.2]

theorem lnirExprEvalEq_sound (env : VarEnv) (st : HeapState) (e1 e2 : LNIRExpr)
    (h : lnirExprEvalEq e1 e2 = true) :
    evalExpr env st e1 = evalExpr env st e2 := by
  cases e1 <;> cases e2 <;> simp only [lnirExprEvalEq, Bool.and_eq_true, beq_iff_eq] at h
  all_goals try contradiction
  case scalar.scalar a b => rw [ScalarExpr_eq_of_beq h]
  case constU256.constU256 a b => rw [h]
  case mulDivDown.mulDivDown => rcases h with ⟨⟨rfl, rfl⟩, rfl⟩; rfl
  case mulDivUp.mulDivUp => rcases h with ⟨⟨rfl, rfl⟩, rfl⟩; rfl
  case storageLoad.storageLoad => rcases h with ⟨rfl, rfl⟩; rfl
  case storageStore.storageStore => rcases h with ⟨⟨rfl, rfl⟩, rfl⟩; rfl
  case mkTuple.mkTuple xs ys => rw [varIdListEq_sound xs ys h]
  case projTuple.projTuple => rcases h with ⟨rfl, rfl⟩; rfl
  case allocCtor.allocCtor tag1 os1 ss1 tag2 os2 ss2 =>
    rcases h with ⟨⟨rfl, hos⟩, hss⟩
    rw [varIdListEq_sound os1 os2 hos, varIdListEq_sound ss1 ss2 hss]
  case ctorGetObj.ctorGetObj => rcases h with ⟨rfl, rfl⟩; rfl
  case ctorGetScalar.ctorGetScalar => rcases h with ⟨rfl, rfl⟩; rfl
  case isExclusive.isExclusive => rw [h]
  case sarrayLen.sarrayLen => rw [h]
  case sarrayDataPtr.sarrayDataPtr => rw [h]; rfl
  case sarrayEnsureExclusive.sarrayEnsureExclusive => rw [h]; rfl
  case sarrayGet.sarrayGet => rcases h with ⟨rfl, rfl⟩; rfl
  case sarraySet.sarraySet => rcases h with ⟨⟨rfl, rfl⟩, rfl⟩; rfl
  case rawLoad.rawLoad => rcases h with ⟨rfl, rfl⟩; rfl
  case boxScalar.boxScalar => rw [h]; rfl
  case unboxScalar.unboxScalar => rw [h]; rfl
  case call.call f1 as1 _ ext1 f2 as2 _ ext2 =>
    rcases h with ⟨⟨rfl, has⟩, rfl⟩
    rw [varIdListEq_sound as1 as2 has]; rfl

theorem parallelKernelEq_sound (k1 k2 : ParallelKernelKind) (h : parallelKernelEq k1 k2 = true) :
    k1 = k2 := by
  cases k1 <;> cases k2 <;> simp only [parallelKernelEq, Bool.and_eq_true, beq_iff_eq] at h
  all_goals try contradiction
  case mapScaleAdd.mapScaleAdd => rcases h with ⟨rfl, rfl⟩; rfl
  case zipAdd.zipAdd => rfl
  case zipMul.zipMul => rfl
  case saxpy.saxpy => rw [h]
  case dotProduct.dotProduct => rfl
  case stencil1D3Pt.stencil1D3Pt => rcases h with ⟨⟨rfl, rfl⟩, rfl⟩; rfl
  case customScalar.customScalar idx1 ins1 b1 idx2 ins2 b2 =>
    rcases h with ⟨⟨rfl, hins⟩, hb⟩
    rw [varIdListEq_sound ins1 ins2 hins, ScalarExpr_eq_of_beq hb]

/-- Semantic invariant relating concrete `VarEnv` to `SymRefinesCtx`. -/
def CtxHolds (ctx : SymRefinesCtx) (env : VarEnv) : Prop :=
  (∀ v, ctx.boundVars.contains v = true → ∃ val, env v = some val) ∧
  (∀ v, ctx.u64Vars.contains v = true → ∃ n : UInt64, env v = some (.u64 n)) ∧
  (∀ kv, kv ∈ ctx.constU64 → env kv.1 = some (.u64 kv.2)) ∧
  (∀ kv, kv ∈ ctx.constBool → env kv.1 = some (.bool kv.2)) ∧
  (∀ tf, tf ∈ ctx.tuples → ∃ vals : List Val,
    env tf.1 = some (.tuple vals) ∧ evalVarList env tf.2 = .ok vals)

theorem CtxHolds.empty (env : VarEnv) : CtxHolds {} env := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro _ h; simp at h
  · intro _ h; simp at h
  · intro _ h; simp at h
  · intro _ h; simp at h
  · intro _ h; simp at h

theorem findConstU64_mem (v : VarId) (n : UInt64) (xs : List (VarId × UInt64)) :
    findConstU64 v xs = some n → (v, n) ∈ xs := by
  induction xs with
  | nil => simp [findConstU64]
  | cons kv rest ih =>
    rcases kv with ⟨k, val⟩
    simp only [findConstU64]
    split
    · rename_i hkv; rw [beq_iff_eq] at hkv; subst hkv
      intro h
      injection h with hval
      subst hval
      exact List.mem_cons_self ..
    · intro h; exact List.mem_cons_of_mem _ (ih h)

theorem findConstBool_mem (v : VarId) (b : Bool) (xs : List (VarId × Bool)) :
    findConstBool v xs = some b → (v, b) ∈ xs := by
  induction xs with
  | nil => simp [findConstBool]
  | cons kv rest ih =>
    rcases kv with ⟨k, val⟩
    simp only [findConstBool]
    split
    · rename_i hkv; rw [beq_iff_eq] at hkv; subst hkv
      intro h
      injection h with hval
      subst hval
      exact List.mem_cons_self ..
    · intro h; exact List.mem_cons_of_mem _ (ih h)

theorem findTupleField_mem (tVar : VarId) (idx : Nat) (fVar : VarId)
    (xs : List (VarId × List VarId)) :
    findTupleField tVar idx xs = some fVar →
    ∃ fs, (tVar, fs) ∈ xs ∧ fs[idx]? = some fVar := by
  induction xs with
  | nil => simp [findTupleField]
  | cons kv rest ih =>
    rcases kv with ⟨k, fs⟩
    simp only [findTupleField]
    split
    · rename_i hkt; rw [beq_iff_eq] at hkt; subst hkt
      intro h; exact ⟨fs, List.mem_cons_self .., h⟩
    · intro h
      rcases ih h with ⟨fs', hmem, hidx⟩
      exact ⟨fs', List.mem_cons_of_mem _ hmem, hidx⟩

theorem filterOutVarId_contains (dst v : VarId) (xs : List VarId) :
    (filterOutVarId dst xs).contains v = true → v ≠ dst ∧ xs.contains v = true := by
  induction xs with
  | nil => simp [filterOutVarId]
  | cons x rest ih =>
    simp only [filterOutVarId]
    split
    · intro h
      rcases ih h with ⟨hne, hmem⟩
      exact ⟨hne, by rw [List.contains_cons, hmem, Bool.or_true]⟩
    · rename_i hxd
      rw [List.contains_cons, Bool.or_eq_true, beq_iff_eq]
      rintro (rfl | hr)
      · exact ⟨fun hveq => hxd (beq_iff_eq.mpr hveq),
          by rw [List.contains_cons, beq_self_eq_true, Bool.true_or]⟩
      · rcases ih hr with ⟨hne, hmem⟩
        exact ⟨hne, by rw [List.contains_cons, hmem, Bool.or_true]⟩

theorem filterOutConstU64_mem (dst : VarId) (kv : VarId × UInt64)
    (xs : List (VarId × UInt64)) :
    kv ∈ filterOutConstU64 dst xs → kv.1 ≠ dst ∧ kv ∈ xs := by
  induction xs with
  | nil => simp [filterOutConstU64]
  | cons x rest ih =>
    rcases x with ⟨k, val⟩
    simp only [filterOutConstU64]
    split
    · intro h; exact ⟨(ih h).1, List.mem_cons_of_mem _ (ih h).2⟩
    · rename_i hkd
      rw [List.mem_cons]
      rintro (rfl | hr)
      · exact ⟨fun heq => hkd (beq_iff_eq.mpr heq), List.mem_cons_self ..⟩
      · exact ⟨(ih hr).1, List.mem_cons_of_mem _ (ih hr).2⟩

theorem filterOutConstBool_mem (dst : VarId) (kv : VarId × Bool)
    (xs : List (VarId × Bool)) :
    kv ∈ filterOutConstBool dst xs → kv.1 ≠ dst ∧ kv ∈ xs := by
  induction xs with
  | nil => simp [filterOutConstBool]
  | cons x rest ih =>
    rcases x with ⟨k, val⟩
    simp only [filterOutConstBool]
    split
    · intro h; exact ⟨(ih h).1, List.mem_cons_of_mem _ (ih h).2⟩
    · rename_i hkd
      rw [List.mem_cons]
      rintro (rfl | hr)
      · exact ⟨fun heq => hkd (beq_iff_eq.mpr heq), List.mem_cons_self ..⟩
      · exact ⟨(ih hr).1, List.mem_cons_of_mem _ (ih hr).2⟩

theorem dropClobberedTuples_mem (dst : VarId) (tf : VarId × List VarId)
    (xs : List (VarId × List VarId)) :
    tf ∈ dropClobberedTuples dst xs →
    tf.1 ≠ dst ∧ tf.2.contains dst = false ∧ tf ∈ xs := by
  induction xs with
  | nil => simp [dropClobberedTuples]
  | cons x rest ih =>
    rcases x with ⟨tVar, fs⟩
    simp only [dropClobberedTuples]
    split
    · intro h
      rcases ih h with ⟨h1, h2, h3⟩
      exact ⟨h1, h2, List.mem_cons_of_mem _ h3⟩
    · rename_i hnot
      simp only [Bool.or_eq_true, not_or] at hnot
      rw [List.mem_cons]
      rintro (rfl | hr)
      · refine ⟨fun heq => hnot.1 (beq_iff_eq.mpr heq), ?_, List.mem_cons_self ..⟩
        cases hfc : fs.contains dst
        · rfl
        · exact False.elim (hnot.2 hfc)
      · rcases ih hr with ⟨h1, h2, h3⟩
        exact ⟨h1, h2, List.mem_cons_of_mem _ h3⟩

theorem evalVarList_bind_not_contains (env : VarEnv) (dst : VarId) (val : Val) (fs : List VarId)
    (hnc : fs.contains dst = false) :
    evalVarList (env.bind dst val) fs = evalVarList env fs := by
  induction fs with
  | nil => rfl
  | cons f rest ih =>
    simp only [List.contains_cons, Bool.or_eq_false_iff] at hnc
    have hne : (f == dst) = false := by
      cases hfd : (f == dst)
      · rfl
      · rw [beq_iff_eq] at hfd; subst hfd; simp at hnc
    simp only [evalVarList, VarEnv.bind_ne env dst f val hne, ih hnc.2]

theorem CtxHolds.killVar_bind {ctx : SymRefinesCtx} {env : VarEnv}
    (hctx : CtxHolds ctx env) (dst : VarId) (val : Val) :
    CtxHolds (ctx.killVar dst) (env.bind dst val) := by
  rcases hctx with ⟨hb, hu, hc64, hcb, htup⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rcases filterOutVarId_contains dst v ctx.boundVars hv with ⟨hne, hv'⟩
    rw [VarEnv.bind_ne env dst v val (beq_eq_false_iff_ne.mpr hne)]
    exact hb v hv'
  · intro v hv
    rcases filterOutVarId_contains dst v ctx.u64Vars hv with ⟨hne, hv'⟩
    rw [VarEnv.bind_ne env dst v val (beq_eq_false_iff_ne.mpr hne)]
    exact hu v hv'
  · intro kv hkv
    rcases filterOutConstU64_mem dst kv ctx.constU64 hkv with ⟨hne, hkv'⟩
    rw [VarEnv.bind_ne env dst kv.1 val (beq_eq_false_iff_ne.mpr hne)]
    exact hc64 kv hkv'
  · intro kv hkv
    rcases filterOutConstBool_mem dst kv ctx.constBool hkv with ⟨hne, hkv'⟩
    rw [VarEnv.bind_ne env dst kv.1 val (beq_eq_false_iff_ne.mpr hne)]
    exact hcb kv hkv'
  · intro tf htf
    rcases dropClobberedTuples_mem dst tf ctx.tuples htf with ⟨hne, hnc, htf'⟩
    rcases htup tf htf' with ⟨vals, htv, hevl⟩
    refine ⟨vals, ?_, ?_⟩
    · rw [VarEnv.bind_ne env dst tf.1 val (beq_eq_false_iff_ne.mpr hne)]
      exact htv
    · rw [evalVarList_bind_not_contains env dst val tf.2 hnc]
      exact hevl

theorem CtxHolds.addBound_of_some {ctx : SymRefinesCtx} {env : VarEnv}
    (hctx : CtxHolds ctx env) (v : VarId) (val : Val) (hv : env v = some val) :
    CtxHolds (ctx.addBound v) env := by
  unfold SymRefinesCtx.addBound
  split
  · exact hctx
  · refine ⟨?_, hctx.2.1, hctx.2.2.1, hctx.2.2.2.1, hctx.2.2.2.2⟩
    intro x hx
    rw [List.contains_cons, Bool.or_eq_true, beq_iff_eq] at hx
    rcases hx with rfl | hx'
    · exact ⟨val, hv⟩
    · exact hctx.1 x hx'

theorem CtxHolds.addU64_of_u64 {ctx : SymRefinesCtx} {env : VarEnv}
    (hctx : CtxHolds ctx env) (v : VarId) (n : UInt64) (hv : env v = some (.u64 n)) :
    CtxHolds (ctx.addU64 v) env := by
  unfold SymRefinesCtx.addU64
  dsimp only
  have h1 := hctx.addBound_of_some v (.u64 n) hv
  split
  · exact h1
  · refine ⟨h1.1, ?_, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2⟩
    intro x hx
    rw [List.contains_cons, Bool.or_eq_true, beq_iff_eq] at hx
    rcases hx with rfl | hx'
    · exact ⟨n, hv⟩
    · exact h1.2.1 x hx'

theorem CtxHolds.addBoundVars_of_evalVarList {ctx : SymRefinesCtx} {env : VarEnv}
    (hctx : CtxHolds ctx env) (vs : List VarId) (vals : List Val)
    (hevl : evalVarList env vs = .ok vals) :
    CtxHolds (ctx.addBoundVars vs) env := by
  induction vs generalizing ctx vals with
  | nil => exact hctx
  | cons x rest ih =>
    simp only [evalVarList] at hevl
    cases hx : env x with
    | none => simp [hx] at hevl
    | some vx =>
      rw [hx] at hevl
      cases hrest : evalVarList env rest with
      | error _ => simp [hrest] at hevl
      | ok vrest =>
        exact ih (hctx.addBound_of_some x vx hx) vrest hrest

theorem substKnownConsts_eq {ctx : SymRefinesCtx} {env : VarEnv}
    (hctx : CtxHolds ctx env) (e : ScalarExpr) :
    evalScalarExpr env (substKnownConsts ctx e) = evalScalarExpr env e := by
  induction e with
  | constU64 _ | constBool _ => rfl
  | var id =>
    simp only [substKnownConsts]
    cases hu : findConstU64 id ctx.constU64 with
    | some n =>
      have hm := findConstU64_mem id n ctx.constU64 hu
      simp [evalScalarExpr, hctx.2.2.1 (id, n) hm]
    | none =>
      cases hb : findConstBool id ctx.constBool with
      | some b =>
        have hm := findConstBool_mem id b ctx.constBool hb
        simp [evalScalarExpr, hctx.2.2.2.1 (id, b) hm]
      | none => rfl
  | binOp op l r ihl ihr =>
    simp only [substKnownConsts, evalScalarExpr, ihl, ihr]
  | unaryOp op a iha =>
    simp only [substKnownConsts, evalScalarExpr, iha]
  | select c t f ihc iht ihf =>
    simp only [substKnownConsts, evalScalarExpr, ihc, iht, ihf]
  | fma a b c iha ihb ihc =>
    simp only [substKnownConsts, evalScalarExpr, iha, ihb, ihc]

theorem expandFmaScalar_eq (env : VarEnv) (e : ScalarExpr) :
    evalScalarExpr env (expandFmaScalar e) = evalScalarExpr env e := by
  induction e with
  | constU64 _ | constBool _ | var _ => rfl
  | binOp op l r ihl ihr =>
    simp only [expandFmaScalar, evalScalarExpr, ihl, ihr]
  | unaryOp op a iha =>
    simp only [expandFmaScalar, evalScalarExpr, iha]
  | select c t f ihc iht ihf =>
    simp only [expandFmaScalar, evalScalarExpr, ihc, iht, ihf]
  | fma a b c iha ihb ihc =>
    simp only [expandFmaScalar, evalScalarExpr, iha, ihb, ihc]
    cases evalScalarExpr env a with
    | error _ => rfl
    | ok va =>
      cases evalScalarExpr env b with
      | error _ => rfl
      | ok vb =>
        cases evalScalarExpr env c with
        | error _ =>
          cases evalBinOp .mul va vb <;> rfl
        | ok vc => rfl

theorem forcedU64VarsOfScalar_mem_sound (e : ScalarExpr) (env : VarEnv) (val : Val)
    (heval : evalScalarExpr env e = .ok val) (id : VarId)
    (hmem : (forcedU64VarsOfScalar e).contains id = true) :
    ∃ n : UInt64, env id = some (.u64 n) := by
  rw [List.contains_iff_mem] at hmem
  simp only [forcedU64VarsOfScalar, List.mem_filter] at hmem
  exact varForcedU64_sound id e env val hmem.2 heval

theorem addForcedVars_sound_aux {ctx : SymRefinesCtx} {env : VarEnv}
    (hctx : CtxHolds ctx env) (vs : List VarId)
    (hvs : ∀ id ∈ vs, ∃ n : UInt64, env id = some (.u64 n)) :
    CtxHolds (ctx.addForcedVars vs) env := by
  induction vs generalizing ctx with
  | nil => exact hctx
  | cons v rest ih =>
    obtain ⟨n, hn⟩ := hvs v (List.mem_cons_self ..)
    exact ih (hctx.addU64_of_u64 v n hn)
      (fun id hid => hvs id (List.mem_cons_of_mem _ hid))

theorem addForcedVars_contains_u64 (ctx : SymRefinesCtx) (vs : List VarId) (id : VarId)
    (h : (unionVars ctx.u64Vars vs).contains id = true) :
    (ctx.addForcedVars vs).u64Vars.contains id = true := by
  rw [List.contains_iff_mem] at h ⊢
  simp only [unionVars, List.mem_append, List.mem_filter] at h
  have hpres : ∀ (c : SymRefinesCtx) (ws : List VarId) (x : VarId),
      x ∈ c.u64Vars → x ∈ (c.addForcedVars ws).u64Vars := by
    intro c ws x hx
    induction ws generalizing c with
    | nil => exact hx
    | cons w rest ih =>
      apply ih
      unfold SymRefinesCtx.addU64
      dsimp only [SymRefinesCtx.addBound]
      split
      · split
        · exact hx
        · exact List.mem_cons_of_mem _ hx
      · split
        · exact hx
        · exact List.mem_cons_of_mem _ hx
  have hin : ∀ (c : SymRefinesCtx) (ws : List VarId) (x : VarId),
      x ∈ ws → x ∈ (c.addForcedVars ws).u64Vars := by
    intro c ws x hx
    induction ws generalizing c with
    | nil => nomatch hx
    | cons w rest ih =>
      rw [List.mem_cons] at hx
      rcases hx with rfl | hrest
      · apply hpres (c.addU64 x) rest x
        unfold SymRefinesCtx.addU64 SymRefinesCtx.addBound
        dsimp only
        split
        · split
          · rename_i hcu; exact List.contains_iff_mem.mp hcu
          · exact List.mem_cons_self ..
        · split
          · rename_i hcu; exact List.contains_iff_mem.mp hcu
          · exact List.mem_cons_self ..
      · exact ih _ hrest
  rcases h with h1 | ⟨h2, _⟩
  · exact hpres ctx vs id h1
  · exact hin ctx vs id h2

theorem symbolicScalarRefines_sound {ctx : SymRefinesCtx} {env : VarEnv}
    (hctx : CtxHolds ctx env) (eSrc eTgt : ScalarExpr) (val : Val)
    (href : symbolicScalarRefines ctx eSrc eTgt = true)
    (hsrc : evalScalarExpr env eSrc = .ok val) :
    evalScalarExpr env eTgt = .ok val := by
  let sSrc := expandFmaScalar (substKnownConsts ctx eSrc)
  let sTgt := expandFmaScalar (substKnownConsts ctx eTgt)
  have heqS : evalScalarExpr env sSrc = .ok val := by
    simp only [sSrc, expandFmaScalar_eq, substKnownConsts_eq hctx, hsrc]
  have heqT : evalScalarExpr env eTgt = evalScalarExpr env sTgt := by
    simp only [sTgt, expandFmaScalar_eq, substKnownConsts_eq hctx]
  rw [heqT]
  change (
    (sSrc == sTgt) ||
    (rewriteScalarVerified sSrc == rewriteScalarVerified sTgt) ||
    (contractKernelScalar sSrc == contractKernelScalar sTgt) ||
    (let u64s := unionVars ctx.u64Vars (forcedU64VarsOfScalar sSrc)
     isPureU64ScalarExpr sSrc && isPureU64ScalarExpr sTgt &&
     isPureU64SymExprIn u64s (scalarToSymExpr sSrc) &&
     isPureU64SymExprIn u64s (scalarToSymExpr sTgt) &&
     pureSymExprEq (normSymExpr (scalarToSymExpr sSrc))
       (normSymExpr (scalarToSymExpr sTgt)))) = true at href
  dsimp only at href
  simp only [Bool.or_eq_true, Bool.and_eq_true] at href
  rcases href with ((h1 | h2) | h3) | ⟨⟨⟨⟨hpS, hpT⟩, hinS⟩, hinT⟩, hnorm⟩
  · rw [← ScalarExpr_eq_of_beq h1]; exact heqS
  · have hrS := rewriteScalarVerified_sound sSrc env
    have hrT := rewriteScalarVerified_sound sTgt env
    rw [hrT, ← ScalarExpr_eq_of_beq h2, ← hrS, heqS]
  · have hcS := contractKernelScalar_sound sSrc env
    have hcT := contractKernelScalar_sound sTgt env
    rw [hcT, ← ScalarExpr_eq_of_beq h3, ← hcS, heqS]
  · let u64s := unionVars ctx.u64Vars (forcedU64VarsOfScalar sSrc)
    have hvars : ∀ id : VarId, u64s.contains id = true →
        ∃ n : UInt64, (SymValuation.ofVarEnv env).varVal id = some (.u64 n) := by
      intro id hid
      rw [List.contains_iff_mem] at hid
      simp only [u64s, unionVars, List.mem_append, List.mem_filter] at hid
      rcases hid with h1 | ⟨h2, _⟩
      · exact hctx.2.1 id (List.contains_iff_mem.mpr h1)
      · exact forcedU64VarsOfScalar_mem_sound sSrc env val heqS id (List.contains_iff_mem.mpr h2)
    have hdenS := scalarToSymExpr_denotes env sSrc hpS
    have hdenT := scalarToSymExpr_denotes env sTgt hpT
    obtain ⟨nS, hdS, hdnS⟩ :=
      normSymExpr_pureU64_denotes u64s (SymValuation.ofVarEnv env) (scalarToSymExpr sSrc) hinS hvars
    obtain ⟨nT, hdT, hdnT⟩ :=
      normSymExpr_pureU64_denotes u64s (SymValuation.ofVarEnv env) (scalarToSymExpr sTgt) hinT hvars
    have hnormEq := pureSymExprEq_sound _ _ hnorm
    rw [hdenS, heqS] at hdS
    rw [hnormEq, hdnT] at hdnS
    injection hdnS with hnEq
    rw [← hdenT, hdT, hnEq, ← hdS]

theorem CtxHolds.afterScalarLet_sound {ctx : SymRefinesCtx} {env : VarEnv}
    (hctx : CtxHolds ctx env) (dst : VarId) (eSrc : ScalarExpr) (val : Val)
    (hsrc : evalScalarExpr env eSrc = .ok val) :
    CtxHolds (ctx.afterScalarLet dst eSrc) (env.bind dst val) := by
  let sSrc := expandFmaScalar (substKnownConsts ctx eSrc)
  have heqS : evalScalarExpr env sSrc = .ok val := by
    simp only [sSrc, expandFmaScalar_eq, substKnownConsts_eq hctx, hsrc]
  have hforced : CtxHolds (ctx.addForcedVars (forcedU64VarsOfScalar sSrc)) env :=
    addForcedVars_sound_aux hctx _ fun id hid =>
      forcedU64VarsOfScalar_mem_sound sSrc env val heqS id (List.contains_iff_mem.mpr hid)
  have hkilled : CtxHolds (((ctx.addForcedVars (forcedU64VarsOfScalar sSrc)).killVar dst).addBound dst)
      (env.bind dst val) :=
    (hforced.killVar_bind dst val).addBound_of_some dst val (VarEnv.bind_self env dst val)
  change CtxHolds (
    let ctxForced := ctx.addForcedVars (forcedU64VarsOfScalar sSrc)
    let isDstU64 :=
      isPureU64ScalarExpr sSrc &&
      isPureU64SymExprIn ctxForced.u64Vars (scalarToSymExpr sSrc)
    let ctxKilled := (ctxForced.killVar dst).addBound dst
    match rewriteScalarVerified sSrc with
    | .constU64 n =>
      { ctxKilled with
        u64Vars := if ctxKilled.u64Vars.contains dst then ctxKilled.u64Vars else dst :: ctxKilled.u64Vars
        constU64 := (dst, n) :: ctxKilled.constU64 }
    | .constBool b =>
      { ctxKilled with
        constBool := (dst, b) :: ctxKilled.constBool }
    | _ =>
      if isDstU64 then ctxKilled.addU64 dst else ctxKilled) (env.bind dst val)
  dsimp only
  have hrw := rewriteScalarVerified_sound sSrc env
  generalize hr : rewriteScalarVerified sSrc = rwExpr at hrw ⊢
  cases rwExpr with
  | constU64 n =>
    dsimp only
    rw [heqS] at hrw
    simp only [evalScalarExpr] at hrw
    injection hrw with hval; subst hval
    refine ⟨hkilled.1, ?_, ?_, hkilled.2.2.2.1, hkilled.2.2.2.2⟩
    · intro x hx
      dsimp only at hx
      split at hx
      · exact hkilled.2.1 x hx
      · rw [List.contains_cons, Bool.or_eq_true, beq_iff_eq] at hx
        rcases hx with hxd | hx'
        · rw [hxd]; exact ⟨n, VarEnv.bind_self env dst (.u64 n)⟩
        · exact hkilled.2.1 x hx'
    · intro kv hkv
      dsimp only at hkv
      rw [List.mem_cons] at hkv
      rcases hkv with rfl | hkv'
      · exact VarEnv.bind_self env dst (.u64 n)
      · exact hkilled.2.2.1 kv hkv'
  | constBool b =>
    dsimp only
    rw [heqS] at hrw
    simp only [evalScalarExpr] at hrw
    injection hrw with hval; subst hval
    refine ⟨hkilled.1, hkilled.2.1, hkilled.2.2.1, ?_, hkilled.2.2.2.2⟩
    intro kv hkv
    dsimp only at hkv
    rw [List.mem_cons] at hkv
    rcases hkv with rfl | hkv'
    · exact VarEnv.bind_self env dst (.bool b)
    · exact hkilled.2.2.2.1 kv hkv'
  | var _ | binOp _ _ _ | unaryOp _ _ | select _ _ _ | fma _ _ _ =>
    dsimp only
    cases hisU64 :
        (isPureU64ScalarExpr sSrc &&
          isPureU64SymExprIn (ctx.addForcedVars (forcedU64VarsOfScalar sSrc)).u64Vars
            (scalarToSymExpr sSrc))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact hkilled
    · simp only [↓reduceIte]
      simp only [Bool.and_eq_true] at hisU64
      rcases hisU64 with ⟨hpS, hinS⟩
      obtain ⟨nS, hdS, _⟩ :=
        normSymExpr_pureU64_denotes _ (SymValuation.ofVarEnv env)
          (scalarToSymExpr sSrc) hinS (fun id hid => hforced.2.1 id hid)
      rw [scalarToSymExpr_denotes env sSrc hpS, heqS] at hdS
      injection hdS with hval; subst hval
      exact hkilled.addU64_of_u64 dst nS (VarEnv.bind_self env dst (.u64 nS))

end LeanNative.Proofs
