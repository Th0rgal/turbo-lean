import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.Proofs.PeepholeProofs
import LeanNative.Transform.KernelFusion

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Transform

/-! ## C8 Deliverable 1 Soundness Proofs: Intra-Kernel Specialization & Producer-Consumer `parFor` Fusion

Zero `import Lean`, zero `sorryAx`, standard axioms only (`propext`, `Quot.sound`, `Classical.choice`).
-/

/-! ### 1. Verified Scalar Contraction (`contractKernelScalar_sound`) -/

/-- Single-step FMA contraction preserves `evalScalarExpr` on all `Val`s. -/
theorem contractKernelScalarStep_sound (e : ScalarExpr) :
    ScalarExprEquiv e (contractKernelScalarStep e) := by
  intro env
  cases e with
  | constU64 _ | constBool _ | var _ | unaryOp _ _ | select _ _ _ | fma _ _ _ => rfl
  | binOp op lhs rhs =>
    cases op with
    | add =>
      cases lhs with
      | constU64 _ | constBool _ | var _ | unaryOp _ _ | select _ _ _ | fma _ _ _ => rfl
      | binOp op2 a b =>
        cases op2 with
        | mul =>
          simp only [contractKernelScalarStep, evalScalarExpr]
          cases evalScalarExpr env a with
          | error _ => rfl
          | ok va =>
            cases evalScalarExpr env b with
            | error _ => rfl
            | ok vb =>
              cases evalBinOp .mul va vb <;> cases evalScalarExpr env rhs <;> rfl
        | add | sub | div | mod | bitAnd | bitOr | bitXor | shl | shr | sar
        | eq | lt | le | addChecked256 | subChecked256 | mulChecked256
        | clmul64 | clmul64Hi | gf2Affine | eor3 => rfl
    | sub | mul | div | mod | bitAnd | bitOr | bitXor | shl | shr | sar
    | eq | lt | le | addChecked256 | subChecked256 | mulChecked256
    | clmul64 | clmul64Hi | gf2Affine | eor3 => rfl

/-- Recursive scalar simplifier & FMA contractor preserves `evalScalarExpr` unconditionally. -/
theorem contractKernelScalar_sound (e : ScalarExpr) :
    ScalarExprEquiv e (contractKernelScalar e) := by
  induction e with
  | constU64 _ | constBool _ | var _ => exact ScalarExprEquiv.refl _
  | unaryOp op a ih =>
    intro env; simp only [contractKernelScalar]; rw [← contractKernelScalarStep_sound _ env]
    simp only [evalScalarExpr, ih env]
  | binOp op l r ihl ihr =>
    intro env; simp only [contractKernelScalar]; rw [← contractKernelScalarStep_sound _ env]
    rw [← rewriteConstFoldStep_sound _ env, ← rewriteScalarPeepholeStep_sound _ env]
    simp only [evalScalarExpr, ihl env, ihr env]
  | select c t f ihc iht ihf =>
    intro env; simp only [contractKernelScalar]; rw [← contractKernelScalarStep_sound _ env]
    rw [← rewriteSelectStep_sound _ _ _ env]; simp only [evalScalarExpr, ihc env, iht env, ihf env]
  | fma a b c iha ihb ihc =>
    intro env; simp only [contractKernelScalar]; rw [← contractKernelScalarStep_sound _ env]
    simp only [evalScalarExpr, iha env, ihb env, ihc env]

/-! ### 2. Intra-Kernel Specialization (`specializeKernelCode_refines`) -/

private theorem matchBuiltinKernel1_elem_eq
    (env : VarEnv) (st : HeapState) (inputs : List VarId) (len : Nat)
    (idxVar x : VarId) (body : ScalarExpr) (k : ParallelKernelKind) (i : Nat)
    (hm : matchBuiltinKernel1 x body = some k) :
    evalParKernelElem env st inputs len (.customScalar idxVar [x] body) i =
    evalParKernelElem env st inputs len k i ∧ k ≠ .dotProduct := by
  cases body with
  | constU64 _ | constBool _ | unaryOp _ _ | select _ _ _ => cases hm
  | var x' =>
    by_cases hx : x' = x
    · subst hx; simp only [matchBuiltinKernel1, ↓reduceIte, Option.some.injEq] at hm; subst hm
      refine ⟨?_, nofun⟩; simp only [evalParKernelElem, bindCustomParInputs]
      cases readParInput env st inputs 0 i with
      | error _ => rfl
      | ok vx =>
        simp only [evalScalarExpr, VarEnv.bind, beq_self_eq_true, ↓reduceIte]
        exact congrArg Except.ok (by rw [UInt64.mul_one, UInt64.add_zero])
    · simp only [matchBuiltinKernel1, hx, ↓reduceIte] at hm; cases hm
  | fma a b c =>
    cases a with
    | var x' =>
      cases b with
      | constU64 scale =>
        cases c with
        | constU64 bias =>
          by_cases hx : x' = x
          · subst hx; simp only [matchBuiltinKernel1, ↓reduceIte, Option.some.injEq] at hm; subst hm
            refine ⟨?_, nofun⟩; simp only [evalParKernelElem, bindCustomParInputs]
            cases readParInput env st inputs 0 i with
            | error _ => rfl
            | ok vx => simp only [evalScalarExpr, VarEnv.bind, beq_self_eq_true, ↓reduceIte]; rfl
          · simp only [matchBuiltinKernel1, hx, ↓reduceIte] at hm; cases hm
        | constBool _ | var _ | binOp _ _ _ | unaryOp _ _ | select _ _ _ | fma _ _ _ => cases hm
      | constBool _ | var _ | binOp _ _ _ | unaryOp _ _ | select _ _ _ | fma _ _ _ => cases hm
    | constU64 _ | constBool _ | binOp _ _ _ | unaryOp _ _ | select _ _ _ | fma _ _ _ => cases hm
  | binOp op lhs rhs =>
    cases op with
    | mul =>
      cases lhs with
      | var x' =>
        cases rhs with
        | constU64 scale =>
          by_cases hx : x' = x
          · subst hx; simp only [matchBuiltinKernel1, ↓reduceIte, Option.some.injEq] at hm; subst hm
            refine ⟨?_, nofun⟩; simp only [evalParKernelElem, bindCustomParInputs]
            cases readParInput env st inputs 0 i with
            | error _ => rfl
            | ok vx =>
              simp only [evalScalarExpr, VarEnv.bind, beq_self_eq_true, ↓reduceIte]
              exact congrArg Except.ok (UInt64.add_zero (vx * scale)).symm
          · simp only [matchBuiltinKernel1, hx, ↓reduceIte] at hm; cases hm
        | constBool _ | var _ | binOp _ _ _ | unaryOp _ _ | select _ _ _ | fma _ _ _ => cases hm
      | constU64 _ | constBool _ | binOp _ _ _ | unaryOp _ _ | select _ _ _ | fma _ _ _ => cases hm
    | add =>
      cases rhs with
      | constU64 bias =>
        cases lhs with
        | var x' =>
          by_cases hx : x' = x
          · subst hx; simp only [matchBuiltinKernel1, ↓reduceIte, Option.some.injEq] at hm; subst hm
            refine ⟨?_, nofun⟩; simp only [evalParKernelElem, bindCustomParInputs]
            cases readParInput env st inputs 0 i with
            | error _ => rfl
            | ok vx =>
              simp only [evalScalarExpr, VarEnv.bind, beq_self_eq_true, ↓reduceIte]
              change Except.ok (vx + bias) = Except.ok (vx * 1 + bias)
              exact congrArg Except.ok (by rw [UInt64.mul_one])
          · simp only [matchBuiltinKernel1, hx, ↓reduceIte] at hm; cases hm
        | binOp op2 a2 b2 =>
          cases op2 with
          | mul =>
            cases a2 with
            | var x' =>
              cases b2 with
              | constU64 scale =>
                by_cases hx : x' = x
                · subst hx; simp only [matchBuiltinKernel1, ↓reduceIte, Option.some.injEq] at hm; subst hm
                  refine ⟨?_, nofun⟩; simp only [evalParKernelElem, bindCustomParInputs]
                  cases readParInput env st inputs 0 i with
                  | error _ => rfl
                  | ok vx => simp only [evalScalarExpr, VarEnv.bind, beq_self_eq_true, ↓reduceIte]; rfl
                · simp only [matchBuiltinKernel1, hx, ↓reduceIte] at hm; cases hm
              | constBool _ | var _ | binOp _ _ _ | unaryOp _ _ | select _ _ _ | fma _ _ _ => cases hm
            | constU64 _ | constBool _ | binOp _ _ _ | unaryOp _ _ | select _ _ _ | fma _ _ _ => cases hm
          | add | sub | div | mod | bitAnd | bitOr | bitXor | shl | shr | sar | eq | lt | le
          | addChecked256 | subChecked256 | mulChecked256 | clmul64 | clmul64Hi | gf2Affine | eor3 => cases hm
        | constU64 _ | constBool _ | unaryOp _ _ | select _ _ _ | fma _ _ _ => cases hm
      | constBool _ | var _ | binOp _ _ _ | unaryOp _ _ | select _ _ _ | fma _ _ _ => cases hm
    | sub | div | mod | bitAnd | bitOr | bitXor | shl | shr | sar | eq | lt | le
    | addChecked256 | subChecked256 | mulChecked256 | clmul64 | clmul64Hi | gf2Affine | eor3 => cases hm

private theorem matchBuiltinKernel2_elem_eq
    (env : VarEnv) (st : HeapState) (inputs : List VarId) (len : Nat)
    (idxVar x y : VarId) (body : ScalarExpr) (k : ParallelKernelKind) (i : Nat)
    (hxy : x ≠ y)
    (hm : matchBuiltinKernel2 x y body = some k) :
    evalParKernelElem env st inputs len (.customScalar idxVar [x, y] body) i =
    evalParKernelElem env st inputs len k i ∧ k ≠ .dotProduct := by
  have hyx_beq : (x == y) = false := beq_false_of_ne hxy
  cases body with
  | constU64 _ | constBool _ | var _ | unaryOp _ _ | select _ _ _ => cases hm
  | fma a b c =>
    cases a with
    | constU64 alpha =>
      cases b with
      | var x' =>
        cases c with
        | var y' =>
          by_cases hcond : x' = x ∧ y' = y
          · rcases hcond with ⟨rfl, rfl⟩
            simp only [matchBuiltinKernel2, and_self, ↓reduceIte, Option.some.injEq] at hm; subst hm
            refine ⟨?_, nofun⟩; simp only [evalParKernelElem, bindCustomParInputs]
            cases readParInput env st inputs 0 i with
            | error _ => rfl
            | ok vx =>
              cases readParInput env st inputs 1 i with
              | error _ => rfl
              | ok vy => simp only [evalScalarExpr, VarEnv.bind, hyx_beq, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]; rfl
          · simp only [matchBuiltinKernel2, hcond, ↓reduceIte] at hm; cases hm
        | constU64 _ | constBool _ | binOp _ _ _ | unaryOp _ _ | select _ _ _ | fma _ _ _ => cases hm
      | constU64 _ | constBool _ | binOp _ _ _ | unaryOp _ _ | select _ _ _ | fma _ _ _ => cases hm
    | constBool _ | var _ | binOp _ _ _ | unaryOp _ _ | select _ _ _ | fma _ _ _ => cases hm
  | binOp op lhs rhs =>
    cases op with
    | mul =>
      cases lhs with
      | var x' =>
        cases rhs with
        | var y' =>
          by_cases hcond : x' = x ∧ y' = y
          · rcases hcond with ⟨rfl, rfl⟩
            simp only [matchBuiltinKernel2, and_self, ↓reduceIte, Option.some.injEq] at hm; subst hm
            refine ⟨?_, nofun⟩; simp only [evalParKernelElem, bindCustomParInputs]
            cases readParInput env st inputs 0 i with
            | error _ => rfl
            | ok vx =>
              cases readParInput env st inputs 1 i with
              | error _ => rfl
              | ok vy => simp only [evalScalarExpr, VarEnv.bind, hyx_beq, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]; rfl
          · simp only [matchBuiltinKernel2, hcond, ↓reduceIte] at hm; cases hm
        | constU64 _ | constBool _ | binOp _ _ _ | unaryOp _ _ | select _ _ _ | fma _ _ _ => cases hm
      | constU64 _ | constBool _ | binOp _ _ _ | unaryOp _ _ | select _ _ _ | fma _ _ _ => cases hm
    | add =>
      cases rhs with
      | var y' =>
        cases lhs with
        | var x' =>
          by_cases hcond : x' = x ∧ y' = y
          · rcases hcond with ⟨rfl, rfl⟩
            simp only [matchBuiltinKernel2, and_self, ↓reduceIte, Option.some.injEq] at hm; subst hm
            refine ⟨?_, nofun⟩; simp only [evalParKernelElem, bindCustomParInputs]
            cases readParInput env st inputs 0 i with
            | error _ => rfl
            | ok vx =>
              cases readParInput env st inputs 1 i with
              | error _ => rfl
              | ok vy => simp only [evalScalarExpr, VarEnv.bind, hyx_beq, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]; rfl
          · simp only [matchBuiltinKernel2, hcond, ↓reduceIte] at hm; cases hm
        | binOp op2 a2 b2 =>
          cases op2 with
          | mul =>
            cases a2 with
            | constU64 alpha =>
              cases b2 with
              | var x' =>
                by_cases hcond : x' = x ∧ y' = y
                · rcases hcond with ⟨rfl, rfl⟩
                  simp only [matchBuiltinKernel2, and_self, ↓reduceIte, Option.some.injEq] at hm; subst hm
                  refine ⟨?_, nofun⟩; simp only [evalParKernelElem, bindCustomParInputs]
                  cases readParInput env st inputs 0 i with
                  | error _ => rfl
                  | ok vx =>
                    cases readParInput env st inputs 1 i with
                    | error _ => rfl
                    | ok vy => simp only [evalScalarExpr, VarEnv.bind, hyx_beq, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]; rfl
                · simp only [matchBuiltinKernel2, hcond, ↓reduceIte] at hm; cases hm
              | constU64 _ | constBool _ | binOp _ _ _ | unaryOp _ _ | select _ _ _ | fma _ _ _ => cases hm
            | constBool _ | var _ | binOp _ _ _ | unaryOp _ _ | select _ _ _ | fma _ _ _ => cases hm
          | add | sub | div | mod | bitAnd | bitOr | bitXor | shl | shr | sar | eq | lt | le
          | addChecked256 | subChecked256 | mulChecked256 | clmul64 | clmul64Hi | gf2Affine | eor3 => cases hm
        | constU64 _ | constBool _ | unaryOp _ _ | select _ _ _ | fma _ _ _ => cases hm
      | constU64 _ | constBool _ | binOp _ _ _ | unaryOp _ _ | select _ _ _ | fma _ _ _ => cases hm
    | sub | div | mod | bitAnd | bitOr | bitXor | shl | shr | sar | eq | lt | le
    | addChecked256 | subChecked256 | mulChecked256 | clmul64 | clmul64Hi | gf2Affine | eor3 => cases hm

/-- Whenever `matchBuiltinKernel idxVar inVars body = some k`, evaluating `k` at element `i`
    matches `.customScalar idxVar inVars body` and `k ≠ .dotProduct`. -/
theorem matchBuiltinKernel_elem_sound
    (env : VarEnv) (st : HeapState) (inputs : List VarId) (len : Nat)
    (idxVar : VarId) (inVars : List VarId) (body : ScalarExpr) (k : ParallelKernelKind) (i : Nat)
    (hm : matchBuiltinKernel idxVar inVars body = some k) :
    evalParKernelElem env st inputs len (.customScalar idxVar inVars body) i =
    evalParKernelElem env st inputs len k i ∧ k ≠ .dotProduct := by
  cases inVars with
  | nil => simp [matchBuiltinKernel] at hm
  | cons x rest =>
    cases rest with
    | nil =>
      simp only [matchBuiltinKernel] at hm; split at hm
      · simp at hm
      · exact matchBuiltinKernel1_elem_eq env st inputs len idxVar x body k i hm
    | cons y rest2 =>
      cases rest2 with
      | nil =>
        simp only [matchBuiltinKernel] at hm; split at hm
        · simp at hm
        · rename_i hnot
          exact matchBuiltinKernel2_elem_eq env st inputs len idxVar x y body k i (fun h => hnot (.inr (.inr h))) hm
      | cons _ _ => simp [matchBuiltinKernel] at hm

/-- `specializeKernel` preserves per-element parallel kernel evaluation identically. -/
theorem specializeKernel_elem_sound
    (env : VarEnv) (st : HeapState) (inputs : List VarId) (len : Nat)
    (kernel : ParallelKernelKind) (i : Nat) :
    evalParKernelElem env st inputs len kernel i =
    evalParKernelElem env st inputs len (specializeKernel kernel) i := by
  cases kernel with
  | mapScaleAdd _ _ | zipAdd | zipMul | saxpy _ | dotProduct | stencil1D3Pt _ _ _ => rfl
  | customScalar idxVar inVars body =>
    simp only [specializeKernel]
    have hbody_eq :
        evalParKernelElem env st inputs len (.customScalar idxVar inVars body) i =
        evalParKernelElem env st inputs len (.customScalar idxVar inVars (contractKernelScalar body)) i := by
      simp only [evalParKernelElem]
      cases bindCustomParInputs env st inputs i (env.bind idxVar (.u64 i.toUInt64)) 0 inVars with
      | error _ => rfl
      | ok kEnv => simp only [contractKernelScalar_sound body kEnv]
    rw [hbody_eq]
    cases hm : matchBuiltinKernel idxVar inVars (contractKernelScalar body) with
    | none => rfl
    | some kSpec =>
      exact (matchBuiltinKernel_elem_sound env st inputs len idxVar inVars
        (contractKernelScalar body) kSpec i hm).1

/-- `specializeKernel` preserves `evalParKernelLoop` over any index list `idxs`. -/
theorem specializeKernel_loop_sound
    (env : VarEnv) (st : HeapState) (inputs : List VarId) (len : Nat)
    (kernel : ParallelKernelKind) (idxs : List Nat) :
    evalParKernelLoop env st inputs len kernel idxs =
    evalParKernelLoop env st inputs len (specializeKernel kernel) idxs := by
  induction idxs with
  | nil => rfl
  | cons i is ih =>
    simp only [evalParKernelLoop, specializeKernel_elem_sound env st inputs len kernel i, ih]

/-- `specializeKernel` preserves `evalParFor` identically (same `.sarrayId` and `HeapState`!). -/
theorem specializeKernel_parFor_eq
    (fuel : Nat) (env : VarEnv) (st : HeapState) (lenVar : VarId) (inputs : List VarId)
    (kernel : ParallelKernelKind) :
    evalParFor fuel env st lenVar inputs kernel =
    evalParFor fuel env st lenVar inputs (specializeKernel kernel) := by
  unfold evalParFor
  cases env lenVar with
  | none => rfl
  | some lv =>
    cases lv with
    | u64 n =>
      by_cases hf : n.toNat > fuel
      · simp [hf]
      · simp only [hf, ↓reduceIte]
        cases evalVarList env inputs with
        | error _ => rfl
        | ok _ =>
          rw [specializeKernel_loop_sound env st inputs n.toNat kernel (List.range n.toNat)]
          cases evalParKernelLoop env st inputs n.toNat (specializeKernel kernel) (List.range n.toNat) with
          | error _ => rfl
          | ok elems =>
            cases kernel with
            | dotProduct | mapScaleAdd _ _ | zipAdd | zipMul | saxpy _ | stencil1D3Pt _ _ _ => rfl
            | customScalar idxVar inVars body =>
              simp only [specializeKernel]
              cases hm : matchBuiltinKernel idxVar inVars (contractKernelScalar body) with
              | none => rfl
              | some k =>
                cases k with
                | dotProduct =>
                  exact False.elim ((matchBuiltinKernel_elem_sound VarEnv.empty HeapState.empty [] 0
                    idxVar inVars (contractKernelScalar body) .dotProduct 0 hm).2 rfl)
                | _ => rfl
    | _ => rfl

private theorem evalSeqLoop_refines_step
    (count curIdx : Nat) (idxVar accVar : VarId) (accVal : Val) (env : VarEnv) (st : HeapState)
    (f g : VarEnv → HeapState → Except UBError (Val × HeapState))
    (v : Val) (st' : HeapState)
    (hfg : ∀ e s v1 s1, f e s = .ok (v1, s1) → g e s = .ok (v1, s1))
    (hf : evalSeqLoop count curIdx idxVar accVar accVal env st f = .ok (v, st')) :
    evalSeqLoop count curIdx idxVar accVar accVal env st g = .ok (v, st') := by
  induction count generalizing curIdx accVal st with
  | zero => exact hf
  | succ count' ih =>
    simp only [evalSeqLoop] at hf ⊢
    cases hstep : f ((env.bind idxVar (.u64 curIdx.toUInt64)).bind accVar accVal) st with
    | error _ => rw [hstep] at hf; cases hf
    | ok pair =>
      rw [hstep] at hf
      rw [hfg _ _ pair.1 pair.2 hstep]
      exact ih (curIdx + 1) pair.1 pair.2 hf

/-- Top-level `CodeRefines` soundness theorem for `specializeKernelCode`. -/
theorem specializeKernelCode_refines (code : LNIRCode) :
    CodeRefines code (specializeKernelCode code) := by
  induction code with
  | ret _ | unreachable => exact CodeRefines.refl _
  | letBind _ _ _ _ ih => exact CodeRefines.letBind_congr (ExprRefines.refl _) ih
  | rawStore _ _ _ _ _ ih => exact CodeRefines.rawStore_congr ih
  | incRef _ _ _ ih => exact CodeRefines.incRef_congr ih
  | decRef _ _ _ ih => exact CodeRefines.decRef_congr ih
  | ite _ _ _ iht ihe => exact CodeRefines.ite_congr iht ihe
  | seqFor idx lo hi acc init accTy s k ihs ihk =>
    intro fuel env st v st' hsrc
    simp only [specializeKernelCode]
    rw [evalCode] at hsrc ⊢
    cases hlo : env lo <;> cases hhi : env hi
    all_goals cases hinit : env init <;> simp only [hlo, hhi, hinit] at hsrc ⊢
    case some.some.some vlo vhi vinit =>
      cases vlo with
      | u64 nlo =>
        cases vhi with
        | u64 nhi =>
          simp only at hsrc ⊢
          cases hloop : evalSeqLoop (nhi.toNat - nlo.toNat) nlo.toNat idx acc vinit env st
              (fun e st0 => evalCode fuel e st0 s) with
          | error _ => rw [hloop] at hsrc; cases hsrc
          | ok pair =>
            rw [hloop] at hsrc
            have hloop2 := evalSeqLoop_refines_step (nhi.toNat - nlo.toNat) nlo.toNat idx acc vinit env st
              (fun e st0 => evalCode fuel e st0 s)
              (fun e st0 => evalCode fuel e st0 (specializeKernelCode s))
              pair.1 pair.2 (fun e st0 v1 s1 h => ihs fuel e st0 v1 s1 h) hloop
            rw [hloop2]
            exact ihk fuel (env.bind acc pair.1) pair.2 v st' hsrc
        | u256 _ | bool _ | tuple _ | objPtr _ | sarrayId _ | rawPtrId _ | storageMapId _ | unit => exact hsrc
      | u256 _ | bool _ | tuple _ | objPtr _ | sarrayId _ | rawPtrId _ | storageMapId _ | unit => exact hsrc
    all_goals exact hsrc
  | parFor out len inputs ety kernel k ih =>
    intro fuel env st v st' hsrc
    simp only [specializeKernelCode]
    rw [evalCode] at hsrc ⊢
    rw [← specializeKernel_parFor_eq]
    cases hpar : evalParFor fuel env st len inputs kernel with
    | error _ => rw [hpar] at hsrc; cases hsrc
    | ok pair =>
      rw [hpar] at hsrc
      exact ih fuel (env.bind out pair.1) pair.2 v st' hsrc

/-! ### 3. Producer-Consumer Multi-Stage `parFor` Loop Fusion Soundness -/

/-- Substitution lemma for `substScalarVar`: evaluating `substScalarVar target repl body` in `env`
    equals evaluating `body` in `env.bind target v` whenever `evalScalarExpr env repl = .ok v`. -/
theorem substScalarVar_eval_eq (env : VarEnv) (target : VarId) (repl body : ScalarExpr) (v : Val)
    (hrepl : evalScalarExpr env repl = .ok v) :
    evalScalarExpr env (substScalarVar target repl body) =
    evalScalarExpr (env.bind target v) body := by
  induction body with
  | constU64 _ | constBool _ => rfl
  | var id =>
    simp only [substScalarVar, evalScalarExpr, VarEnv.bind]
    by_cases hid : (id == target) = true
    · simp [hid, hrepl]
    · simp [hid, evalScalarExpr]
  | unaryOp op a ih =>
    simp only [substScalarVar, evalScalarExpr, ih]
  | binOp op l r ihl ihr =>
    simp only [substScalarVar, evalScalarExpr, ihl, ihr]
  | select c t f ihc iht ihf =>
    simp only [substScalarVar, evalScalarExpr, ihc, iht, ihf]
  | fma a b c iha ihb ihc =>
    simp only [substScalarVar, evalScalarExpr, iha, ihb, ihc]

/-- Modular 64-bit ring identity justifying `fuseMapScaleAddPair`:
    `(x * s1 + b1) * s2 + b2 = x * (s1 * s2) + (b1 * s2 + b2)` in `UInt64`. -/
theorem fuseMapScaleAddPair_algebra (x s1 b1 s2 b2 : UInt64) :
    (x * s1 + b1) * s2 + b2 = x * (s1 * s2) + (b1 * s2 + b2) := by
  rw [UInt64.add_mul, UInt64.mul_assoc, UInt64.add_assoc]

/-- Elementwise producer-consumer fusion theorem for two `.mapScaleAdd` stages. -/
theorem fuseMapScaleAdd_elem_sound
    (env : VarEnv) (st : HeapState) (srcBuf tmpVar : VarId) (len : Nat)
    (s1 b1 s2 b2 : UInt64) (elems1 : List UInt64) (i : Nat)
    (hlen : elems1.length = len) (hi : i < len)
    (h1 : evalParKernelElem env st [srcBuf] len (.mapScaleAdd s1 b1) i = .ok (elems1[i]'(by omega))) :
    let outId1 := st.nextId + 1
    let outBuf1 : ArrayBuffer := { id := outId1, exclusive := true, data := elems1.toArray }
    let st1 : HeapState := { st with buffers := outBuf1 :: st.buffers, nextId := outId1 }
    let env1 : VarEnv := env.bind tmpVar (.sarrayId outId1)
    evalParKernelElem env1 st1 [tmpVar] len (.mapScaleAdd s2 b2) i =
    evalParKernelElem env st [srcBuf] len (fuseMapScaleAddPair s1 b1 s2 b2) i := by
  intro outId1 outBuf1 st1 env1
  simp only [evalParKernelElem] at h1 ⊢
  cases hread : readParInput env st [srcBuf] 0 i with
  | error err => rw [hread] at h1; cases h1
  | ok x =>
    rw [hread] at h1
    injection h1 with hx_eq
    have htmp : readParInput env1 st1 [tmpVar] 0 i = .ok (elems1[i]'(by omega)) := by
      have hisz : i < elems1.length := by omega
      simp [readParInput, env1, st1, HeapState.readElem, HeapState.findBuffer, outBuf1, hisz]
    rw [htmp, ← hx_eq, fuseMapScaleAddPair]
    simp only [fuseMapScaleAddPair_algebra]

private theorem evalParKernelLoop_length_eq
    (env : VarEnv) (st : HeapState) (inputs : List VarId) (len : Nat)
    (kernel : ParallelKernelKind) (idxs : List Nat) (elems : List UInt64)
    (hloop : evalParKernelLoop env st inputs len kernel idxs = .ok elems) :
    elems.length = idxs.length := by
  induction idxs generalizing elems with
  | nil => injection hloop with he; subst he; rfl
  | cons a as ih =>
    simp only [evalParKernelLoop] at hloop
    cases ha : evalParKernelElem env st inputs len kernel a with
    | error _ => rw [ha] at hloop; cases hloop
    | ok x =>
      rw [ha] at hloop
      cases hl2 : evalParKernelLoop env st inputs len kernel as with
      | error _ => rw [hl2] at hloop; cases hloop
      | ok xs =>
        rw [hl2] at hloop; injection hloop with he
        subst he; simp [ih xs hl2]

private theorem evalParKernelLoop_getElem_ok
    (env : VarEnv) (st : HeapState) (inputs : List VarId) (len : Nat)
    (kernel : ParallelKernelKind) (idxs : List Nat) (elems : List UInt64)
    (hloop : evalParKernelLoop env st inputs len kernel idxs = .ok elems)
    (k : Nat) (hk : k < idxs.length) :
    evalParKernelElem env st inputs len kernel idxs[k] =
    .ok (elems[k]'(by rw [evalParKernelLoop_length_eq env st inputs len kernel idxs elems hloop]; exact hk)) := by
  induction idxs generalizing elems k with
  | nil => exact absurd hk (Nat.not_lt_zero _)
  | cons a as ih =>
    simp only [evalParKernelLoop] at hloop
    cases ha : evalParKernelElem env st inputs len kernel a with
    | error _ => rw [ha] at hloop; cases hloop
    | ok x =>
      rw [ha] at hloop
      cases has : evalParKernelLoop env st inputs len kernel as with
      | error _ => rw [has] at hloop; cases hloop
      | ok xs =>
        rw [has] at hloop; injection hloop with he; subst he
        cases k with
        | zero => simp [ha]
        | succ k' => simpa using ih xs has k' (Nat.lt_of_succ_lt_succ hk)

private theorem evalParKernelLoop_ext_subset
    (env1 env2 : VarEnv) (st1 st2 : HeapState) (ins1 ins2 : List VarId) (len : Nat)
    (k1 k2 : ParallelKernelKind) (idxs : List Nat)
    (heq : ∀ i, i ∈ idxs →
      evalParKernelElem env1 st1 ins1 len k1 i = evalParKernelElem env2 st2 ins2 len k2 i) :
    evalParKernelLoop env1 st1 ins1 len k1 idxs =
    evalParKernelLoop env2 st2 ins2 len k2 idxs := by
  induction idxs with
  | nil => rfl
  | cons i is ih =>
    simp only [evalParKernelLoop]; rw [heq i (.head is), ih (fun j hj => heq j (.tail i hj))]

/-- Full loop-level producer-consumer fusion theorem for `evalParKernelLoop` over `List.range len`. -/
theorem fuseMapScaleAdd_loop_sound
    (env : VarEnv) (st : HeapState) (srcBuf tmpVar : VarId) (len : Nat)
    (s1 b1 s2 b2 : UInt64) (elems1 : List UInt64)
    (hloop1 : evalParKernelLoop env st [srcBuf] len (.mapScaleAdd s1 b1) (List.range len) = .ok elems1) :
    let outId1 := st.nextId + 1
    let outBuf1 : ArrayBuffer := { id := outId1, exclusive := true, data := elems1.toArray }
    let st1 : HeapState := { st with buffers := outBuf1 :: st.buffers, nextId := outId1 }
    let env1 : VarEnv := env.bind tmpVar (.sarrayId outId1)
    evalParKernelLoop env1 st1 [tmpVar] len (.mapScaleAdd s2 b2) (List.range len) =
    evalParKernelLoop env st [srcBuf] len (fuseMapScaleAddPair s1 b1 s2 b2) (List.range len) := by
  intro outId1 outBuf1 st1 env1
  have hlen : elems1.length = len := by
    simpa using evalParKernelLoop_length_eq env st [srcBuf] len (.mapScaleAdd s1 b1) (List.range len) elems1 hloop1
  apply evalParKernelLoop_ext_subset; intro i hi_mem
  have hi : i < len := List.mem_range.mp hi_mem
  have hir : i < (List.range len).length := by simpa using hi
  have h1i : evalParKernelElem env st [srcBuf] len (.mapScaleAdd s1 b1) i = .ok (elems1[i]'(by omega)) := by
    have hraw := evalParKernelLoop_getElem_ok env st [srcBuf] len (.mapScaleAdd s1 b1)
      (List.range len) elems1 hloop1 i hir
    simpa [List.getElem_range] using hraw
  exact fuseMapScaleAdd_elem_sound env st srcBuf tmpVar len s1 b1 s2 b2 elems1 i hlen hi h1i

/-- End-to-end `evalCode` buffer-content observational refinement theorem for `fuseParForCode`
    (`fuseParForKernels_sound`): whenever a two-stage `parFor` producer-consumer pipeline over
    scalar element type `elemTy` (`sameElemType elemTy elemTy = true`) evaluates to
    `(.sarrayId idSrc, stSrc)`, the `fuseParForCode`-transformed single-pass `parFor` evaluates to
    `(.sarrayId idTgt, stTgt)` with identical `ArrayBuffer.data`, `exclusive = true`, and strictly
    one fewer intermediate `HeapState` buffer allocation (`stTgt.nextId + 1 = stSrc.nextId`). -/
theorem fuseParForKernels_sound
    (fuel : Nat) (env : VarEnv) (st : HeapState)
    (tmpVar outVar lenVar srcBuf : VarId) (elemTy : LNIRType)
    (s1 b1 s2 b2 : UInt64) (vSrc : Val) (stSrc : HeapState)
    (helem : sameElemType elemTy elemTy = true)
    (hlen_ne : tmpVar ≠ lenVar) (hout_ne : tmpVar ≠ outVar) (hsrc_ne : srcBuf ≠ tmpVar)
    (hsrc : evalCode fuel env st
      (.parFor tmpVar lenVar [srcBuf] elemTy (.mapScaleAdd s1 b1)
        (.parFor outVar lenVar [tmpVar] elemTy (.mapScaleAdd s2 b2) (.ret outVar))) =
      .ok (vSrc, stSrc)) :
    ∃ (idSrc idTgt : Nat) (stTgt : HeapState) (bufSrc bufTgt : ArrayBuffer),
      vSrc = .sarrayId idSrc ∧
      evalCode fuel env st
        (fuseParForCode (.parFor tmpVar lenVar [srcBuf] elemTy (.mapScaleAdd s1 b1)
          (.parFor outVar lenVar [tmpVar] elemTy (.mapScaleAdd s2 b2) (.ret outVar)))) =
        .ok (.sarrayId idTgt, stTgt) ∧
      stSrc.findBuffer idSrc = some bufSrc ∧
      stTgt.findBuffer idTgt = some bufTgt ∧
      bufSrc.data = bufTgt.data ∧
      bufSrc.exclusive = true ∧
      bufTgt.exclusive = true ∧
      stTgt.nextId + 1 = stSrc.nextId := by
  have hcode :
      fuseParForCode (.parFor tmpVar lenVar [srcBuf] elemTy (.mapScaleAdd s1 b1)
        (.parFor outVar lenVar [tmpVar] elemTy (.mapScaleAdd s2 b2) (.ret outVar))) =
      .parFor outVar lenVar [srcBuf] elemTy (fuseMapScaleAddPair s1 b1 s2 b2) (.ret outVar) := by
    have hout_bne : (tmpVar != outVar) = true := bne_iff_ne.mpr hout_ne
    have hout_beq_symm : (outVar == tmpVar) = false := beq_false_of_ne (Ne.symm hout_ne)
    have htmp_src : tmpVar ≠ srcBuf := Ne.symm hsrc_ne
    simp [fuseParForCode, specializeKernel, stripDeadTmpDecRef, codeUsesVar,
      fuseTwoParForStage, hout_bne, hout_beq_symm, htmp_src, helem]
  rw [hcode]
  simp only [evalCode] at hsrc ⊢
  unfold evalParFor at hsrc ⊢
  cases hlen : env lenVar with
  | none => rw [hlen] at hsrc; cases hsrc
  | some lv =>
    rw [hlen] at hsrc
    cases lv with
    | u64 n =>
      by_cases hf : n.toNat > fuel
      · simp [hf] at hsrc
      · simp only [hf, ↓reduceIte] at hsrc ⊢
        cases hvl : evalVarList env [srcBuf] with
        | error _ => rw [hvl] at hsrc; cases hsrc
        | ok _ =>
          rw [hvl] at hsrc
          cases hloop1 : evalParKernelLoop env st [srcBuf] n.toNat (.mapScaleAdd s1 b1) (List.range n.toNat) with
          | error _ => rw [hloop1] at hsrc; cases hsrc
          | ok elems1 =>
            rw [hloop1] at hsrc; simp only at hsrc
            have hne_beq : (lenVar == tmpVar) = false := beq_false_of_ne (Ne.symm hlen_ne)
            have hlen1 : (env.bind tmpVar (.sarrayId (st.nextId + 1))) lenVar = some (.u64 n) := by
              simp [VarEnv.bind, hne_beq, hlen]
            have hvl1 : evalVarList (env.bind tmpVar (.sarrayId (st.nextId + 1))) [tmpVar] =
                .ok [.sarrayId (st.nextId + 1)] := by simp [evalVarList, VarEnv.bind]
            rw [hlen1] at hsrc; simp only [hf, ↓reduceIte, hvl1] at hsrc
            rw [fuseMapScaleAdd_loop_sound env st srcBuf tmpVar n.toNat s1 b1 s2 b2 elems1 hloop1] at hsrc
            cases hloop2 : evalParKernelLoop env st [srcBuf] n.toNat
                (fuseMapScaleAddPair s1 b1 s2 b2) (List.range n.toNat) with
            | error _ => rw [hloop2] at hsrc; cases hsrc
            | ok elems2 =>
              rw [hloop2] at hsrc
              simp only [fuseMapScaleAddPair, VarEnv.bind, beq_self_eq_true, ↓reduceIte] at hsrc ⊢
              injection hsrc with hpair; injection hpair with hv hst
              subst hv; subst hst
              refine ⟨st.nextId + 1 + 1, st.nextId + 1,
                { st with
                  buffers := { id := st.nextId + 1, exclusive := true, data := elems2.toArray } :: st.buffers
                  nextId := st.nextId + 1 },
                { id := st.nextId + 1 + 1, exclusive := true, data := elems2.toArray },
                { id := st.nextId + 1, exclusive := true, data := elems2.toArray },
                rfl, rfl, by simp [HeapState.findBuffer], by simp [HeapState.findBuffer], rfl, rfl, rfl, rfl⟩
    | _ => simp at hsrc

/-- General 1-input `.customScalar` producer-consumer fusion soundness at element `i`
    for `UInt64`-producing producers (`evalScalarExpr ... pBody = .ok (.u64 v1)`). -/
theorem fuseCustomScalar1_elem_sound
    (env : VarEnv) (st : HeapState) (srcBuf : VarId) (len : Nat)
    (idxVar pVar cVar : VarId) (pBody cBody : ScalarExpr) (i : Nat) (x v1 : UInt64)
    (hread : readParInput env st [srcBuf] 0 i = .ok x)
    (hp : evalScalarExpr ((env.bind idxVar (.u64 i.toUInt64)).bind pVar (.u64 x)) pBody = .ok (.u64 v1)) :
    evalParKernelElem env st [srcBuf] len (.customScalar idxVar [pVar] (substScalarVar cVar pBody cBody)) i =
    (match evalScalarExpr (((env.bind idxVar (.u64 i.toUInt64)).bind pVar (.u64 x)).bind cVar (.u64 v1)) cBody with
     | .ok (.u64 v) => .ok v
     | .ok (.bool b) => .ok (if b then 1 else 0)
     | .ok _ => .error (.typeError "customScalar body must evaluate to u64 or bool")
     | .error err => .error err) := by
  simp only [evalParKernelElem, bindCustomParInputs, hread]
  rw [substScalarVar_eval_eq ((env.bind idxVar (.u64 i.toUInt64)).bind pVar (.u64 x)) cVar pBody cBody (.u64 v1) hp]
  rfl

/-- General 1-input `.customScalar` producer-consumer fusion soundness at element `i`
    for `Bool`-producing producers (`evalScalarExpr ... pBody = .ok (.bool b1)`), proving that
    wrapping `pBody` in `.select pBody (.constU64 1) (.constU64 0)` matches `evalParKernelElem`'s
    `bool -> UInt64` (`if b1 then 1 else 0`) boundary coercion (`Eval.lean:490`). -/
theorem fuseCustomScalar1_bool_coerced_elem_sound
    (env : VarEnv) (st : HeapState) (srcBuf : VarId) (len : Nat)
    (idxVar pVar cVar : VarId) (pBody cBody : ScalarExpr) (i : Nat) (x : UInt64) (b1 : Bool)
    (hread : readParInput env st [srcBuf] 0 i = .ok x)
    (hp : evalScalarExpr ((env.bind idxVar (.u64 i.toUInt64)).bind pVar (.u64 x)) pBody = .ok (.bool b1)) :
    evalParKernelElem env st [srcBuf] len
      (.customScalar idxVar [pVar]
        (substScalarVar cVar (.select pBody (.constU64 1) (.constU64 0)) cBody)) i =
    (match evalScalarExpr
        (((env.bind idxVar (.u64 i.toUInt64)).bind pVar (.u64 x)).bind cVar (.u64 (if b1 then 1 else 0))) cBody with
     | .ok (.u64 v) => .ok v
     | .ok (.bool b) => .ok (if b then 1 else 0)
     | .ok _ => .error (.typeError "customScalar body must evaluate to u64 or bool")
     | .error err => .error err) := by
  have hsel :
      evalScalarExpr ((env.bind idxVar (.u64 i.toUInt64)).bind pVar (.u64 x))
        (.select pBody (.constU64 1) (.constU64 0)) =
      .ok (.u64 (if b1 then 1 else 0)) := by
    cases b1 <;> simp [evalScalarExpr, hp]
  simp only [evalParKernelElem, bindCustomParInputs, hread]
  rw [substScalarVar_eval_eq ((env.bind idxVar (.u64 i.toUInt64)).bind pVar (.u64 x)) cVar
    (.select pBody (.constU64 1) (.constU64 0)) cBody (.u64 (if b1 then 1 else 0)) hsel]
  rfl

end LeanNative.Proofs
