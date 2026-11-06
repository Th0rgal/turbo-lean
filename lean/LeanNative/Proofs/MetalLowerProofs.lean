import LeanNative.Backend.MetalLower
import LeanNative.Backend.MetalAst
import LeanNative.Proofs.MetalLowerSpec
import LeanNative.Proofs.MetalSIMT6

namespace LeanNative.Proofs.MetalLowerProofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend
open LeanNative.Backend.MetalLower
open LeanNative.Proofs
open LeanNative.Proofs.MetalLowerSpec

/-- The scalar lowerer stays in the unambiguous scalar grammar provided its variable
spellings are valid identifiers. This premise is about names, not parser success. -/
theorem lowerScalar_canonical (idxName : String) (idxVar : Nat) (e : ScalarExpr)
    (hidx : MetalAst.CanonicalMSLName idxName)
    (hvars : ∀ id : Nat, MetalAst.CanonicalMSLName s!"v{id}") :
    MetalAst.CanonicalMSLExpr (lowerScalar idxName idxVar e) := by
  induction e with
  | constU64 n => trivial
  | constBool b => cases b <;> trivial
  | var id =>
    unfold lowerScalar
    split
    · exact hidx
    · exact hvars id
  | binOp op l r hl hr =>
    cases op <;> simp_all [lowerScalar, m63, u, MetalAst.CanonicalMSLExpr]
  | unaryOp op a ha =>
    cases op <;> simp_all [lowerScalar, u, MetalAst.CanonicalMSLExpr]
  | select c t f hc ht hf => simp_all [lowerScalar, u, MetalAst.CanonicalMSLExpr]
  | fma a b c ha hb hc => simp_all [lowerScalar, MetalAst.CanonicalMSLExpr]

theorem canonicalBlock_ofList (stmts : List MetalAst.MSLStmt) :
    MetalAst.CanonicalMSLBlock (.ofList stmts) ↔
      ∀ stmt ∈ stmts, MetalAst.CanonicalMSLStmt stmt := by
  induction stmts with
  | nil => simp [MetalAst.MSLBlock.ofList, MetalAst.CanonicalMSLBlock]
  | cons s ss ih => simp [MetalAst.MSLBlock.ofList, MetalAst.CanonicalMSLBlock, ih]

theorem bufParam_type_canonical (name : String) (idx : Nat) (isConst : Bool) :
    MetalAst.CanonicalMSLType (bufParam name idx isConst).ty := by
  simp [bufParam, MetalAst.CanonicalMSLType, MetalAst.CanonicalMSLValueType]

theorem guarded_canonical (inner : List MetalAst.MSLStmt)
    (h : ∀ stmt ∈ inner, MetalAst.CanonicalMSLStmt stmt) :
    ∀ stmt ∈ guarded inner, MetalAst.CanonicalMSLStmt stmt := by
  have hg : MetalAst.CanonicalMSLName "gid" := by simp [MetalAst.CanonicalMSLName, MetalAst.mslNameChar]; decide
  have hn : MetalAst.CanonicalMSLName "n" := by simp [MetalAst.CanonicalMSLName, MetalAst.mslNameChar]; decide
  simpa [guarded, MetalAst.CanonicalMSLStmt, MetalAst.CanonicalMSLExpr,
    MetalAst.CanonicalMSLBlock, canonicalBlock_ofList, hg, hn] using h

theorem storeOut_canonical (rhs : MetalAst.MSLExpr) (h : MetalAst.CanonicalMSLExpr rhs) :
    MetalAst.CanonicalMSLStmt (storeOut rhs) := by
  have ho : MetalAst.CanonicalMSLBindingName "out" := by
    simp [MetalAst.CanonicalMSLBindingName, MetalAst.CanonicalMSLName, MetalAst.mslNameChar,
      MetalAst.parseMSLScalarType]; decide
  have hg : MetalAst.CanonicalMSLName "gid" := by simp [MetalAst.CanonicalMSLName, MetalAst.mslNameChar]; decide
  exact ⟨ho, hg, h⟩

theorem kernelOf_canonical (name : String) (nIn : Nat) (compute : MetalAst.MSLExpr)
    (hn : MetalAst.CanonicalMSLName name)
    (hi : ∀ i : Nat, MetalAst.CanonicalMSLName s!"in{i}")
    (hc : MetalAst.CanonicalMSLExpr compute) :
    MetalAst.CanonicalMSLKernel (kernelOf name nIn compute) := by
  have ho : MetalAst.CanonicalMSLName "out" := by simp [MetalAst.CanonicalMSLName, MetalAst.mslNameChar]; decide
  have hl : MetalAst.CanonicalMSLName "n" := by simp [MetalAst.CanonicalMSLName, MetalAst.mslNameChar]; decide
  have hg : MetalAst.CanonicalMSLName "gid" := by simp [MetalAst.CanonicalMSLName, MetalAst.mslNameChar]; decide
  refine ⟨hn, ?_, rfl, guarded_canonical _ (by simpa using storeOut_canonical compute hc)⟩
  intro param hp
  simp only [kernelOf, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with ⟨i, _, rfl⟩ | rfl | rfl | rfl
  all_goals simp [bufParam, lenParam, gidParam, MetalAst.CanonicalMSLType,
    MetalAst.CanonicalMSLValueType, ho, hl, hg]
  exact hi i

theorem lowerKind_canonical (name : String) (kind : ParallelKernelKind)
    (hn : MetalAst.CanonicalMSLName name)
    (hi : ∀ i : Nat, MetalAst.CanonicalMSLName s!"in{i}")
    (hv : ∀ i : Nat, MetalAst.CanonicalMSLName s!"v{i}") :
    MetalAst.CanonicalMSLKernel (lowerKind name kind) := by
  have hg : MetalAst.CanonicalMSLName "gid" := by simp [MetalAst.CanonicalMSLName, MetalAst.mslNameChar]; decide
  have hg64 : MetalAst.CanonicalMSLName "gid64" := by simp [MetalAst.CanonicalMSLName, MetalAst.mslNameChar]; decide
  have hl : MetalAst.CanonicalMSLName "n" := by simp [MetalAst.CanonicalMSLName, MetalAst.mslNameChar]; decide
  have he (i : Nat) : MetalAst.CanonicalMSLExpr (elem s!"in{i}") := ⟨hi i, hg⟩
  cases kind with
  | mapScaleAdd s b | zipAdd | zipMul | saxpy a =>
    apply kernelOf_canonical _ _ _ hn hi
    all_goals
      simp [MetalAst.CanonicalMSLExpr, elem, MetalAst.CanonicalMSLName, MetalAst.mslNameChar]
      decide
  | dotProduct => simp [lowerKind, MetalAst.CanonicalMSLKernel, MetalAst.CanonicalMSLStmt, hn]
  | stencil1D3Pt l c r =>
    have hp := (kernelOf_canonical name 1 (.immU64 0) hn hi trivial).2.1
    refine ⟨hn, hp, rfl, guarded_canonical _ ?_⟩
    simp [MetalAst.CanonicalMSLStmt, MetalAst.CanonicalMSLBlock,
      MetalAst.CanonicalMSLExpr, storeOut, elem, u,
      MetalAst.CanonicalMSLBindingName, MetalAst.CanonicalMSLName, MetalAst.mslNameChar,
      MetalAst.parseMSLScalarType]
    decide
  | customScalar idx inputs body =>
    have hp := (kernelOf_canonical name inputs.length (.immU64 0) hn hi trivial).2.1
    refine ⟨hn, hp, rfl, guarded_canonical _ ?_⟩
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map]
    intro stmt hs
    rcases hs with (rfl | ⟨i, _, rfl⟩) | rfl
    · exact ⟨trivial, hg64, Or.inl rfl, hg⟩
    · exact ⟨trivial, hv _, he i⟩
    · exact storeOut_canonical _ (lowerScalar_canonical _ _ _ hg64 hv)

theorem lowerScalar_inferExprType (g : MetalAst.MSLGroupState) (ls : MetalAst.MSLLocals)
    (idxName : String) (idxVar : Nat) (boundVars : List Nat) (e : ScalarExpr) (s : Bool)
    (hsort : inferScalarSort boundVars e = some s)
    (hty : ∀ id ∈ boundVars, ls.lookupType? (if id == idxVar then idxName else s!"v{id}") = some .ulong) :
    MetalAst.inferExprType g ls (lowerScalar idxName idxVar e) = .ulong := by
  induction e generalizing s with
  | constU64 _ | constBool _ => rfl
  | var id =>
    simp only [inferScalarSort] at hsort
    split at hsort
    · rename_i hmem; have hl := hty id hmem; unfold lowerScalar v
      cases hidx : id == idxVar
      · simp only [hidx, Bool.false_eq_true, ite_false] at hl ⊢
        simp only [MetalAst.inferExprType, hl]
      · simp only [hidx, ite_true] at hl ⊢
        simp only [MetalAst.inferExprType, hl]
    · cases hsort
  | binOp op l r ihl ihr =>
    simp only [inferScalarSort] at hsort
    cases hsl : inferScalarSort boundVars l <;> simp only [hsl] at hsort
    · cases hsort
    · cases hsr : inferScalarSort boundVars r <;> simp only [hsr] at hsort
      · cases hsort
      · rename_i sl sr; have tl := ihl sl hsl; have tr := ihr sr hsr
        cases sl
        · cases sr <;> try simp at hsort
          cases op <;> simp [inferBinOpU64] at hsort
          all_goals
            simp only [lowerScalar, u, m63, MetalAst.inferExprType,
              MetalSIMT.promoteMSLArithType_ulong, tl, tr]
        · cases sr <;> try simp at hsort
          cases op <;> simp [inferBinOpBool] at hsort
          all_goals
            simp only [lowerScalar, MetalAst.inferExprType]
  | unaryOp op a iha =>
    simp only [inferScalarSort] at hsort
    cases hsa : inferScalarSort boundVars a <;> simp only [hsa] at hsort
    · cases hsort
    · rename_i sa; have ta := iha sa hsa
      cases sa <;> try simp at hsort
      cases op <;> simp [inferUnaryOpU64] at hsort
      all_goals
        simp only [lowerScalar, u, MetalAst.inferExprType,
          MetalSIMT.promoteMSLArithType_ulong, ta]
  | select c t f _ iht _ =>
    simp only [inferScalarSort] at hsort
    cases hsc : inferScalarSort boundVars c <;> simp only [hsc] at hsort
    · cases hsort
    · cases hst : inferScalarSort boundVars t <;> simp only [hst] at hsort
      · cases hsort
      · rename_i st; cases hsf : inferScalarSort boundVars f <;> simp only [hsf] at hsort
        · cases hsort
        · simp only [lowerScalar, MetalAst.inferExprType, iht st hst]
  | fma a b c iha ihb ihc =>
    simp only [inferScalarSort] at hsort
    cases hsa : inferScalarSort boundVars a <;> simp only [hsa] at hsort
    · cases hsort
    · cases hsb : inferScalarSort boundVars b <;> simp only [hsb] at hsort
      · cases hsort
      · cases hsc : inferScalarSort boundVars c <;> simp only [hsc] at hsort
        · cases hsort
        · rename_i sa sb sc
          simp only [lowerScalar, MetalAst.inferExprType, MetalSIMT.promoteMSLArithType_ulong,
            iha sa hsa, ihb sb hsb, ihc sc hsc]
theorem varEnvMatchesLocals_mem (env : VarEnv) (ls : MetalAst.MSLLocals)
    (idxName : String) (idxVar : Nat) (boundVars : List Nat)
    (hmatch : varEnvMatchesLocals env ls idxName idxVar boundVars)
    {id : Nat} (hmem : id ∈ boundVars) :
    ∃ x : UInt64, env id = some (.u64 x) ∧
      ls.lookup? (if id == idxVar then idxName else s!"v{id}") = some x.toBitVec ∧
      ls.lookupType? (if id == idxVar then idxName else s!"v{id}") = some .ulong := by
  induction boundVars with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases hmatch with ⟨hhd, htl⟩
    cases List.mem_cons.mp hmem with
    | inl heq => subst heq; exact hhd
    | inr hrest => exact ih htl hrest

private theorem valOfSort_false {v : Val} {bv : BitVec 64} (h : valOfSort false v = some bv) :
    ∃ x : UInt64, v = .u64 x ∧ bv = x.toBitVec := by
  cases v <;> simp [valOfSort] at h
  exact ⟨_, rfl, h.symm⟩

private theorem valOfSort_true {v : Val} {bv : BitVec 64} (h : valOfSort true v = some bv) :
    ∃ b : Bool, v = .bool b ∧ bv = (if b then 1#64 else 0#64) := by
  cases v <;> simp [valOfSort] at h
  exact ⟨_, rfl, h.symm⟩

private theorem lowerBinOpU64_eval
    (callEval : Nat → MetalAst.MSLGroupState → MetalAst.Dim3 → MetalAst.MSLLocals →
      List MetalAst.MSLAccess → String → MetalAst.MSLExprList → MetalAst.MSLOutcome MetalAst.MSLEval)
    (env : VarEnv) (idxName : String) (idxVar : Nat) (l r : ScalarExpr)
    (op : BinOp) (s : Bool) (xl xr : UInt64) (hsort : inferBinOpU64 op = some s)
    (hevl : evalScalarExpr env l = .ok (.u64 xl)) (hevr : evalScalarExpr env r = .ok (.u64 xr)) :
    ∃ (val : Val) (bv : BitVec 64),
      evalScalarExpr env (.binOp op l r) = .ok val ∧ valOfSort s val = some bv ∧
      ∀ (f : Nat) (g : MetalAst.MSLGroupState) (t : MetalAst.Dim3) (ls : MetalAst.MSLLocals)
        (lg : List MetalAst.MSLAccess),
        MetalAst.evalExprWithCall callEval f g t ls lg (lowerScalar idxName idxVar l) =
          .ok { value := xl.toBitVec, fields := [], locals := ls, log := lg } →
        MetalAst.evalExprWithCall callEval f g t ls lg (lowerScalar idxName idxVar r) =
          .ok { value := xr.toBitVec, fields := [], locals := ls, log := lg } →
        MetalAst.inferExprType g ls (lowerScalar idxName idxVar l) = .ulong →
        MetalAst.inferExprType g ls (lowerScalar idxName idxVar r) = .ulong →
        MetalAst.evalExprWithCall callEval f g t ls lg (lowerScalar idxName idxVar (.binOp op l r)) =
          .ok { value := bv, fields := [], locals := ls, log := lg } := by
  cases op with
  | addChecked256 | subChecked256 | mulChecked256 | clmul64 | clmul64Hi | gf2Affine => cases hsort
  | add => rcases hsort with ⟨rfl⟩; exact ⟨_, _, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
      fun f g t ls lg => MetalSIMT.ev_add_ulong callEval f g t ls lg _ _ _ _⟩
  | sub => rcases hsort with ⟨rfl⟩; exact ⟨_, _, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
      fun f g t ls lg => MetalSIMT.ev_sub_ulong callEval f g t ls lg _ _ _ _⟩
  | mul => rcases hsort with ⟨rfl⟩; exact ⟨_, _, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
      fun f g t ls lg => MetalSIMT.ev_mul_ulong callEval f g t ls lg _ _ _ _⟩
  | bitAnd => rcases hsort with ⟨rfl⟩; exact ⟨_, _, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
      fun f g t ls lg => MetalSIMT.ev_bitand_ulong callEval f g t ls lg _ _ _ _⟩
  | bitOr => rcases hsort with ⟨rfl⟩; exact ⟨_, _, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
      fun f g t ls lg => MetalSIMT.ev_bitor_ulong callEval f g t ls lg _ _ _ _⟩
  | bitXor => rcases hsort with ⟨rfl⟩; exact ⟨_, _, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
      fun f g t ls lg => MetalSIMT.ev_bitxor_ulong callEval f g t ls lg _ _ _ _⟩
  | div => rcases hsort with ⟨rfl⟩; exact ⟨_, _, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
      fun f g t ls lg => MetalSIMT.ev_div_guarded_ulong callEval f g t ls lg _ _ _ _⟩
  | mod => rcases hsort with ⟨rfl⟩; exact ⟨_, _, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
      fun f g t ls lg => MetalSIMT.ev_mod_guarded_ulong callEval f g t ls lg _ _ _ _⟩
  | shl =>
    rcases hsort with ⟨rfl⟩; refine ⟨_, _, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl, fun f g t ls lg hl hr htl htr => ?_⟩
    rw [← MetalSIMT.shl_bv_eq_u64]; exact MetalSIMT.ev_shl_masked_ulong callEval f g t ls lg _ _ _ _ hl hr htl htr
  | shr =>
    rcases hsort with ⟨rfl⟩; refine ⟨_, _, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl, fun f g t ls lg hl hr htl htr => ?_⟩
    rw [← MetalSIMT.shr_bv_eq_u64]; exact MetalSIMT.ev_shr_masked_ulong callEval f g t ls lg _ _ _ _ hl hr htl htr
  | sar =>
    rcases hsort with ⟨rfl⟩; refine ⟨_, _, by simp only [evalScalarExpr, hevl, hevr]; rfl, rfl, fun f g t ls lg hl hr htl htr => ?_⟩
    rw [← MetalSIMT.sar_bv_eq_u64]; exact MetalSIMT.ev_sar_masked_ulong callEval f g t ls lg _ _ _ _ hl hr htl htr
  | eor3 =>
    rcases hsort with ⟨rfl⟩
    refine ⟨.u64 ((xl ^^^ (xr >>> 32)) ^^^ (xr &&& 0xffffffff)), _, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
      fun f g t ls lg hl hr htl htr => ?_⟩
    rw [← MetalSIMT.eor3_bv_eq_u64]; exact MetalSIMT.ev_eor3_compound_ulong callEval f g t ls lg _ _ _ _ hl hr htl htr
  | eq =>
    rcases hsort with ⟨rfl⟩; refine ⟨_, _, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl, fun f g t ls lg hl hr htl htr => ?_⟩
    rw [← MetalSIMT.eq_bv_iff]; exact MetalSIMT.ev_eq_cast_ulong callEval f g t ls lg _ _ _ _ hl hr htl htr
  | lt => rcases hsort with ⟨rfl⟩; exact ⟨_, _, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
      fun f g t ls lg => MetalSIMT.ev_lt_cast_ulong callEval f g t ls lg _ _ _ _⟩
  | le => rcases hsort with ⟨rfl⟩; exact ⟨_, _, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
      fun f g t ls lg => MetalSIMT.ev_le_cast_ulong callEval f g t ls lg _ _ _ _⟩

private theorem lowerScalar_eval_core
    (callEval : Nat → MetalAst.MSLGroupState → MetalAst.Dim3 → MetalAst.MSLLocals →
      List MetalAst.MSLAccess → String → MetalAst.MSLExprList → MetalAst.MSLOutcome MetalAst.MSLEval)
    (env : VarEnv) (idxName : String) (idxVar : Nat) (boundVars : List Nat)
    (henv : ∀ id ∈ boundVars, ∃ x : UInt64, env id = some (.u64 x))
    (e : ScalarExpr) (s : Bool) (hsort : inferScalarSort boundVars e = some s) :
    ∃ (val : Val) (bv : BitVec 64), evalScalarExpr env e = .ok val ∧ valOfSort s val = some bv ∧
      ∀ (fuel : Nat) (g : MetalAst.MSLGroupState) (tid : MetalAst.Dim3) (ls : MetalAst.MSLLocals)
        (log : List MetalAst.MSLAccess), varEnvMatchesLocals env ls idxName idxVar boundVars →
        MetalAst.evalExprWithCall callEval fuel g tid ls log (lowerScalar idxName idxVar e) =
          .ok { value := bv, fields := [], locals := ls, log := log } := by
  have htyM (ls : MetalAst.MSLLocals) (hm : varEnvMatchesLocals env ls idxName idxVar boundVars)
      (id : Nat) (hmem : id ∈ boundVars) :
      ls.lookupType? (if id == idxVar then idxName else s!"v{id}") = some .ulong := by
    rcases varEnvMatchesLocals_mem env ls idxName idxVar boundVars hm hmem with ⟨_, _, _, ht⟩
    exact ht
  induction e generalizing s with
  | constU64 n =>
    rcases hsort with ⟨rfl⟩; refine ⟨.u64 n, n.toBitVec, rfl, rfl, fun _ _ _ _ _ _ => ?_⟩
    unfold lowerScalar; rw [MetalAst.evalExprWithCall]
  | constBool b =>
    rcases hsort with ⟨rfl⟩; exact ⟨.bool b, if b then 1#64 else 0#64, rfl, rfl, fun _ _ _ _ _ _ => by cases b <;> rfl⟩
  | var id =>
    simp only [inferScalarSort] at hsort; split at hsort
    · rename_i hmem; rcases hsort with ⟨rfl⟩; rcases henv id hmem with ⟨x, hx⟩
      refine ⟨.u64 x, x.toBitVec, by simp only [evalScalarExpr, hx], rfl, fun fuel g tid ls log hm => ?_⟩
      rcases varEnvMatchesLocals_mem env ls idxName idxVar boundVars hm hmem with ⟨x', hx', hlk, hlt⟩
      obtain ⟨rfl⟩ : Val.u64 x = Val.u64 x' := Option.some.inj (hx.symm.trans hx')
      unfold lowerScalar v
      cases hidx : id == idxVar <;> simp only [hidx, Bool.false_eq_true, ite_false, ite_true] at hlk hlt ⊢ <;>
        exact MetalSIMT.ev_var_bound callEval fuel g tid ls log _ x.toBitVec hlk hlt
    · cases hsort
  | unaryOp op a iha =>
    simp only [inferScalarSort] at hsort
    cases hsa : inferScalarSort boundVars a <;> simp only [hsa] at hsort
    · cases hsort
    · rename_i sa; cases sa <;> simp at hsort
      rcases iha false hsa with ⟨_, _, heva, hva, haAll⟩
      rcases valOfSort_false hva with ⟨xa, rfl, rfl⟩
      cases op with
      | clz256 => cases hsort
      | not => rcases hsort with ⟨rfl⟩; exact ⟨.u64 (~~~xa), _, by simp [evalScalarExpr, heva]; rfl, rfl,
          fun f g t ls lg hm => MetalSIMT.ev_bitnot_ulong callEval f g t ls lg _ _ (haAll f g t ls lg hm)
            (lowerScalar_inferExprType g ls idxName idxVar boundVars a false hsa (htyM ls hm))⟩
      | neg => rcases hsort with ⟨rfl⟩; exact ⟨.u64 (0 - xa), _, by simp [evalScalarExpr, heva]; rfl, rfl,
          fun f g t ls lg hm => MetalSIMT.ev_neg_zero_sub_ulong callEval f g t ls lg _ _ (haAll f g t ls lg hm)
            (lowerScalar_inferExprType g ls idxName idxVar boundVars a false hsa (htyM ls hm))⟩
  | fma a b c iha ihb ihc =>
    simp only [inferScalarSort] at hsort
    cases hsa : inferScalarSort boundVars a <;> simp only [hsa] at hsort
    · cases hsort
    · cases hsb : inferScalarSort boundVars b <;> simp only [hsb] at hsort
      · cases hsort
      · cases hsc : inferScalarSort boundVars c <;> simp only [hsc] at hsort
        · cases hsort
        · rename_i sa sb sc
          cases sa <;> simp at hsort
          cases sb <;> simp at hsort
          cases sc <;> simp at hsort
          subst hsort
          rcases iha false hsa with ⟨_, _, heva, hva, haAll⟩
          rcases ihb false hsb with ⟨_, _, hevb, hvb, hbAll⟩
          rcases ihc false hsc with ⟨_, _, hevc, hvc, hcAll⟩
          rcases valOfSort_false hva with ⟨xa, rfl, rfl⟩
          rcases valOfSort_false hvb with ⟨xb, rfl, rfl⟩
          rcases valOfSort_false hvc with ⟨xc, rfl, rfl⟩
          exact ⟨.u64 (xa * xb + xc), (xa * xb + xc).toBitVec,
            by simp [evalScalarExpr, heva, hevb, hevc]; rfl, rfl, fun f g t ls lg hm =>
              MetalSIMT.ev_fma_compound_ulong callEval f g t ls lg _ _ _ _ _ _
                (haAll f g t ls lg hm) (hbAll f g t ls lg hm) (hcAll f g t ls lg hm)
                (lowerScalar_inferExprType g ls idxName idxVar boundVars a false hsa (htyM ls hm))
                (lowerScalar_inferExprType g ls idxName idxVar boundVars b false hsb (htyM ls hm))
                (lowerScalar_inferExprType g ls idxName idxVar boundVars c false hsc (htyM ls hm))⟩
  | select c t f ihc iht ihf =>
    simp only [inferScalarSort] at hsort
    cases hsc : inferScalarSort boundVars c <;> simp only [hsc] at hsort
    · cases hsort
    · cases hst : inferScalarSort boundVars t <;> simp only [hst] at hsort
      · cases hsort
      · cases hsf : inferScalarSort boundVars f <;> simp only [hsf] at hsort
        · cases hsort
        · rename_i sc st sf
          cases heq : (st == sf)
          · simp [heq] at hsort
          · simp only [heq, ite_true, Option.some.injEq] at hsort
            have hstf : st = sf := eq_of_beq heq
            subst hstf hsort
            rcases ihc sc hsc with ⟨_, _, hevc, hvc, hcAll⟩
            rcases iht st hst with ⟨vt, bvt, hevt, _, htAll⟩
            rcases ihf st hsf with ⟨vf, bvf, hevf, _, hfAll⟩
            cases sc
            · rcases valOfSort_false hvc with ⟨xc, rfl, rfl⟩
              refine ⟨if xc != 0 then vt else vf, if xc != 0 then bvt else bvf, ?_,
                by cases (xc != 0) <;> assumption, fun fl g td ls lg hm => ?_⟩
              · cases hxc : (xc != 0) <;> simp [evalScalarExpr, hevc, hxc, hevt, hevf]
              · rw [← MetalSIMT.bne_zero_bv_iff]
                exact MetalSIMT.ev_select_ne_zero callEval fl g td ls lg _ _ _ _ _ _
                  (hcAll fl g td ls lg hm) (htAll fl g td ls lg hm) (hfAll fl g td ls lg hm)
                  (lowerScalar_inferExprType g ls idxName idxVar boundVars c false hsc (htyM ls hm))
            · rcases valOfSort_true hvc with ⟨bc, rfl, rfl⟩
              refine ⟨if bc then vt else vf, if bc then bvt else bvf, ?_, by cases bc <;> assumption, fun fl g td ls lg hm => ?_⟩
              · cases bc <;> simp [evalScalarExpr, hevc, hevt, hevf]
              · have h := MetalSIMT.ev_select_ne_zero callEval fl g td ls lg _ _ _ _ _ _
                  (hcAll fl g td ls lg hm) (htAll fl g td ls lg hm) (hfAll fl g td ls lg hm)
                  (lowerScalar_inferExprType g ls idxName idxVar boundVars c true hsc (htyM ls hm))
                cases bc <;> exact h
  | binOp op l r ihl ihr =>
    simp only [inferScalarSort] at hsort
    cases hsl : inferScalarSort boundVars l <;> simp only [hsl] at hsort
    · cases hsort
    · cases hsr : inferScalarSort boundVars r <;> simp only [hsr] at hsort
      · cases hsort
      · rename_i sl sr
        cases sl <;> cases sr <;> try simp at hsort
        · rcases ihl false hsl with ⟨_, _, hevl, hvl, hlAll⟩
          rcases ihr false hsr with ⟨_, _, hevr, hvr, hrAll⟩
          rcases valOfSort_false hvl with ⟨xl, rfl, rfl⟩
          rcases valOfSort_false hvr with ⟨xr, rfl, rfl⟩
          obtain ⟨val, bv, hev, hvs, hmsl⟩ := lowerBinOpU64_eval callEval env idxName idxVar l r op s xl xr hsort hevl hevr
          exact ⟨val, bv, hev, hvs, fun fl g td ls lg hm => hmsl fl g td ls lg (hlAll fl g td ls lg hm) (hrAll fl g td ls lg hm)
            (lowerScalar_inferExprType g ls idxName idxVar boundVars l false hsl (htyM ls hm))
            (lowerScalar_inferExprType g ls idxName idxVar boundVars r false hsr (htyM ls hm))⟩
        · rcases ihl true hsl with ⟨_, _, hevl, hvl, hlAll⟩
          rcases ihr true hsr with ⟨_, _, hevr, hvr, hrAll⟩
          rcases valOfSort_true hvl with ⟨bl, rfl, rfl⟩
          rcases valOfSort_true hvr with ⟨br, rfl, rfl⟩
          cases op <;> simp [inferBinOpBool] at hsort
          subst hsort
          refine ⟨.bool (bl == br), if bl == br then 1#64 else 0#64, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
            fun fl g td ls lg hm => ?_⟩
          rw [← MetalSIMT.bool_bv_beq]
          exact MetalSIMT.ev_eq_cast_ulong callEval fl g td ls lg _ _ _ _ (hlAll fl g td ls lg hm) (hrAll fl g td ls lg hm)
            (lowerScalar_inferExprType g ls idxName idxVar boundVars l true hsl (htyM ls hm))
            (lowerScalar_inferExprType g ls idxName idxVar boundVars r true hsr (htyM ls hm))
/-- Expression-level soundness of `MetalLower.lowerScalar`: every well-sorted `LNIR.ScalarExpr`
evaluates in `MetalAst.evalExprWithCall` to the exact bitvector encoding of `LNIR.evalScalarExpr`,
preserving `MSLLocals` and `MSLAccess` epoch logs. -/
theorem lowerScalar_eval_sound
    (callEval : Nat → MetalAst.MSLGroupState → MetalAst.Dim3 → MetalAst.MSLLocals →
      List MetalAst.MSLAccess → String → MetalAst.MSLExprList → MetalAst.MSLOutcome MetalAst.MSLEval)
    (fuel : Nat) (g : MetalAst.MSLGroupState) (tid : MetalAst.Dim3) (ls : MetalAst.MSLLocals)
    (log : List MetalAst.MSLAccess) (env : VarEnv) (idxName : String) (idxVar : Nat) (boundVars : List Nat)
    (e : ScalarExpr) (s : Bool) (hsort : inferScalarSort boundVars e = some s)
    (hmatch : varEnvMatchesLocals env ls idxName idxVar boundVars) :
    ∃ (val : Val) (bv : BitVec 64), evalScalarExpr env e = .ok val ∧ valOfSort s val = some bv ∧
      MetalAst.evalExprWithCall callEval fuel g tid ls log (lowerScalar idxName idxVar e) =
        .ok { value := bv, fields := [], locals := ls, log := log } := by
  have henv : ∀ id ∈ boundVars, ∃ x : UInt64, env id = some (.u64 x) := fun id hmem => by
    rcases varEnvMatchesLocals_mem env ls idxName idxVar boundVars hmatch hmem with ⟨x, hx, _, _⟩
    exact ⟨x, hx⟩
  obtain ⟨val, bv, hev, hvs, hmsl⟩ := lowerScalar_eval_core callEval env idxName idxVar boundVars henv e s hsort
  exact ⟨val, bv, hev, hvs, hmsl fuel g tid ls log hmatch⟩

private theorem packInputDeviceBuffersGo_props (env : VarEnv) (st : HeapState) (len : Nat) :
    ∀ (inputs : List VarId) (idx : Nat) (bufs : List (Nat × MetalAst.ByteMemory)),
      packInputDeviceBuffersGo env st len idx inputs = some bufs →
      (∀ k, idx + inputs.length ≤ k → bufs.lookup k = none) ∧
      (∀ j < inputs.length, ∃ (words : List (BitVec 64)),
        bufs.lookup (idx + j) = some (MetalAst.ByteMemory.ofU64Words words) ∧ words.length = len ∧
        ∀ i (_ : i < len) (hwi : i < words.length),
          ∃ x : UInt64, readParInput env st inputs j i = .ok x ∧ words[i] = x.toBitVec)
  | [], _, bufs, h => by
    simp only [packInputDeviceBuffersGo_nil, Option.some.injEq] at h; subst h
    exact ⟨fun _ _ => rfl, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | v :: rest, idx, bufs, h => by
    rw [packInputDeviceBuffersGo_cons] at h
    cases hp : packOneDeviceBuffer env st len v with
    | none => simp [hp] at h
    | some mem0 =>
      rw [hp] at h; dsimp only at h
      cases ht : packInputDeviceBuffersGo env st len (idx + 1) rest with
      | none => simp [ht] at h
      | some tail =>
        rw [ht] at h; simp only [Option.some.injEq] at h; subst h
        unfold packOneDeviceBuffer at hp
        cases hv : env v with
        | none => simp [hv] at hp
        | some val =>
          cases val <;> simp only [hv] at hp <;> try cases hp
          all_goals
            rename_i bid
            cases hfind : st.findBuffer bid with
            | none => simp [hfind] at hp
            | some buf =>
              rw [hfind] at hp; dsimp only at hp
              by_cases hlenLe : len ≤ buf.data.size
              · simp only [hlenLe, ite_true, Option.some.injEq] at hp; subst hp
                rcases packInputDeviceBuffersGo_props env st len rest (idx + 1) tail ht with ⟨hhi, hmid⟩
                refine ⟨fun k hk => ?_, fun j hj => ?_⟩
                · simp only [List.length_cons] at hk
                  simp only [List.lookup, beq_eq_false_iff_ne.mpr (by omega : k ≠ idx)]
                  exact hhi k (by omega)
                · cases j with
                  | zero =>
                    let w0 := (List.range len).map fun i => (buf.data[i]?.getD 0).toBitVec
                    refine ⟨w0, by simp [Nat.add_zero, List.lookup, w0], by simp [w0], fun i hi _ => ?_⟩
                    have hiBuf : i < buf.data.size := Nat.lt_of_lt_of_le hi hlenLe
                    refine ⟨buf.data[i], ?_, by simp [w0, Array.getElem?_eq_getElem hiBuf]⟩
                    unfold readParInput; simp [hv, HeapState.readElem, hfind, hiBuf]
                  | succ j' =>
                    simp only [List.length_cons] at hj
                    rcases hmid j' (by omega) with ⟨wj, hlk, hwlen, hread⟩
                    have hadd : idx + (j' + 1) = (idx + 1) + j' := by omega
                    have hne : ((idx + 1) + j' == idx) = false := beq_eq_false_iff_ne.mpr (by omega)
                    refine ⟨wj, by simp only [List.lookup]; rw [hadd, hne]; exact hlk, hwlen, fun i hi hwi => ?_⟩
                    rcases hread i hi hwi with ⟨x, hr, hw⟩
                    refine ⟨x, ?_, hw⟩
                    unfold readParInput at hr ⊢; simp only [List.getElem?_cons_succ]
                    cases hget : rest[j']? with
                    | none => rw [hget] at hr; cases hr
                    | some _ => rw [hget] at hr; exact hr
              · simp [hlenLe] at hp

private theorem varEnvMatchesLocals_append_one (curEnv : VarEnv) (ls : MetalAst.MSLLocals)
    (idxName : String) (idxVar iv : VarId) (x : UInt64) (hivNe : iv ≠ idxVar)
    (hlk : ls.lookup? s!"v{iv}" = some x.toBitVec) (hty : ls.lookupType? s!"v{iv}" = some .ulong) :
    ∀ (vs : List VarId), iv ∉ vs → varEnvMatchesLocals curEnv ls idxName idxVar vs →
      varEnvMatchesLocals (curEnv.bind iv (.u64 x)) ls idxName idxVar (vs ++ [iv])
  | [], _, _ => by
    have hbeq : (iv == idxVar) = false := beq_eq_false_iff_ne.mpr hivNe
    refine ⟨⟨x, VarEnv.bind_self curEnv iv (.u64 x), ?_, ?_⟩, trivial⟩
    · simp only [hbeq, Bool.false_eq_true, ite_false]; exact hlk
    · simp only [hbeq, Bool.false_eq_true, ite_false]; exact hty
  | u :: us, hnot, ⟨⟨xu, hu, hlku, htyu⟩, htl⟩ => by
    have hne : u ≠ iv := fun heq => hnot (heq ▸ .head us)
    refine ⟨⟨xu, (VarEnv.bind_ne curEnv iv u (.u64 x) (beq_eq_false_iff_ne.mpr hne)).trans hu, hlku, htyu⟩,
      varEnvMatchesLocals_append_one curEnv ls idxName idxVar iv x hivNe hlk hty us (fun hm => hnot (.tail u hm)) htl⟩

private theorem bindCustomParInputs_props (env : VarEnv) (st : HeapState) (inputs : List VarId)
    (cx : Nat) (inWords : Nat → List (BitVec 64))
    (hread : ∀ j < inputs.length, ∃ (hc : cx < (inWords j).length) (x : UInt64),
      readParInput env st inputs j cx = .ok x ∧ (inWords j)[cx] = x.toBitVec) :
    ∀ (rem : List VarId) (k0 : Nat) (curEnv : VarEnv) (ls : MetalAst.MSLLocals)
      (idxVar : VarId) (prior : List VarId),
      k0 + rem.length = inputs.length → (idxVar :: (prior ++ rem)).Nodup →
      varEnvMatchesLocals curEnv ls "gid64" idxVar (idxVar :: prior) →
      (∀ m (hm : m < rem.length), ∃ (hc : cx < (inWords (k0 + m)).length),
        ls.lookup? s!"v{rem[m]'hm}" = some ((inWords (k0 + m))[cx]) ∧
        ls.lookupType? s!"v{rem[m]'hm}" = some .ulong) →
      ∃ kEnv : VarEnv, bindCustomParInputs env st inputs cx curEnv k0 rem = .ok kEnv ∧
        varEnvMatchesLocals kEnv ls "gid64" idxVar (idxVar :: (prior ++ rem))
  | [], _, curEnv, _, _, _, _, _, hcur, _ => by simp only [List.append_nil, bindCustomParInputs]; exact ⟨curEnv, rfl, hcur⟩
  | iv :: rest, k0, curEnv, ls, idxVar, prior, hklen, hnd, hcur, hrem => by
    simp only [List.length_cons] at hklen
    rcases hread k0 (by omega) with ⟨_, x0, hr0, hw0⟩
    rcases hrem 0 (by simp) with ⟨_, hlk0, hty0⟩
    simp only [Nat.add_zero, List.getElem_cons_zero] at hlk0 hty0
    rw [hw0] at hlk0
    have hndCons := List.nodup_cons.mp hnd
    have hivNeIdx : iv ≠ idxVar := fun heq => hndCons.1 (heq ▸ List.mem_append_right prior (.head rest))
    have hivNotHead : iv ∉ (idxVar :: prior) := by
      rcases List.nodup_append.mp hndCons.2 with ⟨_, _, hdisj⟩
      intro hm; rcases List.mem_cons.mp hm with h1 | h2
      · exact hivNeIdx h1
      · exact hdisj iv h2 iv (.head rest) rfl
    have hnextMatch := varEnvMatchesLocals_append_one curEnv ls "gid64" idxVar iv x0
      hivNeIdx hlk0 hty0 (idxVar :: prior) hivNotHead hcur
    simp only [List.cons_append] at hnextMatch
    have happEq : prior ++ (iv :: rest) = (prior ++ [iv]) ++ rest := by simp
    rw [happEq] at hnd ⊢
    obtain ⟨kEnv, hbindRest, hmatchFinal⟩ := bindCustomParInputs_props env st inputs cx inWords hread rest (k0 + 1)
      (curEnv.bind iv (.u64 x0)) ls idxVar (prior ++ [iv]) (by omega) hnd hnextMatch (fun m hm => by
        rcases hrem (m + 1) (by simp; omega) with ⟨hcm, hlkm, htym⟩
        have hadd : k0 + (m + 1) = (k0 + 1) + m := by omega
        simp only [List.getElem_cons_succ, hadd] at hcm hlkm htym
        exact ⟨hcm, hlkm, htym⟩)
    exact ⟨kEnv, by unfold bindCustomParInputs; rw [hr0]; exact hbindRest, hmatchFinal⟩

private theorem evalParKernelLoop_of_all (env : VarEnv) (st : HeapState) (inputs : List VarId)
    (len : Nat) (k : ParallelKernelKind) (specU64 : Nat → UInt64) :
    ∀ (idxs : List Nat), (∀ i ∈ idxs, evalParKernelElem env st inputs len k i = .ok (specU64 i)) →
      ∃ elems : List UInt64, evalParKernelLoop env st inputs len k idxs = .ok elems ∧ elems = idxs.map specU64
  | [], _ => ⟨[], rfl, rfl⟩
  | i :: is, hall => by
    obtain ⟨xs, hxs, hmap⟩ := evalParKernelLoop_of_all env st inputs len k specU64 is (fun j hj => hall j (.tail i hj))
    refine ⟨specU64 i :: xs, ?_, by simp [hmap]⟩
    unfold evalParKernelLoop; rw [hall i (.head is), hxs]

/-- End-to-end 1D SIMT lowering soundness (`LNIR.ParallelKernelKind` -> `MetalAst.MSLModule`):
for every well-formed `wfMetalKernel k` whose input array buffers are packed via
`packInputDeviceBuffers`, `LNIR.evalParKernelLoop` succeeds over `0 .. len - 1` and
`MetalAst.evalMSLKernel` on the lowered kernel in `lowerToMetal name k` terminates without
data races or undefined behavior, writing the exact 64-bit word `elems[i].toBitVec` at every
output element `i < len`. -/
theorem lowerToMetal_evalMSLKernel_sound
    (env : VarEnv) (st : HeapState) (inputs : List VarId) (name : String) (k : ParallelKernelKind)
    (len nGroups groupSize : Nat) (inBufs : List (Nat × MetalAst.ByteMemory))
    (hwf : wfMetalKernel k = true) (harity : inputs.length = kernelArity k)
    (hpack : packInputDeviceBuffers env st inputs len = some inBufs)
    (hlenCov : len ≤ nGroups * groupSize) (hgrid32 : nGroups * groupSize < 2 ^ 32) :
    ∃ (elems : List UInt64) (kern : MetalAst.MSLKernelDecl)
      (devBufsF : List (Nat × MetalAst.ByteMemory)) (outMemF : MetalAst.ByteMemory),
      (lowerToMetal name k).kernels = [kern] ∧
      evalParKernelLoop env st inputs len k (List.range len) = .ok elems ∧ elems.length = len ∧
      MetalAst.evalMSLKernel (groupStepsForKind groupSize k) kern
        { x := nGroups, y := 1, z := 1 } { x := groupSize, y := 1, z := 1 }
        (mkDeviceBuffers inBufs (kernelArity k) len)
        (mkConstLenBuffers (kernelArity k) len) [] [] = .ok devBufsF ∧
      devBufsF.lookup (kernelArity k) = some outMemF ∧
      (∀ (i : Nat) (hi : i < elems.length), outMemF.readU64Word? i = some (elems[i]'hi).toBitVec) := by
  have hlen64 : len * 8 ≤ 2 ^ 64 := by omega
  rcases packInputDeviceBuffersGo_props env st len inputs 0 inBufs hpack with ⟨hhi, hmid⟩
  have hinOutNone : inBufs.lookup (kernelArity k) = none := hhi (kernelArity k) (by omega)
  let inWords : Nat → List (BitVec 64) := fun j =>
    (List.range len).map fun i => match readParInput env st inputs j i with | .ok x => x.toBitVec | .error _ => 0#64
  have hinWordsLen : ∀ j, (inWords j).length = len := fun _ => by simp [inWords]
  have hinLookup : ∀ j < kernelArity k,
      inBufs.lookup j = some (MetalAst.ByteMemory.ofU64Words (inWords j)) ∧
      (inWords j).length = len := by
    intro j hj
    rcases hmid j (by omega) with ⟨words, hlk, hwlen, hrd⟩
    simp only [Nat.zero_add] at hlk
    have heqW : words = inWords j := by
      apply List.ext_getElem (by simp [hwlen, inWords])
      intro i hi1 _
      rcases hrd i (by omega) hi1 with ⟨x, hrx, hwx⟩
      simp [inWords, hrx, hwx]
    rw [heqW] at hlk
    exact ⟨hlk, hinWordsLen j⟩
  have hreadElem : ∀ j < kernelArity k, ∀ i < len,
      ∃ (hc : i < (inWords j).length) (x : UInt64),
        readParInput env st inputs j i = .ok x ∧ (inWords j)[i]'hc = x.toBitVec := by
    intro j hj i hi
    rcases hmid j (by omega) with ⟨_, _, hwlen, hrd⟩
    rcases hrd i hi (by omega) with ⟨x, hrx, _⟩
    exact ⟨by simp [inWords, hi], x, hrx, by simp [inWords, hrx]⟩
  let specU64 : Nat → UInt64 := fun i =>
    match evalParKernelElem env st inputs len k i with
    | .ok v => v
    | .error _ => 0
  have ⟨stepsInner, inner, hparams, hshared, hbody, hfuel, hInner, helemAll⟩ :
      ∃ (stepsInner : Nat) (inner : List MetalAst.MSLStmt),
        (lowerKind name k).params = MetalSIMT.stdKernelParams (kernelArity k) ∧
        (lowerKind name k).sharedDecls = [] ∧
        (lowerKind name k).body =
          [MetalAst.MSLStmt.ifElse
            (.lt (.cast .ulong (.var "gid")) (.var "n"))
            (MetalAst.MSLBlock.ofList inner) .nil, .returnStmt] ∧
        groupSize * (stepsInner + 2) ≤ groupStepsForKind groupSize k ∧
        MetalSIMT.LaneInnerSpec (kernelArity k) len stepsInner inWords
          (fun i => (specU64 i).toBitVec) inner ∧
        (∀ i < len, evalParKernelElem env st inputs len k i = .ok (specU64 i)) := by
    cases k with
    | mapScaleAdd scale bias =>
      refine ⟨1, [storeOut (.add (.mul (elem "in0") (.immU64 scale.toBitVec)) (.immU64 bias.toBitVec))],
        rfl, rfl, rfl, by simp [groupStepsForKind]; omega, ?_, ?_⟩
      · refine MetalSIMT.laneInnerSpec_congr (MetalSIMT.laneInner_mapScaleAdd len scale.toBitVec bias.toBitVec inWords) ?_
        intro cx hcx
        rcases hreadElem 0 (by simp [kernelArity]) cx hcx with ⟨hc0, x, hrx, hwx⟩
        simp [specU64, evalParKernelElem, hrx, dite_eq_left_of_eq_true (eq_true hc0), hwx]
      · intro i hi
        rcases hreadElem 0 (by simp [kernelArity]) i hi with ⟨_, x, hrx, _⟩
        simp [specU64, evalParKernelElem, hrx]
    | zipAdd =>
      refine ⟨1, [storeOut (.add (elem "in0") (elem "in1"))], rfl, rfl, rfl, by simp [groupStepsForKind]; omega,
        MetalSIMT.laneInnerSpec_congr (MetalSIMT.laneInner_zipAdd len inWords) fun cx hcx => ?_, fun i hi => ?_⟩
      · rcases hreadElem 0 (by simp [kernelArity]) cx hcx with ⟨hc0, x, hrx, hwx⟩
        rcases hreadElem 1 (by simp [kernelArity]) cx hcx with ⟨hc1, y, hry, hwy⟩
        simp [specU64, evalParKernelElem, hrx, hry, dite_eq_left_of_eq_true (eq_true hc0),
          dite_eq_left_of_eq_true (eq_true hc1), hwx, hwy]
      · rcases hreadElem 0 (by simp [kernelArity]) i hi with ⟨_, x, hrx, _⟩
        rcases hreadElem 1 (by simp [kernelArity]) i hi with ⟨_, y, hry, _⟩
        simp [specU64, evalParKernelElem, hrx, hry]
    | dotProduct =>
      simp [wfMetalKernel] at hwf
    | zipMul =>
      refine ⟨1, [storeOut (.mul (elem "in0") (elem "in1"))], rfl, rfl, rfl, by simp [groupStepsForKind]; omega,
        MetalSIMT.laneInnerSpec_congr (MetalSIMT.laneInner_zipMul len inWords) fun cx hcx => ?_, fun i hi => ?_⟩
      · rcases hreadElem 0 (by simp [kernelArity]) cx hcx with ⟨hc0, x, hrx, hwx⟩
        rcases hreadElem 1 (by simp [kernelArity]) cx hcx with ⟨hc1, y, hry, hwy⟩
        simp [specU64, evalParKernelElem, hrx, hry, dite_eq_left_of_eq_true (eq_true hc0),
          dite_eq_left_of_eq_true (eq_true hc1), hwx, hwy]
      · rcases hreadElem 0 (by simp [kernelArity]) i hi with ⟨_, x, hrx, _⟩
        rcases hreadElem 1 (by simp [kernelArity]) i hi with ⟨_, y, hry, _⟩
        simp [specU64, evalParKernelElem, hrx, hry]
    | saxpy alpha =>
      refine ⟨1, [storeOut (.add (.mul (.immU64 alpha.toBitVec) (elem "in0")) (elem "in1"))], rfl, rfl, rfl,
        by simp [groupStepsForKind]; omega,
        MetalSIMT.laneInnerSpec_congr (MetalSIMT.laneInner_saxpy len alpha.toBitVec inWords) fun cx hcx => ?_, fun i hi => ?_⟩
      · rcases hreadElem 0 (by simp [kernelArity]) cx hcx with ⟨hc0, x, hrx, hwx⟩
        rcases hreadElem 1 (by simp [kernelArity]) cx hcx with ⟨hc1, y, hry, hwy⟩
        simp [specU64, evalParKernelElem, hrx, hry, dite_eq_left_of_eq_true (eq_true hc0),
          dite_eq_left_of_eq_true (eq_true hc1), hwx, hwy]
      · rcases hreadElem 0 (by simp [kernelArity]) i hi with ⟨_, x, hrx, _⟩
        rcases hreadElem 1 (by simp [kernelArity]) i hi with ⟨_, y, hry, _⟩
        simp [specU64, evalParKernelElem, hrx, hry]
    | stencil1D3Pt wL wC wR =>
      have hst : ∀ cx < len, ∃ v : UInt64, evalParKernelElem env st inputs len (.stencil1D3Pt wL wC wR) cx = .ok v ∧
          (if (cx == 0 || decide (len ≤ cx + 1)) = true then
            if h0 : cx < (inWords 0).length then (inWords 0)[cx] else 0#64
          else if hL : cx - 1 < (inWords 0).length then
            if hC : cx < (inWords 0).length then
              if hR : cx + 1 < (inWords 0).length then
                wL.toBitVec * (inWords 0)[cx - 1] + wC.toBitVec * (inWords 0)[cx] + wR.toBitVec * (inWords 0)[cx + 1]
              else 0#64 else 0#64 else 0#64) = v.toBitVec := by
        intro cx hcx
        rcases hreadElem 0 (by simp [kernelArity]) cx hcx with ⟨hcC, xC, hrC, hwC⟩
        cases hedge : (cx == 0 || decide (cx + 1 ≥ len))
        · have hcxPos : 0 < cx := by cases cx with | zero => simp at hedge | succ _ => omega
          have hcx1Lt : cx + 1 < len := by
            rcases Bool.or_eq_false_iff.mp hedge with ⟨_, h2⟩; simp only [decide_eq_false_iff_not] at h2; omega
          rcases hreadElem 0 (by simp [kernelArity]) (cx - 1) (by omega) with ⟨hcL, xL, hrL, hwL⟩
          rcases hreadElem 0 (by simp [kernelArity]) (cx + 1) hcx1Lt with ⟨hcR, xR, hrR, hwR⟩
          simp only [ge_iff_le] at hedge
          exact ⟨wL * xL + wC * xC + wR * xR, by simp [evalParKernelElem, hedge, hrL, hrC, hrR],
            by rw [ite_eq_right Bool.false_ne_true, dite_eq_left hcL, dite_eq_left hcC, dite_eq_left hcR, hwL, hwC, hwR]; rfl⟩
        · simp only [ge_iff_le] at hedge
          exact ⟨xC, by simp [evalParKernelElem, hedge, hrC],
            by rw [ite_eq_left rfl, dite_eq_left hcC, hwC]⟩
      let ii := MetalAst.MSLExpr.cast .ulong (.var "gid")
      let edge := MetalAst.MSLExpr.logOr (.eq ii (u 0)) (.ge (.add ii (u 1)) (.var "n"))
      let interior := MetalAst.MSLExpr.add (.add (.mul (.immU64 wL.toBitVec) (.index "in0" (.sub ii (u 1))))
        (.mul (.immU64 wC.toBitVec) (elem "in0"))) (.mul (.immU64 wR.toBitVec) (.index "in0" (.add ii (u 1))))
      refine ⟨2, [.ifElse edge (.cons (storeOut (elem "in0")) .nil) (.cons (storeOut interior) .nil)],
        rfl, rfl, rfl, by simp [groupStepsForKind]; omega, ?_, ?_⟩
      · refine MetalSIMT.laneInnerSpec_congr
          (MetalSIMT.laneInner_stencil1D3Pt len wL.toBitVec wC.toBitVec wR.toBitVec inWords) (fun cx hcx => ?_)
        rcases hst cx hcx with ⟨v, hv, hsw⟩
        dsimp only [specU64]; rw [hv]; exact hsw
      · intro i hi
        rcases hst i hi with ⟨v, hv, _⟩
        dsimp only [specU64]; rw [hv]
    | customScalar idxVar inVars body =>
      simp only [wfMetalKernel, Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_exists] at hwf
      rcases hwf with ⟨⟨hnodup, hnotMem⟩, ⟨s, hsort⟩⟩
      simp only [kernelArity] at harity hinLookup hreadElem hinOutNone ⊢
      have hndAll : (idxVar :: inVars).Nodup := List.nodup_cons.mpr ⟨hnotMem, hnodup⟩
      have hbindU64 : ∀ cx < len, ∃ kEnv : VarEnv,
          bindCustomParInputs env st inputs cx (env.bind idxVar (.u64 cx.toUInt64)) 0 inVars = .ok kEnv ∧
          (∀ id ∈ idxVar :: inVars, ∃ x : UInt64, kEnv id = some (.u64 x)) := by
        intro cx hcx
        suffices h : ∀ (rem : List VarId) (k0 : Nat) (cur : VarEnv), k0 + rem.length = inputs.length →
            ∃ kEnv, bindCustomParInputs env st inputs cx cur k0 rem = .ok kEnv ∧
              ∀ id, (∃ x, cur id = some (.u64 x)) ∨ id ∈ rem → ∃ x, kEnv id = some (.u64 x) from by
          rcases h inVars 0 (env.bind idxVar (.u64 cx.toUInt64)) (by omega) with ⟨kEnv, hb, hall⟩
          refine ⟨kEnv, hb, fun id hid => hall id ?_⟩
          rcases List.mem_cons.mp hid with rfl | htl
          · exact Or.inl ⟨cx.toUInt64, VarEnv.bind_self env id (.u64 cx.toUInt64)⟩
          · exact Or.inr htl
        intro rem; induction rem with
        | nil => intro _ cur _; exact ⟨cur, rfl, fun _ hid => hid.elim id (fun h => nomatch h)⟩
        | cons iv rest ih =>
          intro k0 cur hk; simp only [List.length_cons] at hk
          rcases hreadElem k0 (by omega) cx hcx with ⟨_, x0, hr0, _⟩
          rcases ih (k0 + 1) (cur.bind iv (.u64 x0)) (by omega) with ⟨kEnv, hbRest, hall⟩
          refine ⟨kEnv, by unfold bindCustomParInputs; rw [hr0]; exact hbRest, fun id hid => hall id ?_⟩
          rcases hid with ⟨x, hx⟩ | hmem
          · by_cases heq : id = iv
            · subst heq; exact Or.inl ⟨x0, VarEnv.bind_self cur id (.u64 x0)⟩
            · exact Or.inl ⟨x, (VarEnv.bind_ne cur iv id (.u64 x0) (beq_eq_false_iff_ne.mpr heq)).trans hx⟩
          · exact (List.mem_cons.mp hmem).elim (fun h => Or.inl ⟨x0, h ▸ VarEnv.bind_self cur iv (.u64 x0)⟩) Or.inr
      let loads := (List.range inVars.length).map fun m =>
        MetalAst.MSLStmt.varDecl .ulong s!"v{inVars[m]?.getD 0}" (elem s!"in{m}")
      refine ⟨inVars.length + 2,
        [MetalAst.MSLStmt.varDecl .ulong "gid64" (.cast .ulong (.var "gid"))] ++
          loads ++ [storeOut (lowerScalar "gid64" idxVar body)],
        rfl, rfl, rfl,
        by dsimp [groupStepsForKind]
           exact Nat.le_trans (Nat.mul_le_mul_left groupSize (by omega)) (Nat.le_add_right _ 2), ?_, ?_⟩
      · apply MetalSIMT.laneInner_varDecls_storeOut inVars len inWords
          (fun i => (specU64 i).toBitVec) (lowerScalar "gid64" idxVar body) hnodup
        intro g tid ls cx hcxLen hcx32 hgidV hgidT hvars
        have hcur0 : varEnvMatchesLocals (env.bind idxVar (.u64 cx.toUInt64)) ls "gid64" idxVar [idxVar] :=
          ⟨⟨cx.toUInt64, VarEnv.bind_self env idxVar _, by simp [MetalSIMT.u64_ofNat_toBitVec cx hcx32, hgidV],
            by simp [hgidT]⟩, trivial⟩
        have hrem0 : ∀ m (hm : m < inVars.length), ∃ (hc : cx < (inWords (0 + m)).length),
            ls.lookup? s!"v{inVars[m]'hm}" = some ((inWords (0 + m))[cx]'hc) ∧
            ls.lookupType? s!"v{inVars[m]'hm}" = some .ulong := by
          intro m hm
          have hc : cx < (inWords m).length := by rw [hinWordsLen]; exact hcxLen
          have ⟨hv, ht⟩ := hvars m hm hc
          simp only [Nat.zero_add]; exact ⟨hc, hv, ht⟩
        obtain ⟨kEnv, hbind, hmatch⟩ := bindCustomParInputs_props env st inputs cx inWords
          (fun j hj => hreadElem j (by omega) cx hcxLen)
          inVars 0 (env.bind idxVar (.u64 cx.toUInt64)) ls idxVar [] (by omega) hndAll hcur0 hrem0
        simp only [List.nil_append] at hmatch
        obtain ⟨val, bv, hevBody, hvs, hmsl⟩ :=
          lowerScalar_eval_sound MetalAst.kernelCallEval
            (MetalAst.effectiveCalleeFuel g) g tid ls g.epochLog
            kEnv "gid64" idxVar (idxVar :: inVars) body s hsort hmatch
        cases s with
        | false =>
          rcases valOfSort_false hvs with ⟨v, rfl, rfl⟩
          have hspec : specU64 cx = v := by simp [specU64, evalParKernelElem, hbind, hevBody]
          rw [hspec]; exact hmsl
        | true =>
          rcases valOfSort_true hvs with ⟨b, rfl, rfl⟩
          have hspec : specU64 cx = (if b then 1 else 0) := by simp [specU64, evalParKernelElem, hbind, hevBody]
          have hbv : (specU64 cx).toBitVec = (if b then 1#64 else 0#64) := by rw [hspec]; cases b <;> rfl
          rw [hbv]; exact hmsl
      · intro i hi
        obtain ⟨kEnv, hbind, henvK⟩ := hbindU64 i hi
        obtain ⟨val, bv, hevBody, hvs, _⟩ :=
          lowerScalar_eval_core MetalAst.kernelCallEval
            kEnv "gid64" idxVar (idxVar :: inVars) henvK body s hsort
        cases s with
        | false =>
          rcases valOfSort_false hvs with ⟨v, rfl, rfl⟩
          simp [specU64, evalParKernelElem, hbind, hevBody]
        | true =>
          rcases valOfSort_true hvs with ⟨b, rfl, rfl⟩
          simp [specU64, evalParKernelElem, hbind, hevBody]
  obtain ⟨elems, hloop, heqMap⟩ := evalParKernelLoop_of_all env st inputs len k specU64 (List.range len)
    (fun i hi => helemAll i (List.mem_range.mp hi))
  obtain ⟨devBufsF, outMemF, hmsl, houtF, hwords⟩ :=
    MetalSIMT.evalMSLKernel_guarded_1d
      (kernelArity k) len nGroups groupSize stepsInner (groupStepsForKind groupSize k)
      (lowerKind name k) inBufs inWords (fun i => (specU64 i).toBitVec) inner
      hparams hshared hbody hInner hlen64 hlenCov hgrid32 hfuel hinLookup hinOutNone
  refine ⟨elems, lowerKind name k, devBufsF, outMemF, rfl, hloop, by simp [heqMap], hmsl, houtF, ?_⟩
  intro i hi
  have hiLen : i < len := by simpa [heqMap] using hi
  have hget : elems[i]'hi = specU64 i := by subst heqMap; simp
  rw [hget]
  exact hwords i hiLen

end LeanNative.Proofs.MetalLowerProofs
