import LeanNative.Proofs.SymbolicTVRefinesCtxSoundness

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Transform

theorem evalVarList_of_all_bound {ctx : SymRefinesCtx} {env : VarEnv}
    (hctx : CtxHolds ctx env) (fs : List VarId)
    (hall : fs.all (fun f => ctx.boundVars.contains f) = true) :
    ∃ vals : List Val, evalVarList env fs = .ok vals := by
  induction fs with
  | nil => exact ⟨[], rfl⟩
  | cons f rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨vf, hvf⟩ := hctx.1 f hall.1
    obtain ⟨vrest, hvrest⟩ := ih hall.2
    exact ⟨vf :: vrest, by simp [evalVarList, hvf, hvrest]⟩

theorem evalVarList_index_eq (env : VarEnv) (fs : List VarId) (vals : List Val)
    (idx : Nat) (fVar : VarId)
    (hevl : evalVarList env fs = .ok vals)
    (hidx : fs[idx]? = some fVar) :
    ∃ val : Val, vals[idx]? = some val ∧ env fVar = some val := by
  induction fs generalizing vals idx with
  | nil => simp at hidx
  | cons f rest ih =>
    simp only [evalVarList] at hevl
    cases hf : env f with
    | none => simp [hf] at hevl
    | some vf =>
      rw [hf] at hevl
      cases hrest : evalVarList env rest with
      | error _ => simp [hrest] at hevl
      | ok vrest =>
        rw [hrest] at hevl
        injection hevl with hv; subst hv
        cases idx with
        | zero =>
          simp only [List.getElem?_cons_zero] at hidx ⊢
          injection hidx with hfeq; subst hfeq
          exact ⟨vf, rfl, hf⟩
        | succ i =>
          simp only [List.getElem?_cons_succ] at hidx ⊢
          exact ih vrest i hrest hidx

theorem CtxHolds.afterMkTupleLet_sound {ctx : SymRefinesCtx} {env : VarEnv}
    (hctx : CtxHolds ctx env) (dst : VarId) (fs : List VarId) (vals : List Val)
    (hevl : evalVarList env fs = .ok vals) :
    CtxHolds (ctx.afterMkTupleLet dst fs) (env.bind dst (.tuple vals)) := by
  have hb := hctx.addBoundVars_of_evalVarList fs vals hevl
  have hk := (hb.killVar_bind dst (.tuple vals)).addBound_of_some dst (.tuple vals)
    (VarEnv.bind_self env dst (.tuple vals))
  unfold SymRefinesCtx.afterMkTupleLet
  dsimp only
  cases hfc : fs.contains dst
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, ?_⟩
    intro tf htf
    dsimp only at htf
    rw [List.mem_cons] at htf
    rcases htf with rfl | hrest
    · refine ⟨vals, VarEnv.bind_self env dst (.tuple vals), ?_⟩
      rw [evalVarList_bind_not_contains env dst (.tuple vals) fs hfc]
      exact hevl
    · exact hk.2.2.2.2 tf (dropClobberedTuples_mem dst tf _ hrest).2.2
  · simp only [↓reduceIte]
    exact hk

theorem evalScalarExpr_bind_not_uses (env : VarEnv) (dst : VarId) (val : Val) (e : ScalarExpr)
    (hnu : scalarExprUsesVar dst e = false) :
    evalScalarExpr (env.bind dst val) e = evalScalarExpr env e := by
  induction e with
  | constU64 _ | constBool _ => rfl
  | var id =>
    simp only [scalarExprUsesVar] at hnu
    simp only [evalScalarExpr, VarEnv.bind_ne env dst id val hnu]
  | binOp op l r ihl ihr =>
    simp only [scalarExprUsesVar, Bool.or_eq_false_iff] at hnu
    simp only [evalScalarExpr, ihl hnu.1, ihr hnu.2]
  | unaryOp op a iha =>
    simp only [scalarExprUsesVar] at hnu
    simp only [evalScalarExpr, iha hnu]
  | select c t f ihc iht ihf =>
    simp only [scalarExprUsesVar, Bool.or_eq_false_iff] at hnu
    simp only [evalScalarExpr, ihc hnu.1.1, iht hnu.1.2, ihf hnu.2]
  | fma a b c iha ihb ihc =>
    simp only [scalarExprUsesVar, Bool.or_eq_false_iff] at hnu
    simp only [evalScalarExpr, iha hnu.1.1, ihb hnu.1.2, ihc hnu.2]

theorem evalExpr_bind_not_uses (env : VarEnv) (st : HeapState) (dst : VarId) (val : Val)
    (e : LNIRExpr) (hnu : exprUsesVar dst e = false) :
    evalExpr (env.bind dst val) st e = evalExpr env st e := by
  cases e with
  | scalar se =>
    simp only [exprUsesVar] at hnu
    simp only [evalExpr, evalScalarExpr_bind_not_uses env dst val se hnu]
  | constU256 _ => rfl
  | mulDivDown a b d =>
    simp only [exprUsesVar, Bool.or_eq_false_iff] at hnu
    simp only [evalExpr, VarEnv.bind_ne env dst a val hnu.1.1,
      VarEnv.bind_ne env dst b val hnu.1.2, VarEnv.bind_ne env dst d val hnu.2]
  | mulDivUp a b d =>
    simp only [exprUsesVar, Bool.or_eq_false_iff] at hnu
    simp only [evalExpr, VarEnv.bind_ne env dst a val hnu.1.1,
      VarEnv.bind_ne env dst b val hnu.1.2, VarEnv.bind_ne env dst d val hnu.2]
  | storageLoad m s =>
    simp only [exprUsesVar, Bool.or_eq_false_iff] at hnu
    simp only [evalExpr, VarEnv.bind_ne env dst m val hnu.1, VarEnv.bind_ne env dst s val hnu.2]
  | storageStore m s v =>
    simp only [exprUsesVar, Bool.or_eq_false_iff] at hnu
    simp only [evalExpr, VarEnv.bind_ne env dst m val hnu.1.1,
      VarEnv.bind_ne env dst s val hnu.1.2, VarEnv.bind_ne env dst v val hnu.2]
  | mkTuple fs =>
    simp only [exprUsesVar] at hnu
    simp only [evalExpr, evalVarList_bind_not_contains env dst val fs hnu]
  | projTuple tv idx =>
    simp only [exprUsesVar] at hnu
    simp only [evalExpr, VarEnv.bind_ne env dst tv val hnu]
  | allocCtor tag ofs sfs =>
    simp only [exprUsesVar, Bool.or_eq_false_iff] at hnu
    simp only [evalExpr, evalVarList_bind_not_contains env dst val ofs hnu.1,
      evalVarList_bind_not_contains env dst val sfs hnu.2]
  | ctorGetObj cv idx =>
    simp only [exprUsesVar] at hnu
    simp only [evalExpr, evalCtorGet, VarEnv.bind_ne env dst cv val hnu]
  | ctorGetScalar cv idx ty =>
    simp only [exprUsesVar] at hnu
    simp only [evalExpr, evalCtorGet, VarEnv.bind_ne env dst cv val hnu]
  | isExclusive ov =>
    simp only [exprUsesVar] at hnu
    simp only [evalExpr, VarEnv.bind_ne env dst ov val hnu]
  | sarrayLen av =>
    simp only [exprUsesVar] at hnu
    simp only [evalExpr, VarEnv.bind_ne env dst av val hnu]
  | sarrayDataPtr av ety =>
    simp only [exprUsesVar] at hnu
    simp only [evalExpr, VarEnv.bind_ne env dst av val hnu]
  | sarrayEnsureExclusive av ety =>
    simp only [exprUsesVar] at hnu
    simp only [evalExpr, VarEnv.bind_ne env dst av val hnu]
  | sarrayGet av iv ety =>
    simp only [exprUsesVar, Bool.or_eq_false_iff] at hnu
    simp only [evalExpr, VarEnv.bind_ne env dst av val hnu.1, VarEnv.bind_ne env dst iv val hnu.2]
  | sarraySet av iv vv ety =>
    simp only [exprUsesVar, Bool.or_eq_false_iff] at hnu
    simp only [evalExpr, VarEnv.bind_ne env dst av val hnu.1.1,
      VarEnv.bind_ne env dst iv val hnu.1.2, VarEnv.bind_ne env dst vv val hnu.2]
  | rawLoad pv iv ety =>
    simp only [exprUsesVar, Bool.or_eq_false_iff] at hnu
    simp only [evalExpr, VarEnv.bind_ne env dst pv val hnu.1, VarEnv.bind_ne env dst iv val hnu.2]
  | boxScalar vv ty =>
    simp only [exprUsesVar] at hnu
    simp only [evalExpr, VarEnv.bind_ne env dst vv val hnu]
  | unboxScalar bv ty =>
    simp only [exprUsesVar] at hnu
    simp only [evalExpr, VarEnv.bind_ne env dst bv val hnu]
  | call fn args rty ext =>
    simp only [exprUsesVar] at hnu
    simp only [evalExpr, evalVarList_bind_not_contains env dst val args hnu]

theorem VarEnv.bind_overwrite (env : VarEnv) (x : VarId) (v1 v2 : Val) :
    (env.bind x v1).bind x v2 = env.bind x v2 := by
  funext y
  unfold VarEnv.bind
  split <;> rfl

theorem VarEnv.bind_comm (env : VarEnv) (x y : VarId) (vx vy : Val) (hne : x ≠ y) :
    (env.bind x vx).bind y vy = (env.bind y vy).bind x vx := by
  funext z
  unfold VarEnv.bind
  by_cases hzy : (z == y) = true
  · rw [beq_iff_eq] at hzy; subst hzy
    have hzx : (z == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
    simp [hzx]
  · simp [hzy]

theorem readParInput_bind_not_contains (env : VarEnv) (st : HeapState) (dst : VarId) (val : Val)
    (inputs : List VarId) (argIdx elemIdx : Nat) (hnc : inputs.contains dst = false) :
    readParInput (env.bind dst val) st inputs argIdx elemIdx =
    readParInput env st inputs argIdx elemIdx := by
  unfold readParInput
  cases hi : inputs[argIdx]? with
  | none => rfl
  | some v =>
    have hmem : v ∈ inputs := List.mem_of_getElem? hi
    have hvd : (v == dst) = false := by
      cases h : (v == dst)
      · rfl
      · rw [beq_iff_eq] at h; subst h
        rw [List.contains_iff_mem.mpr hmem] at hnc; nomatch hnc
    simp only [VarEnv.bind_ne env dst v val hvd]

theorem bindCustomParInputs_bind_dead (env : VarEnv) (st : HeapState) (dst : VarId) (val : Val)
    (inputs : List VarId) (elemIdx : Nat) (curEnv1 curEnv2 : VarEnv) (argIdx : Nat)
    (inVars : List VarId) (body : ScalarExpr)
    (hnc : inputs.contains dst = false)
    (hcur : ∀ z, scalarExprUsesVar z body = true → curEnv1 z = curEnv2 z) :
    match bindCustomParInputs (env.bind dst val) st inputs elemIdx curEnv1 argIdx inVars,
          bindCustomParInputs env st inputs elemIdx curEnv2 argIdx inVars with
    | .ok kEnv1, .ok kEnv2 => ∀ z, scalarExprUsesVar z body = true → kEnv1 z = kEnv2 z
    | .error e1, .error e2 => e1 = e2
    | _, _ => False := by
  induction inVars generalizing curEnv1 curEnv2 argIdx with
  | nil => exact hcur
  | cons iv rest ih =>
    simp only [bindCustomParInputs,
      readParInput_bind_not_contains env st dst val inputs argIdx elemIdx hnc]
    cases readParInput env st inputs argIdx elemIdx with
    | error _ => rfl
    | ok x =>
      apply ih (curEnv1.bind iv (.u64 x)) (curEnv2.bind iv (.u64 x)) (argIdx + 1)
      intro z hz
      unfold VarEnv.bind
      split
      · rfl
      · exact hcur z hz

theorem evalScalarExpr_congr_used (env1 env2 : VarEnv) (e : ScalarExpr)
    (h : ∀ z, scalarExprUsesVar z e = true → env1 z = env2 z) :
    evalScalarExpr env1 e = evalScalarExpr env2 e := by
  induction e with
  | constU64 _ | constBool _ => rfl
  | var id =>
    have hid : scalarExprUsesVar id (.var id) = true := by simp [scalarExprUsesVar]
    simp only [evalScalarExpr, h id hid]
  | binOp op l r ihl ihr =>
    simp only [evalScalarExpr,
      ihl (fun z hz => h z (by simp [scalarExprUsesVar, hz])),
      ihr (fun z hz => h z (by simp [scalarExprUsesVar, hz]))]
  | unaryOp op a iha =>
    simp only [evalScalarExpr, iha (fun z hz => h z (by simp [scalarExprUsesVar, hz]))]
  | select c t f ihc iht ihf =>
    simp only [evalScalarExpr,
      ihc (fun z hz => h z (by simp [scalarExprUsesVar, hz])),
      iht (fun z hz => h z (by simp [scalarExprUsesVar, hz])),
      ihf (fun z hz => h z (by simp [scalarExprUsesVar, hz]))]
  | fma a b c iha ihb ihc =>
    simp only [evalScalarExpr,
      iha (fun z hz => h z (by simp [scalarExprUsesVar, hz])),
      ihb (fun z hz => h z (by simp [scalarExprUsesVar, hz])),
      ihc (fun z hz => h z (by simp [scalarExprUsesVar, hz]))]

theorem evalParKernelElem_bind_not_uses (env : VarEnv) (st : HeapState) (dst : VarId) (val : Val)
    (inputs : List VarId) (len : Nat) (kern : ParallelKernelKind) (i : Nat)
    (hnc : inputs.contains dst = false) (hku : kernelUsesVar dst kern = false) :
    evalParKernelElem (env.bind dst val) st inputs len kern i =
    evalParKernelElem env st inputs len kern i := by
  cases kern with
  | mapScaleAdd s b =>
    simp only [evalParKernelElem, readParInput_bind_not_contains env st dst val inputs 0 i hnc]
  | zipAdd | zipMul | dotProduct | saxpy _ =>
    simp only [evalParKernelElem,
      readParInput_bind_not_contains env st dst val inputs 0 i hnc,
      readParInput_bind_not_contains env st dst val inputs 1 i hnc]
  | stencil1D3Pt wL wC wR =>
    simp only [evalParKernelElem,
      readParInput_bind_not_contains env st dst val inputs 0 i hnc,
      readParInput_bind_not_contains env st dst val inputs 0 (i - 1) hnc,
      readParInput_bind_not_contains env st dst val inputs 0 (i + 1) hnc]
  | customScalar idxVar inVars body =>
    simp only [kernelUsesVar, Bool.or_eq_false_iff] at hku
    rcases hku with ⟨_, hbodyOrIdx⟩
    unfold evalParKernelElem
    have hcur : ∀ z, scalarExprUsesVar z body = true →
        ((env.bind dst val).bind idxVar (.u64 i.toUInt64)) z =
        (env.bind idxVar (.u64 i.toUInt64)) z := by
      intro z hz
      unfold VarEnv.bind
      by_cases hzi : (z == idxVar) = true
      · simp [hzi]
      · simp only [hzi, Bool.false_eq_true, ↓reduceIte]
        have hzd : (z == dst) = false := by
          cases h : (z == dst)
          · rfl
          · rw [beq_iff_eq] at h; subst h
            have hidxNe : (idxVar != z) = true := by
              cases hiz : (idxVar == z)
              · simp [bne, hiz]
              · rw [beq_iff_eq] at hiz; subst hiz; simp at hzi
            simp [hidxNe, hz] at hbodyOrIdx
        simp [hzd]
    have hbind := bindCustomParInputs_bind_dead env st dst val inputs i
      ((env.bind dst val).bind idxVar (.u64 i.toUInt64))
      (env.bind idxVar (.u64 i.toUInt64)) 0 inVars body hnc hcur
    dsimp only
    cases hb1 : bindCustomParInputs (env.bind dst val) st inputs i
        ((env.bind dst val).bind idxVar (.u64 i.toUInt64)) 0 inVars <;>
      cases hb2 : bindCustomParInputs env st inputs i
        (env.bind idxVar (.u64 i.toUInt64)) 0 inVars
    · rw [hb1, hb2] at hbind; dsimp only at hbind ⊢; rw [hbind]
    · rw [hb1, hb2] at hbind; exact False.elim hbind
    · rw [hb1, hb2] at hbind; exact False.elim hbind
    · rw [hb1, hb2] at hbind; dsimp only at hbind ⊢
      rw [evalScalarExpr_congr_used _ _ body hbind]

theorem evalParKernelLoop_bind_not_uses (env : VarEnv) (st : HeapState) (dst : VarId) (val : Val)
    (inputs : List VarId) (len : Nat) (kern : ParallelKernelKind) (is : List Nat)
    (hnc : inputs.contains dst = false) (hku : kernelUsesVar dst kern = false) :
    evalParKernelLoop (env.bind dst val) st inputs len kern is =
    evalParKernelLoop env st inputs len kern is := by
  induction is with
  | nil => rfl
  | cons i rest ih =>
    simp only [evalParKernelLoop,
      evalParKernelElem_bind_not_uses env st dst val inputs len kern i hnc hku, ih]

theorem evalParFor_bind_not_uses (fuel : Nat) (env : VarEnv) (st : HeapState)
    (dst : VarId) (val : Val) (lenVar : VarId) (inputs : List VarId) (kern : ParallelKernelKind)
    (hlen : (lenVar == dst) = false)
    (hnc : inputs.contains dst = false) (hku : kernelUsesVar dst kern = false) :
    evalParFor fuel (env.bind dst val) st lenVar inputs kern =
    evalParFor fuel env st lenVar inputs kern := by
  unfold evalParFor
  rw [VarEnv.bind_ne env dst lenVar val hlen]
  cases env lenVar with
  | none => rfl
  | some v =>
    cases v with
    | u64 n =>
      dsimp only
      split
      · rfl
      · rw [evalVarList_bind_not_contains env dst val inputs hnc,
            evalParKernelLoop_bind_not_uses env st dst val inputs n.toNat kern (List.range n.toNat) hnc hku]
    | _ => rfl

theorem evalSeqLoop_congr_step (count curIdx : Nat) (idxVar accVar : VarId)
    (accVal : Val) (env1 env2 : VarEnv) (st : HeapState)
    (step1 step2 : VarEnv → HeapState → Except UBError (Val × HeapState))
    (hstep : ∀ i av sSt,
      step1 ((env1.bind idxVar (.u64 i)).bind accVar av) sSt =
      step2 ((env2.bind idxVar (.u64 i)).bind accVar av) sSt) :
    evalSeqLoop count curIdx idxVar accVar accVal env1 st step1 =
    evalSeqLoop count curIdx idxVar accVar accVal env2 st step2 := by
  induction count generalizing curIdx accVal st with
  | zero => rfl
  | succ c ih =>
    simp only [evalSeqLoop, hstep curIdx.toUInt64 accVal st]
    cases step2 ((env2.bind idxVar (.u64 curIdx.toUInt64)).bind accVar accVal) st with
    | error _ => rfl
    | ok pair => exact ih (curIdx + 1) pair.1 pair.2

theorem evalCode_bind_not_uses (fuel : Nat) (code : LNIRCode) (env : VarEnv) (st : HeapState)
    (dst : VarId) (val : Val) (hnu : codeUsesVar dst code = false) :
    evalCode fuel (env.bind dst val) st code = evalCode fuel env st code := by
  induction code generalizing env st with
  | letBind d ty e k ih =>
    simp only [codeUsesVar, Bool.or_eq_false_iff] at hnu
    simp only [evalCode, evalExpr_bind_not_uses env st dst val e hnu.1]
    cases evalExpr env st e with
    | error _ => rfl
    | ok pair =>
      rcases pair with ⟨v, st'⟩
      dsimp only
      by_cases hdd : d = dst
      · subst hdd
        rw [VarEnv.bind_overwrite]
      · have hne : (d != dst) = true := bne_iff_ne.mpr hdd
        simp only [hne, Bool.true_and] at hnu
        rw [VarEnv.bind_comm env dst d val v (Ne.symm hdd)]
        exact ih (env.bind d v) st' hnu.2
  | rawStore pv iv vv ety k ih =>
    simp only [codeUsesVar, Bool.or_eq_false_iff] at hnu
    simp only [evalCode, VarEnv.bind_ne env dst pv val hnu.1.1.1,
      VarEnv.bind_ne env dst iv val hnu.1.1.2, VarEnv.bind_ne env dst vv val hnu.1.2]
    cases env pv with
    | none => rfl
    | some vp =>
      cases env iv with
      | none => cases vp <;> rfl
      | some vi =>
        cases env vv with
        | none => cases vp <;> cases vi <;> rfl
        | some vval =>
          cases vp <;> cases vi
          all_goals
            cases vval <;> try rfl
          all_goals
            dsimp only
            cases st.writeElemExclusive _ _ _ with
            | error _ => rfl
            | ok st' => exact ih env st' hnu.2
  | incRef ov c k ih =>
    simp only [codeUsesVar, Bool.or_eq_false_iff] at hnu
    simp only [evalCode, HeapState.evalIncRef, VarEnv.bind_ne env dst ov val hnu.1]
    cases env ov with
    | none => rfl
    | some vo =>
      cases vo <;> dsimp only
      case sarrayId bid =>
        cases st.incRefBuf bid c with
        | error _ => rfl
        | ok st' => exact ih env st' hnu.2
      case objPtr oid =>
        cases st.incRefObj oid c with
        | error _ => rfl
        | ok st' => exact ih env st' hnu.2
      all_goals exact ih env st hnu.2
  | decRef ov c k ih =>
    simp only [codeUsesVar, Bool.or_eq_false_iff] at hnu
    simp only [evalCode, HeapState.evalDecRef, VarEnv.bind_ne env dst ov val hnu.1]
    cases env ov with
    | none => rfl
    | some vo =>
      cases vo <;> dsimp only
      case sarrayId bid =>
        cases st.decRefBuf bid c with
        | error _ => rfl
        | ok st' => exact ih env st' hnu.2
      case objPtr oid =>
        cases st.decRefObj oid c with
        | error _ => rfl
        | ok st' => exact ih env st' hnu.2
      all_goals exact ih env st hnu.2
  | ite cv t e iht ihe =>
    simp only [codeUsesVar, Bool.or_eq_false_iff] at hnu
    simp only [evalCode, VarEnv.bind_ne env dst cv val hnu.1.1]
    cases env cv with
    | none => rfl
    | some vc =>
      cases vc with
      | bool b =>
        cases b
        · exact ihe env st hnu.2
        · exact iht env st hnu.1.2
      | u64 n =>
        dsimp only
        split
        · exact iht env st hnu.1.2
        · exact ihe env st hnu.2
      | u256 w =>
        dsimp only
        split
        · exact iht env st hnu.1.2
        · exact ihe env st hnu.2
      | _ => rfl
  | seqFor iv lv hv av ai aty step k ihs ihk =>
    simp only [codeUsesVar, Bool.or_eq_false_iff] at hnu
    rcases hnu with ⟨⟨⟨⟨hlv, hhv⟩, hai⟩, hstepUse⟩, hkUse⟩
    simp only [evalCode, VarEnv.bind_ne env dst lv val hlv,
      VarEnv.bind_ne env dst hv val hhv, VarEnv.bind_ne env dst ai val hai]
    cases env lv with
    | none => rfl
    | some vlo =>
      cases env hv with
      | none => cases vlo <;> rfl
      | some vhi =>
        cases env ai with
        | none => cases vlo <;> cases vhi <;> rfl
        | some vinit =>
          cases vlo <;> cases vhi <;> try rfl
          rename_i lo hi
          dsimp only
          have hloopEq :
              evalSeqLoop (hi.toNat - lo.toNat) lo.toNat iv av vinit (env.bind dst val) st
                (fun sEnv sSt => evalCode fuel sEnv sSt step) =
              evalSeqLoop (hi.toNat - lo.toNat) lo.toNat iv av vinit env st
                (fun sEnv sSt => evalCode fuel sEnv sSt step) := by
            apply evalSeqLoop_congr_step
            intro i accV sSt
            by_cases hid : iv = dst
            · subst hid; rw [VarEnv.bind_overwrite]
            · by_cases had : av = dst
              · rw [← had, VarEnv.bind_comm env av iv val (.u64 i) (had ▸ Ne.symm hid),
                    VarEnv.bind_overwrite]
              · have hivNe : (iv != dst) = true := bne_iff_ne.mpr hid
                have havNe : (av != dst) = true := bne_iff_ne.mpr had
                simp only [hivNe, havNe, Bool.true_and] at hstepUse
                rw [VarEnv.bind_comm env dst iv val (.u64 i) (Ne.symm hid),
                    VarEnv.bind_comm (env.bind iv (.u64 i)) dst av val accV (Ne.symm had)]
                exact ihs _ sSt hstepUse
          rw [hloopEq]
          cases evalSeqLoop (hi.toNat - lo.toNat) lo.toNat iv av vinit env st
              (fun sEnv sSt => evalCode fuel sEnv sSt step) with
          | error _ => rfl
          | ok pair =>
            rcases pair with ⟨finalAcc, st'⟩
            dsimp only
            by_cases had : av = dst
            · subst had; rw [VarEnv.bind_overwrite]
            · have havNe : (av != dst) = true := bne_iff_ne.mpr had
              simp only [havNe, Bool.true_and] at hkUse
              rw [VarEnv.bind_comm env dst av val finalAcc (Ne.symm had)]
              exact ihk (env.bind av finalAcc) st' hkUse
  | parFor ov lv ins ety kern k ihk =>
    simp only [codeUsesVar, Bool.or_eq_false_iff] at hnu
    rcases hnu with ⟨⟨⟨hlv, hins⟩, hkern⟩, hkUse⟩
    simp only [evalCode, evalParFor_bind_not_uses fuel env st dst val lv ins kern hlv hins hkern]
    cases evalParFor fuel env st lv ins kern with
    | error _ => rfl
    | ok pair =>
      rcases pair with ⟨outVal, st'⟩
      dsimp only
      by_cases hod : ov = dst
      · subst hod; rw [VarEnv.bind_overwrite]
      · have hovNe : (ov != dst) = true := bne_iff_ne.mpr hod
        simp only [hovNe, Bool.true_and] at hkUse
        rw [VarEnv.bind_comm env dst ov val outVal (Ne.symm hod)]
        exact ihk (env.bind ov outVal) st' hkUse
  | ret v =>
    simp only [codeUsesVar] at hnu
    simp only [evalCode, VarEnv.bind_ne env dst v val hnu]
  | unreachable => rfl

end LeanNative.Proofs
