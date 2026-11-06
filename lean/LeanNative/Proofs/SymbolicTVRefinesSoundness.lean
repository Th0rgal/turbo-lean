import LeanNative.Proofs.SymbolicTVRefinesDeadSoundness

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Transform

theorem bindU64Vars_bindCustomParInputs {ctx : SymRefinesCtx} {env curEnv kEnv : VarEnv}
    (st : HeapState) (inputs : List VarId) (elemIdx argIdx : Nat) (inVars : List VarId)
    (hcur : CtxHolds ctx curEnv)
    (hbind : bindCustomParInputs env st inputs elemIdx curEnv argIdx inVars = .ok kEnv) :
    CtxHolds (ctx.bindU64Vars inVars) kEnv := by
  induction inVars generalizing ctx curEnv argIdx with
  | nil =>
    simp only [bindCustomParInputs] at hbind
    injection hbind with heq; subst heq
    exact hcur
  | cons iv rest ih =>
    simp only [bindCustomParInputs] at hbind
    cases hread : readParInput env st inputs argIdx elemIdx with
    | error _ => rw [hread] at hbind; contradiction
    | ok x =>
      rw [hread] at hbind
      have hnext : CtxHolds ((ctx.killVar iv).addU64 iv) (curEnv.bind iv (.u64 x)) :=
        (hcur.killVar_bind iv (.u64 x)).addU64_of_u64 iv x (VarEnv.bind_self curEnv iv (.u64 x))
      exact ih (argIdx + 1) hnext hbind

theorem symbolicKernelRefines_elem_sound {ctx : SymRefinesCtx} {env : VarEnv}
    (hctx : CtxHolds ctx env) (st : HeapState) (inputs : List VarId) (len : Nat)
    (kSrc kTgt : ParallelKernelKind) (i : Nat) (out : UInt64)
    (href : symbolicKernelRefines ctx kSrc kTgt = true)
    (hsrc : evalParKernelElem env st inputs len kSrc i = .ok out) :
    evalParKernelElem env st inputs len kTgt i = .ok out := by
  unfold symbolicKernelRefines at href
  simp only [Bool.or_eq_true] at href
  rcases href with (h1 | h2) | h3
  · rw [← parallelKernelEq_sound kSrc kTgt h1]; exact hsrc
  · rw [← parallelKernelEq_sound (specializeKernel kSrc) kTgt h2,
        ← specializeKernel_elem_sound env st inputs len kSrc i]
    exact hsrc
  · cases kSrc <;> cases kTgt <;> simp only at h3
    all_goals try contradiction
    rename_i idx1 ins1 body1 idx2 ins2 body2
    simp only [Bool.and_eq_true, beq_iff_eq] at h3
    rcases h3 with ⟨⟨rfl, hins⟩, hbody⟩
    have hinsEq := varIdListEq_sound ins1 ins2 hins
    subst hinsEq
    simp only [evalParKernelElem] at hsrc ⊢
    cases hbind : bindCustomParInputs env st inputs i (env.bind idx1 (.u64 i.toUInt64)) 0 ins1 with
    | error _ => rw [hbind] at hsrc; contradiction
    | ok kEnv =>
      rw [hbind] at hsrc
      dsimp only at hsrc ⊢
      cases hb1 : evalScalarExpr kEnv body1 with
      | error _ => rw [hb1] at hsrc; contradiction
      | ok v =>
        rw [hb1] at hsrc
        have hk0 : CtxHolds ((ctx.killVar idx1).addU64 idx1) (env.bind idx1 (.u64 i.toUInt64)) :=
          (hctx.killVar_bind idx1 (.u64 i.toUInt64)).addU64_of_u64 idx1 i.toUInt64
            (VarEnv.bind_self env idx1 (.u64 i.toUInt64))
        have hkCtx := bindU64Vars_bindCustomParInputs st inputs i 0 ins1 hk0 hbind
        have hb2 := symbolicScalarRefines_sound hkCtx body1 body2 v hbody hb1
        rw [hb2]
        exact hsrc

theorem symbolicKernelRefines_loop_sound {ctx : SymRefinesCtx} {env : VarEnv}
    (hctx : CtxHolds ctx env) (st : HeapState) (inputs : List VarId) (len : Nat)
    (kSrc kTgt : ParallelKernelKind) (is : List Nat) (elems : List UInt64)
    (href : symbolicKernelRefines ctx kSrc kTgt = true)
    (hsrc : evalParKernelLoop env st inputs len kSrc is = .ok elems) :
    evalParKernelLoop env st inputs len kTgt is = .ok elems := by
  induction is generalizing elems with
  | nil => exact hsrc
  | cons i rest ih =>
    simp only [evalParKernelLoop] at hsrc ⊢
    cases he1 : evalParKernelElem env st inputs len kSrc i with
    | error _ => rw [he1] at hsrc; contradiction
    | ok x =>
      cases hr1 : evalParKernelLoop env st inputs len kSrc rest with
      | error _ => rw [he1, hr1] at hsrc; contradiction
      | ok xs =>
        rw [he1, hr1] at hsrc
        rw [symbolicKernelRefines_elem_sound hctx st inputs len kSrc kTgt i x href he1,
            ih xs hr1]
        exact hsrc

theorem symbolicKernelRefines_not_dotProduct_iff {ctx : SymRefinesCtx}
    (kSrc kTgt : ParallelKernelKind) (href : symbolicKernelRefines ctx kSrc kTgt = true) :
    (kSrc = .dotProduct ↔ kTgt = .dotProduct) := by
  unfold symbolicKernelRefines at href
  simp only [Bool.or_eq_true] at href
  rcases href with (h1 | h2) | h3
  · rw [parallelKernelEq_sound kSrc kTgt h1]
  · rw [← parallelKernelEq_sound (specializeKernel kSrc) kTgt h2]
    cases kSrc with
    | dotProduct => simp [specializeKernel]
    | mapScaleAdd _ _ | zipAdd | zipMul | saxpy _ | stencil1D3Pt _ _ _ => simp [specializeKernel]
    | customScalar idxVar inVars body =>
      simp only [specializeKernel]
      constructor
      · intro h; nomatch h
      · intro h
        cases hm : matchBuiltinKernel idxVar inVars (contractKernelScalar body) with
        | none => rw [hm] at h; nomatch h
        | some k =>
          rw [hm] at h; subst h
          exact False.elim ((matchBuiltinKernel_elem_sound VarEnv.empty HeapState.empty [] 0
            idxVar inVars (contractKernelScalar body) .dotProduct 0 hm).2 rfl)
  · cases kSrc <;> cases kTgt
    all_goals
      simp only at h3
      try contradiction
    constructor <;> (intro h; nomatch h)

theorem symbolicKernelRefines_parFor_sound {ctx : SymRefinesCtx} {env : VarEnv}
    (hctx : CtxHolds ctx env) (fuel : Nat) (st : HeapState)
    (lenVar : VarId) (inputs : List VarId) (kSrc kTgt : ParallelKernelKind) (elemTy : LNIRType)
    (pair : Val × HeapState)
    (href : symbolicKernelRefines ((ctx.addU64 lenVar).addBoundVars inputs) kSrc kTgt = true)
    (hsrc : evalParFor fuel env st lenVar inputs kSrc elemTy = .ok pair) :
    evalParFor fuel env st lenVar inputs kTgt elemTy = .ok pair ∧
    CtxHolds ((ctx.addU64 lenVar).addBoundVars inputs) env := by
  unfold evalParFor at hsrc ⊢
  cases hlen : env lenVar with
  | none => rw [hlen] at hsrc; contradiction
  | some lv =>
    rw [hlen] at hsrc
    cases lv with
    | u64 n =>
      dsimp only at hsrc ⊢
      by_cases hgt : n.toNat > fuel
      · simp only [hgt, ↓reduceIte] at hsrc; contradiction
      · simp only [hgt, ↓reduceIte] at hsrc ⊢
        cases hvars : evalVarList env inputs with
        | error _ => rw [hvars] at hsrc; contradiction
        | ok vs =>
          rw [hvars] at hsrc
          have hctxLen : CtxHolds ((ctx.addU64 lenVar).addBoundVars inputs) env :=
            (hctx.addU64_of_u64 lenVar n hlen).addBoundVars_of_evalVarList inputs vs hvars
          let stIn : HeapState :=
            if maskElemVal elemTy 0xFFFFFFFFFFFFFFFF == 0xFFFFFFFFFFFFFFFF then st
            else { st with buffers := st.buffers.map (fun b => { b with data := b.data.map (maskElemVal elemTy) }) }
          cases hloop : evalParKernelLoop env stIn inputs n.toNat kSrc (List.range n.toNat) with
          | error _ => rw [hloop] at hsrc; contradiction
          | ok elems =>
            rw [hloop] at hsrc
            rw [symbolicKernelRefines_loop_sound hctxLen stIn inputs n.toNat kSrc kTgt
                  (List.range n.toNat) elems href hloop]
            have hdot := symbolicKernelRefines_not_dotProduct_iff kSrc kTgt href
            refine ⟨?_, hctxLen⟩
            cases kSrc <;> cases kTgt <;> try exact hsrc
            all_goals
              exfalso
              try exact (hdot.mp rfl |> fun h => nomatch h)
              try exact (hdot.mpr rfl |> fun h => nomatch h)
    | _ => contradiction

theorem symbolicCodeRefinesAux_sound (ctx : SymRefinesCtx) (src tgt : LNIRCode)
    (href : symbolicCodeRefinesAux ctx src tgt = true)
    (fuel : Nat) (env : VarEnv) (st : HeapState) (v : Val) (st' : HeapState)
    (hctx : CtxHolds ctx env)
    (hsrc : evalCode fuel env st src = .ok (v, st')) :
    evalCode fuel env st tgt = .ok (v, st') := by
  induction src generalizing ctx tgt env st v st' with
  | ret v1 =>
    cases tgt with
    | ret v2 =>
      simp only [symbolicCodeRefinesAux, beq_iff_eq] at href
      subst href; exact hsrc
    | _ => simp [symbolicCodeRefinesAux] at href
  | unreachable =>
    simp [evalCode] at hsrc
  | letBind dst1 ty1 val1 k1 ih =>
    have hgeneric :
        ∀ {dst2 : VarId} {ty2 : LNIRType} {val2 : LNIRExpr} {k2 : LNIRCode},
          (dst1 == dst2 && lnirExprEvalEq val1 val2 &&
            symbolicCodeRefinesAux ((ctx.killVar dst1).addBound dst1) k1 k2) = true →
          evalCode fuel env st (.letBind dst2 ty2 val2 k2) = .ok (v, st') := by
      intro dst2 ty2 val2 k2 href'
      simp only [Bool.and_eq_true, beq_iff_eq] at href'
      rcases href' with ⟨⟨rfl, heq⟩, hk⟩
      simp only [evalCode] at hsrc ⊢
      rw [← lnirExprEvalEq_sound env st val1 val2 heq]
      cases hex : evalExpr env st val1 with
      | error _ => rw [hex] at hsrc; contradiction
      | ok pair =>
        rw [hex] at hsrc
        exact ih ((ctx.killVar dst1).addBound dst1) k2 hk (env.bind dst1 pair.1) pair.2 v st'
          ((hctx.killVar_bind dst1 pair.1).addBound_of_some dst1 pair.1
            (VarEnv.bind_self env dst1 pair.1)) hsrc
    cases val1 with
    | mkTuple fs1 =>
      simp only [symbolicCodeRefinesAux] at href
      have hditch :
          ((fs1.all fun f => ctx.boundVars.contains f) &&
            varDeadInCode dst1 tgt &&
            symbolicCodeRefinesAux (ctx.afterMkTupleLet dst1 fs1) k1 tgt) = true →
          evalCode fuel env st tgt = .ok (v, st') := by
        intro h
        simp only [Bool.and_eq_true, varDeadInCode, Bool.not_eq_true'] at h
        rcases h with ⟨⟨_, hdead⟩, hk⟩
        simp only [evalCode, evalExpr] at hsrc
        cases hevl : evalVarList env fs1 with
        | error _ => rw [hevl] at hsrc; contradiction
        | ok vals =>
          rw [hevl] at hsrc
          have htgt := ih (ctx.afterMkTupleLet dst1 fs1) tgt hk (env.bind dst1 (.tuple vals)) st v st'
            (hctx.afterMkTupleLet_sound dst1 fs1 vals hevl) hsrc
          rw [evalCode_bind_not_uses fuel tgt env st dst1 (.tuple vals) hdead] at htgt
          exact htgt
      cases tgt with
      | letBind dst2 ty2 val2 k2 =>
        cases val2 with
        | mkTuple fs2 =>
          dsimp only at href
          cases hkeep : (dst1 == dst2 && varIdListEq fs1 fs2 &&
              symbolicCodeRefinesAux (ctx.afterMkTupleLet dst1 fs1) k1 k2)
          · simp only [hkeep, Bool.false_eq_true, ↓reduceIte] at href
            exact hditch href
          · simp only [Bool.and_eq_true, beq_iff_eq] at hkeep
            rcases hkeep with ⟨⟨rfl, hfs⟩, hk⟩
            rw [← varIdListEq_sound fs1 fs2 hfs]
            simp only [evalCode, evalExpr] at hsrc ⊢
            cases hevl : evalVarList env fs1 with
            | error _ => rw [hevl] at hsrc; contradiction
            | ok vals =>
              rw [hevl] at hsrc
              exact ih (ctx.afterMkTupleLet dst1 fs1) k2 hk (env.bind dst1 (.tuple vals)) st v st'
                (hctx.afterMkTupleLet_sound dst1 fs1 vals hevl) hsrc
        | _ =>
          dsimp only at href
          simp only [Bool.false_eq_true, ↓reduceIte] at href
          exact hditch href
      | _ =>
        dsimp only at href
        simp only [Bool.false_eq_true, ↓reduceIte] at href
        exact hditch href
    | scalar e1 =>
      cases tgt with
      | letBind dst2 ty2 val2 k2 =>
        cases val2 with
        | scalar e2 =>
          simp only [symbolicCodeRefinesAux, Bool.and_eq_true, beq_iff_eq] at href
          rcases href with ⟨⟨rfl, he⟩, hk⟩
          simp only [evalCode, evalExpr] at hsrc ⊢
          cases hs1 : evalScalarExpr env e1 with
          | error _ => rw [hs1] at hsrc; contradiction
          | ok val =>
            rw [hs1] at hsrc
            rw [symbolicScalarRefines_sound hctx e1 e2 val he hs1]
            exact ih (ctx.afterScalarLet dst1 e1) k2 hk (env.bind dst1 val) st v st'
              (hctx.afterScalarLet_sound dst1 e1 val hs1) hsrc
        | _ => simp [symbolicCodeRefinesAux] at href
      | _ => simp [symbolicCodeRefinesAux] at href
    | projTuple tVar idx =>
      cases tgt with
      | letBind dst2 ty2 val2 k2 =>
        cases val2 with
        | scalar e2 =>
          simp only [symbolicCodeRefinesAux, Bool.and_eq_true, beq_iff_eq] at href
          rcases href with ⟨rfl, hfind⟩
          cases hft : findTupleField tVar idx ctx.tuples with
          | none => rw [hft] at hfind; contradiction
          | some fVar =>
            rw [hft] at hfind
            simp only [Bool.and_eq_true] at hfind
            rcases hfind with ⟨he2, hk⟩
            obtain ⟨fs, htmem, hfidx⟩ := findTupleField_mem tVar idx fVar ctx.tuples hft
            obtain ⟨vals, htv, hevl⟩ := hctx.2.2.2.2 (tVar, fs) htmem
            obtain ⟨fVal, hvidx, hfenv⟩ := evalVarList_index_eq env fs vals idx fVar hevl hfidx
            simp only [evalCode, evalExpr, htv, hvidx] at hsrc
            simp only [evalCode, evalExpr]
            have hfEval : evalScalarExpr env (.var fVar) = .ok fVal := by
              simp [evalScalarExpr, hfenv]
            rw [symbolicScalarRefines_sound hctx (.var fVar) e2 fVal he2 hfEval]
            exact ih (ctx.afterScalarLet dst1 (.var fVar)) k2 hk (env.bind dst1 fVal) st v st'
              (hctx.afterScalarLet_sound dst1 (.var fVar) fVal hfEval) hsrc
        | _ => exact hgeneric href
      | _ => simp [symbolicCodeRefinesAux] at href
    | _ =>
      cases tgt with
      | letBind dst2 ty2 val2 k2 => exact hgeneric href
      | _ => simp [symbolicCodeRefinesAux] at href
  | rawStore p1 i1 v1 ty1 k1 ih =>
    cases tgt with
    | rawStore p2 i2 v2 ty2 k2 =>
      simp only [symbolicCodeRefinesAux, Bool.and_eq_true, beq_iff_eq] at href
      rcases href with ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hmask⟩, hk⟩
      have hm : ∀ w, maskElemVal ty1 w = maskElemVal ty2 w := maskElemVal_eq_of_allOnes_eq ty1 ty2 hmask
      simp only [evalCode] at hsrc ⊢
      cases hp : env p1 with
      | none => rw [hp] at hsrc; contradiction
      | some vp =>
        cases hi : env i1 with
        | none => rw [hp, hi] at hsrc; cases vp <;> contradiction
        | some vi =>
          cases hv : env v1 with
          | none =>
            rw [hp, hi, hv] at hsrc
            cases vp <;> cases vi <;> contradiction
          | some vv =>
            rw [hp, hi, hv] at hsrc
            cases vp <;> cases vi
            all_goals
              cases vv <;> try contradiction
            all_goals
              rename_i bid idx nval
              dsimp only at hsrc ⊢
              rw [← hm nval]
              cases hw : st.writeElemExclusive bid idx.toNat (maskElemVal ty1 nval) with
              | error _ => rw [hw] at hsrc; contradiction
              | ok st1 =>
                rw [hw] at hsrc
                have hctx' := ((hctx.addBound_of_some p1 _ hp).addU64_of_u64 i1 idx hi).addU64_of_u64 v1 nval hv
                exact ih _ k2 hk env st1 v st' hctx' hsrc
    | _ => simp [symbolicCodeRefinesAux] at href
  | incRef o1 c1 k1 ih =>
    cases tgt with
    | incRef o2 c2 k2 =>
      simp only [symbolicCodeRefinesAux, Bool.and_eq_true, beq_iff_eq] at href
      rcases href with ⟨⟨rfl, rfl⟩, hk⟩
      simp only [evalCode] at hsrc ⊢
      cases hinc : st.evalIncRef env o1 c1 with
      | error _ => rw [hinc] at hsrc; contradiction
      | ok st1 =>
        rw [hinc] at hsrc
        exact ih ctx k2 hk env st1 v st' hctx hsrc
    | _ => simp [symbolicCodeRefinesAux] at href
  | decRef o1 c1 k1 ih =>
    cases tgt with
    | decRef o2 c2 k2 =>
      simp only [symbolicCodeRefinesAux, Bool.and_eq_true, beq_iff_eq] at href
      rcases href with ⟨⟨rfl, rfl⟩, hk⟩
      simp only [evalCode] at hsrc ⊢
      cases hdec : st.evalDecRef env o1 c1 with
      | error _ => rw [hdec] at hsrc; contradiction
      | ok st1 =>
        rw [hdec] at hsrc
        exact ih ctx k2 hk env st1 v st' hctx hsrc
    | _ => simp [symbolicCodeRefinesAux] at href
  | ite condVar t1 e1 iht ihe =>
    simp only [symbolicCodeRefinesAux] at href
    have hconst :
        ∀ {tgt' : LNIRCode},
          (match findConstBool condVar ctx.constBool with
           | some true => symbolicCodeRefinesAux ctx t1 tgt'
           | some false => symbolicCodeRefinesAux ctx e1 tgt'
           | none =>
             match findConstU64 condVar ctx.constU64 with
             | some n =>
               if n != 0 then symbolicCodeRefinesAux ctx t1 tgt'
               else symbolicCodeRefinesAux ctx e1 tgt'
             | none => false) = true →
          evalCode fuel env st tgt' = .ok (v, st') := by
      intro tgt' hf
      cases hcb : findConstBool condVar ctx.constBool with
      | some b =>
        rw [hcb] at hf
        have hcv := hctx.2.2.2.1 (condVar, b) (findConstBool_mem condVar b ctx.constBool hcb)
        cases b
        · simp only [evalCode, hcv] at hsrc
          exact ihe ctx tgt' hf env st v st' hctx hsrc
        · simp only [evalCode, hcv] at hsrc
          exact iht ctx tgt' hf env st v st' hctx hsrc
      | none =>
        rw [hcb] at hf
        cases hcu : findConstU64 condVar ctx.constU64 with
        | none => rw [hcu] at hf; contradiction
        | some n =>
          rw [hcu] at hf
          have hcv := hctx.2.2.1 (condVar, n) (findConstU64_mem condVar n ctx.constU64 hcu)
          simp only [evalCode, hcv] at hsrc
          dsimp only at hf hsrc
          cases hnz : (n != 0)
          · simp only [hnz, Bool.false_eq_true, ↓reduceIte] at hf hsrc
            exact ihe ctx tgt' hf env st v st' hctx hsrc
          · simp only [hnz, ↓reduceIte] at hf hsrc
            exact iht ctx tgt' hf env st v st' hctx hsrc
    cases tgt with
    | ite c2 t2 e2 =>
      dsimp only at href
      cases hsame : (condVar == c2 &&
          symbolicCodeRefinesAux (ctx.addBound condVar) t1 t2 &&
          symbolicCodeRefinesAux (ctx.addBound condVar) e1 e2)
      · simp only [hsame, Bool.false_eq_true, ↓reduceIte] at href
        exact hconst href
      · simp only [Bool.and_eq_true, beq_iff_eq] at hsame
        rcases hsame with ⟨⟨rfl, ht⟩, he⟩
        simp only [evalCode] at hsrc ⊢
        cases hc : env condVar with
        | none => rw [hc] at hsrc; contradiction
        | some vc =>
          rw [hc] at hsrc
          have hctx' := hctx.addBound_of_some condVar vc hc
          cases vc with
          | bool b =>
            cases b
            · exact ihe _ e2 he env st v st' hctx' hsrc
            · exact iht _ t2 ht env st v st' hctx' hsrc
          | u64 n =>
            dsimp only at hsrc ⊢
            cases hn : (n != 0)
            · simp only [hn, Bool.false_eq_true, ↓reduceIte] at hsrc ⊢
              exact ihe _ e2 he env st v st' hctx' hsrc
            · simp only [hn, ↓reduceIte] at hsrc ⊢
              exact iht _ t2 ht env st v st' hctx' hsrc
          | u256 w =>
            dsimp only at hsrc ⊢
            cases hw : (w != UInt256.zero)
            · simp only [hw, Bool.false_eq_true, ↓reduceIte] at hsrc ⊢
              exact ihe _ e2 he env st v st' hctx' hsrc
            · simp only [hw, ↓reduceIte] at hsrc ⊢
              exact iht _ t2 ht env st v st' hctx' hsrc
          | _ => contradiction
    | _ =>
      dsimp only at href
      simp only [Bool.false_eq_true, ↓reduceIte] at href
      exact hconst href
  | seqFor idx1 lo1 hi1 acc1 init1 ty1 step1 k1 ihs ihk =>
    cases tgt with
    | seqFor idx2 lo2 hi2 acc2 init2 ty2 step2 k2 =>
      simp only [symbolicCodeRefinesAux, Bool.and_eq_true, beq_iff_eq] at href
      rcases href with ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hstep, hk⟩
      simp only [evalCode] at hsrc ⊢
      cases hlo : env lo1 with
      | none => rw [hlo] at hsrc; contradiction
      | some vlo =>
        cases hhi : env hi1 with
        | none => rw [hlo, hhi] at hsrc; cases vlo <;> contradiction
        | some vhi =>
          cases hinit : env init1 with
          | none =>
            rw [hlo, hhi, hinit] at hsrc
            cases vlo <;> cases vhi <;> contradiction
          | some vinit =>
            rw [hlo, hhi, hinit] at hsrc
            cases vlo <;> cases vhi <;> try contradiction
            rename_i lo hi
            dsimp only at hsrc ⊢
            have hctxB : CtxHolds (((ctx.addU64 lo1).addU64 hi1).addBound init1) env :=
              ((hctx.addU64_of_u64 lo1 lo hlo).addU64_of_u64 hi1 hi hhi).addBound_of_some init1 vinit hinit
            have hloop_imp : ∀ (cnt cur : Nat) (accVal : Val) (sSt : HeapState) (res : Val × HeapState),
                evalSeqLoop cnt cur idx1 acc1 accVal env sSt
                  (fun sEnv sSt' => evalCode fuel sEnv sSt' step1) = .ok res →
                evalSeqLoop cnt cur idx1 acc1 accVal env sSt
                  (fun sEnv sSt' => evalCode fuel sEnv sSt' step2) = .ok res := by
              intro cnt
              induction cnt with
              | zero => intro _ _ _ _ h; exact h
              | succ c ihc =>
                intro cur accVal sSt res h
                simp only [evalSeqLoop] at h ⊢
                let stepEnv := (env.bind idx1 (.u64 cur.toUInt64)).bind acc1 accVal
                have hStepCtx : CtxHolds
                    ((((((ctx.addU64 lo1).addU64 hi1).addBound init1).killVar idx1).addU64 idx1).killVar acc1 |>.addBound acc1)
                    stepEnv :=
                  ((((hctxB.killVar_bind idx1 (.u64 cur.toUInt64)).addU64_of_u64 idx1 cur.toUInt64
                    (VarEnv.bind_self env idx1 (.u64 cur.toUInt64))).killVar_bind acc1 accVal).addBound_of_some
                    acc1 accVal (VarEnv.bind_self _ acc1 accVal))
                cases hs1 : evalCode fuel stepEnv sSt step1 with
                | error _ => rw [hs1] at h; contradiction
                | ok pair =>
                  rw [hs1] at h
                  rcases pair with ⟨nextAcc, stMid⟩
                  rw [ihs _ step2 hstep stepEnv sSt nextAcc stMid hStepCtx hs1]
                  exact ihc (cur + 1) nextAcc stMid res h
            cases hloop : evalSeqLoop (hi.toNat - lo.toNat) lo.toNat idx1 acc1 vinit env st
                (fun sEnv sSt => evalCode fuel sEnv sSt step1) with
            | error _ => rw [hloop] at hsrc; contradiction
            | ok pair =>
              rw [hloop] at hsrc
              rw [hloop_imp _ _ _ _ pair hloop]
              rcases pair with ⟨finalAcc, stLoop⟩
              have hContCtx : CtxHolds
                  ((((ctx.addU64 lo1).addU64 hi1).addBound init1).killVar acc1 |>.addBound acc1)
                  (env.bind acc1 finalAcc) :=
                (hctxB.killVar_bind acc1 finalAcc).addBound_of_some acc1 finalAcc
                  (VarEnv.bind_self env acc1 finalAcc)
              exact ihk _ k2 hk (env.bind acc1 finalAcc) stLoop v st' hContCtx hsrc
    | _ => simp [symbolicCodeRefinesAux] at href
  | parFor out1 len1 ins1 ety1 kern1 k1 ihk =>
    cases tgt with
    | parFor out2 len2 ins2 ety2 kern2 k2 =>
      simp only [symbolicCodeRefinesAux, Bool.and_eq_true, beq_iff_eq] at href
      rcases href with ⟨⟨⟨⟨rfl, rfl⟩, hins⟩, hmask⟩, hkern, hk⟩
      rw [← varIdListEq_sound ins1 ins2 hins]
      have hm : maskElemVal ety1 = maskElemVal ety2 := funext (maskElemVal_eq_of_allOnes_eq ety1 ety2 hmask)
      have hparEq : evalParFor fuel env st len1 ins1 kern2 ety2 = evalParFor fuel env st len1 ins1 kern2 ety1 := by
        unfold evalParFor; rw [hm]
      simp only [evalCode, hparEq] at hsrc ⊢
      cases hp1 : evalParFor fuel env st len1 ins1 kern1 ety1 with
      | error _ => rw [hp1] at hsrc; contradiction
      | ok pair =>
        rw [hp1] at hsrc
        obtain ⟨hp2, hctxLen⟩ := symbolicKernelRefines_parFor_sound hctx fuel st len1 ins1 kern1 kern2 ety1 pair hkern hp1
        rw [hp2]
        rcases pair with ⟨outVal, stPar⟩
        have hContCtx := (hctxLen.killVar_bind out1 outVal).addBound_of_some out1 outVal
          (VarEnv.bind_self env out1 outVal)
        exact ihk _ k2 hk (env.bind out1 outVal) stPar v st' hContCtx hsrc
    | _ => simp [symbolicCodeRefinesAux] at href

/-- Master kernel-checked soundness theorem (`symbolicCodeRefines_sound`) for the total
    symbolic `LNIRCode` translation validator (`symbolicCodeRefines`):
    whenever `symbolicCodeRefines src tgt = true`, `CodeRefines src tgt` holds unconditionally
    over `evalCode` (`0 sorryAx`, `0` external solver trust). -/
theorem symbolicCodeRefines_sound (src tgt : LNIRCode)
    (h : symbolicCodeRefines src tgt = true) :
    CodeRefines src tgt := by
  intro fuel env st v st' hsrc
  exact symbolicCodeRefinesAux_sound {} src tgt h fuel env st v st' (CtxHolds.empty env) hsrc

/-- Machine-checked `VerifiedTVPassContract` soundness theorem (`symbolicValidatedDeclOpt_sound`):
    whenever `runSymbolicValidatedDecl propose d = some d'`, `CodeRefines d.body d'.body` holds
    in the Lean 4 kernel (`0 sorryAx`, `0` external solver TCB). -/
theorem symbolicValidatedDeclOpt_sound (propose : LNIRDecl → LNIRDecl) (d d' : LNIRDecl)
    (h : runSymbolicValidatedDecl propose d = some d') :
    CodeRefines d.body d'.body := by
  unfold runSymbolicValidatedDecl at h
  dsimp only at h
  cases hgate : (d.checkElemTypes.isNone && (propose d).checkElemTypes.isNone && symbolicCodeRefines d.body (propose d).body)
  · rw [hgate] at h; cases h
  · rw [hgate] at h
    simp only [↓reduceIte, Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true] at hgate
    exact symbolicCodeRefines_sound d.body (propose d).body hgate.2

end LeanNative.Proofs
