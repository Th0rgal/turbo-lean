import LeanNative.Proofs.SuperoptHelpersSoundness

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Transform

/-!
# Kernel-Checked Soundness of the Enumerative Superoptimizer (`LeanNative.Proofs.SuperoptSoundness`)

Proves `checkSuperoptScalarVerified_sound` and lifts it through candidate folding, loop bodies,
and `parFor` kernels to `superoptCode_sound`, `superoptDecl_sound`, and `superoptModule_sound`.
-/

/-- Kernel decision procedure soundness: `checkSuperoptScalarVerified e cand = true` implies
    `ExprRefines (.scalar e) (.scalar cand)`. -/
theorem checkSuperoptScalarVerified_sound :
    ∀ (e cand : ScalarExpr),
      checkSuperoptScalarVerified e cand = true →
      ExprRefines (.scalar e) (.scalar cand)
  | e, cand, hcheck => by
    unfold checkSuperoptScalarVerified at hcheck
    by_cases heq : (cand == e) = true
    · have heq' := ScalarExpr_eq_of_beq heq
      subst heq'
      exact ExprRefines.refl _
    · rw [ite_eq_right heq] at hcheck
      by_cases hpeep : (cand == rewriteScalarPeephole e) = true
      · have hpeep' := ScalarExpr_eq_of_beq hpeep
        subst hpeep'
        exact ExprRefines.of_scalar_equiv (rewriteScalarPeephole_sound e)
      · rw [ite_eq_right hpeep] at hcheck
        by_cases hver : (cand == rewriteScalarVerified e) = true
        · have hver' := ScalarExpr_eq_of_beq hver
          subst hver'
          exact ExprRefines.of_scalar_equiv (rewriteScalarVerified_sound e)
        · rw [ite_eq_right hver] at hcheck
          dsimp only [] at hcheck
          by_cases hpure :
              (isPureU64ScalarExpr e &&
               isPureU64ScalarExpr cand &&
               (unionVars (collectScalarVars e) (collectScalarVars cand)).all (fun v => varForcedU64 v e) &&
               (normSymExpr (scalarToSymExpr e) == normSymExpr (scalarToSymExpr cand))) = true
          · simp only [Bool.and_eq_true] at hpure
            rcases hpure with ⟨⟨⟨he, hc⟩, hall⟩, hbeq⟩
            have hnorm := SymExpr_eq_of_beq hbeq
            intro env st v st' heval
            simp only [evalExpr] at heval ⊢
            cases hse : evalScalarExpr env e with
            | error err => simp [hse] at heval
            | ok sv =>
              rw [hse] at heval
              injection heval with hpair
              injection hpair with hv hst
              subst hv; subst hst
              have hvars : ∀ id : VarId,
                  (unionVars (collectScalarVars e) (collectScalarVars cand)).contains id = true →
                  ∃ n : UInt64, env id = some (Val.u64 n) := by
                intro id hid
                rw [List.contains_iff_mem] at hid
                rw [List.all_eq_true] at hall
                exact varForcedU64_sound id e env sv (hall id hid) hse
              have hsc := normSymExpr_pureU64_scalar_refines e cand env sv he hc hvars hnorm hse
              rw [hsc]
          · rw [ite_eq_right hpure] at hcheck
            cases e with
            | constU64 _ | constBool _ | var _ => cases hcheck
            | binOp op l r =>
              cases cand with
              | constU64 _ | constBool _ | var _ | unaryOp _ _ | select _ _ _ =>
                cases op <;> cases l <;> try cases hcheck
                rename_i op1 _ _; cases op1 <;> cases hcheck
              | binOp op' l' r' =>
                simp only [Bool.and_eq_true] at hcheck
                rcases hcheck with ⟨⟨hop, hl⟩, hr⟩
                have hop' := BinOp_eq_of_beq hop
                subst hop'
                have ihl := checkSuperoptScalarVerified_sound l l' hl
                have ihr := checkSuperoptScalarVerified_sound r r' hr
                exact ExprRefines.scalar_binOp_congr ihl ihr
              | fma a' b' c' =>
                cases op with
                | add =>
                  cases l with
                  | binOp op1 l1 r1 =>
                    cases op1 with
                    | mul =>
                      simp only [Bool.and_eq_true] at hcheck
                      rcases hcheck with ⟨⟨hl1, hr1⟩, hr⟩
                      have ihl1 := checkSuperoptScalarVerified_sound l1 a' hl1
                      have ihr1 := checkSuperoptScalarVerified_sound r1 b' hr1
                      have ihr := checkSuperoptScalarVerified_sound r c' hr
                      apply ExprRefines.scalar_of_eval
                      intro env v hv
                      simp only [evalScalarExpr] at hv ⊢
                      split at hv <;> try contradiction
                      next xy z hxy hz =>
                        split at hxy <;> try contradiction
                        next x y hx hy =>
                          simpa only [ExprRefines.scalar_eval ihl1 _ _ hx,
                            ExprRefines.scalar_eval ihr1 _ _ hy, hxy,
                            ExprRefines.scalar_eval ihr _ _ hz] using hv
                    | _ => cases hcheck
                  | _ => cases hcheck
                | _ => cases hcheck
            | unaryOp op a =>
              cases cand with
              | unaryOp op' a' =>
                simp only [Bool.and_eq_true] at hcheck
                rcases hcheck with ⟨hop, ha⟩
                have hop' := UnaryOp_eq_of_beq hop
                subst hop'
                have iha := checkSuperoptScalarVerified_sound a a' ha
                exact ExprRefines.scalar_unaryOp_congr iha
              | _ => cases hcheck
            | select c t f =>
              cases cand with
              | select c' t' f' =>
                simp only [Bool.and_eq_true] at hcheck
                rcases hcheck with ⟨⟨hc, ht⟩, hf⟩
                have ihc := checkSuperoptScalarVerified_sound c c' hc
                have iht := checkSuperoptScalarVerified_sound t t' ht
                have ihf := checkSuperoptScalarVerified_sound f f' hf
                exact ExprRefines.scalar_select_congr ihc iht ihf
              | _ => cases hcheck
            | fma a b c =>
              cases cand with
              | fma a' b' c' =>
                simp only [Bool.and_eq_true] at hcheck
                rcases hcheck with ⟨⟨ha, hb⟩, hc⟩
                have iha := checkSuperoptScalarVerified_sound a a' ha
                have ihb := checkSuperoptScalarVerified_sound b b' hb
                have ihc := checkSuperoptScalarVerified_sound c c' hc
                exact ExprRefines.scalar_fma_congr iha ihb ihc
              | binOp op l r =>
                cases op with
                | add =>
                  cases l with
                  | binOp op1 l1 r1 =>
                    cases op1 with
                    | mul =>
                      simp only [Bool.and_eq_true] at hcheck
                      rcases hcheck with ⟨⟨ha, hb⟩, hc⟩
                      have iha := checkSuperoptScalarVerified_sound a l1 ha
                      have ihb := checkSuperoptScalarVerified_sound b r1 hb
                      have ihc := checkSuperoptScalarVerified_sound c r hc
                      apply ExprRefines.scalar_of_eval
                      intro env v hv
                      simp only [evalScalarExpr] at hv ⊢
                      split at hv <;> try contradiction
                      next x y hx hy =>
                        split at hv <;> try contradiction
                        next xy z hxy hz =>
                          simpa only [ExprRefines.scalar_eval iha _ _ hx,
                            ExprRefines.scalar_eval ihb _ _ hy, hxy,
                            ExprRefines.scalar_eval ihc _ _ hz] using hv
                    | _ => cases hcheck
                  | _ => cases hcheck
                | _ => cases hcheck
              | _ => cases hcheck
termination_by e cand => sizeOf e + sizeOf cand


/-- Fold over synthesized candidates preserves `ExprRefines` relative to root `e0`. -/
theorem foldl_superopt_cands_sound (e0 : ScalarExpr) (p : HardwareCostProfile)
    (cands : List ScalarExpr) (acc : ScalarExpr)
    (hacc : ExprRefines (.scalar e0) (.scalar acc)) :
    ExprRefines (.scalar e0) (.scalar (cands.foldl (fun a cand =>
      let cCost := scalarExprCostWithProfile p cand
      let checksOk :=
        checkSuperoptScalarVerified e0 cand &&
        fastCheckScalarEquiv e0 cand &&
        symCheckScalarEquiv e0 cand
      if checksOk && cCost < scalarExprCostWithProfile p a then cand else a) acc)) := by
  induction cands generalizing acc with
  | nil => exact hacc
  | cons cand rest ih =>
    simp only [List.foldl]
    by_cases hcond :
        ((checkSuperoptScalarVerified e0 cand &&
          fastCheckScalarEquiv e0 cand &&
          symCheckScalarEquiv e0 cand) &&
         decide (scalarExprCostWithProfile p cand < scalarExprCostWithProfile p acc)) = true
    · have hv : checkSuperoptScalarVerified e0 cand = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        exact hcond.1.1.1
      rw [ite_eq_left hcond]
      exact ih cand (checkSuperoptScalarVerified_sound e0 cand hv)
    · rw [ite_eq_right hcond]
      exact ih acc hacc

/-- Core superoptimizer preserves scalar expression semantics. -/
theorem superoptScalarExprCore_sound (p : HardwareCostProfile) (targetLabel declName : String) (e : ScalarExpr) :
    ExprRefines (.scalar e) (.scalar (superoptScalarExprCore p targetLabel declName e).1) := by
  unfold superoptScalarExprCore
  simp only []
  let cands := synthesizeCandidates p.target e
  let bestCand := cands.foldl (fun acc cand =>
      let cCost := scalarExprCostWithProfile p cand
      let checksOk :=
        checkSuperoptScalarVerified e cand &&
        fastCheckScalarEquiv e cand &&
        symCheckScalarEquiv e cand
      if checksOk && cCost < scalarExprCostWithProfile p acc then cand else acc) e
  have hbest := foldl_superopt_cands_sound e p cands e (ExprRefines.refl _)
  change ExprRefines (.scalar e) (.scalar bestCand) at hbest
  split
  · exact hbest
  · exact ExprRefines.refl _

theorem superoptScalarExpr_sound (target : SuperoptTarget) (declName : String) (e : ScalarExpr) :
    ExprRefines (.scalar e) (.scalar (superoptScalarExpr target declName e).1) :=
  superoptScalarExprCore_sound (HardwareCostProfile.forTarget target) target.toString declName e

theorem superoptScalarExprWithProfile_sound (p : HardwareCostProfile) (declName : String) (e : ScalarExpr) :
    ExprRefines (.scalar e) (.scalar (superoptScalarExprWithProfile p declName e).1) :=
  superoptScalarExprCore_sound p s!"{p.target.toString}:{p.profileId}" declName e

/-- Custom scalar `parFor` kernel element forward refinement. -/
theorem evalParKernelElem_customScalar_refines (env : VarEnv) (st : HeapState)
    (inputs : List VarId) (len : Nat) (idxVar : VarId) (inVars : List VarId)
    (body body' : ScalarExpr) (i : Nat) (out : UInt64)
    (href : ExprRefines (.scalar body) (.scalar body'))
    (hsrc : evalParKernelElem env st inputs len (.customScalar idxVar inVars body) i = .ok out) :
    evalParKernelElem env st inputs len (.customScalar idxVar inVars body') i = .ok out := by
  unfold evalParKernelElem at hsrc ⊢
  cases hbind : bindCustomParInputs env st inputs i (env.bind idxVar (.u64 i.toUInt64)) 0 inVars with
  | error err => simp [hbind] at hsrc
  | ok kEnv =>
    simp only [hbind] at hsrc ⊢
    cases hbody : evalScalarExpr kEnv body with
    | error err => simp [hbody] at hsrc
    | ok v =>
      have htgt := href kEnv st v st (by simp [evalExpr, hbody])
      simp only [evalExpr] at htgt
      cases hbody' : evalScalarExpr kEnv body' with
      | error err => simp [hbody'] at htgt
      | ok v' =>
        rw [hbody'] at htgt
        injection htgt with hpair
        injection hpair with hv _
        subst hv
        rw [hbody] at hsrc
        exact hsrc

/-- Custom scalar `parFor` kernel loop forward refinement. -/
theorem evalParKernelLoop_customScalar_refines (env : VarEnv) (st : HeapState)
    (inputs : List VarId) (len : Nat) (idxVar : VarId) (inVars : List VarId)
    (body body' : ScalarExpr) (is : List Nat) (elems : List UInt64)
    (href : ExprRefines (.scalar body) (.scalar body'))
    (hsrc : evalParKernelLoop env st inputs len (.customScalar idxVar inVars body) is = .ok elems) :
    evalParKernelLoop env st inputs len (.customScalar idxVar inVars body') is = .ok elems := by
  induction is generalizing elems with
  | nil =>
    simp only [evalParKernelLoop] at hsrc ⊢
    exact hsrc
  | cons i rest ih =>
    simp only [evalParKernelLoop] at hsrc ⊢
    cases helem : evalParKernelElem env st inputs len (.customScalar idxVar inVars body) i with
    | error err => simp [helem] at hsrc
    | ok x =>
      cases hrest : evalParKernelLoop env st inputs len (.customScalar idxVar inVars body) rest with
      | error err => simp [helem, hrest] at hsrc
      | ok xs =>
        rw [helem, hrest] at hsrc
        have helem' :=
          evalParKernelElem_customScalar_refines env st inputs len idxVar inVars body body' i x href helem
        have hrest' := ih xs hrest
        rw [helem', hrest']
        exact hsrc

/-- Custom scalar `parFor` forward refinement. -/
theorem evalParFor_customScalar_refines (fuel : Nat) (env : VarEnv) (st : HeapState)
    (lenVar : VarId) (inputs : List VarId) (idxVar : VarId) (inVars : List VarId)
    (body body' : ScalarExpr) (pair : Val × HeapState)
    (href : ExprRefines (.scalar body) (.scalar body'))
    (hsrc : evalParFor fuel env st lenVar inputs (.customScalar idxVar inVars body) = .ok pair) :
    evalParFor fuel env st lenVar inputs (.customScalar idxVar inVars body') = .ok pair := by
  unfold evalParFor at hsrc ⊢
  cases hlen : env lenVar with
  | none => simp [hlen] at hsrc
  | some v =>
    rw [hlen] at hsrc
    cases v with
    | u64 n =>
      dsimp only [] at hsrc ⊢
      by_cases hfuel : (n.toNat > fuel)
      · simp [hfuel] at hsrc
      · simp only [hfuel, ↓reduceIte] at hsrc ⊢
        cases hvars : evalVarList env inputs with
        | error err => simp [hvars] at hsrc
        | ok vs =>
          rw [hvars] at hsrc
          cases hloop :
              evalParKernelLoop env st inputs n.toNat (.customScalar idxVar inVars body)
                (List.range n.toNat) with
          | error err => simp [hloop] at hsrc
          | ok elems =>
            rw [hloop] at hsrc
            have hloop' :=
              evalParKernelLoop_customScalar_refines env st inputs n.toNat idxVar inVars
                body body' (List.range n.toNat) elems href hloop
            rw [hloop']
            exact hsrc
    | _ => simp at hsrc

/-- Bounded sequential loop (`evalSeqLoop`) forward refinement. -/
theorem evalSeqLoop_refines (count curIdx : Nat) (idxVar accVar : VarId)
    (accVal : Val) (env : VarEnv) (st : HeapState)
    (step1 step2 : VarEnv → HeapState → Except UBError (Val × HeapState))
    (pair : Val × HeapState)
    (hstep : ∀ sEnv sSt v sSt', step1 sEnv sSt = .ok (v, sSt') → step2 sEnv sSt = .ok (v, sSt'))
    (hsrc : evalSeqLoop count curIdx idxVar accVar accVal env st step1 = .ok pair) :
    evalSeqLoop count curIdx idxVar accVar accVal env st step2 = .ok pair := by
  induction count generalizing curIdx accVal st with
  | zero =>
    simp only [evalSeqLoop] at hsrc ⊢
    exact hsrc
  | succ count' ih =>
    simp only [evalSeqLoop] at hsrc ⊢
    cases hs1 : step1 ((env.bind idxVar (.u64 curIdx.toUInt64)).bind accVar accVal) st with
    | error err => simp [hs1] at hsrc
    | ok p1 =>
      rcases p1 with ⟨nextAcc, st1⟩
      rw [hs1] at hsrc
      have hs2 :=
        hstep ((env.bind idxVar (.u64 curIdx.toUInt64)).bind accVar accVal) st nextAcc st1 hs1
      rw [hs2]
      exact ih (curIdx + 1) nextAcc st1 hsrc

/-- Simultaneous refinement of a sequential loop body and its continuation. -/
theorem CodeRefines.seqFor_congr {iv lv hv av ai : VarId} {aty : LNIRType}
    {step1 step2 k1 k2 : LNIRCode} (hstep : CodeRefines step1 step2) (hk : CodeRefines k1 k2) :
    CodeRefines (.seqFor iv lv hv av ai aty step1 k1) (.seqFor iv lv hv av ai aty step2 k2) := by
  intro fuel env st v st' hsrc
  simp only [evalCode] at hsrc ⊢
  split at hsrc <;> try contradiction
  next lo hi initVal hlo hhi hinit =>
    split at hsrc
    next acc st1 hloop =>
      rw [evalSeqLoop_refines _ _ _ _ _ _ _ _ _ _ (hstep fuel) hloop]
      exact hk fuel _ _ _ _ hsrc
    next => contradiction

/-- Code-level superoptimizer preserves operational semantics (`CodeRefines`). -/
theorem superoptCodeCore_sound (p : HardwareCostProfile) (targetLabel declName : String)
    (code : LNIRCode) :
    CodeRefines code (superoptCodeCore p targetLabel declName code).1 := by
  induction code with
  | letBind dst ty val k ih =>
    cases val with
    | scalar se =>
      simp only [superoptCodeCore]
      exact CodeRefines.letBind_congr (superoptScalarExprCore_sound p targetLabel declName se) ih
    | _ =>
      simp only [superoptCodeCore]
      exact CodeRefines.letBind_congr (ExprRefines.refl _) ih
  | rawStore pv iv vv ety k ih =>
    simp only [superoptCodeCore]
    exact CodeRefines.rawStore_congr ih
  | incRef ov c k ih =>
    simp only [superoptCodeCore]
    exact CodeRefines.incRef_congr ih
  | decRef ov c k ih =>
    simp only [superoptCodeCore]
    exact CodeRefines.decRef_congr ih
  | ite cv t e iht ihe =>
    simp only [superoptCodeCore]
    exact CodeRefines.ite_congr iht ihe
  | seqFor _ _ _ _ _ _ _ _ ihs ihk => exact CodeRefines.seqFor_congr ihs ihk
  | parFor ov lv ins ety kern k ih =>
    cases kern with
    | customScalar idxVar inVars body =>
      intro fuel env st v st' hsrc
      simp only [superoptCodeCore, evalCode] at hsrc ⊢
      cases hpar : evalParFor fuel env st lv ins (.customScalar idxVar inVars body) with
      | error err => simp [hpar] at hsrc
      | ok pair =>
        rw [hpar] at hsrc
        have hbody := superoptScalarExprCore_sound p targetLabel declName body
        have hpar' :=
          evalParFor_customScalar_refines fuel env st lv ins idxVar inVars body
            (superoptScalarExprCore p targetLabel declName body).1 pair hbody hpar
        rw [hpar']
        exact ih fuel (env.bind ov pair.1) pair.2 v st' hsrc
    | _ =>
      simp only [superoptCodeCore]
      exact CodeRefines.parFor_congr ih
  | ret _ =>
    simp only [superoptCodeCore]
    exact CodeRefines.refl _
  | unreachable =>
    simp only [superoptCodeCore]
    exact CodeRefines.refl _

theorem superoptCode_sound (target : SuperoptTarget) (declName : String) (code : LNIRCode) :
    CodeRefines code (superoptCode target declName code).1 :=
  superoptCodeCore_sound (HardwareCostProfile.forTarget target) target.toString declName code

theorem superoptDeclCore_sound (p : HardwareCostProfile) (targetLabel : String) (d : LNIRDecl) :
    CodeRefines d.body (superoptDeclCore p targetLabel d).1.body := by
  unfold superoptDeclCore
  simp only []
  exact superoptCodeCore_sound p targetLabel d.name d.body

/-- Declaration-level superoptimizer soundness (`superoptDecl_sound`). -/
theorem superoptDecl_sound (target : SuperoptTarget) (d : LNIRDecl) :
    CodeRefines d.body (superoptDecl target d).1.body :=
  superoptDeclCore_sound (HardwareCostProfile.forTarget target) target.toString d

theorem foldl_decls_mem_acc (p : HardwareCostProfile) (targetLabel : String)
    (ds : List LNIRDecl) (dAcc : List LNIRDecl) (rAcc : List SuperoptRewriteRecord)
    (x : LNIRDecl) (hx : x ∈ dAcc) :
    x ∈ (ds.foldl (fun (accD, accR) d =>
      let (d', recs) := superoptDeclCore p targetLabel d
      (accD ++ [d'], accR ++ recs)) (dAcc, rAcc)).1 := by
  induction ds generalizing dAcc rAcc with
  | nil => exact hx
  | cons d0 rest ih =>
    simp only [List.foldl]
    exact ih (dAcc ++ [(superoptDeclCore p targetLabel d0).1])
      (rAcc ++ (superoptDeclCore p targetLabel d0).2) (List.mem_append_left _ hx)

theorem foldl_decls_refines (p : HardwareCostProfile) (targetLabel : String)
    (ds : List LNIRDecl) (dAcc : List LNIRDecl) (rAcc : List SuperoptRewriteRecord) :
    ∀ d ∈ ds, ∃ d' ∈ (ds.foldl (fun (accD, accR) d =>
      let (d', recs) := superoptDeclCore p targetLabel d
      (accD ++ [d'], accR ++ recs)) (dAcc, rAcc)).1, CodeRefines d.body d'.body := by
  intro d hd
  induction ds generalizing dAcc rAcc with
  | nil => cases hd
  | cons d0 rest ih =>
    simp only [List.foldl, List.mem_cons] at hd ⊢
    cases hd with
    | inl heq =>
      subst d
      refine ⟨(superoptDeclCore p targetLabel d0).1, ?_, superoptDeclCore_sound p targetLabel d0⟩
      exact foldl_decls_mem_acc p targetLabel rest
        (dAcc ++ [(superoptDeclCore p targetLabel d0).1])
        (rAcc ++ (superoptDeclCore p targetLabel d0).2)
        (superoptDeclCore p targetLabel d0).1
        (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    | inr hmem =>
      exact ih (dAcc ++ [(superoptDeclCore p targetLabel d0).1])
        (rAcc ++ (superoptDeclCore p targetLabel d0).2) hmem

/-- Module-level superoptimizer soundness (`superoptModuleCore_sound`). -/
theorem superoptModuleCore_sound (p : HardwareCostProfile) (targetLabel : String) (m : LNIRModule) :
    ∀ d ∈ m.decls, ∃ d' ∈ (superoptModuleCore p targetLabel m).1.decls,
      CodeRefines d.body d'.body := by
  intro d hd
  unfold superoptModuleCore
  exact foldl_decls_refines p targetLabel m.decls [] [] d hd

/-- Module-level superoptimizer soundness (`superoptModule_sound`). -/
theorem superoptModule_sound (target : SuperoptTarget) (m : LNIRModule) :
    ∀ d ∈ m.decls, ∃ d' ∈ (superoptModule target m).1.decls, CodeRefines d.body d'.body :=
  superoptModuleCore_sound (HardwareCostProfile.forTarget target) target.toString m

/-- Profile-guided module-level superoptimizer soundness (`superoptModuleWithProfile_sound`). -/
theorem superoptModuleWithProfile_sound (p : HardwareCostProfile) (m : LNIRModule) :
    ∀ d ∈ m.decls, ∃ d' ∈ (superoptModuleWithProfile p m).1.decls, CodeRefines d.body d'.body :=
  superoptModuleCore_sound p s!"{p.target.toString}:{p.profileId}" m

end LeanNative.Proofs
