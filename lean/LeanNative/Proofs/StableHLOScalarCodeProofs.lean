import LeanNative.Proofs.StableHLOTensorProofs

/-!
# Pure Scalar / Eager-Select Code Lowering & Heap Simulation (`LeanNative.Proofs.StableHLOScalarCodeProofs`)

Proves:
1. Compositional pure/branching `lowerScalarCode_post` (`letBind (.scalar ...)`, `ite`
   lowered eagerly to `convert` + `select`, and `ret`).
2. Heap/environment simulation invariants (`HeapExtends`, `HLOValRel`, `HLOFullEnvAgree`)
   and `evalParFor` inversion lemmas used by `StableHLOKernelProofs` and `StableHLOLowerProofs`.
-/

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend.TargetIR
open LeanNative.Backend.StableHLOAst
open LeanNative.Backend.StableHLOLower
open LeanNative.Backend.LLVMLower (isI64Ty isI1Ty sameScalarTy)

/-! ## 1. Pure Scalar / Eager-Select `lowerScalarCode` Soundness -/

/-- Post-condition of `lowerScalarCode`: for every `fuel` and `st`, `evalCode` returns `(v, st)`
without touching the heap, and `evalOps` binds `res.reg` to `encodeScalarTyped res.ty v`. -/
def HLOScalarCodePost (env : VarEnv) (code : LNIRCode) (tenv : Env) (k : Nat)
    (res : HLOScalarRes) : Prop :=
  k ≤ res.nextTmp ∧
  res.ops.all isNonReturnOp = true ∧
  ∃ v w tenv',
    (∀ fuel st, evalCode fuel env st code = .ok (v, st)) ∧
    encodeScalarTyped res.ty v = some w ∧
    evalOps tenv res.ops = .ok tenv' ∧
    tenv' res.reg = some (mkScUi64 w) ∧
    HLORegFresh tenv' res.nextTmp ∧
    (∀ q, (∀ j, k ≤ j → j < res.nextTmp → q ≠ hloTmpReg j) → tenv' q = tenv q)

theorem hloEnvAgree_bind_scalar (Γ : HLOTyEnv) (env : VarEnv) (tenv : Env)
    (dst : VarId) (reg : String) (ty : LNIRType) (kn : Option Nat) (val : Val) (w : BitVec 64)
    (hAgree : HLOEnvAgree Γ env tenv)
    (hw : encodeScalarTyped ty val = some w)
    (hLook : tenv reg = some (mkScUi64 w)) :
    HLOEnvAgree (Γ.bind dst ⟨reg, .scalar ty kn⟩) (env.bind dst val) tenv := by
  intro x rx tyx knx hΓ
  unfold HLOTyEnv.bind at hΓ
  by_cases hxd : (x == dst) = true
  · simp only [hxd, ↓reduceIte, Option.some.injEq] at hΓ
    have hx_eq : x = dst := eq_of_beq hxd
    subst hx_eq
    injection hΓ with hr hk
    injection hk with hty _
    subst hr; subst hty
    exact ⟨val, w, VarEnv.bind_self env x val, hw, hLook⟩
  · have hxf : (x == dst) = false := Bool.eq_false_iff.mpr hxd
    simp only [hxf, Bool.false_eq_true, ↓reduceIte] at hΓ
    rcases hAgree x rx tyx knx hΓ with ⟨vx, wx, henv, hwx, htx⟩
    exact ⟨vx, wx, (VarEnv.bind_ne env dst x val hxf).trans henv, hwx, htx⟩

theorem lowerScalarCode_ite_step (Γ : HLOTyEnv) (env : VarEnv) (condVar : VarId)
    (thenB elseB : LNIRCode) (tenv : Env) (k : Nat) (cReg : String) (cTy : LNIRType)
    (kn : Option Nat) (rt re : HLOScalarRes)
    (hΓc : Γ condVar = some ⟨cReg, .scalar cTy kn⟩)
    (hAgree : HLOEnvAgree Γ env tenv) (hFr0 : HLORegFresh tenv k)
    (hcTy : (isI1Ty cTy || isI64Ty cTy) = true)
    (hsame : sameScalarTy rt.ty re.ty = true)
    (hT : HLOScalarCodePost env thenB tenv k rt)
    (hE : ∀ tenvT, evalOps tenv rt.ops = .ok tenvT →
      (∀ q, (∀ j, k ≤ j → j < rt.nextTmp → q ≠ hloTmpReg j) → tenvT q = tenv q) →
      HLORegFresh tenvT rt.nextTmp →
      HLOScalarCodePost env elseB tenvT rt.nextTmp re) :
    HLOScalarCodePost env (.ite condVar thenB elseB) tenv k
      ⟨rt.ty, hloTmpReg (re.nextTmp + 1), re.nextTmp + 2,
        rt.ops ++ re.ops ++
          [ StableHLOOp.convert (hloTmpReg re.nextTmp) cReg .i1
          , StableHLOOp.select (hloTmpReg (re.nextTmp + 1)) (hloTmpReg re.nextTmp) rt.reg re.reg ]⟩ := by
  rcases hAgree condVar cReg cTy kn hΓc with ⟨vc, wc, henvC, hEncC, hLookC0⟩
  rcases hT with ⟨ht_le, ht_all, vt, wt, tenvT, hEvT, hEncT, hExT, hLookT, hFrT, hFrameT⟩
  rcases hE tenvT hExT hFrameT hFrT with
    ⟨he_le, he_all, ve, we, tenvE, hEvE, hEncE, hExE, hLookE, hFrE, hFrameE⟩
  have hte_le : k ≤ re.nextTmp := Nat.le_trans ht_le he_le
  have hFrTE := frame_hloTmp_range tenv tenvT tenvE k rt.nextTmp re.nextTmp ht_le he_le hFrameT hFrameE
  have hExTE : evalOps tenv (rt.ops ++ re.ops) = .ok tenvE := by
    rw [evalOps_append_nonReturn rt.ops re.ops tenv tenvT ht_all hExT]
    exact hExE
  have hLookCE : tenvE cReg = some (mkScUi64 wc) := by
    rw [hFrTE cReg (fun j hj _ => operand_ne_hloTmp_of_fresh hLookC0 hFr0 hj)]
    exact hLookC0
  have hLookTE : tenvE rt.reg = some (mkScUi64 wt) := by
    rw [hFrameE rt.reg (fun j hj _ => operand_ne_hloTmp_of_fresh hLookT hFrT hj)]
    exact hLookT
  rcases sameScalarTy_eq_true rt.ty re.ty hsame with ⟨hte_eq, _⟩
  rw [← hte_eq] at hEncE
  let p := hloTmpReg re.nextTmp
  let d := hloTmpReg (re.nextTmp + 1)
  have hExec2 : ∀ (bSel : Bool) (tP : TensorVal),
      tP = { ty := scI1Ty, data := #[if bSel then 1#64 else 0#64] } →
      evalOp tenvE (.convert p cReg .i1) = .ok (tenvE.bind p tP) →
      evalOps tenvE [ .convert p cReg .i1, .select d p rt.reg re.reg ] =
        .ok ((tenvE.bind p tP).bind d (mkScUi64 (if bSel then wt else we))) := by
    intro bSel tP htP hs1
    subst htP
    rw [evalOps_cons_nonReturn _ _ _ rfl, hs1]
    dsimp only [bind, Except.bind]
    rw [evalOps_cons_nonReturn _ _ _ rfl]
    rw [evalOp_select_sc (tenvE.bind p _) d p rt.reg re.reg bSel wt we (env_bind_self _ _ _)
      (by rw [env_bind_ne _ _ _ _ (operand_ne_hloTmp_of_fresh hLookTE hFrE (Nat.le_refl _))]; exact hLookTE)
      (by rw [env_bind_ne _ _ _ _ (operand_ne_hloTmp_of_fresh hLookE hFrE (Nat.le_refl _))]; exact hLookE)]
    rfl
  have hAllTE : (rt.ops ++ re.ops ++
      [ StableHLOOp.convert p cReg .i1, StableHLOOp.select d p rt.reg re.reg ]).all
      isNonReturnOp = true := by
    rw [List.all_append, Bool.and_eq_true, List.all_append, Bool.and_eq_true]
    exact ⟨⟨ht_all, he_all⟩, rfl⟩
  simp only [Bool.or_eq_true] at hcTy
  rcases hcTy with hci1 | hci64
  · rw [isI1Ty_eq_true cTy hci1] at hEncC
    rcases typed_i1_inv vc wc hEncC with ⟨bc, rfl, rfl⟩
    have hbw : (if ((if bc then (1#64 : BitVec 64) else 0#64) == 0#64) then (0#64 : BitVec 64) else 1#64) =
        (if bc then 1#64 else 0#64) := by cases bc <;> rfl
    have hs1 : evalOp tenvE (.convert p cReg .i1) =
        .ok (tenvE.bind p { ty := scI1Ty, data := #[if bc then 1#64 else 0#64] }) := by
      rw [evalOp_convert_ui64_i1_sc tenvE p cReg (if bc then 1#64 else 0#64) hLookCE, hbw]
    let tP : TensorVal := { ty := scI1Ty, data := #[if bc then 1#64 else 0#64] }
    let tenvF := (tenvE.bind p tP).bind d (mkScUi64 (if bc then wt else we))
    dsimp only [HLOScalarCodePost, HLOScalarRes.nextTmp, HLOScalarRes.ops, HLOScalarRes.reg, HLOScalarRes.ty]
    refine ⟨Nat.le_trans hte_le (by omega), hAllTE, if bc then vt else ve, if bc then wt else we, tenvF,
      ?_, by cases bc <;> assumption, ?_, env_bind_self _ _ _,
      hloRegFresh_bind_lt _ (hloRegFresh_bind_lt _ hFrE (by omega)) (by omega), ?_⟩
    · intro fuel st
      unfold evalCode
      rw [henvC]
      cases bc
      · exact hEvE fuel st
      · exact hEvT fuel st
    · rw [evalOps_append_nonReturn (rt.ops ++ re.ops) _ tenv tenvE
        (by rw [List.all_append, Bool.and_eq_true]; exact ⟨ht_all, he_all⟩) hExTE]
      exact hExec2 bc tP rfl hs1
    · exact frame_hloTmp_range tenv tenvE _ k re.nextTmp (re.nextTmp + 2) hte_le (by omega) hFrTE
        (fun q hq => by
          dsimp only [tenvF, d, p]
          rw [env_bind_ne _ _ _ _ (hq (re.nextTmp + 1) (by omega) (by omega)),
              env_bind_ne _ _ _ _ (hq re.nextTmp (by omega) (by omega))])
  · rw [isI64Ty_eq_true cTy hci64] at hEncC
    rcases typed_i64_inv vc wc hEncC with ⟨nc, rfl, rfl⟩
    have hbw : (if (nc.toBitVec == 0#64) then (0#64 : BitVec 64) else 1#64) =
        (if (nc != 0) then 1#64 else 0#64) := by
      by_cases hnz : nc = 0
      · subst hnz; rfl
      · have h1 : (nc != 0) = true := bne_iff_ne.mpr hnz
        have h2 : (nc.toBitVec == 0#64) = false :=
          Bool.eq_false_iff.mpr (fun heq => hnz (UInt64.eq_of_toBitVec_eq (eq_of_beq heq)))
        rw [h1, h2]; rfl
    have hs1 : evalOp tenvE (.convert p cReg .i1) =
        .ok (tenvE.bind p { ty := scI1Ty, data := #[if (nc != 0) then 1#64 else 0#64] }) := by
      rw [evalOp_convert_ui64_i1_sc tenvE p cReg nc.toBitVec hLookCE, hbw]
    let tP : TensorVal := { ty := scI1Ty, data := #[if (nc != 0) then 1#64 else 0#64] }
    let tenvF := (tenvE.bind p tP).bind d (mkScUi64 (if (nc != 0) then wt else we))
    dsimp only [HLOScalarCodePost, HLOScalarRes.nextTmp, HLOScalarRes.ops, HLOScalarRes.reg, HLOScalarRes.ty]
    refine ⟨Nat.le_trans hte_le (by omega), hAllTE, if (nc != 0) then vt else ve,
      if (nc != 0) then wt else we, tenvF,
      ?_, by cases (nc != 0) <;> assumption, ?_, env_bind_self _ _ _,
      hloRegFresh_bind_lt _ (hloRegFresh_bind_lt _ hFrE (by omega)) (by omega), ?_⟩
    · intro fuel st
      unfold evalCode
      rw [henvC]
      dsimp only
      cases (nc != 0)
      · exact hEvE fuel st
      · exact hEvT fuel st
    · rw [evalOps_append_nonReturn (rt.ops ++ re.ops) _ tenv tenvE
        (by rw [List.all_append, Bool.and_eq_true]; exact ⟨ht_all, he_all⟩) hExTE]
      exact hExec2 (nc != 0) tP rfl hs1
    · exact frame_hloTmp_range tenv tenvE _ k re.nextTmp (re.nextTmp + 2) hte_le (by omega) hFrTE
        (fun q hq => by
          dsimp only [tenvF, d, p]
          rw [env_bind_ne _ _ _ _ (hq (re.nextTmp + 1) (by omega) (by omega)),
              env_bind_ne _ _ _ _ (hq re.nextTmp (by omega) (by omega))])

theorem evalExpr_scalar_eq (env : VarEnv) (st : HeapState) (se : ScalarExpr) :
    evalExpr env st (.scalar se) = (evalScalarExpr env se).map fun v => (v, st) := by
  simp only [evalExpr]
  cases evalScalarExpr env se <;> rfl

theorem lowerScalarCode_post (Γ : HLOTyEnv) (env : VarEnv) (code : LNIRCode)
    (tenv : Env) (k : Nat) (res : HLOScalarRes)
    (hAgree : HLOEnvAgree Γ env tenv) (hFr : HLORegFresh tenv k)
    (hLow : lowerScalarCode Γ code k = some res) :
    HLOScalarCodePost env code tenv k res := by
  induction code generalizing Γ env tenv k res with
  | ret v =>
    dsimp [lowerScalarCode] at hLow
    cases hΓ : Γ v with
    | none => simp [hΓ] at hLow
    | some e =>
      rcases e with ⟨r, kind⟩
      cases kind with
      | tensor1D _ => simp [hΓ] at hLow
      | scalar ty kn =>
        simp only [hΓ] at hLow
        rcases hAgree v r ty kn hΓ with ⟨val, w, henv, hw, htenv⟩
        by_cases hty : (isI64Ty ty || isI1Ty ty) = true
        · simp only [hty, ↓reduceIte, Option.some.injEq] at hLow
          subst hLow
          exact ⟨Nat.le_refl k, rfl, val, w, tenv,
            fun _ _ => by unfold evalCode; rw [henv], hw, rfl, htenv, hFr, fun _ _ => rfl⟩
        · simp [hty] at hLow
  | letBind dst declTy expr kCode ih =>
    cases expr with
    | scalar se =>
      dsimp [lowerScalarCode] at hLow
      cases hLs : lowerScalarExpr Γ se k with
      | none => simp [hLs] at hLow
      | some rs =>
        simp only [hLs, Option.bind] at hLow
        by_cases hsame : sameScalarTy rs.ty declTy = true
        · simp only [hsame, ↓reduceIte] at hLow
          cases hLk : lowerScalarCode (Γ.bind dst ⟨rs.reg, .scalar declTy (knownNatOfScalarExpr se)⟩)
              kCode rs.nextTmp with
          | none => simp [hLk] at hLow
          | some rk =>
            simp only [hLk, Option.some.injEq] at hLow
            subst hLow
            rcases lowerHLOScalarExpr_post Γ env se tenv k rs hAgree hFr hLs with
              ⟨hs_le, hs_all, vs, ws, tenvS, hEvS, hEncS, hExS, hLookS, hFrS, hFrameS⟩
            rcases sameScalarTy_eq_true rs.ty declTy hsame with ⟨hdecl_eq, _⟩
            rw [hdecl_eq] at hEncS
            have hAgS := hloEnvAgree_preserved Γ env tenv tenvS k rs.nextTmp hAgree hFr hFrameS
            have hAgBind := hloEnvAgree_bind_scalar Γ env tenvS dst rs.reg declTy
              (knownNatOfScalarExpr se) vs ws hAgS hEncS hLookS
            rcases ih (Γ.bind dst ⟨rs.reg, .scalar declTy (knownNatOfScalarExpr se)⟩)
                (env.bind dst vs) tenvS rs.nextTmp rk hAgBind hFrS hLk with
              ⟨hk_le, hk_all, vk, wk, tenvK, hEvK, hEncK, hExK, hLookK, hFrK, hFrameK⟩
            refine ⟨Nat.le_trans hs_le hk_le, ?_, vk, wk, tenvK, ?_, hEncK, ?_, hLookK, hFrK,
              frame_hloTmp_range tenv tenvS tenvK k rs.nextTmp rk.nextTmp hs_le hk_le hFrameS hFrameK⟩
            · rw [List.all_append, Bool.and_eq_true]; exact ⟨hs_all, hk_all⟩
            · intro fuel st
              unfold evalCode
              rw [evalExpr_scalar_eq env st se, hEvS]
              exact hEvK fuel st
            · rw [evalOps_append_nonReturn rs.ops rk.ops tenv tenvS hs_all hExS]
              exact hExK
        · simp [hsame] at hLow
    | _ => simp [lowerScalarCode] at hLow
  | ite condVar thenB elseB iht ihe =>
    dsimp [lowerScalarCode] at hLow
    cases hΓc : Γ condVar with
    | none => simp [hΓc] at hLow
    | some e =>
      rcases e with ⟨cReg, kind⟩
      cases kind with
      | tensor1D _ => simp [hΓc] at hLow
      | scalar cTy kn =>
        simp only [hΓc] at hLow
        by_cases hcTy : (isI1Ty cTy || isI64Ty cTy) = true
        · simp only [hcTy, ↓reduceIte] at hLow
          cases hLt : lowerScalarCode Γ thenB k with
          | none => simp [hLt] at hLow
          | some rt =>
            simp only [hLt, Option.bind] at hLow
            cases hLe : lowerScalarCode Γ elseB rt.nextTmp with
            | none => simp [hLe] at hLow
            | some re =>
              simp only [hLe] at hLow
              by_cases hsame : sameScalarTy rt.ty re.ty = true
              · simp only [hsame, ↓reduceIte, Option.some.injEq] at hLow
                subst hLow
                exact lowerScalarCode_ite_step Γ env condVar thenB elseB tenv k cReg cTy kn rt re
                  hΓc hAgree hFr hcTy hsame
                  (iht Γ env tenv k rt hAgree hFr hLt)
                  (fun tenvT _ hFrameT hFrT =>
                    ihe Γ env tenvT rt.nextTmp re
                      (hloEnvAgree_preserved Γ env tenv tenvT k rt.nextTmp hAgree hFr hFrameT)
                      hFrT hLe)
              · simp [hsame] at hLow
        · simp [hcTy] at hLow
  | _ => simp [lowerScalarCode] at hLow

/-! ## 2. Heap Monotonicity, Full Environment Simulation & `evalParFor` Inversions -/

/-- Monotonic heap extension preserving all existing `ArrayBuffer`s with `id ≤ st.nextId`. -/
def HeapExtends (st st' : HeapState) : Prop :=
  st.nextId ≤ st'.nextId ∧
  ∀ bufId, bufId ≤ st.nextId → st'.findBuffer bufId = st.findBuffer bufId

theorem heapExtends_trans {s1 s2 s3 : HeapState}
    (h12 : HeapExtends s1 s2) (h23 : HeapExtends s2 s3) :
    HeapExtends s1 s3 :=
  ⟨Nat.le_trans h12.1 h23.1,
    fun bid hbid => (h23.2 bid (Nat.le_trans hbid h12.1)).trans (h12.2 bid hbid)⟩

/-- Value relation linking an `HLOVarKind`, an LNIR `Val` in `st`, and a `StableHLOAst.TensorVal`. -/
def HLOValRel (st : HeapState) : HLOVarKind → Val → TensorVal → Prop
  | .scalar ty kn, v, tv =>
    (∃ w, encodeScalarTyped ty v = some w ∧ tv = mkScUi64 w) ∧
    (∀ m, kn = some m → ∃ u : UInt64, v = .u64 u ∧ u.toNat = m)
  | .tensor1D n, v, tv =>
    ∃ bufId buf,
      v = .sarrayId bufId ∧
      bufId ≤ st.nextId ∧
      st.findBuffer bufId = some buf ∧
      buf.data.size = n ∧
      tv = mkVecUi64 buf.data

theorem hloValRel_mono {st st' : HeapState} {vk : HLOVarKind} {v : Val} {tv : TensorVal}
    (hExt : HeapExtends st st') (hRel : HLOValRel st vk v tv) :
    HLOValRel st' vk v tv := by
  cases vk with
  | scalar _ _ => exact hRel
  | tensor1D n =>
    rcases hRel with ⟨bid, buf, hv, hle, hfind, hsz, htv⟩
    exact ⟨bid, buf, hv, Nat.le_trans hle hExt.1, (hExt.2 bid hle).trans hfind, hsz, htv⟩

/-- Full environment simulation across both scalar and 1-D tensor bindings. -/
def HLOFullEnvAgree (Γ : HLOTyEnv) (env : VarEnv) (st : HeapState) (tenv : Env) : Prop :=
  ∀ v r vk, Γ v = some ⟨r, vk⟩ →
    ∃ val tv,
      env v = some val ∧
      HLOValRel st vk val tv ∧
      tenv r = some tv

theorem hloFullEnvAgree_to_scalar {Γ : HLOTyEnv} {env : VarEnv} {st : HeapState} {tenv : Env}
    (h : HLOFullEnvAgree Γ env st tenv) :
    HLOEnvAgree Γ env tenv := by
  intro v r ty kn hΓ
  rcases h v r (.scalar ty kn) hΓ with ⟨val, tv, henv, ⟨⟨w, hw, htv⟩, _⟩, htenv⟩
  subst htv
  exact ⟨val, w, henv, hw, htenv⟩

theorem hloFullEnvAgree_preserved (Γ : HLOTyEnv) (env : VarEnv) (st st' : HeapState)
    (tenv tenv' : Env) (k nextK : Nat)
    (hAgree : HLOFullEnvAgree Γ env st tenv)
    (hExt : HeapExtends st st')
    (hFr : HLORegFresh tenv k)
    (hFrame : ∀ q, (∀ j, k ≤ j → j < nextK → q ≠ hloTmpReg j) → tenv' q = tenv q) :
    HLOFullEnvAgree Γ env st' tenv' := by
  intro v r vk hΓ
  rcases hAgree v r vk hΓ with ⟨val, tv, henv, hrel, htenv⟩
  have hne : ∀ j, k ≤ j → j < nextK → r ≠ hloTmpReg j := by
    intro j hkj _ heq
    have hnone := hFr j hkj
    rw [← heq, htenv] at hnone
    nomatch hnone
  exact ⟨val, tv, henv, hloValRel_mono hExt hrel, (hFrame r hne).trans htenv⟩

theorem hloFullEnvAgree_bind (Γ : HLOTyEnv) (env : VarEnv) (st : HeapState) (tenv : Env)
    (dst : VarId) (reg : String) (vk : HLOVarKind) (val : Val) (tv : TensorVal)
    (hAgree : HLOFullEnvAgree Γ env st tenv)
    (hRel : HLOValRel st vk val tv)
    (hLook : tenv reg = some tv) :
    HLOFullEnvAgree (Γ.bind dst ⟨reg, vk⟩) (env.bind dst val) st tenv := by
  intro x rx vkx hΓ
  unfold HLOTyEnv.bind at hΓ
  by_cases hxd : (x == dst) = true
  · simp only [hxd, ↓reduceIte, Option.some.injEq] at hΓ
    have hx_eq : x = dst := eq_of_beq hxd
    subst hx_eq
    injection hΓ with hr hk
    subst hr; subst hk
    exact ⟨val, tv, VarEnv.bind_self env x val, hRel, hLook⟩
  · have hxf : (x == dst) = false := Bool.eq_false_iff.mpr hxd
    simp only [hxf, Bool.false_eq_true, ↓reduceIte] at hΓ
    rcases hAgree x rx vkx hΓ with ⟨vx, tvx, henv, hrelx, htx⟩
    exact ⟨vx, tvx, (VarEnv.bind_ne env dst x val hxf).trans henv, hrelx, htx⟩

theorem evalParKernelLoop_eq_map (env : VarEnv) (st : HeapState) (inputs : List VarId)
    (len : Nat) (kernel : ParallelKernelKind) (f : Nat → UInt64) :
    ∀ (is : List Nat),
      (∀ i, i ∈ is → evalParKernelElem env st inputs len kernel i = .ok (f i)) →
      evalParKernelLoop env st inputs len kernel is = .ok (is.map f)
  | [], _ => rfl
  | i :: is, hf => by
    simp only [evalParKernelLoop, List.map_cons]
    rw [hf i (List.mem_cons_self ..),
      evalParKernelLoop_eq_map env st inputs len kernel f is
        (fun j hj => hf j (List.mem_cons_of_mem i hj))]

theorem readElem_of_findBuffer (st : HeapState) (bid : Nat) (buf : ArrayBuffer) (i : Nat)
    (hfind : st.findBuffer bid = some buf) (hi : i < buf.data.size) :
    st.readElem bid i = .ok (buf.data.getD i 0) := by
  simp [HeapState.readElem, hfind, hi, Array.getD]

theorem allocOutBuf_rel (st : HeapState) (outData : Array UInt64) :
    let outId := st.nextId + 1
    let outBuf : ArrayBuffer := { id := outId, exclusive := true, data := outData }
    let st' := { st with buffers := outBuf :: st.buffers, nextId := outId }
    HeapExtends st st' ∧
    HLOValRel st' (.tensor1D outData.size) (.sarrayId outId) (mkVecUi64 outData) := by
  refine ⟨⟨Nat.le_succ _, fun bid hbid => ?_⟩,
    st.nextId + 1, { id := st.nextId + 1, exclusive := true, data := outData },
    rfl, Nat.le_refl _, ?_, rfl, rfl⟩
  · have hne : ((st.nextId + 1 == bid) = false) :=
      Bool.eq_false_iff.mpr (fun heq => by
        have := eq_of_beq heq
        have hlt : bid < st.nextId + 1 := Nat.lt_succ_of_le hbid
        omega)
    simp [HeapState.findBuffer, hne]
  · simp [HeapState.findBuffer]

theorem evalParFor_mapScaleAdd_inv (fuel : Nat) (env : VarEnv) (st st' : HeapState)
    (lenVar x : VarId) (uLen scale bias : UInt64) (bx : Nat)
    (outVal : Val) (f : Nat → UInt64)
    (hLen : env lenVar = some (.u64 uLen))
    (hX : env x = some (.sarrayId bx))
    (hElem : ∀ i, i < uLen.toNat →
      evalParKernelElem env st [x] uLen.toNat (.mapScaleAdd scale bias) i = .ok (f i))
    (hEval : evalParFor fuel env st lenVar [x] (.mapScaleAdd scale bias) = .ok (outVal, st')) :
    outVal = .sarrayId (st.nextId + 1) ∧
    st' = { st with
      buffers := { id := st.nextId + 1, exclusive := true,
                   data := ((List.range uLen.toNat).map f).toArray } :: st.buffers,
      nextId := st.nextId + 1 } := by
  unfold evalParFor at hEval
  rw [hLen] at hEval
  dsimp only at hEval
  by_cases hgt : uLen.toNat > fuel
  · simp [hgt] at hEval
  · simp only [hgt, ↓reduceIte, evalVarList, hX, maskElemVal_i64_fun, id_eq, beq_self_eq_true] at hEval
    rw [evalParKernelLoop_eq_map env st [x] uLen.toNat (.mapScaleAdd scale bias) f
      (List.range uLen.toNat) (fun i hi => hElem i (List.mem_range.mp hi))] at hEval
    simp only [List.map_id] at hEval
    injection hEval with hp
    injection hp with hv hst
    exact ⟨hv.symm, hst.symm⟩

def parKernelOutData (kernel : ParallelKernelKind) (elems : List UInt64) : Array UInt64 :=
  match kernel with
  | .dotProduct => #[elems.foldl (· + ·) 0]
  | _ => elems.toArray

theorem evalParFor_inv_2 (fuel : Nat) (env : VarEnv) (st st' : HeapState)
    (lenVar x y : VarId) (uLen : UInt64) (bx by_ : Nat)
    (kernel : ParallelKernelKind) (outVal : Val) (f : Nat → UInt64)
    (hLen : env lenVar = some (.u64 uLen))
    (hX : env x = some (.sarrayId bx)) (hY : env y = some (.sarrayId by_))
    (hElem : ∀ i, i < uLen.toNat → evalParKernelElem env st [x, y] uLen.toNat kernel i = .ok (f i))
    (hEval : evalParFor fuel env st lenVar [x, y] kernel = .ok (outVal, st')) :
    outVal = .sarrayId (st.nextId + 1) ∧
    st' = { st with
      buffers := { id := st.nextId + 1, exclusive := true,
                   data := parKernelOutData kernel ((List.range uLen.toNat).map f) } :: st.buffers,
      nextId := st.nextId + 1 } := by
  unfold evalParFor at hEval
  rw [hLen] at hEval
  dsimp only at hEval
  by_cases hgt : uLen.toNat > fuel
  · simp [hgt] at hEval
  · simp only [hgt, ↓reduceIte, evalVarList, hX, hY, maskElemVal_i64_fun, id_eq, beq_self_eq_true] at hEval
    rw [evalParKernelLoop_eq_map env st [x, y] uLen.toNat kernel f (List.range uLen.toNat)
      (fun i hi => hElem i (List.mem_range.mp hi))] at hEval
    cases kernel <;>
    · simp only [parKernelOutData, List.map_id] at hEval ⊢
      injection hEval with hp
      injection hp with hv hst
      exact ⟨hv.symm, hst.symm⟩

end LeanNative.Proofs
