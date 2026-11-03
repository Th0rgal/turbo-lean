import LeanNative.Proofs.StableHLOKernelProofs

/-!
# Compositional `LNIRCode` & Parameter Lowering Proofs (`LeanNative.Proofs.StableHLOCodeProofs`)

Proves:
1. `lowerHLOCode_post`: compositional simulation for `StableHLOLower.lowerCode` across
   scalar `letBind`, `sarrayLen`, static-index `sarrayGet` (`slice` + `reshape`),
   `parFor` tensor kernels, scalar `ite` diamonds, and `ret`.
2. `bindHLOParams_post`: left-to-right parameter binding simulation between
   `initHLOParams` and `StableHLOAst.bindArgs`.
-/

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend.TargetIR
open LeanNative.Backend.StableHLOAst
open LeanNative.Backend.StableHLOLower
open LeanNative.Backend.LLVMLower (isI64Ty isI1Ty sameScalarTy)

/-! ## 1. Value Well-Formedness & `knownNatOfScalarExpr` Helpers -/

abbrev HLOCodePost := HLOParKernelPost

theorem knownNatOfScalarExpr_inv (env : VarEnv) (se : ScalarExpr) (v : Val) (m : Nat)
    (hEv : evalScalarExpr env se = .ok v)
    (hKn : knownNatOfScalarExpr se = some m) :
    ∃ u : UInt64, v = .u64 u ∧ u.toNat = m := by
  cases se <;> simp [knownNatOfScalarExpr] at hKn
  case constU64 u =>
    simp [evalScalarExpr] at hEv
    subst hEv
    subst hKn
    exact ⟨u, rfl, rfl⟩

theorem hloValRel_wellFormed {st : HeapState} {vk : HLOVarKind} {v : Val} {tv : TensorVal}
    (h : HLOValRel st vk v tv) :
    tv.ty = vk.tensorType ∧ checkWellFormed tv = .ok () := by
  cases vk with
  | scalar ty kn =>
    rcases h with ⟨⟨w, _, rfl⟩, _⟩
    exact ⟨rfl, checkWellFormed_mkScUi64 w⟩
  | tensor1D n =>
    rcases h with ⟨_, buf, _, _, _, hsz, rfl⟩
    refine ⟨?_, checkWellFormed_mkVecUi64 buf.data⟩
    simp [mkVecUi64, HLOVarKind.tensorType, hsz]

theorem lookup_of_hloValRel (st : HeapState) (tenv : Env) (r : String) (vk : HLOVarKind)
    (v : Val) (tv : TensorVal) (hRel : HLOValRel st vk v tv) (hLook : tenv r = some tv) :
    lookup tenv r = .ok tv := by
  simp [lookup, hLook, (hloValRel_wellFormed hRel).2, Bind.bind, Except.bind]

/-! ## 2. Step Lemmas for `sarrayLen` and `sarrayGet` -/

theorem lowerHLOCode_sarrayLen_step (Γ : HLOTyEnv) (fuel : Nat) (env : VarEnv)
    (st st' : HeapState) (dst arrVar : VarId) (kCode : LNIRCode) (retVal : Val)
    (tenv : Env) (k n : Nat) (rArr : String) (rk : HLOCodeRes)
    (hΓ : Γ arrVar = some ⟨rArr, .tensor1D n⟩)
    (hn : n < 2 ^ 64)
    (hAgree : HLOFullEnvAgree Γ env st tenv)
    (hFr : HLORegFresh tenv k)
    (hEval : evalCode fuel env st (.letBind dst .i64 (.sarrayLen arrVar) kCode) = .ok (retVal, st'))
    (hIH : ∀ tenv1,
      HLOFullEnvAgree (Γ.bind dst ⟨hloTmpReg k, .scalar .i64 (some n)⟩)
        (env.bind dst (.u64 n.toUInt64)) st tenv1 →
      HLORegFresh tenv1 (k + 1) →
      evalCode fuel (env.bind dst (.u64 n.toUInt64)) st kCode = .ok (retVal, st') →
      HLOCodePost st st' retVal tenv1 (k + 1) rk) :
    HLOCodePost st st' retVal tenv k
      ⟨rk.outKind, rk.reg, rk.nextTmp,
        StableHLOOp.constant (hloTmpReg k) (mkScUi64 (BitVec.ofNat 64 n)) :: rk.ops⟩ := by
  rcases hAgree arrVar rArr (.tensor1D n) hΓ with
    ⟨_, _, henvArr, ⟨bid, buf, rfl, _, hFind, hSz, rfl⟩, _⟩
  unfold evalCode at hEval
  simp only [evalExpr, henvArr, hFind, hSz] at hEval
  let tvN := mkScUi64 (BitVec.ofNat 64 n)
  let tenv1 := tenv.bind (hloTmpReg k) tvN
  have huNat : n.toUInt64.toNat = n := by
    simp [Nat.toUInt64, Nat.mod_eq_of_lt hn]
  have hRelN : HLOValRel st (.scalar .i64 (some n)) (.u64 n.toUInt64) tvN := by
    refine ⟨⟨BitVec.ofNat 64 n, rfl, rfl⟩, ?_⟩
    intro m hm
    injection hm with hm_eq
    subst hm_eq
    exact ⟨n.toUInt64, rfl, huNat⟩
  have hFrame1 : ∀ q, (∀ j, k ≤ j → j < k + 1 → q ≠ hloTmpReg j) → tenv1 q = tenv q :=
    fun q hq => env_bind_ne tenv (hloTmpReg k) q tvN (hq k (Nat.le_refl k) (Nat.lt_succ_self k))
  have hAg1 := hloFullEnvAgree_preserved Γ env st st tenv tenv1 k (k + 1)
    hAgree ⟨Nat.le_refl _, fun _ _ => rfl⟩ hFr hFrame1
  have hAgBind := hloFullEnvAgree_bind Γ env st tenv1 dst (hloTmpReg k)
    (.scalar .i64 (some n)) (.u64 n.toUInt64) tvN hAg1 hRelN (env_bind_self _ _ _)
  have hFr1 : HLORegFresh tenv1 (k + 1) := hloRegFresh_bind_lt tvN hFr (Nat.lt_succ_self k)
  rcases hIH tenv1 hAgBind hFr1 hEval with
    ⟨hk_le, hk_all, hExtK, tvOut, tenvK, hRelK, hExK, hLookK, hFrK, hFrameK⟩
  refine ⟨by dsimp only; omega, ?_, hExtK, tvOut, tenvK, hRelK, ?_, hLookK, hFrK,
    frame_hloTmp_range tenv tenv1 tenvK k (k + 1) rk.nextTmp (Nat.le_succ k) hk_le hFrame1 hFrameK⟩
  · simp [List.all_cons, isNonReturnOp, hk_all]
  · rw [evalOps_cons_nonReturn _ _ _ rfl, evalOp_constant_sc]
    exact hExK

theorem lowerHLOCode_sarrayGet_step (Γ : HLOTyEnv) (fuel : Nat) (env : VarEnv)
    (st st' : HeapState) (dst arrVar idxVar : VarId) (kCode : LNIRCode) (retVal : Val)
    (tenv : Env) (k n idx : Nat) (rArr rIdx : String) (rk : HLOCodeRes)
    (hΓA : Γ arrVar = some ⟨rArr, .tensor1D n⟩)
    (hΓI : Γ idxVar = some ⟨rIdx, .scalar .i64 (some idx)⟩)
    (hIdxLt : idx < n)
    (hAgree : HLOFullEnvAgree Γ env st tenv)
    (hFr : HLORegFresh tenv k)
    (hEval : evalCode fuel env st (.letBind dst .i64 (.sarrayGet arrVar idxVar .i64) kCode) =
      .ok (retVal, st'))
    (hIH : ∀ (elem : UInt64) (tenv2 : Env),
      HLOFullEnvAgree (Γ.bind dst ⟨hloTmpReg (k + 1), .scalar .i64 none⟩)
        (env.bind dst (.u64 elem)) st tenv2 →
      HLORegFresh tenv2 (k + 2) →
      evalCode fuel (env.bind dst (.u64 elem)) st kCode = .ok (retVal, st') →
      (∀ q, (∀ j, k ≤ j → j < k + 2 → q ≠ hloTmpReg j) → tenv2 q = tenv q) →
      evalOps tenv [ .slice (hloTmpReg k) rArr [idx] [idx + 1] [1]
                   , .reshape (hloTmpReg (k + 1)) (hloTmpReg k) [] ] = .ok tenv2 →
      HLOCodePost st st' retVal tenv2 (k + 2) rk) :
    HLOCodePost st st' retVal tenv k
      ⟨rk.outKind, rk.reg, rk.nextTmp,
        [ .slice (hloTmpReg k) rArr [idx] [idx + 1] [1]
        , .reshape (hloTmpReg (k + 1)) (hloTmpReg k) [] ] ++ rk.ops⟩ := by
  rcases hAgree arrVar rArr (.tensor1D n) hΓA with
    ⟨_, _, henvArr, ⟨bid, buf, rfl, _, hFind, hSz, rfl⟩, hLookArr⟩
  rcases hAgree idxVar rIdx (.scalar .i64 (some idx)) hΓI with
    ⟨_, _, henvIdx, ⟨_, hKnIdx⟩, _⟩
  rcases hKnIdx idx rfl with ⟨uIdx, rfl, huIdx⟩
  have hLtSz : idx < buf.data.size := by omega
  unfold evalCode at hEval
  simp only [evalExpr, henvArr, henvIdx, huIdx,
    readElem_of_findBuffer st bid buf idx hFind hLtSz] at hEval
  have hGetD : buf.data.getD idx 0 = buf.data[idx] := by simp [Array.getD, hLtSz]
  rw [hGetD] at hEval
  let elem := buf.data[idx]
  let tenv1 := tenv.bind (hloTmpReg k) (mkVecUi64 #[elem])
  let tenv2 := tenv1.bind (hloTmpReg (k + 1)) (mkScUi64 elem.toBitVec)
  have hs1 := evalOp_slice_one tenv (hloTmpReg k) rArr buf.data idx hLookArr hLtSz
  have hs2 := evalOp_reshape_vec1_to_scalar tenv1 (hloTmpReg (k + 1)) (hloTmpReg k) elem
    (env_bind_self _ _ _)
  have hEx0 : evalOps tenv
      [ .slice (hloTmpReg k) rArr [idx] [idx + 1] [1]
      , .reshape (hloTmpReg (k + 1)) (hloTmpReg k) [] ] = .ok tenv2 := by
    rw [evalOps_cons_nonReturn _ _ _ rfl, hs1]
    dsimp only [Bind.bind, Except.bind]
    rw [evalOps_cons_nonReturn _ _ _ rfl, hs2]
    rfl
  have hFrame2 : ∀ q, (∀ j, k ≤ j → j < k + 2 → q ≠ hloTmpReg j) → tenv2 q = tenv q := by
    intro q hq
    dsimp only [tenv2, tenv1]
    rw [env_bind_ne _ _ _ _ (hq (k + 1) (by omega) (by omega)),
        env_bind_ne _ _ _ _ (hq k (by omega) (by omega))]
  have hAg2 := hloFullEnvAgree_preserved Γ env st st tenv tenv2 k (k + 2)
    hAgree ⟨Nat.le_refl _, fun _ _ => rfl⟩ hFr hFrame2
  have hRelElem : HLOValRel st (.scalar .i64 none) (.u64 elem) (mkScUi64 elem.toBitVec) :=
    ⟨⟨elem.toBitVec, rfl, rfl⟩, fun _ hm => nomatch hm⟩
  have hAgBind := hloFullEnvAgree_bind Γ env st tenv2 dst (hloTmpReg (k + 1))
    (.scalar .i64 none) (.u64 elem) (mkScUi64 elem.toBitVec) hAg2 hRelElem (env_bind_self _ _ _)
  have hFr2 : HLORegFresh tenv2 (k + 2) :=
    hloRegFresh_bind_lt _ (hloRegFresh_bind_lt _ hFr (by omega)) (by omega)
  rcases hIH elem tenv2 hAgBind hFr2 hEval hFrame2 hEx0 with
    ⟨hk_le, hk_all, hExtK, tvOut, tenvK, hRelK, hExK, hLookK, hFrK, hFrameK⟩
  refine ⟨by dsimp only; omega, ?_, hExtK, tvOut, tenvK, hRelK, ?_, hLookK, hFrK,
    frame_hloTmp_range tenv tenv2 tenvK k (k + 2) rk.nextTmp (by omega) hk_le hFrame2 hFrameK⟩
  · rw [List.all_append, Bool.and_eq_true]
    exact ⟨rfl, hk_all⟩
  · rw [evalOps_append_nonReturn _ rk.ops tenv tenv2 rfl hEx0]
    exact hExK

/-! ## 3. Compositional `lowerHLOCode_post` -/

theorem lowerHLOCode_post (Γ : HLOTyEnv) (fuel : Nat) (env : VarEnv) (st st' : HeapState)
    (code : LNIRCode) (retVal : Val) (tenv : Env) (k : Nat) (res : HLOCodeRes)
    (hAgree : HLOFullEnvAgree Γ env st tenv) (hFr : HLORegFresh tenv k)
    (hLow : lowerCode Γ code k = some res)
    (hEval : evalCode fuel env st code = .ok (retVal, st')) :
    HLOCodePost st st' retVal tenv k res := by
  induction code generalizing Γ env st st' retVal tenv k res with
  | ret v =>
    dsimp [lowerCode] at hLow
    cases hΓ : Γ v with
    | none => simp [hΓ] at hLow
    | some e =>
      rcases e with ⟨r, vk⟩
      rcases hAgree v r vk hΓ with ⟨val, tv, henv, hrel, htenv⟩
      unfold evalCode at hEval
      rw [henv] at hEval
      injection hEval with hp
      injection hp with hv hst
      subst hv
      subst hst
      cases vk with
      | scalar ty kn =>
        simp only [hΓ] at hLow
        by_cases hty : (isI64Ty ty || isI1Ty ty) = true
        · simp only [hty, ↓reduceIte, Option.some.injEq] at hLow
          subst hLow
          exact ⟨Nat.le_refl k, rfl, ⟨Nat.le_refl _, fun _ _ => rfl⟩,
            tv, tenv, hrel, rfl, htenv, hFr, fun _ _ => rfl⟩
        · simp [hty] at hLow
      | tensor1D n =>
        simp only [hΓ, Option.some.injEq] at hLow
        subst hLow
        exact ⟨Nat.le_refl k, rfl, ⟨Nat.le_refl _, fun _ _ => rfl⟩,
          tv, tenv, hrel, rfl, htenv, hFr, fun _ _ => rfl⟩
  | letBind dst declTy expr kCode ih =>
    cases expr with
    | scalar se =>
      dsimp [lowerCode] at hLow
      cases hLs : lowerScalarExpr Γ se k with
      | none => simp [hLs] at hLow
      | some rs =>
        simp only [hLs, Option.bind] at hLow
        by_cases hsame : sameScalarTy rs.ty declTy = true
        · simp only [hsame, ↓reduceIte] at hLow
          cases hLk : lowerCode (Γ.bind dst ⟨rs.reg, .scalar declTy (knownNatOfScalarExpr se)⟩)
              kCode rs.nextTmp with
          | none => simp [hLk] at hLow
          | some rk =>
            simp only [hLk, Option.some.injEq] at hLow
            subst hLow
            rcases lowerHLOScalarExpr_post Γ env se tenv k rs
                (hloFullEnvAgree_to_scalar hAgree) hFr hLs with
              ⟨hs_le, hs_all, vs, ws, tenvS, hEvS, hEncS, hExS, hLookS, hFrS, hFrameS⟩
            rcases sameScalarTy_eq_true rs.ty declTy hsame with ⟨hdecl_eq, _⟩
            rw [hdecl_eq] at hEncS
            unfold evalCode at hEval
            rw [evalExpr_scalar_eq env st se, hEvS] at hEval
            have hRelS : HLOValRel st (.scalar declTy (knownNatOfScalarExpr se)) vs (mkScUi64 ws) :=
              ⟨⟨ws, hEncS, rfl⟩, fun m hm => knownNatOfScalarExpr_inv env se vs m hEvS hm⟩
            have hAgS := hloFullEnvAgree_preserved Γ env st st tenv tenvS k rs.nextTmp
              hAgree ⟨Nat.le_refl _, fun _ _ => rfl⟩ hFr hFrameS
            have hAgBind := hloFullEnvAgree_bind Γ env st tenvS dst rs.reg
              (.scalar declTy (knownNatOfScalarExpr se)) vs (mkScUi64 ws) hAgS hRelS hLookS
            rcases ih (Γ.bind dst ⟨rs.reg, .scalar declTy (knownNatOfScalarExpr se)⟩)
                (env.bind dst vs) st st' retVal tenvS rs.nextTmp rk hAgBind hFrS hLk hEval with
              ⟨hk_le, hk_all, hExtK, tvK, tenvK, hRelK, hExK, hLookK, hFrK, hFrameK⟩
            refine ⟨Nat.le_trans hs_le hk_le, ?_, hExtK, tvK, tenvK, hRelK, ?_, hLookK, hFrK,
              frame_hloTmp_range tenv tenvS tenvK k rs.nextTmp rk.nextTmp hs_le hk_le hFrameS hFrameK⟩
            · rw [List.all_append, Bool.and_eq_true]
              exact ⟨hs_all, hk_all⟩
            · rw [evalOps_append_nonReturn rs.ops rk.ops tenv tenvS hs_all hExS]
              exact hExK
        · simp [hsame] at hLow
    | sarrayLen arrVar =>
      cases declTy <;> try (simp [lowerCode] at hLow; done)
      dsimp [lowerCode] at hLow
      cases hΓ : Γ arrVar with
      | none => simp [hΓ] at hLow
      | some e =>
        rcases e with ⟨rArr, vk⟩
        cases vk with
        | scalar _ _ => simp [hΓ] at hLow
        | tensor1D n =>
          simp only [hΓ] at hLow
          by_cases hn_dec : decide (n < 2 ^ 64) = true
          · simp only [hn_dec, ↓reduceIte] at hLow
            cases hLk : lowerCode (Γ.bind dst ⟨hloTmpReg k, .scalar .i64 (some n)⟩)
                kCode (k + 1) with
            | none => simp [hLk] at hLow
            | some rk =>
              simp only [hLk, Option.bind, Option.some.injEq] at hLow
              subst hLow
              exact lowerHLOCode_sarrayLen_step Γ fuel env st st' dst arrVar kCode retVal
                tenv k n rArr rk hΓ (of_decide_eq_true hn_dec) hAgree hFr hEval
                (fun tenv1 hAg1 hFr1 hEv1 =>
                  ih _ _ st st' retVal tenv1 (k + 1) rk hAg1 hFr1 hLk hEv1)
          · simp [hn_dec] at hLow
    | sarrayGet arrVar idxVar elemTy =>
      cases declTy <;> try (simp [lowerCode] at hLow; done)
      cases elemTy <;> try (simp [lowerCode] at hLow; done)
      dsimp [lowerCode] at hLow
      cases hΓA : Γ arrVar with
      | none => simp [hΓA] at hLow
      | some eA =>
        rcases eA with ⟨rArr, vkA⟩
        cases vkA with
        | scalar _ _ => simp [hΓA] at hLow
        | tensor1D n =>
          cases hΓI : Γ idxVar with
          | none => simp [hΓA, hΓI] at hLow
          | some eI =>
            rcases eI with ⟨rIdx, vkI⟩
            cases vkI with
            | tensor1D _ => simp [hΓA, hΓI] at hLow
            | scalar tyI knI =>
              cases tyI <;> try (simp [hΓA, hΓI] at hLow; done)
              cases knI with
              | none => simp [hΓA, hΓI] at hLow
              | some idx =>
                simp only [hΓA, hΓI] at hLow
                by_cases hlt_dec : decide (idx < n) = true
                · simp only [hlt_dec, ↓reduceIte] at hLow
                  cases hLk : lowerCode (Γ.bind dst ⟨hloTmpReg (k + 1), .scalar .i64 none⟩)
                      kCode (k + 2) with
                  | none => simp [hLk] at hLow
                  | some rk =>
                    simp only [hLk, Option.bind, Option.some.injEq] at hLow
                    subst hLow
                    exact lowerHLOCode_sarrayGet_step Γ fuel env st st' dst arrVar idxVar kCode
                      retVal tenv k n idx rArr rIdx rk hΓA hΓI (of_decide_eq_true hlt_dec)
                      hAgree hFr hEval
                      (fun elem tenv2 hAg2 hFr2 hEv2 _ _ =>
                        ih _ _ st st' retVal tenv2 (k + 2) rk hAg2 hFr2 hLk hEv2)
                · simp [hlt_dec] at hLow
    | _ => simp [lowerCode] at hLow
  | parFor outVar lenVar inputs elemTy kernel kCode ih =>
    cases elemTy <;> try (simp [lowerCode] at hLow; done)
    dsimp [lowerCode] at hLow
    cases hLp : lowerParKernel Γ lenVar inputs kernel k with
    | none => simp [hLp] at hLow
    | some rp =>
      simp only [hLp, Option.bind] at hLow
      cases hLk : lowerCode (Γ.bind outVar ⟨rp.reg, rp.outKind⟩) kCode rp.nextTmp with
      | none => simp [hLk] at hLow
      | some rk =>
        simp only [hLk, Option.some.injEq] at hLow
        subst hLow
        unfold evalCode at hEval
        cases hPar : evalParFor fuel env st lenVar inputs kernel with
        | error err => simp [hPar] at hEval
        | ok pair =>
          rcases pair with ⟨outVal, st1⟩
          simp only [hPar] at hEval
          rcases lowerParKernel_post Γ fuel env st st1 lenVar inputs kernel outVal tenv k rp
              hAgree hFr hLp hPar with
            ⟨hp_le, hp_all, hExtP, tvP, tenvP, hRelP, hExP, hLookP, hFrP, hFrameP⟩
          have hAgP := hloFullEnvAgree_preserved Γ env st st1 tenv tenvP k rp.nextTmp
            hAgree hExtP hFr hFrameP
          have hAgBind := hloFullEnvAgree_bind Γ env st1 tenvP outVar rp.reg rp.outKind
            outVal tvP hAgP hRelP hLookP
          rcases ih (Γ.bind outVar ⟨rp.reg, rp.outKind⟩) (env.bind outVar outVal)
              st1 st' retVal tenvP rp.nextTmp rk hAgBind hFrP hLk hEval with
            ⟨hk_le, hk_all, hExtK, tvK, tenvK, hRelK, hExK, hLookK, hFrK, hFrameK⟩
          refine ⟨Nat.le_trans hp_le hk_le, ?_, heapExtends_trans hExtP hExtK,
            tvK, tenvK, hRelK, ?_, hLookK, hFrK,
            frame_hloTmp_range tenv tenvP tenvK k rp.nextTmp rk.nextTmp hp_le hk_le hFrameP hFrameK⟩
          · rw [List.all_append, Bool.and_eq_true]
            exact ⟨hp_all, hk_all⟩
          · rw [evalOps_append_nonReturn rp.ops rk.ops tenv tenvP hp_all hExP]
            exact hExK
  | ite condVar thenB elseB =>
    dsimp [lowerCode] at hLow
    cases hLs : lowerScalarCode Γ (.ite condVar thenB elseB) k with
    | none => simp [hLs] at hLow
    | some rs =>
      simp only [hLs, Option.bind, Option.some.injEq] at hLow
      subst hLow
      rcases lowerScalarCode_post Γ env (.ite condVar thenB elseB) tenv k rs
          (hloFullEnvAgree_to_scalar hAgree) hFr hLs with
        ⟨hs_le, hs_all, vs, ws, tenvS, hEvS, hEncS, hExS, hLookS, hFrS, hFrameS⟩
      have hEq : (.ok (vs, st) : Except UBError (Val × HeapState)) = .ok (retVal, st') :=
        (hEvS fuel st).symm.trans hEval
      injection hEq with hp
      injection hp with hv hst
      subst hv
      subst hst
      exact ⟨hs_le, hs_all, ⟨Nat.le_refl _, fun _ _ => rfl⟩,
        mkScUi64 ws, tenvS, ⟨⟨ws, hEncS, rfl⟩, fun _ hm => nomatch hm⟩,
        hExS, hLookS, hFrS, hFrameS⟩
  | _ => simp [lowerCode] at hLow

/-! ## 4. Parameter Binding Simulation (`initHLOParams` ↔ `bindArgs`) -/

theorem hloVarReg_injective {a b : VarId} (h : hloVarReg a = hloVarReg b) : a = b := by
  unfold hloVarReg at h
  have h1 := congrArg String.toList h
  simp only [String.toList_append] at h1
  have h2 : ("v".toList ++ (ppInt a).toList).drop 1 = ("v".toList ++ (ppInt b).toList).drop 1 :=
    congrArg (List.drop 1) h1
  have hv : "v".toList = ['v'] := rfl
  rw [hv] at h2
  simp only [List.cons_append, List.drop_succ_cons, List.drop_zero] at h2
  exact ppInt_injective a b (String.ext_iff.mpr h2)

def HLOVarRegCanonical (Γ : HLOTyEnv) : Prop :=
  ∀ x r vk, Γ x = some ⟨r, vk⟩ → r = hloVarReg x

/-- Bind a list of `LNIRParam`s to source `Val`s left-to-right. -/
def bindHLOParamEnv (env : VarEnv) : List LNIRParam → List Val → VarEnv
  | [], _ => env
  | _, [] => env
  | p :: ps, v :: vs => bindHLOParamEnv (env.bind p.id v) ps vs

/-- Pointwise argument relation between `LNIRParam`s, source `Val`s in `st`, and `TensorVal`s. -/
def HLOArgsRel (tensorLen : Nat) (st : HeapState) :
    List LNIRParam → List Val → List TensorVal → Prop
  | [], [], [] => True
  | p :: ps, v :: vs, tv :: tvs =>
    (∃ vk, paramVarKind tensorLen p.ty = some vk ∧ HLOValRel st vk v tv) ∧
    HLOArgsRel tensorLen st ps vs tvs
  | _, _, _ => False

theorem bindHLOParams_post (tensorLen : Nat) (Γ : HLOTyEnv) (env : VarEnv)
    (st : HeapState) (tenv : Env) (ps : List LNIRParam) (vs : List Val) (tvs : List TensorVal)
    (out : HLOTyEnv × List (String × TensorType))
    (hCanon : HLOVarRegCanonical Γ)
    (hAgree : HLOFullEnvAgree Γ env st tenv)
    (hFr : HLORegFresh tenv 0)
    (hInit : initHLOParamsAcc tensorLen Γ ps = some out)
    (hArgs : HLOArgsRel tensorLen st ps vs tvs) :
    tvs.length = out.2.length ∧
    ∃ tenv0,
      bindArgs tenv out.2 tvs = .ok tenv0 ∧
      HLOFullEnvAgree out.1 (bindHLOParamEnv env ps vs) st tenv0 ∧
      HLORegFresh tenv0 0 := by
  induction ps generalizing Γ env tenv vs tvs out with
  | nil =>
    cases vs with
    | cons _ _ => cases tvs <;> exact False.elim hArgs
    | nil =>
      cases tvs with
      | cons _ _ => exact False.elim hArgs
      | nil =>
        simp only [initHLOParamsAcc, Option.some.injEq] at hInit
        subst hInit
        exact ⟨rfl, tenv, rfl, hAgree, hFr⟩
  | cons p ps' ih =>
    cases vs with
    | nil => cases tvs <;> exact False.elim hArgs
    | cons v vs' =>
      cases tvs with
      | nil => exact False.elim hArgs
      | cons tv tvs' =>
        rcases hArgs with ⟨⟨vk, hvk, hRel⟩, hArgsRest⟩
        dsimp [initHLOParamsAcc] at hInit
        rw [hvk] at hInit
        simp only [Option.bind] at hInit
        cases hRest : initHLOParamsAcc tensorLen (Γ.bind p.id ⟨hloVarReg p.id, vk⟩) ps' with
        | none => simp [hRest] at hInit
        | some out1 =>
          simp only [hRest, Option.some.injEq] at hInit
          subst hInit
          rcases hloValRel_wellFormed hRel with ⟨hty, hwf⟩
          have hCanon1 : HLOVarRegCanonical (Γ.bind p.id ⟨hloVarReg p.id, vk⟩) := by
            intro x rx vkx hΓx
            unfold HLOTyEnv.bind at hΓx
            by_cases hxp : (x == p.id) = true
            · simp only [hxp, ↓reduceIte, Option.some.injEq] at hΓx
              have hx_eq : x = p.id := eq_of_beq hxp
              injection hΓx with hrx _
              exact hrx.symm.trans (congrArg hloVarReg hx_eq.symm)
            · have hxf : (x == p.id) = false := Bool.eq_false_iff.mpr hxp
              simp only [hxf, Bool.false_eq_true, ↓reduceIte] at hΓx
              exact hCanon x rx vkx hΓx
          have hAg1 : HLOFullEnvAgree (Γ.bind p.id ⟨hloVarReg p.id, vk⟩)
              (env.bind p.id v) st (tenv.bind (hloVarReg p.id) tv) := by
            intro x rx vkx hΓx
            unfold HLOTyEnv.bind at hΓx
            by_cases hxp : (x == p.id) = true
            · simp only [hxp, ↓reduceIte, Option.some.injEq] at hΓx
              have hx_eq : x = p.id := eq_of_beq hxp
              subst hx_eq
              injection hΓx with hrx hvkx
              subst hrx
              subst hvkx
              exact ⟨v, tv, VarEnv.bind_self env p.id v, hRel, env_bind_self _ _ _⟩
            · have hxf : (x == p.id) = false := Bool.eq_false_iff.mpr hxp
              simp only [hxf, Bool.false_eq_true, ↓reduceIte] at hΓx
              have hrx := hCanon x rx vkx hΓx
              subst hrx
              have hne : hloVarReg x ≠ hloVarReg p.id :=
                fun heq => hxp (beq_iff_eq.mpr (hloVarReg_injective heq))
              rcases hAgree x (hloVarReg x) vkx hΓx with ⟨vx, tvx, henvx, hrelx, htenvx⟩
              exact ⟨vx, tvx, (VarEnv.bind_ne env p.id x v hxf).trans henvx, hrelx,
                (env_bind_ne tenv (hloVarReg p.id) (hloVarReg x) tv hne).trans htenvx⟩
          have hFr1 : HLORegFresh (tenv.bind (hloVarReg p.id) tv) 0 := by
            intro j hj
            rw [env_bind_ne tenv (hloVarReg p.id) (hloTmpReg j) tv
              (hloVarReg_ne_hloTmpReg p.id j).symm]
            exact hFr j hj
          rcases ih (Γ.bind p.id ⟨hloVarReg p.id, vk⟩) (env.bind p.id v)
              (tenv.bind (hloVarReg p.id) tv) vs' tvs' out1 hCanon1 hAg1 hFr1 hRest hArgsRest with
            ⟨hlenRest, tenv0, hBindRest, hAg0, hFr0⟩
          refine ⟨by simp [hlenRest], tenv0, ?_, hAg0, hFr0⟩
          unfold bindArgs
          rw [hty, tensorType_bne_self]
          simp only [Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind, hwf]
          exact hBindRest

end LeanNative.Proofs
