import LeanNative.Proofs.StableHLOScalarCodeProofs

/-!
# Parallel Kernel Lowering Soundness (`LeanNative.Proofs.StableHLOKernelProofs`)

Proves `lowerParKernel_post`: compositional soundness of `lowerParKernel` across all five
tensor `ParallelKernelKind`s (`mapScaleAdd`, `zipAdd`, `zipMul`, `saxpy`, `dotProduct`).
-/

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend.TargetIR
open LeanNative.Backend.StableHLOAst
open LeanNative.Backend.StableHLOLower

/-- Post-condition of `lowerParKernel` paired with a successful `evalParFor` transition. -/
def HLOParKernelPost (st st' : HeapState) (outVal : Val) (tenv : Env) (k : Nat)
    (res : HLOCodeRes) : Prop :=
  k ≤ res.nextTmp ∧
  res.ops.all isNonReturnOp = true ∧
  HeapExtends st st' ∧
  ∃ tv tenv',
    HLOValRel st' res.outKind outVal tv ∧
    evalOps tenv res.ops = .ok tenv' ∧
    tenv' res.reg = some tv ∧
    HLORegFresh tenv' res.nextTmp ∧
    (∀ q, (∀ j, k ≤ j → j < res.nextTmp → q ≠ hloTmpReg j) → tenv' q = tenv q)

/-- Compositional soundness of `lowerParKernel` across all lowered parallel tensor kernels. -/
theorem lowerParKernel_post (Γ : HLOTyEnv) (fuel : Nat) (env : VarEnv) (st st' : HeapState)
    (lenVar : VarId) (inputs : List VarId) (kernel : ParallelKernelKind)
    (outVal : Val) (tenv : Env) (k : Nat) (res : HLOCodeRes)
    (hAgree : HLOFullEnvAgree Γ env st tenv) (hFr : HLORegFresh tenv k)
    (hLow : lowerParKernel Γ lenVar inputs kernel k = some res)
    (hEval : evalParFor fuel env st lenVar inputs kernel = .ok (outVal, st')) :
    HLOParKernelPost st st' outVal tenv k res := by
  dsimp [lowerParKernel] at hLow
  cases hΓL : Γ lenVar with
  | none => simp [hΓL] at hLow
  | some eL =>
    rcases eL with ⟨rLen, vkL⟩
    cases vkL with
    | tensor1D _ => simp [hΓL] at hLow
    | scalar tyL knL =>
      cases tyL <;> try (simp [hΓL] at hLow; done)
      cases knL with
      | none => simp [hΓL] at hLow
      | some n =>
        simp only [hΓL] at hLow
        rcases hAgree lenVar rLen (.scalar .i64 (some n)) hΓL with
          ⟨vLen, _, henvLen, ⟨_, hknLen⟩, _⟩
        rcases hknLen n rfl with ⟨uLen, rfl, huLen⟩
        cases kernel with
        | stencil1D3Pt _ _ _ => simp at hLow
        | customScalar _ _ _ => simp at hLow
        | mapScaleAdd scale bias =>
          cases inputs with
          | nil => simp at hLow
          | cons x rest =>
            cases rest with
            | cons _ _ => simp at hLow
            | nil =>
              cases hΓx : Γ x with
              | none => simp [hΓx] at hLow
              | some ex =>
                rcases ex with ⟨rx, vkx⟩
                cases vkx with
                | scalar _ _ => simp [hΓx] at hLow
                | tensor1D nx =>
                  simp only [hΓx] at hLow
                  by_cases hnx : (nx == n) = true
                  · simp only [hnx, ↓reduceIte, Option.some.injEq] at hLow
                    have hnx_eq : nx = n := eq_of_beq hnx
                    subst hLow
                    rw [hnx_eq] at hΓx
                    rcases hAgree x rx (.tensor1D n) hΓx with
                      ⟨vx, tvx, henvX, ⟨bx, bufx, rfl, hbxLe, hFindX, hSzX, rfl⟩, hLookX⟩
                    have hInv := evalParFor_mapScaleAdd_inv fuel env st st' lenVar x uLen scale bias bx
                      outVal (fun i => bufx.data.getD i 0 * scale + bias)
                      henvLen henvX
                      (fun i hi => by
                        simp [evalParKernelElem, readParInput, henvX,
                          readElem_of_findBuffer st bx bufx i hFindX (by omega)])
                      hEval
                    rcases hInv with ⟨rfl, rfl⟩
                    rw [huLen, range_map_unary_eq_toList_map (fun a => a * scale + bias) bufx.data n hSzX]
                    let outArr := (bufx.data.toList.map (fun a => a * scale + bias)).toArray
                    have hOutSz : outArr.size = n := by simp [outArr, hSzX]
                    rcases allocOutBuf_rel st outArr with ⟨hExt, hRelOut⟩
                    rw [hOutSz] at hRelOut
                    let cS := hloTmpReg k
                    let bS := hloTmpReg (k + 1)
                    let m := hloTmpReg (k + 2)
                    let cB := hloTmpReg (k + 3)
                    let bB := hloTmpReg (k + 4)
                    let d := hloTmpReg (k + 5)
                    have hrx0 : rx ≠ cS := operand_ne_hloTmp_of_fresh hLookX hFr (by omega)
                    have hrx1 : rx ≠ bS := operand_ne_hloTmp_of_fresh hLookX hFr (by omega)
                    let e1 := tenv.bind cS (mkScUi64 scale.toBitVec)
                    let vecS := (List.replicate n scale).toArray
                    let e2 := e1.bind bS (mkVecUi64 vecS)
                    let vecM := (bufx.data.toList.map (fun a => a * scale)).toArray
                    let e3 := e2.bind m (mkVecUi64 vecM)
                    let e4 := e3.bind cB (mkScUi64 bias.toBitVec)
                    let vecB := (List.replicate n bias).toArray
                    let e5 := e4.bind bB (mkVecUi64 vecB)
                    let e6 := e5.bind d (mkVecUi64 outArr)
                    dsimp only [HLOParKernelPost]
                    refine ⟨by omega, rfl, hExt, mkVecUi64 outArr, e6, hRelOut, ?_,
                      env_bind_self _ _ _, ?_, ?_⟩
                    · rw [evalOps_cons_nonReturn _ _ _ rfl, evalOp_constant_sc]
                      dsimp only [bind, Except.bind]
                      rw [evalOps_cons_nonReturn _ _ _ rfl,
                        evalOp_broadcast_scalar e1 bS cS n scale.toBitVec (env_bind_self _ _ _)]
                      simp only [UInt64.ofBitVec_toBitVec]
                      dsimp only [bind, Except.bind]
                      have hLookX2 : e2 rx = some (mkVecUi64 bufx.data) := by
                        dsimp only [e2, e1]
                        rw [env_bind_ne _ _ _ _ hrx1, env_bind_ne _ _ _ _ hrx0]
                        exact hLookX
                      rw [evalOps_cons_nonReturn _ _ _ rfl,
                        evalOp_mul_vec e2 m rx bS bufx.data vecS hLookX2 (env_bind_self _ _ _)
                          (by simp [vecS, hSzX])]
                      have hm_eq : ((bufx.data.toList.zip vecS.toList).map (fun p => p.1 * p.2)).toArray = vecM := by
                        dsimp only [vecS, vecM]
                        have hlenX : bufx.data.toList.length = n := by simp [hSzX]
                        rw [← hlenX, zip_replicate_right_map (· * ·) scale bufx.data.toList]
                      rw [hm_eq]
                      dsimp only [bind, Except.bind]
                      rw [evalOps_cons_nonReturn _ _ _ rfl, evalOp_constant_sc]
                      dsimp only [bind, Except.bind]
                      rw [evalOps_cons_nonReturn _ _ _ rfl,
                        evalOp_broadcast_scalar e4 bB cB n bias.toBitVec (env_bind_self _ _ _)]
                      simp only [UInt64.ofBitVec_toBitVec]
                      dsimp only [bind, Except.bind]
                      have hLookM5 : e5 m = some (mkVecUi64 vecM) := by
                        dsimp only [e5, e4]
                        rw [env_bind_ne _ _ _ _ (hloTmpReg_ne_of_ne (by omega)),
                            env_bind_ne _ _ _ _ (hloTmpReg_ne_of_ne (by omega))]
                        exact env_bind_self _ _ _
                      rw [evalOps_cons_nonReturn _ _ _ rfl,
                        evalOp_add_vec e5 d m bB vecM vecB hLookM5 (env_bind_self _ _ _)
                          (by simp [vecM, vecB, hSzX])]
                      have hd_eq : ((vecM.toList.zip vecB.toList).map (fun p => p.1 + p.2)).toArray = outArr := by
                        have hlenM : vecM.toList.length = n := by simp [vecM, hSzX]
                        dsimp only [vecB, outArr]
                        rw [← hlenM, zip_replicate_right_map (· + ·) bias vecM.toList]
                        simp [vecM]
                      rw [hd_eq]; rfl
                    · exact hloRegFresh_bind_lt _ (hloRegFresh_bind_lt _ (hloRegFresh_bind_lt _
                        (hloRegFresh_bind_lt _ (hloRegFresh_bind_lt _
                          (hloRegFresh_bind_lt _ hFr (by omega)) (by omega)) (by omega))
                          (by omega)) (by omega)) (by omega)
                    · intro q hq
                      dsimp only [e6, e5, e4, e3, e2, e1, d, bB, cB, m, bS, cS]
                      rw [env_bind_ne _ _ _ _ (hq (k + 5) (by omega) (by omega)),
                          env_bind_ne _ _ _ _ (hq (k + 4) (by omega) (by omega)),
                          env_bind_ne _ _ _ _ (hq (k + 3) (by omega) (by omega)),
                          env_bind_ne _ _ _ _ (hq (k + 2) (by omega) (by omega)),
                          env_bind_ne _ _ _ _ (hq (k + 1) (by omega) (by omega)),
                          env_bind_ne _ _ _ _ (hq k (by omega) (by omega))]
                  · simp [hnx] at hLow
        | zipAdd =>
          cases inputs with
          | nil => simp at hLow
          | cons x rest =>
            cases rest with
            | nil => simp at hLow
            | cons y rest2 =>
              cases rest2 with
              | cons _ _ => simp at hLow
              | nil =>
                cases hΓx : Γ x with
                | none => simp [hΓx] at hLow
                | some ex =>
                  rcases ex with ⟨rx, vkx⟩
                  cases vkx with
                  | scalar _ _ => simp [hΓx] at hLow
                  | tensor1D nx =>
                    cases hΓy : Γ y with
                    | none => simp [hΓx, hΓy] at hLow
                    | some ey =>
                      rcases ey with ⟨ry, vky⟩
                      cases vky with
                      | scalar _ _ => simp [hΓx, hΓy] at hLow
                      | tensor1D ny =>
                        simp only [hΓx, hΓy] at hLow
                        by_cases hnxy : (nx == n && ny == n) = true
                        · simp only [hnxy, ↓reduceIte, Option.some.injEq] at hLow
                          rw [Bool.and_eq_true] at hnxy
                          have hnx_eq := eq_of_beq hnxy.1
                          have hny_eq := eq_of_beq hnxy.2
                          subst hLow
                          rw [hnx_eq] at hΓx; rw [hny_eq] at hΓy
                          rcases hAgree x rx (.tensor1D n) hΓx with
                            ⟨_, _, henvX, ⟨bx, bufx, rfl, _, hFindX, hSzX, rfl⟩, hLookX⟩
                          rcases hAgree y ry (.tensor1D n) hΓy with
                            ⟨_, _, henvY, ⟨by_, bufy, rfl, _, hFindY, hSzY, rfl⟩, hLookY⟩
                          rcases evalParFor_inv_2 fuel env st st' lenVar x y uLen bx by_ .zipAdd outVal
                            (fun i => bufx.data.getD i 0 + bufy.data.getD i 0) henvLen henvX henvY
                            (fun i hi => by
                              simp [evalParKernelElem, readParInput, henvX, henvY,
                                readElem_of_findBuffer st bx bufx i hFindX (by omega),
                                readElem_of_findBuffer st by_ bufy i hFindY (by omega)])
                            hEval with ⟨rfl, rfl⟩
                          dsimp only [parKernelOutData]
                          rw [huLen, range_map_bin_eq_zip_map (· + ·) bufx.data bufy.data n hSzX hSzY]
                          let outArr := ((bufx.data.toList.zip bufy.data.toList).map (fun p => p.1 + p.2)).toArray
                          have hOutSz : outArr.size = n := by simp [outArr, hSzX, hSzY]
                          rcases allocOutBuf_rel st outArr with ⟨hExt, hRelOut⟩
                          rw [hOutSz] at hRelOut
                          dsimp only [HLOParKernelPost]
                          refine ⟨by omega, rfl, hExt, mkVecUi64 outArr,
                            tenv.bind (hloTmpReg k) (mkVecUi64 outArr), hRelOut, ?_,
                            env_bind_self _ _ _, hloRegFresh_bind_lt _ hFr (by omega),
                            fun q hq => env_bind_ne _ _ _ _ (hq k (by omega) (by omega))⟩
                          rw [evalOps_cons_nonReturn _ _ _ rfl,
                            evalOp_add_vec tenv (hloTmpReg k) rx ry bufx.data bufy.data hLookX hLookY
                              (hSzX.trans hSzY.symm)]
                          rfl
                        · simp [hnxy] at hLow
        | zipMul =>
          cases inputs with
          | nil => simp at hLow
          | cons x rest =>
            cases rest with
            | nil => simp at hLow
            | cons y rest2 =>
              cases rest2 with
              | cons _ _ => simp at hLow
              | nil =>
                cases hΓx : Γ x with
                | none => simp [hΓx] at hLow
                | some ex =>
                  rcases ex with ⟨rx, vkx⟩
                  cases vkx with
                  | scalar _ _ => simp [hΓx] at hLow
                  | tensor1D nx =>
                    cases hΓy : Γ y with
                    | none => simp [hΓx, hΓy] at hLow
                    | some ey =>
                      rcases ey with ⟨ry, vky⟩
                      cases vky with
                      | scalar _ _ => simp [hΓx, hΓy] at hLow
                      | tensor1D ny =>
                        simp only [hΓx, hΓy] at hLow
                        by_cases hnxy : (nx == n && ny == n) = true
                        · simp only [hnxy, ↓reduceIte, Option.some.injEq] at hLow
                          rw [Bool.and_eq_true] at hnxy
                          have hnx_eq := eq_of_beq hnxy.1
                          have hny_eq := eq_of_beq hnxy.2
                          subst hLow
                          rw [hnx_eq] at hΓx; rw [hny_eq] at hΓy
                          rcases hAgree x rx (.tensor1D n) hΓx with
                            ⟨_, _, henvX, ⟨bx, bufx, rfl, _, hFindX, hSzX, rfl⟩, hLookX⟩
                          rcases hAgree y ry (.tensor1D n) hΓy with
                            ⟨_, _, henvY, ⟨by_, bufy, rfl, _, hFindY, hSzY, rfl⟩, hLookY⟩
                          rcases evalParFor_inv_2 fuel env st st' lenVar x y uLen bx by_ .zipMul outVal
                            (fun i => bufx.data.getD i 0 * bufy.data.getD i 0) henvLen henvX henvY
                            (fun i hi => by
                              simp [evalParKernelElem, readParInput, henvX, henvY,
                                readElem_of_findBuffer st bx bufx i hFindX (by omega),
                                readElem_of_findBuffer st by_ bufy i hFindY (by omega)])
                            hEval with ⟨rfl, rfl⟩
                          dsimp only [parKernelOutData]
                          rw [huLen, range_map_bin_eq_zip_map (· * ·) bufx.data bufy.data n hSzX hSzY]
                          let outArr := ((bufx.data.toList.zip bufy.data.toList).map (fun p => p.1 * p.2)).toArray
                          have hOutSz : outArr.size = n := by simp [outArr, hSzX, hSzY]
                          rcases allocOutBuf_rel st outArr with ⟨hExt, hRelOut⟩
                          rw [hOutSz] at hRelOut
                          dsimp only [HLOParKernelPost]
                          refine ⟨by omega, rfl, hExt, mkVecUi64 outArr,
                            tenv.bind (hloTmpReg k) (mkVecUi64 outArr), hRelOut, ?_,
                            env_bind_self _ _ _, hloRegFresh_bind_lt _ hFr (by omega),
                            fun q hq => env_bind_ne _ _ _ _ (hq k (by omega) (by omega))⟩
                          rw [evalOps_cons_nonReturn _ _ _ rfl,
                            evalOp_mul_vec tenv (hloTmpReg k) rx ry bufx.data bufy.data hLookX hLookY
                              (hSzX.trans hSzY.symm)]
                          rfl
                        · simp [hnxy] at hLow
        | saxpy alpha =>
          cases inputs with
          | nil => simp at hLow
          | cons x rest =>
            cases rest with
            | nil => simp at hLow
            | cons y rest2 =>
              cases rest2 with
              | cons _ _ => simp at hLow
              | nil =>
                cases hΓx : Γ x with
                | none => simp [hΓx] at hLow
                | some ex =>
                  rcases ex with ⟨rx, vkx⟩
                  cases vkx with
                  | scalar _ _ => simp [hΓx] at hLow
                  | tensor1D nx =>
                    cases hΓy : Γ y with
                    | none => simp [hΓx, hΓy] at hLow
                    | some ey =>
                      rcases ey with ⟨ry, vky⟩
                      cases vky with
                      | scalar _ _ => simp [hΓx, hΓy] at hLow
                      | tensor1D ny =>
                        simp only [hΓx, hΓy] at hLow
                        by_cases hnxy : (nx == n && ny == n) = true
                        · simp only [hnxy, ↓reduceIte, Option.some.injEq] at hLow
                          rw [Bool.and_eq_true] at hnxy
                          have hnx_eq := eq_of_beq hnxy.1
                          have hny_eq := eq_of_beq hnxy.2
                          subst hLow
                          rw [hnx_eq] at hΓx; rw [hny_eq] at hΓy
                          rcases hAgree x rx (.tensor1D n) hΓx with
                            ⟨_, _, henvX, ⟨bx, bufx, rfl, _, hFindX, hSzX, rfl⟩, hLookX⟩
                          rcases hAgree y ry (.tensor1D n) hΓy with
                            ⟨_, _, henvY, ⟨by_, bufy, rfl, _, hFindY, hSzY, rfl⟩, hLookY⟩
                          rcases evalParFor_inv_2 fuel env st st' lenVar x y uLen bx by_ (.saxpy alpha) outVal
                            (fun i => alpha * bufx.data.getD i 0 + bufy.data.getD i 0) henvLen henvX henvY
                            (fun i hi => by
                              simp [evalParKernelElem, readParInput, henvX, henvY,
                                readElem_of_findBuffer st bx bufx i hFindX (by omega),
                                readElem_of_findBuffer st by_ bufy i hFindY (by omega)])
                            hEval with ⟨rfl, rfl⟩
                          dsimp only [parKernelOutData]
                          rw [huLen, range_map_bin_eq_zip_map (fun a b => alpha * a + b)
                            bufx.data bufy.data n hSzX hSzY]
                          let outArr := ((bufx.data.toList.zip bufy.data.toList).map
                            (fun p => alpha * p.1 + p.2)).toArray
                          have hOutSz : outArr.size = n := by simp [outArr, hSzX, hSzY]
                          rcases allocOutBuf_rel st outArr with ⟨hExt, hRelOut⟩
                          rw [hOutSz] at hRelOut
                          let cA := hloTmpReg k
                          let bA := hloTmpReg (k + 1)
                          let m := hloTmpReg (k + 2)
                          let d := hloTmpReg (k + 3)
                          let e1 := tenv.bind cA (mkScUi64 alpha.toBitVec)
                          let vecA := (List.replicate n alpha).toArray
                          let e2 := e1.bind bA (mkVecUi64 vecA)
                          let vecM := (bufx.data.toList.map (fun a => alpha * a)).toArray
                          let e3 := e2.bind m (mkVecUi64 vecM)
                          let e4 := e3.bind d (mkVecUi64 outArr)
                          dsimp only [HLOParKernelPost]
                          refine ⟨by omega, rfl, hExt, mkVecUi64 outArr, e4, hRelOut, ?_,
                            env_bind_self _ _ _,
                            hloRegFresh_bind_lt _ (hloRegFresh_bind_lt _
                              (hloRegFresh_bind_lt _ (hloRegFresh_bind_lt _ hFr (by omega))
                                (by omega)) (by omega)) (by omega),
                            fun q hq => by
                              dsimp only [e4, e3, e2, e1, d, m, bA, cA]
                              rw [env_bind_ne _ _ _ _ (hq (k + 3) (by omega) (by omega)),
                                  env_bind_ne _ _ _ _ (hq (k + 2) (by omega) (by omega)),
                                  env_bind_ne _ _ _ _ (hq (k + 1) (by omega) (by omega)),
                                  env_bind_ne _ _ _ _ (hq k (by omega) (by omega))]⟩
                          rw [evalOps_cons_nonReturn _ _ _ rfl, evalOp_constant_sc]
                          dsimp only [bind, Except.bind]
                          rw [evalOps_cons_nonReturn _ _ _ rfl,
                            evalOp_broadcast_scalar e1 bA cA n alpha.toBitVec (env_bind_self _ _ _)]
                          simp only [UInt64.ofBitVec_toBitVec]
                          dsimp only [bind, Except.bind]
                          have hLookX2 : e2 rx = some (mkVecUi64 bufx.data) := by
                            dsimp only [e2, e1]
                            rw [env_bind_ne _ _ _ _ (operand_ne_hloTmp_of_fresh hLookX hFr (by omega)),
                                env_bind_ne _ _ _ _ (operand_ne_hloTmp_of_fresh hLookX hFr (by omega))]
                            exact hLookX
                          rw [evalOps_cons_nonReturn _ _ _ rfl,
                            evalOp_mul_vec e2 m bA rx vecA bufx.data (env_bind_self _ _ _) hLookX2
                              (by simp [vecA, hSzX])]
                          have hm_eq : ((vecA.toList.zip bufx.data.toList).map (fun p => p.1 * p.2)).toArray = vecM := by
                            dsimp only [vecA, vecM]
                            have hlenX : bufx.data.toList.length = n := by simp [hSzX]
                            rw [← hlenX, zip_replicate_left_map (· * ·) alpha bufx.data.toList]
                          rw [hm_eq]
                          dsimp only [bind, Except.bind]
                          have hLookY3 : e3 ry = some (mkVecUi64 bufy.data) := by
                            dsimp only [e3, e2, e1]
                            rw [env_bind_ne _ _ _ _ (operand_ne_hloTmp_of_fresh hLookY hFr (by omega)),
                                env_bind_ne _ _ _ _ (operand_ne_hloTmp_of_fresh hLookY hFr (by omega)),
                                env_bind_ne _ _ _ _ (operand_ne_hloTmp_of_fresh hLookY hFr (by omega))]
                            exact hLookY
                          rw [evalOps_cons_nonReturn _ _ _ rfl,
                            evalOp_add_vec e3 d m ry vecM bufy.data (env_bind_self _ _ _) hLookY3
                              (by simp [vecM, hSzX, hSzY])]
                          have hd_eq : ((vecM.toList.zip bufy.data.toList).map (fun p => p.1 + p.2)).toArray = outArr := by
                            simp [vecM, outArr, zip_map_left (fun a => alpha * a) (· + ·)]
                          rw [hd_eq]; rfl
                        · simp [hnxy] at hLow
        | dotProduct =>
          cases inputs with
          | nil => simp at hLow
          | cons x rest =>
            cases rest with
            | nil => simp at hLow
            | cons y rest2 =>
              cases rest2 with
              | cons _ _ => simp at hLow
              | nil =>
                cases hΓx : Γ x with
                | none => simp [hΓx] at hLow
                | some ex =>
                  rcases ex with ⟨rx, vkx⟩
                  cases vkx with
                  | scalar _ _ => simp [hΓx] at hLow
                  | tensor1D nx =>
                    cases hΓy : Γ y with
                    | none => simp [hΓx, hΓy] at hLow
                    | some ey =>
                      rcases ey with ⟨ry, vky⟩
                      cases vky with
                      | scalar _ _ => simp [hΓx, hΓy] at hLow
                      | tensor1D ny =>
                        simp only [hΓx, hΓy] at hLow
                        by_cases hnxy : (nx == n && ny == n) = true
                        · simp only [hnxy, ↓reduceIte, Option.some.injEq] at hLow
                          rw [Bool.and_eq_true] at hnxy
                          have hnx_eq := eq_of_beq hnxy.1
                          have hny_eq := eq_of_beq hnxy.2
                          subst hLow
                          rw [hnx_eq] at hΓx; rw [hny_eq] at hΓy
                          rcases hAgree x rx (.tensor1D n) hΓx with
                            ⟨_, _, henvX, ⟨bx, bufx, rfl, _, hFindX, hSzX, rfl⟩, hLookX⟩
                          rcases hAgree y ry (.tensor1D n) hΓy with
                            ⟨_, _, henvY, ⟨by_, bufy, rfl, _, hFindY, hSzY, rfl⟩, hLookY⟩
                          rcases evalParFor_inv_2 fuel env st st' lenVar x y uLen bx by_ .dotProduct outVal
                            (fun i => bufx.data.getD i 0 * bufy.data.getD i 0) henvLen henvX henvY
                            (fun i hi => by
                              simp [evalParKernelElem, readParInput, henvX, henvY,
                                readElem_of_findBuffer st bx bufx i hFindX (by omega),
                                readElem_of_findBuffer st by_ bufy i hFindY (by omega)])
                            hEval with ⟨rfl, rfl⟩
                          dsimp only [parKernelOutData]
                          rw [huLen, range_map_bin_eq_zip_map (· * ·) bufx.data bufy.data n hSzX hSzY]
                          let sumVal : UInt64 :=
                            ((bufx.data.toList.zip bufy.data.toList).map (fun p => p.1 * p.2)).foldl (· + ·) 0
                          let outArr : Array UInt64 := #[sumVal]
                          rcases allocOutBuf_rel st outArr with ⟨hExt, hRelOut⟩
                          let dot0 := hloTmpReg k
                          let d := hloTmpReg (k + 1)
                          let e1 := tenv.bind dot0 (mkScUi64 sumVal.toBitVec)
                          let e2 := e1.bind d (mkVecUi64 outArr)
                          dsimp only [HLOParKernelPost]
                          refine ⟨by omega, rfl, hExt, mkVecUi64 outArr, e2, hRelOut, ?_,
                            env_bind_self _ _ _,
                            hloRegFresh_bind_lt _ (hloRegFresh_bind_lt _ hFr (by omega)) (by omega),
                            fun q hq => by
                              dsimp only [e2, e1, d, dot0]
                              rw [env_bind_ne _ _ _ _ (hq (k + 1) (by omega) (by omega)),
                                  env_bind_ne _ _ _ _ (hq k (by omega) (by omega))]⟩
                          rw [evalOps_cons_nonReturn _ _ _ rfl,
                            evalOp_dot_1d tenv dot0 rx ry bufx.data bufy.data hLookX hLookY
                              (hSzX.trans hSzY.symm)]
                          dsimp only [bind, Except.bind]
                          rw [evalOps_cons_nonReturn _ _ _ rfl,
                            evalOp_reshape_scalar_to_vec1 e1 d dot0 sumVal (env_bind_self _ _ _)]
                          rfl
                        · simp [hnxy] at hLow

end LeanNative.Proofs
