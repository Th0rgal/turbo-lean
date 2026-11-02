import LeanNative.Proofs.LLVMCFGHelpersProofs

/-!
# Compositional CFG Lowering Soundness (`LeanNative.Proofs.LLVMCFGLowerProofs`)

Proves compositional semantic preservation (`lowerCode_post` and `lowerCode_sound`)
from `LeanNative.Semantics.evalCode` to `LeanNative.Backend.LLVMAst.execBlockWith`
across `LNIRCode.ret`, `LNIRCode.letBind` of scalar expressions, and `LNIRCode.ite`
multi-block CFG diamonds with `PhiNode` join blocks.
-/

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend.TargetIR
open LeanNative.Backend.LLVMAst
open LeanNative.Backend.LLVMLower

/-! ## 3. Main Compositional Induction: `lowerCode_post` and `lowerCode_sound` -/

theorem lowerCode_post
    (runCall : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal →
      ExecOutcome ⊕ ExecState)
    (fn : LLVMFn) (Γ : ScalarTyEnv) (env : VarEnv) (exitCont : Option BlockLabel)
    (code : LNIRCode) (st : ExecState) (lbl : BlockLabel) (kTmp kBlk : Nat) (rc : CodeLowerRes)
    (hAgree : EnvTypedAgree Γ env st.regs)
    (hLbl : ∀ j, kBlk ≤ j → lbl ≠ blkLabel j)
    (hLow : lowerCode Γ lbl exitCont code kTmp kBlk = some rc)
    (hSubBlks : ∀ b ∈ rc.restBlks, findBlock fn b.label = some b) :
    ∃ v w,
      evalCode 2 env HeapState.empty code = .ok (v, HeapState.empty) ∧
      encodeScalarTyped rc.ty v = some w ∧
      RegionExecSpec runCall fn exitCont code st rc w := by
  induction code generalizing Γ env exitCont st lbl kTmp kBlk rc with
  | ret vId =>
    dsimp [lowerCode] at hLow
    cases hΓ : Γ vId with
    | none => simp [hΓ] at hLow
    | some ty =>
      simp only [hΓ] at hLow
      rcases hAgree vId ty hΓ with ⟨val, w, henv, henc, hlook⟩
      by_cases h64 : isI64Ty ty = true
      · simp only [h64, ↓reduceIte, Option.some.injEq] at hLow
        subst hLow
        rw [isI64Ty_eq_true ty h64] at henc
        refine ⟨val, w, ?_, henc, ret_region_spec runCall fn exitCont vId st lbl kTmp kBlk .i64 w hlook⟩
        unfold evalCode
        rw [henv]
      · simp only [h64, Bool.false_eq_true, ↓reduceIte] at hLow
        by_cases h1 : isI1Ty ty = true
        · simp only [h1, ↓reduceIte, Option.some.injEq] at hLow
          subst hLow
          rw [isI1Ty_eq_true ty h1] at henc
          refine ⟨val, w, ?_, henc, ret_region_spec runCall fn exitCont vId st lbl kTmp kBlk .i1 w hlook⟩
          unfold evalCode
          rw [henv]
        · simp [h1] at hLow
  | letBind dst declTy val k ih =>
    cases val with
    | scalar se =>
      dsimp [lowerCode] at hLow
      cases hse : lowerScalarExpr Γ se kTmp with
      | none => simp [hse] at hLow
      | some rse =>
        simp only [hse, Option.bind] at hLow
        by_cases hs : sameScalarTy rse.ty declTy = true
        · simp only [hs, ↓reduceIte] at hLow
          cases hk : lowerCode (Γ.bind dst rse.ty) lbl exitCont k rse.nextTmp kBlk with
          | none => simp [hk] at hLow
          | some rk =>
            simp only [hk, Option.some.injEq] at hLow
            subst hLow
            rcases lowerScalarExpr_post runCall Γ env se st kTmp rse hAgree hse with
              ⟨_, _, vs, ws, st0, hEvs, hEncs, hEx, hMem, hGlob, _, hLook, hFr⟩
            have hMov := scalar_move_exec runCall st0 dst rse.dst ws hLook
            let movI : LLVMInstr := .add (varReg dst) .none .i64 (.reg rse.dst) (c64 0)
            let st1 : ExecState := bindReg st0 (varReg dst) (.bits .i64 ws)
            have hPfx : execInstrsWith runCall st (rse.instrs ++ [movI]) = .inr st1 := by
              rw [execInstrsWith_append runCall st st0 rse.instrs [movI] hEx]
              simp [execInstrsWith, movI, hMov, st1]
            have hAg0 := envTypedAgree_preserved Γ env st.regs st0.regs kTmp rse.nextTmp hAgree hFr
            have hAg1 : EnvTypedAgree (Γ.bind dst rse.ty) (env.bind dst vs) st1.regs :=
              envTypedAgree_bind_var Γ env st0.regs dst rse.ty vs ws hAg0 hEncs
            have hWfK := lowerCode_wf (Γ.bind dst rse.ty) lbl exitCont k rse.nextTmp kBlk rk hLbl hk
            rcases ih (Γ.bind dst rse.ty) (env.bind dst vs) exitCont st1 lbl rse.nextTmp kBlk rk
              hAg1 hLbl hk hSubBlks with ⟨v, w, hEvK, hEncK, hRetK, hContK⟩
            refine ⟨v, w, ?_, hEncK, ?_, ?_⟩
            · rw [evalLetBind_scalar env dst declTy se k vs hEvs]
              exact hEvK
            · intro hnone fuel hfuel
              have hbase : codeBlockFuel k ≤ fuel := by simpa [codeBlockFuel] using hfuel
              have hPhi : rk.entryBlk.phis = [] := hWfK.2.2.2.1
              have hMem1 : st1.mem = st.mem := by simp [st1, bindReg, hMem]
              have hEq := prepend_entry_instrs_execBlockWith runCall fn fuel st st1
                (rse.instrs ++ [movI]) rk.entryBlk.label rk.entryBlk.body rk.entryBlk.term hPfx hMem1
              dsimp only [movI] at hEq
              have hLhsEq :
                  ({ rk.entryBlk with body := rse.instrs ++ [movI] ++ rk.entryBlk.body } : LLVMBlock) =
                  { label := rk.entryBlk.label, phis := [],
                    body := (rse.instrs ++ [movI]) ++ rk.entryBlk.body, term := rk.entryBlk.term } := by
                rcases hb0 : rk.entryBlk with ⟨lbl0, phis0, body0, term0⟩
                have hp0 : phis0 = [] := by rw [← hPhi, hb0]
                subst hp0
                rfl
              dsimp only [movI] at hLhsEq ⊢
              rw [hLhsEq, hEq]
              have hBlkEq : rk.entryBlk =
                  { label := rk.entryBlk.label, phis := [],
                    body := rk.entryBlk.body, term := rk.entryBlk.term } := by
                rcases hb0 : rk.entryBlk with ⟨lbl0, phis0, body0, term0⟩
                have hp0 : phis0 = [] := by rw [← hPhi, hb0]
                subst hp0
                rfl
              rw [← hBlkEq, hRetK hnone fuel hbase]
              simp [hMem1]
            · intro jLbl jBlk hcont hfind
              rcases hContK jLbl jBlk hcont hfind with ⟨d, stExit, hd1, hd2, hM, hG, hP, hL, hRun⟩
              refine ⟨d, stExit, hd1, by simpa [codeBlockFuel] using hd2, ?_, ?_, hP, hL, ?_⟩
              · rw [hM]; simp [st1, bindReg, hMem]
              · rw [hG]; simp [st1, bindReg, hGlob]
              · intro fuel hfuel
                have hPhi : rk.entryBlk.phis = [] := hWfK.2.2.2.1
                have hMem1 : st1.mem = st.mem := by simp [st1, bindReg, hMem]
                have hEq := prepend_entry_instrs_execBlockWith runCall fn fuel st st1
                  (rse.instrs ++ [movI]) rk.entryBlk.label rk.entryBlk.body rk.entryBlk.term hPfx hMem1
                dsimp only [movI] at hEq
                have hLhsEq :
                    ({ rk.entryBlk with body := rse.instrs ++ [movI] ++ rk.entryBlk.body } : LLVMBlock) =
                    { label := rk.entryBlk.label, phis := [],
                      body := (rse.instrs ++ [movI]) ++ rk.entryBlk.body, term := rk.entryBlk.term } := by
                  rcases hb0 : rk.entryBlk with ⟨lbl0, phis0, body0, term0⟩
                  have hp0 : phis0 = [] := by rw [← hPhi, hb0]
                  subst hp0
                  rfl
                dsimp only [movI] at hLhsEq ⊢
                rw [hLhsEq, hEq]
                have hBlkEq : rk.entryBlk =
                    { label := rk.entryBlk.label, phis := [],
                      body := rk.entryBlk.body, term := rk.entryBlk.term } := by
                  rcases hb0 : rk.entryBlk with ⟨lbl0, phis0, body0, term0⟩
                  have hp0 : phis0 = [] := by rw [← hPhi, hb0]
                  subst hp0
                  rfl
                rw [← hBlkEq]
                exact hRun fuel hfuel
        · simp [hs] at hLow
    | _ => simp [lowerCode] at hLow
  | ite c t e iht ihe =>
    dsimp [lowerCode] at hLow
    cases hΓ : Γ c with
    | none => simp [hΓ] at hLow
    | some cty =>
      simp only [hΓ] at hLow
      by_cases hc : (isI1Ty cty || isI64Ty cty) = true
      · simp only [hc, ↓reduceIte] at hLow
        cases ht : lowerCode Γ (blkLabel kBlk) (some (blkLabel (kBlk + 2))) t (kTmp + 2) (kBlk + 3) with
        | none => simp [ht] at hLow
        | some rt =>
          simp only [ht, Option.bind] at hLow
          cases he : lowerCode Γ (blkLabel (kBlk + 1)) (some (blkLabel (kBlk + 2))) e rt.nextTmp rt.nextBlk with
          | none => simp [he] at hLow
          | some re =>
            simp only [he] at hLow
            by_cases hs : sameScalarTy rt.ty re.ty = true
            · simp only [hs, ↓reduceIte, Option.some.injEq] at hLow
              subst hLow
              rcases hAgree c cty hΓ with ⟨vc, wc, henvC, hencC, hlookC⟩
              have hTLbl : ∀ j, kBlk + 3 ≤ j → blkLabel kBlk ≠ blkLabel j :=
                fun j hj h => by have := blkLabel_injective _ _ h; omega
              have hWfT := lowerCode_wf Γ (blkLabel kBlk) (some (blkLabel (kBlk + 2))) t
                (kTmp + 2) (kBlk + 3) rt hTLbl ht
              have hELbl : ∀ j, rt.nextBlk ≤ j → blkLabel (kBlk + 1) ≠ blkLabel j :=
                fun j hj h => by have := hWfT.2.1; have := blkLabel_injective _ _ h; omega
              have hWfE := lowerCode_wf Γ (blkLabel (kBlk + 1)) (some (blkLabel (kBlk + 2))) e
                rt.nextTmp rt.nextBlk re hELbl he
              have hSubT : ∀ b ∈ rt.restBlks, findBlock fn b.label = some b :=
                fun b hb => hSubBlks b (by
                  dsimp only
                  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ hb)))
              have hSubE : ∀ b ∈ re.restBlks, findBlock fn b.label = some b :=
                fun b hb => hSubBlks b (by
                  dsimp only
                  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ hb))))
              have hFindTEntry : findBlock fn (blkLabel kBlk) = some rt.entryBlk := by
                have hm := hSubBlks rt.entryBlk (by
                  dsimp only
                  exact List.Mem.head _)
                simpa [hWfT.2.2.1] using hm
              have hFindEEntry : findBlock fn (blkLabel (kBlk + 1)) = some re.entryBlk := by
                have hm := hSubBlks re.entryBlk (by
                  dsimp only
                  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ (List.Mem.head _))))
                simpa [hWfE.2.2.1] using hm
              let joinBlk : LLVMBlock :=
                mkJoinBlk (blkLabel (kBlk + 2)) exitCont (tmpReg (kTmp + 1))
                  rt.exitReg re.exitReg rt.exitLbl re.exitLbl
              have hFindJoin : findBlock fn (blkLabel (kBlk + 2)) = some joinBlk := by
                have hm := hSubBlks joinBlk (by
                  dsimp only [joinBlk]
                  exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.Mem.head _)))
                exact hm
              have hExitNe : rt.exitLbl ≠ re.exitLbl := by
                have htBlkLe := hWfT.2.1
                have heBlkLe := hWfE.2.1
                rcases hWfT.2.2.2.2.1 with htEx | ⟨jt, hjt1, hjt2, htEx⟩ <;>
                  rcases hWfE.2.2.2.2.1 with heEx | ⟨je, hje1, _, heEx⟩
                · rw [htEx, heEx]
                  intro h
                  have := blkLabel_injective _ _ h
                  omega
                · rw [htEx, heEx]
                  intro h
                  have := blkLabel_injective _ _ h
                  omega
                · rw [htEx, heEx]
                  intro h
                  have := blkLabel_injective _ _ h
                  omega
                · rw [htEx, heEx]
                  intro h
                  have := blkLabel_injective _ _ h
                  omega
              have hEvCond := ite_cond_eval env c cty vc wc t e hc henvC hencC
              have hTyEq : rt.ty = re.ty := (sameScalarTy_eq_true rt.ty re.ty hs).1
              by_cases hwc : (wc != 0#64) = true
              · let stT0 : ExecState :=
                  let s := bindReg st (tmpReg kTmp) (.bits .i1 1#1); { s with prevBlock := some lbl }
                have hAgT : EnvTypedAgree Γ env stT0.regs :=
                  envTypedAgree_bind_tmp Γ env st.regs kTmp (.bits .i1 1#1) hAgree
                rcases iht Γ env (some (blkLabel (kBlk + 2))) stT0 (blkLabel kBlk)
                  (kTmp + 2) (kBlk + 3) rt hAgT hTLbl ht hSubT with
                  ⟨vt, wt, hEvT, hEncT, _, hContT⟩
                rcases hContT (blkLabel (kBlk + 2)) joinBlk rfl hFindJoin with
                  ⟨dt, stExitT, hdt1, hdt2, hMT, hGT, hPT, hLT, hRunT⟩
                refine ⟨vt, wt, ?_, hEncT, ?_, ?_⟩
                · rw [hEvCond]
                  simp only [hwc, ↓reduceIte]
                  exact hEvT
                · intro hnone fuel hfuel
                  have hge : dt + 2 ≤ fuel := by
                    dsimp [codeBlockFuel] at hfuel; omega
                  have hf1 : fuel = (fuel - 1) + 1 := by omega
                  rw [hf1]
                  have hHead := ite_head_step runCall fn (fuel - 1) st lbl
                    (blkLabel kBlk) (blkLabel (kBlk + 1)) c kTmp wc
                    rt.entryBlk re.entryBlk hlookC hFindTEntry hFindEEntry
                  dsimp only at hHead ⊢
                  rw [hHead]
                  simp only [hwc, ↓reduceIte]
                  change execBlockWith runCall fn (fuel - 1) stT0 rt.entryBlk = _
                  rw [hRunT (fuel - 1) (by omega)]
                  have hf2 : fuel - 1 - dt = (fuel - dt - 2) + 1 := by omega
                  rw [hf2]
                  have hJ := (join_phi_left_exec runCall fn exitCont (fuel - dt - 2)
                    stExitT (blkLabel (kBlk + 2)) rt.exitLbl re.exitLbl
                    (tmpReg (kTmp + 1)) rt.exitReg re.exitReg wt hPT hLT).1 hnone
                  rw [hJ, hMT]
                  rfl
                · intro outLbl outBlk hout hFindOut
                  let stJoinOut : ExecState :=
                    let s := bindReg stExitT (tmpReg (kTmp + 1)) (.bits .i64 wt)
                    { s with prevBlock := some (blkLabel (kBlk + 2)) }
                  refine ⟨dt + 2, stJoinOut, by omega, by dsimp [codeBlockFuel]; omega,
                    by simp [stJoinOut, bindReg, hMT, stT0],
                    by simp [stJoinOut, bindReg, hGT, stT0],
                    rfl, lookup_cons_self _ _ _, ?_⟩
                  intro fuel hfuel
                  have hf1 : fuel = (fuel - 1) + 1 := by omega
                  rw [hf1]
                  have hHead := ite_head_step runCall fn (fuel - 1) st lbl
                    (blkLabel kBlk) (blkLabel (kBlk + 1)) c kTmp wc
                    rt.entryBlk re.entryBlk hlookC hFindTEntry hFindEEntry
                  dsimp only at hHead ⊢
                  rw [hHead]
                  simp only [hwc, ↓reduceIte]
                  change execBlockWith runCall fn (fuel - 1) stT0 rt.entryBlk = _
                  rw [hRunT (fuel - 1) (by omega)]
                  have hf2 : fuel - 1 - dt = (fuel - (dt + 2)) + 1 := by omega
                  rw [hf2]
                  have hJ := (join_phi_left_exec runCall fn exitCont (fuel - (dt + 2))
                    stExitT (blkLabel (kBlk + 2)) rt.exitLbl re.exitLbl
                    (tmpReg (kTmp + 1)) rt.exitReg re.exitReg wt hPT hLT).2 outLbl outBlk hout hFindOut
                  have hf3 : fuel - 1 + 1 - (dt + 2) = fuel - (dt + 2) := by omega
                  rw [hf3]
                  exact hJ
              · have hwcF : (wc != 0#64) = false := Bool.eq_false_iff.mpr hwc
                let stE0 : ExecState :=
                  let s := bindReg st (tmpReg kTmp) (.bits .i1 0#1); { s with prevBlock := some lbl }
                have hAgE : EnvTypedAgree Γ env stE0.regs :=
                  envTypedAgree_bind_tmp Γ env st.regs kTmp (.bits .i1 0#1) hAgree
                rcases ihe Γ env (some (blkLabel (kBlk + 2))) stE0 (blkLabel (kBlk + 1))
                  rt.nextTmp rt.nextBlk re hAgE hELbl he hSubE with
                  ⟨ve, we, hEvE, hEncE, _, hContE⟩
                rcases hContE (blkLabel (kBlk + 2)) joinBlk rfl hFindJoin with
                  ⟨de, stExitE, hde1, hde2, hME, hGE, hPE, hLE, hRunE⟩
                refine ⟨ve, we, ?_, ?_, ?_, ?_⟩
                · rw [hEvCond, hwcF]
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  exact hEvE
                · dsimp only
                  rw [hTyEq]
                  exact hEncE
                · intro hnone fuel hfuel
                  have hge : de + 2 ≤ fuel := by
                    dsimp [codeBlockFuel] at hfuel; omega
                  have hf1 : fuel = (fuel - 1) + 1 := by omega
                  rw [hf1]
                  have hHead := ite_head_step runCall fn (fuel - 1) st lbl
                    (blkLabel kBlk) (blkLabel (kBlk + 1)) c kTmp wc
                    rt.entryBlk re.entryBlk hlookC hFindTEntry hFindEEntry
                  dsimp only at hHead ⊢
                  rw [hHead, hwcF]
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  change execBlockWith runCall fn (fuel - 1) stE0 re.entryBlk = _
                  rw [hRunE (fuel - 1) (by omega)]
                  have hf2 : fuel - 1 - de = (fuel - de - 2) + 1 := by omega
                  rw [hf2]
                  have hJ := (join_phi_right_exec runCall fn exitCont (fuel - de - 2)
                    stExitE (blkLabel (kBlk + 2)) rt.exitLbl re.exitLbl
                    (tmpReg (kTmp + 1)) rt.exitReg re.exitReg we hExitNe hPE hLE).1 hnone
                  rw [hJ, hME]
                  rfl
                · intro outLbl outBlk hout hFindOut
                  let stJoinOut : ExecState :=
                    let s := bindReg stExitE (tmpReg (kTmp + 1)) (.bits .i64 we)
                    { s with prevBlock := some (blkLabel (kBlk + 2)) }
                  refine ⟨de + 2, stJoinOut, by omega, by dsimp [codeBlockFuel]; omega,
                    by simp [stJoinOut, bindReg, hME, stE0],
                    by simp [stJoinOut, bindReg, hGE, stE0],
                    rfl, lookup_cons_self _ _ _, ?_⟩
                  intro fuel hfuel
                  have hf1 : fuel = (fuel - 1) + 1 := by omega
                  rw [hf1]
                  have hHead := ite_head_step runCall fn (fuel - 1) st lbl
                    (blkLabel kBlk) (blkLabel (kBlk + 1)) c kTmp wc
                    rt.entryBlk re.entryBlk hlookC hFindTEntry hFindEEntry
                  dsimp only at hHead ⊢
                  rw [hHead, hwcF]
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  change execBlockWith runCall fn (fuel - 1) stE0 re.entryBlk = _
                  rw [hRunE (fuel - 1) (by omega)]
                  have hf2 : fuel - 1 - de = (fuel - (de + 2)) + 1 := by omega
                  rw [hf2]
                  have hJ := (join_phi_right_exec runCall fn exitCont (fuel - (de + 2))
                    stExitE (blkLabel (kBlk + 2)) rt.exitLbl re.exitLbl
                    (tmpReg (kTmp + 1)) rt.exitReg re.exitReg we hExitNe hPE hLE).2 outLbl outBlk hout hFindOut
                  have hf3 : fuel - 1 + 1 - (de + 2) = fuel - (de + 2) := by omega
                  rw [hf3]
                  exact hJ
            · simp [hs] at hLow
      · simp [hc] at hLow
  | _ => simp [lowerCode] at hLow

/-- Top-level compositional soundness theorem for `lowerCode` (`exitCont = none`). -/
theorem lowerCode_sound
    (Γ : ScalarTyEnv) (env : VarEnv) (code : LNIRCode) (st : ExecState)
    (kTmp kBlk : Nat) (rc : CodeLowerRes) (mod_ : LLVMModule) (fn : LLVMFn)
    (fuel : Nat) (val : Val)
    (hAgree : EnvTypedAgree Γ env st.regs)
    (hLow : lowerCode Γ entryLabel none code kTmp kBlk = some rc)
    (hFnBlks : fn.blocks = rc.entryBlk :: rc.restBlks)
    (hFuel : codeBlockFuel code ≤ fuel)
    (hEval : evalCode 2 env HeapState.empty code = .ok (val, HeapState.empty)) :
    ∃ w, encodeScalarVal val = some w ∧
      execBlock mod_ fn fuel st rc.entryBlk = .returned (some (.bits .i64 w)) := by
  have hLbl : ∀ j, kBlk ≤ j → entryLabel ≠ blkLabel j := fun j _ => entryLabel_ne_blkLabel j
  have hWf := lowerCode_wf Γ entryLabel none code kTmp kBlk rc hLbl hLow
  have hSubBlks : ∀ b ∈ rc.restBlks, findBlock fn b.label = some b := by
    intro b hb
    rcases hWf.2.2.2.2.2.1 b hb with ⟨j, _, _, hbj⟩
    have hne : (rc.entryBlk.label == b.label) = false := by
      rw [hWf.2.2.1, hbj]
      exact Bool.eq_false_iff.mpr (fun heq => entryLabel_ne_blkLabel j (eq_of_beq heq))
    simp [findBlock, hFnBlks, hne, hWf.2.2.2.2.2.2 b hb]
  rcases lowerCode_post (runCallWith mod_ fuel) fn Γ env none code st entryLabel kTmp kBlk rc
    hAgree hLbl hLow hSubBlks with ⟨v, w, hEv, hEnc, hRet, _⟩
  rw [hEval] at hEv
  injection hEv with hp
  injection hp with hv _
  subst hv
  refine ⟨w, encodeScalarVal_of_typed rc.ty val w hEnc, ?_⟩
  unfold execBlock
  rw [hRet rfl fuel hFuel]
  rfl

end LeanNative.Proofs
