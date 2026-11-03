import LeanNative.Proofs.LLVMScalarLowerProofs

/-!
# CFG Lowering Helpers (`LeanNative.Proofs.LLVMCFGHelpersProofs`)

Well-formedness of `lowerCode` and continuation-parametric block execution
lemmas used by `lowerCode_post` / `lowerCode_sound`.
-/

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend.TargetIR
open LeanNative.Backend.LLVMAst
open LeanNative.Backend.LLVMLower

/-! ## 1. Block Freshness, List Lookup & Well-Formedness -/

theorem codeBlockFuel_pos (code : LNIRCode) : 0 < codeBlockFuel code := by
  induction code with
  | letBind _ _ _ _ ih => exact ih
  | ite _ _ _ _ _ => dsimp [codeBlockFuel]; omega
  | _ => exact Nat.zero_lt_succ 0

theorem find?_append_left {α : Type} (p : α → Bool) (xs ys : List α) (x : α)
    (hx : xs.find? p = some x) :
    (xs ++ ys).find? p = some x := by
  induction xs with
  | nil => simp [List.find?] at hx
  | cons a rest ih =>
    simp only [List.find?] at hx
    cases hp : p a
    · simp only [hp] at hx
      simp [List.cons_append, hp, ih hx]
    · simp only [hp, Option.some.injEq] at hx
      subst hx
      simp [List.cons_append, hp]

theorem find?_append_right {α : Type} (p : α → Bool) (xs ys : List α)
    (hnone : ∀ a ∈ xs, p a = false) :
    (xs ++ ys).find? p = ys.find? p := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    have ha : p a = false := hnone a (List.Mem.head rest)
    have hrest : ∀ b ∈ rest, p b = false := fun b hb => hnone b (List.Mem.tail a hb)
    simp [List.cons_append, ha, ih hrest]

theorem lowerScalarExpr_nextTmp_le (Γ : ScalarTyEnv) (se : ScalarExpr) (k : Nat)
    (res : ScalarLowerRes) (h : lowerScalarExpr Γ se k = some res) :
    k ≤ res.nextTmp := by
  induction se generalizing k res with
  | constU64 _ =>
    simp only [lowerScalarExpr, Option.some.injEq] at h
    subst h
    exact Nat.le_succ k
  | constBool _ =>
    simp only [lowerScalarExpr, Option.some.injEq] at h
    subst h
    exact Nat.le_succ k
  | var v =>
    dsimp [lowerScalarExpr] at h
    cases hΓ : Γ v with
    | none => simp [hΓ] at h
    | some ty =>
      simp only [hΓ] at h
      by_cases h64 : isI64Ty ty = true
      · simp only [h64, ↓reduceIte, Option.some.injEq] at h
        subst h
        exact Nat.le_refl k
      · simp only [h64, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h1 : isI1Ty ty = true
        · simp only [h1, ↓reduceIte, Option.some.injEq] at h
          subst h
          exact Nat.le_refl k
        · simp [h1] at h
  | binOp op l r ihl ihr =>
    dsimp [lowerScalarExpr] at h
    cases hl : lowerScalarExpr Γ l k with
    | none => simp [hl] at h
    | some rl =>
      simp only [hl, Option.bind] at h
      cases hr : lowerScalarExpr Γ r rl.nextTmp with
      | none => simp [hr] at h
      | some rr =>
        simp only [hr] at h
        have h1 := ihl k rl hl
        have h2 := ihr rl.nextTmp rr hr
        rcases lowerBinOpStep_inv op rl rr res h with ⟨_, _, h64⟩ | ⟨_, _, _, hres⟩
        · cases op <;> simp only [lowerBinOp64, Option.some.injEq] at h64
          case add => subst h64; dsimp only; omega
          case sub => subst h64; dsimp only; omega
          case mul => subst h64; dsimp only; omega
          case div => subst h64; dsimp only [emitDivRem]; omega
          case mod => subst h64; dsimp only [emitDivRem]; omega
          case bitAnd => subst h64; dsimp only; omega
          case bitOr => subst h64; dsimp only; omega
          case bitXor => subst h64; dsimp only; omega
          case shl => subst h64; dsimp only [emitShift]; omega
          case shr => subst h64; dsimp only [emitShift]; omega
          case sar => subst h64; dsimp only [emitShift]; omega
          case eq => subst h64; dsimp only [emitCmp]; omega
          case lt => subst h64; dsimp only [emitCmp]; omega
          case le => subst h64; dsimp only [emitCmp]; omega
          all_goals nomatch h64
        · subst hres
          dsimp only [emitCmp]
          omega
  | unaryOp op a iha =>
    cases op with
    | not =>
      dsimp [lowerScalarExpr] at h
      cases ha : lowerScalarExpr Γ a k with
      | none => simp [ha] at h
      | some ra =>
        simp only [ha, Option.bind] at h
        have h1 := iha k ra ha
        by_cases h64 : isI64Ty ra.ty = true
        · simp only [h64, ↓reduceIte, Option.some.injEq] at h
          subst h; dsimp only; omega
        · simp only [h64, Bool.false_eq_true, ↓reduceIte] at h
          by_cases h1t : isI1Ty ra.ty = true
          · simp only [h1t, ↓reduceIte, Option.some.injEq] at h
            subst h; dsimp only; omega
          · simp [h1t] at h
    | neg =>
      dsimp [lowerScalarExpr] at h
      cases ha : lowerScalarExpr Γ a k with
      | none => simp [ha] at h
      | some ra =>
        simp only [ha, Option.bind] at h
        have h1 := iha k ra ha
        by_cases h64 : isI64Ty ra.ty = true
        · simp only [h64, ↓reduceIte, Option.some.injEq] at h
          subst h; dsimp only; omega
        · simp [h64] at h
    | clz256 => simp [lowerScalarExpr] at h
  | select c t e ihc iht ihe =>
    dsimp [lowerScalarExpr] at h
    cases hc : lowerScalarExpr Γ c k with
    | none => simp [hc] at h
    | some rc =>
      simp only [hc, Option.bind] at h
      cases ht : lowerScalarExpr Γ t rc.nextTmp with
      | none => simp [ht] at h
      | some rt =>
        simp only [ht] at h
        cases he : lowerScalarExpr Γ e rt.nextTmp with
        | none => simp [he] at h
        | some re =>
          simp only [he] at h
          have h1 := ihc k rc hc
          have h2 := iht rc.nextTmp rt ht
          have h3 := ihe rt.nextTmp re he
          by_cases hcond : ((isI1Ty rc.ty || isI64Ty rc.ty) && sameScalarTy rt.ty re.ty) = true
          · simp only [hcond, ↓reduceIte, Option.some.injEq] at h
            subst h; dsimp only; omega
          · simp [hcond] at h
  | fma a b c iha ihb ihc =>
    dsimp [lowerScalarExpr] at h
    cases ha : lowerScalarExpr Γ a k with
    | none => simp [ha] at h
    | some ra =>
      simp only [ha, Option.bind] at h
      cases hb : lowerScalarExpr Γ b ra.nextTmp with
      | none => simp [hb] at h
      | some rb =>
        simp only [hb] at h
        cases hc : lowerScalarExpr Γ c rb.nextTmp with
        | none => simp [hc] at h
        | some rc =>
          simp only [hc] at h
          have h1 := iha k ra ha
          have h2 := ihb ra.nextTmp rb hb
          have h3 := ihc rb.nextTmp rc hc
          by_cases hall : (isI64Ty ra.ty && isI64Ty rb.ty && isI64Ty rc.ty) = true
          · simp only [hall, ↓reduceIte, Option.some.injEq] at h
            subst h; dsimp only; omega
          · simp [hall] at h

/-- Well-formedness and block-label freshness invariant of `lowerCode`. -/
def CodeLowerWF (lbl : BlockLabel) (kTmp kBlk : Nat) (rc : CodeLowerRes) : Prop :=
  kTmp ≤ rc.nextTmp ∧
  kBlk ≤ rc.nextBlk ∧
  rc.entryBlk.label = lbl ∧
  rc.entryBlk.phis = [] ∧
  (rc.exitLbl = lbl ∨ (∃ j, kBlk ≤ j ∧ j < rc.nextBlk ∧ rc.exitLbl = blkLabel j)) ∧
  (∀ b ∈ rc.restBlks, ∃ j, kBlk ≤ j ∧ j < rc.nextBlk ∧ b.label = blkLabel j) ∧
  (∀ b ∈ rc.restBlks, (rc.restBlks.find? fun x => x.label == b.label) = some b)

theorem lowerCode_wf (Γ : ScalarTyEnv) (lbl : BlockLabel) (exitCont : Option BlockLabel)
    (code : LNIRCode) (kTmp kBlk : Nat) (rc : CodeLowerRes)
    (hLbl : ∀ j, kBlk ≤ j → lbl ≠ blkLabel j)
    (hLow : lowerCode Γ lbl exitCont code kTmp kBlk = some rc) :
    CodeLowerWF lbl kTmp kBlk rc := by
  induction code generalizing Γ lbl exitCont kTmp kBlk rc with
  | ret v =>
    dsimp [lowerCode] at hLow
    cases hΓ : Γ v with
    | none => simp [hΓ] at hLow
    | some ty =>
      simp only [hΓ] at hLow
      by_cases h64 : isI64Ty ty = true
      · simp only [h64, ↓reduceIte, Option.some.injEq] at hLow
        subst hLow
        refine ⟨Nat.le_refl _, Nat.le_refl _, rfl, rfl, Or.inl rfl, ?_, ?_⟩
        · intro b hb
          cases hb
        · intro b hb
          cases hb
      · simp only [h64, Bool.false_eq_true, ↓reduceIte] at hLow
        by_cases h1 : isI1Ty ty = true
        · simp only [h1, ↓reduceIte, Option.some.injEq] at hLow
          subst hLow
          refine ⟨Nat.le_refl _, Nat.le_refl _, rfl, rfl, Or.inl rfl, ?_, ?_⟩
          · intro b hb
            cases hb
          · intro b hb
            cases hb
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
            have hseLe := lowerScalarExpr_nextTmp_le Γ se kTmp rse hse
            rcases ih (Γ.bind dst rse.ty) lbl exitCont rse.nextTmp kBlk rk hLbl hk with
              ⟨htLe, hbLe, heLbl, hePhi, hexLbl, hRest, hFind⟩
            exact ⟨Nat.le_trans hseLe htLe, hbLe, heLbl, hePhi, hexLbl, hRest, hFind⟩
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
              have hTLbl : ∀ j, kBlk + 3 ≤ j → blkLabel kBlk ≠ blkLabel j :=
                fun j hj h => by have := blkLabel_injective _ _ h; omega
              rcases iht Γ (blkLabel kBlk) (some (blkLabel (kBlk + 2))) (kTmp + 2) (kBlk + 3) rt hTLbl ht with
                ⟨htTmp, htBlk, htELbl, _, _, htRest, htFind⟩
              have hELbl : ∀ j, rt.nextBlk ≤ j → blkLabel (kBlk + 1) ≠ blkLabel j :=
                fun j hj h => by have := blkLabel_injective _ _ h; omega
              rcases ihe Γ (blkLabel (kBlk + 1)) (some (blkLabel (kBlk + 2))) rt.nextTmp rt.nextBlk re hELbl he with
                ⟨heTmp, heBlk, heELbl, _, _, heRest, heFind⟩
              have hMemT : ∀ b ∈ rt.entryBlk :: rt.restBlks,
                  b.label = blkLabel kBlk ∨ (∃ j, kBlk + 3 ≤ j ∧ j < rt.nextBlk ∧ b.label = blkLabel j) := by
                intro b hb
                rcases List.mem_cons.mp hb with rfl | hb'
                · exact Or.inl htELbl
                · exact Or.inr (htRest b hb')
              have hMemE : ∀ b ∈ re.entryBlk :: re.restBlks,
                  b.label = blkLabel (kBlk + 1) ∨ (∃ j, rt.nextBlk ≤ j ∧ j < re.nextBlk ∧ b.label = blkLabel j) := by
                intro b hb
                rcases List.mem_cons.mp hb with rfl | hb'
                · exact Or.inl heELbl
                · exact Or.inr (heRest b hb')
              refine ⟨by dsimp only; omega, by dsimp only; omega, rfl, rfl,
                Or.inr ⟨kBlk + 2, by omega, by dsimp only; omega, rfl⟩, ?_, ?_⟩
              · intro b hb
                dsimp only at hb ⊢
                rcases List.mem_cons.mp hb with rfl | hbRest
                · exact ⟨kBlk, by omega, by omega, htELbl⟩
                · rw [List.mem_append] at hbRest
                  rcases hbRest with hbTE | hbJoin
                  · rw [List.mem_append] at hbTE
                    rcases hbTE with hbT | hbE
                    · rcases htRest b hbT with ⟨j, hj1, hj2, hbj⟩
                      exact ⟨j, by omega, by omega, hbj⟩
                    · rcases hMemE b hbE with hbk | ⟨j, hj1, hj2, hbj⟩
                      · exact ⟨kBlk + 1, by omega, by omega, hbk⟩
                      · exact ⟨j, by omega, by omega, hbj⟩
                  · rcases List.mem_cons.mp hbJoin with rfl | hbNil
                    · exact ⟨kBlk + 2, by omega, by omega, rfl⟩
                    · cases hbNil
              · intro b hb
                dsimp only at hb ⊢
                have hFindT : ∀ x ∈ rt.entryBlk :: rt.restBlks,
                    ((rt.entryBlk :: rt.restBlks).find? fun y => y.label == x.label) = some x := by
                  intro x hx
                  rcases List.mem_cons.mp hx with rfl | hx'
                  · simp only [List.find?, BEq.rfl]
                  · rcases htRest x hx' with ⟨j, hj1, _, hxj⟩
                    have hne : (rt.entryBlk.label == x.label) = false := by
                      rw [htELbl, hxj]
                      exact Bool.eq_false_iff.mpr (fun heq => by
                        have := blkLabel_injective _ _ (eq_of_beq heq); omega)
                    simp only [List.find?, hne, htFind x hx']
                have hFindE : ∀ x ∈ re.entryBlk :: re.restBlks,
                    ((re.entryBlk :: re.restBlks).find? fun y => y.label == x.label) = some x := by
                  intro x hx
                  rcases List.mem_cons.mp hx with rfl | hx'
                  · simp only [List.find?, BEq.rfl]
                  · rcases heRest x hx' with ⟨j, hj1, _, hxj⟩
                    have hne : (re.entryBlk.label == x.label) = false := by
                      rw [heELbl, hxj]
                      exact Bool.eq_false_iff.mpr (fun heq => by
                        have := blkLabel_injective _ _ (eq_of_beq heq); omega)
                    simp only [List.find?, hne, heFind x hx']
                rcases List.mem_cons.mp hb with rfl | hbRest
                · simp only [List.find?, BEq.rfl]
                · rw [List.mem_append] at hbRest
                  rcases hbRest with hbTE | hbJoin
                  · rw [List.mem_append] at hbTE
                    rcases hbTE with hbT | hbE
                    · exact find?_append_left _ _ _ b (find?_append_left _ _ _ b (hFindT b (List.mem_cons_of_mem _ hbT)))
                    · have hNotT : ∀ a ∈ rt.entryBlk :: rt.restBlks, (a.label == b.label) = false := by
                        intro a ha
                        apply Bool.eq_false_iff.mpr
                        intro heq
                        have hlEq := eq_of_beq heq
                        rcases hMemT a ha with ha0 | ⟨ja, hja1, hja2, haJ⟩ <;>
                          rcases hMemE b hbE with hb0 | ⟨jb, hjb1, hjb2, hbJ⟩
                        · rw [ha0, hb0] at hlEq; have := blkLabel_injective _ _ hlEq; omega
                        · rw [ha0, hbJ] at hlEq; have := blkLabel_injective _ _ hlEq; omega
                        · rw [haJ, hb0] at hlEq; have := blkLabel_injective _ _ hlEq; omega
                        · rw [haJ, hbJ] at hlEq; have := blkLabel_injective _ _ hlEq; omega
                      let jBlk := mkJoinBlk (blkLabel (kBlk + 2)) exitCont (tmpReg (kTmp + 1))
                        rt.exitReg re.exitReg rt.exitLbl re.exitLbl
                      have hAssoc :
                          rt.entryBlk :: (rt.restBlks ++ re.entryBlk :: re.restBlks ++ [jBlk]) =
                          (rt.entryBlk :: rt.restBlks) ++
                            ((re.entryBlk :: re.restBlks) ++ [jBlk]) := by
                        simp [List.append_assoc]
                      rw [hAssoc, find?_append_right _ _ _ hNotT]
                      exact find?_append_left _ _ _ b (hFindE b hbE)
                  · rcases List.mem_cons.mp hbJoin with rfl | hbNil
                    · have hNotTE : ∀ a ∈ (rt.entryBlk :: rt.restBlks) ++ (re.entryBlk :: re.restBlks),
                          (a.label == blkLabel (kBlk + 2)) = false := by
                        intro a ha
                        apply Bool.eq_false_iff.mpr
                        intro heq
                        have hlEq := eq_of_beq heq
                        rcases List.mem_append.mp ha with haT | haE
                        · rcases hMemT a haT with ha0 | ⟨ja, hja1, _, haJ⟩
                          · rw [ha0] at hlEq
                            have := blkLabel_injective _ _ hlEq
                            omega
                          · rw [haJ] at hlEq
                            have := blkLabel_injective _ _ hlEq
                            omega
                        · rcases hMemE a haE with ha0 | ⟨ja, hja1, _, haJ⟩
                          · rw [ha0] at hlEq
                            have := blkLabel_injective _ _ hlEq
                            omega
                          · rw [haJ] at hlEq
                            have := blkLabel_injective _ _ hlEq
                            omega
                      let jBlk := mkJoinBlk (blkLabel (kBlk + 2)) exitCont (tmpReg (kTmp + 1))
                        rt.exitReg re.exitReg rt.exitLbl re.exitLbl
                      have hAssoc2 :
                          rt.entryBlk :: (rt.restBlks ++ re.entryBlk :: re.restBlks ++ [jBlk]) =
                          ((rt.entryBlk :: rt.restBlks) ++ (re.entryBlk :: re.restBlks)) ++
                            [jBlk] := by
                        simp [List.append_assoc]
                      rw [hAssoc2]
                      have hJlbl : jBlk.label = blkLabel (kBlk + 2) := rfl
                      rw [hJlbl, find?_append_right _ _ _ hNotTE]
                      simp only [List.find?, jBlk, mkJoinBlk, BEq.rfl]
                    · cases hbNil
            · simp [hs] at hLow
      · simp [hc] at hLow
  | _ => simp [lowerCode] at hLow

/-! ## 2. Continuation-Parametric CFG Execution Specification -/

/-- Execution of `rc` inside `fn`: consumes at most `codeBlockFuel code` block steps
along the dynamically taken path, either returning `w` (`exitCont = none`) or
entering the explicit continuation `jBlk` with predecessor `rc.exitLbl` and `rc.exitReg = w`. -/
def RegionExecSpec
    (runCall : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal →
      ExecOutcome ⊕ ExecState)
    (fn : LLVMFn) (exitCont : Option BlockLabel) (code : LNIRCode)
    (st : ExecState) (rc : CodeLowerRes) (w : BitVec 64) : Prop :=
  (exitCont = none →
    ∀ fuel, codeBlockFuel code ≤ fuel →
      execBlockWith runCall fn fuel st rc.entryBlk = .returned (some (.bits .i64 w)) st.mem) ∧
  (∀ jLbl jBlk,
    exitCont = some jLbl →
    findBlock fn jLbl = some jBlk →
    ∃ d stExit,
      1 ≤ d ∧
      d ≤ codeBlockFuel code ∧
      stExit.mem = st.mem ∧
      stExit.globals = st.globals ∧
      stExit.prevBlock = some rc.exitLbl ∧
      stExit.regs.lookup rc.exitReg = some (.bits .i64 w) ∧
      ∀ fuel, d ≤ fuel →
        execBlockWith runCall fn fuel st rc.entryBlk =
          execBlockWith runCall fn (fuel - d) stExit jBlk)

theorem ret_region_spec
    (runCall : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal →
      ExecOutcome ⊕ ExecState)
    (fn : LLVMFn) (exitCont : Option BlockLabel) (vId : VarId)
    (st : ExecState) (lbl : BlockLabel) (kTmp kBlk : Nat) (ty : LNIRType) (w : BitVec 64)
    (hlook : st.regs.lookup (varReg vId) = some (.bits .i64 w)) :
    RegionExecSpec runCall fn exitCont (.ret vId) st
      ⟨ty, varReg vId, lbl, kTmp, kBlk,
        { label := lbl, phis := [], body := [], term := exitTerminator exitCont (varReg vId) }, []⟩ w := by
  refine ⟨?_, ?_⟩
  · intro hnone fuel hfuel
    cases fuel with
    | zero => dsimp [codeBlockFuel] at hfuel; omega
    | succ fuel' =>
      simp [execBlockWith, execInstrsWith, evalPhis, commitPhis, exitTerminator, hnone,
        evalTypedOperand, evalOperand, lookupReg, w64, hlook]
  · intro jLbl jBlk hcont hfind
    refine ⟨1, { st with prevBlock := some lbl }, Nat.le_refl 1, Nat.le_refl 1,
      rfl, rfl, rfl, hlook, ?_⟩
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ fuel' =>
      simp [execBlockWith, execInstrsWith, evalPhis, commitPhis, exitTerminator, hcont, hfind]

theorem scalar_move_exec
    (runCall : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal →
      ExecOutcome ⊕ ExecState)
    (st : ExecState) (dst : VarId) (src : RegName) (w : BitVec 64)
    (hsrc : st.regs.lookup src = some (.bits .i64 w)) :
    stepInstrWith runCall st (.add (varReg dst) .none .i64 (.reg src) (c64 0)) =
      .inr (bindReg st (varReg dst) (.bits .i64 w)) := by
  simp [stepInstrWith, evalOperand, lookupReg, hsrc, c64, binResult, flagsOverflow, bindReg]
  exact congrArg (LLVMVal.bits .i64) (BitVec.add_zero w)

theorem prepend_entry_instrs_execBlockWith
    (runCall : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal →
      ExecOutcome ⊕ ExecState)
    (fn : LLVMFn) (fuel : Nat) (st st1 : ExecState) (pfx : List LLVMInstr)
    (lbl : BlockLabel) (body : List LLVMInstr) (term : Terminator)
    (hPfx : execInstrsWith runCall st pfx = .inr st1)
    (hMem : st1.mem = st.mem) :
    execBlockWith runCall fn fuel st { label := lbl, phis := [], body := pfx ++ body, term := term } =
      execBlockWith runCall fn fuel st1 { label := lbl, phis := [], body := body, term := term } := by
  cases fuel with
  | zero => rfl
  | succ f =>
    simp only [execBlockWith, evalPhis, List.map_nil, commitPhis, List.foldl_nil]
    rw [execInstrsWith_append runCall st st1 pfx body hPfx]
    cases hBody : execInstrsWith runCall st1 body with
    | inl out =>
      cases out with
      | returned rv => simp [hMem]
      | ub msg => simp
      | outOfFuel => simp
    | inr st' =>
      simp

theorem join_phi_left_exec
    (runCall : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal →
      ExecOutcome ⊕ ExecState)
    (fn : LLVMFn) (exitCont : Option BlockLabel) (fuel : Nat) (stExit : ExecState)
    (jLbl tExitLbl eExitLbl : BlockLabel) (res tExitReg eExitReg : RegName) (w : BitVec 64)
    (hPrev : stExit.prevBlock = some tExitLbl)
    (hReg : stExit.regs.lookup tExitReg = some (.bits .i64 w)) :
    (exitCont = none →
      execBlockWith runCall fn (fuel + 1) stExit
        (mkJoinBlk jLbl exitCont res tExitReg eExitReg tExitLbl eExitLbl) =
        .returned (some (.bits .i64 w)) stExit.mem) ∧
    (∀ outLbl outBlk, exitCont = some outLbl → findBlock fn outLbl = some outBlk →
      execBlockWith runCall fn (fuel + 1) stExit
        (mkJoinBlk jLbl exitCont res tExitReg eExitReg tExitLbl eExitLbl) =
        execBlockWith runCall fn fuel
          (let s := bindReg stExit res (.bits .i64 w); { s with prevBlock := some jLbl }) outBlk) := by
  have hPhiVal :
      resolvePhi stExit w64 stExit.prevBlock
        (mkJoinPhi res tExitReg eExitReg tExitLbl eExitLbl).incomings = .bits .i64 w := by
    simp [resolvePhi, hPrev, mkJoinPhi, evalTypedOperand, evalOperand, lookupReg, hReg]
  refine ⟨?_, ?_⟩
  · intro hnone
    simp [mkJoinBlk, mkJoinPhi, execBlockWith, evalPhis, commitPhis, bindReg, execInstrsWith,
      exitTerminator, hnone, evalTypedOperand, evalOperand, lookupReg] at hPhiVal ⊢
    simp [hPhiVal]
  · intro outLbl outBlk hout hfind
    simp [mkJoinBlk, mkJoinPhi, execBlockWith, evalPhis, commitPhis, execInstrsWith,
      exitTerminator, hout, hfind] at hPhiVal ⊢
    simp [hPhiVal]

theorem join_phi_right_exec
    (runCall : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal →
      ExecOutcome ⊕ ExecState)
    (fn : LLVMFn) (exitCont : Option BlockLabel) (fuel : Nat) (stExit : ExecState)
    (jLbl tExitLbl eExitLbl : BlockLabel) (res tExitReg eExitReg : RegName) (w : BitVec 64)
    (hNe : tExitLbl ≠ eExitLbl)
    (hPrev : stExit.prevBlock = some eExitLbl)
    (hReg : stExit.regs.lookup eExitReg = some (.bits .i64 w)) :
    (exitCont = none →
      execBlockWith runCall fn (fuel + 1) stExit
        (mkJoinBlk jLbl exitCont res tExitReg eExitReg tExitLbl eExitLbl) =
        .returned (some (.bits .i64 w)) stExit.mem) ∧
    (∀ outLbl outBlk, exitCont = some outLbl → findBlock fn outLbl = some outBlk →
      execBlockWith runCall fn (fuel + 1) stExit
        (mkJoinBlk jLbl exitCont res tExitReg eExitReg tExitLbl eExitLbl) =
        execBlockWith runCall fn fuel
          (let s := bindReg stExit res (.bits .i64 w); { s with prevBlock := some jLbl }) outBlk) := by
  have hBeqNe : (tExitLbl == eExitLbl) = false :=
    Bool.eq_false_iff.mpr (fun heq => hNe (eq_of_beq heq))
  have hPhiVal :
      resolvePhi stExit w64 stExit.prevBlock
        (mkJoinPhi res tExitReg eExitReg tExitLbl eExitLbl).incomings = .bits .i64 w := by
    simp [resolvePhi, hPrev, mkJoinPhi, hBeqNe, evalTypedOperand, evalOperand, lookupReg, hReg]
  refine ⟨?_, ?_⟩
  · intro hnone
    simp [mkJoinBlk, mkJoinPhi, execBlockWith, evalPhis, commitPhis, bindReg, execInstrsWith,
      exitTerminator, hnone, evalTypedOperand, evalOperand, lookupReg] at hPhiVal ⊢
    simp [hPhiVal]
  · intro outLbl outBlk hout hfind
    simp [mkJoinBlk, mkJoinPhi, execBlockWith, evalPhis, commitPhis, execInstrsWith,
      exitTerminator, hout, hfind] at hPhiVal ⊢
    simp [hPhiVal]

theorem evalIte_bool (env : VarEnv) (c : VarId) (t e : LNIRCode) (b : Bool)
    (henv : env c = some (.bool b)) :
    evalCode 2 env HeapState.empty (.ite c t e) =
      if b then evalCode 2 env HeapState.empty t
      else evalCode 2 env HeapState.empty e := by
  cases b <;> simp [evalCode, henv]

theorem evalIte_u64 (env : VarEnv) (c : VarId) (t e : LNIRCode) (n : UInt64)
    (henv : env c = some (.u64 n)) :
    evalCode 2 env HeapState.empty (.ite c t e) =
      if n != 0 then evalCode 2 env HeapState.empty t
      else evalCode 2 env HeapState.empty e := by
  simp [evalCode, henv]

theorem ite_cond_eval (env : VarEnv) (c : VarId) (cty : LNIRType) (vc : Val) (wc : BitVec 64)
    (t e : LNIRCode)
    (hcondTy : (isI1Ty cty || isI64Ty cty) = true)
    (henv : env c = some vc)
    (henc : encodeScalarTyped cty vc = some wc) :
    evalCode 2 env HeapState.empty (.ite c t e) =
      (if wc != 0#64 then evalCode 2 env HeapState.empty t
       else evalCode 2 env HeapState.empty e) := by
  simp only [Bool.or_eq_true] at hcondTy
  rcases hcondTy with h1 | h64
  · rw [isI1Ty_eq_true cty h1] at henc
    rcases typed_i1_inv vc wc henc with ⟨b, rfl, rfl⟩
    cases b
    · rw [evalIte_bool env c t e false henv]
      rfl
    · rw [evalIte_bool env c t e true henv]
      have hne : ((1#64 : BitVec 64) != 0#64) = true := by
        apply bne_iff_ne.mpr
        intro hc
        nomatch hc
      simp [hne]
  · rw [isI64Ty_eq_true cty h64] at henc
    rcases typed_i64_inv vc wc henc with ⟨n, rfl, rfl⟩
    rw [evalIte_u64 env c t e n henv]
    have hbn : (n.toBitVec != 0#64) = (n != 0) := by
      by_cases hnz : n = 0
      · subst hnz; simp
      · have hbv : n.toBitVec ≠ 0#64 := fun hb => hnz (UInt64.eq_of_toBitVec_eq hb)
        rw [bne_iff_ne.mpr hbv, bne_iff_ne.mpr hnz]
    rw [hbn]

theorem evalLetBind_scalar (env : VarEnv) (dst : VarId) (declTy : LNIRType)
    (se : ScalarExpr) (k : LNIRCode) (vs : Val)
    (hEvs : evalScalarExpr env se = .ok vs) :
    evalCode 2 env HeapState.empty (.letBind dst declTy (.scalar se) k) =
      evalCode 2 (env.bind dst vs) HeapState.empty k := by
  simp [evalCode, evalExpr, hEvs]

theorem ite_head_step
    (runCall : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal →
      ExecOutcome ⊕ ExecState)
    (fn : LLVMFn) (fuel : Nat) (st : ExecState) (lbl tLbl eLbl : BlockLabel)
    (c : VarId) (kTmp : Nat) (wc : BitVec 64) (tBlk eBlk : LLVMBlock)
    (hlook : st.regs.lookup (varReg c) = some (.bits .i64 wc))
    (hFindT : findBlock fn tLbl = some tBlk)
    (hFindE : findBlock fn eLbl = some eBlk) :
    execBlockWith runCall fn (fuel + 1) st (mkIteHeadBlk lbl tLbl eLbl c (tmpReg kTmp)) =
      if wc != 0#64 then
        execBlockWith runCall fn fuel
          (let s := bindReg st (tmpReg kTmp) (.bits .i1 1#1); { s with prevBlock := some lbl }) tBlk
      else
        execBlockWith runCall fn fuel
          (let s := bindReg st (tmpReg kTmp) (.bits .i1 0#1); { s with prevBlock := some lbl }) eBlk := by
  have h11 : (@BEq.beq (BitVec IntWidth.i1.bits) _ 1#1 1#1) = true := BEq.refl _
  by_cases hwc : wc = 0#64
  · subst hwc
    simp [mkIteHeadBlk, execBlockWith, evalPhis, commitPhis, execInstrsWith, stepInstrWith,
      evalOperand, lookupReg, hlook, icmpEval, w64, c64, IntWidth.bits, bindReg, hFindE]
  · have hne1 : (wc != 0#64) = true := bne_iff_ne.mpr hwc
    have hne2 : (@bne (BitVec IntWidth.i64.bits) _ wc 0#64) = true := hne1
    simp [mkIteHeadBlk, execBlockWith, evalPhis, commitPhis, execInstrsWith, stepInstrWith,
      evalOperand, lookupReg, hlook, icmpEval, w64, c64, bindReg, hne1, hne2, h11, hFindT]

end LeanNative.Proofs
