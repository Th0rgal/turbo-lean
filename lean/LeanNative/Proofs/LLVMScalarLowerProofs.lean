import LeanNative.Proofs.LLVMScalarHelpersProofs

/-!
# Compositional `ScalarExpr` → LLVM AST Soundness (`LeanNative.Proofs.LLVMScalarLowerProofs`)

Proves compositional semantic preservation (`lowerScalarExpr_post` and
`lowerScalarExpr_sound`) from `LeanNative.Semantics.evalScalarExpr` to
`LeanNative.Backend.LLVMAst.execInstrsWith` / `execInstrs`.
-/

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend.TargetIR
open LeanNative.Backend.LLVMAst
open LeanNative.Backend.LLVMLower

/-- Post-condition for `lowerBinOpStep op rl rr = some res` given operand post-conditions. -/
theorem lowerBinOpStep_post
    (runCall : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal →
      ExecOutcome ⊕ ExecState)
    (env : VarEnv) (op : BinOp) (l r : ScalarExpr) (st : ExecState) (k : Nat)
    (rl rr res : ScalarLowerRes)
    (hL : ScalarExecPost runCall env l st k rl)
    (hR : ∀ stL, execInstrsWith runCall st rl.instrs = .inr stL →
      (∀ q, (∀ j, k ≤ j → j < rl.nextTmp → q ≠ tmpReg j) → stL.regs.lookup q = st.regs.lookup q) →
      ScalarExecPost runCall env r stL rl.nextTmp rr)
    (hLow : lowerBinOpStep op rl rr = some res) :
    ScalarExecPost runCall env (.binOp op l r) st k res := by
  rcases hL with ⟨hl_le, hl_fr, vl, wl, stL, hEvL, hEncL, hExL, hMemL, hGlobL, hPrevL, hLookL, hFrL⟩
  rcases hR stL hExL hFrL with
    ⟨hr_le, hr_fr, vr, wr, stR, hEvR, hEncR, hExR, hMemR, hGlobR, hPrevR, hLookR, hFrR⟩
  have hLookLR : stR.regs.lookup rl.dst = some (.bits .i64 wl) := by
    rw [hFrR rl.dst (fun j hlo _ => hl_fr j hlo)]
    exact hLookL
  have hExLR : execInstrsWith runCall st (rl.instrs ++ rr.instrs) = .inr stR := by
    rw [execInstrsWith_append runCall st stL rl.instrs rr.instrs hExL]
    exact hExR
  have hStLR : stR.mem = st.mem ∧ stR.globals = st.globals ∧ stR.prevBlock = st.prevBlock :=
    ⟨hMemR.trans hMemL, hGlobR.trans hGlobL, hPrevR.trans hPrevL⟩
  have hFrLR := frame_tmp_Range st.regs stL.regs stR.regs k rl.nextTmp rr.nextTmp hl_le hr_le hFrL hFrR
  have hkLR : k ≤ rr.nextTmp := Nat.le_trans hl_le hr_le
  rcases lowerBinOpStep_inv op rl rr res hLow with ⟨htl, htr, h64⟩ | ⟨htl, htr, hop, hres⟩
  · clear hLow
    rw [htl] at hEncL
    rw [htr] at hEncR
    rcases typed_i64_inv vl wl hEncL with ⟨a, rfl, rfl⟩
    rcases typed_i64_inv vr wr hEncR with ⟨b, rfl, rfl⟩
    rcases lowerBinOp64_exec runCall stR op rl rr res a b hLookLR hLookR
      (fun j hj => hl_fr j (Nat.le_trans hr_le hj)) hr_fr h64 with
      ⟨dIdx, ops, v, w, st', hdLo, hdHi, hDst, hIns, hEvOp, hEncV, hExOp, hMO, hGO, hPO, hLkO, hFrO⟩
    clear h64
    rcases res with ⟨rty, rdst, rnext, rins⟩
    dsimp only at hDst hIns hdHi hEncV
    subst hDst
    subst hIns
    have hEv : evalScalarExpr env (.binOp op l r) = .ok v := by
      unfold evalScalarExpr
      rw [hEvL, hEvR]
      exact hEvOp
    exact finishScalarTail runCall env (.binOp op l r) st stR k rr.nextTmp dIdx rnext rty
      (rl.instrs ++ rr.instrs) ops v w hkLR (Nat.le_trans hdLo (Nat.le_of_lt hdHi)) hdHi
      hEv hEncV hExLR hStLR hFrLR ⟨st', hExOp, hMO, hGO, hPO, hLkO, hFrO⟩
  · clear hLow
    subst hop
    subst hres
    rw [htl] at hEncL
    rw [htr] at hEncR
    rcases typed_i1_inv vl wl hEncL with ⟨b1, rfl, rfl⟩
    rcases typed_i1_inv vr wr hEncR with ⟨b2, rfl, rfl⟩
    have hcmp : icmpEval .eq .i64 (if b1 then 1#64 else 0#64) (if b2 then 1#64 else 0#64) =
        (b1 == b2) := bool_word_eq_iff b1 b2
    have hEv : evalScalarExpr env (.binOp .eq l r) = .ok (.bool (b1 == b2)) := by
      unfold evalScalarExpr
      rw [hEvL, hEvR]
      rfl
    refine finishScalarTail runCall env (.binOp .eq l r) st stR k rr.nextTmp
      (rr.nextTmp + 1) (rr.nextTmp + 2) .i1 (rl.instrs ++ rr.instrs)
      (emitCmp rr.nextTmp .eq (.reg rl.dst) (.reg rr.dst)).2.2
      (.bool (b1 == b2)) (if b1 == b2 then 1#64 else 0#64) hkLR
      (Nat.le_add_right rr.nextTmp 2) (Nat.lt_succ_self (rr.nextTmp + 1))
      hEv rfl hExLR hStLR hFrLR ?_
    rw [← hcmp]
    exact emitCmp_exec runCall stR rr.nextTmp .eq rl.dst rr.dst _ _ hLookLR hLookR

/-- Post-condition for `.select c t e` given subexpression post-conditions. -/
theorem lowerSelectStep_post
    (runCall : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal →
      ExecOutcome ⊕ ExecState)
    (env : VarEnv) (c t e : ScalarExpr) (st : ExecState) (k : Nat) (rc rt re : ScalarLowerRes)
    (hcond : ((isI1Ty rc.ty || isI64Ty rc.ty) && sameScalarTy rt.ty re.ty) = true)
    (hC : ScalarExecPost runCall env c st k rc)
    (hT : ∀ stC, execInstrsWith runCall st rc.instrs = .inr stC →
      (∀ q, (∀ j, k ≤ j → j < rc.nextTmp → q ≠ tmpReg j) → stC.regs.lookup q = st.regs.lookup q) →
      ScalarExecPost runCall env t stC rc.nextTmp rt)
    (hE : ∀ stC stT, execInstrsWith runCall st rc.instrs = .inr stC →
      (∀ q, (∀ j, k ≤ j → j < rc.nextTmp → q ≠ tmpReg j) → stC.regs.lookup q = st.regs.lookup q) →
      execInstrsWith runCall stC rt.instrs = .inr stT →
      (∀ q, (∀ j, rc.nextTmp ≤ j → j < rt.nextTmp → q ≠ tmpReg j) → stT.regs.lookup q = stC.regs.lookup q) →
      ScalarExecPost runCall env e stT rt.nextTmp re) :
    ScalarExecPost runCall env (.select c t e) st k
      ⟨rt.ty, tmpReg (re.nextTmp + 1), re.nextTmp + 2,
        rc.instrs ++ rt.instrs ++ re.instrs ++
          [ .icmp (tmpReg re.nextTmp) .ne w64 (.reg rc.dst) (c64 0)
          , .select (tmpReg (re.nextTmp + 1)) (.reg (tmpReg re.nextTmp)) w64 (.reg rt.dst) (.reg re.dst) ]⟩ := by
  rcases hC with ⟨hc_le, hc_fr, vc, wc, stC, hEvC, hEncC, hExC, hMemC, hGlobC, hPrevC, hLookC, hFrC⟩
  rcases hT stC hExC hFrC with
    ⟨ht_le, ht_fr, vt, wt, stT, hEvT, hEncT, hExT, hMemT, hGlobT, hPrevT, hLookT, hFrT⟩
  rcases hE stC stT hExC hFrC hExT hFrT with
    ⟨he_le, he_fr, ve, we, stE, hEvE, hEncE, hExE, hMemE, hGlobE, hPrevE, hLookE, hFrE⟩
  have hct_le := Nat.le_trans hc_le ht_le
  have hcte_le := Nat.le_trans hct_le he_le
  have hFrCT := frame_tmp_Range st.regs stC.regs stT.regs k rc.nextTmp rt.nextTmp hc_le ht_le hFrC hFrT
  have hFrCTE := frame_tmp_Range st.regs stT.regs stE.regs k rt.nextTmp re.nextTmp hct_le he_le hFrCT hFrE
  have hExCT : execInstrsWith runCall st (rc.instrs ++ rt.instrs) = .inr stT := by
    rw [execInstrsWith_append runCall st stC rc.instrs rt.instrs hExC]
    exact hExT
  have hExCTE : execInstrsWith runCall st (rc.instrs ++ rt.instrs ++ re.instrs) = .inr stE := by
    rw [execInstrsWith_append runCall st stT (rc.instrs ++ rt.instrs) re.instrs hExCT]
    exact hExE
  have hLookCE : stE.regs.lookup rc.dst = some (.bits .i64 wc) := by
    rw [hFrE rc.dst (fun j hj _ => hc_fr j (Nat.le_trans ht_le hj)),
        hFrT rc.dst (fun j hj _ => hc_fr j hj)]
    exact hLookC
  have hLookTE : stE.regs.lookup rt.dst = some (.bits .i64 wt) := by
    rw [hFrE rt.dst (fun j hj _ => ht_fr j hj)]
    exact hLookT
  have hStE : stE.mem = st.mem ∧ stE.globals = st.globals ∧ stE.prevBlock = st.prevBlock :=
    ⟨hMemE.trans (hMemT.trans hMemC), hGlobE.trans (hGlobT.trans hGlobC),
     hPrevE.trans (hPrevT.trans hPrevC)⟩
  have hOps := emitSelect_exec runCall stE re.nextTmp rc.dst rt.dst re.dst wc wt we
    hLookCE hLookTE hLookE (ht_fr re.nextTmp he_le) (he_fr re.nextTmp (Nat.le_refl _))
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hcond
  rcases hcond with ⟨hc_ty, hsame⟩
  rcases sameScalarTy_eq_true rt.ty re.ty hsame with ⟨hte_eq, _⟩
  rw [← hte_eq] at hEncE
  rcases hc_ty with hci1 | hci64
  · rw [isI1Ty_eq_true rc.ty hci1] at hEncC
    rcases typed_i1_inv vc wc hEncC with ⟨bc, rfl, rfl⟩
    have hbc_ne : ((if bc then (1#64 : BitVec 64) else 0#64) != 0#64) = bc := by cases bc <;> rfl
    rw [hbc_ne] at hOps
    have hEv : evalScalarExpr env (.select c t e) = .ok (if bc then vt else ve) := by
      unfold evalScalarExpr
      rw [hEvC]
      cases bc
      · exact hEvE
      · exact hEvT
    exact finishScalarTail runCall env (.select c t e) st stE k re.nextTmp (re.nextTmp + 1) (re.nextTmp + 2)
      rt.ty (rc.instrs ++ rt.instrs ++ re.instrs) _ (if bc then vt else ve) (if bc then wt else we)
      hcte_le (Nat.le_add_right re.nextTmp 2) (Nat.lt_succ_self (re.nextTmp + 1))
      hEv (by cases bc <;> assumption) hExCTE hStE hFrCTE hOps
  · rw [isI64Ty_eq_true rc.ty hci64] at hEncC
    rcases typed_i64_inv vc wc hEncC with ⟨nc, rfl, rfl⟩
    have hnc_ne : (nc.toBitVec != 0#64) = (nc != 0) := rfl
    rw [hnc_ne] at hOps
    have hEv : evalScalarExpr env (.select c t e) = .ok (if nc != 0 then vt else ve) := by
      unfold evalScalarExpr
      rw [hEvC]
      dsimp only
      cases (nc != 0)
      · exact hEvE
      · exact hEvT
    exact finishScalarTail runCall env (.select c t e) st stE k re.nextTmp (re.nextTmp + 1) (re.nextTmp + 2)
      rt.ty (rc.instrs ++ rt.instrs ++ re.instrs) _ (if nc != 0 then vt else ve) (if nc != 0 then wt else we)
      hcte_le (Nat.le_add_right re.nextTmp 2) (Nat.lt_succ_self (re.nextTmp + 1))
      hEv (by cases (nc != 0) <;> assumption) hExCTE hStE hFrCTE hOps

/-- Post-condition for `.fma a b c` given subexpression post-conditions. -/
theorem lowerFmaStep_post
    (runCall : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal →
      ExecOutcome ⊕ ExecState)
    (env : VarEnv) (a b c : ScalarExpr) (st : ExecState) (k : Nat) (ra rb rc : ScalarLowerRes)
    (hall : (isI64Ty ra.ty && isI64Ty rb.ty && isI64Ty rc.ty) = true)
    (hA : ScalarExecPost runCall env a st k ra)
    (hB : ∀ stA, execInstrsWith runCall st ra.instrs = .inr stA →
      (∀ q, (∀ j, k ≤ j → j < ra.nextTmp → q ≠ tmpReg j) → stA.regs.lookup q = st.regs.lookup q) →
      ScalarExecPost runCall env b stA ra.nextTmp rb)
    (hC : ∀ stA stB, execInstrsWith runCall st ra.instrs = .inr stA →
      (∀ q, (∀ j, k ≤ j → j < ra.nextTmp → q ≠ tmpReg j) → stA.regs.lookup q = st.regs.lookup q) →
      execInstrsWith runCall stA rb.instrs = .inr stB →
      (∀ q, (∀ j, ra.nextTmp ≤ j → j < rb.nextTmp → q ≠ tmpReg j) → stB.regs.lookup q = stA.regs.lookup q) →
      ScalarExecPost runCall env c stB rb.nextTmp rc) :
    ScalarExecPost runCall env (.fma a b c) st k
      ⟨.i64, tmpReg (rc.nextTmp + 1), rc.nextTmp + 2,
        ra.instrs ++ rb.instrs ++ rc.instrs ++
          [ .mul (tmpReg rc.nextTmp) .none .i64 (.reg ra.dst) (.reg rb.dst)
          , .add (tmpReg (rc.nextTmp + 1)) .none .i64 (.reg (tmpReg rc.nextTmp)) (.reg rc.dst) ]⟩ := by
  simp only [Bool.and_eq_true] at hall
  rcases hall with ⟨⟨ha64, hb64⟩, hc64⟩
  rcases hA with ⟨ha_le, ha_fr, va, wa, stA, hEvA, hEncA, hExA, hMemA, hGlobA, hPrevA, hLookA, hFrA⟩
  rcases hB stA hExA hFrA with
    ⟨hb_le, hb_fr, vb, wb, stB, hEvB, hEncB, hExB, hMemB, hGlobB, hPrevB, hLookB, hFrB⟩
  rcases hC stA stB hExA hFrA hExB hFrB with
    ⟨hc_le, hc_fr, vc, wc, stC, hEvC, hEncC, hExC, hMemC, hGlobC, hPrevC, hLookC, hFrC⟩
  rw [isI64Ty_eq_true ra.ty ha64] at hEncA
  rw [isI64Ty_eq_true rb.ty hb64] at hEncB
  rw [isI64Ty_eq_true rc.ty hc64] at hEncC
  rcases typed_i64_inv va wa hEncA with ⟨na, rfl, rfl⟩
  rcases typed_i64_inv vb wb hEncB with ⟨nb, rfl, rfl⟩
  rcases typed_i64_inv vc wc hEncC with ⟨nc, rfl, rfl⟩
  have hab_le := Nat.le_trans ha_le hb_le
  have habc_le := Nat.le_trans hab_le hc_le
  have hFrAB := frame_tmp_Range st.regs stA.regs stB.regs k ra.nextTmp rb.nextTmp ha_le hb_le hFrA hFrB
  have hFrABC := frame_tmp_Range st.regs stB.regs stC.regs k rb.nextTmp rc.nextTmp hab_le hc_le hFrAB hFrC
  have hExAB : execInstrsWith runCall st (ra.instrs ++ rb.instrs) = .inr stB := by
    rw [execInstrsWith_append runCall st stA ra.instrs rb.instrs hExA]
    exact hExB
  have hExABC : execInstrsWith runCall st (ra.instrs ++ rb.instrs ++ rc.instrs) = .inr stC := by
    rw [execInstrsWith_append runCall st stB (ra.instrs ++ rb.instrs) rc.instrs hExAB]
    exact hExC
  have hLookAC : stC.regs.lookup ra.dst = some (.bits .i64 na.toBitVec) := by
    rw [hFrC ra.dst (fun j hj _ => ha_fr j (Nat.le_trans hb_le hj)),
        hFrB ra.dst (fun j hj _ => ha_fr j hj)]
    exact hLookA
  have hLookBC : stC.regs.lookup rb.dst = some (.bits .i64 nb.toBitVec) := by
    rw [hFrC rb.dst (fun j hj _ => hb_fr j hj)]
    exact hLookB
  have hStC : stC.mem = st.mem ∧ stC.globals = st.globals ∧ stC.prevBlock = st.prevBlock :=
    ⟨hMemC.trans (hMemB.trans hMemA), hGlobC.trans (hGlobB.trans hGlobA),
     hPrevC.trans (hPrevB.trans hPrevA)⟩
  have hEv : evalScalarExpr env (.fma a b c) = .ok (.u64 (na * nb + nc)) := by
    unfold evalScalarExpr
    rw [hEvA, hEvB, hEvC]
    rfl
  exact finishScalarTail runCall env (.fma a b c) st stC k rc.nextTmp (rc.nextTmp + 1) (rc.nextTmp + 2)
    .i64 (ra.instrs ++ rb.instrs ++ rc.instrs) _ (.u64 (na * nb + nc)) (na * nb + nc).toBitVec
    habc_le (Nat.le_add_right rc.nextTmp 2) (Nat.lt_succ_self (rc.nextTmp + 1))
    hEv rfl hExABC hStC hFrABC
    (emitFma_exec runCall stC rc.nextTmp ra.dst rb.dst rc.dst na nb nc hLookAC hLookBC hLookC
      (hc_fr rc.nextTmp (Nat.le_refl _)))

/-- Straight-line `lowerScalarExpr` post-condition: executing the lowered instructions binds
`res.dst` to the exact 64-bit word `evalScalarExpr` produced, leaving memory untouched. -/
theorem lowerScalarExpr_post
    (runCall : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal →
      ExecOutcome ⊕ ExecState)
    (Γ : ScalarTyEnv) (env : VarEnv) (se : ScalarExpr) (st : ExecState) (k : Nat)
    (res : ScalarLowerRes)
    (hAgree : EnvTypedAgree Γ env st.regs)
    (hLow : lowerScalarExpr Γ se k = some res) :
    ScalarExecPost runCall env se st k res := by
  induction se generalizing st k res with
  | constU64 n =>
    simp only [lowerScalarExpr, Option.some.injEq] at hLow
    subst hLow
    refine finishScalarTail runCall env (.constU64 n) st st k k k (k + 1) .i64 [] _
      (.u64 n) n.toBitVec (Nat.le_refl k) (Nat.le_succ k) (Nat.lt_succ_self k) rfl rfl rfl ⟨rfl, rfl, rfl⟩
      (fun _ _ => rfl) (singleBin_exec runCall st k _ n.toBitVec ?_)
    simp [stepInstrWith, evalOperand, c64, binResult, flagsOverflow]
    congr 2
    exact BitVec.add_zero n.toBitVec
  | constBool b =>
    simp only [lowerScalarExpr, Option.some.injEq] at hLow
    subst hLow
    refine finishScalarTail runCall env (.constBool b) st st k k k (k + 1) .i1 [] _
      (.bool b) (if b then 1#64 else 0#64) (Nat.le_refl k) (Nat.le_succ k) (Nat.lt_succ_self k) rfl rfl rfl
      ⟨rfl, rfl, rfl⟩ (fun _ _ => rfl) (singleBin_exec runCall st k _ _ ?_)
    cases b <;> simp [stepInstrWith, evalOperand, c64, binResult, flagsOverflow]
  | var x =>
    dsimp [lowerScalarExpr] at hLow
    cases hΓ : Γ x with
    | none => simp [hΓ] at hLow
    | some ty =>
      simp only [hΓ] at hLow
      by_cases hi64 : isI64Ty ty = true
      · simp only [hi64, ↓reduceIte, Option.some.injEq] at hLow
        subst hLow
        rw [isI64Ty_eq_true ty hi64] at hΓ
        rcases hAgree x _ hΓ with ⟨v, w, henv, hw, hlook⟩
        exact ⟨Nat.le_refl k, fun j _ => varReg_ne_tmpReg x j, v, w, st,
          by unfold evalScalarExpr; rw [henv], hw, rfl, rfl, rfl, rfl, hlook, fun _ _ => rfl⟩
      · simp only [hi64, Bool.false_eq_true, ↓reduceIte] at hLow
        by_cases hi1 : isI1Ty ty = true
        · simp only [hi1, ↓reduceIte, Option.some.injEq] at hLow
          subst hLow
          rw [isI1Ty_eq_true ty hi1] at hΓ
          rcases hAgree x _ hΓ with ⟨v, w, henv, hw, hlook⟩
          exact ⟨Nat.le_refl k, fun j _ => varReg_ne_tmpReg x j, v, w, st,
            by unfold evalScalarExpr; rw [henv], hw, rfl, rfl, rfl, rfl, hlook, fun _ _ => rfl⟩
        · simp [hi1] at hLow
  | binOp op l r ihl ihr =>
    dsimp [lowerScalarExpr] at hLow
    cases hLl : lowerScalarExpr Γ l k with
    | none => simp [hLl] at hLow
    | some rl =>
      simp only [hLl, Option.bind] at hLow
      cases hLr : lowerScalarExpr Γ r rl.nextTmp with
      | none => simp [hLr] at hLow
      | some rr =>
        simp only [hLr] at hLow
        exact lowerBinOpStep_post runCall env op l r st k rl rr res
          (ihl st k rl hAgree hLl)
          (fun stL _ hFrL =>
            ihr stL rl.nextTmp rr
              (envTypedAgree_preserved Γ env st.regs stL.regs k rl.nextTmp hAgree hFrL) hLr)
          hLow
  | unaryOp uop a iha =>
    cases uop with
    | not =>
      dsimp [lowerScalarExpr] at hLow
      cases hLa : lowerScalarExpr Γ a k with
      | none => simp [hLa] at hLow
      | some ra =>
        simp only [hLa, Option.bind] at hLow
        rcases iha st k ra hAgree hLa with
          ⟨ha_le, _, va, wa, stA, hEvA, hEncA, hExA, hMemA, hGlobA, hPrevA, hLookA, hFrA⟩
        by_cases hi64 : isI64Ty ra.ty = true
        · simp only [hi64, ↓reduceIte, Option.some.injEq] at hLow
          subst hLow
          rw [isI64Ty_eq_true ra.ty hi64] at hEncA
          rcases typed_i64_inv va wa hEncA with ⟨n, rfl, rfl⟩
          refine finishScalarTail runCall env (.unaryOp .not a) st stA k ra.nextTmp ra.nextTmp (ra.nextTmp + 1)
            .i64 ra.instrs _ (.u64 (~~~n)) (~~~n).toBitVec ha_le (Nat.le_succ _) (Nat.lt_succ_self _)
            (by unfold evalScalarExpr; rw [hEvA]; rfl) rfl hExA ⟨hMemA, hGlobA, hPrevA⟩ hFrA
            (singleBin_exec runCall stA ra.nextTmp _ _ ?_)
          simp [stepInstrWith, evalOperand, lookupReg, hLookA, c64, binResult, flagsOverflow]
          congr 2
          exact u64_not_xor_allOnes n
        · simp only [hi64, Bool.false_eq_true, ↓reduceIte] at hLow
          by_cases hi1 : isI1Ty ra.ty = true
          · simp only [hi1, ↓reduceIte, Option.some.injEq] at hLow
            subst hLow
            rw [isI1Ty_eq_true ra.ty hi1] at hEncA
            rcases typed_i1_inv va wa hEncA with ⟨b, rfl, rfl⟩
            refine finishScalarTail runCall env (.unaryOp .not a) st stA k ra.nextTmp ra.nextTmp (ra.nextTmp + 1)
              .i1 ra.instrs _ (.bool (!b)) (if !b then 1#64 else 0#64) ha_le (Nat.le_succ _) (Nat.lt_succ_self _)
              (by unfold evalScalarExpr; rw [hEvA]; rfl) rfl hExA ⟨hMemA, hGlobA, hPrevA⟩ hFrA
              (singleBin_exec runCall stA ra.nextTmp _ _ ?_)
            cases b <;> simp [stepInstrWith, evalOperand, lookupReg, hLookA, c64, binResult, flagsOverflow]
          · simp [hi1] at hLow
    | neg =>
      dsimp [lowerScalarExpr] at hLow
      cases hLa : lowerScalarExpr Γ a k with
      | none => simp [hLa] at hLow
      | some ra =>
        simp only [hLa, Option.bind] at hLow
        rcases iha st k ra hAgree hLa with
          ⟨ha_le, _, va, wa, stA, hEvA, hEncA, hExA, hMemA, hGlobA, hPrevA, hLookA, hFrA⟩
        by_cases hi64 : isI64Ty ra.ty = true
        · simp only [hi64, ↓reduceIte, Option.some.injEq] at hLow
          subst hLow
          rw [isI64Ty_eq_true ra.ty hi64] at hEncA
          rcases typed_i64_inv va wa hEncA with ⟨n, rfl, rfl⟩
          refine finishScalarTail runCall env (.unaryOp .neg a) st stA k ra.nextTmp ra.nextTmp (ra.nextTmp + 1)
            .i64 ra.instrs _ (.u64 (0 - n)) (0 - n).toBitVec ha_le (Nat.le_succ _) (Nat.lt_succ_self _)
            (by unfold evalScalarExpr; rw [hEvA]; rfl) rfl hExA ⟨hMemA, hGlobA, hPrevA⟩ hFrA
            (singleBin_exec runCall stA ra.nextTmp _ _ ?_)
          simp [stepInstrWith, evalOperand, lookupReg, hLookA, c64, binResult, flagsOverflow]
          rfl
        · simp [hi64] at hLow
    | clz256 => simp [lowerScalarExpr] at hLow
  | select c t e ihc iht ihe =>
    dsimp [lowerScalarExpr] at hLow
    cases hLc : lowerScalarExpr Γ c k with
    | none => simp [hLc] at hLow
    | some rc =>
      simp only [hLc, Option.bind] at hLow
      cases hLt : lowerScalarExpr Γ t rc.nextTmp with
      | none => simp [hLt] at hLow
      | some rt =>
        simp only [hLt] at hLow
        cases hLe : lowerScalarExpr Γ e rt.nextTmp with
        | none => simp [hLe] at hLow
        | some re =>
          simp only [hLe] at hLow
          by_cases hcond : ((isI1Ty rc.ty || isI64Ty rc.ty) && sameScalarTy rt.ty re.ty) = true
          · simp only [hcond, ↓reduceIte, Option.some.injEq] at hLow
            subst hLow
            exact lowerSelectStep_post runCall env c t e st k rc rt re hcond
              (ihc st k rc hAgree hLc)
              (fun stC _ hFrC =>
                iht stC rc.nextTmp rt
                  (envTypedAgree_preserved Γ env st.regs stC.regs k rc.nextTmp hAgree hFrC) hLt)
              (fun stC stT _ hFrC _ hFrT =>
                have hAgC := envTypedAgree_preserved Γ env st.regs stC.regs k rc.nextTmp hAgree hFrC
                ihe stT rt.nextTmp re
                  (envTypedAgree_preserved Γ env stC.regs stT.regs rc.nextTmp rt.nextTmp hAgC hFrT) hLe)
          · simp [hcond] at hLow
  | fma a b c iha ihb ihc =>
    dsimp [lowerScalarExpr] at hLow
    cases hLa : lowerScalarExpr Γ a k with
    | none => simp [hLa] at hLow
    | some ra =>
      simp only [hLa, Option.bind] at hLow
      cases hLb : lowerScalarExpr Γ b ra.nextTmp with
      | none => simp [hLb] at hLow
      | some rb =>
        simp only [hLb] at hLow
        cases hLc : lowerScalarExpr Γ c rb.nextTmp with
        | none => simp [hLc] at hLow
        | some rc =>
          simp only [hLc] at hLow
          by_cases hall : (isI64Ty ra.ty && isI64Ty rb.ty && isI64Ty rc.ty) = true
          · simp only [hall, ↓reduceIte, Option.some.injEq] at hLow
            subst hLow
            exact lowerFmaStep_post runCall env a b c st k ra rb rc hall
              (iha st k ra hAgree hLa)
              (fun stA _ hFrA =>
                ihb stA ra.nextTmp rb
                  (envTypedAgree_preserved Γ env st.regs stA.regs k ra.nextTmp hAgree hFrA) hLb)
              (fun stA stB _ hFrA _ hFrB =>
                have hAgA := envTypedAgree_preserved Γ env st.regs stA.regs k ra.nextTmp hAgree hFrA
                ihc stB rb.nextTmp rc
                  (envTypedAgree_preserved Γ env stA.regs stB.regs ra.nextTmp rb.nextTmp hAgA hFrB) hLc)
          · simp [hall] at hLow

/-- Soundness of `lowerScalarExpr` against `LLVMAst.execInstrs`: whenever LNIR scalar
evaluation produces `val`, executing the lowered instructions binds `res.dst` to the
corresponding 64-bit word without modifying memory. -/
theorem lowerScalarExpr_sound
    (Γ : ScalarTyEnv) (env : VarEnv) (se : ScalarExpr) (st : ExecState) (k : Nat)
    (res : ScalarLowerRes) (mod_ : LLVMModule) (fuel : Nat) (val : Val)
    (hAgree : EnvTypedAgree Γ env st.regs)
    (hLow : lowerScalarExpr Γ se k = some res)
    (hEval : evalScalarExpr env se = .ok val) :
    ∃ w st', encodeScalarVal val = some w ∧
      execInstrs mod_ fuel st res.instrs = .inr st' ∧
      st'.mem = st.mem ∧
      st'.regs.lookup res.dst = some (.bits .i64 w) := by
  rcases lowerScalarExpr_post (runCallWith mod_ fuel) Γ env se st k res hAgree hLow with
    ⟨_, _, v, w, st', hEv, hEnc, hEx, hMem, _, _, hLook, _⟩
  rw [hEval] at hEv
  injection hEv with hv
  subst hv
  exact ⟨w, st', encodeScalarVal_of_typed res.ty val w hEnc, hEx, hMem, hLook⟩

end LeanNative.Proofs
