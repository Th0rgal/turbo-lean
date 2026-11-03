import LeanNative.Proofs.StableHLOScalarProofs

/-!
# Compositional `ScalarExpr` → StableHLO Soundness (`LeanNative.Proofs.StableHLOScalarLowerProofs`)

Proves compositional semantic preservation (`lowerScalarExpr_post` and `lowerScalarCode_post`)
from `LeanNative.Semantics.evalScalarExpr` / `evalCode` to `StableHLOAst.evalOps`.
-/

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend.TargetIR
open LeanNative.Backend.StableHLOAst
open LeanNative.Backend.StableHLOLower
open LeanNative.Backend.LLVMLower (isI64Ty isI1Ty sameScalarTy)

/-- `tenv` binds every scalar entry of `Γ` to the exact 64-bit word `env` holds. -/
def HLOEnvAgree (Γ : HLOTyEnv) (env : VarEnv) (tenv : Env) : Prop :=
  ∀ v r ty kn, Γ v = some ⟨r, .scalar ty kn⟩ →
    ∃ val w, env v = some val ∧ encodeScalarTyped ty val = some w ∧ tenv r = some (mkScUi64 w)

/-- Execution post-condition of a lowered `ScalarExpr`: `evalOps` binds `res.reg` to the
exact 64-bit word `evalScalarExpr` produced, and only touches fresh temporaries. -/
def HLOScalarExecPost (env : VarEnv) (se : ScalarExpr) (tenv : Env) (k : Nat)
    (res : HLOScalarRes) : Prop :=
  k ≤ res.nextTmp ∧
  res.ops.all isNonReturnOp = true ∧
  ∃ v w tenv',
    evalScalarExpr env se = .ok v ∧
    encodeScalarTyped res.ty v = some w ∧
    evalOps tenv res.ops = .ok tenv' ∧
    tenv' res.reg = some (mkScUi64 w) ∧
    HLORegFresh tenv' res.nextTmp ∧
    (∀ q, (∀ j, k ≤ j → j < res.nextTmp → q ≠ hloTmpReg j) → tenv' q = tenv q)

theorem hloEnvAgree_preserved (Γ : HLOTyEnv) (env : VarEnv) (tenv tenv' : Env) (k k' : Nat)
    (hAgree : HLOEnvAgree Γ env tenv) (hFr0 : HLORegFresh tenv k)
    (hFr : ∀ q, (∀ j, k ≤ j → j < k' → q ≠ hloTmpReg j) → tenv' q = tenv q) :
    HLOEnvAgree Γ env tenv' := by
  intro v r ty kn hΓ
  rcases hAgree v r ty kn hΓ with ⟨val, w, henv, hw, htenv⟩
  have hne : ∀ j, k ≤ j → j < k' → r ≠ hloTmpReg j :=
    fun j hj _ => operand_ne_hloTmp_of_fresh htenv hFr0 hj
  exact ⟨val, w, henv, hw, (hFr r hne).trans htenv⟩

/-- Structural inversion for `lowerHLOBinOpStep`. -/
theorem lowerHLOBinOpStep_inv (op : BinOp) (rl rr res : HLOScalarRes)
    (h : lowerHLOBinOpStep op rl rr = some res) :
    (rl.ty = .i64 ∧ rr.ty = .i64 ∧ lowerHLOBinOp64 op rl rr = some res) ∨
    (rl.ty = .i1 ∧ rr.ty = .i1 ∧ op = .eq ∧
      res = ⟨.i1, (emitHLOCmp rr.nextTmp .eq rl.reg rr.reg).1,
        (emitHLOCmp rr.nextTmp .eq rl.reg rr.reg).2.1,
        (rl.ops ++ rr.ops) ++ (emitHLOCmp rr.nextTmp .eq rl.reg rr.reg).2.2⟩) := by
  cases h1 : rl.ty <;> simp only [lowerHLOBinOpStep, h1] at h
  all_goals try contradiction
  · cases h2 : rr.ty <;> simp only [h2] at h
    all_goals try contradiction
    cases op <;> simp only [Option.some.injEq] at h
    all_goals try contradiction
    exact Or.inr ⟨rfl, rfl, rfl, h.symm⟩
  · cases h2 : rr.ty <;> simp only [h2] at h
    all_goals try contradiction
    exact Or.inl ⟨rfl, rfl, h⟩

theorem finishHLOTail (env : VarEnv) (se : ScalarExpr) (tenv tenvP : Env) (k kMid kEnd : Nat)
    (ty : LNIRType) (dst : String) (pfx ops : List StableHLOOp) (v : Val) (w : BitVec 64)
    (hle1 : k ≤ kMid) (hle2 : kMid ≤ kEnd)
    (hEv : evalScalarExpr env se = .ok v)
    (hEnc : encodeScalarTyped ty v = some w)
    (hPfx : evalOps tenv pfx = .ok tenvP)
    (hAllP : pfx.all isNonReturnOp = true)
    (hFrP : ∀ q, (∀ j, k ≤ j → j < kMid → q ≠ hloTmpReg j) → tenvP q = tenv q)
    (hOps : ∃ tenvF, evalOps tenvP ops = .ok tenvF ∧
      ops.all isNonReturnOp = true ∧
      tenvF dst = some (mkScUi64 w) ∧
      HLORegFresh tenvF kEnd ∧
      (∀ q, (∀ j, kMid ≤ j → j < kEnd → q ≠ hloTmpReg j) → tenvF q = tenvP q)) :
    HLOScalarExecPost env se tenv k ⟨ty, dst, kEnd, pfx ++ ops⟩ := by
  rcases hOps with ⟨tenvF, hExF, hAllF, hLookF, hFrF, hFrF2⟩
  refine ⟨Nat.le_trans hle1 hle2, ?_, v, w, tenvF, hEv, hEnc, ?_, hLookF, hFrF,
    frame_hloTmp_range tenv tenvP tenvF k kMid kEnd hle1 hle2 hFrP hFrF2⟩
  · rw [List.all_append, Bool.and_eq_true]
    exact ⟨hAllP, hAllF⟩
  · exact evalOps_append_nonReturn pfx ops tenv tenvP hAllP hPfx ▸ hExF

theorem lowerHLOBinOp64_exec (tenvR : Env) (op : BinOp) (rl rr res : HLOScalarRes) (a b : UInt64)
    (hLookL : tenvR rl.reg = some (mkScUi64 a.toBitVec))
    (hLookR : tenvR rr.reg = some (mkScUi64 b.toBitVec))
    (hFrAll : HLORegFresh tenvR rr.nextTmp)
    (hLow : lowerHLOBinOp64 op rl rr = some res) :
    ∃ (dIdx : Nat) (ops : List StableHLOOp) (v : Val) (w : BitVec 64) (tenv' : Env),
      rr.nextTmp ≤ dIdx ∧ dIdx < res.nextTmp ∧
      res.reg = hloTmpReg dIdx ∧
      res.ops = (rl.ops ++ rr.ops) ++ ops ∧
      evalBinOp op (.u64 a) (.u64 b) = .ok v ∧
      encodeScalarTyped res.ty v = some w ∧
      evalOps tenvR ops = .ok tenv' ∧
      ops.all isNonReturnOp = true ∧
      tenv' (hloTmpReg dIdx) = some (mkScUi64 w) ∧
      HLORegFresh tenv' res.nextTmp ∧
      (∀ q, (∀ j, rr.nextTmp ≤ j → j < res.nextTmp → q ≠ hloTmpReg j) → tenv' q = tenvR q) := by
  cases op <;> simp only [lowerHLOBinOp64, Option.some.injEq] at hLow
  all_goals try contradiction
  all_goals subst hLow
  all_goals dsimp only [HLOScalarRes.nextTmp, emitHLODivRem, emitHLOShiftLogical, emitHLOSar, emitHLOCmp]
  · exact ⟨rr.nextTmp, _, .u64 (a + b), (a + b).toBitVec,
      tenvR.bind (hloTmpReg rr.nextTmp) (mkScUi64 (a + b).toBitVec),
      Nat.le_refl _, Nat.lt_succ_self _, rfl, rfl, rfl, rfl,
      by rw [evalOps_cons_nonReturn _ _ _ rfl, evalOp_add_sc _ _ _ _ _ _ hLookL hLookR]; rfl,
      rfl, env_bind_self _ _ _, hloRegFresh_bind_lt _ hFrAll (by omega),
      fun q hq => env_bind_ne _ _ _ _ (hq rr.nextTmp (Nat.le_refl _) (Nat.lt_succ_self _))⟩
  · exact ⟨rr.nextTmp, _, .u64 (a - b), (a - b).toBitVec,
      tenvR.bind (hloTmpReg rr.nextTmp) (mkScUi64 (a - b).toBitVec),
      Nat.le_refl _, Nat.lt_succ_self _, rfl, rfl, rfl, rfl,
      by rw [evalOps_cons_nonReturn _ _ _ rfl, evalOp_sub_sc _ _ _ _ _ _ hLookL hLookR]; rfl,
      rfl, env_bind_self _ _ _, hloRegFresh_bind_lt _ hFrAll (by omega),
      fun q hq => env_bind_ne _ _ _ _ (hq rr.nextTmp (Nat.le_refl _) (Nat.lt_succ_self _))⟩
  · exact ⟨rr.nextTmp, _, .u64 (a * b), (a * b).toBitVec,
      tenvR.bind (hloTmpReg rr.nextTmp) (mkScUi64 (a * b).toBitVec),
      Nat.le_refl _, Nat.lt_succ_self _, rfl, rfl, rfl, rfl,
      by rw [evalOps_cons_nonReturn _ _ _ rfl, evalOp_mul_sc _ _ _ _ _ _ hLookL hLookR]; rfl,
      rfl, env_bind_self _ _ _, hloRegFresh_bind_lt _ hFrAll (by omega),
      fun q hq => env_bind_ne _ _ _ _ (hq rr.nextTmp (Nat.le_refl _) (Nat.lt_succ_self _))⟩
  · rcases emitHLODivRem_correct tenvR rr.nextTmp false rl.reg rr.reg a b hLookL hLookR hFrAll with
      ⟨hk', hAll, tenv', hEx, hLook, hFr', hFrF⟩
    exact ⟨rr.nextTmp + 5, _, .u64 (a / b), (a / b).toBitVec, tenv',
      by omega, by omega, rfl, rfl, rfl, rfl, hEx, hAll, hLook, hFr', hFrF⟩
  · rcases emitHLODivRem_correct tenvR rr.nextTmp true rl.reg rr.reg a b hLookL hLookR hFrAll with
      ⟨hk', hAll, tenv', hEx, hLook, hFr', hFrF⟩
    exact ⟨rr.nextTmp + 5, _, .u64 (a % b), (a % b).toBitVec, tenv',
      by omega, by omega, rfl, rfl, rfl, rfl, hEx, hAll, hLook, hFr', hFrF⟩
  · exact ⟨rr.nextTmp, _, .u64 (a &&& b), (a &&& b).toBitVec,
      tenvR.bind (hloTmpReg rr.nextTmp) (mkScUi64 (a &&& b).toBitVec),
      Nat.le_refl _, Nat.lt_succ_self _, rfl, rfl, rfl, rfl,
      by rw [evalOps_cons_nonReturn _ _ _ rfl, evalOp_and_sc _ _ _ _ _ _ hLookL hLookR]; rfl,
      rfl, env_bind_self _ _ _, hloRegFresh_bind_lt _ hFrAll (by omega),
      fun q hq => env_bind_ne _ _ _ _ (hq rr.nextTmp (Nat.le_refl _) (Nat.lt_succ_self _))⟩
  · exact ⟨rr.nextTmp, _, .u64 (a ||| b), (a ||| b).toBitVec,
      tenvR.bind (hloTmpReg rr.nextTmp) (mkScUi64 (a ||| b).toBitVec),
      Nat.le_refl _, Nat.lt_succ_self _, rfl, rfl, rfl, rfl,
      by rw [evalOps_cons_nonReturn _ _ _ rfl, evalOp_or_sc _ _ _ _ _ _ hLookL hLookR]; rfl,
      rfl, env_bind_self _ _ _, hloRegFresh_bind_lt _ hFrAll (by omega),
      fun q hq => env_bind_ne _ _ _ _ (hq rr.nextTmp (Nat.le_refl _) (Nat.lt_succ_self _))⟩
  · exact ⟨rr.nextTmp, _, .u64 (a ^^^ b), (a ^^^ b).toBitVec,
      tenvR.bind (hloTmpReg rr.nextTmp) (mkScUi64 (a ^^^ b).toBitVec),
      Nat.le_refl _, Nat.lt_succ_self _, rfl, rfl, rfl, rfl,
      by rw [evalOps_cons_nonReturn _ _ _ rfl, evalOp_xor_sc _ _ _ _ _ _ hLookL hLookR]; rfl,
      rfl, env_bind_self _ _ _, hloRegFresh_bind_lt _ hFrAll (by omega),
      fun q hq => env_bind_ne _ _ _ _ (hq rr.nextTmp (Nat.le_refl _) (Nat.lt_succ_self _))⟩
  · rcases emitHLOShiftLogical_correct tenvR rr.nextTmp false rl.reg rr.reg a b
      hLookL hLookR hFrAll with ⟨hk', hAll, tenv', hEx, hLook, hFr', hFrF⟩
    exact ⟨rr.nextTmp + 2, _, .u64 (a <<< b), (a <<< b).toBitVec, tenv',
      by omega, by omega, rfl, rfl, rfl, rfl, hEx, hAll, hLook, hFr', hFrF⟩
  · rcases emitHLOShiftLogical_correct tenvR rr.nextTmp true rl.reg rr.reg a b
      hLookL hLookR hFrAll with ⟨hk', hAll, tenv', hEx, hLook, hFr', hFrF⟩
    exact ⟨rr.nextTmp + 2, _, .u64 (a >>> b), (a >>> b).toBitVec, tenv',
      by omega, by omega, rfl, rfl, rfl, rfl, hEx, hAll, hLook, hFr', hFrF⟩
  · rcases emitHLOSar_correct tenvR rr.nextTmp rl.reg rr.reg a b hLookL hLookR hFrAll with
      ⟨hk', hAll, tenv', hEx, hLook, hFr', hFrF⟩
    exact ⟨rr.nextTmp + 5, _, .u64 (lnirSar64 a b), (lnirSar64 a b).toBitVec, tenv',
      by omega, by omega, rfl, rfl, rfl, rfl, hEx, hAll, hLook, hFr', hFrF⟩
  · rcases emitHLOCmp_correct tenvR rr.nextTmp .eq rl.reg rr.reg a.toBitVec b.toBitVec
      hLookL hLookR hFrAll with ⟨hk', hAll, tenv', hEx, hLook, hFr', hFrF⟩
    exact ⟨rr.nextTmp + 1, _, .bool (a == b), if a == b then 1#64 else 0#64, tenv',
      by omega, by omega, rfl, rfl, rfl, rfl, hEx, hAll, hLook, hFr', hFrF⟩
  · rcases emitHLOCmp_correct tenvR rr.nextTmp .lt rl.reg rr.reg a.toBitVec b.toBitVec
      hLookL hLookR hFrAll with ⟨hk', hAll, tenv', hEx, hLook, hFr', hFrF⟩
    exact ⟨rr.nextTmp + 1, _, .bool (decide (a < b)), if decide (a < b) then 1#64 else 0#64, tenv',
      by omega, by omega, rfl, rfl, rfl, rfl, hEx, hAll,
      by rw [cmpDirBool_lt_eq_ult] at hLook; exact hLook, hFr', hFrF⟩
  · rcases emitHLOCmp_correct tenvR rr.nextTmp .le rl.reg rr.reg a.toBitVec b.toBitVec
      hLookL hLookR hFrAll with ⟨hk', hAll, tenv', hEx, hLook, hFr', hFrF⟩
    exact ⟨rr.nextTmp + 1, _, .bool (decide (a ≤ b)), if decide (a ≤ b) then 1#64 else 0#64, tenv',
      by omega, by omega, rfl, rfl, rfl, rfl, hEx, hAll,
      by rw [cmpDirBool_le_eq_ule] at hLook; exact hLook, hFr', hFrF⟩

theorem lowerHLOBinOpStep_post (env : VarEnv) (op : BinOp) (l r : ScalarExpr)
    (tenv : Env) (k : Nat) (rl rr res : HLOScalarRes)
    (hL : HLOScalarExecPost env l tenv k rl)
    (hR : ∀ tenvL, evalOps tenv rl.ops = .ok tenvL →
      (∀ q, (∀ j, k ≤ j → j < rl.nextTmp → q ≠ hloTmpReg j) → tenvL q = tenv q) →
      HLORegFresh tenvL rl.nextTmp →
      HLOScalarExecPost env r tenvL rl.nextTmp rr)
    (hLow : lowerHLOBinOpStep op rl rr = some res) :
    HLOScalarExecPost env (.binOp op l r) tenv k res := by
  rcases hL with ⟨hl_le, hl_all, vl, wl, tenvL, hEvL, hEncL, hExL, hLookL, hFrL, hFrameL⟩
  rcases hR tenvL hExL hFrameL hFrL with
    ⟨hr_le, hr_all, vr, wr, tenvR, hEvR, hEncR, hExR, hLookR, hFrR, hFrameR⟩
  have hLookLR : tenvR rl.reg = some (mkScUi64 wl) := by
    rw [hFrameR rl.reg (fun j hlo _ => operand_ne_hloTmp_of_fresh hLookL hFrL hlo)]
    exact hLookL
  have hExLR : evalOps tenv (rl.ops ++ rr.ops) = .ok tenvR := by
    rw [evalOps_append_nonReturn rl.ops rr.ops tenv tenvL hl_all hExL]
    exact hExR
  have hFrLR := frame_hloTmp_range tenv tenvL tenvR k rl.nextTmp rr.nextTmp hl_le hr_le hFrameL hFrameR
  have hkLR : k ≤ rr.nextTmp := Nat.le_trans hl_le hr_le
  rcases lowerHLOBinOpStep_inv op rl rr res hLow with ⟨htl, htr, h64⟩ | ⟨htl, htr, hop, hres⟩
  · rw [htl] at hEncL
    rw [htr] at hEncR
    rcases typed_i64_inv vl wl hEncL with ⟨a, rfl, rfl⟩
    rcases typed_i64_inv vr wr hEncR with ⟨b, rfl, rfl⟩
    rcases lowerHLOBinOp64_exec tenvR op rl rr res a b hLookLR hLookR
        hFrR h64 with
      ⟨dIdx, ops, v, w, tenv', hdLo, hdHi, hDst, hIns, hEvOp, hEncV, hExOp, hAllO, hLkO, hFrO, hFrF⟩
    rcases res with ⟨rty, rdst, rnext, rops⟩
    dsimp only at hDst hIns hdHi hEncV
    subst hDst
    subst hIns
    have hEv : evalScalarExpr env (.binOp op l r) = .ok v := by
      unfold evalScalarExpr
      rw [hEvL, hEvR]
      exact hEvOp
    exact finishHLOTail env (.binOp op l r) tenv tenvR k rr.nextTmp rnext rty (hloTmpReg dIdx)
      (rl.ops ++ rr.ops) ops v w hkLR (Nat.le_trans hdLo (Nat.le_of_lt hdHi))
      hEv hEncV hExLR (by rw [List.all_append, Bool.and_eq_true]; exact ⟨hl_all, hr_all⟩)
      hFrLR ⟨tenv', hExOp, hAllO, hLkO, hFrO, hFrF⟩
  · subst hop
    subst hres
    rw [htl] at hEncL
    rw [htr] at hEncR
    rcases typed_i1_inv vl wl hEncL with ⟨b1, rfl, rfl⟩
    rcases typed_i1_inv vr wr hEncR with ⟨b2, rfl, rfl⟩
    rcases emitHLOCmp_correct tenvR rr.nextTmp .eq rl.reg rr.reg
        (if b1 then 1#64 else 0#64) (if b2 then 1#64 else 0#64)
        hLookLR hLookR hFrR with ⟨hk', hAll, tenv', hEx, hLook, hFr', hFrF⟩
    have hcmp : cmpDirBool .eq (if b1 then 1#64 else 0#64) (if b2 then 1#64 else 0#64) =
        (b1 == b2) := by cases b1 <;> cases b2 <;> rfl
    have hEv : evalScalarExpr env (.binOp .eq l r) = .ok (.bool (b1 == b2)) := by
      unfold evalScalarExpr
      rw [hEvL, hEvR]
      rfl
    exact finishHLOTail env (.binOp .eq l r) tenv tenvR k rr.nextTmp (rr.nextTmp + 2) .i1
      (hloTmpReg (rr.nextTmp + 1)) (rl.ops ++ rr.ops) _ (.bool (b1 == b2))
      (if b1 == b2 then 1#64 else 0#64) hkLR (by omega)
      hEv rfl hExLR (by rw [List.all_append, Bool.and_eq_true]; exact ⟨hl_all, hr_all⟩)
      hFrLR ⟨tenv', hEx, hAll, by rw [hcmp] at hLook; exact hLook, hFr', hFrF⟩

theorem lowerHLOSelectStep_post (env : VarEnv) (c t e : ScalarExpr) (tenv : Env) (k : Nat)
    (rc rt re : HLOScalarRes)
    (hcond : ((isI1Ty rc.ty || isI64Ty rc.ty) && sameScalarTy rt.ty re.ty) = true)
    (hC : HLOScalarExecPost env c tenv k rc)
    (hT : ∀ tenvC, evalOps tenv rc.ops = .ok tenvC →
      (∀ q, (∀ j, k ≤ j → j < rc.nextTmp → q ≠ hloTmpReg j) → tenvC q = tenv q) →
      HLORegFresh tenvC rc.nextTmp →
      HLOScalarExecPost env t tenvC rc.nextTmp rt)
    (hE : ∀ tenvC tenvT, evalOps tenv rc.ops = .ok tenvC →
      (∀ q, (∀ j, k ≤ j → j < rc.nextTmp → q ≠ hloTmpReg j) → tenvC q = tenv q) →
      HLORegFresh tenvC rc.nextTmp →
      evalOps tenvC rt.ops = .ok tenvT →
      (∀ q, (∀ j, rc.nextTmp ≤ j → j < rt.nextTmp → q ≠ hloTmpReg j) → tenvT q = tenvC q) →
      HLORegFresh tenvT rt.nextTmp →
      HLOScalarExecPost env e tenvT rt.nextTmp re) :
    HLOScalarExecPost env (.select c t e) tenv k
      ⟨rt.ty, hloTmpReg (re.nextTmp + 1), re.nextTmp + 2,
        rc.ops ++ rt.ops ++ re.ops ++
          [ .convert (hloTmpReg re.nextTmp) rc.reg .i1
          , .select (hloTmpReg (re.nextTmp + 1)) (hloTmpReg re.nextTmp) rt.reg re.reg ]⟩ := by
  rcases hC with ⟨hc_le, hc_all, vc, wc, tenvC, hEvC, hEncC, hExC, hLookC, hFrC, hFrameC⟩
  rcases hT tenvC hExC hFrameC hFrC with
    ⟨ht_le, ht_all, vt, wt, tenvT, hEvT, hEncT, hExT, hLookT, hFrT, hFrameT⟩
  rcases hE tenvC tenvT hExC hFrameC hFrC hExT hFrameT hFrT with
    ⟨he_le, he_all, ve, we, tenvE, hEvE, hEncE, hExE, hLookE, hFrE, hFrameE⟩
  have hct_le := Nat.le_trans hc_le ht_le
  have hcte_le := Nat.le_trans hct_le he_le
  have hFrCT := frame_hloTmp_range tenv tenvC tenvT k rc.nextTmp rt.nextTmp hc_le ht_le hFrameC hFrameT
  have hFrCTE := frame_hloTmp_range tenv tenvT tenvE k rt.nextTmp re.nextTmp hct_le he_le hFrCT hFrameE
  have hExCT : evalOps tenv (rc.ops ++ rt.ops) = .ok tenvT := by
    rw [evalOps_append_nonReturn rc.ops rt.ops tenv tenvC hc_all hExC]
    exact hExT
  have hExCTE : evalOps tenv (rc.ops ++ rt.ops ++ re.ops) = .ok tenvE := by
    rw [evalOps_append_nonReturn (rc.ops ++ rt.ops) re.ops tenv tenvT
      (by rw [List.all_append, Bool.and_eq_true]; exact ⟨hc_all, ht_all⟩) hExCT]
    exact hExE
  have hLookCE : tenvE rc.reg = some (mkScUi64 wc) := by
    rw [hFrameE rc.reg (fun j hj _ => operand_ne_hloTmp_of_fresh hLookC hFrC (Nat.le_trans ht_le hj)),
        hFrameT rc.reg (fun j hj _ => operand_ne_hloTmp_of_fresh hLookC hFrC hj)]
    exact hLookC
  have hLookTE : tenvE rt.reg = some (mkScUi64 wt) := by
    rw [hFrameE rt.reg (fun j hj _ => operand_ne_hloTmp_of_fresh hLookT hFrT hj)]
    exact hLookT
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hcond
  rcases hcond with ⟨hc_ty, hsame⟩
  rcases sameScalarTy_eq_true rt.ty re.ty hsame with ⟨hte_eq, _⟩
  rw [← hte_eq] at hEncE
  let p := hloTmpReg re.nextTmp
  let d := hloTmpReg (re.nextTmp + 1)
  have hExec2 : ∀ (bSel : Bool) (tP : TensorVal),
      tP = { ty := scI1Ty, data := #[if bSel then 1#64 else 0#64] } →
      evalOp tenvE (.convert p rc.reg .i1) = .ok (tenvE.bind p tP) →
      evalOps tenvE [ .convert p rc.reg .i1, .select d p rt.reg re.reg ] =
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
  rcases hc_ty with hci1 | hci64
  · rw [isI1Ty_eq_true rc.ty hci1] at hEncC
    rcases typed_i1_inv vc wc hEncC with ⟨bc, rfl, rfl⟩
    have hbw : (if ((if bc then (1#64 : BitVec 64) else 0#64) == 0#64) then (0#64 : BitVec 64) else 1#64) =
        (if bc then 1#64 else 0#64) := by cases bc <;> rfl
    have hs1 : evalOp tenvE (.convert p rc.reg .i1) =
        .ok (tenvE.bind p { ty := scI1Ty, data := #[if bc then 1#64 else 0#64] }) := by
      rw [evalOp_convert_ui64_i1_sc tenvE p rc.reg (if bc then 1#64 else 0#64) hLookCE, hbw]
    have hEv : evalScalarExpr env (.select c t e) = .ok (if bc then vt else ve) := by
      unfold evalScalarExpr
      rw [hEvC]
      cases bc
      · exact hEvE
      · exact hEvT
    exact finishHLOTail env (.select c t e) tenv tenvE k re.nextTmp (re.nextTmp + 2) rt.ty d
      (rc.ops ++ rt.ops ++ re.ops) [ .convert p rc.reg .i1, .select d p rt.reg re.reg ]
      (if bc then vt else ve) (if bc then wt else we) hcte_le (by omega)
      hEv (by cases bc <;> assumption) hExCTE
      (by rw [List.all_append, Bool.and_eq_true]; exact ⟨by rw [List.all_append, Bool.and_eq_true]; exact ⟨hc_all, ht_all⟩, he_all⟩)
      hFrCTE ⟨_, hExec2 bc _ rfl hs1, rfl, env_bind_self _ _ _,
        hloRegFresh_bind_lt _ (hloRegFresh_bind_lt _ hFrE (by omega)) (by omega),
        fun q hq => by
          rw [env_bind_ne _ _ _ _ (hq (re.nextTmp + 1) (by omega) (by omega)),
              env_bind_ne _ _ _ _ (hq re.nextTmp (by omega) (by omega))]⟩
  · rw [isI64Ty_eq_true rc.ty hci64] at hEncC
    rcases typed_i64_inv vc wc hEncC with ⟨nc, rfl, rfl⟩
    have hbw : (if (nc.toBitVec == 0#64) then (0#64 : BitVec 64) else 1#64) =
        (if (nc != 0) then 1#64 else 0#64) := by
      by_cases hnz : nc = 0
      · subst hnz; rfl
      · have h1 : (nc != 0) = true := bne_iff_ne.mpr hnz
        have h2 : (nc.toBitVec == 0#64) = false :=
          Bool.eq_false_iff.mpr (fun heq => hnz (UInt64.eq_of_toBitVec_eq (eq_of_beq heq)))
        rw [h1, h2]; rfl
    have hs1 : evalOp tenvE (.convert p rc.reg .i1) =
        .ok (tenvE.bind p { ty := scI1Ty, data := #[if (nc != 0) then 1#64 else 0#64] }) := by
      rw [evalOp_convert_ui64_i1_sc tenvE p rc.reg nc.toBitVec hLookCE, hbw]
    have hEv : evalScalarExpr env (.select c t e) = .ok (if (nc != 0) then vt else ve) := by
      unfold evalScalarExpr
      rw [hEvC]
      dsimp only
      cases (nc != 0)
      · exact hEvE
      · exact hEvT
    exact finishHLOTail env (.select c t e) tenv tenvE k re.nextTmp (re.nextTmp + 2) rt.ty d
      (rc.ops ++ rt.ops ++ re.ops) [ .convert p rc.reg .i1, .select d p rt.reg re.reg ]
      (if (nc != 0) then vt else ve) (if (nc != 0) then wt else we) hcte_le (by omega)
      hEv (by cases (nc != 0) <;> assumption) hExCTE
      (by rw [List.all_append, Bool.and_eq_true]; exact ⟨by rw [List.all_append, Bool.and_eq_true]; exact ⟨hc_all, ht_all⟩, he_all⟩)
      hFrCTE ⟨_, hExec2 (nc != 0) _ rfl hs1, rfl, env_bind_self _ _ _,
        hloRegFresh_bind_lt _ (hloRegFresh_bind_lt _ hFrE (by omega)) (by omega),
        fun q hq => by
          rw [env_bind_ne _ _ _ _ (hq (re.nextTmp + 1) (by omega) (by omega)),
              env_bind_ne _ _ _ _ (hq re.nextTmp (by omega) (by omega))]⟩

theorem lowerHLOFmaStep_post (env : VarEnv) (a b c : ScalarExpr) (tenv : Env) (k : Nat)
    (ra rb rc : HLOScalarRes)
    (hall : (isI64Ty ra.ty && isI64Ty rb.ty && isI64Ty rc.ty) = true)
    (hA : HLOScalarExecPost env a tenv k ra)
    (hB : ∀ tenvA, evalOps tenv ra.ops = .ok tenvA →
      (∀ q, (∀ j, k ≤ j → j < ra.nextTmp → q ≠ hloTmpReg j) → tenvA q = tenv q) →
      HLORegFresh tenvA ra.nextTmp →
      HLOScalarExecPost env b tenvA ra.nextTmp rb)
    (hC : ∀ tenvA tenvB, evalOps tenv ra.ops = .ok tenvA →
      (∀ q, (∀ j, k ≤ j → j < ra.nextTmp → q ≠ hloTmpReg j) → tenvA q = tenv q) →
      HLORegFresh tenvA ra.nextTmp →
      evalOps tenvA rb.ops = .ok tenvB →
      (∀ q, (∀ j, ra.nextTmp ≤ j → j < rb.nextTmp → q ≠ hloTmpReg j) → tenvB q = tenvA q) →
      HLORegFresh tenvB rb.nextTmp →
      HLOScalarExecPost env c tenvB rb.nextTmp rc) :
    HLOScalarExecPost env (.fma a b c) tenv k
      ⟨.i64, hloTmpReg (rc.nextTmp + 1), rc.nextTmp + 2,
        ra.ops ++ rb.ops ++ rc.ops ++
          [ .multiply (hloTmpReg rc.nextTmp) ra.reg rb.reg
          , .add (hloTmpReg (rc.nextTmp + 1)) (hloTmpReg rc.nextTmp) rc.reg ]⟩ := by
  simp only [Bool.and_eq_true] at hall
  rcases hall with ⟨⟨ha64, hb64⟩, hc64⟩
  rcases hA with ⟨ha_le, ha_all, va, wa, tenvA, hEvA, hEncA, hExA, hLookA, hFrA, hFrameA⟩
  rcases hB tenvA hExA hFrameA hFrA with
    ⟨hb_le, hb_all, vb, wb, tenvB, hEvB, hEncB, hExB, hLookB, hFrB, hFrameB⟩
  rcases hC tenvA tenvB hExA hFrameA hFrA hExB hFrameB hFrB with
    ⟨hc_le, hc_all, vc, wc, tenvC, hEvC, hEncC, hExC, hLookC, hFrC, hFrameC⟩
  rw [isI64Ty_eq_true ra.ty ha64] at hEncA
  rw [isI64Ty_eq_true rb.ty hb64] at hEncB
  rw [isI64Ty_eq_true rc.ty hc64] at hEncC
  rcases typed_i64_inv va wa hEncA with ⟨na, rfl, rfl⟩
  rcases typed_i64_inv vb wb hEncB with ⟨nb, rfl, rfl⟩
  rcases typed_i64_inv vc wc hEncC with ⟨nc, rfl, rfl⟩
  have hab_le := Nat.le_trans ha_le hb_le
  have habc_le := Nat.le_trans hab_le hc_le
  have hFrAB := frame_hloTmp_range tenv tenvA tenvB k ra.nextTmp rb.nextTmp ha_le hb_le hFrameA hFrameB
  have hFrABC := frame_hloTmp_range tenv tenvB tenvC k rb.nextTmp rc.nextTmp hab_le hc_le hFrAB hFrameC
  have hExAB : evalOps tenv (ra.ops ++ rb.ops) = .ok tenvB := by
    rw [evalOps_append_nonReturn ra.ops rb.ops tenv tenvA ha_all hExA]
    exact hExB
  have hExABC : evalOps tenv (ra.ops ++ rb.ops ++ rc.ops) = .ok tenvC := by
    rw [evalOps_append_nonReturn (ra.ops ++ rb.ops) rc.ops tenv tenvB
      (by rw [List.all_append, Bool.and_eq_true]; exact ⟨ha_all, hb_all⟩) hExAB]
    exact hExC
  have hLookAC : tenvC ra.reg = some (mkScUi64 na.toBitVec) := by
    rw [hFrameC ra.reg (fun j hj _ => operand_ne_hloTmp_of_fresh hLookA hFrA (Nat.le_trans hb_le hj)),
        hFrameB ra.reg (fun j hj _ => operand_ne_hloTmp_of_fresh hLookA hFrA hj)]
    exact hLookA
  have hLookBC : tenvC rb.reg = some (mkScUi64 nb.toBitVec) := by
    rw [hFrameC rb.reg (fun j hj _ => operand_ne_hloTmp_of_fresh hLookB hFrB hj)]
    exact hLookB
  have hs1 : evalOp tenvC (.multiply (hloTmpReg rc.nextTmp) ra.reg rb.reg) =
      .ok (tenvC.bind (hloTmpReg rc.nextTmp) (mkScUi64 (na * nb).toBitVec)) :=
    evalOp_mul_sc tenvC (hloTmpReg rc.nextTmp) ra.reg rb.reg na.toBitVec nb.toBitVec hLookAC hLookBC
  have hs2 : evalOp (tenvC.bind (hloTmpReg rc.nextTmp) (mkScUi64 (na * nb).toBitVec))
      (.add (hloTmpReg (rc.nextTmp + 1)) (hloTmpReg rc.nextTmp) rc.reg) =
      .ok ((tenvC.bind (hloTmpReg rc.nextTmp) (mkScUi64 (na * nb).toBitVec)).bind
        (hloTmpReg (rc.nextTmp + 1)) (mkScUi64 (na * nb + nc).toBitVec)) :=
    evalOp_add_sc _ _ _ rc.reg (na * nb).toBitVec nc.toBitVec (env_bind_self _ _ _)
      (by rw [env_bind_ne _ _ _ _ (operand_ne_hloTmp_of_fresh hLookC hFrC (Nat.le_refl _))]; exact hLookC)
  have hEv : evalScalarExpr env (.fma a b c) = .ok (.u64 (na * nb + nc)) := by
    unfold evalScalarExpr
    rw [hEvA, hEvB, hEvC]
    rfl
  exact finishHLOTail env (.fma a b c) tenv tenvC k rc.nextTmp (rc.nextTmp + 2) .i64
    (hloTmpReg (rc.nextTmp + 1))
    (ra.ops ++ rb.ops ++ rc.ops)
    [ .multiply (hloTmpReg rc.nextTmp) ra.reg rb.reg
    , .add (hloTmpReg (rc.nextTmp + 1)) (hloTmpReg rc.nextTmp) rc.reg ]
    (.u64 (na * nb + nc)) (na * nb + nc).toBitVec habc_le (by omega)
    hEv rfl hExABC
    (by rw [List.all_append, Bool.and_eq_true]; exact ⟨by rw [List.all_append, Bool.and_eq_true]; exact ⟨ha_all, hb_all⟩, hc_all⟩)
    hFrABC ⟨_,
      by rw [evalOps_cons_nonReturn _ _ _ rfl, hs1]; dsimp only [bind, Except.bind]
         rw [evalOps_cons_nonReturn _ _ _ rfl, hs2]; rfl,
      rfl, env_bind_self _ _ _,
      hloRegFresh_bind_lt _ (hloRegFresh_bind_lt _ hFrC (by omega)) (by omega),
      fun q hq => by
        rw [env_bind_ne _ _ _ _ (hq (rc.nextTmp + 1) (by omega) (by omega)),
            env_bind_ne _ _ _ _ (hq rc.nextTmp (by omega) (by omega))]⟩

/-- Straight-line `lowerScalarExpr` post-condition. -/
theorem lowerScalarExpr_post (Γ : HLOTyEnv) (env : VarEnv) (se : ScalarExpr)
    (tenv : Env) (k : Nat) (res : HLOScalarRes)
    (hAgree : HLOEnvAgree Γ env tenv)
    (hFr : HLORegFresh tenv k)
    (hLow : lowerScalarExpr Γ se k = some res) :
    HLOScalarExecPost env se tenv k res := by
  induction se generalizing tenv k res with
  | constU64 n =>
    simp only [lowerScalarExpr, Option.some.injEq] at hLow
    subst hLow
    exact finishHLOTail env (.constU64 n) tenv tenv k k (k + 1) .i64 (hloTmpReg k) [] _
      (.u64 n) n.toBitVec (Nat.le_refl k) (Nat.le_succ k) rfl rfl rfl rfl
      (fun _ _ => rfl) ⟨tenv.bind (hloTmpReg k) (mkScUi64 n.toBitVec),
        by rw [evalOps_cons_nonReturn _ _ _ rfl, evalOp_constant_sc]; rfl, rfl,
        env_bind_self _ _ _, hloRegFresh_bind_lt _ hFr (by omega),
        fun q hq => env_bind_ne _ _ _ _ (hq k (Nat.le_refl _) (Nat.lt_succ_self _))⟩
  | constBool b =>
    simp only [lowerScalarExpr, Option.some.injEq] at hLow
    subst hLow
    exact finishHLOTail env (.constBool b) tenv tenv k k (k + 1) .i1 (hloTmpReg k) [] _
      (.bool b) (if b then 1#64 else 0#64) (Nat.le_refl k) (Nat.le_succ k) rfl rfl rfl rfl
      (fun _ _ => rfl) ⟨tenv.bind (hloTmpReg k) (mkScUi64 (if b then 1#64 else 0#64)),
        by rw [evalOps_cons_nonReturn _ _ _ rfl, evalOp_constant_sc]; rfl, rfl,
        env_bind_self _ _ _, hloRegFresh_bind_lt _ hFr (by omega),
        fun q hq => env_bind_ne _ _ _ _ (hq k (Nat.le_refl _) (Nat.lt_succ_self _))⟩
  | var x =>
    dsimp [lowerScalarExpr] at hLow
    cases hΓ : Γ x with
    | none => simp [hΓ] at hLow
    | some e =>
      rcases e with ⟨r, kind⟩
      cases kind with
      | tensor1D _ => simp [hΓ] at hLow
      | scalar ty kn =>
        simp only [hΓ] at hLow
        rcases hAgree x r ty kn hΓ with ⟨val, w, henv, hw, htenv⟩
        by_cases hi64 : isI64Ty ty = true
        · simp only [hi64, Bool.true_or, ↓reduceIte, Option.some.injEq] at hLow
          subst hLow
          exact ⟨Nat.le_refl k, rfl, val, w, tenv,
            by unfold evalScalarExpr; rw [henv], hw, rfl, htenv, hFr, fun _ _ => rfl⟩
        · by_cases hi1 : isI1Ty ty = true
          · simp only [hi64, hi1, Bool.false_or, ↓reduceIte, Option.some.injEq] at hLow
            subst hLow
            exact ⟨Nat.le_refl k, rfl, val, w, tenv,
              by unfold evalScalarExpr; rw [henv], hw, rfl, htenv, hFr, fun _ _ => rfl⟩
          · have hff : (isI64Ty ty || isI1Ty ty) = false := by
              cases h1 : isI64Ty ty <;> cases h2 : isI1Ty ty <;> simp_all
            simp [hff] at hLow
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
        exact lowerHLOBinOpStep_post env op l r tenv k rl rr res
          (ihl tenv k rl hAgree hFr hLl)
          (fun tenvL _ hFrame hFrL =>
            ihr tenvL rl.nextTmp rr (hloEnvAgree_preserved Γ env tenv tenvL k rl.nextTmp
              hAgree hFr hFrame) hFrL hLr)
          hLow
  | unaryOp uop a iha =>
    cases uop with
    | not =>
      dsimp [lowerScalarExpr] at hLow
      cases hLa : lowerScalarExpr Γ a k with
      | none => simp [hLa] at hLow
      | some ra =>
        simp only [hLa, Option.bind] at hLow
        rcases iha tenv k ra hAgree hFr hLa with
          ⟨ha_le, ha_all, va, wa, tenvA, hEvA, hEncA, hExA, hLookA, hFrA, hFrameA⟩
        by_cases hi64 : isI64Ty ra.ty = true
        · simp only [hi64, ↓reduceIte, Option.some.injEq] at hLow
          subst hLow
          rw [isI64Ty_eq_true ra.ty hi64] at hEncA
          rcases typed_i64_inv va wa hEncA with ⟨n, rfl, rfl⟩
          exact finishHLOTail env (.unaryOp .not a) tenv tenvA k ra.nextTmp (ra.nextTmp + 2)
            .i64 (hloTmpReg (ra.nextTmp + 1)) ra.ops _ (.u64 (~~~n)) (~~~n).toBitVec ha_le (by omega)
            (by unfold evalScalarExpr; rw [hEvA]; rfl) rfl
            hExA ha_all hFrameA ⟨(tenvA.bind (hloTmpReg ra.nextTmp)
              (mkScUi64 (BitVec.ofNat 64 0xffffffffffffffff))).bind
              (hloTmpReg (ra.nextTmp + 1)) (mkScUi64 (~~~n).toBitVec),
              by rw [evalOps_cons_nonReturn _ _ _ rfl, evalOp_constant_sc]
                 dsimp only [bind, Except.bind]
                 rw [evalOps_cons_nonReturn _ _ _ rfl]
                 rw [evalOp_xor_sc _ _ ra.reg (hloTmpReg ra.nextTmp) n.toBitVec _
                   (by rw [env_bind_ne _ _ _ _ (operand_ne_hloTmp_of_fresh hLookA hFrA (Nat.le_refl _))]; exact hLookA)
                   (env_bind_self _ _ _), u64_not_xor_allOnes]
                 rfl, rfl, env_bind_self _ _ _,
              hloRegFresh_bind_lt _ (hloRegFresh_bind_lt _ hFrA (by omega)) (by omega),
              fun q hq => by
                rw [env_bind_ne _ _ _ _ (hq (ra.nextTmp + 1) (by omega) (by omega)),
                    env_bind_ne _ _ _ _ (hq ra.nextTmp (by omega) (by omega))]⟩
        · simp only [hi64, Bool.false_eq_true, ↓reduceIte] at hLow
          by_cases hi1 : isI1Ty ra.ty = true
          · simp only [hi1, ↓reduceIte, Option.some.injEq] at hLow
            subst hLow
            rw [isI1Ty_eq_true ra.ty hi1] at hEncA
            rcases typed_i1_inv va wa hEncA with ⟨b, rfl, rfl⟩
            exact finishHLOTail env (.unaryOp .not a) tenv tenvA k ra.nextTmp (ra.nextTmp + 2)
              .i1 (hloTmpReg (ra.nextTmp + 1)) ra.ops _ (.bool (!b)) (if !b then 1#64 else 0#64)
              ha_le (by omega) (by unfold evalScalarExpr; rw [hEvA]; rfl) rfl hExA ha_all hFrameA
              ⟨(tenvA.bind (hloTmpReg ra.nextTmp) (mkScUi64 1#64)).bind
                (hloTmpReg (ra.nextTmp + 1)) (mkScUi64 (if !b then 1#64 else 0#64)),
                by rw [evalOps_cons_nonReturn _ _ _ rfl, evalOp_constant_sc]
                   dsimp only [bind, Except.bind]
                   rw [evalOps_cons_nonReturn _ _ _ rfl]
                   have hlk : (tenvA.bind (hloTmpReg ra.nextTmp) (mkScUi64 1#64)) ra.reg =
                       some (mkScUi64 (if b then 1#64 else 0#64)) := by
                     rw [env_bind_ne _ _ _ _ (operand_ne_hloTmp_of_fresh hLookA hFrA (Nat.le_refl _))]
                     exact hLookA
                   rw [evalOp_xor_sc _ _ ra.reg (hloTmpReg ra.nextTmp)
                     (if b then 1#64 else 0#64) 1#64 hlk (env_bind_self _ _ _)]
                   cases b <;> rfl,
                rfl, env_bind_self _ _ _,
                hloRegFresh_bind_lt _ (hloRegFresh_bind_lt _ hFrA (by omega)) (by omega),
                fun q hq => by
                  rw [env_bind_ne _ _ _ _ (hq (ra.nextTmp + 1) (by omega) (by omega)),
                      env_bind_ne _ _ _ _ (hq ra.nextTmp (by omega) (by omega))]⟩
          · simp [hi1] at hLow
    | neg =>
      dsimp [lowerScalarExpr] at hLow
      cases hLa : lowerScalarExpr Γ a k with
      | none => simp [hLa] at hLow
      | some ra =>
        simp only [hLa, Option.bind] at hLow
        rcases iha tenv k ra hAgree hFr hLa with
          ⟨ha_le, ha_all, va, wa, tenvA, hEvA, hEncA, hExA, hLookA, hFrA, hFrameA⟩
        by_cases hi64 : isI64Ty ra.ty = true
        · simp only [hi64, ↓reduceIte, Option.some.injEq] at hLow
          subst hLow
          rw [isI64Ty_eq_true ra.ty hi64] at hEncA
          rcases typed_i64_inv va wa hEncA with ⟨n, rfl, rfl⟩
          exact finishHLOTail env (.unaryOp .neg a) tenv tenvA k ra.nextTmp (ra.nextTmp + 2)
            .i64 (hloTmpReg (ra.nextTmp + 1)) ra.ops _ (.u64 (0 - n)) (0 - n).toBitVec ha_le (by omega)
            (by unfold evalScalarExpr; rw [hEvA]; rfl) rfl hExA ha_all hFrameA
            ⟨(tenvA.bind (hloTmpReg ra.nextTmp) (mkScUi64 0#64)).bind
              (hloTmpReg (ra.nextTmp + 1)) (mkScUi64 (0 - n).toBitVec),
              by rw [evalOps_cons_nonReturn _ _ _ rfl, evalOp_constant_sc]
                 dsimp only [bind, Except.bind]
                 rw [evalOps_cons_nonReturn _ _ _ rfl]
                 rw [evalOp_sub_sc _ _ (hloTmpReg ra.nextTmp) ra.reg 0#64 n.toBitVec (env_bind_self _ _ _)
                   (by rw [env_bind_ne _ _ _ _ (operand_ne_hloTmp_of_fresh hLookA hFrA (Nat.le_refl _))]; exact hLookA)]
                 rfl, rfl, env_bind_self _ _ _,
              hloRegFresh_bind_lt _ (hloRegFresh_bind_lt _ hFrA (by omega)) (by omega),
              fun q hq => by
                rw [env_bind_ne _ _ _ _ (hq (ra.nextTmp + 1) (by omega) (by omega)),
                    env_bind_ne _ _ _ _ (hq ra.nextTmp (by omega) (by omega))]⟩
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
            exact lowerHLOSelectStep_post env c t e tenv k rc rt re hcond
              (ihc tenv k rc hAgree hFr hLc)
              (fun tenvC _ hFrame hFrC =>
                iht tenvC rc.nextTmp rt (hloEnvAgree_preserved Γ env tenv tenvC k rc.nextTmp
                  hAgree hFr hFrame) hFrC hLt)
              (fun tenvC tenvT _ hFrameC hFrC _ hFrameT hFrT =>
                have hAgC := hloEnvAgree_preserved Γ env tenv tenvC k rc.nextTmp hAgree hFr hFrameC
                ihe tenvT rt.nextTmp re (hloEnvAgree_preserved Γ env tenvC tenvT rc.nextTmp rt.nextTmp
                  hAgC hFrC hFrameT) hFrT hLe)
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
            exact lowerHLOFmaStep_post env a b c tenv k ra rb rc hall
              (iha tenv k ra hAgree hFr hLa)
              (fun tenvA _ hFrame hFrA =>
                ihb tenvA ra.nextTmp rb (hloEnvAgree_preserved Γ env tenv tenvA k ra.nextTmp
                  hAgree hFr hFrame) hFrA hLb)
              (fun tenvA tenvB _ hFrameA hFrA _ hFrameB hFrB =>
                have hAgA := hloEnvAgree_preserved Γ env tenv tenvA k ra.nextTmp hAgree hFr hFrameA
                ihc tenvB rb.nextTmp rc (hloEnvAgree_preserved Γ env tenvA tenvB ra.nextTmp rb.nextTmp
                  hAgA hFrA hFrameB) hFrB hLc)
          · simp [hall] at hLow

end LeanNative.Proofs
