import LeanNative.Backend.MetalLower
import LeanNative.Backend.MetalAst.Proofs
import Std.Tactic.BVDecide

namespace LeanNative.Proofs.MetalLowerProofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend
open LeanNative.Backend.MetalLower

theorem lowerScalar_inferExprType
    (g : MetalAst.MSLGroupState)
    (ls : MetalAst.MSLLocals)
    (idxName : String) (idxVar : Nat) (boundVars : List Nat)
    (e : ScalarExpr) (s : Bool)
    (hsort : inferScalarSort boundVars e = some s)
    (hty : ∀ id ∈ boundVars,
      ls.lookupType? (if id == idxVar then idxName else s!"v{id}") = some .ulong) :
    MetalAst.inferExprType g ls (lowerScalar idxName idxVar e) = .ulong := by
  induction e generalizing s with
  | constU64 _ => rfl
  | constBool _ => rfl
  | var id =>
    simp only [inferScalarSort] at hsort
    split at hsort
    · rename_i hmem
      have hl := hty id hmem
      unfold lowerScalar v
      cases hidx : id == idxVar
      · simp only [hidx, Bool.false_eq_true, ite_false] at hl ⊢
        simp only [MetalAst.inferExprType, hl]
      · simp only [hidx, ite_true] at hl ⊢
        simp only [MetalAst.inferExprType, hl]
    · cases hsort
  | binOp op l r ihl ihr =>
    simp only [inferScalarSort] at hsort
    cases hsl : inferScalarSort boundVars l <;> simp only [hsl] at hsort
    · cases hsort
    · rename_i sl
      cases hsr : inferScalarSort boundVars r <;> simp only [hsr] at hsort
      · cases hsort
      · rename_i sr
        have tl := ihl sl hsl
        have tr := ihr sr hsr
        cases sl
        · cases sr
          · cases op <;> simp [inferBinOpU64] at hsort <;>
              dsimp only [lowerScalar, u, m63, MetalAst.inferExprType] <;>
              simp only [MetalAst.promoteMSLArithType_ulong, tl, tr]
          · simp at hsort
        · cases sr
          · simp at hsort
          · cases op <;> simp [inferBinOpBool] at hsort <;>
              dsimp only [lowerScalar, u, m63, MetalAst.inferExprType] <;>
              simp only [MetalAst.promoteMSLArithType_ulong, tl, tr]
  | unaryOp op a iha =>
    simp only [inferScalarSort] at hsort
    cases hsa : inferScalarSort boundVars a <;> simp only [hsa] at hsort
    · cases hsort
    · rename_i sa
      have ta := iha sa hsa
      cases sa
      · cases op <;> simp [inferUnaryOpU64] at hsort <;>
          dsimp only [lowerScalar, u, MetalAst.inferExprType] <;>
          simp only [MetalAst.promoteMSLArithType_ulong, ta]
      · simp at hsort
  | select c t f ihc iht ihf =>
    simp only [inferScalarSort] at hsort
    cases hsc : inferScalarSort boundVars c <;> simp only [hsc] at hsort
    · cases hsort
    · cases hst : inferScalarSort boundVars t <;> simp only [hst] at hsort
      · cases hsort
      · rename_i st
        cases hsf : inferScalarSort boundVars f <;> simp only [hsf] at hsort
        · cases hsort
        · have tt := iht st hst
          simp only [lowerScalar, MetalAst.inferExprType, tt]
  | fma a b c iha ihb ihc =>
    simp only [inferScalarSort] at hsort
    cases hsa : inferScalarSort boundVars a <;> simp only [hsa] at hsort
    · cases hsort
    · rename_i sa
      cases hsb : inferScalarSort boundVars b <;> simp only [hsb] at hsort
      · cases hsort
      · rename_i sb
        cases hsc : inferScalarSort boundVars c <;> simp only [hsc] at hsort
        · cases hsort
        · rename_i sc
          have ta := iha sa hsa
          have tb := ihb sb hsb
          have tc := ihc sc hsc
          simp only [lowerScalar, MetalAst.inferExprType,
            MetalAst.promoteMSLArithType_ulong, ta, tb, tc]

theorem varEnvMatchesLocals_mem (env : VarEnv) (ls : MetalAst.MSLLocals)
    (idxName : String) (idxVar : Nat) (boundVars : List Nat)
    (hmatch : varEnvMatchesLocals env ls idxName idxVar boundVars)
    {id : Nat} (hmem : id ∈ boundVars) :
    ∃ x : UInt64, env id = some (.u64 x) ∧
      ls.lookup? (if id == idxVar then idxName else s!"v{id}") = some x.toBitVec ∧
      ls.lookupType? (if id == idxVar then idxName else s!"v{id}") = some .ulong := by
  induction boundVars with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases hmatch with ⟨hhd, htl⟩
    cases List.mem_cons.mp hmem with
    | inl heq => subst heq; exact hhd
    | inr hrest => exact ih htl hrest

private theorem valOfSort_false {v : Val} {bv : BitVec 64} (h : valOfSort false v = some bv) :
    ∃ x : UInt64, v = .u64 x ∧ bv = x.toBitVec := by
  cases v <;> simp [valOfSort] at h
  exact ⟨_, rfl, h.symm⟩

private theorem valOfSort_true {v : Val} {bv : BitVec 64} (h : valOfSort true v = some bv) :
    ∃ b : Bool, v = .bool b ∧ bv = (if b then 1#64 else 0#64) := by
  cases v <;> simp [valOfSort] at h
  exact ⟨_, rfl, h.symm⟩

private theorem lowerBinOpU64_eval
    (callEval : Nat → MetalAst.MSLGroupState →
      MetalAst.Dim3 → MetalAst.MSLLocals →
      List MetalAst.MSLAccess → String →
      MetalAst.MSLExprList →
      MetalAst.MSLOutcome MetalAst.MSLEval)
    (env : VarEnv) (idxName : String) (idxVar : Nat) (l r : ScalarExpr)
    (op : BinOp) (s : Bool) (xl xr : UInt64)
    (hsort : inferBinOpU64 op = some s)
    (hevl : evalScalarExpr env l = .ok (.u64 xl)) (hevr : evalScalarExpr env r = .ok (.u64 xr)) :
    ∃ (val : Val) (bv : BitVec 64),
      evalScalarExpr env (.binOp op l r) = .ok val ∧
      valOfSort s val = some bv ∧
      ∀ (fuel : Nat) (g : MetalAst.MSLGroupState)
        (tid : MetalAst.Dim3) (ls : MetalAst.MSLLocals)
        (log : List MetalAst.MSLAccess),
        MetalAst.evalExprWithCall callEval fuel g tid ls log (lowerScalar idxName idxVar l) =
          .ok { value := xl.toBitVec, fields := [], locals := ls, log := log } →
        MetalAst.evalExprWithCall callEval fuel g tid ls log (lowerScalar idxName idxVar r) =
          .ok { value := xr.toBitVec, fields := [], locals := ls, log := log } →
        MetalAst.inferExprType g ls (lowerScalar idxName idxVar l) = .ulong →
        MetalAst.inferExprType g ls (lowerScalar idxName idxVar r) = .ulong →
        MetalAst.evalExprWithCall callEval fuel g tid ls log
          (lowerScalar idxName idxVar (.binOp op l r)) =
          .ok { value := bv, fields := [], locals := ls, log := log } := by
  cases op with
  | addChecked256 | subChecked256 | mulChecked256 | clmul64 | clmul64Hi | gf2Affine => cases hsort
  | add =>
    injection hsort with hs; subst hs
    exact ⟨.u64 (xl + xr), (xl + xr).toBitVec, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
      fun f g t ls lg hl hr htl htr => MetalAst.ev_add_ulong callEval f g t ls lg _ _ _ _ hl hr htl htr⟩
  | sub =>
    injection hsort with hs; subst hs
    exact ⟨.u64 (xl - xr), (xl - xr).toBitVec, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
      fun f g t ls lg hl hr htl htr => MetalAst.ev_sub_ulong callEval f g t ls lg _ _ _ _ hl hr htl htr⟩
  | mul =>
    injection hsort with hs; subst hs
    exact ⟨.u64 (xl * xr), (xl * xr).toBitVec, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
      fun f g t ls lg hl hr htl htr => MetalAst.ev_mul_ulong callEval f g t ls lg _ _ _ _ hl hr htl htr⟩
  | bitAnd =>
    injection hsort with hs; subst hs
    exact ⟨.u64 (xl &&& xr), (xl &&& xr).toBitVec, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
      fun f g t ls lg hl hr htl htr => MetalAst.ev_bitand_ulong callEval f g t ls lg _ _ _ _ hl hr htl htr⟩
  | bitOr =>
    injection hsort with hs; subst hs
    exact ⟨.u64 (xl ||| xr), (xl ||| xr).toBitVec, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
      fun f g t ls lg hl hr htl htr => MetalAst.ev_bitor_ulong callEval f g t ls lg _ _ _ _ hl hr htl htr⟩
  | bitXor =>
    injection hsort with hs; subst hs
    exact ⟨.u64 (xl ^^^ xr), (xl ^^^ xr).toBitVec, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
      fun f g t ls lg hl hr htl htr => MetalAst.ev_bitxor_ulong callEval f g t ls lg _ _ _ _ hl hr htl htr⟩
  | div =>
    injection hsort with hs; subst hs
    exact ⟨.u64 (xl / xr), (xl / xr).toBitVec, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
      fun f g t ls lg hl hr htl htr => MetalAst.ev_div_guarded_ulong callEval f g t ls lg _ _ _ _ hl hr htl htr⟩
  | mod =>
    injection hsort with hs; subst hs
    exact ⟨.u64 (xl % xr), (xl % xr).toBitVec, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
      fun f g t ls lg hl hr htl htr => MetalAst.ev_mod_guarded_ulong callEval f g t ls lg _ _ _ _ hl hr htl htr⟩
  | shl =>
    injection hsort with hs; subst hs
    refine ⟨.u64 (xl <<< xr), (xl <<< xr).toBitVec, ?_, rfl, fun f g t ls lg hl hr htl htr => ?_⟩
    · simp [evalScalarExpr, hevl, hevr]; rfl
    have h := MetalAst.ev_shl_masked_ulong callEval f g t ls lg _ _ _ _ hl hr htl htr
    rw [MetalAst.shl_bv_eq_u64] at h; exact h
  | shr =>
    injection hsort with hs; subst hs
    refine ⟨.u64 (xl >>> xr), (xl >>> xr).toBitVec, ?_, rfl, fun f g t ls lg hl hr htl htr => ?_⟩
    · simp [evalScalarExpr, hevl, hevr]; rfl
    have h := MetalAst.ev_shr_masked_ulong callEval f g t ls lg _ _ _ _ hl hr htl htr
    rw [MetalAst.shr_bv_eq_u64] at h; exact h
  | sar =>
    injection hsort with hs; subst hs
    have hev : evalScalarExpr env (.binOp .sar l r) = .ok (
        let sh := xr &&& 63
        let signBit := (xl >>> 63) &&& 1
        let shifted := xl >>> sh
        .u64 (if signBit != 0 && sh != 0 then shifted ||| (0xffffffffffffffff <<< (64 - sh)) else shifted)) := by
      simp only [evalScalarExpr, hevl, hevr]; rfl
    refine ⟨_, _, hev, rfl, fun f g t ls lg hl hr htl htr => ?_⟩
    have h := MetalAst.ev_sar_masked_ulong callEval f g t ls lg _ _ _ _ hl hr htl htr
    rw [MetalAst.sar_bv_eq_u64] at h; exact h
  | eor3 =>
    injection hsort with hs; subst hs
    refine ⟨.u64 ((xl ^^^ (xr >>> 32)) ^^^ (xr &&& 0xffffffff)), _, ?_, rfl,
      fun f g t ls lg hl hr htl htr => ?_⟩
    · simp [evalScalarExpr, hevl, hevr]; rfl
    have h := MetalAst.ev_eor3_compound_ulong callEval f g t ls lg _ _ _ _ hl hr htl htr
    rw [MetalAst.eor3_bv_eq_u64] at h
    exact h
  | eq =>
    injection hsort with hs; subst hs
    refine ⟨.bool (xl == xr), if xl == xr then 1#64 else 0#64, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
      fun f g t ls lg hl hr htl htr => ?_⟩
    have h := MetalAst.ev_eq_cast_ulong callEval f g t ls lg _ _ _ _ hl hr htl htr
    rw [MetalAst.eq_bv_iff] at h; exact h
  | lt =>
    injection hsort with hs; subst hs
    exact ⟨.bool (decide (xl < xr)), if decide (xl < xr) then 1#64 else 0#64, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
      fun f g t ls lg hl hr htl htr => MetalAst.ev_lt_cast_ulong callEval f g t ls lg _ _ _ _ hl hr htl htr⟩
  | le =>
    injection hsort with hs; subst hs
    exact ⟨.bool (decide (xl ≤ xr)), if decide (xl ≤ xr) then 1#64 else 0#64, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
      fun f g t ls lg hl hr htl htr => MetalAst.ev_le_cast_ulong callEval f g t ls lg _ _ _ _ hl hr htl htr⟩

private theorem lowerScalar_eval_core
    (callEval : Nat → MetalAst.MSLGroupState →
      MetalAst.Dim3 → MetalAst.MSLLocals →
      List MetalAst.MSLAccess → String →
      MetalAst.MSLExprList →
      MetalAst.MSLOutcome MetalAst.MSLEval)
    (env : VarEnv) (idxName : String) (idxVar : Nat) (boundVars : List Nat)
    (henv : ∀ id ∈ boundVars, ∃ x : UInt64, env id = some (.u64 x))
    (e : ScalarExpr) (s : Bool) (hsort : inferScalarSort boundVars e = some s) :
    ∃ (val : Val) (bv : BitVec 64),
      evalScalarExpr env e = .ok val ∧
      valOfSort s val = some bv ∧
      ∀ (fuel : Nat) (g : MetalAst.MSLGroupState)
        (tid : MetalAst.Dim3) (ls : MetalAst.MSLLocals)
        (log : List MetalAst.MSLAccess),
        varEnvMatchesLocals env ls idxName idxVar boundVars →
        MetalAst.evalExprWithCall callEval fuel g tid ls log
          (lowerScalar idxName idxVar e) =
          .ok { value := bv, fields := [], locals := ls, log := log } := by
  have htyM : ∀ (ls : MetalAst.MSLLocals),
      varEnvMatchesLocals env ls idxName idxVar boundVars →
      ∀ id ∈ boundVars, ls.lookupType? (if id == idxVar then idxName else s!"v{id}") = some .ulong := by
    intro ls hm id hmem
    rcases varEnvMatchesLocals_mem env ls idxName idxVar boundVars hm hmem with ⟨_, _, _, ht⟩
    exact ht
  induction e generalizing s with
  | constU64 n =>
    injection hsort with hs; subst hs
    refine ⟨.u64 n, n.toBitVec, rfl, rfl, fun _ _ _ _ _ _ => ?_⟩
    unfold lowerScalar; rw [MetalAst.evalExprWithCall]
  | constBool b =>
    injection hsort with hs; subst hs
    refine ⟨.bool b, if b then 1#64 else 0#64, rfl, rfl, fun _ _ _ _ _ _ => ?_⟩
    cases b <;> rfl
  | var id =>
    simp only [inferScalarSort] at hsort
    split at hsort
    · rename_i hmem
      injection hsort with hs; subst hs
      rcases henv id hmem with ⟨x, hx⟩
      refine ⟨.u64 x, x.toBitVec, by simp only [evalScalarExpr, hx], rfl, fun fuel g tid ls log hm => ?_⟩
      rcases varEnvMatchesLocals_mem env ls idxName idxVar boundVars hm hmem with ⟨x', hx', hlk, hlt⟩
      have hxeq : x' = x := by
        have hsome : (some (.u64 x) : Option Val) = some (.u64 x') := hx.symm.trans hx'
        injection hsome with hv; injection hv with heq; exact heq.symm
      subst x'; unfold lowerScalar v
      cases hidx : id == idxVar
      · simp only [hidx, Bool.false_eq_true, ite_false] at hlk hlt ⊢
        exact MetalAst.ev_var_bound callEval fuel g tid ls log s!"v{id}" x.toBitVec hlk hlt
      · simp only [hidx, ite_true] at hlk hlt ⊢
        exact MetalAst.ev_var_bound callEval fuel g tid ls log idxName x.toBitVec hlk hlt
    · cases hsort
  | unaryOp op a iha =>
    simp only [inferScalarSort] at hsort
    cases hsa : inferScalarSort boundVars a with
    | none => simp [hsa] at hsort
    | some sa =>
      rw [hsa] at hsort
      cases sa
      · simp only [Bool.not_false, ite_true] at hsort
        rcases iha false hsa with ⟨va, _, heva, hva, haAll⟩
        rcases valOfSort_false hva with ⟨xa, rfl, rfl⟩
        cases op with
        | clz256 => cases hsort
        | not =>
          injection hsort with hs; subst hs
          exact ⟨.u64 (~~~xa), (~~~xa).toBitVec, by simp [evalScalarExpr, heva]; rfl, rfl, fun f g t ls lg hm =>
            MetalAst.ev_bitnot_ulong callEval f g t ls lg _ _ (haAll f g t ls lg hm)
              (lowerScalar_inferExprType g ls idxName idxVar boundVars a false hsa (htyM ls hm))⟩
        | neg =>
          injection hsort with hs; subst hs
          exact ⟨.u64 (0 - xa), (0 - xa).toBitVec, by simp [evalScalarExpr, heva]; rfl, rfl, fun f g t ls lg hm =>
            MetalAst.ev_neg_zero_sub_ulong callEval f g t ls lg _ _ (haAll f g t ls lg hm)
              (lowerScalar_inferExprType g ls idxName idxVar boundVars a false hsa (htyM ls hm))⟩
      · simp at hsort
  | fma a b c iha ihb ihc =>
    simp only [inferScalarSort] at hsort
    cases hsa : inferScalarSort boundVars a with
    | none => simp [hsa] at hsort
    | some sa =>
      cases hsb : inferScalarSort boundVars b with
      | none => simp [hsa, hsb] at hsort
      | some sb =>
        cases hsc : inferScalarSort boundVars c with
        | none => simp [hsa, hsb, hsc] at hsort
        | some sc =>
          rw [hsa, hsb, hsc] at hsort
          cases sa
          · cases sb
            · cases sc
              · simp only [Bool.not_false, Bool.and_self, ite_true, Option.some.injEq] at hsort; subst hsort
                rcases iha false hsa with ⟨va, _, heva, hva, haAll⟩
                rcases ihb false hsb with ⟨vb, _, hevb, hvb, hbAll⟩
                rcases ihc false hsc with ⟨vc, _, hevc, hvc, hcAll⟩
                rcases valOfSort_false hva with ⟨xa, rfl, rfl⟩
                rcases valOfSort_false hvb with ⟨xb, rfl, rfl⟩
                rcases valOfSort_false hvc with ⟨xc, rfl, rfl⟩
                exact ⟨.u64 (xa * xb + xc), (xa * xb + xc).toBitVec,
                  by simp [evalScalarExpr, heva, hevb, hevc]; rfl, rfl, fun f g t ls lg hm =>
                    MetalAst.ev_fma_compound_ulong callEval f g t ls lg _ _ _ _ _ _
                      (haAll f g t ls lg hm) (hbAll f g t ls lg hm) (hcAll f g t ls lg hm)
                      (lowerScalar_inferExprType g ls idxName idxVar boundVars a false hsa (htyM ls hm))
                      (lowerScalar_inferExprType g ls idxName idxVar boundVars b false hsb (htyM ls hm))
                      (lowerScalar_inferExprType g ls idxName idxVar boundVars c false hsc (htyM ls hm))⟩
              · simp at hsort
            · simp at hsort
          · simp at hsort
  | select c t f ihc iht ihf =>
    simp only [inferScalarSort] at hsort
    cases hsc : inferScalarSort boundVars c with
    | none => simp [hsc] at hsort
    | some sc =>
      cases hst : inferScalarSort boundVars t with
      | none => simp [hsc, hst] at hsort
      | some st =>
        cases hsf : inferScalarSort boundVars f with
        | none => simp [hsc, hst, hsf] at hsort
        | some sf =>
          rw [hsc, hst, hsf] at hsort
          cases heq : (st == sf)
          · simp [heq] at hsort
          · simp only [heq, ite_true, Option.some.injEq] at hsort
            have hstf : st = sf := eq_of_beq heq
            subst hstf hsort
            rcases ihc sc hsc with ⟨vc, bvc, hevc, hvc, hcAll⟩
            rcases iht st hst with ⟨vt, bvt, hevt, hvt, htAll⟩
            rcases ihf st hsf with ⟨vf, bvf, hevf, hvf, hfAll⟩
            cases sc with
            | true =>
              rcases valOfSort_true hvc with ⟨bc, rfl, rfl⟩
              refine ⟨if bc then vt else vf, if bc then bvt else bvf, ?_, by cases bc <;> assumption, fun fl g td ls lg hm => ?_⟩
              · cases bc <;> simp [evalScalarExpr, hevc, hevt, hevf]
              · have h := MetalAst.ev_select_ne_zero callEval fl g td ls lg _ _ _ _ _ _
                  (hcAll fl g td ls lg hm) (htAll fl g td ls lg hm) (hfAll fl g td ls lg hm)
                  (lowerScalar_inferExprType g ls idxName idxVar boundVars c true hsc (htyM ls hm))
                cases bc <;> exact h
            | false =>
              rcases valOfSort_false hvc with ⟨xc, rfl, rfl⟩
              have hnzEq : (xc.toBitVec != 0#64) = (xc != 0) := by
                cases h : (xc != 0)
                · have hx0 : xc = 0 := by simpa [bne_iff_ne] using h
                  subst hx0; rfl
                · cases h2 : (xc.toBitVec != 0#64)
                  · have hx0 : xc = 0 := UInt64.eq_of_toBitVec_eq (by simpa [bne_iff_ne] using h2)
                    subst hx0; cases h
                  · rfl
              refine ⟨if xc != 0 then vt else vf, if xc != 0 then bvt else bvf, ?_,
                by cases (xc != 0) <;> assumption, fun fl g td ls lg hm => ?_⟩
              · cases hxc : (xc != 0) <;> simp [evalScalarExpr, hevc, hxc, hevt, hevf]
              · have h := MetalAst.ev_select_ne_zero callEval fl g td ls lg _ _ _ _ _ _
                  (hcAll fl g td ls lg hm) (htAll fl g td ls lg hm) (hfAll fl g td ls lg hm)
                  (lowerScalar_inferExprType g ls idxName idxVar boundVars c false hsc (htyM ls hm))
                rw [hnzEq] at h; exact h
  | binOp op l r ihl ihr =>
    simp only [inferScalarSort] at hsort
    cases hsl : inferScalarSort boundVars l with
    | none => simp [hsl] at hsort
    | some sl =>
      cases hsr : inferScalarSort boundVars r with
      | none => simp [hsl, hsr] at hsort
      | some sr =>
        rw [hsl, hsr] at hsort
        cases sl
        · cases sr
          · simp only [Bool.not_false, Bool.and_self, ite_true] at hsort
            rcases ihl false hsl with ⟨vl, _, hevl, hvl, hlAll⟩
            rcases ihr false hsr with ⟨vr, _, hevr, hvr, hrAll⟩
            rcases valOfSort_false hvl with ⟨xl, rfl, rfl⟩
            rcases valOfSort_false hvr with ⟨xr, rfl, rfl⟩
            obtain ⟨val, bv, hev, hvs, hmsl⟩ := lowerBinOpU64_eval callEval env idxName idxVar l r op s xl xr hsort hevl hevr
            exact ⟨val, bv, hev, hvs, fun fl g td ls lg hm => hmsl fl g td ls lg (hlAll fl g td ls lg hm) (hrAll fl g td ls lg hm)
              (lowerScalar_inferExprType g ls idxName idxVar boundVars l false hsl (htyM ls hm))
              (lowerScalar_inferExprType g ls idxName idxVar boundVars r false hsr (htyM ls hm))⟩
          · simp at hsort
        · cases sr
          · simp at hsort
          · simp only [Bool.not_true, Bool.false_eq_true, ite_false, Bool.and_self, ite_true] at hsort
            rcases ihl true hsl with ⟨vl, _, hevl, hvl, hlAll⟩
            rcases ihr true hsr with ⟨vr, _, hevr, hvr, hrAll⟩
            rcases valOfSort_true hvl with ⟨bl, rfl, rfl⟩
            rcases valOfSort_true hvr with ⟨br, rfl, rfl⟩
            cases op <;> simp [inferBinOpBool] at hsort
            subst hsort
            refine ⟨.bool (bl == br), if bl == br then 1#64 else 0#64, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
              fun fl g td ls lg hm => ?_⟩
            have h := MetalAst.ev_eq_cast_ulong callEval fl g td ls lg _ _ _ _
              (hlAll fl g td ls lg hm) (hrAll fl g td ls lg hm)
              (lowerScalar_inferExprType g ls idxName idxVar boundVars l true hsl (htyM ls hm))
              (lowerScalar_inferExprType g ls idxName idxVar boundVars r true hsr (htyM ls hm))
            have hbeq : ((if bl then (1#64 : BitVec 64) else 0#64) == (if br then 1#64 else 0#64)) = (bl == br) := by
              cases bl
              · cases br <;> rfl
              · cases br <;> rfl
            rw [hbeq] at h; exact h

/-- Expression-level soundness of `MetalLower.lowerScalar`: every well-sorted `LNIR.ScalarExpr`
evaluates in `MetalAst.evalExprWithCall` to the exact bitvector encoding of `LNIR.evalScalarExpr`,
preserving `MSLLocals` and `MSLAccess` epoch logs. -/
theorem lowerScalar_eval_sound
    (callEval : Nat → MetalAst.MSLGroupState →
      MetalAst.Dim3 → MetalAst.MSLLocals →
      List MetalAst.MSLAccess → String →
      MetalAst.MSLExprList →
      MetalAst.MSLOutcome MetalAst.MSLEval)
    (fuel : Nat) (g : MetalAst.MSLGroupState)
    (tid : MetalAst.Dim3)
    (ls : MetalAst.MSLLocals)
    (log : List MetalAst.MSLAccess)
    (env : VarEnv) (idxName : String) (idxVar : Nat) (boundVars : List Nat)
    (e : ScalarExpr) (s : Bool)
    (hsort : inferScalarSort boundVars e = some s)
    (hmatch : varEnvMatchesLocals env ls idxName idxVar boundVars) :
    ∃ (val : Val) (bv : BitVec 64),
      evalScalarExpr env e = .ok val ∧
      valOfSort s val = some bv ∧
      MetalAst.evalExprWithCall callEval fuel g tid ls log
        (lowerScalar idxName idxVar e) =
        .ok { value := bv, fields := [], locals := ls, log := log } := by
  have henv : ∀ id ∈ boundVars, ∃ x : UInt64, env id = some (.u64 x) := by
    intro id hmem
    rcases varEnvMatchesLocals_mem env ls idxName idxVar boundVars hmatch hmem with ⟨x, hx, _, _⟩
    exact ⟨x, hx⟩
  obtain ⟨val, bv, hev, hvs, hmsl⟩ := lowerScalar_eval_core callEval env idxName idxVar boundVars henv e s hsort
  exact ⟨val, bv, hev, hvs, hmsl fuel g tid ls log hmatch⟩

private theorem packInputDeviceBuffersGo_props (env : VarEnv) (st : HeapState) (len : Nat) :
    ∀ (inputs : List VarId) (idx : Nat) (bufs : List (Nat × MetalAst.ByteMemory)),
      packInputDeviceBuffersGo env st len idx inputs = some bufs →
      (∀ k, k < idx → bufs.lookup k = none) ∧
      (∀ k, idx + inputs.length ≤ k → bufs.lookup k = none) ∧
      (∀ j < inputs.length, ∃ (words : List (BitVec 64)),
        bufs.lookup (idx + j) = some (MetalAst.ByteMemory.ofU64Words words) ∧
        words.length = len ∧
        ∀ i (_ : i < len) (hwi : i < words.length),
          ∃ x : UInt64, readParInput env st inputs j i = .ok x ∧ words[i] = x.toBitVec)
  | [], idx, bufs, h => by
    simp only [packInputDeviceBuffersGo, Option.some.injEq] at h
    subst h
    exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | v :: rest, idx, bufs, h => by
    unfold packInputDeviceBuffersGo at h
    cases hv : env v with
    | none => simp [hv] at h
    | some val =>
      cases val <;> simp [hv] at h
      all_goals
        rename_i bid
        cases ht : packInputDeviceBuffersGo env st len (idx + 1) rest with
        | none => simp [ht] at h
        | some tail =>
          rw [ht] at h
          dsimp only at h
          cases hfind : st.findBuffer bid with
          | none => simp [hfind] at h
          | some buf =>
            rw [hfind] at h
            dsimp only at h
            split at h
            · rename_i hlenLe
              simp only [Option.some.injEq] at h
              subst h
              rcases packInputDeviceBuffersGo_props env st len rest (idx + 1) tail ht with ⟨hlo, hhi, hmid⟩
              refine ⟨?_, ?_, ?_⟩
              · intro k hk
                have hne : (k == idx) = false := beq_eq_false_iff_ne.mpr (by omega)
                simp only [List.lookup, hne]
                exact hlo k (by omega)
              · intro k hk
                simp only [List.length_cons] at hk
                have hne : (k == idx) = false := beq_eq_false_iff_ne.mpr (by omega)
                simp only [List.lookup, hne]
                exact hhi k (by omega)
              · intro j hj
                cases j with
                | zero =>
                  let words := (List.range len).map fun i => (buf.data[i]?.getD 0).toBitVec
                  refine ⟨words, ?_, by simp [words], ?_⟩
                  · simp [Nat.add_zero, List.lookup, words]
                  · intro i hi hwi
                    have hiBuf : i < buf.data.size := Nat.lt_of_lt_of_le hi hlenLe
                    refine ⟨buf.data[i], ?_, ?_⟩
                    · unfold readParInput
                      simp only [List.getElem?_cons_zero]
                      simp [hv, HeapState.readElem, hfind, hiBuf]
                    · simp [words, Array.getElem?_eq_getElem hiBuf]
                | succ j' =>
                  simp only [List.length_cons] at hj
                  have hj' : j' < rest.length := by omega
                  rcases hmid j' hj' with ⟨words, hlk, hwlen, hread⟩
                  have hadd : idx + (j' + 1) = (idx + 1) + j' := by omega
                  have hne : ((idx + 1) + j' == idx) = false := beq_eq_false_iff_ne.mpr (by omega)
                  refine ⟨words, ?_, hwlen, ?_⟩
                  · simp only [List.lookup]
                    rw [hadd, hne]
                    exact hlk
                  · intro i hi hwi
                    rcases hread i hi hwi with ⟨x, hr, hw⟩
                    refine ⟨x, ?_, hw⟩
                    unfold readParInput at hr ⊢
                    simp only [List.getElem?_cons_succ]
                    cases hget : rest[j']? with
                    | none =>
                      rw [hget] at hr
                      cases hr
                    | some vv =>
                      rw [hget] at hr
                      exact hr
            · cases h

private theorem varEnvMatchesLocals_append_one (curEnv : VarEnv) (ls : MetalAst.MSLLocals)
    (idxName : String) (idxVar iv : VarId) (x : UInt64)
    (hivNe : iv ≠ idxVar)
    (hlk : ls.lookup? s!"v{iv}" = some x.toBitVec)
    (hty : ls.lookupType? s!"v{iv}" = some .ulong) :
    ∀ (vs : List VarId), iv ∉ vs →
      varEnvMatchesLocals curEnv ls idxName idxVar vs →
      varEnvMatchesLocals (curEnv.bind iv (.u64 x)) ls idxName idxVar (vs ++ [iv])
  | [], _, _ => by
    have hbeq : (iv == idxVar) = false := beq_eq_false_iff_ne.mpr hivNe
    refine ⟨⟨x, VarEnv.bind_self curEnv iv (.u64 x), ?_, ?_⟩, trivial⟩
    · simp only [hbeq, Bool.false_eq_true, ite_false]; exact hlk
    · simp only [hbeq, Bool.false_eq_true, ite_false]; exact hty
  | u :: us, hnot, ⟨⟨xu, hu, hlku, htyu⟩, htl⟩ => by
    have hne : u ≠ iv := fun heq => hnot (heq ▸ .head us)
    have hnotTl : iv ∉ us := fun hm => hnot (.tail u hm)
    refine ⟨⟨xu, ?_, hlku, htyu⟩,
      varEnvMatchesLocals_append_one curEnv ls idxName idxVar iv x hivNe hlk hty us hnotTl htl⟩
    rw [VarEnv.bind_ne curEnv iv u (.u64 x) (beq_eq_false_iff_ne.mpr hne)]
    exact hu

private theorem bindCustomParInputs_props (env : VarEnv) (st : HeapState) (inputs : List VarId)
    (cx : Nat) (inWords : Nat → List (BitVec 64))
    (hread : ∀ j < inputs.length, ∃ (hc : cx < (inWords j).length) (x : UInt64),
      readParInput env st inputs j cx = .ok x ∧ (inWords j)[cx] = x.toBitVec) :
    ∀ (rem : List VarId) (k0 : Nat) (curEnv : VarEnv) (ls : MetalAst.MSLLocals)
      (idxVar : VarId) (prior : List VarId),
      k0 + rem.length = inputs.length →
      (idxVar :: (prior ++ rem)).Nodup →
      varEnvMatchesLocals curEnv ls "gid64" idxVar (idxVar :: prior) →
      (∀ m (hm : m < rem.length), ∃ (hc : cx < (inWords (k0 + m)).length),
        ls.lookup? s!"v{rem[m]'hm}" = some ((inWords (k0 + m))[cx]) ∧
        ls.lookupType? s!"v{rem[m]'hm}" = some .ulong) →
      ∃ kEnv : VarEnv,
        bindCustomParInputs env st inputs cx curEnv k0 rem = .ok kEnv ∧
        varEnvMatchesLocals kEnv ls "gid64" idxVar (idxVar :: (prior ++ rem))
  | [], _, curEnv, _, _, prior, _, _, hcur, _ => by
    simp only [List.append_nil, bindCustomParInputs]
    exact ⟨curEnv, rfl, hcur⟩
  | iv :: rest, k0, curEnv, ls, idxVar, prior, hklen, hnd, hcur, hrem => by
    simp only [List.length_cons] at hklen
    have hk0Lt : k0 < inputs.length := by omega
    rcases hread k0 hk0Lt with ⟨hc0, x0, hr0, hw0⟩
    rcases hrem 0 (by simp) with ⟨hc0', hlk0, hty0⟩
    simp only [Nat.add_zero, List.getElem_cons_zero] at hlk0 hty0
    rw [hw0] at hlk0
    have hndCons : idxVar ∉ prior ++ (iv :: rest) ∧ (prior ++ (iv :: rest)).Nodup :=
      List.nodup_cons.mp hnd
    have hivNeIdx : iv ≠ idxVar := fun heq =>
      hndCons.1 (heq ▸ List.mem_append_right prior (.head rest))
    have hivNotPrior : iv ∉ prior := by
      rcases List.nodup_append.mp hndCons.2 with ⟨_, _, hdisj⟩
      exact fun hm => hdisj iv hm iv (.head rest) rfl
    have hivNotHead : iv ∉ (idxVar :: prior) := by
      intro hm
      rcases List.mem_cons.mp hm with h1 | h2
      · exact hivNeIdx h1
      · exact hivNotPrior h2
    have hnextMatch := varEnvMatchesLocals_append_one curEnv ls "gid64" idxVar iv x0
      hivNeIdx hlk0 hty0 (idxVar :: prior) hivNotHead hcur
    simp only [List.cons_append] at hnextMatch
    have happEq : prior ++ (iv :: rest) = (prior ++ [iv]) ++ rest := by simp
    rw [happEq] at hnd ⊢
    have hremNext : ∀ m (hm : m < rest.length), ∃ (hc : cx < (inWords ((k0 + 1) + m)).length),
        ls.lookup? s!"v{rest[m]'hm}" = some ((inWords ((k0 + 1) + m))[cx]) ∧
        ls.lookupType? s!"v{rest[m]'hm}" = some .ulong := by
      intro m hm
      have hm1 : m + 1 < (iv :: rest).length := by simp; omega
      rcases hrem (m + 1) hm1 with ⟨hcm, hlkm, htym⟩
      have hadd : k0 + (m + 1) = (k0 + 1) + m := by omega
      simp only [List.getElem_cons_succ, hadd] at hcm hlkm htym
      exact ⟨hcm, hlkm, htym⟩
    obtain ⟨kEnv, hbindRest, hmatchFinal⟩ :=
      bindCustomParInputs_props env st inputs cx inWords hread rest (k0 + 1)
        (curEnv.bind iv (.u64 x0)) ls idxVar (prior ++ [iv]) (by omega) hnd hnextMatch hremNext
    refine ⟨kEnv, ?_, hmatchFinal⟩
    unfold bindCustomParInputs
    rw [hr0]
    exact hbindRest

private theorem evalParKernelLoop_of_all (env : VarEnv) (st : HeapState) (inputs : List VarId)
    (len : Nat) (k : ParallelKernelKind) (specU64 : Nat → UInt64) :
    ∀ (idxs : List Nat),
      (∀ i ∈ idxs, evalParKernelElem env st inputs len k i = .ok (specU64 i)) →
      ∃ elems : List UInt64,
        evalParKernelLoop env st inputs len k idxs = .ok elems ∧
        elems = idxs.map specU64
  | [], _ => ⟨[], rfl, rfl⟩
  | i :: is, hall => by
    have hi := hall i (.head is)
    obtain ⟨xs, hxs, hmap⟩ := evalParKernelLoop_of_all env st inputs len k specU64 is
      (fun j hj => hall j (.tail i hj))
    refine ⟨specU64 i :: xs, ?_, by simp [hmap]⟩
    unfold evalParKernelLoop
    rw [hi, hxs]

/-- End-to-end 1D SIMT lowering soundness (`LNIR.ParallelKernelKind` -> `MetalAst.MSLModule`):
for every well-formed `wfMetalKernel k` whose input array buffers are packed via
`packInputDeviceBuffers`, `LNIR.evalParKernelLoop` succeeds over `0 .. len - 1` and
`MetalAst.evalMSLKernel` on the lowered kernel in `lowerToMetal name k` terminates without
data races or undefined behavior, writing the exact 64-bit word `elems[i].toBitVec` at every
output element `i < len`. -/
theorem lowerToMetal_evalMSLKernel_sound
    (env : VarEnv) (st : HeapState) (inputs : List VarId)
    (name : String) (k : ParallelKernelKind)
    (len nGroups groupSize : Nat)
    (inBufs : List (Nat × MetalAst.ByteMemory))
    (hwf : wfMetalKernel k = true)
    (harity : inputs.length = kernelArity k)
    (hpack : packInputDeviceBuffers env st inputs len = some inBufs)
    (hlenCov : len ≤ nGroups * groupSize)
    (hgrid32 : nGroups * groupSize < 2 ^ 32) :
    ∃ (elems : List UInt64) (kern : MetalAst.MSLKernelDecl)
      (devBufsF : List (Nat × MetalAst.ByteMemory))
      (outMemF : MetalAst.ByteMemory),
      (lowerToMetal name k).kernels = [kern] ∧
      evalParKernelLoop env st inputs len k (List.range len) = .ok elems ∧
      elems.length = len ∧
      MetalAst.evalMSLKernel (groupStepsForKind groupSize k) kern
        { x := nGroups, y := 1, z := 1 } { x := groupSize, y := 1, z := 1 }
        (mkDeviceBuffers inBufs (kernelArity k) len)
        (mkConstLenBuffers (kernelArity k) len) [] [] = .ok devBufsF ∧
      devBufsF.lookup (kernelArity k) = some outMemF ∧
      (∀ (i : Nat) (hi : i < elems.length),
        outMemF.readU64Word? i = some (elems[i]'hi).toBitVec) := by
  have hlen64 : len * 8 ≤ 2 ^ 64 := by omega
  rcases packInputDeviceBuffersGo_props env st len inputs 0 inBufs hpack with ⟨_, hhi, hmid⟩
  have hinOutNone : inBufs.lookup (kernelArity k) = none := hhi (kernelArity k) (by omega)
  let inWords : Nat → List (BitVec 64) := fun j =>
    (List.range len).map fun i =>
      match readParInput env st inputs j i with
      | .ok x => x.toBitVec
      | .error _ => 0#64
  have hinWordsLen : ∀ j, (inWords j).length = len := fun _ => by simp [inWords]
  have hinLookup : ∀ j < kernelArity k,
      inBufs.lookup j = some (MetalAst.ByteMemory.ofU64Words (inWords j)) ∧
      (inWords j).length = len := by
    intro j hj
    rcases hmid j (by omega) with ⟨words, hlk, hwlen, hrd⟩
    simp only [Nat.zero_add] at hlk
    have heqW : words = inWords j := by
      apply List.ext_getElem (by simp [hwlen, inWords])
      intro i hi1 _
      rcases hrd i (by omega) hi1 with ⟨x, hrx, hwx⟩
      simp [inWords, hrx, hwx]
    rw [heqW] at hlk
    exact ⟨hlk, hinWordsLen j⟩
  have hreadElem : ∀ j < kernelArity k, ∀ i < len,
      ∃ (hc : i < (inWords j).length) (x : UInt64),
        readParInput env st inputs j i = .ok x ∧ (inWords j)[i]'hc = x.toBitVec := by
    intro j hj i hi
    rcases hmid j (by omega) with ⟨_, _, hwlen, hrd⟩
    rcases hrd i hi (by omega) with ⟨x, hrx, _⟩
    exact ⟨by simp [inWords, hi], x, hrx, by simp [inWords, hrx]⟩
  let specU64 : Nat → UInt64 := fun i =>
    match evalParKernelElem env st inputs len k i with
    | .ok v => v
    | .error _ => 0
  have ⟨stepsInner, inner, hparams, hshared, hbody, hfuel, hInner, helemAll⟩ :
      ∃ (stepsInner : Nat) (inner : List MetalAst.MSLStmt),
        (lowerKind name k).params = MetalAst.stdKernelParams (kernelArity k) ∧
        (lowerKind name k).sharedDecls = [] ∧
        (lowerKind name k).body =
          [MetalAst.MSLStmt.ifElse
            (.lt (.cast .ulong (.var "gid")) (.var "n"))
            (MetalAst.MSLBlock.ofList inner) .nil, .returnStmt] ∧
        groupSize * (stepsInner + 2) ≤ groupStepsForKind groupSize k ∧
        MetalAst.LaneInnerSpec (kernelArity k) len stepsInner inWords
          (fun i => (specU64 i).toBitVec) inner ∧
        (∀ i < len, evalParKernelElem env st inputs len k i = .ok (specU64 i)) := by
    cases k with
    | mapScaleAdd scale bias =>
      refine ⟨1, [storeOut (.add (.mul (elem "in0") (.immU64 scale.toBitVec)) (.immU64 bias.toBitVec))],
        rfl, rfl, rfl, by simp [groupStepsForKind]; omega, ?_, ?_⟩
      · refine MetalAst.laneInnerSpec_congr (MetalAst.laneInner_mapScaleAdd len scale.toBitVec bias.toBitVec inWords) ?_
        intro cx hcx
        rcases hreadElem 0 (by simp [kernelArity]) cx hcx with ⟨hc0, x, hrx, hwx⟩
        simp [specU64, evalParKernelElem, hrx, dite_eq_left_of_eq_true (eq_true hc0), hwx]
      · intro i hi
        rcases hreadElem 0 (by simp [kernelArity]) i hi with ⟨_, x, hrx, _⟩
        simp [specU64, evalParKernelElem, hrx]
    | zipAdd =>
      refine ⟨1, [storeOut (.add (elem "in0") (elem "in1"))],
        rfl, rfl, rfl, by simp [groupStepsForKind]; omega, ?_, ?_⟩
      · refine MetalAst.laneInnerSpec_congr (MetalAst.laneInner_zipAdd len inWords) ?_
        intro cx hcx
        rcases hreadElem 0 (by simp [kernelArity]) cx hcx with ⟨hc0, x, hrx, hwx⟩
        rcases hreadElem 1 (by simp [kernelArity]) cx hcx with ⟨hc1, y, hry, hwy⟩
        simp [specU64, evalParKernelElem, hrx, hry,
          dite_eq_left_of_eq_true (eq_true hc0), dite_eq_left_of_eq_true (eq_true hc1), hwx, hwy]
      · intro i hi
        rcases hreadElem 0 (by simp [kernelArity]) i hi with ⟨_, x, hrx, _⟩
        rcases hreadElem 1 (by simp [kernelArity]) i hi with ⟨_, y, hry, _⟩
        simp [specU64, evalParKernelElem, hrx, hry]
    | zipMul =>
      refine ⟨1, [storeOut (.mul (elem "in0") (elem "in1"))],
        rfl, rfl, rfl, by simp [groupStepsForKind]; omega, ?_, ?_⟩
      · refine MetalAst.laneInnerSpec_congr (MetalAst.laneInner_zipMul len inWords) ?_
        intro cx hcx
        rcases hreadElem 0 (by simp [kernelArity]) cx hcx with ⟨hc0, x, hrx, hwx⟩
        rcases hreadElem 1 (by simp [kernelArity]) cx hcx with ⟨hc1, y, hry, hwy⟩
        simp [specU64, evalParKernelElem, hrx, hry,
          dite_eq_left_of_eq_true (eq_true hc0), dite_eq_left_of_eq_true (eq_true hc1), hwx, hwy]
      · intro i hi
        rcases hreadElem 0 (by simp [kernelArity]) i hi with ⟨_, x, hrx, _⟩
        rcases hreadElem 1 (by simp [kernelArity]) i hi with ⟨_, y, hry, _⟩
        simp [specU64, evalParKernelElem, hrx, hry]
    | dotProduct =>
      refine ⟨1, [storeOut (.mul (elem "in0") (elem "in1"))],
        rfl, rfl, rfl, by simp [groupStepsForKind]; omega, ?_, ?_⟩
      · refine MetalAst.laneInnerSpec_congr (MetalAst.laneInner_zipMul len inWords) ?_
        intro cx hcx
        rcases hreadElem 0 (by simp [kernelArity]) cx hcx with ⟨hc0, x, hrx, hwx⟩
        rcases hreadElem 1 (by simp [kernelArity]) cx hcx with ⟨hc1, y, hry, hwy⟩
        simp [specU64, evalParKernelElem, hrx, hry,
          dite_eq_left_of_eq_true (eq_true hc0), dite_eq_left_of_eq_true (eq_true hc1), hwx, hwy]
      · intro i hi
        rcases hreadElem 0 (by simp [kernelArity]) i hi with ⟨_, x, hrx, _⟩
        rcases hreadElem 1 (by simp [kernelArity]) i hi with ⟨_, y, hry, _⟩
        simp [specU64, evalParKernelElem, hrx, hry]
    | saxpy alpha =>
      refine ⟨1, [storeOut (.add (.mul (.immU64 alpha.toBitVec) (elem "in0")) (elem "in1"))],
        rfl, rfl, rfl, by simp [groupStepsForKind]; omega, ?_, ?_⟩
      · refine MetalAst.laneInnerSpec_congr (MetalAst.laneInner_saxpy len alpha.toBitVec inWords) ?_
        intro cx hcx
        rcases hreadElem 0 (by simp [kernelArity]) cx hcx with ⟨hc0, x, hrx, hwx⟩
        rcases hreadElem 1 (by simp [kernelArity]) cx hcx with ⟨hc1, y, hry, hwy⟩
        simp [specU64, evalParKernelElem, hrx, hry,
          dite_eq_left_of_eq_true (eq_true hc0), dite_eq_left_of_eq_true (eq_true hc1), hwx, hwy]
      · intro i hi
        rcases hreadElem 0 (by simp [kernelArity]) i hi with ⟨_, x, hrx, _⟩
        rcases hreadElem 1 (by simp [kernelArity]) i hi with ⟨_, y, hry, _⟩
        simp [specU64, evalParKernelElem, hrx, hry]
    | stencil1D3Pt wL wC wR =>
      let ii := MetalAst.MSLExpr.cast .ulong (.var "gid")
      let edge := MetalAst.MSLExpr.logOr (.eq ii (u 0)) (.ge (.add ii (u 1)) (.var "n"))
      let center := elem "in0"
      let interior := MetalAst.MSLExpr.add (.add
        (.mul (.immU64 wL.toBitVec) (.index "in0" (.sub ii (u 1))))
        (.mul (.immU64 wC.toBitVec) center))
        (.mul (.immU64 wR.toBitVec) (.index "in0" (.add ii (u 1))))
      refine ⟨2, [.ifElse edge (.cons (storeOut center) .nil) (.cons (storeOut interior) .nil)],
        rfl, rfl, rfl, by simp [groupStepsForKind]; omega, ?_, ?_⟩
      · refine MetalAst.laneInnerSpec_congr
          (MetalAst.laneInner_stencil1D3Pt len wL.toBitVec wC.toBitVec wR.toBitVec inWords) ?_
        intro cx hcx
        rcases hreadElem 0 (by simp [kernelArity]) cx hcx with ⟨hcC, xC, hrC, hwC⟩
        cases hedge : (cx == 0 || decide (cx + 1 ≥ len))
        · have hcxPos : 0 < cx := by cases cx with | zero => simp at hedge | succ _ => omega
          have hcx1Lt : cx + 1 < len := by
            rcases Bool.or_eq_false_iff.mp hedge with ⟨_, h2⟩
            simp only [decide_eq_false_iff_not] at h2; omega
          rcases hreadElem 0 (by simp [kernelArity]) (cx - 1) (by omega) with ⟨hcL, xL, hrL, hwL⟩
          rcases hreadElem 0 (by simp [kernelArity]) (cx + 1) hcx1Lt with ⟨hcR, xR, hrR, hwR⟩
          simp only [specU64, evalParKernelElem, ge_iff_le] at hedge ⊢
          simp [hedge, hrL, hrC, hrR, dite_eq_left_of_eq_true (eq_true hcL),
            dite_eq_left_of_eq_true (eq_true hcC), dite_eq_left_of_eq_true (eq_true hcR), hwL, hwC, hwR]
        · simp only [specU64, evalParKernelElem, ge_iff_le] at hedge ⊢
          simp [hedge, hrC, dite_eq_left_of_eq_true (eq_true hcC), hwC]
      · intro i hi
        rcases hreadElem 0 (by simp [kernelArity]) i hi with ⟨_, xC, hrC, _⟩
        cases hedge : (i == 0 || decide (i + 1 ≥ len))
        · have hiPos : 0 < i := by cases i with | zero => simp at hedge | succ _ => omega
          have hi1Lt : i + 1 < len := by
            rcases Bool.or_eq_false_iff.mp hedge with ⟨_, h2⟩
            simp only [decide_eq_false_iff_not] at h2; omega
          rcases hreadElem 0 (by simp [kernelArity]) (i - 1) (by omega) with ⟨_, xL, hrL, _⟩
          rcases hreadElem 0 (by simp [kernelArity]) (i + 1) hi1Lt with ⟨_, xR, hrR, _⟩
          simp only [specU64, evalParKernelElem, ge_iff_le] at hedge ⊢
          simp [hedge, hrL, hrC, hrR]
        · simp only [specU64, evalParKernelElem, ge_iff_le] at hedge ⊢
          simp [hedge, hrC]
    | customScalar idxVar inVars body =>
      simp only [wfMetalKernel, Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_exists] at hwf
      rcases hwf with ⟨⟨hnodup, hnotMem⟩, ⟨s, hsort⟩⟩
      simp only [kernelArity] at harity hinLookup hreadElem hinOutNone ⊢
      have hndAll : (idxVar :: inVars).Nodup := List.nodup_cons.mpr ⟨hnotMem, hnodup⟩
      have hbindU64 : ∀ cx < len, ∃ kEnv : VarEnv,
          bindCustomParInputs env st inputs cx (env.bind idxVar (.u64 cx.toUInt64)) 0 inVars = .ok kEnv ∧
          (∀ id ∈ idxVar :: inVars, ∃ x : UInt64, kEnv id = some (.u64 x)) := by
        intro cx hcx
        have h32 : cx < 2 ^ 32 := by omega
        have haux : ∀ (rem : List VarId) (k0 : Nat) (cur : VarEnv),
            k0 + rem.length = inputs.length →
            ∃ kEnv, bindCustomParInputs env st inputs cx cur k0 rem = .ok kEnv ∧
              ∀ id, (∃ x, cur id = some (.u64 x)) ∨ id ∈ rem → ∃ x, kEnv id = some (.u64 x) := by
          intro rem
          induction rem with
          | nil =>
            intro k0 cur _
            refine ⟨cur, rfl, fun id hid => ?_⟩
            rcases hid with h1 | h2
            · exact h1
            · nomatch h2
          | cons iv rest ih =>
            intro k0 cur hk
            simp only [List.length_cons] at hk
            rcases hreadElem k0 (by omega) cx hcx with ⟨_, x0, hr0, _⟩
            obtain ⟨kEnv, hbRest, hall⟩ := ih (k0 + 1) (cur.bind iv (.u64 x0)) (by omega)
            refine ⟨kEnv, by unfold bindCustomParInputs; rw [hr0]; exact hbRest, fun id hid => hall id ?_⟩
            rcases hid with ⟨x, hx⟩ | hmem
            · by_cases heq : id = iv
              · subst heq; exact Or.inl ⟨x0, VarEnv.bind_self cur id (.u64 x0)⟩
              · exact Or.inl ⟨x, (VarEnv.bind_ne cur iv id (.u64 x0) (beq_eq_false_iff_ne.mpr heq)).trans hx⟩
            · rcases List.mem_cons.mp hmem with rfl | htl
              · exact Or.inl ⟨x0, VarEnv.bind_self cur id (.u64 x0)⟩
              · exact Or.inr htl
        obtain ⟨kEnv, hb, hall⟩ := haux inVars 0 (env.bind idxVar (.u64 cx.toUInt64)) (by omega)
        refine ⟨kEnv, hb, fun id hid => hall id ?_⟩
        rcases List.mem_cons.mp hid with rfl | htl
        · exact Or.inl ⟨cx.toUInt64, VarEnv.bind_self env id (.u64 cx.toUInt64)⟩
        · exact Or.inr htl
      let loads := (List.range inVars.length).map fun m =>
        MetalAst.MSLStmt.varDecl .ulong s!"v{inVars[m]?.getD 0}" (elem s!"in{m}")
      refine ⟨inVars.length + 2,
        [MetalAst.MSLStmt.varDecl .ulong "gid64" (.cast .ulong (.var "gid"))] ++
          loads ++ [storeOut (lowerScalar "gid64" idxVar body)],
        rfl, rfl, rfl,
        by dsimp [groupStepsForKind]
           exact Nat.le_trans (Nat.mul_le_mul_left groupSize (by omega)) (Nat.le_add_right _ 2), ?_, ?_⟩
      · apply MetalAst.laneInner_varDecls_storeOut inVars len inWords
          (fun i => (specU64 i).toBitVec) (lowerScalar "gid64" idxVar body) hnodup
        intro g tid ls cx hcxLen hcx32 hgidV hgidT hvars
        have hreadCx : ∀ j < inputs.length, ∃ (hc : cx < (inWords j).length) (x : UInt64),
            readParInput env st inputs j cx = .ok x ∧ (inWords j)[cx]'hc = x.toBitVec := by
          intro j hj; exact hreadElem j (by omega) cx hcxLen
        have hcur0 : varEnvMatchesLocals (env.bind idxVar (.u64 cx.toUInt64)) ls "gid64" idxVar [idxVar] := by
          refine ⟨⟨cx.toUInt64, VarEnv.bind_self env idxVar _, ?_, ?_⟩, trivial⟩
          · simp [MetalAst.u64_ofNat_toBitVec cx hcx32, hgidV]
          · simp [hgidT]
        have hrem0 : ∀ m (hm : m < inVars.length), ∃ (hc : cx < (inWords (0 + m)).length),
            ls.lookup? s!"v{inVars[m]'hm}" = some ((inWords (0 + m))[cx]'hc) ∧
            ls.lookupType? s!"v{inVars[m]'hm}" = some .ulong := by
          intro m hm
          have hc : cx < (inWords m).length := by rw [hinWordsLen]; exact hcxLen
          have ⟨hv, ht⟩ := hvars m hm hc
          simp only [Nat.zero_add]
          exact ⟨hc, hv, ht⟩
        obtain ⟨kEnv, hbind, hmatch⟩ := bindCustomParInputs_props env st inputs cx inWords hreadCx
          inVars 0 (env.bind idxVar (.u64 cx.toUInt64)) ls idxVar [] (by omega) hndAll hcur0 hrem0
        simp only [List.nil_append] at hmatch
        obtain ⟨val, bv, hevBody, hvs, hmsl⟩ :=
          lowerScalar_eval_sound MetalAst.kernelCallEval
            (MetalAst.effectiveCalleeFuel g) g tid ls g.epochLog
            kEnv "gid64" idxVar (idxVar :: inVars) body s hsort hmatch
        cases s with
        | false =>
          rcases valOfSort_false hvs with ⟨v, rfl, rfl⟩
          have hspec : specU64 cx = v := by simp [specU64, evalParKernelElem, hbind, hevBody]
          rw [hspec]; exact hmsl
        | true =>
          rcases valOfSort_true hvs with ⟨b, rfl, rfl⟩
          have hspec : specU64 cx = (if b then 1 else 0) := by simp [specU64, evalParKernelElem, hbind, hevBody]
          have hbv : (specU64 cx).toBitVec = (if b then 1#64 else 0#64) := by rw [hspec]; cases b <;> rfl
          rw [hbv]; exact hmsl
      · intro i hi
        obtain ⟨kEnv, hbind, henvK⟩ := hbindU64 i hi
        obtain ⟨val, bv, hevBody, hvs, _⟩ :=
          lowerScalar_eval_core MetalAst.kernelCallEval
            kEnv "gid64" idxVar (idxVar :: inVars) henvK body s hsort
        cases s with
        | false =>
          rcases valOfSort_false hvs with ⟨v, rfl, rfl⟩
          simp [specU64, evalParKernelElem, hbind, hevBody]
        | true =>
          rcases valOfSort_true hvs with ⟨b, rfl, rfl⟩
          simp [specU64, evalParKernelElem, hbind, hevBody]
  obtain ⟨elems, hloop, heqMap⟩ := evalParKernelLoop_of_all env st inputs len k specU64 (List.range len)
    (fun i hi => helemAll i (List.mem_range.mp hi))
  obtain ⟨devBufsF, outMemF, hmsl, houtF, hwords⟩ :=
    MetalAst.evalMSLKernel_guarded_1d
      (kernelArity k) len nGroups groupSize stepsInner (groupStepsForKind groupSize k)
      (lowerKind name k) inBufs inWords (fun i => (specU64 i).toBitVec) inner
      hparams hshared hbody hInner hlen64 hlenCov hgrid32 hfuel hinLookup hinOutNone
  refine ⟨elems, lowerKind name k, devBufsF, outMemF, rfl, hloop, by simp [heqMap], hmsl, houtF, ?_⟩
  intro i hi
  have hiLen : i < len := by simpa [heqMap] using hi
  have hget : elems[i]'hi = specU64 i := by subst heqMap; simp
  rw [hget]
  exact hwords i hiLen

end LeanNative.Proofs.MetalLowerProofs
