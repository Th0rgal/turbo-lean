import LeanNative.Proofs.MetalSIMT5

namespace LeanNative.Proofs.MetalSIMT

open LeanNative.Backend.MetalAst

private theorem bv_and_63_toNat (x : BitVec 64) : (x &&& 63#64).toNat = x.toNat % 64 := by
  rw [BitVec.toNat_and]
  have h63 : (63#64 : BitVec 64).toNat = 2 ^ 6 - 1 := rfl
  rw [h63, Nat.and_two_pow_sub_one_eq_mod]

private theorem bv_and_63_lt (x : BitVec 64) : (x &&& 63#64).toNat < 64 := by
  rw [bv_and_63_toNat]
  exact Nat.mod_lt x.toNat (by omega)

private theorem bv_and_63_eq_mod (x : BitVec 64) : (x &&& 63#64) = x % 64#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [bv_and_63_toNat, BitVec.toNat_umod]
  rfl

private theorem bv64_signBit_eq_msb_local (x : BitVec 64) :
    (((x >>> 63#64) &&& 1#64) != 0#64) = x.msb := by
  rw [BitVec.msb_eq_toNat]
  have hxlt : x.toNat < 2 ^ 64 := x.isLt
  have hsh : ((x >>> 63#64) &&& 1#64).toNat = (x.toNat / 2 ^ 63) &&& 1 := by
    rw [BitVec.toNat_and, BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rfl
  by_cases hge : 2 ^ 63 ≤ x.toNat
  · have hdiv : x.toNat / 2 ^ 63 = 1 := by omega
    have hval : (x >>> 63#64) &&& 1#64 = 1#64 := by
      apply BitVec.eq_of_toNat_eq; rw [hsh, hdiv]; rfl
    have hne : ((1#64 : BitVec 64) != 0#64) = true := bne_iff_ne.mpr fun hc => nomatch hc
    rw [hval, hne, decide_eq_true hge]
  · have hdiv : x.toNat / 2 ^ 63 = 0 := by omega
    have hval : (x >>> 63#64) &&& 1#64 = 0#64 := by
      apply BitVec.eq_of_toNat_eq; rw [hsh, hdiv]; rfl
    rw [hval, bne_self_eq_false, decide_eq_false hge]

theorem ev_div_guarded_ulong
    (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState)
    (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a = .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b = .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log
      (.select (.eq b (.immU64 0#64)) (.immU64 0#64) (.div a b)) =
      .ok { value := va / vb, fields := [], locals := ls, log := log } := by
  have hu0 : evalExprWithCall callEval fuel g tid ls log (.immU64 0#64) =
      .ok { value := 0#64, fields := [], locals := ls, log := log } := by
    rw [evalExprWithCall]
  have heq0 := ev_eq_ulong callEval fuel g tid ls log b (.immU64 0#64) vb 0#64 hb hu0 htb rfl
  cases hvb0 : (vb == 0#64)
  · exact (ev_select_false callEval fuel g tid ls log _ _ _ _ heq0 (by simp [hvb0])).trans
      (ev_div_ulong callEval fuel g tid ls log a b va vb ha hb hta htb hvb0)
  · have hv0 : vb = 0#64 := eq_of_beq hvb0
    subst hv0
    have hdiv0 : va / 0#64 = 0#64 := by apply BitVec.eq_of_toNat_eq; simp
    rw [hdiv0]
    exact (ev_select_true callEval fuel g tid ls log _ _ _ _ heq0 rfl).trans hu0

theorem ev_mod_guarded_ulong
    (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState)
    (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a = .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b = .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log
      (.select (.eq b (.immU64 0#64)) a (.rem a b)) =
      .ok { value := va % vb, fields := [], locals := ls, log := log } := by
  have hu0 : evalExprWithCall callEval fuel g tid ls log (.immU64 0#64) =
      .ok { value := 0#64, fields := [], locals := ls, log := log } := by
    rw [evalExprWithCall]
  have heq0 := ev_eq_ulong callEval fuel g tid ls log b (.immU64 0#64) vb 0#64 hb hu0 htb rfl
  cases hvb0 : (vb == 0#64)
  · exact (ev_select_false callEval fuel g tid ls log _ _ _ _ heq0 (by simp [hvb0])).trans
      (ev_rem_ulong callEval fuel g tid ls log a b va vb ha hb hta htb hvb0)
  · have hv0 : vb = 0#64 := eq_of_beq hvb0
    subst hv0
    have hmod0 : va % 0#64 = va := by apply BitVec.eq_of_toNat_eq; simp
    rw [hmod0]
    exact (ev_select_true callEval fuel g tid ls log _ _ _ _ heq0 rfl).trans ha

theorem ev_shl_masked_ulong
    (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState)
    (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a = .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b = .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log
      (.shl a (.bitAnd b (.immU64 63#64))) =
      .ok { value := va <<< (vb &&& 63#64).toNat, fields := [], locals := ls, log := log } := by
  have hu63 : evalExprWithCall callEval fuel g tid ls log (.immU64 63#64) =
      .ok { value := 63#64, fields := [], locals := ls, log := log } := by
    rw [evalExprWithCall]
  have hm := ev_bitand_ulong callEval fuel g tid ls log b (.immU64 63#64) vb 63#64 hb hu63 htb rfl
  exact ev_shl_ulong callEval fuel g tid ls log a _ va (vb &&& 63#64) ha hm hta (bv_and_63_lt vb)

theorem ev_shr_masked_ulong
    (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState)
    (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a = .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b = .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log
      (.shr a (.bitAnd b (.immU64 63#64))) =
      .ok { value := va >>> (vb &&& 63#64).toNat, fields := [], locals := ls, log := log } := by
  have hu63 : evalExprWithCall callEval fuel g tid ls log (.immU64 63#64) =
      .ok { value := 63#64, fields := [], locals := ls, log := log } := by
    rw [evalExprWithCall]
  have hm := ev_bitand_ulong callEval fuel g tid ls log b (.immU64 63#64) vb 63#64 hb hu63 htb rfl
  exact ev_shr_ulong callEval fuel g tid ls log a _ va (vb &&& 63#64) ha hm hta (bv_and_63_lt vb)

theorem ev_sar_masked_ulong
    (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState)
    (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a = .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b = .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log
      (.cast .ulong (.shr (.cast .long a) (.bitAnd b (.immU64 63#64)))) =
      .ok { value := BitVec.sshiftRight va (vb &&& 63#64).toNat, fields := [], locals := ls, log := log } := by
  have hu63 : evalExprWithCall callEval fuel g tid ls log (.immU64 63#64) =
      .ok { value := 63#64, fields := [], locals := ls, log := log } := by
    rw [evalExprWithCall]
  have hm := ev_bitand_ulong callEval fuel g tid ls log b (.immU64 63#64) vb 63#64 hb hu63 htb rfl
  have htm : inferExprType g ls (.bitAnd b (.immU64 63#64)) = .ulong := by
    change promoteMSLArithType (inferExprType g ls b) .ulong = .ulong
    rw [htb]
    rfl
  exact ev_sar_ulong callEval fuel g tid ls log a _ va (vb &&& 63#64) ha hm hta htm (bv_and_63_lt vb)

theorem ev_eor3_compound_ulong
    (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState)
    (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a = .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b = .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log
      (.bitXor (.bitXor a (.shr b (.immU64 32#64))) (.bitAnd b (.immU64 0xffffffff#64))) =
      .ok { value := (va ^^^ (vb >>> (32#64).toNat)) ^^^ (vb &&& 0xffffffff#64), fields := [], locals := ls, log := log } := by
  have hu32 : evalExprWithCall callEval fuel g tid ls log (.immU64 32#64) =
      .ok { value := 32#64, fields := [], locals := ls, log := log } := by
    rw [evalExprWithCall]
  have huff : evalExprWithCall callEval fuel g tid ls log (.immU64 0xffffffff#64) =
      .ok { value := 0xffffffff#64, fields := [], locals := ls, log := log } := by
    rw [evalExprWithCall]
  have hshr := ev_shr_ulong callEval fuel g tid ls log b (.immU64 32#64) vb 32#64 hb hu32 htb (by decide)
  have htshr : inferExprType g ls (.shr b (.immU64 32#64)) = .ulong := by
    change promoteMSLArithType (inferExprType g ls b) .ulong = .ulong
    rw [htb]
    rfl
  have hxor1 := ev_bitxor_ulong callEval fuel g tid ls log a _ va (vb >>> (32#64).toNat) ha hshr hta htshr
  have htxor1 : inferExprType g ls (.bitXor a (.shr b (.immU64 32#64))) = .ulong := by
    change promoteMSLArithType (inferExprType g ls a) (inferExprType g ls (.shr b (.immU64 32#64))) = .ulong
    rw [hta, htshr]
    rfl
  have hand := ev_bitand_ulong callEval fuel g tid ls log b (.immU64 0xffffffff#64) vb 0xffffffff#64 hb huff htb rfl
  have htand : inferExprType g ls (.bitAnd b (.immU64 0xffffffff#64)) = .ulong := by
    change promoteMSLArithType (inferExprType g ls b) .ulong = .ulong
    rw [htb]
    rfl
  exact ev_bitxor_ulong callEval fuel g tid ls log _ _ _ _ hxor1 hand htxor1 htand

theorem ev_eq_cast_ulong
    (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState)
    (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a = .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b = .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.cast .ulong (.eq a b)) =
      .ok { value := if va == vb then 1#64 else 0#64, fields := [], locals := ls, log := log } := by
  have hcmp := ev_eq_ulong callEval fuel g tid ls log a b va vb ha hb hta htb
  have hcast := ev_cast_ulong_from_bool callEval fuel g tid ls log (.eq a b) _ hcmp rfl
  cases h : (va == vb)
  · simp only [h] at hcast ⊢; exact hcast
  · simp only [h] at hcast ⊢; exact hcast

theorem ev_lt_cast_ulong
    (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState)
    (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a = .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b = .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.cast .ulong (.lt a b)) =
      .ok { value := if BitVec.ult va vb then 1#64 else 0#64, fields := [], locals := ls, log := log } := by
  have hcmp := ev_lt_ulong callEval fuel g tid ls log a b va vb ha hb hta htb
  have hcast := ev_cast_ulong_from_bool callEval fuel g tid ls log (.lt a b) _ hcmp rfl
  cases h : BitVec.ult va vb
  · simp only [h] at hcast ⊢; exact hcast
  · simp only [h] at hcast ⊢; exact hcast

theorem ev_le_cast_ulong
    (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState)
    (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a = .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b = .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.cast .ulong (.le a b)) =
      .ok { value := if BitVec.ule va vb then 1#64 else 0#64, fields := [], locals := ls, log := log } := by
  have hcmp := ev_le_ulong callEval fuel g tid ls log a b va vb ha hb hta htb
  have hcast := ev_cast_ulong_from_bool callEval fuel g tid ls log (.le a b) _ hcmp rfl
  cases h : BitVec.ule va vb
  · simp only [h] at hcast ⊢; exact hcast
  · simp only [h] at hcast ⊢; exact hcast



theorem ev_neg_zero_sub_ulong
    (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess)
    (a : MSLExpr) (va : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a = .ok { value := va, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.sub (.immU64 0#64) a) =
      .ok { value := 0#64 - va, fields := [], locals := ls, log := log } := by
  have hu0 : evalExprWithCall callEval fuel g tid ls log (.immU64 0#64) =
      .ok { value := 0#64, fields := [], locals := ls, log := log } := by
    rw [evalExprWithCall]
  exact ev_sub_ulong callEval fuel g tid ls log (.immU64 0#64) a 0#64 va hu0 ha rfl hta

theorem ev_fma_compound_ulong
    (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess)
    (a b c : MSLExpr) (va vb vc : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a = .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b = .ok { value := vb, fields := [], locals := ls, log := log })
    (hc : evalExprWithCall callEval fuel g tid ls log c = .ok { value := vc, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) (htc : inferExprType g ls c = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.add (.mul a b) c) =
      .ok { value := va * vb + vc, fields := [], locals := ls, log := log } := by
  have hmul := ev_mul_ulong callEval fuel g tid ls log a b va vb ha hb hta htb
  have htmul : inferExprType g ls (.mul a b) = .ulong := by
    change promoteMSLArithType (inferExprType g ls a) (inferExprType g ls b) = .ulong
    rw [hta, htb]; rfl
  exact ev_add_ulong callEval fuel g tid ls log (.mul a b) c (va * vb) vc hmul hc htmul htc

theorem ev_select_ne_zero
    (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess)
    (c t f : MSLExpr) (vc vt vf : BitVec 64)
    (hc : evalExprWithCall callEval fuel g tid ls log c = .ok { value := vc, fields := [], locals := ls, log := log })
    (ht : evalExprWithCall callEval fuel g tid ls log t = .ok { value := vt, fields := [], locals := ls, log := log })
    (hf : evalExprWithCall callEval fuel g tid ls log f = .ok { value := vf, fields := [], locals := ls, log := log })
    (htc : inferExprType g ls c = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.select (.ne c (.immU64 0#64)) t f) =
      .ok { value := if vc != 0#64 then vt else vf, fields := [], locals := ls, log := log } := by
  have hu0 : evalExprWithCall callEval fuel g tid ls log (.immU64 0#64) =
      .ok { value := 0#64, fields := [], locals := ls, log := log } := by
    rw [evalExprWithCall]
  have hne0 := ev_ne_ulong callEval fuel g tid ls log c (.immU64 0#64) vc 0#64 hc hu0 htc rfl
  cases hnz : (vc != 0#64)
  · simp only [Bool.false_eq_true, ite_false]
    exact (ev_select_false callEval fuel g tid ls log _ t f _ hne0 (by simp [hnz])).trans hf
  · simp only [ite_true]
    exact (ev_select_true callEval fuel g tid ls log _ t f _ hne0 (by simp [hnz])).trans ht

theorem infer_bin_ulong (g : MSLGroupState) (ls : MSLLocals) (a b : MSLExpr)
    (ha : inferExprType g ls a = .ulong) (hb : inferExprType g ls b = .ulong) :
    inferExprType g ls (.add a b) = .ulong ∧
    inferExprType g ls (.sub a b) = .ulong ∧
    inferExprType g ls (.mul a b) = .ulong ∧
    inferExprType g ls (.div a b) = .ulong ∧
    inferExprType g ls (.rem a b) = .ulong ∧
    inferExprType g ls (.bitAnd a b) = .ulong ∧
    inferExprType g ls (.bitOr a b) = .ulong ∧
    inferExprType g ls (.bitXor a b) = .ulong ∧
    inferExprType g ls (.shl a b) = .ulong ∧
    inferExprType g ls (.shr a b) = .ulong := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    change promoteMSLArithType (inferExprType g ls a) (inferExprType g ls b) = .ulong
    rw [ha, hb]
    rfl

theorem infer_select_ulong (g : MSLGroupState) (ls : MSLLocals) (c t f : MSLExpr)
    (ht : inferExprType g ls t = .ulong) :
    inferExprType g ls (.select c t f) = .ulong := ht



theorem shl_bv_eq_u64 (a b : UInt64) :
    a.toBitVec <<< (b.toBitVec &&& 63#64).toNat = (a <<< b).toBitVec := by
  have h : (a <<< b).toBitVec = a.toBitVec <<< (b.toBitVec % 64#64) := rfl
  rw [h, ← BitVec.shiftLeft_eq', ← bv_and_63_eq_mod]

theorem shr_bv_eq_u64 (a b : UInt64) :
    a.toBitVec >>> (b.toBitVec &&& 63#64).toNat = (a >>> b).toBitVec := by
  have h : (a >>> b).toBitVec = a.toBitVec >>> (b.toBitVec % 64#64) := rfl
  rw [h, ← BitVec.ushiftRight_eq', ← bv_and_63_eq_mod]

theorem sar_bv_eq_u64 (x y : UInt64) :
    BitVec.sshiftRight x.toBitVec (y.toBitVec &&& 63#64).toNat =
      (let sh := y &&& 63
       let signBit := (x >>> 63) &&& 1
       let shifted := x >>> sh
       if signBit != 0 && sh != 0 then shifted ||| (0xffffffffffffffff <<< (64 - sh)) else shifted).toBitVec := by
  let s := (y.toBitVec &&& 63#64).toNat
  have hs_def : s = (y.toBitVec &&& 63#64).toNat := rfl
  rw [← hs_def]
  dsimp only
  have hs_lt : s < 64 := bv_and_63_lt y.toBitVec
  have hsh_bv : (y &&& 63).toBitVec = y.toBitVec &&& 63#64 := rfl
  have hsh_nz : ((y &&& 63) != 0) = decide (s ≠ 0) := by
    by_cases hsz : s = 0
    · have hbv_z : (y &&& 63) = 0 := by
        apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
        simpa [hsh_bv, ← hs_def] using hsz
      simp [hbv_z, hsz]
    · have hbv_nz : (y &&& 63) ≠ 0 := by
        intro hz; apply hsz
        have : (y &&& 63).toBitVec.toNat = 0 := by simp [hz]
        simpa [hsh_bv, ← hs_def] using this
      simp [hbv_nz, hsz]
  have hsign : (((x >>> 63) &&& 1) != 0) = x.toBitVec.msb := by
    have hsb : (((x >>> 63) &&& 1) != 0) = (((x.toBitVec >>> 63#64) &&& 1#64) != 0#64) := rfl
    rw [hsb, bv64_signBit_eq_msb_local]
  have hshift_eq : (x >>> (y &&& 63)).toBitVec = x.toBitVec >>> s := by
    have hmod : (y &&& 63).toBitVec % 64#64 = y.toBitVec &&& 63#64 := by
      rw [hsh_bv, ← bv_and_63_eq_mod]
      apply BitVec.eq_of_toNat_eq
      rw [bv_and_63_toNat, bv_and_63_toNat, Nat.mod_mod]
    change x.toBitVec >>> ((y &&& 63).toBitVec % 64#64) = x.toBitVec >>> s
    rw [hmod, BitVec.ushiftRight_eq', ← hs_def]
  rw [hsign, hsh_nz]
  cases hmsb : x.toBitVec.msb
  · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, hshift_eq]
    ext i hi
    rw [BitVec.getElem_sshiftRight, BitVec.getElem_ushiftRight, hmsb]
    by_cases hsi : s + i < 64
    · simp [hsi, BitVec.getLsbD_eq_getElem]
    · simp [hsi, BitVec.getLsbD_of_ge x.toBitVec (s + i) (by omega)]
  · cases Nat.eq_zero_or_pos s with
    | inl hsz =>
      simp only [hsz, ne_eq, not_true_eq_false, decide_false, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte, hshift_eq]
      ext i hi
      rw [BitVec.getElem_sshiftRight, BitVec.getElem_ushiftRight, hmsb]
      simp [hi, BitVec.getLsbD_eq_getElem]
    | inr hsp =>
      have hsne : decide (s ≠ 0) = true := decide_eq_true (by omega)
      simp only [Bool.true_and, hsne, ↓reduceIte]
      have hall : (0xffffffffffffffff : UInt64).toBitVec = BitVec.allOnes 64 := by
        apply BitVec.eq_of_toNat_eq; rfl
      have hsub_mod : ((64 - (y &&& 63)).toBitVec % 64#64).toNat = 64 - s := by
        have h64s : (64 - (y &&& 63)).toBitVec.toNat = 64 - s := by
          change ((64#64 : BitVec 64) - (y &&& 63).toBitVec).toNat = 64 - s
          rw [hsh_bv, BitVec.toNat_sub_of_le]
          · change 64 - s = 64 - s; rfl
          · rw [BitVec.le_def]; change s ≤ 64; omega
        rw [BitVec.toNat_umod, h64s]
        change (64 - s) % 64 = 64 - s
        exact Nat.mod_eq_of_lt (by omega)
      have hmask : ((0xffffffffffffffff : UInt64) <<< (64 - (y &&& 63))).toBitVec =
          (BitVec.allOnes 64) <<< (64 - s) := by
        change (0xffffffffffffffff : UInt64).toBitVec <<< ((64 - (y &&& 63)).toBitVec % 64#64) = _
        rw [hall, BitVec.shiftLeft_eq', hsub_mod]
      change x.toBitVec.sshiftRight s =
        ((x >>> (y &&& 63)).toBitVec) ||| ((0xffffffffffffffff : UInt64) <<< (64 - (y &&& 63))).toBitVec
      rw [hshift_eq, hmask]
      ext i hi
      rw [BitVec.getElem_sshiftRight, hmsb, BitVec.getElem_or, BitVec.getElem_ushiftRight,
        BitVec.getElem_shiftLeft]
      by_cases hsi : s + i < 64
      · have hlt_sub : i < 64 - s := by omega
        simp [hsi, hlt_sub, BitVec.getLsbD_eq_getElem]
      · have hge_sub : ¬(i < 64 - s) := by omega
        simp only [hsi, ↓reduceDIte, hge_sub]
        rw [BitVec.getElem_allOnes]
        simp

theorem eq_bv_iff (x y : UInt64) : (x.toBitVec == y.toBitVec) = (x == y) := by
  cases h : (x == y)
  · cases h2 : (x.toBitVec == y.toBitVec)
    · rfl
    · rw [UInt64.eq_of_toBitVec_eq (eq_of_beq h2), beq_self_eq_true] at h; cases h
  · rw [eq_of_beq h]; simp

theorem u64_ofNat_toBitVec (cx : Nat) (h : cx < 2 ^ 32) :
    cx.toUInt64.toBitVec = BitVec.ofNat 64 cx := by
  have h64 : cx < 2 ^ 64 := by omega
  apply BitVec.eq_of_toNat_eq
  simp [UInt64.toNat_ofNat', Nat.mod_eq_of_lt h64]

theorem laneInnerSpec_congr {nIn len stepsInner : Nat}
    {inWords : Nat → List (BitVec 64)} {sw1 sw2 : Nat → BitVec 64}
    {inner : List MSLStmt}
    (hspec : LaneInnerSpec nIn len stepsInner inWords sw1 inner)
    (heq : ∀ cx < len, sw1 cx = sw2 cx) :
    LaneInnerSpec nIn len stepsInner inWords sw2 inner := by
  intro g done todo cx tx lo f outMem hcxLen hcx32 hlen64 hlo hf
    hstr hfn hbind hconst hin hout hsize hlog hdone hthreads
  obtain ⟨f', thH, g', outMem', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
    hspec g done todo cx tx lo f outMem hcxLen hcx32 hlen64 hlo hf
      hstr hfn hbind hconst hin hout hsize hlog hdone hthreads
  rw [heq cx hcxLen] at h12
  exact ⟨f', thH, g', outMem', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩


theorem eor3_bv_eq_u64 (a b : UInt64) :
    (a.toBitVec ^^^ (b.toBitVec >>> (32#64).toNat)) ^^^ (b.toBitVec &&& 0xffffffff#64) =
      ((a ^^^ (b >>> 32)) ^^^ (b &&& 0xffffffff)).toBitVec := by
  have h : ((a ^^^ (b >>> 32)) ^^^ (b &&& 0xffffffff)).toBitVec =
      (a.toBitVec ^^^ (b.toBitVec >>> 32#64)) ^^^ (b.toBitVec &&& 0xffffffff#64) := rfl
  rw [h, ← BitVec.ushiftRight_eq']


theorem bne_zero_bv_iff (x : UInt64) : (x.toBitVec != 0#64) = (x != 0) := by
  cases h : (x != 0)
  · have hx0 : x = 0 := by simpa [bne_iff_ne] using h
    subst hx0; rfl
  · cases h2 : (x.toBitVec != 0#64)
    · have hx0 : x = 0 := UInt64.eq_of_toBitVec_eq (by simpa [bne_iff_ne] using h2)
      subst hx0; cases h
    · rfl

theorem bool_bv_beq (bl br : Bool) :
    ((if bl then (1#64 : BitVec 64) else 0#64) == (if br then 1#64 else 0#64)) = (bl == br) := by
  cases bl
  · cases br <;> rfl
  · cases br <;> rfl


end LeanNative.Proofs.MetalSIMT
