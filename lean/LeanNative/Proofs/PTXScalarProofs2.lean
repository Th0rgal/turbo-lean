import LeanNative.Proofs.PTXScalarProofs

/-!
# PTX 8.0 Scalar Expression Execution Soundness (`LeanNative.Proofs.PTXScalarProofs2`)

Proves end-to-end SIMT execution equivalence between `Semantics.evalScalarExpr` and
`PTXLower.lowerScalar` (`0 sorryAx`, `0 ofReduceBool`).
-/

namespace LeanNative.Proofs.PTXScalarProofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend
open LeanNative.Backend.PTXAst
open LeanNative.Proofs.PTXSIMT
open LeanNative.Backend.PTXLower
open LeanNative.Proofs

private theorem exec_tail_arith (op : BinOp) {nP nR nRd di li ri : Nat}
    (hdi : di < nRd) (hli : li < di) (hri : ri < di)
    (xl xr : UInt64) (rf : PTXRegFile)
    (hll : rf.regs.lookup s!"%rd{li}" = some (.scalar xl.toBitVec))
    (hlr : rf.regs.lookup s!"%rd{ri}" = some (.scalar xr.toBitVec))
    (hop : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .bitAnd ∨ op = .bitOr ∨ op = .bitXor) :
    ∃ (y : UInt64) (rf' : PTXRegFile) (inst : PTXInstr),
      evalBinOp op (.u64 xl) (.u64 xr) = .ok (.u64 y) ∧
      (match op with
       | .add => inst = .add .none .u64 s!"%rd{di}" (.reg s!"%rd{li}") (.reg s!"%rd{ri}")
       | .sub => inst = .sub .u64 s!"%rd{di}" (.reg s!"%rd{li}") (.reg s!"%rd{ri}")
       | .mul => inst = .mul .lo .u64 s!"%rd{di}" (.reg s!"%rd{li}") (.reg s!"%rd{ri}")
       | .bitAnd => inst = .bitAnd .b64 s!"%rd{di}" (.reg s!"%rd{li}") (.reg s!"%rd{ri}")
       | .bitOr => inst = .bitOr .b64 s!"%rd{di}" (.reg s!"%rd{li}") (.reg s!"%rd{ri}")
       | _ => inst = .bitXor .b64 s!"%rd{di}" (.reg s!"%rd{li}") (.reg s!"%rd{ri}")) ∧
      RegFramePres di rf rf' ∧
      rf'.regs.lookup s!"%rd{di}" = some (.scalar y.toBitVec) ∧
      PureExec [ins inst] nP nR nRd rf rf' := by
  have hliR : li < nRd := by omega
  have hriR : ri < nRd := by omega
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨xl + xr, rf.setScalarRaw s!"%rd{di}" (xl + xr).toBitVec, _, rfl, rfl,
      regFrame_setRd rf (Nat.le_refl _) _, lookup_rd_self rf di _,
      pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => ?_⟩
    have hex := exec_add_rd s c t hrt di li ri hdi hliR hriR xl.toBitVec xr.toBitVec
      (by rw [hrf]; exact hll) (by rw [hrf]; exact hlr)
    rw [hrf] at hex; exact hex
  · refine ⟨xl - xr, rf.setScalarRaw s!"%rd{di}" (xl - xr).toBitVec, _, rfl, rfl,
      regFrame_setRd rf (Nat.le_refl _) _, lookup_rd_self rf di _,
      pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => ?_⟩
    have hex := exec_sub_rd s c t hrt di li ri hdi hliR hriR xl.toBitVec xr.toBitVec
      (by rw [hrf]; exact hll) (by rw [hrf]; exact hlr)
    rw [hrf] at hex; exact hex
  · refine ⟨xl * xr, rf.setScalarRaw s!"%rd{di}" (xl * xr).toBitVec, _, rfl, rfl,
      regFrame_setRd rf (Nat.le_refl _) _, lookup_rd_self rf di _,
      pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => ?_⟩
    have hex := exec_mul_lo_rd s c t hrt di li ri hdi hliR hriR xl.toBitVec xr.toBitVec
      (by rw [hrf]; exact hll) (by rw [hrf]; exact hlr)
    rw [hrf] at hex; exact hex
  · refine ⟨xl &&& xr, rf.setScalarRaw s!"%rd{di}" (xl &&& xr).toBitVec, _, rfl, rfl,
      regFrame_setRd rf (Nat.le_refl _) _, lookup_rd_self rf di _,
      pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => ?_⟩
    have hex := exec_bitAnd_rd s c t hrt di li ri hdi hliR hriR xl.toBitVec xr.toBitVec
      (by rw [hrf]; exact hll) (by rw [hrf]; exact hlr)
    rw [hrf] at hex; exact hex
  · refine ⟨xl ||| xr, rf.setScalarRaw s!"%rd{di}" (xl ||| xr).toBitVec, _, rfl, rfl,
      regFrame_setRd rf (Nat.le_refl _) _, lookup_rd_self rf di _,
      pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => ?_⟩
    have hex := exec_bitOr_rd s c t hrt di li ri hdi hliR hriR xl.toBitVec xr.toBitVec
      (by rw [hrf]; exact hll) (by rw [hrf]; exact hlr)
    rw [hrf] at hex; exact hex
  · refine ⟨xl ^^^ xr, rf.setScalarRaw s!"%rd{di}" (xl ^^^ xr).toBitVec, _, rfl, rfl,
      regFrame_setRd rf (Nat.le_refl _) _, lookup_rd_self rf di _,
      pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => ?_⟩
    have hex := exec_bitXor_rd s c t hrt di li ri hdi hliR hriR xl.toBitVec xr.toBitVec
      (by rw [hrf]; exact hll) (by rw [hrf]; exact hlr)
    rw [hrf] at hex; exact hex

private theorem exec_tail_select {nP nR nRd di ci ti fi pi : Nat}
    (hdi : di < nRd) (hci : ci < di) (hti : ti < di) (hfi : fi < di) (hpi : pi < nP)
    (vc vt vf : BitVec 64) (rf : PTXRegFile)
    (hlc : rf.regs.lookup s!"%rd{ci}" = some (.scalar vc))
    (hlt : rf.regs.lookup s!"%rd{ti}" = some (.scalar vt))
    (hlf : rf.regs.lookup s!"%rd{fi}" = some (.scalar vf)) :
    ∃ rf' : PTXRegFile,
      RegFramePres di rf rf' ∧
      rf'.regs.lookup s!"%rd{di}" = some (.scalar (if vc != 0#64 then vt else vf)) ∧
      PureExec [
        ins (.setp .ne .u64 s!"%p{pi}" (.reg s!"%rd{ci}") (i64 0)),
        ins (.selp .u64 s!"%rd{di}" (.reg s!"%rd{ti}") (.reg s!"%rd{fi}") s!"%p{pi}")
      ] nP nR nRd rf rf' := by
  let flag := vc != 0#64
  let rf1 := rf.setPredRaw s!"%p{pi}" flag
  let rf2 := rf1.setScalarRaw s!"%rd{di}" (if flag then vt else vf)
  have hf1 : RegFramePres di rf rf1 := regFrame_setP rf di pi flag
  have hf2 : RegFramePres di rf1 rf2 := regFrame_setRd rf1 (Nat.le_refl _) _
  have hs1 : PureExec [ins (.setp .ne .u64 s!"%p{pi}" (.reg s!"%rd{ci}") (i64 0))] nP nR nRd rf rf1 :=
    pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => by
      have hex := exec_setp_imm s c t hrt .ne pi ci hpi (by omega) vc 0#64 (by rw [hrf]; exact hlc)
      rw [hrf] at hex; exact hex
  have hs2 : PureExec [ins (.selp .u64 s!"%rd{di}" (.reg s!"%rd{ti}") (.reg s!"%rd{fi}") s!"%p{pi}")]
      nP nR nRd rf1 rf2 :=
    pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => by
      have hex := exec_selp_rd s c t hrt di ti fi pi hdi (by omega) (by omega) hpi vt vf flag
        (by rw [hrf]; exact (hf1.rd_eq ti hti).trans hlt)
        (by rw [hrf]; exact (hf1.rd_eq fi hfi).trans hlf)
        (by rw [hrf]; exact lookup_p_self rf pi flag)
      rw [hrf] at hex; exact hex
  exact ⟨rf2, regFrame_trans hf1 hf2 (Nat.le_refl _), lookup_rd_self rf1 di _, pureExec_append hs1 hf1 hs2⟩

theorem lowerScalar_eval_sound (env : VarEnv) (varOf : Nat → Option PReg) (boundVars : List Nat)
    (henv : ∀ id ∈ boundVars, ∃ (k : Nat) (x : UInt64), varOf id = some (.rd k) ∧ env id = some (.u64 x))
    (expr : ScalarExpr) (s : Bool) (hsort : inferScalarSort boundVars expr = some s) :
    ∃ (val : Val) (bv : BitVec 64),
      evalScalarExpr env expr = .ok val ∧
      valOfSort s val = some bv ∧
      ∀ (e0 : PEnv) (nP nR nRd : Nat) (rf : PTXRegFile),
        varEnvMatchesPTX env varOf boundVars e0.nextRd rf →
        let out := lowerScalar varOf e0 expr
        out.2.2.nextRd ≤ nRd →
        out.2.2.nextR ≤ nR →
        out.2.2.nextP ≤ nP →
        ∃ (di : Nat) (rf' : PTXRegFile),
          out.2.1 = .rd di ∧
          di < out.2.2.nextRd ∧
          RegFramePres e0.nextRd rf rf' ∧
          rf'.regs.lookup s!"%rd{di}" = some (.scalar bv) ∧
          PureExec out.1 nP nR nRd rf rf' := by
  induction expr generalizing s with
  | constU64 v =>
    rcases hsort with ⟨rfl⟩
    refine ⟨.u64 v, v.toBitVec, rfl, rfl, fun e0 nP nR nRd rf _ hrd _ _ => ?_⟩
    dsimp only [lowerScalar, freshRd] at hrd ⊢
    refine ⟨e0.nextRd, rf.setScalarRaw s!"%rd{e0.nextRd}" v.toBitVec, rfl, by omega,
      regFrame_setRd rf (Nat.le_refl _) _, lookup_rd_self rf e0.nextRd _,
      pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => ?_⟩
    have hex := exec_mov_imm s c t hrt e0.nextRd (by omega) v.toBitVec
    rw [hrf] at hex; exact hex
  | constBool b =>
    rcases hsort with ⟨rfl⟩
    refine ⟨.bool b, if b then 1#64 else 0#64, rfl, rfl, fun e0 nP nR nRd rf _ hrd _ _ => ?_⟩
    dsimp only [lowerScalar, freshRd] at hrd ⊢
    have hbv : BitVec.ofNat 64 (if b then 1 else 0) = (if b then 1#64 else 0#64) := by cases b <;> rfl
    refine ⟨e0.nextRd, rf.setScalarRaw s!"%rd{e0.nextRd}" (if b then 1#64 else 0#64), rfl, by omega,
      regFrame_setRd rf (Nat.le_refl _) _, lookup_rd_self rf e0.nextRd _,
      pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => ?_⟩
    have hex := exec_mov_imm s c t hrt e0.nextRd (by omega) (BitVec.ofNat 64 (if b then 1 else 0))
    have hrf' : rf.setScalarRaw s!"%rd{e0.nextRd}" (BitVec.ofNat 64 (if b then 1 else 0)) =
        rf.setScalarRaw s!"%rd{e0.nextRd}" (if b then 1#64 else 0#64) := by rw [hbv]
    rw [hrf, hrf'] at hex; exact hex
  | var id =>
    simp only [inferScalarSort] at hsort
    split at hsort
    · rename_i hmem
      rcases hsort with ⟨rfl⟩
      rcases henv id hmem with ⟨k0, x0, hvk0, hex0⟩
      refine ⟨.u64 x0, x0.toBitVec, by simp [evalScalarExpr, hex0], rfl,
        fun e0 nP nR nRd rf hm _ _ _ => ?_⟩
      rcases hm id hmem with ⟨k, x, hk, hvk, hex, hlk⟩
      obtain ⟨rfl⟩ : PReg.rd k = PReg.rd k0 := Option.some.inj (hvk.symm.trans hvk0)
      obtain ⟨rfl⟩ : Val.u64 x = Val.u64 x0 := Option.some.inj (hex.symm.trans hex0)
      simp only [lowerScalar, hvk]
      exact ⟨k0, rf, rfl, hk, regFrame_refl e0.nextRd rf, hlk, pureExec_nil nP nR nRd rf⟩
    · cases hsort
  | unaryOp op a iha =>
    simp only [inferScalarSort] at hsort
    cases hsa : inferScalarSort boundVars a <;> simp only [hsa] at hsort
    · cases hsort
    · rename_i sa
      cases sa <;> simp at hsort
      rcases iha false hsa with ⟨va, bva, heva, hva, ihaEx⟩
      rcases valOfSort_false hva with ⟨xa, rfl, rfl⟩
      cases op with
      | clz256 => cases hsort
      | not =>
        rcases hsort with ⟨rfl⟩
        refine ⟨.u64 (~~~xa), (~~~xa).toBitVec, by simp [evalScalarExpr, heva, evalUnaryOp], rfl,
          fun e0 nP nR nRd rf hm hrd hr hp => ?_⟩
        have hvar0 : ∀ id ∈ boundVars, ∃ k < e0.nextRd, varOf id = some (.rd k) := by
          intro id hid; rcases hm id hid with ⟨k, _, hk, hv, _, _⟩; exact ⟨k, hk, hv⟩
        have hbA := lowerScalar_bounds_no_label varOf boundVars e0 a false hsa hvar0
        rcases hA : lowerScalar varOf e0 a with ⟨al, ar, e1⟩; simp only [hA] at hbA
        simp only [lowerScalar, hA, freshRd] at hrd hr hp ⊢
        have hrdA : (lowerScalar varOf e0 a).2.2.nextRd ≤ nRd := by simp only [hA]; omega
        have hrA : (lowerScalar varOf e0 a).2.2.nextR ≤ nR := by simp only [hA]; omega
        have hpA : (lowerScalar varOf e0 a).2.2.nextP ≤ nP := by simp only [hA]; omega
        rcases ihaEx e0 nP nR nRd rf hm hrdA hrA hpA with ⟨ai, rf1, har, hai, hf1, hla, hex1⟩
        simp only [hA] at har hai hex1; subst har
        let rf2 := rf1.setScalarRaw s!"%rd{e1.nextRd}" (~~~xa).toBitVec
        have hf2 : RegFramePres e1.nextRd rf1 rf2 := regFrame_setRd rf1 (Nat.le_refl _) _
        have hs2 : PureExec [ins (.bitNot .b64 s!"%rd{e1.nextRd}" (.reg s!"%rd{ai}"))] nP nR nRd rf1 rf2 :=
          pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => by
            have hex := exec_bitNot_rd s c t hrt e1.nextRd ai (by omega) (by omega) xa.toBitVec
              (by rw [hrf]; exact hla)
            rw [hrf] at hex; exact hex
        exact ⟨e1.nextRd, rf2, rfl, by omega, regFrame_trans hf1 hf2 hbA.1,
          lookup_rd_self rf1 e1.nextRd _, pureExec_append hex1 hf1 hs2⟩
      | neg =>
        rcases hsort with ⟨rfl⟩
        refine ⟨.u64 (0 - xa), (0 - xa).toBitVec, by simp [evalScalarExpr, heva, evalUnaryOp], rfl,
          fun e0 nP nR nRd rf hm hrd hr hp => ?_⟩
        have hvar0 : ∀ id ∈ boundVars, ∃ k < e0.nextRd, varOf id = some (.rd k) := by
          intro id hid; rcases hm id hid with ⟨k, _, hk, hv, _, _⟩; exact ⟨k, hk, hv⟩
        have hbA := lowerScalar_bounds_no_label varOf boundVars e0 a false hsa hvar0
        rcases hA : lowerScalar varOf e0 a with ⟨al, ar, e1⟩; simp only [hA] at hbA
        simp only [lowerScalar, hA, freshRd] at hrd hr hp ⊢
        have hrdA : (lowerScalar varOf e0 a).2.2.nextRd ≤ nRd := by simp only [hA]; omega
        have hrA : (lowerScalar varOf e0 a).2.2.nextR ≤ nR := by simp only [hA]; omega
        have hpA : (lowerScalar varOf e0 a).2.2.nextP ≤ nP := by simp only [hA]; omega
        rcases ihaEx e0 nP nR nRd rf hm hrdA hrA hpA with ⟨ai, rf1, har, hai, hf1, hla, hex1⟩
        simp only [hA] at har hai hex1; subst har
        let rf2 := rf1.setScalarRaw s!"%rd{e1.nextRd}" (0 - xa).toBitVec
        have hf2 : RegFramePres e1.nextRd rf1 rf2 := regFrame_setRd rf1 (Nat.le_refl _) _
        have hs2 : PureExec [ins (.neg .s64 s!"%rd{e1.nextRd}" (.reg s!"%rd{ai}"))] nP nR nRd rf1 rf2 :=
          pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => by
            have hex := exec_neg_rd s c t hrt e1.nextRd ai (by omega) (by omega) xa.toBitVec
              (by rw [hrf]; exact hla)
            rw [hrf] at hex; exact hex
        exact ⟨e1.nextRd, rf2, rfl, by omega, regFrame_trans hf1 hf2 hbA.1,
          lookup_rd_self rf1 e1.nextRd _, pureExec_append hex1 hf1 hs2⟩
  | fma a b c iha ihb ihc =>
    simp only [inferScalarSort] at hsort
    cases hsa : inferScalarSort boundVars a <;> simp only [hsa] at hsort
    · cases hsort
    · cases hsb : inferScalarSort boundVars b <;> simp only [hsb] at hsort
      · cases hsort
      · cases hsc : inferScalarSort boundVars c <;> simp only [hsc] at hsort
        · cases hsort
        · rename_i sa sb sc
          cases sa <;> simp at hsort
          cases sb <;> simp at hsort
          cases sc <;> simp at hsort
          subst hsort
          rcases iha false hsa with ⟨_, _, heva, hva, ihaEx⟩
          rcases ihb false hsb with ⟨_, _, hevb, hvb, ihbEx⟩
          rcases ihc false hsc with ⟨_, _, hevc, hvc, ihcEx⟩
          rcases valOfSort_false hva with ⟨xa, rfl, rfl⟩
          rcases valOfSort_false hvb with ⟨xb, rfl, rfl⟩
          rcases valOfSort_false hvc with ⟨xc, rfl, rfl⟩
          refine ⟨.u64 (xa * xb + xc), (xa * xb + xc).toBitVec,
            by simp [evalScalarExpr, heva, hevb, hevc]; rfl, rfl,
            fun e0 nP nR nRd rf hm hrd hr hp => ?_⟩
          have hvar0 : ∀ id ∈ boundVars, ∃ k < e0.nextRd, varOf id = some (.rd k) := by
            intro id hid; rcases hm id hid with ⟨k, _, hk, hv, _, _⟩; exact ⟨k, hk, hv⟩
          have hbA := lowerScalar_bounds_no_label varOf boundVars e0 a false hsa hvar0
          rcases hA : lowerScalar varOf e0 a with ⟨al, ar, e1⟩; simp only [hA] at hbA
          have hvar1 : ∀ id ∈ boundVars, ∃ k < e1.nextRd, varOf id = some (.rd k) := by
            intro id hid; rcases hvar0 id hid with ⟨k, hk, hv⟩; exact ⟨k, Nat.lt_of_lt_of_le hk hbA.1, hv⟩
          have hbB := lowerScalar_bounds_no_label varOf boundVars e1 b false hsb hvar1
          rcases hB : lowerScalar varOf e1 b with ⟨bl, br, e2⟩; simp only [hB] at hbB
          have hvar2 : ∀ id ∈ boundVars, ∃ k < e2.nextRd, varOf id = some (.rd k) := by
            intro id hid; rcases hvar1 id hid with ⟨k, hk, hv⟩; exact ⟨k, Nat.lt_of_lt_of_le hk hbB.1, hv⟩
          have hbC := lowerScalar_bounds_no_label varOf boundVars e2 c false hsc hvar2
          rcases hC : lowerScalar varOf e2 c with ⟨cl, cr, e3⟩; simp only [hC] at hbC
          simp only [lowerScalar, hA, hB, hC, freshRd] at hrd hr hp ⊢
          have hrdA : (lowerScalar varOf e0 a).2.2.nextRd ≤ nRd := by simp only [hA]; omega
          have hrA : (lowerScalar varOf e0 a).2.2.nextR ≤ nR := by simp only [hA]; omega
          have hpA : (lowerScalar varOf e0 a).2.2.nextP ≤ nP := by simp only [hA]; omega
          rcases ihaEx e0 nP nR nRd rf hm hrdA hrA hpA with
            ⟨ai, rf1, har, hai, hf1, hla, hex1⟩
          simp only [hA] at har hai hex1; subst har
          have hm1 := varEnvMatchesPTX_step hm hbA.1 hf1
          have hrdB : (lowerScalar varOf e1 b).2.2.nextRd ≤ nRd := by simp only [hB]; omega
          have hrB : (lowerScalar varOf e1 b).2.2.nextR ≤ nR := by simp only [hB]; omega
          have hpB : (lowerScalar varOf e1 b).2.2.nextP ≤ nP := by simp only [hB]; omega
          rcases ihbEx e1 nP nR nRd rf1 hm1 hrdB hrB hpB with
            ⟨bi, rf2, hbr, hbi, hf2, hlb, hex2⟩
          simp only [hB] at hbr hbi hex2; subst hbr
          have hm2 := varEnvMatchesPTX_step hm1 hbB.1 hf2
          have hrdC : (lowerScalar varOf e2 c).2.2.nextRd ≤ nRd := by simp only [hC]; omega
          have hrC : (lowerScalar varOf e2 c).2.2.nextR ≤ nR := by simp only [hC]; omega
          have hpC : (lowerScalar varOf e2 c).2.2.nextP ≤ nP := by simp only [hC]; omega
          rcases ihcEx e2 nP nR nRd rf2 hm2 hrdC hrC hpC with
            ⟨ci, rf3, hcr, hci, hf3, hlc, hex3⟩
          simp only [hC] at hcr hci hex3; subst hcr
          have hla3 : rf3.regs.lookup s!"%rd{ai}" = some (.scalar xa.toBitVec) :=
            (hf3.rd_eq ai (by omega)).trans ((hf2.rd_eq ai hai).trans hla)
          have hlb3 : rf3.regs.lookup s!"%rd{bi}" = some (.scalar xb.toBitVec) :=
            (hf3.rd_eq bi hbi).trans hlb
          let rf4 := rf3.setScalarRaw s!"%rd{e3.nextRd}" (xa * xb + xc).toBitVec
          have hf4 : RegFramePres e3.nextRd rf3 rf4 := regFrame_setRd rf3 (Nat.le_refl _) _
          have hs4 : PureExec
              [ins (.mad .lo .u64 s!"%rd{e3.nextRd}" (.reg s!"%rd{ai}") (.reg s!"%rd{bi}") (.reg s!"%rd{ci}"))]
              nP nR nRd rf3 rf4 :=
            pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => by
              have hex := exec_mad_lo_rd s c t hrt e3.nextRd ai bi ci (by omega) (by omega) (by omega) (by omega)
                xa.toBitVec xb.toBitVec xc.toBitVec
                (by rw [hrf]; exact hla3)
                (by rw [hrf]; exact hlb3)
                (by rw [hrf]; exact hlc)
              rw [hrf] at hex; exact hex
          have hf12 := regFrame_trans hf1 hf2 hbA.1
          have hf123 := regFrame_trans hf12 hf3 (Nat.le_trans hbA.1 hbB.1)
          exact ⟨e3.nextRd, rf4, rfl, by omega,
            regFrame_trans hf123 hf4 (Nat.le_trans (Nat.le_trans hbA.1 hbB.1) hbC.1),
            lookup_rd_self rf3 e3.nextRd _,
            pureExec_append (pureExec_append (pureExec_append hex1 hf1 hex2) hf12 hex3) hf123 hs4⟩
  | select c t f ihc iht ihf =>
    simp only [inferScalarSort] at hsort
    cases hsc : inferScalarSort boundVars c <;> simp only [hsc] at hsort
    · cases hsort
    · cases hst : inferScalarSort boundVars t <;> simp only [hst] at hsort
      · cases hsort
      · cases hsf : inferScalarSort boundVars f <;> simp only [hsf] at hsort
        · cases hsort
        · rename_i sc st sf
          cases heqtf : (st == sf) <;> simp [heqtf] at hsort
          obtain rfl : st = sf := eq_of_beq heqtf
          subst hsort
          rcases ihc sc hsc with ⟨vc, bvc, hevc, hvc, ihcEx⟩
          rcases iht st hst with ⟨vt, bvt, hevt, hvt, ihtEx⟩
          rcases ihf st hsf with ⟨vf, bvf, hevf, hvf, ihfEx⟩
          have hsel : evalScalarExpr env (.select c t f) =
              .ok (if bvc != 0#64 then vt else vf) ∧
              valOfSort st (if bvc != 0#64 then vt else vf) =
              some (if bvc != 0#64 then bvt else bvf) := by
            cases sc
            · rcases valOfSort_false hvc with ⟨xc, rfl, rfl⟩
              rw [u64_bne_zero_bv]
              cases hnz : (xc != 0) <;> simp [evalScalarExpr, hevc, hnz, hevt, hevf, hvt, hvf]
            · rcases valOfSort_true hvc with ⟨bc, rfl, rfl⟩
              rw [bool_word_bne_zero]
              cases bc <;> simp [evalScalarExpr, hevc, hevt, hevf, hvt, hvf]
          refine ⟨_, _, hsel.1, hsel.2, fun e0 nP nR nRd rf hm hrd hr hp => ?_⟩
          have hvar0 : ∀ id ∈ boundVars, ∃ k < e0.nextRd, varOf id = some (.rd k) := by
            intro id hid; rcases hm id hid with ⟨k, _, hk, hv, _, _⟩; exact ⟨k, hk, hv⟩
          have hbC := lowerScalar_bounds_no_label varOf boundVars e0 c sc hsc hvar0
          rcases hC : lowerScalar varOf e0 c with ⟨cl, cr, e1⟩; simp only [hC] at hbC
          have hvar1 : ∀ id ∈ boundVars, ∃ k < e1.nextRd, varOf id = some (.rd k) := by
            intro id hid; rcases hvar0 id hid with ⟨k, hk, hv⟩; exact ⟨k, Nat.lt_of_lt_of_le hk hbC.1, hv⟩
          have hbT := lowerScalar_bounds_no_label varOf boundVars e1 t st hst hvar1
          rcases hT : lowerScalar varOf e1 t with ⟨tl, tr, e2⟩; simp only [hT] at hbT
          have hvar2 : ∀ id ∈ boundVars, ∃ k < e2.nextRd, varOf id = some (.rd k) := by
            intro id hid; rcases hvar1 id hid with ⟨k, hk, hv⟩; exact ⟨k, Nat.lt_of_lt_of_le hk hbT.1, hv⟩
          have hbF := lowerScalar_bounds_no_label varOf boundVars e2 f st hsf hvar2
          rcases hF : lowerScalar varOf e2 f with ⟨fl, fr, e3⟩; simp only [hF] at hbF
          simp only [lowerScalar, hC, hT, hF, freshP, freshRd] at hrd hr hp ⊢
          have hrdC : (lowerScalar varOf e0 c).2.2.nextRd ≤ nRd := by simp only [hC]; omega
          have hrC : (lowerScalar varOf e0 c).2.2.nextR ≤ nR := by simp only [hC]; omega
          have hpC : (lowerScalar varOf e0 c).2.2.nextP ≤ nP := by simp only [hC]; omega
          rcases ihcEx e0 nP nR nRd rf hm hrdC hrC hpC with
            ⟨ci, rf1, hcr, hci, hf1, hlc, hex1⟩
          simp only [hC] at hcr hci hex1; subst hcr
          have hm1 := varEnvMatchesPTX_step hm hbC.1 hf1
          have hrdT : (lowerScalar varOf e1 t).2.2.nextRd ≤ nRd := by simp only [hT]; omega
          have hrT : (lowerScalar varOf e1 t).2.2.nextR ≤ nR := by simp only [hT]; omega
          have hpT : (lowerScalar varOf e1 t).2.2.nextP ≤ nP := by simp only [hT]; omega
          rcases ihtEx e1 nP nR nRd rf1 hm1 hrdT hrT hpT with
            ⟨ti, rf2, htr, hti, hf2, hlt, hex2⟩
          simp only [hT] at htr hti hex2; subst htr
          have hm2 := varEnvMatchesPTX_step hm1 hbT.1 hf2
          have hrdF : (lowerScalar varOf e2 f).2.2.nextRd ≤ nRd := by simp only [hF]; omega
          have hrF : (lowerScalar varOf e2 f).2.2.nextR ≤ nR := by simp only [hF]; omega
          have hpF : (lowerScalar varOf e2 f).2.2.nextP ≤ nP := by simp only [hF]; omega
          rcases ihfEx e2 nP nR nRd rf2 hm2 hrdF hrF hpF with
            ⟨fi, rf3, hfr, hfi, hf3, hlf, hex3⟩
          simp only [hF] at hfr hfi hex3; subst hfr
          have hlc3 : rf3.regs.lookup s!"%rd{ci}" = some (.scalar bvc) :=
            (hf3.rd_eq ci (by omega)).trans ((hf2.rd_eq ci hci).trans hlc)
          have hlt3 : rf3.regs.lookup s!"%rd{ti}" = some (.scalar bvt) :=
            (hf3.rd_eq ti hti).trans hlt
          rcases exec_tail_select (nP := nP) (nR := nR) (nRd := nRd) (di := e3.nextRd)
              (ci := ci) (ti := ti) (fi := fi) (pi := e3.nextP)
              (by omega) (by omega) (by omega) hfi (by omega) bvc bvt bvf rf3 hlc3 hlt3 hlf with
            ⟨rf4, hf4, hlk4, hs4⟩
          have hf12 := regFrame_trans hf1 hf2 hbC.1
          have hf123 := regFrame_trans hf12 hf3 (Nat.le_trans hbC.1 hbT.1)
          exact ⟨e3.nextRd, rf4, rfl, by omega,
            regFrame_trans hf123 hf4 (Nat.le_trans (Nat.le_trans hbC.1 hbT.1) hbF.1), hlk4,
            pureExec_append (pureExec_append (pureExec_append hex1 hf1 hex2) hf12 hex3) hf123 hs4⟩
  | binOp op l r ihl ihr =>
    simp only [inferScalarSort] at hsort
    cases hsl : inferScalarSort boundVars l <;> simp only [hsl] at hsort
    · cases hsort
    · cases hsr : inferScalarSort boundVars r <;> simp only [hsr] at hsort
      · cases hsort
      · rename_i sl sr
        rcases ihl sl hsl with ⟨vl, bvl, hevl, hvl, ihlEx⟩
        rcases ihr sr hsr with ⟨vr, bvr, hevr, hvr, ihrEx⟩
        have hstepLR : ∀ (e0 : PEnv) (nP nR nRd : Nat) (rf : PTXRegFile),
            varEnvMatchesPTX env varOf boundVars e0.nextRd rf →
            let (ll, lr, e1) := lowerScalar varOf e0 l
            let (rl, rr, e2) := lowerScalar varOf e1 r
            e2.nextRd ≤ nRd → e2.nextR ≤ nR → e2.nextP ≤ nP →
            ∃ (li ri : Nat) (rf2 : PTXRegFile),
              lr = .rd li ∧ rr = .rd ri ∧
              li < e2.nextRd ∧ ri < e2.nextRd ∧
              e0.nextRd ≤ e2.nextRd ∧
              RegFramePres e0.nextRd rf rf2 ∧
              rf2.regs.lookup s!"%rd{li}" = some (.scalar bvl) ∧
              rf2.regs.lookup s!"%rd{ri}" = some (.scalar bvr) ∧
              PureExec (ll ++ rl) nP nR nRd rf rf2 := by
          intro e0 nP nR nRd rf hm
          have hvar0 : ∀ id ∈ boundVars, ∃ k < e0.nextRd, varOf id = some (.rd k) := by
            intro id hid; rcases hm id hid with ⟨k, _, hk, hv, _, _⟩; exact ⟨k, hk, hv⟩
          have hbL := lowerScalar_bounds_no_label varOf boundVars e0 l sl hsl hvar0
          rcases hL : lowerScalar varOf e0 l with ⟨ll, lr, e1⟩
          simp only [hL] at hbL ⊢
          have hvar1 : ∀ id ∈ boundVars, ∃ k < e1.nextRd, varOf id = some (.rd k) := by
            intro id hid; rcases hvar0 id hid with ⟨k, hk, hv⟩; exact ⟨k, Nat.lt_of_lt_of_le hk hbL.1, hv⟩
          have hbR := lowerScalar_bounds_no_label varOf boundVars e1 r sr hsr hvar1
          rcases hR : lowerScalar varOf e1 r with ⟨rl, rr, e2⟩
          simp only [hR] at hbR ⊢
          intro hrd2 hr2 hp2
          have hrdL : (lowerScalar varOf e0 l).2.2.nextRd ≤ nRd := by simp only [hL]; omega
          have hrL : (lowerScalar varOf e0 l).2.2.nextR ≤ nR := by simp only [hL]; omega
          have hpL : (lowerScalar varOf e0 l).2.2.nextP ≤ nP := by simp only [hL]; omega
          rcases ihlEx e0 nP nR nRd rf hm hrdL hrL hpL with
            ⟨li, rf1, hlr, hli, hf1, hll, hex1⟩
          simp only [hL] at hlr hli hex1; subst hlr
          have hm1 := varEnvMatchesPTX_step hm hbL.1 hf1
          have hrdR : (lowerScalar varOf e1 r).2.2.nextRd ≤ nRd := by simp only [hR]; exact hrd2
          have hrR : (lowerScalar varOf e1 r).2.2.nextR ≤ nR := by simp only [hR]; exact hr2
          have hpR : (lowerScalar varOf e1 r).2.2.nextP ≤ nP := by simp only [hR]; exact hp2
          rcases ihrEx e1 nP nR nRd rf1 hm1 hrdR hrR hpR with
            ⟨ri, rf2, hrr, hri, hf2, hlr2, hex2⟩
          simp only [hR] at hrr hri hex2; subst hrr
          exact ⟨li, ri, rf2, rfl, rfl, by omega, hri, Nat.le_trans hbL.1 hbR.1,
            regFrame_trans hf1 hf2 hbL.1, (hf2.rd_eq li hli).trans hll, hlr2,
            pureExec_append hex1 hf1 hex2⟩
        cases sl
        · cases sr <;> try simp at hsort
          rcases valOfSort_false hvl with ⟨xl, rfl, rfl⟩
          rcases valOfSort_false hvr with ⟨xr, rfl, rfl⟩
          cases op <;> simp [inferBinOpU64] at hsort
          · subst hsort
            refine ⟨.u64 (xl + xr), (xl + xr).toBitVec, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
              fun e0 nP nR nRd rf hm hrd hr hp => ?_⟩
            rcases hL : lowerScalar varOf e0 l with ⟨ll, lr, e1⟩
            rcases hR : lowerScalar varOf e1 r with ⟨rl, rr, e2⟩
            simp only [lowerScalar, hL, hR, freshRd] at hrd hr hp ⊢
            have hLR := hstepLR e0 nP nR nRd rf hm; simp only [hL, hR] at hLR
            rcases hLR (by omega) hr hp with ⟨li, ri, rf2, rfl, rfl, hli, hri, hle02, hf12, hll, hlr2, hex12⟩
            rcases exec_tail_arith .add (nP := nP) (nR := nR) (nRd := nRd) (di := e2.nextRd)
                (by omega) hli hri xl xr rf2 hll hlr2 (Or.inl rfl) with ⟨_, rf3, _, hev, rfl, hf3, hlk3, hs3⟩
            cases hev
            exact ⟨e2.nextRd, rf3, rfl, by omega, regFrame_trans hf12 hf3 hle02, hlk3,
              pureExec_append hex12 hf12 hs3⟩
          · subst hsort
            refine ⟨.u64 (xl - xr), (xl - xr).toBitVec, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
              fun e0 nP nR nRd rf hm hrd hr hp => ?_⟩
            rcases hL : lowerScalar varOf e0 l with ⟨ll, lr, e1⟩
            rcases hR : lowerScalar varOf e1 r with ⟨rl, rr, e2⟩
            simp only [lowerScalar, hL, hR, freshRd] at hrd hr hp ⊢
            have hLR := hstepLR e0 nP nR nRd rf hm; simp only [hL, hR] at hLR
            rcases hLR (by omega) hr hp with ⟨li, ri, rf2, rfl, rfl, hli, hri, hle02, hf12, hll, hlr2, hex12⟩
            rcases exec_tail_arith .sub (nP := nP) (nR := nR) (nRd := nRd) (di := e2.nextRd)
                (by omega) hli hri xl xr rf2 hll hlr2 (Or.inr (Or.inl rfl)) with
              ⟨_, rf3, _, hev, rfl, hf3, hlk3, hs3⟩
            cases hev
            exact ⟨e2.nextRd, rf3, rfl, by omega, regFrame_trans hf12 hf3 hle02, hlk3,
              pureExec_append hex12 hf12 hs3⟩
          · subst hsort
            refine ⟨.u64 (xl * xr), (xl * xr).toBitVec, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
              fun e0 nP nR nRd rf hm hrd hr hp => ?_⟩
            rcases hL : lowerScalar varOf e0 l with ⟨ll, lr, e1⟩
            rcases hR : lowerScalar varOf e1 r with ⟨rl, rr, e2⟩
            simp only [lowerScalar, hL, hR, freshRd] at hrd hr hp ⊢
            have hLR := hstepLR e0 nP nR nRd rf hm; simp only [hL, hR] at hLR
            rcases hLR (by omega) hr hp with ⟨li, ri, rf2, rfl, rfl, hli, hri, hle02, hf12, hll, hlr2, hex12⟩
            rcases exec_tail_arith .mul (nP := nP) (nR := nR) (nRd := nRd) (di := e2.nextRd)
                (by omega) hli hri xl xr rf2 hll hlr2 (Or.inr (Or.inr (Or.inl rfl))) with
              ⟨_, rf3, _, hev, rfl, hf3, hlk3, hs3⟩
            cases hev
            exact ⟨e2.nextRd, rf3, rfl, by omega, regFrame_trans hf12 hf3 hle02, hlk3,
              pureExec_append hex12 hf12 hs3⟩
          · subst hsort
            refine ⟨.u64 (xl / xr), (xl / xr).toBitVec, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
              fun e0 nP nR nRd rf hm hrd hr hp => ?_⟩
            rcases hL : lowerScalar varOf e0 l with ⟨ll, lr, e1⟩
            rcases hR : lowerScalar varOf e1 r with ⟨rl, rr, e2⟩
            simp only [lowerScalar, hL, hR, freshRd, freshP] at hrd hr hp ⊢
            have hLR := hstepLR e0 nP nR nRd rf hm; simp only [hL, hR] at hLR
            rcases hLR (by omega) hr (by omega) with
              ⟨li, ri, rf2, rfl, rfl, hli, hri, hle02, hf12, hll, hlr2, hex12⟩
            rcases exec_tail_divmod false (nP := nP) (nR := nR) (nRd := nRd) (di := e2.nextRd)
                (li := li) (ri := ri) (pi := e2.nextP) (by omega) hli hri (by omega) xl xr rf2 hll hlr2 with
              ⟨rf3, hf3, hlk3, hs3⟩
            exact ⟨e2.nextRd, rf3, rfl, by omega, regFrame_trans hf12 hf3 hle02, hlk3,
              pureExec_append hex12 hf12 hs3⟩
          · subst hsort
            refine ⟨.u64 (xl % xr), (xl % xr).toBitVec, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
              fun e0 nP nR nRd rf hm hrd hr hp => ?_⟩
            rcases hL : lowerScalar varOf e0 l with ⟨ll, lr, e1⟩
            rcases hR : lowerScalar varOf e1 r with ⟨rl, rr, e2⟩
            simp only [lowerScalar, hL, hR, freshRd, freshP] at hrd hr hp ⊢
            have hLR := hstepLR e0 nP nR nRd rf hm; simp only [hL, hR] at hLR
            rcases hLR (by omega) hr (by omega) with
              ⟨li, ri, rf2, rfl, rfl, hli, hri, hle02, hf12, hll, hlr2, hex12⟩
            rcases exec_tail_divmod true (nP := nP) (nR := nR) (nRd := nRd) (di := e2.nextRd)
                (li := li) (ri := ri) (pi := e2.nextP) (by omega) hli hri (by omega) xl xr rf2 hll hlr2 with
              ⟨rf3, hf3, hlk3, hs3⟩
            exact ⟨e2.nextRd, rf3, rfl, by omega, regFrame_trans hf12 hf3 hle02, hlk3,
              pureExec_append hex12 hf12 hs3⟩
          · subst hsort
            refine ⟨.u64 (xl &&& xr), (xl &&& xr).toBitVec, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
              fun e0 nP nR nRd rf hm hrd hr hp => ?_⟩
            rcases hL : lowerScalar varOf e0 l with ⟨ll, lr, e1⟩
            rcases hR : lowerScalar varOf e1 r with ⟨rl, rr, e2⟩
            simp only [lowerScalar, hL, hR, freshRd] at hrd hr hp ⊢
            have hLR := hstepLR e0 nP nR nRd rf hm; simp only [hL, hR] at hLR
            rcases hLR (by omega) hr hp with ⟨li, ri, rf2, rfl, rfl, hli, hri, hle02, hf12, hll, hlr2, hex12⟩
            rcases exec_tail_arith .bitAnd (nP := nP) (nR := nR) (nRd := nRd) (di := e2.nextRd)
                (by omega) hli hri xl xr rf2 hll hlr2 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) with
              ⟨_, rf3, _, hev, rfl, hf3, hlk3, hs3⟩
            cases hev
            exact ⟨e2.nextRd, rf3, rfl, by omega, regFrame_trans hf12 hf3 hle02, hlk3,
              pureExec_append hex12 hf12 hs3⟩
          · subst hsort
            refine ⟨.u64 (xl ||| xr), (xl ||| xr).toBitVec, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
              fun e0 nP nR nRd rf hm hrd hr hp => ?_⟩
            rcases hL : lowerScalar varOf e0 l with ⟨ll, lr, e1⟩
            rcases hR : lowerScalar varOf e1 r with ⟨rl, rr, e2⟩
            simp only [lowerScalar, hL, hR, freshRd] at hrd hr hp ⊢
            have hLR := hstepLR e0 nP nR nRd rf hm; simp only [hL, hR] at hLR
            rcases hLR (by omega) hr hp with ⟨li, ri, rf2, rfl, rfl, hli, hri, hle02, hf12, hll, hlr2, hex12⟩
            rcases exec_tail_arith .bitOr (nP := nP) (nR := nR) (nRd := nRd) (di := e2.nextRd)
                (by omega) hli hri xl xr rf2 hll hlr2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) with
              ⟨_, rf3, _, hev, rfl, hf3, hlk3, hs3⟩
            cases hev
            exact ⟨e2.nextRd, rf3, rfl, by omega, regFrame_trans hf12 hf3 hle02, hlk3,
              pureExec_append hex12 hf12 hs3⟩
          · subst hsort
            refine ⟨.u64 (xl ^^^ xr), (xl ^^^ xr).toBitVec, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
              fun e0 nP nR nRd rf hm hrd hr hp => ?_⟩
            rcases hL : lowerScalar varOf e0 l with ⟨ll, lr, e1⟩
            rcases hR : lowerScalar varOf e1 r with ⟨rl, rr, e2⟩
            simp only [lowerScalar, hL, hR, freshRd] at hrd hr hp ⊢
            have hLR := hstepLR e0 nP nR nRd rf hm; simp only [hL, hR] at hLR
            rcases hLR (by omega) hr hp with ⟨li, ri, rf2, rfl, rfl, hli, hri, hle02, hf12, hll, hlr2, hex12⟩
            rcases exec_tail_arith .bitXor (nP := nP) (nR := nR) (nRd := nRd) (di := e2.nextRd)
                (by omega) hli hri xl xr rf2 hll hlr2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) with
              ⟨_, rf3, _, hev, rfl, hf3, hlk3, hs3⟩
            cases hev
            exact ⟨e2.nextRd, rf3, rfl, by omega, regFrame_trans hf12 hf3 hle02, hlk3,
              pureExec_append hex12 hf12 hs3⟩
          · subst hsort
            refine ⟨.u64 (xl <<< xr), (xl <<< xr).toBitVec, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
              fun e0 nP nR nRd rf hm hrd hr hp => ?_⟩
            rcases hL : lowerScalar varOf e0 l with ⟨ll, lr, e1⟩
            rcases hR : lowerScalar varOf e1 r with ⟨rl, rr, e2⟩
            simp only [lowerScalar, hL, hR, freshRd, freshR] at hrd hr hp ⊢
            have hLR := hstepLR e0 nP nR nRd rf hm; simp only [hL, hR] at hLR
            rcases hLR (by omega) (by omega) hp with
              ⟨li, ri, rf2, rfl, rfl, hli, hri, hle02, hf12, hll, hlr2, hex12⟩
            rcases exec_tail_shift true false (nP := nP) (nR := nR) (nRd := nRd) (di := e2.nextRd)
                (li := li) (ri := ri) (si := e2.nextR) (by omega) hli hri (by omega) xl xr rf2 hll hlr2 with
              ⟨rf3, hf3, hlk3, hs3⟩
            exact ⟨e2.nextRd, rf3, rfl, by omega, regFrame_trans hf12 hf3 hle02, hlk3,
              pureExec_append hex12 hf12 hs3⟩
          · subst hsort
            refine ⟨.u64 (xl >>> xr), (xl >>> xr).toBitVec, by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
              fun e0 nP nR nRd rf hm hrd hr hp => ?_⟩
            rcases hL : lowerScalar varOf e0 l with ⟨ll, lr, e1⟩
            rcases hR : lowerScalar varOf e1 r with ⟨rl, rr, e2⟩
            simp only [lowerScalar, hL, hR, freshRd, freshR] at hrd hr hp ⊢
            have hLR := hstepLR e0 nP nR nRd rf hm; simp only [hL, hR] at hLR
            rcases hLR (by omega) (by omega) hp with
              ⟨li, ri, rf2, rfl, rfl, hli, hri, hle02, hf12, hll, hlr2, hex12⟩
            rcases exec_tail_shift false false (nP := nP) (nR := nR) (nRd := nRd) (di := e2.nextRd)
                (li := li) (ri := ri) (si := e2.nextR) (by omega) hli hri (by omega) xl xr rf2 hll hlr2 with
              ⟨rf3, hf3, hlk3, hs3⟩
            exact ⟨e2.nextRd, rf3, rfl, by omega, regFrame_trans hf12 hf3 hle02, hlk3,
              pureExec_append hex12 hf12 hs3⟩
          · subst hsort
            refine ⟨.u64 (lnirSar64 xl xr), (lnirSar64 xl xr).toBitVec,
              by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
              fun e0 nP nR nRd rf hm hrd hr hp => ?_⟩
            rcases hL : lowerScalar varOf e0 l with ⟨ll, lr, e1⟩
            rcases hR : lowerScalar varOf e1 r with ⟨rl, rr, e2⟩
            simp only [lowerScalar, hL, hR, freshRd, freshR] at hrd hr hp ⊢
            have hLR := hstepLR e0 nP nR nRd rf hm; simp only [hL, hR] at hLR
            rcases hLR (by omega) (by omega) hp with
              ⟨li, ri, rf2, rfl, rfl, hli, hri, hle02, hf12, hll, hlr2, hex12⟩
            rcases exec_tail_shift false true (nP := nP) (nR := nR) (nRd := nRd) (di := e2.nextRd)
                (li := li) (ri := ri) (si := e2.nextR) (by omega) hli hri (by omega) xl xr rf2 hll hlr2 with
              ⟨rf3, hf3, hlk3, hs3⟩
            exact ⟨e2.nextRd, rf3, rfl, by omega, regFrame_trans hf12 hf3 hle02, hlk3,
              pureExec_append hex12 hf12 hs3⟩
          · subst hsort
            refine ⟨.bool (xl == xr), if xl == xr then 1#64 else 0#64,
              by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
              fun e0 nP nR nRd rf hm hrd hr hp => ?_⟩
            rcases hL : lowerScalar varOf e0 l with ⟨ll, lr, e1⟩
            rcases hR : lowerScalar varOf e1 r with ⟨rl, rr, e2⟩
            simp only [lowerScalar, hL, hR, freshRd, freshP] at hrd hr hp ⊢
            have hLR := hstepLR e0 nP nR nRd rf hm; simp only [hL, hR] at hLR
            rcases hLR (by omega) hr (by omega) with
              ⟨li, ri, rf2, rfl, rfl, hli, hri, hle02, hf12, hll, hlr2, hex12⟩
            rcases exec_tail_cmp .eq (nP := nP) (nR := nR) (nRd := nRd) (di := e2.nextRd)
                (li := li) (ri := ri) (pi := e2.nextP) (by omega) hli hri (by omega)
                xl.toBitVec xr.toBitVec rf2 hll hlr2 with ⟨rf3, hf3, hlk3, hs3⟩
            have hcmp : evalPTXCmp .eq .u64 xl.toBitVec xr.toBitVec = (xl == xr) := u64_eq_bv xl xr
            rw [hcmp] at hlk3
            exact ⟨e2.nextRd, rf3, rfl, by omega, regFrame_trans hf12 hf3 hle02, hlk3,
              pureExec_append hex12 hf12 hs3⟩
          · subst hsort
            refine ⟨.bool (decide (xl < xr)), if decide (xl < xr) then 1#64 else 0#64,
              by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
              fun e0 nP nR nRd rf hm hrd hr hp => ?_⟩
            rcases hL : lowerScalar varOf e0 l with ⟨ll, lr, e1⟩
            rcases hR : lowerScalar varOf e1 r with ⟨rl, rr, e2⟩
            simp only [lowerScalar, hL, hR, freshRd, freshP] at hrd hr hp ⊢
            have hLR := hstepLR e0 nP nR nRd rf hm; simp only [hL, hR] at hLR
            rcases hLR (by omega) hr (by omega) with
              ⟨li, ri, rf2, rfl, rfl, hli, hri, hle02, hf12, hll, hlr2, hex12⟩
            rcases exec_tail_cmp .lt (nP := nP) (nR := nR) (nRd := nRd) (di := e2.nextRd)
                (li := li) (ri := ri) (pi := e2.nextP) (by omega) hli hri (by omega)
                xl.toBitVec xr.toBitVec rf2 hll hlr2 with ⟨rf3, hf3, hlk3, hs3⟩
            have hcmp : evalPTXCmp .lt .u64 xl.toBitVec xr.toBitVec = decide (xl < xr) := u64_ult_bv xl xr
            rw [hcmp] at hlk3
            exact ⟨e2.nextRd, rf3, rfl, by omega, regFrame_trans hf12 hf3 hle02, hlk3,
              pureExec_append hex12 hf12 hs3⟩
          · subst hsort
            refine ⟨.bool (decide (xl ≤ xr)), if decide (xl ≤ xr) then 1#64 else 0#64,
              by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
              fun e0 nP nR nRd rf hm hrd hr hp => ?_⟩
            rcases hL : lowerScalar varOf e0 l with ⟨ll, lr, e1⟩
            rcases hR : lowerScalar varOf e1 r with ⟨rl, rr, e2⟩
            simp only [lowerScalar, hL, hR, freshRd, freshP] at hrd hr hp ⊢
            have hLR := hstepLR e0 nP nR nRd rf hm; simp only [hL, hR] at hLR
            rcases hLR (by omega) hr (by omega) with
              ⟨li, ri, rf2, rfl, rfl, hli, hri, hle02, hf12, hll, hlr2, hex12⟩
            rcases exec_tail_cmp .le (nP := nP) (nR := nR) (nRd := nRd) (di := e2.nextRd)
                (li := li) (ri := ri) (pi := e2.nextP) (by omega) hli hri (by omega)
                xl.toBitVec xr.toBitVec rf2 hll hlr2 with ⟨rf3, hf3, hlk3, hs3⟩
            have hcmp : evalPTXCmp .le .u64 xl.toBitVec xr.toBitVec = decide (xl ≤ xr) := u64_ule_bv xl xr
            rw [hcmp] at hlk3
            exact ⟨e2.nextRd, rf3, rfl, by omega, regFrame_trans hf12 hf3 hle02, hlk3,
              pureExec_append hex12 hf12 hs3⟩
          · subst hsort
            refine ⟨.u64 ((xl ^^^ (xr >>> 32)) ^^^ (xr &&& 0xffffffff)),
              ((xl ^^^ (xr >>> 32)) ^^^ (xr &&& 0xffffffff)).toBitVec,
              by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
              fun e0 nP nR nRd rf hm hrd hr hp => ?_⟩
            rcases hL : lowerScalar varOf e0 l with ⟨ll, lr, e1⟩
            rcases hR : lowerScalar varOf e1 r with ⟨rl, rr, e2⟩
            simp only [lowerScalar, hL, hR, freshRd] at hrd hr hp ⊢
            have hLR := hstepLR e0 nP nR nRd rf hm; simp only [hL, hR] at hLR
            rcases hLR (by omega) hr hp with ⟨li, ri, rf2, rfl, rfl, hli, hri, hle02, hf12, hll, hlr2, hex12⟩
            rcases exec_tail_eor3 (nP := nP) (nR := nR) (nRd := nRd) (di := e2.nextRd)
                (li := li) (ri := ri) (by omega) hli hri xl xr rf2 hll hlr2 with
              ⟨rf3, hf3, hlk3, hs3⟩
            exact ⟨e2.nextRd, rf3, rfl, by omega, regFrame_trans hf12 hf3 hle02, hlk3,
              pureExec_append hex12 hf12 hs3⟩
        · cases sr <;> try simp at hsort
          rcases valOfSort_true hvl with ⟨bl, rfl, rfl⟩
          rcases valOfSort_true hvr with ⟨br, rfl, rfl⟩
          cases op <;> simp [inferBinOpBool] at hsort
          subst hsort
          refine ⟨.bool (bl == br), if bl == br then 1#64 else 0#64,
            by simp [evalScalarExpr, hevl, hevr]; rfl, rfl,
            fun e0 nP nR nRd rf hm hrd hr hp => ?_⟩
          rcases hL : lowerScalar varOf e0 l with ⟨ll, lr, e1⟩
          rcases hR : lowerScalar varOf e1 r with ⟨rl, rr, e2⟩
          simp only [lowerScalar, hL, hR, freshRd, freshP] at hrd hr hp ⊢
          have hLR := hstepLR e0 nP nR nRd rf hm; simp only [hL, hR] at hLR
          rcases hLR (by omega) hr (by omega) with
            ⟨li, ri, rf2, rfl, rfl, hli, hri, hle02, hf12, hll, hlr2, hex12⟩
          rcases exec_tail_cmp .eq (nP := nP) (nR := nR) (nRd := nRd) (di := e2.nextRd)
              (li := li) (ri := ri) (pi := e2.nextP) (by omega) hli hri (by omega)
              (if bl then 1#64 else 0#64) (if br then 1#64 else 0#64) rf2 hll hlr2 with
            ⟨rf3, hf3, hlk3, hs3⟩
          have hcmp : evalPTXCmp .eq .u64 (if bl then 1#64 else 0#64) (if br then 1#64 else 0#64) = (bl == br) :=
            bool_word_eq_iff bl br
          rw [hcmp] at hlk3
          exact ⟨e2.nextRd, rf3, rfl, by omega, regFrame_trans hf12 hf3 hle02, hlk3,
            pureExec_append hex12 hf12 hs3⟩

end LeanNative.Proofs.PTXScalarProofs
