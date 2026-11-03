import LeanNative.Backend.PTXLower
import LeanNative.Proofs.PTXGrid4
import LeanNative.Proofs.TargetBitVecProofs

/-!
# PTX 8.0 Scalar Expression Lowering Soundness (`LeanNative.Proofs.PTXScalarProofs`)

Proves register-allocation monotonicity, label-freedom, register-frame preservation, and
SIMT execution equivalence between `Semantics.evalScalarExpr` and `PTXLower.lowerScalar`
under `PTXAst.runCTAWithGlobalLog` (`0 sorryAx`, `0 ofReduceBool`).
-/

namespace LeanNative.Proofs.PTXScalarProofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend
open LeanNative.Backend.PTXAst
open LeanNative.Proofs.PTXSIMT
open LeanNative.Backend.PTXLower
open LeanNative.Proofs

def varEnvMatchesPTX (env : VarEnv) (varOf : Nat → Option PReg) (boundVars : List Nat)
    (rdBound : Nat) (rf : PTXRegFile) : Prop :=
  ∀ id ∈ boundVars, ∃ (k : Nat) (x : UInt64),
    k < rdBound ∧ varOf id = some (.rd k) ∧ env id = some (.u64 x) ∧
      rf.regs.lookup s!"%rd{k}" = some (.scalar x.toBitVec)

theorem valOfSort_false {v : Val} {bv : BitVec 64} (h : valOfSort false v = some bv) :
    ∃ x : UInt64, v = .u64 x ∧ bv = x.toBitVec := by
  cases v <;> simp [valOfSort] at h
  exact ⟨_, rfl, h.symm⟩

theorem valOfSort_true {v : Val} {bv : BitVec 64} (h : valOfSort true v = some bv) :
    ∃ b : Bool, v = .bool b ∧ bv = (if b then 1#64 else 0#64) := by
  cases v <;> simp [valOfSort] at h
  exact ⟨_, rfl, h.symm⟩

theorem lookup_rd_self (rf : PTXRegFile) (i : Nat) (v : BitVec 64) :
    (rf.setScalarRaw s!"%rd{i}" v).regs.lookup s!"%rd{i}" = some (.scalar v) :=
  setAssoc_lookup_self rf.regs s!"%rd{i}" (.scalar v)

theorem lookup_rd_ne (rf : PTXRegFile) {i j : Nat} (hne : j ≠ i) (v : BitVec 64) :
    (rf.setScalarRaw s!"%rd{i}" v).regs.lookup s!"%rd{j}" = rf.regs.lookup s!"%rd{j}" :=
  setAssoc_lookup_ne rf.regs s!"%rd{i}" s!"%rd{j}" (.scalar v)
    (fun h => hne (regName_inj "%rd" j i h))

theorem lookup_r_self (rf : PTXRegFile) (i : Nat) (v : BitVec 64) :
    (rf.setScalarRaw s!"%r{i}" v).regs.lookup s!"%r{i}" = some (.scalar v) :=
  setAssoc_lookup_self rf.regs s!"%r{i}" (.scalar v)

theorem lookup_r_rd (rf : PTXRegFile) (i j : Nat) (v : BitVec 64) :
    (rf.setScalarRaw s!"%r{i}" v).regs.lookup s!"%rd{j}" = rf.regs.lookup s!"%rd{j}" :=
  setAssoc_lookup_ne rf.regs s!"%r{i}" s!"%rd{j}" (.scalar v) (fun h => r_ne_rd i j h.symm)

theorem lookup_p_self (rf : PTXRegFile) (i : Nat) (b : Bool) :
    (rf.setPredRaw s!"%p{i}" b).regs.lookup s!"%p{i}" = some (.pred b) :=
  setAssoc_lookup_self rf.regs s!"%p{i}" (.pred b)

theorem lookup_p_rd (rf : PTXRegFile) (i j : Nat) (b : Bool) :
    (rf.setPredRaw s!"%p{i}" b).regs.lookup s!"%rd{j}" = rf.regs.lookup s!"%rd{j}" :=
  setAssoc_lookup_ne rf.regs s!"%p{i}" s!"%rd{j}" (.pred b) (fun h => p_ne_rd i j h.symm)

structure RegFramePres (bound : Nat) (rf rf' : PTXRegFile) : Prop where
  enforce_eq : rf'.enforceDecls = rf.enforceDecls
  decls_eq : rf'.decls = rf.decls
  rd_eq : ∀ j < bound, rf'.regs.lookup s!"%rd{j}" = rf.regs.lookup s!"%rd{j}"

theorem regFrame_refl (bound : Nat) (rf : PTXRegFile) : RegFramePres bound rf rf :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

theorem regFrame_trans {b1 b2 : Nat} {rf0 rf1 rf2 : PTXRegFile}
    (h1 : RegFramePres b1 rf0 rf1) (h2 : RegFramePres b2 rf1 rf2) (hle : b1 ≤ b2) :
    RegFramePres b1 rf0 rf2 :=
  ⟨h2.enforce_eq.trans h1.enforce_eq, h2.decls_eq.trans h1.decls_eq,
    fun j hj => (h2.rd_eq j (Nat.lt_of_lt_of_le hj hle)).trans (h1.rd_eq j hj)⟩

theorem regFrame_regTyped {bound nP nR nRd : Nat} {rf rf' : PTXRegFile}
    (hf : RegFramePres bound rf rf') (hrt : RegTyped rf nP nR nRd) : RegTyped rf' nP nR nRd := by
  rcases hrt with ⟨he, hp, hr, hrd⟩
  refine ⟨hf.enforce_eq.trans he, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · have := hp i hi; rwa [← hf.decls_eq] at this
  · have := hr i hi; rwa [← hf.decls_eq] at this
  · have := hrd i hi; rwa [← hf.decls_eq] at this

theorem regFrame_setRd (rf : PTXRegFile) {bound i : Nat} (hle : bound ≤ i) (v : BitVec 64) :
    RegFramePres bound rf (rf.setScalarRaw s!"%rd{i}" v) :=
  ⟨rfl, rfl, fun _ hj => lookup_rd_ne rf (by omega) v⟩

theorem regFrame_setR (rf : PTXRegFile) (bound i : Nat) (v : BitVec 64) :
    RegFramePres bound rf (rf.setScalarRaw s!"%r{i}" v) :=
  ⟨rfl, rfl, fun j _ => lookup_r_rd rf i j v⟩

theorem regFrame_setP (rf : PTXRegFile) (bound i : Nat) (b : Bool) :
    RegFramePres bound rf (rf.setPredRaw s!"%p{i}" b) :=
  ⟨rfl, rfl, fun j _ => lookup_p_rd rf i j b⟩

theorem varEnvMatchesPTX_step {env : VarEnv} {varOf : Nat → Option PReg}
    {boundVars : List Nat} {b1 b2 : Nat} {rf1 rf2 : PTXRegFile}
    (hm : varEnvMatchesPTX env varOf boundVars b1 rf1) (hle : b1 ≤ b2)
    (hf : RegFramePres b1 rf1 rf2) : varEnvMatchesPTX env varOf boundVars b2 rf2 := by
  intro id hid
  rcases hm id hid with ⟨k, x, hk, hv, he, hlk⟩
  exact ⟨k, x, Nat.lt_of_lt_of_le hk hle, hv, he, (hf.rd_eq k hk).trans hlk⟩

def SliceAt (stmts el : List PTXStmt) (pc : Nat) : Prop :=
  ∀ k < el.length, stmts[pc + k]? = el[k]?

theorem sliceAt_append_left {stmts l1 l2 : List PTXStmt} {pc : Nat}
    (h : SliceAt stmts (l1 ++ l2) pc) : SliceAt stmts l1 pc := by
  intro k hk
  have h1 := h k (by rw [List.length_append]; omega)
  rwa [List.getElem?_append_left hk] at h1

theorem sliceAt_append_right {stmts l1 l2 : List PTXStmt} {pc : Nat}
    (h : SliceAt stmts (l1 ++ l2) pc) : SliceAt stmts l2 (pc + l1.length) := by
  intro k hk
  have h1 := h (l1.length + k) (by rw [List.length_append]; omega)
  have h2 : pc + l1.length + k = pc + (l1.length + k) := by omega
  rw [h2, h1, List.getElem?_append_right (by omega)]
  simp

def PureExec (el : List PTXStmt) (nP nR nRd : Nat) (rf rf' : PTXRegFile) : Prop :=
  RegTyped rf nP nR nRd →
    ∀ (f : Nat) (stmts : List PTXStmt) (cta : PTXCTAState)
      (done todo : List PTXThreadState) (localBytes tx pc : Nat) (saved : List MemAccessLog),
      (∀ t ∈ done, t.halted = true) →
      SliceAt stmts el pc →
      runCTAWithGlobalLog (f + el.length) stmts
        { cta with threads := done ++ (laneAt localBytes tx pc rf false :: todo) } saved =
      runCTAWithGlobalLog f stmts
        { cta with threads := done ++ (laneAt localBytes tx (pc + el.length) rf' false :: todo) } saved

theorem pureExec_nil (nP nR nRd : Nat) (rf : PTXRegFile) : PureExec [] nP nR nRd rf rf := by
  intro _ _ _ _ _ _ _ _ _ _ _ _; simp

theorem pureExec_append {l1 l2 : List PTXStmt} {nP nR nRd b : Nat} {rf0 rf1 rf2 : PTXRegFile}
    (h1 : PureExec l1 nP nR nRd rf0 rf1) (hf1 : RegFramePres b rf0 rf1)
    (h2 : PureExec l2 nP nR nRd rf1 rf2) : PureExec (l1 ++ l2) nP nR nRd rf0 rf2 := by
  intro hrt f stmts cta done todo localBytes tx pc saved hdone hslice
  have hrt1 := regFrame_regTyped hf1 hrt
  have hf_eq : f + (l1 ++ l2).length = (f + l2.length) + l1.length := by rw [List.length_append]; omega
  have hpc_eq : pc + l1.length + l2.length = pc + (l1 ++ l2).length := by rw [List.length_append]; omega
  rw [hf_eq,
      h1 hrt (f + l2.length) stmts cta done todo localBytes tx pc saved hdone (sliceAt_append_left hslice),
      h2 hrt1 f stmts cta done todo localBytes tx (pc + l1.length) saved hdone (sliceAt_append_right hslice),
      hpc_eq]

theorem pureExec_single {i : PTXInstr} {nP nR nRd : Nat} {rf rf' : PTXRegFile}
    (hnBar : ∀ b, i ≠ .barSync b) (hnShfl : ∀ d s o c m, i ≠ .shflSyncBfly d s o c m)
    (hex : ∀ (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState),
      th.regs = rf → RegTyped th.regs nP nR nRd →
      execNonBarrierInstr stmts cta th i = .ok (thStep th rf', cta.globalMem, cta.sharedMem, cta.epochLog)) :
    PureExec [ins i] nP nR nRd rf rf' := by
  intro hrt f stmts cta done todo localBytes tx pc saved hdone hslice
  have hpc : stmts[pc]? = some (.instr none i) := by simpa [ins] using hslice 0 (by simp)
  exact pure_lane_step f stmts cta done todo localBytes tx pc rf rf' i saved hdone hpc hnBar hnShfl
    (hex stmts _ (laneAt localBytes tx pc rf false) rfl hrt)

theorem u64_eq_bv (a b : UInt64) : (a.toBitVec == b.toBitVec) = (a == b) := by
  cases h : (a == b)
  · apply Bool.eq_false_iff.mpr
    intro heq; rw [UInt64.eq_of_toBitVec_eq (eq_of_beq heq), BEq.rfl] at h; cases h
  · rw [eq_of_beq h, BEq.rfl]

theorem u64_bne_zero_bv (a : UInt64) : (a.toBitVec != 0#64) = (a != 0) := by
  show (!(a.toBitVec == (0 : UInt64).toBitVec)) = (!(a == 0)); rw [u64_eq_bv]

theorem bool_word_bne_zero (b : Bool) :
    ((if b then (1#64 : BitVec 64) else 0#64) != 0#64) = b := by cases b <;> rfl

theorem u64_ult_bv (a b : UInt64) :
    BitVec.ult a.toBitVec b.toBitVec = decide (a < b) := by
  simp [BitVec.ult, UInt64.lt_iff_toNat_lt]

theorem u64_ule_bv (a b : UInt64) :
    BitVec.ule a.toBitVec b.toBitVec = decide (a ≤ b) := by
  simp [BitVec.ule, UInt64.le_iff_toNat_le]

private theorem mask_cvt_and63 (v : BitVec 64) :
    (((v &&& 0xFFFF_FFFF#64) &&& 0xFFFF_FFFF#64) &&& 63#64) &&& 0xFFFF_FFFF#64 = v &&& 63#64 := by
  have hc : (0xFFFF_FFFF#64 : BitVec 64) &&& 0xFFFF_FFFF#64 &&& 63#64 &&& 0xFFFF_FFFF#64 = 63#64 := rfl
  rw [BitVec.and_assoc v, BitVec.and_assoc v, BitVec.and_assoc v, hc]

private theorem and63_fit32 (v : BitVec 64) : ((v &&& 63#64) >>> 32) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, bv64_and_63_toNat]
  have hlt : v.toNat % 64 < 64 := Nat.mod_lt _ (by omega)
  change (v.toNat % 64) / 4294967296 = 0; omega

private theorem denom_guard_nz (vb : BitVec 64) :
    (if vb == 0#64 then (1#64 : BitVec 64) else vb) ≠ 0#64 := by
  cases h : (vb == 0#64)
  · simp only [Bool.false_eq_true, ite_false]
    exact fun heq => Bool.noConfusion (h.symm.trans (beq_iff_eq.mpr heq))
  · simp only [ite_true]
    intro heq; have := congrArg BitVec.toNat heq; simp at this

theorem lowerScalar_bounds_no_label (varOf : Nat → Option PReg) (boundVars : List Nat)
    (e0 : PEnv) (expr : ScalarExpr) (s : Bool)
    (hsort : inferScalarSort boundVars expr = some s)
    (hvar : ∀ id ∈ boundVars, ∃ k < e0.nextRd, varOf id = some (.rd k)) :
    let out := lowerScalar varOf e0 expr
    e0.nextRd ≤ out.2.2.nextRd ∧
      e0.nextR ≤ out.2.2.nextR ∧
      e0.nextP ≤ out.2.2.nextP ∧
      (∃ di < out.2.2.nextRd, out.2.1 = .rd di) ∧
      (∀ lbl, ∀ st ∈ out.1, st ≠ .label lbl) := by
  dsimp only
  induction expr generalizing e0 s with
  | constU64 v =>
    refine ⟨by simp [lowerScalar, freshRd], by simp [lowerScalar, freshRd],
      by simp [lowerScalar, freshRd], ⟨e0.nextRd, by simp [lowerScalar, freshRd], rfl⟩, ?_⟩
    intro lbl st hst
    simp [lowerScalar, freshRd, ins] at hst
    subst hst; simp
  | constBool b =>
    refine ⟨by simp [lowerScalar, freshRd], by simp [lowerScalar, freshRd],
      by simp [lowerScalar, freshRd], ⟨e0.nextRd, by simp [lowerScalar, freshRd], rfl⟩, ?_⟩
    intro lbl st hst
    simp [lowerScalar, freshRd, ins] at hst
    subst hst; simp
  | var id =>
    simp only [inferScalarSort] at hsort
    split at hsort
    · rename_i hmem
      rcases hvar id hmem with ⟨k, hk, hvk⟩
      simp only [lowerScalar, hvk]
      refine ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, ⟨k, hk, rfl⟩, ?_⟩
      intro _ _ h; cases h
    · cases hsort
  | unaryOp op a iha =>
    simp only [inferScalarSort] at hsort
    cases hsa : inferScalarSort boundVars a <;> simp only [hsa] at hsort
    · cases hsort
    · rename_i sa
      cases sa <;> simp at hsort
      have ih1 := iha e0 false hsa hvar
      rcases hA : lowerScalar varOf e0 a with ⟨al, ar, e1⟩
      simp only [hA] at ih1
      rcases ih1 with ⟨hrd1, hr1, hp1, _, hnl1⟩
      cases op with
      | clz256 => cases hsort
      | not =>
        simp only [lowerScalar, hA, freshRd]
        refine ⟨by omega, hr1, hp1, ⟨e1.nextRd, by omega, rfl⟩, ?_⟩
        intro lbl st hst; rcases List.mem_append.mp hst with h1 | h2
        · exact hnl1 lbl st h1
        · simp [ins] at h2; subst h2; simp
      | neg =>
        simp only [lowerScalar, hA, freshRd]
        refine ⟨by omega, hr1, hp1, ⟨e1.nextRd, by omega, rfl⟩, ?_⟩
        intro lbl st hst; rcases List.mem_append.mp hst with h1 | h2
        · exact hnl1 lbl st h1
        · simp [ins] at h2; subst h2; simp
  | binOp op l r ihl ihr =>
    simp only [inferScalarSort] at hsort
    cases hsl : inferScalarSort boundVars l <;> simp only [hsl] at hsort
    · cases hsort
    · cases hsr : inferScalarSort boundVars r <;> simp only [hsr] at hsort
      · cases hsort
      · rename_i sl sr
        have ih1 := ihl e0 sl hsl hvar
        rcases hL : lowerScalar varOf e0 l with ⟨ll, lr, e1⟩
        simp only [hL] at ih1
        rcases ih1 with ⟨hrd1, hr1, hp1, _, hnl1⟩
        have hvar1 : ∀ id ∈ boundVars, ∃ k < e1.nextRd, varOf id = some (.rd k) := by
          intro id hid; rcases hvar id hid with ⟨k, hk, hv⟩; exact ⟨k, Nat.lt_of_lt_of_le hk hrd1, hv⟩
        have ih2 := ihr e1 sr hsr hvar1
        rcases hR : lowerScalar varOf e1 r with ⟨rl, rr, e2⟩
        simp only [hR] at ih2
        rcases ih2 with ⟨hrd2, hr2, hp2, _, hnl2⟩
        have hnlLR : ∀ lbl, ∀ st ∈ ll ++ rl, st ≠ .label lbl := by
          intro lbl st hst; rcases List.mem_append.mp hst with h1 | h2
          · exact hnl1 lbl st h1
          · exact hnl2 lbl st h2
        cases sl
        · cases sr <;> try simp at hsort
          cases op <;> simp [inferBinOpU64] at hsort
          all_goals
            simp only [lowerScalar, hL, hR, freshRd, freshR, freshP]
            refine ⟨by omega, by omega, by omega, ⟨e2.nextRd, by omega, rfl⟩, ?_⟩
            intro lbl st hst; rcases List.mem_append.mp hst with h12 | htail
            · exact hnlLR lbl st h12
            · simp only [List.mem_cons, List.mem_nil_iff, or_false, ins] at htail
              rcases htail with rfl | rfl | rfl | rfl <;> simp
        · cases sr <;> try simp at hsort
          cases op <;> simp [inferBinOpBool] at hsort
          simp only [lowerScalar, hL, hR, freshRd, freshP]
          refine ⟨by omega, by omega, by omega, ⟨e2.nextRd, by omega, rfl⟩, ?_⟩
          intro lbl st hst; rcases List.mem_append.mp hst with h12 | htail
          · exact hnlLR lbl st h12
          · simp only [List.mem_cons, List.mem_nil_iff, or_false, ins] at htail
            rcases htail with rfl | rfl <;> simp
  | select c t f ihc iht ihf =>
    simp only [inferScalarSort] at hsort
    cases hsc : inferScalarSort boundVars c <;> simp only [hsc] at hsort
    · cases hsort
    · cases hst : inferScalarSort boundVars t <;> simp only [hst] at hsort
      · cases hsort
      · cases hsf : inferScalarSort boundVars f <;> simp only [hsf] at hsort
        · cases hsort
        · rename_i sc st sf
          have ih1 := ihc e0 sc hsc hvar
          rcases hC : lowerScalar varOf e0 c with ⟨cl, cr, e1⟩; simp only [hC] at ih1
          rcases ih1 with ⟨hrd1, hr1, hp1, _, hnl1⟩
          have hvar1 : ∀ id ∈ boundVars, ∃ k < e1.nextRd, varOf id = some (.rd k) := by
            intro id hid; rcases hvar id hid with ⟨k, hk, hv⟩; exact ⟨k, Nat.lt_of_lt_of_le hk hrd1, hv⟩
          have ih2 := iht e1 st hst hvar1
          rcases hT : lowerScalar varOf e1 t with ⟨tl, tr, e2⟩; simp only [hT] at ih2
          rcases ih2 with ⟨hrd2, hr2, hp2, _, hnl2⟩
          have hvar2 : ∀ id ∈ boundVars, ∃ k < e2.nextRd, varOf id = some (.rd k) := by
            intro id hid; rcases hvar1 id hid with ⟨k, hk, hv⟩; exact ⟨k, Nat.lt_of_lt_of_le hk hrd2, hv⟩
          have ih3 := ihf e2 sf hsf hvar2
          rcases hF : lowerScalar varOf e2 f with ⟨fl, fr, e3⟩; simp only [hF] at ih3
          rcases ih3 with ⟨hrd3, hr3, hp3, _, hnl3⟩
          simp only [lowerScalar, hC, hT, hF, freshP, freshRd]
          refine ⟨by omega, by omega, by omega, ⟨e3.nextRd, by omega, rfl⟩, ?_⟩
          intro lbl st0 hst0; rcases List.mem_append.mp hst0 with h123 | htail
          · rcases List.mem_append.mp h123 with h12 | h3
            · rcases List.mem_append.mp h12 with h1 | h2
              · exact hnl1 lbl st0 h1
              · exact hnl2 lbl st0 h2
            · exact hnl3 lbl st0 h3
          · simp only [List.mem_cons, List.mem_nil_iff, or_false, ins] at htail
            rcases htail with rfl | rfl <;> simp
  | fma a b c iha ihb ihc =>
    simp only [inferScalarSort] at hsort
    cases hsa : inferScalarSort boundVars a <;> simp only [hsa] at hsort
    · cases hsort
    · cases hsb : inferScalarSort boundVars b <;> simp only [hsb] at hsort
      · cases hsort
      · cases hsc : inferScalarSort boundVars c <;> simp only [hsc] at hsort
        · cases hsort
        · rename_i sa sb sc
          have ih1 := iha e0 sa hsa hvar
          rcases hA : lowerScalar varOf e0 a with ⟨al, ar, e1⟩; simp only [hA] at ih1
          rcases ih1 with ⟨hrd1, hr1, hp1, _, hnl1⟩
          have hvar1 : ∀ id ∈ boundVars, ∃ k < e1.nextRd, varOf id = some (.rd k) := by
            intro id hid; rcases hvar id hid with ⟨k, hk, hv⟩; exact ⟨k, Nat.lt_of_lt_of_le hk hrd1, hv⟩
          have ih2 := ihb e1 sb hsb hvar1
          rcases hB : lowerScalar varOf e1 b with ⟨bl, br, e2⟩; simp only [hB] at ih2
          rcases ih2 with ⟨hrd2, hr2, hp2, _, hnl2⟩
          have hvar2 : ∀ id ∈ boundVars, ∃ k < e2.nextRd, varOf id = some (.rd k) := by
            intro id hid; rcases hvar1 id hid with ⟨k, hk, hv⟩; exact ⟨k, Nat.lt_of_lt_of_le hk hrd2, hv⟩
          have ih3 := ihc e2 sc hsc hvar2
          rcases hC : lowerScalar varOf e2 c with ⟨cl, cr, e3⟩; simp only [hC] at ih3
          rcases ih3 with ⟨hrd3, hr3, hp3, _, hnl3⟩
          simp only [lowerScalar, hA, hB, hC, freshRd]
          refine ⟨by omega, by omega, by omega, ⟨e3.nextRd, by omega, rfl⟩, ?_⟩
          intro lbl st0 hst0; rcases List.mem_append.mp hst0 with h123 | htail
          · rcases List.mem_append.mp h123 with h12 | h3
            · rcases List.mem_append.mp h12 with h1 | h2
              · exact hnl1 lbl st0 h1
              · exact hnl2 lbl st0 h2
            · exact hnl3 lbl st0 h3
          · simp only [List.mem_cons, List.mem_nil_iff, or_false, ins] at htail
            subst htail; simp

theorem exec_tail_shift (isShl isSar : Bool) {nP nR nRd di li ri si : Nat}
    (hdi : di < nRd) (hli : li < di) (hri : ri < di) (hsi1 : si + 1 < nR)
    (xl xr : UInt64) (rf : PTXRegFile)
    (hll : rf.regs.lookup s!"%rd{li}" = some (.scalar xl.toBitVec))
    (hlr : rf.regs.lookup s!"%rd{ri}" = some (.scalar xr.toBitVec)) :
    ∃ rf' : PTXRegFile,
      RegFramePres di rf rf' ∧
      rf'.regs.lookup s!"%rd{di}" = some (.scalar
        (if isShl then (xl <<< xr).toBitVec
         else if isSar then (lnirSar64 xl xr).toBitVec
         else (xl >>> xr).toBitVec)) ∧
      PureExec [
        ins (.cvt .none .u32 .u64 s!"%r{si}" (.reg s!"%rd{ri}")),
        ins (.bitAnd .b32 s!"%r{si + 1}" (.reg s!"%r{si}") (.immU64 63#64)),
        ins (if isShl then .shl .b64 s!"%rd{di}" (.reg s!"%rd{li}") (.reg s!"%r{si + 1}")
             else if isSar then .shr .s64 s!"%rd{di}" (.reg s!"%rd{li}") (.reg s!"%r{si + 1}")
             else .shr .u64 s!"%rd{di}" (.reg s!"%rd{li}") (.reg s!"%r{si + 1}"))
      ] nP nR nRd rf rf' := by
  have hsi : si < nR := by omega
  have hliR : li < nRd := by omega
  have hriR : ri < nRd := by omega
  let rf1 := rf.setScalarRaw s!"%r{si}" ((xr.toBitVec &&& 0xFFFF_FFFF#64) &&& 0xFFFF_FFFF#64)
  let rf2 := rf1.setScalarRaw s!"%r{si + 1}" (xr.toBitVec &&& 63#64)
  have hf1 : RegFramePres di rf rf1 := regFrame_setR rf di si _
  have hf2 : RegFramePres di rf1 rf2 := regFrame_setR rf1 di (si + 1) _
  have hf12 : RegFramePres di rf rf2 := regFrame_trans hf1 hf2 (Nat.le_refl _)
  have hs1 : PureExec [ins (.cvt .none .u32 .u64 s!"%r{si}" (.reg s!"%rd{ri}"))] nP nR nRd rf rf1 :=
    pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => by
      have hex := exec_cvt_u32_u64 s c t hrt si ri hsi hriR xr.toBitVec (by rw [hrf]; exact hlr)
      rw [hrf] at hex; exact hex
  have hs2 : PureExec [ins (.bitAnd .b32 s!"%r{si + 1}" (.reg s!"%r{si}") (.immU64 63#64))] nP nR nRd rf1 rf2 :=
    pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => by
      have hex := exec_bitAnd_r_imm s c t hrt (si + 1) si hsi1 hsi _ 63#64
        (by rw [hrf]; exact lookup_r_self rf si _)
      rw [mask_cvt_and63] at hex
      rw [hrf] at hex; exact hex
  have hll2 : rf2.regs.lookup s!"%rd{li}" = some (.scalar xl.toBitVec) := (hf12.rd_eq li hli).trans hll
  have hls2 : rf2.regs.lookup s!"%r{si + 1}" = some (.scalar (xr.toBitVec &&& 63#64)) :=
    lookup_r_self rf1 (si + 1) _
  have hfit := and63_fit32 xr.toBitVec
  have hlt := bv64_and_63_lt_64 xr.toBitVec
  cases isShl
  · cases isSar
    · refine ⟨rf2.setScalarRaw s!"%rd{di}" ((xl >>> xr).toBitVec),
        regFrame_trans hf12 (regFrame_setRd rf2 (Nat.le_refl _) _) (Nat.le_refl _),
        lookup_rd_self rf2 di _, ?_⟩
      have hs3 : PureExec [ins (.shr .u64 s!"%rd{di}" (.reg s!"%rd{li}") (.reg s!"%r{si + 1}"))]
          nP nR nRd rf2 (rf2.setScalarRaw s!"%rd{di}" ((xl >>> xr).toBitVec)) :=
        pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => by
          have hex := exec_shr_u64 s c t hrt di li (si + 1) hdi hliR hsi1 xl.toBitVec _ hfit hlt
            (by rw [hrf]; exact hll2) (by rw [hrf]; exact hls2)
          rw [← BitVec.ushiftRight_eq', u64_shr_masked_bv, hrf] at hex
          exact hex
      exact pureExec_append hs1 hf1 (pureExec_append hs2 hf2 hs3)
    · refine ⟨rf2.setScalarRaw s!"%rd{di}" ((lnirSar64 xl xr).toBitVec),
        regFrame_trans hf12 (regFrame_setRd rf2 (Nat.le_refl _) _) (Nat.le_refl _),
        lookup_rd_self rf2 di _, ?_⟩
      have hs3 : PureExec [ins (.shr .s64 s!"%rd{di}" (.reg s!"%rd{li}") (.reg s!"%r{si + 1}"))]
          nP nR nRd rf2 (rf2.setScalarRaw s!"%rd{di}" ((lnirSar64 xl xr).toBitVec)) :=
        pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => by
          have hex := exec_shr_s64 s c t hrt di li (si + 1) hdi hliR hsi1 xl.toBitVec _ hfit hlt
            (by rw [hrf]; exact hll2) (by rw [hrf]; exact hls2)
          rw [u64_ashr_masked_bv, hrf] at hex
          exact hex
      exact pureExec_append hs1 hf1 (pureExec_append hs2 hf2 hs3)
  · refine ⟨rf2.setScalarRaw s!"%rd{di}" ((xl <<< xr).toBitVec),
      regFrame_trans hf12 (regFrame_setRd rf2 (Nat.le_refl _) _) (Nat.le_refl _),
      lookup_rd_self rf2 di _, ?_⟩
    have hs3 : PureExec [ins (.shl .b64 s!"%rd{di}" (.reg s!"%rd{li}") (.reg s!"%r{si + 1}"))]
        nP nR nRd rf2 (rf2.setScalarRaw s!"%rd{di}" ((xl <<< xr).toBitVec)) :=
      pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => by
        have hex := exec_shl_rd s c t hrt di li (si + 1) hdi hliR hsi1 xl.toBitVec _ hfit hlt
          (by rw [hrf]; exact hll2) (by rw [hrf]; exact hls2)
        rw [← BitVec.shiftLeft_eq', u64_shl_masked_bv, hrf] at hex
        exact hex
    exact pureExec_append hs1 hf1 (pureExec_append hs2 hf2 hs3)

theorem exec_tail_divmod (isMod : Bool) {nP nR nRd di li ri pi : Nat}
    (hdi : di < nRd) (hli : li < di) (hri : ri < di) (hpi : pi < nP)
    (xl xr : UInt64) (rf : PTXRegFile)
    (hll : rf.regs.lookup s!"%rd{li}" = some (.scalar xl.toBitVec))
    (hlr : rf.regs.lookup s!"%rd{ri}" = some (.scalar xr.toBitVec)) :
    ∃ rf' : PTXRegFile,
      RegFramePres di rf rf' ∧
      rf'.regs.lookup s!"%rd{di}" =
        some (.scalar (if isMod then (xl % xr).toBitVec else (xl / xr).toBitVec)) ∧
      PureExec [
        ins (.setp .eq .u64 s!"%p{pi}" (.reg s!"%rd{ri}") (i64 0)),
        ins (.selp .u64 s!"%rd{di}" (i64 1) (.reg s!"%rd{ri}") s!"%p{pi}"),
        ins (if isMod then .rem .u64 s!"%rd{di}" (.reg s!"%rd{li}") (.reg s!"%rd{di}")
             else .div .u64 s!"%rd{di}" (.reg s!"%rd{li}") (.reg s!"%rd{di}")),
        ins (if isMod then .selp .u64 s!"%rd{di}" (.reg s!"%rd{li}") (.reg s!"%rd{di}") s!"%p{pi}"
             else .selp .u64 s!"%rd{di}" (i64 0) (.reg s!"%rd{di}") s!"%p{pi}")
      ] nP nR nRd rf rf' := by
  have hliR : li < nRd := by omega
  have hriR : ri < nRd := by omega
  let zf := xr.toBitVec == 0#64
  let denom := if zf then 1#64 else xr.toBitVec
  let rf1 := rf.setPredRaw s!"%p{pi}" zf
  let rf2 := rf1.setScalarRaw s!"%rd{di}" denom
  have hf1 : RegFramePres di rf rf1 := regFrame_setP rf di pi zf
  have hf2 : RegFramePres di rf1 rf2 := regFrame_setRd rf1 (Nat.le_refl _) denom
  have hf12 : RegFramePres di rf rf2 := regFrame_trans hf1 hf2 (Nat.le_refl _)
  have hs1 : PureExec [ins (.setp .eq .u64 s!"%p{pi}" (.reg s!"%rd{ri}") (i64 0))] nP nR nRd rf rf1 :=
    pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => by
      have hex := exec_setp_imm s c t hrt .eq pi ri hpi hriR xr.toBitVec 0#64 (by rw [hrf]; exact hlr)
      rw [hrf] at hex; exact hex
  have hs2 : PureExec [ins (.selp .u64 s!"%rd{di}" (i64 1) (.reg s!"%rd{ri}") s!"%p{pi}")] nP nR nRd rf1 rf2 :=
    pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => by
      have hex := exec_selp_imm_rd s c t hrt di ri pi hdi hriR hpi 1#64 xr.toBitVec zf
        (by rw [hrf]; exact (hf1.rd_eq ri hri).trans hlr)
        (by rw [hrf]; exact lookup_p_self rf pi zf)
      rw [hrf] at hex; exact hex
  have hll2 : rf2.regs.lookup s!"%rd{li}" = some (.scalar xl.toBitVec) := (hf12.rd_eq li hli).trans hll
  have hld2 : rf2.regs.lookup s!"%rd{di}" = some (.scalar denom) := lookup_rd_self rf1 di denom
  have hlp2 : rf2.regs.lookup s!"%p{pi}" = some (.pred zf) := by
    unfold rf2 PTXRegFile.setScalarRaw
    rw [setAssoc_lookup_ne _ _ _ _ (p_ne_rd pi di)]
    exact lookup_p_self rf pi zf
  have hnz : denom ≠ 0#64 := denom_guard_nz xr.toBitVec
  cases isMod
  · let rf3 := rf2.setScalarRaw s!"%rd{di}" (xl.toBitVec / denom)
    let rf4 := rf3.setScalarRaw s!"%rd{di}" ((xl / xr).toBitVec)
    have hf3 : RegFramePres di rf2 rf3 := regFrame_setRd rf2 (Nat.le_refl _) _
    have hf4 : RegFramePres di rf3 rf4 := regFrame_setRd rf3 (Nat.le_refl _) _
    have hlp3 : rf3.regs.lookup s!"%p{pi}" = some (.pred zf) := by
      unfold rf3 PTXRegFile.setScalarRaw
      rw [setAssoc_lookup_ne _ _ _ _ (p_ne_rd pi di)]; exact hlp2
    have hs3 : PureExec [ins (.div .u64 s!"%rd{di}" (.reg s!"%rd{li}") (.reg s!"%rd{di}"))] nP nR nRd rf2 rf3 :=
      pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => by
        have hex := exec_div_u64 s c t hrt di li di hdi hliR hdi xl.toBitVec denom hnz
          (by rw [hrf]; exact hll2) (by rw [hrf]; exact hld2)
        rw [hrf] at hex; exact hex
    have hs4 : PureExec [ins (.selp .u64 s!"%rd{di}" (i64 0) (.reg s!"%rd{di}") s!"%p{pi}")] nP nR nRd rf3 rf4 :=
      pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => by
        have hex := exec_selp_imm_rd s c t hrt di di pi hdi hdi hpi 0#64 (xl.toBitVec / denom) zf
          (by rw [hrf]; exact lookup_rd_self rf2 di _) (by rw [hrf]; exact hlp3)
        rw [u64_div_guarded_bv, hrf] at hex
        exact hex
    exact ⟨rf4, regFrame_trans hf12 (regFrame_trans hf3 hf4 (Nat.le_refl _)) (Nat.le_refl _),
      lookup_rd_self rf3 di _, pureExec_append hs1 hf1 (pureExec_append hs2 hf2 (pureExec_append hs3 hf3 hs4))⟩
  · let rf3 := rf2.setScalarRaw s!"%rd{di}" (xl.toBitVec % denom)
    let rf4 := rf3.setScalarRaw s!"%rd{di}" ((xl % xr).toBitVec)
    have hf3 : RegFramePres di rf2 rf3 := regFrame_setRd rf2 (Nat.le_refl _) _
    have hf4 : RegFramePres di rf3 rf4 := regFrame_setRd rf3 (Nat.le_refl _) _
    have hll3 : rf3.regs.lookup s!"%rd{li}" = some (.scalar xl.toBitVec) := (hf3.rd_eq li hli).trans hll2
    have hlp3 : rf3.regs.lookup s!"%p{pi}" = some (.pred zf) := by
      unfold rf3 PTXRegFile.setScalarRaw
      rw [setAssoc_lookup_ne _ _ _ _ (p_ne_rd pi di)]; exact hlp2
    have hs3 : PureExec [ins (.rem .u64 s!"%rd{di}" (.reg s!"%rd{li}") (.reg s!"%rd{di}"))] nP nR nRd rf2 rf3 :=
      pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => by
        have hex := exec_rem_u64 s c t hrt di li di hdi hliR hdi xl.toBitVec denom hnz
          (by rw [hrf]; exact hll2) (by rw [hrf]; exact hld2)
        rw [hrf] at hex; exact hex
    have hs4 : PureExec [ins (.selp .u64 s!"%rd{di}" (.reg s!"%rd{li}") (.reg s!"%rd{di}") s!"%p{pi}")]
        nP nR nRd rf3 rf4 :=
      pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => by
        have hex := exec_selp_rd s c t hrt di li di pi hdi hliR hdi hpi xl.toBitVec (xl.toBitVec % denom) zf
          (by rw [hrf]; exact hll3)
          (by rw [hrf]; exact lookup_rd_self rf2 di _)
          (by rw [hrf]; exact hlp3)
        rw [u64_mod_guarded_bv, hrf] at hex
        exact hex
    exact ⟨rf4, regFrame_trans hf12 (regFrame_trans hf3 hf4 (Nat.le_refl _)) (Nat.le_refl _),
      lookup_rd_self rf3 di _, pureExec_append hs1 hf1 (pureExec_append hs2 hf2 (pureExec_append hs3 hf3 hs4))⟩

theorem exec_tail_eor3 {nP nR nRd di li ri : Nat}
    (hdi1 : di + 1 < nRd) (hli : li < di) (hri : ri < di)
    (xl xr : UInt64) (rf : PTXRegFile)
    (hll : rf.regs.lookup s!"%rd{li}" = some (.scalar xl.toBitVec))
    (hlr : rf.regs.lookup s!"%rd{ri}" = some (.scalar xr.toBitVec)) :
    ∃ rf' : PTXRegFile,
      RegFramePres di rf rf' ∧
      rf'.regs.lookup s!"%rd{di}" =
        some (.scalar ((xl ^^^ (xr >>> 32)) ^^^ (xr &&& 0xffffffff)).toBitVec) ∧
      PureExec [
        ins (.shr .u64 s!"%rd{di + 1}" (.reg s!"%rd{ri}") (i64 32)),
        ins (.bitXor .b64 s!"%rd{di}" (.reg s!"%rd{li}") (.reg s!"%rd{di + 1}")),
        ins (.bitAnd .b64 s!"%rd{di + 1}" (.reg s!"%rd{ri}") (i64 4294967295)),
        ins (.bitXor .b64 s!"%rd{di}" (.reg s!"%rd{di}") (.reg s!"%rd{di + 1}"))
      ] nP nR nRd rf rf' := by
  have hdi : di < nRd := by omega
  have hliR : li < nRd := by omega
  have hriR : ri < nRd := by omega
  let rf1 := rf.setScalarRaw s!"%rd{di + 1}" (xr.toBitVec >>> 32)
  let rf2 := rf1.setScalarRaw s!"%rd{di}" (xl.toBitVec ^^^ (xr.toBitVec >>> 32))
  let rf3 := rf2.setScalarRaw s!"%rd{di + 1}" (xr.toBitVec &&& 4294967295#64)
  let rf4 := rf3.setScalarRaw s!"%rd{di}"
    ((xl.toBitVec ^^^ (xr.toBitVec >>> 32)) ^^^ (xr.toBitVec &&& 4294967295#64))
  have hf1 : RegFramePres di rf rf1 := regFrame_setRd rf (by omega) _
  have hf2 : RegFramePres di rf1 rf2 := regFrame_setRd rf1 (Nat.le_refl _) _
  have hf3 : RegFramePres di rf2 rf3 := regFrame_setRd rf2 (by omega) _
  have hf4 : RegFramePres di rf3 rf4 := regFrame_setRd rf3 (Nat.le_refl _) _
  have hs1 : PureExec [ins (.shr .u64 s!"%rd{di + 1}" (.reg s!"%rd{ri}") (i64 32))] nP nR nRd rf rf1 :=
    pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => by
      have hex := exec_shr_u64_imm s c t hrt (di + 1) ri 32 hdi1 hriR (by omega) xr.toBitVec (by rw [hrf]; exact hlr)
      rw [hrf] at hex; exact hex
  have hs2 : PureExec [ins (.bitXor .b64 s!"%rd{di}" (.reg s!"%rd{li}") (.reg s!"%rd{di + 1}"))]
      nP nR nRd rf1 rf2 :=
    pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => by
      have hex := exec_bitXor_rd s c t hrt di li (di + 1) hdi hliR hdi1 xl.toBitVec (xr.toBitVec >>> 32)
        (by rw [hrf]; exact (hf1.rd_eq li hli).trans hll) (by rw [hrf]; exact lookup_rd_self rf (di + 1) _)
      rw [hrf] at hex; exact hex
  have hlr2 : rf2.regs.lookup s!"%rd{ri}" = some (.scalar xr.toBitVec) :=
    ((regFrame_trans hf1 hf2 (Nat.le_refl _)).rd_eq ri hri).trans hlr
  have hs3 : PureExec [ins (.bitAnd .b64 s!"%rd{di + 1}" (.reg s!"%rd{ri}") (i64 4294967295))]
      nP nR nRd rf2 rf3 :=
    pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => by
      have hex := exec_bitAnd_imm s c t hrt (di + 1) ri hdi1 hriR xr.toBitVec 4294967295#64 (by rw [hrf]; exact hlr2)
      rw [hrf] at hex; exact hex
  have hld3 : rf3.regs.lookup s!"%rd{di}" = some (.scalar (xl.toBitVec ^^^ (xr.toBitVec >>> 32))) :=
    (lookup_rd_ne rf2 (by omega) _).trans (lookup_rd_self rf1 di _)
  have hs4 : PureExec [ins (.bitXor .b64 s!"%rd{di}" (.reg s!"%rd{di}") (.reg s!"%rd{di + 1}"))]
      nP nR nRd rf3 rf4 :=
    pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => by
      have hex := exec_bitXor_rd s c t hrt di di (di + 1) hdi hdi hdi1 _ _
        (by rw [hrf]; exact hld3) (by rw [hrf]; exact lookup_rd_self rf2 (di + 1) _)
      rw [hrf] at hex; exact hex
  exact ⟨rf4,
    regFrame_trans hf1 (regFrame_trans hf2 (regFrame_trans hf3 hf4 (Nat.le_refl _)) (Nat.le_refl _)) (Nat.le_refl _),
    lookup_rd_self rf3 di _,
    pureExec_append hs1 hf1 (pureExec_append hs2 hf2 (pureExec_append hs3 hf3 hs4))⟩

theorem exec_tail_cmp (cmp : PTXCmpOp) {nP nR nRd di li ri pi : Nat}
    (hdi : di < nRd) (hli : li < di) (hri : ri < di) (hpi : pi < nP)
    (va vb : BitVec 64) (rf : PTXRegFile)
    (hll : rf.regs.lookup s!"%rd{li}" = some (.scalar va))
    (hlr : rf.regs.lookup s!"%rd{ri}" = some (.scalar vb)) :
    ∃ rf' : PTXRegFile,
      RegFramePres di rf rf' ∧
      rf'.regs.lookup s!"%rd{di}" =
        some (.scalar (if evalPTXCmp cmp .u64 va vb then 1#64 else 0#64)) ∧
      PureExec [
        ins (.setp cmp .u64 s!"%p{pi}" (.reg s!"%rd{li}") (.reg s!"%rd{ri}")),
        ins (.selp .u64 s!"%rd{di}" (i64 1) (i64 0) s!"%p{pi}")
      ] nP nR nRd rf rf' := by
  let flag := evalPTXCmp cmp .u64 va vb
  let rf1 := rf.setPredRaw s!"%p{pi}" flag
  let rf2 := rf1.setScalarRaw s!"%rd{di}" (if flag then 1#64 else 0#64)
  have hf1 : RegFramePres di rf rf1 := regFrame_setP rf di pi flag
  have hf2 : RegFramePres di rf1 rf2 := regFrame_setRd rf1 (Nat.le_refl _) _
  have hs1 : PureExec [ins (.setp cmp .u64 s!"%p{pi}" (.reg s!"%rd{li}") (.reg s!"%rd{ri}"))]
      nP nR nRd rf rf1 :=
    pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => by
      have hex := exec_setp_rd s c t hrt cmp pi li ri hpi (by omega) (by omega) va vb
        (by rw [hrf]; exact hll) (by rw [hrf]; exact hlr)
      rw [hrf] at hex; exact hex
  have hs2 : PureExec [ins (.selp .u64 s!"%rd{di}" (i64 1) (i64 0) s!"%p{pi}")] nP nR nRd rf1 rf2 :=
    pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun s c t hrf hrt => by
      have hex := exec_selp_imm s c t hrt di pi hdi hpi 1#64 0#64 flag (by rw [hrf]; exact lookup_p_self rf pi flag)
      rw [hrf] at hex; exact hex
  exact ⟨rf2, regFrame_trans hf1 hf2 (Nat.le_refl _), lookup_rd_self rf1 di _, pureExec_append hs1 hf1 hs2⟩

end LeanNative.Proofs.PTXScalarProofs
