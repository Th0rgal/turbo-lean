import LeanNative.Proofs.PTXLowerProofs1

/-!
# `stencil1D3Pt` `MidBodySpec` Proofs (`LeanNative.Proofs.PTXLowerProofs2`)

Proves `MidBodySpec` for `.stencil1D3Pt` (branching boundary guard + interior 3-point
neighborhood loads) (`0 sorryAx`, `0 ofReduceBool`).
-/

namespace LeanNative.Proofs.PTXLowerProofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend
open LeanNative.Backend.PTXAst
open LeanNative.Proofs.PTXSIMT
open LeanNative.Backend.PTXLower
open LeanNative.Proofs.PTXScalarProofs

def stencilMid (bnd : String) (wL wC wR : UInt64) : List PTXStmt :=
  [ ins (.ldParam .u64 "%rd8" "param_in0")
  , ins (.cvtaToGlobal .u64 "%rd8" (.reg "%rd8"))
  , ins (.add .none .u64 "%rd8" (.reg "%rd8") (.reg "%rd5"))
  , ins (.ldGlobal .u64 "%rd7" (.regOffset "%rd8" 0))
  , ins (.setp .eq .u64 "%p1" (.reg "%rd2") (i64 0))
  , ins (.add .none .u64 "%rd9" (.reg "%rd2") (i64 1))
  , ins (.setp .ge .u64 "%p2" (.reg "%rd9") (.reg "%rd3"))
  , ins (.bitOr .pred "%p1" (.reg "%p1") (.reg "%p2"))
  , .instr (some { predReg := "%p1" }) (.bra bnd)
  , ins (.ldGlobal .u64 "%rd10" (.regOffset "%rd8" (-8)))
  , ins (.ldGlobal .u64 "%rd11" (.regOffset "%rd8" 8))
  , ins (.mul .lo .u64 "%rd12" (.reg "%rd10") (.immU64 wL.toBitVec))
  , ins (.mad .lo .u64 "%rd12" (.reg "%rd7") (.immU64 wC.toBitVec) (.reg "%rd12"))
  , ins (.mad .lo .u64 "%rd7" (.reg "%rd11") (.immU64 wR.toBitVec) (.reg "%rd12"))
  , .label bnd ]

theorem stencilMid_no_doneLbl (name : String) (wL wC wR : UInt64) :
    ∀ s ∈ stencilMid s!"$L_boundary_{name}" wL wC wR, s ≠ .label s!"$L_done_{name}" := by
  intro s hs
  simp only [stencilMid, List.mem_cons, List.mem_nil_iff, or_false, ins] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro h; nomatch h
  · intro h; nomatch h
  · intro h; nomatch h
  · intro h; nomatch h
  · intro h; nomatch h
  · intro h; nomatch h
  · intro h; nomatch h
  · intro h; nomatch h
  · intro h; nomatch h
  · intro h; nomatch h
  · intro h; nomatch h
  · intro h; nomatch h
  · intro h; nomatch h
  · intro h; nomatch h
  · intro h
    injection h with hs'
    have h1 : (s!"$L_boundary_{name}").toList[3]? = (s!"$L_done_{name}").toList[3]? :=
      congrArg (fun x => x.toList[3]?) hs'
    have hs1 : s!"$L_boundary_{name}" = "$L_boundary_" ++ name := rfl
    have hs2 : s!"$L_done_{name}" = "$L_done_" ++ name := rfl
    rw [hs1, hs2] at h1
    simp [String.toList_append] at h1

private theorem find_bnd_pc (name : String) (wL wC wR : UInt64) (epilogue : List PTXStmt) :
    findLabelPC?
      (stdGidSetup s!"$L_done_{name}" ++ stencilMid s!"$L_boundary_{name}" wL wC wR ++ epilogue)
      s!"$L_boundary_{name}" = some 28 := by
  let doneLbl := s!"$L_done_{name}"
  let bnd := s!"$L_boundary_{name}"
  let pre14 : List PTXStmt :=
    [ ins (.ldParam .u64 "%rd8" "param_in0")
    , ins (.cvtaToGlobal .u64 "%rd8" (.reg "%rd8"))
    , ins (.add .none .u64 "%rd8" (.reg "%rd8") (.reg "%rd5"))
    , ins (.ldGlobal .u64 "%rd7" (.regOffset "%rd8" 0))
    , ins (.setp .eq .u64 "%p1" (.reg "%rd2") (i64 0))
    , ins (.add .none .u64 "%rd9" (.reg "%rd2") (i64 1))
    , ins (.setp .ge .u64 "%p2" (.reg "%rd9") (.reg "%rd3"))
    , ins (.bitOr .pred "%p1" (.reg "%p1") (.reg "%p2"))
    , .instr (some { predReg := "%p1" }) (.bra bnd)
    , ins (.ldGlobal .u64 "%rd10" (.regOffset "%rd8" (-8)))
    , ins (.ldGlobal .u64 "%rd11" (.regOffset "%rd8" 8))
    , ins (.mul .lo .u64 "%rd12" (.reg "%rd10") (.immU64 wL.toBitVec))
    , ins (.mad .lo .u64 "%rd12" (.reg "%rd7") (.immU64 wC.toBitVec) (.reg "%rd12"))
    , ins (.mad .lo .u64 "%rd7" (.reg "%rd11") (.immU64 wR.toBitVec) (.reg "%rd12")) ]
  have hEq : stdGidSetup doneLbl ++ stencilMid bnd wL wC wR ++ epilogue =
      (stdGidSetup doneLbl ++ pre14) ++ (.label bnd :: epilogue) := by
    simp [stencilMid, pre14, List.append_assoc]
  have hno : ∀ s ∈ stdGidSetup doneLbl ++ pre14, s ≠ .label bnd := by
    intro s hs; rcases List.mem_append.mp hs with h1 | h2
    · exact gid_no_label doneLbl bnd s h1
    · simp only [pre14, List.mem_cons, List.mem_nil_iff, or_false, ins] at h2
      rcases h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  rw [hEq, findLabelPC_at_split (stdGidSetup doneLbl ++ pre14) epilogue bnd hno]
  rfl

private theorem pred_eq_zero_u64 (n : Nat) (hn : n < 2 ^ 64) :
    evalPTXCmp .eq .u64 (BitVec.ofNat 64 n) (BitVec.ofNat 64 0) = (n == 0) := by
  change (BitVec.ofNat 64 n == BitVec.ofNat 64 0) = (n == 0)
  cases h : (n == 0)
  · apply Bool.eq_false_iff.mpr
    intro heq
    have htn := congrArg BitVec.toNat (eq_of_beq heq)
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at htn
    have : (n == 0) = true := beq_iff_eq.mpr htn
    rw [this] at h; cases h
  · rw [eq_of_beq h]; rfl

private theorem stencil_mad_eq (wL wC wR xL xC xR : BitVec 64) :
    xR * wR + (xC * wC + xL * wL) = wL * xL + wC * xC + wR * xR := by
  rw [BitVec.mul_comm xR wR, BitVec.mul_comm xC wC, BitVec.mul_comm xL wL,
      BitVec.add_comm (wC * xC) (wL * xL), BitVec.add_comm (wR * xR) _]

private theorem stencil_pure_step (f pc : Nat) (stmts : List PTXStmt) (cta : PTXCTAState)
    (done todo : List PTXThreadState) (tx : Nat) (rf rf' : PTXRegFile)
    (op : PTXInstr) (saved : List MemAccessLog)
    (hdone : ∀ t ∈ done, t.halted = true)
    (hpc : stmts[pc]? = some (.instr none op))
    (hnBar : ∀ b, op ≠ .barSync b) (hnShfl : ∀ d s o c m, op ≠ .shflSyncBfly d s o c m)
    (hex : ∀ (c : PTXCTAState) (t : PTXThreadState),
      c.paramMem = cta.paramMem → t.regs = rf →
      execNonBarrierInstr stmts c t op =
        .ok (thStep t rf', c.globalMem, c.sharedMem, c.epochLog)) :
    runCTAWithGlobalLog (f + 1) stmts
      { cta with threads := done ++ (laneAt 0 tx pc rf false :: todo) } saved =
    runCTAWithGlobalLog f stmts
      { cta with threads := done ++ (laneAt 0 tx (pc + 1) rf' false :: todo) } saved :=
  pure_lane_step f stmts cta done todo 0 tx pc rf rf' op saved hdone hpc hnBar hnShfl
    (hex { cta with threads := done ++ (laneAt 0 tx pc rf false :: todo) }
      (laneAt 0 tx pc rf false) rfl rfl)

private theorem run_stencil_head (len tx gid : Nat) (name : String) (wL wC wR : UInt64)
    (epilogue : List PTXStmt) (cta : PTXCTAState) (done todo : List PTXThreadState)
    (saved : List MemAccessLog) (allowedLanes : Nat → Prop) (laneOf : Dim3 → Nat)
    (rfG : PTXRegFile) (xC : BitVec 64)
    (hrtG : RegTyped rfG 3 3 13)
    (hgidLt : gid < len) (houn : (1 + 1) * len * 8 ≤ 2 ^ 64)
    (hdone : ∀ t ∈ done, t.halted = true)
    (hp0 : cta.paramMem.lookupParam? "param_in0" = some (BitVec.ofNat 64 0))
    (hldC : cta.globalMem.loadBits (gid * 8) 8 = some xC)
    (hlk2G : rfG.regs.lookup "%rd2" = some (.scalar (BitVec.ofNat 64 gid)))
    (hlk3G : rfG.regs.lookup "%rd3" = some (.scalar (BitVec.ofNat 64 len)))
    (hlk5G : rfG.regs.lookup "%rd5" = some (.scalar (BitVec.ofNat 64 (gid * 8))))
    (hlk6G : rfG.regs.lookup "%rd6" = some (.scalar (BitVec.ofNat 64 (1 * len * 8 + gid * 8))))
    (hlog : SafePTXLog (1 * len * 8) len allowedLanes laneOf cta.epochLog) :
    let stmts := stdGidSetup s!"$L_done_{name}" ++ stencilMid s!"$L_boundary_{name}" wL wC wR ++ epilogue
    let cond := (gid == 0) || decide (len ≤ gid + 1)
    let eC : MemAccessLog := {
      tid := { x := tx, y := 0, z := 0 }, space := .global, addr := gid * 8,
      width := 8, isWrite := false, isAtomic := false }
    ∃ rf21 : PTXRegFile,
      RegTyped rf21 3 3 13 ∧
      rf21.regs.lookup "%rd6" = some (.scalar (BitVec.ofNat 64 (1 * len * 8 + gid * 8))) ∧
      rf21.regs.lookup "%rd7" = some (.scalar xC) ∧
      rf21.regs.lookup "%rd8" = some (.scalar (BitVec.ofNat 64 (gid * 8))) ∧
      PTXLogOk (1 * len * 8) len allowedLanes laneOf (eC :: cta.epochLog) ∧
      ∀ f,
      runCTAWithGlobalLog (f + 9) stmts
        { cta with threads := done ++ (laneAt 0 tx 13 rfG false :: todo) } saved =
      runCTAWithGlobalLog f stmts
        { cta with
          threads := done ++ (laneAt 0 tx (if cond then 28 else 22) rf21 false :: todo)
          epochLog := eC :: cta.epochLog } saved := by
  intro stmts cond eC
  let doneLbl := s!"$L_done_{name}"
  let bnd := s!"$L_boundary_{name}"
  have hlen64 : len < 2 ^ 64 := by omega
  have hgid64 : gid < 2 ^ 64 := by omega
  have hgid1_64 : gid + 1 < 2 ^ 64 := by omega
  have hg8_64 : gid * 8 < 2 ^ 64 := by omega
  have hinC : gid * 8 + 8 ≤ 1 * len * 8 := by omega
  have hpc (k : Nat) (hk : k < 15) : stmts[13 + k]? = (stencilMid bnd wL wC wR)[k]? :=
    sliceAt_mid_split (stdGidSetup doneLbl) (stencilMid bnd wL wC wR) epilogue k hk
  let r14 := rfSet rfG "%rd8" (BitVec.ofNat 64 0)
  let r16 := rfSet r14 "%rd8" (BitVec.ofNat 64 (gid * 8))
  let r17 := rfSet r16 "%rd7" xC
  let b0 := gid == 0
  let b1 := decide (len ≤ gid + 1)
  let r18 := r17.setPredRaw "%p1" b0
  let r19 := rfSet r18 "%rd9" (BitVec.ofNat 64 (gid + 1))
  let r20 := r19.setPredRaw "%p2" b1
  let r21 := r20.setPredRaw "%p1" cond
  have hrt14 : RegTyped r14 3 3 13 := regTyped_rfSet hrtG "%rd8" _
  have hrt16 : RegTyped r16 3 3 13 := regTyped_rfSet hrt14 "%rd8" _
  have hrt17 : RegTyped r17 3 3 13 := regTyped_rfSet hrt16 "%rd7" _
  have hrt18 : RegTyped r18 3 3 13 := RegTyped.setPredRaw_preserves hrt17 "%p1" b0
  have hrt19 : RegTyped r19 3 3 13 := regTyped_rfSet hrt18 "%rd9" _
  have hrt20 : RegTyped r20 3 3 13 := RegTyped.setPredRaw_preserves hrt19 "%p2" b1
  have hrt21 : RegTyped r21 3 3 13 := RegTyped.setPredRaw_preserves hrt20 "%p1" cond
  have hlogC : SafePTXLog (1 * len * 8) len allowedLanes laneOf (eC :: cta.epochLog) := by
    intro e he; rcases List.mem_cons.mp he with rfl | hr
    · exact ⟨rfl, rfl, rfl, Or.inl ⟨rfl, hinC⟩⟩
    · exact hlog e hr
  let ctaC : PTXCTAState := { cta with epochLog := eC :: cta.epochLog }
  have hlk2_17 : r17.regs.lookup "%rd2" = some (.scalar (BitVec.ofNat 64 gid)) := by
    dsimp only [r17, r16, r14]
    rw [lookup_rfSet_ne _ "%rd7" "%rd2" _ (by decide),
        lookup_rfSet_ne _ "%rd8" "%rd2" _ (by decide),
        lookup_rfSet_ne _ "%rd8" "%rd2" _ (by decide), hlk2G]
  have hlk2_18 : r18.regs.lookup "%rd2" = some (.scalar (BitVec.ofNat 64 gid)) := by
    dsimp only [r18, PTXRegFile.setPredRaw]
    rw [setAssoc_lookup_ne _ "%p1" "%rd2" _ (by decide), hlk2_17]
  have hlk3_19 : r19.regs.lookup "%rd3" = some (.scalar (BitVec.ofNat 64 len)) := by
    dsimp only [r19, r18, r17, r16, r14, PTXRegFile.setPredRaw]
    rw [lookup_rfSet_ne _ "%rd9" "%rd3" _ (by decide),
        setAssoc_lookup_ne _ "%p1" "%rd3" _ (by decide),
        lookup_rfSet_ne _ "%rd7" "%rd3" _ (by decide),
        lookup_rfSet_ne _ "%rd8" "%rd3" _ (by decide),
        lookup_rfSet_ne _ "%rd8" "%rd3" _ (by decide), hlk3G]
  have hlkP1_20 : r20.regs.lookup "%p1" = some (.pred b0) := by
    dsimp only [r20, r19, r18, PTXRegFile.setPredRaw]
    rw [setAssoc_lookup_ne _ "%p2" "%p1" _ (by decide),
        lookup_rfSet_ne _ "%rd9" "%p1" _ (by decide),
        setAssoc_lookup_self]
  have hlkP2_20 : r20.regs.lookup "%p2" = some (.pred b1) :=
    setAssoc_lookup_self r19.regs "%p2" (.pred b1)
  have hlkP1_21 : r21.regs.lookup s!"%p{1}" = some (.pred cond) :=
    setAssoc_lookup_self r20.regs "%p1" (.pred cond)
  refine ⟨r21, hrt21, ?_, ?_, ?_, ⟨hlogC⟩, ?_⟩
  · dsimp only [r21, r20, r19, r18, r17, r16, r14, PTXRegFile.setPredRaw]
    rw [setAssoc_lookup_ne _ "%p1" "%rd6" _ (by decide),
        setAssoc_lookup_ne _ "%p2" "%rd6" _ (by decide),
        lookup_rfSet_ne _ "%rd9" "%rd6" _ (by decide),
        setAssoc_lookup_ne _ "%p1" "%rd6" _ (by decide),
        lookup_rfSet_ne _ "%rd7" "%rd6" _ (by decide),
        lookup_rfSet_ne _ "%rd8" "%rd6" _ (by decide),
        lookup_rfSet_ne _ "%rd8" "%rd6" _ (by decide), hlk6G]
  · dsimp only [r21, r20, r19, r18, r17, PTXRegFile.setPredRaw]
    rw [setAssoc_lookup_ne _ "%p1" "%rd7" _ (by decide),
        setAssoc_lookup_ne _ "%p2" "%rd7" _ (by decide),
        lookup_rfSet_ne _ "%rd9" "%rd7" _ (by decide),
        setAssoc_lookup_ne _ "%p1" "%rd7" _ (by decide), lookup_rfSet_self]
  · dsimp only [r21, r20, r19, r18, r17, r16, PTXRegFile.setPredRaw]
    rw [setAssoc_lookup_ne _ "%p1" "%rd8" _ (by decide),
        setAssoc_lookup_ne _ "%p2" "%rd8" _ (by decide),
        lookup_rfSet_ne _ "%rd9" "%rd8" _ (by decide),
        setAssoc_lookup_ne _ "%p1" "%rd8" _ (by decide),
        lookup_rfSet_ne _ "%rd7" "%rd8" _ (by decide), lookup_rfSet_self]
  · intro f
    have hs13 := stencil_pure_step (f + 8) 13 stmts cta done todo tx rfG r14
      (.ldParam .u64 "%rd8" "param_in0") saved hdone (hpc 0 (by omega))
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun c t hpm hrf => by
        have hex := exec_ldParam_rd stmts c t (by rw [hrf]; exact hrtG) 8 (by omega)
          "param_in0" (BitVec.ofNat 64 0) (by rw [hpm]; exact hp0)
        have hr8 : s!"%rd{8}" = "%rd8" := rfl
        rw [hr8, hrf] at hex; exact hex
    have hs14 : runCTAWithGlobalLog ((f + 7) + 1) stmts
        { cta with threads := done ++ (laneAt 0 tx 14 r14 false :: todo) } saved =
      runCTAWithGlobalLog (f + 7) stmts
        { cta with threads := done ++ (laneAt 0 tx 15 r14 false :: todo) } saved := by
      have h' := stencil_pure_step (f + 7) 14 stmts cta done todo tx r14
        (rfSet r14 "%rd8" (BitVec.ofNat 64 0)) (.cvtaToGlobal .u64 "%rd8" (.reg "%rd8"))
        saved hdone (hpc 1 (by omega)) (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
        fun c t _ hrf => by
          have hr8 : s!"%rd{8}" = "%rd8" := rfl
          have hex := exec_cvta_rd stmts c t (by rw [hrf]; exact hrt14) 8 8 (by omega) (by omega)
            (BitVec.ofNat 64 0) (by rw [hr8, hrf]; exact lookup_rfSet_self rfG "%rd8" _)
          rw [hr8, hrf] at hex; exact hex
      rwa [rfSet_overwrite rfG "%rd8" _ _] at h'
    have hs15 := stencil_pure_step (f + 6) 15 stmts cta done todo tx r14 r16
      (.add .none .u64 "%rd8" (.reg "%rd8") (.reg "%rd5")) saved hdone (hpc 2 (by omega))
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun c t _ hrf => by
        have hr8 : s!"%rd{8}" = "%rd8" := rfl
        have hr5 : s!"%rd{5}" = "%rd5" := rfl
        have h5 : r14.regs.lookup "%rd5" = some (.scalar (BitVec.ofNat 64 (gid * 8))) := by
          dsimp only [r14]; rw [lookup_rfSet_ne _ "%rd8" "%rd5" _ (by decide), hlk5G]
        have hex := exec_add_rd stmts c t (by rw [hrf]; exact hrt14) 8 8 5 (by omega) (by omega) (by omega)
          (BitVec.ofNat 64 0) (BitVec.ofNat 64 (gid * 8))
          (by rw [hr8, hrf]; exact lookup_rfSet_self rfG "%rd8" _) (by rw [hr5, hrf]; exact h5)
        rw [hr8, hrf, add_ofNat64 0 (gid * 8) (by omega), Nat.zero_add] at hex; exact hex
    have hex16 := exec_ldGlobal_rd stmts
      { cta with threads := done ++ (laneAt 0 tx 16 r16 false :: todo) }
      (laneAt 0 tx 16 r16 false) hrt16 (1 * len * 8) len allowedLanes laneOf
      7 8 (by omega) (by omega) (gid * 8) xC
      (by have hr8 : s!"%rd{8}" = "%rd8" := rfl; rw [hr8]; exact lookup_rfSet_self r14 "%rd8" _)
      hg8_64 (by omega) hldC hlog hinC
    have hs16 := runCTA_mem_instr (f + 5) stmts
      { cta with threads := done ++ (laneAt 0 tx 16 r16 false :: todo) }
      done (laneAt 0 tx 16 r16 false) todo
      (.ldGlobal .u64 "%rd7" (.regOffset "%rd8" 0))
      (laneAt 0 tx 17 r17 false) cta.globalMem eC saved rfl hdone rfl (hpc 3 (by omega))
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) hex16
    have hs17 := stencil_pure_step (f + 4) 17 stmts ctaC done todo tx r17 r18
      (.setp .eq .u64 "%p1" (.reg "%rd2") (i64 0)) saved hdone (hpc 4 (by omega))
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun c t _ hrf => by
        have hp1 : s!"%p{1}" = "%p1" := rfl
        have hr2 : s!"%rd{2}" = "%rd2" := rfl
        have hex := exec_setp_imm stmts c t (by rw [hrf]; exact hrt17) .eq 1 2 (by omega) (by omega)
          (BitVec.ofNat 64 gid) (BitVec.ofNat 64 0) (by rw [hr2, hrf]; exact hlk2_17)
        rw [hp1, hrf, pred_eq_zero_u64 gid hgid64] at hex; exact hex
    have hs18 := stencil_pure_step (f + 3) 18 stmts ctaC done todo tx r18 r19
      (.add .none .u64 "%rd9" (.reg "%rd2") (i64 1)) saved hdone (hpc 5 (by omega))
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun c t _ hrf => by
        have hr9 : s!"%rd{9}" = "%rd9" := rfl
        have hr2 : s!"%rd{2}" = "%rd2" := rfl
        have hex := exec_add_imm stmts c t (by rw [hrf]; exact hrt18) 9 2 (by omega) (by omega)
          (BitVec.ofNat 64 gid) (BitVec.ofNat 64 1) (by rw [hr2, hrf]; exact hlk2_18)
        rw [hr9, hrf, add_ofNat64 gid 1 hgid1_64] at hex; exact hex
    have hs19 := stencil_pure_step (f + 2) 19 stmts ctaC done todo tx r19 r20
      (.setp .ge .u64 "%p2" (.reg "%rd9") (.reg "%rd3")) saved hdone (hpc 6 (by omega))
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun c t _ hrf => by
        have hp2 : s!"%p{2}" = "%p2" := rfl
        have hr9 : s!"%rd{9}" = "%rd9" := rfl
        have hr3 : s!"%rd{3}" = "%rd3" := rfl
        have hex := exec_setp_rd stmts c t (by rw [hrf]; exact hrt19) .ge 2 9 3 (by omega) (by omega) (by omega)
          (BitVec.ofNat 64 (gid + 1)) (BitVec.ofNat 64 len)
          (by rw [hr9, hrf]; exact lookup_rfSet_self r18 "%rd9" _)
          (by rw [hr3, hrf]; exact hlk3_19)
        have hcmp : evalPTXCmp .ge .u64 (BitVec.ofNat 64 (gid + 1)) (BitVec.ofNat 64 len) = b1 := by
          rw [pred_ge_u64]
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hgid1_64, Nat.mod_eq_of_lt hlen64, b1,
            decide_eq_decide]
          omega
        rw [hp2, hrf, hcmp] at hex; exact hex
    have hs20 := stencil_pure_step (f + 1) 20 stmts ctaC done todo tx r20 r21
      (.bitOr .pred "%p1" (.reg "%p1") (.reg "%p2")) saved hdone (hpc 7 (by omega))
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun c t _ hrf => by
        have hp1 : s!"%p{1}" = "%p1" := rfl
        have hp2 : s!"%p{2}" = "%p2" := rfl
        have hex := exec_bitOr_pred stmts c t (by rw [hrf]; exact hrt20) 1 1 2 (by omega) (by omega) (by omega)
          b0 b1 (by rw [hp1, hrf]; exact hlkP1_20) (by rw [hp2, hrf]; exact hlkP2_20)
        rw [hp1, hrf] at hex; exact hex
    have hs21 := runCTA_bra_pred f stmts
      { ctaC with threads := done ++ (laneAt 0 tx 21 r21 false :: todo) }
      done (laneAt 0 tx 21 r21 false) todo hrt21 1 (by omega) cond bnd 28 saved
      rfl hdone rfl (hpc 8 (by omega)) hlkP1_21 (find_bnd_pc name wL wC wR epilogue)
    have hf9 : f + 9 = (f + 8) + 1 := by omega
    have hf8 : f + 8 = (f + 7) + 1 := by omega
    have hf7 : f + 7 = (f + 6) + 1 := by omega
    have hf6 : f + 6 = (f + 5) + 1 := by omega
    have hf5 : f + 5 = (f + 4) + 1 := by omega
    have hf4 : f + 4 = (f + 3) + 1 := by omega
    have hf3 : f + 3 = (f + 2) + 1 := by omega
    have hf2 : f + 2 = (f + 1) + 1 := by omega
    rw [hf9, hs13, hf8, hs14, hf7, hs15, hf6, hs16, hf5, hs17, hf4, hs18, hf3, hs19, hf2, hs20, hs21]
    cases cond <;> rfl

/-- `MidBodySpec` for `.stencil1D3Pt wL wC wR`. -/
theorem midBody_stencil1D3Pt (len : Nat) (name : String) (wL wC wR : UInt64)
    (inWords : Nat → List (BitVec 64)) (hlen : ∀ j < 1, (inWords j).length = len)
    (houn : (1 + 1) * len * 8 ≤ 2 ^ 64) :
    MidBodySpec 3 3 13 1 len 7 15 s!"$L_done_{name}"
      (stencilMid s!"$L_boundary_{name}" wL wC wR) inWords hlen
      (fun gid =>
        if (gid == 0 || decide (len ≤ gid + 1)) = true then
          if hc : gid < (inWords 0).length then (inWords 0)[gid]'hc else 0#64
        else
          if hL : gid - 1 < (inWords 0).length then
            if hC : gid < (inWords 0).length then
              if hR : gid + 1 < (inWords 0).length then
                wL.toBitVec * (inWords 0)[gid - 1]'hL +
                  wC.toBitVec * (inWords 0)[gid]'hC +
                  wR.toBitVec * (inWords 0)[gid + 1]'hR
              else 0#64
            else 0#64
          else 0#64) := by
  intro blockSize ctaId tx cta done todo saved allowedLanes gid
    _ _ hpm _ _ _ hgidLt hdone hloadAll hlog
  let doneLbl := s!"$L_done_{name}"
  let bnd := s!"$L_boundary_{name}"
  let epilogue : List PTXStmt :=
    [.instr none (.stGlobal .u64 (.regOffset "%rd6" 0) (.reg s!"%rd{7}")),
     .label doneLbl, .instr none .ret]
  let stmts := stdGidSetup doneLbl ++ stencilMid bnd wL wC wR ++ epilogue
  have hlen0 : (inWords 0).length = len := hlen 0 (by omega)
  have hcC : gid < (inWords 0).length := by omega
  let xC := (inWords 0)[gid]'hcC
  have hg8_64 : gid * 8 < 2 ^ 64 := by omega
  have hrt0 : RegTyped (PTXRegFile.ofRegDecls (stdKernelRegs 3 3 13)) 3 3 13 :=
    initRegs_typed 3 3 13 (by omega) (by omega) (by omega)
  let rfG := (gidLane blockSize ctaId (PTXRegFile.ofRegDecls (stdKernelRegs 3 3 13)) 0 tx gid 1 len).regs
  have hrtG : RegTyped rfG 3 3 13 := gidLane_typed blockSize ctaId hrt0 0 tx gid 1 len
  have hp0 : cta.paramMem.lookupParam? "param_in0" = some (BitVec.ofNat 64 0) := by
    have h0 := stdParamMem_lookup_in 1 len 0 (by omega)
    have hstr : s!"param_in{0}" = "param_in0" := rfl
    rw [hpm, ← hstr]; simpa using h0
  have hldC : cta.globalMem.loadBits (gid * 8) 8 = some xC := by
    have := hloadAll 0 (by omega) gid hgidLt; simpa [xC, hlen0] using this
  let eC : MemAccessLog := {
    tid := { x := tx, y := 0, z := 0 }, space := .global, addr := gid * 8,
    width := 8, isWrite := false, isAtomic := false }
  let cond := (gid == 0) || decide (len ≤ gid + 1)
  have hpc (k : Nat) (hk : k < 15) : stmts[13 + k]? = (stencilMid bnd wL wC wR)[k]? :=
    sliceAt_mid_split (stdGidSetup doneLbl) (stencilMid bnd wL wC wR) epilogue k hk
  obtain ⟨rf21, hrt21, h6_21, h7_21, h8_21, hlogC, hhead⟩ :=
    run_stencil_head len tx gid name wL wC wR epilogue cta done todo
      saved allowedLanes (laneOf1D blockSize ctaId) rfG xC hrtG hgidLt houn hdone hp0 hldC
      (gidLane_lookup_gid blockSize ctaId _ 0 tx gid 1 len)
      (gidLane_lookup_len blockSize ctaId _ 0 tx gid 1 len)
      (gidLane_lookup_off blockSize ctaId _ 0 tx gid 1 len)
      (gidLane_lookup_out blockSize ctaId _ 0 tx gid 1 len) hlog
  have hmidLen : (stencilMid bnd wL wC wR).length = 15 := rfl
  by_cases hcond : cond = true
  · refine ⟨9, by omega, rf21, eC :: cta.epochLog, hrt21, h6_21, ?_, hlogC.run, fun f => ?_⟩
    · dsimp only
      change rf21.regs.lookup (toString "%rd" ++ toString 7) =
        some (.scalar (if cond = true then
          if hc : gid < (inWords 0).length then (inWords 0)[gid]'hc else 0#64
        else
          if hL : gid - 1 < (inWords 0).length then
            if hC : gid < (inWords 0).length then
              if hR : gid + 1 < (inWords 0).length then
                wL.toBitVec * (inWords 0)[gid - 1]'hL +
                  wC.toBitVec * (inWords 0)[gid]'hC +
                  wR.toBitVec * (inWords 0)[gid + 1]'hR
              else 0#64
            else 0#64
          else 0#64))
      have hr7 : s!"%rd{7}" = "%rd7" := rfl
      rw [hr7, ite_eq_left_iff.mpr (fun h => False.elim (h hcond)),
        dite_eq_left_of_eq_true (eq_true hcC)]
      exact h7_21
    · have hhead' := hhead f
      change _ = runCTAWithGlobalLog f _
        { cta with
          threads := done ++ (laneAt 0 tx (if cond = true then 28 else 22) rf21 false :: todo)
          epochLog := eC :: cta.epochLog } saved at hhead'
      rw [ite_eq_left_iff.mpr (fun h => False.elim (h hcond))] at hhead'
      rw [gidLane_eq_laneAt blockSize ctaId _ 0 tx gid 1 len rfl, hmidLen]
      exact hhead'
  · have hcondF : cond = false := Bool.eq_false_iff.mpr hcond
    have hpos : 0 < gid := by
      rcases Bool.or_eq_false_iff.mp hcondF with ⟨h1, _⟩
      have hne : gid ≠ 0 := by intro hz; simp [hz] at h1
      omega
    have hgid1Lt : gid + 1 < len := by
      rcases Bool.or_eq_false_iff.mp hcondF with ⟨_, h2⟩
      simp only [decide_eq_false_iff_not] at h2
      omega
    have hL : gid - 1 < (inWords 0).length := by omega
    have hR : gid + 1 < (inWords 0).length := by omega
    let xL := (inWords 0)[gid - 1]'hL
    let xR := (inWords 0)[gid + 1]'hR
    have hldL : cta.globalMem.loadBits ((gid - 1) * 8) 8 = some xL := by
      have := hloadAll 0 (by omega) (gid - 1) (by omega); simpa [xL, hlen0] using this
    have hldR : cta.globalMem.loadBits ((gid + 1) * 8) 8 = some xR := by
      have := hloadAll 0 (by omega) (gid + 1) hgid1Lt; simpa [xR, hlen0] using this
    have hgmL : (Int.ofNat (gid * 8) + (-8)).toNat = (gid - 1) * 8 := by
      change ((gid * 8 : Int) + (-8)).toNat = (gid - 1) * 8; omega
    have hgmR : (Int.ofNat (gid * 8) + 8).toNat = (gid + 1) * 8 := by
      change ((gid * 8 : Int) + 8).toNat = (gid + 1) * 8; omega
    let ctaC : PTXCTAState := { cta with epochLog := eC :: cta.epochLog }
    let eL : MemAccessLog := {
      tid := { x := tx, y := 0, z := 0 }, space := .global, addr := (gid - 1) * 8,
      width := 8, isWrite := false, isAtomic := false }
    let eR : MemAccessLog := {
      tid := { x := tx, y := 0, z := 0 }, space := .global, addr := (gid + 1) * 8,
      width := 8, isWrite := false, isAtomic := false }
    let r22 := rfSet rf21 "%rd10" xL
    let r23 := rfSet r22 "%rd11" xR
    let r24 := rfSet r23 "%rd12" (xL * wL.toBitVec)
    let r25 := rfSet r24 "%rd12" (xC * wC.toBitVec + xL * wL.toBitVec)
    let rfM := rfSet r25 "%rd7" (xR * wR.toBitVec + (xC * wC.toBitVec + xL * wL.toBitVec))
    have hrt22 : RegTyped r22 3 3 13 := regTyped_rfSet hrt21 "%rd10" _
    have hrt23 : RegTyped r23 3 3 13 := regTyped_rfSet hrt22 "%rd11" _
    have hrt24 : RegTyped r24 3 3 13 := regTyped_rfSet hrt23 "%rd12" _
    have hrt25 : RegTyped r25 3 3 13 := regTyped_rfSet hrt24 "%rd12" _
    have hrtM : RegTyped rfM 3 3 13 := regTyped_rfSet hrt25 "%rd7" _
    have hinL : (gid - 1) * 8 + 8 ≤ 1 * len * 8 := by omega
    have hinR : (gid + 1) * 8 + 8 ≤ 1 * len * 8 := by omega
    have hlogL : SafePTXLog (1 * len * 8) len allowedLanes (laneOf1D blockSize ctaId)
        (eL :: ctaC.epochLog) := by
      intro e he; rcases List.mem_cons.mp he with rfl | hr
      · exact ⟨rfl, rfl, rfl, Or.inl ⟨rfl, hinL⟩⟩
      · exact hlogC.run e hr
    have hlogR : SafePTXLog (1 * len * 8) len allowedLanes (laneOf1D blockSize ctaId)
        (eR :: eL :: ctaC.epochLog) := by
      intro e he; rcases List.mem_cons.mp he with rfl | hr
      · exact ⟨rfl, rfl, rfl, Or.inl ⟨rfl, hinR⟩⟩
      · exact hlogL e hr
    have h8_22 : r22.regs.lookup "%rd8" = some (.scalar (BitVec.ofNat 64 (gid * 8))) := by
      dsimp [r22]; rw [lookup_rfSet_ne _ "%rd10" "%rd8" _ (by decide), h8_21]
    have h10_23 : r23.regs.lookup "%rd10" = some (.scalar xL) := by
      dsimp [r23]; rw [lookup_rfSet_ne _ "%rd11" "%rd10" _ (by decide), lookup_rfSet_self]
    have h7_24 : r24.regs.lookup "%rd7" = some (.scalar xC) := by
      dsimp [r24, r23, r22]
      rw [lookup_rfSet_ne _ "%rd12" "%rd7" _ (by decide),
          lookup_rfSet_ne _ "%rd11" "%rd7" _ (by decide),
          lookup_rfSet_ne _ "%rd10" "%rd7" _ (by decide), h7_21]
    have h12_24 : r24.regs.lookup "%rd12" = some (.scalar (xL * wL.toBitVec)) := lookup_rfSet_self _ "%rd12" _
    have h11_25 : r25.regs.lookup "%rd11" = some (.scalar xR) := by
      dsimp [r25, r24, r23]
      rw [lookup_rfSet_ne _ "%rd12" "%rd11" _ (by decide),
          lookup_rfSet_ne _ "%rd12" "%rd11" _ (by decide), lookup_rfSet_self]
    have h12_25 : r25.regs.lookup "%rd12" =
        some (.scalar (xC * wC.toBitVec + xL * wL.toBitVec)) := lookup_rfSet_self _ "%rd12" _
    refine ⟨15, by omega, rfM, eR :: eL :: eC :: cta.epochLog, hrtM, ?_, ?_, hlogR, fun f => ?_⟩
    · dsimp [rfM, r25, r24, r23, r22]
      rw [lookup_rfSet_ne _ "%rd7" "%rd6" _ (by decide),
          lookup_rfSet_ne _ "%rd12" "%rd6" _ (by decide),
          lookup_rfSet_ne _ "%rd12" "%rd6" _ (by decide),
          lookup_rfSet_ne _ "%rd11" "%rd6" _ (by decide),
          lookup_rfSet_ne _ "%rd10" "%rd6" _ (by decide), h6_21]
    · have hr7 : s!"%rd{7}" = "%rd7" := rfl
      dsimp only
      change rfM.regs.lookup (toString "%rd" ++ toString 7) =
        some (.scalar (if cond = true then
          if hc : gid < (inWords 0).length then (inWords 0)[gid]'hc else 0#64
        else
          if hL : gid - 1 < (inWords 0).length then
            if hC : gid < (inWords 0).length then
              if hR : gid + 1 < (inWords 0).length then
                wL.toBitVec * (inWords 0)[gid - 1]'hL +
                  wC.toBitVec * (inWords 0)[gid]'hC +
                  wR.toBitVec * (inWords 0)[gid + 1]'hR
              else 0#64
            else 0#64
          else 0#64))
      rw [hr7, lookup_rfSet_self, ite_eq_right_iff.mpr (fun h => False.elim (hcond h)),
        dite_eq_left_of_eq_true (eq_true hL), dite_eq_left_of_eq_true (eq_true hcC),
        dite_eq_left_of_eq_true (eq_true hR), stencil_mad_eq]
    · have hex22 := exec_ldGlobal_rd_disp stmts
        { ctaC with threads := done ++ (laneAt 0 tx 22 rf21 false :: todo) }
        (laneAt 0 tx 22 rf21 false) hrt21 (1 * len * 8) len allowedLanes (laneOf1D blockSize ctaId)
        10 8 (by omega) (by omega) (gid * 8) (-8) xL h8_21 hg8_64 (by omega) (by omega)
        (by rw [hgmL]; exact hldL) hlogC.run (by rw [hgmL]; exact hinL)
      have hs22 := runCTA_mem_instr (f + 5) stmts
        { ctaC with threads := done ++ (laneAt 0 tx 22 rf21 false :: todo) }
        done (laneAt 0 tx 22 rf21 false) todo
        (.ldGlobal .u64 "%rd10" (.regOffset "%rd8" (-8)))
        (laneAt 0 tx 23 r22 false) cta.globalMem eL saved rfl hdone rfl (hpc 9 (by omega))
        (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) (by
          have hr10 : s!"%rd{10}" = "%rd10" := rfl
          have hr8 : s!"%rd{8}" = "%rd8" := rfl
          have hth : thStep (laneAt 0 tx 22 rf21 false)
              ((laneAt 0 tx 22 rf21 false).regs.setScalarRaw "%rd10" xL) =
              laneAt 0 tx 23 r22 false := by
            simp [thStep, laneAt, r22, rfSet, PTXRegFile.setScalarRaw]
          rw [hr10, hr8, hgmL, hth] at hex22; exact hex22)
      have hex23 := exec_ldGlobal_rd_disp stmts
        { ctaC with
          threads := done ++ (laneAt 0 tx 23 r22 false :: todo)
          epochLog := eL :: ctaC.epochLog }
        (laneAt 0 tx 23 r22 false) hrt22 (1 * len * 8) len allowedLanes (laneOf1D blockSize ctaId)
        11 8 (by omega) (by omega) (gid * 8) 8 xR h8_22 hg8_64 (by omega) (by omega)
        (by rw [hgmR]; exact hldR) hlogL (by rw [hgmR]; exact hinR)
      have hs23 := runCTA_mem_instr (f + 4) stmts
        { ctaC with
          threads := done ++ (laneAt 0 tx 23 r22 false :: todo)
          epochLog := eL :: ctaC.epochLog }
        done (laneAt 0 tx 23 r22 false) todo
        (.ldGlobal .u64 "%rd11" (.regOffset "%rd8" 8))
        (laneAt 0 tx 24 r23 false) cta.globalMem eR saved rfl hdone rfl (hpc 10 (by omega))
        (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) (by
          have hr11 : s!"%rd{11}" = "%rd11" := rfl
          have hr8 : s!"%rd{8}" = "%rd8" := rfl
          have hth : thStep (laneAt 0 tx 23 r22 false)
              ((laneAt 0 tx 23 r22 false).regs.setScalarRaw "%rd11" xR) =
              laneAt 0 tx 24 r23 false := by
            simp [thStep, laneAt, r23, rfSet, PTXRegFile.setScalarRaw]
          rw [hr11, hr8, hgmR, hth] at hex23; exact hex23)
      have hs24 := stencil_pure_step (f + 3) 24 stmts
        { ctaC with epochLog := eR :: eL :: ctaC.epochLog } done todo tx r23 r24
        (.mul .lo .u64 "%rd12" (.reg "%rd10") (.immU64 wL.toBitVec)) saved hdone (hpc 11 (by omega))
        (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun c t _ hrf => by
          have hr10 : s!"%rd{10}" = "%rd10" := rfl
          have hr12 : s!"%rd{12}" = "%rd12" := rfl
          have hex := exec_mul_lo_imm stmts c t (by rw [hrf]; exact hrt23) 12 10 (by omega) (by omega)
            xL wL.toBitVec (by rw [hr10, hrf]; exact h10_23)
          rw [hr12, hrf] at hex; exact hex
      have hs25 := stencil_pure_step (f + 2) 25 stmts
        { ctaC with epochLog := eR :: eL :: ctaC.epochLog } done todo tx r24 r25
        (.mad .lo .u64 "%rd12" (.reg "%rd7") (.immU64 wC.toBitVec) (.reg "%rd12")) saved hdone
        (hpc 12 (by omega)) (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun c t _ hrf => by
          have hr7 : s!"%rd{7}" = "%rd7" := rfl
          have hr12 : s!"%rd{12}" = "%rd12" := rfl
          have hex := exec_mad_lo_imm stmts c t (by rw [hrf]; exact hrt24) 12 7 12
            (by omega) (by omega) (by omega) xC (xL * wL.toBitVec) wC.toBitVec
            (by rw [hr7, hrf]; exact h7_24) (by rw [hr12, hrf]; exact h12_24)
          rw [hr12, hrf] at hex; exact hex
      have hs26 := stencil_pure_step (f + 1) 26 stmts
        { ctaC with epochLog := eR :: eL :: ctaC.epochLog } done todo tx r25 rfM
        (.mad .lo .u64 "%rd7" (.reg "%rd11") (.immU64 wR.toBitVec) (.reg "%rd12")) saved hdone
        (hpc 13 (by omega)) (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) fun c t _ hrf => by
          have hr7 : s!"%rd{7}" = "%rd7" := rfl
          have hr11 : s!"%rd{11}" = "%rd11" := rfl
          have hr12 : s!"%rd{12}" = "%rd12" := rfl
          have hex := exec_mad_lo_imm stmts c t (by rw [hrf]; exact hrt25) 7 11 12
            (by omega) (by omega) (by omega) xR (xC * wC.toBitVec + xL * wL.toBitVec) wR.toBitVec
            (by rw [hr11, hrf]; exact h11_25) (by rw [hr12, hrf]; exact h12_25)
          rw [hr7, hrf] at hex; exact hex
      have hs27 := runCTA_label_step f stmts
        { ctaC with
          threads := done ++ (laneAt 0 tx 27 rfM false :: todo)
          epochLog := eR :: eL :: ctaC.epochLog }
        done (laneAt 0 tx 27 rfM false) todo bnd saved rfl hdone rfl (hpc 14 (by omega))
      have hhead' := hhead (f + 6)
      change _ = runCTAWithGlobalLog (f + 6) _
        { ctaC with threads := done ++ (laneAt 0 tx (if cond = true then 28 else 22) rf21 false :: todo) }
        saved at hhead'
      rw [ite_eq_right_iff.mpr (fun h => False.elim (hcond h))] at hhead'
      have hf15 : f + 15 = (f + 6) + 9 := by omega
      have hf6 : f + 6 = (f + 5) + 1 := by omega
      have hf5 : f + 5 = (f + 4) + 1 := by omega
      have hf4 : f + 4 = (f + 3) + 1 := by omega
      have hf3 : f + 3 = (f + 2) + 1 := by omega
      have hf2 : f + 2 = (f + 1) + 1 := by omega
      rw [hf15, gidLane_eq_laneAt blockSize ctaId _ 0 tx gid 1 len rfl,
          hhead', hf6, hs22, hf5, hs23, hf4, hs24, hf3, hs25, hf2, hs26, hs27]
      rfl

end LeanNative.Proofs.PTXLowerProofs
