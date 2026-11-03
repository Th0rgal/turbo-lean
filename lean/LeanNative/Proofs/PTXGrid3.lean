import LeanNative.Proofs.PTXGrid2

namespace LeanNative.Proofs.PTXSIMT

open LeanNative.Backend.PTXAst

/-! ## 8. Execution of the standard preamble (`stdGidSetup`) and `stdLoadIn` -/

def laneAt (localBytes tx pc : Nat) (rf : PTXRegFile) (halted : Bool := false) : PTXThreadState :=
  { tid := { x := tx, y := 0, z := 0 }
    pc := pc
    regs := rf
    localMem := ByteMemory.zeros localBytes
    halted := halted }

theorem setAssoc_overwrite {α : Type} (xs : List (String × α)) (k : String) (v1 v2 : α) :
    PTXRegFile.setAssoc (PTXRegFile.setAssoc xs k v1) k v2 = PTXRegFile.setAssoc xs k v2 := by
  induction xs with
  | nil => simp [PTXRegFile.setAssoc]
  | cons kv rest ih =>
    rcases kv with ⟨k', v'⟩
    simp only [PTXRegFile.setAssoc]
    cases hk : (k' == k) <;> simp [PTXRegFile.setAssoc, hk, ih]

theorem rfSet_overwrite (rf : PTXRegFile) (nm : String) (v1 v2 : BitVec 64) :
    rfSet (rfSet rf nm v1) nm v2 = rfSet rf nm v2 := by
  unfold rfSet PTXRegFile.setScalarRaw
  congr 1
  exact setAssoc_overwrite rf.regs nm (.scalar v1) (.scalar v2)

def rf7 (blockSize : Nat) (ctaId : Dim3) (rf : PTXRegFile) (tx len : Nat) : PTXRegFile :=
  rfSet (rfSet (rfSet (rfSet (rfSet (rfSet (rfSet rf
    "%r0" (BitVec.ofNat 64 ctaId.x))
    "%r1" (BitVec.ofNat 64 blockSize))
    "%r2" (BitVec.ofNat 64 tx))
    "%rd0" (BitVec.ofNat 64 (ctaId.x * blockSize)))
    "%rd1" (BitVec.ofNat 64 tx))
    "%rd2" (BitVec.ofNat 64 (ctaId.x * blockSize + tx)))
    "%rd3" (BitVec.ofNat 64 len)

def rf8 (blockSize : Nat) (ctaId : Dim3) (rf : PTXRegFile) (tx len : Nat) (cond : Bool) :
    PTXRegFile :=
  (rf7 blockSize ctaId rf tx len).setPredRaw "%p0" cond

def rf13 (blockSize : Nat) (ctaId : Dim3) (rf : PTXRegFile) (tx len nIn : Nat) : PTXRegFile :=
  let gid := ctaId.x * blockSize + tx
  rfSet (rfSet (rfSet (rf8 blockSize ctaId rf tx len false)
    "%rd4" (BitVec.ofNat 64 (nIn * len * 8)))
    "%rd5" (BitVec.ofNat 64 (gid * 8)))
    "%rd6" (BitVec.ofNat 64 (nIn * len * 8 + gid * 8))

def doneLane (blockSize : Nat) (ctaId : Dim3) (rf : PTXRegFile) (localBytes tx : Nat)
    (len retPc : Nat) : PTXThreadState :=
  laneAt localBytes tx (retPc + 1) (rf8 blockSize ctaId rf tx len true) true

theorem laneAt_rf13_eq_gidLane (blockSize : Nat) (ctaId : Dim3) (rf : PTXRegFile)
    (localBytes tx len nIn : Nat) :
    laneAt localBytes tx 13 (rf13 blockSize ctaId rf tx len nIn) false =
      gidLane blockSize ctaId rf localBytes tx (ctaId.x * blockSize + tx) nIn len :=
  rfl

private theorem shl3_eq_mul8 (n : Nat) (hn : n < 2 ^ 61) :
    BitVec.ofNat 64 n <<< 3 = BitVec.ofNat 64 (n * 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]
  have h8 : n * 8 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h8]
  change n <<< 3 % 2 ^ 64 = n * 8
  rw [Nat.shiftLeft_eq, Nat.mul_comm]
  have h8' : 2 ^ 3 * n < 2 ^ 64 := by rw [Nat.mul_comm]; exact h8
  exact Nat.mod_eq_of_lt h8'

theorem add_ofNat64 (a b : Nat) (h : a + b < 2 ^ 64) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : a < 2 ^ 64), Nat.mod_eq_of_lt (by omega : b < 2 ^ 64),
      Nat.mod_eq_of_lt h]

private theorem mul_ofNat64 (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a * b < 2 ^ 64) :
    BitVec.ofNat 64 a * BitVec.ofNat 64 b = BitVec.ofNat 64 (a * b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt h]

theorem gid_no_label (doneLbl lbl : String) : ∀ s ∈ stdGidSetup doneLbl, s ≠ .label lbl := by
  intro s hs
  unfold stdGidSetup at hs
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem loadIn_no_label (k : Nat) (reg lbl : String) : ∀ s ∈ stdLoadIn k reg, s ≠ .label lbl := by
  intro s hs
  unfold stdLoadIn at hs
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl <;> simp

theorem pure_lane_step (f : Nat) (stmts : List PTXStmt) (cta : PTXCTAState)
    (done todo : List PTXThreadState) (localBytes tx pc : Nat)
    (rf rf' : PTXRegFile) (ins : PTXInstr) (saved : List MemAccessLog)
    (hdone : ∀ t ∈ done, t.halted = true)
    (hpc : stmts[pc]? = some (.instr none ins))
    (hnBar : ∀ b, ins ≠ .barSync b)
    (hnShfl : ∀ d s o c m, ins ≠ .shflSyncBfly d s o c m)
    (hexec : execNonBarrierInstr stmts
      { cta with threads := done ++ (laneAt localBytes tx pc rf false :: todo) }
      (laneAt localBytes tx pc rf false) ins =
      .ok (laneAt localBytes tx (pc + 1) rf' false, cta.globalMem, cta.sharedMem, cta.epochLog)) :
    runCTAWithGlobalLog (f + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx pc rf false :: todo) } saved =
    runCTAWithGlobalLog f stmts
      { cta with threads := done ++ (laneAt localBytes tx (pc + 1) rf' false :: todo) } saved :=
  runCTA_pure_instr f stmts
    { cta with threads := done ++ (laneAt localBytes tx pc rf false :: todo) }
    done (laneAt localBytes tx pc rf false) todo ins rf' saved
    rfl hdone rfl hpc hnBar hnShfl hexec

theorem run_gid_to_rf7
    (f : Nat) (doneLbl : String) (suf : List PTXStmt) (cta : PTXCTAState)
    (done todo : List PTXThreadState) (blockSize : Nat) (ctaId : Dim3)
    {rf : PTXRegFile} {nP nR nRd : Nat} (hrt : RegTyped rf nP nR nRd)
    (localBytes tx len : Nat)
    (hr : 2 < nR) (hrd : 3 < nRd)
    (hcta : cta.ctaId = ctaId) (hblk : cta.blockDim = { x := blockSize, y := 1, z := 1 })
    (htx : tx < 2 ^ 32) (hctaX : ctaId.x < 2 ^ 32) (hblkX : blockSize < 2 ^ 32)
    (hdone : ∀ t ∈ done, t.halted = true) (saved : List MemAccessLog)
    (hn : cta.paramMem.lookupParam? "param_n" = some (BitVec.ofNat 64 len)) :
    runCTAWithGlobalLog (f + 7) (stdGidSetup doneLbl ++ suf)
      { cta with threads := done ++ (laneAt localBytes tx 0 rf false :: todo) } saved =
    runCTAWithGlobalLog f (stdGidSetup doneLbl ++ suf)
      { cta with threads := done ++
        (laneAt localBytes tx 7 (rf7 blockSize ctaId rf tx len) false :: todo) } saved := by
  let stmts := stdGidSetup doneLbl ++ suf
  have hgid64 := laneOf1D_lt ctaId.x blockSize tx hctaX hblkX htx
  have hcta64 : ctaId.x < 2 ^ 64 := by omega
  have hblk64 : blockSize < 2 ^ 64 := by omega
  have hprod : ctaId.x * blockSize < 2 ^ 64 := by omega
  let r1 := rfSet rf "%r0" (BitVec.ofNat 64 ctaId.x)
  let r2 := rfSet r1 "%r1" (BitVec.ofNat 64 blockSize)
  let r3 := rfSet r2 "%r2" (BitVec.ofNat 64 tx)
  let r4 := rfSet r3 "%rd0" (BitVec.ofNat 64 (ctaId.x * blockSize))
  let r5 := rfSet r4 "%rd1" (BitVec.ofNat 64 tx)
  let r6 := rfSet r5 "%rd2" (BitVec.ofNat 64 (ctaId.x * blockSize + tx))
  have hs0 : runCTAWithGlobalLog ((f + 6) + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx 0 rf false :: todo) } saved =
    runCTAWithGlobalLog (f + 6) stmts
      { cta with threads := done ++ (laneAt localBytes tx 1 r1 false :: todo) } saved := by
    apply pure_lane_step (f + 6) stmts cta done todo localBytes tx 0 rf r1
      (.mov .u32 "%r0" (.sreg .ctaidX)) saved hdone (by simp [stmts, stdGidSetup])
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    have hex := exec_mov_sreg_r stmts
      { cta with threads := done ++ (laneAt localBytes tx 0 rf false :: todo) }
      (laneAt localBytes tx 0 rf false) hrt 0 (by omega) .ctaidX
      (BitVec.ofNat 64 ctaId.x) (by simp [evalSpecialReg, hcta]) (fit32_ofNat ctaId.x hctaX)
    rw [mask32_ofNat ctaId.x hctaX] at hex; exact hex
  have hs1 : runCTAWithGlobalLog ((f + 5) + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx 1 r1 false :: todo) } saved =
    runCTAWithGlobalLog (f + 5) stmts
      { cta with threads := done ++ (laneAt localBytes tx 2 r2 false :: todo) } saved := by
    apply pure_lane_step (f + 5) stmts cta done todo localBytes tx 1 r1 r2
      (.mov .u32 "%r1" (.sreg .ntidX)) saved hdone (by simp [stmts, stdGidSetup])
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    have hex := exec_mov_sreg_r stmts
      { cta with threads := done ++ (laneAt localBytes tx 1 r1 false :: todo) }
      (laneAt localBytes tx 1 r1 false) hrt 1 (by omega) .ntidX
      (BitVec.ofNat 64 blockSize) (by simp [evalSpecialReg, hblk]) (fit32_ofNat blockSize hblkX)
    rw [mask32_ofNat blockSize hblkX] at hex; exact hex
  have hs2 : runCTAWithGlobalLog ((f + 4) + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx 2 r2 false :: todo) } saved =
    runCTAWithGlobalLog (f + 4) stmts
      { cta with threads := done ++ (laneAt localBytes tx 3 r3 false :: todo) } saved := by
    apply pure_lane_step (f + 4) stmts cta done todo localBytes tx 2 r2 r3
      (.mov .u32 "%r2" (.sreg .tidX)) saved hdone (by simp [stmts, stdGidSetup])
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    have hex := exec_mov_sreg_r stmts
      { cta with threads := done ++ (laneAt localBytes tx 2 r2 false :: todo) }
      (laneAt localBytes tx 2 r2 false) hrt 2 (by omega) .tidX
      (BitVec.ofNat 64 tx) (by simp [evalSpecialReg, laneAt]) (fit32_ofNat tx htx)
    rw [mask32_ofNat tx htx] at hex; exact hex
  have hs3 : runCTAWithGlobalLog ((f + 3) + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx 3 r3 false :: todo) } saved =
    runCTAWithGlobalLog (f + 3) stmts
      { cta with threads := done ++ (laneAt localBytes tx 4 r4 false :: todo) } saved := by
    apply pure_lane_step (f + 3) stmts cta done todo localBytes tx 3 r3 r4
      (.mul .wide .u32 "%rd0" (.reg "%r0") (.reg "%r1")) saved hdone (by simp [stmts, stdGidSetup])
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    have hlk0 : r3.regs.lookup "%r0" = some (.scalar (BitVec.ofNat 64 ctaId.x)) := by
      dsimp only [r3, r2, r1]
      rw [lookup_rfSet_ne _ "%r2" "%r0" _ (by decide),
          lookup_rfSet_ne _ "%r1" "%r0" _ (by decide), lookup_rfSet_self]
    have hlk1 : r3.regs.lookup "%r1" = some (.scalar (BitVec.ofNat 64 blockSize)) := by
      dsimp only [r3, r2]; rw [lookup_rfSet_ne _ "%r2" "%r1" _ (by decide), lookup_rfSet_self]
    have hex := exec_mul_wide_u32 stmts
      { cta with threads := done ++ (laneAt localBytes tx 3 r3 false :: todo) }
      (laneAt localBytes tx 3 r3 false) hrt 0 0 1 (by omega) (by omega) (by omega)
      (BitVec.ofNat 64 ctaId.x) (BitVec.ofNat 64 blockSize)
      (fit32_ofNat ctaId.x hctaX) (fit32_ofNat blockSize hblkX) hlk0 hlk1
    rw [mul_ofNat64 ctaId.x blockSize hcta64 hblk64 hprod] at hex; exact hex
  have hs4 : runCTAWithGlobalLog ((f + 2) + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx 4 r4 false :: todo) } saved =
    runCTAWithGlobalLog (f + 2) stmts
      { cta with threads := done ++ (laneAt localBytes tx 5 r5 false :: todo) } saved := by
    apply pure_lane_step (f + 2) stmts cta done todo localBytes tx 4 r4 r5
      (.cvt .none .u64 .u32 "%rd1" (.reg "%r2")) saved hdone (by simp [stmts, stdGidSetup])
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    have hlk2 : r4.regs.lookup "%r2" = some (.scalar (BitVec.ofNat 64 tx)) := by
      dsimp only [r4, r3]; rw [lookup_rfSet_ne _ "%rd0" "%r2" _ (by decide), lookup_rfSet_self]
    exact exec_cvt_u64_u32 stmts
      { cta with threads := done ++ (laneAt localBytes tx 4 r4 false :: todo) }
      (laneAt localBytes tx 4 r4 false) hrt 1 2 (by omega) (by omega)
      (BitVec.ofNat 64 tx) (fit32_ofNat tx htx) hlk2
  have hs5 : runCTAWithGlobalLog ((f + 1) + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx 5 r5 false :: todo) } saved =
    runCTAWithGlobalLog (f + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx 6 r6 false :: todo) } saved := by
    apply pure_lane_step (f + 1) stmts cta done todo localBytes tx 5 r5 r6
      (.add .none .u64 "%rd2" (.reg "%rd0") (.reg "%rd1")) saved hdone (by simp [stmts, stdGidSetup])
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    have hlk0 : r5.regs.lookup "%rd0" = some (.scalar (BitVec.ofNat 64 (ctaId.x * blockSize))) := by
      dsimp only [r5, r4]; rw [lookup_rfSet_ne _ "%rd1" "%rd0" _ (by decide), lookup_rfSet_self]
    have hlk1 : r5.regs.lookup "%rd1" = some (.scalar (BitVec.ofNat 64 tx)) :=
      lookup_rfSet_self r4 "%rd1" _
    have hex := exec_add_rd stmts
      { cta with threads := done ++ (laneAt localBytes tx 5 r5 false :: todo) }
      (laneAt localBytes tx 5 r5 false) hrt 2 0 1 (by omega) (by omega) (by omega)
      (BitVec.ofNat 64 (ctaId.x * blockSize)) (BitVec.ofNat 64 tx) hlk0 hlk1
    rw [add_ofNat64 (ctaId.x * blockSize) tx hgid64] at hex; exact hex
  have hs6 : runCTAWithGlobalLog (f + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx 6 r6 false :: todo) } saved =
    runCTAWithGlobalLog f stmts
      { cta with threads := done ++
        (laneAt localBytes tx 7 (rf7 blockSize ctaId rf tx len) false :: todo) } saved := by
    apply pure_lane_step f stmts cta done todo localBytes tx 6 r6
      (rf7 blockSize ctaId rf tx len) (.ldParam .u64 "%rd3" "param_n") saved hdone
      (by simp [stmts, stdGidSetup]) (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    exact exec_ldParam_rd stmts
      { cta with threads := done ++ (laneAt localBytes tx 6 r6 false :: todo) }
      (laneAt localBytes tx 6 r6 false) hrt 3 (by omega) "param_n" (BitVec.ofNat 64 len) hn
  have hf7 : f + 7 = (f + 6) + 1 := by omega
  have hf6 : f + 6 = (f + 5) + 1 := by omega
  have hf5 : f + 5 = (f + 4) + 1 := by omega
  have hf4 : f + 4 = (f + 3) + 1 := by omega
  have hf3 : f + 3 = (f + 2) + 1 := by omega
  have hf2 : f + 2 = (f + 1) + 1 := by omega
  rw [hf7, hs0, hf6, hs1, hf5, hs2, hf4, hs3, hf3, hs4, hf2, hs5, hs6]

theorem run_gid_branch
    (f : Nat) (doneLbl : String) (suf : List PTXStmt) (cta : PTXCTAState)
    (done todo : List PTXThreadState) (blockSize : Nat) (ctaId : Dim3)
    {rf : PTXRegFile} {nP nR nRd : Nat} (hrt : RegTyped rf nP nR nRd)
    (localBytes tx len : Nat) (cond : Bool) (donePc : Nat)
    (hrd : 3 < nRd) (hp : 0 < nP)
    (htx : tx < 2 ^ 32) (hctaX : ctaId.x < 2 ^ 32) (hblkX : blockSize < 2 ^ 32)
    (hlen : len < 2 ^ 64)
    (hcond : cond = decide ¬ (ctaId.x * blockSize + tx < len))
    (hdone : ∀ t ∈ done, t.halted = true) (saved : List MemAccessLog)
    (hlbl : findLabelPC? (stdGidSetup doneLbl ++ suf) doneLbl = some donePc) :
    runCTAWithGlobalLog (f + 2) (stdGidSetup doneLbl ++ suf)
      { cta with threads := done ++
        (laneAt localBytes tx 7 (rf7 blockSize ctaId rf tx len) false :: todo) } saved =
    runCTAWithGlobalLog f (stdGidSetup doneLbl ++ suf)
      { cta with threads := done ++
        ((if cond then laneAt localBytes tx donePc (rf8 blockSize ctaId rf tx len true) false
          else laneAt localBytes tx 9 (rf8 blockSize ctaId rf tx len false) false) :: todo) }
      saved := by
  let stmts := stdGidSetup doneLbl ++ suf
  have hgid64 := laneOf1D_lt ctaId.x blockSize tx hctaX hblkX htx
  have hs7 : runCTAWithGlobalLog ((f + 1) + 1) stmts
      { cta with threads := done ++
        (laneAt localBytes tx 7 (rf7 blockSize ctaId rf tx len) false :: todo) } saved =
    runCTAWithGlobalLog (f + 1) stmts
      { cta with threads := done ++
        (laneAt localBytes tx 8 (rf8 blockSize ctaId rf tx len cond) false :: todo) } saved := by
    apply pure_lane_step (f + 1) stmts cta done todo localBytes tx 7
      (rf7 blockSize ctaId rf tx len) (rf8 blockSize ctaId rf tx len cond)
      (.setp .ge .u64 "%p0" (.reg "%rd2") (.reg "%rd3")) saved hdone
      (by simp [stmts, stdGidSetup]) (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    have hlk2 : (rf7 blockSize ctaId rf tx len).regs.lookup "%rd2" =
        some (.scalar (BitVec.ofNat 64 (ctaId.x * blockSize + tx))) := by
      unfold rf7; rw [lookup_rfSet_ne _ "%rd3" "%rd2" _ (by decide), lookup_rfSet_self]
    have hlk3 : (rf7 blockSize ctaId rf tx len).regs.lookup "%rd3" =
        some (.scalar (BitVec.ofNat 64 len)) := lookup_rfSet_self _ "%rd3" _
    have hex := exec_setp_rd stmts
      { cta with threads := done ++
        (laneAt localBytes tx 7 (rf7 blockSize ctaId rf tx len) false :: todo) }
      (laneAt localBytes tx 7 (rf7 blockSize ctaId rf tx len) false)
      hrt .ge 0 2 3 hp (by omega) (by omega)
      (BitVec.ofNat 64 (ctaId.x * blockSize + tx)) (BitVec.ofNat 64 len) hlk2 hlk3
    have hcmp : evalPTXCmp .ge .u64
        (BitVec.ofNat 64 (ctaId.x * blockSize + tx)) (BitVec.ofNat 64 len) = cond := by
      rw [pred_ge_u64, hcond]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hgid64, Nat.mod_eq_of_lt hlen]
    rw [hcmp] at hex; exact hex
  have hlp : (rf8 blockSize ctaId rf tx len cond).regs.lookup s!"%p{0}" =
      some (PTXRegVal.pred cond) := by
    change (rf8 blockSize ctaId rf tx len cond).regs.lookup "%p0" = some (PTXRegVal.pred cond)
    unfold rf8 PTXRegFile.setPredRaw; exact setAssoc_lookup_self _ "%p0" (PTXRegVal.pred cond)
  have hpc8 : stmts[(laneAt localBytes tx 8 (rf8 blockSize ctaId rf tx len cond) false).pc]? =
      some (.instr (some { predReg := s!"%p{0}" }) (.bra doneLbl)) := by
    change (stdGidSetup doneLbl ++ suf)[8]? =
      some (.instr (some { predReg := "%p0" }) (.bra doneLbl))
    simp [stdGidSetup]
  have hs8 := runCTA_bra_pred f stmts
    { cta with threads := done ++
      (laneAt localBytes tx 8 (rf8 blockSize ctaId rf tx len cond) false :: todo) }
    done (laneAt localBytes tx 8 (rf8 blockSize ctaId rf tx len cond) false) todo
    hrt 0 hp cond doneLbl donePc saved rfl hdone rfl hpc8 hlp hlbl
  have hf2 : f + 2 = (f + 1) + 1 := by omega
  rw [hf2, hs7, hs8]
  cases cond <;> rfl

theorem run_gid_outaddr
    (f : Nat) (doneLbl : String) (suf : List PTXStmt) (cta : PTXCTAState)
    (done todo : List PTXThreadState) (blockSize : Nat) (ctaId : Dim3)
    {rf : PTXRegFile} {nP nR nRd : Nat} (hrt : RegTyped rf nP nR nRd)
    (localBytes tx len nIn : Nat)
    (hrd : 6 < nRd)
    (htx : tx < 2 ^ 32) (hctaX : ctaId.x < 2 ^ 32) (hblkX : blockSize < 2 ^ 32)
    (hgidLt : ctaId.x * blockSize + tx < len)
    (houn : (nIn + 1) * len * 8 ≤ 2 ^ 64)
    (hdone : ∀ t ∈ done, t.halted = true) (saved : List MemAccessLog)
    (hout : cta.paramMem.lookupParam? "param_out" = some (BitVec.ofNat 64 (nIn * len * 8))) :
    runCTAWithGlobalLog (f + 4) (stdGidSetup doneLbl ++ suf)
      { cta with threads := done ++
        (laneAt localBytes tx 9 (rf8 blockSize ctaId rf tx len false) false :: todo) } saved =
    runCTAWithGlobalLog f (stdGidSetup doneLbl ++ suf)
      { cta with threads := done ++
        (laneAt localBytes tx 13 (rf13 blockSize ctaId rf tx len nIn) false :: todo) } saved := by
  let stmts := stdGidSetup doneLbl ++ suf
  let gid := ctaId.x * blockSize + tx
  have _ := laneOf1D_lt ctaId.x blockSize tx hctaX hblkX htx
  have hlen8 : nIn * len * 8 + len * 8 ≤ 2 ^ 64 := by
    have : (nIn + 1) * len * 8 = nIn * len * 8 + len * 8 := by simp [Nat.add_mul, Nat.one_mul]
    omega
  have hgid8 : gid * 8 < len * 8 := Nat.mul_lt_mul_of_pos_right hgidLt (by omega)
  have hgid61 : gid < 2 ^ 61 := by omega
  let r8 := rf8 blockSize ctaId rf tx len false
  let r9 := rfSet r8 "%rd4" (BitVec.ofNat 64 (nIn * len * 8))
  let r10 := rfSet r9 "%rd4" (BitVec.ofNat 64 (nIn * len * 8))
  let r11 := rfSet r10 "%rd5" (BitVec.ofNat 64 (gid * 8))
  have hr9eq : r10 = r9 := rfSet_overwrite r8 "%rd4" _ _
  have hs9 : runCTAWithGlobalLog ((f + 3) + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx 9 r8 false :: todo) } saved =
    runCTAWithGlobalLog (f + 3) stmts
      { cta with threads := done ++ (laneAt localBytes tx 10 r9 false :: todo) } saved := by
    apply pure_lane_step (f + 3) stmts cta done todo localBytes tx 9 r8 r9
      (.ldParam .u64 "%rd4" "param_out") saved hdone (by simp [stmts, stdGidSetup])
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    exact exec_ldParam_rd stmts
      { cta with threads := done ++ (laneAt localBytes tx 9 r8 false :: todo) }
      (laneAt localBytes tx 9 r8 false) hrt 4 (by omega) "param_out"
      (BitVec.ofNat 64 (nIn * len * 8)) hout
  have hs10 : runCTAWithGlobalLog ((f + 2) + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx 10 r9 false :: todo) } saved =
    runCTAWithGlobalLog (f + 2) stmts
      { cta with threads := done ++ (laneAt localBytes tx 11 r10 false :: todo) } saved := by
    apply pure_lane_step (f + 2) stmts cta done todo localBytes tx 10 r9 r10
      (.cvtaToGlobal .u64 "%rd4" (.reg "%rd4")) saved hdone (by simp [stmts, stdGidSetup])
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    exact exec_cvta_rd stmts
      { cta with threads := done ++ (laneAt localBytes tx 10 r9 false :: todo) }
      (laneAt localBytes tx 10 r9 false) hrt 4 4 (by omega) (by omega)
      (BitVec.ofNat 64 (nIn * len * 8)) (lookup_rfSet_self r8 "%rd4" _)
  have hs11 : runCTAWithGlobalLog ((f + 1) + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx 11 r10 false :: todo) } saved =
    runCTAWithGlobalLog (f + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx 12 r11 false :: todo) } saved := by
    apply pure_lane_step (f + 1) stmts cta done todo localBytes tx 11 r10 r11
      (.shl .b64 "%rd5" (.reg "%rd2") (.immU64 (BitVec.ofNat 64 3))) saved hdone
      (by simp [stmts, stdGidSetup]) (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    have hlk2 : r10.regs.lookup "%rd2" = some (.scalar (BitVec.ofNat 64 gid)) := by
      dsimp only [r10, r9, r8, rf8, PTXRegFile.setPredRaw, rf7]
      rw [lookup_rfSet_ne _ "%rd4" "%rd2" _ (by decide),
          lookup_rfSet_ne _ "%rd4" "%rd2" _ (by decide),
          setAssoc_lookup_ne _ "%p0" "%rd2" _ (by decide),
          lookup_rfSet_ne _ "%rd3" "%rd2" _ (by decide), lookup_rfSet_self]
    have hex := exec_shl_imm stmts
      { cta with threads := done ++ (laneAt localBytes tx 11 r10 false :: todo) }
      (laneAt localBytes tx 11 r10 false) hrt 5 2 3 (by omega) (by omega) (by omega)
      (BitVec.ofNat 64 gid) hlk2
    rw [shl3_eq_mul8 gid hgid61] at hex; exact hex
  have hs12 : runCTAWithGlobalLog (f + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx 12 r11 false :: todo) } saved =
    runCTAWithGlobalLog f stmts
      { cta with threads := done ++
        (laneAt localBytes tx 13 (rf13 blockSize ctaId rf tx len nIn) false :: todo) } saved := by
    have hr11eq : rfSet r11 "%rd6" (BitVec.ofNat 64 (nIn * len * 8 + gid * 8)) =
        rf13 blockSize ctaId rf tx len nIn := by
      dsimp only [r11, rf13, r8]; rw [hr9eq]
    rw [← hr11eq]
    apply pure_lane_step f stmts cta done todo localBytes tx 12 r11
      (rfSet r11 "%rd6" (BitVec.ofNat 64 (nIn * len * 8 + gid * 8)))
      (.add .none .u64 "%rd6" (.reg "%rd4") (.reg "%rd5")) saved hdone
      (by simp [stmts, stdGidSetup]) (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    have hlk4 : r11.regs.lookup "%rd4" = some (.scalar (BitVec.ofNat 64 (nIn * len * 8))) := by
      dsimp only [r11, r10]; rw [lookup_rfSet_ne _ "%rd5" "%rd4" _ (by decide), lookup_rfSet_self]
    have hlk5 : r11.regs.lookup "%rd5" = some (.scalar (BitVec.ofNat 64 (gid * 8))) :=
      lookup_rfSet_self r10 "%rd5" _
    have hex := exec_add_rd stmts
      { cta with threads := done ++ (laneAt localBytes tx 12 r11 false :: todo) }
      (laneAt localBytes tx 12 r11 false) hrt 6 4 5 (by omega) (by omega) (by omega)
      (BitVec.ofNat 64 (nIn * len * 8)) (BitVec.ofNat 64 (gid * 8)) hlk4 hlk5
    rw [add_ofNat64 (nIn * len * 8) (gid * 8) (by omega)] at hex; exact hex
  have hf4 : f + 4 = (f + 3) + 1 := by omega
  have hf3 : f + 3 = (f + 2) + 1 := by omega
  have hf2 : f + 2 = (f + 1) + 1 := by omega
  rw [hf4, hs9, hf3, hs10, hf2, hs11, hs12]

private theorem find_doneLbl_pc (doneLbl : String) (mid : List PTXStmt)
    (hnoLbl : ∀ s ∈ mid, s ≠ .label doneLbl) :
    findLabelPC? (stdGidSetup doneLbl ++ (mid ++ [.label doneLbl, .instr none .ret])) doneLbl =
      some (13 + mid.length + 1) := by
  have hpreNo : ∀ s ∈ stdGidSetup doneLbl ++ mid, s ≠ .label doneLbl := by
    intro s hs; rcases List.mem_append.mp hs with h1 | h2
    · exact gid_no_label doneLbl doneLbl s h1
    · exact hnoLbl s h2
  have hsplit : stdGidSetup doneLbl ++ (mid ++ [.label doneLbl, .instr none .ret]) =
      (stdGidSetup doneLbl ++ mid) ++ (.label doneLbl :: [.instr none .ret]) := by
    simp [List.append_assoc]
  rw [hsplit, findLabelPC_at_split (stdGidSetup doneLbl ++ mid) [.instr none .ret] doneLbl hpreNo]
  congr 1
  simp [stdGidSetup]
  omega

private theorem ret_stmt_at (doneLbl : String) (mid : List PTXStmt) :
    (stdGidSetup doneLbl ++ mid ++ [.label doneLbl, .instr none .ret])[13 + mid.length + 1]? =
      some (.instr none .ret) := by
  have hpreLen : (stdGidSetup doneLbl ++ mid ++ ([PTXStmt.label doneLbl] : List PTXStmt)).length =
      13 + mid.length + 1 := by
    simp [stdGidSetup]; omega
  have hstEq : stdGidSetup doneLbl ++ mid ++ [.label doneLbl, .instr none .ret] =
      (stdGidSetup doneLbl ++ mid ++ ([PTXStmt.label doneLbl] : List PTXStmt)) ++ [.instr none .ret] := by
    simp [List.append_assoc]
  rw [hstEq, ← hpreLen]
  exact stmt_at (stdGidSetup doneLbl ++ mid ++ ([PTXStmt.label doneLbl] : List PTXStmt)) []
    (.instr none .ret)

/-- Out-of-bounds lane (`¬ gid < len`) executes `stdGidSetup`, jumps past `.label doneLbl`
    to `ret`, and halts in 10 steps without touching memory or `epochLog`. -/
theorem run_gid_oob
    (f : Nat) (doneLbl : String) (mid : List PTXStmt) (cta : PTXCTAState)
    (done todo : List PTXThreadState) (blockSize : Nat) (ctaId : Dim3)
    {rf : PTXRegFile} {nP nR nRd : Nat} (hrt : RegTyped rf nP nR nRd)
    (localBytes tx len : Nat)
    (hp : 0 < nP) (hr : 2 < nR) (hrd : 3 < nRd)
    (hcta : cta.ctaId = ctaId) (hblk : cta.blockDim = { x := blockSize, y := 1, z := 1 })
    (htx : tx < 2 ^ 32) (hctaX : ctaId.x < 2 ^ 32) (hblkX : blockSize < 2 ^ 32)
    (hlen : len < 2 ^ 64)
    (hoob : ¬ (ctaId.x * blockSize + tx < len))
    (hnoLbl : ∀ s ∈ mid, s ≠ .label doneLbl)
    (hdone : ∀ t ∈ done, t.halted = true) (saved : List MemAccessLog)
    (hn : cta.paramMem.lookupParam? "param_n" = some (BitVec.ofNat 64 len)) :
    runCTAWithGlobalLog (f + 10)
      (stdGidSetup doneLbl ++ mid ++ [.label doneLbl, .instr none .ret])
      { cta with threads := done ++ (laneAt localBytes tx 0 rf false :: todo) } saved =
    runCTAWithGlobalLog f
      (stdGidSetup doneLbl ++ mid ++ [.label doneLbl, .instr none .ret])
      { cta with threads := done ++
        (doneLane blockSize ctaId rf localBytes tx len (13 + mid.length + 1) :: todo) } saved := by
  let tail : List PTXStmt := [.label doneLbl, .instr none .ret]
  have hstmts : stdGidSetup doneLbl ++ mid ++ tail = stdGidSetup doneLbl ++ (mid ++ tail) := by
    simp [List.append_assoc]
  have hlbl := find_doneLbl_pc doneLbl mid hnoLbl
  have h7 := run_gid_to_rf7 (f + 3) doneLbl (mid ++ tail)
    cta done todo blockSize ctaId hrt localBytes tx len hr hrd hcta hblk htx hctaX hblkX hdone saved hn
  have hcond : true = decide ¬ (ctaId.x * blockSize + tx < len) := by simp [hoob]
  have h2 := run_gid_branch (f + 1) doneLbl (mid ++ tail)
    cta done todo blockSize ctaId hrt localBytes tx len true (13 + mid.length + 1)
    hrd hp htx hctaX hblkX hlen hcond hdone saved hlbl
  simp only [ite_true] at h2
  have hret := runCTA_ret_step f
    (stdGidSetup doneLbl ++ mid ++ tail)
    { cta with threads := done ++
      (laneAt localBytes tx (13 + mid.length + 1) (rf8 blockSize ctaId rf tx len true) false :: todo) }
    done (laneAt localBytes tx (13 + mid.length + 1) (rf8 blockSize ctaId rf tx len true) false)
    todo saved rfl hdone rfl (ret_stmt_at doneLbl mid)
  have hf10 : f + 10 = (f + 3) + 7 := by omega
  have hf3 : f + 3 = (f + 1) + 2 := by omega
  change runCTAWithGlobalLog (f + 10) (stdGidSetup doneLbl ++ mid ++ tail) _ saved =
    runCTAWithGlobalLog f (stdGidSetup doneLbl ++ mid ++ tail) _ saved
  rw [hf10, hstmts, h7, hf3, h2, ← hstmts, hret]
  dsimp only [doneLane, laneAt]

/-- In-bounds lane (`gid < len`) executes `stdGidSetup` in 13 steps, reaching `gidLane`. -/
theorem run_gid_inbounds
    (f : Nat) (doneLbl : String) (mid : List PTXStmt) (cta : PTXCTAState)
    (done todo : List PTXThreadState) (blockSize : Nat) (ctaId : Dim3)
    {rf : PTXRegFile} {nP nR nRd : Nat} (hrt : RegTyped rf nP nR nRd)
    (localBytes tx len nIn : Nat)
    (hp : 0 < nP) (hr : 2 < nR) (hrd : 6 < nRd)
    (hcta : cta.ctaId = ctaId) (hblk : cta.blockDim = { x := blockSize, y := 1, z := 1 })
    (htx : tx < 2 ^ 32) (hctaX : ctaId.x < 2 ^ 32) (hblkX : blockSize < 2 ^ 32)
    (hgidLt : ctaId.x * blockSize + tx < len)
    (houn : (nIn + 1) * len * 8 ≤ 2 ^ 64)
    (hnoLbl : ∀ s ∈ mid, s ≠ .label doneLbl)
    (hdone : ∀ t ∈ done, t.halted = true) (saved : List MemAccessLog)
    (hn : cta.paramMem.lookupParam? "param_n" = some (BitVec.ofNat 64 len))
    (hout : cta.paramMem.lookupParam? "param_out" = some (BitVec.ofNat 64 (nIn * len * 8))) :
    runCTAWithGlobalLog (f + 13)
      (stdGidSetup doneLbl ++ mid ++ [.label doneLbl, .instr none .ret])
      { cta with threads := done ++ (laneAt localBytes tx 0 rf false :: todo) } saved =
    runCTAWithGlobalLog f
      (stdGidSetup doneLbl ++ mid ++ [.label doneLbl, .instr none .ret])
      { cta with threads := done ++
        (gidLane blockSize ctaId rf localBytes tx (ctaId.x * blockSize + tx) nIn len :: todo) }
      saved := by
  let tail : List PTXStmt := [.label doneLbl, .instr none .ret]
  have hstmts : stdGidSetup doneLbl ++ mid ++ tail = stdGidSetup doneLbl ++ (mid ++ tail) := by
    simp [List.append_assoc]
  have hlen : len < 2 ^ 64 := by
    have : (nIn + 1) * len * 8 = nIn * len * 8 + len * 8 := by simp [Nat.add_mul, Nat.one_mul]
    omega
  have hlbl := find_doneLbl_pc doneLbl mid hnoLbl
  have h7 := run_gid_to_rf7 (f + 6) doneLbl (mid ++ tail)
    cta done todo blockSize ctaId hrt localBytes tx len hr (by omega) hcta hblk htx hctaX hblkX hdone saved hn
  have hcond : false = decide ¬ (ctaId.x * blockSize + tx < len) := by simp [hgidLt]
  have h2 := run_gid_branch (f + 4) doneLbl (mid ++ tail)
    cta done todo blockSize ctaId hrt localBytes tx len false (13 + mid.length + 1)
    (by omega) hp htx hctaX hblkX hlen hcond hdone saved hlbl
  simp only [Bool.false_eq_true, ite_false] at h2
  have h4 := run_gid_outaddr f doneLbl (mid ++ tail)
    cta done todo blockSize ctaId hrt localBytes tx len nIn hrd htx hctaX hblkX hgidLt houn hdone saved hout
  have hf13 : f + 13 = (f + 6) + 7 := by omega
  have hf6 : f + 6 = (f + 4) + 2 := by omega
  change runCTAWithGlobalLog (f + 13) (stdGidSetup doneLbl ++ mid ++ tail) _ saved =
    runCTAWithGlobalLog f (stdGidSetup doneLbl ++ mid ++ tail) _ saved
  rw [hf13, hstmts, h7, hf6, h2, h4, laneAt_rf13_eq_gidLane, ← hstmts]

end LeanNative.Proofs.PTXSIMT
