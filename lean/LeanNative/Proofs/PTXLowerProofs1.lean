import LeanNative.Proofs.PTXScalarProofs2

/-!
# Per-Kind `MidBodySpec` Proofs for `PTXLower` (`LeanNative.Proofs.PTXLowerProofs1`)

Proves `MidBodySpec` for the non-branching `ParallelKernelKind` constructors (`mapScaleAdd`,
`zipAdd`, `zipMul`, `dotProduct`, `saxpy`) (`0 sorryAx`, `0 ofReduceBool`).
-/

namespace LeanNative.Proofs.PTXLowerProofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend
open LeanNative.Backend.PTXAst
open LeanNative.Proofs.PTXSIMT
open LeanNative.Backend.PTXLower
open LeanNative.Proofs
open LeanNative.Proofs.PTXScalarProofs

theorem gidSetup_eq_std (doneLbl : String) :
    PTXLower.gidSetup doneLbl = PTXSIMT.stdGidSetup doneLbl := rfl

theorem loadIn_eq_std (k : Nat) (reg : String) :
    PTXLower.loadIn k reg = PTXSIMT.stdLoadIn k reg := rfl

theorem mkPTXParamMem_eq_std (nIn len : Nat) :
    mkPTXParamMem nIn len = stdParamMem nIn len := rfl

theorem concatPTXMems_eq_std (ms : List ByteMemory) :
    concatPTXMems ms = concatByteMems ms := by
  induction ms with
  | nil => rfl
  | cons m rest ih => simp [concatPTXMems, concatByteMems, ih]

theorem mkPTXGlobalMem_eq_pack (nIn len : Nat) (inWords : List (List (BitVec 64))) :
    mkPTXGlobalMem inWords nIn len =
      packGlobalBuffers nIn len (fun j => inWords[j]?.getD []) := by
  unfold mkPTXGlobalMem packGlobalBuffers
  rw [concatPTXMems_eq_std]

theorem gidLane_eq_laneAt (blockSize : Nat) (ctaId : Dim3) (rf : PTXRegFile)
    (localBytes tx gid nIn len : Nat) (hgid : gid = ctaId.x * blockSize + tx) :
    gidLane blockSize ctaId rf localBytes tx gid nIn len =
      laneAt localBytes tx 13 (gidLane blockSize ctaId rf localBytes tx gid nIn len).regs false := by
  subst hgid
  unfold gidLane laneAt
  rfl

theorem gidLane_lookup_len (blockSize : Nat) (ctaId : Dim3) (rf : PTXRegFile)
    (localBytes tx gid nIn len : Nat) :
    (gidLane blockSize ctaId rf localBytes tx gid nIn len).regs.regs.lookup "%rd3" =
      some (.scalar (BitVec.ofNat 64 len)) := by
  unfold gidLane
  dsimp only [PTXRegFile.setPredRaw]
  rw [lookup_rfSet_ne _ "%rd6" "%rd3" _ (by decide),
      lookup_rfSet_ne _ "%rd5" "%rd3" _ (by decide),
      lookup_rfSet_ne _ "%rd4" "%rd3" _ (by decide),
      setAssoc_lookup_ne _ "%p0" "%rd3" _ (by decide),
      lookup_rfSet_self]

theorem sliceAt_mid_split (pre mid suf : List PTXStmt) :
    SliceAt (pre ++ mid ++ suf) mid pre.length := by
  intro k hk
  have h1 : pre.length + k < (pre ++ mid).length := by rw [List.length_append]; omega
  rw [List.getElem?_append_left h1, List.getElem?_append_right (Nat.le_add_right pre.length k)]
  simp

theorem midBodySpec_congr {nP nR nRd nIn len vi maxMidSteps : Nat}
    {doneLbl : String} {mid : List PTXStmt}
    {inWords : Nat → List (BitVec 64)} {hlen : ∀ j < nIn, (inWords j).length = len}
    {out1 out2 : Nat → BitVec 64}
    (h1 : MidBodySpec nP nR nRd nIn len vi maxMidSteps doneLbl mid inWords hlen out1)
    (heq : ∀ gid < len, out1 gid = out2 gid) :
    MidBodySpec nP nR nRd nIn len vi maxMidSteps doneLbl mid inWords hlen out2 := by
  intro blockSize ctaId tx cta done todo saved allowedLanes gid
    hcta hblk hpm htx hctaX hblkX hgidLt hdone hloadAll hlog
  obtain ⟨s, hs, rfM, logM, hrt, h6, hv, hlogM, hrun⟩ :=
    h1 blockSize ctaId tx cta done todo saved allowedLanes
      hcta hblk hpm htx hctaX hblkX hgidLt hdone hloadAll hlog
  rw [heq gid hgidLt] at hv
  exact ⟨s, hs, rfM, logM, hrt, h6, hv, hlogM, hrun⟩

/-- `MidBodySpec` for `.mapScaleAdd scale bias`. -/
theorem midBody_mapScaleAdd (len : Nat) (scale bias : UInt64) (doneLbl : String)
    (inWords : Nat → List (BitVec 64)) (hlen : ∀ j < 1, (inWords j).length = len)
    (houn : (1 + 1) * len * 8 ≤ 2 ^ 64) :
    MidBodySpec 1 3 9 1 len 8 5 doneLbl
      (stdLoadIn 0 "%rd7" ++
        [ins (.mad .lo .u64 "%rd8" (.reg "%rd7") (.immU64 scale.toBitVec) (.immU64 bias.toBitVec))])
      inWords hlen
      (fun gid => if hc : gid < (inWords 0).length then
        (inWords 0)[gid] * scale.toBitVec + bias.toBitVec else 0#64) := by
  intro blockSize ctaId tx cta done todo saved allowedLanes gid
    _ _ hpm _ _ _ hgidLt hdone hloadAll hlog
  let madS := ins (.mad .lo .u64 "%rd8" (.reg "%rd7") (.immU64 scale.toBitVec) (.immU64 bias.toBitVec))
  let epilogue : List PTXStmt :=
    [.instr none (.stGlobal .u64 (.regOffset "%rd6" 0) (.reg s!"%rd{8}")),
     .label doneLbl, .instr none .ret]
  let stmts := stdGidSetup doneLbl ++ (stdLoadIn 0 "%rd7" ++ [madS]) ++ epilogue
  have hlen0 : (inWords 0).length = len := hlen 0 (by omega)
  have hc0 : gid < (inWords 0).length := by omega
  let w0 := (inWords 0)[gid]'hc0
  have hrt0 : RegTyped (PTXRegFile.ofRegDecls (stdKernelRegs 1 3 9)) 1 3 9 :=
    initRegs_typed 1 3 9 (by omega) (by omega) (by omega)
  let rfG := (gidLane blockSize ctaId (PTXRegFile.ofRegDecls (stdKernelRegs 1 3 9)) 0 tx gid 1 len).regs
  have hrtG : RegTyped rfG 1 3 9 := gidLane_typed blockSize ctaId hrt0 0 tx gid 1 len
  have hparam : cta.paramMem.lookupParam? s!"param_in{0}" = some (BitVec.ofNat 64 (0 * len * 8)) := by
    rw [hpm]; exact stdParamMem_lookup_in 1 len 0 (by omega)
  have hload0 : cta.globalMem.loadBits (0 * len * 8 + gid * 8) 8 = some w0 := by
    have := hloadAll 0 (by omega) gid hgidLt; simpa [w0, hlen0] using this
  have hlk5 : rfG.regs.lookup "%rd5" = some (.scalar (BitVec.ofNat 64 (gid * 8))) :=
    gidLane_lookup_off blockSize ctaId _ 0 tx gid 1 len
  let rf1 := rfSet rfG "%rd7" w0
  let rfM := rfSet rf1 "%rd8" (w0 * scale.toBitVec + bias.toBitVec)
  let entry : MemAccessLog := {
    tid := { x := tx, y := 0, z := 0 }, space := .global, addr := 0 * len * 8 + gid * 8,
    width := 8, isWrite := false, isAtomic := false }
  have hlogOk : SafePTXLog (1 * len * 8) len allowedLanes (laneOf1D blockSize ctaId)
      (entry :: cta.epochLog) := by
    obtain ⟨_, hlg⟩ := run_stdLoadIn 0 (stdGidSetup doneLbl) ([madS] ++ epilogue)
      cta done todo hrtG 0 tx 0 7 gid 1 len w0 allowedLanes (laneOf1D blockSize ctaId)
      (by omega) (by omega) (by decide) (by omega) hgidLt houn hdone saved hlk5 hparam hload0 hlog
    exact hlg.run
  refine ⟨5, by omega, rfM, entry :: cta.epochLog, ?_, ?_, ?_, hlogOk, ?_⟩
  · exact regTyped_rfSet (regTyped_rfSet hrtG "%rd7" w0) "%rd8" _
  · rw [lookup_rfSet_ne _ "%rd8" "%rd6" _ (by decide),
        lookup_rfSet_ne _ "%rd7" "%rd6" _ (by decide)]
    exact gidLane_lookup_out blockSize ctaId _ 0 tx gid 1 len
  · have hr8 : s!"%rd{8}" = "%rd8" := rfl
    rw [hr8, lookup_rfSet_self]
    simp only [w0, hc0, dite_true]
  · intro f
    obtain ⟨hrunL, _⟩ := run_stdLoadIn (f + 1) (stdGidSetup doneLbl) ([madS] ++ epilogue)
      cta done todo hrtG 0 tx 0 7 gid 1 len w0 allowedLanes (laneOf1D blockSize ctaId)
      (by omega) (by omega) (by decide) (by omega) hgidLt houn hdone saved hlk5 hparam hload0 hlog
    have hrunL' : runCTAWithGlobalLog ((f + 1) + 4) stmts
        { cta with threads := done ++ (laneAt 0 tx 13 rfG false :: todo) } saved =
      runCTAWithGlobalLog (f + 1) stmts
        { cta with
          threads := done ++ (laneAt 0 tx 17 rf1 false :: todo)
          epochLog := entry :: cta.epochLog } saved := by
      have hstEq : stdGidSetup doneLbl ++ stdLoadIn 0 s!"%rd{7}" ++ ([madS] ++ epilogue) = stmts := by
        have hr : s!"%rd{7}" = "%rd7" := rfl
        rw [hr]; simp [stmts, List.append_assoc]
      have hrf1Eq : rfSet rfG s!"%rd{7}" w0 = rf1 := rfl
      have hpreL : (stdGidSetup doneLbl).length = 13 := rfl
      rw [hpreL, hstEq, hrf1Eq] at hrunL
      exact hrunL
    have hpc17 : stmts[17]? = some madS := by
      have hEq : stmts = (stdGidSetup doneLbl ++ stdLoadIn 0 "%rd7") ++ (madS :: epilogue) := by
        simp [stmts, List.append_assoc]
      have hlen17 : (stdGidSetup doneLbl ++ stdLoadIn 0 "%rd7").length = 17 := rfl
      rw [hEq, ← hlen17]; exact stmt_at _ _ madS
    have hmad : runCTAWithGlobalLog (f + 1) stmts
        { cta with
          threads := done ++ (laneAt 0 tx 17 rf1 false :: todo)
          epochLog := entry :: cta.epochLog } saved =
        runCTAWithGlobalLog f stmts
          { cta with
            threads := done ++ (laneAt 0 tx 18 rfM false :: todo)
            epochLog := entry :: cta.epochLog } saved := by
      apply pure_lane_step f stmts { cta with epochLog := entry :: cta.epochLog }
        done todo 0 tx 17 rf1 rfM
        (.mad .lo .u64 "%rd8" (.reg "%rd7") (.immU64 scale.toBitVec) (.immU64 bias.toBitVec))
        saved hdone hpc17 (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
      have hex := exec_mad_lo_imm2 stmts
        { cta with
          threads := done ++ (laneAt 0 tx 17 rf1 false :: todo)
          epochLog := entry :: cta.epochLog }
        (laneAt 0 tx 17 rf1 false) (regTyped_rfSet hrtG "%rd7" w0) 8 7 (by omega) (by omega)
        w0 scale.toBitVec bias.toBitVec (by
          have hr7 : s!"%rd{7}" = "%rd7" := rfl
          rw [hr7]; exact lookup_rfSet_self rfG "%rd7" w0)
      have hrfM : (laneAt 0 tx 17 rf1 false).regs.setScalarRaw s!"%rd{8}"
          (w0 * scale.toBitVec + bias.toBitVec) = rfM := rfl
      rw [hrfM] at hex
      exact hex
    have hf5 : f + 5 = (f + 1) + 4 := by omega
    have hmidLen : 13 + (stdLoadIn 0 "%rd7" ++ [madS]).length = 18 := rfl
    rw [hmidLen, hf5, gidLane_eq_laneAt blockSize ctaId _ 0 tx gid 1 len rfl, hrunL', hmad]

/-- Shared 2-input `MidBodySpec` helper for `zipAdd`, `zipMul`, `dotProduct`, and `saxpy`. -/
private theorem midBody_twoInputs (len : Nat) (opInstr : PTXInstr)
    (comb : BitVec 64 → BitVec 64 → BitVec 64) (doneLbl : String)
    (inWords : Nat → List (BitVec 64)) (hlen : ∀ j < 2, (inWords j).length = len)
    (houn : (2 + 1) * len * 8 ≤ 2 ^ 64)
    (hnBar : ∀ b, opInstr ≠ .barSync b)
    (hnShfl : ∀ d s o c m, opInstr ≠ .shflSyncBfly d s o c m)
    (hexOp : ∀ (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState) (w0 w1 : BitVec 64),
      RegTyped th.regs 1 3 10 →
      th.regs.regs.lookup "%rd7" = some (.scalar w0) →
      th.regs.regs.lookup "%rd8" = some (.scalar w1) →
      execNonBarrierInstr stmts cta th opInstr =
        .ok (thStep th (rfSet th.regs "%rd9" (comb w0 w1)),
          cta.globalMem, cta.sharedMem, cta.epochLog)) :
    MidBodySpec 1 3 10 2 len 9 9 doneLbl
      (stdLoadIn 0 "%rd7" ++ stdLoadIn 1 "%rd8" ++ [ins opInstr])
      inWords hlen
      (fun gid =>
        if hc0 : gid < (inWords 0).length then
          if hc1 : gid < (inWords 1).length then
            comb ((inWords 0)[gid]'hc0) ((inWords 1)[gid]'hc1)
          else 0#64
        else 0#64) := by
  intro blockSize ctaId tx cta done todo saved allowedLanes gid
    _ _ hpm _ _ _ hgidLt hdone hloadAll hlog
  let epilogue : List PTXStmt :=
    [.instr none (.stGlobal .u64 (.regOffset "%rd6" 0) (.reg s!"%rd{9}")),
     .label doneLbl, .instr none .ret]
  let stmts := stdGidSetup doneLbl ++ (stdLoadIn 0 "%rd7" ++ stdLoadIn 1 "%rd8" ++ [ins opInstr]) ++ epilogue
  have hlen0 : (inWords 0).length = len := hlen 0 (by omega)
  have hlen1 : (inWords 1).length = len := hlen 1 (by omega)
  have hc0 : gid < (inWords 0).length := by omega
  have hc1 : gid < (inWords 1).length := by omega
  let w0 := (inWords 0)[gid]'hc0
  let w1 := (inWords 1)[gid]'hc1
  have hrt0 : RegTyped (PTXRegFile.ofRegDecls (stdKernelRegs 1 3 10)) 1 3 10 :=
    initRegs_typed 1 3 10 (by omega) (by omega) (by omega)
  let rfG := (gidLane blockSize ctaId (PTXRegFile.ofRegDecls (stdKernelRegs 1 3 10)) 0 tx gid 2 len).regs
  have hrtG : RegTyped rfG 1 3 10 := gidLane_typed blockSize ctaId hrt0 0 tx gid 2 len
  have hp0 : cta.paramMem.lookupParam? s!"param_in{0}" = some (BitVec.ofNat 64 (0 * len * 8)) := by
    rw [hpm]; exact stdParamMem_lookup_in 2 len 0 (by omega)
  have hp1 : cta.paramMem.lookupParam? s!"param_in{1}" = some (BitVec.ofNat 64 (1 * len * 8)) := by
    rw [hpm]; exact stdParamMem_lookup_in 2 len 1 (by omega)
  have hld0 : cta.globalMem.loadBits (0 * len * 8 + gid * 8) 8 = some w0 := by
    have := hloadAll 0 (by omega) gid hgidLt; simpa [w0, hlen0] using this
  have hld1 : cta.globalMem.loadBits (1 * len * 8 + gid * 8) 8 = some w1 := by
    have := hloadAll 1 (by omega) gid hgidLt; simpa [w1, hlen1] using this
  have hlk5G : rfG.regs.lookup "%rd5" = some (.scalar (BitVec.ofNat 64 (gid * 8))) :=
    gidLane_lookup_off blockSize ctaId _ 0 tx gid 2 len
  let rf1 := rfSet rfG "%rd7" w0
  have hrt1 : RegTyped rf1 1 3 10 := regTyped_rfSet hrtG "%rd7" w0
  have hlk5_1 : rf1.regs.lookup "%rd5" = some (.scalar (BitVec.ofNat 64 (gid * 8))) := by
    dsimp only [rf1]; rw [lookup_rfSet_ne _ "%rd7" "%rd5" _ (by decide), hlk5G]
  let rf2 := rfSet rf1 "%rd8" w1
  have hrt2 : RegTyped rf2 1 3 10 := regTyped_rfSet hrt1 "%rd8" w1
  let rfM := rfSet rf2 "%rd9" (comb w0 w1)
  let e0 : MemAccessLog := {
    tid := { x := tx, y := 0, z := 0 }, space := .global, addr := 0 * len * 8 + gid * 8,
    width := 8, isWrite := false, isAtomic := false }
  let e1 : MemAccessLog := {
    tid := { x := tx, y := 0, z := 0 }, space := .global, addr := 1 * len * 8 + gid * 8,
    width := 8, isWrite := false, isAtomic := false }
  let cta0 : PTXCTAState := { cta with epochLog := e0 :: cta.epochLog }
  have hlog0 : SafePTXLog (2 * len * 8) len allowedLanes (laneOf1D blockSize ctaId)
      (e0 :: cta.epochLog) := by
    obtain ⟨_, hlg⟩ := run_stdLoadIn 0 (stdGidSetup doneLbl)
      (stdLoadIn 1 "%rd8" ++ [ins opInstr] ++ epilogue)
      cta done todo hrtG 0 tx 0 7 gid 2 len w0 allowedLanes (laneOf1D blockSize ctaId)
      (by omega) (by omega) (by decide) (by omega) hgidLt houn hdone saved hlk5G hp0 hld0 hlog
    exact hlg.run
  have hlog1 : SafePTXLog (2 * len * 8) len allowedLanes (laneOf1D blockSize ctaId)
      (e1 :: e0 :: cta.epochLog) := by
    obtain ⟨_, hlg⟩ := run_stdLoadIn 0 (stdGidSetup doneLbl ++ stdLoadIn 0 "%rd7")
      ([ins opInstr] ++ epilogue)
      cta0 done todo hrt1 0 tx 1 8 gid 2 len w1
      allowedLanes (laneOf1D blockSize ctaId)
      (by omega) (by omega) (by decide) (by omega) hgidLt houn hdone saved hlk5_1 hp1 hld1 hlog0
    exact hlg.run
  refine ⟨9, by omega, rfM, e1 :: e0 :: cta.epochLog, regTyped_rfSet hrt2 "%rd9" _, ?_, ?_, hlog1, ?_⟩
  · dsimp only [rfM, rf2, rf1]
    rw [lookup_rfSet_ne _ "%rd9" "%rd6" _ (by decide),
        lookup_rfSet_ne _ "%rd8" "%rd6" _ (by decide),
        lookup_rfSet_ne _ "%rd7" "%rd6" _ (by decide)]
    exact gidLane_lookup_out blockSize ctaId _ 0 tx gid 2 len
  · have hr9 : s!"%rd{9}" = "%rd9" := rfl
    rw [hr9, lookup_rfSet_self]
    simp only [w0, w1, hc0, hc1, dite_true]
  · intro f
    obtain ⟨hr0, _⟩ := run_stdLoadIn (f + 5) (stdGidSetup doneLbl)
      (stdLoadIn 1 "%rd8" ++ [ins opInstr] ++ epilogue)
      cta done todo hrtG 0 tx 0 7 gid 2 len w0 allowedLanes (laneOf1D blockSize ctaId)
      (by omega) (by omega) (by decide) (by omega) hgidLt houn hdone saved hlk5G hp0 hld0 hlog
    have hr0' : runCTAWithGlobalLog ((f + 5) + 4) stmts
        { cta with threads := done ++ (laneAt 0 tx 13 rfG false :: todo) } saved =
      runCTAWithGlobalLog (f + 5) stmts
        { cta with threads := done ++ (laneAt 0 tx 17 rf1 false :: todo), epochLog := e0 :: cta.epochLog } saved := by
      have hst0 : stdGidSetup doneLbl ++ stdLoadIn 0 s!"%rd{7}" ++
          (stdLoadIn 1 "%rd8" ++ [ins opInstr] ++ epilogue) = stmts := by
        have hr : s!"%rd{7}" = "%rd7" := rfl
        rw [hr]; simp [stmts, List.append_assoc]
      have hrf1Eq : rfSet rfG s!"%rd{7}" w0 = rf1 := rfl
      have hlen13 : (stdGidSetup doneLbl).length = 13 := rfl
      rw [hlen13, hst0, hrf1Eq] at hr0; exact hr0
    obtain ⟨hr1, _⟩ := run_stdLoadIn (f + 1) (stdGidSetup doneLbl ++ stdLoadIn 0 "%rd7")
      ([ins opInstr] ++ epilogue)
      cta0 done todo hrt1 0 tx 1 8 gid 2 len w1
      allowedLanes (laneOf1D blockSize ctaId)
      (by omega) (by omega) (by decide) (by omega) hgidLt houn hdone saved hlk5_1 hp1 hld1 hlog0
    have hr1' : runCTAWithGlobalLog ((f + 1) + 4) stmts
        { cta with threads := done ++ (laneAt 0 tx 17 rf1 false :: todo), epochLog := e0 :: cta.epochLog } saved =
      runCTAWithGlobalLog (f + 1) stmts
        { cta with threads := done ++ (laneAt 0 tx 21 rf2 false :: todo), epochLog := e1 :: e0 :: cta.epochLog } saved := by
      have hst1 : (stdGidSetup doneLbl ++ stdLoadIn 0 "%rd7") ++ stdLoadIn 1 s!"%rd{8}" ++
          ([ins opInstr] ++ epilogue) = stmts := by
        have hr : s!"%rd{8}" = "%rd8" := rfl
        rw [hr]; simp [stmts, List.append_assoc]
      have hrf2Eq : rfSet rf1 s!"%rd{8}" w1 = rf2 := rfl
      have hlen17 : (stdGidSetup doneLbl ++ stdLoadIn 0 "%rd7").length = 17 := rfl
      rw [hlen17, hst1, hrf2Eq] at hr1; exact hr1
    have hpc21 : stmts[21]? = some (ins opInstr) := by
      have hEq : stmts = (stdGidSetup doneLbl ++ stdLoadIn 0 "%rd7" ++ stdLoadIn 1 "%rd8") ++
          (ins opInstr :: epilogue) := by simp [stmts, List.append_assoc]
      have hlen21 : (stdGidSetup doneLbl ++ stdLoadIn 0 "%rd7" ++ stdLoadIn 1 "%rd8").length = 21 := rfl
      rw [hEq, ← hlen21]; exact stmt_at _ _ (ins opInstr)
    have hlk7 : rf2.regs.lookup "%rd7" = some (.scalar w0) := by
      dsimp only [rf2, rf1]; rw [lookup_rfSet_ne _ "%rd8" "%rd7" _ (by decide), lookup_rfSet_self]
    have hlk8 : rf2.regs.lookup "%rd8" = some (.scalar w1) := lookup_rfSet_self rf1 "%rd8" w1
    have hr2 : runCTAWithGlobalLog (f + 1) stmts
        { cta with
          threads := done ++ (laneAt 0 tx 21 rf2 false :: todo)
          epochLog := e1 :: e0 :: cta.epochLog } saved =
        runCTAWithGlobalLog f stmts
          { cta with
            threads := done ++ (laneAt 0 tx 22 rfM false :: todo)
            epochLog := e1 :: e0 :: cta.epochLog } saved := by
      apply pure_lane_step f stmts { cta with epochLog := e1 :: e0 :: cta.epochLog }
        done todo 0 tx 21 rf2 rfM opInstr saved hdone hpc21 hnBar hnShfl
      exact hexOp stmts _ _ w0 w1 hrt2 hlk7 hlk8
    have hf9 : f + 9 = (f + 5) + 4 := by omega
    have hf5 : f + 5 = (f + 1) + 4 := by omega
    have hmidLen : 13 + (stdLoadIn 0 "%rd7" ++ stdLoadIn 1 "%rd8" ++ [ins opInstr]).length = 22 := rfl
    rw [hmidLen, hf9, gidLane_eq_laneAt blockSize ctaId _ 0 tx gid 2 len rfl, hr0', hf5, hr1', hr2]

theorem midBody_zipAdd (len : Nat) (doneLbl : String)
    (inWords : Nat → List (BitVec 64)) (hlen : ∀ j < 2, (inWords j).length = len)
    (houn : (2 + 1) * len * 8 ≤ 2 ^ 64) :
    MidBodySpec 1 3 10 2 len 9 9 doneLbl
      (stdLoadIn 0 "%rd7" ++ stdLoadIn 1 "%rd8" ++
        [ins (.add .none .u64 "%rd9" (.reg "%rd7") (.reg "%rd8"))])
      inWords hlen
      (fun gid =>
        if hc0 : gid < (inWords 0).length then
          if hc1 : gid < (inWords 1).length then
            (inWords 0)[gid]'hc0 + (inWords 1)[gid]'hc1
          else 0#64
        else 0#64) :=
  midBody_twoInputs len (.add .none .u64 "%rd9" (.reg "%rd7") (.reg "%rd8")) (· + ·)
    doneLbl inWords hlen houn (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    fun stmts cta th w0 w1 hrt h7 h8 => by
      have hex := exec_add_rd stmts cta th hrt 9 7 8 (by omega) (by omega) (by omega) w0 w1 h7 h8
      exact hex

theorem midBody_zipMul (len : Nat) (doneLbl : String)
    (inWords : Nat → List (BitVec 64)) (hlen : ∀ j < 2, (inWords j).length = len)
    (houn : (2 + 1) * len * 8 ≤ 2 ^ 64) :
    MidBodySpec 1 3 10 2 len 9 9 doneLbl
      (stdLoadIn 0 "%rd7" ++ stdLoadIn 1 "%rd8" ++
        [ins (.mul .lo .u64 "%rd9" (.reg "%rd7") (.reg "%rd8"))])
      inWords hlen
      (fun gid =>
        if hc0 : gid < (inWords 0).length then
          if hc1 : gid < (inWords 1).length then
            (inWords 0)[gid]'hc0 * (inWords 1)[gid]'hc1
          else 0#64
        else 0#64) :=
  midBody_twoInputs len (.mul .lo .u64 "%rd9" (.reg "%rd7") (.reg "%rd8")) (· * ·)
    doneLbl inWords hlen houn (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    fun stmts cta th w0 w1 hrt h7 h8 => by
      have hex := exec_mul_lo_rd stmts cta th hrt 9 7 8 (by omega) (by omega) (by omega) w0 w1 h7 h8
      exact hex

theorem midBody_saxpy (len : Nat) (alpha : UInt64) (doneLbl : String)
    (inWords : Nat → List (BitVec 64)) (hlen : ∀ j < 2, (inWords j).length = len)
    (houn : (2 + 1) * len * 8 ≤ 2 ^ 64) :
    MidBodySpec 1 3 10 2 len 9 9 doneLbl
      (stdLoadIn 0 "%rd7" ++ stdLoadIn 1 "%rd8" ++
        [ins (.mad .lo .u64 "%rd9" (.reg "%rd7") (.immU64 alpha.toBitVec) (.reg "%rd8"))])
      inWords hlen
      (fun gid =>
        if hc0 : gid < (inWords 0).length then
          if hc1 : gid < (inWords 1).length then
            (inWords 0)[gid]'hc0 * alpha.toBitVec + (inWords 1)[gid]'hc1
          else 0#64
        else 0#64) :=
  midBody_twoInputs len (.mad .lo .u64 "%rd9" (.reg "%rd7") (.immU64 alpha.toBitVec) (.reg "%rd8"))
    (fun w0 w1 => w0 * alpha.toBitVec + w1)
    doneLbl inWords hlen houn (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    fun stmts cta th w0 w1 hrt h7 h8 => by
      have hex := exec_mad_lo_imm stmts cta th hrt 9 7 8 (by omega) (by omega) (by omega) w0 w1 alpha.toBitVec h7 h8
      exact hex

end LeanNative.Proofs.PTXLowerProofs
