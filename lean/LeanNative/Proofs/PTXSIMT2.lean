import LeanNative.Proofs.PTXSIMT1

namespace LeanNative.Proofs.PTXSIMT

open LeanNative.Backend.PTXAst

/-- Every log entry in `logs` is a `.global` access in the read-only input region `[0, outBase)`
    (`isWrite = false`) or a non-atomic 8-byte write at `(outBase + cx * 8)` by a lane whose
    global linear ID `(ctaId.x * blockSize + tid.x)` equals `cx < len` and belongs to `allowedLanes`. -/
def SafePTXLog (outBase len : Nat) (allowedLanes : Nat → Prop)
    (laneOf : Dim3 → Nat) (logs : List MemAccessLog) : Prop :=
  ∀ e ∈ logs,
    e.space = .global ∧ e.isAtomic = false ∧ e.width = 8 ∧
    ((e.isWrite = false ∧ e.addr + 8 ≤ outBase) ∨
     (e.isWrite = true ∧ ∃ cx < len, allowedLanes cx ∧ laneOf e.tid = cx ∧ e.addr = outBase + cx * 8))

/-- For cross-CTA global logs: every entry is `.global`, `isAtomic = false`, `width = 8`, and either
    an input read (`e.addr + 8 ≤ outBase`, `isWrite = false`) or an output write at `outBase + cx * 8`
    for some `cx < len` satisfying `ctaPred cx`. -/
def SafeGlobalLog (outBase len : Nat) (ctaPred : Nat → Prop) (logs : List MemAccessLog) : Prop :=
  ∀ e ∈ logs,
    e.space = .global ∧ e.isAtomic = false ∧ e.width = 8 ∧
    ((e.isWrite = false ∧ e.addr + 8 ≤ outBase) ∨
     (e.isWrite = true ∧ ∃ cx < len, ctaPred cx ∧ e.addr = outBase + cx * 8))

theorem findDataRace_none_read (outBase len : Nat) (allowedLanes : Nat → Prop)
    (laneOf : Dim3 → Nat) (logs : List MemAccessLog) (tid : Dim3) (addr : Nat)
    (hlog : SafePTXLog outBase len allowedLanes laneOf logs)
    (hin : addr + 8 ≤ outBase) :
    findDataRace? logs tid .global addr 8 false false = none := by
  induction logs with
  | nil => rfl
  | cons e rest ih =>
    rcases hlog e (List.Mem.head rest) with ⟨hsp, _, hw, hkind⟩
    have hrest : SafePTXLog outBase len allowedLanes laneOf rest :=
      fun x hx => hlog x (List.Mem.tail e hx)
    unfold findDataRace?
    rcases hkind with ⟨hew, hea⟩ | ⟨hew, cx, _, _, _, hea⟩
    · simp [hew, ih hrest]
    · have hno : rangesOverlap addr 8 e.addr e.width = false := by
        simp [rangesOverlap, hw, hea]; omega
      simp [hno, ih hrest]

theorem findDataRace_none_write (outBase len : Nat) (allowedLanes : Nat → Prop)
    (laneOf : Dim3 → Nat) (logs : List MemAccessLog) (tid : Dim3) (cx : Nat)
    (hlog : SafePTXLog outBase len allowedLanes laneOf logs)
    (_hcx : cx < len) (hnot : ¬ allowedLanes cx) :
    findDataRace? logs tid .global (outBase + cx * 8) 8 true false = none := by
  induction logs with
  | nil => rfl
  | cons e rest ih =>
    rcases hlog e (List.Mem.head rest) with ⟨hsp, _, hw, hkind⟩
    have hrest : SafePTXLog outBase len allowedLanes laneOf rest :=
      fun x hx => hlog x (List.Mem.tail e hx)
    unfold findDataRace?
    rcases hkind with ⟨_, hea⟩ | ⟨_, cx', _, hal, _, hea⟩
    · have hno : rangesOverlap (outBase + cx * 8) 8 e.addr e.width = false := by
        simp [rangesOverlap, hw]; omega
      simp [hno, ih hrest]
    · have hne : cx ≠ cx' := fun heq => hnot (heq ▸ hal)
      have hno : rangesOverlap (outBase + cx * 8) 8 e.addr e.width = false := by
        simp [rangesOverlap, hw, hea]; omega
      simp [hno, ih hrest]

theorem findCrossCTARace_none (outBase len : Nat) (pPrior pCur : Nat → Prop)
    (hdisj : ∀ cx, pPrior cx → pCur cx → False)
    (prior : List MemAccessLog) (entry : MemAccessLog)
    (hprior : SafeGlobalLog outBase len pPrior prior)
    (hentry : entry.space = .global ∧ entry.isAtomic = false ∧ entry.width = 8 ∧
      ((entry.isWrite = false ∧ entry.addr + 8 ≤ outBase) ∨
       (entry.isWrite = true ∧ ∃ cx < len, pCur cx ∧ entry.addr = outBase + cx * 8))) :
    findCrossCTARace? prior entry = none := by
  induction prior with
  | nil => rfl
  | cons p rest ih =>
    rcases hprior p (List.Mem.head rest) with ⟨_, _, hpw, hpkind⟩
    have hrest : SafeGlobalLog outBase len pPrior rest :=
      fun x hx => hprior x (List.Mem.tail p hx)
    have hrec := ih hrest
    rcases hentry with ⟨_, _, hew, hekind⟩
    unfold findCrossCTARace?
    rcases hekind with ⟨hewr, headr⟩ | ⟨hewr, cxE, _, hcE, headr⟩
    · rcases hpkind with ⟨hpwr, _⟩ | ⟨_, cxP, _, _, hpadr⟩
      · simp [hewr, hpwr, hrec]
      · have hno : rangesOverlap entry.addr entry.width p.addr p.width = false := by
          simp [rangesOverlap, hew, hpw, hpadr]; omega
        simp [hno, hrec]
    · rcases hpkind with ⟨_, hpadr⟩ | ⟨_, cxP, _, hcP, hpadr⟩
      · have hno : rangesOverlap entry.addr entry.width p.addr p.width = false := by
          simp [rangesOverlap, hew, hpw, headr]; omega
        simp [hno, hrec]
      · have hne : cxE ≠ cxP := fun h => hdisj cxE (h ▸ hcP) hcE
        have hno : rangesOverlap entry.addr entry.width p.addr p.width = false := by
          simp [rangesOverlap, hew, hpw, headr, hpadr]; omega
        simp [hno, hrec]

theorem checkCrossCTAGlobalLog_ok (outBase len : Nat) (pPrior pCur : Nat → Prop)
    (hdisj : ∀ cx, pPrior cx → pCur cx → False)
    (prior cur : List MemAccessLog)
    (hprior : SafeGlobalLog outBase len pPrior prior)
    (hcur : SafeGlobalLog outBase len pCur cur) :
    checkCrossCTAGlobalLog prior cur = .ok () := by
  induction cur with
  | nil => rfl
  | cons e rest ih =>
    have he := hcur e (List.Mem.head rest)
    have hrest : SafeGlobalLog outBase len pCur rest :=
      fun x hx => hcur x (List.Mem.tail e hx)
    unfold checkCrossCTAGlobalLog
    have hsp : (e.space != .global) = false := by rw [he.1]; rfl
    have hnone := findCrossCTARace_none outBase len pPrior pCur hdisj prior e hprior he
    simp [hsp, hnone, ih hrest]


theorem RegTyped.setScalarRaw_preserves {rf : PTXRegFile} {nP nR nRd : Nat}
    (hrt : RegTyped rf nP nR nRd) (name : String) (v : BitVec 64) :
    RegTyped (rf.setScalarRaw name v) nP nR nRd := hrt

theorem RegTyped.setPredRaw_preserves {rf : PTXRegFile} {nP nR nRd : Nat}
    (hrt : RegTyped rf nP nR nRd) (name : String) (b : Bool) :
    RegTyped (rf.setPredRaw name b) nP nR nRd := hrt

theorem readScalarChecked_rd {rf : PTXRegFile} {nP nR nRd : Nat}
    (hrt : RegTyped rf nP nR nRd) (i : Nat) (hi : i < nRd) (v : BitVec 64)
    (hlk : rf.regs.lookup s!"%rd{i}" = some (.scalar v)) :
    rf.readScalarChecked s!"%rd{i}" (some 64) = .ok v := by
  rcases hrt with ⟨henf, _, _, hrd⟩
  unfold PTXRegFile.readScalarChecked
  simp only [henf, ite_true, hrd i hi, hlk]
  rfl

theorem readScalarChecked_r {rf : PTXRegFile} {nP nR nRd : Nat}
    (hrt : RegTyped rf nP nR nRd) (i : Nat) (hi : i < nR) (v : BitVec 64)
    (hlk : rf.regs.lookup s!"%r{i}" = some (.scalar v)) :
    rf.readScalarChecked s!"%r{i}" (some 32) = .ok v := by
  rcases hrt with ⟨henf, _, hr, _⟩
  unfold PTXRegFile.readScalarChecked
  simp only [henf, ite_true, hr i hi, hlk]
  rfl

theorem readPredChecked_p {rf : PTXRegFile} {nP nR nRd : Nat}
    (hrt : RegTyped rf nP nR nRd) (i : Nat) (hi : i < nP) (b : Bool)
    (hlk : rf.regs.lookup s!"%p{i}" = some (.pred b)) :
    rf.readPredChecked s!"%p{i}" = .ok b := by
  rcases hrt with ⟨henf, hp, _, _⟩
  unfold PTXRegFile.readPredChecked
  simp only [henf, ite_true, hp i hi, hlk]
  rfl

theorem setScalar_rd {rf : PTXRegFile} {nP nR nRd : Nat}
    (hrt : RegTyped rf nP nR nRd) (i : Nat) (hi : i < nRd) (v : BitVec 64) :
    rf.setScalar s!"%rd{i}" v (some 64) = .ok (rf.setScalarRaw s!"%rd{i}" v) := by
  rcases hrt with ⟨henf, _, _, hrd⟩
  unfold PTXRegFile.setScalar
  simp only [henf, ite_true, hrd i hi]
  rfl

theorem setScalar_r {rf : PTXRegFile} {nP nR nRd : Nat}
    (hrt : RegTyped rf nP nR nRd) (i : Nat) (hi : i < nR) (v : BitVec 64)
    (hfit : (v >>> 32) = 0#64) :
    rf.setScalar s!"%r{i}" v (some 32) =
      .ok (rf.setScalarRaw s!"%r{i}" (v &&& 0xFFFF_FFFF#64)) := by
  rcases hrt with ⟨henf, _, hr, _⟩
  have hmask : v &&& 0xFFFF_FFFF#64 = v := by
    apply BitVec.eq_of_toNat_eq
    have hdiv : v.toNat / 4294967296 = 0 := by
      have := congrArg BitVec.toNat hfit
      simpa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using this
    have hlt : v.toNat < 4294967296 := by omega
    have hand : v.toNat &&& 4294967295 = v.toNat := by
      have : 4294967295 = 2 ^ 32 - 1 := rfl
      rw [this, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt]
    simpa [BitVec.toNat_and] using hand
  have hne : ((v >>> 32) != 0#64) = false := by rw [hfit]; rfl
  have hne2 : (((v &&& 0xFFFF_FFFF#64) >>> 32) != 0#64) = false := by rw [hmask, hfit]; rfl
  have hpred : (PTXType.u32 == PTXType.pred) = false := rfl
  have hbw : PTXType.u32.bitWidth = 32 := rfl
  have h32_32 : (32 == 32) = true := rfl
  have h32_64 : (32 == 64) = false := rfl
  have hd32 : decide (32 < 64) = true := rfl
  unfold PTXRegFile.setScalar
  simp only [henf, ite_true, hr i hi, hpred, hbw, h32_32, h32_64, hd32,
    Bool.true_or, Bool.not_true, Bool.false_eq_true, ite_false,
    hne, maskForType, hne2, Bool.true_and]

theorem setPred_p {rf : PTXRegFile} {nP nR nRd : Nat}
    (hrt : RegTyped rf nP nR nRd) (i : Nat) (hi : i < nP) (b : Bool) :
    rf.setPred s!"%p{i}" b = .ok (rf.setPredRaw s!"%p{i}" b) := by
  rcases hrt with ⟨henf, hp, _, _⟩
  unfold PTXRegFile.setPred
  simp only [henf, ite_true, hp i hi]
  rfl

theorem findLabelPC_append_skip (pre suf : List PTXStmt) (lbl : String)
    (hno : ∀ s ∈ pre, s ≠ .label lbl) :
    findLabelPC? (pre ++ suf) lbl = (findLabelPC? suf lbl).map (· + pre.length) := by
  induction pre with
  | nil =>
    cases h : findLabelPC? suf lbl <;> simp [h]
  | cons hd tl ih =>
    have hhd : hd ≠ .label lbl := hno hd (.head tl)
    have htl : ∀ s ∈ tl, s ≠ .label lbl := fun s hs => hno s (.tail hd hs)
    cases hd with
    | label l =>
      have hne : (l == lbl) = false := beq_eq_false_iff_ne.mpr fun h => hhd (h ▸ rfl)
      simp only [List.cons_append, findLabelPC?, hne, Bool.false_eq_true, ite_false, ih htl,
        Option.map_map, List.length_cons]
      cases findLabelPC? suf lbl <;> simp [Function.comp, Nat.add_assoc]
    | instr g i =>
      simp only [List.cons_append, findLabelPC?, ih htl, Option.map_map, List.length_cons]
      cases findLabelPC? suf lbl <;> simp [Function.comp, Nat.add_assoc]

theorem findLabelPC_at_split (pre suf : List PTXStmt) (lbl : String)
    (hno : ∀ s ∈ pre, s ≠ .label lbl) :
    findLabelPC? (pre ++ (.label lbl :: suf)) lbl = some (pre.length + 1) := by
  rw [findLabelPC_append_skip pre (.label lbl :: suf) lbl hno]
  simp [findLabelPC?, Nat.add_comm]

theorem step_ret (stmts : List PTXStmt) (cta : PTXCTAState)
    (done : List PTXThreadState) (th : PTXThreadState) (todo : List PTXThreadState)
    (hthreads : cta.threads = done ++ (th :: todo))
    (hdone : ∀ t ∈ done, t.halted = true)
    (hnh : th.halted = false)
    (hpc : stmts[th.pc]? = some (.instr none .ret)) :
    stepCTA stmts cta = .ok (false, { cta with
      threads := done ++ ({ th with pc := th.pc + 1, halted := true } :: todo) }) := by
  have h := step_non_barrier_instr stmts cta done th todo none .ret
    { th with pc := th.pc + 1, halted := true } cta.globalMem cta.sharedMem cta.epochLog
    hthreads hdone hnh hpc (fun _ hc => nomatch hc) (fun _ _ _ _ _ hc => nomatch hc) rfl
  exact h

theorem step_pure_instr (stmts : List PTXStmt) (cta : PTXCTAState)
    (done : List PTXThreadState) (th : PTXThreadState) (todo : List PTXThreadState)
    (ins : PTXInstr) (rf' : PTXRegFile)
    (hthreads : cta.threads = done ++ (th :: todo))
    (hdone : ∀ t ∈ done, t.halted = true)
    (hnh : th.halted = false)
    (hpc : stmts[th.pc]? = some (.instr none ins))
    (hnBar : ∀ b, ins ≠ .barSync b)
    (hnShfl : ∀ d s o c m, ins ≠ .shflSyncBfly d s o c m)
    (hexec : execNonBarrierInstr stmts cta th ins =
      .ok ({ th with pc := th.pc + 1, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)) :
    stepCTA stmts cta = .ok (false, { cta with
      threads := done ++ ({ th with pc := th.pc + 1, regs := rf' } :: todo) }) := by
  have hp : execPredicatedInstr stmts cta th none ins =
      .ok ({ th with pc := th.pc + 1, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog) := by
    unfold execPredicatedInstr evalPredGuard; dsimp only [PTXOutcome.bind]; exact hexec
  exact step_non_barrier_instr stmts cta done th todo none ins
    { th with pc := th.pc + 1, regs := rf' } cta.globalMem cta.sharedMem cta.epochLog
    hthreads hdone hnh hpc hnBar hnShfl hp

theorem runCTA_pure_instr (f : Nat) (stmts : List PTXStmt) (cta : PTXCTAState)
    (done : List PTXThreadState) (th : PTXThreadState) (todo : List PTXThreadState)
    (ins : PTXInstr) (rf' : PTXRegFile) (saved : List MemAccessLog)
    (hthreads : cta.threads = done ++ (th :: todo))
    (hdone : ∀ t ∈ done, t.halted = true)
    (hnh : th.halted = false)
    (hpc : stmts[th.pc]? = some (.instr none ins))
    (hnBar : ∀ b, ins ≠ .barSync b)
    (hnShfl : ∀ d s o c m, ins ≠ .shflSyncBfly d s o c m)
    (hexec : execNonBarrierInstr stmts cta th ins =
      .ok ({ th with pc := th.pc + 1, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)) :
    runCTAWithGlobalLog (f + 1) stmts cta saved =
      runCTAWithGlobalLog f stmts
        { cta with threads := done ++ ({ th with pc := th.pc + 1, regs := rf' } :: todo) } saved := by
  have hstep := step_pure_instr stmts cta done th todo ins rf' hthreads hdone hnh hpc hnBar hnShfl hexec
  have hnc : cta.epochLog = [] ∨
      ({ cta with threads := done ++ ({ th with pc := th.pc + 1, regs := rf' } :: todo) } : PTXCTAState).epochLog ≠ [] := by
    cases h : cta.epochLog with
    | nil => exact Or.inl rfl
    | cons x xs => exact Or.inr (by simp)
  exact runCTAWithGlobalLog_step_no_clear f stmts cta _ saved hstep hnc

theorem runCTA_label_step (f : Nat) (stmts : List PTXStmt) (cta : PTXCTAState)
    (done : List PTXThreadState) (th : PTXThreadState) (todo : List PTXThreadState)
    (lbl : String) (saved : List MemAccessLog)
    (hthreads : cta.threads = done ++ (th :: todo))
    (hdone : ∀ t ∈ done, t.halted = true)
    (hnh : th.halted = false)
    (hpc : stmts[th.pc]? = some (.label lbl)) :
    runCTAWithGlobalLog (f + 1) stmts cta saved =
      runCTAWithGlobalLog f stmts
        { cta with threads := done ++ ({ th with pc := th.pc + 1 } :: todo) } saved := by
  have hstep := step_label stmts cta done th todo lbl hthreads hdone hnh hpc
  have hnc : cta.epochLog = [] ∨
      ({ cta with threads := done ++ ({ th with pc := th.pc + 1 } :: todo) } : PTXCTAState).epochLog ≠ [] := by
    cases h : cta.epochLog with
    | nil => exact Or.inl rfl
    | cons x xs => exact Or.inr (by simp)
  exact runCTAWithGlobalLog_step_no_clear f stmts cta _ saved hstep hnc

theorem runCTA_ret_step (f : Nat) (stmts : List PTXStmt) (cta : PTXCTAState)
    (done : List PTXThreadState) (th : PTXThreadState) (todo : List PTXThreadState)
    (saved : List MemAccessLog)
    (hthreads : cta.threads = done ++ (th :: todo))
    (hdone : ∀ t ∈ done, t.halted = true)
    (hnh : th.halted = false)
    (hpc : stmts[th.pc]? = some (.instr none .ret)) :
    runCTAWithGlobalLog (f + 1) stmts cta saved =
      runCTAWithGlobalLog f stmts
        { cta with threads := done ++ ({ th with pc := th.pc + 1, halted := true } :: todo) } saved := by
  have hstep := step_ret stmts cta done th todo hthreads hdone hnh hpc
  have hnc : cta.epochLog = [] ∨
      ({ cta with threads := done ++ ({ th with pc := th.pc + 1, halted := true } :: todo) } : PTXCTAState).epochLog ≠ [] := by
    cases h : cta.epochLog with
    | nil => exact Or.inl rfl
    | cons x xs => exact Or.inr (by simp)
  exact runCTAWithGlobalLog_step_no_clear f stmts cta _ saved hstep hnc


end LeanNative.Proofs.PTXSIMT
