import LeanNative.Proofs.PTXGrid3

namespace LeanNative.Proofs.PTXSIMT

open LeanNative.Backend.PTXAst

/-! ## 9. `stdLoadIn`, store epilogue, CTA thread loop, and 1D grid theorem -/

structure PTXLogOk (outBase len : Nat) (allowedLanes : Nat → Prop)
    (laneOf : Dim3 → Nat) (logs : List MemAccessLog) : Prop where
  run : SafePTXLog outBase len allowedLanes laneOf logs

structure GlobalLogOk (outBase len : Nat) (ctaPred : Nat → Prop)
    (logs : List MemAccessLog) : Prop where
  run : SafeGlobalLog outBase len ctaPred logs

/-- Execute the 4-instruction `stdLoadIn k s!"%rd{di}"` sequence, loading input element `(k, gid)`
    into `%rd{di}` and recording one read-only `.global` log entry in `[0, nIn * len * 8)`. -/
theorem run_stdLoadIn
    (f : Nat) (pre suf : List PTXStmt) (cta : PTXCTAState)
    (done todo : List PTXThreadState)
    {rf : PTXRegFile} {nP nR nRd : Nat} (hrt : RegTyped rf nP nR nRd)
    (localBytes tx k di gid nIn len : Nat) (word : BitVec 64)
    (allowedLanes : Nat → Prop) (laneOf : Dim3 → Nat)
    (hdi : di < nRd) (hr5 : 5 < nRd) (hne5 : 5 ≠ di) (hk : k < nIn) (hgid : gid < len)
    (houn : (nIn + 1) * len * 8 ≤ 2 ^ 64)
    (hdone : ∀ t ∈ done, t.halted = true) (saved : List MemAccessLog)
    (hlk5 : rf.regs.lookup "%rd5" = some (.scalar (BitVec.ofNat 64 (gid * 8))))
    (hparam : cta.paramMem.lookupParam? s!"param_in{k}" = some (BitVec.ofNat 64 (k * len * 8)))
    (hload : cta.globalMem.loadBits (k * len * 8 + gid * 8) 8 = some word)
    (hlog : SafePTXLog (nIn * len * 8) len allowedLanes laneOf cta.epochLog) :
    let entry : MemAccessLog := {
      tid := { x := tx, y := 0, z := 0 }
      space := .global
      addr := k * len * 8 + gid * 8
      width := 8
      isWrite := false
      isAtomic := false }
    runCTAWithGlobalLog (f + 4) (pre ++ stdLoadIn k s!"%rd{di}" ++ suf)
      { cta with threads := done ++ (laneAt localBytes tx pre.length rf false :: todo) } saved =
    runCTAWithGlobalLog f (pre ++ stdLoadIn k s!"%rd{di}" ++ suf)
      { cta with
        threads := done ++ (laneAt localBytes tx (pre.length + 4) (rfSet rf s!"%rd{di}" word) false :: todo)
        epochLog := entry :: cta.epochLog } saved ∧
    PTXLogOk (nIn * len * 8) len allowedLanes laneOf (entry :: cta.epochLog) := by
  intro entry
  let stmts := pre ++ stdLoadIn k s!"%rd{di}" ++ suf
  let s0 : PTXStmt := .instr none (.ldParam .u64 s!"%rd{di}" s!"param_in{k}")
  let s1 : PTXStmt := .instr none (.cvtaToGlobal .u64 s!"%rd{di}" (.reg s!"%rd{di}"))
  let s2 : PTXStmt := .instr none (.add .none .u64 s!"%rd{di}" (.reg s!"%rd{di}") (.reg "%rd5"))
  let s3 : PTXStmt := .instr none (.ldGlobal .u64 s!"%rd{di}" (.regOffset s!"%rd{di}" 0))
  have hinBound : (k * len * 8 + gid * 8) + 8 ≤ nIn * len * 8 := by
    have hg8 : gid * 8 + 8 ≤ len * 8 := by
      have : gid + 1 ≤ len := by omega
      simpa [Nat.right_distrib, Nat.one_mul] using Nat.mul_le_mul_right 8 this
    have hk8 : (k + 1) * len * 8 ≤ nIn * len * 8 :=
      Nat.mul_le_mul_right 8 (Nat.mul_le_mul_right len (by omega))
    have hk8' : k * len * 8 + len * 8 ≤ nIn * len * 8 := by
      simpa [Nat.add_mul, Nat.one_mul, Nat.right_distrib] using hk8
    omega
  have hout64 : nIn * len * 8 < 2 ^ 64 := by
    have : (nIn + 1) * len * 8 = nIn * len * 8 + len * 8 := by simp [Nat.add_mul, Nat.one_mul]
    have hpos : 0 < len * 8 := by omega
    omega
  have haddr64 : k * len * 8 + gid * 8 < 2 ^ 64 := by omega
  have hneStr : "%rd5" ≠ s!"%rd{di}" := fun h => hne5 (regName_inj "%rd" 5 di h)
  have hpc0 : stmts[pre.length]? = some s0 := by
    have hEq : stmts = pre ++ (s0 :: ([s1, s2, s3] ++ suf)) := by
      simp [stmts, stdLoadIn, s0, s1, s2, s3, List.append_assoc]
    rw [hEq]; exact stmt_at pre _ s0
  have hpc1 : stmts[pre.length + 1]? = some s1 := by
    have hEq : stmts = (pre ++ [s0]) ++ (s1 :: ([s2, s3] ++ suf)) := by
      simp [stmts, stdLoadIn, s0, s1, s2, s3, List.append_assoc]
    have hlen1 : (pre ++ [s0]).length = pre.length + 1 := by simp
    rw [hEq, ← hlen1]; exact stmt_at _ _ s1
  have hpc2 : stmts[pre.length + 2]? = some s2 := by
    have hEq : stmts = (pre ++ [s0, s1]) ++ (s2 :: ([s3] ++ suf)) := by
      simp [stmts, stdLoadIn, s0, s1, s2, s3, List.append_assoc]
    have hlen2 : (pre ++ [s0, s1]).length = pre.length + 2 := by simp
    rw [hEq, ← hlen2]; exact stmt_at _ _ s2
  have hpc3 : stmts[pre.length + 3]? = some s3 := by
    have hEq : stmts = (pre ++ [s0, s1, s2]) ++ (s3 :: suf) := by
      simp [stmts, stdLoadIn, s0, s1, s2, s3, List.append_assoc]
    have hlen3 : (pre ++ [s0, s1, s2]).length = pre.length + 3 := by simp
    rw [hEq, ← hlen3]; exact stmt_at _ _ s3
  let r1 := rfSet rf s!"%rd{di}" (BitVec.ofNat 64 (k * len * 8))
  let r3 := rfSet rf s!"%rd{di}" (BitVec.ofNat 64 (k * len * 8 + gid * 8))
  have hs0 : runCTAWithGlobalLog ((f + 3) + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx pre.length rf false :: todo) } saved =
    runCTAWithGlobalLog (f + 3) stmts
      { cta with threads := done ++ (laneAt localBytes tx (pre.length + 1) r1 false :: todo) } saved := by
    apply pure_lane_step (f + 3) stmts cta done todo localBytes tx
      pre.length rf r1 (.ldParam .u64 s!"%rd{di}" s!"param_in{k}") saved hdone hpc0
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    exact exec_ldParam_rd stmts
      { cta with threads := done ++ (laneAt localBytes tx pre.length rf false :: todo) }
      (laneAt localBytes tx pre.length rf false)
      hrt di hdi s!"param_in{k}" (BitVec.ofNat 64 (k * len * 8)) hparam
  have hs1 : runCTAWithGlobalLog ((f + 2) + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx (pre.length + 1) r1 false :: todo) } saved =
    runCTAWithGlobalLog (f + 2) stmts
      { cta with threads := done ++ (laneAt localBytes tx (pre.length + 2) r1 false :: todo) } saved := by
    have hs1' : runCTAWithGlobalLog ((f + 2) + 1) stmts
        { cta with threads := done ++ (laneAt localBytes tx (pre.length + 1) r1 false :: todo) } saved =
      runCTAWithGlobalLog (f + 2) stmts
        { cta with threads := done ++
          (laneAt localBytes tx (pre.length + 2) (rfSet r1 s!"%rd{di}" (BitVec.ofNat 64 (k * len * 8))) false :: todo) }
        saved := by
      apply pure_lane_step (f + 2) stmts cta done todo localBytes tx
        (pre.length + 1) r1 (rfSet r1 s!"%rd{di}" (BitVec.ofNat 64 (k * len * 8)))
        (.cvtaToGlobal .u64 s!"%rd{di}" (.reg s!"%rd{di}")) saved hdone hpc1
        (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
      exact exec_cvta_rd stmts
        { cta with threads := done ++ (laneAt localBytes tx (pre.length + 1) r1 false :: todo) }
        (laneAt localBytes tx (pre.length + 1) r1 false)
        hrt di di hdi hdi (BitVec.ofNat 64 (k * len * 8)) (lookup_rfSet_self rf s!"%rd{di}" _)
    rw [hs1', rfSet_overwrite rf s!"%rd{di}" _ _]
  have hs2 : runCTAWithGlobalLog ((f + 1) + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx (pre.length + 2) r1 false :: todo) } saved =
    runCTAWithGlobalLog (f + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx (pre.length + 3) r3 false :: todo) } saved := by
    have hs2' : runCTAWithGlobalLog ((f + 1) + 1) stmts
        { cta with threads := done ++ (laneAt localBytes tx (pre.length + 2) r1 false :: todo) } saved =
      runCTAWithGlobalLog (f + 1) stmts
        { cta with threads := done ++
          (laneAt localBytes tx (pre.length + 3)
            (rfSet r1 s!"%rd{di}" (BitVec.ofNat 64 (k * len * 8 + gid * 8))) false :: todo) }
        saved := by
      apply pure_lane_step (f + 1) stmts cta done todo localBytes tx
        (pre.length + 2) r1 (rfSet r1 s!"%rd{di}" (BitVec.ofNat 64 (k * len * 8 + gid * 8)))
        (.add .none .u64 s!"%rd{di}" (.reg s!"%rd{di}") (.reg "%rd5")) saved hdone hpc2
        (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
      have hlk5' : r1.regs.lookup "%rd5" = some (.scalar (BitVec.ofNat 64 (gid * 8))) := by
        dsimp only [r1]; rw [lookup_rfSet_ne rf s!"%rd{di}" "%rd5" _ hneStr, hlk5]
      have hex := exec_add_rd stmts
        { cta with threads := done ++ (laneAt localBytes tx (pre.length + 2) r1 false :: todo) }
        (laneAt localBytes tx (pre.length + 2) r1 false)
        hrt di di 5 hdi hdi hr5
        (BitVec.ofNat 64 (k * len * 8)) (BitVec.ofNat 64 (gid * 8))
        (lookup_rfSet_self rf s!"%rd{di}" _) hlk5'
      rw [add_ofNat64 (k * len * 8) (gid * 8) haddr64] at hex; exact hex
    rw [hs2', rfSet_overwrite rf s!"%rd{di}" _ _]
  have hex3 := exec_ldGlobal_rd stmts
    { cta with threads := done ++ (laneAt localBytes tx (pre.length + 3) r3 false :: todo) }
    (laneAt localBytes tx (pre.length + 3) r3 false) hrt (nIn * len * 8) len allowedLanes laneOf
    di di hdi hdi (k * len * 8 + gid * 8) word (lookup_rfSet_self rf s!"%rd{di}" _)
    haddr64 (by omega) hload hlog hinBound
  have hov3 : r3.setScalarRaw s!"%rd{di}" word = rfSet rf s!"%rd{di}" word :=
    rfSet_overwrite rf s!"%rd{di}" _ _
  have hth3 : thStep (laneAt localBytes tx (pre.length + 3) r3 false)
      ((laneAt localBytes tx (pre.length + 3) r3 false).regs.setScalarRaw s!"%rd{di}" word) =
      laneAt localBytes tx (pre.length + 4) (rfSet rf s!"%rd{di}" word) false := by
    dsimp only [thStep, laneAt]
    have hp4 : pre.length + 3 + 1 = pre.length + 4 := by omega
    rw [hov3, hp4]
  rw [hth3] at hex3
  have hs3 := runCTA_mem_instr f stmts
    { cta with threads := done ++ (laneAt localBytes tx (pre.length + 3) r3 false :: todo) }
    done (laneAt localBytes tx (pre.length + 3) r3 false) todo
    (.ldGlobal .u64 s!"%rd{di}" (.regOffset s!"%rd{di}" 0))
    (laneAt localBytes tx (pre.length + 4) (rfSet rf s!"%rd{di}" word) false)
    cta.globalMem entry saved rfl hdone rfl hpc3
    (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) hex3
  refine ⟨?_, ?_⟩
  · have hf4 : f + 4 = (f + 3) + 1 := by omega
    have hf3 : f + 3 = (f + 2) + 1 := by omega
    have hf2 : f + 2 = (f + 1) + 1 := by omega
    change runCTAWithGlobalLog (f + 4) stmts _ saved = runCTAWithGlobalLog f stmts _ saved
    rw [hf4, hs0, hf3, hs1, hf2, hs2, hs3]
  · refine ⟨fun e he => ?_⟩
    rcases List.mem_cons.mp he with rfl | hrest
    · exact ⟨rfl, rfl, rfl, Or.inl ⟨rfl, hinBound⟩⟩
    · exact hlog e hrest

/-- Execute the 3-statement epilogue `[st.global.u64 [%rd6], %rd{vi}, .label doneLbl, ret]`
    for an in-bounds lane, storing `val` at `nIn * len * 8 + gid * 8` and halting the lane. -/
theorem run_store_done_ret
    (f : Nat) (pre : List PTXStmt) (doneLbl : String) (cta : PTXCTAState)
    (done todo : List PTXThreadState)
    {rf : PTXRegFile} {nP nR nRd : Nat} (hrt : RegTyped rf nP nR nRd)
    (localBytes tx vi gid nIn len : Nat) (val : BitVec 64) (gmem' : ByteMemory)
    (allowedLanes : Nat → Prop) (laneOf : Dim3 → Nat)
    (hvi : vi < nRd) (hr6 : 6 < nRd) (hgid : gid < len)
    (houn : (nIn + 1) * len * 8 ≤ 2 ^ 64)
    (hlane : laneOf { x := tx, y := 0, z := 0 } = gid)
    (hnotAllow : ¬ allowedLanes gid)
    (hdone : ∀ t ∈ done, t.halted = true) (saved : List MemAccessLog)
    (hlk6 : rf.regs.lookup "%rd6" = some (.scalar (BitVec.ofNat 64 (nIn * len * 8 + gid * 8))))
    (hlkV : rf.regs.lookup s!"%rd{vi}" = some (.scalar val))
    (hstore : cta.globalMem.storeBits (nIn * len * 8 + gid * 8) 8 val = some gmem')
    (hlog : SafePTXLog (nIn * len * 8) len allowedLanes laneOf cta.epochLog) :
    let epilogue : List PTXStmt :=
      [.instr none (.stGlobal .u64 (.regOffset "%rd6" 0) (.reg s!"%rd{vi}")),
       .label doneLbl,
       .instr none .ret]
    let wentry : MemAccessLog := {
      tid := { x := tx, y := 0, z := 0 }
      space := .global
      addr := nIn * len * 8 + gid * 8
      width := 8
      isWrite := true
      isAtomic := false }
    runCTAWithGlobalLog (f + 3) (pre ++ epilogue)
      { cta with threads := done ++ (laneAt localBytes tx pre.length rf false :: todo) } saved =
    runCTAWithGlobalLog f (pre ++ epilogue)
      { cta with
        threads := done ++ (laneAt localBytes tx (pre.length + 3) rf true :: todo)
        globalMem := gmem'
        epochLog := wentry :: cta.epochLog } saved ∧
    PTXLogOk (nIn * len * 8) len (fun cx => allowedLanes cx ∨ cx = gid)
      laneOf (wentry :: cta.epochLog) := by
  intro epilogue wentry
  let s0 : PTXStmt := .instr none (.stGlobal .u64 (.regOffset "%rd6" 0) (.reg s!"%rd{vi}"))
  let s1 : PTXStmt := .label doneLbl
  let s2 : PTXStmt := .instr none .ret
  have haddr64 : nIn * len * 8 + gid * 8 < 2 ^ 64 := by
    have hg8 : gid * 8 < len * 8 := Nat.mul_lt_mul_of_pos_right hgid (by omega)
    have : (nIn + 1) * len * 8 = nIn * len * 8 + len * 8 := by simp [Nat.add_mul, Nat.one_mul]
    omega
  have hpc0 : (pre ++ epilogue)[pre.length]? = some s0 := stmt_at pre _ s0
  have hpc1 : (pre ++ epilogue)[pre.length + 1]? = some s1 := by
    have hEq : pre ++ epilogue = (pre ++ [s0]) ++ (s1 :: [s2]) := by
      simp [epilogue, s0, s1, s2, List.append_assoc]
    have hlen1 : (pre ++ [s0]).length = pre.length + 1 := by simp
    rw [hEq, ← hlen1]; exact stmt_at _ _ s1
  have hpc2 : (pre ++ epilogue)[pre.length + 2]? = some s2 := by
    have hEq : pre ++ epilogue = (pre ++ [s0, s1]) ++ [s2] := by
      simp [epilogue, s0, s1, s2, List.append_assoc]
    have hlen2 : (pre ++ [s0, s1]).length = pre.length + 2 := by simp
    rw [hEq, ← hlen2]; exact stmt_at _ _ s2
  have hlk6' : rf.regs.lookup s!"%rd{6}" = some (.scalar (BitVec.ofNat 64 (nIn * len * 8 + gid * 8))) :=
    hlk6
  have hex0 := exec_stGlobal_rd (pre ++ epilogue)
    { cta with threads := done ++ (laneAt localBytes tx pre.length rf false :: todo) }
    (laneAt localBytes tx pre.length rf false) hrt (nIn * len * 8) len allowedLanes laneOf
    vi 6 hvi hr6 (nIn * len * 8 + gid * 8) val gmem'
    hlk6' hlkV haddr64 (by omega) hstore hlog ⟨gid, hgid, hnotAllow, rfl⟩
  have hs0 := runCTA_mem_instr (f + 2) (pre ++ epilogue)
    { cta with threads := done ++ (laneAt localBytes tx pre.length rf false :: todo) }
    done (laneAt localBytes tx pre.length rf false) todo
    (.stGlobal .u64 (.regOffset "%rd6" 0) (.reg s!"%rd{vi}"))
    (laneAt localBytes tx (pre.length + 1) rf false)
    gmem' wentry saved rfl hdone rfl hpc0
    (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h) hex0
  have hs1 := runCTA_label_step (f + 1) (pre ++ epilogue)
    { cta with
      threads := done ++ (laneAt localBytes tx (pre.length + 1) rf false :: todo)
      globalMem := gmem'
      epochLog := wentry :: cta.epochLog }
    done (laneAt localBytes tx (pre.length + 1) rf false) todo doneLbl saved
    rfl hdone rfl hpc1
  have hs2 := runCTA_ret_step f (pre ++ epilogue)
    { cta with
      threads := done ++ (laneAt localBytes tx (pre.length + 2) rf false :: todo)
      globalMem := gmem'
      epochLog := wentry :: cta.epochLog }
    done (laneAt localBytes tx (pre.length + 2) rf false) todo saved
    rfl hdone rfl hpc2
  refine ⟨?_, ?_⟩
  · have hf3 : f + 3 = (f + 2) + 1 := by omega
    have hf2 : f + 2 = (f + 1) + 1 := by omega
    have hp2 : pre.length + 1 + 1 = pre.length + 2 := by omega
    have hp3 : pre.length + 2 + 1 = pre.length + 3 := by omega
    rw [hf3, hs0, hf2, hs1]
    dsimp only [laneAt] at hs2 ⊢
    simp only [hp2, hp3] at hs2 ⊢
    exact hs2
  · refine ⟨fun e he => ?_⟩
    rcases List.mem_cons.mp he with rfl | hrest
    · exact ⟨rfl, rfl, rfl, Or.inr ⟨rfl, gid, hgid, Or.inr rfl, hlane, rfl⟩⟩
    · rcases hlog e hrest with ⟨hsp, hat, hw, hkind⟩
      refine ⟨hsp, hat, hw, ?_⟩
      rcases hkind with hl | ⟨hwr, cx, hcx, hal, hln, hadr⟩
      · exact Or.inl hl
      · exact Or.inr ⟨hwr, cx, hcx, Or.inl hal, hln, hadr⟩

/-- Global memory invariant tracking preserved input buffers and written output lanes. -/
def MemState (nIn len : Nat) (inWords : Nat → List (BitVec 64))
    (hlen : ∀ j < nIn, (inWords j).length = len)
    (outFn : Nat → BitVec 64) (written : Nat → Prop) (g : ByteMemory) : Prop :=
  g.bytes.size = (nIn + 1) * len * 8 ∧
  (∀ (j : Nat) (hj : j < nIn) (i : Nat) (hi : i < len),
    g.loadBits (j * len * 8 + i * 8) 8 =
      some ((inWords j)[i]'(by rw [hlen j hj]; exact hi))) ∧
  (∀ i < len, written i → g.loadBits (nIn * len * 8 + i * 8) 8 = some (outFn i))

theorem MemState_init (nIn len : Nat) (inWords : Nat → List (BitVec 64))
    (hlen : ∀ j < nIn, (inWords j).length = len) (outFn : Nat → BitVec 64) :
    MemState nIn len inWords hlen outFn (fun i => i < 0) (packGlobalBuffers nIn len inWords) := by
  refine ⟨packGlobalBuffers_size nIn len inWords hlen, ?_, ?_⟩
  · intro j hj i hi
    exact packGlobalBuffers_load_in nIn len inWords hlen j i hj hi
  · intro i _ hw; omega

theorem MemState_store_out (nIn len : Nat) (inWords : Nat → List (BitVec 64))
    (hlen : ∀ j < nIn, (inWords j).length = len) (outFn : Nat → BitVec 64)
    (gid : Nat) (hgid : gid < len) (g : ByteMemory)
    (hm : MemState nIn len inWords hlen outFn (fun i => i < gid) g) :
    ∃ g', g.storeBits (nIn * len * 8 + gid * 8) 8 (outFn gid) = some g' ∧
      MemState nIn len inWords hlen outFn (fun i => i < gid + 1) g' := by
  rcases hm with ⟨hsz, hin, hout⟩
  have hbound : nIn * len * 8 + gid * 8 + 8 ≤ g.bytes.size := by
    rw [hsz]; exact (outAddr_in_range nIn len gid hgid).1
  rcases storeBits_eq_some_and_size g (nIn * len * 8 + gid * 8) (outFn gid) hbound with
    ⟨g', hst, hsz', hread, hdisj⟩
  refine ⟨g', hst, by rw [hsz', hsz], ?_, ?_⟩
  · intro j hj k hk
    have hk8 : k * 8 + 8 ≤ len * 8 := by
      have : k + 1 ≤ len := by omega
      simpa [Nat.right_distrib, Nat.one_mul] using Nat.mul_le_mul_right 8 this
    have hjl8 : j * len * 8 + len * 8 ≤ nIn * len * 8 := by
      have h1 : (j + 1) * len * 8 ≤ nIn * len * 8 :=
        Nat.mul_le_mul_right 8 (Nat.mul_le_mul_right len (by omega))
      simpa [Nat.add_mul, Nat.one_mul, Nat.right_distrib] using h1
    rw [hdisj (j * len * 8 + k * 8) (Or.inl (by omega))]
    exact hin j hj k hk
  · intro i hi hw
    by_cases heq : i = gid
    · subst heq; exact hread
    · have hlt : i < gid := by omega
      rw [hdisj (nIn * len * 8 + i * 8) (Or.inl (by omega))]
      exact hout i hi hlt

theorem MemState_oob_step (nIn len : Nat) (inWords : Nat → List (BitVec 64))
    (hlen : ∀ j < nIn, (inWords j).length = len) (outFn : Nat → BitVec 64)
    (gid : Nat) (hoob : ¬ gid < len) (g : ByteMemory)
    (hm : MemState nIn len inWords hlen outFn (fun i => i < gid) g) :
    MemState nIn len inWords hlen outFn (fun i => i < gid + 1) g := by
  rcases hm with ⟨hsz, hin, hout⟩
  refine ⟨hsz, hin, ?_⟩
  intro i hi _
  exact hout i hi (by omega)

theorem SafePTXLog_mono {outBase len : Nat} {p1 p2 : Nat → Prop} {laneOf : Dim3 → Nat}
    {logs : List MemAccessLog} (himp : ∀ cx, p1 cx → p2 cx)
    (h : SafePTXLog outBase len p1 laneOf logs) :
    PTXLogOk outBase len p2 laneOf logs := by
  refine ⟨fun e he => ?_⟩
  rcases h e he with ⟨hsp, hat, hw, hkind⟩
  refine ⟨hsp, hat, hw, ?_⟩
  rcases hkind with hl | ⟨hwr, cx, hcx, hp, hln, hadr⟩
  · exact Or.inl hl
  · exact Or.inr ⟨hwr, cx, hcx, himp cx hp, hln, hadr⟩

theorem SafePTXLog_filter_global {outBase len : Nat} {p : Nat → Prop} {laneOf : Dim3 → Nat}
    {logs : List MemAccessLog} (h : SafePTXLog outBase len p laneOf logs) :
    GlobalLogOk outBase len p (logs.filter (fun e => e.space == .global)) := by
  refine ⟨fun e he => ?_⟩
  rcases h e (List.mem_filter.mp he).1 with ⟨hsp, hat, hw, hkind⟩
  refine ⟨hsp, hat, hw, ?_⟩
  rcases hkind with hl | ⟨hwr, cx, hcx, hp, _, hadr⟩
  · exact Or.inl hl
  · exact Or.inr ⟨hwr, cx, hcx, hp, hadr⟩

/-- Per-lane execution contract for the middle statement block `mid` of a 1D kernel. -/
def MidBodySpec (nP nR nRd nIn len vi maxMidSteps : Nat)
    (doneLbl : String) (mid : List PTXStmt)
    (inWords : Nat → List (BitVec 64)) (hlen : ∀ j < nIn, (inWords j).length = len)
    (outFn : Nat → BitVec 64) : Prop :=
  let epilogue : List PTXStmt :=
    [.instr none (.stGlobal .u64 (.regOffset "%rd6" 0) (.reg s!"%rd{vi}")),
     .label doneLbl, .instr none .ret]
  let stmts := stdGidSetup doneLbl ++ mid ++ epilogue
  ∀ (blockSize : Nat) (ctaId : Dim3) (tx : Nat) (cta : PTXCTAState)
    (done todo : List PTXThreadState) (saved : List MemAccessLog)
    (allowedLanes : Nat → Prop),
    let gid := ctaId.x * blockSize + tx
    cta.ctaId = ctaId →
    cta.blockDim = { x := blockSize, y := 1, z := 1 } →
    cta.paramMem = stdParamMem nIn len →
    tx < blockSize →
    ctaId.x < 2 ^ 32 →
    blockSize < 2 ^ 32 →
    gid < len →
    (∀ t ∈ done, t.halted = true) →
    (∀ (j : Nat) (hj : j < nIn) (i : Nat) (hi : i < len),
      cta.globalMem.loadBits (j * len * 8 + i * 8) 8 =
        some ((inWords j)[i]'(by rw [hlen j hj]; exact hi))) →
    SafePTXLog (nIn * len * 8) len allowedLanes (laneOf1D blockSize ctaId) cta.epochLog →
    ∃ stepsMid ≤ maxMidSteps, ∃ rfMid logMid,
      RegTyped rfMid nP nR nRd ∧
      rfMid.regs.lookup "%rd6" = some (.scalar (BitVec.ofNat 64 (nIn * len * 8 + gid * 8))) ∧
      rfMid.regs.lookup s!"%rd{vi}" = some (.scalar (outFn gid)) ∧
      SafePTXLog (nIn * len * 8) len allowedLanes (laneOf1D blockSize ctaId) logMid ∧
      ∀ f,
        runCTAWithGlobalLog (f + stepsMid) stmts
          { cta with threads := done ++
            (gidLane blockSize ctaId (PTXRegFile.ofRegDecls (stdKernelRegs nP nR nRd))
              0 tx gid nIn len :: todo) } saved =
        runCTAWithGlobalLog f stmts
          { cta with
            threads := done ++ (laneAt 0 tx (13 + mid.length) rfMid false :: todo)
            epochLog := logMid } saved

/-- Run one CTA's remaining thread suffix `(List.range blockSize).drop t0` to completion. -/
private theorem runCTA_threads_1d
    (nP nR nRd nIn len vi maxMidSteps blockSize : Nat) (ctaId : Dim3)
    (doneLbl : String) (mid : List PTXStmt)
    (inWords : Nat → List (BitVec 64)) (hlen : ∀ j < nIn, (inWords j).length = len)
    (outFn : Nat → BitVec 64)
    (hp : 0 < nP) (hr : 2 < nR) (hr6 : 6 < nRd) (hvi : vi < nRd)
    (houn : (nIn + 1) * len * 8 ≤ 2 ^ 64)
    (hctaX : ctaId.x < 2 ^ 32) (hblkX : blockSize < 2 ^ 32)
    (hnoLbl : ∀ s ∈ mid, s ≠ .label doneLbl)
    (hMid : MidBodySpec nP nR nRd nIn len vi maxMidSteps doneLbl mid inWords hlen outFn) :
    let epilogue : List PTXStmt :=
      [.instr none (.stGlobal .u64 (.regOffset "%rd6" 0) (.reg s!"%rd{vi}")),
       .label doneLbl, .instr none .ret]
    let stmts := stdGidSetup doneLbl ++ mid ++ epilogue
    let initRf := PTXRegFile.ofRegDecls (stdKernelRegs nP nR nRd)
    ∀ (rem : Nat), rem ≤ blockSize →
      ∀ (fuel : Nat) (cta : PTXCTAState) (done : List PTXThreadState),
        let t0 := blockSize - rem
        cta.ctaId = ctaId →
        cta.blockDim = { x := blockSize, y := 1, z := 1 } →
        cta.paramMem = stdParamMem nIn len →
        cta.threads = done ++ ((List.range rem).map fun d => laneAt 0 (t0 + d) 0 initRf false) →
        (∀ t ∈ done, t.halted = true) →
        MemState nIn len inWords hlen outFn (fun i => i < ctaId.x * blockSize + t0) cta.globalMem →
        SafePTXLog (nIn * len * 8) len
          (fun cx => ctaId.x * blockSize ≤ cx ∧ cx < ctaId.x * blockSize + t0)
          (laneOf1D blockSize ctaId) cta.epochLog →
        rem * (16 + maxMidSteps) + 1 ≤ fuel →
        ∃ ctaFinal ctaLog,
          runCTAWithGlobalLog fuel stmts cta [] = .ok (ctaFinal, ctaLog) ∧
          MemState nIn len inWords hlen outFn
            (fun i => i < ctaId.x * blockSize + blockSize) ctaFinal.globalMem ∧
          GlobalLogOk (nIn * len * 8) len
            (fun cx => ctaId.x * blockSize ≤ cx ∧ cx < ctaId.x * blockSize + blockSize) ctaLog := by
  intro epilogue stmts initRf
  have hrt0 : RegTyped initRf nP nR nRd := initRegs_typed nP nR nRd hp (by omega) (by omega)
  have hlen64 : len < 2 ^ 64 := by
    have : (nIn + 1) * len * 8 = nIn * len * 8 + len * 8 := by simp [Nat.add_mul, Nat.one_mul]
    omega
  let storeStmt : PTXStmt := .instr none (.stGlobal .u64 (.regOffset "%rd6" 0) (.reg s!"%rd{vi}"))
  have hmidNoLbl : ∀ s ∈ mid ++ [storeStmt], s ≠ .label doneLbl := by
    intro s hs; rcases List.mem_append.mp hs with h1 | h2
    · exact hnoLbl s h1
    · rw [List.mem_singleton.mp h2]; simp [storeStmt]
  have hstmtsSplit : stmts = stdGidSetup doneLbl ++ (mid ++ [storeStmt]) ++
      [.label doneLbl, .instr none .ret] := by
    simp [stmts, epilogue, storeStmt, List.append_assoc]
  intro rem
  induction rem with
  | zero =>
    intro _ fuel cta done t0 _ _ _ hthreads hdone hmem hlog hfuel
    have ht0 : t0 = blockSize := by omega
    simp only [List.range_zero, List.map_nil, List.append_nil] at hthreads
    have hall : cta.threads.all (·.halted) = true := by
      rw [hthreads, List.all_eq_true]; exact hdone
    have hf1 : fuel = (fuel - 1) + 1 := by omega
    rw [hf1, runCTAWithGlobalLog_done_halted (fuel - 1) stmts cta [] hall, List.append_nil]
    rw [ht0] at hmem hlog
    exact ⟨cta, _, rfl, hmem, SafePTXLog_filter_global hlog⟩
  | succ r ih =>
    intro hrem fuel cta done t0 hcta hblk hpm hthreads hdone hmem hlog hfuel
    have hfuelStep : (r + 1) * (16 + maxMidSteps) = r * (16 + maxMidSteps) + (16 + maxMidSteps) := by
      simp [Nat.add_mul, Nat.one_mul]
    have ht0Lt : t0 < blockSize := by dsimp only [t0]; omega
    have htx32 : t0 < 2 ^ 32 := by omega
    have hrange : (List.range (r + 1)).map (fun d => laneAt 0 (t0 + d) 0 initRf false) =
        laneAt 0 t0 0 initRf false ::
          (List.range r).map (fun d => laneAt 0 ((blockSize - r) + d) 0 initRf false) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.add_zero]
      congr 1; apply List.map_congr_left; intro d _
      dsimp only [Function.comp_apply, t0]
      have hd : blockSize - (r + 1) + (d + 1) = blockSize - r + d := by omega
      rw [hd]
    let todo := (List.range r).map (fun d => laneAt 0 ((blockSize - r) + d) 0 initRf false)
    have hctaEq : cta = { cta with threads := done ++ (laneAt 0 t0 0 initRf false :: todo) } := by
      cases cta; dsimp only at hthreads
      subst hthreads; rw [hrange]
    have hnP : cta.paramMem.lookupParam? "param_n" = some (BitVec.ofNat 64 len) := by
      rw [hpm]; exact stdParamMem_lookup_n nIn len
    have houtP : cta.paramMem.lookupParam? "param_out" = some (BitVec.ofNat 64 (nIn * len * 8)) := by
      rw [hpm]; exact stdParamMem_lookup_out nIn len
    let gid := ctaId.x * blockSize + t0
    have hnextGid : ctaId.x * blockSize + (blockSize - r) = gid + 1 := by dsimp only [gid, t0]; omega
    by_cases hgidLt : gid < len
    · obtain ⟨stepsMid, hstepsLe, rfMid, logMid, hrtMid, hlk6, hlkV, hlogMid, hrunMid⟩ :=
        hMid blockSize ctaId t0 cta done todo []
          (fun cx => ctaId.x * blockSize ≤ cx ∧ cx < gid)
          hcta hblk hpm ht0Lt hctaX hblkX hgidLt hdone hmem.2.1 hlog
      obtain ⟨g', hstore, hmem'⟩ :=
        MemState_store_out nIn len inWords hlen outFn gid hgidLt cta.globalMem hmem
      let fAfter := fuel - (13 + stepsMid + 3)
      have hfEq : fuel = ((fAfter + 3) + stepsMid) + 13 := by omega
      have h13 := run_gid_inbounds ((fAfter + 3) + stepsMid) doneLbl (mid ++ [storeStmt])
        cta done todo blockSize ctaId hrt0 0 t0 len nIn hp hr hr6 hcta hblk
        htx32 hctaX hblkX hgidLt houn hmidNoLbl hdone [] hnP houtP
      rw [← hstmtsSplit] at h13
      have hmidStep := hrunMid (fAfter + 3)
      have hpreLen : (stdGidSetup doneLbl ++ mid).length = 13 + mid.length := by
        simp [stdGidSetup]; omega
      have hstmtsEp : stmts = (stdGidSetup doneLbl ++ mid) ++ epilogue := rfl
      have hnotAllow : ¬ (ctaId.x * blockSize ≤ gid ∧ gid < gid) := by omega
      have hlaneEq : laneOf1D blockSize ctaId { x := t0, y := 0, z := 0 } = gid := rfl
      have hstStep := run_store_done_ret fAfter (stdGidSetup doneLbl ++ mid) doneLbl
        { cta with epochLog := logMid } done todo hrtMid 0 t0 vi gid nIn len
        (outFn gid) g' (fun cx => ctaId.x * blockSize ≤ cx ∧ cx < gid) (laneOf1D blockSize ctaId)
        hvi hr6 hgidLt houn hlaneEq hnotAllow hdone [] hlk6 hlkV hstore hlogMid
      rcases hstStep with ⟨hrunSt, ⟨hlogSt⟩⟩
      rw [hpreLen] at hrunSt
      let haltedTh := laneAt 0 t0 (13 + mid.length + 3) rfMid true
      let wentry : MemAccessLog := {
        tid := { x := t0, y := 0, z := 0 }, space := .global,
        addr := nIn * len * 8 + gid * 8, width := 8, isWrite := true, isAtomic := false }
      let ctaNext : PTXCTAState := { cta with
        threads := (done ++ [haltedTh]) ++ todo
        globalMem := g'
        epochLog := wentry :: logMid }
      have hchain : runCTAWithGlobalLog fuel stmts cta [] =
          runCTAWithGlobalLog fAfter stmts ctaNext [] := by
        conv => lhs; rw [hctaEq, hfEq]
        rw [h13, hmidStep]
        have h1 : runCTAWithGlobalLog (fAfter + 3) stmts
            { cta with
              threads := done ++ (laneAt 0 t0 (13 + mid.length) rfMid false :: todo)
              epochLog := logMid } [] =
          runCTAWithGlobalLog fAfter stmts
            { cta with
              threads := done ++ (haltedTh :: todo)
              globalMem := g'
              epochLog := wentry :: logMid } [] := hrunSt
        rw [h1]
        simp [ctaNext, List.append_assoc]
      have hdoneNext : ∀ t ∈ done ++ [haltedTh], t.halted = true := by
        intro t ht; rcases List.mem_append.mp ht with hd | hs
        · exact hdone t hd
        · rw [List.mem_singleton.mp hs]; rfl
      have hlogNext : SafePTXLog (nIn * len * 8) len
          (fun cx => ctaId.x * blockSize ≤ cx ∧ cx < ctaId.x * blockSize + (blockSize - r))
          (laneOf1D blockSize ctaId) ctaNext.epochLog :=
        (SafePTXLog_mono (fun _ hcx => by omega) hlogSt).run
      have hmemNext : MemState nIn len inWords hlen outFn
          (fun i => i < ctaId.x * blockSize + (blockSize - r)) ctaNext.globalMem := by
        rw [hnextGid]; exact hmem'
      rw [hchain]
      exact ih (by omega) fAfter ctaNext (done ++ [haltedTh])
        hcta hblk hpm rfl hdoneNext hmemNext hlogNext (by omega)
    · let fAfter := fuel - 10
      have hfEq : fuel = fAfter + 10 := by omega
      have h10 := run_gid_oob fAfter doneLbl (mid ++ [storeStmt])
        cta done todo blockSize ctaId hrt0 0 t0 len hp hr (by omega) hcta hblk
        htx32 hctaX hblkX hlen64 hgidLt hmidNoLbl hdone [] hnP
      rw [← hstmtsSplit] at h10
      let haltedTh := doneLane blockSize ctaId initRf 0 t0 len (13 + (mid ++ [storeStmt]).length + 1)
      let ctaNext : PTXCTAState := { cta with threads := (done ++ [haltedTh]) ++ todo }
      have hchain : runCTAWithGlobalLog fuel stmts cta [] =
          runCTAWithGlobalLog fAfter stmts ctaNext [] := by
        conv => lhs; rw [hctaEq, hfEq]
        rw [h10]
        simp [ctaNext, haltedTh, List.append_assoc]
      have hdoneNext : ∀ t ∈ done ++ [haltedTh], t.halted = true := by
        intro t ht; rcases List.mem_append.mp ht with hd | hs
        · exact hdone t hd
        · rw [List.mem_singleton.mp hs]; rfl
      have hmemNext : MemState nIn len inWords hlen outFn
          (fun i => i < ctaId.x * blockSize + (blockSize - r)) ctaNext.globalMem := by
        rw [hnextGid]
        exact MemState_oob_step nIn len inWords hlen outFn gid hgidLt cta.globalMem hmem
      have hlogNext : SafePTXLog (nIn * len * 8) len
          (fun cx => ctaId.x * blockSize ≤ cx ∧ cx < ctaId.x * blockSize + (blockSize - r))
          (laneOf1D blockSize ctaId) ctaNext.epochLog :=
        (SafePTXLog_mono (fun _ hcx => by omega) hlog).run
      rw [hchain]
      exact ih (by omega) fAfter ctaNext (done ++ [haltedTh])
        hcta hblk hpm rfl hdoneNext hmemNext hlogNext (by omega)

/-- Soundness of launching a standard 1D guarded PTX kernel across `nBlocks` CTAs of `blockSize`
    threads on `evalPTXKernel`, proving absence of intra-CTA and cross-CTA data races and exact
    elementwise agreement on all `len` output 64-bit words. -/
theorem evalPTXKernel_guarded_1d
    (nP nR nRd nIn len nBlocks blockSize vi maxMidSteps fuelPerCTA : Nat)
    (k : PTXKernel) (doneLbl : String) (mid : List PTXStmt)
    (inWords : Nat → List (BitVec 64)) (hlen : ∀ j < nIn, (inWords j).length = len)
    (outFn : Nat → BitVec 64)
    (hregs : k.regDecls = stdKernelRegs nP nR nRd)
    (hlocal : k.localBytes = 0)
    (hbody : k.body = stdGidSetup doneLbl ++ mid ++
      [.instr none (.stGlobal .u64 (.regOffset "%rd6" 0) (.reg s!"%rd{vi}")),
       .label doneLbl, .instr none .ret])
    (hp : 0 < nP) (hr : 2 < nR) (hr6 : 6 < nRd) (hvi : vi < nRd)
    (houn : (nIn + 1) * len * 8 ≤ 2 ^ 64)
    (hlenCov : len ≤ nBlocks * blockSize)
    (hnBlk32 : nBlocks < 2 ^ 32) (hblk32 : blockSize < 2 ^ 32)
    (hfuel : blockSize * (16 + maxMidSteps) + 1 ≤ fuelPerCTA)
    (hnoLbl : ∀ s ∈ mid, s ≠ .label doneLbl)
    (hMid : MidBodySpec nP nR nRd nIn len vi maxMidSteps doneLbl mid inWords hlen outFn) :
    ∃ gFinal,
      evalPTXKernel fuelPerCTA k
        { x := nBlocks, y := 1, z := 1 } { x := blockSize, y := 1, z := 1 }
        (packGlobalBuffers nIn len inWords) (stdParamMem nIn len) = .ok gFinal ∧
      (∀ i < len, gFinal.loadBits (nIn * len * 8 + i * 8) 8 = some (outFn i)) := by
  let gridDim : Dim3 := { x := nBlocks, y := 1, z := 1 }
  let blockDim : Dim3 := { x := blockSize, y := 1, z := 1 }
  let pMem := stdParamMem nIn len
  let cMem := ByteMemory.zeros 0
  have hloop : ∀ (rem : Nat), rem ≤ nBlocks →
      ∀ (gMem : ByteMemory) (priorLog : List MemAccessLog),
        let b0 := nBlocks - rem
        MemState nIn len inWords hlen outFn (fun i => i < b0 * blockSize) gMem →
        SafeGlobalLog (nIn * len * 8) len (fun cx => cx < b0 * blockSize) priorLog →
        ∃ gFinal,
          evalPTXKernelLoop fuelPerCTA k gridDim blockDim pMem cMem gMem priorLog
            ((List.range rem).map fun d => { x := b0 + d, y := 0, z := 0 }) = .ok gFinal ∧
          MemState nIn len inWords hlen outFn (fun i => i < nBlocks * blockSize) gFinal := by
    intro rem
    induction rem with
    | zero =>
      intro _ gMem priorLog b0 hmem _
      have hb0 : b0 = nBlocks := by omega
      rw [hb0] at hmem
      exact ⟨gMem, rfl, hmem⟩
    | succ r ih =>
      intro hrem gMem priorLog b0 hmem hprior
      have hb032 : b0 < 2 ^ 32 := by omega
      have hrange : (List.range (r + 1)).map (fun d => ({ x := b0 + d, y := 0, z := 0 } : Dim3)) =
          { x := b0, y := 0, z := 0 } ::
            (List.range r).map (fun d => { x := (nBlocks - r) + d, y := 0, z := 0 }) := by
        rw [List.range_succ_eq_map, List.map_cons, List.map_map]
        simp only [Nat.add_zero]
        congr 1; apply List.map_congr_left; intro d _
        dsimp only [Function.comp_apply, b0]
        have hd : nBlocks - (r + 1) + (d + 1) = nBlocks - r + d := by omega
        rw [hd]
      rw [hrange]
      unfold evalPTXKernelLoop
      let ctaId : Dim3 := { x := b0, y := 0, z := 0 }
      let cta0 := initCTAState k gridDim blockDim ctaId gMem pMem cMem
      have hthreads0 : cta0.threads = [] ++ ((List.range blockSize).map fun d =>
          laneAt 0 (0 + d) 0 (PTXRegFile.ofRegDecls (stdKernelRegs nP nR nRd)) false) := by
        have ht := initCTA_threads_1d k gridDim blockSize ctaId gMem pMem
        unfold cta0 initCTAState at ht ⊢
        rw [hregs, hlocal] at ht ⊢
        simpa [mkLane, laneAt] using ht
      have hmem0 : MemState nIn len inWords hlen outFn (fun i => i < ctaId.x * blockSize + 0)
          cta0.globalMem := by
        simpa [cta0, initCTAState, ctaId] using hmem
      have hlog0 : SafePTXLog (nIn * len * 8) len
          (fun cx => ctaId.x * blockSize ≤ cx ∧ cx < ctaId.x * blockSize + 0)
          (laneOf1D blockSize ctaId) cta0.epochLog := by
        intro e he; simp [cta0, initCTAState] at he
      obtain ⟨ctaFinal, ctaLog, hrunCTA, hmemCTA, ⟨hlogCTA⟩⟩ :=
        runCTA_threads_1d nP nR nRd nIn len vi maxMidSteps blockSize ctaId doneLbl mid
          inWords hlen outFn hp hr hr6 hvi houn hb032 hblk32 hnoLbl hMid
          blockSize (Nat.le_refl _) fuelPerCTA cta0 []
          rfl rfl rfl (by simpa [Nat.sub_self] using hthreads0)
          (fun _ h => nomatch h) (by simpa [Nat.sub_self] using hmem0)
          (by simpa [Nat.sub_self] using hlog0) hfuel
      rw [← hbody] at hrunCTA
      have hcross := checkCrossCTAGlobalLog_ok (nIn * len * 8) len
        (fun cx => cx < b0 * blockSize)
        (fun cx => ctaId.x * blockSize ≤ cx ∧ cx < ctaId.x * blockSize + blockSize)
        (fun cx h1 h2 => by dsimp [ctaId] at h2; omega) priorLog ctaLog hprior hlogCTA
      have hmulNext : (nBlocks - r) * blockSize = b0 * blockSize + blockSize := by
        have hb1 : nBlocks - r = b0 + 1 := by dsimp only [b0]; omega
        rw [hb1, Nat.add_mul, Nat.one_mul]
      have hmemNext : MemState nIn len inWords hlen outFn
          (fun i => i < (nBlocks - r) * blockSize) ctaFinal.globalMem := by
        rw [hmulNext]; exact hmemCTA
      have hlogNext : SafeGlobalLog (nIn * len * 8) len
          (fun cx => cx < (nBlocks - r) * blockSize) (ctaLog ++ priorLog) := by
        intro e he
        rcases List.mem_append.mp he with hc | hp'
        · rcases hlogCTA e hc with ⟨hsp, hat, hw, hkind⟩
          refine ⟨hsp, hat, hw, ?_⟩
          rcases hkind with hl | ⟨hwr, cx, hcx, hbd, hadr⟩
          · exact Or.inl hl
          · exact Or.inr ⟨hwr, cx, hcx, by dsimp [ctaId] at hbd; omega, hadr⟩
        · rcases hprior e hp' with ⟨hsp, hat, hw, hkind⟩
          refine ⟨hsp, hat, hw, ?_⟩
          rcases hkind with hl | ⟨hwr, cx, hcx, hbd, hadr⟩
          · exact Or.inl hl
          · exact Or.inr ⟨hwr, cx, hcx, by omega, hadr⟩
      obtain ⟨gFinal, hevNext, hmemFinal⟩ :=
        ih (by omega) ctaFinal.globalMem (ctaLog ++ priorLog) hmemNext hlogNext
      refine ⟨gFinal, ?_, hmemFinal⟩
      change PTXOutcome.bind (runCTAWithGlobalLog fuelPerCTA k.body cta0 []) _ = _
      rw [hrunCTA]; dsimp only [PTXOutcome.bind]
      rw [hcross]; dsimp only [PTXOutcome.bind]
      exact hevNext
  have hprior0 : SafeGlobalLog (nIn * len * 8) len (fun cx => cx < 0 * blockSize) [] := by
    intro _ h; nomatch h
  have hmemInit : MemState nIn len inWords hlen outFn (fun i => i < 0 * blockSize)
      (packGlobalBuffers nIn len inWords) := by
    simpa using MemState_init nIn len inWords hlen outFn
  obtain ⟨gFinal, hev, hmemF⟩ := hloop nBlocks (Nat.le_refl _)
    (packGlobalBuffers nIn len inWords) []
    (by simpa [Nat.sub_self] using hmemInit) (by simpa [Nat.sub_self] using hprior0)
  refine ⟨gFinal, ?_, ?_⟩
  · unfold evalPTXKernel; rw [dim3_coords_1d nBlocks]
    simpa [Nat.sub_self] using hev
  · intro i hi; exact hmemF.2.2 i hi (by omega)
end LeanNative.Proofs.PTXSIMT
