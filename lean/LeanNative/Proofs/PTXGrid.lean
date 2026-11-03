import LeanNative.Proofs.PTXExec

namespace LeanNative.Proofs.PTXSIMT

open LeanNative.Backend.PTXAst

theorem runCTA_bra_pred (f : Nat) (stmts : List PTXStmt) (cta : PTXCTAState)
    (done : List PTXThreadState) (th : PTXThreadState) (todo : List PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (pi : Nat) (hpi : pi < nP)
    (cond : Bool) (lbl : String) (target : Nat) (saved : List MemAccessLog)
    (hthreads : cta.threads = done ++ (th :: todo))
    (hdone : ∀ t ∈ done, t.halted = true)
    (hnh : th.halted = false)
    (hpc : stmts[th.pc]? = some (.instr (some { predReg := s!"%p{pi}" }) (.bra lbl)))
    (hlp : th.regs.regs.lookup s!"%p{pi}" = some (.pred cond))
    (hlbl : findLabelPC? stmts lbl = some target) :
    runCTAWithGlobalLog (f + 1) stmts cta saved =
      runCTAWithGlobalLog f stmts { cta with threads := done ++
        ((if cond then { th with pc := target } else { th with pc := th.pc + 1 }) :: todo) } saved := by
  have hexec := exec_bra_pred stmts cta th hrt pi hpi cond lbl target hlp hlbl
  have hstep := step_non_barrier_instr stmts cta done th todo
    (some { predReg := s!"%p{pi}" }) (.bra lbl) _ cta.globalMem cta.sharedMem cta.epochLog
    hthreads hdone hnh hpc (fun _ hc => nomatch hc) (fun _ _ _ _ _ hc => nomatch hc) hexec
  have hnc : cta.epochLog = [] ∨
      ({ cta with threads := done ++
        ((if cond then { th with pc := target } else { th with pc := th.pc + 1 }) :: todo) } : PTXCTAState).epochLog ≠ [] := by
    cases h : cta.epochLog with
    | nil => exact Or.inl rfl
    | cons _ _ => exact Or.inr (by simp)
  exact runCTAWithGlobalLog_step_no_clear f stmts cta _ saved hstep hnc

theorem runCTA_mem_instr (f : Nat) (stmts : List PTXStmt) (cta : PTXCTAState)
    (done : List PTXThreadState) (th : PTXThreadState) (todo : List PTXThreadState)
    (ins : PTXInstr) (th' : PTXThreadState) (gMem' : ByteMemory) (e : MemAccessLog)
    (saved : List MemAccessLog)
    (hthreads : cta.threads = done ++ (th :: todo))
    (hdone : ∀ t ∈ done, t.halted = true)
    (hnh : th.halted = false)
    (hpc : stmts[th.pc]? = some (.instr none ins))
    (hnBar : ∀ b, ins ≠ .barSync b)
    (hnShfl : ∀ d s o c m, ins ≠ .shflSyncBfly d s o c m)
    (hexec : execNonBarrierInstr stmts cta th ins =
      .ok (th', gMem', cta.sharedMem, e :: cta.epochLog)) :
    runCTAWithGlobalLog (f + 1) stmts cta saved =
      runCTAWithGlobalLog f stmts
        { cta with threads := done ++ (th' :: todo), globalMem := gMem', epochLog := e :: cta.epochLog } saved := by
  have hp : execPredicatedInstr stmts cta th none ins =
      .ok (th', gMem', cta.sharedMem, e :: cta.epochLog) := by
    unfold execPredicatedInstr evalPredGuard; dsimp only [PTXOutcome.bind]; exact hexec
  have hstep := step_non_barrier_instr stmts cta done th todo none ins
    th' gMem' cta.sharedMem (e :: cta.epochLog) hthreads hdone hnh hpc hnBar hnShfl hp
  exact runCTAWithGlobalLog_step_no_clear f stmts cta _ saved hstep (Or.inr (by simp))


/-! ## 6. Guarded 1D CTA and grid loop -/

theorem dim3_coords_1d (n : Nat) :
    ({ x := n, y := 1, z := 1 } : Dim3).coords =
      (List.range n).map (fun x => ({ x := x, y := 0, z := 0 } : Dim3)) := by
  simp [Dim3.coords]

/-- Standard 13-statement 1D global-ID setup + bounds check + output-address calculation
    emitted at the start of every `PTXLower` kernel (`pc = 0..12`). -/
def stdGidSetup (doneLbl : String) : List PTXStmt :=
  [ .instr none (.mov .u32 "%r0" (.sreg .ctaidX))
  , .instr none (.mov .u32 "%r1" (.sreg .ntidX))
  , .instr none (.mov .u32 "%r2" (.sreg .tidX))
  , .instr none (.mul .wide .u32 "%rd0" (.reg "%r0") (.reg "%r1"))
  , .instr none (.cvt .none .u64 .u32 "%rd1" (.reg "%r2"))
  , .instr none (.add .none .u64 "%rd2" (.reg "%rd0") (.reg "%rd1"))
  , .instr none (.ldParam .u64 "%rd3" "param_n")
  , .instr none (.setp .ge .u64 "%p0" (.reg "%rd2") (.reg "%rd3"))
  , .instr (some { predReg := "%p0" }) (.bra doneLbl)
  , .instr none (.ldParam .u64 "%rd4" "param_out")
  , .instr none (.cvtaToGlobal .u64 "%rd4" (.reg "%rd4"))
  , .instr none (.shl .b64 "%rd5" (.reg "%rd2") (.immU64 (BitVec.ofNat 64 3)))
  , .instr none (.add .none .u64 "%rd6" (.reg "%rd4") (.reg "%rd5")) ]

def stdParamMem (nIn len : Nat) : ParamMemory :=
  { params := ("param_out", BitVec.ofNat 64 (nIn * len * 8)) ::
      (List.range nIn).map (fun j => (s!"param_in{j}", BitVec.ofNat 64 (j * len * 8))) ++
      [("param_n", BitVec.ofNat 64 len)] }

private theorem paramIn_ne_out (j : Nat) : s!"param_in{j}" ≠ "param_out" := by
  intro h; have h1 := congrArg String.toList h
  simp only [toString, String.toList_append] at h1
  change ('p' :: 'a' :: 'r' :: 'a' :: 'm' :: '_' :: 'i' :: 'n' :: (toString j).toList) =
    "param_out".toList at h1
  injection h1 with _ h2; injection h2 with _ h3; injection h3 with _ h4
  injection h4 with _ h5; injection h5 with _ h6; injection h6 with _ h7
  injection h7 with hio _; exact absurd hio (by decide)

private theorem paramIn_ne_n (j : Nat) : s!"param_in{j}" ≠ "param_n" := by
  intro h; have h1 := congrArg String.toList h
  simp only [toString, String.toList_append] at h1
  change ('p' :: 'a' :: 'r' :: 'a' :: 'm' :: '_' :: 'i' :: 'n' :: (toString j).toList) =
    "param_n".toList at h1
  injection h1 with _ h2; injection h2 with _ h3; injection h3 with _ h4
  injection h4 with _ h5; injection h5 with _ h6; injection h6 with _ h7
  injection h7 with hin _; exact absurd hin (by decide)

theorem stdParamMem_lookup_out (nIn len : Nat) :
    (stdParamMem nIn len).lookupParam? "param_out" = some (BitVec.ofNat 64 (nIn * len * 8)) := by
  simp [stdParamMem, ParamMemory.lookupParam?]

theorem stdParamMem_lookup_n (nIn len : Nat) :
    (stdParamMem nIn len).lookupParam? "param_n" = some (BitVec.ofNat 64 len) := by
  unfold stdParamMem ParamMemory.lookupParam?
  have h1 : ("param_n" == "param_out") = false := by decide
  rw [List.cons_append, List.lookup_cons, h1, List.lookup_append]
  have hnone : ((List.range nIn).map (fun j => (s!"param_in{j}", BitVec.ofNat 64 (j * len * 8)))).lookup "param_n" = none := by
    apply List.lookup_eq_none_iff.mpr
    intro kv hkv
    rcases List.mem_map.mp hkv with ⟨j, _, rfl⟩
    exact bne_iff_ne.mpr (Ne.symm (paramIn_ne_n j))
  rw [hnone]; simp

theorem stdParamMem_lookup_in (nIn len j : Nat) (hj : j < nIn) :
    (stdParamMem nIn len).lookupParam? s!"param_in{j}" = some (BitVec.ofNat 64 (j * len * 8)) := by
  unfold stdParamMem ParamMemory.lookupParam?
  have h1 : (s!"param_in{j}" == "param_out") = false :=
    beq_eq_false_iff_ne.mpr (paramIn_ne_out j)
  rw [List.cons_append, List.lookup_cons, h1, List.lookup_append]
  have haux : ∀ (xs : List Nat), xs.Nodup → j ∈ xs →
      (xs.map (fun k => (s!"param_in{k}", BitVec.ofNat 64 (k * len * 8)))).lookup s!"param_in{j}" =
        some (BitVec.ofNat 64 (j * len * 8)) := by
    intro xs; induction xs with
    | nil => intro _ hm; nomatch hm
    | cons x rest ih =>
      intro hnd hm
      rw [List.nodup_cons] at hnd
      rcases List.mem_cons.mp hm with rfl | hrest
      · simp
      · have hne : j ≠ x := fun h => hnd.1 (h ▸ hrest)
        have hbeq : (s!"param_in{j}" == s!"param_in{x}") = false :=
          beq_eq_false_iff_ne.mpr fun hs => hne (regName_inj "param_in" j x hs)
        rw [List.map_cons, List.lookup_cons, hbeq]
        exact ih hnd.2 hrest
  rw [haux (List.range nIn) List.nodup_range (List.mem_range.mpr hj)]
  rfl

theorem fit32_ofNat (n : Nat) (h : n < 2 ^ 32) :
    (BitVec.ofNat 64 n >>> 32) = 0#64 := by
  have h64 : n < 2 ^ 64 := by omega
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, Nat.shiftRight_eq_div_pow]
  change n / 4294967296 = 0; omega

theorem mask32_ofNat (n : Nat) (h : n < 2 ^ 32) :
    BitVec.ofNat 64 n &&& 0xFFFF_FFFF#64 = BitVec.ofNat 64 n :=
  mask32_id (BitVec.ofNat 64 n) (fit32_ofNat n h)

def rfSet (rf : PTXRegFile) (nm : String) (v : BitVec 64) : PTXRegFile :=
  rf.setScalarRaw nm v

theorem lookup_rfSet_self (rf : PTXRegFile) (nm : String) (v : BitVec 64) :
    (rfSet rf nm v).regs.lookup nm = some (.scalar v) := by
  unfold rfSet PTXRegFile.setScalarRaw
  simp [setAssoc_lookup_self]

theorem lookup_rfSet_ne (rf : PTXRegFile) (nm q : String) (v : BitVec 64) (hne : q ≠ nm) :
    (rfSet rf nm v).regs.lookup q = rf.regs.lookup q := by
  unfold rfSet PTXRegFile.setScalarRaw
  exact setAssoc_lookup_ne rf.regs nm q (.scalar v) hne

theorem regTyped_rfSet {rf : PTXRegFile} {nP nR nRd : Nat}
    (hrt : RegTyped rf nP nR nRd) (nm : String) (v : BitVec 64) :
    RegTyped (rfSet rf nm v) nP nR nRd :=
  RegTyped.setScalarRaw_preserves hrt nm v

theorem stmt_at (pre suf : List PTXStmt) (s : PTXStmt) :
    (pre ++ (s :: suf))[pre.length]? = some s := by
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem pred_ge_u64 (a b : BitVec 64) :
    evalPTXCmp .ge .u64 a b = decide ¬ (a.toNat < b.toNat) := by
  change BitVec.ule b a = decide ¬ (a.toNat < b.toNat)
  rw [BitVec.ule]
  simp only [decide_eq_decide]
  omega

def stdLoadIn (k : Nat) (reg : String) : List PTXStmt :=
  [ .instr none (.ldParam .u64 reg s!"param_in{k}")
  , .instr none (.cvtaToGlobal .u64 reg (.reg reg))
  , .instr none (.add .none .u64 reg (.reg reg) (.reg "%rd5"))
  , .instr none (.ldGlobal .u64 reg (.regOffset reg 0)) ]

/-- Append raw byte arrays across a list of `ByteMemory` regions. -/
def concatByteMems : List ByteMemory → ByteMemory
  | [] => { bytes := #[] }
  | m :: ms => { bytes := m.bytes ++ (concatByteMems ms).bytes }

/-- Pack `nIn` input buffers (`inWords 0 .. inWords (nIn - 1)`, each of `len` 64-bit words)
    followed by a zero-initialized output buffer of `len` 64-bit words at byte offset `nIn * len * 8`. -/
def packGlobalBuffers (nIn len : Nat) (inWords : Nat → List (BitVec 64)) : ByteMemory :=
  concatByteMems (((List.range nIn).map fun j => ByteMemory.ofU64Words (inWords j)) ++
    [ByteMemory.zeros (len * 8)])

theorem concatByteMems_append (xs ys : List ByteMemory) :
    concatByteMems (xs ++ ys) = { bytes := (concatByteMems xs).bytes ++ (concatByteMems ys).bytes } := by
  induction xs with
  | nil => simp [concatByteMems]
  | cons x rest ih =>
    simp [concatByteMems, ih, Array.append_assoc]

theorem concatByteMems_size_uniform (ms : List ByteMemory) (sz : Nat)
    (hall : ∀ m ∈ ms, m.bytes.size = sz) :
    (concatByteMems ms).bytes.size = ms.length * sz := by
  induction ms with
  | nil => simp [concatByteMems]
  | cons m rest ih =>
    have hm := hall m (.head rest)
    have hr := ih (fun x hx => hall x (.tail m hx))
    simp only [concatByteMems, Array.size_append, hm, hr, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem packGlobalBuffers_size (nIn len : Nat) (inWords : Nat → List (BitVec 64))
    (hlen : ∀ j < nIn, (inWords j).length = len) :
    (packGlobalBuffers nIn len inWords).bytes.size = (nIn + 1) * len * 8 := by
  unfold packGlobalBuffers
  have h1 := concatByteMems_size_uniform
    (((List.range nIn).map fun j => ByteMemory.ofU64Words (inWords j)) ++ [ByteMemory.zeros (len * 8)])
    (len * 8) ?_
  · simp only [List.length_append, List.length_map, List.length_range, List.length_singleton] at h1
    rw [h1, Nat.mul_assoc]
  · intro m hm
    rcases List.mem_append.mp hm with hmap | hzero
    · rcases List.mem_map.mp hmap with ⟨j, hj, rfl⟩
      rw [ofU64Words_size, hlen j (List.mem_range.mp hj)]
    · rw [List.mem_singleton.mp hzero]
      simp [ByteMemory.zeros]

theorem readLE_cong_shift (m1 m2 : ByteMemory) (a1 a2 : Nat) :
    ∀ k, (∀ i < k, m1.bytes[a1 + i]? = m2.bytes[a2 + i]?) →
      ByteMemory.readLittleEndianAux m1 a1 k = ByteMemory.readLittleEndianAux m2 a2 k := by
  intro k; induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h; unfold ByteMemory.readLittleEndianAux
    rw [h k (by omega), ih (fun i hi => h i (by omega))]

private theorem loadBits_append_mid (mPre mMid mSuf : ByteMemory) (off : Nat)
    (h : off + 8 ≤ mMid.bytes.size) :
    ({ bytes := mPre.bytes ++ mMid.bytes ++ mSuf.bytes } : ByteMemory).loadBits
      (mPre.bytes.size + off) 8 = mMid.loadBits off 8 := by
  let tot : ByteMemory := { bytes := mPre.bytes ++ mMid.bytes ++ mSuf.bytes }
  have hsz1 : mPre.bytes.size + off + 8 ≤ tot.bytes.size := by
    simp [tot, Array.size_append]; omega
  unfold ByteMemory.loadBits
  rw [ite_eq_left_iff.mpr fun hc => absurd hsz1 hc,
      ite_eq_left_iff.mpr fun hc => absurd h hc]
  apply readLE_cong_shift tot mMid (mPre.bytes.size + off) off 8
  intro i hi
  simp only [tot, Array.append_assoc]
  have hge : mPre.bytes.size ≤ mPre.bytes.size + off + i := by omega
  have hidx : (mPre.bytes.size + off + i) - mPre.bytes.size = off + i := by omega
  rw [Array.getElem?_append_right hge, hidx, Array.getElem?_append_left (by omega)]

theorem packGlobalBuffers_load_in (nIn len : Nat) (inWords : Nat → List (BitVec 64))
    (hlen : ∀ j < nIn, (inWords j).length = len)
    (j i : Nat) (hj : j < nIn) (hi : i < len) :
    (packGlobalBuffers nIn len inWords).loadBits (j * len * 8 + i * 8) 8 =
      some ((inWords j)[i]'(by rw [hlen j hj]; exact hi)) := by
  have hsplit : List.range nIn = List.range j ++ (j :: (List.range (nIn - j - 1)).map (fun d => j + 1 + d)) := by
    apply List.ext_getElem
    · simp; omega
    · intro k hk1 hk2
      rw [List.getElem_range]
      by_cases hkj : k < j
      · rw [List.getElem_append_left (by simp; omega), List.getElem_range]
      · rw [List.getElem_append_right (by simp; omega)]
        simp only [List.length_range]
        by_cases hkeq : k = j
        · subst hkeq; simp
        · let d := k - j - 1
          have hsub : k - j = d + 1 := by omega
          have hd : d < nIn - j - 1 := by simp at hk1; omega
          have hget : (j :: List.map (fun d => j + 1 + d) (List.range (nIn - j - 1)))[k - j]'(by simp; omega) =
              (List.map (fun d => j + 1 + d) (List.range (nIn - j - 1)))[d]'(by simp [hd]) := by
            simp [hsub]
          rw [hget]
          simp [d]; omega
  unfold packGlobalBuffers
  rw [hsplit, List.map_append, List.map_cons, List.append_assoc, List.cons_append]
  let preList := (List.range j).map fun k => ByteMemory.ofU64Words (inWords k)
  let midMem := ByteMemory.ofU64Words (inWords j)
  let sufList := ((List.range (nIn - j - 1)).map (fun d => j + 1 + d)).map
      (fun k => ByteMemory.ofU64Words (inWords k)) ++ [ByteMemory.zeros (len * 8)]
  change (concatByteMems (preList ++ (midMem :: sufList))).loadBits (j * len * 8 + i * 8) 8 = _
  rw [concatByteMems_append]
  have hcons : concatByteMems (midMem :: sufList) =
      { bytes := midMem.bytes ++ (concatByteMems sufList).bytes } := rfl
  rw [hcons, ← Array.append_assoc]
  have hpreSz : (concatByteMems preList).bytes.size = j * (len * 8) := by
    have h1 := concatByteMems_size_uniform preList (len * 8) fun m hm => by
      rcases List.mem_map.mp hm with ⟨k, hk, rfl⟩
      rw [ofU64Words_size, hlen k (Nat.lt_trans (List.mem_range.mp hk) hj)]
    simpa [preList] using h1
  have hpreMul : j * len * 8 = (concatByteMems preList).bytes.size := by rw [hpreSz, Nat.mul_assoc]
  have hmidSz : i * 8 + 8 ≤ midMem.bytes.size := by
    simp [midMem, ofU64Words_size, hlen j hj]; omega
  rw [hpreMul, loadBits_append_mid (concatByteMems preList) midMem (concatByteMems sufList) (i * 8) hmidSz]
  exact ofU64Words_loadBits (inWords j) i (by rw [hlen j hj]; exact hi)


end LeanNative.Proofs.PTXSIMT
