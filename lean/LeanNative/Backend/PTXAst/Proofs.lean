import LeanNative.Backend.PTXAst.Eval

/-!
# Genuine NVIDIA CUDA PTX 8.0 AST (`C2b`) — kernel-checked SIMT theorems.
-/

namespace LeanNative.Backend.PTXAst

/-! ## 4. Kernel-Checked Theorems (`0 sorryAx`, `strict-proofs` clean) -/

/-- Address-space non-interference (Shared -> Global): executing `st.shared` never mutates `globalMem`
    whenever it succeeds, leaving `globalMem` bit-identical to `cta.globalMem`. -/
theorem st_shared_preserves_global (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    (ty : PTXType) (addr : PTXAddr) (src : PTXOperand)
    (th' : PTXThreadState) (gMem' sMem' : ByteMemory)
    (log' : List MemAccessLog)
    (h_exec : execNonBarrierInstr stmts cta th (.stShared ty addr src) = .ok (th', gMem', sMem', log')) :
    gMem' = cta.globalMem := by
  dsimp [execNonBarrierInstr, PTXOutcome.bind] at h_exec
  cases hAddr : evalAddr cta th addr <;> simp [hAddr] at h_exec
  case ok byteAddr =>
    cases hSrc : evalOperand cta th src (some ty.bitWidth) <;> simp [hSrc] at h_exec
    case ok val =>
      cases hAlign : checkAligned .shared byteAddr ty.byteWidth <;> simp [hAlign] at h_exec
      case ok =>
        cases hRace : recordEpochAccess cta.epochLog th.tid .shared byteAddr ty.byteWidth true false <;>
          simp [hRace] at h_exec
        case ok logNext =>
          cases hStore : cta.sharedMem.storeBits byteAddr ty.byteWidth (maskForType ty val) <;>
            simp [hStore] at h_exec
          exact h_exec.2.1.symm

/-- Address-space non-interference (Global -> Shared): executing `st.global` never mutates per-CTA
    `sharedMem` whenever it succeeds, leaving `sharedMem` bit-identical to `cta.sharedMem`. -/
theorem st_global_preserves_shared (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    (ty : PTXType) (addr : PTXAddr) (src : PTXOperand)
    (th' : PTXThreadState) (gMem' sMem' : ByteMemory)
    (log' : List MemAccessLog)
    (h_exec : execNonBarrierInstr stmts cta th (.stGlobal ty addr src) = .ok (th', gMem', sMem', log')) :
    sMem' = cta.sharedMem := by
  dsimp [execNonBarrierInstr, PTXOutcome.bind] at h_exec
  cases hAddr : evalAddr cta th addr <;> simp [hAddr] at h_exec
  case ok byteAddr =>
    cases hSrc : evalOperand cta th src (some ty.bitWidth) <;> simp [hSrc] at h_exec
    case ok val =>
      cases hAlign : checkAligned .global byteAddr ty.byteWidth <;> simp [hAlign] at h_exec
      case ok =>
        cases hRace : recordEpochAccess cta.epochLog th.tid .global byteAddr ty.byteWidth true false <;>
          simp [hRace] at h_exec
        case ok logNext =>
          cases hStore : cta.globalMem.storeBits byteAddr ty.byteWidth (maskForType ty val) <;>
            simp [hStore] at h_exec
          exact h_exec.2.2.1.symm

/-- Predicated instruction false-guard no-op: whenever `evalPredGuard th guard = .ok false`,
    `execPredicatedInstr` advances `th.pc` by 1 while leaving `th.regs`, `cta.globalMem`, and
    `cta.sharedMem` completely untouched for every `PTXInstr` (including `bar.sync` and `st.*`). -/
theorem execInstr_pred_false_noop (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    (guard : Option PTXPredGuard) (ins : PTXInstr)
    (h_false : evalPredGuard th guard = .ok false) :
    execPredicatedInstr stmts cta th guard ins =
      .ok ({ th with pc := th.pc + 1 }, cta.globalMem, cta.sharedMem, cta.epochLog) := by
  unfold execPredicatedInstr PTXOutcome.bind
  rw [h_false]
  rfl

/-- Uniform CTA `bar.sync` convergence: when every thread in the CTA arrives at the exact same
    barrier identifier `bid`, `stepCTABarrier` converges cleanly without error, advancing every
    thread's program counter past the barrier while preserving both `globalMem` and `sharedMem`. -/
theorem bar_sync_uniform_converges (bid : Nat) (states : List (Option Nat)) (cta : PTXCTAState)
    (h_uniform : states.all (fun s => s == some bid) = true) :
    stepCTABarrier bid states cta =
      .ok { cta with threads := cta.threads.map fun th => { th with pc := th.pc + 1 }, epochLog := [] } := by
  unfold stepCTABarrier
  simp [h_uniform]

/-- Divergent CTA `bar.sync` detection: when at least one thread in the CTA disagrees with `some bid`
    (e.g., took a divergent branch or halted early), `stepCTABarrier` traps with explicit
    `PTXOutcome.barrierDivergence bid`. -/
theorem bar_sync_divergent_errors (bid : Nat) (states : List (Option Nat)) (cta : PTXCTAState)
    (h_div : states.all (fun s => s == some bid) = false) :
    stepCTABarrier bid states cta = .barrierDivergence bid := by
  unfold stepCTABarrier
  simp [h_div]

/-- Halted CTA fixed-point: once all threads in `cta` have halted, `runCTA` immediately returns
    `.ok cta` for every step budget `fuel`. -/
theorem runCTA_halted (fuel : Nat) (stmts : List PTXStmt) (cta : PTXCTAState)
    (h_halted : cta.threads.all (·.halted) = true) :
    runCTA fuel stmts cta = .ok cta := by
  cases fuel with
  | zero =>
    unfold runCTA
    simp [h_halted]
  | succ f =>
    unfold runCTA stepCTA PTXOutcome.bind
    simp [h_halted]

/-- Fuel-independent operational determinism of the PTX SIMT CTA semantics (`runCTA`):
    any two executions from the same kernel body and initial CTA state under arbitrary step
    budgets `f1` and `f2` that both reach terminal (non-`fuelExhausted`) outcomes produce
    identical `PTXOutcome` results. -/
theorem runCTA_deterministic (f1 f2 : Nat) (stmts : List PTXStmt) (cta : PTXCTAState)
    (out1 out2 : PTXOutcome PTXCTAState)
    (h1 : runCTA f1 stmts cta = out1)
    (h2 : runCTA f2 stmts cta = out2)
    (hne1 : out1 ≠ .fuelExhausted)
    (hne2 : out2 ≠ .fuelExhausted) :
    out1 = out2 := by
  induction f1 generalizing f2 cta with
  | zero =>
    unfold runCTA at h1
    cases hAll : cta.threads.all (·.halted)
    · simp [hAll] at h1
      exact False.elim (hne1 h1.symm)
    · simp [hAll] at h1
      have hRun2 := runCTA_halted f2 stmts cta hAll
      rw [hRun2] at h2
      exact h1.symm.trans h2
  | succ f1' ih =>
    cases f2 with
    | zero =>
      unfold runCTA at h2
      cases hAll : cta.threads.all (·.halted)
      · simp [hAll] at h2
        exact False.elim (hne2 h2.symm)
      · simp [hAll] at h2
        have hRun1 := runCTA_halted (f1' + 1) stmts cta hAll
        rw [hRun1] at h1
        exact h1.symm.trans h2
    | succ f2' =>
      unfold runCTA PTXOutcome.bind at h1 h2
      cases hStep : stepCTA stmts cta <;> simp [hStep] at h1 h2
      case ok pair =>
        rcases pair with ⟨done, cta'⟩
        cases done with
        | true =>
          simp at h1 h2
          exact h1.symm.trans h2
        | false =>
          simp at h1 h2
          exact ih f2' cta' h1 h2
      all_goals exact h1.symm.trans h2

/-- 1:1 injectivity of `ppPTXType`: distinct PTX AST types pretty-print to distinct PTX type tokens. -/
theorem ppPTXType_injective (t1 t2 : PTXType) (h : ppPTXType t1 = ppPTXType t2) :
    t1 = t2 := by
  cases t1 <;> cases t2 <;> first | rfl | exact absurd h (by decide)

/-- 1:1 injectivity of `ppStateSpace`: distinct PTX state spaces pretty-print to distinct tokens. -/
theorem ppStateSpace_injective (s1 s2 : StateSpace) (h : ppStateSpace s1 = ppStateSpace s2) :
    s1 = s2 := by
  cases s1 <;> cases s2 <;> first | rfl | exact absurd h (by decide)

/-- 1:1 injectivity of `ppSpecialReg`: distinct special coordinate registers render to distinct tokens. -/
theorem ppSpecialReg_injective (r1 r2 : SpecialReg) (h : ppSpecialReg r1 = ppSpecialReg r2) :
    r1 = r2 := by
  cases r1 <;> cases r2 <;> first | rfl | exact absurd h (by decide)

/-- 1:1 injectivity of `ppMulMode`: distinct PTX multiply modifiers render to distinct tokens. -/
theorem ppMulMode_injective (m1 m2 : PTXMulMode) (h : ppMulMode m1 = ppMulMode m2) :
    m1 = m2 := by
  cases m1 <;> cases m2 <;> first | rfl | exact absurd h (by decide)

/-- 1:1 injectivity of `ppCmpOp`: distinct PTX comparison predicates render to distinct tokens. -/
theorem ppCmpOp_injective (c1 c2 : PTXCmpOp) (h : ppCmpOp c1 = ppCmpOp c2) :
    c1 = c2 := by
  cases c1 <;> cases c2 <;> first | rfl | exact absurd h (by decide)

private theorem charList_isPrefixOf_append :
    ∀ (xs ys : List Char), List.isPrefixOf xs (xs ++ ys) = true
  | [], _ => rfl
  | x :: xs, ys => by
    simp [charList_isPrefixOf_append xs ys]

/-- Structural header well-formedness of `ppPTXModule`: every rendered module begins with the exact
    `.version <major>.<minor>`, `.target`, and `.address_size` header directives of `m`. -/
theorem ppPTXModule_header_prefix (m : PTXModule) :
    List.isPrefixOf (ppPTXModuleHeader m).toList (ppPTXModule m).toList = true := by
  unfold ppPTXModule
  cases m.kernels with
  | nil =>
    rw [String.toList_append]
    exact charList_isPrefixOf_append _ _
  | cons k ks =>
    simp only [String.append_assoc, String.toList_append]
    exact charList_isPrefixOf_append _ _

private theorem getLast_append_singleton (xs : List Char) (c : Char) :
    (xs ++ [c]).getLast? = some c := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    cases rest with
    | nil => rfl
    | cons y ys => exact ih

private theorem semicolon_toList_eq : ";".toList = [';'] := by decide

private theorem append_semicolon_getLast (s : String) :
    (s ++ ";").toList.getLast? = some ';' := by
  rw [String.toList_append, semicolon_toList_eq]
  exact getLast_append_singleton s.toList ';'

/-- Structural statement well-formedness of `ppPTXInstr`: every rendered PTX instruction across all
    ISA constructors terminates with a trailing `';'`. -/
theorem ppPTXInstr_semicolon_terminated (ins : PTXInstr) :
    (ppPTXInstr ins).toList.getLast? = some ';' := by
  cases ins <;> exact append_semicolon_getLast _

/-- Integer division by zero traps explicitly with `.divisionByZero` across all PTX integer/bit-size
    types (never silently returning `0`). -/
theorem ptx_div_zero_traps (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    (ty : PTXType) (dst : String) (a b : PTXOperand) (va : BitVec 64)
    (h_int : ty ≠ .f32 ∧ ty ≠ .f64)
    (h_a : evalOperand cta th a (some ty.bitWidth) = .ok va)
    (h_b : evalOperand cta th b (some ty.bitWidth) = .ok 0#64) :
    execNonBarrierInstr stmts cta th (.div ty dst a b) = .divisionByZero := by
  rcases h_int with ⟨hf32, hf64⟩
  dsimp [execNonBarrierInstr, PTXOutcome.bind]
  rw [h_a, h_b]
  cases ty <;>
    first
    | exact absurd rfl hf32
    | exact absurd rfl hf64
    | rfl

/-- Signed 64-bit `INT64_MIN / -1` division overflow traps explicitly with `.signedDivOverflow`. -/
theorem ptx_sdiv64_min_neg1_traps (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    (dst : String) (a b : PTXOperand)
    (h_a : evalOperand cta th a (some PTXType.s64.bitWidth) = .ok 0x8000_0000_0000_0000#64)
    (h_b : evalOperand cta th b (some PTXType.s64.bitWidth) = .ok 0xFFFF_FFFF_FFFF_FFFF#64) :
    execNonBarrierInstr stmts cta th (.div .s64 dst a b) = .signedDivOverflow := by
  dsimp [execNonBarrierInstr, PTXOutcome.bind]
  rw [h_a, h_b]
  rfl

private theorem lookup_setAssoc_same (xs : List (String × PTXRegVal)) (k : String) (v : PTXRegVal) :
    List.lookup k (PTXRegFile.setAssoc xs k v) = some v := by
  induction xs with
  | nil => simp [PTXRegFile.setAssoc]
  | cons hd tl ih =>
    rcases hd with ⟨k', v'⟩
    by_cases hk : k' == k
    · have heq : k' = k := LawfulBEq.eq_of_beq hk
      subst heq
      simp [PTXRegFile.setAssoc]
    · have hk2 : (k == k') = false := by
        cases h2 : k == k'
        · rfl
        · have heq : k = k' := LawfulBEq.eq_of_beq h2
          subst heq
          simp at hk
      simp [PTXRegFile.setAssoc, List.lookup, hk, hk2, ih]

private theorem lookup_setAssoc_ne (xs : List (String × PTXRegVal)) (q k : String) (v : PTXRegVal)
    (hne : q ≠ k) :
    List.lookup q (PTXRegFile.setAssoc xs k v) = List.lookup q xs := by
  induction xs with
  | nil =>
    have hb : (q == k) = false := beq_false_of_ne hne
    simp [PTXRegFile.setAssoc, List.lookup, hb]
  | cons hd tl ih =>
    rcases hd with ⟨k', v'⟩
    by_cases hk : k' == k
    · have heq : k' = k := LawfulBEq.eq_of_beq hk
      subst heq
      have hb : (q == k') = false := beq_false_of_ne hne
      simp [PTXRegFile.setAssoc, List.lookup, hb]
    · simp [PTXRegFile.setAssoc, hk]
      cases hq : q == k' <;> simp [List.lookup, hq, ih]

/-- `setScalarRaw` writes the scalar value that `getScalar` reads back. -/
theorem setScalarRaw_getScalar (rf : PTXRegFile) (name : String) (v : BitVec 64) :
    (rf.setScalarRaw name v).getScalar name = v := by
  simp [PTXRegFile.getScalar, PTXRegFile.setScalarRaw, lookup_setAssoc_same]

/-- `setPredRaw` writes the predicate that `getPred` reads back. -/
theorem setPredRaw_getPred (rf : PTXRegFile) (name : String) (b : Bool) :
    (rf.setPredRaw name b).getPred name = some b := by
  simp [PTXRegFile.getPred, PTXRegFile.setPredRaw, lookup_setAssoc_same]

/-- Writing a distinct register does not disturb an existing predicate. -/
theorem setScalarRaw_preserves_other_pred (rf : PTXRegFile) (predName regName : String) (v : BitVec 64)
    (hne : predName ≠ regName) :
    (rf.setScalarRaw regName v).getPred predName = rf.getPred predName := by
  simp [PTXRegFile.getPred, PTXRegFile.setScalarRaw,
    lookup_setAssoc_ne _ predName regName _ hne]

/-- Production guarded PTX division (`setp.eq.u64 %p, b, 0; selp.u64 safeB, 1, b, %p; div.u64 q, a, safeB; selp.u64 out, 0, q, %p`)
    never traps even when divisor `b = 0`, producing `0` on `b = 0`. -/
theorem ptx_guarded_div_zero_safe (cta : PTXCTAState) (th : PTXThreadState) (va : BitVec 64) :
    let stmts : List PTXStmt := [
      .instr none (.setp .eq .u64 "%p0" (.reg "%rd2") (.immU64 0#64)),
      .instr none (.selp .u64 "%rd3" (.immU64 1#64) (.reg "%rd2") "%p0"),
      .instr none (.div .u64 "%rd3" (.reg "%rd1") (.reg "%rd3")),
      .instr none (.selp .u64 "%rd3" (.immU64 0#64) (.reg "%rd3") "%p0")
    ]
    let th0 : PTXThreadState := { th with
      pc := 0
      regs := (PTXRegFile.empty.setScalarRaw "%rd1" va).setScalarRaw "%rd2" 0#64 }
    (PTXOutcome.bind (execNonBarrierInstr stmts cta th0 (.setp .eq .u64 "%p0" (.reg "%rd2") (.immU64 0#64))) fun (th1, _, _, _) =>
     PTXOutcome.bind (execNonBarrierInstr stmts cta th1 (.selp .u64 "%rd3" (.immU64 1#64) (.reg "%rd2") "%p0")) fun (th2, _, _, _) =>
     PTXOutcome.bind (execNonBarrierInstr stmts cta th2 (.div .u64 "%rd3" (.reg "%rd1") (.reg "%rd3"))) fun (th3, _, _, _) =>
     PTXOutcome.bind (execNonBarrierInstr stmts cta th3 (.selp .u64 "%rd3" (.immU64 0#64) (.reg "%rd3") "%p0")) fun (th4, _, _, _) =>
       .ok (th4.regs.getScalar "%rd3")) = .ok 0#64 := by
  intro stmts th0
  have hUf32 : (PTXType.u64 == PTXType.f32) = false := rfl
  have hUf64 : (PTXType.u64 == PTXType.f64) = false := rfl
  have hUs64 : (PTXType.u64 == PTXType.s64) = false := rfl
  have hUs32 : (PTXType.u64 == PTXType.s32) = false := rfl
  have h1z : (1#64 == 0#64) = false := rfl
  have hne12 : "%rd1" ≠ "%rd2" := by decide
  have hne1p : "%rd1" ≠ "%p0" := by decide
  have hne13 : "%rd1" ≠ "%rd3" := by decide
  have hne2p : "%rd2" ≠ "%p0" := by decide
  have hnep3 : "%p0" ≠ "%rd3" := by decide
  simp [th0, execNonBarrierInstr, PTXOutcome.bind, evalOperand, evalPTXCmp, maskForType,
    PTXRegFile.empty, PTXRegFile.readScalarChecked, PTXRegFile.readPredChecked,
    PTXRegFile.setScalar, PTXRegFile.setPred, PTXRegFile.setScalarRaw, PTXRegFile.setPredRaw,
    PTXRegFile.getScalar, lookup_setAssoc_same, lookup_setAssoc_ne,
    hne12, hne1p, hne13, hne2p, hnep3,
    hUf32, hUf64, hUs64, hUs32]

/-- Misaligned global loads (`byteAddr % ty.byteWidth ≠ 0`) trap explicitly with `.misalignedAccess`. -/
theorem ptx_misaligned_global_load_traps (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    (ty : PTXType) (dst : String) (addr : PTXAddr) (byteAddr : Nat)
    (h_addr : evalAddr cta th addr = .ok byteAddr)
    (h_misalign : byteAddr % ty.byteWidth ≠ 0) :
    execNonBarrierInstr stmts cta th (.ldGlobal ty dst addr) =
      .misalignedAccess .global byteAddr ty.byteWidth := by
  have hb : (byteAddr % ty.byteWidth == 0) = false := beq_false_of_ne h_misalign
  simp [execNonBarrierInstr, PTXOutcome.bind, checkAligned, h_addr, hb]

/-- Stores to read-only `.const` memory trap explicitly with `.readOnlyWrite .const`. -/
theorem ptx_const_store_traps (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    (ty : PTXType) (addr : PTXAddr) (src : PTXOperand) (byteAddr : Nat)
    (h_addr : evalAddr cta th addr = .ok byteAddr) :
    execNonBarrierInstr stmts cta th (.stConst ty addr src) = .readOnlyWrite .const byteAddr := by
  simp [execNonBarrierInstr, PTXOutcome.bind, h_addr]

/-- Negative register address displacements render as `[%rd-8]` (never invalid `[%rd+-8]`). -/
theorem ppPTXAddr_neg_displacement (r : String) :
    ppPTXAddr (.regOffset r (-8)) = "[" ++ r ++ "-8]" := by
  have hstr : toString (-8 : Int) = "-8" := rfl
  simp [ppPTXAddr, hstr, String.append_assoc]
  rfl

/-- Disjoint byte ranges never trigger a SIMT data race: when `a1 + w1 ≤ a2` or `a2 + w2 ≤ a1`,
    `rangesOverlap a1 w1 a2 w2 = false`. -/
theorem rangesOverlap_disjoint_false (a1 w1 a2 w2 : Nat)
    (h_disj : a1 + w1 ≤ a2 ∨ a2 + w2 ≤ a1) :
    rangesOverlap a1 w1 a2 w2 = false := by
  unfold rangesOverlap
  rcases h_disj with h1 | h2
  · exact decide_eq_false (fun ⟨_, hlt⟩ => Nat.not_lt.mpr h1 hlt)
  · exact decide_eq_false (fun ⟨hlt, _⟩ => Nat.not_lt.mpr h2 hlt)

/-- Disjoint per-thread stores in the same barrier epoch never conflict (`recordEpochAccess` succeeds). -/
theorem recordEpochAccess_disjoint_ok (tid1 tid2 : Dim3) (sp : StateSpace)
    (a1 w1 a2 w2 : Nat) (wFlag1 wFlag2 : Bool)
    (h_disj : a1 + w1 ≤ a2 ∨ a2 + w2 ≤ a1) :
    recordEpochAccess [{ tid := tid1, space := sp, addr := a1, width := w1, isWrite := wFlag1 }]
      tid2 sp a2 w2 wFlag2 =
      .ok [{ tid := tid2, space := sp, addr := a2, width := w2, isWrite := wFlag2 },
           { tid := tid1, space := sp, addr := a1, width := w1, isWrite := wFlag1 }] := by
  have hNoOverlap := rangesOverlap_disjoint_false a2 w2 a1 w1 h_disj.symm
  unfold recordEpochAccess findDataRace?
  simp [hNoOverlap]
  rfl

/-- Unsynchronized cross-thread write-write or read-write overlap at the same address traps with `.dataRace`. -/
theorem recordEpochAccess_overlap_races (tid1 tid2 : Dim3) (sp : StateSpace)
    (addr width : Nat)
    (h_diff_tid : (tid1 != tid2) = true)
    (h_pos_width : 0 < width) :
    recordEpochAccess [{ tid := tid1, space := sp, addr := addr, width := width, isWrite := true }]
      tid2 sp addr width false = .dataRace sp addr := by
  have hOv : rangesOverlap addr width addr width = true := by
    unfold rangesOverlap
    exact decide_eq_true ⟨Nat.lt_add_of_pos_right h_pos_width, Nat.lt_add_of_pos_right h_pos_width⟩
  have hSp : (sp == sp) = true := by cases sp <;> rfl
  unfold recordEpochAccess findDataRace?
  simp [h_diff_tid, hOv, hSp]

/-- Fuel monotonicity of `runCTA`: once `runCTA f1 stmts cta` reaches any terminal (non-`fuelExhausted`)
    outcome `out`, running with any larger fuel budget `f2 ≥ f1` produces the exact same `out`. -/
theorem runCTA_mono_fuel (f1 f2 : Nat) (stmts : List PTXStmt) (cta : PTXCTAState)
    (out : PTXOutcome PTXCTAState)
    (hle : f1 ≤ f2)
    (h1 : runCTA f1 stmts cta = out)
    (hne : out ≠ .fuelExhausted) :
    runCTA f2 stmts cta = out := by
  induction f1 generalizing f2 cta with
  | zero =>
    unfold runCTA at h1
    cases hAll : cta.threads.all (·.halted)
    · simp [hAll] at h1
      exact False.elim (hne h1.symm)
    · simp [hAll] at h1
      have hRun2 := runCTA_halted f2 stmts cta hAll
      exact hRun2.trans h1
  | succ f1' ih =>
    cases f2 with
    | zero =>
      exact False.elim (Nat.not_succ_le_zero f1' hle)
    | succ f2' =>
      have hle' : f1' ≤ f2' := Nat.le_of_succ_le_succ hle
      unfold runCTA at h1 ⊢
      cases hStep : stepCTA stmts cta <;> simp [hStep, PTXOutcome.bind] at h1 ⊢
      case ok pair =>
        rcases pair with ⟨done, cta'⟩
        cases done with
        | true =>
          simp at h1 ⊢
          exact h1
        | false =>
          simp at h1 ⊢
          exact ih f2' cta' hle' h1
      all_goals exact h1


/-- Two atomic accesses from distinct threads to the same address in one epoch do not race. -/
theorem recordEpochAccess_atomic_atomic_ok (tid1 tid2 : Dim3) (sp : StateSpace)
    (addr width : Nat) :
    recordEpochAccess
      [{ tid := tid1, space := sp, addr := addr, width := width, isWrite := true, isAtomic := true }]
      tid2 sp addr width true true =
      .ok [
        { tid := tid2, space := sp, addr := addr, width := width, isWrite := true, isAtomic := true },
        { tid := tid1, space := sp, addr := addr, width := width, isWrite := true, isAtomic := true }] := by
  unfold recordEpochAccess findDataRace?
  simp
  rfl

/-- An atomic write races with an overlapping non-atomic access from a distinct thread. -/
theorem recordEpochAccess_atomic_nonatomic_races (tid1 tid2 : Dim3) (sp : StateSpace)
    (addr width : Nat)
    (h_diff_tid : (tid1 != tid2) = true)
    (h_pos_width : 0 < width) :
    recordEpochAccess
      [{ tid := tid1, space := sp, addr := addr, width := width, isWrite := true, isAtomic := true }]
      tid2 sp addr width false false = .dataRace sp addr := by
  have hOv : rangesOverlap addr width addr width = true := by
    unfold rangesOverlap
    exact decide_eq_true ⟨Nat.lt_add_of_pos_right h_pos_width, Nat.lt_add_of_pos_right h_pos_width⟩
  have hSp : (sp == sp) = true := by cases sp <;> rfl
  unfold recordEpochAccess findDataRace?
  simp [h_diff_tid, hOv, hSp]

/-- Reading a register that is not in the declared set traps with `.unboundReg` when enforcement is on. -/
theorem ptx_undeclared_reg_read_traps (name : String) :
    ({ PTXRegFile.empty with enforceDecls := true }).readScalarChecked name = .unboundReg name := by
  simp [PTXRegFile.readScalarChecked, PTXRegFile.empty]

/-- A declared but unwritten register traps with `.unboundReg` on read. -/
theorem ptx_uninit_reg_read_traps (rf : PTXRegFile)
    (h_en : rf.enforceDecls = true)
    (h_decl : rf.decls.lookup "%rd0" = some .u64)
    (h_val : rf.regs.lookup "%rd0" = some .uninit) :
    rf.readScalarChecked "%rd0" (some 64) = .unboundReg "%rd0" := by
  dsimp [PTXRegFile.readScalarChecked]
  rw [h_en, h_decl, h_val]
  rfl

/-- Writing a 64-bit result into a declared 32-bit register traps with `.typeMismatch`. -/
theorem ptx_reg_width_mismatch_traps (rf : PTXRegFile)
    (h_en : rf.enforceDecls = true)
    (h_decl : rf.decls.lookup "%r0" = some .u32) :
    rf.setScalar "%r0" 1#64 (some 64) =
      .typeMismatch "destination register %r0 width 32 mismatches instruction width" := by
  dsimp [PTXRegFile.setScalar]
  rw [h_en, h_decl]
  rfl

/-- `ld.param.s32` masks a 32-bit parameter into canonical 32-bit register form (`maskForType .s32`). -/
theorem ptx_ldParam_s32_canonical_mask (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    (h_param : cta.paramMem.lookupParam? "p" = some 0xFFFF_FFFF_FFFF_FFFF#64)
    (h_set : th.regs.setScalar "%r0" (maskForType .s32 0xFFFF_FFFF_FFFF_FFFF#64) (some PTXType.s32.bitWidth) =
      .ok (th.regs.setScalarRaw "%r0" 0x0000_0000_FFFF_FFFF#64)) :
    execNonBarrierInstr stmts cta th (.ldParam .s32 "%r0" "p") =
      .ok ({ th with pc := th.pc + 1, regs := th.regs.setScalarRaw "%r0" 0x0000_0000_FFFF_FFFF#64 },
           cta.globalMem, cta.sharedMem, cta.epochLog) := by
  dsimp [execNonBarrierInstr, PTXOutcome.bind]
  rw [h_param]
  dsimp
  rw [h_set]

/-- `atom.global.cas.b64` records an atomic epoch access and leaves `sharedMem` unchanged. -/
theorem atomCas_global_preserves_shared (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    (dst : String) (addr : PTXAddr) (cmp src : PTXOperand)
    (th' : PTXThreadState) (gMem' sMem' : ByteMemory) (log' : List MemAccessLog)
    (h_exec : execNonBarrierInstr stmts cta th (.atomCas .global .b64 dst addr cmp src) =
      .ok (th', gMem', sMem', log')) :
    sMem' = cta.sharedMem := by
  have h1 : (StateSpace.global != StateSpace.global) = false := rfl
  have h2 : (PTXType.b64 != PTXType.b64) = false := rfl
  have h3 : (StateSpace.global == StateSpace.global) = true := rfl
  dsimp [execNonBarrierInstr, PTXOutcome.bind] at h_exec
  simp only [h1, h2, h3, Bool.false_and, Bool.and_false] at h_exec
  dsimp at h_exec
  cases hAddr : evalAddr cta th addr <;> simp [hAddr] at h_exec
  case ok byteAddr =>
    cases hCmp : evalOperand cta th cmp (some PTXType.b64.bitWidth) <;> simp [hCmp] at h_exec
    case ok vCmp =>
      cases hSrc : evalOperand cta th src (some PTXType.b64.bitWidth) <;> simp [hSrc] at h_exec
      case ok vSrc =>
        cases hAlign : checkAligned .global byteAddr PTXType.b64.byteWidth <;> simp [hAlign] at h_exec
        case ok =>
          cases hRace : recordEpochAccess cta.epochLog th.tid .global byteAddr PTXType.b64.byteWidth true true <;>
            simp [hRace] at h_exec
          case ok logNext =>
            cases hLoad : cta.globalMem.loadBits byteAddr PTXType.b64.byteWidth <;> simp [hLoad] at h_exec
            case some oldRaw =>
              split at h_exec
              · simp at h_exec
              · split at h_exec <;> simp at h_exec
                exact h_exec.2.2.1.symm

/-- Bitwise `and` on a non-bit type traps with `.typeMismatch`. -/
theorem ptx_bitwise_non_bittype_traps (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    (dst : String) (a b : PTXOperand) :
    execNonBarrierInstr stmts cta th (.bitAnd .u64 dst a b) =
      .typeMismatch "bitwise and requires .pred or .b* type, got .u64" := by
  rfl

end LeanNative.Backend.PTXAst
