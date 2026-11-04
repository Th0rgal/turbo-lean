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

/-! ## 5. Track `D6` — barrier generations and axiomatic weak memory -/

/-- `stepCTABarrierGen` succeeds when every thread in the CTA either arrives at active `bar.sync bid`
    or has already legally exited via `ret`: active participants advance `pc + 1`, `ret`-exited
    threads remain halted at their exit PC, `epochLog` clears, and `barrierGen` bumps `bid`. -/
theorem stepCTABarrier_allows_ret_exited_threads (stmts : List PTXStmt) (bid : Nat)
    (thRet thBar : PTXThreadState) (cta : PTXCTAState)
    (hThreads : cta.threads = [thRet, thBar])
    (hRet : threadExitedByRet stmts thRet = true)
    (hBarUnhalted : thBar.halted = false) :
    stepCTABarrierGen stmts bid [none, some bid] cta =
      .ok { cta with
        threads := [thRet, { thBar with pc := thBar.pc + 1 }]
        epochLog := []
        barrierGen := bumpBarrierGen cta.barrierGen bid } ∧
      (evalPTXKernel 32
        { name := "early_ret_bar_sync"
        , params := [ { ty := .u64, name := "out" } ]
        , regDecls := [ { ty := .u32, prefixName := "%r", count := 1 }
                      , { ty := .u64, prefixName := "%rd", count := 1 }
                      , { ty := .pred, prefixName := "%p", count := 1 } ]
        , body :=
            [ .instr none (.mov .u32 "%r0" (.sreg .tidX))
            , .instr none (.setp .eq .u32 "%p0" (.reg "%r0") (.immU64 0#64))
            , .instr (some { predReg := "%p0" }) .ret
            , .instr none (.barSync 0)
            , .instr none (.ldParam .u64 "%rd0" "out")
            , .instr none (.stGlobal .u64 (.regOffset "%rd0" 0) (.immU64 99#64))
            , .instr none .ret ] }
        { x := 1 } { x := 2 }
        (ByteMemory.ofU64Words [ 0#64 ])
        { params := [ ("out", 0#64) ] } =
        .ok (ByteMemory.ofU64Words [ 99#64 ])) := by
  refine ⟨?_, rfl⟩
  unfold stepCTABarrierGen
  rw [hThreads]
  simp [barrierParticipantsConverged, advanceBarrierParticipants, hRet, hBarUnhalted]

/-- Divergent barrier IDs (`b1 ≠ b2`) across active CTA threads trap with `.barrierDivergence b1`. -/
theorem stepCTABarrier_divergent_barriers_trap (stmts : List PTXStmt) (b1 b2 : Nat)
    (th1 th2 : PTXThreadState) (cta : PTXCTAState)
    (hNe : b1 ≠ b2)
    (hThreads : cta.threads = [th1, th2]) :
    stepCTABarrierGen stmts b1 [some b1, some b2] cta = .barrierDivergence b1 := by
  have hBeqFalse : (b2 == b1) = false := beq_false_of_ne hNe.symm
  unfold stepCTABarrierGen
  rw [hThreads]
  simp [barrierParticipantsConverged, hBeqFalse]

private theorem lookup_bumpBarrierGen_same (gens : List (Nat × Nat)) (bid : Nat) :
    lookupBarrierEpoch (bumpBarrierGen gens bid) bid = lookupBarrierEpoch gens bid + 1 := by
  induction gens with
  | nil =>
    simp [bumpBarrierGen, lookupBarrierEpoch]
  | cons hd rest ih =>
    rcases hd with ⟨b, g⟩
    by_cases hb : b == bid
    · simp [bumpBarrierGen, lookupBarrierEpoch, hb]
    · simp [bumpBarrierGen, lookupBarrierEpoch, hb, ih]

/-- Converging on `bar.sync bid` increments `bid`'s barrier generation counter by `1` and clears
    `epochLog` to open a fresh data-race-free barrier generation. -/
theorem stepCTABarrier_advances_generation_and_clears_epoch (stmts : List PTXStmt) (bid : Nat)
    (states : List (Option Nat)) (cta : PTXCTAState)
    (hConv : barrierParticipantsConverged stmts bid cta.threads states = true) :
    ∃ cta' : PTXCTAState,
      stepCTABarrierGen stmts bid states cta = .ok cta' ∧
      cta'.epochLog = [] ∧
      lookupBarrierEpoch cta'.barrierGen bid = lookupBarrierEpoch cta.barrierGen bid + 1 := by
  refine ⟨{ cta with
    threads := advanceBarrierParticipants bid cta.threads states
    epochLog := []
    barrierGen := bumpBarrierGen cta.barrierGen bid }, ?_, rfl, ?_⟩
  · unfold stepCTABarrierGen
    simp [hConv]
  · exact lookup_bumpBarrierGen_same cta.barrierGen bid

private theorem foldl_atomAddDeltas_shift (xs : List PTXMemEvent) (base : BitVec 64) :
    xs.foldl (fun acc e => acc + (e.valWritten - e.valRead)) base =
      base + sumAtomAddDeltas xs := by
  induction xs generalizing base with
  | nil =>
    simp [sumAtomAddDeltas]
  | cons x rest ih =>
    unfold sumAtomAddDeltas at ih ⊢
    simp only [List.foldl_cons, BitVec.zero_add]
    rw [ih (base + (x.valWritten - x.valRead)), ih (x.valWritten - x.valRead)]
    ac_rfl

private theorem sumAtomAddDeltas_cons (x : PTXMemEvent) (xs : List PTXMemEvent) :
    sumAtomAddDeltas (x :: xs) = (x.valWritten - x.valRead) + sumAtomAddDeltas xs := by
  unfold sumAtomAddDeltas
  simp only [List.foldl_cons, BitVec.zero_add]
  exact foldl_atomAddDeltas_shift xs (x.valWritten - x.valRead)

private theorem bv64_add_sub_cancel_left (a d : BitVec 64) :
    a + (d - a) = d := by
  have h1 : a + (d - a) = d + (a + -a) := by
    rw [BitVec.sub_eq_add_neg]
    ac_rfl
  rw [h1, BitVec.add_right_neg, BitVec.add_zero]

private theorem atomAddChain_telescope :
    ∀ (chain : List PTXMemEvent) (initVal : BitVec 64) (hNe : chain ≠ []),
      (chain.head hNe).valRead = initVal →
      (∀ (xs : List PTXMemEvent) (a b : PTXMemEvent) (ys : List PTXMemEvent),
        chain = xs ++ a :: b :: ys → a.valWritten = b.valRead) →
      (chain.getLast hNe).valWritten = initVal + sumAtomAddDeltas chain
  | [], _, hNe, _, _ => absurd rfl hNe
  | [hd], initVal, _, hHead, _ => by
    simp only [List.head_cons, List.getLast_singleton] at hHead ⊢
    rw [sumAtomAddDeltas_cons]
    simp only [sumAtomAddDeltas, List.foldl_nil, BitVec.add_zero, hHead]
    exact (bv64_add_sub_cancel_left initVal hd.valWritten).symm
  | hd :: m :: rest, initVal, _, hHead, hAdj => by
    simp only [List.head_cons, List.getLast_cons_cons] at hHead ⊢
    have hAdjHead : hd.valWritten = m.valRead :=
      hAdj [] hd m rest rfl
    have hAdjTail : ∀ (xs : List PTXMemEvent) (a b : PTXMemEvent) (ys : List PTXMemEvent),
        m :: rest = xs ++ a :: b :: ys → a.valWritten = b.valRead := by
      intro xs a b ys hEq
      exact hAdj (hd :: xs) a b ys (by simp [hEq])
    have ih := atomAddChain_telescope (m :: rest) hd.valWritten (by simp)
      (by simp [hAdjHead]) hAdjTail
    rw [ih, sumAtomAddDeltas_cons hd (m :: rest), ← hHead]
    have hAssoc : hd.valRead + ((hd.valWritten - hd.valRead) + sumAtomAddDeltas (m :: rest)) =
        (hd.valRead + (hd.valWritten - hd.valRead)) + sumAtomAddDeltas (m :: rest) := by
      ac_rfl
    rw [hAssoc, bv64_add_sub_cancel_left]

private theorem find_eventId_mem_and_eq :
    ∀ {evs : List PTXMemEvent} {eid : Nat} {ev : PTXMemEvent},
      evs.find? (fun e => e.eventId == eid) = some ev →
      ev ∈ evs ∧ ev.eventId = eid
  | [], _, _, h => nomatch h
  | hd :: tl, eid, ev, h => by
    unfold List.find? at h
    cases hb : hd.eventId == eid
    · rw [hb] at h
      rcases find_eventId_mem_and_eq h with ⟨hMem, hEq⟩
      exact ⟨List.Mem.tail _ hMem, hEq⟩
    · rw [hb] at h
      cases h
      exact ⟨List.Mem.head _, LawfulBEq.eq_of_beq hb⟩

private theorem hasEvent_mem_of_some {cand : PTXCandidateExecution} {eid : Nat} {ev : PTXMemEvent}
    (h : cand.hasEvent eid = some ev) :
    ev ∈ cand.events ∧ ev.eventId = eid :=
  find_eventId_mem_and_eq h

private theorem hasEvent_eq_self_of_nodup {evs : List PTXMemEvent}
    (hNodup : (evs.map PTXMemEvent.eventId).Nodup) :
    ∀ {e : PTXMemEvent}, e ∈ evs → evs.find? (fun x => x.eventId == e.eventId) = some e := by
  induction evs with
  | nil =>
    intro _ hMem
    nomatch hMem
  | cons hd tl ih =>
    rcases List.nodup_cons.mp hNodup with ⟨hNotMem, hTlNodup⟩
    intro e hMem
    rcases List.mem_cons.mp hMem with rfl | hInTl
    · simp
    · have hNe : hd.eventId ≠ e.eventId := by
        intro hEq
        exact hNotMem (hEq ▸ List.mem_map_of_mem hInTl)
      have hBeqFalse : (hd.eventId == e.eventId) = false := beq_false_of_ne hNe
      simp [List.find?, hBeqFalse, ih hTlNodup hInTl]

private theorem isImmediateCoChain_tail {cand : PTXCandidateExecution}
    {a b : PTXMemEvent} {rest : List PTXMemEvent}
    (h : isImmediateCoChain cand (a :: b :: rest)) :
    cand.co a.eventId b.eventId ∧
      (¬ ∃ wMid : Nat, cand.co a.eventId wMid ∧ cand.co wMid b.eventId) ∧
      isImmediateCoChain cand (b :: rest) :=
  h

private theorem sameLoc_symm {e1 e2 : PTXMemEvent}
    (h : PTXCandidateExecution.sameLoc e1 e2) :
    PTXCandidateExecution.sameLoc e2 e1 := by
  rcases h with ⟨hs, ha, hw, hg | ⟨hsh, hcta⟩⟩
  · exact ⟨hs.symm, ha.symm, hw.symm, Or.inl (hs.symm.trans hg)⟩
  · exact ⟨hs.symm, ha.symm, hw.symm, Or.inr ⟨hs.symm.trans hsh, hcta.symm⟩⟩

private theorem sameLoc_trans {e1 e2 e3 : PTXMemEvent}
    (h12 : PTXCandidateExecution.sameLoc e1 e2)
    (h23 : PTXCandidateExecution.sameLoc e2 e3) :
    PTXCandidateExecution.sameLoc e1 e3 := by
  rcases h12 with ⟨hs1, ha1, hw1, hg1 | ⟨hsh1, hcta1⟩⟩
  · rcases h23 with ⟨hs2, ha2, hw2, _⟩
    exact ⟨hs1.trans hs2, ha1.trans ha2, hw1.trans hw2, Or.inl hg1⟩
  · rcases h23 with ⟨hs2, ha2, hw2, hg2 | ⟨_, hcta2⟩⟩
    · rw [hs1] at hsh1
      rw [hg2] at hsh1
      nomatch hsh1
    · exact ⟨hs1.trans hs2, ha1.trans ha2, hw1.trans hw2, Or.inr ⟨hsh1, hcta1.trans hcta2⟩⟩

private theorem adj_valWritten_eq_valRead_of_consistent
    {initMem : Nat → StateSpace → Nat → Option (BitVec 64)}
    {cand : PTXCandidateExecution}
    (hCons : PTXAxiomaticConsistent initMem cand)
    (chain : List PTXMemEvent)
    (hSub : ∀ e ∈ chain, e ∈ cand.events ∧ e.isAtomic = true ∧ e.isRead = true ∧ e.isWrite = true)
    (hImm : isImmediateCoChain cand chain) :
    ∀ (xs : List PTXMemEvent) (a b : PTXMemEvent) (ys : List PTXMemEvent),
      chain = xs ++ a :: b :: ys → a.valWritten = b.valRead := by
  induction chain with
  | nil =>
    intro xs a b ys hEq
    cases xs <;> nomatch hEq
  | cons hd tl ih =>
    intro xs a b ys hEq
    cases xs with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hEq
      rcases hEq with ⟨hHdEq, hTlEq⟩
      rw [hHdEq, hTlEq] at hImm hSub
      rcases isImmediateCoChain_tail hImm with ⟨hCoAB, hNoMid, _⟩
      rcases hSub a (List.Mem.head _) with ⟨hMemA, _, _, _⟩
      rcases hSub b (List.Mem.tail _ (List.Mem.head _)) with ⟨hMemB, hAtB, hRdB, hWrB⟩
      rcases hCons.rmw_atomicity b hMemB hAtB hRdB hWrB with ⟨hRmwRf, hRmwNoRf⟩
      rcases hCons.rf_complete b hMemB hRdB with ⟨w, hRfWB, _⟩ | ⟨hNoRf, _⟩
      · rcases hRmwRf hRfWB with ⟨hCoWB, hNoMidWB⟩
        rcases hCons.rf_wf hRfWB with ⟨ew, eb, hHasW, hHasB, hWrW, _, hSameWB, hValEq, _⟩
        rcases hCons.co_wf hCoAB with ⟨ea', eb', hHasA', hHasB', hWrA', _, hSameAB, _⟩
        have hFindA : cand.hasEvent a.eventId = some a :=
          hasEvent_eq_self_of_nodup hCons.eventIds_nodup hMemA
        have hFindB : cand.hasEvent b.eventId = some b :=
          hasEvent_eq_self_of_nodup hCons.eventIds_nodup hMemB
        have hEqA : ea' = a := Option.some.inj (hHasA'.symm.trans hFindA)
        have hEqB1 : eb = b := Option.some.inj (hHasB.symm.trans hFindB)
        have hEqB2 : eb' = b := Option.some.inj (hHasB'.symm.trans hFindB)
        rw [hEqA, hEqB2] at hSameAB
        rw [hEqA] at hWrA'
        rw [hEqB1] at hSameWB hValEq
        rcases hasEvent_mem_of_some hHasW with ⟨hMemW, hWidEq⟩
        by_cases hWA : a.eventId = w
        · have hHasAW : cand.hasEvent w = some a := hWA ▸ hFindA
          have hEwEqA : ew = a := Option.some.inj (hHasW.symm.trans hHasAW)
          rw [← hEwEqA]
          exact hValEq
        · have hSameAW : PTXCandidateExecution.sameLoc a ew :=
            sameLoc_trans hSameAB (sameLoc_symm hSameWB)
          have hAwNe : a.eventId ≠ ew.eventId := by rw [hWidEq]; exact hWA
          rcases hCons.co_total a ew hMemA hMemW hWrA' hWrW hSameAW hAwNe with hCoAW | hCoWA
          · rw [hWidEq] at hCoAW
            exact False.elim (hNoMid ⟨w, hCoAW, hCoWB⟩)
          · rw [hWidEq] at hCoWA
            exact False.elim (hNoMidWB ⟨a.eventId, hCoWA, hCoAB⟩)
      · exact False.elim (hRmwNoRf hNoRf ⟨a.eventId, hCoAB⟩)
    | cons x xs' =>
      simp only [List.cons_append, List.cons.injEq] at hEq
      rcases hEq with ⟨_, hTlEq⟩
      cases tl with
      | nil => cases xs' <;> nomatch hTlEq
      | cons t2 tl' =>
        rcases isImmediateCoChain_tail hImm with ⟨_, _, hImmTl⟩
        exact ih (fun e he => hSub e (List.Mem.tail _ he)) hImmTl xs' a b ys hTlEq

/-- Relaxed cross-CTA `atom.add.global.u64` coherence & commutativity (`D6`):
    in any `PTXAxiomaticConsistent` execution `cand`, for every non-empty immediate-`co`-ordered
    chain `chain` of atomic RMW events whose head has no prior `co` store to that location (so
    RMW atomicity + `rf_complete` force the head to read `initVal` from `initMem`), no update is
    ever lost: the final event's `valWritten` equals `initVal + sumAtomAddDeltas chain` modulo
    `2^64`, regardless of CTA scheduling order. -/
theorem ptx_relaxed_atom_add_co_no_lost_updates
    (initMem : Nat → StateSpace → Nat → Option (BitVec 64))
    (cand : PTXCandidateExecution)
    (hCons : PTXAxiomaticConsistent initMem cand)
    (chain : List PTXMemEvent) (hNe : chain ≠ [])
    (initVal : BitVec 64)
    (hSub : ∀ e ∈ chain, e ∈ cand.events ∧ e.isAtomic = true ∧ e.isRead = true ∧ e.isWrite = true)
    (hImm : isImmediateCoChain cand chain)
    (hHeadInit : initMem (chain.head hNe).addr (chain.head hNe).space (chain.head hNe).width =
      some initVal)
    (hHeadFirst : ¬ ∃ wPre : Nat, cand.co wPre (chain.head hNe).eventId) :
    (chain.getLast hNe).valWritten = initVal + sumAtomAddDeltas chain := by
  let hd := chain.head hNe
  rcases hSub hd (List.head_mem hNe) with ⟨hMemHd, hAtHd, hRdHd, hWrHd⟩
  rcases hCons.rmw_atomicity hd hMemHd hAtHd hRdHd hWrHd with ⟨hRmwRf, _⟩
  have hHdValRead : hd.valRead = initVal := by
    rcases hCons.rf_complete hd hMemHd hRdHd with ⟨w, hRfWHd, _⟩ | ⟨_, hInitEq⟩
    · rcases hRmwRf hRfWHd with ⟨hCoWHd, _⟩
      exact False.elim (hHeadFirst ⟨w, hCoWHd⟩)
    · exact Option.some.inj (hInitEq.symm.trans hHeadInit)
  have hAdj := adj_valWritten_eq_valRead_of_consistent hCons chain hSub hImm
  exact atomAddChain_telescope chain initVal hNe hHdValRead hAdj

/-- Concrete cross-CTA relaxed `atom.add.global.u64` non-vacuity & commutativity witness (`D6`):
    two CTAs atomically adding `19#64` and `23#64` to `.global` address `0` (initialized to `5#64`)
    under both sequential CTA order `(CTA 0 -> CTA 1)` and reversed read-oracle order
    `(CTA 1 -> CTA 0)` both converge to `5#64 + 19#64 + 23#64 = 47#64` with `0` UB/data-race traps. -/
theorem ptx_relaxed_cross_cta_atom_add_commutes :
    let k : PTXKernel :=
      { name := "cross_cta_atom_add"
      , params := [ { ty := .u64, name := "acc" } ]
      , regDecls := [ { ty := .u32, prefixName := "%r", count := 1 }
                    , { ty := .u64, prefixName := "%rd", count := 3 }
                    , { ty := .pred, prefixName := "%p", count := 1 } ]
      , body :=
          [ .instr none (.mov .u32 "%r0" (.sreg .ctaidX))
          , .instr none (.setp .eq .u32 "%p0" (.reg "%r0") (.immU64 0#64))
          , .instr none (.selp .u64 "%rd1" (.immU64 19#64) (.immU64 23#64) "%p0")
          , .instr none (.ldParam .u64 "%rd0" "acc")
          , .instr none (.atomAdd .global .u64 "%rd2" (.regOffset "%rd0" 0) (.reg "%rd1"))
          , .instr none .ret ] }
    let g0 := ByteMemory.ofU64Words [ 5#64 ]
    let revOracle : PTXReadOracle := fun ctaId _ ord sp addr width =>
      if sp == .global && addr == 0 && width == 8 && ord == 0 then
        if ctaId.x == 0 then some 28#64 else some 5#64
      else
        none
    (∃ gSeq evsSeq,
      evalPTXKernelWithOracle none 32 k { x := 2 } { x := 1 } g0
        { params := [ ("acc", 0#64) ] } = .ok (gSeq, evsSeq) ∧
      gSeq.loadBits 0 8 = some 47#64 ∧
      sumAtomAddDeltas evsSeq = 42#64) ∧
    (∃ gRev evsRev,
      evalPTXKernelWithOracle (some revOracle) 32 k { x := 2 } { x := 1 } g0
        { params := [ ("acc", 0#64) ] } = .ok (gRev, evsRev) ∧
      sumAtomAddDeltas evsRev = 42#64 ∧
      5#64 + sumAtomAddDeltas evsRev = 47#64) := by
  exact ⟨⟨_, _, rfl, rfl, rfl⟩, ⟨_, _, rfl, rfl, rfl⟩⟩

/-- Inter-kernel sequential host-stream visibility (`D6`):
    in any `PTXAxiomaticConsistent` execution `cand`, if kernel `k_i` (`ew.kernelIdx < er.kernelIdx`)
    writes `ew.valWritten` to `.global` location `(addr, width)`, no other write to that location
    intervenes (`co`-maximality of `ew`), and kernel `k_j` reads that location in `er`, then
    inter-kernel `sw` (`ew →_sw er`, hence `ew →_hb er`) and `fr`/`coh_rw` coherence force
    `er.valRead = ew.valWritten`. -/
theorem ptx_seq_kernel_global_write_visible
    (initMem : Nat → StateSpace → Nat → Option (BitVec 64))
    (cand : PTXCandidateExecution)
    (hCons : PTXAxiomaticConsistent initMem cand)
    (ew er : PTXMemEvent)
    (hMemW : ew ∈ cand.events) (hMemR : er ∈ cand.events)
    (hSpW : ew.space = .global) (hSpR : er.space = .global)
    (hWrW : ew.isWrite = true) (hRdR : er.isRead = true)
    (hAddr : ew.addr = er.addr) (hWidth : ew.width = er.width)
    (hKernLt : ew.kernelIdx < er.kernelIdx)
    (hCoMax : ¬ ∃ wPost : Nat, cand.co ew.eventId wPost) :
    cand.sw ew.eventId er.eventId ∧ er.valRead = ew.valWritten := by
  have hSw : cand.sw ew.eventId er.eventId :=
    hCons.sw_inter_kernel ew er hMemW hMemR hSpW hSpR hWrW hKernLt
  have hHb : cand.hb ew.eventId er.eventId :=
    PTXHappensBefore.single (Or.inr hSw)
  refine ⟨hSw, ?_⟩
  have hFindW : cand.hasEvent ew.eventId = some ew :=
    hasEvent_eq_self_of_nodup hCons.eventIds_nodup hMemW
  have hFindR : cand.hasEvent er.eventId = some er :=
    hasEvent_eq_self_of_nodup hCons.eventIds_nodup hMemR
  have hNeId : er.eventId ≠ ew.eventId := by
    intro hEq
    have hEvEq : er = ew := Option.some.inj (hFindR.symm.trans (hEq ▸ hFindW))
    rw [hEvEq] at hKernLt
    exact Nat.lt_irrefl _ hKernLt
  have hSameRW : PTXCandidateExecution.sameLoc er ew :=
    ⟨hSpR.trans hSpW.symm, hAddr.symm, hWidth.symm, Or.inl hSpR⟩
  rcases hCons.rf_complete er hMemR hRdR with ⟨w0, hRf0, _⟩ | ⟨hNoRf, _⟩
  · rcases hCons.rf_wf hRf0 with ⟨ew0, er0, hHasW0, hHasR0, hWrW0, _, hSame0R, hVal0, _⟩
    have hEr0Eq : er0 = er := Option.some.inj (hHasR0.symm.trans hFindR)
    rw [hEr0Eq] at hSame0R hVal0
    rcases hasEvent_mem_of_some hHasW0 with ⟨hMemW0, hW0Id⟩
    by_cases hEqW : w0 = ew.eventId
    · have hHasWW0 : cand.hasEvent w0 = some ew := hEqW ▸ hFindW
      have hEw0Eq : ew0 = ew := Option.some.inj (hHasW0.symm.trans hHasWW0)
      rw [hEw0Eq] at hVal0
      exact hVal0.symm
    · have hSame0W : PTXCandidateExecution.sameLoc ew0 ew :=
        sameLoc_trans hSame0R hSameRW
      have hNe0W : ew0.eventId ≠ ew.eventId := by rw [hW0Id]; exact hEqW
      rcases hCons.co_total ew0 ew hMemW0 hMemW hWrW0 hWrW hSame0W hNe0W with hCo0W | hCoW0
      · rw [hW0Id] at hCo0W
        have hFr : cand.fr er.eventId ew.eventId := Or.inl ⟨w0, hRf0, hCo0W⟩
        exact False.elim (hCons.coh_rw hFr hHb)
      · exact False.elim (hCoMax ⟨ew0.eventId, hCoW0⟩)
  · have hFr : cand.fr er.eventId ew.eventId :=
      Or.inr ⟨hNoRf, er, ew, hFindR, hFindW, hRdR, hWrW, hSameRW, hNeId⟩
    exact False.elim (hCons.coh_rw hFr hHb)

/-- Intra-CTA `bar.sync` generation release-acquire visibility (`D6`):
    in any `PTXAxiomaticConsistent` execution `cand`, if thread `ew.tid` in `(kernelIdx, ctaId)`
    writes `ew.valWritten` to `.shared` or `.global` location `(addr, width)` before barrier `bid`
    advances (`lookupBarrierEpoch ew.barrierEpoch bid < lookupBarrierEpoch er.barrierEpoch bid`),
    no later store overwrites that location (`co`-maximality of `ew`), and distinct thread `er.tid`
    in the same CTA reads that location after `bar.sync bid`, then `ew →_sw er` and
    `er.valRead = ew.valWritten`. -/
theorem ptx_cta_barrier_gen_write_visible
    (initMem : Nat → StateSpace → Nat → Option (BitVec 64))
    (cand : PTXCandidateExecution)
    (hCons : PTXAxiomaticConsistent initMem cand)
    (ew er : PTXMemEvent) (bid : Nat)
    (hMemW : ew ∈ cand.events) (hMemR : er ∈ cand.events)
    (hKern : ew.kernelIdx = er.kernelIdx) (hCta : ew.ctaId = er.ctaId)
    (hDiffTid : ew.tid ≠ er.tid)
    (hGenLt : lookupBarrierEpoch ew.barrierEpoch bid < lookupBarrierEpoch er.barrierEpoch bid)
    (hSameLoc : PTXCandidateExecution.sameLoc er ew)
    (hWrW : ew.isWrite = true) (hRdR : er.isRead = true)
    (hCoMax : ¬ ∃ wPost : Nat, cand.co ew.eventId wPost) :
    cand.sw ew.eventId er.eventId ∧ er.valRead = ew.valWritten := by
  have hSw : cand.sw ew.eventId er.eventId :=
    hCons.sw_cta_barrier ew er bid hMemW hMemR hKern hCta hDiffTid hGenLt
  have hHb : cand.hb ew.eventId er.eventId :=
    PTXHappensBefore.single (Or.inr hSw)
  refine ⟨hSw, ?_⟩
  have hFindW : cand.hasEvent ew.eventId = some ew :=
    hasEvent_eq_self_of_nodup hCons.eventIds_nodup hMemW
  have hFindR : cand.hasEvent er.eventId = some er :=
    hasEvent_eq_self_of_nodup hCons.eventIds_nodup hMemR
  have hNeId : er.eventId ≠ ew.eventId := by
    intro hEq
    have hEvEq : er = ew := Option.some.inj (hFindR.symm.trans (hEq ▸ hFindW))
    rw [hEvEq] at hDiffTid
    exact hDiffTid rfl
  rcases hCons.rf_complete er hMemR hRdR with ⟨w0, hRf0, _⟩ | ⟨hNoRf, _⟩
  · rcases hCons.rf_wf hRf0 with ⟨ew0, er0, hHasW0, hHasR0, hWrW0, _, hSame0R, hVal0, _⟩
    have hEr0Eq : er0 = er := Option.some.inj (hHasR0.symm.trans hFindR)
    rw [hEr0Eq] at hSame0R hVal0
    rcases hasEvent_mem_of_some hHasW0 with ⟨hMemW0, hW0Id⟩
    by_cases hEqW : w0 = ew.eventId
    · have hHasWW0 : cand.hasEvent w0 = some ew := hEqW ▸ hFindW
      have hEw0Eq : ew0 = ew := Option.some.inj (hHasW0.symm.trans hHasWW0)
      rw [hEw0Eq] at hVal0
      exact hVal0.symm
    · have hSame0W : PTXCandidateExecution.sameLoc ew0 ew :=
        sameLoc_trans hSame0R hSameLoc
      have hNe0W : ew0.eventId ≠ ew.eventId := by rw [hW0Id]; exact hEqW
      rcases hCons.co_total ew0 ew hMemW0 hMemW hWrW0 hWrW hSame0W hNe0W with hCo0W | hCoW0
      · rw [hW0Id] at hCo0W
        have hFr : cand.fr er.eventId ew.eventId := Or.inl ⟨w0, hRf0, hCo0W⟩
        exact False.elim (hCons.coh_rw hFr hHb)
      · exact False.elim (hCoMax ⟨ew0.eventId, hCoW0⟩)
  · have hFr : cand.fr er.eventId ew.eventId :=
      Or.inr ⟨hNoRf, er, ew, hFindR, hFindW, hRdR, hWrW, hSameLoc, hNeId⟩
    exact False.elim (hCons.coh_rw hFr hHb)

end LeanNative.Backend.PTXAst
