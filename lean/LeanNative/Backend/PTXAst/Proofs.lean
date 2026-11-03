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


/-! ## 5. SIMT Lowering Support Lemmas (`C3b`) -/

private def unDigit (c : Char) : Nat := c.toNat - '0'.toNat
private def parseDigits : List Char → Nat → Nat
  | [], acc => acc
  | c :: cs, acc => parseDigits cs (acc * 10 + unDigit c)

private theorem unDigit_digitChar (d : Nat) (h : d < 10) :
    unDigit (Nat.digitChar d) = d := by
  match d, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => rfl

private theorem parseDigits_toDigitsCore :
    ∀ (fuel n : Nat) (cs : List Char) (_ : n < fuel),
      parseDigits (Nat.toDigitsCore 10 fuel n cs) 0 = parseDigits cs n
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, n, cs, hfuel => by
    unfold Nat.toDigitsCore; dsimp only
    have hchar := unDigit_digitChar (n % 10) (Nat.mod_lt n (by decide))
    split
    · have hn : n = n % 10 := by omega
      simp [parseDigits, hchar]; rw [← hn]
    · rw [parseDigits_toDigitsCore fuel (n / 10) (Nat.digitChar (n % 10) :: cs) (by omega)]
      have hdiv : n / 10 * 10 + n % 10 = n := by omega
      simp [parseDigits, hchar, hdiv]

theorem nat_repr_inj (a b : Nat) (h : toString a = toString b) : a = b := by
  have h1 : (Nat.repr a).toList = (Nat.repr b).toList := congrArg String.toList h
  simp only [Nat.repr, String.toList_ofList, Nat.toDigits] at h1
  have ha := parseDigits_toDigitsCore (a + 1) a [] (Nat.lt_succ_self a)
  have hb := parseDigits_toDigitsCore (b + 1) b [] (Nat.lt_succ_self b)
  rw [h1] at ha; simpa [parseDigits] using ha.symm.trans hb

theorem regName_inj (pre : String) (a b : Nat)
    (h : s!"{pre}{a}" = s!"{pre}{b}") : a = b := by
  have h1 : (pre ++ toString a).toList = (pre ++ toString b).toList := congrArg String.toList h
  simp only [String.toList_append] at h1
  exact nat_repr_inj a b (String.ext_iff.mpr (List.append_cancel_left h1))

private theorem digit_head_isDigit (n : Nat) :
    ∃ c cs, (toString n).toList = c :: cs ∧ c ≠ 'd' := by
  have hd : (toString n).toList = Nat.toDigits 10 n := by
    change (Nat.repr n).toList = Nat.toDigits 10 n; simp [Nat.repr]
  rw [hd]; unfold Nat.toDigits Nat.toDigitsCore; dsimp only
  have hmod : n % 10 < 10 := Nat.mod_lt n (by decide)
  have hne : Nat.digitChar (n % 10) ≠ 'd' := by
    match h : n % 10, hmod with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => decide
  split
  · exact ⟨_, [], rfl, hne⟩
  · have haux : ∀ (f m : Nat) (acc : List Char), acc ≠ [] →
        ∃ c cs, Nat.toDigitsCore 10 f m acc = c :: cs ∧
          (c ∈ acc ∨ ∃ d < 10, c = Nat.digitChar d) := by
      intro f; induction f with
      | zero =>
        intro _ acc hacc; cases acc with
        | nil => contradiction
        | cons c cs => exact ⟨c, cs, rfl, Or.inl (List.Mem.head cs)⟩
      | succ f' ih =>
        intro m acc _; unfold Nat.toDigitsCore; dsimp only
        have hm10 : m % 10 < 10 := Nat.mod_lt m (by decide)
        split
        · exact ⟨_, acc, rfl, Or.inr ⟨m % 10, hm10, rfl⟩⟩
        · rcases ih (m / 10) (Nat.digitChar (m % 10) :: acc) (by simp) with ⟨c, cs, heq, hmem⟩
          refine ⟨c, cs, heq, ?_⟩
          rcases hmem with h1 | h2
          · rcases List.mem_cons.mp h1 with rfl | hrest
            · exact Or.inr ⟨m % 10, hm10, rfl⟩
            · exact Or.inl hrest
          · exact Or.inr h2
    rcases haux n (n / 10) [Nat.digitChar (n % 10)] (by simp) with ⟨c, cs, heq, hmem⟩
    refine ⟨c, cs, heq, ?_⟩
    rcases hmem with h1 | ⟨d, hd, rfl⟩
    · rw [List.mem_singleton.mp h1]; exact hne
    · match d, hd with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => decide

theorem p_ne_r (i j : Nat) : s!"%p{i}" ≠ s!"%r{j}" := by
  intro h; have h1 := congrArg String.toList h
  simp only [toString, String.toList_append] at h1
  change ('%' :: 'p' :: (toString i).toList) = ('%' :: 'r' :: (toString j).toList) at h1
  injection h1 with _ h2; injection h2 with hpr _
  exact absurd hpr (by decide)

theorem p_ne_rd (i j : Nat) : s!"%p{i}" ≠ s!"%rd{j}" := by
  intro h; have h1 := congrArg String.toList h
  simp only [toString, String.toList_append] at h1
  change ('%' :: 'p' :: (toString i).toList) = ('%' :: 'r' :: 'd' :: (toString j).toList) at h1
  injection h1 with _ h2; injection h2 with hpr _
  exact absurd hpr (by decide)

theorem r_ne_rd (i j : Nat) : s!"%r{i}" ≠ s!"%rd{j}" := by
  intro h; have h1 := congrArg String.toList h
  simp only [toString, String.toList_append] at h1
  change ('%' :: 'r' :: (toString i).toList) = ('%' :: 'r' :: 'd' :: (toString j).toList) at h1
  injection h1 with _ h2; injection h2 with _ h3
  rcases digit_head_isDigit i with ⟨c, cs, hci, hcne⟩
  rw [hci] at h3; injection h3 with hcd _
  exact hcne hcd

theorem setAssoc_lookup_self {α : Type} (xs : List (String × α)) (k : String) (v : α) :
    (PTXRegFile.setAssoc xs k v).lookup k = some v := by
  induction xs with
  | nil => simp [PTXRegFile.setAssoc]
  | cons kv rest ih =>
    rcases kv with ⟨k', v'⟩; simp only [PTXRegFile.setAssoc]
    cases hk : (k' == k)
    · have hsy : (k == k') = false := by
        cases hs : (k == k')
        · rfl
        · rw [eq_of_beq hs, beq_self_eq_true] at hk; cases hk
      simp [List.lookup, hsy, ih]
    · simp

theorem setAssoc_lookup_ne {α : Type} (xs : List (String × α)) (k q : String) (v : α)
    (hne : q ≠ k) :
    (PTXRegFile.setAssoc xs k v).lookup q = xs.lookup q := by
  induction xs with
  | nil => simp [PTXRegFile.setAssoc, List.lookup, beq_eq_false_iff_ne.mpr hne]
  | cons kv rest ih =>
    rcases kv with ⟨k', v'⟩; simp only [PTXRegFile.setAssoc]
    cases hk : (k' == k)
    · simp [List.lookup, ih]
    · rw [eq_of_beq hk]; simp [List.lookup, beq_eq_false_iff_ne.mpr hne]

theorem foldl_setAssoc_miss {α : Type} (pairs init : List (String × α)) (q : String)
    (hnm : q ∉ pairs.map Prod.fst) :
    (pairs.foldl (fun a (n, t) => PTXRegFile.setAssoc a n t) init).lookup q = init.lookup q := by
  induction pairs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.mem_cons, not_or] at hnm; simp only [List.foldl]
    rw [ih _ hnm.2, setAssoc_lookup_ne init x.1 q x.2 hnm.1]

theorem foldl_setAssoc_lookup {α : Type} (pairs init : List (String × α)) (q : String) (v : α)
    (hmem : (q, v) ∈ pairs) (hnodup : (pairs.map Prod.fst).Nodup) :
    (pairs.foldl (fun acc (nm, ty) => PTXRegFile.setAssoc acc nm ty) init).lookup q = some v := by
  induction pairs generalizing init with
  | nil => nomatch hmem
  | cons hd tl ih =>
    rcases hd with ⟨nm, ty⟩
    rw [List.map_cons, List.nodup_cons] at hnodup; rcases hnodup with ⟨hnotMem, hndTl⟩
    simp only [List.foldl]
    rcases List.mem_cons.mp hmem with heq | htl
    · injection heq with hq hv; subst hq hv
      rw [foldl_setAssoc_miss tl _ q hnotMem, setAssoc_lookup_self]
    · exact ih _ htl hndTl

def stdPTXRegDecls (nP nR nRd : Nat) : List PTXRegDecl :=
  [ { ty := .pred, prefixName := "%p", count := nP }
  , { ty := .u32, prefixName := "%r", count := nR }
  , { ty := .u64, prefixName := "%rd", count := nRd } ]

def RegTyped (rf : PTXRegFile) (nP nR nRd : Nat) : Prop :=
  rf.enforceDecls = true ∧
  (∀ i < nP, rf.decls.lookup s!"%p{i}" = some .pred) ∧
  (∀ i < nR, rf.decls.lookup s!"%r{i}" = some .u32) ∧
  (∀ i < nRd, rf.decls.lookup s!"%rd{i}" = some .u64)

private theorem nodup_map_regName (pre : String) (n : Nat) :
    ((List.range n).map fun i => s!"{pre}{i}").Nodup := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.nodup_append]
    refine ⟨ih, by simp, ?_⟩
    intro a ha b hb hab
    rcases List.mem_map.mp ha with ⟨ia, hia, rfl⟩
    rw [List.map_singleton, List.mem_singleton] at hb; subst hb
    have hEq := regName_inj pre ia m hab
    exact absurd hEq (Nat.ne_of_lt (List.mem_range.mp hia))

theorem ofRegDecls_regTyped (nP nR nRd : Nat) (hp : 0 < nP) (hr : 0 < nR) (hrd : 0 < nRd) :
    RegTyped (PTXRegFile.ofRegDecls (stdPTXRegDecls nP nR nRd)) nP nR nRd := by
  let lp := (List.range nP).map fun i => (s!"%p{i}", PTXType.pred)
  let lr := (List.range nR).map fun i => (s!"%r{i}", PTXType.u32)
  let lrd := (List.range nRd).map fun i => (s!"%rd{i}", PTXType.u64)
  have hexp : (stdPTXRegDecls nP nR nRd).flatMap PTXRegFile.expandSingleRegDecl =
      lp ++ (lr ++ lrd) := by
    have hp0 : (nP == 0) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hp)
    have hr0 : (nR == 0) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hr)
    have hrd0 : (nRd == 0) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hrd)
    simp [stdPTXRegDecls, PTXRegFile.expandSingleRegDecl, hp0, hr0, hrd0, lp, lr, lrd]
  have hnd : ((lp ++ (lr ++ lrd)).map Prod.fst).Nodup := by
    simp only [List.map_append, List.map_map, Function.comp_def, lp, lr, lrd]
    rw [List.nodup_append]
    refine ⟨nodup_map_regName "%p" nP, ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨nodup_map_regName "%r" nR, nodup_map_regName "%rd" nRd, ?_⟩
      intro a ha b hb hab
      rcases List.mem_map.mp ha with ⟨ia, _, rfl⟩
      rcases List.mem_map.mp hb with ⟨ib, _, rfl⟩
      exact r_ne_rd ia ib hab
    · intro a ha b hb hab
      rcases List.mem_map.mp ha with ⟨ia, _, rfl⟩
      rcases List.mem_append.mp hb with hbr | hbrd
      · rcases List.mem_map.mp hbr with ⟨ib, _, rfl⟩; exact p_ne_r ia ib hab
      · rcases List.mem_map.mp hbrd with ⟨ib, _, rfl⟩; exact p_ne_rd ia ib hab
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro i hi
    unfold PTXRegFile.ofRegDecls; dsimp only; rw [hexp]
    exact foldl_setAssoc_lookup _ [] _ _ (List.mem_append_left _ (List.mem_map_of_mem (List.mem_range.mpr hi))) hnd
  · intro i hi
    unfold PTXRegFile.ofRegDecls; dsimp only; rw [hexp]
    exact foldl_setAssoc_lookup _ [] _ _
      (List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem (List.mem_range.mpr hi)))) hnd
  · intro i hi
    unfold PTXRegFile.ofRegDecls; dsimp only; rw [hexp]
    exact foldl_setAssoc_lookup _ [] _ _
      (List.mem_append_right _ (List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.mpr hi)))) hnd

private theorem writeLE_size (bs : Array UInt8) (addr : Nat) (val : BitVec 64) :
    ∀ k, (ByteMemory.writeLittleEndianAux bs addr val k).size = bs.size := by
  intro k; induction k generalizing bs with
  | zero => rfl
  | succ k ih =>
    unfold ByteMemory.writeLittleEndianAux; rw [ih]; exact Array.size_setIfInBounds ..

private theorem writeLE_get_outside (bs : Array UInt8) (addr : Nat) (val : BitVec 64) :
    ∀ k j, (j < addr ∨ addr + k ≤ j) →
      (ByteMemory.writeLittleEndianAux bs addr val k)[j]? = bs[j]? := by
  intro k; induction k generalizing bs with
  | zero => intros; rfl
  | succ k ih =>
    intro j hout; unfold ByteMemory.writeLittleEndianAux
    rw [ih _ j (by omega), Array.getElem?_setIfInBounds_ne (by omega)]

private theorem writeLE_get_inside (bs : Array UInt8) (addr : Nat) (val : BitVec 64) :
    ∀ k i, i < k → addr + k ≤ bs.size →
      (ByteMemory.writeLittleEndianAux bs addr val k)[addr + i]? =
        some (UInt8.ofNat ((val >>> (i * 8)).toNat % 256)) := by
  intro k; induction k generalizing bs with
  | zero => intro _ hi; exact absurd hi (Nat.not_lt_zero _)
  | succ k ih =>
    intro i hi hsz; unfold ByteMemory.writeLittleEndianAux
    by_cases hik : i = k
    · subst hik
      rw [writeLE_get_outside _ addr val i (addr + i) (by omega), Array.getElem?_setIfInBounds_self]
      exact ite_eq_left_iff.mpr fun hc => absurd (by omega) hc
    · exact ih _ i (by omega) (by rw [Array.size_setIfInBounds]; omega)

private theorem readLE_cong (m1 m2 : ByteMemory) (addr : Nat) :
    ∀ k, (∀ i < k, m1.bytes[addr + i]? = m2.bytes[addr + i]?) →
      ByteMemory.readLittleEndianAux m1 addr k = ByteMemory.readLittleEndianAux m2 addr k := by
  intro k; induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h; unfold ByteMemory.readLittleEndianAux
    rw [h k (by omega), ih (fun i hi => h i (by omega))]

private theorem byteBv_eq (val : BitVec 64) (n : Nat) :
    BitVec.ofNat 64 (UInt8.ofNat ((val >>> (n * 8)).toNat % 256)).toNat =
      (val >>> (n * 8)) &&& 0xFF#64 := by
  have hm : ((val >>> (n * 8)).toNat % 256) % UInt8.size = (val >>> (n * 8)).toNat % 256 :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))
  apply BitVec.eq_of_toNat_eq
  simp only [UInt8.toNat_ofNat', hm, BitVec.toNat_ofNat, BitVec.toNat_and]
  have hlt : (val >>> (n * 8)).toNat % 256 < 2 ^ 64 :=
    Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  rw [Nat.mod_eq_of_lt hlt]
  change (val >>> (n * 8)).toNat % 256 = (val >>> (n * 8)).toNat &&& 255
  exact (Nat.and_two_pow_sub_one_eq_mod _ 8).symm

private def reconLE (val : BitVec 64) : Nat → BitVec 64
  | 0 => 0#64
  | n + 1 => reconLE val n ||| (((val >>> (n * 8)) &&& 0xFF#64) <<< (n * 8))

private theorem mask255_bit (d : Nat) (_ : d < 64) :
    (0xFF#64)[d] = decide (d < 8) := by
  rw [BitVec.getElem_eq_testBit_toNat]
  change (255 : Nat).testBit d = decide (d < 8)
  by_cases h8 : d < 8
  · match d, h8 with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl
  · have hlt2 : 255 < 2 ^ d := Nat.lt_of_lt_of_le (by decide : 255 < 2 ^ 8)
      (Nat.pow_le_pow_right (by decide) (by omega))
    simp [h8, Nat.testBit_lt_two_pow hlt2]

private theorem reconLE_bit (val : BitVec 64) :
    ∀ k (bit : Nat) (_ : bit < 64),
      (reconLE val k)[bit] = (decide (bit < k * 8) && val[bit]) := by
  intro k; induction k with
  | zero => intro _ _; simp [reconLE]
  | succ k ih =>
    intro bit hbit
    simp only [reconLE, BitVec.getElem_or, ih bit hbit,
      BitVec.getElem_shiftLeft, BitVec.getElem_and, BitVec.getElem_ushiftRight]
    by_cases h1 : bit < k * 8
    · have h2 : bit < (k + 1) * 8 := by omega
      simp [h1, h2]
    · have hmask := mask255_bit (bit - k * 8) (by omega)
      have hidx : k * 8 + (bit - k * 8) = bit := by omega
      have hlsb : val.getLsbD bit = val[bit] := by
        simp [BitVec.getLsbD, BitVec.getElem_eq_testBit_toNat]
      by_cases h2 : bit < (k + 1) * 8
      · have hd8 : bit - k * 8 < 8 := by omega
        simp [h1, h2, hmask, hd8, hidx, hlsb]
      · have hd8 : ¬ (bit - k * 8 < 8) := by omega
        simp [h1, h2, hmask, hd8]

private theorem reconLE_8 (val : BitVec 64) : reconLE val 8 = val := by
  ext bit hbit; rw [reconLE_bit val 8 bit hbit]; simp [decide_eq_true hbit]

private theorem readLE_from_bytes (m : ByteMemory) (addr : Nat) (val : BitVec 64) :
    ∀ k, (∀ i < k, m.bytes[addr + i]? = some (UInt8.ofNat ((val >>> (i * 8)).toNat % 256))) →
      ByteMemory.readLittleEndianAux m addr k = some (reconLE val k) := by
  intro k; induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h; unfold ByteMemory.readLittleEndianAux reconLE
    rw [h k (by omega), ih (fun i hi => h i (by omega))]
    dsimp only; rw [byteBv_eq]

theorem storeBits_eq_some_and_size (m : ByteMemory) (addr : Nat) (val : BitVec 64)
    (h : addr + 8 ≤ m.bytes.size) :
    ∃ m', m.storeBits addr 8 val = some m' ∧ m'.bytes.size = m.bytes.size ∧
      m'.loadBits addr 8 = some val ∧
      ∀ a2, (a2 + 8 ≤ addr ∨ addr + 8 ≤ a2) → m'.loadBits a2 8 = m.loadBits a2 8 := by
  have hex : ∃ bs', m.storeBits addr 8 val = some { bytes := bs' } ∧
      bs'.size = m.bytes.size ∧
      (∀ i < 8, bs'[addr + i]? = some (UInt8.ofNat ((val >>> (i * 8)).toNat % 256))) ∧
      (∀ j, (j < addr ∨ addr + 8 ≤ j) → bs'[j]? = m.bytes[j]?) := by
    refine ⟨ByteMemory.writeLittleEndianAux m.bytes addr val 8, ?_, ?_, ?_, ?_⟩
    · unfold ByteMemory.storeBits; exact ite_eq_left_iff.mpr fun hc => absurd h hc
    · exact writeLE_size m.bytes addr val 8
    · intro i hi; exact writeLE_get_inside m.bytes addr val 8 i hi h
    · intro j hj; exact writeLE_get_outside m.bytes addr val 8 j hj
  rcases hex with ⟨bs', hst, hsz, hin, hout⟩
  refine ⟨{ bytes := bs' }, hst, hsz, ?_, ?_⟩
  · unfold ByteMemory.loadBits; dsimp only
    rw [hsz, ite_eq_left_iff.mpr fun hc => absurd h hc,
        readLE_from_bytes { bytes := bs' } addr val 8 hin, reconLE_8]
  · intro a2 hdisj; unfold ByteMemory.loadBits; dsimp only; rw [hsz]
    split
    · exact readLE_cong _ _ a2 8 fun i hi => hout (a2 + i) (by omega)
    · rfl

private theorem fillU64Words_size (ws : List (BitVec 64)) :
    ∀ (bs : Array UInt8) (idx : Nat), (ByteMemory.fillU64Words bs idx ws).size = bs.size := by
  induction ws with
  | nil => intros; rfl
  | cons w rest ih =>
    intro bs idx; unfold ByteMemory.fillU64Words; rw [ih, writeLE_size]

private theorem fillU64Words_get_before (ws : List (BitVec 64)) :
    ∀ (bs : Array UInt8) (idx j : Nat), j < idx * 8 →
      (ByteMemory.fillU64Words bs idx ws)[j]? = bs[j]? := by
  induction ws with
  | nil => intros; rfl
  | cons w rest ih =>
    intro bs idx j hj; unfold ByteMemory.fillU64Words
    rw [ih _ (idx + 1) j (by omega)]
    exact writeLE_get_outside bs (idx * 8) w 8 j (Or.inl hj)

private theorem fillU64Words_get_word (ws : List (BitVec 64)) :
    ∀ (bs : Array UInt8) (base i b : Nat) (hi : i < ws.length),
      b < 8 → (base + ws.length) * 8 ≤ bs.size →
      (ByteMemory.fillU64Words bs base ws)[(base + i) * 8 + b]? =
        some (UInt8.ofNat (((ws[i]'hi) >>> (b * 8)).toNat % 256)) := by
  induction ws with
  | nil => intro _ _ _ _ hi; exact absurd hi (Nat.not_lt_zero _)
  | cons w rest ih =>
    intro bs base i b hi hb hsz; unfold ByteMemory.fillU64Words
    cases i with
    | zero =>
      have hb0 : (base + 0) * 8 + b = base * 8 + b := by omega
      rw [hb0, fillU64Words_get_before rest _ (base + 1) (base * 8 + b) (by omega)]
      exact writeLE_get_inside bs (base * 8) w 8 b hb (by simp only [List.length_cons] at hsz; omega)
    | succ i' =>
      have hi' : i' < rest.length := by simp only [List.length_cons] at hi; omega
      have hsz' : (base + 1 + rest.length) * 8 ≤ (ByteMemory.writeLittleEndianAux bs (base * 8) w 8).size := by
        rw [writeLE_size]; simp only [List.length_cons] at hsz; omega
      have heq : (base + (i' + 1)) * 8 + b = (base + 1 + i') * 8 + b := by omega
      rw [heq]; exact ih _ (base + 1) i' b hi' hb hsz'

theorem ofU64Words_size (ws : List (BitVec 64)) :
    (ByteMemory.ofU64Words ws).bytes.size = ws.length * 8 := by
  simp [ByteMemory.ofU64Words, fillU64Words_size]

theorem ofU64Words_loadBits (ws : List (BitVec 64)) (i : Nat) (hi : i < ws.length) :
    (ByteMemory.ofU64Words ws).loadBits (i * 8) 8 = some (ws[i]'hi) := by
  have hex : ∃ bs', ByteMemory.ofU64Words ws = { bytes := bs' } ∧
      bs'.size = ws.length * 8 ∧
      (∀ b < 8, bs'[i * 8 + b]? = some (UInt8.ofNat (((ws[i]'hi) >>> (b * 8)).toNat % 256))) := by
    refine ⟨ByteMemory.fillU64Words (Array.replicate (ws.length * 8) 0) 0 ws, rfl, ?_, ?_⟩
    · rw [fillU64Words_size, Array.size_replicate]
    · intro b hb
      simpa using fillU64Words_get_word ws (Array.replicate (ws.length * 8) 0) 0 i b hi hb (by simp)
  rcases hex with ⟨bs', heq, hsz, hin⟩
  rw [heq]; unfold ByteMemory.loadBits; dsimp only
  have hle : i * 8 + 8 ≤ ws.length * 8 := by omega
  rw [hsz, ite_eq_left_iff.mpr fun hc => absurd hle hc,
      readLE_from_bytes { bytes := bs' } (i * 8) (ws[i]'hi) 8 hin, reconLE_8]

private theorem walk_halted_prefix (stmts : List PTXStmt) (cta : PTXCTAState)
    (done suffix : List PTXThreadState) (hdone : ∀ t ∈ done, t.halted = true) :
    ∀ pref, stepFirstReadyThread stmts cta pref (done ++ suffix) =
      stepFirstReadyThread stmts cta (done.reverse ++ pref) suffix := by
  induction done with
  | nil => intro pref; simp
  | cons d ds ih =>
    intro pref
    have hd : d.halted = true := hdone d (List.Mem.head ds)
    have hds : ∀ t ∈ ds, t.halted = true := fun t ht => hdone t (List.Mem.tail d ht)
    simp only [List.cons_append, stepFirstReadyThread, hd, ite_true, List.reverse_cons, List.append_assoc]
    exact ih hds (d :: pref)

theorem step_non_barrier_instr (stmts : List PTXStmt) (cta : PTXCTAState)
    (done : List PTXThreadState) (th : PTXThreadState) (todo : List PTXThreadState)
    (guard : Option PTXPredGuard) (ins : PTXInstr)
    (th' : PTXThreadState) (gMem' sMem' : ByteMemory) (log' : List MemAccessLog)
    (hthreads : cta.threads = done ++ (th :: todo))
    (hdone : ∀ t ∈ done, t.halted = true)
    (hnh : th.halted = false)
    (hpc : stmts[th.pc]? = some (.instr guard ins))
    (hnBar : ∀ b, ins ≠ .barSync b)
    (hnShfl : ∀ d s o c m, ins ≠ .shflSyncBfly d s o c m)
    (hexec : execPredicatedInstr stmts cta th guard ins = .ok (th', gMem', sMem', log')) :
    stepCTA stmts cta = .ok (false, { cta with
      threads := done ++ (th' :: todo)
      globalMem := gMem'
      sharedMem := sMem'
      epochLog := log' }) := by
  have hallFalse : cta.threads.all (·.halted) = false := by
    rw [hthreads, List.all_append, List.all_cons, hnh]; simp
  have hstep1 : stepFirstReadyThread stmts cta [] cta.threads = .ok (true, { cta with
      threads := done ++ (th' :: todo), globalMem := gMem', sharedMem := sMem', epochLog := log' }) := by
    rw [hthreads, walk_halted_prefix stmts cta done (th :: todo) hdone []]
    unfold stepFirstReadyThread
    rw [hnh, hpc, List.append_nil, List.reverse_reverse]
    cases ins <;> try (dsimp only; rw [hexec]; rfl)
    · exfalso; exact hnBar _ rfl
    · exfalso; exact hnShfl _ _ _ _ _ rfl
  unfold stepCTA
  rw [hallFalse, hstep1]; rfl

theorem step_label (stmts : List PTXStmt) (cta : PTXCTAState)
    (done : List PTXThreadState) (th : PTXThreadState) (todo : List PTXThreadState)
    (lbl : String)
    (hthreads : cta.threads = done ++ (th :: todo))
    (hdone : ∀ t ∈ done, t.halted = true)
    (hnh : th.halted = false)
    (hpc : stmts[th.pc]? = some (.label lbl)) :
    stepCTA stmts cta = .ok (false, { cta with
      threads := done ++ ({ th with pc := th.pc + 1 } :: todo) }) := by
  have hallFalse : cta.threads.all (·.halted) = false := by
    rw [hthreads, List.all_append, List.all_cons, hnh]; simp
  have hstep1 : stepFirstReadyThread stmts cta [] cta.threads = .ok (true, { cta with
      threads := done ++ ({ th with pc := th.pc + 1 } :: todo) }) := by
    rw [hthreads, walk_halted_prefix stmts cta done (th :: todo) hdone []]
    simp [stepFirstReadyThread, hnh, hpc]
  unfold stepCTA
  rw [hallFalse, hstep1]; rfl

theorem runCTAWithGlobalLog_step_no_clear (f : Nat) (stmts : List PTXStmt)
    (cta cta' : PTXCTAState) (saved : List MemAccessLog)
    (hstep : stepCTA stmts cta = .ok (false, cta'))
    (hnoClear : cta.epochLog = [] ∨ cta'.epochLog ≠ []) :
    runCTAWithGlobalLog (f + 1) stmts cta saved =
      runCTAWithGlobalLog f stmts cta' saved := by
  have hcond : (!cta.epochLog.isEmpty && cta'.epochLog.isEmpty) = false := by
    rcases hnoClear with h1 | h2
    · simp [h1]
    · cases hc : cta'.epochLog with
      | nil => exact absurd hc h2
      | cons _ _ => simp
  conv => lhs; unfold runCTAWithGlobalLog
  rw [hstep]; dsimp only [PTXOutcome.bind]
  rw [hcond]
  rfl

theorem runCTAWithGlobalLog_done_halted (f : Nat) (stmts : List PTXStmt)
    (cta : PTXCTAState) (saved : List MemAccessLog)
    (hhalt : cta.threads.all (·.halted) = true) :
    runCTAWithGlobalLog (f + 1) stmts cta saved =
      .ok (cta, cta.epochLog.filter (fun e => e.space == .global) ++ saved) := by
  have hstep : stepCTA stmts cta = .ok (true, cta) := by
    unfold stepCTA; simp [hhalt]
  have hcond : (!cta.epochLog.isEmpty && cta.epochLog.isEmpty) = false := by
    cases cta.epochLog <;> rfl
  conv => lhs; unfold runCTAWithGlobalLog
  rw [hstep]; dsimp only [PTXOutcome.bind]
  rw [hcond]
  rfl

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

end LeanNative.Backend.PTXAst
