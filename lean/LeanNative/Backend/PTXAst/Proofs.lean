import LeanNative.Backend.PTXAst.Eval
import Std.Data.String.ToNat

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

/-- Prefix consumption preserves the arbitrary suffix. -/
theorem stripPrefixChars_append (pre rest : List Char) :
    stripPrefixChars pre (pre ++ rest) = some rest := by
  induction pre <;> simp_all [stripPrefixChars]

theorem scanPTXName_append (name rest : List Char) (fuel : Nat)
    (hn : ∀ c ∈ name, ptxNameChar c = true)
    (hr : rest = [] ∨ ∃ c cs, rest = c :: cs ∧ ptxNameChar c = false)
    (hf : name.length < fuel) : scanPTXName fuel (name ++ rest) = some (name, rest) := by
  induction name generalizing fuel with
  | nil =>
    cases fuel with
    | zero => simp at hf
    | succ f =>
      rcases hr with rfl | ⟨c, cs, rfl, hc⟩ <;> simp_all [scanPTXName]
  | cons c cs ih =>
    cases fuel with
    | zero => simp at hf
    | succ f =>
      simp only [List.cons_append, scanPTXName, hn c (by simp), ↓reduceIte]
      rw [ih f (by intro x hx; exact hn x (by simp [hx])) (by simpa using hf)]
      rfl

theorem parsePTXPredGuard_roundtrip (g : PTXPredGuard) (rest : List Char)
    (h : CanonicalPTXPredGuard g) (fuel : Nat) (hf : g.predReg.toList.length < fuel) :
    parsePTXPredGuard (fuel + 1) ((ppPredGuard g).toList ++ rest) = some (g, rest) := by
  rcases g with ⟨name, negated⟩
  rcases h with ⟨⟨cs, hn, _⟩, hc⟩
  have hs := scanPTXName_append name.toList (' ' :: rest) fuel hc
    (Or.inr ⟨' ', rest, rfl, by decide⟩) hf
  have hn' : String.ofList ('%' :: cs) = name := by rw [← hn]; simp
  cases negated <;> simp [ppPredGuard, parsePTXPredGuard, stripPrefixChars,
    toString, String.toList_append, List.append_assoc, hn] at hs ⊢ <;>
    simp_all [stripPrefixChars]

/-- A canonical identifier consumes exactly its spelling and leaves the delimiter intact. -/
theorem parsePTXName_roundtrip (name : String) (hn : CanonicalPTXName name)
    (rest : List Char)
    (hr : rest = [] ∨ ∃ c cs, rest = c :: cs ∧ ptxNameChar c = false)
    (fuel : Nat) (hf : name.toList.length < fuel) :
    parsePTXName fuel (name.toList ++ rest) = some (name, rest) := by
  have hs := scanPTXName_append name.toList rest fuel hn.2 hr hf
  have hne : name ≠ "" := by intro he; exact hn.1 (by simp [he])
  simp [parsePTXName, hs, hne]

theorem parsePTXType_roundtrip (ty : PTXType) (fuel : Nat) (rest : List Char) :
    parsePTXType (fuel + 1) ((ppPTXType ty).toList ++ rest) = some (ty, rest) := by
  cases ty <;> rfl

theorem ppPredGuard_injective (a b : PTXPredGuard)
    (ha : CanonicalPTXPredGuard a) (hb : CanonicalPTXPredGuard b)
    (h : ppPredGuard a = ppPredGuard b) : a = b := by
  let fuel := a.predReg.toList.length + b.predReg.toList.length + 1
  have hp := congrArg (fun s : String => parsePTXPredGuard (fuel + 1) (s.toList ++ [])) h
  rw [parsePTXPredGuard_roundtrip a [] ha fuel (by omega),
      parsePTXPredGuard_roundtrip b [] hb fuel (by omega)] at hp
  exact (Option.some.inj hp |> Prod.mk.inj).1

theorem parsePTXNamedOperand_specialReg (sr : SpecialReg) :
    parsePTXNamedOperand (ppSpecialReg sr) = .sreg sr := by
  cases sr <;> decide

theorem parsePTXNamedOperand_reg (name : String)
    (h : CanonicalPTXOperand (.reg name)) : parsePTXNamedOperand name = .reg name := by
  have hf : ptxSpecialRegs.find? (fun sr => ppSpecialReg sr == name) = none := by
    apply List.find?_eq_none.mpr
    intro sr hs
    simpa using h.2.2 sr hs
  simp [parsePTXNamedOperand, hf, h.2.1]

theorem parsePTXOperand_specialReg_roundtrip (sr : SpecialReg) (rest : List Char) :
    parsePTXOperand 16 ((ppPTXOperand (.sreg sr)).toList ++ ',' :: rest) =
      some (.sreg sr, ',' :: rest) := by
  cases sr <;> simp [parsePTXOperand, ppPTXOperand, ppSpecialReg, scanPTXName,
    ptxNameChar, parsePTXNamedOperand, ptxSpecialRegs, List.find?]

theorem parsePTXOperand_reg_roundtrip (name : String) (cs rest : List Char)
    (hn : name.toList = '%' :: cs) (h : CanonicalPTXOperand (.reg name))
    (fuel : Nat) (hf : name.toList.length < fuel) :
    parsePTXOperand fuel ((ppPTXOperand (.reg name)).toList ++ ',' :: rest) =
      some (.reg name, ',' :: rest) := by
  have hs := scanPTXName_append name.toList (',' :: rest) fuel h.1.2
    (Or.inr ⟨',', rest, rfl, by decide⟩) hf
  have hp := parsePTXNamedOperand_reg name h
  have hc : String.ofList ('%' :: cs) = name := by rw [← hn]; simp
  simp only [ppPTXOperand, hn, List.cons_append] at hs ⊢
  simp [parsePTXOperand, hs, hc, hp]

theorem ppPTXOperand_reg_injective (a b : String)
    (h : ppPTXOperand (.reg a) = ppPTXOperand (.reg b)) : a = b := h

theorem parsePTXOperand_reg_suffix_roundtrip (name : String)
    (h : CanonicalPTXOperand (.reg name)) (rest : List Char)
    (hr : rest = [] ∨ ∃ c cs, rest = c :: cs ∧ ptxNameChar c = false)
    (fuel : Nat) (hf : name.toList.length < fuel) :
    parsePTXOperand fuel ((ppPTXOperand (.reg name)).toList ++ rest) =
      some (.reg name, rest) := by
  have hn : ∃ cs, name.toList = '%' :: cs := by
    have hp := String.startsWith_string_iff.mp h.2.1
    obtain ⟨cs, he⟩ := hp
    exact ⟨cs, he.symm⟩
  obtain ⟨cs, hn⟩ := hn
  have hs := scanPTXName_append name.toList rest fuel h.1.2 hr hf
  have hp := parsePTXNamedOperand_reg name h
  have hc : String.ofList ('%' :: cs) = name := by rw [← hn]; simp
  simp only [ppPTXOperand, hn, List.cons_append] at hs ⊢
  simp [parsePTXOperand, hs, hc, hp]

theorem parsePTXOperand_specialReg_suffix_roundtrip (sr : SpecialReg) (rest : List Char)
    (hr : rest = [] ∨ ∃ c cs, rest = c :: cs ∧ ptxNameChar c = false)
    (fuel : Nat) (hf : (ppSpecialReg sr).toList.length < fuel) :
    parsePTXOperand fuel ((ppPTXOperand (.sreg sr)).toList ++ rest) = some (.sreg sr, rest) := by
  have hc : ∀ c ∈ (ppSpecialReg sr).toList, ptxNameChar c = true := by cases sr <;> decide
  have hs := scanPTXName_append (ppSpecialReg sr).toList rest fuel hc hr hf
  cases sr <;> simp only [ppSpecialReg, String.reduceToList, List.cons_append, List.nil_append] at hs
  all_goals simp [parsePTXOperand, ppPTXOperand, ppSpecialReg, hs,
    parsePTXNamedOperand, ptxSpecialRegs, List.find?]

theorem natRepr_ptxNameChars (n : Nat) :
    ∀ c ∈ n.repr.toList, ptxNameChar c = true := by
  intro c hc
  have hd := Nat.isDigit_of_mem_toDigits (b := 10) (n := n) (by omega) (by omega)
    (by simpa only [Nat.toList_repr] using hc)
  simp [ptxNameChar, Char.isAlphanum, hd]

theorem parsePTXOperand_sym_roundtrip (name : String) (hn : CanonicalPTXSymbol name)
    (rest : List Char)
    (hr : rest = [] ∨ ∃ c cs, rest = c :: cs ∧ ptxNameChar c = false)
    (fuel : Nat) (hf : name.toList.length < fuel) :
    parsePTXOperand fuel ((ppPTXOperand (.sym name)).toList ++ rest) = some (.sym name, rest) := by
  obtain ⟨c, cs, he, hc⟩ := hn.2
  have hm : c ≠ '-' := by
    rcases hc with hc | rfl | rfl
    · intro h; subst c; contradiction
    all_goals decide
  have hp : c ≠ '%' := by
    rcases hc with hc | rfl | rfl
    · intro h; subst c; contradiction
    all_goals decide
  have hz : c ≠ '0' := by
    rcases hc with hc | rfl | rfl
    · intro h; subst c; contradiction
    all_goals decide
  have hd : c.isDigit = false := by
    rcases hc with hc | rfl | rfl
    · simp only [Char.isAlpha, Char.isLower, Char.isUpper, Bool.or_eq_true,
        Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [Char.isDigit, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      rcases hc with ⟨h, _⟩ | ⟨h, _⟩ <;> right <;> intro h'
      all_goals
        have h := UInt32.le_iff_toNat_le.mp h
        have h' := UInt32.le_iff_toNat_le.mp h'
        simp at h h'
        omega
    all_goals rfl
  have hstr : String.ofList (c :: cs) = name := by rw [← he]; simp
  have hpercent : name.startsWith "%" = false := by
    simp [String.startsWith_string_eq_false_iff, he, Ne.symm hp]
  have hs := scanPTXName_append name.toList rest fuel hn.1.2 hr hf
  have hnat : name.toNat? = none := by
    apply String.toNat?_eq_none
    apply Bool.eq_false_iff.mpr
    intro h
    have h := String.isNat_iff.mp h
    have hc' := h.2.1 c (by simp [he])
    rcases hc' with hc' | rfl
    · simp [hd] at hc'
    · exact h.2.2.2.1 (by simp [he])
  have hspecial : ptxSpecialRegs.find? (fun sr => ppSpecialReg sr == name) = none := by
    apply List.find?_eq_none.mpr
    intro sr _
    have hne : ppSpecialReg sr ≠ name := by
      intro h
      have hh := congrArg (fun s : String => s.startsWith "%") h
      cases sr <;> simp [ppSpecialReg, hpercent] at hh
    simpa using hne
  simp only [he] at hs
  simp only [ppPTXOperand, he, List.cons_append, parsePTXOperand]
  split
  · simp_all
  · simp only [← List.cons_append, hs, bind, Option.bind]
    simp [hstr, hpercent, hnat, hz, parsePTXNamedOperand, hspecial]

theorem parsePTXName_nat_roundtrip (n : Nat) (rest : List Char)
    (hr : rest = [] ∨ ∃ c cs, rest = c :: cs ∧ ptxNameChar c = false)
    (fuel : Nat) (hf : n.repr.toList.length < fuel) :
    parsePTXName fuel (n.repr.toList ++ rest) = some (n.repr, rest) := by
  exact parsePTXName_roundtrip _ ⟨by simpa only [Nat.toList_repr] using Nat.toDigits_ne_nil,
    natRepr_ptxNameChars n⟩ rest hr fuel hf

theorem parsePTXOperand_u64_roundtrip (v : BitVec 64) (rest : List Char)
    (hr : rest = [] ∨ ∃ c cs, rest = c :: cs ∧ ptxNameChar c = false)
    (fuel : Nat) (hf : v.toNat.repr.toList.length < fuel) :
    parsePTXOperand fuel ((ppPTXOperand (.immU64 v)).toList ++ rest) =
      some (.immU64 v, rest) := by
  have hs := scanPTXName_append v.toNat.repr.toList rest fuel (natRepr_ptxNameChars _) hr hf
  have hd (c : Char) (hc : c ∈ v.toNat.repr.toList) : c.isDigit = true :=
    Nat.isDigit_of_mem_toDigits (b := 10) (n := v.toNat) (by omega) (by omega)
      (by simpa only [Nat.toList_repr] using hc)
  cases he : v.toNat.repr.toList with
  | nil => exact False.elim (Nat.toDigits_ne_nil (by simpa only [Nat.toList_repr] using he))
  | cons c cs =>
    have hc := hd c (by simp [he])
    have hminus : c ≠ '-' := by intro h; subst c; contradiction
    have hpercent : c ≠ '%' := by intro h; subst c; contradiction
    have hstr : String.ofList (c :: cs) = v.toNat.repr := by rw [← he]; exact String.ofList_toList
    have hhexF : ∀ xs, c :: cs ≠ '0' :: 'f' :: xs := by
      intro xs h
      have hh := hd 'f' (by simp [he, h])
      contradiction
    have hhexD : ∀ xs, c :: cs ≠ '0' :: 'd' :: xs := by
      intro xs h
      have hh := hd 'd' (by simp [he, h])
      contradiction
    simp only [ppPTXOperand, toString, he, List.cons_append] at hs ⊢
    have hm : (match c :: (cs ++ rest) with
        | '-' :: xs => (true, xs)
        | _ => (false, c :: (cs ++ rest)) : Bool × List Char) = (false, c :: (cs ++ rest)) := by
      split <;> simp_all
    simp only [parsePTXOperand]
    split
    · simp_all
    · rw [hs]
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        bind, Option.bind]
      have hp : (String.ofList (c :: cs)).startsWith "%" = false := by
        simp [String.startsWith_string_eq_false_iff, Ne.symm hpercent]
      rw [hp]
      simp only [Bool.false_eq_true, ↓reduceIte]
      simp [hstr, Nat.toNat?_repr, v.isLt]

theorem parsePTXInstr_ret_roundtrip (rest : List Char) :
    parsePTXInstr 8 ((ppPTXInstr .ret).toList ++ rest) = some (.ret, rest) := by
  simp [parsePTXInstr, ppPTXInstr, parsePTXName, scanPTXName, ptxNameChar, stripPrefixChars]

theorem parsePTXOperand_s64_roundtrip (n : Int) (hn : n < 0) (rest : List Char)
    (hr : rest = [] ∨ ∃ c cs, rest = c :: cs ∧ ptxNameChar c = false)
    (fuel : Nat) (hf : n.natAbs.repr.toList.length < fuel) :
    parsePTXOperand fuel ((ppPTXOperand (.immS64 n)).toList ++ rest) =
      some (.immS64 n, rest) := by
  cases n with
  | ofNat n => exact False.elim (Int.not_lt.mpr (Int.natCast_nonneg n) hn)
  | negSucc n =>
    have hs := scanPTXName_append (n + 1).repr.toList rest fuel
      (natRepr_ptxNameChars _) hr hf
    have hne : (n + 1).repr.toList ≠ [] := by
      simpa only [Nat.toList_repr] using Nat.toDigits_ne_nil (b := 10) (n := n + 1)
    have hp : (ppPTXOperand (.immS64 (Int.negSucc n))).toList =
        '-' :: (n + 1).repr.toList := by
      simp [ppPTXOperand, toString, Int.repr, Nat.toList_repr]
    rw [hp]
    simp only [List.cons_append, parsePTXOperand, hs, bind, Option.bind]
    simp only [List.isEmpty_iff, hne, ↓reduceIte, String.ofList_toList,
      Nat.toNat?_repr]
    simp
    rfl

theorem toHexFixedGo_append (v : Nat) (acc : List Char) (n : Nat) :
    toHexFixedGo v acc n = toHexFixedGo v [] n ++ acc := by
  induction n generalizing v acc with
  | zero => rfl
  | succ n ih =>
    simp only [toHexFixedGo]
    rw [ih, ih (v / 16) [hexDigitChar v]]
    simp

theorem hexDigitChar_valid (v : Nat) :
    ptxNameChar (hexDigitChar v) = true ∧
    (if hexDigitChar v ≥ '0' && hexDigitChar v ≤ '9' then some ((hexDigitChar v).toNat - '0'.toNat)
      else if hexDigitChar v ≥ 'a' && hexDigitChar v ≤ 'f' then
        some ((hexDigitChar v).toNat - 'a'.toNat + 10) else none) = some (v % 16) := by
  have h : v % 16 < 16 := Nat.mod_lt _ (by decide)
  unfold hexDigitChar
  generalize v % 16 = d at h ⊢
  have hd : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨
      d = 8 ∨ d = 9 ∨ d = 10 ∨ d = 11 ∨ d = 12 ∨ d = 13 ∨ d = 14 ∨ d = 15 := by omega
  rcases hd with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst d <;> decide

theorem parsePTXHex_append_digit (n : Nat) (cs : List Char) (v value : Nat)
    (h : parsePTXHex n cs = some value) :
    parsePTXHex (n + 1) (cs ++ [hexDigitChar v]) = some (value * 16 + v % 16) := by
  induction n generalizing cs value with
  | zero =>
    cases cs <;> simp [parsePTXHex] at h
    subst value
    simpa [parsePTXHex] using (hexDigitChar_valid v).2
  | succ n ih =>
    cases cs with
    | nil => simp [parsePTXHex] at h
    | cons c cs =>
      simp only [List.cons_append, parsePTXHex] at h ⊢
      split at h <;> (try split at h)
      all_goals simp_all only [↓reduceIte, bind, Option.bind]
      all_goals
        cases ht : parsePTXHex n cs <;> simp [ht] at h
        all_goals subst value
        all_goals simp [ih _ _ ht, Nat.pow_succ, Nat.add_mul,
          Nat.mul_assoc, Nat.add_assoc]

theorem parsePTXHex_toHexFixedGo (v n : Nat) (hv : v < 16^n) :
    parsePTXHex n (toHexFixedGo v [] n) = some v := by
  induction n generalizing v with
  | zero =>
    have : v = 0 := by simpa using hv
    subst v
    rfl
  | succ n ih =>
    have hdiv : v / 16 < 16^n := by
      apply Nat.div_lt_of_lt_mul
      simpa [Nat.pow_succ, Nat.mul_comm] using hv
    rw [toHexFixedGo, toHexFixedGo_append]
    rw [parsePTXHex_append_digit n _ v _ (ih _ hdiv)]
    congr 1
    omega

theorem toHexFixedGo_chars (v n : Nat) :
    (toHexFixedGo v [] n).length = n ∧
    ∀ c ∈ toHexFixedGo v [] n, ptxNameChar c = true := by
  induction n generalizing v with
  | zero => simp [toHexFixedGo]
  | succ n ih =>
    rw [toHexFixedGo, toHexFixedGo_append]
    constructor
    · simp [ih]
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact (ih _).2 c hc
      · simpa using List.mem_singleton.mp hc ▸ (hexDigitChar_valid v).1

theorem parsePTXOperand_f32_roundtrip (v : UInt32) (rest : List Char)
    (hr : rest = [] ∨ ∃ c cs, rest = c :: cs ∧ ptxNameChar c = false)
    (fuel : Nat) (hf : 10 < fuel) :
    parsePTXOperand fuel ((ppPTXOperand (.immF32 v)).toList ++ rest) = some (.immF32 v, rest) := by
  have hs := scanPTXName_append ('0' :: 'f' :: toHexFixedGo v.toNat [] 8) rest fuel
    (by simpa [ptxNameChar] using (toHexFixedGo_chars v.toNat 8).2) hr
    (by simpa [(toHexFixedGo_chars v.toNat 8).1] using hf)
  have hh := parsePTXHex_toHexFixedGo v.toNat 8 (by exact v.toFin.isLt)
  simp only [List.cons_append] at hs
  simp only [ppPTXOperand, toString, toHexFixed, String.toList_append,
    String.reduceToList, String.toList_ofList, List.cons_append, List.nil_append]
  simp only [parsePTXOperand, bind, Option.bind]
  simp [hs, hh]

theorem parsePTXOperand_f64_roundtrip (v : UInt64) (rest : List Char)
    (hr : rest = [] ∨ ∃ c cs, rest = c :: cs ∧ ptxNameChar c = false)
    (fuel : Nat) (hf : 18 < fuel) :
    parsePTXOperand fuel ((ppPTXOperand (.immF64 v)).toList ++ rest) = some (.immF64 v, rest) := by
  have hs := scanPTXName_append ('0' :: 'd' :: toHexFixedGo v.toNat [] 16) rest fuel
    (by simpa [ptxNameChar] using (toHexFixedGo_chars v.toNat 16).2) hr
    (by simpa [(toHexFixedGo_chars v.toNat 16).1] using hf)
  have hh := parsePTXHex_toHexFixedGo v.toNat 16 (by exact v.toFin.isLt)
  simp only [List.cons_append] at hs
  simp only [ppPTXOperand, toString, toHexFixed, String.toList_append,
    String.reduceToList, String.toList_ofList, List.cons_append, List.nil_append]
  simp only [parsePTXOperand, bind, Option.bind]
  simp [hs, hh]

theorem parsePTXOperand_roundtrip (op : PTXOperand) (h : CanonicalPTXOperand op)
    (rest : List Char)
    (hr : rest = [] ∨ ∃ c cs, rest = c :: cs ∧ ptxNameChar c = false)
    (fuel : Nat) (hf : (ppPTXOperand op).toList.length < fuel) :
    parsePTXOperand fuel ((ppPTXOperand op).toList ++ rest) = some (op, rest) := by
  cases op with
  | reg name => exact parsePTXOperand_reg_suffix_roundtrip name h rest hr fuel hf
  | sreg sr => exact parsePTXOperand_specialReg_suffix_roundtrip sr rest hr fuel hf
  | sym name => exact parsePTXOperand_sym_roundtrip name h rest hr fuel hf
  | immU64 v => exact parsePTXOperand_u64_roundtrip v rest hr fuel hf
  | immS64 n =>
    apply parsePTXOperand_s64_roundtrip n h rest hr fuel
    cases n with
    | ofNat n => exact False.elim (Int.not_lt.mpr (Int.natCast_nonneg n) h)
    | negSucc n =>
      simp [ppPTXOperand, toString, Int.repr, String.toList_append] at hf ⊢
      omega
  | immF32 v =>
    apply parsePTXOperand_f32_roundtrip v rest hr fuel
    simpa [ppPTXOperand, toString, toHexFixed, String.toList_append,
      (toHexFixedGo_chars v.toNat 8).1] using hf
  | immF64 v =>
    apply parsePTXOperand_f64_roundtrip v rest hr fuel
    simpa [ppPTXOperand, toString, toHexFixed, String.toList_append,
      (toHexFixedGo_chars v.toNat 16).1] using hf

theorem ppPTXOperand_injective_on_canonical (a b : PTXOperand)
    (ha : CanonicalPTXOperand a) (hb : CanonicalPTXOperand b)
    (h : ppPTXOperand a = ppPTXOperand b) : a = b := by
  let fuel := (ppPTXOperand a).toList.length + (ppPTXOperand b).toList.length + 1
  have hp := congrArg (fun s : String => parsePTXOperand fuel (s.toList ++ [])) h
  rw [parsePTXOperand_roundtrip a ha [] (Or.inl rfl) fuel (by omega),
      parsePTXOperand_roundtrip b hb [] (Or.inl rfl) fuel (by omega)] at hp
  exact (Option.some.inj hp |> Prod.mk.inj).1

theorem parsePTXAddr_reg_zero_roundtrip (name : String)
    (hn : CanonicalPTXName name) (hp : name.startsWith "%" = true)
    (rest : List Char) (fuel : Nat) (hf : name.toList.length < fuel) :
    parsePTXAddr fuel ((ppPTXAddr (.regOffset name 0)).toList ++ rest) =
      some (.regOffset name 0, rest) := by
  have hs := scanPTXName_append name.toList (']' :: rest) fuel hn.2
    (Or.inr ⟨']', rest, rfl, rfl⟩) hf
  have hne : name ≠ "" := by intro h; exact hn.1 (by simp [h])
  simp [parsePTXAddr, ppPTXAddr, toString, String.toList_append, List.append_assoc,
    stripPrefixChars, hs, hne]
  simpa using hp

theorem parsePTXInstr_bra_roundtrip (name : String) (hn : CanonicalPTXName name)
    (rest : List Char) (fuel : Nat) (hf : name.toList.length < fuel) (hmin : 4 ≤ fuel) :
    parsePTXInstr fuel ((ppPTXInstr (.bra name)).toList ++ rest) = some (.bra name, rest) := by
  have htok := parsePTXName_roundtrip "bra" (by unfold CanonicalPTXName; decide)
    (' ' :: (name.toList ++ ';' :: rest)) (Or.inr ⟨' ', _, rfl, rfl⟩) fuel (by simp; omega)
  have hname := parsePTXName_roundtrip name hn (';' :: rest)
    (Or.inr ⟨';', rest, rfl, rfl⟩) fuel hf
  simp only [ppPTXInstr, toString, String.toList_append, String.reduceToList,
    List.append_assoc, List.cons_append, List.nil_append] at htok ⊢
  simp [parsePTXInstr, htok, hname, stripPrefixChars]

theorem ptxOpcodeFields_append_dot (a b : List Char) (ha : '.' ∉ a) :
    ptxOpcodeFields (a ++ '.' :: b) = a :: ptxOpcodeFields b := by
  induction a with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ≠ '.' := by intro h; subst c; simp at ha
    have ht : '.' ∉ cs := by simp_all
    simp [List.cons_append, ptxOpcodeFields, ih ht]

theorem ptxOpcodeFields_mov (ty : PTXType) :
    (ptxOpcodeFields ("mov" ++ ppPTXType ty).toList).map String.ofList =
      ["mov", String.ofList ((ppPTXType ty).toList.drop 1)] := by
  cases ty <;> rfl

theorem ptxOpcodeFields_typed (pre : List Char) (ty : PTXType) :
    ptxOpcodeFields (pre ++ (ppPTXType ty).toList) =
      ptxOpcodeFields pre ++ [(ppPTXType ty).toList.drop 1] := by
  induction pre with
  | nil => cases ty <;> rfl
  | cons c cs ih =>
    by_cases hc : c = '.'
    · subst c; simp [ptxOpcodeFields, ih]
    · simp only [List.cons_append]
      simp only [ptxOpcodeFields, ih]
      cases h : ptxOpcodeFields cs with
      | nil =>
        have hn : ∀ xs, ptxOpcodeFields xs ≠ [] := by
          intro xs
          induction xs with
          | nil => simp [ptxOpcodeFields]
          | cons c cs ih =>
            by_cases hc : c = '.'
            · subst c; simp [ptxOpcodeFields]
            · simp [ptxOpcodeFields]; split <;> simp
        exact False.elim (hn cs h)
      | cons field fields => rfl

theorem parsePTXType_suffix (ty : PTXType) (fuel : Nat) :
    parsePTXType (fuel + 1)
      ("." ++ String.ofList ((ppPTXType ty).toList.drop 1)).toList = some (ty, []) := by
  cases ty <;> rfl

theorem ptxTypedName (pre : String) (hp : CanonicalPTXName pre) (ty : PTXType) :
    CanonicalPTXName (pre ++ ppPTXType ty) := by
  constructor
  · intro h
    rw [String.toList_append] at h
    exact hp.1 (List.append_eq_nil_iff.mp h).1
  · intro c hc
    rcases List.mem_append.mp (by simpa using hc) with hc | hc
    · exact hp.2 c hc
    · have ht : ∀ c ∈ (ppPTXType ty).toList, ptxNameChar c = true := by
        cases ty <;> decide
      exact ht c hc

theorem parsePTXTypedName_roundtrip (pre : String) (hp : CanonicalPTXName pre)
    (ty : PTXType) (rest : List Char) (fuel : Nat)
    (hf : (pre ++ ppPTXType ty).toList.length < fuel) :
    parsePTXName fuel ((pre ++ ppPTXType ty).toList ++ ' ' :: rest) =
      some (pre ++ ppPTXType ty, ' ' :: rest) :=
  parsePTXName_roundtrip _ (ptxTypedName pre hp ty) _ (Or.inr ⟨' ', _, rfl, rfl⟩) fuel hf

theorem ptxMovToken_ne (ty : PTXType) :
    ("mov" ++ ppPTXType ty == "ret") = false ∧
    ("mov" ++ ppPTXType ty == "bra") = false ∧
    ("mov" ++ ppPTXType ty == "bar.sync") = false := by
  cases ty <;> decide

theorem parsePTXInstr_mov_step (ty : PTXType) (dst : String) (src : PTXOperand)
    (hd : CanonicalPTXName dst) (rest : List Char) (fuel : Nat)
    (hf : dst.toList.length < fuel) (hmin : 16 ≤ fuel)
    (hs : parsePTXOperand fuel ((ppPTXOperand src).toList ++ ';' :: rest) = some (src, ';' :: rest)) :
    parsePTXInstr fuel ((ppPTXInstr (.mov ty dst src)).toList ++ rest) = some (.mov ty dst src, rest) := by
  have ht : CanonicalPTXName ("mov" ++ ppPTXType ty) := by
    cases ty <;> unfold CanonicalPTXName <;> decide
  have hlen : ("mov" ++ ppPTXType ty).toList.length < fuel := by
    cases ty <;> simp [ppPTXType] <;> omega
  have htok := parsePTXName_roundtrip _ ht
    (' ' :: (dst.toList ++ ", ".toList ++ (ppPTXOperand src).toList ++ ';' :: rest))
    (Or.inr ⟨' ', _, rfl, rfl⟩) fuel hlen
  have hdst := parsePTXName_roundtrip dst hd
    (", ".toList ++ (ppPTXOperand src).toList ++ ';' :: rest)
    (Or.inr ⟨',', _, rfl, rfl⟩) fuel hf
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  simp only [String.toList_append, String.reduceToList, List.append_assoc,
    List.cons_append, List.nil_append] at htok hdst
  simp only [ppPTXInstr, toString, String.toList_append, String.reduceToList,
    List.append_assoc, List.cons_append, List.nil_append]
  simp only [parsePTXInstr, htok]
  simp only [bind, Option.bind, ptxMovToken_ne ty |>.1,
    ptxMovToken_ne ty |>.2.1, ptxMovToken_ne ty |>.2.2, Bool.false_eq_true,
    ↓reduceIte, stripPrefixChars]
  rw [ptxOpcodeFields_mov]
  simp only [List.head?_cons, List.getLast?_cons_cons, List.getLast?_singleton,
    parsePTXType_suffix]
  simp [stripPrefixChars, hdst, hs]

theorem parsePTXInstr_mov_roundtrip (ty : PTXType) (dst : String) (src : PTXOperand)
    (hd : CanonicalPTXName dst) (hs : CanonicalPTXOperand src)
    (rest : List Char) (fuel : Nat)
    (hf : (ppPTXInstr (.mov ty dst src)).toList.length < fuel) (hmin : 16 ≤ fuel) :
    parsePTXInstr fuel ((ppPTXInstr (.mov ty dst src)).toList ++ rest) =
      some (.mov ty dst src, rest) := by
  have hlen : dst.toList.length < fuel ∧ (ppPTXOperand src).toList.length < fuel := by
    simp [ppPTXInstr, toString, String.toList_append] at hf
    omega
  exact parsePTXInstr_mov_step ty dst src hd rest fuel hlen.1 hmin
    (parsePTXOperand_roundtrip src hs (';' :: rest) (Or.inr ⟨';', _, rfl, rfl⟩) fuel hlen.2)

theorem ptxTypedToken_ne (pre : String) (ty : PTXType)
    (hpre : 2 ≤ pre.toList.length) :
    (pre ++ ppPTXType ty == "ret") = false ∧
    (pre ++ ppPTXType ty == "bra") = false ∧
    (pre ++ ppPTXType ty == "bar.sync") = false := by
  have hlen : 3 ≤ (ppPTXType ty).toList.length := by cases ty <;> decide
  have hret : pre ++ ppPTXType ty ≠ "ret" := by
    intro h
    have := congrArg (fun s : String => s.toList.length) h
    simp only [String.toList_append, List.length_append, String.reduceToList, List.length_cons, List.length_nil] at this
    omega
  have hbra : pre ++ ppPTXType ty ≠ "bra" := by
    intro h
    have := congrArg (fun s : String => s.toList.length) h
    simp only [String.toList_append, List.length_append, String.reduceToList, List.length_cons, List.length_nil] at this
    omega
  have hbar : pre ++ ppPTXType ty ≠ "bar.sync" := by
    intro h
    have hs := congrArg (fun s : String => s.toList.getLast?) h
    cases ty <;> simp [ppPTXType, String.toList_append] at hs
  simpa using ⟨hret, hbra, hbar⟩

theorem parsePTXInstr_ldParam_roundtrip (ty : PTXType) (dst name : String)
    (hd : CanonicalPTXName dst) (hn : CanonicalPTXSymbol name)
    (rest : List Char) (fuel : Nat)
    (hf : (ppPTXInstr (.ldParam ty dst name)).toList.length < fuel + 1) :
    parsePTXInstr (fuel + 1) ((ppPTXInstr (.ldParam ty dst name)).toList ++ rest) =
      some (.ldParam ty dst name, rest) := by
  have ht := parsePTXTypedName_roundtrip "ld.param" (by unfold CanonicalPTXName; decide)
    ty (dst.toList ++ ", [".toList ++ name.toList ++ ']' :: ';' :: rest) (fuel + 1)
    (by simp [ppPTXInstr, toString, String.toList_append] at hf ⊢; omega)
  have hd := parsePTXName_roundtrip dst hd
    (", [".toList ++ name.toList ++ ']' :: ';' :: rest)
    (Or.inr ⟨',', _, rfl, rfl⟩) (fuel + 1)
    (by simp [ppPTXInstr, toString, String.toList_append] at hf; omega)
  have hs := scanPTXName_append name.toList (']' :: ';' :: rest) (fuel + 1) hn.1.2
    (Or.inr ⟨']', _, rfl, rfl⟩)
    (by simp [ppPTXInstr, toString, String.toList_append] at hf; omega)
  have hp : name.startsWith "%" = false := by
    obtain ⟨c, cs, he, hc⟩ := hn.2
    have h : c ≠ '%' := by
      rcases hc with hc | rfl | rfl
      · intro h; subst c; contradiction
      all_goals decide
    simp [String.startsWith_string_eq_false_iff, he, Ne.symm h]
  have hnonempty : name ≠ "" := by intro h; exact hn.1.1 (by simp [h])
  have ha : parsePTXAddr (fuel + 1) ('[' :: (name.toList ++ ']' :: ';' :: rest)) =
      some (.paramSym name, ';' :: rest) := by
    simp [parsePTXAddr, stripPrefixChars, hs, hnonempty]
    simpa using hp
  have hne := ptxTypedToken_ne "ld.param" ty (by decide)
  have hfields := congrArg (List.map String.ofList) (ptxOpcodeFields_typed "ld.param".toList ty)
  simp only [String.toList_append, String.reduceToList,
    List.append_assoc, List.cons_append, List.nil_append] at ht hd ha
  simp only [ppPTXInstr, toString, String.toList_append, String.reduceToList,
    List.append_assoc, List.cons_append, List.nil_append]
  simp only [parsePTXInstr, ht, bind, Option.bind, hne.1, hne.2.1, hne.2.2,
    Bool.false_eq_true, ↓reduceIte, stripPrefixChars]
  rw [show (ptxOpcodeFields ("ld.param" ++ ppPTXType ty).toList).map String.ofList =
      ["ld", "param", String.ofList ((ppPTXType ty).toList.drop 1)] by
    simpa [String.toList_append, List.map_append, ptxOpcodeFields] using hfields]
  simp only [List.head?_cons, List.getLast?_cons_cons, List.getLast?_singleton,
    parsePTXType_suffix]
  simp [stripPrefixChars, hd, ha]

theorem parsePTXStmt_instr_step (guard : Option PTXPredGuard) (ins : PTXInstr)
    (hg : ∀ g ∈ guard, CanonicalPTXPredGuard g) (rest : List Char)
    (fuel : Nat) (hf : ∀ g ∈ guard, g.predReg.toList.length < fuel)
    (hi : parsePTXInstr (fuel + 1) ((ppPTXInstr ins).toList ++ rest) = some (ins, rest)) :
    parsePTXStmt (fuel + 1) ((ppPTXStmt (.instr guard ins)).toList ++ rest) =
      some (.instr guard ins, rest) := by
  cases guard with
  | none =>
    have hn' : ∀ cs, (ppPTXInstr ins).toList ++ rest ≠ '@' :: cs := by
      intro cs
      cases ins <;> simp [ppPTXInstr, toString, String.toList_append]
    have hguard : (match (ppPTXInstr ins).toList ++ rest with
        | '@' :: _ => do
          let (g, rest) ← parsePTXPredGuard (fuel + 1) ((ppPTXInstr ins).toList ++ rest)
          pure (some g, rest)
        | _ => some (none, (ppPTXInstr ins).toList ++ rest) :
        Option (Option PTXPredGuard × List Char)) = some (none, (ppPTXInstr ins).toList ++ rest) := by
      split
      · rename_i cs he; exact False.elim (hn' cs he)
      · rfl
    simp [ppPTXStmt, toString, String.toList_append, parsePTXStmt,
      stripPrefixChars, hi]
  | some g =>
    have hp := parsePTXPredGuard_roundtrip g ((ppPTXInstr ins).toList ++ rest)
      (hg g (by simp)) fuel (hf g (by simp))
    have hat : ∃ cs, (ppPredGuard g).toList = '@' :: cs := by
      unfold ppPredGuard
      split <;> simp [toString, String.toList_append]
    obtain ⟨cs, he⟩ := hat
    simp only [ppPTXStmt, toString, String.toList_append, String.reduceToList,
      List.append_assoc, List.cons_append, List.nil_append, parsePTXStmt, stripPrefixChars]
    simp only [he, List.cons_append] at hp ⊢
    simp [hp, hi]

theorem parsePTXAddr_param_roundtrip (name : String)
    (hn : CanonicalPTXName name) (hp : name.startsWith "%" = false)
    (rest : List Char) (fuel : Nat) (hf : name.toList.length < fuel) :
    parsePTXAddr fuel ((ppPTXAddr (.paramSym name)).toList ++ rest) =
      some (.paramSym name, rest) := by
  have hs := scanPTXName_append name.toList (']' :: rest) fuel hn.2
    (Or.inr ⟨']', rest, rfl, rfl⟩) hf
  have hne : name ≠ "" := by intro h; exact hn.1 (by simp [h])
  simp [parsePTXAddr, ppPTXAddr, toString, String.toList_append, List.append_assoc,
    stripPrefixChars, hs, hne]
  simpa using hp

theorem parsePTXParamDecl_roundtrip (p : PTXParamDecl)
    (hn : CanonicalPTXName p.name) (rest : List Char)
    (hr : rest = [] ∨ ∃ c cs, rest = c :: cs ∧ ptxNameChar c = false)
    (fuel : Nat) (hf : p.name.toList.length < fuel + 1) :
    parsePTXParamDecl (fuel + 1)
      ((s!"    .param {ppPTXType p.ty} {p.name}").toList ++ rest) = some (p, rest) := by
  have ht := parsePTXType_roundtrip p.ty fuel (' ' :: (p.name.toList ++ rest))
  have hp := parsePTXName_roundtrip p.name hn rest hr (fuel + 1) hf
  rcases p with ⟨ty, name⟩
  simp [parsePTXParamDecl, toString, String.toList_append, List.append_assoc,
    stripPrefixChars, ht, hp]

theorem parsePTXAddr_offset_roundtrip (name : String) (offset : Int)
    (hn : CanonicalPTXName name) (rest : List Char)
    (fuel : Nat) (hf : name.toList.length < fuel)
    (ho : offset.natAbs.repr.toList.length < fuel) :
    parsePTXAddr fuel
      ((if offset = 0 then s!"[{name}]"
        else if offset > 0 then s!"[{name}+{offset}]" else s!"[{name}{offset}]").toList ++ rest) =
      some ((if name.startsWith "%" then .regOffset name offset
        else if offset = 0 then .paramSym name else .symOffset name offset), rest) := by
  have hne : name ≠ "" := by intro h; exact hn.1 (by simp [h])
  cases offset with
  | ofNat n =>
    cases n with
    | zero =>
      have hs := scanPTXName_append name.toList (']' :: rest) fuel hn.2
        (Or.inr ⟨']', _, rfl, rfl⟩) hf
      simp [parsePTXAddr, toString, String.toList_append, List.append_assoc,
        stripPrefixChars, hs, hne]
    | succ n =>
      have hz : (n : Int) + 1 ≠ 0 := by omega
      have hdigit : (String.ofList (Nat.toDigits 10 (n + 1))).toNat? = some (n + 1) :=
        Nat.toNat?_repr (n + 1)
      have hs := scanPTXName_append name.toList
        ('+' :: ((n + 1).repr.toList ++ ']' :: rest)) fuel hn.2
        (Or.inr ⟨'+', _, rfl, rfl⟩) hf
      have hd := scanPTXName_append (n + 1).repr.toList (']' :: rest) fuel
        (natRepr_ptxNameChars _) (Or.inr ⟨']', _, rfl, rfl⟩) ho
      simp only [Nat.toList_repr] at hs hd
      simp [parsePTXAddr, toString, Int.repr, String.toList_append, List.append_assoc,
        stripPrefixChars, hs, hd, hne, hz, hdigit]
  | negSucc n =>
    have hdigit : (String.ofList (Nat.toDigits 10 (n + 1))).toNat? = some (n + 1) :=
      Nat.toNat?_repr (n + 1)
    have hneg : -((n : Int) + 1) = Int.negSucc n := rfl
    have hs := scanPTXName_append name.toList
      ('-' :: ((n + 1).repr.toList ++ ']' :: rest)) fuel hn.2
      (Or.inr ⟨'-', _, rfl, rfl⟩) hf
    have hd := scanPTXName_append (n + 1).repr.toList (']' :: rest) fuel
      (natRepr_ptxNameChars _) (Or.inr ⟨']', _, rfl, rfl⟩) ho
    simp only [Nat.toList_repr] at hs hd
    simp [parsePTXAddr, toString, Int.repr, String.toList_append, List.append_assoc,
      stripPrefixChars, hs, hd, hne, hdigit, hneg]

theorem parsePTXAddr_roundtrip (a : PTXAddr) (ha : CanonicalPTXAddr a)
    (rest : List Char) (fuel : Nat) (hf : (ppPTXAddr a).toList.length < fuel) :
    parsePTXAddr fuel ((ppPTXAddr a).toList ++ rest) = some (a, rest) := by
  cases a with
  | paramSym name =>
    have hp : name.startsWith "%" = false := by
      obtain ⟨c, cs, he, hc⟩ := ha.2
      have hn : c ≠ '%' := by
        rcases hc with hc | rfl | rfl
        · intro h; subst c; contradiction
        all_goals decide
      simp [String.startsWith_string_eq_false_iff, he, Ne.symm hn]
    apply parsePTXAddr_param_roundtrip name ha.1 hp rest fuel
    simp [ppPTXAddr, toString, String.toList_append] at hf
    omega
  | regOffset name offset =>
    have hlen : name.toList.length < fuel ∧ offset.natAbs.repr.toList.length < fuel := by
      cases offset with
      | ofNat n =>
        have hz (m : Nat) : (m : Int) + 1 ≠ 0 := by omega
        have habs (m : Nat) : ((m : Int) + 1).natAbs = m + 1 := rfl
        cases n <;> simp [ppPTXAddr, toString, Int.repr, String.toList_append, hz, habs] at hf ⊢ <;> omega
      | negSucc n =>
        simp [ppPTXAddr, toString, Int.repr, String.toList_append] at hf ⊢
        omega
    have h := parsePTXAddr_offset_roundtrip name offset ha.1 rest fuel hlen.1 hlen.2
    simpa [ppPTXAddr, ha.2] using h
  | symOffset name offset =>
    have hp : name.startsWith "%" = false := by
      obtain ⟨c, cs, he, hc⟩ := ha.1.2
      have hn : c ≠ '%' := by
        rcases hc with hc | rfl | rfl
        · intro h; subst c; contradiction
        all_goals decide
      simp [String.startsWith_string_eq_false_iff, he, Ne.symm hn]
    have hlen : name.toList.length < fuel ∧ offset.natAbs.repr.toList.length < fuel := by
      cases offset with
      | ofNat n =>
        have hz (m : Nat) : (m : Int) + 1 ≠ 0 := by omega
        have habs (m : Nat) : ((m : Int) + 1).natAbs = m + 1 := rfl
        cases n <;> simp [ppPTXAddr, toString, Int.repr, String.toList_append, hz, habs] at hf ⊢ <;> omega
      | negSucc n =>
        simp [ppPTXAddr, toString, Int.repr, String.toList_append] at hf ⊢
        omega
    have h := parsePTXAddr_offset_roundtrip name offset ha.1.1 rest fuel hlen.1 hlen.2
    simpa [ppPTXAddr, hp, ha.2] using h

theorem ppPTXAddr_injective_on_canonical (a b : PTXAddr)
    (ha : CanonicalPTXAddr a) (hb : CanonicalPTXAddr b)
    (h : ppPTXAddr a = ppPTXAddr b) : a = b := by
  let fuel := (ppPTXAddr a).toList.length + (ppPTXAddr b).toList.length + 1
  have hp := congrArg (fun s : String => parsePTXAddr fuel (s.toList ++ [])) h
  rw [parsePTXAddr_roundtrip a ha [] fuel (by omega),
      parsePTXAddr_roundtrip b hb [] fuel (by omega)] at hp
  exact (Option.some.inj hp |> Prod.mk.inj).1

theorem parsePTXInstr_ret_suffix_roundtrip (rest : List Char) (fuel : Nat) (hf : 3 < fuel) :
    parsePTXInstr fuel ((ppPTXInstr .ret).toList ++ rest) = some (.ret, rest) := by
  have ht := parsePTXName_roundtrip "ret" (by unfold CanonicalPTXName; decide)
    (';' :: rest) (Or.inr ⟨';', _, rfl, rfl⟩) fuel hf
  simp only [String.reduceToList, List.cons_append, List.nil_append] at ht
  simp [parsePTXInstr, ppPTXInstr, ht, stripPrefixChars]

theorem parsePTXInstr_barSync_roundtrip (bid : Nat) (rest : List Char) (fuel : Nat)
    (hf : bid.repr.toList.length < fuel) (hmin : 8 < fuel) :
    parsePTXInstr fuel ((ppPTXInstr (.barSync bid)).toList ++ rest) = some (.barSync bid, rest) := by
  have ht := parsePTXName_roundtrip "bar.sync" (by unfold CanonicalPTXName; decide)
    (' ' :: (bid.repr.toList ++ ';' :: rest)) (Or.inr ⟨' ', _, rfl, rfl⟩) fuel hmin
  have hn := parsePTXName_nat_roundtrip bid (';' :: rest)
    (Or.inr ⟨';', _, rfl, rfl⟩) fuel hf
  simp only [String.reduceToList, List.cons_append, List.nil_append, Nat.toList_repr] at ht hn
  simp [parsePTXInstr, ppPTXInstr, toString, String.toList_append, List.append_assoc,
    ht, hn, stripPrefixChars, Nat.toNat?_repr]

theorem parsePTXInstr_unary_roundtrip (opcode : String) (ty : PTXType)
    (dst : String) (src : PTXOperand)
    (hop : opcode = "mov" ∨ opcode = "not" ∨ opcode = "neg" ∨ opcode = "clz")
    (hd : CanonicalPTXName dst) (hs : CanonicalPTXOperand src)
    (rest : List Char) (fuel : Nat)
    (hf : (opcode ++ ppPTXType ty ++ " " ++ dst ++ ", " ++ ppPTXOperand src ++ ";").toList.length < fuel + 1) :
    parsePTXInstr (fuel + 1)
      ((opcode ++ ppPTXType ty ++ " " ++ dst ++ ", " ++ ppPTXOperand src ++ ";").toList ++ rest) =
      some ((if opcode = "mov" then .mov ty dst src else if opcode = "not" then .bitNot ty dst src
        else if opcode = "neg" then .neg ty dst src else .clz ty dst src), rest) := by
  have hopName : CanonicalPTXName opcode := by
    rcases hop with rfl | rfl | rfl | rfl <;> unfold CanonicalPTXName <;> decide
  have ht := parsePTXTypedName_roundtrip opcode hopName ty
    (dst.toList ++ ',' :: ' ' :: ((ppPTXOperand src).toList ++ ';' :: rest)) (fuel + 1)
    (by simp [String.toList_append] at hf ⊢; omega)
  have hd := parsePTXName_roundtrip dst hd
    (',' :: ' ' :: ((ppPTXOperand src).toList ++ ';' :: rest))
    (Or.inr ⟨',', _, rfl, rfl⟩) (fuel + 1) (by simp [String.toList_append] at hf; omega)
  have hs := parsePTXOperand_roundtrip src hs (';' :: rest)
    (Or.inr ⟨';', _, rfl, rfl⟩) (fuel + 1) (by simp [String.toList_append] at hf; omega)
  have hne := ptxTypedToken_ne opcode ty (by rcases hop with rfl | rfl | rfl | rfl <;> decide)
  have hfields : (ptxOpcodeFields (opcode ++ ppPTXType ty).toList).map String.ofList =
      [opcode, String.ofList ((ppPTXType ty).toList.drop 1)] := by
    rw [String.toList_append, ptxOpcodeFields_typed, List.map_append]
    rcases hop with rfl | rfl | rfl | rfl <;> rfl
  simp only [String.toList_append, String.reduceToList, List.append_assoc,
    List.cons_append, List.nil_append] at ht ⊢
  simp only [parsePTXInstr, ht, bind, Option.bind, hne.1, hne.2.1, hne.2.2,
    Bool.false_eq_true, ↓reduceIte, stripPrefixChars]
  rw [hfields]
  simp only [List.head?_cons, List.getLast?_cons_cons, List.getLast?_singleton, parsePTXType_suffix]
  rcases hop with rfl | rfl | rfl | rfl <;> simp [stripPrefixChars, hd, hs]

theorem parsePTXInstr_binary_roundtrip (opcode : String) (ty : PTXType)
    (dst : String) (a b : PTXOperand)
    (hop : opcode ∈ ["sub", "div", "rem", "and", "or", "xor", "shl", "shr"])
    (hd : CanonicalPTXName dst) (ha : CanonicalPTXOperand a) (hb : CanonicalPTXOperand b)
    (rest : List Char) (fuel : Nat)
    (hf : (opcode ++ ppPTXType ty ++ " " ++ dst ++ ", " ++ ppPTXOperand a ++
      ", " ++ ppPTXOperand b ++ ";").toList.length < fuel + 1) :
    parsePTXInstr (fuel + 1)
      ((opcode ++ ppPTXType ty ++ " " ++ dst ++ ", " ++ ppPTXOperand a ++
        ", " ++ ppPTXOperand b ++ ";").toList ++ rest) =
      some ((match (generalizing := false) opcode with
        | "sub" => .sub ty dst a b | "div" => .div ty dst a b
        | "rem" => .rem ty dst a b | "and" => .bitAnd ty dst a b
        | "or" => .bitOr ty dst a b | "xor" => .bitXor ty dst a b
        | "shl" => .shl ty dst a b | _ => .shr ty dst a b), rest) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  have hopName : CanonicalPTXName opcode := by
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      unfold CanonicalPTXName <;> decide
  have ht := parsePTXTypedName_roundtrip opcode hopName ty
    (dst.toList ++ ',' :: ' ' :: ((ppPTXOperand a).toList ++ ',' :: ' ' ::
      ((ppPTXOperand b).toList ++ ';' :: rest))) (fuel + 1)
    (by simp [String.toList_append] at hf ⊢; omega)
  have hd := parsePTXName_roundtrip dst hd
    (',' :: ' ' :: ((ppPTXOperand a).toList ++ ',' :: ' ' :: ((ppPTXOperand b).toList ++ ';' :: rest)))
    (Or.inr ⟨',', _, rfl, rfl⟩) (fuel + 1) (by simp [String.toList_append] at hf; omega)
  have ha := parsePTXOperand_roundtrip a ha
    (',' :: ' ' :: ((ppPTXOperand b).toList ++ ';' :: rest))
    (Or.inr ⟨',', _, rfl, rfl⟩) (fuel + 1) (by simp [String.toList_append] at hf; omega)
  have hb := parsePTXOperand_roundtrip b hb (';' :: rest)
    (Or.inr ⟨';', _, rfl, rfl⟩) (fuel + 1) (by simp [String.toList_append] at hf; omega)
  have hne := ptxTypedToken_ne opcode ty
    (by rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hfields : (ptxOpcodeFields (opcode ++ ppPTXType ty).toList).map String.ofList =
      [opcode, String.ofList ((ppPTXType ty).toList.drop 1)] := by
    rw [String.toList_append, ptxOpcodeFields_typed, List.map_append]
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  simp only [String.toList_append, List.append_assoc] at ht
  conv =>
    lhs
    arg 2
    simp only [String.toList_append, String.reduceToList, List.append_assoc,
      List.cons_append, List.nil_append]
  simp only [parsePTXInstr, ht, bind, Option.bind, hne.1, hne.2.1, hne.2.2,
    Bool.false_eq_true, ↓reduceIte, stripPrefixChars]
  rw [hfields]
  simp only [List.head?_cons, List.getLast?_cons_cons, List.getLast?_singleton, parsePTXType_suffix]
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [stripPrefixChars, hd, ha, hb]

theorem scanPTXLines_singleton (chars : List Char)
    (hn : '\n' ∉ chars) (fuel : Nat) (hf : chars.length < fuel) :
    scanPTXLines fuel chars = some [chars] := by
  induction chars generalizing fuel with
  | nil => cases fuel <;> simp_all [scanPTXLines]
  | cons c cs ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hc : c ≠ '\n' := by intro he; subst c; simp at hn
      have hs : '\n' ∉ cs := by intro he; exact hn (List.mem_cons_of_mem c he)
      simp [scanPTXLines, ih hs fuel (by simpa using hf), hc]

theorem scanPTXLines_prepend (chars rest : List Char) (lines : List (List Char))
    (hn : '\n' ∉ chars) (fuel : Nat)
    (hp : scanPTXLines fuel rest = some lines) (hne : lines ≠ []) :
    scanPTXLines (fuel + chars.length + 1) (chars ++ '\n' :: rest) =
      some (chars :: lines) := by
  induction chars with
  | nil => cases lines <;> simp_all [scanPTXLines]
  | cons c cs ih =>
    have hc : c ≠ '\n' := by intro he; subst c; simp at hn
    have hs : '\n' ∉ cs := by intro he; exact hn (List.mem_cons_of_mem c he)
    have hi := ih hs
    simp only [Nat.add_assoc] at hi
    simp [List.length_cons, Nat.add_assoc, scanPTXLines, hc, hi]

theorem scanPTXLines_intercalate (lines : List (List Char))
    (hne : lines ≠ []) (hn : ∀ line ∈ lines, '\n' ∉ line) (fuel : Nat)
    (hf : (List.intercalate ['\n'] lines).length < fuel) :
    scanPTXLines fuel (List.intercalate ['\n'] lines) = some lines := by
  induction lines generalizing fuel with
  | nil => contradiction
  | cons line lines ih =>
    cases lines with
    | nil => simpa using scanPTXLines_singleton line (hn line (by simp)) fuel (by simpa using hf)
    | cons next lines =>
      have hp := ih (by simp) (by intro l hl; exact hn l (by simp [hl]))
        (fuel - line.length - 1) (by
          simp [List.intercalate_cons_cons, List.length_append] at hf ⊢
          omega)
      have hr := scanPTXLines_prepend line
        (List.intercalate ['\n'] (next :: lines)) (next :: lines)
        (hn line (by simp)) (fuel - line.length - 1) hp (by simp)
      have he : fuel - line.length - 1 + line.length + 1 = fuel := by
        simp [List.intercalate_cons_cons, List.length_append] at hf
        omega
      simpa [he, List.intercalate_cons_cons] using hr

theorem parsePTXRegDecl_roundtrip (r : PTXRegDecl)
    (hn : CanonicalPTXName r.prefixName) (rest : List Char)
    (fuel : Nat) (hf : r.prefixName.toList.length < fuel + 1)
    (hc : r.count.repr.toList.length < fuel + 1) :
    parsePTXRegDecl (fuel + 1)
      ((s!"    .reg {ppPTXType r.ty} {r.prefixName}<{r.count}>;").toList ++ rest) =
      some (r, rest) := by
  have ht := parsePTXType_roundtrip r.ty fuel
    (' ' :: (r.prefixName.toList ++ '<' :: (r.count.repr.toList ++ '>' :: ';' :: rest)))
  have hp := parsePTXName_roundtrip r.prefixName hn
    ('<' :: (r.count.repr.toList ++ '>' :: ';' :: rest))
    (Or.inr ⟨'<', _, rfl, rfl⟩) (fuel + 1) hf
  have hc := parsePTXName_nat_roundtrip r.count ('>' :: ';' :: rest)
    (Or.inr ⟨'>', _, rfl, rfl⟩) (fuel + 1) hc
  rcases r with ⟨ty, name, count⟩
  simp only [Nat.toList_repr] at ht hp hc
  simp [parsePTXRegDecl, toString, String.toList_append, List.append_assoc,
    stripPrefixChars, ht, hp, hc, Nat.toNat?_repr]

theorem parsePTXSharedDecl_roundtrip (s : PTXSharedDecl)
    (hn : CanonicalPTXName s.name) (rest : List Char)
    (fuel : Nat) (hf : s.name.toList.length < fuel + 1)
    (ha : s.align.repr.toList.length < fuel + 1)
    (hc : s.count.repr.toList.length < fuel + 1) :
    parsePTXSharedDecl (fuel + 1)
      ((s!"    .shared .align {s.align} {ppPTXType s.elemTy} {s.name}[{s.count}];").toList ++ rest) =
      some (s, rest) := by
  have ha := parsePTXName_nat_roundtrip s.align
    (' ' :: ((ppPTXType s.elemTy).toList ++ ' ' :: (s.name.toList ++ '[' ::
      (s.count.repr.toList ++ ']' :: ';' :: rest))))
    (Or.inr ⟨' ', _, rfl, rfl⟩) (fuel + 1) ha
  have ht := parsePTXType_roundtrip s.elemTy fuel
    (' ' :: (s.name.toList ++ '[' :: (s.count.repr.toList ++ ']' :: ';' :: rest)))
  have hp := parsePTXName_roundtrip s.name hn
    ('[' :: (s.count.repr.toList ++ ']' :: ';' :: rest))
    (Or.inr ⟨'[', _, rfl, rfl⟩) (fuel + 1) hf
  have hc := parsePTXName_nat_roundtrip s.count (']' :: ';' :: rest)
    (Or.inr ⟨']', _, rfl, rfl⟩) (fuel + 1) hc
  rcases s with ⟨align, ty, name, count⟩
  simp only [Nat.toList_repr] at ha ht hp hc
  simp [parsePTXSharedDecl, toString, String.toList_append, List.append_assoc,
    stripPrefixChars, ha, ht, hp, hc, Nat.toNat?_repr]

theorem parsePTXStmt_ret_roundtrip (rest : List Char) :
    parsePTXStmt 8 ((ppPTXStmt (.instr none .ret)).toList ++ rest) =
      some (.instr none .ret, rest) := by
  simp [parsePTXStmt, ppPTXStmt, parsePTXInstr, ppPTXInstr,
    parsePTXName, scanPTXName, ptxNameChar, stripPrefixChars, toString]

theorem parsePTXStmt_label_roundtrip (name : String) (hn : CanonicalPTXName name)
    (rest : List Char) (fuel : Nat) (hf : name.toList.length < fuel) :
    parsePTXStmt fuel ((ppPTXStmt (.label name)).toList ++ rest) =
      some (.label name, rest) := by
  have hp := parsePTXName_roundtrip name hn (':' :: rest)
    (Or.inr ⟨':', rest, rfl, rfl⟩) fuel hf
  cases he : name.toList with
  | nil => exact False.elim (hn.1 he)
  | cons c cs =>
    have hc := hn.2 c (by simp [he])
    have hspace : c ≠ ' ' := by intro h; subst c; contradiction
    simp only [ppPTXStmt, toString, String.toList_append, String.reduceToList,
      List.append_assoc, List.cons_append, List.nil_append]
    have hi : stripPrefixChars [' ', ' ', ' ', ' '] (name.toList ++ ':' :: rest) = none := by
      simp [he, stripPrefixChars, Ne.symm hspace]
    simp [parsePTXStmt, hi, hp, stripPrefixChars]

theorem ppPTXType_injective_via_parser : Function.Injective ppPTXType := by
  intro a b h
  have hp := congrArg (fun s : String => parsePTXType 1 (s.toList ++ [])) h
  simpa only [parsePTXType_roundtrip, Option.some.injEq, Prod.mk.injEq, and_true] using hp

theorem ppPTXType_injective (t1 t2 : PTXType) (h : ppPTXType t1 = ppPTXType t2) :
     t1 = t2 := by
  exact ppPTXType_injective_via_parser h

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
theorem stepCTABarrier_allows_ret_exited_threads (bid : Nat)
    (thRet thBar : PTXThreadState) (cta : PTXCTAState)
    (hThreads : cta.threads = [thRet, thBar])
    (hRet : threadExitedByRet thRet = true)
    (hBarUnhalted : thBar.halted = false) :
    stepCTABarrierGen bid [none, some bid] cta =
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

/-- Skipping a predicated `@%p0 ret` (`%p0 = false`) at the end of `stmts` causes the thread to
    fall off the end (`fellOffEnd = true`, `threadExitedByRet = false`), so `stepCTABarrierGen`
    traps with `.barrierDivergence bid` instead of treating the fallen-off thread as `ret`-exited;
    verified both symbolically and on a concrete 2-thread kernel under `evalPTXKernel` and
    `evalPTXKernelWithOracle`. -/
theorem stepCTABarrier_skipped_pred_ret_falloff_traps (bid : Nat)
    (thFell thBar : PTXThreadState) (cta : PTXCTAState)
    (hThreads : cta.threads = [thFell, thBar])
    (hFell : thFell.fellOffEnd = true) :
    stepCTABarrierGen bid [none, some bid] cta = .barrierDivergence bid ∧
      evalPTXKernel 32
        { name := "skipped_pred_ret_falloff"
        , params := []
        , regDecls := [ { ty := .u32, prefixName := "%r", count := 1 }
                      , { ty := .pred, prefixName := "%p", count := 2 } ]
        , body :=
            [ .instr none (.mov .u32 "%r0" (.sreg .tidX))
            , .instr none (.setp .eq .u32 "%p0" (.reg "%r0") (.immU64 0#64))
            , .instr (some { predReg := "%p0", negated := true }) (.bra "AT_BAR")
            , .instr none (.bra "END_SKIP_RET")
            , .label "AT_BAR"
            , .instr none (.barSync 0)
            , .instr none .ret
            , .label "END_SKIP_RET"
            , .instr none (.setp .eq .u32 "%p1" (.immU64 1#64) (.immU64 0#64))
            , .instr (some { predReg := "%p1" }) .ret ] }
        { x := 1 } { x := 2 }
        (ByteMemory.zeros 0)
        { params := [] } = .barrierDivergence 0 ∧
      evalPTXKernelWithOracle none 32
        { name := "skipped_pred_ret_falloff"
        , params := []
        , regDecls := [ { ty := .u32, prefixName := "%r", count := 1 }
                      , { ty := .pred, prefixName := "%p", count := 2 } ]
        , body :=
            [ .instr none (.mov .u32 "%r0" (.sreg .tidX))
            , .instr none (.setp .eq .u32 "%p0" (.reg "%r0") (.immU64 0#64))
            , .instr (some { predReg := "%p0", negated := true }) (.bra "AT_BAR")
            , .instr none (.bra "END_SKIP_RET")
            , .label "AT_BAR"
            , .instr none (.barSync 0)
            , .instr none .ret
            , .label "END_SKIP_RET"
            , .instr none (.setp .eq .u32 "%p1" (.immU64 1#64) (.immU64 0#64))
            , .instr (some { predReg := "%p1" }) .ret ] }
        { x := 1 } { x := 2 }
        (ByteMemory.zeros 0)
        { params := [] } = .barrierDivergence 0 := by
  refine ⟨?_, rfl, rfl⟩
  unfold stepCTABarrierGen
  rw [hThreads]
  simp [barrierParticipantsConverged, threadExitedByRet, hFell]

/-- Divergent barrier IDs (`b1 ≠ b2`) across active CTA threads trap with `.barrierDivergence b1`. -/
theorem stepCTABarrier_divergent_barriers_trap (b1 b2 : Nat)
    (th1 th2 : PTXThreadState) (cta : PTXCTAState)
    (hNe : b1 ≠ b2)
    (hThreads : cta.threads = [th1, th2]) :
    stepCTABarrierGen b1 [some b1, some b2] cta = .barrierDivergence b1 := by
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
theorem stepCTABarrier_advances_generation_and_clears_epoch (bid : Nat)
    (states : List (Option Nat)) (cta : PTXCTAState)
    (hConv : barrierParticipantsConverged bid cta.threads states = true) :
    ∃ cta' : PTXCTAState,
      stepCTABarrierGen bid states cta = .ok cta' ∧
      cta'.epochLog = [] ∧
      lookupBarrierEpoch cta'.barrierGen bid = lookupBarrierEpoch cta.barrierGen bid + 1 := by
  refine ⟨{ cta with
    threads := advanceBarrierParticipants bid cta.threads states
    epochLog := []
    barrierGen := bumpBarrierGen cta.barrierGen bid }, ?_, rfl, ?_⟩
  · unfold stepCTABarrierGen
    simp [hConv]
  · exact lookup_bumpBarrierGen_same cta.barrierGen bid

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

private theorem seqCand_step_lt
    {initMem : Nat → StateSpace → Nat → Option (BitVec 64)}
    {evs : List PTXMemEvent}
    (hWf : wfSequentialEventTrace initMem evs)
    {a b : Nat}
    (hStep : (sequentialCandidateOfEvents evs).poOrSw a b) :
    a < b := by
  rcases hWf with ⟨_, hPoLt, hBarLt, hKernLt, _⟩
  rcases hStep with hPo | hSw
  · rcases hPo with ⟨ea, eb, hFa, hFb, hK, hC, hT, hSeq⟩
    rcases find_eventId_mem_and_eq hFa with ⟨hMa, hEaId⟩
    rcases find_eventId_mem_and_eq hFb with ⟨hMb, hEbId⟩
    rw [← hEaId, ← hEbId]
    exact hPoLt ea eb hMa hMb hK hC hT hSeq
  · rcases hSw with ⟨ea, eb, hFa, hFb, hKind⟩
    rcases find_eventId_mem_and_eq hFa with ⟨hMa, hEaId⟩
    rcases find_eventId_mem_and_eq hFb with ⟨hMb, hEbId⟩
    rw [← hEaId, ← hEbId]
    rcases hKind with ⟨hK, hC, hDiff, bid, hEpoch⟩ | ⟨hSpA, hSpB, hWrA, hKLt⟩
    · exact hBarLt ea eb bid hMa hMb hK hC hDiff hEpoch
    · exact hKernLt ea eb hMa hMb hSpA hSpB hWrA hKLt

private theorem seqCand_hb_lt
    {initMem : Nat → StateSpace → Nat → Option (BitVec 64)}
    {evs : List PTXMemEvent}
    (hWf : wfSequentialEventTrace initMem evs)
    {a b : Nat}
    (hHb : (sequentialCandidateOfEvents evs).hb a b) :
    a < b := by
  induction hHb with
  | single hs => exact seqCand_step_lt hWf hs
  | tail _ hs ih => exact Nat.lt_trans ih (seqCand_step_lt hWf hs)

/-- Canonical `sequentialCandidateOfEvents` soundness (`D6`):
    every well-formed sequential `PTXMemEvent` trace `evs` satisfies `PTXAxiomaticConsistent`
    (including `po_wf` on `poSeq`, `po_irrefl`, `po_trans`, `po_complete`, `hb_irrefl`, `rf`/`co`/`fr`
    coherence, and RMW atomicity). -/
theorem sequentialCandidateOfEvents_consistent
    (initMem : Nat → StateSpace → Nat → Option (BitVec 64))
    (evs : List PTXMemEvent)
    (hWf : wfSequentialEventTrace initMem evs) :
    PTXAxiomaticConsistent initMem (sequentialCandidateOfEvents evs) := by
  have hWfCopy := hWf
  rcases hWf with ⟨hNodup, _, _, _, hReadWf⟩
  refine
    { eventIds_nodup := hNodup
      po_wf := ?_
      po_irrefl := ?_
      po_trans := ?_
      po_complete := ?_
      sw_cta_barrier := ?_
      sw_inter_kernel := ?_
      hb_irrefl := ?_
      rf_wf := ?_
      rf_complete := ?_
      co_wf := ?_
      co_irrefl := ?_
      co_trans := ?_
      co_total := ?_
      coh_ww := ?_
      coh_wr := ?_
      coh_rw := ?_
      coh_vrw := ?_
      rmw_atomicity := ?_ }
  · intro a b hPo
    exact hPo
  · intro a hPo
    rcases hPo with ⟨ea, eb, hFa, hFb, _, _, _, hSeq⟩
    have hEq : ea = eb := Option.some.inj (hFa.symm.trans hFb)
    rw [hEq] at hSeq
    exact Nat.lt_irrefl _ hSeq
  · intro a b c hAB hBC
    rcases hAB with ⟨ea, eb, hFa, hFb, hK1, hC1, hT1, hS1⟩
    rcases hBC with ⟨eb', ec, hFb', hFc, hK2, hC2, hT2, hS2⟩
    have hEbEq : eb' = eb := Option.some.inj (hFb'.symm.trans hFb)
    rw [hEbEq] at hK2 hC2 hT2 hS2
    exact ⟨ea, ec, hFa, hFc, hK1.trans hK2, hC1.trans hC2, hT1.trans hT2, Nat.lt_trans hS1 hS2⟩
  · intro ea eb hMa hMb hK hC hT hSeq
    exact ⟨ea, eb, hasEvent_eq_self_of_nodup hNodup hMa,
      hasEvent_eq_self_of_nodup hNodup hMb, hK, hC, hT, hSeq⟩
  · intro ea eb bid hMa hMb hK hC hDiff hGen
    exact ⟨ea, eb, hasEvent_eq_self_of_nodup hNodup hMa,
      hasEvent_eq_self_of_nodup hNodup hMb, Or.inl ⟨hK, hC, hDiff, bid, hGen⟩⟩
  · intro ea eb hMa hMb hSpA hSpB hWrA hKLt
    exact ⟨ea, eb, hasEvent_eq_self_of_nodup hNodup hMa,
      hasEvent_eq_self_of_nodup hNodup hMb, Or.inr ⟨hSpA, hSpB, hWrA, hKLt⟩⟩
  · intro a hHb
    exact Nat.lt_irrefl a (seqCand_hb_lt hWfCopy hHb)
  · intro w r hRf
    rcases hRf with ⟨er, hFr, hRd, hLatest⟩
    rcases find_eventId_mem_and_eq hFr with ⟨hMr, hErId⟩
    have hRw := hReadWf er hMr hRd
    rw [hLatest] at hRw
    rcases hRw with ⟨ew, hFw, hWrW, hSame, hVal, hLt, _⟩
    rw [hErId] at hLt
    exact ⟨ew, er, hFw, hFr, hWrW, hRd, hSame, hVal, Nat.ne_of_lt hLt⟩
  · intro er hMr hRd
    have hFr : evs.find? (fun x => x.eventId == er.eventId) = some er :=
      hasEvent_eq_self_of_nodup hNodup hMr
    have hRw := hReadWf er hMr hRd
    cases hLat : latestPriorWriteId? evs er with
    | some wId =>
      left
      refine ⟨wId, ⟨er, hFr, hRd, hLat⟩, ?_⟩
      intro w' hRf'
      rcases hRf' with ⟨er', hFr', _, hLat'⟩
      have hEq : er' = er := Option.some.inj (hFr'.symm.trans hFr)
      rw [hEq, hLat] at hLat'
      exact (Option.some.inj hLat').symm
    | none =>
      rw [hLat] at hRw
      right
      refine ⟨?_, hRw.1⟩
      rintro ⟨w, er', hFr', _, hLat'⟩
      have hEq : er' = er := Option.some.inj (hFr'.symm.trans hFr)
      rw [hEq, hLat] at hLat'
      nomatch hLat'
  · intro w1 w2 hCo
    rcases hCo with ⟨e1, e2, hF1, hF2, hW1, hW2, hSame, hLt⟩
    exact ⟨e1, e2, hF1, hF2, hW1, hW2, hSame, Nat.ne_of_lt hLt⟩
  · intro w hCo
    rcases hCo with ⟨_, _, _, _, _, _, _, hLt⟩
    exact Nat.lt_irrefl _ hLt
  · intro w1 w2 w3 h12 h23
    rcases h12 with ⟨e1, e2, hF1, hF2, hW1, _, hS12, hLt12⟩
    rcases h23 with ⟨e2', e3, hF2', hF3, _, hW3, hS23, hLt23⟩
    have hE2Eq : e2' = e2 := Option.some.inj (hF2'.symm.trans hF2)
    rw [hE2Eq] at hS23
    exact ⟨e1, e3, hF1, hF3, hW1, hW3, sameLoc_trans hS12 hS23, Nat.lt_trans hLt12 hLt23⟩
  · intro e1 e2 hM1 hM2 hW1 hW2 hSame hNe
    have hF1 := hasEvent_eq_self_of_nodup hNodup hM1
    have hF2 := hasEvent_eq_self_of_nodup hNodup hM2
    rcases Nat.lt_or_gt_of_ne hNe with hLt | hGt
    · exact Or.inl ⟨e1, e2, hF1, hF2, hW1, hW2, hSame, hLt⟩
    · exact Or.inr ⟨e2, e1, hF2, hF1, hW2, hW1, sameLoc_symm hSame, hGt⟩
  · intro w1 w2 hWrites hHb
    rcases hWrites with ⟨e1, e2, hF1, hF2, hW1, hW2, hSame⟩
    exact ⟨e1, e2, hF1, hF2, hW1, hW2, hSame, seqCand_hb_lt hWfCopy hHb⟩
  · intro w r hRf hHb
    rcases hRf with ⟨er, hFr, hRd, hLat⟩
    rcases find_eventId_mem_and_eq hFr with ⟨hMr, hErId⟩
    have hRw := hReadWf er hMr hRd
    rw [hLat] at hRw
    rcases hRw with ⟨_, _, _, _, _, hLtWR, _⟩
    rw [hErId] at hLtWR
    exact Nat.lt_asymm hLtWR (seqCand_hb_lt hWfCopy hHb)
  · intro r w hFrRel hHb
    have hLtWR : w < r := seqCand_hb_lt hWfCopy hHb
    rcases hFrRel with ⟨w0, hRf0, hCo0⟩ | ⟨hNoRf, er, ew, hFr, hFw, hRd, hWrW, hSameRW, _⟩
    · rcases hRf0 with ⟨er, hFr, hRd, hLat⟩
      rcases find_eventId_mem_and_eq hFr with ⟨hMr, hErId⟩
      rcases hCo0 with ⟨ew0, ew, hFw0, hFw, _, hWrW, hSame0W, hLt0W⟩
      rcases find_eventId_mem_and_eq hFw with ⟨hMw, hEwId⟩
      have hRw := hReadWf er hMr hRd
      rw [hLat] at hRw
      rcases hRw with ⟨ew0', hFw0', _, hSame0R, _, _, hMax⟩
      have hEw0Eq : ew0' = ew0 := Option.some.inj (hFw0'.symm.trans hFw0)
      rw [hEw0Eq] at hSame0R
      have hSameWR : PTXCandidateExecution.sameLoc ew er :=
        sameLoc_trans (sameLoc_symm hSame0W) hSame0R
      have hEwLtEr : ew.eventId < er.eventId := by omega
      have hLe : ew.eventId ≤ w0 := hMax ew hMw hWrW hSameWR hEwLtEr
      omega
    · rcases find_eventId_mem_and_eq hFr with ⟨hMr, hErId⟩
      rcases find_eventId_mem_and_eq hFw with ⟨hMw, hEwId⟩
      have hRw := hReadWf er hMr hRd
      cases hLat : latestPriorWriteId? evs er with
      | some wId =>
        have hFrSelf : evs.find? (fun x => x.eventId == er.eventId) = some er :=
          hasEvent_eq_self_of_nodup hNodup hMr
        have hRfEx : (sequentialCandidateOfEvents evs).rf wId r := by
          rw [← hErId]
          exact ⟨er, hFrSelf, hRd, hLat⟩
        exact hNoRf ⟨wId, hRfEx⟩
      | none =>
        rw [hLat] at hRw
        have hEwLtEr : ew.eventId < er.eventId := by omega
        exact hRw.2 ew hMw hWrW (sameLoc_symm hSameRW) hEwLtEr
  · intro w1 w2 r hRf hCo hHb
    have hLtW2R : w2 < r := seqCand_hb_lt hWfCopy hHb
    rcases hRf with ⟨er, hFr, hRd, hLat⟩
    rcases find_eventId_mem_and_eq hFr with ⟨hMr, hErId⟩
    rcases hCo with ⟨ew1, ew2, hFw1, hFw2, _, hWrW2, hSame12, hLt12⟩
    rcases find_eventId_mem_and_eq hFw2 with ⟨hMw2, hEw2Id⟩
    have hRw := hReadWf er hMr hRd
    rw [hLat] at hRw
    rcases hRw with ⟨ew1', hFw1', _, hSame1R, _, _, hMax⟩
    have hEw1Eq : ew1' = ew1 := Option.some.inj (hFw1'.symm.trans hFw1)
    rw [hEw1Eq] at hSame1R
    have hSame2R : PTXCandidateExecution.sameLoc ew2 er :=
      sameLoc_trans (sameLoc_symm hSame12) hSame1R
    have hEw2LtEr : ew2.eventId < er.eventId := by omega
    have hLe : ew2.eventId ≤ w1 := hMax ew2 hMw2 hWrW2 hSame2R hEw2LtEr
    omega
  · intro e hMe _ hRd hWr
    have hFe : evs.find? (fun x => x.eventId == e.eventId) = some e :=
      hasEvent_eq_self_of_nodup hNodup hMe
    have hRw := hReadWf e hMe hRd
    refine ⟨?_, ?_⟩
    · intro w hRf
      rcases hRf with ⟨er', hFr', _, hLat⟩
      have hEq : er' = e := Option.some.inj (hFr'.symm.trans hFe)
      rw [hEq] at hLat
      rw [hLat] at hRw
      rcases hRw with ⟨ew, hFw, hWrW, hSame, _, hLt, hMax⟩
      refine ⟨⟨ew, e, hFw, hFe, hWrW, hWr, hSame, hLt⟩, ?_⟩
      rintro ⟨wMid, hCo1, hCo2⟩
      rcases hCo1 with ⟨_, eMid, _, hFMid, _, hWrMid, _, hLt1⟩
      rcases hCo2 with ⟨eMid', e', hFMid', hFe', _, _, hSameMidE, hLt2⟩
      have hMidEq : eMid' = eMid := Option.some.inj (hFMid'.symm.trans hFMid)
      have hEEq : e' = e := Option.some.inj (hFe'.symm.trans hFe)
      rw [hMidEq, hEEq] at hSameMidE
      rcases find_eventId_mem_and_eq hFMid with ⟨hMMid, hMidId⟩
      have hMidLtE : eMid.eventId < e.eventId := by omega
      have hLe : eMid.eventId ≤ w := hMax eMid hMMid hWrMid hSameMidE hMidLtE
      omega
    · intro hNoRf ⟨wPre, hCoPre⟩
      cases hLat : latestPriorWriteId? evs e with
      | some wId =>
        exact hNoRf ⟨wId, e, hFe, hRd, hLat⟩
      | none =>
        rw [hLat] at hRw
        rcases hCoPre with ⟨ePre, e', hFPre, hFe', hWrPre, _, hSamePre, hLtPre⟩
        have hEEq : e' = e := Option.some.inj (hFe'.symm.trans hFe)
        rw [hEEq] at hSamePre
        rcases find_eventId_mem_and_eq hFPre with ⟨hMPre, hPreId⟩
        have hPreLt : ePre.eventId < e.eventId := by omega
        exact hRw.2 ePre hMPre hWrPre hSamePre hPreLt

/-- Concrete multi-event `sequentialCandidateOfEvents` consistency witness (`D6`):
    executing a 2-thread CTA kernel where thread 0 writes `41#64` to `.shared`, synchronizes via
    `bar.sync 0`, and thread 1 reads `.shared` (`poSeq = 0`) then writes `42#64` to `.global`
    (`poSeq = 1`) produces a 3-event trace `evs` whose `sequentialCandidateOfEvents evs` satisfies
    `PTXAxiomaticConsistent` with non-empty `po` (`1 -> 2`) and `sw` (`0 -> 1`, `0 -> 2`). -/
theorem sequentialCandidateOfEvents_multi_event_nonvacuous :
    let k : PTXKernel :=
      { name := "seq_cand_po_sw_demo"
      , params := [ { ty := .u64, name := "out" } ]
      , sharedDecls := [ { align := 8, elemTy := .u64, name := "smem", count := 1 } ]
      , regDecls := [ { ty := .u32, prefixName := "%r", count := 1 }
                    , { ty := .u64, prefixName := "%rd", count := 2 }
                    , { ty := .pred, prefixName := "%p", count := 2 } ]
      , body :=
          [ .instr none (.mov .u32 "%r0" (.sreg .tidX))
          , .instr none (.setp .eq .u32 "%p0" (.reg "%r0") (.immU64 0#64))
          , .instr (some { predReg := "%p0" })
              (.stShared .u64 (.symOffset "smem" 0) (.immU64 41#64))
          , .instr none (.barSync 0)
          , .instr none (.setp .eq .u32 "%p1" (.reg "%r0") (.immU64 1#64))
          , .instr (some { predReg := "%p1", negated := true }) .ret
          , .instr none (.ldShared .u64 "%rd0" (.symOffset "smem" 0))
          , .instr none (.add .none .u64 "%rd0" (.reg "%rd0") (.immU64 1#64))
          , .instr none (.ldParam .u64 "%rd1" "out")
          , .instr none (.stGlobal .u64 (.regOffset "%rd1" 0) (.reg "%rd0"))
          , .instr none .ret ] }
    let g0 := ByteMemory.ofU64Words [ 0#64 ]
    ∃ gFinal evs,
      evalPTXKernelWithOracle none 32 k { x := 1 } { x := 2 } g0
        { params := [ ("out", 0#64) ] } = .ok (gFinal, evs) ∧
      gFinal.loadBits 0 8 = some 42#64 ∧
      evs.length = 3 ∧
      PTXAxiomaticConsistent (initMemOfGlobal g0) (sequentialCandidateOfEvents evs) ∧
      (sequentialCandidateOfEvents evs).po 1 2 ∧
      (sequentialCandidateOfEvents evs).sw 0 1 := by
  dsimp only
  let e0 : PTXMemEvent :=
    { eventId := 0
      kernelIdx := 0
      ctaId := { x := 0, y := 0, z := 0 }
      tid := { x := 0, y := 0, z := 0 }
      barrierEpoch := []
      space := .shared
      addr := 0
      width := 8
      isRead := false
      isWrite := true
      isAtomic := false
      valRead := 0#64
      valWritten := 41#64
      poSeq := 0 }
  let e1 : PTXMemEvent :=
    { eventId := 1
      kernelIdx := 0
      ctaId := { x := 0, y := 0, z := 0 }
      tid := { x := 1, y := 0, z := 0 }
      barrierEpoch := [(0, 1)]
      space := .shared
      addr := 0
      width := 8
      isRead := true
      isWrite := false
      isAtomic := false
      valRead := 41#64
      valWritten := 0#64
      poSeq := 0 }
  let e2 : PTXMemEvent :=
    { eventId := 2
      kernelIdx := 0
      ctaId := { x := 0, y := 0, z := 0 }
      tid := { x := 1, y := 0, z := 0 }
      barrierEpoch := [(0, 1)]
      space := .global
      addr := 0
      width := 8
      isRead := false
      isWrite := true
      isAtomic := false
      valRead := 0#64
      valWritten := 42#64
      poSeq := 1 }
  refine ⟨ByteMemory.ofU64Words [ 42#64 ], [e0, e1, e2], rfl, rfl, rfl, ?_, ?_, ?_⟩
  · apply sequentialCandidateOfEvents_consistent
    refine ⟨by decide, ?_, ?_, ?_, ?_⟩
    · intro ea eb hMa hMb hK hC hT hSeq
      rcases List.mem_cons.mp hMa with rfl | hMa1
      · rcases List.mem_cons.mp hMb with rfl | hMb1
        · exfalso; revert hSeq; decide
        · rcases List.mem_cons.mp hMb1 with rfl | hMb2
          · decide
          · rcases List.mem_singleton.mp hMb2 with rfl
            decide
      · rcases List.mem_cons.mp hMa1 with rfl | hMa2
        · rcases List.mem_cons.mp hMb with rfl | hMb1
          · exfalso; revert hT; decide
          · rcases List.mem_cons.mp hMb1 with rfl | hMb2
            · exfalso; revert hSeq; decide
            · rcases List.mem_singleton.mp hMb2 with rfl
              decide
        · rcases List.mem_singleton.mp hMa2 with rfl
          rcases List.mem_cons.mp hMb with rfl | hMb1
          · exfalso; revert hT; decide
          · rcases List.mem_cons.mp hMb1 with rfl | hMb2
            · exfalso; revert hSeq; decide
            · rcases List.mem_singleton.mp hMb2 with rfl
              exfalso; revert hSeq; decide
    · intro ea eb bid hMa hMb _ _ hDiff hGen
      rcases List.mem_cons.mp hMa with rfl | hMa1
      · rcases List.mem_cons.mp hMb with rfl | hMb1
        · exact False.elim (hDiff rfl)
        · rcases List.mem_cons.mp hMb1 with rfl | hMb2
          · decide
          · rcases List.mem_singleton.mp hMb2 with rfl
            decide
      · rcases List.mem_cons.mp hMa1 with rfl | hMa2
        · rcases List.mem_cons.mp hMb with rfl | hMb1
          · exfalso
            simp [e0, e1, lookupBarrierEpoch] at hGen
          · rcases List.mem_cons.mp hMb1 with rfl | hMb2
            · exact False.elim (hDiff rfl)
            · rcases List.mem_singleton.mp hMb2 with rfl
              exact False.elim (hDiff rfl)
        · rcases List.mem_singleton.mp hMa2 with rfl
          rcases List.mem_cons.mp hMb with rfl | hMb1
          · exfalso
            simp [e0, e2, lookupBarrierEpoch] at hGen
          · rcases List.mem_cons.mp hMb1 with rfl | hMb2
            · exact False.elim (hDiff rfl)
            · rcases List.mem_singleton.mp hMb2 with rfl
              exact False.elim (hDiff rfl)
    · intro ea eb hMa hMb _ _ _ hKLt
      have hKa : ea.kernelIdx = 0 := by
        rcases List.mem_cons.mp hMa with rfl | h1
        · rfl
        · rcases List.mem_cons.mp h1 with rfl | h2
          · rfl
          · rw [List.mem_singleton.mp h2]
      have hKb : eb.kernelIdx = 0 := by
        rcases List.mem_cons.mp hMb with rfl | h1
        · rfl
        · rcases List.mem_cons.mp h1 with rfl | h2
          · rfl
          · rw [List.mem_singleton.mp h2]
      omega
    · intro er hMr hRd
      rcases List.mem_cons.mp hMr with rfl | hMr1
      · nomatch hRd
      · rcases List.mem_cons.mp hMr1 with rfl | hMr2
        · refine ⟨e0, rfl, rfl, ⟨rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩, rfl, by decide, ?_⟩
          intro em hMm hWrM _ hLtM
          rcases List.mem_cons.mp hMm with rfl | hMm1
          · decide
          · rcases List.mem_cons.mp hMm1 with rfl | hMm2
            · nomatch hWrM
            · rcases List.mem_singleton.mp hMm2 with rfl
              exfalso; revert hLtM; decide
        · rcases List.mem_singleton.mp hMr2 with rfl
          nomatch hRd
  · exact ⟨e1, e2, rfl, rfl, rfl, rfl, rfl, by decide⟩
  · exact ⟨e0, e1, rfl, rfl, Or.inl ⟨rfl, rfl, by decide, 0, by decide⟩⟩

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

private theorem isImmediateCoChain_tail {cand : PTXCandidateExecution}
    {a b : PTXMemEvent} {rest : List PTXMemEvent}
    (h : isImmediateCoChain cand (a :: b :: rest)) :
    cand.co a.eventId b.eventId ∧
      (¬ ∃ wMid : Nat, cand.co a.eventId wMid ∧ cand.co wMid b.eventId) ∧
      isImmediateCoChain cand (b :: rest) :=
  h

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

private theorem twoEventRev_no_hb {eSec eFst : PTXMemEvent} {a b : Nat}
    (hHb : (twoEventReversedRmwCandidate eSec eFst).hb a b) : False := by
  induction hHb with
  | single hs =>
    rcases hs with hPo | hSw
    · exact hPo
    · exact hSw
  | tail _ _ ih =>
    exact ih

/-- Concrete cross-CTA relaxed `atom.add.global.u64` non-vacuity & commutativity witness (`D6`):
    the recorded RMW events of the sequential schedule (`5#64 → 24#64`, `24#64 → 47#64`) and of the
    reversed read-oracle schedule (`28#64 → 47#64`, `5#64 → 28#64`) are `PTXAxiomaticConsistent`
    (`sequentialCandidateOfEvents` and `twoEventReversedRmwCandidate`). Both immediate `co` chains
    instantiate `ptx_relaxed_atom_add_co_no_lost_updates` to write `5#64 + 19#64 + 23#64 = 47#64`.
    The matching `evalPTXKernelWithOracle` / `evalPTXKernelWithCTAOrder` runs (fuel `8`) are
    `ptx_relaxed_cross_cta_atom_add_exec`. -/
theorem ptx_relaxed_cross_cta_atom_add_commutes :
    let g0 := ByteMemory.ofU64Words [ 5#64 ]
    let e0Seq : PTXMemEvent :=
      { eventId := 0, kernelIdx := 0, ctaId := { x := 0, y := 0, z := 0 }
      , tid := { x := 0, y := 0, z := 0 }, barrierEpoch := [], space := .global
      , addr := 0, width := 8, isRead := true, isWrite := true, isAtomic := true
      , valRead := 5#64, valWritten := 24#64, poSeq := 0 }
    let e1Seq : PTXMemEvent :=
      { eventId := 1, kernelIdx := 0, ctaId := { x := 1, y := 0, z := 0 }
      , tid := { x := 0, y := 0, z := 0 }, barrierEpoch := [], space := .global
      , addr := 0, width := 8, isRead := true, isWrite := true, isAtomic := true
      , valRead := 24#64, valWritten := 47#64, poSeq := 0 }
    let e0Rev : PTXMemEvent :=
      { eventId := 0, kernelIdx := 0, ctaId := { x := 0, y := 0, z := 0 }
      , tid := { x := 0, y := 0, z := 0 }, barrierEpoch := [], space := .global
      , addr := 0, width := 8, isRead := true, isWrite := true, isAtomic := true
      , valRead := 28#64, valWritten := 47#64, poSeq := 0 }
    let e1Rev : PTXMemEvent :=
      { eventId := 1, kernelIdx := 0, ctaId := { x := 1, y := 0, z := 0 }
      , tid := { x := 0, y := 0, z := 0 }, barrierEpoch := [], space := .global
      , addr := 0, width := 8, isRead := true, isWrite := true, isAtomic := true
      , valRead := 5#64, valWritten := 28#64, poSeq := 0 }
    (PTXAxiomaticConsistent (initMemOfGlobal g0) (sequentialCandidateOfEvents [e0Seq, e1Seq]) ∧
      isImmediateCoChain (sequentialCandidateOfEvents [e0Seq, e1Seq]) [e0Seq, e1Seq] ∧
      e1Seq.valWritten = 5#64 + sumAtomAddDeltas [e0Seq, e1Seq] ∧
      e1Seq.valWritten = 47#64) ∧
    (PTXAxiomaticConsistent (initMemOfGlobal g0) (twoEventReversedRmwCandidate e0Rev e1Rev) ∧
      isImmediateCoChain (twoEventReversedRmwCandidate e0Rev e1Rev) [e1Rev, e0Rev] ∧
      e0Rev.valWritten = 5#64 + sumAtomAddDeltas [e1Rev, e0Rev] ∧
      e0Rev.valWritten = 47#64) := by
  have hInit5 : initMemOfGlobal (ByteMemory.ofU64Words [ 5#64 ]) 0 .global 8 = some 5#64 := rfl
  let g0 := ByteMemory.ofU64Words [ 5#64 ]
  let e0Seq : PTXMemEvent :=
    { eventId := 0
      kernelIdx := 0
      ctaId := { x := 0, y := 0, z := 0 }
      tid := { x := 0, y := 0, z := 0 }
      barrierEpoch := []
      space := .global
      addr := 0
      width := 8
      isRead := true
      isWrite := true
      isAtomic := true
      valRead := 5#64
      valWritten := 24#64
      poSeq := 0 }
  let e1Seq : PTXMemEvent :=
    { eventId := 1
      kernelIdx := 0
      ctaId := { x := 1, y := 0, z := 0 }
      tid := { x := 0, y := 0, z := 0 }
      barrierEpoch := []
      space := .global
      addr := 0
      width := 8
      isRead := true
      isWrite := true
      isAtomic := true
      valRead := 24#64
      valWritten := 47#64
      poSeq := 0 }
  let e0Rev : PTXMemEvent :=
    { eventId := 0
      kernelIdx := 0
      ctaId := { x := 0, y := 0, z := 0 }
      tid := { x := 0, y := 0, z := 0 }
      barrierEpoch := []
      space := .global
      addr := 0
      width := 8
      isRead := true
      isWrite := true
      isAtomic := true
      valRead := 28#64
      valWritten := 47#64
      poSeq := 0 }
  let e1Rev : PTXMemEvent :=
    { eventId := 1
      kernelIdx := 0
      ctaId := { x := 1, y := 0, z := 0 }
      tid := { x := 0, y := 0, z := 0 }
      barrierEpoch := []
      space := .global
      addr := 0
      width := 8
      isRead := true
      isWrite := true
      isAtomic := true
      valRead := 5#64
      valWritten := 28#64
      poSeq := 0 }
  refine ⟨?_, ?_⟩
  · have hConsSeq : PTXAxiomaticConsistent (initMemOfGlobal g0)
        (sequentialCandidateOfEvents [e0Seq, e1Seq]) := by
      apply sequentialCandidateOfEvents_consistent
      refine ⟨by decide, ?_, ?_, ?_, ?_⟩
      · intro ea eb hMa hMb _ _ _ hSeq
        have hPa : ea.poSeq = 0 := by
          rcases List.mem_cons.mp hMa with rfl | h1
          · rfl
          · rw [List.mem_singleton.mp h1]
        have hPb : eb.poSeq = 0 := by
          rcases List.mem_cons.mp hMb with rfl | h1
          · rfl
          · rw [List.mem_singleton.mp h1]
        omega
      · intro ea eb _ hMa hMb _ hC hDiff _
        rcases List.mem_cons.mp hMa with rfl | hMa1
        · rcases List.mem_cons.mp hMb with rfl | hMb1
          · exact False.elim (hDiff rfl)
          · rcases List.mem_singleton.mp hMb1 with rfl
            nomatch hC
        · rcases List.mem_singleton.mp hMa1 with rfl
          rcases List.mem_cons.mp hMb with rfl | hMb1
          · nomatch hC
          · rcases List.mem_singleton.mp hMb1 with rfl
            exact False.elim (hDiff rfl)
      · intro ea eb hMa hMb _ _ _ hKLt
        have hKa : ea.kernelIdx = 0 := by
          rcases List.mem_cons.mp hMa with rfl | h1
          · rfl
          · rw [List.mem_singleton.mp h1]
        have hKb : eb.kernelIdx = 0 := by
          rcases List.mem_cons.mp hMb with rfl | h1
          · rfl
          · rw [List.mem_singleton.mp h1]
        omega
      · intro er hMr _
        rcases List.mem_cons.mp hMr with rfl | hMr1
        · refine ⟨hInit5, ?_⟩
          intro em hMm _ _ hLtM
          rcases List.mem_cons.mp hMm with rfl | hMm1
          · exfalso; revert hLtM; decide
          · rcases List.mem_singleton.mp hMm1 with rfl
            exfalso; revert hLtM; decide
        · rcases List.mem_singleton.mp hMr1 with rfl
          refine ⟨e0Seq, rfl, rfl, ⟨rfl, rfl, rfl, Or.inl rfl⟩, rfl, by decide, ?_⟩
          intro em hMm _ _ hLtM
          rcases List.mem_cons.mp hMm with rfl | hMm1
          · decide
          · rcases List.mem_singleton.mp hMm1 with rfl
            exfalso; revert hLtM; decide
    have hImmSeq : isImmediateCoChain (sequentialCandidateOfEvents [e0Seq, e1Seq])
        [e0Seq, e1Seq] := by
      refine ⟨⟨e0Seq, e1Seq, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, Or.inl rfl⟩, by decide⟩, ?_, trivial⟩
      rintro ⟨wMid, ⟨_, _, _, _, _, _, _, hLt1⟩, ⟨_, _, _, _, _, _, _, hLt2⟩⟩
      change 0 < wMid at hLt1
      change wMid < 1 at hLt2
      omega
    have hSubSeq : ∀ e ∈ [e0Seq, e1Seq],
        e ∈ (sequentialCandidateOfEvents [e0Seq, e1Seq]).events ∧
          e.isAtomic = true ∧ e.isRead = true ∧ e.isWrite = true := by
      intro e hMe
      rcases List.mem_cons.mp hMe with rfl | h1
      · exact ⟨List.Mem.head _, rfl, rfl, rfl⟩
      · rcases List.mem_singleton.mp h1 with rfl
        exact ⟨List.Mem.tail _ (List.Mem.head _), rfl, rfl, rfl⟩
    have hNoLostSeq : e1Seq.valWritten = 5#64 + sumAtomAddDeltas [e0Seq, e1Seq] :=
      ptx_relaxed_atom_add_co_no_lost_updates (initMemOfGlobal g0)
        (sequentialCandidateOfEvents [e0Seq, e1Seq]) hConsSeq [e0Seq, e1Seq] (by simp) 5#64
        hSubSeq hImmSeq hInit5
        (by
          rintro ⟨wPre, _, _, _, _, _, _, _, hLt⟩
          change wPre < 0 at hLt
          omega)
    exact ⟨hConsSeq, hImmSeq, hNoLostSeq, rfl⟩
  · have hConsRev : PTXAxiomaticConsistent (initMemOfGlobal g0)
        (twoEventReversedRmwCandidate e0Rev e1Rev) := by
      refine
        { eventIds_nodup := by decide
          po_wf := fun h => False.elim h
          po_irrefl := fun _ h => h
          po_trans := fun h _ => False.elim h
          po_complete := ?_
          sw_cta_barrier := ?_
          sw_inter_kernel := ?_
          hb_irrefl := fun _ hHb => twoEventRev_no_hb hHb
          rf_wf := ?_
          rf_complete := ?_
          co_wf := ?_
          co_irrefl := ?_
          co_trans := ?_
          co_total := ?_
          coh_ww := fun _ hHb => False.elim (twoEventRev_no_hb hHb)
          coh_wr := fun _ hHb => twoEventRev_no_hb hHb
          coh_rw := fun _ hHb => twoEventRev_no_hb hHb
          coh_vrw := fun _ _ hHb => twoEventRev_no_hb hHb
          rmw_atomicity := ?_ }
      · intro ea eb hMa hMb _ _ _ hSeq
        have hPa : ea.poSeq = 0 := by
          rcases List.mem_cons.mp hMa with rfl | h1
          · rfl
          · rw [List.mem_singleton.mp h1]
        have hPb : eb.poSeq = 0 := by
          rcases List.mem_cons.mp hMb with rfl | h1
          · rfl
          · rw [List.mem_singleton.mp h1]
        omega
      · intro ea eb _ hMa hMb _ hC hDiff _
        rcases List.mem_cons.mp hMa with rfl | hMa1
        · rcases List.mem_cons.mp hMb with rfl | hMb1
          · exact False.elim (hDiff rfl)
          · rcases List.mem_singleton.mp hMb1 with rfl
            nomatch hC
        · rcases List.mem_singleton.mp hMa1 with rfl
          rcases List.mem_cons.mp hMb with rfl | hMb1
          · nomatch hC
          · rcases List.mem_singleton.mp hMb1 with rfl
            exact False.elim (hDiff rfl)
      · intro ea eb hMa hMb _ _ _ hKLt
        have hKa : ea.kernelIdx = 0 := by
          rcases List.mem_cons.mp hMa with rfl | h1
          · rfl
          · rw [List.mem_singleton.mp h1]
        have hKb : eb.kernelIdx = 0 := by
          rcases List.mem_cons.mp hMb with rfl | h1
          · rfl
          · rw [List.mem_singleton.mp h1]
        omega
      · intro w r ⟨hW, hR⟩
        rw [hW, hR]
        exact ⟨e1Rev, e0Rev, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, Or.inl rfl⟩, rfl, by decide⟩
      · intro er hMr _
        rcases List.mem_cons.mp hMr with rfl | hMr1
        · left
          exact ⟨1, ⟨rfl, rfl⟩, fun _ ⟨hW, _⟩ => hW⟩
        · rcases List.mem_singleton.mp hMr1 with rfl
          right
          refine ⟨?_, hInit5⟩
          rintro ⟨_, _, hR⟩
          change 1 = 0 at hR
          omega
      · intro w1 w2 ⟨hW1, hW2⟩
        rw [hW1, hW2]
        exact ⟨e1Rev, e0Rev, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, Or.inl rfl⟩, by decide⟩
      · intro w ⟨hW1, hW2⟩
        change w = 1 at hW1
        change w = 0 at hW2
        omega
      · intro w1 w2 w3 ⟨_, h2⟩ ⟨h2', _⟩
        change w2 = 0 at h2
        change w2 = 1 at h2'
        omega
      · intro e1 e2 hM1 hM2 _ _ _ hNe
        rcases List.mem_cons.mp hM1 with rfl | h1
        · rcases List.mem_cons.mp hM2 with rfl | h2
          · exact False.elim (hNe rfl)
          · rcases List.mem_singleton.mp h2 with rfl
            exact Or.inr ⟨rfl, rfl⟩
        · rcases List.mem_singleton.mp h1 with rfl
          rcases List.mem_cons.mp hM2 with rfl | h2
          · exact Or.inl ⟨rfl, rfl⟩
          · rcases List.mem_singleton.mp h2 with rfl
            exact False.elim (hNe rfl)
      · intro e hMe _ _ _
        rcases List.mem_cons.mp hMe with rfl | h1
        · refine ⟨?_, ?_⟩
          · intro w ⟨hW, _⟩
            refine ⟨⟨hW, rfl⟩, ?_⟩
            rintro ⟨wMid, ⟨_, hM1⟩, ⟨hM2, _⟩⟩
            change wMid = 0 at hM1
            change wMid = 1 at hM2
            omega
          · intro hNoRf
            exact False.elim (hNoRf ⟨1, rfl, rfl⟩)
        · rcases List.mem_singleton.mp h1 with rfl
          refine ⟨?_, ?_⟩
          · intro _ ⟨_, hR⟩
            change 1 = 0 at hR
            omega
          · intro _ ⟨_, _, h2⟩
            change 1 = 0 at h2
            omega
    have hImmRev : isImmediateCoChain (twoEventReversedRmwCandidate e0Rev e1Rev)
        [e1Rev, e0Rev] := by
      refine ⟨⟨rfl, rfl⟩, ?_, trivial⟩
      rintro ⟨wMid, ⟨_, hM1⟩, ⟨hM2, _⟩⟩
      change wMid = 0 at hM1
      change wMid = 1 at hM2
      omega
    have hSubRev : ∀ e ∈ [e1Rev, e0Rev],
        e ∈ (twoEventReversedRmwCandidate e0Rev e1Rev).events ∧
          e.isAtomic = true ∧ e.isRead = true ∧ e.isWrite = true := by
      intro e hMe
      rcases List.mem_cons.mp hMe with rfl | h1
      · exact ⟨List.Mem.tail _ (List.Mem.head _), rfl, rfl, rfl⟩
      · rcases List.mem_singleton.mp h1 with rfl
        exact ⟨List.Mem.head _, rfl, rfl, rfl⟩
    have hNoLostRev : e0Rev.valWritten = 5#64 + sumAtomAddDeltas [e1Rev, e0Rev] :=
      ptx_relaxed_atom_add_co_no_lost_updates (initMemOfGlobal g0)
        (twoEventReversedRmwCandidate e0Rev e1Rev) hConsRev [e1Rev, e0Rev] (by simp) 5#64
        hSubRev hImmRev hInit5
        (by
          rintro ⟨_, _, h2⟩
          change 1 = 0 at h2
          omega)
    exact ⟨hConsRev, hImmRev, hNoLostRev, rfl⟩

/-- Executable kernel trace equality (`evalPTXKernelWithOracle`, `evalPTXKernelWithCTAOrder`, and
    `replayCoherentGlobalWrites`) for `ptx_relaxed_cross_cta_atom_add_commutes` (`D6`). -/
theorem ptx_relaxed_cross_cta_atom_add_exec :
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
    let e0Seq : PTXMemEvent :=
      { eventId := 0, kernelIdx := 0, ctaId := { x := 0, y := 0, z := 0 }
      , tid := { x := 0, y := 0, z := 0 }, barrierEpoch := [], space := .global
      , addr := 0, width := 8, isRead := true, isWrite := true, isAtomic := true
      , valRead := 5#64, valWritten := 24#64, poSeq := 0 }
    let e1Seq : PTXMemEvent :=
      { eventId := 1, kernelIdx := 0, ctaId := { x := 1, y := 0, z := 0 }
      , tid := { x := 0, y := 0, z := 0 }, barrierEpoch := [], space := .global
      , addr := 0, width := 8, isRead := true, isWrite := true, isAtomic := true
      , valRead := 24#64, valWritten := 47#64, poSeq := 0 }
    let e0Rev : PTXMemEvent :=
      { eventId := 0, kernelIdx := 0, ctaId := { x := 0, y := 0, z := 0 }
      , tid := { x := 0, y := 0, z := 0 }, barrierEpoch := [], space := .global
      , addr := 0, width := 8, isRead := true, isWrite := true, isAtomic := true
      , valRead := 28#64, valWritten := 47#64, poSeq := 0 }
    let e1Rev : PTXMemEvent :=
      { eventId := 1, kernelIdx := 0, ctaId := { x := 1, y := 0, z := 0 }
      , tid := { x := 0, y := 0, z := 0 }, barrierEpoch := [], space := .global
      , addr := 0, width := 8, isRead := true, isWrite := true, isAtomic := true
      , valRead := 5#64, valWritten := 28#64, poSeq := 0 }
    (∃ gSeq,
      evalPTXKernelWithOracle none 8 k { x := 2 } { x := 1 } g0
        { params := [ ("acc", 0#64) ] } = .ok (gSeq, [e0Seq, e1Seq]) ∧
      gSeq.loadBits 0 8 = some 47#64) ∧
    (∃ gRaw gCoh gCtaOrd evsCtaOrd,
      evalPTXKernelWithOracle (some revOracle) 8 k { x := 2 } { x := 1 } g0
        { params := [ ("acc", 0#64) ] } = .ok (gRaw, [e0Rev, e1Rev]) ∧
      evalPTXKernelWithCTAOrder none 8 k { x := 2 } { x := 1 }
        [{ x := 1, y := 0, z := 0 }, { x := 0, y := 0, z := 0 }] g0
        { params := [ ("acc", 0#64) ] } = .ok (gCtaOrd, evsCtaOrd) ∧
      replayCoherentGlobalWrites g0 [e1Rev, e0Rev] = some gCoh ∧
      gCoh.loadBits 0 8 = some 47#64 ∧
      gCtaOrd.loadBits 0 8 = some 47#64) := by
  exact ⟨⟨_, rfl, rfl⟩, ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl⟩⟩

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
