import LeanNative.Proofs.MetalSIMT1

namespace LeanNative.Proofs.MetalSIMT

open LeanNative.Backend.MetalAst

def SimtLogInv (nIn lo hi : Nat) (a : MSLAccess) : Prop :=
  (∃ k < nIn, a.target = .deviceBuf k ∧ a.isWrite = false) ∨
  (a.target = .deviceBuf nIn ∧ a.width = 8 ∧ ∃ idx, lo ≤ idx ∧ idx < hi ∧ a.addr = idx * 8)

theorem simtLogInv_mono {nIn lo hi lo' hi' : Nat} {a : MSLAccess}
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') (h : SimtLogInv nIn lo hi a) :
    SimtLogInv nIn lo' hi' a := by
  rcases h with h1 | ⟨ht, hw, idx, h1, h2, ha⟩
  · exact Or.inl h1
  · exact Or.inr ⟨ht, hw, idx, by omega, by omega, ha⟩

theorem findDataRaceGo_read_none (tid : Dim3) (k nIn lo hi addr : Nat) (hk : k < nIn) :
    ∀ (log : List MSLAccess), (∀ a ∈ log, SimtLogInv nIn lo hi a) →
      findDataRaceGo tid (.deviceBuf k) addr 8 false false log = none
  | [], _ => rfl
  | a :: rest, hlog => by
    have ha := hlog a (.head rest)
    have hrest := findDataRaceGo_read_none tid k nIn lo hi addr hk rest (fun x hx => hlog x (.tail a hx))
    unfold findDataRaceGo
    rcases ha with ⟨k', _, htk, hwf⟩ | ⟨htn, _, _, _, _, _⟩
    · simp [hwf, hrest]
    · have hne : (MSLMemTarget.deviceBuf k == a.target) = false := by
        rw [htn]; exact devBuf_beq_false (by omega)
      simp [hne, hrest]

theorem recordEpochAccess_read_ok (log : List MSLAccess) (tid : Dim3)
    (k nIn lo hi addr : Nat) (hk : k < nIn)
    (hlog : ∀ a ∈ log, SimtLogInv nIn lo hi a) :
    recordEpochAccess log tid (.deviceBuf k) .device addr 8 false false =
      .ok ({ tid, target := .deviceBuf k, addr, width := 8, isWrite := false, isAtomic := false } :: log) ∧
    ∀ a ∈ ({ tid, target := .deviceBuf k, addr, width := 8, isWrite := false, isAtomic := false } : MSLAccess) :: log,
      SimtLogInv nIn lo hi a := by
  unfold recordEpochAccess findDataRace?
  rw [findDataRaceGo_read_none tid k nIn lo hi addr hk log hlog]
  refine ⟨rfl, ?_⟩
  intro a ha
  rcases List.mem_cons.mp ha with rfl | hmem
  · exact Or.inl ⟨k, hk, rfl, rfl⟩
  · exact hlog a hmem

theorem findDataRaceGo_write_none (tid : Dim3) (nIn lo hi : Nat) :
    ∀ (log : List MSLAccess), (∀ a ∈ log, SimtLogInv nIn lo hi a) →
      findDataRaceGo tid (.deviceBuf nIn) (hi * 8) 8 true false log = none
  | [], _ => rfl
  | a :: rest, hlog => by
    have ha := hlog a (.head rest)
    have hrest := findDataRaceGo_write_none tid nIn lo hi rest (fun x hx => hlog x (.tail a hx))
    unfold findDataRaceGo
    rcases ha with ⟨k, hk, htk, _⟩ | ⟨htn, hw, idx, _, hlt, haddr⟩
    · have hne : (MSLMemTarget.deviceBuf nIn == a.target) = false := by
        rw [htk]; exact devBuf_beq_false (by omega)
      simp [hne, hrest]
    · have hov : rangesOverlap (hi * 8) 8 a.addr a.width = false := by
        rw [haddr, hw]
        unfold rangesOverlap
        simp
        omega
      simp [hov, hrest]

theorem recordEpochAccess_write_ok (log : List MSLAccess) (tid : Dim3)
    (nIn lo hi : Nat) (hle : lo ≤ hi)
    (hlog : ∀ a ∈ log, SimtLogInv nIn lo hi a) :
    recordEpochAccess log tid (.deviceBuf nIn) .device (hi * 8) 8 true false =
      .ok ({ tid, target := .deviceBuf nIn, addr := hi * 8, width := 8, isWrite := true, isAtomic := false } :: log) ∧
    ∀ a ∈ ({ tid, target := .deviceBuf nIn, addr := hi * 8, width := 8, isWrite := true, isAtomic := false } : MSLAccess) :: log,
      SimtLogInv nIn lo (hi + 1) a := by
  unfold recordEpochAccess findDataRace?
  rw [findDataRaceGo_write_none tid nIn lo hi log hlog]
  refine ⟨rfl, ?_⟩
  intro a ha
  rcases List.mem_cons.mp ha with rfl | hmem
  · exact Or.inr ⟨rfl, rfl, hi, hle, Nat.lt_succ_self hi, rfl⟩
  · exact simtLogInv_mono (Nat.le_refl lo) (Nat.le_succ hi) (hlog a hmem)

theorem findCrossGroupRace_none (nIn mid hi : Nat) (b : MSLAccess)
    (hb : SimtLogInv nIn mid hi b) :
    ∀ (prior : List MSLAccess), (∀ a ∈ prior, SimtLogInv nIn 0 mid a) →
      findCrossGroupRace? b.target b.addr b.width b.isWrite b.isAtomic prior = none
  | [], _ => rfl
  | a :: rest, hprior => by
    have ha := hprior a (.head rest)
    have hrest := findCrossGroupRace_none nIn mid hi b hb rest (fun x hx => hprior x (.tail a hx))
    unfold findCrossGroupRace?
    rcases hb with ⟨kb, hkb, htb, hwfb⟩ | ⟨htb, hwb, idxb, hmidb, _, haddrb⟩
    · rcases ha with ⟨_, _, _, hwfa⟩ | ⟨hta, _, _, _, _, _⟩
      · simp [hwfb, hwfa]
        rw [← hwfb]
        exact hrest
      · have hne : (b.target == a.target) = false := by
          rw [htb, hta]; exact devBuf_beq_false (by omega)
        simp [hne, hrest]
    · rcases ha with ⟨ka, hka, hta, _⟩ | ⟨hta, hwa, idxa, _, hlta, haddra⟩
      · have hne : (b.target == a.target) = false := by
          rw [htb, hta]; exact devBuf_beq_false (by omega)
        simp [hne, hrest]
      · have hov : rangesOverlap b.addr b.width a.addr a.width = false := by
          rw [haddrb, hwb, haddra, hwa]
          unfold rangesOverlap
          simp
          omega
        simp [hov, hrest]

theorem checkCrossGroupDeviceLog_ok (nIn mid hi : Nat) (hmid : mid ≤ hi)
    (prior : List MSLAccess) (hprior : ∀ a ∈ prior, SimtLogInv nIn 0 mid a) :
    ∀ (grp : List MSLAccess), (∀ b ∈ grp, SimtLogInv nIn mid hi b) →
      checkCrossGroupDeviceLog prior grp = .ok () ∧
      ∀ x ∈ grp ++ prior, SimtLogInv nIn 0 hi x
  | [], _ =>
    ⟨rfl, fun x hx => by
      simp only [List.nil_append] at hx
      exact simtLogInv_mono (Nat.le_refl 0) hmid (hprior x hx)⟩
  | b :: rest, hgrp => by
    have hb := hgrp b (.head rest)
    have ⟨hok, hall⟩ := checkCrossGroupDeviceLog_ok nIn mid hi hmid prior hprior rest
      (fun x hx => hgrp x (.tail b hx))
    unfold checkCrossGroupDeviceLog
    have hnone := findCrossGroupRace_none nIn mid hi b hb prior hprior
    have hcond : (if !isDeviceAccess b then checkCrossGroupDeviceLog prior rest
        else match findCrossGroupRace? b.target b.addr b.width b.isWrite b.isAtomic prior with
          | some conflictAddr => .dataRace .device conflictAddr
          | none => checkCrossGroupDeviceLog prior rest) = .ok () := by
      rw [hnone]
      split <;> exact hok
    refine ⟨hcond, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact simtLogInv_mono (Nat.zero_le mid) (Nat.le_refl hi) hb
    · exact hall x hmem

theorem stepFirstReadyThread_exec (g : MSLGroupState) (th th' : MSLThreadState)
    (g' : MSLGroupState) (stmt : MSLStmt) (rest : List MSLStmt)
    (hhalted : th.halted = false) (hbar : threadAtBarrier th = false)
    (hsimd : threadAtSimdOp th = false) (hstmts : th.stmts = stmt :: rest)
    (hexec : execNonBarrierStmt g th stmt rest = .ok (th', g')) :
    ∀ (done pre todo : List MSLThreadState),
      (∀ d ∈ done, d.halted = true) →
      stepFirstReadyThread g pre (done ++ (th :: todo)) =
        .ok (true, { g' with threads := pre.reverse ++ done ++ (th' :: todo) })
  | [], pre, todo, _ => by
    simp only [List.nil_append, List.append_nil, stepFirstReadyThread,
      hhalted, hbar, hsimd, Bool.or_false, Bool.false_eq_true, ite_false, hstmts, hexec]
  | d :: ds, pre, todo, hdone => by
    have hd : d.halted = true := hdone d (.head ds)
    have ih := stepFirstReadyThread_exec g th th' g' stmt rest hhalted hbar hsimd hstmts hexec
      ds (d :: pre) todo (fun x hx => hdone x (.tail d hx))
    simp only [List.cons_append, stepFirstReadyThread, hd, Bool.true_or, ite_true]
    rw [ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem list_all_halted_false {done todo : List MSLThreadState} {th : MSLThreadState}
    (h : th.halted = false) :
    (done ++ (th :: todo)).all (·.halted) = false := by
  induction done with
  | nil => simp [h]
  | cons d ds ih => simp [ih]

theorem runGroupWithDeviceLog_step_stmt (f : Nat) (g g' : MSLGroupState)
    (done todo : List MSLThreadState) (th th' : MSLThreadState)
    (stmt : MSLStmt) (rest : List MSLStmt)
    (hthreads : g.threads = done ++ (th :: todo))
    (hdone : ∀ d ∈ done, d.halted = true)
    (hhalted : th.halted = false) (hbar : threadAtBarrier th = false)
    (hsimd : threadAtSimdOp th = false) (hstmts : th.stmts = stmt :: rest)
    (hexec : execNonBarrierStmt g th stmt rest = .ok (th', g'))
    (hlog : g'.epochLog.isEmpty = true → g.epochLog.isEmpty = true) :
    runGroupWithDeviceLog (f + 1) g [] =
      runGroupWithDeviceLog f { g' with threads := done ++ (th' :: todo) } [] := by
  have hall : g.threads.all (·.halted) = false := by
    rw [hthreads]; exact list_all_halted_false hhalted
  have hfirst : stepFirstReadyThread g [] g.threads =
      .ok (true, { g' with threads := done ++ (th' :: todo) }) := by
    rw [hthreads]
    simpa using stepFirstReadyThread_exec g th th' g' stmt rest hhalted hbar hsimd hstmts hexec done [] todo hdone
  have hstep : stepGroup g = .ok (false, { g' with threads := done ++ (th' :: todo) }) := by
    unfold stepGroup
    rw [hall]
    simp only [Bool.false_eq_true, ite_false, hfirst]
  have hsaved : ((!g.epochLog.isEmpty && g'.epochLog.isEmpty) = false) := by
    cases hge : g'.epochLog.isEmpty
    · simp
    · simp [hlog hge]
  rw [runGroupWithDeviceLog]
  rw [hstep]
  simp only [hsaved, Bool.false_eq_true, ite_false]

theorem runGroupWithDeviceLog_all_halted (fuel : Nat) (g : MSLGroupState)
    (hall : g.threads.all (·.halted) = true) :
    runGroupWithDeviceLog fuel g [] = .ok (g, g.epochLog.filter isDeviceAccess) := by
  cases fuel with
  | zero =>
    unfold runGroupWithDeviceLog
    simp [hall]
  | succ f =>
    unfold runGroupWithDeviceLog stepGroup
    simp [hall]


theorem ev_var_bound (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (name : String) (bv : BitVec 64)
    (hl : ls.lookup? name = some bv) (ht : ls.lookupType? name = some .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.var name) =
      .ok { value := bv, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall]
  simp only [hl, ht]
  rfl

theorem ev_cast_ulong_from_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a : MSLExpr) (bv : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := bv, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.cast .ulong a) =
      .ok { value := bv, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hta]
  rfl

theorem ev_cast_ulong_from_bool (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a : MSLExpr) (bv : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := bv, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .bool) :
    evalExprWithCall callEval fuel g tid ls log (.cast .ulong a) =
      .ok { value := if bv != 0#64 then 1#64 else 0#64, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hta]
  rfl

theorem ev_bitnot_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a : MSLExpr) (bv : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := bv, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.bitNot a) =
      .ok { value := ~~~bv, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hta]
  rfl

theorem ev_add_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.add a b) =
      .ok { value := va + vb, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  rw [finishBin_ulong_op g a b .add ls log va vb [] [] hta htb]
  rfl

theorem ev_sub_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.sub a b) =
      .ok { value := va - vb, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  rw [finishBin_ulong_op g a b .sub ls log va vb [] [] hta htb]
  rfl

theorem ev_mul_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.mul a b) =
      .ok { value := va * vb, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  rw [finishBin_ulong_op g a b .mul ls log va vb [] [] hta htb]
  rfl

theorem ev_div_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong)
    (hnz : (vb == 0#64) = false) :
    evalExprWithCall callEval fuel g tid ls log (.div a b) =
      .ok { value := va / vb, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  rw [finishBin_ulong_op g a b .div ls log va vb [] [] hta htb, evalTypedBin_ulong]
  simp only [hnz, Bool.false_eq_true, ite_false]

theorem ev_rem_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong)
    (hnz : (vb == 0#64) = false) :
    evalExprWithCall callEval fuel g tid ls log (.rem a b) =
      .ok { value := va % vb, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  rw [finishBin_ulong_op g a b .rem ls log va vb [] [] hta htb, evalTypedBin_ulong]
  simp only [hnz, Bool.false_eq_true, ite_false]

theorem ev_bitand_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.bitAnd a b) =
      .ok { value := va &&& vb, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  exact finishBitwise_ulong_op g a b (· &&& ·) ls log va vb [] [] hta htb

theorem ev_bitor_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.bitOr a b) =
      .ok { value := va ||| vb, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  exact finishBitwise_ulong_op g a b (· ||| ·) ls log va vb [] [] hta htb

theorem ev_bitxor_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.bitXor a b) =
      .ok { value := va ^^^ vb, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  exact finishBitwise_ulong_op g a b (· ^^^ ·) ls log va vb [] [] hta htb

theorem ev_shl_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (hlt : vb.toNat < 64) :
    evalExprWithCall callEval fuel g tid ls log (.shl a b) =
      .ok { value := va <<< vb.toNat, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  simpa using finishShift_ulong_op g a false ls log va vb [] [] hta hlt

theorem ev_shr_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (hlt : vb.toNat < 64) :
    evalExprWithCall callEval fuel g tid ls log (.shr a b) =
      .ok { value := va >>> vb.toNat, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  simpa using finishShift_ulong_op g a true ls log va vb [] [] hta hlt

theorem ev_sar_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong)
    (hlt : vb.toNat < 64) :
    evalExprWithCall callEval fuel g tid ls log (.cast .ulong (.shr (.cast .long a) b)) =
      .ok { value := va.sshiftRight vb.toNat, fields := [], locals := ls, log := log } := by
  have hcast : evalExprWithCall callEval fuel g tid ls log (.cast .long a) =
      .ok { value := va, fields := [], locals := ls, log := log } := by
    rw [evalExprWithCall, ha]
    simp only [bindEval, hta]
    rfl
  have hshr : evalExprWithCall callEval fuel g tid ls log (.shr (.cast .long a) b) =
      .ok { value := va.sshiftRight vb.toNat, fields := [], locals := ls, log := log } := by
    rw [evalExprWithCall, hcast]
    simp only [bindEval, hb]
    exact finishShift_long_sar_op g (.cast .long a) ls log va vb [] [] rfl hlt
  rw [evalExprWithCall, hshr]
  simp only [bindEval, inferExprType, htb]
  rfl

theorem ev_eq_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.eq a b) =
      .ok { value := if va == vb then 1#64 else 0#64, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  rw [finishCmp_ulong_op g a b .eq ls log va vb [] [] hta htb, evalTypedCmp_ulong]

theorem ev_ne_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.ne a b) =
      .ok { value := if va != vb then 1#64 else 0#64, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  rw [finishCmp_ulong_op g a b .ne ls log va vb [] [] hta htb, evalTypedCmp_ulong]

theorem ev_lt_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.lt a b) =
      .ok { value := if BitVec.ult va vb then 1#64 else 0#64, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  rw [finishCmp_ulong_op g a b .lt ls log va vb [] [] hta htb, evalTypedCmp_ulong]

theorem ev_le_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.le a b) =
      .ok { value := if BitVec.ule va vb then 1#64 else 0#64, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  rw [finishCmp_ulong_op g a b .le ls log va vb [] [] hta htb, evalTypedCmp_ulong]

theorem ev_ge_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.ge a b) =
      .ok { value := if BitVec.ule vb va then 1#64 else 0#64, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  rw [finishCmp_ulong_op g a b .ge ls log va vb [] [] hta htb, evalTypedCmp_ulong]

theorem ev_select_true (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (c t f : MSLExpr) (bv : BitVec 64)
    (hc : evalExprWithCall callEval fuel g tid ls log c =
      .ok { value := bv, fields := [], locals := ls, log := log })
    (hnz : bv != 0#64) :
    evalExprWithCall callEval fuel g tid ls log (.select c t f) =
      evalExprWithCall callEval fuel g tid ls log t := by
  rw [evalExprWithCall, hc]
  simp only [bindEval, hnz, ite_true]

theorem ev_select_false (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (c t f : MSLExpr) (bv : BitVec 64)
    (hc : evalExprWithCall callEval fuel g tid ls log c =
      .ok { value := bv, fields := [], locals := ls, log := log })
    (hz : (bv != 0#64) = false) :
    evalExprWithCall callEval fuel g tid ls log (.select c t f) =
      evalExprWithCall callEval fuel g tid ls log f := by
  rw [evalExprWithCall, hc]
  simp only [bindEval, hz, Bool.false_eq_true, ite_false]



end LeanNative.Proofs.MetalSIMT
