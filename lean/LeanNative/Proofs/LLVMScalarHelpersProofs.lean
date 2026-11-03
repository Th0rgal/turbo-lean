import LeanNative.Semantics.Eval
import LeanNative.Backend.LLVMLower
import LeanNative.Proofs.TargetBitVecProofs

/-!
# Straight-Line LLVM Scalar Lowering Helpers (`LeanNative.Proofs.LLVMScalarHelpersProofs`)

Register/block-label injectivity, typed environment agreement (`EnvTypedAgree`),
frame composition (`ScalarExecPost`), and straight-line instruction-sequence execution
lemmas for `LeanNative.Backend.LLVMLower`.
-/

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend.TargetIR
open LeanNative.Backend.LLVMAst
open LeanNative.Backend.LLVMLower

/-! ## 1. Register & Block-Label Freshness / Injectivity -/

theorem varReg_injective (a b : VarId) (h : varReg a = varReg b) : a = b := by
  have hlist : (ppInt a).toList = (ppInt b).toList := by
    have hc := congrArg String.toList h
    simpa [varReg] using hc
  exact ppInt_injective a b (String.ext hlist)

theorem tmpReg_injective (a b : Nat) (h : tmpReg a = tmpReg b) : a = b := by
  have hlist : (ppInt a).toList = (ppInt b).toList := by
    have hc := congrArg String.toList h
    simpa [tmpReg] using hc
  exact ppInt_injective a b (String.ext hlist)

theorem blkLabel_injective (a b : Nat) (h : blkLabel a = blkLabel b) : a = b := by
  have hlist : (ppInt a).toList = (ppInt b).toList := by
    have hc := congrArg String.toList h
    simpa [blkLabel] using hc
  exact ppInt_injective a b (String.ext hlist)

theorem varReg_ne_tmpReg (v : VarId) (k : Nat) : varReg v ≠ tmpReg k := by
  intro h
  have hc := congrArg String.toList h
  simp [varReg, tmpReg] at hc

theorem entryLabel_ne_blkLabel (k : Nat) : entryLabel ≠ blkLabel k := by
  intro h
  have hc := congrArg String.toList h
  simp [entryLabel, blkLabel] at hc

theorem isI64Ty_eq_true (t : LNIRType) (h : isI64Ty t = true) : t = .i64 := by
  cases t <;> first | rfl | contradiction

theorem isI1Ty_eq_true (t : LNIRType) (h : isI1Ty t = true) : t = .i1 := by
  cases t <;> first | rfl | contradiction

theorem sameScalarTy_eq_true (t1 t2 : LNIRType) (h : sameScalarTy t1 t2 = true) :
    t1 = t2 ∧ (t1 = .i64 ∨ t1 = .i1) := by
  unfold sameScalarTy at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [isI64Ty_eq_true t1 h1, isI64Ty_eq_true t2 h2]
    exact ⟨rfl, Or.inl rfl⟩
  · rw [isI1Ty_eq_true t1 h1, isI1Ty_eq_true t2 h2]
    exact ⟨rfl, Or.inr rfl⟩

/-! ## 2. Straight-Line Instruction Execution & Environment Agreement -/

/-- Agreement between `Γ : ScalarTyEnv`, `env : VarEnv`, and `regs`. -/
def EnvTypedAgree (Γ : ScalarTyEnv) (env : VarEnv) (regs : List (RegName × LLVMVal)) : Prop :=
  ∀ x ty, Γ x = some ty →
    ∃ v w, env x = some v ∧ encodeScalarTyped ty v = some w ∧
      regs.lookup (varReg x) = some (.bits .i64 w)

theorem lookup_cons_ne (r q : RegName) (v : LLVMVal) (regs : List (RegName × LLVMVal))
    (hne : q ≠ r) :
    ((r, v) :: regs).lookup q = regs.lookup q := by
  have hbeq : (q == r) = false := Bool.eq_false_iff.mpr (fun h => hne (eq_of_beq h))
  simp [List.lookup, hbeq]

theorem lookup_cons_self (r : RegName) (v : LLVMVal) (regs : List (RegName × LLVMVal)) :
    ((r, v) :: regs).lookup r = some v := by
  simp [List.lookup]

theorem envTypedAgree_bind_tmp (Γ : ScalarTyEnv) (env : VarEnv)
    (regs : List (RegName × LLVMVal)) (k : Nat) (v : LLVMVal)
    (h : EnvTypedAgree Γ env regs) :
    EnvTypedAgree Γ env ((tmpReg k, v) :: regs) := by
  intro x ty hΓ
  rcases h x ty hΓ with ⟨val, w, henv, hw, hlook⟩
  refine ⟨val, w, henv, hw, ?_⟩
  rw [lookup_cons_ne _ _ _ _ (varReg_ne_tmpReg x k)]
  exact hlook

theorem envTypedAgree_preserved (Γ : ScalarTyEnv) (env : VarEnv)
    (regs1 regs2 : List (RegName × LLVMVal)) (kLo kHi : Nat)
    (h : EnvTypedAgree Γ env regs1)
    (hframe : ∀ q, (∀ j, kLo ≤ j → j < kHi → q ≠ tmpReg j) → regs2.lookup q = regs1.lookup q) :
    EnvTypedAgree Γ env regs2 := by
  intro x ty hΓ
  rcases h x ty hΓ with ⟨val, w, henv, hw, hlook⟩
  refine ⟨val, w, henv, hw, ?_⟩
  rw [hframe (varReg x) (fun j _ _ => varReg_ne_tmpReg x j)]
  exact hlook

theorem envTypedAgree_bind_var (Γ : ScalarTyEnv) (env : VarEnv)
    (regs : List (RegName × LLVMVal)) (dst : VarId) (ty : LNIRType) (val : Val) (w : BitVec 64)
    (h : EnvTypedAgree Γ env regs) (hw : encodeScalarTyped ty val = some w) :
    EnvTypedAgree (Γ.bind dst ty) (env.bind dst val) ((varReg dst, .bits .i64 w) :: regs) := by
  intro x ty' hΓ
  dsimp [ScalarTyEnv.bind] at hΓ
  dsimp [VarEnv.bind]
  by_cases hxd : x == dst
  · have hx_eq : x = dst := eq_of_beq hxd
    subst hx_eq
    simp only [BEq.rfl, ↓reduceIte, Option.some.injEq] at hΓ ⊢
    subst hΓ
    exact ⟨val, w, rfl, hw, lookup_cons_self _ _ _⟩
  · simp only [hxd, Bool.false_eq_true, ↓reduceIte] at hΓ ⊢
    rcases h x ty' hΓ with ⟨vx, wx, henv, hwx, hlook⟩
    have hne : varReg x ≠ varReg dst := fun hr => hxd (beq_iff_eq.mpr (varReg_injective x dst hr))
    refine ⟨vx, wx, henv, hwx, ?_⟩
    rw [lookup_cons_ne _ _ _ _ hne]
    exact hlook

theorem execInstrsWith_append
    (runCall : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal →
      ExecOutcome ⊕ ExecState)
    (st st1 : ExecState) (xs ys : List LLVMInstr)
    (h1 : execInstrsWith runCall st xs = .inr st1) :
    execInstrsWith runCall st (xs ++ ys) = execInstrsWith runCall st1 ys := by
  induction xs generalizing st with
  | nil =>
    simp [execInstrsWith] at h1
    subst h1
    rfl
  | cons x rest ih =>
    simp only [List.cons_append, execInstrsWith] at h1 ⊢
    cases hstep : stepInstrWith runCall st x with
    | inl out => simp [hstep] at h1
    | inr stMid =>
      simp only [hstep] at h1 ⊢
      exact ih stMid h1

/-- Frame & value invariant produced by `lowerScalarExpr Γ se k = some res`. -/
def ScalarExecPost
    (runCall : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal →
      ExecOutcome ⊕ ExecState)
    (env : VarEnv) (se : ScalarExpr) (st : ExecState) (k : Nat) (res : ScalarLowerRes) : Prop :=
  k ≤ res.nextTmp ∧
  (∀ j, res.nextTmp ≤ j → res.dst ≠ tmpReg j) ∧
  ∃ v w st',
    evalScalarExpr env se = .ok v ∧
    encodeScalarTyped res.ty v = some w ∧
    execInstrsWith runCall st res.instrs = .inr st' ∧
    st'.mem = st.mem ∧ st'.globals = st.globals ∧ st'.prevBlock = st.prevBlock ∧
    st'.regs.lookup res.dst = some (.bits .i64 w) ∧
    (∀ q, (∀ j, k ≤ j → j < res.nextTmp → q ≠ tmpReg j) → st'.regs.lookup q = st.regs.lookup q)

/-! ## 3. Straight-Line Operator & Sequence Execution Lemmas -/

theorem fresh_tmp_after (d k2 : Nat) (hd : d < k2) :
    ∀ j, k2 ≤ j → tmpReg d ≠ tmpReg j := by
  intro j hj heq
  have := tmpReg_injective d j heq
  omega

theorem frame_tmp_Range (regs1 regs2 regs3 : List (RegName × LLVMVal)) (k1 k2 k3 : Nat)
    (hle12 : k1 ≤ k2) (hle23 : k2 ≤ k3)
    (hf12 : ∀ q, (∀ j, k1 ≤ j → j < k2 → q ≠ tmpReg j) → regs2.lookup q = regs1.lookup q)
    (hf23 : ∀ q, (∀ j, k2 ≤ j → j < k3 → q ≠ tmpReg j) → regs3.lookup q = regs2.lookup q) :
    ∀ q, (∀ j, k1 ≤ j → j < k3 → q ≠ tmpReg j) → regs3.lookup q = regs1.lookup q := by
  intro q hq
  rw [hf23 q (fun j hlo hhi => hq j (Nat.le_trans hle12 hlo) hhi)]
  exact hf12 q (fun j hlo hhi => hq j hlo (Nat.lt_of_lt_of_le hhi hle23))

theorem singleBin_exec
    (runCall : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal →
      ExecOutcome ⊕ ExecState)
    (st : ExecState) (k : Nat) (ins : LLVMInstr) (w : BitVec 64)
    (hstep : stepInstrWith runCall st ins = .inr (bindReg st (tmpReg k) (.bits .i64 w))) :
    ∃ st', execInstrsWith runCall st [ins] = .inr st' ∧
      st'.mem = st.mem ∧ st'.globals = st.globals ∧ st'.prevBlock = st.prevBlock ∧
      st'.regs.lookup (tmpReg k) = some (.bits .i64 w) ∧
      (∀ q, (∀ j, k ≤ j → j < k + 1 → q ≠ tmpReg j) → st'.regs.lookup q = st.regs.lookup q) := by
  refine ⟨bindReg st (tmpReg k) (.bits .i64 w), ?_, rfl, rfl, rfl, lookup_cons_self _ _ _, ?_⟩
  · simp [execInstrsWith, hstep]
  · intro q hq
    exact lookup_cons_ne _ _ _ _ (hq k (Nat.le_refl k) (Nat.lt_succ_self k))

theorem emitDivRem_exec
    (runCall : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal →
      ExecOutcome ⊕ ExecState)
    (st : ExecState) (k : Nat) (isRem : Bool) (dl dr : RegName) (a b : UInt64)
    (hdl : st.regs.lookup dl = some (.bits .i64 a.toBitVec))
    (hdr : st.regs.lookup dr = some (.bits .i64 b.toBitVec))
    (hl_fr : ∀ j, k ≤ j → dl ≠ tmpReg j)
    (hr_fr : ∀ j, k ≤ j → dr ≠ tmpReg j) :
    ∃ st', execInstrsWith runCall st (emitDivRem k isRem (.reg dl) (.reg dr)).2.2 = .inr st' ∧
      st'.mem = st.mem ∧ st'.globals = st.globals ∧ st'.prevBlock = st.prevBlock ∧
      st'.regs.lookup (tmpReg (k + 3)) =
        some (.bits .i64 (if isRem then (a % b).toBitVec else (a / b).toBitVec)) ∧
      (∀ q, (∀ j, k ≤ j → j < k + 4 → q ≠ tmpReg j) → st'.regs.lookup q = st.regs.lookup q) := by
  have hdr0 : ∀ v0, ((tmpReg k, v0) :: st.regs).lookup dr = some (.bits .i64 b.toBitVec) :=
    fun _ => by
      rw [lookup_cons_ne _ _ _ _ (hr_fr k (Nat.le_refl k))]
      exact hdr
  have hdl1 : ∀ v0 v1, ((tmpReg (k + 1), v1) :: (tmpReg k, v0) :: st.regs).lookup dl =
      some (.bits .i64 a.toBitVec) := fun _ _ => by
    rw [lookup_cons_ne _ _ _ _ (hl_fr (k + 1) (Nat.le_succ k)),
        lookup_cons_ne _ _ _ _ (hl_fr k (Nat.le_refl k))]
    exact hdl
  have hz2 : ∀ v0 v1 v2, ((tmpReg (k + 2), v2) :: (tmpReg (k + 1), v1) :: (tmpReg k, v0) :: st.regs).lookup
      (tmpReg k) = some v0 := fun _ _ _ => by
    rw [lookup_cons_ne _ _ _ _ (fresh_tmp_after k (k + 2) (by omega) (k + 2) (Nat.le_refl _)),
        lookup_cons_ne _ _ _ _ (fresh_tmp_after k (k + 1) (by omega) (k + 1) (Nat.le_refl _))]
    exact lookup_cons_self _ _ _
  have hdl2 : ∀ v0 v1 v2, ((tmpReg (k + 2), v2) :: (tmpReg (k + 1), v1) :: (tmpReg k, v0) :: st.regs).lookup
      dl = some (.bits .i64 a.toBitVec) := fun v0 v1 _ => by
    rw [lookup_cons_ne _ _ _ _ (hl_fr (k + 2) (Nat.le_add_right k 2))]
    exact hdl1 v0 v1
  have h01 : (@BEq.beq (BitVec IntWidth.i1.bits) _ 0#1 1#1) = false :=
    Bool.eq_false_iff.mpr (fun h => by have hc := eq_of_beq h; nomatch hc)
  let zBit : BitVec 1 := if b.toBitVec == 0#64 then 1#1 else 0#1
  let safeB : BitVec 64 := if b.toBitVec == 0#64 then 1#64 else b.toBitVec
  let rawV : BitVec 64 := if isRem then a.toBitVec % safeB else a.toBitVec / safeB
  let resV : BitVec 64 := if isRem then (a % b).toBitVec else (a / b).toBitVec
  refine ⟨{ st with regs := (tmpReg (k + 3), .bits .i64 resV) :: (tmpReg (k + 2), .bits .i64 rawV) ::
      (tmpReg (k + 1), .bits .i64 safeB) :: (tmpReg k, .bits .i1 zBit) :: st.regs },
    ?_, rfl, rfl, rfl, lookup_cons_self _ _ _,
    fun q hq => by repeat (rw [lookup_cons_ne _ _ _ _ (hq _ (by omega) (by omega))])⟩
  by_cases hbz : b = 0
  · subst hbz
    cases isRem
    · simp [emitDivRem, execInstrsWith, stepInstrWith, evalOperand, evalTypedOperand,
        lookupReg, icmpEval, w64, c64, IntWidth.bits, bindReg, hdr, hdl1, divOrRem,
        hz2, zBit, safeB, rawV, resV]
      congr 1
      exact BitVec.udiv_one
    · simp [emitDivRem, execInstrsWith, stepInstrWith, evalOperand, evalTypedOperand,
        lookupReg, icmpEval, w64, c64, IntWidth.bits, bindReg, hdr, hdl1, hdl2, divOrRem,
        hz2, zBit, safeB, rawV, resV]
      congr 1
      exact BitVec.umod_one
  · have hbnz64 : (b.toBitVec == 0#64) = false :=
      Bool.eq_false_iff.mpr (fun h => hbz (UInt64.eq_of_toBitVec_eq (eq_of_beq h)))
    have hbnzi1 : (@BEq.beq (BitVec IntWidth.i64.bits) _ b.toBitVec (0#64 : BitVec 64)) = false := hbnz64
    have hbnzi2 : (@BEq.beq (BitVec IntWidth.i64.bits) _ b.toBitVec 0#IntWidth.i64.bits) = false := hbnz64
    cases isRem
    · simp [emitDivRem, execInstrsWith, stepInstrWith, evalOperand, evalTypedOperand,
        lookupReg, icmpEval, w64, c64, bindReg, hdr, hdr0, hdl1, divOrRem,
        hz2, zBit, safeB, rawV, resV, hbnz64, hbnzi1, hbnzi2, h01]
      rfl
    · simp [emitDivRem, execInstrsWith, stepInstrWith, evalOperand, evalTypedOperand,
        lookupReg, icmpEval, w64, c64, bindReg, hdr, hdr0, hdl1, divOrRem,
        hz2, zBit, safeB, rawV, resV, hbnz64, hbnzi1, hbnzi2, h01]
      rfl

theorem emitShift_exec
    (runCall : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal →
      ExecOutcome ⊕ ExecState)
    (st : ExecState) (k : Nat) (op : BinOp) (dl dr : RegName) (a b : UInt64)
    (hop : op = .shl ∨ op = .shr ∨ op = .sar)
    (hdl : st.regs.lookup dl = some (.bits .i64 a.toBitVec))
    (hdr : st.regs.lookup dr = some (.bits .i64 b.toBitVec))
    (hl_fr : ∀ j, k ≤ j → dl ≠ tmpReg j) :
    ∃ st', execInstrsWith runCall st (emitShift k op (.reg dl) (.reg dr)).2.2 = .inr st' ∧
      st'.mem = st.mem ∧ st'.globals = st.globals ∧ st'.prevBlock = st.prevBlock ∧
      st'.regs.lookup (tmpReg (k + 1)) =
        some (.bits .i64 (match op with
          | .shr => (a >>> b).toBitVec
          | .sar => (lnirSar64 a b).toBitVec
          | _    => (a <<< b).toBitVec)) ∧
      (∀ q, (∀ j, k ≤ j → j < k + 2 → q ≠ tmpReg j) → st'.regs.lookup q = st.regs.lookup q) := by
  have hdl0 : ∀ v0, ((tmpReg k, v0) :: st.regs).lookup dl = some (.bits .i64 a.toBitVec) :=
    fun _ => by
      rw [lookup_cons_ne _ _ _ _ (hl_fr k (Nat.le_refl k))]
      exact hdl
  let mBit : BitVec IntWidth.i64.bits :=
    (@HAnd.hAnd (BitVec IntWidth.i64.bits) (BitVec IntWidth.i64.bits) (BitVec IntWidth.i64.bits) _
      b.toBitVec 63#64)
  have hnle : ¬(IntWidth.i64.bits ≤ mBit.toNat) := by
    have := bv64_and_63_lt_64 b.toBitVec
    change ¬(64 ≤ (b.toBitVec &&& 63#64).toNat)
    omega
  dsimp only [mBit] at hnle
  let resV : BitVec 64 := match op with
    | .shr => (a >>> b).toBitVec
    | .sar => (lnirSar64 a b).toBitVec
    | _    => (a <<< b).toBitVec
  refine ⟨{ st with regs := (tmpReg (k + 1), .bits .i64 resV) :: (tmpReg k, .bits .i64 mBit) :: st.regs },
    ?_, rfl, rfl, rfl, lookup_cons_self _ _ _,
    fun q hq => by repeat (rw [lookup_cons_ne _ _ _ _ (hq _ (by omega) (by omega))])⟩
  rcases hop with rfl | rfl | rfl
  · simp [emitShift, execInstrsWith, stepInstrWith, evalOperand, lookupReg, c64, mBit, resV,
      binResult, shiftResult, flagsOverflow, bindReg, hdr, hdl0, hnle]
    congr 1
    exact u64_shl_masked_bv a b
  · simp [emitShift, execInstrsWith, stepInstrWith, evalOperand, lookupReg, c64, mBit, resV,
      binResult, shiftResult, flagsOverflow, bindReg, hdr, hdl0, hnle]
    congr 1
    exact u64_shr_masked_bv a b
  · simp [emitShift, execInstrsWith, stepInstrWith, evalOperand, lookupReg, c64, mBit, resV,
      binResult, shiftResult, flagsOverflow, bindReg, hdr, hdl0, hnle]
    congr 1
    exact u64_ashr_masked_bv a b

theorem emitCmp_exec
    (runCall : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal →
      ExecOutcome ⊕ ExecState)
    (st : ExecState) (k : Nat) (pred : ICmpPred) (dl dr : RegName) (wl wr : BitVec 64)
    (hdl : st.regs.lookup dl = some (.bits .i64 wl))
    (hdr : st.regs.lookup dr = some (.bits .i64 wr)) :
    ∃ st', execInstrsWith runCall st (emitCmp k pred (.reg dl) (.reg dr)).2.2 = .inr st' ∧
      st'.mem = st.mem ∧ st'.globals = st.globals ∧ st'.prevBlock = st.prevBlock ∧
      st'.regs.lookup (tmpReg (k + 1)) =
        some (.bits .i64 (if icmpEval pred .i64 wl wr then 1#64 else 0#64)) ∧
      (∀ q, (∀ j, k ≤ j → j < k + 2 → q ≠ tmpReg j) → st'.regs.lookup q = st.regs.lookup q) := by
  let cBit : BitVec 1 := if icmpEval pred .i64 wl wr then 1#1 else 0#1
  let resV : BitVec 64 := if icmpEval pred .i64 wl wr then 1#64 else 0#64
  refine ⟨{ st with regs := (tmpReg (k + 1), .bits .i64 resV) :: (tmpReg k, .bits .i1 cBit) :: st.regs },
    ?_, rfl, rfl, rfl, lookup_cons_self _ _ _,
    fun q hq => by repeat (rw [lookup_cons_ne _ _ _ _ (hq _ (by omega) (by omega))])⟩
  simp [emitCmp, execInstrsWith, stepInstrWith, evalOperand, lookupReg, w64, IntWidth.bits, bindReg,
    hdl, hdr, cBit, resV, zext_i1_to_i64]

theorem finishScalarTail
    (runCall : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal →
      ExecOutcome ⊕ ExecState)
    (env : VarEnv) (se : ScalarExpr) (st stP : ExecState) (k kMid dIdx kEnd : Nat)
    (ty : LNIRType) (pfx ops : List LLVMInstr) (v : Val) (w : BitVec 64)
    (hle1 : k ≤ kMid) (hle2 : kMid ≤ kEnd) (hd : dIdx < kEnd)
    (hEv : evalScalarExpr env se = .ok v)
    (hEnc : encodeScalarTyped ty v = some w)
    (hPfx : execInstrsWith runCall st pfx = .inr stP)
    (hStP : stP.mem = st.mem ∧ stP.globals = st.globals ∧ stP.prevBlock = st.prevBlock)
    (hFrP : ∀ q, (∀ j, k ≤ j → j < kMid → q ≠ tmpReg j) → stP.regs.lookup q = st.regs.lookup q)
    (hOps : ∃ stF, execInstrsWith runCall stP ops = .inr stF ∧
      stF.mem = stP.mem ∧ stF.globals = stP.globals ∧ stF.prevBlock = stP.prevBlock ∧
      stF.regs.lookup (tmpReg dIdx) = some (.bits .i64 w) ∧
      (∀ q, (∀ j, kMid ≤ j → j < kEnd → q ≠ tmpReg j) → stF.regs.lookup q = stP.regs.lookup q)) :
    ScalarExecPost runCall env se st k ⟨ty, tmpReg dIdx, kEnd, pfx ++ ops⟩ := by
  rcases hOps with ⟨stF, hExF, hMemF, hGlobF, hPrevF, hLookF, hFrF⟩
  refine ⟨Nat.le_trans hle1 hle2, fresh_tmp_after dIdx kEnd hd, v, w, stF, hEv, hEnc, ?_,
    hMemF.trans hStP.1, hGlobF.trans hStP.2.1, hPrevF.trans hStP.2.2, hLookF,
    frame_tmp_Range st.regs stP.regs stF.regs k kMid kEnd hle1 hle2 hFrP hFrF⟩
  rw [execInstrsWith_append runCall st stP pfx ops hPfx]
  exact hExF

/-- Executing the 1–4 instruction tail emitted by `lowerBinOp64` produces `evalBinOp op (.u64 a) (.u64 b)`. -/
theorem lowerBinOp64_exec
    (runCall : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal →
      ExecOutcome ⊕ ExecState)
    (stR : ExecState) (op : BinOp) (rl rr res : ScalarLowerRes) (a b : UInt64)
    (hLookL : stR.regs.lookup rl.dst = some (.bits .i64 a.toBitVec))
    (hLookR : stR.regs.lookup rr.dst = some (.bits .i64 b.toBitVec))
    (hFrL : ∀ j, rr.nextTmp ≤ j → rl.dst ≠ tmpReg j)
    (hFrR : ∀ j, rr.nextTmp ≤ j → rr.dst ≠ tmpReg j)
    (hLow : lowerBinOp64 op rl rr = some res) :
    ∃ (dIdx : Nat) (ops : List LLVMInstr) (v : Val) (w : BitVec 64) (st' : ExecState),
      rr.nextTmp ≤ dIdx ∧ dIdx < res.nextTmp ∧
      res.dst = tmpReg dIdx ∧
      res.instrs = (rl.instrs ++ rr.instrs) ++ ops ∧
      evalBinOp op (.u64 a) (.u64 b) = .ok v ∧
      encodeScalarTyped res.ty v = some w ∧
      execInstrsWith runCall stR ops = .inr st' ∧
      st'.mem = stR.mem ∧ st'.globals = stR.globals ∧ st'.prevBlock = stR.prevBlock ∧
      st'.regs.lookup (tmpReg dIdx) = some (.bits .i64 w) ∧
      (∀ q, (∀ j, rr.nextTmp ≤ j → j < res.nextTmp → q ≠ tmpReg j) →
        st'.regs.lookup q = stR.regs.lookup q) := by
  have oneStep := fun (instr : LLVMInstr) (w : BitVec 64)
      (hS : stepInstrWith runCall stR instr =
        .inr (bindReg stR (tmpReg rr.nextTmp) (.bits .i64 w))) =>
    singleBin_exec runCall stR rr.nextTmp instr w hS
  cases op <;> simp only [lowerBinOp64, Option.some.injEq] at hLow
  all_goals try contradiction
  all_goals subst hLow
  · rcases oneStep (.add (tmpReg rr.nextTmp) .none .i64 (.reg rl.dst) (.reg rr.dst)) (a + b).toBitVec
      (by simp [stepInstrWith, evalOperand, lookupReg, hLookL, hLookR, binResult, flagsOverflow]; rfl) with
      ⟨st', hEx, hM, hG, hP, hLk, hFr⟩
    exact ⟨rr.nextTmp, _, .u64 (a + b), (a + b).toBitVec, st', Nat.le_refl _, Nat.lt_succ_self _,
      rfl, rfl, rfl, rfl, hEx, hM, hG, hP, hLk, hFr⟩
  · rcases oneStep (.sub (tmpReg rr.nextTmp) .none .i64 (.reg rl.dst) (.reg rr.dst)) (a - b).toBitVec
      (by simp [stepInstrWith, evalOperand, lookupReg, hLookL, hLookR, binResult, flagsOverflow]; rfl) with
      ⟨st', hEx, hM, hG, hP, hLk, hFr⟩
    exact ⟨rr.nextTmp, _, .u64 (a - b), (a - b).toBitVec, st', Nat.le_refl _, Nat.lt_succ_self _,
      rfl, rfl, rfl, rfl, hEx, hM, hG, hP, hLk, hFr⟩
  · rcases oneStep (.mul (tmpReg rr.nextTmp) .none .i64 (.reg rl.dst) (.reg rr.dst)) (a * b).toBitVec
      (by simp [stepInstrWith, evalOperand, lookupReg, hLookL, hLookR, binResult, flagsOverflow]; rfl) with
      ⟨st', hEx, hM, hG, hP, hLk, hFr⟩
    exact ⟨rr.nextTmp, _, .u64 (a * b), (a * b).toBitVec, st', Nat.le_refl _, Nat.lt_succ_self _,
      rfl, rfl, rfl, rfl, hEx, hM, hG, hP, hLk, hFr⟩
  · rcases emitDivRem_exec runCall stR rr.nextTmp false rl.dst rr.dst a b hLookL hLookR hFrL hFrR with
      ⟨st', hEx, hM, hG, hP, hLk, hFr⟩
    exact ⟨rr.nextTmp + 3, _, .u64 (a / b), (a / b).toBitVec, st', Nat.le_add_right _ 3,
      by dsimp only [emitDivRem]; omega, rfl, rfl, rfl, rfl, hEx, hM, hG, hP, hLk, hFr⟩
  · rcases emitDivRem_exec runCall stR rr.nextTmp true rl.dst rr.dst a b hLookL hLookR hFrL hFrR with
      ⟨st', hEx, hM, hG, hP, hLk, hFr⟩
    exact ⟨rr.nextTmp + 3, _, .u64 (a % b), (a % b).toBitVec, st', Nat.le_add_right _ 3,
      by dsimp only [emitDivRem]; omega, rfl, rfl, rfl, rfl, hEx, hM, hG, hP, hLk, hFr⟩
  · rcases oneStep (.and_ (tmpReg rr.nextTmp) .i64 (.reg rl.dst) (.reg rr.dst)) (a &&& b).toBitVec
      (by simp [stepInstrWith, evalOperand, lookupReg, hLookL, hLookR, binResult, flagsOverflow]; rfl) with
      ⟨st', hEx, hM, hG, hP, hLk, hFr⟩
    exact ⟨rr.nextTmp, _, .u64 (a &&& b), (a &&& b).toBitVec, st', Nat.le_refl _, Nat.lt_succ_self _,
      rfl, rfl, rfl, rfl, hEx, hM, hG, hP, hLk, hFr⟩
  · rcases oneStep (.or_ (tmpReg rr.nextTmp) .i64 (.reg rl.dst) (.reg rr.dst)) (a ||| b).toBitVec
      (by simp [stepInstrWith, evalOperand, lookupReg, hLookL, hLookR, binResult, flagsOverflow]; rfl) with
      ⟨st', hEx, hM, hG, hP, hLk, hFr⟩
    exact ⟨rr.nextTmp, _, .u64 (a ||| b), (a ||| b).toBitVec, st', Nat.le_refl _, Nat.lt_succ_self _,
      rfl, rfl, rfl, rfl, hEx, hM, hG, hP, hLk, hFr⟩
  · rcases oneStep (.xor (tmpReg rr.nextTmp) .i64 (.reg rl.dst) (.reg rr.dst)) (a ^^^ b).toBitVec
      (by simp [stepInstrWith, evalOperand, lookupReg, hLookL, hLookR, binResult, flagsOverflow]; rfl) with
      ⟨st', hEx, hM, hG, hP, hLk, hFr⟩
    exact ⟨rr.nextTmp, _, .u64 (a ^^^ b), (a ^^^ b).toBitVec, st', Nat.le_refl _, Nat.lt_succ_self _,
      rfl, rfl, rfl, rfl, hEx, hM, hG, hP, hLk, hFr⟩
  · rcases emitShift_exec runCall stR rr.nextTmp .shl rl.dst rr.dst a b (Or.inl rfl) hLookL hLookR hFrL with
      ⟨st', hEx, hM, hG, hP, hLk, hFr⟩
    exact ⟨rr.nextTmp + 1, _, .u64 (a <<< b), (a <<< b).toBitVec, st', Nat.le_succ _,
      by dsimp only [emitShift]; omega, rfl, rfl, rfl, rfl, hEx, hM, hG, hP, hLk, hFr⟩
  · rcases emitShift_exec runCall stR rr.nextTmp .shr rl.dst rr.dst a b (Or.inr (Or.inl rfl))
      hLookL hLookR hFrL with ⟨st', hEx, hM, hG, hP, hLk, hFr⟩
    exact ⟨rr.nextTmp + 1, _, .u64 (a >>> b), (a >>> b).toBitVec, st', Nat.le_succ _,
      by dsimp only [emitShift]; omega, rfl, rfl, rfl, rfl, hEx, hM, hG, hP, hLk, hFr⟩
  · rcases emitShift_exec runCall stR rr.nextTmp .sar rl.dst rr.dst a b (Or.inr (Or.inr rfl))
      hLookL hLookR hFrL with ⟨st', hEx, hM, hG, hP, hLk, hFr⟩
    exact ⟨rr.nextTmp + 1, _, .u64 (lnirSar64 a b), (lnirSar64 a b).toBitVec, st', Nat.le_succ _,
      by dsimp only [emitShift]; omega, rfl, rfl, rfl, rfl, hEx, hM, hG, hP, hLk, hFr⟩
  · rcases emitCmp_exec runCall stR rr.nextTmp .eq rl.dst rr.dst a.toBitVec b.toBitVec hLookL hLookR with
      ⟨st', hEx, hM, hG, hP, hLk, hFr⟩
    exact ⟨rr.nextTmp + 1, _, .bool (a == b), if a == b then 1#64 else 0#64, st', Nat.le_succ _,
      by dsimp only [emitCmp]; omega, rfl, rfl, rfl, rfl, hEx, hM, hG, hP, hLk, hFr⟩
  · rcases emitCmp_exec runCall stR rr.nextTmp .ult rl.dst rr.dst a.toBitVec b.toBitVec hLookL hLookR with
      ⟨st', hEx, hM, hG, hP, hLk, hFr⟩
    exact ⟨rr.nextTmp + 1, _, .bool (decide (a < b)), if decide (a < b) then 1#64 else 0#64, st',
      Nat.le_succ _, by dsimp only [emitCmp]; omega, rfl, rfl, rfl, rfl, hEx, hM, hG, hP, hLk, hFr⟩
  · rcases emitCmp_exec runCall stR rr.nextTmp .ule rl.dst rr.dst a.toBitVec b.toBitVec hLookL hLookR with
      ⟨st', hEx, hM, hG, hP, hLk, hFr⟩
    exact ⟨rr.nextTmp + 1, _, .bool (decide (a ≤ b)), if decide (a ≤ b) then 1#64 else 0#64, st',
      Nat.le_succ _, by dsimp only [emitCmp]; omega, rfl, rfl, rfl, rfl, hEx, hM, hG, hP, hLk, hFr⟩

/-- Structural inversion for `lowerBinOpStep`. -/
theorem lowerBinOpStep_inv (op : BinOp) (rl rr res : ScalarLowerRes)
    (h : lowerBinOpStep op rl rr = some res) :
    (rl.ty = .i64 ∧ rr.ty = .i64 ∧ lowerBinOp64 op rl rr = some res) ∨
    (rl.ty = .i1 ∧ rr.ty = .i1 ∧ op = .eq ∧
      res = ⟨.i1, (emitCmp rr.nextTmp .eq (.reg rl.dst) (.reg rr.dst)).1,
        (emitCmp rr.nextTmp .eq (.reg rl.dst) (.reg rr.dst)).2.1,
        (rl.instrs ++ rr.instrs) ++ (emitCmp rr.nextTmp .eq (.reg rl.dst) (.reg rr.dst)).2.2⟩) := by
  cases h1 : rl.ty <;> simp only [lowerBinOpStep, h1] at h
  all_goals try contradiction
  · cases h2 : rr.ty <;> simp only [h2] at h
    all_goals try contradiction
    cases op <;> simp only [Option.some.injEq] at h
    all_goals try contradiction
    exact Or.inr ⟨rfl, rfl, rfl, h.symm⟩
  · cases h2 : rr.ty <;> simp only [h2] at h
    all_goals try contradiction
    exact Or.inl ⟨rfl, rfl, h⟩

/-- Two-instruction execution lemma for `.select` (`icmp ne` + `select`). -/
theorem emitSelect_exec
    (runCall : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal →
      ExecOutcome ⊕ ExecState)
    (stE : ExecState) (k : Nat) (dc dt de : RegName) (wc wt we : BitVec 64)
    (hC : stE.regs.lookup dc = some (.bits .i64 wc))
    (hT : stE.regs.lookup dt = some (.bits .i64 wt))
    (hE : stE.regs.lookup de = some (.bits .i64 we))
    (hFrT : dt ≠ tmpReg k) (hFrE : de ≠ tmpReg k) :
    ∃ stF, execInstrsWith runCall stE
        [ .icmp (tmpReg k) .ne w64 (.reg dc) (c64 0)
        , .select (tmpReg (k + 1)) (.reg (tmpReg k)) w64 (.reg dt) (.reg de) ] = .inr stF ∧
      stF.mem = stE.mem ∧ stF.globals = stE.globals ∧ stF.prevBlock = stE.prevBlock ∧
      stF.regs.lookup (tmpReg (k + 1)) = some (.bits .i64 (if wc != 0#64 then wt else we)) ∧
      (∀ q, (∀ j, k ≤ j → j < k + 2 → q ≠ tmpReg j) → stF.regs.lookup q = stE.regs.lookup q) := by
  have hT1 : ∀ b0, ((tmpReg k, b0) :: stE.regs).lookup dt = some (.bits .i64 wt) :=
    fun _ => by
      rw [lookup_cons_ne _ _ _ _ hFrT]
      exact hT
  have hE1 : ∀ b0, ((tmpReg k, b0) :: stE.regs).lookup de = some (.bits .i64 we) :=
    fun _ => by
      rw [lookup_cons_ne _ _ _ _ hFrE]
      exact hE
  let zBit : BitVec 1 := if wc != 0#64 then 1#1 else 0#1
  let selW : BitVec 64 := if wc != 0#64 then wt else we
  refine ⟨{ stE with regs := (tmpReg (k + 1), .bits .i64 selW) :: (tmpReg k, .bits .i1 zBit) :: stE.regs },
    ?_, rfl, rfl, rfl, lookup_cons_self _ _ _, ?_⟩
  · have h11 : (@BEq.beq (BitVec IntWidth.i1.bits) _ 1#1 1#1) = true := BEq.refl _
    by_cases hwc : wc = 0#64
    · subst hwc
      simp [execInstrsWith, stepInstrWith, evalOperand, evalTypedOperand, lookupReg,
        icmpEval, w64, c64, IntWidth.bits, bindReg, hC, hE1, zBit, selW]
    · have hne1 : (wc != 0#64) = true := by simp [bne_iff_ne, hwc]
      have hne2 : (@bne (BitVec IntWidth.i64.bits) _ wc 0#64) = true := hne1
      simp [execInstrsWith, stepInstrWith, evalOperand, evalTypedOperand, lookupReg,
        icmpEval, w64, c64, bindReg, hC, hT1, zBit, selW, hne1, hne2, h11]
  · intro q hq
    rw [lookup_cons_ne _ _ _ _ (hq (k + 1) (Nat.le_succ k) (Nat.lt_succ_self (k + 1))),
        lookup_cons_ne _ _ _ _ (hq k (Nat.le_refl k) (Nat.lt_add_of_pos_right (Nat.zero_lt_succ 1)))]

/-- Two-instruction execution lemma for `.fma` (`mul` + `add`). -/
theorem emitFma_exec
    (runCall : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal →
      ExecOutcome ⊕ ExecState)
    (stC : ExecState) (k : Nat) (da db dc : RegName) (na nb nc : UInt64)
    (hA : stC.regs.lookup da = some (.bits .i64 na.toBitVec))
    (hB : stC.regs.lookup db = some (.bits .i64 nb.toBitVec))
    (hC : stC.regs.lookup dc = some (.bits .i64 nc.toBitVec))
    (hFrC : dc ≠ tmpReg k) :
    ∃ stF, execInstrsWith runCall stC
        [ .mul (tmpReg k) .none .i64 (.reg da) (.reg db)
        , .add (tmpReg (k + 1)) .none .i64 (.reg (tmpReg k)) (.reg dc) ] = .inr stF ∧
      stF.mem = stC.mem ∧ stF.globals = stC.globals ∧ stF.prevBlock = stC.prevBlock ∧
      stF.regs.lookup (tmpReg (k + 1)) = some (.bits .i64 (na * nb + nc).toBitVec) ∧
      (∀ q, (∀ j, k ≤ j → j < k + 2 → q ≠ tmpReg j) → stF.regs.lookup q = stC.regs.lookup q) := by
  have hC1 : ∀ p0, ((tmpReg k, p0) :: stC.regs).lookup dc = some (.bits .i64 nc.toBitVec) :=
    fun _ => by
      rw [lookup_cons_ne _ _ _ _ hFrC]
      exact hC
  let prodV : BitVec 64 := na.toBitVec * nb.toBitVec
  let resV : BitVec 64 := prodV + nc.toBitVec
  refine ⟨{ stC with regs := (tmpReg (k + 1), .bits .i64 resV) :: (tmpReg k, .bits .i64 prodV) :: stC.regs },
    ?_, rfl, rfl, rfl, ?_, ?_⟩
  · simp [execInstrsWith, stepInstrWith, evalOperand, lookupReg, binResult, flagsOverflow,
      bindReg, hA, hB, hC1, prodV, resV]
    exact ⟨rfl, rfl⟩
  · simp [prodV, resV]
  · intro q hq
    rw [lookup_cons_ne _ _ _ _ (hq (k + 1) (Nat.le_succ k) (Nat.lt_succ_self (k + 1))),
        lookup_cons_ne _ _ _ _ (hq k (Nat.le_refl k) (Nat.lt_add_of_pos_right (Nat.zero_lt_succ 1)))]

end LeanNative.Proofs
