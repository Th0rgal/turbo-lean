import LeanNative.Backend.LLVMAst.Syntax
import LeanNative.Backend.LLVMAst.Eval

namespace LeanNative.Backend.LLVMAst

open LeanNative.Backend.TargetIR

theorem add_nsw_overflow_poison (w : IntWidth) (a b : BitVec w.bits)
    (h_ov : addOverflowNSW w a b = true) :
    stepInstr {} 1 {} (.add "r" .nsw w (.constInt w a) (.constInt w b)) =
      .inr (bindReg {} "r" .poison) := by
  simp [stepInstr, stepInstrWith, evalOperand, binResult, flagsOverflow, h_ov]

theorem shl_overshift_poison (w : IntWidth) (a amt : BitVec w.bits)
    (h_over : w.bits ≤ amt.toNat) :
    stepInstr {} 1 {} (.shl "r" .none w (.constInt w a) (.constInt w amt)) =
      .inr (bindReg {} "r" .poison) := by
  simp [stepInstr, stepInstrWith, evalOperand, shiftResult, h_over]

theorem udiv_zero_ub (w : IntWidth) (a : BitVec w.bits) :
    stepInstr {} 1 {} (.udiv "r" false w (.constInt w a) (.constInt w (0#w.bits))) =
      .inl (.ub "division by zero") := by
  simp [stepInstr, stepInstrWith, evalOperand, divOrRem]

theorem phi_resolves_predecessor (st : ExecState) (ty : LLVMType) (lbl : BlockLabel) (op : Operand) :
    resolvePhi st ty (some lbl) [(op, lbl)] = evalTypedOperand st ty op := by
  simp [resolvePhi]

theorem phi_parallel_swap (st : ExecState) (lbl : BlockLabel) (a b : Operand) :
    evalPhis st (some lbl)
      [{ dst := "x", ty := .int .i64, incomings := [(b, lbl)] },
       { dst := "y", ty := .int .i64, incomings := [(a, lbl)] }] =
      [("x", evalTypedOperand st (.int .i64) b), ("y", evalTypedOperand st (.int .i64) a)] := by
  simp [evalPhis, resolvePhi]

theorem writeBytesAt_allocs (m : ByteMem) (base : Nat) (bs : List MemByte) :
    (m.writeBytesAt base bs).allocs = m.allocs := by
  induction bs generalizing m base with
  | nil => rfl
  | cons b rest ih =>
    simp [ByteMem.writeBytesAt, ByteMem.writeAt, ih]

theorem accessInAlloc_writeBytesAt (m : ByteMem) (base : Nat) (bs : List MemByte)
    (addr n : Nat) (needWrite : Bool) :
    (m.writeBytesAt base bs).accessInAlloc addr n needWrite = m.accessInAlloc addr n needWrite := by
  simp [ByteMem.accessInAlloc, ByteMem.findAlloc, writeBytesAt_allocs]

theorem accessInAlloc_read_of_write (m : ByteMem) (addr n : Nat)
    (h : m.accessInAlloc addr n true = true) :
    m.accessInAlloc addr n false = true := by
  unfold ByteMem.accessInAlloc at h ⊢
  cases hf : m.findAlloc addr with
  | none => simp [hf] at h
  | some b =>
    simp only [hf, Bool.not_true, Bool.false_or, Bool.not_false, Bool.true_or, Bool.and_true] at h ⊢
    exact (Bool.and_eq_true_iff.mp h).1

theorem load_after_alloca_store (st : ExecState) (w : IntWidth) (v : BitVec w.bits) (align : Nat)
    (h_pow : isPow2 align = true)
    (h_sz : 0 < w.byteSize)
    (ptr : BitVec 64) (mem1 : ByteMem)
    (h_alloc : st.mem.allocAligned w.byteSize align = some (ptr, mem1)) :
    ∃ mem2, stepInstr {} 1 { st with mem := mem1, regs := [("p", .ptr ptr)] }
        (.store false (.int w) (.constInt w v) (.reg "p") align) =
        .inr { st with mem := mem2, regs := [("p", .ptr ptr)] } ∧
      stepInstr {} 1 { st with mem := mem2, regs := [("p", .ptr ptr)] }
        (.load "out" false (.int w) (.reg "p") align) =
        .inr (bindReg { st with mem := mem2, regs := [("p", .ptr ptr)] } "out" (.bits w v)) := by
  have h_ok := ByteMem.allocAligned_accessOk st.mem w.byteSize align true ptr mem1 h_pow h_sz h_alloc
  have h_nz := ByteMem.allocAligned_nonzero st.mem w.byteSize align true ptr mem1 h_alloc
  have h_al := ByteMem.allocAligned_isAligned st.mem w.byteSize align true ptr mem1 h_pow h_alloc
  have h_in1 : mem1.accessInAlloc ptr.toNat w.byteSize true = true := by
    unfold ByteMem.accessOk at h_ok
    exact (Bool.and_eq_true_iff.mp h_ok).2
  have h_in2 : (mem1.storeInt ptr w v).accessInAlloc ptr.toNat w.byteSize false = true := by
    unfold ByteMem.storeInt
    rw [accessInAlloc_writeBytesAt]
    exact accessInAlloc_read_of_write mem1 ptr.toNat w.byteSize h_in1
  have h_take : ((mem1.storeInt ptr w v).readBytesAt ptr.toNat w.byteSize).take w.byteSize =
      (mem1.storeInt ptr w v).readBytesAt ptr.toNat w.byteSize := by
    apply List.take_of_length_le
    rw [ByteMem.readBytesAt_length]
    exact Nat.le_refl _
  have h_load : ByteMem.bytesToBv? w.bits
      (((mem1.storeInt ptr w v).readBytesAt ptr.toNat w.byteSize).take w.byteSize) = some v := by
    rw [h_take]
    exact ByteMem.loadInt?_storeInt_same mem1 ptr w v
  have h_anz : align ≠ 0 := by
    intro hz
    subst hz
    simp [isPow2] at h_pow
  have h_eff : effectiveAlign (.int w) align = align := by
    simp [effectiveAlign, h_anz]
  refine ⟨mem1.storeInt ptr w v, ?_, ?_⟩
  · simp [stepInstr, stepInstrWith, evalTypedOperand, evalOperand, lookupReg, accessCheck, h_eff,
      storeTypedVal, serializeTypedVal, serializeTypedValAux, LLVMType.sizeOfType, ByteMem.storeInt,
      LLVMType.byteSize, h_pow, h_nz, h_al, h_in1]
  · simp [stepInstr, stepInstrWith, evalOperand, lookupReg, accessCheck, h_eff, loadVal, deserializeVal,
      deserializeValAux, LLVMType.byteSize, h_pow, h_nz, h_al, h_in2, h_load]

theorem select_cond_poison (ty : LLVMType) (tOp eOp : Operand) :
    stepInstr {} 1 {} (.select "r" .poison ty tOp eOp) =
      .inr (bindReg {} "r" .poison) := by
  simp [stepInstr, stepInstrWith, evalOperand]

theorem execFnRel_iff (mod_ : LLVMModule) (fn : LLVMFn) (args : List LLVMVal) (fuel : Nat) (out : ExecOutcome) :
    ExecFnRel mod_ fn args fuel out ↔ execFn mod_ fn args fuel = out := by
  constructor
  · intro h
    cases h
    all_goals simp_all [execFn]
  · intro h
    unfold execFn at h
    cases hg : initGlobals mod_ with
    | none =>
      simp [hg] at h
      subst h
      exact ExecFnRel.noGlobals fuel hg
    | some pair =>
      cases pair with
      | mk mem0 globals =>
        simp [hg] at h
        cases hblocks : fn.blocks with
        | nil =>
          simp [hblocks] at h
          subst h
          exact ExecFnRel.noEntry fuel mem0 globals hg hblocks
        | cons entry rest =>
          simp [hblocks] at h
          cases hbind : bindArgs { mem := mem0, globals := globals } fn.params args with
          | none =>
            simp [hbind] at h
            subst h
            exact ExecFnRel.badArity fuel mem0 globals entry rest hg hblocks hbind
          | some st =>
            simp [hbind] at h
            exact ExecFnRel.ran fuel mem0 globals entry rest st out hg hblocks hbind h

theorem execFn_deterministic (mod_ : LLVMModule) (fn : LLVMFn) (args : List LLVMVal) (fuel : Nat)
    (out1 out2 : ExecOutcome)
    (h1 : ExecFnRel mod_ fn args fuel out1)
    (h2 : ExecFnRel mod_ fn args fuel out2) :
    out1 = out2 := by
  have e1 := (execFnRel_iff mod_ fn args fuel out1).mp h1
  have e2 := (execFnRel_iff mod_ fn args fuel out2).mp h2
  rw [← e1, e2]

theorem stepInstrWith_mono
    (rc1 rc2 : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal → ExecOutcome ⊕ ExecState)
    (st : ExecState) (ins : LLVMInstr)
    (hrc : ∀ st' dst? cc ty callee args,
      rc1 st' dst? cc ty callee args ≠ .inl .outOfFuel →
      rc2 st' dst? cc ty callee args = rc1 st' dst? cc ty callee args)
    (hfin : stepInstrWith rc1 st ins ≠ .inl .outOfFuel) :
    stepInstrWith rc2 st ins = stepInstrWith rc1 st ins := by
  cases ins with
  | call dst? retTy callee args cc =>
    simp only [stepInstrWith] at hfin ⊢
    exact hrc st dst? cc retTy callee (args.map fun pair => evalTypedOperand st pair.fst pair.snd) hfin
  | _ => rfl

theorem execInstrsWith_mono
    (rc1 rc2 : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal → ExecOutcome ⊕ ExecState)
    (st : ExecState) (is : List LLVMInstr)
    (hrc : ∀ st' dst? cc ty callee args,
      rc1 st' dst? cc ty callee args ≠ .inl .outOfFuel →
      rc2 st' dst? cc ty callee args = rc1 st' dst? cc ty callee args)
    (hfin : execInstrsWith rc1 st is ≠ .inl .outOfFuel) :
    execInstrsWith rc2 st is = execInstrsWith rc1 st is := by
  induction is generalizing st with
  | nil => rfl
  | cons ins rest ih =>
    simp only [execInstrsWith] at hfin ⊢
    have hstep : stepInstrWith rc1 st ins ≠ .inl .outOfFuel := by
      intro ho
      rw [ho] at hfin
      exact hfin rfl
    rw [stepInstrWith_mono rc1 rc2 st ins hrc hstep]
    cases hst : stepInstrWith rc1 st ins with
    | inl o => rfl
    | inr st' =>
      rw [hst] at hfin
      exact ih st' hfin

theorem execBlockWith_mono
    (rc1 rc2 : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal → ExecOutcome ⊕ ExecState)
    (fn : LLVMFn) (f1 f2 : Nat) (st : ExecState) (blk : LLVMBlock)
    (hrc : ∀ st' dst? cc ty callee args,
      rc1 st' dst? cc ty callee args ≠ .inl .outOfFuel →
      rc2 st' dst? cc ty callee args = rc1 st' dst? cc ty callee args)
    (hle : f1 ≤ f2)
    (hfin : execBlockWith rc1 fn f1 st blk ≠ .outOfFuel) :
    execBlockWith rc2 fn f2 st blk = execBlockWith rc1 fn f1 st blk := by
  induction f1 generalizing f2 st blk with
  | zero => exact False.elim (hfin rfl)
  | succ k ih =>
    cases f2 with
    | zero => omega
    | succ m =>
      simp only [execBlockWith] at hfin ⊢
      have his : execInstrsWith rc1 (commitPhis st (evalPhis st st.prevBlock blk.phis)) blk.body ≠ .inl .outOfFuel := by
        intro ho
        rw [ho] at hfin
        exact hfin rfl
      rw [execInstrsWith_mono rc1 rc2 (commitPhis st (evalPhis st st.prevBlock blk.phis)) blk.body hrc his]
      cases hexec : execInstrsWith rc1 (commitPhis st (evalPhis st st.prevBlock blk.phis)) blk.body with
      | inl out =>
        cases out <;> simp
      | inr st' =>
        simp only [hexec] at hfin ⊢
        cases hterm : blk.term with
        | br lbl =>
          simp only [hterm] at hfin ⊢
          cases hfind : findBlock fn lbl with
          | none => simp
          | some next =>
            simp only [hfind] at hfin ⊢
            exact ih m { st' with prevBlock := some blk.label } next (by omega) hfin
        | condBr condOp tLbl eLbl =>
          simp only [hterm] at hfin ⊢
          cases heval : evalOperand st' condOp with
          | poison => simp
          | bits wb vb =>
            cases wb with
            | i1 =>
              simp only [heval] at hfin ⊢
              cases hfind : findBlock fn (if vb == 1#1 then tLbl else eLbl) with
              | none => simp
              | some next =>
                simp only [hfind] at hfin ⊢
                exact ih m { st' with prevBlock := some blk.label } next (by omega) hfin
            | i8 | i16 | i32 | i64 | i128 | i256 | i512 => simp
          | ptr _ => simp
          | floatBits _ _ => simp
          | aggNil => simp
          | aggCons _ _ => simp
        | switch w scrutOp defLbl cases =>
          simp only [hterm] at hfin ⊢
          cases heval : evalOperand st' scrutOp with
          | poison => simp
          | bits ws sv =>
            by_cases hws : ws = w
            · subst hws
              simp only [heval, ↓reduceDIte] at hfin ⊢
              cases hfind : findBlock fn (((cases.find? (fun pair => pair.fst == sv)).map (·.snd)).getD defLbl) with
              | none => simp
              | some next =>
                simp only [hfind] at hfin ⊢
                exact ih m { st' with prevBlock := some blk.label } next (by omega) hfin
            · simp [hws]
          | ptr _ => simp
          | floatBits _ _ => simp
          | aggNil => simp
          | aggCons _ _ => simp
        | ret rv =>
          cases rv with
          | none => simp
          | some p =>
            cases p
            simp
        | unreachable => simp

theorem runCallWith_mono (mod_ : LLVMModule) (f1 f2 : Nat)
    (st : ExecState) (dst? : Option RegName) (callCc : CallingConv) (retTy : LLVMType) (callee : GlobalSym) (args : List LLVMVal)
    (hle : f1 ≤ f2)
    (hfin : runCallWith mod_ f1 st dst? callCc retTy callee args ≠ .inl .outOfFuel) :
    runCallWith mod_ f2 st dst? callCc retTy callee args = runCallWith mod_ f1 st dst? callCc retTy callee args := by
  induction f1 generalizing f2 st dst? callCc retTy callee args with
  | zero =>
    cases f2 with
    | zero => rfl
    | succ m =>
      simp only [runCallWith] at hfin ⊢
      by_cases htrap : callee == "llvm.trap"
      · simp [htrap]
      · simp only [htrap, Bool.false_eq_true, ↓reduceIte] at hfin ⊢
        cases hintr : intrinsicResult callee args with
        | some v => simp
        | none =>
          rw [hintr] at hfin
          exact False.elim (hfin rfl)
  | succ k ih =>
    cases f2 with
    | zero => omega
    | succ m =>
      simp only [runCallWith] at hfin ⊢
      by_cases htrap : callee == "llvm.trap"
      · simp [htrap]
      · simp only [htrap, Bool.false_eq_true, ↓reduceIte] at hfin ⊢
        cases hintr : intrinsicResult callee args with
        | some v => simp
        | none =>
          simp only [hintr] at hfin ⊢
          cases hfn : mod_.fns.find? (fun f => f.name == callee) with
          | none => rfl
          | some fn =>
            simp only [hfn] at hfin ⊢
            by_cases hcc : fn.cc != callCc
            · simp [hcc]
            · simp only [hcc, Bool.false_eq_true, ↓reduceIte] at hfin ⊢
              cases hblks : fn.blocks with
              | nil => rfl
              | cons entry rest =>
                simp only [hblks] at hfin ⊢
                cases hbind : bindArgs { mem := st.mem, globals := st.globals } fn.params args with
                | none => rfl
                | some calleeSt =>
                  simp only [hbind] at hfin ⊢
                  have hblkFin : execBlockWith (runCallWith mod_ k) fn (k + 1) calleeSt entry ≠ .outOfFuel := by
                    intro ho
                    rw [ho] at hfin
                    exact hfin rfl
                  have hrc_k : ∀ st' d cc ty c as,
                      runCallWith mod_ k st' d cc ty c as ≠ .inl .outOfFuel →
                      runCallWith mod_ m st' d cc ty c as = runCallWith mod_ k st' d cc ty c as := by
                    intro st' d cc ty c as hc
                    exact ih m st' d cc ty c as (by omega) hc
                  rw [execBlockWith_mono (runCallWith mod_ k) (runCallWith mod_ m) fn (k + 1) (m + 1)
                      calleeSt entry hrc_k (by omega) hblkFin]

theorem execBlock_mono (mod_ : LLVMModule) (fn : LLVMFn) (f1 f2 : Nat) (st : ExecState) (blk : LLVMBlock)
    (hle : f1 ≤ f2)
    (hfin : execBlock mod_ fn f1 st blk ≠ .outOfFuel) :
    execBlock mod_ fn f2 st blk = execBlock mod_ fn f1 st blk := by
  unfold execBlock at hfin ⊢
  have hblkFin : execBlockWith (runCallWith mod_ f1) fn f1 st blk ≠ .outOfFuel := by
    intro ho
    rw [ho] at hfin
    exact hfin rfl
  have heq := execBlockWith_mono (runCallWith mod_ f1) (runCallWith mod_ f2) fn f1 f2 st blk
    (fun st' dst? cc ty callee args hc => runCallWith_mono mod_ f1 f2 st' dst? cc ty callee args hle hc)
    hle hblkFin
  rw [heq]

theorem execFn_mono_fuel (mod_ : LLVMModule) (fn : LLVMFn) (args : List LLVMVal) (f1 f2 : Nat)
    (hle : f1 ≤ f2)
    (hfin : execFn mod_ fn args f1 ≠ .outOfFuel) :
    execFn mod_ fn args f2 = execFn mod_ fn args f1 := by
  unfold execFn at hfin ⊢
  cases hg : initGlobals mod_ with
  | none => simp
  | some pair =>
    cases pair with
    | mk mem0 globals =>
      simp only [hg] at hfin ⊢
      cases hblocks : fn.blocks with
      | nil => simp
      | cons entry rest =>
        cases hbind : bindArgs { mem := mem0, globals := globals } fn.params args with
        | none => simp
        | some st =>
          simp only [hblocks, hbind] at hfin ⊢
          exact execBlock_mono mod_ fn f1 f2 st entry hle hfin

end LeanNative.Backend.LLVMAst
