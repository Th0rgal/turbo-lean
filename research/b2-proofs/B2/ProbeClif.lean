import FV.Clif.Run
import LeanNative.Semantics.Eval

/-! Probe (Q1/Q2/Q4): one module that sees both clifv's CLIF semantics (`Clif.Sem`, `Clif.runLoop`)
and the vendored LNIR evaluator (`evalBinOp`, `evalCode`) on Lean v4.34.1.
Every theorem below is **sorry-free** and about the two repos' own definitions. -/

namespace B2.Probe

open LeanNative.IR LeanNative.Semantics

/-! ## Agreements (u64 ↔ i64) -/

theorem add_agrees (a b : UInt64) :
    evalBinOp .add (.u64 a) (.u64 b) = .ok (.u64 (a + b)) ∧
    Clif.Sem.iadd a.toBitVec b.toBitVec = (a + b).toBitVec := ⟨rfl, rfl⟩

theorem sub_agrees (a b : UInt64) :
    evalBinOp .sub (.u64 a) (.u64 b) = .ok (.u64 (a - b)) ∧
    Clif.Sem.isub a.toBitVec b.toBitVec = (a - b).toBitVec := ⟨rfl, rfl⟩

theorem mul_agrees (a b : UInt64) :
    evalBinOp .mul (.u64 a) (.u64 b) = .ok (.u64 (a * b)) ∧
    Clif.Sem.imul a.toBitVec b.toBitVec = (a * b).toBitVec := ⟨rfl, rfl⟩

/-- Shift amounts: LNIR `UInt64 <<<` reduces mod 64, as CLIF `shiftAmt 64`. -/
theorem shl_agrees (a b : UInt64) :
    evalBinOp .shl (.u64 a) (.u64 b) = .ok (.u64 (a <<< b)) ∧
    Clif.Sem.ishl a.toBitVec b.toBitVec = (a <<< b).toBitVec := by
  refine ⟨rfl, ?_⟩
  simp [Clif.Sem.ishl, Clif.Sem.shiftAmt, UInt64.toBitVec_shiftLeft]

theorem shr_agrees (a b : UInt64) :
    evalBinOp .shr (.u64 a) (.u64 b) = .ok (.u64 (a >>> b)) ∧
    Clif.Sem.ushr a.toBitVec b.toBitVec = (a >>> b).toBitVec := by
  refine ⟨rfl, ?_⟩
  simp [Clif.Sem.ushr, Clif.Sem.shiftAmt, UInt64.toBitVec_shiftRight]

/-- Nonzero divisor: LNIR `div` = CLIF `udiv`. -/
theorem div_agrees_nonzero (a b : UInt64) (hb : b ≠ 0) :
    evalBinOp .div (.u64 a) (.u64 b) = .ok (.u64 (a / b)) ∧
    Clif.Sem.udiv a.toBitVec b.toBitVec = .ok (a / b).toBitVec := by
  refine ⟨rfl, ?_⟩
  have : b.toBitVec ≠ 0 := fun h => hb (UInt64.toBitVec_inj.mp (by simpa using h))
  simp only [Clif.Sem.udiv, this, ite_false, UInt64.toBitVec_div]

/-! ## Mismatch (Q4 evidence): division by zero -/

/-- LNIR returns `0` for `x / 0` (Lean `UInt64` division is total). -/
theorem lnir_div_zero (a : UInt64) : evalBinOp .div (.u64 a) (.u64 0) = .ok (.u64 0) := by
  show Except.ok (Val.u64 (a / 0)) = _
  rw [UInt64.div_zero]

/-- CLIF `udiv x, 0` traps `int_divz`. -/
theorem clif_udiv_zero (a : UInt64) :
    Clif.Sem.udiv a.toBitVec (0 : UInt64).toBitVec = .error .intDivz := by
  simp [Clif.Sem.udiv]

/-- LNIR returns `x` for `x % 0`. -/
theorem lnir_mod_zero (a : UInt64) : evalBinOp .mod (.u64 a) (.u64 0) = .ok (.u64 a) := by
  show Except.ok (Val.u64 (a % 0)) = _
  rw [UInt64.mod_zero]

theorem clif_urem_zero (a : UInt64) :
    Clif.Sem.urem a.toBitVec (0 : UInt64).toBitVec = .error .intDivz := by
  simp [Clif.Sem.urem]

/-! ## Mismatch (Q4 evidence): LNIR accepts ill-typed operand pairs -/

/-- `add` with a zero `u64` returns the other operand whatever its type — e.g. a `bool`. -/
theorem lnir_add_bool_zero (b : Bool) :
    evalBinOp .add (.bool b) (.u64 0) = .ok (.bool b) := rfl

/-- `bitAnd` on two equal non-numeric values succeeds. -/
theorem lnir_bitAnd_bool (b : Bool) :
    evalBinOp .bitAnd (.bool b) (.bool b) = .ok (.bool b) := by
  cases b <;> rfl

/-! ## Statement mentioning both semantics elaborates -/

def BothVisible : Prop :=
  ∀ (code : LNIRCode) (env : Clif.Env) (p : Clif.Program) (cs : Clif.State) (fuel : Nat),
    (∃ v st', evalCode fuel VarEnv.empty ⟨[], 0, [], []⟩ code = .ok (v, st')) →
    ∃ vals m, Clif.runLoop env p fuel cs = .returned vals m

end B2.Probe
