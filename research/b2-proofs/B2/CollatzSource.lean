import B2.Kernel

/-! All-input arithmetic characterization of the actual LNIR benchmark evaluator.
The body is projected from Codec.collatzStepsDecl, not a second source program. -/
namespace B2.CollatzSource
open LeanNative.IR LeanNative.Semantics

def body : LNIRCode :=
  match Codec.collatzStepsDecl.body with
  | .letBind _ _ _ (.seqFor _ _ _ _ _ _ b _) => b
  | _ => .unreachable

def step (x : UInt64) : UInt64 := ((x * 2 + x + 1) / 2) + 0

theorem body_eval (fuel : Nat) (env : VarEnv) (st : HeapState) (i x : UInt64) :
    evalCode fuel ((env.bind 3 (.u64 i)).bind 4 (.u64 x)) st body =
      .ok (.u64 (step x), st) := rfl

theorem repeat_step (count : Nat) (x : UInt64) :
    Nat.repeat step count (step x) = step (Nat.repeat step count x) := by
  induction count with
  | zero => rfl
  | succ count ih => exact congrArg step ih

theorem loop_eval (fuel count i : Nat) (x : UInt64) (env : VarEnv) (st : HeapState) :
    evalSeqLoop count i 3 4 (.u64 x) env st
      (fun e s => evalCode fuel e s body) =
      .ok (.u64 (Nat.repeat step count x), st) := by
  induction count generalizing i x with
  | zero => rfl
  | succ count ih => simpa only [evalSeqLoop, body_eval, Nat.repeat, repeat_step] using ih (i + 1) (step x)

theorem collatz_eval (fuel : Nat) (n steps : UInt64) (st : HeapState) :
    evalCode fuel (B2.entryEnv Codec.collatzStepsDecl [.u64 n, .u64 steps]) st
      Codec.collatzStepsDecl.body =
      .ok (.u64 (Nat.repeat step steps.toNat n), st) := by
  change (match evalSeqLoop steps.toNat 0 3 4 (.u64 n)
      ((B2.entryEnv Codec.collatzStepsDecl [.u64 n, .u64 steps]).bind 2 (.u64 0)) st
      (fun e s => evalCode fuel e s body) with
    | .ok (a, s) => Except.ok (a, s)
    | .error e => Except.error e) =
      (Except.ok (.u64 (Nat.repeat step steps.toNat n), st) : Except UBError (Val × HeapState))
  rw [loop_eval]

#print axioms collatz_eval
end B2.CollatzSource
