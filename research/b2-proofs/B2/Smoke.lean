import B2.Lowering
import LeanNative.IR.Codec
import FV.Clif.Run

/-! Kernel-evaluated regression checks of the real executable lowering and CLIF run.
These are examples, not the all-input O3 simulation obligation. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace B2.Smoke
open LeanNative.IR LeanNative.Backend.Clif

def collatz : Clif.Function :=
  (lowerDecl Codec.collatzStepsDecl).toOption.getD default

theorem collatz_lowered : lowerDecl Codec.collatzStepsDecl = .ok collatz := by
  have h : (lowerDecl Codec.collatzStepsDecl).isOk = true := by decide +kernel
  unfold collatz
  cases hl : lowerDecl Codec.collatzStepsDecl with
  | error e => rw [hl] at h; cases h
  | ok f => rfl

def result (d : LNIRDecl) (args : List Clif.Val) (fuel := 300) : Option (List Clif.Val) :=
  match lowerDecl d with
  | .error _ => none
  | .ok f => (Clif.run .empty { funcs := [f] } f.name args fuel).returnedVals?

theorem collatz_3_5 :
    result Codec.collatzStepsDecl [Clif.Val.ofNat .i64 3, Clif.Val.ofNat .i64 5] =
      some [Clif.Val.ofNat .i64 27] := by decide +kernel

theorem collatz_zero_steps :
    result Codec.collatzStepsDecl [Clif.Val.ofNat .i64 42, Clif.Val.ofNat .i64 0] =
      some [Clif.Val.ofNat .i64 42] := by decide +kernel

def division (op : BinOp) : LNIRDecl :=
  { name := "division", params := [⟨0, "x", .i64, false⟩, ⟨1, "y", .i64, false⟩]
    retTy := .i64, body := .letBind 2 .i64 (.scalar (.binOp op (.var 0) (.var 1))) (.ret 2) }

theorem div_zero : result (division .div) [Clif.Val.ofNat .i64 37, Clif.Val.ofNat .i64 0] =
    some [Clif.Val.ofNat .i64 0] := by decide +kernel

theorem mod_zero : result (division .mod) [Clif.Val.ofNat .i64 37, Clif.Val.ofNat .i64 0] =
    some [Clif.Val.ofNat .i64 37] := by decide +kernel

theorem div_nonzero : result (division .div) [Clif.Val.ofNat .i64 37, Clif.Val.ofNat .i64 5] =
    some [Clif.Val.ofNat .i64 7] := by decide +kernel

theorem mod_nonzero : result (division .mod) [Clif.Val.ofNat .i64 37, Clif.Val.ofNat .i64 5] =
    some [Clif.Val.ofNat .i64 2] := by decide +kernel

/-- Shadows the outer index inside a loop body: the backedge must retain the header index. -/
def nested : LNIRDecl :=
  { name := "nested", params := [], retTy := .i64
    body := .letBind 0 .i64 (.scalar (.constU64 0)) <|
      .letBind 1 .i64 (.scalar (.constU64 2)) <|
      .seqFor 2 0 1 3 0 .i64
        (.seqFor 4 0 1 5 3 .i64
          (.letBind 6 .i64 (.scalar (.binOp .add (.var 5) (.constU64 1))) (.ret 6))
          (.letBind 2 .i64 (.scalar (.constU64 99)) (.ret 5)))
        (.ret 3) }

theorem nested_shadowing : result nested [] = some [Clif.Val.ofNat .i64 4] := by decide +kernel

def boolNot : LNIRDecl :=
  { name := "boolNot", params := [⟨0, "b", .i1, false⟩], retTy := .i1
    body := .letBind 1 .i1 (.scalar (.unaryOp .not (.var 0))) (.ret 1) }

theorem bool_not_true : result boolNot [Clif.Val.ofBool true] = some [Clif.Val.ofBool false] := by decide +kernel

def mixed : LNIRDecl :=
  { name := "bad", params := [], retTy := .i1
    body := .letBind 0 .i1 (.scalar (.binOp .add (.constBool true) (.constU64 0))) (.ret 0) }

theorem rejects_mixed : (lowerDecl mixed).isOk = false := by decide +kernel

#print axioms collatz_lowered
#print axioms collatz_3_5
#print axioms nested_shadowing
end B2.Smoke
