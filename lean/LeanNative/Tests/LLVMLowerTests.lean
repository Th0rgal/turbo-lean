import LeanNative.Backend.LLVMLower
import LeanNative.Backend.LLVMAst

/-!
# `LNIR → LLVMAst` lowering regressions (`LeanNative.Tests.LLVMLowerTests`)

Pure `#guard`s exercising `LeanNative.Backend.LLVMLower` against the independent
`LLVMAst.execFn` interpreter and the `LLVMAst.PP` textual emitter: scalar
arithmetic, masked shifts, guarded division, boolean comparisons, a multi-block
`ite` diamond, and the `M1`..`M5` emitter mutants.
-/

namespace LeanNative.Tests.LLVMLowerTests

open LeanNative.IR
open LeanNative.Backend.LLVMAst
open LeanNative.Backend.LLVMLower

def p64 (id : Nat) (name : String) : LNIRParam := { id := id, name := name, ty := .i64 }

def binDecl (name : String) (se : ScalarExpr) : LNIRDecl :=
  mkBinScalarDecl name .i64 se

def cmpDecl (name : String) (se : ScalarExpr) : LNIRDecl :=
  mkBinScalarDecl name .i1 se

def hasSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

def run2 (d : LNIRDecl) (x y : Nat) : ExecOutcome :=
  match lowerModule d with
  | some m =>
    match m.fns.head? with
    | some fn => execFn m fn [.bits .i64 (BitVec.ofNat 64 x), .bits .i64 (BitVec.ofNat 64 y)] 8
    | none => .ub "no function"
  | none => .ub "lowering failed"

def isBv (w : BitVec 64) : ExecOutcome → Bool
  | .returned (some (.bits .i64 v)) => v == w
  | _ => false

def isWord (w : Nat) (out : ExecOutcome) : Bool :=
  isBv (BitVec.ofNat 64 w) out

def isUb (msg : String) : ExecOutcome → Bool
  | .ub m => m == msg
  | _ => false

def loweredText (d : LNIRDecl) : String := (ppLoweredDecl d).getD ""

#guard isWord 5 (run2 (binDecl "add2" (.binOp .add (.var 0) (.var 1))) 2 3)
#guard isWord 6 (run2 (binDecl "sub2" (.binOp .sub (.var 0) (.var 1))) 9 3)
#guard isWord 42 (run2 (binDecl "mul2" (.binOp .mul (.var 0) (.var 1))) 6 7)
#guard isWord 4 (run2 (binDecl "div2" (.binOp .div (.var 0) (.var 1))) 20 5)
#guard isWord 2 (run2 (binDecl "mod2" (.binOp .mod (.var 0) (.var 1))) 17 5)
#guard isWord 0 (run2 (binDecl "div0" (.binOp .div (.var 0) (.var 1))) 7 0)
#guard isWord 7 (run2 (binDecl "mod0" (.binOp .mod (.var 0) (.var 1))) 7 0)
#guard isWord 2 (run2 (binDecl "and2" (.binOp .bitAnd (.var 0) (.var 1))) 3 6)
#guard isWord 7 (run2 (binDecl "or2" (.binOp .bitOr (.var 0) (.var 1))) 3 6)
#guard isWord 5 (run2 (binDecl "xor2" (.binOp .bitXor (.var 0) (.var 1))) 3 6)
#guard isWord 16 (run2 (binDecl "shl2" (.binOp .shl (.var 0) (.var 1))) 1 4)
#guard isWord 1 (run2 (binDecl "shl_mask" (.binOp .shl (.var 0) (.var 1))) 1 64)
#guard isWord 2 (run2 (binDecl "shr2" (.binOp .shr (.var 0) (.var 1))) 32 4)
#guard isWord 1 (run2 (cmpDecl "lt_true" (.binOp .lt (.var 0) (.var 1))) 3 9)
#guard isWord 0 (run2 (cmpDecl "lt_false" (.binOp .lt (.var 0) (.var 1))) 9 3)
#guard isWord 1 (run2 (cmpDecl "eq_true" (.binOp .eq (.var 0) (.var 1))) 4 4)
#guard isWord 0 (run2 (cmpDecl "eq_false" (.binOp .eq (.var 0) (.var 1))) 4 5)
#guard isWord 14 (run2 (binDecl "fma2" (.fma (.var 0) (.constU64 3) (.var 1))) 4 2)

def absDiff : LNIRDecl :=
  { name := "abs_diff"
  , params := [p64 0 "a", p64 1 "b"]
  , retTy := .i64
  , body :=
      .letBind 2 .i1 (.scalar (.binOp .lt (.var 0) (.var 1)))
        (.ite 2
          (.letBind 3 .i64 (.scalar (.binOp .sub (.var 1) (.var 0))) (.ret 3))
          (.letBind 4 .i64 (.scalar (.binOp .sub (.var 0) (.var 1))) (.ret 4))) }

#guard isWord 7 (run2 absDiff 3 10)
#guard isWord 6 (run2 absDiff 10 4)

def selectDecl : LNIRDecl :=
  binDecl "sel2" (.select (.binOp .lt (.var 0) (.var 1)) (.constU64 11) (.constU64 22))

#guard isWord 11 (run2 selectDecl 1 2)
#guard isWord 22 (run2 selectDecl 5 2)

def boolParamDecl : LNIRDecl :=
  { name := "bool_param"
  , params := [{ id := 0, name := "b", ty := .i1 }]
  , retTy := .i64
  , body := .letBind 1 .i64 (.scalar (.select (.var 0) (.constU64 9) (.constU64 4))) (.ret 1) }

def runBool (b : Bool) : ExecOutcome :=
  match lowerModule boolParamDecl with
  | some m =>
    match m.fns.head? with
    | some fn => execFn m fn [.bits .i64 (if b then 1#64 else 0#64)] 4
    | none => .ub "no function"
  | none => .ub "lowering failed"

#guard isWord 9 (runBool true)
#guard isWord 4 (runBool false)

def runMutant (fn : LLVMFn) (x y : Nat) : ExecOutcome :=
  runFn2 fn (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) 4

#guard isBv (1#64 - 2#64) (run2 (binDecl "spec_sub" (.binOp .sub (.var 0) (.var 1))) 1 2)
#guard isBv (2#64 - 1#64) (runMutant mutantM1 1 2)
#guard isWord 2 (run2 (binDecl "spec_shl" (.binOp .shl (.var 0) (.var 1))) 1 1)
#guard isWord 0 (runMutant mutantM2 1 1)
#guard isWord 0 (run2 (cmpDecl "spec_ult" (.binOp .lt (.var 0) (.var 1))) 3 3)
#guard isWord 1 (runMutant mutantM3 3 3)
#guard isWord 0 (runMutant specUlt256Fn 5 5)
#guard isWord 1 (runMutant mutantM4 5 5)
#guard isWord 0 (runMutant specUdivGuardFn 7 0)
#guard isUb "division by zero" (runMutant mutantM5 7 0)

def badPtrDecl : LNIRDecl :=
  { name := "bad", params := [{ id := 0, name := "p", ty := .objPtr }], retTy := .i64, body := .ret 0 }

#guard (loweredText absDiff).startsWith "target datalayout = \""
#guard hasSubstr (loweredText absDiff) "define ccc i64 @abs_diff"
#guard hasSubstr (loweredText absDiff) "br i1"
#guard hasSubstr (loweredText absDiff) "phi i64"
#guard hasSubstr (loweredText (binDecl "guarded_div" (.binOp .div (.var 0) (.var 1)))) "udiv"
#guard hasSubstr (loweredText (binDecl "masked_shl" (.binOp .shl (.var 0) (.var 1)))) "and i64"
#guard lowerDecl badPtrDecl == none

end LeanNative.Tests.LLVMLowerTests
