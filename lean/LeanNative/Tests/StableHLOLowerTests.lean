import LeanNative.Backend.StableHLOLower
import LeanNative.Backend.StableHLOAst

/-!
# `LNIR → StableHLOAst` lowering regressions (`LeanNative.Tests.StableHLOLowerTests`)

Pure `#guard`s exercising `LeanNative.Backend.StableHLOLower` against the independent
`StableHLOAst.evalFuncOp` interpreter and the `StableHLOAst.ppModuleOp` textual emitter:
scalar arithmetic, guarded division, masked shifts, an `ite` diamond, a chained
`sarrayLen → saxpy → dotProduct → sarrayGet` pipeline, and the `H1`..`H3` emitter mutants.
-/

namespace LeanNative.Tests.StableHLOLowerTests

open LeanNative.IR
open LeanNative.Backend.StableHLOAst
open LeanNative.Backend.StableHLOLower

def p64 (id : Nat) (name : String) : LNIRParam := { id := id, name := name, ty := .i64 }

def binDecl (name : String) (se : ScalarExpr) : LNIRDecl :=
  { name := name
  , params := [p64 0 "a", p64 1 "b"]
  , retTy := .i64
  , body := .letBind 2 .i64 (.scalar se) (.ret 2) }

def cmpDecl (name : String) (se : ScalarExpr) : LNIRDecl :=
  { name := name
  , params := [p64 0 "a", p64 1 "b"]
  , retTy := .i1
  , body := .letBind 2 .i1 (.scalar se) (.ret 2) }

def hasSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

def word (n : Nat) : TensorVal := mkScUi64 (BitVec.ofNat 64 n)

def run2 (d : LNIRDecl) (x y : Nat) : Except ShapeError TensorVal :=
  match lowerToStableHLO d 0 with
  | some fn => evalFuncOp fn [word x, word y]
  | none => .error (.shapeMismatch "lowering failed")

def isBv (w : BitVec 64) : Except ShapeError TensorVal → Bool
  | .ok v => v == mkScUi64 w
  | .error _ => false

def isWord (w : Nat) (out : Except ShapeError TensorVal) : Bool :=
  isBv (BitVec.ofNat 64 w) out

def isDivZero : Except ShapeError TensorVal → Bool
  | .error .divisionByZero => true
  | _ => false

def loweredText (d : LNIRDecl) (len : Nat := 0) : String :=
  match lowerModuleToStableHLO "m" [d] len with
  | some m => ppModuleOp m
  | none => ""

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

def absDiff : LNIRDecl :=
  { name := "hlo_abs_diff"
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

def vec (xs : Array UInt64) : TensorVal :=
  { ty := vecUi64Ty xs.size, data := xs.map UInt64.toBitVec }

def pipeline : LNIRDecl :=
  { name := "saxpy_dot"
  , params :=
      [ { id := 0, name := "x", ty := .sarray .i64 }
      , { id := 1, name := "y", ty := .sarray .i64 } ]
  , retTy := .i64
  , body :=
      .letBind 2 .i64 (.sarrayLen 0)
        (.parFor 3 2 [0, 1] .i64 (.saxpy 2)
          (.parFor 4 2 [3, 1] .i64 .dotProduct
            (.letBind 5 .i64 (.scalar (.constU64 0))
              (.letBind 6 .i64 (.sarrayGet 4 5 .i64)
                (.ret 6))))) }

def runPipeline : Except ShapeError TensorVal :=
  match lowerToStableHLO pipeline 3 with
  | some fn => evalFuncOp fn [vec #[1, 2, 3], vec #[4, 5, 6]]
  | none => .error (.shapeMismatch "lowering failed")

#guard isWord 141 runPipeline

def runMutant (fn : FuncOp) (x y : Nat) : Except ShapeError TensorVal :=
  evalFuncOp fn [word x, word y]

#guard isBv (1#64 - 2#64) (run2 (binDecl "spec_sub" (.binOp .sub (.var 0) (.var 1))) 1 2)
#guard isBv (2#64 - 1#64) (runMutant hloMutantSubSwap 1 2)
#guard isWord 1 (run2 (binDecl "spec_shl" (.binOp .shl (.var 0) (.var 1))) 1 64)
#guard isWord 0 (runMutant hloMutantUnmaskedShl 1 64)
#guard isWord 0 (run2 (binDecl "spec_div" (.binOp .div (.var 0) (.var 1))) 7 0)
#guard isDivZero (runMutant hloMutantUnguardedDiv 7 0)

def badPtrDecl : LNIRDecl :=
  { name := "bad", params := [{ id := 0, name := "p", ty := .objPtr }], retTy := .i64, body := .ret 0 }

#guard (loweredText absDiff).startsWith "module @m {"
#guard hasSubstr (loweredText absDiff) "func.func @hlo_abs_diff"
#guard hasSubstr (loweredText absDiff) "stablehlo.select"
#guard hasSubstr (loweredText absDiff) "stablehlo.compare"
#guard hasSubstr (loweredText (binDecl "guarded_div" (.binOp .div (.var 0) (.var 1)))) "stablehlo.divide"
#guard hasSubstr (loweredText (binDecl "masked_shl" (.binOp .shl (.var 0) (.var 1)))) "stablehlo.shift_left"
#guard hasSubstr (loweredText pipeline 3) "stablehlo.dot_general"
#guard hasSubstr (loweredText pipeline 3) "stablehlo.reshape"
#guard lowerToStableHLO badPtrDecl 0 == none

end LeanNative.Tests.StableHLOLowerTests
