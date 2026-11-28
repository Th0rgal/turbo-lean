import LeanNative.Proofs.H1.SpecLocked

/-!
# W2-L1: the locked H1 statement on a concrete `let` (`LowerSound.lean`)

`SpecLocked.lean` (hash-pinned by H1.F) keeps its witnesses `let`-free because the lowered type of a
`let` was decided by the `opaque` `Lean.Expr.eqv`. Type comparisons now go through the structural
`RealLCNFBridge.exprStructEq`, so a `let`-binding lowers, evaluates, and is refuted by `rfl`.

`letWitness` is a second non-vacuity witness for `specLocked` (a `let` whose right-hand side is a
canonical scalar call); `negWitnessSwappedArith` is a fifth lowerer mutant, killed on it.
-/

namespace LeanNative.Proofs.H1

open Lean Lean.Compiler.LCNF
open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

/-! ## Witness declaration: `h1l_sub (x y : UInt64) := let z := x - y; z` -/

def subLet : LetDecl .impure :=
  { fvarId := fv 3, binderName := .num `v 3, type := ImpureType.uint64
    value := .fap ``UInt64.sub #[.fvar (fv 1), .fvar (fv 2)] rfl }

def subDecl : Decl .impure :=
  { name := `h1l_sub, levelParams := [], type := ImpureType.uint64, inlineAttr? := none
    params := #[mkParam 1 ImpureType.uint64, mkParam 2 ImpureType.uint64]
    value := .code (.let subLet (.return (fv 3))) }

def subCtx : RealBridgeCtx := { paramTypeMap := [(fv 1, .i64), (fv 2, .i64)] }

def subFuel : Nat := 8

def subArgs : List Val := [.u64 9, .u64 5]

/-- The `let` type `ImpureType.uint64` lowers to `.i64` in the kernel. -/
theorem sub_lowered_body :
    (lowerRealLCNFDecl subFuel subCtx subDecl "h1l_sub").map LNIRDecl.body =
      .ok (.letBind 2 .i64 (.scalar (.binOp .sub (.var 0) (.var 1))) (.ret 2)) := rfl

theorem sub_src :
    evalRealLCNFDecl subFuel subCtx subDecl subArgs HeapState.empty = .ok (.u64 4, HeapState.empty) := rfl

/-- Non-vacuity on a `let`: the real lowerer accepts `subDecl`, the source run succeeds, and the
    locked conclusion is the concrete value `9 - 5 = 4`. -/
theorem letWitness :
    ∃ d, lowerRealLCNFDecl subFuel subCtx subDecl "h1l_sub" = .ok d ∧
      evalRealLCNFDecl subFuel subCtx subDecl subArgs HeapState.empty = .ok (.u64 4, HeapState.empty) ∧
      evalLNIRDecl subFuel d subArgs HeapState.empty = .ok (.u64 4, HeapState.empty) :=
  ⟨_, rfl, sub_src, specLocked _ _ _ _ _ _ _ _ _ rfl sub_src⟩

/-! ## Mutant 5 (swapped arithmetic): every scalar `binOp` takes its operands in reverse order -/

def swapScalar : ScalarExpr → ScalarExpr
  | .binOp op a b => .binOp op (swapScalar b) (swapScalar a)
  | .unaryOp op a => .unaryOp op (swapScalar a)
  | .select c t e => .select (swapScalar c) (swapScalar t) (swapScalar e)
  | .fma a b c => .fma (swapScalar a) (swapScalar b) (swapScalar c)
  | e => e

def swapArith : LNIRCode → LNIRCode
  | .letBind x ty (.scalar e) k => .letBind x ty (.scalar (swapScalar e)) (swapArith k)
  | .letBind x ty e k => .letBind x ty e (swapArith k)
  | .rawStore p i v ty k => .rawStore p i v ty (swapArith k)
  | .incRef x n k => .incRef x n (swapArith k)
  | .decRef x n k => .decRef x n (swapArith k)
  | .ite c t e => .ite c (swapArith t) (swapArith e)
  | .seqFor i lo hi a ai ty s k => .seqFor i lo hi a ai ty (swapArith s) (swapArith k)
  | .parFor o n xs ty kk k => .parFor o n xs ty kk (swapArith k)
  | c => c

def negWitnessSwappedArith : LNIRDecl → LNIRDecl := fun d => { d with body := swapArith d.body }

/-- The mutant computes `5 - 9` (wrapping) where the source computes `9 - 5`. -/
theorem swappedArith_run : ∀ d, lowerRealLCNFDecl subFuel subCtx subDecl "h1l_sub" = .ok d →
    evalLNIRDecl subFuel (negWitnessSwappedArith d) subArgs HeapState.empty =
      .ok (.u64 (5 - 9), HeapState.empty) :=
  fun _ h => by cases h; rfl

theorem negWitnessSwappedArith_killed : ¬ H1ForwardSim (mutate negWitnessSwappedArith) := fun h =>
  absurd ((swappedArith_run _ rfl).symm.trans (h _ _ _ _ _ _ _ _ _ rfl sub_src)) (by simp)

end LeanNative.Proofs.H1
