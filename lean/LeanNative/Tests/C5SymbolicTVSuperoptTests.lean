import LeanNative.Core

namespace LeanNative.Tests.C5SymbolicTVSuperoptTests

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Proofs
open LeanNative.Transform

/-- Sample declaration exercising tuple SROA + dead tuple allocation elimination. -/
def sampleTupleSROADecl : LNIRDecl := {
  name := "c5_tuple_sroa"
  params := [{ id := 0, name := "x", ty := .i64, borrow := false },
             { id := 1, name := "y", ty := .i64, borrow := false }]
  retTy := .i64
  assurance := .verifiedKernelProof
  isGpuCand := false
  body :=
    .letBind 10 .i64 (.scalar (.constU64 40))
      (.letBind 11 .i64 (.scalar (.constU64 2))
        (.letBind 2 (.tuple [.i64, .i64]) (.mkTuple [10, 11])
          (.letBind 3 .i64 (.projTuple 2 0)
            (.letBind 4 .i64 (.projTuple 2 1)
              (.letBind 5 .i64 (.scalar (.binOp .add (.var 3) (.var 4)))
                (.ret 5))))))
}

/-- Sample declaration exercising algebraic strength reduction (`x * 8 -> x <<< 3`). -/
def sampleAlgDecl : LNIRDecl := {
  name := "c5_alg_strength"
  params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
  retTy := .i64
  assurance := .verifiedKernelProof
  isGpuCand := false
  body := .letBind 1 .i64 (.scalar (.binOp .mul (.var 0) (.constU64 8))) (.ret 1)
}

/-- Sample declaration exercising FMA loop contraction in `LoopVectorizeOpt`. -/
def sampleLoopVecDecl : LNIRDecl := {
  name := "c5_loop_fma"
  params := [{ id := 0, name := "a", ty := .i64, borrow := false },
             { id := 1, name := "b", ty := .i64, borrow := false },
             { id := 2, name := "c", ty := .i64, borrow := false }]
  retTy := .i64
  assurance := .verifiedKernelProof
  isGpuCand := false
  body :=
    .letBind 3 .i64 (.scalar (.binOp .mul (.var 0) (.var 1)))
      (.letBind 4 .i64 (.scalar (.binOp .add (.var 3) (.var 2)))
        (.ret 4))
}

/-- Adversarial unsound candidate (`x + 1` instead of `x * 8`) MUST be rejected by `symbolicCodeRefines`. -/
def unsoundAlgDecl : LNIRDecl :=
  { sampleAlgDecl with body := .letBind 1 .i64 (.scalar (.binOp .add (.var 0) (.constU64 1))) (.ret 1) }

-- 1. `symbolicCodeRefines` accepts genuine Tuple SROA, AlgebraicOpt, LoopVectorizeOpt, and Superopt rewrites:
#guard symbolicCodeRefines sampleTupleSROADecl.body (unboxTupleSROADecl sampleTupleSROADecl).body == true
#guard (verifiedUnboxTupleSROATVContract.run sampleTupleSROADecl).isSome == true
#guard symbolicCodeRefines sampleAlgDecl.body (optimizeCodeAlgebraic [] sampleAlgDecl.body) == true
#guard (verifiedAlgebraicTVContract.run sampleAlgDecl).isSome == true
#guard symbolicCodeRefines sampleLoopVecDecl.body (loopVectorizeOptDecl sampleLoopVecDecl).1.body == true
#guard (verifiedLoopVectorizeTVContract.run sampleLoopVecDecl).isSome == true
#guard (let (d', _) := superoptDecl .x86_64 sampleAlgDecl
        symbolicCodeRefines sampleAlgDecl.body d'.body == true)

-- 2. `symbolicCodeRefines` and `runSymbolicValidatedDecl` reject unsound candidates:
#guard symbolicCodeRefines sampleAlgDecl.body unsoundAlgDecl.body == false
#guard (runSymbolicValidatedDecl (fun _ => unsoundAlgDecl) sampleAlgDecl).isNone == true

-- 3. `CertChecker` registers all new C5 `SymbolicTV` & `Superopt` kernel soundness theorems:
#guard isRegisteredTheorem "LeanNative.Proofs.SymbolicTVCodeSoundness.symExecCode_pureU64_denotes" == true
#guard isRegisteredTheorem "LeanNative.Proofs.SymbolicTVCodeSoundness.symExecCode_pureU64_eval_eq" == true
#guard isRegisteredTheorem "LeanNative.Proofs.SymbolicTVRefinesSoundness.symbolicCodeRefines_sound" == true
#guard isRegisteredTheorem "LeanNative.Proofs.SymbolicTVRefinesSoundness.symbolicValidatedDeclOpt_sound" == true
#guard isRegisteredTheorem "LeanNative.Proofs.SuperoptSoundness.superoptDecl_sound" == true
#guard isRegisteredTheorem "LeanNative.Proofs.SuperoptSoundness.superoptModule_sound" == true

end LeanNative.Tests.C5SymbolicTVSuperoptTests
