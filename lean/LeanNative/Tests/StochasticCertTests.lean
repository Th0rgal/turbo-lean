import LeanNative.Core

set_option autoImplicit false

namespace LeanNative.Tests.StochasticCertTests

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Transform

def x86Profile : HardwareCostProfile := HardwareCostProfile.forTarget .x86_64
def cudaProfile : HardwareCostProfile := HardwareCostProfile.forTarget .cuda_ptx

def addZeroExpr : ScalarExpr := .binOp .add (.var 0) (.constU64 0)
def addOneMutant : ScalarExpr := .binOp .add (.var 0) (.constU64 1)
def shlWideExpr : ScalarExpr := .binOp .shl (.var 0) (.constU64 64)
def divZeroExpr : ScalarExpr := .binOp .div (.var 0) (.constU64 0)
def mulEightExpr : ScalarExpr := .binOp .mul (.var 0) (.constU64 8)
def shlThreeExpr : ScalarExpr := .binOp .shl (.var 0) (.constU64 3)

#guard certifyScalarPair x86Profile addOneMutant (.var 0) == false
#guard certifyCandidateRule? x86Profile { lhs := addOneMutant, rhs := .var 0 } == none
#guard evalWithStochasticProposer x86Profile (fun _ => some (.var 0)) addOneMutant == addOneMutant

#guard certifyScalarPair x86Profile shlWideExpr (.var 0) == false
#guard certifyScalarPair x86Profile divZeroExpr (.constU64 0) == false
#guard certifyScalarPair x86Profile (.binOp .div (.var 0) (.var 1)) (.var 0) == false

#guard certifyScalarPair x86Profile addZeroExpr (.var 0) == true
#guard certifyScalarPair x86Profile mulEightExpr shlThreeExpr == true
#guard evalWithStochasticProposer x86Profile (fun _ => some shlThreeExpr) mulEightExpr == shlThreeExpr

def evolvedBundle : CertifiedRuleBundle :=
  evolveBundle x86Profile 4 42 [addZeroExpr, mulEightExpr, addOneMutant]

#guard evolvedBundle.certificates.length == 2
#guard CertifiedRuleBundle.fromJson? evolvedBundle.toJson == some evolvedBundle
#guard CertifiedRuleBundle.fromJson? "{}" == none
#guard CertifiedRuleBundle.fromJson? "{\"schema\":\"wrong\"}" == none

def cudaBundle : CertifiedRuleBundle :=
  evolveBundle cudaProfile 3 99 [mulEightExpr]

#guard CertifiedRuleBundle.fromJson? cudaBundle.toJson == some cudaBundle

def extJson : String :=
  "[" ++ ({ lhs := addZeroExpr, rhs := .var 0 : StochasticCandidate }).toJson ++ "," ++
    ({ lhs := addOneMutant, rhs := .var 0 : StochasticCandidate }).toJson ++ "]"

#guard (parseExternalCandidates? extJson).map List.length == some 2
#guard (certifyExternalCandidates? x86Profile extJson).map List.length == some 1

def forgedBundle : CertifiedRuleBundle := {
  profile := x86Profile
  generations := 1
  seed := 7
  certificates := [{
    candidate := { lhs := addOneMutant, rhs := .var 0 }
    costBefore := 1
    costAfter := 0
  }]
}

#guard (certBundleToVerifiedRules forgedBundle).isEmpty

def sampleCode : LNIRCode :=
  .letBind 1 .i64 (.scalar addZeroExpr)
    (.letBind 2 .i64 (.scalar mulEightExpr)
      (.letBind 3 .i64 (.scalar (.binOp .add (.var 1) (.var 2)))
        (.ret 3)))

def optimizedCode : LNIRCode := applyCertifiedBundleCode evolvedBundle sampleCode
def testEnv : VarEnv := VarEnv.empty.bind 0 (.u64 7)

def evalOkEq (res : Except UBError (Val × HeapState)) (v : Val) (st : HeapState) : Bool :=
  match res with
  | .ok (v', st') => v' == v && st' == st
  | .error _ => false

def evalSameOk (a b : Except UBError (Val × HeapState)) : Bool :=
  match a, b with
  | .ok (v1, st1), .ok (v2, st2) => v1 == v2 && st1 == st2
  | _, _ => false

#guard optimizedCode != sampleCode
#guard evalOkEq (evalCode 16 testEnv HeapState.empty sampleCode) (.u64 63) HeapState.empty
#guard evalSameOk (evalCode 16 testEnv HeapState.empty optimizedCode)
  (evalCode 16 testEnv HeapState.empty sampleCode)

def sampleDecl : LNIRDecl := {
  name := "stochastic_sample"
  params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
  retTy := .i64
  assurance := .verifiedKernelProof
  isGpuCand := false
  body := stochasticCertWitnessCode
}

#guard (collectModuleScalarRoots { moduleName := "m", decls := [sampleDecl] }).length == 1
#guard (stochasticCertPass.runDecl sampleDecl).2.changed == true
#guard evalSameOk (evalCode 16 testEnv HeapState.empty (stochasticCertPass.runDecl sampleDecl).1.body)
  (evalCode 16 testEnv HeapState.empty sampleDecl.body)
#guard !(verifiedKernelPasses ++ defaultPasses).any (fun p => p.name == "StochasticCert")
#guard ((mkStochasticCertPass evolvedBundle).runDecl sampleDecl).2.changed
def optInReport :=
  let (_, certs) := runPassPipeline (verifiedKernelPasses ++ [mkStochasticCertPass evolvedBundle])
    { moduleName := "m", decls := [sampleDecl] }
  LeanNative.Proofs.verifyModuleCerts "m" (certs.map LeanNative.Driver.CoreCLI.toOptimizationCert)
#guard optInReport.verified && optInReport.overallAssurance == .verifiedKernelProof

def loopCode : LNIRCode :=
  .letBind 1 .i64 (.scalar (.constU64 0))
    (.letBind 2 .i64 (.scalar (.constU64 4))
      (.seqFor 3 1 2 4 1 .i64
        (.letBind 5 .i64 (.scalar (.binOp .add (.var 4) (.constU64 0))) (.ret 5))
        (.ret 4)))

#guard evalSameOk (evalCode 32 VarEnv.empty HeapState.empty
  (applyStochasticLoopSchedule (proposeLoopSchedule 12345) loopCode))
  (evalCode 32 VarEnv.empty HeapState.empty loopCode)
#guard applyStochasticLoopSchedule { tileSize := 0, unrollFactor := 1 } loopCode == loopCode

end LeanNative.Tests.StochasticCertTests
