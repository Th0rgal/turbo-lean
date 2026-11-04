import Lean.Compiler.LCNF.Basic
import LeanNative.Frontend.ProofRetention
import LeanNative.Proofs.ProofRetentionProofs
import LeanNative.Proofs.CertChecker
import LeanNative.Semantics.Eval
import LeanNative.Backend.LLVMAst
import LeanNative.Backend.PTXAst
import LeanNative.Backend.MetalAst

/-!
# D1 proof-carrying LCNF regressions

`#guard`s for pure-LCNF fact extraction, retained-exclusivity discharge, the
registered proof-retention contract, and LLVM / PTX / Metal specialization.
-/

namespace LeanNative.Tests.ProofRetentionTests

open Lean
open Lean.Compiler.LCNF
open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Frontend.ProofRetention
open LeanNative.Backend.TargetIR
open LeanNative.Backend.LLVMAst
open LeanNative.Backend.PTXAst hiding ByteMemory Dim3
open LeanNative.Backend.MetalAst hiding ByteMemory Dim3
open LeanNative.Proofs
open LeanNative.Transform

def fv (n : Nat) : FVarId := { name := .num `x n }

def mkParam (n : Nat) (ty : Expr) : Param .pure :=
  Param.mk (pu := .pure) (fv n) (.num `p n) ty false

def mkLet (n : Nat) (ty : Expr) (val : LetValue .pure) : LetDecl .pure :=
  LetDecl.mk (pu := .pure) (fv n) (.num `v n) ty val

def constLet (n : Nat) (ty : Expr) (fnName : Name) (args : List (Arg .pure)) : LetDecl .pure :=
  mkLet n ty (LetValue.const (pu := .pure) fnName [] args.toArray)

def pureCode : List (LetDecl .pure) → FVarId → Code .pure
  | [], ret => .return ret
  | d :: ds, ret => .let d (pureCode ds ret)

def hasFact (facts : FactEnv) (f : RetainedFact) : Bool :=
  factMember facts f

def vidOf (facts : FactEnv) (f : RetainedFact) : Option VarId :=
  match facts.find? (· == f) with
  | some (.exclusiveObj v) => some v
  | _ => none

def exSt : HeapState :=
  { buffers := [{ id := 1, exclusive := true, data := #[7, 9] }], nextId := 2 }

def sharedSt : HeapState :=
  { buffers := [{ id := 1, exclusive := false, data := #[7, 9] }], nextId := 2 }

def exEnv : VarEnv := (VarEnv.empty).bind 0 (.sarrayId 1)

def evalOk (fuel : Nat) (env : VarEnv) (st : HeapState) (c : LNIRCode) : Bool :=
  match evalCode fuel env st c with
  | .ok _ => true
  | .error _ => false

def pairEq : Val × HeapState → Val × HeapState → Bool
  | (va, sa), (vb, sb) => va == vb && sa == sb

def evalEq (fuel : Nat) (env : VarEnv) (st : HeapState) (a b : LNIRCode) : Bool :=
  match evalCode fuel env st a, evalCode fuel env st b with
  | .ok pa, .ok pb => pairEq pa pb
  | .error ea, .error eb => ea == eb
  | _, _ => false

def exclChain (objVar dst : VarId) : LNIRCode :=
  .letBind dst .i1 (.isExclusive objVar) (.ret dst)

def ensureChain (objVar dst : VarId) : LNIRCode :=
  .letBind dst (.sarray .i64) (.sarrayEnsureExclusive objVar .i64) (.ret dst)

def localExclChain : LNIRCode :=
  .letBind 1 (.sarray .i64) (.sarrayEnsureExclusive 0 .i64)
    (.letBind 2 .i1 (.isExclusive 1) (.ret 2))

def shadowChain : LNIRCode :=
  .letBind 1 (.sarray .i64) (.sarrayEnsureExclusive 0 .i64)
    (.letBind 1 .i64 (.scalar (.constU64 0))
      (.letBind 2 .i1 (.isExclusive 1) (.ret 2)))

def mutated (kill : LNIRCode → LNIRCode) : LNIRCode :=
  .letBind 1 (.sarray .i64) (.sarrayEnsureExclusive 0 .i64) (kill
    (.letBind 2 .i1 (.isExclusive 1) (.ret 2)))

def i64v (n : Nat) : Operand := .constInt .i64 (BitVec.ofNat 64 n)

def i64b (n : Nat) : LLVMVal := .bits .i64 (BitVec.ofNat 64 n)

def stepVal (ins : LLVMInstr) : Option LLVMVal :=
  match stepInstr {} 1 {} ins with
  | .inr st => st.regs.lookup "r"
  | .inl _ => none

def hasSubstr (hay needle : String) : Bool :=
  (hay.splitOn needle).length > 1

def loadFn (align : Nat) : LLVMFn :=
  { name := "ld", retTy := .int .i64
  , params := [{ name := "p", ty := .ptr 0 }]
  , blocks := [{ label := "entry", body :=
      [.load "r" false (.int .i64) (.reg "p") align], term := .ret (some (.int .i64, .reg "r")) }] }

def wordMem (base outBase : Nat) (word : BitVec 64) :
    Option LeanNative.Backend.PTXAst.ByteMemory :=
  match LeanNative.Backend.PTXAst.ByteMemory.zeros (Nat.max base outBase + 16)
      |>.storeBits base 8 word with
  | some m => some m
  | none => none

def ptxParams (iv nv base outBase : Nat) : ParamMemory :=
  { params :=
      [ ("param_idx", BitVec.ofNat 64 iv), ("param_len", BitVec.ofNat 64 nv)
      , ("param_addr", BitVec.ofNat 64 base), ("param_out", BitVec.ofNat 64 outBase) ] }

def runBoundsPTX (facts : FactEnv) (fuel iv nv base outBase : Nat) (word : BitVec 64) :
    Option (BitVec 64) :=
  match wordMem base outBase word with
  | none => none
  | some g =>
    match evalPTXKernel fuel (boundsFreePTXKernel facts 0 1)
        ({ x := 1, y := 1, z := 1 } : LeanNative.Backend.PTXAst.Dim3)
        { x := 1, y := 1, z := 1 } g
        (ptxParams iv nv base outBase) with
    | .ok g' => g'.loadBits outBase 8
    | _ => none

def runBoundsMSL (facts : FactEnv) (fuel iv nv : Nat) (word : BitVec 64) : Option (BitVec 64) :=
  let buf := LeanNative.Backend.MetalAst.ByteMemory.ofU64Words [word]
  let out := LeanNative.Backend.MetalAst.ByteMemory.zeros 8
  let dev := [(0, buf), (1, out)]
  let cst :=
    [ (2, LeanNative.Backend.MetalAst.ByteMemory.ofU64Words [BitVec.ofNat 64 iv])
    , (3, LeanNative.Backend.MetalAst.ByteMemory.ofU64Words [BitVec.ofNat 64 nv]) ]
  match evalMSLKernel fuel (boundsFreeMetalKernel facts 0 1)
      ({ x := 1, y := 1, z := 1 } : LeanNative.Backend.MetalAst.Dim3)
      { x := 1, y := 1, z := 1 } dev cst with
  | .ok dev' =>
    match dev'.lookup 1 with
    | some m => m.loadBits 0 8
    | none => none
  | _ => none

def idxCode : Code .pure :=
  pureCode [constLet 3 (mkConst ``Bool) ``Nat.blt [.fvar (fv 1), .fvar (fv 2)]] (fv 3)

def addCode : Code .pure :=
  pureCode [constLet 3 (mkConst ``Nat) ``Nat.add [.fvar (fv 1), .fvar (fv 2)]] (fv 3)

def mulCode : Code .pure :=
  pureCode [constLet 3 (mkConst ``Nat) ``Nat.mul [.fvar (fv 1), .fvar (fv 2)]] (fv 3)

def alignCode : Code .pure :=
  pureCode [constLet 2 (mkConst ``Nat) `align8 [.fvar (fv 1)]] (fv 2)

def disjointCode : Code .pure :=
  pureCode [constLet 3 (mkConst ``Bool) `disjoint [.fvar (fv 1), .fvar (fv 2)]] (fv 3)

def exclCode : Code .pure :=
  pureCode [constLet 2 (mkConst ``Bool) `isExclusive [.fvar (fv 1)]] (fv 2)

def idxFacts : FactEnv := retainedPureFacts 8 idxCode
def addFacts : FactEnv := retainedPureFacts 8 addCode
def mulFacts : FactEnv := retainedPureFacts 8 mulCode
def alignFacts : FactEnv := retainedPureFacts 8 alignCode
def disjointFacts : FactEnv := retainedPureFacts 8 disjointCode
def exclFacts : FactEnv := retainedPureFacts 8 exclCode

def dischargedLocal : LNIRCode := dischargeRetainedExclusivity [] localExclChain
def dischargedShadow : LNIRCode := dischargeRetainedExclusivity [] shadowChain
def dischargedStore : LNIRCode :=
  dischargeRetainedExclusivity [] (mutated fun k => .rawStore 0 3 4 .i64 k)
def dischargedInc : LNIRCode :=
  dischargeRetainedExclusivity [] (mutated fun k => .incRef 0 1 k)

def specAdd : LLVMInstr :=
  (emitVerifiedLLVMWithFacts [.noOverflowAdd 1 2 true true] 1 2
    [.add "r" .none .i64 (i64v 4) (i64v 5)]).head!
def specMul : LLVMInstr :=
  (emitVerifiedLLVMWithFacts [.noOverflowMul 1 2 true true] 1 2
    [.mul "r" .none .i64 (i64v 6) (i64v 7)]).head!
def specSub : LLVMInstr :=
  (emitVerifiedLLVMWithFacts [.idxLt 2 1] 1 2
    [.sub "r" .none .i64 (i64v 9) (i64v 3)]).head!
def specLoad : LLVMInstr :=
  attachLoadStoreAlign [.alignedPtr 0 8] 0 (.load "r" false (.int .i64) (.reg "p") 1)
def specStore : LLVMInstr :=
  attachLoadStoreAlign [.alignedPtr 0 8] 0 (.store false (.int .i64) (i64v 1) (.reg "p") 1)
def specFn : LLVMFn :=
  emitVerifiedLLVMFnWithFacts [.disjointSlices 3 4] 3 4 1 2 (loadFn 1) 0

def passOut : LNIRDecl × LeanNative.Transform.PassStepCert :=
  proofRetentionPass.runDecl
    { name := "excl", params := [], retTy := .i1, body := localExclChain }
def passCert : OptimizationCert :=
  { passName := passOut.2.passName, declName := passOut.2.declName
  , inputHash := passOut.2.inputHash, outputHash := passOut.2.outputHash
  , changed := passOut.2.changed, assurance := passOut.2.assurance
  , theoremRef := passOut.2.theoremRef, notes := passOut.2.notes }

-- REGRESSION(pureLcnfFactExtraction)
-- idxLt, overflow, alignment, disjointness and exclusivity survive pure LCNF.
#guard hasFact idxFacts (.idxLt 1 2)
#guard hasFact addFacts (.noOverflowAdd 1 2 true true)
#guard hasFact mulFacts (.noOverflowMul 1 2 true true)
#guard hasFact alignFacts (.alignedPtr 1 8)
#guard hasFact disjointFacts (.disjointSlices 1 2)
#guard hasFact exclFacts (.exclusiveObj 1)
#guard !hasFact idxFacts (.idxLt 2 1)
#guard !hasFact addFacts (.noOverflowAdd 1 2 false false)

-- REGRESSION(retainedExclusivityDischarge)
-- A local ensure-exclusive elides the later check; shadowing and mutation do not.
#guard dischargedLocal ==
  .letBind 1 (.sarray .i64) (.sarrayEnsureExclusive 0 .i64)
    (.letBind 2 .i1 (.scalar (.constBool true)) (.ret 2))
#guard dischargedShadow == shadowChain
#guard dischargedStore == mutated fun k => .rawStore 0 3 4 .i64 k
#guard dischargedInc == mutated fun k => .incRef 0 1 k
#guard evalEq 4 exEnv exSt localExclChain dischargedLocal
#guard evalEq 6 exEnv sharedSt shadowChain dischargedShadow
#guard evalOk 4 exEnv exSt dischargedLocal
#guard !(dischargedStore == dischargedLocal)

-- REGRESSION(registeredProofRetentionContract)
-- The discharge theorem is registered and the emitted pass certificate verifies.
#guard LeanNative.Proofs.isRegisteredTheorem proofRetentionContract.theoremRef
#guard passOut.1.body == dischargedLocal
#guard passCert.theoremRef == proofRetentionContract.theoremRef
#guard (verifySingleCert passCert).1
#guard !(verifySingleCert { passCert with theoremRef := "LeanNative.Proofs.missing" }).1

-- REGRESSION(llvmFactSpecialization)
-- Retained facts attach nuw, nsw, align and noalias without changing the value.
#guard specAdd == .add "r" .nswNuw .i64 (i64v 4) (i64v 5)
#guard specMul == .mul "r" .nswNuw .i64 (i64v 6) (i64v 7)
#guard specSub == .sub "r" .nuw .i64 (i64v 9) (i64v 3)
#guard stepVal specAdd == some (i64b 9)
#guard stepVal (.add "r" .nsw .i64 (i64v 9223372036854775807) (i64v 1)) == some .poison
#guard specLoad == .load "r" false (.int .i64) (.reg "p") 8
#guard specStore == .store false (.int .i64) (i64v 1) (.reg "p") 8
#guard hasSubstr (PP.ppInstr specLoad) ", align 8"
#guard specFn.params.head?.map (·.attrs.contains .noalias) == some true
#guard hasSubstr (PP.ppFn specFn) "noalias"

-- REGRESSION(ptxBoundsFreeParity)
-- A retained idxLt drops the guard and still loads the same in-range word.
#guard (lowerBoundsFreePTXLoad [.idxLt 0 1] 0 1 .u64 "%dst" (.regOffset "%addr" 0)).length == 1
#guard (lowerBoundsFreePTXLoad [] 0 1 .u64 "%dst" (.regOffset "%addr" 0)).length == 4
#guard hasSubstr (ppPTXKernel (boundsFreePTXKernel [.idxLt 0 1] 0 1)) "ld.global.u64"
#guard !hasSubstr (ppPTXKernel (boundsFreePTXKernel [.idxLt 0 1] 0 1)) "setp.ge.u64"
#guard runBoundsPTX [.idxLt 0 1] 9 1 4 16 32 42#64 == some 42#64
#guard runBoundsPTX [] 12 1 4 16 32 42#64 == some 42#64
#guard runBoundsPTX [] 12 5 4 16 32 42#64 == some 0#64

-- REGRESSION(metalBoundsFreeParity)
-- The Metal bounds-free kernel matches the guarded kernel on an in-range index.
#guard (lowerBoundsFreeMetalLoad [.idxLt 0 1] 0 1 "buf").length == 1
#guard (lowerBoundsFreeMetalLoad [] 0 1 "buf").length == 1
#guard hasSubstr (ppMSLKernel (boundsFreeMetalKernel [.idxLt 0 1] 0 1)) "buf[v0]"
#guard !hasSubstr (ppMSLKernel (boundsFreeMetalKernel [.idxLt 0 1] 0 1)) "if ("
#guard runBoundsMSL [.idxLt 0 1] 6 0 2 99#64 == some 99#64
#guard runBoundsMSL [] 7 0 2 99#64 == some 99#64
#guard runBoundsMSL [] 7 3 2 99#64 == some 0#64

end LeanNative.Tests.ProofRetentionTests
