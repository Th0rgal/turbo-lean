import Lean.Compiler.LCNF.Basic
import LeanNative.Frontend.ProofRetention
import LeanNative.Proofs.CertChecker
import LeanNative.Semantics.Eval
import LeanNative.Backend.LLVMAst
import LeanNative.Backend.PTXAst
import LeanNative.Backend.MetalAst
import LeanNative.Backend.PTXLower
import LeanNative.Backend.MetalLower
import LeanNative.Transform.LoopVectorizeOpt

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

def unreachAlt (ctor : Name) : Alt .pure :=
  .alt ctor #[] (.unreach (mkConst ``Nat))

def trueRetAlt (ret : FVarId) : Alt .pure :=
  .alt ``Bool.true #[] (.return ret)

def falseRetAlt (ret : FVarId) : Alt .pure :=
  .alt ``Bool.false #[] (.return ret)

def boolCases (discr : FVarId) (alts : List (Alt .pure)) : Code .pure :=
  .cases ⟨``Bool, mkConst ``Nat, discr, alts.toArray⟩

def natE : Expr := mkConst ``Nat

def fve (n : Nat) : Expr := .fvar (fv n)

def litE (n : Nat) : Expr := .lit (.natVal n)

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
  match stepInstr {} 1 { regs := [("v1", i64b 4), ("v2", i64b 5)] } ins with
  | .inr st => st.regs.lookup "r"
  | .inl _ => none

def stepValRegs (regs : List (RegName × LLVMVal)) (ins : LLVMInstr) : Option LLVMVal :=
  match stepInstr {} 1 { regs := regs } ins with
  | .inr st => st.regs.lookup "r"
  | .inl _ => none

def hasSubstr (hay needle : String) : Bool :=
  (hay.splitOn needle).length > 1

def loadFn (align : Nat) : LLVMFn :=
  { name := "ld", retTy := .int .i64
  , params :=
      [ { name := "v3", ty := .ptr 0 }
      , { name := "v4", ty := .ptr 0 }
      , { name := "other", ty := .ptr 0 } ]
  , blocks := [{ label := "entry", body :=
      [.load "r" false (.int .i64) (.reg "v0") align], term := .ret (some (.int .i64, .reg "r")) }] }

def wordMem (base outBase : Nat) (words : List (BitVec 64)) :
    LeanNative.Backend.PTXAst.ByteMemory :=
  let total := Nat.max (base + words.length * 8) (outBase + words.length * 8) + 16
  let m0 := LeanNative.Backend.PTXAst.ByteMemory.zeros total
  (List.range words.length).foldl (fun acc i =>
    let w := words[i]?.getD 0#64
    (acc.storeBits (base + i * 8) 8 w).getD acc) m0

def ptxParams (nv base outBase : Nat) : ParamMemory :=
  { params :=
      [ ("param_len", BitVec.ofNat 64 nv)
      , ("param_addr", BitVec.ofNat 64 base)
      , ("param_out", BitVec.ofNat 64 outBase) ] }

def runBoundsPTX (facts : FactEnv) (fuel lanes nv base outBase : Nat) (words : List (BitVec 64)) :
    Option (List (BitVec 64)) :=
  let g := wordMem base outBase words
  match evalPTXKernel fuel (boundsFreePTXKernel facts 0 1)
      ({ x := 1, y := 1, z := 1 } : LeanNative.Backend.PTXAst.Dim3)
      { x := lanes, y := 1, z := 1 } g
      (ptxParams nv base outBase) with
  | .ok g' =>
    (List.range words.length).mapM fun i => g'.loadBits (outBase + i * 8) 8
  | _ => none

def runBoundsMSL (facts : FactEnv) (fuel lanes nv : Nat) (words : List (BitVec 64)) :
    Option (List (BitVec 64)) :=
  let buf := LeanNative.Backend.MetalAst.ByteMemory.ofU64Words words
  let out := LeanNative.Backend.MetalAst.ByteMemory.zeros (words.length * 8)
  let dev := [(0, buf), (1, out)]
  let cst := [(2, LeanNative.Backend.MetalAst.ByteMemory.ofU64Words [BitVec.ofNat 64 nv])]
  match evalMSLKernel fuel (boundsFreeMetalKernel facts 0 1)
      ({ x := 1, y := 1, z := 1 } : LeanNative.Backend.MetalAst.Dim3)
      { x := lanes, y := 1, z := 1 } dev cst with
  | .ok dev' =>
    match dev'.lookup 1 with
    | some m => (List.range words.length).mapM fun i => m.loadBits (i * 8) 8
    | none => none
  | _ => none

def idxCode : Code .pure :=
  .let (constLet 3 (mkConst ``Bool) ``Nat.blt [.fvar (fv 1), .fvar (fv 2)])
    (boolCases (fv 3) [trueRetAlt (fv 1), unreachAlt ``Bool.false])

def idxBranchCode : Code .pure :=
  .let (constLet 3 (mkConst ``Bool) ``Nat.blt [.fvar (fv 1), .fvar (fv 2)])
    (boolCases (fv 3) [trueRetAlt (fv 1), falseRetAlt (fv 2)])

def addTy : Expr := mkApp2 (mkConst ``Nat.lt) (mkApp2 (mkConst ``Nat.add) (fve 1) (fve 2)) (litE (2 ^ 63))

def mulTy : Expr := mkApp2 (mkConst ``Nat.lt) (mkApp2 (mkConst ``Nat.mul) (fve 1) (fve 2)) (litE (2 ^ 64))

def subTy : Expr := mkApp2 (mkConst ``Nat.le) (fve 2) (fve 1)

def alignTy : Expr :=
  mkApp3 (mkConst ``Eq [.succ .zero]) natE (mkApp2 (mkConst ``Nat.mod) (fve 1) (litE 8)) (litE 0)

def disjTy : Expr := mkApp4 (mkConst ``SlicesDisjoint) (fve 1) (litE 16) (fve 2) (litE 32)

def propFacts : FactEnv :=
  retainedPureFactsWithParams 16
    [ mkParam 1 natE, mkParam 2 natE
    , mkParam 10 addTy, mkParam 11 mulTy, mkParam 12 subTy
    , mkParam 13 alignTy, mkParam 14 disjTy ]
    (.return (fv 1))

def exclCode : Code .pure :=
  .let (constLet 2 (mkConst ``Bool) `lean_is_exclusive [.fvar (fv 1)])
    (boolCases (fv 2) [trueRetAlt (fv 1), unreachAlt ``Bool.false])

def idxFacts : FactEnv := retainedPureFacts 8 idxCode
def idxBranchFacts : FactEnv := retainedPureFacts 8 idxBranchCode
def idxArmFacts : FactEnv := retainedBranchFacts 8 idxBranchCode
def exclFacts : FactEnv := retainedPureFacts 8 exclCode

def dischargedLocal : LNIRCode := dischargeRetainedExclusivity [] localExclChain
def dischargedShadow : LNIRCode := dischargeRetainedExclusivity [] shadowChain
def dischargedStore : LNIRCode :=
  dischargeRetainedExclusivity [] (mutated fun k => .rawStore 0 3 4 .i64 k)
def dischargedInc : LNIRCode :=
  dischargeRetainedExclusivity [] (mutated fun k => .incRef 0 1 k)

def specAdd : LLVMInstr :=
  (emitVerifiedLLVMWithFacts [.noOverflowAdd 1 2 true true] 1 2
    [.add "r" .none .i64 (.reg "v1") (.reg "v2")]).head!
def specAddMismatch : LLVMInstr :=
  (emitVerifiedLLVMWithFacts [.noOverflowAdd 1 2 true true] 1 2
    [.add "r" .none .i64 (.reg "v2") (.reg "v1")]).head!
def specAddConst : LLVMInstr :=
  (emitVerifiedLLVMWithFacts [.noOverflowAdd 1 2 true true] 1 2
    [.add "r" .none .i64 (i64v 4) (i64v 5)]).head!
def specMul : LLVMInstr :=
  (emitVerifiedLLVMWithFacts [.noOverflowMul 1 2 true true] 1 2
    [.mul "r" .none .i64 (.reg "v1") (.reg "v2")]).head!
def specSub : LLVMInstr :=
  (emitVerifiedLLVMWithFacts [.noOverflowSub 1 2 false true] 1 2
    [.sub "r" .none .i64 (.reg "v1") (.reg "v2")]).head!
def specSubIdxLt : LLVMInstr :=
  (emitVerifiedLLVMWithFacts [.idxLt 2 1] 1 2
    [.sub "r" .none .i64 (.reg "v1") (.reg "v2")]).head!
def specLoad : LLVMInstr :=
  attachLoadStoreAlign [.alignedPtr 0 16] 0 (.load "r" false (.int .i64) (.reg "v0") 1)
def specLoadWrongReg : LLVMInstr :=
  attachLoadStoreAlign [.alignedPtr 0 16] 0 (.load "r" false (.int .i64) (.reg "p") 1)
def specStore : LLVMInstr :=
  attachLoadStoreAlign [.alignedPtr 0 16] 0 (.store false (.int .i64) (i64v 1) (.reg "v0") 1)
def specFn : LLVMFn :=
  emitVerifiedLLVMFnWithFacts [.disjointSlices 3 4 16 32, .alignedPtr 0 16] 3 4 16 32 1 2 (loadFn 8) 0
def specFnLenMismatch : LLVMFn :=
  emitVerifiedLLVMFnWithFacts [.disjointSlices 3 4 16 32] 3 4 16 64 1 2 (loadFn 8) 0

def ptxFacts : FactEnv := [.idxLt 0 1]
def ptxEmpty : FactEnv := []
def ptxKind : ParallelKernelKind := .zipAdd

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
#guard hasFact propFacts (.noOverflowAdd 0 1 true true)
#guard hasFact propFacts (.noOverflowMul 0 1 true true)
#guard hasFact propFacts (.noOverflowSub 0 1 false true)
#guard hasFact propFacts (.alignedPtr 0 8)
#guard hasFact propFacts (.disjointSlices 0 1 7 8)
#guard hasFact exclFacts (.exclusiveObj 1)
#guard idxBranchFacts == []
#guard hasFact idxArmFacts (.idxLt 1 2)
#guard !hasFact idxFacts (.idxLt 2 1)
#guard !hasFact propFacts (.noOverflowAdd 0 1 false false)
#guard vidOf exclFacts (.exclusiveObj 1) == some 1

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
#guard verifiedKernelPasses.any (fun p => p.name == "ProofRetention")
#guard passOut.1.body == dischargedLocal
#guard passCert.theoremRef == proofRetentionContract.theoremRef
#guard (verifySingleCert passCert).1
#guard !(verifySingleCert { passCert with theoremRef := "LeanNative.Proofs.missing" }).1

-- REGRESSION(llvmFactSpecialization)
-- Retained facts attach nuw, nsw, align and noalias without changing the value.
#guard specAdd == .add "r" .nswNuw .i64 (.reg "v1") (.reg "v2")
#guard specAddMismatch == .add "r" .none .i64 (.reg "v2") (.reg "v1")
#guard specAddConst == .add "r" .none .i64 (i64v 4) (i64v 5)
#guard specMul == .mul "r" .nswNuw .i64 (.reg "v1") (.reg "v2")
#guard specSub == .sub "r" .nuw .i64 (.reg "v1") (.reg "v2")
#guard specSubIdxLt == .sub "r" .none .i64 (.reg "v1") (.reg "v2")
#guard stepVal specAdd == some (i64b 9)
#guard stepValRegs [("v1", i64b 9223372036854775807), ("v2", i64b 1)] specAdd == some .poison
#guard alignOfFact [.alignedPtr 0 16] 0 (.int .i64) 1 == 16
#guard alignOfFact [.alignedPtr 0 16] 0 (.int .i64) 0 == 16
#guard alignOfFact [.alignedPtr 0 8] 0 (.int .i64) 0 == 0
#guard alignOfFact [.alignedPtr 0 4] 0 (.int .i64) 8 == 8
#guard specLoad == .load "r" false (.int .i64) (.reg "v0") 16
#guard specLoadWrongReg == .load "r" false (.int .i64) (.reg "p") 1
#guard specStore == .store false (.int .i64) (i64v 1) (.reg "v0") 16
#guard hasSubstr (PP.ppInstr specLoad) ", align 16"
#guard specFn.params.map (fun p => p.attrs.contains .noalias) == [true, true, false]
#guard specFnLenMismatch.params.map (fun p => p.attrs.contains .noalias) == [false, false, false]
#guard hasSubstr (PP.ppFn specFn) "noalias"
#guard specFn.blocks.head?.map (fun b => b.body.head?) ==
  some (some (.load "r" false (.int .i64) (.reg "v0") 16))

-- REGRESSION(ptxBoundsFreeParity)
-- A retained idxLt drops the guard and still loads the same in-range word.
#guard (lowerBoundsFreePTXLoad ptxFacts 0 1 .u64 "%dst" (.regOffset "%addr" 0)).length == 1
#guard (lowerBoundsFreePTXLoad ptxEmpty 0 1 .u64 "%dst" (.regOffset "%addr" 0)).length == 4
#guard hasSubstr (ppPTXKernel (boundsFreePTXKernel ptxFacts 0 1)) "ld.global.u64"
#guard !hasSubstr (ppPTXKernel (boundsFreePTXKernel ptxFacts 0 1)) "setp.ge.u64"
#guard hasSubstr (ppPTXKernel (boundsFreePTXKernel ptxFacts 0 1)) "%ctaid.x"
#guard hasSubstr (ppPTXKernel (boundsFreePTXKernel ptxFacts 0 1)) "%tid.x"
#guard (LeanNative.Backend.PTXLower.lowerKindWithFacts "k" ptxFacts ptxKind).body.length <
  (LeanNative.Backend.PTXLower.lowerKind "k" ptxKind).body.length
#guard runBoundsPTX ptxFacts 64 2 2 16 48 [42#64, 77#64] == some [42#64, 77#64]
#guard runBoundsPTX ptxEmpty 64 2 2 16 48 [42#64, 77#64] == some [42#64, 77#64]
#guard runBoundsPTX ptxEmpty 64 2 1 16 48 [42#64, 77#64] == some [42#64, 0#64]
#guard runBoundsPTX ptxEmpty 64 2 0 16 48 [42#64, 77#64] == some [0#64, 0#64]

-- REGRESSION(metalBoundsFreeParity)
-- The Metal bounds-free kernel matches the guarded kernel on an in-range index.
#guard (lowerBoundsFreeMetalLoad ptxFacts 0 1 "buf").length == 1
#guard (lowerBoundsFreeMetalLoad ptxEmpty 0 1 "buf").length == 1
#guard hasSubstr (ppMSLKernel (boundsFreeMetalKernel ptxFacts 0 1)) "buf[gid]"
#guard !hasSubstr (ppMSLKernel (boundsFreeMetalKernel ptxFacts 0 1)) "if ("
#guard hasSubstr (ppMSLKernel (boundsFreeMetalKernel ptxFacts 0 1)) "thread_position_in_grid"
#guard !hasSubstr (ppMSLKernel (LeanNative.Backend.MetalLower.lowerKindWithFacts "k" ptxFacts ptxKind)) "if ("
#guard hasSubstr (ppMSLKernel (LeanNative.Backend.MetalLower.lowerKind "k" ptxKind)) "if ("
#guard runBoundsMSL ptxFacts 16 2 2 [99#64, 55#64] == some [99#64, 55#64]
#guard runBoundsMSL ptxEmpty 16 2 2 [99#64, 55#64] == some [99#64, 55#64]
#guard runBoundsMSL ptxEmpty 16 2 1 [99#64, 55#64] == some [99#64, 0#64]
#guard runBoundsMSL ptxEmpty 16 2 0 [99#64, 55#64] == some [0#64, 0#64]

end LeanNative.Tests.ProofRetentionTests
