import Lean.Compiler.LCNF.Basic
import LeanNative.Frontend.ProofRetention
import LeanNative.Proofs.CertChecker
import LeanNative.Semantics.Eval
import LeanNative.Backend.LLVMAst
import LeanNative.Backend.PTXAst
import LeanNative.Backend.MetalAst
import LeanNative.Backend.PTXLower
import LeanNative.Backend.MetalLower
import LeanNative.Backend.MLIRGPU
import LeanNative.Backend.Metal
import LeanNative.Backend.LLVM
import LeanNative.IR.Codec
import LeanNative.IR.Bridge
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
      , { name := "len", ty := .int .i64 } ]
  , blocks := [{ label := "entry", body :=
      [.load "r" false (.int .i64) (.reg "v0") align], term := .ret (some (.int .i64, .reg "r")) }] }

def loadFn3Ptr (align : Nat) : LLVMFn :=
  { name := "ld3", retTy := .int .i64
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

def runBoundsPTX (facts : FactEnv) (fuel lanes nv base outBase : Nat) (words : List (BitVec 64))
    (launch? : Option LaunchBoundsCert := none) :
    Option (List (BitVec 64)) :=
  if !launchOptMatchesLaunch launch? 1 lanes nv then none
  else
    let g := wordMem base outBase words
    match evalPTXKernel fuel (boundsFreePTXKernel facts 0 1 launch?)
        ({ x := 1, y := 1, z := 1 } : LeanNative.Backend.PTXAst.Dim3)
        { x := lanes, y := 1, z := 1 } g
        (ptxParams nv base outBase) with
    | .ok g' =>
      (List.range words.length).mapM fun i => g'.loadBits (outBase + i * 8) 8
    | _ => none

def runBoundsMSL (facts : FactEnv) (fuel lanes nv : Nat) (words : List (BitVec 64))
    (launch? : Option LaunchBoundsCert := none) :
    Option (List (BitVec 64)) :=
  if !launchOptMatchesLaunch launch? 1 lanes nv then none
  else
    let buf := LeanNative.Backend.MetalAst.ByteMemory.ofU64Words words
    let out := LeanNative.Backend.MetalAst.ByteMemory.zeros (words.length * 8)
    let dev := [(0, buf), (1, out)]
    let cst := [(2, LeanNative.Backend.MetalAst.ByteMemory.ofU64Words [BitVec.ofNat 64 nv])]
    match evalMSLKernel fuel (boundsFreeMetalKernel facts 0 1 launch?)
        ({ x := 1, y := 1, z := 1 } : LeanNative.Backend.MetalAst.Dim3)
        { x := lanes, y := 1, z := 1 } dev cst with
    | .ok dev' =>
      match dev'.lookup 1 with
      | some m => (List.range words.length).mapM fun i => m.loadBits (i * 8) 8
      | none => none
    | _ => none

def idxCode : Code .pure :=
  .let (constLet 3 (mkConst ``Bool) ``UInt64.decLt [.fvar (fv 1), .fvar (fv 2)])
    (boolCases (fv 3) [trueRetAlt (fv 1), unreachAlt ``Bool.false])

def idxBranchCode : Code .pure :=
  .let (constLet 3 (mkConst ``Bool) ``UInt64.decLt [.fvar (fv 1), .fvar (fv 2)])
    (boolCases (fv 3) [trueRetAlt (fv 1), falseRetAlt (fv 2)])

def idxFalseOnlyCode : Code .pure :=
  .let (constLet 3 (mkConst ``Bool) ``UInt64.decLt [.fvar (fv 1), .fvar (fv 2)])
    (boolCases (fv 3) [unreachAlt ``Bool.true, falseRetAlt (fv 2)])

def natIdxCode : Code .pure :=
  .let (constLet 3 (mkConst ``Bool) ``Nat.blt [.fvar (fv 1), .fvar (fv 2)])
    (boolCases (fv 3) [trueRetAlt (fv 1), unreachAlt ``Bool.false])

def u64E : Expr := mkConst ``UInt64

def u64ToNatE (n : Nat) : Expr := mkApp (mkConst ``UInt64.toNat) (fve n)

def addTy : Expr := mkApp2 (mkConst ``Nat.lt) (mkApp2 (mkConst ``Nat.add) (u64ToNatE 1) (u64ToNatE 2)) (litE (2 ^ 63))

def mulTy : Expr := mkApp2 (mkConst ``Nat.lt) (mkApp2 (mkConst ``Nat.mul) (u64ToNatE 1) (u64ToNatE 2)) (litE (2 ^ 64))

def subTy : Expr := mkApp2 (mkConst ``UInt64.le) (fve 2) (fve 1)

def alignTy : Expr :=
  mkApp3 (mkConst ``Eq [.succ .zero]) natE (mkApp2 (mkConst ``Nat.mod) (u64ToNatE 1) (litE 8)) (litE 0)

def disjTy : Expr := mkApp4 (mkConst ``SlicesDisjoint) (u64ToNatE 1) (u64ToNatE 3) (u64ToNatE 2) (u64ToNatE 4)

def wrapAddTy : Expr :=
  let haddU64 := mkAppN (mkConst ``HAdd.hAdd [0, 0, 0])
    #[u64E, u64E, u64E, mkConst `instHAddUInt64, fve 1, fve 2]
  mkApp2 (mkConst ``Nat.lt) (mkApp (mkConst ``UInt64.toNat) haddU64) (litE (2 ^ 64))

def propFacts : FactEnv :=
  retainedPureFactsWithParams 16
    [ mkParam 1 u64E, mkParam 2 u64E, mkParam 3 u64E, mkParam 4 u64E
    , mkParam 10 addTy, mkParam 11 mulTy, mkParam 12 subTy
    , mkParam 13 alignTy, mkParam 14 disjTy, mkParam 15 wrapAddTy ]
    (.return (fv 1))

def bareNatFacts : FactEnv :=
  retainedPureFactsWithParams 16
    [ mkParam 1 natE, mkParam 2 natE
    , mkParam 10 (mkApp2 (mkConst ``Nat.le) (fve 2) (fve 1))
    , mkParam 11 (mkApp3 (mkConst ``Eq [.succ .zero]) natE (mkApp2 (mkConst ``Nat.mod) (fve 1) (litE 16)) (litE 0)) ]
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
def loadGepFn : LLVMFn :=
  { name := "ld_gep", retTy := .int .i64
  , params :=
      [ { name := "v3", ty := .ptr 0 }
      , { name := "v4", ty := .ptr 0 }
      , { name := "len", ty := .int .i64 } ]
  , blocks := [{ label := "entry", body :=
      [ .getelementptr "p" true (.int .i64) (.reg "v3") [(.i64, i64v 8)] 0
      , .load "r" false (.int .i64) (.reg "p") 8 ], term := .ret (some (.int .i64, .reg "r")) }] }

def loadDerefV3Fn : LLVMFn :=
  { name := "ld_v3", retTy := .int .i64
  , params :=
      [ { name := "v3", ty := .ptr 0 }
      , { name := "v4", ty := .ptr 0 }
      , { name := "len", ty := .int .i64 } ]
  , blocks := [{ label := "entry", body :=
      [.load "r" false (.int .i64) (.reg "v3") 8], term := .ret (some (.int .i64, .reg "r")) }] }

def ptrEscapeRetFn : LLVMFn :=
  { name := "ret_v3", retTy := .ptr 0
  , params := [ { name := "v3", ty := .ptr 0 }, { name := "v4", ty := .ptr 0 } ]
  , blocks := [{ label := "entry", body := [], term := .ret (some (.ptr 0, .reg "v3")) }] }

def loadIntToPtrFn : LLVMFn :=
  { name := "ld_inttoptr", retTy := .int .i64
  , params :=
      [ { name := "v3", ty := .ptr 0 }
      , { name := "v4", ty := .ptr 0 }
      , { name := "v8", ty := .int .i64 } ]
  , blocks := [{ label := "entry", body :=
      [ .store false (.int .i64) (i64v 7) (.reg "v3") 8
      , .inttoptr "q" .i64 (.reg "v8") 0
      , .load "r" false (.int .i64) (.reg "q") 8 ], term := .ret (some (.int .i64, .reg "r")) }] }

def specFn : LLVMFn :=
  emitVerifiedLLVMFnWithFacts [.disjointSlices 3 4 16 32, .alignedPtr 0 16] 3 4 16 32 1 2 (loadFn 8) 0
def specFnIntToPtr : LLVMFn :=
  emitVerifiedLLVMFnWithFacts [.disjointSlices 3 4 16 32, .idxLt 0 16, .idxLt 0 32] 3 4 16 32 1 2 loadIntToPtrFn 3
def specFnGep : LLVMFn :=
  emitVerifiedLLVMFnWithFacts [.disjointSlices 3 4 16 32, .idxLt 0 16] 3 4 16 32 1 2 loadGepFn 0
def specFnDerefNoPos : LLVMFn :=
  emitVerifiedLLVMFnWithFacts [.disjointSlices 3 4 16 32] 3 4 16 32 1 2 loadDerefV3Fn 0
def specFnDerefPos : LLVMFn :=
  emitVerifiedLLVMFnWithFacts [.disjointSlices 3 4 16 32, .idxLt 0 16] 3 4 16 32 1 2 loadDerefV3Fn 0
def specFnPtrEscape : LLVMFn :=
  emitVerifiedLLVMFnWithFacts [.disjointSlices 3 4 16 32, .idxLt 0 16] 3 4 16 32 1 2 ptrEscapeRetFn 0
def specFnLenMismatch : LLVMFn :=
  emitVerifiedLLVMFnWithFacts [.disjointSlices 3 4 16 32] 3 4 16 64 1 2 (loadFn 8) 0
def specFn3Ptr : LLVMFn :=
  emitVerifiedLLVMFnWithFacts [.disjointSlices 3 4 16 32] 3 4 16 32 1 2 (loadFn3Ptr 8) 0
def specFnSelfDisjoint : LLVMFn :=
  emitVerifiedLLVMFnWithFacts [.disjointSlices 3 3 16 32] 3 3 16 32 1 2 (loadFn 8) 0

def rebindAddSeq : List LLVMInstr :=
  emitVerifiedLLVMWithFacts [.noOverflowAdd 1 2 true true] 1 2
    [ .add "v1" .none .i64 (.reg "v1") (i64v 1)
    , .add "r" .none .i64 (.reg "v1") (.reg "v2") ]
def nonRebindAddSeq : List LLVMInstr :=
  emitVerifiedLLVMWithFacts [.noOverflowAdd 1 2 true true] 1 2
    [ .add "tmp" .none .i64 (.reg "v1") (i64v 1)
    , .add "r" .none .i64 (.reg "v1") (.reg "v2") ]
def rebindPtrLoadSeq : List LLVMInstr :=
  emitVerifiedLLVMWithFacts [.alignedPtr 0 16] 1 2
    [ .inttoptr "v0" .i64 (i64v 3) 0
    , .load "r" false (.int .i64) (.reg "v0") 1 ] 0
def loopMutateFn : LLVMFn :=
  { name := "loop_mut", retTy := .int .i64
  , params := [{ name := "v1", ty := .int .i64 }, { name := "v2", ty := .int .i64 }]
  , blocks :=
      [{ label := "entry"
       , body :=
           [ .add "r" .none .i64 (.reg "v1") (.reg "v2")
           , .add "v1" .none .i64 (.reg "v1") (i64v 1) ]
       , term := .br "entry" }] }

def ptxFacts : FactEnv := [.idxLt 0 1]
def ptxIrrelevantFacts : FactEnv := [.noOverflowAdd 0 1 true true, .alignedPtr 0 16, .idxLt 5 6]
def ptxEmpty : FactEnv := []
def ptxKind : ParallelKernelKind := .zipAdd
def ptxCert : Option LaunchBoundsCert :=
  some { gidVar := 0, lenVar := 1, gridDimX := 1, blockDimX := 2, minLen := 2 }
def ptxWrongCert : Option LaunchBoundsCert :=
  some { gidVar := 9, lenVar := 1, gridDimX := 1, blockDimX := 2, minLen := 2 }
def ptxOverGridCert : Option LaunchBoundsCert :=
  some { gidVar := 0, lenVar := 1, gridDimX := 1, blockDimX := 256, minLen := 1 }
def ptxCert256 : LaunchBoundsCert :=
  { gidVar := 0, lenVar := 1, gridDimX := 1, blockDimX := 256, minLen := 256 }

def customShadowDecl : LNIRDecl :=
  { name := "custom_shadow_add"
    params :=
      [ { id := 0, name := "a", ty := .i64 }
      , { id := 1, name := "b", ty := .i64 }
      , { id := 2, name := "arrA", ty := .sarray .i64 }
      , { id := 3, name := "arrB", ty := .sarray .i64 } ]
    retTy := .sarray .i64
    retainedFacts := [.noOverflowAdd 0 1 true true]
    body :=
      .letBind 4 .i64 (.sarrayLen 2)
        (.parFor 5 4 [2, 3] .i64
          (.customScalar 9 [0, 1] (.binOp .add (.var 0) (.var 1)))
          (.ret 5)) }

def e2eScalarDecl : LNIRDecl :=
  { name := "checked_add_u64"
    params := [{ id := 0, name := "a", ty := .i64 }, { id := 1, name := "b", ty := .i64 }]
    retTy := .i64
    retainedFacts := [.noOverflowAdd 0 1 true true]
    body := .letBind 2 .i64 (.scalar (.binOp .add (.var 0) (.var 1))) (.ret 2) }

def e2eGpuDecl (facts : FactEnv) : LNIRDecl :=
  { name := "zip_add_k"
    params := [{ id := 0, name := "x", ty := .sarray .i64 }, { id := 1, name := "y", ty := .sarray .i64 }]
    retTy := .sarray .i64
    retainedFacts := facts
    body := .letBind 2 .i64 (.sarrayLen 0) (.parFor 3 2 [0, 1] .i64 .zipAdd (.ret 3)) }

def idxParamGpuDecl : LNIRDecl :=
  { name := "idx_param_k"
    params :=
      [ { id := 0, name := "idx", ty := .i64 }
      , { id := 1, name := "n", ty := .i64 }
      , { id := 2, name := "x", ty := .sarray .i64 } ]
    retTy := .sarray .i64
    retainedFacts := [.idxLt 0 1]
    body := .parFor 3 1 [2] .i64 (.mapScaleAdd 2 5) (.ret 3) }

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
#guard hasFact propFacts (.noOverflowMul 0 1 false true)
#guard !hasFact propFacts (.noOverflowMul 0 1 true true)
#guard hasFact propFacts (.noOverflowSub 0 1 false true)
#guard hasFact propFacts (.alignedPtr 0 8)
#guard hasFact propFacts (.disjointSlices 0 1 2 3)
#guard !hasFact propFacts (.noOverflowAdd 0 1 false true)
#guard hasFact exclFacts (.exclusiveObj 1)
#guard idxBranchFacts == []
#guard hasFact idxArmFacts (.idxLt 1 2)
#guard retainedPureFacts 8 idxFalseOnlyCode == []
#guard retainedBranchFacts 8 idxFalseOnlyCode == []
#guard !hasFact (retainedPureFacts 8 idxFalseOnlyCode) (.idxLt 1 2)
#guard !hasFact (retainedBranchFacts 8 idxFalseOnlyCode) (.idxLt 1 2)
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
#guard specFn.params.map (fun p => p.attrs.contains .noalias) == [false, false, false]
#guard specFnIntToPtr.params.map (fun p => p.attrs.contains .noalias) == [false, false, false]
#guard specFnGep.params.map (fun p => p.attrs.contains .noalias) == [false, false, false]
#guard specFnDerefNoPos.params.map (fun p => p.attrs.contains .noalias) == [false, false, false]
#guard specFnDerefPos.params.map (fun p => p.attrs.contains .noalias) == [true, true, false]
#guard specFnPtrEscape.params.map (fun p => p.attrs.contains .noalias) == [false, false]
#guard specFnLenMismatch.params.map (fun p => p.attrs.contains .noalias) == [false, false, false]
#guard specFn3Ptr.params.map (fun p => p.attrs.contains .noalias) == [false, false, false]
#guard specFnSelfDisjoint.params.map (fun p => p.attrs.contains .noalias) == [false, false, false]
#guard (applyRetainedFactsLLVMFn [.disjointSlices 3 4 16 32] (loadFn 8)).params.map
  (fun p => p.attrs.contains .noalias) == [false, false, false]
#guard hasSubstr (PP.ppFn specFnDerefPos) "noalias"
#guard specFn.blocks.head?.map (fun b => b.body.head?) ==
  some (some (.load "r" false (.int .i64) (.reg "v0") 16))
#guard rebindAddSeq ==
  [ .add "v1" .none .i64 (.reg "v1") (i64v 1)
  , .add "r" .none .i64 (.reg "v1") (.reg "v2") ]
#guard nonRebindAddSeq ==
  [ .add "tmp" .none .i64 (.reg "v1") (i64v 1)
  , .add "r" .nswNuw .i64 (.reg "v1") (.reg "v2") ]
#guard rebindPtrLoadSeq ==
  [ .inttoptr "v0" .i64 (i64v 3) 0
  , .load "r" false (.int .i64) (.reg "v0") 1 ]
#guard (applyRetainedFactsLLVMFn [.noOverflowAdd 1 2 true true] loopMutateFn).blocks == loopMutateFn.blocks
#guard (emitVerifiedLLVMFnWithFacts [.noOverflowAdd 1 2 true true] 3 4 16 32 1 2 loopMutateFn).blocks ==
  loopMutateFn.blocks

-- REGRESSION(ptxBoundsFreeParity)
-- Intra-kernel loads drop scalar checks from idxLt; SIMT lane guards additionally require LaunchBoundsCert.
#guard (lowerBoundsFreePTXLoad ptxFacts 0 1 .u64 "%dst" (.regOffset "%addr" 0)).length == 1
#guard (lowerBoundsFreePTXLoad ptxEmpty 0 1 .u64 "%dst" (.regOffset "%addr" 0)).length == 4
#guard hasSubstr (ppPTXKernel (boundsFreePTXKernel ptxFacts 0 1 ptxCert)) "ld.global.u64"
#guard !hasSubstr (ppPTXKernel (boundsFreePTXKernel ptxFacts 0 1 ptxCert)) "setp.ge.u64"
#guard hasSubstr (ppPTXKernel (boundsFreePTXKernel ptxFacts 0 1 none)) "setp.ge.u64"
#guard hasSubstr (ppPTXKernel (boundsFreePTXKernel ptxFacts 0 1 ptxWrongCert)) "setp.ge.u64"
#guard hasSubstr (ppPTXKernel (boundsFreePTXKernel ptxFacts 0 1 ptxOverGridCert)) "setp.ge.u64"
#guard hasSubstr (ppPTXKernel (boundsFreePTXKernel ptxEmpty 0 1 ptxCert)) "setp.ge.u64"
#guard hasSubstr (ppPTXKernel (boundsFreePTXKernel ptxFacts 0 1 ptxCert)) "%ctaid.x"
#guard hasSubstr (ppPTXKernel (boundsFreePTXKernel ptxFacts 0 1 ptxCert)) "%tid.x"
#guard (LeanNative.Backend.PTXLower.lowerKindWithFacts "k" ptxFacts ptxKind 0 1 ptxCert).body.length <
  (LeanNative.Backend.PTXLower.lowerKind "k" ptxKind).body.length
#guard (LeanNative.Backend.PTXLower.lowerKindWithFacts "k" ptxFacts ptxKind 0 1 none).body ==
  (LeanNative.Backend.PTXLower.lowerKind "k" ptxKind).body
#guard (LeanNative.Backend.PTXLower.lowerKindWithFacts "k" ptxIrrelevantFacts ptxKind 0 1 ptxCert).body ==
  (LeanNative.Backend.PTXLower.lowerKind "k" ptxKind).body
#guard runBoundsPTX ptxFacts 64 2 2 16 48 [42#64, 77#64] ptxCert == some [42#64, 77#64]
#guard runBoundsPTX ptxFacts 64 2 1 16 48 [42#64, 77#64] ptxCert == none
#guard runBoundsPTX ptxFacts 64 256 256 16 48 [42#64, 77#64] ptxCert == none
#guard !launchCertMatchesLaunch ptxCert256 1 256 1
#guard !launchCertMatchesLaunch { gidVar := 0, lenVar := 1, gridDimX := 1, blockDimX := 2, minLen := 2 } 1 256 256
#guard launchCertMatchesLaunch ptxCert256 1 256 256
#guard runBoundsPTX ptxFacts 64 2 1 16 48 [42#64, 77#64] none == some [42#64, 0#64]
#guard runBoundsPTX ptxEmpty 64 2 2 16 48 [42#64, 77#64] == some [42#64, 77#64]
#guard runBoundsPTX ptxEmpty 64 2 1 16 48 [42#64, 77#64] == some [42#64, 0#64]
#guard runBoundsPTX ptxEmpty 64 2 0 16 48 [42#64, 77#64] == some [0#64, 0#64]

-- REGRESSION(metalBoundsFreeParity)
-- The Metal bounds-free kernel requires LaunchBoundsCert + idxLt and matches the guarded kernel in range.
#guard (lowerBoundsFreeMetalLoad ptxFacts 0 1 "buf").length == 1
#guard (lowerBoundsFreeMetalLoad ptxEmpty 0 1 "buf").length == 1
#guard hasSubstr (ppMSLKernel (boundsFreeMetalKernel ptxFacts 0 1 ptxCert)) "buf[gid]"
#guard !hasSubstr (ppMSLKernel (boundsFreeMetalKernel ptxFacts 0 1 ptxCert)) "if ("
#guard hasSubstr (ppMSLKernel (boundsFreeMetalKernel ptxFacts 0 1 none)) "if ("
#guard hasSubstr (ppMSLKernel (boundsFreeMetalKernel ptxFacts 0 1 ptxWrongCert)) "if ("
#guard hasSubstr (ppMSLKernel (boundsFreeMetalKernel ptxFacts 0 1 ptxOverGridCert)) "if ("
#guard hasSubstr (ppMSLKernel (boundsFreeMetalKernel ptxEmpty 0 1 ptxCert)) "if ("
#guard hasSubstr (ppMSLKernel (boundsFreeMetalKernel ptxFacts 0 1 ptxCert)) "thread_position_in_grid"
#guard !hasSubstr (ppMSLKernel (LeanNative.Backend.MetalLower.lowerKindWithFacts "k" ptxFacts ptxKind 0 1 ptxCert)) "if ("
#guard hasSubstr (ppMSLKernel (LeanNative.Backend.MetalLower.lowerKindWithFacts "k" ptxFacts ptxKind 0 1 none)) "if ("
#guard hasSubstr (ppMSLKernel (LeanNative.Backend.MetalLower.lowerKindWithFacts "k" ptxIrrelevantFacts ptxKind 0 1 ptxCert)) "if ("
#guard hasSubstr (ppMSLKernel (LeanNative.Backend.MetalLower.lowerKind "k" ptxKind)) "if ("
#guard runBoundsMSL ptxFacts 16 2 2 [99#64, 55#64] ptxCert == some [99#64, 55#64]
#guard runBoundsMSL ptxFacts 16 2 1 [99#64, 55#64] ptxCert == none
#guard runBoundsMSL ptxFacts 16 256 256 [99#64, 55#64] ptxCert == none
#guard runBoundsMSL ptxFacts 16 2 1 [99#64, 55#64] none == some [99#64, 0#64]
#guard runBoundsMSL ptxEmpty 16 2 2 [99#64, 55#64] == some [99#64, 55#64]
#guard runBoundsMSL ptxEmpty 16 2 1 [99#64, 55#64] == some [99#64, 0#64]
#guard runBoundsMSL ptxEmpty 16 2 0 [99#64, 55#64] == some [0#64, 0#64]

#guard LNIRModule.fromWire? ({ moduleName := "m", decls := [e2eScalarDecl] } : LNIRModule).toWire ==
  some { moduleName := "m", decls := [e2eScalarDecl] }
#guard (runVerifiedKernelPipeline { moduleName := "m", decls := [e2eScalarDecl] }).1.decls.map (·.retainedFacts) ==
  [[.noOverflowAdd 0 1 true true]]
#guard match LeanNative.Backend.LLVMLower.ppLoweredDeclWithFacts e2eScalarDecl with
  | some s => hasSubstr s "add nsw nuw i64 %v0, %v1"
  | none => false
#guard hasSubstr (LeanNative.Backend.LLVM.emitLLVMOptimized { moduleName := "m", decls := [e2eScalarDecl] })
  "add nsw nuw i64"
#guard !hasSubstr (LeanNative.Backend.LLVM.emitLLVMOptimized { moduleName := "m", decls := [{ e2eScalarDecl with retainedFacts := [] }] })
  "add nsw nuw i64"
#guard
  let ir := LeanNative.Backend.LLVM.emitDeclLLVM true customShadowDecl .x86_64
  hasSubstr ir "cs_value" && hasSubstr ir "= add i64 %cs_value" &&
    !hasSubstr ir "= add nsw nuw i64" && !hasSubstr ir "nsw i64 %cs_value" &&
    !hasSubstr ir "nuw i64 %cs_value"
#guard !hasSubstr (LeanNative.Backend.LLVM.emitLLVMBaseline { moduleName := "m", decls :=
  [{ name := "disj_fn", params := [{ id := 0, name := "p", ty := .rawPtr .i64 }, { id := 1, name := "q", ty := .rawPtr .i64 },
     { id := 2, name := "la", ty := .i64 }, { id := 3, name := "lb", ty := .i64 }],
     retTy := .i64, retainedFacts := [.disjointSlices 0 1 2 3],
     body := .letBind 4 .i64 (.scalar (.constU64 0)) (.ret 4) }] })
  "ptr noalias %arg_v"
-- Top-level decl kernels MUST keep the SIMT tail-lane guard even when `.idxLt 0 lenVar` is present:
-- `VarId 0` is a decl parameter, never the hardware `gid` (`blockSize = 256` rounds the grid up).
#guard hasSubstr (LeanNative.Backend.MLIRGPU.emitPTXModule { moduleName := "m", decls := [e2eGpuDecl [.idxLt 0 2]] })
  "@%p0 bra $L_done_lean_native_decl_zip_add_k;"
#guard hasSubstr (LeanNative.Backend.MLIRGPU.emitPTXModule { moduleName := "m", decls := [e2eGpuDecl ptxIrrelevantFacts] })
  "@%p0 bra $L_done_lean_native_decl_zip_add_k;"
#guard match LeanNative.Backend.Metal.emitMetalDeclKernel (e2eGpuDecl [.idxLt 0 2]) with
  | some s => hasSubstr s "if ("
  | none => false
#guard match LeanNative.Backend.Metal.emitMetalDeclKernel (e2eGpuDecl ptxIrrelevantFacts) with
  | some s => hasSubstr s "if ("
  | none => false
#guard match LeanNative.Backend.PTXLower.lowerDeclToPTXWithFacts (e2eGpuDecl [.idxLt 0 2]) with
  | some m => hasSubstr (ppPTXModule m) "@%p0 bra $L_done_lean_native_decl_zip_add_k;"
  | none => false
#guard match LeanNative.Backend.MetalLower.lowerDeclToMetalWithFacts (e2eGpuDecl [.idxLt 0 2]) with
  | some m => hasSubstr (ppMSLModule m) "if ("
  | none => false
#guard hasSubstr (LeanNative.Backend.MLIRGPU.emitPTXDeclKernel "k_intra" ptxKind)
  "@%p0 bra $L_done_k_intra;"
#guard hasSubstr (LeanNative.Backend.MLIRGPU.emitPTXModule { moduleName := "m", decls := [idxParamGpuDecl] })
  "@%p0 bra $L_done_lean_native_decl_idx_param_k;"
#guard match ((LeanNative.Backend.Metal.emitMetalModule { moduleName := "m", decls := [idxParamGpuDecl] }).splitOn
    "lean_native_metal_decl_idx_param_k")[1]? with
  | some tail => hasSubstr tail "((ulong)gid) < n"
  | none => false
#guard match LeanNative.Backend.PTXLower.lowerDeclToPTXWithFacts idxParamGpuDecl with
  | some m =>
    hasSubstr (ppPTXModule m) "setp.ge.u64" &&
      hasSubstr (ppPTXModule m) "@%p0 bra $L_done_lean_native_decl_idx_param_k;"
  | none => false
#guard match LeanNative.Backend.MetalLower.lowerDeclToMetalWithFacts idxParamGpuDecl with
  | some m => hasSubstr (ppMSLModule m) "((ulong)gid) < n"
  | none => false

@[noinline] def realCheckedAddU64 (a b : UInt64) (_h : a.toNat + b.toNat < 9223372036854775808) : UInt64 :=
  a + b

@[noinline] def realCheckedMulU64 (a b : UInt64) (_h : a.toNat * b.toNat < 18446744073709551616) : UInt64 :=
  a * b

@[noinline] def realWrappingAddU64 (a b : UInt64) (_h : (a + b).toNat < 18446744073709551616) : UInt64 :=
  a + b

@[noinline] def spoofLeU64 (a b : UInt64)
    (_h : @LE.le UInt64 ⟨fun _ _ => True⟩ b a) : UInt64 :=
  a - b

@[noinline] def spoofLtNat (a b : UInt64)
    (_h : @LT.lt Nat ⟨fun _ _ => True⟩ (a.toNat + b.toNat) 9223372036854775808) : UInt64 :=
  a + b

@[noinline] def spoofHAddNat (a b : UInt64)
    (_h : @HAdd.hAdd Nat Nat Nat ⟨fun _ _ => 0⟩ a.toNat b.toNat < 9223372036854775808) : UInt64 :=
  a + b

@[noinline] def spoofDvdNat (p : UInt64)
    (_h : @Dvd.dvd Nat ⟨fun _ _ => True⟩ 16 p.toNat) : UInt64 :=
  p

@[noinline] def spoofModNat (p : UInt64)
    (_h : @HMod.hMod Nat Nat Nat ⟨fun _ _ => 0⟩ p.toNat 16 = 0) : UInt64 :=
  p

@[noinline] def spoofOfNatBound (a b : UInt64)
    (_h : a.toNat + b.toNat < @OfNat.ofNat Nat 9223372036854775808 ⟨2 ^ 100⟩) : UInt64 :=
  a + b

@[noinline] def realErasedSubU64 {_P : Prop} {_h0 : True} (a b : UInt64)
    (_h : b ≤ a) : UInt64 :=
  a - b

@[noinline] def realAlignedModU64 (p : UInt64) (_h : p % 16 = 0) : UInt64 :=
  p

#guard (retainedPureFacts 8 natIdxCode).isEmpty
#guard bareNatFacts.isEmpty

#guard
  let u64 := Lean.mkConst ``UInt64
  let leBA := Lean.mkApp4 (Lean.mkConst ``LE.le [.zero]) u64 (Lean.mkConst ``instLEUInt64) (.bvar 0) (.bvar 1)
  let sig :=
    Lean.Expr.forallE `α (.sort (Lean.Level.succ .zero))
      (.forallE `a u64
        (.forallE `b u64
          (.forallE `hle leBA u64 .default)
          .default)
        .default)
      .implicit
  hasFact (retainedForallParamFacts [0, 1, 2, 3] 64 sig) (.noOverflowSub 1 2 false true)

def checkRealPipelineEndToEnd : Lean.CoreM Bool := do
  let m ← LeanNative.IR.ingestModuleDecls
    #[``realCheckedAddU64, ``realCheckedMulU64, ``realWrappingAddU64,
      ``spoofLeU64, ``spoofLtNat, ``spoofHAddNat, ``spoofDvdNat, ``spoofModNat,
      ``spoofOfNatBound, ``realErasedSubU64, ``realAlignedModU64] "ProofRetentionE2E" .x86_64 false
  let (optMod, _) := LeanNative.Transform.runDefaultPipeline m
  let some dAdd := optMod.decls.find? (fun d => hasSubstr d.name "realCheckedAddU64") | return false
  let some dMul := optMod.decls.find? (fun d => hasSubstr d.name "realCheckedMulU64") | return false
  let some dWrap := optMod.decls.find? (fun d => hasSubstr d.name "realWrappingAddU64") | return false
  let some dSpoofLe := optMod.decls.find? (fun d => hasSubstr d.name "spoofLeU64") | return false
  let some dSpoofLt := optMod.decls.find? (fun d => hasSubstr d.name "spoofLtNat") | return false
  let some dSpoofAdd := optMod.decls.find? (fun d => hasSubstr d.name "spoofHAddNat") | return false
  let some dSpoofDvd := optMod.decls.find? (fun d => hasSubstr d.name "spoofDvdNat") | return false
  let some dSpoofMod := optMod.decls.find? (fun d => hasSubstr d.name "spoofModNat") | return false
  let some dSpoofOfNat := optMod.decls.find? (fun d => hasSubstr d.name "spoofOfNatBound") | return false
  let some dPolySub := optMod.decls.find? (fun d => hasSubstr d.name "realErasedSubU64") | return false
  let some dAlignMod := optMod.decls.find? (fun d => hasSubstr d.name "realAlignedModU64") | return false
  let wireOk := LNIRModule.fromWire? optMod.toWire == some optMod
  let addIr := LeanNative.Backend.LLVM.emitDeclLLVM true dAdd .x86_64
  let mulIr := LeanNative.Backend.LLVM.emitDeclLLVM true dMul .x86_64
  let wrapIr := LeanNative.Backend.LLVM.emitDeclLLVM true dWrap .x86_64
  let spoofLeIr := LeanNative.Backend.LLVM.emitDeclLLVM true dSpoofLe .x86_64
  let spoofLtIr := LeanNative.Backend.LLVM.emitDeclLLVM true dSpoofLt .x86_64
  let spoofAddIr := LeanNative.Backend.LLVM.emitDeclLLVM true dSpoofAdd .x86_64
  let spoofOfNatIr := LeanNative.Backend.LLVM.emitDeclLLVM true dSpoofOfNat .x86_64
  let polySubIr := LeanNative.Backend.LLVM.emitDeclLLVM true dPolySub .x86_64
  return wireOk &&
    hasFact dAdd.retainedFacts (.noOverflowAdd 0 1 true true) &&
    hasFact dMul.retainedFacts (.noOverflowMul 0 1 false true) &&
    !hasFact dMul.retainedFacts (.noOverflowMul 0 1 true true) &&
    dWrap.retainedFacts.isEmpty &&
    dSpoofLe.retainedFacts.isEmpty &&
    dSpoofLt.retainedFacts.isEmpty &&
    dSpoofAdd.retainedFacts.isEmpty &&
    dSpoofDvd.retainedFacts.isEmpty &&
    dSpoofMod.retainedFacts.isEmpty &&
    dSpoofOfNat.retainedFacts.isEmpty &&
    hasFact dPolySub.retainedFacts (.noOverflowSub 2 3 false true) &&
    hasFact dAlignMod.retainedFacts (.alignedPtr 0 16) &&
    hasSubstr addIr "add nsw nuw i64" &&
    hasSubstr mulIr "mul nuw i64" &&
    !hasSubstr mulIr "mul nsw" &&
    !hasSubstr wrapIr "add nsw" &&
    !hasSubstr wrapIr "add nuw" &&
    !hasSubstr spoofLeIr "sub nuw" &&
    !hasSubstr spoofLeIr "sub nsw" &&
    !hasSubstr spoofLtIr "add nsw" &&
    !hasSubstr spoofLtIr "add nuw" &&
    !hasSubstr spoofAddIr "add nsw" &&
    !hasSubstr spoofAddIr "add nuw" &&
    !hasSubstr spoofOfNatIr "add nsw" &&
    !hasSubstr spoofOfNatIr "add nuw" &&
    hasSubstr polySubIr "sub nuw i64"

/-- info: true -/
#guard_msgs in
#eval checkRealPipelineEndToEnd

end LeanNative.Tests.ProofRetentionTests
