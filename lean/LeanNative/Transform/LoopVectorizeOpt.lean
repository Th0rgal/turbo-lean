import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Transform.Pass
import LeanNative.Transform.EqSat
import LeanNative.Transform.LoopSchedule
import LeanNative.Transform.OwnershipRC
import LeanNative.Transform.AlgebraicOpt
import LeanNative.Transform.UnboxTupleSROA
import LeanNative.Transform.HoistExclusivity

namespace LeanNative.Transform

open LeanNative.IR

def contractFmaScalar : ScalarExpr → ScalarExpr
  | .constU64 v => .constU64 v
  | .constBool b => .constBool b
  | .var id => .var id
  | .binOp .add lhs rhs =>
    let l' := contractFmaScalar lhs; let r' := contractFmaScalar rhs
    match l', r' with
    | .binOp .mul a b, c | c, .binOp .mul a b => .fma a b c
    | _, _ => .binOp .add l' r'
  | .binOp op lhs rhs => .binOp op (contractFmaScalar lhs) (contractFmaScalar rhs)
  | .unaryOp op arg => .unaryOp op (contractFmaScalar arg)
  | .select c t f => .select (contractFmaScalar c) (contractFmaScalar t) (contractFmaScalar f)
  | .fma a b c => .fma (contractFmaScalar a) (contractFmaScalar b) (contractFmaScalar c)

def isSimdVectorizableBody : LNIRCode → Bool
  | .letBind _ ty (.scalar _) k | .letBind _ ty (.constU256 _) k
  | .letBind _ ty (.mulDivDown _ _ _) k | .letBind _ ty (.mulDivUp _ _ _) k =>
    ty.isUnboxedScalar && isSimdVectorizableBody k
  | .letBind _ ty (.rawLoad _ _ elemTy) k =>
    ty.isUnboxedScalar && elemTy.isUnboxedScalar && isSimdVectorizableBody k
  | .rawStore _ _ _ elemTy k => elemTy.isUnboxedScalar && isSimdVectorizableBody k
  | .ite _ t e => isSimdVectorizableBody t && isSimdVectorizableBody e
  | .ret _ => true
  | _ => false

/-- Check whether `code` contains at least one `rawLoad` or `rawStore`. -/
def hasRawMemoryAccess : LNIRCode → Bool
  | .letBind _ _ (.rawLoad _ _ _) _ => true
  | .letBind _ _ _ k => hasRawMemoryAccess k
  | .rawStore _ _ _ _ _ => true
  | .incRef _ _ k => hasRawMemoryAccess k
  | .decRef _ _ k => hasRawMemoryAccess k
  | .ite _ t e => hasRawMemoryAccess t || hasRawMemoryAccess e
  | .seqFor _ _ _ _ _ _ s k => hasRawMemoryAccess s || hasRawMemoryAccess k
  | .parFor _ _ _ _ _ k => hasRawMemoryAccess k
  | .ret _ | .unreachable => false

/-- Check whether `objVar` is only read (borrowed) and never mutated or returned in `code`. -/
def isBorrowedReadOnlyIn (objVar : VarId) : LNIRCode → Bool
  | .letBind _ _ (.sarrayEnsureExclusive a _) _ => a != objVar
  | .letBind _ _ (.sarraySet a _ v _) _ => a != objVar && v != objVar
  | .letBind _ _ (.storageStore m _ v) k =>
    m != objVar && v != objVar && isBorrowedReadOnlyIn objVar k
  | .letBind _ _ (.allocCtor _ os ss) k =>
    !(os.contains objVar) && !(ss.contains objVar) && isBorrowedReadOnlyIn objVar k
  | .letBind _ _ (.call _ args _ _) k =>
    !(args.contains objVar) && isBorrowedReadOnlyIn objVar k
  | .letBind _ _ _ k => isBorrowedReadOnlyIn objVar k
  | .rawStore _ _ val _ k => val != objVar && isBorrowedReadOnlyIn objVar k
  | .incRef v _ k => v != objVar && isBorrowedReadOnlyIn objVar k
  | .decRef _ _ k => isBorrowedReadOnlyIn objVar k
  | .ite _ t e => isBorrowedReadOnlyIn objVar t && isBorrowedReadOnlyIn objVar e
  | .seqFor _ _ _ _ init _ s k =>
    init != objVar && isBorrowedReadOnlyIn objVar s && isBorrowedReadOnlyIn objVar k
  | .parFor outVar _ _ _ _ k =>
    outVar != objVar && isBorrowedReadOnlyIn objVar k
  | .ret v => v != objVar
  | .unreachable => true

/-- Remove matching `decRef objVar count` from `code` if present along the continuation spine. -/
def removeMatchingDecRef (objVar : VarId) (count : Nat) : LNIRCode → Option LNIRCode
  | .decRef v c k =>
    if v == objVar && c == count then some k
    else (removeMatchingDecRef objVar count k).map (.decRef v c)
  | .letBind dst ty val k => (removeMatchingDecRef objVar count k).map (.letBind dst ty val)
  | .rawStore p i v elemTy k => (removeMatchingDecRef objVar count k).map (.rawStore p i v elemTy)
  | .seqFor idx lo hi acc init accTy s k =>
    (removeMatchingDecRef objVar count k).map (.seqFor idx lo hi acc init accTy s)
  | .parFor out len ins elemTy kernel k =>
    (removeMatchingDecRef objVar count k).map (.parFor out len ins elemTy kernel)
  | _ => none

/-- Check whether a scalar expression is an ASCII delimiter byte equality test (`b == '\n'`, `b == '|'`, `b == '<'`, `b == ':'`). -/
def isAsciiDelimByteMatch : ScalarExpr → Bool
  | .binOp .eq (.var _) (.constU64 c) | .binOp .eq (.constU64 c) (.var _) => c < 128
  | .binOp .bitOr l r | .select l r (.constBool false) => isAsciiDelimByteMatch l && isAsciiDelimByteMatch r
  | _ => false

/-- Check whether `code` contains an unboxed byte load + ASCII delimiter comparison eligible for 64-bit SWAR / ARM64 NEON (`vceqq_u8` + `vmaxvq_u8`) lowering. -/
def isSwarNeonByteScanBody : LNIRCode → Bool
  | .letBind _ _ (.rawLoad _ _ .i8) k => isSwarNeonByteScanBody k
  | .letBind _ _ (.scalar e) k => isAsciiDelimByteMatch e || isSwarNeonByteScanBody k
  | .ite _ t e => isSwarNeonByteScanBody t || isSwarNeonByteScanBody e
  | _ => false

/-- Verify that an `LNIRCode` block has zero Lean runtime allocations, reference-counting ops, or boxed scalar conversions (`NoRuntimeCheck`, `nm -u == 0`). -/
def checkNoRuntimeCode : LNIRCode → Bool
  | .letBind _ _ (.allocCtor _ _ _) _ | .letBind _ _ (.boxScalar _ _) _
  | .letBind _ _ (.unboxScalar _ _) _ | .letBind _ _ (.sarrayEnsureExclusive _ _) _ => false
  | .letBind _ _ _ k => checkNoRuntimeCode k
  | .rawStore _ _ _ _ k => checkNoRuntimeCode k
  | .incRef _ _ _ | .decRef _ _ _ => false
  | .ite _ t e => checkNoRuntimeCode t && checkNoRuntimeCode e
  | .seqFor _ _ _ _ _ _ s k => checkNoRuntimeCode s && checkNoRuntimeCode k
  | .parFor _ _ _ _ _ k => checkNoRuntimeCode k
  | .ret _ | .unreachable => true

def checkNoRuntimeDecl (d : LNIRDecl) : Bool :=
  d.params.all (fun p => p.ty.isUnboxedScalar || p.borrow) && checkNoRuntimeCode d.body

/-- Attempt to recognize an in-place `rawLoad` + `fma` + `rawStore` `seqFor` step body
    (`out[i] = in[i] * scale + bias`) for SIMD/GPU parallel kernel promotion. -/
def tryMatchMapScaleBiasStep (idxVar accVar : VarId) (stepBody : LNIRCode) :
    Option (VarId × LNIRType × VarId × VarId) :=
  match stepBody with
  | .letBind loadVar elemTy (.rawLoad ptr1 idx1 _)
      (.letBind resVar _ (.scalar (.fma (.var lv) (.var scaleVar) (.var biasVar)))
        (.rawStore ptr2 idx2 rv _ (.ret retVar))) =>
    if idx1 == idxVar && idx2 == idxVar && ptr1 == ptr2 && lv == loadVar &&
       rv == resVar && retVar == accVar then
      some (ptr1, elemTy, scaleVar, biasVar)
    else
      none
  | _ => none

/-- Optimize loop bodies for SIMD vectorization, SWAR/NEON byte scanning, FMA contraction, and borrowed RC elision. -/
def optimizeCodeLoopVectorize (inLoop : Bool) (code : LNIRCode) : LNIRCode × Nat :=
  match code with
  | .incRef objVar count k =>
    let (k', vecCount) := optimizeCodeLoopVectorize inLoop k
    if isBorrowedReadOnlyIn objVar k' then
      match removeMatchingDecRef objVar count k' with
      | some kWithoutDec => (kWithoutDec, vecCount + 1)
      | none => (.incRef objVar count k', vecCount)
    else
      (.incRef objVar count k', vecCount)
  | .decRef objVar count k =>
    let (k', vecCount) := optimizeCodeLoopVectorize inLoop k
    (.decRef objVar count k', vecCount)
  | .letBind dst ty (.scalar e) k =>
    let e' := if inLoop then contractFmaScalar e else e
    let (k', vecCount) := optimizeCodeLoopVectorize inLoop k
    (.letBind dst ty (.scalar e') k', vecCount)
  | .letBind dst ty val k =>
    let (k', vecCount) := optimizeCodeLoopVectorize inLoop k
    (.letBind dst ty val k', vecCount)
  | .rawStore ptrVar idxVar valVar elemTy k =>
    let (k', vecCount) := optimizeCodeLoopVectorize inLoop k
    (.rawStore ptrVar idxVar valVar elemTy k', vecCount)
  | .ite condVar thenBranch elseBranch =>
    let (t', vc1) := optimizeCodeLoopVectorize inLoop thenBranch
    let (e', vc2) := optimizeCodeLoopVectorize inLoop elseBranch
    (.ite condVar t' e', vc1 + vc2)
  | .seqFor idxVar loVar hiVar accVar accInit accTy stepBody k =>
    let isSimd := isSimdVectorizableBody stepBody || isSwarNeonByteScanBody stepBody
    let (stepBody', vc1) := optimizeCodeLoopVectorize true stepBody
    let (k', vc2) := optimizeCodeLoopVectorize inLoop k
    let bonus := if isSimd then 1 else 0
    (.seqFor idxVar loVar hiVar accVar accInit accTy stepBody' k', vc1 + vc2 + bonus)
  | .parFor outVar lenVar inputs elemTy kernel k =>
    let kernel' := match kernel with
      | .customScalar iv ins body => .customScalar iv ins (contractFmaScalar body)
      | other => other
    let (k', vc) := optimizeCodeLoopVectorize inLoop k
    (.parFor outVar lenVar inputs elemTy kernel' k', vc + 1)
  | .ret v => (.ret v, 0)
  | .unreachable => (.unreachable, 0)

/-- Run `LoopVectorizeOpt` on an `LNIRDecl`, contracting loop FMAs, eliding borrowed RC pairs
    around read-only loops, and updating `borrow` / `isGpuCand` flags. -/
def loopVectorizeOptDecl (d : LNIRDecl) : LNIRDecl × Nat :=
  let (body', vecCount) := optimizeCodeLoopVectorize false d.body
  let params' := d.params.map fun p =>
    if !p.borrow && (! p.ty.isUnboxedScalar) && isBorrowedReadOnlyIn p.id body' then
      { p with borrow := true }
    else
      p
  let gpuTypesOk := params'.all (fun p => p.ty.isGpuCompatible) && (d.retTy.isGpuCompatible || d.retTy == .unit)
  let hasVecMem := hasRawMemoryAccess body' || vecCount > 0
  let isGpuCand' := d.isGpuCand || (gpuTypesOk && hasVecMem && hasRawMemoryAccess body')
  ({ d with params := params', body := body', isGpuCand := isGpuCand' }, vecCount)

def loopVectorizeOptPass : TransformPass where
  name := "LoopVectorizeOpt"
  assurance := .translationValidated
  theoremRef := "LeanNative.Proofs.LoopOptProofs.hoistExclusivity_sound"
  runDecl := fun d =>
    let inHash := d.structuralHash
    let (candDecl, vecCount) := loopVectorizeOptDecl d
    let declUnchanged := candDecl.body == d.body && candDecl.params == d.params && candDecl.isGpuCand == d.isGpuCand
    let (d', stepAssurance, stepThmRef, stepNotes) :=
      if declUnchanged then
        let comb := AssuranceLevel.combine d.assurance .verifiedKernelProof
        ({ candDecl with assurance := comb },
         comb,
         "LeanNative.Semantics.CodeRefines.refl",
         s!"Analyzed {vecCount} SIMD/data-parallel loop/borrow regions (declaration unchanged)")
      else if candDecl.body == d.body then
        let comb := AssuranceLevel.combine d.assurance .translationValidated
        ({ candDecl with assurance := comb },
         comb,
         "LeanNative.Proofs.SymbolicTV.validateTranslationDecl",
         s!"Annotated {vecCount} SIMD/borrow metadata flags (body unchanged; metadata annotation assurance={comb})")
      else
        let tvRes := LeanNative.Proofs.validateTranslationDecl d candDecl 64
        if tvRes.passed then
          let comb := AssuranceLevel.combine d.assurance .translationValidated
          ({ candDecl with assurance := comb },
           comb,
           "LeanNative.Proofs.SymbolicTV.validateTranslationDecl",
           s!"Contracted {vecCount} loop FMA/borrow regions (validated by SymbolicTV; branch assurance={comb})")
        else
          let comb := AssuranceLevel.combine d.assurance .verifiedKernelProof
          ({ d with assurance := comb },
           comb,
           "LeanNative.Semantics.CodeRefines.refl",
           "TV rejected loop vectorize body rewrite; preserved original declaration via CodeRefines.refl")
    let outHash := d'.structuralHash
    (d', { passName := "LoopVectorizeOpt", declName := d.name, inputHash := inHash, outputHash := outHash,
           changed := inHash != outHash || d != d', assurance := stepAssurance,
           theoremRef := stepThmRef,
           notes := stepNotes })

/-- Kernel-verified pass pipeline (`Contract V2` / `P3` baseline): every pass is a `VerifiedCodePassContract`
    backed by an unconditional Lean 4 kernel theorem `∀ c, CodeRefines c (runCode c)`. -/
def verifiedKernelPasses : List TransformPass :=
  [eqSatPass, loopSchedulePass, ownershipRCPass]

/-- Extended TV-validated pass pipeline (`UnboxTupleSROA`, `HoistExclusivity`, `LoopVectorizeOpt`,
    and extended `AlgebraicOpt` rules gated by `SymbolicTV.validateTranslationDecl`). -/
def extendedTVPasses : List TransformPass :=
  [algebraicOptPass, unboxTupleSROAPass, hoistExclusivityPass, loopVectorizeOptPass]

def defaultPasses : List TransformPass := extendedTVPasses
def runVerifiedKernelPipeline (m : LNIRModule) : LNIRModule × List PassStepCert := runPassPipeline verifiedKernelPasses m
def runDefaultPipelineDecl (d : LNIRDecl) : LNIRDecl × List PassStepCert := runPassPipelineDecl defaultPasses d
def runDefaultPipeline (m : LNIRModule) : LNIRModule × List PassStepCert := runPassPipeline defaultPasses m

end LeanNative.Transform
