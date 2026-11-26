import Lean
import LeanNative.IR.BridgeHelpers

namespace LeanNative.Tests.BridgeHelpersSplitPin

open Lean

-- Pinned public inventory of `lean/LeanNative/IR/BridgeHelpers/` (S3a split, updated by L1:
-- the second-lowering helper cascade is deleted — see the L1 notes at the head of each
-- helper file and the w-l1 commit messages for the zero-reference evidence).
def expectedPublicDecls : List Name := [
  `LeanNative.IR.hasSimpleGroundDecl,
  `LeanNative.IR.mangleDeclName,
  `LeanNative.IR.mangleDeclNameInEnv,
  `LeanNative.IR.LCNFDeclMetadata,
  `LeanNative.IR.getLCNFDeclMetadata,
  `LeanNative.IR.isSignedScalarTypeExpr,
  `LeanNative.IR.exprUsesSignedScalarType,
  `LeanNative.IR.declUsesSignedScalarTransitively,
  `LeanNative.IR.nullaryEnumScalarType?,
  `LeanNative.IR.isClosureOrRuntimeNatExpr,
  `LeanNative.IR.isSupportedScalarOrFloat,
  `LeanNative.IR.isSupportedParamOrRetType,
  `LeanNative.IR.exprCodomainIsProp,
  `LeanNative.IR.lowerImpureType,
  `LeanNative.IR.tyContainsUSize,
  `LeanNative.IR.instantiateInductExprParams,
  `LeanNative.IR.isStage1DHeapObjectFieldExpr,
  `LeanNative.IR.isStage1DHeapFieldExpr,
  `LeanNative.IR.isSupportedStage1DHeapAdtExpr,
  `LeanNative.IR.declQualifiesForStage1DHeap,
  `LeanNative.IR.validateSupportedTypeM,
  `LeanNative.IR.RcCtorLayoutSpec,
  `LeanNative.IR.getRcCtorLayoutSpecM,
  `LeanNative.IR.checkEnvConstSignatureM,
  `LeanNative.IR.collectEnvExplicitParamTypes,
  `LeanNative.IR.collectDeclExplicitParamTypesM,
  `LeanNative.IR.BridgeState,
  `LeanNative.IR.BridgeM,
  `LeanNative.IR.lowerBridgeType,
  `LeanNative.IR.checkBridgeType,
  `LeanNative.IR.internFVar,
  `LeanNative.IR.freshBridgeVar,
  `LeanNative.IR.getVarType,
  `LeanNative.IR.letValueCallsTarget,
  `LeanNative.IR.codeHasSelfTailCall,
  `LeanNative.IR.declsHaveMutualCycle,
  `LeanNative.IR.collectCodeLocalCallees,
  `LeanNative.IR.substScalarExprVars,
  `LeanNative.IR.eraseBinderNamesAndPrefix,
  `LeanNative.IR.normalizeIntrinsicDecl,
  `LeanNative.IR.canonClmul64Repr,
  `LeanNative.IR.canonClmul64GoRepr,
  `LeanNative.IR.canonClmul64HiRepr,
  `LeanNative.IR.canonClmul64HiGoRepr,
  `LeanNative.IR.canonGf2AffineRepr,
  `LeanNative.IR.canonGf2AffineGoRepr,
  `LeanNative.IR.canonEor3Repr,
  `LeanNative.IR.trustedGfSimdIntrinsicOp,
  `LeanNative.IR.tryLowerGfSimdIntrinsic,
  `LeanNative.IR.isScalarJoinParamType,
  `LeanNative.IR.isTotalScalarExpr,
  `LeanNative.IR.collectScalarCodeRev,
  `LeanNative.IR.collectTupleCodeRev,
  `LeanNative.IR.codeContainsTupleOp,
  `LeanNative.IR.gateCodeWithSymbolicTV,
  `LeanNative.IR.compressScalarCode,
  `LeanNative.IR.isClosedConstHelperName,
  `LeanNative.IR.nameHasCompilerAuxComponent,
  `LeanNative.IR.isCompilerGeneratedAuxDecl,
  `LeanNative.IR.validateIngestedModule,
  `LeanNative.IR.codeHasResidualHeapOrTupleAbiOp,
  `LeanNative.IR.filterNonInternalHelperDecls,
  `LeanNative.IR.collectJmpArgCtors,
  `LeanNative.IR.collectLetCtors,
  `LeanNative.IR.collectFVarCtors,
  `LeanNative.IR.codeAstFuel,
  `LeanNative.IR.collectLetValueFVarsImpure,
  `LeanNative.IR.normalizeEmbeddedSliceGetBangAux,
  `LeanNative.IR.normalizeEmbeddedSliceGetBang,
  `LeanNative.IR.checkImpureLetTypesM,
  `LeanNative.IR.buildRealBridgeCtxM,
  `LeanNative.IR.pureCodeAstFuel,
  `LeanNative.IR.isWordFactTy,
  `LeanNative.IR.isRawPtrFactTy,
  `LeanNative.IR.isExclFactTy,
  `LeanNative.IR.factVarsInScope,
  `LeanNative.IR.collectDeclVarTys,
  `LeanNative.IR.attachBaseDeclFactsM,
  `LeanNative.IR.compressedBodyRetTy,
  `LeanNative.IR.applyValidatedCompression,
  `LeanNative.IR.ingestImpureDeclViaReal,
  `LeanNative.IR.expandCompilerAuxDecls,
  `LeanNative.IR.ingestModuleDeclsWith
]

def expectedPrivateDecls : List Name := [
  `LeanNative.IR.argUsesSigned,
  `LeanNative.IR.codeSignedScan,
  `LeanNative.IR.initialSeenVarsForCode,
  `LeanNative.IR.isBuiltinLNIRRuntimeCall,
  `LeanNative.IR.collectDirectCallees,
  `LeanNative.IR.reachesDeclInCallGraph,
  `LeanNative.IR.collectCodeTypeExprs,
  `LeanNative.IR.collectLetValueCtorAndCalleeNames,
  `LeanNative.IR.collectCodeCtorAndCalleeNames,
  `LeanNative.IR.mkFreshEmbFVarId,
  `LeanNative.IR.collectGetBangIdxUsage,
  `LeanNative.IR.diamondCallGraphRegMod,
  `LeanNative.IR.visitedFuelRegMod
]

def checkBridgeHelpersSplitPin : CoreM Unit := do
  let env ← getEnv
  let missingPublic := expectedPublicDecls.filter fun n => !env.contains n
  if !missingPublic.isEmpty then
    throwError s!"[BridgeHelpersSplitPin] missing public declarations: {missingPublic}"
  let leakedPrivate := expectedPrivateDecls.filter fun n => env.contains n
  if !leakedPrivate.isEmpty then
    throwError s!"[BridgeHelpersSplitPin] private declarations leaked into public environment: {leakedPrivate}"

#eval checkBridgeHelpersSplitPin

end LeanNative.Tests.BridgeHelpersSplitPin
