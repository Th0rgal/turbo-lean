import Lean
import LeanNative.IR.BridgeHelpers

namespace LeanNative.Tests.BridgeHelpersSplitPin

open Lean

/-!
Pinned inventory of `lean/LeanNative/IR/BridgeHelpers/` (S3a split; updated by L1 and its
fix rounds; made falsifiable in a later revision).

Why this shape: the r1 pin checked privates with `!env.contains n`, which holds for a
correctly private declaration and equally for a deleted one, and its public check could
not see leftover public declarations. This version derives the ACTUAL inventory from the
environment and compares both directions:

- Public side: every constant declared in the six helper modules whose name is not private
  and not `Name.isInternalDetail` must equal `expectedPublicDecls` AS A SET — a deletion or
  rename fails the "missing" check, a new or leftover declaration fails the "not in the
  pin" check. The set deliberately includes structure machinery (`mk`, projections,
  `casesOn`, derived instances): deleting a `BridgeState` field (the r1 slim) is exactly
  the class of change this pin must notice.
- Private side: each name in `expectedPrivateDecls` must RESOLVE from the modules'
  constants through `privateToUserName?` (existence — a deleted private fails) and must
  not be visible as a public name (the leak check).

Red-first evidence (recorded in this branch's history): a scratch copy of this checker with a planted
deleted name (`compressScalarCode` / `initialSeenVarsForCode`) fails the missing checks,
and a copy with `BridgeM` omitted from the list fails the leftover check, on the same
build that passes the true lists.

Regenerate `expectedPublicDecls` after an intentional inventory change with the same
derivation this file runs: iterate `env.constants`, keep names whose module index is one
of `helperModules`, drop private names and `isInternalDetail` names, sort by `quickCmp`.
-/

def helperModules : List Name := [
  `LeanNative.IR.BridgeHelpers,
  `LeanNative.IR.BridgeHelpers.TypesAndSigs,
  `LeanNative.IR.BridgeHelpers.StateAndIntrinsics,
  `LeanNative.IR.BridgeHelpers.HeapAndConstructors,
  `LeanNative.IR.BridgeHelpers.RealBridgeCtxAndSlices,
  `LeanNative.IR.BridgeHelpers.DeclIngestAndValidation ]

def expectedPublicDecls : List Name := [
  `LeanNative.IR.BridgeM,
  `LeanNative.IR.isSupportedParamOrRetType,
  `LeanNative.IR.BridgeState.selfDeclName,
  `LeanNative.IR.BridgeState.casesOn,
  `LeanNative.IR.lowerImpureType,
  `LeanNative.IR.getLCNFDeclMetadata,
  `LeanNative.IR.instantiateInductExprParams,
  `LeanNative.IR.letValueCallsTarget,
  `LeanNative.IR.nullaryEnumScalarType?,
  `LeanNative.IR.hasSimpleGroundDecl,
  `LeanNative.IR.instInhabitedBridgeState.default,
  `LeanNative.IR.collectJmpArgCtors,
  `LeanNative.IR.codeHasResidualHeapOrTupleAbiOp,
  `LeanNative.IR.isSupportedStage1DHeapAdtExpr.checkCtorFields,
  `LeanNative.IR.declQualifiesForStage1DHeap,
  `LeanNative.IR.instReprLCNFDeclMetadata,
  `LeanNative.IR.isStage1DHeapObjectFieldExpr,
  `LeanNative.IR.BridgeState.nextVarId,
  `LeanNative.IR.ingestImpureDeclViaReal,
  `LeanNative.IR.BridgeState.mk,
  `LeanNative.IR.LCNFDeclMetadata.mk,
  `LeanNative.IR.attachBaseDeclFactsM,
  `LeanNative.IR.BridgeState.ctorIdx,
  `LeanNative.IR.BridgeState.noConfusion,
  `LeanNative.IR.BridgeState.allowStage1DHeap,
  `LeanNative.IR.validateSupportedTypeM,
  `LeanNative.IR.canonClmul64HiRepr,
  `LeanNative.IR.BridgeState.rec,
  `LeanNative.IR.canonEor3Repr,
  `LeanNative.IR.getRcCtorLayoutSpecM,
  `LeanNative.IR.BridgeState.arch,
  `LeanNative.IR.declQualifiesForStage1DHeap.go,
  `LeanNative.IR.collectCodeLocalCallees,
  `LeanNative.IR.freshBridgeVar,
  `LeanNative.IR.instInhabitedLCNFDeclMetadata,
  `LeanNative.IR.instDecidableEqLCNFDeclMetadata,
  `LeanNative.IR.nameHasCompilerAuxComponent,
  `LeanNative.IR.LCNFDeclMetadata.mangledSymbol,
  `LeanNative.IR.collectFVarCtors,
  `LeanNative.IR.tyContainsUSize,
  `LeanNative.IR.declsHaveMutualCycle,
  `LeanNative.IR.mangleDeclName,
  `LeanNative.IR.tryLowerGfSimdIntrinsic,
  `LeanNative.IR.eraseBinderNamesAndPrefix,
  `LeanNative.IR.isCompilerGeneratedAuxDecl,
  `LeanNative.IR.BridgeState.mk.noConfusion,
  `LeanNative.IR.isClosureOrRuntimeNatExpr,
  `LeanNative.IR.LCNFDeclMetadata.isExtern,
  `LeanNative.IR.collectLetValueFVarsImpure,
  `LeanNative.IR.instInhabitedLCNFDeclMetadata.default,
  `LeanNative.IR.canonGf2AffineGoRepr,
  `LeanNative.IR.collectDeclExplicitParamTypesM,
  `LeanNative.IR.checkEnvConstSignatureM,
  `LeanNative.IR.isWordFactTy,
  `LeanNative.IR.BridgeState.mk.inj,
  `LeanNative.IR.substScalarExprVars,
  `LeanNative.IR.buildRealBridgeCtxM,
  `LeanNative.IR.LCNFDeclMetadata.mk.inj,
  `LeanNative.IR.LCNFDeclMetadata.mk.sizeOf_spec,
  `LeanNative.IR.declsHaveMutualCycle.reaches,
  `LeanNative.IR.LCNFDeclMetadata.declName,
  `LeanNative.IR.validateIngestedModule,
  `LeanNative.IR.filterNonInternalHelperDecls,
  `LeanNative.IR.instInhabitedBridgeState,
  `LeanNative.IR.normalizeIntrinsicDecl,
  `LeanNative.IR.normalizeEmbeddedSliceGetBangAux,
  `LeanNative.IR.instDecidableEqLCNFDeclMetadata.decEq,
  `LeanNative.IR.«termCanon_decl_repr%_:_»,
  `LeanNative.IR.lowerBridgeType,
  `LeanNative.IR.BridgeState.noConfusionType,
  `LeanNative.IR.checkEnvConstSignatureM.go,
  `LeanNative.IR.LCNFDeclMetadata.noConfusion,
  `LeanNative.IR.collectDeclVarTys,
  `LeanNative.IR.BridgeState.fvarToVar,
  `LeanNative.IR.codeAstFuel,
  `LeanNative.IR.collectEnvExplicitParamTypes,
  `LeanNative.IR.LCNFDeclMetadata,
  `LeanNative.IR.canonClmul64Repr,
  `LeanNative.IR.checkBridgeType,
  `LeanNative.IR.expandCompilerAuxDecls,
  `LeanNative.IR.LCNFDeclMetadata.recOn,
  `LeanNative.IR.LCNFDeclMetadata.isSimpleGround,
  `LeanNative.IR.lowerImpureType.dropParams,
  `LeanNative.IR.trustedGfSimdIntrinsicOp,
  `LeanNative.IR.instBEqLCNFDeclMetadata.beq,
  `LeanNative.IR.BridgeState.varTypes,
  `LeanNative.IR.ingestModuleDeclsWith,
  `LeanNative.IR.LCNFDeclMetadata.mk.noConfusion,
  `LeanNative.IR.getVarType,
  `LeanNative.IR.canonGf2AffineRepr,
  `LeanNative.IR.exprCodomainIsProp,
  `LeanNative.IR.LCNFDeclMetadata.rec,
  `LeanNative.IR.instBEqLCNFDeclMetadata,
  `LeanNative.IR.RcCtorLayoutSpec,
  `LeanNative.IR.LCNFDeclMetadata.noConfusionType,
  `LeanNative.IR.BridgeState.recOn,
  `LeanNative.IR.LCNFDeclMetadata.casesOn,
  `LeanNative.IR.BridgeState.localDeclNames,
  `LeanNative.IR.factVarsInScope,
  `LeanNative.IR.BridgeState,
  `LeanNative.IR.isClosedConstHelperName,
  `LeanNative.IR.canonClmul64GoRepr,
  `LeanNative.IR.isExclFactTy,
  `LeanNative.IR.lowerImpureType.collectFields,
  `LeanNative.IR.canonClmul64HiGoRepr,
  `LeanNative.IR.checkImpureLetTypesM,
  `LeanNative.IR.isSupportedScalarOrFloat,
  `LeanNative.IR.BridgeState.mk.injEq,
  `LeanNative.IR.exprCodomainIsProp.returnsProp,
  `LeanNative.IR.mangleDeclNameInEnv,
  `LeanNative.IR.codeHasSelfTailCall,
  `LeanNative.IR.isSignedScalarTypeExpr,
  `LeanNative.IR.collectLetCtors,
  `LeanNative.IR.normalizeEmbeddedSliceGetBang,
  `LeanNative.IR.isStage1DHeapFieldExpr,
  `LeanNative.IR.isSupportedStage1DHeapAdtExpr,
  `LeanNative.IR.internFVar,
  `LeanNative.IR.pureCodeAstFuel,
  `LeanNative.IR.exprUsesSignedScalarType,
  `LeanNative.IR.declUsesSignedScalarTransitively,
  `LeanNative.IR.BridgeState.mk.sizeOf_spec,
  `LeanNative.IR.LCNFDeclMetadata.ctorIdx,
  `LeanNative.IR.LCNFDeclMetadata.mk.injEq,
  `LeanNative.IR.collectEnvExplicitParamTypes.go,
  `LeanNative.IR.instReprLCNFDeclMetadata.repr,
  `LeanNative.IR.isRawPtrFactTy
]

def expectedPrivateDecls : List Name := [
  `LeanNative.IR.argUsesSigned,
  `LeanNative.IR.codeSignedScan,
  `LeanNative.IR.isBuiltinLNIRRuntimeCall,
  `LeanNative.IR.collectDirectCallees,
  `LeanNative.IR.reachesDeclInCallGraph,
  `LeanNative.IR.collectArgFVarsImpure,
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
  let some idxs := helperModules.mapM env.getModuleIdx?
    | throwError "[BridgeHelpersSplitPin] a BridgeHelpers module is missing from the environment"
  let mut actualPub : Array Name := #[]
  let mut privUser : Std.HashSet Name := {}
  for (n, _) in env.constants.toList do
    if let some i := env.getModuleIdxFor? n then
      if idxs.contains i then
        match privateToUserName? n with
        | some u => privUser := privUser.insert u
        | none =>
          if !n.isInternalDetail then
            actualPub := actualPub.push n
  let expectedSet : Std.HashSet Name := expectedPublicDecls.foldl (fun s n => s.insert n) {}
  let actualSet : Std.HashSet Name := actualPub.foldl (fun s n => s.insert n) {}
  let missingPublic := expectedPublicDecls.filter (fun n => !actualSet.contains n)
  unless missingPublic.isEmpty do
    throwError s!"[BridgeHelpersSplitPin] pinned public declarations missing from the helper modules (deleted or renamed): {missingPublic}"
  let extraPublic := (actualPub.filter (fun n => !expectedSet.contains n)).qsort
    (fun a b => a.quickCmp b == .lt)
  unless extraPublic.isEmpty do
    throwError s!"[BridgeHelpersSplitPin] helper-module public declarations not in the pin (new or leftover): {extraPublic.toList}"
  let missingPrivate := expectedPrivateDecls.filter (fun n => !privUser.contains n)
  unless missingPrivate.isEmpty do
    throwError s!"[BridgeHelpersSplitPin] pinned private declarations missing (deleted or renamed): {missingPrivate}"
  let leakedPrivate := expectedPrivateDecls.filter (fun n => env.contains n)
  unless leakedPrivate.isEmpty do
    throwError s!"[BridgeHelpersSplitPin] private declarations leaked into the public namespace: {leakedPrivate}"

#eval checkBridgeHelpersSplitPin

end LeanNative.Tests.BridgeHelpersSplitPin
