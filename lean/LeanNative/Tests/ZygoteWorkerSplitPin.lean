import Lean
import TurboLean.ZygoteWorker

namespace LeanNative.Tests.ZygoteWorkerSplitPin

open Lean

def expectedPublicDecls : List Name := [
  `TurboLean.ZygoteWorker.replayKernelConstants,
  `TurboLean.ZygoteWorker.checkKernelDecl,
  `TurboLean.ZygoteWorker.publicImportArtifacts,
  `TurboLean.ZygoteWorker.monoTypeModuleEntries,
  `TurboLean.ZygoteWorker.hasMonoTypeModuleEntries,
  `TurboLean.ZygoteWorker.originatingMessage?,
  `TurboLean.ZygoteWorker.hexDigitVal,
  `TurboLean.ZygoteWorker.decodeHexToString,
  `TurboLean.ZygoteWorker.encodeStringToHex,
  `TurboLean.ZygoteWorker.encodeHexList,
  `TurboLean.ZygoteWorker.decodeHexList,
  `TurboLean.ZygoteWorker.encodeHexPairs,
  `TurboLean.ZygoteWorker.decodeHexPairs,
  `TurboLean.ZygoteWorker.parseModuleName,
  `TurboLean.ZygoteWorker.parseImportsCsvSpec,
  `TurboLean.ZygoteWorker.parseImportsCsv,
  `TurboLean.ZygoteWorker.coalesceImportsCsv,
  `TurboLean.ZygoteWorker.deriveEvalMainModule,
  `TurboLean.ZygoteWorker.jsonEscape,
  `TurboLean.ZygoteWorker.jsonStrList,
  `TurboLean.ZygoteWorker.jsonKvObj,
  `TurboLean.ZygoteWorker.stderrReplyMark,
  `TurboLean.ZygoteWorker.emitZygoteReply,
  `TurboLean.ZygoteWorker.satSolverRef,
  `TurboLean.ZygoteWorker.withToolchainSatSolver,
  `TurboLean.ZygoteWorker.isAllowedLeanOption,
  `TurboLean.ZygoteWorker.stripWeakPrefixes,
  `TurboLean.ZygoteWorker.applyEncodedLeanArgs,
  `TurboLean.ZygoteWorker.runtimePanicErr,
  `TurboLean.ZygoteWorker.isRuntimePanicText,
  `TurboLean.ZygoteWorker.isAllowedStandardAxiom,
  `TurboLean.ZygoteWorker.globMatch,
  `TurboLean.ZygoteWorker.isAllowedAxiom,
  `TurboLean.ZygoteWorker.exprEqModLetNondep,
  `TurboLean.ZygoteWorker.isExplicitSorryBody,
  `TurboLean.ZygoteWorker.isExplicitSorryStub,
  `TurboLean.ZygoteWorker.canonicalComponent,
  `TurboLean.ZygoteWorker.canonicalName,
  `TurboLean.ZygoteWorker.collectDeclAxioms,
  `TurboLean.ZygoteWorker.hydrateOnePersistentExt,
  `TurboLean.ZygoteWorker.hydrateMetaAuditEnv,
  `TurboLean.ZygoteWorker.hydrateRecAuditEnv,
  `TurboLean.ZygoteWorker.isCoreRecCombinator,
  `TurboLean.ZygoteWorker.checkRecAuditThmDecl,
  `TurboLean.ZygoteWorker.checkRecAuditDefEqKernel,
  `TurboLean.ZygoteWorker.unfoldCliqueAuxThms,
  `TurboLean.ZygoteWorker.reconstructStructuralClique,
  `TurboLean.ZygoteWorker.checkStructuralClique,
  `TurboLean.ZygoteWorker.auditIsForallMotive,
  `TurboLean.ZygoteWorker.auditSplitMatchOrCasesOn,
  `TurboLean.ZygoteWorker.existingAuditMatchArgPusher?,
  `TurboLean.ZygoteWorker.mkAuditMatchArgPusher,
  `TurboLean.ZygoteWorker.auditPushMatcherArgProc,
  `TurboLean.ZygoteWorker.declMatchesAuditScope,
  `TurboLean.ZygoteWorker.checkWFClique,
  `TurboLean.ZygoteWorker.checkPFClique,
  `TurboLean.ZygoteWorker.checkRecursionCliqueMeta,
  `TurboLean.ZygoteWorker.isCompilerPartialRecDefn,
  `TurboLean.ZygoteWorker.hostNameComponents,
  `TurboLean.ZygoteWorker.userNameComponents,
  `TurboLean.ZygoteWorker.parseHostTarget,
  `TurboLean.ZygoteWorker.parseExactRootName,
  `TurboLean.ZygoteWorker.hasFastVerifyComp,
  `TurboLean.ZygoteWorker.kernelThmTypesAlphaEq,
  `TurboLean.ZygoteWorker.parseFastVerifyMapEntries,
  `TurboLean.ZygoteWorker.validateFastVerifyKernelMap,
  `TurboLean.ZygoteWorker.nameMatchesHostTargetPrefix,
  `TurboLean.ZygoteWorker.nameMatchesHostTargetExact,
  `TurboLean.ZygoteWorker.ownedByTarget,
  `TurboLean.ZygoteWorker.stubNameHits,
  `TurboLean.ZygoteWorker.resolveStubNames,
  `TurboLean.ZygoteWorker.stubExemptSet,
  `TurboLean.ZygoteWorker.unexemptPrefixStub,
  `TurboLean.ZygoteWorker.declaresHostName,
  `TurboLean.ZygoteWorker.kernelPolicyHint,
  `TurboLean.ZygoteWorker.auditNewKernelDecls,
  `TurboLean.ZygoteWorker.countExprDagNodes,
  `TurboLean.ZygoteWorker.stripForallConcl,
  `TurboLean.ZygoteWorker.extractNewDeclGoalHead,
  `TurboLean.ZygoteWorker.countNewDeclExprNodes,
  `TurboLean.ZygoteWorker.collectNewDeclUsedConstants,
  `TurboLean.ZygoteWorker.eqConstantInfo,
  `TurboLean.ZygoteWorker.kernelReplayNewDecls,
  `TurboLean.ZygoteWorker.hashBytesBlake3Hex,
  `TurboLean.ZygoteWorker.kernelStatementHash,
  `TurboLean.ZygoteWorker.collectNewTheoremTypeHashes,
  `TurboLean.ZygoteWorker.runCommandsFromState,
  `TurboLean.ZygoteWorker.writeAuditedModuleOlean,
  `TurboLean.ZygoteWorker.writeVerifiedModuleOlean,
  `TurboLean.ZygoteWorker.writeVerifiedOutlineOlean,
  `TurboLean.ZygoteWorker.environmentOnlyPrefix,
  `TurboLean.ZygoteWorker.compactPrefix?,
  `TurboLean.ZygoteWorker.checkShardWithEnv,
  `TurboLean.ZygoteWorker.serializeForkCandResult,
  `TurboLean.ZygoteWorker.deserializeForkCandResult,
  `TurboLean.ZygoteWorker.checkShardWithEnvForked,
  `TurboLean.ZygoteWorker.runBatchFissionSubs,
  `TurboLean.ZygoteWorker.runRaceCandidatesSubsSequential,
  `TurboLean.ZygoteWorker.runRaceCandidatesSubs,
  `TurboLean.ZygoteWorker.isWhitelistedInitExecUnsafe,
  `TurboLean.ZygoteWorker.isWhitelistedInitExecBridge,
  `TurboLean.ZygoteWorker.collectForbiddenAxiomsByDecl,
  `TurboLean.ZygoteWorker.nestedContainerAllowlist,
  `TurboLean.ZygoteWorker.nestedOccurrencesAllowed,
  `TurboLean.ZygoteWorker.nestedInductiveAllowed,
  `TurboLean.ZygoteWorker.isKernelConstantReachable,
  `TurboLean.ZygoteWorker.csimpCandidatePair?,
  `TurboLean.ZygoteWorker.csimpReplacementPair?,
  `TurboLean.ZygoteWorker.compilerAuditCodeViolations,
  `TurboLean.ZygoteWorker.hydrateCompilerAuditEnv,
  `TurboLean.ZygoteWorker.compilerAuditEligible,
  `TurboLean.ZygoteWorker.runPureLcnfPass,
  `TurboLean.ZygoteWorker.compileSingleBaseLcnfDecl,
  `TurboLean.ZygoteWorker.compileSingleToLcnfDecl,
  `TurboLean.ZygoteWorker.lcnfDeclAlphaEqv,
  `TurboLean.ZygoteWorker.isSpecGeneratedConstPair,
  `TurboLean.ZygoteWorker.lcnfPureAlphaEqvModuloSpec,
  `TurboLean.ZygoteWorker.lcnfDeclAlphaEqvModuloSpec,
  `TurboLean.ZygoteWorker.isOpaqueBaseStub,
  `TurboLean.ZygoteWorker.collectModuleStoredBaseDecls,
  `TurboLean.ZygoteWorker.collectLcnfPureConsts,
  `TurboLean.ZygoteWorker.collectIrFnBodyCalls,
  `TurboLean.ZygoteWorker.collectCompiledCodeConsts,
  `TurboLean.ZygoteWorker.safeUnsafeCallWrapperParent?,
  `TurboLean.ZygoteWorker.safeUnsafeCallWrapperBridgeParent?,
  `TurboLean.ZygoteWorker.isPinnedFfiOpaque,
  `TurboLean.ZygoteWorker.collectStubDecls,
  `TurboLean.ZygoteWorker.readAuditedModulePartsAt,
  `TurboLean.ZygoteWorker.readAuditedModuleParts,
  `TurboLean.ZygoteWorker.dupTheoremMatch,
  `TurboLean.ZygoteWorker.verifyProofIrrelevantOleanUpdate,
  `TurboLean.ZygoteWorker.replayAuditedModule,
  `TurboLean.ZygoteWorker.replayAuditedModuleClosure,
  `TurboLean.ZygoteWorker.auditImportedModulesInEnv,
  `TurboLean.ZygoteWorker.auditShardModule,
  `TurboLean.ZygoteWorker.auditModuleSlice,
  `TurboLean.ZygoteWorker.auditCompiledModules,
  `TurboLean.ZygoteWorker.dumpPublicSignatureJson,
  `TurboLean.ZygoteWorker.TimeoutHotspotEntry,
  `TurboLean.ZygoteWorker.SimpHotspotEntry,
  `TurboLean.ZygoteWorker.diagnoseShardHotspots,
  `TurboLean.ZygoteWorker.instMonadEnvReaderTEnvironmentId_turboLean,
  `main
]

def expectedPrivateDecls : List Name := [
  `TurboLean.ZygoteWorker.formatReducibilityStatus,
  `TurboLean.ZygoteWorker.formatInlineAttr,
  `TurboLean.ZygoteWorker.formatHintsStr,
  `TurboLean.ZygoteWorker.formatQuotStr,
  `TurboLean.ZygoteWorker.formatConstantExportPayload,
  `TurboLean.ZygoteWorker.formatAttrKind,
  `TurboLean.ZygoteWorker.formatDiscrKey,
  `TurboLean.ZygoteWorker.formatInstanceEntry,
  `TurboLean.ZygoteWorker.formatSimpEntry,
  `TurboLean.ZygoteWorker.formatExternEntry,
  `TurboLean.ZygoteWorker.formatConstKind,
  `TurboLean.ZygoteWorker.formatCoeFnType,
  `TurboLean.ZygoteWorker.formatHeadIndex,
  `TurboLean.ZygoteWorker.formatGrindEntry,
  `TurboLean.ZygoteWorker.formatLcnfSignature,
  `TurboLean.ZygoteWorker.formatLcnfDeclIO,
  `TurboLean.ZygoteWorker.formatNoConfusionInfo,
  `TurboLean.ZygoteWorker.formatTrivialStructOpt,
  `TurboLean.ZygoteWorker.formatCtorFieldInfo,
  `TurboLean.ZygoteWorker.isWhitelistedPublicSigExtName,
  `TurboLean.ZygoteWorker.walkHotspotMessageData
]


/-- The 49 baseline-exact compiled private names (module `TurboLean.ZygoteWorker`, mangling
`_private.TurboLean.ZygoteWorker.0.*`), captured from the `44ce925b` monolith environment.
Includes source privates and their generated aux decls (matchers, sparse cases, init fns). -/
def expectedPrivateMangledNames : List Name := [
`_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatAttrKind,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatAttrKind.match_1,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatCoeFnType,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatCoeFnType.match_1,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatConstKind,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatConstKind.match_1,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatConstantExportPayload,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatConstantExportPayload.match_1,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatCtorFieldInfo,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatCtorFieldInfo.match_1,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatDiscrKey,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatDiscrKey.match_1,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatExternEntry,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatExternEntry.match_1,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatGrindEntry,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatGrindEntry.match_1,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatHeadIndex,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatHeadIndex.match_1,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatHintsStr,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatHintsStr.match_1,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatInlineAttr,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatInlineAttr.match_1,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatInstanceEntry,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatLcnfDeclIO,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatLcnfDeclIO.match_1,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatLcnfDeclIO.match_3,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatLcnfSignature,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatNoConfusionInfo,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatNoConfusionInfo.match_1,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatQuotStr,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatQuotStr.match_1,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatReducibilityStatus,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatReducibilityStatus.match_1,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatSimpEntry,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatSimpEntry.match_1,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatSimpEntry.match_3,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatTrivialStructOpt,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.formatTrivialStructOpt.match_1,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.initFn._@.TurboLean.ZygoteWorker.1241512177._hygCtx._hyg.2,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.isWhitelistedPublicSigExtName,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.walkHotspotMessageData,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.walkHotspotMessageData._sparseCasesOn_1,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.walkHotspotMessageData._sparseCasesOn_8,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.walkHotspotMessageData._unsafe_rec,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.walkHotspotMessageData.match_1,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.walkHotspotMessageData.match_4,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.walkHotspotMessageData.match_6,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.walkHotspotMessageData.match_8,
  `_private.TurboLean.ZygoteWorker.0.TurboLean.ZygoteWorker.«command#emit_zygote_toolchain_shims»
]

/-- Shim-generated public declarations: the `#emit_zygote_toolchain_shims` invocation is
root-resident (its private `formatReducibilityStatus` is consumed by the root signature-audit
code), so these six publics necessarily elaborate in the root module after all imported
submodules, unlike their baseline position between the instance and `Wire`. -/
def rootResidentShimPublics : List Name := [
  `TurboLean.ZygoteWorker.replayKernelConstants,
  `TurboLean.ZygoteWorker.checkKernelDecl,
  `TurboLean.ZygoteWorker.publicImportArtifacts,
  `TurboLean.ZygoteWorker.monoTypeModuleEntries,
  `TurboLean.ZygoteWorker.hasMonoTypeModuleEntries,
  `TurboLean.ZygoteWorker.originatingMessage?
]

/-- The only ZygoteWorker-family submodules permitted by the revised decomposition. -/
def expectedSplitModules : List Name := [
  `TurboLean.ZygoteWorker.Env,
  `TurboLean.ZygoteWorker.Wire,
  `TurboLean.ZygoteWorker.KernelAudit
]

/-- Submodules that must not exist (folded back into the root module). -/
def removedSplitModules : List Name := [
  `TurboLean.ZygoteWorker.StatementHashing,
  `TurboLean.ZygoteWorker.Signature,
  `TurboLean.ZygoteWorker.Replay,
  `TurboLean.ZygoteWorker.Compiler,
  `TurboLean.ZygoteWorker.Hotspots
]

def checkZygoteWorkerSplitPin : CoreM Unit := do
  let env ← getEnv
  let missingPublic := expectedPublicDecls.filter fun n => !env.contains n
  if !missingPublic.isEmpty then
    throwError s!"[ZygoteWorkerSplitPin] missing public declarations: {missingPublic}"
  let leakedPrivate := expectedPrivateDecls.filter fun n => env.contains n
  if !leakedPrivate.isEmpty then
    throwError s!"[ZygoteWorkerSplitPin] private declarations leaked into public environment: {leakedPrivate}"
  for m in expectedSplitModules do
    if (env.getModuleIdx? m).isNone then
      throwError s!"[ZygoteWorkerSplitPin] expected split module missing: {m}"
  for m in removedSplitModules do
    if (env.getModuleIdx? m).isSome then
      throwError s!"[ZygoteWorkerSplitPin] removed split module still present: {m}"
  let mut lastIdx : Option ModuleIdx := none
  for n in expectedPublicDecls do
    let some idx := env.getModuleIdxFor? n |
      throwError s!"[ZygoteWorkerSplitPin] public declaration has no module: {n}"
    if rootResidentShimPublics.contains n then
      continue
    if let some prev := lastIdx then
      if idx < prev then
        throwError s!"[ZygoteWorkerSplitPin] declaration order drift: {n} (module idx {idx}) after module idx {prev}"
    lastIdx := some idx
  let actualMangled := (env.constants.toList.map (·.1)).filter
    fun n => (`_private.TurboLean.ZygoteWorker).isPrefixOf n
  let actualMangledSorted := actualMangled.toArray.qsort (·.toString < ·.toString)
  let expectedMangledSorted := (expectedPrivateMangledNames.toArray.qsort (·.toString < ·.toString))
  if actualMangledSorted != expectedMangledSorted then
    let missing := expectedPrivateMangledNames.filter fun n => !actualMangled.contains n
    let extra := actualMangled.filter fun n => !expectedPrivateMangledNames.contains n
    throwError s!"[ZygoteWorkerSplitPin] compiled private names diverge from baseline (49): missing={missing.take 5} extra={extra.take 5}"

  let doubledNamespace := (env.constants.toList.map (·.1)).filter
    fun n => (`TurboLean.ZygoteWorker.TurboLean).isPrefixOf n
  if !doubledNamespace.isEmpty then
    throwError s!"[ZygoteWorkerSplitPin] doubled-namespace drift (baseline instance must keep single prefix): {doubledNamespace}"

#eval checkZygoteWorkerSplitPin

end LeanNative.Tests.ZygoteWorkerSplitPin
