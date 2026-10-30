/-
  TurboLean.Kernel: Backward-compatible alias module re-exporting `TurboLean.PolicyGates`.
  The canonical unboxed C-ABI policy gates now live in `TurboLean.PolicyGates`, cleanly
  separated from the dependent CIC typechecker kernel (`ConLeche` in `TurboLean/ConLeche.lean`).
-/
import TurboLean.PolicyGates

namespace TurboLean.Kernel

export TurboLean.PolicyGates (
  canSafelyFissionHavePrologue
  riscvDivU64Spec
  riscvRemU64Spec
  specAuditWitnessGate
  isScopeIsolatedForFastOlean
  verifyDagScheduleStep
  verifyModuleCacheKey
  verifyModuleArtifactSet
  verifyStaticLakeConfig
  verifySlicePassGate
  verifyTlz1TokenBounds
  verifyLexerCommentGuard
  verifyFarkasBoundedStep
  verifyIdentBloomMatch
  verifyConLecheOleanShard
  verifyElabHeaderPinGate
  verifyAuditMaterializeGate
  verifyPackTrustAdmission
  verifyHygieneItemAdmitted
  matryoshkaTierRouterSpec
  isClosedSectionNeededC
  cAbiIsClosedSectionNeeded
  precomputeSectionMinNeededIdxC
  canSafelyFissionHavePrologueC
  cAbiCanFissionHave
  sanitizePhaseOptionsC
  cAbiSanitizeWarningAsError
  cAbiSanitizeForbidSorryAx
  isSoundDeclSummaryC
  cAbiIsSoundDeclSummary
  cAbiCheckStatementPinned
  nodeEffectiveCostC
  isRemoteEligibleC
  shouldSwitchRouteC
  classifyComputeTargetC
  splitMix64C
  boundaryU256LimbC
  genU256LimbC
  u256LtC
  evalU64BinOpC
  stepVerdictConsistentC
  affineStepBudgetC
  loopStepBudgetC
  checkStepBudgetLeC
  riscvDivU64C
  riscvRemU64C
  zygoteLcaReuseSafeC
  specAuditWitnessGateC
  effectiveConeJobCapC
  isScopeIsolatedForFastOleanC
  matryoshkaTierRouterC
  verifyDagScheduleStepC
  verifyModuleCacheKeyC
  verifyModuleArtifactSetC
  verifyStaticLakeConfigC
  verifySlicePassGateC
  verifyTlz1TokenBoundsC
  verifyLexerCommentGuardC
  verifyFarkasBoundedStepC
  verifyIdentBloomMatchC
  verifyConLecheOleanShardC
  verifyElabHeaderPinGateC
  verifyAuditMaterializeGateC
  verifyPackTrustAdmissionC
  verifyHygieneItemAdmittedC
  combinedStepC
)

end TurboLean.Kernel
