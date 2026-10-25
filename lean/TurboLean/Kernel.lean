/-
  TurboLean.Kernel: Pure Unboxed Scalar C-ABI Kernel (`0 import Lean`, `0 sorryAx`)
  Contains all 55 `@[inline, export]` functions (`turbo_spec_*` and `leansys_*`) over
  `Bool`, `UInt8`, `UInt32`, `UInt64` with zero `Nat`, zero `String`, and zero `Repr`
  structures so `lean TurboLean/Kernel.lean -c TurboLean_Kernel.c` + `ld -r --gc-sections`
  produces a self-contained static archive (`libturbo_spec_cabi.a`) with 0 undefined symbols
  and zero hand-written C fallbacks.
-/

namespace TurboLean.Kernel

@[inline]
def canSafelyFissionHavePrologue (prologueContainsIntro : Bool) : Bool := !prologueContainsIntro

@[inline]
def riscvDivU64Spec (lhs rhs : UInt64) : UInt64 := if rhs == 0 then 0xffffffffffffffff else lhs / rhs

@[inline]
def riscvRemU64Spec (lhs rhs : UInt64) : UInt64 := if rhs == 0 then lhs else lhs % rhs

@[inline]
def specAuditWitnessGate (posOk negRefuted : Bool) : Bool :=
  posOk && negRefuted

@[inline]
def isScopeIsolatedForFastOlean (openSectionDepth hasSectionLocalVar : Bool) : Bool :=
  !openSectionDepth && !hasSectionLocalVar

@[inline]
def verifyDagScheduleStep (inDegree completedDeps totalDeps visitedNodes totalNodes : UInt64) : Bool :=
  inDegree == 0 && completedDeps == totalDeps && visitedNodes < totalNodes

@[inline]
def verifyModuleCacheKey (toolchainMatch argsMatch srcMatch depOleansMatch configMatch : Bool) : Bool :=
  toolchainMatch && argsMatch && srcMatch && depOleansMatch && configMatch

@[inline]
def verifyModuleArtifactSet (hasOlean hasIlean isModule hasServerOlean hasPrivateOlean needsC hasC : Bool) : Bool :=
  hasOlean && hasIlean && (!isModule || (hasServerOlean && hasPrivateOlean)) && (!needsC || hasC)

@[inline]
def verifyStaticLakeConfig (hasConfig hasDynamicScript hasUnbuiltExternDep hasUnsupportedFacet : Bool) : Bool :=
  hasConfig && !hasDynamicScript && !hasUnbuiltExternDep && !hasUnsupportedFacet

@[inline]
def verifySlicePassGate (sliceLen minGrain simdWidth : UInt64) (nonAliasing lazyReductionHomomorphic : Bool) : Bool :=
  sliceLen > 0 && simdWidth > 0 && (sliceLen % simdWidth == 0 || minGrain <= sliceLen) &&
  nonAliasing && lazyReductionHomomorphic

@[inline]
def verifyTlz1TokenBounds (isMatch : Bool) (offset tokenLen outLen uncompressedCap : UInt64) : Bool :=
  outLen <= uncompressedCap && tokenLen <= uncompressedCap - outLen &&
    (!isMatch || (0 < offset && offset <= outLen))

@[inline]
def verifyLexerCommentGuard (inString isEscaped twoBytesAvail : Bool) (blockDepth maxDepth : UInt64) : Bool :=
  !inString && !isEscaped && twoBytesAvail && blockDepth < maxDepth

@[inline]
def verifyFarkasBoundedStep (objCoeff colSum accCost weightCost bound : UInt64) : Bool :=
  objCoeff <= colSum && accCost <= bound && weightCost <= bound - accCost

@[inline]
def verifyIdentBloomMatch (isExcludedCore : Bool) (candMask contextMask : UInt64) : Bool :=
  !isExcludedCore && candMask != 0 && (contextMask == 0 || (candMask &&& contextMask) != 0)

/-- Tier-aware Matryoshka cascade router (`0 = pass`, `1 = prune_stop`, `2 = abstain_escalate`). -/
@[inline]
def matryoshkaTierRouterSpec (survPermille pruneFloorPermille escalateBandPermille epsTierPermille : UInt64)
    (counterexampleFound burnedAtEqualOrHigherBudget : Bool) : UInt8 :=
  if counterexampleFound then 1
  else if burnedAtEqualOrHigherBudget then 2
  else if survPermille + epsTierPermille < pruneFloorPermille then 1
  else if survPermille < escalateBandPermille + epsTierPermille then 2
  else 0

@[inline, export turbo_spec_is_closed_section_needed]
def isClosedSectionNeededC (minNeededIdx targetIdx : UInt64) : Bool := decide (minNeededIdx ≤ targetIdx)
abbrev cAbiIsClosedSectionNeeded := isClosedSectionNeededC

@[inline, export turbo_spec_precompute_min_needed_idx]
def precomputeSectionMinNeededIdxC (secClose firstRefIdx totalSpans : UInt64) : UInt64 :=
  if secClose < firstRefIdx then firstRefIdx else totalSpans

@[inline, export turbo_spec_can_fission_have]
def canSafelyFissionHavePrologueC (prologueContainsIntro : Bool) : Bool :=
  canSafelyFissionHavePrologue prologueContainsIntro
abbrev cAbiCanFissionHave := canSafelyFissionHavePrologueC

@[inline, export turbo_spec_sanitize_phase_options]
def sanitizePhaseOptionsC (allowStub warningAsError forbidSorryAx : Bool) : UInt8 :=
  let _ := forbidSorryAx
  let w := if allowStub then false else warningAsError
  let f := if allowStub then false else true
  (if w then 1 else 0) ||| (if f then 2 else 0)

@[inline, export turbo_spec_sanitize_warning_as_error]
def cAbiSanitizeWarningAsError (allowStub warningAsError : Bool) : Bool :=
  if allowStub then false else warningAsError

@[inline, export turbo_spec_sanitize_forbid_sorry_ax]
def cAbiSanitizeForbidSorryAx (allowStub forbidSorryAx : Bool) : Bool :=
  let _ := forbidSorryAx
  if allowStub then false else true

@[inline, export turbo_spec_is_sound_decl_summary]
def isSoundDeclSummaryC (isAxiom isUnsafe isExternOrImplementedBy hasForbidden : Bool) : Bool :=
  !isAxiom && !isUnsafe && !isExternOrImplementedBy && !hasForbidden
abbrev cAbiIsSoundDeclSummary := isSoundDeclSummaryC

@[inline, export turbo_spec_check_statement_pinned]
def cAbiCheckStatementPinned (expectedTypeHash actualTypeHash : UInt64) (isNestedInductive : Bool) : Bool :=
  (expectedTypeHash == actualTypeHash) && !isNestedInductive

@[inline, export turbo_spec_node_effective_cost]
def nodeEffectiveCostC (rttUs queueDepth ewmaExecUs concurrency : UInt64) : UInt64 :=
  let conc := if concurrency == 0 then 1 else concurrency
  rttUs + ((queueDepth + 1) * ewmaExecUs) / conc

@[inline, export turbo_spec_is_remote_eligible]
def isRemoteEligibleC (ttl : UInt64) (isHealthy supportsTarget : Bool) : Bool :=
  decide (ttl > 0) && isHealthy && supportsTarget

@[inline, export turbo_spec_should_switch_route]
def shouldSwitchRouteC (bestCost candCost : UInt64) (candEligible : Bool) : Bool :=
  candEligible && decide (candCost < bestCost)

@[inline, export turbo_spec_classify_compute_target]
def classifyComputeTargetC (tripCount : UInt64) (is256Bit isMatrixOp hasTpu hasGpu : Bool) : UInt8 :=
  if tripCount < 4096 then 0 else if isMatrixOp && hasTpu then 2 else if is256Bit && hasGpu then 1
  else if hasTpu then 2 else if hasGpu then 1 else 0

@[inline, export turbo_spec_splitmix64]
def splitMix64C (x : UInt64) : UInt64 :=
  let s := x + 0x9e3779b97f4a7c15
  let z1 := (s ^^^ (s >>> 30)) * 0xbf58476d1ce4e5b9
  let z2 := (z1 ^^^ (z1 >>> 27)) * 0x94d049bb133111eb
  z2 ^^^ (z2 >>> 31)

@[inline, export turbo_spec_boundary_u256_limb]
def boundaryU256LimbC (slot limbIdx : UInt64) : UInt64 :=
  let s := slot &&& 15; let l := limbIdx &&& 3
  if s == 0 then 0 else if s == 1 then (if l == 0 then 1 else 0)
  else if s == 2 then 0xffffffffffffffff
  else if s == 3 then (if l == 0 then 0xfffffffffffffffe else 0xffffffffffffffff)
  else if s == 4 then 0x5555555555555555 else if s == 5 then 0xaaaaaaaaaaaaaaaa
  else if s == 6 then (if l < 2 then 0xffffffffffffffff else 0)
  else if s == 7 then (if l == 1 then 1 else 0) else if s == 8 then (if l == 2 then 1 else 0)
  else if s == 9 then (if l == 3 then 1 else 0)
  else if s == 10 then (if l == 3 then 0x8000000000000000 else 0)
  else if s == 11 then (if l == 0 then 0xffffffffffffffff else 0)
  else if s == 12 then (if l == 0 then 2 else 0)
  else if s == 13 then (if l == 0 then 3 else if l == 1 then 5 else if l == 2 then 7 else 11)
  else if s == 14 then
    (if l == 0 then 0x123456789abcdef0 else if l == 1 then 0xfedcba9876543210
     else if l == 2 then 0x0f0f0f0f0f0f0f0f else 0xf0f0f0f0f0f0f0f0)
  else 0x8000000000000000

@[inline, export turbo_spec_gen_u256_limb]
def genU256LimbC (idx seed paramId limbIdx : UInt64) : UInt64 :=
  if idx < 4096 then boundaryU256LimbC ((idx >>> ((4 * paramId) &&& 63)) &&& 15) limbIdx
  else splitMix64C ((idx * 1315423911) ^^^ (seed * 2654435761) ^^^ (paramId * 0x9e3779b97f4a7c15) + (limbIdx &&& 3))

@[inline, export turbo_spec_u256_lt]
def u256LtC (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) : Bool :=
  if a3 = b3 then
    if a2 = b2 then
      if a1 = b1 then decide (a0 < b0) else decide (a1 < b1)
    else decide (a2 < b2)
  else decide (a3 < b3)

@[inline, export turbo_spec_eval_u64_binop]
def evalU64BinOpC (op : UInt8) (lhs rhs : UInt64) : UInt64 :=
  if op == 0 then lhs + rhs else if op == 1 then (if lhs >= rhs then lhs - rhs else 0)
  else if op == 2 then lhs * rhs else if op == 3 then (if rhs == 0 then 0 else lhs / rhs)
  else if op == 4 then (if rhs == 0 then 0 else lhs % rhs) else if op == 5 then lhs &&& rhs
  else if op == 6 then lhs ||| rhs else if op == 7 then lhs ^^^ rhs
  else if op == 8 then lhs <<< (rhs &&& 63) else if op == 9 then lhs >>> (rhs &&& 63)
  else if op == 10 then (if lhs == rhs then 1 else 0) else if op == 11 then (if lhs != rhs then 1 else 0)
  else if op == 12 then (if lhs < rhs then 1 else 0) else if op == 13 then (if lhs <= rhs then 1 else 0)
  else if op == 14 then (if lhs > rhs then 1 else 0) else if op == 15 then (if lhs >= rhs then 1 else 0)
  else lhs - rhs

@[inline, export turbo_spec_step_verdict_consistent]
def stepVerdictConsistentC (fullOk compactOk : Bool) : Bool := fullOk == compactOk

@[inline, export turbo_spec_affine_step_budget]
def affineStepBudgetC (scale offset steps : UInt64) : UInt64 := scale * steps + offset

@[inline, export turbo_spec_loop_step_budget]
def loopStepBudgetC (initSteps fuel scale offset iterSteps : UInt64) : UInt64 :=
  initSteps + fuel * (scale * iterSteps + offset)

@[inline, export turbo_spec_check_step_budget_le]
def checkStepBudgetLeC (actualSteps candidateK : UInt64) : Bool := decide (actualSteps ≤ candidateK)

@[inline, export turbo_spec_riscv_div_u64]
def riscvDivU64C (lhs rhs : UInt64) : UInt64 := riscvDivU64Spec lhs rhs

@[inline, export turbo_spec_riscv_rem_u64]
def riscvRemU64C (lhs rhs : UInt64) : UInt64 := riscvRemU64Spec lhs rhs

@[inline, export turbo_spec_zygote_lca_reuse_safe]
def zygoteLcaReuseSafeC (ancestorLen prefixLen : UInt64) : Bool :=
  0 < ancestorLen && ancestorLen <= prefixLen

@[inline, export turbo_spec_audit_witness_gate]
def specAuditWitnessGateC (posOk negRefuted : Bool) : Bool :=
  specAuditWitnessGate posOk negRefuted

@[inline, export turbo_spec_effective_cone_job_cap]
def effectiveConeJobCapC (totalUncached requestedMax : UInt64) : UInt64 :=
  if requestedMax == 0 || totalUncached <= requestedMax then totalUncached else requestedMax

@[inline, export turbo_spec_is_scope_isolated_for_fast_olean]
def isScopeIsolatedForFastOleanC (openSectionDepth hasSectionLocalVar : Bool) : Bool :=
  isScopeIsolatedForFastOlean openSectionDepth hasSectionLocalVar

@[inline, export turbo_spec_matryoshka_tier_router]
def matryoshkaTierRouterC (survPermille pruneFloorPermille escalateBandPermille epsTierPermille : UInt64)
    (counterexampleFound burnedAtEqualOrHigherBudget : Bool) : UInt8 :=
  matryoshkaTierRouterSpec survPermille pruneFloorPermille escalateBandPermille epsTierPermille
    counterexampleFound burnedAtEqualOrHigherBudget

@[inline, export turbo_spec_verify_dag_schedule_step]
def verifyDagScheduleStepC (inDegree completedDeps totalDeps visitedNodes totalNodes : UInt64) : Bool :=
  verifyDagScheduleStep inDegree completedDeps totalDeps visitedNodes totalNodes

@[inline, export turbo_spec_verify_module_cache_key]
def verifyModuleCacheKeyC (toolchainMatch argsMatch srcMatch depOleansMatch configMatch : Bool) : Bool :=
  verifyModuleCacheKey toolchainMatch argsMatch srcMatch depOleansMatch configMatch

@[inline, export turbo_spec_verify_module_artifact_set]
def verifyModuleArtifactSetC (hasOlean hasIlean isModule hasServerOlean hasPrivateOlean needsC hasC : Bool) : Bool :=
  verifyModuleArtifactSet hasOlean hasIlean isModule hasServerOlean hasPrivateOlean needsC hasC

@[inline, export turbo_spec_verify_static_lake_config]
def verifyStaticLakeConfigC (hasConfig hasDynamicScript hasUnbuiltExternDep hasUnsupportedFacet : Bool) : Bool :=
  verifyStaticLakeConfig hasConfig hasDynamicScript hasUnbuiltExternDep hasUnsupportedFacet

@[inline, export turbo_spec_verify_slice_pass_gate]
def verifySlicePassGateC (sliceLen minGrain simdWidth : UInt64) (nonAliasing lazyReductionHomomorphic : Bool) : Bool :=
  verifySlicePassGate sliceLen minGrain simdWidth nonAliasing lazyReductionHomomorphic

@[inline, export turbo_spec_verify_tlz1_token]
def verifyTlz1TokenBoundsC (isMatch : Bool) (offset tokenLen outLen uncompressedCap : UInt64) : Bool :=
  verifyTlz1TokenBounds isMatch offset tokenLen outLen uncompressedCap

@[inline, export turbo_spec_verify_lexer_comment_guard]
def verifyLexerCommentGuardC (inString isEscaped twoBytesAvail : Bool) (blockDepth maxDepth : UInt64) : Bool :=
  verifyLexerCommentGuard inString isEscaped twoBytesAvail blockDepth maxDepth

@[inline, export turbo_spec_verify_farkas_step]
def verifyFarkasBoundedStepC (objCoeff colSum accCost weightCost bound : UInt64) : Bool :=
  verifyFarkasBoundedStep objCoeff colSum accCost weightCost bound

@[inline, export turbo_spec_verify_ident_bloom]
def verifyIdentBloomMatchC (isExcludedCore : Bool) (candMask contextMask : UInt64) : Bool :=
  verifyIdentBloomMatch isExcludedCore candMask contextMask

@[export turbo_spec_combined_step]
def combinedStepC (i : UInt64) : UInt64 :=
  let needed := isClosedSectionNeededC (i &&& 63) 32
  let isForbidden := decide ((i &&& 7) = 7)
  let isSound := isSoundDeclSummaryC isForbidden false false false
  let h := i ^^^ 0xA5A55A5A
  let pinned := cAbiCheckStatementPinned h h false
  let sm := splitMix64C i
  let unhealthyMask := 0 - (decide ((i &&& 15) = 0)).toUInt64
  let cost := unhealthyMask ||| nodeEffectiveCostC ((i &&& 1023) / 1000) (i &&& 7) 2 4
  let lt := u256LtC sm i (sm ^^^ i) (i &&& 3) i sm (i ^^^ 1) ((i + 1) &&& 3)
  needed.toUInt64 ^^^ isSound.toUInt64 ^^^ pinned.toUInt64 ^^^ sm ^^^
  (cost &&& 0xFFFF) ^^^ lt.toUInt64 ^^^ isForbidden.toUInt64

@[inline, export leansys_verify_slice_bounds]
def verifySliceBoundsSysC (off len cap : UInt64) : UInt8 :=
  if off <= cap && len <= cap - off then 1 else 0

@[inline, export leansys_verify_wal_frame]
def verifyWalFrameSysC (magic totalLen : UInt32) (availLen expectedCrc actualCrc : UInt64) : UInt8 :=
  if magic == 0x4C535953 && totalLen.toUInt64 <= availLen && expectedCrc == actualCrc then 1 else 0

@[inline, export leansys_verify_cas_digest]
def verifyCasDigestSysC (expectedHash actualHash : UInt64) (hasPathTraversal : UInt8) : UInt8 :=
  if expectedHash != 0 && expectedHash == actualHash && hasPathTraversal == 0 then 1 else 0

@[inline, export leansys_check_http_bounds]
def checkHttpBoundsSysC (headersCount : UInt32) (contentLen bodyAvail : UInt64) (authOk : UInt8) : UInt8 :=
  if headersCount <= 32 && contentLen <= 16777216 && contentLen <= bodyAvail && authOk == 1 then 1 else 0

@[inline, export leansys_verify_jsonl_tape]
def verifyJsonlTapeSysC (keyOff keyLen valOff valLen bufCap : UInt64) (depth : UInt32) : UInt8 :=
  if keyOff <= bufCap && keyLen <= bufCap - keyOff &&
     valOff <= bufCap && valLen <= bufCap - valOff &&
     keyOff + keyLen <= valOff && depth <= 32 then 1 else 0

@[inline, export leansys_verify_ring_cursor]
def verifyRingCursorSysC (head tail cap msgLen : UInt64) : UInt8 :=
  if cap > 0 && tail <= head && head - tail <= cap &&
     msgLen > 0 && msgLen <= cap - (head - tail) then 1 else 0

@[inline, export leansys_verify_sst_block]
def verifySstBlockSysC (magic numEntries : UInt32) (indexOff footerOff fileSize bloomMask : UInt64) : UInt8 :=
  if magic == 0x4C535354 && numEntries <= 65536 &&
     indexOff <= footerOff && numEntries.toUInt64 * 16 <= footerOff - indexOff &&
     footerOff <= fileSize && 24 <= fileSize - footerOff && bloomMask != 0 then 1 else 0

@[inline, export leansys_verify_poll_interest]
def verifyPollInterestSysC (activeConns maxConns keepAliveReqs maxKeepAlive : UInt32)
    (idleMs maxIdleMs : UInt64) : UInt8 :=
  if activeConns < maxConns && keepAliveReqs < maxKeepAlive && idleMs <= maxIdleMs then 1 else 0

@[inline, export leansys_verify_rlimit_budget]
def verifyRlimitBudgetSysC (rssBytes maxRssBytes elapsedMs timeoutMs pipeBytes maxPipeBytes : UInt64) : UInt8 :=
  if rssBytes <= maxRssBytes && elapsedMs <= timeoutMs && pipeBytes <= maxPipeBytes then 1 else 0

@[inline, export leansys_verify_composite_key_order]
def verifyCompositeKeyOrderSysC (aHi aLo aSeq bHi bLo bSeq : UInt64) : UInt8 :=
  if aHi < bHi || (aHi == bHi && (aLo < bLo || (aLo == bLo && aSeq <= bSeq))) then 1 else 0

@[inline, export leansys_verify_token_auth]
def verifyTokenAuthSysC (matchCur hasPrev matchPrev scopeOk : UInt8) (nowEpoch expiresAt : UInt64) : UInt8 :=
  let tokenMatch := matchCur == 1 || (hasPrev == 1 && matchPrev == 1)
  if tokenMatch && scopeOk == 1 && (expiresAt == 0 || nowEpoch <= expiresAt) then 1 else 0

@[inline, export leansys_verify_log_window]
def verifyLogWindowSysC (startOff nextOff fileLen maxChunkBytes : UInt64) : UInt8 :=
  if startOff <= nextOff && nextOff <= fileLen &&
     nextOff - startOff <= maxChunkBytes && maxChunkBytes <= 262144 then 1 else 0

@[inline, export leansys_verify_jsonrpc_frame]
def verifyJsonRpcFrameSysC (hasV2 hasId : UInt8) (methodLen : UInt32) (frameBytes : UInt64) : UInt8 :=
  if hasV2 == 1 && hasId == 1 && methodLen > 0 && methodLen <= 128 && frameBytes <= 4194304 then 1 else 0

@[inline, export leansys_mix64_word]
def mix64WordSysC (acc word : UInt64) : UInt64 :=
  let v1 := acc + word * 0xBF58476D1CE4E5B9
  let v2 := (v1 <<< 31) ||| (v1 >>> 33)
  let v3 := v2 * 0x9E3779B97F4A7C15
  v3 ^^^ (v3 >>> 27)

@[inline, export leansys_gate_admit]
def verifyGateAdmitSysC (noSorryAx statementPinned certVerified : UInt8) : UInt8 :=
  if noSorryAx == 1 && statementPinned == 1 && certVerified == 1 then 1 else 0

@[inline, export leansys_verify_par_chunk]
def verifyParChunkSysC (chunkStart chunkEnd totalLen minGrain : UInt64) : UInt8 :=
  if chunkStart < chunkEnd && chunkEnd <= totalLen && (minGrain <= chunkEnd - chunkStart || chunkEnd == totalLen) then 1 else 0

@[inline, export leansys_verify_arena_disjoint]
def verifyArenaDisjointSysC (offA lenA offB lenB arenaCap : UInt64) : UInt8 :=
  if offA <= arenaCap && lenA <= arenaCap - offA &&
     offB <= arenaCap && lenB <= arenaCap - offB &&
     (offA + lenA <= offB || offB + lenB <= offA) then 1 else 0

@[inline, export leansys_verify_snapshot_visibility]
def verifySnapshotVisibilitySysC (entrySeq maxSnapshotSeq : UInt64) (isTombstone : UInt8) : UInt8 :=
  if entrySeq <= maxSnapshotSeq && isTombstone == 0 then 1 else 0

@[inline, export leansys_verify_http_route_match]
def verifyHttpRouteMatchSysC (methodMatch pathMatch : UInt8) (routeIdx routeCount : UInt32) : UInt8 :=
  if methodMatch == 1 && pathMatch == 1 && routeIdx < routeCount && routeCount <= 64 then 1 else 0

@[inline, export leansys_verify_counterexample_triage]
def verifyCounterexampleTriageSysC (hasViolation hasMissingHypHint refDisagreesWithCandidate triageClass : UInt8) : UInt8 :=
  if hasViolation == 1 &&
     ((hasMissingHypHint == 1 && triageClass == 1) ||
      (hasMissingHypHint == 0 && refDisagreesWithCandidate == 1 && triageClass == 2) ||
      (hasMissingHypHint == 0 && refDisagreesWithCandidate == 0 && triageClass == 3)) then 1 else 0

end TurboLean.Kernel
