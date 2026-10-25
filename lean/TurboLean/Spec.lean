/-
  TurboLean.Spec: Unified Compositional Specification & Meta-Specification Kernel
  Zero `import Lean` (standalone-compilable into `libturbo_spec_cabi.a` and `lean-native-core`),
  zero `sorry`, zero `native_decide`.
  - Layer 0  : Universal contracts (`MetaGateSpec`, `SpeculativeGate`) imported from `LeanSys.Contracts`.
  - Layer I  : Meta-Specifications (`Costed`, `MetaGateSpec`, `MetaAlgorithmSpec`) &
               Universal Combinators (`SpeculativeGate`, `SoundCacheTier`, `ObservationalProj`,
               `WitnessRefuter`, `ArgminRouteFold`, `ClockedStepBudget`).
  - Layer II : Declarative `MetaGateSpec` / `MetaAlgorithmSpec` bundles, ≤ 3-line corollaries, and C-ABI `@[inline, export]`.
-/
import TurboLean.Kernel
import LeanSys.Gate

namespace TurboLean.Spec
export LeanSys.Contracts (
  MetaGateSpec
  checkGateAdmit
  checkGateAdmit_sound
  evalWithUntrustedAccelerator
  untrusted_accelerator_kernel_replay_sound
  untrusted_accelerator_timeout_fallback
  speculative_gate_rejection_fallback
  speculative_gate_complete
  evalWithUntrustedOptPlugin
  untrusted_opt_plugin_tv_gate_sound
  untrusted_opt_plugin_timeout_fallback
  untrusted_opt_plugin_reject_fallback
)

export TurboLean.Kernel (
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
  combinedStepC
  verifySliceBoundsSysC
  verifyWalFrameSysC
  verifyCasDigestSysC
  checkHttpBoundsSysC
  verifyJsonlTapeSysC
  verifyRingCursorSysC
  verifySstBlockSysC
  verifyPollInterestSysC
  verifyRlimitBudgetSysC
  verifyCompositeKeyOrderSysC
  verifyTokenAuthSysC
  verifyLogWindowSysC
  verifyJsonRpcFrameSysC
  mix64WordSysC
  verifyGateAdmitSysC
  verifyParChunkSysC
  verifyArenaDisjointSysC
)

/-! ============================================================================
    LAYER I: META-SPECIFICATIONS & UNIVERSAL ALGEBRAIC COMBINATORS
    ============================================================================ -/

structure Costed (α : Type) where
  val : α
  steps : Nat
  deriving Repr, DecidableEq, BEq

theorem MetaGateSpec.iff_safe {Input : Type} {Safe : Input → Prop} (M : MetaGateSpec Input Safe) (x : Input) :
    M.gate x = true ↔ Safe x := LeanSys.Contracts.MetaGateSpec.iff_safe M x
theorem MetaGateSpec.rejects_unsafe {Input : Type} {Safe : Input → Prop} (M : MetaGateSpec Input Safe) (x : Input)
    (h_unsafe : ¬ Safe x) : M.gate x = false :=
  LeanSys.Contracts.MetaGateSpec.rejects_unsafe M x h_unsafe
theorem MetaGateSpec.pos_ne_neg {Input : Type} {Safe : Input → Prop} (M : MetaGateSpec Input Safe) :
    M.posWitness ≠ M.negWitness := LeanSys.Contracts.MetaGateSpec.pos_ne_neg M

structure MetaAlgorithmSpec (Input Output : Type) where
  fast : Input → Costed Output
  oracle : Input → Output
  stepBound : Input → Nat
  equiv : ∀ x, (fast x).val = oracle x
  bounded : ∀ x, (fast x).steps ≤ stepBound x

theorem MetaAlgorithmSpec.sound_and_bounded {Input Output : Type} (A : MetaAlgorithmSpec Input Output) (x : Input) :
    (A.fast x).val = A.oracle x ∧ (A.fast x).steps ≤ A.stepBound x := ⟨A.equiv x, A.bounded x⟩

theorem speculative_gate_exists_witness {Goal Proof : Type}
    (accel : Goal → Option Proof) (kernelCheck : Goal → Proof → Bool) (g : Goal) (origProof : Proof)
    (h_ok : evalWithUntrustedAccelerator accel kernelCheck (fun x => kernelCheck x origProof) g = true) :
    ∃ p : Proof, kernelCheck g p = true := by
  unfold evalWithUntrustedAccelerator at h_ok; split at h_ok
  · rename_i dp _; by_cases h_dp : kernelCheck g dp = true
    · exact ⟨dp, h_dp⟩
    · exact ⟨origProof, by simpa [h_dp] using h_ok⟩
  · exact ⟨origProof, h_ok⟩

def evalAccelGuidedTacticSynth {Goal Proof : Type}
    (accelRefute : Goal → Bool) (synthTactic : Goal → Proof)
    (kernelVerify : Goal → Proof → Bool) (g : Goal) (origProof : Proof) : Bool :=
  if accelRefute g then false else if kernelVerify g (synthTactic g) then true else kernelVerify g origProof

abbrev evalTpuGuidedTacticSynth := @evalAccelGuidedTacticSynth

theorem refuter_gated_synth_sound {Goal Proof : Type}
    (tpuRefute : Goal → Bool) (synthTactic : Goal → Proof) (kernelVerify : Goal → Proof → Bool)
    (g : Goal) (origProof : Proof) (h_ok : evalAccelGuidedTacticSynth tpuRefute synthTactic kernelVerify g origProof = true) :
    tpuRefute g = false ∧ ∃ p : Proof, kernelVerify g p = true := by
  unfold evalAccelGuidedTacticSynth at h_ok; split at h_ok
  · contradiction
  · rename_i h_nr; refine ⟨Bool.eq_false_iff.mpr h_nr, ?_⟩
    by_cases h_syn : kernelVerify g (synthTactic g) = true
    · exact ⟨synthTactic g, h_syn⟩
    · exact ⟨origProof, by simpa [h_syn] using h_ok⟩

/-! ### Universal Combinator B: `SoundCacheTier` (Multi-Tier Cache Refinement & Batch Lifting) -/

def queryTier {K : Type} (cache : K → Option Bool) (fallback : K → Bool) (k : K) : Bool := (cache k).getD (fallback k)

theorem queryTier_eq_oracle {K : Type} (cache : K → Option Bool) (oracle : K → Bool)
    (h_sound : ∀ k v, cache k = some v → v = oracle k) (k : K) :
    queryTier cache oracle k = oracle k := by
  unfold queryTier; cases h : cache k <;> first | rfl | exact h_sound k _ h

theorem queryTier_batch_all_eq {K : Type} (cache : K → Option Bool) (oracle : K → Bool)
    (h_sound : ∀ k v, cache k = some v → v = oracle k) (ks : List K) :
    ks.all (queryTier cache oracle) = ks.all oracle := by
  induction ks <;> simp_all [queryTier_eq_oracle]

/-! ### Universal Combinator C: `ObservationalProj` (Quotient Invariance & Mutation Invalidation) -/

theorem proj_invariance {State Key Out : Type}
    (proj : State → Key) (f : Key → Out) (s1 s2 : State) (h_eq : proj s1 = proj s2) :
    f (proj s1) = f (proj s2) := congrArg f h_eq
theorem proj_mutation_invalidates_decide {State Key : Type} [DecidableEq State]
    (proj : State → Key) (s1 s2 : State) (h_diff : proj s1 ≠ proj s2) :
    decide (s1 = s2) = false := decide_eq_false (fun h_eq => h_diff (congrArg proj h_eq))
theorem proj_mutation_invalidates_beq {State Key : Type} [DecidableEq State]
    (proj : State → Key) (s1 s2 : State) (h_diff : proj s1 ≠ proj s2) :
    (s1 == s2) = false := beq_false_of_ne (fun h_eq => h_diff (congrArg proj h_eq))

/-! ### Universal Combinator D: `WitnessRefuter` (Existential Counterexample Refutation) -/

theorem witness_refutes_forall {Witness : Type}
    (evalHyps evalConcl : Witness → Bool) (w : Witness) (h_hyps : evalHyps w = true) (h_concl : evalConcl w = false) :
    ¬ (∀ x : Witness, evalHyps x = true → evalConcl x = true) :=
  fun h_all => by simpa [h_concl] using h_all w h_hyps

/-! ### Universal Combinator E: `ArgminRouteFold` (Queue-Aware Federated Argmin Routing) -/

structure NodeTelemetry where
  nodeId         : Nat
  isHealthy      : Bool
  supportsTarget : Bool
  rttUs          : Nat
  queueDepth     : Nat
  ewmaExecUs     : Nat
  concurrency    : Nat
  deriving Repr, DecidableEq, BEq

def nodeEffectiveCost (n : NodeTelemetry) : Nat := n.rttUs + ((n.queueDepth + 1) * n.ewmaExecUs) / (Nat.max 1 n.concurrency)
def isRemoteEligible (ttl : Nat) (n : NodeTelemetry) : Bool := decide (ttl > 0) && n.isHealthy && n.supportsTarget
def chooseBetterRoute (best : NodeTelemetry) (cand : NodeTelemetry) (ttl : Nat) : NodeTelemetry :=
  if isRemoteEligible ttl cand && decide (nodeEffectiveCost cand < nodeEffectiveCost best) then cand else best
def selectOptimalRoute (localNode : NodeTelemetry) (remotes : List NodeTelemetry) (ttl : Nat) : NodeTelemetry :=
  remotes.foldl (fun best cand => chooseBetterRoute best cand ttl) localNode
def stepFederationTtl (ttl : Nat) : Nat := ttl - 1

theorem isRemoteEligible_eq_true_props (ttl : Nat) (r : NodeTelemetry)
    (h_elig : isRemoteEligible ttl r = true) :
    r.isHealthy = true ∧ r.supportsTarget = true ∧ ttl > 0 := by
  simp only [isRemoteEligible, Bool.and_eq_true, decide_eq_true_eq] at h_elig
  exact ⟨h_elig.1.2, h_elig.2, h_elig.1.1⟩

theorem choose_better_route_cost_le_both (best cand : NodeTelemetry) (ttl : Nat) :
    nodeEffectiveCost (chooseBetterRoute best cand ttl) ≤ nodeEffectiveCost best ∧
    (isRemoteEligible ttl cand = true →
      nodeEffectiveCost (chooseBetterRoute best cand ttl) ≤ nodeEffectiveCost cand) := by
  unfold chooseBetterRoute; split <;> simp_all [Nat.le_of_lt]

theorem foldl_chooseBetterRoute_le_init (init : NodeTelemetry) (rs : List NodeTelemetry) (ttl : Nat) :
    nodeEffectiveCost (rs.foldl (fun b c => chooseBetterRoute b c ttl) init) ≤ nodeEffectiveCost init := by
  induction rs generalizing init with
  | nil => exact Nat.le_refl _
  | cons hd tl ih => exact Nat.le_trans (ih _) (choose_better_route_cost_le_both init hd ttl).1

theorem foldl_chooseBetterRoute_le_mem (init : NodeTelemetry) (rs : List NodeTelemetry) (ttl : Nat)
    (c : NodeTelemetry) (h_mem : c ∈ rs) (h_elig : isRemoteEligible ttl c = true) :
    nodeEffectiveCost (rs.foldl (fun b cand => chooseBetterRoute b cand ttl) init) ≤ nodeEffectiveCost c := by
  induction rs generalizing init with
  | nil => contradiction
  | cons hd tl ih =>
    rcases List.mem_cons.mp h_mem with rfl | h_tl
    · exact Nat.le_trans (foldl_chooseBetterRoute_le_init _ tl ttl) ((choose_better_route_cost_le_both init c ttl).2 h_elig)
    · exact ih _ h_tl

theorem chooseBetterRoute_eq_left_of_le (best cand : NodeTelemetry) (ttl : Nat)
    (h_le : nodeEffectiveCost best ≤ nodeEffectiveCost cand) :
    chooseBetterRoute best cand ttl = best := by
  simp [chooseBetterRoute, Nat.not_lt.mpr h_le]

theorem foldl_chooseBetterRoute_eq_init_of_all_ge (init : NodeTelemetry) (rs : List NodeTelemetry) (ttl : Nat)
    (h_all : ∀ c ∈ rs, nodeEffectiveCost init ≤ nodeEffectiveCost c) :
    rs.foldl (fun b c => chooseBetterRoute b c ttl) init = init := by
  induction rs with
  | nil => rfl
  | cons hd tl ih =>
    simp [chooseBetterRoute_eq_left_of_le init hd ttl (h_all hd (List.mem_cons_self ..)),
          ih (fun c hc => h_all c (List.mem_cons_of_mem hd hc))]

theorem foldl_chooseBetterRoute_zero_ttl (init : NodeTelemetry) (rs : List NodeTelemetry) :
    rs.foldl (fun b c => chooseBetterRoute b c 0) init = init := by
  induction rs generalizing init <;> simp_all [chooseBetterRoute, isRemoteEligible]

theorem chooseBetterRoute_eq_or_eligible (best cand : NodeTelemetry) (ttl : Nat) :
    chooseBetterRoute best cand ttl = best ∨
    (chooseBetterRoute best cand ttl = cand ∧ isRemoteEligible ttl cand = true) := by
  unfold chooseBetterRoute; split <;> simp_all

theorem foldl_chooseBetterRoute_mem_or_init (init : NodeTelemetry) (rs : List NodeTelemetry) (ttl : Nat) :
    let r := rs.foldl (fun b c => chooseBetterRoute b c ttl) init
    r = init ∨ (isRemoteEligible ttl r = true ∧ r ∈ rs) := by
  induction rs generalizing init with
  | nil => exact Or.inl rfl
  | cons hd tl ih =>
    rcases ih (chooseBetterRoute init hd ttl) with h_eq | ⟨h_el, h_mem⟩
    · rcases chooseBetterRoute_eq_or_eligible init hd ttl with h_keep | ⟨h_sw, h_el⟩
      · exact Or.inl (h_eq.trans h_keep)
      · exact Or.inr ⟨by simpa [h_eq.trans h_sw] using h_el, by simp [h_eq.trans h_sw]⟩
    · exact Or.inr ⟨h_el, List.mem_cons_of_mem hd h_mem⟩

theorem foldl_chooseBetterRoute_dominance
    (localNode : NodeTelemetry) (remotes : List NodeTelemetry) (ttl : Nat)
    (h_rtt : localNode.rttUs = 0) (h_q : localNode.queueDepth = 0) (h_conc : localNode.concurrency = 1)
    (h_dom : ∀ c ∈ remotes, localNode.ewmaExecUs ≤ c.rttUs) :
    selectOptimalRoute localNode remotes ttl = localNode := by
  apply foldl_chooseBetterRoute_eq_init_of_all_ge
  intro c hc; unfold nodeEffectiveCost; rw [h_rtt, h_q, h_conc]
  simpa using Nat.le_trans (h_dom c hc) (Nat.le_add_right c.rttUs _)

/-! ### Universal Combinator F: `ClockedStepBudget` (Affine Step-Budget Composition) -/

structure AffineStepBudget where
  scale  : Nat
  offset : Nat
  deriving Repr, DecidableEq, BEq

def AffineStepBudget.eval (b : AffineStepBudget) (steps : Nat) : Nat := b.scale * steps + b.offset
def composeAffineBudget (outer inner : AffineStepBudget) : AffineStepBudget :=
  { scale := outer.scale * inner.scale, offset := outer.scale * inner.offset + outer.offset }
def evalPassChainBudget (passes : List AffineStepBudget) : AffineStepBudget :=
  passes.foldl (fun acc p => composeAffineBudget p acc) { scale := 1, offset := 0 }
def evalLoopStepBudget (initSteps fuel : Nat) (bodyBudget : AffineStepBudget) (iterSteps : Nat) : Nat :=
  initSteps + fuel * bodyBudget.eval iterSteps

inductive SptTree (α : Type) where
  | leaf : SptTree α
  | node : Option α → SptTree α → SptTree α → SptTree α
  deriving Repr, DecidableEq, BEq

def sptLookup {α : Type} : SptTree α → List Bool → Option α
  | .leaf, _ => none
  | .node v _ _, [] => v
  | .node _ l r, b :: bs => sptLookup (if b then r else l) bs

def sptInsert {α : Type} : SptTree α → List Bool → α → SptTree α
  | .leaf, [], val => .node (some val) .leaf .leaf
  | .leaf, b :: bs, val => if b then .node none .leaf (sptInsert .leaf bs val) else .node none (sptInsert .leaf bs val) .leaf
  | .node _ l r, [], val => .node (some val) l r
  | .node v l r, b :: bs, val => if b then .node v l (sptInsert r bs val) else .node v (sptInsert l bs val) r

theorem sptLookup_insert_same {α : Type} (t : SptTree α) (k : List Bool) (val : α) :
    sptLookup (sptInsert t k val) k = some val := by
  induction k generalizing t with
  | nil => cases t <;> rfl
  | cons b bs ih => cases t <;> cases b <;> simp [sptInsert, sptLookup, ih]

theorem composeAffineBudget_eval (outer inner : AffineStepBudget) (steps : Nat) :
    (composeAffineBudget outer inner).eval steps = outer.eval (inner.eval steps) := by
  simp [composeAffineBudget, AffineStepBudget.eval, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem affine_step_budget_monotone (b : AffineStepBudget) {s1 s2 : Nat} (h : s1 ≤ s2) :
    b.eval s1 ≤ b.eval s2 := Nat.add_le_add_right (Nat.mul_le_mul_left b.scale h) b.offset

theorem evalLoopStepBudget_monotone (init fuel : Nat) (b : AffineStepBudget) {s1 s2 : Nat} (h : s1 ≤ s2) :
    evalLoopStepBudget init fuel b s1 ≤ evalLoopStepBudget init fuel b s2 :=
  Nat.add_le_add_left (Nat.mul_le_mul_left fuel (affine_step_budget_monotone b h)) init

/-! ============================================================================
    LAYER II: DECLARATIVE COROLLARIES (≤ 3 LINES) & C-ABI EXPORTS
    ============================================================================ -/

/-! ## 1. Kernel Extension & Statement Pinning Gates -/

structure KernelDeclSummary where
  name : String
  isAxiom : Bool
  isUnsafe : Bool
  isExternOrImplementedBy : Bool
  usedForbidden : List String
  deriving Repr, DecidableEq, BEq

def isSoundDeclSummary (d : KernelDeclSummary) : Bool :=
  !d.isAxiom && !d.isUnsafe && !d.isExternOrImplementedBy && d.usedForbidden.isEmpty
def isSoundKernelExtension (decls : List KernelDeclSummary) : Bool := decls.all isSoundDeclSummary

theorem isSoundDeclSummary_eq_true_iff (d : KernelDeclSummary) :
    isSoundDeclSummary d = true ↔
      (d.isAxiom = false ∧ d.isUnsafe = false ∧ d.isExternOrImplementedBy = false ∧ d.usedForbidden = []) := by
  simp [isSoundDeclSummary, Bool.and_eq_true, List.isEmpty_iff, and_assoc]

def declSummaryMetaSpec : MetaGateSpec KernelDeclSummary
    (fun d => d.isAxiom = false ∧ d.isUnsafe = false ∧ d.isExternOrImplementedBy = false ∧ d.usedForbidden = []) where
  gate := isSoundDeclSummary
  sound := fun d => (isSoundDeclSummary_eq_true_iff d).mp
  complete := fun d => (isSoundDeclSummary_eq_true_iff d).mpr
  posWitness := ⟨"clean_thm", false, false, false, []⟩
  negWitness := ⟨"spoofed_ax", true, false, false, []⟩
  nonVacuous := rfl
  tight := rfl

theorem isSoundKernelExtension_rejects_unsafe_or_axiom (d : KernelDeclSummary)
    (h : d.isAxiom = true ∨ d.isUnsafe = true ∨ d.isExternOrImplementedBy = true) :
    isSoundDeclSummary d = false :=
  declSummaryMetaSpec.rejects_unsafe d (by rcases h with h | h | h <;> simp [h])

def checkStatementPinned (expectedTypeHash actualTypeHash : Nat) (isNestedInductive : Bool) : Bool :=
  (expectedTypeHash == actualTypeHash) && !isNestedInductive

theorem statement_pinning_blocks_tampering (expected actual : Nat) (nested : Bool) (h_tamper : expected ≠ actual) :
    checkStatementPinned expected actual nested = false := by simp [checkStatementPinned, beq_false_of_ne h_tamper]
theorem sea_monster_gate_rejects_nested (expected actual : Nat) :
    checkStatementPinned expected actual true = false := by simp [checkStatementPinned]

/-! ## 2. Observational Quotient & Dependency Cone Locality (`ObservationalProj`) -/

structure EnvDecl where
  name : String
  isTheorem : Bool
  stmtHash : Nat
  bodyHash : Nat
  deriving Repr, DecidableEq, BEq

def declInterfaceProj (d : EnvDecl) : String × Bool × Nat :=
  (d.name, d.isTheorem, if d.isTheorem then d.stmtHash else d.stmtHash + d.bodyHash)
def envInterfaceProj (env : List EnvDecl) : List (String × Bool × Nat) := env.map declInterfaceProj

theorem declInterfaceProj_thm_body_invariant (name : String) (stmt b1 b2 : Nat) :
    declInterfaceProj ⟨name, true, stmt, b1⟩ = declInterfaceProj ⟨name, true, stmt, b2⟩ := rfl

theorem observational_quotient_sound {Decl : Type}
    (verifyFromInterface : List (String × Bool × Nat) → Decl → Bool)
    (env1 env2 : List EnvDecl) (target : Decl) (h_quot : envInterfaceProj env1 = envInterfaceProj env2) :
    verifyFromInterface (envInterfaceProj env1) target = verifyFromInterface (envInterfaceProj env2) target :=
  proj_invariance envInterfaceProj (fun k => verifyFromInterface k target) env1 env2 h_quot

def coneFilter (inCone : String → Bool) (env : List EnvDecl) : List EnvDecl := env.filter (fun d => inCone d.name)

theorem cone_frame_drop_outside (inCone : String → Bool) (frameDecl : EnvDecl) (env : List EnvDecl)
    (h_out : inCone frameDecl.name = false) :
    coneFilter inCone (frameDecl :: env) = coneFilter inCone env := by simp [coneFilter, h_out]

theorem cone_frame_rule_locality {Decl : Type}
    (verifyFromCone : List EnvDecl → Decl → Bool)
    (inCone : String → Bool) (frameDecl : EnvDecl) (env : List EnvDecl) (target : Decl)
    (h_out : inCone frameDecl.name = false) :
    verifyFromCone (coneFilter inCone (frameDecl :: env)) target =
      verifyFromCone (coneFilter inCone env) target :=
  proj_invariance (coneFilter inCone) (fun c => verifyFromCone c target)
    (frameDecl :: env) env (cone_frame_drop_outside inCone frameDecl env h_out)

/-! ## 3. Multi-Tier Cache & Sub-Proof Cut-Fission (`SoundCacheTier`) -/

theorem two_tier_cache_refinement (shmCache sqliteCache : Nat → Option Bool) (oracle : Nat → Bool)
    (h_shm : ∀ k v, shmCache k = some v → v = oracle k)
    (h_sql : ∀ k v, sqliteCache k = some v → v = oracle k) (k : Nat) :
    queryTier shmCache (queryTier sqliteCache oracle) k = oracle k := by
  rw [queryTier_eq_oracle shmCache _ (fun x v hx => (h_shm x v hx).trans (queryTier_eq_oracle sqliteCache oracle h_sql x).symm),
      queryTier_eq_oracle sqliteCache oracle h_sql]

abbrev verifyStepOutOfCore (diskCache : Nat → Option Bool) (kernelStepClean : Nat → Bool) (g : Nat) : Bool :=
  queryTier diskCache kernelStepClean g
def verifyFissionedTheorem (diskCache : Nat → Option Bool) (kernelStepClean : Nat → Bool) (subGoals : List Nat) : Bool :=
  subGoals.all (verifyStepOutOfCore diskCache kernelStepClean)

theorem out_of_core_step_eq_kernel (diskCache : Nat → Option Bool) (kernelStepClean : Nat → Bool)
    (h_disk : ∀ g v, diskCache g = some v → v = kernelStepClean g) (g : Nat) :
    verifyStepOutOfCore diskCache kernelStepClean g = kernelStepClean g :=
  queryTier_eq_oracle diskCache kernelStepClean h_disk g

theorem have_fission_cut_sound (diskCache : Nat → Option Bool) (kernelStepClean : Nat → Bool)
    (h_disk : ∀ g v, diskCache g = some v → v = kernelStepClean g) (subGoals : List Nat) :
    verifyFissionedTheorem diskCache kernelStepClean subGoals = subGoals.all kernelStepClean :=
  queryTier_batch_all_eq diskCache kernelStepClean h_disk subGoals

/-! ## 4. Non-Vacuity & Tightness Gate (`MetaGateSpec`) -/

structure SpecAuditVerdict where
  satisfiedPreconditions : Nat
  mutantsKilled : Nat
  totalMutants : Nat
  deriving Repr, DecidableEq, BEq

def isTightNonVacuousSpec (v : SpecAuditVerdict) : Bool :=
  decide (v.satisfiedPreconditions > 0) && decide (v.totalMutants > 0) && decide (v.mutantsKilled == v.totalMutants)
theorem meta_spec_rejects_vacuous (m total : Nat) : isTightNonVacuousSpec ⟨0, m, total⟩ = false := rfl

theorem meta_spec_non_vacuous_tightness (v : SpecAuditVerdict) :
    isTightNonVacuousSpec v = true ↔
      (v.satisfiedPreconditions > 0 ∧ v.totalMutants > 0 ∧ v.mutantsKilled = v.totalMutants) := by
  simp [isTightNonVacuousSpec, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

def specAuditMetaSpec : MetaGateSpec SpecAuditVerdict
    (fun v => v.satisfiedPreconditions > 0 ∧ v.totalMutants > 0 ∧ v.mutantsKilled = v.totalMutants) where
  gate       := isTightNonVacuousSpec
  sound      := fun v => (meta_spec_non_vacuous_tightness v).mp
  complete   := fun v => (meta_spec_non_vacuous_tightness v).mpr
  posWitness := ⟨4, 3, 3⟩
  negWitness := ⟨0, 3, 3⟩
  nonVacuous := rfl
  tight      := rfl

/-! ## 5. `.olean` Digest Key Invalidation & Determinism Gate (`ObservationalProj`) -/

structure FullShardKey where
  toolchain : String
  oleanDigests : List Nat
  coneHash : Nat
  stmtHash : Nat
  proofHash : Nat
  deriving Repr, DecidableEq

theorem imported_olean_mutation_invalidates_key (k1 k2 : FullShardKey)
    (h_diff : k1.oleanDigests ≠ k2.oleanDigests) : decide (k1 = k2) = false :=
  proj_mutation_invalidates_decide FullShardKey.oleanDigests k1 k2 h_diff

structure PartitionedOleanKey where
  toolchain : String
  localSearchPathDigest : Nat
  importedModuleDigest : Nat
  deriving Repr, DecidableEq

theorem package_pruned_olean_pool_key_sound (k1 k2 : PartitionedOleanKey)
    (h_mut : k1.localSearchPathDigest ≠ k2.localSearchPathDigest ∨ k1.importedModuleDigest ≠ k2.importedModuleDigest) :
    (k1 == k2) = false :=
  proj_mutation_invalidates_beq (fun k => (k.localSearchPathDigest, k.importedModuleDigest)) k1 k2
    (fun h => by injection h with h1 h2; exact h_mut.elim (· h1) (· h2))

structure EvalOutput where
  exitOk : Bool
  messages : List String
  stdout : String
  deriving Repr, DecidableEq

def verifyDeterminismGate (workerOut freshLeanOut : EvalOutput) : Option EvalOutput :=
  if decide (workerOut = freshLeanOut) then some workerOut else none

theorem verifyDeterminismGate_sound (w f out : EvalOutput) (h : verifyDeterminismGate w f = some out) :
    out = f ∧ w = f := by unfold verifyDeterminismGate at h; split at h <;> simp_all

/-! ## 6. Multi-Agent Worktree Lease & Supersession GC Safety -/

structure WorktreeLeaseState where
  worktreeId : String
  isActive : Bool
  activeBlobs : List Nat
  deriving Repr, DecidableEq, BEq

def isBlobProtectedByLeases (pinnedHead : List Nat) (leases : List WorktreeLeaseState) (b : Nat) : Bool :=
  pinnedHead.contains b || leases.any (fun w => w.isActive && w.activeBlobs.contains b)
def canEvictSupersededBlob (pinnedHead : List Nat) (leases : List WorktreeLeaseState) (b : Nat) : Bool :=
  !isBlobProtectedByLeases pinnedHead leases b

theorem head_pinned_blob_never_evicted (pinnedHead : List Nat) (leases : List WorktreeLeaseState) (b : Nat)
    (h_pin : pinnedHead.contains b = true) :
    canEvictSupersededBlob pinnedHead leases b = false := by
  simp only [canEvictSupersededBlob, isBlobProtectedByLeases, h_pin, Bool.true_or, Bool.not_true]

theorem active_worktree_lease_protects_blob (pinnedHead : List Nat) (leases : List WorktreeLeaseState) (b : Nat)
    (h_active : leases.any (fun w => w.isActive && w.activeBlobs.contains b) = true) :
    canEvictSupersededBlob pinnedHead leases b = false := by
  simp only [canEvictSupersededBlob, isBlobProtectedByLeases, h_active, Bool.or_true, Bool.not_true]

/-! ## 7. Speculative Accelerator & Counterexample Corollaries (`SpeculativeGate` & `WitnessRefuter`) -/

def verifyWithDistilledReplay {Goal Proof : Type}
    (kernelCheck : Goal → Proof → Bool) (g : Goal) (origProof : Proof) (distilledProof? : Option Proof) : Bool :=
  evalWithUntrustedAccelerator (fun _ => distilledProof?) kernelCheck (fun x => kernelCheck x origProof) g

theorem distilled_certificate_replay_sound {Goal Proof : Type}
    (kernelCheck : Goal → Proof → Bool) (g : Goal) (origProof : Proof) (distilledProof? : Option Proof)
    (h_ok : verifyWithDistilledReplay kernelCheck g origProof distilledProof? = true) :
    ∃ p : Proof, kernelCheck g p = true :=
  speculative_gate_exists_witness (fun _ => distilledProof?) kernelCheck g origProof h_ok

theorem distilled_certificate_stale_hint_complete {Goal Proof : Type}
    (kernelCheck : Goal → Proof → Bool) (g : Goal) (origProof : Proof) (distilledProof? : Option Proof)
    (h_orig : kernelCheck g origProof = true) :
    verifyWithDistilledReplay kernelCheck g origProof distilledProof? = true :=
  speculative_gate_complete (fun _ => distilledProof?) kernelCheck (fun x => kernelCheck x origProof) g h_orig

def replayPrunedSimpOnly (verifyPrunedSimpOnly : List String → Bool) (fullSimpOracle : Bool) (explicitLemmas : List String) : Bool :=
  evalWithUntrustedAccelerator (fun _ => some explicitLemmas) (fun _ ls => verifyPrunedSimpOnly ls) (fun _ => fullSimpOracle) ()

theorem discr_tree_pruned_simp_only_sound
    (verifyPrunedSimpOnly : List String → Bool) (fullSimpOracle : Bool) (explicitLemmas : List String)
    (h_sound : ∀ ls, verifyPrunedSimpOnly ls = true → fullSimpOracle = true) :
    replayPrunedSimpOnly verifyPrunedSimpOnly fullSimpOracle explicitLemmas = fullSimpOracle :=
  untrusted_accelerator_kernel_replay_sound (fun _ => some explicitLemmas)
    (fun _ ls => verifyPrunedSimpOnly ls) (fun _ => fullSimpOracle) (fun _ ls h => h_sound ls h) ()

theorem discr_tree_pruned_fallback_complete
    (verifyPrunedSimpOnly : List String → Bool) (fullSimpOracle : Bool) (explicitLemmas : List String)
    (h_insufficient : verifyPrunedSimpOnly explicitLemmas = false) :
    replayPrunedSimpOnly verifyPrunedSimpOnly fullSimpOracle explicitLemmas = fullSimpOracle :=
  speculative_gate_rejection_fallback (fun _ => some explicitLemmas)
    (fun _ ls => verifyPrunedSimpOnly ls) (fun _ => fullSimpOracle) () explicitLemmas rfl h_insufficient

theorem multi_site_tactic_chain_sound (kernelAccepts : Nat → Bool) (origChain optChain : Nat) :
    evalWithUntrustedAccelerator (fun _ => some optChain) (fun _ c => kernelAccepts c) kernelAccepts origChain =
      (kernelAccepts optChain || kernelAccepts origChain) := by simp [evalWithUntrustedAccelerator]

def evalAcSum (terms : List Nat) : Nat := terms.foldl (· + ·) 0

theorem ac_normalizer_replay_sound {Goal Cert : Type}
    (acPropose : Goal → Option Cert) (kernelVerifyCert : Goal → Cert → Bool) (kernelFallback : Goal → Bool)
    (h_sound : ∀ g c, kernelVerifyCert g c = true → kernelFallback g = true) (g : Goal) :
    evalWithUntrustedAccelerator acPropose kernelVerifyCert kernelFallback g = kernelFallback g :=
  untrusted_accelerator_kernel_replay_sound acPropose kernelVerifyCert kernelFallback h_sound g

theorem simd_omega_counterexample_sound {Witness : Type}
    (evalHyps evalConcl : Witness → Bool) (w : Witness)
    (h_hyps : evalHyps w = true) (h_concl : evalConcl w = false) :
    ¬ (∀ x : Witness, evalHyps x = true → evalConcl x = true) :=
  witness_refutes_forall evalHyps evalConcl w h_hyps h_concl

def evalBvBoundaryLane (w : Nat) (lhs rhs : Nat → Nat) : Bool := decide (lhs w == rhs w)

theorem bv_boundary_counterexample_sound (w : Nat) (lhs rhs : Nat → Nat)
    (h_cex : evalBvBoundaryLane w lhs rhs = false) :
    ¬ (∀ x, lhs x = rhs x) :=
  witness_refutes_forall (fun _ => true) (fun x => evalBvBoundaryLane x lhs rhs) w rfl h_cex ∘
    fun h x _ => by simp [evalBvBoundaryLane, h x]

/-! ## 8. Batch Fission IPC, Rewrite Fusion & Prefix Line Padding -/

def verifyBatchFissionIpc (ckptValid : Bool) (subVerdicts : List Bool) : Bool := ckptValid && subVerdicts.all id
theorem batch_fission_ipc_sound (ckptValid : Bool) (subVerdicts : List Bool) :
    verifyBatchFissionIpc ckptValid subVerdicts = true ↔ (ckptValid = true ∧ ∀ b ∈ subVerdicts, b = true) := by
  simp [verifyBatchFissionIpc, List.all_eq_true]

def applyRwRules (rules : List (Nat → Nat)) (e : Nat) : Nat := rules.foldl (fun acc r => r acc) e
theorem rw_chain_fusion_sound (r1 r2 : List (Nat → Nat)) (e : Nat) :
    applyRwRules (r1 ++ r2) e = applyRwRules r2 (applyRwRules r1 e) := by simp [applyRwRules, List.foldl_append]

def paddedCommandLine (prefixLines relLine : Nat) : Nat := prefixLines + relLine
theorem eval_prefix_line_padding_preserves_pos (splitIdx offsetInSuffix : Nat) :
    paddedCommandLine splitIdx (1 + offsetInSuffix) = (splitIdx + 1) + offsetInSuffix := by unfold paddedCommandLine; omega

/-! ## 9. Closed-Section Pruning (`MetaAlgorithmSpec`), `where` Stubbing & Fission Prologue Guard -/

def precomputeSectionMinNeededIdx (secClose firstRefIdx totalSpans : Nat) : Costed Nat :=
  { val := if secClose < firstRefIdx then firstRefIdx else totalSpans, steps := 1 }
def closedSectionNeededNaiveOracle (minNeededIdx targetIdx : Nat) : Bool := decide (minNeededIdx ≤ targetIdx)
def isClosedSectionNeededFast (minNeededIdx targetIdx : Nat) : Costed Bool :=
  { val := decide (minNeededIdx ≤ targetIdx), steps := 1 }
def computeClosedSectionMaskCosted (minNeededIdxs : List Nat) (targetIdx : Nat) : Costed (List Bool) :=
  { val := minNeededIdxs.map (fun m => (isClosedSectionNeededFast m targetIdx).val), steps := minNeededIdxs.length }

def closedSectionMaskMetaSpec (minNeededIdxs : List Nat) : MetaAlgorithmSpec Nat (List Bool) where
  fast      := computeClosedSectionMaskCosted minNeededIdxs
  oracle    := fun targetIdx => minNeededIdxs.map (fun m => closedSectionNeededNaiveOracle m targetIdx)
  stepBound := fun _ => minNeededIdxs.length
  equiv     := fun _ => rfl
  bounded   := fun _ => Nat.le_refl _

theorem closed_section_fast_eq_naive_oracle (minNeededIdx targetIdx : Nat) :
    (isClosedSectionNeededFast minNeededIdx targetIdx).val =
      closedSectionNeededNaiveOracle minNeededIdx targetIdx ∧
    (isClosedSectionNeededFast minNeededIdx targetIdx).steps = 1 := ⟨rfl, rfl⟩

theorem closed_section_mask_linear_complexity (minNeededIdxs : List Nat) (targetIdx : Nat) :
    (computeClosedSectionMaskCosted minNeededIdxs targetIdx).steps ≤ minNeededIdxs.length :=
  (closedSectionMaskMetaSpec minNeededIdxs).bounded targetIdx

inductive TheoremBodyForm where
  | assignBy     (sig : String) (rhs : String)
  | patternMatch (sig : String) (arms : String)
  | whereStruct  (sig : String) (whereBody : String)
  deriving Repr, DecidableEq, BEq

def stubTheoremForm : TheoremBodyForm → String × String
  | .assignBy sig _     => (sig, "<stub>")
  | .patternMatch sig _ => (sig, "<stub>")
  | .whereStruct sig _  => (sig, "<stub>")

theorem where_theorem_stub_preserves_interface_hash (sig body1 body2 : String) :
    stubTheoremForm (.whereStruct sig body1) = stubTheoremForm (.whereStruct sig body2) := rfl

structure VerificationPhaseConfig where
  allowStub      : Bool
  warningAsError : Bool
  forbidSorryAx  : Bool
  deriving Repr, DecidableEq, BEq

@[inline]
def sanitizePhaseOptions (cfg : VerificationPhaseConfig) : VerificationPhaseConfig :=
  if cfg.allowStub then { cfg with warningAsError := false, forbidSorryAx := false }
  else { cfg with forbidSorryAx := true }

theorem stubbed_prefix_warningAsError_safe (w f : Bool) :
    (sanitizePhaseOptions { allowStub := true, warningAsError := w, forbidSorryAx := f }).warningAsError = false ∧
    (sanitizePhaseOptions { allowStub := false, warningAsError := w, forbidSorryAx := f }).forbidSorryAx = true :=
  ⟨rfl, rfl⟩

def fissionPrologueMetaSpec : MetaGateSpec Bool (fun hasIntro => hasIntro = false) where
  gate       := canSafelyFissionHavePrologue
  sound      := fun b h => by simpa [canSafelyFissionHavePrologue] using h
  complete   := fun b h => by simp [canSafelyFissionHavePrologue, h]
  posWitness := false
  negWitness := true
  nonVacuous := rfl
  tight      := rfl

theorem fission_prologue_guard_sound :
    canSafelyFissionHavePrologue true = false ∧ canSafelyFissionHavePrologue false = true :=
  ⟨fissionPrologueMetaSpec.tight, fissionPrologueMetaSpec.nonVacuous⟩

/-! ## 10. C-ABI exports live in `TurboLean.Kernel` (re-exported above). -/

def zygoteLcaReuseSafe (ancestorLen prefixLen : Nat) : Bool :=
  decide (0 < ancestorLen ∧ ancestorLen ≤ prefixLen)

def zygoteLcaReuseMetaSpec : MetaGateSpec (Nat × Nat)
    (fun p => 0 < p.1 ∧ p.1 ≤ p.2) where
  gate := fun p => zygoteLcaReuseSafe p.1 p.2
  sound := fun _ h => of_decide_eq_true h
  complete := fun _ h => decide_eq_true h
  posWitness := (128, 256)
  negWitness := (512, 256)
  nonVacuous := rfl
  tight := rfl

theorem zygote_lca_delta_replay_partition (ancestorLen prefixLen : Nat)
    (h : zygoteLcaReuseSafe ancestorLen prefixLen = true) :
    ancestorLen + (prefixLen - ancestorLen) = prefixLen ∧ 0 < ancestorLen := by
  have ⟨h_pos, h_le⟩ := zygoteLcaReuseMetaSpec.sound (ancestorLen, prefixLen) h
  exact ⟨Nat.add_sub_of_le h_le, h_pos⟩

def specAuditWitnessMetaSpec : MetaGateSpec (Bool × Bool)
    (fun w => w.1 = true ∧ w.2 = true) where
  gate := fun w => specAuditWitnessGate w.1 w.2
  sound := fun w h => by simpa [specAuditWitnessGate, Bool.and_eq_true] using h
  complete := fun w h => by simpa [specAuditWitnessGate, Bool.and_eq_true] using h
  posWitness := (true, true)
  negWitness := (true, false)
  nonVacuous := rfl
  tight := rfl

def effectiveConeJobCap (totalUncached requestedMax : Nat) : Nat :=
  if requestedMax = 0 ∨ totalUncached ≤ requestedMax then totalUncached else requestedMax

theorem effectiveConeJobCap_le_total (totalUncached requestedMax : Nat) :
    effectiveConeJobCap totalUncached requestedMax ≤ totalUncached := by
  unfold effectiveConeJobCap; split <;> omega

def scopeIsolatedFastOleanMetaSpec : MetaGateSpec (Bool × Bool)
    (fun s => s.1 = false ∧ s.2 = false) where
  gate := fun s => isScopeIsolatedForFastOlean s.1 s.2
  sound := fun s h => by simpa [isScopeIsolatedForFastOlean, Bool.and_eq_true] using h
  complete := fun s h => by simpa [isScopeIsolatedForFastOlean, Bool.and_eq_true] using h
  posWitness := (false, false)
  negWitness := (true, false)
  nonVacuous := rfl
  tight := rfl

theorem scope_sensitive_shard_rejects_fast_olean (openSec hasVar : Bool)
    (h : openSec = true ∨ hasVar = true) :
    isScopeIsolatedForFastOlean openSec hasVar = false :=
  scopeIsolatedFastOleanMetaSpec.rejects_unsafe (openSec, hasVar) (by rcases h with h | h <;> simp [h])

theorem matryoshka_tier_router_never_prunes_within_eps
    (surv floor esc eps : UInt64) (burned : Bool)
    (h_margin : ¬ (surv + eps < floor)) :
    matryoshkaTierRouterC surv floor esc eps false burned ≠ 1 := by
  unfold matryoshkaTierRouterC matryoshkaTierRouterSpec
  cases burned <;> simp [h_margin]
  split <;> decide

theorem c_abi_exports_match_spec (m t : UInt64) (hasIntro allowStub warn forbid isAx isUn isExt : Bool) :
    cAbiIsClosedSectionNeeded m t = (isClosedSectionNeededFast m.toNat t.toNat).val ∧
    cAbiCanFissionHave hasIntro = canSafelyFissionHavePrologue hasIntro ∧
    cAbiSanitizeWarningAsError allowStub warn =
      (sanitizePhaseOptions { allowStub := allowStub, warningAsError := warn, forbidSorryAx := false }).warningAsError ∧
    cAbiSanitizeForbidSorryAx allowStub forbid =
      (sanitizePhaseOptions { allowStub := allowStub, warningAsError := false, forbidSorryAx := forbid }).forbidSorryAx ∧
    cAbiIsSoundDeclSummary isAx isUn isExt false =
      isSoundDeclSummary { name := "", isAxiom := isAx, isUnsafe := isUn, isExternOrImplementedBy := isExt, usedForbidden := [] } := by
  cases allowStub <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## 11. TPU-Guided Tactic Synthesis & Federated Routing Corollaries -/

theorem tpu_guided_tactic_synthesis_sound {Goal Proof : Type}
    (tpuRefute : Goal → Bool) (synthTactic : Goal → Proof) (kernelVerify : Goal → Proof → Bool)
    (g : Goal) (origProof : Proof) (h_ok : evalTpuGuidedTacticSynth tpuRefute synthTactic kernelVerify g origProof = true) :
    tpuRefute g = false ∧ ∃ p : Proof, kernelVerify g p = true :=
  refuter_gated_synth_sound tpuRefute synthTactic kernelVerify g origProof h_ok

theorem compact_diagnostic_preserves_verdict (verdict : Bool)
    (compactTokens verboseTokens : Nat) (h_smaller : compactTokens ≤ verboseTokens) :
    (verdict, compactTokens).1 = verdict ∧ verboseTokens - (verboseTokens - compactTokens) = compactTokens :=
  ⟨rfl, by omega⟩

theorem route_selection_cost_optimal (localNode : NodeTelemetry) (remotes : List NodeTelemetry) (ttl : Nat) :
    nodeEffectiveCost (selectOptimalRoute localNode remotes ttl) ≤ nodeEffectiveCost localNode ∧
    ∀ c ∈ remotes, isRemoteEligible ttl c = true →
      nodeEffectiveCost (selectOptimalRoute localNode remotes ttl) ≤ nodeEffectiveCost c :=
  ⟨foldl_chooseBetterRoute_le_init localNode remotes ttl, foldl_chooseBetterRoute_le_mem localNode remotes ttl⟩

theorem route_selection_local_zero_network_dominance
    (localNode : NodeTelemetry) (remotes : List NodeTelemetry) (ttl : Nat)
    (h_rtt : localNode.rttUs = 0) (h_q : localNode.queueDepth = 0) (h_conc : localNode.concurrency = 1)
    (h_dom : ∀ c ∈ remotes, localNode.ewmaExecUs ≤ c.rttUs) :
    selectOptimalRoute localNode remotes ttl = localNode ∧
    nodeEffectiveCost (selectOptimalRoute localNode remotes ttl) = nodeEffectiveCost localNode :=
  have h_sel := foldl_chooseBetterRoute_dominance localNode remotes ttl h_rtt h_q h_conc h_dom
  ⟨h_sel, congrArg nodeEffectiveCost h_sel⟩

theorem route_selection_failover_safe (localNode : NodeTelemetry) (remotes : List NodeTelemetry) (ttl : Nat) :
    let r := selectOptimalRoute localNode remotes ttl
    (r = localNode ∨ (isRemoteEligible ttl r = true ∧ r ∈ remotes)) ∧
    (r ≠ localNode → r.isHealthy = true ∧ r.supportsTarget = true ∧ ttl > 0) :=
  ⟨foldl_chooseBetterRoute_mem_or_init localNode remotes ttl, fun h_ne =>
    (foldl_chooseBetterRoute_mem_or_init localNode remotes ttl).elim
      (False.elim ∘ h_ne) (isRemoteEligible_eq_true_props ttl _ ∘ And.left)⟩

theorem federated_tree_routing_terminates (localNode : NodeTelemetry) (remotes : List NodeTelemetry) (ttl : Nat) :
    selectOptimalRoute localNode remotes 0 = localNode ∧ (ttl > 0 → stepFederationTtl ttl < ttl) :=
  ⟨foldl_chooseBetterRoute_zero_ttl localNode remotes, fun _ => by unfold stepFederationTtl; omega⟩

theorem bootstrap_shift_budget_additive (boot targetSteps boundK : Nat) (h : targetSteps ≤ boundK) :
    ({ scale := 1, offset := boot } : AffineStepBudget).eval targetSteps ≤ boot + boundK := by
  simpa [AffineStepBudget.eval, Nat.add_comm] using Nat.add_le_add_left h boot

theorem empirical_lower_bound_refutes_k_cand (obsMax candK : Nat) (h_gt : candK < obsMax) :
    ¬ (obsMax ≤ candK) := Nat.not_le.mpr h_gt

theorem riscv_div_by_zero_spec (x : UInt64) :
    riscvDivU64Spec x 0 = 0xffffffffffffffff ∧ riscvRemU64Spec x 0 = x := ⟨rfl, rfl⟩

theorem zisk_csr_atomic_step_budget (boot csrCount bodySteps boundK : Nat) (h : csrCount + bodySteps ≤ boundK) :
    ({ scale := 1, offset := boot } : AffineStepBudget).eval (csrCount + bodySteps) ≤ boot + boundK :=
  bootstrap_shift_budget_additive boot (csrCount + bodySteps) boundK h

theorem pass_chain_two_passes_eval (p1 p2 : AffineStepBudget) (steps : Nat) :
    (evalPassChainBudget [p1, p2]).eval steps = p2.eval (p1.eval steps) := by
  simp [evalPassChainBudget, composeAffineBudget, AffineStepBudget.eval, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem spt_rom_fetch_deterministic {α : Type} (rom : SptTree α) (pcBits : List Bool) (instr : α) :
    sptLookup (sptInsert rom pcBits instr) pcBits = some instr := sptLookup_insert_same rom pcBits instr

/-! ## 12. Native Module DAG Builder, Per-Module CAS & Static Config Gates -/

structure DagScheduleState where
  inDegree      : UInt64
  completedDeps : UInt64
  totalDeps     : UInt64
  visitedNodes  : UInt64
  totalNodes    : UInt64
  deriving Repr, DecidableEq, BEq

def dagScheduleStepMetaSpec : MetaGateSpec DagScheduleState
    (fun s => s.inDegree = 0 ∧ s.completedDeps = s.totalDeps ∧ s.visitedNodes < s.totalNodes) where
  gate := fun s =>
    verifyDagScheduleStep s.inDegree s.completedDeps s.totalDeps s.visitedNodes s.totalNodes
  sound := fun s h => by
    simpa [verifyDagScheduleStep, Bool.and_eq_true, beq_iff_eq, UInt64.lt_iff_toNat_lt, and_assoc] using h
  complete := fun s h => by
    simpa [verifyDagScheduleStep, Bool.and_eq_true, beq_iff_eq, UInt64.lt_iff_toNat_lt, and_assoc] using h
  posWitness := ⟨0, 3, 3, 2, 5⟩
  negWitness := ⟨1, 2, 3, 2, 5⟩
  nonVacuous := rfl
  tight := rfl

theorem dag_schedule_step_rejects_unresolved_dep (s : DagScheduleState)
    (h_unready : s.inDegree ≠ 0 ∨ s.completedDeps ≠ s.totalDeps ∨ ¬ (s.visitedNodes < s.totalNodes)) :
    verifyDagScheduleStep s.inDegree s.completedDeps s.totalDeps s.visitedNodes s.totalNodes = false :=
  dagScheduleStepMetaSpec.rejects_unsafe s (by rcases h_unready with h | h | h <;> simp [h])

structure ModuleCacheKeyInputs where
  toolchainMatch : Bool
  argsMatch      : Bool
  srcMatch       : Bool
  depOleansMatch : Bool
  configMatch    : Bool
  deriving Repr, DecidableEq, BEq

def moduleCacheKeyMetaSpec : MetaGateSpec ModuleCacheKeyInputs
    (fun k => k.toolchainMatch = true ∧ k.argsMatch = true ∧ k.srcMatch = true ∧
      k.depOleansMatch = true ∧ k.configMatch = true) where
  gate := fun k =>
    verifyModuleCacheKey k.toolchainMatch k.argsMatch k.srcMatch k.depOleansMatch k.configMatch
  sound := fun k h => by
    simpa [verifyModuleCacheKey, Bool.and_eq_true, and_assoc] using h
  complete := fun k h => by
    simpa [verifyModuleCacheKey, Bool.and_eq_true, and_assoc] using h
  posWitness := ⟨true, true, true, true, true⟩
  negWitness := ⟨true, true, true, false, true⟩
  nonVacuous := rfl
  tight := rfl

theorem module_cache_reuse_conservative_sound (k : ModuleCacheKeyInputs)
    (h_hit : verifyModuleCacheKey k.toolchainMatch k.argsMatch k.srcMatch k.depOleansMatch k.configMatch = true) :
    k.toolchainMatch = true ∧ k.argsMatch = true ∧ k.srcMatch = true ∧
    k.depOleansMatch = true ∧ k.configMatch = true :=
  moduleCacheKeyMetaSpec.sound k h_hit

structure ModuleArtifactState where
  hasOlean        : Bool
  hasIlean        : Bool
  isModule        : Bool
  hasServerOlean  : Bool
  hasPrivateOlean : Bool
  needsC          : Bool
  hasC            : Bool
  deriving Repr, DecidableEq, BEq

def moduleArtifactSetMetaSpec : MetaGateSpec ModuleArtifactState
    (fun a => a.hasOlean = true ∧ a.hasIlean = true ∧
      (a.isModule = false ∨ (a.hasServerOlean = true ∧ a.hasPrivateOlean = true)) ∧
      (a.needsC = false ∨ a.hasC = true)) where
  gate := fun a =>
    verifyModuleArtifactSet a.hasOlean a.hasIlean a.isModule a.hasServerOlean a.hasPrivateOlean a.needsC a.hasC
  sound := fun a h => by
    simpa [verifyModuleArtifactSet, Bool.and_eq_true, Bool.or_eq_true, and_assoc] using h
  complete := fun a h => by
    simpa [verifyModuleArtifactSet, Bool.and_eq_true, Bool.or_eq_true, and_assoc] using h
  posWitness := ⟨true, true, true, true, true, false, false⟩
  negWitness := ⟨true, true, true, false, true, false, false⟩
  nonVacuous := rfl
  tight := rfl

theorem module_artifact_set_lazy_c_valid (isMod hasSrv hasPriv : Bool)
    (h_mod : isMod = false ∨ (hasSrv = true ∧ hasPriv = true)) :
    verifyModuleArtifactSet true true isMod hasSrv hasPriv false false = true :=
  moduleArtifactSetMetaSpec.complete ⟨true, true, isMod, hasSrv, hasPriv, false, false⟩ ⟨rfl, rfl, h_mod, Or.inl rfl⟩

structure StaticLakeConfigState where
  hasConfig            : Bool
  hasDynamicScript     : Bool
  hasUnbuiltExternDep  : Bool
  hasUnsupportedFacet  : Bool
  deriving Repr, DecidableEq, BEq

def staticLakeConfigMetaSpec : MetaGateSpec StaticLakeConfigState
    (fun c => c.hasConfig = true ∧ c.hasDynamicScript = false ∧
      c.hasUnbuiltExternDep = false ∧ c.hasUnsupportedFacet = false) where
  gate := fun c =>
    verifyStaticLakeConfig c.hasConfig c.hasDynamicScript c.hasUnbuiltExternDep c.hasUnsupportedFacet
  sound := fun c h => by
    simpa [verifyStaticLakeConfig, Bool.and_eq_true, and_assoc] using h
  complete := fun c h => by
    simpa [verifyStaticLakeConfig, Bool.and_eq_true, and_assoc] using h
  posWitness := ⟨true, false, false, false⟩
  negWitness := ⟨true, true, false, false⟩
  nonVacuous := rfl
  tight := rfl

theorem dynamic_lakefile_fails_closed (c : StaticLakeConfigState)
    (h_dyn : c.hasConfig = false ∨ c.hasDynamicScript = true ∨
      c.hasUnbuiltExternDep = true ∨ c.hasUnsupportedFacet = true) :
    verifyStaticLakeConfig c.hasConfig c.hasDynamicScript c.hasUnbuiltExternDep c.hasUnsupportedFacet = false :=
  staticLakeConfigMetaSpec.rejects_unsafe c (by rcases h_dyn with h | h | h | h <;> simp [h])

structure SlicePassGateState where
  sliceLen                 : UInt64
  minGrain                 : UInt64
  simdWidth                : UInt64
  nonAliasing              : Bool
  lazyReductionHomomorphic : Bool
  deriving Repr, DecidableEq, BEq

def slicePassGateMetaSpec : MetaGateSpec SlicePassGateState
    (fun s => s.sliceLen > 0 ∧ s.simdWidth > 0 ∧
      (s.sliceLen % s.simdWidth = 0 ∨ s.minGrain ≤ s.sliceLen) ∧
      s.nonAliasing = true ∧ s.lazyReductionHomomorphic = true) where
  gate := fun s =>
    verifySlicePassGate s.sliceLen s.minGrain s.simdWidth s.nonAliasing s.lazyReductionHomomorphic
  sound := fun s h => by
    simpa [verifySlicePassGate, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, and_assoc] using h
  complete := fun s h => by
    simpa [verifySlicePassGate, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, and_assoc] using h
  posWitness := ⟨256, 64, 4, true, true⟩
  negWitness := ⟨256, 64, 4, false, true⟩
  nonVacuous := rfl
  tight := rfl

theorem slice_pass_gate_rejects_aliasing_or_non_linear (s : SlicePassGateState)
    (h_bad : s.nonAliasing = false ∨ s.lazyReductionHomomorphic = false ∨ s.sliceLen = 0 ∨ s.simdWidth = 0) :
    verifySlicePassGate s.sliceLen s.minGrain s.simdWidth s.nonAliasing s.lazyReductionHomomorphic = false :=
  slicePassGateMetaSpec.rejects_unsafe s (by rcases h_bad with h | h | h | h <;> simp [h])

/-! ## 13. Pure Lean Migration Bug-Surface Gates (TLZ1 LZ77, Lexer Nesting, Farkas Overflow, SIMD Bloom) -/

structure Tlz1TokenState where
  isMatch         : Bool
  offset          : UInt64
  tokenLen        : UInt64
  outLen          : UInt64
  uncompressedCap : UInt64
  deriving Repr, DecidableEq, BEq

def tlz1TokenBoundsMetaSpec : MetaGateSpec Tlz1TokenState
    (fun s => s.outLen ≤ s.uncompressedCap ∧ s.tokenLen ≤ s.uncompressedCap - s.outLen ∧
      (s.isMatch = false ∨ (0 < s.offset ∧ s.offset ≤ s.outLen))) where
  gate := fun s =>
    verifyTlz1TokenBounds s.isMatch s.offset s.tokenLen s.outLen s.uncompressedCap
  sound := fun s h => by
    simpa [verifyTlz1TokenBounds, Bool.and_eq_true, Bool.or_eq_true, and_assoc] using h
  complete := fun s h => by
    simpa [verifyTlz1TokenBounds, Bool.and_eq_true, Bool.or_eq_true, and_assoc] using h
  posWitness := ⟨true, 4, 8, 16, 64⟩
  negWitness := ⟨true, 0, 8, 16, 64⟩
  nonVacuous := rfl
  tight := rfl

theorem tlz1_zero_offset_or_oob_rejected (s : Tlz1TokenState)
    (h_bad : ¬ (s.outLen ≤ s.uncompressedCap) ∨ ¬ (s.tokenLen ≤ s.uncompressedCap - s.outLen) ∨
      (s.isMatch = true ∧ (s.offset = 0 ∨ ¬ (s.offset ≤ s.outLen)))) :
    verifyTlz1TokenBounds s.isMatch s.offset s.tokenLen s.outLen s.uncompressedCap = false :=
  tlz1TokenBoundsMetaSpec.rejects_unsafe s (by
    rcases h_bad with h | h | ⟨hm, h0 | hoob⟩
    · simp [h]
    · simp [h]
    · simp [hm, h0]
    · simp [hm, hoob])

structure LexerCommentState where
  inString      : Bool
  isEscaped     : Bool
  twoBytesAvail : Bool
  blockDepth    : UInt64
  maxDepth      : UInt64
  deriving Repr, DecidableEq, BEq

def lexerCommentGuardMetaSpec : MetaGateSpec LexerCommentState
    (fun s => s.inString = false ∧ s.isEscaped = false ∧
      s.twoBytesAvail = true ∧ s.blockDepth < s.maxDepth) where
  gate := fun s =>
    verifyLexerCommentGuard s.inString s.isEscaped s.twoBytesAvail s.blockDepth s.maxDepth
  sound := fun s h => by
    simpa [verifyLexerCommentGuard, Bool.and_eq_true, and_assoc] using h
  complete := fun s h => by
    simpa [verifyLexerCommentGuard, Bool.and_eq_true, and_assoc] using h
  posWitness := ⟨false, false, true, 1, 64⟩
  negWitness := ⟨true, false, true, 1, 64⟩
  nonVacuous := rfl
  tight := rfl

theorem lexer_string_or_escape_blocks_comment (s : LexerCommentState)
    (h_block : s.inString = true ∨ s.isEscaped = true ∨
      s.twoBytesAvail = false ∨ ¬ (s.blockDepth < s.maxDepth)) :
    verifyLexerCommentGuard s.inString s.isEscaped s.twoBytesAvail s.blockDepth s.maxDepth = false :=
  lexerCommentGuardMetaSpec.rejects_unsafe s (by rcases h_block with h | h | h | h <;> simp [h])

structure FarkasStepState where
  objCoeff   : UInt64
  colSum     : UInt64
  accCost    : UInt64
  weightCost : UInt64
  bound      : UInt64
  deriving Repr, DecidableEq, BEq

def farkasBoundedStepMetaSpec : MetaGateSpec FarkasStepState
    (fun s => s.objCoeff ≤ s.colSum ∧ s.accCost ≤ s.bound ∧ s.weightCost ≤ s.bound - s.accCost) where
  gate := fun s =>
    verifyFarkasBoundedStep s.objCoeff s.colSum s.accCost s.weightCost s.bound
  sound := fun s h => by
    simpa [verifyFarkasBoundedStep, Bool.and_eq_true, and_assoc] using h
  complete := fun s h => by
    simpa [verifyFarkasBoundedStep, Bool.and_eq_true, and_assoc] using h
  posWitness := ⟨5, 6, 20, 15, 35⟩
  negWitness := ⟨5, 6, 20, 16, 35⟩
  nonVacuous := rfl
  tight := rfl

theorem farkas_step_overflow_or_deficit_rejected (s : FarkasStepState)
    (h_bad : ¬ (s.objCoeff ≤ s.colSum) ∨ ¬ (s.accCost ≤ s.bound) ∨
      ¬ (s.weightCost ≤ s.bound - s.accCost)) :
    verifyFarkasBoundedStep s.objCoeff s.colSum s.accCost s.weightCost s.bound = false :=
  farkasBoundedStepMetaSpec.rejects_unsafe s (by rcases h_bad with h | h | h <;> simp [h])

structure IdentBloomState where
  isExcludedCore : Bool
  candMask       : UInt64
  contextMask    : UInt64
  deriving Repr, DecidableEq, BEq

def identBloomMatchMetaSpec : MetaGateSpec IdentBloomState
    (fun s => s.isExcludedCore = false ∧ s.candMask ≠ 0 ∧
      (s.contextMask = 0 ∨ (s.candMask &&& s.contextMask) ≠ 0)) where
  gate := fun s =>
    verifyIdentBloomMatch s.isExcludedCore s.candMask s.contextMask
  sound := fun s h => by
    simpa [verifyIdentBloomMatch, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq, and_assoc] using h
  complete := fun s h => by
    simpa [verifyIdentBloomMatch, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq, and_assoc] using h
  posWitness := ⟨false, 0x101, 0x301⟩
  negWitness := ⟨false, 0x100, 0x003⟩
  nonVacuous := rfl
  tight := rfl

theorem ident_bloom_disjoint_or_excluded_rejected (s : IdentBloomState)
    (h_disj : s.isExcludedCore = true ∨ s.candMask = 0 ∨
      (s.contextMask ≠ 0 ∧ (s.candMask &&& s.contextMask) = 0)) :
    verifyIdentBloomMatch s.isExcludedCore s.candMask s.contextMask = false :=
  identBloomMatchMetaSpec.rejects_unsafe s (by
    rcases h_disj with h | h | ⟨hctx, hand⟩
    · simp [h]
    · simp [h]
    · simp [hctx, hand])

end TurboLean.Spec
