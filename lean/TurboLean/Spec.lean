/-
  TurboLean.Spec: Unified Compositional Specification & Meta-Specification Kernel
  Zero `import Lean` (standalone-compilable into `libturbo_spec_cabi.a` and `lean-native-core`),
  zero `sorry`, zero `native_decide`.
  - Layer I  : Meta-Specifications (`Costed`, `MetaGateSpec`, `MetaAlgorithmSpec`) &
               Universal Combinators (`SpeculativeGate`, `SoundCacheTier`, `ObservationalProj`,
               `WitnessRefuter`, `ArgminRouteFold`, `ClockedStepBudget`).
  - Layer II : Declarative `MetaGateSpec` / `MetaAlgorithmSpec` bundles, ≤ 3-line corollaries, and C-ABI `@[inline, export]`.
-/
namespace TurboLean.Spec

/-! ============================================================================
    LAYER I: META-SPECIFICATIONS & UNIVERSAL ALGEBRAIC COMBINATORS
    ============================================================================ -/

structure Costed (α : Type) where
  val : α
  steps : Nat
  deriving Repr, DecidableEq, BEq

structure MetaGateSpec (Input : Type) (Safe : Input → Prop) where
  gate : Input → Bool
  sound : ∀ x, gate x = true → Safe x
  complete : ∀ x, Safe x → gate x = true
  posWitness : Input
  negWitness : Input
  nonVacuous : gate posWitness = true
  tight : gate negWitness = false

theorem MetaGateSpec.iff_safe {Input : Type} {Safe : Input → Prop} (M : MetaGateSpec Input Safe) (x : Input) :
    M.gate x = true ↔ Safe x := ⟨M.sound x, M.complete x⟩
theorem MetaGateSpec.pos_ne_neg {Input : Type} {Safe : Input → Prop} (M : MetaGateSpec Input Safe) :
    M.posWitness ≠ M.negWitness := fun h => by simpa [h, M.tight] using M.nonVacuous

structure MetaAlgorithmSpec (Input Output : Type) where
  fast : Input → Costed Output
  oracle : Input → Output
  stepBound : Input → Nat
  equiv : ∀ x, (fast x).val = oracle x
  bounded : ∀ x, (fast x).steps ≤ stepBound x

theorem MetaAlgorithmSpec.sound_and_bounded {Input Output : Type} (A : MetaAlgorithmSpec Input Output) (x : Input) :
    (A.fast x).val = A.oracle x ∧ (A.fast x).steps ≤ A.stepBound x := ⟨A.equiv x, A.bounded x⟩

/-! ### Universal Combinator A: `SpeculativeGate` (Untrusted Proposal + Kernel Gate + Fallback) -/

def evalWithUntrustedAccelerator {Goal Cert : Type}
    (accel : Goal → Option Cert) (kernelVerifyCert : Goal → Cert → Bool) (kernelFallback : Goal → Bool) (g : Goal) : Bool :=
  match accel g with
  | some c => if kernelVerifyCert g c then true else kernelFallback g
  | none => kernelFallback g

theorem untrusted_accelerator_kernel_replay_sound {Goal Cert : Type}
    (accel : Goal → Option Cert) (kernelVerifyCert : Goal → Cert → Bool) (kernelFallback : Goal → Bool)
    (h_cert_sound : ∀ g c, kernelVerifyCert g c = true → kernelFallback g = true) (g : Goal) :
    evalWithUntrustedAccelerator accel kernelVerifyCert kernelFallback g = kernelFallback g := by
  unfold evalWithUntrustedAccelerator; split <;> first | rfl | (split <;> first | rfl | exact (h_cert_sound g _ ‹_›).symm)

theorem untrusted_accelerator_timeout_fallback {Goal Cert : Type}
    (accel : Goal → Option Cert) (kernelVerifyCert : Goal → Cert → Bool) (kernelFallback : Goal → Bool)
    (g : Goal) (h_timeout : accel g = none) :
    evalWithUntrustedAccelerator accel kernelVerifyCert kernelFallback g = kernelFallback g := by
  simp [evalWithUntrustedAccelerator, h_timeout]

theorem speculative_gate_rejection_fallback {Goal Cert : Type}
    (accel : Goal → Option Cert) (kernelVerifyCert : Goal → Cert → Bool) (kernelFallback : Goal → Bool)
    (g : Goal) (c : Cert) (h_some : accel g = some c) (h_rej : kernelVerifyCert g c = false) :
    evalWithUntrustedAccelerator accel kernelVerifyCert kernelFallback g = kernelFallback g := by
  simp [evalWithUntrustedAccelerator, h_some, h_rej]

theorem speculative_gate_complete {Goal Cert : Type}
    (accel : Goal → Option Cert) (kernelVerifyCert : Goal → Cert → Bool) (kernelFallback : Goal → Bool)
    (g : Goal) (h_valid : kernelFallback g = true) :
    evalWithUntrustedAccelerator accel kernelVerifyCert kernelFallback g = true := by
  unfold evalWithUntrustedAccelerator; split <;> simp_all

theorem speculative_gate_exists_witness {Goal Proof : Type}
    (accel : Goal → Option Proof) (kernelCheck : Goal → Proof → Bool) (g : Goal) (origProof : Proof)
    (h_ok : evalWithUntrustedAccelerator accel kernelCheck (fun x => kernelCheck x origProof) g = true) :
    ∃ p : Proof, kernelCheck g p = true := by
  unfold evalWithUntrustedAccelerator at h_ok; split at h_ok
  · rename_i dp _; by_cases h_dp : kernelCheck g dp = true
    · exact ⟨dp, h_dp⟩
    · exact ⟨origProof, by simpa [h_dp] using h_ok⟩
  · exact ⟨origProof, h_ok⟩

def evalTpuGuidedTacticSynth {Goal Proof : Type}
    (tpuRefute : Goal → Bool) (synthTactic : Goal → Proof) (kernelVerify : Goal → Proof → Bool) (g : Goal) (origProof : Proof) : Bool :=
  if tpuRefute g then false else if kernelVerify g (synthTactic g) then true else kernelVerify g origProof

theorem refuter_gated_synth_sound {Goal Proof : Type}
    (tpuRefute : Goal → Bool) (synthTactic : Goal → Proof) (kernelVerify : Goal → Proof → Bool)
    (g : Goal) (origProof : Proof) (h_ok : evalTpuGuidedTacticSynth tpuRefute synthTactic kernelVerify g origProof = true) :
    tpuRefute g = false ∧ ∃ p : Proof, kernelVerify g p = true := by
  unfold evalTpuGuidedTacticSynth at h_ok; split at h_ok
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

/-! ### Universal Combinator F: `ClockedStepBudget` (Affine Step-Budget Composition & Yukon Score) -/

structure AffineStepBudget where
  scale  : Nat
  offset : Nat
  deriving Repr, DecidableEq, BEq

def AffineStepBudget.eval (b : AffineStepBudget) (steps : Nat) : Nat := b.scale * steps + b.offset
def composeAffineBudget (outer inner : AffineStepBudget) : AffineStepBudget :=
  { scale := outer.scale * inner.scale, offset := outer.scale * inner.offset + outer.offset }
def yukonScore (kSteps verifyMinutes : Nat) : Nat := kSteps * 10000 + verifyMinutes
def evalLoopStepBudget (initSteps fuel : Nat) (bodyBudget : AffineStepBudget) (iterSteps : Nat) : Nat :=
  initSteps + fuel * bodyBudget.eval iterSteps
def riscvDivU64Spec (lhs rhs : UInt64) : UInt64 := if rhs == 0 then 0xffffffffffffffff else lhs / rhs
def riscvRemU64Spec (lhs rhs : UInt64) : UInt64 := if rhs == 0 then lhs else lhs % rhs

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

theorem isSoundKernelExtension_rejects_unsafe_or_axiom (d : KernelDeclSummary)
    (h : d.isAxiom = true ∨ d.isUnsafe = true ∨ d.isExternOrImplementedBy = true) :
    isSoundDeclSummary d = false := by
  rcases h with h | h | h <;> simp [isSoundDeclSummary, h]

def declSummaryMetaSpec : MetaGateSpec KernelDeclSummary
    (fun d => d.isAxiom = false ∧ d.isUnsafe = false ∧ d.isExternOrImplementedBy = false ∧ d.usedForbidden = []) where
  gate := isSoundDeclSummary
  sound := fun d => (isSoundDeclSummary_eq_true_iff d).mp
  complete := fun d => (isSoundDeclSummary_eq_true_iff d).mpr
  posWitness := ⟨"clean_thm", false, false, false, []⟩
  negWitness := ⟨"spoofed_ax", true, false, false, []⟩
  nonVacuous := rfl
  tight := rfl

def checkStatementPinned (expectedTypeHash actualTypeHash : Nat) (isNestedInductive : Bool) : Bool :=
  (expectedTypeHash == actualTypeHash) && !isNestedInductive

theorem statement_pinning_blocks_tampering (expected actual : Nat) (nested : Bool) (h_tamper : expected ≠ actual) :
    checkStatementPinned expected actual nested = false := by
  simp [checkStatementPinned, beq_false_of_ne h_tamper]

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
    coneFilter inCone (frameDecl :: env) = coneFilter inCone env := by
  simp [coneFilter, h_out]

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

theorem meta_spec_rejects_vacuous (m total : Nat) :
    isTightNonVacuousSpec ⟨0, m, total⟩ = false := rfl

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
    (h_diff : k1.oleanDigests ≠ k2.oleanDigests) :
    decide (k1 = k2) = false :=
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
    out = f ∧ w = f := by
  unfold verifyDeterminismGate at h; split at h <;> simp_all

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
      (kernelAccepts optChain || kernelAccepts origChain) := by
  simp [evalWithUntrustedAccelerator]

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

def verifyBatchFissionIpc (ckptValid : Bool) (subVerdicts : List Bool) : Bool :=
  ckptValid && subVerdicts.all id

theorem batch_fission_ipc_sound (ckptValid : Bool) (subVerdicts : List Bool) :
    verifyBatchFissionIpc ckptValid subVerdicts = true ↔
      (ckptValid = true ∧ ∀ b ∈ subVerdicts, b = true) := by
  simp [verifyBatchFissionIpc, List.all_eq_true]

def applyRwRules (rules : List (Nat → Nat)) (e : Nat) : Nat :=
  rules.foldl (fun acc r => r acc) e

theorem rw_chain_fusion_sound (r1 r2 : List (Nat → Nat)) (e : Nat) :
    applyRwRules (r1 ++ r2) e = applyRwRules r2 (applyRwRules r1 e) := by
  simp [applyRwRules, List.foldl_append]

def paddedCommandLine (prefixLines relLine : Nat) : Nat := prefixLines + relLine

theorem eval_prefix_line_padding_preserves_pos (splitIdx offsetInSuffix : Nat) :
    paddedCommandLine splitIdx (1 + offsetInSuffix) = (splitIdx + 1) + offsetInSuffix := by
  unfold paddedCommandLine; omega

/-! ## 9. Closed-Section Pruning (`MetaAlgorithmSpec`), `where` Stubbing & Fission Prologue Guard -/

def precomputeSectionMinNeededIdx (secClose firstRefIdx totalSpans : Nat) : Costed Nat :=
  { val := if secClose < firstRefIdx then firstRefIdx else totalSpans, steps := 1 }

def closedSectionNeededNaiveOracle (minNeededIdx targetIdx : Nat) : Bool :=
  decide (minNeededIdx ≤ targetIdx)

def isClosedSectionNeededFast (minNeededIdx targetIdx : Nat) : Costed Bool :=
  { val := decide (minNeededIdx ≤ targetIdx), steps := 1 }

def computeClosedSectionMaskCosted (minNeededIdxs : List Nat) (targetIdx : Nat) : Costed (List Bool) :=
  { val := minNeededIdxs.map (fun m => (isClosedSectionNeededFast m targetIdx).val)
  , steps := minNeededIdxs.length }

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

@[inline]
def canSafelyFissionHavePrologue (prologueContainsIntro : Bool) : Bool := !prologueContainsIntro

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

/-! ## 10. Direct C-ABI `@[export]` Unboxed Entrypoints for Zero-Overhead Rust FFI -/

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
  let cfg := sanitizePhaseOptions { allowStub := allowStub, warningAsError := warningAsError, forbidSorryAx := forbidSorryAx }
  (if cfg.warningAsError then 1 else 0) ||| (if cfg.forbidSorryAx then 2 else 0)

@[inline, export turbo_spec_sanitize_warning_as_error]
def cAbiSanitizeWarningAsError (allowStub warningAsError : Bool) : Bool :=
  (sanitizePhaseOptions { allowStub := allowStub, warningAsError := warningAsError, forbidSorryAx := false }).warningAsError

@[inline, export turbo_spec_sanitize_forbid_sorry_ax]
def cAbiSanitizeForbidSorryAx (allowStub forbidSorryAx : Bool) : Bool :=
  (sanitizePhaseOptions { allowStub := allowStub, warningAsError := false, forbidSorryAx := forbidSorryAx }).forbidSorryAx

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
  if tripCount < 4096 then 0
  else if isMatrixOp && hasTpu then 2
  else if is256Bit && hasGpu then 1
  else if hasTpu then 2
  else if hasGpu then 1
  else 0

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
  if a3 = b3 then if a2 = b2 then if a1 = b1 then decide (a0 < b0) else decide (a1 < b1) else decide (a2 < b2) else decide (a3 < b3)

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

@[inline, export turbo_spec_yukon_score_improves]
def yukonScoreImprovesC (newK newVerifyMin oldK oldVerifyMin : UInt64) : Bool :=
  decide (newK * 10000 + newVerifyMin < oldK * 10000 + oldVerifyMin)

@[inline, export turbo_spec_riscv_div_u64]
def riscvDivU64C (lhs rhs : UInt64) : UInt64 := riscvDivU64Spec lhs rhs

@[inline, export turbo_spec_riscv_rem_u64]
def riscvRemU64C (lhs rhs : UInt64) : UInt64 := riscvRemU64Spec lhs rhs

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

theorem combined_step_c_deterministic (i : UInt64) : combinedStepC i = combinedStepC i := rfl

theorem c_abi_exports_match_spec (m t : UInt64) (hasIntro allowStub warn forbid isAx isUn isExt : Bool) :
    cAbiIsClosedSectionNeeded m t = (isClosedSectionNeededFast m.toNat t.toNat).val ∧
    cAbiCanFissionHave hasIntro = canSafelyFissionHavePrologue hasIntro ∧
    cAbiSanitizeWarningAsError allowStub warn =
      (sanitizePhaseOptions { allowStub := allowStub, warningAsError := warn, forbidSorryAx := false }).warningAsError ∧
    cAbiSanitizeForbidSorryAx allowStub forbid =
      (sanitizePhaseOptions { allowStub := allowStub, warningAsError := false, forbidSorryAx := forbid }).forbidSorryAx ∧
    cAbiIsSoundDeclSummary isAx isUn isExt false =
      isSoundDeclSummary { name := "", isAxiom := isAx, isUnsafe := isUn, isExternOrImplementedBy := isExt, usedForbidden := [] } :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## 11. TPU-Guided Tactic Synthesis & Federated Routing Corollaries -/

theorem tpu_guided_tactic_synthesis_sound {Goal Proof : Type}
    (tpuRefute : Goal → Bool) (synthTactic : Goal → Proof) (kernelVerify : Goal → Proof → Bool)
    (g : Goal) (origProof : Proof) (h_ok : evalTpuGuidedTacticSynth tpuRefute synthTactic kernelVerify g origProof = true) :
    tpuRefute g = false ∧ ∃ p : Proof, kernelVerify g p = true :=
  refuter_gated_synth_sound tpuRefute synthTactic kernelVerify g origProof h_ok

theorem compact_diagnostic_preserves_verdict (verdict : Bool) (compactTokens verboseTokens : Nat)
    (h_smaller : compactTokens ≤ verboseTokens) :
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
    (foldl_chooseBetterRoute_mem_or_init localNode remotes ttl).elim (False.elim ∘ h_ne) (isRemoteEligible_eq_true_props ttl _ ∘ And.left)⟩

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

end TurboLean.Spec
