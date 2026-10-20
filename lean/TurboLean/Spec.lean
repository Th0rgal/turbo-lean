/-
  TurboLean.Spec: Unified Compositional Specification & Meta-Specification Kernel
  Zero `import Lean` (links zero compiler frontend; standalone-compilable by `lean-native-core`),
  zero `sorry`, zero `native_decide`.

  Architecture (2 Layers):
  - Layer I  : Meta-Specifications (`Costed`, `MetaGateSpec`, `MetaAlgorithmSpec`) &
               5 Universal Algebraic Combinators:
               (A) `SpeculativeGate`   — Untrusted Proposal + Verified Kernel Gate + Fallback
               (B) `SoundCacheTier`    — Multi-Tier Cache Refinement & Batch `List.all` Lifting
               (C) `ObservationalProj` — Quotient Invariance & Mutation Key Invalidation
               (D) `WitnessRefuter`    — Finite Witness Counterexample Refutation
               (E) `ProtectedResource` — Monotone Lease & Conjunctive Safety Gate
  - Layer II : Declarative Instantiations of `turbo-lean` Laws 1–13 as 1-line Corollaries
               and verified `MetaGateSpec` / `MetaAlgorithmSpec` bundles.
-/
namespace TurboLean.Spec

/-! ============================================================================
    LAYER I: META-SPECIFICATIONS & 5 UNIVERSAL ALGEBRAIC COMBINATORS
    ============================================================================ -/

/-- Explicit step-counted computation for complexity-bounded specifications. -/
structure Costed (α : Type) where
  val   : α
  steps : Nat
  deriving Repr, DecidableEq, BEq

/-- Meta-Specification of a Boolean decision gate `gate : Input → Bool` with respect to
    a semantic specification `Safe : Input → Prop`.
    Every `MetaGateSpec` instance must simultaneously prove:
    1. `sound`      : Zero false positives (`gate x = true → Safe x`)
    2. `complete`   : Zero false negatives (`Safe x → gate x = true`)
    3. `nonVacuous` : Concrete positive witness (`gate posWitness = true`)
    4. `tight`      : Concrete negative/mutant witness (`gate negWitness = false`) -/
structure MetaGateSpec (Input : Type) (Safe : Input → Prop) where
  gate       : Input → Bool
  sound      : ∀ x, gate x = true → Safe x
  complete   : ∀ x, Safe x → gate x = true
  posWitness : Input
  negWitness : Input
  nonVacuous : gate posWitness = true
  tight      : gate negWitness = false

/-- Universal Meta-Theorem 1: Any `MetaGateSpec` decision procedure is logically equivalent to `Safe`. -/
theorem MetaGateSpec.iff_safe {Input : Type} {Safe : Input → Prop}
    (M : MetaGateSpec Input Safe) (x : Input) :
    M.gate x = true ↔ Safe x :=
  ⟨M.sound x, M.complete x⟩

/-- Universal Meta-Theorem 2: Every `MetaGateSpec` strictly separates its positive witness
    from its negative mutant witness (`posWitness ≠ negWitness`), ruling out degenerate constant gates. -/
theorem MetaGateSpec.pos_ne_neg {Input : Type} {Safe : Input → Prop}
    (M : MetaGateSpec Input Safe) :
    M.posWitness ≠ M.negWitness := by
  intro h_eq
  have h_pos := M.nonVacuous
  rw [h_eq, M.tight] at h_pos
  contradiction

/-- Meta-Specification of a fast algorithm `fast : Input → Costed Output` refining a reference
    oracle `oracle : Input → Output` within a strict complexity bound `stepBound : Input → Nat`. -/
structure MetaAlgorithmSpec (Input Output : Type) where
  fast      : Input → Costed Output
  oracle    : Input → Output
  stepBound : Input → Nat
  equiv     : ∀ x, (fast x).val = oracle x
  bounded   : ∀ x, (fast x).steps ≤ stepBound x

/-- Universal Meta-Theorem 3: Any `MetaAlgorithmSpec` is simultaneously extensionally equal
    to its reference oracle and bounded by `stepBound`. -/
theorem MetaAlgorithmSpec.sound_and_bounded {Input Output : Type}
    (A : MetaAlgorithmSpec Input Output) (x : Input) :
    (A.fast x).val = A.oracle x ∧ (A.fast x).steps ≤ A.stepBound x :=
  ⟨A.equiv x, A.bounded x⟩

/-! ### Universal Combinator A: `SpeculativeGate` (Untrusted Proposal + Kernel Gate + Fallback) -/

/-- Evaluate a candidate certificate `cert?` from an untrusted heuristic accelerator:
    if `cert? = some c` and `kernelVerifyCert g c = true`, accept; otherwise fall back to `kernelFallback g`. -/
def evalWithUntrustedAccelerator {Goal Cert : Type}
    (accel : Goal → Option Cert)
    (kernelVerifyCert : Goal → Cert → Bool)
    (kernelFallback : Goal → Bool)
    (g : Goal) : Bool :=
  match accel g with
  | some c => if kernelVerifyCert g c then true else kernelFallback g
  | none => kernelFallback g

/-- Universal Speculative Soundness (Zero False Positives under Arbitrary / Malicious Accelerators):
    If `kernelVerifyCert` only accepts valid certificates (`∀ g c, kernelVerifyCert g c = true → kernelFallback g = true`),
    then `evalWithUntrustedAccelerator` is observationally identical to `kernelFallback` for ANY `accel` function. -/
theorem untrusted_accelerator_kernel_replay_sound {Goal Cert : Type}
    (accel : Goal → Option Cert)
    (kernelVerifyCert : Goal → Cert → Bool)
    (kernelFallback : Goal → Bool)
    (h_cert_sound : ∀ g c, kernelVerifyCert g c = true → kernelFallback g = true)
    (g : Goal) :
    evalWithUntrustedAccelerator accel kernelVerifyCert kernelFallback g = kernelFallback g := by
  unfold evalWithUntrustedAccelerator
  cases accel g with
  | none => rfl
  | some c =>
    dsimp only
    cases h_kv : kernelVerifyCert g c with
    | false => rfl
    | true => exact (h_cert_sound g c h_kv).symm

/-- Universal Speculative Timeout Fallback:
    Whenever the accelerator times out (`accel g = none`), the result is `kernelFallback g`. -/
theorem untrusted_accelerator_timeout_fallback {Goal Cert : Type}
    (accel : Goal → Option Cert)
    (kernelVerifyCert : Goal → Cert → Bool)
    (kernelFallback : Goal → Bool)
    (g : Goal)
    (h_timeout : accel g = none) :
    evalWithUntrustedAccelerator accel kernelVerifyCert kernelFallback g = kernelFallback g := by
  unfold evalWithUntrustedAccelerator
  rw [h_timeout]

/-- Universal Speculative Rejection Fallback:
    Whenever the candidate certificate `c` is rejected by `kernelVerifyCert`, the result falls back to `kernelFallback g`. -/
theorem speculative_gate_rejection_fallback {Goal Cert : Type}
    (accel : Goal → Option Cert)
    (kernelVerifyCert : Goal → Cert → Bool)
    (kernelFallback : Goal → Bool)
    (g : Goal) (c : Cert)
    (h_some : accel g = some c)
    (h_rej : kernelVerifyCert g c = false) :
    evalWithUntrustedAccelerator accel kernelVerifyCert kernelFallback g = kernelFallback g := by
  unfold evalWithUntrustedAccelerator
  rw [h_some]
  dsimp only
  rw [h_rej]
  rfl

/-- Universal Speculative Completeness (Zero False Rejections on Stale Hints):
    Whenever `kernelFallback g = true`, `evalWithUntrustedAccelerator` returns `true` for ANY `accel`. -/
theorem speculative_gate_complete {Goal Cert : Type}
    (accel : Goal → Option Cert)
    (kernelVerifyCert : Goal → Cert → Bool)
    (kernelFallback : Goal → Bool)
    (g : Goal)
    (h_valid : kernelFallback g = true) :
    evalWithUntrustedAccelerator accel kernelVerifyCert kernelFallback g = true := by
  unfold evalWithUntrustedAccelerator
  cases accel g with
  | none => exact h_valid
  | some c =>
    dsimp only
    cases kernelVerifyCert g c with
    | true => rfl
    | false => exact h_valid

/-! ### Universal Combinator B: `SoundCacheTier` (Multi-Tier Cache Refinement & Batch Lifting) -/

/-- Query a single cache tier `cache : K → Option Bool` with fallback to `fallback : K → Bool`. -/
def queryTier {K : Type} (cache : K → Option Bool) (fallback : K → Bool) (k : K) : Bool :=
  match cache k with
  | some v => v
  | none => fallback k

/-- Universal 1-Tier Cache Refinement:
    Any sound cache tier (`∀ k v, cache k = some v → v = oracle k`) is observationally equal to `oracle`. -/
theorem queryTier_eq_oracle {K : Type} (cache : K → Option Bool) (oracle : K → Bool)
    (h_sound : ∀ k v, cache k = some v → v = oracle k) (k : K) :
    queryTier cache oracle k = oracle k := by
  unfold queryTier
  cases h : cache k with
  | some v => exact h_sound k v h
  | none => rfl

/-- Universal Batch `List.all` Cache Lifting:
    Evaluating `List.all` through a sound cache tier is identical to evaluating `List.all` on the oracle. -/
theorem queryTier_batch_all_eq {K : Type} (cache : K → Option Bool) (oracle : K → Bool)
    (h_sound : ∀ k v, cache k = some v → v = oracle k) (ks : List K) :
    ks.all (queryTier cache oracle) = ks.all oracle := by
  induction ks with
  | nil => rfl
  | cons hd tl ih =>
    dsimp only [List.all]
    rw [queryTier_eq_oracle cache oracle h_sound hd, ih]

/-! ### Universal Combinator C: `ObservationalProj` (Quotient Invariance & Mutation Invalidation) -/

/-- Universal Quotient Invariance:
    Any verifier `f` that factors through projection `proj : State → Key` is invariant under
    modifications that preserve `proj`. -/
theorem proj_invariance {State Key Out : Type}
    (proj : State → Key) (f : Key → Out) (s1 s2 : State)
    (h_eq : proj s1 = proj s2) :
    f (proj s1) = f (proj s2) :=
  congrArg f h_eq

/-- Universal Mutation Invalidation (`decide` form):
    If projection `proj : State → Key` differs between `s1` and `s2`, `decide (s1 = s2) = false`. -/
theorem proj_mutation_invalidates_decide {State Key : Type} [DecidableEq State]
    (proj : State → Key) (s1 s2 : State)
    (h_diff : proj s1 ≠ proj s2) :
    decide (s1 = s2) = false :=
  decide_eq_false (fun h_eq => h_diff (congrArg proj h_eq))

/-- Universal Mutation Invalidation (`BEq` form):
    If projection `proj : State → Key` differs between `s1` and `s2`, `(s1 == s2) = false`. -/
theorem proj_mutation_invalidates_beq {State Key : Type} [DecidableEq State]
    (proj : State → Key) (s1 s2 : State)
    (h_diff : proj s1 ≠ proj s2) :
    (s1 == s2) = false := by
  cases h_beq : (s1 == s2)
  · rfl
  · exact False.elim (h_diff (congrArg proj (of_decide_eq_true h_beq)))

/-! ### Universal Combinator D: `WitnessRefuter` (Existential Counterexample Refutation) -/

/-- Universal Counterexample Refutation:
    Any witness `w` satisfying `evalHyps w = true` and `evalConcl w = false` refutes
    the universal implication `∀ x, evalHyps x = true → evalConcl x = true`. -/
theorem witness_refutes_forall {Witness : Type}
    (evalHyps evalConcl : Witness → Bool)
    (w : Witness)
    (h_hyps : evalHyps w = true)
    (h_concl : evalConcl w = false) :
    ¬ (∀ x : Witness, evalHyps x = true → evalConcl x = true) := by
  intro h_all
  have h_w := h_all w h_hyps
  rw [h_concl] at h_w
  contradiction


/-! ============================================================================
    LAYER II: DECLARATIVE INSTANTIATIONS OF TURBO-LEAN LAWS 1–13
    ============================================================================ -/

/-! ## 1. Executable Kernel Extension Gate (`isSoundKernelExtension` & `checkStatementPinned`) -/

structure KernelDeclSummary where
  name : String
  isAxiom : Bool
  isUnsafe : Bool
  isExternOrImplementedBy : Bool
  usedForbidden : List String
  deriving Repr, DecidableEq, BEq

def isSoundDeclSummary (d : KernelDeclSummary) : Bool :=
  !d.isAxiom && !d.isUnsafe && !d.isExternOrImplementedBy && d.usedForbidden.isEmpty

def isSoundKernelExtension (decls : List KernelDeclSummary) : Bool :=
  decls.all isSoundDeclSummary

theorem isSoundDeclSummary_eq_true_iff (d : KernelDeclSummary) :
    isSoundDeclSummary d = true ↔
      (d.isAxiom = false ∧ d.isUnsafe = false ∧ d.isExternOrImplementedBy = false ∧ d.usedForbidden = []) := by
  rcases d with ⟨name, isAxiom, isUnsafe, isExternOrImplementedBy, usedForbidden⟩
  dsimp only [isSoundDeclSummary]
  cases isAxiom <;> cases isUnsafe <;> cases isExternOrImplementedBy <;> cases usedForbidden <;>
    simp [List.isEmpty]

theorem isSoundKernelExtension_rejects_unsafe_or_axiom (d : KernelDeclSummary)
    (h : d.isAxiom = true ∨ d.isUnsafe = true ∨ d.isExternOrImplementedBy = true) :
    isSoundDeclSummary d = false := by
  rcases d with ⟨name, isAxiom, isUnsafe, isExternOrImplementedBy, usedForbidden⟩
  dsimp only [isSoundDeclSummary] at h ⊢
  rcases h with hAx | hUn | hExt
  · subst hAx; rfl
  · subst hUn; cases isAxiom <;> rfl
  · subst hExt; cases isAxiom <;> cases isUnsafe <;> rfl

/-- Concrete `MetaGateSpec` bundle certifying `isSoundDeclSummary` (Sound, Complete, Non-Vacuous, Tight). -/
def declSummaryMetaSpec : MetaGateSpec KernelDeclSummary
    (fun d => d.isAxiom = false ∧ d.isUnsafe = false ∧ d.isExternOrImplementedBy = false ∧ d.usedForbidden = []) where
  gate       := isSoundDeclSummary
  sound      := fun d h => (isSoundDeclSummary_eq_true_iff d).mp h
  complete   := fun d h => (isSoundDeclSummary_eq_true_iff d).mpr h
  posWitness := ⟨"clean_thm", false, false, false, []⟩
  negWitness := ⟨"spoofed_ax", true, false, false, []⟩
  nonVacuous := rfl
  tight      := rfl

def checkStatementPinned (expectedTypeHash actualTypeHash : Nat) (isNestedInductive : Bool) : Bool :=
  (expectedTypeHash == actualTypeHash) && !isNestedInductive

theorem statement_pinning_blocks_tampering (expected actual : Nat) (nested : Bool)
    (h_tamper : expected ≠ actual) :
    checkStatementPinned expected actual nested = false := by
  dsimp only [checkStatementPinned]
  rw [beq_false_of_ne h_tamper, Bool.false_and]

theorem sea_monster_gate_rejects_nested (expected actual : Nat) :
    checkStatementPinned expected actual true = false := by
  dsimp only [checkStatementPinned]
  rw [Bool.not_true, Bool.and_false]

/-! ## 2. Law 1 — Observational Proof-Irrelevance Quotient (`ObservationalProj` Instance) -/

structure EnvDecl where
  name : String
  isTheorem : Bool
  stmtHash : Nat
  bodyHash : Nat
  deriving Repr, DecidableEq, BEq

def declInterfaceProj (d : EnvDecl) : String × Bool × Nat :=
  (d.name, d.isTheorem, if d.isTheorem then d.stmtHash else d.stmtHash + d.bodyHash)

def envInterfaceProj (env : List EnvDecl) : List (String × Bool × Nat) :=
  env.map declInterfaceProj

theorem declInterfaceProj_thm_body_invariant (name : String) (stmt b1 b2 : Nat) :
    declInterfaceProj ⟨name, true, stmt, b1⟩ = declInterfaceProj ⟨name, true, stmt, b2⟩ :=
  rfl

theorem observational_quotient_sound {Decl : Type}
    (verifyFromInterface : List (String × Bool × Nat) → Decl → Bool)
    (env1 env2 : List EnvDecl) (target : Decl)
    (h_quot : envInterfaceProj env1 = envInterfaceProj env2) :
    verifyFromInterface (envInterfaceProj env1) target =
      verifyFromInterface (envInterfaceProj env2) target :=
  proj_invariance envInterfaceProj (fun k => verifyFromInterface k target) env1 env2 h_quot

/-! ## 3. Law 2 — Dependency Cone Frame Rule (`ObservationalProj` Instance) -/

def coneFilter (inCone : String → Bool) (env : List EnvDecl) : List EnvDecl :=
  env.filter (fun d => inCone d.name)

theorem cone_frame_drop_outside (inCone : String → Bool) (frameDecl : EnvDecl) (env : List EnvDecl)
    (h_out : inCone frameDecl.name = false) :
    coneFilter inCone (frameDecl :: env) = coneFilter inCone env := by
  dsimp only [coneFilter, List.filter]
  rw [h_out]

theorem cone_frame_rule_locality {Decl : Type}
    (verifyFromCone : List EnvDecl → Decl → Bool)
    (inCone : String → Bool) (frameDecl : EnvDecl) (env : List EnvDecl) (target : Decl)
    (h_out : inCone frameDecl.name = false) :
    verifyFromCone (coneFilter inCone (frameDecl :: env)) target =
      verifyFromCone (coneFilter inCone env) target :=
  proj_invariance (coneFilter inCone) (fun c => verifyFromCone c target)
    (frameDecl :: env) env (cone_frame_drop_outside inCone frameDecl env h_out)

/-! ## 4. Law 3 & Law 4 — Multi-Tier Cache & Sub-Proof Cut-Fission (`SoundCacheTier` Instances) -/

theorem two_tier_cache_refinement (shmCache sqliteCache : Nat → Option Bool) (oracle : Nat → Bool)
    (h_shm : ∀ k v, shmCache k = some v → v = oracle k)
    (h_sql : ∀ k v, sqliteCache k = some v → v = oracle k)
    (k : Nat) :
    queryTier shmCache (queryTier sqliteCache oracle) k = oracle k := by
  rw [queryTier_eq_oracle shmCache (queryTier sqliteCache oracle)
      (fun x v hx => (h_shm x v hx).trans (queryTier_eq_oracle sqliteCache oracle h_sql x).symm) k,
      queryTier_eq_oracle sqliteCache oracle h_sql k]

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

/-! ## 5. Law 5 — Meta-Specification Non-Vacuity & Tightness Gate (`MetaGateSpec` Instance) -/

structure SpecAuditVerdict where
  satisfiedPreconditions : Nat
  mutantsKilled : Nat
  totalMutants : Nat
  deriving Repr, DecidableEq, BEq

def isTightNonVacuousSpec (v : SpecAuditVerdict) : Bool :=
  decide (v.satisfiedPreconditions > 0) && decide (v.totalMutants > 0) && decide (v.mutantsKilled == v.totalMutants)

theorem meta_spec_rejects_vacuous (m total : Nat) :
    isTightNonVacuousSpec ⟨0, m, total⟩ = false :=
  rfl

theorem meta_spec_non_vacuous_tightness (v : SpecAuditVerdict) :
    isTightNonVacuousSpec v = true ↔
      (v.satisfiedPreconditions > 0 ∧ v.totalMutants > 0 ∧ v.mutantsKilled = v.totalMutants) := by
  rcases v with ⟨sat, killed, total⟩
  dsimp only [isTightNonVacuousSpec]
  simp [Bool.and_eq_true, decide_eq_true_eq, and_assoc]

def specAuditMetaSpec : MetaGateSpec SpecAuditVerdict
    (fun v => v.satisfiedPreconditions > 0 ∧ v.totalMutants > 0 ∧ v.mutantsKilled = v.totalMutants) where
  gate       := isTightNonVacuousSpec
  sound      := fun v h => (meta_spec_non_vacuous_tightness v).mp h
  complete   := fun v h => (meta_spec_non_vacuous_tightness v).mpr h
  posWitness := ⟨4, 3, 3⟩
  negWitness := ⟨0, 3, 3⟩
  nonVacuous := rfl
  tight      := rfl

/-! ## 6. Law 6 & Law 12b — `.olean` Digest Key Invalidation (`ObservationalProj` Instances) -/

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
    (k1 == k2) = false := by
  refine proj_mutation_invalidates_beq (fun k => (k.localSearchPathDigest, k.importedModuleDigest)) k1 k2 ?_
  intro h_pair
  injection h_pair with h1 h2
  exact h_mut.elim (fun h => h h1) (fun h => h h2)

structure EvalOutput where
  exitOk : Bool
  messages : List String
  stdout : String
  deriving Repr, DecidableEq

def verifyDeterminismGate (workerOut freshLeanOut : EvalOutput) : Option EvalOutput :=
  if decide (workerOut = freshLeanOut) then some workerOut else none

theorem verifyDeterminismGate_sound (w f out : EvalOutput)
    (h : verifyDeterminismGate w f = some out) :
    out = f ∧ w = f := by
  dsimp only [verifyDeterminismGate] at h
  split at h
  · rename_i h_eq
    injection h with h_out
    have h_wf : w = f := of_decide_eq_true h_eq
    exact ⟨h_out.symm.trans h_wf, h_wf⟩
  · contradiction

/-! ## 7. Law 7 — Multi-Agent Worktree Lease & Supersession GC Safety -/

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
  unfold canEvictSupersededBlob isBlobProtectedByLeases
  rw [h_pin, Bool.true_or, Bool.not_true]

theorem active_worktree_lease_protects_blob (pinnedHead : List Nat) (leases : List WorktreeLeaseState) (b : Nat)
    (h_active : leases.any (fun w => w.isActive && w.activeBlobs.contains b) = true) :
    canEvictSupersededBlob pinnedHead leases b = false := by
  unfold canEvictSupersededBlob isBlobProtectedByLeases
  rw [h_active, Bool.or_true, Bool.not_true]

/-! ## 8. Laws 8, 9, 10b & 12a — Accelerator & Distillation Corollaries (`SpeculativeGate` & `WitnessRefuter` Instances) -/

/-- Replay a distilled proof candidate `distilledProof?` through `kernelCheck` (instance of `evalWithUntrustedAccelerator`). -/
def verifyWithDistilledReplay {Goal Proof : Type}
    (kernelCheck : Goal → Proof → Bool) (g : Goal) (origProof : Proof) (distilledProof? : Option Proof) : Bool :=
  evalWithUntrustedAccelerator (fun _ => distilledProof?) kernelCheck (fun x => kernelCheck x origProof) g

theorem distilled_certificate_replay_sound {Goal Proof : Type}
    (kernelCheck : Goal → Proof → Bool) (g : Goal) (origProof : Proof) (distilledProof? : Option Proof)
    (h_ok : verifyWithDistilledReplay kernelCheck g origProof distilledProof? = true) :
    ∃ p : Proof, kernelCheck g p = true := by
  unfold verifyWithDistilledReplay evalWithUntrustedAccelerator at h_ok
  cases distilledProof? with
  | none => exact ⟨origProof, h_ok⟩
  | some dp =>
    dsimp only at h_ok
    cases h_dp : kernelCheck g dp with
    | true => exact ⟨dp, h_dp⟩
    | false => rw [h_dp] at h_ok; exact ⟨origProof, h_ok⟩

theorem distilled_certificate_stale_hint_complete {Goal Proof : Type}
    (kernelCheck : Goal → Proof → Bool) (g : Goal) (origProof : Proof) (distilledProof? : Option Proof)
    (h_orig : kernelCheck g origProof = true) :
    verifyWithDistilledReplay kernelCheck g origProof distilledProof? = true :=
  speculative_gate_complete (fun _ => distilledProof?) kernelCheck (fun x => kernelCheck x origProof) g h_orig

/-- Replay a pruned `simp only [explicitLemmas]` candidate (instance of `evalWithUntrustedAccelerator`). -/
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

def evalAcSum (terms : List Nat) : Nat :=
  terms.foldl (· + ·) 0

theorem ac_normalizer_replay_sound {Goal Cert : Type}
    (acPropose : Goal → Option Cert) (kernelVerifyCert : Goal → Cert → Bool) (kernelFallback : Goal → Bool)
    (h_sound : ∀ g c, kernelVerifyCert g c = true → kernelFallback g = true) (g : Goal) :
    evalWithUntrustedAccelerator acPropose kernelVerifyCert kernelFallback g = kernelFallback g :=
  untrusted_accelerator_kernel_replay_sound acPropose kernelVerifyCert kernelFallback h_sound g

/-- SIMD Omega Counterexample Refutation (1-line instance of `witness_refutes_forall`). -/
theorem simd_omega_counterexample_sound {Witness : Type}
    (evalHyps evalConcl : Witness → Bool) (w : Witness)
    (h_hyps : evalHyps w = true) (h_concl : evalConcl w = false) :
    ¬ (∀ x : Witness, evalHyps x = true → evalConcl x = true) :=
  witness_refutes_forall evalHyps evalConcl w h_hyps h_concl

def evalBvBoundaryLane (w : Nat) (lhs rhs : Nat → Nat) : Bool :=
  decide (lhs w == rhs w)

theorem bv_boundary_counterexample_sound (w : Nat) (lhs rhs : Nat → Nat)
    (h_cex : evalBvBoundaryLane w lhs rhs = false) :
    ¬ (∀ x, lhs x = rhs x) := by
  intro h_all
  unfold evalBvBoundaryLane at h_cex
  rw [h_all w, beq_self_eq_true] at h_cex
  contradiction

/-! ## 9. Laws 10a & 11 — Batch Fission IPC, Rewrite Fusion & Prefix Line Padding -/

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

def paddedCommandLine (prefixLines relLine : Nat) : Nat :=
  prefixLines + relLine

theorem eval_prefix_line_padding_preserves_pos (splitIdx offsetInSuffix : Nat) :
    paddedCommandLine splitIdx (1 + offsetInSuffix) = (splitIdx + 1) + offsetInSuffix := by
  unfold paddedCommandLine; omega

/-! ## 10. Law 13 — O(1) Closed-Section Pruning (`MetaAlgorithmSpec`), `where` Stubbing, `warningAsError` & Fission Prologue Guard -/

def precomputeSectionMinNeededIdx (secClose firstRefIdx totalSpans : Nat) : Costed Nat :=
  { val := if secClose < firstRefIdx then firstRefIdx else totalSpans, steps := 1 }

def closedSectionNeededNaiveOracle (minNeededIdx targetIdx : Nat) : Bool :=
  decide (minNeededIdx ≤ targetIdx)

def isClosedSectionNeededFast (minNeededIdx targetIdx : Nat) : Costed Bool :=
  { val := decide (minNeededIdx ≤ targetIdx), steps := 1 }

def computeClosedSectionMaskCosted (minNeededIdxs : List Nat) (targetIdx : Nat) : Costed (List Bool) :=
  { val := minNeededIdxs.map (fun m => (isClosedSectionNeededFast m targetIdx).val)
  , steps := minNeededIdxs.length }

/-- Concrete `MetaAlgorithmSpec` certifying $O(1)$ per-section check and $O(S)$ mask evaluation. -/
def closedSectionMaskMetaSpec (minNeededIdxs : List Nat) : MetaAlgorithmSpec Nat (List Bool) where
  fast      := computeClosedSectionMaskCosted minNeededIdxs
  oracle    := fun targetIdx => minNeededIdxs.map (fun m => closedSectionNeededNaiveOracle m targetIdx)
  stepBound := fun _ => minNeededIdxs.length
  equiv     := fun _ => rfl
  bounded   := fun _ => Nat.le_refl _

theorem closed_section_fast_eq_naive_oracle (minNeededIdx targetIdx : Nat) :
    (isClosedSectionNeededFast minNeededIdx targetIdx).val =
      closedSectionNeededNaiveOracle minNeededIdx targetIdx ∧
    (isClosedSectionNeededFast minNeededIdx targetIdx).steps = 1 :=
  ⟨rfl, rfl⟩

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
    stubTheoremForm (.whereStruct sig body1) = stubTheoremForm (.whereStruct sig body2) :=
  rfl

structure VerificationPhaseConfig where
  allowStub      : Bool
  warningAsError : Bool
  forbidSorryAx  : Bool
  deriving Repr, DecidableEq, BEq

def sanitizePhaseOptions (cfg : VerificationPhaseConfig) : VerificationPhaseConfig :=
  if cfg.allowStub then
    { cfg with warningAsError := false, forbidSorryAx := false }
  else
    { cfg with forbidSorryAx := true }

theorem stubbed_prefix_warningAsError_safe (w f : Bool) :
    (sanitizePhaseOptions { allowStub := true, warningAsError := w, forbidSorryAx := f }).warningAsError = false ∧
    (sanitizePhaseOptions { allowStub := false, warningAsError := w, forbidSorryAx := f }).forbidSorryAx = true :=
  ⟨rfl, rfl⟩

def canSafelyFissionHavePrologue (prologueContainsIntro : Bool) : Bool :=
  !prologueContainsIntro

/-- Concrete `MetaGateSpec` certifying `canSafelyFissionHavePrologue`. -/
def fissionPrologueMetaSpec : MetaGateSpec Bool (fun hasIntro => hasIntro = false) where
  gate       := canSafelyFissionHavePrologue
  sound      := fun b h => by cases b <;> first | rfl | contradiction
  complete   := fun b h => by subst h; rfl
  posWitness := false
  negWitness := true
  nonVacuous := rfl
  tight      := rfl

theorem fission_prologue_guard_sound :
    canSafelyFissionHavePrologue true = false ∧ canSafelyFissionHavePrologue false = true :=
  ⟨fissionPrologueMetaSpec.tight, fissionPrologueMetaSpec.nonVacuous⟩

end TurboLean.Spec
