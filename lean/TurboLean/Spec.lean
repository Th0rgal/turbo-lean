/-
  TurboLean.Spec: Unified Executable High-Level Formal Specification
  Zero `import Lean` (links zero compiler frontend; standalone-compilable by `lean-native-core`),
  zero `sorry`, zero `native_decide`.

  Formalizes and proves the 6 foundational high-level abstractions of `turbo-lean`:
  1. Executable Kernel Extension Gate (`isSoundKernelExtension`, `checkStatementPinned`)
  2. Law 1 — Observational Proof-Irrelevance Quotient (`declInterfaceProj`, `envInterfaceProj`)
  3. Law 2 — Dependency Cone Frame Rule (`coneFilter` & Separation Locality)
  4. Law 3 — Multi-Tier Cache Pipeline Refinement (`queryTier`, `two_tier_cache_refinement`)
  5. Law 4 — Sub-Proof Cut-Fission & Out-of-Core Disk Checkpoint Soundness (`have_fission_cut_sound`)
  6. Law 5 — Meta-Specification Non-Vacuity & Tightness Gate (`meta_spec_non_vacuous_tightness`)
-/
namespace TurboLean.Spec

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

def checkStatementPinned (expectedTypeHash actualTypeHash : Nat) (isNestedInductive : Bool) : Bool :=
  (expectedTypeHash == actualTypeHash) && !isNestedInductive

theorem statement_pinning_blocks_tampering (expected actual : Nat) (nested : Bool)
    (h_tamper : expected ≠ actual) :
    checkStatementPinned expected actual nested = false := by
  dsimp only [checkStatementPinned]
  have h_beq : (expected == actual) = false := beq_false_of_ne h_tamper
  rw [h_beq, Bool.false_and]

theorem sea_monster_gate_rejects_nested (expected actual : Nat) :
    checkStatementPinned expected actual true = false := by
  dsimp only [checkStatementPinned]
  rw [Bool.not_true, Bool.and_false]

/-! ## 2. Law 1 — Observational Proof-Irrelevance Quotient (`interfaceProj`) -/

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
      verifyFromInterface (envInterfaceProj env2) target := by
  rw [h_quot]

/-! ## 3. Law 2 — Dependency Cone Frame Rule (`coneProject` & Separation Locality) -/

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
      verifyFromCone (coneFilter inCone env) target := by
  rw [cone_frame_drop_outside inCone frameDecl env h_out]

/-! ## 4. Law 3 — Multi-Tier Cache Pipeline Refinement (`cacheTierCompose`) -/

def queryTier (cache : Nat → Option Bool) (fallback : Nat → Bool) (k : Nat) : Bool :=
  match cache k with
  | some v => v
  | none => fallback k

theorem two_tier_cache_refinement (shmCache sqliteCache : Nat → Option Bool) (oracle : Nat → Bool)
    (h_shm : ∀ k v, shmCache k = some v → v = oracle k)
    (h_sql : ∀ k v, sqliteCache k = some v → v = oracle k)
    (k : Nat) :
    queryTier shmCache (queryTier sqliteCache oracle) k = oracle k := by
  dsimp only [queryTier]
  cases h1 : shmCache k with
  | some v => exact h_shm k v h1
  | none =>
    cases h2 : sqliteCache k with
    | some v => exact h_sql k v h2
    | none => rfl

/-! ## 5. Law 4 — Sub-Proof Cut-Fission & Out-of-Core Disk Checkpoint Soundness (`have_fission_cut_sound`) -/

def verifyStepOutOfCore (diskCache : Nat → Option Bool) (kernelStepClean : Nat → Bool) (g : Nat) : Bool :=
  match diskCache g with
  | some v => v
  | none => kernelStepClean g

def verifyFissionedTheorem (diskCache : Nat → Option Bool) (kernelStepClean : Nat → Bool) (subGoals : List Nat) : Bool :=
  subGoals.all (verifyStepOutOfCore diskCache kernelStepClean)

theorem out_of_core_step_eq_kernel (diskCache : Nat → Option Bool) (kernelStepClean : Nat → Bool)
    (h_disk : ∀ g v, diskCache g = some v → v = kernelStepClean g) (g : Nat) :
    verifyStepOutOfCore diskCache kernelStepClean g = kernelStepClean g := by
  dsimp only [verifyStepOutOfCore]
  cases h : diskCache g with
  | some v => exact h_disk g v h
  | none => rfl

theorem have_fission_cut_sound (diskCache : Nat → Option Bool) (kernelStepClean : Nat → Bool)
    (h_disk : ∀ g v, diskCache g = some v → v = kernelStepClean g) (subGoals : List Nat) :
    verifyFissionedTheorem diskCache kernelStepClean subGoals = subGoals.all kernelStepClean := by
  dsimp only [verifyFissionedTheorem]
  induction subGoals with
  | nil => rfl
  | cons hd tl ih =>
    dsimp only [List.all]
    rw [out_of_core_step_eq_kernel diskCache kernelStepClean h_disk hd, ih]

/-! ## 6. Law 5 — Meta-Specification Non-Vacuity & Tightness Gate (`meta_spec_non_vacuous_tightness`) -/

structure SpecAuditVerdict where
  satisfiedPreconditions : Nat
  mutantsKilled : Nat
  totalMutants : Nat
  deriving Repr, DecidableEq, BEq

def isTightNonVacuousSpec (v : SpecAuditVerdict) : Bool :=
  decide (v.satisfiedPreconditions > 0) && decide (v.totalMutants > 0) && decide (v.mutantsKilled == v.totalMutants)

theorem meta_spec_rejects_vacuous (m total : Nat) :
    isTightNonVacuousSpec ⟨0, m, total⟩ = false := by
  rfl

theorem meta_spec_non_vacuous_tightness (v : SpecAuditVerdict) :
    isTightNonVacuousSpec v = true ↔
      (v.satisfiedPreconditions > 0 ∧ v.totalMutants > 0 ∧ v.mutantsKilled = v.totalMutants) := by
  rcases v with ⟨sat, killed, total⟩
  dsimp only [isTightNonVacuousSpec]
  simp [Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-! ## 7. Law 6 — Imported `.olean` Digest Invalidation & Deterministic Eval Equivalence -/

structure FullShardKey where
  toolchain : String
  oleanDigests : List Nat
  coneHash : Nat
  stmtHash : Nat
  proofHash : Nat
  deriving Repr, DecidableEq

theorem imported_olean_mutation_invalidates_key (k1 k2 : FullShardKey)
    (h_diff : k1.oleanDigests ≠ k2.oleanDigests) :
    decide (k1 = k2) = false := by
  refine decide_eq_false (fun h_eq => h_diff ?_)
  rw [h_eq]

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

/-! ## 8. Law 6b — Untrusted Accelerator / Verified Kernel Replay Soundness -/

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

/-- Law 6a (Zero False Positives under Arbitrary / Malicious Accelerators):
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
  cases h_acc : accel g with
  | none => rfl
  | some c =>
    dsimp only
    cases h_kv : kernelVerifyCert g c with
    | false => rfl
    | true => exact (h_cert_sound g c h_kv).symm

/-- Law 6b (Transparent Fallback on Accelerator Timeout or Rejection):
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

/-! ## 9. Law 7 — Multi-Agent Worktree Lease & Supersession GC Safety -/

structure WorktreeLeaseState where
  worktreeId : String
  isActive : Bool
  activeBlobs : List Nat
  deriving Repr, DecidableEq, BEq

/-- A blob `b` is protected from Supersession GC iff it is in `pinnedHead` OR in `activeBlobs` of an active worktree lease. -/
def isBlobProtectedByLeases (pinnedHead : List Nat) (leases : List WorktreeLeaseState) (b : Nat) : Bool :=
  pinnedHead.contains b || leases.any (fun w => w.isActive && w.activeBlobs.contains b)

def canEvictSupersededBlob (pinnedHead : List Nat) (leases : List WorktreeLeaseState) (b : Nat) : Bool :=
  !isBlobProtectedByLeases pinnedHead leases b

/-- Law 7a: Any blob pinned by HEAD is never evicted by Supersession GC. -/
theorem head_pinned_blob_never_evicted (pinnedHead : List Nat) (leases : List WorktreeLeaseState) (b : Nat)
    (h_pin : pinnedHead.contains b = true) :
    canEvictSupersededBlob pinnedHead leases b = false := by
  unfold canEvictSupersededBlob isBlobProtectedByLeases
  rw [h_pin, Bool.true_or, Bool.not_true]

/-- Law 7b: If any active worktree lease protects blob `b`, Supersession GC cannot evict `b`. -/
theorem active_worktree_lease_protects_blob (pinnedHead : List Nat) (leases : List WorktreeLeaseState) (b : Nat)
    (h_active : leases.any (fun w => w.isActive && w.activeBlobs.contains b) = true) :
    canEvictSupersededBlob pinnedHead leases b = false := by
  unfold canEvictSupersededBlob isBlobProtectedByLeases
  rw [h_active, Bool.or_true, Bool.not_true]

/-! ## 10. Law 8 — Closed-Loop Proof Distillation & Fast-Reject Soundness -/

/-- Replay a distilled proof candidate `distilledProof?` through `kernelCheck`;
    if `distilledProof? = some p` and `kernelCheck g p = true`, accept `true` and cache `p`;
    otherwise fall back to elaborating the original `origProof` via `kernelCheck g origProof`. -/
def verifyWithDistilledReplay {Goal Proof : Type}
    (kernelCheck : Goal → Proof → Bool)
    (g : Goal)
    (origProof : Proof)
    (distilledProof? : Option Proof) : Bool :=
  match distilledProof? with
  | some p => if kernelCheck g p then true else kernelCheck g origProof
  | none => kernelCheck g origProof

/-- Law 8a (Zero False Positives from Distilled Proof Replay):
    If `verifyWithDistilledReplay` returns `true`, then there exists a valid proof `p` (either `distilledProof` or `origProof`)
    such that `kernelCheck g p = true` (by Proof Irrelevance, any kernel-accepted proof of `g` establishes `g`). -/
theorem distilled_certificate_replay_sound {Goal Proof : Type}
    (kernelCheck : Goal → Proof → Bool)
    (g : Goal)
    (origProof : Proof)
    (distilledProof? : Option Proof)
    (h_ok : verifyWithDistilledReplay kernelCheck g origProof distilledProof? = true) :
    ∃ p : Proof, kernelCheck g p = true := by
  unfold verifyWithDistilledReplay at h_ok
  cases distilledProof? with
  | none => exact ⟨origProof, h_ok⟩
  | some dp =>
    dsimp only at h_ok
    cases h_dp : kernelCheck g dp with
    | true => exact ⟨dp, h_dp⟩
    | false =>
      rw [h_dp] at h_ok
      exact ⟨origProof, h_ok⟩

/-- Law 8b (Completeness / Zero False Rejections on Stale Distilled Hints):
    Whenever the original proof is valid (`kernelCheck g origProof = true`),
    `verifyWithDistilledReplay` is guaranteed to return `true` even if `distilledProof?` is stale or rejected! -/
theorem distilled_certificate_stale_hint_complete {Goal Proof : Type}
    (kernelCheck : Goal → Proof → Bool)
    (g : Goal)
    (origProof : Proof)
    (distilledProof? : Option Proof)
    (h_orig : kernelCheck g origProof = true) :
    verifyWithDistilledReplay kernelCheck g origProof distilledProof? = true := by
  unfold verifyWithDistilledReplay
  cases distilledProof? with
  | none => exact h_orig
  | some dp =>
    dsimp only
    cases kernelCheck g dp with
    | true => rfl
    | false => exact h_orig

/-- Law 8c (SIMD Omega Counterexample Fast-Reject Soundness):
    If a finite witness assignment `w : Witness` satisfies all hypotheses (`evalHyps w = true`)
    and falsifies the conclusion (`evalConcl w = false`), then the universal arithmetic goal
    cannot hold (`¬ (∀ x : Witness, evalHyps x = true → evalConcl x = true)`). -/
theorem simd_omega_counterexample_sound {Witness : Type}
    (evalHyps evalConcl : Witness → Bool)
    (w : Witness)
    (h_hyps : evalHyps w = true)
    (h_concl : evalConcl w = false) :
    ¬ (∀ x : Witness, evalHyps x = true → evalConcl x = true) := by
  intro h_all
  have h_w := h_all w h_hyps
  rw [h_concl] at h_w
  contradiction

/-! ## 11. Law 9 — Discrimination-Tree Pruning & BitVec Boundary Counterexample Soundness -/

/-- Replay a pruned `simp only [explicitLemmas]` candidate through the kernel gate;
    if `verifyPrunedSimpOnly explicitLemmas = true`, accept `true`;
    otherwise fall back transparently to `fullSimpOracle`. -/
def replayPrunedSimpOnly
    (verifyPrunedSimpOnly : List String → Bool)
    (fullSimpOracle : Bool)
    (explicitLemmas : List String) : Bool :=
  if verifyPrunedSimpOnly explicitLemmas then true else fullSimpOracle

/-- Law 9a (Discrimination-Tree Pruned `simp only` Soundness):
    If `KernelGate` only accepts valid `simp only` proofs (`∀ ls, verifyPrunedSimpOnly ls = true → fullSimpOracle = true`),
    then `replayPrunedSimpOnly` is observationally equivalent to `fullSimpOracle`. -/
theorem discr_tree_pruned_simp_only_sound
    (verifyPrunedSimpOnly : List String → Bool)
    (fullSimpOracle : Bool)
    (explicitLemmas : List String)
    (h_sound : ∀ ls, verifyPrunedSimpOnly ls = true → fullSimpOracle = true) :
    replayPrunedSimpOnly verifyPrunedSimpOnly fullSimpOracle explicitLemmas = fullSimpOracle := by
  unfold replayPrunedSimpOnly
  cases h_vp : verifyPrunedSimpOnly explicitLemmas with
  | false => rfl
  | true => exact (h_sound explicitLemmas h_vp).symm

/-- Law 9b (Discrimination-Tree Pruned Fallback Completeness — Zero False Rejections):
    Whenever `simp only [explicitLemmas]` is insufficient (`verifyPrunedSimpOnly explicitLemmas = false`,
    e.g. because an unnamed global `@[simp]` lemma was also needed), `replayPrunedSimpOnly`
    falls back transparently to `fullSimpOracle`. -/
theorem discr_tree_pruned_fallback_complete
    (verifyPrunedSimpOnly : List String → Bool)
    (fullSimpOracle : Bool)
    (explicitLemmas : List String)
    (h_insufficient : verifyPrunedSimpOnly explicitLemmas = false) :
    replayPrunedSimpOnly verifyPrunedSimpOnly fullSimpOracle explicitLemmas = fullSimpOracle := by
  unfold replayPrunedSimpOnly
  rw [h_insufficient]
  rfl

/-- Evaluate a bit-vector equality `lhs x = rhs x` on a concrete boundary lane `w : Nat`. -/
def evalBvBoundaryLane (w : Nat) (lhs rhs : Nat → Nat) : Bool :=
  decide (lhs w == rhs w)

/-- Law 9c (BitVec Boundary Lane Counterexample Soundness):
    If `evalBvBoundaryLane w lhs rhs = false` for any boundary lane `w`,
    then the universal identity `∀ x, lhs x = rhs x` is false. -/
theorem bv_boundary_counterexample_sound
    (w : Nat) (lhs rhs : Nat → Nat)
    (h_cex : evalBvBoundaryLane w lhs rhs = false) :
    ¬ (∀ x, lhs x = rhs x) := by
  intro h_all
  unfold evalBvBoundaryLane at h_cex
  have h_eq : lhs w = rhs w := h_all w
  rw [h_eq, beq_self_eq_true] at h_cex
  contradiction

end TurboLean.Spec


