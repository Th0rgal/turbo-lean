# AGENTS.md — Architectural Charter (`turbo-lean` [incl. `LeanNative`] ⟷ `lean-sys` ⟷ `orb`)

## 1. Symbiosis & Architectural Roles

`turbo-lean` (unifying `TurboLean` and `LeanNative`), `lean-sys`, and `orb` form a co-designed formal verification, native compilation, and systems runtime stack for Lean 4:

- **`turbo-lean` (`lean/TurboLean/` + `crates/turbo-lean/` — Incremental Verification, Zygote Elaboration & Counterexample Triage)**:
  Partitions Lean modules into topological dependency cones and sub-proof cuts, caches artifacts across content-addressed memory and persistent stores, orchestrates warm `Command.State` Zygote workers, exposes an MCP server (`turbo_fast_check`, `turbo_agent_step`, `turbo_audit_spec`, `turbo_check`, `turbo_pr_verify`, `turbo_status`) with structured counterexample triage (`CandidateBug | SpecTooStrong | ReferenceDiscrepancy`), and enforces an in-kernel soundness gate (`0 sorryAx`, `0 native_decide`, `0 trustCompiler`, statement pinning, and nested-inductive hygiene).
- **`LeanNative` (`lean/LeanNative/` — Verified `LNIR` Native Compiler, Acceleration Plugins & Hardware Fast-Check)**:
  Embedded directly in `lean/LeanNative/`. Lowers pure Lean 4 / `LNIR` (`letBind`, `incRef`, `decRef`, `call`, `parFor`, 256-bit arithmetic) via `@[simd]`, `@[gpu]`, `@[tpu]`, and `@[superopt]` plugins into verified C-ABI SIMD, LLVM IR, NVIDIA PTX, Apple Metal 3.0, and Cloud TPU v6e (`StableHLO` / `Pallas`) kernels. Certifies counterexamples (`leannative_certify_cex_witnesses`, `leannative_fastcheck_rewrite_step`) and spec non-vacuity via executable operational semantics (`evalCode`) and symbolic translation validation (`CodeRefines`) with **199 kernel-checked theorems** (`<!-- inventory:leannative_tight_specs -->106/106<!-- /inventory:leannative_tight_specs -->` tight specs in `lean/LeanNative/Spec.lean`).
- **`lean-sys` & `orb` (`Th0rgal/lean-sys` & `Th0rgal/sandboxed.sh` — Verified Systems & Orchestration Kernels)**:
  `turbo-lean` links **<!-- inventory:turbo_cabi_exports -->63<!-- /inventory:turbo_cabi_exports --> zero-runtime C-ABI symbols** (`38 turbo_spec_*` + `20 leansys_*` + `5 leannative_*`) directly into `libturbo_spec_cabi.a` (`crates/turbo-lean/src/c_abi.rs`, `owner_count == 1` verified via `nm`). `turbo-lean --json audit-spec` audits `lean/TurboLean/Spec.lean` (<!-- inventory:turbo_tight_specs -->86/86<!-- /inventory:turbo_tight_specs --> tight specs), `lean/LeanNative/Spec.lean` (<!-- inventory:leannative_tight_specs -->106/106<!-- /inventory:leannative_tight_specs --> tight specs), `LeanSys/Spec.lean` (`36/36` tight specs, `26` C-ABI exports), and `orb/lean/Orb/Spec.lean` (`24/24` tight specs, `12` C-ABI exports) for non-vacuity, tightness, and zero horizontal packing warnings.
- **Shared Layer-0 Contracts**: Consumes the universal `MetaGateSpec` and `SpeculativeGate` contracts from `LeanSys.Gate` (`LeanSys.Contracts.MetaGate` and `LeanSys.Contracts.SpeculativeGate`), enforcing non-vacuity, tightness, and zero-trust speculative execution across all verification and compilation stages.

```
Agent / CLI / MCP ──► Stage 0: Cone & CAS Filter (`TurboLean/Spec.lean` + `LeanSys` C-ABI Gates)
                  ──► Stage 1: In-Process Counterexample Triage & Hardware Fast-Check (`LeanNative/Spec.lean`)
                  ──► Stage 2: Speculative Tactic Racing & Warm Zygote Replay (`ZygoteWorker.lean`)
                  ──► Stage 3: In-Kernel Axiom & Statement Pinning Gate (`Inspector.lean` / `AxiomAudit.lean`)
```

---

## 2. Seven Non-Negotiable Engineering Rules

1. **Zero Model-Code Gap via Direct C-ABI (`@[inline, export]`)**:
   Executable decision gates, cost models, counterexample triage rules, and state transitions affecting soundness or routing live in `lean/TurboLean/Spec.lean`, `lean/TurboLean/Kernel.lean`, and `lean/LeanNative/Spec.lean` (with zero compiler-frontend dependencies) and are compiled directly to unboxed C-ABI primitives (`<!-- inventory:turbo_cabi_exports -->63<!-- /inventory:turbo_cabi_exports -->` symbols in `libturbo_spec_cabi.a`). Host runtimes call the compiled Lean specification directly instead of re-implementing shadow logic in Rust.

2. **Two-Layer Specification Compression (`Layer I` Meta-Specs vs. `Layer II` Corollaries ≤ 3 Lines)**:
   - **Layer I (Universal Meta-Specifications & Combinators)**: Structural reasoning lives in reusable algebraic combinators (`MetaGateSpec`, `MetaAlgorithmSpec`, `SpeculativeGate`, `SoundCacheTier`, `ObservationalProj`, `WitnessRefuter`, `ArgminRouteFold`, `ClockedStepBudget`), shared with `LeanSys.Contracts`.
   - **Layer II (Declarative Corollaries)**: Concrete subsystem properties are instantiated as `MetaGateSpec` / `MetaAlgorithmSpec` bundles or corollaries of **≤ 3 lines** discharging directly through Layer I combinators.

3. **Hermetic Segregation of Formal Kernel vs. Untrusted Heuristic Plugins behind `SpeculativeGate`**:
   All heuristic accelerators, tactic synthesizers, superoptimizer rewrites, and hardware backends (`@[simd]`, `@[gpu]`, `@[tpu]`, `@[superopt]`, external JSONL-stdio processes) are treated as untrusted proposals. Every proposal is gated by `SpeculativeGate` (`evalWithUntrustedAccelerator` / `evalWithUntrustedOptPlugin`) and verified by the Lean kernel or translation validator (`0 sorryAx`, `0 native_decide`), with transparent fallback to the baseline on timeout or rejection.

4. **Mathlib4 Algebraic Proof Style**:
   Proofs in `Spec.lean` and across `lean/TurboLean/` and `lean/LeanNative/` must follow concise Mathlib4 algebraic idioms (`split <;> simp_all`, `simpa`, `omega`, `iff` equivalences, and point-free combinators). Verbose `cases <;> cases` cascades and repetitive boilerplate are forbidden.

5. **LOC Reduction Ratchet**:
   Every refactoring, bug fix, or feature addition must actively compress or factor existing code and specifications. New capabilities are integrated by generalizing Layer I combinators or unified runtime traits rather than accreting ad-hoc modules or duplicating logic across repositories.

6. **Doc & Context Ratchet (`scripts/sync_docs_inventory.py`)**:
   Any commit that changes `TurboLean/Spec.lean` tight-spec counts (`<!-- inventory:turbo_tight_specs -->86/86<!-- /inventory:turbo_tight_specs -->`), `LeanNative/Spec.lean` tight-spec counts (`<!-- inventory:leannative_tight_specs -->106/106<!-- /inventory:leannative_tight_specs -->`), or C-ABI exports (`<!-- inventory:turbo_cabi_exports -->63<!-- /inventory:turbo_cabi_exports -->`) must update `README.md` and `AGENTS.md` in the same change. `./scripts/ci_verify.sh` checks those counters.

7. **End-to-End Amdahl & Ablation Ratchet (`ΔE2E >= 1%` or Delete)**:
   - **No Micro-Benchmark-Only Optimizations**: No hardware backend, cascade tier, heuristic pass, or rewrite rule lands without a measured wall-clock speedup on the end-to-end pipeline.
   - **Mandatory Ablation & Pruning**: Any optimization, cascade tier, or superopt rule with $0$ hits on the canonical corpus or whose ablation degrades E2E geomean by $< 1\%$ must be deleted to enforce $\Delta\text{LOC} \le 0$.

---

## 3. Repository Layout & Verification Entrypoints

- **Formal Specifications & C-ABI Kernels**: [`lean/TurboLean/Kernel.lean`](lean/TurboLean/Kernel.lean), [`lean/TurboLean/Spec.lean`](lean/TurboLean/Spec.lean) (`<!-- inventory:turbo_tight_specs -->86/86<!-- /inventory:turbo_tight_specs -->`), & [`lean/LeanNative/Spec.lean`](lean/LeanNative/Spec.lean) (`<!-- inventory:leannative_tight_specs -->106/106<!-- /inventory:leannative_tight_specs -->`)
- **Kernel Replay & Axiom Audit**: [`lean/TurboLean/Assembler.lean`](lean/TurboLean/Assembler.lean), [`lean/TurboLean/Inspector.lean`](lean/TurboLean/Inspector.lean), [`lean/LeanNative/Proofs/AxiomAudit.lean`](lean/LeanNative/Proofs/AxiomAudit.lean)
- **Verified Native Compiler & Acceleration Plugins**: [`lean/LeanNative/Semantics/Eval.lean`](lean/LeanNative/Semantics/Eval.lean), [`lean/LeanNative/Transform/Plugins.lean`](lean/LeanNative/Transform/Plugins.lean), [`lean/LeanNative/Transform/Superopt.lean`](lean/LeanNative/Transform/Superopt.lean), [`lean/LeanNative/Backend/`](lean/LeanNative/Backend/)
- **Warm Elaboration & C-ABI Runtime**: [`lean/TurboLean/ZygoteWorker.lean`](lean/TurboLean/ZygoteWorker.lean), [`crates/turbo-lean/src/`](crates/turbo-lean/src/)
- **CI Verification & Inventory Ratchet**: [`scripts/ci_verify.sh`](scripts/ci_verify.sh), [`scripts/sync_docs_inventory.py`](scripts/sync_docs_inventory.py)

---

## 4. Optimization Objectives & Resource Envelopes (`ObjectiveReceipt`)

1. **Layer 1 — Hard Formal Gate (`G(x) = true`)**:
   - `untrusted_accelerator_kernel_replay_sound` (every heuristic candidate replays through the Lean kernel in a prefix-truncated environment with zero target self-reference), `queryTier_eq_oracle` (`0` false-positive CAS hits), `witness_refutes_forall` (`0` false refutations), `0 sorryAx`, `0 native_decide`.
2. **Layer 2 — Lexicographic Objective (`J_turbo`)**:
   - **Primary**: Minimize agent feedback loop latency $\text{Geomean}(\text{latence\_p50}_{\text{warm}}, \text{latence\_p95}_{\text{edit}}, \text{build}_{\text{cone}})$ and deterministic verification heartbeats.
   - **Secondary**: Maximize Tier-0 (`< 10 ms`) masked proof regeneration rate and `proof_term_nodes` compression.
   - **Resource Envelope**: $\text{RSS}_{\text{peak}} \le \text{RAM}_{\text{cap}}$ and $\Delta\text{LOC} \le 0$ (simplicity ratchet).
