# AGENTS.md — Architectural Charter (`turbo-lean` ⟷ `lean-native` ⟷ `lean-sys` ⟷ `orb`)

## 1. Symbiosis & Architectural Roles

`turbo-lean`, `lean-native`, `lean-sys`, and `orb` form a co-designed formal verification and native execution stack for Lean 4:

- **`turbo-lean` (Incremental Verification, Zygote Elaboration & Federated Orchestration)**:
  Partitions Lean modules into topological dependency cones and sub-proof cuts, caches artifacts across content-addressed memory and persistent stores, orchestrates warm `Command.State` Zygote workers, exposes an MCP server for proof agents, and enforces an in-kernel soundness gate (`0 sorryAx`, `0 native_decide`, `0 trustCompiler`, statement pinning, and nested-inductive hygiene). Links `lean-sys` v0.2 C-ABI gates (`leansys_verify_slice_bounds`, `leansys_verify_wal_frame`, `leansys_verify_cas_digest`, `leansys_check_http_bounds`, `leansys_verify_jsonl_tape`, `leansys_verify_ring_cursor`, `leansys_verify_sst_block`, `leansys_verify_poll_interest`, `leansys_verify_rlimit_budget`, `leansys_verify_composite_key_order`, `leansys_verify_token_auth`, `leansys_verify_log_window`, `leansys_verify_jsonrpc_frame`, `leansys_mix64_word`, `leansys_gate_admit`, `leansys_verify_par_chunk`, `leansys_verify_arena_disjoint`) into `crates/turbo-lean/src/c_abi.rs`.
- **`lean-native` (Verified Native Codegen, Translation Validation & Hardware Fast-Check)**:
  Lowers Lean/LNIR into verified C-ABI SIMD, LLVM IR, NVIDIA PTX, Apple Metal, and Cloud TPU XLA/StableHLO kernels. Certifies counterexamples and spec non-vacuity via executable operational semantics (`evalCode`) and symbolic translation validation (`CodeRefines`) before `turbo-lean` spends elaboration compute.
- **`lean-sys` & `orb` (`LeanSys/Spec.lean`, `lean/Orb/Kernel.lean` & `lean/Orb/Spec.lean` — Verified Systems & Orchestration Kernels)**:
  `turbo-lean --json audit-spec` audits `LeanSys/Spec.lean` (31/31 tight specs + 2 in `Hash.lean` + 1 in `Gate.lean` = 33/33 tight specs, 23 C-ABI exports, plus Layer-0 `LeanSys.Gate` re-exporting `LeanSys.Contracts.MetaGate` and `LeanSys.Contracts.SpeculativeGate`), `lean/TurboLean/Spec.lean` (<!-- inventory:turbo_tight_specs -->86/86<!-- /inventory:turbo_tight_specs --> tight specs, <!-- inventory:turbo_cabi_exports -->55<!-- /inventory:turbo_cabi_exports --> C-ABI exports in `lean/TurboLean/Kernel.lean`), and `orb/lean/Orb/Spec.lean` (24/24 tight specs, 12 C-ABI exports in `orb/lean/Orb/Kernel.lean` at `2.288 ns/call`) for non-vacuity, tightness, and zero horizontal packing warnings, with zero hand-written C fallbacks in `build.rs`.
- **Shared Layer-0 Contracts**: Consumes the universal `MetaGateSpec` and `SpeculativeGate` contracts from `LeanSys.Gate` (`LeanSys.Contracts.MetaGate` and `LeanSys.Contracts.SpeculativeGate`), enforcing non-vacuity, tightness, and zero-trust speculative execution across all verification stages.

```
Agent / CLI / MCP ──► Stage 0: Cone & CAS Filter (`turbo-lean` + C-ABI `Spec.lean`)
                  ──► Stage 1: Certified Fast-Check & Vacuity Gate (`lean-native` CPU/GPU/TPU)
                  ──► Stage 2: Speculative Tactic Racing & Warm Zygote Replay (`ZygoteWorker`)
                  ──► Stage 3: In-Kernel Axiom & Statement Pinning Gate (`Inspector` / `AxiomAudit`)
```

---

## 2. Six Non-Negotiable Engineering Rules

1. **Zero Model-Code Gap via Direct C-ABI (`@[export]`)**:
   Executable decision gates, cost models, and state transitions affecting soundness or routing live in `Spec.lean` (with zero compiler-frontend dependencies) and are compiled directly to unboxed C-ABI primitives (`@[inline, export ...]`). Host runtimes call the compiled Lean specification directly instead of re-implementing shadow logic in Rust or Python.

2. **Two-Layer Specification Compression (`Layer I` Meta-Specs vs. `Layer II` Corollaries ≤ 3 Lines)**:
   - **Layer I (Universal Meta-Specifications & Combinators)**: All structural reasoning lives in reusable algebraic combinators (`MetaGateSpec`, `MetaAlgorithmSpec`, `SpeculativeGate`, `SoundCacheTier`, `ObservationalProj`, `WitnessRefuter`, `ArgminRouteFold`, `ClockedStepBudget`), shared with `LeanSys.Contracts`.
   - **Layer II (Declarative Corollaries)**: Concrete subsystem properties are instantiated as `MetaGateSpec` / `MetaAlgorithmSpec` bundles or corollaries of **≤ 3 lines** discharging directly through Layer I combinators.

3. **Hermetic Segregation of Formal Kernel vs. Untrusted Heuristic Plugins behind `SpeculativeGate`**:
   All heuristic accelerators, tactic synthesizers, superoptimizer rewrites, and hardware backends (SIMD, CUDA, Metal, TPU XLA, external JSONL-stdio processes) are treated as untrusted proposals. Every proposal is gated by `SpeculativeGate` (`evalWithUntrustedAccelerator` / `evalWithUntrustedOptPlugin`) and verified by the Lean kernel or translation validator (`0 sorryAx`, `0 native_decide`), with transparent fallback to the baseline on timeout or rejection.

4. **Mathlib4 Algebraic Proof Style**:
   Proofs in `Spec.lean` and across the proof suite must follow concise Mathlib4 algebraic idioms (`split <;> simp_all`, `simpa`, `omega`, `iff` equivalences, and point-free combinators). Verbose `cases <;> cases` cascades and repetitive boilerplate are forbidden.

5. **LOC Reduction Ratchet**:
   Every refactoring, bug fix, or feature addition must actively compress or factor existing code and specifications. New capabilities are integrated by generalizing Layer I combinators or unified runtime traits rather than accreting ad-hoc modules or duplicating logic across repositories.

6. **Doc & Context Ratchet (`--sync-docs`)**:
   Any commit that changes `TurboLean/Spec.lean` tight-spec counts (`<!-- inventory:turbo_tight_specs -->86/86<!-- /inventory:turbo_tight_specs -->` non-vacuous and tight) or C-ABI exports (`<!-- inventory:turbo_cabi_exports -->55<!-- /inventory:turbo_cabi_exports -->`) must update `README.md` and `AGENTS.md` in the same change. `./scripts/ci_verify.sh --sync-docs` checks those counters.

7. **End-to-End Amdahl & Ablation Ratchet (`ΔE2E >= 1%` or Delete)**:
   - **No Micro-Benchmark-Only Optimizations**: No hardware backend, cascade tier, heuristic pass, or rewrite rule lands without a measured wall-clock speedup on the full end-to-end pipeline. Every optimization must state its stage fraction $f$ and stage speedup $s$ (`[f=..., s=... -> E2E=...]`).
   - **Transport-Aware Offload Gate**:
     - Synchronous offload is forbidden unless stage share $f \ge 10\%$ AND $\text{p95}(T_{\text{transport}} + T_{\text{serialize}} + T_{\text{device}} + T_{\text{recert}}) < 0.5 \cdot \text{p95}(T_{\text{CPU}})$.
     - Asynchronous ("Fire-and-Forget") offload must demonstrate a statistically significant $\ge 1\%$ reduction in end-to-end campaign time-to-certified-result (including host queue/interrupt overhead).
   - **Mandatory Ablation Flag & Pruning**: Every non-trivial optimization must be toggleable via env/flag. Any optimization, cascade tier, or superopt rule with $0$ hits on the canonical corpus or whose ablation degrades E2E geomean by $< 1\%$ (95% CI) must be deleted to enforce $\Delta\text{LOC} \le 0$.

---

## 3. Repository Layout & Verification Entrypoints

- **Formal Specifications & C-ABI Kernels**: [`lean/TurboLean/Kernel.lean`](lean/TurboLean/Kernel.lean), [`lean/TurboLean/Spec.lean`](lean/TurboLean/Spec.lean) & [`LeanNative/Spec.lean`](../lean-native/LeanNative/Spec.lean)
- **Kernel Replay & Axiom Audit**: [`lean/TurboLean/Assembler.lean`](lean/TurboLean/Assembler.lean), [`lean/TurboLean/Inspector.lean`](lean/TurboLean/Inspector.lean), [`LeanNative/Proofs/AxiomAudit.lean`](../lean-native/LeanNative/Proofs/AxiomAudit.lean)
- **Warm Elaboration & C-ABI Runtime**: [`lean/TurboLean/ZygoteWorker.lean`](lean/TurboLean/ZygoteWorker.lean), [`crates/turbo-lean/src/`](crates/turbo-lean/src/)
- **Autonomous Research & Verification Suites**: [`autoresearch/run_eval.py`](autoresearch/run_eval.py), [`autoresearch/corpus_bench.py`](autoresearch/corpus_bench.py), [`autoresearch/mcp_agent_arena.py`](autoresearch/mcp_agent_arena.py)

---

## 4. Optimization Objectives & Resource Envelopes (`ObjectiveReceipt`)

Autonomous research on `turbo-lean` separates **Layer 1 (Formal Admissibility)** from **Layer 2 (Lexicographic Empirical Fitness)**:

1. **Layer 1 — Hard Formal Gate (`Spec.lean`, `G(x) = true`)**:
   - `untrusted_accelerator_kernel_replay_sound` (every heuristic/TRM candidate replays through the Lean kernel in a prefix-truncated environment with zero target self-reference), `queryTier_eq_oracle` (`0` false-positive CAS hits), `witness_refutes_forall` (`0` false refutations), `0 sorryAx`.
2. **Layer 2 — Lexicographic Objective (`J_turbo`)**:
   - **Primary**: Minimize agent feedback loop latency $\text{Geomean}(\text{latence\_p50}_{\text{warm}}, \text{latence\_p95}_{\text{edit}}, \text{build}_{\text{cone}})$ and deterministic verification heartbeats.
   - **Secondary**: Maximize Tier-0 (`< 10 ms`) masked proof regeneration rate and `proof_term_nodes` compression.
   - **Resource Envelope**: $\text{RSS}_{\text{peak}} \le \text{RAM}_{\text{cap}}$ and $\Delta\text{LOC} \le 0$ (simplicity ratchet).
