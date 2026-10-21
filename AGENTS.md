# AGENTS.md — Architectural Charter (`turbo-lean` ⟷ `lean-native`)

## 1. Symbiosis & Architectural Roles

`turbo-lean` and `lean-native` form a co-designed formal verification and native execution stack for Lean 4:

- **`turbo-lean` (Incremental Verification, Zygote Elaboration & Federated Orchestration)**:
  Partitions Lean modules into topological dependency cones and sub-proof cuts, caches artifacts across content-addressed memory and persistent stores, orchestrates warm `Command.State` Zygote workers, exposes an MCP server for proof agents, and enforces an in-kernel soundness gate (`0 sorryAx`, `0 native_decide`, `0 trustCompiler`, statement pinning, and nested-inductive hygiene).
- **`lean-native` (Verified Native Codegen, Translation Validation & Hardware Fast-Check)**:
  Lowers Lean/LNIR into verified C-ABI SIMD, LLVM IR, NVIDIA PTX, Apple Metal, and Cloud TPU XLA/StableHLO kernels. Certifies counterexamples and spec non-vacuity via executable operational semantics (`evalCode`) and symbolic translation validation (`CodeRefines`) before `turbo-lean` spends elaboration compute.

```
Agent / CLI / MCP ──► Stage 0: Cone & CAS Filter (`turbo-lean` + C-ABI `Spec.lean`)
                  ──► Stage 1: Certified Fast-Check & Vacuity Gate (`lean-native` CPU/GPU/TPU)
                  ──► Stage 2: Speculative Tactic Racing & Warm Zygote Replay (`ZygoteWorker`)
                  ──► Stage 3: In-Kernel Axiom & Statement Pinning Gate (`Inspector` / `AxiomAudit`)
```

---

## 2. Five Non-Negotiable Engineering Rules

1. **Zero Model-Code Gap via Direct C-ABI (`@[export]`)**:
   Executable decision gates, cost models, and state transitions affecting soundness or routing live in `Spec.lean` (with zero compiler-frontend dependencies) and are compiled directly to unboxed C-ABI primitives (`@[inline, export ...]`). Host runtimes call the compiled Lean specification directly instead of re-implementing shadow logic in Rust or Python.

2. **Two-Layer Specification Compression (`Layer I` Meta-Specs vs. `Layer II` Corollaries ≤ 3 Lines)**:
   - **Layer I (Universal Meta-Specifications & Combinators)**: All structural reasoning lives in reusable algebraic combinators (`MetaGateSpec`, `MetaAlgorithmSpec`, `SpeculativeGate`, `SoundCacheTier`, `ObservationalProj`, `WitnessRefuter`, `ArgminRouteFold`, `ClockedStepBudget`).
   - **Layer II (Declarative Corollaries)**: Concrete subsystem properties are instantiated as `MetaGateSpec` / `MetaAlgorithmSpec` bundles or corollaries of **≤ 3 lines** discharging directly through Layer I combinators.

3. **Hermetic Segregation of Formal Kernel vs. Untrusted Heuristic Plugins behind `SpeculativeGate`**:
   All heuristic accelerators, tactic synthesizers, superoptimizer rewrites, and hardware backends (SIMD, CUDA, Metal, TPU XLA, external JSONL-stdio processes) are treated as untrusted proposals. Every proposal is gated by `SpeculativeGate` (`evalWithUntrustedAccelerator` / `evalWithUntrustedOptPlugin`) and verified by the Lean kernel or translation validator (`0 sorryAx`, `0 native_decide`), with transparent fallback to the baseline on timeout or rejection.

4. **Mathlib4 Algebraic Proof Style**:
   Proofs in `Spec.lean` and across the proof suite must follow concise Mathlib4 algebraic idioms (`split <;> simp_all`, `simpa`, `omega`, `iff` equivalences, and point-free combinators). Verbose `cases <;> cases` cascades and repetitive boilerplate are forbidden.

5. **LOC Reduction Ratchet**:
   Every refactoring, bug fix, or feature addition must actively compress or factor existing code and specifications. New capabilities are integrated by generalizing Layer I combinators or unified runtime traits rather than accreting ad-hoc modules or duplicating logic across repositories.

---

## 3. Repository Layout & Verification Entrypoints

- **Formal Specifications**: [`lean/TurboLean/Spec.lean`](lean/TurboLean/Spec.lean) & [`LeanNative/Spec.lean`](../lean-native/LeanNative/Spec.lean)
- **Kernel Replay & Axiom Audit**: [`lean/TurboLean/Assembler.lean`](lean/TurboLean/Assembler.lean), [`lean/TurboLean/Inspector.lean`](lean/TurboLean/Inspector.lean), [`LeanNative/Proofs/AxiomAudit.lean`](../lean-native/LeanNative/Proofs/AxiomAudit.lean)
- **Warm Elaboration & C-ABI Runtime**: [`lean/TurboLean/ZygoteWorker.lean`](lean/TurboLean/ZygoteWorker.lean), [`crates/turbo-lean/src/`](crates/turbo-lean/src/)
- **Autonomous Research & Verification Suites**: [`autoresearch/run_eval.py`](autoresearch/run_eval.py), [`autoresearch/corpus_bench.py`](autoresearch/corpus_bench.py), [`autoresearch/mcp_agent_arena.py`](autoresearch/mcp_agent_arena.py)
