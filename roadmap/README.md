# `turbo-lean` Autonomous Research & Verification Roadmap

This directory defines the long-horizon engineering and formal verification roadmap for **`Th0rgal/turbo-lean`** (including the embedded **`LeanNative`** compiler and **`TurboLean`** incremental verification engine).

It is architected specifically for **Asymmetric Autonomy**:
- **Tier-1 Frontier Architect Models (`ARCHITECT`)** and human operators define locked formal specifications, algebraic abstractions, and end-to-end architectural cuts.
- **Tier-2 High-Speed Swarm Models (`SWARM_FAST`)** execute leaf-level proof closing, translation validation, and hardware kernel optimization in parallel worktrees under **Zero-Trust Mechanical Gates** where reward hacking or specification weakening is type-theoretically and cryptographically blocked.

---

## Strict Separation of Concerns (Directory Layout)

Per the architectural charter, **what we aim to achieve (Goals & Validation Contracts)** is strictly decoupled from **how autonomous agent fleets execute the work (Strategies)**:

| Document | Scope | Mutability During Object Waves |
| :--- | :--- | :--- |
| [**`GOALS.md`**](./GOALS.md) | **North-Star Technical Goals (`G1`–`G5`)**: What `turbo-lean` and `LeanNative` must become—`con-leche` in-memory kernel integration, elaboration de-trusting & proof distillation, official target semantics (`lean-mlir`, `LNSym`, `sail-riscv-lean`), and radical LOC compression via 3 unified compiler engines, plus an honest shipped-vs-open status ledger. | **Read-Only** (Updated only at milestone or audit checkpoints) |
| [**`VALIDATION_CONTRACTS.md`**](./VALIDATION_CONTRACTS.md) | **Cheat-Proof Conditions of Success (`V1`–`V5`)**: Exact Lean 4 theorem signatures, ban on boolean-flag proxy specs for AST passes, kernel-level `audit-spec` v2 rules, mutant-kill matrices, and the 10-second Tier-1 reviewer audit protocol. | **Immutable / Hash-Pinned** (`.maxwell/frozen_tools.json`) |
| [**`CONFORMANCE_SUITE.md`**](./CONFORMANCE_SUITE.md) | **Non-FV 3-Way Differential Conformance Harness (`C1`–`C4`)**: Bitwise parity across (1) stock Lean 4 C backend, (2) formal `LNIR` operational interpreter, and (3) `LeanNative` compiled CPU/GPU binaries on real Lake projects and grammar-guided fuzzers. | **Append-Only Corpus** (`SEALED` holdout hashes locked) |
| [**`ORB_SHARED_LEAN_ALIGNMENT.md`**](./ORB_SHARED_LEAN_ALIGNMENT.md) | **Cross-Repo Phase & PR Ledger (`P0`–`P7`, `lean-sys`)**: Exact-head audit of what is merged on `main`, what landed across `turbo-lean` and `lean-sys`, and what remains open before external zero-trust pilots. | **Updated at Audit Checkpoints** |
| [**`MAXWELL_STRATEGIES.md`**](./MAXWELL_STRATEGIES.md) | **Autonomous Execution Playbook (`S1`–`S6`)**: How to execute `GOALS.md` at minimum cost and maximum speed using `lfglabs-dev/maxwell`, Orb (`sandboxed` MCP) model/VM routing, real-time struggle detection, `telemetry.thomas.md` priors, and Hindsight (`memory.thomas.md`). | **Evolving** (Continuously refined by `telemetry.thomas.md`) |

---

## Core Architectural Principles

1. **Goals $\neq$ Strategies**: A compiler soundness theorem or LOC compression target in [`GOALS.md`](./GOALS.md) never depends on which LLM or search heuristic produced it. Conversely, [`MAXWELL_STRATEGIES.md`](./MAXWELL_STRATEGIES.md) can swap model tiers, adjust Bayesian risk aversion, or retrain `ANVIL2` Matryoshka slices without touching a single theorem contract in [`VALIDATION_CONTRACTS.md`](./VALIDATION_CONTRACTS.md).
2. **Zero Trust in Worker Models**: Cheap worker models (`SWARM_FAST`) will take any syntactic shortcut permitted by the verifier (e.g., proving 3-boolean `MetaGateSpec` proxy structs instead of AST refinement, hiding tautologies behind 2-hop helper definitions, or stamping `.verifiedKernelProof` via stringly-typed theorem registries). Every loophole is closed mechanically in [`VALIDATION_CONTRACTS.md`](./VALIDATION_CONTRACTS.md).
3. **Official Mechanized Target Semantics Over Custom String Templates**: Instead of maintaining 7,500+ lines of ad-hoc C/LLVM/PTX/Metal string interpolation in `Driver/CoreCLI.lean` and `Backend/LLVM.lean`, `LeanNative` aligns with upstream Lean 4 formalizations: **`leanprover/con-leche`**, **`digama0/lean4lean`**, **`opencompl/lean-mlir`**, **`leanprover/LNSym`**, and **`opencompl/sail-riscv-lean`**.
4. **3-Way Differential Conformance as the Non-FV Safety Net**: Formal proofs only protect what is inside the formal boundary. Running real Lake repositories (`lean4` run suite, `Batteries`, `SciLean`, `LeanSys`, `ArkLib`) through stock Lean 4 C codegen, the formal `LNIR` interpreter (`evalCode`), and `LeanNative` native/GPU binaries simultaneously catches both frontend lowering bugs (`LCNF → LNIR`) and backend emission bugs (`LNIR → LLVM/SIMD/Metal/PTX`).
5. **Radical Simplicity & The LOC Ratchet**: Complexity is a liability in both TCB and build latency. Every milestone must reduce or hold constant maintained lines of code ($\Delta\text{LOC} \le 0$ on existing subsystems) by replacing ad-hoc "Wave 15–32" pattern matchers and repetitive boolean specs with composable algebraic abstractions.
