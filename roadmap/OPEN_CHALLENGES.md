# Open Challenges & Zero-TCB Accelerator Contributions (`roadmap/OPEN_CHALLENGES.md`)

> **Scope**: Concrete, self-contained engineering and formal-verification challenges for external contributors, university research groups, and autonomous coding/proving agents. Every challenge aligns with [`GOALS.md`](./GOALS.md) (`G1`–`G5`) and is evaluated solely through the cheat-proof mechanical gates in [`VALIDATION_CONTRACTS.md`](./VALIDATION_CONTRACTS.md) (`V1`–`V5`) and [`CONFORMANCE_SUITE.md`](./CONFORMANCE_SUITE.md) (`C1`–`C4`).

---

## 1. Two Contribution Tracks: Zero-TCB Plugins vs. Core Verification

`turbo-lean` separates **untrusted heuristic search** from **kernel-checked semantic truth**:

| Track | What You Build | Build & Language Footprint | How `turbo-lean` Verifies Your Work |
| :--- | :--- | :--- | :--- |
| **Track A — Zero-TCB External Accelerators & LNIR Plugins** *(Fastest Entry)* | Out-of-process JSONL-stdio tactic accelerators, counterexample finders, subgoal-cut planners, `LNIR_WIRE_V1` superoptimizers, and `HardwareCostProfile` JSON profiles (`sdk/accelerator-template/`, `plugins/*.py`). | Any language (Python 3 stdlib, Rust, C++, Go, JAX/CUDA); **zero Lean 4 compiler build required** (`< 1 s` local validation via `python3 sdk/accelerator-template/validate.py`). | `SpeculativeGate`: every `rewritten_proof` replays in the Lean 4 kernel (`untrusted_accelerator_kernel_replay_sound`), every `counterexample_found` is checked on concrete witnesses, external `subgoal_cuts` (`sub_decl_source` theorem shards) surface as advisory `rewrite_suggestions` (`applied: false`) in `agent-step` today while built-in `CutFissionAccelerator` / `fission_theorem_have_blocks` replays on `ZygoteWorker`, and every `LNIR` candidate must pass `verifyOptPluginGate` (`SymbolicTV` + 64-state `evalCode` + non-increasing scalar cost). Timeout or invalid output falls back cleanly (`untrusted_accelerator_timeout_fallback`, `untrusted_opt_plugin_reject_fallback`). |
| **Track B — Core Formal Verification & Compiler Sovereignty** | Verified kernel integration (`con-leche`), elaboration de-trusting (`HeaderPin`, CAS `Expr` replay), `LCNF → LNIR` lowering, Target-IR roundtrips/lowering, upstream ISA/IR bisimulation (`lean-mlir`, `LNSym`, `sail-riscv-lean`), and 3-way differential conformance (`C1`–`C4`). | Lean 4 (`v4.35.0`) + Rust (`crates/turbo-lean/`). | Full Contract `V1`–`V5` gate: `0 sorryAx`, `0 native_decide`, `0 trustCompiler`, `audit-spec --policy strict-proofs`, `check_shadow_semantics.lean`, mutant kills, and 3-way `lean -c` / `evalCode` / native ASan conformance. |

To start immediately on **Track A** without building Lean 4, copy [`sdk/accelerator-template/`](../sdk/accelerator-template/README.md) and run `python3 sdk/accelerator-template/validate.py`.

---

## 2. Track A Challenges — Zero-TCB External Accelerators (`SpeculativeGate`)

External tactic plugins connect via `ExternalProcessAccelerator` (`crates/turbo-lean/src/accelerators.rs`), and external `LNIR` superoptimizers connect via `runExternalOptPlugin` (`lean/LeanNative/Transform/Plugins.lean`). Because `evalWithUntrustedAccelerator` and `evalWithUntrustedOptPlugin` reject unsound proposals fail-closed, **bugs, crashes, or hallucinations in an external plugin cannot compromise soundness**.

### Challenge A1: Domain-Specific Tactic & Proof-Distillation Accelerators (`rewritten_proof`)
- **Goal Alignment**: `G2` (Cold-path elaboration speedup & zero-dependency proof distillation).
- **Problem**: General tactics (`simp`, `aesop`, `omega`, `ring`, `bv_decide`) often spend hundreds of milliseconds searching `DiscrTree` or `MetaM` state when a domain-aware external solver (SAT/SMT, Gröbner basis, linear/integer programming, or corpus retrieval over `available_constants`) can emit a minimal `simp only [...]`, `decide`, `bv_decide`, or explicit Farkas/cofactor proof script in `< 10 ms`.
- **Entrypoints**: [`sdk/accelerator-template/plugin.py`](../sdk/accelerator-template/plugin.py), [`plugins/verity_yul_plugin.py`](../plugins/verity_yul_plugin.py), [`plugins/riscv_yukon_plugin.py`](../plugins/riscv_yukon_plugin.py), [`plugins/snark_llvm_superopt_plugin.py`](../plugins/snark_llvm_superopt_plugin.py), [`crates/turbo-lean/src/accelerators.rs`](../crates/turbo-lean/src/accelerators.rs).
- **Mechanical Acceptance Gate**:
  1. Passes `python3 sdk/accelerator-template/validate.py` (schema, budget/timeout, malformed-input, and abstention checks).
  2. Replays with `0 sorryAx` and pinned kernel statement hashes under `turbo-lean agent-step` / `turbo-lean pr-verify --mode untrusted --disallow-statement-changes`.
  3. Achieves a reproducible $\ge 1.0\%$ end-to-end warm/cold check geomean improvement on a target Lean 4 benchmark corpus (`AGENTS.md` Rule 7 Amdahl ratchet).

### Challenge A2: Fast Counterexample & Missing-Hypothesis Synthesizers (`counterexample_found`)
- **Goal Alignment**: `G2` & `G5` (Sub-millisecond false-conjecture refutation and hypothesis repair).
- **Problem**: Autonomous proof agents waste large token and elaboration budgets attempting to prove false intermediate lemmas (`SpecTooStrong` or `CandidateBug`). External randomized/SIMD/GPU/SMT solvers can refute false `BitVec`, `UInt256`, modular-arithmetic, array-indexing, or RISC-V step-budget goals in `< 5 ms` and propose a tight missing hypothesis (`suggested_hypothesis`).
- **Entrypoints**: [`sdk/accelerator-template/plugin.py`](../sdk/accelerator-template/plugin.py), `AcceleratorCertificate::CounterexampleFound` in [`crates/turbo-lean/src/accelerators.rs`](../crates/turbo-lean/src/accelerators.rs), `CounterexampleTriageInput` in [`lean/TurboLean/Spec.lean`](../lean/TurboLean/Spec.lean).
- **Mechanical Acceptance Gate**:
  1. Emits valid `counterexample_found` JSONL certificates with concrete witness assignments within `budget_ms`.
  2. Zero false refutations on true theorems in the conformance corpus (`witness_refutes_forall` / concrete evaluation gate).
  3. Suggests non-vacuous hypotheses (`turbo-lean audit-spec` reports `vacuous_specs == 0`).

### Challenge A3: Subgoal-Cut & Lemma-Fission Planners (`subgoal_cuts`)
- **Goal Alignment**: `G2` (Parallel `ZygoteFork` proof checking & cut fission).
- **Problem**: Long monolithic tactic blocks serialize elaboration. Today, built-in `CutFissionAccelerator` (`builtin:cut-fission` in `crates/turbo-lean/src/accelerators.rs`) emits standalone, self-contained `sub_decl_source` theorem shard strings (`theorem <decl_name> <binders><promoted_hyps> : <cut_ty_or_goal> := <rhs>`), and `check.rs` replays built-in `splitter::fission_theorem_have_blocks` sub-shards on `ZygoteWorker`, whereas external JSONL-stdio `AcceleratorCertificate::SubgoalCuts` certificates from `ExternalProcessAccelerator` are currently surfaced as advisory `rewrite_suggestions` (`applied: false`) in `agent-step` (`crates/turbo-lean/src/gpu_fastcheck.rs`) while `check.rs` speculatively replays `AcceleratorCertificate::RewrittenProof`. External planners under Challenge A3 emit standalone `sub_decl_source` theorem shard strings matching `CutFissionAccelerator` (optionally paired with `rewritten_proof` when immediate speculative replay in `check.rs` is desired); wiring untrusted external `SubgoalCuts` directly into a sound `ZygoteFork` implication-chain check + parallel sub-shard replay in `check.rs` is an open Track A/B host integration bridge.
- **Entrypoints**: `CutFissionAccelerator` and `AcceleratorCertificate::SubgoalCuts` in [`crates/turbo-lean/src/accelerators.rs`](../crates/turbo-lean/src/accelerators.rs), `fission_theorem_have_blocks` in [`crates/turbo-lean/src/splitter.rs`](../crates/turbo-lean/src/splitter.rs), [`crates/turbo-lean/src/check.rs`](../crates/turbo-lean/src/check.rs), [`crates/turbo-lean/src/gpu_fastcheck.rs`](../crates/turbo-lean/src/gpu_fastcheck.rs), `canSafelyFissionHavePrologue` in [`lean/TurboLean/PolicyGates.lean`](../lean/TurboLean/PolicyGates.lean).
- **Mechanical Acceptance Gate**:
  1. External planner emits $\ge 2$ standalone `sub_decl_source` theorem shard strings (`theorem <decl_name> ... := ...`, `0 sorryAx`) matching `CutFissionAccelerator`, validated offline via `python3 sdk/accelerator-template/validate.py` and replaying cleanly through the Lean 4 kernel with promoted hypotheses discharging the original theorem signature.
  2. For the Track A/B host-integration bridge: untrusted external `SubgoalCuts` pass sound implication-chain + outer-signature verification in `check.rs` (`0 sorryAx`, `disallow-statement-changes`) and achieve a measurable wall-clock reduction on multi-hundred-line tactic proofs under `ZygoteFork` / `ZygoteWorker`.

### Challenge A4: Out-of-Process `LNIR_WIRE_V1` Superoptimizers & E-Graph / SMT Synthesizers
- **Goal Alignment**: `G3.2` & `G4` (Translation-validated `LNIR → LNIR` optimization).
- **Problem**: External e-graph engines (`egg`/`egglog`), stochastic MCMC/evolutionary search (`superopt-evolve`), or `BitVec` SMT synthesizers can optimize `LNIRDecl` bodies serialized in the lossless `LNIR_WIRE_V1|` token format (`LeanNative/IR/Codec.lean`) across `x86_64`, `arm64`, `cuda_ptx`, and `apple_metal` without touching the Lean compiler TCB.
- **Entrypoints**: `runExternalOptPlugin` and `verifyOptPluginGate` in [`lean/LeanNative/Transform/Plugins.lean`](../lean/LeanNative/Transform/Plugins.lean), `LNIRModule.toWire` / `LNIRModule.fromWire?` in [`lean/LeanNative/IR/Codec.lean`](../lean/LeanNative/IR/Codec.lean), [`crates/turbo-lean/src/superopt_evolve.rs`](../crates/turbo-lean/src/superopt_evolve.rs), [`sdk/accelerator-template/`](../sdk/accelerator-template/README.md).
- **Mechanical Acceptance Gate**:
  1. Candidate `LNIR_WIRE_V1|` round-trips losslessly through `LNIRModule.fromWire?` with identical parameter `(id, ty)` signature and `retTy`.
  2. Passes `verifyOptPluginGate` (`validateTranslationDecl src cand 64`: UB refinement, return domain, poison refinement, normalized symbolic return value, 64-state `evalCode` equivalence, memory write refinement, and `declScalarCost target cand <= declScalarCost target src`).
  3. Adversarial/unsound rewrites are deterministically rejected (`adversarialRejected == true` in `lean-native-core plugins --json`).
  4. Demonstrates a reproducible native throughput improvement on `python3 scripts/bench_rust_parity.py --trials 7` (`docs/BENCH_RUST_PARITY.md`) while keeping all 128-seed parity checksums bit-exact.

### Challenge A5: Calibrated Hardware Cost Profiles (`HardwareCostProfile`)
- **Goal Alignment**: `G3.2` & `G4` (Target-accurate cost ranking without TCB expansion).
- **Problem**: `HardwareCostProfile` (`lean/LeanNative/Transform/Superopt.lean`) ranks candidate `LNIR` rewrites for `x86_64`, `arm64`, `cuda_ptx`, and `apple_metal`. Because cost profiles only rank candidates that independently pass `fastCheckScalarEquiv` + `symCheckScalarEquiv` (`Law 1`), tuning profiles for Zen 5, Neoverse V2, Apple M3/M4, or NVIDIA Hopper/Blackwell is 100% zero-TCB.
- **Entrypoints**: `HardwareCostProfile` in [`lean/LeanNative/Transform/Superopt.lean`](../lean/LeanNative/Transform/Superopt.lean), `CostAutotuneCLI.lean` in [`lean/LeanNative/Driver/CostAutotuneCLI.lean`](../lean/LeanNative/Driver/CostAutotuneCLI.lean), [`docs/BENCH_RUST_PARITY.md`](../docs/BENCH_RUST_PARITY.md).
- **Mechanical Acceptance Gate**:
  1. Zero `validate-tv` or 128-seed `PARITY_HASH` regressions.
  2. Measurable geomean speedup ($\ge 1.0\%$, $\text{CV} \le 3.0\%$) on target hardware via `python3 scripts/bench_rust_parity.py --trials 7`.

---

## 3. Track B Challenges — Core Formal Verification & Compiler Sovereignty (`G1`–`G5`)

Every Track B contribution must obey **Rule 8 (Zero Shadow-Namespace / Zero-Stubbing)** in [`AGENTS.md`](../AGENTS.md) and **Contracts `V1`–`V5`** in [`VALIDATION_CONTRACTS.md`](./VALIDATION_CONTRACTS.md). Never introduce local toy namespaces (`namespace ConLeche`, `namespace LeanMLIR`, `namespace LNSym`) to satisfy a signature; missing upstream dependencies must be Vendored/Pinned honestly or escalated as `BLOCKED_MISSING_DEPENDENCY`.

### Challenge B1 (`G1` / Milestone `M2`): Vendored `con-leche` Zero-Copy `.olean` Bridge & Transitive `csimp` Attestation
- **Problem**: `--kernel <auto|standard|con-leche|both>` and `VerificationReceipt` (`schema_version = 2`) are landed, and [`verification/con-leche-bridge/`](../verification/con-leche-bridge/) pins upstream [`leanprover/con-leche`](https://github.com/leanprover/con-leche) (`501589f5680d9599dee1bcef30a420bc8924c490`, `leanprover/lean4:v4.35.0`) with 31 kernel-verified soundness theorems (`0 sorryAx`, `0` nonstandard axioms) covering `checkDecls`/`streamEnv` set-theoretic model existence, `Empty`/`False`/`Eq` denotational soundness, `prepareD`/`preparePrelude` permutation & pass-through, `.olean` sparse region decoding (`frontierExpr`/`sparseNameP`/`sparseExprP`/`sparseEntry`), deferred theorem-value `fillDecl`/`buildIndex_fill`/`readOleans_filled` closure invariants, arena exit codes (`1`/`2`/`3` vs. `0`), and `turbo-lean`'s exact `--verified --jobs=<n> --olean --search-path=<sp> [--constant=<c>...] -- <roots...>` and NDJSON `runArgs` invocations, while `lean/TurboLean/ConLeche.lean` still verifies a self-contained model. Remaining frontiers include wiring official `con-leche` (+ [`digama0/lean4lean`](https://github.com/digama0/lean4lean) corner cases) directly into `turbo-lean`'s runtime `--kernel con-leche` path over real mmap'd `.olean` / `ConstantInfo` shards for compatible `lean-toolchain`s, plus Stage B transitive compiled-import `@[csimp]` auditing bound into cache keys and `VerificationReceipt`.
- **Entrypoints**: [`verification/con-leche-bridge/`](../verification/con-leche-bridge/), [`scripts/check_con_leche_bridge_sync.py`](../scripts/check_con_leche_bridge_sync.py), [`lean/TurboLean/ConLeche.lean`](../lean/TurboLean/ConLeche.lean), [`crates/turbo-lean/src/kernel.rs`](../crates/turbo-lean/src/kernel.rs), [`scripts/test_kernel_gate_audit.py`](../scripts/test_kernel_gate_audit.py).
- **Mechanical Gate**: Discharges `olean_mmap_bridge_sound` and `con_leche_verify_decl_sound` (`Contract V4 M2`) over real `.olean` shards, keeps `scripts/check_con_leche_bridge_sync.py` (`>= 31` unique `bridgedTheorems.Nodup` theorems, `0 sorryAx`) green, passes `scripts/test_kernel_gate_audit.py` and `scripts/test_p0_trust_boundary.py`, and fails closed on incompatible toolchains.

### Challenge B2 (`G2` / Milestone `M3`): `HeaderPin` Surface-vs-Kernel Matcher & `LNIR_EXPR_V1` CAS Proof Replay
- **Problem**: Macro expansion, custom elaborators, and implicit binder shadowing in `Lean.Elab` can subtly alter a human-written theorem statement, and cold `MetaM` elaboration dominates build latency. We need (1) structural surface-AST round-trip verification against `ConstantInfo.type` (`pp.all = true`, `pp.universes = true`, `pp.explicit = true`, `shadowedBindersCount == 0`) and (2) distilled kernel `Expr` replay from `TurboStore` bypassing `Lean.Elab` on warm hits.
- **Entrypoints**: [`lean/TurboLean/ElabAudit.lean`](../lean/TurboLean/ElabAudit.lean), [`lean/TurboLean/StatementHash.lean`](../lean/TurboLean/StatementHash.lean), [`crates/turbo-lean/src/audit_spec.rs`](../crates/turbo-lean/src/audit_spec.rs).
- **Mechanical Gate**: Discharges `header_pin_prevents_statement_spoofing` and `cas_proof_replay_sound` (`Contract V4 M3`), kills $\ge 3$ macro-spoofing / binder-shadowing mutants, and passes `audit-spec --policy strict-proofs`.

### Challenge B3 (`G3.1` & `G3.2` / Milestone `M4`): Broader Verified `LCNF → LNIR` Coverage & Full LLVM Heap Codegen
- **Problem**: `RealLCNFBridge` is proved on scalars, flat tuples, and bounded Stage-1D constructors/ADTs, while `compile-llvm` intentionally fails closed on heap-ADT operations. Open frontiers include general recursive `LCNF` functions, closures / partial applications (`pap` / higher-order `.fvar` calls), `letrec`, signed `Int8/16/32/64`, full `HeapObj` LLVM emission, and grounding `LCNF` evaluation in upstream `digama0/lean4lean`.
- **Entrypoints**: [`lean/LeanNative/IR/Bridge.lean`](../lean/LeanNative/IR/Bridge.lean) (`<= 350 LOC` gate), [`lean/LeanNative/Frontend/`](../lean/LeanNative/Frontend/), [`lean/LeanNative/Semantics/Eval.lean`](../lean/LeanNative/Semantics/Eval.lean), [`docs/HEAPOBJ_CONTRACT.md`](../docs/HEAPOBJ_CONTRACT.md).
- **Mechanical Gate**: Preserves `Bridge.lean <= 350 LOC`, `54/54 PASS` in `HeapObjContract.lean`, `0` shadow semantics (`scripts/check_shadow_semantics.lean`), `0 sorryAx` in `AxiomAudit.lean`, and passes 3-way ASan conformance (`live_objects == 0`) on newly supported `LCNF` constructs.

### Challenge B4 (`G3.3` & `G4` / Milestone `M5`): Unified Proved AST-to-Text Emission & Upstream ISA/IR Bridges
- **Problem**:
  1. **Unified AST Pretty-Printing**: Covered PTX scalars, Metal kernels, and the 22-op StableHLO fragment already share typed AST printers and roundtrip proofs (`parse ∘ pp = some`), while standalone string emission paths remain in `Backend/LLVM.lean` (separate from `LLVMEmitVerify`), `Backend/MLIRGPU.lean` (`StableHLOOp.dynamicSlice`/`reduce`), `Backend/Metal.lean`, `Backend/Hybrid.lean`, non-scalar PTX atomic reductions (`dotProduct`), and `Driver/CoreCLI.lean` (`<= 1,000 LOC` gate).
  2. **Upstream Semantics Bridges**: Extend [`verification/lean-mlir-bridge/`](../verification/lean-mlir-bridge/) (`opencompl/lean-mlir` `LLVM.IntW` & `InstCombine.Op.denote` `add`/`sub`/`mul`/`and`/`or`/`xor`/`shl`/`lshr`/`ashr`/`icmp`/`select`/`zext`/`sext`/`trunc` poison-refinement bisimulation, `udiv`/`urem`/`sdiv`/`srem` UB-vs-poison boundary specs including `i1` all-ones overflow, and compositional `StraightLineBisim` SSA sequence & memory/globals frame invariance; 63 kernel-verified theorems), [`verification/lnsym-bridge/`](../verification/lnsym-bridge/) (`leanprover/LNSym` ARM64 NEON `PMULL`/`PMULL2`/`EOR`/`EXT` instruction & 28-instruction `Arm.run` bisimulation, $\mathbb{F}_{2^{128}} \cong \mathbb{F}_2[x]/(x^{128}+x^7+x^2+x+1)$ modular reduction soundness & commutative ring laws, multi-lane additive NTT butterfly slice bisimulation, and SHA-512 / AES-SBOX / Rcon / GCM FIPS 180-4, FIPS 197 & SP 800-38D constant certification + `K0` butterfly twiddle; 50 kernel-verified theorems), and [`verification/sail-riscv-bridge/`](../verification/sail-riscv-bridge/) (`opencompl/sail-riscv-lean` RV64 architectural register/PC/`PcAccess`, RV64I base + `*W` ALU/shift/`LUI`/`AUIPC`/branch/`JAL`/`JALR`, full RV64M + `*W` `DIV`/`DIVU`/`REM`/`REMU`/`MUL`/`MULH`/`MULHSU`/`MULHU`/`MULW`/`DIVW`/`DIVUW`/`REMW`/`REMUW`, `Zba`/`Zbb`/`Zbc`/`Zbs` bit-manipulation, RV64I `LOAD`/`STORE` `LB`/`LBU`/`LH`/`LHU`/`LW`/`LWU`/`LD`/`SB`/`SH`/`SW`/`SD` flat-RAM + store-then-load roundtrip, `RVC` `Zca`/`Zcb`/RV64C compressed `C_*`, `Zaamo`/`Zacas`/`Zalrsc` atomics & reservation-parameterized LR/SC, `Zicsr`/privileged-mode checks, `Sv39`/`Sv48` virtual-memory PTE/SATP/TLB + multi-level `pt_walk`/`translate`/`translateAddr` page-table walk & hardware `Svadu` A/D updates, `MRET`/`SRET`/trap-delegation/`trap_handler`/interrupt dispatch, and RV64F/D IEEE-754 bit-exact NaN-boxing/`FLW`/`FSW`/`FLD`/`FSD`/`C_FL*`/`C_FS*`/`FMV.*`/`FCLASS.*`/`FSGNJ*`/`FMIN.*`/`FMAX.*` bisimulation; 116 kernel-verified theorems) to SoftFloat-backed RV64F/D arithmetic (`FADD`/`FSUB`/`FMUL`/`FDIV`/`FSQRT`/`FMADD`/conversions) and vector (`RVV`) / hypervisor (`H`) extensions.
- **Entrypoints**: [`lean/LeanNative/Backend/`](../lean/LeanNative/Backend/), [`verification/lean-mlir-bridge/`](../verification/lean-mlir-bridge/), [`verification/lnsym-bridge/`](../verification/lnsym-bridge/), [`verification/sail-riscv-bridge/`](../verification/sail-riscv-bridge/), [`scripts/check_lean_mlir_bridge_sync.py`](../scripts/check_lean_mlir_bridge_sync.py), [`scripts/check_lnsym_bridge_sync.py`](../scripts/check_lnsym_bridge_sync.py), [`scripts/check_sail_riscv_bridge_sync.py`](../scripts/check_sail_riscv_bridge_sync.py).
- **Mechanical Gate**: Kernel-proved `parse ∘ pp = some` + canonical injectivity on newly covered constructors, $\Delta\text{LOC} \le 0$ on legacy string emitters (no string-relocation gaming per Rule 8), active emitter mutants `M1`–`M10` killed (`python3 scripts/emitter_mutants.py --unit-tests`), and `check_lean_mlir_bridge_sync.py` / `check_lnsym_bridge_sync.py` / `check_sail_riscv_bridge_sync.py` green with `0 sorryAx` and `0 bv_decide`.

### Challenge B5 (`G5` / Tiers `C1`–`C4`): Ecosystem 3-Way Differential Conformance & 10,000-Seed Alias Fuzzing
- **Problem**: Scale `scripts/run_conformance_suite.py` beyond the current scalar/tuple `C1` subset and 32–64 seed `C4` runs to:
  1. **250+ upstream `leanprover/lean4/tests/lean/run` programs** (`Tier C1`),
  2. **Deterministic Lake ecosystem packages (`Tier C2`)**: `Batteries`, `LeanSys`, `SciLean`, and `ArkLib` / `Verity` 256-bit / `GF(2^128)` kernels, and
  3. **Shared-vs-exclusive array alias & `seqFor` mutation fuzzing (`Tier C4`)** with automatic delta-reduction into `ConformanceRegressions.lean`.
- **Entrypoints**: [`scripts/run_conformance_suite.py`](../scripts/run_conformance_suite.py), [`scripts/run_gpu_tpu_diff.py`](../scripts/run_gpu_tpu_diff.py), [`roadmap/CONFORMANCE_SUITE.md`](./CONFORMANCE_SUITE.md).
- **Mechanical Gate**: `mismatch_count == 0` and `rc_leak_count == 0` across `lean -c`, `evalCode`, and ASan-instrumented `LeanNative` binaries (`python3 scripts/run_conformance_suite.py --tier C1,C4 --fuzz-seeds 64 --asan --ubsan`).

---

## 4. Pre-PR Mechanical Verification Checklist

Before opening a pull request:

- **Track A (External Accelerators & `LNIR` Plugins — No Lean Build Needed)**:
  ```bash
  python3 sdk/accelerator-template/validate.py
  cargo test --release --locked accelerators
  ```
- **Track B (Core Lean / Compiler / Verification Changes)**:
  ```bash
  python3 scripts/sync_docs_inventory.py --check
  python3 scripts/ci_impact_plan.py --self-test
  ./scripts/ci_verify.sh
  ./scripts/verify_roadmap_contract.sh
  ```
