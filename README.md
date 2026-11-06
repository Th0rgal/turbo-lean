<p align="center">
  <img src="logo.svg" width="160" alt="turbo-lean" />
</p>

<h1 align="center">turbo-lean</h1>

<p align="center">
  <strong>Incremental verification, counterexample triage, and verified native/SIMD/GPU/TPU compilation for Lean 4.</strong>
</p>

`turbo-lean` combines an incremental verification oracle (`TurboLean`) and a formally verified native compiler (`LeanNative`) on top of [`lean-sys`](https://github.com/Th0rgal/lean-sys).

---

## Goals

1. **Sub-2ms Incremental Proof Verification & Counterexample Triage (`TurboLean`)**:
   - Re-check edited theorems in milliseconds via warm `ZygoteWorker` checkpoints, content-addressed `.olean`/shard caching, and topological dependency cones instead of rebuilding whole Lake packages.
   - Reject false conjectures in under a millisecond via CPU SIMD / GPU fast-check and classify counterexamples (`CandidateBug | SpecTooStrong | ReferenceDiscrepancy`) through in-process C-ABI gates.
   - Block reward hacking on untrusted proofs: enforce in-kernel transitive axiom checks (`{propext, Quot.sound, Classical.choice}`), reject `sorryAx` / `native_decide` / `trustCompiler` / `unsafe` / `@[extern]` / `@[implemented_by]` bypasses, pin theorem statements from kernel declarations, select kernel engines fail-closed (`--kernel auto|standard|con-leche|both`, `--base`-isolated), and emit signed Ed25519/BLAKE3 provenance receipts.
2. **Verified Native & Accelerator Compilation (`LeanNative`)**:
   - Lower pure Lean 4 (`Lean.Compiler.LCNF`) through `LNIR` to standalone native CPU/SIMD code, GPU kernels, TPU programs, and zero-copy C99/Rust FFI without sacrificing Lean's soundness guarantees.
   - Keep every heuristic optimizer, hardware plugin (`@[simd]`, `@[gpu]`, `@[tpu]`, `@[superopt]`), and stochastic/autotuned rewrite strictly untrusted behind kernel refinement proofs or symbolic translation validation.
   - Pair pure compute kernels with [`lean-sys`](https://github.com/Th0rgal/lean-sys) (`0 import Lean`, `libleanrt.a`-only) when compiled Lean 4 binaries need OS interaction (POSIX I/O, WAL/CAS storage, shared memory, sandboxing, HTTP/JSON-RPC).
3. **North-Star Roadmap ([`roadmap/GOALS.md`](roadmap/GOALS.md))**:
   - **Verified In-Memory Kernel (`G1`)**: Vendor `leanprover/con-leche` (+ `lean4lean` corner cases) over zero-copy mmap'd `.olean` shards for sub-millisecond Lean-in-Lean receipt replay.
   - **Elaboration De-Trusting (`G2`)**: Surface-AST `HeaderPin` round-tripping and distilled CAS kernel proof-term replay (`LNIR_EXPR_V1`) that bypasses `Lean.Elab` on warm builds.
   - **Broader `LCNF` & Upstream Target Semantics (`G3`–`G4`)**: Expand `LCNF` lowering to general recursion, closures, and signed `Int*`; link upstream `opencompl/lean-mlir`, `leanprover/LNSym`, and `opencompl/sail-riscv-lean`; and unify production text emission directly over the proved Target-IR AST pretty-printers.
   - **Ecosystem Differential Fuzzing (`G5`)**: Scale 3-way differential conformance across the upstream Lean 4 run suite, real Lake packages, and continuous `LCNF` fuzzing.

---

## What We Proved

All compiler and gate theorems are audited in the Lean 4 kernel (`#verify_lean_native_axioms` in [`lean/LeanNative/Proofs/AxiomAudit.lean`](lean/LeanNative/Proofs/AxiomAudit.lean)) against standard axioms `[propext, Quot.sound, Classical.choice]` with zero `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, or `Lean.trustCompiler`:

- **Frontend Lowering (`Lean.Compiler.LCNF -> LNIR`)**: Semantic refinement (`lowerRealLCNFCode_sound`, `lowerRealLCNFDecl_sound`) over upstream `Lean.Compiler.LCNF` declarations for the supported scalar, flat-tuple, constructor/ADT, slice, and non-escaping coroutine subset, plus retained LCNF proof facts (`ProofRetention.lean`) discharging bounds and exclusivity checks.
- **Middle-End Optimizations & Ownership/RC (`LNIR -> LNIR`)**: Machine-checked `CodeRefines` proofs across algebraic peepholes and equality saturation (`EqSat.lean`), structured loop scheduling and `parFor` kernel fusion (`LoopSchedule.lean`, `KernelFusionProofs.lean`), closure defunctionalization and ADT/slice lowering (`ClosureADTProofs.lean`, `SliceViewProofs.lean`), unboxed regions and Perceus/COW reference-counting elision (`UnboxedRegion.lean`, `OwnershipRC.lean`, `HeapObjAbiProofs.lean`), and zero-alloc stackless async state machines (`AsyncStateMachine.lean`).
- **Translation Validation & Certifying Superoptimization (`SymbolicTV` & `@[superopt]`)**: Soundness of symbolic execution and equivalence checking over pure 64-bit scalar and obligation-guarded `LNIR` (`SymbolicTVRefinesSoundness.lean`, `SymbolicTVSoundness.lean`), plus kernel-checked cost-guided and stochastic superoptimization (`SuperoptSoundness.lean`, `StochasticCert.lean`, `CostAutotune.lean`).
- **Backend AST Lowering (`LNIR -> Target IR`)**: End-to-end semantic preservation from `LNIR` into five typed Target-IR ASTs (`lowerToLLVM_sound`, `lowerToPTX_sound`, `lowerToMetal_sound`, `lowerToStableHLO_sound`, `validateHybridDispatch_sound`, and `execZeroCopySliceIoHostCall_ok_sound`), plus tight non-vacuous C-ABI decision gates in [`lean/TurboLean/Spec.lean`](lean/TurboLean/Spec.lean) and [`lean/LeanNative/Spec.lean`](lean/LeanNative/Spec.lean).

*(Note: [`lean/TurboLean/ConLeche.lean`](lean/TurboLean/ConLeche.lean) and [`lean/TurboLean/ElabAudit.lean`](lean/TurboLean/ElabAudit.lean) prove CIC typechecking and statement-pinning soundness over a self-contained model; wiring official `leanprover/con-leche` to real `.olean` files remains `G1`/`G2`.)*

---

## Targeted IRs & Why We Can Trust Them

`LeanNative` lowers `LNIR` into **five target IRs**, each formalized in pure Lean 4 with a typed syntax tree and executable operational semantics:

1. **LLVM IR (`LLVMAst`)** — Native CPU & SIMD (`x86_64` AVX2/AVX-512, `aarch64` NEON), modeling exact `BitVec` arithmetic, `poison`/`nsw`/`nuw` propagation, and `noalias` pointer/heap safety ([`lean/LeanNative/Backend/LLVMAst/`](lean/LeanNative/Backend/LLVMAst/)).
2. **NVIDIA CUDA PTX (`PTXAst`)** — SIMT GPU kernels (`sm_80`/`sm_90`), modeling warp/thread execution, shared/global memory race traps, per-barrier generation epochs (`bar.sync` with early-`ret` threads), and optional `po`/`rf`/`co`/`sw` weak-memory consistency ([`lean/LeanNative/Backend/PTXAst/`](lean/LeanNative/Backend/PTXAst/)).
3. **Apple Metal 3.0 MSL (`MetalAst`)** — Apple Silicon GPU kernels, modeling threadgroup execution, barriers, and disjoint buffer-offset bounds ([`lean/LeanNative/Backend/MetalAst/`](lean/LeanNative/Backend/MetalAst/)).
4. **Google TPU StableHLO / MLIR (`StableHLOAst` + JAX `Pallas`)** — Cloud TPU v6e shaped tensor programs ([`lean/LeanNative/Backend/StableHLOAst/`](lean/LeanNative/Backend/StableHLOAst/)).
5. **C99 ABI (`Hybrid` / `CAbiEmit`)** — Standalone `.c`/`.h`/`.rs` static libraries, `lean.h` `HeapObj` reference-counting layout ([`docs/HEAPOBJ_CONTRACT.md`](docs/HEAPOBJ_CONTRACT.md)), and zero-copy host-device slice marshaling ([`lean/LeanNative/Backend/Hybrid.lean`](lean/LeanNative/Backend/Hybrid.lean)).

Because these Target-IR semantics are authored in-repo (not imported from upstream LLVM, NVIDIA, Apple, or OpenXLA) and serialized as text to vendor toolchains, trusting them relies on **four explicit layers**:

1. **In-Kernel Refinement Proofs (`Proven`)**: Every `LNIR -> Target-IR AST` lowering pass is proved in the Lean 4 kernel to preserve program behavior and never introduce modeled undefined behavior (`poison`, out-of-bounds slice access, barrier divergence, or shared-memory races).
2. **Anti-Cheat Shadow-Semantics Gate (`Checked in CI`)**: [`scripts/check_shadow_semantics.lean`](scripts/check_shadow_semantics.lean) ([`docs/SHADOW_SEMANTICS.md`](docs/SHADOW_SEMANTICS.md), empty allowlist) inspects the elaborated kernel constant graph so Target-IR evaluators cannot call, clone, or wrap `LNIR`'s evaluator to make lowering proofs tautological.
3. **3-Way Differential Execution & Emitter Mutation Testing (`Tested in CI`)**: To catch any gap between our formal IR models, text emitters (`LLVM.lean`, `MLIRGPU.lean`, `Metal.lean`, `Hybrid.lean`), and real compilers, CI runs every conformance and fuzzed program across **(a)** stock Lean 4 C execution, **(b)** the formal `LNIR` interpreter (`evalCode` with zero leaked `HeapObj`s), and **(c)** compiled native binaries under **ASan/UBSan** ([`.github/workflows/roadmap-conformance.yml`](.github/workflows/roadmap-conformance.yml)), alongside multi-seed `LeanNative` vs. Rust checksum parity ([`docs/BENCH_RUST_PARITY.md`](docs/BENCH_RUST_PARITY.md)) and seeded emitter mutation kills ([`scripts/emitter_mutants.py`](scripts/emitter_mutants.py)). Unsupported `LCNF` or target constructs fail closed with zero artifact emitted.
4. **Explicit Vendor Toolchain TCB (`Trusted`, `Target IR -> Silicon`)**: Downstream vendor compilers and runtimes (`clang`/LLVM, `ptxas`/CUDA, Apple's Metal compiler, XLA/Pallas, the C compiler, Lean 4.35.0's kernel/`lean.h` runtime, OS loader, and hardware) form the Trusted Computing Base; `turbo-lean` does not verify binary machine code below Target IR.

---

## Quick Start & CLI Usage

```bash
# 1. Incremental Build, Theorem Check & Deterministic Eval
turbo-lean build [target...] [--seed-shards] [--project-dir <dir>]
turbo-lean check <file-or-dir> [--decl <id>] [--kernel auto|standard|con-leche|both] [--jobs <N>] [--max-memory-mb <MB>]
turbo-lean eval <file.lean> [--lean-path <paths>] [--timeout-ms <ms>] [--verify-determinism]

# 2. Agent Loop, Fast-Check (with Counterexample Triage) & Spec Audit
turbo-lean agent-step <file.lean> [--decl <id>] [--max-memory-mb <MB>]
turbo-lean fast-check <file.lean|kernel.cu> [--decl <id>] [--samples <N>]
turbo-lean audit-spec <file.lean>

# 3. Native & Accelerator Compilation (in `lean/`)
(cd lean && lake exe lean-native-core --target llvm|ptx|metal|mlir|c-abi <input.lean> -o <out>)
(cd lean && lake exe lean-native-core self-test)
(cd lean && lake exe turbo-lean-native self-test)

# 4. PR/CI Verification, Cryptographic Receipts & Portable CAS (.tlpack)
turbo-lean pr-verify [--base <git-ref>] [--mode untrusted|trusted] [--kernel auto|standard|con-leche|both] [--receipt <out.json>]
turbo-lean ci-verify [--base <git-ref>] [--mode untrusted|trusted] [--kernel auto|standard|con-leche|both] [--receipt <out.json>]
turbo-lean verify-receipt <receipt.json> [--verify-pubkey <hex-or-path>] [--require-signature]
turbo-lean export -o cache.tlpack && turbo-lean import cache.tlpack
```

### Verification & Policy Notes

- **Toolchain & Option Pinning**: Verdict-producing commands resolve `lean`, `lake`, and `leanc` strictly from the installed toolchain (`PATH` restricted to the toolchain plus `/usr/bin:/bin`). Lake compiler flags are validated against a static allowlist (`warn.sorry = true`, `debug.skipKernelTC = false`; `debug.*`, `internal.*`, `weak.*`, and `run_elab`/`run_cmd`/`run_meta` bypasses are rejected). Non-proof edits automatically re-verify reverse-dependent modules (`bwrap`-isolated in `--mode untrusted`).
- **Configurable Axiom & `@[csimp]` Policy (`turbo-lean.toml`)**: Projects using `bv_decide` or `native_decide` can allow auxiliary axioms via `[axioms] allow = ["*._native.bv_decide.ax_*"]` (resolved from `--base` in `pr-verify`; never `sorryAx` or `Lean.trustCompiler`) and `[csimp] allow = [...]`.
- **Worktree & Telemetry Controls**: Pass `--no-auto-worktree-link` (or `[worktree] auto_link = false`) to keep worktree build artifacts isolated without CAS hardlinking. Telemetry is local-only by default (`remote = false`) and can be disabled completely with `--no-telemetry`, `TURBO_LEAN_TELEMETRY=off`, or `turbo-lean telemetry disable`.

### GitHub Action (`uses: Th0rgal/turbo-lean@main`)

```yaml
- name: Incremental Lean 4 PR Verification
  uses: Th0rgal/turbo-lean@main
  with:
    project-dir: "."
    mode: "pr-verify"
    trust-mode: "untrusted"
    disallow-statement-changes: "true"
    receipt-path: "receipt.json"
    verify-receipt: "true"
```

---

## Benchmarks

- **Native Execution Parity ([`docs/BENCH_RUST_PARITY.md`](docs/BENCH_RUST_PARITY.md))**: Across the canonical `LNIR` kernel suite on Zen 5, optimized `LeanNative` achieves **0.875×** Rust execution time (**1.14×** throughput geomean, with bit-exact checksum parity across all seeds; algorithm-sensitive 256-bit EVM wins offset remaining array-kernel gaps). Reproduce with `python3 scripts/bench_rust_parity.py --trials 7`.
- **Incremental Proof Verification**: Warm single-theorem checks complete in **`~2.8 ms`** (`1,280×` faster than cold `lake env lean` on `verity`), full-repo `pr-verify` runs in **`~24 ms`**, in-process C-ABI counterexample triage takes **`~3 ns`**, and 256-bit GPU `fast-check` evaluates **`1.41B states/s`** on NVIDIA GB10.

---

## Repository Layout

- [`lean/TurboLean/`](lean/TurboLean/) — Incremental verification specs, C-ABI policy gates (`PolicyGates.lean`, `Spec.lean`), statement hashing, in-kernel axiom inspector, and warm `ZygoteWorker`.
- [`lean/LeanNative/`](lean/LeanNative/) — Verified `LNIR` compiler: `LCNF` bridge (`IR/`, `Frontend/`), verified optimization & superoptimization passes (`Transform/`), operational semantics (`Semantics/`), Target-IR ASTs & emitters (`Backend/`), and machine-checked soundness proofs (`Proofs/`).
- [`crates/turbo-lean/`](crates/turbo-lean/) — Rust CLI, MCP server, DAG module scheduler, `bwrap` sandboxed PR verifier, CAS/Zygote orchestrator, and C-ABI bridge.
- [`roadmap/`](roadmap/README.md) — North-Star goals ([`GOALS.md`](roadmap/GOALS.md)), cheat-proof theorem contracts ([`VALIDATION_CONTRACTS.md`](roadmap/VALIDATION_CONTRACTS.md)), 3-way differential conformance ([`CONFORMANCE_SUITE.md`](roadmap/CONFORMANCE_SUITE.md)), and Maxwell oracle pointer ([`MAXWELL_STRATEGIES.md`](roadmap/MAXWELL_STRATEGIES.md)).
