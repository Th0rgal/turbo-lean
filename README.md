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
   - Block reward hacking on untrusted proofs: enforce in-kernel transitive axiom checks (`{propext, Quot.sound, Classical.choice}`), reject `sorryAx` / `native_decide` / `trustCompiler` / `unsafe` / `@[extern]` / `@[implemented_by]` bypasses, pin theorem statements from kernel declarations, select kernel engines fail-closed (`--kernel auto|standard|con-leche|both`, `--base`-isolated), and emit BLAKE3 provenance receipts (`schema_version = 2`, with optional Ed25519 signatures).
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

Registered soundness and refinement theorems in [`lean/LeanNative/Proofs/AxiomAudit.lean`](lean/LeanNative/Proofs/AxiomAudit.lean) (`#verify_lean_native_axioms`), alongside CI kernel replay across [`lean/TurboLean/Spec.lean`](lean/TurboLean/Spec.lean) and [`lean/LeanNative/Spec.lean`](lean/LeanNative/Spec.lean), are checked in the Lean 4 kernel against standard axioms `[propext, Quot.sound, Classical.choice]` with zero `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, or `Lean.trustCompiler`:

- **Frontend Lowering (`Lean.Compiler.LCNF -> LNIR`)**: Semantic refinement (`lowerRealLCNFCode_sound`, `lowerRealLCNFDecl_sound`) against the in-repo `RealLCNFSemantics` evaluator over upstream `Lean.Compiler.LCNF` declarations for the supported scalar, flat-tuple, and bounded Stage-1D constructor/ADT subset, plus retained LCNF proof facts (`ProofRetention.lean`) discharging bounds and exclusivity checks.
- **Middle-End Optimizations & Ownership/RC (`LNIR -> LNIR`)**: Machine-checked `CodeRefines` proofs across algebraic peepholes and equality saturation (`EqSat.lean`), structured loop scheduling and `parFor` kernel fusion (`LoopSchedule.lean`, `KernelFusionProofs.lean`), closure defunctionalization and ADT/slice lowering (`ClosureADTProofs.lean`, `SliceViewProofs.lean`), unboxed regions and Perceus/COW reference-counting elision (`UnboxedRegion.lean`, `OwnershipRC.lean`, `HeapObjAbiProofs.lean`), and zero-alloc stackless async state machines (`AsyncStateMachine.lean`).
- **Translation Validation & Certifying Superoptimization (`SymbolicTV` & `@[superopt]`)**: Unconditional structural `CodeRefines` soundness (`symbolicCodeRefines_sound` in `SymbolicTVRefinesSoundness.lean`) plus fuel-bounded symbolic execution (`SymbolicTVSoundness.lean`), alongside kernel-checked cost-guided and stochastic superoptimization (`SuperoptSoundness.lean`, `StochasticCert.lean`, `CostAutotune.lean`).
- **Backend AST Lowering & Host-Device ABI Contracts**: Semantic preservation for each supported `LNIR` fragment into **four typed Target-IR ASTs** (`lowerToLLVM_sound`, `lowerToPTX_sound`, `lowerToMetal_sound`, `lowerToStableHLO_sound`), verified **C99 ABI / `HeapObj` layout and zero-copy host-device dispatch contracts** (`validateHybridDispatch_sound`, `execZeroCopySliceIoHostCall_ok_sound`, `HeapObjAbiProofs.lean`), and tight non-vacuous C-ABI decision gates in [`lean/TurboLean/Spec.lean`](lean/TurboLean/Spec.lean) and [`lean/LeanNative/Spec.lean`](lean/LeanNative/Spec.lean).

*(Note: [`lean/TurboLean/ConLeche.lean`](lean/TurboLean/ConLeche.lean) and [`lean/TurboLean/ElabAudit.lean`](lean/TurboLean/ElabAudit.lean) prove CIC typechecking and statement-pinning soundness over a self-contained model; wiring official `leanprover/con-leche` to real `.olean` files remains `G1`/`G2`.)*

---

## Targeted IRs & Why We Can Trust Them

`LeanNative` formalizes **four typed Target-IR ASTs** with executable operational semantics in pure Lean 4, paired with **verified C99 ABI / `HeapObj` and host-device dispatch contracts**:

1. **LLVM IR (`LLVMAst`)** — Scalar, control-flow, memory, and generic LLVM vector IR (with text codegen targeting `x86_64` AVX2/AVX-512 and `aarch64` NEON), modeling exact `BitVec` arithmetic, `poison`/`nsw`/`nuw` propagation, and `disjointSlices`-backed `noalias` non-interference ([`lean/LeanNative/Backend/LLVMAst/`](lean/LeanNative/Backend/LLVMAst/)).
2. **NVIDIA CUDA PTX (`PTXAst`)** — SIMT GPU kernels (`sm_80`/`sm_90`), modeling warp/thread execution, shared/global memory race traps, per-barrier generation epochs (`bar.sync` with early-`ret` threads), and optional `po`/`rf`/`co`/`sw` weak-memory consistency ([`lean/LeanNative/Backend/PTXAst/`](lean/LeanNative/Backend/PTXAst/)).
3. **Apple Metal 3.0 MSL (`MetalAst`)** — Apple Silicon GPU kernels, modeling threadgroup execution, barriers, and disjoint buffer-offset bounds ([`lean/LeanNative/Backend/MetalAst/`](lean/LeanNative/Backend/MetalAst/)).
4. **Google TPU StableHLO (`StableHLOAst`)** — Shaped 1D/scalar `StableHLO` tensor programs ([`lean/LeanNative/Backend/StableHLOAst/`](lean/LeanNative/Backend/StableHLOAst/); companion JAX `Pallas` emission lives in `MLIRGPU.lean`).
5. **C99 ABI, `HeapObj` & Hybrid Dispatch Contracts (`CAbiEmit` / `Hybrid`)** — Verified C99 `struct` layouts, `lean.h` `HeapObj` header/RC conservation ([`docs/HEAPOBJ_CONTRACT.md`](docs/HEAPOBJ_CONTRACT.md)), and zero-copy host-device slice launch/marshaling contracts ([`lean/LeanNative/Backend/Hybrid.lean`](lean/LeanNative/Backend/Hybrid.lean), [`lean/LeanNative/Driver/CAbiEmit.lean`](lean/LeanNative/Driver/CAbiEmit.lean)).

Covered PTX kernels, Metal scalar/device functions and wrappers, and i64 StableHLO map/zip/saxpy/dot operations now share the typed AST printers with production emission. Parsers cover scalar PTX instructions/kernels, Metal scalar expressions/blocks/kernels, and a type-environment-threaded StableHLO constant/binary/dot/return function fragment. Kernel-checked roundtrips cover LLVM types, PTX types/predicate guards/register operands/returns, Metal canonical expressions/types/attributes/parameters/statements/blocks/kernels, and StableHLO element types/SSA names. Metal has general fuel-bounded roundtrips and canonical printer injectivity, with a kernel-lowering roundtrip corollary under explicit identifier-validity premises. The axiom audit contains 681 unique theorems. General PTX operand/instruction/kernel and StableHLO operation/function roundtrips and remaining lowerer-canonicality coverage remain open; executable sample roundtrip checks do not close those proof obligations. These Target-IR models are authored in-repo; upstream `lean-mlir`/`LNSym` integration and uncovered helper emission remain future work. Trusting compiled output relies on **four explicit layers**:

1. **In-Kernel Refinement Proofs (`Proven`)**: For each supported `LNIR` fragment and theorem precondition, `LNIR -> Target-IR AST` lowering and Hybrid dispatch validation are proved in the Lean 4 kernel to preserve modeled semantics without introducing modeled `poison`, out-of-bounds slice access, barrier divergence, or shared-memory races.
2. **Anti-Cheat Shadow-Semantics Gate (`Checked in CI`)**: [`scripts/check_shadow_semantics.lean`](scripts/check_shadow_semantics.lean) ([`docs/SHADOW_SEMANTICS.md`](docs/SHADOW_SEMANTICS.md), empty allowlist) checks the elaborated constant graph for forbidden `LNIR`-evaluator dependencies and verbatim/alpha-equivalent syntactic clones.
3. **Differential Conformance & Emitter Mutation Checks (`Tested in CI`)**: [The roadmap workflow](.github/workflows/roadmap-conformance.yml) runs Tier `C1`/`C4` scalar/tuple programs and `LCNF` fuzz cases 3-way across **(a)** stock Lean 4, **(b)** `evalCode`, and **(c)** native LLVM binaries compiled with **ASan** (plus **UBSan** on the C driver/link runtime), while Stage-1D `HeapObj` RC-conservation (`live_objects == 0`) runs 2-way against stock Lean (since `compile-llvm` rejects heap-ADT ops fail-closed until `G3.2`). The impact planner selects 16 seeds for narrowly classified changes, 50 for backend/runtime/unknown inputs, and 64 for main pushes or manual runs; standalone conformance defaults to 32. Docs-only PRs skip compilation only when non-documentation Git-tree digests also agree. Fast inventory, planner, and mutation-runner tests still run. Build caches use the input digest and never substitute for verification. In-kernel mutant kill proofs (`GPUEmitterMutantProofs.lean`, `LLVMEmitVerify.lean`) and `emitter_mutants.py --unit-tests` gate code PRs; the latter also checks that active M1–M10 each apply exactly once. Full mutation campaigns run on push/manual dispatch. Multi-seed Rust parity in [`docs/BENCH_RUST_PARITY.md`](docs/BENCH_RUST_PARITY.md) is benchmark evidence; Tiers `C2`/`C3` and GPU/TPU hardware qualification remain open under `G3.3`/`G5`.
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
turbo-lean fast-check <file.lean|kernel.cu> [--decl <id>] [--backend auto|cpu|gpu|tpu]
turbo-lean audit-spec <file.lean>

# 3. Native & Accelerator Compilation (`lean-native` for `.lean`; `lean-native-core` for LNIR wire/JSON)
(cd lean && lake exe lean-native compile-llvm --input <input.lean> -o <out.ll>)
(cd lean && lake exe lean-native compile-ptx|compile-metal|compile-mlir --input <input.lean> -o <out>)
(cd lean && lake exe lean-native emit-cabi-bindings --input <input.lean> --emit-header <out.h>)
(cd lean && lake exe lean-native-core self-test && lake exe turbo-lean-native self-test)

# 4. PR/CI Verification, Cryptographic Receipts & Portable CAS (.tlpack)
turbo-lean pr-verify [--base <git-ref>] [--mode untrusted|trusted] [--kernel auto|standard|con-leche|both] [--receipt <out.json>] [--signing-key <32-byte-hex>]
turbo-lean ci-verify [--base <git-ref>] [--mode untrusted|trusted] [--kernel auto|standard|con-leche|both] [--receipt <out.json>] [--signing-key <32-byte-hex>]
turbo-lean verify-receipt <receipt.json> [--verify-pubkey <32-byte-hex>] [--require-signature]  # pin expected signer via --verify-pubkey; require any signature via --require-signature
turbo-lean export -o cache.tlpack && turbo-lean import cache.tlpack
```

### Verification & Policy Notes

- **Toolchain & Option Pinning**: Verdict-producing commands resolve `lean`, `lake`, and `leanc` strictly from the installed toolchain (`PATH` restricted to the toolchain plus `/usr/bin:/bin`). Lake compiler flags are validated against a static allowlist (`warn.sorry = true`, `debug.skipKernelTC = false`; disallowed `debug.*` / `internal.*` / `weak.<disallowed>` options are rejected, and source/lakefile scanners reject `run_elab`/`run_cmd`/`run_meta` bypasses). Non-proof edits automatically re-verify reverse-dependent modules (`bwrap`-isolated in `--mode untrusted`).
- **Configurable Axiom & `@[csimp]` Policy (`turbo-lean.toml`)**: Projects using `bv_decide` or `native_decide` can allow auxiliary axioms via `[axioms] allow = ["*._native.bv_decide.ax_*"]` (resolved from `--base` in `pr-verify`; never `sorryAx` or `Lean.trustCompiler`) and `[csimp] allow = [...]`.
- **Worktree & Telemetry Controls**: Pass `--no-auto-worktree-link` (or `[worktree] auto_link = false`) to keep worktree build artifacts isolated without CAS hardlinking. Telemetry is local-only by default (`remote = false`) and can be disabled completely with `--no-telemetry`, `TURBO_LEAN_TELEMETRY=off`, or `turbo-lean telemetry disable`.

### GitHub Action (`uses: Th0rgal/turbo-lean@main`)

```yaml
- name: Incremental Lean 4 PR Verification
  uses: Th0rgal/turbo-lean@main
  with:
    project-dir: "."
    command: "pr-verify"
    mode: "untrusted"
    base-ref: "origin/main"
    disallow-statement-changes: "true"
    receipt-path: "receipt.json"
```

---

## Benchmarks

- **Native Execution Parity ([`docs/BENCH_RUST_PARITY.md`](docs/BENCH_RUST_PARITY.md))**: Across the canonical `LNIR` kernel suite on Zen 5, optimized `LeanNative` achieves **0.875×** Rust execution time (**1.14×** throughput geomean, with bit-exact checksum parity across the reported seed set; algorithm-sensitive 256-bit EVM wins offset remaining array-kernel gaps). Reproduce with `python3 scripts/bench_rust_parity.py --trials 7`.
- **Incremental Proof Verification (Reported Reference Measurements)**: Warm single-theorem checks on `lfglabs-dev/verity` (`Uint256.add_comm`, warm `ZygoteWorker`) reported **`2.80 ms`** (`1,280×` vs. `3,587.5 ms` cold `lake env lean`), cached `pr-verify --base HEAD` across `verity` (9,275 shards) reported **`23.89 ms`**, in-process C-ABI counterexample triage measured **`~3 ns`** vs. `40 µs` JSON-RPC IPC, and 1M-state 256-bit GPU `fast-check` (`CuDenote` on NVIDIA GB10) reported **`1.41B states/s`** (`0.71 ms`).

---

## Repository Layout

- [`lean/TurboLean/`](lean/TurboLean/) — Incremental verification specs, C-ABI policy gates (`PolicyGates.lean`, `Spec.lean`), statement hashing, in-kernel axiom inspector, and warm `ZygoteWorker`.
- [`lean/LeanNative/`](lean/LeanNative/) — Verified `LNIR` compiler: `LCNF` bridge (`IR/`, `Frontend/`), verified optimization & superoptimization passes (`Transform/`), operational semantics (`Semantics/`), Target-IR ASTs & emitters (`Backend/`), and machine-checked soundness proofs (`Proofs/`).
- [`crates/turbo-lean/`](crates/turbo-lean/) — Rust CLI, MCP server, DAG module scheduler, `bwrap` sandboxed PR verifier, CAS/Zygote orchestrator, and C-ABI bridge.
- [`roadmap/`](roadmap/README.md) — North-Star goals ([`GOALS.md`](roadmap/GOALS.md)), cheat-proof theorem contracts ([`VALIDATION_CONTRACTS.md`](roadmap/VALIDATION_CONTRACTS.md)), 3-way differential conformance ([`CONFORMANCE_SUITE.md`](roadmap/CONFORMANCE_SUITE.md)), and Maxwell oracle pointer ([`MAXWELL_STRATEGIES.md`](roadmap/MAXWELL_STRATEGIES.md)).
