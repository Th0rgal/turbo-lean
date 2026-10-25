<p align="center">
  <img src="logo.svg" width="160" alt="turbo-lean" />
</p>

<h1 align="center">turbo-lean</h1>

<p align="center">
  <strong>Incremental verification, counterexample triage, and verified native/SIMD/GPU/TPU compilation for Lean 4.</strong>
</p>

`turbo-lean` unifies the incremental verification oracle (`TurboLean`) and the verified native compiler (`LeanNative`) on top of [`lean-sys`](https://github.com/Th0rgal/lean-sys):
1. **Sub-2ms Agent & Proof Verification Loops**: Verify edited theorems in **`~2 ms`** via warm `ZygoteWorker` checkpoints, reject false lemmas in **`< 1 ms`** on CPU SIMD / CUDA / Metal, and certify & triage counterexamples (`CandidateBug | SpecTooStrong | ReferenceDiscrepancy`) in **`~3 ns`** via in-process C-ABI gates.
2. **Verified Native Compilation & Acceleration Plugins (`@[simd]`, `@[gpu]`, `@[tpu]`)**: Lower pure Lean 4 / `LNIR` kernels to zero-copy C99/Rust FFI, AVX2 / AVX-512 / ARM64 NEON SIMD, NVIDIA CUDA PTX, Apple Metal 3.0 MSL, and Google Cloud TPU v6e (`StableHLO` / `Pallas`) with **199 kernel-checked refinement & soundness theorems** (`106/106` tight specs in `LeanNative/Spec.lean`, `0 sorryAx`).
3. **Adversarial Anti-Reward-Hacking Gate**: Enforce in-kernel transitive axiom checks (`{propext, Quot.sound, Classical.choice}`), block macro-hidden `sorryAx` / `native_decide` / `extern` / `implemented_by` / `unsafe` bypasses, pin theorem statements in `< 10 µs`, and emit Ed25519/BLAKE3 receipts.

---

## Execution Modes (`check`, `eval`, and `LeanNative` Compilation)

1. **Adversarial Proof Verification (`turbo-lean check` / `ci-verify` / `pr-verify` / `agent-step`)**:
   - Audits untrusted theorem proofs in the Lean 4 kernel (`0 sorryAx`, `0 native_decide` / `Lean.ofReduceBool` / `Lean.trustCompiler`, no `unsafe`, `@[extern]`, `@[implemented_by]`, unapproved `axiom`, or nested inductive types) with `< 10 µs` `ConstantInfo.type` Statement Pinning.
2. **Deterministic Evaluation (`turbo-lean eval <file.lean> [--lean-path ...] [--timeout-ms ...] [--verify-determinism]`)**:
   - Drop-in **`~660x–700x`-faster** replacement for `lean <file.lean>` on specification & mutation benchmarks (`rsgb`), preserving 100% of `MessageLog` diagnostics, captured `stdout`, and transitive `.olean` dependency hashes (`Law 6`).
3. **Verified Native & Accelerator Compilation (`lean/LeanNative` — `lean-native` / `lean-native-core`)**:
   - **Segregated Acceleration Plugins (`@[simd]`, `@[gpu]`, `@[tpu]`, `@[superopt]`)**: Rewrites and lowers `LNIR` (`letBind`, `incRef`, `decRef`, `call`, `parFor`, 256-bit EVM/UInt256 arithmetic) with Alive2-style symbolic translation validation (`SymbolicTV.lean`) and cost-guided superoptimization (`Superopt.lean`).
   - **Zero-Runtime C-ABI & Multi-Target Codegen**: Emits standalone `.c` / `.h` / `.rs` static libraries (`--emit-c-abi`), LLVM IR (`x86_64` AVX2/AVX-512, `aarch64` NEON), CUDA PTX (`sm_80`/`sm_90`), Apple Metal 3.0 (`.metal`), and Cloud TPU v6e (`StableHLO` MLIR & JAX `Pallas`).

---

## Architecture & Soundness Guarantees

1. **In-Process C-ABI Oracle & Counterexample Triage (`libturbo_spec_cabi.a`)**
   - Links **<!-- inventory:turbo_cabi_exports -->63<!-- /inventory:turbo_cabi_exports --> zero-runtime C-ABI symbols** (`38 turbo_spec_*` + `20 leansys_*` + `5 leannative_*`) directly into the binary, verified at compile time via `nm` (`owner_count == 1`, `0` undefined symbols).
   - Evaluates candidate counterexamples in-process through `leannative_certify_cex_witnesses`, `leannative_fastcheck_rewrite_step`, and `leansys_verify_counterexample_triage`, classifying every falsified conjecture into `CandidateBug`, `SpecTooStrong` (vacuous precondition), or `ReferenceDiscrepancy` (domain hazard such as div/mod by zero or shift `>= 64`).
2. **Multi-Agent CAS & Memory Governor (`~/.cache/turbo-lean/`)**
   - Coalesces concurrent builds across worktrees via `flock` singleflight, shares immutable `BLAKE3`-addressed `.olean`/shard blobs via reflinks/hardlinks, and bounds RAM (`--max-memory-mb`) with `have`-block proof fission.
3. **Tight Formal Specifications (`0 sorryAx`)**
   - **<!-- inventory:turbo_tight_specs -->89/89<!-- /inventory:turbo_tight_specs --> tight specs** in [`lean/TurboLean/Spec.lean`](lean/TurboLean/Spec.lean), **106/106 tight specs** in [`lean/LeanNative/Spec.lean`](lean/LeanNative/Spec.lean), and **36/36 tight specs** in [`lean-sys`](https://github.com/Th0rgal/lean-sys).

---

## CLI Usage

```bash
# 1. Incremental Build, Theorem Check & Deterministic Eval
turbo-lean build [target...] [--seed-shards] [--project-dir <dir>]
turbo-lean check <file-or-dir> [--decl <id>] [--jobs <N>] [--max-memory-mb <MB>]
turbo-lean eval <file.lean> [--lean-path <paths>] [--timeout-ms <ms>] [--verify-determinism]

# 2. Agent Loop, Fast-Check (with Counterexample Triage) & Spec Audit
turbo-lean agent-step <file.lean> [--decl <id>] [--max-memory-mb <MB>]
turbo-lean fast-check <file.lean|kernel.cu> [--decl <id>] [--samples <N>]
turbo-lean audit-spec <file.lean>

# 3. Native & Accelerator Compilation (LeanNative CLI in `lean/`)
(cd lean && lake exe lean-native-core --target llvm|ptx|metal|mlir|c-abi <input.lean> -o <out>)
(cd lean && lake exe lean-native-core self-test)

# 4. PR/CI Verification, Cryptographic Receipts & Portable CAS (.tlpack)
turbo-lean pr-verify [--base <git-ref>] [--mode untrusted|trusted] [--receipt <out.json>]
turbo-lean ci-verify [--mode untrusted|trusted] [--receipt <out.json>]
turbo-lean export -o cache.tlpack && turbo-lean import cache.tlpack
```

---

## GitHub Action (`uses: Th0rgal/turbo-lean@main`)

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

| Workload / Operation | Baseline `lake env lean` | `turbo-lean` | Speedup / Notes |
| :--- | ---: | ---: | :--- |
| **`lfglabs-dev/verity` (`Uint256.add_comm`, 1/53 decls)** | `3,587.5 ms` | **`2.80 ms`** | **`1,280x`** (warm `ZygoteWorker`) |
| **`lfglabs-dev/verity` (`pr-verify --base HEAD`, 9,275 shards)** | `9,999.4 ms` | **`23.89 ms`** | **`419x`** (full-suffix BLAKE3 + statement pinning) |
| **`verify-receipt` (695 files, 9,275 shards)** | `> 10,000 ms` | **`0.58 ms`** | **`17,390x`** |
| **In-Process C-ABI `FastCheck` & Counterexample Triage** | `40 µs` (IPC) | **`~0.003 µs` (`3 ns`)** | **`~13,000x`** vs JSON-RPC subprocess |
| **1M-State 256-Bit GPU `fast-check` (NVIDIA GB10)** | — | **`0.71 ms`** | **`1,410 M states/s`** (`CuDenote` on `dgx-spark`) |
| **293-Mutant × 10k-Tx GPU Campaign (NVIDIA GB10)** | — | **`2.97 ms`** | **`292 / 293` mutants killed (`99.7%`)** |

---

## Repository Structure

- [`lean/TurboLean/`](lean/TurboLean/) — Incremental verification specifications & kernel tools (`Spec.lean`, `Kernel.lean`, `Assembler.lean`, `Inspector.lean`, `ZygoteWorker.lean`, `Reflection.lean`, `FastCheck.lean`).
- [`lean/LeanNative/`](lean/LeanNative/) — Verified `LNIR` native compiler, `@[simd]`/`@[gpu]`/`@[tpu]` plugins (`Transform/Plugins.lean`, `Superopt.lean`), semantics & 199 soundness theorems (`Semantics/Eval.lean`, `Proofs/`), and multi-backend codegen (`Backend/LLVM.lean`, `PTX.lean`, `Metal.lean`, `MLIR.lean`, `FastCheck.lean`).
- [`crates/turbo-lean/src/`](crates/turbo-lean/src/) — CLI & system orchestrator (`c_abi.rs` 63-symbol FFI bridge, `zygote.rs`, `splitter.rs`, `pr_verify.rs`, `gpu_fastcheck.rs`, `mcp.rs`).
- [`gpu/`](gpu/) & [`autoresearch/`](autoresearch/) — CUDA 256-bit kernels (`CuDenote`/`CuMutate`) and benchmark suite.
