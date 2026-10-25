<p align="center">
  <img src="logo.svg" width="160" alt="turbo-lean" />
</p>

<h1 align="center">turbo-lean</h1>

<p align="center">
  <strong>Fast, incremental build, verification, and counterexample tooling for Lean 4.</strong>
</p>

`turbo-lean` is built around three practical goals:
1. **Make AI agent and automated verification loops nearly instantaneous**: verify a single edited theorem in **`~2 ms`** (via warm in-memory `ZygoteWorker` checkpoints and proof-irrelevant sharding) and reject false candidate lemmas in **`< 1 ms`** (via [`lean-native`](https://github.com/Th0rgal/lean-native) CPU SIMD / GPU execution) instead of waiting 10–60 seconds for `lake build`.
2. **Scale across parallel agent swarms and constrained hardware**: deduplicate concurrent work across worktrees with `flock` singleflight, share immutable `.olean` / shard blobs via hardlinks/reflinks, and bound memory usage (`--max-memory-mb`) with out-of-core disk checkpointing and `have`-block proof fission.
3. **Protect verification against reward-hacking or malicious models**: enforce in-kernel transitive axiom checks (`{propext, Quot.sound, Classical.choice}`), block macro-hidden `sorryAx` / `native_decide` / `extern` / `implemented_by` bypasses, pin theorem statements in the kernel so proofs cannot mutate their own types, and emit offline-verifiable cryptographic receipts.

---

## Two Distinct Execution Modes (`check` vs. `eval`)

A key architectural distinction in `turbo-lean` separates **adversarial theorem-proof verification** from **executable specification & mutation testing**:

1. **Adversarial Proof Verification Mode (`turbo-lean check` / `ci-verify` / `pr-verify` / `agent-step`)**:
   - **Target**: Untrusted LLM-generated theorem proofs (`theorem` / `lemma` declarations).
   - **Soundness Gate**: Enforces the strict in-kernel anti-reward-hacking gate (`0 sorryAx`, `0 native_decide` / `Lean.ofReduceBool` / `Lean.trustCompiler`, forbids `unsafe`, `@[extern]`, `@[implemented_by]`, unapproved `axiom`, and nested inductive "Sea Monsters" `inductiveInfo.isNested`), plus `< 10 µs` in-kernel `ConstantInfo.type` Statement Pinning.

2. **Deterministic Evaluation Mode (`turbo-lean eval <file.lean> [--lean-path ...] [--timeout-ms ...] [--verify-determinism]`)**:
   - **Target**: Drop-in **`~660x–700x`-faster** replacement for `lean <file.lean>` designed for specification & mutation benchmarks such as **[`lfglabs-dev/rust-specification-generation-benchmark` (`rsgb`)](https://github.com/lfglabs-dev/rust-specification-generation-benchmark)**.
   - **Semantics**: Executes `unsafe` / `Lean.Meta.evalExpr` / `#eval` / `#rsgb_test` / `#rsgb_kill` / `#rsgb_outputs` test drivers inside a warm `ZygoteWorker` (`enableInitializersExecution` enabled prior to `importModules`) *without* triggering the proof-only `unsafe` kernel blocker.
   - **100% Output & Diagnostic Parity**: Preserves every `MessageLog` entry (`info` / `warning` / `error` with exact `file:line:col` positions) and captured `IO.FS.Stream` `stdout` (`RSGB_RESULT`, `RSGB_KILL`, `RSGB_OUTPUTS`).
   - **Transitive `.olean` Dependency Hashing (`Law 6`)**: Hashes all transitively resolved `.olean` files across `LEAN_PATH` (`dep_interface_hashes`) into the `eval` cache key so rebuilt or mutated `.olean` libraries (e.g. `rsgb` mutant shims) never hit stale caches.
   - **Preemptive Timeout & Crash Recovery**: Enforces parent-side wall-clock timeouts (`SIGKILL` + `waitpid` `Drop` guard, exiting with code `124` / `RSGB_TIMEOUT`) and automatic worker respawn on crash/timeout, plus `--verify-determinism` to fail-closed on any divergence from fresh `lean <file.lean>`.

---

## How It Works

1. **Fast Feedback for Agents (`check`, `eval`, `fast-check`, `agent-step`)**
   - **Dependency-Cone Theorem Sharding**: Splits large Lean files into a proof-irrelevant prefix (`:= sorry` on prior theorems) and independent theorem shards keyed by their actual dependency cone (`cone_env_hash`). Editing a proof never invalidates downstream theorems or modules.
   - **Warm Zygote Worker Pool**: Keeps `Command.State` prefix checkpoints resident in memory and verifies single theorem edits or `#eval` property drivers in **`~2 ms`** with zero `.olean` reload overhead.
   - **CPU & GPU Counterexample Fast-Reject**: Integrates [`lean-native-core`](https://github.com/Th0rgal/lean-native) (`40 µs/req` JSON-RPC worker), CPU SIMD, NVIDIA CUDA, and Apple Metal to test candidate lemmas on millions of 64/256-bit states before running Lean tactics. Every reported counterexample is re-evaluated through the proved `LeanNative.Semantics.Eval` interpreter (`0%` false positives).

2. **Multi-Agent Caching & Low-Memory Execution (`state.db` + CAS)**
   - **SQLite (WAL) Coordinator + Content-Addressed Store (`~/.cache/turbo-lean/`)**: Stores `.olean`, `.ilean`, `.c`, and verified theorem receipts by `BLAKE3` digest (`0444` immutable blobs), materialized via reflinks (`FICLONE`) or hardlinks (`linkat`).
   - **Multi-Agent Singleflight**: Concurrent agents across separate worktrees coalesce identical build/check tasks automatically via `flock`.
   - **Memory Budget Governor & Disk Spill (`--max-memory-mb`)**: Adapts worker concurrency to available RAM, spills `/dev/shm` staging to SSD under memory pressure, and splits large proofs along `have h : P := by ...` cuts so heavy files verify within tight RAM limits without swap thrashing.

3. **Adversarial Verification & Soundness Guarantees (`ci-verify`, `pr-verify`)**
   - **In-Kernel Gate (`ZygoteWorker.lean` & `Inspector.lean`)**: Audits newly added constants directly in `Lean.Environment` (`collectAxioms`), blocking `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, unapproved `axiom`, `unsafe`, `@[extern]`, `@[implemented_by]`, and nested inductive types—even when hidden behind user macros.
   - **In-Kernel Statement Pinning**: Verifies in `< 10 µs` that metaprogramming inside a proof body has not altered the theorem's kernel `Expr` type.
   - **Verified Core Specification (`lean/TurboLean/Spec.lean` & `Assembler.lean`)**: The caching, cone-pruning, `.olean` dependency invalidation (`Law 6`), and incremental PR classification rules are specified and proved sound in Lean 4 (**<!-- inventory:turbo_tight_specs -->86/86<!-- /inventory:turbo_tight_specs --> tight specs** in `TurboLean/Spec.lean`, **<!-- inventory:turbo_cabi_exports -->55<!-- /inventory:turbo_cabi_exports --> C-ABI exports** in `TurboLean/Kernel.lean`, `0 sorryAx`).

---

## CLI Usage

```bash
# 1. Incremental Build & Single-Theorem Verification (Adversarial Proof Mode)
turbo-lean build [target...] [--seed-shards] [--project-dir <dir>]
turbo-lean check <file-or-dir> [--decl <id>] [--jobs <N>] [--max-memory-mb <MB>] [--low-memory]
turbo-lean seed-shards [--project-dir <dir>]

# 2. Deterministic Evaluation Mode (Drop-in 700x-faster `lean <file.lean>` for rsgb / #eval)
turbo-lean eval <file.lean> [--lean-path <colon-separated-paths>] \
  [--timeout-ms <ms>] [--verify-determinism] [--project-dir <dir>]

# 3. Agent Loop & Counterexample Fast-Check
turbo-lean agent-step <file.lean> [--decl <id>] [--max-memory-mb <MB>]
turbo-lean fast-check <file.lean|kernel.cu> [--decl <id>] [--samples <N>] \
  [--remote-http <http://host:port>] [--remote-ssh <user@host> --via-jump <jump>]
turbo-lean audit-spec <file.lean>

# 4. Git-Aware PR Verification & Cryptographic Receipts
turbo-lean pr-verify [--base <git-ref>] [--mode untrusted|trusted] \
  [--disallow-statement-changes] [--receipt <out.json>] [--project-dir <dir>]
turbo-lean ci-verify [--mode untrusted|trusted] [--receipt <out.json>] [--project-dir <dir>]
turbo-lean verify-receipt <receipt.json> [--expected-interface-hash <blake3>]

# 5. Distributed Cache Sync & Remote Offload Server
turbo-lean export -o cache.tlpack [--portable-only]
turbo-lean import cache.tlpack
turbo-lean sync <http://host:port> [--push] [--bidirectional]
turbo-lean serve [--listen 0.0.0.0:9400] [--gpu-enable]

# 6. Cache Status & Garbage Collection
turbo-lean status
turbo-lean gc [--max-reclaimable-bytes <bytes>]
```

Pass `--json` to any command for structured JSON output.

---

## GitHub Action (`uses: Th0rgal/turbo-lean@main`)

```yaml
steps:
  - uses: actions/checkout@v4
    with:
      fetch-depth: 0

  - name: Incremental Lean 4 PR Verification
    id: verify
    uses: Th0rgal/turbo-lean@main
    with:
      project-dir: "."
      mode: "pr-verify"
      base-ref: ${{ github.event.pull_request.base.sha || 'HEAD~1' }}
      trust-mode: "untrusted"
      disallow-statement-changes: "true"
      receipt-path: "receipt.json"
      verify-receipt: "true"
```

---

## Benchmarks

### 1. Real-World Repository: [`lfglabs-dev/verity`](https://github.com/lfglabs-dev/verity) (695 `.lean` Files, 9,275 Theorem Shards)

Full report: [`autoresearch/VERITY_BENCHMARK.md`](autoresearch/VERITY_BENCHMARK.md)

| Workload on `lfglabs-dev/verity` | Scope | Baseline `lake env lean` | `turbo-lean` (Zygote) | `turbo-lean` (Warm CAS) | Speedup |
| :--- | ---: | ---: | ---: | ---: | ---: |
| `Verity/Core.lean --decl Uint256.add_comm` | 1 / 53 | `3,587.5 ms` | **`2.80 ms`** (`18 ms` CLI) | **`4 ms`** | **`1,280x` / `897x`** |
| `Verity/Core.lean --decl writeAddressWord_wordToAddress` | 1 / 437 | `3,587.5 ms` | **`6.04 ms`** (`20 ms` CLI) | **`4 ms`** | **`594x` / `897x`** |
| `Verity/Proofs/Stdlib/Math.lean --decl safeAdd_isSome_iff_addNoOverflow` | 1 / 212 | `9,999.4 ms` | **`24.51 ms`** (`45 ms` CLI) | **`4 ms`** | **`408x` / `2,500x`** |
| `seed-shards` + `check .` (Full repository check) | 9,275 shards | `> 60,000 ms` | **`122.78 ms`** (seed) | **`70 ms`** | **`> 857x`** |
| `pr-verify --base HEAD` (1 proof edit in `Math.lean`) | 9,275 shards | `9,999.4 ms` | **`70.32 ms`** | **`23.89 ms`** | **`142x` / `419x`** |
| `verify-receipt` (Cryptographic BLAKE3 audit of all 695 files) | 9,275 shards | `> 10,000 ms` | **`0.58 ms`** | **`0.58 ms`** | **`17,390x`** |

### 2. Core Engine & Multi-Arch Latency (`autoresearch/run_eval.py` & `CROSS_ARCH_GPU_BENCHMARK.md`)

| Operation | Latency | Notes |
| :--- | ---: | :--- |
| **`lean-native-core worker` JSON-RPC (`M22`)** | **`0.04 ms` (`40 µs`)** | Certified counterexample & Alive2 TV check (`25,000 req/s`) |
| **Direct Kernel `Lean.addDecl` Replay (`M12`)** | **`0.42 ms` (`418 µs`)** | 4 theorems replayed directly in the kernel without tactics |
| **Warm `ZygoteWorker` New Proof Check (`M19`)** | **`1.94 ms`** | `0 µs` import reload (`Command.State` rollback) |
| **Single-Declaration `check --decl` (`M3` cold / `M4` warm)** | **`2.41 ms` / `1.95 ms`** | End-to-end CLI execution |
| **Incremental `pr-verify` on Proof Edit (`M16`)** | **`3.65 ms`** | Full-suffix BLAKE3 + statement-invariance check |
| **Warm `turbo-lean build` (`M2`) / Cold `ci-verify` (`M1`)** | **`8.02 ms` / `9.93 ms`** | Zero-read `/dev/shm` stat check + Ed25519 receipt |
| **1M-State 256-Bit GPU `fast-check` (NVIDIA GB10)** | **`0.71 ms`** | **`1,410 M states/s`** (`CuDenote` on `dgx-spark`) |
| **293-Mutant × 10k-Tx GPU Campaign (NVIDIA GB10)** | **`2.97 ms`** | **`292 / 293` mutants killed (`99.7%`)** |

---

## Repository Structure

- [`AGENTS.md`](AGENTS.md) — Architectural principles, invariants, and development roadmap.
- [`crates/turbo-lean/src/`](crates/turbo-lean/src/) — Rust CLI, native module DAG builder & per-module CAS (`module_builder.rs`, `lake_build.rs`), AST/scope splitter (`splitter.rs`), `/dev/shm` + SQLite CAS (`shm_cache.rs`, `db.rs`), `ZygoteWorker` & memory governor (`zygote.rs`, `check.rs`), `pr-verify` (`pr_verify.rs`), cryptographic receipts (`receipt.rs`), `.tlpack` sync (`pack.rs`, `server.rs`), and CPU/GPU/TPU Stage-1 fast-check (`accel_fastcheck.rs` / `gpu_fastcheck.rs`).
- [`lean/TurboLean/`](lean/TurboLean/) — Lean 4 specifications and kernel tools (`Kernel.lean` pure scalar C-ABI exports with zero C fallback, `Spec.lean`, `Assembler.lean`, `Inspector.lean`, `ZygoteWorker.lean`, `Reflection.lean`, `FastCheck.lean`).
- [`gpu/`](gpu/) — CUDA 256-bit fast-reject and mutation kernels (`CuDenote` / `CuMutate`).
- [`action.yml`](action.yml) — Reusable GitHub Action for Lean 4 CI.
- [`autoresearch/`](autoresearch/) — Evaluation and differential mutation test suite (`run_eval.py`).
