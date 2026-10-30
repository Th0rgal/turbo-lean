<p align="center">
  <img src="logo.svg" width="160" alt="turbo-lean" />
</p>

<h1 align="center">turbo-lean</h1>

<p align="center">
  <strong>Incremental verification, counterexample triage, and verified native/SIMD/GPU/TPU compilation for Lean 4.</strong>
</p>

`turbo-lean` unifies the incremental verification oracle (`TurboLean`) and the verified native compiler (`LeanNative`) on top of [`lean-sys`](https://github.com/Th0rgal/lean-sys):
1. **Sub-2ms Agent & Proof Verification Loops**: Verify edited theorems in **`~2 ms`** via warm `ZygoteWorker` checkpoints, reject false lemmas in **`< 1 ms`** on CPU SIMD / CUDA / Metal, and certify & triage counterexamples (`CandidateBug | SpecTooStrong | ReferenceDiscrepancy`) in **`~3 ns`** via in-process C-ABI gates.
2. **Verified Native Compilation & Acceleration Plugins (`@[simd]`, `@[gpu]`, `@[tpu]`)**: Lower pure Lean 4 / `LNIR` kernels to zero-copy C99/Rust FFI, AVX2 / AVX-512 / ARM64 NEON SIMD, NVIDIA CUDA PTX, Apple Metal 3.0 MSL, and Google Cloud TPU v6e (`StableHLO` / `Pallas`) with **203 kernel-checked refinement & soundness theorems** (`<!-- inventory:leannative_tight_specs -->120/120<!-- /inventory:leannative_tight_specs -->` tight specs in `LeanNative/Spec.lean`, `0 sorryAx`).
3. **Adversarial Anti-Reward-Hacking Gate**: Enforce in-kernel transitive axiom checks (`{propext, Quot.sound, Classical.choice}`), block macro-hidden `sorryAx` / `native_decide` / `extern` / `implemented_by` / `unsafe` bypasses, pin theorem statements in `< 10 µs`, and emit Ed25519/BLAKE3 receipts.

---

## Execution Modes (`check`, `eval`, and `LeanNative` Compilation)

1. **Adversarial Proof Verification (`turbo-lean check` / `ci-verify` / `pr-verify` / `agent-step`)**:
   - Audits untrusted theorem proofs in the Lean 4 kernel (`0 sorryAx`, `0 native_decide` / `Lean.ofReduceBool` / `Lean.trustCompiler`, no `unsafe`, `@[extern]`, `@[implemented_by]`, unapproved `axiom`, or nested inductive types) with `< 10 µs` `ConstantInfo.type` Statement Pinning.
   - Projects that accept the auxiliary axioms of `native_decide` / `bv_decide` in some proofs allow them in `turbo-lean.toml` (`[axioms] allow = ["*._native.native_decide.ax_*", "*._native.bv_decide.ax_*"]`, `*` globs, never `sorryAx` or `Lean.trustCompiler`); `check`, `agent-step`, trusted `ci-verify` and `pr-verify` (which reads the policy at `--base`) apply it.
   - Only an edit confined to theorem proof bodies is checked per declaration (proof irrelevance). Any other edit (statement, `def`, instance, attribute, option, import, new or deleted file; for `--decl`, a change of that theorem's statement) makes `pr-verify`, `check` and `agent-step` re-check the edited modules and every module that imports them (`bwrap`-sandboxed native module compilation + `--audit-modules` in `pr-verify --mode untrusted`; `lake build` or `[lake] build_command` in `turbo-lean.toml` in trusted mode), so dependents in other files are checked; without a Lake config they refuse to pass.
   - Per-theorem zygote timeout: `check --timeout <secs>`, `[zygote] timeout_secs` in `turbo-lean.toml`, or `TURBO_LEAN_TIMEOUT_MS` (default 30 s); daemons and their HTTP clients follow it.
2. **Deterministic Evaluation (`turbo-lean eval <file.lean> [--lean-path ...] [--timeout-ms ...] [--verify-determinism]`)**:
   - Drop-in **`~660x–700x`-faster** replacement for `lean <file.lean>` on specification & mutation benchmarks (`rsgb`), preserving 100% of `MessageLog` diagnostics, captured `stdout`, and transitive `.olean` dependency hashes (`Law 6`).
3. **Verified Native & Accelerator Compilation (`lean/LeanNative` — `lean-native` / `lean-native-core`)**:
   - **Segregated Acceleration Plugins (`@[simd]`, `@[gpu]`, `@[tpu]`, `@[superopt]`)**: Rewrites and lowers `LNIR` (`letBind`, `incRef`, `decRef`, `call`, `parFor`, 256-bit EVM/UInt256 arithmetic) with Alive2-style symbolic translation validation (`SymbolicTV.lean`) and cost-guided superoptimization (`Superopt.lean`).
   - **Zero-Runtime C-ABI & Multi-Target Codegen**: Emits standalone `.c` / `.h` / `.rs` static libraries (`--emit-c-abi`), LLVM IR (`x86_64` AVX2/AVX-512, `aarch64` NEON), CUDA PTX (`sm_80`/`sm_90`), Apple Metal 3.0 (`.metal`), and Cloud TPU v6e (`StableHLO` MLIR & JAX `Pallas`).
   - **System Interactions via [`lean-sys`](https://github.com/Th0rgal/lean-sys)**: `LeanNative` focuses on pure compute and hardware acceleration. If your compiled native Lean 4 program needs to interact with the operating system (POSIX I/O, crash-atomic WAL/CAS storage, composite-key tables, `/dev/shm` shared-memory IPC, subprocess sandboxing, or HTTP/1.1 & JSON-RPC 2.0 servers with `0 import Lean` and `libleanrt.a`-only), pair it with [`lean-sys`](https://github.com/Th0rgal/lean-sys).

---

## Architecture & Soundness Guarantees

1. **In-Process C-ABI Oracle & Counterexample Triage (`libturbo_spec_cabi.a`)**
   - Links **<!-- inventory:turbo_cabi_exports -->78<!-- /inventory:turbo_cabi_exports --> zero-runtime C-ABI symbols** (`43 turbo_spec_*` + `26 leansys_*` + `9 leannative_*`/`lean_native_*`) directly into the binary, verified at compile time via `nm` (`owner_count == 1`, `0` undefined symbols).
   - Evaluates candidate counterexamples in-process through `leannative_certify_cex_witnesses`, `leannative_fastcheck_rewrite_step`, and `leansys_verify_counterexample_triage`, classifying every falsified conjecture into `CandidateBug`, `SpecTooStrong` (vacuous precondition), or `ReferenceDiscrepancy` (domain hazard such as div/mod by zero or shift `>= 64`).
2. **Multi-Agent CAS & Memory Governor (`~/.cache/turbo-lean/`)**
   - Coalesces concurrent builds across worktrees via `flock` singleflight, shares immutable `BLAKE3`-addressed `.olean`/shard blobs via reflinks/hardlinks, and bounds RAM (`--max-memory-mb`) with `have`-block proof fission.
3. **Tight Formal Specifications (`0 sorryAx`)**
   - **<!-- inventory:turbo_tight_specs -->96/96<!-- /inventory:turbo_tight_specs --> tight specs** in [`lean/TurboLean/Spec.lean`](lean/TurboLean/Spec.lean), **<!-- inventory:leannative_tight_specs -->120/120<!-- /inventory:leannative_tight_specs --> tight specs** in [`lean/LeanNative/Spec.lean`](lean/LeanNative/Spec.lean), and **37/37 tight specs** in [`lean-sys`](https://github.com/Th0rgal/lean-sys).

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

# 3. Native & Accelerator Compilation + Multi-Threaded Native Orchestrator (in `lean/`)
(cd lean && lake exe lean-native-core --target llvm|ptx|metal|mlir|c-abi <input.lean> -o <out>)
(cd lean && lake exe lean-native-core self-test)
(cd lean && lake exe turbo-lean-native self-test)

# 4. PR/CI Verification, Cryptographic Receipts & Portable CAS (.tlpack)
turbo-lean pr-verify [--base <git-ref>] [--mode untrusted|trusted] [--receipt <out.json>]
turbo-lean ci-verify [--mode untrusted|trusted] [--receipt <out.json>]
turbo-lean export -o cache.tlpack && turbo-lean import cache.tlpack

# 5. Telemetry & Local Agent Analytics
turbo-lean telemetry [status|enable|disable|local]
turbo-lean --no-telemetry check <file.lean>
```

---

## Telemetry & Privacy

- **Local-only by default**: Out of the box (`enabled = true`, `remote = false`, `mode = "metrics"`), `turbo-lean` records local timing, cache-hit, and token-compaction counters in `/dev/shm` (`turbo-lean analytics`) and `~/.cache/turbo-lean/telemetry/` without making any network requests or storing raw source blobs.
- **Opt-in remote reporting**: Remote metrics upload is disabled unless explicitly enabled via `turbo-lean telemetry enable`, `--telemetry opt-in` / `--telemetry remote`, `TURBO_LEAN_TELEMETRY=remote`, `SANDBOXED_TELEMETRY_TOKEN`, or `remote = true` in `[telemetry]`.
- **Full disable**: Pass `--no-telemetry` (or `--telemetry off`), set `TURBO_LEAN_TELEMETRY=off` (`0`/`false`/`no`), run `turbo-lean telemetry disable` (persists to `~/.config/turbo-lean/config.toml`), or configure `<project_dir>/turbo-lean.toml`:
  ```toml
  [telemetry]
  enabled = false   # disables all local and remote telemetry
  remote = false    # keep false unless opting into remote reporting
  mode = "off"      # "off" | "local" | "metrics" | "full"
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

- [`lean/TurboLean/`](lean/TurboLean/) — Incremental verification specifications, multi-threaded native orchestrator (`Orchestrator.lean`), & kernel tools (`Spec.lean`, `Kernel.lean`, `Assembler.lean`, `Inspector.lean`, `ZygoteWorker.lean`, `Reflection.lean`, `FastCheck.lean`).
- [`lean/LeanNative/`](lean/LeanNative/) — Verified `LNIR` native compiler, `@[simd]`/`@[gpu]`/`@[tpu]` plugins (`Transform/Plugins.lean`, `Superopt.lean`), semantics & 207 soundness theorems (`Semantics/Eval.lean`, `Proofs/`), and multi-backend codegen (`Backend/LLVM.lean`, `PTX.lean`, `Metal.lean`, `MLIR.lean`, `FastCheck.lean`).
- [`crates/turbo-lean/src/`](crates/turbo-lean/src/) — CLI & system orchestrator (`c_abi.rs` 72-symbol FFI bridge, `module_builder.rs` event-driven ready-queue DAG scheduler, `accelerators.rs` & `gpu_fastcheck.rs` multi-domain `UInt`/`BitVec`/`Word256`/`Nat` counterexample engines, `zygote.rs`, `splitter.rs`, `pr_verify.rs`, `mcp.rs`).
- [`roadmap/`](roadmap/README.md) — Autonomous research & verification roadmap separating North-Star technical goals ([`GOALS.md`](roadmap/GOALS.md)), cheat-proof theorem contracts ([`VALIDATION_CONTRACTS.md`](roadmap/VALIDATION_CONTRACTS.md)), 3-way non-FV differential conformance ([`CONFORMANCE_SUITE.md`](roadmap/CONFORMANCE_SUITE.md)), and Maxwell/Orb execution strategies ([`MAXWELL_STRATEGIES.md`](roadmap/MAXWELL_STRATEGIES.md)).
