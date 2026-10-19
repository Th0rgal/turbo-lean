# AGENTS.md — Architecture, Decisions & Roadmap (`Th0rgal/turbo-lean`)

## 1. Mission & Core Invariants

`turbo-lean` is a high-velocity incremental verification, caching, and GPU-accelerated counterexample engine for Lean 4 (`v4.31.0`), tightly integrated with [`Th0rgal/lean-native` v0.3](https://github.com/Th0rgal/lean-native).

Every change to `turbo-lean` MUST preserve the 11 invariants enforced by [`autoresearch/run_eval.py`](autoresearch/run_eval.py):
1. **`invariants_passed`**: Zero `sorry`, zero `admit`, zero `native_decide`, zero `Lean.ofReduceBool`, zero `@[implemented_by]`/`@[extern]`, and zero unapproved `axiom` across all verified shards.
2. **`kernel_inspector_verified`**: In-kernel transitive axiom audit (`Lean.collectAxioms` in [`lean/TurboLean/Inspector.lean`](lean/TurboLean/Inspector.lean)) confirming all theorems depend strictly on `{propext, Quot.sound, Classical.choice}`.
3. **`kernel_expr_replay_verified`**: Direct `Lean.addDecl (.thmDecl ...)` kernel replay in [`lean/TurboLean/Assembler.lean`](lean/TurboLean/Assembler.lean) with zero tactic execution.
4. **`cryptographic_receipt_verified`**: Offline-verifiable `turbo-lean-verification-receipt-v1` (BLAKE3 + HMAC-BLAKE3 + Ed25519).
5. **`git_pr_verify_verified`**: Semantic Git diff (`pr-verify`) with full-suffix BLAKE3 integrity distinguishing proof-only edits from statement edits and auditing newly introduced hygiene violations.
6. **`multi_agent_singleflight_verified`**: Concurrent processes deduplicating identical shard verifications via `flock` + `/dev/shm`.
7. **`meta_spec_verified`**: 26 machine-checked soundness theorems in [`lean/TurboLean/Assembler.lean`](lean/TurboLean/Assembler.lean) + [`lean/TurboLean/Inspector.lean`](lean/TurboLean/Inspector.lean) proving shard proof irrelevance, cone locality, constraint propagation, macro-resistant kernel gating, and differential cache equivalence (`turboVerify_eq_kernelClean`).
8. **`stateful_ast_splitter_verified`**: Scope-aware tracking (`namespace`, `section`, `variable`, `open`, `mutual`, `@[simproc]`, local instances, pattern-matching theorems `| pat => ...`, and dependency cone `cone_env_hash`) in [`crates/turbo-lean/src/splitter.rs`](crates/turbo-lean/src/splitter.rs).
9. **`zygote_prefix_cow_verified`**: Persistent `ZygoteWorker` ([`lean/TurboLean/ZygoteWorker.lean`](lean/TurboLean/ZygoteWorker.lean)) caching `Command.State` checkpoints by `prefix_env_hash` with $O(1)$ rollback (~1.59 ms) and an in-kernel `auditNewKernelDecls` gate blocking macro-hidden `sorryAx` / `ofReduceBool` / `trustCompiler`.
10. **`lean_to_cuda_transpiler_verified`**: Fast counterexample rejection on 256-bit arithmetic and storage predicates with equality constraint propagation and vacuous-pass detection.
11. **`differential_mutation_oracle_verified`**: Chaos self-healing verification on corrupted `/dev/shm` entries and differential mutation checks (`2.25 ms`).

---

## 2. Codebase Layout (`crates/turbo-lean/src/` & `lean/TurboLean/`)

### Rust Layer (Thin Systems & I/O Shell)
- [`crates/turbo-lean/src/main.rs`](crates/turbo-lean/src/main.rs): CLI definition (`clap`) and top-level command dispatch (~518 lines).
- [`crates/turbo-lean/src/lake_build.rs`](crates/turbo-lean/src/lake_build.rs): Lake toolchain/env caching, `/dev/shm` `ShmProjectStatSummary`, `.olean` freshness tracking, and `build` command.
- [`crates/turbo-lean/src/check.rs`](crates/turbo-lean/src/check.rs): Single-declaration (`--decl`), single-file, and directory verification + `/dev/shm` `st_{stat_hash}.lock` singleflight.
- [`crates/turbo-lean/src/pr_verify.rs`](crates/turbo-lean/src/pr_verify.rs): `pr-verify`, `ci-verify`, `seed-shards`, and deduplicated Git tree semantic diffing (`PrClassificationAccum::classify_modified_file`).
- [`crates/turbo-lean/src/receipt.rs`](crates/turbo-lean/src/receipt.rs): Offline-verifiable `VerificationReceipt` (BLAKE3, HMAC-BLAKE3, Ed25519) and `verify-receipt` command.
- [`crates/turbo-lean/src/zygote.rs`](crates/turbo-lean/src/zygote.rs): Persistent `ZygoteWorker` process pool, `flock`-synchronized binary staging, and local daemon auto-start.
- [`crates/turbo-lean/src/gpu_fastcheck.rs`](crates/turbo-lean/src/gpu_fastcheck.rs): `fast-check` orchestration, equality constraint propagation, vacuous precondition detection, and stateless HTTP GPU offload (`dgx-spark` GB10).
- [`crates/turbo-lean/src/pack.rs`](crates/turbo-lean/src/pack.rs): `.tlpack` archive format, delta `sync`, HTTP client helpers, and atomic shared CAS blob prestaging.
- [`crates/turbo-lean/src/server.rs`](crates/turbo-lean/src/server.rs): Multi-threaded HTTP CAS & remote shard/GPU execution server (`turbo-lean serve`).
- [`crates/turbo-lean/src/shm_cache.rs`](crates/turbo-lean/src/shm_cache.rs): Unified `/dev/shm` atomic writer, schema versioning, `TURBO_LEAN_DEBUG` diagnostics, and bounded LRU quota eviction (`enforce_shm_quota_lru`).
- [`crates/turbo-lean/src/splitter.rs`](crates/turbo-lean/src/splitter.rs): Fast $O(N)$ lexical/structural Lean 4 command splitter, pattern-matching theorem support (`| pat => ...`), declaration dependency cone (`cone_env_hash`), and strict hygiene scanner (`sorry`, `axiom`, `native_decide`, `@[implemented_by]`, `@[extern]`, `unsafe`).
- [`crates/turbo-lean/src/db.rs`](crates/turbo-lean/src/db.rs): SQLite WAL metadata store + Content-Addressable Storage (CAS) with race-free atomic hardlinking/reflinking.

### Lean 4 Layer (Verified Kernel & Semantics Engine)
- [`lean/TurboLean/Inspector.lean`](lean/TurboLean/Inspector.lean): Programmatic `Lean.Environment` constant and transitive axiom auditor.
- [`lean/TurboLean/Assembler.lean`](lean/TurboLean/Assembler.lean): Direct kernel `Declaration.thmDecl` replay + 24 formal meta-theorems (`sharded_proof_irrelevance_sound`, `pr_verify_incremental_sound`, `turboVerify_eq_kernelClean`, `kernel_gate_blocks_macro_bypass`, `relative_cone_sorry_prefix_sound`).
- [`lean/TurboLean/ZygoteWorker.lean`](lean/TurboLean/ZygoteWorker.lean): Long-lived JSON-RPC worker holding `prefix_env_hash -> Command.State` checkpoints in memory + `auditNewKernelDecls` in-kernel gate.
- [`lean/TurboLean/Reflection.lean`](lean/TurboLean/Reflection.lean) & [`lean/TurboLean/FastCheck.lean`](lean/TurboLean/FastCheck.lean): 1,006 verified theorems (`0 sorry`, `0 native_decide`).

---

## 3. Roadmap: Deep Convergence with `Th0rgal/lean-native` v0.3

With [`Th0rgal/lean-native` v0.3](https://github.com/Th0rgal/lean-native) (`375a5ae`) now live, every major building block requested for `lean-native` is available and verified by **61 machine-checked theorems** (`0 sorryAx`):
- **`lean-native-core` (`libleanrt.a`-only, zero `import Lean`)**: `3.7 MB` stripped binary (`64.3x` smaller than `libleanshared.so`), **`2.45 ms`** cold start on ARM64 (`spark-de79`), and **`0.0716 ms/req`** (`13,973 req/s`) via its persistent `lean-native-core worker` JSON-RPC loop!
- **Lossless `LNIR_WIRE_V1` Wire & JSON Codec (`LeanNative.IR.Codec`)**: Allows `ZygoteWorker` (which already holds `libLean` warm in memory) to lower elaborated `LCNF` declarations into `LNIRModule.toWire` and stream them in `< 0.1 ms` to `lean-native-core worker`.
- **Native 256-Bit EVM (`u256`/`i256`) & `StorageMap` Semantics (`LeanNative.IR.Types`, `LeanNative.Semantics.Eval`)**: Checked 256-bit arithmetic (`addChecked256`, `subChecked256`, `mulChecked256`), 512-bit `mulDivDown`/`mulDivUp`, `storageLoad`/`storageStore`, and machine-checked store-to-load forwarding proofs (`storageStore_load_same_sound`, `storageStore_load_ne_sound`).
- **Verified Constraint-Propagating FastCheck & Counterexample Certifier (`LeanNative.Backend.FastCheck`)**:
  - `propagatePreconditionEqualities` + 256-bit boundary/WAD tables + pairwise collision sampling.
  - Emits vectorized LLVM 18 CPU SIMD (`--emit-llvm`) and NVIDIA PTX 8.0 (`--emit-ptx --sm sm_90`, 4-limb `.reg .u64` carry-chain `add.cc.u64`/`mad.lo.cc.u64`) kernels.
  - Formally proves `certifyCounterexample_no_false_positive`: every reported counterexample is re-evaluated through the proved `LeanNative.Semantics.Eval.evalCode` interpreter before emission, guaranteeing **0% false-positive counterexamples**.
- **Pure-Lean RFC BLAKE3 & Shared Schemas (`LeanNative.TurboLean.Adapter`)**: Bit-for-bit identical `"theorem-shard-v1:"` and `"turbo-lean-verification-receipt-v1"` BLAKE3 hashing in pure Lean 4 (`< 0.05 ms`, zero Python).

### Season 5 Action Plan (`turbo-lean` $\times$ `lean-native` v0.3)

1. **Chantier A — Replace Heuristic Rust String Transpilation in `gpu_fastcheck.rs` with `lean-native-core` (`compile-fastcheck` + `worker` + `eval-cex`)**:
   - Wire `crates/turbo-lean/src/gpu_fastcheck.rs` to probe and delegate to `lean-native-core worker` (`0.07 ms/req`) or `lean-native-core compile-fastcheck --emit-ptx / --emit-llvm` when available, while keeping the Rust kernel generator as an automatic fallback.
   - Certify every GPU/SIMD counterexample through `lean-native-core`'s `certifyCounterexample` (`certifyCounterexample_no_false_positive`), mathematically eliminating any risk of transpiler mismatch between Lean semantics and CUDA/LLVM execution.

2. **Chantier B — Embed `LNIR` Bridge inside `ZygoteWorker.lean` for Live LCNF $\to$ `LNIR_WIRE_V1` Extraction**:
   - In `ZygoteWorker.lean`, after elaborating a `def` or candidate `theorem` in the already-warm `Command.State`, extract its `LCNF` representation and serialize it to `LNIR_WIRE_V1` so `lean-native-core` can run Alive2 Symbolic Translation Validation (`validate-tv`), certificate verification (`verify-certs`), and PTX/LLVM fast-checking with **0 ms** frontend startup overhead.

3. **Chantier C — Unified High-Level Executable Specification (`lean/TurboLean/Spec.lean`)**:
   - Factor the pure decision logic (kernel extension hygiene gate `isSoundKernelExtension`, observational proof-irrelevance quotient `interfaceProj`, dependency cone Frame Rule, and incremental PR diff completeness `classifyModuleDiff`) into a single `0 import Lean` module `lean/TurboLean/Spec.lean` shared by both `ZygoteWorker.lean` and `Assembler.lean` (and compilable standalone via `lean-native-core`).

---

## 4. Environment & Verification Commands

```bash
export PATH="/var/lib/sandboxed-node/9304baf4-5074-4dad-8c26-2e2896f70f25/.cargo/bin:/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.31.0/bin:/var/lib/sandboxed-node/caches/elan/bin:$PATH"
export ELAN_HOME="/var/lib/sandboxed-node/caches/elan"

cargo build --release
cargo test --release
python3 autoresearch/run_eval.py
```
