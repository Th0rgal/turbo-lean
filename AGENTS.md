# AGENTS.md — Architecture, Decisions & Roadmap (`Th0rgal/turbo-lean`)

## 1. Mission & Core Invariants

`turbo-lean` is a high-velocity incremental verification, caching, and GPU-accelerated counterexample engine for Lean 4 (`v4.31.0`).

Every change to `turbo-lean` MUST preserve the 10 invariants enforced by [`autoresearch/run_eval.py`](autoresearch/run_eval.py):
1. **`invariants_passed`**: Zero `sorry`, zero `admit`, zero `native_decide`, zero `Lean.ofReduceBool`, and zero unapproved `axiom` across all verified shards.
2. **`kernel_inspector_verified`**: In-kernel transitive axiom audit (`Lean.collectAxioms` in [`lean/TurboLean/Inspector.lean`](lean/TurboLean/Inspector.lean)) confirming all theorems depend strictly on `{propext, Quot.sound, Classical.choice}`.
3. **`kernel_expr_replay_verified`**: Direct `Lean.addDecl (.thmDecl ...)` kernel replay in [`lean/TurboLean/Assembler.lean`](lean/TurboLean/Assembler.lean) with zero tactic execution.
4. **`cryptographic_receipt_verified`**: Offline-verifiable `turbo-lean-verification-receipt-v1` (BLAKE3 + HMAC-BLAKE3 + Ed25519).
5. **`git_pr_verify_verified`**: Semantic Git diff (`pr-verify`) distinguishing proof-only edits from statement edits and auditing newly introduced hygiene violations.
6. **`multi_agent_singleflight_verified`**: Concurrent processes deduplicating identical shard verifications via `flock` + `/dev/shm`.
7. **`meta_spec_verified`**: Machine-checked soundness theorems in [`lean/TurboLean/Assembler.lean`](lean/TurboLean/Assembler.lean) proving shard proof irrelevance and incremental `pr-verify` soundness.
8. **`stateful_ast_splitter_verified`**: Scope-aware tracking (`namespace`, `section`, `variable`, `open`, `mutual`, `@[simproc]`, local instances) in [`crates/turbo-lean/src/splitter.rs`](crates/turbo-lean/src/splitter.rs).
9. **`zygote_prefix_cow_verified`**: Persistent `ZygoteWorker` ([`lean/TurboLean/ZygoteWorker.lean`](lean/TurboLean/ZygoteWorker.lean)) caching `Command.State` checkpoints by `prefix_env_hash` with $O(1)$ rollback (~1.6 ms).
10. **`lean_to_cuda_transpiler_verified`**: Fast counterexample rejection on 256-bit arithmetic and storage predicates.

---

## 2. Codebase Layout (`crates/turbo-lean/src/` & `lean/TurboLean/`)

### Rust Layer (Thin Systems & I/O Shell)
- [`crates/turbo-lean/src/main.rs`](crates/turbo-lean/src/main.rs): CLI definition (`clap`) and top-level command dispatch (~518 lines).
- [`crates/turbo-lean/src/lake_build.rs`](crates/turbo-lean/src/lake_build.rs): Lake toolchain/env caching, `/dev/shm` `ShmProjectStatSummary`, `.olean` freshness tracking, and `build` command.
- [`crates/turbo-lean/src/check.rs`](crates/turbo-lean/src/check.rs): Single-declaration (`--decl`), single-file, and directory verification + `/dev/shm` `st_{stat_hash}.lock` singleflight.
- [`crates/turbo-lean/src/pr_verify.rs`](crates/turbo-lean/src/pr_verify.rs): `pr-verify`, `ci-verify`, `seed-shards`, `verify-receipt`, and cryptographic receipt tests.
- [`crates/turbo-lean/src/zygote.rs`](crates/turbo-lean/src/zygote.rs): Persistent `ZygoteWorker` process pool, `flock`-synchronized binary staging, and local daemon auto-start.
- [`crates/turbo-lean/src/gpu_fastcheck.rs`](crates/turbo-lean/src/gpu_fastcheck.rs): `fast-check` orchestration and stateless HTTP GPU offload (`dgx-spark` GB10).
- [`crates/turbo-lean/src/pack.rs`](crates/turbo-lean/src/pack.rs): `.tlpack` archive format, delta `sync`, HTTP CAS server (`serve`), and atomic shared CAS blob prestaging.
- [`crates/turbo-lean/src/splitter.rs`](crates/turbo-lean/src/splitter.rs): Fast $O(N)$ lexical/structural Lean 4 command splitter and hygiene scanner.
- [`crates/turbo-lean/src/db.rs`](crates/turbo-lean/src/db.rs): SQLite WAL metadata store + Content-Addressable Storage (CAS) with race-free atomic hardlinking/reflinking.

### Lean 4 Layer (Verified Kernel & Semantics Engine)
- [`lean/TurboLean/Inspector.lean`](lean/TurboLean/Inspector.lean): Programmatic `Lean.Environment` constant and transitive axiom auditor.
- [`lean/TurboLean/Assembler.lean`](lean/TurboLean/Assembler.lean): Direct kernel `Declaration.thmDecl` replay + formal meta-theorems (`sharded_proof_irrelevance_sound`, `pr_verify_incremental_sound`).
- [`lean/TurboLean/ZygoteWorker.lean`](lean/TurboLean/ZygoteWorker.lean): Long-lived JSON-RPC worker holding `prefix_env_hash -> Command.State` checkpoints in memory.
- [`lean/TurboLean/Reflection.lean`](lean/TurboLean/Reflection.lean) & [`lean/TurboLean/FastCheck.lean`](lean/TurboLean/FastCheck.lean): 1,006 verified theorems (`0 sorry`, `0 native_decide`).

---

## 3. Architectural Strategy: Convergence with `Th0rgal/lean-native`

1. **Keep the Thin Rust I/O Shell for Cold CLI Startup (`1.3 ms`)**:
   - Any executable linking `libLean` (`import Lean`) runs ~35 ms of C++ static initializers (`lean_initialize()`) and produces a ~218 MB binary.
   - Separating `lean-native` into a `LeanNativeCore` target (without `import Lean`, linking only `libleanrt`) reduces the binary to **4.1 MB** and startup to **2.46 ms**, while the Rust CLI + `/dev/shm` + SQLite CAS layer starts in **1.32 ms**.
2. **Move Semantic Lowering, Optimization & GPU/LLVM Codegen into `lean-native` + `ZygoteWorker`**:
   - Inside `ZygoteWorker`, `libLean` is already warm in memory (`0 ms` initialization cost).
   - Instead of expanding heuristic string-based Lean-to-CUDA parsing in Rust (`gpu_fastcheck.rs`), `turbo-lean` delegates typed `Expr` / `LCNF` ingestion, `LNIR` optimization passes, formal pass certificate verification, and LLVM 18 / MLIR / PTX / CUDA code generation to `th0rgal/lean-native`.
3. **Formalize Core Verification Logic in Lean 4**:
   - Every decision function that affects soundness (shard key derivation, hygiene classification, dependency cone pruning, DAG invalidation, counterexample validation) should be specified and proved sound in Lean 4 (`Assembler.lean` / `LeanNative.Proofs`), with differential tests against the fast Rust paths.

---

## 4. Environment & Verification Commands

```bash
export PATH="/var/lib/sandboxed-node/9304baf4-5074-4dad-8c26-2e2896f70f25/.cargo/bin:/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.31.0/bin:/var/lib/sandboxed-node/caches/elan/bin:$PATH"
export ELAN_HOME="/var/lib/sandboxed-node/caches/elan"

cargo build --release
cargo test --release
python3 autoresearch/run_eval.py
```
