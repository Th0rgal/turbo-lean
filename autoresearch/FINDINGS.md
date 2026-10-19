# Autonomous Optimization & Co-Design Loop (`FINDINGS.md`)

This log records each iteration of the `OBSERVE -> HYPOTHESIZE -> IMPLEMENT -> DECIDE (KEEP / REVERT)` loop across `turbo-lean` and `lean-native` v0.3 (`375a5ae`).

---

## Iteration 1 — Pruning String-Matching Shortcuts & Multi-User `/dev/shm` Isolation (`KEEP` — Simplification & Soundness)
- **OBSERVE**: The external `rsgb` (`rust-specification-generation-benchmark`) audit identified that `ZygoteWorker.lean` contained a string-matching `verifiedStmtCache` shortcut, `zygote.rs` contained a hardcoded `unified_turbo_env` special case for `TurboLean.*` modules and copied worker binaries through world-shared `/dev/shm`, and `/dev/shm/turbo-lean-staging` lacked per-UID namespacing (causing `Permission denied` on multi-user hosts).
- **HYPOTHESIZE**: Deleting `verifiedStmtCache`, `unified_turbo_env`, `/dev/shm` binary execution, and 19 hardcoded host paths/IPs—while isolating `/dev/shm/turbo-lean-staging-<uid>` (`0700`)—eliminates stale/shortcut cache risks and fixes multi-user `cargo test` without degrading warm shard latency.
- **DECIDE (`KEEP`)**: 100% of unit tests and `run_eval.py` invariants pass under isolated per-UID `/dev/shm`, zero hardcoded paths remain, and warm check latency remains `1.6 ms`.

---

## Iteration 2 — Deterministic `turbo-lean eval` Mode, Multi-Import Worker Fix & Transitive `.olean` Hashing (`KEEP` — `700x` Speedup on `rsgb`)
- **OBSERVE**: On `lfglabs-dev/rust-specification-generation-benchmark` (`rsgb`), fresh `lean <file>` takes `~1,400 ms` per property/kill driver run because importing `Driver` + `Aeneas` + `Std` dominates execution, while `ZygoteWorker.lean` previously dropped `logInfo` (`RSGB_RESULT`, `RSGB_KILL`, `RSGB_OUTPUTS`), failed on the 2nd distinct import set due to `withImporting` resetting `enableInitializersExecution`, lacked request timeouts/crash recovery, and passed `dep_interface_hashes = &[]`.
- **HYPOTHESIZE**: Calling `unsafe enableInitializersExecution` before every `Lean.importModules`, returning 100% of `info`/`warning`/`error` messages (`file:line:col: severity: text`) + isolated `stdout`, enforcing parent `libc::poll` wall-clock timeouts (`SIGKILL` + `waitpid` `Drop` + 1x crash respawn), and hashing resolved `.olean` files on `LEAN_PATH` into both `pool_key` and `dep_interface_hashes` will make `turbo-lean eval` a 100% deterministic drop-in replacement for `lean <file>`.
- **DECIDE (`KEEP`)**: `turbo-lean eval` achieves **`~2.0 ms`** warm evaluation latency (vs `1,400 ms` fresh `lean`, **`~700x` speedup**), passes `--verify-determinism` with zero output discrepancies against `lean <file>`, kills infinite `#eval` loops within the configured timeout (exiting `124` with `RSGB_TIMEOUT`), and invalidates cached verdicts immediately when any `.olean` on `LEAN_PATH` is modified (formally proved in `TurboLean.Spec.imported_olean_mutation_invalidates_key`).

---

## Iteration 3 — Internal Lean `trace.profiler` & `Expr.getUsedConstants` Replay Certificate Distillation (`KEEP` — `3.4x` Tactic Replay Speedup)
- **OBSERVE**: Profiling via `autoresearch/corpus_bench.py` (`set_option trace.profiler true` + `IO.getNumHeartbeats`) shows that on cold/uncached proof shards, internal Lean elaboration dominates wall time (`synthInstance` typeclass search and unconstrained `simp` scanning thousands of `@[simp]` lemmas).
- **HYPOTHESIZE**: Extracting the exact used constants from the kernel-verified proof term (`cinfo.value?.get!.getUsedConstants`) to synthesize a compact `simp only [...]` replay certificate reduces tactic elaboration time and heartbeats by `> 2x` while the Lean kernel still checks the full proof term (`0 sorryAx`).
- **DECIDE (`KEEP`)**: Distilling unconstrained `simp` via `Expr.getUsedConstants` reduces elaboration latency by **`3.4x`** and heartbeats by **`> 60%`** on algebraic rewrite chains, verified by Law 5 (`TurboLean.Spec`).
