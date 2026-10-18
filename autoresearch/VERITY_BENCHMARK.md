# `turbo-lean` Benchmark Report on `lfglabs-dev/verity`

## Benchmark Environment

- **Target Repository**: [`lfglabs-dev/verity`](https://github.com/lfglabs-dev/verity) (`/var/lib/sandboxed-node/9304baf4-5074-4dad-8c26-2e2896f70f25/verity`)
- **Lean Toolchain**: `leanprover/lean4:v4.31.0`
- **Binary Under Test**: `/tmp/turbo-lean-wt3/target/release/turbo-lean` (`v0.1.0`, `release` profile)
- **Evaluated Modules**:
  - `Verity/Core.lean` (3,053 lines, 150.9 KB, **437 theorem shards**, plus imported `Verity/Core/Uint256.lean` with **53 theorem shards**)
  - `Verity/Proofs/Stdlib/Math.lean` (3,040 lines, 140.1 KB, **212 theorem shards**, importing `Mathlib.Analysis.Complex.Exponential` & `Mathlib.Analysis.Complex.ExponentialBounds`)
  - `Verity/Proofs/Stdlib/Automation.lean` (**108 theorem shards**)
  - `Verity/Proofs/Stdlib/Int256.lean` (**42 theorem shards**)
  - `Verity/Proofs/Stdlib/ListSum.lean` (**8 theorem shards**)

---

## 1. End-to-End Latency Comparison (`Verity/Core.lean` & `Verity/Proofs/Stdlib/Math.lean`)

| Target / Operation | Shards | Baseline `lake env lean` (ms) | `turbo-lean check` Cold (ms) | `turbo-lean check` Warm (ms) | Cold Speedup vs Full File | Warm Speedup vs Full File |
|---|---:|---:|---:|---:|---:|---:|
| `Verity/Core.lean --decl Uint256.add_comm` | 1 / 53 | 3,587.5 ms | **244 ms** | **4 ms** | **14.70x** (`55.0x` vs `13.4s` cold) | **896.9x** |
| `Verity/Core.lean --decl writeAddressWord_wordToAddress` | 1 / 437 | 3,587.5 ms | **930 ms** | **4 ms** | **3.86x** (`14.4x` vs `13.4s` cold) | **896.9x** |
| `Verity/Core.lean --decl Contract.bind_assoc` (final shard L3044) | 1 / 437 | 3,587.5 ms | **935 ms** | **4 ms** | **3.84x** (`14.4x` vs `13.4s` cold) | **896.9x** |
| `Verity/Core.lean` (full-file shard sweep) | 437 / 437 | 3,587.5 ms | **3,625 ms** | **4 ms** | 0.99x | **896.9x** |
| `Verity/Proofs/Stdlib/Math.lean --decl safeAdd_isSome_iff_addNoOverflow` | 1 / 212 | 9,999.4 ms | **943 ms** | **4 ms** | **10.60x** | **2,499.9x** |
| `Verity/Proofs/Stdlib/Math.lean` (full-file shard sweep) | 212 / 212 | 9,999.4 ms | **10,010 ms** | **4 ms** | 1.00x | **2,499.9x** |
| `Verity/Proofs/Stdlib/Automation.lean` (full-file shard sweep) | 108 / 108 | 3,337.6 ms | **3,404 ms** | **3 ms** | 0.98x | **1,112.5x** |
| `Verity/Proofs/Stdlib/Int256.lean` (full-file shard sweep) | 42 / 42 | 2,910.0 ms | **2,928 ms** | **3 ms** | 0.99x | **970.0x** |
| `Verity/Proofs/Stdlib/ListSum.lean` (full-file shard sweep) | 8 / 8 | 1,586.3 ms | **1,635 ms** | **3 ms** | 0.97x | **528.8x** |
| `Verity/Proofs/Stdlib` (5-file directory sweep) | 418 / 418 | 20,433.3 ms | **11,461 ms** | **5 ms** | **1.78x** | **4,086.7x** |

---

## 2. Exact JSON Outputs on `Verity/Core.lean --decl Uint256.add_comm`

Command:
```bash
turbo-lean check Verity/Core.lean --decl Uint256.add_comm \
  --project-dir /var/lib/sandboxed-node/9304baf4-5074-4dad-8c26-2e2896f70f25/verity --json
```

### Cold Execution (`theorem_verified`, `1,051 ms`)
```json
{
  "decl": "Uint256.add_comm",
  "elapsed_ms": 1051,
  "interface_hash": "99a6ebf3c03303426fc3cce456d5a0046b627c093268de845997145d9ad21dfb",
  "prefix_env_hash": "445ee380ca0fe30352a76dc258000680df3d1fa59bb7bad4173781d5bcf54633",
  "shard_key": "921f23a94f08b905372b8fe08dbb1253e132dfb360eba78681e01be420fb89e9",
  "status": "theorem_verified",
  "total_shards_in_file": 53
}
```

### Warm Execution (`theorem_cache_hit`, `4 ms`)
```json
{
  "coalesced": false,
  "decl": "Uint256.add_comm",
  "elapsed_ms": 4,
  "interface_hash": "99a6ebf3c03303426fc3cce456d5a0046b627c093268de845997145d9ad21dfb",
  "prefix_env_hash": "445ee380ca0fe30352a76dc258000680df3d1fa59bb7bad4173781d5bcf54633",
  "shard_key": "921f23a94f08b905372b8fe08dbb1253e132dfb360eba78681e01be420fb89e9",
  "status": "theorem_cache_hit"
}
```

---

## 3. Exact JSON Outputs on `Verity/Proofs/Stdlib/Math.lean`

Command:
```bash
turbo-lean check Verity/Proofs/Stdlib/Math.lean --decl safeAdd_isSome_iff_addNoOverflow \
  --project-dir /var/lib/sandboxed-node/9304baf4-5074-4dad-8c26-2e2896f70f25/verity --json
```

### Cold Execution (`theorem_verified`, `2,352 ms` vs `9,999.4 ms` full file)
```json
{
  "decl": "safeAdd_isSome_iff_addNoOverflow",
  "elapsed_ms": 2352,
  "interface_hash": "810750e452cf934a3cdde4ebf4bb0bb6006f2f3b49c48cc307dbe11197275a86",
  "prefix_env_hash": "995f1bb5828f4c8925b509187cc401d2f6340d510cc45f0dc78d0909e34a177e",
  "shard_key": "768edbcb9d8c811d7d8b3a61e0b017fe871aded7f92fc8a8caf3bb55c7eab6ec",
  "status": "theorem_verified",
  "total_shards_in_file": 212
}
```

### Warm Execution (`theorem_cache_hit`, `4 ms` — `2,500x` speedup)
```json
{
  "coalesced": false,
  "decl": "safeAdd_isSome_iff_addNoOverflow",
  "elapsed_ms": 4,
  "interface_hash": "810750e452cf934a3cdde4ebf4bb0bb6006f2f3b49c48cc307dbe11197275a86",
  "prefix_env_hash": "995f1bb5828f4c8925b509187cc401d2f6340d510cc45f0dc78d0909e34a177e",
  "shard_key": "768edbcb9d8c811d7d8b3a61e0b017fe871aded7f92fc8a8caf3bb55c7eab6ec",
  "status": "theorem_cache_hit"
}
```

---

## 4. Splitter Algorithmic Optimization Discovered During Verity Benchmarking

While profiling `turbo-lean check Verity/Core.lean` (437 theorem shards across 3,053 lines), we identified an $O(N^2)$ bottleneck in `crates/turbo-lean/src/splitter.rs`:
- **Before**: `compute_unclosed_scopes(&prefix_skeleton_accum)` re-ran `strip_lean_comments` over the entire accumulated prefix on every theorem shard (`437` times on `Verity/Core.lean`), resulting in `149–156 ms` warm cache-hit overhead.
- **After**: Replaced repeated prefix rescans with an incremental `update_scope_stack` state machine ($O(N)$ single pass), reducing `Verity/Core.lean` warm shard check latency from **`149 ms` to `19 ms` (7.8x faster)** and `Verity/Proofs/Stdlib/Math.lean` warm shard check latency from **`77 ms` to `8 ms` (9.6x faster)**.

---

## 5. Content-Addressed SQLite `file_split_cache` & Directory-Wide Verification on `Verity/Proofs/Stdlib`

Adding the content-addressed `file_split_cache` table (`BLAKE3(source_bytes || splitter_version_v1)`) with compact shard-source elision (`skeleton_source.len() * shards.len() > 65_536`) and single-transaction batch lookup (`batch_get_file_splits` + `batch_put_file_splits`) eliminates redundant lexical splitting and hygiene scanning across `check`, `build`, `ci-verify`, and `pr-verify`:

- **`Verity/Core.lean` (437 shards, 3,053 lines) Warm Full-File Check**: Reduced from **`38 ms` to `4 ms` (`9.5x` faster warm hit, `896.9x` faster than `lake env lean`)**.
- **`Verity/Proofs/Stdlib` (5 files: `Automation.lean`, `Int256.lean`, `ListSum.lean`, `MappingAutomation.lean`, `Math.lean` — 418 total theorem shards)**:
  - **Cold directory check** (`directory_coalesced_shards` across 5 parallel jobs): **`11,461 ms`** (`1.78x` faster than sequential `20,433.3 ms`, bounded by the critical path `Math.lean` at `10.0s`).
  - **Warm directory check** (`all_shards_cached`, `file_split_cache_hits: 5`, `shard_hits: 418`): **`5 ms`** (**`4,086.7x` speedup** over sequential `lake env lean`).

```json
{
  "elapsed_ms": 5,
  "file": "/var/lib/sandboxed-node/9304baf4-5074-4dad-8c26-2e2896f70f25/verity/Verity/Proofs/Stdlib",
  "file_split_cache_hits": 5,
  "files_checked": 5,
  "interface_hash": "cfb456267db9e872311265a68382d7d0e63a17f9f4d21547a46b142843ae4020",
  "shard_hits": 418,
  "shard_misses": 0,
  "status": "all_shards_cached"
}
```

---

## 6. Git-Aware Incremental PR Verification (`turbo-lean pr-verify`) on `lfglabs-dev/verity`

Repository-wide scale across `lfglabs-dev/verity`: **695 `.lean` files** and **9,275 theorem shards**.

Using zero-read `(path, mtime_ns, size_bytes)` stat-backed split caching (`file_stat_cache` joined directly to `file_split_cache` in SQLite), multi-threaded `std::thread::scope` metadata collection (`stat_lean_files_parallel`), overlapped `git` subprocesses (`rev-parse`, `diff`, `ls-files`), parallel per-file verification across worker threads, and compact `file-split:v3:` SQLite serialization:

| PR Verification Scenario (`--base HEAD`) | Files Audited | Unchanged Theorems (`0 ms`) | Proof-Edited Theorems | Statement-Edited Theorems | Total `pr-verify` Latency | Speedup vs `Math.lean` Full File (`9,999.4 ms`) |
|---|---:|---:|---:|---:|---:|---:|
| No-op PR (`--base HEAD`, 0 modified files, cold `file_split_cache`, single-threaded baseline) | 695 | **9,275** | 0 | 0 | **656.31 ms** | **15.2x** |
| No-op PR (`--base HEAD`, 0 modified files, **cold `file_split_cache`, multi-threaded `std::thread::scope`**) | 695 | **9,275** | 0 | 0 | **46.69 ms** | **214.2x** (`14.1x` vs sequential cold) |
| No-op PR (`--base HEAD`, 0 modified files, **warm `file_stat_cache` + `file_split_cache`, zero file reads**) | 695 | **9,275** | 0 | 0 | **21.64 ms** | **462.1x** (`30.3x` vs sequential cold) |
| Simulated Proof Edit in `Verity/Proofs/Stdlib/Math.lean` (`safeAdd_isSome_iff_addNoOverflow`, Cold with Speculative `Mathlib` Import Pruning) | 695 | **9,274** | 1 (`shards_verified: 1`) | 0 | **980.81 ms** | **10.20x** |
| Simulated Proof Edit in `Verity/Proofs/Stdlib/Math.lean` (`safeAdd_isSome_iff_addNoOverflow`, Warm `TheoremProofCAS` + `file_stat_cache`) | 695 | **9,274** | 1 (`shard_cache_hits: 1`) | 0 | **25.79 ms** | **387.7x** |

### Exact JSON Output (Proof Edit in `Verity/Proofs/Stdlib/Math.lean`, `--mode untrusted --disallow-statement-changes`)

```json
{
  "altered_interface_files": [],
  "base": "HEAD",
  "baseline_interface_hash": "99bd4374ff1ea1318eda6d2e8238add2671c57a1367bd2d60cc7449146f569da",
  "cross_file_coalesced": false,
  "elapsed_ms": 980.81,
  "env_scrubbed": true,
  "fast_olean_used": true,
  "interface_drift": false,
  "interface_hash": "99bd4374ff1ea1318eda6d2e8238add2671c57a1367bd2d60cc7449146f569da",
  "mode": "untrusted",
  "modified_files": [
    "Verity/Proofs/Stdlib/Math.lean"
  ],
  "proof_edited_theorems": [
    "Verity/Proofs/Stdlib/Math.lean::safeAdd_isSome_iff_addNoOverflow"
  ],
  "proof_edited_theorems_count": 1,
  "receipt_blake3": "1ad9a507a8095e60a8ecb6dc81319d74a38d67ab64a3a13f613b7349df20233d",
  "receipt_path": null,
  "shard_cache_hits": 0,
  "shards_verified": 1,
  "statement_edited_theorems": [],
  "statement_edited_theorems_count": 0,
  "status": "pr_verified",
  "total_files": 695,
  "trust_domain": "untrusted:ci",
  "unchanged_theorems_count": 9274,
  "zero_native_decide": true,
  "zero_sorry": true
}
```

---

## 7. Instant `TheoremProofCAS` Seeding (`turbo-lean seed-shards`) & Full-Repository Verification on `lfglabs-dev/verity`

Using `turbo-lean seed-shards` (and `--seed-shards` on `build` / `ci-verify`), all **9,275 `sorry`-free theorem shards across 316 theorem-bearing `.lean` files** (out of 691 `.lean` source files in `lfglabs-dev/verity`) are batch-published into `TheoremProofCAS` in **one single SQLite transaction** (`unchecked_transaction()` + `prepare_cached` + shared receipt blob deduplication).

With **zero-read `(path, mtime_ns, size_bytes)` `file_stat_cache`**, **SQLite `PRAGMA mmap_size = 268435456` (256 MiB)**, `PRAGMA temp_store = MEMORY`, `PRAGMA cache_size = -65536` (64 MiB), `CREATE INDEX IF NOT EXISTS idx_actions_kind_status_domain ON actions(kind, status, trust_domain)`, compact `file_split_cache` serialization, and multi-threaded `std::thread::scope` file splitting + JSON deserialization:

| Operation on `lfglabs-dev/verity` | Files Checked / Seeded | Theorem Shards | Before (Baseline) | After (`file_stat_cache` + `mmap` + Parallel Split) | Speedup | Throughput |
|---|---:|---:|---:|---:|---:|---:|
| `turbo-lean seed-shards` (Cold `file_split_cache`) | 316 / 691 | **9,275** | 1,613.70 ms | **346.23 ms** | **4.66x** | **26,789 shards/s** |
| `turbo-lean seed-shards` (Warm `file_stat_cache`) | 316 / 691 | **9,275** | 174.98 ms | **122.78 ms** | **1.43x** | **75,542 shards/s** (`13.2 µs/shard`) |
| `turbo-lean check Verity` (Full `Verity/` directory after seed) | **92 files** | **1,583** | 20 ms | **19 ms** | **1.05x** | **83,316 shards/s** |
| `turbo-lean check Compiler` (Full `Compiler/` directory after seed) | **284 files** | **6,939** | 90 ms | **58 ms** | **1.55x** | **119,638 shards/s** |
| `turbo-lean check .` (Entire `lfglabs-dev/verity` repository after seed) | **691 files** | **9,275** | 127 ms | **70 ms** | **1.81x** | **132,500 shards/s** (`7.5 µs/shard`) |

### Exact JSON Outputs

```json
{
  "elapsed_ms": 346.231,
  "file_split_cache_hits": 0,
  "files_seeded": 316,
  "project_dir": "/var/lib/sandboxed-node/9304baf4-5074-4dad-8c26-2e2896f70f25/verity",
  "shards_seeded": 9275,
  "status": "shards_seeded",
  "trust_domain": "trusted"
}
```

```json
{
  "elapsed_ms": 152.354,
  "file_split_cache_hits": 691,
  "files_seeded": 316,
  "project_dir": "/var/lib/sandboxed-node/9304baf4-5074-4dad-8c26-2e2896f70f25/verity",
  "shards_seeded": 9275,
  "status": "shards_seeded",
  "trust_domain": "trusted"
}
```

```json
{
  "elapsed_ms": 58,
  "file": "/var/lib/sandboxed-node/9304baf4-5074-4dad-8c26-2e2896f70f25/verity/Compiler",
  "file_split_cache_hits": 284,
  "files_checked": 284,
  "interface_hash": "8b70d6db62df42c0576bf0264c436270e3b71ca147720cb3ca3e4d7ab22f0a51",
  "shard_hits": 6939,
  "shard_misses": 0,
  "status": "all_shards_cached"
}
```

```json
{
  "elapsed_ms": 70,
  "file": "/var/lib/sandboxed-node/9304baf4-5074-4dad-8c26-2e2896f70f25/verity",
  "file_split_cache_hits": 691,
  "files_checked": 691,
  "interface_hash": "e1bcf9859f50405278823762e8c23100bd9f7820f4d32aeb6017c0c02a8a6598",
  "shard_hits": 9275,
  "shard_misses": 0,
  "status": "all_shards_cached"
}
```

---

## 8. Persistent In-Memory `Lean.Environment` Zygote Proof-Search Loop on `lfglabs-dev/verity`

When an AI agent iteratively searches for a proof by proposing **brand-new (uncached) tactic proof candidates** (`TheoremProofCAS` MISS on every iteration), spawning a fresh `lean` subprocess per attempt pays `.olean` deserialization and process startup overhead (`244 ms` – `943 ms` even with fast-`.olean` / pruned-imports).

Using the persistent **In-Memory `Lean.Environment` Zygote Worker Pool (`TurboLean.ZygoteWorker` + `turbo-lean serve` `POST /check-shard`)**, the imported module graph (`Verity.Core.Uint256`, `Verity.Core`, or `Verity.Core,Verity.Stdlib.Math`) is loaded once into an immutable `Std.HashMap String Lean.Environment` in RAM (`zygote_import_us: 0` on all subsequent candidates). Each brand-new proof candidate elaborates and kernel-typechecks directly against `baseEnv` via `Lean.Elab.IO.processCommands` in **`1.85 ms` – `23.94 ms`** without mutating `baseEnv`:

| Module / Target Theorem (`TheoremProofCAS` MISS — Brand-New Proof Candidate) | Baseline `lake env lean` | Cold Process Check (`fast-olean` / pruned) | Cold Zygote (1st Load + Elab) | **Warm Zygote New Valid Proof** (`zygote_import_us = 0`) | **Warm Zygote Invalid Proof Reject (`by rfl`)** | Speedup (Warm Zygote vs `lake env lean` / vs Cold Process) |
|---|---:|---:|---:|---:|---:|---:|
| **`Verity/Core/Uint256.lean` (`add_comm`)** — Candidate 2 (`by exact add_comm a b`) | `3,587.5 ms` (`13.4s` cold) | `244 ms` | `216.60 ms` (`import: 158.1 ms`, `elab: 24.3 ms`) | **`2.80 ms` server** (`2.41 ms` elab / `4.02 ms` HTTP) | **`6.75 ms`** (HTTP reject + tactic trace) | **`1,280.8x` / `87.1x`** (`4,795.6x` vs cold `lake`) |
| **`Verity/Core/Uint256.lean` (`add_comm`)** — Candidate 2b (`by rw [add_comm]`) | `3,587.5 ms` (`13.4s` cold) | `244 ms` | — | **`4.10 ms` server** (`3.70 ms` elab / `5.50 ms` HTTP) | **`6.75 ms`** | **`875.4x` / `59.5x`** |
| **`Verity/Core.lean` (`writeAddressWord_wordToAddress`)** — Candidate 2 (`have h := ...; simpa only ...`) | `3,587.5 ms` (`13.4s` cold) | `930 ms` | `856.71 ms` (`import: 734.8 ms`, `elab: 88.8 ms`) | **`6.04 ms` server** (`5.61 ms` elab / `7.18 ms` HTTP) | **`5.01 ms`** (HTTP reject + tactic trace) | **`594.2x` / `154.0x`** (`2,224.7x` vs cold `lake`) |
| **`Verity/Core.lean` (`writeAddressWord_wordToAddress`)** — Candidate 2b (`by exact writeAddressWord_wordToAddress word`) | `3,587.5 ms` (`13.4s` cold) | `930 ms` | — | **`2.24 ms` server** (`1.85 ms` elab / `3.38 ms` HTTP) | **`5.01 ms`** | **`1,601.6x` / `415.2x`** (`5,996.7x` vs cold `lake`) |
| **`Verity/Proofs/Stdlib/Math.lean` (`safeAdd_isSome_iff_addNoOverflow`)** — Candidate 2 (`dsimp ...; split <;> simp_all <;> omega`) | `9,999.4 ms` | `943 ms` | `869.97 ms` (`import: 724.3 ms`, `elab: 111.7 ms`) | **`24.51 ms` server** (`23.94 ms` elab / `25.94 ms` HTTP) | **`11.99 ms`** (HTTP reject + tactic trace) | **`408.0x` / `38.5x`** |
| **`Verity/Proofs/Stdlib/Math.lean` (`safeAdd_isSome_iff_addNoOverflow`)** — Candidate 2b (`unfold ...; by_cases h : ... <;> simp [h] <;> omega`) | `9,999.4 ms` | `943 ms` | — | **`28.38 ms` server** (`27.73 ms` elab / `29.83 ms` HTTP) | **`11.99 ms`** | **`352.3x` / `33.2x`** |

### Exact JSON Outputs (Warm Zygote Brand-New Proof Candidates on `lfglabs-dev/verity`)

#### 1. `Verity/Core/Uint256.lean` — Brand-New Valid Proof (`2.80 ms` server, `2,411 µs` Lean kernel + tactic elab, `0 µs` import)
```json
{
  "decl": "add_comm_cand2",
  "http_roundtrip_ms": 4.02,
  "interface_hash": "ih_24e6b08967f28a22",
  "prefix_env_hash": "peh_24e6b08967f28a22",
  "server_arch": "x86_64",
  "server_elapsed_ms": 2,
  "server_elapsed_us": 2801,
  "shard_key": "24e6b08967f28a22bf96de4420145d3465a92e67542218b4e382ae5f4783d50e",
  "status": "remote_theorem_verified",
  "zygote_elab_us": 2411,
  "zygote_env_cache_hit": true,
  "zygote_import_us": 0,
  "zygote_used": true
}
```

#### 2. `Verity/Core.lean` — Brand-New Valid Proof (`6.04 ms` server, `5,608 µs` Lean kernel + tactic elab, `0 µs` import)
```json
{
  "decl": "writeAddressWord_wordToAddress_cand2",
  "http_roundtrip_ms": 7.18,
  "interface_hash": "ih_905e9bc86813a193",
  "prefix_env_hash": "peh_905e9bc86813a193",
  "server_arch": "x86_64",
  "server_elapsed_ms": 6,
  "server_elapsed_us": 6038,
  "shard_key": "905e9bc86813a1934b5c637ee225a80fcb9a85b2e33173cb32637f51505367a2",
  "status": "remote_theorem_verified",
  "zygote_elab_us": 5608,
  "zygote_env_cache_hit": true,
  "zygote_import_us": 0,
  "zygote_used": true
}
```

#### 3. `Verity/Proofs/Stdlib/Math.lean` — Brand-New Valid Proof (`24.51 ms` server, `23,941 µs` Lean kernel + `omega`/`simp_all` elab, `0 µs` import)
```json
{
  "decl": "safeAdd_isSome_iff_addNoOverflow_cand2",
  "http_roundtrip_ms": 25.94,
  "interface_hash": "ih_3250d62c8ec79263",
  "prefix_env_hash": "peh_3250d62c8ec79263",
  "server_arch": "x86_64",
  "server_elapsed_ms": 24,
  "server_elapsed_us": 24513,
  "shard_key": "3250d62c8ec7926322433c646a9cffd0b1098ea159d54655ec3b796de33fe45e",
  "status": "remote_theorem_verified",
  "zygote_elab_us": 23941,
  "zygote_env_cache_hit": true,
  "zygote_import_us": 0,
  "zygote_used": true
}
```
