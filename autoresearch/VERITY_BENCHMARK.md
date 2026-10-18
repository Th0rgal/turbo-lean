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
| `Verity/Core.lean --decl Uint256.add_comm` | 1 / 53 | 3,587.5 ms | **1,051 ms** | **4 ms** | **3.41x** | **896.9x** |
| `Verity/Core.lean --decl writeAddressWord_wordToAddress` | 1 / 437 | 3,587.5 ms | **1,492 ms** | **4 ms** | **2.40x** | **896.9x** |
| `Verity/Core.lean` (full-file shard sweep) | 437 / 437 | 3,587.5 ms | **3,625 ms** | **4 ms** | 0.99x | **896.9x** |
| `Verity/Proofs/Stdlib/Math.lean --decl safeAdd_isSome_iff_addNoOverflow` | 1 / 212 | 9,999.4 ms | **2,352 ms** | **4 ms** | **4.25x** | **2,499.9x** |
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

Adding the content-addressed `file_split_cache` table (`BLAKE3(source_bytes || splitter_version_v1)`) with compact shard-source elision (`skeleton_source.len() * shards.len() > 65_536`) and single-transaction batch lookup (`batch_get_file_splits` + `batch_put_file_splits`) eliminates redundant lexical splitting and hygiene scanning across `check`, `build`, and `ci-verify`:

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

