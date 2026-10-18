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
| `Verity/Core.lean --decl Uint256.add_comm` | 1 / 53 | 3,587.5 ms | **1,051 ms** | **21 ms** | **3.41x** | **170.8x** |
| `Verity/Core.lean --decl writeAddressWord_wordToAddress` | 1 / 437 | 3,587.5 ms | **1,492 ms** | **19 ms** | **2.40x** | **188.8x** |
| `Verity/Core.lean` (full-file shard sweep) | 437 / 437 | 3,587.5 ms | **3,625 ms** | **38 ms** | 0.99x | **94.4x** |
| `Verity/Proofs/Stdlib/Math.lean --decl safeAdd_isSome_iff_addNoOverflow` | 1 / 212 | 9,999.4 ms | **2,352 ms** | **8 ms** | **4.25x** | **1,249.9x** |
| `Verity/Proofs/Stdlib/Math.lean` (full-file shard sweep) | 212 / 212 | 9,999.4 ms | **10,010 ms** | **19 ms** | 1.00x | **526.3x** |
| `Verity/Proofs/Stdlib/Automation.lean` (full-file shard sweep) | 108 / 108 | 3,337.6 ms | **3,404 ms** | **14 ms** | 0.98x | **238.4x** |
| `Verity/Proofs/Stdlib/Int256.lean` (full-file shard sweep) | 42 / 42 | 2,910.0 ms | **2,928 ms** | **11 ms** | 0.99x | **264.5x** |
| `Verity/Proofs/Stdlib/ListSum.lean` (full-file shard sweep) | 8 / 8 | 1,586.3 ms | **1,635 ms** | **7 ms** | 0.97x | **226.6x** |

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

### Warm Execution (`theorem_cache_hit`, `21 ms`)
```json
{
  "coalesced": false,
  "decl": "Uint256.add_comm",
  "elapsed_ms": 21,
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

### Warm Execution (`theorem_cache_hit`, `8 ms` — `1,250x` speedup)
```json
{
  "coalesced": false,
  "decl": "safeAdd_isSome_iff_addNoOverflow",
  "elapsed_ms": 8,
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

## 5. Git-Aware Incremental PR Verification (`turbo-lean pr-verify`) on `lfglabs-dev/verity`

Repository-wide scale across `lfglabs-dev/verity`: **695 `.lean` files** and **9,275 theorem shards**.

| PR Verification Scenario (`--base HEAD`) | Files Audited | Unchanged Theorems (`0 ms`) | Proof-Edited Theorems | Statement-Edited Theorems | Total `pr-verify` Latency | Speedup vs `Math.lean` Full File (`9,999.4 ms`) |
|---|---:|---:|---:|---:|---:|---:|
| No-op PR (`--base HEAD`, 0 modified files) | 695 | **9,275** | 0 | 0 | **656.31 ms** | **15.2x** |
| Simulated Proof Edit in `Verity/Proofs/Stdlib/Math.lean` (`safeAdd_isSome_iff_addNoOverflow`, Cold) | 695 | **9,274** | 1 (`shards_verified: 1`) | 0 | **2,489.21 ms** | **4.02x** |
| Simulated Proof Edit in `Verity/Proofs/Stdlib/Math.lean` (`safeAdd_isSome_iff_addNoOverflow`, Warm `TheoremProofCAS`) | 695 | **9,274** | 1 (`shard_cache_hits: 1`) | 0 | **662.77 ms** | **15.1x** |

### Exact JSON Output (Proof Edit in `Verity/Proofs/Stdlib/Math.lean`, `--mode untrusted --disallow-statement-changes`)

```json
{
  "altered_interface_files": [],
  "base": "HEAD",
  "baseline_interface_hash": "99bd4374ff1ea1318eda6d2e8238add2671c57a1367bd2d60cc7449146f569da",
  "cross_file_coalesced": false,
  "elapsed_ms": 2489.21,
  "env_scrubbed": true,
  "fast_olean_used": false,
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

