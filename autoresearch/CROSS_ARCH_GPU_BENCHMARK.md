# Cross-Architecture (`x86_64` <-> `aarch64`) CAS Sync & NVIDIA GB10 GPU `fast-check` Benchmark Report

## 1. Test Environment

| Node | Architecture | CPU / SoC | GPU Accelerator | OS / Kernel | Lean Toolchain |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Local Worker** | `x86_64-unknown-linux-gnu` | AMD EPYC / x86_64 Cloud Node | None (CPU + Remote Offload) | Linux 6.x (`x86_64`) | `leanprover/lean4:v4.31.0` |
| **NVIDIA DGX Spark (`spark-de79`)** | `aarch64-unknown-linux-gnu` | NVIDIA Grace ARM64 (`aarch64`) | **NVIDIA GB10** (Compute Capability `12.1`, 48 SMs, Unified Memory) | Linux `6.14.0-1015-nvidia` (`aarch64`) | `leanprover/lean4:v4.31.0` |

---

## 2. Bidirectional Cross-Architecture (`x86_64` <-> `aarch64`) CAS Export, Import & HTTP Sync

Lean 4 `.olean`, `.ilean`, `.c`, and `turbo-lean` theorem-level `expr_shard` receipts are architecture-independent across 64-bit little-endian platforms (`x86_64` and `aarch64`), whereas compiled `.o` / `.so` binaries are architecture-specific. `turbo-lean export --portable-only` packages only portable artifacts into a zstd-compressed, BLAKE3-authenticated `.tlpack` bundle (`PackManifest` v1), and `turbo-lean import` / `turbo-lean sync` re-verifies every blob's BLAKE3 digest before materializing hardlinks/reflinks into the target worktree.

### 2.1 Bundle Metrics (`x86_64_cache.tlpack` & `aarch64_cache.tlpack`)

| Metric | `x86_64` Export (`x86_64_cache.tlpack`) | `aarch64` Export (`aarch64_cache.tlpack`) | Match / Determinism |
| :--- | :--- | :--- | :--- |
| **Completed Actions** | `11` (`1` module build + `10` theorem shards) | `11` (`1` module build + `10` theorem shards) | **100% Identical** |
| **Portable Immutable Blobs** | `16` (`.olean`, `.ilean`, `.c`, `expr_shard`) | `16` (`.olean`, `.ilean`, `.c`, `expr_shard`) | **100% Identical** |
| **Uncompressed Logical Size** | `1,401,669` bytes (`1.34 MiB`) | `1,401,669` bytes (`1.34 MiB`) | **Exact byte match** |
| **Compressed `.tlpack` Size (zstd)** | `598 KiB` (`2.34x` compression ratio) | `598 KiB` (`2.34x` compression ratio) | **Exact byte match** |
| **Project Action Key** | `e94b40928177c5488266fa7ed7975265...` | `e94b40928177c5488266fa7ed7975265...` | **Identical BLAKE3** |
| **Proof-Irrelevant Interface Hash** | `1735a920296fd6da12729491776e0605...` | `1735a920296fd6da12729491776e0605...` | **Identical BLAKE3** |
| **`lookup_chain_sound` Shard Key** | `cbc31e91c12d6e6701b139747dca7c40...` | `cbc31e91c12d6e6701b139747dca7c40...` | **Identical BLAKE3** |

### 2.2 End-to-End Build & Theorem Check Latency (`x86_64` <-> `aarch64`)

| Operation | Cold Build / Verification (`ms`) | Cross-Arch Warm Cache Hit (`ms`) | Speedup | Details |
| :--- | :--- | :--- | :--- | :--- |
| **`aarch64` (`dgx-spark`) `build --project-dir lean`** (consuming `x86_64_cache.tlpack`) | `4,289 ms` | **`4 ms`** | **1,072.3x** | 6 portable `.olean`/`.ilean`/`.c` files hardlinked in 4 ms |
| **`aarch64` (`dgx-spark`) `check Reflection.lean --decl lookup_chain_sound`** (consuming `x86_64_cache.tlpack`) | `715 ms` | **`< 1 ms` (`0 ms`)** | **> 715x** | Instant `theorem_cache_hit` via `PrefixEnv` shard key |
| **`aarch64` (`dgx-spark`) `check Reflection.lean`** (all 8 theorem shards from `x86_64`) | `961 ms` | **`< 1 ms` (`0 ms`)** | **> 961x** | `all_shards_cached` (`8` hits, `0` misses) |
| **`x86_64` `build --project-dir lean`** (consuming `aarch64_cache.tlpack` from `dgx-spark`) | `1,103 ms` | **`1 ms`** | **1,103.0x** | 6 portable `.olean`/`.ilean`/`.c` files hardlinked in 1 ms |
| **`x86_64` `check Reflection.lean --decl lookup_chain_sound`** (consuming `aarch64_cache.tlpack`) | `715 ms` | **`< 1 ms` (`0 ms`)** | **> 715x** | Instant `theorem_cache_hit` across architectures |
| **`x86_64` `check Reflection.lean`** (all 8 theorem shards from `aarch64`) | `996 ms` | **`< 1 ms` (`0 ms`)** | **> 996x** | `all_shards_cached` (`8` hits, `0` misses) |

### 2.3 HTTP Server & Delta Sync (`turbo-lean serve` + `turbo-lean sync`)

Running `turbo-lean serve --listen 127.0.0.1:9419 --gpu-enable` on `dgx-spark` (`aarch64`) and synchronizing an empty client CAS via `turbo-lean sync http://127.0.0.1:9419`:

```json
{
  "arch": "aarch64",
  "gpu_enabled": true,
  "ok": true,
  "storage": {
    "active_inflight_leases": 0,
    "active_worktrees": 1,
    "cache_root": "/tmp/turbo-lean-spark-cache",
    "pinned_bytes": 0,
    "reclaimable_bytes": 1401669,
    "total_actions": 11,
    "total_blobs": 16,
    "total_coalesced_waits": 0,
    "total_logical_bytes": 1401669,
    "worktree_retained_bytes": 0
  }
}
```

Client synchronization output:
```text
[turbo-lean] Synced with http://127.0.0.1:9419: pulled 11 actions (16 blobs), pushed 0 actions (0 blobs)
```

---

## 3. GPU `fast-check` (`CuDenote` & `CuMutate`) on NVIDIA GB10 (`dgx-spark`)

`turbo-lean fast-check` supports three execution modes:
1. **Local CUDA GPU (`turbo-lean --json fast-check gpu/cudenote_bench.cu`)**: Compiles `.cu` kernels locally via `nvcc -O3 -arch=native -lcuda` with `CUDA_MODULE_LOADING=LAZY` and lightweight primary context initialization (`CU_CTX_COREDUMP_ENABLE`), keeping total GPU memory footprint under `< 2 MiB` even when 96+ GiB of unified memory on `dgx-spark` is occupied by concurrent LLM inference workers.
2. **Remote SSH/Jump-Host GPU Offload (`turbo-lean --json fast-check gpu/cudenote_bench.cu --remote-ssh th0rgal@100.77.4.93 --via-jump agent-core`)**: Transparently streams `.cu` harnesses from an `x86_64` CPU node to `dgx-spark` (`aarch64` + NVIDIA GB10), compiles and executes on the GB10 GPU, and returns structured JSON metrics.
3. **Native CPU Perceus/FBIP (`turbo-lean --json fast-check lean/TurboLean/FastCheck.lean`)**: Compiles Lean 4 specifications to C (`lean -c`) and native machine code (`leanc -O3`) with automatic `SplitMix64` harness synthesis when `def main` is omitted.

### 3.1 Benchmark Results: CPU (`x86_64` & `aarch64`) vs. NVIDIA GB10 GPU (`dgx-spark`)

| Benchmark Workload | Execution Target | Kernel / Exec Time | Throughput | Counterexamples / Mutants Killed |
| :--- | :--- | :--- | :--- | :--- |
| **1M-State 256-bit Arithmetic Check** (`FastCheck.lean`) | `x86_64` CPU (`leanc -O3` Perceus, 1 core) | `5.81 ms` (`5,809 µs`) | `172.15 M states/s` | `0` violations (checksum verified: `2720173684989076032`) |
| **1M-State 256-bit Arithmetic Check** (`FastCheck.lean`) | `aarch64` Grace CPU (`leanc -O3` Perceus, 1 core) | `6.31 ms` (`6,312 µs`) | `158.43 M states/s` | `0` violations (checksum verified: `2720173684989076032`) |
| **1M-State `CuDenote` Valid Lemma Check** (`cudenote_bench.cu`) | **NVIDIA GB10 GPU** (48 SMs, Compute `12.1`) | **`0.7093 ms`** (`709.3 µs`) | **`1,409.92 M states/s`** (`1.41 B states/s`) | `0` valid lemma violations |
| **10M-State `CuDenote` Valid Lemma Check** (`cudenote_bench.cu`) | **NVIDIA GB10 GPU** (48 SMs, Compute `12.1`) | **`7.2136 ms`** (`7,213.6 µs`) | **`1,386.27 M states/s`** (`1.39 B states/s`) | `0` valid lemma violations |
| **10M-State `CuDenote` 3-Lemma Differential Suite** (`cudenote_bench.cu`) | **NVIDIA GB10 GPU** (48 SMs, Compute `12.1`) | **`22.5697 ms`** | **`443.07 M states/s`** (`1,329.21 M Denote-evals/s`) | `0` valid violations; **`2,491,495`** rounding CEs (first at `idx=1985`); **`5,005,531`** underflow CEs |
| **`CuMutate` Campaign: 293 Mutants × 10,000 Txs** (`2.93M` Denote evals) | **NVIDIA GB10 GPU** (48 SMs, Compute `12.1`) | **`2.9658 ms`** (`2,965.8 µs`) | **`987.91 M Denote-evals/s`** (`0.99 B evals/s`) | **`292 / 293` mutants killed (`99.7%`)**; `2,317,088` diverging `(mutant, tx)` pairs |

### 3.2 Sample Structured JSON Output (`./target/release/turbo-lean --json fast-check gpu/cudenote_bench.cu` on `dgx-spark`)

```json
{
  "cumutate_kernel_ms": 2.9658,
  "cumutate_throughput_mevals_s": 987.91,
  "exec_ms": 1055,
  "fast_reject_3lemma_10m_kernel_ms": 22.5697,
  "fast_reject_3lemma_mstates_s": 443.07,
  "gpu_device": "NVIDIA GB10 (Compute Capability 12.1, 48 SMs)",
  "mode": "local_gpu_cuda",
  "mutants_killed": 292,
  "mutants_total": 293,
  "remote_host": null,
  "status": "ok",
  "throughput_mstates_s": 1333.94,
  "total_ms": 2598,
  "valid_lemma_10m_kernel_ms": 7.4966
}
```
