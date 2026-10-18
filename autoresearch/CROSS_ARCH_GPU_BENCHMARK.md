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

### 2.4 Zero-Redundancy HTTP Delta Push (`turbo-lean sync --push` / `POST /import-delta`)

`turbo-lean sync --push <url>` queries the remote coordinator's `GET /manifest`, computes the exact set of missing local trusted actions/blobs, and either uploads a binary-framed `TLPK v2` delta bundle via `POST /import-delta` (verified with BLAKE3 and inserted in a single SQLite `BEGIN IMMEDIATE ... COMMIT` transaction) or performs a `0`-byte no-op in `< 3 ms` (`delta_push_noop: true`):

| Delta Sync Operation | `x86_64` Latency (`run_eval.py`) | `aarch64` (`dgx-spark`) Latency | Network Payload |
| :--- | :--- | :--- | :--- |
| **Cold HTTP Delta Pull** (`GET /manifest` + `POST /export-delta` + batch import) | **`42.02 ms`** (`22` blobs, `12` actions) | **`38.10 ms`** | `~377 KiB` (`TLPK v2` zstd) |
| **Warm No-Op HTTP Delta Pull** (`M8_delta_sync_noop_ms`) | **`3.28 ms`** | **`0.85 ms`** | **`0` bytes** |
| **Cold HTTP Delta Push** (`sync --push` → `POST /import-delta`, `M9b_delta_sync_push_ms`) | **`33.51 ms`** (`22` blobs, `12` actions) | **`35.00 ms`** (`6` blobs, `1.40 MiB` raw) | `376.8 KiB` (`TLPK v2` zstd) |
| **Warm No-Op HTTP Delta Push** (`sync --push`, `M9c_delta_sync_push_noop_ms`) | **`2.91 ms`** (`delta_push_noop: true`) | **`< 1 ms` (`0 ms`)** (`delta_push_noop: true`) | **`0` bytes** |

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

### 3.3 Content-Addressed Native Binary Cache (`<store>/fastcheck_bins/<blake3_key>`)

Both local `turbo-lean fast-check` and HTTP remote `POST /fast-check` cache compiled native executables (`nvcc -O3 -arch=native` CUDA binaries and `lean -c` + `leanc -O3` Perceus FBIP binaries) by `BLAKE3("fastcheck-bin:v1:" || arch || mode || effective_source)`. Subsequent runs with identical harness source skip compiler invocations completely:

| Offload Mode & Target | Cold Total (`compile_cache_hit: false`) | Warm Total (`compile_cache_hit: true`) | Compilation Overhead Saved | End-to-End Speedup |
| :--- | :--- | :--- | :--- | :--- |
| **HTTP `POST /fast-check` CPU Perceus FBIP** (`FastCheck.lean`, 1M states) | `653.77 ms` (`lean -c` + `leanc -O3` + run) | **`8.34 ms`** (`0 ms` compile, `5.8 ms` exec) | `645.43 ms` | **`78.39×`** |
| **HTTP `POST /fast-check` NVIDIA GB10 GPU** (`cudenote_bench.cu`, `aarch64`) | `2,437 ms` (`nvcc -O3 -arch=native` + run) | **`1,044 ms`** (`0 ms` compile, `1,043 ms` exec) | `1,393 ms` | **`2.33×`** |

---

## 4. End-to-End Live Coordinator Suite on `dgx-spark` (`aarch64` Grace + NVIDIA GB10 GPU)

Running `turbo-lean serve --listen 127.0.0.1:9429 --gpu-enable` on `dgx-spark` (`spark-de79`, `100.77.4.93`, `aarch64-unknown-linux-gnu`, `leanprover/lean4:v4.31.0`) and exercising the complete remote verification, CAS seeding, PR verification, receipt auditing, GB10 GPU `fast-check`, and bidirectional delta sync pipeline:

| Operation on `dgx-spark` (`aarch64` + NVIDIA GB10) | Cold Latency | Warm / Cached Latency | Speedup | Key Telemetry |
| :--- | :--- | :--- | :--- | :--- |
| **`check Reflection.lean --decl lookup_chain_sound --remote-http`** (`POST /check-shard`) | **`272 ms`** (`server: 266 ms`) | **`1 ms`** (`server: 0 ms`) | **`272.0×`** | `remote_theorem_verified` → `remote_theorem_cache_hit` (`arch: "aarch64"`) |
| **`seed-shards --project-dir lean`** (`TheoremProofCAS` bulk seeding) | **`0.455 ms`** (`4` files, `17` shards) | **`0.286 ms`** (`5/5` split cache hits) | **`1.59×`** | **59,440 shards/s** (`16.8 µs/shard`) |
| **`check lean/TurboLean --project-dir lean`** (directory sweep after `seed-shards`) | `961 ms` | **`< 1 ms` (`0 ms`)** | **`> 961×`** | `all_shards_cached` (`4` files, `17` shard hits, `0` misses) |
| **`pr-verify --base HEAD --project-dir lean --receipt /tmp/spark_receipt.json`** | — | **`4.56 ms`** | — | `status: "pr_verified"`, `6` files, `17` unchanged theorems, `zero_sorry: true` |
| **`verify-receipt /tmp/spark_receipt.json --baseline-receipt /tmp/spark_receipt.json`** | — | **`0.019 ms` (`19 µs`)** | — | `status: "receipt_verified"`, `receipt_blake3: "1a2cdb3f06570258..."` |
| **`fast-check gpu/cudenote_bench.cu --remote-http`** (`POST /fast-check` on GB10 GPU) | **`2,437 ms`** (`compile_cache_hit: false`) | **`1,044 ms`** (`compile_cache_hit: true`) | **`2.33×`** | **`1,400.66 M states/s`** (10M valid lemma), **`990.78 M Denote-evals/s`** (`292/293` mutants killed) |
| **`sync http://127.0.0.1:9429 --bidirectional`** (pull + push delta sync) | **`22 ms`** (`18` actions, `13` blobs, `731 KB`) | **`1 ms`** (`0` actions, `0` bytes) | **`22.0×`** | `delta_push_noop: true`, `0` redundant bytes in both directions |

### 4.1 Exact JSON Outputs on `dgx-spark` (`aarch64`)

#### HTTP Remote Theorem-Shard Verification (`POST /check-shard` Cold → Warm)
```json
{
  "decl": "lookup_chain_sound",
  "elapsed_ms": 272,
  "interface_hash": "0ecfc08a217282da476dfce59703bc83cde29c6dc2b1776a63d989896a625a01",
  "prefix_env_hash": "0e2c55b08eb0f159f035945ed17fa0fc5a85e3b56389c22a610aab6d60459fb5",
  "remote_url": "http://127.0.0.1:9429",
  "server_arch": "aarch64",
  "server_elapsed_ms": 266,
  "shard_key": "cbc31e91c12d6e6701b139747dca7c40f69b7f8efd935ca6a7576a27c2b1b00c",
  "status": "remote_theorem_verified",
  "total_shards_in_file": 8
}
```
```json
{
  "decl": "lookup_chain_sound",
  "elapsed_ms": 1,
  "interface_hash": "0ecfc08a217282da476dfce59703bc83cde29c6dc2b1776a63d989896a625a01",
  "prefix_env_hash": "0e2c55b08eb0f159f035945ed17fa0fc5a85e3b56389c22a610aab6d60459fb5",
  "remote_url": "http://127.0.0.1:9429",
  "server_arch": "aarch64",
  "server_elapsed_ms": 0,
  "shard_key": "cbc31e91c12d6e6701b139747dca7c40f69b7f8efd935ca6a7576a27c2b1b00c",
  "status": "remote_theorem_cache_hit",
  "total_shards_in_file": 8
}
```

#### `seed-shards`, Directory `check`, `pr-verify`, and `verify-receipt`
```json
{
  "elapsed_ms": 0.286,
  "file_split_cache_hits": 5,
  "files_seeded": 4,
  "project_dir": "/tmp/turbo-lean-spark/lean",
  "shards_seeded": 17,
  "status": "shards_seeded",
  "trust_domain": "trusted"
}
```
```json
{
  "action_key": "pr-verify:HEAD:46304889106f9b9d",
  "altered_files": [],
  "elapsed_ms": 0.019,
  "files_audited": 6,
  "forbidden_constructs_found": 0,
  "interface_hash": "46304889106f9b9dc876ae08181625d057f8d5f58fa87a735bd151191b260b28",
  "mode": "trusted",
  "receipt_blake3": "1a2cdb3f06570258cf9b78a0394ad5ac57777e27adadd2c70cac833c30a5a50f",
  "schema_version": 1,
  "status": "receipt_verified",
  "theorem_shards": 17
}
```

#### HTTP Remote GPU `fast-check` (`compile_cache_hit: true` on NVIDIA GB10)
```json
{
  "binary_cache_key": "701e66e445b1d258b046395753ea62d0738de01ae280c718d39673d563d63718",
  "client_roundtrip_ms": 1044,
  "compile_cache_hit": true,
  "cumutate_kernel_ms": 2.9687,
  "cumutate_throughput_mevals_s": 986.96,
  "exec_ms": 1043,
  "fast_reject_3lemma_10m_kernel_ms": 22.4757,
  "fast_reject_3lemma_mstates_s": 444.92,
  "gpu_device": "NVIDIA GB10 (Compute Capability 12.1, 48 SMs)",
  "mode": "http_remote_gpu_cuda",
  "mutants_killed": 292,
  "mutants_total": 293,
  "remote_host": "http_server",
  "remote_http": "http://127.0.0.1:9429",
  "server_arch": "aarch64",
  "status": "ok",
  "throughput_mstates_s": 1396.29,
  "total_ms": 1043,
  "valid_lemma_10m_kernel_ms": 7.1618
}
```

---

## 5. In-Memory `Lean.Environment` Zygote Worker Pool & Full Evaluation Suite on `dgx-spark` (`aarch64`)

`lean/TurboLean/ZygoteWorker.lean` (`turbo-zygote-worker`) maintains a persistent JSON-over-stdio worker process inside `turbo-lean serve` that caches imported `Lean.Environment` snapshots in RAM keyed by import header (`import TurboLean.Reflection`, etc.). When a client submits a **brand-new, never-before-seen theorem proof** to `POST /check-shard`:
- **First uncached proof (`zygote_env_cache_hit: false`)**: Spawns the persistent worker, runs `Lean.importModules` once (`137.34 ms` on `aarch64`), caches the resulting `Lean.Environment` in RAM, and elaborates + kernel-checks the theorem via `Lean.Elab.runFrontend`.
- **Subsequent brand-new uncached proofs (`zygote_env_cache_hit: true`, `zygote_import_us: 0`)**: Reuses the in-memory `Lean.Environment` with **zero process spawn and zero `.olean` deserialization**, elaborating and kernel-checking brand-new proofs in **`1.74 ms – 3.09 ms`** (`1,740 µs – 3,089 µs`) on `aarch64` Cortex-X925 (**`101× – 180×` faster** than spawning a cold `lean` subprocess at `314.14 ms`).

### 5.1 `POST /check-shard` Zygote Worker Latency Progression on `dgx-spark` (`aarch64` Cortex-X925)

| Request to `POST /check-shard` (`import TurboLean.Reflection`) | `zygote_env_cache_hit` | `zygote_import_us` | `zygote_elab_us` (Pure Elab + Kernel Check) | `server_elapsed_us` (incl. SQLite CAS Write) | Client HTTP Round-Trip | Speedup vs Cold `lean` Subprocess (`314.14 ms`) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Proof 1**: `spark_zygote_mem_lookup_1` (`mem_lookup_chain_sound`, cold worker spawn + `.olean` import) | `false` | `137,340 µs` (`137.34 ms`) | `49,964 µs` (`49.96 ms`) | `2,474,268 µs` | `2,476.28 ms` | Cold Zygote bootstrap |
| **Proof 2**: `spark_zygote_mem_frame_2` (`mem_lookup_chain_frame_sound`, **brand-new uncached proof**) | **`true`** | **`0 µs`** | **`3,089 µs` (`3.09 ms`)** | **`3,712 µs` (`3.71 ms`)** | **`4.712 ms`** | **`66.7×` round-trip / `101.7×` elab** |
| **Proof 3**: `spark_zygote_storage_3` (`getStorage_setStorage_same`, **brand-new uncached proof**) | **`true`** | **`0 µs`** | **`1,740 µs` (`1.74 ms`)** | **`2,079 µs` (`2.08 ms`)** | **`3.119 ms`** | **`100.7×` round-trip / `180.5×` elab** |
| **`M19_zygote_new_proof_warm_env_ms`** (`run_eval.py` `zygote_eval_thm_2`, **brand-new uncached proof**) | **`true`** | **`0 µs`** | **`~1,600 µs` (`1.60 ms`)** | **`~2,000 µs` (`2.00 ms`)** | **`2.79 ms`** | **`112.6×` round-trip** |

### 5.2 Exact Zygote Worker JSON Telemetry on `dgx-spark` (`aarch64`)

```json
{
  "decl": "spark_zygote_mem_lookup_1",
  "interface_hash": "spark_iface_z",
  "prefix_env_hash": "spark_prefix_z",
  "server_arch": "aarch64",
  "server_elapsed_ms": 2474,
  "server_elapsed_us": 2474268,
  "shard_key": "spark_zygote_key_1",
  "status": "remote_theorem_verified",
  "zygote_elab_us": 49964,
  "zygote_env_cache_hit": false,
  "zygote_import_us": 137340,
  "zygote_used": true
}
```
```json
{
  "decl": "spark_zygote_mem_frame_2",
  "interface_hash": "spark_iface_z",
  "prefix_env_hash": "spark_prefix_z",
  "server_arch": "aarch64",
  "server_elapsed_ms": 3,
  "server_elapsed_us": 3712,
  "shard_key": "spark_zygote_key_2",
  "status": "remote_theorem_verified",
  "zygote_elab_us": 3089,
  "zygote_env_cache_hit": true,
  "zygote_import_us": 0,
  "zygote_used": true
}
```
```json
{
  "decl": "spark_zygote_storage_3",
  "interface_hash": "spark_iface_z",
  "prefix_env_hash": "spark_prefix_z",
  "server_arch": "aarch64",
  "server_elapsed_ms": 2,
  "server_elapsed_us": 2079,
  "shard_key": "spark_zygote_key_3",
  "status": "remote_theorem_verified",
  "zygote_elab_us": 1740,
  "zygote_env_cache_hit": true,
  "zygote_import_us": 0,
  "zygote_used": true
}
```

### 5.3 Full `autoresearch/run_eval.py` Suite on `dgx-spark` (`aarch64-unknown-linux-gnu`)

Executing the complete `python3 autoresearch/run_eval.py` invariant and benchmark harness natively on `dgx-spark` (`aarch64` Grace/Cortex-X925, `d92edc9`):

```json
{
  "invariants_passed": true,
  "kernel_inspector_verified": true,
  "kernel_expr_replay_verified": true,
  "cryptographic_receipt_verified": true,
  "git_pr_verify_verified": true,
  "multi_agent_singleflight_verified": true,
  "interface_hash": "5cf33a5e516c04ca481d3d7adfda5ecc78e17503caed2410d6f45206f8a7a693",
  "metrics": {
    "M1_ci_verify_cold_ms": 963.54,
    "M2_warm_build_hit_ms": 7.66,
    "M3_shard_check_cold_ms": 276.99,
    "M3_before_lake_env_cache_ms": 675.15,
    "M3_after_lake_env_cache_ms": 231.68,
    "M4_shard_check_warm_ms": 4.78,
    "M5_pack_import_ms": 14.07,
    "M5b_pack_import_warm_ms": 14.1,
    "M6_parallel_7_shards_ms": 428.85,
    "M6b_coalesced_2_shards_ms": 315.55,
    "M7_all_8_shards_warm_ms": 3.78,
    "M8_delta_sync_noop_ms": 4.21,
    "M9_delta_sync_incremental_ms": 50.91,
    "M9b_delta_sync_push_ms": 41.94,
    "M9c_delta_sync_push_noop_ms": 4.24,
    "M10_http_remote_fastcheck_ms": 1106.56,
    "M10b_http_remote_fastcheck_warm_ms": 8.75,
    "M10c_http_remote_shard_check_cold_ms": 314.14,
    "M10d_http_remote_shard_check_hit_ms": 6.43,
    "M10e_http_remote_batch_coalesced_ms": 318.19,
    "M8_inspector_shard_cold_ms": 468.97,
    "M9_inspector_shard_warm_ms": 3.31,
    "M10_assembler_shard_cold_ms": 484.35,
    "M11_assembler_shard_warm_ms": 2.48,
    "M12_kernel_adddecl_4_thms_us": 523.65,
    "M13_kernel_adddecl_4_thms_heartbeats": 5760,
    "M14_dir_check_warm_ms": 3.21,
    "M14b_cross_file_coalesced_cold_ms": 306.81,
    "M15_verify_receipt_ms": 2.11,
    "M16_pr_verify_proof_edit_ms": 307.54,
    "M16b_pr_verify_multi_file_edit_ms": 315.13,
    "M17_multi_agent_singleflight_4x_ms": 303.32,
    "M18_seed_shards_ms": 7.88,
    "M19_zygote_new_proof_warm_env_ms": 2.79,
    "stored_blobs": 38,
    "completed_actions": 23,
    "total_shard_hits": 57,
    "saved_compute_ms": 10486,
    "coalesced_singleflight_saves": 3
  }
}
```

### 5.4 Auto-Spawned Local Zygote Daemon (`7178c11`) CLI Evaluation on `dgx-spark` (`aarch64` Cortex-X925)

With PR #33 (`7178c11`), `turbo-lean check` and `turbo-lean pr-verify` automatically spawn and reuse a background local Zygote daemon (`/dev/shm/turbo-lean-staging/zygote_daemon.json`) without requiring a manual `turbo-lean serve` process. Comparing `dgx-spark` (`aarch64` Cortex-X925) evaluation metrics before (`d92edc9`) and after (`7178c11`) auto-spawned local Zygote integration:

| Metric on `dgx-spark` (`aarch64` Cortex-X925) | Subprocess Baseline (`d92edc9`) | Auto-Spawned Local Zygote (`7178c11`) | Speedup |
| :--- | :--- | :--- | :--- |
| **`M3_shard_check_cold_ms`** (`check Reflection.lean --decl lookup_chain_sound`) | `276.99 ms` | **`13.79 ms`** (`24.11 ms` 1st run) | **`20.09×`** |
| **`M3_after_lake_env_cache_ms`** (warmed `lake_env_cache` + local Zygote) | `231.68 ms` | **`17.93 ms`** (`18.98 ms` 1st run) | **`12.92×`** |
| **`M4_shard_check_warm_ms`** (`TheoremProofCAS` cache hit) | `4.78 ms` | **`1.71 ms`** | **`2.80×`** |
| **`M6_parallel_7_shards_ms`** (`check Reflection.lean --parallel-shards --jobs 4`) | `428.85 ms` | **`88.87 ms`** (`120.85 ms` 1st run) | **`4.83×`** |
| **`M6b_coalesced_2_shards_ms`** (`check FastCheck.lean --parallel-shards`) | `315.55 ms` | **`32.18 ms`** | **`9.81×`** |
| **`M10e_http_remote_batch_coalesced_ms`** (`POST /check-shards-batch`) | `318.19 ms` | **`32.73 ms`** | **`9.72×`** |
| **`M16b_pr_verify_multi_file_edit_ms`** (`pr-verify --base HEAD` across 2 edited files) | `315.13 ms` | **`38.30 ms`** | **`8.23×`** |
| **`M18_seed_shards_ms`** (`seed-shards --project-dir lean` with `file_stat_cache`) | `7.88 ms` | **`3.12 ms`** | **`2.53×`** |
| **`M19_zygote_new_proof_warm_env_ms`** (`POST /check-shard` brand-new proof) | `2.79 ms` | **`2.79 ms` – `7.11 ms`** | **`44.2× – 112.6×`** |
| **`M20_local_check_new_proof_zygote_ms`** (`check FastCheck.lean --decl addWithCarry_zero_right` new proof edit) | `276.99 ms` (no local Zygote) | **`8.73 ms`** (`16.65 ms` 1st run) | **`31.73×`** |

```json
{
  "invariants_passed": true,
  "kernel_inspector_verified": true,
  "kernel_expr_replay_verified": true,
  "cryptographic_receipt_verified": true,
  "git_pr_verify_verified": true,
  "multi_agent_singleflight_verified": true,
  "interface_hash": "5cf33a5e516c04ca481d3d7adfda5ecc78e17503caed2410d6f45206f8a7a693",
  "metrics": {
    "M1_ci_verify_cold_ms": 1741.68,
    "M2_warm_build_hit_ms": 10.02,
    "M3_shard_check_cold_ms": 13.79,
    "M3_before_lake_env_cache_ms": 1065.64,
    "M3_after_lake_env_cache_ms": 17.93,
    "M4_shard_check_warm_ms": 1.71,
    "M5_pack_import_ms": 10.8,
    "M5b_pack_import_warm_ms": 13.6,
    "M6_parallel_7_shards_ms": 88.87,
    "M6b_coalesced_2_shards_ms": 32.18,
    "M7_all_8_shards_warm_ms": 2.82,
    "M8_delta_sync_noop_ms": 4.35,
    "M9_delta_sync_incremental_ms": 46.58,
    "M9b_delta_sync_push_ms": 36.02,
    "M9c_delta_sync_push_noop_ms": 2.32,
    "M10_http_remote_fastcheck_ms": 1072.96,
    "M10b_http_remote_fastcheck_warm_ms": 10.42,
    "M10c_http_remote_shard_check_cold_ms": 568.03,
    "M10d_http_remote_shard_check_hit_ms": 5.68,
    "M10e_http_remote_batch_coalesced_ms": 32.73,
    "M8_inspector_shard_cold_ms": 497.67,
    "M9_inspector_shard_warm_ms": 3.97,
    "M10_assembler_shard_cold_ms": 1098.87,
    "M11_assembler_shard_warm_ms": 3.17,
    "M12_kernel_adddecl_4_thms_us": 493.84,
    "M13_kernel_adddecl_4_thms_heartbeats": 5760,
    "M14_dir_check_warm_ms": 2.86,
    "M14b_cross_file_coalesced_cold_ms": 733.62,
    "M15_verify_receipt_ms": 3.22,
    "M16_pr_verify_proof_edit_ms": 755.71,
    "M16b_pr_verify_multi_file_edit_ms": 38.3,
    "M17_multi_agent_singleflight_4x_ms": 812.24,
    "M18_seed_shards_ms": 3.12,
    "M19_zygote_new_proof_warm_env_ms": 7.11,
    "M20_local_check_new_proof_zygote_ms": 8.73,
    "stored_blobs": 38,
    "completed_actions": 23,
    "total_shard_hits": 57,
    "saved_compute_ms": 17369,
    "coalesced_singleflight_saves": 3
  }
}
```

### 5.5 `TCP_NODELAY` Single-Buffer Framing & Coalesced Local Zygote Routing (`9f4600d` / `afeb95e`) on `dgx-spark` (`aarch64` Cortex-X925)

PR #36 (`9f4600d`) sets `TCP_NODELAY` with single-buffer HTTP framing across all Zygote/coordinator sockets (eliminating 40 ms Linux Nagle/delayed-ACK stalls), canonicalizes project `.olean` search paths, and routes single-file coalesced (`M6b`), cross-file coalesced (`M14b`), `Inspector` (`M8`), `Assembler` (`M10`), `pr-verify` (`M16`, `M16b`), and 4-agent Singleflight (`M17`) verification through the persistent local `Lean.Environment` Zygote daemon:

| Metric on `dgx-spark` (`aarch64` Cortex-X925) | Subprocess Baseline (`d92edc9`) | Initial Auto-Zygote (`7178c11`) | Coalesced Auto-Zygote + `TCP_NODELAY` (`afeb95e`) | Total Speedup vs Baseline |
| :--- | :--- | :--- | :--- | :--- |
| **`M3_shard_check_cold_ms`** (`check Reflection.lean --decl lookup_chain_sound`) | `276.99 ms` | `13.79 ms` | **`20.79 ms`** (`11.97 ms` `M3_after_lake_env_cache_ms`) | **`23.14×`** |
| **`M6b_coalesced_2_shards_ms`** (single-file coalesced 2 shards in `FastCheck.lean`) | `315.55 ms` | `32.18 ms` | **`30.23 ms`** | **`10.44×`** |
| **`M8_inspector_shard_cold_ms`** (`check Inspector.lean --decl propext_is_allowed`) | `468.97 ms` | `497.67 ms` | **`18.82 ms`** (warm Zygote) / `430.96 ms` (1st import) | **`24.92×`** |
| **`M10_assembler_shard_cold_ms`** (`check Assembler.lean --decl exprHeadTag_pos`) | `484.35 ms` | `1,098.87 ms` | **`16.35 ms`** (warm Zygote) / `465.48 ms` (1st import) | **`29.62×`** |
| **`M10e_http_remote_batch_coalesced_ms`** (`POST /check-shards-batch`) | `318.19 ms` | `32.73 ms` | **`27.96 ms`** | **`11.38×`** |
| **`M14b_cross_file_coalesced_cold_ms`** (cross-file coalesced `Reflection.lean` + `FastCheck.lean`) | `306.81 ms` | `733.62 ms` | **`21.06 ms`** (`22.02 ms` 2nd run) | **`14.57×`** (`34.83×` vs `7178c11`) |
| **`M16_pr_verify_proof_edit_ms`** (`pr-verify --base HEAD --mode untrusted`) | `307.54 ms` | `755.71 ms` | **`12.98 ms`** (`13.64 ms` 1st run) | **`23.69×`** (`58.22×` vs `7178c11`) |
| **`M16b_pr_verify_multi_file_edit_ms`** (`pr-verify --base HEAD` multi-file proof edit) | `315.13 ms` | `38.30 ms` | **`19.34 ms`** (`22.72 ms` 2nd run) | **`16.29×`** |
| **`M17_multi_agent_singleflight_4x_ms`** (4-agent concurrent Singleflight + local Zygote) | `303.32 ms` | `812.24 ms` | **`12.16 ms`** (`15.98 ms` 1st run) | **`24.94×`** (`66.80×` vs `7178c11`) |
| **`M19_zygote_new_proof_warm_env_ms`** (`POST /check-shard` brand-new proof) | `2.79 ms` | `7.11 ms` | **`1.92 ms`** (`2.19 ms` 2nd run) | **`163.61×`** (vs `314.14 ms` cold) |
| **`M20_local_check_new_proof_zygote_ms`** (`check FastCheck.lean --decl addWithCarry_zero_right` new proof) | `276.99 ms` | `8.73 ms` | **`14.17 ms`** | **`19.55×`** |

```json
{
  "invariants_passed": true,
  "kernel_inspector_verified": true,
  "kernel_expr_replay_verified": true,
  "cryptographic_receipt_verified": true,
  "git_pr_verify_verified": true,
  "multi_agent_singleflight_verified": true,
  "interface_hash": "9574c57f83b8de9023cfac48bd47b8ab15f38820508b6dc7b576557348e4d9a0",
  "metrics": {
    "M1_ci_verify_cold_ms": 1237.08,
    "M2_warm_build_hit_ms": 4.57,
    "M3_shard_check_cold_ms": 21.47,
    "M3_before_lake_env_cache_ms": 668.01,
    "M3_after_lake_env_cache_ms": 20.56,
    "M4_shard_check_warm_ms": 1.82,
    "M5_pack_import_ms": 10.36,
    "M5b_pack_import_warm_ms": 10.18,
    "M6_parallel_7_shards_ms": 100.04,
    "M6b_coalesced_2_shards_ms": 30.23,
    "M7_all_8_shards_warm_ms": 2.46,
    "M8_delta_sync_noop_ms": 3.14,
    "M9_delta_sync_incremental_ms": 35.94,
    "M9b_delta_sync_push_ms": 29.5,
    "M9c_delta_sync_push_noop_ms": 3.29,
    "M10_http_remote_fastcheck_ms": 772.04,
    "M10b_http_remote_fastcheck_warm_ms": 6.28,
    "M10c_http_remote_shard_check_cold_ms": 251.21,
    "M10d_http_remote_shard_check_hit_ms": 5.25,
    "M10e_http_remote_batch_coalesced_ms": 47.71,
    "M8_inspector_shard_cold_ms": 18.82,
    "M9_inspector_shard_warm_ms": 2.53,
    "M10_assembler_shard_cold_ms": 16.35,
    "M11_assembler_shard_warm_ms": 2.33,
    "M12_kernel_adddecl_4_thms_us": 362.21,
    "M13_kernel_adddecl_4_thms_heartbeats": 5760,
    "M14_dir_check_warm_ms": 2.29,
    "M14b_cross_file_coalesced_cold_ms": 22.02,
    "M15_verify_receipt_ms": 1.53,
    "M16_pr_verify_proof_edit_ms": 12.98,
    "M16b_pr_verify_multi_file_edit_ms": 22.72,
    "M17_multi_agent_singleflight_4x_ms": 12.16,
    "M18_seed_shards_ms": 4.53,
    "M19_zygote_new_proof_warm_env_ms": 2.19,
    "M20_local_check_new_proof_zygote_ms": 14.17,
    "stored_blobs": 38,
    "completed_actions": 23,
    "total_shard_hits": 57,
    "saved_compute_ms": 4367,
    "coalesced_singleflight_saves": 3
  }
}
```

### 5.6 Unified 4-Module Zygote `Lean.Environment` & Background Pre-Warming (`e5c856b`) First-Run Evaluation on `dgx-spark` (`aarch64` Cortex-X925)

PR #41 (`e5c856b`) unifies all project modules (`TurboLean.Assembler`, `TurboLean.FastCheck`, `TurboLean.Inspector`, `TurboLean.Reflection`) into a single canonical in-memory `Lean.Environment` key inside `ZygoteWorker` and pre-warms the Zygote environment asynchronously during `turbo-lean serve`, `turbo-lean build`, and `turbo-lean ci-verify`. Even starting from a completely cold machine (after terminating any prior Zygote daemon), **first-run** cold shard verification latencies on `dgx-spark` (`aarch64` Cortex-X925) drop by **`17× – 27×`**:

| First-Run Cold Metric on `dgx-spark` (`aarch64` Cortex-X925) | Subprocess Baseline (`d92edc9`) | Prior First-Run (`afeb95e`) | Pre-Warmed Unified Zygote First-Run (`e5c856b`) | First-Run Speedup |
| :--- | :--- | :--- | :--- | :--- |
| **`M10c_http_remote_shard_check_cold_ms`** (1st `POST /check-shard` to `serve`) | `314.14 ms` | `505.24 ms` | **`25.06 ms`** | **`20.16×`** (vs `afeb95e`) / **`12.54×`** (vs baseline) |
| **`M8_inspector_shard_cold_ms`** (1st `check Inspector.lean --decl propext_is_allowed`) | `468.97 ms` | `430.96 ms` | **`26.63 ms`** (`18.82 ms` 2nd run) | **`16.18×`** (vs `afeb95e`) / **`17.61×`** (vs baseline) |
| **`M10_assembler_shard_cold_ms`** (1st `check Assembler.lean --decl exprHeadTag_pos`) | `484.35 ms` | `465.48 ms` | **`17.99 ms`** (`16.35 ms` 2nd run) | **`25.87×`** (vs `afeb95e`) / **`26.92×`** (vs baseline) |
| **`M3_shard_check_cold_ms`** (1st `check Reflection.lean --decl lookup_chain_sound` after `ci-verify`) | `276.99 ms` | `20.79 ms` | **`35.34 ms`** (`21.47 ms` 2nd run) | **`7.84× – 12.90×`** |
| **`M3_after_lake_env_cache_ms`** (warmed `lake_env_cache` + unified Zygote) | `231.68 ms` | `11.97 ms` | **`18.41 ms`** | **`12.58×`** |
| **`M14b_cross_file_coalesced_cold_ms`** (cross-file coalesced `Reflection.lean` + `FastCheck.lean`) | `306.81 ms` | `21.06 ms` | **`26.06 ms`** | **`11.77×`** |
| **`M16_pr_verify_proof_edit_ms`** (`pr-verify --base HEAD --mode untrusted`) | `307.54 ms` | `13.64 ms` | **`20.39 ms`** | **`15.08×`** |
| **`M16b_pr_verify_multi_file_edit_ms`** (`pr-verify --base HEAD` multi-file edit) | `315.13 ms` | `19.34 ms` | **`24.05 ms`** | **`13.10×`** |
| **`M17_multi_agent_singleflight_4x_ms`** (4-agent concurrent Singleflight + unified Zygote) | `303.32 ms` | `15.98 ms` | **`14.60 ms`** | **`20.78×`** |
| **`M19_zygote_new_proof_warm_env_ms`** (`POST /check-shard` brand-new proof) | `2.79 ms` | `1.92 ms` | **`2.95 ms`** | **`106.5×`** (vs `314.14 ms` cold) |
| **`M20_local_check_new_proof_zygote_ms`** (`check FastCheck.lean --decl addWithCarry_zero_right` new proof) | `276.99 ms` | `17.94 ms` | **`12.78 ms`** | **`21.67×`** |

```json
{
  "invariants_passed": true,
  "kernel_inspector_verified": true,
  "kernel_expr_replay_verified": true,
  "cryptographic_receipt_verified": true,
  "git_pr_verify_verified": true,
  "multi_agent_singleflight_verified": true,
  "interface_hash": "2e515814c0968c827a55ca4115855ea7dc445781a782fa3ad8f3e5c4ef770059",
  "metrics": {
    "M1_ci_verify_cold_ms": 1793.74,
    "M2_warm_build_hit_ms": 7.53,
    "M3_shard_check_cold_ms": 35.34,
    "M3_before_lake_env_cache_ms": 1071.01,
    "M3_after_lake_env_cache_ms": 18.41,
    "M4_shard_check_warm_ms": 5.68,
    "M5_pack_import_ms": 11.47,
    "M5b_pack_import_warm_ms": 9.78,
    "M6_parallel_7_shards_ms": 142.06,
    "M6b_coalesced_2_shards_ms": 48.67,
    "M7_all_8_shards_warm_ms": 4.24,
    "M8_delta_sync_noop_ms": 6.21,
    "M9_delta_sync_incremental_ms": 47.44,
    "M9b_delta_sync_push_ms": 51.88,
    "M9c_delta_sync_push_noop_ms": 2.82,
    "M10_http_remote_fastcheck_ms": 1899.55,
    "M10b_http_remote_fastcheck_warm_ms": 21.77,
    "M10c_http_remote_shard_check_cold_ms": 25.06,
    "M10d_http_remote_shard_check_hit_ms": 6.28,
    "M10e_http_remote_batch_coalesced_ms": 31.85,
    "M8_inspector_shard_cold_ms": 26.63,
    "M9_inspector_shard_warm_ms": 2.07,
    "M10_assembler_shard_cold_ms": 17.99,
    "M11_assembler_shard_warm_ms": 4.29,
    "M12_kernel_adddecl_4_thms_us": 763.46,
    "M13_kernel_adddecl_4_thms_heartbeats": 5760,
    "M14_dir_check_warm_ms": 2.45,
    "M14b_cross_file_coalesced_cold_ms": 26.06,
    "M15_verify_receipt_ms": 1.88,
    "M16_pr_verify_proof_edit_ms": 20.39,
    "M16b_pr_verify_multi_file_edit_ms": 24.05,
    "M17_multi_agent_singleflight_4x_ms": 14.6,
    "M18_seed_shards_ms": 4.9,
    "M19_zygote_new_proof_warm_env_ms": 2.95,
    "M20_local_check_new_proof_zygote_ms": 12.78,
    "stored_blobs": 38,
    "completed_actions": 23,
    "total_shard_hits": 57,
    "saved_compute_ms": 5469,
    "coalesced_singleflight_saves": 3
  }
}
```

### 5.7 Direct `clang+lld` Dynamic `libleanshared.so` Fast-Check & `/dev/shm` Staging (`5834d59`) on `dgx-spark` (`aarch64` Cortex-X925)

PR #45 (`5834d59`) replaces the `leanc` shell wrapper and static archive link in `fast-check` with direct `clang -O2 -fuse-ld=lld` dynamic linking against `libleanshared.so`, uses a minimal `prelude` + `Init.Data.UInt` harness for pure Perceus/FBIP arithmetic specs, and stages all intermediate `.lean`/`.c`/binary artifacts in `/dev/shm` (`RAM`). On `dgx-spark` (`aarch64` Cortex-X925), cold `POST /fast-check` compilation + linking + 1,000,000-state execution (`M10_http_remote_fastcheck_ms`) drops from **`1,899.55 ms` to `500.28 ms` (`3.80×` speedup)**, and `M3_before_lake_env_cache_ms` drops from **`1,071.01 ms` to `427.04 ms` (`2.51×` speedup)**:

| Metric on `dgx-spark` (`aarch64` Cortex-X925) | Subprocess Baseline (`d92edc9`) | Prior Unified Zygote (`e5c856b`) | Dynamic `clang+lld` + `/dev/shm` (`5834d59`) | Speedup |
| :--- | :--- | :--- | :--- | :--- |
| **`M10_http_remote_fastcheck_ms`** (Cold `POST /fast-check`: `lean -c` + `clang+lld` + 1M states) | `1,106.56 ms` | `1,899.55 ms` | **`500.28 ms`** | **`3.80×`** (vs `e5c856b`) / **`2.21×`** (vs `d92edc9`) |
| **`M10b_http_remote_fastcheck_warm_ms`** (Warm `POST /fast-check` binary cache hit + 1M states) | `8.75 ms` | `21.77 ms` | **`11.24 ms`** | **`1.94×`** (vs `e5c856b`) / **`44.5×`** (vs cold) |
| **`M3_before_lake_env_cache_ms`** (First cold shard check with `/dev/shm` staging) | `675.15 ms` | `1,071.01 ms` | **`427.04 ms`** | **`2.51×`** (vs `e5c856b`) / **`1.58×`** (vs `d92edc9`) |
| **`M3_shard_check_cold_ms`** (`check Reflection.lean --decl lookup_chain_sound`) | `276.99 ms` | `35.34 ms` | **`19.42 ms`** | **`14.26×`** (vs baseline) |
| **`M10c_http_remote_shard_check_cold_ms`** (1st `POST /check-shard` to `serve`) | `314.14 ms` | `25.06 ms` | **`17.73 ms`** | **`17.72×`** (vs baseline) |
| **`M8_inspector_shard_cold_ms`** (1st `check Inspector.lean --decl propext_is_allowed`) | `468.97 ms` | `26.63 ms` | **`19.62 ms`** | **`23.90×`** (vs baseline) |
| **`M10_assembler_shard_cold_ms`** (1st `check Assembler.lean --decl exprHeadTag_pos`) | `484.35 ms` | `17.99 ms` | **`16.66 ms`** | **`29.07×`** (vs baseline) |
| **`M12_kernel_adddecl_4_thms_us`** (`Lean.addDecl` kernel replay of 4 theorems) | `523.65 µs` | `763.46 µs` | **`334.31 µs`** | **`1.57×`** (vs baseline) |
| **`M14b_cross_file_coalesced_cold_ms`** (cross-file coalesced `Reflection.lean` + `FastCheck.lean`) | `306.81 ms` | `26.06 ms` | **`20.32 ms`** | **`15.10×`** (vs baseline) |
| **`M16_pr_verify_proof_edit_ms`** (`pr-verify --base HEAD --mode untrusted`) | `307.54 ms` | `20.39 ms` | **`17.66 ms`** | **`17.41×`** (vs baseline) |
| **`M16b_pr_verify_multi_file_edit_ms`** (`pr-verify --base HEAD` multi-file edit) | `315.13 ms` | `24.05 ms` | **`20.47 ms`** | **`15.39×`** (vs baseline) |
| **`M19_zygote_new_proof_warm_env_ms`** (`POST /check-shard` brand-new proof) | `2.79 ms` | `2.95 ms` | **`2.22 ms`** | **`141.5×`** (vs `314.14 ms` cold) |
| **`M20_local_check_new_proof_zygote_ms`** (`check FastCheck.lean --decl addWithCarry_zero_right` new proof) | `276.99 ms` | `12.78 ms` | **`8.54 ms`** | **`32.43×`** (vs baseline) |

```json
{
  "invariants_passed": true,
  "kernel_inspector_verified": true,
  "kernel_expr_replay_verified": true,
  "cryptographic_receipt_verified": true,
  "git_pr_verify_verified": true,
  "multi_agent_singleflight_verified": true,
  "interface_hash": "8df45542c6144b3793c9c71508cd2f92f0e502b3c8601fa5adc80ee33a365010",
  "metrics": {
    "M1_ci_verify_cold_ms": 1341.61,
    "M2_warm_build_hit_ms": 5.59,
    "M3_shard_check_cold_ms": 19.42,
    "M3_before_lake_env_cache_ms": 427.04,
    "M3_after_lake_env_cache_ms": 19.34,
    "M4_shard_check_warm_ms": 1.82,
    "M5_pack_import_ms": 12.36,
    "M5b_pack_import_warm_ms": 11.91,
    "M6_parallel_7_shards_ms": 112.54,
    "M6b_coalesced_2_shards_ms": 30.45,
    "M7_all_8_shards_warm_ms": 1.89,
    "M8_delta_sync_noop_ms": 2.83,
    "M9_delta_sync_incremental_ms": 29.25,
    "M9b_delta_sync_push_ms": 33.82,
    "M9c_delta_sync_push_noop_ms": 3.57,
    "M10_http_remote_fastcheck_ms": 500.28,
    "M10b_http_remote_fastcheck_warm_ms": 11.24,
    "M10c_http_remote_shard_check_cold_ms": 17.73,
    "M10d_http_remote_shard_check_hit_ms": 5.41,
    "M10e_http_remote_batch_coalesced_ms": 31.57,
    "M8_inspector_shard_cold_ms": 19.62,
    "M9_inspector_shard_warm_ms": 1.81,
    "M10_assembler_shard_cold_ms": 16.66,
    "M11_assembler_shard_warm_ms": 2.0,
    "M12_kernel_adddecl_4_thms_us": 334.31,
    "M13_kernel_adddecl_4_thms_heartbeats": 5760,
    "M14_dir_check_warm_ms": 2.95,
    "M14b_cross_file_coalesced_cold_ms": 20.32,
    "M15_verify_receipt_ms": 2.38,
    "M16_pr_verify_proof_edit_ms": 17.66,
    "M16b_pr_verify_multi_file_edit_ms": 20.47,
    "M17_multi_agent_singleflight_4x_ms": 15.44,
    "M18_seed_shards_ms": 4.92,
    "M19_zygote_new_proof_warm_env_ms": 2.22,
    "M20_local_check_new_proof_zygote_ms": 8.54,
    "stored_blobs": 38,
    "completed_actions": 23,
    "total_shard_hits": 57,
    "saved_compute_ms": 4334,
    "coalesced_singleflight_saves": 3
  }
}
```

### 5.8 Bulk SQLite Manifest JOINs & Zero-Subprocess In-Memory `TLPK v2` Streaming (`0b330a0` / `44f45ed`) on `dgx-spark` (`aarch64` Cortex-X925)

PR #49 (`0b330a0`) and PR #50 (`44f45ed`) eliminate N+1 per-action `action_outputs` SQLite queries in `CasStore::export_manifest` via a single bulk `JOIN`, stream `TLPK v2` archives directly in memory (with optional in-process zstd magic-byte detection `0xFD2FB528` and zero `zstd` CLI subprocesses or temp files), and pre-populate known CAS blob hashes before `import_pack_bytes` to skip redundant `fs::metadata` / `blake3::hash` / `fs::write` calls on existing blobs. On `dgx-spark` (`aarch64` Cortex-X925), cold `.tlpack` import (`M5_pack_import_ms`) drops from **`12.36 ms` to `8.60 ms` (`1.44×` speedup)**, warm `.tlpack` import (`M5b_pack_import_warm_ms`) drops from **`11.91 ms` to `5.33 ms` (`2.23×` speedup)**, incremental HTTP delta pull (`M9_delta_sync_incremental_ms`) drops from **`29.25 ms` to `12.94 ms` (`2.26×` speedup, `3.93×` vs baseline)**, and HTTP delta push (`M9b_delta_sync_push_ms`) drops from **`33.82 ms` to `13.71 ms` (`2.47×` speedup, `3.06×` vs baseline)**:

| Metric on `dgx-spark` (`aarch64` Cortex-X925) | Subprocess Baseline (`d92edc9`) | Prior Dynamic `clang+lld` (`5834d59`) | In-Memory `TLPK v2` + Bulk SQL (`44f45ed`) | Speedup |
| :--- | :--- | :--- | :--- | :--- |
| **`M5_pack_import_ms`** (Cold `.tlpack` import into fresh CAS) | `14.07 ms` | `12.36 ms` | **`8.60 ms`** | **`1.44×`** (vs `5834d59`) / **`1.64×`** (vs `d92edc9`) |
| **`M5b_pack_import_warm_ms`** (Warm zero-copy `.tlpack` import with pre-seeded CAS hash set) | `14.10 ms` | `11.91 ms` | **`5.33 ms`** | **`2.23×`** (vs `5834d59`) / **`2.65×`** (vs `d92edc9`) |
| **`M9_delta_sync_incremental_ms`** (HTTP delta pull: `GET /manifest` + `POST /export-delta` + import) | `50.91 ms` | `29.25 ms` | **`12.94 ms`** | **`2.26×`** (vs `5834d59`) / **`3.93×`** (vs `d92edc9`) |
| **`M9b_delta_sync_push_ms`** (HTTP delta push: `sync --push` → `POST /import-delta`) | `41.94 ms` | `33.82 ms` | **`13.71 ms`** | **`2.47×`** (vs `5834d59`) / **`3.06×`** (vs `d92edc9`) |
| **`M9c_delta_sync_push_noop_ms`** (Warm no-op HTTP delta push) | `3.21 ms` | `3.57 ms` | **`2.53 ms`** | **`1.41×`** (vs `5834d59`) |
| **`M10_http_remote_fastcheck_ms`** (Cold `POST /fast-check`: `lean -c` + `clang+lld` + 1M states) | `1,106.56 ms` | `500.28 ms` | **`411.94 ms`** | **`2.69×`** (vs `d92edc9`) / **`4.61×`** (vs `e5c856b`) |
| **`M10b_http_remote_fastcheck_warm_ms`** (Warm `POST /fast-check` binary cache hit + 1M states) | `8.75 ms` | `11.24 ms` | **`10.64 ms`** | **`38.7×`** (vs cold) |
| **`M3_before_lake_env_cache_ms`** (First cold shard check with `/dev/shm` staging) | `675.15 ms` | `427.04 ms` | **`386.17 ms`** | **`1.75×`** (vs `d92edc9`) / **`2.77×`** (vs `e5c856b`) |
| **`M3_shard_check_cold_ms`** (`check Reflection.lean --decl lookup_chain_sound`) | `276.99 ms` | `19.42 ms` | **`13.09 ms`** | **`21.16×`** (vs baseline) |
| **`M6_parallel_7_shards_ms`** (Parallel verification of 7 `Reflection.lean` shards) | `541.40 ms` | `112.54 ms` | **`81.20 ms`** | **`6.67×`** (vs baseline) |
| **`M8_inspector_shard_cold_ms`** (1st `check Inspector.lean --decl propext_is_allowed`) | `468.97 ms` | `19.62 ms` | **`17.64 ms`** | **`26.59×`** (vs baseline) |
| **`M10_assembler_shard_cold_ms`** (1st `check Assembler.lean --decl exprHeadTag_pos`) | `484.35 ms` | `16.66 ms` | **`11.34 ms`** | **`42.71×`** (vs baseline) |
| **`M14b_cross_file_coalesced_cold_ms`** (cross-file coalesced `Reflection.lean` + `FastCheck.lean`) | `306.81 ms` | `20.32 ms` | **`18.97 ms`** | **`16.17×`** (vs baseline) |
| **`M17_multi_agent_singleflight_4x_ms`** (4 concurrent `check-shard` requests coalesced) | `297.70 ms` | `15.44 ms` | **`10.07 ms`** | **`29.56×`** (vs baseline) |
| **`M19_zygote_new_proof_warm_env_ms`** (`POST /check-shard` brand-new proof) | `2.79 ms` | `2.22 ms` | **`2.82 ms`** | **`111.4×`** (vs `314.14 ms` cold) |

```json
{
  "invariants_passed": true,
  "kernel_inspector_verified": true,
  "kernel_expr_replay_verified": true,
  "cryptographic_receipt_verified": true,
  "git_pr_verify_verified": true,
  "multi_agent_singleflight_verified": true,
  "interface_hash": "3f3085d0f9ee03c338761a8cfbf9b0a18cc73564114fb09a9fc24680a82da844",
  "metrics": {
    "M1_ci_verify_cold_ms": 1081.36,
    "M2_warm_build_hit_ms": 7.24,
    "M3_shard_check_cold_ms": 13.09,
    "M3_before_lake_env_cache_ms": 386.17,
    "M3_after_lake_env_cache_ms": 14.06,
    "M4_shard_check_warm_ms": 1.85,
    "M5_pack_import_ms": 8.6,
    "M5b_pack_import_warm_ms": 5.33,
    "M6_parallel_7_shards_ms": 81.2,
    "M6b_coalesced_2_shards_ms": 28.68,
    "M7_all_8_shards_warm_ms": 2.04,
    "M8_delta_sync_noop_ms": 3.52,
    "M9_delta_sync_incremental_ms": 12.94,
    "M9b_delta_sync_push_ms": 13.71,
    "M9c_delta_sync_push_noop_ms": 2.53,
    "M10_http_remote_fastcheck_ms": 411.94,
    "M10b_http_remote_fastcheck_warm_ms": 10.64,
    "M10c_http_remote_shard_check_cold_ms": 35.86,
    "M10d_http_remote_shard_check_hit_ms": 2.79,
    "M10e_http_remote_batch_coalesced_ms": 30.23,
    "M8_inspector_shard_cold_ms": 17.64,
    "M9_inspector_shard_warm_ms": 2.43,
    "M10_assembler_shard_cold_ms": 11.34,
    "M11_assembler_shard_warm_ms": 1.23,
    "M12_kernel_adddecl_4_thms_us": 749.87,
    "M13_kernel_adddecl_4_thms_heartbeats": 5760,
    "M14_dir_check_warm_ms": 3.41,
    "M14b_cross_file_coalesced_cold_ms": 18.97,
    "M15_verify_receipt_ms": 2.28,
    "M16_pr_verify_proof_edit_ms": 19.76,
    "M16b_pr_verify_multi_file_edit_ms": 23.54,
    "M17_multi_agent_singleflight_4x_ms": 10.07,
    "M18_seed_shards_ms": 4.17,
    "M19_zygote_new_proof_warm_env_ms": 2.82,
    "M20_local_check_new_proof_zygote_ms": 14.69,
    "stored_blobs": 38,
    "completed_actions": 23,
    "total_shard_hits": 57,
    "saved_compute_ms": 3897,
    "coalesced_singleflight_saves": 3
  }
}
```
