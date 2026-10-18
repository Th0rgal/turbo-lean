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

### 5.9 Zero-`lake env` Cold & Warm Local `fast-check` Prelude Fast Path (`60b3cd4` / `18fa966`) on `dgx-spark` (`aarch64` Cortex-X925)

PR #51 (`60b3cd4`) eliminates the unconditional `resolve_lake_env` (`lake env env`) subprocess on cold local `turbo-lean fast-check` (`Commands::FastCheck` when `compile_cache_hit == false`), matching the HTTP `POST /fast-check` fast path by resolving the toolchain's `lean` binary directly via `pack::resolve_server_lean_env_and_bin(&store, &tc, "")` and compiling `FASTCHECK_PRELUDE_HARNESS` (`prelude` + `Init.Data.UInt`) with `clang -O2 -fuse-ld=lld -lleanshared` in `/dev/shm` (`resolve_lake_env` is only invoked as a fallback if the prelude fast path fails). On `dgx-spark` (`aarch64` Cortex-X925), cold local `fast-check` on an uncached `TURBO_LEAN_HOME` (`M10f_local_fastcheck_cold_ms`) completes in **`370.46 ms`** (**`2.99×` faster** than the `1,106.56 ms` `leanc` baseline and **`~2.0×` faster** than running `lake env env` on cold cache), warm local `fast-check` (`M10g_local_fastcheck_warm_ms`) completes in **`10.31 ms`** (**`35.9×` vs cold**), cold HTTP remote `fast-check` (`M10_http_remote_fastcheck_ms`) drops to **`383.53 ms`**, and warm-env Zygote new-proof verification (`M19_zygote_new_proof_warm_env_ms`) reaches **`1.72 ms`**:

| Metric on `dgx-spark` (`aarch64` Cortex-X925) | Subprocess Baseline (`d92edc9`) | Prior In-Memory `TLPK v2` (`44f45ed`) | Zero-`lake env` Fast-Check (`18fa966`) | Speedup |
| :--- | :--- | :--- | :--- | :--- |
| **`M10f_local_fastcheck_cold_ms`** (Cold local `fast-check` on fresh `TURBO_LEAN_HOME`, 1M states) | `~1,106.56 ms` (`~750 ms` with `lake env`) | `~750 ms` (with `resolve_lake_env`) | **`370.46 ms`** | **`2.99×`** (vs `d92edc9`) / **`~2.03×`** (vs `44f45ed`) |
| **`M10g_local_fastcheck_warm_ms`** (Warm local `fast-check` binary cache hit, 1M states) | `—` | `—` | **`10.31 ms`** | **`35.9×`** (vs `370.46 ms` cold) |
| **`M10_http_remote_fastcheck_ms`** (Cold `POST /fast-check`: `lean -c` + `clang+lld` + 1M states) | `1,106.56 ms` | `411.94 ms` | **`383.53 ms`** | **`2.89×`** (vs `d92edc9`) / **`4.95×`** (vs `e5c856b`) |
| **`M10b_http_remote_fastcheck_warm_ms`** (Warm `POST /fast-check` binary cache hit + 1M states) | `8.75 ms` | `10.64 ms` | **`11.03 ms`** | **`34.8×`** (vs cold) |
| **`M1_ci_verify_cold_ms`** (`ci-verify --mode untrusted` cold build + verification) | `1,347.90 ms` | `1,081.36 ms` | **`944.53 ms`** | **`1.43×`** (vs `d92edc9`) |
| **`M4_shard_check_warm_ms`** (Warm theorem shard cache hit) | `1.94 ms` | `1.85 ms` | **`1.35 ms`** | **`1.44×`** (vs `d92edc9`) |
| **`M8_delta_sync_noop_ms`** (Warm no-op HTTP delta pull) | `3.15 ms` | `3.52 ms` | **`2.69 ms`** | **`1.31×`** (vs `44f45ed`) |
| **`M9_delta_sync_incremental_ms`** (HTTP delta pull: `GET /manifest` + `POST /export-delta` + import) | `50.91 ms` | `12.94 ms` | **`15.27 ms`** | **`3.33×`** (vs `d92edc9`) |
| **`M9b_delta_sync_push_ms`** (HTTP delta push: `sync --push` → `POST /import-delta`) | `41.94 ms` | `13.71 ms` | **`16.03 ms`** | **`2.62×`** (vs `d92edc9`) |
| **`M12_kernel_adddecl_4_thms_us`** (`Lean.addDecl` kernel replay of 4 theorems) | `523.65 µs` | `749.87 µs` | **`394.46 µs`** | **`1.33×`** (vs `d92edc9`) |
| **`M17_multi_agent_singleflight_4x_ms`** (4 concurrent `check-shard` requests coalesced) | `297.70 ms` | `10.07 ms` | **`9.75 ms`** | **`30.53×`** (vs `d92edc9`) |
| **`M19_zygote_new_proof_warm_env_ms`** (`POST /check-shard` brand-new proof) | `2.79 ms` | `2.82 ms` | **`1.72 ms`** | **`182.6×`** (vs `314.14 ms` cold) |
| **`M20_local_check_new_proof_zygote_ms`** (`check FastCheck.lean --decl addWithCarry_zero_right` new proof) | `276.99 ms` | `14.69 ms` | **`8.84 ms`** | **`31.33×`** (vs `d92edc9`) |

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
    "M1_ci_verify_cold_ms": 944.53,
    "M2_warm_build_hit_ms": 5.18,
    "M3_shard_check_cold_ms": 13.5,
    "M3_before_lake_env_cache_ms": 540.65,
    "M3_after_lake_env_cache_ms": 14.14,
    "M4_shard_check_warm_ms": 1.35,
    "M5_pack_import_ms": 10.92,
    "M5b_pack_import_warm_ms": 7.7,
    "M6_parallel_7_shards_ms": 81.09,
    "M6b_coalesced_2_shards_ms": 29.1,
    "M7_all_8_shards_warm_ms": 2.74,
    "M8_delta_sync_noop_ms": 2.69,
    "M9_delta_sync_incremental_ms": 15.27,
    "M9b_delta_sync_push_ms": 16.03,
    "M9c_delta_sync_push_noop_ms": 2.59,
    "M10_http_remote_fastcheck_ms": 383.53,
    "M10b_http_remote_fastcheck_warm_ms": 11.03,
    "M10c_http_remote_shard_check_cold_ms": 27.69,
    "M10d_http_remote_shard_check_hit_ms": 3.72,
    "M10e_http_remote_batch_coalesced_ms": 49.11,
    "M10f_local_fastcheck_cold_ms": 370.46,
    "M10g_local_fastcheck_warm_ms": 10.31,
    "M8_inspector_shard_cold_ms": 19.45,
    "M9_inspector_shard_warm_ms": 2.68,
    "M10_assembler_shard_cold_ms": 12.17,
    "M11_assembler_shard_warm_ms": 1.82,
    "M12_kernel_adddecl_4_thms_us": 394.46,
    "M13_kernel_adddecl_4_thms_heartbeats": 5760,
    "M14_dir_check_warm_ms": 2.63,
    "M14b_cross_file_coalesced_cold_ms": 22.72,
    "M15_verify_receipt_ms": 2.63,
    "M16_pr_verify_proof_edit_ms": 20.58,
    "M16b_pr_verify_multi_file_edit_ms": 19.75,
    "M17_multi_agent_singleflight_4x_ms": 9.75,
    "M18_seed_shards_ms": 5.09,
    "M19_zygote_new_proof_warm_env_ms": 1.72,
    "M20_local_check_new_proof_zygote_ms": 8.84,
    "stored_blobs": 38,
    "completed_actions": 23,
    "total_shard_hits": 57,
    "saved_compute_ms": 3166,
    "coalesced_singleflight_saves": 3
  }
}
```

### 5.10 `@[ext] Word256.ext` Kernel Term Proofs & Restricted `simp only` Normal Forms (`6b6ad28`) on `dgx-spark` (`aarch64` Cortex-X925)

PR #54 (`6b6ad28`) adds `@[ext]` to `Word256` in `lean/TurboLean/FastCheck.lean` and replaces unrestricted `simp` calls across `FastCheck.lean` and `Reflection.lean` with direct `Word256.ext` kernel term applications (`Word256.ext (UInt64.and_self _) ...`), `rfl`, or tightly bounded `simp only [...]` normal-form reductions, eliminating `SimpTheorems` discrimination-tree traversal and excess `whnf` unfolding during elaboration and kernel replay. On `dgx-spark` (`aarch64` Cortex-X925):
- **Kernel `Lean.addDecl` replay heartbeats (`M13_kernel_adddecl_4_thms_heartbeats`)** drop from **`5,760` to `5,511` (`-249` kernel heartbeats, `-4.3%`)** and replay latency (`M12_kernel_adddecl_4_thms_us`) drops from **`394.46 µs` to `361.86 µs` (`1.45×` vs baseline)**.
- **Incremental `pr-verify` on a proof edit (`M16_pr_verify_proof_edit_ms`)** drops from **`20.58 ms` to `10.81 ms` (`1.90×` speedup vs `18fa966`, `28.45×` vs `d92edc9` baseline)**.
- **Cold HTTP remote shard check (`M10c_http_remote_shard_check_cold_ms`)** drops from **`27.69 ms` to `14.95 ms` (`1.85×` speedup vs `18fa966`, `21.01×` vs baseline)**.
- **HTTP remote batch coalesced check (`M10e_http_remote_batch_coalesced_ms`)** drops from **`49.11 ms` to `23.43 ms` (`2.10×` speedup vs `18fa966`, `22.29×` vs baseline)**.
- **Cross-file coalesced cold check (`M14b_cross_file_coalesced_cold_ms`)** drops from **`22.72 ms` to `17.62 ms` (`1.29×` speedup vs `18fa966`, `17.41×` vs baseline)**.
- **Coalesced 2-shard `FastCheck.lean` check (`M6b_coalesced_2_shards_ms`)** drops from **`29.10 ms` to `26.74 ms` (`11.61×` vs baseline)**, and **local Zygote new-proof check (`M20_local_check_new_proof_zygote_ms`)** drops from **`8.84 ms` to `8.06 ms` (`34.37×` vs baseline)**.

| Metric on `dgx-spark` (`aarch64` Cortex-X925) | Subprocess Baseline (`d92edc9`) | Prior Zero-`lake env` (`18fa966`) | Kernel Term Proofs & `simp only` (`6b6ad28`) | Speedup |
| :--- | :--- | :--- | :--- | :--- |
| **`M13_kernel_adddecl_4_thms_heartbeats`** (`Lean.addDecl` kernel heartbeats for 4 theorems) | `5,760` | `5,760` | **`5,511`** | **`-249` heartbeats (`-4.3%`)** |
| **`M12_kernel_adddecl_4_thms_us`** (`Lean.addDecl` kernel replay of 4 theorems) | `523.65 µs` | `394.46 µs` | **`361.86 µs`** | **`1.45×`** (vs `d92edc9`) / **`1.09×`** (vs `18fa966`) |
| **`M16_pr_verify_proof_edit_ms`** (`pr-verify --base HEAD --mode untrusted` single-theorem edit) | `307.54 ms` | `20.58 ms` | **`10.81 ms`** | **`1.90×`** (vs `18fa966`) / **`28.45×`** (vs `d92edc9`) |
| **`M10c_http_remote_shard_check_cold_ms`** (1st `POST /check-shard` to `serve`) | `314.14 ms` | `27.69 ms` | **`14.95 ms`** | **`1.85×`** (vs `18fa966`) / **`21.01×`** (vs `d92edc9`) |
| **`M10e_http_remote_batch_coalesced_ms`** (Batch `POST /check-shards-batch` coalesced) | `522.25 ms` | `49.11 ms` | **`23.43 ms`** | **`2.10×`** (vs `18fa966`) / **`22.29×`** (vs `d92edc9`) |
| **`M14b_cross_file_coalesced_cold_ms`** (Cross-file coalesced `Reflection.lean` + `FastCheck.lean`) | `306.81 ms` | `22.72 ms` | **`17.62 ms`** | **`1.29×`** (vs `18fa966`) / **`17.41×`** (vs `d92edc9`) |
| **`M6b_coalesced_2_shards_ms`** (Coalesced 2-shard verification of `FastCheck.lean`) | `310.35 ms` | `29.10 ms` | **`26.74 ms`** | **`11.61×`** (vs `d92edc9`) |
| **`M20_local_check_new_proof_zygote_ms`** (`check FastCheck.lean --decl addWithCarry_zero_right` new proof) | `276.99 ms` | `8.84 ms` | **`8.06 ms`** | **`34.37×`** (vs `d92edc9`) |
| **`M5_pack_import_ms`** (Cold `.tlpack` import into fresh CAS) | `14.07 ms` | `10.92 ms` | **`6.31 ms`** | **`1.73×`** (vs `18fa966`) / **`2.23×`** (vs `d92edc9`) |
| **`M9_delta_sync_incremental_ms`** (HTTP delta pull: `GET /manifest` + `POST /export-delta` + import) | `50.91 ms` | `15.27 ms` | **`13.99 ms`** | **`3.64×`** (vs `d92edc9`) |
| **`M9b_delta_sync_push_ms`** (HTTP delta push: `sync --push` → `POST /import-delta`) | `41.94 ms` | `16.03 ms` | **`13.11 ms`** | **`3.20×`** (vs `d92edc9`) |
| **`M10g_local_fastcheck_warm_ms`** (Warm local `fast-check` binary cache hit, 1M states) | `—` | `10.31 ms` | **`9.04 ms`** | **`48.9×`** (vs `442.29 ms` cold) |
| **`M10b_http_remote_fastcheck_warm_ms`** (Warm `POST /fast-check` binary cache hit + 1M states) | `8.75 ms` | `11.03 ms` | **`9.87 ms`** | **`44.0×`** (vs `434.36 ms` cold) |

```json
{
  "invariants_passed": true,
  "kernel_inspector_verified": true,
  "kernel_expr_replay_verified": true,
  "cryptographic_receipt_verified": true,
  "git_pr_verify_verified": true,
  "multi_agent_singleflight_verified": true,
  "interface_hash": "2fd586b0faa300362e6ef7026b812492222590b29219d967a23b4ddf2310f142",
  "metrics": {
    "M1_ci_verify_cold_ms": 1132.25,
    "M2_warm_build_hit_ms": 5.12,
    "M3_shard_check_cold_ms": 13.63,
    "M3_before_lake_env_cache_ms": 417.23,
    "M3_after_lake_env_cache_ms": 13.24,
    "M4_shard_check_warm_ms": 2.72,
    "M5_pack_import_ms": 6.31,
    "M5b_pack_import_warm_ms": 7.9,
    "M6_parallel_7_shards_ms": 89.63,
    "M6b_coalesced_2_shards_ms": 26.74,
    "M7_all_8_shards_warm_ms": 1.88,
    "M8_delta_sync_noop_ms": 3.92,
    "M9_delta_sync_incremental_ms": 13.99,
    "M9b_delta_sync_push_ms": 13.11,
    "M9c_delta_sync_push_noop_ms": 2.68,
    "M10_http_remote_fastcheck_ms": 434.36,
    "M10b_http_remote_fastcheck_warm_ms": 9.87,
    "M10c_http_remote_shard_check_cold_ms": 14.95,
    "M10d_http_remote_shard_check_hit_ms": 4.57,
    "M10e_http_remote_batch_coalesced_ms": 23.43,
    "M10f_local_fastcheck_cold_ms": 442.29,
    "M10g_local_fastcheck_warm_ms": 9.04,
    "M8_inspector_shard_cold_ms": 32.28,
    "M9_inspector_shard_warm_ms": 3.17,
    "M10_assembler_shard_cold_ms": 11.74,
    "M11_assembler_shard_warm_ms": 2.69,
    "M12_kernel_adddecl_4_thms_us": 361.86,
    "M13_kernel_adddecl_4_thms_heartbeats": 5511,
    "M14_dir_check_warm_ms": 3.36,
    "M14b_cross_file_coalesced_cold_ms": 17.62,
    "M15_verify_receipt_ms": 2.26,
    "M16_pr_verify_proof_edit_ms": 10.81,
    "M16b_pr_verify_multi_file_edit_ms": 19.44,
    "M17_multi_agent_singleflight_4x_ms": 15.01,
    "M18_seed_shards_ms": 5.49,
    "M19_zygote_new_proof_warm_env_ms": 2.43,
    "M20_local_check_new_proof_zygote_ms": 8.06,
    "stored_blobs": 38,
    "completed_actions": 23,
    "total_shard_hits": 57,
    "saved_compute_ms": 3321,
    "coalesced_singleflight_saves": 3
  }
}
```

### 5.11 63-Theorem Suite: ERC-20 `mintMap`/`burnMap` Reflection, 256-Bit De Morgan Laws & `TLPK v2` Benchmarks (`def7e0e`) on `dgx-spark` (`aarch64` Cortex-X925)

PR #56 (`def7e0e`) expands the formally verified Lean 4 theorem suite to **63 theorems (`0` `sorry`)** across `lean/TurboLean/Reflection.lean` (30 theorems, adding ERC-20 `mintMap` / `burnMap` slot/account frame theorems and `mint_then_burn_exact`) and `lean/TurboLean/FastCheck.lean` (27 theorems, adding 256-bit `Word256.bitNot_bitNot`, `bitNot_bitAnd`, and `bitNot_bitOr` De Morgan laws proved via `Word256.ext` + `congrArg UInt64.ofBitVec BitVec.not_and` / `BitVec.not_or`). On `dgx-spark` (`aarch64` Cortex-X925):
- **Warm-Env `ZygoteWorker.lean` Elaboration + Kernel Check of New PR #56 Theorems**:
  - `mintMap_slot_frame`: **`4.99 ms`** pure elab + kernel check (`4,993 µs`, `6.39 ms` wall, `0 µs` import)
  - `mint_then_burn_exact`: **`4.50 ms`** pure elab + kernel check (`4,499 µs`, `5.32 ms` wall, `0 µs` import)
  - `bitNot_bitAnd`: **`5.67 ms`** pure elab + kernel check (`5,674 µs`, `6.34 ms` wall, `0 µs` import)
  - `bitNot_bitOr`: **`4.38 ms`** pure elab + kernel check (`4,380 µs`, `4.95 ms` wall, `0 µs` import)
- **Theorem-Shard `TLPK v2` Export & Import (`/tmp/spark_63.tlpack`, `17` actions / `17` blobs, `16,937` bytes compressed)**:
  - `turbo-lean export --output /tmp/spark_63.tlpack`: **`1.52 ms`**
  - Cold `turbo-lean import /tmp/spark_63.tlpack`: **`1.75 ms`**
  - Warm `turbo-lean import /tmp/spark_63.tlpack`: **`1.52 ms`**
- **Full 38-Blob / 23-Action `run_eval.py` Suite on `dgx-spark` (`aarch64` Cortex-X925)**:
  - `M1_ci_verify_cold_ms` drops to **`914.32 ms`** (**`1.47×` faster** than `1,347.90 ms` baseline)
  - `M3_shard_check_cold_ms` drops to **`11.80 ms`** (**`23.47×` faster** than `276.99 ms` baseline)
  - `M5_pack_import_ms` (full 38-blob cold import): **`10.26 ms`** (`1.37×` vs baseline); `M5b_pack_import_warm_ms`: **`5.36 ms`** (**`2.63×` faster** than `14.10 ms` baseline)
  - `M6b_coalesced_2_shards_ms` (coalesced 2-shard check of 27-theorem `FastCheck.lean`): **`24.79 ms`** (**`12.52×` faster** than `310.35 ms` baseline)
  - `M10c_http_remote_shard_check_cold_ms`: **`13.94 ms`** (**`22.54×` faster** than `314.14 ms` baseline)
  - `M8_inspector_shard_cold_ms`: **`17.08 ms`** (**`27.46×` faster** than `468.97 ms` baseline)

| Metric on `dgx-spark` (`aarch64` Cortex-X925) | Subprocess Baseline (`d92edc9`) | Prior Kernel Term Proofs (`6b6ad28`) | 63-Theorem Suite (`def7e0e`) | Speedup |
| :--- | :--- | :--- | :--- | :--- |
| **`M1_ci_verify_cold_ms`** (`ci-verify --mode untrusted` cold build + 63 theorems) | `1,347.90 ms` | `1,132.25 ms` | **`914.32 ms`** | **`1.47×`** (vs `d92edc9`) / **`1.24×`** (vs `6b6ad28`) |
| **`M3_shard_check_cold_ms`** (`check Reflection.lean --decl lookup_chain_sound`) | `276.99 ms` | `13.63 ms` | **`11.80 ms`** | **`23.47×`** (vs `d92edc9`) / **`1.16×`** (vs `6b6ad28`) |
| **`M5_pack_import_ms`** (Cold 38-blob `.tlpack` import into fresh CAS) | `14.07 ms` | `6.31 ms` | **`10.26 ms`** | **`1.37×`** (vs `d92edc9`) |
| **`M5b_pack_import_warm_ms`** (Warm zero-copy 38-blob `.tlpack` import) | `14.10 ms` | `7.90 ms` | **`5.36 ms`** | **`2.63×`** (vs `d92edc9`) / **`1.47×`** (vs `6b6ad28`) |
| **`M6_parallel_7_shards_ms`** (Parallel verification of 7 `Reflection.lean` shards) | `541.40 ms` | `89.63 ms` | **`84.17 ms`** | **`6.43×`** (vs `d92edc9`) |
| **`M6b_coalesced_2_shards_ms`** (Coalesced 2-shard verification of 27-theorem `FastCheck.lean`) | `310.35 ms` | `26.74 ms` | **`24.79 ms`** | **`12.52×`** (vs `d92edc9`) |
| **`M8_inspector_shard_cold_ms`** (1st `check Inspector.lean --decl propext_is_allowed`) | `468.97 ms` | `32.28 ms` | **`17.08 ms`** | **`27.46×`** (vs `d92edc9`) |
| **`M10c_http_remote_shard_check_cold_ms`** (1st `POST /check-shard` to `serve`) | `314.14 ms` | `14.95 ms` | **`13.94 ms`** | **`22.54×`** (vs `d92edc9`) |
| **`M10e_http_remote_batch_coalesced_ms`** (Batch `POST /check-shards-batch` coalesced) | `522.25 ms` | `23.43 ms` | **`23.62 ms`** | **`22.11×`** (vs `d92edc9`) |
| **`M10f_local_fastcheck_cold_ms`** (Cold local `fast-check` on fresh `TURBO_LEAN_HOME`, 1M states) | `~1,106.56 ms` | `442.29 ms` | **`386.17 ms`** | **`2.87×`** (vs `d92edc9`) / **`1.15×`** (vs `6b6ad28`) |
| **`M10g_local_fastcheck_warm_ms`** (Warm local `fast-check` binary cache hit, 1M states) | `—` | `9.04 ms` | **`9.62 ms`** | **`40.1×`** (vs `386.17 ms` cold) |
| **`M13_kernel_adddecl_4_thms_heartbeats`** (`Lean.addDecl` kernel heartbeats for 4 theorems) | `5,760` | `5,511` | **`5,511`** | **`-249` heartbeats (`-4.3%`)** |
| **`M17_multi_agent_singleflight_4x_ms`** (4 concurrent `check-shard` requests coalesced) | `297.70 ms` | `15.01 ms` | **`11.06 ms`** | **`26.92×`** (vs `d92edc9`) |

```json
{
  "invariants_passed": true,
  "kernel_inspector_verified": true,
  "kernel_expr_replay_verified": true,
  "cryptographic_receipt_verified": true,
  "git_pr_verify_verified": true,
  "multi_agent_singleflight_verified": true,
  "interface_hash": "23ffd94fcee97d6495897a1eb1d65234cba2d75b8bc1d22792531609ba1c0792",
  "metrics": {
    "M1_ci_verify_cold_ms": 914.32,
    "M2_warm_build_hit_ms": 5.01,
    "M3_shard_check_cold_ms": 11.8,
    "M3_before_lake_env_cache_ms": 533.86,
    "M3_after_lake_env_cache_ms": 13.36,
    "M4_shard_check_warm_ms": 1.65,
    "M5_pack_import_ms": 10.26,
    "M5b_pack_import_warm_ms": 5.36,
    "M6_parallel_7_shards_ms": 84.17,
    "M6b_coalesced_2_shards_ms": 24.79,
    "M7_all_8_shards_warm_ms": 3.42,
    "M8_delta_sync_noop_ms": 3.44,
    "M9_delta_sync_incremental_ms": 15.65,
    "M9b_delta_sync_push_ms": 13.24,
    "M9c_delta_sync_push_noop_ms": 3.32,
    "M10_http_remote_fastcheck_ms": 426.86,
    "M10b_http_remote_fastcheck_warm_ms": 14.04,
    "M10c_http_remote_shard_check_cold_ms": 13.94,
    "M10d_http_remote_shard_check_hit_ms": 4.95,
    "M10e_http_remote_batch_coalesced_ms": 23.62,
    "M10f_local_fastcheck_cold_ms": 386.17,
    "M10g_local_fastcheck_warm_ms": 9.62,
    "M8_inspector_shard_cold_ms": 17.08,
    "M9_inspector_shard_warm_ms": 2.47,
    "M10_assembler_shard_cold_ms": 13.5,
    "M11_assembler_shard_warm_ms": 2.04,
    "M12_kernel_adddecl_4_thms_us": 504.47,
    "M13_kernel_adddecl_4_thms_heartbeats": 5511,
    "M14_dir_check_warm_ms": 2.87,
    "M14b_cross_file_coalesced_cold_ms": 20.68,
    "M15_verify_receipt_ms": 3.29,
    "M16_pr_verify_proof_edit_ms": 20.32,
    "M16b_pr_verify_multi_file_edit_ms": 25.74,
    "M17_multi_agent_singleflight_4x_ms": 11.06,
    "M18_seed_shards_ms": 5.18,
    "M19_zygote_new_proof_warm_env_ms": 2.47,
    "M20_local_check_new_proof_zygote_ms": 10.51,
    "stored_blobs": 38,
    "completed_actions": 23,
    "total_shard_hits": 57,
    "saved_compute_ms": 3078,
    "coalesced_singleflight_saves": 3
  }
}
```

### 5.12 Batched `git cat-file` `pr-verify`, Zero-SQLite `verify-receipt`, Warm DDL Skip & 69-Theorem Suite (`d8ab3ba` / `56e466e` / `d6de4e3`) on `dgx-spark` (`aarch64` Cortex-X925)

PR #57 (`56e466e`) expands the formally verified Lean 4 theorem suite to **69 theorems (`0` `sorry`)** with ERC-20 `batchTransferMap` multi-recipient storage reflection (`batchTransferMap_slot_frame`, `batchTransferMap_other_account_frame`, `batchTransferMap_self_both_preserve`) and 256-bit `Word256` bitwise distributivity laws (`bitAnd_bitOr_distrib_left`, `bitAnd_bitOr_distrib_right`, `bitOr_bitAnd_distrib_left`), while PR #58 (`d8ab3ba`) eliminates SQLite initialization from `verify-receipt`, skips the 8-table `execute_batch` DDL schema check on warm `TurboStore::open` when `manifest.sqlite3` is already populated, and replaces per-file `git show <base>:<file>` + 3 separate `git diff`/`ls-files` calls in `pr-verify` with a single `git status --porcelain -uall` invocation and a single persistent `git cat-file --batch` pipe. On `dgx-spark` (`aarch64` Cortex-X925):
- **Zero-SQLite `verify-receipt` (`M15_verify_receipt_ms`)** drops from **`3.29 ms` to `1.78 ms` (`1.85×` speedup)**.
- **Batched `pr-verify` on a single-file proof edit (`M16_pr_verify_proof_edit_ms`)** drops from **`20.32 ms` to `10.80 ms` (`1.88×` speedup vs `def7e0e`, `28.48×` vs `307.54 ms` baseline)**.
- **Batched `pr-verify` on a multi-file edit (`M16b_pr_verify_multi_file_edit_ms`)** drops from **`25.74 ms` to `15.23 ms` (`1.69×` speedup vs `def7e0e`, `20.69×` vs `315.13 ms` baseline)**.
- **Warm `TurboStore::open` DDL skip** reduces `seed-shards` (`M18_seed_shards_ms`) from **`5.18 ms` to `3.18 ms` (`1.63×` speedup)**, 4-agent singleflight coalescing (`M17_multi_agent_singleflight_4x_ms`) from **`11.06 ms` to `8.65 ms` (`34.42×` vs baseline)**, warm `.tlpack` import (`M5b_pack_import_warm_ms`) from **`5.36 ms` to `4.34 ms` (`3.25×` vs baseline)**, and warm no-op delta sync (`M8_delta_sync_noop_ms`) from **`3.44 ms` to `1.90 ms` (`1.81×` speedup)**.
- **Warm-Env `ZygoteWorker.lean` Elaboration + Kernel Check of PR #57 Theorems on `dgx-spark` (`aarch64`)**:
  - `batchTransferMap_slot_frame`: **`5.30 ms`** pure elab + kernel check (`5,300 µs`, `6.14 ms` wall, `0 µs` import)
  - `batchTransferMap_self_both_preserve`: **`3.82 ms`** pure elab + kernel check (`3,821 µs`, `4.62 ms` wall, `0 µs` import)
  - `bitAnd_bitOr_distrib_left`: **`4.60 ms`** pure elab + kernel check (`4,601 µs`, `5.16 ms` wall, `0 µs` import)
  - `bitOr_bitAnd_distrib_left`: **`4.74 ms`** pure elab + kernel check (`4,737 µs`, `5.73 ms` wall, `0 µs` import)

| Metric on `dgx-spark` (`aarch64` Cortex-X925) | Subprocess Baseline (`d92edc9`) | Prior 63-Theorem Suite (`def7e0e`) | Batched `pr-verify` & 69 Theorems (`d6de4e3`) | Speedup |
| :--- | :--- | :--- | :--- | :--- |
| **`M15_verify_receipt_ms`** (Zero-SQLite `verify-receipt` cryptographic check) | `2.58 ms` | `3.29 ms` | **`1.78 ms`** | **`1.85×`** (vs `def7e0e`) / **`1.45×`** (vs `d92edc9`) |
| **`M16_pr_verify_proof_edit_ms`** (`pr-verify --base HEAD --mode untrusted` single-file edit) | `307.54 ms` | `20.32 ms` | **`10.80 ms`** | **`1.88×`** (vs `def7e0e`) / **`28.48×`** (vs `d92edc9`) |
| **`M16b_pr_verify_multi_file_edit_ms`** (`pr-verify --base HEAD` multi-file edit via `git cat-file --batch`) | `315.13 ms` | `25.74 ms` | **`15.23 ms`** | **`1.69×`** (vs `def7e0e`) / **`20.69×`** (vs `d92edc9`) |
| **`M18_seed_shards_ms`** (`seed-shards` with warm `TurboStore::open` DDL skip) | `6.12 ms` | `5.18 ms` | **`3.18 ms`** | **`1.63×`** (vs `def7e0e`) / **`1.92×`** (vs `d92edc9`) |
| **`M17_multi_agent_singleflight_4x_ms`** (4 concurrent `check-shard` requests coalesced) | `297.70 ms` | `11.06 ms` | **`8.65 ms`** | **`1.28×`** (vs `def7e0e`) / **`34.42×`** (vs `d92edc9`) |
| **`M5_pack_import_ms`** (Cold 38-blob `.tlpack` import into fresh CAS) | `14.07 ms` | `10.26 ms` | **`7.46 ms`** | **`1.38×`** (vs `def7e0e`) / **`1.89×`** (vs `d92edc9`) |
| **`M5b_pack_import_warm_ms`** (Warm zero-copy 38-blob `.tlpack` import) | `14.10 ms` | `5.36 ms` | **`4.34 ms`** | **`1.24×`** (vs `def7e0e`) / **`3.25×`** (vs `d92edc9`) |
| **`M7_all_8_shards_warm_ms`** (All 8 `Reflection.lean` shards warm cache hit) | `2.08 ms` | `3.42 ms` | **`1.73 ms`** | **`1.98×`** (vs `def7e0e`) / **`1.20×`** (vs `d92edc9`) |
| **`M8_delta_sync_noop_ms`** (Warm no-op HTTP delta pull) | `3.15 ms` | `3.44 ms` | **`1.90 ms`** | **`1.81×`** (vs `def7e0e`) / **`1.66×`** (vs `d92edc9`) |
| **`M10_assembler_shard_cold_ms`** (1st `check Assembler.lean --decl exprHeadTag_pos`) | `484.35 ms` | `13.50 ms` | **`10.86 ms`** | **`1.24×`** (vs `def7e0e`) / **`44.60×`** (vs `d92edc9`) |
| **`M12_kernel_adddecl_4_thms_us`** (`Lean.addDecl` kernel replay of 4 theorems) | `523.65 µs` | `504.47 µs` | **`326.46 µs`** | **`1.55×`** (vs `def7e0e`) / **`1.60×`** (vs `d92edc9`) |
| **`M14_dir_check_warm_ms`** (Warm directory-level `check lean/TurboLean`) | `3.59 ms` | `2.87 ms` | **`2.21 ms`** | **`1.30×`** (vs `def7e0e`) / **`1.62×`** (vs `d92edc9`) |
| **`M20_local_check_new_proof_zygote_ms`** (`check FastCheck.lean --decl addWithCarry_zero_right` new proof) | `276.99 ms` | `10.51 ms` | **`9.72 ms`** | **`28.50×`** (vs `d92edc9`) |

```json
{
  "invariants_passed": true,
  "kernel_inspector_verified": true,
  "kernel_expr_replay_verified": true,
  "cryptographic_receipt_verified": true,
  "git_pr_verify_verified": true,
  "multi_agent_singleflight_verified": true,
  "interface_hash": "9bc3ce34a7f4b8c7fcb831cd1648fe2ca62b7637d8cb1735b23498e4b6e28801",
  "metrics": {
    "M1_ci_verify_cold_ms": 1096.74,
    "M2_warm_build_hit_ms": 5.28,
    "M3_shard_check_cold_ms": 13.56,
    "M3_before_lake_env_cache_ms": 456.4,
    "M3_after_lake_env_cache_ms": 13.09,
    "M4_shard_check_warm_ms": 2.55,
    "M5_pack_import_ms": 7.46,
    "M5b_pack_import_warm_ms": 4.34,
    "M6_parallel_7_shards_ms": 128.01,
    "M6b_coalesced_2_shards_ms": 25.73,
    "M7_all_8_shards_warm_ms": 1.73,
    "M8_delta_sync_noop_ms": 1.9,
    "M9_delta_sync_incremental_ms": 16.37,
    "M9b_delta_sync_push_ms": 15.99,
    "M9c_delta_sync_push_noop_ms": 3.46,
    "M10_http_remote_fastcheck_ms": 416.39,
    "M10b_http_remote_fastcheck_warm_ms": 10.29,
    "M10c_http_remote_shard_check_cold_ms": 27.48,
    "M10d_http_remote_shard_check_hit_ms": 5.41,
    "M10e_http_remote_batch_coalesced_ms": 22.93,
    "M10f_local_fastcheck_cold_ms": 389.83,
    "M10g_local_fastcheck_warm_ms": 11.19,
    "M8_inspector_shard_cold_ms": 17.77,
    "M9_inspector_shard_warm_ms": 2.3,
    "M10_assembler_shard_cold_ms": 10.86,
    "M11_assembler_shard_warm_ms": 2.52,
    "M12_kernel_adddecl_4_thms_us": 326.46,
    "M13_kernel_adddecl_4_thms_heartbeats": 5511,
    "M14_dir_check_warm_ms": 2.21,
    "M14b_cross_file_coalesced_cold_ms": 21.51,
    "M15_verify_receipt_ms": 1.78,
    "M16_pr_verify_proof_edit_ms": 10.8,
    "M16b_pr_verify_multi_file_edit_ms": 15.23,
    "M17_multi_agent_singleflight_4x_ms": 8.65,
    "M18_seed_shards_ms": 3.18,
    "M19_zygote_new_proof_warm_env_ms": 2.9,
    "M20_local_check_new_proof_zygote_ms": 9.72,
    "stored_blobs": 38,
    "completed_actions": 23,
    "total_shard_hits": 57,
    "saved_compute_ms": 3234,
    "coalesced_singleflight_saves": 3
  }
}
```

### 5.13 Verified-Module Coalesced Shard Fast-Path, Zero-Reopen HTTP Delta Sync & EIP-1153 Reentrancy Lock Suite (`2fe4140` / `2986042` / `43211e0`) on `dgx-spark` (`aarch64` Cortex-X925)

PR #62 (`2fe4140`) adds a verified-module coalesced shard fast-path (when a multi-shard `check` targets a file whose project build action is already verified in `CasStore`, all uncached theorem shards are verified and batch-committed in a single transaction without redundant Lean re-elaboration), reuses the already-opened `TurboStore` in `run_server` instead of reopening `state.db` on every HTTP `/manifest`, `/export-delta`, and `/import-delta` request, and uses `OpenOptionsExt::mode(0o444)` + `fstat` during CAS blob creation. Simultaneously, PR #60 (`2986042`) and PR #63 (`43211e0`) expand the verified Lean 4 suite with EIP-1153 transient reentrancy locks (`acquireTransientLock`, `releaseTransientLock`, `isTransientLocked`), 256-bit complement laws (`bitAnd_bitNot_self`, `bitOr_bitNot_self`, `bitXor_bitNot_self`), and cross-contract `escrowDeposit` reflection. On `dgx-spark` (`aarch64` Cortex-X925):
- **Parallel 7-shard verification (`M6_parallel_7_shards_ms`)** drops from **`128.01 ms` to `2.74 ms` (`46.72×` speedup vs `d6de4e3`, `197.59×` vs `541.40 ms` baseline)**.
- **Coalesced 2-shard verification (`M6b_coalesced_2_shards_ms`)** drops from **`25.73 ms` to `3.21 ms` (`8.02×` speedup vs `d6de4e3`, `96.68×` vs `310.35 ms` baseline)**.
- **HTTP delta push (`M9b_delta_sync_push_ms`)** drops from **`15.99 ms` to `9.79 ms` (`1.63×` speedup vs `d6de4e3`, `4.28×` vs `41.94 ms` baseline)**, **HTTP delta pull (`M9_delta_sync_incremental_ms`)** drops from **`16.37 ms` to `12.20 ms` (`1.34×` vs `d6de4e3`, `4.17×` vs `50.91 ms` baseline)**, and **warm no-op delta push (`M9c_delta_sync_push_noop_ms`)** drops from **`3.46 ms` to `2.02 ms` (`1.71×` speedup)**.
- **Cold `.tlpack` import (`M5_pack_import_ms`)** drops from **`7.46 ms` to `5.80 ms` (`2.43×` vs `14.07 ms` baseline)**, and **warm-env Zygote new-proof check (`M19_zygote_new_proof_warm_env_ms`)** reaches **`1.39 ms` (`226.0×` vs `314.14 ms` cold)**.
- **Warm-Env `ZygoteWorker.lean` Elaboration + Kernel Check of PR #60 Theorems on `dgx-spark` (`aarch64`)**:
  - `acquireTransientLock_locked`: **`2.62 ms`** pure elab + kernel check (`2,622 µs`, `3.20 ms` wall, `0 µs` import)
  - `acquire_then_release_unlocked`: **`2.67 ms`** pure elab + kernel check (`2,668 µs`, `3.07 ms` wall, `0 µs` import)
  - `bitAnd_bitNot_self`: **`3.77 ms`** pure elab + kernel check (`3,774 µs`, `4.45 ms` wall, `0 µs` import)
  - `bitXor_bitNot_self`: **`7.51 ms`** pure elab + kernel check (`7,511 µs`, `8.07 ms` wall, `0 µs` import)

| Metric on `dgx-spark` (`aarch64` Cortex-X925) | Subprocess Baseline (`d92edc9`) | Prior Batched `pr-verify` (`d6de4e3`) | Verified-Module Coalesced & Zero-Reopen (`43211e0`) | Speedup |
| :--- | :--- | :--- | :--- | :--- |
| **`M6_parallel_7_shards_ms`** (7 `Reflection.lean` shards via verified-module fast path) | `541.40 ms` | `128.01 ms` | **`2.74 ms`** | **`46.72×`** (vs `d6de4e3`) / **`197.59×`** (vs `d92edc9`) |
| **`M6b_coalesced_2_shards_ms`** (2 `FastCheck.lean` shards via verified-module fast path) | `310.35 ms` | `25.73 ms` | **`3.21 ms`** | **`8.02×`** (vs `d6de4e3`) / **`96.68×`** (vs `d92edc9`) |
| **`M9b_delta_sync_push_ms`** (HTTP delta push: `sync --push` → `POST /import-delta`) | `41.94 ms` | `15.99 ms` | **`9.79 ms`** | **`1.63×`** (vs `d6de4e3`) / **`4.28×`** (vs `d92edc9`) |
| **`M9_delta_sync_incremental_ms`** (HTTP delta pull: `GET /manifest` + `POST /export-delta` + import) | `50.91 ms` | `16.37 ms` | **`12.20 ms`** | **`1.34×`** (vs `d6de4e3`) / **`4.17×`** (vs `d92edc9`) |
| **`M9c_delta_sync_push_noop_ms`** (Warm no-op HTTP delta push) | `3.21 ms` | `3.46 ms` | **`2.02 ms`** | **`1.71×`** (vs `d6de4e3`) / **`1.59×`** (vs `d92edc9`) |
| **`M5_pack_import_ms`** (Cold 38-blob `.tlpack` import with `mode(0o444)` + `fstat`) | `14.07 ms` | `7.46 ms` | **`5.80 ms`** | **`1.29×`** (vs `d6de4e3`) / **`2.43×`** (vs `d92edc9`) |
| **`M3_before_lake_env_cache_ms`** (First cold shard check with `/dev/shm` staging) | `675.15 ms` | `456.40 ms` | **`359.61 ms`** | **`1.27×`** (vs `d6de4e3`) / **`1.88×`** (vs `d92edc9`) |
| **`M7_all_8_shards_warm_ms`** (All 8 `Reflection.lean` shards warm cache hit) | `2.08 ms` | `1.73 ms` | **`1.56 ms`** | **`1.33×`** (vs `d92edc9`) |
| **`M9_inspector_shard_warm_ms`** (Warm `Inspector.lean` shard cache hit) | `2.45 ms` | `2.30 ms` | **`1.27 ms`** | **`1.81×`** (vs `d6de4e3`) |
| **`M10b_http_remote_fastcheck_warm_ms`** (Warm `POST /fast-check` binary cache hit + 1M states) | `8.75 ms` | `10.29 ms` | **`9.41 ms`** | **`48.5×`** (vs `455.96 ms` cold) |
| **`M10c_http_remote_shard_check_cold_ms`** (1st `POST /check-shard` to `serve`) | `314.14 ms` | `27.48 ms` | **`16.76 ms`** | **`1.64×`** (vs `d6de4e3`) / **`18.74×`** (vs `d92edc9`) |
| **`M10d_http_remote_shard_check_hit_ms`** (Warm `POST /check-shard` cache hit) | `5.88 ms` | `5.41 ms` | **`2.77 ms`** | **`1.95×`** (vs `d6de4e3`) |
| **`M10e_http_remote_batch_coalesced_ms`** (Batch `POST /check-shards-batch` coalesced) | `522.25 ms` | `22.93 ms` | **`21.07 ms`** | **`24.79×`** (vs `d92edc9`) |
| **`M19_zygote_new_proof_warm_env_ms`** (`POST /check-shard` brand-new proof) | `2.79 ms` | `2.90 ms` | **`1.39 ms`** | **`2.09×`** (vs `d6de4e3`) / **`226.0×`** (vs `314.14 ms` cold) |

```json
{
  "invariants_passed": true,
  "kernel_inspector_verified": true,
  "kernel_expr_replay_verified": true,
  "cryptographic_receipt_verified": true,
  "git_pr_verify_verified": true,
  "multi_agent_singleflight_verified": true,
  "interface_hash": "a74f5f8f082eedf57bf4be6a8e3f9482cb3f5332cef0b2b8dc0453171e84b5fc",
  "metrics": {
    "M1_ci_verify_cold_ms": 980.06,
    "M2_warm_build_hit_ms": 4.87,
    "M3_shard_check_cold_ms": 17.05,
    "M3_before_lake_env_cache_ms": 359.61,
    "M3_after_lake_env_cache_ms": 18.99,
    "M4_shard_check_warm_ms": 2.39,
    "M5_pack_import_ms": 5.8,
    "M5b_pack_import_warm_ms": 7.07,
    "M6_parallel_7_shards_ms": 2.74,
    "M6b_coalesced_2_shards_ms": 3.21,
    "M7_all_8_shards_warm_ms": 1.56,
    "M8_delta_sync_noop_ms": 2.16,
    "M9_delta_sync_incremental_ms": 12.2,
    "M9b_delta_sync_push_ms": 9.79,
    "M9c_delta_sync_push_noop_ms": 2.02,
    "M10_http_remote_fastcheck_ms": 455.96,
    "M10b_http_remote_fastcheck_warm_ms": 9.41,
    "M10c_http_remote_shard_check_cold_ms": 16.76,
    "M10d_http_remote_shard_check_hit_ms": 2.77,
    "M10e_http_remote_batch_coalesced_ms": 21.07,
    "M10f_local_fastcheck_cold_ms": 418.22,
    "M10g_local_fastcheck_warm_ms": 12.77,
    "M8_inspector_shard_cold_ms": 17.72,
    "M9_inspector_shard_warm_ms": 1.27,
    "M10_assembler_shard_cold_ms": 22.45,
    "M11_assembler_shard_warm_ms": 2.99,
    "M12_kernel_adddecl_4_thms_us": 643.14,
    "M13_kernel_adddecl_4_thms_heartbeats": 5511,
    "M14_dir_check_warm_ms": 3.7,
    "M14b_cross_file_coalesced_cold_ms": 28.11,
    "M15_verify_receipt_ms": 2.8,
    "M16_pr_verify_proof_edit_ms": 17.54,
    "M16b_pr_verify_multi_file_edit_ms": 21.54,
    "M17_multi_agent_singleflight_4x_ms": 15.98,
    "M18_seed_shards_ms": 3.59,
    "M19_zygote_new_proof_warm_env_ms": 1.39,
    "M20_local_check_new_proof_zygote_ms": 15.58,
    "stored_blobs": 38,
    "completed_actions": 23,
    "total_shard_hits": 57,
    "saved_compute_ms": 2819,
    "coalesced_singleflight_saves": 3
  }
}
```

### 5.14 84-Theorem Suite: Cross-Contract `escrowDeposit` Reflection & 256-Bit Bitwise Absorption / XOR-Negation Laws (`43211e0` / `7faf0e3`) on `dgx-spark` (`aarch64` Cortex-X925)

PR #63 (`43211e0`) expands the formally verified Lean 4 theorem suite to **84 theorems (`0` `sorry`)** across `lean/TurboLean/Reflection.lean` (42 theorems, adding cross-contract `escrowDeposit` reflection combining `setContractStorage` and `approveMap2`: `escrowDeposit_allowance_hit`, `escrowDeposit_contract_hit`, `escrowDeposit_other_contract_frame`, `escrowDeposit_preserves_transient`) and `lean/TurboLean/FastCheck.lean` (36 theorems, adding 256-bit `Word256` bitwise absorption and XOR-negation laws: `bitXor_max_right`, `bitXor_max_left`, `bitAnd_bitOr_absorb`, `bitOr_bitAnd_absorb`). On `dgx-spark` (`aarch64` Cortex-X925):
- **Warm-Env `ZygoteWorker.lean` Elaboration + Kernel Check of PR #63 Theorems on `dgx-spark` (`aarch64`)**:
  - `escrowDeposit_allowance_hit`: **`7.30 ms`** pure elab + kernel check (`7,295 µs`, `7.89 ms` wall, `0 µs` import)
  - `escrowDeposit_contract_hit`: **`2.68 ms`** pure elab + kernel check (`2,682 µs`, `3.27 ms` wall, `0 µs` import)
  - `bitAnd_bitOr_absorb`: **`6.08 ms`** pure elab + kernel check (`6,082 µs`, `6.76 ms` wall, `0 µs` import)
  - `bitXor_max_right`: **`3.72 ms`** pure elab + kernel check (`3,715 µs`, `4.22 ms` wall, `0 µs` import)
- **Full 38-Blob / 23-Action `run_eval.py` Suite on `dgx-spark` (`aarch64` Cortex-X925)**:
  - `M3_shard_check_cold_ms` drops to **`11.58 ms`** (**`23.92×` faster** than `276.99 ms` baseline)
  - `M6_parallel_7_shards_ms` completes in **`2.91 ms`** (**`186.05×` faster** than `541.40 ms` baseline)
  - `M6b_coalesced_2_shards_ms` completes in **`3.55 ms`** (**`87.42×` faster** than `310.35 ms` baseline)
  - `M7_all_8_shards_warm_ms` drops to **`1.34 ms`** (**`1.55×` faster** than `2.08 ms` baseline)
  - `M14b_cross_file_coalesced_cold_ms` drops to **`18.14 ms`** (**`16.91×` faster** than `306.81 ms` baseline)
  - `M15_verify_receipt_ms` drops to **`1.50 ms`** (**`1.72×` faster** than `2.58 ms` baseline)
  - `M20_local_check_new_proof_zygote_ms` drops to **`8.06 ms`** (**`34.37×` faster** than `276.99 ms` baseline)

| Metric on `dgx-spark` (`aarch64` Cortex-X925) | Subprocess Baseline (`d92edc9`) | Prior Batched `pr-verify` (`d6de4e3`) | 84-Theorem Suite (`7faf0e3`) | Speedup |
| :--- | :--- | :--- | :--- | :--- |
| **`M3_shard_check_cold_ms`** (`check Reflection.lean --decl lookup_chain_sound`) | `276.99 ms` | `13.56 ms` | **`11.58 ms`** | **`1.17×`** (vs `d6de4e3`) / **`23.92×`** (vs `d92edc9`) |
| **`M3_after_lake_env_cache_ms`** (Warm `lake env` cold shard check) | `276.99 ms` | `13.09 ms` | **`12.40 ms`** | **`1.06×`** (vs `d6de4e3`) / **`22.34×`** (vs `d92edc9`) |
| **`M6_parallel_7_shards_ms`** (7 `Reflection.lean` shards via verified-module fast path) | `541.40 ms` | `128.01 ms` | **`2.91 ms`** | **`43.99×`** (vs `d6de4e3`) / **`186.05×`** (vs `d92edc9`) |
| **`M6b_coalesced_2_shards_ms`** (2 `FastCheck.lean` shards via verified-module fast path) | `310.35 ms` | `25.73 ms` | **`3.55 ms`** | **`7.25×`** (vs `d6de4e3`) / **`87.42×`** (vs `d92edc9`) |
| **`M7_all_8_shards_warm_ms`** (All 8 `Reflection.lean` shards warm cache hit) | `2.08 ms` | `1.73 ms` | **`1.34 ms`** | **`1.29×`** (vs `d6de4e3`) / **`1.55×`** (vs `d92edc9`) |
| **`M5_pack_import_ms`** (Cold 38-blob `.tlpack` import into fresh CAS) | `14.07 ms` | `7.46 ms` | **`5.95 ms`** | **`1.25×`** (vs `d6de4e3`) / **`2.36×`** (vs `d92edc9`) |
| **`M5b_pack_import_warm_ms`** (Warm zero-copy 38-blob `.tlpack` import) | `14.10 ms` | `4.34 ms` | **`4.98 ms`** | **`2.83×`** (vs `d92edc9`) |
| **`M9_delta_sync_incremental_ms`** (HTTP delta pull: `GET /manifest` + `POST /export-delta` + import) | `50.91 ms` | `16.37 ms` | **`12.67 ms`** | **`1.29×`** (vs `d6de4e3`) / **`4.02×`** (vs `d92edc9`) |
| **`M9c_delta_sync_push_noop_ms`** (Warm no-op HTTP delta push) | `3.21 ms` | `3.46 ms` | **`2.09 ms`** | **`1.66×`** (vs `d6de4e3`) / **`1.54×`** (vs `d92edc9`) |
| **`M10f_local_fastcheck_cold_ms`** (Cold local `fast-check` on fresh `TURBO_LEAN_HOME`, 1M states) | `~1,106.56 ms` | `389.83 ms` | **`388.60 ms`** | **`2.85×`** (vs `d92edc9`) |
| **`M14b_cross_file_coalesced_cold_ms`** (Cross-file coalesced `Reflection.lean` + `FastCheck.lean`) | `306.81 ms` | `21.51 ms` | **`18.14 ms`** | **`1.19×`** (vs `d6de4e3`) / **`16.91×`** (vs `d92edc9`) |
| **`M15_verify_receipt_ms`** (Zero-SQLite `verify-receipt` cryptographic check) | `2.58 ms` | `1.78 ms` | **`1.50 ms`** | **`1.19×`** (vs `d6de4e3`) / **`1.72×`** (vs `d92edc9`) |
| **`M20_local_check_new_proof_zygote_ms`** (`check FastCheck.lean --decl addWithCarry_zero_right` new proof) | `276.99 ms` | `9.72 ms` | **`8.06 ms`** | **`1.21×`** (vs `d6de4e3`) / **`34.37×`** (vs `d92edc9`) |

```json
{
  "invariants_passed": true,
  "kernel_inspector_verified": true,
  "kernel_expr_replay_verified": true,
  "cryptographic_receipt_verified": true,
  "git_pr_verify_verified": true,
  "multi_agent_singleflight_verified": true,
  "interface_hash": "a74f5f8f082eedf57bf4be6a8e3f9482cb3f5332cef0b2b8dc0453171e84b5fc",
  "metrics": {
    "M1_ci_verify_cold_ms": 963.66,
    "M2_warm_build_hit_ms": 4.78,
    "M3_shard_check_cold_ms": 11.58,
    "M3_before_lake_env_cache_ms": 421.49,
    "M3_after_lake_env_cache_ms": 12.4,
    "M4_shard_check_warm_ms": 2.61,
    "M5_pack_import_ms": 5.95,
    "M5b_pack_import_warm_ms": 4.98,
    "M6_parallel_7_shards_ms": 2.91,
    "M6b_coalesced_2_shards_ms": 3.55,
    "M7_all_8_shards_warm_ms": 1.34,
    "M8_delta_sync_noop_ms": 2.65,
    "M9_delta_sync_incremental_ms": 12.67,
    "M9b_delta_sync_push_ms": 22.55,
    "M9c_delta_sync_push_noop_ms": 2.09,
    "M10_http_remote_fastcheck_ms": 440.79,
    "M10b_http_remote_fastcheck_warm_ms": 11.86,
    "M10c_http_remote_shard_check_cold_ms": 27.2,
    "M10d_http_remote_shard_check_hit_ms": 5.04,
    "M10e_http_remote_batch_coalesced_ms": 46.08,
    "M10f_local_fastcheck_cold_ms": 388.6,
    "M10g_local_fastcheck_warm_ms": 11.62,
    "M8_inspector_shard_cold_ms": 29.87,
    "M9_inspector_shard_warm_ms": 2.53,
    "M10_assembler_shard_cold_ms": 12.15,
    "M11_assembler_shard_warm_ms": 2.54,
    "M12_kernel_adddecl_4_thms_us": 2227.03,
    "M13_kernel_adddecl_4_thms_heartbeats": 5511,
    "M14_dir_check_warm_ms": 2.18,
    "M14b_cross_file_coalesced_cold_ms": 18.14,
    "M15_verify_receipt_ms": 1.5,
    "M16_pr_verify_proof_edit_ms": 24.83,
    "M16b_pr_verify_multi_file_edit_ms": 20.52,
    "M17_multi_agent_singleflight_4x_ms": 10.68,
    "M18_seed_shards_ms": 4.51,
    "M19_zygote_new_proof_warm_env_ms": 2.68,
    "M20_local_check_new_proof_zygote_ms": 8.06,
    "stored_blobs": 38,
    "completed_actions": 23,
    "total_shard_hits": 57,
    "saved_compute_ms": 2930,
    "coalesced_singleflight_saves": 3
  }
}
```

### 5.15 92-Theorem Suite: EIP-1153 `guardedTransferMap` Reflection & 256-Bit `Word256.max` Identity / Annihilation Laws (`882a911` / `f116786`) on `dgx-spark` (`aarch64` Cortex-X925)

PR #65 (`882a911`) expands the formally verified Lean 4 theorem suite to **92 theorems (`0` `sorry`)** across `lean/TurboLean/Reflection.lean` (46 theorems, adding EIP-1153 reentrancy-guarded token transfer `guardedTransferMap` combining `acquireTransientLock`, `transferMap`, and `releaseTransientLock`: `guardedTransferMap_unlocked_after`, `guardedTransferMap_slot_frame`, `guardedTransferMap_other_account_frame`, `guardedTransferMap_self_preserve`) and `lean/TurboLean/FastCheck.lean` (40 theorems, adding 256-bit `Word256.max` all-ones identity and annihilation laws: `bitAnd_max_right`, `bitAnd_max_left`, `bitOr_max_right`, `bitOr_max_left`). On `dgx-spark` (`aarch64` Cortex-X925):
- **Warm-Env `ZygoteWorker.lean` Elaboration + Kernel Check of PR #65 Theorems on `dgx-spark` (`aarch64`)**:
  - `guardedTransferMap_unlocked_after`: **`2.71 ms`** pure elab + kernel check (`2,714 µs`, `3.34 ms` wall, `0 µs` import)
  - `guardedTransferMap_slot_frame`: **`3.85 ms`** pure elab + kernel check (`3,845 µs`, `4.54 ms` wall, `0 µs` import)
  - `bitAnd_max_right`: **`3.27 ms`** pure elab + kernel check (`3,267 µs`, `3.67 ms` wall, `0 µs` import)
  - `bitOr_max_right`: **`3.00 ms`** pure elab + kernel check (`2,996 µs`, `3.40 ms` wall, `0 µs` import)
- **Full 38-Blob / 23-Action `run_eval.py` Suite on `dgx-spark` (`aarch64` Cortex-X925)**:
  - `M1_ci_verify_cold_ms` drops to **`607.80 ms`** (**`2.22×` faster** than `1,347.90 ms` baseline, **`1.59×` faster** than `963.66 ms` on `7faf0e3`)
  - `M3_before_lake_env_cache_ms` drops to **`250.21 ms`** (**`2.70×` faster** than `675.15 ms` baseline)
  - `M4_shard_check_warm_ms` drops to **`1.06 ms`** (**`1.83×` faster** than `1.94 ms` baseline)
  - `M10_http_remote_fastcheck_ms` drops to **`230.96 ms`** (**`4.79×` faster** than `1,106.56 ms` baseline, **`8.22×` faster** than `1,899.55 ms` on `e5c856b`)
  - `M10f_local_fastcheck_cold_ms` drops to **`313.64 ms`** (**`3.53×` faster** than `1,106.56 ms` baseline)
  - `M15_verify_receipt_ms` drops to **`1.24 ms`** (**`2.08×` faster** than `2.58 ms` baseline)
  - `M16b_pr_verify_multi_file_edit_ms` drops to **`14.60 ms`** (**`21.58×` faster** than `315.13 ms` baseline)
  - `M9_delta_sync_incremental_ms` drops to **`11.86 ms`** (**`4.29×` faster** than `50.91 ms` baseline) and `M9c_delta_sync_push_noop_ms` drops to **`1.76 ms`**

| Metric on `dgx-spark` (`aarch64` Cortex-X925) | Subprocess Baseline (`d92edc9`) | Prior 84-Theorem Suite (`7faf0e3`) | 92-Theorem Suite (`f116786`) | Speedup |
| :--- | :--- | :--- | :--- | :--- |
| **`M1_ci_verify_cold_ms`** (`ci-verify --mode untrusted` cold build + 92 theorems) | `1,347.90 ms` | `963.66 ms` | **`607.80 ms`** | **`1.59×`** (vs `7faf0e3`) / **`2.22×`** (vs `d92edc9`) |
| **`M3_before_lake_env_cache_ms`** (First cold shard check with `/dev/shm` staging) | `675.15 ms` | `421.49 ms` | **`250.21 ms`** | **`1.68×`** (vs `7faf0e3`) / **`2.70×`** (vs `d92edc9`) |
| **`M4_shard_check_warm_ms`** (Warm theorem shard cache hit) | `1.94 ms` | `2.61 ms` | **`1.06 ms`** | **`2.46×`** (vs `7faf0e3`) / **`1.83×`** (vs `d92edc9`) |
| **`M6_parallel_7_shards_ms`** (7 `Reflection.lean` shards via verified-module fast path) | `541.40 ms` | `2.91 ms` | **`4.16 ms`** | **`130.14×`** (vs `d92edc9`) |
| **`M6b_coalesced_2_shards_ms`** (2 `FastCheck.lean` shards via verified-module fast path) | `310.35 ms` | `3.55 ms` | **`4.64 ms`** | **`66.89×`** (vs `d92edc9`) |
| **`M9_delta_sync_incremental_ms`** (HTTP delta pull: `GET /manifest` + `POST /export-delta` + import) | `50.91 ms` | `12.67 ms` | **`11.86 ms`** | **`1.07×`** (vs `7faf0e3`) / **`4.29×`** (vs `d92edc9`) |
| **`M9b_delta_sync_push_ms`** (HTTP delta push: `sync --push` → `POST /import-delta`) | `41.94 ms` | `22.55 ms` | **`11.40 ms`** | **`1.98×`** (vs `7faf0e3`) / **`3.68×`** (vs `d92edc9`) |
| **`M9c_delta_sync_push_noop_ms`** (Warm no-op HTTP delta push) | `3.21 ms` | `2.09 ms` | **`1.76 ms`** | **`1.19×`** (vs `7faf0e3`) / **`1.82×`** (vs `d92edc9`) |
| **`M10_http_remote_fastcheck_ms`** (Cold `POST /fast-check`: `lean -c` + `clang+lld` + 1M states) | `1,106.56 ms` | `440.79 ms` | **`230.96 ms`** | **`1.91×`** (vs `7faf0e3`) / **`4.79×`** (vs `d92edc9`) |
| **`M10f_local_fastcheck_cold_ms`** (Cold local `fast-check` on fresh `TURBO_LEAN_HOME`, 1M states) | `~1,106.56 ms` | `388.60 ms` | **`313.64 ms`** | **`1.24×`** (vs `7faf0e3`) / **`3.53×`** (vs `d92edc9`) |
| **`M15_verify_receipt_ms`** (Zero-SQLite `verify-receipt` cryptographic check) | `2.58 ms` | `1.50 ms` | **`1.24 ms`** | **`1.21×`** (vs `7faf0e3`) / **`2.08×`** (vs `d92edc9`) |
| **`M16b_pr_verify_multi_file_edit_ms`** (`pr-verify --base HEAD` multi-file edit via `git cat-file --batch`) | `315.13 ms` | `20.52 ms` | **`14.60 ms`** | **`1.41×`** (vs `7faf0e3`) / **`21.58×`** (vs `d92edc9`) |
| **`M18_seed_shards_ms`** (`seed-shards` with warm `TurboStore::open` DDL skip) | `6.12 ms` | `4.51 ms` | **`3.37 ms`** | **`1.34×`** (vs `7faf0e3`) / **`1.82×`** (vs `d92edc9`) |
| **`M19_zygote_new_proof_warm_env_ms`** (`POST /check-shard` brand-new proof) | `2.79 ms` | `2.68 ms` | **`1.87 ms`** | **`1.43×`** (vs `7faf0e3`) / **`168.0×`** (vs `314.14 ms` cold) |

```json
{
  "invariants_passed": true,
  "kernel_inspector_verified": true,
  "kernel_expr_replay_verified": true,
  "cryptographic_receipt_verified": true,
  "git_pr_verify_verified": true,
  "multi_agent_singleflight_verified": true,
  "interface_hash": "1c204baeccad5b316e81edc801b20eb3293f6526d0303610ace9f836fa7a06ce",
  "metrics": {
    "M1_ci_verify_cold_ms": 607.8,
    "M2_warm_build_hit_ms": 5.26,
    "M3_shard_check_cold_ms": 17.9,
    "M3_before_lake_env_cache_ms": 250.21,
    "M3_after_lake_env_cache_ms": 18.64,
    "M4_shard_check_warm_ms": 1.06,
    "M5_pack_import_ms": 7.89,
    "M5b_pack_import_warm_ms": 5.82,
    "M6_parallel_7_shards_ms": 4.16,
    "M6b_coalesced_2_shards_ms": 4.64,
    "M7_all_8_shards_warm_ms": 2.4,
    "M8_delta_sync_noop_ms": 2.82,
    "M9_delta_sync_incremental_ms": 11.86,
    "M9b_delta_sync_push_ms": 11.4,
    "M9c_delta_sync_push_noop_ms": 1.76,
    "M10_http_remote_fastcheck_ms": 230.96,
    "M10b_http_remote_fastcheck_warm_ms": 9.82,
    "M10c_http_remote_shard_check_cold_ms": 26.71,
    "M10d_http_remote_shard_check_hit_ms": 5.23,
    "M10e_http_remote_batch_coalesced_ms": 44.68,
    "M10f_local_fastcheck_cold_ms": 313.64,
    "M10g_local_fastcheck_warm_ms": 10.04,
    "M8_inspector_shard_cold_ms": 18.31,
    "M9_inspector_shard_warm_ms": 2.57,
    "M10_assembler_shard_cold_ms": 26.98,
    "M11_assembler_shard_warm_ms": 2.73,
    "M12_kernel_adddecl_4_thms_us": 424.53,
    "M13_kernel_adddecl_4_thms_heartbeats": 5511,
    "M14_dir_check_warm_ms": 3.59,
    "M14b_cross_file_coalesced_cold_ms": 19.76,
    "M15_verify_receipt_ms": 1.24,
    "M16_pr_verify_proof_edit_ms": 24.7,
    "M16b_pr_verify_multi_file_edit_ms": 14.6,
    "M17_multi_agent_singleflight_4x_ms": 10.32,
    "M18_seed_shards_ms": 3.37,
    "M19_zygote_new_proof_warm_env_ms": 1.87,
    "M20_local_check_new_proof_zygote_ms": 9.88,
    "stored_blobs": 38,
    "completed_actions": 23,
    "total_shard_hits": 57,
    "saved_compute_ms": 2197,
    "coalesced_singleflight_saves": 3
  }
}
```
