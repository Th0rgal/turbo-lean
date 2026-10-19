# Multi-Backend Hardware Benchmark: Apple M2 (`Metal` + 16 GB Unified RAM), NVIDIA DGX Spark (`GB10 CUDA`), Linux `x86_64` & `lfglabs-dev/verity`

## 1. Evaluated Hardware Matrix

| Node | Target Triple | CPU / SoC | Memory Architecture | GPU Accelerator | Compiler / Toolchain |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **MacBook Air M2 (`air-2`, `100.76.13.34`)** | `aarch64-apple-darwin` (`arm64`) | Apple M2 (8-core: 4P + 4E) | **16 GiB Unified Memory** (`12,124 MiB` Metal working set) | **Apple M2 GPU** (`Metal.framework`, `MTLResourceStorageModeShared`) | `rustc 1.96.0`, Apple `clang 21.0.0`, `lean4:v4.31.0` |
| **NVIDIA DGX Spark (`spark-de79`, `100.77.4.93`)** | `aarch64-unknown-linux-gnu` | NVIDIA Grace ARM64 (Cortex-X925) | **128 GiB Coherent Unified Memory** | **NVIDIA GB10 Blackwell** (`sm_121`, 48 SMs, CUDA 12.x) | `rustc`, `nvcc -O3 -arch=native`, `lean4:v4.31.0` |
| **Linux `x86_64` Node** | `x86_64-unknown-linux-gnu` | AMD EPYC `x86_64` (AVX2/AVX-512) | System DDR5 + `/dev/shm` `tmpfs` | CPU SIMD (`LLVM 18` + In-Memory `FastVal`) + Remote GPU Offload | `rustc`, `clang 18`, `lean-native-core v0.3.0`, `lean4:v4.31.0` |

---

## 2. Apple M2 Metal Compute Shader vs. NVIDIA GB10 CUDA vs. CPU Fast-Check

On the MacBook Air M2 (`thomas@100.76.13.34`), `/tmp/turbo-lean-m2/cudenote_metal.mm` is compiled with:
```bash
clang++ -O3 -std=c++17 -framework Metal -framework Foundation cudenote_metal.mm -o cudenote_metal
```
The Metal compute pipelines (`cudenote_valid_word256_kernel`, `cudenote_fast_reject_3lemma_kernel`, and `cumutate_293_kernel`) allocate all parameter, counterexample, and mutation buffers with `MTLResourceStorageModeShared`, sharing physical LPDDR5 pages directly between the M2 CPU and M2 GPU with **zero PCIe transfer overhead**.

### 2.1 Cross-Accelerator 256-Bit `Word256` Counterexample & `CuMutate` Throughput

| Workload | Apple M2 Metal GPU (`MTLResourceStorageModeShared`) | NVIDIA GB10 CUDA GPU (`dgx-spark`, 48 SMs) | Apple M2 CPU (`clang++ -O3`, 1 core) | Linux `x86_64` CPU (`leanc -O3` Perceus, 1 core) | Verification / Counterexample Outcome |
| :--- | ---: | ---: | ---: | ---: | :--- |
| **1M-State 256-Bit Valid Lemma Suite** (`De Morgan`, `BitMux`, `addWithCarry`) | **`2.8315 ms`** (`353.17 M states/s`) | **`0.7093 ms`** (`1,409.92 M states/s`) | `8.26 ms` (`121.07 M states/s`) | `5.81 ms` (`172.15 M states/s`) | `0` violations across all `1,000,000` 256-bit states |
| **10M-State 256-Bit Valid Lemma Suite** | **`34.3784 ms`** (`290.88 M states/s`) | **`7.2136 ms`** (`1,386.27 M states/s`) | `82.60 ms` (`121.07 M states/s`) | `58.09 ms` (`172.15 M states/s`) | `0` violations across all `10,000,000` 256-bit states |
| **10M-State 3-Lemma Fast-Reject Suite** (Valid + Overflow + Underflow) | **`5.3863 ms`** (**`1,856.55 M states/s`**) | **`22.5697 ms`** (`443.07 M states/s`) | — | — | `0` valid violations; **`4,998,940`** overflow CEs (first at `idx=18`); **`4,996,219`** underflow CEs (first at `idx=16`) |
| **`CuMutate` Campaign: 293 Mutants × 10,000 Txs** (`2.93M` Denote evals) | **`1.2576 ms`** (**`2,329.79 M evals/s`**) | **`2.9658 ms`** (`987.91 M evals/s`) | — | — | **`292 / 293` mutants killed (`99.7%`)**; only equivalent mutant `#292` survives |

### 2.2 Exact Apple M2 Metal Compute Benchmark Output (`cudenote_metal` on `air-2`)

```json
{
  "device_name": "Apple M2",
  "unified_memory": true,
  "storage_mode": "MTLResourceStorageModeShared (Zero PCIe Copy)",
  "recommended_max_working_set_mb": 12124,
  "valid_1m_gpu_ms": 2.8315,
  "valid_1m_wall_ms": 4.3860,
  "valid_1m_throughput_mstates_s": 353.17,
  "valid_1m_violations": 0,
  "valid_10m_gpu_ms": 34.3784,
  "valid_10m_wall_ms": 34.8900,
  "valid_10m_throughput_mstates_s": 290.88,
  "fast_reject_3lemma_10m_gpu_ms": 5.3863,
  "fast_reject_3lemma_10m_throughput_mstates_s": 1856.55,
  "fast_reject_valid_violations": 0,
  "fast_reject_overflow_ces": 4998940,
  "fast_reject_first_overflow_idx": 18,
  "fast_reject_underflow_ces": 4996219,
  "fast_reject_first_underflow_idx": 16,
  "cumutate_293x10k_gpu_ms": 1.2576,
  "cumutate_293x10k_throughput_mevals_s": 2329.79,
  "mutants_killed": 292,
  "mutants_total": 293,
  "diverging_mutant_tx_pairs": 2806000
}
```

---

## 3. Next-Gen Agent UX (`agent-step` & `audit-spec`) and Low-Memory Governor (`--max-memory-mb 512` vs `2048`)

`turbo-lean` Season 6 introduces two dedicated agent commands and a global memory budget cap (`--max-memory-mb <MB>`, exported via `TURBO_LEAN_MAX_MEMORY_MB`):
1. **`turbo-lean audit-spec <file.lean> [--decl <name>]`**: Audits candidate theorem specifications for vacuous preconditions (syntactic contradictions, pairwise hypothesis conflicts, or 0/N satisfied states in the in-memory `FastVal` evaluator) and tautological conclusions (`x = x`, `True`).
2. **`turbo-lean [--max-memory-mb <MB>] agent-step <file.lean> [--decl <name>] [--project-dir <dir>] [--low-memory]`**:
   - **Stage 1 (Spec Audit + Certified Sub-Millisecond Counterexample Filter + Missing-Hypothesis Synthesis)**: Evaluates candidate 256-bit `Word256` and `ContractState`/`StorageKey` theorems across boundary and SplitMix64 states in memory (`< 0.3 ms`), certified by `lean-native-core` (`LeanNative.Backend.certifyCounterexample_no_false_positive`). If a counterexample is found, `synthesize_missing_hypothesis_hint` immediately returns `"status": "counterexample_rejected"` with a concrete Lean hypothesis fix (`"h_no_overflow : a.val + b.val < 2^256"`, `"h_le : b.val <= a.val"`, or `"h_slot_ne : k1 != k2"`) in **`< 2 ms`** without invoking Lean tactics.
   - **Stage 2 (Memory-Governed `TheoremProofCAS` & Zygote Kernel Verification)**: Verifies the declaration or file under the configured memory budget (`low_memory_mode: true`) and returns a unified JSON receipt.

### 3.1 Multi-Backend Latency Comparison (`MacBook Air M2`, `DGX Spark`, `Linux x86_64`, and `lfglabs-dev/verity`)

| Command & Target | MacBook Air M2 (`arm64-apple-darwin`, 16 GB RAM) | Linux `x86_64` (`x86_64-unknown-linux-gnu`) | NVIDIA DGX Spark (`aarch64-unknown-linux-gnu`) | Notes / Key Telemetry |
| :--- | ---: | ---: | ---: | :--- |
| **`audit-spec lean/TurboLean/Spec.lean`** (7 core spec laws) | **`0.562 ms`** | **`0.240 ms`** | — | `total_specs_audited: 7`, `tight_specs: 7`, `vacuous_specs: 0`, `verdict: "specs_audited"` |
| **`audit-spec lean/TurboLean/FastCheck.lean --decl addWithCarry_zero_right`** | **`1.008 ms`** | **`0.232 ms`** | — | `tight: true`, `vacuous: false`, stateless zero-SQLite fast path |
| **`--max-memory-mb 512 agent-step` Stage 1 Counterexample Reject** (`buggy_add_ovf`) | **`1.770 ms`** | **`0.420 ms` – `3.036 ms`** | — | `status: "counterexample_rejected"`, `suggested_hypothesis: "h_no_overflow : a.val + b.val < 2^256"` |
| **`--max-memory-mb 512 agent-step FastCheck.lean --decl addWithCarry_zero_right --low-memory`** | **`1.600 ms`** (`2.439 ms` cold stat) | **`1.450 ms` – `5.561 ms`** | — | `status: "theorem_cache_hit"`, `stage1_fastcheck_certified: true`, `low_memory_mode: true` |
| **`--max-memory-mb 2048 agent-step Reflection.lean --decl lookup_chain_sound`** | **`0.705 ms`** (`705 µs`) | **`1.210 ms`** | — | `status: "theorem_cache_hit"`, `max_memory_mb: 2048`, `stage1_fastcheck_certified: true` |
| **`--max-memory-mb 512 seed-shards --project-dir lean`** (24 shards, 5 files) | **`31.125 ms`** cold / **`1.031 ms`** warm | **`3.830 ms`** | **`0.455 ms`** cold / **`0.286 ms`** warm | `23,278 shards/s` on M2; `59,440 shards/s` on DGX Spark |
| **`--max-memory-mb 512 check lean/TurboLean --project-dir lean`** | **`5.000 ms`** | **`1.850 ms`** | **`< 1.000 ms`** | `status: "all_shards_cached"`, `24` shard hits, `0` misses |
| **`audit-spec Verity/Proofs/Stdlib/Math.lean --decl safeAdd_isSome_iff_addNoOverflow`** | — | **`0.211 ms`** (`211 µs`) | — | `lfglabs-dev/verity` (3,040 lines, 212 shards): `tight: true`, `vacuous: false` |
| **`--max-memory-mb 2048 agent-step Verity/Proofs/Stdlib/Math.lean --decl safeAdd_isSome_iff_addNoOverflow`** | — | **`22.281 ms`** | — | **`448.8×` faster** than `9,999.4 ms` `lake env lean` on `Math.lean` |
| **`--max-memory-mb 512 agent-step Verity/Core/Uint256.lean --decl Uint256.add_comm --low-memory`** | — | **`24.488 ms`** | — | **`146.5×` faster** than `3,587.5 ms` `lake env lean` on `Core.lean` |

### 3.2 Exact JSON Outputs on MacBook Air M2 (`arm64-apple-darwin`)

#### 1. `turbo-lean --json audit-spec lean/TurboLean/Spec.lean` (`0.562 ms` on M2)
```json
{
  "elapsed_ms": 0.562,
  "file": "lean/TurboLean/Spec.lean",
  "specs": [
    {
      "assessment": "non_vacuous_and_tight",
      "decl": "isSoundDeclSummary_eq_true_iff",
      "tight": true,
      "vacuous": false
    },
    {
      "assessment": "non_vacuous_and_tight",
      "decl": "isSoundKernelExtension_rejects_unsafe_or_axiom",
      "tight": true,
      "vacuous": false
    },
    {
      "assessment": "non_vacuous_and_tight",
      "decl": "declInterfaceProj_thm_body_invariant",
      "tight": true,
      "vacuous": false
    },
    {
      "assessment": "non_vacuous_and_tight",
      "decl": "observational_quotient_sound",
      "tight": true,
      "vacuous": false
    },
    {
      "assessment": "non_vacuous_and_tight",
      "decl": "cone_frame_drop_outside",
      "tight": true,
      "vacuous": false
    },
    {
      "assessment": "non_vacuous_and_tight",
      "decl": "cone_frame_rule_locality",
      "tight": true,
      "vacuous": false
    },
    {
      "assessment": "non_vacuous_and_tight",
      "decl": "two_tier_cache_refinement",
      "tight": true,
      "vacuous": false
    }
  ],
  "status": "ok",
  "tight_specs": 7,
  "total_specs_audited": 7,
  "vacuous_spec_names": [],
  "vacuous_specs": 0,
  "verdict": "specs_audited"
}
```

#### 2. `turbo-lean --json --max-memory-mb 512 agent-step` Stage 1 Counterexample Fast-Reject (`1.77 ms` on M2)
```json
{
  "counterexample": {
    "bindings": [
      [
        "a",
        "0xffffffffffffffff_ffffffffffffffff_ffffffffffffffff_ffffffffffffffff"
      ],
      [
        "b",
        "0x0000000000000000_0000000000000000_0000000000000000_0000000000000001"
      ]
    ],
    "lhs_value": "(0x0000000000000000_0000000000000000_0000000000000000_0000000000000000, true)",
    "rhs_value": "(0x0000000000000000_0000000000000000_0000000000000000_0000000000000000, false)",
    "state_idx": 18
  },
  "decl": "buggy_add_ovf",
  "elapsed_ms": 1.77,
  "file": "/tmp/turbo-lean-m2/cex_probe.lean",
  "lean_native_certified": true,
  "lean_native_engine_version": "0.3.0",
  "low_memory_mode": true,
  "max_memory_mb": 512,
  "n_states": 1024,
  "stage": "stage1_fastcheck",
  "stage1_fastcheck_certified": true,
  "status": "counterexample_rejected",
  "suggested_hypothesis": "h_no_overflow : a.val + b.val < 2^256",
  "violations": 288
}
```

#### 3. `turbo-lean --json --max-memory-mb 512 agent-step` Stage 2 Verified (`1.60 ms` on M2)
```json
{
  "decl": "addWithCarry_zero_right",
  "elapsed_ms": 1.6,
  "file": "lean/TurboLean/FastCheck.lean",
  "interface_hash": "b8c3cdc2e790c27e23cf3e50592fc3381c0b6f136daca3b22f5ac6d6489252e4",
  "lean_native_certified": true,
  "lean_native_engine_version": "0.3.0",
  "low_memory_mode": true,
  "max_memory_mb": 512,
  "prefix_env_hash": "82a27c26e00bf083352e82846f3bde28125ae6fff6025b27122585a6ecce77aa",
  "shard_hits": 1,
  "shard_key": "e031c3213c955d95601c78aa2a952b87ff21183b6f0f6f16e8acb5ef2ec1222f",
  "shard_misses": 0,
  "stage": "stage2_kernel_verified",
  "stage1_fastcheck_certified": true,
  "status": "theorem_cache_hit",
  "tight_specs": 1,
  "total_specs_audited": 1,
  "vacuous_specs": 0,
  "verification_status": "verified",
  "verified": true
}
```
