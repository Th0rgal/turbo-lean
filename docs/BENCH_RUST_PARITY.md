# Wave 3: Rust versus LeanNative native parity

Measured on the shared-harness refactor atop **`afdc92bf71ef9faca83fe2711871554f9e4473da`**,
after D0–D6 merged (JSON records that parent HEAD; measurements include this
commit's working-tree refactor). The eight **actual canonical LNIR** workloads have
optimized LeanNative/Rust time geomean **0.875412×** (1.14232× reciprocal speedup,
114.23% relative throughput); baseline emission is **2.184793×** Rust time.
All 11 measured workloads passed the pre-timing checksum gate on all 128 seeds.
This is a native-call pipeline measurement, **not** compilation latency or a
general claim that Lean is faster than Rust. The EVM division result depends
strongly on the reference algorithm; dot/SAXPY/elementwise multiply-add remain
slower than Rust. No measurements have been dropped from the final run.

## Reproduction and machine

```bash
source /var/lib/orb-node/orb-warm/env.sh # Boat toolchain setup
export TURBO_LEAN_TELEMETRY=off
(cd lean && lake build lean-native-core lean-native turbo-zygote LeanNative.Proofs.AxiomAudit LeanNative.Tests.CostAutotuneTests LeanNative.Tests.ProofRetentionTests)
cargo build --release --bin turbo-lean
python3 scripts/bench_rust_parity.py --trials 7 --json /tmp/bench_rust_parity.json
```

The Python runner uses only the standard library. Required external tools are
the built binaries, Lean (version reporting), rustc, clang, git and lscpu. Temporary generated
sources/objects are removed automatically. JSON includes all seven samples,
median, inclusive-quartile IQR, min/max, calls/s, ratios, checksums, full lscpu,
compiler versions, source HEAD, and live D3/D4 receipts.

* Boat KVM guest: AMD **Ryzen 9 9950X 16-Core Processor**, family 26/model 68
  (Zen 5); **8 exposed vCPUs**, one thread/core, one socket. The model string
  does not mean this guest owns all 16 physical cores.
* Linux **6.8.0-117-generic**, x86_64, glibc 2.39.
* `rustc 1.97.1 (8bab26f4f 2026-07-14)`.
* Ubuntu clang **18.1.3 (1ubuntu1)**, x86_64-pc-linux-gnu.
* Lean **4.35.0**, toolchain commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

## Methodology and coverage

`lean-native-core calibrate-cost --emit-parity-harness <dir>` emits baseline and
default-pipeline optimized LLVM modules, the feature module, names manifest and
shared C harness directly from `CostAutotuneCLI.lean`. Defined symbols are namespaced
so both link with the independent Rust static library into **one executable**.
There is no source-string extraction or temporary `lean --run` driver. Every
runner subprocess receives `TURBO_LEAN_TELEMETRY=off` and the absolute checkout
`LEAN_NATIVE_CORE_BIN`; missing binaries fail with build instructions. The C harness
uses the same `CLOCK_MONOTONIC` timer, rotates variant order by trial, executes
one full warmup then seven trials of 2,000 calls, and keeps rolling checksums.
Before any timing it compares each workload's 64-bit output digest for 128
deterministic seeds across all three variants, aborting on any mismatch.
The shared `run_canonical_kernel` also checks eight kernels on 128 small-input seeds.
Calibration uses the same small inputs for seeds 0–3, 16 scalar steps and four-element
arrays matching `mkDeclBenchState`; its `PARITY_HASH` must match
`verifyAndAccumulateCorpus mod mod 4` exactly.
Timed checksums must also match. This is bit-exact **checksum parity on this
input set**, not an exhaustive equivalence proof; hash collisions and uncovered
inputs remain outside this empirical gate.

Rust uses `#[no_mangle] pub extern "C"`, `-C opt-level=3 -C target-cpu=native
--crate-type=staticlib`; LLVM objects and harness use `clang -O3 -march=native`.
No LTO. Production LLVM function attributes (including baseline `optnone`
helpers and target-cpu annotations) are preserved: passing `-O3` does not erase
those attributes. Consequently the baseline/optimized delta is a full emitted
pipeline comparison, not an isolated D1–D5 causal attribution.

Array calls include construction of three 256-word stack buffers, the kernel,
output digest and any result free; dot product allocates its one-word output
in both implementations. Scalar loops use 128 steps. EVM calls include fresh
two-slot storage setup and pointer adapters for i256 ABI portability. Rust's
four-limb implementation uses a straightforward 512-step long division;
LeanNative's production helper has different lowering/fast paths. Timing
inputs are small positive EVM words, not adversarial full-width arithmetic.
Rust references implement the actual operations, including wrapping u64 math,
ERC20 storage updates and `ceil(a*b/wad) + clz(floor(a*b/wad))`.

The eight names requested for Wave 3 do **not** match
[`mkCanonicalBenchmarkModule8`](../lean/LeanNative/IR/Codec.lean):

| Requested name | What exists at this main revision |
| --- | --- |
| `dot_product_simd` | `dot_product_u64` (measured below) |
| `saxpy_arena` | `saxpy_kernel` (measured below; not an arena benchmark) |
| `layernorm_f64_scaled` | Not in the canonical module; not measured |
| `hash_blake3_compress_round` | Not in the canonical module; not measured |
| `polynomial_horner_u64` | Not in the canonical module; not measured |
| `matmul_tiled_u64` | Present, but body is **elementwise `a*b+c`**, not tiled matrix multiplication |
| `evm_erc20_transfer_u256` | Present and measured |
| `evm_muldiv_wad_u256` | Present and measured |

Collatz, tuple accumulation and scale/bias occupy the other three canonical
slots. Renaming these to layernorm/BLAKE3/Horner would misrepresent the corpus.
There is no stock-Lean source counterpart for this hand-constructed LNIR module;
the baseline below is LeanNative baseline emission, **not stock boxed Lean**.

## Complete canonical results

Times are **median ns/call (IQR ns)**, including the work described above.
Ratio is optimized LeanNative time / Rust time (lower is better). Relative
throughput is `100 / ratio`; absolute throughput is `1e9 / ns` calls/s and is
also emitted in JSON. This VM was not CPU-isolated or affinity-pinned;
nanosecond-scale deltas and sub-percent differences are not significant wins.

| Canonical workload | Rust | LN baseline | LN optimized | Ratio | Relative throughput |
| --- | ---: | ---: | ---: | ---: | ---: |
| `collatz_steps` | 62.6030 (1.4773) | 120.2710 (2.8420) | 62.4925 (2.0692) | 0.9982 | 100.18% |
| `tuple_accum_sum` | 2.2495 (0.0348) | 150.2425 (6.1743) | 2.2440 (0.0152) | 0.9976 | 100.25% |
| `sarray_scale_bias` | 255.5200 (5.4775) | 783.0260 (15.3567) | 255.1990 (7.0940) | 0.9987 | 100.13% |
| `dot_product_u64` | 78.0365 (3.0508) | 156.2885 (6.7978) | 92.6340 (3.3942) | 1.1871 | 84.24% |
| `saxpy_kernel` | 258.4255 (2.4823) | 315.8080 (9.3980) | 288.2360 (6.1212) | 1.1154 | 89.66% |
| `matmul_tiled_u64` | 261.0500 (3.6623) | 348.0335 (5.9638) | 297.9695 (3.1808) | 1.1414 | 87.61% |
| `evm_erc20_transfer_u256` | 20.4135 (0.1620) | 26.0090 (0.5240) | 16.0050 (1.5832) | 0.7840 | 127.54% |
| `evm_muldiv_wad_u256` | 950.4755 (2.5415) | 301.8415 (1.7885) | 278.1930 (1.6857) | 0.2927 | 341.66% |
| **8-kernel geometric mean ratio** | **1.0000** | **2.184793** | **0.875412** | **0.875412** | **114.23%** |

The geometric mean weights every kernel equally, not by total execution time.
The EVM muldiv algorithm gap materially affects the summary; it must accompany
any citation of the geomean. Input setup and hashing can mask compute-only gaps.

## D1 / D2 / D5 feature isolation

These are emitted by `CostAutotuneCLI.featureModule` using the actual merged
implementations, not handwritten C substitutes for LeanNative. They are
excluded from the eight-kernel geomean. Same timer, parity gate and trials.

| Feature case | Rust ns (IQR) | LN control ns (IQR) | LN transformed ns (IQR) | LN/Rust |
| --- | ---: | ---: | ---: | ---: |
| D1 local exclusivity discharge | 2.4445 (0.0428) | 2.4595 (0.0402) | 2.4340 (0.0250) | 0.9957 |
| D2 thread-local RC elision | 2.3740 (0.0105) | 2.3695 (0.0275) | 2.3845 (0.0752) | 1.0044 |
| D5 three-await micro-pipeline | 2.0735 (0.0148) | 33.9190 (2.4273) | 2.0745 (0.0152) | 1.0005 |

* **D1:** repeated `sarrayEnsureExclusive` versus
  `dischargeLocalExclusivity`, with an already-unique stack buffer. Both reduce
  to almost no work; no credible performance win is established. This does
  **not** isolate retained `nsw`/`nuw` or pointer `noalias` facts. Those live in
  `Frontend/ProofRetention.lean` and its typed backend specializations/tests.
* **D2:** balanced inc/dec versus `elideBorrowedAndThreadLocalRC`. The control
  uses a negative shared RC header, the local case a positive unique header.
  Optimized emission already cancels the balanced pair, so the result is
  **parity**, not evidence of an atomic-RC speedup. `UnboxedRegion.lean` provides
  header-free `repr(C)` layouts, borrowed raw loads/stores and portable SIMD;
  this harness does not measure a separate flat-struct layout or real
  `lean_mark_mt` traversal. Such claims remain unmeasured here.
* **D5:** `lowerHeapClosureAsync3` (three allocCtor/decRef pairs) versus
  `optimizeAsyncStateMachine (lowerAsyncAwaitChain ...)`, with deltas 5/7/9.
  The stackless case simplifies to seed+21 and matches Rust. Its ~16.35×
  control/transformed ratio is specific to a three-step statically known chain;
  it is not an event-loop or I/O throughput claim.
* **D6:** `PTXAst` barrier generations and optional axiomatic memory witnesses
  are merged; this CPU-only experiment neither runs PTX nor measures GPU speed.

## D3 + D4 hardware-in-the-loop calibration and Amdahl pruning

The runner also executes these real commands after the timed suite:

```bash
./lean/.lake/build/bin/lean-native-core calibrate-cost --target x86_64 --json
export LEAN_NATIVE_CORE_BIN="$PWD/lean/.lake/build/bin/lean-native-core"
./target/release/turbo-lean superopt-evolve --help
./target/release/turbo-lean superopt-evolve --generations 2 --seed 1 --input canonical --json --no-telemetry
```

The `--help` command was checked separately. D3's deterministic smoke receipt:
16 roots, 4 accepted/verified certificates, 12 rejected candidates, 0 external
candidates; module model cost **54 → 24**, certificate cost **33 → 3**.
The certificates cite `LeanNative.Proofs.certifyScalarPair_sound`. These are
**cost units, not nanoseconds**; they do not establish a 55.6% wall-clock win.
No LLM/solver was used in this smoke run.

Report-run D4 `amdahlReceipt`:

```json
{"accepted":true,"baselineNs":3338869,"candidateNs":3104929,
 "hits":1,"sitesConsidered":1,"sitesPruned":0}
```

The retained site was `collatz_steps:0`, profile `x86_64_skylake_avx2`, target
CPU `x86-64-v3`; the host is Zen 5 but `--target x86_64` selects that preset.
Provenance: `host_cpu_wall_clock`, `compiled_llvm_native_8decl`,
`canonicalCorpusExecuted=true`, `tuningMeasured=true`.
Each operation sample ran 2,000,000 dependency-chain iterations:

| Operation | elapsed ns |
| --- | ---: |
| add | 25,612,486 |
| bitwise | 25,875,902 |
| shift | 26,976,207 |
| cmp | 31,066,279 |
| mul | 34,606,760 |
| div | 38,816,536 |
| fma | 42,485,318 |
| select | 28,903,417 |

[`CostAutotuneCLI.lean`](../lean/LeanNative/Driver/CostAutotuneCLI.lean)
actually calls `ablateSitesLeaveOneOut`, verifies compiled/evaluator parity,
and selects retained sites. Both modes now share generated dispatch, input setup,
digest and timing loops (one warmup, 2,000 calls per kernel). Calibration still uses
**`clang -O2`**, separate executables and one timing per configuration; the paired
report uses `-O3` and seven trials. The JSON exposes the aggregate receipt, not
individual leave-one-out pairs. The accepted 7.01% aggregate time reduction is noisy;
it is not an independently replicated `-O3` Amdahl result.

Rule 7 requires nonzero hits and **ΔE2E ≥ 1%**, so algebraically valid scalar
rewrites should be pruned when LLVM `-O3` already canonicalizes both forms and
their leave-one-out measurements show no benefit. That preserves the verified
target-level equivalence while rejecting unjustified performance complexity.
**The report run pruned zero sites.** A subsequent mandatory verification rerun
passed all checksums and measured geomeans 2.081038× baseline / **0.845106×**
optimized, versus 2.184793× / 0.875412× in the table. It ran from `/tmp/opencode`
with a deliberately failing core first on PATH and in inherited `LEAN_NATIVE_CORE_BIN`;
the runner overrode both correctly. Its D4 receipt instead reported `accepted=false`,
`baselineNs=3044237`, `candidateNs=3044237`, `hits=0`,
`sitesConsidered=1`, `sitesPruned=1`: the lone site was pruned. Both outcomes
are disclosed rather than selecting the favorable receipt. This variation
reinforces the need for repeated per-site timing. We do not invent an `-O3` pruning receipt or
pretend the default optimized column loads the measured profile: it uses the
default production pipeline. A paired, multi-trial, per-site calibrated `-O3`
ablation remains follow-up work.

## Formal assurance summary and remaining scope

[`AxiomAudit.lean`](../lean/LeanNative/Proofs/AxiomAudit.lean) built successfully;
native self-test reports **552** unique audited theorems, **547** `LeanNative.*`
plus **5** `ConLeche`/`TurboLean.ElabAudit`, **0 sorryAx**. Inventory gate:
**124/124** LeanNative tight specs, **94/94** TurboLean tight specs, **78** C-ABI
symbols. The repository records **1,913** LeanNative theorem/lemma declarations;
that is distinct from the unique audited-name count.

The formal boundary is **Lean 4 → Target IR** under the documented supported
subsets and premises: LCNF/LNIR refinement, verified transformations and typed
LLVM/PTX/Metal/StableHLO/C-ABI models. Production text emitters and this harness
are tested, not automatically proven equivalent by the audit count. This
benchmark starts from constructed LNIR and does not exercise source frontend
proof retention. `clang`/LLVM, `rustc`, libc/allocator, OS loader/kernel and CPU
remain downstream TCB; the Rust references and measurement code are unverified.

Local verification passed: seven-trial benchmark, inventory check, native
`pr-verify`, native `self-test`, and `verify_roadmap_contract.sh` (including
scalar ASan/UBSan differential conformance and 32 fuzz cases). The latter
explicitly says **full roadmap coverage remains open**. This report therefore
delivers measured canonical parity and limited feature isolation, not closure
of the absent layernorm/hash/Horner, stock-Lean, full-width EVM, D1 flag,
D2 layout, or calibrated `-O3` per-site measurement gaps.
