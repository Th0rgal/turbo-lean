# Wave 3: Rust versus LeanNative native parity

Measured on main **`a95e5051ab3b4ce5611872b7bccd173c74995381`**, after D0–D6
merged. The eight **actual canonical LNIR** workloads have optimized
LeanNative/Rust time geomean **0.872236×** (1.14648× reciprocal speedup,
114.65% relative throughput); baseline emission is **2.228345×** Rust time.
All 11 measured workloads passed the pre-timing checksum gate on all 128 seeds.
This is a native-call pipeline measurement, **not** compilation latency or a
general claim that Lean is faster than Rust. The EVM division result depends
strongly on the reference algorithm; dot/SAXPY/elementwise multiply-add remain
slower than Rust. No measurements have been dropped from the final run.

## Reproduction and machine

```bash
source /var/lib/orb-node/orb-warm/env.sh # Boat toolchain setup
export TURBO_LEAN_TELEMETRY=off
(cd lean && lake build lean-native-core lean-native turbo-zygote LeanNative.Proofs.AxiomAudit)
cargo build --release --bin turbo-lean
python3 scripts/bench_rust_parity.py --trials 7 --json /tmp/bench_rust_parity.json
```

The Python runner uses only the standard library. Required external tools are
the built binaries, Lake/Lean, rustc, clang, git and lscpu. Temporary generated
sources/objects are removed automatically. JSON includes all seven samples,
median, inclusive-quartile IQR, min/max, calls/s, ratios, checksums, full lscpu,
compiler versions, source HEAD, and live D3/D4 receipts.

* Boat KVM guest: AMD EPYC **4585PX 16-Core Processor**, family 26/model 68
  (Zen 5); **8 exposed vCPUs**, one thread/core, one socket. The model string
  does not mean this guest owns all 16 physical cores.
* Linux **6.8.0-117-generic**, x86_64, glibc 2.39.
* `rustc 1.97.1 (8bab26f4f 2026-07-14)`.
* Ubuntu clang **18.1.3 (1ubuntu1)**, x86_64-pc-linux-gnu.
* Lean **4.35.0**, toolchain commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

## Methodology and coverage

`lean-native-core compile --canonical-benchmark --emit-llvm [--baseline]`
emits both production variants. Defined symbols are namespaced so both link
with the independent Rust static library into **one executable**. The C harness
uses the same `CLOCK_MONOTONIC` timer, rotates variant order by trial, executes
one full warmup then seven trials of 2,000 calls, and keeps rolling checksums.
Before any timing it compares each workload's 64-bit output digest for 128
deterministic seeds across all three variants, aborting on any mismatch.
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
| `collatz_steps` | 63.4545 (1.2520) | 121.8930 (0.7438) | 63.4490 (1.7608) | 0.9999 | 100.01% |
| `tuple_accum_sum` | 2.1440 (0.0478) | 156.2025 (1.8185) | 2.1440 (0.1500) | 1.0000 | 100.00% |
| `sarray_scale_bias` | 260.7540 (3.7328) | 806.6710 (10.8898) | 259.3860 (4.6160) | 0.9948 | 100.53% |
| `dot_product_u64` | 73.9385 (1.9310) | 157.9460 (2.0840) | 91.7720 (4.7138) | 1.2412 | 80.57% |
| `saxpy_kernel` | 260.6635 (1.7028) | 323.1055 (6.1045) | 294.3820 (2.8525) | 1.1294 | 88.55% |
| `matmul_tiled_u64` | 267.0205 (1.2298) | 360.3060 (12.6335) | 302.3875 (2.5348) | 1.1325 | 88.30% |
| `evm_erc20_transfer_u256` | 21.0090 (0.1510) | 26.2850 (0.1450) | 15.3290 (0.0830) | 0.7296 | 137.05% |
| `evm_muldiv_wad_u256` | 975.8485 (11.4115) | 306.5240 (1.6453) | 283.7775 (2.4323) | 0.2908 | 343.88% |
| **8-kernel geometric mean ratio** | **1.0000** | **2.228345** | **0.872236** | **0.872236** | **114.65%** |

The geometric mean weights every kernel equally, not by total execution time.
The EVM muldiv algorithm gap materially affects the summary; it must accompany
any citation of the geomean. Input setup and hashing can mask compute-only gaps.

## D1 / D2 / D5 feature isolation

These are emitted by a temporary Lean driver importing the actual merged
implementations, not handwritten C substitutes for LeanNative. They are
excluded from the eight-kernel geomean. Same timer, parity gate and trials.

| Feature case | Rust ns (IQR) | LN control ns (IQR) | LN transformed ns (IQR) | LN/Rust |
| --- | ---: | ---: | ---: | ---: |
| D1 local exclusivity discharge | 2.4895 (0.3683) | 2.1240 (0.3780) | 2.1690 (0.3683) | 0.8713 |
| D2 thread-local RC elision | 2.1190 (0.3808) | 2.1185 (0.3765) | 2.1190 (0.3830) | 1.0000 |
| D5 three-await micro-pipeline | 2.1340 (0.0200) | 36.3275 (1.3925) | 2.1285 (0.0103) | 0.9974 |

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
  The stackless case simplifies to seed+21 and matches Rust. Its ~17.07×
  control/transformed ratio is specific to a three-step statically known chain;
  it is not an event-loop or I/O throughput claim.
* **D6:** `PTXAst` barrier generations and optional axiomatic memory witnesses
  are merged; this CPU-only experiment neither runs PTX nor measures GPU speed.

## D3 + D4 hardware-in-the-loop calibration and Amdahl pruning

The runner also executes these real commands after the timed suite:

```bash
./lean/.lake/build/bin/lean-native-core calibrate-cost --target x86_64 --json
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
{"accepted":true,"baselineNs":2038197,"candidateNs":2000549,
 "hits":1,"sitesConsidered":1,"sitesPruned":0}
```

The retained site was `collatz_steps:0`, profile `x86_64_skylake_avx2`, target
CPU `x86-64-v3`; the host is Zen 5 but `--target x86_64` selects that preset.
Provenance: `host_cpu_wall_clock`, `compiled_llvm_native_8decl`,
`canonicalCorpusExecuted=true`, `tuningMeasured=true`.
Each operation sample ran 2,000,000 dependency-chain iterations:

| Operation | elapsed ns |
| --- | ---: |
| add | 26,554,458 |
| bitwise | 26,704,962 |
| shift | 27,145,646 |
| cmp | 30,955,837 |
| mul | 34,480,932 |
| div | 38,265,263 |
| fma | 41,963,805 |
| select | 28,821,998 |

[`CostAutotuneCLI.lean`](../lean/LeanNative/Driver/CostAutotuneCLI.lean)
actually calls `ablateSitesLeaveOneOut`, verifies compiled/evaluator parity,
and selects retained sites. Its internal compiler uses **`clang -O2`**, separate
executables and one timing per configuration, not this report's paired `-O3`
seven-trial harness. The JSON exposes the aggregate receipt, not individual
leave-one-out pairs. The accepted 1.85% aggregate time reduction is noisy;
it is not an independently replicated `-O3` Amdahl result.

Rule 7 requires nonzero hits and **ΔE2E ≥ 1%**, so algebraically valid scalar
rewrites should be pruned when LLVM `-O3` already canonicalizes both forms and
their leave-one-out measurements show no benefit. That preserves the verified
target-level equivalence while rejecting unjustified performance complexity.
**The report run pruned zero sites.** A subsequent mandatory verification rerun
passed all checksums and measured geomeans 2.274297× baseline / **0.868770×**
optimized, versus 2.228345× / 0.872236× in the table. Its D4 receipt instead
reported `accepted=false`, `baselineNs=2118333`, `candidateNs=2118333`,
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
