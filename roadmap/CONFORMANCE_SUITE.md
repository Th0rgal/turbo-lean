# Non-FV 3-Way Differential Conformance & Fuzzing Suite (`C1`–`C4`)

> **Why Formal Verification Alone Is Not Enough**:
> Even if every `LNIR → LNIR` optimization pass has a machine-checked `0 sorryAx` proof in Lean 4, a compiler can still silently miscompile real programs if:
> 1. **The Frontend Lowering (`LCNF → LNIR` in `Bridge.lean`)** misinterprets a Lean 4 runtime convention (e.g., closure partial application papering, boxed vs. unboxed scalar tagging, or mutually recursive `letrec`).
> 2. **The Formal Semantics (`Eval.lean`)** makes a simplifying assumption that diverges from the real Lean 4 runtime (`libleanrt.a`).
> 3. **The Backend Emitter (`LLVM.lean`, `Metal.lean`, `PTX.lean`, `CoreCLI.lean`)** has a register-allocation, calling-convention, buffer-offset, or SIMD lane-mask bug below the formal IR layer.
>
> To guarantee we **never miss a bug in the specs or the codegen**, every commit and autonomous wave must pass a **Non-FV 3-Way Differential Conformance Suite**.

---

## 1. Architecture: The 3-Way Differential Oracle

Every program $P$ in the conformance corpus is executed across **three independent engines** on identical inputs $x_1, \dots, x_N$:

```
                       ┌────────────────────────────────────────────────────────┐
                       │ Engine 1: Stock Lean 4 C Backend (`lean -c` + `clang`) │
                       │ • Ground-truth reference for Lean 4 runtime semantics  │
                       └───────────────────────────┬────────────────────────────┘
                                                   │ stdout + return code + SHA-256
┌──────────────────┐   ┌───────────────────────────▼────────────────────────────┐
│ Input Program P  ├──►│ Engine 2: Formal `LNIR` Operational Evaluator          │
│ (`.lean` / LCNF) │   │ (`LeanNative.Semantics.evalDecl` + `HeapState` audit)  │
└──────────────────┘   └───────────────────────────┬────────────────────────────┘
                                                   │ stdout + return code + `liveObjects == 0`
                       ┌───────────────────────────▼────────────────────────────┐
                       │ Engine 3: `LeanNative` Compiled Native / GPU Binary    │
                       │ (LLVM IR / C-ABI SIMD / Apple Metal 3.0 / CUDA PTX)    │
                       └────────────────────────────────────────────────────────┘
```

### Automatic Fault Triangulation
When a discrepancy occurs on input $x$, the 3-way oracle immediately pinpoints the buggy layer without human debugging:

| Discrepancy Pattern | Exact Fault Location | Automated Action |
| :--- | :--- | :--- |
| **`Engine 1 ≠ Engine 2`** | Bug in **`Bridge.lean` (`LCNF → LNIR`)** OR **`Eval.lean` formal semantics** does not match Lean 4's runtime semantics! | Shrink $P$ to a minimal `< 15 line` `.lean` reproducer; add to `MutantSuite.lean`; fix `Bridge.lean` / `Eval.lean` in a `SPEC` wave. |
| **`Engine 2 ≠ Engine 3`** (while `Engine 1 == Engine 2`) | Bug in a **`LeanNative/Transform/` optimization pass** OR **`LeanNative/Backend/` codegen**! | Run binary bisection across `--disable-pass=<name>` flags (`run_ablation_ratchet.py`) to isolate the exact offending pass or backend emitter in $< 5\text{s}$. |
| **`Engine 2` reports `finalHeap.liveObjects > 0` or `useAfterFree`** | **Reference-counting (`incRef`/`decRef`) or borrow-inference leak/double-free**! | Reject pass immediately; extract failing `HeapState` trace as a `negWitness` for `OwnershipRC.lean`. |
| **`Engine 3` fails under `ASan` / `UBSan` / `compute-sanitizer`** | **C-ABI / SIMD alignment / GPU out-of-bounds or race bug**! | Reject kernel; extract lane/offset parameters as a `negWitness` in `SpecLocked.lean`. |

---

## 2. The 4-Tier Conformance Corpus (`C1`–`C4`)

To prevent overfitting to synthetic micro-benchmarks, the conformance suite draws from **four orthogonal tiers** of real Lean 4 and Lake projects:

### Tier C1: Official Lean 4 Compiler Run Suite (`leanprover/lean4/tests/lean/run`)
- **What It Covers**: Curried/uncurried closures, partial applications (`pap`), mutual tail recursion, `UInt8/16/32/64` & `USize` wrapping/overflow edge cases, `BitVec`, `Array` / `ByteArray` copy-on-write (`isExclusive` sharing vs. in-place mutation), `Thunk`, `Task`, and `ST` / `IO.Ref`.
- **Why It Matters**: This is the exact suite the Lean 4 compiler team uses to test `LCNF` and `EmitC`. Any assumption in `LNIR` that breaks on polymorphic closures or shared arrays fails immediately here.
- **Target**: **250+ self-contained run tests** executed on every CI run (`< 15s` via content-addressed binary caching).

### Tier C2: Real-World Lake Ecosystem Packages
Pinned by `(repo_url, commit_sha, lean_toolchain)` so builds are 100% deterministic:
1. **`leanprover-community/batteries`** (`Batteries.Data.Array`, `RBMap`, `HashMap`, `BitVec`, `UInt`): Stresses array slicing, binary search, hash collisions, and reference-counted tree rebalancing.
2. **`Th0rgal/lean-sys`** (`LeanSys.Store`, `LeanSys.Http`, `LeanSys.Scan`): Stresses zero-copy byte scanners (`SSE`, `GFM`, `RichTag`), BLAKE3/CRC32 checksums, and parallel 1D chunk partitioning.
3. **`lecopivo/SciLean` & `LeanAV` (`lean-ffmpeg`)**: Stresses 1D/2D/3D numerical loops, stencil Halo indexing, SIMD `SWAR` / `PCLMULQDQ` / NEON reductions, and `Float` / fixed-point kernels.
4. **Cryptographic & ZK Primitives (`Verity`, `ArkLib`, Blake3, Ligerito `GF(2^128)`)**: Stresses 128-bit carryless multiplication (`clmul64` / `vmull_p64` / `VPCLMULQDQ`), `low_twiddle_zmm_ntt` (`twHi = 0`), `trineon_fold_four` (`17-CLMUL`), 256-bit lazy reduction, and 2-layer Radix-4 NTT butterflies across CPU SIMD, CUDA PTX, and Apple Metal 3.0 (including non-zero M3 buffer offsets).

### Tier C3: Cross-Regime Holdout Portfolio (`R1`–`R6`)
- Mirrors the 6 orthogonal regimes in `maxwell/campaigns/corpora.toml` (`R1` Commutative Algebra, `R2` Hard Analysis, `R3` Formal Conjectures/Combinatorics, `R4` Set Theory/`lean4lean` Foundations, `R5` Verified Systems/SAT/ZK, `R6` Mathematical Physics/`SciLean`) to test `turbo-lean`'s `con-leche` kernel checker (`G1`) and CAS proof-term distillation (`G2`) across every mathematical style in the Lean 4 ecosystem.
- Enforces the `DEV` vs. `SEALED` split: `SEALED` manifests are evaluated at most once per candidate architecture.

### Tier C4: Grammar-Guided `LCNF` & Alive2-Style Mutation Fuzzer
- **Random Well-Typed `LCNF` Generator (`scripts/fuzz_lcnf_conformance.py`)**:
  Generates random, guaranteed-terminating `LCNF` functions combining:
  - Shared vs. exclusive `Array UInt64` aliases passed to the same function (`foo arr arr`), testing whether `HoistExclusivity` or `OwnershipRC` ever mutates a shared array in place.
  - Boundary scalar values: $\{0, 1, 2, 31, 32, 63, 64, 2^{31}-1, 2^{31}, 2^{63}-1, 2^{63}, 2^{64}-1\}$.
  - Deep nested `letBind` chains, `ite` diamond merges with asymmetric `incRef`/`decRef` branches, and `loop` / `parFor` constructs with step sizes $0, 1, 2, 7$.
- **Automatic Counterexample Shrinking**:
  Any fuzz seed where `Engine 1 ≠ Engine 2` or `Engine 2 ≠ Engine 3` is automatically delta-reduced and promoted into a permanent regression test in `lean/LeanNative/Tests/ConformanceRegressions.lean`.

---

## 3. Execution & Gate Integration

```bash
# Fast pre-commit & blocking CI conformance check (Tier C1 scalar subset + Tier C4 fuzzer + ASan/UBSan)
python3 scripts/run_conformance_suite.py --tier C1,C4 --fuzz-seeds 32 --asan --ubsan

# Planned full nightly / milestone conformance & sanitizer soak (Tiers C2 and C3 fail closed until wired)
python3 scripts/run_conformance_suite.py --tier C1,C2,C3,C4 --fuzz-seeds 10000 --asan --ubsan
```

**Hard Gate**: A single mismatch (`mismatch_count > 0`), RC leak (`rc_leak_count > 0`), or requested unimplemented tier (`C2`, `C3`) fails closed with a non-zero exit code.

---

## 4. Current Coverage Status (`main` @ `2a8939e`, `2026-10-31`)

- **Tier C1 (`lean4/tests/lean/run`)**: Scalar + narrow-unsigned (`UInt8/16/32/64`, `USize`, `Bool`, constructor enums, O(N) join-point DAGs, flat-scalar tuple helpers) 3-way fixture (`scripts/test_scalar_frontend.py` across `lean -c`, `eval-lnir --cases-file` / `validate-tv`, and `LeanNative` LLVM) plus Stage 1D heap ADT / Perceus RC probes (`#280`, `e585ba9`) are merged and run on every push and PR via `.github/workflows/roadmap-conformance.yml` (`scripts/verify_roadmap_contract.sh` + `python3 -m unittest -v scripts/test_scalar_frontend.py`). Direct scalar-payload heap ADTs and `compile-llvm` of heap ops fail closed. Expanding Tier C1 to 250+ upstream `lean4/tests/lean/run` files (closures, `pap`, `letrec`, `Array`/`ByteArray` sharing, signed `Int*`) remains open.
- **Tier C2 (Ecosystem Lake Packages)**: First external large-scale incremental-verification validation on **`eth-act/clifv`** (4,624 modules, Lean 4.34.1; PR `#273`, integrated via `#275` and `#309`) is merged on `main`, landing the plain-`lean` fallback `#print axioms` gate, `[axioms] allow` policy resolved at `--base`, Lake reverse-dependency escalation (including `lean_exe` roots) on non-local edits, non-destructive `.olean` refresh, `--timeout` propagation, `bv_decide` `cadical` lookup, and `check --decl` declaration-discovery parity. `python3 scripts/run_conformance_suite.py --tier C2` currently fails closed (`BLOCKED_MISSING_DEPENDENCY`) until 3-way `LeanNative` codegen conformance on `Batteries`, `LeanSys`, `SciLean`, and `ArkLib` is wired. (Separately in `Th0rgal/orb`, `orb#1399` recorded local 6-engine conformance across all 128 public `Orb.Kernel` + `LeanSys.Spec` exports at Orb `3c70e5ada` / Turbo `e585ba9` / LeanSys `c089f3e3`.)
- **Tier C3 (`R1`–`R6` Holdouts)**: Pending official `leanprover/con-leche` vendoring and real `.olean` / `Expr` CAS replay (`M2`–`M3`). `python3 scripts/run_conformance_suite.py --tier C3` fails closed (`BLOCKED_MISSING_DEPENDENCY`).
- **Tier C4 (Grammar-Guided `LCNF` Fuzzer)**: `scripts/fuzz_lcnf_conformance.py` and `scripts/run_conformance_suite.py --tier C1,C4 --fuzz-seeds 32 --asan --ubsan` run inside `scripts/verify_roadmap_contract.sh` and the blocking `.github/workflows/roadmap-conformance.yml` workflow. ASan instruments emitted scalar LLVM IR (`sanitize_address` verified across all emitted function attribute groups) and the C driver; UBSan (`ubsanScope = c_driver_and_link_runtime_only_not_llvm_ir`) instruments the C driver and link runtime only because Clang's `-fsanitize=undefined` is a C/C++ frontend pass that does not insert UB checks into pre-generated `.ll` modules. Compilation uses Lean's `clang -c` paired with a two-step-probed sanitizer linker (such as `/usr/bin/gcc` when Lean's bundled toolchain lacks `libclang_rt.asan`), failing closed if no compatible sanitizer runtime is available; this does **not** claim LLVM-IR UBSan coverage or full heap/loop/alias fuzzer coverage. Scaling to 10,000 nightly seeds and shared-array alias / `seqFor` fuzzing remain open.
