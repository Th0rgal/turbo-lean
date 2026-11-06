# `turbo-lean` North-Star Technical Goals (`G1`–`G5`)

> **Scope**: This document defines **what** `turbo-lean` and `LeanNative` must achieve across five orthogonal technical pillars. It contains **zero** agent-orchestration heuristics; execution strategies live exclusively in [`MAXWELL_STRATEGIES.md`](./MAXWELL_STRATEGIES.md), and exact machine-checkable theorem contracts live in [`VALIDATION_CONTRACTS.md`](./VALIDATION_CONTRACTS.md).

---

## Goal G1: Pluggable Kernel Architecture & Receipt Sovereignty (`standard` C++ `Environment.replay` + Optional `con-leche` + `lean4lean`)

### Problem Statement & Ecosystem Reality
Every target Lean 4 project (`Mathlib`, `EthLib`, `eth-act/clifv`, `init-e`, and `turbo-lean` itself) pins a specific upstream `lean-toolchain` (for example `leanprover/lean4:v4.24.0`, `v4.28.0`, or `v4.35.0`), whereas [`leanprover/con-leche`](https://github.com/leanprover/con-leche) (Joachim Breitner / Lean FRO — a ~1,700 LOC pure-Lean typechecker proven sound against `ZFC + universes` at **~0.69× the CPU instructions** of the C++ kernel) tracks a single upstream Lean toolchain/export format at a time and parses `lean4export` streams out of the box. Consequently, `turbo-lean` cannot force a single hardcoded external kernel across every target repository's `lean-toolchain`: kernel verification must be **pluggable, toolchain-compatible, and cryptographically bound into every receipt**.

### Target Architecture
1. **Pluggable Kernel Engine Contract (`--kernel <auto|standard|con-leche|both>` / `[kernel] engine` / `TURBO_LEAN_KERNEL_ENGINE`)**:
   - **`standard` (Default Universal Baseline)**: Every target repository's exact pinned `lean-toolchain` C++ kernel (`Kernel.Environment.replay` + `Inspector.lean` + `StatementHash.lean`), universally compatible across all Lean 4 versions.
   - **`con-leche` & `both` (Strict Opt-In Verified Lean-in-Lean Kernel)**: Runs `leanprover/con-leche` standalone or in dual-auditor lockstep alongside `standard` (`both`) when a compatible `con-leche` backend is registered for the project's `lean-toolchain`. Explicit `--kernel con-leche` and `--kernel both` **fail closed** (exit non-zero, emit no verified verdict or receipt) whenever `con-leche` is unavailable or incompatible with the target `lean-toolchain` — never silently downgrading to `standard`.
   - **`auto` (Toolchain-Aware Selection)**: Selects a registered compatible `con-leche` backend when available for the target `lean-toolchain`, and otherwise transparently resolves to `standard` while recording the exact resolved engine in JSON outputs and receipts.
   - **Precedence & `--base` Policy Isolation**: Explicit CLI `--kernel` overrides `TURBO_LEAN_KERNEL_ENGINE`, which overrides `[kernel] engine` in `turbo-lean.toml`. In `pr-verify` and `ci-verify --base <ref>`, `[kernel] engine` is read strictly from `--base` (an untrusted PR branch edit to `turbo-lean.toml` is ignored); `ci-verify` without `--base` ignores checkout `turbo-lean.toml`.
2. **Cryptographic Receipt Kernel Provenance (`VerificationReceipt`)**:
   - Every newly issued `VerificationReceipt` (`ci-verify`, `pr-verify`; `schema_version = 2`) records and domain-separates `kernel_engine` (`"standard" | "con-leche" | "both"`), `lean_toolchain`, and `con_leche_rev` (`Option<String>`) inside the length-prefixed `compute_receipt_blake3` digest (and therefore inside optional Ed25519 `ed25519-v1` signatures). `verify-receipt` fails closed on tampered provenance, missing/empty `lean_toolchain`, `"standard"` carrying a `con_leche_rev`, or `"con-leche"`/`"both"` missing `con_leche_rev`, while preserving offline verification and `--baseline-receipt` comparison for legacy `schema_version = 1` receipts.
3. **Vendored `con-leche` Backend & Zero-Copy `.olean` Bridge (`lean/TurboLean/Kernel/ConLeche/`)**:
   - Integrate `leanprover/con-leche`'s `RecM` typechecker and `ZFC` soundness proofs (paired with [`digama0/lean4lean`](https://github.com/digama0/lean4lean) corner cases) behind a zero-copy mmap `.olean` / `Lean.ConstantInfo` reader (`LeanSys.Mmap`) and `LeanNative`-compiled `turbo-con-leche` binary (`< 0.65×` C++ kernel instructions on compatible toolchains), unlocking `--kernel con-leche` and `--kernel both`.

---

## Goal G2: Elaboration De-Trusting & Sub-Millisecond CAS Proof Distillation

### Problem Statement
In Lean 4 builds, **85–95% of wall-clock time** is spent in `Lean.Elab` (`MetaM`, typeclass synthesis `synthInstance`, and tactics like `simp`, `omega`, `aesop`, `bv_decide`), while kernel checking takes only 5–15%. Moreover, macros, custom elaborators, and notations can silently alter a theorem's surface statement during elaboration.

### Target Architecture
1. **Surface-Syntax Header Round-Trip Audit (`HeaderPin`)**:
   - Never trust `Lean.Elab` to preserve a human-written theorem statement.
   - After elaborating a top-level theorem/definition header into `ConstantInfo.type`, run a deterministic **Explicit Pretty-Printer & Surface AST Matcher** (`pp.all = true`, `pp.universes = true`, `pp.explicit = true` structural comparison against the parsed `.lean` surface signature) and verify zero shadowed local binders (`shadowed_constants == 0`).
2. **Untrusted Elaboration $\to$ Distilled CAS Kernel Witness (`LNIR_EXPR_V1`)**:
   - Treat `Lean.Elab` strictly as a **cold-path hint generator** for proof bodies.
   - When a declaration is elaborated once, extract and compress its resulting kernel `Expr` proof term (or zero-dependency certificate: `simp only [...]` lemma list, Farkas linear combination witness for `omega`, LRAT witness for `bv_decide`, `MathlibZeroDepCert`) into the content-addressed store (`LeanSys.Store`).
3. **Warm Build & CI Elaboration Bypass (`turbo-lean build --replay-cas-expr`)**:
   - Whenever a theorem's statement and dependency cone hashes match the CAS, **skip `Lean.Elab` and `MetaM` 100%** and feed the cached `LNIR_EXPR_V1` proof term directly into the `con-leche` kernel checker (`< 1 ms` per module).
4. **Elaboration Hotspot Accelerators (Cold Path)**:
   - Cache `DiscrTree` and `synthInstance` diamond resolutions in memory-mapped `.olean` sidecars so cold `MetaM` elaboration of algebra/analysis modules (`R1`/`R2`) drops by $\ge 2.5\times$.

---

## Goal G3: End-to-End Semantic Sovereignty (Closing the Frontend & Backend Trust Sandwich)

### Problem Statement
Today, `LeanNative` has real operational semantics (`evalCode` in `LeanNative/Semantics/Eval.lean`) and machine-checked proofs for scalar peepholes, 1D loops, and `SymbolicTV`. However, it is sandwiched between two unverified layers:
1. **Frontend (`LeanNative/IR/Bridge.lean`)**: Lowers `Lean.Compiler.LCNF.Code` to `LNIRCode` using fragile string-suffix matching (`callee.endsWith "add"`, `callee.endsWith "get"`) while mixing 1,500+ lines of "Wave 15–32" whole-function rewrites directly into the lowering pass.
2. **Backend (`LeanNative/Backend/LLVM.lean`, `GPUIR.lean`, `Metal.lean`, `Driver/CoreCLI.lean`)**: Emits LLVM IR, CUDA PTX, Apple Metal 3.0, and C-ABI AVX-512/NEON kernels via raw string interpolation without a mechanized target ISA semantics.

### Target Architecture

```
Lean 4 Surface Syntax
   │  (G2: HeaderPin Audit + CAS Proof Distillation)
   ▼
Kernel Expr / ConstantInfo ──► Verified by `con-leche` (G1: ZFC Soundness)
   │
   ▼
Lean.Compiler.LCNF.Code (`lean4lean` LCNF Operational Semantics)
   │  (G3.1: Verified 1-to-1 Syntactic Bridge, 0 inline optimizations)
   ▼
LNIRCode (`LeanNative/Semantics/Eval.lean` + Full-Bitwidth `BitVec 64` Heap/RC Semantics)
   │  (G3.2: Compositional `VerifiedTransformContract` Passes + Total `SymbolicTV`)
   ▼
Typed Target IRs Grounded in Official External Semantics (G3.3):
   ├─► LLVM / MLIR SCF & Arith (`opencompl/lean-mlir`: `BitVec` + `PoisonOr` Alive2 semantics)
   ├─► ARM64 NEON / Crypto (`leanprover/LNSym`: Armv8 AArch64 ISA semantics & `cosim`)
   ├─► RISC-V RV64 (`opencompl/sail-riscv-lean`: Official Sail RISC-V ISA semantics)
   └─► GPU SIMT (`GPUIR` / `Metal 3.0` / `PTX`: Warp/threadgroup barrier & buffer-offset semantics)
```

#### G3.1 — Pure, Verified `LCNF → LNIR` Frontend (`Bridge.lean`)
- **Delete String-Suffix Dispatch**: Replace `callee.endsWith ...` in `classifyPrimitive` with exact pattern matching on fully-qualified `Lean.Name` constants (````UInt64.add`, ````Array.uget`, ````ByteArray.uset`, etc.) and `LCNF` type signatures.
- **Zero Optimizations in `Bridge.lean`**: Strip all Wave 15–32 pattern-matching rewrites out of `Bridge.lean` and move them into modular `LNIR → LNIR` passes under `LeanNative/Transform/`.
- **Frontend Refinement Proof**: Formalize the small-step/fuel evaluator for `LCNF.Code` (building on `digama0/lean4lean`) and prove that `lowerDecl : LCNF.Decl → LNIRDecl` preserves evaluation semantics (`LCNFRefinesLNIR`).

#### G3.2 — Full-Bitwidth `LNIR` Semantics & Proof-Carrying Middle-End (`Transform/`)
- **Upgrade `Value` & `HeapState` (`Eval.lean`)**:
  - Replace truncated `Nat` array/tuple elements with exact `BitVec 64`, `BitVec 128` (`GF(2^128)` carryless `clmul`), nested `Value` trees, and explicit IEEE-754 `Float` bits.
  - Unify `Eval.lean`'s `HeapState` with `Spec.lean`'s `RCState` so reference-counting (`incRef`, `decRef`, `isExclusive` in-place mutation) is verified on actual `LNIRCode` programs rather than disconnected 3-line models.
- **Type-Enforced Pass Pipeline (`VerifiedTransformContract`)**:
  - Deprecate string-based `OptimizationCert.theoremRef : String` in `CertChecker.lean`.
  - Every pass registered in `Transform/Pass.lean` must inhabit `VerifiedTransformContract` (`run : LNIRDecl → LNIRDecl` paired with `sound : ∀ d, CodeRefines d.body (run d).body`) or pass the total `SymbolicTV` verifier (`symbolicCodeRefines d.body (run d).body = true` bridged via `symbolicCodeRefines_sound`).

#### G3.3 — Official Mechanized Target Semantics (`lean-mlir`, `LNSym`, `sail-riscv-lean`)
- **LLVM & MLIR (`opencompl/lean-mlir`)**:
  - Replace raw string interpolation in `Backend/LLVM.lean` and `Backend/MLIRGPU.lean` with an AST lowering into `lean-mlir`'s intrinsically-typed `llvm`, `arith`, and `scf` dialects.
  - Prove lowering soundness against `lean-mlir`'s `BitVec` + `PoisonOr` (poison/undef) semantics, ensuring `nuw`/`nsw`/division-by-zero/shift-overflow UB can never be introduced by `LeanNative`.
- **ARM64 NEON / Crypto (`leanprover/LNSym`)**:
  - Verify `LeanNative`'s critical ARM64 kernels (`vmull_p64` carryless multiply, `veorq_u64` / `eor3` `TriNeon` 3-lane accumulator, Radix-4 NTT butterflies, BLAKE3 compression) against `leanprover/LNSym`'s formal Armv8 AArch64 instruction semantics and hardware co-simulation (`cosim`).
- **RISC-V RV64 (`opencompl/sail-riscv-lean`)**:
  - Ground all RISC-V codegen and cycle/tick bounds in `opencompl/sail-riscv-lean` (mechanized Sail RV64 specification).
- **GPU SIMT (`CUDA PTX` & `Apple Metal 3.0`)**:
  - Formalize multi-thread warp/threadgroup execution with shared-memory bank access, barrier synchronization (`syncthreads` / `threadgroup_barrier`), and M3 Metal buffer-offset bounds (`in_byte_off`, `out_byte_off` alignment & disjointness), proving race-freedom and observational equivalence to sequential `LNIRCode.parFor`.

---

## Goal G4: Radical Simplicity & Internal Abstractions (The LOC Compression Ratchet)

### Problem Statement
Rapid feature waves have accumulated substantial structural duplication across the repository:
- `lean/LeanNative/Driver/CoreCLI.lean` has grown to **~7,500 LOC**, largely embedding raw C/SIMD/Metal source strings.
- `lean/LeanNative/IR/Bridge.lean` has grown to **~2,000 LOC** of ad-hoc Wave 15–32 AST matchers.
- `lean/LeanNative/Spec.lean` (~1,415 LOC) and `lean/TurboLean/Spec.lean` (~800 LOC) contain dozens of repetitive 4-field boolean `MetaGateSpec` boilerplate blocks.

### Target Architecture (Compress Maintained LOC by $\ge 50\%$ While Increasing Coverage)
1. **Replace 32 Ad-Hoc Optimization Waves with 3 Compositional Verified Engines**:
   - **Engine 1 — Verified Equality-Saturation / Declarative Peephole Engine (`Transform/EqSat.lean`)**:
     One generic congruence-closure + context-lifting theorem (`applyRewriteTable_sound`) parameterized by a compact table of verified `BitVec` / `GF(2^128)` algebraic rules (subsuming `AlgebraicOpt`, `PeepholeProofs`, `Superopt`, `low_twiddle_zmm_ntt`, `trineon_fold_four`, and lazy 256-bit reduction).
   - **Engine 2 — Structured Polyhedral Loop (`scf`) & Buffer Scheduler (`Transform/LoopSchedule.lean`)**:
     One parameterized affine loop transformer handling loop fusion, strip-mining/tiling, 2-layer Radix-4 NTT butterfly fusion, 2D stencil Halo tiling, and ping-pong buffer rotation under a single induction principle.
   - **Engine 3 — Linear RC Ownership & Alias Abstract Interpreter (`Transform/OwnershipRC.lean`)**:
     One forward/backward abstract interpretation lattice over `LNIRCode` proving borrow inference, `incRef`/`decRef` cancellation, tuple unboxing (`UnboxTupleSROA`), and `isExclusive` in-place array updates (`HoistExclusivity`).
2. **Generate C-ABI / SIMD / Metal Kernels from `LNIR` Instead of Hardcoded Strings in `CoreCLI.lean`**:
   - Extract the hardcoded C99/AVX-512/NEON/Metal templates out of `Driver/CoreCLI.lean` and generate them directly from verified `LNIR` kernel definitions via the typed backend pipeline, shrinking `CoreCLI.lean` from ~7,500 LOC to **$< 1,000\text{ LOC}$**.
3. **Parameterized Spec Combinators**:
   - Replace repetitive `MetaGateSpec` boilerplate with higher-order dependent combinators (`Spec.andGate`, `Spec.boundedWindowGate`, `Spec.refinementGate`) that automatically synthesize `sound`, `complete`, `posWitness`, and `negWitness` proofs from declarative domain constraints.

---

## Goal G5: Continuous Non-FV Differential Conformance & Miscompilation Fuzzing

### Target Architecture
Even with machine-checked proofs, specification blind spots (e.g., mismatched FFI calling conventions, unmodeled runtime closures, or ABI alignment edge cases) can only be caught by executing real programs end-to-end.
- Establish the automated **3-Way Differential Conformance Harness** defined in [`CONFORMANCE_SUITE.md`](./CONFORMANCE_SUITE.md), requiring **100% bitwise output parity and zero RC heap leaks** across:
  1. Stock Lean 4 C compiler (`lean -c`),
  2. Formal `LNIR` operational interpreter (`evalDecl`), and
  3. `LeanNative` compiled native/SIMD/GPU binaries
  on the official Lean 4 run-test suite, real Lake packages (`Batteries`, `SciLean`, `LeanSys`, `ArkLib`), and 10,000+ grammar-fuzzed `LCNF` programs.

---

## Summary Milestone Table & Audit Status (`main` @ `7ae2a63`, 2026-10-31)

> **Distinction enforced across this roadmap**: **Self-contained formal models** (proved `0 sorryAx` in Lean 4 and checked locally by `scripts/verify_roadmap_contract.sh`) are tracked separately from **GitHub Actions CI enforcement** (`.github/workflows/ci.yml`, `.github/workflows/roadmap-conformance.yml`, and `scripts/ci_verify.sh`) and **upstream integration & runtime CLI wiring** on real Lake projects (`Mathlib`, `EthLib`, `init-e`, `clifv`).

| Milestone | Primary Deliverable | Target Metric / Exit Condition | Current Status on `main` (`7ae2a63`) | Remaining Gap to Exit |
| :--- | :--- | :--- | :--- | :--- |
| **M1 / M1.4: Anti-Cheat, Trust Boundary & Conformance Foundation** | `audit-spec` v2.1 (`--policy strict-proofs`) + `MutantSuite.lean` + Ed25519 trust domains/receipts + scalar 3-way conformance | `0` vacuous/stub bypasses; `94/94` (`TurboLean`) & `120/120` (`LeanNative`) tight specs; `76` C-ABI gates; fail-closed cache/receipt trust | **Landed (`#263`–`#265`, `#267`, `#269`, `#272`, `#275`, `#276`, `#280`, `#291`, `#294`, `#303`, `#304`, `#307`, `#309`, `#310`, `#311`, `#315`, `#316`).** `94/94` (`TurboLean`) & `120/120` (`LeanNative`) tight specs and `76` C-ABI gates run in CI; in-kernel `.olean` soundness gate (`--audit-modules`, with final audited `.olean` verdicts in `#311`), Lake `.trace`/`.olean.hash` sidecar verification, `bwrap` untrusted isolation (provisioned on push & PR in CI), zero-redirect HTTPS + exact loopback/token confinement, configurable `[axioms] allow` policy (resolved at `--base`, never `sorryAx`/`Lean.trustCompiler`), non-local edit Lake reverse-dep recheck, atomic CAS blob publication/repair (`#315`), staged DB/Zygote lock-free publication + closure-digest memoization (`#316`), and opt-in remote telemetry with untrusted TOML isolation are merged. Stage 1D heap ADT / Perceus RC (`#280`, `e585ba9`) is on `main`. Scalar + flat-tuple 3-way conformance and the grammar fuzzer run under `scripts/verify_roadmap_contract.sh` and the blocking `.github/workflows/roadmap-conformance.yml` job (`--tier C1,C4 --asan --ubsan`). | Upgrade `audit-spec` from source unfolding to full kernel `ConstantInfo` delta-unfolding; expand conformance beyond the scalar/flat-tuple/Stage-1D subset to 250+ `lean4/tests/lean/run` files. ASan covers emitted scalar LLVM IR + C driver while UBSan covers only the C driver/link runtime (`c_driver_and_link_runtime_only_not_llvm_ir`), not pre-emitted LLVM IR or full heap/loop/alias coverage. |
| **M2: `con-leche` Zero-Copy Kernel** | `TurboLean/Kernel/ConLeche/` + real `.olean` mmap bridge + `LeanNative` compilation + CLI switch | `pr-verify --kernel con-leche` runs official `leanprover/con-leche` (`master`) on real `.olean`s in `< 1 ms` at $\le 0.65\times$ C++ kernel instructions | **Pluggable `--kernel` selector, `--base` policy isolation & receipt provenance landed; upstream `con-leche` backend still unwired.** `lean/TurboLean/ConLeche.lean` (551 LOC) proves `inferType_sound`, `con_leche_verify_decl_sound`, and `olean_mmap_bridge_sound` over a self-contained CIC + `"OLEN"` shard format. `check`, `ci-verify`, and `pr-verify` wire `--kernel <auto\|standard\|con-leche\|both>`, `TURBO_LEAN_KERNEL_ENGINE`, and `--base`-isolated `[kernel] engine` in `turbo-lean.toml` (`crates/turbo-lean/src/kernel.rs`), domain-separating `kernel_engine`, `lean_toolchain`, and `con_leche_rev` into BLAKE3/Ed25519 receipts (`receipt.rs`) while failing closed whenever `con-leche` or `both` is explicitly requested without a compatible bundled `con-leche` backend (`pr-verify --nanoda-bin` remains a separate external binary hook). | Vendor official `leanprover/con-leche` (+ `lean4lean` corner cases), replace `"OLEN"` shard format with real Lean 4 `.olean` / `ConstantInfo` mmap reader (or `comparator`/`lean4export` replay) for compatible `lean-toolchain`s, and register the compiled `con-leche` backend so `--kernel con-leche` and `--kernel both` execute end-to-end. |
| **M3: Elaboration De-Trusting & CAS Replay** | `HeaderPin` surface-AST auditor + `LNIR_EXPR_V1` CAS proof-term distillation & warm bypass | Warm CI/build skips `Lean.Elab` on unchanged statements ($\ge 10\times$ warm replay speedup) | **Formal model landed; Lake/Elab pipeline unwired.** `lean/TurboLean/ElabAudit.lean` (158 LOC) proves `header_pin_prevents_statement_spoofing` and `cas_proof_replay_sound` over `ConLeche.Expr` (`"LNE1"` blobs). Real `Lean.Elab` still runs on builds, with `#275` escalating non-local statement/def/import edits to `lake build` over affected reverse-dependency modules (including `lean_exe` roots). | Connect `HeaderPin` to real parsed Lean surface signatures vs elaborated `Lean.ConstantInfo.type`; emit & replay real kernel `Expr` witnesses in `TurboStore` during `build`/`ci-verify`. |
| **M4: Verified `LCNF → LNIR` & 3 Unified Engines** | Pure 1-to-1 `Bridge.lean` ($\le 350$ LOC) + `EqSat`, `LoopSchedule`, `OwnershipRC` (`VerifiedCodePassContract`) | `0` `.endsWith` primitives; `Bridge.lean` $< 350$ LOC; O(N) join-point DAG sharing | **LOC, DAG sharing, Stage 1D heap subset & contract structure landed; full Lean LCNF coverage open.** `Bridge.lean` is **348 LOC** (`0` `.endsWith`), `EqSat`/`LoopSchedule`/`OwnershipRC`/`AlgebraicOpt` inhabit `VerifiedCodePassContract`, and `lowerLCNFCode_sound` is proved over the self-contained `LeanNative/IR/LCNF.lean` subset. `#265`, `#270`, and `#280` added narrow unsigned casts/Bool branches, O(N) scalar-select join-point DAG sharing, flat-scalar tuple helper inlining (nested tuples fail closed), and tuple-carrying heap ADT / Perceus RC lowering that still fails closed on direct scalar-payload heap ADTs and on `compile-llvm` of heap ops. | Connect `LCNF.lean` to upstream `Lean.Compiler.LCNF.Code` (`lean4lean`) beyond the scalar/flat-tuple/Stage-1D subset (`BridgeHelpers.lean` is 1,652 LOC of unproved ingestion helpers); complete closures, `letrec`, signed `Int*`, LLVM emission of heap ops, and full `HeapState`/`RCState` unification. |
| **M5: Official Backend Semantics (`lean-mlir` / `LNSym` / `sail-riscv`)** | Typed `lean-mlir` LLVM/SCF lowering + `LNSym` ARM64 NEON proofs + `CoreCLI.lean` $< 1,000$ LOC | `CoreCLI.lean` $< 1,000$ LOC; mechanized target proofs against upstream `opencompl/lean-mlir`, `leanprover/LNSym`, `opencompl/sail-riscv-lean` | **LOC target & internal semantic models landed; upstream Lake deps not yet linked.** `CoreCLI.lean` compressed to **921 LOC** (`KernelTemplates.lean` deleted). `BackendProofs.lean` proves `lowerToLeanMLIR_sound` and `arm64_f128_kernel_refines_lnir` (`0 sorryAx`) against internal `LeanMLIR`/`LNSym` models in `LeanNative/Backend/Semantics.lean` (305 LOC), while `Backend/LLVM.lean` still emits textual LLVM IR. | Pin & link upstream `opencompl/lean-mlir`, `leanprover/LNSym`, and `opencompl/sail-riscv-lean` (or prove formal bisimulation to their ASTs); route production `Backend/LLVM.lean` emission through the proved `lowerLNIRToMLIR` AST rather than string interpolation. |
| **M6: Ecosystem Conformance, OSS Packaging & Real-Repo Pilots** | 10,000 fuzzed `LCNF` programs + `Batteries` / `LeanSys` / `clifv` / `init-e` suites + modular crates + OSS `LICENSE` | `0` miscompilations, `0` RC leaks; turnkey `clifv` (4,624 modules) & `init-e` (`comparator`) support; clean OSS library split | **Licensing, opt-in telemetry, Q8 TRM v4, `clifv` integration, and blocking C1/C4 CI landed; crate split and C2/C3 open.** MIT `LICENSE` (`#268`), Apache-2.0 `LICENSE` in `Th0rgal/lean-sys` (`c089f3e`), opt-in remote telemetry (`--no-telemetry` / `turbo-lean telemetry` / `[telemetry]` with untrusted checkout isolation, `#276`), pure-Rust Q8 Matryoshka MUDD-TRM v4 (`#268`), and `eth-act/clifv` support (`#275`: **13.3 s $\to$ 0.65 s** and **378 s / 8.6 GB $\to$ 22 s / 0.7 GB** warm single-decl speedups) are merged. `.github/workflows/roadmap-conformance.yml` invokes `scripts/verify_roadmap_contract.sh` (`--tier C1,C4 --fuzz-seeds 32 --asan --ubsan`) plus `scripts/test_scalar_frontend.py`. `--tier C2` and `--tier C3` fail closed (`BLOCKED_MISSING_DEPENDENCY`). Orb local evidence at Orb `3c70e5ada` / Turbo `e585ba9` / LeanSys `c089f3e3` recorded 128 public exports, 1044 cases, 5220 comparisons, and zero mismatches, plus real x86_64, dgx-spark ARM64, Node WASM, and Linux-loaded Android x86_64 JNI paths; that evidence is not phase acceptance (23 partial / 106 unconnected, physical devices blocked, receipts unsigned). | Split `crates/turbo-lean` into reusable OSS library crates; vendor C2 ecosystem packages and C3 `con-leche` holdouts; scale nightly fuzzing to 10k seeds. Do not treat scalar ASan/UBSan or the Orb local receipts as full roadmap acceptance. |
