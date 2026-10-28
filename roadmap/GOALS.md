# `turbo-lean` North-Star Technical Goals (`G1`–`G5`)

> **Scope**: This document defines **what** `turbo-lean` and `LeanNative` must achieve across five orthogonal technical pillars. It contains **zero** agent-orchestration heuristics; execution strategies live exclusively in [`MAXWELL_STRATEGIES.md`](./MAXWELL_STRATEGIES.md), and exact machine-checkable theorem contracts live in [`VALIDATION_CONTRACTS.md`](./VALIDATION_CONTRACTS.md).

---

## Goal G1: Verified In-Memory Kernel & Receipt Sovereignty (`con-leche` + `lean4lean`)

### Problem Statement
`turbo-lean` currently relies on the stock ~30,000 LOC C++ Lean 4 kernel (`lean_env_add`, `Kernel.isDefEq`) for `ZygoteWorker` declaration checking and uses structural hash / environment inspection in `TurboLean/Kernel.lean` for `pr-verify`. Meanwhile, [`leanprover/con-leche`](https://github.com/leanprover/con-leche) (Joachim Breitner / Lean FRO) provides a complete Lean 4 typechecker in ~1,700 LOC of pure Lean 4 proven sound against `ZFC + universes` that executes in **~0.69× the CPU instructions** of the C++ kernel—but out of the box it parses `lean4export` text/NDJSON streams, which would bottleneck `turbo-lean`'s sub-2ms latency.

### Target Architecture
1. **Vendored & Verified `con-leche` Core (`lean/TurboLean/Kernel/ConLeche/`)**:
   - Integrate `leanprover/con-leche`'s `RecM` typechecker and its `ZFC` soundness proofs into `turbo-lean`, paired with [`digama0/lean4lean`](https://github.com/digama0/lean4lean) rules for any universe/nested-inductive corner cases where `con-leche` intentionally diverges from the C++ kernel.
2. **Zero-Copy In-Memory `Environment` / `.olean` Bridge (No NDJSON Serialization)**:
   - Bypass `lean4export` text serialization completely.
   - Implement a direct zero-copy reader over mmap'd `.olean` shards (`LeanSys.Mmap`) and in-memory `Lean.ConstantInfo` DAGs that feeds `con-leche`'s kernel state in microseconds.
3. **`LeanNative`-Compiled Standalone Kernel (`turbo-con-leche`)**:
   - Compile the `con-leche` checker via `LeanNative` (`0 import Lean` runtime dependency, unboxed pointer-tagged `Expr` representation, SwissTable hash-consing + WHNF/defeq memoization cache).
   - Wire `turbo-lean pr-verify --kernel con-leche` and `ci-verify` so every cryptographic receipt is verified by a formally verified Lean-in-Lean kernel at **$< 0.65\times$ the instructions** of the stock C++ kernel.

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

## Summary Milestone Table

| Milestone | Primary Deliverable | Target Metric / Exit Condition | Maintained LOC Target |
| :--- | :--- | :--- | :--- |
| **M1: Anti-Cheat & Conformance Foundation** | Kernel-AST `audit-spec` v2 + `SpecLocked.lean` + 3-Way Differential Conformance Runner | `0` 2-hop vacuous bypasses; `100%` parity on 250 baseline Lean 4 run tests | $\Delta\text{LOC} \le 0$ (prune redundant `MetaGateSpec`s) |
| **M2: `con-leche` Zero-Copy Kernel** | `TurboLean/Kernel/ConLeche/` + `.olean` mmap bridge + `LeanNative` compilation | `pr-verify --kernel con-leche` passes in `< 1 ms` at $\le 0.65\times$ C++ kernel instructions | $+1,500$ LOC (`con-leche`), $-1,500$ LOC legacy checks |
| **M3: Elaboration De-Trusting & CAS Replay** | `HeaderPin` surface-AST auditor + `LNIR_EXPR_V1` CAS proof-term distillation | Warm CI/build skips `Lean.Elab` on unchanged statements (`>= 10x` warm replay speedup) | $\Delta\text{LOC} \le 0$ |
| **M4: Verified `LCNF → LNIR` & 3 Unified Engines** | Pure 1-to-1 `Bridge.lean` + `EqSat`, `LoopSchedule`, `OwnershipRC` (`VerifiedTransformContract`) | `0` string-suffix primitives; `0` string `theoremRef`s; `Bridge.lean` $< 350\text{ LOC}$ | $-\mathbf{2,500}\text{ LOC}$ net reduction |
| **M5: Official Backend Semantics (`lean-mlir` / `LNSym` / `sail-riscv`)** | Typed `lean-mlir` LLVM/SCF lowering + `LNSym` ARM64 NEON proofs + `CoreCLI.lean` template elimination | `CoreCLI.lean` $< 1,000\text{ LOC}$; `100%` `LNSym` / `lean-mlir` semantic proofs on hot kernels | $-\mathbf{4,500}\text{ LOC}$ net reduction |
| **M6: Full Ecosystem Conformance Saturation** | 10,000 fuzzed `LCNF` programs + `Batteries` / `SciLean` / `ArkLib` 3-way differential suite | `0` miscompilations, `0` RC leaks, $\Delta\text{E2E}_{\text{geomean}}(\text{SEALED}) \ge +15\%$ | Total repo LOC reduced by $\ge 35\%$ |
