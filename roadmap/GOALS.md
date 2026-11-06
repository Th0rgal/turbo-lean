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

### Historical Baseline & Remaining Trust Gaps
`LeanNative` pairs operational semantics (`evalCode` in `LeanNative/Semantics/Eval.lean`) and machine-checked proofs for middle-end passes, `SymbolicTV`, `RealLCNFBridge`, and typed Target-IR AST subsets (`LLVMAst`, `PTXAst`, `MetalAst`, `StableHLOAst`) with two remaining end-to-end gaps (having historically started from):
1. **Frontend (`LeanNative/IR/Bridge.lean` & `RealLCNFBridge.lean`)**: Historically lowered `Lean.Compiler.LCNF.Code` using string-suffix matching and inline rewrites (since extracted to modular passes with `Bridge.lean` compressed to `< 350` LOC and `RealLCNFBridge` verified on scalars/tuples/Stage-1D ADTs against in-repo `RealLCNFSemantics`), while upstream `lean4lean` `LCNF` semantics and higher-order/recursive `LCNF` coverage remain open.
2. **Backend (`LeanNative/Backend/LLVM.lean`, `MLIRGPU.lean`, `Metal.lean`, `Driver/CoreCLI.lean`)**: Production text emitters still serialize parts of LLVM IR, CUDA PTX, Apple Metal 3.0, and C-ABI SIMD kernels via direct string formatting outside the proved Target-IR AST pretty-printers, and the Target-IR semantics are not yet bridged to upstream `lean-mlir`, `LNSym`, or `sail-riscv-lean`.

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

### Historical Motivation & Ratchet Baseline
Early feature waves accumulated substantial structural duplication across the repository (subsequently ratcheted down by CI gates `Bridge.lean <= 350 LOC` and `CoreCLI.lean <= 1000 LOC`, with backend string-emitter unification continuing below):
- `lean/LeanNative/Driver/CoreCLI.lean` had grown to **~7,500 LOC** of embedded C/SIMD/Metal source strings (now gated at `<= 1,000 LOC`).
- `lean/LeanNative/IR/Bridge.lean` had grown to **~2,000 LOC** of ad-hoc Wave 15–32 AST matchers (now gated at `<= 350 LOC`).
- `lean/LeanNative/Spec.lean` and `lean/TurboLean/Spec.lean` accumulated repetitive 4-field boolean `MetaGateSpec` blocks suitable for higher-order combinator factoring.

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

## Remaining Open Roadmap Items

- **`G1` (`con-leche` Zero-Copy Kernel)**: Vendor official `leanprover/con-leche` (+ `lean4lean` corner cases), replace the self-contained `"OLEN"` model with a direct Lean 4 `.olean` / `ConstantInfo` mmap reader for compatible `lean-toolchain`s, and register the compiled `con-leche` backend behind the landed `--kernel <auto|standard|con-leche|both>` selector and `schema_version = 2` provenance receipts.
- **`G2` (`HeaderPin` & CAS Proof Distillation)**: Connect `HeaderPin` to real parsed Lean surface signatures vs. elaborated `Lean.ConstantInfo.type`, and emit/replay kernel `Expr` witnesses in `TurboStore` during `build`/`ci-verify`.
- **`G3.1` & `G3.2` (Broader `LCNF` Coverage)**: Expand `Lean.Compiler.LCNF -> LNIR` frontend coverage beyond the current scalar, flat-tuple, and bounded Stage-1D constructor/ADT subset (with slice and non-escaping async passes in middle-end `LNIR`) to upstream `lean4lean` `LCNF` semantics, general recursion, closures/higher-order `.fvar` calls, `letrec`, signed `Int*`, and full LLVM heap-op codegen.
- **`G3.3` & `G4` (Upstream Semantics & Unified AST-to-Text Emission)**: Link upstream `opencompl/lean-mlir`, `leanprover/LNSym`, and `opencompl/sail-riscv-lean`, and route production `LLVM`/`PTX`/`Metal`/`StableHLO` text emission directly through the proved Target-IR AST pretty-printers instead of standalone string emitters.
- **`G5` (Ecosystem Differential Fuzzing)**: Expand 3-way differential conformance (`--tier C2,C3`) across 250+ upstream `lean4/tests/lean/run` files, real Lake packages (`Batteries`, `LeanSys`, `SciLean`), and 10,000-seed nightly `LCNF` fuzzing.
