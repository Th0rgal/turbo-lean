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
   - **No replay on warm hits (G2b, deleted 2026-11-26 per the H2 bench-delta rule)**: a warm (cache-hit) `turbo-lean build` keeps its already-materialized outputs and replays nothing unless `--replay-cas-expr` is passed. G2b's warm-hit replay (on by default, then opt-in) was measured on the `build` path at about 15 ms per warm build for counters only (the build's outputs were already in place, so the replay changed nothing), so it was deleted (row G2b). `TURBO_LEAN_WARM_CAS_REPLAY` and `TURBO_LEAN_NO_WARM_CAS_REPLAY` are no longer read, and the build JSON and telemetry no longer carry `cas_expr_replay_missing`, `cas_expr_replay_invalid` or `cas_expr_replay_mode`. The explicit `--replay-cas-expr` flag remains the fail-closed audit mode.
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
- **Completed Baseline**: Canonical `Lean.Name` primitive lookup (`Bridge.lean` with `0` `callee.endsWith` occurrences), pass extraction out of `Bridge.lean` (`<= 350 LOC` CI gate), and `RealLCNFBridge` refinement proofs against in-repo `RealLCNFSemantics` for the scalar/tuple/Stage-1D ADT subset.
- **Remaining Upstream Frontend Refinement**: Ground `LCNF.Code` evaluation in upstream `digama0/lean4lean` operational semantics and extend verified lowering to higher-order closures, general recursive `LCNF` declarations, and remaining primitive operations.

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
2. **Unify Remaining Direct String Emitters onto Proved Target-IR AST Pretty-Printers**:
   - With `Driver/CoreCLI.lean` already compressed under its `<= 1,000 LOC` CI ratchet (`990 LOC`), route remaining direct string codegen paths in `Backend/LLVM.lean`, `Backend/MLIRGPU.lean`, `Backend/Metal.lean`, `Backend/Hybrid.lean`, and `Driver/CoreCLI.lean` through verified `LNIR → TargetAst → TargetAst.pp` pipelines.
   - **Stage 1 partial progress**: PTX custom-scalar kernels use `PTXLower.lowerKind` and `ppPTXKernel`, with M7/M8 targeting the live lowerer. Covered Metal scalars, device functions and wrappers use AST printers, with M9/M10 targeting `MetalLower`; covered i64 StableHLO map/zip/saxpy/dot bodies use `ppBody`, preserving TPU attributes. An optional LLVM AST-emission entrypoint (`LLVMEmitVerify`) agrees with `LLVMLower`; the production runtime emitter in `LLVM.lean` remains separate. Parsers, general covered roundtrip theorems (`parse ∘ pp = some`), and canonical printer injectivity are proved in kernel across covered scalar PTX operands/addresses/instructions/statements/kernels (`parsePTXKernel_roundtrip`, `ppPTXKernel_injective_on_canonical`), Metal canonical expressions/types/attributes/parameters/statements/blocks/kernels (`parseMSLKernel_roundtrip`, `ppMSLKernel_injective_on_canonical`), and the 22-operation covered StableHLO fragment plus `FuncOp` with SSA `TypeEnv` threading (`parseStableHLOOp_roundtrip`, `ppStableHLOOp_injective_on_canonical`, `parseFuncOp_roundtrip`, `ppFuncOp_injective_on_canonical`), together with lowerer canonicality and roundtrip corollaries (`PTXLowerProofs.lowerKind_canonical`/`lowerKind_roundtrip`, `MetalLowerProofs.lowerKind_canonical`/`lowerKind_roundtrip`, `MLIRGPU.lowerStableHLODeclFunc_canonical`/`lowerStableHLODeclFunc_roundtrip`, and `lowerToStableHLO_canonical`/`lowerToStableHLO_roundtrip`) under explicit lexical identifier-validity premises. The axiom audit contains 835 unique theorems (`830` `LeanNative.*` plus `5` `ConLeche`/`TurboLean.ElabAudit`). Executable kernel roundtrip guards also cover representative live lowerer outputs, including M9/M10 inputs. Uncovered constructors (`StableHLOOp.dynamicSlice`/`reduce`, non-scalar PTX atomic reductions, general LLVM instruction/function parser roundtrips) and remaining direct string emitters in `LLVM.lean`, `MLIRGPU.lean`, `Metal.lean`, `Hybrid.lean`, and `CoreCLI.lean` remain open under `G4`.
   - **CI impact planning implemented**: `scripts/ci_impact_plan.py --self-test` exercises real Git histories, documentation boundaries, deletions, renames, file modes, immutable-tree digests, and forced full runs. Both workflows use impact decisions and digest-keyed build caches. Successful-verification receipt reuse is not implemented.
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

## Roadmap Status Ledger (`R0`)

> **Status at `911febf` (`roadmap-complete`, 2026-11-26).** This section used to list the open roadmap items. It now records, for each of them, what has landed (short sha and one clause) and what stays open, with the work-graph row or section that tracks it. Leaf status and order of work live in the work-graph table of [`HORIZONS.md`](./HORIZONS.md); where a row and a line here disagree, the row wins.

- **Priority 0 — Zygote CoW fork pool** *(landed on `main` before this branch)*: `lean/TurboLean/ZygoteFork.lean`, `lean/TurboLean/ZygoteWorker.lean` (split by command in S3b, `7ba6327`) and the POSIX runtime `crates/turbo-lean/src/zygote_fork_posix.lean` run `race_candidates` tactics and opt-in per-shard checks in quiesced POSIX `fork` children (`TURBO_LEAN_RACE_FORK_JOBS`, `TURBO_LEAN_ZYGOTE_FORK_SHARDS=1`); `closure_pool_digest` keys the worker pool by closure content rather than worktree path (`crates/turbo-lean/src/zygote/dispatch.rs` since S2); `ensure_prefix_outline_olean` emits the content-addressed prefix outline for a deep `--decl` (called from `crates/turbo-lean/src/check/single_decl.rs`).
- **`G1` — pluggable kernel and `csimp` attestation**
  - *Landed*: before this branch, `--kernel <auto|standard|con-leche|both>` with `con-leche` as an external binary (`#448`, `#449`), receipts binding `active_csimp_digest` (`#426`), and the M2 theorems proved over the `"OLEN"` model and documented as such (`#460`, `ad54090`). On this branch: the `csimp` / `unsafe` import policy decided before expensive work (P9: `95d34f4`, `54f4b0a`, `9152b62`, `af827da`); `csimp` posture bound through the existing cache keys (G1a: `0f407f0`, round 2 in `af827da`); `--kernel auto` selects the bundled `con-leche` when the toolchain matches (G1c: `9152b62`); an executable discriminator that pins the model parser's rejection of real `.olean` headers (G1b: `1278b76`).
  - *Open by design*: M2 over real `.olean` bytes through a direct `.olean` / `ConstantInfo` reader ([`OPEN_CHALLENGES.md`](./OPEN_CHALLENGES.md) B1; out of scope on this branch, row G1b), and `con-leche` compiled natively (H3).
- **`G2` — `HeaderPin`, CAS proof distillation and spec-auditor hardening**
  - *Landed*: before this branch, Stage A (`crates/turbo-lean/src/audit_spec.rs`) and Stage B (`#451`, `#452`). On this branch: strict `[audit_spec]` JSON (A1j: `ca38d1f`); the kernel-backed `audit-spec` witness (A2: `f4724bb`, round 2 `b8c05a2`); the CAS replay hit rate measured on recorded edit sequences (G2a: `8e01f27`, fix rounds `a3ad5f4`, `449b749`, `89e7abc`); G2b closed on its deleted branch: the warm-hit CAS expr replay landed on by default (`b29fcd1`), went opt-in under the H2 bench-delta rule (`449b749`), and was deleted once the `build`-path accept measurement showed about 15 ms per warm build for no benefit (`f4dfa82e`; row G2b). `--replay-cas-expr` remains the fail-closed replay.
- **`G3.1` & `G3.2` — broader `LCNF` coverage**
  - *Landed* on this branch: one proved lowering path, with the unproved second lowering deleted (L1: `e8a4c1a`, fix rounds `608df44`, `2c84fcc`); non-recursive calls proved under a function environment (L2: `420d1d1`); fuel-indexed recursion semantics and the L3 contract (L3, partial: `e7812fc`); the generated coverage matrix and its committed results, the external `Batteries` corpus included (H1.0a: `1b2b7d0`; H1.0b: `ddf3953`); `RealLCNFSemantics` run as an interpreter against stock Lean (H1.1: `8922a03`, `40275bc`); the H1 statement frozen and hash-pinned (H1.F: `f4365d9`); the mutant kill matrix, 59/60 killed (H1.4: `067b930`, `bff3f48`).
  - *Open*: the L3 recursion proofs (row L3), and the H1.0 accept, a CI job that emits the coverage JSON (row H1.0). The committed coverage results predate L1's bridge edits, so `python3 scripts/lcnf_coverage.py --json` fails its digest gate at this tip until they are re-measured.
  - *Open by design* (H3): closures and higher-order `.fvar` calls, `letrec`, signed `Int*`, runtime objects and full LLVM heap-op codegen. No mechanized upstream `LCNF` semantics exists to ground the source semantics in ([`HORIZONS.md`](./HORIZONS.md), "Verified compilers"), so H1.1 tests the in-repo one against Lean.
- **`G3.3` & `G4` — upstream target semantics and AST-to-text emission**
  - *Landed*: before this branch, the pinned bridge packages `verification/lean-mlir-bridge`, `verification/lnsym-bridge` and `verification/sail-riscv-bridge`, each with a sync check and a CI job. On this branch: the non-LLVM backends are labelled `[unverified tier]` in both drivers' `--help` (H1.F: `f4365d9`).
  - *Open by design* (H3): grounding production codegen in those upstream semantics, and routing production `LLVM` / `PTX` / `Metal` / `StableHLO` text emission through the proved Target-IR AST printers, in the order telemetry says the backends are used; until then the non-LLVM backends get no features (H1 rules). `G4`'s "≥ 50% LOC compression" target is parked ([`HORIZONS.md`](./HORIZONS.md), "Cleanup this implies").
- **`G5` — ecosystem differential conformance and mutant hygiene**
  - *Landed*: before this branch, 10,000-seed nightly `LCNF` alias fuzzing (C4x, `#472`) and the emitter mutant universe narrowed to the live `M1`–`M10` (`#454`). On this branch: a 250-program upstream C1 corpus chosen by the coverage matrix, run as the opt-in `--c1-upstream` leg of the nightly workflow (C1x: `3f5f90a`, `ccd20ff`, `5f0a30c`); pinned `Batteries` v4.35.0 as the opt-in external C2 driver of the nightly workflow (C2x: `1805b4b`).
  - *Open by design*: full 3-way case-vector execution of the upstream C1 programs (none of the 250 lowers with exported scalar entrypoints; [`CONFORMANCE_SUITE.md`](./CONFORMANCE_SUITE.md), Tier C1), and external packages beyond `Batteries` (`LeanSys`, `SciLean`, `ArkLib`).
