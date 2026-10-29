# Orb & Turbo-Lean Trustworthy Shared-Lean Roadmap Alignment (`P0`–`P7` ⟷ `M1`–`M6`)

This document maps the joint **Orb Trustworthy Shared-Lean Roadmap (`P0`–`P7`)** to the public **`Th0rgal/turbo-lean` Roadmap (`M1`–`M6`)** at baseline revision `fbd36764a27c62705c825744d9f0a5ca7523811e` (with `Th0rgal/orb` at `e6b3283eff02e644660a79acc8b0a6d4c6a14331`).

## 1. Milestone & Phase Dependency Mapping

| Orb Phase | Turbo-Lean Milestone | Shared Deliverable & Verification Gate | Honest Status Classification |
| :--- | :--- | :--- | :--- |
| **P0: Honest Claims & Fail-Closed Trust Boundary** | **M1 (`audit-spec` v2 & Anti-Cheat)**, **M3 (`HeaderPin`)** | Fail-closed CLI target/input/tool handling; proper `macosArm64` target; atomic artifact publication; archive/object/WASM header+symbol+platform verification; branch-accurate provenance (`VerifiedKernelProof`, `TranslationValidated`, `Tested`, `Assumed`, `Unsupported`); negative fault-injection suite. | In progress; no phase acceptance. Partial implementation and local checks; exact-head review and all exit gates remain required. |
| **P1: Real Independent Conformance & Trustworthy Harness** | **M1 (`C1` Conformance)**, **M6 (`C4` Fuzzing & Mutants)** | Multi-engine differential runner executing (1) stock Lean (`lean -c`), (2) actual `LNIR` operational interpreter (`eval-lnir`) on frontend-lowered IR (`lean-native emit-lnir`), (3) extracted freestanding C, and (4) `LeanNative` LLVM native/WASM binaries on identical inputs; cryptographic per-case receipts; missing engine = failure; engine & harness mutation tests. | Scalar-only three-engine harness tested locally; full Orb/LeanSys export corpus, alias/RC/seqFor and host-wrapper matrix remain open. |
| **P2: Remove `orbKernel.ts` Duplication via Shared WASM** | Independent of M2/M4 (uses stock Lean extracted C $\to$ WASM first) | `orb_kernel.wasm` compiled from `shared/orb-spec/cabi/orb_kernel_unboxed.c`; generated TypeScript bindings in `orb/src/orbKernel.ts`; async bootstrap before app stores load; cross-client conformance across TS/WASM, Swift C, and Kotlin JNI. | Scheduled in Orb P2 PR |
| **P3: Qualify `LeanNative` on Real Targets** | **M4 (`Bridge.lean` + `EqSat`/`LoopSchedule`/`OwnershipRC`)**, **M5 (`Semantics.lean`)** | Scalar exports qualified first with optional passes disabled, then individually qualified passes; portable Android ARM64 baseline; optional `--wasm-simd128` (scalar default); real execution on `x86_64` Linux (`agent-core`), `aarch64` Linux (`dgx-spark`), `macos-arm64` Apple M2 (`macbook-air`), and `iPhone 13 mini Simulator`; physical iPhone 13 mini & Pixel 8 marked `BLOCKED_PHYSICAL_DEVICE`. | Scheduled in P3 PR; physical iPhone 13 mini & Pixel 8 `BLOCKED_PHYSICAL_DEVICE` |
| **P4: Compositional State-Machine & Arena ABI** | `LeanSys` / `OrbWire` Arena Contract | Generic `Machine<State,Event,Effect>` interface over `OrbWire` word+arena frames; versioned codecs; zero partial mutation on capacity error; host patch application tests. | Scheduled in Orb P4 PR |
| **P5 + P6: Paired Executable Lean Coverage & Stronger Meta-Specs** | **M1.4 (`audit-spec` v2.1)**, **M6 (`MutantSuite.lean`)** | Priority 1–7 domain state machines in `Orb.Kernel` + `Orb.Spec` paired with reachable traces and $\ge 3$ killed mutants per family (boundary, identity/alias, semantic/effect, plus stale/persistence/security). | Scheduled in Orb P5/P6 PRs |
| **P7: Measured Optimization** | **M5 (`LNSym` / NEON / SIMD)**, **M6 (Amdahl Ratchet)** | Eliminate whole-list replacements/rescans; batch ABI calls; benchmark cold start, streaming p50/p99, replay, memory, and huge unclosed fences against predeclared budgets. | Scheduled in P7 PR |

## 2. Provenance & Assurance Level Contract

Every transformation step (`PassStepCert`) and declaration certificate (`DeclCertSummary`) in `LeanNative` must carry the assurance level of the **actual branch executed at compile time**, never a static label attached to the pass name:

1. **`VerifiedKernelProof` (`L4`)**: The exact transformation function `runCode` executed on `d.body` is backed by a machine-checked Lean 4 theorem `∀ c, CodeRefines c (runCode c)` with `0 sorryAx`, verified by `Lean.collectAxioms`.
2. **`TranslationValidated` (`L3`)**: An extended rewrite candidate `candBody != vc.runCode d.body` was selected and accepted by `SymbolicTV.validateTranslationDecl` (symbolic + concrete evaluation equivalence), or verified by an executable translation validator.
3. **`Tested` (`L2`)**: The pass or lowering step is not covered by a kernel refinement proof or total translation validator, but passes the 3-way differential conformance suite on the target corpus.
4. **`Assumed` (`L1`)**: External FFI (`@[extern]`), hardware vendor intrinsics, or target compiler/linker lowering steps outside the mechanized IR boundary.
5. **`Unsupported` (`L0`)**: Construct or target feature is outside the supported subset and must fail closed during compilation.

## Current publication and evidence boundary

Static-library consumers needing a consistent library/header/binding set use
`compile-static-lib canonical --artifact-bundle /path/current -o /path/kernels.a --json`.
The returned `generation` is immutable and must be used for all files in one read
snapshot. One POSIX symlink rename publishes the generation; previous generations
remain available. The legacy output-path API replaces files individually and does
not claim a multi-file transaction. Missing `ln` or a failed archive/tool/pointer
step fails closed. Power-loss durability and remote filesystem rename semantics
are unqualified assumptions.

Audit relational recognition checks a conservative source application/equality
shape and scoped binders; it is not a kernel-AST proof of arbitrary Lean syntax.
Both anti-tautology and unused-parameter defaults remain enabled. Local test
receipts do not constitute target qualification or acceptance of P0–P7.

The local auditor override for validation scripts is `TURBO_AUDITOR_BIN`.
`TURBO_LEAN_BIN` is already used by the native module builder for its Lean
compiler executable; pointing it at the auditor incorrectly fails the toolchain
identity gate. Neither variable changes the cache-key acceptance policy.

Rust ABI generation emits declarations and FFI forwarding wrappers only. It no
longer injects independently implemented SNARK routines or substitutes scalar
zero/XOR bodies for unsupported IR. This removes an unvalidated execution path;
it does not qualify a Rust compiler backend. Frontend ingestion retains all
lowered declarations, including user exports ending in `_redArg`.

The `scripts/ci_verify.sh` check for
`lean_native_ntt_butterfly_fused_2layer_slice` is satisfied by the verified
pure-Lean `@[inline, export lean_native_ntt_butterfly_fused_2layer_slice]` C-ABI
kernel in `lean/LeanNative/Spec.lean` (`nttButterflyFused2LayerSliceC`), proved
equivalent to two sequential Radix-2 $\mathbb{F}_{2^{128}}$ LCH additive NTT
butterfly layers (`gf128_fused_2layer_butterfly_eq_sequential`, `0 sorryAx`),
compiled into `libturbo_spec_cabi.a`, and emitted via `emit-cabi-bindings` as a
pure FFI forwarding wrapper without inline Rust SIMD templates.

`bench-snark-kernels` explicitly returns `BLOCKED_MISSING_DEPENDENCY` and
`benchmarkExecuted=false`. Its former generated-name checks were not execution
or ISA performance evidence. ABI headers likewise declare only supplied kernel
signatures; unrelated handwritten image-kernel prototypes are not injected.

## P1 unsigned scalar frontend repair

The bridge recognizes `UInt8`, `UInt16`, `UInt32`, `UInt64`, `USize`, and `Bool`
casts, unary complements/negations, and binary primitives only by exact primitive
name and matching operand/result types (`canonicalUIntCastMask?` masks by
`min srcMask dstMask`, so both narrowing and widening clamp any unmasked 64-bit
representation, including target-aware 32-bit `USize` on `wasm32` and fail-closed
`USize` rejection on GPU targets). Narrow `UInt8` (`mask = 255`, `shiftMask = 7`),
`UInt16` (`mask = 65535`, `shiftMask = 15`), and `UInt32` (`mask = 4294967295`,
`shiftMask = 31`) operations explicitly mask operands, wrap `.add`/`.sub`/`.mul`
modulo $2^w$, mask shift counts modulo $w$ (and `.shl` results modulo $2^w$), and
preserve Lean 4 total division/modulo by zero (`x / 0 = 0`, `x % 0 = x`) across
`BridgeHelpers.lean`, `Eval.lean`, and `LLVM.lean`. Impure LCNF uses `UInt8` for
comparison results, so the bridge materializes numeric `0`/`1` from the
evaluator's `Bool` rather than mixing `Bool` and `UInt64` values, lowers nullary
enum types cleanly, and lowers internal scalar tuples (`Prod` / `MProd` / `PProd`
and non-recursive single-constructor scalar structs) without 63-bit tagged boxing
truncation. Frontend-ingested non-extern declarations carry `Tested`, not a claim
of a kernel proof of frontend correctness.

Unsupported LCNF constructs fail closed instead of fabricating placeholder IR,
while pure scalar join-point chains scale in $O(N)$:
1. Recursive join points (`lowerJoinPoint`) and unmapped or arity-mismatched
   join-point jumps (`lowerJmpInstr`) throw explicit bridge errors.
2. General self-recursion (tail, non-tail, partial application, recursive local
   functions, and module-level mutual recursion cycles) and unresolved external
   calls fail closed with zero artifact published.
3. Acyclic pure-scalar join points lower via $O(N)$ SSA/select DAG sharing
   (`collectDagOutcome` + `substituteJpTargetInOutcome` + `compressScalarCode`),
   avoiding $O(2^K)$ join-point cloning blowups on chained boolean guards, while
   fallback join-point splicing (`spliceJoinPointJmp` + `freshenJoinPointCode`)
   and helper inlining (`inlineLocalHelperCallsM` + `freshenClonedCont` +
   `flattenInlinedHelperBody`) perform simultaneous parallel parameter
   substitution and alpha-freshen bound `VarId`s across branches.
4. Runtime `Nat`, closures/higher-order `.fvar` calls, `.str` string literals,
   heap ADTs, `.setTag` constructor tag mutations, unintercepted `.isShared`,
   and non-tuple constructor payload `.alt` patterns all fail closed.

The scalar frontend suite (`scripts/test_scalar_frontend.py`, 11 test methods)
executes Stage 1B narrow-ABI/enum/`USize`/`wasm32` probes, 243 cast/branch probes,
162 small-width comparison probes, 336 narrow wrapping arithmetic/shift/div-by-zero
probes, multi-parameter join-point swap and nested tuple-returning helper-inlining
probes, and chained boolean join-point + heterogeneous tuple-helper (`Orb.Kernel`
`attributionStep` / `streamFenceStep`) probes through stock Lean, `LNIR`
(`eval-lnir` + `validate-tv`), and compiled LLVM binaries with 0 mismatches and
no Python result oracle, alongside fail-closed LCNF, `EvalBatch` fault-isolation,
and source boundary tests. Both `./scripts/ci_verify.sh` and
`./scripts/verify_roadmap_contract.sh` pass locally. Remaining open scope:
general recursive/loop (`seqFor`) lowering from LCNF, heap string/constructor
payload/closure support, full Orb/LeanSys export corpus conformance, alias/RC
heap mutation coverage, and multi-target/mobile hardware qualification.
