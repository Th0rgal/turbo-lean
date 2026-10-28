# Orb & Turbo-Lean Trustworthy Shared-Lean Roadmap Alignment (`P0`–`P7` ⟷ `M1`–`M6`)

This document maps the joint **Orb Trustworthy Shared-Lean Roadmap (`P0`–`P7`)** to the public **`Th0rgal/turbo-lean` Roadmap (`M1`–`M6`)** at baseline revision `fbd36764a27c62705c825744d9f0a5ca7523811e` (with `Th0rgal/orb` at `e6b3283eff02e644660a79acc8b0a6d4c6a14331`).

## 1. Milestone & Phase Dependency Mapping

| Orb Phase | Turbo-Lean Milestone | Shared Deliverable & Verification Gate | Honest Status Classification |
| :--- | :--- | :--- | :--- |
| **P0: Honest Claims & Fail-Closed Trust Boundary** | **M1 (`audit-spec` v2 & Anti-Cheat)**, **M3 (`HeaderPin`)** | Fail-closed CLI target/input/tool handling; proper `macosArm64` target; atomic artifact publication; archive/object/WASM header+symbol+platform verification; branch-accurate provenance (`VerifiedKernelProof`, `TranslationValidated`, `Tested`, `Assumed`, `Unsupported`); negative fault-injection suite. | Implemented & verified in this PR (`P0`) |
| **P1: Real Independent Conformance & Trustworthy Harness** | **M1 (`C1` Conformance)**, **M6 (`C4` Fuzzing & Mutants)** | Multi-engine differential runner executing (1) stock Lean (`lean -c`), (2) actual `LNIR` operational interpreter (`eval-lnir`) on frontend-lowered IR (`lean-native emit-lnir`), (3) extracted freestanding C, and (4) `LeanNative` LLVM native/WASM binaries on identical inputs; cryptographic per-case receipts; missing engine = failure; engine & harness mutation tests. | Core C1/C4 3-engine harness hardened in this PR; full Orb/LeanSys export corpus & host-wrapper matrix in Orb P1 PR |
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
