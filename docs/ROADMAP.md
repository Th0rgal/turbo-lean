# Track A / Track B, `Lean 4 -> Target IR` (`C1`–`C8`), & Next-Gen Native (`D0`–`D5`) status

Status of `turbo-lean` verification-boundary hardening (Track A), the completed
`LeanNative` `Lean 4 -> Target IR` formal verification program (`C1`–`C8`,
superseding the earlier `eth-act/clifv` / B2 ISA prototype), the Next-Gen
`D0`–`D5` roadmap (`Proof-Carrying LCNF`, `Unboxed Regions`, `Certifying
Stochastic Superoptimizer`, `Hardware-in-the-Loop Cost Autotuning`, and
`Zero-Alloc Stackless Async`), and open soundness PRs as of `main` at `092ffc5`
(after [#334](https://github.com/Th0rgal/turbo-lean/pull/334) `28a4384` and [#344](https://github.com/Th0rgal/turbo-lean/pull/344) `092ffc5`).
This is a status ledger, not a contract: the locked goals and validation
contracts remain [`roadmap/GOALS.md`](../roadmap/GOALS.md) and
[`roadmap/VALIDATION_CONTRACTS.md`](../roadmap/VALIDATION_CONTRACTS.md), which
this file does not modify. SHAs below are the recorded merge commits or branch
tips; they are not restated guarantees.

## Formal Verification Boundary (`Lean 4 -> Target IR`)

- **Inside the formal boundary (`Lean 4 -> Target IR`)**: `LeanNative` targets
  end-to-end semantic refinement under `{propext, Quot.sound, Classical.choice}`
  (`0 sorryAx`) from `Compiler.LCNF` through `LNIR`, acceleration plugins
  (`@[simd]`, `@[gpu]`, `@[tpu]`, `@[superopt]`), `HeapObj` / `lean.h`
  reference-counting layout, and typed backend AST lowering up to **LLVM IR**,
  **NVIDIA CUDA PTX**, **Apple Metal MSL**, **Google TPU StableHLO / Pallas**,
  and **C99 ABI**.
- **Trusted downstream (`Target IR -> Silicon`)**: Vendor backend compilers and
  runtimes (`clang`/LLVM, `ptxas`/CUDA, Apple's Metal compiler, XLA/Pallas, the
  C compiler, OS loader, and hardware) are part of the Trusted Computing Base;
  no ISA or binary machine-code verification is performed below Target IR, and
  `turbo-lean` carries zero `eth-act/clifv` repository or CI dependencies (`C1`).

## Track A — Verification-boundary hardening (merged on `main`)

| Step | PR | Merge commit | What landed |
| --- | --- | --- | --- |
| A0a | [#288](https://github.com/Th0rgal/turbo-lean/pull/288) | `02c0b30` | Pin theorem statements from built kernel declarations. |
| A0b | [#294](https://github.com/Th0rgal/turbo-lean/pull/294) | `ceebe65` | Bound daemon lifetime and honor per-check timeouts. |
| A0c | [#291](https://github.com/Th0rgal/turbo-lean/pull/291) | `63457a2` | Auto-worktree-link opt-out and strict remote-telemetry opt-in. |
| A0d | [#309](https://github.com/Th0rgal/turbo-lean/pull/309) | `80eaf32` | `check --decl` declaration-discovery parity against the self-contained fixture corpus (`crates/turbo-lean/tests/fixtures/check_decl_corpus/`). |
| A0e | [#303](https://github.com/Th0rgal/turbo-lean/pull/303) | `2a8939e` | Paired external `clifv` benchmark harness (historical; removed from tree in `C1`). |
| A0f / S1 | [#322](https://github.com/Th0rgal/turbo-lean/pull/322) | `e1ff917` | Bind Zygote imported-environment cache to imported `.olean` bytes; content-verified closure memo. |
| A0g / S3 | [#308](https://github.com/Th0rgal/turbo-lean/pull/308) | `8658adc` | Pin verifier executables (`lean`, `lake`, `leanc`) to the installed toolchain (`outside_checkout`, `git >= 2.46`). |
| A0h / S5 | [#318](https://github.com/Th0rgal/turbo-lean/pull/318) | `f68e250` | Lexical declaration-identity resolution (`--decl-identity`), sandboxed probes, and `statement-v1` `kernel_type_hash` attestation. |
| A0i / S6 | [#301](https://github.com/Th0rgal/turbo-lean/pull/301) | `e1bb46c` | Enforce Lean option policy at verification boundaries and independent `Kernel.Environment.replay` on worker/compiled declarations. |
| Docs / Boundary | [#325](https://github.com/Th0rgal/turbo-lean/pull/325) | `a83cd47` | Honest Proven vs. Tested vs. Trusted assurance boundary and Track A/B ledger. |
| Lake inputs | [#317](https://github.com/Th0rgal/turbo-lean/pull/317) | `1277fc6` | Support Lake's declarative file inputs (`input_dir` / `input_file` + `needs`). |
| P0-4 import digests | [#312](https://github.com/Th0rgal/turbo-lean/pull/312) | `2cd99ea` | Pin import artifact digests in the verified-sources manifest. |
| P0-1 `--decl` sorry gate | [#313](https://github.com/Th0rgal/turbo-lean/pull/313) | `61befe4` | Never verify or cache a `--decl` target that uses `sorry`. |
| CAS crash durability | [#321](https://github.com/Th0rgal/turbo-lean/pull/321) | `8768d47` | Crash-durable blob/marker publication and stable singleflight lock inodes. |
| Untrusted write-containment | [#323](https://github.com/Th0rgal/turbo-lean/pull/323) | `048ff6d` | Skip untrusted write-containment test only when the toolchain is missing. |
| Lake v4.35.0 `.trace` parity | [#324](https://github.com/Th0rgal/turbo-lean/pull/324) | `1e6922f` | Restore bit-exact Lake v4.35.0 `.trace`, missing-`.c` outputs, and `precompileModules` parity. |
| Toolchain & warm `.olean` gate | [#341](https://github.com/Th0rgal/turbo-lean/pull/341) | `7a08c45` | Fail-closed toolchain gate, warm `.olean` adoption, and target-cone scoping. |
| Critical-path scheduler & audit | [#344](https://github.com/Th0rgal/turbo-lean/pull/344) | `092ffc5` | Dynamic critical-path module scheduler and concurrent micro-batched audit. |

## Track B — Merged infrastructure & historical baselines

| Item | State | Where |
| --- | --- | --- |
| B0 shadow-semantics checker and allowlist ratchet | **Merged** [#296](https://github.com/Th0rgal/turbo-lean/pull/296) `0212d86` (allowlist **emptied** in [#332](https://github.com/Th0rgal/turbo-lean/pull/332) `946cfe9`) | [`docs/SHADOW_SEMANTICS.md`](SHADOW_SEMANTICS.md), `scripts/check_shadow_semantics.lean`, `scripts/shadow_allowlist.json` (`0` entries). Runs in CI; `main` has no branch protection ruleset yet. |
| B-3 emitter mutation runner | **Merged** [#293](https://github.com/Th0rgal/turbo-lean/pull/293) `1196038` (**`10/10` active mutants killed** in [#334](https://github.com/Th0rgal/turbo-lean/pull/334) `28a4384`) | `scripts/emitter_mutants.py` + `scripts/emitter_mutants.json` (`llvm`/`mlir`/`ptx`/`metal`/`c-abi`, `M1..M10` killed + `M11` N/A). Unit-tested on PRs; full suite runs on `push`/`workflow_dispatch`. |
| D1 step 5a (`HeapObj` contract + regressions) | **Merged** [#292](https://github.com/Th0rgal/turbo-lean/pull/292) `6e347f9` | [`docs/HEAPOBJ_CONTRACT.md`](HEAPOBJ_CONTRACT.md) + `lean/LeanNative/Tests/HeapObjContract.lean`. |
| D1 step 5b (unified `objFields` / `scalarFields`) | **Merged** [#300](https://github.com/Th0rgal/turbo-lean/pull/300) `210f1df` (**`54/54` PASS** in [#331](https://github.com/Th0rgal/turbo-lean/pull/331) `2896cfd`) | Unified `HeapObj {id, tag, objFields, scalarFields}`, `UBError.fuelExhausted`, worklist `decRefValsFuel`/`decRefObjFuel`, `SymExecState.symExhausted`, guarded LLVM heap codegen, and `lean/LeanNative/Tests/HeapObj5b.lean` (`0 XFAIL`, `0 UNCOVERED`). |
| Historical B2 `LNIR -> CLIF -> AArch64` (`collatz_steps`) | **Superseded & removed in `C1`** (landed in [#326](https://github.com/Th0rgal/turbo-lean/pull/326) `93f3e9f`, removed in [#327](https://github.com/Th0rgal/turbo-lean/pull/327) `c98ac64`) | Removed `require fv` (`clifv`), `lean/LeanNative/Backend/Clif.lean` (`compile-clif`), `research/b2-*`, `scripts/check_b2_source_identity.py`, `scripts/*bench_clifv*`, `docs/BENCH_CLIFV.md`, and `.github/workflows/{b2,bench-clifv}.yml` in favor of the `Lean 4 -> Target IR` boundary (`C1`–`C8`). |
| B1 in-repo stand-in semantics | **Superseded & closed** ([#284](https://github.com/Th0rgal/turbo-lean/pull/284) `48f9f25`) | Superseded and closed in `C2` ([#329](https://github.com/Th0rgal/turbo-lean/pull/329), [#330](https://github.com/Th0rgal/turbo-lean/pull/330), [#332](https://github.com/Th0rgal/turbo-lean/pull/332)). |

## `Lean 4 -> Target IR` Roadmap (`C1`–`C8` — Merged on `main`)

All eight milestones of the `Lean 4 -> Target IR` formal verification roadmap are merged on `main` (`0 sorryAx`, `0` shadow-allowlist entries, `10/10` active B-3 emitter mutants killed):

| Milestone | Status & Merge commits | Key deliverables & verified theorems |
| --- | --- | --- |
| **`C1`** | **Merged** [#327](https://github.com/Th0rgal/turbo-lean/pull/327) `c98ac64` | Decoupled `clifv` Lake/CI/bench/B2 dependencies, locked the `Lean 4 -> Target IR` formal boundary in `README.md`, and recorded `C1`–`C8` in `docs/ROADMAP.md`. |
| **`C2`** | **Merged** [#329](https://github.com/Th0rgal/turbo-lean/pull/329) `c973a84`, [#330](https://github.com/Th0rgal/turbo-lean/pull/330) `e5220ec`, [#332](https://github.com/Th0rgal/turbo-lean/pull/332) `946cfe9` | Typed Target-IR ASTs with independent operational semantics — `LLVMAst` (`BitVec` + poison), `PTXAst` / `MetalAst` (SIMT warp/thread execution), and `StableHLOAst` — paired with 1:1 structural pretty-printers, `0` shadow-allowlist entries (`scripts/shadow_allowlist.json`), and closure of draft [#284](https://github.com/Th0rgal/turbo-lean/pull/284). |
| **`C3`** | **Merged** [#336](https://github.com/Th0rgal/turbo-lean/pull/336) `6edf174` (`C3a`), [#334](https://github.com/Th0rgal/turbo-lean/pull/334) `28a4384` (`C3b`) | Kernel-checked Target-IR lowering soundness (`lowerToLLVM_sound`, `lowerToStableHLO_sound`, `lowerToPTX_sound`, `lowerToMetal_sound` + `GPUEmitterMutantProofs`) audited in `AxiomAudit.lean` (`0 sorryAx`), raising `scripts/emitter_mutants.py` kill rate to **`10/10` (`100%`)** applicable mutants (`M1..M10`). |
| **`C4`** | **Merged** [#337](https://github.com/Th0rgal/turbo-lean/pull/337) `55f0ef1` | Real `Lean.Compiler.LCNF -> LNIR` bridge soundness (`lowerRealLCNFCode_sound`, `lowerRealLCNFDecl_sound` in `lean/LeanNative/Proofs/RealLCNFBridgeProofs.lean`) over upstream `Lean.Compiler.LCNF` declarations. |
| **`C5`** | **Merged** [#338](https://github.com/Th0rgal/turbo-lean/pull/338) `e5a62fb` | `symbolicCodeRefines_sound` & `symbolicValidatedDeclOpt_sound` (`SymbolicTVRefinesSoundness.lean`), `symExecCode_pureU64_denotes` & `symExecCode_pureU64_eval_eq` (`SymbolicTVCodeSoundness.lean`), `validateTranslationDeclSound_of_passed` (`SymbolicTVSoundness.lean`), and kernel-checked `@[superopt]` (`checkSuperoptScalarVerified_sound`, `superoptDecl_sound`, `superoptModule_sound` in `SuperoptSoundness.lean`). |
| **`C6`** | **Merged** [#331](https://github.com/Th0rgal/turbo-lean/pull/331) `2896cfd` | Closed out `docs/HEAPOBJ_CONTRACT.md` & `lean/LeanNative/Tests/HeapObjContract.lean` to **`54/54` PASS** (`0 XFAIL`, `0 UNCOVERED`) with formal `lean.h` ABI header/tag/boxing and COW RC preservation proofs (`HeapObjAbiProofs.lean`). |
| **`C7`** | **Merged** [#328](https://github.com/Th0rgal/turbo-lean/pull/328) `70f5480`, [#333](https://github.com/Th0rgal/turbo-lean/pull/333) `72d713b` (`R2a`) | Formalized C99 ABI marshaling, hybrid CPU/GPU/TPU host-device buffer ownership (`validateHybridDispatch_sound`), and zero-copy slice IO C-ABI marshaling (`validateZeroCopySliceIoCall_sound`, `execZeroCopySliceIoHostCall_ok_sound` in `HybridCAbiProofs.lean`). |
| **`C8`** | **Merged** [#335](https://github.com/Th0rgal/turbo-lean/pull/335) `5640d7c` | Verified closure defunctionalization (`defunctionalizeClosure_sound`), general ADT match lowering (`lowerAdtMatch_sound`), checked slice views/folds (`lowerSliceFold_sound`), and `parFor` loop fusion (`fuseParForKernels_sound`). |

## Next-Gen Verified Native & Superoptimization Roadmap (`D0`–`D5`)

Building on the completed `C1`–`C8` `Lean 4 -> Target IR` foundation, Tracks `D0`–`D5` eliminate remaining boxing/RC, bounds-check, async-closure, and static cost-model overhead while keeping external search/autotuning tools strictly untrusted behind `SpeculativeGate` (`0 sorryAx`, `0 native_decide`, `0` solver/LLM TCB, 100% deterministic `.tlpack`-cached builds, `ΔE2E >= 1%` Amdahl ratchet):

| Track | Scope & Module Ownership | Key deliverables & acceptance gates |
| --- | --- | --- |
| **`D0`** | Roadmap & Assurance Sync (`docs/ROADMAP.md`, `README.md`) | Record `C1`–`C8` completion (`437` unique `AxiomAudit`-verified theorems, `10/10` B-3 emitter mutant kills, `0` shadow-allowlist entries) and lock `D1`–`D5` scope and module boundaries (`scripts/sync_docs_inventory.py --check` green). |
| **`D1`** | Proof-Carrying LCNF (`lean/LeanNative/Frontend/ProofRetention.lean`) | Before `.mono` proof erasure, extract `Prop` invariants (`i < n`, pointer alignment, slice disjointness, exclusivity) as `LNIR` refinement facts; statically discharge `lean_is_exclusive` branches and emit verified `noalias`/`nsw`/`nuw` flags on `LLVMAst` plus bounds-free `PTXAst`/`MetalAst` loads with kernel-checked refinement proofs in `AxiomAudit.lean`. |
| **`D2`** | Unboxed Regions & Thread-Local Ownership (`lean/LeanNative/IR/UnboxedRegion.lean`, `Transform/OwnershipRC.lean`) | Add flat header-free `@[unboxed_region]` `repr(C)` structs, borrowed slices, and portable SIMD vector types; extend `OwnershipRC.lean` with single-owner and sendable escape proofs to eliminate 8-byte `lean_object` RC headers and `lean_mark_mt` atomic RC traffic. |
| **`D3`** | Certifying Stochastic Superoptimizer (`lean/LeanNative/Transform/StochasticCert.lean`, `turbo-lean superopt-evolve`) | Offline/CI evolutionary rewrite proposer pairing untrusted LLM/`egglog` search with `1.4B states/s` `fast-check` counterexample falsification behind `SpeculativeGate`, emitting deterministic Lean kernel proof certificates (`VerifiedExprRule` / `SymbolicTV` witness / `LoopScheduleSpec`) into `.tlpack` CAS (`0` build/runtime non-determinism, `0` external solver TCB). |
| **`D4`** | Hardware-in-the-Loop Cost Autotuning (`Transform/CostAutotune.lean` / `D3` profile calibration) | Replace static `HardwareCostProfile` guesses during `D3` offline search with measured wall-clock microbenchmarks across Zen 5 CPU, CUDA (`rtx4090`), and Scaleway targets; enforce `AGENTS.md` Rule 7 by pruning any candidate rule failing `ΔE2E >= 1%` on the canonical corpus. |
| **`D5`** | Zero-Alloc Stackless Async (`lean/LeanNative/Transform/AsyncStateMachine.lean`) | Lower non-escaping `IO` / `lean-sys` event loops and coroutines into flat unboxed state-machine structs with `0` heap-allocated RC closures per poll and kernel-checked state-transition equivalence. |

## Open soundness and parity PRs

| PR | Head | Title |
| --- | --- | --- |
| [#320](https://github.com/Th0rgal/turbo-lean/pull/320) | `3ff77b4` | fix(fastcheck): certify counterexamples only via statement re-evaluation |
| [#340](https://github.com/Th0rgal/turbo-lean/pull/340) | `28bd465` | feat(cli): Boat/Orb toolchain gate, file-target build, check --emit-olean, and mtime-immune hydrate-traces |
| [#342](https://github.com/Th0rgal/turbo-lean/pull/342) | `ce27407` | feat(wave8): proof-only early cutoff, impact, check --allow-sorry, cone export, and gate |
| [#343](https://github.com/Th0rgal/turbo-lean/pull/343) | `b4726cc` | feat(pr-verify): fast proof-only overlay, prebuilt dep closure, and disposable snapshot seeding |
