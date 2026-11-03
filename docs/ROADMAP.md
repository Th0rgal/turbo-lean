# Track A / Track B & `Lean 4 -> Target IR` (`C1`–`C8`) status

Status of `turbo-lean` verification-boundary hardening (Track A), the `LeanNative`
`Lean 4 -> Target IR` formal verification program (`C1`–`C8`, superseding the
earlier `eth-act/clifv` / B2 ISA prototype), and open soundness PRs as of `main`
at `1277fc6` (after [#325](https://github.com/Th0rgal/turbo-lean/pull/325)
`a83cd47` and [#317](https://github.com/Th0rgal/turbo-lean/pull/317) `1277fc6`).
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

## Track B — Merged infrastructure & historical baselines

| Item | State | Where |
| --- | --- | --- |
| B0 shadow-semantics checker and allowlist ratchet | **Merged** [#296](https://github.com/Th0rgal/turbo-lean/pull/296) `0212d86` | [`docs/SHADOW_SEMANTICS.md`](SHADOW_SEMANTICS.md), `scripts/check_shadow_semantics.lean`, `scripts/shadow_allowlist.json` (emptied in `C2`). Runs in CI; `main` has no branch protection ruleset yet. |
| B-3 emitter mutation runner | **Merged** [#293](https://github.com/Th0rgal/turbo-lean/pull/293) `1196038` | `scripts/emitter_mutants.py` + `scripts/emitter_mutants.json` (`llvm`/`mlir`/`ptx`/`metal`/`c-abi`, `M1..M11`: 10 applicable mutants + `M11` N/A). Unit-tested on PRs; full suite runs on `push`/`workflow_dispatch`. |
| D1 step 5a (`HeapObj` contract + regressions) | **Merged** [#292](https://github.com/Th0rgal/turbo-lean/pull/292) `6e347f9` | [`docs/HEAPOBJ_CONTRACT.md`](HEAPOBJ_CONTRACT.md) + `lean/LeanNative/Tests/HeapObjContract.lean`. |
| D1 step 5b (unified `objFields` / `scalarFields`) | **Merged** [#300](https://github.com/Th0rgal/turbo-lean/pull/300) `210f1df` | Unified `HeapObj {id, tag, objFields, scalarFields}`, `UBError.fuelExhausted`, worklist `decRefValsFuel`/`decRefObjFuel`, `SymExecState.symExhausted`, guarded LLVM heap codegen, and `lean/LeanNative/Tests/HeapObj5b.lean` (**47 pass**, **1 XFAIL** `codegen_projection_guarded_field_load`, **6 UNCOVERED** clauses; closed out to **54/54 PASS** in `C6`). |
| Historical B2 `LNIR -> CLIF -> AArch64` (`collatz_steps`) | **Superseded & removed in `C1`** (landed in [#326](https://github.com/Th0rgal/turbo-lean/pull/326) `93f3e9f`) | Removed `require fv` (`clifv`), `lean/LeanNative/Backend/Clif.lean` (`compile-clif`), `research/b2-*`, `scripts/check_b2_source_identity.py`, `scripts/*bench_clifv*`, `docs/BENCH_CLIFV.md`, and `.github/workflows/{b2,bench-clifv}.yml` in favor of the `Lean 4 -> Target IR` boundary (`C1`–`C8`). |
| B1 in-repo stand-in semantics | **Held**, open draft [#284](https://github.com/Th0rgal/turbo-lean/pull/284) `48f9f25` | *HOLD: in-repo stand-in semantics (not upstream lean-mlir/LNSym/con-leche)*. Superseded and closed in `C2`. |

## `Lean 4 -> Target IR` Roadmap (`C1`–`C8`)

Replaced the earlier `clifv`-coupled follow-ups with the eight-step `Lean 4 -> Target IR`
formal verification roadmap:

| Milestone | Scope | Key deliverables & acceptance gates |
| --- | --- | --- |
| **`C1`** | Decouple `clifv` & lock Target-IR boundary | Drop external `clifv` Lake/CI/bench/B2 dependencies (`.github/workflows/{b2,bench-clifv}.yml`, `lean/lakefile.lean`, `lean/LeanNative/Backend/Clif.lean`, `research/b2-*`, `scripts/*clifv*`, `docs/BENCH_CLIFV.md`), lock the `Lean 4 -> Target IR` boundary in `README.md`, and record `C1`–`C8` in `docs/ROADMAP.md`. **In this PR.** |
| **`C2`** | Genuine Target IR ASTs & non-tautological operational semantics | Typed Target-IR ASTs with independent operational semantics — `LLVMAst` (`BitVec` + poison), `PTXAst` / `MetalAst` (SIMT warp/thread execution), and `StableHLOAst` — paired with 1:1 structural pretty-printers, zero `evalBinOp`/`evalUnaryOp` shadow delegation, an empty `scripts/shadow_allowlist.json`, and superseding/closing draft [#284](https://github.com/Th0rgal/turbo-lean/pull/284). |
| **`C3`** | Kernel-checked Target IR emitter soundness | Prove `lowerTo{LLVM,PTX,Metal,StableHLO}_sound` over the real production lowering passes, register every theorem in `lean/LeanNative/Proofs/AxiomAudit.lean` (`0 sorryAx`), and raise `scripts/emitter_mutants.py` empirical/formal kill rate from `1/10` to `>= 9/10` applicable mutants. |
| **`C4`** | Real `Lean.Compiler.LCNF -> LNIR` bridge soundness | Prove end-to-end lowering refinement across `lean/LeanNative/IR/Bridge.lean` and `lean/LeanNative/Proofs/LCNFBridgeProofs.lean` against real `Lean.Compiler.LCNF` declarations (retiring the in-repo `LCNF.evalLCNF` shadow bridge). |
| **`C5`** | General `SymbolicTV` & `@[superopt]` soundness | **In this PR.** `validateTranslationDeclSound_of_passed` (`lean/LeanNative/Proofs/SymbolicTVSoundness.lean`) discharges the recorded symbolic invariants of a passing `validateTranslationDecl`; pure-U64 normalizer soundness (`normSymExpr_pureU64_denotes`, `symEvalScalarRes_pureU64_sound`) and the kernel-checked superoptimizer (`checkSuperoptScalarVerified_sound`, `superoptDecl_sound`, `superoptModule_sound` in `lean/LeanNative/Proofs/SuperoptSoundness.lean`) are registered in `AxiomAudit.lean` (`0 sorryAx`). `TranslationValidated` stays the honest label for TV-only extended candidates (`ofHybridVerifiedContract`). |
| **`C6`** | Full `HeapObj` / `lean.h` ABI layout & RC preservation (`54/54` PASS) | Flip the final `XFAIL` (`codegen_projection_guarded_field_load`) and discharge all `6 UNCOVERED` clauses in `lean/LeanNative/Tests/HeapObjContract.lean` / [`docs/HEAPOBJ_CONTRACT.md`](HEAPOBJ_CONTRACT.md) (`47 pass + 1 XFAIL + 6 UNCOVERED -> 54/54 PASS`) with `lean.h` ABI layout and RC preservation proofs. |
| **`C7`** | Verified C99 ABI & CPU/GPU/TPU hybrid host-dispatch glue | Formalize and verify C99 ABI marshaling and host-device buffer/dispatch glue across `lean/LeanNative/Backend/Hybrid.lean` and `lean/LeanNative/Driver/CAbiEmit.lean`. |
| **`C8`** | Rich Lean 4 language coverage & verified loop fusion | Extend `lean/LeanNative/IR/` and `lean/LeanNative/Transform/Plugins.lean` with verified lowering and loop/kernel fusion for closures, general ADTs, `ByteArray`, and `FloatArray`. |

## Open soundness and parity PRs

None of these are on `main`. One-line scope is the PR title (`#317` merged to
`main` as `1277fc6` and is recorded under Track A above).

| PR | Head | Title |
| --- | --- | --- |
| [#312](https://github.com/Th0rgal/turbo-lean/pull/312) | `7c0962b` | fix: pin import artifact digests in verified-sources manifest (P0-4) |
| [#313](https://github.com/Th0rgal/turbo-lean/pull/313) | `8e66770` | fix(check): never verify or cache a `--decl` target that uses sorry (P0-1) |
| [#320](https://github.com/Th0rgal/turbo-lean/pull/320) | `6b282b3` | fix(fastcheck): certify counterexamples only via statement re-evaluation |
| [#321](https://github.com/Th0rgal/turbo-lean/pull/321) | `dbc0a5f` | fix(cas): crash-durable blob/marker publication and stable singleflight lock inodes |
| [#323](https://github.com/Th0rgal/turbo-lean/pull/323) | `54b9a81` | test(ws4): untrusted write-containment test skips only without the toolchain |
| [#324](https://github.com/Th0rgal/turbo-lean/pull/324) | `17edf04` | fix(module-builder): restore bit-exact Lake v4.35.0 `.trace`, missing-`.c` outputs, and precompileModules parity |

Held draft [#284](https://github.com/Th0rgal/turbo-lean/pull/284) (`48f9f25`) is
listed under Track B above and is slated to be superseded and closed in `C2`.
