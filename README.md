<p align="center">
  <img src="logo.svg" width="160" alt="turbo-lean" />
</p>

<h1 align="center">turbo-lean</h1>

<p align="center">
  <strong>Incremental verification, counterexample triage, and verified native/SIMD/GPU/TPU compilation for Lean 4.</strong>
</p>

`turbo-lean` unifies the incremental verification oracle (`TurboLean`) and the verified native compiler (`LeanNative`) on top of [`lean-sys`](https://github.com/Th0rgal/lean-sys):
1. **Sub-2ms Agent & Proof Verification Loops**: Verify edited theorems in **`~2 ms`** via warm `ZygoteWorker` checkpoints, reject false lemmas in **`< 1 ms`** on CPU SIMD / CUDA / Metal, and certify & triage counterexamples (`CandidateBug | SpecTooStrong | ReferenceDiscrepancy`) in **`~3 ns`** via in-process C-ABI gates.
2. **Verified Native Compilation & Acceleration Plugins (`@[simd]`, `@[gpu]`, `@[tpu]`)**: Lower pure Lean 4 / `LNIR` kernels to zero-copy C99/Rust FFI, AVX2 / AVX-512 / ARM64 NEON SIMD, NVIDIA CUDA PTX, Apple Metal 3.0 MSL, and Google Cloud TPU v6e (`StableHLO` / `Pallas`) with **203 kernel-checked refinement & soundness theorems** (`<!-- inventory:leannative_tight_specs -->120/120<!-- /inventory:leannative_tight_specs -->` tight specs in `LeanNative/Spec.lean`, `0 sorryAx`).
3. **Adversarial Anti-Reward-Hacking Gate**: Enforce in-kernel transitive axiom checks (`{propext, Quot.sound, Classical.choice}`), block macro-hidden `sorryAx` / `native_decide` / `extern` / `implemented_by` / `unsafe` bypasses, pin theorem statements in `< 10 µs`, and emit Ed25519/BLAKE3 receipts.

---

## Execution Modes (`check`, `eval`, and `LeanNative` Compilation)

1. **Adversarial Proof Verification (`turbo-lean check` / `ci-verify` / `pr-verify` / `agent-step`)**:
   - Audits untrusted theorem proofs in the Lean 4 kernel (`0 sorryAx`, `0 native_decide` / `Lean.ofReduceBool` / `Lean.trustCompiler`, no `unsafe`, `@[extern]`, `@[implemented_by]`, unapproved `axiom`, or nested inductive types) with `< 10 µs` `ConstantInfo.type` Statement Pinning.
   - Projects that accept the auxiliary axioms of `native_decide` / `bv_decide` in some proofs allow them in `turbo-lean.toml` (`[axioms] allow = ["*._native.native_decide.ax_*", "*._native.bv_decide.ax_*"]`, `*` globs, never `sorryAx` or `Lean.trustCompiler`); `check`, `agent-step`, trusted `ci-verify` and `pr-verify` (which reads the policy at `--base`) apply it. Audited compiler replacements use `[csimp] allow = ["MyModule.fast_eq"]` (theorem-name `*` globs); `pr-verify` passes only the policy at `--base` to the compiled auditor. Untrusted `ci-verify --base <git-ref>` uses the same policy revision; without `--base` it ignores checkout policy (explicit caller environment allowlists remain supported).
   - Only an edit confined to theorem proof bodies is checked per declaration (proof irrelevance). Any other edit (statement, `def`, instance, attribute, option, import, new or deleted file; for `--decl`, a change of that theorem's statement) makes `pr-verify`, `check` and `agent-step` re-check the edited modules and every module that imports them (`bwrap`-sandboxed native module compilation + `--audit-modules` in `pr-verify --mode untrusted`; `lake build` or `[lake] build_command` in `turbo-lean.toml` in trusted mode), so dependents in other files are checked; without a Lake config they refuse to pass.
   - Per-theorem zygote timeout: `check --timeout <secs>`, `[zygote] timeout_secs` in `turbo-lean.toml`, or `TURBO_LEAN_TIMEOUT_MS` (default 30 s); daemons and their HTTP clients follow it.
2. **Deterministic Evaluation (`turbo-lean eval <file.lean> [--lean-path ...] [--timeout-ms ...] [--verify-determinism]`)**:
   - Drop-in **`~660x–700x`-faster** replacement for `lean <file.lean>` on specification & mutation benchmarks (`rsgb`), preserving 100% of `MessageLog` diagnostics, captured `stdout`, and transitive `.olean` dependency hashes (`Law 6`).
3. **Verified Native & Accelerator Compilation (`lean/LeanNative` — `lean-native` / `lean-native-core`)**:
   - **Segregated Acceleration Plugins (`@[simd]`, `@[gpu]`, `@[tpu]`, `@[superopt]`)**: Rewrites and lowers `LNIR` (`letBind`, `incRef`, `decRef`, `call`, `parFor`, 256-bit EVM/UInt256 arithmetic) with Alive2-style symbolic translation validation (`SymbolicTV.lean`) and cost-guided superoptimization (`Superopt.lean`).
   - **Zero-Runtime C-ABI & Multi-Target Codegen**: Emits standalone `.c` / `.h` / `.rs` static libraries (`--emit-c-abi`), LLVM IR (`x86_64` AVX2/AVX-512, `aarch64` NEON), CUDA PTX (`sm_80`/`sm_90`), Apple Metal 3.0 (`.metal`), and Cloud TPU v6e (`StableHLO` MLIR & JAX `Pallas`).
   - **System Interactions via [`lean-sys`](https://github.com/Th0rgal/lean-sys)**: `LeanNative` focuses on pure compute and hardware acceleration. If your compiled native Lean 4 program needs to interact with the operating system (POSIX I/O, crash-atomic WAL/CAS storage, composite-key tables, `/dev/shm` shared-memory IPC, subprocess sandboxing, or HTTP/1.1 & JSON-RPC 2.0 servers with `0 import Lean` and `libleanrt.a`-only), pair it with [`lean-sys`](https://github.com/Th0rgal/lean-sys).

---

## Architecture & Soundness Guarantees

1. **In-Process C-ABI Oracle & Counterexample Triage (`libturbo_spec_cabi.a`)**
   - Links **<!-- inventory:turbo_cabi_exports -->76<!-- /inventory:turbo_cabi_exports --> zero-runtime C-ABI symbols** (<!-- inventory:turbo_cabi_breakdown -->`41 turbo_spec_*` + `26 leansys_*` + `9 leannative_*`/`lean_native_*`<!-- /inventory:turbo_cabi_breakdown -->) directly into the binary, verified at compile time via `nm` (`owner_count == 1`, `0` undefined symbols).
   - Evaluates candidate counterexamples in-process through `leannative_certify_cex_witnesses`, `leannative_fastcheck_rewrite_step`, and `leansys_verify_counterexample_triage`, classifying every falsified conjecture into `CandidateBug`, `SpecTooStrong` (vacuous precondition), or `ReferenceDiscrepancy` (domain hazard such as div/mod by zero or shift `>= 64`).
2. **Multi-Agent CAS & Memory Governor (`~/.cache/turbo-lean/`)**
   - Coalesces concurrent builds across worktrees via `flock` singleflight, shares immutable `BLAKE3`-addressed `.olean`/shard blobs via reflinks/hardlinks, and bounds RAM (`--max-memory-mb`) with `have`-block proof fission.
3. **Tight Formal Specifications (`0 sorryAx`)**
   - **<!-- inventory:turbo_tight_specs -->94/94<!-- /inventory:turbo_tight_specs --> tight specs** in [`lean/TurboLean/Spec.lean`](lean/TurboLean/Spec.lean), **<!-- inventory:leannative_tight_specs -->120/120<!-- /inventory:leannative_tight_specs --> tight specs** in [`lean/LeanNative/Spec.lean`](lean/LeanNative/Spec.lean), and **37/37 tight specs** in [`lean-sys`](https://github.com/Th0rgal/lean-sys).

---

## Assurance (Proven vs. Tested vs. Trusted)

Status on `main` (`0212d86`). For Track A, Track B, and open soundness PRs, see [`docs/ROADMAP.md`](docs/ROADMAP.md). Every proof listed below is audited in the Lean 4 kernel (`#verify_lean_native_axioms` at `lean/LeanNative/Proofs/AxiomAudit.lean:216-230`) against `allowedStandardAxioms = [propext, Quot.sound, Classical.choice]` (`:26-27`) and `forbiddenAxioms` (`sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler` at `:30-34`).

| Component | What is PROVEN (theorem + file) | What is only TESTED (test / CI step) | What is TRUSTED |
| :--- | :--- | :--- | :--- |
| **LNIR evaluator & IR passes** | `Val.beq_refl` (`lean/LeanNative/Semantics/Value.lean:46`) over `Val` (`:10`); `ScalarExprEquiv` (`lean/LeanNative/Semantics/Refinement.lean:11`), `ExprRefines` (`:31`), `CodeRefines` (`:78`) over `evalBinOp` (`lean/LeanNative/Semantics/Eval.lean:16`), `evalScalarExpr` (`:158`), `evalParKernelLoop` (`:505`), `evalCode` (`:554`); `applyRewriteTable_sound` (`lean/LeanNative/Proofs/PeepholeProofs.lean:679`); `optimizeEqSatCode_sound` (`lean/LeanNative/Transform/EqSat.lean:40`); `unboxTupleProj0_sound` / `unboxTupleProj1_sound` (`lean/LeanNative/Proofs/LoopOptProofs.lean:16,27`), `evalParKernelLoop_append` (`:407`); `scheduleStructuredLoop_sound` (`lean/LeanNative/Transform/LoopSchedule.lean:157`); `elideAndMutateRC_sound` (`lean/LeanNative/Transform/OwnershipRC.lean:144`); `lowerLCNFCode_sound` (`lean/LeanNative/Proofs/LCNFBridgeProofs.lean:109`, `EnvCorresponds` `:23`, `EvalOutcomeEquiv` `:31`) against in-repo `LCNF.evalLCNF` (`lean/LeanNative/IR/LCNF.lean:130`, which shares `evalBinOp`/`evalUnaryOp`; `scripts/shadow_allowlist.json:5-28`). | 3-way differential conformance (`scripts/verify_roadmap_contract.sh:167`, `.github/workflows/roadmap-conformance.yml:71`) and scalar/tuple/Stage-1D frontend tests (`scripts/test_scalar_frontend.py` at `.github/workflows/roadmap-conformance.yml:74`). | Adequacy of `evalCode` and in-repo `LCNF.evalLCNF` as models of upstream `Lean.Compiler.LCNF` and the Lean runtime (`lean.h`). |
| **Backends (`LLVM` / `MLIR` / `PTX` / `Metal` / `C-ABI` / `CLIF`)** | `lowerScalarToMLIR_sound` (`lean/LeanNative/Proofs/BackendProofs.lean:35`) and `lowerToLeanMLIR_sound` (`:125`) against the in-repo `LeanMLIR` model (`lean/LeanNative/Backend/Semantics.lean:17`, whose `denoteExpr` `:58` / `denote` `:102` delegate to `evalBinOp`/`evalUnaryOp`; `scripts/shadow_allowlist.json:30-52`, held in draft `#284`); `arm64_f128_kernel_refines_lnir` (`lean/LeanNative/Proofs/BackendProofs.lean:280`, via `runArm64_butterflyStepInstrs_inv` `:243` and `runArm64_instructions_f128_ntt_loop` `:259`) against the in-repo `LNSym` model (`lean/LeanNative/Backend/Semantics.lean:154`). **No text/object emitter theorem exists on `main`, and there is no `Backend/Clif.lean` on `main`** (see note below on `research/b12-feasibility`). | Actual text/object emitters — `emitLLVMModule` (`lean/LeanNative/Backend/LLVM.lean:1965`), `emitMLIRModule` / `emitPTXModule` / `emitStableHLOModule` / `emitTPUPallasModule` (`lean/LeanNative/Backend/MLIRGPU.lean:189,527,694,755`), `emitMetalModule` (`lean/LeanNative/Backend/Metal.lean:225`), `emitHybridHostGlue` / `emitMetalZeroCopyHostGlue` (`lean/LeanNative/Backend/Hybrid.lean:171,404`), and `verifyObjectBytesForTarget` (`lean/LeanNative/Driver/CAbiEmit.lean:312`) — are tested via `lean-native-core self-test` (`.github/workflows/ci.yml:82`) and 3-way ASan/UBSan conformance (`.github/workflows/roadmap-conformance.yml:20-74`). | `clang`/LLVM, MLIR, `ptxas`/CUDA, Metal, and C toolchains; external ISA/IR specs (x86_64, AArch64, PTX, MSL, StableHLO, System V / Darwin C ABI); header-only ELF/Mach-O/WASM checks (`lean/LeanNative/Driver/CAbiEmit.lean:300-301`). |
| **Translation validation (`SymbolicTV`)** | `normSymExpr_const_sound` (`lean/LeanNative/Proofs/SymbolicTV.lean:2965`), `checkSingleSample_of_codeRefines` (`:2971`), `checkConcreteSamples_of_codeRefines` (`:2985`), `sound_of_checkSingleSample_eq_true` (`:2999`), and `symbolicTV_refl_sound` (`:3013`). **General soundness of `validateTranslationDecl` (`:2867`) / `validateTranslationModule` (`:2941`) is not proven.** | Exercised by `lean-native-core verify-certs` and adversarial plugin gates (`scripts/verify_roadmap_contract.sh:143-164`) and `scripts/test_scalar_frontend.py` (`.github/workflows/roadmap-conformance.yml:74`); fuel-exhaustion fail-closed gaps C6.1/C6.3 remain XFAIL on `main` (`docs/HEAPOBJ_CONTRACT.md:313-315`). | Symbolic execution (`symExecDecl`, fuel 4 at `lean/LeanNative/Proofs/SymbolicTV.lean:2869`) and term normalization (`normSymExpr`) whenever accepting `TranslationValidated` rather than `--verified-kernel-only` (`scripts/verify_roadmap_contract.sh:150`). |
| **`HeapObj` contract (D1 step 5a, `#292`)** | No new theorem in step 5a; existing buffer RC lemmas `decRefBuf_one_frees_buffer`, `decRefBuf_none_error`, `incRefBuf_none_error` (`lean/LeanNative/Proofs/AxiomAudit.lean:153-154`). | Normative contract (`docs/HEAPOBJ_CONTRACT.md:1-25`) + 48 named `#guard` regressions in `lean/LeanNative/Tests/HeapObjContract.lean` (**28 pass**, **20 explicit XFAIL** awaiting draft `#300`, plus **6 UNCOVERED** clauses at `docs/HEAPOBJ_CONTRACT.md:259,266-315,357-364`), enforced structurally and via elaborated `MetaM` checks (`scripts/ci_verify.sh:26-108,121-230`). | Alignment between the split `HeapObj` model and Lean 4.35.0's `lean.h` object layout, `m_rc == 0` persistent objects, and `lean_box` rules (`docs/HEAPOBJ_CONTRACT.md:39-50,85-106`). |
| **Shadow-semantics checker (Track B0, `#296`)** | None (meta-level dependency/body/namespace checker, not a kernel theorem). | `scripts/check_shadow_semantics.lean` (`docs/SHADOW_SEMANTICS.md:3-37`), `scripts/shadow_inventory.json`, and `scripts/shadow_allowlist.json:1-54` run with `--self-test` in `.github/workflows/ci.yml:92-113`. **Advisory only today:** `main` has no branch protection or ruleset, so a failing check does not block merges (`docs/SHADOW_SEMANTICS.md:61-67`, `scripts/shadow_allowlist.json:3`). | Alpha-equivalence scope (eta-expanded, `let`-rewritten, or reordered-match copies are out of scope; `docs/SHADOW_SEMANTICS.md:17-18`) and manual review until a GitHub ruleset is enabled. |
| **Emitter mutation report (B-3, `#293`)** | None (empirical test-suite adequacy check; distinct from the 4 kernel-level spec mutants in `lean/LeanNative/Proofs/MutantSuite.lean`, `scripts/verify_roadmap_contract.sh:80-87`). | `scripts/emitter_mutants.py:1-42` + `scripts/emitter_mutants.json:1-130` (`M1..M11` across `llvm`/`mlir`/`ptx`/`metal`, checks `C1..C7`). Unit-tested on PRs (`.github/workflows/ci.yml:30-31`); full suite runs only on `push`/`workflow_dispatch` with `continue-on-error: true` (non-blocking, `.github/workflows/ci.yml:169-174`). | Adequacy of the hand-seeded mutation operators `M1..M11` as a proxy for emitter defect classes. |
| **Verification cache & kernel gate (`TurboLean`)** | Tight gate specs (`lean/TurboLean/Spec.lean`, `<!-- inventory:turbo_tight_specs -->94/94<!-- /inventory:turbo_tight_specs -->`); `inferType_sound`, `con_leche_verify_decl_sound`, `olean_mmap_bridge_sound` (`lean/TurboLean/ConLeche.lean:372,485,512`) and `header_pin_prevents_statement_spoofing`, `cas_proof_replay_sound` (`lean/TurboLean/ElabAudit.lean:115,128`) **over the self-contained `ConLeche` CIC model (`lean/TurboLean/ConLeche.lean:11`), not Lean 4's C++ kernel or real `.olean` files**. | In-kernel `inspectConstant` / `Lean.collectAxioms` (`lean/TurboLean/Inspector.lean:160,176`), canonical statement material (`lean/TurboLean/StatementHash.lean:10`, `#288`), kernel-audited shard fallback & final Zygote rejection (`run_audited_lean_shard` at `crates/turbo-lean/src/zygote.rs:2437`, `IMPORT_UNAVAILABLE_CODE` at `:4416`, `auditModuleSlice` at `lean/TurboLean/ZygoteWorker.lean:1232`, `#311`), effective-option cache keys (`applyEncodedLeanArgs` at `lean/TurboLean/ZygoteWorker.lean:196`, `eval-shm:v5` at `crates/turbo-lean/src/zygote.rs:4607`, `theorem-shard-v2:` at `crates/turbo-lean/src/lake_build.rs:742`, `http-shard-options-v1:` at `crates/turbo-lean/src/server.rs:1419`, `#305`), and stderr panic-scan provenance (`ZYGOTE_SCANNER_VERSION` / `panicked_since` at `crates/turbo-lean/src/zygote.rs:66,1029`, `#306`), tested via `cargo test --release` and self-verification (`.github/workflows/ci.yml:85,128-155`) plus `scripts/test_p0_trust_boundary.py` / `scripts/test_kernel_gate_audit.py` (`scripts/verify_roadmap_contract.sh:168-169`). | Rust host orchestrator (`crates/turbo-lean/`), `bwrap` sandbox, BLAKE3/Ed25519 receipt plumbing, filesystem/CAS durability, and open boundary items tracked in [`docs/ROADMAP.md`](docs/ROADMAP.md) (`#301`, `#308`, `#312`, `#313`, `#318`, `#322`). |
| **Trusted computing base (TCB)** | — | Toolchain & C-ABI symbol ownership checks (`nm` single-owner check in `crates/turbo-lean/build.rs`, `scripts/sync_docs_inventory.py:18-27`). | Lean 4.35.0 kernel & runtime (`lean/lean-toolchain:1`), axioms `[propext, Quot.sound, Classical.choice]` (`lean/LeanNative/Proofs/AxiomAudit.lean:26-27`), `elan`/Lake, Rust/`rustc`, `clang`/LLVM, OS kernel, and hardware. |

> **Note on CLIF / AArch64 (`research/b12-feasibility`, not on `main`):** Branch `research/b12-feasibility` (`5cda17d`, documented there in `research/B2-spec.md` and `research/B2-status.md`) carries an experimental `lean/LeanNative/Backend/Clif.lean` emitter and a Lean 4.34.1 proof (`B2.EndToEnd.collatz_to_arm`) composing upstream `clifv`'s `E2E.backend_correct_final_of_lower` (`FV/E2E/FinalDirect.lean:23`) for `collatz_steps`, plus generic subset/signature lemmas (`B2.Lowering.lower_in_subsetE`, `B2.Lowering.lower_sig`). Generic scalar-fragment (`F64`) simulation and safety remain open, and none of that branch is merged into `main`.

---

## CLI Usage

```bash
# 1. Incremental Build, Theorem Check & Deterministic Eval
turbo-lean build [target...] [--seed-shards] [--project-dir <dir>]
turbo-lean check <file-or-dir> [--decl <id>] [--jobs <N>] [--max-memory-mb <MB>]
turbo-lean eval <file.lean> [--lean-path <paths>] [--timeout-ms <ms>] [--verify-determinism]

# 2. Agent Loop, Fast-Check (with Counterexample Triage) & Spec Audit
turbo-lean agent-step <file.lean> [--decl <id>] [--max-memory-mb <MB>]
turbo-lean fast-check <file.lean|kernel.cu> [--decl <id>] [--samples <N>]
turbo-lean audit-spec <file.lean>

# 3. Native & Accelerator Compilation + Multi-Threaded Native Orchestrator (in `lean/`)
(cd lean && lake exe lean-native-core --target llvm|ptx|metal|mlir|c-abi <input.lean> -o <out>)
(cd lean && lake exe lean-native-core self-test)
(cd lean && lake exe turbo-lean-native self-test)

# 4. PR/CI Verification, Cryptographic Receipts & Portable CAS (.tlpack)
turbo-lean pr-verify [--base <git-ref>] [--mode untrusted|trusted] [--receipt <out.json>]
turbo-lean ci-verify [--base <git-ref>] [--mode untrusted|trusted] [--receipt <out.json>]
turbo-lean export -o cache.tlpack && turbo-lean import cache.tlpack

# 5. Telemetry & Local Agent Analytics
turbo-lean telemetry [status|enable|disable|local]
turbo-lean --no-telemetry check <file.lean>
```

---

## Telemetry & Privacy

- **Local-only by default**: Out of the box (`enabled = true`, `remote = false`, `mode = "metrics"`), `turbo-lean` records local timing, cache-hit, and token-compaction counters in `/dev/shm` (`turbo-lean analytics`) and `~/.cache/turbo-lean/telemetry/` without making any network requests or storing raw source blobs.
- **Opt-in remote reporting**: Remote metrics upload is disabled unless explicitly enabled via `turbo-lean telemetry enable`, `--telemetry opt-in` / `--telemetry remote`, `TURBO_LEAN_TELEMETRY=remote`, or `remote = true` in `[telemetry]`. A telemetry token alone does not enable it.
- **Existing installations**: Remote reporting now defaults off even if a token was already configured; existing explicit opt-ins still apply. CLI `check` and `fast-check` emit no telemetry in either mode. Emitting MCP tools resolve project consent from request `project_dir`, then server `mcp --project-dir`, then the input file's parent, then CWD.
- **Full disable**: Pass `--no-telemetry` (or `--telemetry off`), set `TURBO_LEAN_TELEMETRY=off` (`0`/`false`/`no`), run `turbo-lean telemetry disable` (persists to `~/.config/turbo-lean/config.toml`), or configure `<project_dir>/turbo-lean.toml`:
  ```toml
  [telemetry]
  enabled = false   # disables all local and remote telemetry
  remote = false    # keep false unless opting into remote reporting
  mode = "off"      # "off" | "local" | "metrics" | "full"
  ```

Telemetry consent precedence is defaults → hub JSON → user TOML → trusted project TOML → environment modes (`SANDBOXED_TELEMETRY_MODE`, `SANDBOXED_TELEMETRY`, `TURBO_LEAN_TELEMETRY`, in that order) → `TURBO_LEAN_TELEMETRY_REMOTE`. CLI `--telemetry` replaces `TURBO_LEAN_TELEMETRY`; `--no-telemetry` takes precedence and disables all emission. Presence of `TURBO_LEAN_NO_REMOTE_TELEMETRY` vetoes remote emission at every layer. `TURBO_LEAN_TRUST_PROJECT_TELEMETRY=0` and untrusted verification exclude project telemetry settings.

## Worktree artifact preservation

Pass the global `--no-auto-worktree-link` flag, set `TURBO_LEAN_NO_WORKTREE_LINK=1`, or set `[worktree] auto_link = false` in the nearest `turbo-lean.toml` (also accepts `.turbo-lean.toml`). Any opt-out wins; an environment false value cannot override the project opt-out. Without an opt-out, automatic artifact sharing remains enabled.

These controls suppress main-clone build/package copying and linking, build-output permission/inode normalization during CAS ingestion, and the entire explicit `worktree-dedup` operation (including package chmod/link/copy and cleanup). Shared CAS cache hits in build, CI/PR verification and module builds validate existing bytes without replacing files or regenerating module sidecars. Missing or different cached outputs fail with instructions to build with Lake first; opted-out native module builds also refuse cache misses. Staging can still copy bytes into the external CAS. Module builds apply the caller's project opt-out to external dependencies too. Under opt-out, stale imports are an error and must be rebuilt explicitly with Lake; turbo-lean does not auto-rebuild them. GC can still prune previously installed CAS hardlinks by inode when expiring tracked worktrees; opting out does not undo those installations.

---

## GitHub Action (`uses: Th0rgal/turbo-lean@main`)

```yaml
- name: Incremental Lean 4 PR Verification
  uses: Th0rgal/turbo-lean@main
  with:
    project-dir: "."
    mode: "pr-verify"
    trust-mode: "untrusted"
    disallow-statement-changes: "true"
    receipt-path: "receipt.json"
    verify-receipt: "true"
```

---

## Benchmarks

| Workload / Operation | Baseline `lake env lean` | `turbo-lean` | Speedup / Notes |
| :--- | ---: | ---: | :--- |
| **`lfglabs-dev/verity` (`Uint256.add_comm`, 1/53 decls)** | `3,587.5 ms` | **`2.80 ms`** | **`1,280x`** (warm `ZygoteWorker`) |
| **`lfglabs-dev/verity` (`pr-verify --base HEAD`, 9,275 shards)** | `9,999.4 ms` | **`23.89 ms`** | **`419x`** (full-suffix BLAKE3 + statement pinning) |
| **`verify-receipt` (695 files, 9,275 shards)** | `> 10,000 ms` | **`0.58 ms`** | **`17,390x`** |
| **In-Process C-ABI `FastCheck` & Counterexample Triage** | `40 µs` (IPC) | **`~0.003 µs` (`3 ns`)** | **`~13,000x`** vs JSON-RPC subprocess |
| **1M-State 256-Bit GPU `fast-check` (NVIDIA GB10)** | — | **`0.71 ms`** | **`1,410 M states/s`** (`CuDenote` on `dgx-spark`) |
| **293-Mutant × 10k-Tx GPU Campaign (NVIDIA GB10)** | — | **`2.97 ms`** | **`292 / 293` mutants killed (`99.7%`)** |

---

## Repository Structure

- [`lean/TurboLean/`](lean/TurboLean/) — Incremental verification specifications, multi-threaded native orchestrator (`Orchestrator.lean`), & C-ABI gates in [`PolicyGates.lean`](lean/TurboLean/PolicyGates.lean) ([`Kernel.lean`](lean/TurboLean/Kernel.lean) is an export alias), plus kernel tools (`Spec.lean`, `Assembler.lean`, `Inspector.lean`, `ZygoteWorker.lean`, `Reflection.lean`, `FastCheck.lean`).
- [`lean/LeanNative/`](lean/LeanNative/) — Verified `LNIR` native compiler, `@[simd]`/`@[gpu]`/`@[tpu]` plugins (`Transform/Plugins.lean`, `Superopt.lean`), semantics & 207 soundness theorems (`Semantics/Eval.lean`, `Proofs/`), and multi-backend codegen (`Backend/LLVM.lean`, `PTX.lean`, `Metal.lean`, `MLIR.lean`, `FastCheck.lean`).
- [`crates/turbo-lean/src/`](crates/turbo-lean/src/) — CLI & system orchestrator (`c_abi.rs` <!-- inventory:turbo_cabi_exports -->76<!-- /inventory:turbo_cabi_exports -->-symbol FFI bridge, `module_builder.rs` event-driven ready-queue DAG scheduler, `accelerators.rs` & `gpu_fastcheck.rs` multi-domain `UInt`/`BitVec`/`Word256`/`Nat` counterexample engines, `zygote.rs`, `splitter.rs`, `pr_verify.rs`, `mcp.rs`).
- [`roadmap/`](roadmap/README.md) — Autonomous research & verification roadmap separating North-Star technical goals ([`GOALS.md`](roadmap/GOALS.md)), cheat-proof theorem contracts ([`VALIDATION_CONTRACTS.md`](roadmap/VALIDATION_CONTRACTS.md)), 3-way non-FV differential conformance ([`CONFORMANCE_SUITE.md`](roadmap/CONFORMANCE_SUITE.md)), and Maxwell/Orb execution strategies ([`MAXWELL_STRATEGIES.md`](roadmap/MAXWELL_STRATEGIES.md)); see [`docs/ROADMAP.md`](docs/ROADMAP.md) for current Track A / Track B and open soundness PR status.
