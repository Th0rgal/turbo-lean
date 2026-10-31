# Orb, `lean-sys` & Turbo-Lean Trustworthy Shared-Lean Roadmap Alignment (`P0`–`P7` ⟷ `M1`–`M6`)

This document maps the joint **Orb Trustworthy Shared-Lean Roadmap (`P0`–`P7`)**, **`Th0rgal/lean-sys`**, and the public **`Th0rgal/turbo-lean` Roadmap (`M1`–`M6`)** at audited revision **`Th0rgal/turbo-lean` `9e4a258` (`#316`; includes `#315` `1a5d89b`, `#303` `2a8939e`, `#310` `6d53683`, and merged Stage 1D `#280` `e585ba96f58cb06414ce5e3216f3ffc0ce235300`)** and **`Th0rgal/lean-sys` `c089f3e31dbd36f2bde2219913d5b9c90da670be`** (2026-10-31; supersedes `cac14f17` / `887354a` / `1498a54`). Orb documentation head is `3cf1318ed`; P1/P3 execution evidence remains pinned at Orb `3c70e5ada278a4e37e0180255f360aa2ff5fe86c`. **P0–P7 remain formally unaccepted.**

## 1. Milestone & Phase Dependency Mapping

| Orb Phase | Turbo-Lean Milestone | Shared Deliverable & Verification Gate | Honest Status Classification (`2026-10-31`) |
| :--- | :--- | :--- | :--- |
| **P0: Honest Claims, Trust Domains & Fail-Closed Boundary** | **M1 / M1.4 (`audit-spec` v2.1 & Anti-Cheat)**, **M3 (`HeaderPin`)** | Fail-closed CLI target/input/tool handling; proper `macosArm64` target; atomic artifact publication; Ed25519 trust domains (`trusted` vs `untrusted`), signed receipts & Lean C-ABI pack admission gate (`#264`, `#267`); in-kernel `.olean` soundness gate + Lake sidecar hash check + `bwrap` untrusted isolation (`#269`, `#276`); zero-redirect HTTPS, exact loopback parsing & env token confinement (`#272`); `pr-verify` plain-`lean` fallback `#print axioms`, `--base` `[axioms] allow` policy & non-local edit Lake escalation (`#275`); statement pinning from built kernel decls (`#288`), lakefile option invalidation (`#304`), origin-bound prebuild credentials (`#307`), Zygote worker hardening (`#310`), atomic CAS blob publication (`#315`), and staged DB/Zygote lock-free publication (`#316`). | **Merged across `turbo-lean` (`#263`–`#276`, `#288`–`#316`) and Orb (`#1396`); P0 remains formally unaccepted.** `94/94` (`TurboLean`) & `120/120` (`LeanNative`) tight specs and `76` C-ABI gates run in CI; `bwrap` is provisioned on both `push` and `pull_request` workflows; untrusted checkouts cannot enable remote telemetry via repo-local `turbo-lean.toml`. Kernel `ConstantInfo` delta-unfolding in `audit-spec` remains open. |
| **P1: Real Independent Conformance & Trustworthy Harness** | **M1 (`C1` Conformance)**, **M6 (`C4` Fuzzing & Mutants)** | Multi-engine differential runner executing (1) stock Lean (`lean -c`), (2) actual `LNIR` operational interpreter (`eval-lnir --cases-file`), (3) extracted freestanding C, and (4) `LeanNative` LLVM binaries on identical inputs; cryptographic per-case receipts; missing engine = failure; engine & harness mutation tests. | **Stage 1D (`#280`, `e585ba9`) & Orb `#1399` merged; blocking `roadmap-conformance.yml` added; P1 remains formally unaccepted.** In `turbo-lean`, `.github/workflows/roadmap-conformance.yml` enforces `scripts/verify_roadmap_contract.sh` (`--tier C1,C4 --fuzz-seeds 32 --asan --ubsan`) and `scripts/test_scalar_frontend.py` on push and PRs. In Orb, local qualification at Orb `3c70e5ada` / Turbo `e585ba9` / LeanSys `c089f3e3` passed all 128 public exports across 6 scalar engines (1044 cases, 5220 comparisons, 0 mismatches), loop/alias/RC (`live_objects == 0`), and 21 domain mutants across native + WASM; receipts remain unsigned local consistency records and 23 partial / 106 unconnected coverage entries remain open. |
| **P2: Remove `orbKernel.ts` Duplication via Shared WASM** | Independent of M2/M4 (uses stock Lean extracted C $\to$ WASM first) | `orb_kernel.wasm` compiled from `shared/orb-spec/cabi/orb_kernel_unboxed.c`; generated TypeScript bindings in `orb/src/orbKernel.ts`; async bootstrap before app stores load; cross-client conformance across TS/WASM, Swift C, and Kotlin JNI. | **Orb `#1398` merged (`b1e82330`); P2 remains formally unaccepted.** `orb_kernel.wasm` and generated TS bindings shipped with open coverage/caller gaps preserved (`coverage_registry.json` still `23 partial / 106 unconnected`). |
| **P3: Qualify `LeanNative` on Real Targets** | **M4 (`Bridge.lean` + `EqSat`/`LoopSchedule`/`OwnershipRC`)**, **M5 (`Semantics.lean`)** | Scalar exports qualified first with optional passes disabled, then individually qualified passes; portable Android ARM64 baseline; optional `--wasm-simd128` (scalar default); real execution on `x86_64` Linux (`agent-core`), `aarch64` Linux (`dgx-spark`), `macos-arm64` Apple M2 (`macbook-air`), and `iPhone 13 mini Simulator`; physical iPhone 13 mini & Pixel 8 marked `BLOCKED_PHYSICAL_DEVICE`. | **Local qualification recorded (`QUALIFIED_WITH_HONEST_DEVICE_BLOCKERS`, Orb `f8a62ab1` at execution head `3c70e5ada` / Turbo `e585ba9`); P3 remains formally unaccepted.** `Bridge.lean` is 348 LOC (`0` `.endsWith`) and `CoreCLI.lean` is 921 LOC. Real execution passed on Linux `x86_64`, `dgx-spark` Linux `aarch64`, Node WASM MVP/SIMD128/shipped module, and Linux-loaded Android `x86_64` JNI (`Tested` assurance, not a kernel proof). MacBook Air is `BLOCKED_HOST_UNREACHABLE`; physical iPhone 13 mini & Pixel 8 stay `BLOCKED_PHYSICAL_DEVICE`; iOS/macOS/Android-ARM64 remain cross-compile-only; repo-owned qualification driver, signed receipts, and production artifact switch remain open. |
| **P4: Compositional State-Machine, Storage & Arena ABI (`lean-sys`)** | `Th0rgal/lean-sys` (`v4.35.0`, `0 import Lean`) | Verified POSIX/CAS/WAL/ShmRing/HTTP/Landlock runtime (`45/45` tight specs, `33` C-ABI gates, `63`-LOC C shim) + generic `Machine<State,Event,Effect>` over `OrbWire` frames. | **`lean-sys` (`#2` `1498a54`, `#3` `c089f3e`) & Orb `#1420` (`f12e6076`) merged; P4 remains formally unaccepted.** 32-bit `Fd` preservation, `MAP_SHARED` `ShmRing` `fstat` bounds, Landlock, smuggling-safe HTTP/1.1, pure-Lean SHA-256/HMAC-SHA256, streaming WAL, immutable CAS, and `OrbWire` framing landed; full authoritative host caller wiring (`23 partial / 106 unconnected`) remains open. |
| **P5 + P6: Paired Executable Lean Coverage & Stronger Meta-Specs** | **M1.4 (`audit-spec` v2.1)**, **M6 (`MutantSuite.lean`)** | Priority 1–7 domain state machines in `Orb.Kernel` + `Orb.Spec` paired with reachable traces and $\ge 3$ killed mutants per family (boundary, identity/alias, semantic/effect, plus stale/persistence/security). | **`turbo-lean` `audit-spec` v2.1 + `MutantSuite.lean` and Orb `#1420` (`f12e6076`) merged; P5–P6 remain formally unaccepted.** Priority domain state machines and the 21-mutant (`7 × 3`) suite landed, while `shared/orb-spec/coverage_registry.json` remains `INCOMPLETE` (`23 partial / 106 unconnected`) pending end-to-end authoritative caller and cross-client adapter parity. |
| **P7: Measured Optimization & External Zero-Trust Pilots** | **M2 (`con-leche`)**, **M5 (`LNSym` / NEON / SIMD)**, **M6 (Ecosystem Pilots)** | Official `leanprover/con-leche` + external `comparator`/`lean4export` replay; `eth-act/clifv` (4,624 modules) & `init-e` (`evm.fast`) benchmarks; modular OSS library crates (`turbo-cas`, `turbo-lean-*`). | **Orb `#1439` (`e602e6ad`) & `#1419` and `turbo-lean` `#268`, `#275`, `#276`, `#303`, `#309` merged; P7 remains formally unaccepted.** Cross-client $O(N)$ checkpointed streaming + ISA-dispatched SIMD scanner in Orb and `clifv` warm single-decl check + `--decl` discovery parity + paired `clifv` build/check benchmark (`#275`, `#303`, `#309`) in `turbo-lean` are merged. Official `con-leche` vendoring, `--kernel` CLI wiring, OSS crate split, and `comparator` shadow pilot remain open. |

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
   tuple-returning `flattenInlinedHelperBody`, gated strictly to flat-scalar
   `d.retTy matches (.tuple _)` while nested tuples fail closed, so scalar
   declarations pay zero extra pass cost while branching flat-scalar tuple helpers
   inline under the 65,536-node cap without unlowered heap/tuple rejection) perform
   simultaneous parallel parameter substitution and alpha-freshen bound `VarId`s
   across branches.
4. Runtime `Nat`, closures/higher-order `.fvar` calls, `.str` string literals,
   heap ADTs outside the non-exported bounded tuple-carrying Stage 1D subset
   (`#280`: recursive/indexed ADTs, direct scalar-payload `sproj`/`sset` ADTs,
   `> 8`-field or non-tuple constructor payloads, and exported heap signatures),
   `.setTag` constructor tag mutations, `.uset`/`.sset` scalar heap mutations,
   `.isShared` outside Stage 1D object variables, signed `Int*`/`ISize` types,
   unmodeled `@[extern]` calls, nested tuples, and non-tuple constructor payload
   `.alt` patterns all fail closed (`compile-llvm` also rejects all Stage 1D heap
   ops fail closed).

The scalar frontend suite (`scripts/test_scalar_frontend.py`) executes Stage 1B
narrow-ABI/enum/`USize`/`wasm32` probes, 243 cast/branch probes, 162 small-width
comparison probes, 336 narrow wrapping arithmetic/shift/div-by-zero probes,
multi-parameter join-point swap and flat-scalar tuple-returning helper-inlining
probes, and chained boolean join-point + heterogeneous tuple-helper (`Orb.Kernel`
`attributionStep` / `streamFenceStep`) probes through stock Lean, `LNIR`
(`eval-lnir` + `validate-tv`), and compiled LLVM binaries with 0 mismatches and
no Python result oracle; it also runs Stage 1D tuple-carrying heap ADT / Perceus
RC probes (`#280`) 2-way across stock Lean (`lake env lean --run`) and `LNIR`
(`eval-lnir` + `validate-tv`, `live_objects == 0`) while asserting `compile-llvm`
and direct scalar-payload heap ADTs fail closed, alongside fail-closed LCNF,
`EvalBatch` fault-isolation, and source boundary tests. The mandatory NTT gate in
`scripts/ci_verify.sh` is satisfied by the
verified pure-Lean C-ABI kernel
`lean_native_ntt_butterfly_fused_2layer_slice`. `./scripts/ci_verify.sh` remains
the inventory/spec gate in `.github/workflows/ci.yml`. Differential conformance
runs in the blocking `.github/workflows/roadmap-conformance.yml` job via
`scripts/verify_roadmap_contract.sh` (`--tier C1,C4 --fuzz-seeds 32 --asan --ubsan`)
and `scripts/test_scalar_frontend.py`. ASan covers emitted scalar LLVM IR and the
C driver (Lean clang compile, two-step-probed system gcc link when the Lean
runtime lacks `libclang_rt.asan`), while UBSan covers only the C driver and link
runtime (`c_driver_and_link_runtime_only_not_llvm_ir`); neither claims LLVM-IR
UBSan coverage or full heap/loop qualification. Remaining open scope: 250+ upstream
`lean4/tests/lean/run` files, general recursive/loop (`seqFor`) lowering from
LCNF, heap string/constructor payload/closure support, signed `Int*`, full
Orb/LeanSys export corpus conformance inside this repository, alias/RC heap
mutation coverage beyond the Stage 1D subset, and multi-target/mobile hardware
qualification. `--tier C2` and `--tier C3` fail closed.

## 3. Merged Hardening & Integration Wave Across `Th0rgal/turbo-lean`, `Th0rgal/lean-sys`, and `Th0rgal/orb` (`2026-10-29` – `2026-10-31`)

| Repo & PR | Merge Commit | Landed Scope & Impact on Roadmap |
| :--- | :--- | :--- |
| **`lean-sys#2`** | `1498a54` | Track 4 audit remediation: 32-bit `Fd` preservation, `MAP_SHARED` `ShmRing`, Linux Landlock syscalls, loop-framed HTTP/1.1, pure-Lean SHA-256/HMAC-SHA256, streaming $>64\text{ MiB}$ WAL, `0444` immutable CAS. |
| **`lean-sys#3`** | `c089f3e` | Residual shim/HTTP/CAS hardening (`45/45` tight specs, `33` C-ABI exports, `63`-LOC shim): `mmap` `fstat` EOF/`SIGBUS` bounds via `leansys_verify_slice_bounds`, `inet_pton` validation, 0-byte send-loop `EIO`, CAS temp-file cleanup, and Apache-2.0 `LICENSE` (`5a807ea`). |
| **`turbo-lean#269`** | `4a6c4bd` | Stage 1C P0/P1 hardening: pure-scalar C-ABI gate `turbo_spec_verify_audited_materialization`, in-kernel `--audit-modules` `.olean` soundness gate in `ZygoteWorker.lean`, fail-closed Lake `.trace`/`.olean.hash` sidecar verification, `bwrap` untrusted PR isolation, strict JSON batch eval. |
| **`turbo-lean#272`** | `c054341` | Residual transport/CI security hardening on top of `#267` (superseding `#271`): `.redirects(0)` on `ureq`, exact loopback host parsing, env token confinement to loopback/HTTPS, SHA-pinned GitHub Actions, fail-closed `action.yml` sync. |
| **`turbo-lean#268`** | `5d24d06` | Pure-Rust quantized `int8` Matryoshka MUDD-TRM v4 premise/vacuity engine (`62.7 KB` embedded weights), structural/LNIR telemetry, compacted shard stat-cache reconstruction, and root MIT `LICENSE`. |
| **`turbo-lean#270`** | `2aedbc0` | Stage 1B LCNF bridge hardening: O(N) scalar-select join-point DAG sharing, flat-scalar tuple helper inlining (nested tuples rejected fail-closed), `partial`/`_unsafe_rec` audit guard, and package `Lean.*` import resolution (`Bridge.lean` = `323` LOC). |
| **`turbo-lean#275`** | `3aeedac` | Integrated external `eth-act/clifv` contribution (`#273` by `@parithosh`): plain-`lean` fallback `#print axioms` gate, `[axioms] allow` policy in `turbo-lean.toml` resolved at `--base` (never `sorryAx`/`Lean.trustCompiler`), fission/remote cache axiom-policy binding, MCP subprocess config-allowlist stripping, Lake reverse-dependency escalation (including `lean_exe` roots) on non-local edits, non-destructive `.olean` refresh, `--timeout` propagation, and `bv_decide` `cadical` discovery. |
| **`turbo-lean#276`** | `cac14f1` | CI `bwrap` provisioning on `push`, parallel test isolation, opt-in remote telemetry (`--no-telemetry` / `--telemetry` / `turbo-lean telemetry` / `[telemetry]`) with untrusted checkout TOML isolation at startup and emission, and shared `shm_cache` runtime factoring (`-243` net LOC). |
| **`turbo-lean#280`** | `e585ba9` | Stage 1D heap ADT / Perceus RC lowering + `SymbolicTV` heap provenance & loop/conditional-UB hardening (superseding closed `#277`); direct scalar-payload heap ADTs and `compile-llvm` of heap ops remain fail-closed (`Bridge.lean` = `348` LOC). |
| **`turbo-lean#288`–`#316`** | `02c0b30`..`9e4a258` | Built-kernel declaration statement pinning (`#288`), worktree auto-link & telemetry opt-in tightening (`#291`), B-3 emitter mutation runner + signal classification (`#293`, `#302`), bounded daemon/check timeouts (`#294`), paired `clifv` build/check benchmark (`#303`), lakefile option invalidation (`#304`), origin-bound remote prebuild (`#307`), `check --decl` `clifv` discovery parity (`#309`), Zygote worker hardening (`#310`), atomic CAS blob publication & torn-blob repair (`#315`), and staged DB/Zygote lock-free publication + closure-digest memoization (`#316`). |
| **`orb#1396`, `#1398`, `#1399`, `#1420`, `#1439`** | `bd95c256`..`e602e6ad` | P0 trust-boundary repairs (`#1396`), P2 shared WASM kernel (`#1398`), P1 128-export 6-engine conformance + P3 target qualification report (`#1399` / `f8a62ab1` at execution head `3c70e5ada` / Turbo `e585ba9`), P4–P6 `OrbWire` + 21-mutant domain suite (`#1420`), and P7 checkpointed $O(N)$ streaming + SIMD scanner (`#1439`). P0–P7 remain formally unaccepted (`coverage_registry.json` `INCOMPLETE`: `23 partial / 106 unconnected`, physical devices blocked, receipts unsigned). |
