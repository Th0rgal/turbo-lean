# Track A / Track B status

Status of the `turbo-lean` for `clifv` integration (Track A), the `LeanNative`
soundness program (Track B), and verification-boundary hardening as of `main` at
`e1bb46c`. This is a status ledger, not a contract: the locked goals and
validation contracts remain [`roadmap/GOALS.md`](../roadmap/GOALS.md) and
[`roadmap/VALIDATION_CONTRACTS.md`](../roadmap/VALIDATION_CONTRACTS.md), which
this file does not modify. SHAs below are the recorded merge commits or branch
tips; they are not restated guarantees.

## Track A — `turbo-lean` for `clifv` & verification-boundary hardening

Merged on `main`:

| Step | PR | Merge commit | What landed |
| --- | --- | --- | --- |
| A0a | [#288](https://github.com/Th0rgal/turbo-lean/pull/288) | `02c0b30` | Pin theorem statements from built kernel declarations. |
| A0b | [#294](https://github.com/Th0rgal/turbo-lean/pull/294) | `ceebe65` | Bound daemon lifetime and honor per-check timeouts. |
| A0c | [#291](https://github.com/Th0rgal/turbo-lean/pull/291) | `63457a2` | Auto-worktree-link opt-out and strict remote-telemetry opt-in. |
| A0d | [#309](https://github.com/Th0rgal/turbo-lean/pull/309) | `80eaf32` | `check --decl` against the `clifv` corpus, plus declaration-discovery parity. |
| A0e | [#303](https://github.com/Th0rgal/turbo-lean/pull/303) | `2a8939e` | Paired `clifv` build/check benchmark (`scripts/bench_clifv.sh`, [`BENCH_CLIFV.md`](BENCH_CLIFV.md)). |
| A0f / S1 | [#322](https://github.com/Th0rgal/turbo-lean/pull/322) | `e1ff917` | Bind Zygote imported-environment cache to imported `.olean` bytes; content-verified closure memo. |
| A0g / S3 | [#308](https://github.com/Th0rgal/turbo-lean/pull/308) | `8658adc` | Pin verifier executables (`lean`, `lake`, `leanc`) to the installed toolchain (`outside_checkout`, `git >= 2.46`). |
| A0h / S5 | [#318](https://github.com/Th0rgal/turbo-lean/pull/318) | `f68e250` | Lexical declaration-identity resolution (`--decl-identity`), sandboxed probes, and `statement-v1` `kernel_type_hash` attestation. |
| A0i / S6 | [#301](https://github.com/Th0rgal/turbo-lean/pull/301) | `e1bb46c` | Enforce Lean option policy at verification boundaries and independent `Kernel.Environment.replay` on worker/compiled declarations. |

Open follow-ups:

- **Shadow CI on `clifv`.** [eth-act/clifv#799](https://github.com/eth-act/clifv/pull/799)
  (`730d873`, *ci: non-blocking turbo-lean shadow verification (no merge requested)*)
  remains an open **draft** (stock Lean remains authoritative; no merge is requested).
  The 20-commit `main` audit at
  [`#issuecomment-6555072384`](https://github.com/eth-act/clifv/pull/799#issuecomment-6555072384)
  records **0 / 20 complete agreements** (`INCOMPLETE`): 19 of the latest 20
  first-parent commits had cancelled/pending stock `Full gate` runs (`stock_ok = null`),
  and on the single eligible commit (`df71db603146`) cold `ci-verify` hit the
  900 s shadow workflow timeout (`rc=124`), while direct per-file `turbo-lean check`
  passed 10/11 changed `.lean` files and rejected 1 witness file
  (`StockMemorySretCopyCheckWitness.lean`) for `native_decide`/`ofReduceBool`
  without a `turbo-lean.toml` allowlist.
- **Paired benchmark (`A0e` / S8).** **No completed paired measurement or speedup
  claim exists yet** (`0` complete timed pairs across both recorded branches):
  - `origin/bench/b1-clifv-vast` (`d9d174a`, `results/bench-clifv/2026-11-01/README.md`)
    ran on a dedicated 64 GiB Vast.ai VM (`rtx4090-a`, Xeon E5-2680 v4 @ 2.40 GHz,
    cgroup `memory.max = 60.13 GiB`, `clifv` `5018b95`). Attempt 1
    (`LEAN_NUM_THREADS=12`, `TURBO_LEAN_JOBS=12`, `TURBO_LEAN_MAX_MEMORY_MB=53248`)
    built `3324` modules (`3497/4556` steps) in untimed `prime-lake: stock` before
    concurrent `StockCmp*DriverRuns` / `StockRotate*Witness` processes (7–10 GiB RSS
    each) hit `memory.max` (`oom_kill`). Attempt 2 (`LEAN_NUM_THREADS=6`,
    `TURBO_LEAN_JOBS=6`, `TURBO_LEAN_MAX_MEMORY_MB=53248`) reached `1104/4556` steps
    (`1038` modules) with **0 OOM kills** (peak `59.08 GiB` during `IselData`/`RuleBitops`,
    then steady `11–20 GiB`) when the 720-minute managed-VM lifetime ceiling expired
    (`INCONCLUSIVE`, 0 pairs).
  - Earlier diagnostic branch `origin/bench/b1-clifv-uruk` (`292a631`,
    `results/bench-clifv/2026-10-31/README.md`) ran on shared 8-thread `uruk` under
    a 16 GiB job cgroup cap (`LEAN_NUM_THREADS=3`, `TURBO_LEAN_JOBS=3`) and also
    recorded **0 complete pairs**.
  - See [Running it on Orb nodes](BENCH_CLIFV.md#running-it-on-orb-nodes).

## Track B — `LeanNative` soundness

| Item | State | Where |
| --- | --- | --- |
| B0 shadow-semantics checker and allowlist ratchet | **Merged** [#296](https://github.com/Th0rgal/turbo-lean/pull/296) `0212d86` | [`docs/SHADOW_SEMANTICS.md`](SHADOW_SEMANTICS.md). The CI step fails the job; it is **not** merge-blocking (no branch protection or ruleset on `main`). |
| B-3 emitter mutation runner | **Merged** [#293](https://github.com/Th0rgal/turbo-lean/pull/293) `1196038` | `scripts/emitter_mutants.py` (`llvm`/`mlir`/`ptx`/`metal`/`c-abi`, `M1..M11`). Unit-tested in CI; the mutation suite itself is a non-blocking `push` / `workflow_dispatch` job. |
| D1 step 5a (`HeapObj` contract + regressions) | **Merged** [#292](https://github.com/Th0rgal/turbo-lean/pull/292) `6e347f9` | [`docs/HEAPOBJ_CONTRACT.md`](HEAPOBJ_CONTRACT.md) + `lean/LeanNative/Tests/HeapObjContract.lean`. |
| D1 step 5b (unified `objFields` / `scalarFields`) | **Merged** [#300](https://github.com/Th0rgal/turbo-lean/pull/300) `210f1df` | Unified `HeapObj {id, tag, objFields, scalarFields}`, `UBError.fuelExhausted`, worklist `decRefValsFuel`/`decRefObjFuel`, `SymExecState.symExhausted`, guarded LLVM heap codegen, and `lean/LeanNative/Tests/HeapObj5b.lean`. Flipped 19/20 XFAILs in `HeapObjContract.lean` (**47 pass**, **1 XFAIL** `codegen_projection_guarded_field_load`, **6 UNCOVERED** clauses). |
| B2 `LNIR → CLIF → AArch64` (`collatz_steps` slice) | **Merged** [#326](https://github.com/Th0rgal/turbo-lean/pull/326) `93f3e9f` | `lean/LeanNative/Backend/Clif.lean` (`compile-clif`), `research/b2-proofs/`, [`research/B2-status.md`](../research/B2-status.md), `scripts/check_b2_source_identity.py`, `.github/workflows/b2.yml`. Generic O1–O2; O3–O7 proved for `collatz_steps` only; generic `F64` simulation/safety remain open. |
| B1 in-repo stand-in semantics | **Held**, open draft [#284](https://github.com/Th0rgal/turbo-lean/pull/284) `48f9f25` | Title: *HOLD: in-repo stand-in semantics (not upstream lean-mlir/LNSym/con-leche)*. Not an upstream semantics proof. |
| B3–B5 | **Not started** | No merged or open PR claims these steps. |

### B2 scope & trust boundary (`#326`, on `main`)

`lean/LeanNative/Backend/Clif.lean` provides executable `LNIR → Clif.Function`
lowering on the compiler toolchain (`Lean 4.35.0`), and `research/b2-proofs/`
checks the proof package on `Lean 4.34.1` against pinned `eth-act/clifv`
(`5018b9509dc124154dbe08a5bd85862595d8eab7`), with byte-identical compiler/vendor
sources enforced by `scripts/check_b2_source_identity.py` and `.github/workflows/b2.yml`.
`B2.Lowering.lower_in_subsetE` and `B2.Lowering.lower_sig` (O1–O2) are generic over
every successful `lowerDecl`; O3–O7 (`B2.EndToEnd.collatz_to_arm`, composing
`clifv`'s `E2E.backend_correct_final_of_lower` and audited in `B2.AxiomAudit`
against `[propext, Quot.sound, Classical.choice]`) are proved for the bounded
wrapping `UInt64` `collatz_steps` kernel only. Generic scalar-fragment (`F64`)
simulation and safety remain open, and the theorem does not prove frontend
elaboration, CLI printing/file export, cross-toolchain runtime equivalence, OS
loading, or physical silicon execution (see [`research/B2-status.md`](../research/B2-status.md)).

## Open soundness and parity PRs

None of these are on `main`. One-line scope is the PR title.

| PR | Head | Title |
| --- | --- | --- |
| [#312](https://github.com/Th0rgal/turbo-lean/pull/312) | `7c0962b` | fix: pin import artifact digests in verified-sources manifest (P0-4) |
| [#313](https://github.com/Th0rgal/turbo-lean/pull/313) | `8e66770` | fix(check): never verify or cache a `--decl` target that uses sorry (P0-1) |
| [#317](https://github.com/Th0rgal/turbo-lean/pull/317) | `f5c6784` | build: support Lake's declarative file inputs (`input_dir` / `input_file` + `needs`) |
| [#320](https://github.com/Th0rgal/turbo-lean/pull/320) | `dcb5fb4` | fix(fastcheck): certify counterexamples only via statement re-evaluation |
| [#321](https://github.com/Th0rgal/turbo-lean/pull/321) | `dbc0a5f` | fix(cas): crash-durable blob/marker publication and stable singleflight lock inodes |
| [#323](https://github.com/Th0rgal/turbo-lean/pull/323) | `54b9a81` | test(ws4): untrusted write-containment test skips only without the toolchain |
| [#324](https://github.com/Th0rgal/turbo-lean/pull/324) | `17edf04` | fix(module-builder): restore bit-exact Lake v4.35.0 `.trace`, missing-`.c` outputs, and precompileModules parity |

Held draft [#284](https://github.com/Th0rgal/turbo-lean/pull/284) (`48f9f25`) is
listed under Track B above and also remains open.
