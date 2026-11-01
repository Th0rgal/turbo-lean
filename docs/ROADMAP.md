# Track A / Track B status

Status of the `turbo-lean` for `clifv` integration (Track A) and the `LeanNative`
soundness program (Track B) as of `main` at `0212d86`. This is a status ledger,
not a contract: the locked goals and validation contracts remain
[`roadmap/GOALS.md`](../roadmap/GOALS.md) and
[`roadmap/VALIDATION_CONTRACTS.md`](../roadmap/VALIDATION_CONTRACTS.md), which this
file does not modify. SHAs below are the recorded merge commits or branch tips;
they are not restated guarantees.

## Track A — `turbo-lean` for `clifv`

A0a–A0e are merged on `main`:

| Step | PR | Merge commit | What landed |
| --- | --- | --- | --- |
| A0a | [#288](https://github.com/Th0rgal/turbo-lean/pull/288) | `02c0b30` | Pin theorem statements from built kernel declarations. |
| A0b | [#294](https://github.com/Th0rgal/turbo-lean/pull/294) | `ceebe65` | Bound daemon lifetime and honor per-check timeouts. |
| A0c | [#291](https://github.com/Th0rgal/turbo-lean/pull/291) | `63457a2` | Auto-worktree-link opt-out and strict remote-telemetry opt-in. |
| A0d | [#309](https://github.com/Th0rgal/turbo-lean/pull/309) | `80eaf32` | `check --decl` against the `clifv` corpus, plus declaration-discovery parity. |
| A0e | [#303](https://github.com/Th0rgal/turbo-lean/pull/303) | `2a8939e` | Paired `clifv` build/check benchmark (`scripts/bench_clifv.sh`, [`BENCH_CLIFV.md`](BENCH_CLIFV.md)). |

Open follow-ups:

- **Shadow CI on `clifv`.** [eth-act/clifv#799](https://github.com/eth-act/clifv/pull/799)
  (`eee0443`, *ci: non-blocking turbo-lean shadow verification (no merge requested)*)
  is an open **draft**. It does not request a merge and is not a required check.
- **Paired benchmark on `uruk`.** `origin/bench/b1-clifv-uruk` at `69c1571` is a
  status snapshot, not a result: attempt 3 was still in the untimed stock prime
  (module 437/4556) with `LEAN_NUM_THREADS=3 TURBO_LEAN_JOBS=3`, and the report
  lists **0 complete pairs**. Attempts 1–2 produced no measurements
  (`5b5fe70`). No speedup number exists yet. See
  [Running it on Orb nodes](BENCH_CLIFV.md#running-it-on-orb-nodes).

## Track B — `LeanNative` soundness

| Item | State | Where |
| --- | --- | --- |
| B0 shadow-semantics checker and allowlist ratchet | **Merged** [#296](https://github.com/Th0rgal/turbo-lean/pull/296) `0212d86` | [`docs/SHADOW_SEMANTICS.md`](SHADOW_SEMANTICS.md). The CI step fails the job; it is **not** merge-blocking (no branch protection or ruleset on `main`). |
| B-3 emitter mutation runner | **Merged** [#293](https://github.com/Th0rgal/turbo-lean/pull/293) `1196038` | `scripts/emitter_mutants.py`. Unit-tested in CI; the mutation suite itself is a non-blocking `push` / `workflow_dispatch` job. |
| D1 step 5a (`HeapObj` contract + regressions) | **Merged** [#292](https://github.com/Th0rgal/turbo-lean/pull/292) `6e347f9` | [`docs/HEAPOBJ_CONTRACT.md`](HEAPOBJ_CONTRACT.md). Normative text plus named regressions; several clauses are XFAIL or UNCOVERED on `main`. |
| D1 step 5b (unified `objFields` / `scalarFields`) | **Open draft** [#300](https://github.com/Th0rgal/turbo-lean/pull/300) `c75faa9` | Not on `main`. The 5a contract says the remaining XFAILs are for this PR. |
| B1 in-repo stand-in semantics | **Held**, open draft [#284](https://github.com/Th0rgal/turbo-lean/pull/284) | Title: *HOLD: in-repo stand-in semantics (not upstream lean-mlir/LNSym/con-leche)*. Not an upstream semantics proof. |
| B2 `LNIR → CLIF → AArch64` | **Not on `main`.** Branch `research/b12-feasibility` at `5cda17d` | Documented in that branch's `research/B2-spec.md` and `research/B2-status.md`. There is no `Backend/Clif.lean` on `main`. |
| B3–B5 | **Not started** | No merged or open PR claims these steps. |

### B2 boundary (branch only)

On `research/b12-feasibility` (`5cda17d`), `research/B2-status.md` records
`B2.EndToEnd.collatz_to_arm` as kernel-checked for `collatz_steps`, composing
the pinned clifv theorem `E2E.backend_correct_final_of_lower`
(`FV/E2E/FinalDirect.lean:23` on that pin). The same note records generic
O1–O2 (`B2.Lowering.lower_in_subsetE`, `B2.Lowering.lower_sig`) and states that
O3–O7 are proved for `collatz_steps` only, that generic F64 simulation and
safety remain open, and that the theorem does not establish frontend
correctness, loader correctness, or hardware execution. Those statements are
claims of that branch's status note, checked against Lean 4.34.1 there; they
are not theorems of this repository's `main`.

## Open soundness and parity PRs

None of these are on `main`. One-line scope is the PR title.

| PR | Head | Title |
| --- | --- | --- |
| [#301](https://github.com/Th0rgal/turbo-lean/pull/301) | `504cfd7` | fix: enforce Lean option policy at verification boundaries |
| [#308](https://github.com/Th0rgal/turbo-lean/pull/308) | `d8c72de` | fix: pin verifier executables to the installed toolchain |
| [#312](https://github.com/Th0rgal/turbo-lean/pull/312) | `87d5f1d` | fix: pin import artifact digests in verified-sources manifest (P0-4) |
| [#313](https://github.com/Th0rgal/turbo-lean/pull/313) | `dcef0f4` | fix(check): never verify or cache a `--decl` target that uses sorry (P0-1) |
| [#317](https://github.com/Th0rgal/turbo-lean/pull/317) | `00ccfb6` | build: support Lake's declarative file inputs (`input_dir` / `input_file` + `needs`) |
| [#318](https://github.com/Th0rgal/turbo-lean/pull/318) | `9e7a355` | A0: resolve lexical scopes and attest Lean declaration identities |
| [#320](https://github.com/Th0rgal/turbo-lean/pull/320) | `ea511e9` | fix(fastcheck): certify counterexamples only via statement re-evaluation |
| [#321](https://github.com/Th0rgal/turbo-lean/pull/321) | `d4e3d86` | fix(cas): crash-durable blob/marker publication and stable singleflight lock inodes |
| [#322](https://github.com/Th0rgal/turbo-lean/pull/322) | `6ef176a` | fix(zygote): bind imported-env cache to imported bytes; content-verified closure memo |
| [#323](https://github.com/Th0rgal/turbo-lean/pull/323) | `54b9a81` | test(ws4): untrusted write-containment test skips only without the toolchain |
| [#324](https://github.com/Th0rgal/turbo-lean/pull/324) (draft) | `8f1b14a` | fix(module-builder): restore bit-exact Lake v4.35.0 `.trace`, missing-`.c` outputs, and precompileModules parity |

[#300](https://github.com/Th0rgal/turbo-lean/pull/300) and
[#284](https://github.com/Th0rgal/turbo-lean/pull/284) are listed under Track B
above and are also still open.
