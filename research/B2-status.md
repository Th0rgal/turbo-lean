# B2 status

Baseline: `5508b9f`; clifv `5018b9509dc124154dbe08a5bd85862595d8eab7`.
Checkpoint: 2026-10-31 14:03 UTC. The real executable lowering lives in
`lean/LeanNative/Backend/Clif.lean`; `compile-clif` calls that definition.
The proof package's default `lake build` passes on Lean 4.34.1.

| Obligation | Status | Evidence / remaining work |
| --- | --- | --- |
| O1 subset | PROVED | `B2.Lowering.lower_in_subsetE`, for every successful executable lowering; `#print axioms`: `[propext, Classical.choice]`. Lowering checks the real `Compile.functionE` and rejects on false. |
| O2 signature | PROVED | `B2.Lowering.lower_sig`, for every successful lowering; `#print axioms`: `[propext]`. |
| O3 simulation | PROVED (collatz_steps) | `B2.CollatzClif.source_simulation` connects the real LNIR evaluator to `Clif.runWith` on the real successfully lowered function, for every UInt64 argument pair and arbitrary source heap/CLIF memory; fuel `15 * steps.toNat + 5`. `loop_returns` proves bounded-loop termination, including non-overflow of the taken index increment. Axioms: `[propext, Classical.choice, Quot.sound]`. The public CLIF run preserves the entire initial memory, including the optional slot-placement oracle. Generic F64 simulation remains open. |
| O4 safety | SORRY | `B2.RunSafety.collatz_run_prefix` excludes both trapped and stuck outcomes of the public `runWith` at every fuel, including initialization, using the all-input termination proof; allowed axioms only. Connecting this to reachable-state `TrapsExplicit` remains open. |
| O5 backend artifacts | SORRY | `B2.Smoke.collatz_lowered` proves the real lowering succeeds (`[propext]`); The exact VCode artifact now has a kernel-checked lowering equation (allowed axioms only); allocation, emission and layout are still open. FinalDirect dependency cone building in background. |
| O6 contracts | SORRY | Generic empty extern/signature/global/slot declarations: `B2.Lowering.lower_declarations` (`[propext]`). `B2.CallFree` proves absent try calls, indirect statements/signatures, and TLS for the actual Collatz function, with only allowed axioms. Complete site/contract discharge remains open. |
| O7 AArch64 x0 | SORRY | Needs O3–O6, backend composition, and transitive axiom audit. |

`B2.Division.total_div_agrees` and `safe_div_executes` have axiom closure
`[propext, Quot.sound]`; `total_mod_agrees` has `[propext]`. They use
`Clif.Sem.udiv/urem` and UInt64 operations from the LNIR evaluator. Full
instruction-sequence simulation remains open. Collatz and nested-loop
CLIF execution checks have `[propext, Quot.sound]`; no native decision.

Six compiler/proof source pairs are committed byte-identical (Types,
AST, Codec, Value, Eval, Clif). `scripts/check_b2_source_identity.py`
passes and verifies a clean pinned dependency. `.github/workflows/b2.yml`
enforces the check, proof build, and compiler-toolchain integration build.
Remote CI for the memory-preservation/call-free checkpoint `02dfbed` passed:
https://github.com/Th0rgal/turbo-lean/actions/runs/41207047569 .
Local Lean 4.35 CoreCLI integration build passed. The actual compiler
dispatcher emitted collatz_steps CLIF successfully (same lowering;
division by two is a shift). `research/b2-compiler-smoke.lean` records
that check and CI now runs it too. No AArch64 emission claim.

`B2.AxiomAudit` is part of the default build. It calls
`Lean.collectAxioms` on every currently claimed result and rejects
anything outside propext/Quot.sound/Classical.choice. The complete active
root (including CollatzSource/CollatzClif and the audit) builds locally.
The loop and entry proofs use the actual `Clif.step`, `Clif.runLoop`,
`Clif.enterFunc`, and `Clif.runWith`; inspected blocks have kernel equalities
to the real generated function. The default build and transitive audit pass,
including the complete body/backedge, bounded-loop, entry, and source simulation.

Next proof work: connect the returning execution to `ClifEntry` and reachable
safety / `TrapsExplicit` (O4); produce backend artifacts/allocation (O5),
discharge contracts (O6), and compose (O7). The FinalDirect build is live;
upstream IselData and IselContract have finished, with dependent proof modules
still building. The shared host suffered a prolonged disk-I/O stall.
`B2.Artifacts`, `B2.BackendEntry`, `B2.BackendContracts`, and `B2.EndToEnd`
are WIP and excluded from the active root and claims until their checks pass.
They contain the concrete pipeline equations, exact upstream entry/reachability
connection, absent-site contracts, and composition code. No O7 claim yet.

The session cgroup has `memory.max = 16 GiB` and `memory.high = 14.4 GiB`.
Running artifact checks alongside four upstream proof workers caused severe
reclaim/I/O stalls. The backend build now runs one compiler at a time. Diagnostic artifact checks
are capped at 2–3 GiB; avoid overlapping unrestricted heavy checks. The live backend build
is PID 1926474, from `research/b2-proofs`, logging to `/tmp/b2-final-cone.log`.
RefinesInsts, RefinesInsts2, RegallocInstsInt/ZR, IselTermsImm and
IselCtlUnmatch have finished. The temporary Lake pause is over; the old
`/tmp/b2-resume-lake.py` helper has finished.
`/tmp/b2-limit-lean-jobs.py 1926474` now limits its compiler subprocesses to one
at a time (each still has four Lean threads), logging to
`/tmp/b2-limit-lean-jobs.log`. Two smaller jobs were intentionally deferred to
free memory: `FV.Backend.Proof.CSemRename` and
`FV.Backend.Proof.LogicImmComplete`. The original build will report these
failures; after it drains, retry the same FinalDirect target with the same
one-compiler controller so the completed large proofs are reused.
Do not duplicate or restart a still-working compiler on a polling timeout. The inspected executable pipeline
reports success through allocation check, emission, and layout; kernel
certification is still open. `Artifacts.input` is a snapshot tied to the actual
lowering by an equality, to prevent repeated lowering during backend checks.
The temporary `/tmp/b2-artifacts-instrumented.lean` reports its stage in
`/tmp/b2-artifact-stage`; its last attempted stage was `lowerFunction`.
Emission uses `Std.HashMap Lbl` and Lean's opaque `mixHash`, so plain
`decide +kernel` gets stuck. `Artifacts` now uses proof-producing `cbv` with
Std's certified map rewrite lemmas. `/tmp/b2-cbv-hashmap.lean` verified an
opaque pair-hash lookup with axioms `[propext, Classical.choice, Quot.sound]`;
the actual pipeline equations still need to be run, separately from the
backend dependency build. The old instrumented temporary copy predates this
`cbv` change: regenerate it before use.

`CalleeOk.pc` and `.ext` are unconditional even for no call sites. The composition
code retains precisely these hook/program-preservation contracts and discharges
`.os` from absence of call sites. Treating the entire `CalleeOk` structure as
vacuous would be incorrect. Do not restart a live build on an observation timeout.

The active root `B2.lean` excludes the old sorry-bearing SpecCore/SpecE2E
sketches. Their DivGuarded, untyped-argument, and empty-program statements
are superseded by B2-spec.md. `B2.Core` contains definitions only.

Resource note: Lake 5.0.0 / Lean 4.34.1 rejects `lake -j4` with
`unknown short option '-j'`. Builds use `LEAN_NUM_THREADS=4` and named
cones; telemetry is off. Ordinary tactic reduction of the first smoke
test grew past 12 GB, so it was stopped; `decide +kernel` completes the
same real CLIF checks in seconds, with audited allowed axioms.

Artifact reduction diagnosis (2026-10-31): raising `maxRecDepth` alone did not
certify any pipeline equation. Equation generation for `Backend.mkVariant`
recurses through the generated ISLE tables; equation generation on partially
applied `externCtor` also exhausted its resource limit. The excluded WIP
`B2.BackendEval` provides explicit unfolding equations and proof-producing
lookup reduction, leaving upstream sources untouched. Its isolated actual
`opcodeV "Iconst"` lookup checked with only the allowed axioms; full lowering remains open.
The original ISLE interpreter and its default million-step fuel remain in use.

The concrete instruction-selection obstruction is resolved: `/tmp/b2-fuel-concrete.log`
checked the exact `B2.Artifacts.lower` equation with `[propext, Classical.choice,
Quot.sound]`. `B2.BackendLower` preserves that literal VCode and proof as a separate
module (its standalone build is running). `B2.IsleFuel.runTerm_of_apply` checked
with the same allowed closure: a successful 1024-fuel call of the actual interpreter
transfers, by upstream fuel monotonicity, to `Backend.runTerm`'s unchanged default
million-fuel execution. `B2.BackendEval` caches individually checked call certificates.
No upstream source or executable semantics changed. Direct million-fuel certificate
replay exceeded both 4 and 8 GiB checker limits; that route is superseded.
The concrete prepared VCode equation checked separately on the inspected candidate;
`B2.Artifacts` still awaits complete checking and remains excluded from the active root.
The original dependency build continues with one compiler; RegallocAtomic is live.
