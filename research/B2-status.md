# B2 status

Baseline: `5508b9f`; clifv `5018b9509dc124154dbe08a5bd85862595d8eab7`.
Checkpoint: 2026-10-31 11:08 UTC. The real executable lowering lives in
`lean/LeanNative/Backend/Clif.lean`; `compile-clif` calls that definition.
The proof package's default `lake build` passes on Lean 4.34.1.

| Obligation | Status | Evidence / remaining work |
| --- | --- | --- |
| O1 subset | PROVED | `B2.Lowering.lower_in_subsetE`, for every successful executable lowering; `#print axioms`: `[propext, Classical.choice]`. Lowering checks the real `Compile.functionE` and rejects on false. |
| O2 signature | PROVED | `B2.Lowering.lower_sig`, for every successful lowering; `#print axioms`: `[propext]`. |
| O3 simulation | PROVED (collatz_steps) | `B2.CollatzClif.source_simulation` connects the real LNIR evaluator to `Clif.runWith` on the real successfully lowered function, for every UInt64 argument pair and arbitrary source heap/CLIF memory; fuel `15 * steps.toNat + 5`. `loop_returns` proves bounded-loop termination, including non-overflow of the taken index increment. Axioms: `[propext, Classical.choice, Quot.sound]`. Generic F64 simulation remains open. |
| O4 safety | SORRY | `B2.RunSafety.collatz_prefix` excludes both trapped and stuck outcomes at every fuel from the initialized entry state, using the all-input termination proof; allowed axioms only. Connecting this to reachable-state `TrapsExplicit` remains open. |
| O5 backend artifacts | SORRY | `B2.Smoke.collatz_lowered` proves the real lowering succeeds (`[propext]`); no checked backend artifacts/allocation yet. FinalDirect dependency cone building in background. |
| O6 contracts | SORRY | Generic empty extern/signature/global/slot declarations: `B2.Lowering.lower_declarations` (`[propext]`). Complete site/contract discharge remains open. |
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
Remote CI for `be544ba` passed:
https://github.com/Th0rgal/turbo-lean/actions/runs/41192718230 .
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
upstream IselData finished after 1853 seconds, with dependent proof modules
still building. Do not restart a live build on an observation timeout.

The active root `B2.lean` excludes the old sorry-bearing SpecCore/SpecE2E
sketches. Their DivGuarded, untyped-argument, and empty-program statements
are superseded by B2-spec.md. `B2.Core` contains definitions only.

Resource note: Lake 5.0.0 / Lean 4.34.1 rejects `lake -j4` with
`unknown short option '-j'`. Builds use `LEAN_NUM_THREADS=4` and named
cones; telemetry is off. Ordinary tactic reduction of the first smoke
test grew past 12 GB, so it was stopped; `decide +kernel` completes the
same real CLIF checks in seconds, with audited allowed axioms.
