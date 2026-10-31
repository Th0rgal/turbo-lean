# B2 status

Baseline: `5508b9f`; clifv `5018b9509dc124154dbe08a5bd85862595d8eab7`.
Checkpoint: 2026-10-31 16:53 UTC. The executable lowering lives in
`lean/LeanNative/Backend/Clif.lean`; `compile-clif` calls that definition.
The default proof build and transitive axiom audit pass on Lean 4.34.1.

| Obligation | Status | Evidence / remaining work |
| --- | --- | --- |
| O1 subset | PROVED | `B2.Lowering.lower_in_subsetE`, for every successful executable lowering; axioms `[propext, Classical.choice]`. Lowering checks the real `Compile.functionE` and rejects on false. |
| O2 signature | PROVED | `B2.Lowering.lower_sig`, for every successful lowering; axioms `[propext]`. |
| O3 simulation | PROVED (collatz_steps) | `B2.CollatzClif.source_simulation` connects the actual LNIR evaluator to `Clif.runWith` on the actual lowered function for every UInt64 argument pair and arbitrary source heap/CLIF memory. Fuel is `15 * steps.toNat + 5`; the entire initial memory, including the slot-placement oracle, is preserved. Generic F64 simulation remains open. |
| O4 safety | PROVED (collatz_steps) | `B2.BackendEntry.entry_eq` and `returns` establish the exact upstream `ClifEntry` contract. `reachable_step_safe` excludes trapped/stuck steps at every reachable state; `traps_explicit` proves the exact upstream `E2E.TrapsExplicit` premise. `B2.RunSafety.collatz_run_prefix` also excludes trapped/stuck public runs at every fuel. |
| O5 backend artifacts | SORRY | `B2.Artifacts.input_eq`, `verifiable`, and `lower` certify the exact instruction-selection artifact from `Backend.lowerFunction`. `B2.Artifacts.prepared`, `spill_alloc`, and `allocation_checked` certify the actual block permutation 0,1,3,2, exact spill allocation, and acceptance by upstream `checkAlloc`. `B2.Artifacts.allocated`, `emitted`, and `laid_out` certify actual AArch64 lowering, emission, and binary layout. Input subset/dominance/scope packaging is still unchecked in the contract draft. |
| O6 contracts | SORRY | `B2.Lowering.lower_declarations` proves empty extern/signature/global/slot declarations generically. `B2.CallFree` proves absence of try calls, indirect statements/signatures, and TLS for the actual Collatz function. Complete contract composition remains unchecked. |
| O7 AArch64 x0 | SORRY | Needs O6, backend composition, and its transitive axiom audit. No AArch64-success claim yet. |

Every PROVED result is in the default root and `B2.AxiomAudit`, which calls
`Lean.collectAxioms` and rejects closures outside `propext`, `Quot.sound`,
and `Classical.choice`. The O3/O4 and instruction-selection closures use
only these axioms. No `native_decide`, added axioms, or upstream source changes.
The old sorry-bearing SpecCore/SpecE2E sketches are excluded; their
DivGuarded, untyped-argument, and empty-program statements are superseded
by B2-spec.md. `B2.Core` contains definitions only.

`B2.Division.total_div_agrees` and `safe_div_executes` have closure
`[propext, Quot.sound]`; `total_mod_agrees` has `[propext]`. They use the
real `Clif.Sem.udiv/urem` and LNIR UInt64 operations. Full generic
instruction-sequence simulation remains open.

Six compiler/proof source pairs are committed byte-identical (Types,
AST, Codec, Value, Eval, Clif). `scripts/check_b2_source_identity.py`
verifies them and a clean pinned clifv. `.github/workflows/b2.yml` enforces
source identity, the proof build, and compiler-toolchain integration.
Remote CI for checkpoint `02dfbed` passed:
https://github.com/Th0rgal/turbo-lean/actions/runs/41207047569 .
The local Lean 4.35 CoreCLI integration build passed; the actual compiler
dispatcher emitted collatz_steps CLIF. `research/b2-compiler-smoke.lean`
records that check and CI runs it too.

Instruction selection is certified in `B2.BackendLower`, now active in
the root and audit. `B2.IsleFuel.runTerm_of_apply` lifts a successful
1024-fuel call of the actual interpreter to `Backend.runTerm` with its
unchanged default million fuel, using upstream fuel monotonicity.
`B2.BackendEval` generates kernel-checked certificates and caches lookup
facts; no executable semantics or interpreter configuration changed.
Direct million-fuel certificate replay exceeded 4 and 8 GiB checker caps;
the monotonicity proof resolves that obstruction.

`B2.BackendAlloc` is active in the root and audit. Its literal allocation is
tied to upstream `spillAlloc` by a kernel-checked equality. `B2.AllocationEval`
unfolds existing spill definitions before Lean's failing singleton-array
equation generation, and registers a certified hash-map size rewrite.
The allocation acceptance proof also passes with closure `[propext, Quot.sound]`.
`B2.Artifacts` is now kernel checked through binary layout and active in the
root and audit. `B2.BackendContracts` and `B2.EndToEnd` remain WIP and
excluded until their checks pass. Emission uses opaque `mixHash`; certified
Std HashMap/HashSet rewrite lemmas are available. Executable pipeline
inspection reports success through allocation check, emission and layout;
the corresponding kernel certificates now pass.

`CalleeOk.pc` and `.ext` are unconditional even without call sites. The WIP
composition retains these hook/program-preservation premises and uses
site absence only for `.os`. Real ABI, machine-entry, stack, memory,
and symbol premises remain explicit.

Next: discharge the remaining contracts and compose the LNIR-to-x0 theorem against `E2E.backend_correct_final_of_lower`.
The FinalDirect dependency cone is building in the background, one compiler
at a time. Do not duplicate or restart a working compiler on a timeout.

Resource notes: the execution environment was replaced around 16:09 UTC;
the former `/tmp/repos/turbo-b2` checkout, compiler processes, and logs vanished.
The pushed checkpoint `e89f7dc` was restored to workspace `turbo-b2`, and clifv
was fetched at the exact pin. Source identity passes. CI passed both the
pipeline checkpoint `5425e2c` and exporter checkpoint `e89f7dc`:
https://github.com/Th0rgal/turbo-lean/actions/runs/41216872036 and
https://github.com/Th0rgal/turbo-lean/actions/runs/41218005244 .
CI also passed the excluded-draft checkpoint `d23535b`:
https://github.com/Th0rgal/turbo-lean/actions/runs/41220002990 .

The initial replacement builds failed: FinalDirect job
`de3fb23e-6a97-5640-bbd2-fa37a78c1d5c` reported a missing file; the concurrent
root attempt hit turbo-lean's default 300-second per-module timeout after
compiler pausing. A separate earlier root job failed because the restored
checkout lacked the pinned `lean-sys` dependency; its sources are now restored.
The proof package remains on Lean 4.34.1.

Durable job `d6c09d26-5bfe-53a1-851b-650addbeee3f` builds the active B2 root
and then FinalDirect sequentially, with native `TURBO_LEAN_JOBS=1` and
`TURBO_LEAN_MODULE_TIMEOUT_SECS=7200`. Logs are `.b2-work/root-v2.log` and
`.b2-work/final-v2.log`; no compiler pausing is used. `LEAN_NUM_THREADS=4`
and telemetry off apply throughout. These builds are pending, not passing
evidence for the restored checkout.

`B2.BackendScope` is an excluded, unverified draft split from BackendContracts
to isolate the dominance check. Its Boolean `insertIfNew` lookup lemma passed
an isolated kernel check and two concrete lookup tests with only the allowed
axioms. Actual `dominatedB` still awaits checking; earlier reductions repeated
decidable-instance transport and exceeded recursion limits. An isolated
diagnostic identifies an unrewritten raw hash-map lookup reaching the opaque
`System.Platform.getNumBits`; this is a reduction obstacle, not evidence of a
false dominance predicate. Method-level lookup rewrites passed isolated kernel checks and concrete
examples. The exact availability array also passed a diagnostic kernel check
against the runtime-extracted context, with only the allowed axioms. The
actual input/context tie and complete dominance statement are still pending. `B2.EndToEnd`
now drafts the explicit equality with x0, but composition is still unchecked.
These draft changes do not upgrade O5, O6, or O7.
