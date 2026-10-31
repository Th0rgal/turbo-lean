# B2 status

Baseline: `5508b9f`; clifv `5018b9509dc124154dbe08a5bd85862595d8eab7`.
Checkpoint: 2026-10-31 19:18 UTC. The executable lowering lives in
`lean/LeanNative/Backend/Clif.lean`; `compile-clif` calls that definition.
The active root and strict transitive axiom audit pass kernel checks on Lean 4.34.1.

| Obligation | Status | Evidence / remaining work |
| --- | --- | --- |
| O1 subset | PROVED | `B2.Lowering.lower_in_subsetE`, for every successful executable lowering; axioms `[propext, Classical.choice]`. Lowering checks the real `Compile.functionE` and rejects on false. |
| O2 signature | PROVED | `B2.Lowering.lower_sig`, for every successful lowering; axioms `[propext]`. |
| O3 simulation | PROVED (collatz_steps) | `B2.CollatzClif.source_simulation` connects the actual LNIR evaluator to `Clif.runWith` on the actual lowered function for every UInt64 argument pair and arbitrary source heap/CLIF memory. Fuel is `15 * steps.toNat + 5`; the entire initial memory, including the slot-placement oracle, is preserved. Generic F64 simulation remains open. |
| O4 safety | PROVED (collatz_steps) | `B2.BackendEntry.entry_eq` and `returns` establish the exact upstream `ClifEntry` contract. `reachable_step_safe` excludes trapped/stuck steps at every reachable state; `traps_explicit` proves the exact upstream `E2E.TrapsExplicit` premise. `B2.RunSafety.collatz_run_prefix` also excludes trapped/stuck public runs at every fuel. |
| O5 backend artifacts | PROVED (collatz_steps) | `B2.Artifacts.input_eq`, `verifiable`, and `lower` certify the exact instruction-selection artifact from `Backend.lowerFunction`. `B2.Artifacts.prepared`, `spill_alloc`, and `allocation_checked` certify the actual block permutation 0,1,3,2, exact spill allocation, and acceptance by upstream `checkAlloc`. `B2.Artifacts.allocated`, `emitted`, and `laid_out` certify actual AArch64 lowering, emission, and binary layout. `B2.BackendContracts.subset`, `dominated`, and `scope` discharge the exact upstream input predicates; all are active and pass the strict transitive audit. |
| O6 contracts | SORRY | `B2.Lowering.lower_declarations` proves empty extern/signature/global/slot declarations generically. `B2.CallFree` proves absence of try calls, indirect statements/signatures, and TLS for the actual Collatz function. Complete contract composition remains unchecked. |
| O7 AArch64 x0 | SORRY | The active, audited `B2.BackendEntry.xholds_cv_iff` identifies upstream `XHolds` for a UInt64 value with equality of its 64 bits (closure `[propext, Quot.sound]`). Needs O6, backend composition, and its transitive axiom audit. No AArch64-success claim yet. |

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
Remote CI for the audited return bridge `fb3c3ef` and checkpoint `4fedc28` passed:
https://github.com/Th0rgal/turbo-lean/actions/runs/41229563046 and
https://github.com/Th0rgal/turbo-lean/actions/runs/41231617710 .
This verifies the active scope proofs, return bridge, and strict audit in a
fresh default-root build, plus source identity and compiler integration.
The local Lean 4.35 CoreCLI integration build passed; the actual compiler
dispatcher emitted collatz_steps CLIF. `research/b2-compiler-smoke.lean`
records that check and CI runs it too.
CI now also assembles the actual exported AArch64 text with Clang, extracts
`.text` using LLVM objcopy, and compares it byte-for-byte with the exported
binary. The same commands passed locally on the 352-byte artifact with the
recorded SHA-256; the new CI step awaits its first remote result.

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
and telemetry off apply throughout. The active-root rebuild finished successfully
at 17:12 UTC, including the strict transitive axiom audit. FinalDirect is now
the active build step. The new export produced 352 bytes with SHA-256
`ccc8f0891484b6692e2be2315f2e729c2fc4e75831561fb07a7c76884991557b`;
Clang 18's AArch64 assembler produced byte-identical `.text`.

The priority build of `FV.Backend.Proof.LowerDecide` passed at 17:47 UTC.
The old follow-up failed before checking any proof because an empty scratch
namespace directory hid the real B2 library. The corrected checker writes only
B2 outputs into the existing library and uses the provisioned compiler. Durable
replacement job `2b881e4f-a6e2-5984-8304-5e41574f486b` never launched a process;
it was cancelled and acknowledged before starting the local replacement.

`B2.BackendScope` passed at 17:53 UTC and is now active in the root and audit.
Its certified method-level HashMap rewrites avoid reduction through opaque
`System.Platform.getNumBits`; no container implementation or upstream source
changed. Actual `dominatedB` computes through `buildCtx` on the exact input,
without a context snapshot. The active-root and strict transitive audit checks
passed at 17:54 UTC, including subset, dominance, scope, and lookup helpers;
their closures contain only the allowed axioms.

The local `.b2-work/proof_followups.py` process now waits for existing contract
dependencies before checking BackendContracts, then waits for FinalDirect
before checking EndToEnd. Logs are `.b2-work/{scope,contracts,end-to-end}.log`.
The end-to-end draft states explicit x0 equality but remains unchecked.
Pending checks do not establish O6 or O7.

At 18:11 UTC the original FinalDirect scheduler is still checking the upstream
`FV.Backend.Proof.CSemRename` module, with steady CPU use and about 4.6 GiB RSS.
Do not restart that working compiler. Broad priority contract builds began
duplicating this module and were stopped; a narrower auxiliary build was also
stopped before launching a compiler. There is now one native scheduler. Its
implementation probes an entire wave before compiling it, so concurrent native
targets can duplicate work and refresh shared outputs even within one project.
Use the existing build's results for the remaining B2 checks.

An isolated kernel check of the draft's exact `prepared_call_free` statement
passed with closure `[propext]`. Complete O6 composition is still pending the
genuine upstream contract dependencies; this isolated result does not upgrade O6.

At 18:27 UTC the same FinalDirect scheduler was checking the upstream
`FV.Backend.Proof.RefinesInsts` module; the follow-up checker is live and waiting
for genuine contract dependencies. The UInt64 return bridge was promoted from
its passing isolated check into BackendEntry and the strict audit, then used
in the excluded end-to-end draft. BackendEntry, the full active audit, and the
active root passed kernel checks at 18:27 UTC. Full O7 composition remains
unchecked; this bridge does not establish an AArch64 execution by itself.

At 18:54 UTC the complete compilation wave was audited and cached, including
the manifest entry `FV/E2E/RegLevelMachine.lean`. The watcher then stopped the
old scheduler while idle, with no compiler child. Its target exit `-15` records
that deliberate checkpoint, not a completed FinalDirect build; the old wrapper's
exit zero does not change that. The waiting direct follow-up checker was stopped
before transferring ownership of B2 outputs.

Replacement durable job `2a132782-c5ed-5e13-a22e-a9ff65c6af8e` was accepted but
launched no process or output. Cancellation was acknowledged before starting the
local replacement at 18:56:54 UTC. The actual scheduler targets `B2.EndToEnd`
from the proof package, with two compiler workers and four Lean threads each;
logs/status are `.b2-work/e2e-build.{log,pid,exit}`. The completed cache was reused
and distinct compiler children were verified live. No concurrent native scheduler
or direct checker owns the same modules. The host has eight CPUs and 64 GiB RAM;
the resource check reported roughly 43 GiB available memory.

The B2 target checks the claimed result closures while keeping the pinned clifv
sources unchanged. Unrelated native-decided witnesses in clifv are outside those
closures; the B2 axiom policy is unchanged. At 19:13 UTC the workers are checking
`FV.Backend.Proof.LogicImmComplete` and `FV.Backend.Proof.RefinesInsts2`.
No B2 contract or end-to-end check result is available yet, so O6/O7 stay SORRY.
