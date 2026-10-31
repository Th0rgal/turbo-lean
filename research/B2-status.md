# B2 status

Baseline: `5508b9f`; clifv `5018b9509dc124154dbe08a5bd85862595d8eab7`.
Checkpoint: 2026-10-31 21:20 UTC. The executable lowering lives in
`lean/LeanNative/Backend/Clif.lean`; `compile-clif` calls that definition.
The active root and strict transitive axiom audit pass kernel checks on Lean 4.34.1.

| Obligation | Status | Evidence / remaining work |
| --- | --- | --- |
| O1 subset | PROVED | `B2.Lowering.lower_in_subsetE`, for every successful executable lowering; axioms `[propext, Classical.choice]`. Lowering checks the real `Compile.functionE` and rejects on false. |
| O2 signature | PROVED | `B2.Lowering.lower_sig`, for every successful lowering; axioms `[propext]`. |
| O3 simulation | PROVED (collatz_steps) | `B2.CollatzClif.source_simulation` connects the actual LNIR evaluator to `Clif.runWith` on the actual lowered function for every UInt64 argument pair and arbitrary source heap/CLIF memory. Fuel is `15 * steps.toNat + 5`; the entire initial memory, including the slot-placement oracle, is preserved. Generic F64 simulation remains open. |
| O4 safety | PROVED (collatz_steps) | `B2.BackendEntry.entry_eq` and `returns` establish the exact upstream `ClifEntry` contract. `reachable_step_safe` excludes trapped/stuck steps at every reachable state; `traps_explicit` proves the exact upstream `E2E.TrapsExplicit` premise. `B2.RunSafety.collatz_run_prefix` also excludes trapped/stuck public runs at every fuel. |
| O5 backend artifacts | PROVED (collatz_steps) | `B2.Artifacts.input_eq`, `verifiable`, and `lower` certify the exact instruction-selection artifact from `Backend.lowerFunction`. `B2.Artifacts.prepared`, `spill_alloc`, and `allocation_checked` certify the actual block permutation 0,1,3,2, exact spill allocation, and acceptance by upstream `checkAlloc`. `B2.Artifacts.allocated`, `emitted`, and `laid_out` certify actual AArch64 lowering, emission, and binary layout. `B2.BackendContracts.subset`, `dominated`, and `scope` discharge the exact upstream input predicates; all are active and pass the strict transitive audit. |
| O6 contracts | PROVED (collatz_steps) | `B2.BackendContracts.prepared_call_free` and `no_call_site` certify absence of calls in the actual prepared VCode. `callee_ok`, `try_contract`, `tls_contract`, `extern_contract`, and `indirect_contract` discharge the exact backend contracts from the real absence facts. The unconditional `CalleeOk.pc`/`.ext` hook clauses remain explicit. The compiled-module audit, updated strict audit, and default root passed at 21:20 UTC; closures contain only the allowed axioms. `B2.Lowering.lower_declarations` also proves empty declarations generically. |
| O7 AArch64 x0 | SORRY | The active, audited `B2.BackendEntry.xholds_cv_iff` identifies upstream `XHolds` for a UInt64 value with equality of its 64 bits (closure `[propext, Quot.sound]`). O6 is discharged; `B2.EndToEnd.collatz_to_arm` still needs the backend composition check and its transitive axiom audit. No AArch64-success claim yet. |

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
fresh pre-O6 default-root build, plus source identity and compiler integration.
The local Lean 4.35 CoreCLI integration build passed; the actual compiler
dispatcher emitted collatz_steps CLIF. `research/b2-compiler-smoke.lean`
records that check and CI runs it too.
CI now also assembles the actual exported AArch64 text with Clang, extracts
`.text` using LLVM objcopy, and compares it byte-for-byte with the exported
binary. The same commands passed locally on the 352-byte artifact with the
SHA-256 `ccc8f0891484b6692e2be2315f2e729c2fc4e75831561fb07a7c76884991557b`.
Pre-O6 implementation commit `15673df` passed the entire
remote workflow, including this new byte comparison, source identity, active
proof audit, and compiler integration:
https://github.com/Th0rgal/turbo-lean/actions/runs/41233670162 .
The workflow now also checks the excluded end-to-end draft as a separate step;
this pending check does not establish O7.

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
root and audit. `B2.BackendContracts` is now checked, audited, and active.
`B2.EndToEnd` remains WIP and excluded until its check passes.
Emission uses opaque `mixHash`; certified
Std HashMap/HashSet rewrite lemmas are available. Executable pipeline
inspection reports success through allocation check, emission and layout;
the corresponding kernel certificates now pass.

`CalleeOk.pc` and `.ext` are unconditional even without call sites. The WIP
composition retains these hook/program-preservation premises and uses
site absence only for `.os`. Real ABI, machine-entry, stack, memory,
and symbol premises remain explicit.

Next: kernel-check the LNIR-to-x0 composition against the genuine
`E2E.backend_correct_final_of_lower`, then activate it and audit its full closure.

O6 acceptance at 21:20 UTC: the exact contract source first passed an independent
read-only kernel check and strict closure audit. Its actual native-built module
then passed an import-based strict audit. `B2.BackendContracts` was added to
`B2.lean` and `B2.AxiomAudit`; both the expanded audit and default root passed
kernel checking. Source identity was rechecked: all six byte pairs match and
clifv remains clean at the exact pin. The O6 activation still needs fresh CI.

A single local native scheduler continues to target `B2.EndToEnd`, from
`research/b2-proofs`, with telemetry off, four Lean threads, two compiler
workers, and a 7200-second per-module timeout. Logs/status are
`.b2-work/e2e-build.{log,pid,exit}`. Completed dependency waves are cached;
the scheduler remains live on the remaining backend dependency cone. No
concurrent native scheduler or compiler restart was used for O6 acceptance.
The root/audit checks wrote only outputs outside that target's dependency graph.

The earlier CI run at `fae880c` passed source identity, the pre-O6 active-root
kernel/axiom audit, and the AArch64 byte comparison. Its draft backend-composition
step is still running:
https://github.com/Th0rgal/turbo-lean/actions/runs/41235235900 .
It has not established O7, and does not verify this new O6 root activation.
The contract and end-to-end proof source files themselves are unchanged.

Unrelated native-decided witnesses in the pinned clifv imports are outside
the claimed B2 result closures. The B2 axiom policy is unchanged; each newly
claimed result is checked transitively against the same allowed list.
