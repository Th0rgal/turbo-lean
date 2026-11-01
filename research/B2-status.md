# B2 status

Baseline: `5508b9f`; clifv `5018b9509dc124154dbe08a5bd85862595d8eab7`.
Checkpoint: 2026-10-31 21:48 UTC. The executable lowering lives in
`lean/LeanNative/Backend/Clif.lean`; `compile-clif` calls that definition.
The active root, including the LNIR-to-AArch64 theorem, and its strict transitive
axiom audit pass kernel checks on Lean 4.34.1. O1–O2 are generic; O3–O7 are
proved for collatz_steps. Generic F64 simulation and safety remain open.

| Obligation | Status | Evidence / remaining work |
| --- | --- | --- |
| O1 subset | PROVED | `B2.Lowering.lower_in_subsetE`, for every successful executable lowering; axioms `[propext, Classical.choice]`. Lowering checks the real `Compile.functionE` and rejects on false. |
| O2 signature | PROVED | `B2.Lowering.lower_sig`, for every successful lowering; axioms `[propext]`. |
| O3 simulation | PROVED (collatz_steps) | `B2.CollatzClif.source_simulation` connects the actual LNIR evaluator to `Clif.runWith` on the actual lowered function for every UInt64 argument pair and arbitrary source heap/CLIF memory. Fuel is `15 * steps.toNat + 5`; the entire initial memory, including the slot-placement oracle, is preserved. Generic F64 simulation remains open. |
| O4 safety | PROVED (collatz_steps) | `B2.BackendEntry.entry_eq` and `returns` establish the exact upstream `ClifEntry` contract. `reachable_step_safe` excludes trapped/stuck steps at every reachable state; `traps_explicit` proves the exact upstream `E2E.TrapsExplicit` premise. `B2.RunSafety.collatz_run_prefix` also excludes trapped/stuck public runs at every fuel. |
| O5 backend artifacts | PROVED (collatz_steps) | `B2.Artifacts.input_eq`, `verifiable`, and `lower` certify the exact instruction-selection artifact from `Backend.lowerFunction`. `B2.Artifacts.prepared`, `spill_alloc`, and `allocation_checked` certify the actual block permutation 0,1,3,2, exact spill allocation, and acceptance by upstream `checkAlloc`. `B2.Artifacts.allocated`, `emitted`, and `laid_out` certify actual AArch64 lowering, emission, and binary layout. `B2.BackendContracts.subset`, `dominated`, and `scope` discharge the exact upstream input predicates; all are active and pass the strict transitive audit. |
| O6 contracts | PROVED (collatz_steps) | `B2.BackendContracts.prepared_call_free` and `no_call_site` certify absence of calls in the actual prepared VCode. `callee_ok`, `try_contract`, `tls_contract`, `extern_contract`, and `indirect_contract` discharge the exact backend contracts from the real absence facts. The unconditional `CalleeOk.pc`/`.ext` hook clauses remain explicit. The compiled-module audit, strict audit, and default root pass; closures contain only the allowed axioms. `B2.Lowering.lower_declarations` also proves empty declarations generically. |
| O7 AArch64 x0 | PROVED (collatz_steps) | `B2.EndToEnd.collatz_to_arm` applies the genuine `E2E.backend_correct_final_of_lower` to the certified concrete pipeline, `BackendEntry.returns`, and discharged contracts. It relates the actual LNIR result to the returned scalar and proves x0 equals `(Nat.repeat B2.CollatzSource.step steps.toNat n).toBitVec`. The actual imported theorem and expanded default root pass the strict transitive audit: `[propext, Classical.choice, Quot.sound]`. |

Every PROVED result is in the default root and `B2.AxiomAudit`, which calls
`Lean.collectAxioms` and rejects closures outside `propext`, `Quot.sound`,
and `Classical.choice`. The O3/O4 and instruction-selection closures use
only these axioms. No `native_decide`, added axioms, or upstream source changes.
The old sorry-bearing `Draft`/`SpecCore`/`SpecE2E` sketches are excluded; their
DivGuarded, untyped-argument, and empty-program statements are superseded
by B2-spec.md. By contrast, `B2.ProbeClif` IS in the import closure (`B2.lean` →
`B2.Division` → `B2.ProbeClif`) and contains only proved facts (not excluded).
`B2.Core` contains definitions only.

## Coverage

- **Inputs**: all `UInt64` inputs `(n, steps)`.
- **CLIF fuel**: `15 * steps.toNat + 5` (`15*steps+5`).
- **Recurrence**: bounded wrapping `UInt64` Collatz step (`B2.CollatzSource.step x = ((x * 2 + x + 1) / 2) + 0` repeated `steps.toNat` times), **not** termination of the mathematical Collatz conjecture.

## Trust boundary

1. **Adequacy of LNIR / CLIF / Arm semantics**: faithfulness of the mechanized LNIR (`LeanNative.Semantics.evalCode`), CLIF (`Clif.runWith` / `Clif.runLoop`), and AArch64 (`Arm.ArmState` / `ArmStepX`) operational models to the intended language and architecture semantics.
2. **Explicit ABI / stack / memory / symbol / hook contracts of `collatz_to_arm`**: the explicit hypotheses of `B2.EndToEnd.collatz_to_arm` (`AbiEntry`, `StackAvail`, `BodyEntry`, `ArgsIn`, `ClifEntry`, `Rel.holds`, `hsym`, `hslot`, and the unconditional `CalleeOk.pc` / `CalleeOk.ext` hook/program-preservation clauses).
3. **Source / dependency identity + build integrity (incl. cross-toolchain runtime correspondence)**: byte-identity between compiler sources (`lean/LeanNative/`, Lean 4.35.0) and proof-package vendored sources (`research/b2-proofs/vendor/LeanNative/`, Lean 4.34.1), exact pinned `eth-act/clifv` / `lean-sys` revisions, Lean kernel / Lake / toolchain integrity, and runtime correspondence across the Lean 4.34.1 proof toolchain and Lean 4.35.0 compiler toolchain.
4. **CLI serialization / artifact export (exercised, not proved)**: `CoreCLI` `compile-clif` argument parsing / CLIF text printing (`Clif.print`) and `Emit.lean` file export of assembly/binary bytes are exercised by smoke/CI checks rather than kernel-proved.
5. **Hardware / OS correspondence (model-level Arm)**: `collatz_to_arm` proves behavior against `clifv`'s model-level AArch64 state machine (`Arm.ArmState`), not physical silicon, caches/MMU, OS loader, or ABI linker behavior.

`B2.Division.total_div_agrees` and `safe_div_executes` have closure
`[propext, Quot.sound]`; `total_mod_agrees` has `[propext]`. They use the
real `Clif.Sem.udiv/urem` and LNIR UInt64 operations. Full generic
instruction-sequence simulation remains open.

Six compiler/proof source pairs are committed byte-identical (Types,
AST, Codec, Value, Eval, Clif). `scripts/check_b2_source_identity.py`
verifies them and a clean pinned clifv. `.github/workflows/b2.yml` enforces
source identity, the proof build, and compiler-toolchain integration.
The local Lean 4.35 CoreCLI integration build passed; the actual compiler
dispatcher emitted collatz_steps CLIF. `research/b2-compiler-smoke.lean`
records that check and CI runs it too.

At 21:44 UTC, the native build of `B2.EndToEnd` completed successfully. An
independent import-based strict audit passed, followed by the expanded
`B2` default-root build, including the O7 audit. `Emit.lean` then exported
the exact proof-backed artifacts. Clang assembly and LLVM `.text`
extraction reproduce all 352 exported bytes, SHA-256
`ccc8f0891484b6692e2be2315f2e729c2fc4e75831561fb07a7c76884991557b`.
Source identity was rechecked after this final build.

The full workflow at `fae880c`, including the unchanged end-to-end proof
source, passed: https://github.com/Th0rgal/turbo-lean/actions/runs/41235235900 .
That revision checked composition separately. O7 is now imported by the
default root and enforced by `B2.AxiomAudit`, so the separate draft step
was removed. Fresh CI for this activation remains pending; prior CI does
not certify the new root/workflow revision.

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
`B2.EndToEnd` is checked, audited, and active in the default root.
Emission uses opaque `mixHash`; certified
Std HashMap/HashSet rewrite lemmas are available. Executable pipeline
inspection reports success through allocation check, emission and layout;
the corresponding kernel certificates now pass.

`CalleeOk.pc` and `.ext` are unconditional even without call sites. The
composition retains those hook/program-preservation premises and uses
site absence only for `.os`. Real ABI, machine-entry, stack availability,
body entry, initial CLIF entry, argument, memory relation, symbol, and
slot-layout premises remain explicit. The source evaluation premise is
supplied for every input by `B2.CollatzSource.collatz_eval`; neither
successful compilation nor the desired machine outcome is assumed.
The theorem concludes `ArmRet`, `ValRel`, and the exact x0 bits. It does
not establish frontend correctness, loader correctness, or hardware execution.

The vendored Types/AST/Codec/Value/Eval/Clif files are byte-identical to
`main` `0212d86`. Value/Eval were re-vendored after #280 (`ac8b089`) added
the fifth `HeapState` field `heapObjs : List HeapObj := []`; Collatz is
scalar-only, so the proofs carry that field unchanged (the empty heap is
now `⟨[], 0, [], [], []⟩`). The existing evaluator and benchmark were not
altered to fit this proof.

## Maintenance

Any PR that changes a vendored compiler source (the files listed in
`scripts/check_b2_source_identity.py`) must re-vendor it byte-identically
into `research/b2-proofs/vendor/LeanNative/`, repair the B2 proofs, and keep
`.github/workflows/b2.yml` green. Never weaken the identity check to pass.

Unrelated native-decided witnesses in the pinned clifv imports are outside
the claimed B2 result closures. Each claimed result is checked transitively
against the allowed list. Historical sorry-bearing sketches remain excluded.
