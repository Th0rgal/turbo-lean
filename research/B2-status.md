# B2 status

Baseline: `5508b9f`; clifv `5018b9509dc124154dbe08a5bd85862595d8eab7`.
Checkpoint: 2026-10-31 10:25 UTC. The real executable lowering lives in
`lean/LeanNative/Backend/Clif.lean`; `compile-clif` calls that definition.
The proof package's default `lake build` passes on Lean 4.34.1.

| Obligation | Status | Evidence / remaining work |
| --- | --- | --- |
| O1 subset | PROVED | `B2.Lowering.lower_in_subsetE`, for every successful executable lowering; `#print axioms`: `[propext, Classical.choice]`. Lowering checks the real `Compile.functionE` and rejects on false. |
| O2 signature | PROVED | `B2.Lowering.lower_sig`, for every successful lowering; `#print axioms`: `[propext]`. |
| O3 simulation | SORRY | No all-input simulation yet. Kernel smoke checks run actual generated CLIF for Collatz (3,5) → 27 and zero steps, div/mod zero and nonzero, bool-not, nested loops with index shadowing, and mixed-type rejection. These are examples only. |
| O4 safety | SORRY | Safe-denominator operation lemmas pass, but no reachable-state safety or TrapsExplicit proof yet. |
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
Remote CI has not yet been observed. Local Lean 4.35 CoreCLI integration
build is still running at this checkpoint; no AArch64 emission claim.

The active root `B2.lean` excludes the old sorry-bearing SpecCore/SpecE2E
sketches. Their DivGuarded, untyped-argument, and empty-program statements
are superseded by B2-spec.md. `B2.Core` contains definitions only.

Resource note: Lake 5.0.0 / Lean 4.34.1 rejects `lake -j4` with
`unknown short option '-j'`. Builds use `LEAN_NUM_THREADS=4` and named
cones; telemetry is off. Ordinary tactic reduction of the first smoke
test grew past 12 GB, so it was stopped; `decide +kernel` completes the
same real CLIF checks in seconds, with audited allowed axioms.
