# B2 status

Baseline: `5508b9f`; clifv `5018b9509dc124154dbe08a5bd85862595d8eab7`.
The Markdown spec is now written. No new lowering or audited correctness
result is claimed by this checkpoint.

| Obligation | Status | Evidence / remaining work |
| --- | --- | --- |
| O1 subset | SORRY | Draft statement only; implement lowerDecl and generic subset proof. |
| O2 signature | SORRY | Draft statement only; prove for executable lowering. |
| O3 simulation | SORRY | ProbeClif has local arithmetic agreements; no LNIR-to-CLIF simulation. |
| O4 safety | SORRY | No reachable-state safety or TrapsExplicit proof. |
| O5 backend artifacts | SORRY | No lowered collatz_steps or checked allocation yet. |
| O6 contracts | SORRY | Absence/vacuity facts not yet discharged for generated code. |
| O7 AArch64 x0 | SORRY | Needs O3–O6, backend composition, and transitive axiom audit. |

Existing Kernel.lean uses kernel `decide` for fragment membership and the
concrete LNIR input (3,5) → 27. These do not establish O3 or O7.
The old draft's DivGuarded, untyped argument, and empty-program
statements are superseded by B2-spec.md. Source vendoring/CI identity,
compiler integration, and proof package reproduction remain required.
