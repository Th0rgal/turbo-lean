# B2 proof package

From the repository root, populate the read-only upstream dependency:

```sh
git clone https://github.com/eth-act/clifv.git research/clifv
git -C research/clifv checkout 5018b9509dc124154dbe08a5bd85862595d8eab7
python3 scripts/check_b2_source_identity.py
export TURBO_LEAN_TELEMETRY=off LEAN_NUM_THREADS=4
cd research/b2-proofs
lake build
lake env lean B2/Lowering.lean
lake env lean B2/Division.lean
```

The active root `B2.lean` excludes historical drafts `SpecCore.lean` and
`SpecE2E.lean`. `B2.Core` contains only definitions. The old draft theorem
statements still have sorries and are not correctness evidence.
`B2.AxiomAudit` fails the build if any claimed B2 result transitively
uses an axiom outside propext/Quot.sound/Classical.choice.

Lake 5.0.0 bundled with Lean 4.34.1 rejects `lake -j4` with
`unknown short option '-j'`; use `LEAN_NUM_THREADS=4`. Build only named
modules/dependency cones, never the entire upstream FV library. To build
the eventual composition dependency in the background:

```sh
lake build +FV.E2E.FinalDirect > /tmp/b2-final-cone.log 2>&1 &
```

`decide +kernel` runs decision reduction in Lean's kernel; it is not
`native_decide`. The smoke tests are examples. `B2.CollatzClif.source_simulation` proves
all-input simulation for collatz_steps through the real CLIF entry/run;
`B2.BackendEntry.traps_explicit` proves the exact upstream reachable-safety
contract. `B2.BackendLower`, `B2.BackendAlloc`, and `B2.Artifacts` certify
the concrete pipeline through binary layout. Backend composition is still open. See `../B2-status.md`.

Compiler integration (Lean 4.35.0) uses the same lowerDecl definition:

```sh
cd ../../lean
lake build lean-native-core
.lake/build/bin/lean-native-core compile-clif --canonical-benchmark --decl collatz_steps -o /tmp/collatz.clif
```

Only F64 declarations are accepted; compiling an entire module that also
contains heap/call/parallel kernels fails closed. This command emits
CLIF; it does not by itself certify or emit an AArch64 binary.

Export the exact kernel-certified backend artifacts after the proof build:

```sh
lake env lean --run Emit.lean /tmp/b2-collatz
```

This writes `/tmp/b2-collatz.s` and `/tmp/b2-collatz.bin` (352 bytes).
The exporter imports the active proof root and axiom audit and reads
`B2.Artifacts.fa`/`fb` directly. Locally, Clang's AArch64 assembler produced
identical `.text` bytes from the exported assembly. The bytes currently have
certified pipeline equations; the LNIR-to-x0 composition is still open.
