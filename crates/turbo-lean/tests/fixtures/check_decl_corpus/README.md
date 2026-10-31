# A0d declaration corpus

Minimal, self-contained adaptations of eth-act/clifv at
`5018b9509dc124154dbe08a5bd85862595d8eab7`. Each module credits its source
paths; building clifv is neither required nor performed.

- `Commands`: option wrappers (inline, stacked, indented), private/protected
  declarations, namespaces, sections with variables, local/scoped simp attributes.
- `Proofs`: have-heavy proof, kernel decision, bit-vector decision, native witness,
  structure-valued theorem, named `where` auxiliary, proof-bearing instance, example.
- `Recursion`: mutual definitions and lemmas, structural recursion, simp theorems.

`Dump.lean` independently traverses the elaborated `env.constants`, selects theorem
constants belonging to the current module, demangles private names, and excludes
internal generated declarations, structure projections, and auxiliaries owned by a
parent theorem. These auxiliaries are checked as part of their parent declaration.
Examples are not persisted in the environment; instances are definitions. Neither
is silently counted as an independently addressable theorem.

The Rust discovery test compares the complete sets, including duplicate detection.
The integration test separately requires its explicitly marked mutation inventory to
match the oracle set, then compares stock `lean` and the actual `check --decl` CLI
on the original, a wrong-term mutant, and the restored source, using the same file
and cache. Both tests are unignored and run in the existing `cargo test --release`
CI step. They require Lean; missing tooling fails the tests. Children use
`LEAN_NUM_THREADS=4`. The fixture's `turbo-lean.toml` explicitly admits only the
native decision witnesses' axiom families, alongside the standard project axioms.
No telemetry settings are changed by the tests.

The pre-fix oracle run found 23 user-facing theorems and 19 shards (42 entries in
its symmetric set difference). Missing targets were `Commands.option_indented`,
`Commands.Nested.scoped_zero`, `Commands.Nested.identity`, and `Recursion.odd_self`;
all discovered targets also lacked their namespace prefix. The splitter now tracks
namespace indentation, accepts indented option-wrapper continuations, derives
mutual-block indentation from commands rather than proof continuations, and emits
qualified names. Reconstruction uses the same qualification to disambiguate names.
