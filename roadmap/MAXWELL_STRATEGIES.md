# Maxwell execution pointer

How this repository is proved and optimized is the generic Maxwell method, not a strategy written for one compiler campaign. The method lives in the Orb Library skill `maxwell` (`Th0rgal/orb-library`, `skill/maxwell/`), with three thin subdocuments:

- `references/proof.md` — frozen contracts, one owner per open file, one harvest path, push before the VM dies.
- `references/compiler.md` — freeze the spec and attack it before implementation; degrade the quorum when a model family is down.
- `references/optimize.md` — refute fast, measure the real pipeline, delete a pass that does not move it.

This file only names the oracles for `turbo-lean`. It does not choose models, fleet sizes, or telemetry. [`GOALS.md`](./GOALS.md) and [`VALIDATION_CONTRACTS.md`](./VALIDATION_CONTRACTS.md) stay the "what."

## Oracles

Confirm the installed binary with `turbo-lean --version` and `turbo-lean --help` before a prompt names a flag. A flag the binary does not have is not an oracle.

| Question | Command |
| --- | --- |
| Does this declaration kernel-check? | `turbo-lean check <file.lean> --decl <Full.Name> --max-memory-mb 6144 --no-auto-worktree-link` |
| Is the spec non-vacuous and tight? | `turbo-lean --json audit-spec [--policy strict-proofs] [--require-nonempty] <Spec.lean>` |
| Does the diff verify against the base? | `turbo-lean pr-verify --base <ref>` |
| Does the tree meet the repo gate? | `turbo-lean ci-verify --project-dir <dir>` |

The kernel is the accept. A worker report, a green mission, or a missing tool is not.

### Layer 4 `audit-spec` Fail-Closed Contract & Prerequisites

- **Fail-Closed Exit & JSON Semantics**: `turbo-lean --json audit-spec` exits non-zero whenever `"ok": false` — including vacuous/trivial specs, stub definitions, forbidden scope declarations, malformed or unknown keys in `audit-spec.toml` / `turbo-lean.toml`, unknown `--policy` presets, `--decl` filter misses (`"verdict": "decl_not_found"`), `--require-nonempty` on zero-theorem inputs (`"verdict": "no_specs_found"`), or unreadable paths (`"verdict": "error"`). Multi-file batches resolve per-target ancestor policy configs independently so results are permutation-invariant, and cache entries live in private `0700` directories (`--cache-dir`, `TURBO_LEAN_AUDIT_CACHE_DIR`, or private user staging).
- **Witness Provenance**: `audit-spec` distinguishes concrete evaluation refutations (`eval_refuted_postcondition(...)`) from syntactic/structural checks on non-executable domains (`heuristic_unverified_*`); only concrete evaluation or Lean kernel replay constitutes a semantic witness.
- **Stage B Queued Follow-Ups (Cross-Module)**: Forwarding `project_dir` in MCP `turbo_audit_spec`, native diagonal seeding inside `gpu_fastcheck.rs`, transitive compiled-import `csimp` auditing and receipt attestation, retiring `not_applicable` `M11` from `scripts/emitter_mutants.json`, and two-sided `MetaGateSpec` / `CveSubspec` Lean gate tests.
- **Git Runtime Prerequisite (`Git >= 2.46`)**: `pr-verify`, `ci-verify`, and Git-backed Rust integration tests enforce `Git >= 2.46` (`trusted_tools::MIN_GIT`) to mitigate Git worktree/submodule CVEs. On hosts whose system `/usr/bin/git` is older (e.g. `2.43.x`), point `TURBO_LEAN_GIT` at a Git `>= 2.46` binary; `audit-spec` and `tests/audit_spec_cli.rs` run standalone without invoking `git`.

## What this file no longer is

Model matrices, Best-of-k tables, Empirical-Bayes priors, and warm-pool counts were campaign notes that never became the method. A future campaign that wants a race or a telemetry sink says so in its own document. Select models from what is healthy at dispatch time.
