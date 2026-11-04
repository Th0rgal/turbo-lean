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
| Is the spec non-vacuous and tight? | `turbo-lean audit-spec <Spec.lean>` |
| Does the diff verify against the base? | `turbo-lean pr-verify --base <ref>` |
| Does the tree meet the repo gate? | `turbo-lean ci-verify --project-dir <dir>` |

The kernel is the accept. A worker report, a green mission, or a missing tool is not.

## What this file no longer is

Model matrices, Best-of-k tables, Empirical-Bayes priors, and warm-pool counts were campaign notes that never became the method. A future campaign that wants a race or a telemetry sink says so in its own document. Select models from what is healthy at dispatch time.
