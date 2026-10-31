# B2c diagnostic measurement

Workspace layout: `results/` is the turbo-lean results checkout on
`research/b2c-measurement`; sibling `clifv/` is the independent clifv clone.
All committed changes stay under `research/`. No PR is created.

From the workspace parent:

```bash
source results/research/b2c_tool/env.sh
# Install leanprover/lean4:v4.34.1 with elan if absent.
source results/research/b2c_tool/setup_build.sh
cc -shared -fPIC -O2 -I "$B2C_REAL_ROOT/include" \
  results/research/b2c_tool/clock.c -o .b2c-clock.so
python3 -u results/research/b2c_tool/run_experiment.py > .b2c-experiment.log 2>&1
```

The runner stops on failure and checkpoints each complete commit with a signed
commit and ordinary push. Do not use `--retry-build` on a partial transition
without restoring its predecessor state: successful modules from an abandoned
attempt would otherwise remain cached and disappear from the new timings.
Preserve the abandoned attempt, reconstruct the preceding commit from a clean
generated `.lake/build` (untimed and excluded), then measure the full current
transition. Keep recovery and abandoned-attempt evidence separate. A
replacement machine must warm the preceding measured commit before timing its
successor; the runner reconstructs this state when the target artifacts are
missing. Completed pushed data is not remeasured.
When resuming a successful recorded build before extraction/replay completed,
the runner also checks/reconstructs the current commit's artifacts. Otherwise
`lake env lean` could import stale artifacts from the preceding warmup. These
builds are recorded separately under `b2c_data/recovery/`, excluded from all
measurement denominators, and preserve the original `build.json`. The isolated
`verify_recovery.py` probe reproduces the stale import and verifies the rebuild
and subsequent no-op check without touching experiment artifacts.

After all 20 complete commit datasets exist:

```bash
python3 results/research/b2c_tool/report.py
```

Audit the report and any `example_shortfalls` before calling the goal complete.
The report includes kernel/build CPU shares for kind and top-module buckets,
and separate summed-kernel, overhead, and total replay CPU for every commit.
The final audit recomputes aggregate denominators and bucket totals from the
measured transitions, verifies top-module rankings, and requires each example
to belong to its actual reuse/cutoff bucket in that transition.
Report generation alone is not a completion claim. Check per-commit coverage,
all targets, first-parent history, replay sums, build attempts, raw timing groups,
and final staged paths. Push the final audited report on the same branch.

`Extract.lean` serializes explicit expression DAGs; `hash_rows.py` normalizes DAG
references to SHA-256 digests and computes dependency-SCC interfaces and K.
The `Expr-v3-retained-nodes` serializer memoizes by object address while retaining
each expression to prevent address reuse. Addresses and cached `Expr.hash` values
never enter the serialization or digests. Replacing child indices with child
digests makes hashes independent of node allocation, sharing, and index layout.
Fixtures preserve binder names, binder annotations, expression metadata, and
syntax source positions, including distinctions ignored by Lean equality maps.

`IF-v2-canonical-lookups` resolves dependency names using `env.find?` after import.
Every stored occurrence retains its own IF, including repeated theorem names with
different types. Noncanonical occurrences have no incoming name references; their
interfaces use their own payload and the imported bindings of dependencies.
Printed-name collisions are rejected. A per-dataset `.name_resolution.json`
records repeated-name coverage and any differing IF inputs. For a focused check,
run `Extract.lean --duplicate-names <targets>` and hash that dump with
`hash_rows.py <dump> <summary> --duplicates`.
`Replay.lean` is an independent addDecl driver, with a native process CPU
clock from `clock.c`. It never invokes Environment.replay. `run_experiment.py`
joins every stored constant to a timed group and records coverage. K is explicitly
an optimistic, incomplete key and is not used to accept declarations.

`kernel_groups.jsonl.gz` preserves every call. `kernel_by_K.jsonl.gz`, when
present, summarizes repeated observations with median/mean/min/max times. Rows
charge group CPU once to a representative; constructor and recursor rows map to
the generating group without duplicating its time.

The first four-process cold build hit the 16 GiB cap. Its evidence is retained
under `62fa93f0/attempt_1/`; later builds serialize module processes. The local
Lake shim accepts `-j4` (unsupported by this Lake release), and the Lean shim
passes `-j4` to Lean itself. `LEAN_NUM_THREADS=4` remains set. The isolated shims
never modify the shared toolchain installation.

The initial Init validation used thread CPU. FV datasets use process CPU,
identified by `cpu_clock` in replay totals, to include all Lean threads.

The total FV replay CPU counter includes process startup and driver elaboration;
`startup_cpu_ns` and `replay_main_cpu_ns` separate them. Replay wall nanoseconds
cover the main function only, as explicitly labeled in the totals.

After generating the report, backfill any absent per-K timing summaries from
`kernel_groups.jsonl.gz` (older live runners may omit that derived table), commit
and push the final research-only artifacts, then run `audit.py`. Its read-only
gates inspect all 20 datasets, raw replay conservation, complete module cones,
timing keys, referenced examples, push order, and the research-only Git diff.
Manual review of examples and key construction remains part of completion.
While later commits run, `audit.py --commit <prefix>` checks one completed,
pushed dataset, including every distinct-K median/mean/min/max and total. This
mode does not certify the unfinished report; the default still requires all 20
datasets and the final report.

Total build CPU denominators use `tree_cpu_seconds`, measured around the whole
memcap/Lake subprocess tree with child resource usage. The Lean module CPU
subtotal is retained separately; Lake, wrapper and other build work remain in
the total. Build wall and summed module elapsed also remain separate measures.
