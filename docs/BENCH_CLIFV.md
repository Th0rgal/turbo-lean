# Paired clifv benchmark (Track A / A0e)

Run on one otherwise idle **Linux machine**, with Python 3, Git, GNU
`/usr/bin/time`, `nproc`, the pinned Lean toolchain installed through Elan, and a
release build of turbo-lean. No Python packages are required for measurements.
Build turbo-lean from a clean commit and pass that checkout as `--turbo-repo`;
the report records its HEAD, executable hash, and version. The script cannot prove
that an arbitrary executable was built from the supplied checkout: the operator
must ensure they match.

```bash
cargo build --release
scripts/bench_clifv.sh --dry-run --pairs 2
scripts/bench_clifv.sh --turbo "$PWD/target/release/turbo-lean" \
  --pairs 5 --sha 5018b95 \
  --work-dir /scratch/clifv-build-work --output /scratch/clifv-build-results
```

Default scenarios are `cold,warm,proof,statement,import`. `--scenarios warm,proof`
selects and orders a subset; `--pairs` defaults to 5 **per scenario**. A run with
one pair is allowed for diagnostics but cannot produce a speedup claim.
`--timeout SECONDS` limits each build/check (default unlimited); a timeout is an
invalid measurement. Work and output directories must be new and separate.
They are retained for inspection. The script never resets an existing checkout.

`--repo` can point to a local mirror of eth-act/clifv. `--sha` accepts a 7–40 digit
hexadecimal commit ID, resolves it to a full SHA, and checks out that commit in
detached mode. The default resolves to
`5018b9509dc124154dbe08a5bd85862595d8eab7` (the resolved SHA in the report is
authoritative). An alternate commit must still contain the exact edit anchor;
a changed anchor aborts the run instead of silently changing the workload.

To compare project verification with a stock build, use a **separate run**:

```bash
scripts/bench_clifv.sh --turbo "$PWD/target/release/turbo-lean" \
  --turbo-command check --scenarios warm,proof,statement,import --pairs 5 \
  --work-dir /scratch/clifv-check-work --output /scratch/clifv-check-results
```

A is always `lake build` with the pinned project's default targets. B defaults to
`turbo-lean build --project-dir .`; check mode uses `turbo-lean check FV
--project-dir .` over the whole default FV library. Check compares verification
latency against build latency; it does not produce Lake's full build artifacts.
Do not present a check ratio as a build acceleration. Exit-status parity is a
coarse correctness check, not a proof of declaration-discovery/kernel parity;
Track A's A0a/A0d address those separately.

## Experiment and cache state

Every scenario executes **A1, B1, A2, B2, …** sequentially on the same host.
No builds or checks overlap. The order is deliberately ABAB, not ABBA or
randomized. Use an idle machine and inspect the recorded loads for order bias.
The runner creates two independent Git clones with no hard-linked objects or
artifacts. No outputs are copied from A to B. `LEAN_NUM_THREADS` is inherited
unchanged by both arms and recorded (null means unset).
`ELAN_TOOLCHAIN` is set to the pinned checkout's toolchain for both arms;
inherited Lean search paths are removed and turbo's toolchain fallback is disabled.

For non-cold scenarios the runner first performs an untimed stock build in each
arm, then an untimed B invocation to prime B's own persistent caches. Failure of
any prime aborts the experiment. It snapshots each arm's `.lake` independently,
plus B's private persistent cache, staging directory, and temporary directory.
Before **each** timed invocation it stops daemons, restores that arm's baseline,
and applies the selected edit. These copies, source resets, daemon shutdowns,
and all warm-ups are outside the timer. Source timestamps are restored for the
warm no-op; edited files receive a new timestamp. Restoring snapshots prevents
pair 2 from accidentally measuring a no-op after pair 1 already built the edit.

| Scenario | State immediately before each arm |
|---|---|
| `cold` | Empty `.lake`; B also starts with empty private CAS, staging and temporary caches. No prime required. |
| `warm` | Restored successful unedited baseline; no source edit. |
| `proof` | Baseline plus one proof-body edit in `FV/E2E/RegLevelCountIWitness.lean`: `rw [iterN_stepC, countIn_true]` becomes `simpa only [iterN_stepC, countIn_true]`. |
| `statement` | Baseline plus a statement edit in the same file: `iterN_stepC_id` changes from 4 steps / result 11 to 5 steps / result 12. The original proof remains unchanged. |
| `import` | Baseline plus `import Init` at the start of the same file; no other source changes. This is intentionally a redundant import. |

The two theorem edits are intended to remain valid. Both arms see byte-identical
source changes, and the report directory retains per-arm patches. If either
compiler rejects an edit, its actual verdict is recorded. There is no source
rewriting to hide a failure. Cold means empty *project/turbo caches*, not cold OS
page caches or an uninstalled toolchain. The script does not flush kernel caches,
change CPU governors, or change thread counts. Snapshot copying can warm OS page
caches. Run all scenarios on the same machine and report these conditions.

Both arms and all setup/cleanup subprocesses run with
`TURBO_LEAN_TELEMETRY=off`. This is confined to the benchmark process environment;
no tests, global shell settings, project settings, or existing CI telemetry
configuration are modified. Private `TURBO_LEAN_HOME`,
`TURBO_LEAN_STAGING_DIR` (under `/dev/shm`) and `TMPDIR` prevent reuse of a user's
CAS or workers. `TURBO_LEAN_NO_WORKTREE_LINK=1` prevents automatic sharing on
versions supporting that option. `TURBO_LEAN_NO_DAEMON=1` uses foreground work on
versions supporting it, so GNU time can account for that work.

Before and after every timed/prime command the runner invokes `turbo-lean daemon
stop` with the private cache if that subcommand is available. Older versions use
SIGTERM, then SIGKILL if necessary. The fallback targets only this UID's
`turbo-lean`/`turbo_zygote*` processes carrying this invocation's unique environment
marker. It never uses broad `pkill`, kills another user's processes, or stops
unrelated turbo-lean sessions. Cleanup failure aborts the experiment. Private
staging is removed on exit; work directories, disk snapshots and logs remain.

## Reports and decision rule

`results.json` conforms to `scripts/bench_clifv.schema.json`. `results.md` includes
machine provenance, summary tables, exit codes and parity for every pair. The
JSON also contains every raw measurement, command, log path and per-run loads.
Reports are checkpointed after complete pairs; aborted/incomplete experiments
cannot publish a ratio. Logs and GNU time output are under `logs/`.

GNU time records wall seconds, user and system CPU seconds, their sum, and peak
RSS in **KiB** for the command and waited-for children. Peak RSS is the maximum
reported for a process, not simultaneous aggregate tree RSS. Detached work on
versions that ignore the daemon-disable setting may be excluded; do not interpret
those measurements as total-machine CPU/RSS. Cleanup runs outside timing.
GNU time's 0.01-second resolution can yield zero measurements on very fast
no-ops; those remain visible and cannot authorize a ratio.

A pair has parity `PASS` when both exit successfully, `FAIL` when both return
ordinary nonzero verdicts, and `INVALID` on a success/failure disagreement,
missing/malformed timing, timeout, signal death or command-launch failure.
The actual exit codes are retained: two distinct ordinary nonzero exit codes
both mean failure. Any invalid pair makes the runner exit 2 and suppresses every
scenario's ratio. Setup/cleanup errors exit 1; completed diagnostic runs with
matching failures may exit 0 but cannot claim a speedup.

For wall, CPU and RSS in each arm the report gives arithmetic mean, median, and
sample CV (`sample standard deviation / mean`, expressed as a fraction in JSON).
The paired wall ratio is the arithmetic mean of `A_i.wall / B_i.wall`, with a
median and CV, and a deterministic paired percentile bootstrap 95% interval:
resample the N whole-pair ratios with replacement 10,000 times, seed 0; report
the 2.5th and 97.5th percentile order statistics. Pairs are never shuffled between
arms. An interval containing 1 does not demonstrate acceleration.

The ratio is **null** in JSON and withheld in Markdown if **any pair in the
experiment is INVALID**, the experiment is incomplete, any workload in that
scenario failed, there are fewer than two usable observations, any measured
metric has zero mean, or any arm's wall/CPU/RSS CV or paired wall-ratio CV exceeds
**10%**. This deliberately conservative gate also covers resource instability.
Raw means/medians/CVs remain available, but no numerical speedup is printed for
a suppressed scenario. Do not remove outliers, select the fastest pair, or
quote an ungated ratio from raw data as a performance verdict.

Provenance includes `nproc`, total memory, host/platform, load before/after the
experiment and each command, `LEAN_NUM_THREADS`, toolchain and Lean version,
turbo-lean HEAD/version/binary SHA-256, full clifv SHA and environment overrides.
Record any additional workload or host conditions alongside published results.

## CI self-test

The standalone `bench-clifv` workflow runs `--dry-run`, shellcheck, and
`scripts/test_bench_clifv.py`. It validates a deterministic fake **two-pair**
report against the JSON Schema, exercises the ratio gate and invalid verdicts,
and drives the runner using local fake tools and a tiny local Git fixture.
It never downloads or builds clifv or a Lean toolchain. Locally:

```bash
python3 -m pip install 'jsonschema==4.23.0'
shellcheck scripts/bench_clifv.sh
scripts/bench_clifv.sh --dry-run --pairs 2
python3 scripts/test_bench_clifv.py
```

The self-test establishes runner/report behavior. Actual performance claims
require a real pinned clifv run; this PR does not publish measurements.
