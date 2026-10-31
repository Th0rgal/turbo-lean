# clifv paired benchmark: GitHub Actions run, 2026-10-31

- Run: https://github.com/Th0rgal/turbo-lean/actions/runs/41214423300 (workflow `.github/workflows/bench-clifv-run.yml`, conclusion `failure`)
- Runner: `scripts/bench_clifv.sh` (A0e, unmodified from main 2a8939e). The turbo-lean checkout is `bench/b1-gha` @ `fcda0ded2aacf1538719f77944445bf179ff96ca`, which is 2a8939e plus the workflow file only.
- Invocation: `--pairs 3 --sha ff90b88aa69bfb7b8fb9ccffc2fe9d02b012b0ed --repo <local bare clone>`, default scenario set `cold,warm,proof,statement,import`, `--turbo-command build`, no `--timeout`. The workflow sent SIGTERM to the benchmark at 19802 s (5 h 30 min) so the report could be written and uploaded before the 350 min job limit.
- clifv SHA (pinned; eth-act/clifv main HEAD when the workflow was written): `ff90b88aa69bfb7b8fb9ccffc2fe9d02b012b0ed`. When the job cloned, main had already moved to `4203e2e7`, but the pinned SHA was used.
- Toolchain: `leanprover/lean4:v4.34.1` (clifv). turbo-lean was built with `leanprover/lean4:v4.35.0` and rustc 1.99.1. turbo binary sha256 `e85241363d0c0e644ee31b429edbc9c560368439c9c66d88e5714156a7963da9`.
- `report.json` is the runner's `results.json` from artifact `bench-clifv-results`. It validates against `scripts/bench_clifv.schema.json` (jsonschema 4.23.0).

## Machine facts

| Fact | Value |
|---|---|
| Runner | GitHub-hosted `ubuntu-latest` (image ubuntu24 20261026.354.1), Ubuntu 24.04.5 LTS |
| `uname -a` | `Linux runnervm48cm3 7.0.0-1017-azure #17~24.04.1-Ubuntu SMP PREEMPT Thu Sep 24 18:46:57 UTC 2026 x86_64 GNU/Linux` |
| CPU | AMD EPYC 9V74 80-Core Processor; `nproc` = 4 (2 cores × 2 threads) |
| Memory | 15 GiB (`MemTotal` 16367524 KiB) + 24 GiB swap file added by the workflow |
| Disk | `/` 145G, 87G free after setup; work dir `/home/runner/work/_temp/bench` (not on the `/dev/shm` device) |
| `LEAN_NUM_THREADS` | unset |
| Load (1/5/15 min) | before 2.39/1.56/0.68, after 4.10/4.32/4.97 |

## Results

Status: **aborted**. **0 pairs completed** in every scenario (3 requested).

| Scenario | Arm | Pairs | Median wall (s) | Min wall (s) | Max wall (s) |
|---|---|---:|---:|---:|---:|
| cold | stock (A) | 0 | n/a | n/a | n/a |
| cold | turbo (B) | 0 | n/a | n/a | n/a |
| warm | stock (A) | 0 | n/a | n/a | n/a |
| warm | turbo (B) | 0 | n/a | n/a | n/a |
| proof | stock (A) | 0 | n/a | n/a | n/a |
| proof | turbo (B) | 0 | n/a | n/a | n/a |
| statement | stock (A) | 0 | n/a | n/a | n/a |
| statement | turbo (B) | 0 | n/a | n/a | n/a |
| import | stock (A) | 0 | n/a | n/a | n/a |
| import | turbo (B) | 0 | n/a | n/a | n/a |

No wall-time measurements exist, so there is **no comparison: inconclusive**. No ratio and no speedup claim.

### INVALID / not measured scenarios

All five scenarios (`cold`, `warm`, `proof`, `statement`, `import`) are unmeasured for the same reason. Because the requested set includes non-cold scenarios, the runner first does an untimed baseline: `lake build FV` in the stock arm (`prime-lake: stock`). That build was still running when the deadline sent SIGTERM. Its log (`logs/prime-lake-stock.log` in the artifact) reaches Lake job **1051 of 4731** after about 5 h 30 min. Lake's per-module times include several modules over 800 s (for example `FV.Backend.Proof.IselShpTab` 801 s and `FV.Backend.Proof.IselEmitTab` 905 s). The runner exited with `bench_clifv: interrupted` and wrote an `aborted` report with no scenarios. No timed command ran, so no pair has a parity verdict.

### Feasibility note (observed, not a measurement)

On this runner class (4 vCPU / 16 GB), a single stock `lake build FV` of clifv at this SHA did not finish in 5.5 h. The protocol needs at least 3 baseline/prime builds plus 3 cold pairs (6 full builds) before any incremental pairs. clifv's own CI splits the same build across many runners in parallel waves. A measured run with this script therefore needs a larger or self-hosted runner, or several jobs that carry state over. A single 350-minute `ubuntu-latest` job cannot provide it.
