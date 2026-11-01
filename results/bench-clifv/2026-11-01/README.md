# clifv paired benchmark (A0e) — vast.ai dedicated VM (`rtx4090-a`), 2026-11-01

Status: **running / approaching 720-min managed-VM hard lifetime cap (`2026-11-01T17:45:42Z`)** — Attempt 2 (`--scenarios cold,warm --pairs 1` at `LEAN_NUM_THREADS=6` / `TURBO_LEAN_JOBS=6`) is in untimed `prime-lake: stock` (`989/4556` steps completed, **0 OOMs** in Attempt 2) after Attempt 1 (`LEAN_NUM_THREADS=12` / `TURBO_LEAN_JOBS=12`) hit the 60.13 GiB cgroup limit at step `3470/4556`. **No complete timed pair was reached; result is INCONCLUSIVE (0 pairs, speedup claim disallowed).**

## Provenance

- `turbo-lean` origin/main SHA: `0212d865be1a1093decef308225a0badcdccb526`
- `turbo-lean` release binary SHA-256: `f027951c464151fe4ab751592f8101b1b9b5363e00382440f18163b482a72614` (`turbo-lean 0.1.0`, built with `rustc 1.99.1` and `leanprover/lean4:v4.35.0`)
- `clifv` SHA: `5018b9509dc124154dbe08a5bd85862595d8eab7` (doc default `5018b95`, toolchain `leanprover/lean4:v4.34.1`)
- Host: Vast.ai dedicated VM (`3fc010451603` / `rtx4090-a`, managed ID `mm5zaje5qn`, created `2026-11-01T05:45:42Z`, hard 720-min lifetime ceiling `2026-11-01T17:45:42Z`), Intel(R) Xeon(R) CPU E5-2680 v4 @ 2.40GHz (Broadwell, 14 physical cores / 28 threads), `nproc=28` (cgroup CPU quota `2687999/100000` = 26.88 cores), RAM 62 GiB (cgroup `memory.max` = `64560824320` bytes = 60.13 GiB), swap 9.3 GiB, kernel `Linux 6.17.0-35-generic #35~24.04.1-Ubuntu SMP PREEMPT_DYNAMIC x86_64`, local disk overlay 120G (device 96; `/dev/shm` device 163).
- Parallelism & memory cap (identical for both arms):
  - **Attempt 1 (`attempt1-j12-oom/`)**: `LEAN_NUM_THREADS=12`, `TURBO_LEAN_JOBS=12`, `TURBO_LEAN_MAX_MEMORY_MB=53248` (`06:18Z`–`13:06Z`, 6h48m wall). Untimed `prime-lake: stock` built `3324` modules (`3497/4556` steps) before 12 concurrent `StockCmp*DriverRuns` / `StockRotate*Witness` Lean processes (several 7–10 GiB RSS each) hit cgroup `memory.max` (`64560812032` bytes / `60.13 GiB` at `2026-11-01T12:48:04Z`), causing 6 kernel `oom_kill` events (`Lean exited with code 137` on steps `3470`, `3474`, `3484`, `3485`, `3490`, `3491`). Cleanly stopped (`status: aborted`, 0 pairs) and preserved in `attempt1-j12-oom/` (schema-validated against `scripts/bench_clifv.schema.json`).
  - **Attempt 2 (`attempt2-j6-inprogress/`, active)**: `LEAN_NUM_THREADS=6`, `TURBO_LEAN_JOBS=6`, `TURBO_LEAN_MAX_MEMORY_MB=53248` (started `13:08Z`). Note: Lake 5.0.0 (`v4.34.1`) has no `-j` flag and sizes its build job pool from `LEAN_NUM_THREADS` (verified empirically: 6 concurrent `lean` processes). Peak cgroup memory in Attempt 2: `59.08 GiB` (`63436648448` bytes at `13:35:20Z` during the early `IselData`/`RuleBitops` wave), subsequently steady at `11–20 GiB` with **0 new OOM kills** (`oom 7` / `oom_kill 6` unchanged from Attempt 1 baseline). However, at 2.40 GHz Broadwell single-core speed and 6 jobs, a single cold stock `lake build FV` of 4,554 Lean modules takes ~8–10 hours, while `--scenarios cold,warm --pairs 1` requires 4 full cold/prime builds (`prime-lake` stock + `prime-lake` turbo + `prime-turbo` + `cold-1` stock + `cold-1` turbo + `warm-1`), exceeding Core's 720-minute (12-hour) maximum managed-VM lifetime.
- Telemetry & remote nodes: `TURBO_LEAN_TELEMETRY=off` (benchmark shell only); remote compute node env vars unset.
- Note on GNU `time`: container base image lacked `/usr/bin/time` without root `apt-get install`; extracted Ubuntu Noble `time` (`1.9-0.2build1`) to `$HOME/.local/bin/time` and mapped `/usr/bin/time` in the Python runner via `sitecustomize.py` (stripping `PYTHONPATH` from child `Popen` environments so Lean/Lake/turbo-lean run in an unperturbed environment; verified 13/13 `scripts/test_bench_clifv.py` pass). Neither `scripts/bench_clifv.*` nor `docs/` were modified (`git status --porcelain --untracked-files=no` is empty).

## Results (0 complete pairs — INCONCLUSIVE, no speedup claim)

| Scenario | Arm | #pairs | Median wall (s) | Min wall (s) | Max wall (s) | Status / Verdict |
|---|---|---:|---:|---:|---:|---|
| cold | stock (A) | 0 | n/a | n/a | n/a | INCONCLUSIVE (untimed prime did not complete within 60.13 GiB @ j=12 / 720m VM cap @ j=6) |
| cold | turbo (B) | 0 | n/a | n/a | n/a | INCONCLUSIVE (not reached) |
| warm | stock (A) | 0 | n/a | n/a | n/a | INCONCLUSIVE (not reached) |
| warm | turbo (B) | 0 | n/a | n/a | n/a | INCONCLUSIVE (not reached) |

### Operational takeaway for the next clifv A0e run
1. **Memory envelope**: 60 GiB cgroup RAM OOMs at `LEAN_NUM_THREADS=12` around step `3470/4556` (`StockCmp*DriverRuns` wave, where individual `lean` processes reach 7–10 GiB RSS). Either use a `>= 96–128 GiB` host (`a100` 96 GiB / `h100` 128 GiB or static >=128 GiB host) for `j=12`, or keep `LEAN_NUM_THREADS <= 6..8` on 64 GiB.
2. **Wall-clock / TTL envelope**: On 2.40 GHz Broadwell (`E5-2680 v4`), a single stock `lake build FV` (`4556` targets) takes ~7.5h at `j=12` and >10h at `j=6`, so `cold,warm` (which builds `FV` from scratch at least 4 times including untimed primes) cannot fit inside a 720-minute (12h) managed-VM hard lifetime cap. Run `--scenarios cold --pairs 1` first (skips the 3 untimed `baseline()` builds, cutting required full builds in half), and/or run on a higher-IPC CPU without a 12h reaper ceiling.
