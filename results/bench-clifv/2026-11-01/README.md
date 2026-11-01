# clifv paired benchmark (A0e) — vast.ai dedicated VM (`rtx4090-a`), 2026-11-01

Status: **running (`--scenarios cold,warm --pairs 1`)** — untimed `prime-lake: stock` in progress (`619/4556` modules completed; heavy `RuleBitops*` wave currently compiling across 12 concurrent `lean` processes).

## Provenance

- `turbo-lean` origin/main SHA: `0212d865be1a1093decef308225a0badcdccb526`
- `turbo-lean` release binary SHA-256: `f027951c464151fe4ab751592f8163b482a72614` (`turbo-lean 0.1.0`, built with `rustc 1.99.1` and `leanprover/lean4:v4.35.0`)
- `clifv` SHA: `5018b9509dc124154dbe08a5bd85862595d8eab7` (doc default `5018b95`, toolchain `leanprover/lean4:v4.34.1`)
- Host: Vast.ai dedicated VM (`3fc010451603` / `rtx4090-a`), Intel(R) Xeon(R) CPU E5-2680 v4 @ 2.40GHz, `nproc=28` (cgroup CPU quota `2687999/100000` = 26.88 cores), RAM 62 GiB (cgroup `memory.max` = 60.13 GiB), swap 9.3 GiB, kernel `Linux 6.17.0-35-generic #35~24.04.1-Ubuntu SMP PREEMPT_DYNAMIC x86_64`, local disk overlay 120G (device 96; `/dev/shm` device 163).
- Parallelism & memory cap (identical for both arms): `LEAN_NUM_THREADS=12`, `TURBO_LEAN_JOBS=12`, `TURBO_LEAN_MAX_MEMORY_MB=53248`. Peak cgroup memory observed so far: `45.47 GiB` (0 OOM events).
- Telemetry & remote nodes: `TURBO_LEAN_TELEMETRY=off` (benchmark shell only); remote compute node env vars unset.
- Note on GNU `time`: container base image lacked `/usr/bin/time` without root `apt-get install`; extracted Ubuntu Noble `time` (`1.9-0.2build1`) to `$HOME/.local/bin/time` and mapped `/usr/bin/time` in the Python runner via `sitecustomize.py` (stripping `PYTHONPATH` from child `Popen` environments so Lean/Lake/turbo-lean run in an unperturbed environment; verified 13/13 `scripts/test_bench_clifv.py` pass). Neither `scripts/bench_clifv.*` nor `docs/` were modified (`git status --porcelain --untracked-files=no` is empty).

## Results (pending first complete pair)

| Scenario | Arm | #pairs | Median wall (s) | Min wall (s) | Max wall (s) |
|---|---|---:|---:|---:|---:|
| cold | stock (A) | 0 | n/a | n/a | n/a |
| cold | turbo (B) | 0 | n/a | n/a | n/a |
| warm | stock (A) | 0 | n/a | n/a | n/a |
| warm | turbo (B) | 0 | n/a | n/a | n/a |
