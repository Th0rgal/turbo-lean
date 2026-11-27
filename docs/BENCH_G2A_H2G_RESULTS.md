# G2a / H2.G measurement results

Numbers for two roadmap leaves (roadmap/HORIZONS.md): **G2a**, the CAS replay hit
rate on the recorded edit sequences, and **H2.G**, the share of loop time in
batched hashing against the 10% line.

Setup: machine label `g2a-ro-192c` (recorded as the host hostname; the live node
name appears nowhere in the artifact), binary `target-g2a/release/turbo-lean`
built at commit `0773522c` (clean tree), binary sha256
`8ac9a35b81353fb602964d4e1996502769a8718bf73771194ae6785f7b446d80`, 5 trials per
cell, per-check timeout 2400 s, load1 at start/end 84.15 / 63.39, run started
2026-11-26T05:34:09Z. Artifact: `scripts/bench_check_loop_g2a_replay.json`,
produced by `scripts/bench_check_loop.py` (full per-phase medians and PSI
samples live there). Measured set: 4 of 6 workloads; the two others are recorded
below as an unexplained hang (open item, under separate investigation) and a
blocked-as-expected probe.

## G2a: CAS replay hit rate on the recorded edit sequences

Recorded sequence per workload: 5 unedited warm re-checks
(`warm_cache_hit_daemon`), then 5 re-checks each after a distinct proof-body
edit (`warm_edited_proof_daemon`). A hit is a `theorem_cache_hit` reply (proof
replayed from the theorem CAS, no elaboration); a miss is `theorem_verified`.

Run-wide:

| condition | hits/calls | hit_rate |
|---|---|---|
| unedited re-checks | 20/20 | 1.0 |
| edited re-checks | 0/20 | 0.0 |
| overall (1:1 unedited:edited mix) | 20/40 | 0.5 |

The overall rate reflects the sequence's own trial mix, so it is meaningful
only beside its call counts. The bench asserts health per cell: every warm
unedited trial must report `theorem_cache_hit` and every edited trial
`theorem_verified`, or the workload is marked failed. The measured claim is
that those asserts passed on every trial (4 workloads, 5 trials per
condition); the per-condition rates of 1.0 and 0.0 follow from the asserts,
so the rates alone do not distinguish a healthy run from one with dropped
trials. The call counts and health flags carry that information.

Per workload and mode (hits/calls; statuses were uniform per cell:
`theorem_verified` for cold and edited, `theorem_cache_hit` for warm cache-hit;
the fission subshard sums read 0 as recorded by the pre-change script, whose
summing collapsed absent fields to 0, so a reported zero and a never-emitted
field are not distinguishable in this artifact; the current script records
None when no trial reported the field):

| workload | cold_no_daemon | warm_cache_hit_daemon | warm_edited_proof_daemon |
|---|---|---|---|
| batteries_list_lemmas_top | 0/5 | 5/5 | 0/5 |
| batteries_rbtree_lemmas_mid | 0/5 | 5/5 | 0/5 |
| batteries_string_lemmas_top | 0/5 | 5/5 | 0/5 |
| batteries_unionfind_top | 0/5 | 5/5 | 0/5 |

## H2.G: batched-hashing share of loop time, against the 10% line

The measured span is `cas_lookup`: the shard-key BLAKE3 hashing plus the CAS
probe (the key computation in `crates/turbo-lean/src/lake_build/env.rs` runs
inside this span). Share = cas_lookup median / external wall median. Hashing
outside this span is not covered; see the lower-bound paragraph after the
aggregates.

Per cell:

| workload / mode | wall ms | cas_lookup ms | share |
|---|---|---|---|
| batteries_list_lemmas_top / cold | 5381.8 | 0.6 | 0.0111% |
| batteries_list_lemmas_top / warm cache-hit | 2449.3 | 0.7 | 0.0286% |
| batteries_list_lemmas_top / warm edited | 4956.8 | 0.7 | 0.0141% |
| batteries_rbtree_lemmas_mid / cold | 13531.8 | 0.5 | 0.0037% |
| batteries_rbtree_lemmas_mid / warm cache-hit | 3030.3 | 0.7 | 0.0231% |
| batteries_rbtree_lemmas_mid / warm edited | 3630.2 | 0.6 | 0.0165% |
| batteries_string_lemmas_top / cold | 16127.9 | 0.6 | 0.0037% |
| batteries_string_lemmas_top / warm cache-hit | 2454.2 | 0.7 | 0.0285% |
| batteries_string_lemmas_top / warm edited | 2770.3 | 0.6 | 0.0217% |
| batteries_unionfind_top / cold | 5504.9 | 0.5 | 0.0091% |
| batteries_unionfind_top / warm cache-hit | 2346.7 | 0.7 | 0.0298% |
| batteries_unionfind_top / warm edited | 2407.7 | 0.6 | 0.0249% |

Aggregates (sum of cas_lookup medians / sum of wall medians):

| aggregate | share |
|---|---|
| cold_no_daemon | 0.0054% |
| warm_cache_hit_daemon | 0.0272% |
| warm_edited_proof_daemon | 0.0182% |
| warm loop (cache-hit + edited) | 0.0220% |
| all modes incl. cold | 0.0116% |
| worst single cell (unionfind / warm cache-hit) | 0.0298% |

The worst cell (0.0298%) is about 336x under the 10% line; every aggregate is
at least 360x under it.

These shares cover the `cas_lookup` span only, so they are a lower bound on
total hashing time, not the total. Hash call sites also exist in the modules
the `import_refresh` span wraps (the freshness, cache, and DAG code under
`crates/turbo-lean/src/lake_build/` and `crates/turbo-lean/src/module_builder/`,
called inside the span recorded at `crates/turbo-lean/src/check.rs:564`) and
in the declaration-identity cache-key path
(`crates/turbo-lean/src/check/identity.rs:259`), so that hash time lands in
the `import_refresh` and `identity_probe` phases and is not separately
metered. Closed decidable evaluation has no separate phase meter either; it
runs inside the `elaboration` phase, whose whole-phase medians are in the
artifact's `phases_ms_median` tables.

Contention caveat: the run was taken on a busy node (`busy_allowed` true,
load1 84.15 at start, 63.39 at end). One cell, batteries_list_lemmas_top /
warm edited, reads `psi_contended` true (memory.some up to 22.26%, runs
2787-12544 ms, rel_spread 1.9683), and batteries_string_lemmas_top / cold has
rel_spread 0.6493. Wall time is the denominator of every share, so contention
inflates walls and makes the shares read smaller than they would be on a
quiet node.

## G2b: warm CAS-expr replay, on-vs-off delta

Paired sequential runs on one rebuilt binary at `d885a9b8` (sha256
`e4fccb2515a3ac08…`, opt-out string present in the binary with a grep
control), same venue, flags, and label as above; 5 trials per cell; four
active Batteries workloads. Artifacts:
`scripts/bench_check_loop_g2b_on.json` (default) and
`scripts/bench_check_loop_g2b_off.json` (`TURBO_LEAN_NO_WARM_CAS_REPLAY=1`).

Warm cache-hit medians, OFF -> ON, classified by the bench's own
tolerance with OFF as baseline:

| workload | OFF ms | ON ms | delta | band | class |
|---|---|---|---|---|---|
| batteries_list_lemmas_top | 2351.3 | 2461.7 | +4.70% | ±260.1 | unchanged |
| batteries_rbtree_lemmas_mid | 3029.5 | 3088.7 | +1.95% | ±328.0 | unchanged |
| batteries_string_lemmas_top | 2586.0 | 2532.3 | -2.08% | ±529.3 | unchanged |
| batteries_unionfind_top | 2233.8 | 2241.9 | +0.36% | ±248.4 | unchanged |

Cold and warm-edited cells are also all unchanged; no cell of 12 falls
outside the band. The structural reading comes first: this bench cannot
observe the change at all — `run_build_command_with_cas_replay` is reached
only from the `build` CLI and `pr_verify`, never from the `check` path this
bench drives — so the null delta is expected by construction and decides
nothing about the replay's real cost (the runs were also taken on a busy
node, like everything above). What landed per the delta rule then was the
opt-in (`TURBO_LEAN_WARM_CAS_REPLAY=1` enabled; the opt-out still forced off;
the replay path was kept unchanged). The forward options were a
`build`-shaped warm loop or `check`-path wiring measured on a quiet node, or
deleting the path, the leaf's other branch; the next section took the first
and the leaf ended on its deleted branch. With the revert the telemetry mode strings were
renamed (`warm_default` to `warm_opt_in`, `warm_default_error` to
`warm_opt_in_error`), a telemetry contract change; no external consumer of
the old strings was found (pr_verify and the integration tests read zero
occurrences). The deletion then removed the mode field altogether.

## G2b: build-shaped warm loop, the opt-in's own cost

The first forward option above, taken. This section records a feature that
was deleted afterwards (see its end), and it describes
`scripts/bench_build_loop.py` as it was at `ae8afc38`, with the ON and OFF
sides it no longer has. The script drives the `build` path that the
check-loop bench cannot reach. It generates a Lake
fixture of 4 independent modules with 50 distinct `omega` theorems each, runs
one cold `turbo-lean build --seed-shards` into a fresh CAS, then 1 warmup and
20 measured rounds of warm `turbo-lean build`. A round is one call per side,
and the side order alternates ABBA (ON,OFF then OFF,ON) so drift lands on both
sides. Every call is a fresh process with no daemon, telemetry off, and a
private `TURBO_LEAN_HOME`, staging dir and `TMPDIR`. ON sets
`TURBO_LEAN_WARM_CAS_REPLAY=1`; OFF sets neither switch. Each call is held to
its side's expectation: ON must report `cache_hit`, `warm_opt_in` and one
replayed shard per seeded receipt, OFF must report `off`, and any other answer
fails the run. That is the assert the check-loop delta lacked: a side whose
opt-in never reaches the replay cannot pass as a measured null.

Setup: commit `ae8afc38` (clean tree), binary `target/release/turbo-lean`
sha256 `1abed53058499c27d6a5287002f772902c51742d583d08c7a41383670a2bc93e`,
Lean 4.35.0, machine label `g2b-build-192c` (192 CPUs), run started
2026-11-26T18:58:15Z, `/proc/loadavg` `53.18 55.35 84.11` at start and
`66.83 57.98 84.05` at end (`busy_allowed` true), PSI not contended
(memory.some and io.some at most 3.63). Cold seeded build: 26.4 s, 5 modules
compiled, 200 shards seeded. Artifact: `scripts/bench_build_loop_g2b.json`.
Command, as run at `ae8afc38`. It reproduces the table below only at that
commit: the current script has no sides, and its `--out` must not point at this
artifact:

```
python3 scripts/bench_build_loop.py --turbo-lean-bin target/release/turbo-lean \
    --machine-label g2b-build-192c --allow-busy-node \
    --out <results.json>
```

Warm cache-hit builds, 20 measured calls per side:

| side | external wall median ms | IQR ms | tool `elapsed_ms` median | IQR ms | replay per call |
|---|---|---|---|---|---|
| OFF (no switch) | 98.8 | 97.5–102.0 | 87.5 | 86.0–89.5 | `off`, 0 shards |
| ON (`TURBO_LEAN_WARM_CAS_REPLAY=1`) | 113.6 | 110.8–120.9 | 102.5 | 99.8–105.5 | `warm_opt_in`, 200 shards |

ON minus OFF: +14.8 ms (+14.98%) on the external wall and +15.0 ms (+17.14%)
on `elapsed_ms`. Paired by round, the median difference is +14.2 ms (IQR
11.7–18.4) on the wall and +13.5 ms (IQR 11.8–16.0) on `elapsed_ms`; ON was
slower in 17 and 18 of the 20 rounds. That is about 0.07 ms per replayed
shard, which on a receipt-seeded store is a CAS lookup plus a receipt check,
not a kernel replay.

The bench's own tolerance rule (OFF as the baseline, the rule the check-loop
G2b table above used) classes both deltas `unchanged`, with bands of ±148.1 ms
and ±149.0 ms. The bands are that wide because the rule scales with OFF's
max-min spread, and one 154.2 ms OFF call stretches it (OFF ranged 92.6–154.2
ms). The quartiles separate the sides where the band cannot: they do not
overlap, so the opt-in's measured cost is about 15 ms per warm build of this
fixture. Limits: one run, on a loaded node, on a synthetic 200-shard fixture;
the cost should scale with the replayed shard count of a real warm build,
which this run does not measure.

Outcome: the warm trigger was deleted in `cf766a08`. This measurement closed
the leaf on its deleted branch. The replay bought
nothing on this path: the warm build's outputs are already in place, and the
replay only read the CAS, filled derived split caches and reported counters,
so it never gated, repaired or invalidated anything. A measured cost with no
benefit is a change that does not move the benchmark, which the H2 rule
reverts, so the warm trigger was deleted (roadmap/HORIZONS.md row G2b):
`TURBO_LEAN_WARM_CAS_REPLAY` and `TURBO_LEAN_NO_WARM_CAS_REPLAY` are no longer
read, the build JSON and telemetry no longer carry `cas_expr_replay_missing`,
`cas_expr_replay_invalid` or `cas_expr_replay_mode`, and `--replay-cas-expr`
is the only replay. `scripts/bench_build_loop.py` stays as a plain warm-build
bench (one series of warm cache-hit builds, no sides), so it does not
reproduce the table above; `scripts/bench_build_loop_g2b.json` is kept as
that table's record.

## Per-cell peak RSS across the 5 trials (MB, trial order)

From `peak_rss_mb_trials` (the tool's own `peak_rss_mb` reading per check). No
cell is a monotonic riser.

| workload / mode | trial RSS (MB) |
|---|---|
| batteries_list_lemmas_top / cold | 481, 481, 481, 481, 481 |
| batteries_list_lemmas_top / warm edited | 185, 187, 187, 186, 186 |
| batteries_rbtree_lemmas_mid / cold | 531, 528, 529, 528, 526 |
| batteries_rbtree_lemmas_mid / warm edited | 272, 272, 271, 271, 269 |
| batteries_string_lemmas_top / cold | 487, 489, 489, 489, 489 |
| batteries_string_lemmas_top / warm edited | 155, 155, 155, 155, 155 |
| batteries_unionfind_top / cold | 428, 428, 428, 428, 428 |
| batteries_unionfind_top / warm edited | 144, 144, 144, 144, 144 |

Warm cache-hit cells are not recorded: the tool's `theorem_cache_hit` reply
carries no `peak_rss_mb` field (the field is computed only on the verified
path; `crates/turbo-lean/src/check/single_decl.rs`).

## Workloads outside the measured set

**batteries_rbtree_lemmas_top** is an unexplained hang, recorded as an open
item to investigate separately from these results. On the baseline host this
workload's cold median is 10232 ms with rel_spread 0.0044; here every cold
trial ran past the 900 s and then the 2400 s per-check budget, more than 200x
that median, while batteries_rbtree_lemmas_mid in the same file finished cold
in 13.5 s. The warm setup then timed out too. Not retried in this round.
Verbatim from the run logs:

At 2400 s (`g2a-workloads/bench-plain.out`):

```
  cold median=Nonems rel_spread=0.0
ENVIRONMENT ERROR (exit 4): warm setup run for batteries_rbtree_lemmas_top failed (exit -1); cannot measure warm modes: 
timeout after 2400s
```

At 900 s (`g2a-workloads/bench.out`):

```
  cold median=Nonems rel_spread=0.0
ENVIRONMENT ERROR (exit 4): warm setup run for batteries_rbtree_lemmas_top failed (exit -1); cannot measure warm modes: 
timeout after 900s
```

**pfr_more_ruzsa_dist** is blocked as expected and is outside the recorded
sequence by design. Verbatim:

```
blocked: status=blocked_as_expected probe_exits=[1, 1, 1, 1, 1, 1] error_classes=['stale_import_refresh_fail_closed'] median=82.4ms
```

A note on the artifact's own verdict field: it reads `measurement_failed`
(process exit 1) solely because the run was restricted with `--only-workloads`
and, in the bench script as it stood at that run, the skipped
`batteries_rbtree_lemmas_top` entry stayed at status `pending`, which the
health check counts as unmeasured. `measured_nothing` and `comparison_errors`
are both empty, and every measured cell passed the bench's health asserts
(subject to the contention caveat in the H2.G section). The script now records
deliberately filtered workloads as `skipped_by_filter` and reports such runs
as `partial_run` (exit 0); the committed artifact predates that and is kept
as recorded.
