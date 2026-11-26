# G2a / H2.G measurement results

Numbers for two roadmap leaves (roadmap/HORIZONS.md): **G2a**, the CAS replay hit
rate on the recorded edit sequences, and **H2.G**, the share of loop time in
batched hashing against the 10% line.

Setup: machine label `g2a-ro-192c` (recorded as the host hostname; the live node
name appears nowhere in the artifact), binary `target-g2a/release/turbo-lean`
built at commit `ed26b375` (clean tree), binary sha256
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
the tool reported the fission subshard counters as explicit zeros in every
counted reply):

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
