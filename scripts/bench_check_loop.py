#!/usr/bin/env python3
"""M1 pinned benchmark of the `turbo-lean check` loop (roadmap/HORIZONS.md, row M1).

Measures the five pinned `Batteries` declarations and the pinned `PFR`
declaration (expected `blocked` today) across three loop regimes, writes a
results JSON, and — when a baseline is available on the same host — gates the
medians against it. Every performance change in this project must show before
and after numbers from this script; a change that does not move them is
reverted.

The run JSON also records the G2a number (roadmap/HORIZONS.md): the CAS replay
hit rate over the recorded warm edit sequences, per mode (`cas_replay` inside
each measured mode result) and run-wide (top-level `cas_replay`).

A results JSON is meant to be committed, so it records no host path: the
binary is recorded relative to its repository (else by file name), the
repository and scratch root are left out, path-valued settings
(PATH_VALUED_SETTINGS) are recorded as a `<sha256:...>` digest of the value,
and a recorded stderr excerpt names the scratch root, the checkouts, the
binary's directory, this repository, the working directory, the temp dir and
the home dir by placeholder.

Each workload's daemons are stopped when the workload ends. `daemon stop`
waits on turbo-lean's user-wide lifecycle lock, which any other turbo-lean
command of the same user holds while it runs, so the bench gives it
DAEMON_STOP_TIMEOUT_S and then ends whatever the workload's staging namespace
still runs itself, by turbo-lean's own scope rule widened to renamed builds
and one-shot runs (scoped_daemon_processes).

Prerequisite: a fresh `Batteries` clone at the pinned rev fails every check
until each workload's import closure is built. Without the built `.olean`
files the identity probe exits 1 with "produced no `.olean`" and every cold
trial fails, so build the workloads' modules in the clone first:

    lake build Batteries.Data.List.Lemmas Batteries.Data.String.Lemmas \
        Batteries.Recycling.RBTree.Lemmas Batteries.Data.UnionFind.Basic

(a single-workload run needs only its own module, as the M1b noise runs did
with `lake build Batteries.Data.UnionFind.Basic`).

Typical before/after on one machine (the only comparison this script trusts),
with the environment it requires (TURBO_LEAN_GIT must be git >= 2.46) and the
checkout arguments it needs:

    export TURBO_LEAN_GIT=/path/to/git-2.46+ TURBO_LEAN_ALLOWED_CSIMP='*' \
        TURBO_LEAN_ALLOWED_UNSAFE='*' TURBO_LEAN_ALLOWED_IMPLEMENTED_BY='*'
    git checkout main && python3 scripts/bench_check_loop.py \
        --turbo-lean-bin target/release/turbo-lean \
        --batteries-dir /path/to/batteries --pfr-dir /path/to/pfr \
        --out /tmp/m1_main.json
    git checkout <branch> && python3 scripts/bench_check_loop.py \
        --turbo-lean-bin target/release/turbo-lean \
        --batteries-dir /path/to/batteries --pfr-dir /path/to/pfr \
        --baseline /tmp/m1_main.json --strict-comparison --out /tmp/m1_branch.json

`--strict-comparison` means "a comparison really happened": without it a
skipped comparison exits 0 while saying so; with it the after-run fails unless
the two runs were actually compared.

Exit codes:
    0  measurements healthy; comparison passed, or was explicitly skipped and
       flagged (`comparison_skipped_*`), or was not requested (`not_compared`),
       or the run was deliberately partial (`partial_run`, --only-workloads).
       The script never reports a pass for a comparison it skipped.
    1  regression, unhealthy measurement, or (with --strict-comparison) a
       skipped, absent, or partial-run comparison.
    2  usage error.
    3  stale expectation: a workload expected `blocked` (PFR) passed.
    4  environment/setup failure (missing env, wrong revs, wrong git, missing
       or malformed baseline, ...).

Required environment (validated, fail-closed; all recorded in the output,
TURBO_LEAN_GIT as the digest of its path):
    TURBO_LEAN_GIT                     git >= 2.46 binary (system git is refused)
    TURBO_LEAN_ALLOWED_CSIMP=*         imported @[csimp] allowed until P9 lands
    TURBO_LEAN_ALLOWED_UNSAFE=*        imported unsafe defs allowed until P9
    TURBO_LEAN_ALLOWED_IMPLEMENTED_BY=*  imported implemented_by allowed until P9

Python standard library only.
"""

from __future__ import annotations

import argparse
from typing import NamedTuple
import hashlib
import json
import math
import os
import platform
import re
import shutil
import signal
import stat
import statistics
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path

# 2: check_calls renamed classified_calls (a check_calls alias stays in every
#    bucket for old readers), cold modes carry no cas_replay block, fission
#    sums can be None, host blocks carry host_fingerprint, filtered workloads
#    read skipped_by_filter with a partial_run verdict.
SCHEMA_VERSION = 2
NOISE_FLOOR_MS = 25.0
# Between-run floor for the gate: two runs of one binary on one node drift by
# up to ~13% on cold workloads (import_refresh is page-cache sensitive), while
# warm daemon medians stayed within ~2% across runs. The cold floor is 20%.
MIN_REL_TOLERANCE = {"cold_no_daemon": 0.20, "warm_cache_hit_daemon": 0.10,
                     "warm_edited_proof_daemon": 0.10}
SPREAD_SAFETY = 2.0
COVERAGE_GATE = 0.90
BUSY_LOAD_THRESHOLD = 1.0  # one 100%-CPU tenant already poisons warm medians
DEFAULT_TRIALS = 5
DEFAULT_WARMUP = 1
# Per-check wall budget. 900 s is the default; a loaded host can push a cold
# Batteries warm-setup past it (measured 2026-11-25), so a run may widen the
# budget through TURBO_LEAN_BENCH_CHECK_TIMEOUT_S. The override is validated in
# validate_environment() so a malformed value is an environment error (exit 4),
# never a bare crash; the value is recorded with the results.
CHECK_TIMEOUT_S = 900

PINNED_REVS = {
    "batteries": "66e469188fe07963e5cf666c7d4433f45b8131c5",  # tag v4.35.0
    "pfr": "ebe2d96230b1abb190f74592aace441a0f10fe09",        # tag v4.35.0
}

MODES = ("cold_no_daemon", "warm_cache_hit_daemon", "warm_edited_proof_daemon")

# `expected_status` mirrors what `main` does today. When P1 lands and PFR
# passes, this table must be flipped to `active` (the script then exits 3 on
# the old expectation, so the flip is impossible to miss).
WORKLOADS = [
    {"id": "batteries_list_lemmas_top", "repo": "batteries", "expected_status": "active",
     "file": "Batteries/Data/List/Lemmas.lean", "decl": "List.dropLast_eq_eraseIdx", "line": 46},
    {"id": "batteries_string_lemmas_top", "repo": "batteries", "expected_status": "active",
     "file": "Batteries/Data/String/Lemmas.lean", "decl": "String.lt_antisymm", "line": 33},
    {"id": "batteries_rbtree_lemmas_top", "repo": "batteries", "expected_status": "active",
     "file": "Batteries/Recycling/RBTree/Lemmas.lean", "decl": "RBTree.RBNode.min?_reverse",
     "line": 27},
    {"id": "batteries_rbtree_lemmas_mid", "repo": "batteries", "expected_status": "active",
     "file": "Batteries/Recycling/RBTree/Lemmas.lean", "decl": "RBTree.RBNode.Path.ordered_iff",
     "line": 626},
    {"id": "batteries_unionfind_top", "repo": "batteries", "expected_status": "active",
     "file": "Batteries/Data/UnionFind/Basic.lean", "decl": "Batteries.UnionFind.parentD_eq",
     "line": 33},
    {"id": "pfr_more_ruzsa_dist", "repo": "pfr", "expected_status": "blocked",
     "file": "PFR/MoreRuzsaDist.lean", "decl": "rdist_of_neg_le", "line": 55,
     "extra_args": ["--no-auto-worktree-link"],
     "expected_error_classes": ["stale_import_refresh_fail_closed",
                                "declaration_identity_unknown_module_prefix"],
     "note": "Never run without --no-auto-worktree-link: the default purges "
             "prebuilt Mathlib .olean files from the checkout."},
]

REQUIRED_ENV = {
    "TURBO_LEAN_ALLOWED_CSIMP": "*",
    "TURBO_LEAN_ALLOWED_UNSAFE": "*",
    "TURBO_LEAN_ALLOWED_IMPLEMENTED_BY": "*",
}
RECORDED_ENV_VARS = [
    "TURBO_LEAN_GIT", "TURBO_LEAN_ALLOWED_CSIMP", "TURBO_LEAN_ALLOWED_UNSAFE",
    "TURBO_LEAN_ALLOWED_IMPLEMENTED_BY", "TURBO_LEAN_HOME", "TURBO_LEAN_STAGING_DIR",
    "TURBO_LEAN_NO_DAEMON", "TURBO_LEAN_NO_REMOTE_TELEMETRY", "TURBO_LEAN_TELEMETRY",
    "TURBO_LEAN_DAEMON_IDLE_SECS", "TURBO_LEAN_BENCH_CHECK_TIMEOUT_S",
]
# Recorded settings whose values are host paths. A results JSON is committed, so
# these are recorded as a digest of the value, never the path itself; the digest
# still tells two different paths apart, so settings_match keeps comparing them.
PATH_VALUED_SETTINGS = ("TURBO_LEAN_GIT", "TURBO_LEAN_HOME", "TURBO_LEAN_STAGING_DIR")
PATH_DIGEST_PREFIX = "<sha256:"


def recorded_setting(var: str, val):
    """The committed form of one recorded setting.

    A path-valued setting becomes `<sha256:` + the first 12 hex digits of the
    value's SHA-256 + `>`; an already-digested value is kept as it is, so a raw
    path in an older artifact and the digest of the same path compare equal.
    Other settings are recorded verbatim.
    """
    if var not in PATH_VALUED_SETTINGS or not val:
        return val
    if isinstance(val, str) and val.startswith(PATH_DIGEST_PREFIX):
        return val
    return f"{PATH_DIGEST_PREFIX}{hashlib.sha256(str(val).encode()).hexdigest()[:12]}>"


def recorded_settings(environ=None) -> dict:
    """Every RECORDED_ENV_VARS setting of `environ` (default os.environ), committed form."""
    env = os.environ if environ is None else environ
    return {v: recorded_setting(v, env.get(v)) for v in RECORDED_ENV_VARS}


def binary_record(binary: Path, repo_path, sha256: str) -> dict:
    """The binary relative to its repository, else by file name: never a host path."""
    rel = Path(binary).name
    if repo_path:
        try:
            rel = str(Path(binary).relative_to(Path(repo_path).resolve()))
        except ValueError:
            pass
    return {"path": rel, "sha256": sha256}


def scrub_host_paths(text: str, roots) -> str:
    """Replace each (root, placeholder) host root in free text, longest root first.

    A root that is empty or the filesystem root itself is skipped, so a bare `/`
    (a sandbox's home, say) never rewrites every path in the text.
    """
    for root, placeholder in sorted(roots, key=lambda r: len(r[0] or ""), reverse=True):
        if root and len(Path(root).parts) > 1:
            text = text.replace(root, placeholder)
    return text


def remove_tree(root) -> None:
    """Remove a directory the bench made, read-only directories included.

    turbo-lean writes its closure-snapshot store (TURBO_LEAN_HOME/closure-realm/
    closure-snapshots/<digest>/...) with read-only directories, which a plain
    rmtree cannot empty, so every directory under `root` is made owner-writable
    first. Symlinks are never followed or chmodded, and nothing outside `root`
    is touched. What still cannot be removed is reported, never silently left.
    """
    root = Path(root)
    if not root.exists():
        return
    try:
        os.chmod(root, stat.S_IRWXU)
    except OSError:
        pass
    for dirpath, dirnames, _files in os.walk(root, followlinks=False):
        for name in dirnames:
            p = os.path.join(dirpath, name)
            if not os.path.islink(p):
                try:
                    os.chmod(p, stat.S_IRWXU)
                except OSError:
                    pass
    shutil.rmtree(root, ignore_errors=True)
    if root.exists():
        print(f"warning: could not fully remove {root}", file=sys.stderr)


VERDICT_EXIT = {
    "pass": 0, "not_compared": 0,
    "comparison_skipped_host_mismatch": 0, "comparison_skipped_settings_mismatch": 0,
    "comparison_refused_workload_rev_mismatch": 4,
    "comparison_refused_toolchain_mismatch": 4,
    "blocked_workload_unexpected_failure": 4,
    "partial_run": 0,
    "regression": 1, "measurement_failed": 1, "stale_expectation": 3,
}


class BenchEnvError(Exception):
    """Environment or setup failure -> exit 4."""


def utc_now_iso() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


# ---------------------------------------------------------------- statistics

def median(xs):
    return statistics.median(xs) if xs else float("nan")


def rel_spread(xs) -> float:
    """(max - min) / median over measured runs; 0.0 for a single run."""
    if len(xs) < 2:
        return 0.0
    med = median(xs)
    if not med:
        return float("inf")
    return (max(xs) - min(xs)) / med


def tolerance_ms(baseline_median: float, baseline_rel_spread: float, mode: str) -> float:
    """Per-workload gate taken from the baseline's measured spread.

    A fixed 1.15x gate flags noise on workloads whose observed run-to-run
    spread reaches 20-40%, so the tolerance grows with the measured spread
    (SPREAD_SAFETY times) around a per-mode floor, plus NOISE_FLOOR_MS.
    """
    factor = 1.0 + max(MIN_REL_TOLERANCE.get(mode, 0.20),
                       SPREAD_SAFETY * baseline_rel_spread)
    return baseline_median * factor + NOISE_FLOOR_MS


# ------------------------------------------------------------ result shapes

def make_baseline(turbo_lean_commit, host, trials, settings, workloads, **extra):
    base = {
        "schema_version": SCHEMA_VERSION,
        "kind": "baseline",
        "created_utc": utc_now_iso(),
        "turbo_lean_commit": turbo_lean_commit,
        "host": host,
        "trials": trials,
        "settings": settings,
        "workloads": workloads,
    }
    base.update(extra)
    return base


def empty_workload_result(w):
    return {
        "repo": w["repo"], "file": w["file"], "decl": w["decl"],
        "expected_status": w["expected_status"], "status": "pending", "modes": {},
    }


def selected_workloads(args):
    """WORKLOADS filtered by --only-workloads, in table order.

    The filter applies only to the measurement loop: validate_baseline and
    compare_run keep seeing the full table so baseline files stay complete.
    main marks unselected workloads `skipped_by_filter` after the loop, and
    compare_run reports such a run as `partial_run`. Name validation (exit 2
    on an unknown id) happens in main's argparse stage; this helper assumes
    the names are valid.
    """
    raw = getattr(args, "only_workloads", None)
    if not raw:
        return list(WORKLOADS)
    names = {n.strip() for n in raw.split(",") if n.strip()}
    return [w for w in WORKLOADS if w["id"] in names]


def empty_run_result(workloads, trials):
    return {
        "schema_version": SCHEMA_VERSION, "kind": "results", "created_utc": utc_now_iso(),
        "turbo_lean_commit": None, "toolchain": None, "host": {}, "trials": trials,
        "settings": {},
        "workloads": {w["id"]: empty_workload_result(w) for w in workloads},
    }


def mode_result(runs_ms, coverage_ratios, statuses, extra=None, phase_dicts=None,
                psi_lists=None, failed_trials=0, tool_coverage=None,
                fission_dicts=None, rss_mbs=None, replay_mode=False):
    xs = list(runs_ms)
    out = {
        "runs_ms": [round(x, 1) for x in xs],
        "trials": len(xs),
        "failed_trials": failed_trials,
        "median_ms": round(median(xs), 1) if xs else None,
        "spread_ms": round(max(xs) - min(xs), 1) if len(xs) > 1 else 0.0,
        "rel_spread": round(rel_spread(xs), 4) if len(xs) > 1 else 0.0,
        "coverage_ratio_min": round(min(tool_coverage), 4) if tool_coverage else None,
        "coverage_ratio_external_min": round(min(coverage_ratios), 4) if coverage_ratios else None,
        "statuses_observed": sorted(set(statuses)),
    }
    # Per-trial peak RSS as the tool reported it (`peak_rss_mb` in its check
    # JSON), in trial order, so a monotonic riser across trials stays visible.
    # Absent values stay absent rather than 0: a missing reading is not 0 MB.
    if rss_mbs is not None and any(v is not None for v in rss_mbs):
        out["peak_rss_mb_trials"] = list(rss_mbs)
    # G2a (roadmap/HORIZONS.md): a `theorem_cache_hit` call replayed the
    # declaration's proof from the theorem CAS with no elaboration; a
    # `theorem_verified` call ran elaboration (a CAS miss for its target).
    # Any other status (a blocked probe's exit_*) counts as neither, so
    # hits + misses can be below `trials`. Only the warm daemon modes are in
    # the recorded replay sequence (replay_mode); a cold run has no CAS to
    # hit, so it carries no cas_replay block at all.
    if replay_mode:
        hits = sum(1 for s in statuses if s == "theorem_cache_hit")
        misses = sum(1 for s in statuses if s == "theorem_verified")
        if hits or misses:
            replay = {"hits": hits, "misses": misses,
                      "hit_rate": round(hits / (hits + misses), 4)}
            if fission_dicts is not None:
                def fission_sum(key):
                    # None when no trial reported the field: "never emitted"
                    # stays distinguishable from a reported zero, like the
                    # RSS handling above.
                    vals = [d.get(key) for d in fission_dicts
                            if d.get(key) is not None]
                    return sum(int(v) for v in vals) if vals else None
                replay["fission_cached_subshards"] = fission_sum(
                    "fission_cached_subshards")
                replay["fission_verified_subshards"] = fission_sum(
                    "fission_verified_subshards")
            out["cas_replay"] = replay
    if phase_dicts:
        names = sorted({k for pd in phase_dicts for k in pd})
        out["phases_ms_median"] = {
            name: round(median([pd[name] for pd in phase_dicts if name in pd]), 1)
            for name in names
            if any(name in pd for pd in phase_dicts)
        }
    if psi_lists:
        flat_keys = ("cpu.some", "cpu.full", "memory.some", "memory.full",
                     "io.some", "io.full", "load1")

        def flatten(p):
            out = {}
            for k in flat_keys:
                if k == "load1":
                    v = p.get("load1")
                else:
                    res_name, field = k.split(".")
                    v = (p.get(res_name) or {}).get(field)
                out[k] = round(v, 2) if isinstance(v, (int, float)) else None
            return out
        trials = [flatten(p) for trial in psi_lists for p in trial]
        out["psi_trials"] = trials  # per-trial load samples, kept honestly
        maxima = {}
        for k in flat_keys:
            vals = [t[k] for t in trials if isinstance(t[k], (int, float))]
            maxima[k] = round(max(vals), 2) if vals else None
        out["psi_max"] = maxima
        out["psi_contended"] = bool(any(
            isinstance(maxima.get(k), (int, float)) and maxima[k] > 10.0
            for k in ("memory.some", "memory.full", "io.some", "io.full")))
    if extra:
        out.update(extra)
    return out


def active_workload_result(wid, modes):
    return {"id": wid, "status": "ok", "modes": modes}


def blocked_workload_result(exit_code, error_class, median_ms):
    return {
        "status": "blocked_as_expected" if exit_code != 0 else "unexpectedly_passing",
        "expected_status": "blocked",
        "exit_code": exit_code,
        "error_class": error_class,
        "modes": {"cold_no_daemon": {"trials": 1, "median_ms": median_ms,
                                     "runs_ms": [median_ms], "rel_spread": 0.0}},
    }


# --------------------------------------------------- G2a CAS replay hit rate

REPLAY_SEQUENCE_MODES = ("warm_cache_hit_daemon", "warm_edited_proof_daemon")


def summarize_cas_replay(results):
    """G2a (roadmap/HORIZONS.md): CAS replay hit rate on the recorded edit
    sequences, computed from the statuses the tool reported.

    The recorded sequence per active workload is the warm daemon loop this
    script drives: `trials` unedited re-checks of the pinned declaration
    (`warm_cache_hit_daemon`), then `trials` re-checks each after a distinct
    proof-body edit (`warm_edited_proof_daemon`); warmup and settling runs
    are excluded, as everywhere in this script. A check call counts as a CAS
    replay hit when the tool reported `theorem_cache_hit` (proof replayed
    from the theorem CAS, no elaboration) and as a miss when it reported
    `theorem_verified` (elaboration ran). The per-condition rates carry the
    information; the overall rate also reflects the sequence's own
    unedited:edited mix (trials:trials), so it is only meaningful next to
    its call counts, never alone. Blocked workloads and the cold mode are
    outside the recorded sequence and are not counted.
    """
    def bucket(modes):
        hits = misses = failed = other = 0
        fission_cached, fission_verified = [], []
        workloads = []
        for wid, w in sorted((results.get("workloads") or {}).items()):
            if w.get("expected_status") == "blocked":
                continue
            for mode in modes:
                m = (w.get("modes") or {}).get(mode) or {}
                if not m:
                    continue
                # Failed trials never reach the status lists, and healthy
                # trials with a status outside the two counted ones are not
                # classified; both counts ride along so the rates cannot hide
                # them (classified_calls is NOT the number of calls made).
                # They are counted from EVERY replay-mode dict: an all-failed
                # or all-other mode emits no cas_replay block at all, and a
                # total failure is exactly what these counts exist for.
                rep = m.get("cas_replay") or {}
                h, mi = rep.get("hits", 0), rep.get("misses", 0)
                hits += h
                misses += mi
                failed += int(m.get("failed_trials") or 0)
                trials = m.get("trials")
                if isinstance(trials, int):
                    other += max(trials - h - mi, 0)
                for key, acc in (("fission_cached_subshards", fission_cached),
                                 ("fission_verified_subshards", fission_verified)):
                    v = rep.get(key)
                    if v is not None:
                        acc.append(int(v))
                if wid not in workloads:
                    workloads.append(wid)
        calls = hits + misses
        # check_calls is a schema-1 alias of classified_calls, kept for old
        # readers; new code reads classified_calls.
        return {"workloads": workloads, "classified_calls": calls,
                "check_calls": calls,
                "hits": hits, "misses": misses,
                "hit_rate": round(hits / calls, 4) if calls else None,
                "failed_trials": failed,
                "other_status_calls": other,
                "fission_cached_subshards": (sum(fission_cached)
                                             if fission_cached else None),
                "fission_verified_subshards": (sum(fission_verified)
                                               if fission_verified else None)}

    return {
        "sequence": ("per active workload: {t} unedited warm re-checks "
                     "(warm_cache_hit_daemon), then {t} edited re-checks "
                     "(warm_edited_proof_daemon); warmup and settling runs "
                     "excluded").format(t=results.get("trials")),
        "unedited_recheck": bucket(("warm_cache_hit_daemon",)),
        "edited_recheck": bucket(("warm_edited_proof_daemon",)),
        "overall": bucket(REPLAY_SEQUENCE_MODES),
        # Non-blocked workloads whose recorded status is not healthy; their
        # surviving trials are still counted above, so the flag travels with
        # the numbers.
        "non_ok_workloads": sorted(
            wid for wid, w in (results.get("workloads") or {}).items()
            if w.get("expected_status") != "blocked"
            and w.get("status") not in (None, "ok", "skipped_by_filter")),
    }


def validate_baseline(base):
    errs = []
    if not isinstance(base, dict):
        return ["baseline is not a JSON object"]
    for key in ("schema_version", "kind", "created_utc", "turbo_lean_commit",
                "turbo_lean_binary", "workload_revs", "toolchain",
                "host", "trials", "settings", "workloads"):
        if key not in base:
            errs.append(f"missing required key: {key}")
    if "kind" in base and base["kind"] not in ("baseline", "results"):
        errs.append(f"unexpected kind: {base['kind']}")
    if "turbo_lean_dirty" not in base:
        errs.append("baseline_missing_turbo_lean_dirty: turbo_lean_dirty missing "
                    "(provenance requires the marker, exactly boolean false)")
    elif not isinstance(base["turbo_lean_dirty"], bool):
        errs.append(f"baseline_invalid_turbo_lean_dirty: turbo_lean_dirty must be exactly "
                    f"boolean false, got {base['turbo_lean_dirty']!r}")
    elif base["turbo_lean_dirty"]:
        errs.append("baseline_dirty_tree: turbo_lean_dirty is true")
    commit = base.get("turbo_lean_commit")
    if not isinstance(commit, str) or not commit or commit == "not_a_git_checkout":
        errs.append("baseline_missing_turbo_lean_commit: turbo_lean_commit missing, null, or not a git commit")
    binary = base.get("turbo_lean_binary")
    sha = binary.get("sha256") if isinstance(binary, dict) else None
    if not isinstance(sha, str) or not re.fullmatch(r"[0-9a-f]{64}", sha):
        errs.append("baseline_missing_binary_hash: turbo_lean_binary.sha256 missing or invalid")
    revs = base.get("workload_revs")
    if not isinstance(revs, dict) or any(
            not isinstance(revs.get(repo), str) or not revs.get(repo) for repo in PINNED_REVS):
        errs.append("baseline_missing_workload_revs: workload_revs missing or incomplete")
    tc = base.get("toolchain")
    if (not isinstance(tc, dict)
            or not isinstance(tc.get("lean_toolchain"), str) or not tc.get("lean_toolchain").strip()
            or not isinstance(tc.get("lean_version"), str) or not tc.get("lean_version").strip()):
        errs.append("baseline_missing_toolchain: toolchain (lean_toolchain + lean_version) missing or null")
    host = base.get("host") or {}
    for key in ("hostname", "cpu_model", "nproc"):
        if key not in host:
            errs.append(f"host missing {key}")
    settings = base.get("settings") or {}
    for var in ("TURBO_LEAN_GIT", "TURBO_LEAN_ALLOWED_CSIMP",
                "TURBO_LEAN_ALLOWED_UNSAFE", "TURBO_LEAN_ALLOWED_IMPLEMENTED_BY"):
        if not settings.get(var):
            errs.append(f"settings missing {var}: the numbers are only valid with it recorded")
    wl = base.get("workloads") or {}
    for w in WORKLOADS:
        wid = w["id"]
        if wid not in wl:
            errs.append(f"workload missing: {wid}")
            continue
        entry = wl[wid]
        modes = entry.get("modes") or {}
        if entry.get("expected_status") == "blocked":
            continue
        for mode in MODES:
            m = modes.get(mode)
            trials = m.get("trials") if isinstance(m, dict) else None
            if not isinstance(m, dict) or not trials or int(trials) <= 0 \
                    or m.get("median_ms") is None:
                errs.append(f"{wid}/{mode} has no measured trials")
                continue
            med = m["median_ms"]
            if not isinstance(med, (int, float)) or isinstance(med, bool) \
                    or math.isnan(med) or math.isinf(med) or med <= 0:
                errs.append(f"{wid}/{mode} median_ms must be a positive finite "
                            f"number, got {med!r}")
    return errs


# --------------------------------------------------------------- comparison

def host_matches(base, res) -> bool:
    bh, rh = base.get("host") or {}, res.get("host") or {}
    bf, rf = bh.get("host_fingerprint"), rh.get("host_fingerprint")
    lb, lr = bh.get("machine_label"), rh.get("machine_label")
    if (lb or lr) and not (bf and rf):
        # A labeled host records the label AS its hostname, and without a
        # machine-id it records no fingerprint, so two machine-id-less
        # machines sharing a label would pass the hostname fallback below.
        # A label on either side therefore requires both fingerprints; a
        # missing one is a host mismatch.
        return False
    if bf and rf:
        if bf != rf:
            return False
    elif bf or rf:
        # A fingerprint on exactly one side is always a mismatch: the
        # fingerprinted side proves machine-id identity is available, and a
        # bare hostname on the other side cannot verify the same machine.
        # The unfingerprinted side may be either shape — a legacy schema-1
        # entry with no host_fingerprint key at all, or a current entry
        # recording None because the machine exposes no machine-id — and
        # both read the same here. The migration path is --rebaseline.
        return False
    elif bh.get("hostname") != rh.get("hostname"):
        # Neither side has a fingerprint (the key is absent on a legacy
        # schema-1 entry; a current entry without a machine-id records
        # None), so hostnames are compared as before. Unlabeled entries'
        # hostname is the real node name.
        return False
    # The label narrows the match further: both-fingerprints is already
    # required above whenever a label is present, so a shared label never
    # admits two machines, and a label present on only one side is a
    # condition mismatch — the help promises a baseline from a different
    # label is never compared, and "no label" is a different condition.
    if bool(lb) != bool(lr):
        return False
    if lb and lr and lb != lr:
        return False
    return True


def settings_match(base, res) -> bool:
    """Every recorded TURBO_LEAN_* setting must agree, not just four keys.

    Both sides are read in committed form (recorded_setting), so a raw path in an
    older artifact and the digest of the same path compare equal."""
    key = lambda s: {v: recorded_setting(v, s.get(v)) for v in RECORDED_ENV_VARS}
    return key(base.get("settings") or {}) == key(res.get("settings") or {})


def workload_revs_match(base, res) -> bool:
    br, rr = base.get("workload_revs") or {}, res.get("workload_revs") or {}
    return bool(br) and bool(rr) and all(
        br.get(repo) and br.get(repo) == rr.get(repo) for repo in PINNED_REVS)


def toolchain_key(entry):
    tc = entry.get("toolchain") if isinstance(entry, dict) else None
    if not isinstance(tc, dict):
        return None
    return {"lean_toolchain": tc.get("lean_toolchain"),
            "lean_version": tc.get("lean_version")}


def toolchain_matches(base, res) -> bool:
    bt, rt = toolchain_key(base), toolchain_key(res)
    return (bt is not None and rt is not None
            and bool(bt["lean_toolchain"]) and bool(bt["lean_version"])
            and bt == rt)


class TrialSplit(NamedTuple):
    """Per-mode series over the HEALTHY trials (in trial order), plus the
    count of failed ones. Named fields so a new series cannot silently
    misalign positional use; a NamedTuple rather than a dataclass because
    external tools load this script with spec_from_file_location without
    registering it in sys.modules, and under `from __future__ import
    annotations` a dataclass resolves its field strings through sys.modules
    at class creation and dies there. Positional unpacking stays available."""
    runs: list
    covs: list
    tool_covs: list
    statuses: list
    phases: list
    psis: list
    fissions: list
    rss_mbs: list
    failed: int


def trial_failed(r) -> bool:
    """A trial whose command exited non-zero, reported no status or a failed
    one is a failed measurement, even if a time was parsed."""
    if r.get("exit_code") != 0:
        return True
    j = r.get("json")
    if not isinstance(j, dict):
        return True
    status = j.get("status")
    if not status or status in ("failed", "error"):
        return True
    return False


def compare_run(baseline, res):
    """Gate `res` against `baseline`. Never passes a comparison it skipped."""
    verdict = {
        "verdict": None, "regressions": [], "improvements": [], "measured_nothing": [],
        "comparison_errors": [], "unexpected_successes": [],
        "unexpected_blocked_failures": [], "pfr_status": None,
        "skipped_reason": None, "same_binary": None,
        "baseline_commit": baseline.get("turbo_lean_commit") if baseline else None,
        "run_commit": res.get("turbo_lean_commit"),
        "baseline_binary_sha256": ((baseline.get("turbo_lean_binary") or {}).get("sha256")
                                   if baseline else None),
        "run_binary_sha256": (res.get("turbo_lean_binary") or {}).get("sha256"),
        "gates": {},
    }
    for wid in baseline["workloads"] if baseline else {}:
        if wid not in res["workloads"]:
            verdict["comparison_errors"].append(
                f"workload {wid} is in the baseline but not in this run's results")
    for wid in res["workloads"]:
        if baseline and wid not in baseline["workloads"]:
            verdict["comparison_errors"].append(
                f"workload {wid} is in this run's results but not in the baseline")
    bad_blocked = sorted(
        wid for wid, w in res["workloads"].items()
        if w.get("expected_status") == "blocked"
        and w.get("status") == "blocked_unexpected_failure")
    if bad_blocked and not verdict["comparison_errors"]:
        verdict["unexpected_blocked_failures"] = [
            {"workload": wid,
             "probe_error_classes": res["workloads"][wid].get("probe_error_classes"),
             "expected_error_classes": res["workloads"][wid].get("expected_error_classes")}
            for wid in bad_blocked
        ]
        verdict["pfr_status"] = res["workloads"].get("pfr_more_ruzsa_dist", {}).get("status")
        verdict["verdict"] = "blocked_workload_unexpected_failure"
        verdict["skipped_reason"] = (
            f"blocked workload failed with unexpected error class: "
            f"{verdict['unexpected_blocked_failures']}")
        return verdict
    healthy = all(
        (w.get("status") in ("ok", "skipped_by_filter")
         if w.get("expected_status") != "blocked"
         else w.get("status") in ("blocked_as_expected", "unexpectedly_passing",
                                  "skipped_by_filter"))
        for w in res["workloads"].values()
    ) and not verdict["comparison_errors"]
    if not healthy:
        verdict["verdict"] = "measurement_failed"
        return verdict
    verdict["pfr_status"] = res["workloads"]["pfr_more_ruzsa_dist"]["status"]
    # An unexpected success of a blocked workload is a stale expectation no
    # matter whether a comparison happens: it must exit 3 even without a
    # baseline, and even when the comparison would be skipped.
    unexpected = sorted(
        wid for wid, w in res["workloads"].items()
        if w.get("expected_status") == "blocked" and w.get("status") == "unexpectedly_passing")
    if unexpected:
        verdict["unexpected_successes"] = unexpected
        verdict["verdict"] = "stale_expectation"
        return verdict
    # A --only-workloads run is deliberately partial: it can neither pass nor
    # gate the full table, and its exit must stay distinguishable from a real
    # failure (exit 0 under VERDICT_EXIT, where measurement_failed exits 1).
    skipped = sorted(
        wid for wid, w in res["workloads"].items()
        if w.get("status") == "skipped_by_filter")
    if skipped:
        verdict["verdict"] = "partial_run"
        verdict["skipped_reason"] = (
            "run restricted with --only-workloads; unmeasured: "
            + ", ".join(skipped))
        return verdict
    if baseline is None:
        verdict["verdict"] = "not_compared"
        verdict["skipped_reason"] = "no baseline given or found"
        return verdict
    b_sha = verdict["baseline_binary_sha256"]
    r_sha = verdict["run_binary_sha256"]
    verdict["same_binary"] = bool(b_sha and r_sha and b_sha == r_sha)
    if not workload_revs_match(baseline, res):
        verdict["verdict"] = "comparison_refused_workload_rev_mismatch"
        verdict["skipped_reason"] = (
            f"baseline workload_revs={baseline.get('workload_revs')} != "
            f"run workload_revs={res.get('workload_revs')}; "
            "refusing comparison across different workload revisions")
        return verdict
    if not toolchain_matches(baseline, res):
        verdict["verdict"] = "comparison_refused_toolchain_mismatch"
        verdict["skipped_reason"] = (
            f"baseline toolchain={toolchain_key(baseline)} != "
            f"run toolchain={toolchain_key(res)}; "
            "refusing comparison across different Lean toolchains")
        return verdict
    if not host_matches(baseline, res):
        bh, rh = baseline.get("host") or {}, res.get("host") or {}

        def fp12(h):
            fp = h.get("host_fingerprint")
            return fp[:12] if isinstance(fp, str) and fp else None
        verdict["verdict"] = "comparison_skipped_host_mismatch"
        verdict["skipped_reason"] = (
            f"baseline host {bh.get('hostname')}/{bh.get('machine_label')}"
            f" (fingerprint {fp12(bh)}) != this host "
            f"{rh.get('hostname')}/{rh.get('machine_label')}"
            f" (fingerprint {fp12(rh)}); "
            "a baseline from another machine or condition proves nothing here")
        return verdict
    if not settings_match(baseline, res):
        verdict["verdict"] = "comparison_skipped_settings_mismatch"
        verdict["skipped_reason"] = "TURBO_LEAN_* settings differ from the baseline run"
        return verdict
    for w in WORKLOADS:
        wid = w["id"]
        base_w, res_w = (baseline.get("workloads") or {}).get(wid), res["workloads"].get(wid)
        if res_w is None or base_w is None:
            verdict["comparison_errors"].append(
                f"workload {wid} present on one side only")
            verdict["verdict"] = "measurement_failed"
            continue
        if res_w.get("status") == "unexpectedly_passing":
            verdict["unexpected_successes"].append(wid)
            verdict["verdict"] = "stale_expectation"
            continue
        if res_w.get("expected_status") == "blocked" or base_w.get("expected_status") == "blocked":
            continue  # blocked probes record one fail-fast mode; nothing to gate
        for mode in MODES:
            b, r = (base_w.get("modes") or {}).get(mode), (res_w.get("modes") or {}).get(mode)
            if b is None or b.get("median_ms") is None:
                verdict["comparison_errors"].append(
                    f"baseline has no measured median for {wid}/{mode}")
                verdict["verdict"] = "measurement_failed"
                continue
            if r is None or not r.get("trials") or r.get("median_ms") is None:
                verdict["regressions"].append(f"{wid}/{mode}")
                verdict["measured_nothing"].append(f"{wid}/{mode}")
                verdict["gates"][f"{wid}/{mode}"] = {"verdict": "measured_nothing"}
                continue
            tol = tolerance_ms(b["median_ms"], b.get("rel_spread", 0.0), mode)
            band = tol - b["median_ms"]  # noise band, applied in BOTH directions
            new = r["median_ms"]
            delta = new - b["median_ms"]
            if new > tol:
                cls = "regressed"
            elif new < b["median_ms"] - band:
                cls = "improved"
            else:
                cls = "unchanged"
            gate = {"baseline_median_ms": b["median_ms"], "baseline_rel_spread": b.get("rel_spread"),
                    "new_median_ms": new, "delta_ms": round(delta, 1),
                    "delta_pct": round(100.0 * delta / b["median_ms"], 2),
                    "noise_band_ms": round(band, 1), "verdict": cls}
            if cls == "regressed":
                gate["over_by_ms"] = round(new - tol, 1)
                verdict["regressions"].append(f"{wid}/{mode}")
            elif cls == "improved":
                gate["under_by_ms"] = round((b["median_ms"] - band) - new, 1)
                verdict["improvements"].append(f"{wid}/{mode}")
            verdict["gates"][f"{wid}/{mode}"] = gate
    if verdict["verdict"] is None:
        verdict["verdict"] = "pass" if not verdict["regressions"] else "regression"
    if verdict["verdict"] in ("pass", "regression"):
        cells = sorted((k, g) for k, g in verdict["gates"].items()
                       if g.get("baseline_median_ms") is not None)
        n_reg, n_imp = len(verdict["regressions"]), len(verdict["improvements"])
        line = (f"bench_check_loop: {verdict['verdict']} | {len(cells)} cells: "
                f"{n_reg} regressed, {n_imp} improved, {len(cells) - n_reg - n_imp} unchanged")
        if cells:
            worst_name, worst = max(cells, key=lambda kv: kv[1]["delta_pct"])
            line += (f" | worst: {worst_name} {worst['delta_ms']:+.1f} ms "
                     f"({worst['delta_pct']:+.2f}%)")
        verdict["summary"] = line
    return verdict


# ------------------------------------------------------- proof-body editing

BENCH_HAVE_RE = re.compile(r"^ *have _m1_bench_trial_\d+ : True := trivial\n", re.M)


def insert_bench_have(decl_src: str, trial_index: int) -> str:
    """Insert a unique `have` into a proof body to force a CAS miss.

    `:= by` proofs gain one tactic line; term-style proofs are wrapped in a
    parenthesized term-level `have` (same statement, edited proof).
    """
    marker = ":= by"
    pos = decl_src.find(marker)
    if pos >= 0:
        end = pos + len(marker)
        if decl_src[end:end + 1] != "\n":
            raise BenchEnvError("':= by' is not at end of its line; cannot insert bench have")
        return (decl_src[:end] + f"\n  have _m1_bench_trial_{trial_index} : True := trivial"
                + decl_src[end:])
    sep = decl_src.rfind(":=")
    if sep < 0:
        raise BenchEnvError("proof has neither ':= by' nor ':='; cannot insert bench have")
    rest = decl_src[sep + 2:]
    term = rest.strip()
    trailing = rest[len(rest.rstrip()):]
    if not term:
        raise BenchEnvError("empty term-style proof; cannot insert bench have")
    return (decl_src[:sep] + f":= (have _m1_bench_trial_{trial_index} : True := trivial; "
            + term + ")" + trailing)


TERM_UNWRAP_RE = re.compile(r"\(have _m1_bench_trial_\d+ : True := trivial; (.*)\)",
                            re.S)


def remove_bench_have(decl_src: str) -> str:
    """Inverse of insert_bench_have."""
    unwrapped = TERM_UNWRAP_RE.sub(r"\1", decl_src)
    return BENCH_HAVE_RE.sub("", unwrapped)


TOP_LEVEL_START_RE = re.compile(
    r"^(theorem|lemma|def|abbrev|instance|structure|class|namespace|section|end|open|"
    r"axiom|example|unsafe|partial|noncomputable|private|protected|\[|@|/-|/-!|--)",
)


def locate_decl_block(src: str, decl: str, prefer_line=None):
    """Return (start, end) char offsets of the declaration's source block.

    Names can be attribute-prefixed (`@[simp] theorem foo`) and short names can
    be reused in sibling namespaces, so `prefer_line` disambiguates.
    """
    short = decl.split(".")[-1]
    kw_re = re.compile(
        rf"^(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|unsafe\s+|noncomputable\s+|"
        rf"partial\s+)*(?:theorem|lemma|def|abbrev|instance)\s+{re.escape(short)}\b")
    lines = src.splitlines(keepends=True)
    matches = [i for i, line in enumerate(lines) if kw_re.match(line)]
    if not matches:
        raise BenchEnvError(f"declaration {decl} not found in workload file")
    if prefer_line is not None and len(matches) > 1:
        start_line = min(matches, key=lambda i: abs((i + 1) - prefer_line))
    else:
        start_line = matches[0]
    end_line = len(lines)
    for j in range(start_line + 1, len(lines)):
        if TOP_LEVEL_START_RE.match(lines[j]):
            end_line = j
            break
    start = sum(len(x) for x in lines[:start_line])
    end = sum(len(x) for x in lines[:end_line])
    return start, end, start_line + 1


# ------------------------------------------------------------ host identity

def read_machine_id() -> str:
    """The machine-id, or '' when unreadable (containers commonly lack it)."""
    try:
        return Path("/etc/machine-id").read_text().strip()
    except OSError:
        return ""


def host_id(machine_label):
    cpu_model = "unknown"
    try:
        for line in Path("/proc/cpuinfo").read_text().splitlines():
            if line.startswith("model name"):
                cpu_model = line.split(":", 1)[1].strip()
                break
    except OSError:
        pass
    mem_gb = None
    try:
        for line in Path("/proc/meminfo").read_text().splitlines():
            if line.startswith("MemTotal"):
                mem_gb = round(int(line.split()[1]) / 1e6, 1)
                break
    except OSError:
        pass
    machine_id = read_machine_id()
    # The fingerprint is what host_matches compares: it pins the physical
    # machine without putting its name in the JSON (a label is a condition
    # tag two machines could share, so it cannot carry the machine identity).
    # Without a machine-id it is None, never sha256(hostname + "\0"): that
    # would be a confirmable hash of the node name, and ephemeral containers
    # (fresh hostname each run) would never match each other. host_matches
    # then falls back to the hostname/label comparison.
    fingerprint = (hashlib.sha256(
        (platform.node() + "\0" + machine_id).encode()).hexdigest()
        if machine_id else None)
    return {
        # With a label the label IS the recorded hostname: the live node name
        # stays out of the JSON entirely (the label exists so results never
        # carry the machine's real name; see g2a-workloads/DIAG-warm-modes.md).
        "hostname": machine_label if machine_label else platform.node(),
        "machine_label": machine_label,
        "host_fingerprint": fingerprint,
        "kernel": f"{platform.system()} {platform.release()}",
        "cpu_model": cpu_model,
        "nproc": os.cpu_count(),
        "mem_gb": mem_gb,
    }


def parse_psi_lines(text: str):
    """Parse one /proc/pressure file: lines are `some avg10=… …` and
    `full avg10=… …`. Unreadable or missing fields are null, never 0.0 —
    a failed read must not masquerade as a quiet system."""
    out = {"some": None, "full": None}
    for line in (text or "").splitlines():
        m = re.match(r"^(some|full)\s+avg10=([0-9.]+)", line.strip())
        if m:
            try:
                out[m.group(1)] = float(m.group(2))
            except ValueError:
                pass
    return out


def sample_psi():
    psi = {}
    for name in ("cpu", "memory", "io"):
        try:
            psi[name] = parse_psi_lines(Path(f"/proc/pressure/{name}").read_text())
        except OSError:
            psi[name] = {"some": None, "full": None}
    try:
        psi["load1"] = round(os.getloadavg()[0], 2)
    except (OSError, AttributeError):
        psi["load1"] = None
    return psi


def psi_contended(psi) -> bool:
    return psi.get("memory", 0.0) > 10.0 or psi.get("io", 0.0) > 10.0


# ------------------------------------------------------------ git utilities

def git_version(git_bin: str):
    try:
        out = subprocess.check_output([git_bin, "--version"], text=True, timeout=10)
    except (OSError, subprocess.SubprocessError) as e:
        raise BenchEnvError(f"TURBO_LEAN_GIT={git_bin} is not runnable: {e}") from e
    m = re.search(r"git version (\d+)\.(\d+)", out)
    if not m:
        raise BenchEnvError(f"cannot parse git version from: {out.strip()}")
    return (int(m.group(1)), int(m.group(2))), out.strip()


def repo_commit(git_bin: str, repo: Path):
    try:
        rev = subprocess.check_output([git_bin, "-C", str(repo), "rev-parse", "HEAD"],
                                      text=True, stderr=subprocess.DEVNULL, timeout=10).strip()
        # Tracked changes only: untracked scratch (e.g. __pycache__) must not
        # make a clean tree look dirty, but a leftover edit always does.
        dirty = subprocess.run([git_bin, "-C", str(repo), "status", "--porcelain",
                                "--untracked-files=no"],
                               capture_output=True, text=True, timeout=10).stdout.strip() != ""
        return rev, dirty
    except (OSError, subprocess.SubprocessError):
        return None, None


def turbo_lean_commit_for(binary: Path, git_bin: str):
    repo = binary.resolve().parent
    while repo != repo.parent:
        if (repo / ".git").exists():
            rev, dirty = repo_commit(git_bin, repo)
            if rev:
                return rev, dirty, str(repo)
        repo = repo.parent
    return "not_a_git_checkout", None, None


def detect_toolchain(dirs):
    tc_by_repo = {}
    for repo in sorted(dirs):
        p = dirs[repo] / "lean-toolchain"
        if not p.is_file():
            raise BenchEnvError(f"{repo} lean-toolchain file missing: {p}")
        val = p.read_text().strip()
        if not val:
            raise BenchEnvError(f"{repo} lean-toolchain file is empty: {p}")
        tc_by_repo[repo] = val
    unique = sorted(set(tc_by_repo.values()))
    if len(unique) != 1:
        raise BenchEnvError(
            f"workload lean-toolchain files disagree ({tc_by_repo}); "
            "all pinned workloads must share one Lean toolchain")
    lean_tc = unique[0]
    lean_bin = shutil.which("lean")
    if not lean_bin:
        elan_lean = Path.home() / ".elan" / "bin" / "lean"
        if elan_lean.is_file():
            lean_bin = str(elan_lean)
    if not lean_bin:
        raise BenchEnvError("lean binary not found on PATH (needed to record lean --version)")
    try:
        lean_ver = subprocess.check_output(
            [lean_bin, "--version"], cwd=str(dirs["batteries"]),
            text=True, stderr=subprocess.STDOUT, timeout=30).strip().splitlines()[0].strip()
    except (OSError, subprocess.SubprocessError, IndexError) as e:
        raise BenchEnvError(f"failed to run `{lean_bin} --version`: {e}") from e
    if not lean_ver:
        raise BenchEnvError(f"`{lean_bin} --version` produced empty output")
    return {"lean_toolchain": lean_tc, "lean_version": lean_ver, "by_repo": tc_by_repo}


# ----------------------------------------------------------- daemon control

# `daemon stop` first takes turbo-lean's one user-wide lifecycle lock
# exclusively, and every running turbo-lean command of the same user holds that
# lock shared, so on a shared machine a scoped stop waits on unrelated work, and
# overlapping commands can keep it waiting indefinitely. The bench gives it this
# long, then ends whatever its own staging namespace still has running itself.
DAEMON_STOP_TIMEOUT_S = 20
DAEMON_TERM_GRACE_S = 2.0
DAEMON_KILL_GRACE_S = 1.0
# Worker invocations turbo-lean's own scoped stop leaves alone.
_AUDIT_WORKER_FLAGS = (b"--audit-modules", b"--decl-identity", b"--public-sig")


def _is_serve_command(args) -> bool:
    """turbo-lean's is_serve_command: the first command word after argv[0] is `serve`."""
    words = iter([a for a in args if a][1:])
    for a in words:
        if a in (b"--cache-dir", b"--max-memory-mb", b"--telemetry"):
            next(words, None)
        elif not a.startswith(b"-"):
            return a == b"serve"
    return False


def _proc_state_and_start(proc_dir: Path):
    """(state letter, starttime) from /proc/<pid>/stat, or (None, None)."""
    try:
        text = (proc_dir / "stat").read_text()
    except OSError:
        return None, None
    _comm, sep, rest = text.rpartition(") ")
    fields = rest.split() if sep else []
    if len(fields) < 20:
        return None, None
    return fields[0], fields[19]  # fields 3 and 22


def scoped_daemon_processes(staging, bin_path, proc_root: Path = Path("/proc")) -> list:
    """(pid, starttime) of every live process of this user in one staging namespace.

    turbo-lean's own scoped-stop rule (zygote/daemon.rs, owned_lifecycle_process):
    `serve` daemons carrying TURBO_LEAN_DAEMON=1 and zygote workers (except the
    audit helpers) whose TURBO_LEAN_STAGING_DIR is the namespace. The bench
    widens it twice. A one-shot run's disposable `-oneshot-` sibling namespace
    counts as this namespace, so workers a killed one-shot check left behind are
    found. A server is matched by the bench's own binary path, where turbo-lean
    requires the file name `turbo-lean`, so a renamed binary's daemons are found
    too.
    """
    staging = str(staging)
    exact = os.fsencode(f"TURBO_LEAN_STAGING_DIR={staging}")
    sibling = os.fsencode(f"TURBO_LEAN_STAGING_DIR={staging}-oneshot-")
    bin_real = os.path.realpath(str(bin_path))
    uid, me = os.geteuid(), os.getpid()
    found = []
    try:
        entries = list(proc_root.iterdir())
    except OSError:
        return found
    for entry in entries:
        if not entry.name.isdigit():
            continue
        pid = int(entry.name)
        if pid <= 1 or pid == me:
            continue
        # Cheapest test first: a busy machine runs tens of thousands of
        # processes, and only the bench binary and zygote workers are read further.
        try:
            if entry.stat().st_uid != uid:
                continue
            exe = os.readlink(entry / "exe")
        except OSError:
            continue
        if exe.endswith(" (deleted)"):
            exe = exe[: -len(" (deleted)")]
        name = os.path.basename(exe)
        maybe_worker = name.startswith("turbo_zygote_") or name == "turbo-zygote"
        if exe != bin_real and not maybe_worker:
            continue
        try:
            args = (entry / "cmdline").read_bytes().split(b"\0")
            env = (entry / "environ").read_bytes().split(b"\0")
        except OSError:
            continue
        if not any(v == exact or v.startswith(sibling) for v in env):
            continue
        server = (exe == bin_real and _is_serve_command(args)
                  and b"TURBO_LEAN_DAEMON=1" in env)
        worker = maybe_worker and not any(a in _AUDIT_WORKER_FLAGS for a in args)
        if not (server or worker):
            continue
        state, start = _proc_state_and_start(entry)
        if start is None or state in ("Z", "X"):
            continue
        found.append((pid, start))
    return sorted(found)


def _signal_scanned(pid: int, start: str, sig) -> bool:
    """Signal `pid` only while it is still the process that was scanned.

    The pidfd pins the process before its start time is re-read, so a recycled
    pid is never signalled; without pidfd support the window between the
    re-read and kill() is the only one left.
    """
    fd = None
    try:
        if hasattr(os, "pidfd_open") and hasattr(signal, "pidfd_send_signal"):
            fd = os.pidfd_open(pid)
        state, now = _proc_state_and_start(Path("/proc") / str(pid))
        if now != start or state in ("Z", "X"):
            return False
        if fd is not None:
            signal.pidfd_send_signal(fd, sig)
        else:
            os.kill(pid, sig)
        return True
    except OSError:
        return False
    finally:
        if fd is not None:
            os.close(fd)


def terminate_scanned(procs, term_grace_s=None, kill_grace_s=None):
    """SIGTERM each scanned process, SIGKILL whichever outlives the grace period.

    Returns (signalled, survivors); turbo-lean's own stop uses the same order.
    """
    term_grace_s = DAEMON_TERM_GRACE_S if term_grace_s is None else term_grace_s
    kill_grace_s = DAEMON_KILL_GRACE_S if kill_grace_s is None else kill_grace_s

    def alive(p):
        state, now = _proc_state_and_start(Path("/proc") / str(p[0]))
        return now == p[1] and state not in (None, "Z", "X")

    def wait(procs_, seconds):
        deadline = time.monotonic() + seconds
        while any(alive(p) for p in procs_) and time.monotonic() < deadline:
            time.sleep(0.02)

    signalled = [p for p in procs if _signal_scanned(p[0], p[1], signal.SIGTERM)]
    wait(signalled, term_grace_s)
    for p in signalled:
        if alive(p):
            _signal_scanned(p[0], p[1], signal.SIGKILL)
    wait(signalled, kill_grace_s)
    return signalled, [p for p in signalled if alive(p)]


def stop_daemons(bin_path: Path, env):
    """End every daemon of this workload's staging namespace.

    `daemon stop` goes first; whatever the namespace still has running after it
    (it timed out waiting on the lifecycle lock, failed, or never matched the
    process) is terminated here by the same scope rule, so a trial never leaks
    a daemon.
    """
    try:
        subprocess.run([str(bin_path), "daemon", "stop"], env=env,
                       timeout=DAEMON_STOP_TIMEOUT_S, stdout=subprocess.DEVNULL,
                       stderr=subprocess.DEVNULL, check=False)
    except (OSError, subprocess.SubprocessError) as e:
        print(f"warning: daemon stop failed ({e}); ending the namespace's "
              "daemons directly", file=sys.stderr)
    staging = env.get("TURBO_LEAN_STAGING_DIR")
    if not staging:
        return
    left = scoped_daemon_processes(staging, bin_path)
    if not left:
        return
    signalled, survivors = terminate_scanned(left)
    if survivors:
        print(f"warning: {len(survivors)} process(es) of {staging} outlived SIGKILL: "
              f"pids {[p[0] for p in survivors]}", file=sys.stderr)
    else:
        print(f"note: ended {len(signalled)} process(es) `daemon stop` left in {staging}",
              file=sys.stderr)


# --------------------------------------------------------------- check call

def parse_check_json(stdout: str):
    """Return the JSON object printed by `check --json` (pretty-printed)."""
    text = (stdout or "").strip()
    if not text:
        return None
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        pass
    start, end = text.find("{"), text.rfind("}")
    if 0 <= start < end:
        try:
            return json.loads(text[start:end + 1])
        except json.JSONDecodeError:
            return None
    return None


def diff_olean_inventory(before, after):
    """Return (deleted, created) path sets between two .olean inventories.

    A count comparison would miss a deletion offset by a creation; the
    path-level diff does not.
    """
    before, after = set(before or ()), set(after or ())
    return before - after, after - before


def classify_error(returncode, parsed, stderr):
    text = ""
    if parsed:
        text = str(parsed.get("error", ""))
    text = text + "\n" + (stderr or "")
    low = text.lower()
    if "declaration identity unconfirmed" in low and "unknown module prefix" in low:
        return "declaration_identity_unknown_module_prefix"
    if "declaration identity unconfirmed" in low:
        return "declaration_identity_unconfirmed"
    if "declaration" in low and "not found" in low:
        return "declaration_not_found"
    if "failed to read" in low and "no such file" in low:
        return "source_file_not_found"
    if ("worktree opt-out prevents refreshing stale imports" in low
            or ("stale imports" in low and "import_refresh" in low)
            or "fail-closed import freshness gate" in low):
        return "stale_import_refresh_fail_closed"
    if "warn.sorry" in low or "sorry" in low:
        return "warn_sorry_refused"
    if "git" in low and "2.46" in low:
        return "git_too_old"
    if "csimp" in low:
        return "csimp_refused"
    if "unsafe" in low or "implemented_by" in low:
        return "unsafe_or_implemented_by_refused"
    if returncode != 0:
        return f"exit_{returncode}"
    return "unknown"


class Runner:
    def __init__(self, args):
        self.args = args
        self.bin = Path(args.turbo_lean_bin).resolve()
        self.dirs = {"batteries": Path(args.batteries_dir).resolve(),
                     "pfr": Path(args.pfr_dir).resolve()}
        self.git_bin = os.environ["TURBO_LEAN_GIT"]
        self.trials = args.trials
        self.warmups = args.warmup
        # --check-timeout-s; getattr keeps stub args objects in tests working.
        self.check_timeout_s = getattr(args, "check_timeout_s", None) or CHECK_TIMEOUT_S
        self.scratch = Path(tempfile.mkdtemp(prefix="m1-bench-")).resolve()
        # Host roots a recorded stderr excerpt may name, each as written and as
        # resolved (a symlinked home or temp dir prints either way).
        roots = [(str(self.scratch), "<scratch>"),
                 (str(self.dirs["batteries"]), "<batteries>"),
                 (str(self.dirs["pfr"]), "<pfr>"),
                 (str(self.bin.parent), "<bin-dir>"),
                 (str(Path(__file__).resolve().parent.parent), "<repo>"),
                 (os.getcwd(), "<cwd>"),
                 (tempfile.gettempdir(), "<tmp>"),
                 (os.path.expanduser("~"), "<home>")]
        self.path_roots = roots + [(os.path.realpath(r), p) for r, p in roots
                                   if os.path.isabs(r)]
        self.revs = {}
        self.oleans_guard_violated = False
        self._edited_path = None      # source file currently holding a bench edit
        self._edited_original = None  # its untouched bytes

    def remember_edit(self, path: Path, original: bytes):
        self._edited_path, self._edited_original = path, original

    def clear_edit(self, path: Path, original: bytes):
        """Restore the source and forget the pending edit (idempotent)."""
        try:
            path.write_bytes(original)
        except OSError as e:
            print(f"warning: could not restore {path}: {e}", file=sys.stderr)
        if self._edited_path == path:
            self._edited_path, self._edited_original = None, None

    def restore_pending_edit(self):
        if self._edited_path is not None:
            path, original = self._edited_path, self._edited_original
            self._edited_path, self._edited_original = None, None
            try:
                path.write_bytes(original)
                print(f"\nrestored {path} after signal", file=sys.stderr, flush=True)
            except OSError as e:
                print(f"warning: could not restore {path} after signal: {e}",
                      file=sys.stderr, flush=True)

    # -- paths ------------------------------------------------------------
    def wl_scratch(self, wid):
        return self.scratch / wid

    def source_path(self, w):
        return self.dirs[w["repo"]] / w["file"]

    def proj_dir(self, w):
        return self.dirs[w["repo"]]

    # -- environment ------------------------------------------------------
    def trial_env(self, cache: Path, home: Path, staging: Path, no_daemon: bool):
        env = dict(os.environ)
        env["TURBO_LEAN_HOME"] = str(home)
        env["TURBO_LEAN_STAGING_DIR"] = str(staging)
        env["TURBO_LEAN_NO_REMOTE_TELEMETRY"] = "1"
        env["TURBO_LEAN_TELEMETRY"] = "off"
        env["TURBO_LEAN_DAEMON_IDLE_SECS"] = "7200"
        if no_daemon:
            env["TURBO_LEAN_NO_DAEMON"] = "1"
        else:
            env.pop("TURBO_LEAN_NO_DAEMON", None)
        return env

    def effective_check_timeout_s(self):
        # The --check-timeout-s flag (folded into check_timeout_s at
        # construction) wins; a runner without one reads the module global at
        # call time, so the TURBO_LEAN_BENCH_CHECK_TIMEOUT_S rebind is honored
        # and the child's --timeout argv and subprocess.run's bound always
        # carry the same value.
        return getattr(self, "check_timeout_s", None) or CHECK_TIMEOUT_S

    def check_argv(self, w, cache: Path, file_path: Path):
        argv = [str(self.bin), "--cache-dir", str(cache), "--json", "--no-telemetry",
                "check", "--project-dir", str(self.proj_dir(w)),
                "--decl", w["decl"], "--timeout", str(self.effective_check_timeout_s()),
                str(file_path)]
        return argv + list(w.get("extra_args", []))

    def run_check(self, w, cache: Path, home: Path, staging: Path, no_daemon: bool,
                  timeout_s=None):
        if timeout_s is None:
            timeout_s = self.effective_check_timeout_s()
        env = self.trial_env(cache, home, staging, no_daemon)
        argv = self.check_argv(w, cache, self.source_path(w))
        psi_before = sample_psi()
        t0 = time.perf_counter_ns()
        try:
            proc = subprocess.run(argv, env=env, capture_output=True, text=True,
                                  timeout=timeout_s)
            rc, out, err = proc.returncode, proc.stdout, proc.stderr
        except subprocess.TimeoutExpired as e:
            rc, out, err = -1, e.stdout or "", (e.stderr or "") + f"\ntimeout after {timeout_s}s"
        wall_ms = (time.perf_counter_ns() - t0) / 1e6
        psi_after = sample_psi()
        parsed = parse_check_json(out or "")
        return {"exit_code": rc, "external_wall_ms": wall_ms, "json": parsed,
                "stderr": err or "", "argv": argv, "env": env,
                "psi_before": psi_before, "psi_after": psi_after}

    # -- guards -----------------------------------------------------------
    def remove_verified_sources(self, w):
        marker = self.proj_dir(w) / ".lake" / "build" / ".turbo_verified_sources.json"
        try:
            marker.unlink()
        except FileNotFoundError:
            pass

    def count_oleans(self, w):
        root = self.proj_dir(w) / ".lake" / "packages"
        n = 0
        if root.is_dir():
            for _p in root.rglob("*.olean"):
                n += 1
        return n

    def olean_inventory(self, w):
        """Set of dependency-artifact paths (relative to .lake/packages)."""
        root = self.proj_dir(w) / ".lake" / "packages"
        if not root.is_dir():
            return set()
        return {str(p.relative_to(root)) for p in root.rglob("*.olean")}

    def assert_source_clean(self, w):
        inside = subprocess.run([self.git_bin, "-C", str(self.proj_dir(w)),
                                 "rev-parse", "--is-inside-work-tree"],
                                capture_output=True, text=True)
        if inside.stdout.strip() != "true":
            return  # not a git checkout; nothing to protect
        status = subprocess.run([self.git_bin, "-C", str(self.proj_dir(w)), "status",
                                 "--porcelain", "--", w["file"]],
                                capture_output=True, text=True).stdout.strip()
        if status:
            raise BenchEnvError(
                f"workload source {w['file']} is dirty after restore: {status!r}")

    # -- modes ------------------------------------------------------------
    @staticmethod
    def split_trials(trial_results):
        """Partition measured trials: keep only healthy trials' timings.

        A trial whose command exited non-zero, reported no status or a failed
        one is a failed measurement even if a time was parsed; it is excluded
        from the median and counted in `failed_trials`.
        """
        runs, covs, tool_covs, statuses, phases, psis = [], [], [], [], [], []
        fissions, rsss, failed = [], [], 0
        for r in trial_results:
            if trial_failed(r):
                failed += 1
                continue
            j = r.get("json") or {}
            fissions.append({k: j.get(k) for k in (
                "fission_cached_subshards", "fission_verified_subshards")})
            rsss.append(j.get("peak_rss_mb"))
            runs.append(r["external_wall_ms"])
            statuses.append(str((r.get("json") or {}).get("status") or f"exit_{r['exit_code']}"))
            pt = (r.get("json") or {}).get("phase_timings") or {}
            wall = pt.get("wall_ms")
            covs.append((wall / r["external_wall_ms"])
                        if isinstance(wall, (int, float)) and wall
                        and r["external_wall_ms"] > 0 else 0.0)
            tool_covs.append(pt.get("coverage_ratio") or 0.0)
            phases.append(pt.get("phases_ms") or {})
            psis.append([r.get("psi_before") or {}, r.get("psi_after") or {}])
        return TrialSplit(runs=runs, covs=covs, tool_covs=tool_covs,
                          statuses=statuses, phases=phases, psis=psis,
                          fissions=fissions, rss_mbs=rsss, failed=failed)

    def run_cold_mode(self, w):
        trial_results = []
        total = self.warmups + self.trials
        for i in range(total):
            d = self.wl_scratch(w["id"]) / f"cold_{i}"
            cache, home, staging = d / "cache", d / "home", d / "staging"
            for p in (cache, home, staging):
                p.mkdir(parents=True)
            self.remove_verified_sources(w)
            r = self.run_check(w, cache, home, staging, no_daemon=True)
            remove_tree(d)
            if i >= self.warmups:
                trial_results.append(r)
        ts = self.split_trials(trial_results)
        return mode_result(ts.runs, ts.covs, ts.statuses, phase_dicts=ts.phases,
                           psi_lists=ts.psis, failed_trials=ts.failed,
                           tool_coverage=ts.tool_covs, fission_dicts=ts.fissions,
                           rss_mbs=ts.rss_mbs)

    def run_warm_modes(self, w):
        d = self.wl_scratch(w["id"]) / "warm"
        cache, home, staging = d / "cache", d / "home", d / "staging"
        for p in (cache, home, staging):
            p.mkdir(parents=True)
        try:
            self.remove_verified_sources(w)
            setup = self.run_check(w, cache, home, staging, no_daemon=True)
            if setup["exit_code"] != 0:
                raise BenchEnvError(
                    f"warm setup run for {w['id']} failed (exit {setup['exit_code']}); "
                    f"cannot measure warm modes: {setup['stderr'][-500:]}")
            hit_trials = []
            for _ in range(self.trials):
                hit_trials.append(self.run_check(w, cache, home, staging, no_daemon=False))
            hs = self.split_trials(hit_trials)
            warm_cache = mode_result(hs.runs, hs.covs, hs.statuses,
                                     phase_dicts=hs.phases, psi_lists=hs.psis,
                                     failed_trials=hs.failed,
                                     tool_coverage=hs.tool_covs,
                                     fission_dicts=hs.fissions,
                                     rss_mbs=hs.rss_mbs, replay_mode=True)
            if not all(s == "theorem_cache_hit" for s in hs.statuses):
                warm_cache["cache_hit_assert_failed"] = hs.statuses
            edit_runs, edit_covs, edit_status, edit_phases, edit_psis = [], [], [], [], []
            src_path = self.source_path(w)
            original = src_path.read_bytes()
            edit_trials = []
            try:
                for i in range(-1, self.trials):
                    src = original.decode()
                    s, e, _line = locate_decl_block(src, w["decl"], w.get("line"))
                    edited = src[:s] + insert_bench_have(src[s:e], i) + src[e:]
                    src_path.write_text(edited)
                    self.remember_edit(src_path, original)
                    try:
                        r = self.run_check(w, cache, home, staging, no_daemon=False)
                    finally:
                        self.clear_edit(src_path, original)
                    if i < 0:
                        continue  # settling run: first edit after the cache-hit
                                  # phase pays a one-off penalty; discard it
                    edit_trials.append(r)
            finally:
                self.clear_edit(src_path, original)
            es = self.split_trials(edit_trials)
            warm_edit = mode_result(es.runs, es.covs, es.statuses,
                                    phase_dicts=es.phases, psi_lists=es.psis,
                                    failed_trials=es.failed,
                                    tool_coverage=es.tool_covs,
                                    fission_dicts=es.fissions,
                                    rss_mbs=es.rss_mbs, replay_mode=True)
            if not all(s == "theorem_verified" for s in es.statuses):
                warm_edit["verified_assert_failed"] = es.statuses
            return warm_cache, warm_edit
        finally:
            stop_daemons(self.bin, self.trial_env(cache, home, staging, no_daemon=False))
            remove_tree(d)
            self.assert_source_clean(w)

    def run_pfr_workload(self, w):
        """Fail-fast probe of a blocked workload.

        Every probe's exit code and failure class is checked (not just the
        last); the dependency-artifact inventory is compared path by path
        before/after each probe inside a `finally`, so a deletion offset by a
        creation is still caught.
        """
        probe_exits, probe_class_list, psis, runs, statuses = [], [], [], [], []
        stderr_excerpt = ""
        expected_classes = set(w.get("expected_error_classes") or ())
        total = self.warmups + self.trials
        for i in range(total):
            d = self.wl_scratch(w["id"]) / f"cold_{i}"
            cache, home, staging = d / "cache", d / "home", d / "staging"
            for p in (cache, home, staging):
                p.mkdir(parents=True)
            inv_before = self.olean_inventory(w)
            try:
                r = self.run_check(w, cache, home, staging, no_daemon=True)
            finally:
                missing, extra = diff_olean_inventory(inv_before, self.olean_inventory(w))
                if missing or extra:
                    self.oleans_guard_violated = True
                    raise BenchEnvError(
                        f"SAFETY: PFR probe changed the dependency .olean inventory "
                        f"({len(missing)} deleted, {len(extra)} created, e.g. "
                        f"{sorted(missing | extra)[:3]}); aborting before more damage. "
                        "This must never happen (--no-auto-worktree-link is mandatory).")
            remove_tree(d)
            probe_exits.append(r["exit_code"])
            cls = (classify_error(r["exit_code"], r.get("json"), r["stderr"])
                   if r["exit_code"] != 0 else "unexpected_exit_0")
            probe_class_list.append(cls)
            psis.append([r.get("psi_before") or {}, r.get("psi_after") or {}])
            if i >= self.warmups:
                runs.append(r["external_wall_ms"])
                statuses.append(f"exit_{r['exit_code']}")
                if not stderr_excerpt and r["stderr"]:
                    stderr_excerpt = scrub_host_paths(r["stderr"], self.path_roots)[:500]
        probe_classes = set(probe_class_list)
        m = mode_result(runs, [], statuses, psi_lists=psis)
        m["error_classes"] = sorted(probe_classes)
        m["probe_error_classes"] = probe_class_list
        if stderr_excerpt:
            m["stderr_excerpt"] = stderr_excerpt
        any_passed = any(e == 0 for e in probe_exits)
        all_expected = (bool(probe_exits) and not any_passed
                        and bool(expected_classes)
                        and all(c in expected_classes for c in probe_class_list))
        if any_passed or not probe_exits:
            status = "unexpectedly_passing"
        elif all_expected:
            status = "blocked_as_expected"
        else:
            status = "blocked_unexpected_failure"
        entry = {
            "status": status,
            "expected_status": "blocked",
            "expected_error_classes": sorted(expected_classes),
            "exit_code": probe_exits[-1] if probe_exits else None,
            "probe_exit_codes": probe_exits,
            "probe_error_classes": probe_class_list,
            "error_class": sorted(probe_classes)[0] if probe_classes else None,
            "repo": w["repo"], "file": w["file"], "decl": w["decl"],
            "modes": {"cold_no_daemon": m},
        }
        print(f"  blocked: status={status} probe_exits={probe_exits} "
              f"error_classes={sorted(probe_classes)} median={m['median_ms']}ms", flush=True)
        return entry

    # -- whole workloads ---------------------------------------------------
    def run_workload(self, w):
        wid = w["id"]
        print(f"[{utc_now_iso()}] workload {wid} ...", flush=True)
        if w["expected_status"] == "blocked":
            entry = self.run_pfr_workload(w)
            return entry
        cold = self.run_cold_mode(w)
        print(f"  cold median={cold['median_ms']}ms rel_spread={cold['rel_spread']}", flush=True)
        warm_cache, warm_edit = self.run_warm_modes(w)
        print(f"  warm cache-hit median={warm_cache['median_ms']}ms, "
              f"edited median={warm_edit['median_ms']}ms", flush=True)

        def mode_healthy(m, assert_key):
            return (m["trials"] > 0 and m.get("failed_trials", 0) == 0
                    and m["coverage_ratio_external_min"] is not None
                    and m["coverage_ratio_external_min"] >= COVERAGE_GATE
                    and assert_key not in m)
        healthy = (mode_healthy(cold, "")
                   and mode_healthy(warm_cache, "cache_hit_assert_failed")
                   and mode_healthy(warm_edit, "verified_assert_failed"))
        return {"id": wid, "status": "ok" if healthy else "failed",
                "repo": w["repo"], "file": w["file"], "decl": w["decl"],
                "expected_status": "active",
                "modes": {"cold_no_daemon": cold, "warm_cache_hit_daemon": warm_cache,
                          "warm_edited_proof_daemon": warm_edit}}


# ------------------------------------------------------------------- main

def install_signal_restore(runner: Runner):
    """On SIGTERM/SIGINT, restore the edited workload source before exiting.

    The `finally` in run_warm_modes does not run when the default SIGTERM
    action kills the process, so the edit would be left behind for the next
    run to trip over (check_pinned_revs refuses dirty checkouts for exactly
    that reason). The handler restores first, then exits 128+signum.
    """
    def handler(signum, _frame):
        runner.restore_pending_edit()
        raise SystemExit(128 + signum)
    for sig_name in ("SIGTERM", "SIGINT"):
        sig = getattr(signal, sig_name, None)
        if sig is not None:
            try:
                signal.signal(sig, handler)
            except (ValueError, OSError):
                pass  # not the main thread (tests)


def _apply_check_timeout_override():
    """Fold in TURBO_LEAN_BENCH_CHECK_TIMEOUT_S, validated.

    A junk or non-positive value raises BenchEnvError so the run exits 4
    (environment error) per the exit-code contract, instead of an uncaught
    ValueError exiting 1 (reserved for a regression verdict).
    """
    global CHECK_TIMEOUT_S
    raw = os.environ.get("TURBO_LEAN_BENCH_CHECK_TIMEOUT_S")
    if raw is None:
        return
    try:
        value = int(raw)
    except ValueError as e:
        raise BenchEnvError(
            f"TURBO_LEAN_BENCH_CHECK_TIMEOUT_S must be an integer number of "
            f"seconds, got {raw!r}") from e
    if value <= 0:
        raise BenchEnvError(
            f"TURBO_LEAN_BENCH_CHECK_TIMEOUT_S must be positive, got {raw!r}")
    CHECK_TIMEOUT_S = value


def validate_environment(args):
    _apply_check_timeout_override()
    for var, expected in REQUIRED_ENV.items():
        got = os.environ.get(var)
        if got != expected:
            raise BenchEnvError(
                f"{var} must be '{expected}' (Batteries files are refused otherwise, "
                f"until P9 lands); got {got!r}")
    git_bin = os.environ.get("TURBO_LEAN_GIT")
    if not git_bin:
        raise BenchEnvError(
            "TURBO_LEAN_GIT must point at a git >= 2.46 binary; system git 2.43 is "
            "refused by turbo-lean (edit-locality requirement).")
    (maj, minor), human = git_version(git_bin)
    if (maj, minor) < (2, 46):
        raise BenchEnvError(f"TURBO_LEAN_GIT is {human}; need >= 2.46")
    if not Path(args.turbo_lean_bin).is_file():
        raise BenchEnvError(f"turbo-lean binary not found: {args.turbo_lean_bin}")
    for repo in ("batteries", "pfr"):
        d = Path(args.batteries_dir if repo == "batteries" else args.pfr_dir)
        if not d.is_dir():
            raise BenchEnvError(f"{repo} checkout not found: {d}")
    return git_bin, human


def require_quiet_node(args):
    try:
        load1, load5, _ = os.getloadavg()
    except (OSError, AttributeError):
        return None
    load1, load5 = round(load1, 2), round(load5, 2)
    if max(load1, load5) > BUSY_LOAD_THRESHOLD and not args.allow_busy_node:
        raise BenchEnvError(
            f"node load average (1 min {load1:.2f} / 5 min {load5:.2f}) exceeds "
            f"{BUSY_LOAD_THRESHOLD}; another process is loading this machine and would "
            "poison the medians. Re-run when the node is idle, or pass --allow-busy-node "
            "to record the condition.")
    return load1


def check_pinned_revs(runner: Runner):
    for repo, expected in PINNED_REVS.items():
        rev, dirty = repo_commit(runner.git_bin, runner.dirs[repo])
        runner.revs[repo] = rev
        if rev is not None and dirty:
            raise BenchEnvError(
                f"{repo} checkout {runner.dirs[repo]} has uncommitted tracked changes; "
                "commit or restore them first. A dirty checkout can hide an edit left "
                "behind by a killed run and invalidates the recorded provenance.")
        if rev != expected and not runner.args.skip_rev_check:
            raise BenchEnvError(
                f"{repo} checkout is at {rev}, benchmark is pinned to {expected}; "
                "point --batteries-dir/--pfr-dir at the pinned revs or pass "
                "--skip-rev-check (the JSON then records revs_pinned=false).")


def load_baseline_or_none(args):
    """Load and fully validate the baseline BEFORE any measurement.

    A baseline named on the command line (or found at the default path) that is
    missing, unreadable, malformed, or lacks a workload, a mode or trials is a
    setup error, never a warning followed by a silent skip: a comparison that
    quietly did not happen is how false passes are made.
    """
    if args.no_baseline:
        return None
    bpath = args.baseline
    if bpath is None:
        default = Path(__file__).resolve().parent / "bench_check_loop_baseline.json"
        if not default.is_file():
            return None
        bpath = str(default)
    try:
        baseline = json.loads(Path(bpath).read_text())
    except (OSError, json.JSONDecodeError) as e:
        raise BenchEnvError(f"cannot load baseline {bpath}: {e}") from e
    errs = validate_baseline(baseline)
    if errs:
        raise BenchEnvError(
            f"baseline {bpath} failed validation: " + "; ".join(errs)
            + " (refusing to run: a comparison against a broken baseline would "
              "silently skip cells and could pass falsely)")
    return baseline


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--turbo-lean-bin", default="target/release/turbo-lean")
    ap.add_argument("--batteries-dir")
    ap.add_argument("--pfr-dir")
    ap.add_argument("--trials", type=int, default=DEFAULT_TRIALS)
    ap.add_argument("--warmup", type=int, default=DEFAULT_WARMUP,
                    help="discarded settling runs before measured trials (default 1)")
    ap.add_argument("--check-timeout-s", type=int, default=None,
                    help="per-check budget in seconds, passed to `check --timeout` and "
                         "used as the subprocess timeout (default: "
                         "TURBO_LEAN_BENCH_CHECK_TIMEOUT_S if set, else 900). The "
                         "default is resolved AFTER environment validation, so the env "
                         "override reaches real runs; a default captured at parser "
                         "build would freeze the import-time 900 in.")
    ap.add_argument("--only-workloads",
                    help="comma-separated workload ids; only these are measured, the "
                         "rest are recorded as skipped_by_filter and the run verdict "
                         "is partial_run (exit 0; exit 1 under --strict-comparison). "
                         "For targeted re-measurement; normally used with "
                         "--no-baseline. Not combinable with --rebaseline.")
    ap.add_argument("--out", help="write the full results JSON here")
    ap.add_argument("--baseline", help="baseline or prior results JSON to compare against "
                                       "(default: scripts/bench_check_loop_baseline.json "
                                       "when present)")
    ap.add_argument("--no-baseline", action="store_true", help="never compare")
    ap.add_argument("--rebaseline", action="store_true",
                    help="this run becomes the new baseline JSON (written to --out)")
    ap.add_argument("--machine-label", help="label for this machine/condition; also "
                                            "recorded as the host hostname field in place "
                                            "of the live node name; a baseline from a "
                                            "different label is never compared")
    ap.add_argument("--skip-rev-check", action="store_true",
                    help="do not enforce pinned Batteries/PFR revs (recorded honestly)")
    ap.add_argument("--allow-busy-node", action="store_true",
                    help="run even when the node's 1-min load average exceeds "
                         f"{BUSY_LOAD_THRESHOLD} (recorded as node_busy_allowed)")
    ap.add_argument("--strict-comparison", action="store_true",
                    help="exit 1 when a comparison was skipped instead of passed")
    ap.add_argument("--validate-only", metavar="JSON",
                    help="validate a baseline/results file and exit")
    args = ap.parse_args(argv)

    if args.trials <= 0:
        ap.error(f"--trials must be >= 1, got {args.trials}")
    if args.warmup < 0:
        ap.error(f"--warmup must be >= 0, got {args.warmup}")
    if args.check_timeout_s is not None and args.check_timeout_s <= 0:
        ap.error(f"--check-timeout-s must be >= 1, got {args.check_timeout_s}")
    if args.only_workloads is not None:
        names = [n.strip() for n in args.only_workloads.split(",") if n.strip()]
        if not names:
            ap.error("--only-workloads needs at least one workload id")
        valid = {w["id"] for w in WORKLOADS}
        unknown = sorted(set(names) - valid)
        if unknown:
            ap.error(f"unknown workload id(s): {', '.join(unknown)}; valid ids: "
                     + ", ".join(w["id"] for w in WORKLOADS))
        if args.rebaseline:
            ap.error("--rebaseline cannot be combined with --only-workloads: "
                     "a baseline must measure every workload")

    if args.validate_only:
        try:
            data = json.loads(Path(args.validate_only).read_text())
        except (OSError, json.JSONDecodeError) as e:
            print(f"INVALID: cannot read {args.validate_only}: {e}")
            return 1
        errs = validate_baseline(data)
        for e in errs:
            print(f"INVALID: {e}")
        if not errs:
            print(f"OK: {data.get('kind')} at {args.validate_only} is schema-valid "
                  f"({data.get('turbo_lean_commit')}, host {data.get('host', {}).get('hostname')})")
        return 0 if not errs else 1
    if not args.batteries_dir or not args.pfr_dir:
        ap.error("--batteries-dir and --pfr-dir are required (unless --validate-only); "
                 "the environment needs TURBO_LEAN_GIT (git >= 2.46) and "
                 "TURBO_LEAN_ALLOWED_{CSIMP,UNSAFE,IMPLEMENTED_BY}='*'")

    # Environment validation failures are environment errors (exit 4) like every
    # other BenchEnvError; an uncaught raise here used to exit 1, the code reserved
    # for a regression verdict.
    try:
        git_bin, git_human = validate_environment(args)
    except BenchEnvError as e:
        print(f"ENVIRONMENT ERROR (exit 4): {e}", file=sys.stderr)
        return 4
    if args.check_timeout_s is None:
        # Resolved only now: validate_environment has folded the (validated)
        # TURBO_LEAN_BENCH_CHECK_TIMEOUT_S override into the global, so the
        # recorded args carry the value every trial actually used. An explicit
        # --check-timeout-s flag wins over the env override.
        args.check_timeout_s = CHECK_TIMEOUT_S
    runner = Runner(args)
    install_signal_restore(runner)
    t_start = time.monotonic()
    try:
        load_at_start = require_quiet_node(args)
        check_pinned_revs(runner)
        baseline = load_baseline_or_none(args)
        commit, dirty, repo_path = turbo_lean_commit_for(runner.bin, git_bin)
        if args.rebaseline and dirty:
            raise BenchEnvError(
                f"--rebaseline requires a clean turbo-lean tree at {repo_path}; "
                "commit or restore the tracked changes first: the committed baseline "
                "must record honest provenance (commit + dirty flag + binary hash).")
        binary_sha = hashlib.sha256(runner.bin.read_bytes()).hexdigest()
        toolchain = detect_toolchain(runner.dirs)
        h = host_id(args.machine_label)
        # The results JSON is a committed artifact: no host path goes in it. The
        # repository and scratch root are left out, the binary is recorded relative
        # to its repository, and path-valued settings as digests.
        settings = recorded_settings()
        settings["git_version"] = git_human
        results = empty_run_result(WORKLOADS, args.trials)
        results.update({
            "turbo_lean_commit": commit, "turbo_lean_dirty": dirty,
            "turbo_lean_binary": binary_record(runner.bin, repo_path, binary_sha),
            "toolchain": toolchain,
            "host": h, "settings": settings, "workload_revs": dict(runner.revs),
            "revs_pinned": (not args.skip_rev_check),
            "node": {"load1_at_start": None if load_at_start is None else round(load_at_start, 2),
                     "load1_at_end": None,
                     "busy_allowed": args.allow_busy_node},
            "args": {"trials": args.trials, "warmup": args.warmup,
                     "skip_rev_check": args.skip_rev_check,
                     "check_timeout_s": args.check_timeout_s,
                     "only_workloads": args.only_workloads},
        })
        selected = selected_workloads(args)
        for w in selected:
            entry = runner.run_workload(w)
            results["workloads"][w["id"]] = entry
        selected_ids = {w["id"] for w in selected}
        for w in WORKLOADS:
            if w["id"] not in selected_ids:
                # Deliberately unmeasured, not failed: the verdict side reads
                # this status and reports partial_run instead of
                # measurement_failed.
                results["workloads"][w["id"]]["status"] = "skipped_by_filter"
        results["cas_replay"] = summarize_cas_replay(results)
        verdict = compare_run(baseline, results)
        results["verdict"] = verdict
        if args.rebaseline:
            results["kind"] = "baseline"
        results["run_duration_s"] = round(time.monotonic() - t_start, 1)
        try:
            results["node"]["load1_at_end"] = round(os.getloadavg()[0], 2)
        except (OSError, AttributeError, KeyError):
            pass
        payload = json.dumps(results, indent=2)
        if args.out:
            Path(args.out).write_text(payload + "\n")
        print(payload if not args.out else f"results written to {args.out}")
        if baseline is not None:
            same_note = " (same binary)" if verdict.get("same_binary") else ""
            print(f"COMPARISON PROVENANCE: baseline commit={verdict.get('baseline_commit')} "
                  f"sha256={verdict.get('baseline_binary_sha256')} -> "
                  f"run commit={verdict.get('run_commit')} "
                  f"sha256={verdict.get('run_binary_sha256')}{same_note}")
        for cell in sorted(verdict["gates"]):
            g = verdict["gates"][cell]
            if g.get("baseline_median_ms") is None:
                continue
            print(f"  {cell}: {g['baseline_median_ms']} -> {g['new_median_ms']} ms "
                  f"({g['delta_ms']:+.1f} ms, {g['delta_pct']:+.2f}%) "
                  f"band ±{g['noise_band_ms']} ms: {g['verdict']}")
        rep = results["cas_replay"]
        if (rep["overall"]["classified_calls"] or rep["overall"]["failed_trials"]
                or rep["overall"]["other_status_calls"] or rep["non_ok_workloads"]):
            un, ed, ov = rep["unedited_recheck"], rep["edited_recheck"], rep["overall"]
            extra = ""
            if ov["failed_trials"] or ov["other_status_calls"]:
                extra += (f" | failed_trials={ov['failed_trials']} "
                          f"other_status_calls={ov['other_status_calls']}")
            if rep["non_ok_workloads"]:
                extra += f" | non_ok_workloads={rep['non_ok_workloads']}"
            print(f"G2A CAS REPLAY: overall {ov['hits']}/{ov['classified_calls']} "
                  f"classified (hit_rate={ov['hit_rate']}) | unedited re-checks "
                  f"{un['hits']}/{un['classified_calls']} (hit_rate={un['hit_rate']}) | "
                  f"edited re-checks {ed['hits']}/{ed['classified_calls']} "
                  f"(hit_rate={ed['hit_rate']})" + extra, flush=True)
        if verdict.get("summary"):
            print(f"SUMMARY: {verdict['summary']}", flush=True)
        print(f"VERDICT: {verdict['verdict']}"
              + (f" ({verdict['skipped_reason']})" if verdict.get("skipped_reason") else "")
              + (f" regressions={verdict['regressions']}" if verdict["regressions"] else "")
              + (f" unexpected_successes={verdict['unexpected_successes']}"
                 if verdict["unexpected_successes"] else ""), flush=True)
        code = VERDICT_EXIT[verdict["verdict"]]
        if (code == 0 and args.strict_comparison
                and verdict["verdict"] in ("not_compared",
                                           "partial_run",
                                           "comparison_skipped_host_mismatch",
                                           "comparison_skipped_settings_mismatch")):
            code = 1
        return code
    except BenchEnvError as e:
        print(f"ENVIRONMENT ERROR (exit 4): {e}", file=sys.stderr)
        return 4
    finally:
        remove_tree(runner.scratch)


if __name__ == "__main__":
    sys.exit(main())
