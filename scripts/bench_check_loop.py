#!/usr/bin/env python3
"""M1 pinned benchmark of the `turbo-lean check` loop (roadmap/HORIZONS.md line 142).

Measures the five pinned `Batteries` declarations and the pinned `PFR`
declaration (expected `blocked` today) across three loop regimes, writes a
results JSON, and — when a baseline is available on the same host — gates the
medians against it. Every performance change in this project must show before
and after numbers from this script; a change that does not move them is
reverted.

Typical before/after on one machine (the only comparison this script trusts):

    git checkout main    && python3 scripts/bench_check_loop.py --out /tmp/m1_main.json
    git checkout <branch> && python3 scripts/bench_check_loop.py --baseline /tmp/m1_main.json --out /tmp/m1_branch.json

Exit codes:
    0  measurements healthy; comparison passed, or was explicitly skipped and
       flagged (`comparison_skipped_*`), or was not requested (`not_compared`).
       The script never reports a pass for a comparison it skipped.
    1  regression, unhealthy measurement, or (with --strict-comparison) a
       skipped comparison.
    2  usage error.
    3  stale expectation: a workload expected `blocked` (PFR) passed.
    4  environment/setup failure (missing env, wrong revs, wrong git, ...).

Required environment (validated, fail-closed; all recorded in the output):
    TURBO_LEAN_GIT                     git >= 2.46 binary (system git is refused)
    TURBO_LEAN_ALLOWED_CSIMP=*         imported @[csimp] allowed until P9 lands
    TURBO_LEAN_ALLOWED_UNSAFE=*        imported unsafe defs allowed until P9
    TURBO_LEAN_ALLOWED_IMPLEMENTED_BY=*  imported implemented_by allowed until P9

Python standard library only.
"""

from __future__ import annotations

import argparse
import json
import os
import platform
import re
import shutil
import signal
import statistics
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path

SCHEMA_VERSION = 1
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
     "file": "PFR/MoreRuzsaDist.lean", "decl": "ProbabilityTheory.rdist_of_neg_le", "line": 55,
     "extra_args": ["--no-auto-worktree-link"],
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
    "TURBO_LEAN_DAEMON_IDLE_SECS",
]

VERDICT_EXIT = {
    "pass": 0, "not_compared": 0,
    "comparison_skipped_host_mismatch": 0, "comparison_skipped_settings_mismatch": 0,
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


def empty_run_result(workloads, trials):
    return {
        "schema_version": SCHEMA_VERSION, "kind": "results", "created_utc": utc_now_iso(),
        "turbo_lean_commit": None, "host": {}, "trials": trials, "settings": {},
        "workloads": {w["id"]: empty_workload_result(w) for w in workloads},
    }


def mode_result(runs_ms, coverage_ratios, statuses, extra=None, phase_dicts=None,
                psi_lists=None):
    xs = list(runs_ms)
    out = {
        "runs_ms": [round(x, 1) for x in xs],
        "trials": len(xs),
        "median_ms": round(median(xs), 1) if xs else None,
        "spread_ms": round(max(xs) - min(xs), 1) if len(xs) > 1 else 0.0,
        "rel_spread": round(rel_spread(xs), 4) if len(xs) > 1 else 0.0,
        "coverage_ratio_min": round(min(coverage_ratios), 4) if coverage_ratios else None,
        "statuses_observed": sorted(set(statuses)),
    }
    if phase_dicts:
        names = sorted({k for pd in phase_dicts for k in pd})
        out["phases_ms_median"] = {
            name: round(median([pd[name] for pd in phase_dicts if name in pd]), 1)
            for name in names
            if any(name in pd for pd in phase_dicts)
        }
    if psi_lists:
        worst = {k: max((p.get(k, 0.0) for trial in psi_lists for p in trial),
                        default=0.0) for k in ("cpu", "memory", "io")}
        out["psi_max_avg10"] = {k: round(v, 2) for k, v in worst.items()}
        out["psi_contended"] = bool(worst.get("memory", 0.0) > 10.0
                                    or worst.get("io", 0.0) > 10.0)
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


def validate_baseline(base):
    errs = []
    if not isinstance(base, dict):
        return ["baseline is not a JSON object"]
    for key in ("schema_version", "kind", "created_utc", "turbo_lean_commit",
                "host", "trials", "settings", "workloads"):
        if key not in base:
            errs.append(f"missing required key: {key}")
    if "kind" in base and base["kind"] not in ("baseline", "results"):
        errs.append(f"unexpected kind: {base['kind']}")
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
            if not m or not m.get("trials") or m.get("median_ms") is None:
                errs.append(f"{wid}/{mode} has no measured trials")
    return errs


# --------------------------------------------------------------- comparison

def host_matches(base, res) -> bool:
    bh, rh = base.get("host") or {}, res.get("host") or {}
    if bh.get("hostname") != rh.get("hostname"):
        return False
    lb, lr = bh.get("machine_label"), rh.get("machine_label")
    if lb and lr and lb != lr:
        return False
    return True


def settings_match(base, res) -> bool:
    key = lambda s: {v: s.get(v) for v in
                     ("TURBO_LEAN_GIT", "TURBO_LEAN_ALLOWED_CSIMP",
                      "TURBO_LEAN_ALLOWED_UNSAFE", "TURBO_LEAN_ALLOWED_IMPLEMENTED_BY")}
    return key(base.get("settings") or {}) == key(res.get("settings") or {})


def compare_run(baseline, res):
    """Gate `res` against `baseline`. Never passes a comparison it skipped."""
    verdict = {
        "verdict": None, "regressions": [], "improvements": [], "measured_nothing": [],
        "unexpected_successes": [], "pfr_status": None, "skipped_reason": None,
        "same_binary": None, "gates": {},
    }
    healthy = all(
        (w.get("status") == "ok" if w.get("expected_status") != "blocked"
         else w.get("status") in ("blocked_as_expected", "unexpectedly_passing"))
        for w in res["workloads"].values()
    )
    if not healthy:
        verdict["verdict"] = "measurement_failed"
        return verdict
    verdict["pfr_status"] = res["workloads"]["pfr_more_ruzsa_dist"]["status"]
    if baseline is None:
        verdict["verdict"] = "not_compared"
        verdict["skipped_reason"] = "no baseline given or found"
        return verdict
    verdict["same_binary"] = (res.get("turbo_lean_commit") == baseline.get("turbo_lean_commit"))
    if not host_matches(baseline, res):
        verdict["verdict"] = "comparison_skipped_host_mismatch"
        verdict["skipped_reason"] = (
            f"baseline host {baseline.get('host', {}).get('hostname')}/"
            f"{baseline.get('host', {}).get('machine_label')} != this host "
            f"{res.get('host', {}).get('hostname')}/{res.get('host', {}).get('machine_label')}; "
            "a baseline from another machine proves nothing here")
        return verdict
    if not settings_match(baseline, res):
        verdict["verdict"] = "comparison_skipped_settings_mismatch"
        verdict["skipped_reason"] = "TURBO_LEAN_* settings differ from the baseline run"
        return verdict
    for w in WORKLOADS:
        wid = w["id"]
        base_w, res_w = baseline["workloads"].get(wid), res["workloads"][wid]
        if res_w.get("status") == "unexpectedly_passing":
            verdict["unexpected_successes"].append(wid)
            verdict["verdict"] = "stale_expectation"
            continue
        if base_w is None:
            continue
        for mode in MODES:
            b, r = (base_w.get("modes") or {}).get(mode), (res_w.get("modes") or {}).get(mode)
            if b is None or b.get("median_ms") is None:
                continue
            if r is None or not r.get("trials") or r.get("median_ms") is None:
                verdict["regressions"].append(f"{wid}/{mode}")
                verdict["measured_nothing"].append(f"{wid}/{mode}")
                verdict["gates"][f"{wid}/{mode}"] = {"verdict": "measured_nothing"}
                continue
            tol = tolerance_ms(b["median_ms"], b.get("rel_spread", 0.0), mode)
            new = r["median_ms"]
            gate = {"baseline_median_ms": b["median_ms"], "baseline_rel_spread": b.get("rel_spread"),
                    "tolerance_ms": round(tol, 1), "new_median_ms": new,
                    "verdict": "pass" if new <= tol else "regression"}
            if new > tol:
                gate["over_by_ms"] = round(new - tol, 1)
                verdict["regressions"].append(f"{wid}/{mode}")
            elif new < b["median_ms"] * 0.8:
                verdict["improvements"].append(f"{wid}/{mode}")
            verdict["gates"][f"{wid}/{mode}"] = gate
    if verdict["verdict"] is None:
        verdict["verdict"] = "pass" if not verdict["regressions"] else "regression"
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
    return {
        "hostname": platform.node(),
        "machine_label": machine_label,
        "kernel": f"{platform.system()} {platform.release()}",
        "cpu_model": cpu_model,
        "nproc": os.cpu_count(),
        "mem_gb": mem_gb,
    }


def sample_psi():
    psi = {}
    for name in ("cpu", "memory", "io"):
        try:
            for line in Path(f"/proc/pressure/{name}").read_text().splitlines():
                if line.startswith("avg10"):
                    psi[name] = float(line.split()[1])
        except (OSError, ValueError, IndexError):
            pass
    try:
        psi["load1"] = os.getloadavg()[0]
    except (OSError, AttributeError):
        pass
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
        dirty = subprocess.run([git_bin, "-C", str(repo), "status", "--porcelain"],
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


# ----------------------------------------------------------- daemon control

def stop_daemons(bin_path: Path, env):
    """Stop daemons scoped to this workload's staging/cache, best effort."""
    try:
        subprocess.run([str(bin_path), "daemon", "stop"], env=env, timeout=60,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False)
    except (OSError, subprocess.SubprocessError) as e:
        print(f"warning: daemon stop failed ({e}); killing via pidfiles", file=sys.stderr)


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


def classify_error(returncode, parsed, stderr):
    text = ""
    if parsed:
        text = str(parsed.get("error", ""))
    text = text + "\n" + (stderr or "")
    low = text.lower()
    if "stale" in low or "import_refresh" in low or "imports fresh" in low:
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
        self.scratch = Path(tempfile.mkdtemp(prefix="m1-bench-")).resolve()
        self.revs = {}
        self.oleans_guard_violated = False

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

    def check_argv(self, w, cache: Path, file_path: Path):
        argv = [str(self.bin), "--cache-dir", str(cache), "--json", "--no-telemetry",
                "check", "--project-dir", str(self.proj_dir(w)),
                "--decl", w["decl"], "--timeout", str(CHECK_TIMEOUT_S), str(file_path)]
        return argv + list(w.get("extra_args", []))

    def run_check(self, w, cache: Path, home: Path, staging: Path, no_daemon: bool,
                  timeout_s=CHECK_TIMEOUT_S):
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
    def run_cold_mode(self, w):
        runs, covs, statuses, phases, psis = [], [], [], [], []
        total = self.warmups + self.trials
        for i in range(total):
            d = self.wl_scratch(w["id"]) / f"cold_{i}"
            cache, home, staging = d / "cache", d / "home", d / "staging"
            for p in (cache, home, staging):
                p.mkdir(parents=True)
            self.remove_verified_sources(w)
            r = self.run_check(w, cache, home, staging, no_daemon=True)
            shutil.rmtree(d, ignore_errors=True)
            if i >= self.warmups:
                runs.append(r["external_wall_ms"])
                statuses.append(f"exit_{r['exit_code']}")
                pt = (r.get("json") or {}).get("phase_timings") or {}
                covs.append(pt.get("coverage_ratio", 0.0))
                phases.append(pt.get("phases_ms") or {})
                psis.append([r.get("psi_before") or {}, r.get("psi_after") or {}])
        return mode_result(runs, covs, statuses, phase_dicts=phases, psi_lists=psis)

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
            hit_runs, hit_covs, hit_status, hit_phases, hit_psis = [], [], [], [], []
            for _ in range(self.trials):
                r = self.run_check(w, cache, home, staging, no_daemon=False)
                hit_runs.append(r["external_wall_ms"])
                pt = (r.get("json") or {}).get("phase_timings") or {}
                hit_covs.append(pt.get("coverage_ratio", 0.0))
                hit_status.append(str((r.get("json") or {}).get("status")))
                hit_phases.append(pt.get("phases_ms") or {})
                hit_psis.append([r.get("psi_before") or {}, r.get("psi_after") or {}])
            warm_cache = mode_result(hit_runs, hit_covs, hit_status,
                                     phase_dicts=hit_phases, psi_lists=hit_psis)
            if not all(s == "theorem_cache_hit" for s in hit_status):
                warm_cache["cache_hit_assert_failed"] = hit_status
            edit_runs, edit_covs, edit_status, edit_phases, edit_psis = [], [], [], [], []
            src_path = self.source_path(w)
            original = src_path.read_bytes()
            try:
                for i in range(-1, self.trials):
                    src = original.decode()
                    s, e, _line = locate_decl_block(src, w["decl"], w.get("line"))
                    edited = src[:s] + insert_bench_have(src[s:e], i) + src[e:]
                    src_path.write_text(edited)
                    try:
                        r = self.run_check(w, cache, home, staging, no_daemon=False)
                    finally:
                        src_path.write_bytes(original)
                    if i < 0:
                        continue  # settling run: first edit after the cache-hit
                                  # phase pays a one-off penalty; discard it
                    edit_runs.append(r["external_wall_ms"])
                    pt = (r.get("json") or {}).get("phase_timings") or {}
                    edit_covs.append(pt.get("coverage_ratio", 0.0))
                    edit_status.append(str((r.get("json") or {}).get("status")))
                    edit_phases.append(pt.get("phases_ms") or {})
                    edit_psis.append([r.get("psi_before") or {}, r.get("psi_after") or {}])
            finally:
                src_path.write_bytes(original)
            warm_edit = mode_result(edit_runs, edit_covs, edit_status,
                                    phase_dicts=edit_phases, psi_lists=edit_psis)
            if not all(s == "theorem_verified" for s in edit_status):
                warm_edit["verified_assert_failed"] = edit_status
            return warm_cache, warm_edit
        finally:
            stop_daemons(self.bin, self.trial_env(cache, home, staging, no_daemon=False))
            shutil.rmtree(d, ignore_errors=True)
            self.assert_source_clean(w)

    def run_pfr_workload(self, w):
        runs, covs, statuses, errors, psis = [], [], [], set(), []
        exit_code = None
        stderr_excerpt = ""
        total = self.warmups + self.trials
        for i in range(total):
            d = self.wl_scratch(w["id"]) / f"cold_{i}"
            cache, home, staging = d / "cache", d / "home", d / "staging"
            for p in (cache, home, staging):
                p.mkdir(parents=True)
            oleans_before = self.count_oleans(w)
            r = self.run_check(w, cache, home, staging, no_daemon=True)
            oleans_after = self.count_oleans(w)
            if oleans_after < oleans_before:
                self.oleans_guard_violated = True
                raise BenchEnvError(
                    f"SAFETY: PFR check deleted {oleans_before - oleans_after} prebuilt "
                    ".olean files from the checkout; aborting before more damage. "
                    "This must never happen (--no-auto-worktree-link is mandatory).")
            shutil.rmtree(d, ignore_errors=True)
            if i >= self.warmups:
                runs.append(r["external_wall_ms"])
                statuses.append(f"exit_{r['exit_code']}")
                pt = (r.get("json") or {}).get("phase_timings") or {}
                covs.append(pt.get("coverage_ratio", 0.0))
                errors.add(classify_error(r["exit_code"], r.get("json"), r["stderr"]))
                exit_code = r["exit_code"]
                psis.append([r.get("psi_before") or {}, r.get("psi_after") or {}])
                if not stderr_excerpt and r["stderr"]:
                    stderr_excerpt = r["stderr"][:500]
        m = mode_result(runs, covs, statuses, psi_lists=psis)
        m["error_classes"] = sorted(errors)
        if stderr_excerpt:
            m["stderr_excerpt"] = stderr_excerpt
        return m, exit_code, sorted(errors)[0] if errors else None

    # -- whole workloads ---------------------------------------------------
    def run_workload(self, w):
        wid = w["id"]
        print(f"[{utc_now_iso()}] workload {wid} ...", flush=True)
        if w["expected_status"] == "blocked":
            m, exit_code, err_class = self.run_pfr_workload(w)
            entry = blocked_workload_result(exit_code, err_class,
                                            median_ms=m["median_ms"])
            entry.update({"repo": w["repo"], "file": w["file"], "decl": w["decl"],
                          "modes": {"cold_no_daemon": m}})
            print(f"  blocked: exit={exit_code} error_class={err_class} "
                  f"median={m['median_ms']}ms", flush=True)
            return entry
        cold = self.run_cold_mode(w)
        print(f"  cold median={cold['median_ms']}ms rel_spread={cold['rel_spread']}", flush=True)
        warm_cache, warm_edit = self.run_warm_modes(w)
        print(f"  warm cache-hit median={warm_cache['median_ms']}ms, "
              f"edited median={warm_edit['median_ms']}ms", flush=True)
        healthy = (
            cold["trials"] > 0 and cold["coverage_ratio_min"] is not None
            and cold["coverage_ratio_min"] >= COVERAGE_GATE
            and warm_cache["trials"] > 0
            and warm_cache["coverage_ratio_min"] >= COVERAGE_GATE
            and "cache_hit_assert_failed" not in warm_cache
            and warm_edit["trials"] > 0
            and warm_edit["coverage_ratio_min"] >= COVERAGE_GATE
            and "verified_assert_failed" not in warm_edit)
        return {"id": wid, "status": "ok" if healthy else "failed",
                "repo": w["repo"], "file": w["file"], "decl": w["decl"],
                "expected_status": "active",
                "modes": {"cold_no_daemon": cold, "warm_cache_hit_daemon": warm_cache,
                          "warm_edited_proof_daemon": warm_edit}}


# ------------------------------------------------------------------- main

def validate_environment(args):
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
        rev, _dirty = repo_commit(runner.git_bin, runner.dirs[repo])
        runner.revs[repo] = rev
        if rev != expected and not runner.args.skip_rev_check:
            raise BenchEnvError(
                f"{repo} checkout is at {rev}, benchmark is pinned to {expected}; "
                "point --batteries-dir/--pfr-dir at the pinned revs or pass "
                "--skip-rev-check (the JSON then records revs_pinned=false).")


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--turbo-lean-bin", default="target/release/turbo-lean")
    ap.add_argument("--batteries-dir")
    ap.add_argument("--pfr-dir")
    ap.add_argument("--trials", type=int, default=DEFAULT_TRIALS)
    ap.add_argument("--warmup", type=int, default=DEFAULT_WARMUP,
                    help="discarded settling runs before measured trials (default 1)")
    ap.add_argument("--out", help="write the full results JSON here")
    ap.add_argument("--baseline", help="baseline or prior results JSON to compare against "
                                       "(default: scripts/bench_check_loop_baseline.json "
                                       "when present)")
    ap.add_argument("--no-baseline", action="store_true", help="never compare")
    ap.add_argument("--rebaseline", action="store_true",
                    help="this run becomes the new baseline JSON (written to --out)")
    ap.add_argument("--machine-label", help="label for this machine/condition; a baseline "
                                            "from a different label is never compared")
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
        ap.error("--batteries-dir and --pfr-dir are required (unless --validate-only)")

    git_bin, git_human = validate_environment(args)
    runner = Runner(args)
    t_start = time.monotonic()
    try:
        load_at_start = require_quiet_node(args)
        check_pinned_revs(runner)
        commit, dirty, repo_path = turbo_lean_commit_for(runner.bin, git_bin)
        binary_sha = None
        h = host_id(args.machine_label)
        settings = {v: os.environ.get(v) for v in RECORDED_ENV_VARS}
        settings["git_version"] = git_human
        settings["scratch_root"] = str(runner.scratch)
        results = empty_run_result(WORKLOADS, args.trials)
        results.update({
            "turbo_lean_commit": commit, "turbo_lean_dirty": dirty,
            "turbo_lean_repo": repo_path,
            "turbo_lean_binary": {"path": str(runner.bin), "sha256": binary_sha},
            "host": h, "settings": settings, "workload_revs": dict(runner.revs),
            "revs_pinned": (not args.skip_rev_check),
            "node": {"load1_at_start": None if load_at_start is None else round(load_at_start, 2),
                     "load1_at_end": None,
                     "busy_allowed": args.allow_busy_node},
            "args": {"trials": args.trials, "warmup": args.warmup,
                     "skip_rev_check": args.skip_rev_check},
        })
        for w in WORKLOADS:
            entry = runner.run_workload(w)
            results["workloads"][w["id"]] = entry
        baseline = None
        if not args.no_baseline:
            bpath = args.baseline
            if bpath is None:
                default = Path(__file__).resolve().parent / "bench_check_loop_baseline.json"
                bpath = default if default.is_file() else None
            if bpath is not None:
                try:
                    baseline = json.loads(Path(bpath).read_text())
                    errs = validate_baseline(baseline)
                    if errs:
                        print(f"warning: baseline {bpath} failed validation: {errs}",
                              file=sys.stderr)
                        baseline = None
                except (OSError, json.JSONDecodeError) as e:
                    print(f"warning: cannot load baseline {bpath}: {e}", file=sys.stderr)
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
        print(f"VERDICT: {verdict['verdict']}"
              + (f" ({verdict['skipped_reason']})" if verdict.get("skipped_reason") else "")
              + (f" regressions={verdict['regressions']}" if verdict["regressions"] else "")
              + (f" unexpected_successes={verdict['unexpected_successes']}"
                 if verdict["unexpected_successes"] else ""), flush=True)
        code = VERDICT_EXIT[verdict["verdict"]]
        if (code == 0 and args.strict_comparison
                and str(verdict["verdict"]).startswith("comparison_skipped")):
            code = 1
        return code
    except BenchEnvError as e:
        print(f"ENVIRONMENT ERROR (exit 4): {e}", file=sys.stderr)
        return 4
    finally:
        shutil.rmtree(runner.scratch, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
