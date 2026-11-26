#!/usr/bin/env python3
"""Build-shaped warm loop: warm cache-hit `turbo-lean build` on a generated Lake fixture.

The pinned check-loop bench (scripts/bench_check_loop.py) drives `check`, so it
never reaches `run_build_command_with_cas_replay`
(crates/turbo-lean/src/lake_build/build.rs), the path behind the `build` CLI.
This script drives that path on a small generated Lake fixture and records how
long a warm (cache-hit) build takes:

1. cold: one `turbo-lean build --seed-shards` into a fresh CAS. Expected:
   status `built` and `shards_seeded` equal to the fixture's theorem count (one
   receipt per theorem, so the fixture is the one the generator meant).
2. warm: `--warmup` discarded calls, then `--trials` measured calls of
   `turbo-lean build` (no `--seed-shards`). Expected: status `cache_hit`.
3. summary: median and quartiles of the external wall and of the tool's own
   `elapsed_ms` over the measured calls.

History: this script was written for roadmap/HORIZONS.md row G2b and measured
that row's warm CAS-expr replay opt-in ON vs OFF (scripts/bench_build_loop_g2b.json,
written at 0a593169 in this script's schema-1 shape; do not write over it). The
opt-in cost about 15 ms per warm build and produced counters only, so it was
deleted along with this script's ON/OFF sides. The cold call still seeds, so a
run here measures the same kind of store as that artifact's OFF side.

Every call is a fresh process with TURBO_LEAN_NO_DAEMON=1, telemetry off, and a
private TURBO_LEAN_HOME, staging dir and TMPDIR under the run's scratch root.
The former warm-replay opt-in (TURBO_LEAN_WARM_CAS_REPLAY) is removed from every
call's environment and its force-off switch (TURBO_LEAN_NO_WARM_CAS_REPLAY) is
set to 1, so a binary built before their deletion also measures a plain warm
build. A call that exits non-zero, prints no JSON object, does not report its
expected status, or reports that a replay ran is a failed trial: it is kept out
of the medians, counted, and the verdict is `measurement_failed` (exit 1). A call
that outlives --build-timeout-s is killed together with the processes it started
(each call runs in its own session).

Typical run (one machine, one binary, `lean` on PATH through elan):

    python3 scripts/bench_build_loop.py \\
        --turbo-lean-bin target/release/turbo-lean \\
        --machine-label <label> --allow-busy-node \\
        --out <results.json>

The results JSON records no absolute path: the binary is recorded relative to
its repository (or by file name), path-valued caller settings as digests, the
scratch root not at all, and --machine-label replaces the node name in the
host block (the check-loop bench's rules, shared).

Exit codes:
    0  measured: the cold build and every warm call are healthy
    1  measurement failed: an unhealthy cold build or a failed warm trial
    2  usage error
    4  environment/setup failure (missing binary or `lean`, a busy node without
       --allow-busy-node, an --out directory that cannot be written, a binary
       that cannot be launched, ...)

Python standard library only. Host identity, PSI sampling and the statistics
are scripts/bench_check_loop.py's own, loaded from beside this file.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import shutil
import signal
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent


def _load_check_loop():
    """scripts/bench_check_loop.py as a module, for the helpers both benches share.

    Loaded by path under a private module name, so it works under `python3 -I`
    (the script's directory is then not on sys.path) and never replaces a
    caller's own `bench_check_loop` registration.
    """
    spec = importlib.util.spec_from_file_location(
        "_bench_check_loop_shared", SCRIPT_DIR / "bench_check_loop.py")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


bcl = _load_check_loop()
BenchEnvError = bcl.BenchEnvError

SCHEMA_VERSION = 2
DEFAULT_TRIALS = 20
DEFAULT_WARMUP = 1
DEFAULT_MODULES = 4
DEFAULT_THEOREMS_PER_MODULE = 50
BUILD_TIMEOUT_S = 900
# The warm-replay mode strings a binary from before the trigger's deletion reported
# when its replay ran (HORIZONS.md row G2b).
REPLAYING_MODES = ("warm_default", "warm_default_error", "warm_opt_in", "warm_opt_in_error")
# After a timed-out call's group is killed, how long its pipes may stay open.
KILL_DRAIN_S = 5
FIXTURE_LIB = "BenchFixture"
# The deleted G2b warm-replay opt-in. No current binary reads it; it is removed
# from every call, and the force-off switch is set in CHILD_COMMON, so an older
# binary cannot replay either.
RETIRED_SWITCHES = ("TURBO_LEAN_WARM_CAS_REPLAY",)
# What every child call gets on top of the caller's environment, with the
# scratch root written as a placeholder (the real paths stay out of the JSON).
# child_env builds the real environment from this table, so the recorded
# settings are what the calls ran with.
CHILD_COMMON = {
    "TURBO_LEAN_NO_WARM_CAS_REPLAY": "1",
    "TURBO_LEAN_HOME": "<scratch>/home",
    "TURBO_LEAN_STAGING_DIR": "<scratch>/staging",
    "TURBO_LEAN_NO_REMOTE_TELEMETRY": "1",
    "TURBO_LEAN_TELEMETRY": "off",
    "TURBO_LEAN_NO_DAEMON": "1",
    "TMPDIR": "<scratch>/tmp",
}


# ------------------------------------------------------------------ fixture

def fixture_files(modules: int, theorems_per_module: int, toolchain: str) -> dict:
    """The generated Lake project as {relative path: text}; deterministic.

    One `lean_lib` of `modules` independent modules (they compile in parallel
    on the cold build), each holding `theorems_per_module` distinct `omega`
    theorems, and a root module importing them all. Each theorem is one clean
    shard for the splitter, so the cold `--seed-shards` seeds exactly
    modules * theorems_per_module receipts.
    """
    files = {
        "lean-toolchain": toolchain.strip() + "\n",
        "lakefile.toml": (f'name = "benchfixture"\n'
                          f'defaultTargets = ["{FIXTURE_LIB}"]\n'
                          f"\n"
                          f"[[lean_lib]]\n"
                          f'name = "{FIXTURE_LIB}"\n'),
    }
    imports = []
    for m in range(modules):
        imports.append(f"import {FIXTURE_LIB}.M{m}\n")
        body = []
        for t in range(theorems_per_module):
            k = m * theorems_per_module + t + 1
            body.append(f"theorem bf_m{m}_t{t} (n : Nat) : n + {k} = {k} + n := by omega\n")
        files[f"{FIXTURE_LIB}/M{m}.lean"] = "\n".join(body)
    files[f"{FIXTURE_LIB}.lean"] = "".join(imports)
    return files


def fixture_digest(files: dict) -> str:
    h = hashlib.sha256()
    for rel in sorted(files):
        h.update(rel.encode() + b"\0" + files[rel].encode() + b"\0")
    return h.hexdigest()


def write_fixture(root: Path, files: dict) -> None:
    for rel, text in files.items():
        p = root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)


# The run's scratch root holds the tool's read-only closure-snapshot
# directories; the check-loop bench's remove_tree clears those too.
remove_tree = bcl.remove_tree


def repo_lean_toolchain() -> str:
    p = REPO_ROOT / "lean" / "lean-toolchain"
    try:
        val = p.read_text().strip()
    except OSError as e:
        raise BenchEnvError(
            f"cannot read lean/lean-toolchain ({e}); pass --lean-toolchain") from e
    if not val:
        raise BenchEnvError("lean/lean-toolchain is empty; pass --lean-toolchain")
    return val


# ------------------------------------------------------------- environment

def validate_environment(args) -> Path:
    """Fail closed before any measurement; returns the resolved binary."""
    binary = Path(args.turbo_lean_bin)
    if not binary.is_file():
        raise BenchEnvError(f"turbo-lean binary not found: {args.turbo_lean_bin}")
    if not os.access(binary, os.X_OK):
        raise BenchEnvError(f"turbo-lean binary is not executable: {args.turbo_lean_bin}")
    if not shutil.which("lean"):
        raise BenchEnvError(
            "lean is not on PATH; the cold build compiles the fixture "
            "(export PATH=\"$HOME/.elan/bin:$PATH\")")
    return binary.resolve()


def refuse_other_artifact(out: Path) -> None:
    """An existing --out file must be an earlier result of this script's own schema.

    A committed record of another shape (the schema-1 G2b artifact, a check-loop
    results file) is evidence this run would replace, so it exits 4 first. A file
    that is not JSON is refused too; a missing file is fine.
    """
    if not out.exists():
        return
    if out.is_dir():
        raise BenchEnvError(f"--out: {out.name} is a directory")
    if not os.access(out, os.W_OK):
        raise BenchEnvError(f"--out: {out.name} exists and is not writable")
    try:
        old = json.loads(out.read_text())
    except (OSError, ValueError) as e:
        raise BenchEnvError(f"--out: {out.name} exists and is not a results JSON ({e})") from e
    if not isinstance(old, dict):
        raise BenchEnvError(
            f"--out: {out.name} exists and holds {type(old).__name__} JSON, not a JSON "
            "object; refusing to overwrite it")
    if (old.get("schema_version"), old.get("kind")) != (SCHEMA_VERSION, "build_loop_results"):
        raise BenchEnvError(
            f"--out: {out.name} exists with schema_version {old.get('schema_version')!r} / "
            f"kind {old.get('kind')!r}, not this script's schema {SCHEMA_VERSION} "
            "build_loop_results; refusing to overwrite it")


def lean_version(fixture_dir: Path) -> str:
    """`lean --version` run inside the fixture, so elan resolves its toolchain."""
    lean_bin = shutil.which("lean")
    try:
        proc = subprocess.run([lean_bin, "--version"], cwd=str(fixture_dir),
                              capture_output=True, text=True, timeout=300)
    except (OSError, subprocess.SubprocessError) as e:
        raise BenchEnvError(f"failed to run `lean --version` in the fixture: {e}") from e
    lines = (proc.stdout or "").strip().splitlines()
    if proc.returncode != 0 or not lines or not lines[0].strip():
        raise BenchEnvError(
            f"`lean --version` in the fixture failed (exit {proc.returncode}): "
            f"{(proc.stderr or '')[-300:].strip()}")
    return lines[0].strip()


def read_loadavg():
    """The first three /proc/loadavg fields, or None when unreadable."""
    try:
        return " ".join(Path("/proc/loadavg").read_text().split()[:3])
    except OSError:
        return None


def load1_now():
    try:
        return round(os.getloadavg()[0], 2)
    except (OSError, AttributeError):
        return None


# The binary relative to its repository, else by file name; the check-loop
# bench's own rule, so both benches' artifacts carry no host path.
binary_record = bcl.binary_record


# ------------------------------------------------------------- build calls

def child_env(scratch: Path) -> dict:
    env = dict(os.environ)
    for var in RETIRED_SWITCHES:
        env.pop(var, None)
    env.update({key: value.replace("<scratch>", str(scratch))
                for key, value in CHILD_COMMON.items()})
    return env


def build_argv(binary, scratch: Path, seed: bool) -> list:
    argv = [str(binary), "--cache-dir", str(scratch / "cache"), "--json",
            "--no-telemetry", "build", "--project-dir", str(scratch / "fixture")]
    if seed:
        argv.append("--seed-shards")
    return argv


def _partial(v) -> str:
    """Text of the partial output a TimeoutExpired carries (bytes, str or None)."""
    return bcl._decode_partial(v)


def _kill_group(proc) -> None:
    """SIGKILL the call's whole process group (it leads its own session)."""
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except (ProcessLookupError, PermissionError):
        pass


def _end_escaped(argv, env):
    """End what a timed-out call left in the run's staging namespace.

    The group kill misses a worker that started its own session. The check-loop
    bench's scope rule (the staging namespace and this binary) finds those, and
    its SIGTERM-then-SIGKILL ends them. Returns (note for the trial's stderr,
    contaminated): contaminated is True when a process could not be ended, and the
    caller then stops measuring, because a stray process skews every later call.
    """
    staging = env.get("TURBO_LEAN_STAGING_DIR")
    if not staging:
        return "; a process may have escaped the call's group (no staging namespace to scan)", False
    try:
        left = bcl.scoped_daemon_processes(staging, Path(argv[0]).resolve())
        if not left:
            return "; the call's pipes stayed open after the kill but no process was found", False
        _signalled, survivors = bcl.terminate_scanned(left)
    except OSError as e:
        return f"; a process escaped the call's group and the scan failed ({e})", True
    if survivors:
        return (f"; {len(survivors)} process(es) escaped the call's group and could not be "
                "ended"), True
    return f"; {len(left)} process(es) escaped the call's group and were ended", False


def run_build(argv, env, timeout_s):
    """One build call, in its own session so a timeout takes lake and lean with it."""
    psi_before = bcl.sample_psi()
    t0 = time.perf_counter_ns()
    try:
        proc = subprocess.Popen(argv, env=env, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, text=True, start_new_session=True)
    except OSError as e:
        raise BenchEnvError(f"failed to launch {argv[0]}: {e}") from e
    contaminated = False
    try:
        out, err = proc.communicate(timeout=timeout_s)
        rc = proc.returncode
    except subprocess.TimeoutExpired:
        _kill_group(proc)
        note = ""
        try:
            out, err = proc.communicate(timeout=KILL_DRAIN_S)
        except subprocess.TimeoutExpired as e:
            # A descendant that left the process group (a zygote worker) can still
            # hold the pipes: keep what was read, close our ends and move on.
            out, err = _partial(e.stdout), _partial(e.stderr)
            for pipe in (proc.stdout, proc.stderr):
                if pipe is not None:
                    pipe.close()
            proc.wait()
            note, contaminated = _end_escaped(argv, env)
        rc = -1
        err = (err or "") + f"\ntimeout after {timeout_s}s" + note
    except BaseException:
        _kill_group(proc)
        proc.wait()
        raise
    wall_ms = (time.perf_counter_ns() - t0) / 1e6
    psi_after = bcl.sample_psi()
    return {"exit_code": rc, "external_wall_ms": wall_ms,
            "json": bcl.parse_check_json(out or ""), "stderr": err or "",
            "psi_before": psi_before, "psi_after": psi_after,
            "contaminated": contaminated}


def path_roots(scratch: Path, binary: Path, git_bin=None) -> list:
    """The (root, placeholder) pairs a recorded stderr excerpt may name.

    The check-loop bench's rule: the scratch root, the binary's directory, this
    repository, the working and temp directories, the home directory, and the
    directory of an absolute TURBO_LEAN_GIT, each as written and as resolved.
    """
    lean = shutil.which("lean")
    toolchain = [(str(Path(lean).parent), "<lean-dir>")] if lean else []
    return bcl.host_path_roots(scratch, {}, binary, git_bin, extra_roots=toolchain)


def _failure_head(r, roots=None):
    if r.get("exit_code") != 0:
        stderr = r.get("stderr") or ""
        if roots:
            # Scrub before cutting the tail, so a path split by the cut cannot leak.
            stderr = bcl.scrub_host_paths(stderr, roots)
        tail = stderr[-300:].strip()
        return f"exit {r.get('exit_code')}" + (f": {tail}" if tail else "")
    if not isinstance(r.get("json"), dict):
        return "no JSON object on stdout"
    return None


def _scrubbed(text, roots):
    """`text` with every host root replaced by its placeholder (None stays None)."""
    return bcl.scrub_host_paths(text, roots) if text and roots else text


def cold_problem(r, theorems: int, roots=None):
    """None when the cold seeded build met its expectation, else why not (scrubbed)."""
    return _scrubbed(_cold_problem(r, theorems, roots), roots)


def _cold_problem(r, theorems: int, roots=None):
    head = _failure_head(r, roots)
    if head:
        return head
    j = r["json"]
    if j.get("status") != "built":
        return f"status {j.get('status')!r}, expected 'built'"
    if j.get("shards_seeded") != theorems:
        return (f"shards_seeded {j.get('shards_seeded')!r}, expected {theorems} "
                "(one per fixture theorem)")
    return None


def trial_problem(r, roots=None):
    """None when a warm call was a healthy cache hit that replayed nothing, else why
    not (scrubbed)."""
    return _scrubbed(_trial_problem(r, roots), roots)


def _trial_problem(r, roots=None):
    head = _failure_head(r, roots)
    if head:
        return head
    j = r["json"]
    status = j.get("status")
    if status != "cache_hit":
        return f"status {status!r}, expected 'cache_hit'"
    replayed, mode = j.get("cas_expr_replayed"), j.get("cas_expr_replay_mode")
    count = replayed if isinstance(replayed, int) and not isinstance(replayed, bool) else None
    if (count is not None and count > 0) or mode in REPLAYING_MODES:
        return (f"a warm replay ran (cas_expr_replayed {replayed!r}, "
                f"cas_expr_replay_mode {mode!r}); the bench measures a build that "
                "replays nothing")
    # Anything but a non-negative integer (a negative, NaN, float, string, bool) is
    # not a count this bench understands.
    if replayed is not None and (count is None or count < 0):
        return f"unrecognized cas_expr_replayed {replayed!r}; cannot tell whether a replay ran"
    if mode not in (None, "off"):
        return (f"unrecognized cas_expr_replay_mode {mode!r}; cannot tell whether a "
                "replay ran")
    return None


# --------------------------------------------------------------- statistics

def quartiles(xs):
    """(q1, q3) by the inclusive method; None for fewer than two values."""
    if len(xs) < 2:
        return None
    q1, _q2, q3 = statistics.quantiles(xs, n=4, method="inclusive")
    return q1, q3


def series_stats(xs) -> dict:
    q = quartiles(xs)
    return {
        "n": len(xs),
        "median_ms": round(bcl.median(xs), 1) if xs else None,
        "q1_ms": round(q[0], 1) if q else None,
        "q3_ms": round(q[1], 1) if q else None,
        "iqr_ms": round(q[1] - q[0], 1) if q else None,
        "rel_spread": round(bcl.rel_spread(xs), 4) if len(xs) > 1 else 0.0,
    }


def tool_elapsed(t):
    v = (t.get("json") or {}).get("elapsed_ms")
    return float(v) if isinstance(v, (int, float)) and not isinstance(v, bool) else None


def summarize_warm(trials) -> dict:
    """The measured warm calls, in the check-loop bench's mode-result shape plus
    quartiles and the tool's own elapsed_ms."""
    healthy = [t for t in trials if t["problem"] is None]
    walls = [t["external_wall_ms"] for t in healthy]
    out = bcl.mode_result(
        walls, [], [str(t["json"].get("status")) for t in healthy],
        psi_lists=[[t["psi_before"], t["psi_after"]] for t in healthy],
        failed_trials=len(trials) - len(healthy))
    # The build path has no phase-coverage meter; these stay out rather than null.
    out.pop("coverage_ratio_min", None)
    out.pop("coverage_ratio_external_min", None)
    wall = series_stats(walls)
    out.update({"q1_ms": wall["q1_ms"], "q3_ms": wall["q3_ms"], "iqr_ms": wall["iqr_ms"]})
    elapsed = [e for e in (tool_elapsed(t) for t in healthy) if e is not None]
    out["tool_elapsed_ms"] = dict(series_stats(elapsed), runs_ms=[round(e, 1) for e in elapsed])
    out["materialized_files_observed"] = sorted(
        {t["json"].get("materialized_files") for t in healthy}, key=repr)
    problems = [f"call {t['call']}: {t['problem']}" for t in trials if t["problem"]]
    if problems:
        out["problems"] = problems[:5]
    return out


# --------------------------------------------------------------------- main

def cold_record(r, problem) -> dict:
    j = r.get("json") if isinstance(r.get("json"), dict) else {}
    rec = {"exit_code": r.get("exit_code"),
           "external_wall_ms": round(r["external_wall_ms"], 1),
           "problem": problem}
    for key in ("status", "elapsed_ms", "shards_seeded", "modules_total",
                "modules_compiled", "artifacts_stored", "materialized_files"):
        rec[key] = j.get(key)
    return rec


def print_summary(results) -> None:
    warm = results.get("warm")
    if warm and warm.get("median_ms") is not None:
        el = warm["tool_elapsed_ms"]
        print(f"BUILD LOOP: warm cache-hit build, external wall median {warm['median_ms']} ms "
              f"(IQR {warm['q1_ms']}-{warm['q3_ms']}, n={warm['trials']}, "
              f"failed {warm['failed_trials']}) | tool elapsed_ms median {el['median_ms']} ms "
              f"(IQR {el['q1_ms']}-{el['q3_ms']})", flush=True)
    v = results["verdict"]
    print(f"VERDICT: {v['verdict']}"
          + (f" problems={v['problems']}" if v["problems"] else ""), flush=True)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--turbo-lean-bin", default="target/release/turbo-lean")
    ap.add_argument("--trials", type=int, default=DEFAULT_TRIALS,
                    help=f"measured warm builds (default {DEFAULT_TRIALS})")
    ap.add_argument("--warmup", type=int, default=DEFAULT_WARMUP,
                    help=f"discarded warm builds before the measured ones (default {DEFAULT_WARMUP})")
    ap.add_argument("--modules", type=int, default=DEFAULT_MODULES,
                    help=f"fixture modules (default {DEFAULT_MODULES})")
    ap.add_argument("--theorems-per-module", type=int, default=DEFAULT_THEOREMS_PER_MODULE,
                    help=f"theorems per fixture module (default {DEFAULT_THEOREMS_PER_MODULE})")
    ap.add_argument("--lean-toolchain",
                    help="toolchain line for the fixture (default: lean/lean-toolchain)")
    ap.add_argument("--build-timeout-s", type=int, default=BUILD_TIMEOUT_S,
                    help=f"per-call wall budget in seconds (default {BUILD_TIMEOUT_S})")
    ap.add_argument("--scratch-dir",
                    help="parent directory of the run's scratch root (default: the "
                         "system temp dir); the root is removed at the end")
    ap.add_argument("--keep-scratch", action="store_true",
                    help="leave the scratch root (fixture, CAS, homes) in place")
    ap.add_argument("--out", help="write the results JSON here")
    ap.add_argument("--machine-label",
                    help="recorded as the host hostname in place of the live node name")
    ap.add_argument("--allow-busy-node", action="store_true",
                    help=f"run even when the 1-min load average exceeds "
                         f"{bcl.BUSY_LOAD_THRESHOLD} (recorded as busy_allowed)")
    args = ap.parse_args(argv)
    for name in ("trials", "modules", "theorems_per_module", "build_timeout_s"):
        if getattr(args, name) < 1:
            ap.error(f"--{name.replace('_', '-')} must be >= 1, got {getattr(args, name)}")
    if args.warmup < 0:
        ap.error(f"--warmup must be >= 0, got {args.warmup}")

    t_start = time.monotonic()
    scratch = None
    try:
        binary = validate_environment(args)
        if args.scratch_dir and not Path(args.scratch_dir).is_dir():
            raise BenchEnvError(f"--scratch-dir is not a directory: {args.scratch_dir}")
        if args.out:
            # Fail before the cold build, not after the last warm call.
            out_dir = Path(args.out).resolve().parent
            if not out_dir.is_dir() or not os.access(out_dir, os.W_OK | os.X_OK):
                raise BenchEnvError(
                    f"--out: {out_dir} is not a writable directory")
            refuse_other_artifact(Path(args.out))
        loadavg_at_start = read_loadavg()
        load_at_start = bcl.require_quiet_node(args)
        toolchain_line = args.lean_toolchain or repo_lean_toolchain()
        files = fixture_files(args.modules, args.theorems_per_module, toolchain_line)
        theorems = args.modules * args.theorems_per_module
        scratch = Path(tempfile.mkdtemp(prefix="build-loop-",
                                        dir=args.scratch_dir)).resolve()
        for sub in ("fixture", "cache", "home", "staging", "tmp"):
            (scratch / sub).mkdir()
        (scratch / "tmp").chmod(0o700)
        write_fixture(scratch / "fixture", files)
        lean_ver = lean_version(scratch / "fixture")
        git_bin = os.environ.get("TURBO_LEAN_GIT") or shutil.which("git") or "git"
        commit, dirty, repo_path = bcl.turbo_lean_commit_for(binary, git_bin)
        binary_sha = hashlib.sha256(binary.read_bytes()).hexdigest()
        env = child_env(scratch)
        results = {
            "schema_version": SCHEMA_VERSION, "kind": "build_loop_results",
            "created_utc": bcl.utc_now_iso(),
            "turbo_lean_commit": commit, "turbo_lean_dirty": dirty,
            "turbo_lean_binary": binary_record(binary, repo_path, binary_sha),
            "toolchain": {"lean_toolchain": toolchain_line, "lean_version": lean_ver},
            "host": bcl.host_id(args.machine_label),
            "node": {"load1_at_start": load_at_start, "loadavg_at_start": loadavg_at_start,
                     "load1_at_end": None, "loadavg_at_end": None,
                     "busy_allowed": args.allow_busy_node},
            "settings": {
                "caller": bcl.recorded_settings(), "child_common": dict(CHILD_COMMON),
                "child_removed": list(RETIRED_SWITCHES),
                "argv_cold": ["turbo-lean"] + [
                    a.replace(str(scratch), "<scratch>") for a in build_argv("", scratch, True)[1:]],
                "argv_warm": ["turbo-lean"] + [
                    a.replace(str(scratch), "<scratch>") for a in build_argv("", scratch, False)[1:]],
            },
            "fixture": {"lib": FIXTURE_LIB, "modules": args.modules,
                        "theorems_per_module": args.theorems_per_module,
                        "theorems": theorems, "sha256": fixture_digest(files)},
            "args": {"trials": args.trials, "warmup": args.warmup,
                     "build_timeout_s": args.build_timeout_s},
        }
        print(f"[{bcl.utc_now_iso()}] cold seeded build ({args.modules} modules x "
              f"{args.theorems_per_module} theorems) ...", flush=True)
        cold = run_build(build_argv(binary, scratch, True), env, args.build_timeout_s)
        roots = path_roots(scratch, binary, git_bin)
        problem = cold_problem(cold, theorems, roots)
        results["cold"] = cold_record(cold, problem)
        problems = [f"cold: {problem}"] if problem else []
        if not problem:
            print(f"  cold built in {cold['external_wall_ms']:.0f} ms, "
                  f"{cold['json']['shards_seeded']} shards seeded; {args.warmup} warmup + "
                  f"{args.trials} measured warm builds ...", flush=True)
            trials = []
            for call in range(args.warmup + args.trials):
                r = run_build(build_argv(binary, scratch, False), env, args.build_timeout_s)
                r.update(call=call, measured=call >= args.warmup,
                         problem=trial_problem(r, roots))
                trials.append(r)
                if r["contaminated"]:
                    # A process the bench could not end skews every later call.
                    print("  stopping the warm loop: a stray process could not be ended",
                          flush=True)
                    break
            results["sequence"] = [{"call": t["call"], "measured": t["measured"],
                                    "ok": t["problem"] is None} for t in trials]
            warm = summarize_warm([t for t in trials if t["measured"]])
            results["warm"] = warm
            problems.extend(warm.get("problems", []))
            warm_failed = [t for t in trials if not t["measured"] and t["problem"]]
            for t in warm_failed[:3]:
                problems.append(f"warmup call {t['call']}: {t['problem']}")
        # The problem strings were scrubbed where cold_problem and trial_problem made them.
        results["verdict"] = {"verdict": "measurement_failed" if problems else "measured",
                              "problems": problems}
        results["run_duration_s"] = round(time.monotonic() - t_start, 1)
        results["node"]["load1_at_end"] = load1_now()
        results["node"]["loadavg_at_end"] = read_loadavg()
        payload = json.dumps(results, indent=2)
        if args.out:
            Path(args.out).write_text(payload + "\n")
            print(f"results written to {args.out}")
        else:
            print(payload)
        print_summary(results)
        return 1 if problems else 0
    except BenchEnvError as e:
        print(f"ENVIRONMENT ERROR (exit 4): {e}", file=sys.stderr)
        return 4
    finally:
        if scratch is not None and not args.keep_scratch:
            remove_tree(scratch)


if __name__ == "__main__":
    sys.exit(main())
