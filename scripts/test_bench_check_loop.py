#!/usr/bin/env python3
"""Contract tests for `scripts/bench_check_loop.py` (M1 pinned benchmark).

Run: python3 scripts/test_bench_check_loop.py
No Lean toolchain or turbo-lean build required: the end-to-end case drives the
script with a stub binary that emulates `check --json`.
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import math
import os
import platform
import re
import signal
import stat
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path
from unittest import mock

SCRIPT = Path(__file__).resolve().parent / "bench_check_loop.py"

# The bench signals processes it finds in /proc, and several tests let it run
# against the real /proc. For the whole test run, every way it can send a signal
# (os.kill, os.killpg, a pidfd from os.pidfd_open) refuses a target that this
# test process did not start, so a defect or a mutation in its scope rule can
# never reach another process of the same user on a shared machine. A bench the
# tests run as a subprocess starts through BENCH_CMD, which runs it inside this
# module, so it carries the same guard. Each refusal is written to stderr and
# recorded in REFUSED_SIGNALS; the NoForeignSignals tests fail on any.
REFUSED_SIGNALS = []
GUARD_REFUSAL = "test guard refused"
BENCH_CMD = [sys.executable, str(Path(__file__).resolve()), "--run-guarded", str(SCRIPT)]


def started_by_this_run(pid: int) -> bool:
    """True when `pid` is this test process or one of its descendants."""
    me = os.getpid()
    for _ in range(64):
        if pid == me:
            return True
        if pid <= 1:
            return False
        try:
            fields = Path(f"/proc/{pid}/stat").read_text().rpartition(") ")[2].split()
            pid = int(fields[1])  # field 4: the parent pid
        except (OSError, IndexError, ValueError):
            return False
    return False


def _refuse_foreign(name, real):
    def guarded(pid, *args):
        if not started_by_this_run(pid):
            REFUSED_SIGNALS.append((name, pid))
            sys.stderr.write(f"{GUARD_REFUSAL} {name}({pid})\n")
            raise PermissionError(f"test guard: {name}({pid}) targets a process "
                                  "this test run did not start")
        return real(pid, *args)
    return guarded


os.kill = _refuse_foreign("kill", os.kill)
os.killpg = _refuse_foreign("killpg", os.killpg)
if hasattr(os, "pidfd_open"):
    os.pidfd_open = _refuse_foreign("pidfd_open", os.pidfd_open)


class NoForeignSignals:
    """A test fails when the bench tried to signal a process it did not start."""

    def setUp(self):
        super().setUp()
        REFUSED_SIGNALS.clear()

    def tearDown(self):
        refused = list(REFUSED_SIGNALS)
        REFUSED_SIGNALS.clear()
        super().tearDown()
        self.assertEqual(refused, [], "the bench tried to signal a process this test "
                         "did not start")


def load_script():
    spec = importlib.util.spec_from_file_location("bench_check_loop", SCRIPT)
    mod = importlib.util.module_from_spec(spec)
    # Register before exec, per the importlib recipe: the script uses
    # `from __future__ import annotations`, so its dataclass resolves field
    # annotations through sys.modules[module name] at class-creation time.
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


def make_stub_binary(root: Path, body: str | None = None):
    stub = root / "fake-turbo-lean"
    stub.write_text(body or (
        "#!/usr/bin/env python3\n"
        "import json, os, sys, time\n"
        "args = sys.argv[1:]\n"
        "time.sleep(0.04)\n"
        "if os.environ.get('FAKE_PFR_FAIL') and '--no-auto-worktree-link' in args:\n"
        "    print(json.dumps({'error': 'stale imports: import_refresh fail-closed'}))\n"
        "    sys.exit(1)\n"
        "status = 'theorem_verified'\n"
        "if not os.environ.get('TURBO_LEAN_NO_DAEMON'):\n"
        "    try:\n"
        "        body = open(args[-1]).read()\n"
        "        status = ('theorem_verified' if '_m1_bench_trial_' in body\n"
        "                  else 'theorem_cache_hit')\n"
        "    except OSError:\n"
        "        pass\n"
        "wall = float(os.environ.get('FAKE_WALL_MS', '200'))\n"
        "cov = float(os.environ.get('FAKE_COV', '0.99'))\n"
        "out = {'status': status, 'decl': 'd', 'elapsed_ms': 50,\n"
        "       'phase_timings': {'wall_ms': wall, 'phase_sum_ms': wall - 1,\n"
        "                         'phase_covered_ms': wall - 1, 'phase_overlap_ms': 0.0,\n"
        "                         'coverage_ratio': cov,\n"
        "                         'phases_ms': {'setup': 10.0, 'elaboration': wall - 11.0}}}\n"
        "print(json.dumps(out)); sys.exit(0)\n"
    ))
    stub.chmod(0o755)
    real_git = __import__("shutil").which("git") or "/usr/bin/git"
    gitstub = root / "fake-git"
    gitstub.write_text(
        "#!/bin/sh\n"
        "if [ \"$1\" = \"--version\" ]; then printf 'git version 2.47.1\\n'; exit 0; fi\n"
        f"exec {real_git} \"$@\"\n")
    gitstub.chmod(0o755)
    return stub, gitstub


def make_fake_projects(root: Path):
    bats = root / "batteries"
    files = {
        "Batteries/Data/List/Lemmas.lean": "theorem dropLast_eq_eraseIdx :\n"
                                           "    True := by\n  trivial\n",
        "Batteries/Data/String/Lemmas.lean": "theorem lt_antisymm :\n"
                                             "    True := by\n  trivial\n",
        "Batteries/Recycling/RBTree/Lemmas.lean": (
            "@[simp] theorem min?_reverse :\n    True := by\n  trivial\n"
            "theorem ordered_iff :\n    True := by\n  trivial\n"),
        "Batteries/Data/UnionFind/Basic.lean": "theorem parentD_eq :\n"
                                               "    True := by\n  trivial\n",
    }
    for rel, body in files.items():
        p = bats / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(body)
    (bats / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
    pfr = root / "pfr"
    (pfr / "PFR").mkdir(parents=True, exist_ok=True)
    (pfr / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
    (pfr / "PFR" / "MoreRuzsaDist.lean").write_text(
        "lemma rdist_of_neg_le : True := by trivial\n")
    bin_dir = root / "fake-bin"
    bin_dir.mkdir(exist_ok=True)
    leanstub = bin_dir / "lean"
    leanstub.write_text("#!/bin/sh\nprintf 'Lean (version 4.35.0, fake)\\n'\n")
    leanstub.chmod(0o755)
    real_git = __import__("shutil").which("git") or "/usr/bin/git"
    git_env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t",
                   GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@t")
    for proj in (bats, pfr):
        if not (proj / ".git").exists():
            subprocess.run([real_git, "-C", str(proj), "init", "-q"], check=True, env=git_env)
            subprocess.run([real_git, "-C", str(proj), "add", "-A"], check=True, env=git_env)
            subprocess.run([real_git, "-C", str(proj), "commit", "-q", "-m", "init"],
                           check=True, env=git_env)
    return bats, pfr


def run_bench(root, extra, stub_body=None, env_extra=None, make_projects=True):
    stub, gitstub = make_stub_binary(root, stub_body)
    if make_projects:
        make_fake_projects(root)
    bats, pfr = root / "batteries", root / "pfr"
    path_prefix = str(root / "fake-bin")
    env = dict(os.environ, TURBO_LEAN_GIT=str(gitstub),
               PATH=path_prefix + os.pathsep + os.environ.get("PATH", ""),
               TURBO_LEAN_ALLOWED_CSIMP="*", TURBO_LEAN_ALLOWED_UNSAFE="*",
               TURBO_LEAN_ALLOWED_IMPLEMENTED_BY="*", FAKE_PFR_FAIL="1")
    env.update(env_extra or {})
    cmd = BENCH_CMD + ["--turbo-lean-bin", str(stub),
                       "--batteries-dir", str(bats), "--pfr-dir", str(pfr),
                       "--trials", "2", "--warmup", "0", "--skip-rev-check",
                       "--allow-busy-node"] + extra
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=600, env=env)
    if GUARD_REFUSAL in r.stderr:
        raise AssertionError("the bench tried to signal a process this test did not "
                             "start:\n" + r.stderr)
    return r


def sample_baseline(mod, **overrides):
    return mod.make_baseline(
        turbo_lean_commit="8a1d67dba051f59440c91df828584657efd12605",
        host={"hostname": "bench-host", "machine_label": "lab-node-1",
              # A labeled host must carry a fingerprint (a label on either
              # side requires both); fixtures compared against copies of this
              # host say "same machine, same condition".
              "host_fingerprint": "c" * 64,
              "kernel": "Linux 6.8", "cpu_model": "test-cpu", "nproc": 8, "mem_gb": 62},
        trials=5,
        settings={"TURBO_LEAN_GIT": "/fake/git", "TURBO_LEAN_ALLOWED_CSIMP": "*",
                  "TURBO_LEAN_ALLOWED_UNSAFE": "*", "TURBO_LEAN_ALLOWED_IMPLEMENTED_BY": "*",
                  **{v: None for v in ("TURBO_LEAN_HOME", "TURBO_LEAN_STAGING_DIR",
                                       "TURBO_LEAN_NO_DAEMON", "TURBO_LEAN_NO_REMOTE_TELEMETRY",
                                       "TURBO_LEAN_TELEMETRY", "TURBO_LEAN_DAEMON_IDLE_SECS")}},
         workloads={w["id"]: mod.empty_workload_result(w) for w in mod.WORKLOADS},
         turbo_lean_dirty=False,
         turbo_lean_binary={"path": "/fake/turbo-lean", "sha256": "a" * 64},
         workload_revs={"batteries": "b" * 40, "pfr": "c" * 40},
         toolchain={"lean_toolchain": "leanprover/lean4:v4.35.0",
                    "lean_version": "Lean (version 4.35.0)"},
     )



def fill_workload(mod, base, wid, median_ms, rel_spread=0.03, modes=None):
    base["workloads"][wid] = mod.active_workload_result(
        wid, {m: {"median_ms": median_ms, "rel_spread": rel_spread,
                  "trials": 5, "coverage_ratio_min": 0.9998}
              for m in (modes or mod.MODES)})


def full_valid_baseline(mod):
    base = sample_baseline(mod)
    for w in mod.WORKLOADS:
        if w["expected_status"] == "blocked":
            base["workloads"][w["id"]] = mod.blocked_workload_result(
                exit_code=1, error_class="stale_import_refresh_fail_closed",
                median_ms=6000.0)
        else:
            fill_workload(mod, base, w["id"], 1000.0)
    return base


class WorkloadTable(unittest.TestCase):
    def test_table_matches_m1_contract(self):
        mod = load_script()
        by_id = {w["id"]: w for w in mod.WORKLOADS}
        self.assertEqual(len(mod.WORKLOADS), 6)
        for wid in ("batteries_list_lemmas_top", "batteries_string_lemmas_top",
                    "batteries_rbtree_lemmas_top", "batteries_rbtree_lemmas_mid",
                    "batteries_unionfind_top"):
            self.assertEqual(by_id[wid]["expected_status"], "active", wid)
            self.assertEqual(by_id[wid]["repo"], "batteries", wid)
        pfr = by_id["pfr_more_ruzsa_dist"]
        self.assertEqual(pfr["expected_status"], "blocked")
        self.assertEqual(pfr["repo"], "pfr")
        self.assertTrue(pfr["extra_args"])
        for w in mod.WORKLOADS:
            self.assertIn("file", w) and self.assertIn("decl", w)
            self.assertTrue(w["file"].endswith(".lean"), w)

    def test_modes_defined(self):
        mod = load_script()
        self.assertIn("cold_no_daemon", mod.MODES)
        self.assertIn("warm_cache_hit_daemon", mod.MODES)
        self.assertIn("warm_edited_proof_daemon", mod.MODES)


class Stats(unittest.TestCase):
    def test_median(self):
        mod = load_script()
        self.assertEqual(mod.median([3.0, 1.0, 2.0]), 2.0)
        self.assertEqual(mod.median([4.0]), 4.0)
        self.assertTrue(math.isnan(mod.median([])))

    def test_rel_spread(self):
        mod = load_script()
        self.assertAlmostEqual(mod.rel_spread([100.0, 110.0, 90.0]), 0.2)
        self.assertEqual(mod.rel_spread([100.0, 100.0]), 0.0)

    def test_gate_grows_with_measured_spread(self):
        mod = load_script()
        tight = mod.tolerance_ms(1000.0, 0.02, "warm_cache_hit_daemon")
        loose = mod.tolerance_ms(1000.0, 0.20, "warm_cache_hit_daemon")
        cold = mod.tolerance_ms(1000.0, 0.0, "cold_no_daemon")
        self.assertGreater(loose, tight)
        self.assertAlmostEqual(tight, 1000.0 * 1.10 + 25.0)
        self.assertAlmostEqual(loose, 1000.0 * (1.0 + 2.0 * 0.20) + 25.0)
        # Cold workloads drift more between runs (page-cache-sensitive
        # import_refresh): their floor is 20%, not 10%.
        self.assertAlmostEqual(cold, 1000.0 * 1.20 + 25.0)


class CheckTimeoutOverride(unittest.TestCase):
    def test_env_override_reaches_subprocess_timeout(self):
        # TURBO_LEAN_BENCH_CHECK_TIMEOUT_S is folded into CHECK_TIMEOUT_S by
        # validate_environment through _apply_check_timeout_override(),
        # validated (junk is a BenchEnvError, exit 4, never a bare crash).
        # The child's `--timeout` argv reads the global at call time;
        # subprocess.run's own bound must carry the same value, so run_check
        # may not freeze the module global into its parameter default at
        # definition time.
        key = "TURBO_LEAN_BENCH_CHECK_TIMEOUT_S"
        prev = os.environ.get(key)
        os.environ[key] = "123"
        try:
            # Real script behavior, no hand rebind: import keeps the 900
            # default; the override call applies the env value; junk raises.
            mod = load_script()
            self.assertEqual(mod.CHECK_TIMEOUT_S, 900)
            mod._apply_check_timeout_override()
            self.assertEqual(mod.CHECK_TIMEOUT_S, 123)
            os.environ[key] = "junk"
            with self.assertRaises(mod.BenchEnvError):
                mod._apply_check_timeout_override()
            os.environ[key] = "123"

            recorded = {}

            class FakeProc:
                returncode = 0
                stdout = "{}"
                stderr = ""

            class FakeSubprocess:
                TimeoutExpired = subprocess.TimeoutExpired

                @staticmethod
                def run(argv, **kwargs):
                    recorded["argv"] = list(argv)
                    recorded["timeout"] = kwargs.get("timeout")
                    return FakeProc()

            # Seam: replace the module-level `subprocess` binding of this
            # freshly loaded module instance only; the real module object
            # used by the rest of the suite is untouched.
            mod.subprocess = FakeSubprocess

            runner = object.__new__(mod.Runner)
            runner.bin = Path("/fake/turbo-lean")
            runner.dirs = {"batteries": Path("/fake/batteries")}
            w = {"id": "wl", "repo": "batteries", "file": "A.lean", "decl": "d"}
            with tempfile.TemporaryDirectory(prefix="m1-timeout-") as td:
                tdp = Path(td)
                runner.run_check(w, tdp / "cache", tdp / "home", tdp / "staging",
                                 no_daemon=True)
            # Control: the argv half already resolves the global at call time.
            argv = recorded["argv"]
            self.assertEqual(argv[argv.index("--timeout") + 1], "123")
            # The property under test: the subprocess bound carries the
            # override, not the import-time 900.
            self.assertEqual(recorded["timeout"], 123)
        finally:
            if prev is None:
                os.environ.pop(key, None)
            else:
                os.environ[key] = prev


class BaselineSchema(unittest.TestCase):
    def test_validate_requires_provenance(self):
        mod = load_script()
        base = full_valid_baseline(mod)
        self.assertEqual(mod.validate_baseline(base), [])
        for key in ("host", "turbo_lean_commit", "trials", "settings", "created_utc"):
            broken = json.loads(json.dumps(base))
            broken.pop(key)
            self.assertTrue(mod.validate_baseline(broken), key)
        broken = json.loads(json.dumps(base))
        broken["settings"].pop("TURBO_LEAN_ALLOWED_CSIMP")
        self.assertTrue(mod.validate_baseline(broken))

    def test_validate_requires_all_workloads(self):
        mod = load_script()
        base = full_valid_baseline(mod)
        base["workloads"].pop("pfr_more_ruzsa_dist")
        self.assertTrue(mod.validate_baseline(base))
        base2 = full_valid_baseline(mod)
        base2["workloads"].pop("batteries_unionfind_top")
        self.assertTrue(mod.validate_baseline(base2))

    def test_turbo_lean_dirty_marker_must_be_present_and_exactly_boolean_false(self):
        """DeepSeek review: `is True` accepts missing key, null, "true", numbers."""
        mod = load_script()
        base = full_valid_baseline(mod)
        self.assertEqual(mod.validate_baseline(base), [])  # control: valid false

        missing = json.loads(json.dumps(base))
        missing.pop("turbo_lean_dirty")
        errs = mod.validate_baseline(missing)
        self.assertTrue(any(e.startswith("baseline_missing_turbo_lean_dirty")
                            for e in errs), errs)

        for bad in (None, "true", "false", "True", 1, 0, 1.0, ["false"], {"dirty": False}):
            broken = json.loads(json.dumps(base))
            broken["turbo_lean_dirty"] = bad
            errs = mod.validate_baseline(broken)
            self.assertTrue(any(e.startswith("baseline_invalid_turbo_lean_dirty")
                                for e in errs), (bad, errs))

        dirty = json.loads(json.dumps(base))
        dirty["turbo_lean_dirty"] = True
        errs = mod.validate_baseline(dirty)
        self.assertTrue(any("baseline_dirty_tree" in e for e in errs), errs)


class Comparison(unittest.TestCase):
    def setUp(self):
        self.mod = load_script()

    def _baseline(self):
        mod = self.mod
        base = sample_baseline(mod)
        for wid, ms in (("batteries_list_lemmas_top", 1000.0),
                        ("batteries_string_lemmas_top", 5000.0)):
            fill_workload(mod, base, wid, ms)
        for wid in ("batteries_rbtree_lemmas_top", "batteries_rbtree_lemmas_mid",
                    "batteries_unionfind_top"):
            fill_workload(mod, base, wid, 1000.0)
        base["workloads"]["pfr_more_ruzsa_dist"] = mod.blocked_workload_result(
            exit_code=1, error_class="import_refresh_fail_closed", median_ms=6000.0)
        return base

    def _results(self, scale=1.0, host="bench-host", pfr_exit=1):
        mod = self.mod
        sb = sample_baseline(mod)
        res = mod.empty_run_result(mod.WORKLOADS, trials=5)
        res["host"] = dict(sb["host"], hostname=host)
        res["settings"] = sb["settings"]
        res["turbo_lean_commit"] = sb["turbo_lean_commit"]
        res["turbo_lean_dirty"] = sb["turbo_lean_dirty"]
        res["turbo_lean_binary"] = dict(sb["turbo_lean_binary"])
        res["workload_revs"] = dict(sb["workload_revs"])
        res["toolchain"] = dict(sb["toolchain"])
        for wid, ms in (("batteries_list_lemmas_top", 1000.0),
                        ("batteries_string_lemmas_top", 5000.0),
                        ("batteries_rbtree_lemmas_top", 1000.0),
                        ("batteries_rbtree_lemmas_mid", 1000.0),
                        ("batteries_unionfind_top", 1000.0)):
            fill_workload(mod, res, wid, ms * scale)
        res["workloads"]["pfr_more_ruzsa_dist"] = mod.blocked_workload_result(
            exit_code=pfr_exit, error_class=None if pfr_exit == 0 else "import_refresh_fail_closed",
            median_ms=6000.0)
        return res

    def test_identical_results_pass(self):
        verdict = self.mod.compare_run(self._baseline(), self._results())
        self.assertEqual(verdict["verdict"], "pass")
        self.assertEqual(verdict["regressions"], [])

    def test_regression_detected(self):
        verdict = self.mod.compare_run(self._baseline(), self._results(scale=1.5))
        self.assertEqual(verdict["verdict"], "regression")
        self.assertTrue(any(r.startswith("batteries_list_lemmas_top/")
                            for r in verdict["regressions"]))

    def test_noisy_workload_within_spread_gate_passes(self):
        # Baseline spread 20% on this workload: a 1.3x median is noise, not a
        # regression; a workload with tight spread at the same scale fails.
        base = self._baseline()
        fill_workload(self.mod, base, "batteries_list_lemmas_top", 1000.0, rel_spread=0.20)
        res = self._results()
        fill_workload(self.mod, res, "batteries_list_lemmas_top", 1300.0)
        verdict = self.mod.compare_run(base, res)
        self.assertEqual(verdict["verdict"], "pass")
        tight = self._baseline()
        verdict2 = self.mod.compare_run(tight, res)
        self.assertEqual(verdict2["verdict"], "regression")

    def test_host_mismatch_is_skipped_never_pass(self):
        # A different machine differs in FINGERPRINT: a changed hostname with
        # the same fingerprint and label is the same machine relabeled, which
        # compares (fingerprint-first identity). So the mismatch fixture
        # changes the fingerprint too, modeling a real other machine.
        res = self._results(host="other-runner")
        res["host"]["host_fingerprint"] = "d" * 64
        verdict = self.mod.compare_run(self._baseline(), res)
        self.assertEqual(verdict["verdict"], "comparison_skipped_host_mismatch")
        self.assertNotEqual(verdict["verdict"], "pass")

    def test_missing_baseline_is_not_compared(self):
        verdict = self.mod.compare_run(None, self._results())
        self.assertEqual(verdict["verdict"], "not_compared")

    def test_empty_trials_cannot_pass(self):
        res = self._results()
        res["workloads"]["batteries_list_lemmas_top"]["modes"]["cold_no_daemon"]["trials"] = 0
        res["workloads"]["batteries_list_lemmas_top"]["modes"]["cold_no_daemon"]["median_ms"] = None
        verdict = self.mod.compare_run(self._baseline(), res)
        self.assertEqual(verdict["verdict"], "regression")

    def test_pfr_passing_is_stale_expectation(self):
        verdict = self.mod.compare_run(self._baseline(), self._results(pfr_exit=0))
        self.assertEqual(verdict["verdict"], "stale_expectation")
        self.assertIn("pfr_more_ruzsa_dist", verdict["unexpected_successes"])

    def test_pfr_still_blocked_reports_honestly(self):
        verdict = self.mod.compare_run(self._baseline(), self._results())
        self.assertEqual(verdict["pfr_status"], "blocked_as_expected")


class EditedProof(unittest.TestCase):
    def test_inserted_have_forces_cas_miss(self):
        mod = load_script()
        src = (
            "theorem foo {xs : List α} (h : i + 1 = xs.length) :\n"
            "    xs.dropLast = List.eraseIdx xs i := by\n"
            "  ext\n"
            "  grind\n"
        )
        edited = mod.insert_bench_have(src, 7)
        self.assertIn("have _m1_bench_trial_7 : True := trivial", edited)
        # Statement byte-identical; only the proof body gained a line.
        self.assertEqual(edited.split(":= by")[0], src.split(":= by")[0])
        # Insertion is idempotent per trial index and restores cleanly.
        self.assertEqual(mod.remove_bench_have(edited), src)

    def test_term_style_proof_wrapping(self):
        mod = load_script()
        src = ("theorem parentD_eq {arr : Array UFNode} {i} (h) :\n"
               "    parentD arr i = arr[i].parent := dite_eq_left _\n")
        edited = mod.insert_bench_have(src, 3)
        self.assertIn(":= (have _m1_bench_trial_3 : True := trivial; dite_eq_left _)", edited)
        self.assertEqual(mod.remove_bench_have(edited), src)

    def test_term_style_multiline_proof(self):
        mod = load_script()
        src = ("theorem foo :\n"
               "    True :=\n"
               "  trivial\n")
        edited = mod.insert_bench_have(src, 1)
        self.assertIn("(have _m1_bench_trial_1 : True := trivial; trivial)", edited)
        # Whitespace may be normalized; statement and proof term must not change.
        norm = lambda s: " ".join(s.split())
        self.assertEqual(norm(mod.remove_bench_have(edited)), norm(src))


class CasReplay(unittest.TestCase):
    """G2a (roadmap/HORIZONS.md): CAS replay hit rate on recorded edit sequences."""

    def test_mode_result_counts_hits_and_misses_from_statuses(self):
        mod = load_script()
        m = mod.mode_result([100.0, 110.0, 120.0], [0.99] * 3,
                            ["theorem_cache_hit", "theorem_cache_hit", "theorem_verified"],
                            replay_mode=True)
        self.assertEqual(m["cas_replay"],
                         {"hits": 2, "misses": 1, "hit_rate": 0.6667})

    def test_mode_result_fission_sums_tolerate_missing_fields(self):
        mod = load_script()
        m = mod.mode_result([100.0, 100.0], [0.99, 0.99],
                            ["theorem_verified", "theorem_verified"],
                            fission_dicts=[{"fission_cached_subshards": 3,
                                            "fission_verified_subshards": None},
                                           {}],
                            replay_mode=True)
        self.assertEqual(m["cas_replay"]["fission_cached_subshards"], 3)
        # Never reported in any trial: None, not 0 ("the tool never emits this"
        # must stay distinguishable from "the tool reported zero").
        self.assertIsNone(m["cas_replay"]["fission_verified_subshards"])
        self.assertEqual(m["cas_replay"]["hits"], 0)
        self.assertEqual(m["cas_replay"]["misses"], 2)

    def test_mode_result_without_theorem_statuses_has_no_replay(self):
        mod = load_script()
        m = mod.mode_result([100.0], [], ["exit_1"], replay_mode=True)
        self.assertNotIn("cas_replay", m)

    def test_summary_separates_unedited_and_edited_conditions(self):
        mod = load_script()
        res = {"trials": 2, "workloads": {
            "w1": {"expected_status": "active", "modes": {
                "cold_no_daemon": {"cas_replay": {"hits": 0, "misses": 2,
                                                  "hit_rate": 0.0}},
                "warm_cache_hit_daemon": {"cas_replay": {"hits": 2, "misses": 0,
                                                         "hit_rate": 1.0}},
                "warm_edited_proof_daemon": {"cas_replay": {"hits": 0, "misses": 2,
                                                            "hit_rate": 0.0}}}},
            "pfr": {"expected_status": "blocked",
                    "modes": {"cold_no_daemon": {}}},
        }}
        rep = mod.summarize_cas_replay(res)
        self.assertEqual(rep["unedited_recheck"]["hits"], 2)
        self.assertEqual(rep["unedited_recheck"]["hit_rate"], 1.0)
        self.assertEqual(rep["edited_recheck"]["misses"], 2)
        self.assertEqual(rep["edited_recheck"]["hit_rate"], 0.0)
        self.assertEqual(rep["overall"]["classified_calls"], 4)
        self.assertEqual(rep["overall"]["hit_rate"], 0.5)
        self.assertEqual(rep["overall"]["failed_trials"], 0)
        # The cold mode and blocked workloads are outside the recorded sequence.
        self.assertEqual(rep["overall"]["workloads"], ["w1"])
        self.assertEqual(rep["non_ok_workloads"], [])
        self.assertIn("2 unedited warm re-checks", rep["sequence"])

    def test_summary_with_no_measured_warm_modes_is_empty_not_wrong(self):
        mod = load_script()
        rep = mod.summarize_cas_replay({"trials": 2, "workloads": {}})
        self.assertEqual(rep["overall"]["classified_calls"], 0)
        self.assertIsNone(rep["overall"]["hit_rate"])

    def test_end_to_end_records_cas_replay(self):
        with tempfile.TemporaryDirectory(prefix="m1-replay-") as td:
            r = run_bench(Path(td), ["--no-baseline", "--out", str(Path(td) / "o.json")])
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            data = json.loads((Path(td) / "o.json").read_text())
            rep = data["cas_replay"]
            # 5 active workloads x trials=2: every unedited warm re-check hits
            # the CAS; every edited re-check misses (the inserted `have`
            # changes the proof, so the shard key no longer matches).
            un, ed, ov = (rep["unedited_recheck"], rep["edited_recheck"],
                          rep["overall"])
            self.assertEqual((un["hits"], un["misses"], un["hit_rate"]),
                             (10, 0, 1.0), un)
            self.assertEqual((ed["hits"], ed["misses"], ed["hit_rate"]),
                             (0, 10, 0.0), ed)
            self.assertEqual((ov["classified_calls"], ov["hit_rate"]), (20, 0.5), ov)
            self.assertEqual(len(ov["workloads"]), 5, ov)
            self.assertIn("G2A CAS REPLAY:", r.stdout)
            modes = data["workloads"]["batteries_list_lemmas_top"]["modes"]
            self.assertEqual(modes["warm_cache_hit_daemon"]["cas_replay"]["hit_rate"], 1.0)
            self.assertEqual(modes["warm_edited_proof_daemon"]["cas_replay"]["hit_rate"], 0.0)
            # Cold runs have no CAS to hit; they are outside the replay sequence.
            self.assertNotIn("cas_replay", modes["cold_no_daemon"])


class BaselineStrictness(unittest.TestCase):
    """Group 1: a named baseline is an obligation; skipped is never a pass."""

    def test_missing_named_baseline_is_error(self):
        with tempfile.TemporaryDirectory(prefix="m1-strict-") as td:
            r = run_bench(Path(td), ["--baseline", str(Path(td) / "nope.json"),
                                     "--out", str(Path(td) / "o.json")])
            self.assertNotEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("cannot load baseline", r.stderr)

    def test_malformed_baseline_is_error(self):
        with tempfile.TemporaryDirectory(prefix="m1-strict-") as td:
            bad = Path(td) / "bad.json"
            bad.write_text("{not json at all")
            r = run_bench(Path(td), ["--baseline", str(bad), "--out", str(Path(td) / "o.json")])
            self.assertNotEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("cannot load baseline", r.stderr)

    def test_baseline_missing_workload_is_error(self):
        mod = load_script()
        with tempfile.TemporaryDirectory(prefix="m1-strict-") as td:
            base = full_valid_baseline(mod)
            base["workloads"].pop("batteries_unionfind_top")
            p = Path(td) / "b.json"
            p.write_text(json.dumps(base))
            r = run_bench(Path(td), ["--baseline", str(p), "--out", str(Path(td) / "o.json")])
            self.assertNotEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("batteries_unionfind_top", r.stderr)

    def test_baseline_missing_mode_is_error(self):
        mod = load_script()
        with tempfile.TemporaryDirectory(prefix="m1-strict-") as td:
            base = full_valid_baseline(mod)
            del base["workloads"]["batteries_list_lemmas_top"]["modes"]["warm_edited_proof_daemon"]
            p = Path(td) / "b.json"
            p.write_text(json.dumps(base))
            r = run_bench(Path(td), ["--baseline", str(p), "--out", str(Path(td) / "o.json")])
            self.assertNotEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("warm_edited_proof_daemon", r.stderr)

    def test_baseline_nan_median_is_error(self):
        mod = load_script()
        with tempfile.TemporaryDirectory(prefix="m1-strict-") as td:
            base = full_valid_baseline(mod)
            base["workloads"]["batteries_list_lemmas_top"]["modes"]["cold_no_daemon"]["median_ms"] = float("nan")
            p = Path(td) / "b.json"
            p.write_text(json.dumps(base))  # json.dumps writes NaN, json.loads reads it back
            r = run_bench(Path(td), ["--baseline", str(p), "--out", str(Path(td) / "o.json")])
            self.assertNotEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("median_ms", r.stderr)

    def test_baseline_nonpositive_median_is_error(self):
        mod = load_script()
        for bad in (0.0, -5.0):
            with tempfile.TemporaryDirectory(prefix="m1-strict-") as td:
                base = full_valid_baseline(mod)
                base["workloads"]["batteries_list_lemmas_top"]["modes"]["cold_no_daemon"]["median_ms"] = bad
                p = Path(td) / "b.json"
                p.write_text(json.dumps(base))
                r = run_bench(Path(td), ["--baseline", str(p), "--out", str(Path(td) / "o.json")])
                self.assertNotEqual(r.returncode, 0, r.stdout + r.stderr)

    def test_baseline_nonpositive_trials_is_error(self):
        mod = load_script()
        with tempfile.TemporaryDirectory(prefix="m1-strict-") as td:
            base = full_valid_baseline(mod)
            base["workloads"]["batteries_list_lemmas_top"]["modes"]["cold_no_daemon"]["trials"] = -3
            p = Path(td) / "b.json"
            p.write_text(json.dumps(base))
            r = run_bench(Path(td), ["--baseline", str(p), "--out", str(Path(td) / "o.json")])
            self.assertNotEqual(r.returncode, 0, r.stdout + r.stderr)

    def test_strict_comparison_makes_not_compared_nonzero(self):
        with tempfile.TemporaryDirectory(prefix="m1-strict-") as td:
            r = run_bench(Path(td), ["--no-baseline", "--strict-comparison",
                                     "--out", str(Path(td) / "o.json")])
            self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
            self.assertIn("not_compared", r.stdout)

    def test_strict_comparison_makes_host_mismatch_nonzero(self):
        mod = load_script()
        with tempfile.TemporaryDirectory(prefix="m1-strict-") as td:
            r0 = run_bench(Path(td), ["--no-baseline", "--out", str(Path(td) / "o0.json")])
            self.assertEqual(r0.returncode, 0, r0.stdout + r0.stderr)
            o0 = json.loads((Path(td) / "o0.json").read_text())
            base = full_valid_baseline(mod)
            base["workload_revs"] = dict(o0["workload_revs"])
            base["toolchain"] = dict(o0["toolchain"])
            base["host"]["hostname"] = "some-other-box"
            p = Path(td) / "b.json"
            p.write_text(json.dumps(base))
            r = run_bench(Path(td), ["--baseline", str(p), "--strict-comparison",
                                     "--out", str(Path(td) / "o.json")])
            self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
            self.assertIn("comparison_skipped_host_mismatch", r.stdout)

    def test_nonpositive_trials_is_usage_error(self):
        mod = load_script()
        with tempfile.TemporaryDirectory(prefix="m1-strict-") as td:
            with self.assertRaises(SystemExit) as cm:
                mod.main(["--turbo-lean-bin", "x", "--batteries-dir", "b",
                          "--pfr-dir", "p", "--trials", "0"])
            self.assertEqual(cm.exception.code, 2)

    def test_workload_on_one_side_only_is_named_error(self):
        mod = load_script()
        base = full_valid_baseline(mod)
        res = mod.empty_run_result(mod.WORKLOADS, trials=5)
        res["host"] = dict(base["host"])
        res["settings"] = dict(base["settings"])
        res["turbo_lean_commit"] = base["turbo_lean_commit"]
        res["workloads"].pop("batteries_string_lemmas_top")  # results side lost a workload
        for w in mod.WORKLOADS:
            if w["id"] == "batteries_string_lemmas_top":
                continue
            if w["expected_status"] == "blocked":
                res["workloads"][w["id"]] = mod.blocked_workload_result(1, "x", 6000.0)
            else:
                fill_workload(mod, res, w["id"], 1000.0)
        verdict = mod.compare_run(base, res)
        self.assertEqual(verdict["verdict"], "measurement_failed")
        self.assertTrue(any("batteries_string_lemmas_top" in e and "results" in e
                            for e in verdict["comparison_errors"]),
                        verdict["comparison_errors"])

    def test_baseline_workload_missing_from_results_is_named_error(self):
        mod = load_script()
        base = full_valid_baseline(mod)
        res = mod.empty_run_result(mod.WORKLOADS, trials=5)
        res["host"] = dict(base["host"])
        res["settings"] = dict(base["settings"])
        res["turbo_lean_commit"] = base["turbo_lean_commit"]
        res["workloads"] = {k: v for k, v in res["workloads"].items()
                            if k != "pfr_more_ruzsa_dist"}
        for w in mod.WORKLOADS:
            if w["expected_status"] != "blocked":
                fill_workload(mod, res, w["id"], 1000.0)
        verdict = mod.compare_run(base, res)
        self.assertEqual(verdict["verdict"], "measurement_failed")
        self.assertTrue(any("pfr_more_ruzsa_dist" in e for e in verdict["comparison_errors"]),
                        verdict["comparison_errors"])

    def test_settings_mismatch_on_fifth_var(self):
        mod = load_script()
        base = full_valid_baseline(mod)
        res = mod_results_like(mod, base, 1000.0)
        res["settings"]["TURBO_LEAN_HOME"] = "/somewhere/else"
        verdict = mod.compare_run(base, res)
        self.assertEqual(verdict["verdict"], "comparison_skipped_settings_mismatch")

    def test_failed_cold_trials_are_not_measured(self):
        body = (
            "#!/usr/bin/env python3\n"
            "import json, os, sys, time\n"
            "args = sys.argv[1:]\n"
            "time.sleep(0.04)\n"
            "if '--no-auto-worktree-link' in args:\n"
            "    print(json.dumps({'error': 'stale imports: import_refresh fail-closed'}))\n"
            "    sys.exit(1)\n"
            "if os.environ.get('TURBO_LEAN_NO_DAEMON') and 'warm' not in ' '.join(args):\n"
            "    sys.stderr.write('boom'); sys.exit(1)\n"   # every cold trial fails
            "out = {'status': 'theorem_cache_hit', 'decl': 'd', 'elapsed_ms': 40,\n"
            "       'phase_timings': {'wall_ms': 200.0, 'phase_sum_ms': 199.0,\n"
            "                         'phase_covered_ms': 59.0, 'phase_overlap_ms': 0.0,\n"
            "                         'coverage_ratio': 0.99,\n"
            "                         'phases_ms': {'setup': 10.0, 'elaboration': 49.0}}}\n"
            "print(json.dumps(out)); sys.exit(0)\n")
        with tempfile.TemporaryDirectory(prefix="m1-fail-") as td:
            r = run_bench(Path(td), ["--no-baseline", "--out", str(Path(td) / "o.json")],
                          stub_body=body)
            self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
            self.assertIn("measurement_failed", r.stdout)
            data = json.loads((Path(td) / "o.json").read_text())
            cold = data["workloads"]["batteries_list_lemmas_top"]["modes"]["cold_no_daemon"]
            self.assertEqual(cold["trials"], 0, cold)          # failed runs measured nothing
            self.assertEqual(cold["failed_trials"], 2, cold)   # and are counted as failures

    def test_coverage_is_external_not_self_reported(self):
        # Tool claims coverage 0.99, but its internal wall (10 ms) covers only a
        # fraction of the externally measured wall (~45 ms): must fail.
        body = (
            "#!/usr/bin/env python3\n"
            "import json, os, sys, time\n"
            "args = sys.argv[1:]\n"
            "time.sleep(0.04)\n"
            "if '--no-auto-worktree-link' in args:\n"
            "    print(json.dumps({'error': 'stale imports: import_refresh fail-closed'}))\n"
            "    sys.exit(1)\n"
            "out = {'status': 'theorem_cache_hit', 'decl': 'd', 'elapsed_ms': 10,\n"
            "       'phase_timings': {'wall_ms': 10.0, 'phase_sum_ms': 9.0,\n"
            "                         'phase_covered_ms': 9.0, 'phase_overlap_ms': 0.0,\n"
            "                         'coverage_ratio': 0.99,\n"
            "                         'phases_ms': {'setup': 5.0, 'elaboration': 4.0}}}\n"
            "print(json.dumps(out)); sys.exit(0)\n")
        with tempfile.TemporaryDirectory(prefix="m1-cov-") as td:
            r = run_bench(Path(td), ["--no-baseline", "--out", str(Path(td) / "o.json")],
                          stub_body=body)
            self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
            self.assertIn("measurement_failed", r.stdout)
            data = json.loads((Path(td) / "o.json").read_text())
            cold = data["workloads"]["batteries_list_lemmas_top"]["modes"]["cold_no_daemon"]
            self.assertLess(cold["coverage_ratio_external_min"], 0.90, cold)


class ImprovementSide(unittest.TestCase):
    """Group 2: every cell reports baseline, new, delta, band, and a word."""

    def setUp(self):
        self.mod = load_script()
        self.base = full_valid_baseline(self.mod)
        self.res = mod_results_like(self.mod, self.base, 1000.0)

    def _gates(self, scale):
        res = mod_results_like(self.mod, self.base, 1000.0 * scale)
        v = self.mod.compare_run(self.base, res)
        return v, {k: g for k, g in v["gates"].items()
                   if g.get("baseline_median_ms") is not None}

    def test_identical_cells_are_unchanged_and_pass(self):
        v, gates = self._gates(1.0)
        self.assertEqual(v["verdict"], "pass")
        self.assertEqual(len(gates), 15)
        for k, g in gates.items():
            self.assertEqual(g["verdict"], "unchanged", k)
            for field in ("baseline_median_ms", "new_median_ms", "delta_ms",
                          "delta_pct", "noise_band_ms"):
                self.assertIn(field, g, (k, field))

    def test_improvement_classified_with_symmetric_band(self):
        # Baseline 1000 ms, no spread, warm floor 10%: tolerance 1125 ms, so the
        # symmetric band is 125 ms -> improved means strictly below 875 ms.
        base = full_valid_baseline(self.mod)
        v1 = self.mod.compare_run(base, mod_results_like(self.mod, base, 880.0))
        g1 = v1["gates"]["batteries_list_lemmas_top/warm_cache_hit_daemon"]
        self.assertEqual(g1["verdict"], "unchanged", g1)
        v2 = self.mod.compare_run(base, mod_results_like(self.mod, base, 870.0))
        g2 = v2["gates"]["batteries_list_lemmas_top/warm_cache_hit_daemon"]
        self.assertEqual(g2["verdict"], "improved", g2)
        self.assertEqual(v2["verdict"], "pass")  # an improvement never fails the run
        self.assertIn("batteries_list_lemmas_top/warm_cache_hit_daemon", v2["improvements"])

    def test_regression_classification_carries_delta(self):
        v, gates = self._gates(1.5)
        self.assertEqual(v["verdict"], "regression")
        for k, g in gates.items():
            self.assertEqual(g["verdict"], "regressed", k)
            self.assertGreater(g["delta_ms"], 0, k)
            self.assertGreater(g["delta_pct"], 0, k)

    def test_summary_line_counts_all_three_words(self):
        v, gates = self._gates(1.0)
        self.assertIn("15 cells: 0 regressed, 0 improved, 15 unchanged", v["summary"])
        v2, _ = self._gates(0.5)
        self.assertIn("15 regressed, 0 improved, 0 unchanged", v2["summary"]) \
            if False else self.assertIn("0 regressed, 15 improved, 0 unchanged", v2["summary"])

    def test_per_cell_lines_and_summary_are_printed(self):
        with tempfile.TemporaryDirectory(prefix="m1-imp-") as td:
            # Baseline provenance (host + recorded settings + revs + toolchain)
            # must match this run, so derive them from a first --no-baseline run.
            r0 = run_bench(Path(td), ["--no-baseline", "--out", str(Path(td) / "o0.json")])
            self.assertEqual(r0.returncode, 0, r0.stdout + r0.stderr)
            o0 = json.loads((Path(td) / "o0.json").read_text())
            base = full_valid_baseline(self.mod)
            # Same host AND same condition: sync the whole host block (label
            # and fingerprint included) — a labeled baseline no longer matches
            # an unlabeled run on the same machine.
            base["host"] = dict(o0["host"])
            base["settings"] = dict(o0["settings"])
            base["workload_revs"] = dict(o0.get("workload_revs") or base["workload_revs"])
            base["toolchain"] = dict(o0.get("toolchain") or base["toolchain"])
            bp = Path(td) / "b.json"
            bp.write_text(json.dumps(base))
            r = run_bench(Path(td), ["--baseline", str(bp), "--out", str(Path(td) / "o.json")])
            self.assertIn("-> ", r.stdout)
            self.assertIn("band ±", r.stdout)
            self.assertIn("SUMMARY: bench_check_loop:", r.stdout)
            self.assertRegex(r.stdout, r"\d+ cells: \d+ regressed, \d+ improved, \d+ unchanged")


def mod_results_like(mod, base, median_ms):
    res = mod.empty_run_result(mod.WORKLOADS, trials=5)
    res["host"] = dict(base["host"])
    res["settings"] = dict(base["settings"])
    res["turbo_lean_commit"] = base["turbo_lean_commit"]
    res["turbo_lean_dirty"] = base.get("turbo_lean_dirty")
    res["turbo_lean_binary"] = dict(base.get("turbo_lean_binary") or {})
    res["workload_revs"] = dict(base.get("workload_revs") or {})
    res["toolchain"] = dict(base.get("toolchain") or {})
    for w in mod.WORKLOADS:
        if w["expected_status"] == "blocked":
            res["workloads"][w["id"]] = mod.blocked_workload_result(
                1, "stale_import_refresh_fail_closed", 6000.0)
        else:
            fill_workload(mod, res, w["id"], median_ms)
    return res


class PfrAndSourceSafety(unittest.TestCase):
    """Group 3: PFR probes are checked individually; the checkout is sacred."""

    PFR_STUB = (
        "#!/usr/bin/env python3\n"
        "import json, os, sys, time\n"
        "args = sys.argv[1:]\n"
        "time.sleep(0.04)\n"
        "cnt_file = os.environ.get('FAKE_COUNTER_FILE')\n"
        "n = 0\n"
        "if cnt_file and '--no-auto-worktree-link' in args:\n"
        "    try: n = int(open(cnt_file).read() or 0)\n"
        "    except OSError: n = 0\n"
        "    open(cnt_file, 'w').write(str(n + 1))\n"
        "if os.environ.get('FAKE_OLEAN_SWAP') and '--no-auto-worktree-link' in args:\n"
        "    pd = args[args.index('--project-dir') + 1]\n"
        "    pkg = os.path.join(pd, '.lake', 'packages')\n"
        "    os.makedirs(pkg, exist_ok=True)\n"
        "    a = os.path.join(pkg, 'A.olean')\n"
        "    if os.path.exists(a):\n"
        "        os.remove(a)\n"
        "    open(os.path.join(pkg, 'B.olean'), 'w').write('x')\n"
        "if '--no-auto-worktree-link' in args:\n"
        "    mode = os.environ.get('FAKE_PFR_MODE', 'fail')\n"
         "    if mode == 'pass' or (mode == 'pass_first' and n == 0):\n"
         "        print(json.dumps({'status': 'theorem_verified', 'decl': 'd',\n"
         "                          'elapsed_ms': 40, 'phase_timings': {\n"
         "                          'wall_ms': 200.0, 'coverage_ratio': 0.99,\n"
         "                          'phases_ms': {}}})); sys.exit(0)\n"
         "    if mode == 'unexpected' or (mode == 'unexpected_second' and n == 1):\n"
         "        print(json.dumps({'error': 'Error: Declaration `typo` not found in PFR/MoreRuzsaDist.lean'}))\n"
         "        sys.exit(1)\n"
         "    if mode == 'id_unconfirmed':\n"
         "        sys.stderr.write(\"Error: Cannot report a verdict: declaration identity unconfirmed for `rdist_of_neg_le`\\nerror: unknown module prefix 'PFR'\\n\")\n"
         "        sys.exit(1)\n"
         "    if mode == 'stale_lock' or (mode == 'stale_lock_second' and n >= 1):\n"
         "        print(json.dumps({'error': 'Error: build lock is stale, retry later'}))\n"
         "        sys.exit(1)\n"
         "    if mode == 'stale_text':\n"
         "        print(json.dumps({'error': 'Error: shm cache entry is stale, retry later'}))\n"
         "        sys.exit(1)\n"
         "    print(json.dumps({'error': 'stale imports: import_refresh fail-closed'}))\n"

        "    sys.exit(1)\n"
        "status = 'theorem_cache_hit'\n"
        "if not os.environ.get('TURBO_LEAN_NO_DAEMON'):\n"
        "    try:\n"
        "        body = open(args[-1]).read()\n"
        "        status = ('theorem_verified' if '_m1_bench_trial_' in body\n"
        "                  else 'theorem_cache_hit')\n"
        "    except OSError:\n"
        "        pass\n"
        "out = {'status': status, 'decl': 'd', 'elapsed_ms': 50,\n"
        "       'phase_timings': {'wall_ms': 200.0, 'phase_sum_ms': 199.0,\n"
        "                         'phase_covered_ms': 199.0, 'phase_overlap_ms': 0.0,\n"
        "                         'coverage_ratio': 0.99,\n"
        "                         'phases_ms': {'setup': 10.0, 'elaboration': 189.0}}}\n"
        "print(json.dumps(out)); sys.exit(0)\n")

    def _run(self, td, extra, env_extra=None, stub_body=None, make_projects=True):
        return run_bench(Path(td), extra + ["--out", str(Path(td) / "o.json")],
                         stub_body=stub_body or self.PFR_STUB, env_extra=env_extra,
                         make_projects=make_projects)

    def test_pfr_unexpected_success_is_stale_even_without_baseline(self):
        with tempfile.TemporaryDirectory(prefix="m1-pfr-") as td:
            r = self._run(td, ["--no-baseline"], env_extra={"FAKE_PFR_MODE": "pass"})
            self.assertEqual(r.returncode, 3, r.stdout + r.stderr)
            self.assertIn("stale_expectation", r.stdout)

    def test_pfr_error_classes_are_specific_and_unexpected_failure_is_rejected(self):
        mod = load_script()
        pfr = [w for w in mod.WORKLOADS if w["id"] == "pfr_more_ruzsa_dist"][0]
        self.assertIn("expected_error_classes", pfr)
        self.assertIn("declaration_identity_unknown_module_prefix", pfr["expected_error_classes"])
        self.assertIn("stale_import_refresh_fail_closed", pfr["expected_error_classes"])
        self.assertEqual(
            mod.classify_error(1, None,
                               "Error: Cannot report a verdict: declaration identity unconfirmed for `rdist_of_neg_le`\n"
                               "error: unknown module prefix 'PFR'"),
            "declaration_identity_unknown_module_prefix")
        self.assertEqual(
            mod.classify_error(1, None,
                               "Error: Worktree opt-out prevents refreshing stale imports: Mathlib.Data.Fin.Basic"),
            "stale_import_refresh_fail_closed")
        self.assertEqual(mod.classify_error(1, None, "Error: Declaration `typo` not found in file"),
                         "declaration_not_found")
        self.assertEqual(mod.classify_error(1, None, "Error: Failed to read x: No such file or directory"),
                         "source_file_not_found")
        self.assertEqual(mod.classify_error(1, None, "Error: unrelated failure"), "exit_1")

    def test_pfr_unexpected_failure_is_named_and_nonzero(self):
        with tempfile.TemporaryDirectory(prefix="m1-pfr-unexpected-") as td:
            r = self._run(td, ["--no-baseline"], env_extra={"FAKE_PFR_MODE": "unexpected"})
            self.assertNotEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertNotEqual(r.returncode, 3, r.stdout + r.stderr)
            combined = r.stdout + r.stderr
            self.assertIn("blocked_workload_unexpected_failure", combined)
            self.assertIn("declaration_not_found", combined)

    def test_pfr_expected_failure_is_blocked_as_expected(self):
        for mode in ("fail", "id_unconfirmed"):
            with tempfile.TemporaryDirectory(prefix="m1-pfr-expected-") as td:
                r = self._run(td, ["--no-baseline"], env_extra={"FAKE_PFR_MODE": mode})
                self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
                data = json.loads((Path(td) / "o.json").read_text())
                pfr = data["workloads"]["pfr_more_ruzsa_dist"]
                self.assertEqual(pfr["status"], "blocked_as_expected")
                expected_cls = ("stale_import_refresh_fail_closed" if mode == "fail"
                                else "declaration_identity_unknown_module_prefix")
                self.assertEqual(pfr["error_class"], expected_cls)

    def test_pfr_mixed_expected_and_unexpected_probe_failure_is_rejected(self):
        with tempfile.TemporaryDirectory(prefix="m1-pfr-mixed-") as td:
            r = self._run(td, ["--no-baseline"],
                          env_extra={"FAKE_PFR_MODE": "unexpected_second",
                                     "FAKE_COUNTER_FILE": str(Path(td) / "cnt")})
            self.assertEqual(r.returncode, 4, r.stdout + r.stderr)
            self.assertIn("blocked_workload_unexpected_failure", r.stdout + r.stderr)
            self.assertIn("declaration_not_found", r.stdout + r.stderr)

    def test_generic_stale_lock_failure_is_not_import_refresh_class(self):
        """DeepSeek2670: 'build lock is stale' matched the broad bare-'stale' rule."""
        mod = load_script()
        self.assertEqual(
            mod.classify_error(1, None, "Error: build lock is stale, retry later"),
            "exit_1")

    def test_unrelated_stale_text_is_not_import_refresh_class(self):
        mod = load_script()
        self.assertEqual(
            mod.classify_error(1, None, "Error: shm cache entry is stale, retry later"),
            "exit_1")

    def test_genuine_import_refresh_shapes_keep_expected_class(self):
        mod = load_script()
        self.assertEqual(
            mod.classify_error(1, None, "stale imports: import_refresh fail-closed"),
            "stale_import_refresh_fail_closed")
        self.assertEqual(
            mod.classify_error(1, None, "Error: Worktree opt-out prevents refreshing "
                                        "stale imports: Mathlib.Data.Fin.Basic"),
            "stale_import_refresh_fail_closed")

    def test_stale_lock_probe_is_unexpected_failure_not_blocked_as_expected(self):
        with tempfile.TemporaryDirectory(prefix="m1-pfr-lock-") as td:
            r = self._run(td, ["--no-baseline"], env_extra={"FAKE_PFR_MODE": "stale_lock"})
            self.assertEqual(r.returncode, 4, r.stdout + r.stderr)
            combined = r.stdout + r.stderr
            self.assertIn("blocked_workload_unexpected_failure", combined)
            data = json.loads((Path(td) / "o.json").read_text())
            pfr = data["workloads"]["pfr_more_ruzsa_dist"]
            self.assertEqual(pfr["status"], "blocked_unexpected_failure", pfr)
            self.assertEqual(pfr["error_class"], "exit_1", pfr)
            self.assertNotIn("stale_import_refresh_fail_closed",
                             pfr["probe_error_classes"], pfr)

    def test_unrelated_stale_text_probe_is_unexpected_failure(self):
        with tempfile.TemporaryDirectory(prefix="m1-pfr-staletext-") as td:
            r = self._run(td, ["--no-baseline"], env_extra={"FAKE_PFR_MODE": "stale_text"})
            self.assertEqual(r.returncode, 4, r.stdout + r.stderr)
            self.assertIn("blocked_workload_unexpected_failure", r.stdout + r.stderr)

    def test_mixed_genuine_and_stale_lock_probes_are_rejected(self):
        with tempfile.TemporaryDirectory(prefix="m1-pfr-mixed-lock-") as td:
            r = self._run(td, ["--no-baseline"],
                          env_extra={"FAKE_PFR_MODE": "stale_lock_second",
                                     "FAKE_COUNTER_FILE": str(Path(td) / "cnt")})
            self.assertEqual(r.returncode, 4, r.stdout + r.stderr)
            combined = r.stdout + r.stderr
            self.assertIn("blocked_workload_unexpected_failure", combined)
            data = json.loads((Path(td) / "o.json").read_text())
            pfr = data["workloads"]["pfr_more_ruzsa_dist"]
            self.assertEqual(pfr["status"], "blocked_unexpected_failure", pfr)

    def test_genuine_expected_probe_failure_still_blocked_as_expected(self):
        with tempfile.TemporaryDirectory(prefix="m1-pfr-genuine-") as td:
            r = self._run(td, ["--no-baseline"], env_extra={"FAKE_PFR_MODE": "fail"})
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            data = json.loads((Path(td) / "o.json").read_text())
            pfr = data["workloads"]["pfr_more_ruzsa_dist"]
            self.assertEqual(pfr["status"], "blocked_as_expected", pfr)
            self.assertEqual(pfr["error_class"], "stale_import_refresh_fail_closed", pfr)
            # successes: the active workloads still measure OK in the same run
            for wid in ("batteries_list_lemmas_top", "batteries_unionfind_top"):
                self.assertEqual(data["workloads"][wid]["status"], "ok", wid)

    def test_pfr_every_probe_exit_is_checked_not_just_the_last(self):
        with tempfile.TemporaryDirectory(prefix="m1-pfr-") as td:
            r = self._run(td, ["--no-baseline"],
                          env_extra={"FAKE_PFR_MODE": "pass_first",
                                     "FAKE_COUNTER_FILE": str(Path(td) / "cnt")})
            self.assertEqual(r.returncode, 3, r.stdout + r.stderr)
            data = json.loads((Path(td) / "o.json").read_text())
            pfr = data["workloads"]["pfr_more_ruzsa_dist"]
            self.assertEqual(pfr["status"], "unexpectedly_passing", pfr)
            self.assertIn(0, pfr["probe_exit_codes"], pfr)

    def test_olean_inventory_guard_catches_offsetting_change(self):
        with tempfile.TemporaryDirectory(prefix="m1-olean-") as td:
            # Pre-create one prebuilt dependency artifact; the stub replaces it
            # with another (same count, different path) during the PFR probe.
            pkg = Path(td) / "pfr" / ".lake" / "packages"
            pkg.mkdir(parents=True, exist_ok=True)
            (pkg / "A.olean").write_bytes(b"m")
            r = self._run(td, ["--no-baseline"], env_extra={"FAKE_OLEAN_SWAP": "1"})
            self.assertEqual(r.returncode, 4, r.stdout + r.stderr)
            self.assertIn("inventory", r.stderr)

    def test_olean_inventory_diff_reports_missing_and_extra(self):
        mod = load_script()
        missing, extra = mod.diff_olean_inventory({"a.olean", "b.olean"}, {"b.olean", "c.olean"})
        self.assertEqual(missing, {"a.olean"})
        self.assertEqual(extra, {"c.olean"})

    def test_dirty_checkout_is_refused(self):
        with tempfile.TemporaryDirectory(prefix="m1-dirty-") as td:
            run_bench(Path(td), ["--no-baseline"])  # materializes fake git projects
            (Path(td) / "batteries" / "Batteries" / "Data" / "List" / "Lemmas.lean").write_text(
                "theorem dropLast_eq_eraseIdx :\n    True := by\n  trivial\n-- leftover edit\n")
            r = self._run(td, ["--no-baseline"], make_projects=False)
            self.assertEqual(r.returncode, 4, r.stdout + r.stderr)
            self.assertIn("dirty", r.stderr)

    def test_sigterm_restores_edited_source(self):
        import signal as sig
        body = self.PFR_STUB.replace(
            "out = {'status': status",
            "if status == 'theorem_verified' and os.environ.get('FAKE_SLOW_EDIT'):\n"
            "    time.sleep(3.0)\n"
            "out = {'status': status")
        with tempfile.TemporaryDirectory(prefix="m1-term-") as td:
            # Materialize stub + fake projects with a first (fast) run.
            r0 = self._run(td, ["--no-baseline"], env_extra={"FAKE_SLOW_EDIT": "1"},
                           stub_body=body)
            src = Path(td) / "batteries" / "Batteries" / "Data" / "String" / "Lemmas.lean"
            original = src.read_text()
            proc = subprocess.Popen(
                BENCH_CMD + ["--turbo-lean-bin", str(Path(td) / "fake-turbo-lean"),
                 "--batteries-dir", str(Path(td) / "batteries"), "--pfr-dir", str(Path(td) / "pfr"),
                 "--trials", "1", "--warmup", "0", "--skip-rev-check", "--allow-busy-node",
                 "--no-baseline", "--out", str(Path(td) / "o2.json")],
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                env=dict(os.environ, TURBO_LEAN_GIT=str(Path(td) / "fake-git"),
                         PATH=str(Path(td) / "fake-bin") + os.pathsep + os.environ.get("PATH", ""),
                         TURBO_LEAN_ALLOWED_CSIMP="*", TURBO_LEAN_ALLOWED_UNSAFE="*",
                         TURBO_LEAN_ALLOWED_IMPLEMENTED_BY="*", FAKE_PFR_FAIL="1",
                         FAKE_SLOW_EDIT="1"))
            try:
                edited = False
                for _ in range(400):
                    if "_m1_bench_trial_" in src.read_text():
                        edited = True
                        break
                    if proc.poll() is not None:
                        break
                    time.sleep(0.05)
                self.assertTrue(edited, "source was never edited; cannot test SIGTERM restore")
                proc.send_signal(sig.SIGTERM)
                rc = proc.wait(timeout=60)
            finally:
                if proc.poll() is None:
                    proc.kill()
                    proc.wait(timeout=60)
            self.assertNotEqual(rc, 0)
            self.assertNotIn("_m1_bench_trial_", src.read_text(), "SIGTERM left the edit behind")


class Provenance(unittest.TestCase):
    """Group 4: the binary's identity and honest noise telemetry."""

    def test_run_records_binary_sha256(self):
        with tempfile.TemporaryDirectory(prefix="m1-prov-") as td:
            r = run_bench(Path(td), ["--no-baseline", "--out", str(Path(td) / "o.json")])
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            data = json.loads((Path(td) / "o.json").read_text())
            sha = (data.get("turbo_lean_binary") or {}).get("sha256")
            self.assertIsInstance(sha, str, data.get("turbo_lean_binary"))
            self.assertEqual(len(sha), 64)
            int(sha, 16)  # hex
            self.assertIn("turbo_lean_dirty", data)

    def test_rebaseline_refuses_dirty_tree(self):
        import subprocess as sp
        with tempfile.TemporaryDirectory(prefix="m1-rebase-") as td:
            body = ("\n".join(
                l for l in PfrAndSourceSafety.PFR_STUB.splitlines()
                if "--no-auto-worktree-link" not in l and "FAKE_COUNTER" not in l
                and "FAKE_OLEAN" not in l and "sys.exit(1)" not in l
                and "stale imports" not in l and "print(json.dumps({'error'" not in l)
                + "\nprint(json.dumps({'status': 'theorem_cache_hit', 'decl': 'd',\n"
                  "   'elapsed_ms': 50, 'phase_timings': {'wall_ms': 200.0,\n"
                  "   'coverage_ratio': 0.99, 'phases_ms': {}}})); sys.exit(0)\n")
            # Build the stub INSIDE a git repo: turbo_lean_commit_for walks up
            # from the binary to find the enclosing checkout.
            repo = Path(td) / "tl"
            (repo / "target" / "release").mkdir(parents=True)
            stub, gitstub = make_stub_binary(repo / "target" / "release", body)
            make_fake_projects(Path(td))
            real_git = __import__("shutil").which("git")
            def g(*a, **kw):
                sp.run([real_git, "-C", str(repo)] + list(a), check=True, capture_output=True,
                       env=dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t",
                                GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@t"))
            g("init", "-q")
            g("add", "-A")
            g("commit", "-q", "-m", "init")
            (repo / "dirty.txt").write_text("uncommitted\n")
            g("add", "-A")  # staged but uncommitted: still dirty
            env = dict(os.environ, TURBO_LEAN_GIT=str(gitstub),
                       PATH=str(Path(td) / "fake-bin") + os.pathsep + os.environ.get("PATH", ""),
                       TURBO_LEAN_ALLOWED_CSIMP="*", TURBO_LEAN_ALLOWED_UNSAFE="*",
                       TURBO_LEAN_ALLOWED_IMPLEMENTED_BY="*", FAKE_PFR_FAIL="1")
            cmd = BENCH_CMD + ["--turbo-lean-bin", str(stub),
                   "--batteries-dir", str(Path(td) / "batteries"),
                   "--pfr-dir", str(Path(td) / "pfr"),
                   "--trials", "1", "--warmup", "0", "--skip-rev-check",
                   "--allow-busy-node", "--rebaseline", "--no-baseline",
                   "--out", str(Path(td) / "b.json")]
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=600, env=env)
            self.assertEqual(r.returncode, 4, r.stdout + r.stderr)
            self.assertIn("--rebaseline requires a clean", r.stderr)

    def test_psi_parser_reads_some_and_full_lines(self):
        mod = load_script()
        text = ("some avg10=0.00 avg60=0.00 avg300=0.00 total=134981125933\n"
                "full avg10=1.25 avg60=0.00 avg300=0.01 total=0\n")
        self.assertEqual(mod.parse_psi_lines(text), {"some": 0.0, "full": 1.25})
        self.assertEqual(mod.parse_psi_lines("garbage"), {"some": None, "full": None})
        self.assertEqual(mod.parse_psi_lines(""), {"some": None, "full": None})

    def test_sample_psi_reports_real_kernel_values(self):
        mod = load_script()
        psi = mod.sample_psi()
        self.assertIn("load1", psi)
        for name in ("cpu", "memory", "io"):
            self.assertIsInstance(psi[name], dict, name)
            self.assertIn("some", psi[name]) and self.assertIn("full", psi[name])
        # This test host exposes PSI; a failed read must be null, never 0.0.
        if any(v is not None for v in psi["cpu"].values()):
            self.assertIsInstance(psi["cpu"]["some"], float)

    def test_mode_result_keeps_per_trial_load_samples(self):
        mod = load_script()
        m = mod.mode_result([100.0, 110.0], [0.99, 0.99], ["theorem_cache_hit"],
                            psi_lists=[[{"cpu": {"some": 0.1, "full": 0.0},
                                         "memory": {"some": 0.0, "full": 0.0},
                                         "io": {"some": 0.0, "full": 0.0}, "load1": 1.5},
                                        {"cpu": {"some": 0.2, "full": 0.0},
                                         "memory": {"some": 0.0, "full": 0.0},
                                         "io": {"some": 0.0, "full": 0.0}, "load1": 2.5}]])
        loads = [t.get("load1") for t in m["psi_trials"]]
        self.assertEqual(loads, [1.5, 2.5])
        self.assertEqual(m["psi_max"]["cpu.some"], 0.2)
        self.assertIn("psi_contended", m)


class EndToEnd(unittest.TestCase):
    """Drive the full script against a stub turbo-lean binary."""

    def _run_bench(self, root, extra):
        return run_bench(root, extra)

    def test_full_run_and_comparison(self):
        mod = load_script()
        with tempfile.TemporaryDirectory(prefix="m1-bench-test-") as td:
            root = Path(td)
            out = root / "run.json"
            # Fake projects are not git repos: rev pinning must be skipped explicitly.
            r1 = self._run_bench(root, ["--machine-label", "lab-node-1",
                                        "--out", str(out), "--no-baseline"])
            self.assertEqual(r1.returncode, 0, r1.stdout + r1.stderr)
            data = json.loads(out.read_text())
            self.assertEqual(data["verdict"]["verdict"], "not_compared")
            self.assertEqual(data["turbo_lean_commit"], "not_a_git_checkout")
            for wid in ("batteries_list_lemmas_top", "batteries_unionfind_top"):
                wl = data["workloads"][wid]
                self.assertEqual(wl["status"], "ok", wid)
                for mode in mod.MODES:
                    self.assertGreater(wl["modes"][mode]["trials"], 0, (wid, mode))
            # PFR stub fails => blocked as expected.
            self.assertEqual(data["workloads"]["pfr_more_ruzsa_dist"]["status"], "blocked_as_expected")

            # Comparison verdicts must not depend on scheduler timing: feed
            # FIXED numbers into the comparison. Reusing r1's run as the base
            # (same provenance/settings) but replacing every measured median
            # with a constant makes the verdicts deterministic. This replaced
            # the previous version, which compared two measured runs and
            # failed on loaded machines when the second run drifted past the
            # noise band (reviewer's flaky failure).
            def base_with_fixed_medians(median):
                base = json.loads(out.read_text())
                base["turbo_lean_commit"] = "1" * 40
                base["turbo_lean_dirty"] = False
                for wid, wl in base["workloads"].items():
                    if wl.get("expected_status") == "blocked":
                        continue
                    for mode in mod.MODES:
                        m = wl["modes"][mode]
                        m["median_ms"] = median
                        m["runs_ms"] = [median] * m["trials"]
                p = root / f"fixed_{median}.json"
                p.write_text(json.dumps(base))
                return p
            huge = base_with_fixed_medians(1_000_000.0)
            r2 = self._run_bench(root, ["--machine-label", "lab-node-1",
                                        "--out", str(root / "run2.json"),
                                        "--baseline", str(huge)])
            self.assertEqual(r2.returncode, 0, r2.stdout + r2.stderr)
            data2 = json.loads((root / "run2.json").read_text())
            self.assertEqual(data2["verdict"]["verdict"], "pass", data2["verdict"])
            # And the mirror case: a baseline far below any real measurement
            # must be a regression (exit 1), deterministically.
            tiny = base_with_fixed_medians(0.001)
            r4 = self._run_bench(root, ["--machine-label", "lab-node-1",
                                        "--out", str(root / "run4.json"),
                                        "--baseline", str(tiny)])
            self.assertEqual(r4.returncode, 1, r4.stdout + r4.stderr)
            data4 = json.loads((root / "run4.json").read_text())
            self.assertEqual(data4["verdict"]["verdict"], "regression", data4["verdict"])
            self.assertTrue(data4["verdict"]["regressions"], data4["verdict"])
            # Cross-host comparison must be flagged, never a pass.
            r3 = self._run_bench(root, ["--machine-label", "other-runner",
                                        "--out", str(root / "run3.json"),
                                        "--baseline", str(huge)])
            self.assertEqual(r3.returncode, 0, r3.stdout + r3.stderr)
            data3 = json.loads((root / "run3.json").read_text())
            self.assertEqual(data3["verdict"]["verdict"], "comparison_skipped_host_mismatch")


class ComparabilityAndProvenance(unittest.TestCase):
    """Point 1: malformed provenance rejected; incomparable runs refused; binary compared honestly."""

    def test_baseline_rejected_when_dirty_or_provenance_missing(self):
        mod = load_script()
        good = full_valid_baseline(mod)
        self.assertEqual(mod.validate_baseline(good), [])

        dirty = json.loads(json.dumps(good))
        dirty["turbo_lean_dirty"] = True
        errs = mod.validate_baseline(dirty)
        self.assertTrue(any("dirty" in e for e in errs), errs)

        for field in ("turbo_lean_commit", "turbo_lean_binary", "workload_revs", "toolchain"):
            for bad in (None, "REMOVE"):
                broken = json.loads(json.dumps(good))
                if bad == "REMOVE":
                    broken.pop(field, None)
                else:
                    broken[field] = None
                errs = mod.validate_baseline(broken)
                self.assertTrue(errs, (field, bad))

        bad_commit = json.loads(json.dumps(good))
        bad_commit["turbo_lean_commit"] = "not_a_git_checkout"
        self.assertTrue(mod.validate_baseline(bad_commit))

        bad_bin = json.loads(json.dumps(good))
        bad_bin["turbo_lean_binary"] = {"path": "/fake", "sha256": None}
        self.assertTrue(mod.validate_baseline(bad_bin))

        bad_revs = json.loads(json.dumps(good))
        bad_revs["workload_revs"] = {"batteries": "b" * 40, "pfr": None}
        self.assertTrue(mod.validate_baseline(bad_revs))

        bad_tc1 = json.loads(json.dumps(good))
        bad_tc1["toolchain"] = {"lean_toolchain": None, "lean_version": "Lean (version 4.35.0)"}
        self.assertTrue(mod.validate_baseline(bad_tc1))

        bad_tc2 = json.loads(json.dumps(good))
        bad_tc2["toolchain"] = {"lean_toolchain": "leanprover/lean4:v4.35.0", "lean_version": None}
        self.assertTrue(mod.validate_baseline(bad_tc2))

    def test_dirty_baseline_exits_nonzero_with_named_error(self):
        mod = load_script()
        with tempfile.TemporaryDirectory(prefix="m1-dirty-base-") as td:
            base = full_valid_baseline(mod)
            base["turbo_lean_dirty"] = True
            bp = Path(td) / "b.json"
            bp.write_text(json.dumps(base))
            r = run_bench(Path(td), ["--baseline", str(bp), "--out", str(Path(td) / "o.json")])
            self.assertNotEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("dirty", r.stderr)

    def test_validate_only_cli_rejects_dirty_marker_that_is_not_boolean_false(self):
        """DeepSeek review: --validate-only passed null and string "true" markers."""
        mod = load_script()
        with tempfile.TemporaryDirectory(prefix="m1-validate-only-") as td:
            def cli(name, mutate):
                base = full_valid_baseline(mod)
                mutate(base)
                p = Path(td) / f"{name}.json"
                p.write_text(json.dumps(base))
                return subprocess.run(BENCH_CMD + ["--validate-only", str(p)],
                                      capture_output=True, text=True, timeout=300)

            ok = cli("valid", lambda b: None)
            self.assertEqual(ok.returncode, 0, ok.stdout + ok.stderr)
            self.assertIn("OK:", ok.stdout)

            for name, mutate, fragment in (
                    ("string_true", lambda b: b.__setitem__("turbo_lean_dirty", "true"),
                     "baseline_invalid_turbo_lean_dirty"),
                    ("null", lambda b: b.__setitem__("turbo_lean_dirty", None),
                     "baseline_invalid_turbo_lean_dirty"),
                    ("number", lambda b: b.__setitem__("turbo_lean_dirty", 1),
                     "baseline_invalid_turbo_lean_dirty"),
                    ("missing", lambda b: b.pop("turbo_lean_dirty"),
                     "baseline_missing_turbo_lean_dirty"),
                    ("bool_true", lambda b: b.__setitem__("turbo_lean_dirty", True),
                     "baseline_dirty_tree")):
                r = cli(name, mutate)
                self.assertNotEqual(r.returncode, 0, (name, r.stdout + r.stderr))
                self.assertIn(fragment, r.stdout + r.stderr, name)

            valid_false = cli("valid_false", lambda b: b.__setitem__("turbo_lean_dirty", False))
            self.assertEqual(valid_false.returncode, 0, valid_false.stdout + valid_false.stderr)

    def test_workload_rev_mismatch_refuses_comparison_nonzero_and_prints_both(self):
        mod = load_script()
        with tempfile.TemporaryDirectory(prefix="m1-rev-mis-") as td:
            r0 = run_bench(Path(td), ["--no-baseline", "--out", str(Path(td) / "o0.json")])
            self.assertEqual(r0.returncode, 0, r0.stdout + r0.stderr)
            o0 = json.loads((Path(td) / "o0.json").read_text())
            base = full_valid_baseline(mod)
            # Same host AND same condition: sync the whole host block (label
            # and fingerprint included) — a labeled baseline no longer matches
            # an unlabeled run on the same machine.
            base["host"] = dict(o0["host"])
            base["settings"] = dict(o0["settings"])
            base["toolchain"] = dict(o0.get("toolchain") or full_valid_baseline(mod)["toolchain"])
            base["workload_revs"] = dict(o0["workload_revs"], batteries="deadbeef" * 5)
            bp = Path(td) / "b.json"
            bp.write_text(json.dumps(base))
            r = run_bench(Path(td), ["--baseline", str(bp), "--out", str(Path(td) / "o.json")])
            self.assertNotEqual(r.returncode, 0, r.stdout + r.stderr)
            combined = r.stdout + r.stderr
            self.assertIn("comparison_refused_workload_rev_mismatch", combined)
            self.assertIn("deadbeef" * 5, combined)
            self.assertIn(o0["workload_revs"]["batteries"], combined)

    def test_toolchain_mismatch_refuses_comparison_nonzero_and_prints_both(self):
        mod = load_script()
        with tempfile.TemporaryDirectory(prefix="m1-tc-mis-") as td:
            r0 = run_bench(Path(td), ["--no-baseline", "--out", str(Path(td) / "o0.json")])
            self.assertEqual(r0.returncode, 0, r0.stdout + r0.stderr)
            o0 = json.loads((Path(td) / "o0.json").read_text())
            base = full_valid_baseline(mod)
            # Same host AND same condition: sync the whole host block (label
            # and fingerprint included) — a labeled baseline no longer matches
            # an unlabeled run on the same machine.
            base["host"] = dict(o0["host"])
            base["settings"] = dict(o0["settings"])
            base["workload_revs"] = dict(o0["workload_revs"])
            base["toolchain"] = {"lean_toolchain": "leanprover/lean4:v4.34.0",
                                 "lean_version": "Lean (version 4.34.0, old)"}
            bp = Path(td) / "b.json"
            bp.write_text(json.dumps(base))
            r = run_bench(Path(td), ["--baseline", str(bp), "--out", str(Path(td) / "o.json")])
            self.assertNotEqual(r.returncode, 0, r.stdout + r.stderr)
            combined = r.stdout + r.stderr
            self.assertIn("comparison_refused_toolchain_mismatch", combined)
            self.assertIn("v4.34.0", combined)
            self.assertIn("v4.35.0", combined)

    def test_different_binary_and_commit_is_compared_and_prints_both(self):
        mod = load_script()
        with tempfile.TemporaryDirectory(prefix="m1-diff-bin-") as td:
            r0 = run_bench(Path(td), ["--no-baseline", "--out", str(Path(td) / "o0.json")])
            self.assertEqual(r0.returncode, 0, r0.stdout + r0.stderr)
            o0 = json.loads((Path(td) / "o0.json").read_text())
            base = full_valid_baseline(mod)
            for wid, wl in base["workloads"].items():
                if wl.get("expected_status") == "blocked":
                    continue
                for m in wl["modes"].values():
                    m["median_ms"] = 1_000_000.0
                    m["runs_ms"] = [1_000_000.0] * m["trials"]
            # Same host AND same condition: sync the whole host block (label
            # and fingerprint included) — a labeled baseline no longer matches
            # an unlabeled run on the same machine.
            base["host"] = dict(o0["host"])
            base["settings"] = dict(o0["settings"])
            base["workload_revs"] = dict(o0["workload_revs"])
            base["toolchain"] = dict(o0.get("toolchain") or full_valid_baseline(mod)["toolchain"])
            base["turbo_lean_commit"] = "1111111111111111111111111111111111111111"
            base["turbo_lean_binary"] = {"path": "/old/turbo-lean", "sha256": "2" * 64}
            bp = Path(td) / "b.json"
            bp.write_text(json.dumps(base))
            r = run_bench(Path(td), ["--baseline", str(bp), "--out", str(Path(td) / "o.json")])
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            o = json.loads((Path(td) / "o.json").read_text())
            v = o["verdict"]
            self.assertEqual(v["verdict"], "pass")
            self.assertIs(v["same_binary"], False)
            self.assertEqual(v["baseline_commit"], "1" * 40)
            self.assertEqual(v["run_commit"], o["turbo_lean_commit"])
            self.assertEqual(v["baseline_binary_sha256"], "2" * 64)
            self.assertEqual(v["run_binary_sha256"], o["turbo_lean_binary"]["sha256"])
            self.assertIn("1" * 40, r.stdout)
            self.assertIn(o["turbo_lean_commit"], r.stdout)
            self.assertIn("2" * 64, r.stdout)
            self.assertIn(o["turbo_lean_binary"]["sha256"], r.stdout)
            self.assertNotIn("same binary", r.stdout)

    def test_same_binary_says_same_binary_and_records_toolchain(self):
        mod = load_script()
        with tempfile.TemporaryDirectory(prefix="m1-same-bin-") as td:
            r0 = run_bench(Path(td), ["--no-baseline", "--out", str(Path(td) / "o0.json")])
            self.assertEqual(r0.returncode, 0, r0.stdout + r0.stderr)
            o0 = json.loads((Path(td) / "o0.json").read_text())
            self.assertEqual(o0["toolchain"]["lean_toolchain"], "leanprover/lean4:v4.35.0")
            self.assertIn("Lean (version 4.35.0", o0["toolchain"]["lean_version"])
            base = full_valid_baseline(mod)
            for wid, wl in base["workloads"].items():
                if wl.get("expected_status") == "blocked":
                    continue
                for m in wl["modes"].values():
                    m["median_ms"] = 1_000_000.0
                    m["runs_ms"] = [1_000_000.0] * m["trials"]
            # Same host AND same condition: sync the whole host block (label
            # and fingerprint included) — a labeled baseline no longer matches
            # an unlabeled run on the same machine.
            base["host"] = dict(o0["host"])
            base["settings"] = dict(o0["settings"])
            base["workload_revs"] = dict(o0["workload_revs"])
            base["toolchain"] = dict(o0.get("toolchain") or full_valid_baseline(mod)["toolchain"])
            base["turbo_lean_commit"] = "3" * 40
            base["turbo_lean_binary"] = dict(o0["turbo_lean_binary"])
            bp = Path(td) / "b.json"
            bp.write_text(json.dumps(base))
            r = run_bench(Path(td), ["--baseline", str(bp), "--out", str(Path(td) / "o.json")])
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            o = json.loads((Path(td) / "o.json").read_text())
            self.assertIs(o["verdict"]["same_binary"], True)
            self.assertIn("same binary", r.stdout)


class CliFlags(unittest.TestCase):
    """--check-timeout-s and --only-workloads (G2a measurement plumbing)."""

    @staticmethod
    def _runner_args(**extra):
        attrs = {"turbo_lean_bin": "t", "batteries_dir": "b", "pfr_dir": "p",
                 "trials": 1, "warmup": 0}
        attrs.update(extra)
        return type("A", (), attrs)()

    def _make_runner(self, mod, args):
        old_git = os.environ.get("TURBO_LEAN_GIT")
        os.environ["TURBO_LEAN_GIT"] = old_git or "/usr/bin/git"
        runner = mod.Runner(args)
        self.addCleanup(__import__("shutil").rmtree, runner.scratch,
                        ignore_errors=True)
        if old_git is None:
            self.addCleanup(os.environ.pop, "TURBO_LEAN_GIT", None)
        return runner

    def test_check_timeout_flag_reaches_check_argv(self):
        mod = load_script()
        runner = self._make_runner(mod, self._runner_args(check_timeout_s=1234))
        with tempfile.TemporaryDirectory() as td:
            argv = runner.check_argv(mod.WORKLOADS[0], Path(td), Path(td) / "f.lean")
        self.assertEqual(argv[argv.index("--timeout") + 1], "1234")

    def test_check_timeout_defaults_when_args_lack_attr(self):
        mod = load_script()
        runner = self._make_runner(mod, self._runner_args())
        with tempfile.TemporaryDirectory() as td:
            argv = runner.check_argv(mod.WORKLOADS[0], Path(td), Path(td) / "f.lean")
        self.assertEqual(argv[argv.index("--timeout") + 1], str(mod.CHECK_TIMEOUT_S))

    def test_only_workloads_unknown_name_exits_2(self):
        mod = load_script()
        with self.assertRaises(SystemExit) as cm:
            mod.main(["--only-workloads", "not_a_workload",
                      "--batteries-dir", "b", "--pfr-dir", "p"])
        self.assertEqual(cm.exception.code, 2)

    def test_only_workloads_filters_measurement_selection_in_order(self):
        mod = load_script()
        picked = type("A", (), {"only_workloads":
                                "batteries_unionfind_top,batteries_list_lemmas_top"})()
        ids = [w["id"] for w in mod.selected_workloads(picked)]
        self.assertEqual(ids, ["batteries_list_lemmas_top", "batteries_unionfind_top"])
        everything = type("A", (), {"only_workloads": None})()
        self.assertEqual(len(mod.selected_workloads(everything)), len(mod.WORKLOADS))


class PeakRssRecording(unittest.TestCase):
    def test_mode_result_records_per_trial_peak_rss(self):
        mod = load_script()
        m = mod.mode_result([100.0, 110.0], [0.99, 0.99],
                            ["theorem_cache_hit"] * 2, rss_mbs=[812, 815])
        self.assertEqual(m["peak_rss_mb_trials"], [812, 815])

    def test_mode_result_without_rss_values_has_no_rss_key(self):
        mod = load_script()
        self.assertNotIn("peak_rss_mb_trials",
                         mod.mode_result([100.0], [0.99], ["theorem_cache_hit"]))
        self.assertNotIn("peak_rss_mb_trials",
                         mod.mode_result([100.0], [0.99], ["theorem_cache_hit"],
                                         rss_mbs=[None]))

    def test_split_trials_extracts_peak_rss_per_healthy_trial(self):
        mod = load_script()
        def trial(status, rss, exit_code=0):
            return {"exit_code": exit_code, "external_wall_ms": 100.0,
                    "json": {"status": status, "peak_rss_mb": rss},
                    "stderr": "", "psi_before": {}, "psi_after": {}}
        trials = [trial("theorem_cache_hit", 801),
                  trial("failed", 999, exit_code=1),   # excluded like its timing
                  trial("theorem_cache_hit", 803)]
        ts = mod.Runner.split_trials(trials)
        self.assertEqual(ts.rss_mbs, [801, 803])
        self.assertEqual(ts.failed, 1)


class ScriptLoadsUnregistered(unittest.TestCase):
    def test_script_loads_without_sys_modules_registration(self):
        # External tools load this script exactly like this, without first
        # registering it in sys.modules; class creation must survive that
        # (under future annotations a dataclass resolves its field strings
        # through sys.modules and dies here with AttributeError).
        spec = importlib.util.spec_from_file_location(
            "bench_check_loop_unregistered", SCRIPT)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        ts = mod.Runner.split_trials([])
        self.assertEqual((ts.runs, ts.failed), ([], 0))
        # Positional unpacking stays available to external callers.
        runs, covs, tool_covs, statuses, phases, psis, fissions, rss, failed = ts
        self.assertEqual((runs, failed), ([], 0))


class HostFingerprint(unittest.TestCase):
    @staticmethod
    def _host(hostname, label, fp):
        h = {"hostname": hostname, "machine_label": label}
        if fp is not None:
            h["host_fingerprint"] = fp
        return {"host": h}

    def test_same_label_different_machines_do_not_match(self):
        mod = load_script()
        self.assertFalse(mod.host_matches(self._host("quiet", "quiet", "a" * 64),
                                          self._host("quiet", "quiet", "b" * 64)))

    def test_same_fingerprint_same_label_matches(self):
        mod = load_script()
        self.assertTrue(mod.host_matches(self._host("quiet", "quiet", "a" * 64),
                                         self._host("quiet", "quiet", "a" * 64)))

    def test_same_fingerprint_different_labels_do_not_match(self):
        mod = load_script()
        self.assertFalse(mod.host_matches(self._host("x", "x", "a" * 64),
                                          self._host("y", "y", "a" * 64)))

    def test_legacy_hosts_without_fingerprint_compare_hostnames(self):
        mod = load_script()
        self.assertTrue(mod.host_matches(self._host("uruk", None, None),
                                         self._host("uruk", None, None)))
        self.assertFalse(mod.host_matches(self._host("uruk", None, None),
                                          self._host("gilgamesh", None, None)))

    def test_unfingerprinted_baseline_never_matches_a_labeled_run(self):
        # An old baseline (real hostname, no fingerprint) against a new labeled
        # run mismatches twice over: the label requires both fingerprints, and
        # a one-sided fingerprint is always a mismatch. Migration: --rebaseline.
        mod = load_script()
        self.assertFalse(mod.host_matches(self._host("uruk", None, None),
                                          self._host("g2a-ro-192c", "g2a-ro-192c",
                                                     "a" * 64)))

    def test_fingerprint_on_one_side_only_is_always_a_mismatch(self):
        # A key PRESENT but None (a new-schema entry from a machine-id-less
        # host) against a real fingerprint must mismatch even with equal
        # hostnames and no labels: the None side's hostname proves nothing
        # about the machine. A key ABSENT on both sides is the schema-1
        # legacy case, where the hostname fallback still applies.
        mod = load_script()
        with_fp = {"host": {"hostname": "box", "machine_label": None,
                            "host_fingerprint": "a" * 64}}
        none_fp = {"host": {"hostname": "box", "machine_label": None,
                            "host_fingerprint": None}}
        legacy = {"host": {"hostname": "box", "machine_label": None}}
        self.assertFalse(mod.host_matches(with_fp, none_fp))
        self.assertFalse(mod.host_matches(none_fp, with_fp))
        self.assertFalse(mod.host_matches(legacy, with_fp))
        # Legacy-vs-legacy and legacy-vs-present-None keep the fallback.
        self.assertTrue(mod.host_matches(legacy, dict(legacy)))
        self.assertTrue(mod.host_matches(legacy, none_fp))

    def test_label_requires_fingerprints_on_both_sides(self):
        # host_id writes the label into hostname and records no fingerprint
        # without a machine-id, so two machine-id-less containers sharing a
        # label would pass the legacy hostname fallback. A label on either
        # side therefore requires both fingerprints; a missing one is a host
        # mismatch.
        mod = load_script()
        self.assertFalse(mod.host_matches(self._host("quiet", "quiet", None),
                                          self._host("quiet", "quiet", None)))
        labeled_fp = self._host("quiet", "quiet", "a" * 64)
        labeled_no_fp = self._host("quiet", "quiet", None)
        self.assertFalse(mod.host_matches(labeled_no_fp, labeled_fp))
        self.assertFalse(mod.host_matches(labeled_fp, labeled_no_fp))

    def test_label_on_one_side_only_does_not_match(self):
        # The help promises a labeled baseline is never compared with a run
        # under another condition; an unlabeled run is another condition,
        # same machine or not.
        mod = load_script()
        labeled = self._host("quiet", "quiet", "a" * 64)
        unlabeled = self._host("node-1", None, "a" * 64)
        self.assertFalse(mod.host_matches(labeled, unlabeled))
        self.assertFalse(mod.host_matches(unlabeled, labeled))

    def test_host_mismatch_reason_names_fingerprints(self):
        mod = load_script()
        base = full_valid_baseline(mod)
        base["host"]["host_fingerprint"] = "a" * 64
        base["host"]["machine_label"] = "quiet"
        base["host"]["hostname"] = "quiet"
        res = mod_results_like(mod, base, 1000.0)
        res["host"] = dict(base["host"], host_fingerprint="b" * 64)
        v = mod.compare_run(base, res)
        self.assertEqual(v["verdict"], "comparison_skipped_host_mismatch")
        self.assertIn(("a" * 64)[:12], v["skipped_reason"])
        self.assertIn(("b" * 64)[:12], v["skipped_reason"])

    def test_no_machine_id_means_no_fingerprint(self):
        # Without a machine-id the fingerprint would be sha256(hostname+"\0"),
        # a confirmable hash of the node name — against the no-node-name
        # claim — and ephemeral containers would never match each other.
        # The honest degradation is None, so the hostname/label fallback
        # applies in host_matches.
        mod = load_script()
        mod.read_machine_id = lambda: ""
        h = mod.host_id("g2a-ro-192c")
        self.assertIsNone(h["host_fingerprint"])
        # Control: with a machine-id the fingerprint is a 64-hex digest and
        # differs across machine-ids.
        mod.read_machine_id = lambda: "mid-one"
        f1 = mod.host_id("g2a-ro-192c")["host_fingerprint"]
        mod.read_machine_id = lambda: "mid-two"
        f2 = mod.host_id("g2a-ro-192c")["host_fingerprint"]
        self.assertTrue(re.fullmatch(r"[0-9a-f]{64}", f1 or ""), f1)
        self.assertNotEqual(f1, f2)

    def test_host_id_records_hex_fingerprint_never_node_name(self):
        mod = load_script()
        # Stubbed like its sibling test_no_machine_id_means_no_fingerprint:
        # without this the test demands a 64-hex fingerprint from the real
        # /etc/machine-id and fails on any host that lacks one, a case the
        # script's own docstring calls common in containers.
        mod.read_machine_id = lambda: "fixture-machine-id"
        h = mod.host_id("g2a-ro-192c")
        fp = h.get("host_fingerprint")
        self.assertTrue(isinstance(fp, str) and re.fullmatch(r"[0-9a-f]{64}", fp), fp)
        node = platform.node()
        if node and node not in "g2a-ro-192c":
            self.assertNotIn(node, json.dumps(h))
        self.assertEqual(mod.host_id(None).get("host_fingerprint"), fp)


class ReplaySummaryHonesty(unittest.TestCase):
    def test_summarize_carries_failed_and_other_status_counts(self):
        mod = load_script()
        res = {"trials": 5, "workloads": {"w1": {
            "expected_status": "active", "status": "failed",
            "modes": {"warm_cache_hit_daemon": {
                "trials": 2, "failed_trials": 3,
                "cas_replay": {"hits": 1, "misses": 0, "hit_rate": 1.0}}}}}}
        rep = mod.summarize_cas_replay(res)
        un = rep["unedited_recheck"]
        self.assertEqual(un["classified_calls"], 1)
        self.assertEqual(un["failed_trials"], 3)
        self.assertEqual(un["other_status_calls"], 1)
        self.assertIsNone(un["fission_cached_subshards"])
        self.assertIsNone(un["fission_verified_subshards"])
        self.assertEqual(rep["non_ok_workloads"], ["w1"])

    def test_schema_bumped_and_buckets_carry_check_calls_alias(self):
        # The count field was renamed classified_calls and cold modes lost
        # their cas_replay block: a schema change, so SCHEMA_VERSION moves to
        # 2 and old readers keep a check_calls alias in every bucket.
        mod = load_script()
        self.assertEqual(mod.SCHEMA_VERSION, 2)
        rep = mod.summarize_cas_replay({"trials": 2, "workloads": {}})
        for bucket in ("unedited_recheck", "edited_recheck", "overall"):
            self.assertEqual(rep[bucket]["check_calls"],
                             rep[bucket]["classified_calls"])

    def test_fission_counters_keep_none_distinct_from_zero(self):
        mod = load_script()
        m = mod.mode_result([100.0], [0.99], ["theorem_verified"],
                            fission_dicts=[{}], replay_mode=True)
        self.assertIsNone(m["cas_replay"]["fission_cached_subshards"])
        self.assertIsNone(m["cas_replay"]["fission_verified_subshards"])

    def test_mode_result_without_replay_mode_carries_no_cas_replay(self):
        mod = load_script()
        m = mod.mode_result([100.0], [0.99], ["theorem_verified"])
        self.assertNotIn("cas_replay", m)


class ReplayFailureVisibility(unittest.TestCase):
    def test_all_failed_warm_mode_still_counts_failed_trials(self):
        # mode_result emits no cas_replay when every trial failed; the bucket
        # must count those failures anyway — a total failure is exactly what
        # the counts exist for.
        mod = load_script()
        res = {"trials": 5, "workloads": {"w1": {
            "expected_status": "active", "status": "failed",
            "modes": {"warm_cache_hit_daemon": {"trials": 0,
                                                "failed_trials": 5}}}}}
        rep = mod.summarize_cas_replay(res)
        un = rep["unedited_recheck"]
        self.assertEqual(un["failed_trials"], 5)
        self.assertEqual(un["classified_calls"], 0)
        self.assertIn("w1", un["workloads"])

    def test_all_other_status_warm_mode_still_counts_other_calls(self):
        mod = load_script()
        res = {"trials": 3, "workloads": {"w1": {
            "expected_status": "active", "status": "failed",
            "modes": {"warm_cache_hit_daemon": {"trials": 3,
                                                "failed_trials": 0}}}}}
        rep = mod.summarize_cas_replay(res)
        self.assertEqual(rep["unedited_recheck"]["other_status_calls"], 3)

    def test_g2a_line_prints_for_an_all_failed_warm_loop(self):
        # Warm trials run with the daemon (TURBO_LEAN_NO_DAEMON unset); this
        # stub fails every one of them while cold trials and the warm setup
        # (both no_daemon) succeed, so every replay call fails and
        # classified_calls is 0 run-wide.
        stub_body = (
            "#!/usr/bin/env python3\n"
            "import json, os, sys\n"
            "args = sys.argv[1:]\n"
            "if os.environ.get('FAKE_PFR_FAIL') and '--no-auto-worktree-link' in args:\n"
            "    print(json.dumps({'error': 'stale imports: import_refresh fail-closed'}))\n"
            "    sys.exit(1)\n"
            "if not os.environ.get('TURBO_LEAN_NO_DAEMON'):\n"
            "    sys.exit(1)\n"
            "out = {'status': 'theorem_verified', 'decl': 'd', 'elapsed_ms': 50,\n"
            "       'phase_timings': {'wall_ms': 200.0, 'phase_sum_ms': 199.0,\n"
            "                         'phase_covered_ms': 199.0, 'phase_overlap_ms': 0.0,\n"
            "                         'coverage_ratio': 0.99,\n"
            "                         'phases_ms': {'setup': 10.0}}}\n"
            "print(json.dumps(out)); sys.exit(0)\n")
        with tempfile.TemporaryDirectory(prefix="m1-allfail-") as td:
            r = run_bench(Path(td), ["--no-baseline", "--only-workloads",
                                     "batteries_list_lemmas_top",
                                     "--out", str(Path(td) / "o.json")],
                          stub_body=stub_body)
            self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
            self.assertIn("G2A CAS REPLAY:", r.stdout)
            self.assertIn("failed_trials=4", r.stdout)
            self.assertIn("non_ok_workloads=['batteries_list_lemmas_top']", r.stdout)


class CheckTimeoutMainPath(unittest.TestCase):
    def test_env_override_reaches_a_real_run(self):
        # Through main(), the path a real run takes: no --check-timeout-s
        # flag, env override set. The recorded args must carry the value
        # actually used (argparse's import-time default froze 900 in and the
        # validated global was never read back).
        with tempfile.TemporaryDirectory(prefix="m1-timeout-main-") as td:
            r = run_bench(Path(td), ["--no-baseline", "--only-workloads",
                                     "batteries_list_lemmas_top",
                                     "--out", str(Path(td) / "o.json")],
                          env_extra={"TURBO_LEAN_BENCH_CHECK_TIMEOUT_S": "123"})
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            data = json.loads((Path(td) / "o.json").read_text())
            self.assertEqual(data["args"]["check_timeout_s"], 123)
            self.assertEqual(
                data["settings"]["TURBO_LEAN_BENCH_CHECK_TIMEOUT_S"], "123")

    def test_explicit_flag_beats_env_override(self):
        with tempfile.TemporaryDirectory(prefix="m1-timeout-flag-") as td:
            r = run_bench(Path(td), ["--no-baseline", "--only-workloads",
                                     "batteries_list_lemmas_top",
                                     "--check-timeout-s", "77",
                                     "--out", str(Path(td) / "o.json")],
                          env_extra={"TURBO_LEAN_BENCH_CHECK_TIMEOUT_S": "123"})
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            data = json.loads((Path(td) / "o.json").read_text())
            self.assertEqual(data["args"]["check_timeout_s"], 77)


class CommittedArtifactIsPathFree(unittest.TestCase):
    """A results JSON is committed, so it carries no host path."""

    @staticmethod
    def digest(value):
        import hashlib
        return "<sha256:" + hashlib.sha256(value.encode()).hexdigest()[:12] + ">"

    def test_recorded_settings_digest_path_values_and_keep_the_rest(self):
        mod = load_script()
        got = mod.recorded_settings({"TURBO_LEAN_GIT": "/usr/bin/git",
                                     "TURBO_LEAN_HOME": "/home/someone/.cache/tl",
                                     "TURBO_LEAN_ALLOWED_CSIMP": "*"})
        self.assertEqual(got["TURBO_LEAN_GIT"], self.digest("/usr/bin/git"))
        self.assertEqual(got["TURBO_LEAN_HOME"], self.digest("/home/someone/.cache/tl"))
        self.assertEqual(got["TURBO_LEAN_ALLOWED_CSIMP"], "*")
        self.assertIsNone(got["TURBO_LEAN_STAGING_DIR"])
        self.assertEqual(set(got), set(mod.RECORDED_ENV_VARS))
        # A digest is kept as it is, so re-recording an artifact changes nothing.
        d = got["TURBO_LEAN_GIT"]
        self.assertEqual(mod.recorded_setting("TURBO_LEAN_GIT", d), d)

    def test_settings_match_reads_a_raw_path_and_its_digest_alike(self):
        mod = load_script()
        base = full_valid_baseline(mod)
        base["settings"]["TURBO_LEAN_GIT"] = "/usr/bin/git"
        res = {"settings": dict(base["settings"])}
        res["settings"]["TURBO_LEAN_GIT"] = self.digest("/usr/bin/git")
        self.assertTrue(mod.settings_match(base, res))
        # A different path is still a different setting.
        res["settings"]["TURBO_LEAN_GIT"] = self.digest("/opt/git/bin/git")
        self.assertFalse(mod.settings_match(base, res))
        res["settings"]["TURBO_LEAN_GIT"] = "/opt/git/bin/git"
        self.assertFalse(mod.settings_match(base, res))

    def test_scrub_replaces_the_longest_root_first_and_never_the_filesystem_root(self):
        mod = load_script()
        text = "failed in /tmp/m1-bench-x/w/cold_0 and /tmp/other, see /"
        self.assertEqual(
            mod.scrub_host_paths(text, [("/tmp", "<tmp>"), ("/tmp/m1-bench-x", "<scratch>"),
                                        ("/", "<root>"), ("", "<empty>")]),
            "failed in <scratch>/w/cold_0 and <tmp>/other, see /")

    def test_binary_is_recorded_relative_to_its_repository_or_by_name(self):
        mod = load_script()
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            b = root / "target" / "release" / "turbo-lean"
            self.assertEqual(mod.binary_record(b, str(root), "s"),
                             {"path": "target/release/turbo-lean", "sha256": "s"})
            self.assertEqual(mod.binary_record(b, None, "s")["path"], "turbo-lean")
            self.assertEqual(mod.binary_record(b, str(root / "elsewhere"), "s")["path"],
                             "turbo-lean")

    def test_results_json_names_no_host_path(self):
        with tempfile.TemporaryDirectory(prefix="m1-pathfree-") as td:
            root = Path(td)
            stub, _ = make_stub_binary(root)
            # The PFR probe's stderr names its working directory and the file it
            # checked: the excerpt recorded from it must name them by placeholder.
            marker = "    print(json.dumps({'error': 'stale imports: import_refresh fail-closed'}))\n"
            default = stub.read_text()
            self.assertIn(marker, default)
            body = default.replace(
                marker,
                "    sys.stderr.write('probe failed in ' + os.getcwd() + ' on '"
                " + ' '.join(a for a in args if a.endswith('.lean'))"
                " + ' home ' + os.environ.get('TURBO_LEAN_HOME', '') + '\\n')\n" + marker)
            out = root / "o.json"
            r = run_bench(root, ["--no-baseline", "--out", str(out)], stub_body=body,
                          env_extra={"TURBO_LEAN_HOME": str(root / "tl-home")})
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            text = out.read_text()
            data = json.loads(text)
            for host_path in {str(root), os.path.realpath(str(root))}:
                self.assertNotIn(host_path, text)
            self.assertNotIn("turbo_lean_repo", data)
            self.assertNotIn("scratch_root", data["settings"])
            self.assertEqual(data["turbo_lean_binary"]["path"], "fake-turbo-lean")
            self.assertTrue(data["settings"]["TURBO_LEAN_GIT"].startswith("<sha256:"))
            self.assertEqual(data["settings"]["TURBO_LEAN_HOME"],
                             self.digest(str(root / "tl-home")))

            def excerpts(node):
                if isinstance(node, dict):
                    for k, v in node.items():
                        if k == "stderr_excerpt":
                            yield v
                        else:
                            yield from excerpts(v)
                elif isinstance(node, list):
                    for v in node:
                        yield from excerpts(v)
            found = list(excerpts(data))
            self.assertTrue(found, "the PFR probe recorded no stderr excerpt")
            for e in found:
                self.assertIn(" on <pfr>/", e)
                self.assertIn(" home <scratch>/", e)


class ForeignSignalGuard(unittest.TestCase):
    """The test run's own guard refuses a process outside its tree and lets its
    children through. Signal 0 only checks that a target exists."""

    def test_a_process_that_left_this_run_is_refused(self):
        # The test starts a process that leaves its tree by a double fork, so
        # init or a subreaper adopts it: to the guard it then looks like any
        # other process of the user. It exits when the test closes `hold_w`.
        hold_r, hold_w = os.pipe()
        report_r, report_w = os.pipe()
        child = os.fork()
        if child == 0:
            try:
                os.close(report_r)
                grandchild = os.fork()
                if grandchild == 0:
                    try:
                        os.close(hold_w)
                        os.read(hold_r, 1)
                    finally:
                        os._exit(0)
                os.write(report_w, f"{grandchild}\n".encode())
            finally:
                os._exit(0)
        os.close(hold_r)
        os.close(report_w)
        os.waitpid(child, 0)
        target = int(os.read(report_r, 32).decode().strip())
        os.close(report_r)
        try:
            REFUSED_SIGNALS.clear()
            self.assertFalse(started_by_this_run(target))
            with self.assertRaises(PermissionError):
                os.kill(target, 0)
            if hasattr(os, "pidfd_open"):
                with self.assertRaises(PermissionError):
                    os.pidfd_open(target)
            self.assertEqual([pid for _, pid in REFUSED_SIGNALS],
                             [target] * (2 if hasattr(os, "pidfd_open") else 1))
        finally:
            REFUSED_SIGNALS.clear()
            os.close(hold_w)

    def test_a_child_is_let_through(self):
        REFUSED_SIGNALS.clear()
        child = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(30)"])
        try:
            os.kill(child.pid, 0)
            if hasattr(os, "pidfd_open"):
                os.close(os.pidfd_open(child.pid))
        finally:
            child.kill()
            child.wait(timeout=10)
        self.assertEqual(REFUSED_SIGNALS, [])


class DaemonCleanup(NoForeignSignals, unittest.TestCase):
    """A workload's daemons end with it, even when `daemon stop` gives up, and
    nothing outside the workload's staging namespace is touched."""

    SLEEPER = b"import time\ntime.sleep(120)\n"

    def spawn(self, staging, command, daemon=True, program=SLEEPER):
        # `python - <command>` reads its program from stdin, so `command` is the
        # first word after the flags, where turbo-lean looks for `serve`.
        env = dict(os.environ, TURBO_LEAN_STAGING_DIR=str(staging))
        if daemon:
            env["TURBO_LEAN_DAEMON"] = "1"
        p = subprocess.Popen([sys.executable, "-", command], env=env, stdin=subprocess.PIPE,
                             stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        self.addCleanup(self.reap, p)
        p.stdin.write(program)
        p.stdin.close()
        return p

    def test_a_daemon_that_ignores_sigterm_is_killed(self):
        mod = load_script()
        with tempfile.TemporaryDirectory(prefix="m1-daemons-") as td:
            staging = Path(td) / "staging"
            bin_path = Path(sys.executable).resolve()
            ready = Path(td) / "ready"
            stubborn = self.spawn(staging, "serve", program=(
                "import signal, time\n"
                "signal.signal(signal.SIGTERM, signal.SIG_IGN)\n"
                f"open({str(ready)!r}, 'w').close()\n"
                "time.sleep(120)\n").encode())
            deadline = time.monotonic() + 10
            while not ready.exists() and time.monotonic() < deadline:
                time.sleep(0.05)
            self.assertTrue(ready.exists(), "the stubborn daemon never started")
            done = subprocess.CompletedProcess([str(bin_path), "daemon", "stop"], 0)
            with mock.patch.object(mod.subprocess, "run", return_value=done), \
                    contextlib.redirect_stderr(io.StringIO()):
                mod.stop_daemons(bin_path, {"TURBO_LEAN_STAGING_DIR": str(staging)})
            self.assertEqual(stubborn.wait(timeout=5), -signal.SIGKILL)

    @staticmethod
    def reap(p):
        if p.poll() is None:
            p.kill()
        p.wait(timeout=10)

    @staticmethod
    def wait_until_listed(mod, staging, bin_path, n):
        deadline = time.monotonic() + 10
        while time.monotonic() < deadline:
            if len(mod.scoped_daemon_processes(staging, bin_path)) >= n:
                return
            time.sleep(0.05)

    def test_a_timed_out_daemon_stop_still_ends_this_namespace_and_only_it(self):
        mod = load_script()
        with tempfile.TemporaryDirectory(prefix="m1-daemons-") as td:
            staging, other = Path(td) / "staging", Path(td) / "other"
            bin_path = Path(sys.executable).resolve()
            ours = self.spawn(staging, "serve")
            theirs = self.spawn(other, "serve")
            not_a_daemon = self.spawn(staging, "check", daemon=False)
            self.wait_until_listed(mod, staging, bin_path, 1)
            err = io.StringIO()
            hung = subprocess.TimeoutExpired([str(bin_path), "daemon", "stop"],
                                             mod.DAEMON_STOP_TIMEOUT_S)
            with mock.patch.object(mod.subprocess, "run", side_effect=hung), \
                    contextlib.redirect_stderr(err):
                mod.stop_daemons(bin_path, {"TURBO_LEAN_STAGING_DIR": str(staging)})
            self.assertEqual(ours.wait(timeout=5), -signal.SIGTERM, err.getvalue())
            self.assertIsNone(theirs.poll(), "another namespace's daemon was signalled")
            self.assertIsNone(not_a_daemon.poll(), "a process that is not a daemon was signalled")
            self.assertIn("daemon stop failed", err.getvalue())
            self.assertEqual(mod.scoped_daemon_processes(staging, bin_path), [])

    def test_a_daemon_stop_that_returns_but_leaves_a_daemon_is_finished_off(self):
        # `daemon stop` matches a server by the name `turbo-lean`, so a renamed
        # binary's daemon survives its own stop; the bench finds it by path.
        mod = load_script()
        with tempfile.TemporaryDirectory(prefix="m1-daemons-") as td:
            staging = Path(td) / "staging"
            bin_path = Path(sys.executable).resolve()
            ours = self.spawn(staging, "serve")
            self.wait_until_listed(mod, staging, bin_path, 1)
            done = subprocess.CompletedProcess([str(bin_path), "daemon", "stop"], 0)
            with mock.patch.object(mod.subprocess, "run", return_value=done), \
                    contextlib.redirect_stderr(io.StringIO()):
                mod.stop_daemons(bin_path, {"TURBO_LEAN_STAGING_DIR": str(staging)})
            self.assertEqual(ours.wait(timeout=5), -signal.SIGTERM)

    def test_the_scope_rule_on_a_fake_proc_tree(self):
        mod = load_script()
        with tempfile.TemporaryDirectory() as td:
            proc = Path(td).resolve() / "proc"
            bin_path = Path(td).resolve() / "bin" / "turbo-lean-renamed"
            staging = "/s/ns"
            ns = f"TURBO_LEAN_STAGING_DIR={staging}"

            def fake(pid, exe, args, env, state="S"):
                d = proc / str(pid)
                d.mkdir(parents=True)
                (d / "exe").symlink_to(exe)
                (d / "cmdline").write_bytes(b"\0".join(a.encode() for a in args) + b"\0")
                (d / "environ").write_bytes(b"\0".join(e.encode() for e in env) + b"\0")
                (d / "stat").write_text(
                    f"{pid} (a b) {state} " + " ".join(["0"] * 18) + f" {1000 + pid} 0\n")

            b = str(bin_path)
            fake(101, b, [b, "--cache-dir", "c", "serve"], [ns, "TURBO_LEAN_DAEMON=1"])
            fake(102, "/x/turbo_zygote_ab", ["w"], [ns])
            fake(103, "/x/turbo_zygote_ab", ["w", "--decl-identity"], [ns])
            fake(104, b, [b, "check", "f.lean"], [ns, "TURBO_LEAN_DAEMON=1"])
            fake(105, b, [b, "serve"], ["TURBO_LEAN_STAGING_DIR=/s/other", "TURBO_LEAN_DAEMON=1"])
            fake(106, "/usr/bin/turbo-lean", ["/usr/bin/turbo-lean", "serve"],
                 [ns, "TURBO_LEAN_DAEMON=1"])
            fake(107, "/x/turbo-zygote", ["w"], ["TURBO_LEAN_STAGING_DIR=/s/ns-oneshot-9-1"])
            fake(108, "/x/turbo_zygote_ab", ["w"], [ns], state="Z")
            fake(109, b + " (deleted)", [b, "serve"], [ns, "TURBO_LEAN_DAEMON=1"])
            fake(110, b, [b, "serve"], [ns])
            fake(111, "/x/turbo_zygote_ab", ["w"], ["TURBO_LEAN_STAGING_DIR=/s/ns2"])
            (proc / "self").mkdir()
            got = mod.scoped_daemon_processes(staging, bin_path, proc_root=proc)
            # Servers of this binary and namespace, its workers and its one-shot
            # sibling's workers; never an audit helper, a non-serve command,
            # another namespace or binary, a zombie, or a server without
            # TURBO_LEAN_DAEMON=1.
            self.assertEqual(got, [(101, "1101"), (102, "1102"), (107, "1107"), (109, "1109")])


class ScratchRemoval(NoForeignSignals, unittest.TestCase):
    """turbo-lean writes read-only directories (closure snapshots) under its
    home; the bench must still remove every trial directory it made."""

    def test_remove_tree_clears_read_only_dirs_and_never_follows_a_symlink(self):
        mod = load_script()
        with tempfile.TemporaryDirectory() as td:
            base = Path(td).resolve()
            outside = base / "outside"
            outside.mkdir()
            (outside / "keep.txt").write_text("k")
            outside.chmod(0o555)
            root = base / "scratch-root"
            store = root / "home" / "closure-realm" / "d0"
            store.mkdir(parents=True)
            (store / "x.ilean").write_text("x")
            store.chmod(0o500)
            store.parent.chmod(0o500)
            (root / "link").symlink_to(outside, target_is_directory=True)
            try:
                mod.remove_tree(root)
                self.assertFalse(root.exists())
                self.assertEqual(stat.S_IMODE(outside.stat().st_mode), 0o555)
                self.assertEqual((outside / "keep.txt").read_text(), "k")
            finally:
                outside.chmod(0o755)

    def test_a_run_whose_checks_write_read_only_dirs_leaves_no_scratch(self):
        with tempfile.TemporaryDirectory(prefix="m1-scratch-") as td:
            root = Path(td)
            stub, _ = make_stub_binary(root)
            marker = "status = 'theorem_verified'\n"
            default = stub.read_text()
            self.assertIn(marker, default)
            body = default.replace(marker, marker + (
                "_snap = os.path.join(os.environ['TURBO_LEAN_HOME'], 'closure-realm', 'd0')\n"
                "if not os.path.isdir(_snap):\n"
                "    os.makedirs(_snap)\n"
                "    open(os.path.join(_snap, 'x.ilean'), 'w').write('x')\n"
                "    os.chmod(_snap, 0o500)\n"
                "    os.chmod(os.path.dirname(_snap), 0o500)\n"), 1)
            tmp = root / "tmp"
            tmp.mkdir()
            r = run_bench(root, ["--no-baseline", "--out", str(root / "o.json")],
                          stub_body=body, env_extra={"TMPDIR": str(tmp)})
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertEqual(sorted(p.name for p in tmp.iterdir()), [])


class OnlyWorkloadsPartialRun(unittest.TestCase):
    def test_only_workloads_marks_skipped_and_partial_run(self):
        with tempfile.TemporaryDirectory(prefix="m1-filter-") as td:
            r = run_bench(Path(td), ["--no-baseline", "--only-workloads",
                                     "batteries_list_lemmas_top",
                                     "--out", str(Path(td) / "o.json")])
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            data = json.loads((Path(td) / "o.json").read_text())
            self.assertEqual(data["workloads"]["batteries_unionfind_top"]["status"],
                             "skipped_by_filter")
            self.assertEqual(data["workloads"]["pfr_more_ruzsa_dist"]["status"],
                             "skipped_by_filter")
            self.assertEqual(data["verdict"]["verdict"], "partial_run")
            self.assertIn("VERDICT: partial_run", r.stdout)

    def test_partial_run_fails_under_strict_comparison(self):
        # --strict-comparison promises "a comparison really happened"; a
        # filtered run never compares, so with a baseline given it must
        # exit 1, not slip through as exit 0.
        mod = load_script()
        with tempfile.TemporaryDirectory(prefix="m1-filter-strict-") as td:
            bp = Path(td) / "b.json"
            bp.write_text(json.dumps(full_valid_baseline(mod)))
            r = run_bench(Path(td), ["--baseline", str(bp), "--strict-comparison",
                                     "--only-workloads", "batteries_list_lemmas_top",
                                     "--out", str(Path(td) / "o.json")])
            self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
            self.assertIn("partial_run", r.stdout)

    def test_rebaseline_with_only_workloads_is_usage_error(self):
        mod = load_script()
        with self.assertRaises(SystemExit) as cm:
            mod.main(["--turbo-lean-bin", "x", "--batteries-dir", "b",
                      "--pfr-dir", "p", "--rebaseline",
                      "--only-workloads", "batteries_list_lemmas_top"])
        self.assertEqual(cm.exception.code, 2)


class SplitTrialsNamedFields(unittest.TestCase):
    def test_split_trials_returns_named_fields(self):
        mod = load_script()
        trial = {"exit_code": 0, "external_wall_ms": 100.0,
                 "json": {"status": "theorem_cache_hit", "peak_rss_mb": 801},
                 "stderr": "", "psi_before": {}, "psi_after": {}}
        ts = mod.Runner.split_trials([trial])
        self.assertEqual(ts.rss_mbs, [801])
        self.assertEqual(ts.failed, 0)
        self.assertEqual(ts.runs, [100.0])
        self.assertEqual(ts.statuses, ["theorem_cache_hit"])


class HostIdLabel(unittest.TestCase):
    def test_host_id_with_label_records_label_as_hostname(self):
        mod = load_script()
        h = mod.host_id("g2a-ro-192c")
        self.assertEqual(h["hostname"], "g2a-ro-192c")
        self.assertEqual(h["machine_label"], "g2a-ro-192c")

    def test_host_id_with_label_keeps_node_name_out_of_host_block(self):
        mod = load_script()
        label = "g2a-ro-192c"
        node = platform.node()
        if not node or node in label:
            self.skipTest("node name empty or a substring of the label")
        self.assertNotIn(node, json.dumps(mod.host_id(label)))

    def test_host_id_without_label_records_node_name(self):
        mod = load_script()
        h = mod.host_id(None)
        self.assertEqual(h["hostname"], platform.node())
        self.assertIsNone(h["machine_label"])


if __name__ == "__main__":
    if sys.argv[1:2] == ["--run-guarded"]:
        # BENCH_CMD: run the bench in this process, which carries the signal
        # guard installed above, as `python3 bench_check_loop.py ARGS` would.
        import runpy
        sys.argv = sys.argv[2:]
        runpy.run_path(sys.argv[0], run_name="__main__")
    else:
        unittest.main(verbosity=2)
