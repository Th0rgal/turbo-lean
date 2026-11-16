#!/usr/bin/env python3
"""Contract tests for `scripts/bench_check_loop.py` (M1 pinned benchmark).

Run: python3 scripts/test_bench_check_loop.py
No Lean toolchain or turbo-lean build required: the end-to-end case drives the
script with a stub binary that emulates `check --json`.
"""

from __future__ import annotations

import importlib.util
import json
import math
import os
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parent / "bench_check_loop.py"


def load_script():
    spec = importlib.util.spec_from_file_location("bench_check_loop", SCRIPT)
    mod = importlib.util.module_from_spec(spec)
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
    cmd = [sys.executable, str(SCRIPT), "--turbo-lean-bin", str(stub),
           "--batteries-dir", str(bats), "--pfr-dir", str(pfr),
           "--trials", "2", "--warmup", "0", "--skip-rev-check", "--allow-busy-node"] + extra
    return subprocess.run(cmd, capture_output=True, text=True, timeout=600, env=env)


def sample_baseline(mod, **overrides):
    return mod.make_baseline(
        turbo_lean_commit="8a1d67dba051f59440c91df828584657efd12605",
        host={"hostname": "bench-host", "machine_label": "lab-node-1",
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
        verdict = self.mod.compare_run(self._baseline(), self._results(host="other-runner"))
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
            base = full_valid_baseline(mod)
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
            base["host"]["hostname"] = o0["host"]["hostname"]
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
                [sys.executable, str(SCRIPT), "--turbo-lean-bin", str(Path(td) / "fake-turbo-lean"),
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
            cmd = [sys.executable, str(SCRIPT), "--turbo-lean-bin", str(stub),
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

    def test_workload_rev_mismatch_refuses_comparison_nonzero_and_prints_both(self):
        mod = load_script()
        with tempfile.TemporaryDirectory(prefix="m1-rev-mis-") as td:
            r0 = run_bench(Path(td), ["--no-baseline", "--out", str(Path(td) / "o0.json")])
            self.assertEqual(r0.returncode, 0, r0.stdout + r0.stderr)
            o0 = json.loads((Path(td) / "o0.json").read_text())
            base = full_valid_baseline(mod)
            base["host"]["hostname"] = o0["host"]["hostname"]
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
            base["host"]["hostname"] = o0["host"]["hostname"]
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
            base["host"]["hostname"] = o0["host"]["hostname"]
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
            base["host"]["hostname"] = o0["host"]["hostname"]
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


if __name__ == "__main__":
    unittest.main(verbosity=2)
