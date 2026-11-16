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
    pfr = root / "pfr"
    (pfr / "PFR").mkdir(parents=True, exist_ok=True)
    (pfr / "PFR" / "MoreRuzsaDist.lean").write_text(
        "lemma rdist_of_neg_le : True := by trivial\n")
    return bats, pfr


def run_bench(root, extra, stub_body=None, env_extra=None):
    stub, gitstub = make_stub_binary(root, stub_body)
    bats, pfr = make_fake_projects(root)
    env = dict(os.environ, TURBO_LEAN_GIT=str(gitstub),
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
                  "TURBO_LEAN_ALLOWED_UNSAFE": "*", "TURBO_LEAN_ALLOWED_IMPLEMENTED_BY": "*"},
        workloads={w["id"]: mod.empty_workload_result(w) for w in mod.WORKLOADS},
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
        res = mod.empty_run_result(mod.WORKLOADS, trials=5)
        res["host"] = dict(sample_baseline(mod)["host"], hostname=host)
        res["settings"] = sample_baseline(mod)["settings"]
        res["turbo_lean_commit"] = sample_baseline(mod)["turbo_lean_commit"]
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
        res = mod.empty_run_result(mod.WORKLOADS, trials=5)
        res["host"] = dict(base["host"])
        res["settings"] = dict(base["settings"])
        res["settings"]["TURBO_LEAN_HOME"] = "/somewhere/else"
        res["turbo_lean_commit"] = base["turbo_lean_commit"]
        for w in mod.WORKLOADS:
            if w["expected_status"] == "blocked":
                res["workloads"][w["id"]] = mod.blocked_workload_result(1, "x", 6000.0)
            else:
                fill_workload(mod, res, w["id"], 1000.0)
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
            # Same-host comparison of two identical runs must pass.
            r2 = self._run_bench(root, ["--machine-label", "lab-node-1",
                                        "--out", str(root / "run2.json"),
                                        "--baseline", str(out)])
            self.assertEqual(r2.returncode, 0, r2.stdout + r2.stderr)
            data2 = json.loads((root / "run2.json").read_text())
            self.assertEqual(data2["verdict"]["verdict"], "pass")
            # Cross-host comparison must be flagged, never a pass.
            r3 = self._run_bench(root, ["--machine-label", "other-runner",
                                        "--out", str(root / "run3.json"),
                                        "--baseline", str(out)])
            self.assertEqual(r3.returncode, 0, r3.stdout + r3.stderr)
            data3 = json.loads((root / "run3.json").read_text())
            self.assertEqual(data3["verdict"]["verdict"], "comparison_skipped_host_mismatch")


if __name__ == "__main__":
    unittest.main(verbosity=2)
