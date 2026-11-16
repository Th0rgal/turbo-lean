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


def fill_workload(mod, baseline, wid, median_ms, rel_spread=0.03):
    baseline["workloads"][wid] = mod.active_workload_result(
        wid, {"cold_no_daemon": {"median_ms": median_ms, "rel_spread": rel_spread,
                                 "trials": 5, "coverage_ratio_min": 0.9998}})


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
        tight = mod.tolerance_ms(1000.0, 0.02)
        loose = mod.tolerance_ms(1000.0, 0.20)
        self.assertGreater(loose, tight)
        self.assertAlmostEqual(tight, 1000.0 * 1.10 + 25.0)
        self.assertAlmostEqual(loose, 1000.0 * (1.0 + 2.0 * 0.20) + 25.0)


class BaselineSchema(unittest.TestCase):
    def test_validate_requires_provenance(self):
        mod = load_script()
        base = sample_baseline(mod)
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
        base = sample_baseline(mod)
        base["workloads"].pop("pfr_more_ruzsa_dist")
        self.assertTrue(mod.validate_baseline(base))


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
        self.assertIn("batteries_list_lemmas_top", verdict["regressions"])

    def test_noisy_workload_within_spread_gate_passes(self):
        # Baseline spread 20% on this mode: a 1.3x median is noise, not a regression.
        base = self._baseline()
        base["workloads"]["batteries_list_lemmas_top"]["modes"]["cold_no_daemon"]["rel_spread"] = 0.20
        res = self._results(scale=1.3)
        verdict = self.mod.compare_run(base, res)
        self.assertEqual(verdict["verdict"], "pass")

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


class EndToEnd(unittest.TestCase):
    """Drive the full script against a stub turbo-lean binary."""

    def _stub_binary(self, root: Path):
        stub = root / "fake-turbo-lean"
        stub.write_text(
            "#!/usr/bin/env python3\n"
            "import json, os, sys, time\n"
            "args = sys.argv[1:]\n"
            "time.sleep(0.05)\n"
            "out = {'status': 'theorem_verified', 'decl': 'd', 'elapsed_ms': 50,\n"
            "       'phase_timings': {'wall_ms': 50.0, 'phase_sum_ms': 49.0,\n"
            "                         'phase_covered_ms': 49.0, 'phase_overlap_ms': 0.0,\n"
            "                         'coverage_ratio': 0.98,\n"
            "                         'phases_ms': {'setup': 10.0, 'elaboration': 39.0}}}\n"
            "if os.environ.get('FAKE_PFR_FAIL') and any('--no-auto-worktree-link' in a for a in args):\n"
            "    out = {'error': 'import_refresh_fail_closed: stale imports'}\n"
            "    print(json.dumps(out)); sys.exit(1)\n"
            "print(json.dumps(out)); sys.exit(0)\n"
        )
        stub.chmod(0o755)
        return stub

    def _fake_projects(self, root: Path):
        bats = root / "batteries"
        (bats / "Batteries" / "Data").mkdir(parents=True)
        (bats / "Batteries" / "Data" / "Lemmas.lean").write_text(
            "theorem dummy : True := by trivial\n")
        pfr = root / "pfr"
        (pfr / "PFR").mkdir(parents=True)
        (pfr / "PFR" / "MoreRuzsaDist.lean").write_text(
            "lemma rdist_of_neg_le : True := by trivial\n")
        return bats, pfr

    def test_full_run_and_comparison(self):
        mod = load_script()
        with tempfile.TemporaryDirectory(prefix="m1-bench-test-") as td:
            root = Path(td)
            stub = self._stub_binary(root)
            bats, pfr = self._fake_projects(root)
            out = root / "run.json"
            # Fake projects are not git repos: rev pinning must be skipped explicitly.
            r1 = subprocess.run(
                [sys.executable, str(SCRIPT), "--turbo-lean-bin", str(stub),
                 "--batteries-dir", str(bats), "--pfr-dir", str(pfr),
                 "--trials", "2", "--warmup", "0", "--skip-rev-check",
                 "--machine-label", "lab-node-1", "--out", str(out),
                 "--no-daemon-assume", "--no-baseline"],
                capture_output=True, text=True, timeout=300)
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
            r2 = subprocess.run(
                [sys.executable, str(SCRIPT), "--turbo-lean-bin", str(stub),
                 "--batteries-dir", str(bats), "--pfr-dir", str(pfr),
                 "--trials", "2", "--warmup", "0", "--skip-rev-check",
                 "--machine-label", "lab-node-1", "--out", str(root / "run2.json"),
                 "--no-daemon-assume", "--baseline", str(out)],
                capture_output=True, text=True, timeout=300)
            self.assertEqual(r2.returncode, 0, r2.stdout + r2.stderr)
            data2 = json.loads((root / "run2.json").read_text())
            self.assertEqual(data2["verdict"]["verdict"], "pass")
            # Cross-host comparison must be flagged, never a pass.
            r3 = subprocess.run(
                [sys.executable, str(SCRIPT), "--turbo-lean-bin", str(stub),
                 "--batteries-dir", str(bats), "--pfr-dir", str(pfr),
                 "--trials", "2", "--warmup", "0", "--skip-rev-check",
                 "--machine-label", "other-runner", "--out", str(root / "run3.json"),
                 "--no-daemon-assume", "--baseline", str(out)],
                capture_output=True, text=True, timeout=300)
            self.assertEqual(r3.returncode, 0, r3.stdout + r3.stderr)
            data3 = json.loads((root / "run3.json").read_text())
            self.assertEqual(data3["verdict"]["verdict"], "comparison_skipped_host_mismatch")


if __name__ == "__main__":
    unittest.main(verbosity=2)
