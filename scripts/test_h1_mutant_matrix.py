#!/usr/bin/env python3
"""W2-H1.4: tests for `scripts/h1_mutant_matrix.py` and the `lcnf_coverage.py` coverage ratchet.

Covers the passing matrix on this tree and fail-closed negatives: a tampered `SpecLocked.lean`,
a mutant missing from the source or the audit, a mutant using `sorryAx` / `Lean.trustCompiler`,
an audit below the theorem floor, and ratchet regressions (proved share down, `lowered_unproved`
up, stale committed summary). The real kernel audit is exercised when `lean-native-core` is built.
"""

import copy
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent
ROOT = SCRIPTS_DIR.parent
sys.path.insert(0, str(SCRIPTS_DIR))

import h1_mutant_matrix as mm  # noqa: E402
import lcnf_coverage as cov  # noqa: E402

MATRIX_PY = SCRIPTS_DIR / "h1_mutant_matrix.py"
CORE_BIN = Path(os.environ.get("CORE_BIN", ROOT / "lean" / ".lake" / "build" / "bin" / "lean-native-core"))
STANDARD = ["propext", "Classical.choice", "Quot.sound"]


def good_audit():
    results = [
        {
            "theoremName": f"{mm.H1_NAMESPACE}.{name}",
            "existsInEnv": True,
            "passed": True,
            "axiomsUsed": list(STANDARD),
            "forbiddenFound": [],
            "nonStandardFound": [],
        }
        for name, *_ in mm.H1_KILLED_MUTANTS
    ]
    return {"passed": True, "theoremsAudited": mm.AUDITED_THEOREM_FLOOR, "forbiddenAxiomsFound": [], "results": results}


def committed_ratchet():
    return json.loads(cov.RATCHET_FILE.read_text(encoding="utf-8"))


def run_matrix(*args, stdin=None):
    return subprocess.run(
        [sys.executable, str(MATRIX_PY), *args], input=stdin, capture_output=True, text=True, timeout=590
    )


class MutantMatrixPasses(unittest.TestCase):
    def test_spec_locked_matches_pin(self):
        self.assertEqual(mm.check_spec_lock(ROOT), [])
        self.assertEqual(mm.sha256_file(ROOT / mm.SPEC_LOCKED_PATH), mm.SPEC_LOCKED_SHA256)

    def test_matrix_meets_floor_and_every_mutant_is_declared(self):
        self.assertGreaterEqual(len({m[0] for m in mm.H1_KILLED_MUTANTS}), mm.MIN_KILLED_MUTANTS)
        self.assertEqual(mm.check_mutant_sources(ROOT), [])

    def test_clean_audit_passes(self):
        self.assertEqual(mm.check_axiom_audit(good_audit()), [])
        proc = run_matrix("--audit-json", "-", stdin=json.dumps(good_audit()))
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertIn("[OK] H1 mutant matrix", proc.stdout)

    @unittest.skipUnless(CORE_BIN.is_file() and os.access(CORE_BIN, os.X_OK), "lean-native-core not built")
    def test_real_kernel_audit_passes(self):
        proc = run_matrix("--core-bin", str(CORE_BIN), "--json")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        out = json.loads(proc.stdout)
        self.assertTrue(out["ok"], out["errors"])
        self.assertGreaterEqual(out["theorems_audited"], mm.AUDITED_THEOREM_FLOOR)

    def test_committed_ratchet_summary_holds(self):
        doc = committed_ratchet()
        self.assertEqual(cov.check_coverage_ratchet(doc, copy.deepcopy(doc)), [])
        self.assertEqual(doc["mutant_kill_matrix"]["count"], len(mm.H1_KILLED_MUTANTS))
        self.assertEqual(doc["spec_locked"]["pinned_sha256"], mm.SPEC_LOCKED_SHA256)
        self.assertLessEqual(doc["lcnf_constructor_matrix"]["lowered_unproved"], 2)
        self.assertEqual(set(doc["corpora"]), {"batteries", "c1", "c2"})


class MutantMatrixFailsClosed(unittest.TestCase):
    def _tree_copy(self):
        tmp = Path(tempfile.mkdtemp(prefix="h1-matrix-"))
        self.addCleanup(shutil.rmtree, tmp)
        for rel in {mm.SPEC_LOCKED_PATH, *(m[1] for m in mm.H1_KILLED_MUTANTS)}:
            (tmp / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / rel, tmp / rel)
        return tmp

    def test_tampered_spec_locked_exits_nonzero(self):
        tmp = self._tree_copy()
        with open(tmp / mm.SPEC_LOCKED_PATH, "a", encoding="utf-8") as fh:
            fh.write("\n-- drift\n")
        self.assertTrue(any("drifted" in e for e in mm.check_spec_lock(tmp)))
        proc = run_matrix("--root", str(tmp), "--audit-json", "-", stdin=json.dumps(good_audit()))
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("drifted", proc.stderr)

    def test_missing_spec_locked_exits_nonzero(self):
        tmp = self._tree_copy()
        (tmp / mm.SPEC_LOCKED_PATH).unlink()
        proc = run_matrix("--root", str(tmp), "--audit-json", "-", stdin=json.dumps(good_audit()))
        self.assertNotEqual(proc.returncode, 0)

    def test_mutant_removed_from_source_exits_nonzero(self):
        tmp = self._tree_copy()
        name, rel, *_ = mm.H1_KILLED_MUTANTS[-1]
        path = tmp / rel
        path.write_text(path.read_text(encoding="utf-8").replace(f"theorem {name}", f"theorem {name}_gone"))
        self.assertTrue(any(name in e for e in mm.check_mutant_sources(tmp)))
        proc = run_matrix("--root", str(tmp), "--audit-json", "-", stdin=json.dumps(good_audit()))
        self.assertNotEqual(proc.returncode, 0)

    def test_matrix_below_floor_fails(self):
        errs = mm.check_mutant_sources(ROOT, mm.H1_KILLED_MUTANTS[: mm.MIN_KILLED_MUTANTS - 1])
        self.assertTrue(any("floor" in e for e in errs))

    def test_mutant_missing_from_audit_exits_nonzero(self):
        audit = good_audit()
        audit["results"].pop()
        self.assertTrue(any("missing from the axiom audit" in e for e in mm.check_axiom_audit(audit)))
        proc = run_matrix("--audit-json", "-", stdin=json.dumps(audit))
        self.assertNotEqual(proc.returncode, 0)

    def test_forbidden_axioms_on_a_mutant_fail(self):
        for axiom in ("sorryAx", "Lean.trustCompiler"):
            audit = good_audit()
            audit["results"][0]["axiomsUsed"].append(axiom)
            self.assertTrue(mm.check_axiom_audit(audit), axiom)
            audit = good_audit()
            audit["results"][0]["forbiddenFound"] = [axiom]
            self.assertTrue(mm.check_axiom_audit(audit), axiom)

    def test_audit_level_failures(self):
        for mutate in (
            lambda d: d.update(passed=False),
            lambda d: d.update(theoremsAudited=mm.AUDITED_THEOREM_FLOOR - 1),
            lambda d: d.update(theoremsAudited=True),
            lambda d: d.update(forbiddenAxiomsFound=["sorryAx"]),
            lambda d: d.pop("results"),
            lambda d: d["results"][0].update(existsInEnv=False),
        ):
            audit = good_audit()
            mutate(audit)
            self.assertTrue(mm.check_axiom_audit(audit), audit)
        self.assertTrue(mm.check_axiom_audit([]))

    def test_malformed_audit_json_exits_nonzero(self):
        proc = run_matrix("--audit-json", "-", stdin="not json")
        self.assertNotEqual(proc.returncode, 0)
        self.assertNotEqual(run_matrix().returncode, 0)


class CoverageRatchetFailsClosed(unittest.TestCase):
    def _errors_after(self, mutate):
        doc = committed_ratchet()
        live = copy.deepcopy(doc)
        mutate(live)
        return cov.check_coverage_ratchet(live, doc)

    def test_lowered_unproved_increase_fails(self):
        def bump(d):
            d["lcnf_constructor_matrix"]["lowered_unproved"] += 1
        self.assertTrue(any("matrix lowered_unproved" in e for e in self._errors_after(bump)))

    def test_proved_share_drop_fails(self):
        for label in ("batteries", "c1", "c2"):
            def drop(d, label=label):
                d["corpora"][label]["proved"] -= 1
                d["corpora"][label]["rejected"] += 1
            self.assertTrue(any(f"`{label}` proved share" in e for e in self._errors_after(drop)), label)

    def test_corpus_lowered_unproved_increase_fails(self):
        def bump(d):
            d["corpora"]["c1"]["lowered_unproved"] += 1
        self.assertTrue(any("`c1` lowered_unproved" in e for e in self._errors_after(bump)))

    def test_matrix_proved_drop_fails(self):
        def drop(d):
            d["lcnf_constructor_matrix"]["proved"] -= 1
        self.assertTrue(any("matrix proved" in e for e in self._errors_after(drop)))

    def test_unmeasured_corpus_fails(self):
        def unmeasure(d):
            d["corpora"]["batteries"] = {
                "source": d["corpora"]["batteries"]["source"],
                "measurement_source": "not_measured",
                "ratchet": d["corpora"]["batteries"]["ratchet"],
            }
        self.assertTrue(any("not measured" in e for e in self._errors_after(unmeasure)))

    def test_spec_drift_and_small_matrix_fail(self):
        def drift(d):
            d["spec_locked"]["actual_sha256"] = "0" * 64
        self.assertTrue(any("drifted" in e for e in self._errors_after(drift)))

        def shrink(d):
            d["mutant_kill_matrix"]["count"] = d["mutant_kill_matrix"]["floor"] - 1
        self.assertTrue(any("mutant kill matrix" in e for e in self._errors_after(shrink)))

    def test_stale_or_missing_committed_summary_fails(self):
        doc = committed_ratchet()
        stale = copy.deepcopy(doc)
        stale["corpora"]["c1"]["proved_share"] = 0.0
        self.assertTrue(any("differs" in e for e in cov.check_coverage_ratchet(doc, stale)))
        self.assertTrue(any("Missing committed" in e for e in cov.check_coverage_ratchet(doc, None)))

    def test_improvement_within_bounds_only_flags_stale_summary(self):
        doc = committed_ratchet()
        live = copy.deepcopy(doc)
        live["corpora"]["c1"]["proved"] += 1
        live["corpora"]["c1"]["lowered_unproved"] -= 1
        errs = cov.check_coverage_ratchet(live, doc)
        self.assertEqual(len(errs), 1, errs)
        self.assertIn("differs", errs[0])


if __name__ == "__main__":
    unittest.main(verbosity=2)
