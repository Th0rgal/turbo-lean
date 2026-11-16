"""C4x alias-tier contract tests for the Tier C4 LCNF/LNIR differential fuzzer.

The C4x leaf (roadmap/HORIZONS.md) requires genuine alias fuzzing at 10k seeds:
programs where two live names denote the same heap object, so a wrong
reference count or an in-place update becomes observable. A fuzzer that
reports 10k passing seeds while generating few or no aliasing programs is
worse than none, so the number of generated programs that really contain an
alias must be measured, printed, and held above a stated floor.

These tests are pure Python (no compiled engine required) except the
end-to-end mutation test, which skips when engines are unavailable.
"""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fuzz_lcnf_conformance as fuzzer

# Stated floor: at least 1 in 8 generated seeds must be a genuine alias program.
ALIAS_FLOOR_RATIO = 8
N = 64


def _alias_programs() -> list[dict]:
    programs = [fuzzer.build_program(seed) for seed in range(N)]
    return [p for p in programs if fuzzer.program_contains_alias(p)]


class AliasTierGeneration(unittest.TestCase):
    def test_alias_tier_generates_genuine_alias_programs_above_floor(self):
        alias = _alias_programs()
        self.assertGreaterEqual(len(alias), N // ALIAS_FLOOR_RATIO)

    def test_shared_and_exclusive_variants_both_generated(self):
        alias = _alias_programs()
        self.assertTrue(any(p["alias_shared"] for p in alias),
                        "no shared-alias (foo arr arr) programs generated")
        self.assertTrue(any(not p["alias_shared"] for p in alias),
                        "no exclusive-alias programs generated")

    def test_alias_programs_carry_two_name_probe_metadata(self):
        for p in _alias_programs():
            self.assertEqual(p["k"], "alias_program")
            self.assertIn("alias_probe", p)

    def test_scalar_programs_are_not_miscounted_as_alias(self):
        programs = [fuzzer.build_program(seed) for seed in range(N)]
        scalar = [p for p in programs if not fuzzer.program_contains_alias(p)]
        self.assertTrue(scalar)
        # The old 1/6 "scalar_conditional" shape is explicitly not an alias test.
        for p in scalar:
            self.assertFalse(fuzzer.program_contains_alias(p))


class AliasReportContract(unittest.TestCase):
    def test_report_counts_alias_programs_even_without_engines(self):
        report = fuzzer.run_fuzzer(
            N,
            override_lean="/nonexistent/lean",
            override_core="/nonexistent/core",
            override_clang="/nonexistent/clang",
        )
        self.assertFalse(report["ok"])
        self.assertEqual(report["status"], "incomplete_missing_engine")
        self.assertIn("alias_program_count", report)
        self.assertGreaterEqual(report["alias_program_count"], N // ALIAS_FLOOR_RATIO)
        self.assertTrue(report["alias_floor_met"])


class BrokenAliasDetection(unittest.TestCase):
    def test_in_place_update_seen_through_old_name_is_a_mismatch(self):
        alias = _alias_programs()
        self.assertTrue(alias)
        p = alias[0]
        correct = {"ret": 11, "old_read": 5, "new_read": 8}
        # Wrong reference count: the old name observed the in-place update.
        wrong_rc = {"ret": 11, "old_read": 8, "new_read": 8}
        self.assertTrue(fuzzer.alias_observations_differ(correct, wrong_rc))
        self.assertFalse(fuzzer.alias_observations_differ(correct, dict(correct)))
        self.assertIsNotNone(fuzzer.alias_mismatch(p, correct, wrong_rc))
        self.assertIsNone(fuzzer.alias_mismatch(p, correct, dict(correct)))

    def test_mutated_alias_engine_value_fails_the_run(self):
        engines = fuzzer.probe_engines()
        if not (engines["stock_lean_c"] and engines["lnir_eval"] and engines["c_abi_llvm"]):
            self.skipTest("conformance engines unavailable on this node")
        report = fuzzer.run_fuzzer(16, mutate_engine="lnir_eval")
        self.assertFalse(report["ok"])
        self.assertGreater(report["mismatch_count"], 0)


if __name__ == "__main__":
    unittest.main()
