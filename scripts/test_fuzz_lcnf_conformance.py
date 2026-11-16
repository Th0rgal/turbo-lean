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
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fuzz_lcnf_conformance as fuzzer

# Stated floor: at least 1 in 8 generated seeds must be a genuine alias program.
ALIAS_FLOOR_RATIO = 8
N = 64


def _alias_programs() -> list[dict]:
    programs = [fuzzer.build_program(seed) for seed in range(N)]
    return [p for p in programs if fuzzer.program_contains_alias(p)]


class AliasSeedRuleExactness(unittest.TestCase):
    """The allocation rule itself, pinned exactly - a floor cannot catch a
    regression that still clears it (e.g. 1 seed in 7 instead of 1 in 6
    yields 1428 >= 1250 at 10k seeds), so the exact seed set, the shared and
    exclusive split, and the boundary seeds are asserted against the rule
    computed independently here (not by calling the generator's constants).
    """

    NS = 10_000

    @staticmethod
    def _expected_sets(n: int) -> tuple[set[int], set[int]]:
        # Rule (C4x): every seed > 3 with seed % 6 == 0 takes the alias tier;
        # shared when seed // 6 is even, exclusive when odd.
        expected_all = {s for s in range(4, n) if s % 6 == 0}
        expected_shared = {s for s in expected_all if (s // 6) % 2 == 0}
        expected_exclusive = expected_all - expected_shared
        return expected_shared, expected_exclusive

    def _observed(self, n: int) -> tuple[set[int], set[int]]:
        observed_shared: set[int] = set()
        observed_exclusive: set[int] = set()
        for s in range(n):
            p = fuzzer.build_program(s)
            if fuzzer.program_contains_alias(p):
                (observed_shared if p["alias_shared"] else observed_exclusive).add(s)
        return observed_shared, observed_exclusive

    def test_exact_alias_seed_set_and_shared_exclusive_split_at_10k(self):
        exp_sh, ex_ex = self._expected_sets(self.NS)
        obs_sh, obs_ex = self._observed(self.NS)
        self.assertEqual(obs_sh, exp_sh)
        self.assertEqual(obs_ex, ex_ex)
        # Reviewer's independent count: 1,666 of 10,000 (833 shared / 833 exclusive).
        self.assertEqual(len(obs_sh) + len(obs_ex), 1666)
        self.assertEqual(len(obs_sh), 833)
        self.assertEqual(len(obs_ex), 833)

    def test_alias_boundary_seeds(self):
        for s in (0, 1, 2, 3, 4, 5, 7, 11, 9997, 9998, 9999):
            self.assertFalse(fuzzer.program_contains_alias(fuzzer.build_program(s)), f"seed {s}")
        self.assertFalse(fuzzer.build_program(6)["alias_shared"], "6//6==1 odd -> exclusive")
        self.assertTrue(fuzzer.build_program(12)["alias_shared"], "12//6==2 even -> shared")
        self.assertFalse(fuzzer.build_program(9990)["alias_shared"], "1665 odd -> exclusive")
        self.assertTrue(fuzzer.build_program(9996)["alias_shared"], "1666 even -> shared")

    def test_mutated_allocation_rule_is_detected(self):
        """A wrong distribution must fail the exact assertions above."""
        expected_shared, expected_exclusive = self._expected_sets(200)
        with mock.patch.object(fuzzer, "ALIAS_SEED_MOD", 7):
            obs_sh, obs_ex = self._observed(200)
        self.assertNotEqual(obs_sh | obs_ex, expected_shared | expected_exclusive,
                            "a 1-in-7 mutant went undetected by the exact seed-set assertion")
        self.assertNotEqual(obs_sh, expected_shared)
        self.assertNotEqual(obs_ex, expected_exclusive)
        self.assertEqual(obs_sh | obs_ex, {s for s in range(4, 200) if s % 7 == 0 and s > 3})


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


class ReceiptsContract(unittest.TestCase):
    """P0 callers read run_fuzzer()["receipts"] as a dict (test_p0_trust_boundary.py:359)."""

    def test_receipts_merge_is_a_dict_with_totals_even_for_many_batches(self):
        scalar = [
            {"lean_source_sha256": "a" * 64, "lnir_eval_executed_decls": 256,
             "symbolic_tv_passed_decls": 256, "stock_runtime": "stock lean -c + leanc (full generated C, no replacements)"},
            {"lean_source_sha256": "b" * 64, "lnir_eval_executed_decls": 170,
             "symbolic_tv_passed_decls": 170, "stock_runtime": "stock lean -c + leanc (full generated C, no replacements)"},
        ]
        alias = [
            {"lean_source_sha256": "c" * 64, "lnir_eval_executed_decls": 288,
             "symbolic_tv_passed_decls": 288, "alias_llvm_fail_closed": True},
        ]
        merged = fuzzer.merge_fuzz_receipts(scalar, alias)
        self.assertIsInstance(merged, dict)
        self.assertEqual(merged["lnir_eval_executed_decls"], 256 + 170 + 288)
        self.assertEqual(merged["symbolic_tv_passed_decls"], 256 + 170 + 288)
        self.assertIsInstance(merged["batch_receipts"], list)
        self.assertEqual(len(merged["batch_receipts"]), 3)

    def test_receipts_merge_tolerates_patched_empty_batches(self):
        merged = fuzzer.merge_fuzz_receipts([{}, {}], [])
        self.assertIsInstance(merged, dict)
        self.assertEqual(merged["lnir_eval_executed_decls"], 0)

    def test_run_fuzzer_report_receipts_stay_a_dict(self):
        engines = fuzzer.probe_engines()
        if not (engines["stock_lean_c"] and engines["lnir_eval"] and engines["c_abi_llvm"]):
            self.skipTest("conformance engines unavailable on this node")
        report = fuzzer.run_fuzzer(12)
        self.assertTrue(report["ok"], report)
        receipts = report["receipts"]
        self.assertIsInstance(receipts, dict)
        self.assertGreaterEqual(receipts["lnir_eval_executed_decls"], 12)


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
