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
import os
import sys
import tempfile
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


class ClangResolutionOrder(unittest.TestCase):
    """Environment portability: TURBO_LEAN_CLANG wins over everything; a usable
    system clang (banner >= LLVM 16, or passing the `memory(none)` IR probe)
    wins next, because it carries the sanitizer runtimes; the pinned toolchain's
    bundled clang (derived from lean/lean-toolchain, honoring ELAN_HOME) is the
    fallback for hosts whose system clang predates the IR the toolchain emits.
    Pure resolution-order tests; no second toolchain required."""

    @staticmethod
    def _fake_clang(dirpath):
        p = Path(dirpath) / "clang"
        p.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        p.chmod(0o755)
        return p

    def test_repo_pinned_toolchain_reads_lean_toolchain_file(self):
        pin = fuzzer.repo_pinned_toolchain()
        on_disk = (fuzzer.ROOT / "lean" / "lean-toolchain").read_text(encoding="utf-8").strip()
        self.assertEqual(pin, on_disk)
        self.assertTrue(pin)

    def test_elan_toolchain_dir_name_mangles_slash_and_colon(self):
        self.assertEqual(
            fuzzer.elan_toolchain_dir_name("leanprover/lean4:v4.35.0"),
            "leanprover--lean4---v4.35.0",
        )

    def test_elan_home_is_first_toolchain_clang_candidate(self):
        with mock.patch.dict(os.environ, {"ELAN_HOME": "/custom/elan-home"}):
            cands = fuzzer.pinned_toolchain_clang_candidates()
        pin_dir = fuzzer.elan_toolchain_dir_name(fuzzer.repo_pinned_toolchain())
        self.assertEqual(
            cands[0], str(Path("/custom/elan-home") / "toolchains" / pin_dir / "bin" / "clang")
        )
        self.assertIn(
            str(Path.home() / ".elan" / "toolchains" / pin_dir / "bin" / "clang"), cands
        )

    def test_turbo_lean_clang_override_has_highest_precedence(self):
        with tempfile.TemporaryDirectory(prefix="tl-clang-override-") as tmp:
            fake = self._fake_clang(tmp)
            with mock.patch.dict(os.environ, {"TURBO_LEAN_CLANG": str(fake)}):
                self.assertEqual(fuzzer.find_clang_binary(), str(fake))

    @staticmethod
    def _system_clang_present():
        import shutil as _shutil

        return any(
            c and Path(c).is_file() for c in ("/usr/bin/clang", _shutil.which("clang"))
        )

    def test_system_clang_preferred_over_bundled_when_banner_is_new_enough(self):
        if not self._system_clang_present():
            self.skipTest("no system clang on this node")
        with tempfile.TemporaryDirectory(prefix="tl-elan-home-") as tmp:
            pin = fuzzer.repo_pinned_toolchain()
            bindir = Path(tmp) / "toolchains" / fuzzer.elan_toolchain_dir_name(pin) / "bin"
            bindir.mkdir(parents=True)
            fake_bundled = self._fake_clang(bindir)
            with mock.patch.dict(os.environ, {"ELAN_HOME": tmp}):
                os.environ.pop("TURBO_LEAN_CLANG", None)
                with mock.patch.object(fuzzer, "clang_version_major", return_value=16):
                    got = fuzzer.find_clang_binary()
        self.assertIsNotNone(got)
        self.assertNotEqual(
            got, str(fake_bundled), "a usable system clang must win over the bundled clang"
        )

    def test_bundled_toolchain_clang_is_the_fallback_when_system_unusable(self):
        with tempfile.TemporaryDirectory(prefix="tl-elan-home-") as tmp:
            pin = fuzzer.repo_pinned_toolchain()
            bindir = Path(tmp) / "toolchains" / fuzzer.elan_toolchain_dir_name(pin) / "bin"
            bindir.mkdir(parents=True)
            fake_bundled = self._fake_clang(bindir)
            with mock.patch.dict(os.environ, {"ELAN_HOME": tmp}):
                os.environ.pop("TURBO_LEAN_CLANG", None)
                with mock.patch.object(
                    fuzzer, "clang_version_major", return_value=15
                ), mock.patch.object(
                    fuzzer, "clang_can_lower_pinned_ir", return_value=False
                ):
                    self.assertEqual(fuzzer.find_clang_binary(), str(fake_bundled))

    def test_old_banner_system_clang_accepted_when_the_ir_probe_passes(self):
        # Apple clang 15 is LLVM 16 and a ccache wrapper may print no parsable
        # banner: the functional probe, not the banner, decides.
        if not self._system_clang_present():
            self.skipTest("no system clang on this node")
        with mock.patch.dict(os.environ, {}):
            os.environ.pop("TURBO_LEAN_CLANG", None)
            with mock.patch.object(
                fuzzer, "pinned_toolchain_clang_candidates", return_value=[]
            ), mock.patch.object(
                fuzzer, "clang_version_major", return_value=15
            ), mock.patch.object(
                fuzzer, "clang_can_lower_pinned_ir", return_value=True
            ):
                self.assertIsNotNone(fuzzer.find_clang_binary())

    def test_unparsable_banner_system_clang_decided_by_the_ir_probe(self):
        if not self._system_clang_present():
            self.skipTest("no system clang on this node")
        with mock.patch.dict(os.environ, {}):
            os.environ.pop("TURBO_LEAN_CLANG", None)
            with mock.patch.object(
                fuzzer, "pinned_toolchain_clang_candidates", return_value=[]
            ), mock.patch.object(
                fuzzer, "clang_version_major", return_value=None
            ), mock.patch.object(
                fuzzer, "clang_can_lower_pinned_ir", return_value=True
            ):
                self.assertIsNotNone(fuzzer.find_clang_binary())

    def test_system_clang_rejected_when_banner_old_and_probe_fails(self):
        with mock.patch.dict(os.environ, {}):
            os.environ.pop("TURBO_LEAN_CLANG", None)
            with mock.patch.object(
                fuzzer, "pinned_toolchain_clang_candidates", return_value=[]
            ), mock.patch.object(
                fuzzer, "clang_version_major", return_value=15
            ), mock.patch.object(
                fuzzer, "clang_can_lower_pinned_ir", return_value=False
            ):
                self.assertIsNone(fuzzer.find_clang_binary())

    def test_ir_probe_result_is_cached_per_path(self):
        calls = []

        class _Res:
            returncode = 1
            stdout = ""
            stderr = ""

        def fake_run(cmd, **kw):
            calls.append([str(a) for a in cmd])
            return _Res()

        fuzzer._clang_ir_probe_cache.clear()
        try:
            with mock.patch.object(fuzzer.subprocess, "run", side_effect=fake_run):
                self.assertFalse(fuzzer.clang_can_lower_pinned_ir("/usr/bin/clang"))
                self.assertFalse(fuzzer.clang_can_lower_pinned_ir("/usr/bin/clang"))
        finally:
            fuzzer._clang_ir_probe_cache.clear()
        self.assertEqual(len(calls), 1, "the IR probe must run once per clang path")

    def test_toolchain_version_token(self):
        self.assertEqual(
            fuzzer.toolchain_version_token("leanprover/lean4:v4.35.0"), "4.35.0"
        )
        # A missing/empty pin yields None, never "": an empty token is a
        # substring of every `lean --version` banner, so "" would silently
        # PASS the callers' substring version checks.
        self.assertIsNone(fuzzer.toolchain_version_token(None))
        self.assertIsNone(fuzzer.toolchain_version_token(""))

    def test_missing_pin_fails_the_version_check_closed_in_both_callers(self):
        import run_conformance_suite as suite
        import run_heapobj_abi_sanitizers as san

        with mock.patch.object(suite, "PINNED_CON_LECHE_TOOLCHAIN", None):
            with self.assertRaisesRegex(RuntimeError, "toolchain pin"):
                suite.find_v435_lean_and_init()
        with mock.patch.object(fuzzer, "repo_pinned_toolchain", return_value=None):
            with self.assertRaisesRegex(RuntimeError, "toolchain pin"):
                san.find_lean_prefix()


class PinnedToolchainEnv(unittest.TestCase):
    """Environment portability: an elan-shimmed binary (lean / lake / leanc)
    invoked on files in a temp dir outside the repo resolves elan's DEFAULT
    toolchain, not the repo pin (measured as `incompatible header ...
    v4.36.0/lib/lean/Init.olean` against the repo's v4.35.0 pin). Subprocess
    environments therefore pin ELAN_TOOLCHAIN from lean/lean-toolchain."""

    def test_sets_elan_toolchain_from_repo_pin(self):
        base = {"PATH": "/usr/bin"}
        env = fuzzer.pinned_toolchain_env(base)
        self.assertEqual(env["ELAN_TOOLCHAIN"], fuzzer.repo_pinned_toolchain())
        self.assertEqual(env["PATH"], "/usr/bin")
        self.assertNotIn("ELAN_TOOLCHAIN", base)

    def test_repo_pin_overrides_ambient_elan_toolchain(self):
        env = fuzzer.pinned_toolchain_env({"ELAN_TOOLCHAIN": "leanprover/lean4:v4.99.0"})
        self.assertEqual(env["ELAN_TOOLCHAIN"], fuzzer.repo_pinned_toolchain())

    def test_defaults_to_current_environ(self):
        with mock.patch.dict(os.environ, {"TL_SENTINEL_VAR": "1"}):
            env = fuzzer.pinned_toolchain_env()
        self.assertEqual(env.get("TL_SENTINEL_VAR"), "1")
        self.assertEqual(env.get("ELAN_TOOLCHAIN"), fuzzer.repo_pinned_toolchain())

    def test_missing_pin_leaves_env_unchanged(self):
        with mock.patch.object(fuzzer, "repo_pinned_toolchain", return_value=None):
            env = fuzzer.pinned_toolchain_env({"A": "b"})
        self.assertEqual(env, {"A": "b"})

    def test_explicit_toolchain_parameter_overrides_repo_pin(self):
        # C2/C3 of the conformance suite pin to the con-leche toolchain, which
        # must not silently become the repo pin the day lean/lean-toolchain bumps.
        env = fuzzer.pinned_toolchain_env({}, toolchain="leanprover/lean4:v9.9.9")
        self.assertEqual(env["ELAN_TOOLCHAIN"], "leanprover/lean4:v9.9.9")


class _EmitLnirReached(Exception):
    pass


class PinnedEnvReachesToolchainSubprocesses(unittest.TestCase):
    """The pin must reach the actual call sites, not only exist as a helper:
    `lean-native emit-lnir` on a temp-dir batch file was the measured C1
    failure (incompatible Init.olean header from the default toolchain)."""

    @staticmethod
    def _drive_until_emit(batch_fn, programs):
        calls = []

        class _Res:
            returncode = 0
            # Three stock values: enough for one scalar program, and exactly
            # the ret/old_read/new_read triple one alias program expects.
            stdout = '["1","1","1"]'
            stderr = ""

        def fake_run(cmd, **kw):
            argv = [str(a) for a in cmd]
            calls.append((argv, kw.get("env")))
            if any("emit-lnir" in a for a in argv):
                raise _EmitLnirReached()
            return _Res()

        engines = {
            "lean_bin": "/fake/lean",
            "core_bin": "/fake/lean-native-core",
            "full_bin": "/fake/lean-native",
            "clang_bin": "/fake/clang",
            "sanitizer_linker": None,
        }
        with mock.patch.dict(os.environ, {}):
            os.environ.pop("TURBO_CONFORMANCE_ASAN", None)
            os.environ.pop("TURBO_CONFORMANCE_UBSAN", None)
            with mock.patch.object(fuzzer.subprocess, "run", side_effect=fake_run):
                try:
                    batch_fn(programs, engines)
                except _EmitLnirReached:
                    return calls
        raise AssertionError("the emit-lnir call site was never reached")

    def _assert_toolchain_calls_pinned(self, calls):
        pin = fuzzer.repo_pinned_toolchain()
        toolchain_calls = [
            (argv, env)
            for argv, env in calls
            if argv[0] in ("/fake/lean", "/fake/lean-native") or argv[0].endswith("leanc")
        ]
        self.assertTrue(toolchain_calls, "no lean/leanc/lean-native subprocess was recorded")
        for argv, env in toolchain_calls:
            self.assertIsNotNone(env, f"{argv} ran without an explicit env (pin lost)")
            self.assertEqual(
                env.get("ELAN_TOOLCHAIN"), pin, f"{argv} env lacks the repo toolchain pin"
            )

    def test_run_three_way_batch_toolchain_calls_carry_the_pin(self):
        calls = self._drive_until_emit(fuzzer.run_three_way_batch, [fuzzer.build_program(1)])
        self._assert_toolchain_calls_pinned(calls)

    def test_run_alias_batch_toolchain_calls_carry_the_pin(self):
        program = fuzzer.build_program(6)
        self.assertTrue(fuzzer.program_contains_alias(program), "seed 6 must be an alias program")
        calls = self._drive_until_emit(fuzzer.run_alias_batch, [program])
        self._assert_toolchain_calls_pinned(calls)

    def test_test_modules_pin_in_setup_module_and_restore_in_teardown(self):
        import importlib

        import test_p0_trust_boundary as tp0
        import test_scalar_frontend as tsf

        for mod in (tsf, tp0):
            with mock.patch.dict(os.environ, {}):
                os.environ.pop("ELAN_TOOLCHAIN", None)
                importlib.reload(mod)
                self.assertIsNone(
                    os.environ.get("ELAN_TOOLCHAIN"),
                    f"importing {mod.__name__} must not mutate os.environ",
                )
                mod.setUpModule()
                self.assertEqual(
                    os.environ.get("ELAN_TOOLCHAIN"),
                    fuzzer.repo_pinned_toolchain(),
                    f"{mod.__name__}.setUpModule must pin ELAN_TOOLCHAIN",
                )
                mod.tearDownModule()
                self.assertIsNone(
                    os.environ.get("ELAN_TOOLCHAIN"),
                    f"{mod.__name__}.tearDownModule must restore the saved env",
                )


class ConLecheToolchainPinConsistency(unittest.TestCase):
    def test_suite_startup_fails_loudly_on_pin_mismatch(self):
        import run_conformance_suite as suite

        # Equal pins today: must not raise.
        suite.assert_toolchain_pins_consistent()
        with mock.patch.object(
            suite.fuzz, "repo_pinned_toolchain", return_value="leanprover/lean4:v9.9.9"
        ):
            with self.assertRaises(SystemExit):
                suite.assert_toolchain_pins_consistent()


if __name__ == "__main__":
    unittest.main()
