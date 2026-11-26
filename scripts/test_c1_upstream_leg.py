#!/usr/bin/env python3
"""Unit tests for the Tier C1 upstream-leg hardening (roadmap leaf C1x, rows R1/R2/R4).

Pure python: no engines, no network, no provisioned corpus. The outcome
classification contract (`classify_c1_upstream_rejection`), the toolchain-pin
consistency gate, and the upstream-call exception wrapper are all testable
without a built toolchain, so this module runs in the fast per-PR gates.
"""
import sys
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import build_c1_corpus_manifest as c1_corpus
import run_conformance_suite as suite


class C1UpstreamClassificationTest(unittest.TestCase):
    def test_deliberate_refusals_are_rejected_fail_closed(self):
        # One sample per deliberate-refusal diagnostic family, measured live at
        # the pin over all 250 manifest programs (2026-11-26).
        samples = (
            "[lean-native] Unsupported non-scalar parameter `array` of `foo` type `Array.{0} Nat`",
            "[lean-native] Unsupported external or non-scalar call `f` in Stage 1B",
            "[lean-native] unsupported string literal",
            "[lean-native] unsupported higher-order fvar call",
            "[lean-native] unsupported erased runtime argument in pure core",
            "[lean-native] unsupported self-tail recursion in List.mapTR.loop: no qualified loop lowering",
            "[lean-native] Failed to extract any LCNF declarations from '/x/y.lean'",
            "[lean-native] Module contains no Stage 1B scalar functions after filtering non-scalar helpers",
        )
        for stderr in samples:
            self.assertEqual(
                suite.classify_c1_upstream_rejection(1, stderr), "rejected_fail_closed", stderr
            )

    def test_other_nonzero_outcomes_are_frontend_error(self):
        cases = (
            # elaboration error (BuildExe.lean prints this, no refusal marker)
            (1, "Elaboration failed for /x/y.lean"),
            # internal bridge invariant trip (RealLCNFBridge.lean:526) is NOT a
            # deliberate unsupported-construct refusal
            (1, "[lean-native] internal bridge error: unintercepted isShared"),
            (1, ""),  # silent nonzero exit
            (1, "usage: emit-lnir --wire <src> -o <out>"),  # usage error
            # negative returncode = killed by a signal, whatever stderr says
            (-6, "[lean-native] Unsupported partial application (`pap f`) in Stage 1B"),
        )
        for rc, stderr in cases:
            self.assertEqual(
                suite.classify_c1_upstream_rejection(rc, stderr), "frontend_error", (rc, stderr)
            )

    def test_mixed_output_disqualifiers_override_refusal_markers(self):
        # F1 (round 2): a disqualifying fatal shape anywhere in stderr OR
        # stdout makes the outcome frontend_error even when a deliberate
        # refusal marker is also present, and returncode >= 128 is a signal
        # death whatever the output says.
        mixed_stderr = (
            "[lean-native] Unsupported non-scalar parameter `a` of `f` type `Array.{0} Nat`\n"
            "[lean-native] internal bridge error: unintercepted isShared\n"
        )
        self.assertEqual(suite.classify_c1_upstream_rejection(1, mixed_stderr), "frontend_error")
        panic_stderr = (
            "[lean-native] unsupported string literal\n"
            "PANIC at Lean.Compiler.LCNF.toDecl Lean/Compiler/LCNF.lean:10:2: oops\n"
        )
        self.assertEqual(suite.classify_c1_upstream_rejection(1, panic_stderr), "frontend_error")
        elab_mixed = (
            "[lean-native] Unsupported partial application (`pap f`) in Stage 1B\n"
            "Elaboration failed for /x/y.lean\n"
        )
        self.assertEqual(suite.classify_c1_upstream_rejection(1, elab_mixed), "frontend_error")
        self.assertEqual(
            suite.classify_c1_upstream_rejection(1, "uncaught exception: out of memory"),
            "frontend_error",
        )
        # disqualifier on stdout beside a clean refusal on stderr
        self.assertEqual(
            suite.classify_c1_upstream_rejection(
                1, "[lean-native] unsupported string literal", "PANIC at f F.lean:1:1: x"
            ),
            "frontend_error",
        )
        # benign program stdout must NOT disqualify a clean refusal
        self.assertEqual(
            suite.classify_c1_upstream_rejection(
                1, "[lean-native] unsupported string literal", ">> [10] 40\n>> [10] 50\n"
            ),
            "rejected_fail_closed",
        )
        # 128+N shell-encoded signal death with a refusal marker present
        self.assertEqual(
            suite.classify_c1_upstream_rejection(134, "[lean-native] unsupported string literal"),
            "frontend_error",
        )

    def test_canary_fixture_exists_and_is_scalar_subset(self):
        src = suite.C1_UPSTREAM_CANARY
        self.assertTrue(src.is_file(), f"canary fixture missing: {src}")
        text = src.read_text(encoding="utf-8")
        self.assertIn("def ", text)
        for banned in ('"', "fun ", "λ", "Array", "let rec", "partial def", " Int "):
            self.assertNotIn(banned, text, f"canary must stay in the scalar subset (found {banned!r})")


class C1ToolchainPinTest(unittest.TestCase):
    def test_mismatch_fails_only_the_opted_in_leg(self):
        # F5 (round 2, re-pins the round-1 behavior): a C1_UPSTREAM_TOOLCHAIN
        # drift no longer stops main() for unrelated tiers; the opted-in leg
        # fails closed with a named status, before any provisioning.
        with mock.patch.object(c1_corpus, "C1_UPSTREAM_TOOLCHAIN", "leanprover/lean4:v9.99.9"):
            suite.assert_toolchain_pins_consistent()  # must not raise
            with mock.patch.object(
                suite,
                "ensure_c1_upstream_corpus",
                side_effect=AssertionError("provisioning must not run on a pin mismatch"),
            ):
                sub = suite.run_c1_upstream_corpus(enabled=True)
                self.assertIs(sub.get("ok"), False)
                self.assertEqual(sub.get("status"), "failed_toolchain_pin_mismatch")
                disabled = suite.run_c1_upstream_corpus(enabled=False)
                self.assertIs(disabled.get("optedIn"), False)

    def test_consistent_pins_pass(self):
        suite.assert_toolchain_pins_consistent()
        self.assertEqual(c1_corpus.C1_UPSTREAM_TOOLCHAIN, suite.fuzz.repo_pinned_toolchain())


class C1UpstreamExceptionWrapperTest(unittest.TestCase):
    def test_upstream_exception_becomes_failed_subresult(self):
        # R4: an exception in the upstream leg never raises past the C1 tier;
        # it is recorded as a failed upstream sub-result.
        with mock.patch.object(suite, "run_c1_upstream_corpus", side_effect=RuntimeError("planted")):
            sub = suite.c1_upstream_subresult(enabled=True)
        self.assertIs(sub.get("ok"), False)
        self.assertEqual(sub.get("status"), "failed_upstream_leg_exception")
        self.assertIn("planted", sub.get("error", ""))
        self.assertIs(sub.get("optedIn"), True)


if __name__ == "__main__":
    unittest.main()
