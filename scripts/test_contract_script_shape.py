#!/usr/bin/env python3
"""HY1 pin: structural contract of scripts/verify_roadmap_contract.sh.

Records what the contract script prints that identifies its structure —
the numbered gate headers in order, the final summary line, and the
exit-status behavior — and fails when any of that changes. The HY1 split
into scripts/contract.d/ fragments must keep all of it identical.

Static checks always run (no build needed). The end-to-end runtime check
runs the real script only when CONTRACT_SHAPE_RUNTIME=1 is set and the
built binaries exist, so it can never recurse into itself when it is run
from inside the contract run.
"""

import hashlib
import os
import re
import shutil
import subprocess
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent
ROOT = SCRIPTS_DIR.parent
CONTRACT_SH = SCRIPTS_DIR / "verify_roadmap_contract.sh"
CONTRACT_D = SCRIPTS_DIR / "contract.d"

# The gate headers exactly as the unmodified script prints them, in order.
# Ten numbered gates plus the "[2b/10]" sub-gate of gate 2 and the "[3b/10]"
# H1.1 differential sub-gate of gate 3.
EXPECTED_GATE_HEADERS = [
    "=== [1/10] Spec & Documentation Pinning Ratchet (Contract V1) ===",
    "=== [2/10] Multi-Hop Vacuity, Tightness & Packing Audit (audit-spec v2) ===",
    "=== [2b/10] Configurable Anti-Reward-Hacking & Shadow-Namespace Gate (audit-spec v2.1, Contract V1/V2/V3) ===",
    "=== [3/10] In-Kernel Transitive Axiom Gate (Lean.collectAxioms) ===",
    "=== [3b/10] H1.1 Differential LCNF Interpreter Gate (RealLCNFSemantics vs compiled Lean reference) ===",
    "=== [4/10] Verified Pass Contract & Bridge/CoreCLI Hygiene Gate (Contract V2, M4 & M5) ===",
    "=== [5/10] Segregated Plugin & Adversarial Mutant Gate (Law 1) ===",
    "=== [6/10] 3-Way Differential Conformance Suite (C1, Provisioned C2 Lake Packages, C4), Grammar-Guided LCNF Fuzzer & P0 Trust Boundary ===",
    "=== [7/10] Stage 2 LLVM Differential (lli), Alive2 Translation Validation & lean-mlir Bridge Gate ===",
    "=== [8/10] Stage 3 GPU/TPU Differential (ptxas, OpenXLA StableHLO, Metal MSL 3.0) & LNSym / Sail-RISC-V / ConLeche Bridge Gates ===",
    "=== [9/10] Stage 4 Target-IR 4-Backend Differential & Sanitizer/UB Fuzzing Gate ===",
    "=== [10/10] Stage 5 Unwrapped libleanrt.a HeapObj/ABI ASan/LSan/UBSan & TSan Stress Gate ===",
]

# The one summary line printed after the last gate, on success only.
EXPECTED_FINAL_LINE = (
    "=== LOCAL VALIDATION GATES PASSED (scalar + multi-module Lake C2 fixtures; "
    "full roadmap coverage remains open) ==="
)

# The gate fragments exactly as HY1 left them, in the order the runner
# sources them (lexicographic, C collation). A later leaf that adds a
# fragment or changes one must update this list and the hashes below in the
# same commit, so the pin keeps failing on anything it was not told about.
EXPECTED_FRAGMENT_NAMES = [
    "10_docs_pinning_ratchet.sh",
    "20_audit_spec_v2.sh",
    "21_audit_spec_strict_proofs.sh",
    "30_axiom_gate.sh",
    "35_h11_lcnf_differential.sh",
    "40_verified_pass_hygiene.sh",
    "50_plugin_mutant_gate.sh",
    "60_conformance_fuzz_trust.sh",
    "70_llvm_alive2_leanmlir.sh",
    "80_gpu_tpu_bridges.sh",
    "90_target_ir_fuzz.sh",
    "99_heapobj_sanitizers.sh",
]

# SHA-256 of each fragment's bytes. A gate that is edited, emptied below its
# header or truncated changes its hash; a later leaf that legitimately
# changes a fragment updates its hash here in the same commit.
EXPECTED_FRAGMENT_HASHES = {
    "10_docs_pinning_ratchet.sh": "ac187453635c45e67abc47e65127f25aeb67c00a8318e6768dd236b2ceddb9ac",
    "20_audit_spec_v2.sh": "e0e9df7c3c15bc028155d847c77c6f142f47ac73806f5fc0c4d0c5304ef9b951",
    "21_audit_spec_strict_proofs.sh": "d0c073cae6410d0092a388ff404b2cacaea2e112f1639fe93796af0c066fd15f",
    "30_axiom_gate.sh": "49e36170e63217edc80887b8d26cb6b199b079596de0abdc54bd6e4104a8f60a",
    "35_h11_lcnf_differential.sh": "55cacb9004d575aaa08d9a9ab3a6e4d3cce746ba87cd7fcb736f0ea6203a9828",
    "40_verified_pass_hygiene.sh": "7cbb8ca4782a952d9a2e31466de6d6677273a9f7a49e9386cb3be086d1d997e0",
    "50_plugin_mutant_gate.sh": "d7463ec4943426b4e235e6706eac9e49f4def2e2eec02437c8b510948763ea43",
    "60_conformance_fuzz_trust.sh": "fdb3048842442b9a5a3b2f7ee69bcf743afbef69e7f921470c28cfcc688ec10f",
    "70_llvm_alive2_leanmlir.sh": "78bdb696aa1e89b2300de270d9284902a58dd5a5aeb5bee78ed79cb1b89e0ca2",
    "80_gpu_tpu_bridges.sh": "c9887ba4b3fa22d0fb6e2c10d4de9fc952a4ca47895c5fff570003e08863b798",
    "90_target_ir_fuzz.sh": "d547e8e891d7443383ce86f125718c6b2c69439b850f36303584297e88b8c278",
    "99_heapobj_sanitizers.sh": "e38b638d6d2cba43b8939e90afef0c860b666e7faa91b1198bbb3fa0105e36e2",
}

ECHO_HEADER_RE = re.compile(r'^echo "(=== .* ===)"\s*$', re.MULTILINE)
GATE_HEADER_RE = re.compile(r"^=== \[\d+b?/10\] ")
FINAL_LINE_RE = re.compile(r"^=== LOCAL VALIDATION GATES PASSED")


def echo_header_lines(text):
    return [m.group(1) for m in ECHO_HEADER_RE.finditer(text)]


def effective_header_lines():
    """The header lines the run prints, in order: the runner's own echoes
    before the fragment-ordering line (the preamble has none today), then
    the echoes of each contract.d fragment in the order the runner sources
    them, then the runner's echoes after the loop (the final summary line)."""
    text = CONTRACT_SH.read_text()
    order_line_index = next(
        (i for i, ln in enumerate(text.splitlines()) if "contract.d/*.sh" in ln),
        None,
    )
    if order_line_index is None:
        # Pre-HY1 layout: the gates (and the summary) are all in the runner.
        return echo_header_lines(text)
    lines = text.splitlines()
    before, after = "\n".join(lines[:order_line_index]), "\n".join(lines[order_line_index + 1 :])
    result = echo_header_lines(before)
    if CONTRACT_D.is_dir():
        for fragment in sorted(CONTRACT_D.glob("*.sh")):
            result.extend(echo_header_lines(fragment.read_text()))
    result.extend(echo_header_lines(after))
    return result


def runner_ordering_command():
    """The runner's one-line fragment-expansion mechanism, extracted from the
    `< <(...)` process substitution, ready to run standalone with ROOT_DIR in
    the environment. Raises if the runner does not have the expected shape."""
    for line in CONTRACT_SH.read_text().splitlines():
        if "contract.d/*.sh" in line and "< <(" in line:
            inner = line.split("< <(", 1)[1].strip()
            if not inner.endswith(")"):
                raise AssertionError(f"ordering line is not a single < <(...) substitution: {line!r}")
            return inner[:-1]
    raise AssertionError("runner has no single-line < <(...) fragment-ordering mechanism")


def installed_locales():
    try:
        return set(subprocess.run(["locale", "-a"], capture_output=True, text=True, timeout=10).stdout.split())
    except (OSError, subprocess.SubprocessError):
        return set()


NON_C_LOCALE_CANDIDATES = ("en_US.UTF-8", "en_US.utf8", "C.UTF-8")


def non_c_locale():
    """A locale whose collation differs from C, if one is installed."""
    installed = installed_locales()
    for candidate in NON_C_LOCALE_CANDIDATES:
        if candidate in installed and candidate != "C":
            return candidate
    return None


class ContractScriptShape(unittest.TestCase):
    def test_runner_sources_all_fragments(self):
        text = CONTRACT_SH.read_text()
        if not CONTRACT_D.is_dir():
            # Pre-HY1 layout: the gates are the runner's own text.
            self.assertNotIn("contract.d", text)
            return
        self.assertIn("scripts/contract.d/*.sh", text, "runner must expand every contract.d fragment")
        self.assertIn("source", text, "runner must source the fragments into its own shell")

    def test_fragment_ordering_is_locale_independent(self):
        if not CONTRACT_D.is_dir():
            self.skipTest("pre-HY1 layout: fragments are inline in the runner")
        mechanism = runner_ordering_command()
        self.assertIn(
            "LC_ALL=C", mechanism,
            "the fragment expansion must pin the collation (LC_ALL=C) itself",
        )
        other = non_c_locale()
        if other is None:
            self.skipTest("no non-C locale installed; the mechanism assertion above is the check")
        env = {**os.environ, "ROOT_DIR": str(ROOT)}
        run = lambda lc: subprocess.run(
            ["bash", "-c", mechanism], env={**env, "LC_ALL": lc},
            capture_output=True, text=True, timeout=30,
        )
        under_c, under_other = run("C"), run(other)
        self.assertEqual(under_c.returncode, 0, under_c.stderr)
        self.assertEqual(under_other.returncode, 0, under_other.stderr)
        self.assertEqual(
            under_other.stdout, under_c.stdout,
            f"fragment order differs under LC_ALL={other}; the expansion must pin LC_ALL=C itself",
        )
        self.assertEqual(
            [Path(p).name for p in under_c.stdout.split()],
            sorted(p.name for p in CONTRACT_D.glob("*.sh")),
            "the pinned-collation expansion must yield the C-collated fragment order",
        )

    def test_gate_headers_present_in_order(self):
        printed = [line for line in effective_header_lines() if GATE_HEADER_RE.match(line)]
        self.assertEqual(printed, EXPECTED_GATE_HEADERS)

    def test_final_summary_line_is_last_header_line(self):
        printed = effective_header_lines()
        self.assertTrue(printed, "no === echo lines found at all")
        self.assertTrue(FINAL_LINE_RE.match(printed[-1]), f"last === echo line is {printed[-1]!r}")
        self.assertEqual(printed[-1], EXPECTED_FINAL_LINE)
        finals = [line for line in printed if FINAL_LINE_RE.match(line)]
        self.assertEqual(finals, [EXPECTED_FINAL_LINE], "final summary line must appear exactly once")

    def test_no_unexpected_gate_header_shape(self):
        printed = effective_header_lines()
        for line in printed:
            self.assertTrue(
                GATE_HEADER_RE.match(line) or FINAL_LINE_RE.match(line),
                f"unexpected === line not covered by the pin: {line!r}",
            )

    def test_fragment_files_are_exactly_the_pinned_list(self):
        if not CONTRACT_D.is_dir():
            self.skipTest("pre-HY1 layout: fragments are inline in the runner")
        actual = sorted(p.name for p in CONTRACT_D.glob("*.sh"))
        self.assertEqual(
            actual, sorted(EXPECTED_FRAGMENT_NAMES),
            "contract.d gained, lost or renamed a fragment without the pin being updated",
        )

    def test_fragment_bodies_match_pinned_hashes(self):
        if not CONTRACT_D.is_dir():
            self.skipTest("pre-HY1 layout: fragments are inline in the runner")
        for name in EXPECTED_FRAGMENT_NAMES:
            fragment = CONTRACT_D / name
            self.assertTrue(fragment.is_file(), f"fragment {name} is missing")
            digest = hashlib.sha256(fragment.read_bytes()).hexdigest()
            self.assertEqual(
                digest, EXPECTED_FRAGMENT_HASHES.get(name),
                f"fragment {name} changed (edited, emptied or truncated) without its pin hash being updated",
            )

    def test_any_gate_failure_fails_the_run(self):
        text = CONTRACT_SH.read_text()
        self.assertIn("set -euo pipefail", text, "contract script must abort on the first failing gate")
        for fragment in sorted(CONTRACT_D.glob("*.sh")) if CONTRACT_D.is_dir() else []:
            self.assertNotIn(
                "set -e", fragment.read_text(),
                f"{fragment.name} must not reset shell options behind the runner's back",
            )


def contract_binaries_available():
    """Mirror the preamble's binary discovery; True only if it can pass the checks."""
    turbo = os.environ.get("TURBO_AUDITOR_BIN")
    if turbo is None:
        turbo = ROOT / "target" / "release" / "turbo-lean"
        if not turbo.exists():
            turbo = shutil.which("turbo-lean")
    lake_bins = [
        ROOT / "lean" / ".lake" / "build" / "bin" / name
        for name in ("lean-native", "lean-native-core", "turbo-zygote")
    ]
    return bool(turbo and os.path.isfile(str(turbo)) and os.access(str(turbo), os.X_OK)) and all(
        p.exists() and os.access(p, os.X_OK) for p in lake_bins
    )


@unittest.skipUnless(
    os.environ.get("CONTRACT_SHAPE_RUNTIME") == "1",
    "end-to-end run is opt-in (CONTRACT_SHAPE_RUNTIME=1) so this test can be part of the contract run without recursing",
)
class ContractScriptEndToEndShape(unittest.TestCase):
    def test_run_matches_pinned_shape(self):
        self.assertTrue(contract_binaries_available(), "contract binaries missing; build first")
        proc = subprocess.run(
            ["bash", str(CONTRACT_SH)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=4 * 60 * 60,
        )
        printed = [ln for ln in proc.stdout.splitlines() if GATE_HEADER_RE.match(ln)]
        if proc.returncode == 0:
            self.assertEqual(printed, EXPECTED_GATE_HEADERS, "exit 0 must have run every gate header in order")
            self.assertTrue(
                FINAL_LINE_RE.match(proc.stdout.splitlines()[-1]) if proc.stdout.splitlines() else False,
                "exit 0 must print the final summary line",
            )
        else:
            self.assertEqual(
                printed,
                EXPECTED_GATE_HEADERS[: len(printed)],
                "a failing run must stop at a pinned gate, not skip or reorder one",
            )
            self.assertFalse(
                any(FINAL_LINE_RE.match(ln) for ln in proc.stdout.splitlines()),
                "the final summary line must not print on a failing run",
            )


if __name__ == "__main__":
    unittest.main()
