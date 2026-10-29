#!/usr/bin/env python3
"""Run the real scalar three-engine corpus and separate certificate/plugin gates.

The former Python reference formulas and C runtime stubs were not independent
Lean execution. They are deliberately excluded from acceptance. Full loop,
alias/RC, Orb/LeanSys export and target/host-wrapper coverage remains required.
"""
from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path

import fuzz_lcnf_conformance as fuzz

ROOT = Path(__file__).resolve().parent.parent
CORE = ROOT / "lean/.lake/build/bin/lean-native-core"


def command_json(*args: str) -> dict:
    result = subprocess.run([str(CORE), *args], cwd=ROOT, check=True,
                            capture_output=True, text=True)
    value = json.loads(result.stdout)
    if not isinstance(value, dict):
        raise RuntimeError("Expected a structured gate report")
    return value


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--fuzz-seeds", type=int, default=50)
    args = parser.parse_args()
    failures = []
    try:
        certs = command_json("verify-certs", "--canonical-benchmark", "--json")
        plugins = command_json("plugins", "--canonical-benchmark", "--test-adversarial", "--json")
        if certs.get("verified") is not True or not certs.get("declSummaries"):
            failures.append({"stage": "certificate_chain", "detail": certs})
        if (plugins.get("adversarialRejected") is not True
                or type(plugins.get("rejectedCount")) is not int or plugins["rejectedCount"] < 1
                or not plugins.get("declAudits")
                or any(r.get("tvVerified") is not True for r in plugins["declAudits"])):
            failures.append({"stage": "adversarial_plugin_gate", "detail": plugins})
        execution = fuzz.run_fuzzer(args.fuzz_seeds)
        if execution.get("ok") is not True or execution.get("checked", 0) != args.fuzz_seeds or args.fuzz_seeds < 1:
            failures.append({"stage": "scalar_three_engine_execution", "detail": execution})
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        failures.append({"stage": "execution_failure", "detail": str(error)})
        certs, plugins, execution = {}, {}, {}
    report = {
        "schemaVersion": "turbo-lean-conformance-v2",
        "ok": not failures,
        "scope": "scalar_three_engine_and_separate_certificate_plugin_gates",
        "fullRoadmapAccepted": False,
        "missingCoverage": ["alias_RC_seqFor", "all_Orb_LeanSys_exports", "WASM_and_host_wrappers", "target_qualification"],
        "divergences": len(failures),
        "divergenceDetails": failures,
        "lcnfFuzzSeedsChecked": execution.get("checked", 0),
        "lcnfFuzzRcLeaks": execution.get("rc_leak_count"),
        "certificateChainVerified": certs.get("verified", False),
        "overallAssurance": certs.get("overallAssurance", "Unknown"),
        "adversarialMutantRejected": plugins.get("adversarialRejected", False),
        "execution": execution,
    }
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(f"[conformance] scalar suite: {'PASSED' if report['ok'] else 'FAILED'}; "
              f"executed={report['lcnfFuzzSeedsChecked']}; full roadmap acceptance remains open")
        for failure in failures:
            print(json.dumps(failure, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
