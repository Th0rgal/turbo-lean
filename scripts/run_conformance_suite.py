#!/usr/bin/env python3
"""Run tiered differential conformance (`--tier` / `--tiers`), sanitizer checks, and certificate/plugin gates.

The former Python reference formulas and C runtime stubs were not independent
Lean execution. They are deliberately excluded from acceptance. Full loop
(`seqFor`), upstream 250+ `lean4/tests/lean/run`, ecosystem Lake packages
(`C2`), `con-leche` holdouts (`C3`), and hardware target qualification remain
open and fail closed when requested via `--tier`.
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any

import fuzz_lcnf_conformance as fuzz

ROOT = Path(__file__).resolve().parent.parent
CORE = ROOT / "lean/.lake/build/bin/lean-native-core"

VALID_TIERS = ("C1", "C2", "C3", "C4")
C1_CORPUS_TESTS = (
    "ScalarFrontend.test_small_width_comparisons",
    "ScalarFrontend.test_narrow_wrapping_arithmetic_shifts_and_div_zero",
    "ScalarFrontend.test_join_point_param_swap_and_nested_helper_inlining",
    "ScalarFrontend.test_chained_boolean_join_points_and_tuple_helpers",
)


def parse_tiers(raw_tiers: list[str] | None) -> list[str]:
    if not raw_tiers:
        return ["C4"]
    selected: list[str] = []
    for raw in raw_tiers:
        for item in raw.split(","):
            tier = item.strip().upper()
            if not tier:
                continue
            if tier not in VALID_TIERS:
                raise ValueError(f"Unknown conformance tier '{item}'; expected subset of {','.join(VALID_TIERS)}")
            if tier not in selected:
                selected.append(tier)
    if not selected:
        raise ValueError("At least one non-empty conformance tier is required")
    return selected


def command_json(*args: str) -> dict[str, Any]:
    result = subprocess.run([str(CORE), *args], cwd=ROOT, check=True,
                            capture_output=True, text=True)
    value = json.loads(result.stdout)
    if not isinstance(value, dict):
        raise RuntimeError("Expected a structured gate report")
    return value


def run_c1_corpus(asan: bool, ubsan: bool) -> dict[str, Any]:
    engines = fuzz.probe_engines(asan=asan, ubsan=ubsan)
    if not (engines["stock_lean_c"] and engines["lnir_eval"] and engines["c_abi_llvm"]):
        return {
            "tier": "C1",
            "ok": False,
            "status": "incomplete_missing_engine",
            "asan": asan,
            "ubsan": ubsan,
            "tests": list(C1_CORPUS_TESTS),
            "engines": {
                "stock_lean_c": engines["stock_lean_c"],
                "lnir_validate_tv": engines["lnir_eval"],
                "c_abi_llvm": engines["c_abi_llvm"],
            },
        }
    cmd = [
        sys.executable,
        "-m",
        "unittest",
        "-v",
        *(f"scripts.test_scalar_frontend.{name}" for name in C1_CORPUS_TESTS),
    ]
    sub_env = dict(os.environ)
    sub_env["TURBO_CONFORMANCE_ASAN"] = "1" if asan else "0"
    sub_env["TURBO_CONFORMANCE_UBSAN"] = "1" if ubsan else "0"
    res = subprocess.run(cmd, cwd=ROOT, env=sub_env, capture_output=True, text=True)
    ok = res.returncode == 0
    return {
        "tier": "C1",
        "ok": ok,
        "status": "passed_scalar_tuple_subset" if ok else "failed_or_incomplete",
        "coverage": "scalar_narrow_unsigned_joinpoint_and_flat_tuple_subset",
        "tests": list(C1_CORPUS_TESTS),
        "testCount": len(C1_CORPUS_TESTS),
        "asan": asan,
        "ubsan": ubsan,
        "returncode": res.returncode,
        "stderrTail": (res.stderr or "")[-1200:],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--fuzz-seeds", type=int, default=50)
    parser.add_argument(
        "--tier",
        "--tiers",
        dest="tiers",
        action="append",
        default=None,
        help="Comma-separated conformance tiers (C1,C2,C3,C4). Default: C4; C2/C3 fail closed until wired.",
    )
    parser.add_argument("--asan", action="store_true", help="Enable AddressSanitizer on compiled LLVM binaries")
    parser.add_argument("--ubsan", action="store_true", help="Enable UndefinedBehaviorSanitizer on compiled LLVM binaries")
    args = parser.parse_args()

    failures: list[dict[str, Any]] = []
    tier_results: dict[str, Any] = {}
    certs: dict[str, Any] = {}
    plugins: dict[str, Any] = {}
    execution: dict[str, Any] = {}

    try:
        tiers = parse_tiers(args.tiers)
    except ValueError as err:
        parser.error(str(err))
        return 2

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

        for tier in tiers:
            if tier == "C1":
                c1 = run_c1_corpus(asan=args.asan, ubsan=args.ubsan)
                tier_results["C1"] = c1
                if c1.get("ok") is not True:
                    failures.append({"stage": "tier_C1_scalar_corpus", "detail": c1})
            elif tier == "C2":
                c2 = {
                    "tier": "C2",
                    "ok": False,
                    "status": "BLOCKED_MISSING_DEPENDENCY",
                    "reason": "Ecosystem Lake codegen corpus (Batteries, LeanSys, SciLean, ArkLib) is not yet wired into 3-way LeanNative execution",
                }
                tier_results["C2"] = c2
                failures.append({"stage": "tier_C2_unimplemented", "detail": c2})
            elif tier == "C3":
                c3 = {
                    "tier": "C3",
                    "ok": False,
                    "status": "BLOCKED_MISSING_DEPENDENCY",
                    "reason": "Cross-regime holdouts (R1-R6) require upstream leanprover/con-leche vendoring and real .olean replay",
                }
                tier_results["C3"] = c3
                failures.append({"stage": "tier_C3_unimplemented", "detail": c3})
            elif tier == "C4":
                execution = fuzz.run_fuzzer(args.fuzz_seeds, asan=args.asan, ubsan=args.ubsan)
                tier_results["C4"] = execution
                if execution.get("ok") is not True or execution.get("checked", 0) != args.fuzz_seeds or args.fuzz_seeds < 1:
                    failures.append({"stage": "scalar_three_engine_execution", "detail": execution})
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        failures.append({"stage": "execution_failure", "detail": str(error)})

    report = {
        "schemaVersion": "turbo-lean-conformance-v2",
        "ok": not failures,
        "tiersRequested": tiers,
        "tierResults": tier_results,
        "asan": args.asan,
        "ubsan": args.ubsan,
        "scope": "scalar_three_engine_and_separate_certificate_plugin_gates",
        "fullRoadmapAccepted": False,
        "missingCoverage": ["alias_RC_seqFor_llvm", "upstream_lean4_run_250", "tier_C2_ecosystem_packages", "tier_C3_con_leche_holdouts", "target_qualification"],
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
        print(
            f"[conformance] tiers={','.join(tiers)} asan={args.asan} ubsan={args.ubsan}: "
            f"{'PASSED' if report['ok'] else 'FAILED'}; "
            f"fuzz_checked={report['lcnfFuzzSeedsChecked']}; full roadmap acceptance remains open"
        )
        for failure in failures:
            print(json.dumps(failure, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
