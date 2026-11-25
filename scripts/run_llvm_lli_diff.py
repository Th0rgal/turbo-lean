#!/usr/bin/env python3
"""Stage 2A: Differential execution gate between `LLVMAst.execFn` and `lli --force-interpreter`.

Runs concrete IR modules emitted by `LLVMAst.PP.ppModule` (and lowered from `LNIRDecl` via
`LLVMLower.lowerModuleWithFacts`) through LLVM's reference interpreter (`lli --force-interpreter`),
checking 64-bit bit-exact agreement across all 8-bit exit-code slices (`[0..63]`), plus negative
mutant divergence checks proving that semantic mismatches are caught.
"""
from __future__ import annotations

import argparse
import json
import os
import platform
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Any

ROOT_DIR = Path(__file__).resolve().parent.parent

# Host-CPU `(lean --arch spelling, llvm triple, datalayout)` pairs, mirroring the
# Rust-side `builtin_fastcheck_cpu_target` (crates/turbo-lean/src/gpu_fastcheck.rs)
# and the Lean-side `TargetArch.llvmTriple` / `TargetArch.dataLayout` constants
# (lean/LeanNative/IR/Types.lean).
HOST_CPU_TARGETS: dict[str, tuple[str, str, str]] = {
    "x86_64": (
        "x86_64",
        "x86_64-unknown-linux-gnu",
        "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128",
    ),
    "aarch64": (
        "arm64",
        "aarch64-unknown-linux-gnu",
        "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128",
    ),
}


def host_llvm_cpu_target() -> tuple[str, str, str]:
    """`(lean --arch spelling, llvm triple, datalayout)` for the host CPU."""
    machine = platform.machine().lower()
    key = "aarch64" if machine in ("aarch64", "arm64") else "x86_64"
    return HOST_CPU_TARGETS[key]


def find_llvm_tool(names: list[str]) -> str | None:
    for name in names:
        env_override = os.environ.get(name.upper().replace("-", "_"))
        if env_override and Path(env_override).is_file():
            return env_override
        found = shutil.which(name)
        if found:
            return found
    for ver in ("18", "19", "17", "20"):
        for base in names:
            cand = f"/usr/lib/llvm-{ver}/bin/{base}"
            if Path(cand).is_file() and os.access(cand, os.X_OK):
                return cand
    return None


def iter_llvm_tool_candidates(names: list[str]):
    """Yield every resolvable candidate for `names` (env override, PATH, versioned
    /usr/lib/llvm-* trees), deduplicated, in `find_llvm_tool`'s precedence order.
    Used to probe-gate tool selection the way `fuzz_lcnf_conformance.find_clang_binary`
    does: the first candidate that passes the functional probe wins."""
    seen: set[str] = set()
    for name in names:
        env_override = os.environ.get(name.upper().replace("-", "_"))
        if env_override and Path(env_override).is_file() and env_override not in seen:
            seen.add(env_override)
            yield env_override
        found = shutil.which(name)
        if found and found not in seen:
            seen.add(found)
            yield found
    for ver in ("18", "19", "17", "20"):
        for base in names:
            cand = f"/usr/lib/llvm-{ver}/bin/{base}"
            if cand not in seen and Path(cand).is_file() and os.access(cand, os.X_OK):
                seen.add(cand)
                yield cand


def build_lli_harness_ir(module_ir: str, fn_name: str, inputs: list[int]) -> str:
    """Append a side-effect-free `@main(i32 %argc, ptr %argv)` wrapper that invokes `@<fn_name>`
    with exact `i64` constants and returns byte `(result >> (8 * (argc - 1))) & 0xFF` as `i32`.

    Passing `0..7` extra dummy arguments to `lli --force-interpreter` sets `argc = 1..8`,
    allowing one verified IR file per input vector to reconstruct the full 64-bit return word
    without requiring external libc `printf` FFI inside `--force-interpreter`.
    """
    arg_list = ", ".join(f"i64 {u}" for u in inputs)
    wrapper = f"""
define i32 @main(i32 %argc, ptr %argv) {{
entry:
  %res64 = call i64 @{fn_name}({arg_list})
  %idx32 = sub i32 %argc, 1
  %idx64 = zext i32 %idx32 to i64
  %sh = mul i64 %idx64, 8
  %shifted = lshr i64 %res64, %sh
  %masked = and i64 %shifted, 255
  %byte = trunc i64 %masked to i32
  ret i32 %byte
}}
"""
    return module_ir.rstrip() + "\n" + wrapper


def run_lli_u64(lli_bin: str, opt_bin: str, ir_path: Path, verify_ir: bool = True) -> int:
    if verify_ir:
        chk = subprocess.run(
            [opt_bin, "-passes=verify", "-disable-output", str(ir_path)],
            capture_output=True,
            text=True,
            timeout=30,
        )
        if chk.returncode != 0:
            raise RuntimeError(f"opt -passes=verify failed on {ir_path}:\n{chk.stderr}")

    word = 0
    for byte_idx in range(8):
        dummy_args = ["x"] * byte_idx
        proc = subprocess.run(
            [lli_bin, "--force-interpreter", str(ir_path), *dummy_args],
            capture_output=True,
            text=True,
            timeout=30,
        )
        if proc.returncode < 0:
            raise RuntimeError(
                f"lli --force-interpreter crashed with signal {-proc.returncode} on {ir_path}:\n{proc.stderr}"
            )
        if proc.stderr and (
            "LLVM ERROR" in proc.stderr
            or "Cannot execute" in proc.stderr
            or "error:" in proc.stderr.lower()
        ):
            raise RuntimeError(f"lli --force-interpreter error on {ir_path}:\n{proc.stderr}")
        byte_val = proc.returncode & 0xFF
        word |= byte_val << (8 * byte_idx)
    return word


def build_ub_probe_ir() -> str:
    """Host-arch udiv-by-zero probe module (triple/datalayout from `HOST_CPU_TARGETS`)."""
    _, triple, datalayout = host_llvm_cpu_target()
    return f"""target datalayout = "{datalayout}"
target triple = "{triple}"
define i32 @main(i32 %argc, ptr %argv) {{
entry:
  %z = sub i32 %argc, %argc
  %q = udiv i32 42, %z
  ret i32 %q
}}
"""


def classify_ub_probe(outcomes: list[tuple[int, str]]) -> dict[str, Any]:
    """Classify repeated UB-probe runs. Trap evidence is a signal (`rc < 0`) or an
    explicit `ERROR` diagnostic on stderr, on EVERY run. A plain exit status proves
    nothing: `udiv` by zero is UB, and an interpreter that does not trap (measured on
    LLVM 15 `lli`: rc 80/96/64/48/128/0 for the same input) returns `@main`'s garbage
    value as the exit code, so even `rc >= 128` is a coin flip, not a trap."""
    rcs = [rc for rc, _ in outcomes]
    trapped_each = [rc < 0 or "ERROR" in stderr for rc, stderr in outcomes]
    return {
        "trapped": bool(trapped_each) and all(trapped_each),
        "deterministic": len(set(rcs)) == 1 and len(set(trapped_each)) == 1,
        "returncodes": rcs,
        "stderr": outcomes[-1][1].strip()[:240] if outcomes else "",
    }


def run_ub_probe_lli(lli_bin: str, runs: int = 2) -> dict[str, Any]:
    """Negative UB probe: division by zero under `lli --force-interpreter` must trap/abort
    deterministically (signal or explicit `ERROR` diagnostics on every run) rather than
    exiting with an arbitrary 0..255 status."""
    with tempfile.TemporaryDirectory(prefix="tl-lli-ub-") as tmp:
        p = Path(tmp) / "ub_div_zero.ll"
        p.write_text(build_ub_probe_ir(), encoding="utf-8")
        outcomes: list[tuple[int, str]] = []
        for _ in range(max(2, runs)):
            proc = subprocess.run(
                [lli_bin, "--force-interpreter", str(p)],
                capture_output=True,
                text=True,
                timeout=15,
            )
            outcomes.append((proc.returncode, proc.stderr))
    return classify_ub_probe(outcomes)


KNOWN_ANSWER_RET = 7


def build_known_answer_ir() -> str:
    """Host-arch module whose `@main` must exit with exactly `KNOWN_ANSWER_RET`."""
    _, triple, datalayout = host_llvm_cpu_target()
    return f"""target datalayout = "{datalayout}"
target triple = "{triple}"
define i32 @main(i32 %argc, ptr %argv) {{
entry:
  ret i32 {KNOWN_ANSWER_RET}
}}
"""


def llvm_tool_version_line(bin_path: str) -> str:
    try:
        proc = subprocess.run([bin_path, "--version"], capture_output=True, text=True, timeout=15)
    except (OSError, subprocess.SubprocessError):
        return ""
    for line in proc.stdout.splitlines():
        if "LLVM version" in line:
            return line.strip()
    head = proc.stdout.strip().splitlines()
    return head[0].strip() if head else ""


def qualify_lli_engine(lli_bin: str, opt_bin: str) -> dict[str, Any]:
    """Probe-gate the `lli`/`opt` pair against the IR shapes this stage emits (the
    sibling of `fuzz_lcnf_conformance.find_clang_binary`'s functional IR probe; the
    toolchain does not bundle `lli`/`opt`, so the system ones can be too old):
      1. `opt -passes=verify` accepts a host-arch opaque-pointer module;
      2. `lli --force-interpreter` runs it with the exact expected exit code, twice;
      3. the udiv-by-zero UB probe traps deterministically (an interpreter that
         reports a garbage exit value for UB disqualifies itself rather than
         yielding a coin-flip verdict)."""
    result: dict[str, Any] = {
        "lli_bin": lli_bin,
        "opt_bin": opt_bin,
        "lli_version": llvm_tool_version_line(lli_bin),
        "opt_version": llvm_tool_version_line(opt_bin),
        "usable": False,
        "reason": None,
    }
    try:
        with tempfile.TemporaryDirectory(prefix="tl-lli-qualify-") as tmp:
            ka = Path(tmp) / "known_answer.ll"
            ka.write_text(build_known_answer_ir(), encoding="utf-8")
            chk = subprocess.run(
                [opt_bin, "-passes=verify", "-disable-output", str(ka)],
                capture_output=True,
                text=True,
                timeout=30,
            )
            if chk.returncode != 0:
                result["reason"] = (
                    f"opt -passes=verify rejected host-arch IR: {chk.stderr.strip()[:240]}"
                )
                return result
            for _ in range(2):
                proc = subprocess.run(
                    [lli_bin, "--force-interpreter", str(ka)],
                    capture_output=True,
                    text=True,
                    timeout=15,
                )
                if proc.returncode != KNOWN_ANSWER_RET:
                    result["reason"] = (
                        f"lli --force-interpreter returned {proc.returncode} for a known-answer "
                        f"module expecting {KNOWN_ANSWER_RET}: {proc.stderr.strip()[:240]}"
                    )
                    return result
        probe = run_ub_probe_lli(lli_bin)
    except (OSError, subprocess.SubprocessError) as exc:
        result["reason"] = f"engine probe failed to execute: {exc}"
        return result
    result["ub_div_zero_probe"] = probe
    if not probe["trapped"]:
        result["reason"] = (
            "udiv-by-zero probe did not trap deterministically "
            f"(returncodes={probe['returncodes']}); this interpreter reports a garbage "
            "exit value for UB, so its pass/fail verdicts are unreliable"
        )
        return result
    result["usable"] = True
    return result


def run_suite(core_bin: Path, lli_bin: str, opt_bin: str) -> dict[str, Any]:
    proc = subprocess.run(
        [str(core_bin), "llvm-diff-suite"],
        capture_output=True,
        text=True,
        timeout=60,
        check=True,
    )
    payload = json.loads(proc.stdout)
    cases = payload["cases"]
    if len(cases) < 10:
        raise RuntimeError(f"Expected >= 10 diff cases from llvm-diff-suite, got {len(cases)}")

    total_vectors = 0
    mismatches: list[dict[str, Any]] = []
    negative_kills: list[dict[str, Any]] = []
    negative_survivors: list[str] = []

    with tempfile.TemporaryDirectory(prefix="tl-lli-diff-") as tmp_dir:
        tmp = Path(tmp_dir)
        for case in cases:
            cid = case["id"]
            fn_name = case["fnName"]
            ir_text = case["irText"]
            vectors = case["vectors"]
            for v_idx, vec in enumerate(vectors):
                inputs = [int(x) for x in vec["inputs"]]
                expected_word = int(vec["expectedWord"])
                ir_file = tmp / f"{cid}_v{v_idx}.ll"
                ir_file.write_text(build_lli_harness_ir(ir_text, fn_name, inputs), encoding="utf-8")
                actual_word = run_lli_u64(lli_bin, opt_bin, ir_file, verify_ir=True)
                total_vectors += 1
                if actual_word != expected_word:
                    mismatches.append(
                        {
                            "case": cid,
                            "fnName": fn_name,
                            "inputs": inputs,
                            "expected_execFn": hex(expected_word),
                            "actual_lli": hex(actual_word),
                        }
                    )

            neg_ir = case.get("negativeMutantIr")
            if neg_ir:
                diverged_on: dict[str, Any] | None = None
                for v_idx, vec in enumerate(vectors):
                    inputs = [int(x) for x in vec["inputs"]]
                    expected_word = int(vec["expectedWord"])
                    neg_file = tmp / f"{cid}_neg_v{v_idx}.ll"
                    neg_file.write_text(build_lli_harness_ir(neg_ir, fn_name, inputs), encoding="utf-8")
                    neg_word = run_lli_u64(lli_bin, opt_bin, neg_file, verify_ir=True)
                    if neg_word != expected_word:
                        diverged_on = {
                            "case": cid,
                            "reason": case.get("negativeMutantReason"),
                            "inputs": inputs,
                            "expected_execFn": hex(expected_word),
                            "mutant_lli": hex(neg_word),
                        }
                        break
                if diverged_on is not None:
                    negative_kills.append(diverged_on)
                else:
                    negative_survivors.append(cid)

    ub_probe = run_ub_probe_lli(lli_bin)
    ok = (
        len(mismatches) == 0
        and len(negative_survivors) == 0
        and len(negative_kills) >= 6
        and bool(ub_probe["trapped"])
    )
    return {
        "ok": ok,
        "lli_bin": lli_bin,
        "opt_bin": opt_bin,
        "cases_checked": len(cases),
        "vectors_checked": total_vectors,
        "mismatches": mismatches,
        "negative_mutants_killed": len(negative_kills),
        "negative_kills": negative_kills,
        "negative_survivors": negative_survivors,
        "ub_div_zero_probe": ub_probe,
    }


class SelfTests(unittest.TestCase):
    def test_harness_generation(self) -> None:
        base_ir = 'define ccc i64 @foo(i64 %a, i64 %b) {\nentry:\n  %r = add i64 %a, %b\n  ret i64 %r\n}'
        wrapped = build_lli_harness_ir(base_ir, "foo", [0x1122334455667788, 5])
        self.assertIn("call i64 @foo(i64 1234605616436508552, i64 5)", wrapped)
        self.assertIn("define i32 @main(i32 %argc, ptr %argv)", wrapped)
        self.assertIn("lshr i64 %res64, %sh", wrapped)

    def test_probe_ir_targets_host_arch(self) -> None:
        arch, triple, datalayout = host_llvm_cpu_target()
        if platform.machine().lower() in ("aarch64", "arm64"):
            self.assertEqual(arch, "arm64")
            self.assertEqual(triple, "aarch64-unknown-linux-gnu")
        else:
            self.assertEqual(arch, "x86_64")
            self.assertEqual(triple, "x86_64-unknown-linux-gnu")
        for ir in (build_ub_probe_ir(), build_known_answer_ir()):
            self.assertIn(f'target triple = "{triple}"', ir)
            self.assertIn(f'target datalayout = "{datalayout}"', ir)

    def test_ub_probe_classification_requires_deterministic_trap_evidence(self) -> None:
        # Measured on LLVM 15 lli: udiv-by-zero returned rc 80/96/64/48/128/0 for one
        # input, so a bare exit status (even >= 128) must never read as a trap.
        garbage_flip = classify_ub_probe([(128, ""), (0, "")])
        self.assertFalse(garbage_flip["trapped"])
        self.assertFalse(garbage_flip["deterministic"])
        stable_garbage = classify_ub_probe([(160, ""), (160, "")])
        self.assertFalse(stable_garbage["trapped"])
        self.assertTrue(stable_garbage["deterministic"])
        signal_trap = classify_ub_probe([(-6, ""), (-6, "")])
        self.assertTrue(signal_trap["trapped"])
        self.assertTrue(signal_trap["deterministic"])
        error_trap = classify_ub_probe(
            [(70, "LLVM ERROR: divide by zero"), (70, "LLVM ERROR: divide by zero")]
        )
        self.assertTrue(error_trap["trapped"])
        one_bad_run = classify_ub_probe([(-6, ""), (0, "")])
        self.assertFalse(one_bad_run["trapped"])


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--core-bin",
        default=str(ROOT_DIR / "lean" / ".lake" / "build" / "bin" / "lean-native-core"),
    )
    ap.add_argument("--lli-bin", default=None)
    ap.add_argument("--opt-bin", default=None)
    ap.add_argument("--json-out", default=None)
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        res = unittest.TextTestRunner(verbosity=2).run(
            unittest.defaultTestLoader.loadTestsFromTestCase(SelfTests)
        )
        return 0 if res.wasSuccessful() else 1

    core_bin = Path(args.core_bin)
    if not core_bin.is_file():
        print(f"[FAIL] Missing lean-native-core binary at {core_bin}", file=sys.stderr)
        return 1

    opt_bin = args.opt_bin or find_llvm_tool(["opt-18", "opt"])
    if not opt_bin:
        print("[FAIL] Missing `opt` / `opt-18` binary (install llvm-18)", file=sys.stderr)
        return 1

    lli_candidates = [args.lli_bin] if args.lli_bin else list(iter_llvm_tool_candidates(["lli-18", "lli"]))
    if not lli_candidates:
        print("[FAIL] Missing `lli` / `lli-18` binary (install llvm-18)", file=sys.stderr)
        return 1

    qualifications: list[dict[str, Any]] = []
    engine: dict[str, Any] | None = None
    for cand in lli_candidates:
        q = qualify_lli_engine(cand, opt_bin)
        qualifications.append(q)
        if q["usable"]:
            engine = q
            break

    if engine is None:
        report = {
            "status": "skipped_missing_engine",
            "skipped": True,
            "reason": (
                "no installed lli interpreter is usable for the emitted host-arch IR "
                "(the Lean toolchain does not bundle lli/opt; install llvm >= 18)"
            ),
            "candidates": qualifications,
        }
        if args.json_out:
            Path(args.json_out).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        print("[stage2a-lli-diff] SKIPPED (missing engine): " + report["reason"])
        for q in qualifications:
            print(
                f"  candidate lli={q['lli_bin']} ({q['lli_version'] or 'version unknown'}): {q['reason']}"
            )
        return 0

    lli_bin = engine["lli_bin"]
    report = run_suite(core_bin, lli_bin, opt_bin)
    report["engine_qualification"] = engine
    if args.json_out:
        Path(args.json_out).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    print(
        f"[stage2a-lli-diff] ok={report['ok']} cases={report['cases_checked']} "
        f"vectors={report['vectors_checked']} mismatches={len(report['mismatches'])} "
        f"neg_mutants_killed={report['negative_mutants_killed']} "
        f"ub_probe_trapped={report['ub_div_zero_probe']['trapped']}"
    )
    if not report["ok"]:
        print(json.dumps(report, indent=2), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
