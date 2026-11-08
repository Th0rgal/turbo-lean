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
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Any

ROOT_DIR = Path(__file__).resolve().parent.parent


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


def run_ub_probe_lli(lli_bin: str) -> dict[str, Any]:
    """Negative UB probe: division by zero under `lli --force-interpreter` must trap/abort rather
    than silently succeeding with a normal 0..255 exit status across byte slices."""
    ub_ir = """target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"
define i32 @main(i32 %argc, ptr %argv) {
entry:
  %z = sub i32 %argc, %argc
  %q = udiv i32 42, %z
  ret i32 %q
}
"""
    with tempfile.TemporaryDirectory(prefix="tl-lli-ub-") as tmp:
        p = Path(tmp) / "ub_div_zero.ll"
        p.write_text(ub_ir, encoding="utf-8")
        proc = subprocess.run(
            [lli_bin, "--force-interpreter", str(p)],
            capture_output=True,
            text=True,
            timeout=15,
        )
        trapped = proc.returncode < 0 or proc.returncode >= 128 or "ERROR" in proc.stderr
        return {
            "trapped": trapped,
            "returncode": proc.returncode,
            "stderr": proc.stderr.strip()[:240],
        }


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

    lli_bin = args.lli_bin or find_llvm_tool(["lli-18", "lli"])
    if not lli_bin:
        print("[FAIL] Missing `lli` / `lli-18` binary (install llvm-18)", file=sys.stderr)
        return 1

    opt_bin = args.opt_bin or find_llvm_tool(["opt-18", "opt"])
    if not opt_bin:
        print("[FAIL] Missing `opt` / `opt-18` binary (install llvm-18)", file=sys.stderr)
        return 1
    report = run_suite(core_bin, lli_bin, opt_bin)
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
