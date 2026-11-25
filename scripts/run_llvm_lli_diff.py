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

sys.path.insert(0, str(Path(__file__).resolve().parent))
import host_arch  # noqa: E402

ROOT_DIR = Path(__file__).resolve().parent.parent

# `(llvm triple, datalayout)` per Lean `TargetArch` spelling, mirroring the
# Rust-side `builtin_fastcheck_cpu_target` (crates/turbo-lean/src/gpu_fastcheck.rs)
# and the Lean-side `TargetArch.llvmTriple` / `TargetArch.dataLayout` constants
# (lean/LeanNative/IR/Types.lean).
HOST_CPU_TARGETS: dict[str, tuple[str, str]] = {
    "x86_64": (
        "x86_64-unknown-linux-gnu",
        "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128",
    ),
    "arm64": (
        "aarch64-unknown-linux-gnu",
        "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128",
    ),
}


def host_llvm_cpu_target() -> tuple[str, str, str]:
    """`(lean --arch spelling, llvm triple, datalayout)` for the host CPU.
    Raises on machines with no native-emission support (see host_arch)."""
    arch = host_arch.host_target_arch()
    triple, datalayout = HOST_CPU_TARGETS[arch]
    return arch, triple, datalayout


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


UB_PROBE_DEFINED_RESULT = 90


def build_ub_probe_ir() -> str:
    """Host-arch udiv-by-zero probe module (triple/datalayout from `HOST_CPU_TARGETS`).
    `@main` returns `%q + UB_PROBE_DEFINED_RESULT`: x86_64 traps at the udiv before
    the add, and AArch64's defined zero quotient makes the exit status exactly the
    sentinel, so a garbage-exit interpreter returning 0 for UB does not qualify."""
    _, triple, datalayout = host_llvm_cpu_target()
    return f"""target datalayout = "{datalayout}"
target triple = "{triple}"
define i32 @main(i32 %argc, ptr %argv) {{
entry:
  %z = sub i32 %argc, %argc
  %q = udiv i32 42, %z
  %r = add i32 %q, {UB_PROBE_DEFINED_RESULT}
  ret i32 %r
}}
"""


def classify_ub_probe(outcomes: list[tuple[int, str]], machine: str | None = None) -> dict[str, Any]:
    """Classify repeated UB-probe runs against the HOST's expectation.

    Trap evidence is a signal (`rc < 0`) or an explicit `ERROR` diagnostic on
    stderr, on EVERY run. On x86_64 a plain exit status proves nothing: the
    interpreter's native division raises SIGFPE, and anything else is `@main`'s
    garbage value (measured on LLVM 15 `lli`: rc 80/96/64/48/128/0 for one input),
    so even `rc >= 128` is a coin flip, not a trap. AArch64 DEFINES integer
    division by zero as 0, so a release-build `lli` there deterministically exits
    with the probe's sentinel (`0 + UB_PROBE_DEFINED_RESULT`) without trapping;
    that exact outcome conforms on aarch64 hosts, as does a deterministic trap
    from an assertions-enabled build. A steady 0 does NOT conform anywhere: 0 sat
    in the measured garbage set."""
    if machine is None:
        machine = platform.machine().lower()
    rcs = [rc for rc, _ in outcomes]
    trapped_each = [rc < 0 or "ERROR" in stderr for rc, stderr in outcomes]
    trapped = bool(trapped_each) and all(trapped_each)
    deterministic = len(set(rcs)) == 1 and len(set(trapped_each)) == 1
    if machine in ("aarch64", "arm64"):
        expectation = (
            "a deterministic trap, or the defined result (udiv-by-zero quotient 0 + "
            f"{UB_PROBE_DEFINED_RESULT} = exit {UB_PROBE_DEFINED_RESULT}), on every run"
        )
        conforming = deterministic and (
            trapped or all(rc == UB_PROBE_DEFINED_RESULT for rc in rcs)
        )
    else:
        expectation = "a deterministic trap (signal or ERROR diagnostics) on every run"
        conforming = deterministic and trapped
    return {
        "trapped": trapped,
        "deterministic": deterministic,
        "conforming": conforming,
        "expectation": expectation,
        "machine": machine,
        "returncodes": rcs,
        "stderr": outcomes[-1][1].strip()[:240] if outcomes else "",
    }


def run_ub_probe_lli(lli_bin: str, runs: int = 2) -> dict[str, Any]:
    """Negative UB probe: division by zero under `lli --force-interpreter` must meet the
    host expectation deterministically (a trap on x86_64; a trap or the defined sentinel
    exit on AArch64). An arbitrary 0..255 status proves nothing."""
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
      3. the udiv-by-zero UB probe meets the host expectation deterministically
         (a trap on x86_64; a trap or the defined sentinel exit on AArch64); an
         interpreter that reports a garbage exit value for UB disqualifies itself
         rather than yielding a coin-flip verdict."""
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
    except RuntimeError as exc:
        # host_arch.host_target_arch() raises on unsupported machines; surface it
        # as this candidate's named reason (run_gpu_tpu_diff's shape), never a
        # traceback out of a caller that only wanted ptx/metal legs.
        result["reason"] = f"host qualification unavailable: {exc}"
        return result
    result["ub_div_zero_probe"] = probe
    if not probe["conforming"]:
        result["reason"] = (
            f"udiv-by-zero probe did not meet the host expectation ({probe['expectation']}): "
            f"returncodes={probe['returncodes']}, stderr={probe['stderr'] or '<empty>'}"
        )
        return result
    result["usable"] = True
    return result


def sibling_opt_for_lli(lli_bin: str) -> str | None:
    """The `opt` from the SAME LLVM install as `lli_bin`: same directory, same
    version suffix (`/usr/lib/llvm-18/bin/lli` -> `.../opt`, `/usr/bin/lli-18`
    -> `/usr/bin/opt-18`). Mixing installs would let an old `opt` verify modules
    a newer `lli` runs (or the reverse), so the pair is selected together."""
    p = Path(lli_bin)
    if not p.name.startswith("lli"):
        return None
    cand = p.with_name("opt" + p.name[len("lli"):])
    if cand.is_file() and os.access(str(cand), os.X_OK):
        return str(cand)
    return None


def find_qualified_llvm_engine(
    lli_override: str | None = None,
    opt_override: str | None = None,
) -> tuple[dict[str, Any] | None, list[dict[str, Any]]]:
    """One selector for every stage that interprets the emitted IR: the first
    `lli` that passes `qualify_lli_engine` together with the `opt` of the same
    LLVM install. Returns `(engine, rejected)`. An override pins the candidate
    set to exactly that pair, so a named binary that fails qualification comes
    back as `(None, [its qualification record])` for the caller to FAIL on."""
    if lli_override or opt_override:
        lli = lli_override or find_llvm_tool(["lli-18", "lli"])
        opt = opt_override or (sibling_opt_for_lli(lli) if lli else None) or find_llvm_tool(["opt-18", "opt"])
        if not lli or not opt:
            return None, [{
                "lli_bin": lli,
                "opt_bin": opt,
                "usable": False,
                "reason": "explicit engine selection incomplete: lli or opt not found",
            }]
        q = qualify_lli_engine(lli, opt)
        return (q if q["usable"] else None), [q]
    rejected: list[dict[str, Any]] = []
    for lli in iter_llvm_tool_candidates(["lli-18", "lli-19", "lli", "lli-17", "lli-20"]):
        opt = sibling_opt_for_lli(lli)
        if not opt:
            rejected.append({
                "lli_bin": lli,
                "opt_bin": None,
                "usable": False,
                "reason": "no opt in the same LLVM install (same directory, same version suffix)",
            })
            continue
        q = qualify_lli_engine(lli, opt)
        if q["usable"]:
            return q, rejected
        rejected.append(q)
    return None, rejected


def llvm_strict_tools_default() -> bool:
    """Missing-engine states FAIL instead of skipping when
    TURBO_LLI_DIFF_STRICT_TOOLS is true. The roadmap contract step (which
    provisions llvm-18) sets it explicitly in its workflow env; there is no
    implicit CI default, because the impact-gate jobs run the self-tests on
    runners with no LLVM install."""
    return host_arch.strict_tools_default("TURBO_LLI_DIFF_STRICT_TOOLS")


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
        and bool(ub_probe["conforming"])
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
        # Measured on LLVM 15 lli (x86_64): udiv-by-zero returned rc 80/96/64/48/128/0
        # for one input, so a bare exit status (even >= 128) must never read as a trap.
        garbage_flip = classify_ub_probe([(128, ""), (0, "")], machine="x86_64")
        self.assertFalse(garbage_flip["trapped"])
        self.assertFalse(garbage_flip["deterministic"])
        self.assertFalse(garbage_flip["conforming"])
        stable_garbage = classify_ub_probe([(160, ""), (160, "")], machine="x86_64")
        self.assertFalse(stable_garbage["trapped"])
        self.assertTrue(stable_garbage["deterministic"])
        self.assertFalse(stable_garbage["conforming"])
        signal_trap = classify_ub_probe([(-6, ""), (-6, "")], machine="x86_64")
        self.assertTrue(signal_trap["trapped"])
        self.assertTrue(signal_trap["deterministic"])
        self.assertTrue(signal_trap["conforming"])
        error_trap = classify_ub_probe(
            [(70, "LLVM ERROR: divide by zero"), (70, "LLVM ERROR: divide by zero")],
            machine="x86_64",
        )
        self.assertTrue(error_trap["trapped"])
        self.assertTrue(error_trap["conforming"])
        one_bad_run = classify_ub_probe([(-6, ""), (0, "")], machine="x86_64")
        self.assertFalse(one_bad_run["trapped"])
        self.assertFalse(one_bad_run["conforming"])

    def test_ub_probe_conformance_is_arch_aware_on_aarch64(self) -> None:
        # AArch64 defines integer division by zero as 0 (no trap), and the probe
        # adds UB_PROBE_DEFINED_RESULT to the quotient before returning, so a
        # release lli interpreter deterministically exits with exactly that
        # sentinel there; that engine is usable.
        defined = classify_ub_probe(
            [(UB_PROBE_DEFINED_RESULT, ""), (UB_PROBE_DEFINED_RESULT, "")], machine="aarch64"
        )
        self.assertFalse(defined["trapped"])
        self.assertTrue(defined["conforming"])
        # An assertions-enabled aarch64 lli that aborts is also usable.
        self.assertTrue(classify_ub_probe([(-6, ""), (-6, "")], machine="aarch64")["conforming"])
        # A garbage-exit interpreter that returns 0 for UB must NOT qualify: the
        # sentinel exists so the defined result is distinguishable from the 0
        # that sat in the measured LLVM 15 garbage set.
        self.assertFalse(classify_ub_probe([(0, ""), (0, "")], machine="aarch64")["conforming"])
        # Nondeterminism, or a stable value other than the sentinel, is not usable.
        self.assertFalse(
            classify_ub_probe(
                [(UB_PROBE_DEFINED_RESULT, ""), (128, "")], machine="arm64"
            )["conforming"]
        )
        self.assertFalse(classify_ub_probe([(64, ""), (64, "")], machine="aarch64")["conforming"])
        # On x86_64 the division traps, so a plain sentinel exit stays rejected.
        self.assertFalse(
            classify_ub_probe(
                [(UB_PROBE_DEFINED_RESULT, ""), (UB_PROBE_DEFINED_RESULT, "")], machine="x86_64"
            )["conforming"]
        )
        # The sentinel appears in the emitted probe IR after the udiv.
        self.assertIn(f"add i32 %q, {UB_PROBE_DEFINED_RESULT}", build_ub_probe_ir())


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

    engine, rejected = find_qualified_llvm_engine(args.lli_bin, args.opt_bin)

    if engine is None:
        if not rejected:
            print("[FAIL] Missing `lli` / `lli-18` binary (install llvm-18)", file=sys.stderr)
            return 1
        explicit = bool(args.lli_bin or args.opt_bin)
        strict = llvm_strict_tools_default()
        hard_fail = explicit or strict
        report = {
            "status": "failed_missing_engine" if hard_fail else "skipped_missing_engine",
            "skipped": not hard_fail,
            "strict": strict,
            "explicit_engine_args": explicit,
            "reason": (
                "no lli/opt pair (same LLVM install) passed qualification for the emitted "
                "host-arch IR; the measured per-candidate causes follow (the Lean toolchain "
                "does not bundle lli/opt; the CI jobs install llvm-18)"
            ),
            "candidates": rejected,
        }
        if args.json_out:
            Path(args.json_out).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        head = "FAILED" if hard_fail else "SKIPPED"
        why = (
            " for explicitly named engine args" if explicit
            else (" under strict mode" if strict else "")
        )
        print(f"[stage2a-lli-diff] {head} (missing engine{why}): " + report["reason"])
        for q in rejected:
            ver = q.get("lli_version") or "version unknown"
            print(f"  candidate lli={q.get('lli_bin')} opt={q.get('opt_bin')} ({ver}): {q.get('reason')}")
        return 1 if hard_fail else 0

    report = run_suite(core_bin, engine["lli_bin"], engine["opt_bin"])
    report["engine_qualification"] = engine
    if args.json_out:
        Path(args.json_out).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    print(
        f"[stage2a-lli-diff] ok={report['ok']} cases={report['cases_checked']} "
        f"vectors={report['vectors_checked']} mismatches={len(report['mismatches'])} "
        f"neg_mutants_killed={report['negative_mutants_killed']} "
        f"ub_probe_conforming={report['ub_div_zero_probe']['conforming']}"
    )
    if not report["ok"]:
        print(json.dumps(report, indent=2), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
