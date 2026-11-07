#!/usr/bin/env python3
"""Stage 2B: Alive2 (`alive-tv`) Translation Validation Gate.

Validates:
1. Positive lowered/optimized LLVM IR pairs:
   - `lean-native-core compile-llvm --canonical-benchmark -O0` vs `-O3` (including loop CFGs)
   - `lean-native-core compile-llvm --fastcheck-sample -O0` vs `-O3`
   - Typed `LLVMLower.lowerModuleWithFacts` IR vs `opt -passes='default<O2>'`
2. Negative mutant rejection (`M1..M5`):
   - Proves `alive-tv` rejects swapped `sub`, `shl->lshr`, `ult->ule` (64 & 256-bit), and
     unguarded `udiv` (UB on zero divisor).

Also supports `--ensure-alive-tv <cache_dir>` to build `AliveToolkit/alive2` at a pinned
LLVM-18-compatible commit (`2547695358b01758a01f4bdab2ced70178189074`) when not cached.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Any

ROOT_DIR = Path(__file__).resolve().parent.parent
PINNED_ALIVE2_REPO = "https://github.com/AliveToolkit/alive2.git"
PINNED_ALIVE2_COMMIT = "2547695358b01758a01f4bdab2ced70178189074"

SUMMARY_CORRECT_RE = re.compile(r"^\s*(\d+)\s+correct transformations?\b", re.M)
SUMMARY_INCORRECT_RE = re.compile(r"^\s*(\d+)\s+incorrect transformations?\b", re.M)
SUMMARY_FAILED_RE = re.compile(r"^\s*(\d+)\s+failed-to-prove transformations?\b", re.M)
SUMMARY_ALIVE_ERR_RE = re.compile(r"^\s*(\d+)\s+Alive2 errors?\b", re.M)
USER_FN_DEF_RE = re.compile(r"^define\s+dso_local\b[^\n]*?@([A-Za-z0-9_.$]+)\s*\(", re.M)
USER_FN_BLOCK_RE = re.compile(
    r"^define\s+dso_local\b[^\n]*?@([A-Za-z0-9_.$]+)\s*\([^{]*\{.*?\n\}",
    re.M | re.S,
)
CALL_CALLEE_RE = re.compile(r"\bcall\b[^\n@]*@([A-Za-z0-9_.$]+)\s*\(")
UNSUPPORTED_ALIVE2_TYPE_RE = re.compile(r"\bi512\b")
SAFE_INLINED_HELPERS = frozenset({"lean_native_box_u64", "lean_native_unbox_u64"})


def extract_user_functions(ir_text: str) -> list[str]:
    """Extract compiled LNIR user/ABI function names (`define dso_local ... @fn(`),
    skipping `define weak_odr dso_local` runtime/atomic/intrinsics helpers."""
    seen: dict[str, None] = {}
    for m in USER_FN_DEF_RE.finditer(ir_text):
        seen.setdefault(m.group(1), None)
    return list(seen.keys())


def extract_alive2_supported_functions(ir_text: str) -> list[str]:
    """Extract `define dso_local` functions supported by per-function `alive-tv` checking:
    excludes functions using `i512` arithmetic or external runtime/trap calls (while allowing
    pure `weak_odr` tagging helpers in `SAFE_INLINED_HELPERS` that are inlined before TV)."""
    supported: list[str] = []
    seen: set[str] = set()
    for m in USER_FN_BLOCK_RE.finditer(ir_text):
        fn_name = m.group(1)
        body = m.group(0)
        if fn_name in seen:
            continue
        seen.add(fn_name)
        if UNSUPPORTED_ALIVE2_TYPE_RE.search(body):
            continue
        callees = {cm.group(1) for cm in CALL_CALLEE_RE.finditer(body)}
        if not callees.issubset(SAFE_INLINED_HELPERS):
            continue
        supported.append(fn_name)
    return supported


def inline_pure_helpers_for_tv(opt_bin: str, src_ll: Path, out_ll: Path) -> None:
    """Strip `noinline`/`optnone` on baseline IR and run `inline,dce` so pure `weak_odr`
    tagging helpers (`@lean_native_box_u64`) are inlined prior to per-function `alive-tv`."""
    raw = src_ll.read_text(encoding="utf-8")
    relaxed = re.sub(r"\b(?:noinline|optnone)\s*", "", raw)
    out_ll.write_text(relaxed, encoding="utf-8")
    subprocess.run(
        [opt_bin, "-S", "-passes=inline,dce", str(out_ll), "-o", str(out_ll)],
        check=True,
        capture_output=True,
        text=True,
    )


def find_tool(names: list[str]) -> str | None:
    for name in names:
        override = os.environ.get(name.upper().replace("-", "_"))
        if override and Path(override).is_file():
            return override
        found = shutil.which(name)
        if found:
            return found
    for ver in ("18", "19", "17", "20"):
        for base in names:
            cand = f"/usr/lib/llvm-{ver}/bin/{base}"
            if Path(cand).is_file() and os.access(cand, os.X_OK):
                return cand
    return None


def parse_alive_tv_output(stdout: str, stderr: str, returncode: int) -> dict[str, Any]:
    combined = stdout + "\n" + stderr
    m_corr = SUMMARY_CORRECT_RE.search(combined)
    m_inc = SUMMARY_INCORRECT_RE.search(combined)
    m_fail = SUMMARY_FAILED_RE.search(combined)
    m_err = SUMMARY_ALIVE_ERR_RE.search(combined)
    correct = int(m_corr.group(1)) if m_corr else 0
    incorrect = int(m_inc.group(1)) if m_inc else 0
    failed = int(m_fail.group(1)) if m_fail else 0
    errors = int(m_err.group(1)) if m_err else 0
    verified = (
        returncode == 0
        and m_corr is not None
        and correct >= 1
        and incorrect == 0
        and failed == 0
        and errors == 0
    )
    rejected = (
        errors == 0
        and failed == 0
        and m_inc is not None
        and incorrect >= 1
        and "Transformation doesn't verify!" in combined
    )
    return {
        "returncode": returncode,
        "correct": correct,
        "incorrect": incorrect,
        "failed_to_prove": failed,
        "alive2_errors": errors,
        "verified": verified,
        "rejected": rejected,
    }


def ensure_alive_tv(cache_dir: Path, llvm_dir: str | None = None) -> Path:
    bin_path = cache_dir / "bin" / "alive-tv"
    stamp_path = cache_dir / "bin" / "alive-tv.commit"
    if (
        bin_path.is_file()
        and os.access(bin_path, os.X_OK)
        and stamp_path.is_file()
        and stamp_path.read_text(encoding="utf-8").strip() == PINNED_ALIVE2_COMMIT
    ):
        probe = subprocess.run([str(bin_path), "--version"], capture_output=True, text=True)
        if probe.returncode == 0:
            return bin_path

    if llvm_dir is None:
        for cand in (
            "/usr/lib/llvm-18/lib/cmake/llvm",
            "/usr/lib/llvm-19/lib/cmake/llvm",
            "/usr/lib/cmake/llvm",
        ):
            if Path(cand).is_dir():
                llvm_dir = cand
                break
    if not llvm_dir:
        raise RuntimeError("Could not locate LLVMConfig.cmake (install llvm-18-dev)")

    cache_dir.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="alive2-build-") as tmp_dir:
        src_dir = Path(tmp_dir) / "alive2-src"
        bld_dir = Path(tmp_dir) / "alive2-build"
        subprocess.run(["git", "init", "-q", str(src_dir)], check=True)
        subprocess.run(
            ["git", "-C", str(src_dir), "remote", "add", "origin", PINNED_ALIVE2_REPO],
            check=True,
        )
        subprocess.run(
            ["git", "-C", str(src_dir), "fetch", "--depth", "1", "origin", PINNED_ALIVE2_COMMIT],
            check=True,
        )
        subprocess.run(
            ["git", "-C", str(src_dir), "checkout", "-q", "FETCH_HEAD"],
            check=True,
        )
        head_sha = (
            subprocess.check_output(["git", "-C", str(src_dir), "rev-parse", "HEAD"])
            .decode()
            .strip()
        )
        if head_sha != PINNED_ALIVE2_COMMIT:
            raise RuntimeError(f"Pinned Alive2 SHA mismatch: {head_sha} != {PINNED_ALIVE2_COMMIT}")

        # Ubuntu's packaged llvm-18-dev sets LLVM_ENABLE_EH=OFF in LLVMConfig.cmake while
        # LLVM_ENABLE_RTTI=ON, causing AddLLVM.cmake's `add_llvm_executable(alive-tv ...)` to
        # append `-fno-exceptions` *after* CMAKE_CXX_FLAGS. Relax the CMake configure guard and
        # force `LLVM_ENABLE_EH=ON` + explicit `-fexceptions` on `alive-tv` (which uses `try/catch`).
        cmake_file = src_dir / "CMakeLists.txt"
        cmake_txt = cmake_file.read_text(encoding="utf-8")
        cmake_txt = cmake_txt.replace(
            '  if (NOT LLVM_ENABLE_EH)\n    message(FATAL_ERROR "LLVM must be built with \'-DLLVM_ENABLE_EH=ON\'")\n  endif()',
            '  set(LLVM_ENABLE_EH ON)\n  set(LLVM_REQUIRES_EH ON)',
        )
        cmake_txt = cmake_txt.replace(
            '  add_llvm_executable(alive-tv\n    "tools/alive-tv.cpp"\n  )',
            '  add_llvm_executable(alive-tv\n    "tools/alive-tv.cpp"\n  )\n  target_compile_options(alive-tv PRIVATE -fexceptions -frtti)',
        )
        cmake_file.write_text(cmake_txt, encoding="utf-8")

        # GCC 13/14+ libstdc++ (Ubuntu 24.04) removed transitive <algorithm>/<cstdint>/<limits>/<numeric>
        # includes that Alive2's pinned LLVM-18 snapshot relied on. Pre-including those four standard
        # headers keeps every Alive2 translation unit compiling cleanly without patching upstream sources.
        cxx_flags = (
            "-fexceptions -frtti -Wno-error "
            "-include algorithm -include cstdint -include limits -include numeric"
        )
        cmake_cmd = [
            "cmake",
            "-GNinja",
            "-S",
            str(src_dir),
            "-B",
            str(bld_dir),
            "-DCMAKE_BUILD_TYPE=Release",
            "-DBUILD_LLVM_UTILS=ON",
            "-DBUILD_TV=OFF",
            f"-DLLVM_DIR={llvm_dir}",
            f"-DCMAKE_CXX_FLAGS={cxx_flags}",
        ]
        subprocess.run(cmake_cmd, check=True)
        jobs = str(min(os.cpu_count() or 2, 8))
        subprocess.run(["ninja", "-C", str(bld_dir), "-j", jobs, "alive-tv"], check=True)
        built = bld_dir / "alive-tv"
        if not built.is_file():
            raise RuntimeError(f"Expected {built} after ninja build")
        (cache_dir / "bin").mkdir(parents=True, exist_ok=True)
        shutil.copy2(built, bin_path)
        bin_path.chmod(0o755)
        stamp_path.write_text(PINNED_ALIVE2_COMMIT + "\n", encoding="utf-8")
    return bin_path


def run_alive_pair(
    alive_tv: str,
    src_path: Path,
    tgt_path: Path,
    extra_flags: list[str] | None = None,
    disable_undef_input: bool = False,
) -> dict[str, Any]:
    flags = [
        "--smt-to=20000",
        "--src-unroll=4",
        "--tgt-unroll=4",
        *(["--disable-undef-input"] if disable_undef_input else []),
        *(extra_flags or []),
    ]
    proc = subprocess.run(
        [alive_tv, *flags, str(src_path), str(tgt_path)],
        capture_output=True,
        text=True,
        timeout=90,
    )
    parsed = parse_alive_tv_output(proc.stdout, proc.stderr, proc.returncode)
    parsed["stdout_tail"] = proc.stdout[-1200:]
    parsed["stderr_tail"] = proc.stderr[-600:]
    return parsed


def run_suite(core_bin: Path, alive_tv: str, opt_bin: str) -> dict[str, Any]:
    fx_proc = subprocess.run(
        [str(core_bin), "llvm-diff-suite", "--alive2-fixtures"],
        capture_output=True,
        text=True,
        timeout=60,
        check=True,
    )
    fixtures = json.loads(fx_proc.stdout)

    positive_results: list[dict[str, Any]] = []
    negative_results: list[dict[str, Any]] = []

    with tempfile.TemporaryDirectory(prefix="tl-alive2-tv-") as tmp_dir:
        tmp = Path(tmp_dir)

        # 1. Pipeline pairs: compile-llvm --baseline vs -O3 on canonical benchmark & fastcheck sample
        for corpus_flag, label in (
            ("--canonical-benchmark", "pipeline_canonical_O0_vs_O3"),
            ("--fastcheck-sample", "pipeline_fastcheck_O0_vs_O3"),
        ):
            raw_src_ll = tmp / f"{label}_raw_src.ll"
            src_ll = tmp / f"{label}_src.ll"
            tgt_ll = tmp / f"{label}_tgt.ll"
            subprocess.run(
                [str(core_bin), "compile-llvm", corpus_flag, "--baseline", "-o", str(raw_src_ll)],
                check=True,
                capture_output=True,
                text=True,
            )
            subprocess.run(
                [str(core_bin), "compile-llvm", corpus_flag, "-O3", "-o", str(tgt_ll)],
                check=True,
                capture_output=True,
                text=True,
            )
            inline_pure_helpers_for_tv(opt_bin, raw_src_ll, src_ll)
            # Pipeline --baseline vs -O3 lowers pure LNIR functions whose ABI entry points receive
            # well-defined scalar/pointer arguments from the Lean runtime/C-ABI boundary.
            # Scope `--func` to Alive2-supported `define dso_local` functions (excluding `i512`
            # arithmetic and external storage/heap runtime calls that Alive2 cannot model).
            src_fns = extract_alive2_supported_functions(src_ll.read_text(encoding="utf-8"))
            tgt_fns = set(extract_alive2_supported_functions(tgt_ll.read_text(encoding="utf-8")))
            shared_fns = [fn for fn in src_fns if fn in tgt_fns]
            if not shared_fns:
                raise RuntimeError(f"No Alive2-supported user functions found in {label}")
            fn_flags = [f"--func={fn}" for fn in shared_fns]
            res = run_alive_pair(
                alive_tv,
                src_ll,
                tgt_ll,
                extra_flags=fn_flags,
                disable_undef_input=True,
            )
            res["id"] = label
            res["checked_functions"] = shared_fns
            positive_results.append(res)

        # 2. Lowered LNIR -> LLVMAst modules vs LLVM `opt` passes
        # `LLVMAst.Eval` models `PoisonOr Val` (determined bitvectors + poison, without `undef`),
        # matching `compile-llvm`'s `noundef` ABI boundary via `--disable-undef-input`.
        for item in fixtures["loweredPositives"]:
            pid = f"opt_O2_{item['id']}"
            src_ll = tmp / f"{pid}_src.ll"
            tgt_ll = tmp / f"{pid}_tgt.ll"
            src_ll.write_text(item["srcIr"], encoding="utf-8")
            opt_passes = item.get("optPasses", "default<O2>")
            subprocess.run(
                [opt_bin, "-S", f"-passes={opt_passes}", str(src_ll), "-o", str(tgt_ll)],
                check=True,
                capture_output=True,
                text=True,
            )
            res = run_alive_pair(alive_tv, src_ll, tgt_ll, disable_undef_input=True)
            res["id"] = pid
            res["opt_passes"] = opt_passes
            positive_results.append(res)

        # 3. Negative mutant rejection (M1..M5): alive-tv MUST reject every mutant
        for mut in fixtures["negativeMutants"]:
            mid = mut["id"]
            src_ll = tmp / f"{mid}_src.ll"
            tgt_ll = tmp / f"{mid}_tgt.ll"
            src_ll.write_text(mut["srcIr"], encoding="utf-8")
            tgt_ll.write_text(mut["tgtIr"], encoding="utf-8")
            res = run_alive_pair(alive_tv, src_ll, tgt_ll, disable_undef_input=True)
            res["id"] = mid
            res["description"] = mut["description"]
            negative_results.append(res)

    pos_failures = [r for r in positive_results if not r["verified"]]
    neg_survivors = [r for r in negative_results if not r["rejected"]]
    ok = (
        len(positive_results) >= 7
        and len(pos_failures) == 0
        and len(negative_results) >= 5
        and len(neg_survivors) == 0
    )
    return {
        "ok": ok,
        "alive_tv": alive_tv,
        "opt_bin": opt_bin,
        "pinned_alive2_commit": PINNED_ALIVE2_COMMIT,
        "positives_checked": len(positive_results),
        "positive_failures": pos_failures,
        "positive_summaries": [
            {"id": r["id"], "correct": r["correct"], "verified": r["verified"]}
            for r in positive_results
        ],
        "negatives_checked": len(negative_results),
        "negative_survivors": neg_survivors,
        "negative_summaries": [
            {
                "id": r["id"],
                "incorrect": r["incorrect"],
                "rejected": r["rejected"],
            }
            for r in negative_results
        ],
    }


class SelfTests(unittest.TestCase):
    def test_parse_verified_summary(self) -> None:
        sample_ok = """
Summary:
  8 correct transformations
  0 incorrect transformations
  0 failed-to-prove transformations
  0 Alive2 errors
"""
        d = parse_alive_tv_output(sample_ok, "", 0)
        self.assertTrue(d["verified"])
        self.assertFalse(d["rejected"])
        self.assertEqual(d["correct"], 8)

    def test_parse_rejected_summary(self) -> None:
        sample_bad = """
Transformation doesn't verify!
ERROR: Value mismatch

Summary:
  0 correct transformations
  1 incorrect transformations
  0 failed-to-prove transformations
  0 Alive2 errors
"""
        for rc in (0, 1):
            d = parse_alive_tv_output(sample_bad, "", rc)
            self.assertFalse(d["verified"])
            self.assertTrue(d["rejected"])
            self.assertEqual(d["incorrect"], 1)

    def test_extract_user_functions_skips_weak_odr_helpers(self) -> None:
        sample_ir = (
            "define weak_odr dso_local void @lean_inc_ref_n(ptr %obj, i64 %n) #0 {\n"
            "define dso_local i64 @collatz_steps(i64 noundef %v0, i64 noundef %v1) #0 {\n"
            "define dso_local ptr @lean_native_abi_collatz_steps(ptr %a, ptr %b) #0 {\n"
        )
        self.assertEqual(
            extract_user_functions(sample_ir),
            ["collatz_steps", "lean_native_abi_collatz_steps"],
        )

    def test_extract_alive2_supported_functions_filters_i512_and_extern_calls(self) -> None:
        sample_ir = (
            "define dso_local i64 @collatz_steps(i64 noundef %v0, i64 noundef %v1) #0 {\n"
            "entry:\n  ret i64 %v0\n}\n\n"
            "define dso_local i64 @tuple_accum_sum(i64 noundef %v0, i64 noundef %v1) #1 {\n"
            "entry:\n  %b = call ptr @lean_native_box_u64(i64 %v0)\n  ret i64 %v1\n}\n\n"
            "define dso_local i256 @evm_muldiv_wad_u256(i256 %a, i256 %b, i256 %w) #0 {\n"
            "entry:\n  %z = zext i256 %a to i512\n  ret i256 %a\n}\n\n"
            "define dso_local ptr @sarray_scale_bias(ptr %arr, i64 %s, i64 %b) #0 {\n"
            "entry:\n  %e = call ptr @lean_native_ensure_exclusive(ptr %arr)\n  ret ptr %e\n}\n"
        )
        self.assertEqual(
            extract_alive2_supported_functions(sample_ir),
            ["collatz_steps", "tuple_accum_sum"],
        )

    def test_parse_error_is_not_clean_rejection(self) -> None:
        sample_err = """
ERROR: Could not parse IR
Summary:
  0 correct transformations
  1 incorrect transformations
  0 failed-to-prove transformations
  1 Alive2 errors
"""
        d = parse_alive_tv_output(sample_err, "", 1)
        self.assertFalse(d["verified"])
        self.assertFalse(d["rejected"])
        self.assertEqual(d["alive2_errors"], 1)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--core-bin",
        default=str(ROOT_DIR / "lean" / ".lake" / "build" / "bin" / "lean-native-core"),
    )
    ap.add_argument("--alive-tv", default=None)
    ap.add_argument("--ensure-alive-tv", default=None, help="Build/cache alive-tv in directory")
    ap.add_argument("--llvm-dir", default=None)
    ap.add_argument("--opt-bin", default=None)
    ap.add_argument("--json-out", default=None)
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        res = unittest.TextTestRunner(verbosity=2).run(
            unittest.defaultTestLoader.loadTestsFromTestCase(SelfTests)
        )
        return 0 if res.wasSuccessful() else 1

    alive_tv = args.alive_tv
    if args.ensure_alive_tv:
        alive_tv = str(ensure_alive_tv(Path(args.ensure_alive_tv), args.llvm_dir))
    if not alive_tv:
        alive_tv = find_tool(["alive-tv"])
    if not alive_tv:
        print(
            "[FAIL] Missing `alive-tv` binary (pass --alive-tv or --ensure-alive-tv <cache_dir>)",
            file=sys.stderr,
        )
        return 1

    core_bin = Path(args.core_bin)
    if not core_bin.is_file():
        print(f"[FAIL] Missing lean-native-core binary at {core_bin}", file=sys.stderr)
        return 1

    opt_bin = args.opt_bin or find_tool(["opt-18", "opt"])
    if not opt_bin:
        print("[FAIL] Missing `opt` / `opt-18` binary", file=sys.stderr)
        return 1

    report = run_suite(core_bin, alive_tv, opt_bin)
    if args.json_out:
        Path(args.json_out).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    print(
        f"[stage2b-alive2-tv] ok={report['ok']} "
        f"positives={report['positives_checked']} (failures={len(report['positive_failures'])}) "
        f"negatives={report['negatives_checked']} (survivors={len(report['negative_survivors'])})"
    )
    if not report["ok"]:
        print(json.dumps(report, indent=2), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
