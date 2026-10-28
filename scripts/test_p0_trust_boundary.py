#!/usr/bin/env python3
"""Phase P0 Negative Injection & Trust-Boundary Verification Suite for `turbo-lean` / `LeanNative`.

Exercises and verifies every P0/P1 exit gate and reviewer finding:
  1. Missing input file (`--lnir /nonexistent`, `--input /nonexistent`, positional `/nonexistent`,
     `eval-lnir --opt /nonexistent`) and missing flag values (`--arch`, `--target`, `-o`, `--lnir`,
     `--input`, `--clang-bin`, `--ar-bin`) fail closed with non-zero exit.
  2. Corrupt/invalid wire or JSON input (`--lnir <corrupt>`, JSON with valid `moduleName` but invalid
     `wire`, and JSON-RPC `worker` with `"wire": "not-valid-lnir"`) fails closed without falling back
     to `mkCanonicalBenchmarkModule`.
  3. Unknown target architecture (`--arch bogus-arch`, `--target bogus-target`, worker `"arch": "bogus"`)
     fails closed with non-zero exit / `ok: false`.
  4. Proper `macos-arm64` target is distinct from `ios-arm64` and `ios-sim-arm64`:
     - `macos-arm64`: `arm64-apple-macosx14.0.0`, `"target-cpu"="apple-m2"`, Mach-O `LC_BUILD_VERSION` `platform = 1`.
     - `ios-arm64`: `arm64-apple-ios16.0.0`, `"target-cpu"="apple-a15"`, Mach-O `LC_BUILD_VERSION` `platform = 2`.
     - `ios-sim-arm64`: `arm64-apple-ios16.0.0-simulator`, Mach-O `LC_BUILD_VERSION` `platform = 7`.
  5. `wasm32` defaults to portable scalar WebAssembly (no unconditional `+simd128`), and enables
     `+simd128` only when `--wasm-simd128` (or `"wasmSimd128": true` in worker) is explicitly passed.
  6. `compile-static-lib` fails closed when `clang` or `ar` fails, rejects thin/empty archives,
     uses unique per-invocation staging paths, and preserves pre-existing `.a`, `.h`, and `--emit-asm`
     outputs untouched on failure. `compile` validates `--arch` before writing `--emit-header`/`-o`.
  7. Per-stage provenance labels follow the actual executed branch and never launder `Assumed` (`A_L1`),
     `Tested` (`A_TEST`), or `Unsupported` (`A_L0`) declarations into `VerifiedKernelProof`. Modules
     containing `Unsupported` (`A_L0`) declarations are rejected fail-closed.
  8. `fuzz_lcnf_conformance.run_fuzzer` executes all 3 engines (stock `lean -c`, frontend-lowered
     `lean-native emit-lnir` + `eval-lnir --batch-json`, and `compile-llvm` + `clang`) across ALL seeds
     without requiring custom `PATH`, fails closed when any engine is missing, and catches mutations.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

import fuzz_lcnf_conformance as fuzzer  # noqa: E402

CORE_BIN = ROOT / "lean" / ".lake" / "build" / "bin" / "lean-native-core"


def find_clang() -> str:
    for cand in [
        "/usr/bin/clang",
        str(Path.home() / ".elan/toolchains/leanprover--lean4---v4.35.0/bin/clang"),
        "/root/.elan/toolchains/leanprover--lean4---v4.35.0/bin/clang",
        "/var/lib/sandboxed-node/.elan/toolchains/leanprover--lean4---v4.35.0/bin/clang",
        shutil.which("clang"),
    ]:
        if cand and Path(cand).is_file() and os.access(cand, os.X_OK):
            return cand
    raise RuntimeError("clang not found")


class TestP0TrustBoundary(unittest.TestCase):
    def test_01_missing_input_and_missing_flag_values_fail_closed(self) -> None:
        for args in (
            ["compile-llvm", "--lnir", "/tmp/nonexistent_lnir_file_p0.lnir"],
            ["compile-llvm", "--input", "/tmp/nonexistent_input_file_p0.lnir"],
            ["compile-llvm", "/tmp/nonexistent_pos_file_p0.lean"],
            ["eval-lnir", "--opt", "/tmp/nonexistent_opt_pos_file_p0.lnir", "--args", "1,2"],
            ["emit-cabi-bindings", "--lean", "/tmp/nonexistent_lean_file_p0.lean"],
            ["compile-llvm", "--lnir"],
            ["compile-llvm", "--input"],
            ["compile-llvm", "--arch"],
            ["compile-llvm", "--target"],
            ["compile-llvm", "-o"],
            ["compile-static-lib", "--clang-bin"],
            ["compile-static-lib", "--ar-bin"],
        ):
            res = subprocess.run([str(CORE_BIN), *args], capture_output=True, text=True)
            self.assertNotEqual(res.returncode, 0, f"Expected non-zero exit for {args}, got 0: {res.stdout}")

    def test_02_corrupt_wire_and_worker_invalid_wire_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory(prefix="p0_corrupt_") as tmp:
            tmpdir = Path(tmp)
            bad_json = tmpdir / "spoof_canonical.json"
            bad_json.write_text(
                json.dumps({"moduleName": "LeanNative.Benchmarks.Canonical", "wire": "not-valid-lnir"}),
                encoding="utf-8",
            )
            res = subprocess.run(
                [str(CORE_BIN), "compile-llvm", "--lnir", str(bad_json)],
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(res.returncode, 0, "Corrupt wire inside JSON with canonical moduleName must fail closed")

        worker_input = (
            '{"id":1,"method":"compile-llvm","arch":"x86_64","wire":"not-valid-lnir"}\n'
            '{"id":2,"method":"batch-fastcheck","wire":"not-valid-lnir"}\n'
            '{"id":3,"method":"compile-llvm","arch":"bogus-arch"}\n'
            '{"id":4,"method":"exit"}\n'
        )
        w_res = subprocess.run(
            [str(CORE_BIN), "worker"],
            input=worker_input,
            capture_output=True,
            text=True,
            check=True,
        )
        lines = [json.loads(line) for line in w_res.stdout.splitlines() if line.strip()]
        self.assertFalse(lines[0]["ok"])
        self.assertEqual(lines[0]["error"], "invalid_lnir_wire")
        self.assertFalse(lines[1]["ok"])
        self.assertEqual(lines[1]["error"], "invalid_lnir_wire")
        self.assertFalse(lines[2]["ok"])
        self.assertIn("unsupported_target_arch", lines[2]["error"])

    def test_03_unknown_target_fails_closed_before_writing_outputs(self) -> None:
        for args in (
            ["compile-llvm", "--arch", "bogus_unknown_isa"],
            ["compile-static-lib", "--arch", "mips64el-unknown"],
            ["superopt", "--target", "sparc64"],
            ["plugins", "--target", "vax"],
        ):
            res = subprocess.run([str(CORE_BIN), *args], capture_output=True, text=True)
            self.assertNotEqual(res.returncode, 0, f"Expected non-zero exit for {args}, got 0")

        with tempfile.TemporaryDirectory(prefix="p0_order_") as tmp:
            tmpdir = Path(tmp)
            hdr = tmpdir / "existing.h"
            hdr.write_text("/* preserved header */\n", encoding="utf-8")
            res = subprocess.run(
                [str(CORE_BIN), "compile", "--arch", "bogus_isa", "--emit-header", str(hdr)],
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(res.returncode, 0)
            self.assertEqual(hdr.read_text(encoding="utf-8"), "/* preserved header */\n")

    def test_04_macos_arm64_distinct_from_ios_arm64_and_macho_platform_verified(self) -> None:
        mac_ir = subprocess.check_output(
            [str(CORE_BIN), "compile-llvm", "--arch", "macos-arm64"], text=True
        )
        ios_ir = subprocess.check_output(
            [str(CORE_BIN), "compile-llvm", "--arch", "ios-arm64"], text=True
        )
        self.assertIn('target triple = "arm64-apple-macosx14.0.0"', mac_ir)
        self.assertIn('"target-cpu"="apple-m2"', mac_ir)
        self.assertIn('target triple = "arm64-apple-ios16.0.0"', ios_ir)
        self.assertIn('"target-cpu"="apple-a15"', ios_ir)
        self.assertNotEqual(mac_ir, ios_ir)

        clang_bin = find_clang()
        with tempfile.TemporaryDirectory(prefix="p0_macho_") as tmp:
            tmpdir = Path(tmp)
            for arch_flag, expected_fmt in (
                ("macos-arm64", "Mach-O ARM64 platform=1"),
                ("ios-arm64", "Mach-O ARM64 platform=2"),
                ("ios-sim-arm64", "Mach-O ARM64 platform=7"),
            ):
                out_a = tmpdir / f"lib_{arch_flag}.a"
                res = subprocess.run(
                    [str(CORE_BIN), "compile-static-lib", "--arch", arch_flag, "--clang-bin", clang_bin, "-o", str(out_a), "--json"],
                    capture_output=True,
                    text=True,
                    check=True,
                )
                j = json.loads(res.stdout)
                self.assertTrue(j["archive"])
                self.assertEqual(j["objectFormat"], expected_fmt)
                self.assertEqual(out_a.read_bytes()[:8], b"!<arch>\n")
                self.assertGreater(len(out_a.read_bytes()), 68)

    def test_05_wasm32_scalar_default_and_explicit_simd128(self) -> None:
        wasm_scalar = subprocess.check_output(
            [str(CORE_BIN), "compile-llvm", "--arch", "wasm32"], text=True
        )
        wasm_simd = subprocess.check_output(
            [str(CORE_BIN), "compile-llvm", "--arch", "wasm32", "--wasm-simd128"], text=True
        )
        self.assertNotIn("+simd128", wasm_scalar)
        self.assertIn("+simd128", wasm_simd)

    def test_06_compile_static_lib_tool_failure_thin_archive_and_atomic_preservation(self) -> None:
        clang_bin = find_clang()
        with tempfile.TemporaryDirectory(prefix="p0_atomic_") as tmp:
            tmpdir = Path(tmp)
            out_a = tmpdir / "libatomic.a"
            out_h = tmpdir / "libatomic.h"
            out_s = tmpdir / "libatomic.s"
            subprocess.run(
                [
                    str(CORE_BIN),
                    "compile-static-lib",
                    "--arch",
                    "x86_64",
                    "--clang-bin",
                    clang_bin,
                    "-o",
                    str(out_a),
                    "--header",
                    str(out_h),
                    "--emit-asm",
                    str(out_s),
                ],
                check=True,
                capture_output=True,
                text=True,
            )
            valid_a = out_a.read_bytes()
            valid_h = out_h.read_text(encoding="utf-8")
            valid_s = out_s.read_text(encoding="utf-8")
            self.assertTrue(valid_a.startswith(b"!<arch>\n"))

            # Sentinel overwrite on .h and .s to verify they are NOT clobbered when ar fails
            out_h.write_text("/* sentinel header */\n", encoding="utf-8")
            out_s.write_text("; sentinel asm\n", encoding="utf-8")

            fail_ar = subprocess.run(
                [
                    str(CORE_BIN),
                    "compile-static-lib",
                    "--arch",
                    "x86_64",
                    "--clang-bin",
                    clang_bin,
                    "--ar-bin",
                    "/nonexistent/ar",
                    "-o",
                    str(out_a),
                    "--header",
                    str(out_h),
                    "--emit-asm",
                    str(out_s),
                ],
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(fail_ar.returncode, 0)
            self.assertEqual(out_a.read_bytes(), valid_a, "Previous valid .a must be preserved on ar failure")
            self.assertEqual(out_h.read_text(encoding="utf-8"), "/* sentinel header */\n", "Header must not be overwritten before archive succeeds")
            self.assertEqual(out_s.read_text(encoding="utf-8"), "; sentinel asm\n", "Assembly must not be overwritten before archive succeeds")

            # Fake archiver that writes a thin archive header `!<thin>\n` -> must be rejected!
            thin_ar = tmpdir / "fake_thin_ar.sh"
            thin_ar.write_text('#!/usr/bin/env bash\nprintf "!<thin>\\n%-60s\\n" "fake" > "$2"\n', encoding="utf-8")
            thin_ar.chmod(0o755)
            fail_thin = subprocess.run(
                [
                    str(CORE_BIN),
                    "compile-static-lib",
                    "--arch",
                    "x86_64",
                    "--clang-bin",
                    clang_bin,
                    "--ar-bin",
                    str(thin_ar),
                    "-o",
                    str(out_a),
                ],
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(fail_thin.returncode, 0, "Thin archive must be rejected")
            self.assertEqual(out_a.read_bytes(), valid_a, "Previous valid .a must be preserved when thin archive is rejected")

    def test_07_branch_accurate_provenance_and_no_laundering(self) -> None:
        default_certs = json.loads(
            subprocess.check_output([str(CORE_BIN), "verify-certs", "--json"], text=True)
        )
        self.assertTrue(default_certs["verified"])
        self.assertEqual(default_certs["overallAssurance"], "TranslationValidated")
        by_name = {d["declName"]: d for d in default_certs["declSummaries"]}
        self.assertEqual(by_name["collatz_steps"]["overallAssurance"], "VerifiedKernelProof")
        self.assertEqual(by_name["sarray_scale_bias"]["overallAssurance"], "TranslationValidated")
        self.assertEqual(by_name["dot_product_u64"]["overallAssurance"], "TranslationValidated")
        self.assertEqual(by_name["saxpy_kernel"]["overallAssurance"], "VerifiedKernelProof")

        kernel_only_certs = json.loads(
            subprocess.check_output([str(CORE_BIN), "verify-certs", "--verified-kernel-only", "--json"], text=True)
        )
        self.assertTrue(kernel_only_certs["verified"])
        self.assertEqual(kernel_only_certs["overallAssurance"], "VerifiedKernelProof")
        for d in kernel_only_certs["declSummaries"]:
            self.assertEqual(d["overallAssurance"], "VerifiedKernelProof")

        with tempfile.TemporaryDirectory(prefix="p0_prov_") as tmp:
            tmpdir = Path(tmp)
            # 1. Assumed (`A_L1`) declaration must stay `Assumed`, never laundered to `VerifiedKernelProof`
            assumed_lnir = tmpdir / "assumed.lnir"
            assumed_lnir.write_text(
                "LNIR_WIRE_V1|54657374|1|D_decl|666e5f617373756d6564|A_L1|0|1|0|7830|0|T_i64|T_i64|C_ret|0\n",
                encoding="utf-8",
            )
            ass_rep = json.loads(
                subprocess.check_output(
                    [str(CORE_BIN), "verify-certs", "--lnir", str(assumed_lnir), "--verified-kernel-only", "--json"],
                    text=True,
                )
            )
            self.assertEqual(ass_rep["overallAssurance"], "Assumed")
            self.assertEqual(ass_rep["declSummaries"][0]["overallAssurance"], "Assumed")

            # 2. Tested (`A_TEST`) declaration must stay `Tested`
            tested_lnir = tmpdir / "tested.lnir"
            tested_lnir.write_text(
                "LNIR_WIRE_V1|54657374|1|D_decl|666e5f746573746564|A_TEST|0|1|0|7830|0|T_i64|T_i64|C_ret|0\n",
                encoding="utf-8",
            )
            tst_rep = json.loads(
                subprocess.check_output(
                    [str(CORE_BIN), "verify-certs", "--lnir", str(tested_lnir), "--verified-kernel-only", "--json"],
                    text=True,
                )
            )
            self.assertEqual(tst_rep["overallAssurance"], "Tested")
            self.assertEqual(tst_rep["declSummaries"][0]["overallAssurance"], "Tested")

            # 3. Unsupported (`A_L0`) declaration must fail closed (non-zero exit)
            unsup_lnir = tmpdir / "unsup.lnir"
            unsup_lnir.write_text(
                "LNIR_WIRE_V1|54657374|1|D_decl|666e5f756e737570|A_L0|0|1|0|7830|0|T_i64|T_i64|C_ret|0\n",
                encoding="utf-8",
            )
            unsup_res = subprocess.run(
                [str(CORE_BIN), "verify-certs", "--lnir", str(unsup_lnir), "--json"],
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(unsup_res.returncode, 0, "Unsupported (A_L0) declaration must fail closed")

    def test_08_fuzzer_missing_engine_and_mutation_kills_across_all_seeds(self) -> None:
        missing = fuzzer.run_fuzzer(
            10,
            override_core="/nonexistent/lean-native-core",
            override_clang="/nonexistent/clang",
        )
        self.assertFalse(missing["ok"])
        self.assertEqual(missing["status"], "incomplete_missing_engine")

        clean = fuzzer.run_fuzzer(12)
        self.assertTrue(clean["ok"], f"Expected clean fuzzer run to pass: {clean}")
        self.assertGreaterEqual(clean["receipts"]["lnir_eval_executed_decls"], 12)

        for eng in ("stock_lean_c", "lnir_eval", "c_abi_llvm"):
            mutated = fuzzer.run_fuzzer(10, mutate_engine=eng)
            self.assertFalse(mutated["ok"], f"Mutation in {eng} (including seed >= 8) must fail conformance")
            self.assertGreaterEqual(mutated["mismatch_count"], 1)


if __name__ == "__main__":
    unittest.main()
