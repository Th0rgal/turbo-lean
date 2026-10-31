#!/usr/bin/env python3
"""Phase P0 Negative Injection & Trust-Boundary Verification Suite for `turbo-lean` / `LeanNative`.

Exercises targeted P0 trust-boundary checks and scalar conformance regressions.
Full export, loop/alias/RC, host-wrapper and target qualification remains open:
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
import re
import shutil
import signal
import time
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
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
            ["compile-llvm"], ["compile-static-lib"], ["validate-tv"], ["emit-lnir"],
            ["verify-certs"], ["verify-certs", "--json"], ["verify-certs", "--slot-regression"],
            ["superopt"], ["plugins"], ["telemetry"],
            ["compile"], ["--c-abi"], ["--emit-c-abi"], ["bogus-cmd", "--c-abi"],
            ["compile-mlir"], ["compile-ptx"], ["compile-metal"], ["compile-fastcheck"], ["compile-hybrid"],
            ["compile-llvm", "--lnir", "/tmp/nonexistent_lnir_file_p0.lnir"],
            ["compile-llvm", "--input", "/tmp/nonexistent_input_file_p0.lnir"],
            ["compile-llvm", "/tmp/nonexistent_pos_file_p0.lean"],
            ["eval-lnir", "--opt", "/tmp/nonexistent_opt_pos_file_p0.lnir", "--args", "1,2"],
            ["emit-cabi-bindings", "--lean", "/tmp/nonexistent_lean_file_p0.lean"],
            ["compile-llvm", "--args", "--baseline"],
            ["compile-llvm", "--args", "1"],
            ["eval-lnir", "--args", "--opt"],
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
                [str(CORE_BIN), "compile-llvm", "canonical", "--lnir", str(bad_json)],
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(res.returncode, 0, "Corrupt wire inside JSON with canonical moduleName must fail closed")

        worker_input = (
            '{"id":1,"method":"compile-llvm","arch":"x86_64","wire":"not-valid-lnir"}\n'
            '{"id":2,"method":"batch-fastcheck","wire":"not-valid-lnir"}\n'
            '{"id":3,"method":"compile-llvm","arch":"bogus-arch","canonical_benchmark":true}\n'
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
            [str(CORE_BIN), "compile-llvm", "canonical", "--arch", "macos-arm64"], text=True
        )
        ios_ir = subprocess.check_output(
            [str(CORE_BIN), "compile-llvm", "canonical", "--arch", "ios-arm64"], text=True
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
                    [str(CORE_BIN), "compile-static-lib", "canonical", "--arch", arch_flag, "--clang-bin", clang_bin, "-o", str(out_a), "--json"],
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
            [str(CORE_BIN), "compile-llvm", "canonical", "--arch", "wasm32"], text=True
        )
        wasm_simd = subprocess.check_output(
            [str(CORE_BIN), "compile-llvm", "canonical", "--arch", "wasm32", "--wasm-simd128"], text=True
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
                    "canonical",
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
                    "canonical",
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
                    "canonical",
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
            subprocess.check_output([str(CORE_BIN), "verify-certs", "--canonical-benchmark", "--json"], text=True)
        )
        self.assertTrue(default_certs["verified"])
        self.assertEqual(default_certs["overallAssurance"], "TranslationValidated")
        by_name = {d["declName"]: d for d in default_certs["declSummaries"]}
        self.assertEqual(by_name["collatz_steps"]["overallAssurance"], "VerifiedKernelProof")
        self.assertEqual(by_name["tuple_accum_sum"]["overallAssurance"], "TranslationValidated")
        self.assertEqual(by_name["sarray_scale_bias"]["overallAssurance"], "TranslationValidated")
        self.assertEqual(by_name["dot_product_u64"]["overallAssurance"], "VerifiedKernelProof")
        self.assertEqual(by_name["saxpy_kernel"]["overallAssurance"], "VerifiedKernelProof")

        kernel_only_certs = json.loads(
            subprocess.check_output([str(CORE_BIN), "verify-certs", "--canonical-benchmark", "--verified-kernel-only", "--json"], text=True)
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

    def test_09_wrong_type_wire_and_unsupported_fast_path(self) -> None:
        unsupported = "LNIR_WIRE_V1|54657374|1|D_decl|666e|A_L0|0|1|0|7830|0|T_i64|T_i64|C_ret|0"
        requests = []
        for method in ("compile-llvm", "batch-fastcheck", "eval-cex", "ping", "select-target", "riscv-step-audit"):
            for wire in (None, 42, [], {}, True, "INVALID", unsupported):
                for nested in (False, True):
                    req = {"id": len(requests), "method": method}
                    req.update({"params": {"wire": wire}} if nested else {"wire": wire})
                    requests.append(req)
        result = subprocess.run([str(CORE_BIN), "worker"],
                                input="".join(json.dumps(r) + "\n" for r in requests),
                                check=True, capture_output=True, text=True)
        rows = [json.loads(line) for line in result.stdout.splitlines()]
        self.assertEqual(len(rows), len(requests))
        for row in rows:
            self.assertFalse(row["ok"], row)

        # `eval-cex` never certifies raw unequal pairs or unbound witnesses; it certifies ONLY
        # when `decl_wire` + parameter bindings satisfy preconditions and evaluate to false.
        buggy_fc_wire = (
            "LNIR_WIRE_V1|46617374436865636b|1|"
            "D_decl|62756767795f6c74|A_L3|1|2|0|78|0|T_i64|1|79|0|T_i64|T_i1|"
            "C_let|2|T_i1|E_scalar|S_bin|B_lt|S_var|0|S_u64|10|"
            "C_let|3|T_i1|E_scalar|S_bool|1|"
            "C_ite|2|"
            "C_let|4|T_i1|E_scalar|S_bin|B_lt|S_var|0|S_var|1|C_ret|4|"
            "C_ret|3"
        )
        eval_cex_requests = [
            {"id": 1, "method": "eval-cex"},
            {"id": 2, "method": "eval-cex", "lhs": "0x1", "rhs": "0x0"},
            {"id": 3, "method": "eval-cex", "lhs": "0x5", "rhs": "0x5"},
            {"id": 4, "method": "eval-cex", "decl_wire": buggy_fc_wire, "x": "5"},
            {"id": 5, "method": "eval-cex", "decl_wire": buggy_fc_wire, "x": "20", "y": "0"},
            {"id": 6, "method": "eval-cex", "decl_wire": buggy_fc_wire, "x": "5", "y": "8"},
            {"id": 7, "method": "eval-cex", "decl_wire": buggy_fc_wire, "bindings": {"x": "5", "y": "5"}},
            {"id": 8, "method": "eval-cex", "decl_wire": unsupported, "x": "5", "y": "5"},
            {"id": 9, "method": "eval-cex", "decl_wire": 42},
        ]
        ec_res = subprocess.run([str(CORE_BIN), "worker"],
                                input="".join(json.dumps(r) + "\n" for r in eval_cex_requests),
                                check=True, capture_output=True, text=True)
        ec_rows = [json.loads(line) for line in ec_res.stdout.splitlines()]
        self.assertEqual(len(ec_rows), len(eval_cex_requests))
        for idx, expected_reason in (
            (0, "missing_witness"),
            (1, "statement_required"),
            (2, "lhs_eq_rhs"),
            (3, "witness_not_bound"),
            (4, "precondition_failed"),
            (5, "not_a_counterexample"),
        ):
            self.assertTrue(ec_rows[idx]["ok"], ec_rows[idx])
            self.assertFalse(ec_rows[idx]["result"]["certified"], ec_rows[idx])
            self.assertEqual(ec_rows[idx]["result"]["certification"], "unavailable", ec_rows[idx])
            self.assertEqual(ec_rows[idx]["result"]["reason"], expected_reason, ec_rows[idx])
            self.assertEqual(ec_rows[idx]["result"]["falsePositives"], 1, ec_rows[idx])
        self.assertTrue(ec_rows[6]["ok"], ec_rows[6])
        self.assertTrue(ec_rows[6]["result"]["certified"], ec_rows[6])
        self.assertEqual(ec_rows[6]["result"]["certification"], "evalCode", ec_rows[6])
        self.assertIsNone(ec_rows[6]["result"]["reason"], ec_rows[6])
        self.assertEqual(ec_rows[6]["result"]["falsePositives"], 0, ec_rows[6])
        self.assertFalse(ec_rows[7]["ok"], ec_rows[7])
        self.assertFalse(ec_rows[8]["ok"], ec_rows[8])

    def test_worker_missing_compile_input_never_uses_benchmark(self) -> None:
        all_methods = (
            "compile-llvm", "compile-ptx", "compile-metal", "compile-mlir",
            "compile-tpu", "compile-fastcheck", "batch-fastcheck",
            "superopt", "plugins", "verify-certs", "validate-tv",
        )
        requests = [{"id": i, "method": method} for i, method in enumerate(all_methods)]
        result = subprocess.run([str(CORE_BIN), "worker"],
                                input="".join(json.dumps(r) + "\n" for r in requests),
                                check=True, capture_output=True, text=True)
        rows = [json.loads(line) for line in result.stdout.splitlines()]
        self.assertEqual(len(rows), len(requests))
        self.assertTrue(all(row.get("ok") is False and row.get("error") == "explicit_input_wire_required"
                            for row in rows), rows)

        # Custom wire + fastcheck:true on compile-ptx / compile-metal must emit custom kernel, not cached sample
        custom_wire = (
            "LNIR_WIRE_V1|437573746f6d4d6f64|1|D_decl|637573746f6d5f66635f6b65726e656c|"
            "A_L3|1|1|0|7830|0|T_i64|T_i1|C_let|1|T_i1|E_scalar|S_bin|B_lt|S_var|0|S_u64|9|C_ret|1"
        )
        fc_requests = [
            {"id": 100, "method": "compile-ptx", "fastcheck": True, "wire": custom_wire},
            {"id": 101, "method": "compile-metal", "fastcheck": True, "wire": custom_wire},
            {"id": 102, "method": "compile-ptx", "fastcheck": True, "fastcheck_sample": True},
            {"id": 103, "method": "compile-ptx", "fastcheck": True, "canonical_benchmark": True},
        ]
        fc_res = subprocess.run([str(CORE_BIN), "worker"],
                                input="".join(json.dumps(r) + "\n" for r in fc_requests),
                                check=True, capture_output=True, text=True)
        fc_rows = [json.loads(line) for line in fc_res.stdout.splitlines()]
        self.assertEqual(len(fc_rows), 4)
        self.assertTrue(fc_rows[0]["ok"])
        self.assertEqual(fc_rows[0]["result"]["decls"], 1)
        self.assertIn("custom_fc_kernel", fc_rows[0]["result"]["ptx"])
        self.assertNotIn("evm_constrained_buggy_prop", fc_rows[0]["result"]["ptx"])
        self.assertTrue(fc_rows[1]["ok"])
        self.assertEqual(fc_rows[1]["result"]["decls"], 1)
        self.assertIn("custom_fc_kernel", fc_rows[1]["result"]["metal"])
        self.assertNotIn("evm_constrained_buggy_prop", fc_rows[1]["result"]["metal"])
        self.assertTrue(fc_rows[2]["ok"])
        self.assertEqual(fc_rows[2]["result"]["decls"], 2)
        self.assertIn("evm_constrained_buggy_prop", fc_rows[2]["result"]["ptx"])
        self.assertTrue(fc_rows[3]["ok"])
        self.assertGreater(fc_rows[3]["result"]["decls"], 2)
        self.assertNotIn("evm_constrained_buggy_prop", fc_rows[3]["result"]["ptx"])

        cli_fc = json.loads(subprocess.check_output(
            [str(CORE_BIN), "compile-fastcheck", "--canonical-benchmark", "--samples", "64", "--json"],
            text=True))
        self.assertEqual(cli_fc["moduleName"], "LeanNative.Benchmarks.Canonical")
        cli_ptx = subprocess.check_output(
            [str(CORE_BIN), "compile-ptx", "--fastcheck", "--canonical-benchmark"],
            text=True)
        self.assertNotIn("evm_constrained_buggy_prop", cli_ptx)

    def test_tv_summary_cannot_hide_skipped_or_invalid_rows(self) -> None:
        def row(name):
            return {"declName": name, "srcHash": "abc", "tgtHash": "def",
                    "concreteSamplesTot": 64, "concreteSamplesOk": 64,
                    **{key: True for key in ("passed", "ubRefines", "domainEquiv", "poisonRefines",
                                            "symRetEquiv", "concreteRefines", "memWritesEquiv")}}
        good = {"schemaVersion": "lean-native-symbolic-tv-v2", "allPassed": True,
                "passedDecls": 2, "totalDecls": 2, "declResults": [row("a"), row("b")]}
        fuzzer.validate_tv_coverage(good, {"a", "b"})
        bad_reports = [
            {**good, "passedDecls": 0, "totalDecls": 0, "declResults": []},
            {**good, "allPassed": "true"}, {**good, "passedDecls": True},
            {**good, "declResults": [row("a"), {**row("b"), "symRetEquiv": False}]},
            {**good, "declResults": [row("a"), {**row("b"), "concreteSamplesOk": 0}]},
            {**good, "declResults": [good["declResults"][0]] * 2},
            {**good, "declResults": [{"declName": "a", "passed": True}, {"declName": "wrong", "passed": True}]},
            {**good, "declResults": [{"declName": "a", "passed": True}, {"declName": "b", "passed": False}]},
        ]
        for report in bad_reports:
            with self.subTest(report=report), self.assertRaises(RuntimeError):
                fuzzer.validate_tv_coverage(report, {"a", "b"})

    def test_10_exact_named_batch_and_failed_rows(self) -> None:
        def decl(name: str, body: str) -> str:
            return f"D_decl|{name.encode().hex()}|A_L4|0|1|0|7830|0|T_i64|T_i64|{body}"
        with tempfile.TemporaryDirectory() as tmp:
            wire = Path(tmp) / "batch.lnir"
            wire.write_text("LNIR_WIRE_V1|54657374|2|" + decl("prefix_id", "C_ret|0")
                            + "|" + decl("broken", "C_ret|99"))
            def evaluate(args: str) -> subprocess.CompletedProcess:
                return subprocess.run([str(CORE_BIN), "eval-lnir", "--lnir", str(wire),
                                       "--batch-json", "--args", args], capture_output=True, text=True)
            good = evaluate("prefix_id:7")
            self.assertEqual(good.returncode, 0, good.stderr)
            self.assertEqual(json.loads(good.stdout)[0]["value_u64"], "7")
            failed = evaluate("prefix_id:7;broken:8")
            self.assertNotEqual(failed.returncode, 0)
            self.assertEqual([r["ok"] for r in json.loads(failed.stdout)], [True, False])
            for args in ("id:7", "prefix_id:7:8", "prefix_id:18446744073709551616"):
                self.assertNotEqual(evaluate(args).returncode, 0, args)

    def test_11_fabricated_archives_and_staging_failure(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            out = root / "keep.a"
            header = root / "keep.h"
            out.write_bytes(b"previous archive")
            header.write_bytes(b"previous header")
            for mode in ("substring", "trailing", "index_only", "extra_member", "truncated"):
                archiver = root / "fake_ar"
                archiver.write_text(
                    "#!/usr/bin/env python3\nimport sys\nfrom pathlib import Path\n"
                    "obj=Path(sys.argv[3]).read_bytes()\n"
                    "def member(name, data):\n"
                    "    h=f'{name:<16}{0:<12}{0:<6}{0:<6}{100644:<8}{len(data):<10}`\\n'.encode()\n"
                    "    return h+data+(b'\\n' if len(data)%2 else b'')\n"
                    f"mode={mode!r}\n"
                    "payload={'substring':member('x.o/',b'junk'+obj),"
                    "'trailing':member('x.o/',obj)+b'junk',"
                    "'index_only':member('/',obj),"
                    "'extra_member':member('x.o/',obj)+member('y.o/',b'junk'),"
                    "'truncated':member('x.o/',obj)[:-1]}[mode]\n"
                    "Path(sys.argv[2]).write_bytes(b'!<arch>\\n'+payload)\n")
                archiver.chmod(0o755)
                result = subprocess.run([str(CORE_BIN), "compile-static-lib", "canonical", "--clang-bin", find_clang(),
                                         "--ar-bin", str(archiver), "-o", str(out), "--header", str(header)],
                                        capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0, mode)
                self.assertEqual(out.read_bytes(), b"previous archive")
                self.assertEqual(header.read_bytes(), b"previous header")
            for extra in (["--emit-rust", str(root / "absent" / "out.rs")],
                          ["--header", str(out)], ["--emit-xcframework", str(root / "Kit")],
                          ["--target", "nvptx64"], ["--target", "hybrid"], ["--target", "wasm32"]):
                result = subprocess.run([str(CORE_BIN), "compile-static-lib", "canonical", "--clang-bin", find_clang(),
                                         "-o", str(out), *extra], capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0, extra)
                self.assertEqual(out.read_bytes(), b"previous archive")
            self.assertEqual(list(root.glob("*.tmp.*")), [])

    def test_artifact_bundle_publishes_one_immutable_generation(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            bundle = root / "current"
            archive, header = root / "kernels.a", root / "kernels.h"
            archive.write_bytes(b"legacy archive")
            header.write_bytes(b"legacy header")
            args = [str(CORE_BIN), "compile-static-lib", "canonical", "--clang-bin", find_clang(),
                    "-o", str(archive), "--header", str(header), "--artifact-bundle", str(bundle), "--json"]
            first = subprocess.run(args, capture_output=True, text=True)
            self.assertEqual(first.returncode, 0, first.stderr)
            self.assertEqual(json.loads(first.stdout)["publication"], "generation-pointer")
            self.assertTrue(bundle.is_symlink())
            old = bundle.resolve(strict=True)
            old_files = {p.name: p.read_bytes() for p in old.iterdir()}
            self.assertEqual(set(old_files), {"kernels.a", "kernels.h"})
            self.assertTrue(old_files["kernels.a"].startswith(b"!<arch>\n"))
            self.assertEqual(archive.read_bytes(), b"legacy archive")
            self.assertEqual(header.read_bytes(), b"legacy header")
            second = subprocess.run(args, capture_output=True, text=True)
            self.assertEqual(second.returncode, 0, second.stderr)
            self.assertNotEqual(bundle.resolve(), old)
            self.assertEqual({p.name: p.read_bytes() for p in old.iterdir()}, old_files)
            current = bundle.resolve()
            failed = subprocess.run(args + ["--ar-bin", "/nonexistent/archiver"], capture_output=True, text=True)
            self.assertNotEqual(failed.returncode, 0)
            self.assertEqual(bundle.resolve(), current)
            self.assertEqual(list(root.glob("*.tmp.*")), [])

    def test_kill_before_bundle_commit_preserves_previous_generation(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            bundle = root / "current"
            args = [str(CORE_BIN), "compile-static-lib", "canonical", "--clang-bin", find_clang(),
                    "-o", str(root / "kernels.a"), "--artifact-bundle", str(bundle)]
            subprocess.run(args, check=True, capture_output=True, text=True)
            old = bundle.resolve(strict=True)
            contents = {p.name: p.read_bytes() for p in old.iterdir()}
            tools = root / "tools"
            tools.mkdir()
            marker = root / "before_commit"
            fake_ln = tools / "ln"
            fake_ln.write_text("#!/usr/bin/env python3\nfrom pathlib import Path\nimport time\n"
                               f"Path({str(marker)!r}).write_text('staged')\ntime.sleep(30)\n")
            fake_ln.chmod(0o755)
            env = {**os.environ, "PATH": str(tools) + os.pathsep + os.environ.get("PATH", "")}
            proc = subprocess.Popen(args, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                    start_new_session=True)
            try:
                deadline = time.monotonic() + 15
                while not marker.exists() and proc.poll() is None and time.monotonic() < deadline:
                    time.sleep(0.02)
                self.assertTrue(marker.exists(), "compiler did not reach pre-publication boundary")
                self.assertEqual(bundle.resolve(), old)
            finally:
                if proc.poll() is None:
                    os.killpg(proc.pid, signal.SIGKILL)
                proc.communicate(timeout=5)
            self.assertLess(proc.returncode, 0)
            self.assertEqual(bundle.resolve(), old)
            self.assertEqual({p.name: p.read_bytes() for p in old.iterdir()}, contents)

    def test_export_redarg_name_is_preserved_and_rust_wrappers_delegate_to_abi(self) -> None:
        """A linked-backend mutation tests forwarding, not engine conformance."""
        with tempfile.TemporaryDirectory(prefix="p0_abi_forwarding_") as tmp:
            root = Path(tmp)
            source, wire, bindings = root / "Fixture.lean", root / "fixture.lnir", root / "bindings.rs"
            source.write_text("@[export kept_redArg]\ndef keep (x : UInt64) : UInt64 := x + 7\n"
                              "@[export plain_export]\ndef plain (x : UInt64) : UInt64 := x * 3\n")
            subprocess.run([str(fuzzer.LEAN_NATIVE_FULL), "emit-lnir", str(source), "--wire", "-o", str(wire)],
                           check=True, capture_output=True, text=True)
            evaluated = subprocess.run([str(CORE_BIN), "eval-lnir", "--lnir", str(wire),
                                        "--batch-json", "--args", "kept_redArg:5;plain_export:5"],
                                       check=True, capture_output=True, text=True)
            rows = {r["decl"]: int(r["value_u64"]) for r in json.loads(evaluated.stdout)}
            self.assertEqual(rows, {"kept_redArg": 12, "plain_export": 15})
            subprocess.run([str(CORE_BIN), "compile-static-lib", "--lnir", str(wire),
                            "--clang-bin", find_clang(), "-o", str(root / "libfixture.a"),
                            "--emit-rust", str(bindings)], check=True, capture_output=True, text=True)
            generated = bindings.read_text()
            self.assertIn("c_abi::kept_redArg(", generated)
            self.assertNotIn("binius_tower_xor64", generated)
            header = (root / "libfixture.a.h").read_text()
            self.assertIn("kept_redArg(", header)
            self.assertIn("plain_export(", header)
            self.assertNotIn("lean_native_swscale_down2x2_u8(", header)
            driver = root / "main.rs"
            driver.write_text('mod bindings;\nfn main() { unsafe { println!("{} {}", '
                              'bindings::kept_redArg(5), bindings::plain_export(5)); } }\n')
            binary = root / "runner"
            def run_linked() -> str:
                subprocess.run(["rustc", "--edition=2021", str(driver), "-L", str(root),
                                "-l", "static=fixture", "-o", str(binary)],
                               check=True, capture_output=True, text=True)
                return subprocess.run([str(binary)], check=True, capture_output=True, text=True).stdout.strip()
            self.assertEqual(run_linked(), "12 15")
            # Replace only the linked backend. Independent inline Rust would
            # continue returning the old values and fail this mutation check.
            backend = root / "mutated.c"
            backend.write_text("#include <stdint.h>\n"
                               "uint64_t kept_redArg(uint64_t x) { return x + 91; }\n"
                               "uint64_t plain_export(uint64_t x) { return x ^ 42; }\n")
            obj = root / "mutated.o"
            subprocess.run([find_clang(), "-c", str(backend), "-o", str(obj)],
                           check=True, capture_output=True, text=True)
            (root / "libfixture.a").unlink()
            subprocess.run(["ar", "rcs", str(root / "libfixture.a"), str(obj)],
                           check=True, capture_output=True, text=True)
            self.assertEqual(run_linked(), "96 47")

    def test_snark_benchmark_reports_missing_execution_dependency(self) -> None:
        result = subprocess.run([str(CORE_BIN), "bench-snark-kernels", "--json"],
                                capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        report = json.loads(result.stdout)
        self.assertFalse(report["ok"])
        self.assertEqual(report["status"], "BLOCKED_MISSING_DEPENDENCY")
        self.assertIs(report["benchmarkExecuted"], False)
        self.assertNotIn("elapsed_ns", report)

    def test_12_skipped_execution_and_missing_frontend_never_pass(self) -> None:
        ready = {"stock_lean_c": True, "lnir_eval": True, "c_abi_llvm": True}
        skipped = {"executed_count": 0, "mismatches": [], "receipts": {}}
        with patch.object(fuzzer, "probe_engines", return_value=ready), patch.object(
                fuzzer, "run_three_way_batch", return_value=skipped):
            for n in (0, 3):
                result = fuzzer.run_fuzzer(n)
                self.assertFalse(result["ok"])
                self.assertIsNone(result["rc_leak_count"])
                self.assertEqual(result["checked"], 0)
        with patch.object(fuzzer, "LEAN_NATIVE_FULL", Path("/nonexistent/frontend")):
            self.assertEqual(fuzzer.run_fuzzer(3)["status"], "incomplete_missing_engine")

    def test_13_tiered_conformance_and_sanitizer_gates_fail_closed(self) -> None:
        suite = ROOT / "scripts" / "run_conformance_suite.py"
        for bad_tier in ("C2", "C3"):
            res = subprocess.run(
                [sys.executable, str(suite), "--tier", bad_tier, "--json"],
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(res.returncode, 0, bad_tier)
            rep = json.loads(res.stdout)
            self.assertFalse(rep["ok"])
            self.assertEqual(rep["tierResults"][bad_tier]["status"], "BLOCKED_MISSING_DEPENDENCY")

        bad_arg = subprocess.run(
            [sys.executable, str(suite), "--tier", "C99"],
            capture_output=True,
            text=True,
        )
        self.assertEqual(bad_arg.returncode, 2)

        with patch.object(fuzzer, "find_sanitizer_linker", return_value=None):
            missing_san = fuzzer.run_fuzzer(4, asan=True, ubsan=True)
            self.assertFalse(missing_san["ok"])
            self.assertEqual(missing_san["status"], "incomplete_missing_engine")

        engines = fuzzer.probe_engines(asan=True, ubsan=True)
        self.assertTrue(engines["c_abi_llvm"], engines)

        # Fail closed when LLVM IR has zero definitions or references an undefined attribute group,
        # handle non-#0/#1 attribute groups, and stay idempotent when sanitize_address is already present.
        with self.assertRaises(RuntimeError):
            fuzzer.instrument_llvm_ir_for_asan("; empty module\n")
        with self.assertRaises(RuntimeError):
            fuzzer.instrument_llvm_ir_for_asan("define i64 @f() #7 {\n  ret i64 0\n}\n")
        inst_custom = fuzzer.instrument_llvm_ir_for_asan(
            "define dso_local i64 @g() #3 {\n  ret i64 0\n}\n"
            "define dso_local i64 @bare() {\n  ret i64 1\n}\n"
            "attributes #3 = {nounwind}\n"
        )
        self.assertIn("attributes #3 = { sanitize_address nounwind }", inst_custom)
        self.assertIn("define dso_local i64 @bare() sanitize_address {", inst_custom)
        self.assertEqual(fuzzer.instrument_llvm_ir_for_asan(inst_custom).count("sanitize_address"), 2)
        multi = fuzzer.instrument_llvm_ir_for_asan(
            'define i64 @multi(i64 %x) #0 #1 section ".text" {\n  ret i64 %x\n}\n'
            'define i64 @quoted(i64 %x) "section" "#9" #4 {\n  ret i64 %x\n}\n'
            "attributes #0 = { nounwind }\n"
            "attributes #1 = { uwtable }\n"
            "attributes #4 = { nounwind }\n"
            'attributes #9 = { "not-an-attribute" }\n'
        )
        self.assertIn("attributes #0 = { sanitize_address nounwind }", multi)
        self.assertIn("attributes #1 = { sanitize_address uwtable }", multi)
        self.assertIn("attributes #4 = { sanitize_address nounwind }", multi)
        self.assertNotIn("sanitize_address", multi.split("attributes #9", 1)[1])
        self.assertEqual(fuzzer.instrument_llvm_ir_for_asan(multi).count("sanitize_address"), 3)

        with tempfile.TemporaryDirectory(prefix="p0_san_kill_") as tmp:
            p = Path(tmp)
            ll = p / "oob.ll"
            c = p / "driver.c"
            b = p / "oob_runner"
            ll.write_text(
                "define dso_local i64 @oob_read(i64 %idx) #2 {\n"
                "entry:\n"
                "  %arr = alloca [2 x i64], align 8\n"
                "  %ptr = getelementptr [2 x i64], ptr %arr, i64 0, i64 %idx\n"
                "  %v = load volatile i64, ptr %ptr, align 8\n"
                "  ret i64 %v\n"
                "}\n"
                "attributes #2 = {nounwind uwtable}\n",
                encoding="utf-8",
            )
            c.write_text(
                "#include <stdint.h>\n#include <stdio.h>\n"
                "extern uint64_t oob_read(uint64_t);\n"
                "int main(void) {\n"
                "  volatile int shift = 70;\n"
                "  int ub = 1 << shift;\n"
                "  printf(\"%d %llu\\n\", ub, (unsigned long long)oob_read(2));\n"
                "  return 0;\n"
                "}\n",
                encoding="utf-8",
            )
            san_meta = fuzzer.compile_and_link_llvm_driver(
                clang_bin=engines["clang_bin"],
                extra_inc=fuzzer.clang_extra_flags(engines["clang_bin"]),
                ll_path=ll,
                driver_c_path=c,
                out_bin_path=b,
                asan=True,
                ubsan=False,
                sanitizer_linker=engines["sanitizer_linker"],
            )
            self.assertEqual(san_meta["ubsan_scope"], "disabled")
            c_no_ub = p / "driver_asan.c"
            c_no_ub.write_text(
                "#include <stdint.h>\n#include <stdio.h>\n"
                "extern uint64_t oob_read(uint64_t);\n"
                "int main(void) { printf(\"%llu\\n\", (unsigned long long)oob_read(2)); return 0; }\n",
                encoding="utf-8",
            )
            fuzzer.compile_and_link_llvm_driver(
                clang_bin=engines["clang_bin"],
                extra_inc=fuzzer.clang_extra_flags(engines["clang_bin"]),
                ll_path=ll,
                driver_c_path=c_no_ub,
                out_bin_path=b,
                asan=True,
                ubsan=False,
                sanitizer_linker=engines["sanitizer_linker"],
            )
            crash = subprocess.run(
                [str(b)],
                env={**os.environ, "ASAN_OPTIONS": "detect_leaks=0:abort_on_error=1:halt_on_error=1"},
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(crash.returncode, 0, "ASan must abort on out-of-bounds LLVM alloca read")
            self.assertIn("AddressSanitizer", crash.stderr)

            ub_bin = p / "ub_runner"
            ub_ll = p / "noop.ll"
            ub_ll.write_text(
                "define dso_local i64 @oob_read(i64 %idx) #0 {\n"
                "entry:\n"
                "  ret i64 %idx\n"
                "}\n"
                "attributes #0 = { nounwind uwtable }\n",
                encoding="utf-8",
            )
            ub_meta = fuzzer.compile_and_link_llvm_driver(
                clang_bin=engines["clang_bin"],
                extra_inc=fuzzer.clang_extra_flags(engines["clang_bin"]),
                ll_path=ub_ll,
                driver_c_path=c,
                out_bin_path=ub_bin,
                asan=False,
                ubsan=True,
            )
            self.assertEqual(ub_meta["ubsan_scope"], "c_driver_and_link_runtime_only_not_llvm_ir")
            ub_crash = subprocess.run(
                [str(ub_bin)],
                env={**os.environ, "UBSAN_OPTIONS": "print_stacktrace=1:halt_on_error=1"},
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(ub_crash.returncode, 0, "UBSan must abort on C driver shift UB")

        # End-to-end propagation: an ASan abort in the compiled LLVM binary must fail run_fuzzer / run_conformance_suite.
        orig_instrument_asan = fuzzer.instrument_llvm_ir_for_asan

        def _inject_oob_ir(ir_text: str) -> str:
            base = orig_instrument_asan(ir_text)
            if "@fuzz_seed_0" not in base:
                return base
            patched, n_repl = re.subn(
                r"(^define\b[^\n]*@fuzz_seed_0\([^\n{]*\{\nentry:\n)",
                r"\1  %bad_arr = alloca [2 x i64], align 8\n"
                r"  %bad_idx_slot = alloca i64, align 8\n"
                r"  store volatile i64 2, ptr %bad_idx_slot, align 8\n"
                r"  %bad_idx = load volatile i64, ptr %bad_idx_slot, align 8\n"
                r"  %bad_ptr = getelementptr [2 x i64], ptr %bad_arr, i64 0, i64 %bad_idx\n"
                r"  %bad_ld = load volatile i64, ptr %bad_ptr, align 8\n",
                base,
                count=1,
                flags=re.M,
            )
            self.assertEqual(n_repl, 1, "Failed to inject OOB read into @fuzz_seed_0")
            return patched

        with patch.object(fuzzer, "instrument_llvm_ir_for_asan", side_effect=_inject_oob_ir):
            failed_fuzz = fuzzer.run_fuzzer(1, asan=True, ubsan=False)
            self.assertFalse(failed_fuzz["ok"], failed_fuzz)
            self.assertEqual(failed_fuzz["checked"], 0)
            self.assertTrue(failed_fuzz["shrunk_failures"])

        contract_sh = ROOT / "scripts" / "verify_roadmap_contract.sh"
        bad_auditor = subprocess.run(
            ["bash", str(contract_sh)],
            env={**os.environ, "TURBO_AUDITOR_BIN": "/nonexistent/turbo-lean"},
            capture_output=True,
            text=True,
        )
        self.assertNotEqual(bad_auditor.returncode, 0)
        self.assertIn("TURBO_AUDITOR_BIN", bad_auditor.stderr)

    def test_14_emitter_mutants_unit_and_negative_accounting(self):
        import emitter_mutants as em

        self.assertTrue(em.run_unit_tests())
        spec = em.load_spec()
        ids = [m["id"] for m in spec["mutations"]]
        self.assertEqual(ids, [f"M{i}" for i in range(1, 12)])
        base_rows = [
            {
                "id": m["id"],
                "backend": m["backend"],
                "outcome": "KILLED",
                "killed_by": ["C1"],
                "checks": {},
            }
            for m in spec["mutations"]
        ]
        self.assertTrue(em.summarize(base_rows, spec, ids)["conclusive"])
        survived = [dict(r) for r in base_rows]
        survived[0] = {**survived[0], "outcome": "SURVIVED", "killed_by": []}
        s_sum = em.summarize(survived, spec, ids)
        self.assertEqual(s_sum["counts"].get("SURVIVED"), 1)
        infra = [dict(r) for r in base_rows]
        infra[1] = {**infra[1], "outcome": "INFRA_FAILED", "killed_by": []}
        i_sum = em.summarize(infra, spec, ids)
        self.assertFalse(i_sum["conclusive"])
        self.assertEqual(i_sum["infra_failed_ids"], ["M2"])
        apply_fail = [dict(r) for r in base_rows]
        apply_fail[2] = {**apply_fail[2], "outcome": "APPLY_FAILED", "killed_by": []}
        a_sum = em.summarize(apply_fail, spec, ids)
        self.assertFalse(a_sum["conclusive"])
        self.assertEqual(a_sum["apply_failed_ids"], ["M3"])
        missing_row = em.summarize(base_rows[:-1], spec, ids)
        self.assertFalse(missing_row["conclusive"])
        self.assertEqual(missing_row["missing_universe_ids"], ["M11"])
        targeted_sum = em.summarize(base_rows[:2], spec, ids[:2], targeted=True)
        self.assertFalse(targeted_sum["conclusive"])
        self.assertEqual(targeted_sum["run_outcome"], "TARGETED")
        with tempfile.TemporaryDirectory() as tmp:
            bad_home = Path(tmp) / "home"
            bad_home.mkdir()
            (bad_home / ".gitconfig").write_text("[commit]\n\tgpgsign = true\n[gpg]\n\tprogram = /nonexistent/gpg\n")
            unit = subprocess.run(
                [sys.executable, str(ROOT / "scripts" / "emitter_mutants.py"), "--unit-tests"],
                env={**os.environ, "HOME": str(bad_home)},
                capture_output=True,
                text=True,
            )
            self.assertEqual(unit.returncode, 0, unit.stderr + unit.stdout)


if __name__ == "__main__":
    unittest.main()
