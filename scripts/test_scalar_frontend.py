"""Actual stock-Lean/LNIR/LLVM execution; no Python result oracle."""
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import fuzz_lcnf_conformance as fuzzer


class ScalarFrontend(unittest.TestCase):
    def test_primitive_boundaries(self):
        # Run the actual Lean bridge: same leaf names, mismatched types/arity
        # and local calls must stay outside the canonical intrinsic boundary.
        source = '''import LeanNative.IR.Bridge
open LeanNative.IR
#guard canonicalUIntCastMask? `UInt64.toUInt8 [.i64] .i8 == some 255
#guard canonicalUIntCastMask? `UInt8.toUInt64 [.i8] .i64 == some 18446744073709551615
#guard canonicalUIntCastMask? `User.UInt64.toUInt8 [.i64] .i8 == none
#guard canonicalUIntCastMask? `UInt64.toUInt8 [.i32] .i8 == none
#guard canonicalUIntCastMask? `UInt64.toUInt8 [.i64] .i32 == none
#guard canonicalUIntCastMask? `UInt64.toUInt8 [] .i8 == none
#guard canonicalUIntCastMask? `UInt64.toUInt8 [.i64, .i64] .i8 == none
#eval do
  let env ← Lean.mkEmptyEnvironment
  let rejected : List (Lean.Name × List VarId × LNIRType × List LNIRType × Bool) :=
      [(`UInt64.toUInt8, [0], .i8, [.i64], true),
       (`User.UInt64.toUInt8, [0], .i8, [.i64], false),
       (`UInt64.toUInt8, [0], .i8, [.i32], false),
       (`UInt64.toUInt8, [0], .i32, [.i64], false),
       (`UInt64.toUInt8, [], .i8, [], false),
       (`UInt64.toUInt8, [0, 1], .i8, [.i64, .i64], false),
       (`UInt64.decEq, [0, 1], .i8, [.i64, .i64], true)]
  for (name, args, ret, tys, localCall) in rejected do
    unless (tryLowerIntrinsicCall env name args ret tys localCall).isNone do
      throw (IO.userError s!"unexpected intrinsic: {name}")
  match tryLowerIntrinsicCall env `UInt64.decEq [0, 1] .i8 [.i64, .i64] with
  | some (.scalar (.select (.binOp .eq _ _) (.constU64 1) (.constU64 0))) => pure ()
  | _ => throw (IO.userError "UInt8 comparison lost its numeric representation")
'''
        with tempfile.TemporaryDirectory(prefix="scalar_boundary_") as tmp:
            path = Path(tmp) / "Boundary.lean"
            path.write_text(source)
            result = subprocess.run(["lake", "env", "lean", str(path)],
                                    cwd=fuzzer.ROOT / "lean", capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_unsigned_casts_and_input_dependent_boolean_branches(self):
        engines = fuzzer.probe_engines()
        self.assertTrue(all(engines[k] for k in ("stock_lean_c", "lnir_eval", "c_abi_llvm")), engines)
        trees = [{"k": "uint_cast", "src_bits": src, "dst_bits": dst, "arg": {"k": "var"}}
                 for src in (8, 16, 32, 64) for dst in (8, 16, 32, 64) if src != dst]
        trees += [{"k": "ite_input", "boundary": n, "op": op}
                  for op in ("==", "<", "<=") for n in (0, 1, 255, 2**32, 2**64 - 1)]
        programs = [{"seed": i, "arg0": value, "tree": tree}
                    for i, (tree, value) in enumerate((t, v) for t in trees
                    for v in (0, 1, 255, 256, 65535, 65536, 2**32 - 1, 2**32, 2**64 - 1))]
        try:
            result = fuzzer.run_three_way_batch(programs, engines)
        except subprocess.CalledProcessError as error:
            self.fail(f"real engine failed: {error}; stdout={error.stdout}; stderr={error.stderr}")
        print(json.dumps(result, sort_keys=True))
        self.assertEqual(result["executed_count"], len(programs))
        self.assertEqual(result["mismatches"], [])

    def test_stage1b_narrow_abi_usize_bool_enums_joinpoints_and_divmod_zero(self):
        engines = fuzzer.probe_engines()
        self.assertTrue(all(engines[k] for k in ("stock_lean_c", "lnir_eval", "c_abi_llvm")), engines)
        lean_bin = engines["lean_bin"]
        core_bin = engines["core_bin"]
        full_bin = engines["full_bin"]
        clang_bin = engines["clang_bin"]
        lean_prefix = subprocess.run(
            [lean_bin, "--print-prefix"], check=True, capture_output=True, text=True
        ).stdout.strip()
        leanc = str(Path(lean_prefix) / "bin" / "leanc")

        lean_src = """inductive Mode where
  | fast
  | safe
  | fallback

def localAddMask (a : UInt16) (b : UInt16) : UInt16 :=
  let step := fun (u : UInt16) (v : UInt16) => (u + v) ^^^ (0x1234 : UInt16)
  step a b

@[export s1b_u8_ops]
def s1b_u8_ops (x : UInt8) (y : UInt8) : UInt8 :=
  let s := x + (-y)
  let d := x / y
  let m := x % y
  let sh := (x <<< y) ^^^ (x >>> y)
  let c := ~~~s
  let b := (x == y).toUInt8
  if x != y && !(x < y || x <= (3 : UInt8)) then (c + d + b) ^^^ (m ||| sh)
  else (s * y) + d + m + sh + b

@[export s1b_u16_helper_jp]
def s1b_u16_helper_jp (x : UInt16) (y : UInt16) : UInt16 :=
  let base := localAddMask (-x) y
  let b16 := (x != y).toUInt16
  let joined : UInt16 :=
    if x < y then base + (7 : UInt16) + b16
    else if x == y then base ^^^ (0xFF00 : UInt16)
    else (base / y) + (base % y)
  (joined <<< (y &&& (31 : UInt16))) ||| (joined >>> (3 : UInt16))

@[export s1b_u32_divmod_casts]
def s1b_u32_divmod_casts (x : UInt32) (y : UInt32) : UInt32 :=
  let q := x / y
  let r := (-x) % y
  let w8 := x.toUInt8.toUInt32
  let w16 := y.toUInt16.toUInt32
  let w64 := (x.toUInt64 + (-y.toUInt64)).toUInt32 + (decide (x < y)).toUInt32
  ((q ^^^ r) + w8 + w16) ^^^ (~~~w64)

@[export s1b_bool_logic]
def s1b_bool_logic (a : Bool) (b : Bool) (x : UInt64) : Bool :=
  let p := (a && !b) || (b != (x == (0 : UInt64)))
  let q := (a == b) != ((-x + a.toUInt64) <= (255 : UInt64))
  p != q

@[export s1b_usize_ops]
def s1b_usize_ops (x : USize) (y : USize) : USize :=
  let q := (-x) / y
  let r := x % y
  let sh := (x <<< y) ^^^ (x >>> y)
  let c8 := x.toUInt8.toUSize + (x == y).toUSize
  let c16 := y.toUInt16.toUSize
  let c32 := x.toUInt32.toUSize
  let c64 := y.toUInt64.toUSize
  if x < y || x == y then (q + r + sh) ^^^ c8 ^^^ c16
  else ((x - y) * (3 : USize)) + q + r + c32 + c64

def pickMode (tag : UInt8) : Mode :=
  if tag == (0 : UInt8) then .fast
  else if tag == (1 : UInt8) then .safe
  else .fallback

@[export s1b_enum_branch]
def s1b_enum_branch (tag : UInt8) (x : UInt64) (y : UInt64) : UInt64 :=
  let m := pickMode tag
  let res : UInt64 :=
    match m with
    | .fast => (x / y) ^^^ (x % y)
    | .safe =>
      let z := if x != y then x + (19 : UInt64) else y + (23 : UInt64)
      z * (5 : UInt64)
    | .fallback => (~~~x) >>> y
  res + (if tag <= (1 : UInt8) then (11 : UInt64) else (29 : UInt64))
"""
        u8_inputs = [(0, 0), (1, 0), (250, 13), (255, 255), (128, 9), (3, 3), (42, 7)]
        u16_inputs = [(0, 0), (65535, 0), (1024, 1024), (17, 50000), (60000, 19)]
        u32_inputs = [(0, 0), (0xFFFFFFFF, 0), (0x80000000, 3), (0x12345678, 0x9ABCDEF0), (255, 65536)]
        bool_inputs = [(b1, b2, x) for b1 in (0, 1) for b2 in (0, 1) for x in (0, 1, 255, 256, 2**64 - 1)]
        usize_inputs = [(0, 0), (1, 0), (0xFFFFFFFF, 1), (0x123456789ABCDEF0, 0), (0x123456789ABCDEF0, 65), (99, 99)]
        enum_inputs = [(t, x, y) for t in (0, 1, 2, 255) for (x, y) in ((0, 0), (123456789, 0), (2**64 - 1, 7), (42, 42))]

        cases = []
        for idx, (x, y) in enumerate(u8_inputs):
            cases.append({"id": f"u8_{idx}", "decl": "s1b_u8_ops", "args": [x, y]})
        for idx, (x, y) in enumerate(u16_inputs):
            cases.append({"id": f"u16_{idx}", "decl": "s1b_u16_helper_jp", "args": [x, y]})
        for idx, (x, y) in enumerate(u32_inputs):
            cases.append({"id": f"u32_{idx}", "decl": "s1b_u32_divmod_casts", "args": [x, y]})
        for idx, (a, b, x) in enumerate(bool_inputs):
            cases.append({"id": f"bool_{idx}", "decl": "s1b_bool_logic", "args": [a, b, str(x)]})
        for idx, (x, y) in enumerate(usize_inputs):
            cases.append({"id": f"usize_{idx}", "decl": "s1b_usize_ops", "args": [str(x), str(y)]})
        for idx, (t, x, y) in enumerate(enum_inputs):
            cases.append({"id": f"enum_{idx}", "decl": "s1b_enum_branch", "args": [t, str(x), str(y)]})

        with tempfile.TemporaryDirectory(prefix="s1b_conformance_") as tmp:
            tmpdir = Path(tmp)
            lean_path = tmpdir / "Stage1B.lean"
            lean_path.write_text(lean_src, encoding="utf-8")

            stock_calls = []
            for c in cases:
                d = c["decl"]
                a = c["args"]
                if d == "s1b_u8_ops":
                    expr = f"(s1b_u8_ops ({a[0]} : UInt8) ({a[1]} : UInt8)).toUInt64"
                elif d == "s1b_u16_helper_jp":
                    expr = f"(s1b_u16_helper_jp ({a[0]} : UInt16) ({a[1]} : UInt16)).toUInt64"
                elif d == "s1b_u32_divmod_casts":
                    expr = f"(s1b_u32_divmod_casts ({a[0]} : UInt32) ({a[1]} : UInt32)).toUInt64"
                elif d == "s1b_bool_logic":
                    b_lit = lambda v: "true" if int(v) != 0 else "false"
                    expr = f"(if s1b_bool_logic {b_lit(a[0])} {b_lit(a[1])} ({a[2]} : UInt64) then (1 : UInt64) else 0)"
                elif d == "s1b_usize_ops":
                    expr = f"(s1b_usize_ops ({a[0]} : UInt64).toUSize ({a[1]} : UInt64).toUSize).toUInt64"
                else:
                    expr = f"(s1b_enum_branch ({a[0]} : UInt8) ({a[1]} : UInt64) ({a[2]} : UInt64))"
                stock_calls.append(f"toString ({expr})")

            stock_lean = tmpdir / "StockStage1B.lean"
            stock_c = tmpdir / "StockStage1B.c"
            stock_bin = tmpdir / "stock_s1b"
            stock_lean.write_text(
                lean_src
                + '\ndef main : IO Unit :=\n  IO.println ("[" ++ String.intercalate "," ['
                + ", ".join(stock_calls)
                + '] ++ "]")\n',
                encoding="utf-8",
            )
            subprocess.run(
                [lean_bin, str(stock_lean), "-c", str(stock_c)],
                cwd=str(tmpdir),
                check=True,
                capture_output=True,
                text=True,
            )
            subprocess.run([leanc, "-O2", str(stock_c), "-o", str(stock_bin)], check=True, capture_output=True, text=True)
            stock_vals = [int(v) for v in json.loads(subprocess.check_output([str(stock_bin)], text=True))]

            wire_path = tmpdir / "stage1b.lnir"
            subprocess.run(
                [full_bin, "emit-lnir", "--wire", "--arch", "x86_64", str(lean_path), "-o", str(wire_path)],
                check=True,
                capture_output=True,
                text=True,
            )
            tv_rep = json.loads(
                subprocess.check_output([core_bin, "validate-tv", "--lnir", str(wire_path), "--json"], text=True)
            )
            self.assertTrue(tv_rep["allPassed"], tv_rep)

            cases_jsonl = tmpdir / "cases.jsonl"
            cases_jsonl.write_text("\n".join(json.dumps(c) for c in cases) + "\n", encoding="utf-8")
            ev_out = subprocess.check_output(
                [core_bin, "eval-lnir", "--lnir", str(wire_path), "--arch", "x86_64", "--opt", "--cases-file", str(cases_jsonl)],
                text=True,
            )
            ev_rows = json.loads(ev_out)
            self.assertEqual(len(ev_rows), len(cases))
            for r in ev_rows:
                self.assertTrue(r["ok"], r)
            lnir_vals = [int(r["value_u64"]) for r in ev_rows]

            ll_x64 = tmpdir / "stage1b.x86_64.ll"
            ll_arm = tmpdir / "stage1b.arm64.ll"
            subprocess.run(
                [core_bin, "compile-llvm", "--lnir", str(wire_path), "--arch", "x86_64", "-o", str(ll_x64)],
                check=True,
                capture_output=True,
                text=True,
            )
            subprocess.run(
                [core_bin, "compile-llvm", "--lnir", str(wire_path), "--arch", "arm64", "-o", str(ll_arm)],
                check=True,
                capture_output=True,
                text=True,
            )
            ir_x64 = ll_x64.read_text(encoding="utf-8")
            ir_arm = ll_arm.read_text(encoding="utf-8")
            self.assertIn("define dso_local zeroext i8 @s1b_u8_ops(i8 zeroext noundef %arg_v0, i8 zeroext noundef %arg_v1)", ir_x64)
            self.assertIn("define dso_local zeroext i16 @s1b_u16_helper_jp(i16 zeroext noundef %arg_v0, i16 zeroext noundef %arg_v1)", ir_x64)
            self.assertIn("define dso_local i32 @s1b_u32_divmod_casts(i32 noundef %arg_v0, i32 noundef %arg_v1)", ir_x64)
            self.assertIn("define dso_local zeroext i8 @s1b_bool_logic(i8 zeroext noundef %arg_v0, i8 zeroext noundef %arg_v1, i64 noundef %arg_v2)", ir_x64)
            self.assertIn("define dso_local i8 @s1b_u8_ops(i8 noundef %arg_v0, i8 noundef %arg_v1)", ir_arm)
            self.assertIn("define dso_local i16 @s1b_u16_helper_jp(i16 noundef %arg_v0, i16 noundef %arg_v1)", ir_arm)

            c_lines = [
                "#include <stdint.h>",
                "#include <stddef.h>",
                "#include <stdio.h>",
                "extern uint8_t s1b_u8_ops(uint8_t, uint8_t);",
                "extern uint16_t s1b_u16_helper_jp(uint16_t, uint16_t);",
                "extern uint32_t s1b_u32_divmod_casts(uint32_t, uint32_t);",
                "extern uint8_t s1b_bool_logic(uint8_t, uint8_t, uint64_t);",
                "extern size_t s1b_usize_ops(size_t, size_t);",
                "extern uint64_t s1b_enum_branch(uint8_t, uint64_t, uint64_t);",
                "int main(void) {",
                '  printf("[");',
            ]
            for idx, c in enumerate(cases):
                sep = "," if idx > 0 else ""
                d = c["decl"]
                a = c["args"]
                if d == "s1b_u8_ops":
                    call_s = f"(unsigned long long)s1b_u8_ops((uint8_t){int(a[0])}U, (uint8_t){int(a[1])}U)"
                elif d == "s1b_u16_helper_jp":
                    call_s = f"(unsigned long long)s1b_u16_helper_jp((uint16_t){int(a[0])}U, (uint16_t){int(a[1])}U)"
                elif d == "s1b_u32_divmod_casts":
                    call_s = f"(unsigned long long)s1b_u32_divmod_casts((uint32_t){int(a[0])}U, (uint32_t){int(a[1])}U)"
                elif d == "s1b_bool_logic":
                    call_s = f"(unsigned long long)s1b_bool_logic((uint8_t){int(a[0])}U, (uint8_t){int(a[1])}U, (uint64_t){int(a[2])}ULL)"
                elif d == "s1b_usize_ops":
                    call_s = f"(unsigned long long)s1b_usize_ops((size_t){int(a[0])}ULL, (size_t){int(a[1])}ULL)"
                else:
                    call_s = f"(unsigned long long)s1b_enum_branch((uint8_t){int(a[0])}U, (uint64_t){int(a[1])}ULL, (uint64_t){int(a[2])}ULL)"
                c_lines.append(f'  printf("{sep}\\"%llu\\"", {call_s});')
            c_lines += ['  printf("]\\n");', "  return 0;", "}"]
            c_driver = tmpdir / "driver.c"
            c_runner = tmpdir / "c_runner"
            c_driver.write_text("\n".join(c_lines) + "\n", encoding="utf-8")
            subprocess.run(
                [clang_bin, "-O2", "-Wno-override-module", *fuzzer.clang_extra_flags(clang_bin), str(ll_x64), str(c_driver), "-o", str(c_runner)],
                check=True,
                capture_output=True,
                text=True,
            )
            llvm_vals = [int(v) for v in json.loads(subprocess.check_output([str(c_runner)], text=True))]

            self.assertEqual(lnir_vals, stock_vals)
            self.assertEqual(llvm_vals, stock_vals)

    def test_wasm32_usize_semantics_and_gpu_usize_rejection(self):
        engines = fuzzer.probe_engines()
        core_bin = engines["core_bin"]
        full_bin = engines["full_bin"]
        usize_src = """@[export wasm_usize_probe]
def wasm_usize_probe (x : USize) (y : USize) : UInt64 :=
  let wrapped := x + (1 : USize)
  let shifted := x <<< y
  wrapped.toUInt64 ^^^ shifted.toUInt64
"""
        with tempfile.TemporaryDirectory(prefix="s1b_wasm_usize_") as tmp:
            tmpdir = Path(tmp)
            src_path = tmpdir / "WasmUSize.lean"
            src_path.write_text(usize_src, encoding="utf-8")
            wasm_wire = tmpdir / "wasm.lnir"
            x64_wire = tmpdir / "x64.lnir"
            subprocess.run(
                [full_bin, "emit-lnir", "--wire", "--arch", "wasm32", str(src_path), "-o", str(wasm_wire)],
                check=True,
                capture_output=True,
                text=True,
            )
            subprocess.run(
                [full_bin, "emit-lnir", "--wire", "--arch", "x86_64", str(src_path), "-o", str(x64_wire)],
                check=True,
                capture_output=True,
                text=True,
            )
            wasm_ev = json.loads(
                subprocess.check_output(
                    [
                        core_bin,
                        "eval-lnir",
                        "--lnir",
                        str(wasm_wire),
                        "--arch",
                        "wasm32",
                        "--batch-json",
                        "--args",
                        "wasm_usize_probe:4294967295,33",
                    ],
                    text=True,
                )
            )
            x64_ev = json.loads(
                subprocess.check_output(
                    [
                        core_bin,
                        "eval-lnir",
                        "--lnir",
                        str(x64_wire),
                        "--arch",
                        "x86_64",
                        "--batch-json",
                        "--args",
                        "wasm_usize_probe:4294967295,33",
                    ],
                    text=True,
                )
            )
            self.assertEqual(int(wasm_ev[0]["value_u64"]), (0) ^ ((0xFFFFFFFF << 1) & 0xFFFFFFFF))
            self.assertEqual(int(x64_ev[0]["value_u64"]), 0x100000000 ^ ((0xFFFFFFFF << 33) & 0xFFFFFFFFFFFFFFFF))

            wasm_ll = tmpdir / "wasm.ll"
            subprocess.run(
                [core_bin, "compile-llvm", "--lnir", str(wasm_wire), "--arch", "wasm32", "-o", str(wasm_ll)],
                check=True,
                capture_output=True,
                text=True,
            )
            self.assertIn("define dso_local i64 @wasm_usize_probe(i32 noundef %arg_v0, i32 noundef %arg_v1)", wasm_ll.read_text(encoding="utf-8"))

            for bad_arch in ("nvptx64", "hybrid"):
                bad_res = subprocess.run(
                    [full_bin, "emit-lnir", "--wire", "--arch", bad_arch, str(src_path), "-o", str(tmpdir / "bad.lnir")],
                    capture_output=True,
                    text=True,
                )
                self.assertNotEqual(bad_res.returncode, 0, f"USize must fail closed on {bad_arch}")

    def test_fail_closed_unsupported_constructs_and_fault_isolated_cases_file(self):
        engines = fuzzer.probe_engines()
        core_bin = engines["core_bin"]
        full_bin = engines["full_bin"]
        rejected_snippets = {
            "nat_param": "def bad_nat (n : Nat) : UInt64 := n.toUInt64\n",
            "direct_recursion": "partial def bad_rec (x : UInt64) : UInt64 := if x == 0 then 0 else bad_rec (x - 1)\n",
            "mutual_recursion": "mutual\npartial def ping (x : UInt64) : UInt64 := if x == 0 then 1 else pong (x - 1)\npartial def pong (x : UInt64) : UInt64 := if x == 0 then 2 else ping (x - 1)\nend\n",
            "closure_param": "def bad_clos (f : UInt64 → UInt64) (x : UInt64) : UInt64 := f x\n",
            "heap_adt": "inductive Boxed where | mk (x : UInt64) (s : String)\ndef bad_adt (b : Boxed) : UInt64 := match b with | .mk x _ => x\n",
            "string_lit": "def bad_str (x : UInt64) : String := if x == 0 then \"zero\" else \"nonzero\"\n",
            "unmodeled_extern_log2": "@[export bad_log2]\ndef bad_log2 (x : UInt64) : UInt64 := x.log2\n",
            "user_extern_decl": "@[extern \"c_magic\"] opaque magic_ext : UInt64 → UInt64\n@[export call_magic]\ndef call_magic (x : UInt64) : UInt64 := magic_ext x\n",
            "signed_int8_param": "@[export bad_i8]\ndef bad_i8 (x : Int8) : Int8 := x + 1\n",
            "signed_int64_internal": "@[export bad_i64_inner]\ndef bad_i64_inner (x : UInt64) : UInt64 := (Int64.ofBitVec x.toBitVec / (-1 : Int64)).toBitVec.toNat.toUInt64\n",
            "single_ctor_enum": "inductive Solo where | only\n@[export bad_solo]\ndef bad_solo (s : Solo) : UInt8 := match s with | .only => 1\n",
        }
        with tempfile.TemporaryDirectory(prefix="s1b_failclosed_") as tmp:
            tmpdir = Path(tmp)
            for label, code in rejected_snippets.items():
                p = tmpdir / f"{label}.lean"
                p.write_text(code, encoding="utf-8")
                res = subprocess.run(
                    [full_bin, "emit-lnir", "--wire", str(p), "-o", str(tmpdir / f"{label}.lnir")],
                    capture_output=True,
                    text=True,
                )
                self.assertNotEqual(res.returncode, 0, f"Expected fail-closed rejection for {label}, got stdout={res.stdout}")

            valid_src = tmpdir / "ValidBatch.lean"
            valid_src.write_text(
                "@[export add_u8]\ndef add_u8 (a : UInt8) (b : UInt8) : UInt8 := a + b\n",
                encoding="utf-8",
            )
            wire = tmpdir / "valid.lnir"
            subprocess.run([full_bin, "emit-lnir", "--wire", str(valid_src), "-o", str(wire)], check=True, capture_output=True, text=True)

            mixed_cases = tmpdir / "mixed_cases.jsonl"
            mixed_cases.write_text(
                "\n".join(
                    [
                        json.dumps({"id": "c_ok_1", "decl": "add_u8", "args": [250, 10]}),
                        json.dumps({"id": "c_missing", "decl": "no_such_decl", "args": [1, 2]}),
                        json.dumps({"id": "c_bad_arity", "decl": "add_u8", "args": [1]}),
                        "{malformed json line",
                        '{"id": "c_corrupt_tail", "decl": "add_u8", "args": [1, 2], "junk": }',
                        '{"id": "c_missing_comma", "decl": "add_u8", "args": [1, 2] "extra": 1}',
                        json.dumps({"id": 'c_"quoted"_2', "decl": "add_u8", "args": ["300", "5"]}),
                    ]
                )
                + "\n",
                encoding="utf-8",
            )
            batch_proc = subprocess.run(
                [core_bin, "eval-lnir", "--lnir", str(wire), "--cases-file", str(mixed_cases)],
                capture_output=True,
                text=True,
            )
            self.assertEqual(batch_proc.returncode, 1, batch_proc.stderr)
            rows = json.loads(batch_proc.stdout)
            self.assertEqual(len(rows), 7)
            self.assertEqual((rows[0]["id"], rows[0]["ok"], rows[0]["value_u64"]), ("c_ok_1", True, "4"))
            self.assertEqual((rows[1]["id"], rows[1]["ok"], rows[1]["error"]), ("c_missing", False, "decl_missing_or_ambiguous"))
            self.assertEqual((rows[2]["id"], rows[2]["ok"], rows[2]["error"]), ("c_bad_arity", False, "arity_mismatch"))
            self.assertEqual((rows[3]["ok"], rows[3]["error"]), (False, "malformed_case_json"))
            self.assertEqual((rows[4]["ok"], rows[4]["error"]), (False, "malformed_case_json"))
            self.assertEqual((rows[5]["ok"], rows[5]["error"]), (False, "malformed_case_json"))
            self.assertEqual((rows[6]["id"], rows[6]["ok"], rows[6]["value_u64"]), ('c_"quoted"_2', True, "49"))

            enum256_ctors = "\n".join(f"  | c{i}" for i in range(256))
            enum256_src = tmpdir / "Enum256.lean"
            enum256_src.write_text(
                f"inductive BigEnum where\n{enum256_ctors}\n"
                "@[export big_enum_tag]\ndef big_enum_tag (e : BigEnum) : UInt16 :=\n"
                "  match e with\n  | .c0 => 10\n  | .c255 => 999\n  | _ => 42\n",
                encoding="utf-8",
            )
            enum256_wire = tmpdir / "enum256.lnir"
            subprocess.run([full_bin, "emit-lnir", "--wire", str(enum256_src), "-o", str(enum256_wire)], check=True, capture_output=True, text=True)
            enum256_ll = tmpdir / "enum256.ll"
            subprocess.run([core_bin, "compile-llvm", "--lnir", str(enum256_wire), "--arch", "x86_64", "-o", str(enum256_ll)], check=True, capture_output=True, text=True)
            self.assertIn("define dso_local zeroext i16 @big_enum_tag(i16 zeroext noundef %arg_v0)", enum256_ll.read_text(encoding="utf-8"))

            unsup_and_valid = tmpdir / "unsup_mix.lnir"
            unsup_and_valid.write_text(
                "LNIR_WIRE_V1|54657374|2|"
                "D_decl|6164645f7538|A_TEST|0|1|0|7830|0|T_i8|T_i8|C_ret|0|"
                "D_decl|6261645f756e737570|A_L0|0|1|0|7830|0|T_i64|T_i64|C_ret|0\n",
                encoding="utf-8",
            )
            unsup_cases = tmpdir / "unsup_cases.jsonl"
            unsup_cases.write_text(json.dumps({"id": "c1", "decl": "add_u8", "args": [7]}) + "\n", encoding="utf-8")
            unsup_proc = subprocess.run(
                [core_bin, "eval-lnir", "--lnir", str(unsup_and_valid), "--cases-file", str(unsup_cases)],
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(unsup_proc.returncode, 0, "eval-lnir --cases-file must fail closed on A_L0 module")

            ext_call_lnir = tmpdir / "ext_call.lnir"
            ext_call_lnir.write_text(
                "LNIR_WIRE_V1|54657374|1|D_decl|6261645f657874|A_TEST|0|1|0|7830|0|T_i64|T_i64|"
                "C_let|1|T_i64|E_call|6c5f55496e7436345f6c6f6732|1|1|0|T_i64|C_ret|1\n",
                encoding="utf-8",
            )
            for subcmd in (
                ["compile-llvm", "--lnir", str(ext_call_lnir), "-o", str(tmpdir / "bad_ext.ll")],
                ["compile-static-lib", "--lnir", str(ext_call_lnir), "-o", str(tmpdir / "bad_ext.a")],
            ):
                bad_ext_proc = subprocess.run([core_bin, *subcmd], capture_output=True, text=True)
                self.assertNotEqual(bad_ext_proc.returncode, 0, f"{subcmd[0]} must fail closed on unmodeled external call")
            tv_ext_proc = subprocess.run([core_bin, "validate-tv", "--lnir", str(ext_call_lnir), "--json"], capture_output=True, text=True)
            self.assertNotEqual(tv_ext_proc.returncode, 0, "validate-tv must return non-zero on unmodeled external calls")
            tv_ext = json.loads(tv_ext_proc.stdout)
            self.assertFalse(tv_ext["allPassed"], "validate-tv must not vacuously pass unmodeled external calls")

            json_array_cases = tmpdir / "array_cases.json"
            json_array_cases.write_text(
                json.dumps(
                    [
                        {"case_id": 101, "decl": "add_u8", "args": [200, 100]},
                        {"case_id": 102, "decl": "add_u8", "args": "7,8"},
                    ]
                ),
                encoding="utf-8",
            )
            arr_proc = subprocess.run(
                [core_bin, "eval-lnir", "--lnir", str(wire), "--cases-file", str(json_array_cases)],
                check=True,
                capture_output=True,
                text=True,
            )
            arr_rows = json.loads(arr_proc.stdout)
            self.assertEqual(len(arr_rows), 2)
            self.assertEqual((arr_rows[0]["case_id"], arr_rows[0]["ok"], arr_rows[0]["value_u64"]), (101, True, "44"))
            self.assertEqual((arr_rows[1]["case_id"], arr_rows[1]["ok"], arr_rows[1]["value_u64"]), (102, True, "15"))


if __name__ == "__main__":
    unittest.main()
