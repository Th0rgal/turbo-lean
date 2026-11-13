import json
import os
import random
import re
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MASK = (1 << 64) - 1


def kmul(a, b):
    result = 0
    for _ in range(64):
        if b & 1:
            result ^= a
        a = ((a << 1) ^ (0x1b if a >> 63 else 0)) & MASK
        b >>= 1
    return result


def emul(a, b):
    result = [0] * 5
    for i in range(3):
        for j in range(3):
            result[i + j] ^= kmul(a[i], b[j])
    for j in (4, 3):
        result[j - 3] ^= result[j]
        result[j - 2] ^= result[j]
    return result[:3]


def clmul64_pair(a, b):
    lo = 0
    for i in range(64):
        if (b >> i) & 1:
            lo ^= (a << i) & MASK
    hi = 0
    for i in range(1, 64):
        if (b >> i) & 1:
            hi ^= (a >> (64 - i)) & MASK
    return lo, hi


def gf2_affine64(x, m, imm8):
    out = 0
    for b in range(8):
        xb = (x >> (b * 8)) & 0xFF
        acc = 0
        for i in range(8):
            row = (m >> ((7 - i) * 8)) & 0xFF
            p = row & xb
            parity = bin(p).count("1") & 1
            acc |= parity << i
        out |= ((acc ^ (imm8 & 0xFF)) & 0xFF) << (b * 8)
    return out


def ternary_logic64(a, b, c, imm8):
    na, nb, nc = (~a) & MASK, (~b) & MASK, (~c) & MASK
    terms = [
        na & nb & nc,
        na & nb & c,
        na & b & nc,
        na & b & c,
        a & nb & nc,
        a & nb & c,
        a & b & nc,
        a & b & c,
    ]
    out = 0
    for bit, term in enumerate(terms):
        if (imm8 >> bit) & 1:
            out |= term
    return out & MASK


def zmm_slice_ref(n, seed):
    acc = 0
    for i in range(n):
        a = (seed + ((i * 0x9E3779B97F4A7C15) & MASK)) & MASK
        b = ((seed ^ 0xFEEDFACECAFEBEEF) + ((i * 0xBF58476D1CE4E5B9) & MASK)) & MASK
        c = (((seed << 7) & MASK) ^ ((i * 0x94D049BB133111EB) & MASK)) & MASK
        lo, hi = clmul64_pair(a, b)
        g = gf2_affine64(lo ^ hi, 0x8040201008040201, 0x63)
        t = ternary_logic64(g, c, a, 0x96)
        acc ^= t
    return acc


class BuildExeP0(unittest.TestCase):
    def test_standalone_io_native_kernels_and_boxing(self):
        with tempfile.TemporaryDirectory(prefix="build-exe-p0-") as tmp:
            out = Path(os.environ.get("TURBO_P0_EVIDENCE_DIR", tmp)).resolve()
            out.mkdir(parents=True, exist_ok=True)
            exe = out / "field-io"
            records = []

            def run(args, expect=0, **kwargs):
                p = subprocess.run(list(map(str, args)), text=True, capture_output=True,
                                   cwd=ROOT / "lean", **kwargs)
                records.append(dict(args=list(map(str, args)), rc=p.returncode,
                                    stdout=p.stdout, stderr=p.stderr))
                (out / "commands.json").write_text(json.dumps(records, indent=2))
                self.assertEqual(p.returncode, expect, p.stderr + p.stdout)
                return p.stdout

            run([ROOT / "lean/.lake/build/bin/lean-native", "build-exe", "--input",
                 ROOT / "scripts/fixtures/BuildExeP0.lean", "-o", exe, "--standalone"])
            rng = random.Random(29385)
            kv = [(0, 0), (0, 1), (1, MASK), (1 << 63, 2), (MASK, MASK),
                  (0x123456789abcdef, 0xfedcba9876543210)]
            kv += [(rng.getrandbits(64), rng.getrandbits(64)) for _ in range(256)]
            ev = [([0, 1, 0], [0, 0, 1]), ([0, 0, 1], [0, 0, 1]),
                  ([1, MASK, 1 << 63], [0xfedcba9876543210, 3, 7])]
            ev += [([rng.getrandbits(64) for _ in range(3)],
                    [rng.getrandbits(64) for _ in range(3)]) for _ in range(128)]
            for a, b in kv:
                self.assertEqual(int(run([exe, "K", a, b])), kmul(a, b))
            for a, b in ev:
                self.assertEqual(list(map(int, run([exe, "E", *a, *b]).split())), emul(a, b))
            for value in (0, 1 << 63, MASK):
                self.assertEqual(int(run([exe, "I", value])), value)
            for n_lanes in (0, 1, 7, 8, 9, 16, 25, 64, 73):
                seed = rng.getrandbits(64)
                self.assertEqual(int(run([exe, "Z", n_lanes, seed])), zmm_slice_ref(n_lanes, seed))
            symbols = run(["nm", "--defined-only", exe])
            (out / "symbols.txt").write_text(symbols)
            for symbol in ("p0_kmul", "p0_emul0", "p0_emul1", "p0_emul2"):
                self.assertEqual(len(re.findall(rf"^\w+ T {symbol}$", symbols, re.M)), 1)
                disasm = run(["objdump", "-d", f"--disassemble={symbol}", exe])
                (out / f"{symbol}.asm").write_text(disasm)
                self.assertRegex(disasm, r"\bvp?clmul")
                self.assertNotRegex(disasm, r"\bcall\w*\s")
            self.assertEqual(len(re.findall(r"^\w+ T p0_zmm_slice_kernel$", symbols, re.M)), 1)
            zmm_disasm = run(["objdump", "-d", "--disassemble=p0_zmm_slice_kernel", exe])
            (out / "p0_zmm_slice_kernel.asm").write_text(zmm_disasm)
            self.assertRegex(zmm_disasm, r"%zmm")
            self.assertRegex(zmm_disasm, r"\bvpclmul\w*.*%zmm")
            self.assertRegex(zmm_disasm, r"\bvgf2p8affineqb\b.*%zmm")
            self.assertRegex(zmm_disasm, r"\bvpternlogq\b.*%zmm")
            self.assertRegex(zmm_disasm, r"\bvmovdqu64\b.*%zmm")
            self.assertNotIn("--allow-multiple-definition", (ROOT / "lean/LeanNative/Driver/BuildExe.lean").read_text())
            sysroot = Path(os.environ["LEAN_SYSROOT"])
            harness = out / "boxing.c"
            harness.write_text('#include <lean/lean.h>\n#include <stdint.h>\n'
                'extern lean_object *lean_native_abi_p0_identity(lean_object *);\n'
                'extern lean_object *lean_native_abi_p0_identity32(lean_object *);\n'
                'extern lean_object *lean_native_abi_p0_identitySize(lean_object *);\n'
                'extern lean_object *lean_native_box_u64(uint64_t);\n'
                'extern uint64_t lean_native_unbox_u64(lean_object *);\n'
                'extern void lean_initialize_runtime_module(void);\n'
                'int main(void) { lean_initialize_runtime_module();\n'
                'uint64_t values[] = {0, UINT64_C(9223372036854775808), UINT64_MAX};\n'
                'for (unsigned i=0; i<3; ++i) {\n'
                'lean_object *a=lean_box_uint64(values[i]);\n'
                'lean_object *b=lean_native_abi_p0_identity(a);\n'
                'lean_object *c=lean_native_box_u64(values[i]);\n'
                'if (lean_unbox_uint64(b)!=values[i] || lean_native_unbox_u64(a)!=values[i]\n'
                ' || lean_unbox_uint64(c)!=values[i]) return 1;\n'
                'lean_dec(a); lean_dec(b); lean_dec(c);\n'
                'a=lean_box_uint32((uint32_t)values[i]); b=lean_native_abi_p0_identity32(a);\n'
                'if (lean_unbox_uint32(b)!=(uint32_t)values[i]) return 2; lean_dec(a); lean_dec(b);\n'
                'a=lean_box_usize((size_t)values[i]); b=lean_native_abi_p0_identitySize(a);\n'
                'if (lean_unbox_usize(b)!=(size_t)values[i]) return 3; lean_dec(a); lean_dec(b);\n'
                '} return 0; }\n')
            run(["/usr/bin/clang", "-O3", "-march=native", "-ffunction-sections", "-fdata-sections",
                 "-c", str(exe) + ".opt.ll", "-o", out / "program.o"])
            run(["objcopy", "--redefine-sym", "main=lean_program_main", out / "program.o"])
            run(["/usr/bin/clang", "-O2", "-I" + str(sysroot / "include"), harness,
                 out / "program.o", str(exe) + ".runtime.c", "-Wl,--gc-sections",
                 "-L" + str(sysroot / "lib/lean"), "-lleanshared",
                 "-Wl,-rpath," + str(sysroot / "lib/lean"), "-o", out / "boxing"])
            run([out / "boxing"])
            bare = out / "bare.c"
            bare.write_text('#include <stdint.h>\n'
                'extern uint64_t p0_identity(uint64_t);\n'
                'extern void *lean_native_abi_p0_identity(void *);\n'
                'int main(int argc, char **argv) {\n'
                'if (argc>1) lean_native_abi_p0_identity((void *)1);\n'
                'return p0_identity(UINT64_MAX)!=UINT64_MAX; }\n')
            run(["/usr/bin/clang", "-O2", "-march=native", bare, str(exe) + ".lnir.ll", "-o", out / "bare"])
            run([out / "bare"])
            run([out / "bare", "missing-runtime"], expect=-4)
            for tool, message in (("llvm-link", "optimized definition merge failed"),
                                  ("opt", "LLVM optimization failed")):
                tools = out / (tool + "-failure")
                tools.mkdir(exist_ok=True)
                fault = tools / tool
                fault.write_text("#!/bin/sh\nexit 73\n")
                fault.chmod(0o755)
                failed = out / (tool + "-preserved")
                failed.write_bytes(b"previous executable")
                run([ROOT / "lean/.lake/build/bin/lean-native", "build-exe", "--input",
                     ROOT / "scripts/fixtures/BuildExeP0.lean", "-o", failed, "--standalone"],
                    expect=1, env={**os.environ, "PATH": str(tools) + os.pathsep + os.environ["PATH"]})
                self.assertIn(message, records[-1]["stderr"])
                self.assertEqual(failed.read_bytes(), b"previous executable")
            unsupported = out / "Unsupported.lean"
            unsupported.write_text('@[export bad_kernel]\ndef bad (x : String) : String := x\n'
                                   'def main : IO Unit := pure ()\n')
            rejected = out / "rejected"
            run([ROOT / "lean/.lake/build/bin/lean-native", "build-exe", "--input",
                 unsupported, "-o", rejected, "--standalone"], expect=1)
            self.assertIn("non-scalar", records[-1]["stderr"])
            self.assertFalse(rejected.exists())
            (out / "result.json").write_text(json.dumps(dict(k=len(kv), e=len(ev),
                uint64=[0, 1 << 63, MASK], standalone=True, native_clmul=True)))


if __name__ == "__main__":
    unittest.main()
