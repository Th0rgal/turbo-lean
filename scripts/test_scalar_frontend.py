"""Actual stock-Lean/LNIR/LLVM execution; no Python result oracle."""
import json
import subprocess
import tempfile
import unittest
from pathlib import Path
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


if __name__ == "__main__":
    unittest.main()
