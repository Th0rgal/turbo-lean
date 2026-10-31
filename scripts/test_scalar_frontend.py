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
    def test_small_width_comparisons(self):
        engines = fuzzer.probe_engines()
        self.assertTrue(all(engines[k] for k in ("stock_lean_c", "lnir_eval", "c_abi_llvm")), engines)
        trees = [{"k": "ite_input", "bits": bits, "boundary": n, "op": op}
                 for bits in (8, 16) for op in ("==", "<", "<=")
                 for n in (0, 1, 2**bits - 1)]
        programs = [{"seed": i, "arg0": v, "tree": t}
                    for i, (t, v) in enumerate((t, v) for t in trees
                    for v in (0, 1, 255, 256, 65535, 65536, 2**32 - 1, 2**32, 2**64 - 1))]
        try:
            result = fuzzer.run_three_way_batch(programs, engines)
        except subprocess.CalledProcessError as error:
            self.fail(f"real engine failed: {error}; stdout={error.stdout}; stderr={error.stderr}")
        print(json.dumps(result, sort_keys=True))
        self.assertEqual(result["executed_count"], len(programs))
        self.assertEqual(result["mismatches"], [])

    def test_narrow_wrapping_arithmetic_shifts_and_div_zero(self):
        engines = fuzzer.probe_engines()
        self.assertTrue(all(engines[k] for k in ("stock_lean_c", "lnir_eval", "c_abi_llvm")), engines)
        exprs = []
        for w, maxv, sh_wrap, hi_bit in ((8, 255, 8, 128), (16, 65535, 16, 32768), (32, 4294967295, 32, 2147483648)):
            cast = f"x0.toUInt{w}"
            exprs.extend([
                f"(({cast} + (1 : UInt{w})).toUInt64 + (if {cast} + (1 : UInt{w}) == 0 then 100 else 0))",
                f"(({cast} - (1 : UInt{w})).toUInt64 + (if {cast} - (1 : UInt{w}) == ({maxv} : UInt{w}) then 200 else 0))",
                f"(({cast} * (3 : UInt{w})).toUInt64)",
                f"(((1 : UInt{w}) <<< ({sh_wrap} : UInt{w})).toUInt64 + (({hi_bit} : UInt{w}) <<< (1 : UInt{w})).toUInt64 + ({cast} <<< ({cast} + ({sh_wrap} : UInt{w}))).toUInt64)",
                f"((({hi_bit} : UInt{w}) >>> ({sh_wrap} : UInt{w})).toUInt64 + ({cast} >>> ({cast} + ({sh_wrap} : UInt{w}))).toUInt64)",
                f"(({cast} / (0 : UInt{w})).toUInt64 + ({cast} % (0 : UInt{w})).toUInt64 + ({cast} / (({cast} &&& 3) + 1)).toUInt64 + ({cast} % (({cast} &&& 3) + 1)).toUInt64)",
                f"(({cast} / ({cast} &&& 1)).toUInt64 + ({cast} % ({cast} &&& 1)).toUInt64)",
            ])
        inputs = (0, 1, 2, 7, 8, 127, 128, 255, 256, 32768, 65535, 65536, 2**31, 2**32 - 1, 2**32, 2**64 - 1)
        programs = [{"seed": i, "arg0": v, "tree": {"k": "raw_lean", "expr": e}}
                    for i, (e, v) in enumerate((e, v) for e in exprs for v in inputs)]
        result = fuzzer.run_three_way_batch(programs, engines)
        self.assertEqual(result["executed_count"], len(programs))
        self.assertEqual(result["mismatches"], [])

    def test_join_point_param_swap_and_nested_helper_inlining(self):
        engines = fuzzer.probe_engines()
        self.assertTrue(all(engines[k] for k in ("stock_lean_c", "lnir_eval", "c_abi_llvm")), engines)
        preamble = '''def leafHelper (a b : UInt64) : UInt64 := (a * 17) ^^^ (b + 9)
def pairHelper (x y : UInt64) : UInt64 × UInt64 :=
  if x < y then (leafHelper y x, leafHelper x y) else (leafHelper x y, leafHelper y x)
def outerHelper (u v : UInt64) : UInt64 :=
  let p := pairHelper u v
  if (u &&& 1) == 0 then leafHelper p.1 p.2 + leafHelper p.2 u
  else leafHelper p.2 p.1 ^^^ leafHelper p.1 v
'''
        exprs = [
            '''(let a := x0 + 3
                let b := (x0 ^^^ 0x55) + 11
                let swapped := if (x0 &&& 1) == 1 then (b, a) else (a, b)
                let swapped2 := if (x0 &&& 2) == 2 then (swapped.2, swapped.1) else (swapped.1, swapped.2)
                swapped2.1 * 257 + swapped2.2)''',
            '''(let r1 := if (x0 &&& 4) == 0 then outerHelper x0 (x0 + 13) else outerHelper (x0 + 29) x0
                let r2 := outerHelper (r1 &&& 255) ((x0 >>> 3) &&& 255)
                r1 ^^^ r2)''',
        ]
        inputs = (0, 1, 2, 3, 4, 5, 6, 7, 42, 255, 256, 65535, 2**32 - 1, 2**64 - 1)
        programs = [{"seed": i, "arg0": v, "preamble": preamble, "tree": {"k": "raw_lean", "expr": e}}
                    for i, (e, v) in enumerate((e, v) for e in exprs for v in inputs)]
        result = fuzzer.run_three_way_batch(programs, engines)
        self.assertEqual(result["executed_count"], len(programs))
        self.assertEqual(result["mismatches"], [])

    def test_chained_boolean_join_points_and_tuple_helpers(self):
        engines = fuzzer.probe_engines()
        self.assertTrue(all(engines[k] for k in ("stock_lean_c", "lnir_eval", "c_abi_llvm")), engines)
        preamble = '''def taskcardStep (turnEnded allClosed turnOutcomeFinished : UInt8) : UInt8 :=
  if turnEnded == 0 then 0
  else if allClosed == 1 then 1
  else if turnOutcomeFinished == 1 then 2
  else 3
def attributionInScope (principalKind claimedKind sameMission isDescendant : UInt8) : Bool :=
  claimedKind == 0 ||
  (principalKind == 5 && (claimedKind == 1 || claimedKind == 2 || claimedKind == 5)) ||
  ((principalKind == 1 || principalKind == 2) &&
    ((claimedKind == 1 && sameMission == 1) || (claimedKind == 2 && isDescendant == 1))) ||
  ((principalKind == 3 || principalKind == 4 || principalKind == 6) && claimedKind == principalKind)
def attributionPrincipal (principalKind : UInt8) : UInt8 :=
  if principalKind ≤ 6 then principalKind else 0
def attributionKind (principalKind claimedKind sameMission isDescendant : UInt8) : UInt8 :=
  if attributionInScope (attributionPrincipal principalKind) claimedKind sameMission isDescendant then
    (if claimedKind == 0 then attributionPrincipal principalKind else claimedKind)
  else attributionPrincipal principalKind
def attributionStep (principalKind claimedKind sameMission isDescendant : UInt8) : UInt32 :=
  (attributionKind principalKind claimedKind sameMission isDescendant).toUInt32 |||
    (if attributionInScope (attributionPrincipal principalKind) claimedKind sameMission isDescendant
     then 256 else 0)
def streamNextFencePair
    (openKind : UInt8) (openCount : UInt32) (markerKind : UInt8) (markerCount : UInt32) : UInt8 × UInt32 :=
  if openKind == 0 then
    if (markerKind == 1 || markerKind == 2) && 3 ≤ markerCount then (markerKind, markerCount) else (0, 0)
  else
    if markerKind == openKind && openCount ≤ markerCount && 3 ≤ markerCount then (0, 0) else (openKind, openCount)
def streamFenceStep
    (openKind : UInt8) (openCount : UInt32) (markerKind : UInt8) (markerCount : UInt32) : UInt64 :=
  let p := streamNextFencePair openKind openCount markerKind markerCount
  p.1.toUInt64 ||| (p.2.toUInt64 <<< 32)
'''
        exprs = [
            '''(let rawStatus := x0.toUInt8
                let turnEnded := (x0 >>> 8).toUInt8
                let allClosed := (x0 >>> 16).toUInt8
                let turnOutcomeFinished := (x0 >>> 24).toUInt8
                let norm : UInt8 :=
                  if rawStatus == 2 then 2
                  else if rawStatus == 3 then 3
                  else if rawStatus == 1 && turnEnded == 0 then 1
                  else 0
                let done : UInt32 := if norm == 2 then 256 else 0
                let active : UInt32 := if norm == 1 then 65536 else 0
                let card : UInt32 := (taskcardStep turnEnded allClosed turnOutcomeFinished).toUInt32 <<< 24
                (norm.toUInt32 ||| done ||| active ||| card).toUInt64)''',
            '''(let u0 := x0.toUInt8
                let u1 := (x0 >>> 8).toUInt8
                let u2 := (x0 >>> 16).toUInt8
                let u3 := (x0 >>> 24).toUInt8
                (attributionStep u0 u1 u2 u3).toUInt64)''',
            '''(let openKind := x0.toUInt8
                let openCount := x0.toUInt32
                let markerKind := (x0 >>> 32).toUInt8
                let markerCount := (x0 >>> 32).toUInt32
                streamFenceStep openKind openCount markerKind markerCount)''',
            '''(let tick := x0.toUInt8
                let openKind := (x0 >>> 8).toUInt8
                let openCount := (x0 >>> 16).toUInt32
                let lineBlank := (x0 >>> 48).toUInt8
                let lineTick := (x0 >>> 56).toUInt8
                let markerKind := (x0 >>> 16).toUInt8
                let markerCount := (x0 >>> 24).toUInt32
                let pos := (x0 >>> 16).toUInt32
                let commit := (x0 >>> 24).toUInt32
                let nextTick : UInt8 := if lineTick == 1 then (if tick == 1 then 0 else 1) else (if tick == 1 then 1 else 0)
                let nextFenceKind := (streamNextFencePair openKind openCount markerKind markerCount).1
                let nextPos := if pos ≤ 0xFFFFFFFF - 1 then pos + 1 else 0xFFFFFFFF
                let commits : UInt8 := if lineBlank == 1 && nextTick == 0 && nextFenceKind == 0 then 1 else 0
                let nextCommit : UInt32 := if commits == 1 then nextPos else commit
                let nextFenceBits : UInt32 :=
                  if nextFenceKind == 1 then 256 else if nextFenceKind == 2 then 512 else 0
                let commitBits : UInt32 := if commits == 1 then 65536 else 0
                let lo32 : UInt32 := nextTick.toUInt32 ||| nextFenceBits ||| commitBits
                lo32.toUInt64 ||| (nextCommit.toUInt64 <<< 32))''',
        ]
        inputs = (0, 1, 255, 0x010204080F112233, 0x7FAA55FF00CC9933)
        programs = [{"seed": i, "arg0": v, "preamble": preamble, "tree": {"k": "raw_lean", "expr": e}}
                    for i, (e, v) in enumerate((e, v) for e in exprs for v in inputs)]
        result = fuzzer.run_three_way_batch(programs, engines)
        self.assertEqual(result["executed_count"], len(programs))
        self.assertEqual(result["mismatches"], [])

    def test_primitive_boundaries(self):
        # Run the actual Lean bridge: same leaf names, mismatched types/arity
        # and local calls must stay outside the canonical intrinsic boundary.
        source = '''import LeanNative.IR.Bridge
open LeanNative.IR
#guard canonicalUIntCastMask? `UInt64.toUInt8 [.i64] .i8 == some 255
#guard canonicalUIntCastMask? `UInt8.toUInt64 [.i8] .i64 == some 255
#guard canonicalUIntCastMask? `UInt16.toUInt32 [.i16] .i32 == some 65535
#guard canonicalUIntCastMask? `UInt32.toUInt16 [.i32] .i16 == some 65535
#guard canonicalUIntCastMask? `UInt32.toUInt64 [.i32] .i64 == some 4294967295
#guard canonicalUIntCastMask? `User.UInt64.toUInt8 [.i64] .i8 == none
#guard canonicalUIntCastMask? `UInt64.toUInt8 [.i32] .i8 == none
#guard canonicalUIntCastMask? `UInt64.toUInt8 [.i64] .i32 == none
#guard canonicalUIntCastMask? `UInt64.toUInt8 [] .i8 == none
#guard canonicalUIntCastMask? `UInt64.toUInt8 [.i64, .i64] .i8 == none
#guard lookupCanonicalBinOp? `UInt32.blt == some .lt
#guard lookupCanonicalBinOp? `UInt32.ble == some .le
#guard lookupCanonicalBinOp? `USize.blt == some .lt
#guard lookupCanonicalBinOp? `USize.ble == some .le
#eval do
  let env ← Lean.mkEmptyEnvironment
  let rejected : List (Lean.Name × List VarId × LNIRType × List LNIRType × Bool) :=
      [(`UInt64.toUInt8, [0], .i8, [.i64], true),
       (`User.UInt64.toUInt8, [0], .i8, [.i64], false),
       (`UInt64.toUInt8, [0], .i8, [.i32], false),
       (`UInt64.toUInt8, [0], .i32, [.i64], false),
       (`UInt64.toUInt8, [], .i8, [], false),
       (`UInt64.toUInt8, [0, 1], .i8, [.i64, .i64], false),
       (`UInt64.decEq, [0, 1], .i8, [.i64, .i64], true),
       (`UInt8.decEq, [0, 1], .i8, [.i32, .i32], false),
       (`UInt8.add, [0, 1], .i64, [.i8, .i8], false),
       (`UInt16.decLe, [0, 1], .i64, [.i16, .i16], false),
       (`UInt32.add, [0, 1], .i32, [.i64, .i64], false),
       (`UInt64.mul, [0, 1], .i64, [.i32, .i32], false),
       (`USize.sub, [0, 1], .usize, [.i64, .i64], false),
       (`User.UInt8.decEq, [0, 1], .i8, [.i8, .i8], false)]
  for (name, args, ret, tys, localCall) in rejected do
    unless (tryLowerIntrinsicCall env name args ret tys localCall).isNone do
      throw (IO.userError s!"unexpected intrinsic: {name}")
  match tryLowerIntrinsicCall env `UInt64.decEq [0, 1] .i8 [.i64, .i64] with
  | some (.scalar (.select (.binOp .eq _ _) (.constU64 1) (.constU64 0))) => pure ()
  | _ => throw (IO.userError "UInt8 comparison lost its numeric representation")
'''
        source += '''
def signedInner (x : UInt64) : UInt64 := (Int64.ofBitVec x.toBitVec / (-1 : Int64)).toBitVec.toNat.toUInt64
def signedOuter (x : UInt64) : UInt64 := signedInner x + 1
def signedOuter2 (x : UInt64) : UInt64 := signedOuter x * 3
def unsignedInner (x : UInt64) : UInt64 := x / 3
def unsignedOuter (x : UInt64) : UInt64 := unsignedInner x + 1
#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  let some outer := env.find? `signedOuter2 | Lean.throwError "missing signedOuter2"
  if outer.value?.any exprUsesSignedScalarType then Lean.throwError "fixture is not transitive"
  for (n, expected) in [(`signedOuter2, true), (`signedOuter, true), (`unsignedOuter, false)] do
    let some d ← Lean.Compiler.LCNF.getBaseDecl? n | Lean.throwError s!"no base decl {n}"
    unless (← declUsesSignedScalarTransitively d) == expected do
      Lean.throwError s!"transitive signed scan wrong for {n}"
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
            "signed_int64_transitive": "def sInner (x : UInt64) : UInt64 := (Int64.ofBitVec x.toBitVec / (-1 : Int64)).toBitVec.toNat.toUInt64\n@[export s_outer]\ndef sOuter (x : UInt64) : UInt64 := sInner x + 1\n",
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
                        json.dumps({"id": "c_\u00e9\U0001F600\x01", "decl": "add_\u0075\u0038", "args": [1, 2]}),
                        '{"id": "c_raw_ctl\x01", "decl": "add_u8", "args": [1, 2]}',
                        '{"id": "c_lone_surrogate", "decl": "add_u8\\uD800", "args": [1, 2]}',
                        '{"id": "c_bad_hex", "decl": "add_u\\u00G8", "args": [1, 2]}',
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
            self.assertEqual(len(rows), 11)
            self.assertEqual((rows[0]["id"], rows[0]["ok"], rows[0]["value_u64"]), ("c_ok_1", True, "4"))
            self.assertEqual((rows[1]["id"], rows[1]["ok"], rows[1]["error"]), ("c_missing", False, "decl_missing_or_ambiguous"))
            self.assertEqual((rows[2]["id"], rows[2]["ok"], rows[2]["error"]), ("c_bad_arity", False, "arity_mismatch"))
            self.assertEqual((rows[3]["ok"], rows[3]["error"]), (False, "malformed_case_json"))
            self.assertEqual((rows[4]["ok"], rows[4]["error"]), (False, "malformed_case_json"))
            self.assertEqual((rows[5]["ok"], rows[5]["error"]), (False, "malformed_case_json"))
            self.assertEqual((rows[6]["id"], rows[6]["ok"], rows[6]["value_u64"]), ('c_"quoted"_2', True, "49"))
            self.assertEqual((rows[7]["id"], rows[7]["ok"], rows[7]["value_u64"]), ("c_\u00e9\U0001F600\x01", True, "3"))
            for row in rows[8:]:
                self.assertEqual((row["ok"], row["error"]), (False, "malformed_case_json"))

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

    def test_self_tail_and_non_tail_recursion_and_string_literals_fail_closed(self):
        cases = [
            ("self_tail_rec", '''@[export count_tail]
def countTail : Nat → UInt64 → UInt64
  | 0, acc => acc
  | n+1, acc => countTail n (acc+1)
'''),
            ("non_tail_rec", '''@[export sum_non_tail]
def sumNonTail : Nat → UInt64
  | 0 => 0
  | n + 1 => 1 + sumNonTail n
'''),
            ("mutual_rec", '''mutual
def isEven : Nat → UInt64
  | 0 => 1
  | n + 1 => isOdd n
def isOdd : Nat → UInt64
  | 0 => 0
  | n + 1 => isEven n
end
@[export check_even]
def checkEven (n : Nat) : UInt64 := isEven n
'''),
            ("u64_self_tail_rec", '''@[export count_u64]
partial def countU64 (n acc : UInt64) : UInt64 :=
  if n == 0 then acc else countU64 (n - 1) (acc + 1)
'''),
            ("string_lit", '''@[export str_bad]
def strBad (x : UInt64) : String :=
  if x == 0 then "hello" else "world"
'''),
            ("exported_tuple", '''@[export bad_exp_tup]
def badExpTup (x : UInt8) (y : UInt32) : UInt8 × UInt32 := (x, y)
'''),
            ("nested_tuple_helper", '''def nestedPair (x : UInt64) : (UInt64 × UInt64) × UInt64 := ((x, x + 1), x + 2)
@[export call_nested_pair]
def callNestedPair (x : UInt64) : UInt64 :=
  let p := nestedPair x
  p.1.1 + p.1.2 + p.2
'''),
        ]
        for label, src in cases:
            with self.subTest(label=label), tempfile.TemporaryDirectory(prefix=f"fail_closed_{label}_") as directory:
                source = Path(directory) / "Bad.lean"
                source.write_text(src)
                output = Path(directory) / "module.lnir"
                result = subprocess.run([str(fuzzer.LEAN_NATIVE_FULL), "emit-lnir", "--wire", str(source),
                                         "-o", str(output)], capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0, f"{label}: {result.stdout + result.stderr}")
                self.assertFalse(output.exists(), f"{label} published an artifact despite failure")

    def test_unsupported_lcnf_paths_fail_closed(self):
        source = '''import LeanNative.IR.Bridge
open Lean LeanNative.IR Lean.Compiler.LCNF
run_meta do
  let j : FVarId := ⟨`join⟩
  let x : FVarId := ⟨`value⟩
  let r : FVarId := ⟨`res⟩
  let ty := mkConst ``UInt64
  let recursive : FunDecl .impure := .mk j `join #[] ty (.jmp j #[])
  let recLocalFn : FunDecl .pure := .mk j `recFn #[.mk x `p0 ty false] ty (.let ⟨r, `r, ty, .fvar j #[.fvar x]⟩ (.return r))
  let p0 : Param .pure := .mk x `p0 ty false
  let actions : List (String × BridgeM LNIRCode) :=
    [("recursive join point", lowerImpureCode (.jp recursive (.jmp j #[]))),
     ("unmapped join point", lowerImpureCode (.jmp j #[.fvar x])),
     ("arity mismatch", lowerImpureCode (.jp (.mk j `join #[] ty (.return x)) (.jmp j #[.fvar x]))),
     ("constructor tag mutation", lowerImpureCode (.setTag x 1 (.return x))),
     ("recursive local function", lowerPureCode (.fun recLocalFn (.return x))),
             ("higher-order fvar call", lowerPureLetValue (.fvar x #[.fvar x]) .i64 >>= fun _ => pure (.ret 0)),
             ("constructor payload pattern", lowerPureAlts 0 false 0 [.alt `Boxed.mk #[p0] (.return x)]),
             ("unsupported string literal", lowerLitValue (.str "abc") >>= fun _ => pure (.ret 0)),
             ("Unsupported heap reset", lowerImpureLetValue (.reset 2 x rfl) .objPtr >>= fun _ => pure (.ret 0))]
  for (expected, action) in actions do
    let rejected ← try
      let _ ← action.run' {}
      pure false
    catch error =>
      let message ← error.toMessageData.toString
      unless (message.splitOn expected).length > 1 do
        throwError "wrong rejection for {expected}: {message}"
      pure true
    unless rejected do throwError "accepted unsupported {expected}"
  let ordinary : FunDecl .impure := .mk j `join #[] ty (.return x)
  let _ ← (lowerImpureCode (.jp ordinary (.jmp j #[]))).run' { varTypes := ({} : Std.HashMap VarId LNIRType).insert 0 .i64, fvarToVar := ({} : Std.HashMap FVarId VarId).insert x 0, nextVarId := 1 }
'''
        with tempfile.TemporaryDirectory(prefix="unsupported_lcnf_") as directory:
            path = Path(directory) / "Boundary.lean"
            path.write_text(source)
            result = subprocess.run(["lake", "env", "lean", str(path)], cwd=fuzzer.ROOT / "lean",
                                    capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_telemetry_mode_flags_opt_in_and_default_off(self):
        engines = fuzzer.probe_engines()
        core_bin = engines["core_bin"]
        with tempfile.TemporaryDirectory(prefix="telemetry_flag_") as directory:
            tmp = Path(directory)
            src = tmp / "TelProbe.lean"
            src.write_text("@[export tel_id]\ndef tel_id (x : UInt64) : UInt64 := x + 1\n", encoding="utf-8")
            wire = tmp / "tel.lnir"
            subprocess.run([engines["full_bin"], "emit-lnir", "--wire", str(src), "-o", str(wire)],
                           check=True, capture_output=True, text=True)
            spool_default = tmp / "spool_default"
            subprocess.run(
                [core_bin, "compile-llvm", "--lnir", str(wire), "-o", str(tmp / "d.ll")],
                env={**dict(__import__("os").environ), "LEAN_NATIVE_TELEMETRY_DIR": str(spool_default)},
                check=True, capture_output=True, text=True,
            )
            self.assertFalse(spool_default.exists(), "compile-llvm without --telemetry* must not emit telemetry")
            for mode_flag in ("--telemetry=metrics", "--telemetry=local", "--telemetry"):
                spool_mode = tmp / f"spool_{mode_flag.replace('-', '_').replace('=', '_')}"
                subprocess.run(
                    [core_bin, "compile-llvm", mode_flag, "--lnir", str(wire), "-o", str(tmp / "m.ll")],
                    env={**dict(__import__("os").environ), "LEAN_NATIVE_TELEMETRY_DIR": str(spool_mode)},
                    check=True, capture_output=True, text=True,
                )
                self.assertTrue((spool_mode / "events.jsonl").is_file(), f"{mode_flag} failed to emit events.jsonl")

    def test_validate_ingested_module_deduplicates_diamond_and_duplicate_call_edges(self):
        engines = fuzzer.probe_engines()
        lean_src = """def k (x : UInt64) : UInt64 := (x ^^^ 0x9e3779b97f4a7c15) + 1

def g (x : UInt64) : UInt64 :=
  let a := k x
  let b := k (a + 3)
  a ^^^ b

def h (x : UInt64) : UInt64 :=
  let a := k (x + 7)
  let b := k (a + 11)
  a + b

@[export diamond_entry]
def f (x : UInt64) : UInt64 :=
  let p := g x
  let q := h x
  let r := g (p + 1)
  let s := h (q + 1)
  (p ^^^ q) + (r ^^^ s)
"""
        with tempfile.TemporaryDirectory(prefix="dup_call_edges_") as directory:
            tmp = Path(directory)
            src = tmp / "Diamond.lean"
            src.write_text(lean_src, encoding="utf-8")
            wire = tmp / "diamond.lnir"
            res = subprocess.run(
                [engines["full_bin"], "emit-lnir", "--wire", "--arch", "x86_64", str(src), "-o", str(wire)],
                capture_output=True, text=True,
            )
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            cases_jsonl = tmp / "cases.jsonl"
            cases_jsonl.write_text(
                "\n".join(json.dumps(c) for c in [
                    {"id": "c0", "decl": "diamond_entry", "args": [0]},
                    {"id": "c1", "decl": "diamond_entry", "args": [42]},
                ]) + "\n",
                encoding="utf-8",
            )
            ev_res = subprocess.run(
                [engines["core_bin"], "eval-lnir", "--lnir", str(wire), "--arch", "x86_64", "--opt", "--cases-file", str(cases_jsonl)],
                capture_output=True, text=True,
            )
            self.assertEqual(ev_res.returncode, 0, ev_res.stdout + ev_res.stderr)
            ev_rows = json.loads(ev_res.stdout)
            stock_src = tmp / "StockDiamond.lean"
            stock_src.write_text(
                lean_src
                + '\ndef main : IO Unit := IO.println s!"[{f 0},{f 42}]"\n',
                encoding="utf-8",
            )
            stock_out = subprocess.check_output(
                ["lake", "env", "lean", "--run", str(stock_src)],
                cwd=fuzzer.ROOT / "lean",
                text=True,
            )
            self.assertEqual([int(r["value_u64"]) for r in ev_rows], json.loads(stock_out))

    def test_stage1d_heap_adt_perceus_reuse_alias_drop_tv_and_fail_closed_llvm(self):
        engines = fuzzer.probe_engines()
        lean_src = """inductive RcPacket where
  | pair : (UInt64 × UInt64) → (UInt64 × UInt64) → RcPacket
  | empty : RcPacket

@[inline] def foldPacket (pkt : RcPacket) : UInt64 :=
  match pkt with
  | .pair p q => ((p.1 * 1315423911) + p.2) ^^^ ((q.1 * 2654435761) + q.2)
  | .empty => 0x9E3779B97F4A7C15

@[inline] def stepPacket (pkt : RcPacket) (delta : UInt64) : RcPacket :=
  match pkt with
  | .pair p q => .pair (p.1 + delta, p.2 ^^^ delta) (q.1 + (delta <<< 1), q.2 + 17)
  | .empty => .empty

@[export probe_rc_reuse]
def probe_rc_reuse (seed delta : UInt64) : UInt64 :=
  let p0 := if seed == 0 then RcPacket.empty else RcPacket.pair (seed, seed + 5) (delta, delta + 11)
  foldPacket (stepPacket (stepPacket p0 (delta + 1)) (delta ^^^ 7))

@[export probe_rc_alias]
def probe_rc_alias (seed delta : UInt64) : UInt64 :=
  let base := RcPacket.pair (seed, seed ^^^ 0x9E3779B97F4A7C15) (delta + 3, seed + delta)
  foldPacket base + (foldPacket (stepPacket base (delta + 5)) ^^^ foldPacket (stepPacket base (delta + 19)))

@[inline] def swapPairIf (flag : UInt64) (p : UInt64 × UInt64) : UInt64 × UInt64 :=
  if (flag &&& 1) == 0 then (p.1 + 3, p.2 ^^^ 5) else (p.2 + 7, p.1 ^^^ 11)

@[export probe_rc_drop]
def probe_rc_drop (sel seed delta : UInt64) : UInt64 :=
  let live := RcPacket.pair (seed + 1, delta + 2) (seed ^^^ delta, seed + 29)
  let dead := RcPacket.pair (seed * 7, delta * 11) (seed + 41, delta + 43)
  let base :=
    if (sel &&& 1) == 0 then (foldPacket (stepPacket live delta), delta)
    else (foldPacket (stepPacket dead (delta + 9)), delta + 9)
  let chosen := swapPairIf seed base
  chosen.1 ^^^ chosen.2
"""
        with tempfile.TemporaryDirectory(prefix="stage1d_heap_rc_") as directory:
            tmp = Path(directory)
            src = tmp / "Stage1DHeap.lean"
            src.write_text(lean_src, encoding="utf-8")
            wire = tmp / "stage1d.lnir"
            res = subprocess.run(
                [engines["full_bin"], "emit-lnir", "--wire", str(src), "-o", str(wire)],
                capture_output=True, text=True,
            )
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            wire_text = wire.read_text(encoding="utf-8")
            for op in ("C_inc", "C_dec", "E_ctor", "E_cgeto", "E_isexcl", "E_mktup", "E_projtup", "C_ite"):
                self.assertGreater(wire_text.count(op), 0, f"missing expected opcode {op} in Stage 1D wire")
            tv = json.loads(subprocess.check_output(
                [engines["core_bin"], "validate-tv", "--lnir", str(wire), "--json"], text=True,
            ))
            self.assertTrue(tv.get("allPassed"), tv)
            llvm_out = tmp / "bad.ll"
            llvm_res = subprocess.run(
                [engines["core_bin"], "compile-llvm", "--lnir", str(wire), "-o", str(llvm_out)],
                capture_output=True, text=True,
            )
            self.assertNotEqual(llvm_res.returncode, 0, "compile-llvm must fail closed on Stage 1D heap ops")
            self.assertFalse(llvm_out.exists())
            stock_src = tmp / "StockStage1D.lean"
            stock_src.write_text(
                lean_src + '\ndef main : IO Unit := IO.println s!"[{probe_rc_reuse 0 7},{probe_rc_reuse 42 7},{probe_rc_alias 42 7},{probe_rc_drop 0 42 7},{probe_rc_drop 1 42 7}]"\n',
                encoding="utf-8",
            )
            expected = json.loads(subprocess.check_output(
                ["lake", "env", "lean", "--run", str(stock_src)], cwd=fuzzer.ROOT / "lean", text=True,
            ))
            probes = [("probe_rc_reuse", [0, 7]), ("probe_rc_reuse", [42, 7]), ("probe_rc_alias", [42, 7]),
                      ("probe_rc_drop", [0, 42, 7]), ("probe_rc_drop", [1, 42, 7])]
            for extra in ([], ["--opt"]):
                got = []
                for sym, args in probes:
                    row = json.loads(subprocess.check_output(
                        [engines["core_bin"], "eval-lnir", "--lnir", str(wire), "--args",
                         f"{sym}:" + ",".join(map(str, args)), "--batch-json", *extra], text=True,
                    ))[0]
                    self.assertTrue(row.get("ok"), row)
                    self.assertEqual(row.get("live_objects"), 0, row)
                    got.append(int(row["value_u64"]))
                self.assertEqual(got, expected)

            # 3-field tuple-carrying heap ADT validates cleanly under SymbolicTV (`nonVacuousCount > 0`)
            tri_src = tmp / "TriPacket.lean"
            tri_src.write_text('''inductive TriPacket where
  | tri : (UInt64 × UInt64) → (UInt64 × UInt64) → (UInt64 × UInt64) → TriPacket
  | empty : TriPacket

@[inline] def stepTriField (p : TriPacket) (d : UInt64) : TriPacket :=
  match p with
  | .tri a b c => .tri (a.1 + d, a.2) b (c.1 ^^^ d, c.2 + 1)
  | .empty => .empty

@[inline] def readThirdField (p : TriPacket) : UInt64 :=
  match p with
  | .tri a b c => a.1 + b.2 + c.1 + c.2
  | .empty => 99

@[export probe_tri]
def probe_tri (x : UInt64) : UInt64 :=
  let init := if x == 0 then TriPacket.empty else TriPacket.tri (x, x + 1) (x + 3, x + 4) (x + 5, x + 6)
  readThirdField (stepTriField init 7)
''', encoding="utf-8")
            tri_wire = tmp / "tri.lnir"
            subprocess.run([engines["full_bin"], "emit-lnir", "--wire", str(tri_src), "-o", str(tri_wire)],
                           check=True, capture_output=True, text=True)
            tri_tv = json.loads(subprocess.check_output(
                [engines["core_bin"], "validate-tv", "--lnir", str(tri_wire), "--json"], text=True,
            ))
            self.assertTrue(tri_tv.get("allPassed"), tri_tv)

            # Direct scalar-payload heap ADT (`sproj`/`sset`) fails closed instead of accepting without projection lowering
            bad_scalar_adt = tmp / "BadScalarAdt.lean"
            bad_scalar_adt.write_text('''inductive DirectScalarPkt where
  | data : UInt64 → DirectScalarPkt
  | empty : DirectScalarPkt

def readDirect (p : DirectScalarPkt) : UInt64 :=
  match p with
  | .data x => x + 1
  | .empty => 0

@[export probe_bad_direct]
def probe_bad_direct (x : UInt64) : UInt64 := readDirect (.data x)
''', encoding="utf-8")
            bad_wire = tmp / "bad_scalar_adt.lnir"
            bad_res = subprocess.run(
                [engines["full_bin"], "emit-lnir", "--wire", str(bad_scalar_adt), "-o", str(bad_wire)],
                capture_output=True, text=True,
            )
            self.assertNotEqual(bad_res.returncode, 0, "direct scalar-payload heap ADT must fail closed")
            self.assertFalse(bad_wire.exists())

            # SymbolicTV sees `lean_native_ctor_set` writes through `.scalar (.var a)` object aliases
            alias_tv = tmp / "AliasTv.lean"
            alias_tv.write_text('''import LeanNative.Proofs.SymbolicTV
open LeanNative.IR LeanNative.Proofs
#eval show IO Unit from do
  let mkDecl (readVar : VarId) : LNIRDecl := {
    name := "alias_write_test"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .i64
    body :=
      .letBind 1 .i64 (.scalar (.constU64 1))
        (.letBind 2 .objPtr (.allocCtor 0 [1] [])
          (.letBind 3 .objPtr (.scalar (.var 2))
            (.letBind 4 .i64 (.scalar (.constU64 0))
              (.letBind 5 .i64 (.scalar (.constU64 2))
                (.letBind 6 .unit (.call "lean_native_ctor_set" [2, 4, 5] .unit false)
                  (.letBind 7 .i64 (.ctorGetObj readVar 0)
                    (.decRef 2 1 (.ret 7))))))))
  }
  let res := validateTranslationDecl (mkDecl 3) (mkDecl 2) 8
  unless res.passed && res.symRetEquiv do
    throw <| IO.userError s!"alias TV failed: {reprStr res}"
  -- 1. Constructor mutation on input object with x == 999 guard (outside concrete 1..8 samples) must be rejected by memWritesEquiv
  let mkGuardedMutation (badBranch : Bool) : LNIRDecl := {
    name := "ctor_set_mem_summary"
    params := [{ id := 0, name := "p", ty := .objPtr, borrow := false }, { id := 1, name := "x", ty := .i64, borrow := false }]
    retTy := .i64
    body :=
      .letBind 2 .i1 (.isExclusive 0)
        (.ite 2
          (.letBind 3 .i64 (.scalar (.constU64 0))
            (.letBind 4 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
              (.letBind 5 .i64 (.scalar (if badBranch then .select (.var 4) (.constU64 3) (.constU64 2) else .constU64 2))
                (.letBind 6 .unit (.call "lean_native_ctor_set" [0, 3, 5] .unit false)
                  (.letBind 7 .i64 (.scalar (.constU64 0)) (.ret 7))))))
          (.letBind 7 .i64 (.scalar (.constU64 0)) (.ret 7)))
  }
  let mutRes := validateTranslationDecl (mkGuardedMutation false) (mkGuardedMutation true) 8
  unless !mutRes.memWritesEquiv && !mutRes.passed do
    throw <| IO.userError s!"expected inequivalent constructor write to be rejected: {reprStr mutRes}"
  -- 2. Allocating, incRef'ing to rc=2, and querying isExclusive must match constant false (and restore true after decRef)
  let mkRcDecl (useConst : Bool) : LNIRDecl := {
    name := "rc_excl_query"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .i1
    body :=
      .letBind 1 .objPtr (.allocCtor 0 [0] [])
        (.incRef 1 1
          ((if useConst then fun k => .letBind 2 .i1 (.scalar (.constBool false)) k
            else fun k => .letBind 2 .i1 (.isExclusive 1) k)
            (.decRef 1 1
              (.letBind 3 .i1 (.isExclusive 1)
                (.decRef 1 1
                  (if useConst then
                     .letBind 4 .i1 (.scalar (.constBool false)) (.ret 4)
                   else
                     .letBind 4 .i1 (.scalar (.binOp .eq (.var 2) (.var 3))) (.ret 4)))))))
  }
  let rcRes := validateTranslationDecl (mkRcDecl false) (mkRcDecl true) 8
  unless rcRes.passed && rcRes.symRetEquiv do
    throw <| IO.userError s!"expected incRef/decRef exclusivity queries to fold to false/true: {reprStr rcRes}"
  -- 3. Scalar seqFor accumulator returned directly vs `acc + 0` must pass symRetEquiv
  let mkLoopDecl (addZero : Bool) : LNIRDecl := {
    name := "loop_acc_alias"
    params := [{ id := 0, name := "init", ty := .i64, borrow := false }]
    retTy := .i64
    body :=
      .letBind 1 .i64 (.scalar (.constU64 0))
        (.letBind 2 .i64 (.scalar (.constU64 4))
          (.seqFor 3 1 2 4 0 .i64
            (.letBind 5 .i64 (.scalar (.binOp .add (.var 4) (.constU64 1))) (.ret 5))
            (if addZero then .letBind 6 .i64 (.scalar (.binOp .add (.var 4) (.constU64 0))) (.ret 6)
             else .ret 4)))
  }
  let loopRes := validateTranslationDecl (mkLoopDecl false) (mkLoopDecl true) 8
  unless loopRes.passed && loopRes.symRetEquiv do
    throw <| IO.userError s!"expected scalar loop accumulator TV equivalence: {reprStr loopRes}"
  -- 4. Guarded `.unreachable` on `x == 999` (outside concrete 1..8 samples) must fail domainEquiv, while shared guarded `.unreachable` refines
  let baseline : LNIRDecl := {
    name := "guarded_unreachable"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .i64
    body := .letBind 1 .i64 (.scalar (.constU64 0)) (.ret 1)
  }
  let corrupt : LNIRDecl := {
    name := "guarded_unreachable"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .i64
    body :=
      .letBind 2 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 999)))
        (.ite 2 .unreachable (.letBind 1 .i64 (.scalar (.constU64 0)) (.ret 1)))
  }
  let corruptSame : LNIRDecl := {
    name := "guarded_unreachable"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .i64
    body :=
      .letBind 2 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 999)))
        (.ite 2 .unreachable (.letBind 1 .i64 (.scalar (.binOp .add (.constU64 0) (.constU64 0))) (.ret 1)))
  }
  let guBad := validateTranslationDecl baseline corrupt 8
  unless !guBad.domainEquiv && !guBad.passed do
    throw <| IO.userError s!"guarded unreachable corruption accepted: {reprStr guBad}"
  let guGood := validateTranslationDecl corrupt corruptSame 8
  unless guGood.domainEquiv && guGood.passed do
    throw <| IO.userError s!"matching guarded unreachable rejected: {reprStr guGood}"
  -- 5. Projecting an allocated child object preserves its heap-root identity for `isExclusive` and `ctor_set`
  let childDecl (project : Bool) : LNIRDecl := {
    name := "projected_child"
    params := []
    retTy := .i1
    body :=
      .letBind 0 .objPtr (.allocCtor 0 [] [])
        (.letBind 1 .objPtr (.allocCtor 0 [0] [])
          (.letBind 2 .objPtr (.ctorGetObj 1 0)
            (.letBind 3 .i1 (.isExclusive (if project then 2 else 0))
              (.decRef 1 1 (.ret 3)))))
  }
  let childRes := validateTranslationDecl (childDecl true) (childDecl false) 8
  unless childRes.passed && childRes.symRetEquiv do
    throw <| IO.userError s!"projected child lost identity: {reprStr childRes}"
  -- 6. Newly allocated child escaping into an input object must compare full reachable child contents in memWritesEquiv
  let mkEscapingChildDecl (corruptField : Bool) : LNIRDecl := {
    name := "escaping_child_write"
    params := [
      { id := 0, name := "p", ty := .objPtr, borrow := false },
      { id := 1, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i64
    body :=
      .letBind 2 .i64 (.call "lean_native_ctor_tag" [0] .i64 false)
        (.letBind 3 .i1 (.scalar (.binOp .eq (.var 2) (.constU64 0)))
          (.ite 3
            (.letBind 4 .i1 (.isExclusive 0)
              (.ite 4
                (.letBind 5 .i64 (if corruptField then
                    .scalar (.select (.binOp .eq (.var 1) (.constU64 999)) (.constU64 3) (.constU64 2))
                  else
                    .scalar (.constU64 2))
                  (.letBind 6 .objPtr (.allocCtor 0 [] [5])
                    (.letBind 7 .i64 (.scalar (.constU64 0))
                      (.letBind 8 .unit (.call "lean_native_ctor_set" [0, 7, 6] .unit false)
                        (.ret 7)))))
                (.letBind 9 .i64 (.scalar (.constU64 0)) (.ret 9))))
            (.letBind 10 .i64 (.scalar (.constU64 0)) (.ret 10))))
  }
  let escBad := validateTranslationDecl (mkEscapingChildDecl false) (mkEscapingChildDecl true) 8
  unless !escBad.memWritesEquiv && !escBad.passed do
    throw <| IO.userError s!"escaping child field corruption accepted: {reprStr escBad}"
  -- 6b. Even without a prior ctor_tag branch, storing an allocated child into an input object must reject corrupted child fields
  let mkDirectEscapingChildDecl (corruptField : Bool) : LNIRDecl := {
    name := "direct_escaping_child_write"
    params := [
      { id := 0, name := "p", ty := .objPtr, borrow := false },
      { id := 1, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i64
    body :=
      .letBind 2 .i1 (.isExclusive 0)
        (.ite 2
          (.letBind 3 .i64 (if corruptField then
              .scalar (.select (.binOp .eq (.var 1) (.constU64 999)) (.constU64 3) (.constU64 2))
            else
              .scalar (.constU64 2))
            (.letBind 4 .objPtr (.allocCtor 0 [] [3])
              (.letBind 5 .i64 (.scalar (.constU64 0))
                (.letBind 6 .unit (.call "lean_native_ctor_set" [0, 5, 4] .unit false)
                  (.ret 5)))))
          (.letBind 7 .i64 (.scalar (.constU64 0)) (.ret 7)))
  }
  let escDirectBad := validateTranslationDecl (mkDirectEscapingChildDecl false) (mkDirectEscapingChildDecl true) 8
  unless !escDirectBad.memWritesEquiv && !escDirectBad.passed do
    throw <| IO.userError s!"direct escaping child field corruption accepted: {reprStr escDirectBad}"
  -- 7. Freeing a parent constructor recursively decrements its child references, restoring child exclusivity
  let mkParentDropDecl (foldTrue : Bool) : LNIRDecl := {
    name := "parent_drop_child_excl"
    params := []
    retTy := .i1
    body :=
      .letBind 0 .objPtr (.allocCtor 0 [] [])
        (.incRef 0 1
          (.letBind 1 .objPtr (.allocCtor 0 [0] [])
            (.decRef 1 1
              (.letBind 2 .i1 (if foldTrue then .scalar (.constBool true) else .isExclusive 0)
                (.decRef 0 1 (.ret 2))))))
  }
  let dropRes := validateTranslationDecl (mkParentDropDecl false) (mkParentDropDecl true) 8
  unless dropRes.passed && dropRes.symRetEquiv do
    throw <| IO.userError s!"parent drop failed to restore child exclusivity: {reprStr dropRes}"
  -- 8. Returned heap graphs must preserve sharing identities (`[a, a]` vs `[a, b]` on `x == 999`) while accepting alpha-equivalent fresh SSA IDs
  let mkSharedReturnSrc (baseId : VarId) : LNIRDecl := {
    name := "shared_return_graph"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .objPtr
    body :=
      .letBind baseId .i64 (.scalar (.constU64 7))
        (.letBind (baseId + 1) .objPtr (.allocCtor 0 [] [baseId])
          (.incRef (baseId + 1) 1
            (.letBind (baseId + 2) .objPtr (.allocCtor 0 [baseId + 1, baseId + 1] [])
              (.ret (baseId + 2)))))
  }
  let mkUnsharedReturnTgt : LNIRDecl := {
    name := "shared_return_graph"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .objPtr
    body :=
      .letBind 1 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 999)))
        (.ite 1
          (.letBind 2 .i64 (.scalar (.constU64 7))
            (.letBind 3 .objPtr (.allocCtor 0 [] [2])
              (.letBind 4 .objPtr (.allocCtor 0 [] [2])
                (.letBind 5 .objPtr (.allocCtor 0 [3, 4] [])
                  (.ret 5)))))
          (.letBind 6 .i64 (.scalar (.constU64 7))
            (.letBind 7 .objPtr (.allocCtor 0 [] [6])
              (.incRef 7 1
                (.letBind 8 .objPtr (.allocCtor 0 [7, 7] [])
                  (.ret 8))))))
  }
  let shareBad := validateTranslationDecl (mkSharedReturnSrc 10) mkUnsharedReturnTgt 8
  unless !shareBad.symRetEquiv && !shareBad.passed do
    throw <| IO.userError s!"returned heap sharing loss accepted: {reprStr shareBad}"
  let shareAlphaOk := validateTranslationDecl (mkSharedReturnSrc 10) (mkSharedReturnSrc 20) 8
  unless shareAlphaOk.symRetEquiv && shareAlphaOk.passed do
    throw <| IO.userError s!"alpha-equivalent returned heap sharing rejected: {reprStr shareAlphaOk}"
  -- 9. Returned top-level root must include its own root identity and terminal RC (rejecting extra incRef on `x == 999`)
  let mkRootRcDecl (extraIncOn999 : Bool) : LNIRDecl := {
    name := "returned_root_rc"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .objPtr
    body :=
      .letBind 1 .i64 (.scalar (.constU64 42))
        (.letBind 2 .objPtr (.allocCtor 0 [] [1])
          (if extraIncOn999 then
             .letBind 3 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 999)))
               (.ite 3 (.incRef 2 1 (.ret 2)) (.ret 2))
           else
             .ret 2))
  }
  let rootRcBad := validateTranslationDecl (mkRootRcDecl false) (mkRootRcDecl true) 8
  unless !rootRcBad.symRetEquiv && !rootRcBad.passed do
    throw <| IO.userError s!"returned root RC corruption accepted: {reprStr rootRcBad}"
  -- 10. Non-escaping leaked allocation or parameter RC mismatch on `x == 999` must fail memWritesEquiv (`rcDeltas`)
  let mkParamRcLeakDecl (leakOn999 : Bool) : LNIRDecl := {
    name := "param_rc_leak"
    params := [{ id := 0, name := "p", ty := .objPtr, borrow := false }, { id := 1, name := "x", ty := .i64, borrow := false }]
    retTy := .i64
    body :=
      if leakOn999 then
        .letBind 2 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
          (.ite 2
            (.incRef 0 1 (.letBind 3 .i64 (.scalar (.constU64 0)) (.ret 3)))
            (.letBind 3 .i64 (.scalar (.constU64 0)) (.ret 3)))
      else
        .letBind 3 .i64 (.scalar (.constU64 0)) (.ret 3)
  }
  let paramRcBad := validateTranslationDecl (mkParamRcLeakDecl false) (mkParamRcLeakDecl true) 8
  unless !paramRcBad.memWritesEquiv && !paramRcBad.passed do
    throw <| IO.userError s!"parameter RC leak accepted: {reprStr paramRcBad}"
  -- 11. Projected input child RC leak (`c := p[0]`, `incRef c` on `x == 999`) must fail memWritesEquiv (`nonAllocRcDeltas`)
  let mkProjChildRcLeakDecl (leakChildOn999 : Bool) : LNIRDecl := {
    name := "proj_child_rc_leak"
    params := [{ id := 0, name := "p", ty := .objPtr, borrow := false }, { id := 1, name := "x", ty := .i64, borrow := false }]
    retTy := .i64
    body :=
      .letBind 2 .i64 (.call "lean_native_ctor_tag" [0] .i64 false)
        (.letBind 3 .i1 (.scalar (.binOp .eq (.var 2) (.constU64 0)))
          (.ite 3
            (.letBind 4 .objPtr (.ctorGetObj 0 0)
              (if leakChildOn999 then
                 .letBind 5 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
                   (.ite 5
                     (.incRef 4 1 (.letBind 6 .i64 (.scalar (.constU64 0)) (.ret 6)))
                     (.letBind 6 .i64 (.scalar (.constU64 0)) (.ret 6)))
               else
                 .letBind 6 .i64 (.scalar (.constU64 0)) (.ret 6)))
            (.letBind 7 .i64 (.scalar (.constU64 0)) (.ret 7))))
  }
  let projChildLeakBad := validateTranslationDecl (mkProjChildRcLeakDecl false) (mkProjChildRcLeakDecl true) 8
  unless !projChildLeakBad.ubRefines && !projChildLeakBad.passed do
    throw <| IO.userError s!"projected input child RC leak accepted: {reprStr projChildLeakBad}"
  -- 12. Sharing between returned root and escaping heap write (`p[0] := a; ret a` vs `p[0] := a; ret b` on `x == 999`) must be preserved
  let mkCrossAliasRetWriteDecl (returnDifferentRootOn999 : Bool) : LNIRDecl := {
    name := "cross_alias_ret_write"
    params := [{ id := 0, name := "p", ty := .objPtr, borrow := false }, { id := 1, name := "x", ty := .i64, borrow := false }]
    retTy := .objPtr
    body :=
      .letBind 2 .i64 (.call "lean_native_ctor_tag" [0] .i64 false)
        (.letBind 3 .i1 (.scalar (.binOp .eq (.var 2) (.constU64 0)))
          (.ite 3
            (.letBind 4 .i1 (.isExclusive 0)
              (.ite 4
                (.letBind 5 .i64 (.scalar (.constU64 7))
                  (.letBind 6 .objPtr (.allocCtor 0 [] [5])
                    (.incRef 6 1
                      (.letBind 7 .objPtr (.allocCtor 0 [] [5])
                        (.incRef 7 1
                          (.letBind 8 .i64 (.scalar (.constU64 0))
                            (.letBind 9 .unit (.call "lean_native_ctor_set" [0, 8, 6] .unit false)
                              (if returnDifferentRootOn999 then
                                 .letBind 10 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
                                   (.ite 10 (.ret 7) (.ret 6))
                               else
                                 .ret 6))))))))
                (.ret 0)))
            (.ret 0)))
  }
  let crossAliasBad := validateTranslationDecl (mkCrossAliasRetWriteDecl false) (mkCrossAliasRetWriteDecl true) 8
  unless !crossAliasBad.memWritesEquiv && !crossAliasBad.passed do
    throw <| IO.userError s!"cross-alias loss between return and write accepted: {reprStr crossAliasBad}"
  -- 13. `decRef p 1; incRef p 1` on an unknown-RC input object (`x == 999`) must fail ubRefines (`ubCond` requires `rc > 1`)
  let mkDecIncUnknownRcDecl (decThenInc : Bool) : LNIRDecl := {
    name := "dec_inc_unknown_rc"
    params := [{ id := 0, name := "p", ty := .objPtr, borrow := false }, { id := 1, name := "x", ty := .i64, borrow := false }]
    retTy := .i64
    body :=
      if decThenInc then
        .letBind 2 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
          (.ite 2
            (.decRef 0 1 (.incRef 0 1 (.letBind 3 .i64 (.scalar (.constU64 0)) (.ret 3))))
            (.letBind 3 .i64 (.scalar (.constU64 0)) (.ret 3)))
      else
        .letBind 3 .i64 (.scalar (.constU64 0)) (.ret 3)
  }
  let decIncBad := validateTranslationDecl (mkDecIncUnknownRcDecl false) (mkDecIncUnknownRcDecl true) 8
  unless !decIncBad.ubRefines && !decIncBad.passed do
    throw <| IO.userError s!"decRef-then-incRef use-after-free on unknown RC accepted: {reprStr decIncBad}"
  -- 13b. Conversely, eliding a redundant `incRef p 1; decRef p 1` pair when `p` is already accessed (`ctor_tag p`) refines (`ubCond` implied)
  let mkIncDecRedundantDecl (withPair : Bool) : LNIRDecl := {
    name := "inc_dec_redundant_live"
    params := [{ id := 0, name := "p", ty := .objPtr, borrow := false }]
    retTy := .i64
    body :=
      .letBind 1 .i64 (.call "lean_native_ctor_tag" [0] .i64 false)
        (if withPair then .incRef 0 1 (.decRef 0 1 (.ret 1)) else .ret 1)
  }
  let incDecGood := validateTranslationDecl (mkIncDecRedundantDecl true) (mkIncDecRedundantDecl false) 8
  unless incDecGood.ubRefines && incDecGood.passed do
    throw <| IO.userError s!"eliding redundant incRef/decRef on live object rejected: {reprStr incDecGood}"
  -- 13c. Adding an unproved `incRef p 1; decRef p 1` on `x == 999` without prior liveness must also fail ubRefines (`p` could have RC == 0 or wrap)
  let mkIncDecDeadBad := validateTranslationDecl (mkDecIncUnknownRcDecl false) {
    name := "inc_dec_unknown_rc"
    params := [{ id := 0, name := "p", ty := .objPtr, borrow := false }, { id := 1, name := "x", ty := .i64, borrow := false }]
    retTy := .i64
    body :=
      .letBind 2 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
        (.ite 2
          (.incRef 0 1 (.decRef 0 1 (.letBind 3 .i64 (.scalar (.constU64 0)) (.ret 3))))
          (.letBind 3 .i64 (.scalar (.constU64 0)) (.ret 3)))
  } 8
  unless !mkIncDecDeadBad.ubRefines && !mkIncDecDeadBad.passed do
    throw <| IO.userError s!"unproved incRef/decRef on potentially dead unknown RC accepted: {reprStr mkIncDecDeadBad}"
  -- 14. Path-conditional UB on one source branch (`unguarded ctor_set p[0]` on `x == 888`) must NOT collapse `sSrc.ubCond`
  --     to `false` on other defined paths (`decRef q 1; incRef q 1` on `x == 999` must still fail `ubRefines`)
  let mkBranchConditionalUbDecl (corruptOtherBranch : Bool) : LNIRDecl := {
    name := "branch_conditional_ub"
    params := [
      { id := 0, name := "p", ty := .objPtr, borrow := false },
      { id := 1, name := "q", ty := .objPtr, borrow := false },
      { id := 2, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i64
    body :=
      .letBind 3 .i1 (.scalar (.binOp .eq (.var 2) (.constU64 888)))
        (.ite 3
          (.letBind 4 .i64 (.scalar (.constU64 0))
            (.letBind 5 .i64 (.scalar (.constU64 42))
              (.letBind 6 .unit (.call "lean_native_ctor_set" [0, 4, 5] .unit false)
                (.ret 4))))
          (if corruptOtherBranch then
             .letBind 7 .i1 (.scalar (.binOp .eq (.var 2) (.constU64 999)))
               (.ite 7
                 (.decRef 1 1 (.incRef 1 1 (.letBind 8 .i64 (.scalar (.constU64 0)) (.ret 8))))
                 (.letBind 8 .i64 (.scalar (.constU64 0)) (.ret 8)))
           else
             .letBind 8 .i64 (.scalar (.constU64 0)) (.ret 8)))
  }
  let branchUbBad := validateTranslationDecl (mkBranchConditionalUbDecl false) (mkBranchConditionalUbDecl true) 8
  unless !branchUbBad.ubRefines && !branchUbBad.passed do
    throw <| IO.userError s!"branch-conditional UB masked target UB on defined path: {reprStr branchUbBad}"
  -- 15. Possible aliasing between projected input children (`a := p[0]`, `b := p[1]`):
  --     `before := isExclusive b; decRef a 1; after := isExclusive b` must NOT treat `before` and `after` as equivalent!
  let mkProjSiblingAliasDecl (returnAfter : Bool) : LNIRDecl := {
    name := "proj_sibling_alias_excl"
    params := [
      { id := 0, name := "p", ty := .objPtr, borrow := false },
      { id := 1, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i1
    body :=
      .letBind 2 .i64 (.call "lean_native_ctor_tag" [0] .i64 false)
        (.letBind 3 .i1 (.scalar (.binOp .eq (.var 2) (.constU64 0)))
          (.ite 3
            (.letBind 4 .objPtr (.ctorGetObj 0 0)
              (.letBind 5 .objPtr (.ctorGetObj 0 1)
                (.letBind 6 .i1 (.isExclusive 5)
                  (.decRef 4 1
                    (.letBind 7 .i1 (.isExclusive 5)
                      (if returnAfter then
                         .letBind 8 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
                           (.ite 8 (.ret 7) (.ret 6))
                       else
                         .ret 6))))))
            (.letBind 9 .i1 (.scalar (.constBool false)) (.ret 9))))
  }
  let sibAliasBad := validateTranslationDecl (mkProjSiblingAliasDecl false) (mkProjSiblingAliasDecl true) 64
  unless !sibAliasBad.ubRefines && !sibAliasBad.passed do
    throw <| IO.userError s!"projected sibling child may-alias exclusivity drift accepted: {reprStr sibAliasBad}"
  -- 15a2. Also test `incRef a 1; decRef a 1` (supported non-freeing path) invalidating sibling `isExclusive b`:
  let mkProjSiblingIncAliasDecl (returnDuringInc : Bool) : LNIRDecl := {
    name := "proj_sibling_inc_alias_excl"
    params := [
      { id := 0, name := "p", ty := .objPtr, borrow := false },
      { id := 1, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i1
    body :=
      .letBind 2 .i64 (.call "lean_native_ctor_tag" [0] .i64 false)
        (.letBind 3 .i1 (.scalar (.binOp .eq (.var 2) (.constU64 0)))
          (.ite 3
            (.letBind 4 .objPtr (.ctorGetObj 0 0)
              (.letBind 5 .objPtr (.ctorGetObj 0 1)
                (.letBind 6 .i1 (.isExclusive 5)
                  (.incRef 4 1
                    (.letBind 7 .i1 (.isExclusive 5)
                      (.decRef 4 1
                        (if returnDuringInc then
                           .letBind 8 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
                             (.ite 8 (.ret 7) (.ret 6))
                         else
                           .ret 6)))))))
            (.letBind 9 .i1 (.scalar (.constBool false)) (.ret 9))))
  }
  let sibIncAliasBad := validateTranslationDecl (mkProjSiblingIncAliasDecl false) (mkProjSiblingIncAliasDecl true) 64
  unless !sibIncAliasBad.ubRefines && !sibIncAliasBad.passed do
    throw <| IO.userError s!"projected sibling child incRef may-alias exclusivity drift accepted: {reprStr sibIncAliasBad}"
  -- 15b. Even when `p` and `q` are distinct input parameters (`p` and `q` may alias the same heap object),
  --      `incRef p 1; decRef p 1` must NOT allow folding `isExclusive q` across `incRef p 1` (`incRef p 1; x := isExclusive q; decRef p 1; ret x` vs `x := isExclusive q; incRef p 1; decRef p 1; ret x`)
  let mkParamAliasExclDecl (queryDuringInc : Bool) : LNIRDecl := {
    name := "param_alias_excl"
    params := [
      { id := 0, name := "p", ty := .objPtr, borrow := false },
      { id := 1, name := "q", ty := .objPtr, borrow := false }
    ]
    retTy := .i1
    body :=
      if queryDuringInc then
        .incRef 0 1
          (.letBind 2 .i1 (.isExclusive 1)
            (.decRef 0 1 (.ret 2)))
      else
        .letBind 2 .i1 (.isExclusive 1)
          (.incRef 0 1
            (.decRef 0 1 (.ret 2)))
  }
  let paramAliasExclBad := validateTranslationDecl (mkParamAliasExclDecl true) (mkParamAliasExclDecl false) 64
  unless !paramAliasExclBad.passed do
    throw <| IO.userError s!"cross-parameter may-alias exclusivity reordering accepted: {reprStr paramAliasExclBad}"
  -- 16. Moving `lean_native_ctor_tag q` past `decRef p 1` inside an `isExclusive p` branch must fail `ubRefines`
  --     (borrowed `q` may alias RC-1 `p`, so `q` may be freed by `decRef p 1`)
  let mkPostFreeAliasReadDecl (readAfterFree : Bool) : LNIRDecl := {
    name := "post_free_alias_read"
    params := [
      { id := 0, name := "p", ty := .objPtr, borrow := false },
      { id := 1, name := "q", ty := .objPtr, borrow := true }
    ]
    retTy := .i64
    body :=
      .letBind 2 .i1 (.isExclusive 0)
        (.ite 2
          (if readAfterFree then
             .decRef 0 1
               (.letBind 3 .i64 (.call "lean_native_ctor_tag" [1] .i64 false)
                 (.ret 3))
           else
             .letBind 3 .i64 (.call "lean_native_ctor_tag" [1] .i64 false)
               (.decRef 0 1 (.ret 3)))
          (.letBind 4 .i64 (.scalar (.constU64 0)) (.ret 4)))
  }
  let postFreeBad := validateTranslationDecl (mkPostFreeAliasReadDecl false) (mkPostFreeAliasReadDecl true) 64
  unless !postFreeBad.ubRefines && !postFreeBad.passed do
    throw <| IO.userError s!"post-free may-alias read accepted: {reprStr postFreeBad}"
  -- 17. Epoch-generated projected field roots (`400000 + epoch * 100000 + ...` = `500016` for param 1 field 0 at epoch 1)
  --     must never collide with `.allocTag` or parameter ID 16!
  let mkEpochFieldVsParam16Decl (returnParam16On999 : Bool) : LNIRDecl := {
    name := "epoch_field_vs_param16"
    params :=
      ((List.range 17).map fun i => { id := i, name := s!"p{i}", ty := .objPtr, borrow := false }) ++
      [{ id := 17, name := "x", ty := .i64, borrow := false }]
    retTy := .objPtr
    body :=
      .incRef 0 1
        (.letBind 20 .i64 (.call "lean_native_ctor_tag" [1] .i64 false)
          (.letBind 21 .i1 (.scalar (.binOp .eq (.var 20) (.constU64 0)))
            (.ite 21
              (.letBind 22 .objPtr (.ctorGetObj 1 0)
                (if returnParam16On999 then
                   .letBind 23 .i1 (.scalar (.binOp .eq (.var 17) (.constU64 999)))
                     (.ite 23 (.ret 16) (.ret 22))
                 else
                   .ret 22))
              (.ret 16))))
  }
  let epochCollBad := validateTranslationDecl (mkEpochFieldVsParam16Decl false) (mkEpochFieldVsParam16Decl true) 8
  unless !epochCollBad.symRetEquiv && !epochCollBad.passed do
    throw <| IO.userError s!"epoch-projected field root collided with param 16: {reprStr epochCollBad}"
  -- 18. Mutating `q[0]` after caching `p[0]` (`p` and borrowed `q` may alias) must invalidate cached `.tuple` fields on `p`
  let mkCrossParamWriteStaleReadDecl (rereadAfterWrite : Bool) : LNIRDecl := {
    name := "cross_param_write_stale_read"
    params := [
      { id := 0, name := "p", ty := .objPtr, borrow := false },
      { id := 1, name := "q", ty := .objPtr, borrow := true },
      { id := 2, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i64
    body :=
      .letBind 3 .i1 (.isExclusive 0)
        (.ite 3
          (.letBind 4 .i1 (.isExclusive 1)
            (.ite 4
              (.letBind 5 .i64 (.scalar (.constU64 0))
                (.letBind 6 .i64 (.scalar (.constU64 2))
                  (.letBind 7 .unit (.call "lean_native_ctor_set" [0, 5, 6] .unit false)
                    (.letBind 8 .i64 (.ctorGetScalar 0 0 .i64)
                      (.letBind 9 .i64 (.scalar (.constU64 3))
                        (.letBind 10 .i1 (.isExclusive 1)
                          (.ite 10
                            (.letBind 11 .unit (.call "lean_native_ctor_set" [1, 5, 9] .unit false)
                              (.letBind 12 .i1 (.isExclusive 0)
                                (.ite 12
                                  (if rereadAfterWrite then
                                     .letBind 13 .i1 (.scalar (.binOp .eq (.var 2) (.constU64 999)))
                                       (.ite 13
                                         (.letBind 14 .i64 (.ctorGetScalar 0 0 .i64) (.ret 14))
                                         (.ret 8))
                                   else
                                     .ret 8)
                                  (.ret 5))))
                            (.ret 5))))))))
              (.letBind 15 .i64 (.scalar (.constU64 0)) (.ret 15))))
          (.letBind 16 .i64 (.scalar (.constU64 0)) (.ret 16)))
  }
  let staleReadBad := validateTranslationDecl (mkCrossParamWriteStaleReadDecl false) (mkCrossParamWriteStaleReadDecl true) 8
  unless !staleReadBad.symRetEquiv && !staleReadBad.passed do
    throw <| IO.userError s!"cached input constructor fields survived may-alias write: {reprStr staleReadBad}"
  -- 19. Nullary immediate constructor (`.scalar (.constU64 1)`) must fold `isExclusive` to `true` without heap-liveness requirement
  let mkImmediateExclDecl (foldTrue : Bool) : LNIRDecl := {
    name := "immediate_ctor_is_excl"
    params := []
    retTy := .i1
    body :=
      .letBind 0 .taggedPtr (.scalar (.constU64 1))
        (.letBind 1 .i1 (if foldTrue then .scalar (.constBool true) else .isExclusive 0)
          (.ret 1))
  }
  let immExclRes := validateTranslationDecl (mkImmediateExclDecl false) (mkImmediateExclDecl true) 8
  unless immExclRes.symRetEquiv && immExclRes.ubRefines && immExclRes.passed do
    throw <| IO.userError s!"immediate constructor isExclusive failed to fold to true: {reprStr immExclRes}"
  -- 20. Stale `b := isExclusive p` saved across `incRef p 1` must NOT mark `p` exclusive when branching on `b`
  let mkStaleExclBranchDecl (foldTrue : Bool) : LNIRDecl := {
    name := "stale_excl_branch"
    params := [
      { id := 0, name := "p", ty := .objPtr, borrow := false },
      { id := 1, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i1
    body :=
      .letBind 2 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
        (.ite 2
          (.letBind 3 .i1 (.isExclusive 0)
            (.incRef 0 1
              (.ite 3
                (if foldTrue then
                   .letBind 4 .i1 (.scalar (.constBool true)) (.ret 4)
                 else
                   .letBind 4 .i1 (.isExclusive 0) (.ret 4))
                (.letBind 5 .i1 (.scalar (.constBool false)) (.ret 5)))))
          (.letBind 6 .i1 (.scalar (.constBool false)) (.ret 6)))
  }
  let staleExclBad := validateTranslationDecl (mkStaleExclBranchDecl false) (mkStaleExclBranchDecl true) 8
  unless !staleExclBad.symRetEquiv && !staleExclBad.passed do
    throw <| IO.userError s!"stale isExclusive predicate marked incremented root exclusive: {reprStr staleExclBad}"
  -- 21. Pointer-valued `ScalarExpr.select` (`r := select true a a` and symbolic `r := select (x == 500) a b`)
  --     must preserve heap-root alias identity across subsequent `ctor_set` writes!
  let mkSelectAliasDecl (constOneTarget : Bool) : LNIRDecl := {
    name := "select_alias_write"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .i64
    body :=
      .letBind 1 .i64 (.scalar (.constU64 1))
        (.letBind 2 .objPtr (.allocCtor 0 [] [1])
          (.letBind 3 .objPtr (.scalar (.select (.constBool true) (.var 2) (.var 2)))
            (.letBind 4 .i64 (.scalar (.constU64 0))
              (.letBind 5 .i64 (.scalar (.select (.binOp .eq (.var 0) (.constU64 999)) (.constU64 2) (.constU64 1)))
                (.letBind 6 .unit (.call "lean_native_ctor_set" [2, 4, 5] .unit false)
                  (if constOneTarget then
                     .decRef 2 1 (.ret 1)
                   else
                     .letBind 7 .i64 (.ctorGetScalar 3 0 .i64)
                       (.decRef 2 1 (.ret 7))))))))
  }
  let selAliasBad := validateTranslationDecl (mkSelectAliasDecl false) (mkSelectAliasDecl true) 8
  unless !selAliasBad.symRetEquiv && !selAliasBad.passed do
    throw <| IO.userError s!"select pointer alias lost subsequent ctor_set write: {reprStr selAliasBad}"
  let mkSymSelectAliasDecl (constOneTarget : Bool) : LNIRDecl := {
    name := "sym_select_alias_write"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .i64
    body :=
      .letBind 1 .i64 (.scalar (.constU64 1))
        (.letBind 2 .objPtr (.allocCtor 0 [] [1])
          (.letBind 3 .objPtr (.allocCtor 0 [] [1])
            (.letBind 4 .objPtr (.scalar (.select (.binOp .eq (.var 0) (.constU64 999)) (.var 2) (.var 3)))
              (.letBind 5 .i64 (.scalar (.constU64 0))
                (.letBind 6 .i64 (.scalar (.constU64 2))
                  (.letBind 7 .unit (.call "lean_native_ctor_set" [2, 5, 6] .unit false)
                    (if constOneTarget then
                       .decRef 2 1 (.decRef 3 1 (.ret 1))
                     else
                       .letBind 8 .i64 (.ctorGetScalar 4 0 .i64)
                         (.decRef 2 1 (.decRef 3 1 (.ret 8))))))))))
  }
  let symSelAliasBad := validateTranslationDecl (mkSymSelectAliasDecl false) (mkSymSelectAliasDecl true) 8
  unless !symSelAliasBad.symRetEquiv && !symSelAliasBad.passed do
    throw <| IO.userError s!"symbolic select pointer alias lost subsequent ctor_set write: {reprStr symSelAliasBad}"
  -- 22. `mkTuple` / `projTuple` containing heap pointers must preserve heap-root alias identity across `ctor_set` writes
  let mkTuplePtrAliasDecl (constOneTarget : Bool) : LNIRDecl := {
    name := "tuple_ptr_alias_write"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .i64
    body :=
      .letBind 1 .i64 (.scalar (.constU64 1))
        (.letBind 2 .objPtr (.allocCtor 0 [] [1])
          (.letBind 3 (.tuple [.objPtr]) (.mkTuple [2])
            (.letBind 4 .objPtr (.projTuple 3 0)
              (.letBind 5 .i64 (.scalar (.constU64 0))
                (.letBind 6 .i64 (.scalar (.select (.binOp .eq (.var 0) (.constU64 999)) (.constU64 2) (.constU64 1)))
                  (.letBind 7 .unit (.call "lean_native_ctor_set" [2, 5, 6] .unit false)
                    (if constOneTarget then
                       .decRef 2 1 (.ret 1)
                     else
                       .letBind 8 .i64 (.ctorGetScalar 4 0 .i64)
                         (.decRef 2 1 (.ret 8)))))))))
  }
  let tupAliasBad := validateTranslationDecl (mkTuplePtrAliasDecl false) (mkTuplePtrAliasDecl true) 8
  unless !tupAliasBad.symRetEquiv && !tupAliasBad.passed do
    throw <| IO.userError s!"mkTuple/projTuple pointer alias lost subsequent ctor_set write: {reprStr tupAliasBad}"
  -- 22b. Conditional `.ite` producing `mkTuple [a]` vs `mkTuple [b]` followed by `projTuple` also preserves branch heap-root aliases
  let mkIteTuplePtrAliasDecl (constOneTarget : Bool) : LNIRDecl := {
    name := "ite_tuple_ptr_alias_write"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .i64
    body :=
      .letBind 1 .i64 (.scalar (.constU64 1))
        (.letBind 2 .objPtr (.allocCtor 0 [] [1])
          (.letBind 3 .objPtr (.allocCtor 0 [] [1])
            (.letBind 4 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 999)))
              (.letBind 5 (.tuple [.objPtr]) (.mkTuple [2])
                (.letBind 6 (.tuple [.objPtr]) (.mkTuple [3])
                  (.letBind 7 .i64 (.scalar (.constU64 0))
                    (.letBind 8 .i64 (.scalar (.constU64 2))
                      (.letBind 9 .unit (.call "lean_native_ctor_set" [2, 7, 8] .unit false)
                        (.ite 4
                          (.letBind 10 .objPtr (.projTuple 5 0)
                            (if constOneTarget then
                               .decRef 2 1 (.decRef 3 1 (.ret 1))
                             else
                               .letBind 11 .i64 (.ctorGetScalar 10 0 .i64)
                                 (.decRef 2 1 (.decRef 3 1 (.ret 11)))))
                          (.decRef 2 1 (.decRef 3 1 (.ret 1))))))))))))
  }
  let iteTupAliasBad := validateTranslationDecl (mkIteTuplePtrAliasDecl false) (mkIteTuplePtrAliasDecl true) 8
  unless !iteTupAliasBad.symRetEquiv && !iteTupAliasBad.passed do
    throw <| IO.userError s!"ite mkTuple/projTuple pointer alias lost subsequent ctor_set write: {reprStr iteTupAliasBad}"
  -- 23. Unproved `ctorGetObj p 8` (and even `ctorGetObj p 1` when source only projected `p[0]`) on `x == 999`
  --     must fail `ubRefines` (`SymExpr.ctorLen` bounds predicate)
  let mkInputOobProjDecl (oobIdx : Option Nat) : LNIRDecl := {
    name := "input_ctor_oob_proj"
    params := [
      { id := 0, name := "p", ty := .objPtr, borrow := false },
      { id := 1, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i64
    body :=
      .letBind 2 .i64 (.call "lean_native_ctor_tag" [0] .i64 false)
        (.letBind 3 .objPtr (.ctorGetObj 0 0)
          (match oobIdx with
           | some idx =>
             .letBind 4 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
               (.ite 4
                 (.letBind 5 .objPtr (.ctorGetObj 0 idx)
                   (.letBind 6 .i64 (.scalar (.constU64 0)) (.ret 6)))
                 (.letBind 6 .i64 (.scalar (.constU64 0)) (.ret 6)))
           | none =>
             .letBind 6 .i64 (.scalar (.constU64 0)) (.ret 6)))
  }
  let oob8Bad := validateTranslationDecl (mkInputOobProjDecl none) (mkInputOobProjDecl (some 8)) 8
  unless !oob8Bad.ubRefines && !oob8Bad.passed do
    throw <| IO.userError s!"out-of-bounds ctorGetObj p 8 accepted: {reprStr oob8Bad}"
  let oob1Bad := validateTranslationDecl (mkInputOobProjDecl none) (mkInputOobProjDecl (some 1)) 8
  unless !oob1Bad.ubRefines && !oob1Bad.passed do
    throw <| IO.userError s!"unproved ctorGetObj p 1 beyond source p[0] accepted: {reprStr oob1Bad}"
  let inb0Good := validateTranslationDecl (mkInputOobProjDecl (some 0)) (mkInputOobProjDecl none) 8
  unless inb0Good.ubRefines && inb0Good.passed do
    throw <| IO.userError s!"eliding redundant in-bounds ctorGetObj p 0 rejected: {reprStr inb0Good}"
  -- 24. Scalar parameter IDs (e.g. `100000`, `24000`, `30000`, `9000`, `90000`) must never collide with
  --     `SymExpr.rcSym`, `SymExpr.ctorTag`, `SymExpr.sarrayLen`, synthetic projected fields, or `jointHeap`!
  let mkHighVarIdNoRcSpoofDecl (foldTrue : Bool) : LNIRDecl := {
    name := "high_var_id_no_rc_spoof"
    params := [
      { id := 0, name := "p", ty := .objPtr, borrow := false },
      { id := 100000, name := "a", ty := .i64, borrow := false },
      { id := 1, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i1
    body :=
      .letBind 2 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
        (.ite 2
          (.letBind 3 .i1 (.scalar (.binOp .eq (.var 100000) (.constU64 1)))
            (.ite 3
              (if foldTrue then
                 .letBind 4 .i1 (.scalar (.constBool true)) (.ret 4)
               else
                 .letBind 4 .i1 (.isExclusive 0) (.ret 4))
              (.letBind 5 .i1 (.scalar (.constBool true)) (.ret 5))))
          (.letBind 6 .i1 (.scalar (.constBool true)) (.ret 6)))
  }
  let rcSpoofBad := validateTranslationDecl (mkHighVarIdNoRcSpoofDecl false) (mkHighVarIdNoRcSpoofDecl true) 8
  unless !rcSpoofBad.symRetEquiv && !rcSpoofBad.passed do
    throw <| IO.userError s!"ordinary parameter ID 100000 spoofed SymExpr.rcSym exclusivity: {reprStr rcSpoofBad}"
  -- 25. Nested projected field `p1[0][0]` at epoch 0 must NOT collide with `p0[0]` at epoch 1 (`cantorPairNat` bijection)
  let mkNestedVsEpochProjDecl (retSecond : Bool) : LNIRDecl := {
    name := "nested_vs_epoch_proj"
    params := [
      { id := 0, name := "p0", ty := .objPtr, borrow := false },
      { id := 1, name := "p1", ty := .objPtr, borrow := false },
      { id := 2, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i1
    body :=
      .letBind 3 .i1 (.scalar (.binOp .eq (.var 2) (.constU64 999)))
        (.ite 3
          (.letBind 4 .objPtr (.ctorGetObj 1 0)
            (.letBind 5 .objPtr (.ctorGetObj 4 0)
              (.incRef 1 1
                (.letBind 6 .objPtr (.ctorGetObj 0 0)
                  (.letBind 7 .i1 (.isExclusive 5)
                    (.letBind 8 .i1 (.isExclusive 6)
                      (if retSecond then .ret 8 else .ret 7)))))))
          (.letBind 9 .i1 (.scalar (.constBool true)) (.ret 9)))
  }
  let nestedCollBad := validateTranslationDecl (mkNestedVsEpochProjDecl false) (mkNestedVsEpochProjDecl true) 8
  unless !nestedCollBad.ubRefines && !nestedCollBad.passed do
    throw <| IO.userError s!"nested p1[0][0] at epoch 0 collided with p0[0] at epoch 1: {reprStr nestedCollBad}"
  -- 26. `allocCtor` containing a tag-refined external root `p` (whose RC is still unknown) must preserve `.symVar p`
  --     reference identity rather than copying `p`'s cached `.tuple` fields!
  let mkExtRootInAllocCtorDecl (returnOldSnapshot : Bool) : LNIRDecl := {
    name := "ext_root_in_alloc_ctor"
    params := [
      { id := 0, name := "p", ty := .objPtr, borrow := false },
      { id := 1, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i64
    body :=
      .letBind 2 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
        (.ite 2
          (.letBind 3 .i64 (.call "lean_native_ctor_tag" [0] .i64 false)
            (.letBind 4 .i1 (.scalar (.binOp .eq (.var 3) (.constU64 0)))
              (.ite 4
                (.letBind 5 .objPtr (.allocCtor 0 [0] [])
                  (.letBind 6 .i1 (.isExclusive 0)
                    (.ite 6
                      (.letBind 7 .i64 (.ctorGetScalar 0 0 .i64)
                        (.letBind 8 .i64 (.scalar (.constU64 0))
                          (.letBind 9 .i64 (.scalar (.binOp .add (.var 7) (.constU64 1)))
                            (.letBind 10 .unit (.call "lean_native_ctor_set" [0, 8, 9] .unit false)
                              (.letBind 11 .objPtr (.ctorGetObj 5 0)
                                (.letBind 12 .i64 (.ctorGetScalar 11 0 .i64)
                                  (.incRef 0 1
                                    (.decRef 5 1
                                      (if returnOldSnapshot then .ret 7 else .ret 12)))))))))
                      (.incRef 0 1 (.decRef 5 1 (.letBind 13 .i64 (.scalar (.constU64 0)) (.ret 13)))))))
                (.letBind 14 .i64 (.scalar (.constU64 0)) (.ret 14)))))
          (.letBind 15 .i64 (.scalar (.constU64 0)) (.ret 15)))
  }
  let extInAllocBad := validateTranslationDecl (mkExtRootInAllocCtorDecl false) (mkExtRootInAllocCtorDecl true) 8
  unless !extInAllocBad.ubRefines && !extInAllocBad.passed do
    throw <| IO.userError s!"allocCtor copied cached external root fields instead of preserving root identity: {reprStr extInAllocBad}"
  -- 27. Arithmetic on a scalar field projected from an input heap object (`p[0][0] + 1`, via `.ctorGetObj` with `.i64`
  --     or `.ctorGetScalar`) must fail closed (`symUnsupported`) on non-identity rewrites because the uncached field's
  --     runtime sort in `HeapState` could be `.objPtr` or `.u64`, while reflexive (`src == tgt`) still passes!
  let mkNestedScalarProjArithDecl (retConstVal : UInt64) : LNIRDecl := {
    name := "nested_scalar_proj_arith"
    params := [
      { id := 0, name := "p", ty := .objPtr, borrow := false },
      { id := 1, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i64
    body :=
      .letBind 2 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
        (.ite 2
          (.letBind 3 .objPtr (.ctorGetObj 0 0)
            (.letBind 4 .i64 (.ctorGetObj 3 0)
              (.letBind 5 .i64 (.scalar (.binOp .add (.var 4) (.constU64 1)))
                (.letBind 6 .i64 (.scalar (.constU64 retConstVal))
                  (.ret 6)))))
          (.letBind 7 .i64 (.scalar (.constU64 0)) (.ret 7)))
  }
  let nestedScalarArithBad := validateTranslationDecl (mkNestedScalarProjArithDecl 0) (mkNestedScalarProjArithDecl 1) 8
  unless !nestedScalarArithBad.ubRefines && !nestedScalarArithBad.passed do
    throw <| IO.userError s!"uncached scalar projection arithmetic accepted non-identity target: {reprStr nestedScalarArithBad}"
  let nestedScalarArithGood := validateTranslationDecl (mkNestedScalarProjArithDecl 0) (mkNestedScalarProjArithDecl 0) 8
  unless nestedScalarArithGood.passed do
    throw <| IO.userError s!"equivalent scalar projection arithmetic rejected: {reprStr nestedScalarArithGood}"
  -- 27b. Also test `.taggedPtr` intermediate projection (`let 4 : taggedPtr := ctorGetObj 3 0; let 9 : i64 := var 4; let 10 := 9 + 1`),
  --      ensuring non-identity rewrites fail closed (`symUnsupported`) when runtime sort of `p[0][0]` is unknown!
  let mkTaggedScalarProjArithDecl (retConstVal : UInt64) : LNIRDecl := {
    name := "tagged_scalar_proj_arith"
    params := [
      { id := 0, name := "p", ty := .objPtr, borrow := false },
      { id := 1, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i64
    body :=
      .letBind 2 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
        (.ite 2
          (.letBind 3 .objPtr (.ctorGetObj 0 0)
            (.letBind 4 .taggedPtr (.ctorGetObj 3 0)
              (.letBind 8 .i64 (.scalar (.var 4))
                (.letBind 5 .i64 (.scalar (.binOp .add (.var 8) (.constU64 1)))
                  (.letBind 6 .i64 (.scalar (.constU64 retConstVal))
                    (.ret 6))))))
          (.letBind 7 .i64 (.scalar (.constU64 0)) (.ret 7)))
  }
  let taggedScalarBad := validateTranslationDecl (mkTaggedScalarProjArithDecl 0) (mkTaggedScalarProjArithDecl 1) 8
  unless !taggedScalarBad.ubRefines && !taggedScalarBad.passed do
    throw <| IO.userError s!"taggedPtr uncached projection arithmetic accepted non-identity target: {reprStr taggedScalarBad}"
  -- 28. Unsupported symbolic execution in `src` (e.g. pointer arithmetic `p + 1` or unknown extern call) must
  --     fail closed (`symUnsupported == true` -> `passed == false`), never vacuously accepting `tgt`!
  let mkUnsupportedSrcDecl (retVal : UInt64) : LNIRDecl := {
    name := "unsupported_src_fail_closed"
    params := [
      { id := 0, name := "p", ty := .objPtr, borrow := false },
      { id := 1, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i64
    body :=
      .letBind 2 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
        (.ite 2
          (.letBind 3 .i64 (.call "lean_native_unknown_extern" [0] .i64 true)
            (.letBind 4 .i64 (.scalar (.constU64 retVal)) (.ret 4)))
          (.letBind 5 .i64 (.scalar (.constU64 0)) (.ret 5)))
  }
  let unsuppBad := validateTranslationDecl (mkUnsupportedSrcDecl 0) (mkUnsupportedSrcDecl 1) 8
  unless !unsuppBad.ubRefines && !unsuppBad.passed do
    throw <| IO.userError s!"unsupported symbolic execution in source vacuously accepted target: {reprStr unsuppBad}"
  -- 29. `lean_native_ctor_set` without a statically proven exclusive root must keep the exclusivity requirement in
  --     `ubCond` WITHOUT poisoning the cached root binding's `noUB`, so a later `lean_native_ctor_tag` read still
  --     compares symbolically on the defined exclusive path (`x == 999`)!
  let mkUnprovenExclStoreDecl (retConstVal : UInt64) : LNIRDecl := {
    name := "unproven_excl_store"
    params := [
      { id := 0, name := "p", ty := .objPtr, borrow := false },
      { id := 1, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i64
    body :=
      .letBind 2 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
        (.ite 2
          (.letBind 3 .objPtr (.ctorGetObj 0 0)
            (.letBind 8 .i64 (.scalar (.constU64 0))
              (.letBind 4 .unit (.call "lean_native_ctor_set" [0, 8, 3] .unit false)
                (.letBind 5 .i64 (.call "lean_native_ctor_tag" [0] .i64 false)
                  (.letBind 6 .i64 (.scalar (.constU64 retConstVal))
                    (.ret 6))))))
          (.letBind 7 .i64 (.scalar (.constU64 0)) (.ret 7)))
  }
  let unprovenExclBad := validateTranslationDecl (mkUnprovenExclStoreDecl 0) (mkUnprovenExclStoreDecl 1) 8
  unless !unprovenExclBad.symRetEquiv && !unprovenExclBad.passed do
    throw <| IO.userError s!"unproven-exclusive ctor_set poisoned cached root noUB and masked return difference: {reprStr unprovenExclBad}"
  let unprovenExclGood := validateTranslationDecl (mkUnprovenExclStoreDecl 0) (mkUnprovenExclStoreDecl 0) 8
  unless unprovenExclGood.passed do
    throw <| IO.userError s!"equivalent unproven-exclusive ctor_set rejected: {reprStr unprovenExclGood}"
  -- 30. Boolean `.i1` parameter `b == true` must preserve sort `some true` (never manufacturing source UB),
  --     and untyped `.taggedPtr` comparison `obj == true` must mark `symUnsupported` (failing closed)!
  let mkBoolParamEqDecl (retAt999 : UInt64) : LNIRDecl := {
    name := "bool_param_eq"
    params := [
      { id := 0, name := "b", ty := .i1, borrow := false },
      { id := 1, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i64
    body :=
      .letBind 2 .i1 (.scalar (.binOp .eq (.var 0) (.constBool true)))
        (.letBind 3 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
          (.ite 3
            (.letBind 4 .i64 (.scalar (.constU64 retAt999)) (.ret 4))
            (.letBind 5 .i64 (.scalar (.constU64 0)) (.ret 5))))
  }
  let boolParamBad := validateTranslationDecl (mkBoolParamEqDecl 0) (mkBoolParamEqDecl 1) 8
  unless !boolParamBad.symRetEquiv && !boolParamBad.passed do
    throw <| IO.userError s!"i1 parameter equality `b == true` erroneously collapsed ubCond: {reprStr boolParamBad}"
  let boolParamGood := validateTranslationDecl (mkBoolParamEqDecl 0) (mkBoolParamEqDecl 0) 8
  unless boolParamGood.passed do
    throw <| IO.userError s!"equivalent i1 parameter equality `b == true` rejected: {reprStr boolParamGood}"
  -- 30b. Untyped `.taggedPtr` comparison `obj == true` must mark `symUnsupported` and fail closed on any non-identity rewrite
  let mkUntypedBoolCmpDecl (retVal : Bool) : LNIRDecl := {
    name := "untyped_bool_cmp"
    params := [{ id := 0, name := "obj", ty := .taggedPtr, borrow := false }]
    retTy := .i1
    body :=
      .letBind 1 .i1 (.scalar (.binOp .eq (.var 0) (.constBool true)))
        (.letBind 2 .i1 (.scalar (.constBool retVal)) (.ret 2))
  }
  let untypedBoolRes := validateTranslationDecl (mkUntypedBoolCmpDecl false) (mkUntypedBoolCmpDecl true) 8
  unless !untypedBoolRes.ubRefines && !untypedBoolRes.passed do
    throw <| IO.userError s!"untyped taggedPtr boolean comparison accepted without symUnsupported: {reprStr untypedBoolRes}"
  -- 30c. `.tuple [.i1, .i64]` parameter projection `p.0 == true` must also preserve `.i1` sort and concrete `.bool` sampling
  let mkTupleBoolParamDecl (retAt999 : UInt64) : LNIRDecl := {
    name := "tuple_bool_param"
    params := [
      { id := 0, name := "pair", ty := .tuple [.i1, .i64], borrow := false },
      { id := 1, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i64
    body :=
      .letBind 2 .i1 (.projTuple 0 0)
        (.letBind 3 .i1 (.scalar (.binOp .eq (.var 2) (.constBool true)))
          (.letBind 4 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
            (.ite 4
              (.letBind 5 .i64 (.scalar (.constU64 retAt999)) (.ret 5))
              (.letBind 6 .i64 (.scalar (.constU64 0)) (.ret 6)))))
  }
  let tupleBoolBad := validateTranslationDecl (mkTupleBoolParamDecl 0) (mkTupleBoolParamDecl 1) 8
  unless !tupleBoolBad.symRetEquiv && !tupleBoolBad.passed do
    throw <| IO.userError s!"tuple .i1 projection `pair.0 == true` collapsed ubCond: {reprStr tupleBoolBad}"
  let tupleBoolGood := validateTranslationDecl (mkTupleBoolParamDecl 0) (mkTupleBoolParamDecl 0) 8
  unless tupleBoolGood.passed do
    throw <| IO.userError s!"equivalent tuple .i1 projection `pair.0 == true` rejected: {reprStr tupleBoolGood}"
  -- 31. Copying an unboxed tuple via `.scalar (.var a)` must propagate `typedTuples` provenance so nesting `b`
  --     inside `mkTuple [b]` preserves its field expressions rather than collapsing to an opaque `.symVar`!
  let mkCopiedTypedTupleDecl (srcMode : Bool) : LNIRDecl := {
    name := "copied_typed_tuple"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .tuple [.tuple [.i64]]
    body :=
      .letBind 1 .i64
        (if srcMode then
          .scalar (.select (.binOp .eq (.var 0) (.constU64 999)) (.constU64 2) (.constU64 1))
        else
          .scalar (.constU64 1))
        (.letBind 2 (.tuple [.i64]) (.mkTuple [1])
          (.letBind 3 (.tuple [.i64]) (.scalar (.var 2))
            (.letBind 4 (.tuple [.tuple [.i64]]) (.mkTuple [3])
              (.ret 4))))
  }
  let copiedTupleBad := validateTranslationDecl (mkCopiedTypedTupleDecl true) (mkCopiedTypedTupleDecl false) 8
  unless !copiedTupleBad.symRetEquiv && !copiedTupleBad.passed do
    throw <| IO.userError s!"scalar copy of typed tuple lost provenance in nested mkTuple: {reprStr copiedTupleBad}"
  let copiedTupleGood := validateTranslationDecl (mkCopiedTypedTupleDecl true) (mkCopiedTypedTupleDecl true) 8
  unless copiedTupleGood.passed do
    throw <| IO.userError s!"equivalent scalar copy of typed tuple rejected: {reprStr copiedTupleGood}"
  -- 32. Branch-conditional UB inside an unused `ScalarExpr.select b 0 (true + 1)` must keep definedness
  --     conditional on `b` (never collapsing `ubCond` to constant false for `b = true, x = 999`)!
  let mkConditionalSelectUbDecl (retAt999 : UInt64) : LNIRDecl := {
    name := "conditional_select_ub"
    params := [
      { id := 0, name := "b", ty := .i1, borrow := false },
      { id := 1, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i64
    body :=
      .letBind 2 .i64 (.scalar (.select (.var 0) (.constU64 0) (.binOp .add (.constBool true) (.constU64 1))))
        (.letBind 3 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
          (.ite 3
            (.letBind 4 .i64 (.scalar (.constU64 retAt999)) (.ret 4))
            (.letBind 5 .i64 (.scalar (.constU64 0)) (.ret 5))))
  }
  let condSelectUbBad := validateTranslationDecl (mkConditionalSelectUbDecl 0) (mkConditionalSelectUbDecl 1) 8
  unless !condSelectUbBad.symRetEquiv && !condSelectUbBad.passed do
    throw <| IO.userError s!"branch-conditional UB in ScalarExpr.select collapsed ubCond globally: {reprStr condSelectUbBad}"
  let condSelectUbGood := validateTranslationDecl (mkConditionalSelectUbDecl 0) (mkConditionalSelectUbDecl 0) 8
  unless condSelectUbGood.passed do
    throw <| IO.userError s!"equivalent branch-conditional UB in ScalarExpr.select rejected: {reprStr condSelectUbGood}"
  -- 33. Concrete `evalBinOp` identity/idempotence cases on Boolean operands (`b &&& b`, `b + 0`, `b * 1`, `b ||| 0`)
  --     are concretely defined and must NOT collapse `ubCond` to false; and runtime-dependent `b + y` or `b1 &&& b2`
  --     must fail closed (`symUnsupported`) rather than assuming source UB!
  let mkBoolBitAndIdemDecl (retAt999 : UInt64) : LNIRDecl := {
    name := "bool_bitand_idem"
    params := [
      { id := 0, name := "b", ty := .i1, borrow := false },
      { id := 1, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i64
    body :=
      .letBind 2 .i1 (.scalar (.binOp .bitAnd (.var 0) (.var 0)))
        (.letBind 3 .i1 (.scalar (.binOp .add (.var 2) (.constU64 0)))
          (.letBind 4 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
            (.ite 4
              (.letBind 5 .i64 (.scalar (.constU64 retAt999)) (.ret 5))
              (.letBind 6 .i64 (.scalar (.constU64 0)) (.ret 6)))))
  }
  let boolIdemBad := validateTranslationDecl (mkBoolBitAndIdemDecl 0) (mkBoolBitAndIdemDecl 1) 8
  unless !boolIdemBad.symRetEquiv && !boolIdemBad.passed do
    throw <| IO.userError s!"Boolean identity/idempotence ops collapsed ubCond to false: {reprStr boolIdemBad}"
  let boolIdemGood := validateTranslationDecl (mkBoolBitAndIdemDecl 0) (mkBoolBitAndIdemDecl 0) 8
  unless boolIdemGood.passed do
    throw <| IO.userError s!"equivalent Boolean identity/idempotence ops rejected: {reprStr boolIdemGood}"
  let mkBoolRuntimeAddDecl (retAt999 : UInt64) : LNIRDecl := {
    name := "bool_runtime_add"
    params := [
      { id := 0, name := "b", ty := .i1, borrow := false },
      { id := 1, name := "y", ty := .i64, borrow := false },
      { id := 2, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i64
    body :=
      .letBind 3 .i1 (.scalar (.binOp .add (.var 0) (.var 1)))
        (.letBind 4 .i1 (.scalar (.binOp .eq (.var 2) (.constU64 999)))
          (.ite 4
            (.letBind 5 .i64 (.scalar (.constU64 retAt999)) (.ret 5))
            (.letBind 6 .i64 (.scalar (.constU64 0)) (.ret 6))))
  }
  let boolRuntimeBad := validateTranslationDecl (mkBoolRuntimeAddDecl 0) (mkBoolRuntimeAddDecl 1) 8
  unless !boolRuntimeBad.ubRefines && !boolRuntimeBad.passed do
    throw <| IO.userError s!"runtime-conditional `b + y` treated as definite source UB instead of unsupported: {reprStr boolRuntimeBad}"
  -- 34. `.fma` must route through the checked symbolic `mul`/`add` handlers so `fma true 1 0` stays defined
  --     (concrete `evalBinOp` identity cases) instead of collapsing `ubCond` to false!
  let mkFmaIdentityDecl (retAt999 : UInt64) : LNIRDecl := {
    name := "fma_identity"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .i64
    body :=
      .letBind 1 .i1 (.scalar (.fma (.constBool true) (.constU64 1) (.constU64 0)))
        (.letBind 2 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 999)))
          (.ite 2
            (.letBind 3 .i64 (.scalar (.constU64 retAt999)) (.ret 3))
            (.letBind 4 .i64 (.scalar (.constU64 0)) (.ret 4))))
  }
  let fmaIdBad := validateTranslationDecl (mkFmaIdentityDecl 0) (mkFmaIdentityDecl 1) 8
  unless !fmaIdBad.symRetEquiv && !fmaIdBad.passed do
    throw <| IO.userError s!"fma identity `true * 1 + 0` collapsed ubCond to false: {reprStr fmaIdBad}"
  let fmaIdGood := validateTranslationDecl (mkFmaIdentityDecl 0) (mkFmaIdentityDecl 0) 8
  unless fmaIdGood.passed do
    throw <| IO.userError s!"equivalent fma identity `true * 1 + 0` rejected: {reprStr fmaIdGood}"
  let mkFmaZeroBoolDecl (retAt999 : UInt64) : LNIRDecl := {
    name := "fma_zero_bool"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .i64
    body :=
      .letBind 1 .i1 (.scalar (.fma (.constU64 0) (.constU64 5) (.constBool true)))
        (.letBind 2 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 999)))
          (.ite 2
            (.letBind 3 .i64 (.scalar (.constU64 retAt999)) (.ret 3))
            (.letBind 4 .i64 (.scalar (.constU64 0)) (.ret 4))))
  }
  let fmaZeroBoolBad := validateTranslationDecl (mkFmaZeroBoolDecl 0) (mkFmaZeroBoolDecl 1) 8
  unless !fmaZeroBoolBad.symRetEquiv && !fmaZeroBoolBad.passed do
    throw <| IO.userError s!"fma `0 * 5 + true` collapsed ubCond to false: {reprStr fmaZeroBoolBad}"
  -- 35. `.u256` arithmetic `(y + constU256(2^64 - 1)) + constU256(1)` must preserve 256-bit carry (`y + 2^64` mod `2^256`)
  --     and NEVER fold via 64-bit wraparound to `y`, and mixed-width `y + constU64(1)` must be treated as UB!
  let mkU256CarryDecl (collapseCarry : Bool) : LNIRDecl := {
    name := "u256_low_limb_carry"
    params := [
      { id := 0, name := "y", ty := .u256, borrow := false },
      { id := 1, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .u256
    body :=
      .letBind 2 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
        (.ite 2
          (if collapseCarry then
             .ret 0
           else
             .letBind 3 .u256 (.constU256 ⟨0xffffffffffffffff, 0, 0, 0⟩)
               (.letBind 4 .u256 (.constU256 ⟨1, 0, 0, 0⟩)
                 (.letBind 5 .u256 (.scalar (.binOp .add (.binOp .add (.var 0) (.var 3)) (.var 4)))
                   (.ret 5))))
          (.ret 0))
  }
  let u256CarryBad := validateTranslationDecl (mkU256CarryDecl false) (mkU256CarryDecl true) 8
  unless !u256CarryBad.symRetEquiv && !u256CarryBad.passed do
    throw <| IO.userError s!"u256 low-limb carry `(y + (2^64 - 1)) + 1` erroneously folded to `y`: {reprStr u256CarryBad}"
  let u256CarryGood := validateTranslationDecl (mkU256CarryDecl false) (mkU256CarryDecl false) 8
  unless u256CarryGood.passed do
    throw <| IO.userError s!"equivalent u256 low-limb carry rejected: {reprStr u256CarryGood}"
  -- 36. Unknown-RC `decRef p 1` on an `.objPtr` input (which may free `p` when `rc == 1`, invalidating borrowed alias `q`)
  --     must mark symbolic execution unsupported (`symUnsupported`) and fail closed instead of assuming `rc > 1`!
  let mkUnknownRcFreeAliasDecl (readAfterDec : Bool) : LNIRDecl := {
    name := "unknown_rc_free_alias"
    params := [
      { id := 0, name := "p", ty := .objPtr, borrow := false },
      { id := 1, name := "q", ty := .objPtr, borrow := true }
    ]
    retTy := .i64
    body :=
      .letBind 2 .i64 (.call "lean_native_ctor_tag" [1] .i64 false)
        (.decRef 0 1
          (if readAfterDec then
             .letBind 3 .i64 (.call "lean_native_ctor_tag" [1] .i64 false)
               (.letBind 4 .i64 (.scalar (.constU64 0)) (.ret 4))
           else
             .letBind 4 .i64 (.scalar (.constU64 0)) (.ret 4)))
  }
  let unkFreeBad := validateTranslationDecl (mkUnknownRcFreeAliasDecl false) (mkUnknownRcFreeAliasDecl true) 8
  unless !unkFreeBad.ubRefines && !unkFreeBad.passed do
    throw <| IO.userError s!"unknown-RC decRef on objPtr masked post-free alias read: {reprStr unkFreeBad}"
  -- 37. Zero-count `incRef a 0` / `decRef a 0` on a freed heap object must check liveness (never skipping `rc == 0` UB)!
  let mkFreedZeroCountRcDecl (incZeroAt999 : Bool) : LNIRDecl := {
    name := "freed_zero_count_rc"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .i64
    body :=
      .letBind 1 .objPtr (.allocCtor 0 [] [])
        (.decRef 1 1
          (if incZeroAt999 then
             .letBind 2 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 999)))
               (.ite 2
                 (.incRef 1 0 (.letBind 3 .i64 (.scalar (.constU64 0)) (.ret 3)))
                 (.letBind 3 .i64 (.scalar (.constU64 0)) (.ret 3)))
           else
             .letBind 3 .i64 (.scalar (.constU64 0)) (.ret 3)))
  }
  let freedZeroBad := validateTranslationDecl (mkFreedZeroCountRcDecl false) (mkFreedZeroCountRcDecl true) 8
  unless !freedZeroBad.ubRefines && !freedZeroBad.passed do
    throw <| IO.userError s!"zero-count incRef on freed heap object bypassed liveness check: {reprStr freedZeroBad}"
  let mkRcWidthDecl (count : Nat) : LNIRDecl := {
    name := "known_rc_width"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .objPtr
    body :=
      .letBind 1 .objPtr (.allocCtor 0 [] [])
        (.letBind 2 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 999)))
          (.ite 2 (.incRef 1 count (.ret 1)) (.ret 1)))
  }
  for count in [18446744073709551616, 18446744073709551615] do
    let rcWidthBad := validateTranslationDecl (mkRcWidthDecl 0) (mkRcWidthDecl count) 8
    unless !rcWidthBad.ubRefines && !rcWidthBad.passed do
      throw <| IO.userError s!"known RC width overflow accepted for {count}: {reprStr rcWidthBad}"
  unless (validateTranslationDecl (mkRcWidthDecl 0) (mkRcWidthDecl 0) 8).passed do
    throw <| IO.userError "equivalent in-range known RC rejected"
  let mkSelectRootSafetyDecl (corrupt : Bool) : LNIRDecl := {
    name := "select_root_conditional_safety"
    params := [
      { id := 0, name := "y", ty := .u256, borrow := false },
      { id := 1, name := "z", ty := .u256, borrow := false },
      { id := 2, name := "a", ty := .i64, borrow := false },
      { id := 3, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i64
    body :=
      .letBind 4 .i64 (.scalar (.select (.binOp .div (.var 0) (.var 1)) (.var 2) (.var 2)))
        (.letBind 5 .i64 (.scalar
          (if corrupt then .select (.binOp .eq (.var 3) (.constU64 999)) (.constU64 1) (.constU64 0)
           else .constU64 0)) (.ret 5))
  }
  let selectRootSafetyBad := validateTranslationDecl (mkSelectRootSafetyDecl false) (mkSelectRootSafetyDecl true) 8
  unless !selectRootSafetyBad.ubRefines && !selectRootSafetyBad.passed do
    throw <| IO.userError s!"matching select roots discarded conditional safety: {reprStr selectRootSafetyBad}"
  let mkTupleHeapNamespaceDecl (returnLeaf : Bool) : LNIRDecl := {
    name := "tuple_heap_namespace"
    params := [
      { id := 0, name := "p", ty := .objPtr, borrow := false },
      { id := 1, name := "t", ty := .tuple (List.replicate 5907 .i64), borrow := false },
      { id := 2, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i64
    body :=
      .letBind 3 .i1 (.scalar (.binOp .eq (.var 2) (.constU64 999)))
        (.ite 3
          (.letBind 4 .i64 (.ctorGetScalar 0 0 .i64)
            (.letBind 5 .i64 (.projTuple 1 5906) (.ret (if returnLeaf then 5 else 4))))
          (.letBind 6 .i64 (.scalar (.constU64 0)) (.ret 6)))
  }
  let namespaceBad := validateTranslationDecl (mkTupleHeapNamespaceDecl false) (mkTupleHeapNamespaceDecl true) 0
  unless !namespaceBad.symRetEquiv && !namespaceBad.passed do
    throw <| IO.userError s!"tuple leaf collided with heap projection namespace: {reprStr namespaceBad}"
  let mkUnknownExtRcWrapDecl (incWrap : Bool) (c1 c2 : Nat) : LNIRDecl := {
    name := "unknown_ext_rc_wrap"
    params := [
      { id := 0, name := "p", ty := .objPtr, borrow := false },
      { id := 1, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i64
    body :=
      if incWrap then
        .letBind 2 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
          (.ite 2
            (.incRef 0 c1 (.incRef 0 c2 (.letBind 3 .i64 (.scalar (.constU64 0)) (.ret 3))))
            (.letBind 3 .i64 (.scalar (.constU64 0)) (.ret 3)))
      else
        .letBind 3 .i64 (.scalar (.constU64 0)) (.ret 3)
  }
  for (c1, c2) in [(18446744073709551615, 1), (4611686018427387904, 4611686018427387904)] do
    let extWrapBad := validateTranslationDecl (mkUnknownExtRcWrapDecl true c1 c2) (mkUnknownExtRcWrapDecl false 0 0) 8
    unless !extWrapBad.ubRefines && !extWrapBad.passed do
      throw <| IO.userError s!"unknown external RC overflow accepted for ({c1}, {c2}): {reprStr extWrapBad}"
  let mkBadCtorTagImmediateDecl (useU256 : Bool) (callTag : Bool) : LNIRDecl := {
    name := "ctor_tag_bad_immediate"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .i64
    body :=
      .letBind 1 (if useU256 then .u256 else .tuple [])
        (if useU256 then .constU256 UInt256.zero else .mkTuple [])
        (if callTag then
           .letBind 2 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 999)))
             (.ite 2
               (.letBind 3 .i64 (.call "lean_native_ctor_tag" [1] .i64 false)
                 (.letBind 4 .i64 (.scalar (.constU64 0)) (.ret 4)))
               (.letBind 4 .i64 (.scalar (.constU64 0)) (.ret 4)))
         else
           .letBind 4 .i64 (.scalar (.constU64 0)) (.ret 4))
  }
  for useU256 in [true, false] do
    let tagImmBad := validateTranslationDecl (mkBadCtorTagImmediateDecl useU256 false) (mkBadCtorTagImmediateDecl useU256 true) 8
    unless !tagImmBad.ubRefines && !tagImmBad.passed do
      throw <| IO.userError s!"lean_native_ctor_tag on unsupported immediate accepted (u256={useU256}): {reprStr tagImmBad}"
  let mkUnboxHeapTypeDecl (checkExcl : Bool) (useRootInExcl : Bool) : LNIRDecl := {
    name := "unbox_heap_type"
    params := [
      { id := 0, name := "p", ty := .objPtr, borrow := false },
      { id := 1, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i1
    body :=
      .letBind 2 .i64 (.unboxScalar 0 .i64)
        (if checkExcl then
           .letBind 3 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
             (.ite 3
               (.letBind 4 .i1 (.isExclusive (if useRootInExcl then 0 else 2)) (.ret 4))
               (.letBind 4 .i1 (.scalar (.constBool true)) (.ret 4)))
         else
           .letBind 4 .i1 (.scalar (.constBool true)) (.ret 4))
  }
  for useRoot in [true, false] do
    let unboxBad := validateTranslationDecl (mkUnboxHeapTypeDecl true useRoot) (mkUnboxHeapTypeDecl false useRoot) 8
    unless !unboxBad.symRetEquiv && !unboxBad.passed do
      throw <| IO.userError s!"unboxScalar erased heap type of objPtr (useRoot={useRoot}): {reprStr unboxBad}"
  let mkProjCachedSortDecl (corruptAt999 : Bool) (cmpProjected : Bool) : LNIRDecl := {
    name := "proj_cached_sort"
    params := [
      { id := 0, name := "b", ty := .i1, borrow := false },
      { id := 1, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i64
    body :=
      .letBind 2 .objPtr (.allocCtor 0 [] [0])
        (.letBind 3 .i64 (.ctorGetScalar 2 0 .i64)
          (.letBind 4 .i1 (.scalar (.binOp .eq (.var (if cmpProjected then 3 else 0)) (.constBool true)))
            (.decRef 2 1
              (.letBind 5 .i64 (.scalar
                (if corruptAt999 then .select (.binOp .eq (.var 1) (.constU64 999)) (.constU64 1) (.constU64 0)
                 else .constU64 0)) (.ret 5)))))
  }
  for cmpProjected in [false, true] do
    let projSortBad := validateTranslationDecl (mkProjCachedSortDecl false cmpProjected) (mkProjCachedSortDecl true cmpProjected) 8
    unless !projSortBad.symRetEquiv && !projSortBad.passed do
      throw <| IO.userError s!"ctorGetScalar overwrote cached field runtime sort (cmpProjected={cmpProjected}): {reprStr projSortBad}"
  let mkProjTupleOnHeapCtorDecl (projHeap : Bool) : LNIRDecl := {
    name := "proj_tuple_on_heap_ctor"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .i64
    body :=
      .letBind 1 .objPtr (.allocCtor 0 [] [0])
        (if projHeap then
           .letBind 2 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 999)))
             (.ite 2
               (.letBind 3 .i64 (.projTuple 1 0) (.decRef 1 1 (.letBind 4 .i64 (.scalar (.constU64 0)) (.ret 4))))
               (.decRef 1 1 (.letBind 4 .i64 (.scalar (.constU64 0)) (.ret 4))))
         else
           .decRef 1 1 (.letBind 4 .i64 (.scalar (.constU64 0)) (.ret 4)))
  }
  let projHeapBad := validateTranslationDecl (mkProjTupleOnHeapCtorDecl false) (mkProjTupleOnHeapCtorDecl true) 8
  unless !projHeapBad.ubRefines && !projHeapBad.passed do
    throw <| IO.userError s!"projTuple on heap constructor root accepted: {reprStr projHeapBad}"
  let mkScalarFieldsHeapPtrDecl (constTrue : Bool) : LNIRDecl := {
    name := "scalar_fields_heap_ptr"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .i1
    body :=
      .letBind 1 .objPtr (.allocCtor 0 [] [])
        (.letBind 2 .objPtr (.allocCtor 0 [] [1])
          (.letBind 3 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 999)))
            (.ite 3
              (.incRef 1 1
                (.letBind 4 .objPtr (.ctorGetObj 2 0)
                  (.letBind 5 .i1 (if constTrue then .scalar (.constBool true) else .isExclusive 4)
                    (.decRef 1 1 (.decRef 2 1 (.ret 5))))))
              (.letBind 4 .objPtr (.ctorGetObj 2 0)
                (.letBind 5 .i1 (if constTrue then .scalar (.constBool true) else .isExclusive 4)
                  (.decRef 2 1 (.ret 5)))))))
  }
  let scalarFieldsHeapBad := validateTranslationDecl (mkScalarFieldsHeapPtrDecl false) (mkScalarFieldsHeapPtrDecl true) 8
  unless !scalarFieldsHeapBad.symRetEquiv && !scalarFieldsHeapBad.passed do
    throw <| IO.userError s!"allocCtor scalarFields copied heap snapshot instead of root identity: {reprStr scalarFieldsHeapBad}"
  let mkUncachedCtorFieldExclDecl (constTrue : Bool) : LNIRDecl := {
    name := "uncached_ctor_field_excl"
    params := [
      { id := 0, name := "p", ty := .objPtr, borrow := false },
      { id := 1, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i1
    body :=
      .letBind 2 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
        (.ite 2
          (.letBind 3 .i64 (.ctorGetScalar 0 0 .i64)
            (if constTrue then
               .letBind 4 .i1 (.scalar (.constBool true)) (.ret 4)
             else
               .letBind 4 .i1 (.isExclusive 3) (.ret 4)))
          (.letBind 4 .i1 (.scalar (.constBool true)) (.ret 4)))
  }
  let uncachedFieldBad := validateTranslationDecl (mkUncachedCtorFieldExclDecl false) (mkUncachedCtorFieldExclDecl true) 8
  unless !uncachedFieldBad.ubRefines && !uncachedFieldBad.passed do
    throw <| IO.userError s!"ctorGetScalar assumed runtime scalar sort on uncached field: {reprStr uncachedFieldBad}"
  let mkTupleParamObjPtrProjDecl (constTrue : Bool) : LNIRDecl := {
    name := "tuple_param_objptr_proj"
    params := [
      { id := 0, name := "t", ty := .tuple [.objPtr], borrow := false },
      { id := 1, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .i1
    body :=
      .letBind 2 .i64 (.projTuple 0 0)
        (.letBind 3 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
          (.ite 3
            (if constTrue then
               .letBind 4 .i1 (.scalar (.constBool true)) (.ret 4)
             else
               .letBind 4 .i1 (.isExclusive 2) (.ret 4))
            (.letBind 4 .i1 (.scalar (.constBool true)) (.ret 4))))
  }
  let tupleParamObjBad := validateTranslationDecl (mkTupleParamObjPtrProjDecl false) (mkTupleParamObjPtrProjDecl true) 8
  unless !tupleParamObjBad.ubRefines && !tupleParamObjBad.passed do
    throw <| IO.userError s!"projTuple manufactured scalar sort for tuple [objPtr] parameter field: {reprStr tupleParamObjBad}"
  let mkCtorGetOnUnboxedTupleDecl (corruptAt999 : Bool) (returnProjected : Bool) : LNIRDecl := {
    name := "ctor_get_on_unboxed_tuple"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .i64
    body :=
      .letBind 1 .i64 (.scalar (.constU64 0))
        (.letBind 2 (.tuple [.i64, .i64]) (.mkTuple [1, 0])
          (.letBind 3 .i64 (.ctorGetScalar 2 0 .i64)
            (if returnProjected then
               .letBind 4 .i64 (.scalar (if corruptAt999 then .select (.binOp .eq (.var 0) (.constU64 999)) (.constU64 1) (.var 0) else .var 3))
                 (.ret 4)
             else
               .letBind 4 .i64 (.scalar (if corruptAt999 then .select (.binOp .eq (.var 0) (.constU64 999)) (.constU64 1) (.constU64 0) else .constU64 0))
                 (.ret 4))))
  }
  for retProj in [false, true] do
    let ctorTupleBad := validateTranslationDecl (mkCtorGetOnUnboxedTupleDecl false retProj) (mkCtorGetOnUnboxedTupleDecl true retProj) 8
    unless !ctorTupleBad.symRetEquiv && !ctorTupleBad.passed do
      throw <| IO.userError s!"ctorGetScalar on unboxed tuple collapsed ubCond or returned wrong field (retProj={retProj}): {reprStr ctorTupleBad}"
  unless (validateTranslationDecl (mkCtorGetOnUnboxedTupleDecl false true) (mkCtorGetOnUnboxedTupleDecl false true) 8).passed do
    throw <| IO.userError "equivalent ctorGetScalar on unboxed tuple rejected"
  let mkTagRefinedReturnDecl (returnTupleAt999 : Bool) : LNIRDecl := {
    name := "tag_refined_return_heap_provenance"
    params := [
      { id := 0, name := "p", ty := .objPtr, borrow := false },
      { id := 1, name := "x", ty := .i64, borrow := false }
    ]
    retTy := .objPtr
    body :=
      .letBind 2 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
        (.ite 2
          (.letBind 3 .i64 (.call "lean_native_ctor_tag" [0] .i64 false)
            (.letBind 4 .i1 (.scalar (.binOp .eq (.var 3) (.constU64 0)))
              (.ite 4
                (.letBind 10 .i64 (.scalar (.constU64 0))
                  (.letBind 11 .objPtr (.ctorGetObj 0 0)
                    (.letBind 12 .objPtr (.ctorGetObj 0 1)
                      (.letBind 13 .objPtr (.ctorGetObj 0 2)
                        (.letBind 14 .objPtr (.ctorGetObj 0 3)
                          (.letBind 15 .objPtr (.ctorGetObj 0 4)
                            (.letBind 16 .objPtr (.ctorGetObj 0 5)
                              (.letBind 17 .objPtr (.ctorGetObj 0 6)
                                (.letBind 18 .objPtr (.ctorGetObj 0 7)
                                  (.letBind 19 (.tuple (List.replicate 9 .i64)) (.mkTuple [10, 11, 12, 13, 14, 15, 16, 17, 18])
                                    (.ret (if returnTupleAt999 then 19 else 0))))))))))))
                (.ret 0))))
          (.ret 0))
  }
  let tagRetBad := validateTranslationDecl (mkTagRefinedReturnDecl false) (mkTagRefinedReturnDecl true) 8
  unless !tagRetBad.symRetEquiv && !tagRetBad.passed do
    throw <| IO.userError s!"tag-refined input objPtr return collapsed to unboxed tuple: {reprStr tagRetBad}"
  let mkOverflowTagDecl (tagAt999 : Nat) : LNIRDecl := {
    name := "alloc_ctor_tag_overflow"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .objPtr
    body :=
      .letBind 1 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 999)))
        (.ite 1
          (.letBind 2 .objPtr (.allocCtor tagAt999 [] []) (.ret 2))
          (.letBind 2 .objPtr (.allocCtor 0 [] []) (.ret 2)))
  }
  let ovfTagBad := validateTranslationDecl (mkOverflowTagDecl 0) (mkOverflowTagDecl 18446744073709551616) 8
  unless !ovfTagBad.ubRefines && !ovfTagBad.passed do
    throw <| IO.userError s!"allocCtor tag > UInt64.max truncated without failing closed: {reprStr ovfTagBad}"
  let ovfTagSrcBad := validateTranslationDecl (mkOverflowTagDecl 18446744073709551616) (mkOverflowTagDecl 0) 8
  unless !ovfTagSrcBad.ubRefines && !ovfTagSrcBad.passed do
    throw <| IO.userError s!"source allocCtor tag > UInt64.max accepted non-identity target: {reprStr ovfTagSrcBad}"
  let mkLoopHeapAccDecl (constOneAt999 : Bool) : LNIRDecl := {
    name := "loop_heap_acc_proj"
    params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
    retTy := .i64
    body :=
      .letBind 1 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 999)))
        (.ite 1
          (.letBind 2 .i64 (.scalar (.constU64 7))
            (.letBind 3 .objPtr (.allocCtor 0 [] [2])
              (.letBind 4 .i64 (.scalar (.constU64 0))
                (.letBind 5 .i64 (.scalar (.constU64 4))
                  (.seqFor 6 4 5 7 3 .objPtr
                    (.ret 7)
                    (.letBind 8 .i64 (.ctorGetScalar 7 0 .i64)
                      (.decRef 7 1
                        (if constOneAt999 then
                           .letBind 9 .i64 (.scalar (.constU64 1)) (.ret 9)
                         else
                           .ret 8))))))))
          (.letBind 9 .i64 (.scalar (.constU64 0)) (.ret 9)))
  }
  let loopHeapBad := validateTranslationDecl (mkLoopHeapAccDecl false) (mkLoopHeapAccDecl true) 8
  unless !loopHeapBad.symRetEquiv && !loopHeapBad.passed do
    throw <| IO.userError s!"seqFor loop body return expanded heap summary into accumulator: {reprStr loopHeapBad}"
  unless (validateTranslationDecl (mkLoopHeapAccDecl false) (mkLoopHeapAccDecl false) 8).passed do
    throw <| IO.userError "equivalent seqFor heap-accumulator declaration rejected"
''', encoding="utf-8")
            alias_res = subprocess.run(["lake", "env", "lean", str(alias_tv)], cwd=fuzzer.ROOT / "lean",
                                       capture_output=True, text=True)
            self.assertEqual(alias_res.returncode, 0, alias_res.stdout + alias_res.stderr)


if __name__ == "__main__":
    unittest.main()
