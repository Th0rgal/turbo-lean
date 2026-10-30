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
     ("unsupported string literal", lowerLitValue (.str "abc") >>= fun _ => pure (.ret 0))]
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

    def test_opt_in_allow_rc_adt_lowering_and_default_rejection(self):
        engines = fuzzer.probe_engines()
        core_bin = engines["core_bin"]
        full_bin = engines["full_bin"]
        lean_bin = engines["lean_bin"]
        source = """inductive Packet where
  | pair : (UInt64 × UInt64) → (UInt64 × UInt64) → Packet
  | empty : Packet

@[inline] def stepPacket (pkt : Packet) (delta : UInt64) : Packet :=
  match pkt with
  | .pair p q =>
    .pair (p.1 + delta, p.2 ^^^ delta) (q.1 + (delta <<< 1), q.2 + 17)
  | .empty => .empty

@[inline] def foldPacket (pkt : Packet) : UInt64 :=
  match pkt with
  | .pair p q => ((p.1 * 31) ^^^ p.2) + ((q.1 * 13) ^^^ q.2)
  | .empty => 99
""" + """
@[export probe_rc_reuse]
def probe_rc_reuse (x y : UInt64) : UInt64 :=
  let p0 := Packet.pair (x, y) (x + 3, y ^^^ 9)
  let p1 := stepPacket p0 11
  foldPacket p1

@[export probe_rc_alias]
def probe_rc_alias (x y : UInt64) : UInt64 :=
  let p0 := Packet.pair (x, y) (y + 5, x ^^^ 15)
  let p1 := stepPacket p0 7
  let p2 := stepPacket p0 19
  foldPacket p1 + foldPacket p2
"""
        with tempfile.TemporaryDirectory(prefix="allow_rc_adt_") as directory:
            tmp = Path(directory)
            src = tmp / "RcAdtProbe.lean"
            src.write_text(source, encoding="utf-8")
            wire = tmp / "rc_adt.lnir"
            rejected = subprocess.run(
                [full_bin, "emit-lnir", "--wire", str(src), "-o", str(wire)],
                capture_output=True, text=True,
            )
            self.assertNotEqual(rejected.returncode, 0, "default emit-lnir must stay scalar-only without --allow-rc-adt")
            subprocess.run(
                [full_bin, "emit-lnir", "--wire", "--allow-rc-adt", str(src), "-o", str(wire)],
                check=True, capture_output=True, text=True,
            )
            wire_text = wire.read_text(encoding="utf-8")
            for token in ("C_inc", "C_dec", "E_ctor", "E_cgeto", "E_isexcl", "E_mktup", "E_projtup", "C_ite"):
                self.assertGreater(wire_text.count(token), 0, f"missing expected LNIR wire op {token}")
            tv_out = subprocess.check_output(
                [core_bin, "validate-tv", "--lnir", str(wire), "--json"], text=True,
            )
            tv_json = json.loads(tv_out)
            self.assertTrue(tv_json.get("allPassed"), tv_json)
            oracle = tmp / "Oracle.lean"
            oracle.write_text(
                "import RcAdtProbe\n"
                "def main : IO Unit := do\n"
                "  IO.println s!\"{(probe_rc_reuse 42 7).toNat},{(probe_rc_alias 42 7).toNat}\"\n",
                encoding="utf-8",
            )
            env = {**dict(__import__("os").environ), "LEAN_PATH": str(tmp)}
            subprocess.run([lean_bin, "RcAdtProbe.lean", "-o", "RcAdtProbe.olean"], cwd=tmp, env=env, check=True)
            stock_vals = [int(x) for x in subprocess.check_output(
                [lean_bin, "--run", "Oracle.lean"], cwd=tmp, env=env, text=True
            ).strip().split(",")]
            bindings = "probe_rc_reuse:42,7;probe_rc_alias:42,7"
            for extra in ([], ["--opt"]):
                rows = json.loads(subprocess.check_output(
                    [core_bin, "eval-lnir", "--lnir", str(wire), "--args", bindings, "--batch-json", *extra],
                    text=True,
                ))
                self.assertEqual([int(r["value_u64"]) for r in rows], stock_vals)
                self.assertEqual([r["live_objects"] for r in rows], [0, 0])

    def test_rc_adt_heap_semantics_uaf_recursive_decref_and_del_shell(self):
        core_bin = fuzzer.probe_engines()["core_bin"]
        del_hex = "lean_native_del_obj".encode("utf-8").hex()
        decls = [
            "D_decl|" + "distinguish_objs".encode().hex() + "|A_L2|0|1|0|78|0|T_i64|T_i1|"
            "C_let|1|T_objPtr|E_ctor|0|0|1|0|"
            "C_let|2|T_objPtr|E_ctor|0|0|1|0|"
            "C_let|3|T_i64|E_cgets|1|0|T_i64|"
            "C_let|4|T_i64|E_cgets|2|0|T_i64|"
            "C_dec|1|1|C_dec|2|1|"
            "C_let|5|T_i1|E_scalar|S_bin|B_eq|S_var|3|S_var|4|C_ret|5",
            "D_decl|" + "uaf_after_dec".encode().hex() + "|A_L2|0|1|0|78|0|T_i64|T_i64|"
            "C_let|1|T_objPtr|E_ctor|0|0|1|0|"
            "C_dec|1|1|"
            "C_let|2|T_i64|E_cgets|1|0|T_i64|C_ret|2",
            "D_decl|" + "recursive_child_decref".encode().hex() + "|A_L2|0|1|0|78|0|T_i64|T_i64|"
            "C_let|1|T_objPtr|E_ctor|0|0|1|0|"
            "C_let|2|T_objPtr|E_ctor|1|1|1|0|"
            "C_dec|2|1|C_ret|0",
            "D_decl|" + "del_shell_preserves_child".encode().hex() + "|A_L2|0|1|0|78|0|T_i64|T_i64|"
            "C_let|1|T_objPtr|E_ctor|0|0|1|0|"
            "C_let|2|T_objPtr|E_ctor|1|1|1|0|"
            "C_let|3|T_objPtr|E_cgeto|2|0|"
            "C_let|4|T_unit|E_call|" + del_hex + "|0|1|2|T_unit|"
            "C_let|5|T_i64|E_cgets|3|0|T_i64|"
            "C_dec|3|1|C_ret|5",
        ]
        wire_text = f"LNIR_WIRE_V1|{'rc_heap_sem'.encode().hex()}|{len(decls)}|" + "|".join(decls)
        with tempfile.TemporaryDirectory(prefix="rc_heap_sem_") as directory:
            wire_path = Path(directory) / "rc_heap_sem.lnir"
            wire_path.write_text(wire_text, encoding="utf-8")
            r_dist = json.loads(subprocess.check_output(
                [core_bin, "eval-lnir", "--lnir", str(wire_path), "--decl", "distinguish_objs", "--args", "77"],
                text=True,
            ))
            self.assertTrue(r_dist["ok"], r_dist)
            self.assertEqual(int(r_dist["value_u64"]), 1)
            self.assertEqual(r_dist["live_objects"], 0)
            uaf_run = subprocess.run(
                [core_bin, "eval-lnir", "--lnir", str(wire_path), "--decl", "uaf_after_dec", "--args", "77"],
                capture_output=True, text=True,
            )
            self.assertNotEqual(uaf_run.returncode, 0)
            uaf_json = json.loads(uaf_run.stdout)
            self.assertFalse(uaf_json["ok"])
            self.assertIn("useAfterFree", uaf_json["error"])
            r_rec = json.loads(subprocess.check_output(
                [core_bin, "eval-lnir", "--lnir", str(wire_path), "--decl", "recursive_child_decref", "--args", "55"],
                text=True,
            ))
            self.assertTrue(r_rec["ok"], r_rec)
            self.assertEqual(r_rec["live_objects"], 0)
            for extra in ([], ["--opt"]):
                r_shell = json.loads(subprocess.check_output(
                    [core_bin, "eval-lnir", "--lnir", str(wire_path), "--decl", "del_shell_preserves_child", "--args", "91", *extra],
                    text=True,
                ))
                self.assertTrue(r_shell["ok"], r_shell)
                self.assertEqual(int(r_shell["value_u64"]), 91)
                self.assertEqual(r_shell["live_objects"], 0)

    def test_impure_lcnf_layout_sset_uset_box_settag_del_persistent_and_residual_call_gate(self):
        engines = fuzzer.probe_engines()
        core_bin = engines["core_bin"]
        full_bin = engines["full_bin"]
        lean_bin = engines["lean_bin"]
        source = """inductive LeafBox where
  | mkA : UInt64 → LeafBox
  | mkB : UInt64 → LeafBox

inductive MixedNode where
  | alpha : LeafBox → USize → UInt64 → UInt8 → Bool → MixedNode
  | beta : LeafBox → USize → UInt64 → UInt8 → Bool → MixedNode
  | leaf : UInt64 → MixedNode

@[inline] def flipNode (n : MixedNode) (delta : UInt64) : MixedNode :=
  match n with
  | .alpha child us u64 b8 flag =>
    .beta child (us + 3) (u64 + delta) (b8 + 1) (!flag)
  | .beta child us u64 b8 flag =>
    .alpha child (us + 5) (u64 ^^^ delta) (b8 + 2) (!flag)
  | .leaf v => .leaf (v + delta)

@[inline] def scoreNode (n : MixedNode) : UInt64 :=
  match n with
  | .alpha child us u64 b8 flag =>
    let childV := match child with | .mkA k => k | .mkB k => k + 1
    childV + us.toUInt64 * 17 + u64 + b8.toUInt64 * 257 + (if flag then 1000 else 2000)
  | .beta child us u64 b8 flag =>
    let childV := match child with | .mkA k => k | .mkB k => k + 1
    childV + us.toUInt64 * 31 + u64 + b8.toUInt64 * 513 + (if flag then 3000 else 4000)
  | .leaf v => v + 99

def constClosedNode : MixedNode :=
  MixedNode.alpha (LeafBox.mkA 41) 7 900 12 true

inductive ErasedCarrier where
  | mk : UInt64 → True → UInt64 → ErasedCarrier

@[inline] def bumpCarrier (c : ErasedCarrier) (d : UInt64) : ErasedCarrier :=
  match c with
  | .mk a h b => .mk (a + d) h (b ^^^ d)

@[export probe_mixed_reuse]
def probe_mixed_reuse (x : UInt64) : UInt64 :=
  let n0 := MixedNode.alpha (LeafBox.mkA (x + 1)) (x.toUSize + 2) (x * 5) x.toUInt8 (x % 2 == 0)
  let n1 := flipNode n0 19
  let n2 := flipNode n1 23
  scoreNode n2

@[export probe_mixed_shared_and_closed]
def probe_mixed_shared_and_closed (x : UInt64) : UInt64 :=
  let n0 := MixedNode.alpha (LeafBox.mkB (x + 4)) 9 (x + 100) 5 true
  let a := flipNode n0 7
  let b := flipNode n0 13
  let c := flipNode constClosedNode x
  scoreNode a + scoreNode b + scoreNode c

@[export probe_boxed_prod_and_erased]
def probe_boxed_prod_and_erased (x : UInt64) : UInt64 :=
  let p : MixedNode × UInt64 := (MixedNode.leaf (x + 11), x * 3 + 7)
  let q : MixedNode × UInt64 := (flipNode p.1 5, p.2 + 29)
  let ec := bumpCarrier (ErasedCarrier.mk x trivial (x + 8)) 15
  let ecSum := match ec with | .mk u _ v => u + v
  scoreNode q.1 + q.2 + ecSum

@[inline] def bumpObjProd (p : MixedNode × UInt64) (d : UInt64) : MixedNode × UInt64 :=
  match p with
  | (n, k) => (flipNode n d, k + d)

@[inline] def bumpObjMProd (p : MProd MixedNode UInt64) (d : UInt64) : MProd MixedNode UInt64 :=
  match p with
  | ⟨n, k⟩ => ⟨flipNode n d, k + d⟩

@[export probe_obj_prod_shared_and_excl]
def probe_obj_prod_shared_and_excl (x : UInt64) : UInt64 :=
  let base : MixedNode × UInt64 := (MixedNode.alpha (LeafBox.mkA (x + 3)) (x.toUSize + 1) (x * 2) x.toUInt8 true, x + 5)
  let ex1 := bumpObjProd base 7
  let ex2 := bumpObjProd ex1 11
  let sh : MixedNode × UInt64 := (MixedNode.leaf (x + 9), x + 13)
  let sa := bumpObjProd sh 17
  let sb := bumpObjProd sh 23
  scoreNode ex2.1 + ex2.2 + scoreNode sa.1 + sa.2 + scoreNode sb.1 + sb.2

@[export probe_mprod_and_nested_prod]
def probe_mprod_and_nested_prod (x : UInt64) : UInt64 :=
  let mp0 : MProd MixedNode UInt64 := ⟨MixedNode.leaf (x + 4), x + 6⟩
  let mp1 := bumpObjMProd mp0 9
  let mps : MProd MixedNode UInt64 := ⟨MixedNode.alpha (LeafBox.mkB (x + 2)) 5 (x + 8) 3 false, x + 10⟩
  let mpa := bumpObjMProd mps 13
  let mpb := bumpObjMProd mps 19
  let nested : (MixedNode × UInt64) × (UInt64 × UInt64) :=
    ((MixedNode.leaf (x + 21), x + 22), (x + 23, x + 24))
  let nestedExcl : (MixedNode × UInt64) × (UInt64 × UInt64) :=
    match nested with
    | ((n, a), (b, c)) => ((flipNode n 5, a + b), (b + 1, c + 2))
  let nestedSharedA := bumpObjProd nestedExcl.1 3
  let nestedSharedB := bumpObjProd nestedExcl.1 7
  let pp : PProd MixedNode UInt64 := ⟨MixedNode.leaf (x + 31), x + 32⟩
  let ppNext : PProd MixedNode UInt64 := match pp with | ⟨n, k⟩ => ⟨flipNode n 11, k + 13⟩
  let ppSharedA := flipNode ppNext.1 2
  let ppSharedB := flipNode ppNext.1 6
  scoreNode mp1.1 + mp1.2 + scoreNode mpa.1 + mpa.2 + scoreNode mpb.1 + mpb.2 +
    scoreNode nestedSharedA.1 + nestedSharedA.2 + scoreNode nestedSharedB.1 + nestedSharedB.2 +
    nestedExcl.2.1 + nestedExcl.2.2 + scoreNode ppSharedA + scoreNode ppSharedB + ppNext.2
"""
        rec_source = """inductive NatList where
  | nil : NatList
  | cons : UInt64 → NatList → NatList

def sumList : NatList → UInt64
  | .nil => 0
  | .cons h t => h + sumList t

@[export probe_rec]
def probe_rec (x : UInt64) : UInt64 :=
  sumList (.cons x (.cons (x + 1) .nil))
"""
        with tempfile.TemporaryDirectory(prefix="impure_lcnf_layout_") as directory:
            tmp = Path(directory)
            src = tmp / "MixedLayoutProbe.lean"
            src.write_text(source, encoding="utf-8")
            wire = tmp / "mixed_layout.lnir"
            subprocess.run(
                [full_bin, "emit-lnir", "--wire", "--allow-rc-adt", str(src), "-o", str(wire)],
                check=True, capture_output=True, text=True,
            )
            wire_text = wire.read_text(encoding="utf-8")
            self.assertIn("E_cgets", wire_text)
            self.assertIn("lean_native_del_obj".encode("utf-8").hex(), wire_text)
            tv_json = json.loads(subprocess.check_output(
                [core_bin, "validate-tv", "--lnir", str(wire), "--json"], text=True,
            ))
            self.assertTrue(tv_json.get("allPassed"), tv_json)
            for decl_res in tv_json.get("declResults", []):
                self.assertGreater(decl_res.get("concreteSamplesOk", 0), 0, decl_res)
            cert_json = json.loads(subprocess.check_output(
                [core_bin, "verify-certs", "--lnir", str(wire), "--json"], text=True,
            ))
            self.assertTrue(cert_json.get("verified"), cert_json)
            tv_src_json = json.loads(subprocess.check_output(
                [full_bin, "validate-tv", "--allow-rc-adt", str(src), "--json"], text=True,
            ))
            self.assertTrue(tv_src_json.get("allPassed"), tv_src_json)
            cert_src_json = json.loads(subprocess.check_output(
                [full_bin, "verify-certs", "--allow-rc-adt", str(src), "--json"], text=True,
            ))
            self.assertTrue(cert_src_json.get("verified"), cert_src_json)
            oracle = tmp / "Oracle.lean"
            oracle.write_text(
                "import MixedLayoutProbe\n"
                "def main : IO Unit := do\n"
                "  IO.println s!\"{(probe_mixed_reuse 37).toNat},{(probe_mixed_shared_and_closed 37).toNat},{(probe_boxed_prod_and_erased 37).toNat},{(probe_obj_prod_shared_and_excl 37).toNat},{(probe_mprod_and_nested_prod 37).toNat}\"\n",
                encoding="utf-8",
            )
            env = {**dict(__import__("os").environ), "LEAN_PATH": str(tmp)}
            subprocess.run([lean_bin, "MixedLayoutProbe.lean", "-o", "MixedLayoutProbe.olean"], cwd=tmp, env=env, check=True)
            stock_vals = [int(x) for x in subprocess.check_output(
                [lean_bin, "--run", "Oracle.lean"], cwd=tmp, env=env, text=True
            ).strip().split(",")]
            bindings = "probe_mixed_reuse:37;probe_mixed_shared_and_closed:37;probe_boxed_prod_and_erased:37;probe_obj_prod_shared_and_excl:37;probe_mprod_and_nested_prod:37"
            for extra in ([], ["--opt"]):
                rows = json.loads(subprocess.check_output(
                    [core_bin, "eval-lnir", "--lnir", str(wire), "--args", bindings, "--batch-json", *extra],
                    text=True,
                ))
                self.assertEqual([int(r["value_u64"]) for r in rows], stock_vals)
                self.assertEqual(rows[0]["live_objects"], 0)
                self.assertEqual(rows[2]["live_objects"], 0)
                self.assertEqual(rows[3]["live_objects"], 0)
                self.assertEqual(rows[4]["live_objects"], 0)
                self.assertLessEqual(rows[1]["live_objects"], 2)
            rec_file = tmp / "RecProbe.lean"
            rec_file.write_text(rec_source, encoding="utf-8")
            rec_res = subprocess.run(
                [full_bin, "emit-lnir", "--wire", "--allow-rc-adt", str(rec_file), "-o", str(tmp / "rec.lnir")],
                capture_output=True, text=True,
            )
            self.assertNotEqual(rec_res.returncode, 0, "residual uninlined recursive call must fail closed")

    def test_allow_rc_adt_cli_and_wire_fail_closed_gates(self):
        engines = fuzzer.probe_engines()
        core_bin = engines["core_bin"]
        full_bin = engines["full_bin"]
        rc_decl = (
            "D_decl|" + "rc_only_decl".encode().hex() + "|A_L2|0|1|0|78|0|T_objPtr|T_i64|"
            "C_let|1|T_i64|E_cgets|0|0|T_i64|C_dec|0|1|C_ret|1"
        )
        rc_wire = f"LNIR_WIRE_V1|{'rc_gate_mod'.encode().hex()}|1|{rc_decl}"
        with tempfile.TemporaryDirectory(prefix="rc_adt_gate_") as directory:
            tmp = Path(directory)
            wire_file = tmp / "rc_gate.lnir"
            wire_file.write_text(rc_wire, encoding="utf-8")
            tv_ok = json.loads(subprocess.check_output(
                [core_bin, "validate-tv", "--lnir", str(wire_file), "--json"], text=True,
            ))
            self.assertTrue(tv_ok.get("allPassed"), tv_ok)
            self.assertEqual(tv_ok["declResults"][0]["concreteSamplesOk"], 64)
            cert_ok = json.loads(subprocess.check_output(
                [core_bin, "verify-certs", "--lnir", str(wire_file), "--json"], text=True,
            ))
            self.assertTrue(cert_ok.get("verified"), cert_ok)
            slot_ok = subprocess.run(
                [core_bin, "compile-llvm", "--slot-regression"],
                capture_output=True, text=True,
            )
            self.assertEqual(slot_ok.returncode, 0, slot_ok.stderr)
            for bad_flag_cmd in (
                [full_bin, "compile-llvm", "--allow-rc-adt", "--canonical-benchmark"],
                [full_bin, "compile-static-lib", "--allow-rc-adt", "--canonical-benchmark", "-o", str(tmp / "x.a")],
                [full_bin, "compile-ptx", "--allow-rc-adt", "--canonical-benchmark"],
                [full_bin, "compile-metal", "--allow-rc-adt", "--canonical-benchmark"],
                [full_bin, "compile-mlir", "--allow-rc-adt", "--canonical-benchmark"],
                [full_bin, "compile-fastcheck", "--allow-rc-adt", "--fastcheck-sample"],
                [full_bin, "compile-hybrid", "--allow-rc-adt", "--canonical-benchmark"],
                [full_bin, "emit-cabi-bindings", "--allow-rc-adt", "--canonical-benchmark"],
                [full_bin, "superopt", "--allow-rc-adt", "--canonical-benchmark"],
                [full_bin, "plugins", "--allow-rc-adt", "--canonical-benchmark"],
                [full_bin, "telemetry", "--allow-rc-adt", "--canonical-benchmark"],
                [full_bin, "--c-abi", "--allow-rc-adt", "--canonical-benchmark"],
                [full_bin, "build-exe", "--allow-rc-adt", str(tmp / "missing.lean")],
                [full_bin, "worker", "--allow-rc-adt"],
            ):
                res = subprocess.run(bad_flag_cmd, capture_output=True, text=True)
                self.assertNotEqual(res.returncode, 0, f"expected --allow-rc-adt rejection for {bad_flag_cmd}")
            for bad_wire_cmd in (
                [core_bin, "compile-llvm", "--lnir", str(wire_file)],
                [core_bin, "compile-static-lib", "--lnir", str(wire_file), "-o", str(tmp / "y.a")],
                [core_bin, "compile-ptx", "--lnir", str(wire_file)],
                [core_bin, "compile-metal", "--lnir", str(wire_file)],
                [core_bin, "compile-mlir", "--lnir", str(wire_file)],
                [core_bin, "compile-fastcheck", "--lnir", str(wire_file)],
                [core_bin, "compile-hybrid", "--lnir", str(wire_file)],
                [core_bin, "emit-cabi-bindings", "--lnir", str(wire_file)],
                [core_bin, "superopt", "--lnir", str(wire_file)],
                [core_bin, "plugins", "--lnir", str(wire_file)],
                [core_bin, "compile", "--lnir", str(wire_file)],
            ):
                res = subprocess.run(bad_wire_cmd, capture_output=True, text=True)
                self.assertNotEqual(res.returncode, 0, f"expected RC-ADT wire rejection for {bad_wire_cmd}")
            worker_reqs = [
                {"id": 1, "method": "compile-llvm", "wire": rc_wire},
                {"id": 2, "method": "compile-ptx", "wire": rc_wire},
                {"id": 3, "method": "compile-metal", "wire": rc_wire},
                {"id": 4, "method": "compile-mlir", "wire": rc_wire},
                {"id": 5, "method": "compile-fastcheck", "wire": rc_wire},
                {"id": 6, "method": "fastcheck", "wire": rc_wire},
                {"id": 7, "method": "batch-fastcheck", "wire": rc_wire},
                {"id": 8, "method": "superopt", "wire": rc_wire},
                {"id": 9, "method": "plugins", "wire": rc_wire},
                {"id": 10, "method": "validate-tv", "wire": rc_wire},
                {"id": 11, "method": "verify-certs", "wire": rc_wire},
                {"id": 12, "method": "validate-tv", "wire": rc_wire, "allow_rc_adt": True},
                {"id": 99, "method": "shutdown"},
            ]
            worker_in = "\n".join(json.dumps(r) for r in worker_reqs) + "\n"
            worker_out = subprocess.check_output(
                [core_bin, "worker"], input=worker_in, text=True,
            ).strip().splitlines()
            by_id = {json.loads(line)["id"]: json.loads(line) for line in worker_out}
            for rid in (1, 2, 3, 4, 5, 6, 7, 8, 9, 12):
                self.assertFalse(by_id[rid]["ok"], by_id[rid])
            self.assertTrue(by_id[10]["ok"], by_id[10])
            self.assertTrue(by_id[11]["ok"], by_id[11])


if __name__ == "__main__":
    unittest.main()
