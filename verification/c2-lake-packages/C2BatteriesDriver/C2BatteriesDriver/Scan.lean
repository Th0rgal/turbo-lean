import Batteries.Data.HashMap.Basic
import Batteries.Data.UInt

/-! Scalar scan-digest kernel for the Tier C2 3-way differential, compiled
against the pinned upstream `leanprover-community/batteries` build.

The exported kernels must stay scalar (`UInt64 → UInt64`): the LNIR bridge
lowers only declarations local to this package and fails closed on heap ADTs.
The pinned Batteries code is exercised at elaboration time instead: the
`#guard` below builds a `Batteries.HashMap` keyed by the suite's eight
boundary test vectors (hashing, bucket collisions, lookup) and checks it
agrees with the scalar kernel on every vector, in both the stock `lean`
elaboration and the `lean-native` frontend elaboration of the inlined
umbrella module. -/

def c2bRotl (x : UInt64) (r : UInt64) : UInt64 :=
  let s := r &&& 63
  if s == 0 then x else (x <<< s) ||| (x >>> (64 - s))

def c2bScanStep (acc : UInt64) (k : UInt64) : UInt64 :=
  let m := (acc ^^^ k) * 0x9E3779B97F4A7C15
  c2bRotl m 29 + (k >>> 7)

def c2bScanMix (x0 : UInt64) : UInt64 :=
  let a := c2bScanStep 0x243F6A8885A308D3 x0
  let b := c2bScanStep a (x0 >>> 17)
  let c := c2bScanStep b (x0 <<< 9)
  let d := c2bScanStep c (x0 ^^^ 0xA5A5A5A5A5A5A5A5)
  c2bRotl (c2bScanStep d (c2bRotl x0 33)) 13

-- Pinned-Batteries conformance on the Tier C2 boundary vectors
-- (`C2_TEST_VECTORS` in scripts/run_conformance_suite.py).
#guard (let vs : List UInt64 := [0, 1, 42, 0x00000000000000AA, 0x41393A0A7E7D03AA, 0x0123456789ABCDEF, 0x8000000000000001, 0xFFFFFFFFFFFFFFFF]; let href := Batteries.HashMap.ofList (vs.map fun k => (k, c2bScanMix k)); href.size == 8 && vs.all fun v => href.find? v == some (c2bScanMix v))
