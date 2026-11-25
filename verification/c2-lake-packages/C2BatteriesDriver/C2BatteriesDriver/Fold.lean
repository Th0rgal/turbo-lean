import Batteries.Data.UnionFind.Basic
import Batteries.Data.BitVec

/-! Scalar SWAR popcount/rank kernel for the Tier C2 3-way differential,
compiled against the pinned upstream `leanprover-community/batteries` build.

As in `Scan.lean`, the exported kernels stay scalar; the pinned Batteries
code runs at elaboration time: the `#guard` below pushes eight nodes into a
`Batteries.UnionFind`, unions them along edges derived from the suite's
boundary test vectors (path compression, rank linking), and checks root
agreement on every derived edge. -/

def c2bPopcount (x0 : UInt64) : UInt64 :=
  let m1 : UInt64 := (x0 &&& (0x5555555555555555 : UInt64)) + ((x0 >>> 1) &&& (0x5555555555555555 : UInt64))
  let m2 : UInt64 := (m1 &&& (0x3333333333333333 : UInt64)) + ((m1 >>> 2) &&& (0x3333333333333333 : UInt64))
  let m3 : UInt64 := (m2 + (m2 >>> 4)) &&& (0x0F0F0F0F0F0F0F0F : UInt64)
  (m3 * 0x0101010101010101) >>> 56

def c2bFoldRank (x0 : UInt64) : UInt64 :=
  let p : UInt64 := c2bPopcount x0
  let a : UInt64 := (x0 ^^^ (x0 >>> 33)) * 0xC2B2AE3D27D4EB4F
  let b : UInt64 := a + (p <<< 3) + 0x165667B19E3779F9
  (b ^^^ (b >>> 29)) + (p <<< 56)

#guard c2bPopcount 0 == 0 && c2bPopcount 1 == 1 && c2bPopcount 0xAA == 4 &&
  c2bPopcount 0xFFFFFFFFFFFFFFFF == 64

-- Pinned-Batteries conformance on the Tier C2 boundary vectors
-- (`C2_TEST_VECTORS` in scripts/run_conformance_suite.py).
#guard (let vs : List UInt64 := [0, 1, 42, 0x00000000000000AA, 0x41393A0A7E7D03AA, 0x0123456789ABCDEF, 0x8000000000000001, 0xFFFFFFFFFFFFFFFF]; let uf0 := vs.foldl (fun (u : Batteries.UnionFind) (_ : UInt64) => u.push) Batteries.UnionFind.empty; let uf := vs.foldl (fun (u : Batteries.UnionFind) (v : UInt64) => u.union! (v % 8).toNat ((v >>> 3) % 8).toNat) uf0; vs.all fun (v : UInt64) => uf.rootD (v % 8).toNat == uf.rootD ((v >>> 3) % 8).toNat)
