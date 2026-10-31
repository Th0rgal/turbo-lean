/-! Shadow-semantics fixture: an independent BitVec-only target semantics.
Expected: `check_shadow_semantics` reports no violation for `ShadowFixtureBitVec`. -/

namespace ShadowFixtureBitVec

inductive Op where
  | add | sub | xor
  deriving Repr, DecidableEq

def denote : Op → BitVec 64 → BitVec 64 → BitVec 64
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .xor, a, b => a ^^^ b

structure Reg where
  lo : BitVec 64
  hi : BitVec 64

def Reg.denoteLo (op : Op) (r s : Reg) : BitVec 64 := denote op r.lo s.lo

end ShadowFixtureBitVec
