import LeanNative.Semantics.Eval

/-! Shadow-semantics fixture (helper module, NOT inventoried): a verbatim copy of
`LeanNative.Semantics.evalUnaryOp` in an unrelated module and namespace. It is not a target
itself; `ShadowFixtureHelperClone.denote` (HelperClone.lean) calls it. -/

namespace UnrelatedUtil
open LeanNative.IR LeanNative.Semantics

def unaryCopy (op : UnaryOp) (v : Val) : Except UBError Val :=
  match op, v with
  | .not, .bool b   => .ok (.bool (!b))
  | .not, .u64 n    => .ok (.u64 (~~~n))
  | .not, .u256 w   => .ok (.u256 (UInt256.bitNot w))
  | .neg, .u64 n    => .ok (.u64 (0 - n))
  | .neg, .u256 w   => .ok (.u256 (UInt256.sub UInt256.zero w))
  | .clz256, .u256 w => .ok (.u256 (UInt256.clz w))
  | .clz256, .u64 n  => .ok (.u256 (UInt256.clz (UInt256.ofUInt64 n)))
  | _, _ => .error (.typeError "evalUnaryOp: invalid operand type")

end UnrelatedUtil
