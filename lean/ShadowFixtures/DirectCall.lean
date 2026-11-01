import LeanNative.Semantics.Eval

/-! Shadow-semantics fixture: a "target" semantics that calls the source evaluator directly.
Expected: `check_shadow_semantics` reports `ShadowFixtureDirect.denote → evalBinOp (call≤3)`. -/

namespace ShadowFixtureDirect
open LeanNative.IR LeanNative.Semantics

def denote (op : BinOp) (a b : Val) : Except UBError Val := evalBinOp op a b

end ShadowFixtureDirect
