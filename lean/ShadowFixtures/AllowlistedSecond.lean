import LeanNative.Semantics.Eval

/-! Shadow-semantics fixture: a namespace with one allowlisted violation (`first`) and a SECOND
new violation (`second`). Expected: the self-test allowlist lists only `first`, so the ratchet
must fail on `ShadowFixtureAllowlisted.second → evalUnaryOp`; namespace-level allowlisting is
never enough. -/

namespace ShadowFixtureAllowlisted
open LeanNative.IR LeanNative.Semantics

def first (op : BinOp) (a b : Val) : Except UBError Val := evalBinOp op a b

/-- Two hops away from the evaluator: `second → helper → evalUnaryOp`. -/
def helper (op : UnaryOp) (a : Val) : Except UBError Val := evalUnaryOp op a
def second (a : Val) : Except UBError Val := helper .neg a

end ShadowFixtureAllowlisted
