import ShadowFixtures.HelperCloneLib

/-! Shadow-semantics fixture: a target that references no forbidden constant but calls a verbatim
copy of `evalUnaryOp` living in an unrelated, un-inventoried module / namespace
(`UnrelatedUtil.unaryCopy`). Expected: `ShadowFixtureHelperClone.denote → evalUnaryOp (clone)`. -/

namespace ShadowFixtureHelperClone
open LeanNative.IR LeanNative.Semantics

def denote (v : Val) : Except UBError Val := UnrelatedUtil.unaryCopy .neg v

end ShadowFixtureHelperClone
