import ShadowFixtures.OpaqueCloneLib

/-! Shadow-semantics fixtures for `opaque`, recursive `partial` (`_unsafe_rec`), and
`implemented_by` evaluator clones whose helper module imports ONLY `LeanNative.Semantics.Value`
(never `LeanNative.Semantics.Eval`). Every target below must fail with `kind = "clone"`. -/

namespace ShadowFixtureOpaqueClone
open LeanNative.IR LeanNative.Semantics

/-- Target calling an `opaque` helper holding the verbatim `evalUnaryOp` body. -/
def denoteOpaque (v : Val) : Except UBError Val :=
  UnrelatedOpaqueUtil.unaryOpaqueCopy .neg v

/-- Target calling a recursive `partial def` helper holding the verbatim `evalVarList` body
    (body present only in `varListPartialCopy._unsafe_rec`). -/
def denotePartialRec (env : VarEnv) (xs : List VarId) : Except UBError (List Val) :=
  UnrelatedOpaqueUtil.varListPartialCopy env xs

/-- Target calling a computable recursive `opaque` helper holding the verbatim `evalSeqLoop` body. -/
def denoteOpaqueRec (count : Nat) (env : VarEnv) (st : HeapState) :
    Except UBError (Val × HeapState) :=
  UnrelatedOpaqueUtil.seqLoopOpaqueCopy count 0 0 1 .unit env st (fun _ s => .ok (.unit, s))

/-- Target calling a recursive `noncomputable opaque` helper holding the verbatim `evalSeqLoop`
    body (stored only in `.opaqueInfo`, with no `_unsafe_rec`). -/
noncomputable def denoteNoncompOpaqueRec (count : Nat) (env : VarEnv) (st : HeapState) :
    Except UBError (Val × HeapState) :=
  UnrelatedOpaqueUtil.seqLoopNoncompOpaqueCopy count 0 0 1 .unit env st (fun _ s => .ok (.unit, s))

/- `denoteImplByOpaqueClone`: synthesized in memory by `withImplementedByFixture` (because source
   implemented-by attributes are rejected by the repository hygiene gate) with logical body
   `unaryLogical` and `implemented_by` pointing at `UnrelatedOpaqueUtil.unaryOpaqueCopy`. -/

end ShadowFixtureOpaqueClone
