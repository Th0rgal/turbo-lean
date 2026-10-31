import ShadowFixtures.TraversalLib

/-! Shadow-semantics traversal fixtures. Every target below references NO forbidden constant in its
own source text except through the stated traversal class; the self-test asserts the exact
(target, forbidden evaluator, kind) triple for each. -/

namespace ShadowFixtureTraversal
open LeanNative.IR LeanNative.Semantics UnrelatedTraversal

/-- call∞ through > 3 hops: `deep → h1 → h2 → h3 → h4 → evalBinOp` (5 hops). -/
def deep (a b : Val) : Except UBError Val := h1 a b

/-- Synthesized instance: `Denote.den` resolves to `instDenoteBinOp`, which calls `evalBinOp`. -/
def viaInstance (a b : Val) : Except UBError Val := Denote.den BinOp.add a b

/- `implemented_by` (`viaImplementedBy`): synthesized in the imported environment by the
   self-test (see `UnrelatedTraversal.unaryImpl`), because a source implemented-by attribute is rejected
   by the repository hygiene gate. -/

/-- Macro-expanded call: `shadow_add!` expands to `evalBinOp .add`. -/
def viaMacro (a b : Val) : Except UBError Val := shadow_add! a b

/-- `partial def`: the declaration itself is opaque; the body (and the `evalUnaryOp` call)
    lives only in the `_unsafe_rec` auxiliary. -/
partial def viaUnsafeRec (n : Nat) (v : Val) : Except UBError Val :=
  if n = 0 then evalUnaryOp .neg v else viaUnsafeRec (n - 1) v

/-- Proof auxiliary: the only `evalBinOp` mention is inside a nested proof, abstracted by the
    elaborator into `viaProofAux.proof_1`. -/
def viaProofAux (n : Nat) : Fin (n + 1) :=
  ⟨0, by
    have _h : evalBinOp .add (.u64 0) (.u64 0) = evalBinOp .add (.u64 0) (.u64 0) := rfl
    omega⟩

/-- Inductive / constructor / recursor: the target mentions only the inductive `AddsTo`; the
    forbidden constant is reached through `AddsTo`'s constructor and recursor types. (A
    `RecursorRule.rhs` only mentions the recursor itself and bound variables, so no violation can
    be reachable through recursor rules ALONE; the rules are still traversed.) -/
def viaInductive (a b : Val) (_h : AddsTo a b) : Nat := 0

/-- Matcher auxiliary: the generated `viaMatcher.match_1` mentions `evalBinOp` (the `mk`
    alternative binds the proof field). The elaborated body also mentions it in the alternative's
    binder type, so this fixture checks detection, not path isolation; the isolated-auxiliary
    cases are `viaUnsafeRec` (`_unsafe_rec` only) and `viaProofAux` (`_proof_n` only). -/
def viaMatcher (w : AddsToT) : Val :=
  match w with
  | .mk a _ _ => a

end ShadowFixtureTraversal
