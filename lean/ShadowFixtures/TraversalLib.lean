import LeanNative.Semantics.Eval

/-! Shadow-semantics fixture helpers (NOT inventoried: namespace `UnrelatedTraversal`). Each
helper is only reachable from a `ShadowFixtureTraversal` target through one traversal class. -/

namespace UnrelatedTraversal
open LeanNative.IR LeanNative.Semantics

/-! call∞: a 4-helper chain, so `target → h1 → h2 → h3 → h4 → evalBinOp` is 5 hops. -/
def h4 (a b : Val) : Except UBError Val := evalBinOp .add a b
def h3 (a b : Val) : Except UBError Val := h4 a b
def h2 (a b : Val) : Except UBError Val := h3 a b
def h1 (a b : Val) : Except UBError Val := h2 a b

/-! Synthesized instance: the target only mentions the class method; instance resolution
inserts `instDenoteBinOp`, whose body calls `evalBinOp`. -/
class Denote (α : Type) where
  den : α → Val → Val → Except UBError Val

instance : Denote BinOp where
  den := evalBinOp

/-! `implemented_by`: the compiled implementation calls `evalUnaryOp`; the logical body does not. -/
def unaryImpl (op : UnaryOp) (v : Val) : Except UBError Val := evalUnaryOp op v

/-! Macro: expands to a call of `evalBinOp` at the use site. -/
macro "shadow_add!" a:term:max b:term:max : term =>
  `(LeanNative.Semantics.evalBinOp LeanNative.IR.BinOp.add $a $b)

/-! Recursor rules: an inductive whose constructor field type mentions `evalBinOp`. -/
inductive AddsTo : Val → Val → Prop where
  | mk (a b : Val) : evalBinOp .add a b = .ok b → AddsTo a b

/-- Data-carrying variant (eliminates into `Type`, so `match` on it generates a matcher). -/
inductive AddsToT : Type where
  | mk (a b : Val) (h : evalBinOp .add a b = .ok b) : AddsToT

end UnrelatedTraversal
