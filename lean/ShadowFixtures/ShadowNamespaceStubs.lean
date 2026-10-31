/-! Shadow-semantics negative fixtures for banned local shadow/stub namespaces (`ConLeche`,
`LCNF`, `LeanMLIR`, `LNSym`) outside their pinned grandfather modules (and specifically inside
`lean/LeanNative/Proofs/`), including the two reward-hacking stubs from Contract V1–V3:
1. Toy `ConLeche.CICValid` asserting syntactic equality (`d.ty = d.val`).
2. Size-only `ConLeche.parseOleanShard` returning an empty `decls := []` list.
3. Local `LCNF` / `LeanMLIR` / `LNSym` shadow definitions referencing no `eval*` constants.

None of these mention `LeanNative.Semantics.eval*`, so reachability / clone checks alone would
pass; the declaration-origin check must flag every one as `shadow-origin`. -/

namespace ShadowFixtureOrigin

namespace ConLeche

structure Expr where
  tag : Nat
  deriving DecidableEq

structure Decl where
  name : String
  wfTag : Bool
  ty : Expr
  val : Expr

structure Env where
  decls : List Decl
  headerMagic : UInt32

def CICValid (_env : Env) (d : Decl) : Prop :=
  d.wfTag = true ∧ d.ty = d.val

def parseOleanShard (bytes : ByteArray) : Except String Env :=
  if bytes.size >= 4 then .ok { decls := [], headerMagic := 0x4F4C454E } else .error "bad"

theorem verify_toy_sound (env : Env) (d : Decl) (h : d.wfTag = true ∧ d.ty = d.val) :
    CICValid env d := h

theorem olean_toy_sound (bytes : ByteArray) (env : Env)
    (h : parseOleanShard bytes = .ok env) : bytes.size >= 4 := by
  unfold parseOleanShard at h
  split at h <;> simp_all

private def _privateToyStub : Prop := True

end ConLeche

namespace LCNF
def evalToy (x : Nat) : Nat := x
end LCNF

namespace LeanMLIR
def denoteToy (x : BitVec 64) : BitVec 64 := x
end LeanMLIR

namespace LNSym
def stepToy (x : BitVec 128) : BitVec 128 := x
end LNSym

end ShadowFixtureOrigin
