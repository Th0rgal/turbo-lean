import FV.Clif.Syntax
import LeanNative.Semantics.Eval

/-! Scalar fragment and relations, independent of the historical statement sketch.
`declF` is a syntax filter; executable lowering additionally checks types and scope. -/

namespace B2

open LeanNative.IR LeanNative.Semantics

/-! ## Fragment F₆₄ (syntactic, decidable) -/

/-- Syntactic scalar operators; div/mod use the total safe-denominator lowering. -/
def binOpF : BinOp → Bool
  | .add | .sub | .mul | .div | .mod | .bitAnd | .bitOr | .bitXor
  | .shl | .shr | .sar | .eq | .lt | .le => true
  | _ => false

def unOpF : UnaryOp → Bool
  | .not | .neg => true
  | .clz256 => false

def scalarF : ScalarExpr → Bool
  | .constU64 _ | .constBool _ | .var _ => true
  | .binOp op a b => binOpF op && scalarF a && scalarF b
  | .unaryOp op a => unOpF op && scalarF a
  | .select c t e => scalarF c && scalarF t && scalarF e
  | .fma a b c => scalarF a && scalarF b && scalarF c

def tyF : LNIRType → Bool
  | .i1 | .i64 => true
  | _ => false

/-- F₆₄ code: `letBind` of scalar expressions at `i1`/`i64`, `ite`, `seqFor`, `ret`. No heap,
no RC, no `parFor`, no calls, no 256-bit. -/
def codeF : LNIRCode → Bool
  | .letBind _ ty (.scalar e) k => tyF ty && scalarF e && codeF k
  | .ite _ t e => codeF t && codeF e
  | .seqFor _ _ _ _ _ ty body k => tyF ty && codeF body && codeF k
  | .ret _ => true
  | _ => false

def declF (d : LNIRDecl) : Bool :=
  d.params.all (fun p => tyF p.ty) && tyF d.retTy && codeF d.body

/-! ## Value correspondence (no new semantics: both sides are the repos' own `Val`s) -/

/-- LNIR `u64` ↔ CLIF `i64`, LNIR `bool` ↔ CLIF `i8` 0/1 (CLIF `icmp` result). -/
def ValRel : Val → Clif.Val → Prop
  | .u64 n, v => v = ⟨.i64, n.toBitVec⟩
  | .bool b, v => v = ⟨.i8, if b then 1#8 else 0#8⟩
  | _, _ => False

/-- Pointwise `ValRel` on argument lists (core has no `List.Forall₂`). -/
def ArgsRel (vs : List Val) (cvs : List Clif.Val) : Prop :=
  vs.length = cvs.length ∧ ∀ (i : Nat) v cv, vs[i]? = some v → cvs[i]? = some cv → ValRel v cv

def clifTy : LNIRType → Clif.Ty
  | .i1 => .i8
  | _ => .i64

/-- The LNIR entry state of `d` on argument values `vs`. -/
def entryEnv (d : LNIRDecl) (vs : List Val) : VarEnv :=
  (d.params.zip vs).foldl (fun env (p, v) => env.bind p.id v) VarEnv.empty

/-- Empty LNIR heap (F₆₄ never touches it). -/
def emptyHeap : HeapState := ⟨[], 0, [], []⟩

end B2
