import LeanNative.IR.Types
import LeanNative.IR.AST

namespace LeanNative.IR

open LeanNative.IR

/-! ## C8 Deliverable 2: Typed Closure Defunctionalization & Multi-Constructor ADT Lowering

Zero `import Lean`, zero nested `where` / `let rec`, strictly top-level structural recursion.

Lowering model (all expressed in existing `LNIRCode` so it evaluates under the locked `evalCode`):
1. A closure is packed as a heap constructor (`.allocCtor`) carrying the captured environment in its
   object slots and the code-pointer index as the constructor tag.
2. Dispatch is a tag-`ite` chain over `.call "lean_native_ctor_tag"` projecting captured fields with
   `.ctorGetObj` before the direct call.
3. A known (statically resolved) closure is specialized to a direct call with the captured fields
   threaded as ordinary arguments (`specializeKnownClosure`).
4. Closure `seqFor` fold/map combinators lower to a bounded `seqFor` whose step body applies the
   closure body to the index and accumulator.
5. Multi-constructor ADTs lower through `.allocCtor` and an exhaustive tag-dispatch `ite` chain
   (`lowerAdtMatch`).
-/

/-- One captured environment field of a closure or ADT payload. -/
structure CapturedField where
  src : VarId
  ty  : LNIRType
  deriving Repr, Inhabited, BEq

/-- A defunctionalized closure: code-pointer index plus the captured environment fields. -/
structure ClosureSpec where
  codeIdx : Nat
  fields  : List CapturedField
  deriving Repr, Inhabited, BEq

/-- One arm of an exhaustive constructor `match`: constructor tag, payload projections, body. -/
structure AdtArm where
  tag     : Nat
  fields  : List CapturedField
  body    : LNIRCode
  deriving Repr, Inhabited, BEq

/-- Pack a closure value: captured fields become object slots, the code-pointer index is the tag. -/
def lowerClosureAlloc (dst : VarId) (cl : ClosureSpec) (k : LNIRCode) : LNIRCode :=
  .letBind dst .objPtr (.allocCtor cl.codeIdx (cl.fields.map (·.src)) []) k

/-- Project the captured object slot `idx` of closure `clVar` into `dst`. -/
def lowerClosureGetField (dst : VarId) (ty : LNIRType) (clVar : VarId) (idx : Nat) (k : LNIRCode) : LNIRCode :=
  .letBind dst ty (.ctorGetObj clVar idx) k

/-- Direct call of a statically known closure: the captured fields are passed as plain arguments. -/
def specializeKnownClosure (dst : VarId) (retTy : LNIRType) (fnName : String)
    (cl : ClosureSpec) (extra : List VarId) (k : LNIRCode) : LNIRCode :=
  .letBind dst retTy (.call fnName (cl.fields.map (·.src) ++ extra) retTy false) k

/-- `seqFor` map/fold combinator over a closure body: `body` is the per-iteration step. -/
def lowerClosureSeqFor (idxVar loVar hiVar accVar accInit : VarId) (accTy : LNIRType)
    (body k : LNIRCode) : LNIRCode :=
  .seqFor idxVar loVar hiVar accVar accInit accTy body k

/-- Allocate one ADT constructor: payload fields are object slots, `tag` selects the constructor. -/
def lowerAdtCtor (dst : VarId) (tag : Nat) (fields : List VarId) (k : LNIRCode) : LNIRCode :=
  .letBind dst .objPtr (.allocCtor tag fields []) k

/-- Bind the payload projections of one constructor arm before its body. -/
def bindAdtFields (fields : List CapturedField) (src : VarId) (idx : Nat) (k : LNIRCode) : LNIRCode :=
  match fields with
  | [] => k
  | f :: fs => .letBind f.src f.ty (.ctorGetObj src idx) (bindAdtFields fs src (idx + 1) k)

/-- Exhaustive tag-dispatch `match` over ADT `scrutinee` as a nested `ite` chain on its tag.
    `tagVar` receives the tag; each arm's projections are bound immediately before its body.
    `condBase` is the first fresh variable used for the per-arm comparison results. -/
def lowerAdtMatchArms (scrutinee tagVar : VarId) (condBase : VarId)
    (arms : List AdtArm) (fallback : LNIRCode) : LNIRCode :=
  match arms with
  | [] => fallback
  | arm :: rest =>
    let cond := condBase
    let thenB := bindAdtFields arm.fields scrutinee 0 arm.body
    .letBind cond .i1 (.scalar (.binOp .eq (.var tagVar) (.constU64 arm.tag.toUInt64)))
      (.ite cond thenB (lowerAdtMatchArms scrutinee tagVar (condBase + 1) rest fallback))

/-- Full ADT `match`: read the constructor tag, then dispatch. -/
def lowerAdtMatch (scrutinee tagVar : VarId) (condBase : VarId)
    (arms : List AdtArm) (fallback : LNIRCode) : LNIRCode :=
  .letBind tagVar .i64 (.call "lean_native_ctor_tag" [scrutinee] .i64 false)
    (lowerAdtMatchArms scrutinee tagVar condBase arms fallback)

/-- Tag-dispatch table for a closure: identical shape to ADT match, one arm per code pointer. -/
def lowerClosureDispatch (clVar tagVar : VarId) (condBase : VarId)
    (arms : List AdtArm) (fallback : LNIRCode) : LNIRCode :=
  lowerAdtMatch clVar tagVar condBase arms fallback

end LeanNative.IR
