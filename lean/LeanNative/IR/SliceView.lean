import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Spec

namespace LeanNative.IR

open LeanNative.Semantics

/-! ## C8 Deliverable 3: Zero-Copy `ByteArraySlice` & `FloatArraySlice` Views

Links LNIR slice views directly to `LeanNative.Spec.{ByteSliceView, isValidByteSlice, subSliceView}`
and lowers bounds-checked reads, sub-slicing, and fold reductions into zero-copy `.sarrayGet` /
`.rawLoad` / `.seqFor` code without allocating intermediate backing buffers.
-/

/-- Element flavor of a typed zero-copy slice view (`ByteArraySlice` vs `FloatArraySlice`). -/
inductive SliceElemKind where
  | byteSlice
  | floatSlice
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Map a `SliceElemKind` to its LNIR element type (`.i8` for bytes, `.f64` for 64-bit floats). -/
def SliceElemKind.lnirType : SliceElemKind → LNIRType
  | .byteSlice => .i8
  | .floatSlice => .f64

/-- Typed zero-copy slice descriptor `(arrVar, kind, view)` over a backing `ArrayBuffer`. -/
structure TypedSliceView where
  arrVar : VarId
  kind   : SliceElemKind
  view   : LeanNative.Spec.ByteSliceView
  deriving Repr, DecidableEq, BEq

/-- Construct a `ByteArraySlice` view `(offset, len)` inside `backingLen`. -/
def mkByteArraySlice (arrVar : VarId) (backingLen offset len : Nat) : TypedSliceView :=
  { arrVar := arrVar, kind := .byteSlice,
    view := { backingLen := backingLen, offset := offset, len := len } }

/-- Construct a `FloatArraySlice` view `(offset, len)` inside `backingLen` (UInt64 IEEE-754 words). -/
def mkFloatArraySlice (arrVar : VarId) (backingLen offset len : Nat) : TypedSliceView :=
  { arrVar := arrVar, kind := .floatSlice,
    view := { backingLen := backingLen, offset := offset, len := len } }

/-- Checked bounds gate linking `TypedSliceView` directly to `LeanNative.Spec.isValidByteSlice`. -/
def checkSliceViewValid (s : TypedSliceView) : Bool :=
  LeanNative.Spec.isValidByteSlice s.view

/-- Checked sub-slice gate: returns `some subSlice` iff both parent and `[subOff, subOff + subLen)` are valid. -/
def checkedSubSlice (s : TypedSliceView) (subOff subLen : Nat) : Option TypedSliceView :=
  if LeanNative.Spec.isValidByteSlice s.view && decide (subOff + subLen ≤ s.view.len) then
    some { s with view := LeanNative.Spec.subSliceView s.view subOff subLen }
  else
    none

/-- Pure model of summing `len` width-masked elements starting at `offset` in `data` (left-to-right). -/
def sumSliceFrom (elemTy : LNIRType) (data : Array UInt64) (curIdx : Nat) (acc : UInt64) : Nat → UInt64
  | 0 => acc
  | n + 1 =>
    let cur := if h : curIdx < data.size then maskElemVal elemTy data[curIdx] else 0
    sumSliceFrom elemTy data (curIdx + 1) (acc + cur) n

/-- Lower a zero-copy indexed read `s[idxVar]` to `posTmp := offset + idxVar; dst := sarrayGet arr posTmp`. -/
def lowerSliceGet (dst posTmp : VarId) (s : TypedSliceView) (idxVar : VarId) (k : LNIRCode) : LNIRCode :=
  .letBind posTmp .i64 (.scalar (.binOp .add (.constU64 s.view.offset.toUInt64) (.var idxVar)))
    (.letBind dst s.kind.lnirType (.sarrayGet s.arrVar posTmp s.kind.lnirType) k)

/-- Lower a zero-copy raw pointer load `rawLoad arr (offset + idxVar)` without copying the backing buffer. -/
def lowerSliceRawLoad (dst posTmp : VarId) (s : TypedSliceView) (idxVar : VarId) (k : LNIRCode) : LNIRCode :=
  .letBind posTmp .i64 (.scalar (.binOp .add (.constU64 s.view.offset.toUInt64) (.var idxVar)))
    (.letBind dst s.kind.lnirType (.rawLoad s.arrVar posTmp s.kind.lnirType) k)

/-- Step body of `lowerSliceFold` at relative index `idxVar` with running accumulator `accVar`. -/
def sliceFoldStep (s : TypedSliceView) (idxVar accVar posTmp elemTmp nextAcc : VarId) : LNIRCode :=
  .letBind posTmp .i64 (.scalar (.binOp .add (.constU64 s.view.offset.toUInt64) (.var idxVar)))
    (.letBind elemTmp s.kind.lnirType (.sarrayGet s.arrVar posTmp s.kind.lnirType)
      (.letBind nextAcc .i64 (.scalar (.binOp .add (.var accVar) (.var elemTmp)))
        (.ret nextAcc)))

/-- Lower a zero-copy additive fold reduction over `s` starting from `initVal` using `seqFor` over `[0, len)`.
    Allocates zero `ArrayBuffer`s (`st.nextId` and `st.buffers` are preserved identically). -/
def lowerSliceFold (s : TypedSliceView) (initVal : UInt64)
    (loVar hiVar initVar idxVar accVar posTmp elemTmp nextAcc : VarId) (k : LNIRCode) : LNIRCode :=
  .letBind loVar .i64 (.scalar (.constU64 0))
    (.letBind hiVar .i64 (.scalar (.constU64 s.view.len.toUInt64))
      (.letBind initVar .i64 (.scalar (.constU64 initVal))
        (.seqFor idxVar loVar hiVar accVar initVar .i64
          (sliceFoldStep s idxVar accVar posTmp elemTmp nextAcc)
          k)))

end LeanNative.IR
