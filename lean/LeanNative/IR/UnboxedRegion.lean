import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Spec
import LeanNative.Backend.TargetIR
import LeanNative.Backend.LLVMAst.Syntax

set_option autoImplicit false

namespace LeanNative.IR

open LeanNative.Backend.TargetIR
open LeanNative.Backend.LLVMAst

/-!
# Track D2: Unboxed Regions, Portable SIMD Layouts & Thread-Local RC Ownership

Header-free `repr(C)` layouts, borrowed byte slices, and portable SIMD vectors.
Lowering emits only scalar, tuple, and raw-buffer LNIR: zero `allocCtor`, `incRef`, and `decRef`.
-/

def regionAlignUp (n a : Nat) : Nat :=
  if a == 0 then n else a * ((n + (a - 1)) / a)

inductive UnboxedScalarKind where
  | u8
  | u16
  | u32
  | u64
  | f32
  | f64
  deriving Repr, DecidableEq, Inhabited, BEq

def UnboxedScalarKind.byteSize (k : UnboxedScalarKind) : Nat :=
  match k with
  | .u8 => 1
  | .u16 => 2
  | .u32 | .f32 => 4
  | .u64 | .f64 => 8

def UnboxedScalarKind.naturalAlign (k : UnboxedScalarKind) : Nat :=
  match k with
  | .u8 => 1
  | .u16 => 2
  | .u32 | .f32 => 4
  | .u64 | .f64 => 8

def UnboxedScalarKind.lnirType (k : UnboxedScalarKind) : LNIRType :=
  match k with
  | .u8 => .i8
  | .u16 => .i16
  | .u32 | .f32 => .i32
  | .u64 | .f64 => .i64

def UnboxedScalarKind.intWidth? (k : UnboxedScalarKind) : Option IntWidth :=
  match k with
  | .u8 => some .i8
  | .u16 => some .i16
  | .u32 => some .i32
  | .u64 => some .i64
  | .f32 | .f64 => none

def UnboxedScalarKind.floatWidth? (k : UnboxedScalarKind) : Option FloatWidth :=
  match k with
  | .f32 => some .f32
  | .f64 => some .f64
  | _ => none

structure UnboxedField where
  name : String
  kind : UnboxedScalarKind
  deriving Repr, DecidableEq, Inhabited, BEq

structure PlacedUnboxedField where
  field  : UnboxedField
  offset : Nat
  size   : Nat
  align  : Nat
  deriving Repr, DecidableEq, Inhabited, BEq

def placeUnboxedField (off : Nat) (f : UnboxedField) : PlacedUnboxedField × Nat :=
  let aligned := regionAlignUp off f.kind.naturalAlign
  ({ field := f, offset := aligned, size := f.kind.byteSize, align := f.kind.naturalAlign },
    aligned + f.kind.byteSize)

def placeUnboxedFieldsFrom (fields : List UnboxedField) (off maxA : Nat) :
    List PlacedUnboxedField × Nat × Nat :=
  match fields with
  | [] => ([], off, maxA)
  | f :: fs =>
    let placed := placeUnboxedField off f
    let rest := placeUnboxedFieldsFrom fs placed.2 (Nat.max maxA f.kind.naturalAlign)
    ⟨placed.1 :: rest.1, rest.2.1, rest.2.2⟩

structure UnboxedStructLayout where
  name        : String
  fields      : List PlacedUnboxedField
  stride      : Nat
  align       : Nat
  headerBytes : Nat
  deriving Repr, DecidableEq, Inhabited, BEq

def mkUnboxedStructLayout (name : String) (fields : List UnboxedField) : UnboxedStructLayout :=
  let placed := placeUnboxedFieldsFrom fields 0 1
  let align := placed.2.2
  { name := name
    fields := placed.1
    stride := regionAlignUp placed.2.1 align
    align := align
    headerBytes := 0 }

def heapObjHeaderBytes : Nat := 8

def unboxedVsHeapHeader (layout : UnboxedStructLayout) : Bool :=
  decide (layout.headerBytes = 0 ∧ layout.headerBytes < heapObjHeaderBytes)

def fieldByteEnd (f : PlacedUnboxedField) : Nat := f.offset + f.size

def layoutFieldsDisjoint (fields : List PlacedUnboxedField) : Bool :=
  match fields with
  | [] => true
  | f :: fs =>
    fs.all (fun g => decide (fieldByteEnd f ≤ g.offset)) && layoutFieldsDisjoint fs

def layoutFieldsAligned (fields : List PlacedUnboxedField) : Bool :=
  fields.all (fun f =>
    decide (0 < f.align) && decide (f.offset % f.align = 0) && decide (f.size = f.align))

def layoutWellFormed (layout : UnboxedStructLayout) : Bool :=
  layout.headerBytes == 0 &&
  decide (0 < layout.align) &&
  decide (layout.stride % layout.align = 0) &&
  layoutFieldsDisjoint layout.fields &&
  layoutFieldsAligned layout.fields &&
  layout.fields.all (fun f => decide (fieldByteEnd f ≤ layout.stride))

inductive RegionOwnership where
  | borrowed
  | threadLocalSingleOwner
  | uniqueSendable
  | sharedMT
  deriving Repr, DecidableEq, Inhabited, BEq

def RegionOwnership.rcMode (own : RegionOwnership) : RcMode :=
  match own with
  | .borrowed | .threadLocalSingleOwner => .freestanding
  | .uniqueSendable => .singleThreaded
  | .sharedMT => .atomic

def RegionOwnership.emitsRc (own : RegionOwnership) : Bool :=
  match own with
  | .borrowed | .threadLocalSingleOwner => false
  | .uniqueSendable | .sharedMT => true

structure BorrowedRegionSlice where
  ptrVar : VarId
  view   : LeanNative.Spec.ByteSliceView
  own    : RegionOwnership
  deriving Repr, DecidableEq, BEq

def borrowedSliceValid (s : BorrowedRegionSlice) : Bool :=
  LeanNative.Spec.isValidByteSlice s.view && (s.own == .borrowed)

def borrowedSliceSub (s : BorrowedRegionSlice) (subOff subLen : Nat) : Option BorrowedRegionSlice :=
  if borrowedSliceValid s && decide (subOff + subLen ≤ s.view.len) then
    some { s with view := LeanNative.Spec.subSliceView s.view subOff subLen }
  else
    none

inductive PortableSimdKind where
  | v2i64
  | v4i64
  | v4f64
  | v16i8
  deriving Repr, DecidableEq, Inhabited, BEq

def PortableSimdKind.lanes (k : PortableSimdKind) : Nat :=
  match k with
  | .v2i64 => 2
  | .v4i64 | .v4f64 => 4
  | .v16i8 => 16

def PortableSimdKind.laneBits (k : PortableSimdKind) : Nat :=
  match k with
  | .v16i8 => 8
  | .v2i64 | .v4i64 | .v4f64 => 64

def PortableSimdKind.laneType (k : PortableSimdKind) : LNIRType :=
  match k with
  | .v16i8 => .i8
  | .v2i64 | .v4i64 => .i64
  | .v4f64 => .f64

def PortableSimdKind.llvmLaneType (k : PortableSimdKind) : LLVMType :=
  match k with
  | .v16i8 => .int .i8
  | .v2i64 | .v4i64 => .int .i64
  | .v4f64 => .float .f64

def PortableSimdKind.llvmType (k : PortableSimdKind) : LLVMType :=
  .vec k.lanes k.llvmLaneType

def PortableSimdKind.bitWidth (k : PortableSimdKind) : Nat :=
  k.lanes * k.laneBits

structure PortableSimdVec where
  kind   : PortableSimdKind
  lanes  : List VarId
  dst    : VarId
  deriving Repr, DecidableEq, Inhabited, BEq

def portableSimdArityOk (v : PortableSimdVec) : Bool :=
  decide (v.lanes.length = v.kind.lanes)

def lowerSimdTuple (v : PortableSimdVec) (k : LNIRCode) : LNIRCode :=
  .letBind v.dst (.tuple (List.replicate v.kind.lanes v.kind.laneType)) (.mkTuple v.lanes) k

def lowerSimdLane (dst tupleVar : VarId) (kind : PortableSimdKind) (lane : Nat) (k : LNIRCode) : LNIRCode :=
  .letBind dst kind.laneType (.projTuple tupleVar lane) k

def lowerBorrowedSliceLoad (dst idxVar posVar : VarId) (s : BorrowedRegionSlice) (k : LNIRCode) : LNIRCode :=
  .letBind posVar .i64 (.scalar (.binOp .add (.constU64 s.view.offset.toUInt64) (.var idxVar)))
    (.letBind dst .i64 (.rawLoad s.ptrVar posVar .i64) k)

def lowerUnboxedFieldLoad (dst baseVar idxVar posVar : VarId) (field : PlacedUnboxedField)
    (k : LNIRCode) : LNIRCode :=
  .letBind posVar .i64
      (.scalar (.binOp .add (.var idxVar) (.constU64 field.offset.toUInt64)))
    (.letBind dst field.field.kind.lnirType (.rawLoad baseVar posVar field.field.kind.lnirType) k)

def codeHasHeapRc (code : LNIRCode) : Bool :=
  match code with
  | .letBind _ _ val k =>
    match val with
    | .allocCtor _ _ _ => true
    | _ => codeHasHeapRc k
  | .incRef _ _ _ | .decRef _ _ _ => true
  | .rawStore _ _ _ _ k => codeHasHeapRc k
  | .ite _ t e => codeHasHeapRc t || codeHasHeapRc e
  | .seqFor _ _ _ _ _ _ step k => codeHasHeapRc step || codeHasHeapRc k
  | .parFor _ _ _ _ _ k => codeHasHeapRc k
  | .ret _ | .unreachable => false

def lowerUnboxedRegionCode (dst posVar idxVar : VarId) (layout : UnboxedStructLayout)
    (slice : BorrowedRegionSlice) (baseVar : VarId) (k : LNIRCode) : LNIRCode :=
  match layout.fields with
  | [] => lowerBorrowedSliceLoad dst idxVar posVar slice k
  | f :: _ => lowerUnboxedFieldLoad dst baseVar idxVar posVar f k

def lowerUnboxedRegionRcFree (dst posVar idxVar : VarId) (layout : UnboxedStructLayout)
    (slice : BorrowedRegionSlice) (baseVar : VarId) : Bool :=
  !(codeHasHeapRc (lowerUnboxedRegionCode dst posVar idxVar layout slice baseVar (.ret dst)))

def exprMentions (v : VarId) (e : LNIRExpr) : Bool :=
  match e with
  | .scalar (.var x) => x == v
  | .scalar (.binOp _ l r) => exprMentions v (.scalar l) || exprMentions v (.scalar r)
  | .scalar (.unaryOp _ a) => exprMentions v (.scalar a)
  | .scalar (.select c t e1) =>
    exprMentions v (.scalar c) || exprMentions v (.scalar t) || exprMentions v (.scalar e1)
  | .scalar (.fma a b c) =>
    exprMentions v (.scalar a) || exprMentions v (.scalar b) || exprMentions v (.scalar c)
  | .mkTuple fs => fs.contains v
  | .allocCtor _ os ss => os.contains v || ss.contains v
  | .call _ args _ _ => args.contains v
  | .projTuple x _ | .ctorGetObj x _ | .ctorGetScalar x _ _ | .isExclusive x | .sarrayLen x => x == v
  | .sarrayDataPtr x _ | .sarrayEnsureExclusive x _ => x == v
  | .sarrayGet a i _ | .rawLoad a i _ => a == v || i == v
  | .sarraySet a i x _ => a == v || i == v || x == v
  | .storageLoad a i => a == v || i == v
  | .storageStore a i x => a == v || i == v || x == v
  | .mulDivDown a b d | .mulDivUp a b d => a == v || b == v || d == v
  | .boxScalar x _ | .unboxScalar x _ => x == v
  | .scalar (.constU64 _) | .scalar (.constBool _) | .constU256 _ => false

def codeEscapes (v : VarId) (code : LNIRCode) : Bool :=
  match code with
  | .letBind dst _ val k =>
    exprMentions v val || (dst != v && codeEscapes v k)
  | .rawStore p i x _ k => p == v || i == v || x == v || codeEscapes v k
  | .incRef x c k => (x == v && 0 < c) || codeEscapes v k
  | .decRef x c k => (x == v && 0 < c) || codeEscapes v k
  | .ite c t e => c == v || codeEscapes v t || codeEscapes v e
  | .seqFor _ lo hi _ init _ step k =>
    lo == v || hi == v || init == v || codeEscapes v step || codeEscapes v k
  | .parFor _ len ins _ _ k => len == v || ins.contains v || codeEscapes v k
  | .ret x => x == v
  | .unreachable => false

def checkThreadLocalNonEscaping (v : VarId) (code : LNIRCode) : Bool :=
  !(codeEscapes v code)

def checkSendableTransfer (v : VarId) (code : LNIRCode) (rc : Nat) : Bool :=
  rc == 1 && !(codeEscapes v code)

def rejectSharedMarkMt (v : VarId) (code : LNIRCode) : Bool :=
  checkThreadLocalNonEscaping v code

def simdLaneGet (vs : List LLVMVal) (i : Nat) : Option LLVMVal :=
  vs[i]?

def simdLaneSet (vs : List LLVMVal) (i : Nat) (elem : LLVMVal) : List LLVMVal :=
  vs.set i elem

def portableSimdWidthPreserved (k : PortableSimdKind) : Bool :=
  decide (k.llvmType.bitSize = k.bitWidth)

end LeanNative.IR
