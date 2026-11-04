import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Spec
import LeanNative.Backend.TargetIR
import LeanNative.Backend.LLVMAst.Syntax
import LeanNative.Backend.LLVMAst.Eval
import LeanNative.Semantics.Value

set_option autoImplicit false

namespace LeanNative.IR

open LeanNative.Backend.TargetIR
open LeanNative.Backend.LLVMAst
open LeanNative.Semantics

/-! Track D2: header-free `repr(C)` layouts, portable SIMD, semantic escape, sendable
ownership, and concrete `LLVMAst` header RC / SIMD / multi-field `ByteMem` lowering. -/

def regionAlignUp (n a : Nat) : Nat :=
  if a == 0 then n else a * ((n + (a - 1)) / a)

inductive UnboxedScalarKind where
  | u8 | u16 | u32 | u64 | f32 | f64
  deriving Repr, DecidableEq, Inhabited, BEq

def UnboxedScalarKind.byteSize (k : UnboxedScalarKind) : Nat :=
  match k with
  | .u8 => 1 | .u16 => 2 | .u32 | .f32 => 4 | .u64 | .f64 => 8

def UnboxedScalarKind.lnirType (k : UnboxedScalarKind) : LNIRType :=
  match k with
  | .u8 => .i8 | .u16 => .i16 | .u32 => .i32 | .u64 => .i64 | .f32 => .f32 | .f64 => .f64

def UnboxedScalarKind.llvmType (k : UnboxedScalarKind) : LLVMType :=
  match k with
  | .u8 => .int .i8 | .u16 => .int .i16 | .u32 => .int .i32 | .u64 => .int .i64
  | .f32 => .float .f32 | .f64 => .float .f64

def fieldValMatchesKind (k : UnboxedScalarKind) (v : LLVMVal) : Bool :=
  match k, v with
  | .u8, .bits .i8 _
  | .u16, .bits .i16 _
  | .u32, .bits .i32 _
  | .u64, .bits .i64 _
  | .f32, .floatBits .f32 _
  | .f64, .floatBits .f64 _ => true
  | _, _ => false

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
  let aligned := regionAlignUp off f.kind.byteSize
  ({ field := f, offset := aligned, size := f.kind.byteSize, align := f.kind.byteSize },
    aligned + f.kind.byteSize)

def placeUnboxedFieldsFrom (fields : List UnboxedField) (off maxA : Nat) :
    List PlacedUnboxedField × Nat × Nat :=
  match fields with
  | [] => ([], off, maxA)
  | f :: fs =>
    let placed := placeUnboxedField off f
    let rest := placeUnboxedFieldsFrom fs placed.2 (Nat.max maxA f.kind.byteSize)
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
    decide (0 < f.align) && decide (f.offset % f.align = 0) &&
    decide (f.size = f.align) && decide (f.size = f.field.kind.byteSize))

def layoutWellFormed (layout : UnboxedStructLayout) : Bool :=
  layout.headerBytes == 0 &&
  decide (0 < layout.align) &&
  decide (layout.stride % layout.align = 0) &&
  layoutFieldsDisjoint layout.fields &&
  layoutFieldsAligned layout.fields &&
  layout.fields.all (fun f => decide (fieldByteEnd f ≤ layout.stride))

inductive RegionOwnership where
  | borrowed | threadLocalSingleOwner | uniqueSendable | sharedMT
  deriving Repr, DecidableEq, Inhabited, BEq

def RegionOwnership.rcMode (own : RegionOwnership) : RcMode :=
  match own with
  | .borrowed | .threadLocalSingleOwner => .freestanding
  | .uniqueSendable => .singleThreaded | .sharedMT => .atomic

def RegionOwnership.emitsRc (own : RegionOwnership) : Bool :=
  match own with
  | .borrowed | .threadLocalSingleOwner => false | .uniqueSendable | .sharedMT => true

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
  else none

inductive PortableSimdKind where
  | v2i64 | v4i64 | v4f64 | v16i8
  deriving Repr, DecidableEq, Inhabited, BEq

def PortableSimdKind.lanes (k : PortableSimdKind) : Nat :=
  match k with | .v2i64 => 2 | .v4i64 | .v4f64 => 4 | .v16i8 => 16

def PortableSimdKind.laneBits (k : PortableSimdKind) : Nat :=
  match k with | .v16i8 => 8 | .v2i64 | .v4i64 | .v4f64 => 64

def PortableSimdKind.laneType (k : PortableSimdKind) : LNIRType :=
  match k with | .v16i8 => .i8 | .v2i64 | .v4i64 => .i64 | .v4f64 => .f64

def PortableSimdKind.llvmLaneType (k : PortableSimdKind) : LLVMType :=
  match k with | .v16i8 => .int .i8 | .v2i64 | .v4i64 => .int .i64 | .v4f64 => .float .f64

def PortableSimdKind.llvmType (k : PortableSimdKind) : LLVMType := .vec k.lanes k.llvmLaneType

def PortableSimdKind.bitWidth (k : PortableSimdKind) : Nat := k.lanes * k.laneBits

def portableSimdWidthPreserved (k : PortableSimdKind) : Bool :=
  decide (k.llvmType.bitSize = k.bitWidth)

def lowerSimdInsertLane (dst : RegName) (kind : PortableSimdKind) (vec elem : Operand)
    (lane : UInt64) : LLVMInstr :=
  .insertelement dst kind.lanes kind.llvmLaneType vec elem .i32
    (.constInt .i32 (BitVec.ofNat 32 lane.toNat))

def lowerSimdExtractLane (dst : RegName) (kind : PortableSimdKind) (vec : Operand)
    (lane : UInt64) : LLVMInstr :=
  .extractelement dst kind.lanes kind.llvmLaneType vec .i32
    (.constInt .i32 (BitVec.ofNat 32 lane.toNat))

def lowerSimdBuildVecAux (dst : RegName) (kind : PortableSimdKind) (idx : Nat) (cur : Operand)
    (elems : List Operand) : List LLVMInstr :=
  match elems with
  | [] => []
  | [e] => [lowerSimdInsertLane dst kind cur e idx.toUInt64]
  | e :: es =>
    let stepReg := s!"{dst}_lane_{idx}"
    lowerSimdInsertLane stepReg kind cur e idx.toUInt64 ::
      lowerSimdBuildVecAux dst kind (idx + 1) (.reg stepReg) es

def lowerSimdBuildVec (dst : RegName) (kind : PortableSimdKind) (elems : List Operand) : List LLVMInstr :=
  lowerSimdBuildVecAux dst kind 0 .constZero elems

def byteOffsetToWord (byteOff : Nat) : Nat := byteOff / 8

def alignedWordIndex (base byteOff : Nat) : Bool :=
  decide (base % 8 = 0 ∧ byteOff % 8 = 0)

def lowerBorrowedSliceLoad (dst idxVar posVar : VarId) (s : BorrowedRegionSlice) (k : LNIRCode) :
    LNIRCode :=
  .letBind posVar .i64
      (.scalar (.binOp .add (.constU64 (byteOffsetToWord s.view.offset).toUInt64)
        (.binOp .shr (.var idxVar) (.constU64 3))))
    (.letBind dst .i64 (.rawLoad s.ptrVar posVar .i64) k)

def lowerUnboxedFieldLoad (dst baseVar idxVar posVar : VarId) (field : PlacedUnboxedField)
    (k : LNIRCode) : LNIRCode :=
  .letBind posVar .i64
      (.scalar (.binOp .add (.binOp .shr (.var idxVar) (.constU64 3))
        (.constU64 (byteOffsetToWord field.offset).toUInt64)))
    (.letBind dst field.field.kind.lnirType (.rawLoad baseVar posVar field.field.kind.lnirType) k)

def lowerUnboxedFieldStore (baseVar idxVar posVar valVar : VarId) (field : PlacedUnboxedField)
    (k : LNIRCode) : LNIRCode :=
  .letBind posVar .i64
      (.scalar (.binOp .add (.binOp .shr (.var idxVar) (.constU64 3))
        (.constU64 (byteOffsetToWord field.offset).toUInt64)))
    (.rawStore baseVar posVar valVar field.field.kind.lnirType k)

def lowerUnboxedStructStore (baseVar idxVar posVar : VarId) (layout : UnboxedStructLayout)
    (valVars : List VarId) (k : LNIRCode) : LNIRCode :=
  (layout.fields.zip valVars).foldr
    (fun (f, valVar) acc => lowerUnboxedFieldStore baseVar idxVar posVar valVar f acc) k

def lowerUnboxedStructLoads (baseVar idxVar posVar : VarId) (layout : UnboxedStructLayout)
    (dstVars : List VarId) (k : LNIRCode) : LNIRCode :=
  (layout.fields.zip dstVars).foldr
    (fun (f, dst) acc => lowerUnboxedFieldLoad dst baseVar idxVar posVar f acc) k

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

def emitLLVMFieldStore (ptrReg : RegName) (base : Operand) (field : PlacedUnboxedField)
    (val : Operand) : List LLVMInstr :=
  [ .getelementptr ptrReg false (.int .i8) base
      [(.i64, .constInt .i64 (BitVec.ofNat 64 field.offset))]
  , .store false field.field.kind.llvmType val (.reg ptrReg) field.align ]

def emitLLVMFieldLoad (dst ptrReg : RegName) (base : Operand) (field : PlacedUnboxedField) :
    List LLVMInstr :=
  [ .getelementptr ptrReg false (.int .i8) base
      [(.i64, .constInt .i64 (BitVec.ofNat 64 field.offset))]
  , .load dst false field.field.kind.llvmType (.reg ptrReg) field.align ]

def emitLLVMStructStore (ptrPrefix : String) (base : Operand) (layout : UnboxedStructLayout)
    (vals : List Operand) : List LLVMInstr :=
  ((layout.fields.zip vals).map fun (f, v) =>
    emitLLVMFieldStore s!"{ptrPrefix}_{f.field.name}_ptr" base f v).flatten

def emitLLVMStructLoads (dstPrefix : String) (base : Operand) (layout : UnboxedStructLayout) : List LLVMInstr :=
  (layout.fields.map fun f =>
    emitLLVMFieldLoad s!"{dstPrefix}_{f.field.name}" s!"{dstPrefix}_{f.field.name}_ptr" base f).flatten

def scalarMentions (aliases : List VarId) (se : ScalarExpr) : Bool :=
  match se with
  | .constU64 _ | .constBool _ => false
  | .var id => aliases.contains id
  | .binOp _ l r => scalarMentions aliases l || scalarMentions aliases r
  | .unaryOp _ a => scalarMentions aliases a
  | .select c t e => scalarMentions aliases c || scalarMentions aliases t || scalarMentions aliases e
  | .fma a b c => scalarMentions aliases a || scalarMentions aliases b || scalarMentions aliases c

def exprMayAlias (aliases : List VarId) (e : LNIRExpr) : Bool :=
  match e with
  | .scalar se => scalarMentions aliases se
  | .unboxScalar boxVar _ => aliases.contains boxVar
  | .call fn args _ isExtern =>
    !isExtern && fn == "lean_native_unbox_u64" && args.any aliases.contains
  | _ => false

def isMarkMtExpr (e : LNIRExpr) : Bool :=
  match e with
  | .call fn _ _ _ => fn == "lean_mark_mt"
  | _ => false

def exprEscapesWith (aliases : List VarId) (e : LNIRExpr) : Bool :=
  match e with
  | .allocCtor _ os ss => os.any aliases.contains || ss.any aliases.contains
  | .mkTuple fs => fs.any aliases.contains
  | .sarraySet _ _ x _ => aliases.contains x
  | .storageStore _ _ x => aliases.contains x
  | .boxScalar x _ => aliases.contains x
  | .call fn args _ isExtern =>
    if fn == "lean_mark_mt" || (!isExtern && (fn == "lean_native_sarray_len" ||
        fn == "lean_native_unbox_u64" || fn == "lean_native_ctor_tag")) then
      false
    else
      args.any aliases.contains
  | _ => false

def exprEscapes (v : VarId) (e : LNIRExpr) : Bool :=
  exprEscapesWith [v] e

def codeEscapesWith (aliases : List VarId) (code : LNIRCode) : Bool :=
  match code with
  | .letBind dst _ val k =>
    if isMarkMtExpr val then
      codeEscapesWith aliases k
    else
      let rest := aliases.filter (· != dst)
      let nextAliases := if exprMayAlias aliases val then dst :: rest else rest
      exprEscapesWith aliases val || codeEscapesWith nextAliases k
  | .rawStore _ _ x _ k => aliases.contains x || codeEscapesWith aliases k
  | .incRef _ _ k | .decRef _ _ k => codeEscapesWith aliases k
  | .ite _ t e => codeEscapesWith aliases t || codeEscapesWith aliases e
  | .seqFor iv _ _ av init _ step k =>
    let stepAliases := aliases.filter (fun x => x != iv && x != av)
    let kAliases := aliases.filter (· != av)
    aliases.contains init || codeEscapesWith stepAliases step || codeEscapesWith kAliases k
  | .parFor ov _ ins _ _ k =>
    ins.any aliases.contains || codeEscapesWith (aliases.filter (· != ov)) k
  | .ret r => aliases.contains r
  | .unreachable => false

def codeEscapes (v : VarId) (code : LNIRCode) : Bool :=
  codeEscapesWith [v] code

def checkThreadLocalNonEscaping (v : VarId) (code : LNIRCode) : Bool :=
  !(codeEscapes v code)

def heapNonCapturing (targetId : Nat) (st : HeapState) : Bool :=
  st.heapObjs.all fun o =>
    !(o.objFields.any (· == .objPtr targetId) || o.scalarFields.any (· == .objPtr targetId))

inductive HeaderRcState where
  | uniqueSingleThreaded | sharedSingleThreaded | multiThreaded
  deriving Repr, DecidableEq, Inhabited, BEq

def classifyHeaderRc (rc : Int) : HeaderRcState :=
  if rc < 0 then .multiThreaded else if rc == 0 then .uniqueSingleThreaded else .sharedSingleThreaded

def readHeaderRcState (m : ByteMem) (hdrAddr : BitVec 64) : Option (Int × HeaderRcState) :=
  (m.loadInt? hdrAddr .i64).map fun word =>
    let rc := bvSigned .i64 word
    (rc, classifyHeaderRc rc)

def emitAtomicRcInc (dst : RegName) (ptr : Operand) : LLVMInstr :=
  .atomicrmw dst .add ptr (.int .i64) (.constInt .i64 1#64) .seqCst 8

def emitAtomicRcDec (dst : RegName) (ptr : Operand) : LLVMInstr :=
  .atomicrmw dst .sub ptr (.int .i64) (.constInt .i64 1#64) .seqCst 8

def emitThreadLocalRcInc (dst tmp : RegName) (ptr : Operand) : List LLVMInstr :=
  [ .load dst false (.int .i64) ptr 8
  , .add tmp .none .i64 (.reg dst) (.constInt .i64 1#64)
  , .store false (.int .i64) (.reg tmp) ptr 8 ]

def emitThreadLocalRcDec (dst tmp : RegName) (ptr : Operand) : List LLVMInstr :=
  [ .load dst false (.int .i64) ptr 8
  , .sub tmp .none .i64 (.reg dst) (.constInt .i64 1#64)
  , .store false (.int .i64) (.reg tmp) ptr 8 ]

def emitMarkMtHeader (dst : RegName) (ptr : Operand) (v : VarId) (code : LNIRCode) :
    List LLVMInstr :=
  if checkThreadLocalNonEscaping v code then []
  else [.atomicrmw dst .xchg ptr (.int .i64) (.constInt .i64 (BitVec.ofInt 64 (-1))) .seqCst 8]

inductive TransferMode where
  | uniqueZeroCopy | sharedMarkedMt
  deriving Repr, DecidableEq, Inhabited, BEq

structure SendableSlot where
  objId     : Nat
  headerRc  : Int
  exclusive : Bool
  mode      : TransferMode
  deriving Repr, DecidableEq, Inhabited, BEq

structure SendableChannelState where
  senderOwned   : List Nat
  inFlight      : List SendableSlot
  receiverOwned : List Nat
  deriving Repr, DecidableEq, Inhabited, BEq

def slotWellFormed (s : SendableSlot) : Bool :=
  match s.mode with
  | .uniqueZeroCopy => s.headerRc == 0 && s.exclusive
  | .sharedMarkedMt => decide (s.headerRc < 0) && !s.exclusive

def idsDisjoint (xs ys : List Nat) : Bool :=
  xs.all (fun x => !(ys.contains x))

def channelDisjoint (ch : SendableChannelState) : Bool :=
  let flightIds := ch.inFlight.map (·.objId)
  idsDisjoint ch.senderOwned flightIds &&
  idsDisjoint ch.senderOwned ch.receiverOwned &&
  idsDisjoint flightIds ch.receiverOwned &&
  ch.inFlight.all slotWellFormed

def sendSlot (ch : SendableChannelState) (objId : Nat) (v : VarId) (code : LNIRCode)
    (hdrRc : Int) (exclusive : Bool) : Option SendableChannelState :=
  if !checkThreadLocalNonEscaping v code || !(ch.senderOwned.contains objId) ||
      ch.inFlight.any (·.objId == objId) || ch.receiverOwned.contains objId then
    none
  else if hdrRc == 0 && exclusive then
    some { ch with
      senderOwned := ch.senderOwned.filter (· != objId)
      inFlight := { objId, headerRc := 0, exclusive := true, mode := .uniqueZeroCopy } :: ch.inFlight }
  else if decide (0 < hdrRc) then
    some { ch with
      senderOwned := ch.senderOwned.filter (· != objId)
      inFlight := { objId, headerRc := -hdrRc, exclusive := false, mode := .sharedMarkedMt } :: ch.inFlight }
  else
    none

def recvSlot (ch : SendableChannelState) (objId : Nat) :
    Option (SendableSlot × SendableChannelState) :=
  match ch.inFlight.find? (·.objId == objId) with
  | none => none
  | some slot =>
    if ch.senderOwned.contains objId || ch.receiverOwned.contains objId then none
    else
      some (slot, { ch with
        inFlight := ch.inFlight.filter (·.objId != objId)
        receiverOwned := objId :: ch.receiverOwned })

end LeanNative.IR
