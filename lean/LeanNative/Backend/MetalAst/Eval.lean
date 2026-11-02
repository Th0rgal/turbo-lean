import LeanNative.Backend.MetalAst.Syntax

namespace LeanNative.Backend.MetalAst

/-! ## Independent SIMT Threadgroup Operational Semantics -/

/-- 3D grid or threadgroup dimensions / coordinates. -/
structure Dim3 where
  x : Nat := 1
  y : Nat := 1
  z : Nat := 1
  deriving Repr, DecidableEq, Inhabited, BEq

namespace Dim3

def coords (d : Dim3) : List Dim3 :=
  (List.range d.z).flatMap fun z =>
    (List.range d.y).flatMap fun y =>
      (List.range d.x).map fun x => { x, y, z }

end Dim3

/-- Byte-addressed bounded memory buffer backing `device`, `constant`, and `threadgroup` storage. -/
structure ByteMemory where
  bytes : Array UInt8
  deriving Repr, DecidableEq, Inhabited, BEq

namespace ByteMemory

def zeros (numBytes : Nat) : ByteMemory :=
  { bytes := Array.replicate numBytes 0 }

def size (m : ByteMemory) : Nat :=
  m.bytes.size

def readLEAux (m : ByteMemory) (addr : Nat) : Nat → Option (BitVec 64)
  | 0 => some 0#64
  | k + 1 =>
    match m.bytes[addr + k]?, readLEAux m addr k with
    | some b, some rest =>
      some (rest ||| (BitVec.ofNat 64 b.toNat <<< (k * 8)))
    | _, _ => none

/-- Bounds-checked little-endian load of `width` bytes. -/
def loadBits (m : ByteMemory) (addr width : Nat) : Option (BitVec 64) :=
  if width > 0 && addr + width ≤ m.bytes.size then
    readLEAux m addr width
  else
    none

def writeLEAux (bs : Array UInt8) (addr : Nat) (val : BitVec 64) : Nat → Array UInt8
  | 0 => bs
  | k + 1 =>
    let b : UInt8 := UInt8.ofNat ((val >>> (k * 8)).toNat % 256)
    writeLEAux (bs.setIfInBounds (addr + k) b) addr val k

/-- Bounds-checked little-endian store of `width` bytes. -/
def storeBits (m : ByteMemory) (addr width : Nat) (val : BitVec 64) : Option ByteMemory :=
  if width > 0 && addr + width ≤ m.bytes.size then
    some { bytes := writeLEAux m.bytes addr val width }
  else
    none

def fillU64Words (bs : Array UInt8) (idx : Nat) : List (BitVec 64) → Array UInt8
  | [] => bs
  | w :: rest => fillU64Words (writeLEAux bs (idx * 8) w 8) (idx + 1) rest

/-- Build a `ByteMemory` from a list of 64-bit little-endian words. -/
def ofU64Words (words : List (BitVec 64)) : ByteMemory :=
  let empty := Array.replicate (words.length * 8) (0 : UInt8)
  { bytes := fillU64Words empty 0 words }

/-- Read a 64-bit little-endian word at element index `elemIdx`. -/
def readU64Word? (m : ByteMemory) (elemIdx : Nat) : Option (BitVec 64) :=
  m.loadBits (elemIdx * 8) 8

def fillU32Words (bs : Array UInt8) (idx : Nat) : List (BitVec 32) → Array UInt8
  | [] => bs
  | w :: rest => fillU32Words (writeLEAux bs (idx * 4) (BitVec.setWidth 64 w) 4) (idx + 1) rest

/-- Build a `ByteMemory` from a list of 32-bit little-endian words. -/
def ofU32Words (words : List (BitVec 32)) : ByteMemory :=
  let empty := Array.replicate (words.length * 4) (0 : UInt8)
  { bytes := fillU32Words empty 0 words }

/-- Read a 32-bit little-endian word at element index `elemIdx`. -/
def readU32Word? (m : ByteMemory) (elemIdx : Nat) : Option (BitVec 32) :=
  (m.loadBits (elemIdx * 4) 4).map (BitVec.setWidth 32)

def fillU16Words (bs : Array UInt8) (idx : Nat) : List (BitVec 16) → Array UInt8
  | [] => bs
  | w :: rest => fillU16Words (writeLEAux bs (idx * 2) (BitVec.setWidth 64 w) 2) (idx + 1) rest

/-- Build a `ByteMemory` from a list of 16-bit little-endian words (such as IEEE-754 `half`). -/
def ofU16Words (words : List (BitVec 16)) : ByteMemory :=
  let empty := Array.replicate (words.length * 2) (0 : UInt8)
  { bytes := fillU16Words empty 0 words }

/-- Read a 16-bit little-endian word at element index `elemIdx`. -/
def readU16Word? (m : ByteMemory) (elemIdx : Nat) : Option (BitVec 16) :=
  (m.loadBits (elemIdx * 2) 2).map (BitVec.setWidth 16)

end ByteMemory

/-- One lane of a thread-local fixed-size array (`T arr[N]`). -/
structure MSLLocalSlot where
  value  : BitVec 64
  fields : List (String × BitVec 64) := []
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Per-thread local variable environment (`thread` address space) storing typed values,
    multi-word struct/vector fields (`name.field`), and fixed-size thread arrays. -/
structure MSLLocals where
  vars   : List (String × BitVec 64) := []
  types  : List (String × MSLType) := []
  fields : List (String × BitVec 64) := []
  arrays : List (String × List MSLLocalSlot) := []
  deriving Repr, DecidableEq, Inhabited, BEq

namespace MSLLocals

def empty : MSLLocals := { vars := [], types := [], fields := [], arrays := [] }

def lookup? (ls : MSLLocals) (name : String) : Option (BitVec 64) :=
  ls.vars.lookup name

def lookupType? (ls : MSLLocals) (name : String) : Option MSLType :=
  ls.types.lookup name

def lookupField? (ls : MSLLocals) (varName fieldName : String) : Option (BitVec 64) :=
  ls.fields.lookup (varName ++ "." ++ fieldName)

def lookupArray? (ls : MSLLocals) (name : String) : Option (List MSLLocalSlot) :=
  ls.arrays.lookup name

def setAssoc : List (String × BitVec 64) → String → BitVec 64 → List (String × BitVec 64)
  | [], k, v => [(k, v)]
  | (k', v') :: rest, k, v =>
    if k' == k then (k, v) :: rest else (k', v') :: setAssoc rest k v

def setTypeAssoc : List (String × MSLType) → String → MSLType → List (String × MSLType)
  | [], k, t => [(k, t)]
  | (k', t') :: rest, k, t =>
    if k' == k then (k, t) :: rest else (k', t') :: setTypeAssoc rest k t

def setArrayAssoc : List (String × List MSLLocalSlot) → String → List MSLLocalSlot →
    List (String × List MSLLocalSlot)
  | [], k, v => [(k, v)]
  | (k', v') :: rest, k, v =>
    if k' == k then (k, v) :: rest else (k', v') :: setArrayAssoc rest k v

def set (ls : MSLLocals) (name : String) (v : BitVec 64) : MSLLocals :=
  { ls with vars := setAssoc ls.vars name v }

def setTyped (ls : MSLLocals) (name : String) (ty : MSLType) (v : BitVec 64) : MSLLocals :=
  { ls with
    vars := setAssoc ls.vars name v
    types := setTypeAssoc ls.types name ty }

def setField (ls : MSLLocals) (varName fieldName : String) (v : BitVec 64) : MSLLocals :=
  { ls with fields := setAssoc ls.fields (varName ++ "." ++ fieldName) v }

def setArray (ls : MSLLocals) (name : String) (slots : List MSLLocalSlot) : MSLLocals :=
  { ls with arrays := setArrayAssoc ls.arrays name slots }

end MSLLocals

/-- Classification of kernel-scoped buffer and shared-array identifiers. -/
inductive MSLBufferBinding where
  | deviceBuf      : Nat → Bool → MSLType → MSLBufferBinding
  | constantBuf    : Nat → MSLType → MSLBufferBinding
  | constantScalar : Nat → MSLType → MSLBufferBinding
  | threadgroupArr : String → MSLType → MSLBufferBinding
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Memory object identity used for barrier-epoch data-race tracking.
    Distinct `device` buffer indices and distinct `threadgroup` array names do not alias. -/
inductive MSLMemTarget where
  | deviceBuf      : Nat → MSLMemTarget
  | threadgroupArr : String → MSLMemTarget
  deriving Repr, DecidableEq, Inhabited, BEq

/-- One per-thread byte access recorded inside the current barrier epoch. -/
structure MSLAccess where
  tid      : Dim3
  target   : MSLMemTarget
  addr     : Nat
  width    : Nat
  isWrite  : Bool
  isAtomic : Bool := false
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Explicit operational outcome of MSL SIMT execution. -/
inductive MSLOutcome (α : Type) where
  | ok                  : α → MSLOutcome α
  | readOnlyViolation   : String → Nat → MSLOutcome α
  | barrierDivergence   : MSLOutcome α
  | divisionByZero      : MSLOutcome α
  | signedDivOverflow   : MSLOutcome α
  | shiftOutOfRange     : MSLOutcome α
  | dataRace            : MSLAddressSpace → Nat → MSLOutcome α
  | unsupportedFloatOp  : String → MSLOutcome α
  | outOfBoundsLoad     : MSLAddressSpace → Nat → Nat → MSLOutcome α
  | outOfBoundsWrite    : MSLAddressSpace → Nat → Nat → MSLOutcome α
  | unboundIdentifier   : String → MSLOutcome α
  | fuelExhausted       : MSLOutcome α
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Per-lane execution state inside a Metal threadgroup. -/
structure MSLThreadState where
  tid    : Dim3
  locals : MSLLocals := MSLLocals.empty
  stmts  : List MSLStmt := []
  retVal : Option (BitVec 64) := none
  halted : Bool := false
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Complete SIMT threadgroup execution state with separated `device`, `constant`, and
    `threadgroup` memory tables, helper function declarations, struct definitions, and
    per-epoch data-race tracking. -/
structure MSLGroupState where
  gridDim           : Dim3
  groupDim          : Dim3
  groupId           : Dim3
  structs           : List MSLStructDecl := []
  funcs             : List MSLFuncDecl := []
  bindings          : List (String × MSLBufferBinding) := []
  deviceBuffers     : List (Nat × ByteMemory) := []
  constantBuffers   : List (Nat × ByteMemory) := []
  threadgroupArrays : List (String × ByteMemory) := []
  epochLog          : List MSLAccess := []
  threads           : List MSLThreadState := []
  fuelBudget        : Nat := 0
  deriving Repr, DecidableEq, Inhabited, BEq

/-- True when two half-open byte ranges overlap. -/
def rangesOverlap (a1 w1 a2 w2 : Nat) : Bool :=
  decide (a1 < a2 + w2 ∧ a2 < a1 + w1)

/-- Scan an epoch log for an unsynchronized cross-thread conflicting access on the same memory
    object. Two atomic accesses never race with each other; an atomic access still races with a
    non-atomic access. -/
def findDataRaceGo (tid : Dim3) (tgt : MSLMemTarget) (addr width : Nat)
    (isWrite isAtomic : Bool) : List MSLAccess → Option Nat
  | [] => none
  | a :: rest =>
    if (tid != a.tid) && (tgt == a.target) &&
        (isWrite || a.isWrite) && !(isAtomic && a.isAtomic) &&
        rangesOverlap addr width a.addr a.width then
      some (Nat.max addr a.addr)
    else
      findDataRaceGo tid tgt addr width isWrite isAtomic rest

def findDataRace? (log : List MSLAccess) (tid : Dim3) (tgt : MSLMemTarget)
    (addr width : Nat) (isWrite isAtomic : Bool) : Option Nat :=
  findDataRaceGo tid tgt addr width isWrite isAtomic log

/-- Record one epoch access, trapping with `.dataRace` on a conflicting prior access. -/
def recordEpochAccess (log : List MSLAccess) (tid : Dim3) (tgt : MSLMemTarget)
    (sp : MSLAddressSpace) (addr width : Nat) (isWrite : Bool)
    (isAtomic : Bool := false) : MSLOutcome (List MSLAccess) :=
  match findDataRace? log tid tgt addr width isWrite isAtomic with
  | some conflictAddr => .dataRace sp conflictAddr
  | none => .ok ({ tid, target := tgt, addr, width, isWrite, isAtomic } :: log)

/-- Canonical width mask for an MSL scalar type over `BitVec 64`. -/
def maskForType (ty : MSLType) (v : BitVec 64) : BitVec 64 :=
  match ty with
  | .void => 0#64
  | .bool => if v != 0#64 then 1#64 else 0#64
  | .uchar => v &&& 0xFF#64
  | .ushort | .half => v &&& 0xFFFF#64
  | .uint | .int | .float | .atomicUint => v &&& 0xFFFF_FFFF#64
  | .ulong | .long | .double | .uint2 | .uint3 | .uint4 | .ulong2
  | .u256 | .pointer _ _ _ | .ref _ _ | .threadArr _ _ _ | .structTy _ => v

/-- Sign-extend a value whose low `bits` bits are significant into `BitVec 64`. -/
def signExtendTo64 (bits : Nat) (v : BitVec 64) : BitVec 64 :=
  if bits == 0 || bits >= 64 then v
  else
    let lo := v &&& ((1#64 <<< bits) - 1#64)
    if (lo >>> (bits - 1)) &&& 1#64 == 1#64 then
      lo ||| (~~~((1#64 <<< bits) - 1#64))
    else
      lo

/-- Normalize a binary16 subnormal significand. Structural on `fuel`. -/
def f16NormSub (f e : Nat) : Nat → Nat × Nat
  | 0 => (f, e)
  | k + 1 =>
    if (f &&& 0x400) != 0 then (f &&& 0x3FF, e)
    else f16NormSub (f <<< 1) (e - 1) k

/-- Pure IEEE-754 binary16 -> binary32 widening (reduces definitionally in the Lean kernel). -/
def f16BitsToF32Bits (bits16 : BitVec 16) : BitVec 32 :=
  let sign : Nat := (bits16 >>> 15).toNat &&& 1
  let exp16 : Nat := (bits16 >>> 10).toNat &&& 0x1F
  let frac16 : Nat := bits16.toNat &&& 0x3FF
  if exp16 == 0 then
    if frac16 == 0 then
      BitVec.ofNat 32 (sign <<< 31)
    else
      let (normFrac, exp32) := f16NormSub (frac16 <<< 1) 112 16
      BitVec.ofNat 32 ((sign <<< 31) ||| (exp32 <<< 23) ||| (normFrac <<< 13))
  else if exp16 == 0x1F then
    let frac32 := if frac16 == 0 then 0 else (frac16 <<< 13) ||| 0x400000
    BitVec.ofNat 32 ((sign <<< 31) ||| (0xFF <<< 23) ||| frac32)
  else
    BitVec.ofNat 32 ((sign <<< 31) ||| ((exp16 + 112) <<< 23) ||| (frac16 <<< 13))

/-- Pure IEEE-754 binary32 -> binary16 round-to-nearest-even narrowing. -/
def f32BitsToF16BitsRn (bits32 : BitVec 32) : BitVec 16 :=
  let sign : Nat := (bits32 >>> 31).toNat &&& 1
  let exp32 : Nat := (bits32 >>> 23).toNat &&& 0xFF
  let frac32 : Nat := bits32.toNat &&& 0x7FFFFF
  if exp32 == 0xFF then
    let frac16 := if frac32 == 0 then 0 else ((frac32 >>> 13) ||| 0x200)
    BitVec.ofNat 16 ((sign <<< 15) ||| (0x1F <<< 10) ||| (frac16 &&& 0x3FF))
  else if exp32 == 0 then
    BitVec.ofNat 16 (sign <<< 15)
  else
    let unb : Int := Int.ofNat exp32 - 127
    if unb > 15 then
      BitVec.ofNat 16 ((sign <<< 15) ||| (0x1F <<< 10))
    else if unb >= -14 then
      let exp16 : Nat := Int.toNat (unb + 15)
      let hi : Nat := frac32 >>> 13
      let rem : Nat := frac32 &&& 0x1FFF
      let roundUp := rem > 0x1000 || (rem == 0x1000 && (hi &&& 1) == 1)
      let rounded := if roundUp then hi + 1 else hi
      if rounded >= 0x400 then
        let exp16' := exp16 + 1
        if exp16' >= 0x1F then
          BitVec.ofNat 16 ((sign <<< 15) ||| (0x1F <<< 10))
        else
          BitVec.ofNat 16 ((sign <<< 15) ||| (exp16' <<< 10))
      else
        BitVec.ofNat 16 ((sign <<< 15) ||| (exp16 <<< 10) ||| rounded)
    else if unb >= -25 then
      let shift : Nat := Int.toNat (-14 - unb) + 13
      let fullSig : Nat := (1 <<< 23) ||| frac32
      let hi : Nat := fullSig >>> shift
      let halfBit : Nat := 1 <<< (shift - 1)
      let remMask : Nat := (1 <<< shift) - 1
      let rem : Nat := fullSig &&& remMask
      let roundUp := rem > halfBit || (rem == halfBit && (hi &&& 1) == 1)
      let rounded := if roundUp then hi + 1 else hi
      if rounded >= 0x400 then
        BitVec.ofNat 16 ((sign <<< 15) ||| (1 <<< 10) ||| (rounded &&& 0x3FF))
      else
        BitVec.ofNat 16 ((sign <<< 15) ||| rounded)
    else
      BitVec.ofNat 16 (sign <<< 15)

/-- Normalize a binary32 subnormal significand. Structural on `fuel`. -/
def f32NormSub (m e : Nat) : Nat → Nat × Nat
  | 0 => (m, e)
  | k + 1 =>
    if (m &&& 0x80_0000) != 0 then (m &&& 0x7F_FFFF, e)
    else f32NormSub (m <<< 1) (e - 1) k

/-- Pure IEEE-754 binary32 -> binary64 widening on raw bit patterns. -/
def f32BitsToF64Bits (bits32 : BitVec 32) : BitVec 64 :=
  let b : Nat := bits32.toNat
  let sign : Nat := (b >>> 31) &&& 1
  let exp32 : Nat := (b >>> 23) &&& 0xFF
  let frac32 : Nat := b &&& 0x7F_FFFF
  if exp32 == 0xFF then
    if frac32 == 0 then
      BitVec.ofNat 64 ((sign <<< 63) ||| (0x7FF <<< 52))
    else
      BitVec.ofNat 64 ((sign <<< 63) ||| (0x7FF <<< 52) ||| (1 <<< 51) ||| (frac32 <<< 29))
  else if exp32 == 0 then
    if frac32 == 0 then
      BitVec.ofNat 64 (sign <<< 63)
    else
      let (normFrac, exp64) := f32NormSub frac32 (1023 - 126) 24
      BitVec.ofNat 64 ((sign <<< 63) ||| (exp64 <<< 52) ||| (normFrac <<< 29))
  else
    BitVec.ofNat 64 ((sign <<< 63) ||| ((exp32 + (1023 - 127)) <<< 52) ||| (frac32 <<< 29))

/-- Pure IEEE-754 binary64 -> binary32 round-to-nearest-even narrowing. -/
def f64BitsToF32BitsRn (bits64 : BitVec 64) : BitVec 32 :=
  let b : Nat := bits64.toNat
  let sign : Nat := (b >>> 63) &&& 1
  let exp64 : Nat := (b >>> 52) &&& 0x7FF
  let frac64 : Nat := b &&& 0xF_FFFF_FFFF_FFFF
  if exp64 == 0x7FF then
    if frac64 == 0 then
      BitVec.ofNat 32 ((sign <<< 31) ||| (0xFF <<< 23))
    else
      BitVec.ofNat 32 ((sign <<< 31) ||| (0xFF <<< 23) ||| 0x40_0000)
  else if exp64 == 0 && frac64 == 0 then
    BitVec.ofNat 32 (sign <<< 31)
  else
    let unbiased : Int :=
      if exp64 == 0 then -1022 else Int.ofNat exp64 - 1023
    let sig53 : Nat :=
      if exp64 == 0 then frac64 else (1 <<< 52) ||| frac64
    if unbiased > 127 then
      BitVec.ofNat 32 ((sign <<< 31) ||| (0xFF <<< 23))
    else if unbiased < -149 then
      BitVec.ofNat 32 (sign <<< 31)
    else if unbiased < -126 then
      let shift : Nat := (-126 - unbiased).toNat + 29
      let q : Nat := sig53 >>> shift
      let remMask : Nat := (1 <<< shift) - 1
      let rem : Nat := sig53 &&& remMask
      let half : Nat := 1 <<< (shift - 1)
      let roundUp := rem > half || (rem == half && (q &&& 1) == 1)
      let rounded : Nat := if roundUp then q + 1 else q
      if rounded >= 0x80_0000 then
        BitVec.ofNat 32 ((sign <<< 31) ||| (1 <<< 23) ||| (rounded &&& 0x7F_FFFF))
      else
        BitVec.ofNat 32 ((sign <<< 31) ||| rounded)
    else
      let exp32 : Nat := (unbiased + 127).toNat
      let q : Nat := sig53 >>> 29
      let rem : Nat := sig53 &&& ((1 <<< 29) - 1)
      let half : Nat := 1 <<< 28
      let roundUp := rem > half || (rem == half && (q &&& 1) == 1)
      let rounded : Nat := if roundUp then q + 1 else q
      if rounded >= (1 <<< 24) then
        let exp32' := exp32 + 1
        if exp32' >= 0xFF then
          BitVec.ofNat 32 ((sign <<< 31) ||| (0xFF <<< 23))
        else
          BitVec.ofNat 32 ((sign <<< 31) ||| (exp32' <<< 23))
      else
        BitVec.ofNat 32 ((sign <<< 31) ||| (exp32 <<< 23) ||| (rounded &&& 0x7F_FFFF))

def bvToF16 (v : BitVec 64) : Float32 :=
  Float32.ofBits ⟨f16BitsToF32Bits (v.truncate 16)⟩

def f16ToBv (x : Float32) : BitVec 64 :=
  BitVec.ofNat 64 (f32BitsToF16BitsRn x.toBits.toBitVec).toNat

def bvToF32 (v : BitVec 64) : Float32 :=
  Float32.ofBits (UInt32.ofNat (v &&& 0xFFFF_FFFF#64).toNat)

def f32ToBv (x : Float32) : BitVec 64 :=
  BitVec.ofNat 64 x.toBits.toNat

def bvToF64 (v : BitVec 64) : Float :=
  Float.ofBits (UInt64.ofNat v.toNat)

def f64ToBv (x : Float) : BitVec 64 :=
  x.toBits.toBitVec

/-- Convert a bit pattern interpreted as `srcTy` into `dstTy` (integer width/sign or IEEE-754). -/
def evalMSLCast (dstTy srcTy : MSLType) (v : BitVec 64) : MSLOutcome (BitVec 64) :=
  match dstTy, srcTy with
  | .half, .half => .ok (maskForType .half v)
  | .float, .float => .ok (maskForType .float v)
  | .double, .double => .ok v
  | .float, .half => .ok (BitVec.ofNat 64 (f16BitsToF32Bits (v.truncate 16)).toNat)
  | .half, .float => .ok (BitVec.ofNat 64 (f32BitsToF16BitsRn (v.truncate 32)).toNat)
  | .double, .float => .ok (f32BitsToF64Bits (v.truncate 32))
  | .float, .double => .ok (BitVec.ofNat 64 (f64BitsToF32BitsRn v).toNat)
  | .double, .half => .ok (f32BitsToF64Bits (f16BitsToF32Bits (v.truncate 16)))
  | .half, .double =>
    .ok (BitVec.ofNat 64 (f32BitsToF16BitsRn (f64BitsToF32BitsRn v)).toNat)
  | .float, .uint | .float, .uchar | .float, .ushort | .float, .atomicUint =>
    .ok (f32ToBv (UInt32.ofNat (maskForType srcTy v).toNat).toFloat32)
  | .float, .ulong | .float, .u256 =>
    .ok (f32ToBv (UInt64.ofNat v.toNat).toFloat32)
  | .float, .int =>
    .ok (f32ToBv (Int32.ofBitVec (v.truncate 32)).toFloat32)
  | .float, .long =>
    .ok (f32ToBv (Int64.ofBitVec v).toFloat32)
  | .double, .uint | .double, .uchar | .double, .ushort | .double, .atomicUint =>
    .ok (f64ToBv (UInt32.ofNat (maskForType srcTy v).toNat).toFloat)
  | .double, .ulong | .double, .u256 =>
    .ok (f64ToBv (UInt64.ofNat v.toNat).toFloat)
  | .double, .int =>
    .ok (f64ToBv (Int32.ofBitVec (v.truncate 32)).toFloat)
  | .double, .long =>
    .ok (f64ToBv (Int64.ofBitVec v).toFloat)
  | .uint, .float | .atomicUint, .float =>
    .ok (BitVec.ofNat 64 (bvToF32 v).toUInt32.toNat)
  | .ulong, .float | .u256, .float =>
    .ok (bvToF32 v).toUInt64.toBitVec
  | .int, .float =>
    .ok ((bvToF32 v).toInt32.toBitVec.zeroExtend 64)
  | .long, .float =>
    .ok (bvToF32 v).toInt64.toBitVec
  | .uint, .double | .atomicUint, .double =>
    .ok (BitVec.ofNat 64 (bvToF64 v).toUInt32.toNat)
  | .ulong, .double | .u256, .double =>
    .ok (bvToF64 v).toUInt64.toBitVec
  | .int, .double =>
    .ok ((bvToF64 v).toInt32.toBitVec.zeroExtend 64)
  | .long, .double =>
    .ok (bvToF64 v).toInt64.toBitVec
  | .half, _ | _, .half =>
    .unsupportedFloatOp "unsupported half conversion"
  | _, .float | _, .double | .float, _ | .double, _ =>
    .unsupportedFloatOp "unsupported float conversion"
  | _, _ =>
    let ext :=
      if srcTy.isSigned && dstTy.bitWidth > srcTy.bitWidth then
        signExtendTo64 srcTy.bitWidth v
      else
        maskForType srcTy v
    .ok (maskForType dstTy ext)

/-- Linear lane index inside the threadgroup. -/
def linearTid (groupDim tid : Dim3) : Nat :=
  tid.x + groupDim.x * (tid.y + groupDim.y * tid.z)

/-- Simdgroup id of a lane (32 threads per Apple GPU simdgroup). -/
def simdgroupOf (groupDim tid : Dim3) : Nat :=
  linearTid groupDim tid / 32

/-- Lane index inside its simdgroup (`0 .. 31`). -/
def simdLaneOf (groupDim tid : Dim3) : Nat :=
  linearTid groupDim tid % 32

/-- Evaluate exact 3D coordinate triple `(x, y, z)` for a Metal parameter attribute. -/
def evalBuiltinCoords (g : MSLGroupState) (tid : Dim3) : MSLAttr → Nat × Nat × Nat
  | .buffer idx => (idx, 0, 0)
  | .threadPositionInGrid =>
    (g.groupId.x * g.groupDim.x + tid.x,
     g.groupId.y * g.groupDim.y + tid.y,
     g.groupId.z * g.groupDim.z + tid.z)
  | .threadPositionInThreadgroup => (tid.x, tid.y, tid.z)
  | .threadgroupPositionInGrid => (g.groupId.x, g.groupId.y, g.groupId.z)
  | .threadsPerThreadgroup => (g.groupDim.x, g.groupDim.y, g.groupDim.z)
  | .threadIndexInSimdgroup => (simdLaneOf g.groupDim tid, 0, 0)
  | .simdgroupIndexInThreadgroup => (simdgroupOf g.groupDim tid, 0, 0)

def setIndexedMem : List (Nat × ByteMemory) → Nat → ByteMemory → List (Nat × ByteMemory)
  | [], idx, mem => [(idx, mem)]
  | (idx', mem') :: rest, idx, mem =>
    if idx' == idx then (idx, mem) :: rest else (idx', mem') :: setIndexedMem rest idx mem

def setNamedMem : List (String × ByteMemory) → String → ByteMemory → List (String × ByteMemory)
  | [], name, mem => [(name, mem)]
  | (name', mem') :: rest, name, mem =>
    if name' == name then (name, mem) :: rest else (name', mem') :: setNamedMem rest name mem

/-- Field names of a struct or vector type, in declaration order. -/
def structFieldNames (structs : List MSLStructDecl) : MSLType → List String
  | .uint2 | .ulong2 => ["x", "y"]
  | .uint3 => ["x", "y", "z"]
  | .uint4 => ["x", "y", "z", "w"]
  | .u256 =>
    match structs.find? (fun s => s.name == "ln_u256") with
    | some sd => sd.fields.map (·.name)
    | none => ["l0", "l1", "l2", "l3"]
  | .structTy sname =>
    match structs.find? (fun s => s.name == sname) with
    | some sd => sd.fields.map (·.name)
    | none => []
  | _ => []

/-- Scalar type of one struct/vector field. -/
def structFieldType (structs : List MSLStructDecl) (ty : MSLType) (field : String) : MSLType :=
  match ty with
  | .uint2 | .uint3 | .uint4 => .uint
  | .ulong2 | .u256 => .ulong
  | .structTy sname =>
    match structs.find? (fun s => s.name == sname) with
    | some sd =>
      match sd.fields.find? (fun f => f.name == field) with
      | some fd => fd.ty
      | none => .ulong
    | none => .ulong
  | _ => .ulong

/-- Byte offset and byte width of one declared struct field. Structural on the field list. -/
def structFieldLayoutGo (field : String) (off : Nat) : List MSLStructField → Option (Nat × Nat)
  | [] => none
  | f :: rest =>
    if f.name == field then some (off, f.ty.byteWidth)
    else structFieldLayoutGo field (off + f.ty.byteWidth) rest

/-- Byte offset and byte width of one struct field, or `none` when `field` is not declared. -/
def structFieldLayout (structs : List MSLStructDecl) (ty : MSLType) (field : String) :
    Option (Nat × Nat) :=
  match ty with
  | .uint2 => match field with | "x" => some (0, 4) | "y" => some (4, 4) | _ => none
  | .uint3 =>
    match field with | "x" => some (0, 4) | "y" => some (4, 4) | "z" => some (8, 4) | _ => none
  | .uint4 =>
    match field with
    | "x" => some (0, 4) | "y" => some (4, 4) | "z" => some (8, 4) | "w" => some (12, 4) | _ => none
  | .ulong2 => match field with | "x" => some (0, 8) | "y" => some (8, 8) | _ => none
  | .u256 =>
    let names := structFieldNames structs .u256
    match names.idxOf? field with
    | some i => some (i * 8, 8)
    | none => none
  | .structTy sname =>
    match structs.find? (fun s => s.name == sname) with
    | some sd => structFieldLayoutGo field 0 sd.fields
    | none => none
  | _ => none

/-- Total byte width of a struct or vector type, including declared struct layouts. -/
def aggregateByteWidth (structs : List MSLStructDecl) (ty : MSLType) : Nat :=
  match ty with
  | .structTy sname =>
    match structs.find? (fun s => s.name == sname) with
    | some sd => sd.fields.foldl (fun acc f => acc + f.ty.byteWidth) 0
    | none => 0
  | other => other.byteWidth

/-- Infer the result type of an expression from declared locals, bindings, and constructors. -/
def inferExprType (g : MSLGroupState) (ls : MSLLocals) : MSLExpr → MSLType
  | .var name =>
    match ls.lookupType? name with
    | some ty => ty
    | none =>
      match g.bindings.lookup name with
      | some (.constantScalar _ elemTy) => elemTy
      | _ => .ulong
  | .immU64 _ => .ulong
  | .immBool _ => .bool
  | .immF16 _ => .half
  | .immF32 _ => .float
  | .immF64 _ => .double
  | .fieldAccess base field => structFieldType g.structs (inferExprType g ls base) field
  | .structLit ty _ => ty
  | .bitNot a | .neg a | .clz a => inferExprType g ls a
  | .logNot _ | .logAnd _ _ | .logOr _ _ => .bool
  | .deref ptrName =>
    match ls.lookupArray? ptrName with
    | some _ => (ls.lookupType? ptrName).getD .ulong
    | none =>
      match g.bindings.lookup ptrName with
      | some (.deviceBuf _ _ elemTy) => elemTy
      | some (.constantBuf _ elemTy) => elemTy
      | some (.constantScalar _ elemTy) => elemTy
      | some (.threadgroupArr _ elemTy) => elemTy
      | none => .ulong
  | .cast ty _ => ty
  | .add a b | .sub a b | .mul a b | .div a b | .rem a b =>
    promoteMSLArithType (inferExprType g ls a) (inferExprType g ls b)
  | .bitAnd a b | .bitOr a b | .bitXor a b | .shl a b | .shr a b =>
    promoteMSLArithType (inferExprType g ls a) (inferExprType g ls b)
  | .eq _ _ | .ne _ _ | .lt _ _ | .le _ _ | .gt _ _ | .ge _ _ => .bool
  | .select _ t _ => inferExprType g ls t
  | .builtinSelect f _ _ => inferExprType g ls f
  | .fma a _ _ => inferExprType g ls a
  | .index target _ =>
    match ls.lookupArray? target with
    | some _ => (ls.lookupType? target).getD .ulong
    | none =>
      match g.bindings.lookup target with
      | some (.deviceBuf _ _ elemTy) => elemTy
      | some (.constantBuf _ elemTy) => elemTy
      | some (.constantScalar _ elemTy) => elemTy
      | some (.threadgroupArr _ elemTy) => elemTy
      | none => .ulong
  | .call name _ =>
    match g.funcs.find? (fun f => f.name == name) with
    | some fn => fn.retTy
    | none => .ulong

/-- Lift a non-`.ok` outcome across result types. -/
def propagateErr {α β : Type} : MSLOutcome α → MSLOutcome β
  | .ok _ => .fuelExhausted
  | .readOnlyViolation t i => .readOnlyViolation t i
  | .barrierDivergence => .barrierDivergence
  | .divisionByZero => .divisionByZero
  | .signedDivOverflow => .signedDivOverflow
  | .shiftOutOfRange => .shiftOutOfRange
  | .dataRace s a => .dataRace s a
  | .unsupportedFloatOp m => .unsupportedFloatOp m
  | .outOfBoundsLoad s b i => .outOfBoundsLoad s b i
  | .outOfBoundsWrite s b i => .outOfBoundsWrite s b i
  | .unboundIdentifier n => .unboundIdentifier n
  | .fuelExhausted => .fuelExhausted

inductive MSLBin where
  | add | sub | mul | div | rem

inductive MSLCmp where
  | eq | ne | lt | le | gt | ge

def evalTypedBin (ty : MSLType) (op : MSLBin) (va vb : BitVec 64) : MSLOutcome (BitVec 64) :=
  match ty with
  | .half =>
    let x := bvToF16 va
    let y := bvToF16 vb
    match op with
    | .add => .ok (f16ToBv (x + y))
    | .sub => .ok (f16ToBv (x - y))
    | .mul => .ok (f16ToBv (x * y))
    | .div => .ok (f16ToBv (x / y))
    | .rem => .unsupportedFloatOp "half remainder"
  | .float =>
    let x := bvToF32 va
    let y := bvToF32 vb
    match op with
    | .add => .ok (f32ToBv (x + y))
    | .sub => .ok (f32ToBv (x - y))
    | .mul => .ok (f32ToBv (x * y))
    | .div => .ok (f32ToBv (x / y))
    | .rem => .unsupportedFloatOp "float remainder"
  | .double =>
    let x := bvToF64 va
    let y := bvToF64 vb
    match op with
    | .add => .ok (f64ToBv (x + y))
    | .sub => .ok (f64ToBv (x - y))
    | .mul => .ok (f64ToBv (x * y))
    | .div => .ok (f64ToBv (x / y))
    | .rem => .unsupportedFloatOp "double remainder"
  | .int =>
    let a32 := va.truncate 32
    let b32 := vb.truncate 32
    match op with
    | .div =>
      if b32 == 0#32 then .divisionByZero
      else if a32 == 2147483648#32 && b32 == 4294967295#32 then .signedDivOverflow
      else .ok (maskForType .int ((a32.sdiv b32).zeroExtend 64))
    | .rem =>
      if b32 == 0#32 then .divisionByZero
      else if a32 == 2147483648#32 && b32 == 4294967295#32 then .signedDivOverflow
      else .ok (maskForType .int ((a32.srem b32).zeroExtend 64))
    | .add => .ok (maskForType .int (va + vb))
    | .sub => .ok (maskForType .int (va - vb))
    | .mul => .ok (maskForType .int (va * vb))
  | .long =>
    match op with
    | .div =>
      if vb == 0#64 then .divisionByZero
      else if va == 9223372036854775808#64 && vb == 18446744073709551615#64 then .signedDivOverflow
      else .ok (va.sdiv vb)
    | .rem =>
      if vb == 0#64 then .divisionByZero
      else if va == 9223372036854775808#64 && vb == 18446744073709551615#64 then .signedDivOverflow
      else .ok (va.srem vb)
    | .add => .ok (va + vb)
    | .sub => .ok (va - vb)
    | .mul => .ok (va * vb)
  | _ =>
    match op with
    | .div => if vb == 0#64 then .divisionByZero else .ok (maskForType ty (va / vb))
    | .rem => if vb == 0#64 then .divisionByZero else .ok (maskForType ty (va % vb))
    | .add => .ok (maskForType ty (va + vb))
    | .sub => .ok (maskForType ty (va - vb))
    | .mul => .ok (maskForType ty (va * vb))

def evalTypedCmp (ty : MSLType) (op : MSLCmp) (va vb : BitVec 64) : MSLOutcome (BitVec 64) :=
  let bit (b : Bool) : BitVec 64 := if b then 1#64 else 0#64
  let va := maskForType ty va
  let vb := maskForType ty vb
  match ty with
  | .half =>
    let x := bvToF16 va
    let y := bvToF16 vb
    let nan := x.isNaN || y.isNaN
    match op with
    | .eq => .ok (bit (!nan && x == y))
    | .ne => .ok (bit (nan || x != y))
    | .lt => .ok (bit (!nan && x < y))
    | .le => .ok (bit (!nan && x <= y))
    | .gt => .ok (bit (!nan && x > y))
    | .ge => .ok (bit (!nan && x >= y))
  | .float =>
    let x := bvToF32 va
    let y := bvToF32 vb
    let nan := x.isNaN || y.isNaN
    match op with
    | .eq => .ok (bit (!nan && x == y))
    | .ne => .ok (bit (nan || x != y))
    | .lt => .ok (bit (!nan && x < y))
    | .le => .ok (bit (!nan && x <= y))
    | .gt => .ok (bit (!nan && x > y))
    | .ge => .ok (bit (!nan && x >= y))
  | .double =>
    let x := bvToF64 va
    let y := bvToF64 vb
    let nan := x.isNaN || y.isNaN
    match op with
    | .eq => .ok (bit (!nan && x == y))
    | .ne => .ok (bit (nan || x != y))
    | .lt => .ok (bit (!nan && x < y))
    | .le => .ok (bit (!nan && x <= y))
    | .gt => .ok (bit (!nan && x > y))
    | .ge => .ok (bit (!nan && x >= y))
  | .int =>
    let a32 := va.truncate 32
    let b32 := vb.truncate 32
    match op with
    | .eq => .ok (bit (a32 == b32))
    | .ne => .ok (bit (a32 != b32))
    | .lt => .ok (bit (BitVec.slt a32 b32))
    | .le => .ok (bit (BitVec.sle a32 b32))
    | .gt => .ok (bit (BitVec.slt b32 a32))
    | .ge => .ok (bit (BitVec.sle b32 a32))
  | .long =>
    match op with
    | .eq => .ok (bit (va == vb))
    | .ne => .ok (bit (va != vb))
    | .lt => .ok (bit (BitVec.slt va vb))
    | .le => .ok (bit (BitVec.sle va vb))
    | .gt => .ok (bit (BitVec.slt vb va))
    | .ge => .ok (bit (BitVec.sle vb va))
  | _ =>
    match op with
    | .eq => .ok (bit (va == vb))
    | .ne => .ok (bit (va != vb))
    | .lt => .ok (bit (BitVec.ult va vb))
    | .le => .ok (bit (BitVec.ule va vb))
    | .gt => .ok (bit (BitVec.ult vb va))
    | .ge => .ok (bit (BitVec.ule vb va))

/-- Result of evaluating one expression: scalar value, struct fields, updated locals, and epoch log. -/
structure MSLEval where
  value  : BitVec 64
  fields : List (String × BitVec 64) := []
  locals : MSLLocals
  log    : List MSLAccess
  deriving Repr, DecidableEq, Inhabited

/-- Load an aggregate (vector or struct) from `ByteMemory` at `byteAddr`. -/
def loadAggregateGo (structs : List MSLStructDecl) (mem : ByteMemory) (elemTy : MSLType)
    (byteAddr : Nat) (acc : List (String × BitVec 64)) : List String →
    Option (BitVec 64 × List (String × BitVec 64))
  | [] =>
    match acc.reverse with
    | [] => none
    | (_, v) :: _ => some (v, acc.reverse)
  | n :: rest =>
    match structFieldLayout structs elemTy n with
    | none => none
    | some (off, w) =>
      match mem.loadBits (byteAddr + off) w with
      | none => none
      | some raw =>
        let fv := maskForType (structFieldType structs elemTy n) raw
        loadAggregateGo structs mem elemTy byteAddr ((n, fv) :: acc) rest

def loadAggregate (structs : List MSLStructDecl) (mem : ByteMemory) (elemTy : MSLType)
    (byteAddr : Nat) : Option (BitVec 64 × List (String × BitVec 64)) :=
  loadAggregateGo structs mem elemTy byteAddr [] (structFieldNames structs elemTy)

/-- Load an element (scalar, vector, or struct) from `ByteMemory` at `byteAddr`. -/
def loadTypedElem (structs : List MSLStructDecl) (mem : ByteMemory) (elemTy : MSLType)
    (byteAddr : Nat) : Option (BitVec 64 × List (String × BitVec 64)) :=
  if structFieldNames structs elemTy != [] then
    loadAggregate structs mem elemTy byteAddr
  else
    match mem.loadBits byteAddr elemTy.byteWidth with
    | some raw => some (maskForType elemTy raw, [])
    | none => none

def storeFields (structs : List MSLStructDecl) (mem : ByteMemory) (elemTy : MSLType)
    (byteAddr : Nat) (val : BitVec 64) (fields : List (String × BitVec 64)) :
    List String → Option ByteMemory
  | [] => some mem
  | n :: rest =>
    match structFieldLayout structs elemTy n with
    | none => none
    | some (off, w) =>
      let firstField := ((structFieldNames structs elemTy).head?).getD ""
      let fv := (fields.lookup n).getD (if n == firstField then val else 0#64)
      let fty := structFieldType structs elemTy n
      match mem.storeBits (byteAddr + off) w (maskForType fty fv) with
      | none => none
      | some mem' => storeFields structs mem' elemTy byteAddr val fields rest

/-- Store an element (scalar, vector, or struct) into `ByteMemory` at `byteAddr`. -/
def storeTypedElem (structs : List MSLStructDecl) (mem : ByteMemory) (elemTy : MSLType)
    (byteAddr : Nat) (val : BitVec 64) (fields : List (String × BitVec 64) := []) :
    Option ByteMemory :=
  let names := structFieldNames structs elemTy
  if names != [] then
    storeFields structs mem elemTy byteAddr val fields names
  else
    mem.storeBits byteAddr elemTy.byteWidth (maskForType elemTy val)

/-- Read one element of a bound buffer, recording the access when it can race. -/
def readBoundElement (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess)
    (target : String) (elemIdx : Nat) : MSLOutcome MSLEval :=
  match g.bindings.lookup target with
  | none => .unboundIdentifier target
  | some (.constantScalar bufIdx elemTy) =>
    match g.constantBuffers.lookup bufIdx with
    | none => .outOfBoundsLoad .constant bufIdx elemIdx
    | some mem =>
      match loadTypedElem g.structs mem elemTy 0 with
      | some (v, flds) => .ok { value := v, fields := flds, locals := ls, log }
      | none => .outOfBoundsLoad .constant bufIdx 0
  | some (.constantBuf bufIdx elemTy) =>
    match g.constantBuffers.lookup bufIdx with
    | none => .outOfBoundsLoad .constant bufIdx elemIdx
    | some mem =>
      match loadTypedElem g.structs mem elemTy (elemIdx * aggregateByteWidth g.structs elemTy) with
      | some (v, flds) => .ok { value := v, fields := flds, locals := ls, log }
      | none => .outOfBoundsLoad .constant bufIdx elemIdx
  | some (.deviceBuf bufIdx _ elemTy) =>
    match g.deviceBuffers.lookup bufIdx with
    | none => .outOfBoundsLoad .device bufIdx elemIdx
    | some mem =>
      let width := aggregateByteWidth g.structs elemTy
      let byteAddr := elemIdx * width
      match recordEpochAccess log tid (.deviceBuf bufIdx) .device byteAddr width false with
      | .ok log' =>
        match loadTypedElem g.structs mem elemTy byteAddr with
        | some (v, flds) => .ok { value := v, fields := flds, locals := ls, log := log' }
        | none => .outOfBoundsLoad .device bufIdx elemIdx
      | err => propagateErr err
  | some (.threadgroupArr arrName elemTy) =>
    match g.threadgroupArrays.lookup arrName with
    | none => .outOfBoundsLoad .threadgroup 0 elemIdx
    | some mem =>
      let width := aggregateByteWidth g.structs elemTy
      let byteAddr := elemIdx * width
      match recordEpochAccess log tid (.threadgroupArr arrName) .threadgroup byteAddr width false with
      | .ok log' =>
        match loadTypedElem g.structs mem elemTy byteAddr with
        | some (v, flds) => .ok { value := v, fields := flds, locals := ls, log := log' }
        | none => .outOfBoundsLoad .threadgroup 0 elemIdx
      | err => propagateErr err

def bindEval (mx : MSLOutcome MSLEval) (k : MSLEval → MSLOutcome MSLEval) : MSLOutcome MSLEval :=
  match mx with
  | .ok ev => k ev
  | err => err

/-- Apply a scalar bitwise/arithmetic operator to every lane of a vector, keeping field names. -/
def mapVectorFields (op : BitVec 64 → BitVec 64 → BitVec 64)
    (fa fb : List (String × BitVec 64)) : List (String × BitVec 64) :=
  fa.map fun (n, va) => (n, op va ((fb.lookup n).getD 0#64))

/-- Apply one scalar arithmetic operator to every lane of a vector. -/
def vectorBinGo (laneTy : MSLType) (op : MSLBin) (rb : List (String × BitVec 64)) :
    List (String × BitVec 64) → MSLOutcome (List (String × BitVec 64))
  | [] => .ok []
  | (n, va) :: rest =>
    match evalTypedBin laneTy op va ((rb.lookup n).getD 0#64) with
    | .ok v =>
      match vectorBinGo laneTy op rb rest with
      | .ok vs => .ok ((n, v) :: vs)
      | err => err
    | err => propagateErr err

def finishBin (g : MSLGroupState) (a b : MSLExpr) (op : MSLBin)
    (ea eb : MSLEval) : MSLOutcome MSLEval :=
  let tyA := inferExprType g eb.locals a
  let tyB := inferExprType g eb.locals b
  let ty := promoteMSLArithType tyA tyB
  if tyA.isVector && tyA == tyB then
    let laneTy := structFieldType g.structs tyA "x"
    match vectorBinGo laneTy op eb.fields ea.fields with
    | .ok flds => .ok { value := (flds.head?.map (·.2)).getD 0#64, fields := flds,
                        locals := eb.locals, log := eb.log }
    | err => propagateErr err
  else
    match evalMSLCast ty tyA ea.value with
    | .ok va =>
      match evalMSLCast ty tyB eb.value with
      | .ok vb =>
        match evalTypedBin ty op va vb with
        | .ok v => .ok { value := v, locals := eb.locals, log := eb.log }
        | err => propagateErr err
      | err => propagateErr err
    | err => propagateErr err

def finishBitwise (g : MSLGroupState) (a b : MSLExpr)
    (op : BitVec 64 → BitVec 64 → BitVec 64) (ea eb : MSLEval) : MSLOutcome MSLEval :=
  let tyA := inferExprType g eb.locals a
  let tyB := inferExprType g eb.locals b
  let ty := promoteMSLArithType tyA tyB
  if ty.isFloat then .unsupportedFloatOp "float bitwise op"
  else if ty.isVector then
    let laneTy := structFieldType g.structs ty "x"
    let flds := mapVectorFields (fun x y => maskForType laneTy (op x y)) ea.fields eb.fields
    .ok { value := (flds.head?.map (·.2)).getD 0#64, fields := flds,
          locals := eb.locals, log := eb.log }
  else
    match evalMSLCast ty tyA ea.value with
    | .ok va =>
      match evalMSLCast ty tyB eb.value with
      | .ok vb => .ok { value := maskForType ty (op va vb), locals := eb.locals, log := eb.log }
      | err => propagateErr err
    | err => propagateErr err

def finishShift (g : MSLGroupState) (a : MSLExpr) (right : Bool)
    (ea eb : MSLEval) : MSLOutcome MSLEval :=
  let ty := inferExprType g eb.locals a
  if ty.isFloat then .unsupportedFloatOp "float shift"
  else if ty.isVector then
    let laneTy := structFieldType g.structs ty "x"
    let w := laneTy.bitWidth
    if w == 0 || eb.value.toNat >= w then
      .shiftOutOfRange
    else
      let flds := ea.fields.map fun (n, va) =>
        let shifted :=
          if right && laneTy.isSigned then
            (signExtendTo64 w va).sshiftRight eb.value.toNat
          else if right then va >>> eb.value.toNat
          else va <<< eb.value.toNat
        (n, maskForType laneTy shifted)
      .ok { value := (flds.head?.map (·.2)).getD 0#64, fields := flds,
            locals := eb.locals, log := eb.log }
  else
    let w := ty.bitWidth
    if w == 0 || eb.value.toNat >= w then
      .shiftOutOfRange
    else if right && ty.isSigned then
      let src := if w <= 32 then ea.value.truncate 32 |>.sshiftRight eb.value.toNat |>.zeroExtend 64
                 else ea.value.sshiftRight eb.value.toNat
      .ok { value := maskForType ty src, locals := eb.locals, log := eb.log }
    else if right then
      .ok { value := maskForType ty (ea.value >>> eb.value.toNat), locals := eb.locals, log := eb.log }
    else
      .ok { value := maskForType ty (ea.value <<< eb.value.toNat), locals := eb.locals, log := eb.log }

def finishCmp (g : MSLGroupState) (a b : MSLExpr) (op : MSLCmp)
    (ea eb : MSLEval) : MSLOutcome MSLEval :=
  let tyA := inferExprType g eb.locals a
  let tyB := inferExprType g eb.locals b
  let ty := promoteMSLArithType tyA tyB
  match evalMSLCast ty tyA ea.value with
  | .ok va =>
    match evalMSLCast ty tyB eb.value with
    | .ok vb =>
      match evalTypedCmp ty op va vb with
      | .ok v => .ok { value := v, locals := eb.locals, log := eb.log }
      | err => propagateErr err
    | err => propagateErr err
  | err => propagateErr err

/- Evaluate an expression. `callEval` interprets helper calls so recursion stays structural
   on `MSLExpr` / `MSLExprList` (reduces by `rfl` in the Lean kernel).
   C++ `?:` (`.select`) and `&&` / `||` short-circuit; Metal builtin `select` is eager. -/
mutual
def evalExprWithCall
    (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList →
      MSLOutcome MSLEval)
    (fuel : Nat)
    (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess) :
    MSLExpr → MSLOutcome MSLEval
  | .var name =>
    match ls.lookup? name with
    | some v =>
      let names := structFieldNames g.structs ((ls.lookupType? name).getD .ulong)
      let flds := names.filterMap fun n =>
        match ls.lookupField? name n with
        | some fv => some (n, fv)
        | none => none
      .ok { value := v, fields := flds, locals := ls, log }
    | none =>
      match g.bindings.lookup name with
      | some (.constantScalar bufIdx elemTy) =>
        match g.constantBuffers.lookup bufIdx with
        | some mem =>
          match loadTypedElem g.structs mem elemTy 0 with
          | some (v, flds) => .ok { value := v, fields := flds, locals := ls, log }
          | none => .outOfBoundsLoad .constant bufIdx 0
        | none => .outOfBoundsLoad .constant bufIdx 0
      | _ => .unboundIdentifier name
  | .immU64 v => .ok { value := v, locals := ls, log }
  | .immBool b => .ok { value := if b then 1#64 else 0#64, locals := ls, log }
  | .immF16 bits => .ok { value := BitVec.ofNat 64 bits.toNat, locals := ls, log }
  | .immF32 bits => .ok { value := BitVec.ofNat 64 bits.toNat, locals := ls, log }
  | .immF64 bits => .ok { value := bits, locals := ls, log }
  | .fieldAccess base field =>
    match evalExprWithCall callEval fuel g tid ls log base with
    | .ok ev =>
      match ev.fields.lookup field with
      | some v => .ok { value := v, locals := ev.locals, log := ev.log }
      | none =>
        match base with
        | .var name =>
          match ev.locals.lookupField? name field with
          | some v => .ok { value := v, locals := ev.locals, log := ev.log }
          | none => .unboundIdentifier (name ++ "." ++ field)
        | _ => .unboundIdentifier field
    | err => err
  | .structLit ty args =>
    match evalExprList callEval fuel g tid ls log args with
    | .ok (vals, ls', log') =>
      let names := structFieldNames g.structs ty
      let flds := names.zip vals
      .ok { value := vals.head?.getD 0#64, fields := flds, locals := ls', log := log' }
    | err => propagateErr err
  | .bitNot a =>
    bindEval (evalExprWithCall callEval fuel g tid ls log a) fun ev =>
      let ty := inferExprType g ev.locals a
      if ty.isFloat then .unsupportedFloatOp "float bitNot"
      else if ty.isVector then
        let laneTy := structFieldType g.structs ty "x"
        let flds := ev.fields.map fun (n, v) => (n, maskForType laneTy (~~~v))
        .ok { value := (flds.head?.map (·.2)).getD 0#64, fields := flds,
              locals := ev.locals, log := ev.log }
      else .ok { value := maskForType ty (~~~ev.value), locals := ev.locals, log := ev.log }
  | .logNot a =>
    bindEval (evalExprWithCall callEval fuel g tid ls log a) fun ev =>
      .ok { value := if ev.value == 0#64 then 1#64 else 0#64, locals := ev.locals, log := ev.log }
  | .neg a =>
    bindEval (evalExprWithCall callEval fuel g tid ls log a) fun ev =>
      let ty := inferExprType g ev.locals a
      let v :=
        match ty with
        | .half => f16ToBv (-bvToF16 ev.value)
        | .float => f32ToBv (-bvToF32 ev.value)
        | .double => f64ToBv (-bvToF64 ev.value)
        | _ => maskForType ty (0#64 - ev.value)
      .ok { value := v, locals := ev.locals, log := ev.log }
  | .clz a =>
    bindEval (evalExprWithCall callEval fuel g tid ls log a) fun ev =>
      let ty := inferExprType g ev.locals a
      if ty.isFloat then .unsupportedFloatOp "float clz"
      else
        let bits := ty.bitWidth
        let masked := maskForType ty ev.value
        let z := if bits == 0 then 0 else (masked.truncate bits).clz.toNat
        .ok { value := maskForType ty (BitVec.ofNat 64 z), locals := ev.locals, log := ev.log }
  | .deref ptrName =>
    match ls.lookupArray? ptrName with
    | some slots =>
      match slots[0]? with
      | some slot => .ok { value := slot.value, fields := slot.fields, locals := ls, log }
      | none => .outOfBoundsLoad .thread 0 0
    | none => readBoundElement g tid ls log ptrName 0
  | .cast ty a =>
    bindEval (evalExprWithCall callEval fuel g tid ls log a) fun ev =>
      match evalMSLCast ty (inferExprType g ev.locals a) ev.value with
      | .ok v => .ok { value := v, locals := ev.locals, log := ev.log }
      | err => propagateErr err
  | .add a b =>
    bindEval (evalExprWithCall callEval fuel g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval fuel g tid ea.locals ea.log b) fun eb =>
      finishBin g a b .add ea eb
  | .sub a b =>
    bindEval (evalExprWithCall callEval fuel g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval fuel g tid ea.locals ea.log b) fun eb =>
      finishBin g a b .sub ea eb
  | .mul a b =>
    bindEval (evalExprWithCall callEval fuel g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval fuel g tid ea.locals ea.log b) fun eb =>
      finishBin g a b .mul ea eb
  | .div a b =>
    bindEval (evalExprWithCall callEval fuel g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval fuel g tid ea.locals ea.log b) fun eb =>
      finishBin g a b .div ea eb
  | .rem a b =>
    bindEval (evalExprWithCall callEval fuel g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval fuel g tid ea.locals ea.log b) fun eb =>
      finishBin g a b .rem ea eb
  | .bitAnd a b =>
    bindEval (evalExprWithCall callEval fuel g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval fuel g tid ea.locals ea.log b) fun eb =>
      finishBitwise g a b (· &&& ·) ea eb
  | .bitOr a b =>
    bindEval (evalExprWithCall callEval fuel g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval fuel g tid ea.locals ea.log b) fun eb =>
      finishBitwise g a b (· ||| ·) ea eb
  | .bitXor a b =>
    bindEval (evalExprWithCall callEval fuel g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval fuel g tid ea.locals ea.log b) fun eb =>
      finishBitwise g a b (· ^^^ ·) ea eb
  | .shl a b =>
    bindEval (evalExprWithCall callEval fuel g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval fuel g tid ea.locals ea.log b) fun eb =>
      finishShift g a false ea eb
  | .shr a b =>
    bindEval (evalExprWithCall callEval fuel g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval fuel g tid ea.locals ea.log b) fun eb =>
      finishShift g a true ea eb
  | .logAnd a b =>
    bindEval (evalExprWithCall callEval fuel g tid ls log a) fun ea =>
      if ea.value == 0#64 then
        .ok { value := 0#64, locals := ea.locals, log := ea.log }
      else
        bindEval (evalExprWithCall callEval fuel g tid ea.locals ea.log b) fun eb =>
          .ok { value := if eb.value == 0#64 then 0#64 else 1#64,
                locals := eb.locals, log := eb.log }
  | .logOr a b =>
    bindEval (evalExprWithCall callEval fuel g tid ls log a) fun ea =>
      if ea.value != 0#64 then
        .ok { value := 1#64, locals := ea.locals, log := ea.log }
      else
        bindEval (evalExprWithCall callEval fuel g tid ea.locals ea.log b) fun eb =>
          .ok { value := if eb.value == 0#64 then 0#64 else 1#64,
                locals := eb.locals, log := eb.log }
  | .eq a b =>
    bindEval (evalExprWithCall callEval fuel g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval fuel g tid ea.locals ea.log b) fun eb =>
      finishCmp g a b .eq ea eb
  | .ne a b =>
    bindEval (evalExprWithCall callEval fuel g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval fuel g tid ea.locals ea.log b) fun eb =>
      finishCmp g a b .ne ea eb
  | .lt a b =>
    bindEval (evalExprWithCall callEval fuel g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval fuel g tid ea.locals ea.log b) fun eb =>
      finishCmp g a b .lt ea eb
  | .le a b =>
    bindEval (evalExprWithCall callEval fuel g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval fuel g tid ea.locals ea.log b) fun eb =>
      finishCmp g a b .le ea eb
  | .gt a b =>
    bindEval (evalExprWithCall callEval fuel g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval fuel g tid ea.locals ea.log b) fun eb =>
      finishCmp g a b .gt ea eb
  | .ge a b =>
    bindEval (evalExprWithCall callEval fuel g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval fuel g tid ea.locals ea.log b) fun eb =>
      finishCmp g a b .ge ea eb
  | .select c t f =>
    bindEval (evalExprWithCall callEval fuel g tid ls log c) fun ev =>
      if ev.value != 0#64 then evalExprWithCall callEval fuel g tid ev.locals ev.log t
      else evalExprWithCall callEval fuel g tid ev.locals ev.log f
  | .builtinSelect falseVal trueVal cond =>
    bindEval (evalExprWithCall callEval fuel g tid ls log falseVal) fun ef =>
    bindEval (evalExprWithCall callEval fuel g tid ef.locals ef.log trueVal) fun et =>
    bindEval (evalExprWithCall callEval fuel g tid et.locals et.log cond) fun ec =>
      .ok { value := if ec.value != 0#64 then et.value else ef.value
            fields := if ec.value != 0#64 then et.fields else ef.fields
            locals := ec.locals
            log := ec.log }
  | .fma a b c =>
    bindEval (evalExprWithCall callEval fuel g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval fuel g tid ea.locals ea.log b) fun eb =>
    bindEval (evalExprWithCall callEval fuel g tid eb.locals eb.log c) fun ec =>
      let ty := inferExprType g ec.locals a
      let v :=
        match ty with
        | .half => f16ToBv (Float32.fma (bvToF16 ea.value) (bvToF16 eb.value) (bvToF16 ec.value))
        | .float => f32ToBv (Float32.fma (bvToF32 ea.value) (bvToF32 eb.value) (bvToF32 ec.value))
        | .double => f64ToBv (Float.fma (bvToF64 ea.value) (bvToF64 eb.value) (bvToF64 ec.value))
        | _ => maskForType ty (ea.value * eb.value + ec.value)
      .ok { value := v, locals := ec.locals, log := ec.log }
  | .index target idxExpr =>
    bindEval (evalExprWithCall callEval fuel g tid ls log idxExpr) fun ev =>
      match ev.locals.lookupArray? target with
      | some slots =>
        match slots[ev.value.toNat]? with
        | some slot =>
          .ok { value := slot.value, fields := slot.fields, locals := ev.locals, log := ev.log }
        | none => .outOfBoundsLoad .thread 0 ev.value.toNat
      | none => readBoundElement g tid ev.locals ev.log target ev.value.toNat
  | .call name args =>
    callEval fuel g tid ls log name args

def evalExprList
    (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList →
      MSLOutcome MSLEval)
    (fuel : Nat)
    (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess) :
    MSLExprList → MSLOutcome (List (BitVec 64) × MSLLocals × List MSLAccess)
  | .nil => .ok ([], ls, log)
  | .cons e rest =>
    match evalExprWithCall callEval fuel g tid ls log e with
    | .ok ev =>
      match evalExprList callEval fuel g tid ev.locals ev.log rest with
      | .ok (vs, ls', log') => .ok (ev.value :: vs, ls', log')
      | err => err
    | err => propagateErr err

def evalExprSlotList
    (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList →
      MSLOutcome MSLEval)
    (fuel : Nat)
    (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess) :
    MSLExprList → MSLOutcome (List MSLLocalSlot × MSLLocals × List MSLAccess)
  | .nil => .ok ([], ls, log)
  | .cons e rest =>
    match evalExprWithCall callEval fuel g tid ls log e with
    | .ok ev =>
      match evalExprSlotList callEval fuel g tid ev.locals ev.log rest with
      | .ok (slots, ls', log') =>
        .ok ({ value := ev.value, fields := ev.fields } :: slots, ls', log')
      | err => err
    | err => propagateErr err
end

/-- Bind a scalar or struct value into locals, masking to the declared type. -/
def bindValue (structs : List MSLStructDecl) (ls : MSLLocals) (name : String) (ty : MSLType)
    (v : BitVec 64) (flds : List (String × BitVec 64)) : MSLLocals :=
  let ls' := ls.setTyped name ty (maskForType ty v)
  flds.foldl (fun acc (fn, fv) =>
    acc.setField name fn (maskForType (structFieldType structs ty fn) fv)) ls'

/-- Bounds-checked write of one element into `deviceBuffers[bufIdx]`. -/
def writeDeviceBuffer (g : MSLGroupState) (bufIdx : Nat) (elemTy : MSLType)
    (elemIdx : Nat) (val : BitVec 64) (fields : List (String × BitVec 64) := []) :
    MSLOutcome MSLGroupState :=
  match g.deviceBuffers.lookup bufIdx with
  | none => .outOfBoundsWrite .device bufIdx elemIdx
  | some mem =>
    match storeTypedElem g.structs mem elemTy (elemIdx * aggregateByteWidth g.structs elemTy)
        val fields with
    | some mem' =>
      .ok { g with deviceBuffers := setIndexedMem g.deviceBuffers bufIdx mem' }
    | none => .outOfBoundsWrite .device bufIdx elemIdx

/-- Bounds-checked write of one element into `threadgroupArrays[arrName]`. -/
def writeThreadgroupArray (g : MSLGroupState) (arrName : String) (elemTy : MSLType)
    (elemIdx : Nat) (val : BitVec 64) (fields : List (String × BitVec 64) := []) :
    MSLOutcome MSLGroupState :=
  match g.threadgroupArrays.lookup arrName with
  | none => .outOfBoundsWrite .threadgroup 0 elemIdx
  | some mem =>
    match storeTypedElem g.structs mem elemTy (elemIdx * aggregateByteWidth g.structs elemTy)
        val fields with
    | some mem' =>
      .ok { g with threadgroupArrays := setNamedMem g.threadgroupArrays arrName mem' }
    | none => .outOfBoundsWrite .threadgroup 0 elemIdx

/-- Write one indexed element, trapping on read-only targets, out-of-bounds, and data races.
    `atomic = true` records the access as atomic so it races only with non-atomic accesses. -/
def execIndexWrite (g : MSLGroupState) (tid : Dim3) (target : String) (elemIdx : Nat)
    (val : BitVec 64) (fields : List (String × BitVec 64) := [])
    (atomic : Bool := false) : MSLOutcome MSLGroupState :=
  match g.bindings.lookup target with
  | none => .unboundIdentifier target
  | some (.constantBuf _ _) | some (.constantScalar _ _) =>
    .readOnlyViolation target elemIdx
  | some (.deviceBuf _ true _) =>
    .readOnlyViolation target elemIdx
  | some (.deviceBuf bufIdx false elemTy) =>
    let width := aggregateByteWidth g.structs elemTy
    let byteAddr := elemIdx * width
    match recordEpochAccess g.epochLog tid (.deviceBuf bufIdx) .device byteAddr width true atomic with
    | .ok log' => writeDeviceBuffer { g with epochLog := log' } bufIdx elemTy elemIdx val fields
    | err => propagateErr err
  | some (.threadgroupArr arrName elemTy) =>
    let width := aggregateByteWidth g.structs elemTy
    let byteAddr := elemIdx * width
    match recordEpochAccess g.epochLog tid (.threadgroupArr arrName) .threadgroup byteAddr width true atomic with
    | .ok log' => writeThreadgroupArray { g with epochLog := log' } arrName elemTy elemIdx val fields
    | err => propagateErr err

/-- Execute an atomic read-modify-write (`atomic_fetch_add_explicit` or `atomic_exchange_explicit`)
    on `target[elemIdx]` (with `idx = none` denoting scalar/zero-index `target`). -/
def execAtomicRMW (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (declTy : Option MSLType) (dst : Option String) (target : String) (elemIdx : Nat)
    (rmw : MSLType → BitVec 64 → BitVec 64) :
    MSLOutcome (MSLLocals × MSLGroupState) :=
  match g.bindings.lookup target with
  | none => .unboundIdentifier target
  | some (.constantBuf _ _) | some (.constantScalar _ _) => .readOnlyViolation target elemIdx
  | some (.deviceBuf _ true _) => .readOnlyViolation target elemIdx
  | some (.deviceBuf bufIdx false elemTy) =>
    match g.deviceBuffers.lookup bufIdx with
    | none => .outOfBoundsWrite .device bufIdx elemIdx
    | some mem =>
      let width := aggregateByteWidth g.structs elemTy
      match mem.loadBits (elemIdx * width) elemTy.byteWidth with
      | none => .outOfBoundsWrite .device bufIdx elemIdx
      | some old =>
        let maskedOld := maskForType elemTy old
        let newVal := maskForType elemTy (rmw elemTy maskedOld)
        match execIndexWrite g tid target elemIdx newVal [] true with
        | .ok g' =>
          let ls' :=
            match dst with
            | none => ls
            | some name =>
              let ty := declTy.getD ((ls.lookupType? name).getD elemTy)
              ls.setTyped name ty (maskForType ty maskedOld)
          .ok (ls', g')
        | err => propagateErr err
  | some (.threadgroupArr arrName elemTy) =>
    match g.threadgroupArrays.lookup arrName with
    | none => .outOfBoundsWrite .threadgroup 0 elemIdx
    | some mem =>
      let width := aggregateByteWidth g.structs elemTy
      match mem.loadBits (elemIdx * width) elemTy.byteWidth with
      | none => .outOfBoundsWrite .threadgroup 0 elemIdx
      | some old =>
        let maskedOld := maskForType elemTy old
        let newVal := maskForType elemTy (rmw elemTy maskedOld)
        match execIndexWrite g tid target elemIdx newVal [] true with
        | .ok g' =>
          let ls' :=
            match dst with
            | none => ls
            | some name =>
              let ty := declTy.getD ((ls.lookupType? name).getD elemTy)
              ls.setTyped name ty (maskForType ty maskedOld)
          .ok (ls', g')
        | err => propagateErr err

/-- Default per-callee statement budget when `MSLGroupState.fuelBudget = 0`. -/
def defaultCalleeBudget : Nat := 1024

/-- Effective per-callee statement budget. -/
def effectiveCalleeFuel (g : MSLGroupState) : Nat :=
  if g.fuelBudget == 0 then defaultCalleeBudget else g.fuelBudget

/-- Build a stack-allocated array slot list of length `count` from optional initializer slots. -/
def padArraySlots (structs : List MSLStructDecl) (elemTy : MSLType) (count : Nat)
    (initSlots : List MSLLocalSlot) : List MSLLocalSlot :=
  let zeroFields := (structFieldNames structs elemTy).map fun n => (n, 0#64)
  let zeroSlot : MSLLocalSlot := { value := 0#64, fields := zeroFields }
  (List.range count).map fun i =>
    match initSlots[i]? with
    | some sl =>
      let maskedVal := maskForType elemTy sl.value
      let maskedFlds := sl.fields.map fun (fn, fv) =>
        (fn, maskForType (structFieldType structs elemTy fn) fv)
      { value := maskedVal, fields := maskedFlds }
    | none => zeroSlot

/-- Update one element of a stack-allocated local array, returning `none` if out of bounds. -/
def updateArraySlot (structs : List MSLStructDecl) (elemTy : MSLType)
    (slots : List MSLLocalSlot) (idx : Nat) (val : BitVec 64)
    (fields : List (String × BitVec 64)) : Option (List MSLLocalSlot) :=
  if idx < slots.length then
    let maskedVal := maskForType elemTy val
    let names := structFieldNames structs elemTy
    let maskedFlds :=
      if names == [] then []
      else names.map fun fn =>
        let fv := (fields.lookup fn).getD (if fn == (names.head?.getD "") then maskedVal else 0#64)
        (fn, maskForType (structFieldType structs elemTy fn) fv)
    some (slots.set idx { value := maskedVal, fields := maskedFlds })
  else
    none

/-- Execute one non-barrier, non-collective statement parameterized by `callEval` and `calleeFuel`. -/
def execStmtWithCall
    (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList →
      MSLOutcome MSLEval)
    (calleeFuel : Nat)
    (g : MSLGroupState) (th : MSLThreadState) (stmt : MSLStmt)
    (rest : List MSLStmt) : MSLOutcome (MSLThreadState × MSLGroupState) :=
  match stmt with
  | .varDecl ty name rhs =>
    let boundCheck : Option MSLBufferBinding :=
      match g.bindings.lookup name with
      | none =>
        match rhs with
        | .var src => g.bindings.lookup src
        | _ => none
      | some _ => none
    match boundCheck with
    | some (.constantScalar bufIdx elemTy) =>
      match g.constantBuffers.lookup bufIdx with
      | some mem =>
        match loadTypedElem g.structs mem elemTy 0 with
        | some (v, flds) =>
          let ls := bindValue g.structs th.locals name ty v flds
          .ok ({ th with locals := ls, stmts := rest }, g)
        | none => .outOfBoundsLoad .constant bufIdx 0
      | none => .outOfBoundsLoad .constant bufIdx 0
    | _ =>
      match evalExprWithCall callEval calleeFuel g th.tid th.locals g.epochLog rhs with
      | .ok ev =>
        let ls := bindValue g.structs ev.locals name ty ev.value ev.fields
        .ok ({ th with locals := ls, stmts := rest }, { g with epochLog := ev.log })
      | err => propagateErr err
  | .arrayDecl elemTy name count initList =>
    match evalExprSlotList callEval calleeFuel g th.tid th.locals g.epochLog initList with
    | .ok (initSlots, lsAfter, logAfter) =>
      let slots := padArraySlots g.structs elemTy count initSlots
      let ls1 := lsAfter.setTyped name elemTy 0#64
      let ls2 := ls1.setArray name slots
      .ok ({ th with locals := ls2, stmts := rest }, { g with epochLog := logAfter })
    | err => propagateErr err
  | .assign name rhs =>
    match evalExprWithCall callEval calleeFuel g th.tid th.locals g.epochLog rhs with
    | .ok ev =>
      let ty := (ev.locals.lookupType? name).getD (inferExprType g ev.locals rhs)
      let ls := bindValue g.structs ev.locals name ty ev.value ev.fields
      .ok ({ th with locals := ls, stmts := rest }, { g with epochLog := ev.log })
    | err => propagateErr err
  | .fieldAssign varName field rhs =>
    match evalExprWithCall callEval calleeFuel g th.tid th.locals g.epochLog rhs with
    | .ok ev =>
      let varTy := (ev.locals.lookupType? varName).getD .ulong
      let fty := structFieldType g.structs varTy field
      let masked := maskForType fty ev.value
      let ls1 := ev.locals.setField varName field masked
      let firstField := (structFieldNames g.structs varTy).head?.getD ""
      let ls2 := if field == firstField then ls1.set varName masked else ls1
      .ok ({ th with locals := ls2, stmts := rest }, { g with epochLog := ev.log })
    | err => propagateErr err
  | .indexAssign target idxExpr rhs =>
    match evalExprWithCall callEval calleeFuel g th.tid th.locals g.epochLog idxExpr with
    | .ok ei =>
      match evalExprWithCall callEval calleeFuel g th.tid ei.locals ei.log rhs with
      | .ok er =>
        let elemIdx := ei.value.toNat
        match er.locals.lookupArray? target with
        | some slots =>
          let elemTy := (er.locals.lookupType? target).getD (inferExprType g er.locals rhs)
          match updateArraySlot g.structs elemTy slots elemIdx er.value er.fields with
          | some slots' =>
            let ls' := er.locals.setArray target slots'
            .ok ({ th with locals := ls', stmts := rest }, { g with epochLog := er.log })
          | none => .outOfBoundsWrite .thread 0 elemIdx
        | none =>
          match execIndexWrite { g with epochLog := er.log } th.tid target
              elemIdx er.value er.fields false with
          | .ok g' => .ok ({ th with locals := er.locals, stmts := rest }, g')
          | err => propagateErr err
      | err => propagateErr err
    | err => propagateErr err
  | .derefAssign ptrName rhs =>
    match evalExprWithCall callEval calleeFuel g th.tid th.locals g.epochLog rhs with
    | .ok er =>
      match er.locals.lookupArray? ptrName with
      | some slots =>
        let elemTy := (er.locals.lookupType? ptrName).getD (inferExprType g er.locals rhs)
        match updateArraySlot g.structs elemTy slots 0 er.value er.fields with
        | some slots' =>
          let ls' := er.locals.setArray ptrName slots'
          .ok ({ th with locals := ls', stmts := rest }, { g with epochLog := er.log })
        | none => .outOfBoundsWrite .thread 0 0
      | none =>
        match execIndexWrite { g with epochLog := er.log } th.tid ptrName
            0 er.value er.fields false with
        | .ok g' => .ok ({ th with locals := er.locals, stmts := rest }, g')
        | err => propagateErr err
    | err => propagateErr err
  | .callAssign declTy dst fnName args =>
    match callEval calleeFuel g th.tid th.locals g.epochLog fnName args with
    | .ok ev =>
      let ty := declTy.getD ((ev.locals.lookupType? dst).getD
        (inferExprType g ev.locals (.call fnName args)))
      let ls := bindValue g.structs ev.locals dst ty ev.value ev.fields
      .ok ({ th with locals := ls, stmts := rest }, { g with epochLog := ev.log })
    | err => propagateErr err
  | .exprStmt e =>
    match evalExprWithCall callEval calleeFuel g th.tid th.locals g.epochLog e with
    | .ok ev => .ok ({ th with locals := ev.locals, stmts := rest }, { g with epochLog := ev.log })
    | err => propagateErr err
  | .atomicFetchAdd declTy dst target idxOpt valExpr =>
    let idxRes : MSLOutcome MSLEval :=
      match idxOpt with
      | some idxExpr => evalExprWithCall callEval calleeFuel g th.tid th.locals g.epochLog idxExpr
      | none => .ok { value := 0#64, locals := th.locals, log := g.epochLog }
    match idxRes with
    | .ok ei =>
      match evalExprWithCall callEval calleeFuel g th.tid ei.locals ei.log valExpr with
      | .ok ev =>
        match execAtomicRMW { g with epochLog := ev.log } th.tid ev.locals declTy dst target
            ei.value.toNat (fun _ old => old + ev.value) with
        | .ok (ls', g') => .ok ({ th with locals := ls', stmts := rest }, g')
        | err => propagateErr err
      | err => propagateErr err
    | err => propagateErr err
  | .atomicExchange declTy dst target idxOpt valExpr =>
    let idxRes : MSLOutcome MSLEval :=
      match idxOpt with
      | some idxExpr => evalExprWithCall callEval calleeFuel g th.tid th.locals g.epochLog idxExpr
      | none => .ok { value := 0#64, locals := th.locals, log := g.epochLog }
    match idxRes with
    | .ok ei =>
      match evalExprWithCall callEval calleeFuel g th.tid ei.locals ei.log valExpr with
      | .ok ev =>
        match execAtomicRMW { g with epochLog := ev.log } th.tid ev.locals declTy dst target
            ei.value.toNat (fun _ _ => ev.value) with
        | .ok (ls', g') => .ok ({ th with locals := ls', stmts := rest }, g')
        | err => propagateErr err
      | err => propagateErr err
    | err => propagateErr err
  | .simdShuffleXor _ _ _ _ | .simdSum _ _ _ | .threadgroupBarrier =>
    .barrierDivergence
  | .ifElse cond thenBr elseBr =>
    match evalExprWithCall callEval calleeFuel g th.tid th.locals g.epochLog cond with
    | .ok ev =>
      let branch := if ev.value != 0#64 then thenBr.toList else elseBr.toList
      .ok ({ th with locals := ev.locals, stmts := branch ++ rest }, { g with epochLog := ev.log })
    | err => propagateErr err
  | .forLoop loopVar ty initExpr condExpr stepExpr body =>
    match evalExprWithCall callEval calleeFuel g th.tid th.locals g.epochLog initExpr with
    | .ok ev =>
      let ls := ev.locals.setTyped loopVar ty (maskForType ty ev.value)
      let cont := .whileLoop condExpr (body.append (.cons (.assign loopVar stepExpr) .nil))
      .ok ({ th with locals := ls, stmts := cont :: rest }, { g with epochLog := ev.log })
    | err => propagateErr err
  | .whileLoop condExpr body =>
    match evalExprWithCall callEval calleeFuel g th.tid th.locals g.epochLog condExpr with
    | .ok ev =>
      if ev.value != 0#64 then
        .ok ({ th with locals := ev.locals, stmts := body.toList ++ (stmt :: rest) },
             { g with epochLog := ev.log })
      else
        .ok ({ th with locals := ev.locals, stmts := rest }, { g with epochLog := ev.log })
    | err => propagateErr err
  | .returnVal e =>
    match evalExprWithCall callEval calleeFuel g th.tid th.locals g.epochLog e with
    | .ok ev =>
      let ls := ev.fields.foldl (fun acc (n, v) => acc.setField "$ret" n v) ev.locals
      .ok ({ th with retVal := some ev.value, locals := ls, stmts := [], halted := true },
           { g with epochLog := ev.log })
    | err => propagateErr err
  | .returnStmt =>
    .ok ({ th with stmts := [], halted := true }, g)

/-- Run a helper body for at most `steps` statements, threading memory and epoch updates.
    Structural on `steps`. -/
def runCalleeWithCall
    (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList →
      MSLOutcome MSLEval)
    (calleeFuel : Nat) (steps : Nat) (g : MSLGroupState) (th : MSLThreadState) :
    MSLOutcome (MSLThreadState × MSLGroupState) :=
  match steps with
  | 0 => if th.halted then .ok (th, g) else .fuelExhausted
  | s + 1 =>
    if th.halted then .ok (th, g)
    else
      match th.stmts with
      | [] => .ok ({ th with halted := true }, g)
      | stmt :: rest =>
        match execStmtWithCall callEval calleeFuel g th stmt rest with
        | .ok (th', g') => runCalleeWithCall callEval calleeFuel s g' th'
        | err => propagateErr err

/-- Copy `thread T&` (including `arr[idx]` element refs) and mutable `thread T arr[N]` parameters
    back into the caller after a helper returns. -/
def writeBackRefs (structs : List MSLStructDecl) (caller callee : MSLLocals)
    (params : List MSLParamDecl) (argSlots : List (MSLExpr × Nat)) : MSLLocals :=
  (params.zip argSlots).foldl (fun acc (p, (e, idxVal)) =>
    match p.ty, e with
    | .ref .thread _, .var name =>
      match callee.lookup? p.name with
      | some v =>
        let ty := (acc.lookupType? name).getD .ulong
        let acc' := acc.setTyped name ty (maskForType ty v)
        (structFieldNames structs ty).foldl (fun a fn =>
          match callee.lookupField? p.name fn with
          | some fv => a.setField name fn fv
          | none => a) acc'
      | none => acc
    | .ref .thread innerTy, .index arrName _ =>
      match acc.lookupArray? arrName, callee.lookup? p.name with
      | some slots, some v =>
        let flds := (structFieldNames structs innerTy).filterMap fun fn =>
          (callee.lookupField? p.name fn).map fun fv => (fn, fv)
        match updateArraySlot structs innerTy slots idxVal v flds with
        | some slots' => acc.setArray arrName slots'
        | none => acc
      | _, _ => acc
    | .threadArr false _ _, .var arrName =>
      match callee.lookupArray? p.name with
      | some slots => acc.setArray arrName slots
      | none => acc
    | _, _ => acc) caller

/-- Bind helper parameters, supporting value params, `thread T&` (on locals or `arr[idx]`),
    and `thread [const] T arr[N]` stack array parameters. Structural on `MSLExprList`. -/
def bindParams
    (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList →
      MSLOutcome MSLEval)
    (calleeFuel : Nat) (structs : List MSLStructDecl) (fnName : String)
    (g : MSLGroupState) (tid : Dim3) :
    List MSLParamDecl → MSLExprList → MSLLocals → MSLLocals → List MSLAccess →
      MSLOutcome (MSLLocals × MSLLocals × List MSLAccess × List (MSLExpr × Nat))
  | [], .nil, callerLs, calleeAcc, curLog => .ok (callerLs, calleeAcc, curLog, [])
  | p :: prest, .cons e erest, callerLs, calleeAcc, curLog =>
    match p.ty, e with
    | .threadArr _ elemTy count, .var arrName =>
      match callerLs.lookupArray? arrName with
      | some slots =>
        let padded := padArraySlots structs elemTy count slots
        let calleeAcc1 := calleeAcc.setTyped p.name elemTy 0#64
        let calleeAcc2 := calleeAcc1.setArray p.name padded
        match bindParams callEval calleeFuel structs fnName g tid prest erest
            callerLs calleeAcc2 curLog with
        | .ok (cLs, calLs, log', metaRest) => .ok (cLs, calLs, log', (e, 0) :: metaRest)
        | err => err
      | none => .unboundIdentifier arrName
    | .ref .thread innerTy, .index arrName idxExpr =>
      match evalExprWithCall callEval calleeFuel g tid callerLs curLog idxExpr with
      | .ok ei =>
        let idxVal := ei.value.toNat
        match ei.locals.lookupArray? arrName with
        | some slots =>
          match slots[idxVal]? with
          | some slot =>
            let calleeAcc' := bindValue structs calleeAcc p.name innerTy slot.value slot.fields
            match bindParams callEval calleeFuel structs fnName g tid prest erest
                ei.locals calleeAcc' ei.log with
            | .ok (cLs, calLs, log', metaRest) =>
              .ok (cLs, calLs, log', (e, idxVal) :: metaRest)
            | err => err
          | none => .outOfBoundsLoad .thread 0 idxVal
        | none => .unboundIdentifier arrName
      | err => propagateErr err
    | _, _ =>
      match evalExprWithCall callEval calleeFuel g tid callerLs curLog e with
      | .ok ev =>
        let paramTy := match p.ty with | .ref .thread inner => inner | other => other
        let calleeAcc' := bindValue structs calleeAcc p.name paramTy ev.value ev.fields
        match bindParams callEval calleeFuel structs fnName g tid prest erest
            ev.locals calleeAcc' ev.log with
        | .ok (cLs, calLs, log', metaRest) => .ok (cLs, calLs, log', (e, 0) :: metaRest)
        | err => err
      | err => propagateErr err
  | _, _, _, _, _ => .unboundIdentifier fnName

/-- Maximum nested helper call depth supported by `kernelCallEval` (>= 8 for deep pipelines). -/
def defaultCallDepth : Nat := 10

/-- Interpret a function call at bounded nesting depth `depth`. Structural on `depth`. -/
def makeCallEval (depth : Nat) (calleeFuel : Nat) (g : MSLGroupState) (tid : Dim3)
    (ls : MSLLocals) (log : List MSLAccess) (name : String) (args : MSLExprList) :
    MSLOutcome MSLEval :=
  match depth with
  | 0 => .fuelExhausted
  | d + 1 =>
    match g.funcs.find? (fun f => f.name == name) with
    | none => .unboundIdentifier name
    | some fn =>
      match bindParams (makeCallEval d) calleeFuel g.structs name g tid
          fn.params args ls MSLLocals.empty log with
      | .ok (callerLs', calleeLocals, logAfterArgs, argMeta) =>
        let callee : MSLThreadState :=
          { tid, locals := calleeLocals, stmts := fn.body.toList, halted := false }
        match runCalleeWithCall (makeCallEval d) calleeFuel calleeFuel
            { g with epochLog := logAfterArgs } callee with
        | .ok (th', gAfter) =>
          let retFields :=
            (structFieldNames g.structs fn.retTy).filterMap fun n =>
              match th'.locals.lookupField? "$ret" n with
              | some v => some (n, v)
              | none => none
          let callerOut := writeBackRefs g.structs callerLs' th'.locals fn.params argMeta
          .ok { value := maskForType fn.retTy (th'.retVal.getD 0#64)
                fields := retFields
                locals := callerOut
                log := gAfter.epochLog }
        | err => propagateErr err
      | err => propagateErr err

/-- Default helper-call evaluator (supports call chains up to `defaultCallDepth = 10`). -/
def kernelCallEval :
    Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList →
      MSLOutcome MSLEval :=
  makeCallEval defaultCallDepth

/-- Evaluate an `MSLExpr` over `BitVec 64` (independent of `LeanNative.Semantics`). -/
def evalMSLExpr (g : MSLGroupState) (th : MSLThreadState) (e : MSLExpr) : MSLOutcome (BitVec 64) :=
  match evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog e with
  | .ok ev => .ok ev.value
  | err => propagateErr err

/-- Execute one non-barrier, non-collective `MSLStmt`. -/
def execNonBarrierStmt (g : MSLGroupState) (th : MSLThreadState) (stmt : MSLStmt)
    (rest : List MSLStmt) : MSLOutcome (MSLThreadState × MSLGroupState) :=
  execStmtWithCall kernelCallEval (effectiveCalleeFuel g) g th stmt rest

/-- True when the thread is parked on `threadgroup_barrier`. -/
def threadAtBarrier (th : MSLThreadState) : Bool :=
  match th.stmts with
  | .threadgroupBarrier :: _ => true
  | _ => false

/-- True when the thread is parked on a simdgroup collective (`simd_shuffle_xor` / `simd_sum`). -/
def threadAtSimdOp (th : MSLThreadState) : Bool :=
  match th.stmts with
  | .simdShuffleXor _ _ _ _ :: _ => true
  | .simdSum _ _ _ :: _ => true
  | _ => false

/-- Pop the leading `threadgroup_barrier` from a synchronized thread's continuation. -/
def advanceBarrierThread (th : MSLThreadState) : MSLThreadState :=
  match th.stmts with
  | .threadgroupBarrier :: rest => { th with stmts := rest }
  | _ => th

/-- Synchronize a Metal threadgroup at `threadgroup_barrier(mem_flags::mem_threadgroup)`:
    succeeds iff the threadgroup is non-empty and every thread has arrived uniformly at
    `threadgroupBarrier`, clearing `epochLog`; otherwise traps with `.barrierDivergence`. -/
def stepGroupBarrier (g : MSLGroupState) : MSLOutcome MSLGroupState :=
  if !g.threads.isEmpty && g.threads.all threadAtBarrier then
    .ok { g with threads := g.threads.map advanceBarrierThread, epochLog := [] }
  else
    .barrierDivergence

def addSimdValues (ty : MSLType) (a b : BitVec 64) : BitVec 64 :=
  match ty with
  | .half => f16ToBv (bvToF16 a + bvToF16 b)
  | .float => f32ToBv (bvToF32 a + bvToF32 b)
  | .double => f64ToBv (bvToF64 a + bvToF64 b)
  | _ => maskForType ty (a + b)

/-- Pre-evaluated per-lane state for a single-pass `simd_shuffle_xor` collective. -/
structure SimdShuffleSample where
  lane     : Nat
  srcVal   : BitVec 64
  srcFlds  : List (String × BitVec 64)
  partner  : Nat
  declTy   : Option MSLType
  dst      : String
  inferred : MSLType
  locals   : MSLLocals
  tail     : List MSLStmt

/-- Pass 1 of `simd_shuffle_xor`: evaluate `srcExpr` and `maskExpr` exactly once per active lane
    in `sgId`, threading `curLog` across lanes. Structural on the thread list. -/
def collectSimdShuffle (g : MSLGroupState) (sgId : Nat) (curLog : List MSLAccess) :
    List MSLThreadState →
      MSLOutcome (List (Dim3 × SimdShuffleSample) × List (Nat × (BitVec 64 × List (String × BitVec 64))) × List MSLAccess)
  | [] => .ok ([], [], curLog)
  | th :: rest =>
    if !th.halted && simdgroupOf g.groupDim th.tid == sgId then
      match th.stmts with
      | .simdShuffleXor declTy dst srcExpr maskExpr :: tail =>
        let cf := effectiveCalleeFuel g
        match evalExprWithCall kernelCallEval cf g th.tid th.locals curLog srcExpr with
        | .ok es =>
          match evalExprWithCall kernelCallEval cf g th.tid es.locals es.log maskExpr with
          | .ok em =>
            let lane := simdLaneOf g.groupDim th.tid
            let partner := lane ^^^ (em.value.toNat % 32)
            let inferred := inferExprType g em.locals srcExpr
            let sample : SimdShuffleSample :=
              { lane, srcVal := es.value, srcFlds := es.fields, partner
                declTy, dst, inferred, locals := em.locals, tail }
            match collectSimdShuffle g sgId em.log rest with
            | .ok (samples, laneVals, log') =>
              .ok ((th.tid, sample) :: samples,
                   (lane, (es.value, es.fields)) :: laneVals,
                   log')
            | err => err
          | err => propagateErr err
        | err => propagateErr err
      | _ => .barrierDivergence
    else
      collectSimdShuffle g sgId curLog rest

/-- Pass 2 of `simd_shuffle_xor`: distribute shuffled values into each lane's `dst` without
    re-evaluating `srcExpr` or `maskExpr`. Structural on the thread list. -/
def distributeSimdShuffle (g : MSLGroupState) (sgId : Nat)
    (samples : List (Dim3 × SimdShuffleSample))
    (laneVals : List (Nat × (BitVec 64 × List (String × BitVec 64)))) :
    List MSLThreadState → List MSLThreadState
  | [] => []
  | th :: rest =>
    let rest' := distributeSimdShuffle g sgId samples laneVals rest
    if !th.halted && simdgroupOf g.groupDim th.tid == sgId then
      match samples.lookup th.tid with
      | some sm =>
        let (v, flds) := (laneVals.lookup sm.partner).getD (sm.srcVal, sm.srcFlds)
        let ty := sm.declTy.getD ((sm.locals.lookupType? sm.dst).getD sm.inferred)
        let ls := bindValue g.structs sm.locals sm.dst ty v flds
        { th with locals := ls, stmts := sm.tail } :: rest'
      | none => th :: rest'
    else
      th :: rest'

/-- Pre-evaluated per-lane state for a single-pass `simd_sum` collective. -/
structure SimdSumSample where
  declTy   : Option MSLType
  dst      : String
  inferred : MSLType
  locals   : MSLLocals
  tail     : List MSLStmt

/-- Pass 1 of `simd_sum`: evaluate `srcExpr` once per active lane in `sgId`, threading `curLog`
    and accumulating the reduced sum. Structural on the thread list. -/
def collectSimdSum (g : MSLGroupState) (sgId : Nat) (sumTy : MSLType) (curLog : List MSLAccess) :
    List MSLThreadState →
      MSLOutcome (List (Dim3 × SimdSumSample) × BitVec 64 × List MSLAccess)
  | [] => .ok ([], 0#64, curLog)
  | th :: rest =>
    if !th.halted && simdgroupOf g.groupDim th.tid == sgId then
      match th.stmts with
      | .simdSum declTy dst srcExpr :: tail =>
        let cf := effectiveCalleeFuel g
        match evalExprWithCall kernelCallEval cf g th.tid th.locals curLog srcExpr with
        | .ok es =>
          let inferred := inferExprType g es.locals srcExpr
          let sample : SimdSumSample :=
            { declTy, dst, inferred, locals := es.locals, tail }
          match collectSimdSum g sgId sumTy es.log rest with
          | .ok (samples, acc, log') =>
            .ok ((th.tid, sample) :: samples, addSimdValues sumTy es.value acc, log')
          | err => err
        | err => propagateErr err
      | _ => .barrierDivergence
    else
      collectSimdSum g sgId sumTy curLog rest

/-- Pass 2 of `simd_sum`: write the reduced `total` into each active lane's `dst` without
    re-evaluating `srcExpr`. Structural on the thread list. -/
def distributeSimdSum (g : MSLGroupState) (sgId : Nat)
    (samples : List (Dim3 × SimdSumSample)) (total : BitVec 64) :
    List MSLThreadState → List MSLThreadState
  | [] => []
  | th :: rest =>
    let rest' := distributeSimdSum g sgId samples total rest
    if !th.halted && simdgroupOf g.groupDim th.tid == sgId then
      match samples.lookup th.tid with
      | some sm =>
        let ty := sm.declTy.getD ((sm.locals.lookupType? sm.dst).getD sm.inferred)
        let ls := sm.locals.setTyped sm.dst ty (maskForType ty total)
        { th with locals := ls, stmts := sm.tail } :: rest'
      | none => th :: rest'
    else
      th :: rest'

/-- Resolve one simdgroup collective across all live lanes in simdgroup `sgId` in a single
    expression-evaluation pass (preserving side effects and epoch-log entries once per lane).
    Traps with `.barrierDivergence` if any live lane in `sgId` is at a different statement. -/
def stepSimdgroup (g : MSLGroupState) (sgId : Nat) : MSLOutcome MSLGroupState :=
  let liveInSg := g.threads.filter (fun th => !th.halted && simdgroupOf g.groupDim th.tid == sgId)
  match liveInSg with
  | [] => .barrierDivergence
  | leader :: _ =>
    match leader.stmts with
    | .simdShuffleXor _ _ _ _ :: _ =>
      match collectSimdShuffle g sgId g.epochLog g.threads with
      | .ok (samples, laneVals, log') =>
        let threads' := distributeSimdShuffle g sgId samples laneVals g.threads
        .ok { g with threads := threads', epochLog := log' }
      | err => propagateErr err
    | .simdSum _ _ leaderSrc :: _ =>
      let sumTy := inferExprType g leader.locals leaderSrc
      match collectSimdSum g sgId sumTy g.epochLog g.threads with
      | .ok (samples, total, log') =>
        let threads' := distributeSimdSum g sgId samples total g.threads
        .ok { g with threads := threads', epochLog := log' }
      | err => propagateErr err
    | _ => .barrierDivergence

/-- Advance the first non-halted thread not parked on a barrier or simd collective. -/
def stepFirstReadyThread (g : MSLGroupState) :
    List MSLThreadState → List MSLThreadState → MSLOutcome (Bool × MSLGroupState)
  | _, [] => .ok (false, g)
  | prefixRev, th :: suffix =>
    if th.halted || threadAtBarrier th || threadAtSimdOp th then
      stepFirstReadyThread g (th :: prefixRev) suffix
    else
      match th.stmts with
      | [] =>
        let th' := { th with halted := true }
        .ok (true, { g with threads := prefixRev.reverse ++ (th' :: suffix) })
      | stmt :: rest =>
        match execNonBarrierStmt g th stmt rest with
        | .ok (th', g') =>
          .ok (true, { g' with threads := prefixRev.reverse ++ (th' :: suffix) })
        | err => propagateErr err

/-- Single SIMT threadgroup step:
    1. If all threads have halted, report completion (`done = true`).
    2. Otherwise, step the next ready non-barrier, non-collective thread.
    3. Once every non-halted thread is parked, execute a ready simdgroup collective if present,
       otherwise synchronize `stepGroupBarrier` in lockstep. -/
def stepGroup (g : MSLGroupState) : MSLOutcome (Bool × MSLGroupState) :=
  if g.threads.all (·.halted) then
    .ok (true, g)
  else
    match stepFirstReadyThread g [] g.threads with
    | .ok (true, g') => .ok (false, g')
    | .ok (false, g') =>
      match g'.threads.find? (fun th => !th.halted && threadAtSimdOp th) with
      | some th =>
        match stepSimdgroup g' (simdgroupOf g'.groupDim th.tid) with
        | .ok synced => .ok (false, synced)
        | err => propagateErr err
      | none =>
        match stepGroupBarrier g' with
        | .ok synced => .ok (false, synced)
        | err => propagateErr err
    | err => propagateErr err

/-- Multi-step SIMT threadgroup evaluator with monotone step budget `fuel`. -/
def runGroup (fuel : Nat) (g : MSLGroupState) : MSLOutcome MSLGroupState :=
  match fuel with
  | 0 =>
    if g.threads.all (·.halted) then .ok g else .fuelExhausted
  | f + 1 =>
    match stepGroup g with
    | .ok (true, g') => .ok g'
    | .ok (false, g') => runGroup f g'
    | err => propagateErr err

/-- Build kernel parameter and `threadgroup` shared-array bindings for an `MSLKernelDecl`. -/
def buildKernelBindings (k : MSLKernelDecl) : List (String × MSLBufferBinding) :=
  let paramBindings := k.params.filterMap fun p =>
    match p.attr, p.ty with
    | some (.buffer idx), .pointer .device isConst elemTy =>
      some (p.name, .deviceBuf idx isConst elemTy)
    | some (.buffer idx), .pointer .constant _ elemTy =>
      some (p.name, .constantBuf idx elemTy)
    | some (.buffer idx), .ref .constant elemTy =>
      some (p.name, .constantScalar idx elemTy)
    | some (.buffer _), .pointer .threadgroup _ elemTy =>
      some (p.name, .threadgroupArr p.name elemTy)
    | _, _ => none
  let sharedBindings := k.sharedDecls.map fun s =>
    (s.name, .threadgroupArr s.name s.elemTy)
  paramBindings ++ sharedBindings

/-- Bind `.x`, `.y`, `.z` coordinate fields (and scalar `.x`) for a builtin parameter. -/
def initBuiltinLocal (ls : MSLLocals) (name : String) (ty : MSLType)
    (coords : Nat × Nat × Nat) : MSLLocals :=
  let (cx, cy, cz) := coords
  let fty := structFieldType [] ty "x"
  let xBv := maskForType fty (BitVec.ofNat 64 cx)
  let yBv := maskForType fty (BitVec.ofNat 64 cy)
  let zBv := maskForType fty (BitVec.ofNat 64 cz)
  let ls1 := ls.setTyped name ty (maskForType ty (BitVec.ofNat 64 cx))
  let ls2 := ls1.setField name "x" xBv
  let ls3 := ls2.setField name "y" yBv
  ls3.setField name "z" zBv

/-- Initialize per-lane builtin coordinate locals declared on `k.params`. -/
def initThreadLocals (k : MSLKernelDecl) (g : MSLGroupState) (tid : Dim3) : MSLLocals :=
  k.params.foldl (fun acc p =>
    match p.attr with
    | some (.buffer _) | none => acc
    | some attr => initBuiltinLocal acc p.name p.ty (evalBuiltinCoords g tid attr)) MSLLocals.empty

/-- Initialize a fresh `MSLGroupState` for threadgroup coordinate `groupId`. -/
def initGroupState (k : MSLKernelDecl) (gridDim groupDim groupId : Dim3)
    (deviceBuffers constantBuffers : List (Nat × ByteMemory))
    (funcs : List MSLFuncDecl := []) (structs : List MSLStructDecl := [])
    (fuelBudget : Nat := 0) : MSLGroupState :=
  let bindings := buildKernelBindings k
  let tgArrays := k.sharedDecls.map fun s =>
    (s.name, ByteMemory.zeros (s.count * aggregateByteWidth structs s.elemTy))
  let g0 : MSLGroupState :=
    { gridDim, groupDim, groupId, structs, funcs, bindings
      deviceBuffers, constantBuffers
      threadgroupArrays := tgArrays
      epochLog := []
      threads := []
      fuelBudget }
  let threads := groupDim.coords.map fun tid =>
    { tid := tid
      locals := initThreadLocals k g0 tid
      stmts := k.body
      halted := false }
  { g0 with threads }

/-- Run `evalMSLKernel` across a list of threadgroup coordinates, threading `deviceBuffers`.
    Structural on the coordinate list. -/
def evalMSLKernelLoop (fuelPerGroup : Nat) (k : MSLKernelDecl) (gridDim groupDim : Dim3)
    (constantBuffers : List (Nat × ByteMemory))
    (funcs : List MSLFuncDecl) (structs : List MSLStructDecl)
    (devBufs : List (Nat × ByteMemory)) :
    List Dim3 → MSLOutcome (List (Nat × ByteMemory))
  | [] => .ok devBufs
  | gid :: rest =>
    let g0 := initGroupState k gridDim groupDim gid devBufs constantBuffers funcs structs fuelPerGroup
    match runGroup fuelPerGroup g0 with
    | .ok gFinal => evalMSLKernelLoop fuelPerGroup k gridDim groupDim constantBuffers funcs structs
        gFinal.deviceBuffers rest
    | err => propagateErr err

/-- Launch an `MSLKernelDecl` across every threadgroup in `gridDim` (each with fresh zeroed
    `threadgroup` shared arrays and immutable `constantBuffers`), threading `deviceBuffers`
    across threadgroups and returning the final `device` buffer table. -/
def evalMSLKernel (fuelPerGroup : Nat) (k : MSLKernelDecl) (gridDim groupDim : Dim3)
    (deviceBuffers constantBuffers : List (Nat × ByteMemory))
    (funcs : List MSLFuncDecl := []) (structs : List MSLStructDecl := []) :
    MSLOutcome (List (Nat × ByteMemory)) :=
  evalMSLKernelLoop fuelPerGroup k gridDim groupDim constantBuffers funcs structs
    deviceBuffers gridDim.coords

/-! ## 2. 1:1 Structural Pretty-Printer (`MSLModule -> String`) -/

/-- Render an `MSLAddressSpace` qualifier token. -/
def ppMSLAddressSpace : MSLAddressSpace → String
  | .device      => "device"
  | .constant    => "constant"
  | .thread      => "thread"
  | .threadgroup => "threadgroup"

/-- Render an `MSLType` into valid Metal Shading Language syntax. -/
def ppMSLType : MSLType → String
  | .void                  => "void"
  | .bool                  => "bool"
  | .uchar                 => "uchar"
  | .ushort                => "ushort"
  | .uint                  => "uint"
  | .int                   => "int"
  | .ulong                 => "ulong"
  | .long                  => "long"
  | .half                  => "half"
  | .float                 => "float"
  | .double                => "double"
  | .uint2                 => "uint2"
  | .uint3                 => "uint3"
  | .uint4                 => "uint4"
  | .ulong2                => "ulong2"
  | .atomicUint            => "atomic_uint"
  | .u256                  => "ln_u256"
  | .pointer sp isConst el =>
    if isConst && sp != .constant then
      ppMSLAddressSpace sp ++ " const " ++ ppMSLType el ++ "*"
    else
      ppMSLAddressSpace sp ++ " " ++ ppMSLType el ++ "*"
  | .ref sp elem           => ppMSLAddressSpace sp ++ " " ++ ppMSLType elem ++ "&"
  | .threadArr isConst el n =>
    if isConst then "thread const " ++ ppMSLType el ++ s!"[{n}]"
    else "thread " ++ ppMSLType el ++ s!"[{n}]"
  | .structTy name         => name

/-- Render an `MSLAttr` inside `[[...]]`. -/
def ppMSLAttr : MSLAttr → String
  | .buffer idx                  => s!"buffer({idx})"
  | .threadPositionInGrid        => "thread_position_in_grid"
  | .threadPositionInThreadgroup => "thread_position_in_threadgroup"
  | .threadgroupPositionInGrid   => "threadgroup_position_in_grid"
  | .threadsPerThreadgroup       => "threads_per_threadgroup"
  | .threadIndexInSimdgroup      => "thread_index_in_simdgroup"
  | .simdgroupIndexInThreadgroup => "simdgroup_index_in_threadgroup"

def hexDigitMSL (n : Nat) : Char :=
  match n % 16 with
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3'
  | 4 => '4' | 5 => '5' | 6 => '6' | 7 => '7'
  | 8 => '8' | 9 => '9' | 10 => 'A' | 11 => 'B'
  | 12 => 'C' | 13 => 'D' | 14 => 'E' | _ => 'F'

def hexNibblesMSL (v : Nat) : Nat → List Char
  | 0 => []
  | k + 1 => hexDigitMSL (v >>> (k * 4)) :: hexNibblesMSL v k

/- Render an `MSLExpr` (and mutually `MSLExprList`) into valid MSL 3.0 expression syntax. -/
mutual
def ppMSLExpr : MSLExpr → String
  | .var name         => name
  | .immU64 v         => s!"{v.toNat}UL"
  | .immBool b        => if b then "true" else "false"
  | .immF16 bits      =>
    let h := String.ofList (hexNibblesMSL bits.toNat 4)
    s!"as_type<half>((ushort)0x{h}u)"
  | .immF32 bits      =>
    let h := String.ofList (hexNibblesMSL bits.toNat 8)
    s!"as_type<float>(0x{h}u)"
  | .immF64 bits      =>
    let h := String.ofList (hexNibblesMSL bits.toNat 16)
    s!"as_type<double>(0x{h}UL)"
  | .fieldAccess e f  => s!"{ppMSLExpr e}.{f}"
  | .structLit ty args =>
    let items := String.intercalate ", " (ppMSLExprList args)
    if ty.isVector then ppMSLType ty ++ "(" ++ items ++ ")"
    else "{ " ++ items ++ " }"
  | .bitNot a         => s!"(~{ppMSLExpr a})"
  | .logNot a         => s!"(!{ppMSLExpr a})"
  | .neg a            => s!"(-{ppMSLExpr a})"
  | .clz a            => s!"clz({ppMSLExpr a})"
  | .deref ptr        => s!"(*{ptr})"
  | .cast ty a        => s!"(({ppMSLType ty}){ppMSLExpr a})"
  | .add a b          => s!"({ppMSLExpr a} + {ppMSLExpr b})"
  | .sub a b          => s!"({ppMSLExpr a} - {ppMSLExpr b})"
  | .mul a b          => s!"({ppMSLExpr a} * {ppMSLExpr b})"
  | .div a b          => s!"({ppMSLExpr a} / {ppMSLExpr b})"
  | .rem a b          => s!"({ppMSLExpr a} % {ppMSLExpr b})"
  | .bitAnd a b       => s!"({ppMSLExpr a} & {ppMSLExpr b})"
  | .bitOr a b        => s!"({ppMSLExpr a} | {ppMSLExpr b})"
  | .bitXor a b       => s!"({ppMSLExpr a} ^ {ppMSLExpr b})"
  | .shl a b          => s!"({ppMSLExpr a} << {ppMSLExpr b})"
  | .shr a b          => s!"({ppMSLExpr a} >> {ppMSLExpr b})"
  | .logAnd a b       => s!"({ppMSLExpr a} && {ppMSLExpr b})"
  | .logOr a b        => s!"({ppMSLExpr a} || {ppMSLExpr b})"
  | .eq a b           => s!"({ppMSLExpr a} == {ppMSLExpr b})"
  | .ne a b           => s!"({ppMSLExpr a} != {ppMSLExpr b})"
  | .lt a b           => s!"({ppMSLExpr a} < {ppMSLExpr b})"
  | .le a b           => s!"({ppMSLExpr a} <= {ppMSLExpr b})"
  | .gt a b           => s!"({ppMSLExpr a} > {ppMSLExpr b})"
  | .ge a b           => s!"({ppMSLExpr a} >= {ppMSLExpr b})"
  | .select c t f     => s!"({ppMSLExpr c} ? {ppMSLExpr t} : {ppMSLExpr f})"
  | .builtinSelect f t c =>
    s!"select({ppMSLExpr f}, {ppMSLExpr t}, {ppMSLExpr c})"
  | .fma a b c        => s!"fma({ppMSLExpr a}, {ppMSLExpr b}, {ppMSLExpr c})"
  | .index arr idx    => s!"{arr}[{ppMSLExpr idx}]"
  | .call fn args     =>
    let items := String.intercalate ", " (ppMSLExprList args)
    s!"{fn}({items})"

def ppMSLExprList : MSLExprList → List String
  | .nil => []
  | .cons e rest => ppMSLExpr e :: ppMSLExprList rest
end

def ppOptDeclPrefix (declTy : Option MSLType) (dst : String) : String :=
  match declTy with
  | some ty => ppMSLType ty ++ " " ++ dst ++ " = "
  | none => dst ++ " = "

def ppAtomicPtrArg (target : String) : Option MSLExpr → String
  | some idx => "&" ++ target ++ "[" ++ ppMSLExpr idx ++ "]"
  | none => target

/- Render an `MSLStmt` (and mutually `MSLBlock`) with indentation `indent`. -/
mutual
def ppMSLStmt (indent : String := "    ") : MSLStmt → String
  | .varDecl ty name rhs =>
    indent ++ ppMSLType ty ++ " " ++ name ++ " = " ++ ppMSLExpr rhs ++ ";"
  | .arrayDecl elemTy name count initList =>
    let items := ppMSLExprList initList
    if items.isEmpty then
      indent ++ ppMSLType elemTy ++ " " ++ name ++ s!"[{count}];"
    else
      indent ++ ppMSLType elemTy ++ " " ++ name ++ s!"[{count}] = \{ " ++
        String.intercalate ", " items ++ " };"
  | .assign name rhs =>
    indent ++ name ++ " = " ++ ppMSLExpr rhs ++ ";"
  | .fieldAssign varName field rhs =>
    indent ++ varName ++ "." ++ field ++ " = " ++ ppMSLExpr rhs ++ ";"
  | .indexAssign target idx rhs =>
    indent ++ target ++ "[" ++ ppMSLExpr idx ++ "] = " ++ ppMSLExpr rhs ++ ";"
  | .derefAssign ptrName rhs =>
    indent ++ "*" ++ ptrName ++ " = " ++ ppMSLExpr rhs ++ ";"
  | .callAssign declTy dst fnName args =>
    let items := String.intercalate ", " (ppMSLExprList args)
    indent ++ ppOptDeclPrefix declTy dst ++ fnName ++ "(" ++ items ++ ");"
  | .exprStmt e =>
    indent ++ ppMSLExpr e ++ ";"
  | .atomicFetchAdd declTy dst target idxOpt val =>
    let callStr :=
      "atomic_fetch_add_explicit(" ++ ppAtomicPtrArg target idxOpt ++ ", " ++
      ppMSLExpr val ++ ", memory_order_relaxed)"
    match dst with
    | none => indent ++ callStr ++ ";"
    | some d => indent ++ ppOptDeclPrefix declTy d ++ callStr ++ ";"
  | .atomicExchange declTy dst target idxOpt val =>
    let callStr :=
      "atomic_exchange_explicit(" ++ ppAtomicPtrArg target idxOpt ++ ", " ++
      ppMSLExpr val ++ ", memory_order_relaxed)"
    match dst with
    | none => indent ++ callStr ++ ";"
    | some d => indent ++ ppOptDeclPrefix declTy d ++ callStr ++ ";"
  | .simdShuffleXor declTy dst src mask =>
    indent ++ ppOptDeclPrefix declTy dst ++
      "simd_shuffle_xor(" ++ ppMSLExpr src ++ ", " ++ ppMSLExpr mask ++ ");"
  | .simdSum declTy dst src =>
    indent ++ ppOptDeclPrefix declTy dst ++ "simd_sum(" ++ ppMSLExpr src ++ ");"
  | .ifElse cond thenBr elseBr =>
    let tb := String.intercalate "\n" (ppMSLBlockLines (indent ++ "    ") thenBr)
    let fb := String.intercalate "\n" (ppMSLBlockLines (indent ++ "    ") elseBr)
    if elseBr.isEmpty then
      indent ++ "if (" ++ ppMSLExpr cond ++ ") {\n" ++ tb ++ "\n" ++ indent ++ "}"
    else
      indent ++ "if (" ++ ppMSLExpr cond ++ ") {\n" ++ tb ++ "\n" ++ indent ++
        "} else {\n" ++ fb ++ "\n" ++ indent ++ "}"
  | .forLoop loopVar ty initExpr condExpr stepExpr body =>
    let bb := String.intercalate "\n" (ppMSLBlockLines (indent ++ "    ") body)
    let hdr :=
      ppMSLType ty ++ " " ++ loopVar ++ " = " ++ ppMSLExpr initExpr ++ "; " ++
      ppMSLExpr condExpr ++ "; " ++ loopVar ++ " = " ++ ppMSLExpr stepExpr
    indent ++ "for (" ++ hdr ++ ") {\n" ++ bb ++ "\n" ++ indent ++ "}"
  | .whileLoop condExpr body =>
    let bb := String.intercalate "\n" (ppMSLBlockLines (indent ++ "    ") body)
    indent ++ "while (" ++ ppMSLExpr condExpr ++ ") {\n" ++ bb ++ "\n" ++ indent ++ "}"
  | .threadgroupBarrier =>
    indent ++ "threadgroup_barrier(mem_flags::mem_threadgroup)" ++ ";"
  | .returnVal e =>
    indent ++ "return " ++ ppMSLExpr e ++ ";"
  | .returnStmt =>
    indent ++ "return" ++ ";"

def ppMSLBlockLines (indent : String) : MSLBlock → List String
  | .nil => []
  | .cons s rest => ppMSLStmt indent s :: ppMSLBlockLines indent rest
end

/-- Render a kernel or helper parameter declaration. -/
def ppMSLParam (p : MSLParamDecl) : String :=
  match p.ty with
  | .threadArr isConst elemTy count =>
    let qual := if isConst then "thread const " else "thread "
    qual ++ ppMSLType elemTy ++ " " ++ p.name ++ s!"[{count}]"
  | _ =>
    match p.attr with
    | some attr => "    " ++ ppMSLType p.ty ++ " " ++ p.name ++ " [[" ++ ppMSLAttr attr ++ "]]"
    | none      => ppMSLType p.ty ++ " " ++ p.name

/-- Render a `threadgroup` shared array declaration inside a kernel body. -/
def ppMSLThreadgroupDecl (d : MSLThreadgroupDecl) : String :=
  s!"    threadgroup {ppMSLType d.elemTy} {d.name}[{d.count}];"

/-- Render a top-level MSL `struct` definition. -/
def ppMSLStructDecl (s : MSLStructDecl) : String :=
  let fields := String.intercalate " " (s.fields.map fun f => ppMSLType f.ty ++ " " ++ f.name ++ ";")
  "struct " ++ s.name ++ " { " ++ fields ++ " };"

/-- Render a top-level MSL `inline` helper function declaration. -/
def ppMSLFuncDecl (fn : MSLFuncDecl) : String :=
  let inlinePref := if fn.inline then "inline " else ""
  let params := String.intercalate ", " (fn.params.map ppMSLParam)
  let body := String.intercalate "\n" (ppMSLBlockLines "    " fn.body)
  inlinePref ++ ppMSLType fn.retTy ++ " " ++ fn.name ++ "(" ++ params ++ ") {\n" ++ body ++ "\n}"

/-- Canonical `kernel void <name>(\n` signature prefix of a rendered Metal kernel. -/
def ppMSLKernelSignaturePrefix (name : String) : String :=
  "kernel void " ++ name ++ "(\n"

/-- Render a `kernel void` Metal compute function. -/
def ppMSLKernel (k : MSLKernelDecl) : String :=
  let paramLines := String.intercalate ",\n" (k.params.map ppMSLParam)
  let sharedLines := k.sharedDecls.map ppMSLThreadgroupDecl
  let bodyLines := k.body.map (ppMSLStmt "    ")
  let inner := String.intercalate "\n" (sharedLines ++ bodyLines)
  ppMSLKernelSignaturePrefix k.name ++ paramLines ++ "\n) {\n" ++ inner ++ "\n}"

/-- Canonical MSL 3.0 standard library include & namespace header. -/
def ppMSLModuleHeader : String :=
  "#include <metal_stdlib>\nusing namespace metal;"

/-- Render a complete `MSLModule` with `#include <metal_stdlib>`, `using namespace metal;`,
    optional `struct` declarations, helper functions, and all `kernel void` entry points. -/
def ppMSLModule (m : MSLModule) : String :=
  let blocks :=
    (m.structs.map ppMSLStructDecl) ++
    (m.funcs.map ppMSLFuncDecl) ++
    (m.kernels.map ppMSLKernel)
  match blocks with
  | [] => ppMSLModuleHeader ++ "\n"
  | bs => ppMSLModuleHeader ++ "\n\n" ++ String.intercalate "\n\n" bs ++ "\n"

end LeanNative.Backend.MetalAst
