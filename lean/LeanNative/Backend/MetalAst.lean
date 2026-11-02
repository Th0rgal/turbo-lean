/-!
# Genuine Apple Metal MSL 3.0 AST, Independent SIMT Semantics & 1:1 Pretty-Printer (`C2b`)

Provides:
1. Typed Metal Shading Language (MSL 3.0) compute AST (`MSLAddressSpace`, `MSLType`, `MSLAttr`,
   `MSLExpr`, `MSLStmt`, `MSLParamDecl`, `MSLThreadgroupDecl`, `MSLStructDecl`, `MSLKernelDecl`,
   `MSLModule`) covering every construct emitted by production Metal lowering (`device`,
   `constant`, `thread`, `threadgroup` address spaces; `buffer(n)`, `thread_position_in_grid`,
   `thread_position_in_threadgroup`, `threadgroup_position_in_grid`, `threads_per_threadgroup`
   attributes; scalar/pointer/reference/struct types; `varDecl`, `assign`, `indexAssign`,
   `ifElse`, `forLoop`, `whileLoop`, `threadgroupBarrier`, `returnStmt`).
2. Independent SIMT threadgroup operational semantics (`BitVec`-backed per-lane evaluation,
   separated `device` buffer table, read-only `constant` buffer table rejecting writes with
   `MSLOutcome.readOnlyViolation`, per-threadgroup shared arrays, byte/element bounds checks, and
   lockstep `threadgroup_barrier(mem_flags::mem_threadgroup)` synchronization catching divergent
   barrier execution via `MSLOutcome.barrierDivergence`), with zero imports or calls to
   `LeanNative.Semantics.Eval`.
3. 1:1 structural pretty-printer (`ppMSLAddressSpace`, `ppMSLType`, `ppMSLAttr`, `ppMSLExpr`,
   `ppMSLStmt`, `ppMSLKernel`, `ppMSLModule`) emitting `#include <metal_stdlib>`,
   `using namespace metal;`, and `kernel void ...`.
4. Kernel-checked theorems (`0 sorryAx`, `strict-proofs` clean) for `constant` address-space
   immutability (`exec_preserves_constant_buffers`, `runGroup_preserves_constant_buffers`,
   `constant_write_rejected`), `device` vs `threadgroup` isolation, out-of-bounds buffer write
   detection (`oob_device_write_caught`), uniform vs divergent `threadgroupBarrier`
   synchronization, fuel-independent determinism, and pretty-printer injectivity/header lemmas.
-/

namespace LeanNative.Backend.MetalAst

/-! ## 1. Typed Metal Shading Language (MSL 3.0) AST -/

/-- Metal Shading Language address spaces. -/
inductive MSLAddressSpace where
  | device
  | constant
  | thread
  | threadgroup
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Metal Shading Language scalar, pointer, reference, and struct types. -/
inductive MSLType where
  | void
  | bool
  | uchar
  | ushort
  | uint
  | int
  | ulong
  | long
  | half
  | float
  | double
  | uint2
  | uint3
  | uint4
  | ulong2
  | atomicUint
  | u256
  | pointer  : MSLAddressSpace → Bool → MSLType → MSLType
  | ref      : MSLAddressSpace → MSLType → MSLType
  | structTy : String → MSLType
  deriving Repr, DecidableEq, Inhabited, BEq

namespace MSLType

/-- Addressable byte width of an MSL type (`0` for `void`, `8` for pointers/references). -/
def byteWidth : MSLType → Nat
  | .void => 0
  | .bool | .uchar => 1
  | .ushort | .half => 2
  | .uint | .int | .float | .atomicUint => 4
  | .ulong | .long | .double | .uint2 | .pointer _ _ _ | .ref _ _ => 8
  | .uint3 => 12
  | .uint4 | .ulong2 => 16
  | .u256 => 32
  | .structTy _ => 8

/-- Scalar bit width used for width masking, sign-extension, and shift bounds. -/
def bitWidth : MSLType → Nat
  | .void => 0
  | .bool | .uchar => 8
  | .ushort | .half => 16
  | .uint | .int | .float | .atomicUint => 32
  | .ulong | .long | .double | .uint2 | .uint3 | .uint4 | .ulong2
  | .u256 | .pointer _ _ _ | .ref _ _ | .structTy _ => 64

/-- True when signed integer rules apply to arithmetic/shifts/comparisons. -/
def isSigned : MSLType → Bool
  | .int | .long => true
  | _ => false

/-- True for IEEE-754 floating-point scalar types (`.half`, `.float`, `.double`). -/
def isFloat : MSLType → Bool
  | .half | .float | .double => true
  | _ => false

end MSLType

/-- Metal kernel parameter and thread/grid coordinate attributes (`[[...]]`). -/
inductive MSLAttr where
  | buffer                      : Nat → MSLAttr
  | threadPositionInGrid        : MSLAttr
  | threadPositionInThreadgroup : MSLAttr
  | threadgroupPositionInGrid   : MSLAttr
  | threadsPerThreadgroup       : MSLAttr
  | threadIndexInSimdgroup      : MSLAttr
  | simdgroupIndexInThreadgroup : MSLAttr
  deriving Repr, DecidableEq, Inhabited, BEq

/- Typed MSL expression AST (and argument lists `MSLExprList` mutually so `MSLExpr` stays
   non-nested for `TurboLean.KernelGate`). -/
mutual
inductive MSLExpr where
  | var           : String → MSLExpr
  | immU64        : BitVec 64 → MSLExpr
  | immBool       : Bool → MSLExpr
  | immF16        : BitVec 16 → MSLExpr
  | immF32        : BitVec 32 → MSLExpr
  | immF64        : BitVec 64 → MSLExpr
  | fieldAccess   : MSLExpr → String → MSLExpr
  | structLit     : MSLType → MSLExprList → MSLExpr
  | bitNot        : MSLExpr → MSLExpr
  | logNot        : MSLExpr → MSLExpr
  | neg           : MSLExpr → MSLExpr
  | clz           : MSLExpr → MSLExpr
  | cast          : MSLType → MSLExpr → MSLExpr
  | add           : MSLExpr → MSLExpr → MSLExpr
  | sub           : MSLExpr → MSLExpr → MSLExpr
  | mul           : MSLExpr → MSLExpr → MSLExpr
  | div           : MSLExpr → MSLExpr → MSLExpr
  | rem           : MSLExpr → MSLExpr → MSLExpr
  | bitAnd        : MSLExpr → MSLExpr → MSLExpr
  | bitOr         : MSLExpr → MSLExpr → MSLExpr
  | bitXor        : MSLExpr → MSLExpr → MSLExpr
  | shl           : MSLExpr → MSLExpr → MSLExpr
  | shr           : MSLExpr → MSLExpr → MSLExpr
  | eq            : MSLExpr → MSLExpr → MSLExpr
  | ne            : MSLExpr → MSLExpr → MSLExpr
  | lt            : MSLExpr → MSLExpr → MSLExpr
  | le            : MSLExpr → MSLExpr → MSLExpr
  | gt            : MSLExpr → MSLExpr → MSLExpr
  | ge            : MSLExpr → MSLExpr → MSLExpr
  | select        : MSLExpr → MSLExpr → MSLExpr → MSLExpr
  | builtinSelect : MSLExpr → MSLExpr → MSLExpr → MSLExpr
  | fma           : MSLExpr → MSLExpr → MSLExpr → MSLExpr
  | index         : String → MSLExpr → MSLExpr
  | call          : String → MSLExprList → MSLExpr
  deriving Repr, DecidableEq, Inhabited, BEq

inductive MSLExprList where
  | nil  : MSLExprList
  | cons : MSLExpr → MSLExprList → MSLExprList
  deriving Repr, DecidableEq, Inhabited, BEq
end

namespace MSLExprList

def ofList : List MSLExpr → MSLExprList
  | [] => .nil
  | e :: rest => .cons e (ofList rest)

def toList : MSLExprList → List MSLExpr
  | .nil => []
  | .cons e rest => e :: toList rest

end MSLExprList

/- Structured MSL statement AST covering compute kernels, loops, conditionals, helper functions,
   simdgroup collectives, atomics, and barriers.
   Contains `MSLBlock` mutually rather than `List MSLStmt` so `MSLStmt` is a non-nested inductive
   compatible with `TurboLean.KernelGate` theorem-shard audits. -/
mutual
inductive MSLStmt where
  | varDecl         : MSLType → String → MSLExpr → MSLStmt
  | assign          : String → MSLExpr → MSLStmt
  | fieldAssign     : String → String → MSLExpr → MSLStmt
  | indexAssign     : String → MSLExpr → MSLExpr → MSLStmt
  | callAssign      : Option MSLType → String → String → MSLExprList → MSLStmt
  | exprStmt        : MSLExpr → MSLStmt
  | atomicFetchAdd  : Option MSLType → Option String → String → MSLExpr → MSLExpr → MSLStmt
  | simdShuffleXor  : Option MSLType → String → MSLExpr → MSLExpr → MSLStmt
  | simdSum         : Option MSLType → String → MSLExpr → MSLStmt
  | ifElse          : MSLExpr → MSLBlock → MSLBlock → MSLStmt
  | forLoop         : String → MSLType → MSLExpr → MSLExpr → MSLExpr → MSLBlock → MSLStmt
  | whileLoop       : MSLExpr → MSLBlock → MSLStmt
  | threadgroupBarrier : MSLStmt
  | returnVal       : MSLExpr → MSLStmt
  | returnStmt      : MSLStmt
  deriving Repr, DecidableEq, Inhabited, BEq

inductive MSLBlock where
  | nil  : MSLBlock
  | cons : MSLStmt → MSLBlock → MSLBlock
  deriving Repr, DecidableEq, Inhabited, BEq
end

namespace MSLBlock

/-- Convert a `List MSLStmt` into an `MSLBlock`. -/
def ofList : List MSLStmt → MSLBlock
  | [] => .nil
  | s :: rest => .cons s (ofList rest)

/-- Convert an `MSLBlock` into a `List MSLStmt`. -/
def toList : MSLBlock → List MSLStmt
  | .nil => []
  | .cons s rest => s :: toList rest

/-- True iff `MSLBlock` has zero statements. -/
def isEmpty : MSLBlock → Bool
  | .nil => true
  | .cons _ _ => false

/-- Concatenate two `MSLBlock` statement sequences. -/
def append : MSLBlock → MSLBlock → MSLBlock
  | .nil, ys => ys
  | .cons s rest, ys => .cons s (append rest ys)

end MSLBlock

/-- Kernel or helper function parameter declaration (`<ty> <name> [[<attr>]]` or `<ty> <name>`). -/
structure MSLParamDecl where
  ty   : MSLType
  name : String
  attr : Option MSLAttr := none
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Per-threadgroup shared array declaration (`threadgroup <elemTy> <name>[<count>];`). -/
structure MSLThreadgroupDecl where
  elemTy : MSLType
  name   : String
  count  : Nat
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Struct field declaration for MSL `struct` definitions (such as `ln_u256`). -/
structure MSLStructField where
  ty   : MSLType
  name : String
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Top-level MSL `struct` declaration. -/
structure MSLStructDecl where
  name   : String
  fields : List MSLStructField
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Metal `kernel void` compute function declaration. -/
structure MSLKernelDecl where
  name        : String
  params      : List MSLParamDecl
  sharedDecls : List MSLThreadgroupDecl := []
  body        : List MSLStmt
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Metal function declaration (`inline <ret> <name>(...)`). -/
structure MSLFuncDecl where
  inline : Bool := true
  retTy  : MSLType
  name   : String
  params : List MSLParamDecl
  body   : MSLBlock
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Complete Apple Metal MSL 3.0 module. -/
structure MSLModule where
  structs : List MSLStructDecl := []
  funcs   : List MSLFuncDecl := []
  kernels : List MSLKernelDecl
  deriving Repr, DecidableEq, Inhabited, BEq

/-! ## 2. Independent SIMT Threadgroup Operational Semantics -/

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

private def readLEAux (m : ByteMemory) (addr : Nat) : Nat → Option (BitVec 64)
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

private def writeLEAux (bs : Array UInt8) (addr : Nat) (val : BitVec 64) : Nat → Array UInt8
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

/-- Build a `ByteMemory` from a list of 64-bit little-endian words. -/
def ofU64Words (words : List (BitVec 64)) : ByteMemory :=
  let empty := Array.replicate (words.length * 8) (0 : UInt8)
  let rec fill (bs : Array UInt8) (idx : Nat) : List (BitVec 64) → Array UInt8
    | [] => bs
    | w :: rest => fill (writeLEAux bs (idx * 8) w 8) (idx + 1) rest
  { bytes := fill empty 0 words }

/-- Read a 64-bit little-endian word at element index `elemIdx`. -/
def readU64Word? (m : ByteMemory) (elemIdx : Nat) : Option (BitVec 64) :=
  m.loadBits (elemIdx * 8) 8

/-- Build a `ByteMemory` from a list of 32-bit little-endian words. -/
def ofU32Words (words : List (BitVec 32)) : ByteMemory :=
  let empty := Array.replicate (words.length * 4) (0 : UInt8)
  let rec fill (bs : Array UInt8) (idx : Nat) : List (BitVec 32) → Array UInt8
    | [] => bs
    | w :: rest => fill (writeLEAux bs (idx * 4) (BitVec.setWidth 64 w) 4) (idx + 1) rest
  { bytes := fill empty 0 words }

/-- Read a 32-bit little-endian word at element index `elemIdx`. -/
def readU32Word? (m : ByteMemory) (elemIdx : Nat) : Option (BitVec 32) :=
  (m.loadBits (elemIdx * 4) 4).map (BitVec.setWidth 32)

/-- Build a `ByteMemory` from a list of 16-bit little-endian words (such as IEEE-754 `half`). -/
def ofU16Words (words : List (BitVec 16)) : ByteMemory :=
  let empty := Array.replicate (words.length * 2) (0 : UInt8)
  let rec fill (bs : Array UInt8) (idx : Nat) : List (BitVec 16) → Array UInt8
    | [] => bs
    | w :: rest => fill (writeLEAux bs (idx * 2) (BitVec.setWidth 64 w) 2) (idx + 1) rest
  { bytes := fill empty 0 words }

/-- Read a 16-bit little-endian word at element index `elemIdx`. -/
def readU16Word? (m : ByteMemory) (elemIdx : Nat) : Option (BitVec 16) :=
  (m.loadBits (elemIdx * 2) 2).map (BitVec.setWidth 16)

end ByteMemory

/-- Per-thread local variable environment (`thread` address space) storing typed values
    and multi-word struct/vector fields (`name.field`). -/
structure MSLLocals where
  vars   : List (String × BitVec 64) := []
  types  : List (String × MSLType) := []
  fields : List (String × BitVec 64) := []
  deriving Repr, DecidableEq, Inhabited, BEq

namespace MSLLocals

def empty : MSLLocals := { vars := [], types := [], fields := [] }

def lookup? (ls : MSLLocals) (name : String) : Option (BitVec 64) :=
  ls.vars.lookup name

def lookupType? (ls : MSLLocals) (name : String) : Option MSLType :=
  ls.types.lookup name

def lookupField? (ls : MSLLocals) (varName fieldName : String) : Option (BitVec 64) :=
  ls.fields.lookup (varName ++ "." ++ fieldName)

def setAssoc : List (String × BitVec 64) → String → BitVec 64 → List (String × BitVec 64)
  | [], k, v => [(k, v)]
  | (k', v') :: rest, k, v =>
    if k' == k then (k, v) :: rest else (k', v') :: setAssoc rest k v

def setTypeAssoc : List (String × MSLType) → String → MSLType → List (String × MSLType)
  | [], k, t => [(k, t)]
  | (k', t') :: rest, k, t =>
    if k' == k then (k, t) :: rest else (k', t') :: setTypeAssoc rest k t

def set (ls : MSLLocals) (name : String) (v : BitVec 64) : MSLLocals :=
  { ls with vars := setAssoc ls.vars name v }

def setTyped (ls : MSLLocals) (name : String) (ty : MSLType) (v : BitVec 64) : MSLLocals :=
  { ls with
    vars := setAssoc ls.vars name v
    types := setTypeAssoc ls.types name ty }

def setField (ls : MSLLocals) (varName fieldName : String) (v : BitVec 64) : MSLLocals :=
  { ls with fields := setAssoc ls.fields (varName ++ "." ++ fieldName) v }

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
  tid     : Dim3
  target  : MSLMemTarget
  addr    : Nat
  width   : Nat
  isWrite : Bool
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
  deriving Repr, DecidableEq, Inhabited, BEq

/-- True when two half-open byte ranges overlap. -/
def rangesOverlap (a1 w1 a2 w2 : Nat) : Bool :=
  decide (a1 < a2 + w2 ∧ a2 < a1 + w1)

/-- Scan an epoch log for an unsynchronized cross-thread write-write or read-write overlap
    on the same memory object. -/
def findDataRace? (log : List MSLAccess) (tid : Dim3) (tgt : MSLMemTarget)
    (addr width : Nat) (isWrite : Bool) : Option Nat :=
  let rec go : List MSLAccess → Option Nat
    | [] => none
    | a :: rest =>
      if (tid != a.tid) && (tgt == a.target) &&
          (isWrite || a.isWrite) && rangesOverlap addr width a.addr a.width then
        some (Nat.max addr a.addr)
      else
        go rest
  go log

/-- Record one epoch access, trapping with `.dataRace` on a conflicting prior access. -/
def recordEpochAccess (log : List MSLAccess) (tid : Dim3) (tgt : MSLMemTarget)
    (sp : MSLAddressSpace) (addr width : Nat) (isWrite : Bool) : MSLOutcome (List MSLAccess) :=
  match findDataRace? log tid tgt addr width isWrite with
  | some conflictAddr => .dataRace sp conflictAddr
  | none => .ok ({ tid, target := tgt, addr, width, isWrite } :: log)

/-- Canonical width mask for an MSL scalar type over `BitVec 64`. -/
def maskForType (ty : MSLType) (v : BitVec 64) : BitVec 64 :=
  match ty with
  | .void => 0#64
  | .bool => if v != 0#64 then 1#64 else 0#64
  | .uchar => v &&& 0xFF#64
  | .ushort | .half => v &&& 0xFFFF#64
  | .uint | .int | .float | .atomicUint => v &&& 0xFFFF_FFFF#64
  | .ulong | .long | .double | .uint2 | .uint3 | .uint4 | .ulong2
  | .u256 | .pointer _ _ _ | .ref _ _ | .structTy _ => v

/-- Sign-extend a value whose low `bits` bits are significant into `BitVec 64`. -/
def signExtendTo64 (bits : Nat) (v : BitVec 64) : BitVec 64 :=
  if bits == 0 || bits >= 64 then v
  else
    let lo := v &&& ((1#64 <<< bits) - 1#64)
    if (lo >>> (bits - 1)) &&& 1#64 == 1#64 then
      lo ||| (~~~((1#64 <<< bits) - 1#64))
    else
      lo

/-- Pure IEEE-754 binary16 -> binary32 widening (reduces definitionally in the Lean kernel). -/
def f16BitsToF32Bits (bits16 : BitVec 16) : BitVec 32 :=
  let sign : Nat := (bits16 >>> 15).toNat &&& 1
  let exp16 : Nat := (bits16 >>> 10).toNat &&& 0x1F
  let frac16 : Nat := bits16.toNat &&& 0x3FF
  if exp16 == 0 then
    if frac16 == 0 then
      BitVec.ofNat 32 (sign <<< 31)
    else
      let rec normSub (f : Nat) (e : Nat) : Nat → Nat × Nat
        | 0 => (f, e)
        | k + 1 =>
          if (f &&& 0x400) != 0 then (f &&& 0x3FF, e)
          else normSub (f <<< 1) (e - 1) k
      let (normFrac, exp32) := normSub (frac16 <<< 1) 112 16
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
      let rec normSub (m : Nat) (e : Nat) (fuel : Nat) : Nat × Nat :=
        match fuel with
        | 0 => (m, e)
        | k + 1 =>
          if (m &&& 0x80_0000) != 0 then (m &&& 0x7F_FFFF, e)
          else normSub (m <<< 1) (e - 1) k
      let (normFrac, exp64) := normSub frac32 (1023 - 126) 24
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

private def bvToF16 (v : BitVec 64) : Float32 :=
  Float32.ofBits ⟨f16BitsToF32Bits (v.truncate 16)⟩

private def f16ToBv (x : Float32) : BitVec 64 :=
  BitVec.ofNat 64 (f32BitsToF16BitsRn x.toBits.toBitVec).toNat

private def bvToF32 (v : BitVec 64) : Float32 :=
  Float32.ofBits (UInt32.ofNat (v &&& 0xFFFF_FFFF#64).toNat)

private def f32ToBv (x : Float32) : BitVec 64 :=
  BitVec.ofNat 64 x.toBits.toNat

private def bvToF64 (v : BitVec 64) : Float :=
  Float.ofBits (UInt64.ofNat v.toNat)

private def f64ToBv (x : Float) : BitVec 64 :=
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

private def setIndexedMem : List (Nat × ByteMemory) → Nat → ByteMemory → List (Nat × ByteMemory)
  | [], idx, mem => [(idx, mem)]
  | (idx', mem') :: rest, idx, mem =>
    if idx' == idx then (idx, mem) :: rest else (idx', mem') :: setIndexedMem rest idx mem

private def setNamedMem : List (String × ByteMemory) → String → ByteMemory → List (String × ByteMemory)
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
  | .logNot _ => .bool
  | .cast ty _ => ty
  | .add a _ | .sub a _ | .mul a _ | .div a _ | .rem a _
  | .bitAnd a _ | .bitOr a _ | .bitXor a _ | .shl a _ | .shr a _ => inferExprType g ls a
  | .eq _ _ | .ne _ _ | .lt _ _ | .le _ _ | .gt _ _ | .ge _ _ => .bool
  | .select _ t _ => inferExprType g ls t
  | .builtinSelect f _ _ => inferExprType g ls f
  | .fma a _ _ => inferExprType g ls a
  | .index target _ =>
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

private inductive MSLBin where
  | add | sub | mul | div | rem

private inductive MSLCmp where
  | eq | ne | lt | le | gt | ge

private def evalTypedBin (ty : MSLType) (op : MSLBin) (va vb : BitVec 64) : MSLOutcome (BitVec 64) :=
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

private def evalTypedCmp (ty : MSLType) (op : MSLCmp) (va vb : BitVec 64) : MSLOutcome (BitVec 64) :=
  let bit (b : Bool) : BitVec 64 := if b then 1#64 else 0#64
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

/-- Load an element (including 4-limb `ln_u256`) from `ByteMemory` at `byteAddr`. -/
private def loadTypedElem (mem : ByteMemory) (elemTy : MSLType) (byteAddr : Nat) :
    Option (BitVec 64 × List (String × BitVec 64)) :=
  match elemTy with
  | .u256 =>
    match mem.loadBits byteAddr 8, mem.loadBits (byteAddr + 8) 8,
          mem.loadBits (byteAddr + 16) 8, mem.loadBits (byteAddr + 24) 8 with
    | some w0, some w1, some w2, some w3 =>
      some (w0, [("l0", w0), ("l1", w1), ("l2", w2), ("l3", w3)])
    | _, _, _, _ => none
  | _ =>
    match mem.loadBits byteAddr elemTy.byteWidth with
    | some raw => some (maskForType elemTy raw, [])
    | none => none

/-- Store an element (including 4-limb `ln_u256`) into `ByteMemory` at `byteAddr`. -/
def storeTypedElem (mem : ByteMemory) (elemTy : MSLType) (byteAddr : Nat)
    (val : BitVec 64) (fields : List (String × BitVec 64) := []) : Option ByteMemory :=
  match elemTy with
  | .u256 =>
    let w0 := (fields.lookup "l0").getD val
    let w1 := (fields.lookup "l1").getD 0#64
    let w2 := (fields.lookup "l2").getD 0#64
    let w3 := (fields.lookup "l3").getD 0#64
    match mem.storeBits byteAddr 8 w0 with
    | none => none
    | some m1 =>
      match m1.storeBits (byteAddr + 8) 8 w1 with
      | none => none
      | some m2 =>
        match m2.storeBits (byteAddr + 16) 8 w2 with
        | none => none
        | some m3 => m3.storeBits (byteAddr + 24) 8 w3
  | _ =>
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
      match loadTypedElem mem elemTy 0 with
      | some (v, flds) => .ok { value := v, fields := flds, locals := ls, log }
      | none => .outOfBoundsLoad .constant bufIdx 0
  | some (.constantBuf bufIdx elemTy) =>
    match g.constantBuffers.lookup bufIdx with
    | none => .outOfBoundsLoad .constant bufIdx elemIdx
    | some mem =>
      match loadTypedElem mem elemTy (elemIdx * elemTy.byteWidth) with
      | some (v, flds) => .ok { value := v, fields := flds, locals := ls, log }
      | none => .outOfBoundsLoad .constant bufIdx elemIdx
  | some (.deviceBuf bufIdx _ elemTy) =>
    match g.deviceBuffers.lookup bufIdx with
    | none => .outOfBoundsLoad .device bufIdx elemIdx
    | some mem =>
      let byteAddr := elemIdx * elemTy.byteWidth
      match recordEpochAccess log tid (.deviceBuf bufIdx) .device byteAddr elemTy.byteWidth false with
      | .ok log' =>
        match loadTypedElem mem elemTy byteAddr with
        | some (v, flds) => .ok { value := v, fields := flds, locals := ls, log := log' }
        | none => .outOfBoundsLoad .device bufIdx elemIdx
      | err => propagateErr err
  | some (.threadgroupArr arrName elemTy) =>
    match g.threadgroupArrays.lookup arrName with
    | none => .outOfBoundsLoad .threadgroup 0 elemIdx
    | some mem =>
      let byteAddr := elemIdx * elemTy.byteWidth
      match recordEpochAccess log tid (.threadgroupArr arrName) .threadgroup byteAddr elemTy.byteWidth false with
      | .ok log' =>
        match loadTypedElem mem elemTy byteAddr with
        | some (v, flds) => .ok { value := v, fields := flds, locals := ls, log := log' }
        | none => .outOfBoundsLoad .threadgroup 0 elemIdx
      | err => propagateErr err

private def bindEval (mx : MSLOutcome MSLEval) (k : MSLEval → MSLOutcome MSLEval) :
    MSLOutcome MSLEval :=
  match mx with
  | .ok ev => k ev
  | err => err

private def finishBin (g : MSLGroupState) (a : MSLExpr) (op : MSLBin)
    (ea eb : MSLEval) : MSLOutcome MSLEval :=
  match evalTypedBin (inferExprType g eb.locals a) op ea.value eb.value with
  | .ok v => .ok { value := v, locals := eb.locals, log := eb.log }
  | err => propagateErr err

private def finishBitwise (g : MSLGroupState) (a : MSLExpr)
    (op : BitVec 64 → BitVec 64 → BitVec 64) (ea eb : MSLEval) : MSLOutcome MSLEval :=
  let ty := inferExprType g eb.locals a
  if ty.isFloat then .unsupportedFloatOp "float bitwise op"
  else .ok { value := maskForType ty (op ea.value eb.value), locals := eb.locals, log := eb.log }

private def finishShift (g : MSLGroupState) (a : MSLExpr) (right : Bool)
    (ea eb : MSLEval) : MSLOutcome MSLEval :=
  let ty := inferExprType g eb.locals a
  if ty.isFloat then .unsupportedFloatOp "float shift"
  else
    let w := ty.bitWidth
    if w == 0 || eb.value.toNat >= w then
      .shiftOutOfRange
    else if right && ty.isSigned then
      .ok { value := maskForType ty ((signExtendTo64 w ea.value).sshiftRight eb.value.toNat)
            locals := eb.locals
            log := eb.log }
    else if right then
      .ok { value := maskForType ty (ea.value >>> eb.value.toNat)
            locals := eb.locals
            log := eb.log }
    else
      .ok { value := maskForType ty (ea.value <<< eb.value.toNat)
            locals := eb.locals
            log := eb.log }

private def finishCmp (g : MSLGroupState) (a : MSLExpr) (op : MSLCmp)
    (ea eb : MSLEval) : MSLOutcome MSLEval :=
  match evalTypedCmp (inferExprType g eb.locals a) op ea.value eb.value with
  | .ok v => .ok { value := v, locals := eb.locals, log := eb.log }
  | err => propagateErr err

/- Evaluate an expression. `callEval` interprets helper calls so recursion stays structural
   on `MSLExpr` / `MSLExprList` (reduces by `rfl` in the Lean kernel).
   C++ `?:` (`.select`) short-circuits; Metal builtin `select` (`.builtinSelect`) is eager. -/
mutual
def evalExprWithCall
    (callEval : MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList →
      MSLOutcome MSLEval)
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
          match loadTypedElem mem elemTy 0 with
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
    match evalExprWithCall callEval g tid ls log base with
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
    match evalExprList callEval g tid ls log args with
    | .ok (vals, ls', log') =>
      let names := structFieldNames g.structs ty
      let flds := names.zip vals
      .ok { value := vals.head?.getD 0#64, fields := flds, locals := ls', log := log' }
    | err => propagateErr err
  | .bitNot a =>
    bindEval (evalExprWithCall callEval g tid ls log a) fun ev =>
      let ty := inferExprType g ev.locals a
      if ty.isFloat then .unsupportedFloatOp "float bitNot"
      else .ok { value := maskForType ty (~~~ev.value), locals := ev.locals, log := ev.log }
  | .logNot a =>
    bindEval (evalExprWithCall callEval g tid ls log a) fun ev =>
      .ok { value := if ev.value == 0#64 then 1#64 else 0#64, locals := ev.locals, log := ev.log }
  | .neg a =>
    bindEval (evalExprWithCall callEval g tid ls log a) fun ev =>
      let ty := inferExprType g ev.locals a
      let v :=
        match ty with
        | .half => f16ToBv (-bvToF16 ev.value)
        | .float => f32ToBv (-bvToF32 ev.value)
        | .double => f64ToBv (-bvToF64 ev.value)
        | _ => maskForType ty (0#64 - ev.value)
      .ok { value := v, locals := ev.locals, log := ev.log }
  | .clz a =>
    bindEval (evalExprWithCall callEval g tid ls log a) fun ev =>
      let ty := inferExprType g ev.locals a
      if ty.isFloat then .unsupportedFloatOp "float clz"
      else
        let bits := ty.bitWidth
        let masked := maskForType ty ev.value
        let z := if bits == 0 then 0 else (masked.truncate bits).clz.toNat
        .ok { value := maskForType ty (BitVec.ofNat 64 z), locals := ev.locals, log := ev.log }
  | .cast ty a =>
    bindEval (evalExprWithCall callEval g tid ls log a) fun ev =>
      match evalMSLCast ty (inferExprType g ev.locals a) ev.value with
      | .ok v => .ok { value := v, locals := ev.locals, log := ev.log }
      | err => propagateErr err
  | .add a b =>
    bindEval (evalExprWithCall callEval g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval g tid ea.locals ea.log b) fun eb =>
      finishBin g a .add ea eb
  | .sub a b =>
    bindEval (evalExprWithCall callEval g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval g tid ea.locals ea.log b) fun eb =>
      finishBin g a .sub ea eb
  | .mul a b =>
    bindEval (evalExprWithCall callEval g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval g tid ea.locals ea.log b) fun eb =>
      finishBin g a .mul ea eb
  | .div a b =>
    bindEval (evalExprWithCall callEval g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval g tid ea.locals ea.log b) fun eb =>
      finishBin g a .div ea eb
  | .rem a b =>
    bindEval (evalExprWithCall callEval g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval g tid ea.locals ea.log b) fun eb =>
      finishBin g a .rem ea eb
  | .bitAnd a b =>
    bindEval (evalExprWithCall callEval g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval g tid ea.locals ea.log b) fun eb =>
      finishBitwise g a (· &&& ·) ea eb
  | .bitOr a b =>
    bindEval (evalExprWithCall callEval g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval g tid ea.locals ea.log b) fun eb =>
      finishBitwise g a (· ||| ·) ea eb
  | .bitXor a b =>
    bindEval (evalExprWithCall callEval g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval g tid ea.locals ea.log b) fun eb =>
      finishBitwise g a (· ^^^ ·) ea eb
  | .shl a b =>
    bindEval (evalExprWithCall callEval g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval g tid ea.locals ea.log b) fun eb =>
      finishShift g a false ea eb
  | .shr a b =>
    bindEval (evalExprWithCall callEval g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval g tid ea.locals ea.log b) fun eb =>
      finishShift g a true ea eb
  | .eq a b =>
    bindEval (evalExprWithCall callEval g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval g tid ea.locals ea.log b) fun eb =>
      finishCmp g a .eq ea eb
  | .ne a b =>
    bindEval (evalExprWithCall callEval g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval g tid ea.locals ea.log b) fun eb =>
      finishCmp g a .ne ea eb
  | .lt a b =>
    bindEval (evalExprWithCall callEval g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval g tid ea.locals ea.log b) fun eb =>
      finishCmp g a .lt ea eb
  | .le a b =>
    bindEval (evalExprWithCall callEval g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval g tid ea.locals ea.log b) fun eb =>
      finishCmp g a .le ea eb
  | .gt a b =>
    bindEval (evalExprWithCall callEval g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval g tid ea.locals ea.log b) fun eb =>
      finishCmp g a .gt ea eb
  | .ge a b =>
    bindEval (evalExprWithCall callEval g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval g tid ea.locals ea.log b) fun eb =>
      finishCmp g a .ge ea eb
  | .select c t f =>
    bindEval (evalExprWithCall callEval g tid ls log c) fun ev =>
      if ev.value != 0#64 then evalExprWithCall callEval g tid ev.locals ev.log t
      else evalExprWithCall callEval g tid ev.locals ev.log f
  | .builtinSelect falseVal trueVal cond =>
    bindEval (evalExprWithCall callEval g tid ls log falseVal) fun ef =>
    bindEval (evalExprWithCall callEval g tid ef.locals ef.log trueVal) fun et =>
    bindEval (evalExprWithCall callEval g tid et.locals et.log cond) fun ec =>
      .ok { value := if ec.value != 0#64 then et.value else ef.value
            fields := if ec.value != 0#64 then et.fields else ef.fields
            locals := ec.locals
            log := ec.log }
  | .fma a b c =>
    bindEval (evalExprWithCall callEval g tid ls log a) fun ea =>
    bindEval (evalExprWithCall callEval g tid ea.locals ea.log b) fun eb =>
    bindEval (evalExprWithCall callEval g tid eb.locals eb.log c) fun ec =>
      let ty := inferExprType g ec.locals a
      let v :=
        match ty with
        | .half => f16ToBv (Float32.fma (bvToF16 ea.value) (bvToF16 eb.value) (bvToF16 ec.value))
        | .float => f32ToBv (Float32.fma (bvToF32 ea.value) (bvToF32 eb.value) (bvToF32 ec.value))
        | .double => f64ToBv (Float.fma (bvToF64 ea.value) (bvToF64 eb.value) (bvToF64 ec.value))
        | _ => maskForType ty (ea.value * eb.value + ec.value)
      .ok { value := v, locals := ec.locals, log := ec.log }
  | .index target idxExpr =>
    bindEval (evalExprWithCall callEval g tid ls log idxExpr) fun ev =>
      readBoundElement g tid ev.locals ev.log target ev.value.toNat
  | .call name args =>
    callEval g tid ls log name args

def evalExprList
    (callEval : MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList →
      MSLOutcome MSLEval)
    (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess) :
    MSLExprList → MSLOutcome (List (BitVec 64) × MSLLocals × List MSLAccess)
  | .nil => .ok ([], ls, log)
  | .cons e rest =>
    match evalExprWithCall callEval g tid ls log e with
    | .ok ev =>
      match evalExprList callEval g tid ev.locals ev.log rest with
      | .ok (vs, ls', log') => .ok (ev.value :: vs, ls', log')
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
    match storeTypedElem mem elemTy (elemIdx * elemTy.byteWidth) val fields with
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
    match storeTypedElem mem elemTy (elemIdx * elemTy.byteWidth) val fields with
    | some mem' =>
      .ok { g with threadgroupArrays := setNamedMem g.threadgroupArrays arrName mem' }
    | none => .outOfBoundsWrite .threadgroup 0 elemIdx

/-- Write one indexed element, trapping on read-only targets, out-of-bounds, and data races.
    `atomic = true` skips recording in `epochLog` (atomics do not race with other atomics). -/
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
    let byteAddr := elemIdx * elemTy.byteWidth
    if atomic then
      writeDeviceBuffer g bufIdx elemTy elemIdx val fields
    else
      match recordEpochAccess g.epochLog tid (.deviceBuf bufIdx) .device byteAddr elemTy.byteWidth true with
      | .ok log' => writeDeviceBuffer { g with epochLog := log' } bufIdx elemTy elemIdx val fields
      | err => propagateErr err
  | some (.threadgroupArr arrName elemTy) =>
    let byteAddr := elemIdx * elemTy.byteWidth
    if atomic then
      writeThreadgroupArray g arrName elemTy elemIdx val fields
    else
      match recordEpochAccess g.epochLog tid (.threadgroupArr arrName) .threadgroup byteAddr elemTy.byteWidth true with
      | .ok log' => writeThreadgroupArray { g with epochLog := log' } arrName elemTy elemIdx val fields
      | err => propagateErr err

/-- Execute one statement that is not a barrier or simdgroup collective. -/
def execStmtWithCall
    (callEval : MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList →
      MSLOutcome MSLEval)
    (g : MSLGroupState) (th : MSLThreadState) (stmt : MSLStmt) (rest : List MSLStmt) :
    MSLOutcome (MSLThreadState × MSLGroupState) :=
  match stmt with
  | .varDecl ty name rhs =>
    match evalExprWithCall callEval g th.tid th.locals g.epochLog rhs with
    | .ok ev =>
      let ls := bindValue g.structs ev.locals name ty ev.value ev.fields
      .ok ({ th with locals := ls, stmts := rest }, { g with epochLog := ev.log })
    | err => propagateErr err
  | .assign name rhs =>
    match g.bindings.lookup name with
    | some (.constantBuf _ _) | some (.constantScalar _ _) => .readOnlyViolation name 0
    | some (.deviceBuf _ true _) => .readOnlyViolation name 0
    | _ =>
      match evalExprWithCall callEval g th.tid th.locals g.epochLog rhs with
      | .ok ev =>
        let ty := (ev.locals.lookupType? name).getD (inferExprType g ev.locals rhs)
        let ls := bindValue g.structs ev.locals name ty ev.value ev.fields
        .ok ({ th with locals := ls, stmts := rest }, { g with epochLog := ev.log })
      | err => propagateErr err
  | .fieldAssign varName field rhs =>
    match evalExprWithCall callEval g th.tid th.locals g.epochLog rhs with
    | .ok ev =>
      let fty :=
        match ev.locals.lookupType? varName with
        | some ty => structFieldType g.structs ty field
        | none => .ulong
      let ls := ev.locals.setField varName field (maskForType fty ev.value)
      .ok ({ th with locals := ls, stmts := rest }, { g with epochLog := ev.log })
    | err => propagateErr err
  | .indexAssign target idxExpr rhs =>
    match evalExprWithCall callEval g th.tid th.locals g.epochLog idxExpr with
    | .ok ei =>
      match evalExprWithCall callEval g th.tid ei.locals ei.log rhs with
      | .ok er =>
        match execIndexWrite { g with epochLog := er.log } th.tid target
            ei.value.toNat er.value er.fields false with
        | .ok g' => .ok ({ th with locals := er.locals, stmts := rest }, g')
        | err => propagateErr err
      | err => propagateErr err
    | err => propagateErr err
  | .callAssign declTy dst fnName args =>
    match callEval g th.tid th.locals g.epochLog fnName args with
    | .ok ev =>
      let ty := declTy.getD ((ev.locals.lookupType? dst).getD
        (inferExprType g ev.locals (.call fnName args)))
      let ls := bindValue g.structs ev.locals dst ty ev.value ev.fields
      .ok ({ th with locals := ls, stmts := rest }, { g with epochLog := ev.log })
    | err => propagateErr err
  | .exprStmt e =>
    match evalExprWithCall callEval g th.tid th.locals g.epochLog e with
    | .ok ev => .ok ({ th with locals := ev.locals, stmts := rest }, { g with epochLog := ev.log })
    | err => propagateErr err
  | .atomicFetchAdd declTy dst target idxExpr valExpr =>
    match evalExprWithCall callEval g th.tid th.locals g.epochLog idxExpr with
    | .ok ei =>
      match evalExprWithCall callEval g th.tid ei.locals ei.log valExpr with
      | .ok ev =>
        let elemIdx := ei.value.toNat
        match g.bindings.lookup target with
        | none => .unboundIdentifier target
        | some (.constantBuf _ _) | some (.constantScalar _ _) => .readOnlyViolation target elemIdx
        | some (.deviceBuf _ true _) => .readOnlyViolation target elemIdx
        | some (.deviceBuf bufIdx false elemTy) =>
          match g.deviceBuffers.lookup bufIdx with
          | none => .outOfBoundsWrite .device bufIdx elemIdx
          | some mem =>
            match mem.loadBits (elemIdx * elemTy.byteWidth) elemTy.byteWidth with
            | none => .outOfBoundsWrite .device bufIdx elemIdx
            | some old =>
              let maskedOld := maskForType elemTy old
              let newVal := maskForType elemTy (maskedOld + ev.value)
              match execIndexWrite { g with epochLog := ev.log } th.tid target
                  elemIdx newVal [] true with
              | .ok g' =>
                let ls :=
                  match dst with
                  | none => ev.locals
                  | some name =>
                    let ty := declTy.getD ((ev.locals.lookupType? name).getD elemTy)
                    ev.locals.setTyped name ty (maskForType ty maskedOld)
                .ok ({ th with locals := ls, stmts := rest }, g')
              | err => propagateErr err
        | some (.threadgroupArr arrName elemTy) =>
          match g.threadgroupArrays.lookup arrName with
          | none => .outOfBoundsWrite .threadgroup 0 elemIdx
          | some mem =>
            match mem.loadBits (elemIdx * elemTy.byteWidth) elemTy.byteWidth with
            | none => .outOfBoundsWrite .threadgroup 0 elemIdx
            | some old =>
              let maskedOld := maskForType elemTy old
              let newVal := maskForType elemTy (maskedOld + ev.value)
              match execIndexWrite { g with epochLog := ev.log } th.tid target
                  elemIdx newVal [] true with
              | .ok g' =>
                let ls :=
                  match dst with
                  | none => ev.locals
                  | some name =>
                    let ty := declTy.getD ((ev.locals.lookupType? name).getD elemTy)
                    ev.locals.setTyped name ty (maskForType ty maskedOld)
                .ok ({ th with locals := ls, stmts := rest }, g')
              | err => propagateErr err
      | err => propagateErr err
    | err => propagateErr err
  | .simdShuffleXor _ _ _ _ | .simdSum _ _ _ | .threadgroupBarrier =>
    .barrierDivergence
  | .ifElse cond thenBr elseBr =>
    match evalExprWithCall callEval g th.tid th.locals g.epochLog cond with
    | .ok ev =>
      let branch := if ev.value != 0#64 then thenBr.toList else elseBr.toList
      .ok ({ th with locals := ev.locals, stmts := branch ++ rest }, { g with epochLog := ev.log })
    | err => propagateErr err
  | .forLoop loopVar ty initExpr condExpr stepExpr body =>
    match evalExprWithCall callEval g th.tid th.locals g.epochLog initExpr with
    | .ok ev =>
      let ls := ev.locals.setTyped loopVar ty (maskForType ty ev.value)
      let cont := .whileLoop condExpr (body.append (.cons (.assign loopVar stepExpr) .nil))
      .ok ({ th with locals := ls, stmts := cont :: rest }, { g with epochLog := ev.log })
    | err => propagateErr err
  | .whileLoop condExpr body =>
    match evalExprWithCall callEval g th.tid th.locals g.epochLog condExpr with
    | .ok ev =>
      if ev.value != 0#64 then
        .ok ({ th with locals := ev.locals, stmts := body.toList ++ (stmt :: rest) },
             { g with epochLog := ev.log })
      else
        .ok ({ th with locals := ev.locals, stmts := rest }, { g with epochLog := ev.log })
    | err => propagateErr err
  | .returnVal e =>
    match evalExprWithCall callEval g th.tid th.locals g.epochLog e with
    | .ok ev =>
      let ls := ev.fields.foldl (fun acc (n, v) => acc.setField "$ret" n v) ev.locals
      .ok ({ th with retVal := some ev.value, locals := ls, stmts := [], halted := true },
           { g with epochLog := ev.log })
    | err => propagateErr err
  | .returnStmt =>
    .ok ({ th with stmts := [], halted := true }, g)

/-- Run a helper body for at most `fuel` statements. Structural on `fuel`. -/
def runCalleeWithCall
    (callEval : MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList →
      MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (th : MSLThreadState) :
    MSLOutcome (MSLThreadState × List MSLAccess) :=
  match fuel with
  | 0 => if th.halted then .ok (th, g.epochLog) else .fuelExhausted
  | f + 1 =>
    if th.halted then .ok (th, g.epochLog)
    else
      match th.stmts with
      | [] => .ok ({ th with halted := true }, g.epochLog)
      | stmt :: rest =>
        match execStmtWithCall callEval g th stmt rest with
        | .ok (th', g') => runCalleeWithCall callEval f g' th'
        | err => propagateErr err

/-- Copy `thread T&` reference parameters back into the caller after a helper returns. -/
def writeBackRefs (structs : List MSLStructDecl) (caller callee : MSLLocals)
    (params : List MSLParamDecl) (args : List MSLExpr) : MSLLocals :=
  (params.zip args).foldl (fun acc (p, e) =>
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
    | _, _ => acc) caller

/-- Bind helper parameters. Structural on `MSLExprList`; `callEval` evaluates each argument. -/
def bindParams
    (callEval : MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList →
      MSLOutcome MSLEval)
    (structs : List MSLStructDecl) (fnName : String)
    (g : MSLGroupState) (tid : Dim3) :
    List MSLParamDecl → MSLExprList → MSLLocals → MSLLocals → List MSLAccess →
      MSLOutcome (MSLLocals × MSLLocals × List MSLAccess)
  | [], .nil, callerLs, calleeAcc, curLog => .ok (callerLs, calleeAcc, curLog)
  | p :: prest, .cons e erest, callerLs, calleeAcc, curLog =>
    match evalExprWithCall callEval g tid callerLs curLog e with
    | .ok ev =>
      let paramTy := match p.ty with | .ref .thread inner => inner | other => other
      let calleeAcc' := bindValue structs calleeAcc p.name paramTy ev.value ev.fields
      bindParams callEval structs fnName g tid prest erest ev.locals calleeAcc' ev.log
    | err => propagateErr err
  | _, _, _, _, _ => .unboundIdentifier fnName

/-- Interpret a function call at bounded nesting depth `depth`. Structural on `depth`. -/
def makeCallEval (depth : Nat) :
    MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList →
      MSLOutcome MSLEval :=
  match depth with
  | 0 => fun _ _ _ _ name _ => .unboundIdentifier name
  | d + 1 => fun g tid ls log name args =>
    match g.funcs.find? (fun f => f.name == name) with
    | none => .unboundIdentifier name
    | some fn =>
      match bindParams (makeCallEval d) g.structs name g tid fn.params args ls MSLLocals.empty log with
      | .ok (callerLs', calleeLocals, logAfterArgs) =>
        let callee : MSLThreadState :=
          { tid, locals := calleeLocals, stmts := fn.body.toList, halted := false }
        match runCalleeWithCall (makeCallEval d) 64 { g with epochLog := logAfterArgs } callee with
        | .ok (th', logFinal) =>
          let retFields :=
            (structFieldNames g.structs fn.retTy).filterMap fun n =>
              match th'.locals.lookupField? "$ret" n with
              | some v => some (n, v)
              | none => none
          let callerOut := writeBackRefs g.structs callerLs' th'.locals fn.params args.toList
          .ok { value := maskForType fn.retTy (th'.retVal.getD 0#64)
                fields := retFields
                locals := callerOut
                log := logFinal }
        | err => propagateErr err
      | err => propagateErr err

/-- Default helper-call evaluator (supports kernel -> composite helper -> leaf helper). -/
def kernelCallEval :
    MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList →
      MSLOutcome MSLEval :=
  makeCallEval 2

/-- Evaluate an `MSLExpr` over `BitVec 64` (independent of `LeanNative.Semantics`). -/
def evalMSLExpr (g : MSLGroupState) (th : MSLThreadState) (e : MSLExpr) : MSLOutcome (BitVec 64) :=
  match evalExprWithCall kernelCallEval g th.tid th.locals g.epochLog e with
  | .ok ev => .ok ev.value
  | err => propagateErr err

/-- Execute one non-barrier, non-collective `MSLStmt`. -/
def execNonBarrierStmt (g : MSLGroupState) (th : MSLThreadState) (stmt : MSLStmt)
    (rest : List MSLStmt) : MSLOutcome (MSLThreadState × MSLGroupState) :=
  execStmtWithCall kernelCallEval g th stmt rest

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

private def addSimdValues (ty : MSLType) (a b : BitVec 64) : BitVec 64 :=
  match ty with
  | .half => f16ToBv (bvToF16 a + bvToF16 b)
  | .float => f32ToBv (bvToF32 a + bvToF32 b)
  | .double => f64ToBv (bvToF64 a + bvToF64 b)
  | _ => maskForType ty (a + b)

/-- Resolve one simdgroup collective across all live lanes in simdgroup `sgId`.
    Traps with `.barrierDivergence` if any live lane in `sgId` is at a different statement. -/
def stepSimdgroup (g : MSLGroupState) (sgId : Nat) : MSLOutcome MSLGroupState :=
  let liveInSg := g.threads.filter (fun th => !th.halted && simdgroupOf g.groupDim th.tid == sgId)
  match liveInSg with
  | [] => .barrierDivergence
  | leader :: _ =>
    match leader.stmts with
    | .simdShuffleXor _ _ _ _ :: _ =>
      let rec collectSrc (curLog : List MSLAccess) :
          List MSLThreadState → MSLOutcome (List (Nat × BitVec 64) × List MSLAccess)
        | [] => .ok ([], curLog)
        | th :: rest =>
          if !th.halted && simdgroupOf g.groupDim th.tid == sgId then
            match th.stmts with
            | .simdShuffleXor _ _ srcExpr _ :: _ =>
              match evalExprWithCall kernelCallEval g th.tid th.locals curLog srcExpr with
              | .ok es =>
                match collectSrc es.log rest with
                | .ok (ps, log') =>
                  .ok ((simdLaneOf g.groupDim th.tid, es.value) :: ps, log')
                | err => err
              | err => propagateErr err
            | _ => .barrierDivergence
          else
            collectSrc curLog rest
      let rec applyShuffle (laneVals : List (Nat × BitVec 64)) (curLog : List MSLAccess) :
          List MSLThreadState → MSLOutcome (List MSLThreadState × List MSLAccess)
        | [] => .ok ([], curLog)
        | th :: rest =>
          if !th.halted && simdgroupOf g.groupDim th.tid == sgId then
            match th.stmts with
            | .simdShuffleXor declTy dst srcExpr maskExpr :: tail =>
              match evalExprWithCall kernelCallEval g th.tid th.locals curLog srcExpr with
              | .ok es =>
                match evalExprWithCall kernelCallEval g th.tid es.locals es.log maskExpr with
                | .ok em =>
                  let partner := (simdLaneOf g.groupDim th.tid) ^^^ (em.value.toNat % 32)
                  let v := (laneVals.lookup partner).getD es.value
                  let ty := declTy.getD ((em.locals.lookupType? dst).getD
                    (inferExprType g em.locals srcExpr))
                  let ls := em.locals.setTyped dst ty (maskForType ty v)
                  match applyShuffle laneVals em.log rest with
                  | .ok (ths, log') => .ok ({ th with locals := ls, stmts := tail } :: ths, log')
                  | err => err
                | err => propagateErr err
              | err => propagateErr err
            | _ => .barrierDivergence
          else
            match applyShuffle laneVals curLog rest with
            | .ok (ths, log') => .ok (th :: ths, log')
            | err => err
      match collectSrc g.epochLog g.threads with
      | .ok (laneVals, _) =>
        match applyShuffle laneVals g.epochLog g.threads with
        | .ok (threads', log') => .ok { g with threads := threads', epochLog := log' }
        | err => propagateErr err
      | err => propagateErr err
    | .simdSum _ _ leaderSrc :: _ =>
      let sumTy := inferExprType g leader.locals leaderSrc
      let rec collectSum (curLog : List MSLAccess) :
          List MSLThreadState → MSLOutcome (BitVec 64 × List MSLAccess)
        | [] => .ok (0#64, curLog)
        | th :: rest =>
          if !th.halted && simdgroupOf g.groupDim th.tid == sgId then
            match th.stmts with
            | .simdSum _ _ srcExpr :: _ =>
              match evalExprWithCall kernelCallEval g th.tid th.locals curLog srcExpr with
              | .ok es =>
                match collectSum es.log rest with
                | .ok (acc, log') => .ok (addSimdValues sumTy es.value acc, log')
                | err => err
              | err => propagateErr err
            | _ => .barrierDivergence
          else
            collectSum curLog rest
      let rec applySum (total : BitVec 64) (curLog : List MSLAccess) :
          List MSLThreadState → MSLOutcome (List MSLThreadState × List MSLAccess)
        | [] => .ok ([], curLog)
        | th :: rest =>
          if !th.halted && simdgroupOf g.groupDim th.tid == sgId then
            match th.stmts with
            | .simdSum declTy dst srcExpr :: tail =>
              match evalExprWithCall kernelCallEval g th.tid th.locals curLog srcExpr with
              | .ok es =>
                let ty := declTy.getD ((es.locals.lookupType? dst).getD
                  (inferExprType g es.locals srcExpr))
                let ls := es.locals.setTyped dst ty (maskForType ty total)
                match applySum total es.log rest with
                | .ok (ths, log') => .ok ({ th with locals := ls, stmts := tail } :: ths, log')
                | err => err
              | err => propagateErr err
            | _ => .barrierDivergence
          else
            match applySum total curLog rest with
            | .ok (ths, log') => .ok (th :: ths, log')
            | err => err
      match collectSum g.epochLog g.threads with
      | .ok (total, _) =>
        match applySum total g.epochLog g.threads with
        | .ok (threads', log') => .ok { g with threads := threads', epochLog := log' }
        | err => propagateErr err
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
    (funcs : List MSLFuncDecl := []) (structs : List MSLStructDecl := []) : MSLGroupState :=
  let bindings := buildKernelBindings k
  let tgArrays := k.sharedDecls.map fun s =>
    (s.name, ByteMemory.zeros (s.count * s.elemTy.byteWidth))
  let g0 : MSLGroupState :=
    { gridDim, groupDim, groupId, structs, funcs, bindings
      deviceBuffers, constantBuffers
      threadgroupArrays := tgArrays
      epochLog := []
      threads := [] }
  let threads := groupDim.coords.map fun tid =>
    { tid := tid
      locals := initThreadLocals k g0 tid
      stmts := k.body
      halted := false }
  { g0 with threads }

/-- Launch an `MSLKernelDecl` across every threadgroup in `gridDim` (each with fresh zeroed
    `threadgroup` shared arrays and immutable `constantBuffers`), threading `deviceBuffers`
    across threadgroups and returning the final `device` buffer table. -/
def evalMSLKernel (fuelPerGroup : Nat) (k : MSLKernelDecl) (gridDim groupDim : Dim3)
    (deviceBuffers constantBuffers : List (Nat × ByteMemory))
    (funcs : List MSLFuncDecl := []) (structs : List MSLStructDecl := []) :
    MSLOutcome (List (Nat × ByteMemory)) :=
  let rec loopGroups (devBufs : List (Nat × ByteMemory)) :
      List Dim3 → MSLOutcome (List (Nat × ByteMemory))
    | [] => .ok devBufs
    | gid :: rest =>
      let g0 := initGroupState k gridDim groupDim gid devBufs constantBuffers funcs structs
      match runGroup fuelPerGroup g0 with
      | .ok gFinal => loopGroups gFinal.deviceBuffers rest
      | err => propagateErr err
  loopGroups deviceBuffers gridDim.coords
/-! ## 3. 1:1 Structural Pretty-Printer (`MSLModule -> String`) -/

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

private def hexDigitMSL (n : Nat) : Char :=
  match n % 16 with
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3'
  | 4 => '4' | 5 => '5' | 6 => '6' | 7 => '7'
  | 8 => '8' | 9 => '9' | 10 => 'A' | 11 => 'B'
  | 12 => 'C' | 13 => 'D' | 14 => 'E' | _ => 'F'

private def hexNibblesMSL (v : Nat) : Nat → List Char
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
  | .structLit _ args =>
    let items := String.intercalate ", " (ppMSLExprList args)
    "{ " ++ items ++ " }"
  | .bitNot a         => s!"(~{ppMSLExpr a})"
  | .logNot a         => s!"(!{ppMSLExpr a})"
  | .neg a            => s!"(-{ppMSLExpr a})"
  | .clz a            => s!"clz({ppMSLExpr a})"
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

private def ppOptDeclPrefix (declTy : Option MSLType) (dst : String) : String :=
  match declTy with
  | some ty => ppMSLType ty ++ " " ++ dst ++ " = "
  | none => dst ++ " = "

/- Render an `MSLStmt` (and mutually `MSLBlock`) with indentation `indent`. -/
mutual
def ppMSLStmt (indent : String := "    ") : MSLStmt → String
  | .varDecl ty name rhs =>
    indent ++ ppMSLType ty ++ " " ++ name ++ " = " ++ ppMSLExpr rhs ++ ";"
  | .assign name rhs =>
    indent ++ name ++ " = " ++ ppMSLExpr rhs ++ ";"
  | .fieldAssign varName field rhs =>
    indent ++ varName ++ "." ++ field ++ " = " ++ ppMSLExpr rhs ++ ";"
  | .indexAssign target idx rhs =>
    indent ++ target ++ "[" ++ ppMSLExpr idx ++ "] = " ++ ppMSLExpr rhs ++ ";"
  | .callAssign declTy dst fnName args =>
    let items := String.intercalate ", " (ppMSLExprList args)
    indent ++ ppOptDeclPrefix declTy dst ++ fnName ++ "(" ++ items ++ ");"
  | .exprStmt e =>
    indent ++ ppMSLExpr e ++ ";"
  | .atomicFetchAdd declTy dst target idx val =>
    let callStr :=
      "atomic_fetch_add_explicit(&" ++ target ++ "[" ++ ppMSLExpr idx ++ "], " ++
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
/-! ## 4. Kernel-Checked Theorems (`0 sorryAx`, `strict-proofs` clean) -/

private theorem writeLEAux_size (bs : Array UInt8) (addr : Nat) (val : BitVec 64) :
    ∀ n : Nat, (ByteMemory.writeLEAux bs addr val n).size = bs.size
  | 0 => rfl
  | k + 1 => by
    simp [ByteMemory.writeLEAux, Array.size_setIfInBounds, writeLEAux_size _ addr val k]

private theorem storeBits_size (m m' : ByteMemory) (addr width : Nat) (val : BitVec 64)
    (h : m.storeBits addr width val = some m') :
    m'.bytes.size = m.bytes.size := by
  unfold ByteMemory.storeBits at h
  split at h <;> simp at h
  rw [← h]
  exact writeLEAux_size m.bytes addr val width

/-- `writeDeviceBuffer` never alters `constantBuffers` or `threadgroupArrays`. -/
theorem writeDeviceBuffer_preserves_const_and_tg (g g' : MSLGroupState)
    (bufIdx : Nat) (elemTy : MSLType) (elemIdx : Nat) (val : BitVec 64)
    (fields : List (String × BitVec 64))
    (h : writeDeviceBuffer g bufIdx elemTy elemIdx val fields = .ok g') :
    g'.constantBuffers = g.constantBuffers ∧ g'.threadgroupArrays = g.threadgroupArrays := by
  unfold writeDeviceBuffer at h
  cases hLookup : g.deviceBuffers.lookup bufIdx <;> simp [hLookup] at h
  case some mem =>
    cases hStore : storeTypedElem mem elemTy (elemIdx * elemTy.byteWidth) val fields <;>
      simp [hStore] at h
    subst h
    exact ⟨rfl, rfl⟩

/-- `writeThreadgroupArray` never alters `constantBuffers` or `deviceBuffers`. -/
theorem writeThreadgroupArray_preserves_const_and_dev (g g' : MSLGroupState)
    (arrName : String) (elemTy : MSLType) (elemIdx : Nat) (val : BitVec 64)
    (fields : List (String × BitVec 64))
    (h : writeThreadgroupArray g arrName elemTy elemIdx val fields = .ok g') :
    g'.constantBuffers = g.constantBuffers ∧ g'.deviceBuffers = g.deviceBuffers := by
  unfold writeThreadgroupArray at h
  cases hLookup : g.threadgroupArrays.lookup arrName <;> simp [hLookup] at h
  case some mem =>
    cases hStore : storeTypedElem mem elemTy (elemIdx * elemTy.byteWidth) val fields <;>
      simp [hStore] at h
    subst h
    exact ⟨rfl, rfl⟩

/-- `execIndexWrite` preserves `constantBuffers` across every address space and atomicity mode. -/
theorem execIndexWrite_preserves_constant_buffers (g g' : MSLGroupState)
    (tid : Dim3) (target : String) (elemIdx : Nat) (val : BitVec 64)
    (fields : List (String × BitVec 64)) (atomic : Bool)
    (h : execIndexWrite g tid target elemIdx val fields atomic = .ok g') :
    g'.constantBuffers = g.constantBuffers := by
  unfold execIndexWrite at h
  cases hBind : g.bindings.lookup target <;> simp [hBind] at h
  case some binding =>
    cases binding with
    | constantBuf _ _ => simp at h
    | constantScalar _ _ => simp at h
    | deviceBuf bufIdx isConst elemTy =>
      cases isConst <;> simp at h
      cases atomic <;> simp at h
      · cases hRec : recordEpochAccess g.epochLog tid (.deviceBuf bufIdx) .device
            (elemIdx * elemTy.byteWidth) elemTy.byteWidth true <;>
          simp [hRec, propagateErr] at h
        case ok log' =>
          exact (writeDeviceBuffer_preserves_const_and_tg
            { g with epochLog := log' } g' bufIdx elemTy elemIdx val fields h).1
      · exact (writeDeviceBuffer_preserves_const_and_tg
          g g' bufIdx elemTy elemIdx val fields h).1
    | threadgroupArr arrName elemTy =>
      simp at h
      cases atomic <;> simp at h
      · cases hRec : recordEpochAccess g.epochLog tid (.threadgroupArr arrName) .threadgroup
            (elemIdx * elemTy.byteWidth) elemTy.byteWidth true <;>
          simp [hRec, propagateErr] at h
        case ok log' =>
          exact (writeThreadgroupArray_preserves_const_and_dev
            { g with epochLog := log' } g' arrName elemTy elemIdx val fields h).1
      · exact (writeThreadgroupArray_preserves_const_and_dev
          g g' arrName elemTy elemIdx val fields h).1

/-- `constant` address-space immutability (statement level): executing ANY `MSLStmt` preserves
    `g.constantBuffers` bit-identically whenever it succeeds. -/
theorem exec_preserves_constant_buffers (g : MSLGroupState) (th : MSLThreadState)
    (stmt : MSLStmt) (rest : List MSLStmt) (th' : MSLThreadState) (g' : MSLGroupState)
    (h : execNonBarrierStmt g th stmt rest = .ok (th', g')) :
    g'.constantBuffers = g.constantBuffers := by
  unfold execNonBarrierStmt execStmtWithCall at h
  cases stmt with
  | varDecl ty name rhs =>
    dsimp only at h
    cases hE : evalExprWithCall kernelCallEval g th.tid th.locals g.epochLog rhs <;>
      simp [hE, propagateErr] at h
    rw [← h.2]
  | assign name rhs =>
    dsimp only at h
    cases hB : g.bindings.lookup name with
    | none =>
      simp [hB] at h
      cases hE : evalExprWithCall kernelCallEval g th.tid th.locals g.epochLog rhs <;>
        simp [hE, propagateErr] at h
      rw [← h.2]
    | some b =>
      cases b with
      | constantBuf _ _ => simp [hB] at h
      | constantScalar _ _ => simp [hB] at h
      | deviceBuf _ isConst _ =>
        cases isConst <;> simp [hB] at h
        cases hE : evalExprWithCall kernelCallEval g th.tid th.locals g.epochLog rhs <;>
          simp [hE, propagateErr] at h
        rw [← h.2]
      | threadgroupArr _ _ =>
        simp [hB] at h
        cases hE : evalExprWithCall kernelCallEval g th.tid th.locals g.epochLog rhs <;>
          simp [hE, propagateErr] at h
        rw [← h.2]
  | fieldAssign varName field rhs =>
    dsimp only at h
    cases hE : evalExprWithCall kernelCallEval g th.tid th.locals g.epochLog rhs <;>
      simp [hE, propagateErr] at h
    rw [← h.2]
  | indexAssign target idxExpr rhsExpr =>
    dsimp only at h
    cases hI : evalExprWithCall kernelCallEval g th.tid th.locals g.epochLog idxExpr <;>
      simp [hI, propagateErr] at h
    case ok ei =>
      cases hR : evalExprWithCall kernelCallEval g th.tid ei.locals ei.log rhsExpr <;>
        simp [hR] at h
      case ok er =>
        cases hW : execIndexWrite { g with epochLog := er.log } th.tid target
            ei.value.toNat er.value er.fields false <;>
          simp [hW] at h
        case ok gMid =>
          rw [← h.2]
          exact execIndexWrite_preserves_constant_buffers
            { g with epochLog := er.log } gMid th.tid target ei.value.toNat er.value er.fields false hW
  | callAssign declTy dst fnName args =>
    dsimp only at h
    cases hC : kernelCallEval g th.tid th.locals g.epochLog fnName args <;>
      simp [hC, propagateErr] at h
    rw [← h.2]
  | exprStmt e =>
    dsimp only at h
    cases hE : evalExprWithCall kernelCallEval g th.tid th.locals g.epochLog e <;>
      simp [hE, propagateErr] at h
    rw [← h.2]
  | atomicFetchAdd declTy dst target idxExpr valExpr =>
    dsimp only at h
    cases hI : evalExprWithCall kernelCallEval g th.tid th.locals g.epochLog idxExpr <;>
      simp [hI, propagateErr] at h
    case ok ei =>
      cases hV : evalExprWithCall kernelCallEval g th.tid ei.locals ei.log valExpr <;>
        simp [hV] at h
      case ok ev =>
        cases hB : g.bindings.lookup target <;> simp [hB] at h
        case some b =>
          cases b with
          | constantBuf _ _ => simp at h
          | constantScalar _ _ => simp at h
          | deviceBuf bufIdx isConst elemTy =>
            cases isConst <;> simp at h
            cases hM : g.deviceBuffers.lookup bufIdx <;> simp [hM] at h
            case some mem =>
              cases hL : mem.loadBits (ei.value.toNat * elemTy.byteWidth) elemTy.byteWidth <;>
                simp [hL] at h
              case some old =>
                cases hW : execIndexWrite { g with epochLog := ev.log } th.tid target
                    ei.value.toNat (maskForType elemTy (maskForType elemTy old + ev.value))
                    [] true <;>
                  simp [hW] at h
                case ok gMid =>
                  rw [← h.2]
                  exact execIndexWrite_preserves_constant_buffers
                    { g with epochLog := ev.log } gMid th.tid target ei.value.toNat _ [] true hW
          | threadgroupArr arrName elemTy =>
            simp at h
            cases hM : g.threadgroupArrays.lookup arrName <;> simp [hM] at h
            case some mem =>
              cases hL : mem.loadBits (ei.value.toNat * elemTy.byteWidth) elemTy.byteWidth <;>
                simp [hL] at h
              case some old =>
                cases hW : execIndexWrite { g with epochLog := ev.log } th.tid target
                    ei.value.toNat (maskForType elemTy (maskForType elemTy old + ev.value))
                    [] true <;>
                  simp [hW] at h
                case ok gMid =>
                  rw [← h.2]
                  exact execIndexWrite_preserves_constant_buffers
                    { g with epochLog := ev.log } gMid th.tid target ei.value.toNat _ [] true hW
  | simdShuffleXor _ _ _ _ => simp at h
  | simdSum _ _ _ => simp at h
  | threadgroupBarrier => simp at h
  | ifElse cond thenBr elseBr =>
    dsimp only at h
    cases hC : evalExprWithCall kernelCallEval g th.tid th.locals g.epochLog cond <;>
      simp [hC, propagateErr] at h
    rw [← h.2]
  | forLoop loopVar ty initExpr condExpr stepExpr body =>
    dsimp only at h
    cases hInit : evalExprWithCall kernelCallEval g th.tid th.locals g.epochLog initExpr <;>
      simp [hInit, propagateErr] at h
    rw [← h.2]
  | whileLoop condExpr body =>
    dsimp only at h
    cases hC : evalExprWithCall kernelCallEval g th.tid th.locals g.epochLog condExpr <;>
      simp [hC, propagateErr] at h
    case ok ev =>
      split at h <;> simp at h <;> rw [← h.2]
  | returnVal e =>
    dsimp only at h
    cases hE : evalExprWithCall kernelCallEval g th.tid th.locals g.epochLog e <;>
      simp [hE, propagateErr] at h
    rw [← h.2]
  | returnStmt =>
    dsimp only at h
    simp at h
    rw [← h.2]

/-- Explicit write rejection for `constant` buffers: any indexed write targeting a `constant`
    buffer binding traps with `MSLOutcome.readOnlyViolation`. -/
theorem constant_write_rejected (g : MSLGroupState) (tid : Dim3) (target : String)
    (bufIdx : Nat) (elemTy : MSLType) (elemIdx : Nat) (val : BitVec 64)
    (fields : List (String × BitVec 64)) (atomic : Bool)
    (h_const : g.bindings.lookup target = some (.constantBuf bufIdx elemTy)) :
    execIndexWrite g tid target elemIdx val fields atomic = .readOnlyViolation target elemIdx := by
  unfold execIndexWrite
  rw [h_const]

/-- Explicit write rejection for `device const T*` buffers: any indexed write targeting a
    read-only `device const` pointer traps with `MSLOutcome.readOnlyViolation`. -/
theorem device_const_write_rejected (g : MSLGroupState) (tid : Dim3) (target : String)
    (bufIdx : Nat) (elemTy : MSLType) (elemIdx : Nat) (val : BitVec 64)
    (fields : List (String × BitVec 64)) (atomic : Bool)
    (h_ro : g.bindings.lookup target = some (.deviceBuf bufIdx true elemTy)) :
    execIndexWrite g tid target elemIdx val fields atomic = .readOnlyViolation target elemIdx := by
  unfold execIndexWrite
  rw [h_ro]

/-- Address-space isolation (`device` -> `threadgroup`): writing to a mutable `device` buffer
    never mutates per-threadgroup shared memory `threadgroupArrays`. -/
theorem device_write_preserves_threadgroup (g g' : MSLGroupState) (tid : Dim3) (target : String)
    (bufIdx : Nat) (elemTy : MSLType) (elemIdx : Nat) (val : BitVec 64)
    (fields : List (String × BitVec 64)) (atomic : Bool)
    (h_dev : g.bindings.lookup target = some (.deviceBuf bufIdx false elemTy))
    (h_exec : execIndexWrite g tid target elemIdx val fields atomic = .ok g') :
    g'.threadgroupArrays = g.threadgroupArrays := by
  unfold execIndexWrite at h_exec
  rw [h_dev] at h_exec
  dsimp only at h_exec
  cases atomic <;> simp at h_exec
  · cases hRec : recordEpochAccess g.epochLog tid (.deviceBuf bufIdx) .device
        (elemIdx * elemTy.byteWidth) elemTy.byteWidth true <;>
      simp [hRec, propagateErr] at h_exec
    case ok log' =>
      exact (writeDeviceBuffer_preserves_const_and_tg
        { g with epochLog := log' } g' bufIdx elemTy elemIdx val fields h_exec).2
  · exact (writeDeviceBuffer_preserves_const_and_tg
      g g' bufIdx elemTy elemIdx val fields h_exec).2

/-- Address-space isolation (`threadgroup` -> `device`): writing to a `threadgroup` shared array
    never mutates `deviceBuffers`. -/
theorem threadgroup_write_preserves_device (g g' : MSLGroupState) (tid : Dim3)
    (target arrName : String) (elemTy : MSLType) (elemIdx : Nat) (val : BitVec 64)
    (fields : List (String × BitVec 64)) (atomic : Bool)
    (h_tg : g.bindings.lookup target = some (.threadgroupArr arrName elemTy))
    (h_exec : execIndexWrite g tid target elemIdx val fields atomic = .ok g') :
    g'.deviceBuffers = g.deviceBuffers := by
  unfold execIndexWrite at h_exec
  rw [h_tg] at h_exec
  dsimp only at h_exec
  cases atomic <;> simp at h_exec
  · cases hRec : recordEpochAccess g.epochLog tid (.threadgroupArr arrName) .threadgroup
        (elemIdx * elemTy.byteWidth) elemTy.byteWidth true <;>
      simp [hRec, propagateErr] at h_exec
    case ok log' =>
      exact (writeThreadgroupArray_preserves_const_and_dev
        { g with epochLog := log' } g' arrName elemTy elemIdx val fields h_exec).2
  · exact (writeThreadgroupArray_preserves_const_and_dev
      g g' arrName elemTy elemIdx val fields h_exec).2

private theorem storeTypedElem_oob (mem : ByteMemory) (elemTy : MSLType) (byteAddr : Nat)
    (val : BitVec 64) (fields : List (String × BitVec 64))
    (h_oob : mem.bytes.size < byteAddr + elemTy.byteWidth) :
    storeTypedElem mem elemTy byteAddr val fields = none := by
  cases elemTy with
  | u256 =>
    simp only [storeTypedElem]
    simp [MSLType.byteWidth] at h_oob
    cases h1 : mem.storeBits byteAddr 8 ((fields.lookup "l0").getD val) with
    | none => rfl
    | some m1 =>
      dsimp only
      have hs1 := storeBits_size mem m1 byteAddr 8 _ h1
      cases h2 : m1.storeBits (byteAddr + 8) 8 ((fields.lookup "l1").getD 0#64) with
      | none => rfl
      | some m2 =>
        dsimp only
        have hs2 := storeBits_size m1 m2 (byteAddr + 8) 8 _ h2
        cases h3 : m2.storeBits (byteAddr + 16) 8 ((fields.lookup "l2").getD 0#64) with
        | none => rfl
        | some m3 =>
          dsimp only
          have hs3 := storeBits_size m2 m3 (byteAddr + 16) 8 _ h3
          unfold ByteMemory.storeBits
          have hNotLe : ¬ ((byteAddr + 24) + 8 ≤ m3.bytes.size) := by omega
          simp [hNotLe]
  | _ =>
    simp only [storeTypedElem]
    unfold ByteMemory.storeBits
    have hNotLe : ¬ (byteAddr + _ ≤ mem.bytes.size) := Nat.not_le_of_gt h_oob
    simp [hNotLe]

/-- Out-of-bounds `device` buffer write safety: whenever the byte span
    `elemIdx * elemTy.byteWidth + elemTy.byteWidth` exceeds `mem.size`, `writeDeviceBuffer`
    catches the violation and returns `MSLOutcome.outOfBoundsWrite .device bufIdx elemIdx`. -/
theorem oob_device_write_caught (g : MSLGroupState) (bufIdx : Nat) (elemTy : MSLType)
    (elemIdx : Nat) (val : BitVec 64) (fields : List (String × BitVec 64)) (mem : ByteMemory)
    (h_buf : g.deviceBuffers.lookup bufIdx = some mem)
    (h_oob : mem.bytes.size < elemIdx * elemTy.byteWidth + elemTy.byteWidth) :
    writeDeviceBuffer g bufIdx elemTy elemIdx val fields =
      .outOfBoundsWrite .device bufIdx elemIdx := by
  simp [writeDeviceBuffer, h_buf,
    storeTypedElem_oob mem elemTy (elemIdx * elemTy.byteWidth) val fields h_oob]

/-- Division by zero traps with `MSLOutcome.divisionByZero` rather than returning `0`. -/
theorem msl_div_zero_traps (g : MSLGroupState) (th : MSLThreadState)
    (rx ry : String) (vx : BitVec 64)
    (h_rx : th.locals.lookup? rx = some vx)
    (h_ty : th.locals.lookupType? rx = some .ulong)
    (h_ry : th.locals.lookup? ry = some 0#64) :
    evalMSLExpr g th (.div (.var rx) (.var ry)) = .divisionByZero := by
  simp [evalMSLExpr, evalExprWithCall, bindEval, finishBin, inferExprType,
    evalTypedBin, propagateErr, h_rx, h_ty, h_ry]

/-- Signed 32-bit `INT32_MIN / -1` traps with `MSLOutcome.signedDivOverflow`. -/
theorem msl_signed_div_overflow_traps (g : MSLGroupState) (th : MSLThreadState)
    (rx ry : String)
    (h_rx : th.locals.lookup? rx = some 2147483648#64)
    (h_ty : th.locals.lookupType? rx = some .int)
    (h_ry : th.locals.lookup? ry = some 4294967295#64) :
    evalMSLExpr g th (.div (.var rx) (.var ry)) = .signedDivOverflow := by
  simp [evalMSLExpr, evalExprWithCall, bindEval, finishBin, inferExprType,
    evalTypedBin, propagateErr, h_rx, h_ty, h_ry]

/-- Production C++ ternary `((ry != 0UL) ? (rx / ry) : 0UL)` short-circuits `rx / ry` when
    `ry == 0` and safely returns `0#64` even without evaluating `rx`. -/
theorem msl_guarded_div_zero_safe (g : MSLGroupState) (th : MSLThreadState)
    (rx ry : String)
    (h_ry : th.locals.lookup? ry = some 0#64)
    (h_ty : th.locals.lookupType? ry = some .ulong) :
    evalMSLExpr g th
      (.select (.ne (.var ry) (.immU64 0#64)) (.div (.var rx) (.var ry)) (.immU64 0#64)) =
      .ok 0#64 := by
  simp [evalMSLExpr, evalExprWithCall, bindEval, finishCmp, inferExprType,
    evalTypedCmp, h_ry, h_ty]

/-- Mutant `M9` soundness witness: replacing C++ short-circuit `?:` with Metal's eager
    `select(0UL, rx / ry, ry != 0UL)` evaluates `rx / ry` when `ry == 0` and traps with
    `MSLOutcome.divisionByZero`. -/
theorem msl_builtinSelect_eager_div_zero_traps (g : MSLGroupState) (th : MSLThreadState)
    (rx ry : String) (vx : BitVec 64)
    (h_rx : th.locals.lookup? rx = some vx)
    (h_ty : th.locals.lookupType? rx = some .ulong)
    (h_ry : th.locals.lookup? ry = some 0#64) :
    evalMSLExpr g th
      (.builtinSelect (.immU64 0#64) (.div (.var rx) (.var ry)) (.ne (.var ry) (.immU64 0#64))) =
      .divisionByZero := by
  simp [evalMSLExpr, evalExprWithCall, bindEval, finishBin, inferExprType,
    evalTypedBin, propagateErr, h_rx, h_ty, h_ry]

/-- Floating-point remainder (`%`) is rejected with `MSLOutcome.unsupportedFloatOp` instead of
    silently applying integer modulo to IEEE-754 bit patterns. -/
theorem msl_float_rem_unsupported (g : MSLGroupState) (th : MSLThreadState)
    (rx ry : String) (vx vy : BitVec 64)
    (h_rx : th.locals.lookup? rx = some vx)
    (h_ty : th.locals.lookupType? rx = some .float)
    (h_ry : th.locals.lookup? ry = some vy) :
    evalMSLExpr g th (.rem (.var rx) (.var ry)) = .unsupportedFloatOp "float remainder" := by
  simp [evalMSLExpr, evalExprWithCall, bindEval, finishBin, inferExprType,
    evalTypedBin, propagateErr, h_rx, h_ty, h_ry]

/-- Shifting a 32-bit `uint` by an amount `≥ 32` traps with `MSLOutcome.shiftOutOfRange`. -/
theorem msl_uint_shift_ge_width_traps (g : MSLGroupState) (th : MSLThreadState)
    (rx : String) (vx amt : BitVec 64)
    (h_rx : th.locals.lookup? rx = some vx)
    (h_ty : th.locals.lookupType? rx = some .uint)
    (h_ge : 32 ≤ amt.toNat) :
    evalMSLExpr g th (.shl (.var rx) (.immU64 amt)) = .shiftOutOfRange := by
  simp [evalMSLExpr, evalExprWithCall, bindEval, finishShift, inferExprType,
    MSLType.isFloat, MSLType.bitWidth, propagateErr, h_rx, h_ty, h_ge]

/-- Disjoint byte ranges never race: recording an access whose byte span lies strictly after a
    prior epoch entry succeeds without triggering `MSLOutcome.dataRace`. -/
theorem recordEpochAccess_disjoint_ok (a : MSLAccess) (tid : Dim3) (tgt : MSLMemTarget)
    (sp : MSLAddressSpace) (addr width : Nat) (isWrite : Bool)
    (h_disj : a.addr + a.width ≤ addr) :
    recordEpochAccess [a] tid tgt sp addr width isWrite =
      .ok [{ tid, target := tgt, addr, width, isWrite }, a] := by
  have hNo : ¬ (addr < a.addr + a.width ∧ a.addr < addr + width) := by omega
  simp [recordEpochAccess, findDataRace?, findDataRace?.go, rangesOverlap, hNo]

/-- Overlapping unsynchronized cross-thread write/read accesses on the same memory target trap
    with `MSLOutcome.dataRace`. -/
theorem recordEpochAccess_overlap_races (a : MSLAccess) (tid : Dim3) (tgt : MSLMemTarget)
    (sp : MSLAddressSpace) (addr width : Nat)
    (h_diff : (tid != a.tid) = true)
    (h_tgt : tgt = a.target)
    (h_ov1 : addr < a.addr + a.width)
    (h_ov2 : a.addr < addr + width) :
    recordEpochAccess [a] tid tgt sp addr width true = .dataRace sp (Nat.max addr a.addr) := by
  subst tgt
  have hTgt : (a.target == a.target) = true := by
    cases a.target with
    | deviceBuf idx => change (idx == idx) = true; simp
    | threadgroupArr nm => change (nm == nm) = true; simp
  have hOv : decide (addr < a.addr + a.width ∧ a.addr < addr + width) = true :=
    decide_eq_true ⟨h_ov1, h_ov2⟩
  simp [recordEpochAccess, findDataRace?, findDataRace?.go, rangesOverlap, h_diff, hTgt, hOv]

/-- Uniform `threadgroupBarrier` synchronization: when a non-empty threadgroup has every thread
    parked at `threadgroup_barrier`, `stepGroupBarrier` converges cleanly, advancing all threads
    past the barrier and clearing `epochLog` while preserving `deviceBuffers`, `constantBuffers`,
    and `threadgroupArrays`. -/
theorem threadgroupBarrier_uniform_converges (g : MSLGroupState)
    (h_nonempty : g.threads.isEmpty = false)
    (h_uniform : g.threads.all threadAtBarrier = true) :
    stepGroupBarrier g =
      .ok { g with threads := g.threads.map advanceBarrierThread, epochLog := [] } := by
  unfold stepGroupBarrier
  simp [h_nonempty, h_uniform]

/-- Divergent `threadgroupBarrier` detection: if the threadgroup is empty or at least one thread
    is not parked at `threadgroup_barrier` when barrier synchronization is attempted,
    `stepGroupBarrier` traps with `MSLOutcome.barrierDivergence`. -/
theorem threadgroupBarrier_divergent_errors (g : MSLGroupState)
    (h_div : (!g.threads.isEmpty && g.threads.all threadAtBarrier) = false) :
    stepGroupBarrier g = .barrierDivergence := by
  unfold stepGroupBarrier
  have hFalse : ¬ ((!g.threads.isEmpty && g.threads.all threadAtBarrier) = true) := by
    rw [h_div]; decide
  exact ite_eq_right_iff.mpr fun h => False.elim (hFalse h)

private theorem stepSimdgroup_preserves_const (g g' : MSLGroupState) (sgId : Nat)
    (h : stepSimdgroup g sgId = .ok g') :
    g'.constantBuffers = g.constantBuffers := by
  unfold stepSimdgroup at h
  dsimp only at h
  cases hLive : g.threads.filter (fun th => !th.halted && simdgroupOf g.groupDim th.tid == sgId) with
  | nil => simp [hLive] at h
  | cons leader rest =>
    simp [hLive] at h
    cases hStmts : leader.stmts with
    | nil => simp [hStmts] at h
    | cons hd tl =>
      cases hd <;> simp [hStmts] at h
      case simdShuffleXor =>
        cases hCS : stepSimdgroup.collectSrc g sgId g.epochLog g.threads <;>
          simp [hCS, propagateErr] at h
        case ok pair1 =>
          cases hAS : stepSimdgroup.applyShuffle g sgId pair1.1 g.epochLog g.threads <;>
            simp [hAS] at h
          rw [← h]
      case simdSum declTy dst leaderSrc =>
        cases hCS : stepSimdgroup.collectSum g sgId (inferExprType g leader.locals leaderSrc)
            g.epochLog g.threads <;>
          simp [hCS, propagateErr] at h
        case ok pair1 =>
          cases hAS : stepSimdgroup.applySum g sgId pair1.1 g.epochLog g.threads <;>
            simp [hAS] at h
          rw [← h]

private theorem stepFirstReady_preserves_const (g : MSLGroupState) :
    ∀ (pre suf : List MSLThreadState) (progressed : Bool) (g' : MSLGroupState),
      stepFirstReadyThread g pre suf = .ok (progressed, g') →
      g'.constantBuffers = g.constantBuffers
  | _, [], _, g', h => by
    simp [stepFirstReadyThread] at h
    rw [← h.2]
  | pre, th :: suf, progressed, g', h => by
    unfold stepFirstReadyThread at h
    split at h
    · exact stepFirstReady_preserves_const g (th :: pre) suf progressed g' h
    · cases hStmts : th.stmts with
      | nil =>
        simp [hStmts] at h
        rw [← h.2]
      | cons s rest =>
        simp [hStmts] at h
        cases hExec : execNonBarrierStmt g th s rest <;>
          simp [hExec, propagateErr] at h
        case ok pair =>
          rw [← h.2]
          exact exec_preserves_constant_buffers g th s rest pair.1 pair.2 hExec

private theorem stepGroup_preserves_const (g g' : MSLGroupState) (done : Bool)
    (hStep : stepGroup g = .ok (done, g')) :
    g'.constantBuffers = g.constantBuffers := by
  unfold stepGroup at hStep
  split at hStep
  · simp at hStep
    exact congrArg MSLGroupState.constantBuffers hStep.2.symm
  · cases hReady : stepFirstReadyThread g [] g.threads <;>
      simp [hReady, propagateErr] at hStep
    case ok rpair =>
      rcases rpair with ⟨progressed, gMid⟩
      have hC1 := stepFirstReady_preserves_const g [] g.threads progressed gMid hReady
      cases progressed with
      | true =>
        simp at hStep
        exact (congrArg MSLGroupState.constantBuffers hStep.2.symm).trans hC1
      | false =>
        simp at hStep
        cases hFind : gMid.threads.find? (fun th => !th.halted && threadAtSimdOp th) with
        | some th =>
          simp [hFind] at hStep
          cases hSimd : stepSimdgroup gMid (simdgroupOf gMid.groupDim th.tid) <;>
            simp [hSimd] at hStep
          case ok synced =>
            have hEq1 := congrArg MSLGroupState.constantBuffers hStep.2.symm
            have hEq2 := stepSimdgroup_preserves_const gMid synced _ hSimd
            exact (hEq1.trans hEq2).trans hC1
        | none =>
          simp [hFind] at hStep
          cases hBar : stepGroupBarrier gMid <;> simp [hBar] at hStep
          case ok synced =>
            have hEq1 := congrArg MSLGroupState.constantBuffers hStep.2.symm
            unfold stepGroupBarrier at hBar
            split at hBar <;> simp at hBar
            have hEq2 : synced.constantBuffers = gMid.constantBuffers := by rw [← hBar]
            exact (hEq1.trans hEq2).trans hC1

/-- Multi-step `constant` buffer immutability: running an entire threadgroup for any `fuel`
    budget preserves `constantBuffers` unchanged. -/
theorem runGroup_preserves_constant_buffers (fuel : Nat) (g g' : MSLGroupState)
    (h : runGroup fuel g = .ok g') :
    g'.constantBuffers = g.constantBuffers := by
  induction fuel generalizing g with
  | zero =>
    unfold runGroup at h
    split at h <;> simp at h
    exact congrArg MSLGroupState.constantBuffers h.symm
  | succ f ih =>
    unfold runGroup at h
    cases hStep : stepGroup g <;> simp [hStep, propagateErr] at h
    case ok pair =>
      rcases pair with ⟨done, gNext⟩
      have hStepConst := stepGroup_preserves_const g gNext done hStep
      cases done with
      | true =>
        simp at h
        exact (congrArg MSLGroupState.constantBuffers h.symm).trans hStepConst
      | false =>
        simp at h
        exact (ih gNext h).trans hStepConst

/-- Halted threadgroup fixed-point: once all threads in `g` have halted, `runGroup` returns
    `.ok g` for every step budget `fuel`. -/
theorem runGroup_halted (fuel : Nat) (g : MSLGroupState)
    (h_halted : g.threads.all (·.halted) = true) :
    runGroup fuel g = .ok g := by
  cases fuel with
  | zero =>
    unfold runGroup
    simp [h_halted]
  | succ f =>
    unfold runGroup stepGroup
    simp [h_halted]

/-- Monotone fuel stability of `runGroup`: once `runGroup f1 g` reaches a terminal
    (non-`fuelExhausted`) outcome `out`, any larger step budget `f2 ≥ f1` reaches the exact same
    terminal outcome `out`. -/
theorem runGroup_mono_fuel (f1 f2 : Nat) (g : MSLGroupState)
    (out : MSLOutcome MSLGroupState)
    (h1 : runGroup f1 g = out)
    (h_term : out ≠ .fuelExhausted)
    (h_le : f1 ≤ f2) :
    runGroup f2 g = out := by
  induction f1 generalizing f2 g with
  | zero =>
    unfold runGroup at h1
    cases hAll : g.threads.all (·.halted)
    · simp [hAll] at h1
      exact False.elim (h_term h1.symm)
    · simp [hAll] at h1
      rw [runGroup_halted f2 g hAll]
      exact h1
  | succ f1' ih =>
    cases f2 with
    | zero => omega
    | succ f2' =>
      have hLe' : f1' ≤ f2' := Nat.le_of_succ_le_succ h_le
      unfold runGroup at h1 ⊢
      cases hStep : stepGroup g <;> simp [hStep, propagateErr] at h1 ⊢
      case ok pair =>
        rcases pair with ⟨done, g'⟩
        cases done with
        | true =>
          simp at h1 ⊢
          exact h1
        | false =>
          simp at h1 ⊢
          exact ih f2' g' h1 hLe'
      all_goals exact h1

/-- Fuel-independent operational determinism of the Metal SIMT threadgroup semantics (`runGroup`):
    any two executions from the same initial `MSLGroupState` under arbitrary step budgets `f1`
    and `f2` that both reach terminal (non-`fuelExhausted`) outcomes produce identical results. -/
theorem runGroup_deterministic (f1 f2 : Nat) (g : MSLGroupState)
    (out1 out2 : MSLOutcome MSLGroupState)
    (h1 : runGroup f1 g = out1)
    (h2 : runGroup f2 g = out2)
    (hne1 : out1 ≠ .fuelExhausted)
    (hne2 : out2 ≠ .fuelExhausted) :
    out1 = out2 := by
  by_cases hLe : f1 ≤ f2
  · have hMono := runGroup_mono_fuel f1 f2 g out1 h1 hne1 hLe
    exact hMono.symm.trans h2
  · have hLe2 : f2 ≤ f1 := by omega
    have hMono := runGroup_mono_fuel f2 f1 g out2 h2 hne2 hLe2
    exact h1.symm.trans hMono

/-- 1:1 injectivity of `ppMSLAddressSpace`: distinct MSL address spaces render to distinct tokens. -/
theorem ppMSLAddressSpace_injective (s1 s2 : MSLAddressSpace)
    (h : ppMSLAddressSpace s1 = ppMSLAddressSpace s2) :
    s1 = s2 := by
  cases s1 <;> cases s2 <;> first | rfl | exact absurd h (by decide)

/-- Read-only `device const` pointers render with the explicit `device const <T>*` qualifier. -/
theorem ppMSLType_device_const_pointer (elem : MSLType) :
    ppMSLType (.pointer .device true elem) = "device const " ++ ppMSLType elem ++ "*" := rfl

private theorem charList_isPrefixOf_append :
    ∀ (xs ys : List Char), List.isPrefixOf xs (xs ++ ys) = true
  | [], _ => rfl
  | x :: xs, ys => by
    simp [charList_isPrefixOf_append xs ys]

/-- Structural header well-formedness of `ppMSLModule`: every rendered Metal module begins with
    `#include <metal_stdlib>\nusing namespace metal;`. -/
theorem ppMSLModule_header_prefix (m : MSLModule) :
    List.isPrefixOf ppMSLModuleHeader.toList (ppMSLModule m).toList = true := by
  unfold ppMSLModule
  cases (m.structs.map ppMSLStructDecl ++ m.funcs.map ppMSLFuncDecl ++ m.kernels.map ppMSLKernel) with
  | nil =>
    rw [String.toList_append]
    exact charList_isPrefixOf_append _ _
  | cons b bs =>
    simp only [String.append_assoc, String.toList_append]
    exact charList_isPrefixOf_append _ _

/-- Structural signature well-formedness of `ppMSLKernel`: every rendered compute kernel begins
    with `kernel void <name>(\n`. -/
theorem ppMSLKernel_signature_prefix (k : MSLKernelDecl) :
    List.isPrefixOf (ppMSLKernelSignaturePrefix k.name).toList (ppMSLKernel k).toList = true := by
  unfold ppMSLKernel
  simp only [String.append_assoc, String.toList_append]
  exact charList_isPrefixOf_append _ _

private theorem getLast_append_singleton (xs : List Char) (c : Char) :
    (xs ++ [c]).getLast? = some c := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    cases rest with
    | nil => rfl
    | cons y ys => exact ih

private theorem semicolon_toList_eq : ";".toList = [';'] := by decide

/-- Structural well-formedness of `ppMSLStmt` on `threadgroupBarrier`: renders a semicolon-terminated
    `threadgroup_barrier(mem_flags::mem_threadgroup);` statement for any indentation prefix. -/
theorem ppMSLStmt_barrier_semicolon (indent : String) :
    (ppMSLStmt indent .threadgroupBarrier).toList.getLast? = some ';' := by
  unfold ppMSLStmt
  simp only [String.append_assoc, String.toList_append, semicolon_toList_eq]
  rw [← List.append_assoc]
  exact getLast_append_singleton _ ';'

end LeanNative.Backend.MetalAst
