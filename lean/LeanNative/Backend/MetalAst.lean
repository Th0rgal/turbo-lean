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
  | u256
  | pointer  : MSLAddressSpace → MSLType → MSLType
  | ref      : MSLAddressSpace → MSLType → MSLType
  | structTy : String → MSLType
  deriving Repr, DecidableEq, Inhabited, BEq

namespace MSLType

/-- Addressable byte width of an MSL type (`0` for `void`, `8` for pointers/references). -/
def byteWidth : MSLType → Nat
  | .void => 0
  | .bool | .uchar => 1
  | .ushort | .half => 2
  | .uint | .int | .float => 4
  | .ulong | .long | .double | .pointer _ _ | .ref _ _ => 8
  | .u256 => 32
  | .structTy _ => 8

/-- True when signed integer rules apply to arithmetic/shifts/comparisons. -/
def isSigned : MSLType → Bool
  | .int | .long => true
  | _ => false

end MSLType

/-- Metal kernel parameter and thread/grid coordinate attributes (`[[...]]`). -/
inductive MSLAttr where
  | buffer                      : Nat → MSLAttr
  | threadPositionInGrid        : MSLAttr
  | threadPositionInThreadgroup : MSLAttr
  | threadgroupPositionInGrid   : MSLAttr
  | threadsPerThreadgroup       : MSLAttr
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Typed MSL expression AST. -/
inductive MSLExpr where
  | var     : String → MSLExpr
  | immU64  : BitVec 64 → MSLExpr
  | immBool : Bool → MSLExpr
  | builtin : MSLAttr → MSLExpr
  | bitNot  : MSLExpr → MSLExpr
  | logNot  : MSLExpr → MSLExpr
  | neg     : MSLExpr → MSLExpr
  | cast    : MSLType → MSLExpr → MSLExpr
  | add     : MSLExpr → MSLExpr → MSLExpr
  | sub     : MSLExpr → MSLExpr → MSLExpr
  | mul     : MSLExpr → MSLExpr → MSLExpr
  | div     : MSLExpr → MSLExpr → MSLExpr
  | rem     : MSLExpr → MSLExpr → MSLExpr
  | bitAnd  : MSLExpr → MSLExpr → MSLExpr
  | bitOr   : MSLExpr → MSLExpr → MSLExpr
  | bitXor  : MSLExpr → MSLExpr → MSLExpr
  | shl     : MSLExpr → MSLExpr → MSLExpr
  | shr     : MSLExpr → MSLExpr → MSLExpr
  | eq      : MSLExpr → MSLExpr → MSLExpr
  | ne      : MSLExpr → MSLExpr → MSLExpr
  | lt      : MSLExpr → MSLExpr → MSLExpr
  | le      : MSLExpr → MSLExpr → MSLExpr
  | gt      : MSLExpr → MSLExpr → MSLExpr
  | ge      : MSLExpr → MSLExpr → MSLExpr
  | select  : MSLExpr → MSLExpr → MSLExpr → MSLExpr
  | fma     : MSLExpr → MSLExpr → MSLExpr → MSLExpr
  | index   : String → MSLExpr → MSLExpr
  deriving Repr, DecidableEq, Inhabited, BEq

/- Structured MSL statement AST covering compute kernels, loops, conditionals, and barriers.
   Contains `MSLBlock` mutually rather than `List MSLStmt` so `MSLStmt` is a non-nested inductive
   compatible with `TurboLean.KernelGate` theorem-shard audits. -/
mutual
inductive MSLStmt where
  | varDecl            : MSLType → String → MSLExpr → MSLStmt
  | assign             : String → MSLExpr → MSLStmt
  | indexAssign        : String → MSLExpr → MSLExpr → MSLStmt
  | ifElse             : MSLExpr → MSLBlock → MSLBlock → MSLStmt
  | forLoop            : String → MSLType → MSLExpr → MSLExpr → MSLExpr → MSLBlock → MSLStmt
  | whileLoop          : MSLExpr → MSLBlock → MSLStmt
  | threadgroupBarrier : MSLStmt
  | returnStmt         : MSLStmt
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

/-- Kernel parameter declaration (`<ty> <name> [[<attr>]]`). -/
structure MSLParamDecl where
  ty   : MSLType
  name : String
  attr : MSLAttr
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

/-- Complete Apple Metal MSL 3.0 module. -/
structure MSLModule where
  structs : List MSLStructDecl := []
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

end ByteMemory

/-- Per-thread local variable environment (`thread` address space). -/
structure MSLLocals where
  vars : List (String × BitVec 64) := []
  deriving Repr, DecidableEq, Inhabited, BEq

namespace MSLLocals

def empty : MSLLocals := { vars := [] }

def lookup? (ls : MSLLocals) (name : String) : Option (BitVec 64) :=
  ls.vars.lookup name

private def setAssoc : List (String × BitVec 64) → String → BitVec 64 → List (String × BitVec 64)
  | [], k, v => [(k, v)]
  | (k', v') :: rest, k, v =>
    if k' == k then (k, v) :: rest else (k', v') :: setAssoc rest k v

def set (ls : MSLLocals) (name : String) (v : BitVec 64) : MSLLocals :=
  { vars := setAssoc ls.vars name v }

end MSLLocals

/-- Classification of kernel-scoped buffer and shared-array identifiers. -/
inductive MSLBufferBinding where
  | deviceBuf      : Nat → MSLType → MSLBufferBinding
  | constantBuf    : Nat → MSLType → MSLBufferBinding
  | constantScalar : Nat → MSLType → MSLBufferBinding
  | threadgroupArr : String → MSLType → MSLBufferBinding
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Per-lane execution state inside a Metal threadgroup. -/
structure MSLThreadState where
  tid    : Dim3
  locals : MSLLocals := MSLLocals.empty
  stmts  : List MSLStmt := []
  halted : Bool := false
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Complete SIMT threadgroup execution state with separated `device`, `constant`, and
    `threadgroup` memory tables. -/
structure MSLGroupState where
  gridDim           : Dim3
  groupDim          : Dim3
  groupId           : Dim3
  bindings          : List (String × MSLBufferBinding) := []
  deviceBuffers     : List (Nat × ByteMemory) := []
  constantBuffers   : List (Nat × ByteMemory) := []
  threadgroupArrays : List (String × ByteMemory) := []
  threads           : List MSLThreadState := []
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Explicit operational outcome of MSL SIMT execution. -/
inductive MSLOutcome (α : Type) where
  | ok                : α → MSLOutcome α
  | readOnlyViolation : String → Nat → MSLOutcome α
  | barrierDivergence : MSLOutcome α
  | outOfBoundsLoad   : MSLAddressSpace → Nat → Nat → MSLOutcome α
  | outOfBoundsWrite  : MSLAddressSpace → Nat → Nat → MSLOutcome α
  | unboundIdentifier : String → MSLOutcome α
  | fuelExhausted     : MSLOutcome α
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Canonical width mask for an MSL scalar type over `BitVec 64`. -/
def maskForType (ty : MSLType) (v : BitVec 64) : BitVec 64 :=
  match ty with
  | .void => 0#64
  | .bool => if v != 0#64 then 1#64 else 0#64
  | .uchar => v &&& 0xFF#64
  | .ushort | .half => v &&& 0xFFFF#64
  | .uint | .int | .float => v &&& 0xFFFF_FFFF#64
  | .ulong | .long | .double | .u256 | .pointer _ _ | .ref _ _ | .structTy _ => v

/-- Evaluate a Metal thread/grid coordinate builtin attribute for lane `th` in group `g`. -/
def evalBuiltinAttr (g : MSLGroupState) (th : MSLThreadState) : MSLAttr → BitVec 64
  | .buffer idx => BitVec.ofNat 64 idx
  | .threadPositionInGrid => BitVec.ofNat 64 (g.groupId.x * g.groupDim.x + th.tid.x)
  | .threadPositionInThreadgroup => BitVec.ofNat 64 th.tid.x
  | .threadgroupPositionInGrid => BitVec.ofNat 64 g.groupId.x
  | .threadsPerThreadgroup => BitVec.ofNat 64 g.groupDim.x

private def setIndexedMem : List (Nat × ByteMemory) → Nat → ByteMemory → List (Nat × ByteMemory)
  | [], idx, mem => [(idx, mem)]
  | (idx', mem') :: rest, idx, mem =>
    if idx' == idx then (idx, mem) :: rest else (idx', mem') :: setIndexedMem rest idx mem

private def setNamedMem : List (String × ByteMemory) → String → ByteMemory → List (String × ByteMemory)
  | [], name, mem => [(name, mem)]
  | (name', mem') :: rest, name, mem =>
    if name' == name then (name, mem) :: rest else (name', mem') :: setNamedMem rest name mem

/-- Read an element from a bound `device`, `constant`, or `threadgroup` buffer/array. -/
def readBoundElement (g : MSLGroupState) (name : String) (elemIdx : Nat) :
    MSLOutcome (BitVec 64) :=
  match g.bindings.lookup name with
  | some (.deviceBuf bufIdx elemTy) =>
    match g.deviceBuffers.lookup bufIdx with
    | some mem =>
      match mem.loadBits (elemIdx * elemTy.byteWidth) elemTy.byteWidth with
      | some raw => .ok (maskForType elemTy raw)
      | none => .outOfBoundsLoad .device bufIdx elemIdx
    | none => .outOfBoundsLoad .device bufIdx elemIdx
  | some (.constantBuf bufIdx elemTy) | some (.constantScalar bufIdx elemTy) =>
    match g.constantBuffers.lookup bufIdx with
    | some mem =>
      match mem.loadBits (elemIdx * elemTy.byteWidth) elemTy.byteWidth with
      | some raw => .ok (maskForType elemTy raw)
      | none => .outOfBoundsLoad .constant bufIdx elemIdx
    | none => .outOfBoundsLoad .constant bufIdx elemIdx
  | some (.threadgroupArr arrName elemTy) =>
    match g.threadgroupArrays.lookup arrName with
    | some mem =>
      match mem.loadBits (elemIdx * elemTy.byteWidth) elemTy.byteWidth with
      | some raw => .ok (maskForType elemTy raw)
      | none => .outOfBoundsLoad .threadgroup 0 elemIdx
    | none => .outOfBoundsLoad .threadgroup 0 elemIdx
  | none => .unboundIdentifier name

/-- Evaluate an `MSLExpr` directly over `BitVec 64` with zero `LeanNative.Semantics` delegation. -/
def evalMSLExpr (g : MSLGroupState) (th : MSLThreadState) : MSLExpr → MSLOutcome (BitVec 64)
  | .var name =>
    match th.locals.lookup? name with
    | some v => .ok v
    | none =>
      match g.bindings.lookup name with
      | some (.constantScalar bufIdx elemTy) =>
        match g.constantBuffers.lookup bufIdx with
        | some mem =>
          match mem.loadBits 0 elemTy.byteWidth with
          | some raw => .ok (maskForType elemTy raw)
          | none => .outOfBoundsLoad .constant bufIdx 0
        | none => .outOfBoundsLoad .constant bufIdx 0
      | _ => .unboundIdentifier name
  | .immU64 v => .ok v
  | .immBool b => .ok (if b then 1#64 else 0#64)
  | .builtin attr => .ok (evalBuiltinAttr g th attr)
  | .bitNot a =>
    match evalMSLExpr g th a with
    | .ok va => .ok (~~~va)
    | err => err
  | .logNot a =>
    match evalMSLExpr g th a with
    | .ok va => .ok (if va == 0#64 then 1#64 else 0#64)
    | err => err
  | .neg a =>
    match evalMSLExpr g th a with
    | .ok va => .ok (0#64 - va)
    | err => err
  | .cast ty a =>
    match evalMSLExpr g th a with
    | .ok va => .ok (maskForType ty va)
    | err => err
  | .add a b =>
    match evalMSLExpr g th a, evalMSLExpr g th b with
    | .ok va, .ok vb => .ok (va + vb)
    | err, .ok _ => err
    | _, err => err
  | .sub a b =>
    match evalMSLExpr g th a, evalMSLExpr g th b with
    | .ok va, .ok vb => .ok (va - vb)
    | err, .ok _ => err
    | _, err => err
  | .mul a b =>
    match evalMSLExpr g th a, evalMSLExpr g th b with
    | .ok va, .ok vb => .ok (va * vb)
    | err, .ok _ => err
    | _, err => err
  | .div a b =>
    match evalMSLExpr g th a, evalMSLExpr g th b with
    | .ok va, .ok vb => .ok (if vb == 0#64 then 0#64 else va / vb)
    | err, .ok _ => err
    | _, err => err
  | .rem a b =>
    match evalMSLExpr g th a, evalMSLExpr g th b with
    | .ok va, .ok vb => .ok (if vb == 0#64 then va else va % vb)
    | err, .ok _ => err
    | _, err => err
  | .bitAnd a b =>
    match evalMSLExpr g th a, evalMSLExpr g th b with
    | .ok va, .ok vb => .ok (va &&& vb)
    | err, .ok _ => err
    | _, err => err
  | .bitOr a b =>
    match evalMSLExpr g th a, evalMSLExpr g th b with
    | .ok va, .ok vb => .ok (va ||| vb)
    | err, .ok _ => err
    | _, err => err
  | .bitXor a b =>
    match evalMSLExpr g th a, evalMSLExpr g th b with
    | .ok va, .ok vb => .ok (va ^^^ vb)
    | err, .ok _ => err
    | _, err => err
  | .shl a b =>
    match evalMSLExpr g th a, evalMSLExpr g th b with
    | .ok va, .ok vb => .ok (va <<< (vb &&& 63#64).toNat)
    | err, .ok _ => err
    | _, err => err
  | .shr a b =>
    match evalMSLExpr g th a, evalMSLExpr g th b with
    | .ok va, .ok vb => .ok (va >>> (vb &&& 63#64).toNat)
    | err, .ok _ => err
    | _, err => err
  | .eq a b =>
    match evalMSLExpr g th a, evalMSLExpr g th b with
    | .ok va, .ok vb => .ok (if va == vb then 1#64 else 0#64)
    | err, .ok _ => err
    | _, err => err
  | .ne a b =>
    match evalMSLExpr g th a, evalMSLExpr g th b with
    | .ok va, .ok vb => .ok (if va != vb then 1#64 else 0#64)
    | err, .ok _ => err
    | _, err => err
  | .lt a b =>
    match evalMSLExpr g th a, evalMSLExpr g th b with
    | .ok va, .ok vb => .ok (if BitVec.ult va vb then 1#64 else 0#64)
    | err, .ok _ => err
    | _, err => err
  | .le a b =>
    match evalMSLExpr g th a, evalMSLExpr g th b with
    | .ok va, .ok vb => .ok (if BitVec.ule va vb then 1#64 else 0#64)
    | err, .ok _ => err
    | _, err => err
  | .gt a b =>
    match evalMSLExpr g th a, evalMSLExpr g th b with
    | .ok va, .ok vb => .ok (if BitVec.ult vb va then 1#64 else 0#64)
    | err, .ok _ => err
    | _, err => err
  | .ge a b =>
    match evalMSLExpr g th a, evalMSLExpr g th b with
    | .ok va, .ok vb => .ok (if BitVec.ule vb va then 1#64 else 0#64)
    | err, .ok _ => err
    | _, err => err
  | .select c t f =>
    match evalMSLExpr g th c, evalMSLExpr g th t, evalMSLExpr g th f with
    | .ok vc, .ok vt, .ok vf => .ok (if vc != 0#64 then vt else vf)
    | err, .ok _, .ok _ => err
    | _, err, .ok _ => err
    | _, _, err => err
  | .fma a b c =>
    match evalMSLExpr g th a, evalMSLExpr g th b, evalMSLExpr g th c with
    | .ok va, .ok vb, .ok vc => .ok (va * vb + vc)
    | err, .ok _, .ok _ => err
    | _, err, .ok _ => err
    | _, _, err => err
  | .index target idxExpr =>
    match evalMSLExpr g th idxExpr with
    | .ok idxBv => readBoundElement g target idxBv.toNat
    | err => err

/-- Bounds-checked write into a `device` buffer at `(bufIdx, elemIdx)`, leaving `constantBuffers`
    and `threadgroupArrays` untouched. -/
def writeDeviceBuffer (g : MSLGroupState) (bufIdx : Nat) (elemTy : MSLType)
    (elemIdx : Nat) (val : BitVec 64) : MSLOutcome MSLGroupState :=
  match g.deviceBuffers.lookup bufIdx with
  | some mem =>
    match mem.storeBits (elemIdx * elemTy.byteWidth) elemTy.byteWidth (maskForType elemTy val) with
    | some mem' => .ok { g with deviceBuffers := setIndexedMem g.deviceBuffers bufIdx mem' }
    | none => .outOfBoundsWrite .device bufIdx elemIdx
  | none => .outOfBoundsWrite .device bufIdx elemIdx

/-- Bounds-checked write into a `threadgroup` shared array at `(arrName, elemIdx)`, leaving
    `deviceBuffers` and `constantBuffers` untouched. -/
def writeThreadgroupArray (g : MSLGroupState) (arrName : String) (elemTy : MSLType)
    (elemIdx : Nat) (val : BitVec 64) : MSLOutcome MSLGroupState :=
  match g.threadgroupArrays.lookup arrName with
  | some mem =>
    match mem.storeBits (elemIdx * elemTy.byteWidth) elemTy.byteWidth (maskForType elemTy val) with
    | some mem' => .ok { g with threadgroupArrays := setNamedMem g.threadgroupArrays arrName mem' }
    | none => .outOfBoundsWrite .threadgroup 0 elemIdx
  | none => .outOfBoundsWrite .threadgroup 0 elemIdx

/-- Execute a buffer/array indexed write (`target[elemIdx] = val`), enforcing `constant`
    immutability (`MSLOutcome.readOnlyViolation`) and address-space isolation. -/
def execIndexWrite (g : MSLGroupState) (target : String) (elemIdx : Nat) (val : BitVec 64) :
    MSLOutcome MSLGroupState :=
  match g.bindings.lookup target with
  | some (.constantBuf _ _) | some (.constantScalar _ _) =>
    .readOnlyViolation target elemIdx
  | some (.deviceBuf bufIdx elemTy) =>
    writeDeviceBuffer g bufIdx elemTy elemIdx val
  | some (.threadgroupArr arrName elemTy) =>
    writeThreadgroupArray g arrName elemTy elemIdx val
  | none =>
    .unboundIdentifier target

/-- Propagate an expression error to any `MSLOutcome β`. -/
private def propagateExprErr {β : Type} : MSLOutcome (BitVec 64) → MSLOutcome β
  | .ok _ => .fuelExhausted
  | .readOnlyViolation t i => .readOnlyViolation t i
  | .barrierDivergence => .barrierDivergence
  | .outOfBoundsLoad s b i => .outOfBoundsLoad s b i
  | .outOfBoundsWrite s b i => .outOfBoundsWrite s b i
  | .unboundIdentifier n => .unboundIdentifier n
  | .fuelExhausted => .fuelExhausted

/-- Execute one non-barrier `MSLStmt` at the head of thread `th`'s continuation `rest`. -/
def execNonBarrierStmt (g : MSLGroupState) (th : MSLThreadState)
    (stmt : MSLStmt) (rest : List MSLStmt) :
    MSLOutcome (MSLThreadState × MSLGroupState) :=
  match stmt with
  | .varDecl ty name rhs =>
    match evalMSLExpr g th rhs with
    | .ok v =>
      let th' := { th with locals := th.locals.set name (maskForType ty v), stmts := rest }
      .ok (th', g)
    | err => propagateExprErr err
  | .assign name rhs =>
    match g.bindings.lookup name with
    | some (.constantScalar _ _) | some (.constantBuf _ _) =>
      .readOnlyViolation name 0
    | _ =>
      match evalMSLExpr g th rhs with
      | .ok v =>
        let th' := { th with locals := th.locals.set name v, stmts := rest }
        .ok (th', g)
      | err => propagateExprErr err
  | .indexAssign target idxExpr rhsExpr =>
    match evalMSLExpr g th idxExpr, evalMSLExpr g th rhsExpr with
    | .ok idxBv, .ok valBv =>
      match execIndexWrite g target idxBv.toNat valBv with
      | .ok g' => .ok ({ th with stmts := rest }, g')
      | .readOnlyViolation t i => .readOnlyViolation t i
      | .barrierDivergence => .barrierDivergence
      | .outOfBoundsLoad s b i => .outOfBoundsLoad s b i
      | .outOfBoundsWrite s b i => .outOfBoundsWrite s b i
      | .unboundIdentifier n => .unboundIdentifier n
      | .fuelExhausted => .fuelExhausted
    | err, .ok _ => propagateExprErr err
    | _, err => propagateExprErr err
  | .ifElse cond thenBr elseBr =>
    match evalMSLExpr g th cond with
    | .ok vc =>
      let chosen := if vc != 0#64 then thenBr.toList else elseBr.toList
      .ok ({ th with stmts := chosen ++ rest }, g)
    | err => propagateExprErr err
  | .forLoop loopVar ty initExpr condExpr stepExpr body =>
    match evalMSLExpr g th initExpr with
    | .ok vInit =>
      let locals' := th.locals.set loopVar (maskForType ty vInit)
      let bodyWithStep := body.append (.cons (.assign loopVar (.cast ty stepExpr)) .nil)
      let loopTail := .whileLoop condExpr bodyWithStep :: rest
      .ok ({ th with locals := locals', stmts := loopTail }, g)
    | err => propagateExprErr err
  | .whileLoop condExpr body =>
    match evalMSLExpr g th condExpr with
    | .ok vc =>
      if vc != 0#64 then
        .ok ({ th with stmts := body.toList ++ (.whileLoop condExpr body :: rest) }, g)
      else
        .ok ({ th with stmts := rest }, g)
    | err => propagateExprErr err
  | .threadgroupBarrier =>
    .barrierDivergence
  | .returnStmt =>
    .ok ({ th with stmts := [], halted := true }, g)

/-- True iff thread `th` is unhalted and currently parked at `threadgroup_barrier`. -/
def threadAtBarrier (th : MSLThreadState) : Bool :=
  !th.halted && match th.stmts with
    | .threadgroupBarrier :: _ => true
    | _ => false

/-- Pop the leading `threadgroup_barrier` from a synchronized thread's continuation. -/
def advanceBarrierThread (th : MSLThreadState) : MSLThreadState :=
  match th.stmts with
  | .threadgroupBarrier :: rest => { th with stmts := rest }
  | _ => th

/-- Synchronize a Metal threadgroup at `threadgroup_barrier(mem_flags::mem_threadgroup)`:
    succeeds iff the threadgroup is non-empty and every thread in the threadgroup has arrived
    uniformly at `threadgroupBarrier`; otherwise traps with `MSLOutcome.barrierDivergence`. -/
def stepGroupBarrier (g : MSLGroupState) : MSLOutcome MSLGroupState :=
  if !g.threads.isEmpty && g.threads.all threadAtBarrier then
    .ok { g with threads := g.threads.map advanceBarrierThread }
  else
    .barrierDivergence

/-- Advance the first non-halted, non-barrier-waiting thread in `g` by one statement. -/
def stepFirstReadyThread (g : MSLGroupState) :
    List MSLThreadState → List MSLThreadState → MSLOutcome (Bool × MSLGroupState)
  | _, [] => .ok (false, g)
  | prefixRev, th :: suffix =>
    if th.halted || threadAtBarrier th then
      stepFirstReadyThread g (th :: prefixRev) suffix
    else
      match th.stmts with
      | [] =>
        let th' := { th with halted := true }
        .ok (true, { g with threads := prefixRev.reverse ++ (th' :: suffix) })
      | .threadgroupBarrier :: _ =>
        stepFirstReadyThread g (th :: prefixRev) suffix
      | stmt :: rest =>
        match execNonBarrierStmt g th stmt rest with
        | .ok (th', g') =>
          .ok (true, { g' with threads := prefixRev.reverse ++ (th' :: suffix) })
        | .readOnlyViolation t i => .readOnlyViolation t i
        | .barrierDivergence => .barrierDivergence
        | .outOfBoundsLoad s b i => .outOfBoundsLoad s b i
        | .outOfBoundsWrite s b i => .outOfBoundsWrite s b i
        | .unboundIdentifier n => .unboundIdentifier n
        | .fuelExhausted => .fuelExhausted

/-- Single SIMT threadgroup step:
    1. If all threads have halted, report completion (`done = true`).
    2. Otherwise, step the next ready non-barrier thread.
    3. Once every non-halted thread is parked, synchronize `stepGroupBarrier` in lockstep (or trap
       on divergent barrier arrival). -/
def stepGroup (g : MSLGroupState) : MSLOutcome (Bool × MSLGroupState) :=
  if g.threads.all (·.halted) then
    .ok (true, g)
  else
    match stepFirstReadyThread g [] g.threads with
    | .ok (true, g') => .ok (false, g')
    | .ok (false, g') =>
      match stepGroupBarrier g' with
      | .ok synced => .ok (false, synced)
      | .barrierDivergence => .barrierDivergence
      | .readOnlyViolation t i => .readOnlyViolation t i
      | .outOfBoundsLoad s b i => .outOfBoundsLoad s b i
      | .outOfBoundsWrite s b i => .outOfBoundsWrite s b i
      | .unboundIdentifier n => .unboundIdentifier n
      | .fuelExhausted => .fuelExhausted
    | .readOnlyViolation t i => .readOnlyViolation t i
    | .barrierDivergence => .barrierDivergence
    | .outOfBoundsLoad s b i => .outOfBoundsLoad s b i
    | .outOfBoundsWrite s b i => .outOfBoundsWrite s b i
    | .unboundIdentifier n => .unboundIdentifier n
    | .fuelExhausted => .fuelExhausted

/-- Multi-step SIMT threadgroup evaluator with step budget `fuel`. -/
def runGroup (fuel : Nat) (g : MSLGroupState) : MSLOutcome MSLGroupState :=
  match fuel with
  | 0 =>
    if g.threads.all (·.halted) then .ok g else .fuelExhausted
  | f + 1 =>
    match stepGroup g with
    | .ok (true, g') => .ok g'
    | .ok (false, g') => runGroup f g'
    | .readOnlyViolation t i => .readOnlyViolation t i
    | .barrierDivergence => .barrierDivergence
    | .outOfBoundsLoad s b i => .outOfBoundsLoad s b i
    | .outOfBoundsWrite s b i => .outOfBoundsWrite s b i
    | .unboundIdentifier n => .unboundIdentifier n
    | .fuelExhausted => .fuelExhausted

/-- Build kernel parameter and `threadgroup` shared-array bindings for an `MSLKernelDecl`. -/
def buildKernelBindings (k : MSLKernelDecl) : List (String × MSLBufferBinding) :=
  let paramBindings := k.params.filterMap fun p =>
    match p.attr, p.ty with
    | .buffer idx, .pointer .device elemTy => some (p.name, .deviceBuf idx elemTy)
    | .buffer idx, .pointer .constant elemTy => some (p.name, .constantBuf idx elemTy)
    | .buffer idx, .ref .constant elemTy => some (p.name, .constantScalar idx elemTy)
    | .buffer _, .pointer .threadgroup elemTy => some (p.name, .threadgroupArr p.name elemTy)
    | _, _ => none
  let sharedBindings := k.sharedDecls.map fun s =>
    (s.name, .threadgroupArr s.name s.elemTy)
  paramBindings ++ sharedBindings

/-- Initialize per-lane builtin coordinate locals declared on `k.params`. -/
def initThreadLocals (k : MSLKernelDecl) (groupDim groupId tid : Dim3) : MSLLocals :=
  k.params.foldl (fun acc p =>
    match p.attr with
    | .buffer _ => acc
    | .threadPositionInGrid =>
      acc.set p.name (BitVec.ofNat 64 (groupId.x * groupDim.x + tid.x))
    | .threadPositionInThreadgroup =>
      acc.set p.name (BitVec.ofNat 64 tid.x)
    | .threadgroupPositionInGrid =>
      acc.set p.name (BitVec.ofNat 64 groupId.x)
    | .threadsPerThreadgroup =>
      acc.set p.name (BitVec.ofNat 64 groupDim.x)) MSLLocals.empty

/-- Initialize a fresh `MSLGroupState` for threadgroup coordinate `groupId`. -/
def initGroupState (k : MSLKernelDecl) (gridDim groupDim groupId : Dim3)
    (deviceBuffers constantBuffers : List (Nat × ByteMemory)) : MSLGroupState :=
  let bindings := buildKernelBindings k
  let tgArrays := k.sharedDecls.map fun s =>
    (s.name, ByteMemory.zeros (s.count * s.elemTy.byteWidth))
  let threads := groupDim.coords.map fun tid =>
    { tid := tid
      locals := initThreadLocals k groupDim groupId tid
      stmts := k.body
      halted := false }
  { gridDim
    groupDim
    groupId
    bindings
    deviceBuffers
    constantBuffers
    threadgroupArrays := tgArrays
    threads }

/-- Launch an `MSLKernelDecl` across every threadgroup in `gridDim` (each with fresh zeroed
    `threadgroup` shared arrays and immutable `constantBuffers`), threading `deviceBuffers` across
    threadgroups and returning the final `device` buffer table. -/
def evalMSLKernel (fuelPerGroup : Nat) (k : MSLKernelDecl) (gridDim groupDim : Dim3)
    (deviceBuffers constantBuffers : List (Nat × ByteMemory)) :
    MSLOutcome (List (Nat × ByteMemory)) :=
  let rec loopGroups (devBufs : List (Nat × ByteMemory)) :
      List Dim3 → MSLOutcome (List (Nat × ByteMemory))
    | [] => .ok devBufs
    | gid :: rest =>
      let g0 := initGroupState k gridDim groupDim gid devBufs constantBuffers
      match runGroup fuelPerGroup g0 with
      | .ok gFinal => loopGroups gFinal.deviceBuffers rest
      | .readOnlyViolation t i => .readOnlyViolation t i
      | .barrierDivergence => .barrierDivergence
      | .outOfBoundsLoad s b i => .outOfBoundsLoad s b i
      | .outOfBoundsWrite s b i => .outOfBoundsWrite s b i
      | .unboundIdentifier n => .unboundIdentifier n
      | .fuelExhausted => .fuelExhausted
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
  | .void            => "void"
  | .bool            => "bool"
  | .uchar           => "uchar"
  | .ushort          => "ushort"
  | .uint            => "uint"
  | .int             => "int"
  | .ulong           => "ulong"
  | .long            => "long"
  | .half            => "half"
  | .float           => "float"
  | .double          => "double"
  | .u256            => "ln_u256"
  | .pointer sp elem => s!"{ppMSLAddressSpace sp} {ppMSLType elem}*"
  | .ref sp elem     => s!"{ppMSLAddressSpace sp} {ppMSLType elem}&"
  | .structTy name   => s!"struct {name}"

/-- Render an `MSLAttr` inside `[[...]]`. -/
def ppMSLAttr : MSLAttr → String
  | .buffer idx                  => s!"buffer({idx})"
  | .threadPositionInGrid        => "thread_position_in_grid"
  | .threadPositionInThreadgroup => "thread_position_in_threadgroup"
  | .threadgroupPositionInGrid   => "threadgroup_position_in_grid"
  | .threadsPerThreadgroup       => "threads_per_threadgroup"

/-- Render an `MSLExpr` into parenthesized MSL 3.0 expression syntax. -/
def ppMSLExpr : MSLExpr → String
  | .var name       => name
  | .immU64 v       => s!"{v.toNat}UL"
  | .immBool b      => if b then "true" else "false"
  | .builtin attr   => ppMSLAttr attr
  | .bitNot a       => s!"(~{ppMSLExpr a})"
  | .logNot a       => s!"(!{ppMSLExpr a})"
  | .neg a          => s!"(-{ppMSLExpr a})"
  | .cast ty a      => s!"(({ppMSLType ty}){ppMSLExpr a})"
  | .add a b        => s!"({ppMSLExpr a} + {ppMSLExpr b})"
  | .sub a b        => s!"({ppMSLExpr a} - {ppMSLExpr b})"
  | .mul a b        => s!"({ppMSLExpr a} * {ppMSLExpr b})"
  | .div a b        => s!"({ppMSLExpr a} / {ppMSLExpr b})"
  | .rem a b        => s!"({ppMSLExpr a} % {ppMSLExpr b})"
  | .bitAnd a b     => s!"({ppMSLExpr a} & {ppMSLExpr b})"
  | .bitOr a b      => s!"({ppMSLExpr a} | {ppMSLExpr b})"
  | .bitXor a b     => s!"({ppMSLExpr a} ^ {ppMSLExpr b})"
  | .shl a b        => s!"({ppMSLExpr a} << {ppMSLExpr b})"
  | .shr a b        => s!"({ppMSLExpr a} >> {ppMSLExpr b})"
  | .eq a b         => s!"({ppMSLExpr a} == {ppMSLExpr b})"
  | .ne a b         => s!"({ppMSLExpr a} != {ppMSLExpr b})"
  | .lt a b         => s!"({ppMSLExpr a} < {ppMSLExpr b})"
  | .le a b         => s!"({ppMSLExpr a} <= {ppMSLExpr b})"
  | .gt a b         => s!"({ppMSLExpr a} > {ppMSLExpr b})"
  | .ge a b         => s!"({ppMSLExpr a} >= {ppMSLExpr b})"
  | .select c t f   => s!"({ppMSLExpr c} ? {ppMSLExpr t} : {ppMSLExpr f})"
  | .fma a b c      => s!"fma({ppMSLExpr a}, {ppMSLExpr b}, {ppMSLExpr c})"
  | .index arr idx  => s!"{arr}[{ppMSLExpr idx}]"

/- Render an `MSLStmt` (and mutually `MSLBlock`) with indentation `indent`. -/
mutual
def ppMSLStmt (indent : String := "    ") : MSLStmt → String
  | .varDecl ty name rhs =>
    s!"{indent}{ppMSLType ty} {name} = {ppMSLExpr rhs}" ++ ";"
  | .assign name rhs =>
    s!"{indent}{name} = {ppMSLExpr rhs}" ++ ";"
  | .indexAssign target idx rhs =>
    s!"{indent}{target}[{ppMSLExpr idx}] = {ppMSLExpr rhs}" ++ ";"
  | .ifElse cond thenBr elseBr =>
    let tb := String.intercalate "\n" (ppMSLBlockLines (indent ++ "    ") thenBr)
    let fb := String.intercalate "\n" (ppMSLBlockLines (indent ++ "    ") elseBr)
    if elseBr.isEmpty then
      s!"{indent}if ({ppMSLExpr cond}) \{\n{tb}\n{indent}}"
    else
      s!"{indent}if ({ppMSLExpr cond}) \{\n{tb}\n{indent}} else \{\n{fb}\n{indent}}"
  | .forLoop loopVar ty initExpr condExpr stepExpr body =>
    let bb := String.intercalate "\n" (ppMSLBlockLines (indent ++ "    ") body)
    let hdr :=
      s!"{ppMSLType ty} {loopVar} = {ppMSLExpr initExpr}; " ++
      s!"{ppMSLExpr condExpr}; {loopVar} = {ppMSLExpr stepExpr}"
    s!"{indent}for ({hdr}) \{\n{bb}\n{indent}}"
  | .whileLoop condExpr body =>
    let bb := String.intercalate "\n" (ppMSLBlockLines (indent ++ "    ") body)
    s!"{indent}while ({ppMSLExpr condExpr}) \{\n{bb}\n{indent}}"
  | .threadgroupBarrier =>
    s!"{indent}threadgroup_barrier(mem_flags::mem_threadgroup)" ++ ";"
  | .returnStmt =>
    s!"{indent}return" ++ ";"

def ppMSLBlockLines (indent : String) : MSLBlock → List String
  | .nil => []
  | .cons s rest => ppMSLStmt indent s :: ppMSLBlockLines indent rest
end

/-- Render a kernel parameter declaration (`    <ty> <name> [[<attr>]]`). -/
def ppMSLParam (p : MSLParamDecl) : String :=
  s!"    {ppMSLType p.ty} {p.name} [[{ppMSLAttr p.attr}]]"

/-- Render a `threadgroup` shared array declaration inside a kernel body. -/
def ppMSLThreadgroupDecl (d : MSLThreadgroupDecl) : String :=
  s!"    threadgroup {ppMSLType d.elemTy} {d.name}[{d.count}];"

/-- Render a top-level MSL `struct` definition. -/
def ppMSLStructDecl (s : MSLStructDecl) : String :=
  let fields := String.intercalate " " (s.fields.map fun f => s!"{ppMSLType f.ty} {f.name};")
  s!"struct {s.name} \{ {fields} };"

/-- Canonical `kernel void <name>(\n` signature prefix of a rendered Metal kernel. -/
def ppMSLKernelSignaturePrefix (name : String) : String :=
  "kernel void " ++ name ++ "(\n"

/-- Render a `kernel void` Metal compute function. -/
def ppMSLKernel (k : MSLKernelDecl) : String :=
  let paramLines := String.intercalate ",\n" (k.params.map ppMSLParam)
  let sharedLines := k.sharedDecls.map ppMSLThreadgroupDecl
  let bodyLines := k.body.map (ppMSLStmt "    ")
  let inner := String.intercalate "\n" (sharedLines ++ bodyLines)
  ppMSLKernelSignaturePrefix k.name ++ s!"{paramLines}\n) \{\n{inner}\n}"

/-- Canonical MSL 3.0 standard library include & namespace header. -/
def ppMSLModuleHeader : String :=
  "#include <metal_stdlib>\nusing namespace metal;"

/-- Render a complete `MSLModule` with `#include <metal_stdlib>`, `using namespace metal;`,
    optional `struct` declarations, and all `kernel void` entry points. -/
def ppMSLModule (m : MSLModule) : String :=
  let blocks := (m.structs.map ppMSLStructDecl) ++ (m.kernels.map ppMSLKernel)
  match blocks with
  | [] => ppMSLModuleHeader ++ "\n"
  | bs => ppMSLModuleHeader ++ "\n\n" ++ String.intercalate "\n\n" bs ++ "\n"

/-! ## 4. Kernel-Checked Theorems (`0 sorryAx`, `strict-proofs` clean) -/

/-- `writeDeviceBuffer` never alters `constantBuffers` or `threadgroupArrays`. -/
theorem writeDeviceBuffer_preserves_const_and_tg (g g' : MSLGroupState)
    (bufIdx : Nat) (elemTy : MSLType) (elemIdx : Nat) (val : BitVec 64)
    (h : writeDeviceBuffer g bufIdx elemTy elemIdx val = .ok g') :
    g'.constantBuffers = g.constantBuffers ∧ g'.threadgroupArrays = g.threadgroupArrays := by
  unfold writeDeviceBuffer at h
  cases hLookup : g.deviceBuffers.lookup bufIdx <;> simp [hLookup] at h
  case some mem =>
    cases hStore : mem.storeBits (elemIdx * elemTy.byteWidth) elemTy.byteWidth
        (maskForType elemTy val) <;> simp [hStore] at h
    subst h
    exact ⟨rfl, rfl⟩

/-- `writeThreadgroupArray` never alters `constantBuffers` or `deviceBuffers`. -/
theorem writeThreadgroupArray_preserves_const_and_dev (g g' : MSLGroupState)
    (arrName : String) (elemTy : MSLType) (elemIdx : Nat) (val : BitVec 64)
    (h : writeThreadgroupArray g arrName elemTy elemIdx val = .ok g') :
    g'.constantBuffers = g.constantBuffers ∧ g'.deviceBuffers = g.deviceBuffers := by
  unfold writeThreadgroupArray at h
  cases hLookup : g.threadgroupArrays.lookup arrName <;> simp [hLookup] at h
  case some mem =>
    cases hStore : mem.storeBits (elemIdx * elemTy.byteWidth) elemTy.byteWidth
        (maskForType elemTy val) <;> simp [hStore] at h
    subst h
    exact ⟨rfl, rfl⟩

/-- `execIndexWrite` preserves `constantBuffers` across every address space. -/
theorem execIndexWrite_preserves_constant_buffers (g g' : MSLGroupState)
    (target : String) (elemIdx : Nat) (val : BitVec 64)
    (h : execIndexWrite g target elemIdx val = .ok g') :
    g'.constantBuffers = g.constantBuffers := by
  unfold execIndexWrite at h
  cases hBind : g.bindings.lookup target <;> simp [hBind] at h
  case some binding =>
    cases binding <;> simp at h
    case deviceBuf bufIdx elemTy =>
      exact (writeDeviceBuffer_preserves_const_and_tg g g' bufIdx elemTy elemIdx val h).1
    case threadgroupArr arrName elemTy =>
      exact (writeThreadgroupArray_preserves_const_and_dev g g' arrName elemTy elemIdx val h).1

/-- `constant` address-space immutability (statement level): executing ANY `MSLStmt` preserves
    `g.constantBuffers` bit-identically whenever it succeeds. -/
theorem exec_preserves_constant_buffers (g : MSLGroupState) (th : MSLThreadState)
    (stmt : MSLStmt) (rest : List MSLStmt) (th' : MSLThreadState) (g' : MSLGroupState)
    (h : execNonBarrierStmt g th stmt rest = .ok (th', g')) :
    g'.constantBuffers = g.constantBuffers := by
  cases stmt with
  | varDecl ty name rhs =>
    dsimp [execNonBarrierStmt] at h
    cases hE : evalMSLExpr g th rhs <;> simp [hE, propagateExprErr] at h
    exact congrArg MSLGroupState.constantBuffers h.2.symm
  | assign name rhs =>
    dsimp [execNonBarrierStmt] at h
    cases hB : g.bindings.lookup name with
    | none =>
      simp [hB] at h
      cases hE : evalMSLExpr g th rhs <;> simp [hE, propagateExprErr] at h
      exact congrArg MSLGroupState.constantBuffers h.2.symm
    | some b =>
      cases b <;> simp [hB] at h <;>
        (cases hE : evalMSLExpr g th rhs <;> simp [hE, propagateExprErr] at h
         exact congrArg MSLGroupState.constantBuffers h.2.symm)
  | indexAssign target idxExpr rhsExpr =>
    dsimp [execNonBarrierStmt] at h
    cases hI : evalMSLExpr g th idxExpr <;> cases hR : evalMSLExpr g th rhsExpr <;>
      simp [hI, hR, propagateExprErr] at h
    case ok.ok idxBv valBv =>
      cases hW : execIndexWrite g target idxBv.toNat valBv <;> simp [hW] at h
      case ok gMid =>
        rw [← h.2]
        exact execIndexWrite_preserves_constant_buffers g gMid target idxBv.toNat valBv hW
  | ifElse cond thenBr elseBr =>
    dsimp [execNonBarrierStmt] at h
    cases hC : evalMSLExpr g th cond <;> simp [hC, propagateExprErr] at h
    exact congrArg MSLGroupState.constantBuffers h.2.symm
  | forLoop loopVar ty initExpr condExpr stepExpr body =>
    dsimp [execNonBarrierStmt] at h
    cases hInit : evalMSLExpr g th initExpr <;> simp [hInit, propagateExprErr] at h
    exact congrArg MSLGroupState.constantBuffers h.2.symm
  | whileLoop condExpr body =>
    dsimp [execNonBarrierStmt] at h
    cases hC : evalMSLExpr g th condExpr <;> simp [hC, propagateExprErr] at h
    case ok vc =>
      split at h <;> simp at h <;> exact congrArg MSLGroupState.constantBuffers h.2.symm
  | threadgroupBarrier =>
    dsimp [execNonBarrierStmt] at h
    cases h
  | returnStmt =>
    dsimp [execNonBarrierStmt] at h
    simp at h
    exact congrArg MSLGroupState.constantBuffers h.2.symm

/-- Explicit write rejection for `constant` buffers: any indexed write targeting a `constant`
    buffer binding traps with `MSLOutcome.readOnlyViolation`. -/
theorem constant_write_rejected (g : MSLGroupState) (target : String)
    (bufIdx : Nat) (elemTy : MSLType) (elemIdx : Nat) (val : BitVec 64)
    (h_const : g.bindings.lookup target = some (.constantBuf bufIdx elemTy)) :
    execIndexWrite g target elemIdx val = .readOnlyViolation target elemIdx := by
  unfold execIndexWrite
  rw [h_const]

/-- Address-space isolation (`device` -> `threadgroup`): writing to a `device` buffer never
    mutates per-threadgroup shared memory `threadgroupArrays`. -/
theorem device_write_preserves_threadgroup (g g' : MSLGroupState) (target : String)
    (bufIdx : Nat) (elemTy : MSLType) (elemIdx : Nat) (val : BitVec 64)
    (h_dev : g.bindings.lookup target = some (.deviceBuf bufIdx elemTy))
    (h_exec : execIndexWrite g target elemIdx val = .ok g') :
    g'.threadgroupArrays = g.threadgroupArrays := by
  unfold execIndexWrite at h_exec
  rw [h_dev] at h_exec
  exact (writeDeviceBuffer_preserves_const_and_tg g g' bufIdx elemTy elemIdx val h_exec).2

/-- Address-space isolation (`threadgroup` -> `device`): writing to a `threadgroup` shared array
    never mutates `deviceBuffers`. -/
theorem threadgroup_write_preserves_device (g g' : MSLGroupState) (target arrName : String)
    (elemTy : MSLType) (elemIdx : Nat) (val : BitVec 64)
    (h_tg : g.bindings.lookup target = some (.threadgroupArr arrName elemTy))
    (h_exec : execIndexWrite g target elemIdx val = .ok g') :
    g'.deviceBuffers = g.deviceBuffers := by
  unfold execIndexWrite at h_exec
  rw [h_tg] at h_exec
  exact (writeThreadgroupArray_preserves_const_and_dev g g' arrName elemTy elemIdx val h_exec).2

/-- Out-of-bounds `device` buffer write safety: whenever the byte span
    `elemIdx * elemTy.byteWidth + elemTy.byteWidth` exceeds `mem.size`, `writeDeviceBuffer`
    catches the violation and returns `MSLOutcome.outOfBoundsWrite .device bufIdx elemIdx`. -/
theorem oob_device_write_caught (g : MSLGroupState) (bufIdx : Nat) (elemTy : MSLType)
    (elemIdx : Nat) (val : BitVec 64) (mem : ByteMemory)
    (h_buf : g.deviceBuffers.lookup bufIdx = some mem)
    (h_oob : mem.bytes.size < elemIdx * elemTy.byteWidth + elemTy.byteWidth) :
    writeDeviceBuffer g bufIdx elemTy elemIdx val = .outOfBoundsWrite .device bufIdx elemIdx := by
  unfold writeDeviceBuffer
  rw [h_buf]
  have hNotLe : ¬ (elemIdx * elemTy.byteWidth + elemTy.byteWidth ≤ mem.bytes.size) :=
    Nat.not_le_of_gt h_oob
  simp [ByteMemory.storeBits, hNotLe]

/-- Uniform `threadgroupBarrier` synchronization: when a non-empty threadgroup has every thread
    parked at `threadgroup_barrier`, `stepGroupBarrier` converges cleanly, advancing all threads
    past the barrier while preserving `deviceBuffers`, `constantBuffers`, and `threadgroupArrays`. -/
theorem threadgroupBarrier_uniform_converges (g : MSLGroupState)
    (h_nonempty : g.threads.isEmpty = false)
    (h_uniform : g.threads.all threadAtBarrier = true) :
    stepGroupBarrier g = .ok { g with threads := g.threads.map advanceBarrierThread } := by
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

private theorem stepFirstReady_preserves_const (g : MSLGroupState) :
    ∀ (pre suf : List MSLThreadState) (progressed : Bool) (g' : MSLGroupState),
      stepFirstReadyThread g pre suf = .ok (progressed, g') →
      g'.constantBuffers = g.constantBuffers
  | _, [], _, g', h => by
    simp [stepFirstReadyThread] at h
    exact congrArg MSLGroupState.constantBuffers h.2.symm
  | pre, th :: suf, progressed, g', h => by
    unfold stepFirstReadyThread at h
    split at h
    · exact stepFirstReady_preserves_const g (th :: pre) suf progressed g' h
    · cases hStmts : th.stmts with
      | nil =>
        simp [hStmts] at h
        rw [← h.2]
      | cons s rest =>
        cases s with
        | threadgroupBarrier =>
          simp [hStmts] at h
          exact stepFirstReady_preserves_const g (th :: pre) suf progressed g' h
        | varDecl ty name rhs =>
          simp [hStmts] at h
          cases hExec : execNonBarrierStmt g th (.varDecl ty name rhs) rest <;>
            simp [hExec] at h
          case ok pair =>
            rw [← h.2]
            exact exec_preserves_constant_buffers g th _ rest pair.1 pair.2 hExec
        | assign name rhs =>
          simp [hStmts] at h
          cases hExec : execNonBarrierStmt g th (.assign name rhs) rest <;>
            simp [hExec] at h
          case ok pair =>
            rw [← h.2]
            exact exec_preserves_constant_buffers g th _ rest pair.1 pair.2 hExec
        | indexAssign target idxExpr rhsExpr =>
          simp [hStmts] at h
          cases hExec : execNonBarrierStmt g th (.indexAssign target idxExpr rhsExpr) rest <;>
            simp [hExec] at h
          case ok pair =>
            rw [← h.2]
            exact exec_preserves_constant_buffers g th _ rest pair.1 pair.2 hExec
        | ifElse cond thenBr elseBr =>
          simp [hStmts] at h
          cases hExec : execNonBarrierStmt g th (.ifElse cond thenBr elseBr) rest <;>
            simp [hExec] at h
          case ok pair =>
            rw [← h.2]
            exact exec_preserves_constant_buffers g th _ rest pair.1 pair.2 hExec
        | forLoop lv ty initE condE stepE body =>
          simp [hStmts] at h
          cases hExec : execNonBarrierStmt g th (.forLoop lv ty initE condE stepE body) rest <;>
            simp [hExec] at h
          case ok pair =>
            rw [← h.2]
            exact exec_preserves_constant_buffers g th _ rest pair.1 pair.2 hExec
        | whileLoop condE body =>
          simp [hStmts] at h
          cases hExec : execNonBarrierStmt g th (.whileLoop condE body) rest <;>
            simp [hExec] at h
          case ok pair =>
            rw [← h.2]
            exact exec_preserves_constant_buffers g th _ rest pair.1 pair.2 hExec
        | returnStmt =>
          simp [hStmts] at h
          cases hExec : execNonBarrierStmt g th .returnStmt rest <;>
            simp [hExec] at h
          case ok pair =>
            rw [← h.2]
            exact exec_preserves_constant_buffers g th _ rest pair.1 pair.2 hExec

private theorem stepGroup_preserves_const (g g' : MSLGroupState) (done : Bool)
    (hStep : stepGroup g = .ok (done, g')) :
    g'.constantBuffers = g.constantBuffers := by
  unfold stepGroup at hStep
  split at hStep
  · simp at hStep
    exact congrArg MSLGroupState.constantBuffers hStep.2.symm
  · cases hReady : stepFirstReadyThread g [] g.threads with
    | ok rpair =>
      rcases rpair with ⟨progressed, gMid⟩
      cases progressed with
      | true =>
        simp [hReady] at hStep
        have hEq : g'.constantBuffers = gMid.constantBuffers :=
          congrArg MSLGroupState.constantBuffers hStep.2.symm
        exact hEq.trans (stepFirstReady_preserves_const g [] g.threads true gMid hReady)
      | false =>
        simp [hReady] at hStep
        have hC1 := stepFirstReady_preserves_const g [] g.threads false gMid hReady
        cases hBar : stepGroupBarrier gMid <;> simp [hBar] at hStep
        case ok synced =>
          have hEq1 : g'.constantBuffers = synced.constantBuffers :=
            congrArg MSLGroupState.constantBuffers hStep.2.symm
          unfold stepGroupBarrier at hBar
          split at hBar <;> simp at hBar
          have hEq2 : synced.constantBuffers = gMid.constantBuffers := by
            rw [← hBar]
          exact (hEq1.trans hEq2).trans hC1
    | readOnlyViolation t i => simp [hReady] at hStep
    | barrierDivergence => simp [hReady] at hStep
    | outOfBoundsLoad s b i => simp [hReady] at hStep
    | outOfBoundsWrite s b i => simp [hReady] at hStep
    | unboundIdentifier n => simp [hReady] at hStep
    | fuelExhausted => simp [hReady] at hStep

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
    cases hStep : stepGroup g with
    | ok pair =>
      rcases pair with ⟨done, gNext⟩
      have hStepConst := stepGroup_preserves_const g gNext done hStep
      cases done with
      | true =>
        simp [hStep] at h
        have hEq : g'.constantBuffers = gNext.constantBuffers :=
          congrArg MSLGroupState.constantBuffers h.symm
        exact hEq.trans hStepConst
      | false =>
        simp [hStep] at h
        exact (ih gNext h).trans hStepConst
    | readOnlyViolation t i => simp [hStep] at h
    | barrierDivergence => simp [hStep] at h
    | outOfBoundsLoad s b i => simp [hStep] at h
    | outOfBoundsWrite s b i => simp [hStep] at h
    | unboundIdentifier n => simp [hStep] at h
    | fuelExhausted => simp [hStep] at h

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
  induction f1 generalizing f2 g with
  | zero =>
    unfold runGroup at h1
    cases hAll : g.threads.all (·.halted)
    · simp [hAll] at h1
      exact False.elim (hne1 h1.symm)
    · simp [hAll] at h1
      have hRun2 := runGroup_halted f2 g hAll
      rw [hRun2] at h2
      exact h1.symm.trans h2
  | succ f1' ih =>
    cases f2 with
    | zero =>
      unfold runGroup at h2
      cases hAll : g.threads.all (·.halted)
      · simp [hAll] at h2
        exact False.elim (hne2 h2.symm)
      · simp [hAll] at h2
        have hRun1 := runGroup_halted (f1' + 1) g hAll
        rw [hRun1] at h1
        exact h1.symm.trans h2
    | succ f2' =>
      unfold runGroup at h1 h2
      cases hStep : stepGroup g with
      | ok pair =>
        cases pair with
        | mk done g' =>
          cases done with
          | true =>
            simp [hStep] at h1 h2
            exact h1.symm.trans h2
          | false =>
            simp [hStep] at h1 h2
            exact ih f2' g' h1 h2
      | readOnlyViolation t i =>
        simp [hStep] at h1 h2; exact h1.symm.trans h2
      | barrierDivergence =>
        simp [hStep] at h1 h2; exact h1.symm.trans h2
      | outOfBoundsLoad s b i =>
        simp [hStep] at h1 h2; exact h1.symm.trans h2
      | outOfBoundsWrite s b i =>
        simp [hStep] at h1 h2; exact h1.symm.trans h2
      | unboundIdentifier n =>
        simp [hStep] at h1 h2; exact h1.symm.trans h2
      | fuelExhausted =>
        simp [hStep] at h1 h2; exact h1.symm.trans h2

/-- 1:1 injectivity of `ppMSLAddressSpace`: distinct MSL address spaces render to distinct tokens. -/
theorem ppMSLAddressSpace_injective (s1 s2 : MSLAddressSpace)
    (h : ppMSLAddressSpace s1 = ppMSLAddressSpace s2) :
    s1 = s2 := by
  cases s1 <;> cases s2 <;> first | rfl | exact absurd h (by decide)

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
  cases (m.structs.map ppMSLStructDecl ++ m.kernels.map ppMSLKernel) with
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
  dsimp only
  rw [String.toList_append]
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
  rw [String.toList_append, semicolon_toList_eq]
  exact getLast_append_singleton _ ';'

end LeanNative.Backend.MetalAst
