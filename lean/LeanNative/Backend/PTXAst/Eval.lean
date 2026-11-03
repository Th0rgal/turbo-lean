import LeanNative.Backend.PTXAst.Syntax

/-!
# Genuine NVIDIA CUDA PTX 8.0 AST (`C2b`) — independent SIMT semantics and pretty-printer.
-/

namespace LeanNative.Backend.PTXAst

/-! ## 2. Independent SIMT Operational Semantics -/

/-- 3D grid or CTA (thread-block) dimensions / coordinates. -/
structure Dim3 where
  x : Nat := 1
  y : Nat := 1
  z : Nat := 1
  deriving Repr, DecidableEq, Inhabited, BEq

namespace Dim3

def totalThreads (d : Dim3) : Nat :=
  d.x * d.y * d.z

def coords (d : Dim3) : List Dim3 :=
  (List.range d.z).flatMap fun z =>
    (List.range d.y).flatMap fun y =>
      (List.range d.x).map fun x => { x, y, z }

def linearTid (blockDim tid : Dim3) : Nat :=
  (tid.z * blockDim.y + tid.y) * blockDim.x + tid.x

end Dim3

/-- Per-thread register values: `uninit` for declared-but-unwritten registers, `pred` (`Bool`) for
    `.pred`, and `scalar` (`BitVec 64`, masked per register width) for scalar integer & IEEE
    bit-pattern registers. -/
inductive PTXRegVal where
  | uninit : PTXRegVal
  | pred   : Bool → PTXRegVal
  | scalar : BitVec 64 → PTXRegVal
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Total association-list register file per thread, tracking declared register types when `enforceDecls`
    is enabled (`initCTAState` populates `decls` from `k.regDecls`). -/
structure PTXRegFile where
  regs         : List (String × PTXRegVal) := []
  decls        : List (String × PTXType) := []
  enforceDecls : Bool := false
  deriving Repr, DecidableEq, Inhabited, BEq

namespace PTXRegFile

def empty : PTXRegFile := { regs := [], decls := [], enforceDecls := false }

def setAssoc {α : Type} (xs : List (String × α)) (k : String) (v : α) :
    List (String × α) :=
  match xs with
  | [] => [(k, v)]
  | (k', v') :: rest =>
    if k' == k then (k, v) :: rest else (k', v') :: setAssoc rest k v

def expandSingleRegDecl (d : PTXRegDecl) : List (String × PTXType) :=
  if d.count == 0 then
    [(d.prefixName, d.ty)]
  else
    (List.range d.count).map fun idx => (s!"{d.prefixName}{idx}", d.ty)

/-- Populate a fresh register file from a kernel's `.reg` declarations (`%p0..%p{n-1}` or single-reg
    when `count == 0`), initializing every declared register to `.uninit` with `enforceDecls := true`. -/
def ofRegDecls (regDecls : List PTXRegDecl) : PTXRegFile :=
  let expanded := regDecls.flatMap expandSingleRegDecl
  let initRegs := expanded.foldl (fun acc (nm, _) => setAssoc acc nm .uninit) []
  let initDecls := expanded.foldl (fun acc (nm, ty) => setAssoc acc nm ty) []
  { regs := initRegs, decls := initDecls, enforceDecls := true }

def getScalar (rf : PTXRegFile) (name : String) : BitVec 64 :=
  match rf.regs.lookup name with
  | some (.scalar v) => v
  | some (.pred b)   => if b then 1#64 else 0#64
  | _                => 0#64

def getPred (rf : PTXRegFile) (name : String) : Option Bool :=
  match rf.regs.lookup name with
  | some (.pred b) => some b
  | _              => none

def setScalarRaw (rf : PTXRegFile) (name : String) (v : BitVec 64) : PTXRegFile :=
  { rf with regs := setAssoc rf.regs name (.scalar v) }

def setPredRaw (rf : PTXRegFile) (name : String) (b : Bool) : PTXRegFile :=
  { rf with regs := setAssoc rf.regs name (.pred b) }

end PTXRegFile

/-- Byte-addressed bounded memory buffer used independently for `globalMem`, per-CTA `sharedMem`,
    read-only `constMem`, and per-thread `localMem`. -/
structure ByteMemory where
  bytes : Array UInt8
  deriving Repr, DecidableEq, Inhabited, BEq

namespace ByteMemory

def zeros (numBytes : Nat) : ByteMemory :=
  { bytes := Array.replicate numBytes 0 }

def size (m : ByteMemory) : Nat :=
  m.bytes.size

def readLittleEndianAux (m : ByteMemory) (addr : Nat) : Nat → Option (BitVec 64)
  | 0 => some 0#64
  | k + 1 =>
    match m.bytes[addr + k]?, readLittleEndianAux m addr k with
    | some b, some rest =>
      let byteBv : BitVec 64 := BitVec.ofNat 64 b.toNat
      let shifted : BitVec 64 := byteBv <<< (k * 8)
      some (rest ||| shifted)
    | _, _ => none

/-- Bounds-checked little-endian load of `width` bytes (`1`, `2`, `4`, or `8`). -/
def loadBits (m : ByteMemory) (addr : Nat) (width : Nat) : Option (BitVec 64) :=
  if addr + width ≤ m.bytes.size then
    readLittleEndianAux m addr width
  else
    none

def writeLittleEndianAux (bs : Array UInt8) (addr : Nat) (val : BitVec 64) : Nat → Array UInt8
  | 0 => bs
  | k + 1 =>
    let byteVal : UInt8 := UInt8.ofNat ((val >>> (k * 8)).toNat % 256)
    let bs' := bs.setIfInBounds (addr + k) byteVal
    writeLittleEndianAux bs' addr val k

/-- Bounds-checked little-endian store of `width` bytes (`1`, `2`, `4`, or `8`). -/
def storeBits (m : ByteMemory) (addr : Nat) (width : Nat) (val : BitVec 64) : Option ByteMemory :=
  if addr + width ≤ m.bytes.size then
    some { bytes := writeLittleEndianAux m.bytes addr val width }
  else
    none

def fillU64Words (bs : Array UInt8) (idx : Nat) : List (BitVec 64) → Array UInt8
  | [] => bs
  | w :: rest => fillU64Words (writeLittleEndianAux bs (idx * 8) w 8) (idx + 1) rest

/-- Helper to initialize memory from an array of 64-bit little-endian words. -/
def ofU64Words (words : List (BitVec 64)) : ByteMemory :=
  let emptyBytes := Array.replicate (words.length * 8) (0 : UInt8)
  { bytes := fillU64Words emptyBytes 0 words }

/-- Read back a 64-bit word at element index `elemIdx` (byte offset `elemIdx * 8`). -/
def readU64Word? (m : ByteMemory) (elemIdx : Nat) : Option (BitVec 64) :=
  m.loadBits (elemIdx * 8) 8

end ByteMemory

/-- Read-only kernel `.param` state space mapping parameter names to 64-bit values. -/
structure ParamMemory where
  params : List (String × BitVec 64) := []
  deriving Repr, DecidableEq, Inhabited, BEq

namespace ParamMemory

def lookupParam? (pm : ParamMemory) (name : String) : Option (BitVec 64) :=
  pm.params.lookup name

end ParamMemory

/-- Per-CTA shared-memory symbol table mapping `.shared` symbol names to byte offsets in `sharedMem`. -/
structure SharedLayout where
  offsets   : List (String × Nat) := []
  totalSize : Nat := 0
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Compute deterministic byte offsets for a kernel's `.shared` declarations. -/
def buildSharedLayout (decls : List PTXSharedDecl) : SharedLayout :=
  decls.foldl (fun acc d =>
    let align := if d.align == 0 then 1 else d.align
    let alignedOff := ((acc.totalSize + align - 1) / align) * align
    let byteSpan := d.count * d.elemTy.byteWidth
    { offsets := acc.offsets ++ [(d.name, alignedOff)]
      totalSize := alignedOff + byteSpan }) {}

/-- Per-barrier-epoch memory access record for SIMT race detection (`W-W` and `R-W` conflicts, plus
    mixed atomic vs non-atomic conflicts). -/
structure MemAccessLog where
  tid      : Dim3
  space    : StateSpace
  addr     : Nat
  width    : Nat
  isWrite  : Bool
  isAtomic : Bool := false
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Check whether two half-open byte intervals `[a1, a1 + w1)` and `[a2, a2 + w2)` overlap. -/
def rangesOverlap (a1 w1 a2 w2 : Nat) : Bool :=
  decide (a1 < a2 + w2 ∧ a2 < a1 + w1)

/-- Check whether a memory access conflicts with any prior access in the current barrier epoch from a
    distinct thread (`tid' != tid`) on the same address space: two overlapping accesses race iff at
    least one is a write AND NOT both are atomic (`!(isAtomic && entry.isAtomic)`). -/
def findDataRace? (logs : List MemAccessLog) (tid : Dim3) (space : StateSpace)
    (addr width : Nat) (isWrite : Bool) (isAtomic : Bool := false) : Option Nat :=
  match logs with
  | [] => none
  | entry :: rest =>
    if entry.tid != tid && entry.space == space &&
       (isWrite || entry.isWrite) && !(isAtomic && entry.isAtomic) &&
       rangesOverlap addr width entry.addr entry.width then
      some (Nat.max addr entry.addr)
    else
      findDataRace? rest tid space addr width isWrite isAtomic

/-- Per-thread execution state inside a CTA, including per-thread `.local` private memory. -/
structure PTXThreadState where
  tid      : Dim3
  pc       : Nat := 0
  regs     : PTXRegFile := PTXRegFile.empty
  localMem : ByteMemory := ByteMemory.zeros 0
  halted   : Bool := false
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Complete CTA (Cooperative Thread Array) SIMT state with separated address spaces and
    barrier-epoch memory access tracking for race detection. -/
structure PTXCTAState where
  gridDim      : Dim3
  blockDim     : Dim3
  ctaId        : Dim3
  threads      : List PTXThreadState
  globalMem    : ByteMemory
  sharedMem    : ByteMemory
  constMem     : ByteMemory := ByteMemory.zeros 0
  paramMem     : ParamMemory
  sharedLayout : SharedLayout
  epochLog     : List MemAccessLog := []
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Explicit operational outcome of PTX SIMT execution, distinguishing normal completion from
    division by zero, signed overflow, misaligned loads/stores, SIMT data races, barrier
    divergence, out-of-bounds memory accesses, read-only `.const` writes, unsupported float ops,
    and fuel exhaustion. -/
inductive PTXOutcome (α : Type) where
  | ok                  : α → PTXOutcome α
  | divisionByZero      : PTXOutcome α
  | signedDivOverflow   : PTXOutcome α
  | misalignedAccess    : StateSpace → Nat → Nat → PTXOutcome α
  | readOnlyWrite       : StateSpace → Nat → PTXOutcome α
  | dataRace            : StateSpace → Nat → PTXOutcome α
  | unsupportedFloatOp  : String → PTXOutcome α
  | barrierDivergence   : Nat → PTXOutcome α
  | outOfBoundsLoad     : StateSpace → Nat → PTXOutcome α
  | outOfBoundsStore    : StateSpace → Nat → PTXOutcome α
  | unboundParam        : String → PTXOutcome α
  | unboundPred         : String → PTXOutcome α
  | unboundReg          : String → PTXOutcome α
  | typeMismatch        : String → PTXOutcome α
  | unboundLabel        : String → PTXOutcome α
  | invalidOperand      : String → PTXOutcome α
  | fuelExhausted       : PTXOutcome α
  deriving Repr, DecidableEq, Inhabited, BEq

namespace PTXOutcome

@[inline] def bind {α β : Type} (x : PTXOutcome α) (f : α → PTXOutcome β) : PTXOutcome β :=
  match x with
  | .ok v                 => f v
  | .divisionByZero       => .divisionByZero
  | .signedDivOverflow    => .signedDivOverflow
  | .misalignedAccess s a w => .misalignedAccess s a w
  | .readOnlyWrite s a    => .readOnlyWrite s a
  | .dataRace s a         => .dataRace s a
  | .unsupportedFloatOp m => .unsupportedFloatOp m
  | .barrierDivergence b  => .barrierDivergence b
  | .outOfBoundsLoad s a  => .outOfBoundsLoad s a
  | .outOfBoundsStore s a => .outOfBoundsStore s a
  | .unboundParam p       => .unboundParam p
  | .unboundPred p        => .unboundPred p
  | .unboundReg r         => .unboundReg r
  | .typeMismatch m       => .typeMismatch m
  | .unboundLabel l       => .unboundLabel l
  | .invalidOperand m     => .invalidOperand m
  | .fuelExhausted        => .fuelExhausted

end PTXOutcome

/-- Truncate/mask a 64-bit `BitVec` according to `PTXType` width (sign-extending signed 32-bit values
    only when explicitly converted, keeping low bits canonical per register width). -/
def maskForType (ty : PTXType) (v : BitVec 64) : BitVec 64 :=
  match ty with
  | .pred => if v != 0#64 then 1#64 else 0#64
  | .b8 => v &&& 0xFF#64
  | .b16 | .u16 => v &&& 0xFFFF#64
  | .b32 | .u32 | .s32 | .f32 => v &&& 0xFFFF_FFFF#64
  | .b64 | .u64 | .s64 | .f64 => v

/-- Sign-extend a 32-bit value stored in the lower 32 bits of `BitVec 64` to 64 bits. -/
def signExtend32To64 (v : BitVec 64) : BitVec 64 :=
  let v32 : BitVec 32 := v.truncate 32
  v32.signExtend 64

private def normSubF32 (m : Nat) (e : Nat) : Nat → Nat × Nat
  | 0 => (m, e)
  | k + 1 =>
    if (m &&& 0x80_0000) != 0 then (m &&& 0x7F_FFFF, e)
    else normSubF32 (m <<< 1) (e - 1) k

/-- Pure IEEE-754 binary32 -> binary64 widening on raw bit patterns (reduces definitionally in the Lean kernel). -/
def f32BitsToF64Bits (bits32 : UInt32) : UInt64 :=
  let b : Nat := bits32.toNat
  let sign : Nat := (b >>> 31) &&& 1
  let exp32 : Nat := (b >>> 23) &&& 0xFF
  let frac32 : Nat := b &&& 0x7F_FFFF
  if exp32 == 0xFF then
    if frac32 == 0 then
      UInt64.ofNat ((sign <<< 63) ||| (0x7FF <<< 52))
    else
      UInt64.ofNat ((sign <<< 63) ||| (0x7FF <<< 52) ||| (1 <<< 51) ||| (frac32 <<< 29))
  else if exp32 == 0 then
    if frac32 == 0 then
      UInt64.ofNat (sign <<< 63)
    else
      let (normFrac, exp64) := normSubF32 frac32 (1023 - 126) 24
      UInt64.ofNat ((sign <<< 63) ||| (exp64 <<< 52) ||| (normFrac <<< 29))
  else
    let exp64 : Nat := exp32 + (1023 - 127)
    UInt64.ofNat ((sign <<< 63) ||| (exp64 <<< 52) ||| (frac32 <<< 29))

/-- Pure IEEE-754 binary64 -> binary32 narrowing (`rn` or `rz`, reduces definitionally in the Lean kernel). -/
def f64BitsToF32Bits (rzMode : Bool) (bits64 : UInt64) : UInt32 :=
  let b : Nat := bits64.toNat
  let sign : Nat := (b >>> 63) &&& 1
  let exp64 : Nat := (b >>> 52) &&& 0x7FF
  let frac64 : Nat := b &&& 0xF_FFFF_FFFF_FFFF
  if exp64 == 0x7FF then
    if frac64 == 0 then
      UInt32.ofNat ((sign <<< 31) ||| (0xFF <<< 23))
    else
      UInt32.ofNat ((sign <<< 31) ||| (0xFF <<< 23) ||| 0x40_0000)
  else if exp64 == 0 && frac64 == 0 then
    UInt32.ofNat (sign <<< 31)
  else
    let unbiased : Int :=
      if exp64 == 0 then -1022 else Int.ofNat exp64 - 1023
    let sig53 : Nat :=
      if exp64 == 0 then frac64 else (1 <<< 52) ||| frac64
    if unbiased > 127 then
      if rzMode then
        UInt32.ofNat ((sign <<< 31) ||| (0xFE <<< 23) ||| 0x7F_FFFF)
      else
        UInt32.ofNat ((sign <<< 31) ||| (0xFF <<< 23))
    else if unbiased < -149 then
      UInt32.ofNat (sign <<< 31)
    else if unbiased < -126 then
      let shift : Nat := (-126 - unbiased).toNat + 29
      let q : Nat := sig53 >>> shift
      let remMask : Nat := (1 <<< shift) - 1
      let rem : Nat := sig53 &&& remMask
      let half : Nat := 1 <<< (shift - 1)
      let roundUp : Bool :=
        if rzMode then false
        else rem > half || (rem == half && (q &&& 1) == 1)
      let rounded : Nat := if roundUp then q + 1 else q
      if rounded >= 0x80_0000 then
        UInt32.ofNat ((sign <<< 31) ||| (1 <<< 23) ||| (rounded &&& 0x7F_FFFF))
      else
        UInt32.ofNat ((sign <<< 31) ||| rounded)
    else
      let exp32 : Nat := (unbiased + 127).toNat
      let q : Nat := sig53 >>> 29
      let rem : Nat := sig53 &&& ((1 <<< 29) - 1)
      let half : Nat := 1 <<< 28
      let roundUp : Bool :=
        if rzMode then false
        else rem > half || (rem == half && (q &&& 1) == 1)
      let rounded : Nat := if roundUp then q + 1 else q
      if rounded >= (1 <<< 24) then
        let exp32' := exp32 + 1
        if exp32' >= 0xFF then
          if rzMode then UInt32.ofNat ((sign <<< 31) ||| (0xFE <<< 23) ||| 0x7F_FFFF)
          else UInt32.ofNat ((sign <<< 31) ||| (0xFF <<< 23))
        else
          UInt32.ofNat ((sign <<< 31) ||| (exp32' <<< 23))
      else
        UInt32.ofNat ((sign <<< 31) ||| (exp32 <<< 23) ||| (rounded &&& 0x7F_FFFF))

private def bvToF32 (v : BitVec 64) : Float32 :=
  Float32.ofBits (UInt32.ofNat (v &&& 0xFFFF_FFFF#64).toNat)

private def f32ToBv (x : Float32) : BitVec 64 :=
  BitVec.ofNat 64 x.toBits.toNat

private def bvToF64 (v : BitVec 64) : Float :=
  Float.ofBits (UInt64.ofNat v.toNat)

private def f64ToBv (x : Float) : BitVec 64 :=
  x.toBits.toBitVec

/-- Evaluate `cvt` across integer and IEEE-754 floating-point types, failing closed on unsupported float modes. -/
def evalPTXCvt (rm : PTXRoundMode) (dstTy srcTy : PTXType) (v : BitVec 64) : PTXOutcome (BitVec 64) :=
  let rz := rm == .rz
  match dstTy, srcTy with
  | .f32, .f32 => .ok (maskForType .f32 v)
  | .f64, .f64 => .ok v
  | .f64, .f32 =>
    let b32 := UInt32.ofNat (v &&& 0xFFFF_FFFF#64).toNat
    .ok (f32BitsToF64Bits b32).toBitVec
  | .f32, .f64 =>
    let b32 := f64BitsToF32Bits rz (UInt64.ofNat v.toNat)
    .ok (BitVec.ofNat 64 b32.toNat)
  | .f32, .u32 | .f32, .b32 | .f32, .u64 | .f32, .b64 | .f32, .u16 | .f32, .b16
  | .f32, .s32 | .f32, .s64 | .f64, .u32 | .f64, .b32 | .f64, .u64 | .f64, .b64
  | .f64, .u16 | .f64, .b16 | .f64, .s32 | .f64, .s64 =>
    if rm == .rz then
      .unsupportedFloatOp "cvt.rz int-to-float"
    else
      match dstTy, srcTy with
      | .f32, .u32 | .f32, .b32 =>
        let u := UInt32.ofNat (v &&& 0xFFFF_FFFF#64).toNat
        .ok (f32ToBv u.toFloat32)
      | .f32, .u64 | .f32, .b64 =>
        let u := UInt64.ofNat v.toNat
        .ok (f32ToBv u.toFloat32)
      | .f32, .u16 | .f32, .b16 =>
        let u := UInt32.ofNat (v &&& 0xFFFF#64).toNat
        .ok (f32ToBv u.toFloat32)
      | .f32, .s32 =>
        let i := Int32.ofBitVec (v.truncate 32)
        .ok (f32ToBv i.toFloat32)
      | .f32, .s64 =>
        let i := Int64.ofBitVec v
        .ok (f32ToBv i.toFloat32)
      | .f64, .u32 | .f64, .b32 =>
        let u := UInt32.ofNat (v &&& 0xFFFF_FFFF#64).toNat
        .ok (f64ToBv u.toFloat)
      | .f64, .u64 | .f64, .b64 =>
        let u := UInt64.ofNat v.toNat
        .ok (f64ToBv u.toFloat)
      | .f64, .u16 | .f64, .b16 =>
        let u := UInt32.ofNat (v &&& 0xFFFF#64).toNat
        .ok (f64ToBv u.toFloat)
      | .f64, .s32 =>
        let i := Int32.ofBitVec (v.truncate 32)
        .ok (f64ToBv i.toFloat)
      | .f64, .s64 =>
        let i := Int64.ofBitVec v
        .ok (f64ToBv i.toFloat)
      | _, _ => .unsupportedFloatOp "unsupported float conversion"
  | .u32, .f32 | .b32, .f32 | .u64, .f32 | .b64, .f32 | .s32, .f32 | .s64, .f32
  | .u32, .f64 | .b32, .f64 | .u64, .f64 | .b64, .f64 | .s32, .f64 | .s64, .f64 =>
    if rm == .rn then
      .unsupportedFloatOp "cvt.rn float-to-int"
    else
      match dstTy, srcTy with
      | .u32, .f32 | .b32, .f32 =>
        .ok (BitVec.ofNat 64 (bvToF32 v).toUInt32.toNat)
      | .u64, .f32 | .b64, .f32 =>
        .ok (bvToF32 v).toUInt64.toBitVec
      | .s32, .f32 =>
        .ok ((bvToF32 v).toInt32.toBitVec.zeroExtend 64)
      | .s64, .f32 =>
        .ok (bvToF32 v).toInt64.toBitVec
      | .u32, .f64 | .b32, .f64 =>
        .ok (BitVec.ofNat 64 (bvToF64 v).toUInt32.toNat)
      | .u64, .f64 | .b64, .f64 =>
        .ok (bvToF64 v).toUInt64.toBitVec
      | .s32, .f64 =>
        .ok ((bvToF64 v).toInt32.toBitVec.zeroExtend 64)
      | .s64, .f64 =>
        .ok (bvToF64 v).toInt64.toBitVec
      | _, _ => .unsupportedFloatOp "unsupported float conversion"
  | _, .f32 | _, .f64 | .f32, _ | .f64, _ =>
    .unsupportedFloatOp "unsupported float conversion"
  | _, _ =>
    let ext :=
      if srcTy == .s32 && (dstTy == .s64 || dstTy == .u64 || dstTy == .b64) then
        signExtend32To64 v
      else
        maskForType srcTy v
    .ok (maskForType dstTy ext)

/-- Evaluate a special hardware coordinate register for `(gridDim, blockDim, ctaId, tid)`. -/
def evalSpecialReg (gridDim blockDim ctaId tid : Dim3) : SpecialReg → BitVec 64
  | .tidX    => BitVec.ofNat 64 tid.x
  | .tidY    => BitVec.ofNat 64 tid.y
  | .tidZ    => BitVec.ofNat 64 tid.z
  | .ntidX   => BitVec.ofNat 64 blockDim.x
  | .ntidY   => BitVec.ofNat 64 blockDim.y
  | .ntidZ   => BitVec.ofNat 64 blockDim.z
  | .ctaidX  => BitVec.ofNat 64 ctaId.x
  | .ctaidY  => BitVec.ofNat 64 ctaId.y
  | .ctaidZ  => BitVec.ofNat 64 ctaId.z
  | .nctaidX => BitVec.ofNat 64 gridDim.x
  | .nctaidY => BitVec.ofNat 64 gridDim.y
  | .nctaidZ => BitVec.ofNat 64 gridDim.z

/-- Validated scalar register read: traps with `.unboundReg` if undeclared (when `enforceDecls`) or
    uninitialized, and `.typeMismatch` if `name` is a `.pred` register or mismatches `expectedWidth?`
    (widening sub-word `.b8`/`.b16`/`.u16` registers when declared as <= 32-bit in 32-bit ops is disallowed,
    exact declared register width must match `expectedWidth?`). -/
def PTXRegFile.readScalarChecked (rf : PTXRegFile) (name : String)
    (expectedWidth? : Option Nat := none) : PTXOutcome (BitVec 64) :=
  if rf.enforceDecls then
    match rf.decls.lookup name with
    | none => .unboundReg name
    | some declTy =>
      if declTy == .pred then
        .typeMismatch s!"predicate register {name} used as scalar operand"
      else
        let regWidth := if declTy.bitWidth < 32 then 32 else declTy.bitWidth
        let expWidth := match expectedWidth? with
          | none => regWidth
          | some w => if w < 32 then 32 else w
        if regWidth != expWidth then
          .typeMismatch s!"register {name} width {declTy.bitWidth} mismatches instruction width"
        else
          match rf.regs.lookup name with
          | some (.scalar v) => .ok v
          | some (.pred _) => .typeMismatch s!"predicate register {name} used as scalar operand"
          | _ => .unboundReg name
  else
    match rf.regs.lookup name with
    | some (.scalar v) => .ok v
    | some (.pred _) => .typeMismatch s!"predicate register {name} used as scalar operand"
    | some .uninit => .unboundReg name
    | none => .ok 0#64

/-- Validated predicate register read: traps with `.unboundPred` if uninitialized/absent (or `.unboundReg`
    if undeclared when `enforceDecls`) and `.typeMismatch` if `name` is a scalar register. -/
def PTXRegFile.readPredChecked (rf : PTXRegFile) (name : String) : PTXOutcome Bool :=
  if rf.enforceDecls then
    match rf.decls.lookup name with
    | none => .unboundReg name
    | some declTy =>
      if declTy != .pred then
        .typeMismatch s!"scalar register {name} used as predicate"
      else
        match rf.regs.lookup name with
        | some (.pred b) => .ok b
        | some (.scalar _) => .typeMismatch s!"scalar register {name} used as predicate"
        | _ => .unboundPred name
  else
    match rf.regs.lookup name with
    | some (.pred b) => .ok b
    | some (.scalar _) => .typeMismatch s!"scalar register {name} used as predicate"
    | _ => .unboundPred name

/-- Validated scalar register write: enforces declared register existence and bit-width match when
    `enforceDecls = true` (sub-32-bit `.b8`/`.b16`/`.u16` memory loads/ops may target their exact width
    or a 32-bit general register per PTX 8.0), masking `v` to the declared register width. -/
def PTXRegFile.setScalar (rf : PTXRegFile) (name : String) (v : BitVec 64)
    (instrWidth? : Option Nat := none) : PTXOutcome PTXRegFile :=
  if rf.enforceDecls then
    match rf.decls.lookup name with
    | none => .unboundReg name
    | some declTy =>
      if declTy == .pred then
        .typeMismatch s!"cannot write scalar value to predicate register {name}"
      else
        let regWidth := if declTy.bitWidth < 32 then 32 else declTy.bitWidth
        let okWidth := match instrWidth? with
          | none => true
          | some w =>
            let normW := if w < 32 then 32 else w
            declTy.bitWidth == w || regWidth == normW
        if !okWidth then
          .typeMismatch s!"destination register {name} width {declTy.bitWidth} mismatches instruction width"
        else
          let masked :=
            if declTy.bitWidth == 64 then v
            else if (v >>> 32) != 0#64 then v
            else maskForType declTy v
          if declTy.bitWidth < 64 && (masked >>> 32) != 0#64 then
            .typeMismatch s!"scalar value written to {name} is not canonical for a 32-bit register"
          else
            .ok (rf.setScalarRaw name masked)
  else
    .ok (rf.setScalarRaw name v)

/-- Validated predicate register write: enforces that `name` is declared as `.pred` when `enforceDecls = true`. -/
def PTXRegFile.setPred (rf : PTXRegFile) (name : String) (b : Bool) : PTXOutcome PTXRegFile :=
  if rf.enforceDecls then
    match rf.decls.lookup name with
    | none => .unboundReg name
    | some declTy =>
      if declTy != .pred then
        .typeMismatch s!"cannot write predicate value to non-pred register {name}"
      else
        .ok (rf.setPredRaw name b)
  else
    .ok (rf.setPredRaw name b)

/-- Render a `PTXType` suffix (`.pred`, `.u64`, `.b32`, ...). -/
def ppPTXType : PTXType → String
  | .pred => ".pred"
  | .b8   => ".b8"
  | .b16  => ".b16"
  | .b32  => ".b32"
  | .b64  => ".b64"
  | .u16  => ".u16"
  | .u32  => ".u32"
  | .u64  => ".u64"
  | .s32  => ".s32"
  | .s64  => ".s64"
  | .f32  => ".f32"
  | .f64  => ".f64"

/-- Evaluate a `PTXOperand` to a `BitVec 64` in the context of a thread and CTA. -/
def evalOperand (cta : PTXCTAState) (th : PTXThreadState) (op : PTXOperand)
    (expectedWidth? : Option Nat := none) : PTXOutcome (BitVec 64) :=
  match op with
  | .reg name => th.regs.readScalarChecked name expectedWidth?
  | .sreg sr => .ok (evalSpecialReg cta.gridDim cta.blockDim cta.ctaId th.tid sr)
  | .immU64 v => .ok v
  | .immS64 i =>
    if i ≥ 0 then
      .ok (BitVec.ofNat 64 i.toNat)
    else
      .ok (0#64 - BitVec.ofNat 64 (-i).toNat)
  | .immF32 bits => .ok (BitVec.ofNat 64 bits.toNat)
  | .immF64 bits => .ok bits.toBitVec
  | .sym name =>
    match cta.sharedLayout.offsets.lookup name with
    | some off => .ok (BitVec.ofNat 64 off)
    | none => .invalidOperand s!"unknown shared symbol {name}"

/-- Validate that a shift-amount operand fits `.u32`/`.b32` width (`upper 32 bits == 0` and non-negative immediate). -/
def evalShiftAmount (cta : PTXCTAState) (th : PTXThreadState) (sh : PTXOperand) :
    PTXOutcome Nat :=
  match sh with
  | .immS64 i =>
    if i < 0 || i >= 4294967296 then
      .invalidOperand s!"shift amount immediate out of u32 range: {i}"
    else
      .ok i.toNat
  | .immF32 _ | .immF64 _ =>
    .invalidOperand "floating-point immediate used as shift amount"
  | _ =>
    PTXOutcome.bind (evalOperand cta th sh (some 32)) fun vsh =>
      if (vsh >>> 32) != 0#64 then
        .invalidOperand "shift amount exceeds 32-bit .u32/.b32 operand width"
      else
        .ok (vsh &&& 0xFFFF_FFFF#64).toNat

/-- Resolve a byte address for addressable state spaces (`global`, `shared`, `const`, `local`). -/
def evalAddr (cta : PTXCTAState) (th : PTXThreadState) (addr : PTXAddr) : PTXOutcome Nat :=
  match addr with
  | .paramSym sym => .invalidOperand s!"param symbol [{sym}] used as addressable pointer"
  | .regOffset regName disp =>
    PTXOutcome.bind (th.regs.readScalarChecked regName (some 64)) fun baseBv =>
      let base : Int := Int.ofNat baseBv.toNat
      let effective := base + disp
      if effective < 0 then
        .invalidOperand s!"negative effective address {effective}"
      else
        .ok effective.toNat
  | .symOffset sym disp =>
    match cta.sharedLayout.offsets.lookup sym with
    | some baseOff =>
      let effective : Int := Int.ofNat baseOff + disp
      if effective < 0 then
        .invalidOperand s!"negative shared symbol address {effective}"
      else
        .ok effective.toNat
    | none => .invalidOperand s!"unknown shared symbol {sym}"

/-- Evaluate a `setp` comparison directly over `BitVec` and IEEE-754 `Float32`/`Float`.
    For IEEE-754 `.f32` and `.f64`, ordered comparisons (`.eq`, `.lt`, `.le`, `.gt`, `.ge`) return
    `false` when either operand is NaN, while `.ne` returns `a != b` (which is `true` if either is NaN,
    matching PTX `setp.ne.f32`/`setp.neu.f32` unordered-inequality semantics for `!=`). -/
def evalPTXCmp (cmp : PTXCmpOp) (ty : PTXType) (a b : BitVec 64) : Bool :=
  match ty with
  | .f32 =>
    let fa := bvToF32 a
    let fb := bvToF32 b
    match cmp with
    | .eq => fa == fb
    | .ne => fa != fb
    | .lt | .lo => decide (fa < fb)
    | .le | .ls => decide (fa ≤ fb)
    | .gt | .hi => decide (fb < fa)
    | .ge | .hs => decide (fb ≤ fa)
  | .f64 =>
    let fa := bvToF64 a
    let fb := bvToF64 b
    match cmp with
    | .eq => fa == fb
    | .ne => fa != fb
    | .lt | .lo => decide (fa < fb)
    | .le | .ls => decide (fa ≤ fb)
    | .gt | .hi => decide (fb < fa)
    | .ge | .hs => decide (fb ≤ fa)
  | .b32 | .u32 =>
    let a32 : BitVec 32 := a.truncate 32
    let b32 : BitVec 32 := b.truncate 32
    match cmp with
    | .eq => a32 == b32
    | .ne => a32 != b32
    | .lt | .lo => BitVec.ult a32 b32
    | .le | .ls => BitVec.ule a32 b32
    | .gt | .hi => BitVec.ult b32 a32
    | .ge | .hs => BitVec.ule b32 a32
  | .s32 =>
    let a32 : BitVec 32 := a.truncate 32
    let b32 : BitVec 32 := b.truncate 32
    match cmp with
    | .eq => a32 == b32
    | .ne => a32 != b32
    | .lt => BitVec.slt a32 b32
    | .le => BitVec.sle a32 b32
    | .gt => BitVec.slt b32 a32
    | .ge => BitVec.sle b32 a32
    | .lo => BitVec.ult a32 b32
    | .ls => BitVec.ule a32 b32
    | .hi => BitVec.ult b32 a32
    | .hs => BitVec.ule b32 a32
  | .s64 =>
    match cmp with
    | .eq => a == b
    | .ne => a != b
    | .lt => BitVec.slt a b
    | .le => BitVec.sle a b
    | .gt => BitVec.slt b a
    | .ge => BitVec.sle b a
    | .lo => BitVec.ult a b
    | .ls => BitVec.ule a b
    | .hi => BitVec.ult b a
    | .hs => BitVec.ule b a
  | _ =>
    let am := maskForType ty a
    let bm := maskForType ty b
    match cmp with
    | .eq => am == bm
    | .ne => am != bm
    | .lt | .lo => BitVec.ult am bm
    | .le | .ls => BitVec.ule am bm
    | .gt | .hi => BitVec.ult bm am
    | .ge | .hs => BitVec.ule bm am

/-- Find the statement index immediately following `.label lbl` in `stmts`. -/
def findLabelPC? (stmts : List PTXStmt) (lbl : String) : Option Nat :=
  match stmts with
  | [] => none
  | .label l :: rest => if l == lbl then some 1 else (findLabelPC? rest lbl).map (· + 1)
  | _ :: rest => (findLabelPC? rest lbl).map (· + 1)

/-- Evaluate an optional predicate guard (`@p` / `@!p`) in thread `th`. -/
def evalPredGuard (th : PTXThreadState) : Option PTXPredGuard → PTXOutcome Bool
  | none => .ok true
  | some g =>
    PTXOutcome.bind (th.regs.readPredChecked g.predReg) fun b =>
      .ok (if g.negated then !b else b)

/-- Check natural byte alignment (`byteAddr % width == 0`). -/
def checkAligned (sp : StateSpace) (byteAddr width : Nat) : PTXOutcome Unit :=
  if byteAddr % width == 0 then
    .ok ()
  else
    .misalignedAccess sp byteAddr width

/-- Check cross-thread SIMT race freedom for a `global`/`shared` access in the current epoch,
    returning the updated epoch log on success or `.dataRace sp conflictAddr` on conflict.
    Atomic accesses set `isAtomic := true` and only race with non-atomic overlapping accesses. -/
def recordEpochAccess (logs : List MemAccessLog) (tid : Dim3) (sp : StateSpace)
    (byteAddr width : Nat) (isWrite : Bool) (isAtomic : Bool := false) :
    PTXOutcome (List MemAccessLog) :=
  match findDataRace? logs tid sp byteAddr width isWrite isAtomic with
  | some conflictAddr => .dataRace sp conflictAddr
  | none =>
    .ok ({ tid := tid, space := sp, addr := byteAddr, width := width, isWrite := isWrite,
           isAtomic := isAtomic } :: logs)

/-- Evaluate a predicate-typed operand (`and.pred`/`or.pred`/`xor.pred`/`not.pred`/`mov.pred`). -/
def evalPredOperand (cta : PTXCTAState) (th : PTXThreadState) (op : PTXOperand) : PTXOutcome Bool :=
  match op with
  | .reg name => th.regs.readPredChecked name
  | _ => PTXOutcome.bind (evalOperand cta th op none) fun v => .ok (v != 0#64)

/-- Execute a single non-barrier, non-warp-collective `PTXInstr` for one active thread `th` against
    `(cta, stmts)`, returning `(PTXThreadState, ByteMemory (global), ByteMemory (shared), List MemAccessLog)`. -/
def execNonBarrierInstr (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    (ins : PTXInstr) : PTXOutcome (PTXThreadState × ByteMemory × ByteMemory × List MemAccessLog) :=
  let nextPc := th.pc + 1
  match ins with
  | .mov ty dst src =>
    if ty == .pred then
      PTXOutcome.bind (evalPredOperand cta th src) fun b =>
        PTXOutcome.bind (th.regs.setPred dst b) fun rf' =>
          .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
    else
      PTXOutcome.bind (evalOperand cta th src (some ty.bitWidth)) fun v =>
        PTXOutcome.bind (th.regs.setScalar dst (maskForType ty v) (some ty.bitWidth)) fun rf' =>
          .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
  | .movPack2x32 dst loOp hiOp =>
    PTXOutcome.bind (evalOperand cta th loOp (some 32)) fun vLo =>
      PTXOutcome.bind (evalOperand cta th hiOp (some 32)) fun vHi =>
        let lo := vLo &&& 0xFFFF_FFFF#64
        let hi := (vHi &&& 0xFFFF_FFFF#64) <<< 32
        PTXOutcome.bind (th.regs.setScalar dst (lo ||| hi) (some 64)) fun rf' =>
          .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
  | .movUnpack2x32 dstLo dstHi srcOp =>
    PTXOutcome.bind (evalOperand cta th srcOp (some 64)) fun v =>
      let lo := v &&& 0xFFFF_FFFF#64
      let hi := (v >>> 32) &&& 0xFFFF_FFFF#64
      PTXOutcome.bind (th.regs.setScalar dstLo lo (some 32)) fun rf1 =>
        PTXOutcome.bind (rf1.setScalar dstHi hi (some 32)) fun rf2 =>
          .ok ({ th with pc := nextPc, regs := rf2 }, cta.globalMem, cta.sharedMem, cta.epochLog)
  | .clz ty dst srcOp =>
    if ty != .b32 && ty != .u32 && ty != .b64 && ty != .u64 then
      .invalidOperand "clz requires .b32/.u32/.b64/.u64 operand type"
    else
      PTXOutcome.bind (evalOperand cta th srcOp (some ty.bitWidth)) fun v =>
        let cnt : BitVec 64 :=
          if ty == .b32 || ty == .u32 then
            let c32 := BitVec.clz (v.truncate 32)
            c32.zeroExtend 64
          else
            BitVec.clz v
        PTXOutcome.bind (th.regs.setScalar dst (cnt &&& 0xFFFF_FFFF#64) (some 32)) fun rf' =>
          .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
  | .ldParam ty dst paramName =>
    match cta.paramMem.lookupParam? paramName with
    | some v =>
      let val := maskForType ty v
      PTXOutcome.bind (th.regs.setScalar dst val (some ty.bitWidth)) fun rf' =>
        .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
    | none => .unboundParam paramName
  | .ldGlobal ty dst addr =>
    PTXOutcome.bind (evalAddr cta th addr) fun byteAddr =>
      let w := ty.byteWidth
      PTXOutcome.bind (checkAligned .global byteAddr w) fun () =>
        PTXOutcome.bind (recordEpochAccess cta.epochLog th.tid .global byteAddr w false false) fun log' =>
          match cta.globalMem.loadBits byteAddr w with
          | some raw =>
            let v := maskForType ty raw
            PTXOutcome.bind (th.regs.setScalar dst v (some ty.bitWidth)) fun rf' =>
              .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, log')
          | none => .outOfBoundsLoad .global byteAddr
  | .ldShared ty dst addr =>
    PTXOutcome.bind (evalAddr cta th addr) fun byteAddr =>
      let w := ty.byteWidth
      PTXOutcome.bind (checkAligned .shared byteAddr w) fun () =>
        PTXOutcome.bind (recordEpochAccess cta.epochLog th.tid .shared byteAddr w false false) fun log' =>
          match cta.sharedMem.loadBits byteAddr w with
          | some raw =>
            let v := maskForType ty raw
            PTXOutcome.bind (th.regs.setScalar dst v (some ty.bitWidth)) fun rf' =>
              .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, log')
          | none => .outOfBoundsLoad .shared byteAddr
  | .ldConst ty dst addr =>
    PTXOutcome.bind (evalAddr cta th addr) fun byteAddr =>
      let w := ty.byteWidth
      PTXOutcome.bind (checkAligned .const byteAddr w) fun () =>
        match cta.constMem.loadBits byteAddr w with
        | some raw =>
          let v := maskForType ty raw
          PTXOutcome.bind (th.regs.setScalar dst v (some ty.bitWidth)) fun rf' =>
            .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
        | none => .outOfBoundsLoad .const byteAddr
  | .ldLocal ty dst addr =>
    PTXOutcome.bind (evalAddr cta th addr) fun byteAddr =>
      let w := ty.byteWidth
      PTXOutcome.bind (checkAligned .local byteAddr w) fun () =>
        match th.localMem.loadBits byteAddr w with
        | some raw =>
          let v := maskForType ty raw
          PTXOutcome.bind (th.regs.setScalar dst v (some ty.bitWidth)) fun rf' =>
            .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
        | none => .outOfBoundsLoad .local byteAddr
  | .stGlobal ty addr src =>
    PTXOutcome.bind (evalAddr cta th addr) fun byteAddr =>
      PTXOutcome.bind (evalOperand cta th src (some ty.bitWidth)) fun v =>
        let w := ty.byteWidth
        PTXOutcome.bind (checkAligned .global byteAddr w) fun () =>
          PTXOutcome.bind (recordEpochAccess cta.epochLog th.tid .global byteAddr w true false) fun log' =>
            match cta.globalMem.storeBits byteAddr w (maskForType ty v) with
            | some g' => .ok ({ th with pc := nextPc }, g', cta.sharedMem, log')
            | none => .outOfBoundsStore .global byteAddr
  | .stShared ty addr src =>
    PTXOutcome.bind (evalAddr cta th addr) fun byteAddr =>
      PTXOutcome.bind (evalOperand cta th src (some ty.bitWidth)) fun v =>
        let w := ty.byteWidth
        PTXOutcome.bind (checkAligned .shared byteAddr w) fun () =>
          PTXOutcome.bind (recordEpochAccess cta.epochLog th.tid .shared byteAddr w true false) fun log' =>
            match cta.sharedMem.storeBits byteAddr w (maskForType ty v) with
            | some s' => .ok ({ th with pc := nextPc }, cta.globalMem, s', log')
            | none => .outOfBoundsStore .shared byteAddr
  | .stLocal ty addr src =>
    PTXOutcome.bind (evalAddr cta th addr) fun byteAddr =>
      PTXOutcome.bind (evalOperand cta th src (some ty.bitWidth)) fun v =>
        let w := ty.byteWidth
        PTXOutcome.bind (checkAligned .local byteAddr w) fun () =>
          match th.localMem.storeBits byteAddr w (maskForType ty v) with
          | some l' => .ok ({ th with pc := nextPc, localMem := l' }, cta.globalMem, cta.sharedMem, cta.epochLog)
          | none => .outOfBoundsStore .local byteAddr
  | .stConst _ addr _ =>
    PTXOutcome.bind (evalAddr cta th addr) fun byteAddr =>
      .readOnlyWrite .const byteAddr
  | .atomAdd sp ty dst addr src =>
    if sp != .global && sp != .shared then
      .invalidOperand "atom.add requires .global or .shared state space"
    else
      PTXOutcome.bind (evalAddr cta th addr) fun byteAddr =>
        PTXOutcome.bind (evalOperand cta th src (some ty.bitWidth)) fun v =>
          let w := ty.byteWidth
          PTXOutcome.bind (checkAligned sp byteAddr w) fun () =>
            PTXOutcome.bind (recordEpochAccess cta.epochLog th.tid sp byteAddr w true true) fun log' =>
              let mem := if sp == .global then cta.globalMem else cta.sharedMem
              match mem.loadBits byteAddr w with
              | none => .outOfBoundsStore sp byteAddr
              | some oldRaw =>
                let oldVal := maskForType ty oldRaw
                let addResOutcome : PTXOutcome (BitVec 64) :=
                  match ty with
                  | .f32 => .ok (f32ToBv (bvToF32 oldRaw + bvToF32 v))
                  | .f64 => .ok (f64ToBv (bvToF64 oldRaw + bvToF64 v))
                  | .u32 | .b32 | .s32 | .u64 | .b64 | .s64 =>
                    .ok (maskForType ty (maskForType ty oldRaw + maskForType ty v))
                  | _ => .invalidOperand "atom.add unsupported data type"
                PTXOutcome.bind addResOutcome fun newVal =>
                  match mem.storeBits byteAddr w newVal with
                  | none => .outOfBoundsStore sp byteAddr
                  | some mem' =>
                    PTXOutcome.bind (th.regs.setScalar dst oldVal (some ty.bitWidth)) fun rf' =>
                      let th' := { th with pc := nextPc, regs := rf' }
                      if sp == .global then
                        .ok (th', mem', cta.sharedMem, log')
                      else
                        .ok (th', cta.globalMem, mem', log')
  | .atomCas sp ty dst addr cmpOp srcOp =>
    if sp != .global && sp != .shared then
      .invalidOperand "atom.cas requires .global or .shared state space"
    else if ty != .b32 && ty != .u32 && ty != .b64 && ty != .u64 then
      .typeMismatch "atom.cas requires .b32/.u32/.b64/.u64 type"
    else
      PTXOutcome.bind (evalAddr cta th addr) fun byteAddr =>
        PTXOutcome.bind (evalOperand cta th cmpOp (some ty.bitWidth)) fun vCmp =>
          PTXOutcome.bind (evalOperand cta th srcOp (some ty.bitWidth)) fun vSrc =>
            let w := ty.byteWidth
            PTXOutcome.bind (checkAligned sp byteAddr w) fun () =>
              PTXOutcome.bind (recordEpochAccess cta.epochLog th.tid sp byteAddr w true true) fun log' =>
                let mem := if sp == .global then cta.globalMem else cta.sharedMem
                match mem.loadBits byteAddr w with
                | none => .outOfBoundsStore sp byteAddr
                | some oldRaw =>
                  let oldVal := maskForType ty oldRaw
                  let cmpMasked := maskForType ty vCmp
                  let nextStoreVal := if oldVal == cmpMasked then maskForType ty vSrc else oldVal
                  match mem.storeBits byteAddr w nextStoreVal with
                  | none => .outOfBoundsStore sp byteAddr
                  | some mem' =>
                    PTXOutcome.bind (th.regs.setScalar dst oldVal (some ty.bitWidth)) fun rf' =>
                      let th' := { th with pc := nextPc, regs := rf' }
                      if sp == .global then
                        .ok (th', mem', cta.sharedMem, log')
                      else
                        .ok (th', cta.globalMem, mem', log')
  | .cvtaToGlobal ty dst src =>
    PTXOutcome.bind (evalOperand cta th src (some ty.bitWidth)) fun v =>
      PTXOutcome.bind (th.regs.setScalar dst (maskForType ty v) (some ty.bitWidth)) fun rf' =>
        .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
  | .cvt rm dstTy srcTy dst src =>
    PTXOutcome.bind (evalOperand cta th src (some srcTy.bitWidth)) fun v =>
      PTXOutcome.bind (evalPTXCvt rm dstTy srcTy v) fun out =>
        PTXOutcome.bind (th.regs.setScalar dst out (some dstTy.bitWidth)) fun rf' =>
          .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
  | .add rm ty dst a b =>
    PTXOutcome.bind (evalOperand cta th a (some ty.bitWidth)) fun va =>
      PTXOutcome.bind (evalOperand cta th b (some ty.bitWidth)) fun vb =>
        if ty == .f32 then
          if rm == .rz then .unsupportedFloatOp "add.rz.f32"
          else
            let res := f32ToBv (bvToF32 va + bvToF32 vb)
            PTXOutcome.bind (th.regs.setScalar dst res (some ty.bitWidth)) fun rf' =>
              .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
        else if ty == .f64 then
          if rm == .rz then .unsupportedFloatOp "add.rz.f64"
          else
            let res := f64ToBv (bvToF64 va + bvToF64 vb)
            PTXOutcome.bind (th.regs.setScalar dst res (some ty.bitWidth)) fun rf' =>
              .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
        else
          let res := maskForType ty (maskForType ty va + maskForType ty vb)
          PTXOutcome.bind (th.regs.setScalar dst res (some ty.bitWidth)) fun rf' =>
            .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
  | .sub ty dst a b =>
    PTXOutcome.bind (evalOperand cta th a (some ty.bitWidth)) fun va =>
      PTXOutcome.bind (evalOperand cta th b (some ty.bitWidth)) fun vb =>
        let res :=
          if ty == .f32 then f32ToBv (bvToF32 va - bvToF32 vb)
          else if ty == .f64 then f64ToBv (bvToF64 va - bvToF64 vb)
          else maskForType ty (maskForType ty va - maskForType ty vb)
        PTXOutcome.bind (th.regs.setScalar dst res (some ty.bitWidth)) fun rf' =>
          .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
  | .mul mode ty dst a b =>
    PTXOutcome.bind (evalOperand cta th a (some ty.bitWidth)) fun va =>
      PTXOutcome.bind (evalOperand cta th b (some ty.bitWidth)) fun vb =>
        let dstWidth := if mode == .wide && (ty == .u32 || ty == .b32 || ty == .s32) then 64 else ty.bitWidth
        if ty == .f32 then
          if mode != .rn && mode != .lo then .unsupportedFloatOp "mul float mode"
          else
            let out := f32ToBv (bvToF32 va * bvToF32 vb)
            PTXOutcome.bind (th.regs.setScalar dst out (some dstWidth)) fun rf' =>
              .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
        else if ty == .f64 then
          if mode != .rn && mode != .lo then .unsupportedFloatOp "mul float mode"
          else
            let out := f64ToBv (bvToF64 va * bvToF64 vb)
            PTXOutcome.bind (th.regs.setScalar dst out (some dstWidth)) fun rf' =>
              .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
        else
          let out := match mode, ty with
            | .wide, .u32 | .wide, .b32 =>
              .ok ((va &&& 0xFFFF_FFFF#64) * (vb &&& 0xFFFF_FFFF#64))
            | .wide, .s32 =>
              .ok (signExtend32To64 va * signExtend32To64 vb)
            | .wide, _ =>
              .typeMismatch "mul.wide requires a 32-bit integer type"
            | .rn, _ =>
              .typeMismatch "mul.rn requires a floating-point type"
            | .hi, .u64 | .hi, .b64 =>
              let prod128 : BitVec 128 := (va.zeroExtend 128) * (vb.zeroExtend 128)
              .ok ((prod128 >>> 64).truncate 64)
            | .hi, .s64 =>
              let prod128 : BitVec 128 := (va.signExtend 128) * (vb.signExtend 128)
              .ok ((prod128 >>> 64).truncate 64)
            | .hi, .u32 | .hi, .b32 =>
              let prod64 : BitVec 64 := (va &&& 0xFFFF_FFFF#64) * (vb &&& 0xFFFF_FFFF#64)
              .ok ((prod64 >>> 32) &&& 0xFFFF_FFFF#64)
            | .hi, .s32 =>
              let prod64 : BitVec 64 := signExtend32To64 va * signExtend32To64 vb
              .ok ((prod64 >>> 32) &&& 0xFFFF_FFFF#64)
            | .hi, .u16 | .hi, .b16 =>
              let prod32 : BitVec 64 := (va &&& 0xFFFF#64) * (vb &&& 0xFFFF#64)
              .ok ((prod32 >>> 16) &&& 0xFFFF#64)
            | _, _ =>
              .ok (maskForType ty (maskForType ty va * maskForType ty vb))
          PTXOutcome.bind out fun outVal =>
            PTXOutcome.bind (th.regs.setScalar dst outVal (some dstWidth)) fun rf' =>
              .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
  | .div ty dst a b =>
    PTXOutcome.bind (evalOperand cta th a (some ty.bitWidth)) fun va =>
      PTXOutcome.bind (evalOperand cta th b (some ty.bitWidth)) fun vb =>
        if ty == .f32 then
          let res := f32ToBv (bvToF32 va / bvToF32 vb)
          PTXOutcome.bind (th.regs.setScalar dst res (some ty.bitWidth)) fun rf' =>
            .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
        else if ty == .f64 then
          let res := f64ToBv (bvToF64 va / bvToF64 vb)
          PTXOutcome.bind (th.regs.setScalar dst res (some ty.bitWidth)) fun rf' =>
            .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
        else
          let ma := maskForType ty va
          let mb := maskForType ty vb
          if mb == 0#64 then
            .divisionByZero
          else if ty == .s64 then
            if ma == 0x8000_0000_0000_0000#64 && mb == 0xFFFF_FFFF_FFFF_FFFF#64 then
              .signedDivOverflow
            else
              let res := BitVec.sdiv ma mb
              PTXOutcome.bind (th.regs.setScalar dst res (some ty.bitWidth)) fun rf' =>
                .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
          else if ty == .s32 then
            let a32 := ma.truncate 32
            let b32 := mb.truncate 32
            if a32 == 0x8000_0000#32 && b32 == 0xFFFF_FFFF#32 then
              .signedDivOverflow
            else
              let q32 := BitVec.sdiv a32 b32
              PTXOutcome.bind (th.regs.setScalar dst (q32.zeroExtend 64) (some ty.bitWidth)) fun rf' =>
                .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
          else
            let res := maskForType ty (ma / mb)
            PTXOutcome.bind (th.regs.setScalar dst res (some ty.bitWidth)) fun rf' =>
              .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
  | .rem ty dst a b =>
    PTXOutcome.bind (evalOperand cta th a (some ty.bitWidth)) fun va =>
      PTXOutcome.bind (evalOperand cta th b (some ty.bitWidth)) fun vb =>
        if ty == .f32 || ty == .f64 then
          .unsupportedFloatOp "rem on floating-point type"
        else
          let ma := maskForType ty va
          let mb := maskForType ty vb
          if mb == 0#64 then
            .divisionByZero
          else if ty == .s64 then
            if ma == 0x8000_0000_0000_0000#64 && mb == 0xFFFF_FFFF_FFFF_FFFF#64 then
              .signedDivOverflow
            else
              let res := BitVec.srem ma mb
              PTXOutcome.bind (th.regs.setScalar dst res (some ty.bitWidth)) fun rf' =>
                .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
          else if ty == .s32 then
            let a32 := ma.truncate 32
            let b32 := mb.truncate 32
            if a32 == 0x8000_0000#32 && b32 == 0xFFFF_FFFF#32 then
              .signedDivOverflow
            else
              let r32 := BitVec.srem a32 b32
              PTXOutcome.bind (th.regs.setScalar dst (r32.zeroExtend 64) (some ty.bitWidth)) fun rf' =>
                .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
          else
            let res := maskForType ty (ma % mb)
            PTXOutcome.bind (th.regs.setScalar dst res (some ty.bitWidth)) fun rf' =>
              .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
  | .mad mode ty dst a b c =>
    if ty == .f32 || ty == .f64 then
      if mode != .rn then
        .unsupportedFloatOp "mad float mode"
      else
        PTXOutcome.bind (evalOperand cta th a (some ty.bitWidth)) fun va =>
          PTXOutcome.bind (evalOperand cta th b (some ty.bitWidth)) fun vb =>
            PTXOutcome.bind (evalOperand cta th c (some ty.bitWidth)) fun vc =>
              let res :=
                if ty == .f32 then f32ToBv (Float32.fma (bvToF32 va) (bvToF32 vb) (bvToF32 vc))
                else f64ToBv (Float.fma (bvToF64 va) (bvToF64 vb) (bvToF64 vc))
              PTXOutcome.bind (th.regs.setScalar dst res (some ty.bitWidth)) fun rf' =>
                .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
    else if mode == .rn then
      .typeMismatch "mad.rn requires a floating-point type"
    else if mode == .wide && ty != .u32 && ty != .b32 && ty != .s32 then
      .typeMismatch "mad.wide requires a 32-bit integer type"
    else
      let resTy := if mode == .wide then PTXType.u64 else ty
      PTXOutcome.bind (evalOperand cta th a (some ty.bitWidth)) fun va =>
        PTXOutcome.bind (evalOperand cta th b (some ty.bitWidth)) fun vb =>
          PTXOutcome.bind (evalOperand cta th c (some resTy.bitWidth)) fun vc =>
            let prod := match mode, ty with
              | .wide, .u32 | .wide, .b32 =>
                (va &&& 0xFFFF_FFFF#64) * (vb &&& 0xFFFF_FFFF#64)
              | .wide, .s32 =>
                signExtend32To64 va * signExtend32To64 vb
              | .hi, .u64 | .hi, .b64 =>
                let prod128 : BitVec 128 := (va.zeroExtend 128) * (vb.zeroExtend 128)
                (prod128 >>> 64).truncate 64
              | .hi, .s64 =>
                let prod128 : BitVec 128 := (va.signExtend 128) * (vb.signExtend 128)
                (prod128 >>> 64).truncate 64
              | .hi, .u32 | .hi, .b32 =>
                let prod64 : BitVec 64 := (va &&& 0xFFFF_FFFF#64) * (vb &&& 0xFFFF_FFFF#64)
                (prod64 >>> 32) &&& 0xFFFF_FFFF#64
              | .hi, .s32 =>
                let prod64 : BitVec 64 := signExtend32To64 va * signExtend32To64 vb
                (prod64 >>> 32) &&& 0xFFFF_FFFF#64
              | .hi, .u16 | .hi, .b16 =>
                let prod32 : BitVec 64 := (va &&& 0xFFFF#64) * (vb &&& 0xFFFF#64)
                (prod32 >>> 16) &&& 0xFFFF#64
              | _, _ =>
                maskForType ty (maskForType ty va * maskForType ty vb)
            let res := maskForType resTy (prod + maskForType resTy vc)
            PTXOutcome.bind (th.regs.setScalar dst res (some resTy.bitWidth)) fun rf' =>
              .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
  | .fma rm ty dst a b c =>
    PTXOutcome.bind (evalOperand cta th a (some ty.bitWidth)) fun va =>
      PTXOutcome.bind (evalOperand cta th b (some ty.bitWidth)) fun vb =>
        PTXOutcome.bind (evalOperand cta th c (some ty.bitWidth)) fun vc =>
          if rm == .rz then
            .unsupportedFloatOp "fma.rz"
          else if ty == .f32 then
            let res := f32ToBv (Float32.fma (bvToF32 va) (bvToF32 vb) (bvToF32 vc))
            PTXOutcome.bind (th.regs.setScalar dst res (some ty.bitWidth)) fun rf' =>
              .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
          else if ty == .f64 then
            let res := f64ToBv (Float.fma (bvToF64 va) (bvToF64 vb) (bvToF64 vc))
            PTXOutcome.bind (th.regs.setScalar dst res (some ty.bitWidth)) fun rf' =>
              .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
          else
            .unsupportedFloatOp "fma requires .f32 or .f64"
  | .bitAnd ty dst a b =>
    if ty == .pred then
      PTXOutcome.bind (evalPredOperand cta th a) fun pa =>
        PTXOutcome.bind (evalPredOperand cta th b) fun pb =>
          PTXOutcome.bind (th.regs.setPred dst (pa && pb)) fun rf' =>
            .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
    else if !ty.isBitType then
      .typeMismatch s!"bitwise and requires .pred or .b* type, got {ppPTXType ty}"
    else
      PTXOutcome.bind (evalOperand cta th a (some ty.bitWidth)) fun va =>
        PTXOutcome.bind (evalOperand cta th b (some ty.bitWidth)) fun vb =>
          let res := maskForType ty (va &&& vb)
          PTXOutcome.bind (th.regs.setScalar dst res (some ty.bitWidth)) fun rf' =>
            .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
  | .bitOr ty dst a b =>
    if ty == .pred then
      PTXOutcome.bind (evalPredOperand cta th a) fun pa =>
        PTXOutcome.bind (evalPredOperand cta th b) fun pb =>
          PTXOutcome.bind (th.regs.setPred dst (pa || pb)) fun rf' =>
            .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
    else if !ty.isBitType then
      .typeMismatch s!"bitwise or requires .pred or .b* type, got {ppPTXType ty}"
    else
      PTXOutcome.bind (evalOperand cta th a (some ty.bitWidth)) fun va =>
        PTXOutcome.bind (evalOperand cta th b (some ty.bitWidth)) fun vb =>
          let res := maskForType ty (va ||| vb)
          PTXOutcome.bind (th.regs.setScalar dst res (some ty.bitWidth)) fun rf' =>
            .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
  | .bitXor ty dst a b =>
    if ty == .pred then
      PTXOutcome.bind (evalPredOperand cta th a) fun pa =>
        PTXOutcome.bind (evalPredOperand cta th b) fun pb =>
          PTXOutcome.bind (th.regs.setPred dst (pa != pb)) fun rf' =>
            .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
    else if !ty.isBitType then
      .typeMismatch s!"bitwise xor requires .pred or .b* type, got {ppPTXType ty}"
    else
      PTXOutcome.bind (evalOperand cta th a (some ty.bitWidth)) fun va =>
        PTXOutcome.bind (evalOperand cta th b (some ty.bitWidth)) fun vb =>
          let res := maskForType ty (va ^^^ vb)
          PTXOutcome.bind (th.regs.setScalar dst res (some ty.bitWidth)) fun rf' =>
            .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
  | .bitNot ty dst a =>
    if ty == .pred then
      PTXOutcome.bind (evalPredOperand cta th a) fun pa =>
        PTXOutcome.bind (th.regs.setPred dst (!pa)) fun rf' =>
          .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
    else if !ty.isBitType then
      .typeMismatch s!"bitwise not requires .pred or .b* type, got {ppPTXType ty}"
    else
      PTXOutcome.bind (evalOperand cta th a (some ty.bitWidth)) fun va =>
        let res := maskForType ty (~~~va)
        PTXOutcome.bind (th.regs.setScalar dst res (some ty.bitWidth)) fun rf' =>
          .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
  | .neg ty dst a =>
    PTXOutcome.bind (evalOperand cta th a (some ty.bitWidth)) fun va =>
      let res :=
        if ty == .f32 then f32ToBv (-bvToF32 va)
        else if ty == .f64 then f64ToBv (-bvToF64 va)
        else maskForType ty (0#64 - maskForType ty va)
      PTXOutcome.bind (th.regs.setScalar dst res (some ty.bitWidth)) fun rf' =>
        .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
  | .shl ty dst a sh =>
    if !ty.isBitType || ty == .b8 then
      .typeMismatch "shl requires .b16/.b32/.b64 bit-size type"
    else
      PTXOutcome.bind (evalOperand cta th a (some ty.bitWidth)) fun va =>
        PTXOutcome.bind (evalShiftAmount cta th sh) fun shiftAmt =>
          let width := ty.bitWidth
          let res :=
            if shiftAmt ≥ width then 0#64
            else maskForType ty ((maskForType ty va) <<< shiftAmt)
          PTXOutcome.bind (th.regs.setScalar dst res (some ty.bitWidth)) fun rf' =>
            .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
  | .shr ty dst a sh =>
    if ty == .f32 || ty == .f64 || ty == .pred || ty == .b8 then
      .typeMismatch "shr requires .b16/.b32/.b64/.u16/.u32/.u64/.s32/.s64 type"
    else
      PTXOutcome.bind (evalOperand cta th a (some ty.bitWidth)) fun va =>
        PTXOutcome.bind (evalShiftAmount cta th sh) fun shiftAmt =>
          let res := match ty with
            | .s64 =>
              let clamped := if shiftAmt ≥ 63 then 63 else shiftAmt
              BitVec.sshiftRight va clamped
            | .s32 =>
              let clamped := if shiftAmt ≥ 31 then 31 else shiftAmt
              let s32 := BitVec.sshiftRight (va.truncate 32) clamped
              s32.zeroExtend 64
            | _ =>
              let width := ty.bitWidth
              if shiftAmt ≥ width then 0#64
              else maskForType ty ((maskForType ty va) >>> shiftAmt)
          PTXOutcome.bind (th.regs.setScalar dst res (some ty.bitWidth)) fun rf' =>
            .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
  | .setp cmp ty dstPred a b =>
    PTXOutcome.bind (evalOperand cta th a (some ty.bitWidth)) fun va =>
      PTXOutcome.bind (evalOperand cta th b (some ty.bitWidth)) fun vb =>
        let flag := evalPTXCmp cmp ty va vb
        PTXOutcome.bind (th.regs.setPred dstPred flag) fun rf' =>
          .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
  | .selp ty dst tOp fOp predName =>
    PTXOutcome.bind (th.regs.readPredChecked predName) fun cond =>
      PTXOutcome.bind (evalOperand cta th tOp (some ty.bitWidth)) fun vt =>
        PTXOutcome.bind (evalOperand cta th fOp (some ty.bitWidth)) fun vf =>
          let chosen := maskForType ty (if cond then vt else vf)
          PTXOutcome.bind (th.regs.setScalar dst chosen (some ty.bitWidth)) fun rf' =>
            .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
  | .shflSyncBfly _ _ _ _ _ =>
    .barrierDivergence 0
  | .barSync bid =>
    .barrierDivergence bid
  | .bra targetLbl =>
    match findLabelPC? stmts targetLbl with
    | some targetPc => .ok ({ th with pc := targetPc }, cta.globalMem, cta.sharedMem, cta.epochLog)
    | none => .unboundLabel targetLbl
  | .ret =>
    .ok ({ th with pc := nextPc, halted := true }, cta.globalMem, cta.sharedMem, cta.epochLog)

/-- Execute a single predicated instruction (`@p` / `@!p`) for thread `th`.
    When the evaluated guard is `false`, the instruction is a pure PC-advancing no-op. -/
def execPredicatedInstr (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    (guard : Option PTXPredGuard) (ins : PTXInstr) :
    PTXOutcome (PTXThreadState × ByteMemory × ByteMemory × List MemAccessLog) :=
  PTXOutcome.bind (evalPredGuard th guard) fun active =>
    if active then
      execNonBarrierInstr stmts cta th ins
    else
      .ok ({ th with pc := th.pc + 1 }, cta.globalMem, cta.sharedMem, cta.epochLog)

/-- True if thread `th` is currently parked at an active (`guard = true`, unhalted) `bar.sync bid`
    at `stmts[th.pc]?`. -/
def threadAtActiveBarrier (stmts : List PTXStmt) (th : PTXThreadState) :
    PTXOutcome (Option Nat) :=
  if th.halted then
    .ok none
  else
    match stmts[th.pc]? with
    | some (.instr guard (.barSync bid)) =>
      PTXOutcome.bind (evalPredGuard th guard) fun active =>
        .ok (if active then some bid else none)
    | _ => .ok none

/-- True if thread `th` is currently parked at an active (`guard = true`, unhalted) `shfl.sync.bfly.b32`
    at `stmts[th.pc]?`. -/
def threadAtActiveShfl (stmts : List PTXStmt) (th : PTXThreadState) :
    PTXOutcome Bool :=
  if th.halted then
    .ok false
  else
    match stmts[th.pc]? with
    | some (.instr guard (.shflSyncBfly _ _ _ _ _)) =>
      evalPredGuard th guard
    | _ => .ok false

/-- Collect the barrier state of every thread in `threads`. -/
def collectBarrierStates (stmts : List PTXStmt) :
    List PTXThreadState → PTXOutcome (List (Option Nat))
  | [] => .ok []
  | th :: rest =>
    PTXOutcome.bind (threadAtActiveBarrier stmts th) fun b =>
      PTXOutcome.bind (collectBarrierStates stmts rest) fun bs =>
        .ok (b :: bs)

/-- Synchronize a CTA when every thread in the CTA has arrived at the exact same `bar.sync bid`:
    advances all threads past the barrier (`pc + 1`) and clears `epochLog` to begin a fresh
    data-race-free barrier epoch. If some thread is at `bar.sync bid` while another thread in the CTA
    is halted or at a different barrier / stuck elsewhere, reports `PTXOutcome.barrierDivergence bid`. -/
def stepCTABarrier (bid : Nat) (states : List (Option Nat)) (cta : PTXCTAState) :
    PTXOutcome PTXCTAState :=
  if states.all (fun s => s == some bid) then
    .ok { cta with
      threads := cta.threads.map fun th => { th with pc := th.pc + 1 }
      epochLog := [] }
  else
    .barrierDivergence bid

private def evalShflParticipants (stmts : List PTXStmt) (cta : PTXCTAState) (shflPc : Nat)
    (threads : List PTXThreadState) :
    PTXOutcome (List (Nat × PTXThreadState × String × BitVec 64 × Nat × Nat × Nat)) :=
  match threads with
  | [] => .ok []
  | th :: rest =>
    PTXOutcome.bind (threadAtActiveShfl stmts th) fun atShfl =>
      if !atShfl then
        evalShflParticipants stmts cta shflPc rest
      else if th.pc != shflPc then
        .barrierDivergence 0
      else
        match stmts[th.pc]? with
        | some (.instr _ (.shflSyncBfly dst srcOp offOp clampOp maskOp)) =>
          PTXOutcome.bind (evalOperand cta th srcOp (some 32)) fun vSrc =>
            PTXOutcome.bind (evalOperand cta th offOp (some 32)) fun vOff =>
              PTXOutcome.bind (evalOperand cta th clampOp (some 32)) fun vClamp =>
                PTXOutcome.bind (evalOperand cta th maskOp (some 32)) fun vMask =>
                  PTXOutcome.bind (evalShflParticipants stmts cta shflPc rest) fun tail =>
                    let lane := (cta.blockDim.linearTid th.tid) % 32
                    let off := (vOff &&& 0x1F#64).toNat
                    let clampVal := (vClamp &&& 0xFFFF_FFFF#64).toNat
                    let maskVal := (vMask &&& 0xFFFF_FFFF#64).toNat
                    .ok ((lane, th, dst, vSrc &&& 0xFFFF_FFFF#64, off, clampVal, maskVal) :: tail)
        | _ => .barrierDivergence 0

private def applyShflResults (blockDim : Dim3) (warpId : Nat) (requiredMask : Nat)
    (parts : List (Nat × PTXThreadState × String × BitVec 64 × Nat × Nat × Nat)) :
    List PTXThreadState → PTXOutcome (List PTXThreadState)
  | [] => .ok []
  | th :: rest =>
    let lin := blockDim.linearTid th.tid
    if lin / 32 != warpId then
      PTXOutcome.bind (applyShflResults blockDim warpId requiredMask parts rest) fun rest' =>
        .ok (th :: rest')
    else
      let lane := lin % 32
      match parts.find? (fun (l, _, _, _, _, _, _) => l == lane) with
      | none =>
        PTXOutcome.bind (applyShflResults blockDim warpId requiredMask parts rest) fun rest' =>
          .ok (th :: rest')
      | some (_, _, dst, selfVal, off, clampVal, _) =>
        let maxLane := clampVal &&& 0x1F
        let segMask := (clampVal >>> 8) &&& 0x1F
        let minLane := lane &&& segMask
        let upperBound := minLane ||| (maxLane &&& (0x1F ^^^ segMask))
        let cand := lane ^^^ off
        let srcLane :=
          if cand ≤ upperBound && ((requiredMask >>> cand) &&& 1) == 1 then cand else lane
        let resVal := match parts.find? (fun (l, _, _, _, _, _, _) => l == srcLane) with
          | some (_, _, _, v, _, _, _) => v
          | none => selfVal
        PTXOutcome.bind (th.regs.setScalar dst resVal (some 32)) fun rf' =>
          PTXOutcome.bind (applyShflResults blockDim warpId requiredMask parts rest) fun rest' =>
            .ok ({ th with pc := th.pc + 1, regs := rf' } :: rest')

/-- Execute one warp's synchronous `shfl.sync.bfly.b32` exchange for `warpId`.
    All active participants named in `membermask` within this warp must be parked at the identical
    `pc` executing `shfl.sync.bfly.b32`; each participating lane reads its partner lane's pre-shuffle
    32-bit operand (`srcLane = laneId ^^^ offset`, clamped via `clampMask`/`segMask` per PTX 8.0) and
    writes `dst` in lockstep before advancing `pc`. -/
def stepWarpShfl (stmts : List PTXStmt) (cta : PTXCTAState) (warpId : Nat) (shflPc : Nat) :
    PTXOutcome PTXCTAState :=
  let warpThreads := cta.threads.filter fun th => (cta.blockDim.linearTid th.tid) / 32 == warpId
  PTXOutcome.bind (evalShflParticipants stmts cta shflPc warpThreads) fun parts =>
    match parts with
    | [] => .barrierDivergence 0
    | (_, _, _, _, _, _, mask0) :: _ =>
      let existingWarpMask : Nat := warpThreads.foldl (fun acc th =>
        let lane := (cta.blockDim.linearTid th.tid) % 32
        acc ||| (1 <<< lane)) 0
      let requiredMask : Nat := mask0 &&& existingWarpMask
      let arrivedMask : Nat := parts.foldl (fun acc (lane, _, _, _, _, _, _) =>
        acc ||| (1 <<< lane)) 0
      let masksAgree : Bool := parts.all fun (lane, _, _, _, _, _, m) =>
        (m &&& existingWarpMask) == requiredMask && ((requiredMask >>> lane) &&& 1) == 1
      if !masksAgree || arrivedMask != requiredMask then
        .barrierDivergence 0
      else
        PTXOutcome.bind (applyShflResults cta.blockDim warpId requiredMask parts cta.threads) fun updatedThreads =>
          .ok { cta with threads := updatedThreads }

/-- Find the first warp that has at least one thread parked at an active `shfl.sync.bfly.b32`. -/
def findWaitingShflWarp? (stmts : List PTXStmt) (blockDim : Dim3) :
    List PTXThreadState → PTXOutcome (Option (Nat × Nat))
  | [] => .ok none
  | th :: rest =>
    PTXOutcome.bind (threadAtActiveShfl stmts th) fun active =>
      if active then
        .ok (some ((blockDim.linearTid th.tid) / 32, th.pc))
      else
        findWaitingShflWarp? stmts blockDim rest

/-- Advance the first non-halted, non-barrier-waiting, non-shfl-waiting thread by one statement, so
    threads run independently up to CTA barriers (`bar.sync`) or warp collectives (`shfl.sync.bfly.b32`). -/
def stepFirstReadyThread (stmts : List PTXStmt) (cta : PTXCTAState) :
    List PTXThreadState → List PTXThreadState → PTXOutcome (Bool × PTXCTAState)
  | _, [] => .ok (false, cta)
  | prefixRev, th :: suffix =>
    if th.halted then
      stepFirstReadyThread stmts cta (th :: prefixRev) suffix
    else
      match stmts[th.pc]? with
      | none =>
        let th' := { th with halted := true }
        .ok (true, { cta with threads := prefixRev.reverse ++ (th' :: suffix) })
      | some (.label _) =>
        let th' := { th with pc := th.pc + 1 }
        .ok (true, { cta with threads := prefixRev.reverse ++ (th' :: suffix) })
      | some (.instr guard (.barSync _)) =>
        PTXOutcome.bind (evalPredGuard th guard) fun active =>
          if active then
            stepFirstReadyThread stmts cta (th :: prefixRev) suffix
          else
            let th' := { th with pc := th.pc + 1 }
            .ok (true, { cta with threads := prefixRev.reverse ++ (th' :: suffix) })
      | some (.instr guard (.shflSyncBfly _ _ _ _ _)) =>
        PTXOutcome.bind (evalPredGuard th guard) fun active =>
          if active then
            stepFirstReadyThread stmts cta (th :: prefixRev) suffix
          else
            let th' := { th with pc := th.pc + 1 }
            .ok (true, { cta with threads := prefixRev.reverse ++ (th' :: suffix) })
      | some (.instr guard ins) =>
        PTXOutcome.bind (execPredicatedInstr stmts cta th guard ins) fun (th', gMem', sMem', log') =>
          .ok (true, { cta with
            threads := prefixRev.reverse ++ (th' :: suffix)
            globalMem := gMem'
            sharedMem := sMem'
            epochLog := log' })

/-- Single SIMT CTA step:
    1. If all threads are halted, CTA execution is complete (`done = true`).
    2. Otherwise, if any non-barrier-waiting, non-shfl-waiting thread can advance, advance it.
    3. Otherwise, if any warp is parked at `shfl.sync.bfly.b32`, execute the warp shuffle in lockstep.
    4. Otherwise, inspect CTA `bar.sync` states: if all threads agree on `some bid`, release the
       barrier in lockstep and clear `epochLog`; otherwise report `PTXOutcome.barrierDivergence bid`. -/
def stepCTA (stmts : List PTXStmt) (cta : PTXCTAState) : PTXOutcome (Bool × PTXCTAState) :=
  if cta.threads.all (·.halted) then
    .ok (true, cta)
  else
    PTXOutcome.bind (stepFirstReadyThread stmts cta [] cta.threads) fun (progressed, cta') =>
      if progressed then
        .ok (false, cta')
      else
        PTXOutcome.bind (findWaitingShflWarp? stmts cta'.blockDim cta'.threads) fun shflOpt =>
          match shflOpt with
          | some (warpId, shflPc) =>
            PTXOutcome.bind (stepWarpShfl stmts cta' warpId shflPc) fun afterShfl =>
              .ok (false, afterShfl)
          | none =>
            PTXOutcome.bind (collectBarrierStates stmts cta'.threads) fun barStates =>
              match barStates.findSome? id with
              | some bid =>
                PTXOutcome.bind (stepCTABarrier bid barStates cta') fun synced =>
                  .ok (false, synced)
              | none => .ok (true, cta')

/-- Execute a CTA with bounded `fuel` steps. -/
def runCTA (fuel : Nat) (stmts : List PTXStmt) (cta : PTXCTAState) : PTXOutcome PTXCTAState :=
  match fuel with
  | 0 =>
    if cta.threads.all (·.halted) then .ok cta else .fuelExhausted
  | f + 1 =>
    PTXOutcome.bind (stepCTA stmts cta) fun (done, cta') =>
      if done then .ok cta' else runCTA f stmts cta'

/-- Initialize a `PTXCTAState` for a kernel launch on CTA coordinate `ctaId` (with optional `.const` memory),
    populating each thread's register file from `k.regDecls` with declared width & initialization checks enabled. -/
def initCTAState (k : PTXKernel) (gridDim blockDim ctaId : Dim3)
    (globalMem : ByteMemory) (paramMem : ParamMemory)
    (constMem : ByteMemory := ByteMemory.zeros 0) : PTXCTAState :=
  let layout := buildSharedLayout k.sharedDecls
  let initRegs := PTXRegFile.ofRegDecls k.regDecls
  let threads := blockDim.coords.map fun tid =>
    { tid := tid
      pc := 0
      regs := initRegs
      localMem := ByteMemory.zeros k.localBytes
      halted := false }
  { gridDim
    blockDim
    ctaId
    threads
    globalMem
    sharedMem := ByteMemory.zeros layout.totalSize
    constMem
    paramMem
    sharedLayout := layout
    epochLog := [] }

/-- Check whether two `.global` memory accesses across distinct CTAs conflict (`W-W` or `R-W`, and
    not both atomic). -/
def findCrossCTARace? (prior : List MemAccessLog) (entry : MemAccessLog) : Option Nat :=
  match prior with
  | [] => none
  | p :: rest =>
    if p.space == .global && entry.space == .global &&
       (entry.isWrite || p.isWrite) && !(entry.isAtomic && p.isAtomic) &&
       rangesOverlap entry.addr entry.width p.addr p.width then
      some (Nat.max entry.addr p.addr)
    else
      findCrossCTARace? rest entry

def checkCrossCTAGlobalLog (prior : List MemAccessLog) :
    List MemAccessLog → PTXOutcome Unit
  | [] => .ok ()
  | entry :: rest =>
    if entry.space != .global then
      checkCrossCTAGlobalLog prior rest
    else
      match findCrossCTARace? prior entry with
      | some conflictAddr => .dataRace .global conflictAddr
      | none => checkCrossCTAGlobalLog prior rest

/-- Execute a CTA with bounded `fuel` steps, returning both the final `PTXCTAState` and the list of
    all `.global` memory accesses performed across all barrier epochs of this CTA (`bar.sync`
    synchronizes intra-CTA threads only, never across distinct CTAs). -/
def runCTAWithGlobalLog (fuel : Nat) (stmts : List PTXStmt) (cta : PTXCTAState)
    (savedGlobal : List MemAccessLog := []) : PTXOutcome (PTXCTAState × List MemAccessLog) :=
  match fuel with
  | 0 =>
    if cta.threads.all (·.halted) then
      let curGlobal := cta.epochLog.filter (fun e => e.space == .global)
      .ok (cta, curGlobal ++ savedGlobal)
    else
      .fuelExhausted
  | f + 1 =>
    let preGlobal := cta.epochLog.filter (fun e => e.space == .global)
    PTXOutcome.bind (stepCTA stmts cta) fun (done, cta') =>
      let saved' :=
        if !cta.epochLog.isEmpty && cta'.epochLog.isEmpty then
          preGlobal ++ savedGlobal
        else
          savedGlobal
      if done then
        let postGlobal := cta'.epochLog.filter (fun e => e.space == .global)
        .ok (cta', postGlobal ++ saved')
      else
        runCTAWithGlobalLog f stmts cta' saved'

def evalPTXKernelLoop (fuelPerCTA : Nat) (k : PTXKernel) (gridDim blockDim : Dim3)
    (paramMem : ParamMemory) (constMem : ByteMemory) (gMem : ByteMemory)
    (priorGlobalLog : List MemAccessLog) :
    List Dim3 → PTXOutcome ByteMemory
  | [] => .ok gMem
  | ctaId :: rest =>
    let cta0 := initCTAState k gridDim blockDim ctaId gMem paramMem constMem
    PTXOutcome.bind (runCTAWithGlobalLog fuelPerCTA k.body cta0 []) fun (ctaFinal, ctaGlobalLog) =>
      PTXOutcome.bind (checkCrossCTAGlobalLog priorGlobalLog ctaGlobalLog) fun () =>
        evalPTXKernelLoop fuelPerCTA k gridDim blockDim paramMem constMem ctaFinal.globalMem
          (ctaGlobalLog ++ priorGlobalLog) rest

/-- Launch a `PTXKernel` across every CTA in `gridDim` (each with fresh per-CTA `sharedMem` and
    per-thread `localMem`), threading `globalMem` across CTAs, trapping on unsynchronized cross-CTA
    `.global` data races, and returning the final `ByteMemory`. -/
def evalPTXKernel (fuelPerCTA : Nat) (k : PTXKernel) (gridDim blockDim : Dim3)
    (globalMem : ByteMemory) (paramMem : ParamMemory)
    (constMem : ByteMemory := ByteMemory.zeros 0) : PTXOutcome ByteMemory :=
  evalPTXKernelLoop fuelPerCTA k gridDim blockDim paramMem constMem globalMem [] gridDim.coords

/-! ## 3. 1:1 Structural Pretty-Printer -/

/-- Render a `StateSpace` directive/modifier. -/
def ppStateSpace : StateSpace → String
  | .reg    => ".reg"
  | .param  => ".param"
  | .shared => ".shared"
  | .global => ".global"
  | .local  => ".local"
  | .const  => ".const"

/-- Render a `SpecialReg` (`%tid.x`, `%ctaid.x`, ...). -/
def ppSpecialReg : SpecialReg → String
  | .tidX    => "%tid.x"
  | .tidY    => "%tid.y"
  | .tidZ    => "%tid.z"
  | .ntidX   => "%ntid.x"
  | .ntidY   => "%ntid.y"
  | .ntidZ   => "%ntid.z"
  | .ctaidX  => "%ctaid.x"
  | .ctaidY  => "%ctaid.y"
  | .ctaidZ  => "%ctaid.z"
  | .nctaidX => "%nctaid.x"
  | .nctaidY => "%nctaid.y"
  | .nctaidZ => "%nctaid.z"

/-- Render a `PTXMulMode` modifier. -/
def ppMulMode : PTXMulMode → String
  | .lo   => ".lo"
  | .hi   => ".hi"
  | .wide => ".wide"
  | .rn   => ".rn"

/-- Render an optional `PTXRoundMode` modifier. -/
def ppRoundMode : PTXRoundMode → String
  | .none => ""
  | .rn   => ".rn"
  | .rz   => ".rz"

/-- Render a `PTXCmpOp` modifier. -/
def ppCmpOp : PTXCmpOp → String
  | .eq => ".eq"
  | .ne => ".ne"
  | .lt => ".lt"
  | .le => ".le"
  | .gt => ".gt"
  | .ge => ".ge"
  | .lo => ".lo"
  | .ls => ".ls"
  | .hi => ".hi"
  | .hs => ".hs"

private def hexDigitChar (n : Nat) : Char :=
  let d := n % 16
  if d < 10 then Char.ofNat ('0'.toNat + d) else Char.ofNat ('a'.toNat + (d - 10))

private def toHexFixedGo (v : Nat) (acc : List Char) : Nat → List Char
  | 0 => acc
  | k + 1 => toHexFixedGo (v / 16) (hexDigitChar v :: acc) k

private def toHexFixed (val : Nat) (nibbles : Nat) : String :=
  String.ofList (toHexFixedGo val [] nibbles)

/-- Render a `PTXOperand`. -/
def ppPTXOperand : PTXOperand → String
  | .reg r       => r
  | .sreg sr     => ppSpecialReg sr
  | .immU64 v    => toString v.toNat
  | .immS64 i    => toString i
  | .immF32 bits => s!"0f{toHexFixed bits.toNat 8}"
  | .immF64 bits => s!"0d{toHexFixed bits.toNat 16}"
  | .sym s       => s

/-- Render a `PTXAddr` bracketed memory operand. -/
def ppPTXAddr : PTXAddr → String
  | .paramSym name => s!"[{name}]"
  | .regOffset r 0 => s!"[{r}]"
  | .regOffset r off =>
    if off > 0 then s!"[{r}+{off}]" else s!"[{r}{off}]"
  | .symOffset s 0 => s!"[{s}]"
  | .symOffset s off =>
    if off > 0 then s!"[{s}+{off}]" else s!"[{s}{off}]"

/-- Render a `PTXPredGuard` (`@%p1 ` or `@!%p1 `). -/
def ppPredGuard (g : PTXPredGuard) : String :=
  if g.negated then s!"@!{g.predReg} " else s!"@{g.predReg} "

/-- Render a single `PTXInstr` (without leading indentation or predicate guard). -/
def ppPTXInstr : PTXInstr → String
  | .mov ty dst src =>
    s!"mov{ppPTXType ty} {dst}, {ppPTXOperand src}" ++ ";"
  | .ldParam ty dst paramName =>
    s!"ld.param{ppPTXType ty} {dst}, [{paramName}]" ++ ";"
  | .ldGlobal ty dst addr =>
    s!"ld.global{ppPTXType ty} {dst}, {ppPTXAddr addr}" ++ ";"
  | .ldShared ty dst addr =>
    s!"ld.shared{ppPTXType ty} {dst}, {ppPTXAddr addr}" ++ ";"
  | .stGlobal ty addr src =>
    s!"st.global{ppPTXType ty} {ppPTXAddr addr}, {ppPTXOperand src}" ++ ";"
  | .stShared ty addr src =>
    s!"st.shared{ppPTXType ty} {ppPTXAddr addr}, {ppPTXOperand src}" ++ ";"
  | .cvtaToGlobal ty dst src =>
    s!"cvta.to.global{ppPTXType ty} {dst}, {ppPTXOperand src}" ++ ";"
  | .cvt rm dstTy srcTy dst src =>
    s!"cvt{ppRoundMode rm}{ppPTXType dstTy}{ppPTXType srcTy} {dst}, {ppPTXOperand src}" ++ ";"
  | .add rm ty dst a b =>
    s!"add{ppRoundMode rm}{ppPTXType ty} {dst}, {ppPTXOperand a}, {ppPTXOperand b}" ++ ";"
  | .sub ty dst a b =>
    s!"sub{ppPTXType ty} {dst}, {ppPTXOperand a}, {ppPTXOperand b}" ++ ";"
  | .mul mode ty dst a b =>
    s!"mul{ppMulMode mode}{ppPTXType ty} {dst}, {ppPTXOperand a}, {ppPTXOperand b}" ++ ";"
  | .div ty dst a b =>
    s!"div{ppPTXType ty} {dst}, {ppPTXOperand a}, {ppPTXOperand b}" ++ ";"
  | .rem ty dst a b =>
    s!"rem{ppPTXType ty} {dst}, {ppPTXOperand a}, {ppPTXOperand b}" ++ ";"
  | .mad mode ty dst a b c =>
    s!"mad{ppMulMode mode}{ppPTXType ty} {dst}, {ppPTXOperand a}, {ppPTXOperand b}, {ppPTXOperand c}" ++ ";"
  | .fma rm ty dst a b c =>
    s!"fma{ppRoundMode rm}{ppPTXType ty} {dst}, {ppPTXOperand a}, {ppPTXOperand b}, {ppPTXOperand c}" ++ ";"
  | .bitAnd ty dst a b =>
    s!"and{ppPTXType ty} {dst}, {ppPTXOperand a}, {ppPTXOperand b}" ++ ";"
  | .bitOr ty dst a b =>
    s!"or{ppPTXType ty} {dst}, {ppPTXOperand a}, {ppPTXOperand b}" ++ ";"
  | .bitXor ty dst a b =>
    s!"xor{ppPTXType ty} {dst}, {ppPTXOperand a}, {ppPTXOperand b}" ++ ";"
  | .bitNot ty dst a =>
    s!"not{ppPTXType ty} {dst}, {ppPTXOperand a}" ++ ";"
  | .neg ty dst a =>
    s!"neg{ppPTXType ty} {dst}, {ppPTXOperand a}" ++ ";"
  | .shl ty dst a sh =>
    s!"shl{ppPTXType ty} {dst}, {ppPTXOperand a}, {ppPTXOperand sh}" ++ ";"
  | .shr ty dst a sh =>
    s!"shr{ppPTXType ty} {dst}, {ppPTXOperand a}, {ppPTXOperand sh}" ++ ";"
  | .setp cmp ty dst a b =>
    s!"setp{ppCmpOp cmp}{ppPTXType ty} {dst}, {ppPTXOperand a}, {ppPTXOperand b}" ++ ";"
  | .selp ty dst tOp fOp p =>
    s!"selp{ppPTXType ty} {dst}, {ppPTXOperand tOp}, {ppPTXOperand fOp}, {p}" ++ ";"
  | .barSync bid =>
    s!"bar.sync {bid}" ++ ";"
  | .bra lbl =>
    s!"bra {lbl}" ++ ";"
  | .ret =>
    "ret" ++ ";"
  | .clz ty dst src =>
    s!"clz{ppPTXType ty} {dst}, {ppPTXOperand src}" ++ ";"
  | .movPack2x32 dst loOp hiOp =>
    ("mov.b64 " ++ dst ++ ", {" ++ ppPTXOperand loOp ++ ", " ++ ppPTXOperand hiOp ++ "}") ++ ";"
  | .movUnpack2x32 dstLo dstHi srcOp =>
    ("mov.b64 {" ++ dstLo ++ ", " ++ dstHi ++ "}, " ++ ppPTXOperand srcOp) ++ ";"
  | .shflSyncBfly dst srcOp offOp clampOp maskOp =>
    s!"shfl.sync.bfly.b32 {dst}, {ppPTXOperand srcOp}, {ppPTXOperand offOp}, {ppPTXOperand clampOp}, {ppPTXOperand maskOp}" ++ ";"
  | .atomAdd sp ty dst addr src =>
    s!"atom{ppStateSpace sp}.add{ppPTXType ty} {dst}, {ppPTXAddr addr}, {ppPTXOperand src}" ++ ";"
  | .atomCas sp ty dst addr cmp src =>
    s!"atom{ppStateSpace sp}.cas{ppPTXType ty} {dst}, {ppPTXAddr addr}, {ppPTXOperand cmp}, {ppPTXOperand src}" ++ ";"
  | .ldConst ty dst addr =>
    s!"ld.const{ppPTXType ty} {dst}, {ppPTXAddr addr}" ++ ";"
  | .ldLocal ty dst addr =>
    s!"ld.local{ppPTXType ty} {dst}, {ppPTXAddr addr}" ++ ";"
  | .stLocal ty addr src =>
    s!"st.local{ppPTXType ty} {ppPTXAddr addr}, {ppPTXOperand src}" ++ ";"
  | .stConst ty addr src =>
    s!"st.const{ppPTXType ty} {ppPTXAddr addr}, {ppPTXOperand src}" ++ ";"

/-- Render a `PTXStmt` inside a kernel body. -/
def ppPTXStmt : PTXStmt → String
  | .label lbl => s!"{lbl}:"
  | .instr none ins => s!"    {ppPTXInstr ins}"
  | .instr (some g) ins => s!"    {ppPredGuard g}{ppPTXInstr ins}"

/-- Render a `.visible .entry` `PTXKernel`. -/
def ppPTXKernel (k : PTXKernel) : String :=
  let paramLines := String.intercalate ",\n"
    (k.params.map fun p => s!"    .param {ppPTXType p.ty} {p.name}")
  let sharedLines := k.sharedDecls.map fun s =>
    s!"    .shared .align {s.align} {ppPTXType s.elemTy} {s.name}[{s.count}];"
  let localLines :=
    if k.localBytes == 0 then []
    else [s!"    .local .align 8 .b8 __local_mem[{k.localBytes}];"]
  let regLines := k.regDecls.map fun r =>
    s!"    .reg {ppPTXType r.ty} {r.prefixName}<{r.count}>;"
  let bodyLines := k.body.map ppPTXStmt
  let header :=
    if k.params.isEmpty then s!".visible .entry {k.name}()\n\{"
    else s!".visible .entry {k.name}(\n{paramLines}\n)\n\{"
  String.intercalate "\n" ([header] ++ sharedLines ++ localLines ++ regLines ++ bodyLines ++ ["}"])

/-- Render the canonical `.version` / `.target` / `.address_size` header of a `PTXModule`. -/
def ppPTXModuleHeader (m : PTXModule) : String :=
  s!".version {m.versionMajor}.{m.versionMinor}\n.target {m.target}\n.address_size {m.addressSize}"

/-- Render a complete `PTXModule` with `.version`, `.target`, `.address_size`, and all entry kernels. -/
def ppPTXModule (m : PTXModule) : String :=
  let header := ppPTXModuleHeader m
  match m.kernels with
  | [] => header ++ "\n"
  | ks => header ++ "\n\n" ++ String.intercalate "\n\n" (ks.map ppPTXKernel) ++ "\n"

end LeanNative.Backend.PTXAst
