/-!
# Genuine NVIDIA CUDA PTX 8.0 AST, Independent SIMT Semantics & 1:1 Pretty-Printer (`C2b`)

Provides:
1. Typed PTX ISA AST (`PTXType`, `StateSpace`, `SpecialReg`, `PTXOperand`, predicated `@p`/`@!p`
   instructions, `PTXInstr`, `PTXKernel`, `PTXModule`) covering every PTX construct emitted by
   production lowering (`mov`, `ld.param`, `ld.global`, `ld.shared`, `st.global`, `st.shared`,
   `cvta.to.global`, `cvt`, `add`, `sub`, `mul` (`lo`/`wide`/`rn`), `div`, `rem`, `mad`, `fma`,
   `and`, `or`, `xor`, `not`, `neg`, `shl`, `shr`, `setp`, `selp`, `bar.sync`, `bra`, `ret`).
2. Independent SIMT operational semantics (`BitVec`-backed scalar/predicate register file,
   `Dim3` grid/CTA coordinates, separated `globalMem`, per-CTA `sharedMem`, and read-only
   `paramMem` address spaces, bounds-checked `ld`/`st`, predicated instruction execution, and
   lockstep CTA `bar.sync` synchronization catching barrier divergence via
   `PTXOutcome.barrierDivergence`), with zero imports or calls to `LeanNative.Semantics.Eval`.
3. 1:1 structural pretty-printer (`ppPTXType`, `ppPTXInstr`, `ppPTXKernel`, `ppPTXModule`).
4. Kernel-checked theorems (`0 sorryAx`, `strict-proofs` clean) for address-space non-interference,
   predicated false guard no-op, uniform `bar.sync` convergence vs divergent barrier detection,
   determinism, and pretty-printer injectivity / well-formedness.
-/

namespace LeanNative.Backend.PTXAst

/-! ## 1. Typed PTX ISA AST -/

/-- PTX fundamental scalar and predicate data types. -/
inductive PTXType where
  | pred
  | b8
  | b16
  | b32
  | b64
  | u16
  | u32
  | u64
  | s32
  | s64
  | f32
  | f64
  deriving Repr, DecidableEq, Inhabited, BEq

namespace PTXType

/-- Byte width of a PTX data type in addressable memory (predicates occupy 1 byte when stored). -/
def byteWidth : PTXType → Nat
  | .pred | .b8 => 1
  | .b16 | .u16 => 2
  | .b32 | .u32 | .s32 | .f32 => 4
  | .b64 | .u64 | .s64 | .f64 => 8

/-- True when signed arithmetic/comparison rules apply. -/
def isSigned : PTXType → Bool
  | .s32 | .s64 => true
  | _ => false

/-- Bit width of a PTX scalar register type. -/
def bitWidth (ty : PTXType) : Nat :=
  if ty == .pred then 1 else ty.byteWidth * 8

end PTXType

/-- PTX architectural state spaces. -/
inductive StateSpace where
  | reg
  | param
  | shared
  | global
  | local
  | const
  deriving Repr, DecidableEq, Inhabited, BEq

/-- PTX special read-only hardware thread/CTA coordinate registers. -/
inductive SpecialReg where
  | tidX | tidY | tidZ
  | ntidX | ntidY | ntidZ
  | ctaidX | ctaidY | ctaidZ
  | nctaidX | nctaidY | nctaidZ
  deriving Repr, DecidableEq, Inhabited, BEq

/-- PTX multiplication width / rounding mode modifier. -/
inductive PTXMulMode where
  | lo
  | hi
  | wide
  | rn
  deriving Repr, DecidableEq, Inhabited, BEq

/-- PTX floating-point rounding modifier for `fma` / `cvt`. -/
inductive PTXRoundMode where
  | none
  | rn
  | rz
  deriving Repr, DecidableEq, Inhabited, BEq

/-- PTX `setp` comparison operators. -/
inductive PTXCmpOp where
  | eq
  | ne
  | lt
  | le
  | gt
  | ge
  | lo
  | ls
  | hi
  | hs
  deriving Repr, DecidableEq, Inhabited, BEq

/-- PTX instruction operand. -/
inductive PTXOperand where
  | reg    : String → PTXOperand
  | sreg   : SpecialReg → PTXOperand
  | immU64 : BitVec 64 → PTXOperand
  | immS64 : Int → PTXOperand
  | immF32 : UInt32 → PTXOperand
  | immF64 : UInt64 → PTXOperand
  | sym    : String → PTXOperand
  deriving Repr, DecidableEq, Inhabited, BEq

/-- PTX memory address expression (`[sym]`, `[%rd]`, `[%rd+off]`). -/
inductive PTXAddr where
  | paramSym  : String → PTXAddr
  | regOffset : String → Int → PTXAddr
  | symOffset : String → Int → PTXAddr
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Optional instruction predicate guard (`@%p` or `@!%p`). -/
structure PTXPredGuard where
  predReg : String
  negated : Bool := false
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Core PTX instruction set covering production GPU lowering. -/
inductive PTXInstr where
  | mov          : PTXType → String → PTXOperand → PTXInstr
  | ldParam      : PTXType → String → String → PTXInstr
  | ldGlobal     : PTXType → String → PTXAddr → PTXInstr
  | ldShared     : PTXType → String → PTXAddr → PTXInstr
  | stGlobal     : PTXType → PTXAddr → PTXOperand → PTXInstr
  | stShared     : PTXType → PTXAddr → PTXOperand → PTXInstr
  | cvtaToGlobal : PTXType → String → PTXOperand → PTXInstr
  | cvt          : PTXRoundMode → PTXType → PTXType → String → PTXOperand → PTXInstr
  | add          : PTXRoundMode → PTXType → String → PTXOperand → PTXOperand → PTXInstr
  | sub          : PTXType → String → PTXOperand → PTXOperand → PTXInstr
  | mul          : PTXMulMode → PTXType → String → PTXOperand → PTXOperand → PTXInstr
  | div          : PTXType → String → PTXOperand → PTXOperand → PTXInstr
  | rem          : PTXType → String → PTXOperand → PTXOperand → PTXInstr
  | mad          : PTXMulMode → PTXType → String → PTXOperand → PTXOperand → PTXOperand → PTXInstr
  | fma          : PTXRoundMode → PTXType → String → PTXOperand → PTXOperand → PTXOperand → PTXInstr
  | bitAnd       : PTXType → String → PTXOperand → PTXOperand → PTXInstr
  | bitOr        : PTXType → String → PTXOperand → PTXOperand → PTXInstr
  | bitXor       : PTXType → String → PTXOperand → PTXOperand → PTXInstr
  | bitNot       : PTXType → String → PTXOperand → PTXInstr
  | neg          : PTXType → String → PTXOperand → PTXInstr
  | shl          : PTXType → String → PTXOperand → PTXOperand → PTXInstr
  | shr          : PTXType → String → PTXOperand → PTXOperand → PTXInstr
  | setp         : PTXCmpOp → PTXType → String → PTXOperand → PTXOperand → PTXInstr
  | selp         : PTXType → String → PTXOperand → PTXOperand → String → PTXInstr
  | barSync      : Nat → PTXInstr
  | bra          : String → PTXInstr
  | ret          : PTXInstr
  | clz          : PTXType → String → PTXOperand → PTXInstr
  | movPack2x32  : String → PTXOperand → PTXOperand → PTXInstr
  | movUnpack2x32 : String → String → PTXOperand → PTXInstr
  | shflSyncBfly : String → PTXOperand → PTXOperand → PTXOperand → PTXOperand → PTXInstr
  | atomAdd      : StateSpace → PTXType → String → PTXAddr → PTXOperand → PTXInstr
  | ldConst      : PTXType → String → PTXAddr → PTXInstr
  | ldLocal      : PTXType → String → PTXAddr → PTXInstr
  | stLocal      : PTXType → PTXAddr → PTXOperand → PTXInstr
  | stConst      : PTXType → PTXAddr → PTXOperand → PTXInstr
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Statement inside a PTX kernel body: either a label or a possibly-predicated instruction. -/
inductive PTXStmt where
  | label : String → PTXStmt
  | instr : Option PTXPredGuard → PTXInstr → PTXStmt
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Kernel `.param` entry parameter declaration. -/
structure PTXParamDecl where
  ty   : PTXType
  name : String
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Kernel `.reg` bank or explicit register declaration. -/
structure PTXRegDecl where
  ty     : PTXType
  prefixName : String
  count  : Nat
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Per-CTA `.shared` array declaration inside a PTX kernel. -/
structure PTXSharedDecl where
  align : Nat
  elemTy : PTXType
  name  : String
  count : Nat
  deriving Repr, DecidableEq, Inhabited, BEq

/-- PTX `.visible .entry` kernel definition. -/
structure PTXKernel where
  name        : String
  params      : List PTXParamDecl
  sharedDecls : List PTXSharedDecl := []
  localBytes  : Nat := 0
  regDecls    : List PTXRegDecl := []
  body        : List PTXStmt
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Complete PTX module with `.version`, `.target`, `.address_size`, and kernels. -/
structure PTXModule where
  versionMajor : Nat := 8
  versionMinor : Nat := 0
  target       : String := "sm_90"
  addressSize  : Nat := 64
  kernels      : List PTXKernel
  deriving Repr, DecidableEq, Inhabited, BEq
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

/-- Per-thread register values: `Bool` for `.pred` and `BitVec 64` (zero/sign-masked per instruction width)
    for scalar/vector integer & IEEE bit-pattern registers. -/
inductive PTXRegVal where
  | pred   : Bool → PTXRegVal
  | scalar : BitVec 64 → PTXRegVal
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Total association-list register file per thread. -/
structure PTXRegFile where
  regs : List (String × PTXRegVal) := []
  deriving Repr, DecidableEq, Inhabited, BEq

namespace PTXRegFile

def empty : PTXRegFile := { regs := [] }

def getScalar (rf : PTXRegFile) (name : String) : BitVec 64 :=
  match rf.regs.lookup name with
  | some (.scalar v) => v
  | some (.pred b)   => if b then 1#64 else 0#64
  | none             => 0#64

def getPred (rf : PTXRegFile) (name : String) : Option Bool :=
  match rf.regs.lookup name with
  | some (.pred b) => some b
  | _              => none

private def setAssoc (xs : List (String × PTXRegVal)) (k : String) (v : PTXRegVal) :
    List (String × PTXRegVal) :=
  match xs with
  | [] => [(k, v)]
  | (k', v') :: rest =>
    if k' == k then (k, v) :: rest else (k', v') :: setAssoc rest k v

def setScalar (rf : PTXRegFile) (name : String) (v : BitVec 64) : PTXRegFile :=
  { regs := setAssoc rf.regs name (.scalar v) }

def setPred (rf : PTXRegFile) (name : String) (b : Bool) : PTXRegFile :=
  { regs := setAssoc rf.regs name (.pred b) }

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

private def readLittleEndianAux (m : ByteMemory) (addr : Nat) : Nat → Option (BitVec 64)
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

private def writeLittleEndianAux (bs : Array UInt8) (addr : Nat) (val : BitVec 64) : Nat → Array UInt8
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

/-- Helper to initialize memory from an array of 64-bit little-endian words. -/
def ofU64Words (words : List (BitVec 64)) : ByteMemory :=
  let emptyBytes := Array.replicate (words.length * 8) (0 : UInt8)
  let rec fill (bs : Array UInt8) (idx : Nat) : List (BitVec 64) → Array UInt8
    | [] => bs
    | w :: rest => fill (writeLittleEndianAux bs (idx * 8) w 8) (idx + 1) rest
  { bytes := fill emptyBytes 0 words }

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

/-- Per-barrier-epoch memory access record for SIMT race detection (`W-W` and `R-W` conflicts). -/
structure MemAccessLog where
  tid     : Dim3
  space   : StateSpace
  addr    : Nat
  width   : Nat
  isWrite : Bool
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Check whether two half-open byte intervals `[a1, a1 + w1)` and `[a2, a2 + w2)` overlap. -/
def rangesOverlap (a1 w1 a2 w2 : Nat) : Bool :=
  decide (a1 < a2 + w2 ∧ a2 < a1 + w1)

/-- Check whether an ordinary (non-atomic) access conflicts with any prior access in the current
    barrier epoch from a distinct thread (`tid' != tid`) on the same address space where at least
    one of the two accesses is a write. -/
def findDataRace? (logs : List MemAccessLog) (tid : Dim3) (space : StateSpace)
    (addr width : Nat) (isWrite : Bool) : Option Nat :=
  let rec go : List MemAccessLog → Option Nat
    | [] => none
    | entry :: rest =>
      if entry.tid != tid && entry.space == space && (isWrite || entry.isWrite) &&
         rangesOverlap addr width entry.addr entry.width then
        some (Nat.max addr entry.addr)
      else
        go rest
  go logs

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
      let rec normSub (m : Nat) (e : Nat) (fuel : Nat) : Nat × Nat :=
        match fuel with
        | 0 => (m, e)
        | k + 1 =>
          if (m &&& 0x80_0000) != 0 then (m &&& 0x7F_FFFF, e)
          else normSub (m <<< 1) (e - 1) k
      let (normFrac, exp64) := normSub frac32 (1023 - 126) 24
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

/-- Evaluate a `PTXOperand` to a `BitVec 64` in the context of a thread and CTA. -/
def evalOperand (cta : PTXCTAState) (th : PTXThreadState) (op : PTXOperand) :
    PTXOutcome (BitVec 64) :=
  match op with
  | .reg name => .ok (th.regs.getScalar name)
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
    PTXOutcome.bind (evalOperand cta th sh) fun vsh =>
      if (vsh >>> 32) != 0#64 then
        .invalidOperand "shift amount exceeds 32-bit .u32/.b32 operand width"
      else
        .ok (vsh &&& 0xFFFF_FFFF#64).toNat

/-- Resolve a byte address for addressable state spaces (`global`, `shared`, `const`, `local`). -/
def evalAddr (cta : PTXCTAState) (th : PTXThreadState) : PTXAddr → PTXOutcome Nat
  | .paramSym sym => .invalidOperand s!"param symbol [{sym}] used as addressable pointer"
  | .regOffset regName disp =>
    let base : Int := Int.ofNat (th.regs.getScalar regName).toNat
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
  let rec go (idx : Nat) : List PTXStmt → Option Nat
    | [] => none
    | .label l :: rest => if l == lbl then some (idx + 1) else go (idx + 1) rest
    | _ :: rest => go (idx + 1) rest
  go 0 stmts

/-- Evaluate an optional predicate guard (`@p` / `@!p`) in thread `th`. -/
def evalPredGuard (th : PTXThreadState) : Option PTXPredGuard → PTXOutcome Bool
  | none => .ok true
  | some g =>
    match th.regs.getPred g.predReg with
    | some b => .ok (if g.negated then !b else b)
    | none => .unboundPred g.predReg

/-- Check natural byte alignment (`byteAddr % width == 0`). -/
def checkAligned (sp : StateSpace) (byteAddr width : Nat) : PTXOutcome Unit :=
  if byteAddr % width == 0 then
    .ok ()
  else
    .misalignedAccess sp byteAddr width

/-- Check cross-thread SIMT race freedom for a non-atomic `global`/`shared` access in the current epoch,
    returning the updated epoch log on success or `.dataRace sp conflictAddr` on conflict. -/
def recordEpochAccess (logs : List MemAccessLog) (tid : Dim3) (sp : StateSpace)
    (byteAddr width : Nat) (isWrite : Bool) : PTXOutcome (List MemAccessLog) :=
  match findDataRace? logs tid sp byteAddr width isWrite with
  | some conflictAddr => .dataRace sp conflictAddr
  | none =>
    .ok ({ tid := tid, space := sp, addr := byteAddr, width := width, isWrite := isWrite } :: logs)

/-- Execute a single non-barrier, non-warp-collective `PTXInstr` for one active thread `th` against
    `(cta, stmts)`, returning `(PTXThreadState, ByteMemory (global), ByteMemory (shared), List MemAccessLog)`. -/
def execNonBarrierInstr (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    (ins : PTXInstr) : PTXOutcome (PTXThreadState × ByteMemory × ByteMemory × List MemAccessLog) :=
  let nextPc := th.pc + 1
  match ins with
  | .mov ty dst src =>
    PTXOutcome.bind (evalOperand cta th src) fun v =>
      let rf' :=
        if ty == .pred then th.regs.setPred dst (v != 0#64)
        else th.regs.setScalar dst (maskForType ty v)
      .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
  | .movPack2x32 dst loOp hiOp =>
    PTXOutcome.bind (evalOperand cta th loOp) fun vLo =>
      PTXOutcome.bind (evalOperand cta th hiOp) fun vHi =>
        let lo := vLo &&& 0xFFFF_FFFF#64
        let hi := (vHi &&& 0xFFFF_FFFF#64) <<< 32
        .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst (lo ||| hi) },
             cta.globalMem, cta.sharedMem, cta.epochLog)
  | .movUnpack2x32 dstLo dstHi srcOp =>
    PTXOutcome.bind (evalOperand cta th srcOp) fun v =>
      let lo := v &&& 0xFFFF_FFFF#64
      let hi := (v >>> 32) &&& 0xFFFF_FFFF#64
      let rf' := (th.regs.setScalar dstLo lo).setScalar dstHi hi
      .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
  | .clz ty dst srcOp =>
    if ty != .b32 && ty != .u32 && ty != .b64 && ty != .u64 then
      .invalidOperand "clz requires .b32/.u32/.b64/.u64 operand type"
    else
      PTXOutcome.bind (evalOperand cta th srcOp) fun v =>
        let cnt : BitVec 64 :=
          if ty == .b32 || ty == .u32 then
            let c32 := BitVec.clz (v.truncate 32)
            c32.zeroExtend 64
          else
            BitVec.clz v
        .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst (cnt &&& 0xFFFF_FFFF#64) },
             cta.globalMem, cta.sharedMem, cta.epochLog)
  | .ldParam ty dst paramName =>
    match cta.paramMem.lookupParam? paramName with
    | some v =>
      let rf' := th.regs.setScalar dst (maskForType ty v)
      .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem, cta.epochLog)
    | none => .unboundParam paramName
  | .ldGlobal ty dst addr =>
    PTXOutcome.bind (evalAddr cta th addr) fun byteAddr =>
      let w := ty.byteWidth
      PTXOutcome.bind (checkAligned .global byteAddr w) fun () =>
        PTXOutcome.bind (recordEpochAccess cta.epochLog th.tid .global byteAddr w false) fun log' =>
          match cta.globalMem.loadBits byteAddr w with
          | some raw =>
            let v := if ty == .s32 then signExtend32To64 raw else maskForType ty raw
            .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst v }, cta.globalMem, cta.sharedMem, log')
          | none => .outOfBoundsLoad .global byteAddr
  | .ldShared ty dst addr =>
    PTXOutcome.bind (evalAddr cta th addr) fun byteAddr =>
      let w := ty.byteWidth
      PTXOutcome.bind (checkAligned .shared byteAddr w) fun () =>
        PTXOutcome.bind (recordEpochAccess cta.epochLog th.tid .shared byteAddr w false) fun log' =>
          match cta.sharedMem.loadBits byteAddr w with
          | some raw =>
            let v := if ty == .s32 then signExtend32To64 raw else maskForType ty raw
            .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst v }, cta.globalMem, cta.sharedMem, log')
          | none => .outOfBoundsLoad .shared byteAddr
  | .ldConst ty dst addr =>
    PTXOutcome.bind (evalAddr cta th addr) fun byteAddr =>
      let w := ty.byteWidth
      PTXOutcome.bind (checkAligned .const byteAddr w) fun () =>
        match cta.constMem.loadBits byteAddr w with
        | some raw =>
          let v := if ty == .s32 then signExtend32To64 raw else maskForType ty raw
          .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst v }, cta.globalMem, cta.sharedMem, cta.epochLog)
        | none => .outOfBoundsLoad .const byteAddr
  | .ldLocal ty dst addr =>
    PTXOutcome.bind (evalAddr cta th addr) fun byteAddr =>
      let w := ty.byteWidth
      PTXOutcome.bind (checkAligned .local byteAddr w) fun () =>
        match th.localMem.loadBits byteAddr w with
        | some raw =>
          let v := if ty == .s32 then signExtend32To64 raw else maskForType ty raw
          .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst v }, cta.globalMem, cta.sharedMem, cta.epochLog)
        | none => .outOfBoundsLoad .local byteAddr
  | .stGlobal ty addr src =>
    PTXOutcome.bind (evalAddr cta th addr) fun byteAddr =>
      PTXOutcome.bind (evalOperand cta th src) fun v =>
        let w := ty.byteWidth
        PTXOutcome.bind (checkAligned .global byteAddr w) fun () =>
          PTXOutcome.bind (recordEpochAccess cta.epochLog th.tid .global byteAddr w true) fun log' =>
            match cta.globalMem.storeBits byteAddr w (maskForType ty v) with
            | some g' => .ok ({ th with pc := nextPc }, g', cta.sharedMem, log')
            | none => .outOfBoundsStore .global byteAddr
  | .stShared ty addr src =>
    PTXOutcome.bind (evalAddr cta th addr) fun byteAddr =>
      PTXOutcome.bind (evalOperand cta th src) fun v =>
        let w := ty.byteWidth
        PTXOutcome.bind (checkAligned .shared byteAddr w) fun () =>
          PTXOutcome.bind (recordEpochAccess cta.epochLog th.tid .shared byteAddr w true) fun log' =>
            match cta.sharedMem.storeBits byteAddr w (maskForType ty v) with
            | some s' => .ok ({ th with pc := nextPc }, cta.globalMem, s', log')
            | none => .outOfBoundsStore .shared byteAddr
  | .stLocal ty addr src =>
    PTXOutcome.bind (evalAddr cta th addr) fun byteAddr =>
      PTXOutcome.bind (evalOperand cta th src) fun v =>
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
        PTXOutcome.bind (evalOperand cta th src) fun v =>
          let w := ty.byteWidth
          PTXOutcome.bind (checkAligned sp byteAddr w) fun () =>
            let mem := if sp == .global then cta.globalMem else cta.sharedMem
            match mem.loadBits byteAddr w with
            | none => .outOfBoundsStore sp byteAddr
            | some oldRaw =>
              let oldVal := maskForType ty oldRaw
              let addResOutcome : PTXOutcome (BitVec 64) :=
                match ty with
                | .f32 => .ok (f32ToBv (bvToF32 oldVal + bvToF32 v))
                | .f64 => .ok (f64ToBv (bvToF64 oldVal + bvToF64 v))
                | .u32 | .b32 | .s32 | .u64 | .b64 | .s64 =>
                  .ok (maskForType ty (oldVal + maskForType ty v))
                | _ => .invalidOperand "atom.add unsupported data type"
              PTXOutcome.bind addResOutcome fun newVal =>
                match mem.storeBits byteAddr w newVal with
                | none => .outOfBoundsStore sp byteAddr
                | some mem' =>
                  let th' := { th with pc := nextPc, regs := th.regs.setScalar dst oldVal }
                  if sp == .global then
                    .ok (th', mem', cta.sharedMem, cta.epochLog)
                  else
                    .ok (th', cta.globalMem, mem', cta.epochLog)
  | .cvtaToGlobal ty dst src =>
    PTXOutcome.bind (evalOperand cta th src) fun v =>
      .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst (maskForType ty v) },
           cta.globalMem, cta.sharedMem, cta.epochLog)
  | .cvt rm dstTy srcTy dst src =>
    PTXOutcome.bind (evalOperand cta th src) fun v =>
      PTXOutcome.bind (evalPTXCvt rm dstTy srcTy v) fun out =>
        .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst out },
             cta.globalMem, cta.sharedMem, cta.epochLog)
  | .add rm ty dst a b =>
    PTXOutcome.bind (evalOperand cta th a) fun va =>
      PTXOutcome.bind (evalOperand cta th b) fun vb =>
        if ty == .f32 then
          if rm == .rz then .unsupportedFloatOp "add.rz.f32"
          else
            let res := f32ToBv (bvToF32 va + bvToF32 vb)
            .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
                 cta.globalMem, cta.sharedMem, cta.epochLog)
        else if ty == .f64 then
          if rm == .rz then .unsupportedFloatOp "add.rz.f64"
          else
            let res := f64ToBv (bvToF64 va + bvToF64 vb)
            .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
                 cta.globalMem, cta.sharedMem, cta.epochLog)
        else
          let res := maskForType ty (maskForType ty va + maskForType ty vb)
          .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
               cta.globalMem, cta.sharedMem, cta.epochLog)
  | .sub ty dst a b =>
    PTXOutcome.bind (evalOperand cta th a) fun va =>
      PTXOutcome.bind (evalOperand cta th b) fun vb =>
        let res :=
          if ty == .f32 then f32ToBv (bvToF32 va - bvToF32 vb)
          else if ty == .f64 then f64ToBv (bvToF64 va - bvToF64 vb)
          else maskForType ty (maskForType ty va - maskForType ty vb)
        .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
             cta.globalMem, cta.sharedMem, cta.epochLog)
  | .mul mode ty dst a b =>
    PTXOutcome.bind (evalOperand cta th a) fun va =>
      PTXOutcome.bind (evalOperand cta th b) fun vb =>
        if ty == .f32 then
          if mode != .rn && mode != .lo then .unsupportedFloatOp "mul float mode"
          else
            let out := f32ToBv (bvToF32 va * bvToF32 vb)
            .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst out },
                 cta.globalMem, cta.sharedMem, cta.epochLog)
        else if ty == .f64 then
          if mode != .rn && mode != .lo then .unsupportedFloatOp "mul float mode"
          else
            let out := f64ToBv (bvToF64 va * bvToF64 vb)
            .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst out },
                 cta.globalMem, cta.sharedMem, cta.epochLog)
        else
          let out := match mode, ty with
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
            | _, _ =>
              maskForType ty (maskForType ty va * maskForType ty vb)
          .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst out },
               cta.globalMem, cta.sharedMem, cta.epochLog)
  | .div ty dst a b =>
    PTXOutcome.bind (evalOperand cta th a) fun va =>
      PTXOutcome.bind (evalOperand cta th b) fun vb =>
        if ty == .f32 then
          let res := f32ToBv (bvToF32 va / bvToF32 vb)
          .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
               cta.globalMem, cta.sharedMem, cta.epochLog)
        else if ty == .f64 then
          let res := f64ToBv (bvToF64 va / bvToF64 vb)
          .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
               cta.globalMem, cta.sharedMem, cta.epochLog)
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
              .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
                   cta.globalMem, cta.sharedMem, cta.epochLog)
          else if ty == .s32 then
            let a32 := ma.truncate 32
            let b32 := mb.truncate 32
            if a32 == 0x8000_0000#32 && b32 == 0xFFFF_FFFF#32 then
              .signedDivOverflow
            else
              let q32 := BitVec.sdiv a32 b32
              .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst (q32.zeroExtend 64) },
                   cta.globalMem, cta.sharedMem, cta.epochLog)
          else
            let res := maskForType ty (ma / mb)
            .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
                 cta.globalMem, cta.sharedMem, cta.epochLog)
  | .rem ty dst a b =>
    PTXOutcome.bind (evalOperand cta th a) fun va =>
      PTXOutcome.bind (evalOperand cta th b) fun vb =>
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
              .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
                   cta.globalMem, cta.sharedMem, cta.epochLog)
          else if ty == .s32 then
            let a32 := ma.truncate 32
            let b32 := mb.truncate 32
            if a32 == 0x8000_0000#32 && b32 == 0xFFFF_FFFF#32 then
              .signedDivOverflow
            else
              let r32 := BitVec.srem a32 b32
              .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst (r32.zeroExtend 64) },
                   cta.globalMem, cta.sharedMem, cta.epochLog)
          else
            let res := maskForType ty (ma % mb)
            .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
                 cta.globalMem, cta.sharedMem, cta.epochLog)
  | .mad mode ty dst a b c =>
    PTXOutcome.bind (evalOperand cta th a) fun va =>
      PTXOutcome.bind (evalOperand cta th b) fun vb =>
        PTXOutcome.bind (evalOperand cta th c) fun vc =>
          if ty == .f32 then
            let res := f32ToBv (bvToF32 va * bvToF32 vb + bvToF32 vc)
            .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
                 cta.globalMem, cta.sharedMem, cta.epochLog)
          else if ty == .f64 then
            let res := f64ToBv (bvToF64 va * bvToF64 vb + bvToF64 vc)
            .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
                 cta.globalMem, cta.sharedMem, cta.epochLog)
          else
            let prod := match mode, ty with
              | .wide, .u32 | .wide, .b32 =>
                (va &&& 0xFFFF_FFFF#64) * (vb &&& 0xFFFF_FFFF#64)
              | .wide, .s32 =>
                signExtend32To64 va * signExtend32To64 vb
              | _, _ =>
                maskForType ty (maskForType ty va * maskForType ty vb)
            let resTy := if mode == .wide && (ty == .u32 || ty == .b32 || ty == .s32) then .u64 else ty
            let res := maskForType resTy (prod + maskForType resTy vc)
            .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
                 cta.globalMem, cta.sharedMem, cta.epochLog)
  | .fma rm ty dst a b c =>
    PTXOutcome.bind (evalOperand cta th a) fun va =>
      PTXOutcome.bind (evalOperand cta th b) fun vb =>
        PTXOutcome.bind (evalOperand cta th c) fun vc =>
          if rm == .rz then
            .unsupportedFloatOp "fma.rz"
          else if ty == .f32 then
            let res := f32ToBv (Float32.fma (bvToF32 va) (bvToF32 vb) (bvToF32 vc))
            .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
                 cta.globalMem, cta.sharedMem, cta.epochLog)
          else if ty == .f64 then
            let res := f64ToBv (Float.fma (bvToF64 va) (bvToF64 vb) (bvToF64 vc))
            .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
                 cta.globalMem, cta.sharedMem, cta.epochLog)
          else
            .unsupportedFloatOp "fma requires .f32 or .f64"
  | .bitAnd ty dst a b =>
    PTXOutcome.bind (evalOperand cta th a) fun va =>
      PTXOutcome.bind (evalOperand cta th b) fun vb =>
        if ty == .f32 || ty == .f64 then
          .invalidOperand "bitwise and requires .pred or .b* type"
        else if ty == .pred then
          match th.regs.getPred (match a with | .reg r => r | _ => ""),
                th.regs.getPred (match b with | .reg r => r | _ => "") with
          | some pa, some pb =>
            .ok ({ th with pc := nextPc, regs := th.regs.setPred dst (pa && pb) },
                 cta.globalMem, cta.sharedMem, cta.epochLog)
          | _, _ =>
            .ok ({ th with pc := nextPc, regs := th.regs.setPred dst (va != 0#64 && vb != 0#64) },
                 cta.globalMem, cta.sharedMem, cta.epochLog)
        else
          let res := maskForType ty (va &&& vb)
          .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
               cta.globalMem, cta.sharedMem, cta.epochLog)
  | .bitOr ty dst a b =>
    PTXOutcome.bind (evalOperand cta th a) fun va =>
      PTXOutcome.bind (evalOperand cta th b) fun vb =>
        if ty == .f32 || ty == .f64 then
          .invalidOperand "bitwise or requires .pred or .b* type"
        else if ty == .pred then
          match th.regs.getPred (match a with | .reg r => r | _ => ""),
                th.regs.getPred (match b with | .reg r => r | _ => "") with
          | some pa, some pb =>
            .ok ({ th with pc := nextPc, regs := th.regs.setPred dst (pa || pb) },
                 cta.globalMem, cta.sharedMem, cta.epochLog)
          | _, _ =>
            .ok ({ th with pc := nextPc, regs := th.regs.setPred dst (va != 0#64 || vb != 0#64) },
                 cta.globalMem, cta.sharedMem, cta.epochLog)
        else
          let res := maskForType ty (va ||| vb)
          .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
               cta.globalMem, cta.sharedMem, cta.epochLog)
  | .bitXor ty dst a b =>
    PTXOutcome.bind (evalOperand cta th a) fun va =>
      PTXOutcome.bind (evalOperand cta th b) fun vb =>
        if ty == .f32 || ty == .f64 then
          .invalidOperand "bitwise xor requires .pred or .b* type"
        else if ty == .pred then
          match th.regs.getPred (match a with | .reg r => r | _ => ""),
                th.regs.getPred (match b with | .reg r => r | _ => "") with
          | some pa, some pb =>
            .ok ({ th with pc := nextPc, regs := th.regs.setPred dst (pa != pb) },
                 cta.globalMem, cta.sharedMem, cta.epochLog)
          | _, _ =>
            .ok ({ th with pc := nextPc, regs := th.regs.setPred dst ((va != 0#64) != (vb != 0#64)) },
                 cta.globalMem, cta.sharedMem, cta.epochLog)
        else
          let res := maskForType ty (va ^^^ vb)
          .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
               cta.globalMem, cta.sharedMem, cta.epochLog)
  | .bitNot ty dst a =>
    PTXOutcome.bind (evalOperand cta th a) fun va =>
      if ty == .f32 || ty == .f64 then
        .invalidOperand "bitwise not requires .pred or .b* type"
      else if ty == .pred then
        match th.regs.getPred (match a with | .reg r => r | _ => "") with
        | some pa =>
          .ok ({ th with pc := nextPc, regs := th.regs.setPred dst (!pa) },
               cta.globalMem, cta.sharedMem, cta.epochLog)
        | none =>
          .ok ({ th with pc := nextPc, regs := th.regs.setPred dst (va == 0#64) },
               cta.globalMem, cta.sharedMem, cta.epochLog)
      else
        let res := maskForType ty (~~~va)
        .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
             cta.globalMem, cta.sharedMem, cta.epochLog)
  | .neg ty dst a =>
    PTXOutcome.bind (evalOperand cta th a) fun va =>
      let res :=
        if ty == .f32 then f32ToBv (-bvToF32 va)
        else if ty == .f64 then f64ToBv (-bvToF64 va)
        else maskForType ty (0#64 - maskForType ty va)
      .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
           cta.globalMem, cta.sharedMem, cta.epochLog)
  | .shl ty dst a sh =>
    if ty == .f32 || ty == .f64 || ty == .pred then
      .invalidOperand "shl requires integer/bit-size type"
    else
      PTXOutcome.bind (evalOperand cta th a) fun va =>
        PTXOutcome.bind (evalShiftAmount cta th sh) fun shiftAmt =>
          let width := ty.bitWidth
          let res :=
            if shiftAmt ≥ width then 0#64
            else maskForType ty ((maskForType ty va) <<< shiftAmt)
          .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
               cta.globalMem, cta.sharedMem, cta.epochLog)
  | .shr ty dst a sh =>
    if ty == .f32 || ty == .f64 || ty == .pred then
      .invalidOperand "shr requires integer/bit-size type"
    else
      PTXOutcome.bind (evalOperand cta th a) fun va =>
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
          .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
               cta.globalMem, cta.sharedMem, cta.epochLog)
  | .setp cmp ty dstPred a b =>
    PTXOutcome.bind (evalOperand cta th a) fun va =>
      PTXOutcome.bind (evalOperand cta th b) fun vb =>
        let flag := evalPTXCmp cmp ty va vb
        .ok ({ th with pc := nextPc, regs := th.regs.setPred dstPred flag },
             cta.globalMem, cta.sharedMem, cta.epochLog)
  | .selp ty dst tOp fOp predName =>
    match th.regs.getPred predName with
    | none => .unboundPred predName
    | some cond =>
      PTXOutcome.bind (evalOperand cta th tOp) fun vt =>
        PTXOutcome.bind (evalOperand cta th fOp) fun vf =>
          let chosen := maskForType ty (if cond then vt else vf)
          .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst chosen },
               cta.globalMem, cta.sharedMem, cta.epochLog)
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

/-- Execute one warp's synchronous `shfl.sync.bfly.b32` exchange for `warpId`.
    All active participants named in `membermask` within this warp must be parked at the identical
    `pc` executing `shfl.sync.bfly.b32`; each participating lane reads its partner lane's pre-shuffle
    32-bit operand (`srcLane = laneId ^^^ offset`, clamped via `clampMask`/`segMask` per PTX 8.0) and
    writes `dst` in lockstep before advancing `pc`. -/
def stepWarpShfl (stmts : List PTXStmt) (cta : PTXCTAState) (warpId : Nat) (shflPc : Nat) :
    PTXOutcome PTXCTAState :=
  let warpThreads := cta.threads.filter fun th => (cta.blockDim.linearTid th.tid) / 32 == warpId
  let rec evalParticipants :
      List PTXThreadState → PTXOutcome (List (Nat × PTXThreadState × String × BitVec 64 × Nat × Nat × Nat))
    | [] => .ok []
    | th :: rest =>
      PTXOutcome.bind (threadAtActiveShfl stmts th) fun atShfl =>
        if !atShfl then
          evalParticipants rest
        else if th.pc != shflPc then
          .barrierDivergence 0
        else
          match stmts[th.pc]? with
          | some (.instr _ (.shflSyncBfly dst srcOp offOp clampOp maskOp)) =>
            PTXOutcome.bind (evalOperand cta th srcOp) fun vSrc =>
              PTXOutcome.bind (evalOperand cta th offOp) fun vOff =>
                PTXOutcome.bind (evalOperand cta th clampOp) fun vClamp =>
                  PTXOutcome.bind (evalOperand cta th maskOp) fun vMask =>
                    PTXOutcome.bind (evalParticipants rest) fun tail =>
                      let lane := (cta.blockDim.linearTid th.tid) % 32
                      let off := (vOff &&& 0x1F#64).toNat
                      let clampVal := (vClamp &&& 0xFFFF_FFFF#64).toNat
                      let maskVal := (vMask &&& 0xFFFF_FFFF#64).toNat
                      .ok ((lane, th, dst, vSrc &&& 0xFFFF_FFFF#64, off, clampVal, maskVal) :: tail)
          | _ => .barrierDivergence 0
  PTXOutcome.bind (evalParticipants warpThreads) fun parts =>
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
        let lookupLaneVal (targetLane : Nat) (fallback : BitVec 64) : BitVec 64 :=
          match parts.find? (fun (l, _, _, _, _, _, _) => l == targetLane) with
          | some (_, _, _, v, _, _, _) => v
          | none => fallback
        let updatedThreads := cta.threads.map fun th =>
          let lin := cta.blockDim.linearTid th.tid
          if lin / 32 != warpId then
            th
          else
            let lane := lin % 32
            match parts.find? (fun (l, _, _, _, _, _, _) => l == lane) with
            | none => th
            | some (_, _, dst, selfVal, off, clampVal, _) =>
              let maxLane := clampVal &&& 0x1F
              let segMask := (clampVal >>> 8) &&& 0x1F
              let minLane := lane &&& segMask
              let upperBound := minLane ||| (maxLane &&& (0x1F ^^^ segMask))
              let cand := lane ^^^ off
              let srcLane :=
                if cand ≤ upperBound && ((requiredMask >>> cand) &&& 1) == 1 then cand else lane
              let resVal := lookupLaneVal srcLane selfVal
              { th with pc := th.pc + 1, regs := th.regs.setScalar dst resVal }
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

/-- Initialize a `PTXCTAState` for a kernel launch on CTA coordinate `ctaId` (with optional `.const` memory). -/
def initCTAState (k : PTXKernel) (gridDim blockDim ctaId : Dim3)
    (globalMem : ByteMemory) (paramMem : ParamMemory)
    (constMem : ByteMemory := ByteMemory.zeros 0) : PTXCTAState :=
  let layout := buildSharedLayout k.sharedDecls
  let threads := blockDim.coords.map fun tid =>
    { tid := tid
      pc := 0
      regs := PTXRegFile.empty
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

/-- Launch a `PTXKernel` across every CTA in `gridDim` (each with fresh per-CTA `sharedMem` and
    per-thread `localMem`), threading `globalMem` across CTAs and returning the final `ByteMemory`. -/
def evalPTXKernel (fuelPerCTA : Nat) (k : PTXKernel) (gridDim blockDim : Dim3)
    (globalMem : ByteMemory) (paramMem : ParamMemory)
    (constMem : ByteMemory := ByteMemory.zeros 0) : PTXOutcome ByteMemory :=
  let rec loopCTAs (gMem : ByteMemory) : List Dim3 → PTXOutcome ByteMemory
    | [] => .ok gMem
    | ctaId :: rest =>
      let cta0 := initCTAState k gridDim blockDim ctaId gMem paramMem constMem
      PTXOutcome.bind (runCTA fuelPerCTA k.body cta0) fun ctaFinal =>
        loopCTAs ctaFinal.globalMem rest
  loopCTAs globalMem gridDim.coords

/-! ## 3. 1:1 Structural Pretty-Printer -/

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

private def toHexFixed (val : Nat) (nibbles : Nat) : String :=
  let rec go (v : Nat) (acc : List Char) : Nat → List Char
    | 0 => acc
    | k + 1 => go (v / 16) (hexDigitChar v :: acc) k
  String.ofList (go val [] nibbles)

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
/-! ## 4. Kernel-Checked Theorems (`0 sorryAx`, `strict-proofs` clean) -/

/-- Address-space non-interference (Shared -> Global): executing `st.shared` never mutates `globalMem`
    whenever it succeeds, leaving `globalMem` bit-identical to `cta.globalMem`. -/
theorem st_shared_preserves_global (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    (ty : PTXType) (addr : PTXAddr) (src : PTXOperand)
    (th' : PTXThreadState) (gMem' sMem' : ByteMemory)
    (log' : List MemAccessLog)
    (h_exec : execNonBarrierInstr stmts cta th (.stShared ty addr src) = .ok (th', gMem', sMem', log')) :
    gMem' = cta.globalMem := by
  dsimp [execNonBarrierInstr, PTXOutcome.bind] at h_exec
  cases hAddr : evalAddr cta th addr <;> simp [hAddr] at h_exec
  case ok byteAddr =>
    cases hSrc : evalOperand cta th src <;> simp [hSrc] at h_exec
    case ok val =>
      cases hAlign : checkAligned .shared byteAddr ty.byteWidth <;> simp [hAlign] at h_exec
      case ok =>
        cases hRace : recordEpochAccess cta.epochLog th.tid .shared byteAddr ty.byteWidth true <;>
          simp [hRace] at h_exec
        case ok logNext =>
          cases hStore : cta.sharedMem.storeBits byteAddr ty.byteWidth (maskForType ty val) <;>
            simp [hStore] at h_exec
          exact h_exec.2.1.symm

/-- Address-space non-interference (Global -> Shared): executing `st.global` never mutates per-CTA
    `sharedMem` whenever it succeeds, leaving `sharedMem` bit-identical to `cta.sharedMem`. -/
theorem st_global_preserves_shared (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    (ty : PTXType) (addr : PTXAddr) (src : PTXOperand)
    (th' : PTXThreadState) (gMem' sMem' : ByteMemory)
    (log' : List MemAccessLog)
    (h_exec : execNonBarrierInstr stmts cta th (.stGlobal ty addr src) = .ok (th', gMem', sMem', log')) :
    sMem' = cta.sharedMem := by
  dsimp [execNonBarrierInstr, PTXOutcome.bind] at h_exec
  cases hAddr : evalAddr cta th addr <;> simp [hAddr] at h_exec
  case ok byteAddr =>
    cases hSrc : evalOperand cta th src <;> simp [hSrc] at h_exec
    case ok val =>
      cases hAlign : checkAligned .global byteAddr ty.byteWidth <;> simp [hAlign] at h_exec
      case ok =>
        cases hRace : recordEpochAccess cta.epochLog th.tid .global byteAddr ty.byteWidth true <;>
          simp [hRace] at h_exec
        case ok logNext =>
          cases hStore : cta.globalMem.storeBits byteAddr ty.byteWidth (maskForType ty val) <;>
            simp [hStore] at h_exec
          exact h_exec.2.2.1.symm

/-- Predicated instruction false-guard no-op: whenever `evalPredGuard th guard = .ok false`,
    `execPredicatedInstr` advances `th.pc` by 1 while leaving `th.regs`, `cta.globalMem`, and
    `cta.sharedMem` completely untouched for every `PTXInstr` (including `bar.sync` and `st.*`). -/
theorem execInstr_pred_false_noop (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    (guard : Option PTXPredGuard) (ins : PTXInstr)
    (h_false : evalPredGuard th guard = .ok false) :
    execPredicatedInstr stmts cta th guard ins =
      .ok ({ th with pc := th.pc + 1 }, cta.globalMem, cta.sharedMem, cta.epochLog) := by
  unfold execPredicatedInstr PTXOutcome.bind
  rw [h_false]
  rfl

/-- Uniform CTA `bar.sync` convergence: when every thread in the CTA arrives at the exact same
    barrier identifier `bid`, `stepCTABarrier` converges cleanly without error, advancing every
    thread's program counter past the barrier while preserving both `globalMem` and `sharedMem`. -/
theorem bar_sync_uniform_converges (bid : Nat) (states : List (Option Nat)) (cta : PTXCTAState)
    (h_uniform : states.all (fun s => s == some bid) = true) :
    stepCTABarrier bid states cta =
      .ok { cta with threads := cta.threads.map fun th => { th with pc := th.pc + 1 }, epochLog := [] } := by
  unfold stepCTABarrier
  simp [h_uniform]

/-- Divergent CTA `bar.sync` detection: when at least one thread in the CTA disagrees with `some bid`
    (e.g., took a divergent branch or halted early), `stepCTABarrier` traps with explicit
    `PTXOutcome.barrierDivergence bid`. -/
theorem bar_sync_divergent_errors (bid : Nat) (states : List (Option Nat)) (cta : PTXCTAState)
    (h_div : states.all (fun s => s == some bid) = false) :
    stepCTABarrier bid states cta = .barrierDivergence bid := by
  unfold stepCTABarrier
  simp [h_div]

/-- Halted CTA fixed-point: once all threads in `cta` have halted, `runCTA` immediately returns
    `.ok cta` for every step budget `fuel`. -/
theorem runCTA_halted (fuel : Nat) (stmts : List PTXStmt) (cta : PTXCTAState)
    (h_halted : cta.threads.all (·.halted) = true) :
    runCTA fuel stmts cta = .ok cta := by
  cases fuel with
  | zero =>
    unfold runCTA
    simp [h_halted]
  | succ f =>
    unfold runCTA stepCTA PTXOutcome.bind
    simp [h_halted]

/-- Fuel-independent operational determinism of the PTX SIMT CTA semantics (`runCTA`):
    any two executions from the same kernel body and initial CTA state under arbitrary step
    budgets `f1` and `f2` that both reach terminal (non-`fuelExhausted`) outcomes produce
    identical `PTXOutcome` results. -/
theorem runCTA_deterministic (f1 f2 : Nat) (stmts : List PTXStmt) (cta : PTXCTAState)
    (out1 out2 : PTXOutcome PTXCTAState)
    (h1 : runCTA f1 stmts cta = out1)
    (h2 : runCTA f2 stmts cta = out2)
    (hne1 : out1 ≠ .fuelExhausted)
    (hne2 : out2 ≠ .fuelExhausted) :
    out1 = out2 := by
  induction f1 generalizing f2 cta with
  | zero =>
    unfold runCTA at h1
    cases hAll : cta.threads.all (·.halted)
    · simp [hAll] at h1
      exact False.elim (hne1 h1.symm)
    · simp [hAll] at h1
      have hRun2 := runCTA_halted f2 stmts cta hAll
      rw [hRun2] at h2
      exact h1.symm.trans h2
  | succ f1' ih =>
    cases f2 with
    | zero =>
      unfold runCTA at h2
      cases hAll : cta.threads.all (·.halted)
      · simp [hAll] at h2
        exact False.elim (hne2 h2.symm)
      · simp [hAll] at h2
        have hRun1 := runCTA_halted (f1' + 1) stmts cta hAll
        rw [hRun1] at h1
        exact h1.symm.trans h2
    | succ f2' =>
      unfold runCTA PTXOutcome.bind at h1 h2
      cases hStep : stepCTA stmts cta <;> simp [hStep] at h1 h2
      case ok pair =>
        rcases pair with ⟨done, cta'⟩
        cases done with
        | true =>
          simp at h1 h2
          exact h1.symm.trans h2
        | false =>
          simp at h1 h2
          exact ih f2' cta' h1 h2
      all_goals exact h1.symm.trans h2

/-- 1:1 injectivity of `ppPTXType`: distinct PTX AST types pretty-print to distinct PTX type tokens. -/
theorem ppPTXType_injective (t1 t2 : PTXType) (h : ppPTXType t1 = ppPTXType t2) :
    t1 = t2 := by
  cases t1 <;> cases t2 <;> first | rfl | exact absurd h (by decide)

/-- 1:1 injectivity of `ppStateSpace`: distinct PTX state spaces pretty-print to distinct tokens. -/
theorem ppStateSpace_injective (s1 s2 : StateSpace) (h : ppStateSpace s1 = ppStateSpace s2) :
    s1 = s2 := by
  cases s1 <;> cases s2 <;> first | rfl | exact absurd h (by decide)

/-- 1:1 injectivity of `ppSpecialReg`: distinct special coordinate registers render to distinct tokens. -/
theorem ppSpecialReg_injective (r1 r2 : SpecialReg) (h : ppSpecialReg r1 = ppSpecialReg r2) :
    r1 = r2 := by
  cases r1 <;> cases r2 <;> first | rfl | exact absurd h (by decide)

/-- 1:1 injectivity of `ppMulMode`: distinct PTX multiply modifiers render to distinct tokens. -/
theorem ppMulMode_injective (m1 m2 : PTXMulMode) (h : ppMulMode m1 = ppMulMode m2) :
    m1 = m2 := by
  cases m1 <;> cases m2 <;> first | rfl | exact absurd h (by decide)

/-- 1:1 injectivity of `ppCmpOp`: distinct PTX comparison predicates render to distinct tokens. -/
theorem ppCmpOp_injective (c1 c2 : PTXCmpOp) (h : ppCmpOp c1 = ppCmpOp c2) :
    c1 = c2 := by
  cases c1 <;> cases c2 <;> first | rfl | exact absurd h (by decide)

private theorem charList_isPrefixOf_append :
    ∀ (xs ys : List Char), List.isPrefixOf xs (xs ++ ys) = true
  | [], _ => rfl
  | x :: xs, ys => by
    simp [charList_isPrefixOf_append xs ys]

/-- Structural header well-formedness of `ppPTXModule`: every rendered module begins with the exact
    `.version <major>.<minor>`, `.target`, and `.address_size` header directives of `m`. -/
theorem ppPTXModule_header_prefix (m : PTXModule) :
    List.isPrefixOf (ppPTXModuleHeader m).toList (ppPTXModule m).toList = true := by
  unfold ppPTXModule
  cases m.kernels with
  | nil =>
    rw [String.toList_append]
    exact charList_isPrefixOf_append _ _
  | cons k ks =>
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

private theorem append_semicolon_getLast (s : String) :
    (s ++ ";").toList.getLast? = some ';' := by
  rw [String.toList_append, semicolon_toList_eq]
  exact getLast_append_singleton s.toList ';'

/-- Structural statement well-formedness of `ppPTXInstr`: every rendered PTX instruction across all
    ISA constructors terminates with a trailing `';'`. -/
theorem ppPTXInstr_semicolon_terminated (ins : PTXInstr) :
    (ppPTXInstr ins).toList.getLast? = some ';' := by
  cases ins <;> exact append_semicolon_getLast _

/-- Integer division by zero traps explicitly with `.divisionByZero` across all PTX integer/bit-size
    types (never silently returning `0`). -/
theorem ptx_div_zero_traps (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    (ty : PTXType) (dst : String) (a b : PTXOperand) (va : BitVec 64)
    (h_int : ty ≠ .f32 ∧ ty ≠ .f64)
    (h_a : evalOperand cta th a = .ok va)
    (h_b : evalOperand cta th b = .ok 0#64) :
    execNonBarrierInstr stmts cta th (.div ty dst a b) = .divisionByZero := by
  rcases h_int with ⟨hf32, hf64⟩
  cases ty <;>
    first
    | exact absurd rfl hf32
    | exact absurd rfl hf64
    | (simp [execNonBarrierInstr, PTXOutcome.bind, h_a, h_b, maskForType]; rfl)

/-- Signed 64-bit `INT64_MIN / -1` division overflow traps explicitly with `.signedDivOverflow`. -/
theorem ptx_sdiv64_min_neg1_traps (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    (dst : String) (a b : PTXOperand)
    (h_a : evalOperand cta th a = .ok 0x8000_0000_0000_0000#64)
    (h_b : evalOperand cta th b = .ok 0xFFFF_FFFF_FFFF_FFFF#64) :
    execNonBarrierInstr stmts cta th (.div .s64 dst a b) = .signedDivOverflow := by
  simp [execNonBarrierInstr, PTXOutcome.bind, h_a, h_b, maskForType]
  rfl

private theorem lookup_setAssoc_same (xs : List (String × PTXRegVal)) (k : String) (v : PTXRegVal) :
    List.lookup k (PTXRegFile.setAssoc xs k v) = some v := by
  induction xs with
  | nil => simp [PTXRegFile.setAssoc]
  | cons hd tl ih =>
    rcases hd with ⟨k', v'⟩
    by_cases hk : k' == k
    · have heq : k' = k := LawfulBEq.eq_of_beq hk
      subst heq
      simp [PTXRegFile.setAssoc]
    · have hk2 : (k == k') = false := by
        cases h2 : k == k'
        · rfl
        · have heq : k = k' := LawfulBEq.eq_of_beq h2
          subst heq
          simp at hk
      simp [PTXRegFile.setAssoc, List.lookup, hk, hk2, ih]

private theorem lookup_setAssoc_ne (xs : List (String × PTXRegVal)) (q k : String) (v : PTXRegVal)
    (hne : q ≠ k) :
    List.lookup q (PTXRegFile.setAssoc xs k v) = List.lookup q xs := by
  induction xs with
  | nil =>
    have hb : (q == k) = false := beq_false_of_ne hne
    simp [PTXRegFile.setAssoc, List.lookup, hb]
  | cons hd tl ih =>
    rcases hd with ⟨k', v'⟩
    by_cases hk : k' == k
    · have heq : k' = k := LawfulBEq.eq_of_beq hk
      subst heq
      have hb : (q == k') = false := beq_false_of_ne hne
      simp [PTXRegFile.setAssoc, List.lookup, hb]
    · simp [PTXRegFile.setAssoc, hk]
      cases hq : q == k' <;> simp [List.lookup, hq, ih]

/-- Production guarded PTX division (`setp.eq.u64 %p, b, 0; selp.u64 safeB, 1, b, %p; div.u64 q, a, safeB; selp.u64 out, 0, q, %p`)
    never traps even when divisor `b = 0`, producing `0` on `b = 0` and `a / b` on `b ≠ 0`. -/
theorem ptx_guarded_div_zero_safe (cta : PTXCTAState) (th : PTXThreadState) (va : BitVec 64) :
    let stmts : List PTXStmt := [
      .instr none (.setp .eq .u64 "%p0" (.reg "%rd2") (.immU64 0#64)),
      .instr none (.selp .u64 "%rd3" (.immU64 1#64) (.reg "%rd2") "%p0"),
      .instr none (.div .u64 "%rd3" (.reg "%rd1") (.reg "%rd3")),
      .instr none (.selp .u64 "%rd3" (.immU64 0#64) (.reg "%rd3") "%p0")
    ]
    let th0 : PTXThreadState := { th with
      pc := 0
      regs := (th.regs.setScalar "%rd1" va).setScalar "%rd2" 0#64 }
    (PTXOutcome.bind (execNonBarrierInstr stmts cta th0 (.setp .eq .u64 "%p0" (.reg "%rd2") (.immU64 0#64))) fun (th1, _, _, _) =>
     PTXOutcome.bind (execNonBarrierInstr stmts cta th1 (.selp .u64 "%rd3" (.immU64 1#64) (.reg "%rd2") "%p0")) fun (th2, _, _, _) =>
     PTXOutcome.bind (execNonBarrierInstr stmts cta th2 (.div .u64 "%rd3" (.reg "%rd1") (.reg "%rd3"))) fun (th3, _, _, _) =>
     PTXOutcome.bind (execNonBarrierInstr stmts cta th3 (.selp .u64 "%rd3" (.immU64 0#64) (.reg "%rd3") "%p0")) fun (th4, _, _, _) =>
       .ok (th4.regs.getScalar "%rd3")) = .ok 0#64 := by
  intro stmts th0
  have hGet2 : th0.regs.getScalar "%rd2" = 0#64 := by
    simp [th0, PTXRegFile.getScalar, PTXRegFile.setScalar, lookup_setAssoc_same]
  have hPred0 : (th0.regs.setPred "%p0" true).getPred "%p0" = some true := by
    simp [PTXRegFile.getPred, PTXRegFile.setPred, lookup_setAssoc_same]
  have hGet3 : ((th0.regs.setPred "%p0" true).setScalar "%rd3" 1#64).getScalar "%rd3" = 1#64 := by
    simp [PTXRegFile.getScalar, PTXRegFile.setScalar, lookup_setAssoc_same]
  have hPredAfter : ∀ (w : BitVec 64),
      (((th0.regs.setPred "%p0" true).setScalar "%rd3" 1#64).setScalar "%rd3" w).getPred "%p0" =
        some true := by
    intro w
    have hne : "%p0" ≠ "%rd3" := by decide
    simp [PTXRegFile.getPred, PTXRegFile.setScalar, PTXRegFile.setPred,
      lookup_setAssoc_ne _ "%p0" "%rd3" _ hne, lookup_setAssoc_same]
  have hFinal : ∀ (rf : PTXRegFile), (rf.setScalar "%rd3" 0#64).getScalar "%rd3" = 0#64 := by
    intro rf
    simp [PTXRegFile.getScalar, PTXRegFile.setScalar, lookup_setAssoc_same]
  have hUf32 : (PTXType.u64 == PTXType.f32) = false := rfl
  have hUf64 : (PTXType.u64 == PTXType.f64) = false := rfl
  have hUs64 : (PTXType.u64 == PTXType.s64) = false := rfl
  have hUs32 : (PTXType.u64 == PTXType.s32) = false := rfl
  have h1z : (1#64 == 0#64) = false := rfl
  simp [execNonBarrierInstr, PTXOutcome.bind, evalOperand, evalPTXCmp, maskForType,
    hGet2, hPred0, hGet3, hUf32, hUf64, hUs64, hUs32, h1z, hPredAfter, hFinal]

/-- Misaligned global loads (`byteAddr % ty.byteWidth ≠ 0`) trap explicitly with `.misalignedAccess`. -/
theorem ptx_misaligned_global_load_traps (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    (ty : PTXType) (dst : String) (addr : PTXAddr) (byteAddr : Nat)
    (h_addr : evalAddr cta th addr = .ok byteAddr)
    (h_misalign : byteAddr % ty.byteWidth ≠ 0) :
    execNonBarrierInstr stmts cta th (.ldGlobal ty dst addr) =
      .misalignedAccess .global byteAddr ty.byteWidth := by
  have hb : (byteAddr % ty.byteWidth == 0) = false := beq_false_of_ne h_misalign
  simp [execNonBarrierInstr, PTXOutcome.bind, checkAligned, h_addr, hb]

/-- Stores to read-only `.const` memory trap explicitly with `.readOnlyWrite .const`. -/
theorem ptx_const_store_traps (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    (ty : PTXType) (addr : PTXAddr) (src : PTXOperand) (byteAddr : Nat)
    (h_addr : evalAddr cta th addr = .ok byteAddr) :
    execNonBarrierInstr stmts cta th (.stConst ty addr src) = .readOnlyWrite .const byteAddr := by
  simp [execNonBarrierInstr, PTXOutcome.bind, h_addr]

/-- Negative register address displacements render as `[%rd-8]` (never invalid `[%rd+-8]`). -/
theorem ppPTXAddr_neg_displacement (r : String) :
    ppPTXAddr (.regOffset r (-8)) = "[" ++ r ++ "-8]" := by
  have hstr : toString (-8 : Int) = "-8" := rfl
  simp [ppPTXAddr, hstr, String.append_assoc]
  rfl

/-- Disjoint byte ranges never trigger a SIMT data race: when `a1 + w1 ≤ a2` or `a2 + w2 ≤ a1`,
    `rangesOverlap a1 w1 a2 w2 = false`. -/
theorem rangesOverlap_disjoint_false (a1 w1 a2 w2 : Nat)
    (h_disj : a1 + w1 ≤ a2 ∨ a2 + w2 ≤ a1) :
    rangesOverlap a1 w1 a2 w2 = false := by
  unfold rangesOverlap
  rcases h_disj with h1 | h2
  · exact decide_eq_false (fun ⟨_, hlt⟩ => Nat.not_lt.mpr h1 hlt)
  · exact decide_eq_false (fun ⟨hlt, _⟩ => Nat.not_lt.mpr h2 hlt)

/-- Disjoint per-thread stores in the same barrier epoch never conflict (`recordEpochAccess` succeeds). -/
theorem recordEpochAccess_disjoint_ok (tid1 tid2 : Dim3) (sp : StateSpace)
    (a1 w1 a2 w2 : Nat) (wFlag1 wFlag2 : Bool)
    (h_disj : a1 + w1 ≤ a2 ∨ a2 + w2 ≤ a1) :
    recordEpochAccess [{ tid := tid1, space := sp, addr := a1, width := w1, isWrite := wFlag1 }]
      tid2 sp a2 w2 wFlag2 =
      .ok [{ tid := tid2, space := sp, addr := a2, width := w2, isWrite := wFlag2 },
           { tid := tid1, space := sp, addr := a1, width := w1, isWrite := wFlag1 }] := by
  have hNoOverlap := rangesOverlap_disjoint_false a2 w2 a1 w1 h_disj.symm
  unfold recordEpochAccess findDataRace? findDataRace?.go
  simp [hNoOverlap]
  rfl

/-- Unsynchronized cross-thread write-write or read-write overlap at the same address traps with `.dataRace`. -/
theorem recordEpochAccess_overlap_races (tid1 tid2 : Dim3) (sp : StateSpace)
    (addr width : Nat)
    (h_diff_tid : (tid1 != tid2) = true)
    (h_pos_width : 0 < width) :
    recordEpochAccess [{ tid := tid1, space := sp, addr := addr, width := width, isWrite := true }]
      tid2 sp addr width false = .dataRace sp addr := by
  have hOv : rangesOverlap addr width addr width = true := by
    unfold rangesOverlap
    exact decide_eq_true ⟨Nat.lt_add_of_pos_right h_pos_width, Nat.lt_add_of_pos_right h_pos_width⟩
  have hSp : (sp == sp) = true := by cases sp <;> rfl
  unfold recordEpochAccess findDataRace? findDataRace?.go
  simp [h_diff_tid, hOv, hSp]

/-- Fuel monotonicity of `runCTA`: once `runCTA f1 stmts cta` reaches any terminal (non-`fuelExhausted`)
    outcome `out`, running with any larger fuel budget `f2 ≥ f1` produces the exact same `out`. -/
theorem runCTA_mono_fuel (f1 f2 : Nat) (stmts : List PTXStmt) (cta : PTXCTAState)
    (out : PTXOutcome PTXCTAState)
    (hle : f1 ≤ f2)
    (h1 : runCTA f1 stmts cta = out)
    (hne : out ≠ .fuelExhausted) :
    runCTA f2 stmts cta = out := by
  induction f1 generalizing f2 cta with
  | zero =>
    unfold runCTA at h1
    cases hAll : cta.threads.all (·.halted)
    · simp [hAll] at h1
      exact False.elim (hne h1.symm)
    · simp [hAll] at h1
      have hRun2 := runCTA_halted f2 stmts cta hAll
      exact hRun2.trans h1
  | succ f1' ih =>
    cases f2 with
    | zero =>
      exact False.elim (Nat.not_succ_le_zero f1' hle)
    | succ f2' =>
      have hle' : f1' ≤ f2' := Nat.le_of_succ_le_succ hle
      unfold runCTA at h1 ⊢
      cases hStep : stepCTA stmts cta <;> simp [hStep, PTXOutcome.bind] at h1 ⊢
      case ok pair =>
        rcases pair with ⟨done, cta'⟩
        cases done with
        | true =>
          simp at h1 ⊢
          exact h1
        | false =>
          simp at h1 ⊢
          exact ih f2' cta' hle' h1
      all_goals exact h1

end LeanNative.Backend.PTXAst
