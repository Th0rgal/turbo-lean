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

/-- Byte-addressed bounded memory buffer used independently for `globalMem` and per-CTA `sharedMem`. -/
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

/-- Per-thread execution state inside a CTA. -/
structure PTXThreadState where
  tid    : Dim3
  pc     : Nat := 0
  regs   : PTXRegFile := PTXRegFile.empty
  halted : Bool := false
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Complete CTA (Cooperative Thread Array) SIMT state with separated address spaces. -/
structure PTXCTAState where
  gridDim      : Dim3
  blockDim     : Dim3
  ctaId        : Dim3
  threads      : List PTXThreadState
  globalMem    : ByteMemory
  sharedMem    : ByteMemory
  paramMem     : ParamMemory
  sharedLayout : SharedLayout
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Explicit operational outcome of PTX SIMT execution, distinguishing normal completion from
    barrier divergence, out-of-bounds memory accesses, invalid labels, and fuel exhaustion. -/
inductive PTXOutcome (α : Type) where
  | ok                : α → PTXOutcome α
  | barrierDivergence : Nat → PTXOutcome α
  | outOfBoundsLoad   : StateSpace → Nat → PTXOutcome α
  | outOfBoundsStore  : StateSpace → Nat → PTXOutcome α
  | unboundParam      : String → PTXOutcome α
  | unboundPred       : String → PTXOutcome α
  | unboundLabel      : String → PTXOutcome α
  | invalidOperand    : String → PTXOutcome α
  | fuelExhausted     : PTXOutcome α
  deriving Repr, DecidableEq, Inhabited, BEq

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

/-- Resolve a byte address for `global` or `shared` state space accesses. -/
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

/-- Evaluate a `setp` comparison directly over `BitVec` without any `LeanNative.Semantics` calls. -/
def evalPTXCmp (cmp : PTXCmpOp) (ty : PTXType) (a b : BitVec 64) : Bool :=
  match ty with
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

/-- Execute a single non-barrier `PTXInstr` for one active thread `th` against `(cta, stmts)`,
    returning the updated `(PTXThreadState, ByteMemory (global), ByteMemory (shared))`. -/
def execNonBarrierInstr (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    (ins : PTXInstr) : PTXOutcome (PTXThreadState × ByteMemory × ByteMemory) :=
  let nextPc := th.pc + 1
  match ins with
  | .mov ty dst src =>
    match evalOperand cta th src with
    | .ok v =>
      let rf' :=
        if ty == .pred then th.regs.setPred dst (v != 0#64)
        else th.regs.setScalar dst (maskForType ty v)
      .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem)
    | .invalidOperand m => .invalidOperand m
    | _ => .invalidOperand "mov operand failure"
  | .ldParam ty dst paramName =>
    match cta.paramMem.lookupParam? paramName with
    | some v =>
      let rf' := th.regs.setScalar dst (maskForType ty v)
      .ok ({ th with pc := nextPc, regs := rf' }, cta.globalMem, cta.sharedMem)
    | none => .unboundParam paramName
  | .ldGlobal ty dst addr =>
    match evalAddr cta th addr with
    | .ok byteAddr =>
      match cta.globalMem.loadBits byteAddr ty.byteWidth with
      | some raw =>
        let v := if ty == .s32 then signExtend32To64 raw else maskForType ty raw
        .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst v }, cta.globalMem, cta.sharedMem)
      | none => .outOfBoundsLoad .global byteAddr
    | .invalidOperand m => .invalidOperand m
    | _ => .invalidOperand "ld.global address error"
  | .ldShared ty dst addr =>
    match evalAddr cta th addr with
    | .ok byteAddr =>
      match cta.sharedMem.loadBits byteAddr ty.byteWidth with
      | some raw =>
        let v := if ty == .s32 then signExtend32To64 raw else maskForType ty raw
        .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst v }, cta.globalMem, cta.sharedMem)
      | none => .outOfBoundsLoad .shared byteAddr
    | .invalidOperand m => .invalidOperand m
    | _ => .invalidOperand "ld.shared address error"
  | .stGlobal ty addr src =>
    match evalAddr cta th addr, evalOperand cta th src with
    | .ok byteAddr, .ok v =>
      match cta.globalMem.storeBits byteAddr ty.byteWidth (maskForType ty v) with
      | some g' => .ok ({ th with pc := nextPc }, g', cta.sharedMem)
      | none => .outOfBoundsStore .global byteAddr
    | .invalidOperand m, _ => .invalidOperand m
    | _, .invalidOperand m => .invalidOperand m
    | _, _ => .invalidOperand "st.global operand error"
  | .stShared ty addr src =>
    match evalAddr cta th addr, evalOperand cta th src with
    | .ok byteAddr, .ok v =>
      match cta.sharedMem.storeBits byteAddr ty.byteWidth (maskForType ty v) with
      | some s' => .ok ({ th with pc := nextPc }, cta.globalMem, s')
      | none => .outOfBoundsStore .shared byteAddr
    | .invalidOperand m, _ => .invalidOperand m
    | _, .invalidOperand m => .invalidOperand m
    | _, _ => .invalidOperand "st.shared operand error"
  | .cvtaToGlobal ty dst src =>
    match evalOperand cta th src with
    | .ok v =>
      .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst (maskForType ty v) },
           cta.globalMem, cta.sharedMem)
    | .invalidOperand m => .invalidOperand m
    | _ => .invalidOperand "cvta.to.global error"
  | .cvt _rm dstTy srcTy dst src =>
    match evalOperand cta th src with
    | .ok v =>
      let ext :=
        if srcTy == .s32 && (dstTy == .s64 || dstTy == .u64 || dstTy == .b64) then
          signExtend32To64 v
        else
          maskForType srcTy v
      let out := maskForType dstTy ext
      .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst out },
           cta.globalMem, cta.sharedMem)
    | .invalidOperand m => .invalidOperand m
    | _ => .invalidOperand "cvt error"
  | .add _rm ty dst a b =>
    match evalOperand cta th a, evalOperand cta th b with
    | .ok va, .ok vb =>
      let res := maskForType ty (maskForType ty va + maskForType ty vb)
      .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
           cta.globalMem, cta.sharedMem)
    | .invalidOperand m, _ | _, .invalidOperand m => .invalidOperand m
    | _, _ => .invalidOperand "add error"
  | .sub ty dst a b =>
    match evalOperand cta th a, evalOperand cta th b with
    | .ok va, .ok vb =>
      let res := maskForType ty (maskForType ty va - maskForType ty vb)
      .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
           cta.globalMem, cta.sharedMem)
    | .invalidOperand m, _ | _, .invalidOperand m => .invalidOperand m
    | _, _ => .invalidOperand "sub error"
  | .mul mode ty dst a b =>
    match evalOperand cta th a, evalOperand cta th b with
    | .ok va, .ok vb =>
      let out := match mode, ty with
        | .wide, .u32 | .wide, .b32 =>
          (va &&& 0xFFFF_FFFF#64) * (vb &&& 0xFFFF_FFFF#64)
        | .wide, .s32 =>
          signExtend32To64 va * signExtend32To64 vb
        | .hi, .u64 | .hi, .b64 =>
          let prod128 : BitVec 128 := (va.zeroExtend 128) * (vb.zeroExtend 128)
          (prod128 >>> 64).truncate 64
        | _, _ =>
          maskForType ty (maskForType ty va * maskForType ty vb)
      .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst out },
           cta.globalMem, cta.sharedMem)
    | .invalidOperand m, _ | _, .invalidOperand m => .invalidOperand m
    | _, _ => .invalidOperand "mul error"
  | .div ty dst a b =>
    match evalOperand cta th a, evalOperand cta th b with
    | .ok va, .ok vb =>
      let ma := maskForType ty va
      let mb := maskForType ty vb
      let res :=
        if mb == 0#64 then 0#64
        else if ty == .s64 then BitVec.sdiv ma mb
        else if ty == .s32 then
          let q32 := BitVec.sdiv (ma.truncate 32) (mb.truncate 32)
          q32.zeroExtend 64
        else maskForType ty (ma / mb)
      .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
           cta.globalMem, cta.sharedMem)
    | .invalidOperand m, _ | _, .invalidOperand m => .invalidOperand m
    | _, _ => .invalidOperand "div error"
  | .rem ty dst a b =>
    match evalOperand cta th a, evalOperand cta th b with
    | .ok va, .ok vb =>
      let ma := maskForType ty va
      let mb := maskForType ty vb
      let res :=
        if mb == 0#64 then ma
        else if ty == .s64 then BitVec.srem ma mb
        else if ty == .s32 then
          let r32 := BitVec.srem (ma.truncate 32) (mb.truncate 32)
          r32.zeroExtend 64
        else maskForType ty (ma % mb)
      .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
           cta.globalMem, cta.sharedMem)
    | .invalidOperand m, _ | _, .invalidOperand m => .invalidOperand m
    | _, _ => .invalidOperand "rem error"
  | .mad mode ty dst a b c =>
    match evalOperand cta th a, evalOperand cta th b, evalOperand cta th c with
    | .ok va, .ok vb, .ok vc =>
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
           cta.globalMem, cta.sharedMem)
    | .invalidOperand m, _, _ | _, .invalidOperand m, _ | _, _, .invalidOperand m =>
      .invalidOperand m
    | _, _, _ => .invalidOperand "mad error"
  | .fma _rm ty dst a b c =>
    match evalOperand cta th a, evalOperand cta th b, evalOperand cta th c with
    | .ok va, .ok vb, .ok vc =>
      let res := maskForType ty (maskForType ty va * maskForType ty vb + maskForType ty vc)
      .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
           cta.globalMem, cta.sharedMem)
    | .invalidOperand m, _, _ | _, .invalidOperand m, _ | _, _, .invalidOperand m =>
      .invalidOperand m
    | _, _, _ => .invalidOperand "fma error"
  | .bitAnd ty dst a b =>
    match evalOperand cta th a, evalOperand cta th b with
    | .ok va, .ok vb =>
      if ty == .pred then
        match th.regs.getPred (match a with | .reg r => r | _ => ""),
              th.regs.getPred (match b with | .reg r => r | _ => "") with
        | some pa, some pb =>
          .ok ({ th with pc := nextPc, regs := th.regs.setPred dst (pa && pb) },
               cta.globalMem, cta.sharedMem)
        | _, _ =>
          .ok ({ th with pc := nextPc, regs := th.regs.setPred dst (va != 0#64 && vb != 0#64) },
               cta.globalMem, cta.sharedMem)
      else
        let res := maskForType ty (va &&& vb)
        .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
             cta.globalMem, cta.sharedMem)
    | .invalidOperand m, _ | _, .invalidOperand m => .invalidOperand m
    | _, _ => .invalidOperand "and error"
  | .bitOr ty dst a b =>
    match evalOperand cta th a, evalOperand cta th b with
    | .ok va, .ok vb =>
      if ty == .pred then
        match th.regs.getPred (match a with | .reg r => r | _ => ""),
              th.regs.getPred (match b with | .reg r => r | _ => "") with
        | some pa, some pb =>
          .ok ({ th with pc := nextPc, regs := th.regs.setPred dst (pa || pb) },
               cta.globalMem, cta.sharedMem)
        | _, _ =>
          .ok ({ th with pc := nextPc, regs := th.regs.setPred dst (va != 0#64 || vb != 0#64) },
               cta.globalMem, cta.sharedMem)
      else
        let res := maskForType ty (va ||| vb)
        .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
             cta.globalMem, cta.sharedMem)
    | .invalidOperand m, _ | _, .invalidOperand m => .invalidOperand m
    | _, _ => .invalidOperand "or error"
  | .bitXor ty dst a b =>
    match evalOperand cta th a, evalOperand cta th b with
    | .ok va, .ok vb =>
      if ty == .pred then
        match th.regs.getPred (match a with | .reg r => r | _ => ""),
              th.regs.getPred (match b with | .reg r => r | _ => "") with
        | some pa, some pb =>
          .ok ({ th with pc := nextPc, regs := th.regs.setPred dst (pa != pb) },
               cta.globalMem, cta.sharedMem)
        | _, _ =>
          .ok ({ th with pc := nextPc, regs := th.regs.setPred dst ((va != 0#64) != (vb != 0#64)) },
               cta.globalMem, cta.sharedMem)
      else
        let res := maskForType ty (va ^^^ vb)
        .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
             cta.globalMem, cta.sharedMem)
    | .invalidOperand m, _ | _, .invalidOperand m => .invalidOperand m
    | _, _ => .invalidOperand "xor error"
  | .bitNot ty dst a =>
    match evalOperand cta th a with
    | .ok va =>
      if ty == .pred then
        match th.regs.getPred (match a with | .reg r => r | _ => "") with
        | some pa =>
          .ok ({ th with pc := nextPc, regs := th.regs.setPred dst (!pa) },
               cta.globalMem, cta.sharedMem)
        | none =>
          .ok ({ th with pc := nextPc, regs := th.regs.setPred dst (va == 0#64) },
               cta.globalMem, cta.sharedMem)
      else
        let res := maskForType ty (~~~va)
        .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
             cta.globalMem, cta.sharedMem)
    | .invalidOperand m => .invalidOperand m
    | _ => .invalidOperand "not error"
  | .neg ty dst a =>
    match evalOperand cta th a with
    | .ok va =>
      let res := maskForType ty (0#64 - maskForType ty va)
      .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
           cta.globalMem, cta.sharedMem)
    | .invalidOperand m => .invalidOperand m
    | _ => .invalidOperand "neg error"
  | .shl ty dst a sh =>
    match evalOperand cta th a, evalOperand cta th sh with
    | .ok va, .ok vsh =>
      let shiftAmt := (vsh &&& 0xFFFF_FFFF#64).toNat
      let width := ty.bitWidth
      let res :=
        if shiftAmt ≥ width then 0#64
        else maskForType ty ((maskForType ty va) <<< shiftAmt)
      .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst res },
           cta.globalMem, cta.sharedMem)
    | .invalidOperand m, _ | _, .invalidOperand m => .invalidOperand m
    | _, _ => .invalidOperand "shl error"
  | .shr ty dst a sh =>
    match evalOperand cta th a, evalOperand cta th sh with
    | .ok va, .ok vsh =>
      let shiftAmt := (vsh &&& 0xFFFF_FFFF#64).toNat
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
           cta.globalMem, cta.sharedMem)
    | .invalidOperand m, _ | _, .invalidOperand m => .invalidOperand m
    | _, _ => .invalidOperand "shr error"
  | .setp cmp ty dstPred a b =>
    match evalOperand cta th a, evalOperand cta th b with
    | .ok va, .ok vb =>
      let flag := evalPTXCmp cmp ty va vb
      .ok ({ th with pc := nextPc, regs := th.regs.setPred dstPred flag },
           cta.globalMem, cta.sharedMem)
    | .invalidOperand m, _ | _, .invalidOperand m => .invalidOperand m
    | _, _ => .invalidOperand "setp error"
  | .selp ty dst tOp fOp predName =>
    match th.regs.getPred predName with
    | none => .unboundPred predName
    | some cond =>
      match evalOperand cta th tOp, evalOperand cta th fOp with
      | .ok vt, .ok vf =>
        let chosen := maskForType ty (if cond then vt else vf)
        .ok ({ th with pc := nextPc, regs := th.regs.setScalar dst chosen },
             cta.globalMem, cta.sharedMem)
      | .invalidOperand m, _ | _, .invalidOperand m => .invalidOperand m
      | _, _ => .invalidOperand "selp error"
  | .barSync bid =>
    .barrierDivergence bid
  | .bra targetLbl =>
    match findLabelPC? stmts targetLbl with
    | some targetPc => .ok ({ th with pc := targetPc }, cta.globalMem, cta.sharedMem)
    | none => .unboundLabel targetLbl
  | .ret =>
    .ok ({ th with pc := nextPc, halted := true }, cta.globalMem, cta.sharedMem)

/-- Execute a single predicated instruction (`@p` / `@!p`) for thread `th`.
    When the evaluated guard is `false`, the instruction is a pure PC-advancing no-op. -/
def execPredicatedInstr (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    (guard : Option PTXPredGuard) (ins : PTXInstr) :
    PTXOutcome (PTXThreadState × ByteMemory × ByteMemory) :=
  match evalPredGuard th guard with
  | .ok true => execNonBarrierInstr stmts cta th ins
  | .ok false => .ok ({ th with pc := th.pc + 1 }, cta.globalMem, cta.sharedMem)
  | .unboundPred p => .unboundPred p
  | .barrierDivergence b => .barrierDivergence b
  | .outOfBoundsLoad sp a => .outOfBoundsLoad sp a
  | .outOfBoundsStore sp a => .outOfBoundsStore sp a
  | .unboundParam p => .unboundParam p
  | .unboundLabel l => .unboundLabel l
  | .invalidOperand m => .invalidOperand m
  | .fuelExhausted => .fuelExhausted

/-- True if thread `th` is currently parked at an active (guard = `true`, unhalted) `bar.sync bid`
    at `stmts[th.pc]?`. Returns `Except PTXOutcome` via `PTXOutcome (Option Nat)`. -/
def threadAtActiveBarrier (stmts : List PTXStmt) (th : PTXThreadState) :
    PTXOutcome (Option Nat) :=
  if th.halted then
    .ok none
  else
    match stmts[th.pc]? with
    | some (.instr guard (.barSync bid)) =>
      match evalPredGuard th guard with
      | .ok true => .ok (some bid)
      | .ok false => .ok none
      | .unboundPred p => .unboundPred p
      | _ => .invalidOperand "invalid barrier predicate"
    | _ => .ok none

/-- Collect the barrier state of every thread in `threads`. -/
def collectBarrierStates (stmts : List PTXStmt) :
    List PTXThreadState → PTXOutcome (List (Option Nat))
  | [] => .ok []
  | th :: rest =>
    match threadAtActiveBarrier stmts th, collectBarrierStates stmts rest with
    | .ok b, .ok bs => .ok (b :: bs)
    | .unboundPred p, _ => .unboundPred p
    | _, .unboundPred p => .unboundPred p
    | .invalidOperand m, _ => .invalidOperand m
    | _, .invalidOperand m => .invalidOperand m
    | .barrierDivergence d, _ => .barrierDivergence d
    | _, .barrierDivergence d => .barrierDivergence d
    | .outOfBoundsLoad s a, _ => .outOfBoundsLoad s a
    | _, .outOfBoundsLoad s a => .outOfBoundsLoad s a
    | .outOfBoundsStore s a, _ => .outOfBoundsStore s a
    | _, .outOfBoundsStore s a => .outOfBoundsStore s a
    | .unboundParam p, _ => .unboundParam p
    | _, .unboundParam p => .unboundParam p
    | .unboundLabel l, _ => .unboundLabel l
    | _, .unboundLabel l => .unboundLabel l
    | .fuelExhausted, _ => .fuelExhausted
    | _, .fuelExhausted => .fuelExhausted

/-- Synchronize a CTA when every thread in the CTA has arrived at the exact same `bar.sync bid`:
    advances all threads past the barrier (`pc + 1`). If some thread is at `bar.sync bid` while
    another thread in the CTA is halted or at a different barrier / stuck elsewhere, reports
    `PTXOutcome.barrierDivergence bid`. -/
def stepCTABarrier (bid : Nat) (states : List (Option Nat)) (cta : PTXCTAState) :
    PTXOutcome PTXCTAState :=
  if states.all (fun s => s == some bid) then
    .ok { cta with threads := cta.threads.map fun th => { th with pc := th.pc + 1 } }
  else
    .barrierDivergence bid

/-- Advance the first non-halted, non-barrier-waiting thread by one statement, so threads run
    independently up to CTA barriers (`bar.sync`) where lockstep convergence is enforced. -/
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
        match evalPredGuard th guard with
        | .ok true =>
          stepFirstReadyThread stmts cta (th :: prefixRev) suffix
        | .ok false =>
          let th' := { th with pc := th.pc + 1 }
          .ok (true, { cta with threads := prefixRev.reverse ++ (th' :: suffix) })
        | .unboundPred p => .unboundPred p
        | _ => .invalidOperand "barrier guard error"
      | some (.instr guard ins) =>
        match execPredicatedInstr stmts cta th guard ins with
        | .ok (th', gMem', sMem') =>
          .ok (true, { cta with
            threads := prefixRev.reverse ++ (th' :: suffix)
            globalMem := gMem'
            sharedMem := sMem' })
        | .barrierDivergence b => .barrierDivergence b
        | .outOfBoundsLoad s a => .outOfBoundsLoad s a
        | .outOfBoundsStore s a => .outOfBoundsStore s a
        | .unboundParam p => .unboundParam p
        | .unboundPred p => .unboundPred p
        | .unboundLabel l => .unboundLabel l
        | .invalidOperand m => .invalidOperand m
        | .fuelExhausted => .fuelExhausted

/-- Single SIMT CTA step:
    1. If all threads are halted, CTA execution is complete (`done = true`).
    2. Otherwise, if any non-barrier-waiting thread can advance toward the next barrier or `ret`,
       advance it.
    3. Once no thread can advance without crossing a barrier, inspect CTA barrier states:
       if all threads in the CTA agree on `some bid`, release the barrier in lockstep;
       otherwise report `PTXOutcome.barrierDivergence bid`. -/
def stepCTA (stmts : List PTXStmt) (cta : PTXCTAState) : PTXOutcome (Bool × PTXCTAState) :=
  if cta.threads.all (·.halted) then
    .ok (true, cta)
  else
    match stepFirstReadyThread stmts cta [] cta.threads with
    | .ok (true, cta') => .ok (false, cta')
    | .ok (false, cta') =>
      match collectBarrierStates stmts cta'.threads with
      | .ok barStates =>
        match barStates.findSome? id with
        | some bid =>
          match stepCTABarrier bid barStates cta' with
          | .ok synced => .ok (false, synced)
          | .barrierDivergence b => .barrierDivergence b
          | _ => .barrierDivergence bid
        | none => .ok (true, cta')
      | .unboundPred p => .unboundPred p
      | .invalidOperand m => .invalidOperand m
      | .barrierDivergence b => .barrierDivergence b
      | .outOfBoundsLoad s a => .outOfBoundsLoad s a
      | .outOfBoundsStore s a => .outOfBoundsStore s a
      | .unboundParam p => .unboundParam p
      | .unboundLabel l => .unboundLabel l
      | .fuelExhausted => .fuelExhausted
    | .barrierDivergence b => .barrierDivergence b
    | .outOfBoundsLoad s a => .outOfBoundsLoad s a
    | .outOfBoundsStore s a => .outOfBoundsStore s a
    | .unboundParam p => .unboundParam p
    | .unboundPred p => .unboundPred p
    | .unboundLabel l => .unboundLabel l
    | .invalidOperand m => .invalidOperand m
    | .fuelExhausted => .fuelExhausted

/-- Execute a CTA with bounded `fuel` steps. -/
def runCTA (fuel : Nat) (stmts : List PTXStmt) (cta : PTXCTAState) : PTXOutcome PTXCTAState :=
  match fuel with
  | 0 =>
    if cta.threads.all (·.halted) then .ok cta else .fuelExhausted
  | f + 1 =>
    match stepCTA stmts cta with
    | .ok (true, cta') => .ok cta'
    | .ok (false, cta') => runCTA f stmts cta'
    | .barrierDivergence b => .barrierDivergence b
    | .outOfBoundsLoad s a => .outOfBoundsLoad s a
    | .outOfBoundsStore s a => .outOfBoundsStore s a
    | .unboundParam p => .unboundParam p
    | .unboundPred p => .unboundPred p
    | .unboundLabel l => .unboundLabel l
    | .invalidOperand m => .invalidOperand m
    | .fuelExhausted => .fuelExhausted

/-- Initialize a `PTXCTAState` for a kernel launch on CTA coordinate `ctaId`. -/
def initCTAState (k : PTXKernel) (gridDim blockDim ctaId : Dim3)
    (globalMem : ByteMemory) (paramMem : ParamMemory) : PTXCTAState :=
  let layout := buildSharedLayout k.sharedDecls
  let threads := blockDim.coords.map fun tid => { tid := tid, pc := 0, regs := PTXRegFile.empty, halted := false }
  { gridDim
    blockDim
    ctaId
    threads
    globalMem
    sharedMem := ByteMemory.zeros layout.totalSize
    paramMem
    sharedLayout := layout }

/-- Launch a `PTXKernel` across every CTA in `gridDim` (each with fresh per-CTA `sharedMem`),
    threading `globalMem` across CTAs and returning the final `ByteMemory`. -/
def evalPTXKernel (fuelPerCTA : Nat) (k : PTXKernel) (gridDim blockDim : Dim3)
    (globalMem : ByteMemory) (paramMem : ParamMemory) : PTXOutcome ByteMemory :=
  let rec loopCTAs (gMem : ByteMemory) : List Dim3 → PTXOutcome ByteMemory
    | [] => .ok gMem
    | ctaId :: rest =>
      let cta0 := initCTAState k gridDim blockDim ctaId gMem paramMem
      match runCTA fuelPerCTA k.body cta0 with
      | .ok ctaFinal => loopCTAs ctaFinal.globalMem rest
      | .barrierDivergence b => .barrierDivergence b
      | .outOfBoundsLoad s a => .outOfBoundsLoad s a
      | .outOfBoundsStore s a => .outOfBoundsStore s a
      | .unboundParam p => .unboundParam p
      | .unboundPred p => .unboundPred p
      | .unboundLabel l => .unboundLabel l
      | .invalidOperand m => .invalidOperand m
      | .fuelExhausted => .fuelExhausted
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
    if off > 0 then s!"[{r}+{off}]" else s!"[{r}+{off}]"
  | .symOffset s 0 => s!"[{s}]"
  | .symOffset s off => s!"[{s}+{off}]"

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
  let regLines := k.regDecls.map fun r =>
    s!"    .reg {ppPTXType r.ty} {r.prefixName}<{r.count}>;"
  let bodyLines := k.body.map ppPTXStmt
  let header :=
    if k.params.isEmpty then s!".visible .entry {k.name}()\n\{"
    else s!".visible .entry {k.name}(\n{paramLines}\n)\n\{"
  String.intercalate "\n" ([header] ++ sharedLines ++ regLines ++ bodyLines ++ ["}"])

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
    (h_exec : execNonBarrierInstr stmts cta th (.stShared ty addr src) = .ok (th', gMem', sMem')) :
    gMem' = cta.globalMem := by
  dsimp [execNonBarrierInstr] at h_exec
  cases hAddr : evalAddr cta th addr <;> cases hSrc : evalOperand cta th src <;>
    simp [hAddr, hSrc] at h_exec
  case ok.ok byteAddr val =>
    cases hStore : cta.sharedMem.storeBits byteAddr ty.byteWidth (maskForType ty val) <;>
      simp [hStore] at h_exec
    exact h_exec.2.1.symm

/-- Address-space non-interference (Global -> Shared): executing `st.global` never mutates per-CTA
    `sharedMem` whenever it succeeds, leaving `sharedMem` bit-identical to `cta.sharedMem`. -/
theorem st_global_preserves_shared (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    (ty : PTXType) (addr : PTXAddr) (src : PTXOperand)
    (th' : PTXThreadState) (gMem' sMem' : ByteMemory)
    (h_exec : execNonBarrierInstr stmts cta th (.stGlobal ty addr src) = .ok (th', gMem', sMem')) :
    sMem' = cta.sharedMem := by
  dsimp [execNonBarrierInstr] at h_exec
  cases hAddr : evalAddr cta th addr <;> cases hSrc : evalOperand cta th src <;>
    simp [hAddr, hSrc] at h_exec
  case ok.ok byteAddr val =>
    cases hStore : cta.globalMem.storeBits byteAddr ty.byteWidth (maskForType ty val) <;>
      simp [hStore] at h_exec
    exact h_exec.2.2.symm

/-- Predicated instruction false-guard no-op: whenever `evalPredGuard th guard = .ok false`,
    `execPredicatedInstr` advances `th.pc` by 1 while leaving `th.regs`, `cta.globalMem`, and
    `cta.sharedMem` completely untouched for every `PTXInstr` (including `bar.sync` and `st.*`). -/
theorem execInstr_pred_false_noop (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    (guard : Option PTXPredGuard) (ins : PTXInstr)
    (h_false : evalPredGuard th guard = .ok false) :
    execPredicatedInstr stmts cta th guard ins =
      .ok ({ th with pc := th.pc + 1 }, cta.globalMem, cta.sharedMem) := by
  unfold execPredicatedInstr
  rw [h_false]

/-- Uniform CTA `bar.sync` convergence: when every thread in the CTA arrives at the exact same
    barrier identifier `bid`, `stepCTABarrier` converges cleanly without error, advancing every
    thread's program counter past the barrier while preserving both `globalMem` and `sharedMem`. -/
theorem bar_sync_uniform_converges (bid : Nat) (states : List (Option Nat)) (cta : PTXCTAState)
    (h_uniform : states.all (fun s => s == some bid) = true) :
    stepCTABarrier bid states cta =
      .ok { cta with threads := cta.threads.map fun th => { th with pc := th.pc + 1 } } := by
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
    unfold runCTA stepCTA
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
      unfold runCTA at h1 h2
      cases hStep : stepCTA stmts cta with
      | ok pair =>
        cases pair with
        | mk done cta' =>
          cases done with
          | true =>
            simp [hStep] at h1 h2
            exact h1.symm.trans h2
          | false =>
            simp [hStep] at h1 h2
            exact ih f2' cta' h1 h2
      | barrierDivergence b =>
        simp [hStep] at h1 h2
        exact h1.symm.trans h2
      | outOfBoundsLoad s a =>
        simp [hStep] at h1 h2
        exact h1.symm.trans h2
      | outOfBoundsStore s a =>
        simp [hStep] at h1 h2
        exact h1.symm.trans h2
      | unboundParam p =>
        simp [hStep] at h1 h2
        exact h1.symm.trans h2
      | unboundPred p =>
        simp [hStep] at h1 h2
        exact h1.symm.trans h2
      | unboundLabel l =>
        simp [hStep] at h1 h2
        exact h1.symm.trans h2
      | invalidOperand m =>
        simp [hStep] at h1 h2
        exact h1.symm.trans h2
      | fuelExhausted =>
        simp [hStep] at h1 h2
        exact h1.symm.trans h2

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
    27 ISA constructors terminates with a trailing `';'`. -/
theorem ppPTXInstr_semicolon_terminated (ins : PTXInstr) :
    (ppPTXInstr ins).toList.getLast? = some ';' := by
  cases ins <;> exact append_semicolon_getLast _

end LeanNative.Backend.PTXAst
