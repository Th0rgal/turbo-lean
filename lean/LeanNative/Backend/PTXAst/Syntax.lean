/-!
# Genuine NVIDIA CUDA PTX 8.0 AST (`C2b`) — typed ISA syntax.
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

/-- True when `ty` is an untyped bit-size type (`.b8`, `.b16`, `.b32`, `.b64`). -/
def isBitType : PTXType → Bool
  | .b8 | .b16 | .b32 | .b64 => true
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
  | atomCas      : StateSpace → PTXType → String → PTXAddr → PTXOperand → PTXOperand → PTXInstr
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

/-- Optional per-thread read oracle mapping `(ctaId, tid, threadAccessOrdinal, space, byteAddr, width)`
    to an optional candidate `BitVec 64` raw read value (`none` falls back to current memory). -/
abbrev PTXReadOracle := Dim3 → Dim3 → Nat → StateSpace → Nat → Nat → Option (BitVec 64)

/-- Recorded addressable-memory event (`ld.*`, `st.*`, `atom.add`, `atom.cas`) for axiomatic weak-memory
    consistency (`D6`). `isRead` and `isWrite` are both `true` on atomic RMW events (`atom.add`, `atom.cas`). -/
structure PTXMemEvent where
  eventId      : Nat
  kernelIdx    : Nat := 0
  ctaId        : Dim3
  tid          : Dim3
  barrierEpoch : List (Nat × Nat) := []
  space        : StateSpace
  addr         : Nat
  width        : Nat
  isRead       : Bool := false
  isWrite      : Bool := false
  isAtomic     : Bool := false
  valRead      : BitVec 64 := 0#64
  valWritten   : BitVec 64 := 0#64
  poSeq        : Nat := 0
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Transitive closure `(po ∪ sw)+` over event identifiers. -/
inductive PTXHappensBefore (step : Nat → Nat → Prop) : Nat → Nat → Prop where
  | single : ∀ {a b : Nat}, step a b → PTXHappensBefore step a b
  | tail   : ∀ {a b c : Nat}, PTXHappensBefore step a b → step b c → PTXHappensBefore step a c

/-- Candidate weak-memory execution (`po`, `rf`, `co`, `sw`) over a recorded `PTXMemEvent` trace. -/
structure PTXCandidateExecution where
  events : List PTXMemEvent
  po     : Nat → Nat → Prop
  rf     : Nat → Nat → Prop
  co     : Nat → Nat → Prop
  sw     : Nat → Nat → Prop

namespace PTXCandidateExecution

def hasEvent (cand : PTXCandidateExecution) (eid : Nat) : Option PTXMemEvent :=
  cand.events.find? (fun e => e.eventId == eid)

def sameLoc (e1 e2 : PTXMemEvent) : Prop :=
  e1.space = e2.space ∧ e1.addr = e2.addr ∧ e1.width = e2.width ∧
  (e1.space = .global ∨ (e1.space = .shared ∧ e1.ctaId = e2.ctaId))

def poOrSw (cand : PTXCandidateExecution) (a b : Nat) : Prop :=
  cand.po a b ∨ cand.sw a b

def hb (cand : PTXCandidateExecution) (a b : Nat) : Prop :=
  PTXHappensBefore cand.poOrSw a b

def fr (cand : PTXCandidateExecution) (r w : Nat) : Prop :=
  (∃ w0 : Nat, cand.rf w0 r ∧ cand.co w0 w) ∨
  ((¬ ∃ w0 : Nat, cand.rf w0 r) ∧
    ∃ er ew : PTXMemEvent,
      cand.hasEvent r = some er ∧ cand.hasEvent w = some ew ∧
      er.isRead = true ∧ ew.isWrite = true ∧ sameLoc er ew ∧ r ≠ w)

end PTXCandidateExecution

/-- Lookup a barrier generation counter in `barrierEpoch` (`0` if never reached). -/
def lookupBarrierEpoch (epochs : List (Nat × Nat)) (bid : Nat) : Nat :=
  match epochs with
  | [] => 0
  | (b, g) :: rest => if b == bid then g else lookupBarrierEpoch rest bid

/-- Axiomatic PTX weak-memory consistency predicate (`po` / `rf` / `co` / `sw`) over `BitVec 64`
    values (`D6`), enforcing intra-CTA `bar.sync` release-acquire synchronization, sequential
    inter-kernel launch ordering, `hb := (po ∪ sw)+` irreflexivity, per-location `co` totality and
    `rf`/`co`/`fr` coherence, and `atom.add`/`atom.cas` RMW atomicity (no intervening `co` store). -/
structure PTXAxiomaticConsistent (initMem : Nat → StateSpace → Nat → Option (BitVec 64))
    (cand : PTXCandidateExecution) : Prop where
  eventIds_nodup : (cand.events.map PTXMemEvent.eventId).Nodup
  po_wf : ∀ {a b : Nat}, cand.po a b →
    ∃ ea eb : PTXMemEvent,
      cand.hasEvent a = some ea ∧ cand.hasEvent b = some eb ∧
      ea.kernelIdx = eb.kernelIdx ∧ ea.ctaId = eb.ctaId ∧ ea.tid = eb.tid ∧ ea.poSeq < eb.poSeq
  po_irrefl : ∀ (a : Nat), ¬ cand.po a a
  po_trans : ∀ {a b c : Nat}, cand.po a b → cand.po b c → cand.po a c
  po_complete : ∀ (ea eb : PTXMemEvent),
    ea ∈ cand.events → eb ∈ cand.events →
    ea.kernelIdx = eb.kernelIdx → ea.ctaId = eb.ctaId → ea.tid = eb.tid →
    ea.poSeq < eb.poSeq → cand.po ea.eventId eb.eventId
  sw_cta_barrier : ∀ (ea eb : PTXMemEvent) (bid : Nat),
    ea ∈ cand.events → eb ∈ cand.events →
    ea.kernelIdx = eb.kernelIdx → ea.ctaId = eb.ctaId → ea.tid ≠ eb.tid →
    lookupBarrierEpoch ea.barrierEpoch bid < lookupBarrierEpoch eb.barrierEpoch bid →
    cand.sw ea.eventId eb.eventId
  sw_inter_kernel : ∀ (ea eb : PTXMemEvent),
    ea ∈ cand.events → eb ∈ cand.events →
    ea.space = .global → eb.space = .global →
    ea.isWrite = true → ea.kernelIdx < eb.kernelIdx →
    cand.sw ea.eventId eb.eventId
  hb_irrefl : ∀ (a : Nat), ¬ cand.hb a a
  rf_wf : ∀ {w r : Nat}, cand.rf w r →
    ∃ ew er : PTXMemEvent,
      cand.hasEvent w = some ew ∧ cand.hasEvent r = some er ∧
      ew.isWrite = true ∧ er.isRead = true ∧
      PTXCandidateExecution.sameLoc ew er ∧ ew.valWritten = er.valRead ∧ w ≠ r
  rf_complete : ∀ (er : PTXMemEvent),
    er ∈ cand.events → er.isRead = true →
    (∃ w : Nat, cand.rf w er.eventId ∧ ∀ w' : Nat, cand.rf w' er.eventId → w' = w) ∨
      ((¬ ∃ w : Nat, cand.rf w er.eventId) ∧
        initMem er.addr er.space er.width = some er.valRead)
  co_wf : ∀ {w1 w2 : Nat}, cand.co w1 w2 →
    ∃ e1 e2 : PTXMemEvent,
      cand.hasEvent w1 = some e1 ∧ cand.hasEvent w2 = some e2 ∧
      e1.isWrite = true ∧ e2.isWrite = true ∧
      PTXCandidateExecution.sameLoc e1 e2 ∧ w1 ≠ w2
  co_irrefl : ∀ (w : Nat), ¬ cand.co w w
  co_trans : ∀ {w1 w2 w3 : Nat}, cand.co w1 w2 → cand.co w2 w3 → cand.co w1 w3
  co_total : ∀ (e1 e2 : PTXMemEvent),
    e1 ∈ cand.events → e2 ∈ cand.events →
    e1.isWrite = true → e2.isWrite = true →
    PTXCandidateExecution.sameLoc e1 e2 → e1.eventId ≠ e2.eventId →
    cand.co e1.eventId e2.eventId ∨ cand.co e2.eventId e1.eventId
  coh_ww : ∀ {w1 w2 : Nat},
    (∃ e1 e2 : PTXMemEvent,
      cand.hasEvent w1 = some e1 ∧ cand.hasEvent w2 = some e2 ∧
      e1.isWrite = true ∧ e2.isWrite = true ∧ PTXCandidateExecution.sameLoc e1 e2) →
    cand.hb w1 w2 → cand.co w1 w2
  coh_wr : ∀ {w r : Nat}, cand.rf w r → ¬ cand.hb r w
  coh_rw : ∀ {r w : Nat}, cand.fr r w → ¬ cand.hb w r
  coh_vrw : ∀ {w1 w2 r : Nat}, cand.rf w1 r → cand.co w1 w2 → ¬ cand.hb w2 r
  rmw_atomicity : ∀ (e : PTXMemEvent),
    e ∈ cand.events → e.isAtomic = true → e.isRead = true → e.isWrite = true →
    (∀ {w : Nat}, cand.rf w e.eventId →
      cand.co w e.eventId ∧ ¬ ∃ wMid : Nat, cand.co w wMid ∧ cand.co wMid e.eventId) ∧
    ((¬ ∃ w : Nat, cand.rf w e.eventId) → ¬ ∃ wPre : Nat, cand.co wPre e.eventId)

end LeanNative.Backend.PTXAst
