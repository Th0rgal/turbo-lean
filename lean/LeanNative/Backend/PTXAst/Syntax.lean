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

end LeanNative.Backend.PTXAst
