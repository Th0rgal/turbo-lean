/-!
# Typed Apple Metal MSL 3.0 AST (`C2b`)

Typed Metal Shading Language (MSL 3.0) compute AST covering every construct emitted by
production Metal lowering: address spaces, scalar/vector/pointer/reference/struct types,
expressions (including short-circuit `&&` / `||`), statements (including thread-local fixed-size
arrays and `atomic_exchange_explicit`), kernel/helper declarations, and struct definitions.
-/

namespace LeanNative.Backend.MetalAst

/-! ## Typed Metal Shading Language (MSL 3.0) AST -/

/-- Metal Shading Language address spaces. -/
inductive MSLAddressSpace where
  | device
  | constant
  | thread
  | threadgroup
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Metal Shading Language scalar, vector, pointer, reference, array, and struct types. -/
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
  | pointer   : MSLAddressSpace → Bool → MSLType → MSLType
  | ref       : MSLAddressSpace → MSLType → MSLType
  | threadArr : Bool → MSLType → Nat → MSLType
  | structTy  : String → MSLType
  deriving Repr, DecidableEq, Inhabited, BEq

namespace MSLType

/-- Addressable byte width of an MSL type (`0` for `void`, `8` for pointers/references). -/
def byteWidth : MSLType → Nat
  | .void => 0
  | .bool | .uchar => 1
  | .ushort | .half => 2
  | .uint | .int | .float | .atomicUint => 4
  | .ulong | .long | .double | .pointer _ _ _ | .ref _ _ => 8
  | .uint2 => 8
  | .uint3 => 12
  | .uint4 | .ulong2 => 16
  | .u256 => 32
  | .threadArr _ elem n => elem.byteWidth * n
  | .structTy _ => 0

/-- Scalar bit width used for width masking, sign-extension, and shift bounds. -/
def bitWidth : MSLType → Nat
  | .void => 0
  | .bool | .uchar => 8
  | .ushort | .half => 16
  | .uint | .int | .float | .atomicUint => 32
  | .ulong | .long | .double | .uint2 | .uint3 | .uint4 | .ulong2
  | .u256 | .pointer _ _ _ | .ref _ _ | .threadArr _ _ _ | .structTy _ => 64

/-- True when signed integer rules apply to arithmetic/shifts/comparisons. -/
def isSigned : MSLType → Bool
  | .int | .long => true
  | _ => false

/-- True for IEEE-754 floating-point scalar types (`.half`, `.float`, `.double`). -/
def isFloat : MSLType → Bool
  | .half | .float | .double => true
  | _ => false

/-- True for multi-lane vector types. -/
def isVector : MSLType → Bool
  | .uint2 | .uint3 | .uint4 | .ulong2 => true
  | _ => false

/-- Integer rank used by the C++/MSL usual arithmetic conversions
    (`bool < uchar < ushort < int < uint < long < ulong`). Floating types are handled separately. -/
def arithRank : MSLType → Nat
  | .bool => 0
  | .uchar => 1
  | .ushort => 2
  | .int => 3
  | .uint | .atomicUint => 4
  | .long => 5
  | .ulong | .u256 | .pointer _ _ _ | .ref _ _ | .structTy _ => 6
  | _ => 6

end MSLType

/-- Result type of a binary arithmetic/bitwise/relational operator after the C++/MSL usual
    arithmetic conversions (`bool < uchar < ushort < int < uint < long < ulong < half < float < double`,
    preserving homogeneous vector types). -/
def promoteMSLArithType (a b : MSLType) : MSLType :=
  if a.isVector then a
  else if b.isVector then b
  else if a == .double || b == .double then .double
  else if a == .float || b == .float then .float
  else if a == .half || b == .half then .half
  else if a.arithRank < b.arithRank then b
  else a

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
  | deref         : String → MSLExpr
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
  | logAnd        : MSLExpr → MSLExpr → MSLExpr
  | logOr         : MSLExpr → MSLExpr → MSLExpr
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
   simdgroup collectives, atomics, thread-local arrays, and barriers.
   Contains `MSLBlock` mutually rather than `List MSLStmt` so `MSLStmt` is a non-nested inductive
   compatible with `TurboLean.KernelGate` theorem-shard audits. -/
mutual
inductive MSLStmt where
  | varDecl         : MSLType → String → MSLExpr → MSLStmt
  | arrayDecl       : MSLType → String → Nat → MSLExprList → MSLStmt
  | assign          : String → MSLExpr → MSLStmt
  | fieldAssign     : String → String → MSLExpr → MSLStmt
  | indexAssign     : String → MSLExpr → MSLExpr → MSLStmt
  | derefAssign     : String → MSLExpr → MSLStmt
  | callAssign      : Option MSLType → String → String → MSLExprList → MSLStmt
  | exprStmt        : MSLExpr → MSLStmt
  | atomicFetchAdd  : Option MSLType → Option String → String → Option MSLExpr → MSLExpr → MSLStmt
  | atomicExchange  : Option MSLType → Option String → String → Option MSLExpr → MSLExpr → MSLStmt
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

end LeanNative.Backend.MetalAst
