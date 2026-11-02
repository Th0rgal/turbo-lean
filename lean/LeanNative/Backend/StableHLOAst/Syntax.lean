import LeanNative.IR.Types

namespace LeanNative.Backend.StableHLOAst

open LeanNative.IR

/-- Element types carried by a StableHLO tensor. `bf16` is stored as raw `UInt16` bits. -/
inductive ElemType where
  | i1 | i8 | i16 | i32 | i64
  | ui8 | ui16 | ui32 | ui64
  | f32 | f64 | bf16
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Ranked tensor type: static shape plus element type. -/
structure TensorType where
  shape : List Nat
  elem  : ElemType
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Product of the shape dimensions. The empty shape is a scalar (`1`). -/
def TensorType.numElements (ty : TensorType) : Nat :=
  ty.shape.foldl (· * ·) 1

/-- Comparison directions used by `stablehlo.compare`. -/
inductive CompareDir where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr, Inhabited, BEq

/-- A typed, flat, row-major tensor buffer. Well-formed values satisfy `data.size = ty.numElements`. -/
structure TensorVal where
  ty   : TensorType
  data : Array (BitVec 64)
  deriving DecidableEq, Repr, Inhabited

def TensorVal.wellFormed (t : TensorVal) : Prop :=
  t.data.size = t.ty.numElements

/-- StableHLO operations used by the typed AST. Operands are SSA names. -/
inductive StableHLOOp where
  | constant (dst : String) (value : TensorVal)
  | add (dst lhs rhs : String)
  | subtract (dst lhs rhs : String)
  | multiply (dst lhs rhs : String)
  | divide (dst lhs rhs : String)
  | remainder (dst lhs rhs : String)
  | maximum (dst lhs rhs : String)
  | minimum (dst lhs rhs : String)
  | and (dst lhs rhs : String)
  | or (dst lhs rhs : String)
  | xor (dst lhs rhs : String)
  | shiftLeft (dst lhs rhs : String)
  | shiftRightArithmetic (dst lhs rhs : String)
  | shiftRightLogical (dst lhs rhs : String)
  | compare (dst lhs rhs : String) (dir : CompareDir)
  | select (dst pred onTrue onFalse : String)
  | broadcastInDim (dst src : String) (outShape : List Nat) (dims : List Nat)
  | reshape (dst src : String) (outShape : List Nat)
  | slice (dst src : String) (starts limits strides : List Nat)
  | dynamicSlice (dst src : String) (startIndices : List String) (sliceSizes : List Nat)
  | dotGeneral (dst lhs rhs : String)
      (lhsBatch rhsBatch lhsContract rhsContract : List Nat) (outShape : List Nat)
  | reduce (dst src init : String) (dims : List Nat) (body : String) (outShape : List Nat)
  | convert (dst src : String) (outElem : ElemType)
  | returnOp (src : String)
  deriving DecidableEq, Repr, Inhabited

/-- A StableHLO function: named parameters, a result type, and a straight-line body. -/
structure FuncOp where
  name    : String
  params  : List (String × TensorType)
  result  : TensorType
  body    : List StableHLOOp
  deriving DecidableEq, Repr, Inhabited

/-- A StableHLO module. -/
structure ModuleOp where
  name  : String
  funcs : List FuncOp
  deriving DecidableEq, Repr, Inhabited

/-- Shape or type mismatch reported by the independent interpreter. -/
inductive ShapeError where
  | unbound (name : String)
  | typeMismatch (expected got : TensorType)
  | shapeMismatch (detail : String)
  | rankMismatch (expected got : Nat)
  | volumeMismatch (expected got : Nat)
  | divisionByZero
  deriving DecidableEq, Repr, Inhabited, BEq

abbrev Env := String → Option TensorVal

def Env.empty : Env := fun _ => none

def Env.bind (env : Env) (name : String) (v : TensorVal) : Env :=
  fun n => if n == name then some v else env n

/-- SSA name to tensor type, threaded through the pretty-printer. -/
abbrev TypeEnv := String → Option TensorType

def TypeEnv.empty : TypeEnv := fun _ => none

def TypeEnv.bind (env : TypeEnv) (name : String) (ty : TensorType) : TypeEnv :=
  fun n => if n == name then some ty else env n

/-- Storage width of an element, including IEEE bit widths. Integer ops must not use this. -/
def storageBitWidth : ElemType → Nat
  | .i1 => 1 | .i8 | .ui8 => 8 | .i16 | .ui16 | .bf16 => 16
  | .i32 | .ui32 | .f32 => 32 | .i64 | .ui64 | .f64 => 64

/-- Integer arithmetic width. `none` for every floating type, so integer ops cannot touch floats. -/
def intBitWidth? : ElemType → Option Nat
  | .i1 => some 1 | .i8 | .ui8 => some 8 | .i16 | .ui16 => some 16
  | .i32 | .ui32 => some 32 | .i64 | .ui64 => some 64
  | .f32 | .f64 | .bf16 => none

/-- StableHLO signed integers. `i1` is a signless boolean `{0, 1}`, never signed. -/
def isSigned : ElemType → Bool
  | .i8 | .i16 | .i32 | .i64 => true
  | _ => false

def isFloat : ElemType → Bool
  | .f32 | .f64 | .bf16 => true
  | _ => false

end LeanNative.Backend.StableHLOAst
