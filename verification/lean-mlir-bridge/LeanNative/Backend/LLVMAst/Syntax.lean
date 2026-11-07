import LeanNative.Backend.TargetIR

namespace LeanNative.Backend.LLVMAst

open LeanNative.Backend.TargetIR

inductive ICmpPred where
  | eq | ne | ult | ule | ugt | uge | slt | sle | sgt | sge
  deriving Repr, DecidableEq, Inhabited

inductive FCmpPred where
  | oeq | one | olt | ole | ogt | oge | ord | uno | ueq | une | ult | ule | ugt | uge | true_ | false_
  deriving Repr, DecidableEq, Inhabited

inductive OverflowFlags where
  | none | nsw | nuw | nswNuw
  deriving Repr, DecidableEq, Inhabited

inductive AtomicRMWOp where
  | add | sub | and_ | or_ | xor | nand | max | min | umax | umin | xchg
  deriving Repr, DecidableEq, Inhabited

inductive AtomicOrdering where
  | monotonic | acquire | release | acqRel | seqCst
  deriving Repr, DecidableEq, Inhabited

inductive CallingConv where
  | ccc | fastcc | coldcc
  deriving Repr, DecidableEq, Inhabited

inductive ParamAttr where
  | zeroext | signext | noalias | noundef | readonly | writeonly | nocapture
  deriving Repr, DecidableEq, Inhabited

mutual
inductive LLVMType where
  | void
  | int : IntWidth → LLVMType
  | float : FloatWidth → LLVMType
  | ptr : AddrSpace → LLVMType
  | structFields : Bool → LLVMTypeFields → LLVMType
  | array : Nat → LLVMType → LLVMType
  | vec : Nat → LLVMType → LLVMType
  deriving Repr, DecidableEq, Inhabited

inductive LLVMTypeFields where
  | nil : LLVMTypeFields
  | cons : LLVMType → LLVMTypeFields → LLVMTypeFields
  deriving Repr, DecidableEq, Inhabited
end

namespace LLVMTypeFields

def ofList : List LLVMType → LLVMTypeFields
  | [] => .nil
  | h :: rest => .cons h (ofList rest)

end LLVMTypeFields

namespace LLVMType

def struct (fields : List LLVMType) (packed : Bool := false) : LLVMType :=
  .structFields packed (LLVMTypeFields.ofList fields)

mutual
def sizeOfType : LLVMType → Nat
  | .void => 0
  | .int _ | .float _ | .ptr _ => 1
  | .structFields _ fs => 1 + sizeOfFields fs
  | .array _ et => 1 + sizeOfType et
  | .vec _ et => 1 + sizeOfType et

def sizeOfFields : LLVMTypeFields → Nat
  | .nil => 1
  | .cons h t => 1 + sizeOfType h + sizeOfFields t
end

mutual
def bitSize : LLVMType → Nat
  | .void => 0
  | .int w => w.bits
  | .float fw => fw.bits
  | .ptr _ => 64
  | .structFields _ fs => fieldsBitSize fs
  | .array n et => n * et.bitSize
  | .vec n et => n * et.bitSize

def fieldsBitSize : LLVMTypeFields → Nat
  | .nil => 0
  | .cons h t => h.bitSize + fieldsBitSize t
end

mutual
def abiAlign : LLVMType → Nat
  | .void => 1
  | .int w => w.naturalAlign
  | .float fw => fw.naturalAlign
  | .ptr _ => 8
  | .structFields true _ => 1
  | .structFields false fs => fieldsAbiAlign fs
  | .array _ et => et.abiAlign
  | .vec n et => nextPow2 ((n * et.bitSize + 7) / 8)

def fieldsAbiAlign : LLVMTypeFields → Nat
  | .nil => 1
  | .cons h t => Nat.max h.abiAlign (fieldsAbiAlign t)
end

mutual
def byteSize : LLVMType → Nat
  | .void => 0
  | .int w => w.byteSize
  | .float fw => fw.byteSize
  | .ptr _ => 8
  | .structFields packed fs =>
    let rawEnd := fieldsRawEnd packed fs 0
    if packed then rawEnd
    else ByteMem.alignUp rawEnd (fieldsAbiAlign fs)
  | .array n et => n * et.byteSize
  | .vec n et =>
    let bits := n * et.bitSize
    if bits == 0 then 0 else nextPow2 ((bits + 7) / 8)

def fieldsRawEnd : Bool → LLVMTypeFields → Nat → Nat
  | _, .nil, cur => cur
  | packed, .cons h t, cur =>
    let off := if packed then cur else ByteMem.alignUp cur h.abiAlign
    fieldsRawEnd packed t (off + h.byteSize)
end

def structFieldTy : LLVMTypeFields → Nat → Option LLVMType
  | .cons h _, 0 => some h
  | .cons _ t, i + 1 => structFieldTy t i
  | .nil, _ => none

def structFieldOffsetAux (packed : Bool) : LLVMTypeFields → Nat → Nat → Option Nat
  | .nil, _, _ => none
  | .cons h _, 0, cur =>
    some (if packed then cur else ByteMem.alignUp cur h.abiAlign)
  | .cons h t, i + 1, cur =>
    let off := if packed then cur else ByteMem.alignUp cur h.abiAlign
    structFieldOffsetAux packed t i (off + h.byteSize)

def structFieldOffset (packed : Bool) (fs : LLVMTypeFields) (idx : Nat) : Option Nat :=
  structFieldOffsetAux packed fs idx 0

end LLVMType

inductive Operand where
  | reg : RegName → Operand
  | global : GlobalSym → Operand
  | constInt : (w : IntWidth) → BitVec w.bits → Operand
  | constFloat : (fw : FloatWidth) → BitVec fw.bits → Operand
  | constNull : Operand
  | constUndef : Operand
  | constZero : Operand
  | aggNil : Operand
  | aggCons : Operand → Operand → Operand
  | poison : Operand
  deriving Repr, DecidableEq, Inhabited

def Operand.constAgg (ops : List Operand) : Operand :=
  ops.foldr .aggCons .aggNil

inductive LLVMInstr where
  | alloca : RegName → LLVMType → Nat → LLVMInstr
  | load : RegName → Bool → LLVMType → Operand → Nat → (as_ : AddrSpace := 0) → LLVMInstr
  | store : Bool → LLVMType → Operand → Operand → Nat → (as_ : AddrSpace := 0) → LLVMInstr
  | add : RegName → OverflowFlags → IntWidth → Operand → Operand → LLVMInstr
  | sub : RegName → OverflowFlags → IntWidth → Operand → Operand → LLVMInstr
  | mul : RegName → OverflowFlags → IntWidth → Operand → Operand → LLVMInstr
  | udiv : RegName → Bool → IntWidth → Operand → Operand → LLVMInstr
  | sdiv : RegName → Bool → IntWidth → Operand → Operand → LLVMInstr
  | urem : RegName → IntWidth → Operand → Operand → LLVMInstr
  | srem : RegName → IntWidth → Operand → Operand → LLVMInstr
  | and_ : RegName → IntWidth → Operand → Operand → LLVMInstr
  | or_ : RegName → IntWidth → Operand → Operand → LLVMInstr
  | xor : RegName → IntWidth → Operand → Operand → LLVMInstr
  | shl : RegName → OverflowFlags → IntWidth → Operand → Operand → LLVMInstr
  | lshr : RegName → Bool → IntWidth → Operand → Operand → LLVMInstr
  | ashr : RegName → Bool → IntWidth → Operand → Operand → LLVMInstr
  | icmp : RegName → ICmpPred → LLVMType → Operand → Operand → LLVMInstr
  | fadd : RegName → FloatWidth → Operand → Operand → LLVMInstr
  | fsub : RegName → FloatWidth → Operand → Operand → LLVMInstr
  | fmul : RegName → FloatWidth → Operand → Operand → LLVMInstr
  | fdiv : RegName → FloatWidth → Operand → Operand → LLVMInstr
  | fcmp : RegName → FCmpPred → FloatWidth → Operand → Operand → LLVMInstr
  | zext : RegName → IntWidth → Operand → IntWidth → LLVMInstr
  | sext : RegName → IntWidth → Operand → IntWidth → LLVMInstr
  | trunc : RegName → IntWidth → Operand → IntWidth → LLVMInstr
  | bitcast : RegName → LLVMType → Operand → LLVMType → LLVMInstr
  | inttoptr : RegName → IntWidth → Operand → AddrSpace → LLVMInstr
  | ptrtoint : RegName → AddrSpace → Operand → IntWidth → LLVMInstr
  | getelementptr : RegName → Bool → LLVMType → Operand → List (IntWidth × Operand) →
      (as_ : AddrSpace := 0) → LLVMInstr
  | select : RegName → Operand → LLVMType → Operand → Operand → LLVMInstr
  | call : Option RegName → LLVMType → GlobalSym → List (LLVMType × Operand) →
      (cc : CallingConv := .ccc) → LLVMInstr
  | atomicrmw : RegName → AtomicRMWOp → Operand → LLVMType → Operand → AtomicOrdering → Nat →
      (as_ : AddrSpace := 0) → LLVMInstr
  | insertelement : RegName → Nat → LLVMType → Operand → Operand → IntWidth → Operand → LLVMInstr
  | extractelement : RegName → Nat → LLVMType → Operand → IntWidth → Operand → LLVMInstr
  | shufflevector : RegName → Nat → Nat → LLVMType → Operand → Operand → List Nat → LLVMInstr
  | insertvalue : RegName → LLVMType → Operand → LLVMType → Operand → List Nat → LLVMInstr
  | extractvalue : RegName → LLVMType → Operand → List Nat → LLVMInstr
  deriving Repr, DecidableEq, Inhabited

inductive Terminator where
  | br : BlockLabel → Terminator
  | condBr : Operand → BlockLabel → BlockLabel → Terminator
  | switch : (w : IntWidth) → Operand → BlockLabel → List (BitVec w.bits × BlockLabel) → Terminator
  | ret : Option (LLVMType × Operand) → Terminator
  | unreachable : Terminator
  deriving Repr, DecidableEq, Inhabited

structure PhiNode where
  dst : RegName
  ty : LLVMType
  incomings : List (Operand × BlockLabel)
  deriving Repr, DecidableEq, Inhabited

structure LLVMBlock where
  label : BlockLabel
  phis : List PhiNode := []
  body : List LLVMInstr := []
  term : Terminator
  deriving Repr, DecidableEq, Inhabited

structure LLVMParam where
  name : RegName
  ty : LLVMType
  attrs : List ParamAttr := []
  deriving Repr, DecidableEq, Inhabited

structure LLVMFn where
  name : GlobalSym
  retTy : LLVMType
  params : List LLVMParam
  cc : CallingConv := .ccc
  blocks : List LLVMBlock
  deriving Repr, DecidableEq, Inhabited

inductive Linkage where
  | external | private_ | internal | weakOdr
  deriving Repr, DecidableEq, Inhabited

structure LLVMGlobal where
  name : GlobalSym
  ty : LLVMType
  linkage : Linkage := .external
  isConstant : Bool := false
  init : Option Operand := none
  align : Nat := 0
  deriving Repr, DecidableEq, Inhabited

structure LLVMExtern where
  name : GlobalSym
  retTy : LLVMType
  paramTys : List LLVMType
  deriving Repr, DecidableEq, Inhabited

structure LLVMModule where
  dataLayout : String := ""
  triple : String := ""
  globals : List LLVMGlobal := []
  externs : List LLVMExtern := []
  fns : List LLVMFn := []
  deriving Repr, DecidableEq, Inhabited

inductive LLVMVal where
  | bits : (w : IntWidth) → BitVec w.bits → LLVMVal
  | ptr : BitVec 64 → LLVMVal
  | floatBits : (fw : FloatWidth) → BitVec fw.bits → LLVMVal
  | aggNil : LLVMVal
  | aggCons : LLVMVal → LLVMVal → LLVMVal
  | poison : LLVMVal
  deriving Repr, DecidableEq, Inhabited

def LLVMVal.agg (vs : List LLVMVal) : LLVMVal :=
  vs.foldr .aggCons .aggNil

def LLVMVal.toList? : LLVMVal → Option (List LLVMVal)
  | .aggNil => some []
  | .aggCons h t =>
    match t.toList? with
    | some rest => some (h :: rest)
    | none => none
  | _ => none

def LLVMVal.ofList : List LLVMVal → LLVMVal
  | [] => .aggNil
  | h :: rest => .aggCons h (ofList rest)

mutual
def LLVMVal.zeroOf : LLVMType → LLVMVal
  | .void => .aggNil
  | .int w => .bits w (BitVec.ofNat w.bits 0)
  | .float fw => .floatBits fw (BitVec.ofNat fw.bits 0)
  | .ptr _ => .ptr 0#64
  | .structFields _ fs => zeroOfFields fs
  | .array n et => LLVMVal.ofList (List.replicate n (zeroOf et))
  | .vec n et => LLVMVal.ofList (List.replicate n (zeroOf et))

def LLVMVal.zeroOfFields : LLVMTypeFields → LLVMVal
  | .nil => .aggNil
  | .cons h t => .aggCons (LLVMVal.zeroOf h) (LLVMVal.zeroOfFields t)
end

mutual
def LLVMVal.undefOf : LLVMType → LLVMVal
  | .void => .aggNil
  | .int w => .bits w (BitVec.ofNat w.bits 0)
  | .float fw => .floatBits fw (BitVec.ofNat fw.bits 0)
  | .ptr _ => .ptr 0#64
  | .structFields _ fs => undefOfFields fs
  | .array n et => LLVMVal.ofList (List.replicate n (undefOf et))
  | .vec n et => LLVMVal.ofList (List.replicate n (undefOf et))

def LLVMVal.undefOfFields : LLVMTypeFields → LLVMVal
  | .nil => .aggNil
  | .cons h t => .aggCons (LLVMVal.undefOf h) (LLVMVal.undefOfFields t)
end

inductive ExecOutcome where
  | returned : Option LLVMVal → ExecOutcome
  | ub : String → ExecOutcome
  | outOfFuel : ExecOutcome
  deriving Repr, DecidableEq, Inhabited

structure ExecState where
  regs : List (RegName × LLVMVal) := []
  globals : List (GlobalSym × BitVec 64) := []
  mem : ByteMem := {}
  prevBlock : Option BlockLabel := none
  deriving Repr, DecidableEq, Inhabited

def repeatMapIdx {α : Type} (n : Nat) (f : Nat → α) : List α :=
  go 0 n
where
  go (i : Nat) : Nat → List α
    | 0 => []
    | k + 1 => f i :: go (i + 1) k

end LeanNative.Backend.LLVMAst
