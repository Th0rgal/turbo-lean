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
  | structFields : LLVMTypeFields → LLVMType
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

def struct (fields : List LLVMType) : LLVMType :=
  .structFields (LLVMTypeFields.ofList fields)

def byteSize : LLVMType → Nat
  | .void => 0
  | .int w => w.byteSize
  | .float fw => fw.byteSize
  | .ptr _ => 8
  | .structFields fs => fieldsByteSize fs
  | .array n et => n * et.byteSize
  | .vec n et => n * et.byteSize
where
  fieldsByteSize : LLVMTypeFields → Nat
    | .nil => 0
    | .cons h t => h.byteSize + fieldsByteSize t

def bitSize : LLVMType → Nat
  | .void => 0
  | .int w => w.bits
  | .float fw => fw.bits
  | .ptr _ => 64
  | .structFields fs => fieldsBitSize fs
  | .array n et => n * et.bitSize
  | .vec n et => n * et.bitSize
where
  fieldsBitSize : LLVMTypeFields → Nat
    | .nil => 0
    | .cons h t => h.bitSize + fieldsBitSize t

def structFieldTy : LLVMTypeFields → Nat → Option LLVMType
  | .cons h _, 0 => some h
  | .cons _ t, i + 1 => structFieldTy t i
  | .nil, _ => none

def structFieldOffset : LLVMTypeFields → Nat → Option Nat
  | .cons _ _, 0 => some 0
  | .cons h t, i + 1 => (structFieldOffset t i).map (fun o => h.byteSize + o)
  | .nil, _ => none

end LLVMType

inductive Operand where
  | reg : RegName → Operand
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
  | load : RegName → Bool → LLVMType → Operand → Nat → LLVMInstr
  | store : Bool → LLVMType → Operand → Operand → Nat → LLVMInstr
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
  | getelementptr : RegName → Bool → LLVMType → Operand → List (IntWidth × Operand) → LLVMInstr
  | select : RegName → Operand → LLVMType → Operand → Operand → LLVMInstr
  | call : Option RegName → LLVMType → GlobalSym → List (LLVMType × Operand) → LLVMInstr
  | atomicrmw : RegName → AtomicRMWOp → Operand → LLVMType → Operand → AtomicOrdering → Nat → LLVMInstr
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

def LLVMVal.zeroOf : LLVMType → LLVMVal
  | .void => .aggNil
  | .int w => .bits w (BitVec.ofNat w.bits 0)
  | .float fw => .floatBits fw (BitVec.ofNat fw.bits 0)
  | .ptr _ => .ptr 0#64
  | .structFields fs => zeroFields fs
  | .array n et => LLVMVal.ofList (List.replicate n (zeroOf et))
  | .vec n et => LLVMVal.ofList (List.replicate n (zeroOf et))
where
  zeroFields : LLVMTypeFields → LLVMVal
    | .nil => .aggNil
    | .cons h t => .aggCons (zeroOf h) (zeroFields t)

def LLVMVal.undefOf : LLVMType → LLVMVal
  | .void => .aggNil
  | .int w => .bits w (BitVec.ofNat w.bits 0)
  | .float fw => .floatBits fw (BitVec.ofNat fw.bits 0)
  | .ptr _ => .ptr 0#64
  | .structFields fs => undefFields fs
  | .array n et => LLVMVal.ofList (List.replicate n (undefOf et))
  | .vec n et => LLVMVal.ofList (List.replicate n (undefOf et))
where
  undefFields : LLVMTypeFields → LLVMVal
    | .nil => .aggNil
    | .cons h t => .aggCons (undefOf h) (undefFields t)

inductive ExecOutcome where
  | returned : Option LLVMVal → ExecOutcome
  | ub : String → ExecOutcome
  | outOfFuel : ExecOutcome
  deriving Repr, DecidableEq, Inhabited

structure ExecState where
  regs : List (RegName × LLVMVal) := []
  mem : ByteMem := {}
  prevBlock : Option BlockLabel := none
  deriving Repr, DecidableEq, Inhabited

def lookupReg (st : ExecState) (r : RegName) : Option LLVMVal :=
  st.regs.lookup r

def bindReg (st : ExecState) (r : RegName) (v : LLVMVal) : ExecState :=
  { st with regs := (r, v) :: st.regs }

def evalOperand (st : ExecState) : Operand → LLVMVal
  | .reg r => (lookupReg st r).getD .poison
  | .constInt w v => .bits w v
  | .constFloat fw v => .floatBits fw v
  | .constNull => .ptr 0#64
  | .constUndef => .poison
  | .constZero => .aggNil
  | .aggNil => .aggNil
  | .aggCons h t => .aggCons (evalOperand st h) (evalOperand st t)
  | .poison => .poison

def evalTypedOperand (st : ExecState) (ty : LLVMType) (op : Operand) : LLVMVal :=
  match op with
  | .constZero => LLVMVal.zeroOf ty
  | .constUndef => LLVMVal.undefOf ty
  | .aggNil =>
    match ty with
    | .array _ _ | .vec _ _ | .structFields _ => LLVMVal.zeroOf ty
    | _ => .aggNil
  | .aggCons h t =>
    match ty with
    | .structFields (.cons hty tty) => .aggCons (evalTypedOperand st hty h) (evalTypedOperand st (.structFields tty) t)
    | .array (k + 1) et => .aggCons (evalTypedOperand st et h) (evalTypedOperand st (.array k et) t)
    | .vec (k + 1) et => .aggCons (evalTypedOperand st et h) (evalTypedOperand st (.vec k et) t)
    | _ => .aggCons (evalOperand st h) (evalOperand st t)
  | _ => evalOperand st op

def asBits (w : IntWidth) : LLVMVal → Option (BitVec w.bits)
  | .bits w' v => if h : w' = w then some (h ▸ v) else none
  | .poison => none
  | _ => none

def isPoison (v : LLVMVal) : Bool :=
  match v with
  | .poison => true
  | _ => false

def bvSigned (w : IntWidth) (v : BitVec w.bits) : Int :=
  let u : Int := Int.ofNat v.toNat
  let half : Int := (2 : Int) ^ (w.bits - 1)
  if u < half then u else u - (2 : Int) ^ w.bits

def addOverflowNSW (w : IntWidth) (a b : BitVec w.bits) : Bool :=
  let sum := bvSigned w a + bvSigned w b
  let lo := -((2 : Int) ^ (w.bits - 1))
  let hi := (2 : Int) ^ (w.bits - 1) - 1
  decide (sum < lo ∨ hi < sum)

def addOverflowNUW (w : IntWidth) (a b : BitVec w.bits) : Bool :=
  decide (2 ^ w.bits ≤ a.toNat + b.toNat)

def subOverflowNSW (w : IntWidth) (a b : BitVec w.bits) : Bool :=
  let diff := bvSigned w a - bvSigned w b
  let lo := -((2 : Int) ^ (w.bits - 1))
  let hi := (2 : Int) ^ (w.bits - 1) - 1
  decide (diff < lo ∨ hi < diff)

def subOverflowNUW (w : IntWidth) (a b : BitVec w.bits) : Bool :=
  decide (a.toNat < b.toNat)

def mulOverflowNSW (w : IntWidth) (a b : BitVec w.bits) : Bool :=
  let prod := bvSigned w a * bvSigned w b
  let lo := -((2 : Int) ^ (w.bits - 1))
  let hi := (2 : Int) ^ (w.bits - 1) - 1
  decide (prod < lo ∨ hi < prod)

def mulOverflowNUW (w : IntWidth) (a b : BitVec w.bits) : Bool :=
  decide (2 ^ w.bits ≤ a.toNat * b.toNat)

def flagsOverflow (flags : OverflowFlags) (nsw nuw : Bool) : Bool :=
  match flags with
  | .none => false
  | .nsw => nsw
  | .nuw => nuw
  | .nswNuw => nsw || nuw

def sdivOverflow (w : IntWidth) (a b : BitVec w.bits) : Bool :=
  bvSigned w a == -((2 : Int) ^ (w.bits - 1)) && bvSigned w b == -1

def bvSDiv (w : IntWidth) (a b : BitVec w.bits) : BitVec w.bits :=
  let sa := bvSigned w a
  let sb := bvSigned w b
  let q : Int := Int.tdiv sa sb
  if 0 ≤ q then BitVec.ofNat w.bits q.toNat
  else BitVec.ofNat w.bits (2 ^ w.bits - (-q).toNat % 2 ^ w.bits)

def bvSRem (w : IntWidth) (a b : BitVec w.bits) : BitVec w.bits :=
  let sa := bvSigned w a
  let sb := bvSigned w b
  let r : Int := Int.tmod sa sb
  if 0 ≤ r then BitVec.ofNat w.bits r.toNat
  else BitVec.ofNat w.bits (2 ^ w.bits - (-r).toNat % 2 ^ w.bits)

def shlOverflowNUW (w : IntWidth) (a amt : BitVec w.bits) : Bool :=
  let shifted : BitVec w.bits := a <<< amt
  (shifted >>> amt) != a

def shlOverflowNSW (w : IntWidth) (a amt : BitVec w.bits) : Bool :=
  let prod := bvSigned w a * ((2 : Int) ^ amt.toNat)
  let lo := -((2 : Int) ^ (w.bits - 1))
  let hi := (2 : Int) ^ (w.bits - 1) - 1
  decide (prod < lo ∨ hi < prod)

def evalRMWOp (op : AtomicRMWOp) (w : IntWidth) (old val : BitVec w.bits) : BitVec w.bits :=
  match op with
  | .add => old + val
  | .sub => old - val
  | .and_ => old &&& val
  | .or_ => old ||| val
  | .xor => old ^^^ val
  | .nand => ~~~(old &&& val)
  | .max => if bvSigned w old < bvSigned w val then val else old
  | .min => if bvSigned w val < bvSigned w old then val else old
  | .umax => if old.toNat < val.toNat then val else old
  | .umin => if val.toNat < old.toNat then val else old
  | .xchg => val

def icmpEval (p : ICmpPred) (w : IntWidth) (a b : BitVec w.bits) : Bool :=
  match p with
  | .eq => a == b
  | .ne => a != b
  | .ult => a.toNat < b.toNat
  | .ule => a.toNat ≤ b.toNat
  | .ugt => b.toNat < a.toNat
  | .uge => b.toNat ≤ a.toNat
  | .slt => bvSigned w a < bvSigned w b
  | .sle => bvSigned w a ≤ bvSigned w b
  | .sgt => bvSigned w b < bvSigned w a
  | .sge => bvSigned w b ≤ bvSigned w a

def f64IsNaN (b : BitVec 64) : Bool :=
  (Float.ofBits b.toNat.toUInt64).isNaN

def f32IsNaN (b : BitVec 32) : Bool :=
  (Float32.ofBits b.toNat.toUInt32).isNaN

def f64SignBit (b : BitVec 64) : Bool :=
  b.getLsbD 63

def f32SignBit (b : BitVec 32) : Bool :=
  b.getLsbD 31

def fcmpEval : FCmpPred → (fw : FloatWidth) → BitVec fw.bits → BitVec fw.bits → Bool
  | p, .f64, a, b =>
    let aNaN := f64IsNaN a
    let bNaN := f64IsNaN b
    let unordered := aNaN || bNaN
    let fa := Float.ofBits a.toNat.toUInt64
    let fb := Float.ofBits b.toNat.toUInt64
    let eqAB := fa == fb
    let ltAB := fa < fb
    match p with
    | .false_ => false
    | .true_ => true
    | .uno => unordered
    | .ord => !unordered
    | .oeq => !unordered && eqAB
    | .one => !unordered && !eqAB
    | .olt => !unordered && ltAB
    | .ole => !unordered && (ltAB || eqAB)
    | .ogt => !unordered && !ltAB && !eqAB
    | .oge => !unordered && !ltAB
    | .ueq => unordered || eqAB
    | .une => unordered || !eqAB
    | .ult => unordered || ltAB
    | .ule => unordered || ltAB || eqAB
    | .ugt => unordered || (!ltAB && !eqAB)
    | .uge => unordered || !ltAB
  | p, .f32, a, b =>
    let aNaN := f32IsNaN a
    let bNaN := f32IsNaN b
    let unordered := aNaN || bNaN
    let fa := Float32.ofBits a.toNat.toUInt32
    let fb := Float32.ofBits b.toNat.toUInt32
    let eqAB := fa == fb
    let ltAB := fa < fb
    match p with
    | .false_ => false
    | .true_ => true
    | .uno => unordered
    | .ord => !unordered
    | .oeq => !unordered && eqAB
    | .one => !unordered && !eqAB
    | .olt => !unordered && ltAB
    | .ole => !unordered && (ltAB || eqAB)
    | .ogt => !unordered && !ltAB && !eqAB
    | .oge => !unordered && !ltAB
    | .ueq => unordered || eqAB
    | .une => unordered || !eqAB
    | .ult => unordered || ltAB
    | .ule => unordered || ltAB || eqAB
    | .ugt => unordered || (!ltAB && !eqAB)
    | .uge => unordered || !ltAB

def f64Bin (op : String) (a b : BitVec 64) : BitVec 64 :=
  let fa := Float.ofBits a.toNat.toUInt64
  let fb := Float.ofBits b.toNat.toUInt64
  let fr := match op with
    | "add" => fa + fb
    | "sub" => fa - fb
    | "mul" => fa * fb
    | _ => fa / fb
  BitVec.ofNat 64 fr.toBits.toNat

def f32Bin (op : String) (a b : BitVec 32) : BitVec 32 :=
  let fa := Float32.ofBits a.toNat.toUInt32
  let fb := Float32.ofBits b.toNat.toUInt32
  let fr := match op with
    | "add" => fa + fb
    | "sub" => fa - fb
    | "mul" => fa * fb
    | _ => fa / fb
  BitVec.ofNat 32 fr.toBits.toNat

def serializeVal : LLVMVal → List MemByte
  | .bits w bv => ByteMem.initBytes (ByteMem.bvToLEBytes w.byteSize bv)
  | .ptr p => ByteMem.initBytes (ByteMem.bvToLEBytes 8 p)
  | .floatBits fw fb => ByteMem.initBytes (ByteMem.bvToLEBytes fw.byteSize fb)
  | .poison => ByteMem.poisonBytes 1
  | .aggNil => []
  | .aggCons h t => serializeVal h ++ serializeVal t

def deserializeVal (ty : LLVMType) (bs : List MemByte) : LLVMVal :=
  match ty with
  | .void => .aggNil
  | .int w =>
    match ByteMem.bytesToBv? w.bits (bs.take w.byteSize) with
    | some v => .bits w v
    | none => .poison
  | .ptr _ =>
    match ByteMem.bytesToBv? 64 (bs.take 8) with
    | some v => .ptr v
    | none => .poison
  | .float fw =>
    match ByteMem.bytesToBv? fw.bits (bs.take fw.byteSize) with
    | some v => .floatBits fw v
    | none => .poison
  | .structFields fs => deserializeFields fs bs
  | .array n et => deserializeElems n et bs
  | .vec n et => deserializeElems n et bs
where
  deserializeFields : LLVMTypeFields → List MemByte → LLVMVal
    | .nil, _ => .aggNil
    | .cons h t, bs =>
      let n := h.byteSize
      .aggCons (deserializeVal h (bs.take n)) (deserializeFields t (bs.drop n))
  deserializeElems : Nat → LLVMType → List MemByte → LLVMVal
    | 0, _, _ => .aggNil
    | k + 1, et, bs =>
      let n := et.byteSize
      .aggCons (deserializeVal et (bs.take n)) (deserializeElems k et (bs.drop n))

def storeVal (m : ByteMem) (addr : BitVec 64) (v : LLVMVal) : ByteMem :=
  m.writeBytesAt addr.toNat (serializeVal v)

def loadVal (m : ByteMem) (addr : BitVec 64) (ty : LLVMType) : LLVMVal :=
  deserializeVal ty (m.readBytesAt addr.toNat ty.byteSize)

def gepIndexSigned (w : IntWidth) (v : BitVec w.bits) : Int :=
  bvSigned w v

def gepOffset (baseTy : LLVMType) (idxs : List (Int × IntWidth)) : Option Int :=
  match idxs with
  | [] => some 0
  | (i0, _) :: rest =>
    let step0 : Int := Int.ofNat baseTy.byteSize * i0
    match rest with
    | [] => some step0
    | _ =>
      match walk baseTy rest with
      | some inner => some (step0 + inner)
      | none => none
where
  walk : LLVMType → List (Int × IntWidth) → Option Int
    | _, [] => some 0
    | .array _ et, (i, _) :: rest =>
      match walk et rest with
      | some inner => some (Int.ofNat et.byteSize * i + inner)
      | none => none
    | .structFields fs, (i, w) :: rest =>
      if w == .i32 then
        if 0 ≤ i then
          match LLVMType.structFieldOffset fs i.toNat, LLVMType.structFieldTy fs i.toNat with
          | some off, some fty =>
            match walk fty rest with
            | some inner => some (Int.ofNat off + inner)
            | none => none
          | _, _ => none
        else none
      else none
    | _, _ => none

def bitcastVal (srcTy dstTy : LLVMType) (v : LLVMVal) : Option LLVMVal :=
  if srcTy.bitSize != dstTy.bitSize then none
  else if isPoison v then some .poison
  else
    let bs := serializeVal v
    if bs.length * 8 < dstTy.bitSize then none
    else some (deserializeVal dstTy bs)

def bswapBytes (w : IntWidth) (v : BitVec w.bits) : BitVec w.bits :=
  let rec go : Nat → Nat → Nat → Nat
    | 0, _, acc => acc
    | k + 1, src, acc => go k (src / 256) (acc * 256 + src % 256)
  BitVec.ofNat w.bits (go w.byteSize v.toNat 0)

def ctlzBits (w : IntWidth) (v : BitVec w.bits) : BitVec w.bits :=
  let rec go : Nat → Nat
    | 0 => w.bits
    | k + 1 => if v.getLsbD k then w.bits - 1 - k else go k
  BitVec.ofNat w.bits (go w.bits)

def uaddOverflow (w : IntWidth) (a b : BitVec w.bits) : LLVMVal :=
  let sum := a + b
  let ov : BitVec 1 := if addOverflowNUW w a b then 1#1 else 0#1
  .aggCons (.bits w sum) (.aggCons (.bits .i1 ov) .aggNil)

structure ExtResult where
  dst : Option LLVMVal
  mem : ByteMem
  deriving Repr, DecidableEq

def extOracle : GlobalSym → List LLVMVal → ByteMem → Option ExtResult :=
  fun _ _ _ => none

def resolvePhi (st : ExecState) (ty : LLVMType) (prev : Option BlockLabel) (incomings : List (Operand × BlockLabel)) : LLVMVal :=
  match prev with
  | none => .poison
  | some lbl =>
    match incomings.find? (fun pair => pair.snd == lbl) with
    | none => .poison
    | some (op, _) => evalTypedOperand st ty op

def evalPhis (st : ExecState) (prev : Option BlockLabel) (phis : List PhiNode) : List (RegName × LLVMVal) :=
  phis.map fun phi => (phi.dst, resolvePhi st phi.ty prev phi.incomings)

def commitPhis (st : ExecState) (binds : List (RegName × LLVMVal)) : ExecState :=
  binds.foldl (fun acc (r, v) => bindReg acc r v) st

def bindArgs (st : ExecState) : List LLVMParam → List LLVMVal → Option ExecState
  | [], [] => some st
  | p :: ps, v :: vs => bindArgs (bindReg st p.name v) ps vs
  | _, _ => none

def findBlock (fn : LLVMFn) (lbl : BlockLabel) : Option LLVMBlock :=
  fn.blocks.find? (fun b => b.label == lbl)

def binResult (dst : RegName) (st : ExecState) (w : IntWidth) (flags : OverflowFlags)
    (a b : LLVMVal) (kind : String) : ExecOutcome ⊕ ExecState :=
  match a, b with
  | .poison, _ => .inr (bindReg st dst .poison)
  | _, .poison => .inr (bindReg st dst .poison)
  | .bits wa va, .bits wb vb =>
    if ha : wa = w then
      if hb : wb = w then
        let va' : BitVec w.bits := ha ▸ va
        let vb' : BitVec w.bits := hb ▸ vb
        let nsw := match kind with
          | "add" => addOverflowNSW w va' vb'
          | "sub" => subOverflowNSW w va' vb'
          | "mul" => mulOverflowNSW w va' vb'
          | _ => false
        let nuw := match kind with
          | "add" => addOverflowNUW w va' vb'
          | "sub" => subOverflowNUW w va' vb'
          | "mul" => mulOverflowNUW w va' vb'
          | _ => false
        let res := match kind with
          | "add" => va' + vb'
          | "sub" => va' - vb'
          | "mul" => va' * vb'
          | "and" => va' &&& vb'
          | "or" => va' ||| vb'
          | "xor" => va' ^^^ vb'
          | _ => va'
        if flagsOverflow flags nsw nuw then .inr (bindReg st dst .poison)
        else .inr (bindReg st dst (.bits w res))
      else .inl (.ub "operand width mismatch")
    else .inl (.ub "operand width mismatch")
  | _, _ => .inl (.ub "non-integer operand")

def divOrRem (dst : RegName) (st : ExecState) (w : IntWidth) (exact : Bool) (a b : LLVMVal)
    (signed isRem : Bool) : ExecOutcome ⊕ ExecState :=
  match a, b with
  | .poison, _ => .inr (bindReg st dst .poison)
  | _, .poison => .inr (bindReg st dst .poison)
  | .bits wa va, .bits wb vb =>
    if ha : wa = w then
      if hb : wb = w then
        let va' : BitVec w.bits := ha ▸ va
        let vb' : BitVec w.bits := hb ▸ vb
        if vb' == 0#w.bits then .inl (.ub "division by zero")
        else if signed && sdivOverflow w va' vb' then .inl (.ub "signed division overflow")
        else
          let res :=
            if signed then
              if isRem then bvSRem w va' vb' else bvSDiv w va' vb'
            else
              if isRem then va' % vb' else va' / vb'
          let inexact :=
            if isRem then false
            else if signed then bvSRem w va' vb' != 0#w.bits else va' % vb' != 0#w.bits
          if exact && inexact then .inr (bindReg st dst .poison)
          else .inr (bindReg st dst (.bits w res))
      else .inl (.ub "operand width mismatch")
    else .inl (.ub "operand width mismatch")
  | _, _ => .inl (.ub "non-integer operand")

def shiftResult (dst : RegName) (st : ExecState) (w : IntWidth) (flags : OverflowFlags)
    (exact : Bool) (a b : LLVMVal) (kind : String) : ExecOutcome ⊕ ExecState :=
  match a, b with
  | .poison, _ => .inr (bindReg st dst .poison)
  | _, .poison => .inr (bindReg st dst .poison)
  | .bits wa va, .bits wb vb =>
    if ha : wa = w then
      if hb : wb = w then
        let va' : BitVec w.bits := ha ▸ va
        let vb' : BitVec w.bits := hb ▸ vb
        if w.bits ≤ vb'.toNat then .inr (bindReg st dst .poison)
        else
          let res := match kind with
            | "shl" => va' <<< vb'
            | "ashr" => va'.sshiftRight vb'.toNat
            | _ => va' >>> vb'
          let shiftedOut := match kind with
            | "lshr" => (va' <<< (w.bits - vb'.toNat)) != 0#w.bits
            | "ashr" => (va' <<< (w.bits - vb'.toNat)) != 0#w.bits
            | _ => false
          let nsw := if kind == "shl" then shlOverflowNSW w va' vb' else false
          let nuw := if kind == "shl" then shlOverflowNUW w va' vb' else false
          if flagsOverflow flags nsw nuw then .inr (bindReg st dst .poison)
          else if exact && shiftedOut then .inr (bindReg st dst .poison)
          else .inr (bindReg st dst (.bits w res))
      else .inl (.ub "operand width mismatch")
    else .inl (.ub "operand width mismatch")
  | _, _ => .inl (.ub "non-integer operand")

def floatBinEval : (fw : FloatWidth) → String → BitVec fw.bits → BitVec fw.bits → BitVec fw.bits
  | .f64, kind, a, b => f64Bin kind a b
  | .f32, kind, a, b => f32Bin kind a b

def floatResult (dst : RegName) (st : ExecState) (fw : FloatWidth) (a b : LLVMVal)
    (kind : String) : ExecOutcome ⊕ ExecState :=
  match a, b with
  | .poison, _ => .inr (bindReg st dst .poison)
  | _, .poison => .inr (bindReg st dst .poison)
  | .floatBits fa va, .floatBits fb vb =>
    if hfa : fa = fw then
      if hfb : fb = fw then
        let res := floatBinEval fw kind (hfa ▸ va) (hfb ▸ vb)
        .inr (bindReg st dst (.floatBits fw res))
      else .inl (.ub "float width mismatch")
    else .inl (.ub "float width mismatch")
  | _, _ => .inl (.ub "float on non-float")

def accessCheck (m : ByteMem) (addr : BitVec 64) (n align : Nat) (needWrite : Bool) : Option String :=
  if addr == 0#64 then some "null pointer"
  else if align != 0 && !isAligned addr align then some "misaligned access"
  else if !m.accessInAlloc addr.toNat n needWrite then some "out of bounds access"
  else none

def gepResult (st : ExecState) (dst : RegName) (inbounds_ : Bool) (ty : LLVMType)
    (base : BitVec 64) (idxs : List (IntWidth × Operand)) : ExecOutcome ⊕ ExecState :=
  let evalIdx : IntWidth × Operand → Option (Int × IntWidth) := fun (w, op) =>
    match evalOperand st op with
    | .poison => none
    | .bits w' v => if h : w' = w then some (gepIndexSigned w (h ▸ v), w) else none
    | _ => none
  if idxs.any (fun pair => isPoison (evalOperand st pair.snd)) then
    .inr (bindReg st dst .poison)
  else
    match idxs.mapM evalIdx with
    | none => .inl (.ub "getelementptr index type mismatch")
    | some ixs =>
      match gepOffset ty ixs with
      | none => .inl (.ub "getelementptr ill-typed index")
      | some off =>
        let resAddr : Int := Int.ofNat base.toNat + off
        if inbounds_ && !st.mem.inboundsInAlloc base.toNat resAddr then
          .inr (bindReg st dst .poison)
        else if resAddr < 0 then
          .inl (.ub "getelementptr negative address")
        else
          .inr (bindReg st dst (.ptr (BitVec.ofNat 64 resAddr.toNat)))

def intrinsicResult (callee : GlobalSym) (args : List LLVMVal) : Option LLVMVal :=
  match callee, args with
  | "llvm.uadd.with.overflow.i64", [.bits .i64 a, .bits .i64 b] =>
    some (uaddOverflow .i64 a b)
  | "llvm.uadd.with.overflow.i256", [.bits .i256 a, .bits .i256 b] =>
    some (uaddOverflow .i256 a b)
  | "llvm.bswap.i64", [.bits .i64 a] => some (.bits .i64 (bswapBytes .i64 a))
  | "llvm.bswap.i256", [.bits .i256 a] => some (.bits .i256 (bswapBytes .i256 a))
  | "llvm.ctlz.i64", [.bits .i64 a, .bits .i1 z] =>
    if a == 0#64 && z == 1#1 then some .poison else some (.bits .i64 (ctlzBits .i64 a))
  | "llvm.ctlz.i256", [.bits .i256 a, .bits .i1 z] =>
    if a == 0#256 && z == 1#1 then some .poison else some (.bits .i256 (ctlzBits .i256 a))
  | _, _ => none

def stepInstrWith (runCall : ExecState → Option RegName → LLVMType → GlobalSym → List LLVMVal → ExecOutcome ⊕ ExecState)
    (st : ExecState) : LLVMInstr → ExecOutcome ⊕ ExecState
  | .alloca dst ty align =>
    match st.mem.allocAligned ty.byteSize (if isPow2 align then align else 1) with
    | none => .inl (.ub "alloca out of address space")
    | some (ptr, mem') => .inr (bindReg { st with mem := mem' } dst (.ptr ptr))
  | .load dst _volatile ty ptrOp align =>
    match evalOperand st ptrOp with
    | .poison => .inl (.ub "load from poison pointer")
    | .ptr addr =>
      match accessCheck st.mem addr ty.byteSize align false with
      | some "null pointer" => .inl (.ub "load from null pointer")
      | some "misaligned access" => .inl (.ub "misaligned load")
      | some _ => .inl (.ub "load out of bounds")
      | none => .inr (bindReg st dst (loadVal st.mem addr ty))
    | _ => .inl (.ub "load from non-pointer")
  | .store _volatile ty valOp ptrOp align =>
    let val := evalTypedOperand st ty valOp
    match evalOperand st ptrOp with
    | .poison => .inl (.ub "store to poison pointer")
    | .ptr addr =>
      match accessCheck st.mem addr ty.byteSize align true with
      | some "null pointer" => .inl (.ub "store to null pointer")
      | some "misaligned access" => .inl (.ub "misaligned store")
      | some _ => .inl (.ub "store out of bounds")
      | none => .inr { st with mem := storeVal st.mem addr val }
    | _ => .inl (.ub "store to non-pointer")
  | .add dst flags w aOp bOp =>
    binResult dst st w flags (evalOperand st aOp) (evalOperand st bOp) "add"
  | .sub dst flags w aOp bOp =>
    binResult dst st w flags (evalOperand st aOp) (evalOperand st bOp) "sub"
  | .mul dst flags w aOp bOp =>
    binResult dst st w flags (evalOperand st aOp) (evalOperand st bOp) "mul"
  | .udiv dst exact w aOp bOp =>
    divOrRem dst st w exact (evalOperand st aOp) (evalOperand st bOp) false false
  | .sdiv dst exact w aOp bOp =>
    divOrRem dst st w exact (evalOperand st aOp) (evalOperand st bOp) true false
  | .urem dst w aOp bOp =>
    divOrRem dst st w false (evalOperand st aOp) (evalOperand st bOp) false true
  | .srem dst w aOp bOp =>
    divOrRem dst st w false (evalOperand st aOp) (evalOperand st bOp) true true
  | .and_ dst w aOp bOp =>
    binResult dst st w .none (evalOperand st aOp) (evalOperand st bOp) "and"
  | .or_ dst w aOp bOp =>
    binResult dst st w .none (evalOperand st aOp) (evalOperand st bOp) "or"
  | .xor dst w aOp bOp =>
    binResult dst st w .none (evalOperand st aOp) (evalOperand st bOp) "xor"
  | .shl dst flags w aOp bOp =>
    shiftResult dst st w flags false (evalOperand st aOp) (evalOperand st bOp) "shl"
  | .lshr dst exact w aOp bOp =>
    shiftResult dst st w .none exact (evalOperand st aOp) (evalOperand st bOp) "lshr"
  | .ashr dst exact w aOp bOp =>
    shiftResult dst st w .none exact (evalOperand st aOp) (evalOperand st bOp) "ashr"
  | .icmp dst pred ty aOp bOp =>
    match ty with
    | .int w =>
      match evalOperand st aOp, evalOperand st bOp with
      | .poison, _ => .inr (bindReg st dst .poison)
      | _, .poison => .inr (bindReg st dst .poison)
      | .bits wa va, .bits wb vb =>
        if ha : wa = w then
          if hb : wb = w then
            let bit : BitVec 1 := if icmpEval pred w (ha ▸ va) (hb ▸ vb) then 1#1 else 0#1
            .inr (bindReg st dst (.bits .i1 bit))
          else .inl (.ub "icmp width mismatch")
        else .inl (.ub "icmp width mismatch")
      | _, _ => .inl (.ub "icmp on non-integer")
    | .ptr _ =>
      match evalOperand st aOp, evalOperand st bOp with
      | .poison, _ => .inr (bindReg st dst .poison)
      | _, .poison => .inr (bindReg st dst .poison)
      | .ptr a, .ptr b =>
        let bit : BitVec 1 := if icmpEval pred .i64 a b then 1#1 else 0#1
        .inr (bindReg st dst (.bits .i1 bit))
      | _, _ => .inl (.ub "icmp on non-pointer")
    | _ => .inl (.ub "icmp on unsupported type")
  | .fadd dst fw aOp bOp => floatResult dst st fw (evalOperand st aOp) (evalOperand st bOp) "add"
  | .fsub dst fw aOp bOp => floatResult dst st fw (evalOperand st aOp) (evalOperand st bOp) "sub"
  | .fmul dst fw aOp bOp => floatResult dst st fw (evalOperand st aOp) (evalOperand st bOp) "mul"
  | .fdiv dst fw aOp bOp => floatResult dst st fw (evalOperand st aOp) (evalOperand st bOp) "div"
  | .fcmp dst pred fw aOp bOp =>
    match evalOperand st aOp, evalOperand st bOp with
    | .poison, _ => .inr (bindReg st dst .poison)
    | _, .poison => .inr (bindReg st dst .poison)
    | .floatBits fa va, .floatBits fb vb =>
      if hfa : fa = fw then
        if hfb : fb = fw then
          let bit : BitVec 1 := if fcmpEval pred fw (hfa ▸ va) (hfb ▸ vb) then 1#1 else 0#1
          .inr (bindReg st dst (.bits .i1 bit))
        else .inl (.ub "fcmp width mismatch")
      else .inl (.ub "fcmp width mismatch")
    | _, _ => .inl (.ub "fcmp on non-float")
  | .zext dst srcW op dstW =>
    match evalOperand st op with
    | .poison => .inr (bindReg st dst .poison)
    | .bits w v =>
      if h : w = srcW then
        if srcW.bits ≤ dstW.bits then
          .inr (bindReg st dst (.bits dstW ((h ▸ v).zeroExtend dstW.bits)))
        else .inl (.ub "zext to narrower width")
      else .inl (.ub "zext source width mismatch")
    | _ => .inl (.ub "zext on non-integer")
  | .sext dst srcW op dstW =>
    match evalOperand st op with
    | .poison => .inr (bindReg st dst .poison)
    | .bits w v =>
      if h : w = srcW then
        if srcW.bits ≤ dstW.bits then
          .inr (bindReg st dst (.bits dstW ((h ▸ v).signExtend dstW.bits)))
        else .inl (.ub "sext to narrower width")
      else .inl (.ub "sext source width mismatch")
    | _ => .inl (.ub "sext on non-integer")
  | .trunc dst srcW op dstW =>
    match evalOperand st op with
    | .poison => .inr (bindReg st dst .poison)
    | .bits w v =>
      if h : w = srcW then
        if dstW.bits ≤ srcW.bits then
          .inr (bindReg st dst (.bits dstW ((h ▸ v).truncate dstW.bits)))
        else .inl (.ub "trunc to wider width")
      else .inl (.ub "trunc source width mismatch")
    | _ => .inl (.ub "trunc on non-integer")
  | .bitcast dst srcTy op dstTy =>
    match bitcastVal srcTy dstTy (evalTypedOperand st srcTy op) with
    | none => .inl (.ub "bitcast size mismatch")
    | some v => .inr (bindReg st dst v)
  | .inttoptr dst srcW op _as =>
    match evalOperand st op with
    | .poison => .inr (bindReg st dst .poison)
    | .bits w v =>
      if h : w = srcW then .inr (bindReg st dst (.ptr ((h ▸ v).zeroExtend 64)))
      else .inl (.ub "inttoptr width mismatch")
    | _ => .inl (.ub "inttoptr on non-integer")
  | .ptrtoint dst _as op dstW =>
    match evalOperand st op with
    | .poison => .inr (bindReg st dst .poison)
    | .ptr p => .inr (bindReg st dst (.bits dstW (p.truncate dstW.bits)))
    | _ => .inl (.ub "ptrtoint on non-pointer")
  | .getelementptr dst inbounds_ ty baseOp idxs =>
    match evalOperand st baseOp with
    | .poison => .inr (bindReg st dst .poison)
    | .ptr base => gepResult st dst inbounds_ ty base idxs
    | _ => .inl (.ub "getelementptr on non-pointer")
  | .select dst condOp ty tOp eOp =>
    match evalOperand st condOp with
    | .poison => .inr (bindReg st dst .poison)
    | .bits .i1 c =>
      if c == 1#1 then .inr (bindReg st dst (evalTypedOperand st ty tOp))
      else .inr (bindReg st dst (evalTypedOperand st ty eOp))
    | _ => .inl (.ub "select condition is not i1")
  | .call dst? retTy callee args =>
    let argVals := args.map fun pair => evalTypedOperand st pair.fst pair.snd
    runCall st dst? retTy callee argVals
  | .atomicrmw dst op ptrOp ty valOp _ord align =>
    match ty with
    | .int w =>
      match evalOperand st ptrOp with
      | .poison => .inl (.ub "atomicrmw on poison pointer")
      | .ptr addr =>
        match accessCheck st.mem addr w.byteSize align true with
        | some "null pointer" => .inl (.ub "atomicrmw on null pointer")
        | some "misaligned access" => .inl (.ub "misaligned atomicrmw")
        | some _ => .inl (.ub "atomicrmw out of bounds")
        | none =>
          match evalOperand st valOp with
          | .poison => .inr (bindReg { st with mem := st.mem.storePoison addr w.byteSize } dst .poison)
          | .bits wv vv =>
            if h : wv = w then
              match st.mem.loadInt? addr w with
              | none => .inl (.ub "atomicrmw poison memory")
              | some old =>
                let mem' := st.mem.storeInt addr w (evalRMWOp op w old (h ▸ vv))
                .inr (bindReg { st with mem := mem' } dst (.bits w old))
            else .inl (.ub "atomicrmw width mismatch")
          | _ => .inl (.ub "atomicrmw non-integer value")
      | _ => .inl (.ub "atomicrmw on non-pointer")
    | _ => .inl (.ub "atomicrmw on non-integer type")
  | .insertelement dst n et vecOp elemOp idxW idxOp =>
    match evalOperand st idxOp with
    | .poison => .inr (bindReg st dst .poison)
    | .bits w iv =>
      if h : w = idxW then
        let i := (h ▸ iv).toNat
        if n ≤ i then .inl (.ub "insertelement index out of range")
        else
          let vval := evalTypedOperand st (.vec n et) vecOp
          if isPoison vval then .inr (bindReg st dst .poison)
          else
            match vval.toList? with
            | some vs => .inr (bindReg st dst (LLVMVal.agg (vs.set i (evalTypedOperand st et elemOp))))
            | none => .inl (.ub "insertelement on non-vector")
      else .inl (.ub "insertelement index width mismatch")
    | _ => .inl (.ub "insertelement non-integer index")
  | .extractelement dst n et vecOp idxW idxOp =>
    match evalOperand st idxOp with
    | .poison => .inr (bindReg st dst .poison)
    | .bits w iv =>
      if h : w = idxW then
        let i := (h ▸ iv).toNat
        if n ≤ i then .inl (.ub "extractelement index out of range")
        else
          let vval := evalTypedOperand st (.vec n et) vecOp
          if isPoison vval then .inr (bindReg st dst .poison)
          else
            match vval.toList? with
            | some vs => .inr (bindReg st dst (vs.getD i .poison))
            | none => .inl (.ub "extractelement on non-vector")
      else .inl (.ub "extractelement index width mismatch")
    | _ => .inl (.ub "extractelement non-integer index")
  | .shufflevector dst n m et aOp bOp mask =>
    let av := evalTypedOperand st (.vec n et) aOp
    let bv := evalTypedOperand st (.vec m et) bOp
    if isPoison av || isPoison bv then .inr (bindReg st dst .poison)
    else
      match av.toList?, bv.toList? with
      | some va, some vb =>
        .inr (bindReg st dst (LLVMVal.agg (mask.map fun i => (va ++ vb).getD i .poison)))
      | _, _ => .inl (.ub "shufflevector on non-vector")
  | .insertvalue dst ty aggOp elemTy elemOp idxs =>
    let aval := evalTypedOperand st ty aggOp
    if isPoison aval then .inr (bindReg st dst .poison)
    else
      match setAt aval idxs (evalTypedOperand st elemTy elemOp) with
      | none => .inl (.ub "insertvalue index out of range")
      | some v => .inr (bindReg st dst v)
  | .extractvalue dst ty aggOp idxs =>
    let aval := evalTypedOperand st ty aggOp
    if isPoison aval then .inr (bindReg st dst .poison)
    else
      match getAt aval idxs with
      | none => .inl (.ub "extractvalue index out of range")
      | some v => .inr (bindReg st dst v)
where
  getAt : LLVMVal → List Nat → Option LLVMVal
    | v, [] => some v
    | v, i :: rest =>
      match v.toList? with
      | none => none
      | some vs =>
        if vs.length ≤ i then none
        else getAt (vs.getD i .poison) rest
  setAt : LLVMVal → List Nat → LLVMVal → Option LLVMVal
    | _, [], elem => some elem
    | v, i :: rest, elem =>
      match v.toList? with
      | none => none
      | some vs =>
        if vs.length ≤ i then none
        else
          match setAt (vs.getD i .poison) rest elem with
          | none => none
          | some inner => some (LLVMVal.agg (vs.set i inner))

def execInstrsWith (runCall : ExecState → Option RegName → LLVMType → GlobalSym → List LLVMVal → ExecOutcome ⊕ ExecState)
    (st : ExecState) : List LLVMInstr → ExecOutcome ⊕ ExecState
  | [] => .inr st
  | ins :: rest =>
    match stepInstrWith runCall st ins with
    | .inl out => .inl out
    | .inr st' => execInstrsWith runCall st' rest

inductive CalleeRes where
  | returned : Option LLVMVal → ByteMem → CalleeRes
  | ub : String → CalleeRes
  | outOfFuel : CalleeRes
  deriving Repr, DecidableEq

def execBlockWith (runCall : ExecState → Option RegName → LLVMType → GlobalSym → List LLVMVal → ExecOutcome ⊕ ExecState)
    (fn : LLVMFn) : Nat → ExecState → LLVMBlock → CalleeRes
  | 0, _, _ => .outOfFuel
  | k + 1, st, blk =>
    let binds := evalPhis st st.prevBlock blk.phis
    let stPhi := commitPhis st binds
    match execInstrsWith runCall stPhi blk.body with
    | .inl (.returned rv) => .returned rv stPhi.mem
    | .inl (.ub msg) => .ub msg
    | .inl .outOfFuel => .outOfFuel
    | .inr st' =>
      match blk.term with
      | .br lbl =>
        match findBlock fn lbl with
        | none => .ub "branch to missing block"
        | some next => execBlockWith runCall fn k { st' with prevBlock := some blk.label } next
      | .condBr condOp tLbl eLbl =>
        match evalOperand st' condOp with
        | .poison => .ub "conditional branch on poison"
        | .bits .i1 c =>
          let lbl := if c == 1#1 then tLbl else eLbl
          match findBlock fn lbl with
          | none => .ub "branch to missing block"
          | some next => execBlockWith runCall fn k { st' with prevBlock := some blk.label } next
        | _ => .ub "conditional branch on non-i1"
      | .switch w scrutOp defLbl cases =>
        match evalOperand st' scrutOp with
        | .poison => .ub "switch on poison"
        | .bits ws sv =>
          if h : ws = w then
            let key : BitVec w.bits := h ▸ sv
            let lbl := (cases.find? (fun pair => pair.fst == key)).map (·.snd) |>.getD defLbl
            match findBlock fn lbl with
            | none => .ub "switch to missing block"
            | some next => execBlockWith runCall fn k { st' with prevBlock := some blk.label } next
          else .ub "switch width mismatch"
        | _ => .ub "switch on non-integer"
      | .ret none => .returned none st'.mem
      | .ret (some (ty, op)) => .returned (some (evalTypedOperand st' ty op)) st'.mem
      | .unreachable => .ub "unreachable"

def runCallWith (mod_ : LLVMModule) (fuel : Nat) (st : ExecState)
    (dst? : Option RegName) (retTy : LLVMType) (callee : GlobalSym) (argVals : List LLVMVal) :
    ExecOutcome ⊕ ExecState :=
  match fuel with
  | 0 =>
    if callee == "llvm.trap" then .inl (.ub "trap")
    else
      match intrinsicResult callee argVals with
      | some v =>
        match dst? with
        | none => .inr st
        | some dst => .inr (bindReg st dst v)
      | none => .inl .outOfFuel
  | k + 1 =>
    if callee == "llvm.trap" then .inl (.ub "trap")
    else
      match intrinsicResult callee argVals with
      | some v =>
        match dst? with
        | none => .inr st
        | some dst => .inr (bindReg st dst v)
      | none =>
        match mod_.fns.find? (fun f => f.name == callee) with
        | some fn =>
          match fn.blocks with
          | [] => .inl (.ub "callee has no entry block")
          | entry :: _ =>
            match bindArgs { mem := st.mem } fn.params argVals with
            | none => .inl (.ub "callee arity mismatch")
            | some calleeSt =>
              match execBlockWith (runCallWith mod_ k) fn (k + 1) calleeSt entry with
              | .returned rv mem' =>
                let st' := { st with mem := mem' }
                match dst? with
                | none => .inr st'
                | some dst =>
                  match rv with
                  | some v => .inr (bindReg st' dst v)
                  | none =>
                    if retTy == .void then .inr st' else .inr (bindReg st' dst .poison)
              | .ub msg => .inl (.ub msg)
              | .outOfFuel => .inl .outOfFuel
        | none =>
          match extOracle callee argVals st.mem with
          | some er =>
            let st' := { st with mem := er.mem }
            match dst? with
            | none => .inr st'
            | some dst =>
              match er.dst with
              | some v => .inr (bindReg st' dst v)
              | none => if retTy == .void then .inr st' else .inl (.ub "unmodeled external call")
          | none => .inl (.ub "unmodeled external call")

def calleeResToOutcome : CalleeRes → ExecOutcome
  | .returned rv _ => .returned rv
  | .ub msg => .ub msg
  | .outOfFuel => .outOfFuel

def stepInstr (mod_ : LLVMModule) (fuel : Nat) (st : ExecState) (ins : LLVMInstr) : ExecOutcome ⊕ ExecState :=
  stepInstrWith (runCallWith mod_ fuel) st ins

def execInstrs (mod_ : LLVMModule) (fuel : Nat) (st : ExecState) (is : List LLVMInstr) : ExecOutcome ⊕ ExecState :=
  execInstrsWith (runCallWith mod_ fuel) st is

def execBlock (mod_ : LLVMModule) (fn : LLVMFn) (fuel : Nat) (st : ExecState) (blk : LLVMBlock) : ExecOutcome :=
  calleeResToOutcome (execBlockWith (runCallWith mod_ fuel) fn fuel st blk)

def execFn (mod_ : LLVMModule) (fn : LLVMFn) (args : List LLVMVal) (fuel : Nat) : ExecOutcome :=
  match fn.blocks with
  | [] => .ub "function has no entry block"
  | entry :: _ =>
    match bindArgs {} fn.params args with
    | none => .ub "argument arity mismatch"
    | some st => execBlock mod_ fn fuel st entry

namespace PP

def ppInt (n : Nat) : String := TargetIR.ppInt n

def ppICmp : ICmpPred → String
  | .eq => "eq" | .ne => "ne" | .ult => "ult" | .ule => "ule" | .ugt => "ugt"
  | .uge => "uge" | .slt => "slt" | .sle => "sle" | .sgt => "sgt" | .sge => "sge"

def ppFCmp : FCmpPred → String
  | .oeq => "oeq" | .one => "one" | .olt => "olt" | .ole => "ole" | .ogt => "ogt" | .oge => "oge"
  | .ord => "ord" | .uno => "uno" | .ueq => "ueq" | .une => "une" | .ult => "ult" | .ule => "ule"
  | .ugt => "ugt" | .uge => "uge" | .true_ => "true" | .false_ => "false"

def ppFlags : OverflowFlags → String
  | .none => "" | .nsw => " nsw" | .nuw => " nuw" | .nswNuw => " nsw nuw"

def ppExact (exact : Bool) : String :=
  if exact then " exact" else ""

def ppVolatile (volatile : Bool) : String :=
  if volatile then " volatile" else ""

def ppOrdering : AtomicOrdering → String
  | .monotonic => "monotonic" | .acquire => "acquire" | .release => "release"
  | .acqRel => "acq_rel" | .seqCst => "seq_cst"

def ppRMW : AtomicRMWOp → String
  | .add => "add" | .sub => "sub" | .and_ => "and" | .or_ => "or" | .xor => "xor"
  | .nand => "nand" | .max => "max" | .min => "min" | .umax => "umax" | .umin => "umin" | .xchg => "xchg"

def ppCC : CallingConv → String
  | .ccc => "ccc" | .fastcc => "fastcc" | .coldcc => "coldcc"

def ppAttr : ParamAttr → String
  | .zeroext => "zeroext" | .signext => "signext" | .noalias => "noalias" | .noundef => "noundef"
  | .readonly => "readonly" | .writeonly => "writeonly" | .nocapture => "nocapture"

def ppLinkage : Linkage → String
  | .external => "" | .private_ => "private " | .internal => "internal " | .weakOdr => "weak_odr "

def hexDigit (n : Nat) : Char :=
  match n with
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | 9 => '9'
  | 10 => 'A' | 11 => 'B' | 12 => 'C' | 13 => 'D' | 14 => 'E'
  | _ => 'F'

def toHex16Aux : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | k + 1, x, acc => toHex16Aux k (x / 16) (hexDigit (x % 16) :: acc)

def ppHex64 (u : UInt64) : String :=
  "0x" ++ String.ofList (toHex16Aux 16 u.toNat [])

def f32BitsToDoubleHexBits (b : BitVec 32) : UInt64 :=
  let raw := b.toNat
  let exp := (raw / 8388608) % 256
  let mant := raw % 8388608
  if exp == 255 && mant != 0 then
    let sign64 := if raw / 2147483648 == 1 then (1 : Nat) <<< 63 else 0
    let exp64 := (2047 : Nat) <<< 52
    let mant64 := mant <<< 29
    UInt64.ofNat (sign64 ||| exp64 ||| mant64)
  else
    (Float32.ofBits (UInt32.ofNat raw)).toFloat.toBits

def ppFloatHex (fw : FloatWidth) (b : BitVec fw.bits) : String :=
  match fw with
  | .f64 => ppHex64 b.toNat.toUInt64
  | .f32 => ppHex64 (f32BitsToDoubleHexBits b)

mutual
def typeChars : LLVMType → List Char
  | .void => ['v', 'o', 'i', 'd']
  | .int .i1 => ['i', '1']
  | .int .i8 => ['i', '8']
  | .int .i16 => ['i', '1', '6']
  | .int .i32 => ['i', '3', '2']
  | .int .i64 => ['i', '6', '4']
  | .int .i128 => ['i', '1', '2', '8']
  | .int .i256 => ['i', '2', '5', '6']
  | .int .i512 => ['i', '5', '1', '2']
  | .float .f32 => ['f', 'l', 'o', 'a', 't']
  | .float .f64 => ['d', 'o', 'u', 'b', 'l', 'e']
  | .ptr as_ =>
    if as_ == 0 then ['p', 't', 'r']
    else ['p', 't', 'r', ' ', 'a', 'd', 'd', 'r', 's', 'p', 'a', 'c', 'e', '('] ++ TargetIR.natDigits as_ ++ [')']
  | .structFields .nil => ['{', ' ', '}']
  | .structFields (.cons h t) => ['{', ' '] ++ typeChars h ++ fieldsTailChars t ++ [' ', '}']
  | .array n et => ['['] ++ TargetIR.natDigits n ++ [' ', 'x', ' '] ++ typeChars et ++ [']']
  | .vec n et => ['<'] ++ TargetIR.natDigits n ++ [' ', 'x', ' '] ++ typeChars et ++ ['>']

def fieldsTailChars : LLVMTypeFields → List Char
  | .nil => []
  | .cons h t => [',', ' '] ++ typeChars h ++ fieldsTailChars t
end

def ppType (ty : LLVMType) : String :=
  String.ofList (typeChars ty)

mutual
def parseType : Nat → List Char → Option (LLVMType × List Char)
  | 0, _ => none
  | _ + 1, 'v' :: 'o' :: 'i' :: 'd' :: rest => some (.void, rest)
  | _ + 1, 'f' :: 'l' :: 'o' :: 'a' :: 't' :: rest => some (.float .f32, rest)
  | _ + 1, 'd' :: 'o' :: 'u' :: 'b' :: 'l' :: 'e' :: rest => some (.float .f64, rest)
  | _ + 1, 'i' :: '1' :: '2' :: '8' :: rest => some (.int .i128, rest)
  | _ + 1, 'i' :: '2' :: '5' :: '6' :: rest => some (.int .i256, rest)
  | _ + 1, 'i' :: '5' :: '1' :: '2' :: rest => some (.int .i512, rest)
  | _ + 1, 'i' :: '1' :: '6' :: rest => some (.int .i16, rest)
  | _ + 1, 'i' :: '3' :: '2' :: rest => some (.int .i32, rest)
  | _ + 1, 'i' :: '6' :: '4' :: rest => some (.int .i64, rest)
  | _ + 1, 'i' :: '8' :: rest => some (.int .i8, rest)
  | _ + 1, 'i' :: '1' :: rest => some (.int .i1, rest)
  | _ + 1, 'p' :: 't' :: 'r' :: ' ' :: 'a' :: 'd' :: 'd' :: 'r' :: 's' :: 'p' :: 'a' :: 'c' :: 'e' :: '(' :: cs =>
    match TargetIR.readDigits 0 cs with
    | (as_, ')' :: rest) => some (.ptr as_, rest)
    | _ => none
  | _ + 1, 'p' :: 't' :: 'r' :: rest => some (.ptr 0, rest)
  | _ + 1, '{' :: ' ' :: '}' :: rest => some (.structFields .nil, rest)
  | fuel + 1, '{' :: ' ' :: cs =>
    match parseType fuel cs with
    | some (h, rest1) =>
      match parseFieldsTail fuel rest1 with
      | some (t, ' ' :: '}' :: rest2) => some (.structFields (.cons h t), rest2)
      | _ => none
    | none => none
  | fuel + 1, '[' :: cs =>
    match TargetIR.readDigits 0 cs with
    | (n, ' ' :: 'x' :: ' ' :: rest1) =>
      match parseType fuel rest1 with
      | some (et, ']' :: rest2) => some (.array n et, rest2)
      | _ => none
    | _ => none
  | fuel + 1, '<' :: cs =>
    match TargetIR.readDigits 0 cs with
    | (n, ' ' :: 'x' :: ' ' :: rest1) =>
      match parseType fuel rest1 with
      | some (et, '>' :: rest2) => some (.vec n et, rest2)
      | _ => none
    | _ => none
  | _ + 1, _ => none

def parseFieldsTail : Nat → List Char → Option (LLVMTypeFields × List Char)
  | 0, _ => none
  | fuel + 1, ',' :: ' ' :: cs =>
    match parseType fuel cs with
    | some (h, rest1) =>
      match parseFieldsTail fuel rest1 with
      | some (t, rest2) => some (.cons h t, rest2)
      | none => none
    | none => none
  | _ + 1, cs => some (.nil, cs)
end

mutual
def typeDepth : LLVMType → Nat
  | .void | .int _ | .float _ | .ptr _ => 1
  | .structFields fs => 1 + fieldsDepth fs
  | .array _ et => 1 + typeDepth et
  | .vec _ et => 1 + typeDepth et

def fieldsDepth : LLVMTypeFields → Nat
  | .nil => 1
  | .cons h t => 1 + Nat.max (typeDepth h) (fieldsDepth t)
end

inductive ValidTypeSuffix : List Char → Prop where
  | nil : ValidTypeSuffix []
  | comma (cs : List Char) : ValidTypeSuffix (',' :: cs)
  | closeBrace (cs : List Char) : ValidTypeSuffix (' ' :: '}' :: cs)
  | closeBracket (cs : List Char) : ValidTypeSuffix (']' :: cs)
  | closeAngle (cs : List Char) : ValidTypeSuffix ('>' :: cs)

inductive ValidTailSuffix : List Char → Prop where
  | closeBrace (cs : List Char) : ValidTailSuffix (' ' :: '}' :: cs)

def ppVal : Operand → String
  | .reg r => "%" ++ r
  | .constInt _ v => ppInt v.toNat
  | .constFloat fw v => ppFloatHex fw v
  | .constNull => "null"
  | .constUndef => "undef"
  | .constZero => "zeroinitializer"
  | .aggNil => ""
  | .aggCons h t => ppVal h ++ ", " ++ ppVal t
  | .poison => "poison"

mutual
def ppAggElems : LLVMTypeFields → Operand → List String
  | .cons hty tty, .aggCons hop top => ppTypedOperand hty hop :: ppAggElems tty top
  | _, _ => []

def ppHomogElems : Nat → LLVMType → Operand → List String
  | k + 1, et, .aggCons hop top => ppTypedOperand et hop :: ppHomogElems k et top
  | _, _, _ => []

def ppBareVal (ty : LLVMType) (op : Operand) : String :=
  match op with
  | .aggNil | .constZero =>
    match ty with
    | .int _ => "0"
    | .float fw => ppFloatHex fw (BitVec.ofNat fw.bits 0)
    | .ptr _ => "null"
    | _ => "zeroinitializer"
  | .aggCons _ _ =>
    match ty with
    | .vec n et => "<" ++ String.intercalate ", " (ppHomogElems n et op) ++ ">"
    | .array n et => "[" ++ String.intercalate ", " (ppHomogElems n et op) ++ "]"
    | .structFields fs => "{ " ++ String.intercalate ", " (ppAggElems fs op) ++ " }"
    | _ => ppVal op
  | _ => ppVal op

def ppTypedOperand (ty : LLVMType) (op : Operand) : String :=
  ppType ty ++ " " ++ ppBareVal ty op
end

def ppAlign (align : Nat) : String :=
  if align == 0 then "" else ", align " ++ ppInt align

def ppGEP (inbounds_ : Bool) (ty : LLVMType) (base : Operand) (idxs : List (IntWidth × Operand)) : String :=
  let ib := if inbounds_ then " inbounds" else ""
  let idxStr := String.join (idxs.map fun (w, op) => ", " ++ w.pp ++ " " ++ ppVal op)
  "getelementptr" ++ ib ++ " " ++ ppType ty ++ ", ptr " ++ ppVal base ++ idxStr

def ppInstr : LLVMInstr → String
  | .alloca dst ty align =>
    "%" ++ dst ++ " = alloca " ++ ppType ty ++ ppAlign align
  | .load dst volatile ty ptrOp align =>
    "%" ++ dst ++ " = load" ++ ppVolatile volatile ++ " " ++ ppType ty ++ ", ptr " ++ ppVal ptrOp ++ ppAlign align
  | .store volatile ty valOp ptrOp align =>
    "store" ++ ppVolatile volatile ++ " " ++ ppTypedOperand ty valOp ++ ", ptr " ++ ppVal ptrOp ++ ppAlign align
  | .add dst flags w aOp bOp =>
    "%" ++ dst ++ " = add" ++ ppFlags flags ++ " " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .sub dst flags w aOp bOp =>
    "%" ++ dst ++ " = sub" ++ ppFlags flags ++ " " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .mul dst flags w aOp bOp =>
    "%" ++ dst ++ " = mul" ++ ppFlags flags ++ " " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .udiv dst exact w aOp bOp =>
    "%" ++ dst ++ " = udiv" ++ ppExact exact ++ " " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .sdiv dst exact w aOp bOp =>
    "%" ++ dst ++ " = sdiv" ++ ppExact exact ++ " " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .urem dst w aOp bOp =>
    "%" ++ dst ++ " = urem " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .srem dst w aOp bOp =>
    "%" ++ dst ++ " = srem " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .and_ dst w aOp bOp =>
    "%" ++ dst ++ " = and " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .or_ dst w aOp bOp =>
    "%" ++ dst ++ " = or " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .xor dst w aOp bOp =>
    "%" ++ dst ++ " = xor " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .shl dst flags w aOp bOp =>
    "%" ++ dst ++ " = shl" ++ ppFlags flags ++ " " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .lshr dst exact w aOp bOp =>
    "%" ++ dst ++ " = lshr" ++ ppExact exact ++ " " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .ashr dst exact w aOp bOp =>
    "%" ++ dst ++ " = ashr" ++ ppExact exact ++ " " ++ w.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .icmp dst pred ty aOp bOp =>
    "%" ++ dst ++ " = icmp " ++ ppICmp pred ++ " " ++ ppType ty ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .fadd dst fw aOp bOp =>
    "%" ++ dst ++ " = fadd " ++ fw.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .fsub dst fw aOp bOp =>
    "%" ++ dst ++ " = fsub " ++ fw.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .fmul dst fw aOp bOp =>
    "%" ++ dst ++ " = fmul " ++ fw.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .fdiv dst fw aOp bOp =>
    "%" ++ dst ++ " = fdiv " ++ fw.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .fcmp dst pred fw aOp bOp =>
    "%" ++ dst ++ " = fcmp " ++ ppFCmp pred ++ " " ++ fw.pp ++ " " ++ ppVal aOp ++ ", " ++ ppVal bOp
  | .zext dst srcW op dstW =>
    "%" ++ dst ++ " = zext " ++ srcW.pp ++ " " ++ ppVal op ++ " to " ++ dstW.pp
  | .sext dst srcW op dstW =>
    "%" ++ dst ++ " = sext " ++ srcW.pp ++ " " ++ ppVal op ++ " to " ++ dstW.pp
  | .trunc dst srcW op dstW =>
    "%" ++ dst ++ " = trunc " ++ srcW.pp ++ " " ++ ppVal op ++ " to " ++ dstW.pp
  | .bitcast dst srcTy op dstTy =>
    "%" ++ dst ++ " = bitcast " ++ ppTypedOperand srcTy op ++ " to " ++ ppType dstTy
  | .inttoptr dst srcW op as_ =>
    "%" ++ dst ++ " = inttoptr " ++ srcW.pp ++ " " ++ ppVal op ++ " to " ++ ppType (.ptr as_)
  | .ptrtoint dst as_ op dstW =>
    "%" ++ dst ++ " = ptrtoint " ++ ppType (.ptr as_) ++ " " ++ ppVal op ++ " to " ++ dstW.pp
  | .getelementptr dst inbounds_ ty baseOp idxs =>
    "%" ++ dst ++ " = " ++ ppGEP inbounds_ ty baseOp idxs
  | .select dst condOp ty tOp eOp =>
    "%" ++ dst ++ " = select i1 " ++ ppVal condOp ++ ", " ++ ppTypedOperand ty tOp ++ ", " ++ ppTypedOperand ty eOp
  | .call dst? retTy callee args =>
    let lhs := match dst? with | none => "" | some dst => "%" ++ dst ++ " = "
    let argStr := String.intercalate ", " (args.map fun (ty, op) => ppTypedOperand ty op)
    lhs ++ "call " ++ ppType retTy ++ " @" ++ callee ++ "(" ++ argStr ++ ")"
  | .atomicrmw dst op ptrOp ty valOp ord align =>
    "%" ++ dst ++ " = atomicrmw " ++ ppRMW op ++ " ptr " ++ ppVal ptrOp ++ ", " ++ ppTypedOperand ty valOp ++
      " " ++ ppOrdering ord ++ ppAlign align
  | .insertelement dst n et vecOp elemOp idxW idxOp =>
    "%" ++ dst ++ " = insertelement " ++ ppTypedOperand (.vec n et) vecOp ++ ", " ++
      ppTypedOperand et elemOp ++ ", " ++ idxW.pp ++ " " ++ ppVal idxOp
  | .extractelement dst n et vecOp idxW idxOp =>
    "%" ++ dst ++ " = extractelement " ++ ppTypedOperand (.vec n et) vecOp ++ ", " ++ idxW.pp ++ " " ++ ppVal idxOp
  | .shufflevector dst n m et aOp bOp mask =>
    let maskTy := "<" ++ ppInt mask.length ++ " x i32>"
    let maskVal := "<" ++ String.intercalate ", " (mask.map fun i => "i32 " ++ ppInt i) ++ ">"
    "%" ++ dst ++ " = shufflevector " ++ ppTypedOperand (.vec n et) aOp ++ ", " ++
      ppTypedOperand (.vec m et) bOp ++ ", " ++ maskTy ++ " " ++ maskVal
  | .insertvalue dst ty aggOp elemTy elemOp idxs =>
    "%" ++ dst ++ " = insertvalue " ++ ppTypedOperand ty aggOp ++ ", " ++ ppTypedOperand elemTy elemOp ++
      String.join (idxs.map fun i => ", " ++ ppInt i)
  | .extractvalue dst ty aggOp idxs =>
    "%" ++ dst ++ " = extractvalue " ++ ppTypedOperand ty aggOp ++ String.join (idxs.map fun i => ", " ++ ppInt i)

def ppTerm : Terminator → String
  | .br lbl => "br label %" ++ lbl
  | .condBr condOp tLbl eLbl =>
    "br i1 " ++ ppVal condOp ++ ", label %" ++ tLbl ++ ", label %" ++ eLbl
  | .switch w scrutOp defLbl cases =>
    let arms := String.intercalate "\n" (cases.map fun (k, lbl) =>
      "    " ++ w.pp ++ " " ++ ppInt k.toNat ++ ", label %" ++ lbl)
    "switch " ++ w.pp ++ " " ++ ppVal scrutOp ++ ", label %" ++ defLbl ++ " [\n" ++ arms ++ "\n  ]"
  | .ret none => "ret void"
  | .ret (some (ty, op)) => "ret " ++ ppTypedOperand ty op
  | .unreachable => "unreachable"

def ppPhi (p : PhiNode) : String :=
  let arms := String.intercalate ", " (p.incomings.map fun (op, lbl) => "[ " ++ ppBareVal p.ty op ++ ", %" ++ lbl ++ " ]")
  "%" ++ p.dst ++ " = phi " ++ ppType p.ty ++ " " ++ arms

def ppBlock (b : LLVMBlock) : String :=
  b.label ++ ":\n" ++ String.intercalate "\n"
    (b.phis.map (fun p => "  " ++ ppPhi p) ++ b.body.map (fun i => "  " ++ ppInstr i) ++ ["  " ++ ppTerm b.term])

def ppParam (p : LLVMParam) : String :=
  let attrs := if p.attrs.isEmpty then "" else " " ++ String.intercalate " " (p.attrs.map ppAttr)
  ppType p.ty ++ attrs ++ " %" ++ p.name

def ppFn (fn : LLVMFn) : String :=
  "define " ++ ppCC fn.cc ++ " " ++ ppType fn.retTy ++ " @" ++ fn.name ++ "(" ++
    String.intercalate ", " (fn.params.map ppParam) ++ ") {\n" ++
    String.intercalate "\n" (fn.blocks.map ppBlock) ++ "\n}"

def ppGlobal (g : LLVMGlobal) : String :=
  let kind := if g.isConstant then "constant " else "global "
  let link := if g.linkage == .external && g.init.isNone then "external " else ppLinkage g.linkage
  let body :=
    if g.linkage == .external && g.init.isNone then ppType g.ty
    else match g.init with
      | none => ppType g.ty ++ " zeroinitializer"
      | some op => ppTypedOperand g.ty op
  "@" ++ g.name ++ " = " ++ link ++ kind ++ body ++ ppAlign g.align

def ppExtern (e : LLVMExtern) : String :=
  "declare " ++ ppType e.retTy ++ " @" ++ e.name ++ "(" ++ String.intercalate ", " (e.paramTys.map ppType) ++ ")"

def ppModule (m : LLVMModule) : String :=
  String.intercalate "\n" ([
    "target datalayout = \"" ++ m.dataLayout ++ "\"",
    "target triple = \"" ++ m.triple ++ "\""
  ] ++ m.globals.map ppGlobal ++ m.externs.map ppExtern ++ m.fns.map ppFn)

end PP

theorem parseType_int (fuel : Nat) (w : IntWidth) (rest : List Char)
    (hsuf : PP.ValidTypeSuffix rest) :
    PP.parseType (fuel + 1) (PP.typeChars (.int w) ++ rest) = some (.int w, rest) := by
  cases w with
  | i1 => cases hsuf <;> rfl
  | i8 | i16 | i32 | i64 | i128 | i256 | i512 => rfl

theorem parseType_ptr (fuel : Nat) (as_ : AddrSpace) (rest : List Char)
    (hsuf : PP.ValidTypeSuffix rest) :
    PP.parseType (fuel + 1) (PP.typeChars (.ptr as_) ++ rest) = some (.ptr as_, rest) := by
  by_cases hz : as_ == 0
  · have ha : as_ = 0 := beq_iff_eq.mp hz
    subst ha
    cases hsuf <;> rfl
  · simp only [PP.typeChars, hz, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.append_assoc, List.nil_append]
    simp only [PP.parseType]
    rw [readDigits_natDigits_delim as_ ')' rest rfl]
    rfl

theorem typeChars_head_not_brace (ty : LLVMType) (rest : List Char) :
    ∃ c cs, c ≠ '}' ∧ PP.typeChars ty ++ rest = c :: cs := by
  cases ty with
  | void => exact ⟨'v', 'o' :: 'i' :: 'd' :: rest, by decide, rfl⟩
  | int w => cases w <;> exact ⟨'i', _, by decide, rfl⟩
  | float fw =>
    cases fw with
    | f32 => exact ⟨'f', _, by decide, rfl⟩
    | f64 => exact ⟨'d', _, by decide, rfl⟩
  | ptr a =>
    by_cases ha : a == 0
    · simp only [PP.typeChars, ha, ↓reduceIte]
      exact ⟨'p', _, by decide, rfl⟩
    · simp only [PP.typeChars, ha, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.append_assoc]
      exact ⟨'p', _, by decide, rfl⟩
  | structFields fs =>
    cases fs with
    | nil => exact ⟨'{', _, by decide, rfl⟩
    | cons _ _ => exact ⟨'{', _, by decide, rfl⟩
  | array _ _ => exact ⟨'[', _, by decide, rfl⟩
  | vec _ _ => exact ⟨'<', _, by decide, rfl⟩

theorem parseType_struct_open (fuel : Nat) (c : Char) (cs : List Char) (hc : c ≠ '}')
    (h : LLVMType) (rest1 : List Char) (t : LLVMTypeFields) (rest2 : List Char)
    (hp1 : PP.parseType fuel (c :: cs) = some (h, rest1))
    (hp2 : PP.parseFieldsTail fuel rest1 = some (t, ' ' :: '}' :: rest2)) :
    PP.parseType (fuel + 1) ('{' :: ' ' :: c :: cs) = some (.structFields (.cons h t), rest2) := by
  simp [PP.parseType, hc, hp1, hp2]

mutual
theorem parseType_roundtrip (fuel : Nat) (ty : LLVMType) (rest : List Char)
    (hf : PP.typeDepth ty ≤ fuel)
    (hsuf : PP.ValidTypeSuffix rest) :
    PP.parseType fuel (PP.typeChars ty ++ rest) = some (ty, rest) := by
  cases fuel with
  | zero =>
    cases ty <;> simp [PP.typeDepth] at hf
  | succ f =>
    cases ty with
    | void => rfl
    | int w => exact parseType_int f w rest hsuf
    | float fw => cases fw <;> rfl
    | ptr as_ => exact parseType_ptr f as_ rest hsuf
    | structFields fs =>
      cases fs with
      | nil => rfl
      | cons h t =>
        simp only [PP.typeDepth, PP.fieldsDepth] at hf
        have hmax : Nat.max (PP.typeDepth h) (PP.fieldsDepth t) ≤ f := by omega
        have hh_le : PP.typeDepth h ≤ f := Nat.le_trans (Nat.le_max_left _ _) hmax
        have ht_le : PP.fieldsDepth t ≤ f := Nat.le_trans (Nat.le_max_right _ _) hmax
        have htsuf : PP.ValidTypeSuffix (PP.fieldsTailChars t ++ (' ' :: '}' :: rest)) := by
          cases t with
          | nil => exact .closeBrace rest
          | cons _ _ => exact .comma _
        simp only [PP.typeChars, List.cons_append, List.nil_append, List.append_assoc]
        rcases typeChars_head_not_brace h (PP.fieldsTailChars t ++ ' ' :: '}' :: rest) with ⟨c, cs, hc, heq⟩
        have hp1 : PP.parseType f (c :: cs) = some (h, PP.fieldsTailChars t ++ ' ' :: '}' :: rest) := by
          rw [← heq]
          exact parseType_roundtrip f h (PP.fieldsTailChars t ++ ' ' :: '}' :: rest) hh_le htsuf
        have hp2 : PP.parseFieldsTail f (PP.fieldsTailChars t ++ ' ' :: '}' :: rest) =
            some (t, ' ' :: '}' :: rest) :=
          parseFieldsTail_roundtrip f t (' ' :: '}' :: rest) ht_le (.closeBrace rest)
        rw [heq]
        exact parseType_struct_open f c cs hc h _ t rest hp1 hp2
    | array n et =>
      simp only [PP.typeDepth] at hf
      simp only [PP.typeChars, List.cons_append, List.append_assoc, List.nil_append, PP.parseType]
      rw [readDigits_natDigits_delim n ' ' ('x' :: ' ' :: (PP.typeChars et ++ ']' :: rest)) rfl]
      simp only
      rw [parseType_roundtrip f et (']' :: rest) (by omega) (.closeBracket rest)]
      rfl
    | vec n et =>
      simp only [PP.typeDepth] at hf
      simp only [PP.typeChars, List.cons_append, List.append_assoc, List.nil_append, PP.parseType]
      rw [readDigits_natDigits_delim n ' ' ('x' :: ' ' :: (PP.typeChars et ++ '>' :: rest)) rfl]
      simp only
      rw [parseType_roundtrip f et ('>' :: rest) (by omega) (.closeAngle rest)]
      rfl

theorem parseFieldsTail_roundtrip (fuel : Nat) (fs : LLVMTypeFields) (rest : List Char)
    (hf : PP.fieldsDepth fs ≤ fuel)
    (hsuf : PP.ValidTailSuffix rest) :
    PP.parseFieldsTail fuel (PP.fieldsTailChars fs ++ rest) = some (fs, rest) := by
  cases fuel with
  | zero =>
    cases fs <;> simp [PP.fieldsDepth] at hf
  | succ f =>
    cases fs with
    | nil =>
      cases hsuf with
      | closeBrace cs => rfl
    | cons h t =>
      simp only [PP.fieldsDepth] at hf
      have hmax : Nat.max (PP.typeDepth h) (PP.fieldsDepth t) ≤ f := by omega
      have hh_le : PP.typeDepth h ≤ f := Nat.le_trans (Nat.le_max_left _ _) hmax
      have ht_le : PP.fieldsDepth t ≤ f := Nat.le_trans (Nat.le_max_right _ _) hmax
      have htsuf : PP.ValidTypeSuffix (PP.fieldsTailChars t ++ rest) := by
        cases t with
        | nil =>
          cases hsuf with
          | closeBrace cs => exact .closeBrace cs
        | cons _ _ => exact .comma _
      simp only [PP.fieldsTailChars, List.cons_append, List.nil_append, List.append_assoc, PP.parseFieldsTail]
      rw [parseType_roundtrip f h (PP.fieldsTailChars t ++ rest) hh_le htsuf]
      simp only
      rw [parseFieldsTail_roundtrip f t rest ht_le hsuf]
end

theorem ppType_injective (t1 t2 : LLVMType) (h : PP.ppType t1 = PP.ppType t2) : t1 = t2 := by
  have hchars : PP.typeChars t1 = PP.typeChars t2 := by
    have hto := congrArg String.toList h
    simpa [PP.ppType] using hto
  let fuel := Nat.max (PP.typeDepth t1) (PP.typeDepth t2)
  have h1 := parseType_roundtrip fuel t1 [] (Nat.le_max_left _ _) .nil
  have h2 := parseType_roundtrip fuel t2 [] (Nat.le_max_right _ _) .nil
  simp only [List.append_nil] at h1 h2
  rw [hchars] at h1
  rw [h1] at h2
  injection h2 with hpair
  exact (Prod.mk.inj hpair).1

theorem add_nsw_overflow_poison (w : IntWidth) (a b : BitVec w.bits)
    (h_ov : addOverflowNSW w a b = true) :
    stepInstr {} 1 {} (.add "r" .nsw w (.constInt w a) (.constInt w b)) =
      .inr (bindReg {} "r" .poison) := by
  simp [stepInstr, stepInstrWith, evalOperand, binResult, flagsOverflow, h_ov]

theorem shl_overshift_poison (w : IntWidth) (a amt : BitVec w.bits)
    (h_over : w.bits ≤ amt.toNat) :
    stepInstr {} 1 {} (.shl "r" .none w (.constInt w a) (.constInt w amt)) =
      .inr (bindReg {} "r" .poison) := by
  simp [stepInstr, stepInstrWith, evalOperand, shiftResult, h_over]

theorem udiv_zero_ub (w : IntWidth) (a : BitVec w.bits) :
    stepInstr {} 1 {} (.udiv "r" false w (.constInt w a) (.constInt w (0#w.bits))) =
      .inl (.ub "division by zero") := by
  simp [stepInstr, stepInstrWith, evalOperand, divOrRem]

theorem phi_resolves_predecessor (st : ExecState) (ty : LLVMType) (lbl : BlockLabel) (op : Operand) :
    resolvePhi st ty (some lbl) [(op, lbl)] = evalTypedOperand st ty op := by
  simp [resolvePhi]

theorem phi_parallel_swap (st : ExecState) (lbl : BlockLabel) (a b : Operand) :
    evalPhis st (some lbl)
      [{ dst := "x", ty := .int .i64, incomings := [(b, lbl)] },
       { dst := "y", ty := .int .i64, incomings := [(a, lbl)] }] =
      [("x", evalTypedOperand st (.int .i64) b), ("y", evalTypedOperand st (.int .i64) a)] := by
  simp [evalPhis, resolvePhi]

theorem writeBytesAt_allocs (m : ByteMem) (base : Nat) (bs : List MemByte) :
    (m.writeBytesAt base bs).allocs = m.allocs := by
  induction bs generalizing m base with
  | nil => rfl
  | cons b rest ih =>
    simp [ByteMem.writeBytesAt, ByteMem.writeAt, ih]

theorem accessInAlloc_writeBytesAt (m : ByteMem) (base : Nat) (bs : List MemByte)
    (addr n : Nat) (needWrite : Bool) :
    (m.writeBytesAt base bs).accessInAlloc addr n needWrite = m.accessInAlloc addr n needWrite := by
  simp [ByteMem.accessInAlloc, ByteMem.findAlloc, writeBytesAt_allocs]

theorem accessInAlloc_read_of_write (m : ByteMem) (addr n : Nat)
    (h : m.accessInAlloc addr n true = true) :
    m.accessInAlloc addr n false = true := by
  unfold ByteMem.accessInAlloc at h ⊢
  cases hf : m.findAlloc addr with
  | none => simp [hf] at h
  | some b =>
    simp only [hf, Bool.not_true, Bool.false_or, Bool.not_false, Bool.true_or, Bool.and_true] at h ⊢
    exact (Bool.and_eq_true_iff.mp h).1

theorem load_after_alloca_store (st : ExecState) (w : IntWidth) (v : BitVec w.bits) (align : Nat)
    (h_pow : isPow2 align = true)
    (h_sz : 0 < w.byteSize)
    (ptr : BitVec 64) (mem1 : ByteMem)
    (h_alloc : st.mem.allocAligned w.byteSize align = some (ptr, mem1)) :
    ∃ mem2, stepInstr {} 1 { st with mem := mem1, regs := [("p", .ptr ptr)] }
        (.store false (.int w) (.constInt w v) (.reg "p") align) =
        .inr { st with mem := mem2, regs := [("p", .ptr ptr)] } ∧
      stepInstr {} 1 { st with mem := mem2, regs := [("p", .ptr ptr)] }
        (.load "out" false (.int w) (.reg "p") align) =
        .inr (bindReg { st with mem := mem2, regs := [("p", .ptr ptr)] } "out" (.bits w v)) := by
  have h_ok := ByteMem.allocAligned_accessOk st.mem w.byteSize align true ptr mem1 h_pow h_sz h_alloc
  have h_nz := ByteMem.allocAligned_nonzero st.mem w.byteSize align true ptr mem1 h_alloc
  have h_al := ByteMem.allocAligned_isAligned st.mem w.byteSize align true ptr mem1 h_pow h_alloc
  have h_in1 : mem1.accessInAlloc ptr.toNat w.byteSize true = true := by
    unfold ByteMem.accessOk at h_ok
    exact (Bool.and_eq_true_iff.mp h_ok).2
  have h_in2 : (mem1.storeInt ptr w v).accessInAlloc ptr.toNat w.byteSize false = true := by
    unfold ByteMem.storeInt
    rw [accessInAlloc_writeBytesAt]
    exact accessInAlloc_read_of_write mem1 ptr.toNat w.byteSize h_in1
  have h_take : ((mem1.storeInt ptr w v).readBytesAt ptr.toNat w.byteSize).take w.byteSize =
      (mem1.storeInt ptr w v).readBytesAt ptr.toNat w.byteSize := by
    apply List.take_of_length_le
    rw [ByteMem.readBytesAt_length]
    exact Nat.le_refl _
  have h_load : ByteMem.bytesToBv? w.bits
      (((mem1.storeInt ptr w v).readBytesAt ptr.toNat w.byteSize).take w.byteSize) = some v := by
    rw [h_take]
    exact ByteMem.loadInt?_storeInt_same mem1 ptr w v
  refine ⟨mem1.storeInt ptr w v, ?_, ?_⟩
  · simp [stepInstr, stepInstrWith, evalTypedOperand, evalOperand, lookupReg, accessCheck, storeVal, serializeVal,
      ByteMem.storeInt, LLVMType.byteSize, h_nz, h_al, h_in1]
  · simp [stepInstr, stepInstrWith, evalOperand, lookupReg, accessCheck, loadVal, deserializeVal,
      LLVMType.byteSize, h_nz, h_al, h_in2, h_load]

theorem select_cond_poison (ty : LLVMType) (tOp eOp : Operand) :
    stepInstr {} 1 {} (.select "r" .poison ty tOp eOp) =
      .inr (bindReg {} "r" .poison) := by
  simp [stepInstr, stepInstrWith, evalOperand]

theorem ppInstr_nonempty (ins : LLVMInstr) : PP.ppInstr ins ≠ "" := by
  cases ins <;> simp [PP.ppInstr, PP.ppFlags, PP.ppExact, PP.ppVolatile, PP.ppICmp, PP.ppFCmp,
    PP.ppRMW, PP.ppOrdering, PP.ppAlign, PP.ppGEP, PP.ppTypedOperand, PP.ppVal, PP.ppType]

inductive ExecFnRel (mod_ : LLVMModule) (fn : LLVMFn) (args : List LLVMVal) : Nat → ExecOutcome → Prop where
  | noEntry (fuel : Nat) (h : fn.blocks = []) :
      ExecFnRel mod_ fn args fuel (.ub "function has no entry block")
  | badArity (fuel : Nat) (entry : LLVMBlock) (rest : List LLVMBlock)
      (h : fn.blocks = entry :: rest) (hbind : bindArgs {} fn.params args = none) :
      ExecFnRel mod_ fn args fuel (.ub "argument arity mismatch")
  | ran (fuel : Nat) (entry : LLVMBlock) (rest : List LLVMBlock) (st : ExecState) (out : ExecOutcome)
      (h : fn.blocks = entry :: rest) (hbind : bindArgs {} fn.params args = some st)
      (hrun : execBlock mod_ fn fuel st entry = out) :
      ExecFnRel mod_ fn args fuel out

theorem execFnRel_iff (mod_ : LLVMModule) (fn : LLVMFn) (args : List LLVMVal) (fuel : Nat) (out : ExecOutcome) :
    ExecFnRel mod_ fn args fuel out ↔ execFn mod_ fn args fuel = out := by
  constructor
  · intro h
    cases h
    all_goals simp_all [execFn]
  · intro h
    unfold execFn at h
    cases hblocks : fn.blocks with
    | nil =>
      simp [hblocks] at h
      subst h
      exact ExecFnRel.noEntry fuel hblocks
    | cons entry rest =>
      simp [hblocks] at h
      cases hbind : bindArgs {} fn.params args with
      | none =>
        simp [hbind] at h
        subst h
        exact ExecFnRel.badArity fuel entry rest hblocks hbind
      | some st =>
        simp [hbind] at h
        exact ExecFnRel.ran fuel entry rest st out hblocks hbind h

theorem execFn_deterministic (mod_ : LLVMModule) (fn : LLVMFn) (args : List LLVMVal) (fuel : Nat)
    (out1 out2 : ExecOutcome)
    (h1 : ExecFnRel mod_ fn args fuel out1)
    (h2 : ExecFnRel mod_ fn args fuel out2) :
    out1 = out2 := by
  have e1 := (execFnRel_iff mod_ fn args fuel out1).mp h1
  have e2 := (execFnRel_iff mod_ fn args fuel out2).mp h2
  rw [← e1, e2]

theorem stepInstrWith_mono
    (rc1 rc2 : ExecState → Option RegName → LLVMType → GlobalSym → List LLVMVal → ExecOutcome ⊕ ExecState)
    (st : ExecState) (ins : LLVMInstr)
    (hrc : ∀ st' dst? ty callee args,
      rc1 st' dst? ty callee args ≠ .inl .outOfFuel →
      rc2 st' dst? ty callee args = rc1 st' dst? ty callee args)
    (hfin : stepInstrWith rc1 st ins ≠ .inl .outOfFuel) :
    stepInstrWith rc2 st ins = stepInstrWith rc1 st ins := by
  cases ins with
  | call dst? retTy callee args =>
    simp only [stepInstrWith] at hfin ⊢
    exact hrc st dst? retTy callee (args.map fun pair => evalTypedOperand st pair.fst pair.snd) hfin
  | _ => rfl

theorem execInstrsWith_mono
    (rc1 rc2 : ExecState → Option RegName → LLVMType → GlobalSym → List LLVMVal → ExecOutcome ⊕ ExecState)
    (st : ExecState) (is : List LLVMInstr)
    (hrc : ∀ st' dst? ty callee args,
      rc1 st' dst? ty callee args ≠ .inl .outOfFuel →
      rc2 st' dst? ty callee args = rc1 st' dst? ty callee args)
    (hfin : execInstrsWith rc1 st is ≠ .inl .outOfFuel) :
    execInstrsWith rc2 st is = execInstrsWith rc1 st is := by
  induction is generalizing st with
  | nil => rfl
  | cons ins rest ih =>
    simp only [execInstrsWith] at hfin ⊢
    have hstep : stepInstrWith rc1 st ins ≠ .inl .outOfFuel := by
      intro ho
      rw [ho] at hfin
      exact hfin rfl
    rw [stepInstrWith_mono rc1 rc2 st ins hrc hstep]
    cases hst : stepInstrWith rc1 st ins with
    | inl o => rfl
    | inr st' =>
      rw [hst] at hfin
      exact ih st' hfin

theorem execBlockWith_mono
    (rc1 rc2 : ExecState → Option RegName → LLVMType → GlobalSym → List LLVMVal → ExecOutcome ⊕ ExecState)
    (fn : LLVMFn) (f1 f2 : Nat) (st : ExecState) (blk : LLVMBlock)
    (hrc : ∀ st' dst? ty callee args,
      rc1 st' dst? ty callee args ≠ .inl .outOfFuel →
      rc2 st' dst? ty callee args = rc1 st' dst? ty callee args)
    (hle : f1 ≤ f2)
    (hfin : execBlockWith rc1 fn f1 st blk ≠ .outOfFuel) :
    execBlockWith rc2 fn f2 st blk = execBlockWith rc1 fn f1 st blk := by
  induction f1 generalizing f2 st blk with
  | zero => exact False.elim (hfin rfl)
  | succ k ih =>
    cases f2 with
    | zero => omega
    | succ m =>
      simp only [execBlockWith] at hfin ⊢
      have his : execInstrsWith rc1 (commitPhis st (evalPhis st st.prevBlock blk.phis)) blk.body ≠ .inl .outOfFuel := by
        intro ho
        rw [ho] at hfin
        exact hfin rfl
      rw [execInstrsWith_mono rc1 rc2 (commitPhis st (evalPhis st st.prevBlock blk.phis)) blk.body hrc his]
      cases hexec : execInstrsWith rc1 (commitPhis st (evalPhis st st.prevBlock blk.phis)) blk.body with
      | inl out =>
        cases out <;> simp
      | inr st' =>
        simp only [hexec] at hfin ⊢
        cases hterm : blk.term with
        | br lbl =>
          simp only [hterm] at hfin ⊢
          cases hfind : findBlock fn lbl with
          | none => simp
          | some next =>
            simp only [hfind] at hfin ⊢
            exact ih m { st' with prevBlock := some blk.label } next (by omega) hfin
        | condBr condOp tLbl eLbl =>
          simp only [hterm] at hfin ⊢
          cases heval : evalOperand st' condOp with
          | poison => simp
          | bits wb vb =>
            cases wb with
            | i1 =>
              simp only [heval] at hfin ⊢
              cases hfind : findBlock fn (if vb == 1#1 then tLbl else eLbl) with
              | none => simp
              | some next =>
                simp only [hfind] at hfin ⊢
                exact ih m { st' with prevBlock := some blk.label } next (by omega) hfin
            | i8 | i16 | i32 | i64 | i128 | i256 | i512 => simp
          | ptr _ => simp
          | floatBits _ _ => simp
          | aggNil => simp
          | aggCons _ _ => simp
        | switch w scrutOp defLbl cases =>
          simp only [hterm] at hfin ⊢
          cases heval : evalOperand st' scrutOp with
          | poison => simp
          | bits ws sv =>
            by_cases hws : ws = w
            · subst hws
              simp only [heval, ↓reduceDIte] at hfin ⊢
              cases hfind : findBlock fn (((cases.find? (fun pair => pair.fst == sv)).map (·.snd)).getD defLbl) with
              | none => simp
              | some next =>
                simp only [hfind] at hfin ⊢
                exact ih m { st' with prevBlock := some blk.label } next (by omega) hfin
            · simp [hws]
          | ptr _ => simp
          | floatBits _ _ => simp
          | aggNil => simp
          | aggCons _ _ => simp
        | ret rv =>
          cases rv with
          | none => simp
          | some p =>
            cases p
            simp
        | unreachable => simp

theorem runCallWith_mono (mod_ : LLVMModule) (f1 f2 : Nat)
    (st : ExecState) (dst? : Option RegName) (retTy : LLVMType) (callee : GlobalSym) (args : List LLVMVal)
    (hle : f1 ≤ f2)
    (hfin : runCallWith mod_ f1 st dst? retTy callee args ≠ .inl .outOfFuel) :
    runCallWith mod_ f2 st dst? retTy callee args = runCallWith mod_ f1 st dst? retTy callee args := by
  induction f1 generalizing f2 st dst? retTy callee args with
  | zero =>
    cases f2 with
    | zero => rfl
    | succ m =>
      simp only [runCallWith] at hfin ⊢
      by_cases htrap : callee == "llvm.trap"
      · simp [htrap]
      · simp only [htrap, Bool.false_eq_true, ↓reduceIte] at hfin ⊢
        cases hintr : intrinsicResult callee args with
        | some v => simp
        | none =>
          rw [hintr] at hfin
          exact False.elim (hfin rfl)
  | succ k ih =>
    cases f2 with
    | zero => omega
    | succ m =>
      simp only [runCallWith] at hfin ⊢
      by_cases htrap : callee == "llvm.trap"
      · simp [htrap]
      · simp only [htrap, Bool.false_eq_true, ↓reduceIte] at hfin ⊢
        cases hintr : intrinsicResult callee args with
        | some v => simp
        | none =>
          simp only [hintr] at hfin ⊢
          cases hfn : mod_.fns.find? (fun f => f.name == callee) with
          | none => rfl
          | some fn =>
            simp only [hfn] at hfin ⊢
            cases hblks : fn.blocks with
            | nil => rfl
            | cons entry rest =>
              simp only [hblks] at hfin ⊢
              cases hbind : bindArgs { mem := st.mem } fn.params args with
              | none => rfl
              | some calleeSt =>
                simp only [hbind] at hfin ⊢
                have hblkFin : execBlockWith (runCallWith mod_ k) fn (k + 1) calleeSt entry ≠ .outOfFuel := by
                  intro ho
                  rw [ho] at hfin
                  exact hfin rfl
                have hrc_k : ∀ st' d ty c as,
                    runCallWith mod_ k st' d ty c as ≠ .inl .outOfFuel →
                    runCallWith mod_ m st' d ty c as = runCallWith mod_ k st' d ty c as := by
                  intro st' d ty c as hc
                  exact ih m st' d ty c as (by omega) hc
                rw [execBlockWith_mono (runCallWith mod_ k) (runCallWith mod_ m) fn (k + 1) (m + 1)
                    calleeSt entry hrc_k (by omega) hblkFin]

theorem execBlock_mono (mod_ : LLVMModule) (fn : LLVMFn) (f1 f2 : Nat) (st : ExecState) (blk : LLVMBlock)
    (hle : f1 ≤ f2)
    (hfin : execBlock mod_ fn f1 st blk ≠ .outOfFuel) :
    execBlock mod_ fn f2 st blk = execBlock mod_ fn f1 st blk := by
  unfold execBlock at hfin ⊢
  have hblkFin : execBlockWith (runCallWith mod_ f1) fn f1 st blk ≠ .outOfFuel := by
    intro ho
    rw [ho] at hfin
    exact hfin rfl
  have heq := execBlockWith_mono (runCallWith mod_ f1) (runCallWith mod_ f2) fn f1 f2 st blk
    (fun st' dst? ty callee args hc => runCallWith_mono mod_ f1 f2 st' dst? ty callee args hle hc)
    hle hblkFin
  rw [heq]

theorem execFn_mono_fuel (mod_ : LLVMModule) (fn : LLVMFn) (args : List LLVMVal) (f1 f2 : Nat)
    (hle : f1 ≤ f2)
    (hfin : execFn mod_ fn args f1 ≠ .outOfFuel) :
    execFn mod_ fn args f2 = execFn mod_ fn args f1 := by
  unfold execFn at hfin ⊢
  cases hblocks : fn.blocks with
  | nil => simp
  | cons entry rest =>
    cases hbind : bindArgs {} fn.params args with
    | none => simp
    | some st =>
      simp only [hblocks, hbind] at hfin ⊢
      exact execBlock_mono mod_ fn f1 f2 st entry hle hfin

end LeanNative.Backend.LLVMAst
