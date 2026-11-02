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

inductive LLVMType where
  | void
  | int : IntWidth → LLVMType
  | float : FloatWidth → LLVMType
  | ptr : AddrSpace → LLVMType
  | structNil : LLVMType
  | structCons : LLVMType → LLVMType → LLVMType
  | array : Nat → LLVMType → LLVMType
  | vec : Nat → LLVMType → LLVMType
  deriving Repr, DecidableEq, Inhabited

namespace LLVMType

def struct (fields : List LLVMType) : LLVMType :=
  fields.foldr .structCons .structNil

def byteSize : LLVMType → Nat
  | .void => 0
  | .int w => w.byteSize
  | .float fw => fw.byteSize
  | .ptr _ => 8
  | .structNil => 0
  | .structCons h t => h.byteSize + t.byteSize
  | .array n et => n * et.byteSize
  | .vec n et => n * et.byteSize

end LLVMType

inductive Operand where
  | reg : RegName → Operand
  | constInt : (w : IntWidth) → BitVec w.bits → Operand
  | constFloat : (fw : FloatWidth) → BitVec fw.bits → Operand
  | constNull : Operand
  | aggNil : Operand
  | aggCons : Operand → Operand → Operand
  | poison : Operand
  deriving Repr, DecidableEq, Inhabited

def Operand.constAgg (ops : List Operand) : Operand :=
  ops.foldr .aggCons .aggNil

inductive LLVMInstr where
  | alloca : RegName → LLVMType → Nat → LLVMInstr
  | load : RegName → LLVMType → Operand → Nat → LLVMInstr
  | store : LLVMType → Operand → Operand → Nat → LLVMInstr
  | add : RegName → OverflowFlags → IntWidth → Operand → Operand → LLVMInstr
  | sub : RegName → OverflowFlags → IntWidth → Operand → Operand → LLVMInstr
  | mul : RegName → OverflowFlags → IntWidth → Operand → Operand → LLVMInstr
  | udiv : RegName → IntWidth → Operand → Operand → LLVMInstr
  | sdiv : RegName → IntWidth → Operand → Operand → LLVMInstr
  | urem : RegName → IntWidth → Operand → Operand → LLVMInstr
  | srem : RegName → IntWidth → Operand → Operand → LLVMInstr
  | and_ : RegName → IntWidth → Operand → Operand → LLVMInstr
  | or_ : RegName → IntWidth → Operand → Operand → LLVMInstr
  | xor : RegName → IntWidth → Operand → Operand → LLVMInstr
  | shl : RegName → OverflowFlags → IntWidth → Operand → Operand → LLVMInstr
  | lshr : RegName → IntWidth → Operand → Operand → LLVMInstr
  | ashr : RegName → IntWidth → Operand → Operand → LLVMInstr
  | icmp : RegName → ICmpPred → IntWidth → Operand → Operand → LLVMInstr
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
  | getelementptr : RegName → LLVMType → Operand → List Operand → LLVMInstr
  | select : RegName → Operand → LLVMType → Operand → Operand → LLVMInstr
  | phi : RegName → LLVMType → List (Operand × BlockLabel) → LLVMInstr
  | call : Option RegName → LLVMType → GlobalSym → List Operand → LLVMInstr
  | atomicrmw : RegName → AtomicRMWOp → Operand → IntWidth → Operand → AtomicOrdering → Nat → LLVMInstr
  | insertelement : RegName → Nat → LLVMType → Operand → Operand → Operand → LLVMInstr
  | extractelement : RegName → Nat → LLVMType → Operand → Operand → LLVMInstr
  | shufflevector : RegName → Nat → Nat → LLVMType → Operand → Operand → List Nat → LLVMInstr
  | insertvalue : RegName → LLVMType → Operand → Operand → Nat → LLVMInstr
  | extractvalue : RegName → LLVMType → Operand → Nat → LLVMInstr
  deriving Repr, DecidableEq, Inhabited

inductive Terminator where
  | br : BlockLabel → Terminator
  | condBr : Operand → BlockLabel → BlockLabel → Terminator
  | switch : IntWidth → Operand → BlockLabel → List (BitVec 64 × BlockLabel) → Terminator
  | ret : Option (LLVMType × Operand) → Terminator
  | unreachable : Terminator
  deriving Repr, DecidableEq, Inhabited

structure LLVMBlock where
  label : BlockLabel
  phis : List LLVMInstr := []
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
  init : Option Operand := none
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
  | .aggNil => .aggNil
  | .aggCons h t => .aggCons (evalOperand st h) (evalOperand st t)
  | .poison => .poison

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

def fcmpEval (p : FCmpPred) (fw : FloatWidth) (a b : BitVec fw.bits) : Bool :=
  let aNaN := a == 0#(fw.bits)
  let bNaN := b == 0#(fw.bits)
  let unordered := aNaN || bNaN
  let eqAB := a == b
  let ltAB := a.toNat < b.toNat
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

def checkAlign (addr : BitVec 64) (align : Nat) : Bool :=
  align == 0 || isAligned addr align

def storeVal (m : ByteMem) (addr : BitVec 64) (v : LLVMVal) : ByteMem :=
  match v with
  | .bits w bv => m.storeInt addr w bv
  | .ptr p => m.storePtr addr p
  | .floatBits fw fb => m.storeFloatBits addr fw fb
  | .poison => m.storePoison addr
  | .aggNil => m
  | .aggCons _ _ => m

def loadVal (m : ByteMem) (addr : BitVec 64) (ty : LLVMType) : LLVMVal :=
  if m.isPoisonCell addr then .poison
  else
    match ty with
    | .int w => .bits w (m.loadInt addr w)
    | .ptr _ => .ptr (m.loadPtr addr)
    | .float fw => .floatBits fw (m.loadFloatBits addr fw)
    | .void => .aggNil
    | .structNil => .aggNil
    | .structCons _ _ => .aggNil
    | .array _ _ => .aggNil
    | .vec _ _ => .aggNil

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

def divOrRem (dst : RegName) (st : ExecState) (w : IntWidth) (a b : LLVMVal)
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
          .inr (bindReg st dst (.bits w res))
      else .inl (.ub "operand width mismatch")
    else .inl (.ub "operand width mismatch")
  | _, _ => .inl (.ub "non-integer operand")

def shiftResult (dst : RegName) (st : ExecState) (w : IntWidth) (flags : OverflowFlags)
    (a b : LLVMVal) (kind : String) : ExecOutcome ⊕ ExecState :=
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
          let nsw := if kind == "shl" then shlOverflowNSW w va' vb' else false
          let nuw := if kind == "shl" then shlOverflowNUW w va' vb' else false
          if flagsOverflow flags nsw nuw then .inr (bindReg st dst .poison)
          else .inr (bindReg st dst (.bits w res))
      else .inl (.ub "operand width mismatch")
    else .inl (.ub "operand width mismatch")
  | _, _ => .inl (.ub "non-integer operand")

def resolvePhi (st : ExecState) (prev : Option BlockLabel) (incomings : List (Operand × BlockLabel)) : LLVMVal :=
  match prev with
  | none => .poison
  | some lbl =>
    match incomings.find? (fun pair => pair.snd == lbl) with
    | none => .poison
    | some (op, _) => evalOperand st op

def bindArgs (st : ExecState) : List LLVMParam → List LLVMVal → Option ExecState
  | [], [] => some st
  | p :: ps, v :: vs => bindArgs (bindReg st p.name v) ps vs
  | _, _ => none

def stepInstr (mod_ : LLVMModule) (st : ExecState) : LLVMInstr → ExecOutcome ⊕ ExecState
  | .alloca dst ty align =>
    match st.mem.allocAligned ty.byteSize (if isPow2 align then align else 1) with
    | none => .inl (.ub "alloca out of address space")
    | some (ptr, mem') =>
      .inr (bindReg { st with mem := mem' } dst (.ptr ptr))
  | .load dst ty ptrOp align =>
    match evalOperand st ptrOp with
    | .poison => .inl (.ub "load from poison pointer")
    | .ptr addr =>
      if addr == 0#64 then .inl (.ub "load from null pointer")
      else if checkAlign addr align then
        .inr (bindReg st dst (loadVal st.mem addr ty))
      else .inl (.ub "misaligned load")
    | _ => .inl (.ub "load from non-pointer")
  | .store _ty valOp ptrOp align =>
    let val := evalOperand st valOp
    match evalOperand st ptrOp with
    | .poison => .inl (.ub "store to poison pointer")
    | .ptr addr =>
      if addr == 0#64 then .inl (.ub "store to null pointer")
      else if checkAlign addr align then
        .inr { st with mem := storeVal st.mem addr val }
      else .inl (.ub "misaligned store")
    | _ => .inl (.ub "store to non-pointer")
  | .add dst flags w aOp bOp =>
    binResult dst st w flags (evalOperand st aOp) (evalOperand st bOp) "add"
  | .sub dst flags w aOp bOp =>
    binResult dst st w flags (evalOperand st aOp) (evalOperand st bOp) "sub"
  | .mul dst flags w aOp bOp =>
    binResult dst st w flags (evalOperand st aOp) (evalOperand st bOp) "mul"
  | .udiv dst w aOp bOp =>
    divOrRem dst st w (evalOperand st aOp) (evalOperand st bOp) false false
  | .sdiv dst w aOp bOp =>
    divOrRem dst st w (evalOperand st aOp) (evalOperand st bOp) true false
  | .urem dst w aOp bOp =>
    divOrRem dst st w (evalOperand st aOp) (evalOperand st bOp) false true
  | .srem dst w aOp bOp =>
    divOrRem dst st w (evalOperand st aOp) (evalOperand st bOp) true true
  | .and_ dst w aOp bOp =>
    binResult dst st w .none (evalOperand st aOp) (evalOperand st bOp) "and"
  | .or_ dst w aOp bOp =>
    binResult dst st w .none (evalOperand st aOp) (evalOperand st bOp) "or"
  | .xor dst w aOp bOp =>
    binResult dst st w .none (evalOperand st aOp) (evalOperand st bOp) "xor"
  | .shl dst flags w aOp bOp =>
    shiftResult dst st w flags (evalOperand st aOp) (evalOperand st bOp) "shl"
  | .lshr dst w aOp bOp =>
    shiftResult dst st w .none (evalOperand st aOp) (evalOperand st bOp) "lshr"
  | .ashr dst w aOp bOp =>
    shiftResult dst st w .none (evalOperand st aOp) (evalOperand st bOp) "ashr"
  | .icmp dst pred w aOp bOp =>
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
  | .fadd dst fw aOp bOp =>
    match evalOperand st aOp, evalOperand st bOp with
    | .poison, _ => .inr (bindReg st dst .poison)
    | _, .poison => .inr (bindReg st dst .poison)
    | .floatBits fa va, .floatBits fb vb =>
      if hfa : fa = fw then
        if hfb : fb = fw then
          .inr (bindReg st dst (.floatBits fw ((hfa ▸ va) + (hfb ▸ vb))))
        else .inl (.ub "fadd width mismatch")
      else .inl (.ub "fadd width mismatch")
    | _, _ => .inl (.ub "fadd on non-float")
  | .fsub dst fw aOp bOp =>
    match evalOperand st aOp, evalOperand st bOp with
    | .poison, _ => .inr (bindReg st dst .poison)
    | _, .poison => .inr (bindReg st dst .poison)
    | .floatBits fa va, .floatBits fb vb =>
      if hfa : fa = fw then
        if hfb : fb = fw then
          .inr (bindReg st dst (.floatBits fw ((hfa ▸ va) - (hfb ▸ vb))))
        else .inl (.ub "fsub width mismatch")
      else .inl (.ub "fsub width mismatch")
    | _, _ => .inl (.ub "fsub on non-float")
  | .fmul dst fw aOp bOp =>
    match evalOperand st aOp, evalOperand st bOp with
    | .poison, _ => .inr (bindReg st dst .poison)
    | _, .poison => .inr (bindReg st dst .poison)
    | .floatBits fa va, .floatBits fb vb =>
      if hfa : fa = fw then
        if hfb : fb = fw then
          .inr (bindReg st dst (.floatBits fw ((hfa ▸ va) * (hfb ▸ vb))))
        else .inl (.ub "fmul width mismatch")
      else .inl (.ub "fmul width mismatch")
    | _, _ => .inl (.ub "fmul on non-float")
  | .fdiv dst fw aOp bOp =>
    match evalOperand st aOp, evalOperand st bOp with
    | .poison, _ => .inr (bindReg st dst .poison)
    | _, .poison => .inr (bindReg st dst .poison)
    | .floatBits fa va, .floatBits fb vb =>
      if hfa : fa = fw then
        if hfb : fb = fw then
          let vb' : BitVec fw.bits := hfb ▸ vb
          if vb' == 0#fw.bits then .inl (.ub "float division by zero")
          else .inr (bindReg st dst (.floatBits fw ((hfa ▸ va) / vb')))
        else .inl (.ub "fdiv width mismatch")
      else .inl (.ub "fdiv width mismatch")
    | _, _ => .inl (.ub "fdiv on non-float")
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
    let v := evalOperand st op
    if srcTy.byteSize == dstTy.byteSize then
      if isPoison v then .inr (bindReg st dst .poison)
      else .inr (bindReg st dst v)
    else .inl (.ub "bitcast size mismatch")
  | .inttoptr dst srcW op _as =>
    match evalOperand st op with
    | .poison => .inr (bindReg st dst .poison)
    | .bits w v =>
      if h : w = srcW then
        .inr (bindReg st dst (.ptr ((h ▸ v).zeroExtend 64)))
      else .inl (.ub "inttoptr width mismatch")
    | _ => .inl (.ub "inttoptr on non-integer")
  | .ptrtoint dst _as op dstW =>
    match evalOperand st op with
    | .poison => .inr (bindReg st dst .poison)
    | .ptr p =>
      .inr (bindReg st dst (.bits dstW (p.truncate dstW.bits)))
    | _ => .inl (.ub "ptrtoint on non-pointer")
  | .getelementptr dst ty baseOp idxs =>
    match evalOperand st baseOp with
    | .poison => .inr (bindReg st dst .poison)
    | .ptr base =>
      let scale := Nat.max ty.byteSize 1
      let off := idxs.foldl (fun acc idx =>
        match evalOperand st idx with
        | .bits _ iv => acc + iv.toNat * scale
        | .poison => acc + scale
        | _ => acc) 0
      .inr (bindReg st dst (.ptr (BitVec.ofNat 64 (base.toNat + off))))
    | _ => .inl (.ub "getelementptr on non-pointer")
  | .select dst condOp ty tOp eOp =>
    let _selTy := ty.byteSize
    match evalOperand st condOp with
    | .poison => .inr (bindReg st dst .poison)
    | .bits .i1 c =>
      if c == 1#1 then .inr (bindReg st dst (evalOperand st tOp))
      else .inr (bindReg st dst (evalOperand st eOp))
    | _ => .inl (.ub "select condition is not i1")
  | .phi dst ty incomings =>
    let resolved := resolvePhi st st.prevBlock incomings
    let _phiSize := ty.byteSize
    .inr (bindReg st dst resolved)
  | .call dst? retTy callee args =>
    let argVals := args.map (evalOperand st)
    if callee == "llvm.trap" then .inl (.ub "trap")
    else
      match mod_.fns.find? (fun f => f.name == callee) with
      | none =>
        match dst? with
        | none => .inr st
        | some dst =>
          if retTy == LLVMType.void || argVals.isEmpty then .inr st
          else .inr (bindReg st dst .poison)
      | some fn =>
        match fn.blocks with
        | [] => .inl (.ub "callee has no entry block")
        | entry :: _ =>
          match bindArgs {} fn.params argVals with
          | none => .inl (.ub "callee arity mismatch")
          | some calleeSt =>
            match entry.term with
            | .ret (some (_rty, rop)) =>
              match entry.phis, entry.body with
              | [], [] =>
                let rv := evalOperand calleeSt rop
                match dst? with
                | none => .inr st
                | some dst => .inr (bindReg st dst rv)
              | _, _ =>
                match dst? with
                | none => .inr st
                | some dst => if retTy == LLVMType.void then .inr st else .inr (bindReg st dst .poison)
            | .ret none =>
              match dst? with
              | none => .inr st
              | some dst => if retTy == LLVMType.void then .inr st else .inr (bindReg st dst .poison)
            | .unreachable => .inl (.ub "callee unreachable")
            | _ =>
              match dst? with
              | none => .inr st
              | some dst => if retTy == LLVMType.void then .inr st else .inr (bindReg st dst .poison)
  | .atomicrmw dst op ptrOp w valOp _ord align =>
    match evalOperand st ptrOp with
    | .poison => .inl (.ub "atomicrmw on poison pointer")
    | .ptr addr =>
      if checkAlign addr align then
        match evalOperand st valOp with
        | .poison => .inr (bindReg { st with mem := st.mem.storePoison addr } dst .poison)
        | .bits wv vv =>
          if h : wv = w then
            let old := st.mem.loadInt addr w
            let mem' := st.mem.storeInt addr w (evalRMWOp op w old (h ▸ vv))
            .inr (bindReg { st with mem := mem' } dst (.bits w old))
          else .inl (.ub "atomicrmw width mismatch")
        | _ => .inl (.ub "atomicrmw non-integer value")
      else .inl (.ub "misaligned atomicrmw")
    | _ => .inl (.ub "atomicrmw on non-pointer")
  | .insertelement dst n et vecOp elemOp idxOp =>
    let _elemSize := et.byteSize
    match evalOperand st idxOp with
    | .poison => .inr (bindReg st dst .poison)
    | .bits _ iv =>
      if n ≤ iv.toNat then .inl (.ub "insertelement index out of range")
      else
        let vval := evalOperand st vecOp
        if isPoison vval then .inr (bindReg st dst .poison)
        else
          match vval.toList? with
          | some vs =>
            let vs' := vs.set iv.toNat (evalOperand st elemOp)
            .inr (bindReg st dst (LLVMVal.agg vs'))
          | none => .inl (.ub "insertelement on non-vector")
    | _ => .inl (.ub "insertelement non-integer index")
  | .extractelement dst n et vecOp idxOp =>
    let _elemSize := et.byteSize
    match evalOperand st idxOp with
    | .poison => .inr (bindReg st dst .poison)
    | .bits _ iv =>
      if n ≤ iv.toNat then .inl (.ub "extractelement index out of range")
      else
        let vval := evalOperand st vecOp
        if isPoison vval then .inr (bindReg st dst .poison)
        else
          match vval.toList? with
          | some vs => .inr (bindReg st dst (vs.getD iv.toNat .poison))
          | none => .inl (.ub "extractelement on non-vector")
    | _ => .inl (.ub "extractelement non-integer index")
  | .shufflevector dst n m et aOp bOp mask =>
    let _lane := n + m + et.byteSize
    let av := evalOperand st aOp
    let bv := evalOperand st bOp
    if isPoison av || isPoison bv then .inr (bindReg st dst .poison)
    else
      match av.toList?, bv.toList? with
      | some va, some vb =>
        let picked := mask.map fun i => (va ++ vb).getD i .poison
        .inr (bindReg st dst (LLVMVal.agg picked))
      | _, _ => .inl (.ub "shufflevector on non-vector")
  | .insertvalue dst ty aggOp elemOp idx =>
    let _aggSize := ty.byteSize
    let aval := evalOperand st aggOp
    if isPoison aval then .inr (bindReg st dst .poison)
    else
      match aval.toList? with
      | some vs =>
        if vs.length ≤ idx then .inl (.ub "insertvalue index out of range")
        else .inr (bindReg st dst (LLVMVal.agg (vs.set idx (evalOperand st elemOp))))
      | none => .inl (.ub "insertvalue on non-aggregate")
  | .extractvalue dst ty aggOp idx =>
    let _aggSize := ty.byteSize
    let aval := evalOperand st aggOp
    if isPoison aval then .inr (bindReg st dst .poison)
    else
      match aval.toList? with
      | some vs =>
        if vs.length ≤ idx then .inl (.ub "extractvalue index out of range")
        else .inr (bindReg st dst (vs.getD idx .poison))
      | none => .inl (.ub "extractvalue on non-aggregate")

def execInstrs (mod_ : LLVMModule) (st : ExecState) : List LLVMInstr → ExecOutcome ⊕ ExecState
  | [] => .inr st
  | ins :: rest =>
    match stepInstr mod_ st ins with
    | .inl out => .inl out
    | .inr st' => execInstrs mod_ st' rest

def findBlock (fn : LLVMFn) (lbl : BlockLabel) : Option LLVMBlock :=
  fn.blocks.find? (fun b => b.label == lbl)

def execBlock (mod_ : LLVMModule) (fn : LLVMFn) (fuel : Nat) (st : ExecState) (blk : LLVMBlock) : ExecOutcome :=
  match fuel with
  | 0 => .outOfFuel
  | k + 1 =>
    match execInstrs mod_ st (blk.phis ++ blk.body) with
    | .inl out => out
    | .inr st' =>
      match blk.term with
      | .br lbl =>
        match findBlock fn lbl with
        | none => .ub "branch to missing block"
        | some next => execBlock mod_ fn k { st' with prevBlock := some blk.label } next
      | .condBr condOp tLbl eLbl =>
        match evalOperand st' condOp with
        | .poison => .ub "conditional branch on poison"
        | .bits .i1 c =>
          let lbl := if c == 1#1 then tLbl else eLbl
          match findBlock fn lbl with
          | none => .ub "branch to missing block"
          | some next => execBlock mod_ fn k { st' with prevBlock := some blk.label } next
        | _ => .ub "conditional branch on non-i1"
      | .switch w scrutOp defLbl cases =>
        match evalOperand st' scrutOp with
        | .poison => .ub "switch on poison"
        | .bits ws sv =>
          if h : ws = w then
            let key := (h ▸ sv).zeroExtend 64
            let lbl := (cases.find? (fun pair => pair.fst == key)).map (·.snd) |>.getD defLbl
            match findBlock fn lbl with
            | none => .ub "switch to missing block"
            | some next => execBlock mod_ fn k { st' with prevBlock := some blk.label } next
          else .ub "switch width mismatch"
        | _ => .ub "switch on non-integer"
      | .ret none => .returned none
      | .ret (some (_ty, op)) => .returned (some (evalOperand st' op))
      | .unreachable => .ub "unreachable"

def execFn (mod_ : LLVMModule) (fn : LLVMFn) (args : List LLVMVal) (fuel : Nat) : ExecOutcome :=
  match fn.blocks with
  | [] => .ub "function has no entry block"
  | entry :: _ =>
    match bindArgs {} fn.params args with
    | none => .ub "argument arity mismatch"
    | some st => execBlock mod_ fn fuel st entry

namespace PP

def ppInt (n : Nat) : String := toString n

def ppICmp : ICmpPred → String
  | .eq => "eq" | .ne => "ne" | .ult => "ult" | .ule => "ule" | .ugt => "ugt"
  | .uge => "uge" | .slt => "slt" | .sle => "sle" | .sgt => "sgt" | .sge => "sge"

def ppFCmp : FCmpPred → String
  | .oeq => "oeq" | .one => "one" | .olt => "olt" | .ole => "ole" | .ogt => "ogt" | .oge => "oge"
  | .ord => "ord" | .uno => "uno" | .ueq => "ueq" | .une => "une" | .ult => "ult" | .ule => "ule"
  | .ugt => "ugt" | .uge => "uge" | .true_ => "true" | .false_ => "false"

def ppFlags : OverflowFlags → String
  | .none => "" | .nsw => " nsw" | .nuw => " nuw" | .nswNuw => " nsw nuw"

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

def ppTypeAux (inStruct : Bool) : LLVMType → String
  | .void => "void"
  | .int w => w.pp
  | .float fw => fw.pp
  | .ptr as_ => if as_ == 0 then "ptr" else "ptr addrspace(" ++ ppInt as_ ++ ")"
  | .structNil => if inStruct then "" else "{ }"
  | .structCons h .structNil =>
    if inStruct then ppTypeAux false h else "{ " ++ ppTypeAux false h ++ " }"
  | .structCons h t =>
    if inStruct then ppTypeAux false h ++ ", " ++ ppTypeAux true t
    else "{ " ++ ppTypeAux false h ++ ", " ++ ppTypeAux true t ++ " }"
  | .array n et => "[" ++ ppInt n ++ " x " ++ ppTypeAux false et ++ "]"
  | .vec n et => "<" ++ ppInt n ++ " x " ++ ppTypeAux false et ++ ">"

def ppType (ty : LLVMType) : String :=
  ppTypeAux false ty

def ppOperandAux (inAgg : Bool) : Operand → String
  | .reg r => "%" ++ r
  | .constInt w v => w.pp ++ " " ++ ppInt v.toNat
  | .constFloat fw v => fw.pp ++ " " ++ ppInt v.toNat
  | .constNull => "ptr null"
  | .aggNil => if inAgg then "" else "{ }"
  | .aggCons h .aggNil =>
    if inAgg then ppOperandAux false h else "{ " ++ ppOperandAux false h ++ " }"
  | .aggCons h t =>
    if inAgg then ppOperandAux false h ++ ", " ++ ppOperandAux true t
    else "{ " ++ ppOperandAux false h ++ ", " ++ ppOperandAux true t ++ " }"
  | .poison => "poison"

def ppOperand (op : Operand) : String :=
  ppOperandAux false op

def ppInstr : LLVMInstr → String
  | .alloca dst ty align =>
    "%" ++ dst ++ " = alloca " ++ ppType ty ++ ", align " ++ ppInt align
  | .load dst ty ptrOp align =>
    "%" ++ dst ++ " = load " ++ ppType ty ++ ", " ++ ppOperand ptrOp ++ ", align " ++ ppInt align
  | .store ty valOp ptrOp align =>
    "store " ++ ppType ty ++ " " ++ ppOperand valOp ++ ", " ++ ppOperand ptrOp ++ ", align " ++ ppInt align
  | .add dst flags w aOp bOp =>
    "%" ++ dst ++ " = add" ++ ppFlags flags ++ " " ++ w.pp ++ " " ++ ppOperand aOp ++ ", " ++ ppOperand bOp
  | .sub dst flags w aOp bOp =>
    "%" ++ dst ++ " = sub" ++ ppFlags flags ++ " " ++ w.pp ++ " " ++ ppOperand aOp ++ ", " ++ ppOperand bOp
  | .mul dst flags w aOp bOp =>
    "%" ++ dst ++ " = mul" ++ ppFlags flags ++ " " ++ w.pp ++ " " ++ ppOperand aOp ++ ", " ++ ppOperand bOp
  | .udiv dst w aOp bOp =>
    "%" ++ dst ++ " = udiv " ++ w.pp ++ " " ++ ppOperand aOp ++ ", " ++ ppOperand bOp
  | .sdiv dst w aOp bOp =>
    "%" ++ dst ++ " = sdiv " ++ w.pp ++ " " ++ ppOperand aOp ++ ", " ++ ppOperand bOp
  | .urem dst w aOp bOp =>
    "%" ++ dst ++ " = urem " ++ w.pp ++ " " ++ ppOperand aOp ++ ", " ++ ppOperand bOp
  | .srem dst w aOp bOp =>
    "%" ++ dst ++ " = srem " ++ w.pp ++ " " ++ ppOperand aOp ++ ", " ++ ppOperand bOp
  | .and_ dst w aOp bOp =>
    "%" ++ dst ++ " = and " ++ w.pp ++ " " ++ ppOperand aOp ++ ", " ++ ppOperand bOp
  | .or_ dst w aOp bOp =>
    "%" ++ dst ++ " = or " ++ w.pp ++ " " ++ ppOperand aOp ++ ", " ++ ppOperand bOp
  | .xor dst w aOp bOp =>
    "%" ++ dst ++ " = xor " ++ w.pp ++ " " ++ ppOperand aOp ++ ", " ++ ppOperand bOp
  | .shl dst flags w aOp bOp =>
    "%" ++ dst ++ " = shl" ++ ppFlags flags ++ " " ++ w.pp ++ " " ++ ppOperand aOp ++ ", " ++ ppOperand bOp
  | .lshr dst w aOp bOp =>
    "%" ++ dst ++ " = lshr " ++ w.pp ++ " " ++ ppOperand aOp ++ ", " ++ ppOperand bOp
  | .ashr dst w aOp bOp =>
    "%" ++ dst ++ " = ashr " ++ w.pp ++ " " ++ ppOperand aOp ++ ", " ++ ppOperand bOp
  | .icmp dst pred w aOp bOp =>
    "%" ++ dst ++ " = icmp " ++ ppICmp pred ++ " " ++ w.pp ++ " " ++ ppOperand aOp ++ ", " ++ ppOperand bOp
  | .fadd dst fw aOp bOp =>
    "%" ++ dst ++ " = fadd " ++ fw.pp ++ " " ++ ppOperand aOp ++ ", " ++ ppOperand bOp
  | .fsub dst fw aOp bOp =>
    "%" ++ dst ++ " = fsub " ++ fw.pp ++ " " ++ ppOperand aOp ++ ", " ++ ppOperand bOp
  | .fmul dst fw aOp bOp =>
    "%" ++ dst ++ " = fmul " ++ fw.pp ++ " " ++ ppOperand aOp ++ ", " ++ ppOperand bOp
  | .fdiv dst fw aOp bOp =>
    "%" ++ dst ++ " = fdiv " ++ fw.pp ++ " " ++ ppOperand aOp ++ ", " ++ ppOperand bOp
  | .fcmp dst pred fw aOp bOp =>
    "%" ++ dst ++ " = fcmp " ++ ppFCmp pred ++ " " ++ fw.pp ++ " " ++ ppOperand aOp ++ ", " ++ ppOperand bOp
  | .zext dst srcW op dstW =>
    "%" ++ dst ++ " = zext " ++ srcW.pp ++ " " ++ ppOperand op ++ " to " ++ dstW.pp
  | .sext dst srcW op dstW =>
    "%" ++ dst ++ " = sext " ++ srcW.pp ++ " " ++ ppOperand op ++ " to " ++ dstW.pp
  | .trunc dst srcW op dstW =>
    "%" ++ dst ++ " = trunc " ++ srcW.pp ++ " " ++ ppOperand op ++ " to " ++ dstW.pp
  | .bitcast dst srcTy op dstTy =>
    "%" ++ dst ++ " = bitcast " ++ ppType srcTy ++ " " ++ ppOperand op ++ " to " ++ ppType dstTy
  | .inttoptr dst srcW op as_ =>
    "%" ++ dst ++ " = inttoptr " ++ srcW.pp ++ " " ++ ppOperand op ++ " to " ++ ppType (.ptr as_)
  | .ptrtoint dst as_ op dstW =>
    "%" ++ dst ++ " = ptrtoint " ++ ppType (.ptr as_) ++ " " ++ ppOperand op ++ " to " ++ dstW.pp
  | .getelementptr dst ty baseOp idxs =>
    "%" ++ dst ++ " = getelementptr " ++ ppType ty ++ ", " ++ ppOperand baseOp ++
      String.join (idxs.map fun i => ", " ++ ppOperand i)
  | .select dst condOp ty tOp eOp =>
    "%" ++ dst ++ " = select " ++ ppOperand condOp ++ ", " ++ ppType ty ++ " " ++ ppOperand tOp ++ ", " ++ ppType ty ++ " " ++ ppOperand eOp
  | .phi dst ty incomings =>
    "%" ++ dst ++ " = phi " ++ ppType ty ++ " " ++
      String.intercalate ", " (incomings.map fun (op, lbl) => "[ " ++ ppOperand op ++ ", %" ++ lbl ++ " ]")
  | .call dst? retTy callee args =>
    let lhs := match dst? with | none => "" | some dst => "%" ++ dst ++ " = "
    lhs ++ "call " ++ ppType retTy ++ " @" ++ callee ++ "(" ++ String.intercalate ", " (args.map ppOperand) ++ ")"
  | .atomicrmw dst op ptrOp w valOp ord align =>
    "%" ++ dst ++ " = atomicrmw " ++ ppRMW op ++ " " ++ ppOperand ptrOp ++ ", " ++ w.pp ++ " " ++ ppOperand valOp ++
      " " ++ ppOrdering ord ++ ", align " ++ ppInt align
  | .insertelement dst n et vecOp elemOp idxOp =>
    "%" ++ dst ++ " = insertelement " ++ ppType (.vec n et) ++ " " ++ ppOperand vecOp ++ ", " ++
      ppType et ++ " " ++ ppOperand elemOp ++ ", " ++ ppOperand idxOp
  | .extractelement dst n et vecOp idxOp =>
    "%" ++ dst ++ " = extractelement " ++ ppType (.vec n et) ++ " " ++ ppOperand vecOp ++ ", " ++ ppOperand idxOp
  | .shufflevector dst n m et aOp bOp mask =>
    "%" ++ dst ++ " = shufflevector " ++ ppType (.vec n et) ++ " " ++ ppOperand aOp ++ ", " ++ ppType (.vec m et) ++ " " ++ ppOperand bOp ++
      ", <" ++ ppInt mask.length ++ " x i32> " ++ String.intercalate ", " (mask.map ppInt)
  | .insertvalue dst ty aggOp elemOp idx =>
    "%" ++ dst ++ " = insertvalue " ++ ppType ty ++ " " ++ ppOperand aggOp ++ ", " ++ ppOperand elemOp ++ ", " ++ ppInt idx
  | .extractvalue dst ty aggOp idx =>
    "%" ++ dst ++ " = extractvalue " ++ ppType ty ++ " " ++ ppOperand aggOp ++ ", " ++ ppInt idx

def ppTerm : Terminator → String
  | .br lbl => "br label %" ++ lbl
  | .condBr condOp tLbl eLbl => "br " ++ ppOperand condOp ++ ", label %" ++ tLbl ++ ", label %" ++ eLbl
  | .switch w scrutOp defLbl cases =>
    "switch " ++ w.pp ++ " " ++ ppOperand scrutOp ++ ", label %" ++ defLbl ++ " [" ++
      String.intercalate " " (cases.map fun (k, lbl) => w.pp ++ " " ++ ppInt k.toNat ++ ", label %" ++ lbl) ++ "]"
  | .ret none => "ret void"
  | .ret (some (ty, op)) => "ret " ++ ppType ty ++ " " ++ ppOperand op
  | .unreachable => "unreachable"

def ppBlock (b : LLVMBlock) : String :=
  b.label ++ ":\n" ++ String.intercalate "\n" ((b.phis ++ b.body).map (fun i => "  " ++ ppInstr i) ++ ["  " ++ ppTerm b.term])

def ppParam (p : LLVMParam) : String :=
  String.intercalate " " (p.attrs.map ppAttr ++ [ppType p.ty, "%" ++ p.name])

def ppFn (fn : LLVMFn) : String :=
  "define " ++ ppCC fn.cc ++ " " ++ ppType fn.retTy ++ " @" ++ fn.name ++ "(" ++
    String.intercalate ", " (fn.params.map ppParam) ++ ") {\n" ++
    String.intercalate "\n" (fn.blocks.map ppBlock) ++ "\n}"

def ppGlobal (g : LLVMGlobal) : String :=
  "@" ++ g.name ++ " = global " ++ ppType g.ty ++ " " ++
    match g.init with | none => "zeroinitializer" | some op => ppOperand op

def ppExtern (e : LLVMExtern) : String :=
  "declare " ++ ppType e.retTy ++ " @" ++ e.name ++ "(" ++ String.intercalate ", " (e.paramTys.map ppType) ++ ")"

def ppModule (m : LLVMModule) : String :=
  String.intercalate "\n" ([
    "target datalayout = \"" ++ m.dataLayout ++ "\"",
    "target triple = \"" ++ m.triple ++ "\""
  ] ++ m.globals.map ppGlobal ++ m.externs.map ppExtern ++ m.fns.map ppFn)

end PP

theorem add_nsw_overflow_poison (w : IntWidth) (a b : BitVec w.bits)
    (h_ov : addOverflowNSW w a b = true) :
    stepInstr {} {} (.add "r" .nsw w (.constInt w a) (.constInt w b)) =
      .inr (bindReg {} "r" .poison) := by
  simp [stepInstr, evalOperand, binResult, flagsOverflow, h_ov]

theorem shl_overshift_poison (w : IntWidth) (a amt : BitVec w.bits)
    (h_over : w.bits ≤ amt.toNat) :
    stepInstr {} {} (.shl "r" .none w (.constInt w a) (.constInt w amt)) =
      .inr (bindReg {} "r" .poison) := by
  simp [stepInstr, evalOperand, shiftResult, h_over]

theorem udiv_zero_ub (w : IntWidth) (a : BitVec w.bits) :
    stepInstr {} {} (.udiv "r" w (.constInt w a) (.constInt w (0#w.bits))) =
      .inl (.ub "division by zero") := by
  simp [stepInstr, evalOperand, divOrRem]

theorem phi_resolves_predecessor (st : ExecState) (lbl : BlockLabel) (op : Operand) :
    resolvePhi st (some lbl) [(op, lbl)] = evalOperand st op := by
  simp [resolvePhi]

theorem load_after_alloca_store (st : ExecState) (w : IntWidth) (v : BitVec w.bits) (align : Nat)
    (h_pow : isPow2 align = true)
    (ptr : BitVec 64) (mem1 : ByteMem)
    (h_alloc : st.mem.allocAligned w.byteSize align = some (ptr, mem1)) :
    ∃ mem2, stepInstr {} { st with mem := mem1, regs := [("p", .ptr ptr)] }
        (.store (.int w) (.constInt w v) (.reg "p") align) = .inr { st with mem := mem2, regs := [("p", .ptr ptr)] } ∧
      stepInstr {} { st with mem := mem2, regs := [("p", .ptr ptr)] }
        (.load "out" (.int w) (.reg "p") align) =
        .inr (bindReg { st with mem := mem2, regs := [("p", .ptr ptr)] } "out" (.bits w v)) := by
  have h_nz := ByteMem.allocAligned_nonzero st.mem w.byteSize align ptr mem1 h_alloc
  have h_al := ByteMem.allocAligned_isAligned st.mem w.byteSize align ptr mem1 h_pow h_alloc
  have h_np : (mem1.storeInt ptr w v).isPoisonCell ptr = false := by
    simp [ByteMem.isPoisonCell, ByteMem.storeInt, ByteMem.readAt_writeAt_same]
  refine ⟨mem1.storeInt ptr w v, ?_, ?_⟩
  · simp [stepInstr, evalOperand, lookupReg, checkAlign, h_al, h_nz, storeVal]
  · simp [stepInstr, evalOperand, lookupReg, checkAlign, h_al, h_nz, loadVal,
          h_np, ByteMem.load_store_same]

theorem select_cond_poison (ty : LLVMType) (tOp eOp : Operand) :
    stepInstr {} {} (.select "r" .poison ty tOp eOp) =
      .inr (bindReg {} "r" .poison) := by
  simp [stepInstr, evalOperand]

theorem ppInstr_nonempty (ins : LLVMInstr) : PP.ppInstr ins ≠ "" := by
  cases ins <;> simp [PP.ppInstr, PP.ppFlags, PP.ppICmp, PP.ppFCmp, PP.ppRMW, PP.ppOrdering]

theorem ppType_injective (t1 t2 : LLVMType)
    (h1 : ∃ w, t1 = .int w ∨ t1 = .ptr 0 ∨ t1 = .void)
    (h2 : ∃ w, t2 = .int w ∨ t2 = .ptr 0 ∨ t2 = .void)
    (h : PP.ppType t1 = PP.ppType t2) : t1 = t2 := by
  rcases h1 with ⟨w1, h1⟩
  rcases h2 with ⟨w2, h2⟩
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2
  all_goals
    subst h1
    subst h2
  · simp [PP.ppType, PP.ppTypeAux] at h
    exact congrArg LLVMType.int (IntWidth.ppIntWidth_injective _ _ h)
  · cases w1 <;> simp [PP.ppType, PP.ppTypeAux, IntWidth.pp] at h
  · cases w1 <;> simp [PP.ppType, PP.ppTypeAux, IntWidth.pp] at h
  · cases w2 <;> simp [PP.ppType, PP.ppTypeAux, IntWidth.pp] at h
  · rfl
  · simp [PP.ppType, PP.ppTypeAux] at h
  · cases w2 <;> simp [PP.ppType, PP.ppTypeAux, IntWidth.pp] at h
  · simp [PP.ppType, PP.ppTypeAux] at h
  · rfl

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

theorem execBlock_mono (mod_ : LLVMModule) (fn : LLVMFn) (f1 f2 : Nat) (st : ExecState) (blk : LLVMBlock)
    (hle : f1 ≤ f2)
    (hfin : execBlock mod_ fn f1 st blk ≠ .outOfFuel) :
    execBlock mod_ fn f2 st blk = execBlock mod_ fn f1 st blk := by
  induction f1 generalizing f2 st blk with
  | zero => exact False.elim (hfin rfl)
  | succ k ih =>
    cases f2 with
    | zero => omega
    | succ m =>
      simp only [execBlock] at hfin ⊢
      cases hexec : execInstrs mod_ st (blk.phis ++ blk.body) with
      | inl out => simp
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
              cases hfind : findBlock fn (((cases.find? (fun pair => pair.fst == sv.zeroExtend 64)).map (·.snd)).getD defLbl) with
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
