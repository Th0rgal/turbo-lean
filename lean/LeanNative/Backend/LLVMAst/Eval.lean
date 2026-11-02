import LeanNative.Backend.LLVMAst.Syntax

namespace LeanNative.Backend.LLVMAst

open LeanNative.Backend.TargetIR

def lookupReg (st : ExecState) (r : RegName) : Option LLVMVal :=
  st.regs.lookup r

def bindReg (st : ExecState) (r : RegName) (v : LLVMVal) : ExecState :=
  { st with regs := (r, v) :: st.regs }

def evalOperand (st : ExecState) : Operand → LLVMVal
  | .reg r => (lookupReg st r).getD .poison
  | .global sym =>
    match st.globals.lookup sym with
    | some ptr => .ptr ptr
    | none => .poison
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
    | .array _ _ | .vec _ _ | .structFields _ _ => LLVMVal.zeroOf ty
    | _ => .aggNil
  | .aggCons h t =>
    match ty with
    | .structFields packed (.cons hty tty) =>
      .aggCons (evalTypedOperand st hty h) (evalTypedOperand st (.structFields packed tty) t)
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

def packI1Chunk : Nat → List LLVMVal → Option (BitVec 8)
  | 0, _ => some 0#8
  | k + 1, [] =>
    match packI1Chunk k [] with
    | some hi => some (hi <<< 1)
    | none => none
  | k + 1, .bits .i1 b :: rest =>
    match packI1Chunk k rest with
    | some hi => some ((hi <<< 1) ||| (if b == 1#1 then 1#8 else 0#8))
    | none => none
  | _, _ => none

def packI1Lanes : Nat → List LLVMVal → List MemByte
  | 0, _ => []
  | bytes + 1, vs =>
    let b0 :=
      match packI1Chunk 8 (vs.take 8) with
      | some bv => MemByte.init bv
      | none => MemByte.poisonByte
    b0 :: packI1Lanes bytes (vs.drop 8)

def unpackI1Chunk (b : MemByte) : Nat → Nat → List LLVMVal
  | 0, _ => []
  | k + 1, shift =>
    let elem :=
      match b with
      | .init bv => LLVMVal.bits .i1 (if bv.getLsbD shift then 1#1 else 0#1)
      | .poisonByte => .poison
    elem :: unpackI1Chunk b k (shift + 1)

def unpackI1Lanes : Nat → List MemByte → List LLVMVal
  | 0, _ => []
  | n, [] => List.replicate n .poison
  | n, b :: bs =>
    let chunk := Nat.min n 8
    unpackI1Chunk b chunk 0 ++ unpackI1Lanes (n - chunk) bs

def structFieldOffsetList (packed : Bool) : LLVMTypeFields → Nat → List (Nat × LLVMType)
  | .nil, _ => []
  | .cons h t, cur =>
    let off := if packed then cur else ByteMem.alignUp cur h.abiAlign
    (off, h) :: structFieldOffsetList packed t (off + h.byteSize)

def padChunkList : Nat → List (Nat × List MemByte) → List MemByte
  | _, [] => []
  | cur, (off, chunk) :: rest =>
    ByteMem.zeroBytes (off - cur) ++ chunk ++ padChunkList (off + chunk.length) rest

def serializeTypedValAux : Nat → LLVMType → LLVMVal → List MemByte
  | 0, ty, _ => ByteMem.poisonBytes ty.byteSize
  | _ + 1, .void, _ => []
  | _ + 1, .int w, .bits w' bv =>
    if h : w' = w then ByteMem.initBytes (ByteMem.bvToLEBytes w.byteSize (h ▸ bv))
    else ByteMem.poisonBytes w.byteSize
  | _ + 1, .int w, _ => ByteMem.poisonBytes w.byteSize
  | _ + 1, .ptr _, .ptr p => ByteMem.initBytes (ByteMem.bvToLEBytes 8 p)
  | _ + 1, .ptr _, _ => ByteMem.poisonBytes 8
  | _ + 1, .float fw, .floatBits fw' fb =>
    if h : fw' = fw then ByteMem.initBytes (ByteMem.bvToLEBytes fw.byteSize (h ▸ fb))
    else ByteMem.poisonBytes fw.byteSize
  | _ + 1, .float fw, _ => ByteMem.poisonBytes fw.byteSize
  | fuel + 1, .structFields packed fs, v =>
    let total := (LLVMType.structFields packed fs).byteSize
    if isPoison v then ByteMem.poisonBytes total
    else
      match v.toList? with
      | none => ByteMem.poisonBytes total
      | some vs =>
        let specs := structFieldOffsetList packed fs 0
        let chunks := repeatMapIdx specs.length fun i =>
          match specs.getD i (0, .void) with
          | (off, fty) => (off, serializeTypedValAux fuel fty (vs.getD i .poison))
        let raw := padChunkList 0 chunks
        raw ++ ByteMem.zeroBytes (total - Nat.min raw.length total)
  | fuel + 1, .array n et, v =>
    if isPoison v then ByteMem.poisonBytes (LLVMType.array n et).byteSize
    else
      match v.toList? with
      | none => ByteMem.poisonBytes (LLVMType.array n et).byteSize
      | some vs =>
        (repeatMapIdx n fun i => serializeTypedValAux fuel et (vs.getD i .poison)).flatten
  | fuel + 1, .vec n et, v =>
    let storeBytes := (LLVMType.vec n et).byteSize
    if isPoison v then ByteMem.poisonBytes storeBytes
    else
      match v.toList? with
      | none => ByteMem.poisonBytes storeBytes
      | some vs =>
        if et == .int .i1 then
          let rawBytes := (n + 7) / 8
          let packed := packI1Lanes rawBytes (vs.take n)
          packed ++ ByteMem.zeroBytes (storeBytes - Nat.min packed.length storeBytes)
        else
          let rawBytes := (n * et.bitSize + 7) / 8
          let body := ((repeatMapIdx n fun i => serializeTypedValAux fuel et (vs.getD i .poison)).flatten).take rawBytes
          body ++ ByteMem.zeroBytes (storeBytes - Nat.min body.length storeBytes)

def serializeTypedVal (ty : LLVMType) (v : LLVMVal) : List MemByte :=
  serializeTypedValAux (ty.sizeOfType + 1) ty v

def deserializeValAux : Nat → LLVMType → List MemByte → LLVMVal
  | 0, _, _ => .poison
  | _ + 1, .void, _ => .aggNil
  | _ + 1, .int w, bs =>
    match ByteMem.bytesToBv? w.bits (bs.take w.byteSize) with
    | some v => .bits w v
    | none => .poison
  | _ + 1, .ptr _, bs =>
    match ByteMem.bytesToBv? 64 (bs.take 8) with
    | some v => .ptr v
    | none => .poison
  | _ + 1, .float fw, bs =>
    match ByteMem.bytesToBv? fw.bits (bs.take fw.byteSize) with
    | some v => .floatBits fw v
    | none => .poison
  | fuel + 1, .structFields packed fs, bs =>
    let specs := structFieldOffsetList packed fs 0
    LLVMVal.ofList (repeatMapIdx specs.length fun i =>
      match specs.getD i (0, .void) with
      | (off, fty) => deserializeValAux fuel fty ((bs.drop off).take fty.byteSize))
  | fuel + 1, .array n et, bs =>
    let sz := et.byteSize
    LLVMVal.ofList (repeatMapIdx n fun i =>
      deserializeValAux fuel et ((bs.drop (i * sz)).take sz))
  | fuel + 1, .vec n et, bs =>
    if et == .int .i1 then
      LLVMVal.ofList (unpackI1Lanes n bs)
    else
      let sz := et.byteSize
      LLVMVal.ofList (repeatMapIdx n fun i =>
        deserializeValAux fuel et ((bs.drop (i * sz)).take sz))

def deserializeVal (ty : LLVMType) (bs : List MemByte) : LLVMVal :=
  deserializeValAux (ty.sizeOfType + 1) ty bs

def serializeVal (v : LLVMVal) : List MemByte :=
  match v with
  | .bits w bv => ByteMem.initBytes (ByteMem.bvToLEBytes w.byteSize bv)
  | .ptr p => ByteMem.initBytes (ByteMem.bvToLEBytes 8 p)
  | .floatBits fw fb => ByteMem.initBytes (ByteMem.bvToLEBytes fw.byteSize fb)
  | .poison => ByteMem.poisonBytes 1
  | .aggNil => []
  | .aggCons h t => serializeVal h ++ serializeVal t

def storeTypedVal (m : ByteMem) (addr : BitVec 64) (ty : LLVMType) (v : LLVMVal) : ByteMem :=
  m.writeBytesAt addr.toNat (serializeTypedVal ty v)

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
    | .structFields packed fs, (i, w) :: rest =>
      if w == .i32 then
        if 0 ≤ i then
          match LLVMType.structFieldOffset packed fs i.toNat, LLVMType.structFieldTy fs i.toNat with
          | some off, some fty =>
            match walk fty rest with
            | some inner => some (Int.ofNat off + inner)
            | none => none
          | _, _ => none
        else none
      else none
    | _, _ => none

def containsPtr : LLVMType → Bool
  | .ptr _ => true
  | .vec _ et => containsPtr et
  | _ => false

def bitcastVal (srcTy dstTy : LLVMType) (v : LLVMVal) : Option LLVMVal :=
  if srcTy.bitSize != dstTy.bitSize then none
  else if srcTy matches .void || srcTy matches .structFields _ _ || srcTy matches .array _ _ then none
  else if dstTy matches .void || dstTy matches .structFields _ _ || dstTy matches .array _ _ then none
  else if isPoison v then some .poison
  else if containsPtr srcTy || containsPtr dstTy then
    if srcTy == dstTy then some v else none
  else some (deserializeVal dstTy (serializeTypedVal srcTy v))

def bswapBytes (w : IntWidth) (v : BitVec w.bits) : BitVec w.bits :=
  BitVec.ofNat w.bits (bswapAcc w.byteSize v.toNat 0)
where
  bswapAcc : Nat → Nat → Nat → Nat
    | 0, _, acc => acc
    | k + 1, src, acc => bswapAcc k (src / 256) (acc * 256 + src % 256)

def ctlzBits (w : IntWidth) (v : BitVec w.bits) : BitVec w.bits :=
  BitVec.ofNat w.bits (ctlzAcc w v w.bits)
where
  ctlzAcc (w : IntWidth) (v : BitVec w.bits) : Nat → Nat
    | 0 => w.bits
    | k + 1 => if v.getLsbD k then w.bits - 1 - k else ctlzAcc w v k

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
  match b with
  | .poison => .inl (.ub "division by poison")
  | .bits wb vb =>
    if hb : wb = w then
      let vb' : BitVec w.bits := hb ▸ vb
      if vb' == 0#w.bits then .inl (.ub "division by zero")
      else
        match a with
        | .poison =>
          if signed && bvSigned w vb' == -1 then .inl (.ub "signed division overflow")
          else .inr (bindReg st dst .poison)
        | .bits wa va =>
          if ha : wa = w then
            let va' : BitVec w.bits := ha ▸ va
            if signed && sdivOverflow w va' vb' then .inl (.ub "signed division overflow")
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
        | _ => .inl (.ub "non-integer operand")
    else .inl (.ub "operand width mismatch")
  | _ => .inl (.ub "non-integer operand")

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

def effectiveAlign (ty : LLVMType) (align : Nat) : Nat :=
  if align == 0 then ty.abiAlign else align

def accessCheck (m : ByteMem) (addr : BitVec 64) (n align : Nat) (needWrite : Bool) : Option String :=
  if addr == 0#64 then some "null pointer"
  else if !isPow2 align then some "invalid alignment"
  else if !isAligned addr align then some "misaligned access"
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

def stepInstrWith
    (runCall : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal →
      ExecOutcome ⊕ ExecState)
    (st : ExecState) : LLVMInstr → ExecOutcome ⊕ ExecState
  | .alloca dst ty align =>
    let effAlign := effectiveAlign ty align
    if !isPow2 effAlign then .inl (.ub "invalid alignment")
    else
      match st.mem.allocAligned ty.byteSize effAlign with
      | none => .inl (.ub "alloca out of address space")
      | some (ptr, mem') => .inr (bindReg { st with mem := mem' } dst (.ptr ptr))
  | .load dst _volatile ty ptrOp align _as =>
    let effAlign := effectiveAlign ty align
    match evalOperand st ptrOp with
    | .poison => .inl (.ub "load from poison pointer")
    | .ptr addr =>
      match accessCheck st.mem addr ty.byteSize effAlign false with
      | some "null pointer" => .inl (.ub "load from null pointer")
      | some "invalid alignment" => .inl (.ub "invalid alignment")
      | some "misaligned access" => .inl (.ub "misaligned load")
      | some _ => .inl (.ub "load out of bounds")
      | none => .inr (bindReg st dst (loadVal st.mem addr ty))
    | _ => .inl (.ub "load from non-pointer")
  | .store _volatile ty valOp ptrOp align _as =>
    let effAlign := effectiveAlign ty align
    let val := evalTypedOperand st ty valOp
    match evalOperand st ptrOp with
    | .poison => .inl (.ub "store to poison pointer")
    | .ptr addr =>
      match accessCheck st.mem addr ty.byteSize effAlign true with
      | some "null pointer" => .inl (.ub "store to null pointer")
      | some "invalid alignment" => .inl (.ub "invalid alignment")
      | some "misaligned access" => .inl (.ub "misaligned store")
      | some _ => .inl (.ub "store out of bounds")
      | none => .inr { st with mem := storeTypedVal st.mem addr ty val }
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
  | .getelementptr dst inbounds_ ty baseOp idxs _as =>
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
  | .call dst? retTy callee args cc =>
    let argVals := args.map fun pair => evalTypedOperand st pair.fst pair.snd
    runCall st dst? cc retTy callee argVals
  | .atomicrmw dst op ptrOp ty valOp _ord align _as =>
    match ty with
    | .int w =>
      let effAlign := if align == 0 then w.byteSize else align
      match evalOperand st ptrOp with
      | .poison => .inl (.ub "atomicrmw on poison pointer")
      | .ptr addr =>
        match accessCheck st.mem addr w.byteSize effAlign true with
        | some "null pointer" => .inl (.ub "atomicrmw on null pointer")
        | some "invalid alignment" => .inl (.ub "invalid alignment")
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
        if n ≤ i then .inr (bindReg st dst .poison)
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
        if n ≤ i then .inr (bindReg st dst .poison)
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

def execInstrsWith
    (runCall : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal →
      ExecOutcome ⊕ ExecState)
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

def execBlockWith
    (runCall : ExecState → Option RegName → CallingConv → LLVMType → GlobalSym → List LLVMVal →
      ExecOutcome ⊕ ExecState)
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
    (dst? : Option RegName) (callCc : CallingConv) (retTy : LLVMType) (callee : GlobalSym) (argVals : List LLVMVal) :
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
          if fn.cc != callCc then .inl (.ub "calling convention mismatch")
          else
            match fn.blocks with
            | [] => .inl (.ub "callee has no entry block")
            | entry :: _ =>
              match bindArgs { mem := st.mem, globals := st.globals } fn.params argVals with
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

def initGlobalsAux : List LLVMGlobal → ByteMem → List (GlobalSym × BitVec 64) → Option (ByteMem × List (GlobalSym × BitVec 64))
  | [], m, acc => some (m, acc.reverse)
  | g :: gs, m, acc =>
    if g.linkage == .external && g.init.isNone then
      initGlobalsAux gs m acc
    else
      let gAlign := Nat.max g.ty.abiAlign (if isPow2 g.align then g.align else 1)
      match m.allocAligned g.ty.byteSize gAlign (!g.isConstant) with
      | none => none
      | some (ptr, m') =>
        let initVal := match g.init with
          | some op => evalTypedOperand { globals := acc.reverse, mem := m' } g.ty op
          | none => LLVMVal.zeroOf g.ty
        let m'' := storeTypedVal m' ptr g.ty initVal
        initGlobalsAux gs m'' ((g.name, ptr) :: acc)

def initGlobals (mod_ : LLVMModule) : Option (ByteMem × List (GlobalSym × BitVec 64)) :=
  initGlobalsAux mod_.globals {} []

def execFn (mod_ : LLVMModule) (fn : LLVMFn) (args : List LLVMVal) (fuel : Nat) : ExecOutcome :=
  match initGlobals mod_ with
  | none => .ub "global allocation failed"
  | some (mem0, globals) =>
    match fn.blocks with
    | [] => .ub "function has no entry block"
    | entry :: _ =>
      match bindArgs { mem := mem0, globals := globals } fn.params args with
      | none => .ub "argument arity mismatch"
      | some st => execBlock mod_ fn fuel st entry

inductive ExecFnRel (mod_ : LLVMModule) (fn : LLVMFn) (args : List LLVMVal) : Nat → ExecOutcome → Prop where
  | noGlobals (fuel : Nat) (h : initGlobals mod_ = none) :
      ExecFnRel mod_ fn args fuel (.ub "global allocation failed")
  | noEntry (fuel : Nat) (mem0 : ByteMem) (globals : List (GlobalSym × BitVec 64))
      (hg : initGlobals mod_ = some (mem0, globals)) (h : fn.blocks = []) :
      ExecFnRel mod_ fn args fuel (.ub "function has no entry block")
  | badArity (fuel : Nat) (mem0 : ByteMem) (globals : List (GlobalSym × BitVec 64))
      (entry : LLVMBlock) (rest : List LLVMBlock)
      (hg : initGlobals mod_ = some (mem0, globals))
      (h : fn.blocks = entry :: rest)
      (hbind : bindArgs { mem := mem0, globals := globals } fn.params args = none) :
      ExecFnRel mod_ fn args fuel (.ub "argument arity mismatch")
  | ran (fuel : Nat) (mem0 : ByteMem) (globals : List (GlobalSym × BitVec 64))
      (entry : LLVMBlock) (rest : List LLVMBlock) (st : ExecState) (out : ExecOutcome)
      (hg : initGlobals mod_ = some (mem0, globals))
      (h : fn.blocks = entry :: rest)
      (hbind : bindArgs { mem := mem0, globals := globals } fn.params args = some st)
      (hrun : execBlock mod_ fn fuel st entry = out) :
      ExecFnRel mod_ fn args fuel out

end LeanNative.Backend.LLVMAst
