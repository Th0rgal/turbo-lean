import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value

namespace LCNF

open LeanNative.IR
open LeanNative.Semantics

/-!
# BitVec-Backed 64/256-Bit Primitive Arithmetic & Bitwise Helpers (`LeanNative.IR.LCNF`)

Provides independent `BitVec` limb packing and primitive binary/unary operator helpers
(`Limbs4x64`, `primBinOp`, `primUnaryOp`). Real `Lean.Compiler.LCNF` lowering and its
end-to-end soundness theorems live in `LeanNative.IR.RealLCNFBridge` and
`LeanNative.Proofs.RealLCNFBridgeProofs`.
-/

/-- Four 64-bit `BitVec` limbs for LCNF 256-bit primitive bitwise operations. -/
structure Limbs4x64 where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  deriving Repr, DecidableEq, Inhabited

def packLimbs (w : UInt256) : Limbs4x64 :=
  ⟨w.lo0.toBitVec, w.lo1.toBitVec, w.hi0.toBitVec, w.hi1.toBitVec⟩

def unpackLimbs (v : Limbs4x64) : UInt256 :=
  ⟨UInt64.ofBitVec v.w0, UInt64.ofBitVec v.w1, UInt64.ofBitVec v.w2, UInt64.ofBitVec v.w3⟩

def toBv256 (w : UInt256) : BitVec 256 :=
  BitVec.ofNat 256 w.toNat

def ofBv256 (b : BitVec 256) : UInt256 :=
  UInt256.ofNat b.toNat

def promoteBv256 : Val → Option (BitVec 256)
  | .u256 w => some (toBv256 w)
  | .u64 n => some (BitVec.ofNat 256 n.toBitVec.toNat)
  | _ => none

def primSar64 (a b : BitVec 64) : BitVec 64 :=
  let sh := b &&& 63#64
  let shifted := a >>> (sh % 64#64)
  let signBit := (a >>> 63#64) &&& 1#64
  if signBit != 0#64 && sh != 0#64 then
    shifted ||| ((BitVec.allOnes 64) <<< ((64#64 - sh) % 64#64))
  else
    shifted

def primSar256 (a : BitVec 256) (sh : Nat) : BitVec 256 :=
  let isNeg := decide (2 ^ 255 ≤ a.toNat)
  if sh ≥ 256 then
    if isNeg then BitVec.allOnes 256 else 0#256
  else if sh == 0 then
    a
  else
    let shifted := a >>> sh
    if !isNeg then shifted
    else shifted + ((BitVec.allOnes 256) <<< (256 - sh))

/-- Independent `BitVec`-backed LCNF primitive binary operator evaluation. Operates strictly
    on typed scalar words (`.u64` / `.u256` / `.bool`), rejecting ill-typed non-scalar operands
    with `.error (.typeError ...)` and zero divisors with `.error .divisionByZero` rather than
    untyped identity/zero/one shortcuts. -/
def primBinOp (op : BinOp) (v1 v2 : Val) : Except UBError Val :=
  match op with
  | .add =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.u64 (UInt64.ofBitVec (a.toBitVec + b.toBitVec)))
    | .u256 a, .u256 b => .ok (.u256 (ofBv256 (toBv256 a + toBv256 b)))
    | _, _ => .error (.typeError "evalBinOp: invalid operand types")
  | .sub =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.u64 (UInt64.ofBitVec (a.toBitVec - b.toBitVec)))
    | .u256 a, .u256 b => .ok (.u256 (ofBv256 (toBv256 a - toBv256 b)))
    | _, _ => .error (.typeError "evalBinOp: invalid operand types")
  | .mul =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.u64 (UInt64.ofBitVec (a.toBitVec * b.toBitVec)))
    | .u256 a, .u256 b => .ok (.u256 (ofBv256 (toBv256 a * toBv256 b)))
    | _, _ => .error (.typeError "evalBinOp: invalid operand types")
  | .div =>
    match v1, v2 with
    | .u64 a, .u64 b =>
      if b.toBitVec == 0#64 then .error .divisionByZero
      else .ok (.u64 (UInt64.ofBitVec (a.toBitVec / b.toBitVec)))
    | .u256 a, .u256 b =>
      if toBv256 b == 0#256 then .error .divisionByZero
      else .ok (.u256 (ofBv256 (toBv256 a / toBv256 b)))
    | _, _ => .error (.typeError "evalBinOp: invalid operand types")
  | .mod =>
    match v1, v2 with
    | .u64 a, .u64 b =>
      if b.toBitVec == 0#64 then .error .divisionByZero
      else .ok (.u64 (UInt64.ofBitVec (a.toBitVec % b.toBitVec)))
    | .u256 a, .u256 b =>
      if toBv256 b == 0#256 then .error .divisionByZero
      else .ok (.u256 (ofBv256 (toBv256 a % toBv256 b)))
    | _, _ => .error (.typeError "evalBinOp: invalid operand types")
  | .bitAnd =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.u64 (UInt64.ofBitVec (a.toBitVec &&& b.toBitVec)))
    | .u256 a, .u256 b =>
      let la := packLimbs a
      let lb := packLimbs b
      .ok (.u256 (unpackLimbs ⟨la.w0 &&& lb.w0, la.w1 &&& lb.w1, la.w2 &&& lb.w2, la.w3 &&& lb.w3⟩))
    | _, _ => .error (.typeError "bitAnd requires u64 or u256")
  | .bitOr =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.u64 (UInt64.ofBitVec (a.toBitVec ||| b.toBitVec)))
    | .u256 a, .u256 b =>
      let la := packLimbs a
      let lb := packLimbs b
      .ok (.u256 (unpackLimbs ⟨la.w0 ||| lb.w0, la.w1 ||| lb.w1, la.w2 ||| lb.w2, la.w3 ||| lb.w3⟩))
    | _, _ => .error (.typeError "bitOr requires u64 or u256")
  | .bitXor =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.u64 (UInt64.ofBitVec (a.toBitVec ^^^ b.toBitVec)))
    | .u256 a, .u256 b =>
      let la := packLimbs a
      let lb := packLimbs b
      .ok (.u256 (unpackLimbs ⟨la.w0 ^^^ lb.w0, la.w1 ^^^ lb.w1, la.w2 ^^^ lb.w2, la.w3 ^^^ lb.w3⟩))
    | _, _ => .error (.typeError "evalBinOp: invalid operand types")
  | .shl =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.u64 (UInt64.ofBitVec (a.toBitVec <<< (b.toBitVec % 64#64))))
    | .u256 a, .u256 b => .ok (.u256 (ofBv256 (toBv256 a <<< (toBv256 b).toNat)))
    | _, _ => .error (.typeError "evalBinOp: invalid operand types")
  | .shr =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.u64 (UInt64.ofBitVec (a.toBitVec >>> (b.toBitVec % 64#64))))
    | .u256 a, .u256 b => .ok (.u256 (ofBv256 (toBv256 a >>> (toBv256 b).toNat)))
    | _, _ => .error (.typeError "evalBinOp: invalid operand types")
  | .sar =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.u64 (UInt64.ofBitVec (primSar64 a.toBitVec b.toBitVec)))
    | .u256 a, .u256 b => .ok (.u256 (ofBv256 (primSar256 (toBv256 a) (toBv256 b).toNat)))
    | _, _ => .error (.typeError "evalBinOp: invalid operand types")
  | .eq =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.bool (a.toBitVec == b.toBitVec))
    | .u256 a, .u256 b => .ok (.bool (toBv256 a == toBv256 b))
    | .bool a, .bool b => .ok (.bool (a == b))
    | _, _ => .error (.typeError "evalBinOp: invalid operand types")
  | .lt =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.bool (decide (a.toBitVec < b.toBitVec)))
    | .u256 a, .u256 b => .ok (.bool (decide (toBv256 a < toBv256 b)))
    | _, _ => .error (.typeError "evalBinOp: invalid operand types")
  | .le =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.bool (decide (a.toBitVec ≤ b.toBitVec)))
    | .u256 a, .u256 b => .ok (.bool (decide (toBv256 a ≤ toBv256 b)))
    | _, _ => .error (.typeError "evalBinOp: invalid operand types")
  | .addChecked256 =>
    match promoteBv256 v1, promoteBv256 v2 with
    | some a, some b =>
      if BitVec.uaddOverflow a b then .error (.arithmeticOverflow "addChecked256 overflow")
      else .ok (.u256 (ofBv256 (a + b)))
    | _, _ => .error (.typeError "addChecked256 requires u256/u64 operands")
  | .subChecked256 =>
    match promoteBv256 v1, promoteBv256 v2 with
    | some a, some b =>
      if decide (a < b) then .error (.arithmeticOverflow "subChecked256 underflow")
      else .ok (.u256 (ofBv256 (a - b)))
    | _, _ => .error (.typeError "subChecked256 requires u256/u64 operands")
  | .mulChecked256 =>
    match promoteBv256 v1, promoteBv256 v2 with
    | some a, some b =>
      if BitVec.umulOverflow a b then .error (.arithmeticOverflow "mulChecked256 overflow")
      else .ok (.u256 (ofBv256 (a * b)))
    | _, _ => .error (.typeError "mulChecked256 requires u256/u64 operands")
  | .clmul64 =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.u64 (clmul64 a b))
    | _, _ => .error (.typeError "evalBinOp: clmul64/clmul64Hi/gf2Affine/eor3 require u64")
  | .clmul64Hi =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.u64 (clmul64Hi a b))
    | _, _ => .error (.typeError "evalBinOp: clmul64/clmul64Hi/gf2Affine/eor3 require u64")
  | .gf2Affine =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.u64 (gf2Affine a b))
    | _, _ => .error (.typeError "evalBinOp: clmul64/clmul64Hi/gf2Affine/eor3 require u64")
  | .eor3 =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.u64 (eor3 a b))
    | _, _ => .error (.typeError "evalBinOp: clmul64/clmul64Hi/gf2Affine/eor3 require u64")

/-- Independent `BitVec`-backed LCNF primitive unary operator evaluation. -/
def primUnaryOp (op : UnaryOp) (v : Val) : Except UBError Val :=
  match op, v with
  | .not, .u64 n => .ok (.u64 (UInt64.ofBitVec (~~~n.toBitVec)))
  | .not, .u256 w =>
    let lw := packLimbs w
    .ok (.u256 (unpackLimbs ⟨~~~lw.w0, ~~~lw.w1, ~~~lw.w2, ~~~lw.w3⟩))
  | .not, .bool b => .ok (.bool (!b))
  | .neg, .u64 n => .ok (.u64 (UInt64.ofBitVec (0#64 - n.toBitVec)))
  | .neg, .u256 w => .ok (.u256 (ofBv256 (0#256 - toBv256 w)))
  | .clz256, .u256 w => .ok (.u256 (UInt256.clz (ofBv256 (toBv256 w))))
  | .clz256, .u64 n => .ok (.u256 (UInt256.clz (ofBv256 (BitVec.ofNat 256 n.toBitVec.toNat))))
  | _, _ => .error (.typeError "evalUnaryOp: invalid operand type")

end LCNF
