import LeanNative.Semantics.Eval

/-! Shadow-semantics fixture: verbatim source copy of `LeanNative.Semantics.evalBinOp`
(with its `match`) under a new name, in a file that IMPORTS `LeanNative.Semantics.Eval`.
Expected: `check_shadow_semantics` reports `ShadowFixtureClone.evalBinOp → evalBinOp (clone)`
even though no forbidden constant is referenced. -/

namespace ShadowFixtureClone
open LeanNative.IR LeanNative.Semantics

def evalBinOp (op : BinOp) (v1 v2 : Val) : Except UBError Val :=
  match op with
  | .add =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.u64 (a + b))
    | v, .u64 0 => .ok v
    | .u64 0, v => .ok v
    | .u256 a, .u256 b => .ok (.u256 (UInt256.add a b))
    | _, _ => .error (.typeError "evalBinOp: invalid operand types")
  | .sub =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.u64 (a - b))
    | v, .u64 0 => .ok v
    | .u256 a, .u256 b => .ok (.u256 (UInt256.sub a b))
    | _, _ => .error (.typeError "evalBinOp: invalid operand types")
  | .mul =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.u64 (a * b))
    | v, .u64 1 => .ok v
    | .u64 1, v => .ok v
    | .u256 a, .u256 b => .ok (.u256 (UInt256.mul a b))
    | _, _ => .error (.typeError "evalBinOp: invalid operand types")
  | .div =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.u64 (a / b))
    | v, .u64 1 => .ok v
    | .u256 a, .u256 b =>
      match UInt256.div a b with
      | some q => .ok (.u256 q)
      | none => .error .divisionByZero
    | _, _ => .error (.typeError "evalBinOp: invalid operand types")
  | .mod =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.u64 (a % b))
    | .u256 a, .u256 b =>
      match UInt256.mod a b with
      | some r => .ok (.u256 r)
      | none => .error .divisionByZero
    | _, _ => .error (.typeError "evalBinOp: invalid operand types")
  | .bitAnd =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.u64 (a &&& b))
    | .u256 a, .u256 b => .ok (.u256 (UInt256.bitAnd a b))
    | v1, v2 =>
      if v1 == v2 then .ok v1 else .error (.typeError "bitAnd requires u64 or u256")
  | .bitOr =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.u64 (a ||| b))
    | v, .u64 0 => .ok v
    | .u64 0, v => .ok v
    | .u256 a, .u256 b => .ok (.u256 (UInt256.bitOr a b))
    | v1, v2 =>
      if v1 == v2 then .ok v1 else .error (.typeError "bitOr requires u64 or u256")
  | .bitXor =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.u64 (a ^^^ b))
    | v, .u64 0 => .ok v
    | .u64 0, v => .ok v
    | .u256 a, .u256 b => .ok (.u256 (UInt256.bitXor a b))
    | _, _ => .error (.typeError "evalBinOp: invalid operand types")
  | .shl =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.u64 (a <<< b))
    | v, .u64 0 => .ok v
    | .u256 a, .u256 b => .ok (.u256 (UInt256.shl a b.toNat))
    | _, _ => .error (.typeError "evalBinOp: invalid operand types")
  | .shr =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.u64 (a >>> b))
    | v, .u64 0 => .ok v
    | .u256 a, .u256 b => .ok (.u256 (UInt256.shr a b.toNat))
    | _, _ => .error (.typeError "evalBinOp: invalid operand types")
  | .sar =>
    match v1, v2 with
    | .u64 a, .u64 b =>
      let sh := b &&& 63
      let shifted := a >>> sh
      let signBit := (a >>> 63) &&& 1
      let res :=
        if signBit != 0 && sh != 0 then
          shifted ||| (0xffffffffffffffff <<< (64 - sh))
        else
          shifted
      .ok (.u64 res)
    | .u256 a, .u256 b => .ok (.u256 (UInt256.sar a b.toNat))
    | _, _ => .error (.typeError "evalBinOp: invalid operand types")
  | .eq =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.bool (a == b))
    | .u256 a, .u256 b => .ok (.bool (a == b))
    | .bool a, .bool b => .ok (.bool (a == b))
    | _, _ => .error (.typeError "evalBinOp: invalid operand types")
  | .lt =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.bool (decide (a < b)))
    | .u256 a, .u256 b => .ok (.bool (UInt256.lt a b))
    | _, _ => .error (.typeError "evalBinOp: invalid operand types")
  | .le =>
    match v1, v2 with
    | .u64 a, .u64 b => .ok (.bool (decide (a ≤ b)))
    | .u256 a, .u256 b => .ok (.bool (UInt256.le a b))
    | _, _ => .error (.typeError "evalBinOp: invalid operand types")
  | .addChecked256 =>
    match v1.toU256?, v2.toU256? with
    | some a, some b =>
      match UInt256.addChecked a b with
      | some res => .ok (.u256 res)
      | none => .error (.arithmeticOverflow "addChecked256 overflow")
    | _, _ => .error (.typeError "addChecked256 requires u256/u64 operands")
  | .subChecked256 =>
    match v1.toU256?, v2.toU256? with
    | some a, some b =>
      match UInt256.subChecked a b with
      | some res => .ok (.u256 res)
      | none => .error (.arithmeticOverflow "subChecked256 underflow")
    | _, _ => .error (.typeError "subChecked256 requires u256/u64 operands")
  | .mulChecked256 =>
    match v1.toU256?, v2.toU256? with
    | some a, some b =>
      match UInt256.mulChecked a b with
      | some res => .ok (.u256 res)
      | none => .error (.arithmeticOverflow "mulChecked256 overflow")
    | _, _ => .error (.typeError "mulChecked256 requires u256/u64 operands")
  | .clmul64 | .clmul64Hi | .gf2Affine | .eor3 =>
    match v1, v2 with
    | .u64 a, .u64 b =>
      .ok (.u64 (match op with | .clmul64 => clmul64 a b | .clmul64Hi => clmul64Hi a b | .gf2Affine => gf2Affine a b | _ => eor3 a b))
    | _, _ => .error (.typeError "evalBinOp: clmul64/clmul64Hi/gf2Affine/eor3 require u64")

end ShadowFixtureClone
