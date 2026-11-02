import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value

namespace LCNF

open LeanNative.IR
open LeanNative.Semantics

/-!
# Formalized Lean 4 LCNF (`Lean.Compiler.LCNF`) Operational Subset (`LeanNative.IR.LCNF`)

Provides the formal syntax (`LCNF.LetValue`, `LCNF.Code`, `LCNF.Env`), independent operational
semantics (`LCNF.evalLetValue`, `LCNF.evalLCNF`), and partial lowering pass (`LCNF.lowerLetValue`,
`LCNF.lowerCode`) to `LNIRCode` for Milestone M4 (`lowerLCNFCode_sound`).
-/

/-- Formalized LCNF right-hand-side let-binding expressions (`LCNF.LetValue`). -/
inductive LetValue where
  | litU64          : UInt64 → LetValue
  | litBool         : Bool → LetValue
  | litU256         : UInt256 → LetValue
  | fvar            : VarId → LetValue
  | binOp           : BinOp → VarId → VarId → LetValue
  | unaryOp         : UnaryOp → VarId → LetValue
  | mkPair          : VarId → VarId → LetValue
  | projTuple       : VarId → Nat → LetValue
  | sarrayLen       : VarId → LetValue
  | sarrayGet       : VarId → VarId → LNIRType → LetValue
  | sarraySet       : VarId → VarId → VarId → LNIRType → LetValue
  | unsupportedCall : String → LetValue
  deriving Repr, Inhabited, BEq

/-- Formalized LCNF ANF code blocks (`LCNF.Code`).
    Note that `.casesBool discr falseBranch trueBranch` follows Lean LCNF `Bool` constructor
    ordering (`Bool.false` = ctor 0 first, `Bool.true` = ctor 1 second), whereas `LNIRCode.ite`
    orders `thenBranch` (`true`) before `elseBranch` (`false`). -/
inductive Code where
  | letBind   : VarId → LNIRType → LetValue → Code → Code
  | inc       : VarId → Nat → Code → Code
  | dec       : VarId → Nat → Code → Code
  | casesBool : VarId → Code → Code → Code
  | return    : VarId → Code
  | unreach   : Code
  deriving Repr, Inhabited, BEq

/-- LCNF variable environment mapping free variable IDs (`VarId`) to runtime values. -/
abbrev Env := VarId → Option Val

namespace Env

def bind (env : Env) (x : VarId) (v : Val) : Env :=
  fun y => if y == x then some v else env y

end Env

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

/-- Independent operational evaluation of `LCNF.LetValue` over `LCNF.Env` and `HeapState`. -/
def evalLetValue (env : Env) (st : HeapState) : LetValue → Except UBError (Val × HeapState)
  | .litU64 n => .ok (.u64 n, st)
  | .litBool b => .ok (.bool b, st)
  | .litU256 w => .ok (.u256 w, st)
  | .fvar x =>
    match env x with
    | some v => .ok (v, st)
    | none => .error (.unboundVar x)
  | .binOp op aVar bVar =>
    match env aVar, env bVar with
    | some va, some vb =>
      match primBinOp op va vb with
      | .ok v => .ok (v, st)
      | .error err => .error err
    | none, _ => .error (.unboundVar aVar)
    | some _, none => .error (.unboundVar bVar)
  | .unaryOp op aVar =>
    match env aVar with
    | some va =>
      match primUnaryOp op va with
      | .ok v => .ok (v, st)
      | .error err => .error err
    | none => .error (.unboundVar aVar)
  | .mkPair aVar bVar =>
    match env aVar, env bVar with
    | some va, some vb => .ok (.tuple [va, vb], st)
    | none, _ => .error (.unboundVar aVar)
    | some _, none => .error (.unboundVar bVar)
  | .projTuple tupleVar idx =>
    match env tupleVar with
    | some (.tuple vals) =>
      match vals[idx]? with
      | some v => .ok (v, st)
      | none => .error (.outOfBounds idx vals.length)
    | some _ => .error (.typeError "projTuple expects tuple value")
    | none => .error (.unboundVar tupleVar)
  | .sarrayLen arrVar =>
    match env arrVar with
    | some (.sarrayId bufId) =>
      match st.findBuffer bufId with
      | some buf => .ok (.u64 buf.data.size.toUInt64, st)
      | none => .error (.typeError s!"unknown sarray buffer {bufId}")
    | some _ => .error (.typeError "sarrayLen expects sarrayId")
    | none => .error (.unboundVar arrVar)
  | .sarrayGet arrVar idxVar _elemTy =>
    match env arrVar, env idxVar with
    | some (.sarrayId bufId), some (.u64 idx) =>
      match st.readElem bufId idx.toNat with
      | .ok v => .ok (.u64 v, st)
      | .error err => .error err
    | none, _ => .error (.unboundVar arrVar)
    | _, none => .error (.unboundVar idxVar)
    | _, _ => .error (.typeError "sarrayGet expects sarrayId and u64 index")
  | .sarraySet arrVar idxVar valVar _elemTy =>
    match env arrVar, env idxVar, env valVar with
    | some (.sarrayId bufId), some (.u64 idx), some (.u64 val) =>
      match st.ensureExclusive bufId with
      | .ok st1 =>
        match st1.writeElemExclusive bufId idx.toNat val with
        | .ok st2 => .ok (.sarrayId bufId, st2)
        | .error err => .error err
      | .error err => .error err
    | none, _, _ => .error (.unboundVar arrVar)
    | _, none, _ => .error (.unboundVar idxVar)
    | _, _, none => .error (.unboundVar valVar)
    | _, _, _ => .error (.typeError "sarraySet expects sarrayId, u64 index, and u64 value")
  | .unsupportedCall fnName =>
    .error (.unsupportedCall fnName)

/-- Independent operational evaluator for `LCNF.Code` (`evalLCNF`), defined directly on `LCNF.Code`
    without referencing `lowerCode` or `evalCode`. -/
def evalLCNF (env : Env) (st : HeapState) (code : Code) (fuel : Nat) : Except UBError (Val × HeapState) :=
  match code with
  | .letBind dst _ty val k =>
    match evalLetValue env st val with
    | .ok (v, st') => evalLCNF (Env.bind env dst v) st' k fuel
    | .error err => .error err
  | .inc objVar count k =>
    match st.evalIncRef env objVar count with
    | .ok st' => evalLCNF env st' k fuel
    | .error err => .error err
  | .dec objVar count k =>
    match st.evalDecRef env objVar count with
    | .ok st' => evalLCNF env st' k fuel
    | .error err => .error err
  | .casesBool discr falseBranch trueBranch =>
    match env discr with
    | some (.bool true) => evalLCNF env st trueBranch fuel
    | some (.bool false) => evalLCNF env st falseBranch fuel
    | some (.u64 n) =>
      if n != 0 then evalLCNF env st trueBranch fuel
      else evalLCNF env st falseBranch fuel
    | some (.u256 w) =>
      if w != UInt256.zero then evalLCNF env st trueBranch fuel
      else evalLCNF env st falseBranch fuel
    | some _ => .error (.typeError "ite condition must be bool, u64, or u64")
    | none => .error (.unboundVar discr)
  | .return v =>
    match env v with
    | some val => .ok (val, st)
    | none => .error (.unboundVar v)
  | .unreach =>
    .error (.typeError "reached unreachable code")

/-- Lower an `LCNF.LetValue` into an `LNIRExpr`, rejecting `.unsupportedCall` with a descriptive error. -/
def lowerLetValue : LetValue → Except String LNIRExpr
  | .litU64 n => .ok (.scalar (.constU64 n))
  | .litBool b => .ok (.scalar (.constBool b))
  | .litU256 w => .ok (.constU256 w)
  | .fvar x => .ok (.scalar (.var x))
  | .binOp op aVar bVar => .ok (.scalar (.binOp op (.var aVar) (.var bVar)))
  | .unaryOp op aVar => .ok (.scalar (.unaryOp op (.var aVar)))
  | .mkPair aVar bVar => .ok (.mkTuple [aVar, bVar])
  | .projTuple tupleVar idx => .ok (.projTuple tupleVar idx)
  | .sarrayLen arrVar => .ok (.sarrayLen arrVar)
  | .sarrayGet arrVar idxVar elemTy => .ok (.sarrayGet arrVar idxVar elemTy)
  | .sarraySet arrVar idxVar valVar elemTy => .ok (.sarraySet arrVar idxVar valVar elemTy)
  | .unsupportedCall fnName => .error s!"unsupported LCNF call: {fnName}"

/-- Lower an `LCNF.Code` block into `LNIRCode`, translating `.casesBool discr falseBranch trueBranch`
    into `.ite discr trueBranch' falseBranch'` and rejecting unsupported calls. -/
def lowerCode : Code → Except String LNIRCode
  | .letBind dst ty val k =>
    match lowerLetValue val, lowerCode k with
    | .ok expr, .ok k' => .ok (.letBind dst ty expr k')
    | .error err, _ => .error err
    | .ok _, .error err => .error err
  | .inc objVar count k =>
    match lowerCode k with
    | .ok k' => .ok (.incRef objVar count k')
    | .error err => .error err
  | .dec objVar count k =>
    match lowerCode k with
    | .ok k' => .ok (.decRef objVar count k')
    | .error err => .error err
  | .casesBool discr falseBranch trueBranch =>
    match lowerCode falseBranch, lowerCode trueBranch with
    | .ok fb', .ok tb' => .ok (.ite discr tb' fb')
    | .error err, _ => .error err
    | .ok _, .error err => .error err
  | .return v => .ok (.ret v)
  | .unreach => .ok .unreachable

end LCNF
