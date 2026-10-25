import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value

namespace LeanNative.Semantics

open LeanNative.IR

/-- Helper to extract a 256-bit `UInt256` from a `Val` (promoting `.u64` if needed). -/
def Val.toU256? : Val → Option UInt256
  | .u256 w => some w
  | .u64 x  => some (UInt256.ofUInt64 x)
  | _       => none

/-- Total, deterministic evaluation of binary scalar operators on `Val` (64-bit and 256-bit EVM). -/
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
    | .u64 a, .u64 b =>
      if b == 0 then .error .divisionByZero else .ok (.u64 (a / b))
    | v, .u64 1 => .ok v
    | .u256 a, .u256 b =>
      match UInt256.div a b with
      | some q => .ok (.u256 q)
      | none => .error .divisionByZero
    | _, _ => .error (.typeError "evalBinOp: invalid operand types")
  | .mod =>
    match v1, v2 with
    | .u64 a, .u64 b =>
      if b == 0 then .error .divisionByZero else .ok (.u64 (a % b))
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

/-- Total, deterministic evaluation of unary scalar operators on `Val`. -/
def evalUnaryOp (op : UnaryOp) (v : Val) : Except UBError Val :=
  match op, v with
  | .not, .bool b   => .ok (.bool (!b))
  | .not, .u64 n    => .ok (.u64 (~~~n))
  | .not, .u256 w   => .ok (.u256 (UInt256.bitNot w))
  | .neg, .u64 n    => .ok (.u64 (0 - n))
  | .neg, .u256 w   => .ok (.u256 (UInt256.sub UInt256.zero w))
  | .clz256, .u256 w => .ok (.u256 (UInt256.clz w))
  | .clz256, .u64 n  => .ok (.u256 (UInt256.clz (UInt256.ofUInt64 n)))
  | _, _ => .error (.typeError "evalUnaryOp: invalid operand type")

/-- Total denotational evaluator for pure scalar SSA expressions (`ScalarExpr`). -/
def evalScalarExpr (env : VarEnv) : ScalarExpr → Except UBError Val
  | .constU64 val => .ok (.u64 val)
  | .constBool val => .ok (.bool val)
  | .var id =>
    match env id with
    | some v => .ok v
    | none => .error (.unboundVar id)
  | .binOp op lhs rhs =>
    match evalScalarExpr env lhs, evalScalarExpr env rhs with
    | .ok v1, .ok v2 => evalBinOp op v1 v2
    | .error err, _ => .error err
    | .ok _, .error err => .error err
  | .unaryOp op arg =>
    match evalScalarExpr env arg with
    | .ok v => evalUnaryOp op v
    | .error err => .error err
  | .select cond thenVal elseVal =>
    match evalScalarExpr env cond with
    | .ok (.bool true) => evalScalarExpr env thenVal
    | .ok (.bool false) => evalScalarExpr env elseVal
    | .ok (.u64 n) =>
      if n != 0 then evalScalarExpr env thenVal else evalScalarExpr env elseVal
    | .ok (.u256 w) =>
      if w != UInt256.zero then evalScalarExpr env thenVal else evalScalarExpr env elseVal
    | .ok _ => .error (.typeError "select condition must be bool, u64, or u256")
    | .error err => .error err
  | .fma a b c =>
    match evalScalarExpr env a, evalScalarExpr env b with
    | .ok va, .ok vb =>
      match evalBinOp .mul va vb, evalScalarExpr env c with
      | .ok vab, .ok vc => evalBinOp .add vab vc
      | .error err, _ => .error err
      | .ok _, .error err => .error err
    | .error err, _ => .error err
    | .ok _, .error err => .error err

/-- Look up a list of SSA variables in `VarEnv`. -/
def evalVarList (env : VarEnv) : List VarId → Except UBError (List Val)
  | [] => .ok []
  | x :: xs =>
    match env x, evalVarList env xs with
    | some v, .ok vs => .ok (v :: vs)
    | none, _ => .error (.unboundVar x)
    | some _, .error err => .error err

/-- Total evaluator for right-hand side LNIR expressions (`LNIRExpr`). -/
def evalExpr (env : VarEnv) (st : HeapState) (e : LNIRExpr) : Except UBError (Val × HeapState) :=
  match e with
  | .scalar se =>
    match evalScalarExpr env se with
    | .ok v => .ok (v, st)
    | .error err => .error err
  | .constU256 val =>
    .ok (.u256 val, st)
  | .mulDivDown aVar bVar denomVar =>
    match env aVar, env bVar, env denomVar with
    | some va, some vb, some vd =>
      match va.toU256?, vb.toU256?, vd.toU256? with
      | some a, some b, some d =>
        if d == UInt256.zero then .error .divisionByZero
        else
          match UInt256.mulDivDown a b d with
          | some q => .ok (.u256 q, st)
          | none => .error (.arithmeticOverflow "mulDivDown overflow")
      | _, _, _ => .error (.typeError "mulDivDown expects u256/u64 operands")
    | none, _, _ => .error (.unboundVar aVar)
    | _, none, _ => .error (.unboundVar bVar)
    | _, _, none => .error (.unboundVar denomVar)
  | .mulDivUp aVar bVar denomVar =>
    match env aVar, env bVar, env denomVar with
    | some va, some vb, some vd =>
      match va.toU256?, vb.toU256?, vd.toU256? with
      | some a, some b, some d =>
        if d == UInt256.zero then .error .divisionByZero
        else
          match UInt256.mulDivUp a b d with
          | some q => .ok (.u256 q, st)
          | none => .error (.arithmeticOverflow "mulDivUp overflow")
      | _, _, _ => .error (.typeError "mulDivUp expects u256/u64 operands")
    | none, _, _ => .error (.unboundVar aVar)
    | _, none, _ => .error (.unboundVar bVar)
    | _, _, none => .error (.unboundVar denomVar)
  | .storageLoad mapVar slotVar =>
    match env mapVar, env slotVar with
    | some (.storageMapId mapId), some vSlot =>
      match vSlot.toU256? with
      | some slot => .ok (.u256 (st.storageLoad mapId slot), st)
      | none => .error (.typeError "storageLoad slot must be u256 or u64")
    | none, _ => .error (.unboundVar mapVar)
    | _, none => .error (.unboundVar slotVar)
    | _, _ => .error (.typeError "storageLoad expects storageMapId")
  | .storageStore mapVar slotVar valVar =>
    match env mapVar, env slotVar, env valVar with
    | some (.storageMapId mapId), some vSlot, some vVal =>
      match vSlot.toU256?, vVal.toU256? with
      | some slot, some val =>
        let st' := st.storageStore mapId slot val
        .ok (.storageMapId mapId, st')
      | _, _ => .error (.typeError "storageStore slot and value must be u256 or u64")
    | none, _, _ => .error (.unboundVar mapVar)
    | _, none, _ => .error (.unboundVar slotVar)
    | _, _, none => .error (.unboundVar valVar)
    | _, _, _ => .error (.typeError "storageStore expects storageMapId")
  | .mkTuple fields =>
    match evalVarList env fields with
    | .ok vals => .ok (.tuple vals, st)
    | .error err => .error err
  | .projTuple tupleVar idx =>
    match env tupleVar with
    | some (.tuple vals) =>
      match vals[idx]? with
      | some v => .ok (v, st)
      | none => .error (.outOfBounds idx vals.length)
    | some _ => .error (.typeError "projTuple expects tuple value")
    | none => .error (.unboundVar tupleVar)
  | .allocCtor tag objFields scalarFields =>
    match evalVarList env (objFields ++ scalarFields) with
    | .ok vals => .ok (.tuple (.u64 tag.toUInt64 :: vals), st)
    | .error err => .error err
  | .ctorGetObj ctorVar idx =>
    match env ctorVar with
    | some (.tuple (_tag :: vals)) =>
      match vals[idx]? with
      | some v => .ok (v, st)
      | none => .error (.outOfBounds idx vals.length)
    | some (.tuple []) => .error (.outOfBounds idx 0)
    | some _ => .error (.typeError "ctorGetObj expects constructor tuple")
    | none => .error (.unboundVar ctorVar)
  | .ctorGetScalar ctorVar idx _ty =>
    match env ctorVar with
    | some (.tuple (_tag :: vals)) =>
      match vals[idx]? with
      | some v => .ok (v, st)
      | none => .error (.outOfBounds idx vals.length)
    | some (.tuple []) => .error (.outOfBounds idx 0)
    | some _ => .error (.typeError "ctorGetScalar expects constructor tuple")
    | none => .error (.unboundVar ctorVar)
  | .isExclusive objVar =>
    match env objVar with
    | some (.sarrayId bufId) =>
      match st.findBuffer bufId with
      | some buf => .ok (.bool buf.exclusive, st)
      | none => .error (.typeError s!"unknown sarray buffer {bufId}")
    | some _ => .ok (.bool true, st)
    | none => .error (.unboundVar objVar)
  | .sarrayLen arrVar =>
    match env arrVar with
    | some (.sarrayId bufId) =>
      match st.findBuffer bufId with
      | some buf => .ok (.u64 buf.data.size.toUInt64, st)
      | none => .error (.typeError s!"unknown sarray buffer {bufId}")
    | some _ => .error (.typeError "sarrayLen expects sarrayId")
    | none => .error (.unboundVar arrVar)
  | .sarrayDataPtr arrVar _elemTy =>
    match env arrVar with
    | some (.sarrayId bufId) =>
      match st.findBuffer bufId with
      | some buf =>
        if buf.exclusive then .ok (.rawPtrId bufId, st)
        else .error (.nonExclusiveWrite bufId)
      | none => .error (.typeError s!"unknown sarray buffer {bufId}")
    | some (.rawPtrId bufId) => .ok (.rawPtrId bufId, st)
    | some _ => .error (.typeError "sarrayDataPtr expects sarrayId")
    | none => .error (.unboundVar arrVar)
  | .sarrayEnsureExclusive arrVar _elemTy =>
    match env arrVar with
    | some (.sarrayId bufId) =>
      match st.ensureExclusive bufId with
      | .ok st' => .ok (.sarrayId bufId, st')
      | .error err => .error err
    | some _ => .error (.typeError "sarrayEnsureExclusive expects sarrayId")
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
  | .rawLoad ptrVar idxVar _elemTy =>
    match env ptrVar, env idxVar with
    | some (.rawPtrId bufId), some (.u64 idx) =>
      match st.readElem bufId idx.toNat with
      | .ok v => .ok (.u64 v, st)
      | .error err => .error err
    | some (.sarrayId bufId), some (.u64 idx) =>
      match st.readElem bufId idx.toNat with
      | .ok v => .ok (.u64 v, st)
      | .error err => .error err
    | none, _ => .error (.unboundVar ptrVar)
    | _, none => .error (.unboundVar idxVar)
    | _, _ => .error (.typeError "rawLoad expects rawPtrId/sarrayId and u64 index")
  | .boxScalar valVar _ty =>
    match env valVar with
    | some v => .ok (v, st)
    | none => .error (.unboundVar valVar)
  | .unboxScalar boxVar _ty =>
    match env boxVar with
    | some v => .ok (v, st)
    | none => .error (.unboundVar boxVar)
  | .call fnName args _retTy isExtern =>
    match evalVarList env args with
    | .ok vals =>
      if isExtern then
        .error (.unsupportedCall fnName)
      else if fnName == "lean_native_box_u64" || fnName == "lean_native_unbox_u64" then
        match vals with
        | [v] => .ok (v, st)
        | _ => .error (.typeError s!"{fnName} expects 1 argument")
      else if fnName == "lean_native_ensure_exclusive" then
        match vals with
        | [.sarrayId bufId] =>
          match st.ensureExclusive bufId with
          | .ok st' => .ok (.sarrayId bufId, st')
          | .error err => .error err
        | [v] => .ok (v, st)
        | _ => .error (.typeError "lean_native_ensure_exclusive expects 1 argument")
      else if fnName == "lean_native_sarray_len" then
        match vals with
        | [.sarrayId bufId] =>
          match st.findBuffer bufId with
          | some buf => .ok (.u64 buf.data.size.toUInt64, st)
          | none => .error (.typeError s!"unknown sarray buffer {bufId}")
        | _ => .error (.typeError "lean_native_sarray_len expects 1 sarrayId argument")
      else
        .error (.unsupportedCall fnName)
    | .error err => .error err

/-- Read element `elemIdx` from the `argIdx`-th input buffer/scalar of a `parFor` kernel, propagating UB errors. -/
def readParInput (env : VarEnv) (st : HeapState) (inputs : List VarId) (argIdx elemIdx : Nat) : Except UBError UInt64 :=
  match inputs[argIdx]? with
  | none => .error (.outOfBounds argIdx inputs.length)
  | some v =>
    match env v with
    | none => .error (.unboundVar v)
    | some (.sarrayId bid) | some (.rawPtrId bid) => st.readElem bid elemIdx
    | some (.u64 x) => .ok x
    | some _ => .error (.typeError "parFor input must be sarrayId, rawPtrId, or u64")

/-- Bind custom scalar kernel input variables `inVars` to elements at `elemIdx`. -/
def bindCustomParInputs (env : VarEnv) (st : HeapState) (inputs : List VarId) (elemIdx : Nat)
    (curEnv : VarEnv) (argIdx : Nat) : List VarId → Except UBError VarEnv
  | [] => .ok curEnv
  | iv :: rest =>
    match readParInput env st inputs argIdx elemIdx with
    | .ok x => bindCustomParInputs env st inputs elemIdx (curEnv.bind iv (.u64 x)) (argIdx + 1) rest
    | .error err => .error err

/-- Evaluate element `i` of a data-parallel `ParallelKernelKind` over `inputs`. -/
def evalParKernelElem (env : VarEnv) (st : HeapState) (inputs : List VarId) (len : Nat)
    (kernel : ParallelKernelKind) (i : Nat) : Except UBError UInt64 :=
  match kernel with
  | .mapScaleAdd scale bias =>
    match readParInput env st inputs 0 i with
    | .ok x => .ok (x * scale + bias)
    | .error err => .error err
  | .zipAdd =>
    match readParInput env st inputs 0 i, readParInput env st inputs 1 i with
    | .ok x, .ok y => .ok (x + y)
    | .error err, _ => .error err
    | _, .error err => .error err
  | .zipMul | .dotProduct =>
    match readParInput env st inputs 0 i, readParInput env st inputs 1 i with
    | .ok x, .ok y => .ok (x * y)
    | .error err, _ => .error err
    | _, .error err => .error err
  | .saxpy alpha =>
    match readParInput env st inputs 0 i, readParInput env st inputs 1 i with
    | .ok x, .ok y => .ok (alpha * x + y)
    | .error err, _ => .error err
    | _, .error err => .error err
  | .stencil1D3Pt wL wC wR =>
    if i == 0 || i + 1 >= len then
      readParInput env st inputs 0 i
    else
      match readParInput env st inputs 0 (i - 1), readParInput env st inputs 0 i, readParInput env st inputs 0 (i + 1) with
      | .ok l, .ok c, .ok r => .ok (wL * l + wC * c + wR * r)
      | .error err, _, _ => .error err
      | _, .error err, _ => .error err
      | _, _, .error err => .error err
  | .customScalar idxVar inVars body =>
    let kEnv0 := env.bind idxVar (.u64 i.toUInt64)
    match bindCustomParInputs env st inputs i kEnv0 0 inVars with
    | .ok kEnv =>
      match evalScalarExpr kEnv body with
      | .ok (.u64 v) => .ok v
      | .ok (.bool b) => .ok (if b then 1 else 0)
      | .ok _ => .error (.typeError "customScalar body must evaluate to u64 or bool")
      | .error err => .error err
    | .error err => .error err

/-- Evaluate all indices in `0 .. len - 1` for a `parFor` kernel, stopping on the first `UBError`. -/
def evalParKernelLoop (env : VarEnv) (st : HeapState) (inputs : List VarId) (len : Nat)
    (kernel : ParallelKernelKind) : List Nat → Except UBError (List UInt64)
  | [] => .ok []
  | i :: is =>
    match evalParKernelElem env st inputs len kernel i, evalParKernelLoop env st inputs len kernel is with
    | .ok x, .ok xs => .ok (x :: xs)
    | .error err, _ => .error err
    | _, .error err => .error err

/-- Deterministic parallel loop evaluator allocating a fresh output `ArrayBuffer` (`st.nextId + 1`) in `HeapState`. -/
def evalParFor (fuel : Nat) (env : VarEnv) (st : HeapState) (lenVar : VarId) (inputs : List VarId)
    (kernel : ParallelKernelKind) : Except UBError (Val × HeapState) :=
  match env lenVar with
  | none => .error (.unboundVar lenVar)
  | some (.u64 n) =>
    let len := n.toNat
    if len > fuel then .error (.outOfBounds len fuel)
    else
      match evalVarList env inputs with
      | .error err => .error err
      | .ok _ =>
        match evalParKernelLoop env st inputs len kernel (List.range len) with
        | .error err => .error err
        | .ok elems =>
          let outData := match kernel with
            | .dotProduct => #[elems.foldl (· + ·) 0]
            | _ => elems.toArray
          let outId := st.nextId + 1
          let outBuf : ArrayBuffer := { id := outId, exclusive := true, data := outData }
          .ok (.sarrayId outId, { st with buffers := outBuf :: st.buffers, nextId := outId })
  | some _ => .error (.typeError "parFor length must be u64")

/-- Bounded sequential loop evaluation helper for `seqFor`. -/
def evalSeqLoop (count : Nat) (curIdx : Nat) (idxVar accVar : VarId)
    (accVal : Val) (env : VarEnv) (st : HeapState)
    (evalStep : VarEnv → HeapState → Except UBError (Val × HeapState)) :
    Except UBError (Val × HeapState) :=
  match count with
  | 0 => .ok (accVal, st)
  | count' + 1 =>
    let stepEnv := (env.bind idxVar (.u64 curIdx.toUInt64)).bind accVar accVal
    match evalStep stepEnv st with
    | .ok (nextAcc, st') =>
      evalSeqLoop count' (curIdx + 1) idxVar accVar nextAcc env st' evalStep
    | .error err => .error err

/-- Total operational evaluator for structured `LNIRCode` by direct structural recursion on `code`.
    Because `LNIRCode` is a finite syntax tree and `seqFor` is bounded by `hi - lo`,
    termination is structural on `code : LNIRCode` with no artificial `fuel = 0` truncation. -/
def evalCode (fuel : Nat) : VarEnv → HeapState → LNIRCode → Except UBError (Val × HeapState)
  | env, st, .letBind dst _ty val k =>
    match evalExpr env st val with
    | .ok (v, st') => evalCode fuel (env.bind dst v) st' k
    | .error err => .error err
  | env, st, .rawStore ptrVar idxVar valVar _elemTy k =>
    match env ptrVar, env idxVar, env valVar with
    | some (.rawPtrId bufId), some (.u64 idx), some (.u64 val) =>
      match st.writeElemExclusive bufId idx.toNat val with
      | .ok st' => evalCode fuel env st' k
      | .error err => .error err
    | some (.sarrayId bufId), some (.u64 idx), some (.u64 val) =>
      match st.writeElemExclusive bufId idx.toNat val with
      | .ok st' => evalCode fuel env st' k
      | .error err => .error err
    | none, _, _ => .error (.unboundVar ptrVar)
    | _, none, _ => .error (.unboundVar idxVar)
    | _, _, none => .error (.unboundVar valVar)
    | _, _, _ => .error (.typeError "rawStore requires rawPtrId/sarrayId and u64 index/value")
  | env, st, .incRef objVar count k =>
    match st.evalIncRef env objVar count with
    | .ok st' => evalCode fuel env st' k
    | .error err => .error err
  | env, st, .decRef objVar count k =>
    match st.evalDecRef env objVar count with
    | .ok st' => evalCode fuel env st' k
    | .error err => .error err
  | env, st, .ite condVar thenBranch elseBranch =>
    match env condVar with
    | some (.bool true) => evalCode fuel env st thenBranch
    | some (.bool false) => evalCode fuel env st elseBranch
    | some (.u64 n) =>
      if n != 0 then evalCode fuel env st thenBranch
      else evalCode fuel env st elseBranch
    | some (.u256 w) =>
      if w != UInt256.zero then evalCode fuel env st thenBranch
      else evalCode fuel env st elseBranch
    | some _ => .error (.typeError "ite condition must be bool, u64, or u64")
    | none => .error (.unboundVar condVar)
  | env, st, .seqFor idxVar loVar hiVar accVar accInit _accTy stepBody k =>
    match env loVar, env hiVar, env accInit with
    | some (.u64 lo), some (.u64 hi), some initVal =>
      let count := hi.toNat - lo.toNat
      match evalSeqLoop count lo.toNat idxVar accVar initVal env st
          (fun stepEnv stepSt => evalCode fuel stepEnv stepSt stepBody) with
      | .ok (finalAcc, st') => evalCode fuel (env.bind accVar finalAcc) st' k
      | .error err => .error err
    | none, _, _ => .error (.unboundVar loVar)
    | _, none, _ => .error (.unboundVar hiVar)
    | _, _, none => .error (.unboundVar accInit)
    | _, _, _ => .error (.typeError "seqFor bounds must be u64")
  | env, st, .parFor outVar lenVar inputs _elemTy kernel k =>
    match evalParFor fuel env st lenVar inputs kernel with
    | .ok (outVal, st') => evalCode fuel (env.bind outVar outVal) st' k
    | .error err => .error err
  | env, st, .ret v =>
    match env v with
    | some val => .ok (val, st)
    | none => .error (.unboundVar v)
  | _, _, .unreachable =>
    .error (.typeError "reached unreachable code")

end LeanNative.Semantics
