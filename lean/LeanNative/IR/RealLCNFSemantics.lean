import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.IR.RealLCNFBridge
import LeanNative.Semantics.Value
import Lean.Compiler.LCNF.Basic

namespace LeanNative.IR.RealLCNFSemantics

open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.Semantics

/-!
# Independent Operational Semantics of Real `Lean.Compiler.LCNF` (`RealLCNFSemantics`)

Track C4 evaluator over real upstream `Lean.Compiler.LCNF` ASTs (`LitValue`, `Arg .impure`,
`LetValue .impure`, `Alt .impure`, `Code .impure`, `Decl .impure`).
It does not import `LeanNative.Semantics.Eval` and does not call `lowerRealLCNFCode` /
`lowerImpureStepPure`. Arithmetic is computed directly over fixed-width `BitVec 64` words masked
to the operand bitwidth (`1`, `8`, `16`, `32`, or `64`), constructor/projection/mutation layout
follows `RcCtorLayoutSpec` (`HEAPOBJ_CONTRACT C1.2`), and non-recursive join points (`Code.jp` /
`Code.jmp`) evaluate the recorded join-point body under bound parameter environments.
-/

structure JpBody where
  params : List (Lean.Compiler.LCNF.Param .impure)
  code   : Lean.Compiler.LCNF.Code .impure
  deriving Inhabited

structure LEnv where
  vals  : Lean.FVarId → Option Val := fun _ => none
  tys   : Lean.FVarId → Option LNIRType := fun _ => none
  ctors : Lean.FVarId → Option Lean.Name := fun _ => none
  jps   : Lean.FVarId → Option JpBody := fun _ => none
  deriving Inhabited

def LEnv.empty : LEnv := {}

def LEnv.bind (env : LEnv) (x : Lean.FVarId) (v : Val) (ctor? : Option Lean.Name := none)
    (ty? : Option LNIRType := none) : LEnv :=
  { env with
    vals  := fun y => if y == x then some v else env.vals y
    tys   := fun y => if y == x then ty? else env.tys y
    ctors := fun y => if y == x then ctor? else env.ctors y }

def bindParams (ctx : RealBridgeCtx) (isTopLevel : Bool) (env : LEnv) :
    List (Lean.Compiler.LCNF.Param .impure) → List Val → Except UBError LEnv
  | [], [] => .ok env
  | p :: ps, v :: vs =>
    let pTy := if isTopLevel then ctx.lowerParamType p else lowerGroundImpureTypeWith ctx p.type
    let env1 : LEnv := { env with
      vals  := fun y => if y == p.fvarId then some v else env.vals y
      tys   := fun y => if y == p.fvarId then some pTy else env.tys y
      ctors := fun y => if y == p.fvarId then none else env.ctors y }
    bindParams ctx isTopLevel env1 ps vs
  | _, _ => .error (.typeError "join point arity mismatch")

def jpParamType (ctx : RealBridgeCtx) (origTys : Lean.FVarId → Option LNIRType)
    (p : Lean.Compiler.LCNF.Param .impure) (a : Lean.Compiler.LCNF.Arg .impure) : LNIRType :=
  let rawPTy := lowerGroundImpureTypeWith ctx p.type
  match a with
  | .fvar x =>
    let vt := (origTys x).getD .objPtr
    if isUnboxedScalarOrTuple vt && isHeapPtrType rawPTy then vt else rawPTy
  | .erased | .type .. =>
    if !ctx.allowStage1DHeap && isHeapPtrType rawPTy then .i64 else rawPTy

def bindJpParams (ctx : RealBridgeCtx) (origTys : Lean.FVarId → Option LNIRType) (env : LEnv) :
    List (Lean.Compiler.LCNF.Param .impure) → List (Lean.Compiler.LCNF.Arg .impure) → List Val → Except UBError LEnv
  | [], [], [] => .ok env
  | p :: ps, a :: as_, v :: vs =>
    let pTy := jpParamType ctx origTys p a
    let env1 : LEnv := { env with
      vals  := fun y => if y == p.fvarId then some v else env.vals y
      tys   := fun y => if y == p.fvarId then some pTy else env.tys y
      ctors := fun y => if y == p.fvarId then none else env.ctors y }
    bindJpParams ctx origTys env1 ps as_ vs
  | _, _, _ => .error (.typeError "join point arity mismatch")

def LEnv.withCtor (env : LEnv) (x : Lean.FVarId) (ctorName : Lean.Name) : LEnv :=
  { env with ctors := fun y => if y == x then some ctorName else env.ctors y }

def LEnv.withCtorOpt (env : LEnv) (x : Lean.FVarId) (ctor? : Option Lean.Name) : LEnv :=
  { env with ctors := fun y => if y == x then ctor? else env.ctors y }

def LEnv.resolveCtor? (ctx : RealBridgeCtx) (env : LEnv) (x : Lean.FVarId) : Option Lean.Name :=
  env.ctors x <|> ctx.findKnownFVarCtor? x

def LEnv.bindJp (env : LEnv) (x : Lean.FVarId) (body : JpBody) : LEnv :=
  { env with jps := fun y => if y == x then some body else env.jps y }

def wordOf (n : Nat) : UInt64 := n.toUInt64

def bvOf (v : Val) : Option (BitVec 64) :=
  match v with
  | .u64 n => some n.toBitVec
  | .bool b => some (if b then 1#64 else 0#64)
  | _ => none

def ofWord (w : BitVec 64) : Val := .u64 (UInt64.ofBitVec w)

def widthOf (arch : TargetArch) (ty : LNIRType) : Nat :=
  match ty with
  | .i1 => 1
  | .i8 => 8
  | .i16 => 16
  | .i32 => 32
  | .usize => if arch.isILP32 then 32 else 64
  | _ => 64

def maskOf (arch : TargetArch) (ty : LNIRType) : BitVec 64 :=
  BitVec.ofNat 64 (2 ^ widthOf arch ty - 1)

def masked (arch : TargetArch) (ty : LNIRType) (w : BitVec 64) : BitVec 64 :=
  w &&& maskOf arch ty

def shiftMaskOf (arch : TargetArch) (ty : LNIRType) : BitVec 64 :=
  BitVec.ofNat 64 (widthOf arch ty - 1)

def wrapBoolOut (b : Bool) (retTy : LNIRType) : Except UBError Val :=
  if lnirTypeEq retTy .i1 then .ok (.bool b)
  else if lnirTypeEq retTy .i8 then .ok (.u64 (if b then 1 else 0))
  else .error (.typeError "comparison / boolean intrinsic expects i1 or i8 return type")

def wordBin (arch : TargetArch) (op : BinOp) (ty retTy : LNIRType) (va vb : Val) : Except UBError Val :=
  if lnirTypeEq ty .i1 then
    match op, va, vb with
    | .bitAnd, .bool a, .bool b => wrapBoolOut (a && b) retTy
    | .bitOr,  .bool a, .bool b => wrapBoolOut (a || b) retTy
    | .bitXor, .bool a, .bool b => wrapBoolOut (a != b) retTy
    | .eq,     .bool a, .bool b => wrapBoolOut (a == b) retTy
    | _, _, _ => .error (.typeError "unsupported i1 scalar operator")
  else
    match va, vb with
    | .u64 na, .u64 nb =>
      if (lnirTypeEq ty .usize || lnirTypeEq retTy .usize) && !archSupportsUSize arch then
        .error (.typeError "USize unsupported on target architecture")
      else
      let am := masked arch ty na.toBitVec
      let bm := masked arch ty nb.toBitVec
      match op with
      | .add => if lnirTypeEq retTy ty then .ok (ofWord (masked arch ty (am + bm))) else .error (.typeError "return type mismatch")
      | .sub => if lnirTypeEq retTy ty then .ok (ofWord (masked arch ty (am - bm))) else .error (.typeError "return type mismatch")
      | .mul => if lnirTypeEq retTy ty then .ok (ofWord (masked arch ty (am * bm))) else .error (.typeError "return type mismatch")
      | .div => if lnirTypeEq retTy ty then .ok (ofWord (if bm == 0#64 then 0#64 else am / bm)) else .error (.typeError "return type mismatch")
      | .mod => if lnirTypeEq retTy ty then .ok (ofWord (if bm == 0#64 then am else am % bm)) else .error (.typeError "return type mismatch")
      | .bitAnd => if lnirTypeEq retTy ty then .ok (ofWord (masked arch ty (am &&& bm))) else .error (.typeError "return type mismatch")
      | .bitOr  => if lnirTypeEq retTy ty then .ok (ofWord (masked arch ty (am ||| bm))) else .error (.typeError "return type mismatch")
      | .bitXor => if lnirTypeEq retTy ty then .ok (ofWord (masked arch ty (am ^^^ bm))) else .error (.typeError "return type mismatch")
      | .shl =>
        if lnirTypeEq retTy ty then
          if shiftMaskOf arch ty == 63#64 then .ok (ofWord (masked arch ty (UInt64.ofBitVec am <<< UInt64.ofBitVec bm).toBitVec))
          else .ok (ofWord (masked arch ty (am <<< (bm &&& shiftMaskOf arch ty))))
        else .error (.typeError "return type mismatch")
      | .shr =>
        if lnirTypeEq retTy ty then
          if shiftMaskOf arch ty == 63#64 then .ok (ofWord (UInt64.ofBitVec am >>> UInt64.ofBitVec bm).toBitVec)
          else .ok (ofWord (am >>> (bm &&& shiftMaskOf arch ty)))
        else .error (.typeError "return type mismatch")
      | .eq => wrapBoolOut (am == bm) retTy
      | .lt => wrapBoolOut (decide (am < bm)) retTy
      | .le => wrapBoolOut (decide (am ≤ bm)) retTy
      | _ => .error (.typeError "unsupported real-LCNF binary operator")
    | _, _ => .error (.typeError "scalar binary intrinsic expects u64 operands")

def boolBitOf (v : Val) : Option Bool :=
  match v with
  | .bool b => some b
  | .u64 n => some ((n &&& 1) != 0)
  | _ => none

def boolBitTyped (v : Val) (ty : LNIRType) : Option Bool :=
  if lnirTypeEq ty .i1 then
    match v with | .bool b => some b | _ => none
  else if lnirTypeEq ty .i8 then
    match v with | .u64 n => some ((n &&& 1) != 0) | _ => none
  else none

def evalBoolBinCall? (fn : Lean.Name) (va vb : Val) (tyA tyB retTy : LNIRType) :
    Option (Except UBError Val) :=
  let evalOp (op : Bool → Bool → Bool) : Option (Except UBError Val) :=
    if (!lnirTypeEq tyA .i1 && !lnirTypeEq tyA .i8) || (!lnirTypeEq tyB .i1 && !lnirTypeEq tyB .i8) ||
        (!lnirTypeEq retTy .i1 && !lnirTypeEq retTy .i8) then none
    else match boolBitTyped va tyA, boolBitTyped vb tyB with
      | some a, some b => some (wrapBoolOut (op a b) retTy)
      | _, _ => some (.error (.typeError "boolean intrinsic expects typed bool or i8-encoded bool"))
  if fn == ``Bool.and then evalOp (· && ·)
  else if fn == ``Bool.or then evalOp (· || ·)
  else if fn == ``Bool.xor || fn == `Bool.bne || fn == `bne then evalOp (· != ·)
  else if fn == ``Bool.beq then evalOp (· == ·)
  else none

def uintPrimMask? (arch : TargetArch) (nm : Lean.Name) : Option (LNIRType × BitVec 64) :=
  if nm == ``UInt8 then some (.i8, 0xFF#64)
  else if nm == ``UInt16 then some (.i16, 0xFFFF#64)
  else if nm == ``UInt32 then some (.i32, 0xFFFFFFFF#64)
  else if nm == ``UInt64 then some (.i64, 0xFFFFFFFFFFFFFFFF#64)
  else if nm == ``USize && archSupportsUSize arch then
    some (.usize, if arch.isILP32 then 0xFFFFFFFF#64 else 0xFFFFFFFFFFFFFFFF#64)
  else none

def canonicalCastEval (fuel : Nat)
    (pairs : List (Lean.Name × LNIRType × BitVec 64 × Lean.Name × String × LNIRType × BitVec 64))
    (fn : Lean.Name) (va : Val) (tyA retTy : LNIRType) : Option (Except UBError Val) :=
  match fuel, pairs with
  | 0, _ | _, [] => none
  | fuel + 1, (src, sTy, sm, dst, toSuffix, dTy, dm) :: rest =>
    if src != dst && fn == Lean.Name.str src toSuffix &&
        lnirTypeEq tyA sTy && lnirTypeEq retTy dTy then
      some <| match va with
        | .u64 n => .ok (ofWord (n.toBitVec &&& (if sm.toNat ≤ dm.toNat then sm else dm)))
        | _ => .error (.typeError "bitAnd requires u64 or u256")
    else
      canonicalCastEval fuel rest fn va tyA retTy

def evalUnaryOrCastCall? (arch : TargetArch) (fn : Lean.Name) (va : Val) (tyA retTy : LNIRType) :
    Option (Except UBError Val) :=
  if fn == ``Bool.not then
    if lnirTypeEq tyA .i1 && lnirTypeEq retTy .i1 then
      some <| match va with
        | .bool b => .ok (.bool (!b))
        | _ => .error (.typeError "evalUnaryOp: invalid operand type")
    else if lnirTypeEq tyA .i8 && lnirTypeEq retTy .i8 then
      some <| match va with
        | .u64 n => .ok (.u64 (if (n &&& 1) == 0 then 1 else 0))
        | _ => .error (.typeError "bitAnd requires u64 or u256")
    else none
  else if fn == ``Bool.toUInt8 || fn == ``Bool.toUInt16 ||
          fn == ``Bool.toUInt32 || fn == ``Bool.toUInt64 || fn == ``Bool.toUSize then
    let expectedRet : LNIRType :=
      if fn == ``Bool.toUInt8 then .i8
      else if fn == ``Bool.toUInt16 then .i16
      else if fn == ``Bool.toUInt32 then .i32
      else if fn == ``Bool.toUInt64 then .i64
      else .usize
    if !lnirTypeEq retTy expectedRet || !isSupportedStage1BScalarType expectedRet arch then none
    else if lnirTypeEq tyA .i1 then
      some <| match va with
        | .bool b => .ok (.u64 (if b then 1 else 0))
        | _ => .error (.typeError "select condition must be bool, u64, or u256")
    else if lnirTypeEq tyA .i8 then
      some <| match va with
        | .u64 n => .ok (.u64 (n &&& 1))
        | _ => .error (.typeError "bitAnd requires u64 or u256")
    else none
  else
    let unarySpec? : Option (LNIRType × Bool) :=
      if fn == ``UInt8.complement then some (.i8, false)
      else if fn == ``UInt16.complement then some (.i16, false)
      else if fn == ``UInt32.complement then some (.i32, false)
      else if fn == ``UInt64.complement then some (.i64, false)
      else if fn == ``USize.complement then some (.usize, false)
      else if fn == ``UInt8.neg then some (.i8, true)
      else if fn == ``UInt16.neg then some (.i16, true)
      else if fn == ``UInt32.neg then some (.i32, true)
      else if fn == ``UInt64.neg then some (.i64, true)
      else if fn == ``USize.neg then some (.usize, true)
      else none
    match unarySpec? with
    | some (opTy, isNeg) =>
      if !lnirTypeEq tyA opTy || !lnirTypeEq retTy opTy || !isSupportedStage1BScalarType opTy arch then none
      else
        some <| match va with
          | .u64 n =>
            let w := n.toBitVec
            let raw := if isNeg then 0#64 - w else ~~~w
            .ok (ofWord (masked arch opTy raw))
          | _ =>
            if isNeg then .error (.typeError "evalBinOp: invalid operand types")
            else .error (.typeError "evalUnaryOp: invalid operand type")
    | none =>
      let prims : List (Lean.Name × String × LNIRType × BitVec 64) :=
        [(``UInt8, "toUInt8", .i8, 0xFF#64), (``UInt16, "toUInt16", .i16, 0xFFFF#64),
         (``UInt32, "toUInt32", .i32, 0xFFFFFFFF#64), (``UInt64, "toUInt64", .i64, 0xFFFFFFFFFFFFFFFF#64)] ++
        (match uintPrimMask? arch ``USize with | some (ty, m) => [(``USize, "toUSize", ty, m)] | none => [])
      let pairs := prims.flatMap fun (src, _, sTy, sm) =>
        prims.map fun (dst, toSuffix, dTy, dm) => (src, sTy, sm, dst, toSuffix, dTy, dm)
      canonicalCastEval 64 pairs fn va tyA retTy

def asBool (v : Val) : Except UBError Bool :=
  match v with
  | .bool b => .ok b
  | .u64 n => .ok (n != 0)
  | .u256 w => .ok (w != UInt256.zero)
  | _ => .error (.typeError "ite condition must be bool, u64, or u64")

def evalLit (arch : TargetArch) (lit : Lean.Compiler.LCNF.LitValue) (ty : LNIRType)
    (allowInternalObj : Bool := false) : Except UBError Val :=
  if lnirTypeEq ty .usize && !archSupportsUSize arch then
    .error (.typeError "USize unsupported on target architecture")
  else
    let raw : Except UBError (BitVec 64) := match lit with
      | .nat n =>
        if (lnirTypeEq ty .taggedPtr || lnirTypeEq ty .objPtr) && !allowInternalObj then
          .error (.typeError "unsupported runtime Nat literal")
        else
          .ok (BitVec.ofNat 64 (n % (2 ^ 64)))
      | .uint8 v => .ok v.toUInt64.toBitVec
      | .uint16 v => .ok v.toUInt64.toBitVec
      | .uint32 v => .ok v.toUInt64.toBitVec
      | .uint64 v => .ok v.toBitVec
      | .usize v =>
        if !archSupportsUSize arch then .error (.typeError "USize unsupported on target architecture")
        else .ok (masked arch .usize v.toBitVec)
      | .str _ => .error (.typeError "unsupported string literal")
    match raw with
    | .error e => .error e
    | .ok w0 =>
      let w := match scalarWidthMask? ty arch with
        | some m => w0 &&& m.toBitVec
        | none => w0
      if lnirTypeEq ty .i1 then .ok (.bool (w != 0#64)) else .ok (ofWord w)

def evalArg (env : Lean.FVarId → Option Val) (arg : Lean.Compiler.LCNF.Arg .impure) : Except UBError Val :=
  match arg with
  | .fvar x => match env x with | some v => .ok v | none => .error (.unboundVar 0)
  | .erased | .type .. => .error (.typeError "erased runtime argument")

def evalArgs (env : Lean.FVarId → Option Val) :
    List (Lean.Compiler.LCNF.Arg .impure) → Except UBError (List Val)
  | [] => .ok []
  | a :: as_ =>
    match evalArg env a, evalArgs env as_ with
    | .ok v, .ok vs => .ok (v :: vs)
    | .error e, _ | _, .error e => .error e

def evalJpArg (env : Lean.FVarId → Option Val) (arg : Lean.Compiler.LCNF.Arg .impure) : Except UBError Val :=
  match arg with
  | .erased | .type .. => .ok (.u64 0)
  | .fvar x => match env x with | some v => .ok v | none => .error (.unboundVar 0)

def evalJpArgs (env : Lean.FVarId → Option Val) :
    List (Lean.Compiler.LCNF.Arg .impure) → Except UBError (List Val)
  | [] => .ok []
  | a :: as_ =>
    match evalJpArg env a, evalJpArgs env as_ with
    | .ok v, .ok vs => .ok (v :: vs)
    | .error e, _ | _, .error e => .error e

def evalGfSimd (op : BinOp) (va vb : Val) : Except UBError Val :=
  match op with
  | .clmul64 =>
    match va, vb with
    | .u64 a, .u64 b => .ok (.u64 (clmul64 a b))
    | _, _ => .error (.typeError "evalBinOp: clmul64/clmul64Hi/gf2Affine/eor3 require u64")
  | .clmul64Hi =>
    match va, vb with
    | .u64 a, .u64 b => .ok (.u64 (clmul64Hi a b))
    | _, _ => .error (.typeError "evalBinOp: clmul64/clmul64Hi/gf2Affine/eor3 require u64")
  | .gf2Affine =>
    match va, vb with
    | .u64 a, .u64 b => .ok (.u64 (gf2Affine a b))
    | _, _ => .error (.typeError "evalBinOp: clmul64/clmul64Hi/gf2Affine/eor3 require u64")
  | .eor3 =>
    match va, vb with
    | .u64 a, .u64 b => .ok (.u64 (eor3 a b))
    | _, _ => .error (.typeError "evalBinOp: clmul64/clmul64Hi/gf2Affine/eor3 require u64")
  | _ => .error (.unsupportedCall "non-gfSimd op")

def fieldGet (fs : List Val) (idx : Nat) : Except UBError Val :=
  match fs[idx]? with
  | some v => .ok v
  | none => .error (.outOfBounds idx fs.length)

def tagOf (v : Val) (st : HeapState) : Except UBError Val :=
  match v with
  | .objPtr objId => (st.liveHeapObj objId).map fun o => .u64 (wordOf o.tag)
  | .u64 n => .ok (.u64 n)
  | .bool b => .ok (.u64 (if b then 1 else 0))
  | .tuple (.u64 n :: _) => .ok (.u64 n)
  | _ => .error (.typeError "lean_native_ctor_tag expects heap object or unboxed tag")

def evalCtorVal (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
    (ctorName : Lean.Name) (cidx : Nat) (args : List (Lean.Compiler.LCNF.Arg .impure))
    (retTy : LNIRType) : Except UBError (Val × HeapState × Option Lean.Name) :=
  if args.isEmpty then
    if ctorName == ``Bool.false then
      .ok ((if lnirTypeEq retTy .i1 then .bool false else .u64 0), st, none)
    else if ctorName == ``Bool.true then
      .ok ((if lnirTypeEq retTy .i1 then .bool true else .u64 1), st, none)
    else if ctorName == ``Unit.unit || ctorName == ``PUnit.unit then
      .ok (.u64 0, st, none)
    else
      .ok ((if lnirTypeEq retTy .i1 then .bool (cidx != 0) else .u64 (wordOf cidx)), st, none)
  else
    let heapSpec? :=
      if ctx.allowStage1DHeap then
        match ctx.findLayout? ctorName with
        | some spec =>
          let dropCnt := if args.length > spec.objSlots then args.length - spec.objSlots else 0
          let fArgs := args.drop dropCnt
          let fTys := fArgs.map fun | .fvar x => (env.tys x).getD .objPtr | _ => .objPtr
          if spec.scalarSlots.isEmpty && !fArgs.isEmpty &&
              fTys.all (fun t => isSupportedStage1BScalarOrTuple t ctx.arch || isHeapPtrType t) then
            some spec
          else none
        | none => none
      else none
    match heapSpec? with
    | some spec =>
      let dropCnt := if args.length > spec.objSlots then args.length - spec.objSlots else 0
      match evalArgs env.vals (args.drop dropCnt) with
      | .ok vs =>
        if vs.isEmpty then .ok (.tuple [.u64 (wordOf cidx)], st, some ctorName)
        else if !vs.all Val.wfField then
          .error (.typeError "allocCtor: object field is a tuple owning an edge")
        else
          let (objId, st') := st.allocHeapCtor cidx vs []
          .ok (.objPtr objId, st', some ctorName)
      | .error e => .error e
    | none =>
      match ctx.findTupleArity? ctorName with
      | some numFields =>
        let dropCnt := if args.length > numFields then args.length - numFields else 0
        match evalArgs env.vals (args.drop dropCnt) with
        | .ok vs => .ok (.tuple vs, st, none)
        | .error e => .error e
      | none => .error (.unsupportedCall s!"ctor {ctorName}")

def LEnv.isTupleVar (env : LEnv) (x : Lean.FVarId) : Bool :=
  match env.tys x with
  | some (.tuple _) => true
  | _ => false

def LEnv.isHeapVar (env : LEnv) (x : Lean.FVarId) : Bool :=
  match env.tys x with
  | none => true
  | some t => isHeapPtrType t

def collectSliceEnvArgs (env : LEnv) :
    List (Lean.Compiler.LCNF.Arg .impure) → Option (List Val × List LNIRType)
  | [] => some ([], [])
  | .erased :: rest | .type .. :: rest => collectSliceEnvArgs env rest
  | .fvar x :: rest =>
    match env.vals x, collectSliceEnvArgs env rest with
    | some v, some (vs, ts) =>
      let t := (env.tys x).getD .objPtr
      some (if lnirTypeEq t .unit then (vs, ts) else (v :: vs, t :: ts))
    | _, _ => none

def evalSliceCall? (arch : TargetArch) (fn : Lean.Name) (env : LEnv) (st : HeapState)
    (args : List (Lean.Compiler.LCNF.Arg .impure)) (ty : LNIRType) :
    Option (Except UBError (Val × HeapState × Option Lean.Name)) :=
  if arch.isWasm then none
  else
  let validLenRet := lnirTypeEq ty .i64 || (lnirTypeEq ty .usize && archSupportsUSize arch)
  let validIdx (t : LNIRType) := lnirTypeEq t .i64 || (lnirTypeEq t .usize && archSupportsUSize arch)
  match collectSliceEnvArgs env args with
  | some ([vArr], [.sarray elemTy]) =>
    if ((fn == ``ByteArray.usize && lnirTypeEq elemTy .i8) ||
        (fn == ``FloatArray.usize && lnirTypeEq elemTy .f64)) && validLenRet then
      some (match vArr with
        | .sarrayId bufId =>
          match st.findBuffer bufId with
          | some buf => .ok (.u64 buf.data.size.toUInt64, st, none)
          | none => .error (.typeError s!"unknown sarray buffer {bufId}")
        | _ => .error (.typeError "sarrayLen expects sarrayId"))
    else none
  | some ([vArr, vIdx], [.sarray elemTy, idxTy]) =>
    if validIdx idxTy &&
       ((fn == ``ByteArray.uget && lnirTypeEq elemTy .i8 && lnirTypeEq ty .i8) ||
        (fn == ``FloatArray.uget && lnirTypeEq elemTy .f64 && lnirTypeEq ty .f64) ||
        (arch.isFreestandingEmbedded && fn == ``ByteArray.get! && lnirTypeEq elemTy .i8 && lnirTypeEq ty .i8)) then
      some (match vArr, vIdx with
        | .sarrayId bufId, .u64 idx =>
          (st.readElem bufId idx.toNat).map (fun v => (.u64 (maskElemVal elemTy v), st, none))
        | _, _ => .error (.typeError "sarrayGet expects sarrayId and u64 index"))
    else none
  | _ => none

def evalLetValue (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
    (lv : Lean.Compiler.LCNF.LetValue .impure) (ty : LNIRType) :
    Except UBError (Val × HeapState × Option Lean.Name) :=
  match lv with
  | .lit lit => (evalLit ctx.arch lit ty true).map (·, st, none)
  | .erased => .ok (.u64 0, st, none)
  | .fvar x args =>
    if !args.isEmpty then .error (.unsupportedCall "higher-order fvar")
    else match env.vals x with | some v => .ok (v, st, none) | none => .error (.unboundVar 0)
  | .ctor info args _ =>
    if ctx.allowStage1DHeap && (info.usize > 0 || info.ssize > 0) then
      match ctx.findLayout? info.name with
      | none => .error (.unsupportedCall s!"unknown layout {info.name}")
      | some spec =>
        if args.size != spec.objSlots then
          .error (.typeError "ctor object arity mismatch")
        else
          match evalArgs env.vals args.toList with
          | .error e => .error e
          | .ok vs =>
            let zeros := spec.scalarSlots.map fun _ => Val.u64 0
            if vs.isEmpty && zeros.isEmpty then .ok (.tuple [.u64 spec.cidx.toUInt64], st, some info.name)
            else if !vs.all Val.wfField then
              .error (.typeError "allocCtor: object field is a tuple owning an edge")
            else
              let (objId, st') := st.allocHeapCtor spec.cidx vs zeros
              .ok (.objPtr objId, st', some info.name)
    else
      evalCtorVal ctx env st info.name info.cidx args.toList ty
  | .reuse _ info _ args _ =>
    evalCtorVal ctx env st info.name info.cidx args.toList ty
  | .oproj idx x _ =>
    let isTupleSrc := env.isTupleVar x
    match env.vals x with
    | some (.objPtr objId) =>
      if isTupleSrc then .error (.typeError "projTuple expects tuple value")
      else (st.liveHeapObj objId).bind fun o => (fieldGet o.objFields idx).map (·, st, none)
    | some (.tuple vs) =>
      if isTupleSrc then (fieldGet vs idx).map (·, st, none)
      else match vs with
        | _tag :: vals => (fieldGet vals idx).map (·, st, none)
        | [] => .error (.outOfBounds idx 0)
    | some _ =>
      if isTupleSrc then .error (.typeError "projTuple expects tuple value")
      else .error (.typeError "ctorGet expects heap constructor or constructor tuple")
    | none => .error (.unboundVar 0)
  | .uproj idx x _ =>
    let isTupleSrc := env.isTupleVar x
    match env.vals x with
    | some (.tuple vs) =>
      if isTupleSrc then (fieldGet vs idx).map (·, st, none)
      else
        let slot := match env.resolveCtor? ctx x >>= ctx.findLayout? >>= (·.usizeSlot? idx) with
          | some (s, _) => s
          | none => idx
        match vs with
        | _tag :: vals => (fieldGet vals slot).map (·, st, none)
        | [] => .error (.outOfBounds slot 0)
    | some (.objPtr objId) =>
      if isTupleSrc then .error (.typeError "projTuple expects tuple value")
      else
        let slot := match env.resolveCtor? ctx x >>= ctx.findLayout? >>= (·.usizeSlot? idx) with
          | some (s, _) => s
          | none => idx
        (st.liveHeapObj objId).bind fun o => (fieldGet o.scalarFields slot).map (·, st, none)
    | some _ =>
      if isTupleSrc then .error (.typeError "projTuple expects tuple value")
      else .error (.typeError "ctorGet expects heap constructor or constructor tuple")
    | none => .error (.unboundVar 0)
  | .sproj n off x _ =>
    let isTupleSrc := env.isTupleVar x
    match env.vals x with
    | some (.tuple vs) =>
      if isTupleSrc then (fieldGet vs off).map (·, st, none)
      else
        let slot := match env.resolveCtor? ctx x >>= ctx.findLayout? >>= (·.scalarSlot? n off) with
          | some (s, _) => s
          | none => off
        match vs with
        | _tag :: vals => (fieldGet vals slot).map (·, st, none)
        | [] => .error (.outOfBounds slot 0)
    | some (.objPtr objId) =>
      if isTupleSrc then .error (.typeError "projTuple expects tuple value")
      else
        let slot := match env.resolveCtor? ctx x >>= ctx.findLayout? >>= (·.scalarSlot? n off) with
          | some (s, _) => s
          | none => off
        (st.liveHeapObj objId).bind fun o => (fieldGet o.scalarFields slot).map (·, st, none)
    | some _ =>
      if isTupleSrc then .error (.typeError "projTuple expects tuple value")
      else .error (.typeError "ctorGet expects heap constructor or constructor tuple")
    | none => .error (.unboundVar 0)
  | .fap fn args _ =>
    if (ctx.findLocalCallee? fn).isSome then
      .error (.unsupportedCall fn.toString)
    else
    match evalSliceCall? ctx.arch fn env st args.toList ty with
    | some res => res
    | none =>
    match args.toList with
    | [a, b] =>
      match evalArg env.vals a, evalArg env.vals b with
      | .ok va, .ok vb =>
        let tA := match a with | .fvar x => (env.tys x).getD .objPtr | _ => .objPtr
        let tB := match b with | .fvar x => (env.tys x).getD .objPtr | _ => .objPtr
        match ctx.findGfSimd? fn with
        | some gfOp =>
          if lnirTypeEq ty .i64 && lnirTypeEq tA .i64 && lnirTypeEq tB .i64 then
            (evalGfSimd gfOp va vb).map (·, st, none)
          else .error (.typeError "GF/SIMD intrinsic operand type mismatch")
        | none =>
          match lookupCanonicalTypedBinOp? fn with
          | some (opTy, op) =>
            if lnirTypeEq tA opTy && lnirTypeEq tB opTy then (wordBin ctx.arch op opTy ty va vb).map (·, st, none)
            else .error (.typeError "binary intrinsic operand type mismatch")
          | none =>
            match evalBoolBinCall? fn va vb tA tB ty with
            | some r => r.map (·, st, none)
            | none => .error (.unsupportedCall fn.toString)
      | .error e, _ | _, .error e => .error e
    | [a] =>
      match evalArg env.vals a with
      | .ok va =>
        let tA := match a with | .fvar x => (env.tys x).getD .objPtr | _ => .objPtr
        match evalUnaryOrCastCall? ctx.arch fn va tA ty with
        | some r => r.map (·, st, none)
        | none => .error (.unsupportedCall fn.toString)
      | .error e => .error e
    | _ => .error (.unsupportedCall fn.toString)
  | .isShared x _ =>
    if !env.isHeapVar x then .ok (.bool true, st, none)
    else match env.vals x with
    | some (.objPtr objId) =>
      let rc := st.getObjRefCount objId
      if rc == 0 then .error (.useAfterFree objId) else .ok (.bool (rc != 1), st, none)
    | some (.sarrayId bufId) =>
      match st.findBuffer bufId with
      | some buf => .ok (.bool (!buf.exclusive), st, none)
      | none => .error (.typeError s!"unknown sarray buffer {bufId}")
    | some _ => .ok (.bool false, st, none)
    | none => .error (.unboundVar 0)
  | .box _ x _ | .unbox x _ | .reset _ x _ =>
    match env.vals x with | some v => .ok (v, st, none) | none => .error (.unboundVar 0)
  | .pap fn _ _ => .error (.unsupportedCall s!"pap {fn}")

def applyRc (isInc : Bool) (env : LEnv) (st : HeapState) (x : Lean.FVarId) (n : Nat) :
    Except UBError HeapState :=
  if !env.isHeapVar x then .ok st
  else match env.vals x with
  | some (.sarrayId bufId) =>
    if isInc then st.incRefBuf bufId n else st.decRefBuf bufId n
  | some (.objPtr objId) =>
    if isInc then st.incRefObj objId n else st.decRefObj objId n
  | some _ => .ok st
  | none => .error (.unboundVar 0)

def writeField (st : HeapState) (objId : Nat) (idx : Nat) (v : Val) (isObj : Bool) :
    Except UBError HeapState :=
  st.writeHeapObjFieldExclusive objId idx v isObj

def evalStep (fuel : Nat) (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
    (target : Lean.Compiler.LCNF.Code .impure ⊕
      (Val × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure))) :
    Except UBError (Val × HeapState) :=
  match fuel with
  | 0 => .error .fuelExhausted
  | fuel + 1 =>
    match target with
    | .inr (cond, isBool, idx, discr?, alts) =>
      match alts with
      | [] => .error (.typeError "reached unreachable code")
      | [.alt _ _ code _] | [.default code] =>
        evalStep fuel ctx env st (.inl code)
      | [.ctorAlt info code _] =>
        let envIn := match discr? with
          | some dx => if (env.vals dx).isSome then env.withCtor dx info.name else env
          | none => env
        evalStep fuel ctx envIn st (.inl code)
      | alt :: rest =>
        match alt with
        | .default code => evalStep fuel ctx env st (.inl code)
        | .ctorAlt info code _ =>
          let envIn := match discr? with
            | some dx => if (env.vals dx).isSome then env.withCtor dx info.name else env
            | none => env
          if isBool then
            match asBool cond with
            | .ok b =>
              if info.cidx == 0 then
                if b then evalStep fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
                else evalStep fuel ctx envIn st (.inl code)
              else if info.cidx == 1 then
                if b then evalStep fuel ctx envIn st (.inl code)
                else evalStep fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
              else evalStep fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
            | .error e => .error e
          else
            match cond with
            | .u64 n =>
              if n == info.cidx.toUInt64 then evalStep fuel ctx envIn st (.inl code)
              else evalStep fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
            | _ => .error (.typeError "evalBinOp: invalid operand types")
        | .alt ctorName _ code _ =>
          let cidx := (ctx.findNullaryCtor? ctorName).getD idx
          if isBool then
            match asBool cond with
            | .ok b =>
              if cidx == 0 then
                if b then evalStep fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
                else evalStep fuel ctx env st (.inl code)
              else if cidx == 1 then
                if b then evalStep fuel ctx env st (.inl code)
                else evalStep fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
              else evalStep fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
            | .error e => .error e
          else
            match cond with
            | .u64 n =>
              if n == cidx.toUInt64 then evalStep fuel ctx env st (.inl code)
              else evalStep fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
            | _ => .error (.typeError "evalBinOp: invalid operand types")
    | .inl code =>
      match code with
      | .let decl k =>
        let rawTy := lowerGroundImpureTypeWith ctx decl.type
        match evalLetValue ctx env st decl.value rawTy with
        | .ok (v, st', ctor?) =>
          let storedTy := match decl.value with
            | .ctor info args _ | .reuse _ info _ args _ =>
              if ctor?.isSome then .objPtr
              else if args.isEmpty then (if isUnboxedScalarOrTuple rawTy then rawTy else .i64)
              else match ctx.findTupleArity? info.name with
                | some numFields =>
                  let dropCnt := if args.size > numFields then args.size - numFields else 0
                  .tuple ((args.toList.drop dropCnt).map fun
                    | .fvar x => (env.tys x).getD .objPtr
                    | _ => .objPtr)
                | none => rawTy
            | .box _ x _ =>
              let sty := (env.tys x).getD .objPtr
              if isUnboxedScalarOrTuple sty then sty else .i64
            | .fvar x _ | .unbox x _ | .reset _ x _ =>
              let sty := (env.tys x).getD .objPtr
              if isUnboxedScalarOrTuple rawTy then rawTy
              else if isUnboxedScalarOrTuple sty then sty else rawTy
            | .oproj idx x _ =>
              match (env.tys x).getD .objPtr with
              | .tuple fs => if isUnboxedScalarOrTuple rawTy then rawTy else fs[idx]?.getD .i64
              | _ => rawTy
            | .uproj idx x _ =>
              match (env.tys x).getD .objPtr with
              | .tuple fs => if isUnboxedScalarOrTuple rawTy then rawTy else fs[idx]?.getD .i64
              | _ => rawTy
            | .sproj _ off x _ =>
              match (env.tys x).getD .objPtr with
              | .tuple fs => if isUnboxedScalarOrTuple rawTy then rawTy else fs[off]?.getD .i64
              | _ => rawTy
            | .isShared x _ =>
              if isUnboxedScalarOrTuple ((env.tys x).getD .objPtr) then
                if isUnboxedScalarOrTuple rawTy then rawTy else .i64
              else .i1
            | .lit _ | .erased =>
              if isUnboxedScalarOrTuple rawTy then rawTy else .i64
            | .fap _ _ _ =>
              if isUnboxedScalarOrTuple rawTy then rawTy else .i64
            | .pap _ _ _ => rawTy
          let storedCtor := match decl.value with
            | .ctor _ _ _ => if lnirTypeEq storedTy .objPtr then ctor? else none
            | _ => none
          evalStep fuel ctx (env.bind decl.fvarId v storedCtor (some storedTy)) st' (.inl k)
        | .error e => .error e
      | .inc x n _ _ k _ =>
        match applyRc true env st x n with
        | .ok st' => evalStep fuel ctx env st' (.inl k)
        | .error e => .error e
      | .dec x n _ _ _ k _ =>
        match applyRc false env st x n with
        | .ok st' => evalStep fuel ctx env st' (.inl k)
        | .error e => .error e
      | .del x k _ =>
        let isHeapTy := env.isHeapVar x
        match env.vals x with
        | some (.objPtr objId) =>
          let stepRes :=
            if ctx.allowStage1DHeap && isHeapTy then st.delObjShell objId
            else if isHeapTy then st.decRefObj objId 1
            else .ok st
          match stepRes with
          | .ok st' => evalStep fuel ctx env st' (.inl k)
          | .error e => .error e
        | some (.sarrayId bufId) =>
          let stepRes :=
            if ctx.allowStage1DHeap && isHeapTy then .error (.typeError "lean_native_del_obj expects (objPtr)")
            else if isHeapTy then st.decRefBuf bufId 1
            else .ok st
          match stepRes with
          | .ok st' => evalStep fuel ctx env st' (.inl k)
          | .error e => .error e
        | some _ =>
          if ctx.allowStage1DHeap && isHeapTy then .error (.typeError "lean_native_del_obj expects (objPtr)")
          else evalStep fuel ctx env st (.inl k)
        | none =>
          if isHeapTy then .error (.unboundVar 0)
          else evalStep fuel ctx env st (.inl k)
      | .setTag x cidx k _ =>
        match env.vals x with
        | some (.objPtr objId) =>
          let nextCtor? := match env.resolveCtor? ctx x with
            | some cur =>
              if ctx.hasSiblingEntry cur then ctx.findSiblingCtor? cur cidx
              else none
            | none => none
          match st.setHeapObjTagExclusive objId (cidx.toUInt64).toNat with
          | .ok st' => evalStep fuel ctx (env.withCtorOpt x nextCtor?) st' (.inl k)
          | .error e => .error e
        | none => .error (.unboundVar 0)
        | _ => .error (.typeError "lean_native_ctor_set_tag expects (objPtr, u64)")
      | .oset x i y k _ =>
        if !env.isHeapVar x then evalStep fuel ctx env st (.inl k)
        else match env.vals x with
        | some (.objPtr objId) =>
          match evalArg env.vals y with
          | .ok v =>
            match writeField st objId (i.toUInt64).toNat v true with
            | .ok st' => evalStep fuel ctx env st' (.inl k)
            | .error e => .error e
          | .error e => .error e
        | none => .error (.unboundVar 0)
        | some _ =>
          match evalArg env.vals y with
          | .ok _ => .error (.typeError "lean_native_ctor_set expects (objPtr, u64, val)")
          | .error e => .error e
      | .uset x i y k _ =>
        match env.vals x, env.vals y with
        | some (.objPtr objId), some v =>
          let slot := match env.resolveCtor? ctx x >>= ctx.findLayout? >>= (·.usizeSlot? i) with
            | some (s, _) => s
            | none => i
          match writeField st objId (slot.toUInt64).toNat v false with
          | .ok st' => evalStep fuel ctx env st' (.inl k)
          | .error e => .error e
        | none, _ | _, none => .error (.unboundVar 0)
        | _, _ => .error (.typeError "lean_native_ctor_set_scalar expects (objPtr, u64, val)")
      | .sset x n off y _ k _ =>
        match env.vals x, env.vals y with
        | some (.objPtr objId), some v =>
          let slot := match env.resolveCtor? ctx x >>= ctx.findLayout? >>= (·.scalarSlot? n off) with
            | some (s, _) => s
            | none => off
          match writeField st objId (slot.toUInt64).toNat v false with
          | .ok st' => evalStep fuel ctx env st' (.inl k)
          | .error e => .error e
        | none, _ | _, none => .error (.unboundVar 0)
        | _, _ => .error (.typeError "lean_native_ctor_set_scalar expects (objPtr, u64, val)")
      | .cases c =>
        match env.vals c.discr with
        | none => .error (.unboundVar 0)
        | some v =>
          let ordered := orderAltsPure c.alts.toList
          if (ctx.allowStage1DHeap || c.typeName == ``Bool) && env.isHeapVar c.discr then
            match tagOf v st with
            | .ok tag => evalStep fuel ctx env st (.inr (tag, false, 0, some c.discr, ordered))
            | .error e => .error e
          else
            let isBool := c.typeName == ``Bool || lnirTypeEq ((env.tys c.discr).getD .objPtr) .i1
            evalStep fuel ctx env st (.inr (v, isBool, 0, none, ordered))
      | .return x =>
        match env.vals x with | some v => .ok (v, st) | none => .error (.unboundVar 0)
      | .unreach _ => .error (.typeError "reached unreachable code")
      | .jp decl k =>
        if hasJmpToPure fuel decl.fvarId (.inl decl.value) then
          .error (.unsupportedCall "recursive join point")
        else
          let env' := env.bindJp decl.fvarId { params := decl.params.toList, code := decl.value }
          evalStep fuel ctx env' st (.inl k)
      | .jmp fvarId args =>
        match env.jps fvarId with
        | none => .error (.unsupportedCall "unmapped join point")
        | some body =>
          match evalJpArgs env.vals args.toList with
          | .error e => .error e
          | .ok vs =>
            match bindJpParams ctx env.tys env body.params args.toList vs with
            | .ok env' => evalStep fuel ctx env' st (.inl body.code)
            | .error e => .error e
      | .fun decl _ _ => .error (.unsupportedCall s!"local function {decl.binderName}")

def evalRealLCNFCode (fuel : Nat) (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
    (code : Lean.Compiler.LCNF.Code .impure) : Except UBError (Val × HeapState) :=
  evalStep fuel ctx env st (.inl code)

def evalRealLCNFDecl (fuel : Nat) (ctx : RealBridgeCtx)
    (decl : Lean.Compiler.LCNF.Decl .impure) (args : List Val)
    (st : HeapState := HeapState.empty) : Except UBError (Val × HeapState) :=
  match decl.value with
  | .extern _ => .error (.unsupportedCall s!"extern {decl.name}")
  | .code c =>
    match bindParams ctx true LEnv.empty decl.params.toList args with
    | .ok env => evalRealLCNFCode fuel ctx env st c
    | .error e => .error e

end LeanNative.IR.RealLCNFSemantics
