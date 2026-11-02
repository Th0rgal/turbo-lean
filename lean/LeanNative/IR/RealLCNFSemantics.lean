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
  ctors : Lean.FVarId → Option Lean.Name := fun _ => none
  jps   : Lean.FVarId → Option JpBody := fun _ => none
  deriving Inhabited

def LEnv.empty : LEnv := {}

def LEnv.bind (env : LEnv) (x : Lean.FVarId) (v : Val) (ctor? : Option Lean.Name := none) : LEnv :=
  { env with
    vals  := fun y => if y == x then some v else env.vals y
    ctors := fun y => if y == x then ctor? else env.ctors y }

def LEnv.withCtor (env : LEnv) (x : Lean.FVarId) (ctorName : Lean.Name) : LEnv :=
  { env with ctors := fun y => if y == x then some ctorName else env.ctors y }

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
  | .usize => if arch.isWasm then 32 else 64
  | _ => 64

def maskOf (arch : TargetArch) (ty : LNIRType) : BitVec 64 :=
  BitVec.ofNat 64 (2 ^ widthOf arch ty - 1)

def masked (arch : TargetArch) (ty : LNIRType) (w : BitVec 64) : BitVec 64 :=
  w &&& maskOf arch ty

def shiftMaskOf (arch : TargetArch) (ty : LNIRType) : BitVec 64 :=
  BitVec.ofNat 64 (widthOf arch ty - 1)

def wrapBoolOut (b : Bool) (retTy : LNIRType) : Except UBError Val :=
  if retTy == .i1 then .ok (.bool b)
  else if retTy == .i8 then .ok (.u64 (if b then 1 else 0))
  else .error (.typeError "comparison / boolean intrinsic expects i1 or i8 return type")

def wordBin (arch : TargetArch) (op : BinOp) (ty retTy : LNIRType) (va vb : Val) : Except UBError Val :=
  if ty == .i1 then
    let asBit : Val → Option Bool
      | .bool b => some b
      | .u64 n => some (n != 0)
      | _ => none
    match op, asBit va, asBit vb with
    | .bitAnd, some a, some b => wrapBoolOut (a && b) retTy
    | .bitOr,  some a, some b => wrapBoolOut (a || b) retTy
    | .bitXor, some a, some b => wrapBoolOut (a != b) retTy
    | .eq,     some a, some b => wrapBoolOut (a == b) retTy
    | _, _, _ => .error (.typeError "unsupported i1 scalar operator")
  else
    match va, vb with
    | .u64 na, .u64 nb =>
      let am := masked arch ty na.toBitVec
      let bm := masked arch ty nb.toBitVec
      match op with
      | .add => .ok (ofWord (masked arch ty (am + bm)))
      | .sub => .ok (ofWord (masked arch ty (am - bm)))
      | .mul => .ok (ofWord (masked arch ty (am * bm)))
      | .div => .ok (ofWord (if bm == 0#64 then 0#64 else masked arch ty (am / bm)))
      | .mod => .ok (ofWord (if bm == 0#64 then am else masked arch ty (am % bm)))
      | .bitAnd => .ok (ofWord (masked arch ty (am &&& bm)))
      | .bitOr  => .ok (ofWord (masked arch ty (am ||| bm)))
      | .bitXor => .ok (ofWord (masked arch ty (am ^^^ bm)))
      | .shl =>
        let sh := bm &&& shiftMaskOf arch ty
        .ok (ofWord (masked arch ty (am <<< sh)))
      | .shr =>
        let sh := bm &&& shiftMaskOf arch ty
        .ok (ofWord (am >>> sh))
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

def evalBoolBinCall? (fn : Lean.Name) (va vb : Val) (retTy : LNIRType) : Option (Except UBError Val) :=
  let evalOp (op : Bool → Bool → Bool) : Option (Except UBError Val) :=
    match boolBitOf va, boolBitOf vb with
    | some a, some b => some (wrapBoolOut (op a b) retTy)
    | _, _ => some (.error (.typeError "boolean intrinsic expects bool or i8-encoded bool"))
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
    some (.usize, if arch.isWasm then 0xFFFFFFFF#64 else 0xFFFFFFFFFFFFFFFF#64)
  else none

def evalUnaryOrCastCall? (arch : TargetArch) (fn : Lean.Name) (va : Val) (retTy : LNIRType) :
    Option (Except UBError Val) :=
  if fn == ``Bool.not then
    some <| match va, retTy with
      | .bool b, .i1 => .ok (.bool (!b))
      | .u64 n, .i8 => .ok (.u64 (if (n &&& 1) == 0 then 1 else 0))
      | _, _ => .error (.typeError "Bool.not expects matching i1 or i8 operand")
  else if fn == ``Bool.toUInt8 || fn == ``Bool.toUInt16 ||
          fn == ``Bool.toUInt32 || fn == ``Bool.toUInt64 || fn == ``Bool.toUSize then
    some <| match boolBitOf va with
      | some b => .ok (.u64 (if b then 1 else 0))
      | none => .error (.typeError "Bool.toUInt* expects bool or i8 operand")
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
      some <| match va with
        | .u64 n =>
          let w := n.toBitVec
          let raw := if isNeg then 0#64 - w else ~~~w
          .ok (ofWord (masked arch opTy raw))
        | _ => .error (.typeError "UInt unary intrinsic expects u64 word")
    | none =>
      let primNames : List Lean.Name := [``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize]
      primNames.findSome? fun src => primNames.findSome? fun dst =>
        if src != dst && fn == Lean.Name.str src ("to" ++ dst.toString) then
          match uintPrimMask? arch src, uintPrimMask? arch dst with
          | some (_, sm), some (dTy, dm) =>
            if retTy == dTy then
              some <| match va with
                | .u64 n => .ok (ofWord (n.toBitVec &&& (if sm.toNat ≤ dm.toNat then sm else dm)))
                | _ => .error (.typeError "UInt cast expects u64 word")
            else none
          | _, _ => none
        else none

def asBool (v : Val) : Except UBError Bool :=
  match v with
  | .bool b => .ok b
  | .u64 n => .ok (n != 0)
  | _ => .error (.typeError "condition must be a scalar")

def evalLit (arch : TargetArch) (lit : Lean.Compiler.LCNF.LitValue) (ty : LNIRType) : Except UBError Val :=
  if ty == .usize && !archSupportsUSize arch then
    .error (.typeError "USize unsupported on target architecture")
  else
    let raw : Except UBError (BitVec 64) := match lit with
      | .nat n => .ok (BitVec.ofNat 64 (n % (2 ^ 64)))
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
      if ty == .i1 then .ok (.bool (w != 0#64)) else .ok (ofWord w)

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

def bindParams (env : LEnv) :
    List (Lean.Compiler.LCNF.Param .impure) → List Val → Except UBError LEnv
  | [], [] => .ok env
  | p :: ps, v :: vs => bindParams (env.bind p.fvarId v none) ps vs
  | _, _ => .error (.typeError "join point arity mismatch")

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
  | _ => .error (.typeError "tag expects heap object or unboxed tag")

def evalCtorVal (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
    (ctorName : Lean.Name) (cidx : Nat) (args : List (Lean.Compiler.LCNF.Arg .impure))
    (retTy : LNIRType) : Except UBError (Val × HeapState × Option Lean.Name) :=
  if args.isEmpty then
    if ctorName == ``Bool.false then
      .ok ((if retTy == .i1 then .bool false else .u64 0), st, none)
    else if ctorName == ``Bool.true then
      .ok ((if retTy == .i1 then .bool true else .u64 1), st, none)
    else if ctorName == ``Unit.unit || ctorName == ``PUnit.unit then
      .ok (.u64 0, st, none)
    else
      .ok ((if retTy == .i1 then .bool (cidx != 0) else .u64 (wordOf cidx)), st, none)
  else
    let heapSpec? :=
      if ctx.allowStage1DHeap then
        match ctx.findLayout? ctorName with
        | some spec => if spec.scalarSlots.isEmpty && spec.objSlots > 0 then some spec else none
        | none => none
      else none
    match heapSpec? with
    | some spec =>
      let dropCnt := if args.length > spec.objSlots then args.length - spec.objSlots else 0
      match evalArgs env.vals (args.drop dropCnt) with
      | .ok vs =>
        if !vs.all Val.wfField then
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

def evalLetValue (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
    (lv : Lean.Compiler.LCNF.LetValue .impure) (ty : LNIRType) :
    Except UBError (Val × HeapState × Option Lean.Name) :=
  match lv with
  | .lit lit => (evalLit ctx.arch lit ty).map (·, st, none)
  | .erased => .ok (.u64 0, st, none)
  | .fvar x args =>
    if !args.isEmpty then .error (.unsupportedCall "higher-order fvar")
    else match env.vals x with | some v => .ok (v, st, none) | none => .error (.unboundVar 0)
  | .ctor info args _ =>
    evalCtorVal ctx env st info.name info.cidx args.toList ty
  | .reuse _ info _ args _ =>
    evalCtorVal ctx env st info.name info.cidx args.toList ty
  | .oproj idx x _ =>
    match env.vals x with
    | some (.objPtr objId) =>
      (st.liveHeapObj objId).bind fun o => (fieldGet o.objFields idx).map (·, st, none)
    | some (.tuple vs) => (fieldGet vs idx).map (·, st, none)
    | some _ => .error (.typeError "object projection expects heap object or tuple")
    | none => .error (.unboundVar 0)
  | .uproj idx x _ =>
    match env.vals x with
    | some (.tuple vs) => (fieldGet vs idx).map (·, st, none)
    | some (.objPtr objId) =>
      match env.ctors x >>= ctx.findLayout? >>= (·.usizeSlot? idx) with
      | some (slot, _) =>
        (st.liveHeapObj objId).bind fun o => (fieldGet o.scalarFields slot).map (·, st, none)
      | none =>
        (st.liveHeapObj objId).bind fun o => (fieldGet o.scalarFields idx).map (·, st, none)
    | some _ => .error (.typeError "usize projection expects heap object or tuple")
    | none => .error (.unboundVar 0)
  | .sproj n off x _ =>
    match env.vals x with
    | some (.tuple vs) => (fieldGet vs off).map (·, st, none)
    | some (.objPtr objId) =>
      match env.ctors x >>= ctx.findLayout? >>= (·.scalarSlot? n off) with
      | some (slot, _) =>
        (st.liveHeapObj objId).bind fun o => (fieldGet o.scalarFields slot).map (·, st, none)
      | none =>
        (st.liveHeapObj objId).bind fun o => (fieldGet o.scalarFields off).map (·, st, none)
    | some _ => .error (.typeError "scalar projection expects heap object or tuple")
    | none => .error (.unboundVar 0)
  | .fap fn args _ =>
    match args.toList with
    | [a, b] =>
      match evalArg env.vals a, evalArg env.vals b with
      | .ok va, .ok vb =>
        match lookupCanonicalTypedBinOp? fn with
        | some (opTy, op) => (wordBin ctx.arch op opTy ty va vb).map (·, st, none)
        | none =>
          match evalBoolBinCall? fn va vb ty with
          | some r => r.map (·, st, none)
          | none => .error (.unsupportedCall fn.toString)
      | .error e, _ | _, .error e => .error e
    | [a] =>
      match evalArg env.vals a with
      | .ok va =>
        match evalUnaryOrCastCall? ctx.arch fn va ty with
        | some r => r.map (·, st, none)
        | none => .error (.unsupportedCall fn.toString)
      | .error e => .error e
    | _ => .error (.unsupportedCall fn.toString)
  | .isShared x _ =>
    match env.vals x with
    | some (.objPtr objId) =>
      let rc := st.getObjRefCount objId
      if rc == 0 then .error (.useAfterFree objId) else .ok (.bool (rc != 1), st, none)
    | some (.sarrayId bufId) =>
      match st.findBuffer bufId with
      | some buf => .ok (.bool (!buf.exclusive), st, none)
      | none => .error (.typeError s!"unknown sarray buffer {bufId}")
    | some _ => .ok (.bool true, st, none)
    | none => .error (.unboundVar 0)
  | .box _ x _ | .unbox x _ | .reset _ x _ =>
    match env.vals x with | some v => .ok (v, st, none) | none => .error (.unboundVar 0)
  | .pap fn _ _ => .error (.unsupportedCall s!"pap {fn}")

def applyRc (isInc : Bool) (env : Lean.FVarId → Option Val) (st : HeapState) (x : Lean.FVarId) (n : Nat) :
    Except UBError HeapState :=
  match env x with
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
      | [] => .error (.typeError "unreachable / uncovered cases")
      | [.alt _ _ code _] | [.default code] =>
        evalStep fuel ctx env st (.inl code)
      | [.ctorAlt info code _] =>
        let envIn := match discr? with | some dx => env.withCtor dx info.name | none => env
        evalStep fuel ctx envIn st (.inl code)
      | alt :: rest =>
        match alt with
        | .default code => evalStep fuel ctx env st (.inl code)
        | .ctorAlt info code _ =>
          let envIn := match discr? with | some dx => env.withCtor dx info.name | none => env
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
            | .bool b =>
              if (if b then (1 : UInt64) else 0) == info.cidx.toUInt64 then
                evalStep fuel ctx envIn st (.inl code)
              else evalStep fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
            | _ => .error (.typeError "case discriminant must be a scalar or tag")
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
            | .bool b =>
              if (if b then (1 : UInt64) else 0) == cidx.toUInt64 then
                evalStep fuel ctx env st (.inl code)
              else evalStep fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
            | _ => .error (.typeError "case discriminant must be a scalar or tag")
    | .inl code =>
      match code with
      | .let decl k =>
        let ty := lowerGroundImpureType decl.type
        match evalLetValue ctx env st decl.value ty with
        | .ok (v, st', ctor?) =>
          evalStep fuel ctx (env.bind decl.fvarId v ctor?) st' (.inl k)
        | .error e => .error e
      | .inc x n _ _ k _ =>
        match applyRc true env.vals st x n with
        | .ok st' => evalStep fuel ctx env st' (.inl k)
        | .error e => .error e
      | .dec x n _ _ _ k _ =>
        match applyRc false env.vals st x n with
        | .ok st' => evalStep fuel ctx env st' (.inl k)
        | .error e => .error e
      | .del x k _ =>
        match env.vals x with
        | some (.objPtr objId) =>
          let stepRes :=
            if ctx.allowStage1DHeap then st.delObjShell objId else st.decRefObj objId 1
          match stepRes with
          | .ok st' => evalStep fuel ctx env st' (.inl k)
          | .error e => .error e
        | some (.sarrayId bufId) =>
          match st.decRefBuf bufId 1 with
          | .ok st' => evalStep fuel ctx env st' (.inl k)
          | .error e => .error e
        | some _ => evalStep fuel ctx env st (.inl k)
        | none => .error (.unboundVar 0)
      | .setTag x cidx k _ =>
        match env.vals x with
        | some (.objPtr objId) =>
          match st.setHeapObjTagExclusive objId cidx with
          | .ok st' => evalStep fuel ctx env st' (.inl k)
          | .error e => .error e
        | none => .error (.unboundVar 0)
        | _ => .error (.typeError "setTag expects a heap object")
      | .oset x i y k _ =>
        match env.vals x with
        | some (.objPtr objId) =>
          match evalArg env.vals y with
          | .ok v =>
            match writeField st objId i v true with
            | .ok st' => evalStep fuel ctx env st' (.inl k)
            | .error e => .error e
          | .error e => .error e
        | none => .error (.unboundVar 0)
        | some _ => evalStep fuel ctx env st (.inl k)
      | .uset x i y k _ =>
        match env.vals x, env.vals y with
        | some (.objPtr objId), some v =>
          let slot := match env.ctors x >>= ctx.findLayout? >>= (·.usizeSlot? i) with
            | some (s, _) => s
            | none => i
          match writeField st objId slot v false with
          | .ok st' => evalStep fuel ctx env st' (.inl k)
          | .error e => .error e
        | none, _ | _, none => .error (.unboundVar 0)
        | _, _ => .error (.typeError "scalar mutation expects a heap object")
      | .sset x n off y _ k _ =>
        match env.vals x, env.vals y with
        | some (.objPtr objId), some v =>
          let slot := match env.ctors x >>= ctx.findLayout? >>= (·.scalarSlot? n off) with
            | some (s, _) => s
            | none => off
          match writeField st objId slot v false with
          | .ok st' => evalStep fuel ctx env st' (.inl k)
          | .error e => .error e
        | none, _ | _, none => .error (.unboundVar 0)
        | _, _ => .error (.typeError "scalar mutation expects a heap object")
      | .cases c =>
        match env.vals c.discr with
        | none => .error (.unboundVar 0)
        | some v =>
          let ordered := orderAltsPure c.alts.toList
          if ctx.allowStage1DHeap && c.typeName != ``Bool then
            match v with
            | .objPtr _ =>
              match tagOf v st with
              | .ok tag => evalStep fuel ctx env st (.inr (tag, false, 0, some c.discr, ordered))
              | .error e => .error e
            | _ =>
              let isBool := c.typeName == ``Bool || (match v with | .bool _ => true | _ => false)
              evalStep fuel ctx env st (.inr (v, isBool, 0, none, ordered))
          else
            let isBool := c.typeName == ``Bool || (match v with | .bool _ => true | _ => false)
            evalStep fuel ctx env st (.inr (v, isBool, 0, none, ordered))
      | .return x =>
        match env.vals x with | some v => .ok (v, st) | none => .error (.unboundVar 0)
      | .unreach _ => .error (.typeError "unreachable code reached")
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
          match evalArgs env.vals args.toList with
          | .error e => .error e
          | .ok vs =>
            match bindParams env body.params vs with
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
    match bindParams LEnv.empty decl.params.toList args with
    | .ok env => evalRealLCNFCode fuel ctx env st c
    | .error e => .error e

end LeanNative.IR.RealLCNFSemantics
