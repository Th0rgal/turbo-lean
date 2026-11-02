import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.ToImpureType
import LeanNative.IR.Types
import LeanNative.IR.AST

namespace LeanNative.IR.RealLCNFBridge

open LeanNative.IR

/-!
# Pure Deterministic `Lean.Compiler.LCNF → LNIR` Lowering Core (`RealLCNFBridge.lean`)

Track C4: Factors the deterministic, effect-free core of `Bridge.lean` / `BridgeHelpers.lean`
directly over real upstream `Lean.Compiler.LCNF` ASTs (`LitValue`, `Arg`, `LetValue`, `Alt`,
`Code`, `Decl`). Production `Bridge.lean` and `BridgeHelpers.lean` call these functions directly
(zero model-code gap), and `RealLCNFBridgeProofs.lean` proves end-to-end semantic refinement
against the independent `RealLCNFSemantics` evaluator and `LeanNative.Semantics.evalCode`.

Every recursive definition is a single `def` with an explicit `fuel : Nat` parameter (zero `partial`,
zero mutual well-founded `_mutual`, zero nested `where` / `let rec` recursion).
-/

/-- Canonical `Lean.Name` lookup table with explicit operand width (`LNIRType`).
    Runtime `Nat` is excluded so unbounded integer operations fail closed. -/
def canonicalScalarBinOpTypedTable : List (Lean.Name × LNIRType × BinOp) := [
  (``UInt64.add, .i64, .add), (``UInt64.sub, .i64, .sub), (``UInt64.mul, .i64, .mul), (``UInt64.div, .i64, .div), (``UInt64.mod, .i64, .mod),
  (``UInt64.land, .i64, .bitAnd), (``UInt64.lor, .i64, .bitOr), (``UInt64.xor, .i64, .bitXor), (``UInt64.shiftLeft, .i64, .shl), (``UInt64.shiftRight, .i64, .shr),
  (``UInt64.decEq, .i64, .eq), (`UInt64.beq, .i64, .eq), (``UInt64.decLt, .i64, .lt), (`UInt64.blt, .i64, .lt), (``UInt64.decLe, .i64, .le), (`UInt64.ble, .i64, .le),
  (``UInt32.add, .i32, .add), (``UInt32.sub, .i32, .sub), (``UInt32.mul, .i32, .mul), (``UInt32.div, .i32, .div), (``UInt32.mod, .i32, .mod),
  (``UInt32.land, .i32, .bitAnd), (``UInt32.lor, .i32, .bitOr), (``UInt32.xor, .i32, .bitXor), (``UInt32.shiftLeft, .i32, .shl), (``UInt32.shiftRight, .i32, .shr),
  (``UInt32.decEq, .i32, .eq), (`UInt32.beq, .i32, .eq), (``UInt32.decLt, .i32, .lt), (`UInt32.blt, .i32, .lt), (``UInt32.decLe, .i32, .le), (`UInt32.ble, .i32, .le),
  (``UInt16.add, .i16, .add), (``UInt16.sub, .i16, .sub), (``UInt16.mul, .i16, .mul), (``UInt16.div, .i16, .div), (``UInt16.mod, .i16, .mod),
  (``UInt16.land, .i16, .bitAnd), (``UInt16.lor, .i16, .bitOr), (``UInt16.xor, .i16, .bitXor), (``UInt16.shiftLeft, .i16, .shl), (``UInt16.shiftRight, .i16, .shr),
  (``UInt16.decEq, .i16, .eq), (`UInt16.beq, .i16, .eq), (``UInt16.decLt, .i16, .lt), (`UInt16.blt, .i16, .lt), (``UInt16.decLe, .i16, .le), (`UInt16.ble, .i16, .le),
  (``UInt8.add, .i8, .add), (``UInt8.sub, .i8, .sub), (``UInt8.mul, .i8, .mul), (``UInt8.div, .i8, .div), (``UInt8.mod, .i8, .mod),
  (``UInt8.land, .i8, .bitAnd), (``UInt8.lor, .i8, .bitOr), (``UInt8.xor, .i8, .bitXor), (``UInt8.shiftLeft, .i8, .shl), (``UInt8.shiftRight, .i8, .shr),
  (``UInt8.decEq, .i8, .eq), (`UInt8.beq, .i8, .eq), (``UInt8.decLt, .i8, .lt), (`UInt8.blt, .i8, .lt), (``UInt8.decLe, .i8, .le), (`UInt8.ble, .i8, .le),
  (``USize.add, .usize, .add), (``USize.sub, .usize, .sub), (``USize.mul, .usize, .mul), (``USize.div, .usize, .div), (``USize.mod, .usize, .mod),
  (``USize.land, .usize, .bitAnd), (``USize.lor, .usize, .bitOr), (``USize.xor, .usize, .bitXor), (``USize.shiftLeft, .usize, .shl), (``USize.shiftRight, .usize, .shr),
  (``USize.decEq, .usize, .eq), (`USize.beq, .usize, .eq), (``USize.decLt, .usize, .lt), (`USize.blt, .usize, .lt), (``USize.decLe, .usize, .le), (`USize.ble, .usize, .le)
]

def canonicalScalarBinOpTable : List (Lean.Name × BinOp) :=
  canonicalScalarBinOpTypedTable.map fun (n, _, op) => (n, op)

def lookupCanonicalTypedBinOp? (fnName : Lean.Name) : Option (LNIRType × BinOp) :=
  (canonicalScalarBinOpTypedTable.find? (fun (n, _, _) => n == fnName)).map Prod.snd

def lookupCanonicalBinOp? (fnName : Lean.Name) : Option BinOp :=
  (lookupCanonicalTypedBinOp? fnName).map Prod.snd

def archSupportsUSize (arch : TargetArch) : Bool :=
  match arch with
  | .nvptx64 | .hybridCpuGpu => false
  | _ => true

def archUSizeMask (arch : TargetArch) : UInt64 :=
  match arch with
  | .wasm32 => 0xFFFFFFFF
  | _ => 0xFFFFFFFFFFFFFFFF

def archUSizeShiftMask (arch : TargetArch) : UInt64 :=
  match arch with
  | .wasm32 => 31
  | _ => 63

def scalarWidthMask? (ty : LNIRType) (arch : TargetArch := .x86_64) : Option UInt64 :=
  match ty with
  | .i8 => some 0xFF
  | .i16 => some 0xFFFF
  | .i32 => some 0xFFFFFFFF
  | .i64 => some 0xFFFFFFFFFFFFFFFF
  | .usize => if archSupportsUSize arch then some (archUSizeMask arch) else none
  | _ => none

def scalarShiftMask? (ty : LNIRType) (arch : TargetArch := .x86_64) : Option UInt64 :=
  match ty with
  | .i8 => some 7
  | .i16 => some 15
  | .i32 => some 31
  | .i64 => some 63
  | .usize => if archSupportsUSize arch then some (archUSizeShiftMask arch) else none
  | _ => none

def isSupportedStage1BScalarType (ty : LNIRType) (arch : TargetArch) : Bool :=
  match ty with
  | .i1 | .i8 | .i16 | .i32 | .i64 | .unit => true
  | .usize => archSupportsUSize arch
  | _ => false

def isFlatUnboxedScalar : LNIRType → Bool
  | .i1 | .i8 | .i16 | .i32 | .i64 | .usize | .u256 | .i256 => true
  | _ => false

def isUnboxedScalarOrTuple : LNIRType → Bool
  | .tuple fs => !fs.isEmpty && fs.all isFlatUnboxedScalar
  | ty => isFlatUnboxedScalar ty

def isSupportedStage1BScalarOrTuple (ty : LNIRType) (arch : TargetArch) : Bool :=
  if isSupportedStage1BScalarType ty arch then true
  else match ty with
    | .tuple fs => !fs.isEmpty && fs.length ≤ 8 && fs.all (isSupportedStage1BScalarType · arch)
    | _ => false

/-- Exact primitive names and types only: unsigned narrowing truncates low bits;
    widening masks by `min srcMask dstMask` to clamp any unmasked i64 representation. -/
def canonicalUIntCastMask? (fnName : Lean.Name) (argTys : List LNIRType) (retTy : LNIRType)
    (arch : TargetArch := .x86_64) : Option UInt64 := do
  let usizeEntry : List (Lean.Name × LNIRType × UInt64) :=
    if archSupportsUSize arch then [(``USize, .usize, archUSizeMask arch)] else []
  let types : List (Lean.Name × LNIRType × UInt64) :=
    [(``UInt8, .i8, 255), (``UInt16, .i16, 65535),
     (``UInt32, .i32, 4294967295), (``UInt64, .i64, 18446744073709551615)] ++ usizeEntry
  types.findSome? fun (src, srcTy, srcMask) => types.findSome? fun (dst, dstTy, dstMask) =>
    if src != dst && fnName == Lean.Name.str src ("to" ++ dst.toString) &&
        argTys == [srcTy] && retTy == dstTy then
      some (min srcMask dstMask)
    else none

/-- Lower a canonical binary scalar primitive to a pure width-masked `ScalarExpr`. -/
def lowerScalarIntrinsicExpr? (op : BinOp) (lhs rhs : VarId) (operandTy retTy : LNIRType)
    (arch : TargetArch) : Option ScalarExpr := do
  if (operandTy == .usize || retTy == .usize) && !archSupportsUSize arch then none else
  let wrapBool (cmp : ScalarExpr) : Option ScalarExpr :=
    if retTy == .i8 then some (.select cmp (.constU64 1) (.constU64 0))
    else if retTy == .i1 then some cmp
    else none
  if operandTy == .i1 then
    let bL : ScalarExpr := .var lhs
    let bR : ScalarExpr := .var rhs
    match op with
    | .bitAnd => wrapBool (.select bL bR (.constBool false))
    | .bitOr  => wrapBool (.select bL (.constBool true) bR)
    | .bitXor => wrapBool (.unaryOp .not (.binOp .eq bL bR))
    | .eq     => wrapBool (.binOp .eq bL bR)
    | _       => none
  else
    let mask ← scalarWidthMask? operandTy arch
    let sMask ← scalarShiftMask? operandTy arch
    let lMasked : ScalarExpr := if mask == 0xFFFFFFFFFFFFFFFF then .var lhs else .binOp .bitAnd (.var lhs) (.constU64 mask)
    let rMasked : ScalarExpr := if mask == 0xFFFFFFFFFFFFFFFF then .var rhs else .binOp .bitAnd (.var rhs) (.constU64 mask)
    match op with
    | .add | .sub | .mul =>
      if retTy != operandTy then none
      else
        let raw := ScalarExpr.binOp op lMasked rMasked
        some (if mask == 0xFFFFFFFFFFFFFFFF then raw else .binOp .bitAnd raw (.constU64 mask))
    | .div =>
      if retTy != operandTy then none
      else some (.select (.binOp .eq rMasked (.constU64 0)) (.constU64 0) (.binOp .div lMasked rMasked))
    | .mod =>
      if retTy != operandTy then none
      else some (.select (.binOp .eq rMasked (.constU64 0)) lMasked (.binOp .mod lMasked rMasked))
    | .bitAnd | .bitOr | .bitXor =>
      if retTy != operandTy then none
      else
        let raw := ScalarExpr.binOp op lMasked rMasked
        some (if mask == 0xFFFFFFFFFFFFFFFF then raw else .binOp .bitAnd raw (.constU64 mask))
    | .shl =>
      if retTy != operandTy then none
      else
        let shAmt : ScalarExpr := if sMask == 63 then rMasked else .binOp .bitAnd rMasked (.constU64 sMask)
        let raw := ScalarExpr.binOp .shl lMasked shAmt
        some (if mask == 0xFFFFFFFFFFFFFFFF then raw else .binOp .bitAnd raw (.constU64 mask))
    | .shr =>
      if retTy != operandTy then none
      else
        let shAmt : ScalarExpr := if sMask == 63 then rMasked else .binOp .bitAnd rMasked (.constU64 sMask)
        some (.binOp .shr lMasked shAmt)
    | .eq | .lt | .le =>
      wrapBool (.binOp op lMasked rMasked)
    | _ => none

/-- Lower a canonical boolean binary primitive (`Bool.and`, `Bool.or`, `Bool.xor`, `Bool.beq`, `Bool.bne`, `bne`). -/
def lowerBoolBinIntrinsic? (fnName : Lean.Name) (lhs rhs : VarId) (argTys : List LNIRType)
    (retTy : LNIRType) : Option LNIRExpr := do
  let toCond (v : VarId) (t : LNIRType) : Option ScalarExpr :=
    if t == .i1 then some (.var v)
    else if t == .i8 then some (.unaryOp .not (.binOp .eq (.binOp .bitAnd (.var v) (.constU64 1)) (.constU64 0)))
    else none
  let wrapOut (bExpr : ScalarExpr) : Option LNIRExpr :=
    if retTy == .i1 then some (.scalar bExpr)
    else if retTy == .i8 then some (.scalar (.select bExpr (.constU64 1) (.constU64 0)))
    else none
  let [tL, tR] := argTys | none
  let cL ← toCond lhs tL
  let cR ← toCond rhs tR
  if fnName == ``Bool.and then wrapOut (.select cL cR (.constBool false))
  else if fnName == ``Bool.or then wrapOut (.select cL (.constBool true) cR)
  else if fnName == ``Bool.xor || fnName == `Bool.bne || fnName == `bne then wrapOut (.unaryOp .not (.binOp .eq cL cR))
  else if fnName == ``Bool.beq then wrapOut (.binOp .eq cL cR)
  else none

/-- Lower a canonical unary scalar/boolean primitive (`Bool.not`, `Bool.toUInt*`, `UInt*.complement`, `UInt*.neg`). -/
def lowerUnaryScalarIntrinsic? (fnName : Lean.Name) (arg : VarId) (argTys : List LNIRType)
    (retTy : LNIRType) (arch : TargetArch) : Option LNIRExpr := do
  let [srcTy] := argTys | none
  if fnName == ``Bool.not then
    if srcTy == .i1 && retTy == .i1 then
      return .scalar (.unaryOp .not (.var arg))
    else if srcTy == .i8 && retTy == .i8 then
      let isZero := ScalarExpr.binOp .eq (.binOp .bitAnd (.var arg) (.constU64 1)) (.constU64 0)
      return .scalar (.select isZero (.constU64 1) (.constU64 0))
    else none
  else if fnName == ``Bool.toUInt8 || fnName == ``Bool.toUInt16 ||
          fnName == ``Bool.toUInt32 || fnName == ``Bool.toUInt64 || fnName == ``Bool.toUSize then
    let expectedRet : LNIRType :=
      if fnName == ``Bool.toUInt8 then .i8
      else if fnName == ``Bool.toUInt16 then .i16
      else if fnName == ``Bool.toUInt32 then .i32
      else if fnName == ``Bool.toUInt64 then .i64
      else .usize
    guard ((srcTy == .i1 || srcTy == .i8) && retTy == expectedRet && isSupportedStage1BScalarType expectedRet arch)
    if srcTy == .i1 then
      return .scalar (.select (.var arg) (.constU64 1) (.constU64 0))
    else
      return .scalar (.binOp .bitAnd (.var arg) (.constU64 1))
  else
    let (expectedTy, isNeg) ←
      if fnName == ``UInt8.complement then some (LNIRType.i8, false)
      else if fnName == ``UInt16.complement then some (.i16, false)
      else if fnName == ``UInt32.complement then some (.i32, false)
      else if fnName == ``UInt64.complement then some (.i64, false)
      else if fnName == ``USize.complement then some (.usize, false)
      else if fnName == ``UInt8.neg then some (.i8, true)
      else if fnName == ``UInt16.neg then some (.i16, true)
      else if fnName == ``UInt32.neg then some (.i32, true)
      else if fnName == ``UInt64.neg then some (.i64, true)
      else if fnName == ``USize.neg then some (.usize, true)
      else none
    guard (srcTy == expectedTy && retTy == expectedTy)
    let mask ← scalarWidthMask? expectedTy arch
    let raw := if isNeg then ScalarExpr.binOp .sub (.constU64 0) (.var arg) else ScalarExpr.unaryOp .not (.var arg)
    return .scalar (if mask == 0xFFFFFFFFFFFFFFFF then raw else .binOp .bitAnd raw (.constU64 mask))

/-- Pure canonical intrinsic lowering (shared verbatim by `Bridge.tryLowerIntrinsicCall`). -/
def lowerCanonicalIntrinsicPure? (fnName : Lean.Name) (argVars : List VarId)
    (retTy : LNIRType) (argTys : List LNIRType := []) (isLocal : Bool := false)
    (arch : TargetArch := .x86_64) : Option LNIRExpr :=
  if isLocal then none
  else match argVars with
  | [lhs, rhs] =>
    match lookupCanonicalTypedBinOp? fnName with
    | some (opTy, op) =>
      if argTys != [opTy, opTy] then none
      else .scalar <$> lowerScalarIntrinsicExpr? op lhs rhs opTy retTy arch
    | none => lowerBoolBinIntrinsic? fnName lhs rhs argTys retTy
  | [arg] =>
    match canonicalUIntCastMask? fnName argTys retTy arch with
    | some effMask => some (.scalar (.binOp .bitAnd (.var arg) (.constU64 effMask)))
    | none => lowerUnaryScalarIntrinsic? fnName arg argTys retTy arch
  | _ => none

/-- Pure deterministic literal lowering (returns `Except String LNIRExpr` with exact production error messages). -/
def lowerLitValuePure (lit : Lean.Compiler.LCNF.LitValue) (retTy : LNIRType := .i64)
    (arch : TargetArch := .x86_64) (allowInternalObj : Bool := false) : Except String LNIRExpr := do
  if retTy == .usize && !archSupportsUSize arch then
    throw s!"[lean-native] Unsupported USize literal on target `{reprStr arch}`"
  let raw : UInt64 ← match lit with
    | .nat n =>
      if (retTy == .taggedPtr || retTy == .objPtr) && !allowInternalObj then
        throw "[lean-native] Unsupported runtime Nat literal"
      let m := (scalarWidthMask? retTy arch).getD 0xFFFFFFFFFFFFFFFF
      pure ((n % (2 ^ 64)).toUInt64 &&& m)
    | .uint8 v => pure v.toUInt64
    | .uint16 v => pure v.toUInt64
    | .uint32 v => pure v.toUInt64
    | .uint64 v => pure v
    | .usize v =>
      if !archSupportsUSize arch then
        throw s!"[lean-native] Unsupported USize literal on target `{reprStr arch}`"
      pure (v &&& archUSizeMask arch)
    | .str _ => throw "[lean-native] unsupported string literal"
  let masked := match scalarWidthMask? retTy arch with
    | some m => raw &&& m
    | none => raw
  if retTy == .i1 then
    return .scalar (.constBool (masked != 0))
  return .scalar (.constU64 masked)

/-- Pure tag-branch lowering (`Bool` swaps `cidx == 0` / `cidx == 1`; numeric tags emit `cmpVar := (condVar == cidx)`). -/
def lowerTagBranchPure (condVar : VarId) (condTy : LNIRType) (cidx : Nat) (isBool : Bool)
    (cmpVar : VarId) (yes no : LNIRCode) : LNIRCode × Bool :=
  if isBool || condTy == .i1 then
    (if cidx == 0 then .ite condVar no yes else if cidx == 1 then .ite condVar yes no else no, false)
  else
    (.letBind cmpVar .i1 (.scalar (.binOp .eq (.var condVar) (.constU64 cidx.toUInt64))) (.ite cmpVar yes no), true)

/-- Order `cases` alternatives so all constructor branches precede `.default`, matching Lean LCNF dispatch. -/
def orderAltsPure {pu} (alts : List (Lean.Compiler.LCNF.Alt pu)) : List (Lean.Compiler.LCNF.Alt pu) :=
  alts.filter (fun | .default _ => false | _ => true) ++ alts.filter (fun | .default _ => true | _ => false)

/-- Pure lowering of non-tuple atomic `Lean.Compiler.LCNF.ImpureType` and ground scalar `Lean.Expr` types. -/
def lowerAtomicImpureType (e : Lean.Expr) : LNIRType :=
  if e == Lean.Compiler.LCNF.ImpureType.uint8 then .i8
  else if e == Lean.Compiler.LCNF.ImpureType.uint16 then .i16
  else if e == Lean.Compiler.LCNF.ImpureType.uint32 then .i32
  else if e == Lean.Compiler.LCNF.ImpureType.uint64 then .i64
  else if e == Lean.Compiler.LCNF.ImpureType.usize then .usize
  else if e == Lean.Compiler.LCNF.ImpureType.float32 then .f32
  else if e == Lean.Compiler.LCNF.ImpureType.float then .f64
  else if e == Lean.Compiler.LCNF.ImpureType.object then .objPtr
  else if e == Lean.Compiler.LCNF.ImpureType.tagged || e == Lean.Compiler.LCNF.ImpureType.tobject then .taggedPtr
  else if e == Lean.Compiler.LCNF.ImpureType.erased || e == Lean.Compiler.LCNF.ImpureType.void then .unit
  else match e.getAppFn with
    | .const declName _ =>
      if declName == ``UInt8 then .i8
      else if declName == ``UInt16 then .i16
      else if declName == ``UInt32 then .i32
      else if declName == ``UInt64 then .i64
      else if declName == ``USize then .usize
      else if declName == ``Bool then .i1
      else if declName == ``Unit || declName == ``PUnit || declName == ``lcErased || declName == ``lcVoid then .unit
      else .objPtr
    | _ => .objPtr

/-- Pure lowering of standard `Lean.Compiler.LCNF.ImpureType` and ground scalar/pair `Lean.Expr` types. -/
def lowerGroundImpureType (e : Lean.Expr) : LNIRType :=
  let t0 := lowerAtomicImpureType e
  if t0 != .objPtr || e == Lean.Compiler.LCNF.ImpureType.object then t0
  else match e.getAppFn with
    | .const declName _ =>
      if declName == ``Prod || declName == ``MProd || declName == ``PProd then
        match e.getAppArgs[0]?, e.getAppArgs[1]? with
        | some a, some b =>
          let ta := lowerAtomicImpureType a
          let tb := lowerAtomicImpureType b
          if isFlatUnboxedScalar ta && isFlatUnboxedScalar tb then .tuple [ta, tb] else .objPtr
        | _, _ => .objPtr
      else .objPtr
    | _ => .objPtr

/-- HEAPOBJ_CONTRACT C1.2 constructor layout specification (shared between `RealLCNFBridge` and `BridgeHelpers`). -/
structure RcCtorLayoutSpec where
  ctorName    : Lean.Name := .anonymous
  cidx        : Nat := 0
  objSlots    : Nat := 0
  usizeSlots  : Nat := 0
  scalarSlots : List (Option Nat × LNIRType) := []
  deriving Inhabited, BEq, Repr

/-- `uproj i` / `uset i`: `usize` slot `i - objSlots` (C1.2: `lean_ctor_get_usize(o, n + k)`). -/
def RcCtorLayoutSpec.usizeSlot? (spec : RcCtorLayoutSpec) (i : Nat) : Option (Nat × LNIRType) :=
  if spec.objSlots ≤ i && i - spec.objSlots < spec.usizeSlots then some (i - spec.objSlots, .usize) else none

/-- `sproj n off` / `sset n off`: scalar slot at byte offset `off` (C1.2: requires `n = objSlots + usizeSlots`). -/
def RcCtorLayoutSpec.scalarSlot? (spec : RcCtorLayoutSpec) (n off : Nat) : Option (Nat × LNIRType) :=
  if n != spec.objSlots + spec.usizeSlots then none
  else (spec.scalarSlots.zipIdx.find? (·.1.1 == some off)).map fun ((_, ty), i) => (i, ty)

/-- Pure read-only lowering context over real `Lean.Compiler.LCNF` declarations. -/
structure RealBridgeCtx where
  arch             : TargetArch := .x86_64
  allowStage1DHeap : Bool := false
  ctorLayouts      : List (Lean.Name × RcCtorLayoutSpec) := []
  nullaryCtors     : List (Lean.Name × Nat) := []
  tupleStructCtors : List (Lean.Name × Nat) := []
  deriving Inhabited

def RealBridgeCtx.findLayout? (ctx : RealBridgeCtx) (ctorName : Lean.Name) : Option RcCtorLayoutSpec :=
  (ctx.ctorLayouts.find? (fun (n, _) => n == ctorName)).map Prod.snd

def RealBridgeCtx.findNullaryCtor? (ctx : RealBridgeCtx) (ctorName : Lean.Name) : Option Nat :=
  (ctx.nullaryCtors.find? (fun (n, _) => n == ctorName)).map Prod.snd

def RealBridgeCtx.findTupleArity? (ctx : RealBridgeCtx) (ctorName : Lean.Name) : Option Nat :=
  if ctorName == ``Prod.mk || ctorName == ``MProd.mk || ctorName == ``PProd.mk then some 2
  else (ctx.tupleStructCtors.find? (fun (n, _) => n == ctorName)).map Prod.snd

/-- Pure deterministic state for lowering real `Lean.Compiler.LCNF.Code .impure` to `LNIRCode`.
    Uses association lists so proofs over variable interning and fresh SSA allocation are elementary. -/
structure RealBridgeState where
  fvarMap    : List (Lean.FVarId × VarId) := []
  varTypes   : List (VarId × LNIRType) := []
  activeCtor : List (VarId × Lean.Name) := []
  jpDecls    : List (Lean.FVarId × List (Lean.Compiler.LCNF.Param .impure) × Lean.Compiler.LCNF.Code .impure) := []
  nextVarId  : VarId := 0
  deriving Inhabited

namespace RealBridgeState

def lookupFVar? (st : RealBridgeState) (fvarId : Lean.FVarId) : Option VarId :=
  (st.fvarMap.find? (fun (f, _) => f == fvarId)).map Prod.snd

def lookupJp? (st : RealBridgeState) (fvarId : Lean.FVarId) :
    Option (List (Lean.Compiler.LCNF.Param .impure) × Lean.Compiler.LCNF.Code .impure) :=
  (st.jpDecls.find? (fun (f, _, _) => f == fvarId)).map Prod.snd

def getVarType (st : RealBridgeState) (vid : VarId) : LNIRType :=
  match st.varTypes.find? (fun (v, _) => v == vid) with
  | some (_, ty) => ty
  | none => .objPtr

def getActiveCtor? (st : RealBridgeState) (vid : VarId) : Option Lean.Name :=
  (st.activeCtor.find? (fun (v, _) => v == vid)).map Prod.snd

def setVarType (st : RealBridgeState) (vid : VarId) (ty : LNIRType) : RealBridgeState :=
  { st with varTypes := (vid, ty) :: st.varTypes.filter (fun (v, _) => v != vid) }

def setActiveCtor (st : RealBridgeState) (vid : VarId) (ctorName : Lean.Name) : RealBridgeState :=
  { st with activeCtor := (vid, ctorName) :: st.activeCtor.filter (fun (v, _) => v != vid) }

def setJpDecl (st : RealBridgeState) (fvarId : Lean.FVarId)
    (params : List (Lean.Compiler.LCNF.Param .impure)) (code : Lean.Compiler.LCNF.Code .impure) :
    RealBridgeState :=
  { st with jpDecls := (fvarId, params, code) :: st.jpDecls.filter (fun (f, _, _) => f != fvarId) }

def freshVar (st : RealBridgeState) (ty : LNIRType) : VarId × RealBridgeState :=
  let vid := st.nextVarId
  (vid, { (st.setVarType vid ty) with nextVarId := vid + 1 })

def internFVar (st : RealBridgeState) (fvarId : Lean.FVarId) (ty : LNIRType := .objPtr)
    (authoritative : Bool := false) : VarId × RealBridgeState :=
  match st.lookupFVar? fvarId with
  | some vid => (vid, if authoritative then st.setVarType vid ty else st)
  | none =>
    let vid := st.nextVarId
    (vid, { (st.setVarType vid ty) with
      fvarMap := (fvarId, vid) :: st.fvarMap
      nextVarId := vid + 1 })

end RealBridgeState

/-- Lower one `Lean.Compiler.LCNF.Arg .impure` in pure `RealBridgeState`. -/
def lowerRealArg (ctx : RealBridgeCtx) (st : RealBridgeState) (arg : Lean.Compiler.LCNF.Arg .impure)
    (allowInternalObj : Bool := false) : Except String (VarId × RealBridgeState) :=
  match arg with
  | .fvar fvarId =>
    match st.lookupFVar? fvarId with
    | none => .error s!"[lean-native] unbound LCNF free variable `{fvarId.name}`"
    | some vid =>
      let vTy := st.getVarType vid
      if isSupportedStage1BScalarOrTuple vTy ctx.arch || (allowInternalObj && (vTy == .objPtr || vTy == .taggedPtr)) then
        .ok (vid, st)
      else
        .error s!"[lean-native] Unsupported non-scalar argument of type `{reprStr vTy}`"
  | .erased | .type .. => .error "[lean-native] unsupported erased runtime argument in pure core"

/-- Lower a list of `Lean.Compiler.LCNF.Arg .impure` left-to-right. -/
def lowerRealArgList (ctx : RealBridgeCtx) (st : RealBridgeState) (allowInternalObj : Bool) :
    List (Lean.Compiler.LCNF.Arg .impure) → Except String (List VarId × RealBridgeState)
  | [] => .ok ([], st)
  | a :: rest => do
    let (v, st1) ← lowerRealArg ctx st a allowInternalObj
    let (vs, st2) ← lowerRealArgList ctx st1 allowInternalObj rest
    return (v :: vs, st2)

/-- Pure constructor lowering over real `Lean.Compiler.LCNF.CtorInfo` and `Arg .impure`. -/
def lowerRealCtor (ctx : RealBridgeCtx) (st : RealBridgeState) (ctorName : Lean.Name) (cidx : Nat)
    (args : List (Lean.Compiler.LCNF.Arg .impure)) (retTy : LNIRType) :
    Except String (LNIRExpr × RealBridgeState) := do
  if args.isEmpty then
    if ctorName == ``Bool.false then
      return (.scalar (if retTy == .i1 then .constBool false else .constU64 0), st)
    if ctorName == ``Bool.true then
      return (.scalar (if retTy == .i1 then .constBool true else .constU64 1), st)
    if ctorName == ``Unit.unit || ctorName == ``PUnit.unit then
      return (.scalar (.constU64 0), st)
    match ctx.findNullaryCtor? ctorName with
    | some _ =>
      if retTy == .i8 || retTy == .i16 || retTy == .i1 ||
          (ctx.allowStage1DHeap && (retTy == .objPtr || retTy == .taggedPtr)) then
        return (.scalar (if retTy == .i1 then .constBool (cidx != 0) else .constU64 cidx.toUInt64), st)
      throw s!"[lean-native] Unsupported constructor `{ctorName}`"
    | none => throw s!"[lean-native] Unknown constructor `{ctorName}`"
  if ctx.allowStage1DHeap then
    if let some spec := ctx.findLayout? ctorName then
      if !spec.scalarSlots.isEmpty then
        throw s!"[lean-native] Unsupported scalar-slot constructor `{ctorName}` outside the impure layout lowering"
      let dropCnt := if args.length > spec.objSlots then args.length - spec.objSlots else 0
      let (argVars, st1) ← lowerRealArgList ctx st true (args.drop dropCnt)
      let argTys := argVars.map st1.getVarType
      if !argVars.isEmpty && argTys.all (fun t => isSupportedStage1BScalarOrTuple t ctx.arch || t == .objPtr || t == .taggedPtr) then
        return (.allocCtor cidx argVars [], st1)
  match ctx.findTupleArity? ctorName with
  | some numFields =>
    let dropCnt := if args.length > numFields then args.length - numFields else 0
    let (argVars, st1) ← lowerRealArgList ctx st true (args.drop dropCnt)
    let argTys := argVars.map st1.getVarType
    if argVars.isEmpty || !(argTys.all fun t => isSupportedStage1BScalarType t ctx.arch || t == .objPtr || t == .taggedPtr) then
      throw s!"[lean-native] Unsupported non-scalar or nested tuple/constructor fields in `{ctorName}`"
    return (.mkTuple argVars, st1)
  | none =>
    throw s!"[lean-native] Unsupported payload-carrying constructor `{ctorName}` in Stage 1B"

/-- Pure lowering of real `Lean.Compiler.LCNF.LetValue .impure` to `LNIRExpr`. -/
def lowerImpureLetValuePure (ctx : RealBridgeCtx) (st : RealBridgeState)
    (lv : Lean.Compiler.LCNF.LetValue .impure) (retTy : LNIRType) :
    Except String (LNIRExpr × RealBridgeState) := do
  match lv with
  | .lit litVal =>
    let expr ← lowerLitValuePure litVal retTy ctx.arch true
    return (expr, st)
  | .erased => return (.scalar (.constU64 0), st)
  | .fvar fvarId args =>
    if !args.isEmpty then throw "[lean-native] unsupported higher-order fvar call"
    let (v, st1) := st.internFVar fvarId
    return (.scalar (.var v), st1)
  | .ctor ctorInfo args _ =>
    lowerRealCtor ctx st ctorInfo.name ctorInfo.cidx args.toList retTy
  | .reuse slotFVar ctorInfo _ args _ =>
    let (sv, st1) := st.internFVar slotFVar
    if isUnboxedScalarOrTuple (st1.getVarType sv) then
      lowerRealCtor ctx st1 ctorInfo.name ctorInfo.cidx args.toList retTy
    else
      throw "[lean-native] Unsupported legacy heap reuse instruction in Stage 1B"
  | .oproj idx fvarId _ =>
    let (v, st1) := st.internFVar fvarId
    match st1.getVarType v with
    | .tuple _ => return (.projTuple v idx, st1)
    | .objPtr | .taggedPtr => return (.ctorGetObj v idx, st1)
    | vt => throw s!"[lean-native] Unsupported projection on `{reprStr vt}` in Stage 1B"
  | .uproj idx fvarId _ =>
    let (v, st1) := st.internFVar fvarId
    match st1.getVarType v with
    | .tuple _ => return (.projTuple v idx, st1)
    | vt =>
      if !(ctx.allowStage1DHeap && (vt == .objPtr || vt == .taggedPtr)) then
        throw s!"[lean-native] Unsupported scalar projection on `{reprStr vt}` in Stage 1B"
      let some cname := st1.getActiveCtor? v
        | throw "[lean-native] Unsupported scalar projection: constructor of the heap object is not statically known (C1.2)"
      let some spec := ctx.findLayout? cname
        | throw s!"[lean-native] Unknown constructor layout `{cname}`"
      let some (slot, ty) := spec.usizeSlot? idx
        | throw s!"[lean-native] Unsupported scalar projection [{idx},0] of `{cname}`: no C1.2 slot"
      return (.ctorGetScalar v slot ty, st1)
  | .sproj n off fvarId _ =>
    let (v, st1) := st.internFVar fvarId
    match st1.getVarType v with
    | .tuple _ => return (.projTuple v off, st1)
    | vt =>
      if !(ctx.allowStage1DHeap && (vt == .objPtr || vt == .taggedPtr)) then
        throw s!"[lean-native] Unsupported scalar projection on `{reprStr vt}` in Stage 1B"
      let some cname := st1.getActiveCtor? v
        | throw "[lean-native] Unsupported scalar projection: constructor of the heap object is not statically known (C1.2)"
      let some spec := ctx.findLayout? cname
        | throw s!"[lean-native] Unknown constructor layout `{cname}`"
      let some (slot, ty) := spec.scalarSlot? n off
        | throw s!"[lean-native] Unsupported scalar projection [{n},{off}] of `{cname}`: no C1.2 slot"
      if retTy != ty then
        throw s!"[lean-native] Scalar projection type `{reprStr retTy}` ≠ slot type `{reprStr ty}` of `{cname}` (C1.2)"
      return (.ctorGetScalar v slot ty, st1)
  | .fap fnName args _ =>
    let (argVars, st1) ← lowerRealArgList ctx st false args.toList
    let argTys := argVars.map st1.getVarType
    match lowerCanonicalIntrinsicPure? fnName argVars retTy argTys false ctx.arch with
    | some intr => return (intr, st1)
    | none => throw s!"[lean-native] Unsupported external or non-scalar call `{fnName}` in Stage 1B"
  | .pap fnName _ _ =>
    throw s!"[lean-native] Unsupported partial application (`pap {fnName}`) in Stage 1B"
  | .box _ fvarId _ | .unbox fvarId _ =>
    let (v, st1) := st.internFVar fvarId
    let vt := st1.getVarType v
    if isUnboxedScalarOrTuple vt || vt == .objPtr || vt == .taggedPtr then
      return (.scalar (.var v), st1)
    else
      throw s!"[lean-native] Unsupported boxing/unboxing of `{reprStr vt}` in Stage 1B"
  | .isShared fvarId _ =>
    let (v, st1) := st.internFVar fvarId
    let vt := st1.getVarType v
    if isUnboxedScalarOrTuple vt then return (.scalar (.constBool true), st1)
    if ctx.allowStage1DHeap && (vt == .objPtr || vt == .taggedPtr) then return (.isExclusive v, st1)
    throw "[lean-native] internal bridge error: unintercepted isShared"
  | .reset _ fvarId _ =>
    let (v, st1) := st.internFVar fvarId
    if isUnboxedScalarOrTuple (st1.getVarType v) then return (.scalar (.var v), st1)
    throw "[lean-native] Unsupported heap reset instruction in Stage 1B"

/-- Pure type inference for a lowered impure right-hand side (`BridgeHelpers.inferImpureRhsType`). -/
def inferImpureRhsTypePure (st : RealBridgeState) (rhs : LNIRExpr) (declTy : LNIRType) (isBox : Bool) : LNIRType :=
  if isBox then
    match rhs with
    | .scalar (.var sv) =>
      let sty := st.getVarType sv
      if isUnboxedScalarOrTuple sty then sty else .i64
    | _ => .i64
  else match rhs with
    | .allocCtor .. => .objPtr
    | .isExclusive .. => .i1
    | .scalar (.var sv) =>
      let sty := st.getVarType sv
      if isUnboxedScalarOrTuple declTy then declTy
      else if isUnboxedScalarOrTuple sty then sty else declTy
    | .scalar _ => if isUnboxedScalarOrTuple declTy then declTy else .i64
    | .mkTuple argVars => .tuple (argVars.map st.getVarType)
    | .projTuple tv idx =>
      match st.getVarType tv with
      | .tuple fs => if isUnboxedScalarOrTuple declTy then declTy else fs[idx]?.getD .i64
      | _ => declTy
    | _ => declTy

/-- Pure reference-counting instruction lowering (`Code.inc` / `Code.dec`, shared with `BridgeHelpers.lowerRefOp`). -/
def lowerRefOpPure (isInc : Bool) (vid : VarId) (vt : LNIRType) (n : Nat) (kCode : LNIRCode) :
    Except String LNIRCode :=
  if isUnboxedScalarOrTuple vt then .ok kCode
  else if vt == .objPtr || vt == .taggedPtr then .ok (if isInc then .incRef vid n kCode else .decRef vid n kCode)
  else .error s!"[lean-native] Unsupported heap RC instruction on `{reprStr vt}` in Stage 1B"

/-- Fuel-bounded check whether `targetFVar` appears in a `Code.jmp` inside `code`/`alts`
    (detects recursive join points without `partial` or mutual well-founded recursion). -/
def hasJmpToPure (fuel : Nat) (targetFVar : Lean.FVarId)
    (target : Lean.Compiler.LCNF.Code .impure ⊕ List (Lean.Compiler.LCNF.Alt .impure)) : Bool :=
  match fuel with
  | 0 => true
  | fuel + 1 =>
    match target with
    | .inr [] => false
    | .inr (alt :: rest) =>
      hasJmpToPure fuel targetFVar (.inl alt.getCode) || hasJmpToPure fuel targetFVar (.inr rest)
    | .inl code =>
      match code with
      | .let _ k | .fun _ k _ | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _
      | .del _ k _ | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ | .setTag _ _ k _ =>
        hasJmpToPure fuel targetFVar (.inl k)
      | .jp d2 k2 =>
        hasJmpToPure fuel targetFVar (.inl d2.value) || hasJmpToPure fuel targetFVar (.inl k2)
      | .jmp fvarId _ => fvarId == targetFVar
      | .cases c => hasJmpToPure fuel targetFVar (.inr c.alts.toList)
      | .return _ | .unreach _ => false

/-- Allocate fresh SSA variables for a join-point call site, returning `(paramFVar, freshVid, pTy, argVid)` tuples. -/
def bindJpCallArgsPure (ctx : RealBridgeCtx) (st : RealBridgeState) :
    List (Lean.Compiler.LCNF.Param .impure) → List (Lean.Compiler.LCNF.Arg .impure) →
    Except String (List (Lean.FVarId × VarId × LNIRType × VarId) × RealBridgeState)
  | [], [] => .ok ([], st)
  | p :: ps, a :: as_ => do
    let pTy := lowerGroundImpureType p.type
    let (argVid, st1) ← lowerRealArg ctx st a true
    let (freshVid, st2) := st1.freshVar pTy
    let (rest, st3) ← bindJpCallArgsPure ctx st2 ps as_
    return ((p.fvarId, freshVid, pTy, argVid) :: rest, st3)
  | _, _ => .error "[lean-native] join point arity mismatch"

/-- Apply `(paramFVar ↦ freshVid)` overrides in `RealBridgeState.fvarMap`. -/
def applyJpParamMapPure (st : RealBridgeState) :
    List (Lean.FVarId × VarId × LNIRType × VarId) → RealBridgeState
  | [] => st
  | (fvarId, freshVid, _, _) :: rest =>
    let st1 := { st with fvarMap := (fvarId, freshVid) :: st.fvarMap.filter (fun (f, _) => f != fvarId) }
    applyJpParamMapPure st1 rest

/-- Prepend `let freshVid : pTy := argVid` bindings before a lowered join-point body. -/
def wrapJpCallBindsPure : List (Lean.FVarId × VarId × LNIRType × VarId) → LNIRCode → LNIRCode
  | [], body => body
  | (_, freshVid, pTy, argVid) :: rest, body =>
    .letBind freshVid pTy (.scalar (.var argVid)) (wrapJpCallBindsPure rest body)

/-- Single-`def` fuel-bounded lowering of real `Lean.Compiler.LCNF.Code .impure` and `Alt .impure` lists
    (mode `Sum`: `Sum.inl code` lowers a code block; `Sum.inr (condVar, isBool, idx, discr?, alts)` lowers
    ordered `cases` alternatives without mutual well-founded recursion). -/
def lowerImpureStepPure (fuel : Nat) (ctx : RealBridgeCtx) (st : RealBridgeState)
    (target : Lean.Compiler.LCNF.Code .impure ⊕
      (VarId × Bool × Nat × Option VarId × List (Lean.Compiler.LCNF.Alt .impure))) :
    Except String (LNIRCode × RealBridgeState) :=
  match fuel with
  | 0 => .error "[lean-native] lowering fuel exhausted"
  | fuel + 1 =>
    match target with
    | .inr (condVar, isBool, idx, discr?, alts) =>
      match alts with
      | [] => .ok (.unreachable, st)
      | [.alt ctorName params code _] =>
        if !params.isEmpty then .error s!"[lean-native] unsupported constructor payload pattern in {ctorName}"
        else lowerImpureStepPure fuel ctx st (.inl code)
      | [.ctorAlt info code _] =>
        let saved := st.activeCtor
        let stIn := match discr? with | some dv => st.setActiveCtor dv info.name | none => st
        match lowerImpureStepPure fuel ctx stIn (.inl code) with
        | .ok (c, stOut) => .ok (c, { stOut with activeCtor := saved })
        | .error e => .error e
      | [.default code] =>
        lowerImpureStepPure fuel ctx st (.inl code)
      | alt :: rest =>
        match alt with
        | .default code =>
          lowerImpureStepPure fuel ctx st (.inl code)
        | .ctorAlt info code _ => do
          let condTy := st.getVarType condVar
          let saved := st.activeCtor
          let stIn := match discr? with | some dv => st.setActiveCtor dv info.name | none => st
          let (yesCode, st1) ← lowerImpureStepPure fuel ctx stIn (.inl code)
          let st1Restored := { st1 with activeCtor := saved }
          let (noCode, st2) ← lowerImpureStepPure fuel ctx st1Restored (.inr (condVar, isBool, idx + 1, discr?, rest))
          if isBool || condTy == .i1 then
            let (branched, _) := lowerTagBranchPure condVar condTy info.cidx isBool 0 yesCode noCode
            return (branched, st2)
          else
            let (cmpVar, st3) := st2.freshVar .i1
            let (branched, _) := lowerTagBranchPure condVar condTy info.cidx isBool cmpVar yesCode noCode
            return (branched, st3)
        | .alt ctorName params code _ => do
          if !params.isEmpty then
            throw s!"[lean-native] unsupported constructor payload pattern in {ctorName}"
          let condTy := st.getVarType condVar
          let cidx := (ctx.findNullaryCtor? ctorName).getD idx
          let (yesCode, st1) ← lowerImpureStepPure fuel ctx st (.inl code)
          let (noCode, st2) ← lowerImpureStepPure fuel ctx st1 (.inr (condVar, isBool, idx + 1, discr?, rest))
          if isBool || condTy == .i1 then
            let (branched, _) := lowerTagBranchPure condVar condTy cidx isBool 0 yesCode noCode
            return (branched, st2)
          else
            let (cmpVar, st3) := st2.freshVar .i1
            let (branched, _) := lowerTagBranchPure condVar condTy cidx isBool cmpVar yesCode noCode
            return (branched, st3)
    | .inl code =>
      match code with
      | .let decl k => do
        let rawDeclTy := lowerGroundImpureType decl.type
        let (rhs, st1) ← lowerImpureLetValuePure ctx st decl.value rawDeclTy
        let isBox := match decl.value with | .box _ _ _ => true | _ => false
        let ty := inferImpureRhsTypePure st1 rhs rawDeclTy isBox
        let (dst, st2) := st1.internFVar decl.fvarId ty true
        let st2' := match decl.value with
          | .ctor info _ _ => if ty == .objPtr then st2.setActiveCtor dst info.name else st2
          | _ => st2
        match rhs with
        | .isExclusive _ =>
          let (exclVar, st3) := st2'.freshVar .i1
          let (kCode, st4) ← lowerImpureStepPure fuel ctx st3 (.inl k)
          return (.letBind exclVar .i1 rhs (.letBind dst .i1 (.scalar (.unaryOp .not (.var exclVar))) kCode), st4)
        | _ =>
          let (kCode, st3) ← lowerImpureStepPure fuel ctx st2' (.inl k)
          return (.letBind dst ty rhs kCode, st3)
      | .inc fvarId n _ _ k _ => do
        let (v, st1) := st.internFVar fvarId
        let vt := st1.getVarType v
        let (kCode, st2) ← lowerImpureStepPure fuel ctx st1 (.inl k)
        let code' ← lowerRefOpPure true v vt n kCode
        return (code', st2)
      | .dec fvarId n _ _ _ k _ => do
        let (v, st1) := st.internFVar fvarId
        let vt := st1.getVarType v
        let (kCode, st2) ← lowerImpureStepPure fuel ctx st1 (.inl k)
        let code' ← lowerRefOpPure false v vt n kCode
        return (code', st2)
      | .del fvarId k _ => do
        let (objVid, st1) := st.internFVar fvarId
        let vt := st1.getVarType objVid
        if ctx.allowStage1DHeap && (vt == .objPtr || vt == .taggedPtr) then
          let (unitVid, st2) := st1.freshVar .unit
          let (kCode, st3) ← lowerImpureStepPure fuel ctx st2 (.inl k)
          return (.letBind unitVid .unit (.call "lean_native_del_obj" [objVid] .unit false) kCode, st3)
        else
          let (kCode, st2) ← lowerImpureStepPure fuel ctx st1 (.inl k)
          let code' ← lowerRefOpPure false objVid vt 1 kCode
          return (code', st2)
      | .setTag fvarId cidx k _ => do
        let (objVid, st1) := st.internFVar fvarId
        let vt := st1.getVarType objVid
        if !(ctx.allowStage1DHeap && (vt == .objPtr || vt == .taggedPtr)) then
          throw "[lean-native] unsupported constructor tag mutation"
        let (tagVid, st2) := st1.freshVar .i64
        let (unitVid, st3) := st2.freshVar .unit
        let (kCode, st4) ← lowerImpureStepPure fuel ctx st3 (.inl k)
        return (.letBind tagVid .i64 (.scalar (.constU64 cidx.toUInt64))
          (.letBind unitVid .unit (.call "lean_native_ctor_set_tag" [objVid, tagVid] .unit false) kCode), st4)
      | .oset fvarId idx y k _ => do
        let (objVid, st1) := st.internFVar fvarId
        let objTy := st1.getVarType objVid
        if ctx.allowStage1DHeap && (objTy == .objPtr || objTy == .taggedPtr) then
          let (valVid, st2) ← lowerRealArg ctx st1 y true
          let (idxVid, st3) := st2.freshVar .i64
          let (unitVid, st4) := st3.freshVar .unit
          let (kCode, st5) ← lowerImpureStepPure fuel ctx st4 (.inl k)
          return (.letBind idxVid .i64 (.scalar (.constU64 idx.toUInt64))
            (.letBind unitVid .unit (.call "lean_native_ctor_set" [objVid, idxVid, valVid] .unit false) kCode), st5)
        else if isUnboxedScalarOrTuple objTy then
          lowerImpureStepPure fuel ctx st1 (.inl k)
        else
          throw "[lean-native] Unsupported heap field mutation in Stage 1B"
      | .uset fvarId i y k _ => do
        let (objVid, st1) := st.internFVar fvarId
        let objTy := st1.getVarType objVid
        if isUnboxedScalarOrTuple objTy || !ctx.allowStage1DHeap || !(objTy == .objPtr || objTy == .taggedPtr) then
          throw "[lean-native] Unsupported heap field mutation in Stage 1B"
        let some cname := st1.getActiveCtor? objVid
          | throw "[lean-native] Unsupported scalar field mutation: constructor of the heap object is not statically known (C1.2)"
        let some spec := ctx.findLayout? cname
          | throw s!"[lean-native] Unknown constructor layout `{cname}`"
        let some (slot, _) := spec.usizeSlot? i
          | throw s!"[lean-native] Unsupported scalar mutation [{i},0] of `{cname}`: no C1.2 slot"
        let (valVid, st2) := st1.internFVar y
        let (idxVid, st3) := st2.freshVar .i64
        let (unitVid, st4) := st3.freshVar .unit
        let (kCode, st5) ← lowerImpureStepPure fuel ctx st4 (.inl k)
        return (.letBind idxVid .i64 (.scalar (.constU64 slot.toUInt64))
          (.letBind unitVid .unit (.call "lean_native_ctor_set_scalar" [objVid, idxVid, valVid] .unit false) kCode), st5)
      | .sset fvarId n off y _ k _ => do
        let (objVid, st1) := st.internFVar fvarId
        let objTy := st1.getVarType objVid
        if isUnboxedScalarOrTuple objTy || !ctx.allowStage1DHeap || !(objTy == .objPtr || objTy == .taggedPtr) then
          throw "[lean-native] Unsupported heap field mutation in Stage 1B"
        let some cname := st1.getActiveCtor? objVid
          | throw "[lean-native] Unsupported scalar field mutation: constructor of the heap object is not statically known (C1.2)"
        let some spec := ctx.findLayout? cname
          | throw s!"[lean-native] Unknown constructor layout `{cname}`"
        let some (slot, _) := spec.scalarSlot? n off
          | throw s!"[lean-native] Unsupported scalar mutation [{n},{off}] of `{cname}`: no C1.2 slot"
        let (valVid, st2) := st1.internFVar y
        let (idxVid, st3) := st2.freshVar .i64
        let (unitVid, st4) := st3.freshVar .unit
        let (kCode, st5) ← lowerImpureStepPure fuel ctx st4 (.inl k)
        return (.letBind idxVid .i64 (.scalar (.constU64 slot.toUInt64))
          (.letBind unitVid .unit (.call "lean_native_ctor_set_scalar" [objVid, idxVid, valVid] .unit false) kCode), st5)
      | .cases c => do
        let (condVar, st1) := st.internFVar c.discr
        let condTy := st1.getVarType condVar
        let ordered := orderAltsPure c.alts.toList
        if ctx.allowStage1DHeap && c.typeName != ``Bool && (condTy == .objPtr || condTy == .taggedPtr) then
          let (tagVar, st2) := st1.freshVar .i64
          let (altsCode, st3) ← lowerImpureStepPure fuel ctx st2 (.inr (tagVar, false, 0, some condVar, ordered))
          return (.letBind tagVar .i64 (.call "lean_native_ctor_tag" [condVar] .i64 false) altsCode, st3)
        else if !isSupportedStage1BScalarType condTy ctx.arch then
          throw s!"[lean-native] Unsupported cases scrutinee type `{c.typeName}`"
        else
          lowerImpureStepPure fuel ctx st1 (.inr (condVar, c.typeName == ``Bool, 0, none, ordered))
      | .return fvarId =>
        let (v, st1) := st.internFVar fvarId
        .ok (.ret v, st1)
      | .unreach _ =>
        .ok (.unreachable, st)
      | .fun decl _ _ =>
        .error s!"[lean-native] Unsupported local function `{decl.binderName}` in pure core"
      | .jp decl k =>
        if hasJmpToPure fuel decl.fvarId (.inl decl.value) then
          .error s!"[lean-native] unsupported recursive join point `{decl.fvarId.name}`: no qualified loop lowering"
        else
          let stWithJp := st.setJpDecl decl.fvarId decl.params.toList decl.value
          lowerImpureStepPure fuel ctx stWithJp (.inl k)
      | .jmp fvarId args => do
        let some (jpParams, jpBody) := st.lookupJp? fvarId
          | throw s!"[lean-native] unsupported unmapped join point `{fvarId.name}`"
        let (binds, st1) ← bindJpCallArgsPure ctx st jpParams args.toList
        let savedFVars := st1.fvarMap
        let savedActive := st1.activeCtor
        let stIn := applyJpParamMapPure st1 binds
        let (bodyCode, stOut) ← lowerImpureStepPure fuel ctx stIn (.inl jpBody)
        return (wrapJpCallBindsPure binds bodyCode,
          { stOut with fvarMap := savedFVars, activeCtor := savedActive })

/-- Lower a real `Lean.Compiler.LCNF.Code .impure` block in pure `RealBridgeState`. -/
def lowerRealLCNFCode (fuel : Nat) (ctx : RealBridgeCtx) (st : RealBridgeState)
    (code : Lean.Compiler.LCNF.Code .impure) : Except String (LNIRCode × RealBridgeState) :=
  lowerImpureStepPure fuel ctx st (.inl code)

/-- Intern parameter list of a real `Lean.Compiler.LCNF.Decl .impure` left-to-right. -/
def internRealParams (st : RealBridgeState) :
    List (Lean.Compiler.LCNF.Param .impure) → List LNIRParam × RealBridgeState
  | [] => ([], st)
  | p :: ps =>
    let pTy := lowerGroundImpureType p.type
    let (vid, st1) := st.internFVar p.fvarId pTy true
    let param : LNIRParam := { id := vid, name := p.binderName.toString, ty := pTy, borrow := p.borrow }
    let (rest, st2) := internRealParams st1 ps
    (param :: rest, st2)

/-- Lower a real `Lean.Compiler.LCNF.Decl .impure` in pure `RealBridgeState` (`lowerRealDecl`). -/
def lowerRealLCNFDecl (fuel : Nat) (ctx : RealBridgeCtx) (decl : Lean.Compiler.LCNF.Decl .impure)
    (mangledName : String := decl.name.toString) : Except String LNIRDecl := do
  match decl.value with
  | .extern _ =>
    throw s!"[lean-native] Unsupported `@[extern]` declaration `{decl.name}` in Stage 1B"
  | .code c =>
    let (lnirParams, stParams) := internRealParams {} decl.params.toList
    let retTy := lowerGroundImpureType decl.type
    let (body, _) ← lowerRealLCNFCode fuel ctx stParams c
    return {
      name := mangledName
      params := lnirParams
      retTy := retTy
      body := body
      assurance := .tested
      isGpuCand := lnirParams.all (fun p => p.ty.isGpuCompatible) && retTy.isGpuCompatible
    }

end LeanNative.IR.RealLCNFBridge
