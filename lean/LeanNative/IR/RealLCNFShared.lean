import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.ToImpureType
import LeanNative.IR.Types
import LeanNative.IR.AST

namespace LeanNative.IR.RealLCNFBridge

open LeanNative.IR

/-!
# Shared `Lean.Compiler.LCNF` Bridge Definitions (`RealLCNFShared.lean`)

H1.1: the definitions shared between the lowerer (`RealLCNFBridge.lean`) and the independent
operational semantics (`RealLCNFSemantics.lean`), factored out so the semantics does not import
the lowering functions it is measured against: the canonical scalar-operator tables and lookups,
target-architecture width/mask helpers, `LNIRType` predicates and fuel-bounded structural
equality, `cases`-alternative ordering, ground impure type lowering, the HEAPOBJ_CONTRACT C1.2
constructor layout specification (`RcCtorLayoutSpec`), the read-only lowering/evaluation context
(`RealBridgeCtx`) with its lookups and `lowerParamType`, and the recursive-join-point detector
(`hasJmpToPure`). Declarations stay in the `LeanNative.IR.RealLCNFBridge` namespace, so every
existing fully-qualified name, `open`, and proof is unchanged.

No lowering function lives here: `lowerImpureStepPure`, `lowerRealLCNFCode`, and
`lowerRealLCNFDecl` remain in `RealLCNFBridge.lean`, which imports this file.
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
  if arch.isILP32 then 0xFFFFFFFF else 0xFFFFFFFFFFFFFFFF

def archUSizeShiftMask (arch : TargetArch) : UInt64 :=
  if arch.isILP32 then 31 else 63

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
  | .i1 | .i8 | .i16 | .i32 | .i64 | .usize | .u256 | .i256 | .f64 => true
  | _ => false

def isSupportedSliceType : LNIRType → Bool
  | .sarray .i8 | .sarray .f64 => true
  | _ => false

def isUnboxedScalarOrTuple : LNIRType → Bool
  | .tuple fs => !fs.isEmpty && fs.all isFlatUnboxedScalar
  | ty => isFlatUnboxedScalar ty

def isSupportedStage1BScalarOrTuple (ty : LNIRType) (arch : TargetArch) : Bool :=
  if isSupportedStage1BScalarType ty arch then true
  else match ty with
    | .tuple fs => !fs.isEmpty && fs.length ≤ 8 && fs.all (isSupportedStage1BScalarType · arch)
    | _ => false

/-- Kernel-reducible fuel-bounded structural equality on `LNIRType` (`instBEqLNIRType.beq` is
    `opaque` in the Lean kernel because `LNIRType.tuple` is a nested inductive). -/
def lnirTypeEqFuel : Nat → LNIRType → LNIRType → Bool
  | 0, _, _ => false
  | _ + 1, .i1, .i1 => true
  | _ + 1, .i8, .i8 => true
  | _ + 1, .i16, .i16 => true
  | _ + 1, .i32, .i32 => true
  | _ + 1, .i64, .i64 => true
  | _ + 1, .usize, .usize => true
  | _ + 1, .u256, .u256 => true
  | _ + 1, .i256, .i256 => true
  | _ + 1, .f16, .f16 => true
  | _ + 1, .f32, .f32 => true
  | _ + 1, .f64, .f64 => true
  | _ + 1, .objPtr, .objPtr => true
  | _ + 1, .taggedPtr, .taggedPtr => true
  | _ + 1, .storageMap, .storageMap => true
  | _ + 1, .unit, .unit => true
  | fuel + 1, .sarray a, .sarray b => lnirTypeEqFuel fuel a b
  | fuel + 1, .rawPtr a, .rawPtr b => lnirTypeEqFuel fuel a b
  | _, .tuple [], .tuple [] => true
  | fuel + 1, .tuple (a :: as_), .tuple (b :: bs) =>
    lnirTypeEqFuel fuel a b && lnirTypeEqFuel fuel (.tuple as_) (.tuple bs)
  | _, _, _ => false

def lnirTypeEq (a b : LNIRType) : Bool :=
  lnirTypeEqFuel 32 a b

def lnirTypeListEq : List LNIRType → List LNIRType → Bool
  | [], [] => true
  | a :: as_, b :: bs => lnirTypeEq a b && lnirTypeListEq as_ bs
  | _, _ => false

def isHeapPtrType : LNIRType → Bool
  | .objPtr | .taggedPtr => true
  | _ => false

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
  if !lnirTypeEq t0 .objPtr || e == Lean.Compiler.LCNF.ImpureType.object then t0
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
  deriving Inhabited, Repr

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
  ctorSiblings     : List (Lean.Name × Nat × Lean.Name) := []
  typeOverrides    : List (Lean.Expr × LNIRType) := []
  paramTypeMap     : List (Lean.FVarId × LNIRType) := []
  localCallees     : List (Lean.Name × String) := []
  gfSimdIntrinsics : List (Lean.Name × BinOp) := []
  knownFVarCtors   : List (Lean.FVarId × Lean.Name) := []
  deriving Inhabited

def RealBridgeCtx.findLayout? (ctx : RealBridgeCtx) (ctorName : Lean.Name) : Option RcCtorLayoutSpec :=
  (ctx.ctorLayouts.find? (fun (n, _) => n == ctorName)).map Prod.snd

def RealBridgeCtx.findNullaryCtor? (ctx : RealBridgeCtx) (ctorName : Lean.Name) : Option Nat :=
  (ctx.nullaryCtors.find? (fun (n, _) => n == ctorName)).map Prod.snd

def RealBridgeCtx.findTupleArity? (ctx : RealBridgeCtx) (ctorName : Lean.Name) : Option Nat :=
  if ctorName == ``Prod.mk || ctorName == ``MProd.mk || ctorName == ``PProd.mk then some 2
  else (ctx.tupleStructCtors.find? (fun (n, _) => n == ctorName)).map Prod.snd

def RealBridgeCtx.findSiblingCtor? (ctx : RealBridgeCtx) (curCtor : Lean.Name) (cidx : Nat) : Option Lean.Name :=
  (ctx.ctorSiblings.find? (fun (c, i, _) => c == curCtor && i == cidx)).map fun (_, _, n) => n

def RealBridgeCtx.hasSiblingEntry (ctx : RealBridgeCtx) (curCtor : Lean.Name) : Bool :=
  ctx.ctorSiblings.any (fun (c, _, _) => c == curCtor)

def RealBridgeCtx.findLocalCallee? (ctx : RealBridgeCtx) (fnName : Lean.Name) : Option String :=
  (ctx.localCallees.find? (fun (n, _) => n == fnName)).map Prod.snd

def RealBridgeCtx.findGfSimd? (ctx : RealBridgeCtx) (fnName : Lean.Name) : Option BinOp :=
  (ctx.gfSimdIntrinsics.find? (fun (n, _) => n == fnName)).map Prod.snd

def RealBridgeCtx.findKnownFVarCtor? (ctx : RealBridgeCtx) (fvarId : Lean.FVarId) : Option Lean.Name :=
  (ctx.knownFVarCtors.find? (fun (f, _) => f == fvarId)).map Prod.snd

def lowerGroundImpureTypeWith (ctx : RealBridgeCtx) (e : Lean.Expr) : LNIRType :=
  match ctx.typeOverrides.find? (fun (ex, _) => ex == e) with
  | some (_, ty) => ty
  | none => lowerGroundImpureType e

def RealBridgeCtx.lowerParamType (ctx : RealBridgeCtx) (p : Lean.Compiler.LCNF.Param .impure) : LNIRType :=
  match ctx.paramTypeMap.find? (fun (f, _) => f == p.fvarId) with
  | some (_, ty) => ty
  | none => lowerGroundImpureTypeWith ctx p.type

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

end LeanNative.IR.RealLCNFBridge
