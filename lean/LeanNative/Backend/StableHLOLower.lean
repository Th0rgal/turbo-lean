import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Backend.TargetIR
import LeanNative.Backend.StableHLOAst.Syntax
import LeanNative.Backend.StableHLOAst.Eval
import LeanNative.Backend.LLVMLower

/-!
# LNIR → Typed StableHLO AST Lowering (`LeanNative.Backend.StableHLOLower`)

Total, compositional lowering of both:
1. The typed scalar/branching LNIR fragment (`ScalarExpr`, `letBind`, nested `ite`
   lowered to eager `convert` + `select`, `ret`), and
2. Data-parallel tensor pipelines (`sarrayLen`, `sarrayGet`, and `LNIRCode.parFor`
   with `.mapScaleAdd`, `.zipAdd`, `.zipMul`, `.saxpy`, and `.dotProduct` via
   `stablehlo.dot_general` + `stablehlo.reshape`)
into `LeanNative.Backend.StableHLOAst` (`FuncOp` / `ModuleOp`), whose operational
evaluator (`StableHLOAst.evalOp`, `evalOps`, `evalFuncOp`) is completely independent
of `LeanNative.Semantics.eval*`.
-/

namespace LeanNative.Backend.StableHLOLower

open LeanNative.IR
open LeanNative.Backend.TargetIR
open LeanNative.Backend.StableHLOAst
open LeanNative.Backend.LLVMLower (isI64Ty isI1Ty sameScalarTy)

/-- 0-D unsigned 64-bit scalar tensor type (`tensor<ui64>`). -/
def scUi64Ty : TensorType := { shape := [], elem := .ui64 }

/-- 0-D signed 64-bit scalar tensor type (`tensor<i64>`), used for arithmetic right shift. -/
def scI64Ty : TensorType := { shape := [], elem := .i64 }

/-- 0-D boolean scalar tensor type (`tensor<i1>`), used by `compare` and `select`. -/
def scI1Ty : TensorType := { shape := [], elem := .i1 }

/-- 1-D unsigned 64-bit vector tensor type (`tensor<n x ui64>`). -/
def vecUi64Ty (n : Nat) : TensorType := { shape := [n], elem := .ui64 }

/-- Construct a well-formed 0-D `tensor<ui64>` constant from a 64-bit word. -/
def mkScUi64 (w : BitVec 64) : TensorVal := { ty := scUi64Ty, data := #[w] }

/-- StableHLO SSA parameter name for an LNIR `VarId` (`"v"` + decimal digits). -/
def hloVarReg (v : VarId) : String := "v" ++ ppInt v

/-- Fresh StableHLO SSA temporary name (`"t"` + decimal digits), disjoint from `hloVarReg`. -/
def hloTmpReg (k : Nat) : String := "t" ++ ppInt k

/-- Predicate checking that a `StableHLOOp` is not `.returnOp` (so `evalOps` composes). -/
def isNonReturnOp : StableHLOOp → Bool
  | .returnOp _ => false
  | _ => true

/-- Static value classification tracked during `LNIR → StableHLOAst` lowering. -/
inductive HLOVarKind where
  | scalar (ty : LNIRType) (knownNat : Option Nat)
  | tensor1D (len : Nat)
  deriving Repr, Inhabited, BEq

/-- Static `TensorType` corresponding to an `HLOVarKind`. -/
def HLOVarKind.tensorType : HLOVarKind → TensorType
  | .scalar _ _ => scUi64Ty
  | .tensor1D n => vecUi64Ty n

/-- Lowering environment entry mapping an LNIR `VarId` to its StableHLO SSA name and kind. -/
structure HLOEntry where
  reg  : String
  kind : HLOVarKind
  deriving Repr, Inhabited, BEq

/-- Compile-time environment for `LNIR → StableHLOAst` lowering. -/
abbrev HLOTyEnv := VarId → Option HLOEntry

def HLOTyEnv.empty : HLOTyEnv := fun _ => none

def HLOTyEnv.bind (Γ : HLOTyEnv) (v : VarId) (e : HLOEntry) : HLOTyEnv :=
  fun q => if q == v then some e else Γ q

/-- Map an LNIR parameter type to its `HLOVarKind` given static 1-D extent `tensorLen`. -/
def paramVarKind (tensorLen : Nat) : LNIRType → Option HLOVarKind
  | .i64 => some (.scalar .i64 none)
  | .i1 => some (.scalar .i1 none)
  | .sarray .i64 =>
    if decide (tensorLen < 2 ^ 64) then some (.tensor1D tensorLen) else none
  | _ => none

/-- Build the initial `HLOTyEnv` and `FuncOp.params` list left-to-right. -/
def initHLOParamsAcc (tensorLen : Nat) (Γ : HLOTyEnv) :
    List LNIRParam → Option (HLOTyEnv × List (String × TensorType))
  | [] => some (Γ, [])
  | p :: ps => do
    let vk ← paramVarKind tensorLen p.ty
    let r := hloVarReg p.id
    let (Γ', rest) ← initHLOParamsAcc tensorLen (Γ.bind p.id ⟨r, vk⟩) ps
    some (Γ', (r, vk.tensorType) :: rest)

def initHLOParams (tensorLen : Nat) (ps : List LNIRParam) :
    Option (HLOTyEnv × List (String × TensorType)) :=
  initHLOParamsAcc tensorLen HLOTyEnv.empty ps

/-- Result of lowering a pure `ScalarExpr` to straight-line `StableHLOOp`s. -/
structure HLOScalarRes where
  ty      : LNIRType
  reg     : String
  nextTmp : Nat
  ops     : List StableHLOOp
  deriving Repr, Inhabited, BEq

/-- Result of lowering an `LNIRCode` block to straight-line `StableHLOOp`s (without `returnOp`). -/
structure HLOCodeRes where
  outKind : HLOVarKind
  reg     : String
  nextTmp : Nat
  ops     : List StableHLOOp
  deriving Repr, Inhabited, BEq

/-- Guarded 64-bit unsigned `divide` / `remainder` sequence avoiding `ShapeError.divisionByZero`. -/
def emitHLODivRem (k : Nat) (isRem : Bool) (a b : String) :
    String × Nat × List StableHLOOp :=
  let c0 := hloTmpReg k
  let c1 := hloTmpReg (k + 1)
  let z := hloTmpReg (k + 2)
  let safe := hloTmpReg (k + 3)
  let raw := hloTmpReg (k + 4)
  let res := hloTmpReg (k + 5)
  let divOp : StableHLOOp :=
    if isRem then .remainder raw a safe else .divide raw a safe
  let fallback : String := if isRem then a else c0
  (res, k + 6,
    [ .constant c0 (mkScUi64 0#64)
    , .constant c1 (mkScUi64 1#64)
    , .compare z b c0 .eq
    , .select safe z c1 b
    , divOp
    , .select res z fallback raw ])

/-- Masked 64-bit logical shift (`amt = b & 63`, so `amt < 64` avoids saturation mismatch). -/
def emitHLOShiftLogical (k : Nat) (isRight : Bool) (a b : String) :
    String × Nat × List StableHLOOp :=
  let c63 := hloTmpReg k
  let amt := hloTmpReg (k + 1)
  let res := hloTmpReg (k + 2)
  let shOp : StableHLOOp :=
    if isRight then .shiftRightLogical res a amt else .shiftLeft res a amt
  (res, k + 3,
    [ .constant c63 (mkScUi64 63#64)
    , .and amt b c63
    , shOp ])

/-- Masked 64-bit signed arithmetic right shift via `ui64 -> i64` conversion + `shiftRightArithmetic`. -/
def emitHLOSar (k : Nat) (a b : String) : String × Nat × List StableHLOOp :=
  let c63 := hloTmpReg k
  let amt := hloTmpReg (k + 1)
  let ls := hloTmpReg (k + 2)
  let as_ := hloTmpReg (k + 3)
  let rs := hloTmpReg (k + 4)
  let res := hloTmpReg (k + 5)
  (res, k + 6,
    [ .constant c63 (mkScUi64 63#64)
    , .and amt b c63
    , .convert ls a .i64
    , .convert as_ amt .i64
    , .shiftRightArithmetic rs ls as_
    , .convert res rs .ui64 ])

/-- Unsigned 64-bit comparison (`compare` -> `tensor<i1>`, then `convert` -> `tensor<ui64>`). -/
def emitHLOCmp (k : Nat) (dir : CompareDir) (a b : String) :
    String × Nat × List StableHLOOp :=
  let cmp := hloTmpReg k
  let res := hloTmpReg (k + 1)
  (res, k + 2,
    [ .compare cmp a b dir
    , .convert res cmp .ui64 ])

/-- Type-checked 64-bit binary op tail emission after lowering `rl` and `rr`. -/
def lowerHLOBinOp64 (op : BinOp) (rl rr : HLOScalarRes) : Option HLOScalarRes :=
  let pfx := rl.ops ++ rr.ops
  let k2 := rr.nextTmp
  match op with
  | .add =>
    let d := hloTmpReg k2
    some ⟨.i64, d, k2 + 1, pfx ++ [.add d rl.reg rr.reg]⟩
  | .sub =>
    let d := hloTmpReg k2
    some ⟨.i64, d, k2 + 1, pfx ++ [.subtract d rl.reg rr.reg]⟩
  | .mul =>
    let d := hloTmpReg k2
    some ⟨.i64, d, k2 + 1, pfx ++ [.multiply d rl.reg rr.reg]⟩
  | .div =>
    let (d, k3, ops) := emitHLODivRem k2 false rl.reg rr.reg
    some ⟨.i64, d, k3, pfx ++ ops⟩
  | .mod =>
    let (d, k3, ops) := emitHLODivRem k2 true rl.reg rr.reg
    some ⟨.i64, d, k3, pfx ++ ops⟩
  | .bitAnd =>
    let d := hloTmpReg k2
    some ⟨.i64, d, k2 + 1, pfx ++ [.and d rl.reg rr.reg]⟩
  | .bitOr =>
    let d := hloTmpReg k2
    some ⟨.i64, d, k2 + 1, pfx ++ [.or d rl.reg rr.reg]⟩
  | .bitXor =>
    let d := hloTmpReg k2
    some ⟨.i64, d, k2 + 1, pfx ++ [.xor d rl.reg rr.reg]⟩
  | .shl =>
    let (d, k3, ops) := emitHLOShiftLogical k2 false rl.reg rr.reg
    some ⟨.i64, d, k3, pfx ++ ops⟩
  | .shr =>
    let (d, k3, ops) := emitHLOShiftLogical k2 true rl.reg rr.reg
    some ⟨.i64, d, k3, pfx ++ ops⟩
  | .sar =>
    let (d, k3, ops) := emitHLOSar k2 rl.reg rr.reg
    some ⟨.i64, d, k3, pfx ++ ops⟩
  | .eq =>
    let (d, k3, ops) := emitHLOCmp k2 .eq rl.reg rr.reg
    some ⟨.i1, d, k3, pfx ++ ops⟩
  | .lt =>
    let (d, k3, ops) := emitHLOCmp k2 .lt rl.reg rr.reg
    some ⟨.i1, d, k3, pfx ++ ops⟩
  | .le =>
    let (d, k3, ops) := emitHLOCmp k2 .le rl.reg rr.reg
    some ⟨.i1, d, k3, pfx ++ ops⟩
  | _ => none

/-- Type-checked binary op tail emission after lowering `rl` and `rr`. -/
def lowerHLOBinOpStep (op : BinOp) (rl rr : HLOScalarRes) : Option HLOScalarRes :=
  match rl.ty with
  | .i64 =>
    match rr.ty with
    | .i64 => lowerHLOBinOp64 op rl rr
    | _ => none
  | .i1 =>
    match rr.ty with
    | .i1 =>
      match op with
      | .eq =>
        let (d, k3, ops) := emitHLOCmp rr.nextTmp .eq rl.reg rr.reg
        some ⟨.i1, d, k3, (rl.ops ++ rr.ops) ++ ops⟩
      | _ => none
    | _ => none
  | _ => none

/-- Lower a pure `ScalarExpr` into straight-line `StableHLOOp`s producing a `tensor<ui64>`. -/
def lowerScalarExpr (Γ : HLOTyEnv) : ScalarExpr → Nat → Option HLOScalarRes
  | .constU64 val, k =>
    let d := hloTmpReg k
    some ⟨.i64, d, k + 1, [.constant d (mkScUi64 val.toBitVec)]⟩
  | .constBool b, k =>
    let d := hloTmpReg k
    some ⟨.i1, d, k + 1, [.constant d (mkScUi64 (if b then 1#64 else 0#64))]⟩
  | .var id, k =>
    match Γ id with
    | some ⟨r, .scalar ty _⟩ =>
      if isI64Ty ty || isI1Ty ty then some ⟨ty, r, k, []⟩ else none
    | _ => none
  | .unaryOp op arg, k => do
    let ra ← lowerScalarExpr Γ arg k
    match op with
    | .not =>
      if isI64Ty ra.ty then
        let cOnes := hloTmpReg ra.nextTmp
        let d := hloTmpReg (ra.nextTmp + 1)
        some ⟨.i64, d, ra.nextTmp + 2,
          ra.ops ++
            [ .constant cOnes (mkScUi64 (BitVec.ofNat 64 0xffffffffffffffff))
            , .xor d ra.reg cOnes ]⟩
      else if isI1Ty ra.ty then
        let cOne := hloTmpReg ra.nextTmp
        let d := hloTmpReg (ra.nextTmp + 1)
        some ⟨.i1, d, ra.nextTmp + 2,
          ra.ops ++ [ .constant cOne (mkScUi64 1#64), .xor d ra.reg cOne ]⟩
      else none
    | .neg =>
      if isI64Ty ra.ty then
        let c0 := hloTmpReg ra.nextTmp
        let d := hloTmpReg (ra.nextTmp + 1)
        some ⟨.i64, d, ra.nextTmp + 2,
          ra.ops ++ [ .constant c0 (mkScUi64 0#64), .subtract d c0 ra.reg ]⟩
      else none
    | .clz256 => none
  | .binOp op lhs rhs, k => do
    let rl ← lowerScalarExpr Γ lhs k
    let rr ← lowerScalarExpr Γ rhs rl.nextTmp
    lowerHLOBinOpStep op rl rr
  | .select cond tv ev, k => do
    let rc ← lowerScalarExpr Γ cond k
    let rt ← lowerScalarExpr Γ tv rc.nextTmp
    let re ← lowerScalarExpr Γ ev rt.nextTmp
    if (isI1Ty rc.ty || isI64Ty rc.ty) && sameScalarTy rt.ty re.ty then
      let p := hloTmpReg re.nextTmp
      let d := hloTmpReg (re.nextTmp + 1)
      some ⟨rt.ty, d, re.nextTmp + 2,
        rc.ops ++ rt.ops ++ re.ops ++
          [ .convert p rc.reg .i1
          , .select d p rt.reg re.reg ]⟩
    else none
  | .fma a b c, k => do
    let ra ← lowerScalarExpr Γ a k
    let rb ← lowerScalarExpr Γ b ra.nextTmp
    let rc ← lowerScalarExpr Γ c rb.nextTmp
    if isI64Ty ra.ty && isI64Ty rb.ty && isI64Ty rc.ty then
      let m := hloTmpReg rc.nextTmp
      let d := hloTmpReg (rc.nextTmp + 1)
      some ⟨.i64, d, rc.nextTmp + 2,
        ra.ops ++ rb.ops ++ rc.ops ++
          [ .multiply m ra.reg rb.reg
          , .add d m rc.reg ]⟩
    else none

/-- Extract known compile-time `Nat` value for `constU64` scalar literals. -/
def knownNatOfScalarExpr : ScalarExpr → Option Nat
  | .constU64 v => some v.toNat
  | _ => none

/-- Lower a pure scalar/branching `LNIRCode` (`letBind (.scalar ...)`, `ite`, `ret`).
Every `LNIRCode` accepted by `lowerScalarCode` is total and heap-preserving, making eager
evaluation of both `ite` branches via `stablehlo.select` unconditionally sound. -/
def lowerScalarCode (Γ : HLOTyEnv) : LNIRCode → Nat → Option HLOScalarRes
  | .ret v, k =>
    match Γ v with
    | some ⟨r, .scalar ty _⟩ =>
      if isI64Ty ty || isI1Ty ty then some ⟨ty, r, k, []⟩ else none
    | _ => none
  | .letBind dst declTy (.scalar se) kCode, k => do
    let rs ← lowerScalarExpr Γ se k
    if sameScalarTy rs.ty declTy then
      let rk ← lowerScalarCode (Γ.bind dst ⟨rs.reg, .scalar declTy (knownNatOfScalarExpr se)⟩)
        kCode rs.nextTmp
      some ⟨rk.ty, rk.reg, rk.nextTmp, rs.ops ++ rk.ops⟩
    else none
  | .ite condVar thenB elseB, k =>
    match Γ condVar with
    | some ⟨cReg, .scalar cTy _⟩ =>
      if isI1Ty cTy || isI64Ty cTy then do
        let rt ← lowerScalarCode Γ thenB k
        let re ← lowerScalarCode Γ elseB rt.nextTmp
        if sameScalarTy rt.ty re.ty then
          let p := hloTmpReg re.nextTmp
          let d := hloTmpReg (re.nextTmp + 1)
          some ⟨rt.ty, d, re.nextTmp + 2,
            rt.ops ++ re.ops ++
              [ .convert p cReg .i1
              , .select d p rt.reg re.reg ]⟩
        else none
      else none
    | _ => none
  | _, _ => none

/-- Lower a data-parallel `ParallelKernelKind` (`mapScaleAdd`, `zipAdd`, `zipMul`,
`saxpy`, `dotProduct`) over 1-D `tensor<n x ui64>` buffers into `StableHLOOp`s. -/
def lowerParKernel (Γ : HLOTyEnv) (lenVar : VarId) (inputs : List VarId)
    (kernel : ParallelKernelKind) (k : Nat) : Option HLOCodeRes :=
  match Γ lenVar with
  | some ⟨_, .scalar .i64 (some n)⟩ =>
    match kernel, inputs with
    | .mapScaleAdd scale bias, [x] =>
      match Γ x with
      | some ⟨rx, .tensor1D nx⟩ =>
        if nx == n then
          let cS := hloTmpReg k
          let bS := hloTmpReg (k + 1)
          let m := hloTmpReg (k + 2)
          let cB := hloTmpReg (k + 3)
          let bB := hloTmpReg (k + 4)
          let d := hloTmpReg (k + 5)
          some ⟨.tensor1D n, d, k + 6,
            [ .constant cS (mkScUi64 scale.toBitVec)
            , .broadcastInDim bS cS [n] []
            , .multiply m rx bS
            , .constant cB (mkScUi64 bias.toBitVec)
            , .broadcastInDim bB cB [n] []
            , .add d m bB ]⟩
        else none
      | _ => none
    | .zipAdd, [x, y] =>
      match Γ x, Γ y with
      | some ⟨rx, .tensor1D nx⟩, some ⟨ry, .tensor1D ny⟩ =>
        if nx == n && ny == n then
          let d := hloTmpReg k
          some ⟨.tensor1D n, d, k + 1, [.add d rx ry]⟩
        else none
      | _, _ => none
    | .zipMul, [x, y] =>
      match Γ x, Γ y with
      | some ⟨rx, .tensor1D nx⟩, some ⟨ry, .tensor1D ny⟩ =>
        if nx == n && ny == n then
          let d := hloTmpReg k
          some ⟨.tensor1D n, d, k + 1, [.multiply d rx ry]⟩
        else none
      | _, _ => none
    | .saxpy alpha, [x, y] =>
      match Γ x, Γ y with
      | some ⟨rx, .tensor1D nx⟩, some ⟨ry, .tensor1D ny⟩ =>
        if nx == n && ny == n then
          let cA := hloTmpReg k
          let bA := hloTmpReg (k + 1)
          let m := hloTmpReg (k + 2)
          let d := hloTmpReg (k + 3)
          some ⟨.tensor1D n, d, k + 4,
            [ .constant cA (mkScUi64 alpha.toBitVec)
            , .broadcastInDim bA cA [n] []
            , .multiply m bA rx
            , .add d m ry ]⟩
        else none
      | _, _ => none
    | .dotProduct, [x, y] =>
      match Γ x, Γ y with
      | some ⟨rx, .tensor1D nx⟩, some ⟨ry, .tensor1D ny⟩ =>
        if nx == n && ny == n then
          let dot0 := hloTmpReg k
          let d := hloTmpReg (k + 1)
          some ⟨.tensor1D 1, d, k + 2,
            [ .dotGeneral dot0 rx ry [] [] [0] [0] []
            , .reshape d dot0 [1] ]⟩
        else none
      | _, _ => none
    | _, _ => none
  | _ => none

/-- Compositional `LNIRCode → StableHLOOp` lowering covering scalar let-bindings,
`sarrayLen`, static-index `sarrayGet` (`slice` + `reshape`), `parFor` tensor kernels,
scalar `ite` diamonds, and `ret`. -/
def lowerCode (Γ : HLOTyEnv) : LNIRCode → Nat → Option HLOCodeRes
  | .ret v, k =>
    match Γ v with
    | some ⟨r, .scalar ty kn⟩ =>
      if isI64Ty ty || isI1Ty ty then some ⟨.scalar ty kn, r, k, []⟩ else none
    | some ⟨r, .tensor1D n⟩ =>
      some ⟨.tensor1D n, r, k, []⟩
    | none => none
  | .letBind dst declTy (.scalar se) kCode, k => do
    let rs ← lowerScalarExpr Γ se k
    if sameScalarTy rs.ty declTy then
      let rk ← lowerCode (Γ.bind dst ⟨rs.reg, .scalar declTy (knownNatOfScalarExpr se)⟩)
        kCode rs.nextTmp
      some ⟨rk.outKind, rk.reg, rk.nextTmp, rs.ops ++ rk.ops⟩
    else none
  | .letBind dst .i64 (.sarrayLen arrVar) kCode, k =>
    match Γ arrVar with
    | some ⟨_, .tensor1D n⟩ =>
      if decide (n < 2 ^ 64) then do
        let d := hloTmpReg k
        let op := StableHLOOp.constant d (mkScUi64 (BitVec.ofNat 64 n))
        let rk ← lowerCode (Γ.bind dst ⟨d, .scalar .i64 (some n)⟩) kCode (k + 1)
        some ⟨rk.outKind, rk.reg, rk.nextTmp, op :: rk.ops⟩
      else none
    | _ => none
  | .letBind dst .i64 (.sarrayGet arrVar idxVar .i64) kCode, k =>
    match Γ arrVar, Γ idxVar with
    | some ⟨rArr, .tensor1D n⟩, some ⟨_, .scalar .i64 (some idx)⟩ =>
      if decide (idx < n) then do
        let sl := hloTmpReg k
        let d := hloTmpReg (k + 1)
        let ops0 : List StableHLOOp :=
          [ .slice sl rArr [idx] [idx + 1] [1]
          , .reshape d sl [] ]
        let rk ← lowerCode (Γ.bind dst ⟨d, .scalar .i64 none⟩) kCode (k + 2)
        some ⟨rk.outKind, rk.reg, rk.nextTmp, ops0 ++ rk.ops⟩
      else none
    | _, _ => none
  | .parFor outVar lenVar inputs .i64 kernel kCode, k => do
    let rp ← lowerParKernel Γ lenVar inputs kernel k
    let rk ← lowerCode (Γ.bind outVar ⟨rp.reg, rp.outKind⟩) kCode rp.nextTmp
    some ⟨rk.outKind, rk.reg, rk.nextTmp, rp.ops ++ rk.ops⟩
  | .ite condVar thenB elseB, k => do
    let rs ← lowerScalarCode Γ (.ite condVar thenB elseB) k
    some ⟨.scalar rs.ty none, rs.reg, rs.nextTmp, rs.ops⟩
  | _, _ => none

/-- Check that the lowered `HLOVarKind` matches `d.retTy` and return the `FuncOp` result type. -/
def matchReturnKind (retTy : LNIRType) : HLOVarKind → Option TensorType
  | .scalar ty _ => if sameScalarTy ty retTy then some scUi64Ty else none
  | .tensor1D n =>
    match retTy with
    | .sarray .i64 => some (vecUi64Ty n)
    | _ => none

/-- Lower a top-level `LNIRDecl` with static 1-D tensor extent `tensorLen` (default `0` for
scalar-only functions) into a typed `StableHLOAst.FuncOp`. -/
def lowerToStableHLO (d : LNIRDecl) (tensorLen : Nat := 0) : Option FuncOp := do
  let (Γ0, params) ← initHLOParams tensorLen d.params
  let rc ← lowerCode Γ0 d.body 0
  let resTy ← matchReturnKind d.retTy rc.outKind
  some
    { name := d.name
    , params := params
    , result := resTy
    , body := rc.ops ++ [.returnOp rc.reg] }

/-- Lower a list of `LNIRDecl`s into a `StableHLOAst.ModuleOp`. -/
def lowerModuleToStableHLO (modName : String) (decls : List LNIRDecl)
    (tensorLen : Nat := 0) : Option ModuleOp := do
  let fns ← decls.mapM (fun d => lowerToStableHLO d tensorLen)
  some { name := modName, funcs := fns }

/-! ## Emitter Mutant Witnesses (for Mechanized Mutant-Kill Proofs) -/

/-- Mutant H1: swaps operand order in `subtract` (`b - a` instead of `a - b`). -/
def hloMutantSubSwap : FuncOp :=
  { name := "mutant_sub_swap"
  , params := [("v0", scUi64Ty), ("v1", scUi64Ty)]
  , result := scUi64Ty
  , body := [.subtract "t0" "v1" "v0", .returnOp "t0"] }

/-- Mutant H2: omits the `& 63` shift-amount mask before `shiftLeft`. -/
def hloMutantUnmaskedShl : FuncOp :=
  { name := "mutant_unmasked_shl"
  , params := [("v0", scUi64Ty), ("v1", scUi64Ty)]
  , result := scUi64Ty
  , body := [.shiftLeft "t0" "v0" "v1", .returnOp "t0"] }

/-- Mutant H3: omits the zero-divisor guard before `divide` (causing `.divisionByZero`). -/
def hloMutantUnguardedDiv : FuncOp :=
  { name := "mutant_unguarded_div"
  , params := [("v0", scUi64Ty), ("v1", scUi64Ty)]
  , result := scUi64Ty
  , body := [.divide "t0" "v0" "v1", .returnOp "t0"] }

end LeanNative.Backend.StableHLOLower
