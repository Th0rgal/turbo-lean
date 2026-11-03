import LeanNative.IR.AST
import LeanNative.Backend.MetalAst

/-!
# Typed LNIR → Metal MSL 3.0 lowering (`LeanNative.Backend.MetalLower`)

Total, structural lowering of `ScalarExpr` / `ParallelKernelKind` into the typed
`MetalAst` consumed by `evalMSLKernel`. Comparisons are widened to `ulong`,
shifts are masked by 63, and division / remainder by zero select the LNIR
result (`0` / dividend) through short-circuit `?:` so the evaluator never traps.
-/

namespace LeanNative.Backend.MetalLower

open LeanNative.IR
open LeanNative.Backend.MetalAst

def u (n : Nat) : MSLExpr := .immU64 (BitVec.ofNat 64 n)

def v (id : Nat) : MSLExpr := .var s!"v{id}"

def m63 (e : MSLExpr) : MSLExpr := .bitAnd e (u 63)

def lowerScalar (idxName : String) (idxVar : Nat) : ScalarExpr → MSLExpr
  | .constU64 n => .immU64 n.toBitVec
  | .constBool b => u (if b then 1 else 0)
  | .var id => if id == idxVar then .var idxName else v id
  | .binOp op l r =>
    let ls := lowerScalar idxName idxVar l
    let rs := lowerScalar idxName idxVar r
    match op with
    | .add | .addChecked256 => .add ls rs
    | .sub | .subChecked256 => .sub ls rs
    | .mul | .mulChecked256 => .mul ls rs
    | .div => .select (.eq rs (u 0)) (u 0) (.div ls rs)
    | .mod => .select (.eq rs (u 0)) ls (.rem ls rs)
    | .bitAnd => .bitAnd ls rs
    | .bitOr => .bitOr ls rs
    | .bitXor => .bitXor ls rs
    | .shl => .shl ls (m63 rs)
    | .shr => .shr ls (m63 rs)
    | .sar => .cast .ulong (.shr (.cast .long ls) (m63 rs))
    | .eq => .cast .ulong (.eq ls rs)
    | .lt => .cast .ulong (.lt ls rs)
    | .le => .cast .ulong (.le ls rs)
    | .eor3 => .bitXor (.bitXor ls (.shr rs (u 32))) (.bitAnd rs (.immU64 0xffffffff#64))
    | .clmul64 | .clmul64Hi | .gf2Affine => .bitXor ls rs
  | .unaryOp op a =>
    let as_ := lowerScalar idxName idxVar a
    match op with
    | .not => .bitNot as_
    | .neg => .sub (u 0) as_
    | .clz256 => .add (u 192) (.clz as_)
  | .select c t f =>
    .select (.ne (lowerScalar idxName idxVar c) (u 0))
      (lowerScalar idxName idxVar t) (lowerScalar idxName idxVar f)
  | .fma a b c =>
    .add (.mul (lowerScalar idxName idxVar a) (lowerScalar idxName idxVar b))
      (lowerScalar idxName idxVar c)

def bufParam (name : String) (idx : Nat) (isConst : Bool) : MSLParamDecl :=
  { ty := .pointer .device isConst .ulong, name := name, attr := some (.buffer idx) }

def lenParam (idx : Nat) : MSLParamDecl :=
  { ty := .ref .constant .ulong, name := "n", attr := some (.buffer idx) }

def gidParam : MSLParamDecl :=
  { ty := .uint, name := "gid", attr := some .threadPositionInGrid }

def guarded (inner : List MSLStmt) : List MSLStmt :=
  [ .ifElse (.lt (.cast .ulong (.var "gid")) (.var "n")) (MSLBlock.ofList inner) .nil
  , .returnStmt ]

def elem (name : String) : MSLExpr := .index name (.var "gid")

def storeOut (rhs : MSLExpr) : MSLStmt := .indexAssign "out" (.var "gid") rhs

def kernelOf (name : String) (nIn : Nat) (compute : MSLExpr) : MSLKernelDecl where
  name := name
  params := (List.range nIn).map (fun i => bufParam s!"in{i}" i true) ++
    [bufParam "out" nIn false, lenParam (nIn + 1), gidParam]
  body := guarded [storeOut compute]

def lowerKind (name : String) : ParallelKernelKind → MSLKernelDecl
  | .mapScaleAdd scale bias =>
    kernelOf name 1 (.add (.mul (elem "in0") (.immU64 scale.toBitVec)) (.immU64 bias.toBitVec))
  | .zipAdd => kernelOf name 2 (.add (elem "in0") (elem "in1"))
  | .zipMul => kernelOf name 2 (.mul (elem "in0") (elem "in1"))
  | .dotProduct =>
    -- Rejected by `wfMetalKernel` and `lowerDeclToMetal` (dotProduct is a reduction, not 1-D map).
    { name := name, params := [], body := [.returnStmt] }
  | .saxpy alpha =>
    kernelOf name 2 (.add (.mul (.immU64 alpha.toBitVec) (elem "in0")) (elem "in1"))
  | .stencil1D3Pt wL wC wR =>
    let i := .cast .ulong (.var "gid")
    let edge := .logOr (.eq i (u 0)) (.ge (.add i (u 1)) (.var "n"))
    let center := elem "in0"
    let interior := .add (.add
      (.mul (.immU64 wL.toBitVec) (.index "in0" (.sub i (u 1))))
      (.mul (.immU64 wC.toBitVec) center))
      (.mul (.immU64 wR.toBitVec) (.index "in0" (.add i (u 1))))
    { name := name
      params := [bufParam "in0" 0 true, bufParam "out" 1 false, lenParam 2, gidParam]
      body := guarded [.ifElse edge (.cons (storeOut center) .nil)
        (.cons (storeOut interior) .nil)] }
  | .customScalar idxVar inVars body =>
    let loads := (List.range inVars.length).map fun k =>
      let id := inVars[k]?.getD 0
      .varDecl .ulong s!"v{id}" (elem s!"in{k}")
    let rhs := lowerScalar "gid64" idxVar body
    { name := name
      params := (List.range inVars.length).map (fun i => bufParam s!"in{i}" i true) ++
        [bufParam "out" inVars.length false, lenParam (inVars.length + 1), gidParam]
      body := guarded
        ([.varDecl .ulong "gid64" (.cast .ulong (.var "gid"))] ++ loads ++ [storeOut rhs]) }

def lowerToMetal (name : String) (k : ParallelKernelKind) : MSLModule where
  kernels := [lowerKind name k]

def ppLowered (name : String) (k : ParallelKernelKind) : String :=
  ppMSLModule (lowerToMetal name k)

/-- Build the `saxpy` `MSLKernelDecl` with `x [[buffer(0)]]`, `y [[buffer(1)]]` parameter names
matching `Hybrid.declMetalBindingSpec` while sharing `MetalLower` AST emission. -/
def lowerSaxpyNamed (name : String) (alpha : UInt64) : MSLKernelDecl where
  name := name
  params := [bufParam "x" 0 true, bufParam "y" 1 true, bufParam "out" 2 false, lenParam 3, gidParam]
  body := guarded [storeOut (.add (.mul (.immU64 alpha.toBitVec) (elem "x")) (elem "y"))]

def inferBinOpU64 : BinOp → Option Bool
  | .add => some false | .sub => some false | .mul => some false
  | .div => some false | .mod => some false | .bitAnd => some false
  | .bitOr => some false | .bitXor => some false | .shl => some false
  | .shr => some false | .sar => some false | .eor3 => some false
  | .eq => some true | .lt => some true | .le => some true
  | .addChecked256 => none | .subChecked256 => none | .mulChecked256 => none
  | .clmul64 => none | .clmul64Hi => none | .gf2Affine => none

def inferBinOpBool : BinOp → Option Bool
  | .eq => some true
  | .bitAnd => none | .bitOr => none
  | .add => none | .sub => none | .mul => none | .div => none | .mod => none
  | .bitXor => none | .shl => none | .shr => none | .sar => none
  | .lt => none | .le => none
  | .addChecked256 => none | .subChecked256 => none | .mulChecked256 => none
  | .clmul64 => none | .clmul64Hi => none | .gf2Affine => none | .eor3 => none

def inferUnaryOpU64 : UnaryOp → Option Bool
  | .not => some false | .neg => some false | .clz256 => none

def inferScalarSort (boundVars : List Nat) : ScalarExpr → Option Bool
  | .constU64 _ => some false
  | .constBool _ => some true
  | .var id => if id ∈ boundVars then some false else none
  | .binOp op l r =>
    match inferScalarSort boundVars l with
    | some sl =>
      match inferScalarSort boundVars r with
      | some sr =>
        if !sl && !sr then inferBinOpU64 op
        else if sl && sr then inferBinOpBool op
        else none
      | none => none
    | none => none
  | .unaryOp op a =>
    match inferScalarSort boundVars a with
    | some sa => if !sa then inferUnaryOpU64 op else none
    | none => none
  | .select c t f =>
    match inferScalarSort boundVars c with
    | some _ =>
      match inferScalarSort boundVars t with
      | some st =>
        match inferScalarSort boundVars f with
        | some sf => if st == sf then some st else none
        | none => none
      | none => none
    | none => none
  | .fma a b c =>
    match inferScalarSort boundVars a with
    | some sa =>
      match inferScalarSort boundVars b with
      | some sb =>
        match inferScalarSort boundVars c with
        | some sc => if !sa && !sb && !sc then some false else none
        | none => none
      | none => none
    | none => none

def kernelArity : ParallelKernelKind → Nat
  | .mapScaleAdd _ _ | .stencil1D3Pt _ _ _ => 1
  | .zipAdd | .zipMul | .dotProduct | .saxpy _ => 2
  | .customScalar _ inVars _ => inVars.length

def wfMetalKernel : ParallelKernelKind → Bool
  | .mapScaleAdd _ _ | .zipAdd | .zipMul | .saxpy _ | .stencil1D3Pt _ _ _ => true
  | .dotProduct => false
  | .customScalar idxVar inVars body =>
    decide (inVars.Nodup ∧ idxVar ∉ inVars) && (inferScalarSort (idxVar :: inVars) body).isSome

/-- Extract `(lenVar, inputs, kernel)` from a GPU 1-D `parFor` declaration body
(`parFor outVar lenVar inputs .i64 k (ret outVar)` or preceded by `let lenVar = sarrayLen arrVar`). -/
def extractDeclParFor : LNIRCode → Option (Option VarId × VarId × List VarId × ParallelKernelKind)
  | .parFor outVar lenVar inputs .i64 k (.ret retVar) =>
    if outVar == retVar then some (none, lenVar, inputs, k) else none
  | .letBind lenVar .i64 (.sarrayLen arrVar) (.parFor outVar lenVar' inputs .i64 k (.ret retVar)) =>
    if lenVar == lenVar' && outVar == retVar then some (some arrVar, lenVar, inputs, k) else none
  | _ => none

/-- Lower a top-level `LNIRDecl` containing a well-formed 1-D `parFor` kernel into an `MSLModule`
(`.dotProduct` reductions and ill-typed kernels return `none`). -/
def isSarrayI64 : LNIRType → Bool
  | .sarray .i64 => true
  | _ => false

def lowerDeclToMetal (d : LNIRDecl) : Option MSLModule :=
  if isSarrayI64 d.retTy then
    match extractDeclParFor d.body with
    | some (_, _, inputs, k) =>
      if wfMetalKernel k && inputs.length == kernelArity k then
        some (lowerToMetal s!"lean_native_metal_decl_{d.name}" k)
      else none
    | none => none
  else none

def mkDeviceBuffers (inBufs : List (Nat × ByteMemory)) (nIn len : Nat) :
    List (Nat × ByteMemory) :=
  inBufs ++ [(nIn, ByteMemory.zeros (len * 8))]

def mkConstLenBuffers (nIn len : Nat) : List (Nat × ByteMemory) :=
  [(nIn + 1, ByteMemory.ofU64Words [BitVec.ofNat 64 len])]

def groupStepsForKind (groupSize : Nat) (k : ParallelKernelKind) : Nat :=
  let perThread := match k with
    | .customScalar _ inVars _ => inVars.length + 5
    | .stencil1D3Pt _ _ _ => 5
    | _ => 4
  groupSize * perThread + 2

/-- `M9` mutant of `lowerKind` for `.customScalar`: replaces the zero-divisor guard
`((rs == 0UL) ? 0UL : (ls / rs))` on `.div` with unguarded `ls / rs`. -/
def metalMutantM9Scalar (idxName : String) (idxVar : Nat) : ScalarExpr → MSLExpr
  | .binOp .div l r =>
    .div (lowerScalar idxName idxVar l) (lowerScalar idxName idxVar r)
  | e => lowerScalar idxName idxVar e

def metalMutantM9Kernel (name : String) (idxVar : Nat) (inVars : List VarId) (body : ScalarExpr) :
    MSLKernelDecl :=
  let loads := (List.range inVars.length).map fun k =>
    let id := inVars[k]?.getD 0
    .varDecl .ulong s!"v{id}" (elem s!"in{k}")
  { name := name
    params := (List.range inVars.length).map (fun i => bufParam s!"in{i}" i true) ++
      [bufParam "out" inVars.length false, lenParam (inVars.length + 1), gidParam]
    body := guarded
      ([.varDecl .ulong "gid64" (.cast .ulong (.var "gid"))] ++ loads ++
        [storeOut (metalMutantM9Scalar "gid64" idxVar body)]) }

/-- `M10` mutant of `lowerKind` for `.customScalar`: narrows the 64-bit `.shl` mask
from `& 63UL` (`m63`) to `& 31UL`. -/
def metalMutantM10Scalar (idxName : String) (idxVar : Nat) : ScalarExpr → MSLExpr
  | .binOp .shl l r =>
    .shl (lowerScalar idxName idxVar l) (.bitAnd (lowerScalar idxName idxVar r) (u 31))
  | e => lowerScalar idxName idxVar e

def metalMutantM10Kernel (name : String) (idxVar : Nat) (inVars : List VarId) (body : ScalarExpr) :
    MSLKernelDecl :=
  let loads := (List.range inVars.length).map fun k =>
    let id := inVars[k]?.getD 0
    .varDecl .ulong s!"v{id}" (elem s!"in{k}")
  { name := name
    params := (List.range inVars.length).map (fun i => bufParam s!"in{i}" i true) ++
      [bufParam "out" inVars.length false, lenParam (inVars.length + 1), gidParam]
    body := guarded
      ([.varDecl .ulong "gid64" (.cast .ulong (.var "gid"))] ++ loads ++
        [storeOut (metalMutantM10Scalar "gid64" idxVar body)]) }

end LeanNative.Backend.MetalLower
