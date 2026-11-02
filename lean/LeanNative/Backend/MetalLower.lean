import LeanNative.IR.AST
import LeanNative.Backend.MetalAst
import LeanNative.Semantics.Eval

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
  | .zipMul | .dotProduct => kernelOf name 2 (.mul (elem "in0") (elem "in1"))
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

end LeanNative.Backend.MetalLower
