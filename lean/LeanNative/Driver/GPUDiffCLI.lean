import Lean.Data.Json
import LeanNative.IR.AST
import LeanNative.Semantics.Eval
import LeanNative.Backend.GPUIR
import LeanNative.Backend.MLIRGPU
import LeanNative.Backend.Metal
import LeanNative.Backend.PTXAst
import LeanNative.Backend.PTXLower
import LeanNative.Backend.MetalAst
import LeanNative.Backend.MetalLower
import LeanNative.Backend.StableHLOAst
import LeanNative.Backend.StableHLOLower
import LeanNative.Backend.GPUEmitVerify

namespace LeanNative.Driver.GPUDiffCLI

open Lean
open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend.GPUIR
open LeanNative.Backend.MLIRGPU
open LeanNative.Backend.Metal
open LeanNative.Backend.PTXAst
open LeanNative.Backend.PTXLower
open LeanNative.Backend.MetalAst
open LeanNative.Backend.MetalLower
open LeanNative.Backend.StableHLOAst
open LeanNative.Backend.StableHLOLower
open LeanNative.Backend.GPUEmitVerify

private def u64ArrJson (xs : List UInt64) : Json :=
  Json.arr (xs.map (fun w => toJson w.toNat)).toArray

private def natArrJson (xs : List Nat) : Json :=
  Json.arr (xs.map toJson).toArray

private def ppElemStr : ElemType → String
  | .i1 => "i1" | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
  | .ui8 => "ui8" | .ui16 => "ui16" | .ui32 => "ui32" | .ui64 => "ui64"
  | .f32 => "f32" | .f64 => "f64" | .bf16 => "bf16"

private def tensorValJson (tv : TensorVal) : Json :=
  Json.mkObj [
    ("shape", natArrJson tv.ty.shape),
    ("elem", Json.str (ppElemStr tv.ty.elem)),
    ("words", u64ArrJson (tv.data.toList.map (fun bv => bv.toNat.toUInt64)))
  ]

structure PTXSimtVector where
  inputs : List (List UInt64)
  expected : List UInt64

structure PTXCase where
  id : String
  kernelName : String
  arity : Nat
  ptxText : String
  vectors : List PTXSimtVector
  negativeMutantPtx? : Option String := none
  negativeMutantReason? : Option String := none

private def evalPTXOut (k : PTXKernel) (nIn : Nat) (inputs : List (List UInt64)) : Option (List UInt64) :=
  let len := (inputs[0]?.getD []).length
  let fuel := ctaStepsForKind (Nat.max 1 len) (.customScalar 9 [0, 1] (.constU64 0)) + 256
  runParsedPTX k nIn len inputs fuel

private def mkPTXKernelCase (id : String) (name : String) (kind : ParallelKernelKind)
    (inputSets : List (List (List UInt64)))
    (mutant? : Option (PTXKernel × String) := none) : Except String PTXCase := do
  if inputSets.isEmpty then
    throw s!"[PTX:{id}] empty input vector set"
  let nIn := LeanNative.Backend.PTXLower.kernelArity kind
  let k := LeanNative.Backend.PTXLower.lowerKind name kind
  let modText := ppPTXModule { kernels := [k] }
  let vecs ← inputSets.mapM fun ins => do
    let len := (ins[0]?.getD []).length
    let some expLnir := lnirOut kind ins len
      | throw s!"[PTX:{id}] LNIR reference evaluation failed on inputs {repr ins}"
    let some expPtx := evalPTXOut k nIn ins
      | throw s!"[PTX:{id}] PTXAst reference evaluation failed on inputs {repr ins}"
    if expLnir == expPtx then
      pure { inputs := ins, expected := expPtx : PTXSimtVector }
    else
      throw s!"[PTX:{id}] two-sided evaluator mismatch: LNIR={repr expLnir} vs PTXAst={repr expPtx}"
  let (negText?, negReason?) :=
    match mutant? with
    | none => (none, none)
    | some (mk, r) => (some (ppPTXModule { kernels := [mk] }), some r)
  pure
    { id := id
    , kernelName := k.name
    , arity := nIn
    , ptxText := modText
    , vectors := vecs
    , negativeMutantPtx? := negText?
    , negativeMutantReason? := negReason? }

structure MetalVector where
  inputs : List (List UInt64)
  expected : List UInt64

structure MetalCase where
  id : String
  kernelName : String
  arity : Nat
  mslText : String
  vectors : List MetalVector
  negativeMutantMsl? : Option String := none
  negativeMutantReason? : Option String := none

private def evalMetalOut (k : MSLKernelDecl) (nIn : Nat) (inputs : List (List UInt64)) :
    Option (List UInt64) :=
  let len := (inputs[0]?.getD []).length
  runParsedMSL k [] nIn len inputs (len * 32 + 64)

private def mkMetalKernelCase (id : String) (name : String) (kind : ParallelKernelKind)
    (inputSets : List (List (List UInt64)))
    (mutant? : Option (MSLKernelDecl × String) := none) : Except String MetalCase := do
  if inputSets.isEmpty then
    throw s!"[Metal:{id}] empty input vector set"
  let nIn := LeanNative.Backend.MetalLower.kernelArity kind
  let k := LeanNative.Backend.MetalLower.lowerKind name kind
  let modText := ppMSLModule { kernels := [k] }
  let vecs ← inputSets.mapM fun ins => do
    let len := (ins[0]?.getD []).length
    let some expLnir := lnirOut kind ins len
      | throw s!"[Metal:{id}] LNIR reference evaluation failed on inputs {repr ins}"
    let some expMsl := evalMetalOut k nIn ins
      | throw s!"[Metal:{id}] MetalAst reference evaluation failed on inputs {repr ins}"
    if expLnir == expMsl then
      pure { inputs := ins, expected := expMsl : MetalVector }
    else
      throw s!"[Metal:{id}] two-sided evaluator mismatch: LNIR={repr expLnir} vs MetalAst={repr expMsl}"
  let (negText?, negReason?) :=
    match mutant? with
    | none => (none, none)
    | some (mk, r) => (some (ppMSLModule { kernels := [mk] }), some r)
  pure
    { id := id
    , kernelName := k.name
    , arity := nIn
    , mslText := modText
    , vectors := vecs
    , negativeMutantMsl? := negText?
    , negativeMutantReason? := negReason? }

structure StableHLOVector where
  args : List TensorVal
  expected : TensorVal

structure StableHLOCase where
  id : String
  fnName : String
  mlirText : String
  vectors : List StableHLOVector
  negativeMutantMlir? : Option String := none
  negativeMutantReason? : Option String := none

private def scUi64Val (w : UInt64) : TensorVal :=
  { ty := { shape := [], elem := .ui64 }, data := #[w.toBitVec] }

private def scI64Val (w : UInt64) : TensorVal :=
  { ty := { shape := [], elem := .i64 }, data := #[w.toBitVec] }

private def vecUi64Val (ws : List UInt64) : TensorVal :=
  { ty := { shape := [ws.length], elem := .ui64 }, data := (ws.map UInt64.toBitVec).toArray }

private def matUi64Val (rows cols : Nat) (ws : List UInt64) : TensorVal :=
  { ty := { shape := [rows, cols], elem := .ui64 }, data := (ws.map UInt64.toBitVec).toArray }

private def mkStableHLOCase (id : String) (modName : String) (f : FuncOp)
    (argSets : List (List TensorVal))
    (mutant? : Option (FuncOp × String) := none) : Except String StableHLOCase := do
  if argSets.isEmpty then
    throw s!"[StableHLO:{id}] empty argument vector set"
  let m : ModuleOp := { name := modName, funcs := [f] }
  let vecs ← argSets.mapM fun args => do
    match evalFuncOp f args with
    | .ok tv => pure { args := args, expected := tv : StableHLOVector }
    | .error err => throw s!"[StableHLO:{id}] evalFuncOp failed: {repr err}"
  let (negText?, negReason?) :=
    match mutant? with
    | none => (none, none)
    | some (mf, r) =>
      let mm : ModuleOp := { name := modName ++ "_mutant", funcs := [{ mf with name := f.name }] }
      (some (ppModuleOp mm), some r)
  pure
    { id := id
    , fnName := f.name
    , mlirText := ppModuleOp m
    , vectors := vecs
    , negativeMutantMlir? := negText?
    , negativeMutantReason? := negReason? }

private def mkBinScalarDecl (name : String) (retTy : LNIRType) (se : ScalarExpr) : LNIRDecl :=
  { name := name
  , params := [{ id := 0, name := "a", ty := .i64 }, { id := 1, name := "b", ty := .i64 }]
  , retTy := retTy
  , body := .letBind 2 retTy (.scalar se) (.ret 2)
  , isGpuCand := true }

private def mkTernScalarDecl (name : String) (retTy : LNIRType) (se : ScalarExpr) : LNIRDecl :=
  { name := name
  , params :=
      [ { id := 0, name := "a", ty := .i64 }
      , { id := 1, name := "b", ty := .i64 }
      , { id := 2, name := "c", ty := .i64 } ]
  , retTy := retTy
  , body := .letBind 3 retTy (.scalar se) (.ret 3)
  , isGpuCand := true }

private def buildPTXCases : Except String (List PTXCase) := do
  let vecs1 : List (List (List UInt64)) :=
    [ [[0, 1, 7, 42]], [[10, 20, 30, 40, 50]], [[0xffffffffffffffff, 0x8000000000000000, 3]] ]
  let vecs2 : List (List (List UInt64)) :=
    [ [[5, 1, 100, 0xffffffffffffffff], [2, 4, 37, 1]]
    , [[3, 2, 7, 0], [3, 5, 7, 0]]
    , [[18, 7, 1, 0x123456789abcdef0], [3, 0, 65, 19]] ]
  let subBody : ScalarExpr := .binOp .sub (.var 0) (.var 1)
  let ltBody : ScalarExpr := .binOp .lt (.var 0) (.var 1)
  let divBody : ScalarExpr := .binOp .div (.var 0) (.var 1)
  let shlBody : ScalarExpr := .binOp .shl (.var 0) (.var 1)
  let mixBody : ScalarExpr :=
    .select (.binOp .le (.var 0) (.var 1))
      (.binOp .bitXor (.fma (.var 0) (.constU64 5) (.var 1)) (.binOp .shr (.var 0) (.constU64 3)))
      (.binOp .mod (.var 0) (.var 1))
  let c1 ← mkPTXKernelCase "ptx_map_scale_add" "ln_ptx_map_scale_add" (.mapScaleAdd 3 7) vecs1
  let c2 ← mkPTXKernelCase "ptx_zip_add" "ln_ptx_zip_add" .zipAdd vecs2
  let c3 ← mkPTXKernelCase "ptx_zip_mul" "ln_ptx_zip_mul" .zipMul vecs2
  let c4 ← mkPTXKernelCase "ptx_saxpy" "ln_ptx_saxpy" (.saxpy 5) vecs2
  let c5 ← mkPTXKernelCase "ptx_stencil1d" "ln_ptx_stencil1d" (.stencil1D3Pt 2 5 3) vecs1
  let c6 ← mkPTXKernelCase "ptx_custom_sub" "ln_ptx_sub" (.customScalar 9 [0, 1] subBody) vecs2
    (some (ptxMutantM7Kernel "ln_ptx_sub" 9 [0, 1] subBody, "M7 swapped sub.u64 operands"))
  let c7 ← mkPTXKernelCase "ptx_custom_lt" "ln_ptx_lt" (.customScalar 9 [0, 1] ltBody) vecs2
    (some (ptxMutantM8Kernel "ln_ptx_lt" 9 [0, 1] ltBody, "M8 setp.lt.u64 weakened to setp.le.u64"))
  let c8 ← mkPTXKernelCase "ptx_custom_div_zero_safe" "ln_ptx_div" (.customScalar 9 [0, 1] divBody) vecs2
  let c9 ← mkPTXKernelCase "ptx_custom_shl_mask" "ln_ptx_shl" (.customScalar 9 [0, 1] shlBody) vecs2
  let c10 ← mkPTXKernelCase "ptx_custom_select_fma_mod" "ln_ptx_mix" (.customScalar 9 [0, 1] mixBody) vecs2
  pure [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10]

private def buildMetalCases : Except String (List MetalCase) := do
  let vecs1 : List (List (List UInt64)) :=
    [ [[0, 1, 7, 42]], [[10, 20, 30, 40, 50]], [[0xffffffffffffffff, 0x8000000000000000, 3]] ]
  let vecs2 : List (List (List UInt64)) :=
    [ [[18, 7, 100, 0xffffffffffffffff], [3, 0, 37, 1]]
    , [[1, 3, 7, 0x123456789abcdef0], [32, 65, 7, 19]]
    , [[5, 2, 9, 42], [2, 5, 9, 0]] ]
  let divBody : ScalarExpr := .binOp .div (.var 0) (.var 1)
  let shlBody : ScalarExpr := .binOp .shl (.var 0) (.var 1)
  let subBody : ScalarExpr := .binOp .sub (.var 0) (.var 1)
  let mixBody : ScalarExpr :=
    .select (.binOp .lt (.var 0) (.var 1))
      (.fma (.var 0) (.constU64 7) (.var 1))
      (.binOp .bitXor (.binOp .shr (.var 0) (.var 1)) (.unaryOp .not (.var 1)))
  let m1 ← mkMetalKernelCase "metal_map_scale_add" "ln_msl_map_scale_add" (.mapScaleAdd 3 7) vecs1
  let m2 ← mkMetalKernelCase "metal_zip_add" "ln_msl_zip_add" .zipAdd vecs2
  let m3 ← mkMetalKernelCase "metal_zip_mul" "ln_msl_zip_mul" .zipMul vecs2
  let m4 ← mkMetalKernelCase "metal_saxpy" "ln_msl_saxpy" (.saxpy 5) vecs2
  let m5 ← mkMetalKernelCase "metal_stencil1d" "ln_msl_stencil1d" (.stencil1D3Pt 2 5 3) vecs1
  let m6 ← mkMetalKernelCase "metal_custom_div" "ln_msl_div" (.customScalar 9 [0, 1] divBody) vecs2
    (some (metalMutantM9Kernel "ln_msl_div" 9 [0, 1] divBody, "M9 unguarded Metal division by zero"))
  let m7 ← mkMetalKernelCase "metal_custom_shl" "ln_msl_shl" (.customScalar 9 [0, 1] shlBody) vecs2
    (some (metalMutantM10Kernel "ln_msl_shl" 9 [0, 1] shlBody, "M10 narrowed shift mask & 31UL"))
  let m8 ← mkMetalKernelCase "metal_custom_sub" "ln_msl_sub" (.customScalar 9 [0, 1] subBody) vecs2
  let m9 ← mkMetalKernelCase "metal_custom_select_fma" "ln_msl_mix" (.customScalar 9 [0, 1] mixBody) vecs2
  pure [m1, m2, m3, m4, m5, m6, m7, m8, m9]

private def hloSignedShiftRemFn : FuncOp :=
  let ty : TensorType := { shape := [], elem := .i64 }
  { name := "hlo_signed_sdiv_srem_ashr"
  , params := [("a", ty), ("b", ty)]
  , result := ty
  , body :=
      [ .constant "c1" { ty := ty, data := #[1#64] }
      , .constant "c3" { ty := ty, data := #[3#64] }
      , .or "b_nz" "b" "c1"
      , .divide "q" "a" "b_nz"
      , .remainder "r" "a" "b_nz"
      , .shiftRightArithmetic "sa" "a" "c3"
      , .maximum "mx" "q" "r"
      , .minimum "mn" "mx" "sa"
      , .add "res" "mx" "mn"
      , .returnOp "res" ] }

private def hloTensorOpsFn : FuncOp :=
  let mTy : TensorType := { shape := [2, 2], elem := .ui64 }
  let scTy : TensorType := { shape := [], elem := .ui64 }
  { name := "hlo_dot_reduce_slice_dyn"
  , params := [("lhs", mTy), ("rhs", mTy)]
  , result := scTy
  , body :=
      [ .dotGeneral "prod" "lhs" "rhs" [] [] [1] [0] [2, 2]
      , .slice "row0" "prod" [0, 0] [1, 2] [1, 1]
      , .reshape "vec2" "row0" [2]
      , .constant "idx1" { ty := scTy, data := #[1#64] }
      , .dynamicSlice "ds" "vec2" ["idx1"] [1]
      , .reshape "elem1" "ds" []
      , .constant "zero" { ty := scTy, data := #[0#64] }
      , .reduce "sum_all" "prod" "zero" [0, 1] "add" []
      , .add "res" "sum_all" "elem1"
      , .returnOp "res" ] }

private def buildStableHLOCases : Except String (List StableHLOCase) := do
  let scPairs : List (List TensorVal) :=
    [ [scUi64Val 5, scUi64Val 2]
    , [scUi64Val 2, scUi64Val 5]
    , [scUi64Val 18, scUi64Val 0]
    , [scUi64Val 1, scUi64Val 65]
    , [scUi64Val 0xffffffffffffffff, scUi64Val 3]
    , [scUi64Val 7, scUi64Val 7] ]
  let scSignedPairs : List (List TensorVal) :=
    [ [scI64Val 0xffffffffffffff9c, scI64Val 7]
    , [scI64Val 100, scI64Val 0xfffffffffffffffb]
    , [scI64Val 0x8000000000000000, scI64Val 3] ]
  let dSub := mkBinScalarDecl "lnir_hlo_sub" .i64 (.binOp .sub (.var 0) (.var 1))
  let dShl := mkBinScalarDecl "lnir_hlo_shl" .i64 (.binOp .shl (.var 0) (.var 1))
  let dDiv := mkBinScalarDecl "lnir_hlo_div" .i64 (.binOp .div (.var 0) (.var 1))
  let dIte : LNIRDecl :=
    { name := "lnir_hlo_ite_select"
    , params := [{ id := 0, name := "a", ty := .i64 }, { id := 1, name := "b", ty := .i64 }]
    , retTy := .i64
    , body :=
        .letBind 2 .i1 (.scalar (.binOp .lt (.var 0) (.var 1)))
          (.ite 2
            (.letBind 3 .i64 (.scalar (.fma (.var 0) (.constU64 3) (.var 1))) (.ret 3))
            (.letBind 4 .i64 (.scalar (.binOp .bitXor (.var 0) (.binOp .shr (.var 1) (.constU64 1)))) (.ret 4))) }
  let dSaxpyVec : LNIRDecl :=
    { name := "lnir_hlo_saxpy_vec4"
    , params := [{ id := 0, name := "x", ty := .sarray .i64 }, { id := 1, name := "y", ty := .sarray .i64 }]
    , retTy := .sarray .i64
    , body := .letBind 2 .i64 (.sarrayLen 0) (.parFor 3 2 [0, 1] .i64 (.saxpy 5) (.ret 3)) }
  let dDotSlice : LNIRDecl :=
    { name := "lnir_hlo_dot_vec4"
    , params := [{ id := 0, name := "x", ty := .sarray .i64 }, { id := 1, name := "y", ty := .sarray .i64 }]
    , retTy := .i64
    , body :=
        .letBind 2 .i64 (.sarrayLen 0)
          (.parFor 3 2 [0, 1] .i64 .dotProduct
            (.letBind 4 .i64 (.scalar (.constU64 0))
              (.letBind 5 .i64 (.sarrayGet 3 4 .i64) (.ret 5)))) }
  let some fSub := lowerToStableHLO dSub 0 | throw "lowerToStableHLO failed on lnir_hlo_sub"
  let some fShl := lowerToStableHLO dShl 0 | throw "lowerToStableHLO failed on lnir_hlo_shl"
  let some fDiv := lowerToStableHLO dDiv 0 | throw "lowerToStableHLO failed on lnir_hlo_div"
  let some fIte := lowerToStableHLO dIte 0 | throw "lowerToStableHLO failed on lnir_hlo_ite_select"
  let some fSaxpy := lowerToStableHLO dSaxpyVec 4 | throw "lowerToStableHLO failed on lnir_hlo_saxpy_vec4"
  let some fDot := lowerToStableHLO dDotSlice 4 | throw "lowerToStableHLO failed on lnir_hlo_dot_vec4"
  let vec4Pairs : List (List TensorVal) :=
    [ [vecUi64Val [1, 2, 3, 4], vecUi64Val [10, 20, 30, 40]]
    , [vecUi64Val [0xffffffffffffffff, 0, 7, 9], vecUi64Val [1, 42, 3, 5]] ]
  let mat2Pairs : List (List TensorVal) :=
    [ [matUi64Val 2 2 [1, 2, 3, 4], matUi64Val 2 2 [5, 6, 7, 8]]
    , [matUi64Val 2 2 [2, 0, 1, 3], matUi64Val 2 2 [4, 1, 2, 5]] ]
  let s1 ← mkStableHLOCase "hlo_lowered_sub" "mod_sub" fSub scPairs
    (some (hloMutantSubSwap, "H1 swapped subtract operands"))
  let s2 ← mkStableHLOCase "hlo_lowered_shl" "mod_shl" fShl scPairs
    (some (hloMutantUnmaskedShl, "H2 unmasked shiftLeft poison on >= 64"))
  let s3 ← mkStableHLOCase "hlo_lowered_div" "mod_div" fDiv scPairs
    (some (hloMutantUnguardedDiv, "H3 unguarded divide by zero"))
  let s4 ← mkStableHLOCase "hlo_lowered_ite_fma" "mod_ite" fIte scPairs
  let s5 ← mkStableHLOCase "hlo_lowered_saxpy_vec4" "mod_saxpy" fSaxpy vec4Pairs
  let s6 ← mkStableHLOCase "hlo_lowered_dot_vec4" "mod_dot" fDot vec4Pairs
  let s7 ← mkStableHLOCase "hlo_signed_sdiv_srem_ashr" "mod_signed" hloSignedShiftRemFn scSignedPairs
  let s8 ← mkStableHLOCase "hlo_dot_reduce_slice_dyn" "mod_tensor" hloTensorOpsFn mat2Pairs
  pure [s1, s2, s3, s4, s5, s6, s7, s8]

private def ptxCaseToJson (c : PTXCase) : Json :=
  let base : List (String × Json) :=
    [ ("id", Json.str c.id)
    , ("kernelName", Json.str c.kernelName)
    , ("arity", toJson c.arity)
    , ("ptxText", Json.str c.ptxText)
    , ("vectors", Json.arr (c.vectors.map fun v =>
        Json.mkObj [
          ("inputs", Json.arr (v.inputs.map u64ArrJson).toArray),
          ("expected", u64ArrJson v.expected)
        ]).toArray) ]
  let extra :=
    match c.negativeMutantPtx?, c.negativeMutantReason? with
    | some m, some r => [("negativeMutantPtx", Json.str m), ("negativeMutantReason", Json.str r)]
    | _, _ => []
  Json.mkObj (base ++ extra)

private def metalCaseToJson (c : MetalCase) : Json :=
  let base : List (String × Json) :=
    [ ("id", Json.str c.id)
    , ("kernelName", Json.str c.kernelName)
    , ("arity", toJson c.arity)
    , ("mslText", Json.str c.mslText)
    , ("vectors", Json.arr (c.vectors.map fun v =>
        Json.mkObj [
          ("inputs", Json.arr (v.inputs.map u64ArrJson).toArray),
          ("expected", u64ArrJson v.expected)
        ]).toArray) ]
  let extra :=
    match c.negativeMutantMsl?, c.negativeMutantReason? with
    | some m, some r => [("negativeMutantMsl", Json.str m), ("negativeMutantReason", Json.str r)]
    | _, _ => []
  Json.mkObj (base ++ extra)

private def stableHLOCaseToJson (c : StableHLOCase) : Json :=
  let base : List (String × Json) :=
    [ ("id", Json.str c.id)
    , ("fnName", Json.str c.fnName)
    , ("mlirText", Json.str c.mlirText)
    , ("vectors", Json.arr (c.vectors.map fun v =>
        Json.mkObj [
          ("args", Json.arr (v.args.map tensorValJson).toArray),
          ("expected", tensorValJson v.expected)
        ]).toArray) ]
  let extra :=
    match c.negativeMutantMlir?, c.negativeMutantReason? with
    | some m, some r => [("negativeMutantMlir", Json.str m), ("negativeMutantReason", Json.str r)]
    | _, _ => []
  Json.mkObj (base ++ extra)

private def snarkProbeModule : LNIRModule :=
  let rotr32Body : ScalarExpr :=
    let x32 : ScalarExpr := .binOp .bitAnd (.binOp .bitXor (.var 0) (.var 1)) (.constU64 0xffffffff)
    .binOp .bitAnd
      (.binOp .bitOr
        (.binOp .shr x32 (.var 2))
        (.binOp .shl x32 (.binOp .sub (.constU64 32) (.var 2))))
      (.constU64 0xffffffff)
  { probeMod with
    moduleName := "Stage3GPUDiffSuite"
    decls := probeMod.decls ++
      [ mkBinScalarDecl "snark_fast_ghash_mul_lo" .i64 (.binOp .clmul64 (.var 0) (.var 1))
      , mkBinScalarDecl "snark_fast_ntt_btf_u_lo" .i64 (.binOp .bitXor (.var 0) (.var 1))
      , mkTernScalarDecl "snark_fast_ntt_btf_v_lo" .i64
          (.binOp .bitXor (.binOp .bitXor (.var 0) (.var 2)) (.var 1))
      , mkBinScalarDecl "snark_fast_blake3_add_sum" .i64
          (.binOp .bitAnd (.binOp .add (.var 0) (.var 1)) (.constU64 0xffffffff))
      , mkTernScalarDecl "snark_fast_blake3_xor_rotr32" .i64 rotr32Body
      , mkTernScalarDecl "snark_fast_blake3_finalize_word_pair" .i64
          (.binOp .bitAnd (.binOp .bitXor (.var 0) (.var 1)) (.constU64 0xffffffff)) ] }

def run (_args : List String) : IO UInt32 := do
  let ptxCases ← match buildPTXCases with
    | .ok cs => pure cs
    | .error err => do IO.eprintln s!"[gpu-tpu-diff-suite] PTX case synthesis failed: {err}"; return 1
  let metalCases ← match buildMetalCases with
    | .ok cs => pure cs
    | .error err => do IO.eprintln s!"[gpu-tpu-diff-suite] Metal case synthesis failed: {err}"; return 1
  let hloCases ← match buildStableHLOCases with
    | .ok cs => pure cs
    | .error err => do IO.eprintln s!"[gpu-tpu-diff-suite] StableHLO case synthesis failed: {err}"; return 1
  let prodPTX := emitPTXModule probeMod
  let prodStableHLO := emitStableHLOModule probeMod
  let prodMetal := emitMetalModule snarkProbeModule
  let prodFastCheckMetal := emitFastCheckMetal probeMod
  let out := Json.mkObj [
    ("schema", toJson (1 : Nat)),
    ("productionModules", Json.mkObj [
      ("ptxModule", Json.str prodPTX),
      ("stablehloTpuModule", Json.str prodStableHLO),
      ("metalModule", Json.str prodMetal),
      ("metalFastCheckModule", Json.str prodFastCheckMetal)
    ]),
    ("ptxCases", Json.arr (ptxCases.map ptxCaseToJson).toArray),
    ("metalCases", Json.arr (metalCases.map metalCaseToJson).toArray),
    ("stablehloCases", Json.arr (hloCases.map stableHLOCaseToJson).toArray)
  ]
  IO.println (Json.compress out)
  return 0

end LeanNative.Driver.GPUDiffCLI
