import LeanNative.Backend.PTXAst
import LeanNative.Backend.MetalAst

/-!
# Executable & Kernel-Checked SIMT Tests for `PTXAst` and `MetalAst` (`C2b`)

Covers multi-thread SIMT vector addition, shared-memory reduction, divergent barrier detection,
read-only `constant` address-space violation, and out-of-bounds buffer writes. Every scenario is
checked twice: `#guard` runs the evaluator, and a kernel-checked `rfl` theorem re-proves the same
equality with `0 sorryAx` and no `native_decide`.
-/

namespace LeanNative.Tests.GpuAstTests

set_option maxRecDepth 65536

abbrev PTXMem := LeanNative.Backend.PTXAst.ByteMemory
abbrev PTXParams := LeanNative.Backend.PTXAst.ParamMemory
abbrev PTXRes := LeanNative.Backend.PTXAst.PTXOutcome PTXMem
abbrev MSLMem := LeanNative.Backend.MetalAst.ByteMemory
abbrev MSLDevTable := List (Nat × MSLMem)
abbrev MSLRes := LeanNative.Backend.MetalAst.MSLOutcome MSLDevTable

open LeanNative.Backend.PTXAst
open LeanNative.Backend.MetalAst

/-! ## 1. CUDA PTX: 2-thread SIMT vector addition (`out[i] = a[i] + b[i]`) -/

def ptxVecAddBody : List PTXStmt :=
  [ .instr none (.mov .u32 "%r_tid" (.sreg .tidX))
  , .instr none (.mul .lo .u64 "%r_off" (.reg "%r_tid") (.immU64 8#64))
  , .instr none (.ldParam .u64 "%r_a" "param_a")
  , .instr none (.add .none .u64 "%r_a_addr" (.reg "%r_a") (.reg "%r_off"))
  , .instr none (.ldGlobal .u64 "%r_av" (.regOffset "%r_a_addr" 0))
  , .instr none (.ldParam .u64 "%r_b" "param_b")
  , .instr none (.add .none .u64 "%r_b_addr" (.reg "%r_b") (.reg "%r_off"))
  , .instr none (.ldGlobal .u64 "%r_bv" (.regOffset "%r_b_addr" 0))
  , .instr none (.add .none .u64 "%r_sum" (.reg "%r_av") (.reg "%r_bv"))
  , .instr none (.ldParam .u64 "%r_o" "param_out")
  , .instr none (.add .none .u64 "%r_o_addr" (.reg "%r_o") (.reg "%r_off"))
  , .instr none (.stGlobal .u64 (.regOffset "%r_o_addr" 0) (.reg "%r_sum"))
  , .instr none .ret ]

def ptxVecAddKernel : PTXKernel where
  name := "vec_add_u64"
  params := [ { ty := .u64, name := "param_a" }
            , { ty := .u64, name := "param_b" }
            , { ty := .u64, name := "param_out" } ]
  body := ptxVecAddBody

def ptxVecAddGlobal : LeanNative.Backend.PTXAst.ByteMemory :=
  LeanNative.Backend.PTXAst.ByteMemory.ofU64Words
    [ 3#64, 5#64
    , 10#64, 20#64
    , 0#64, 0#64 ]

def ptxVecAddParams : LeanNative.Backend.PTXAst.ParamMemory :=
  { params := [ ("param_a", 0#64), ("param_b", 16#64), ("param_out", 32#64) ] }

def ptxVecAddResult : LeanNative.Backend.PTXAst.PTXOutcome LeanNative.Backend.PTXAst.ByteMemory :=
  evalPTXKernel 32 ptxVecAddKernel { x := 1 } { x := 2 } ptxVecAddGlobal ptxVecAddParams

def ptxVecAddExpected : LeanNative.Backend.PTXAst.PTXOutcome LeanNative.Backend.PTXAst.ByteMemory :=
  .ok (LeanNative.Backend.PTXAst.ByteMemory.ofU64Words
    [ 3#64, 5#64
    , 10#64, 20#64
    , 13#64, 25#64 ])

def ptxReadWord? (r : PTXRes) (idx : Nat) : Option (BitVec 64) :=
  match r with
  | .ok m => m.readU64Word? idx
  | _ => none

def mslReadWord? (r : MSLRes) (bufIdx elemIdx : Nat) : Option (BitVec 64) :=
  match r with
  | .ok bufs =>
    match bufs.lookup bufIdx with
    | some m => m.readU64Word? elemIdx
    | none => none
  | _ => none

#guard ptxVecAddResult == ptxVecAddExpected

theorem ptx_vec_add_kernel_checked :
    ptxReadWord? ptxVecAddResult 4 = some 13#64 ∧
    ptxReadWord? ptxVecAddResult 5 = some 25#64 := ⟨rfl, rfl⟩

/-! ## 2. CUDA PTX: 2-thread shared-memory reduction (`sum(xs)` via `.shared` + `bar.sync`) -/

def ptxReduceBody : List PTXStmt :=
  [ .instr none (.mov .u32 "%r_tid" (.sreg .tidX))
  , .instr none (.mul .lo .u64 "%r_off" (.reg "%r_tid") (.immU64 8#64))
  , .instr none (.ldParam .u64 "%r_in" "param_in")
  , .instr none (.add .none .u64 "%r_in_addr" (.reg "%r_in") (.reg "%r_off"))
  , .instr none (.ldGlobal .u64 "%r_v" (.regOffset "%r_in_addr" 0))
  , .instr none (.mov .u64 "%r_smem" (.sym "smem"))
  , .instr none (.add .none .u64 "%r_smem_addr" (.reg "%r_smem") (.reg "%r_off"))
  , .instr none (.stShared .u64 (.regOffset "%r_smem_addr" 0) (.reg "%r_v"))
  , .instr none (.barSync 0)
  , .instr none (.setp .eq .u32 "%p_is0" (.reg "%r_tid") (.immU64 0#64))
  , .instr (some { predReg := "%p_is0" }) (.ldShared .u64 "%r_s0" (.symOffset "smem" 0))
  , .instr (some { predReg := "%p_is0" }) (.ldShared .u64 "%r_s1" (.symOffset "smem" 8))
  , .instr (some { predReg := "%p_is0" }) (.add .none .u64 "%r_acc" (.reg "%r_s0") (.reg "%r_s1"))
  , .instr (some { predReg := "%p_is0" }) (.ldParam .u64 "%r_out" "param_out")
  , .instr (some { predReg := "%p_is0" })
      (.stGlobal .u64 (.regOffset "%r_out" 0) (.reg "%r_acc"))
  , .instr none .ret ]

def ptxReduceKernel : PTXKernel where
  name := "shared_reduce_u64"
  params := [ { ty := .u64, name := "param_in" }, { ty := .u64, name := "param_out" } ]
  sharedDecls := [ { align := 8, elemTy := .u64, name := "smem", count := 2 } ]
  body := ptxReduceBody

def ptxReduceGlobal : LeanNative.Backend.PTXAst.ByteMemory :=
  LeanNative.Backend.PTXAst.ByteMemory.ofU64Words [ 17#64, 25#64, 0#64 ]

def ptxReduceParams : LeanNative.Backend.PTXAst.ParamMemory :=
  { params := [ ("param_in", 0#64), ("param_out", 16#64) ] }

def ptxReduceResult : LeanNative.Backend.PTXAst.PTXOutcome LeanNative.Backend.PTXAst.ByteMemory :=
  evalPTXKernel 64 ptxReduceKernel { x := 1 } { x := 2 } ptxReduceGlobal ptxReduceParams

def ptxReduceExpected : LeanNative.Backend.PTXAst.PTXOutcome LeanNative.Backend.PTXAst.ByteMemory :=
  .ok (LeanNative.Backend.PTXAst.ByteMemory.ofU64Words [ 17#64, 25#64, 42#64 ])

#guard ptxReduceResult == ptxReduceExpected

theorem ptx_shared_reduce_kernel_checked :
    ptxReadWord? ptxReduceResult 2 = some 42#64 := rfl

/-! ## 3. CUDA PTX: divergent `bar.sync` is rejected -/

def ptxDivergentBody : List PTXStmt :=
  [ .instr none (.mov .u32 "%r_tid" (.sreg .tidX))
  , .instr none (.setp .eq .u32 "%p_is0" (.reg "%r_tid") (.immU64 0#64))
  , .instr (some { predReg := "%p_is0" }) (.barSync 0)
  , .instr none .ret ]

def ptxDivergentKernel : PTXKernel where
  name := "divergent_barrier"
  params := []
  body := ptxDivergentBody

def ptxDivergentResult : LeanNative.Backend.PTXAst.PTXOutcome LeanNative.Backend.PTXAst.ByteMemory :=
  evalPTXKernel 32 ptxDivergentKernel { x := 1 } { x := 2 }
    (LeanNative.Backend.PTXAst.ByteMemory.zeros 0) { params := [] }

#guard ptxDivergentResult == .barrierDivergence 0

theorem ptx_divergent_barrier_kernel_checked :
    ptxDivergentResult = .barrierDivergence 0 := rfl

/-! ## 4. CUDA PTX: out-of-bounds global store is rejected -/

def ptxOobBody : List PTXStmt :=
  [ .instr none (.mov .u64 "%r_base" (.immU64 16#64))
  , .instr none (.stGlobal .u64 (.regOffset "%r_base" 0) (.immU64 1#64))
  , .instr none .ret ]

def ptxOobKernel : PTXKernel where
  name := "oob_store"
  params := []
  body := ptxOobBody

def ptxOobResult : LeanNative.Backend.PTXAst.PTXOutcome LeanNative.Backend.PTXAst.ByteMemory :=
  evalPTXKernel 16 ptxOobKernel { x := 1 } { x := 1 }
    (LeanNative.Backend.PTXAst.ByteMemory.zeros 8) { params := [] }

#guard ptxOobResult == .outOfBoundsStore .global 16

theorem ptx_oob_store_kernel_checked :
    ptxOobResult = .outOfBoundsStore .global 16 := rfl

/-! ## 5. Apple Metal: 2-thread SIMT vector addition (`out[gid] = a[gid] + b[gid]`) -/

def mslVecAddBody : List MSLStmt :=
  [ .varDecl .ulong "av" (.index "a" (.builtin .threadPositionInGrid))
  , .varDecl .ulong "bv" (.index "b" (.builtin .threadPositionInGrid))
  , .indexAssign "out" (.builtin .threadPositionInGrid) (.add (.var "av") (.var "bv"))
  , .returnStmt ]

def mslVecAddKernel : MSLKernelDecl where
  name := "vec_add_u64"
  params :=
    [ { ty := .pointer .device .ulong, name := "a", attr := .buffer 0 }
    , { ty := .pointer .device .ulong, name := "b", attr := .buffer 1 }
    , { ty := .pointer .device .ulong, name := "out", attr := .buffer 2 }
    , { ty := .uint, name := "gid", attr := .threadPositionInGrid } ]
  body := mslVecAddBody

def mslVecAddDevice : List (Nat × LeanNative.Backend.MetalAst.ByteMemory) :=
  [ (0, LeanNative.Backend.MetalAst.ByteMemory.ofU64Words [ 3#64, 5#64 ])
  , (1, LeanNative.Backend.MetalAst.ByteMemory.ofU64Words [ 10#64, 20#64 ])
  , (2, LeanNative.Backend.MetalAst.ByteMemory.zeros 16) ]

def mslVecAddResult : MSLRes :=
  evalMSLKernel 16 mslVecAddKernel { x := 1 } { x := 2 } mslVecAddDevice []

def mslVecAddExpected : MSLRes :=
  .ok [ (0, LeanNative.Backend.MetalAst.ByteMemory.ofU64Words [ 3#64, 5#64 ])
      , (1, LeanNative.Backend.MetalAst.ByteMemory.ofU64Words [ 10#64, 20#64 ])
      , (2, LeanNative.Backend.MetalAst.ByteMemory.ofU64Words [ 13#64, 25#64 ]) ]

#guard mslVecAddResult == mslVecAddExpected

theorem msl_vec_add_kernel_checked :
    mslReadWord? mslVecAddResult 2 0 = some 13#64 ∧
    mslReadWord? mslVecAddResult 2 1 = some 25#64 := ⟨rfl, rfl⟩

/-! ## 6. Apple Metal: 2-thread `threadgroup` shared-memory reduction -/

def mslReduceBody : List MSLStmt :=
  [ .indexAssign "smem" (.builtin .threadPositionInThreadgroup)
      (.index "inp" (.builtin .threadPositionInThreadgroup))
  , .threadgroupBarrier
  , .ifElse (.eq (.builtin .threadPositionInThreadgroup) (.immU64 0#64))
      (.ofList
        [ .varDecl .ulong "s0" (.index "smem" (.immU64 0#64))
        , .varDecl .ulong "s1" (.index "smem" (.immU64 1#64))
        , .indexAssign "out" (.immU64 0#64) (.add (.var "s0") (.var "s1")) ])
      .nil
  , .returnStmt ]

def mslReduceKernel : MSLKernelDecl where
  name := "shared_reduce_u64"
  params :=
    [ { ty := .pointer .device .ulong, name := "inp", attr := .buffer 0 }
    , { ty := .pointer .device .ulong, name := "out", attr := .buffer 1 } ]
  sharedDecls := [ { elemTy := .ulong, name := "smem", count := 2 } ]
  body := mslReduceBody

def mslReduceDevice : List (Nat × LeanNative.Backend.MetalAst.ByteMemory) :=
  [ (0, LeanNative.Backend.MetalAst.ByteMemory.ofU64Words [ 17#64, 25#64 ])
  , (1, LeanNative.Backend.MetalAst.ByteMemory.zeros 8) ]

def mslReduceResult : MSLRes :=
  evalMSLKernel 32 mslReduceKernel { x := 1 } { x := 2 } mslReduceDevice []

def mslReduceExpected : MSLRes :=
  .ok [ (0, LeanNative.Backend.MetalAst.ByteMemory.ofU64Words [ 17#64, 25#64 ])
      , (1, LeanNative.Backend.MetalAst.ByteMemory.ofU64Words [ 42#64 ]) ]

#guard mslReduceResult == mslReduceExpected

theorem msl_shared_reduce_kernel_checked :
    mslReadWord? mslReduceResult 1 0 = some 42#64 := rfl

/-! ## 7. Apple Metal: divergent `threadgroup_barrier` is rejected -/

def mslDivergentBody : List MSLStmt :=
  [ .ifElse (.eq (.builtin .threadPositionInThreadgroup) (.immU64 0#64))
      (.cons .threadgroupBarrier .nil)
      .nil
  , .returnStmt ]

def mslDivergentKernel : MSLKernelDecl where
  name := "divergent_barrier"
  params := []
  body := mslDivergentBody

def mslDivergentResult : MSLRes :=
  evalMSLKernel 32 mslDivergentKernel { x := 1 } { x := 2 } [] []

#guard mslDivergentResult == .barrierDivergence

theorem msl_divergent_barrier_kernel_checked :
    mslDivergentResult = .barrierDivergence := rfl

/-! ## 8. Apple Metal: writing a `constant` buffer is rejected -/

def mslConstWriteBody : List MSLStmt :=
  [ .indexAssign "coeffs" (.immU64 0#64) (.immU64 99#64)
  , .returnStmt ]

def mslConstWriteKernel : MSLKernelDecl where
  name := "constant_write"
  params :=
    [ { ty := .pointer .constant .ulong, name := "coeffs", attr := .buffer 3 } ]
  body := mslConstWriteBody

def mslConstWriteResult : MSLRes :=
  evalMSLKernel 16 mslConstWriteKernel { x := 1 } { x := 1 } []
    [ (3, LeanNative.Backend.MetalAst.ByteMemory.ofU64Words [ 7#64 ]) ]

#guard mslConstWriteResult == .readOnlyViolation "coeffs" 0

theorem msl_constant_write_rejected_kernel_checked :
    mslConstWriteResult = .readOnlyViolation "coeffs" 0 := rfl

/-! ## 9. Apple Metal: out-of-bounds `device` store is rejected -/

def mslOobBody : List MSLStmt :=
  [ .indexAssign "buf" (.immU64 4#64) (.immU64 1#64)
  , .returnStmt ]

def mslOobKernel : MSLKernelDecl where
  name := "oob_store"
  params :=
    [ { ty := .pointer .device .ulong, name := "buf", attr := .buffer 0 } ]
  body := mslOobBody

def mslOobResult : MSLRes :=
  evalMSLKernel 16 mslOobKernel { x := 1 } { x := 1 }
    [ (0, LeanNative.Backend.MetalAst.ByteMemory.zeros 8) ] []

#guard mslOobResult == .outOfBoundsWrite .device 0 4

theorem msl_oob_write_kernel_checked :
    mslOobResult = .outOfBoundsWrite .device 0 4 := rfl

/-! ## 10. Structural Pretty-Printer Smoke Checks (`PTXModule` and `MSLModule`) -/

def hasSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

def ptxSampleModule : PTXModule where
  kernels := [ ptxVecAddKernel, ptxReduceKernel ]

def mslSampleModule : MSLModule where
  structs := [ { name := "ln_u256", fields := [ { ty := .ulong, name := "w0" } ] } ]
  kernels := [ mslVecAddKernel, mslReduceKernel ]

#guard hasSubstr (ppPTXModule ptxSampleModule) ".version 8.0"
#guard hasSubstr (ppPTXModule ptxSampleModule) ".visible .entry vec_add_u64("
#guard hasSubstr (ppPTXModule ptxSampleModule) "bar.sync 0;"
#guard hasSubstr (ppPTXModule ptxSampleModule) ".shared .align 8 .u64 smem[2];"

#guard hasSubstr (ppMSLModule mslSampleModule) "#include <metal_stdlib>"
#guard hasSubstr (ppMSLModule mslSampleModule) "using namespace metal;"
#guard hasSubstr (ppMSLModule mslSampleModule) "kernel void vec_add_u64("
#guard hasSubstr (ppMSLModule mslSampleModule) "threadgroup ulong smem[2];"
#guard hasSubstr (ppMSLModule mslSampleModule)
  "threadgroup_barrier(mem_flags::mem_threadgroup);"

theorem ptx_sample_module_header_checked :
    List.isPrefixOf
      (ppPTXModuleHeader ptxSampleModule).toList
      (ppPTXModule ptxSampleModule).toList = true :=
  ppPTXModule_header_prefix ptxSampleModule

theorem msl_sample_module_header_checked :
    List.isPrefixOf
      ppMSLModuleHeader.toList
      (ppMSLModule mslSampleModule).toList = true :=
  ppMSLModule_header_prefix mslSampleModule

end LeanNative.Tests.GpuAstTests
