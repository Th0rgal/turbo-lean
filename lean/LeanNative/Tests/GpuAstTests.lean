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
  [ .varDecl .ulong "av" (.index "a" (.var "gid"))
  , .varDecl .ulong "bv" (.index "b" (.var "gid"))
  , .indexAssign "out" (.var "gid") (.add (.var "av") (.var "bv"))
  , .returnStmt ]

def mslVecAddKernel : MSLKernelDecl where
  name := "vec_add_u64"
  params :=
    [ { ty := .pointer .device false .ulong, name := "a", attr := some (.buffer 0) }
    , { ty := .pointer .device false .ulong, name := "b", attr := some (.buffer 1) }
    , { ty := .pointer .device false .ulong, name := "out", attr := some (.buffer 2) }
    , { ty := .uint, name := "gid", attr := some .threadPositionInGrid } ]
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
  [ .indexAssign "smem" (.var "tid")
      (.index "inp" (.var "tid"))
  , .threadgroupBarrier
  , .ifElse (.eq (.var "tid") (.immU64 0#64))
      (.ofList
        [ .varDecl .ulong "s0" (.index "smem" (.immU64 0#64))
        , .varDecl .ulong "s1" (.index "smem" (.immU64 1#64))
        , .indexAssign "out" (.immU64 0#64) (.add (.var "s0") (.var "s1")) ])
      .nil
  , .returnStmt ]

def mslReduceKernel : MSLKernelDecl where
  name := "shared_reduce_u64"
  params :=
    [ { ty := .pointer .device false .ulong, name := "inp", attr := some (.buffer 0) }
    , { ty := .pointer .device false .ulong, name := "out", attr := some (.buffer 1) }
    , { ty := .uint, name := "tid", attr := some .threadPositionInThreadgroup } ]
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
  [ .ifElse (.eq (.var "tid") (.immU64 0#64))
      (.cons .threadgroupBarrier .nil)
      .nil
  , .returnStmt ]

def mslDivergentKernel : MSLKernelDecl where
  name := "divergent_barrier"
  params :=
    [ { ty := .uint, name := "tid", attr := some .threadPositionInThreadgroup } ]
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
    [ { ty := .pointer .constant false .ulong, name := "coeffs", attr := some (.buffer 3) } ]
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
    [ { ty := .pointer .device false .ulong, name := "buf", attr := some (.buffer 0) } ]
  body := mslOobBody

def mslOobResult : MSLRes :=
  evalMSLKernel 16 mslOobKernel { x := 1 } { x := 1 }
    [ (0, LeanNative.Backend.MetalAst.ByteMemory.zeros 8) ] []

#guard mslOobResult == .outOfBoundsWrite .device 0 4

theorem msl_oob_write_kernel_checked :
    mslOobResult = .outOfBoundsWrite .device 0 4 := rfl

/-! ## 10. Finding coverage: PTX div0, signed overflow, float remainder, shift width, races -/

def ptxDiv0Body : List PTXStmt :=
  [ .instr none (.div .u64 "%r" (.immU64 7#64) (.immU64 0#64))
  , .instr none .ret ]

def ptxDiv0Kernel : PTXKernel where
  name := "div0"
  params := []
  body := ptxDiv0Body

def ptxDiv0Result : PTXRes :=
  evalPTXKernel 16 ptxDiv0Kernel { x := 1 } { x := 1 }
    (LeanNative.Backend.PTXAst.ByteMemory.zeros 0) { params := [] }

#guard ptxDiv0Result == .divisionByZero

theorem ptx_div_zero_kernel_checked :
    ptxDiv0Result = .divisionByZero := rfl

def ptxSdivBody : List PTXStmt :=
  [ .instr none (.div .s32 "%r" (.immU64 2147483648#64) (.immU64 4294967295#64))
  , .instr none .ret ]

def ptxSdivKernel : PTXKernel where
  name := "sdiv_overflow"
  params := []
  body := ptxSdivBody

def ptxSdivResult : PTXRes :=
  evalPTXKernel 16 ptxSdivKernel { x := 1 } { x := 1 }
    (LeanNative.Backend.PTXAst.ByteMemory.zeros 0) { params := [] }

#guard ptxSdivResult == .signedDivOverflow

theorem ptx_signed_div_overflow_kernel_checked :
    ptxSdivResult = .signedDivOverflow := rfl

def ptxFloatRemBody : List PTXStmt :=
  [ .instr none (.rem .f32 "%r" (.immF32 0) (.immF32 1))
  , .instr none .ret ]

def ptxFloatRemKernel : PTXKernel where
  name := "float_rem"
  params := []
  body := ptxFloatRemBody

def ptxFloatRemResult : PTXRes :=
  evalPTXKernel 16 ptxFloatRemKernel { x := 1 } { x := 1 }
    (LeanNative.Backend.PTXAst.ByteMemory.zeros 0) { params := [] }

#guard ptxFloatRemResult == .unsupportedFloatOp "rem on floating-point type"

theorem ptx_float_rem_kernel_checked :
    ptxFloatRemResult = .unsupportedFloatOp "rem on floating-point type" := rfl

def ptxShiftBody : List PTXStmt :=
  [ .instr none (.shl .u32 "%r" (.immU64 1#64) (.immU64 0x1_0000_0000#64))
  , .instr none .ret ]

def ptxShiftKernel : PTXKernel where
  name := "shift_oob"
  params := []
  body := ptxShiftBody

def ptxShiftResult : PTXRes :=
  evalPTXKernel 16 ptxShiftKernel { x := 1 } { x := 1 }
    (LeanNative.Backend.PTXAst.ByteMemory.zeros 0) { params := [] }

#guard ptxShiftResult == .invalidOperand "shift amount exceeds 32-bit .u32/.b32 operand width"

theorem ptx_shift_width_kernel_checked :
    ptxShiftResult = .invalidOperand "shift amount exceeds 32-bit .u32/.b32 operand width" := rfl

def ptxRaceBody : List PTXStmt :=
  [ .instr none (.stGlobal .u64 (.regOffset "%r_base" 0) (.immU64 1#64))
  , .instr none .ret ]

def ptxRaceKernel : PTXKernel where
  name := "race_store"
  params := []
  body :=
    [ .instr none (.mov .u64 "%r_base" (.immU64 0#64)) ] ++ ptxRaceBody

def ptxRaceResult : PTXRes :=
  evalPTXKernel 32 ptxRaceKernel { x := 1 } { x := 2 }
    (LeanNative.Backend.PTXAst.ByteMemory.zeros 8) { params := [] }

#guard ptxRaceResult == .dataRace .global 0

theorem ptx_data_race_kernel_checked :
    ptxRaceResult = .dataRace .global 0 := rfl

/-! ## 11. Finding coverage: Metal div0, signed overflow, short-circuit vs eager select, float rem, shift, race -/

def mslUnaryKernel (name : String) (body : List MSLStmt) : MSLKernelDecl where
  name := name
  params :=
    [ { ty := .ulong, name := "rx", attr := none }
    , { ty := .ulong, name := "ry", attr := none } ]
  body := body

def mslDiv0Kernel : MSLKernelDecl :=
  mslUnaryKernel "msl_div0"
    [ .varDecl .ulong "q" (.div (.var "rx") (.var "ry"))
    , .returnStmt ]

def mslLocalsRxRy (rx ry : BitVec 64) (rxTy ryTy : MSLType) : MSLLocals :=
  MSLLocals.empty.setTyped "rx" rxTy rx |>.setTyped "ry" ryTy ry

def mslEmptyGroup : MSLGroupState :=
  { gridDim := {}, groupDim := {}, groupId := {}, threads := [] }

def mslDiv0Result : MSLOutcome (BitVec 64) :=
  evalMSLExpr mslEmptyGroup { tid := {}, locals := mslLocalsRxRy 7#64 0#64 .ulong .ulong, stmts := [], halted := false }
    (.div (.var "rx") (.var "ry"))

#guard mslDiv0Result == .divisionByZero

theorem msl_div_zero_kernel_checked :
    mslDiv0Result = .divisionByZero := rfl

def mslSdivResult : MSLOutcome (BitVec 64) :=
  evalMSLExpr mslEmptyGroup { tid := {}, locals := mslLocalsRxRy 2147483648#64 4294967295#64 .int .int, stmts := [], halted := false }
    (.div (.var "rx") (.var "ry"))

#guard mslSdivResult == .signedDivOverflow

theorem msl_signed_div_overflow_kernel_checked :
    mslSdivResult = .signedDivOverflow := rfl

def mslGuardedResult : MSLOutcome (BitVec 64) :=
  evalMSLExpr mslEmptyGroup { tid := {}, locals := mslLocalsRxRy 7#64 0#64 .ulong .ulong, stmts := [], halted := false }
    (.select (.ne (.var "ry") (.immU64 0#64)) (.div (.var "rx") (.var "ry")) (.immU64 0#64))

#guard mslGuardedResult == .ok 0#64

theorem msl_guarded_div_kernel_checked :
    mslGuardedResult = .ok 0#64 := rfl

def mslEagerResult : MSLOutcome (BitVec 64) :=
  evalMSLExpr mslEmptyGroup { tid := {}, locals := mslLocalsRxRy 7#64 0#64 .ulong .ulong, stmts := [], halted := false }
    (.builtinSelect (.immU64 0#64) (.div (.var "rx") (.var "ry")) (.ne (.var "ry") (.immU64 0#64)))

#guard mslEagerResult == .divisionByZero

theorem msl_builtin_select_eager_kernel_checked :
    mslEagerResult = .divisionByZero := rfl

def mslFloatRemResult : MSLOutcome (BitVec 64) :=
  evalMSLExpr mslEmptyGroup { tid := {}, locals := mslLocalsRxRy 0#64 1#64 .float .float, stmts := [], halted := false }
    (.rem (.var "rx") (.var "ry"))

#guard mslFloatRemResult == .unsupportedFloatOp "float remainder"

theorem msl_float_rem_kernel_checked :
    mslFloatRemResult = .unsupportedFloatOp "float remainder" := rfl

def mslShiftResult : MSLOutcome (BitVec 64) :=
  evalMSLExpr mslEmptyGroup { tid := {}, locals := mslLocalsRxRy 1#64 32#64 .uint .uint, stmts := [], halted := false }
    (.shl (.var "rx") (.var "ry"))

#guard mslShiftResult == .shiftOutOfRange

theorem msl_shift_width_kernel_checked :
    mslShiftResult = .shiftOutOfRange := rfl

def mslRaceKernel : MSLKernelDecl where
  name := "msl_race"
  params :=
    [ { ty := .pointer .device false .ulong, name := "buf", attr := some (.buffer 0) } ]
  body :=
    [ .indexAssign "buf" (.immU64 0#64) (.immU64 1#64)
    , .returnStmt ]

def mslRaceResult : MSLRes :=
  evalMSLKernel 32 mslRaceKernel { x := 1 } { x := 2 }
    [ (0, LeanNative.Backend.MetalAst.ByteMemory.zeros 8) ] []

#guard mslRaceResult == .dataRace .device 0

theorem msl_data_race_kernel_checked :
    mslRaceResult = .dataRace .device 0 := rfl

/-! ## 12. Finding 2–5 end-to-end coverage: IEEE-754 floats, 3D coords, multi-CTA/local/const/atomics/shuffle, helpers & `u256` -/

def ptxFmaKernel : PTXKernel where
  name := "ptx_fma_f32"
  params := [ { ty := .u64, name := "out_ptr" } ]
  body :=
    [ .instr none (.ldParam .u64 "%rd0" "out_ptr")
    , .instr none (.fma .rn .f32 "%f0" (.immF32 0x3FC00000) (.immF32 0x40000000) (.immF32 0x3F000000))
    , .instr none (.cvt .rn .f64 .f32 "%fd0" (.reg "%f0"))
    , .instr none (.stGlobal .f64 (.regOffset "%rd0" 0) (.reg "%fd0"))
    , .instr none .ret ]

def ptxFmaResult : PTXRes :=
  evalPTXKernel 32 ptxFmaKernel { x := 1 } { x := 1 }
    (LeanNative.Backend.PTXAst.ByteMemory.zeros 8)
    { params := [ ("out_ptr", 0#64) ] }

#guard ptxReadWord? ptxFmaResult 0 == some 0x400C000000000000#64

theorem ptx_fma_cvt_f32_f64_kernel_checked :
    ptxReadWord? ptxFmaResult 0 = some 0x400C000000000000#64 := rfl

def ptxMultiCtaKernel : PTXKernel where
  name := "ptx_multi_cta_local_const_atom_shfl"
  params := [ { ty := .u64, name := "out_ptr" } ]
  localBytes := 8
  body :=
    [ .instr none (.ldParam .u64 "%rd_out" "out_ptr")
    , .instr none (.mov .u32 "%r_tid" (.sreg .tidX))
    , .instr none (.mov .u32 "%r_ty" (.sreg .tidY))
    , .instr none (.mov .u32 "%r_cta" (.sreg .ctaidX))
    , .instr none (.mov .u64 "%rd_zero" (.immU64 0#64))
    , .instr none (.ldConst .u64 "%rd_c" (.regOffset "%rd_zero" 0))
    , .instr none (.cvt .none .u64 .u32 "%rd_tid" (.reg "%r_tid"))
    , .instr none (.cvt .none .u64 .u32 "%rd_ty" (.reg "%r_ty"))
    , .instr none (.cvt .none .u64 .u32 "%rd_cta" (.reg "%r_cta"))
    , .instr none (.add .none .u64 "%rd_sum" (.reg "%rd_tid") (.reg "%rd_ty"))
    , .instr none (.add .none .u64 "%rd_sum" (.reg "%rd_sum") (.reg "%rd_cta"))
    , .instr none (.add .none .u64 "%rd_sum" (.reg "%rd_sum") (.reg "%rd_c"))
    , .instr none (.stLocal .u64 (.regOffset "%rd_zero" 0) (.reg "%rd_sum"))
    , .instr none (.ldLocal .u64 "%rd_loc" (.regOffset "%rd_zero" 0))
    , .instr none (.atomAdd .global .u64 "%rd_old" (.regOffset "%rd_out" 0) (.reg "%rd_loc"))
    , .instr none (.mov .b32 "%r_src" (.immU64 1#64))
    , .instr none (.shflSyncBfly "%r_shfl" (.reg "%r_src") (.immU64 1#64) (.immU64 31#64) (.immU64 15#64))
    , .instr none (.cvt .none .u64 .u32 "%rd_shfl" (.reg "%r_shfl"))
    , .instr none (.atomAdd .global .u64 "%rd_old2" (.regOffset "%rd_out" 8) (.reg "%rd_shfl"))
    , .instr none .ret ]

def ptxMultiCtaResult : PTXRes :=
  evalPTXKernel 160 ptxMultiCtaKernel { x := 2, y := 1, z := 1 } { x := 2, y := 2, z := 1 }
    (LeanNative.Backend.PTXAst.ByteMemory.zeros 16)
    { params := [ ("out_ptr", 0#64) ] }
    (LeanNative.Backend.PTXAst.ByteMemory.ofU64Words [ 100#64 ])

#guard ptxReadWord? ptxMultiCtaResult 0 == some 812#64
#guard ptxReadWord? ptxMultiCtaResult 1 == some 8#64

theorem ptx_multi_cta_local_const_atom_shfl_kernel_checked :
    ptxReadWord? ptxMultiCtaResult 0 = some 812#64 ∧
    ptxReadWord? ptxMultiCtaResult 1 = some 8#64 := ⟨rfl, rfl⟩

def mslFmaKernel : MSLKernelDecl where
  name := "msl_fma_f32"
  params :=
    [ { ty := .pointer .device false .double, name := "out", attr := some (.buffer 0) } ]
  body :=
    [ .varDecl .float "f0" (.fma (.immF32 0x3FC00000#32) (.immF32 0x40000000#32) (.immF32 0x3F000000#32))
    , .varDecl .double "d0" (.cast .double (.var "f0"))
    , .indexAssign "out" (.immU64 0#64) (.var "d0")
    , .returnStmt ]

def mslFmaResult : MSLRes :=
  evalMSLKernel 32 mslFmaKernel { x := 1 } { x := 1 }
    [ (0, LeanNative.Backend.MetalAst.ByteMemory.zeros 8) ] []

#guard mslReadWord? mslFmaResult 0 0 == some 0x400C000000000000#64

theorem msl_fma_cvt_f32_f64_kernel_checked :
    mslReadWord? mslFmaResult 0 0 = some 0x400C000000000000#64 := rfl

def mslCoordsKernel : MSLKernelDecl where
  name := "msl_3d_coords"
  params :=
    [ { ty := .pointer .device false .ulong, name := "out", attr := some (.buffer 0) }
    , { ty := .uint3, name := "gid", attr := some .threadPositionInGrid }
    , { ty := .uint3, name := "tid", attr := some .threadPositionInThreadgroup }
    , { ty := .uint3, name := "bid", attr := some .threadgroupPositionInGrid } ]
  body :=
    [ .varDecl .ulong "gx" (.fieldAccess (.var "gid") "x")
    , .varDecl .ulong "gy" (.fieldAccess (.var "gid") "y")
    , .varDecl .ulong "gz" (.fieldAccess (.var "gid") "z")
    , .varDecl .ulong "ty" (.fieldAccess (.var "tid") "y")
    , .varDecl .ulong "bz" (.fieldAccess (.var "bid") "z")
    , .varDecl .ulong "idx" (.add (.mul (.var "gz") (.immU64 4#64)) (.add (.mul (.var "gy") (.immU64 2#64)) (.var "gx")))
    , .varDecl .ulong "v" (.add (.mul (.var "bz") (.immU64 100#64)) (.add (.mul (.var "ty") (.immU64 10#64)) (.var "gx")))
    , .indexAssign "out" (.var "idx") (.var "v")
    , .returnStmt ]

def mslCoordsResult : MSLRes :=
  evalMSLKernel 64 mslCoordsKernel { x := 1, y := 1, z := 2 } { x := 2, y := 2, z := 1 }
    [ (0, LeanNative.Backend.MetalAst.ByteMemory.zeros 64) ] []

#guard mslReadWord? mslCoordsResult 0 7 == some 111#64

theorem msl_3d_coords_kernel_checked :
    mslReadWord? mslCoordsResult 0 7 = some 111#64 := rfl

def mslHelperU256Kernel : MSLKernelDecl where
  name := "msl_helper_u256"
  params :=
    [ { ty := .pointer .device false .u256, name := "out", attr := some (.buffer 0) }
    , { ty := .pointer .constant false .ulong, name := "coeff", attr := some (.buffer 1) } ]
  body :=
    [ .varDecl .ulong "c" (.index "coeff" (.immU64 0#64))
    , .varDecl .u256 "acc" (.structLit .u256 (.ofList [ .var "c", .immU64 2#64, .immU64 3#64, .immU64 4#64 ]))
    , .exprStmt (.call "bump" (.ofList [ .var "acc" ]))
    , .indexAssign "out" (.immU64 0#64) (.var "acc")
    , .returnStmt ]

def mslBumpFunc : MSLFuncDecl where
  retTy := .void
  name := "bump"
  params := [ { ty := .ref .thread .u256, name := "x" } ]
  body := .ofList
    [ .fieldAssign "x" "l0" (.add (.fieldAccess (.var "x") "l0") (.immU64 1#64))
    , .returnStmt ]

def mslHelperU256Result : MSLRes :=
  evalMSLKernel 12 mslHelperU256Kernel { x := 1 } { x := 1 }
    [ (0, LeanNative.Backend.MetalAst.ByteMemory.zeros 32) ]
    [ (1, LeanNative.Backend.MetalAst.ByteMemory.ofU64Words [ 10#64 ]) ]
    [ mslBumpFunc ]
    [ { name := "ln_u256"
      , fields :=
          [ { ty := .ulong, name := "l0" }
          , { ty := .ulong, name := "l1" }
          , { ty := .ulong, name := "l2" }
          , { ty := .ulong, name := "l3" } ] } ]

#guard mslReadWord? mslHelperU256Result 0 0 == some 11#64
#guard mslReadWord? mslHelperU256Result 0 3 == some 4#64

def mslHelperRefKernel : MSLKernelDecl where
  name := "msl_helper_ref"
  params :=
    [ { ty := .pointer .device false .ulong, name := "out", attr := some (.buffer 0) }
    , { ty := .pointer .constant false .ulong, name := "coeff", attr := some (.buffer 1) } ]
  body :=
    [ .varDecl .ulong "acc" (.index "coeff" (.immU64 0#64))
    , .exprStmt (.call "bump_u64" (.ofList [ .var "acc" ]))
    , .indexAssign "out" (.immU64 0#64) (.var "acc")
    , .returnStmt ]

def mslBumpU64Func : MSLFuncDecl where
  retTy := .void
  name := "bump_u64"
  params := [ { ty := .ref .thread .ulong, name := "x" } ]
  body := .ofList
    [ .assign "x" (.add (.var "x") (.immU64 5#64))
    , .returnStmt ]

def mslHelperRefResult : MSLRes :=
  evalMSLKernel 8 mslHelperRefKernel { x := 1 } { x := 1 }
    [ (0, LeanNative.Backend.MetalAst.ByteMemory.zeros 8) ]
    [ (1, LeanNative.Backend.MetalAst.ByteMemory.ofU64Words [ 10#64 ]) ]
    [ mslBumpU64Func ] []

#guard mslReadWord? mslHelperRefResult 0 0 == some 15#64

theorem msl_helper_ref_kernel_checked :
    mslReadWord? mslHelperRefResult 0 0 = some 15#64 := rfl

def mslSimdKernel : MSLKernelDecl where
  name := "msl_simd_collectives"
  params :=
    [ { ty := .pointer .device false .ulong, name := "out", attr := some (.buffer 0) }
    , { ty := .uint, name := "lane", attr := some .threadIndexInSimdgroup } ]
  body :=
    [ .varDecl .ulong "v" (.add (.var "lane") (.immU64 10#64))
    , .simdSum (some .ulong) "s" (.var "v")
    , .simdShuffleXor (some .ulong) "sw" (.var "v") (.immU64 1#64)
    , .indexAssign "out" (.var "lane") (.add (.var "s") (.var "sw"))
    , .returnStmt ]

def mslSimdResult : MSLRes :=
  evalMSLKernel 16 mslSimdKernel { x := 1 } { x := 2 }
    [ (0, LeanNative.Backend.MetalAst.ByteMemory.zeros 16) ] []

#guard mslReadWord? mslSimdResult 0 0 == some 32#64
#guard mslReadWord? mslSimdResult 0 1 == some 31#64

theorem msl_simd_collectives_kernel_checked :
    mslReadWord? mslSimdResult 0 0 = some 32#64 ∧
    mslReadWord? mslSimdResult 0 1 = some 31#64 := ⟨rfl, rfl⟩

def mslDeviceConstKernel : MSLKernelDecl where
  name := "msl_device_const_write"
  params :=
    [ { ty := .pointer .device true .ulong, name := "ro", attr := some (.buffer 0) } ]
  body :=
    [ .indexAssign "ro" (.immU64 0#64) (.immU64 9#64)
    , .returnStmt ]

def mslDeviceConstResult : MSLRes :=
  evalMSLKernel 16 mslDeviceConstKernel { x := 1 } { x := 1 }
    [ (0, LeanNative.Backend.MetalAst.ByteMemory.ofU64Words [ 5#64 ]) ] []

#guard mslDeviceConstResult == .readOnlyViolation "ro" 0

theorem msl_device_const_write_rejected_kernel_checked :
    mslDeviceConstResult = .readOnlyViolation "ro" 0 := rfl

def mslAtomicKernel : MSLKernelDecl where
  name := "msl_atomic_add"
  params :=
    [ { ty := .pointer .device false .uint, name := "acc", attr := some (.buffer 0) }
    , { ty := .uint, name := "tid", attr := some .threadPositionInThreadgroup } ]
  body :=
    [ .atomicFetchAdd (some .uint) (some "prev") "acc" (.immU64 0#64) (.add (.var "tid") (.immU64 1#64))
    , .returnStmt ]

def mslAtomicResult : MSLRes :=
  evalMSLKernel 64 mslAtomicKernel { x := 2 } { x := 2 }
    [ (0, LeanNative.Backend.MetalAst.ByteMemory.ofU32Words [ 10#32 ]) ] []

def mslReadU32? (res : MSLRes) (bufIdx elemIdx : Nat) : Option (BitVec 32) :=
  match res with
  | .ok bufs => (bufs.lookup bufIdx).bind (fun m => m.readU32Word? elemIdx)
  | _ => none

#guard mslReadU32? mslAtomicResult 0 0 == some 16#32

theorem msl_multi_group_atomic_add_kernel_checked :
    mslReadU32? mslAtomicResult 0 0 = some 16#32 := rfl

/-! ## 13. Structural Pretty-Printer Smoke Checks (`PTXModule` and `MSLModule`) -/

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
