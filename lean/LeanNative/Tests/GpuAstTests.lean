import LeanNative.Backend.PTXAst
import LeanNative.Backend.MetalAst

/-!
# Executable & Kernel-Checked SIMT Tests for `PTXAst` and `MetalAst` (`C2b`)

Covers multi-thread SIMT vector addition, shared-memory reduction, divergent barrier detection,
read-only `constant` address-space violation, out-of-bounds buffer writes, declared-register
enforcement (`regDecls`), `atom.cas` & atomic vs non-atomic epoch race rules, multi-lane Metal
vectors/structs (`ulong2`, `u256`, `.structTy`), single-pass simdgroup collectives, depth-8 helper
calls with >64-step helper loops, `thread` local arrays with pass-by-reference write-back,
short-circuit `&&`/`||`, pointer dereference & `atomic_exchange_explicit`, C++/MSL integer rank
promotion, and signed arithmetic shifts. Every scenario is checked twice: `#guard` runs the
evaluator, and a kernel-checked `rfl` theorem re-proves the same equality with `0 sorryAx` and no
`native_decide`.
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

def mslReadU32? (res : MSLRes) (bufIdx elemIdx : Nat) : Option (BitVec 32) :=
  match res with
  | .ok bufs => (bufs.lookup bufIdx).bind (fun m => m.readU32Word? elemIdx)
  | _ => none

/-! ## 1. CUDA PTX: 2-thread SIMT vector addition (`out[i] = a[i] + b[i]`) -/

def ptxVecAddBody : List PTXStmt :=
  [ .instr none (.mov .u32 "%r0" (.sreg .tidX))
  , .instr none (.cvt .none .u64 .u32 "%rd0" (.reg "%r0"))
  , .instr none (.mul .lo .u64 "%rd1" (.reg "%rd0") (.immU64 8#64))
  , .instr none (.ldParam .u64 "%rd2" "param_a")
  , .instr none (.add .none .u64 "%rd3" (.reg "%rd2") (.reg "%rd1"))
  , .instr none (.ldGlobal .u64 "%rd4" (.regOffset "%rd3" 0))
  , .instr none (.ldParam .u64 "%rd5" "param_b")
  , .instr none (.add .none .u64 "%rd6" (.reg "%rd5") (.reg "%rd1"))
  , .instr none (.ldGlobal .u64 "%rd7" (.regOffset "%rd6" 0))
  , .instr none (.add .none .u64 "%rd8" (.reg "%rd4") (.reg "%rd7"))
  , .instr none (.ldParam .u64 "%rd9" "param_out")
  , .instr none (.add .none .u64 "%rd10" (.reg "%rd9") (.reg "%rd1"))
  , .instr none (.stGlobal .u64 (.regOffset "%rd10" 0) (.reg "%rd8"))
  , .instr none .ret ]

def ptxVecAddKernel : PTXKernel where
  name := "vec_add_u64"
  params := [ { ty := .u64, name := "param_a" }
            , { ty := .u64, name := "param_b" }
            , { ty := .u64, name := "param_out" } ]
  regDecls := [ { ty := .u32, prefixName := "%r", count := 1 }
              , { ty := .u64, prefixName := "%rd", count := 11 } ]
  body := ptxVecAddBody

def ptxVecAddGlobal : PTXMem :=
  LeanNative.Backend.PTXAst.ByteMemory.ofU64Words
    [ 3#64, 5#64
    , 10#64, 20#64
    , 0#64, 0#64 ]

def ptxVecAddParams : PTXParams :=
  { params := [ ("param_a", 0#64), ("param_b", 16#64), ("param_out", 32#64) ] }

def ptxVecAddResult : PTXRes :=
  evalPTXKernel 32 ptxVecAddKernel { x := 1 } { x := 2 } ptxVecAddGlobal ptxVecAddParams

def ptxVecAddExpected : PTXRes :=
  .ok (LeanNative.Backend.PTXAst.ByteMemory.ofU64Words
    [ 3#64, 5#64
    , 10#64, 20#64
    , 13#64, 25#64 ])

#guard ptxVecAddResult == ptxVecAddExpected

theorem ptx_vec_add_kernel_checked :
    ptxReadWord? ptxVecAddResult 4 = some 13#64 ∧
    ptxReadWord? ptxVecAddResult 5 = some 25#64 := ⟨rfl, rfl⟩

/-! ## 2. CUDA PTX: 2-thread shared-memory reduction (`sum(xs)` via `.shared` + `bar.sync`) -/

def ptxReduceBody : List PTXStmt :=
  [ .instr none (.mov .u32 "%r0" (.sreg .tidX))
  , .instr none (.cvt .none .u64 .u32 "%rd0" (.reg "%r0"))
  , .instr none (.mul .lo .u64 "%rd1" (.reg "%rd0") (.immU64 8#64))
  , .instr none (.ldParam .u64 "%rd2" "param_in")
  , .instr none (.add .none .u64 "%rd3" (.reg "%rd2") (.reg "%rd1"))
  , .instr none (.ldGlobal .u64 "%rd4" (.regOffset "%rd3" 0))
  , .instr none (.mov .u64 "%rd5" (.sym "smem"))
  , .instr none (.add .none .u64 "%rd6" (.reg "%rd5") (.reg "%rd1"))
  , .instr none (.stShared .u64 (.regOffset "%rd6" 0) (.reg "%rd4"))
  , .instr none (.barSync 0)
  , .instr none (.setp .eq .u32 "%p0" (.reg "%r0") (.immU64 0#64))
  , .instr (some { predReg := "%p0" }) (.ldShared .u64 "%rd7" (.symOffset "smem" 0))
  , .instr (some { predReg := "%p0" }) (.ldShared .u64 "%rd8" (.symOffset "smem" 8))
  , .instr (some { predReg := "%p0" }) (.add .none .u64 "%rd9" (.reg "%rd7") (.reg "%rd8"))
  , .instr (some { predReg := "%p0" }) (.ldParam .u64 "%rd10" "param_out")
  , .instr (some { predReg := "%p0" })
      (.stGlobal .u64 (.regOffset "%rd10" 0) (.reg "%rd9"))
  , .instr none .ret ]

def ptxReduceKernel : PTXKernel where
  name := "shared_reduce_u64"
  params := [ { ty := .u64, name := "param_in" }, { ty := .u64, name := "param_out" } ]
  sharedDecls := [ { align := 8, elemTy := .u64, name := "smem", count := 2 } ]
  regDecls := [ { ty := .u32, prefixName := "%r", count := 1 }
              , { ty := .u64, prefixName := "%rd", count := 11 }
              , { ty := .pred, prefixName := "%p", count := 1 } ]
  body := ptxReduceBody

def ptxReduceGlobal : PTXMem :=
  LeanNative.Backend.PTXAst.ByteMemory.ofU64Words [ 17#64, 25#64, 0#64 ]

def ptxReduceParams : PTXParams :=
  { params := [ ("param_in", 0#64), ("param_out", 16#64) ] }

def ptxReduceResult : PTXRes :=
  evalPTXKernel 64 ptxReduceKernel { x := 1 } { x := 2 } ptxReduceGlobal ptxReduceParams

def ptxReduceExpected : PTXRes :=
  .ok (LeanNative.Backend.PTXAst.ByteMemory.ofU64Words [ 17#64, 25#64, 42#64 ])

#guard ptxReduceResult == ptxReduceExpected

theorem ptx_shared_reduce_kernel_checked :
    ptxReadWord? ptxReduceResult 2 = some 42#64 := rfl

/-! ## 3. CUDA PTX: divergent `bar.sync` is rejected -/

def ptxDivergentKernel : PTXKernel where
  name := "divergent_barrier"
  params := []
  regDecls := [ { ty := .u32, prefixName := "%r", count := 1 }
              , { ty := .pred, prefixName := "%p", count := 1 } ]
  body :=
    [ .instr none (.mov .u32 "%r0" (.sreg .tidX))
    , .instr none (.setp .eq .u32 "%p0" (.reg "%r0") (.immU64 0#64))
    , .instr (some { predReg := "%p0" }) (.barSync 0)
    , .instr none (.barSync 1) ]

def ptxDivergentResult : PTXRes :=
  evalPTXKernel 32 ptxDivergentKernel { x := 1 } { x := 2 }
    (LeanNative.Backend.PTXAst.ByteMemory.zeros 0) { params := [] }

#guard ptxDivergentResult == .barrierDivergence 0

theorem ptx_divergent_barrier_kernel_checked :
    ptxDivergentResult = .barrierDivergence 0 := rfl

/-! ## 4. CUDA PTX: out-of-bounds global store is rejected -/

def ptxOobKernel : PTXKernel where
  name := "oob_store"
  params := []
  regDecls := [ { ty := .u64, prefixName := "%rd", count := 1 } ]
  body :=
    [ .instr none (.mov .u64 "%rd0" (.immU64 16#64))
    , .instr none (.stGlobal .u64 (.regOffset "%rd0" 0) (.immU64 1#64))
    , .instr none .ret ]

def ptxOobResult : PTXRes :=
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

def mslVecAddDevice : MSLDevTable :=
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

def mslReduceDevice : MSLDevTable :=
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

def mslDivergentKernel : MSLKernelDecl where
  name := "divergent_barrier"
  params := [ { ty := .uint, name := "tid", attr := some .threadPositionInThreadgroup } ]
  body :=
    [ .ifElse (.eq (.var "tid") (.immU64 0#64))
        (.cons .threadgroupBarrier .nil)
        .nil
    , .returnStmt ]

def mslDivergentResult : MSLRes :=
  evalMSLKernel 32 mslDivergentKernel { x := 1 } { x := 2 } [] []

#guard mslDivergentResult == .barrierDivergence

theorem msl_divergent_barrier_kernel_checked :
    mslDivergentResult = .barrierDivergence := rfl

/-! ## 8. Apple Metal: writing a `constant` buffer is rejected -/

def mslConstWriteKernel : MSLKernelDecl where
  name := "constant_write"
  params := [ { ty := .pointer .constant false .ulong, name := "coeffs", attr := some (.buffer 3) } ]
  body :=
    [ .indexAssign "coeffs" (.immU64 0#64) (.immU64 99#64)
    , .returnStmt ]

def mslConstWriteResult : MSLRes :=
  evalMSLKernel 16 mslConstWriteKernel { x := 1 } { x := 1 } []
    [ (3, LeanNative.Backend.MetalAst.ByteMemory.ofU64Words [ 7#64 ]) ]

#guard mslConstWriteResult == .readOnlyViolation "coeffs" 0

theorem msl_constant_write_rejected_kernel_checked :
    mslConstWriteResult = .readOnlyViolation "coeffs" 0 := rfl

/-! ## 9. Apple Metal: out-of-bounds `device` store is rejected -/

def mslOobKernel : MSLKernelDecl where
  name := "oob_store"
  params := [ { ty := .pointer .device false .ulong, name := "buf", attr := some (.buffer 0) } ]
  body :=
    [ .indexAssign "buf" (.immU64 4#64) (.immU64 1#64)
    , .returnStmt ]

def mslOobResult : MSLRes :=
  evalMSLKernel 16 mslOobKernel { x := 1 } { x := 1 }
    [ (0, LeanNative.Backend.MetalAst.ByteMemory.zeros 8) ] []

#guard mslOobResult == .outOfBoundsWrite .device 0 4

theorem msl_oob_write_kernel_checked :
    mslOobResult = .outOfBoundsWrite .device 0 4 := rfl

/-! ## 10. PTX div0, signed overflow, float remainder, shift width, non-atomic race -/

def ptxDiv0Kernel : PTXKernel where
  name := "div0"
  params := []
  regDecls := [ { ty := .u64, prefixName := "%rd", count := 1 } ]
  body :=
    [ .instr none (.div .u64 "%rd0" (.immU64 7#64) (.immU64 0#64))
    , .instr none .ret ]

def ptxDiv0Result : PTXRes :=
  evalPTXKernel 16 ptxDiv0Kernel { x := 1 } { x := 1 }
    (LeanNative.Backend.PTXAst.ByteMemory.zeros 0) { params := [] }

#guard ptxDiv0Result == .divisionByZero

theorem ptx_div_zero_kernel_checked :
    ptxDiv0Result = .divisionByZero := rfl

def ptxSdivKernel : PTXKernel where
  name := "sdiv_overflow"
  params := []
  regDecls := [ { ty := .s32, prefixName := "%r", count := 1 } ]
  body :=
    [ .instr none (.div .s32 "%r0" (.immU64 2147483648#64) (.immU64 4294967295#64))
    , .instr none .ret ]

def ptxSdivResult : PTXRes :=
  evalPTXKernel 16 ptxSdivKernel { x := 1 } { x := 1 }
    (LeanNative.Backend.PTXAst.ByteMemory.zeros 0) { params := [] }

#guard ptxSdivResult == .signedDivOverflow

theorem ptx_signed_div_overflow_kernel_checked :
    ptxSdivResult = .signedDivOverflow := rfl

def ptxFloatRemKernel : PTXKernel where
  name := "float_rem"
  params := []
  regDecls := [ { ty := .f32, prefixName := "%f", count := 1 } ]
  body :=
    [ .instr none (.rem .f32 "%f0" (.immF32 0) (.immF32 1))
    , .instr none .ret ]

def ptxFloatRemResult : PTXRes :=
  evalPTXKernel 16 ptxFloatRemKernel { x := 1 } { x := 1 }
    (LeanNative.Backend.PTXAst.ByteMemory.zeros 0) { params := [] }

#guard ptxFloatRemResult == .unsupportedFloatOp "rem on floating-point type"

theorem ptx_float_rem_kernel_checked :
    ptxFloatRemResult = .unsupportedFloatOp "rem on floating-point type" := rfl

def ptxShiftKernel : PTXKernel where
  name := "shift_oob"
  params := []
  regDecls := [ { ty := .b32, prefixName := "%r", count := 1 } ]
  body :=
    [ .instr none (.shl .b32 "%r0" (.immU64 1#64) (.immU64 0x1_0000_0000#64))
    , .instr none .ret ]

def ptxShiftResult : PTXRes :=
  evalPTXKernel 16 ptxShiftKernel { x := 1 } { x := 1 }
    (LeanNative.Backend.PTXAst.ByteMemory.zeros 0) { params := [] }

#guard ptxShiftResult == .invalidOperand "shift amount exceeds 32-bit .u32/.b32 operand width"

theorem ptx_shift_width_kernel_checked :
    ptxShiftResult = .invalidOperand "shift amount exceeds 32-bit .u32/.b32 operand width" := rfl

def ptxRaceKernel : PTXKernel where
  name := "race_store"
  params := []
  regDecls := [ { ty := .u64, prefixName := "%rd", count := 1 } ]
  body :=
    [ .instr none (.mov .u64 "%rd0" (.immU64 0#64))
    , .instr none (.stGlobal .u64 (.regOffset "%rd0" 0) (.immU64 1#64))
    , .instr none .ret ]

def ptxRaceResult : PTXRes :=
  evalPTXKernel 32 ptxRaceKernel { x := 1 } { x := 2 }
    (LeanNative.Backend.PTXAst.ByteMemory.zeros 8) { params := [] }

#guard ptxRaceResult == .dataRace .global 0

theorem ptx_data_race_kernel_checked :
    ptxRaceResult = .dataRace .global 0 := rfl

/-! ## 11. Metal div0, signed overflow, short-circuit vs eager select, float rem, shift, race -/

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
  params := [ { ty := .pointer .device false .ulong, name := "buf", attr := some (.buffer 0) } ]
  body :=
    [ .indexAssign "buf" (.immU64 0#64) (.immU64 1#64)
    , .returnStmt ]

def mslRaceResult : MSLRes :=
  evalMSLKernel 32 mslRaceKernel { x := 1 } { x := 2 }
    [ (0, LeanNative.Backend.MetalAst.ByteMemory.zeros 8) ] []

#guard mslRaceResult == .dataRace .device 0

theorem msl_data_race_kernel_checked :
    mslRaceResult = .dataRace .device 0 := rfl

/-! ## 12. IEEE-754 floats, 3D coords, multi-CTA/local/const/atomics/shuffle, helpers & `u256` -/

def ptxFmaKernel : PTXKernel where
  name := "ptx_fma_f32"
  params := [ { ty := .u64, name := "out_ptr" } ]
  regDecls := [ { ty := .u64, prefixName := "%rd", count := 1 }
              , { ty := .f32, prefixName := "%f", count := 1 }
              , { ty := .f64, prefixName := "%fd", count := 1 } ]
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
  regDecls := [ { ty := .u32, prefixName := "%r", count := 3 }
              , { ty := .b32, prefixName := "%rb", count := 2 }
              , { ty := .u64, prefixName := "%rd", count := 10 } ]
  body :=
    [ .instr none (.ldParam .u64 "%rd0" "out_ptr")
    , .instr none (.mov .u32 "%r0" (.sreg .tidX))
    , .instr none (.mov .u32 "%r1" (.sreg .tidY))
    , .instr none (.mov .u32 "%r2" (.sreg .ctaidX))
    , .instr none (.mov .u64 "%rd1" (.immU64 0#64))
    , .instr none (.ldConst .u64 "%rd2" (.regOffset "%rd1" 0))
    , .instr none (.cvt .none .u64 .u32 "%rd3" (.reg "%r0"))
    , .instr none (.cvt .none .u64 .u32 "%rd4" (.reg "%r1"))
    , .instr none (.cvt .none .u64 .u32 "%rd5" (.reg "%r2"))
    , .instr none (.add .none .u64 "%rd6" (.reg "%rd3") (.reg "%rd4"))
    , .instr none (.add .none .u64 "%rd6" (.reg "%rd6") (.reg "%rd5"))
    , .instr none (.add .none .u64 "%rd6" (.reg "%rd6") (.reg "%rd2"))
    , .instr none (.stLocal .u64 (.regOffset "%rd1" 0) (.reg "%rd6"))
    , .instr none (.ldLocal .u64 "%rd7" (.regOffset "%rd1" 0))
    , .instr none (.atomAdd .global .u64 "%rd8" (.regOffset "%rd0" 0) (.reg "%rd7"))
    , .instr none (.mov .b32 "%rb0" (.immU64 1#64))
    , .instr none (.shflSyncBfly "%rb1" (.reg "%rb0") (.immU64 1#64) (.immU64 31#64) (.immU64 15#64))
    , .instr none (.cvt .none .u64 .u32 "%rd9" (.reg "%rb1"))
    , .instr none (.atomAdd .global .u64 "%rd8" (.regOffset "%rd0" 8) (.reg "%rd9"))
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
  params := [ { ty := .pointer .device false .double, name := "out", attr := some (.buffer 0) } ]
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

theorem msl_helper_u256_kernel_checked :
    mslReadWord? mslHelperU256Result 0 0 = some 11#64 ∧
    mslReadWord? mslHelperU256Result 0 3 = some 4#64 := ⟨rfl, rfl⟩

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
  params := [ { ty := .pointer .device true .ulong, name := "ro", attr := some (.buffer 0) } ]
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
    [ { ty := .pointer .device false .atomicUint, name := "acc", attr := some (.buffer 0) }
    , { ty := .uint, name := "tid", attr := some .threadPositionInThreadgroup } ]
  body :=
    [ .atomicFetchAdd (some .uint) (some "prev") "acc" (some (.immU64 0#64)) (.add (.var "tid") (.immU64 1#64))
    , .returnStmt ]

def mslAtomicResult : MSLRes :=
  evalMSLKernel 64 mslAtomicKernel { x := 2 } { x := 2 }
    [ (0, LeanNative.Backend.MetalAst.ByteMemory.ofU32Words [ 10#32 ]) ] []

#guard mslReadU32? mslAtomicResult 0 0 == some 16#32

theorem msl_multi_group_atomic_add_kernel_checked :
    mslReadU32? mslAtomicResult 0 0 = some 16#32 := rfl

/-! ## 13. Round-2 PTX coverage: `regDecls` checks, `atom.cas`, and atomic vs non-atomic epoch races -/

def ptxUndeclRegKernel : PTXKernel where
  name := "ptx_undecl_reg"
  params := []
  regDecls := []
  body :=
    [ .instr none (.mov .u64 "%rd0" (.immU64 1#64))
    , .instr none .ret ]

def ptxUndeclRegResult : PTXRes :=
  evalPTXKernel 8 ptxUndeclRegKernel { x := 1 } { x := 1 }
    (LeanNative.Backend.PTXAst.ByteMemory.zeros 0) { params := [] }

#guard ptxUndeclRegResult == .unboundReg "%rd0"

theorem ptx_undeclared_reg_rejected :
    ptxUndeclRegResult = .unboundReg "%rd0" := rfl

def ptxUninitRegKernel : PTXKernel where
  name := "ptx_uninit_reg"
  params := []
  regDecls := [ { ty := .u64, prefixName := "%rd", count := 2 } ]
  body :=
    [ .instr none (.add .none .u64 "%rd1" (.reg "%rd0") (.immU64 1#64))
    , .instr none .ret ]

def ptxUninitRegResult : PTXRes :=
  evalPTXKernel 8 ptxUninitRegKernel { x := 1 } { x := 1 }
    (LeanNative.Backend.PTXAst.ByteMemory.zeros 0) { params := [] }

#guard ptxUninitRegResult == .unboundReg "%rd0"

theorem ptx_uninit_reg_rejected :
    ptxUninitRegResult = .unboundReg "%rd0" := rfl

def ptxWidthMismatchKernel : PTXKernel where
  name := "ptx_width_mismatch"
  params := []
  regDecls := [ { ty := .u32, prefixName := "%r", count := 1 }
              , { ty := .u64, prefixName := "%rd", count := 1 } ]
  body :=
    [ .instr none (.mov .u32 "%r0" (.immU64 5#64))
    , .instr none (.add .none .u64 "%rd0" (.reg "%r0") (.immU64 1#64))
    , .instr none .ret ]

def ptxWidthMismatchResult : PTXRes :=
  evalPTXKernel 8 ptxWidthMismatchKernel { x := 1 } { x := 1 }
    (LeanNative.Backend.PTXAst.ByteMemory.zeros 0) { params := [] }

#guard ptxWidthMismatchResult == .typeMismatch "register %r0 width 32 mismatches instruction width"

theorem ptx_reg_width_mismatch_rejected :
    ptxWidthMismatchResult = .typeMismatch "register %r0 width 32 mismatches instruction width" := rfl

def ptxAtomCasKernel : PTXKernel where
  name := "ptx_atom_cas_u64"
  params := [ { ty := .u64, name := "buf" } ]
  regDecls := [ { ty := .u64, prefixName := "%rd", count := 3 } ]
  body :=
    [ .instr none (.ldParam .u64 "%rd0" "buf")
    , .instr none (.atomCas .global .u64 "%rd1" (.regOffset "%rd0" 0) (.immU64 10#64) (.immU64 99#64))
    , .instr none (.atomCas .global .u64 "%rd2" (.regOffset "%rd0" 0) (.immU64 10#64) (.immU64 77#64))
    , .instr none (.stGlobal .u64 (.regOffset "%rd0" 8) (.reg "%rd1"))
    , .instr none (.stGlobal .u64 (.regOffset "%rd0" 16) (.reg "%rd2"))
    , .instr none .ret ]

def ptxAtomCasResult : PTXRes :=
  evalPTXKernel 16 ptxAtomCasKernel { x := 1 } { x := 1 }
    (LeanNative.Backend.PTXAst.ByteMemory.ofU64Words [ 10#64, 0#64, 0#64 ])
    { params := [ ("buf", 0#64) ] }

#guard ptxReadWord? ptxAtomCasResult 0 == some 99#64
#guard ptxReadWord? ptxAtomCasResult 1 == some 10#64
#guard ptxReadWord? ptxAtomCasResult 2 == some 99#64

theorem ptx_atom_cas_kernel_checked :
    ptxReadWord? ptxAtomCasResult 0 = some 99#64 ∧
    ptxReadWord? ptxAtomCasResult 1 = some 10#64 ∧
    ptxReadWord? ptxAtomCasResult 2 = some 99#64 := ⟨rfl, rfl, rfl⟩

def ptxAtomVsStoreRaceKernel : PTXKernel where
  name := "ptx_atom_vs_store_race"
  params := [ { ty := .u64, name := "buf" } ]
  regDecls := [ { ty := .u32, prefixName := "%r", count := 1 }
              , { ty := .u64, prefixName := "%rd", count := 2 }
              , { ty := .pred, prefixName := "%p", count := 2 } ]
  body :=
    [ .instr none (.ldParam .u64 "%rd0" "buf")
    , .instr none (.mov .u32 "%r0" (.sreg .tidX))
    , .instr none (.setp .eq .u32 "%p0" (.reg "%r0") (.immU64 0#64))
    , .instr none (.setp .ne .u32 "%p1" (.reg "%r0") (.immU64 0#64))
    , .instr (some { predReg := "%p0" }) (.atomAdd .global .u64 "%rd1" (.regOffset "%rd0" 0) (.immU64 1#64))
    , .instr (some { predReg := "%p1" }) (.stGlobal .u64 (.regOffset "%rd0" 0) (.immU64 2#64))
    , .instr none .ret ]

def ptxAtomVsStoreRaceResult : PTXRes :=
  evalPTXKernel 32 ptxAtomVsStoreRaceKernel { x := 1 } { x := 2 }
    (LeanNative.Backend.PTXAst.ByteMemory.zeros 8) { params := [ ("buf", 0#64) ] }

#guard ptxAtomVsStoreRaceResult == .dataRace .global 0

theorem ptx_atom_vs_nonatomic_store_race_checked :
    ptxAtomVsStoreRaceResult = .dataRace .global 0 := rfl

/-! ## 14. Round-2 Metal coverage: multi-lane vectors/structs, single-pass simd,
    depth-8 calls, arrays, short-circuit, pointer atomics & rank promotion -/

def mslUlong2Kernel : MSLKernelDecl where
  name := "msl_ulong2_lanes"
  params := [ { ty := .pointer .device false .ulong2, name := "out", attr := some (.buffer 0) } ]
  body :=
    [ .varDecl .ulong2 "a" (.structLit .ulong2 (.ofList [ .immU64 0xAA#64, .immU64 0x5500#64 ]))
    , .varDecl .ulong2 "b" (.structLit .ulong2 (.ofList [ .immU64 0x0F#64, .immU64 0x00FF#64 ]))
    , .varDecl .ulong2 "c" (.bitXor (.var "a") (.var "b"))
    , .fieldAssign "c" "x" (.add (.fieldAccess (.var "c") "x") (.immU64 1#64))
    , .indexAssign "out" (.immU64 0#64) (.var "c")
    , .returnStmt ]

def mslUlong2Result : MSLRes :=
  evalMSLKernel 16 mslUlong2Kernel { x := 1 } { x := 1 }
    [ (0, LeanNative.Backend.MetalAst.ByteMemory.zeros 16) ] []

#guard mslReadWord? mslUlong2Result 0 0 == some 0xA6#64
#guard mslReadWord? mslUlong2Result 0 1 == some 0x55FF#64

theorem msl_ulong2_lane_isolation_checked :
    mslReadWord? mslUlong2Result 0 0 = some 0xA6#64 ∧
    mslReadWord? mslUlong2Result 0 1 = some 0x55FF#64 := ⟨rfl, rfl⟩

def mslImpureBumpFunc : MSLFuncDecl where
  retTy := .ulong
  name := "bump_once"
  params := [ { ty := .ref .thread .ulong, name := "cnt" } ]
  body := .ofList
    [ .assign "cnt" (.add (.var "cnt") (.immU64 1#64))
    , .returnVal (.var "cnt") ]

def mslSinglePassSimdKernel : MSLKernelDecl where
  name := "msl_single_pass_simd"
  params :=
    [ { ty := .pointer .device false .ulong, name := "out", attr := some (.buffer 0) }
    , { ty := .uint, name := "lane", attr := some .threadIndexInSimdgroup } ]
  body :=
    [ .varDecl .ulong "cnt" (.mul (.var "lane") (.immU64 10#64))
    , .simdSum (some .ulong) "s" (.call "bump_once" (.ofList [ .var "cnt" ]))
    , .simdShuffleXor (some .ulong) "sw" (.call "bump_once" (.ofList [ .var "cnt" ])) (.immU64 1#64)
    , .indexAssign "out" (.var "lane")
        (.add (.mul (.var "cnt") (.immU64 100#64)) (.add (.var "s") (.var "sw")))
    , .returnStmt ]

def mslSinglePassSimdResult : MSLRes :=
  evalMSLKernel 32 mslSinglePassSimdKernel { x := 1 } { x := 2 }
    [ (0, LeanNative.Backend.MetalAst.ByteMemory.zeros 16) ] [] [ mslImpureBumpFunc ] []

-- Lane 0: cnt 0 -> simdSum(1, sum=12) -> simdShuffle(2, partner=12) -> 224
-- Lane 1: cnt 10 -> simdSum(11, sum=12) -> simdShuffle(12, partner=2) -> 1214
#guard mslReadWord? mslSinglePassSimdResult 0 0 == some 224#64
#guard mslReadWord? mslSinglePassSimdResult 0 1 == some 1214#64

theorem msl_single_pass_simd_side_effect_checked :
    mslReadWord? mslSinglePassSimdResult 0 0 = some 224#64 ∧
    mslReadWord? mslSinglePassSimdResult 0 1 = some 1214#64 := ⟨rfl, rfl⟩

def mkChainStep (nm nextNm : String) : MSLFuncDecl where
  retTy := .ulong
  name := nm
  params := [ { ty := .ulong, name := "x" } ]
  body := .ofList
    [ .returnVal (.call nextNm (.ofList [ .add (.var "x") (.immU64 1#64) ])) ]

def mslChainLeaf : MSLFuncDecl where
  retTy := .ulong
  name := "chain8"
  params := [ { ty := .ulong, name := "x" } ]
  body := .ofList
    [ .varDecl .ulong "acc" (.var "x")
    , .forLoop "i" .uint (.immU64 0#64) (.lt (.var "i") (.immU64 70#64))
        (.add (.var "i") (.immU64 1#64))
        (.ofList [ .assign "acc" (.add (.var "acc") (.immU64 1#64)) ])
    , .returnVal (.var "acc") ]

def mslDeepChainHelpers : List MSLFuncDecl :=
  [ mkChainStep "chain1" "chain2"
  , mkChainStep "chain2" "chain3"
  , mkChainStep "chain3" "chain4"
  , mkChainStep "chain4" "chain5"
  , mkChainStep "chain5" "chain6"
  , mkChainStep "chain6" "chain7"
  , mkChainStep "chain7" "chain8"
  , mslChainLeaf ]

def mslDeepChainKernel : MSLKernelDecl where
  name := "msl_deep_chain"
  params := [ { ty := .pointer .device false .ulong, name := "out", attr := some (.buffer 0) } ]
  body :=
    [ .varDecl .ulong "res" (.call "chain1" (.ofList [ .immU64 5#64 ]))
    , .indexAssign "out" (.immU64 0#64) (.var "res")
    , .returnStmt ]

def mslDeepChainResult : MSLRes :=
  evalMSLKernel 256 mslDeepChainKernel { x := 1 } { x := 1 }
    [ (0, LeanNative.Backend.MetalAst.ByteMemory.zeros 8) ] [] mslDeepChainHelpers []

-- 5 + 7 intermediate increments + 70 loop iterations in chain8 = 82
#guard mslReadWord? mslDeepChainResult 0 0 == some 82#64

theorem msl_deep_chain_and_long_callee_loop_checked :
    mslReadWord? mslDeepChainResult 0 0 = some 82#64 := rfl

def mslArrayRefFunc : MSLFuncDecl where
  retTy := .void
  name := "mix_words"
  params := [ { ty := .threadArr false .ulong 4, name := "v" } ]
  body := .ofList
    [ .indexAssign "v" (.immU64 0#64) (.add (.index "v" (.immU64 0#64)) (.index "v" (.immU64 1#64)))
    , .indexAssign "v" (.immU64 3#64) (.bitXor (.index "v" (.immU64 3#64)) (.index "v" (.immU64 0#64)))
    , .returnStmt ]

def mslThreadArrayKernel : MSLKernelDecl where
  name := "msl_thread_array_ref"
  params := [ { ty := .pointer .device false .ulong, name := "out", attr := some (.buffer 0) } ]
  body :=
    [ .arrayDecl .ulong "state" 4 (.ofList [ .immU64 10#64, .immU64 20#64, .immU64 30#64, .immU64 7#64 ])
    , .exprStmt (.call "mix_words" (.ofList [ .var "state" ]))
    , .indexAssign "out" (.immU64 0#64) (.index "state" (.immU64 0#64))
    , .indexAssign "out" (.immU64 1#64) (.index "state" (.immU64 3#64))
    , .returnStmt ]

def mslThreadArrayResult : MSLRes :=
  evalMSLKernel 32 mslThreadArrayKernel { x := 1 } { x := 1 }
    [ (0, LeanNative.Backend.MetalAst.ByteMemory.zeros 16) ] [] [ mslArrayRefFunc ] []

-- state[0] = 10 + 20 = 30; state[3] = 7 ^ 30 = 25
#guard mslReadWord? mslThreadArrayResult 0 0 == some 30#64
#guard mslReadWord? mslThreadArrayResult 0 1 == some 25#64

theorem msl_thread_array_pass_by_ref_checked :
    mslReadWord? mslThreadArrayResult 0 0 = some 30#64 ∧
    mslReadWord? mslThreadArrayResult 0 1 = some 25#64 := ⟨rfl, rfl⟩

def mslThreadArrayOobKernel : MSLKernelDecl where
  name := "msl_thread_array_oob"
  params := []
  body :=
    [ .arrayDecl .ulong "state" 2 (.ofList [ .immU64 1#64, .immU64 2#64 ])
    , .indexAssign "state" (.immU64 2#64) (.immU64 9#64)
    , .returnStmt ]

def mslThreadArrayOobResult : MSLRes :=
  evalMSLKernel 16 mslThreadArrayOobKernel { x := 1 } { x := 1 } [] []

#guard mslThreadArrayOobResult == .outOfBoundsWrite .thread 0 2

theorem msl_thread_array_oob_checked :
    mslThreadArrayOobResult = .outOfBoundsWrite .thread 0 2 := rfl

def mslShortCircuitAndResult : MSLOutcome (BitVec 64) :=
  evalMSLExpr mslEmptyGroup { tid := {}, locals := mslLocalsRxRy 7#64 0#64 .ulong .ulong, stmts := [], halted := false }
    (.logAnd (.ne (.var "ry") (.immU64 0#64)) (.gt (.div (.var "rx") (.var "ry")) (.immU64 0#64)))

def mslShortCircuitOrResult : MSLOutcome (BitVec 64) :=
  evalMSLExpr mslEmptyGroup { tid := {}, locals := mslLocalsRxRy 7#64 0#64 .ulong .ulong, stmts := [], halted := false }
    (.logOr (.eq (.var "ry") (.immU64 0#64)) (.gt (.div (.var "rx") (.var "ry")) (.immU64 0#64)))

#guard mslShortCircuitAndResult == .ok 0#64
#guard mslShortCircuitOrResult == .ok 1#64

theorem msl_short_circuit_and_or_checked :
    mslShortCircuitAndResult = .ok 0#64 ∧
    mslShortCircuitOrResult = .ok 1#64 := ⟨rfl, rfl⟩

def mslPtrAtomicDerefKernel : MSLKernelDecl where
  name := "msl_ptr_atomic_deref"
  params :=
    [ { ty := .pointer .device false .atomicUint, name := "lockPtr", attr := some (.buffer 0) }
    , { ty := .pointer .device false .ulong, name := "valPtr", attr := some (.buffer 1) } ]
  body :=
    [ .atomicExchange (some .uint) (some "old0") "lockPtr" none (.immU64 1#64)
    , .atomicFetchAdd (some .uint) (some "old1") "lockPtr" none (.immU64 4#64)
    , .derefAssign "valPtr" (.add (.deref "valPtr") (.add (.var "old0") (.var "old1")))
    , .returnStmt ]

def mslPtrAtomicDerefResult : MSLRes :=
  evalMSLKernel 32 mslPtrAtomicDerefKernel { x := 1 } { x := 1 }
    [ (0, LeanNative.Backend.MetalAst.ByteMemory.ofU32Words [ 7#32 ])
    , (1, LeanNative.Backend.MetalAst.ByteMemory.ofU64Words [ 100#64 ]) ] []

-- old0 = 7 (lock becomes 1), old1 = 1 (lock becomes 5), *valPtr = 100 + 7 + 1 = 108
#guard mslReadU32? mslPtrAtomicDerefResult 0 0 == some 5#32
#guard mslReadWord? mslPtrAtomicDerefResult 1 0 == some 108#64

theorem msl_ptr_atomic_exchange_and_deref_checked :
    mslReadU32? mslPtrAtomicDerefResult 0 0 = some 5#32 ∧
    mslReadWord? mslPtrAtomicDerefResult 1 0 = some 108#64 := ⟨rfl, rfl⟩

def mslAtomVsNonAtomRaceKernel : MSLKernelDecl where
  name := "msl_atom_vs_nonatom_race"
  params :=
    [ { ty := .pointer .device false .uint, name := "buf", attr := some (.buffer 0) }
    , { ty := .uint, name := "tid", attr := some .threadPositionInThreadgroup } ]
  body :=
    [ .ifElse (.eq (.var "tid") (.immU64 0#64))
        (.ofList [ .atomicFetchAdd none none "buf" (some (.immU64 0#64)) (.immU64 1#64) ])
        (.ofList [ .indexAssign "buf" (.immU64 0#64) (.immU64 2#64) ])
    , .returnStmt ]

def mslAtomVsNonAtomRaceResult : MSLRes :=
  evalMSLKernel 32 mslAtomVsNonAtomRaceKernel { x := 1 } { x := 2 }
    [ (0, LeanNative.Backend.MetalAst.ByteMemory.ofU32Words [ 0#32 ]) ] []

#guard mslAtomVsNonAtomRaceResult == .dataRace .device 0

theorem msl_atomic_vs_nonatomic_race_checked :
    mslAtomVsNonAtomRaceResult = .dataRace .device 0 := rfl

def mslRankPromotionResult : MSLOutcome (BitVec 64) :=
  evalMSLExpr mslEmptyGroup
    { tid := {}, locals := mslLocalsRxRy 0xFFFF_FFFF#64 1#64 .uint .ulong, stmts := [], halted := false }
    (.add (.var "rx") (.var "ry"))

def mslSignedShrResult : MSLOutcome (BitVec 64) :=
  evalMSLExpr mslEmptyGroup
    { tid := {}, locals := mslLocalsRxRy 0xFFFF_FFF8#64 1#64 .int .uint, stmts := [], halted := false }
    (.shr (.var "rx") (.var "ry"))

def mslUintMaskCmpResult : MSLOutcome (BitVec 64) :=
  evalMSLExpr mslEmptyGroup
    { tid := {}, locals := mslLocalsRxRy 0x1_0000_0005#64 5#64 .uint .uint, stmts := [], halted := false }
    (.eq (.var "rx") (.var "ry"))

#guard mslRankPromotionResult == .ok 0x1_0000_0000#64
#guard mslSignedShrResult == .ok 0xFFFF_FFFC#64
#guard mslUintMaskCmpResult == .ok 1#64

theorem msl_rank_promotion_signed_shr_and_uint_cmp_checked :
    mslRankPromotionResult = .ok 0x1_0000_0000#64 ∧
    mslSignedShrResult = .ok 0xFFFF_FFFC#64 ∧
    mslUintMaskCmpResult = .ok 1#64 := ⟨rfl, rfl, rfl⟩

def ptxReadU32? (res : PTXRes) (elemIdx : Nat) : Option (BitVec 32) :=
  match res with
  | .ok mem => (mem.loadBits (elemIdx * 4) 4).map (fun v => v.truncate 32)
  | _ => none

def ptxCvtRzResult : PTXRes :=
  evalPTXKernel 8
    { name := "ptx_cvt_rz_fail"
    , params := []
    , regDecls := [ { ty := .u64, prefixName := "%rd", count := 1 }
                  , { ty := .f32, prefixName := "%f", count := 1 } ]
    , body :=
        [ .instr none (.cvt .rz .f32 .u64 "%f0" (.immU64 3#64))
        , .instr none .ret ] }
    { x := 1 } { x := 1 }
    (LeanNative.Backend.PTXAst.ByteMemory.zeros 0) { params := [] }

#guard ptxCvtRzResult == .unsupportedFloatOp "cvt.rz int-to-float"

theorem ptx_cvt_rz_int_to_float_rejected :
    ptxCvtRzResult = .unsupportedFloatOp "cvt.rz int-to-float" := rfl

def ptxS32Kernel : PTXKernel where
  name := "ptx_s32_canonical"
  params := [ { ty := .u64, name := "buf" } ]
  regDecls := [ { ty := .s32, prefixName := "%r", count := 3 }
              , { ty := .u32, prefixName := "%ru", count := 1 }
              , { ty := .u64, prefixName := "%rd", count := 1 }
              , { ty := .pred, prefixName := "%p", count := 1 } ]
  body :=
    [ .instr none (.ldParam .u64 "%rd0" "buf")
    , .instr none (.ldGlobal .s32 "%r0" (.regOffset "%rd0" 0))
    , .instr none (.mov .s32 "%r2" (.immS64 (-1)))
    , .instr none (.setp .eq .s32 "%p0" (.reg "%r0") (.reg "%r2"))
    , .instr none (.selp .u32 "%ru0" (.immU64 1#64) (.immU64 0#64) "%p0")
    , .instr none (.add .none .s32 "%r1" (.reg "%r0") (.immU64 2#64))
    , .instr none (.stGlobal .s32 (.regOffset "%rd0" 4) (.reg "%r1"))
    , .instr none (.stGlobal .u32 (.regOffset "%rd0" 8) (.reg "%ru0"))
    , .instr none .ret ]

def ptxS32Result : PTXRes :=
  evalPTXKernel 24 ptxS32Kernel { x := 1 } { x := 1 }
    (LeanNative.Backend.PTXAst.ByteMemory.ofU64Words [ 0x0000_0000_FFFF_FFFF#64, 0#64 ])
    { params := [ ("buf", 0#64) ] }

#guard ptxReadU32? ptxS32Result 1 == some 1#32
#guard ptxReadU32? ptxS32Result 2 == some 1#32

theorem ptx_s32_canonical_add_checked :
    ptxReadU32? ptxS32Result 1 = some 1#32 ∧
    ptxReadU32? ptxS32Result 2 = some 1#32 := ⟨rfl, rfl⟩

def ptxMadHiKernel : PTXKernel where
  name := "ptx_mad_hi"
  params := [ { ty := .u64, name := "buf" } ]
  regDecls := [ { ty := .u32, prefixName := "%r", count := 1 }
              , { ty := .s32, prefixName := "%rs", count := 1 }
              , { ty := .u64, prefixName := "%rd", count := 1 } ]
  body :=
    [ .instr none (.ldParam .u64 "%rd0" "buf")
    , .instr none (.mad .hi .u32 "%r0" (.immU64 0x1_0000#64) (.immU64 0x1_0000#64) (.immU64 3#64))
    , .instr none (.stGlobal .u32 (.regOffset "%rd0" 0) (.reg "%r0"))
    , .instr none (.mad .hi .s32 "%rs0" (.immU64 0x8000_0000#64) (.immU64 2#64) (.immU64 5#64))
    , .instr none (.stGlobal .s32 (.regOffset "%rd0" 4) (.reg "%rs0"))
    , .instr none .ret ]

def ptxMadHiResult : PTXRes :=
  evalPTXKernel 16 ptxMadHiKernel { x := 1 } { x := 1 }
    (LeanNative.Backend.PTXAst.ByteMemory.zeros 8)
    { params := [ ("buf", 0#64) ] }

#guard ptxReadU32? ptxMadHiResult 0 == some 4#32
#guard ptxReadU32? ptxMadHiResult 1 == some 4#32

theorem ptx_mad_hi_u32_s32_checked :
    ptxReadU32? ptxMadHiResult 0 = some 4#32 ∧
    ptxReadU32? ptxMadHiResult 1 = some 4#32 := ⟨rfl, rfl⟩

def ptxMadWideU64Result : PTXRes :=
  evalPTXKernel 8
    { name := "ptx_mad_wide_u64"
    , params := []
    , regDecls := [ { ty := .u64, prefixName := "%rd", count := 1 } ]
    , body :=
        [ .instr none (.mad .wide .u64 "%rd0" (.immU64 2#64) (.immU64 3#64) (.immU64 1#64))
        , .instr none .ret ] }
    { x := 1 } { x := 1 }
    (LeanNative.Backend.PTXAst.ByteMemory.zeros 0) { params := [] }

#guard ptxMadWideU64Result == .typeMismatch "mad.wide requires a 32-bit integer type"

theorem ptx_mad_wide_u64_rejected :
    ptxMadWideU64Result = .typeMismatch "mad.wide requires a 32-bit integer type" := rfl

def ptxCrossCtaRaceKernel : PTXKernel where
  name := "ptx_cross_cta_race"
  params := [ { ty := .u64, name := "buf" } ]
  regDecls := [ { ty := .u64, prefixName := "%rd", count := 1 } ]
  body :=
    [ .instr none (.ldParam .u64 "%rd0" "buf")
    , .instr none (.barSync 0)
    , .instr none (.stGlobal .u64 (.regOffset "%rd0" 0) (.immU64 1#64))
    , .instr none .ret ]

def ptxCrossCtaRaceResult : PTXRes :=
  evalPTXKernel 32 ptxCrossCtaRaceKernel { x := 2 } { x := 1 }
    (LeanNative.Backend.PTXAst.ByteMemory.zeros 8)
    { params := [ ("buf", 0#64) ] }

#guard ptxCrossCtaRaceResult == .dataRace .global 0

theorem ptx_cross_cta_global_race_checked :
    ptxCrossCtaRaceResult = .dataRace .global 0 := rfl

def ptxCrossCtaAtomKernel : PTXKernel where
  name := "ptx_cross_cta_atom"
  params := [ { ty := .u64, name := "buf" } ]
  regDecls := [ { ty := .u64, prefixName := "%rd", count := 2 } ]
  body :=
    [ .instr none (.ldParam .u64 "%rd0" "buf")
    , .instr none (.barSync 0)
    , .instr none (.atomAdd .global .u64 "%rd1" (.regOffset "%rd0" 0) (.immU64 1#64))
    , .instr none .ret ]

def ptxCrossCtaAtomResult : PTXRes :=
  evalPTXKernel 32 ptxCrossCtaAtomKernel { x := 2 } { x := 1 }
    (LeanNative.Backend.PTXAst.ByteMemory.zeros 8)
    { params := [ ("buf", 0#64) ] }

#guard ptxReadWord? ptxCrossCtaAtomResult 0 == some 2#64

theorem ptx_cross_cta_atomic_add_checked :
    ptxReadWord? ptxCrossCtaAtomResult 0 = some 2#64 := rfl

def mslCrossGroupRaceKernel : MSLKernelDecl where
  name := "msl_cross_group_race"
  params := [ { ty := .pointer .device false .ulong, name := "buf", attr := some (.buffer 0) } ]
  body :=
    [ .threadgroupBarrier
    , .indexAssign "buf" (.immU64 0#64) (.immU64 1#64)
    , .returnStmt ]

def mslCrossGroupRaceResult : MSLRes :=
  evalMSLKernel 16 mslCrossGroupRaceKernel { x := 2 } { x := 1 }
    [ (0, LeanNative.Backend.MetalAst.ByteMemory.zeros 8) ] []

#guard mslCrossGroupRaceResult == .dataRace .device 0

theorem msl_cross_group_device_race_checked :
    mslCrossGroupRaceResult = .dataRace .device 0 := rfl

def mslCrossGroupAtomKernel : MSLKernelDecl where
  name := "msl_cross_group_atom"
  params := [ { ty := .pointer .device false .atomicUint, name := "acc", attr := some (.buffer 0) } ]
  body :=
    [ .threadgroupBarrier
    , .atomicFetchAdd none none "acc" (some (.immU64 0#64)) (.immU64 1#64)
    , .returnStmt ]

def mslCrossGroupAtomResult : MSLRes :=
  evalMSLKernel 16 mslCrossGroupAtomKernel { x := 2 } { x := 1 }
    [ (0, LeanNative.Backend.MetalAst.ByteMemory.ofU32Words [ 0#32 ]) ] []

#guard mslReadU32? mslCrossGroupAtomResult 0 0 == some 2#32

theorem msl_cross_group_atomic_add_checked :
    mslReadU32? mslCrossGroupAtomResult 0 0 = some 2#32 := rfl

/-! ## 15. Structural Pretty-Printer Smoke Checks (`PTXModule` and `MSLModule`) -/

def hasSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

def ptxSampleModule : PTXModule where
  kernels := [ ptxVecAddKernel, ptxReduceKernel, ptxAtomCasKernel ]

def mslSampleModule : MSLModule where
  structs := [ { name := "ln_u256", fields := [ { ty := .ulong, name := "w0" } ] } ]
  kernels := [ mslVecAddKernel, mslReduceKernel, mslUlong2Kernel, mslPtrAtomicDerefKernel ]

#guard hasSubstr (ppPTXModule ptxSampleModule) ".version 8.0"
#guard hasSubstr (ppPTXModule ptxSampleModule) ".visible .entry vec_add_u64("
#guard hasSubstr (ppPTXModule ptxSampleModule) "bar.sync 0;"
#guard hasSubstr (ppPTXModule ptxSampleModule) ".shared .align 8 .u64 smem[2];"
#guard hasSubstr (ppPTXModule ptxSampleModule) ".reg .u64 %rd<11>;"
#guard hasSubstr (ppPTXModule ptxSampleModule) "atom.global.cas.u64"

#guard hasSubstr (ppMSLModule mslSampleModule) "#include <metal_stdlib>"
#guard hasSubstr (ppMSLModule mslSampleModule) "using namespace metal;"
#guard hasSubstr (ppMSLModule mslSampleModule) "kernel void vec_add_u64("
#guard hasSubstr (ppMSLModule mslSampleModule) "threadgroup ulong smem[2];"
#guard hasSubstr (ppMSLModule mslSampleModule)
  "threadgroup_barrier(mem_flags::mem_threadgroup);"
#guard hasSubstr (ppMSLModule mslSampleModule) "ulong2("
#guard hasSubstr (ppMSLModule mslSampleModule) "atomic_exchange_explicit(lockPtr, "

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

/-! ## 16. Track `D6` — early-`ret` barrier generations, read-oracle atomics, and multi-kernel seq -/

def ptxEarlyRetBarSyncKernel : PTXKernel where
  name := "ptx_early_ret_bar_sync"
  params := [ { ty := .u64, name := "out" } ]
  regDecls := [ { ty := .u32, prefixName := "%r", count := 1 }
              , { ty := .u64, prefixName := "%rd", count := 1 }
              , { ty := .pred, prefixName := "%p", count := 1 } ]
  body :=
    [ .instr none (.mov .u32 "%r0" (.sreg .tidX))
    , .instr none (.setp .eq .u32 "%p0" (.reg "%r0") (.immU64 0#64))
    , .instr (some { predReg := "%p0" }) .ret
    , .instr none (.barSync 0)
    , .instr none (.ldParam .u64 "%rd0" "out")
    , .instr none (.stGlobal .u64 (.regOffset "%rd0" 0) (.immU64 99#64))
    , .instr none .ret ]

def ptxEarlyRetBarSyncResult : PTXRes :=
  evalPTXKernel 32 ptxEarlyRetBarSyncKernel { x := 1 } { x := 2 }
    (LeanNative.Backend.PTXAst.ByteMemory.ofU64Words [ 0#64 ])
    { params := [ ("out", 0#64) ] }

#guard ptxReadWord? ptxEarlyRetBarSyncResult 0 == some 99#64

theorem ptx_early_ret_bar_sync_checked :
    ptxReadWord? ptxEarlyRetBarSyncResult 0 = some 99#64 := rfl

def ptxD6MultiKernelWriteKernel : PTXKernel where
  name := "ptx_d6_multi_write"
  params := [ { ty := .u64, name := "buf" } ]
  regDecls := [ { ty := .u64, prefixName := "%rd", count := 1 } ]
  body :=
    [ .instr none (.ldParam .u64 "%rd0" "buf")
    , .instr none (.stGlobal .u64 (.regOffset "%rd0" 0) (.immU64 41#64))
    , .instr none .ret ]

def ptxD6MultiKernelIncKernel : PTXKernel where
  name := "ptx_d6_multi_inc"
  params := [ { ty := .u64, name := "buf" } ]
  regDecls := [ { ty := .u64, prefixName := "%rd", count := 2 } ]
  body :=
    [ .instr none (.ldParam .u64 "%rd0" "buf")
    , .instr none (.ldGlobal .u64 "%rd1" (.regOffset "%rd0" 0))
    , .instr none (.add .none .u64 "%rd1" (.reg "%rd1") (.immU64 1#64))
    , .instr none (.stGlobal .u64 (.regOffset "%rd0" 0) (.reg "%rd1"))
    , .instr none .ret ]

def ptxD6MultiKernelResult : Option (BitVec 64 × Nat) :=
  match evalPTXMultiKernelSeq
      [ { fuelPerCTA := 16
        , kernel := ptxD6MultiKernelWriteKernel
        , gridDim := { x := 1 }
        , blockDim := { x := 1 }
        , paramMem := { params := [ ("buf", 0#64) ] } }
      , { fuelPerCTA := 16
        , kernel := ptxD6MultiKernelIncKernel
        , gridDim := { x := 1 }
        , blockDim := { x := 1 }
        , paramMem := { params := [ ("buf", 0#64) ] } } ]
      (LeanNative.Backend.PTXAst.ByteMemory.ofU64Words [ 0#64 ]) with
  | .ok (gFinal, evs) =>
    match gFinal.readU64Word? 0 with
    | some w => some (w, evs.length)
    | none => none
  | _ => none

#guard ptxD6MultiKernelResult == some (42#64, 3)

theorem ptx_d6_multi_kernel_seq_checked :
    ptxD6MultiKernelResult = some (42#64, 3) := rfl

end LeanNative.Tests.GpuAstTests
