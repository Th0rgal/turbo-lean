import LeanNative.Backend.LLVMAst
import LeanNative.Backend.PTXAst
import LeanNative.Backend.StableHLOAst
import LeanNative.Backend.MetalAst

/-!
# Stage 4 Target-IR Two-Sided UB/Trap & OpenXLA Alignment Proofs (`LeanNative.Proofs.TargetIRFuzzProofs`)

Machine-checked (`0 sorryAx`, `0 native_decide`) kernel theorems establishing the exact
operational UB/trap and edge-case semantics exercised by Stage 4's seeded multi-backend
differential fuzzer (`target-ir-fuzz-suite` / `scripts/run_target_ir_fuzz.py`):

1. `llvm_sdiv64_min_neg1_ub`: `LLVMAst.stepInstr` traps with `.ub "signed division overflow"` on
   `sdiv i64 INT64_MIN, -1` (matching native `opt -passes=asan` + `clang -O0 -fsanitize=address`).
2. `llvm_null_load_ub`: `LLVMAst.stepInstr` traps with `.ub "load from null pointer"` on
   `load ty, ptr null`.
3. `llvm_null_store_ub`: `LLVMAst.stepInstr` traps with `.ub "store to null pointer"` on
   `store ty v, ptr null`.
4. `llvm_oob_gep_inbounds_load_ub`: out-of-allocation `getelementptr inbounds` produces a
   `.poison` pointer whose dereference via `load` traps with `.ub "load from poison pointer"`.
5. `stablehlo_sdiv64_min_neg1_eq`: OpenXLA-aligned `StableHLOAst.sdivWidth 64` evaluates
   `INT64_MIN / -1` to `.ok INT64_MIN` without trapping.
6. `stablehlo_srem64_min_neg1_zero`: OpenXLA-aligned `StableHLOAst.sremWidth 64` evaluates
   `INT64_MIN % -1` to `.ok 0#64` without trapping.
7. `stablehlo_sdiv_zero_traps`: `StableHLOAst.sdivWidth w x 0` traps with `.error .divisionByZero`
   for every width `w` and dividend `x`.
8. `stablehlo_clampStart_bounds`: `StableHLOAst.clampStart dim sz s` clamps arbitrary signed
   `dynamic_slice` indices `s : Int` into `[0, dim - sz]` whenever `sz ≤ dim`.
9. `msl_shift_out_of_range_traps`: `MetalAst.evalMSLExpr` traps with `MSLOutcome.shiftOutOfRange`
   whenever a `ulong` shift amount satisfies `amt ≥ 64`.
10. `ptx_rem_zero_traps`: `PTXAst.execNonBarrierInstr` traps with `PTXOutcome.divisionByZero`
    on integer `rem` by zero across all PTX integer/bit-size types.
-/

namespace LeanNative.Proofs

open LeanNative.Backend.TargetIR
open LeanNative.Backend

/-- Signed 64-bit `sdiv INT64_MIN, -1` traps with `.ub "signed division overflow"` in `LLVMAst`. -/
theorem llvm_sdiv64_min_neg1_ub (st : LLVMAst.ExecState) (dst : RegName) (exact : Bool) :
    LLVMAst.stepInstr {} 1 st
      (.sdiv dst exact .i64
        (.constInt .i64 0x8000000000000000#64)
        (.constInt .i64 0xFFFFFFFFFFFFFFFF#64)) =
      .inl (.ub "signed division overflow") := rfl

/-- Loading from `null` traps with `.ub "load from null pointer"` in `LLVMAst`. -/
theorem llvm_null_load_ub (st : LLVMAst.ExecState) (dst : RegName) (vol : Bool)
    (ty : LLVMAst.LLVMType) (align : Nat) :
    LLVMAst.stepInstr {} 1 st (.load dst vol ty .constNull align) =
      .inl (.ub "load from null pointer") := by
  simp [LLVMAst.stepInstr, LLVMAst.stepInstrWith, LLVMAst.evalOperand, LLVMAst.accessCheck]

/-- Storing to `null` traps with `.ub "store to null pointer"` in `LLVMAst`. -/
theorem llvm_null_store_ub (st : LLVMAst.ExecState) (vol : Bool) (ty : LLVMAst.LLVMType)
    (valOp : LLVMAst.Operand) (align : Nat) :
    LLVMAst.stepInstr {} 1 st (.store vol ty valOp .constNull align) =
      .inl (.ub "store to null pointer") := by
  simp [LLVMAst.stepInstr, LLVMAst.stepInstrWith, LLVMAst.evalOperand, LLVMAst.accessCheck]

/-- Out-of-allocation `getelementptr inbounds i64, ptr %p, i64 2` on an 8-byte `alloca i64`
    yields `.poison`, and loading through that pointer traps with `.ub "load from poison pointer"`. -/
theorem llvm_oob_gep_inbounds_load_ub (m0 m1 : ByteMem) (ptr : BitVec 64)
    (h_alloc : m0.allocAligned 8 8 = some (ptr, m1))
    (h_oob : m1.inboundsInAlloc ptr.toNat (Int.ofNat ptr.toNat + 16) = false) :
    let st1 : LLVMAst.ExecState := { mem := m1, regs := [("p", .ptr ptr)] }
    ∃ st2 : LLVMAst.ExecState,
      LLVMAst.stepInstr {} 1 st1
        (.getelementptr "oob" true (.int .i64) (.reg "p") [(.i64, .constInt .i64 2#64)]) =
        .inr st2 ∧
      LLVMAst.stepInstr {} 1 st2 (.load "r" false (.int .i64) (.reg "oob") 8) =
        .inl (.ub "load from poison pointer") := by
  let _ := h_alloc
  refine ⟨LLVMAst.bindReg { mem := m1, regs := [("p", .ptr ptr)] } "oob" .poison, ?_, ?_⟩
  · have hoff : LLVMAst.gepOffset (.int .i64) [(2, .i64)] = some 16 := rfl
    have hidx : LLVMAst.gepIndexSigned .i64 2#64 = 2 := rfl
    have h_oob' : m1.inboundsInAlloc ptr.toNat (↑ptr.toNat + 16) = false := h_oob
    simp [LLVMAst.stepInstr, LLVMAst.stepInstrWith, LLVMAst.evalOperand, LLVMAst.lookupReg,
      LLVMAst.gepResult, LLVMAst.isPoison, hidx, hoff, h_oob']
  · simp [LLVMAst.stepInstr, LLVMAst.stepInstrWith, LLVMAst.evalOperand, LLVMAst.lookupReg,
      LLVMAst.bindReg]

/-- OpenXLA StableHLO signed 64-bit `INT64_MIN / -1` evaluates to `INT64_MIN` without trapping. -/
theorem stablehlo_sdiv64_min_neg1_eq :
    StableHLOAst.sdivWidth 64 0x8000000000000000#64 0xFFFFFFFFFFFFFFFF#64 =
      .ok 0x8000000000000000#64 := rfl

/-- OpenXLA StableHLO signed 64-bit `INT64_MIN % -1` evaluates to `0#64` without trapping. -/
theorem stablehlo_srem64_min_neg1_zero :
    StableHLOAst.sremWidth 64 0x8000000000000000#64 0xFFFFFFFFFFFFFFFF#64 =
      .ok 0#64 := rfl

/-- `StableHLOAst.sdivWidth w x 0` traps with `.error .divisionByZero` for every width `w` and `x`. -/
theorem stablehlo_sdiv_zero_traps (w : Nat) (x : BitVec 64) :
    StableHLOAst.sdivWidth w x 0#64 = .error .divisionByZero := by
  have hz : StableHLOAst.maskWidth w 0#64 = 0#64 := by
    unfold StableHLOAst.maskWidth
    split <;> simp
  simp [StableHLOAst.sdivWidth, hz]

/-- `StableHLOAst.clampStart dim sz s` always produces a valid start offset `≤ dim - sz`. -/
theorem stablehlo_clampStart_bounds (dim sz : Nat) (s : Int) :
    StableHLOAst.clampStart dim sz s ≤ dim - sz := by
  simp only [StableHLOAst.clampStart, Int.ofNat_eq_natCast]
  split <;> split <;> omega

/-- Shifting a 64-bit `ulong` by `amt ≥ 64` in `MetalAst` traps with `MSLOutcome.shiftOutOfRange`. -/
theorem msl_shift_out_of_range_traps (g : MetalAst.MSLGroupState) (th : MetalAst.MSLThreadState)
    (rx rs : String) (vx vs : BitVec 64)
    (h_rx : th.locals.lookup? rx = some vx)
    (h_tyx : th.locals.lookupType? rx = some .ulong)
    (h_rs : th.locals.lookup? rs = some vs)
    (h_tys : th.locals.lookupType? rs = some .ulong)
    (h_over : 64 ≤ vs.toNat) :
    MetalAst.evalMSLExpr g th (.shl (.var rx) (.var rs)) = .shiftOutOfRange := by
  simp [MetalAst.evalMSLExpr, MetalAst.evalExprWithCall, MetalAst.bindEval, MetalAst.finishShift,
    MetalAst.inferExprType, MetalAst.MSLType.isFloat, MetalAst.MSLType.isVector,
    MetalAst.MSLType.bitWidth, MetalAst.propagateErr, h_rx, h_tyx, h_rs, h_tys, h_over]

/-- Integer remainder by zero traps with `PTXOutcome.divisionByZero` across all PTX integer/bit-size
    types (never silently returning dividend or `0`). -/
theorem ptx_rem_zero_traps (stmts : List PTXAst.PTXStmt) (cta : PTXAst.PTXCTAState)
    (th : PTXAst.PTXThreadState) (ty : PTXAst.PTXType) (dst : String) (a b : PTXAst.PTXOperand)
    (va : BitVec 64)
    (h_int : ty ≠ .f32 ∧ ty ≠ .f64)
    (h_a : PTXAst.evalOperand cta th a (some ty.bitWidth) = .ok va)
    (h_b : PTXAst.evalOperand cta th b (some ty.bitWidth) = .ok 0#64) :
    PTXAst.execNonBarrierInstr stmts cta th (.rem ty dst a b) = .divisionByZero := by
  rcases h_int with ⟨hf32, hf64⟩
  dsimp [PTXAst.execNonBarrierInstr, PTXAst.PTXOutcome.bind]
  rw [h_a, h_b]
  dsimp only
  cases ty <;>
    first
    | exact absurd rfl hf32
    | exact absurd rfl hf64
    | rfl

end LeanNative.Proofs
