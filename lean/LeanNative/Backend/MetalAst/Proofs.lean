import LeanNative.Backend.MetalAst.Eval
import Std.Tactic.BVDecide

/-!
# Metal MSL 3.0 Kernel-Checked Theorems (`LeanNative.Backend.MetalAst.Proofs`)

Kernel-checked theorems over `LeanNative.Backend.MetalAst`:
- `constant` and `device const` write rejection and multi-step `constantBuffers` immutability
- `device` / `threadgroup` / `thread` address-space isolation
- Out-of-bounds `device` and `thread` stack-array load/write trapping
- Division-by-zero, signed 32-bit overflow, shift-out-of-range, and float `%` traps
- Short-circuit C++ `?:`, `&&`, and `||` vs eager `metal::select`
- Integer rank promotion (`promoteMSLArithType`) and signed arithmetic right shift (`>>`)
- Multi-lane vector (`uint2`, `ulong2`, `uint4`) and struct (`ln_u256`) load/store roundtrip
- Epoch data-race detection: disjoint safety, non-atomic overlap race, atomic-atomic compatibility,
  and atomic-vs-non-atomic race detection
- Single-pass `stepSimdgroup` evaluation (evaluating `srcExpr` once per active lane)
- Lockstep `threadgroup_barrier` convergence vs divergence
- Monotone fuel stability (`runGroup_mono_fuel`) and fuel-independent determinism
- Pretty-printer structural well-formedness (`ppMSLModule`, `ppMSLKernel`, `ppMSLType`, `ppMSLStmt`)
-/

namespace LeanNative.Backend.MetalAst

/-- `writeDeviceBuffer` never alters `constantBuffers` or `threadgroupArrays`. -/
theorem writeDeviceBuffer_preserves_const_and_tg (g g' : MSLGroupState)
    (bufIdx : Nat) (elemTy : MSLType) (elemIdx : Nat) (val : BitVec 64)
    (fields : List (String × BitVec 64))
    (h : writeDeviceBuffer g bufIdx elemTy elemIdx val fields = .ok g') :
    g'.constantBuffers = g.constantBuffers ∧ g'.threadgroupArrays = g.threadgroupArrays := by
  unfold writeDeviceBuffer at h
  cases hLookup : g.deviceBuffers.lookup bufIdx <;> simp [hLookup] at h
  case some mem =>
    cases hStore : storeTypedElem g.structs mem elemTy
        (elemIdx * aggregateByteWidth g.structs elemTy) val fields <;>
      simp [hStore] at h
    subst h
    exact ⟨rfl, rfl⟩

/-- `writeThreadgroupArray` never alters `constantBuffers` or `deviceBuffers`. -/
theorem writeThreadgroupArray_preserves_const_and_dev (g g' : MSLGroupState)
    (arrName : String) (elemTy : MSLType) (elemIdx : Nat) (val : BitVec 64)
    (fields : List (String × BitVec 64))
    (h : writeThreadgroupArray g arrName elemTy elemIdx val fields = .ok g') :
    g'.constantBuffers = g.constantBuffers ∧ g'.deviceBuffers = g.deviceBuffers := by
  unfold writeThreadgroupArray at h
  cases hLookup : g.threadgroupArrays.lookup arrName <;> simp [hLookup] at h
  case some mem =>
    cases hStore : storeTypedElem g.structs mem elemTy
        (elemIdx * aggregateByteWidth g.structs elemTy) val fields <;>
      simp [hStore] at h
    subst h
    exact ⟨rfl, rfl⟩

/-- `execIndexWrite` preserves `constantBuffers` across every address space and atomicity mode. -/
theorem execIndexWrite_preserves_constant_buffers (g g' : MSLGroupState)
    (tid : Dim3) (target : String) (elemIdx : Nat) (val : BitVec 64)
    (fields : List (String × BitVec 64)) (atomic : Bool)
    (h : execIndexWrite g tid target elemIdx val fields atomic = .ok g') :
    g'.constantBuffers = g.constantBuffers := by
  unfold execIndexWrite at h
  cases hBind : g.bindings.lookup target <;> simp [hBind] at h
  case some binding =>
    cases binding with
    | constantBuf _ _ => simp at h
    | constantScalar _ _ => simp at h
    | deviceBuf bufIdx isConst elemTy =>
      cases isConst <;> simp at h
      cases hRec : recordEpochAccess g.epochLog tid (.deviceBuf bufIdx) .device
          (elemIdx * aggregateByteWidth g.structs elemTy)
          (aggregateByteWidth g.structs elemTy) true atomic <;>
        simp [hRec, propagateErr] at h
      case ok log' =>
        exact (writeDeviceBuffer_preserves_const_and_tg
          { g with epochLog := log' } g' bufIdx elemTy elemIdx val fields h).1
    | threadgroupArr arrName elemTy =>
      simp at h
      cases hRec : recordEpochAccess g.epochLog tid (.threadgroupArr arrName) .threadgroup
          (elemIdx * aggregateByteWidth g.structs elemTy)
          (aggregateByteWidth g.structs elemTy) true atomic <;>
        simp [hRec, propagateErr] at h
      case ok log' =>
        exact (writeThreadgroupArray_preserves_const_and_dev
          { g with epochLog := log' } g' arrName elemTy elemIdx val fields h).1

/-- `execAtomicRMW` preserves `constantBuffers` across both `device` and `threadgroup` targets. -/
theorem execAtomicRMW_preserves_constant_buffers (g g' : MSLGroupState)
    (tid : Dim3) (ls ls' : MSLLocals) (declTy : Option MSLType) (dst : Option String)
    (target : String) (elemIdx : Nat) (rmw : MSLType → BitVec 64 → BitVec 64)
    (h : execAtomicRMW g tid ls declTy dst target elemIdx rmw = .ok (ls', g')) :
    g'.constantBuffers = g.constantBuffers := by
  unfold execAtomicRMW at h
  cases hB : g.bindings.lookup target <;> simp [hB] at h
  case some b =>
    cases b with
    | constantBuf _ _ => simp at h
    | constantScalar _ _ => simp at h
    | deviceBuf bufIdx isConst elemTy =>
      cases isConst <;> simp at h
      cases hM : g.deviceBuffers.lookup bufIdx <;> simp [hM] at h
      case some mem =>
        cases hL : mem.loadBits (elemIdx * aggregateByteWidth g.structs elemTy)
            elemTy.byteWidth <;> simp [hL] at h
        case some old =>
          cases hW : execIndexWrite g tid target elemIdx
              (maskForType elemTy (rmw elemTy (maskForType elemTy old))) [] true <;>
            simp [hW, propagateErr] at h
          case ok gMid =>
            rw [← h.2]
            exact execIndexWrite_preserves_constant_buffers g gMid tid target elemIdx _ [] true hW
    | threadgroupArr arrName elemTy =>
      simp at h
      cases hM : g.threadgroupArrays.lookup arrName <;> simp [hM] at h
      case some mem =>
        cases hL : mem.loadBits (elemIdx * aggregateByteWidth g.structs elemTy)
            elemTy.byteWidth <;> simp [hL] at h
        case some old =>
          cases hW : execIndexWrite g tid target elemIdx
              (maskForType elemTy (rmw elemTy (maskForType elemTy old))) [] true <;>
            simp [hW, propagateErr] at h
          case ok gMid =>
            rw [← h.2]
            exact execIndexWrite_preserves_constant_buffers g gMid tid target elemIdx _ [] true hW

/-- `constant` address-space immutability (statement level): executing ANY `MSLStmt` preserves
    `g.constantBuffers` bit-identically whenever it succeeds. -/
theorem exec_preserves_constant_buffers (g : MSLGroupState) (th : MSLThreadState)
    (stmt : MSLStmt) (rest : List MSLStmt) (th' : MSLThreadState) (g' : MSLGroupState)
    (h : execNonBarrierStmt g th stmt rest = .ok (th', g')) :
    g'.constantBuffers = g.constantBuffers := by
  unfold execNonBarrierStmt execStmtWithCall at h
  cases stmt with
  | varDecl ty name rhs =>
    dsimp only at h
    split at h
    · rename_i bufIdx elemTy _
      cases hC : g.constantBuffers.lookup bufIdx <;> simp [hC] at h
      case some mem =>
        cases hL : loadTypedElem g.structs mem elemTy 0 <;> simp [hL] at h
        rw [← h.2]
    · cases hE : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog rhs <;>
        simp [hE, propagateErr] at h
      rw [← h.2]
  | arrayDecl elemTy name count initList =>
    dsimp only at h
    cases hE : evalExprSlotList kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog initList <;>
      simp [hE, propagateErr] at h
    rw [← h.2]
  | assign name rhs =>
    dsimp only at h
    cases hE : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog rhs <;>
      simp [hE, propagateErr] at h
    rw [← h.2]
  | fieldAssign varName field rhs =>
    dsimp only at h
    cases hE : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog rhs <;>
      simp [hE, propagateErr] at h
    rw [← h.2]
  | indexAssign target idxExpr rhsExpr =>
    dsimp only at h
    cases hI : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog idxExpr <;>
      simp [hI, propagateErr] at h
    case ok ei =>
      cases hR : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid ei.locals ei.log rhsExpr <;>
        simp [hR] at h
      case ok er =>
        cases hArr : er.locals.lookupArray? target with
        | some slots =>
          simp [hArr] at h
          cases hUpd : updateArraySlot g.structs
              ((er.locals.lookupType? target).getD (inferExprType g er.locals rhsExpr))
              slots ei.value.toNat er.value er.fields <;>
            simp [hUpd] at h
          rw [← h.2]
        | none =>
          simp [hArr] at h
          cases hW : execIndexWrite { g with epochLog := er.log } th.tid target
              ei.value.toNat er.value er.fields false <;>
            simp [hW] at h
          case ok gMid =>
            rw [← h.2]
            exact execIndexWrite_preserves_constant_buffers
              { g with epochLog := er.log } gMid th.tid target ei.value.toNat er.value er.fields false hW
  | derefAssign ptrName rhsExpr =>
    dsimp only at h
    cases hR : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog rhsExpr <;>
      simp [hR, propagateErr] at h
    case ok er =>
      cases hArr : er.locals.lookupArray? ptrName with
      | some slots =>
        simp [hArr] at h
        cases hUpd : updateArraySlot g.structs
            ((er.locals.lookupType? ptrName).getD (inferExprType g er.locals rhsExpr))
            slots 0 er.value er.fields <;>
          simp [hUpd] at h
        rw [← h.2]
      | none =>
        simp [hArr] at h
        cases hW : execIndexWrite { g with epochLog := er.log } th.tid ptrName
            0 er.value er.fields false <;>
          simp [hW] at h
        case ok gMid =>
          rw [← h.2]
          exact execIndexWrite_preserves_constant_buffers
            { g with epochLog := er.log } gMid th.tid ptrName 0 er.value er.fields false hW
  | callAssign declTy dst fnName args =>
    dsimp only at h
    cases hC : kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog fnName args <;>
      simp [hC, propagateErr] at h
    rw [← h.2]
  | exprStmt e =>
    dsimp only at h
    cases hE : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog e <;>
      simp [hE, propagateErr] at h
    rw [← h.2]
  | atomicFetchAdd declTy dst target idxOpt valExpr =>
    dsimp only at h
    cases idxOpt with
    | none =>
      cases hV : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog valExpr <;>
        simp [hV, propagateErr] at h
      case ok ev =>
        cases hA : execAtomicRMW { g with epochLog := ev.log } th.tid ev.locals declTy dst target
            0 (fun _ old => old + ev.value) <;>
          simp [hA] at h
        case ok pair =>
          rw [← h.2]
          exact execAtomicRMW_preserves_constant_buffers
            { g with epochLog := ev.log } pair.2 th.tid ev.locals pair.1 declTy dst target
            0 _ hA
    | some idxExpr =>
      cases hI : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog idxExpr <;>
        simp [hI, propagateErr] at h
      case ok ei =>
        cases hV : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid ei.locals ei.log valExpr <;>
          simp [hV] at h
        case ok ev =>
          cases hA : execAtomicRMW { g with epochLog := ev.log } th.tid ev.locals declTy dst target
              ei.value.toNat (fun _ old => old + ev.value) <;>
            simp [hA] at h
          case ok pair =>
            rw [← h.2]
            exact execAtomicRMW_preserves_constant_buffers
              { g with epochLog := ev.log } pair.2 th.tid ev.locals pair.1 declTy dst target
              ei.value.toNat _ hA
  | atomicExchange declTy dst target idxOpt valExpr =>
    dsimp only at h
    cases idxOpt with
    | none =>
      cases hV : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog valExpr <;>
        simp [hV, propagateErr] at h
      case ok ev =>
        cases hA : execAtomicRMW { g with epochLog := ev.log } th.tid ev.locals declTy dst target
            0 (fun _ _ => ev.value) <;>
          simp [hA] at h
        case ok pair =>
          rw [← h.2]
          exact execAtomicRMW_preserves_constant_buffers
            { g with epochLog := ev.log } pair.2 th.tid ev.locals pair.1 declTy dst target
            0 _ hA
    | some idxExpr =>
      cases hI : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog idxExpr <;>
        simp [hI, propagateErr] at h
      case ok ei =>
        cases hV : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid ei.locals ei.log valExpr <;>
          simp [hV] at h
        case ok ev =>
          cases hA : execAtomicRMW { g with epochLog := ev.log } th.tid ev.locals declTy dst target
              ei.value.toNat (fun _ _ => ev.value) <;>
            simp [hA] at h
          case ok pair =>
            rw [← h.2]
            exact execAtomicRMW_preserves_constant_buffers
              { g with epochLog := ev.log } pair.2 th.tid ev.locals pair.1 declTy dst target
              ei.value.toNat _ hA
  | simdShuffleXor _ _ _ _ => simp at h
  | simdSum _ _ _ => simp at h
  | threadgroupBarrier => simp at h
  | ifElse cond thenBr elseBr =>
    dsimp only at h
    cases hC : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog cond <;>
      simp [hC, propagateErr] at h
    rw [← h.2]
  | forLoop loopVar ty initExpr condExpr stepExpr body =>
    dsimp only at h
    cases hInit : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog initExpr <;>
      simp [hInit, propagateErr] at h
    rw [← h.2]
  | whileLoop condExpr body =>
    dsimp only at h
    cases hC : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog condExpr <;>
      simp [hC, propagateErr] at h
    case ok ev =>
      split at h <;> simp at h <;> rw [← h.2]
  | returnVal e =>
    dsimp only at h
    cases hE : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog e <;>
      simp [hE, propagateErr] at h
    rw [← h.2]
  | returnStmt =>
    dsimp only at h
    simp at h
    rw [← h.2]

/-- Explicit write rejection for `constant` buffers: any indexed write targeting a `constant`
    buffer binding traps with `MSLOutcome.readOnlyViolation`. -/
theorem constant_write_rejected (g : MSLGroupState) (tid : Dim3) (target : String)
    (bufIdx : Nat) (elemTy : MSLType) (elemIdx : Nat) (val : BitVec 64)
    (fields : List (String × BitVec 64)) (atomic : Bool)
    (h_const : g.bindings.lookup target = some (.constantBuf bufIdx elemTy)) :
    execIndexWrite g tid target elemIdx val fields atomic = .readOnlyViolation target elemIdx := by
  unfold execIndexWrite
  rw [h_const]

/-- Explicit write rejection for `device const T*` buffers: any indexed write targeting a
    read-only `device const` pointer traps with `MSLOutcome.readOnlyViolation`. -/
theorem device_const_write_rejected (g : MSLGroupState) (tid : Dim3) (target : String)
    (bufIdx : Nat) (elemTy : MSLType) (elemIdx : Nat) (val : BitVec 64)
    (fields : List (String × BitVec 64)) (atomic : Bool)
    (h_ro : g.bindings.lookup target = some (.deviceBuf bufIdx true elemTy)) :
    execIndexWrite g tid target elemIdx val fields atomic = .readOnlyViolation target elemIdx := by
  unfold execIndexWrite
  rw [h_ro]

/-- Address-space isolation (`device` -> `threadgroup`): writing to a mutable `device` buffer
    never mutates per-threadgroup shared memory `threadgroupArrays`. -/
theorem device_write_preserves_threadgroup (g g' : MSLGroupState) (tid : Dim3) (target : String)
    (bufIdx : Nat) (elemTy : MSLType) (elemIdx : Nat) (val : BitVec 64)
    (fields : List (String × BitVec 64)) (atomic : Bool)
    (h_dev : g.bindings.lookup target = some (.deviceBuf bufIdx false elemTy))
    (h_exec : execIndexWrite g tid target elemIdx val fields atomic = .ok g') :
    g'.threadgroupArrays = g.threadgroupArrays := by
  unfold execIndexWrite at h_exec
  rw [h_dev] at h_exec
  dsimp only at h_exec
  cases hRec : recordEpochAccess g.epochLog tid (.deviceBuf bufIdx) .device
      (elemIdx * aggregateByteWidth g.structs elemTy)
      (aggregateByteWidth g.structs elemTy) true atomic <;>
    simp [hRec, propagateErr] at h_exec
  case ok log' =>
    exact (writeDeviceBuffer_preserves_const_and_tg
      { g with epochLog := log' } g' bufIdx elemTy elemIdx val fields h_exec).2

/-- Address-space isolation (`threadgroup` -> `device`): writing to a `threadgroup` shared array
    never mutates `deviceBuffers`. -/
theorem threadgroup_write_preserves_device (g g' : MSLGroupState) (tid : Dim3)
    (target arrName : String) (elemTy : MSLType) (elemIdx : Nat) (val : BitVec 64)
    (fields : List (String × BitVec 64)) (atomic : Bool)
    (h_tg : g.bindings.lookup target = some (.threadgroupArr arrName elemTy))
    (h_exec : execIndexWrite g tid target elemIdx val fields atomic = .ok g') :
    g'.deviceBuffers = g.deviceBuffers := by
  unfold execIndexWrite at h_exec
  rw [h_tg] at h_exec
  dsimp only at h_exec
  cases hRec : recordEpochAccess g.epochLog tid (.threadgroupArr arrName) .threadgroup
      (elemIdx * aggregateByteWidth g.structs elemTy)
      (aggregateByteWidth g.structs elemTy) true atomic <;>
    simp [hRec, propagateErr] at h_exec
  case ok log' =>
    exact (writeThreadgroupArray_preserves_const_and_dev
      { g with epochLog := log' } g' arrName elemTy elemIdx val fields h_exec).2

/-- Scalar out-of-bounds `device` buffer write safety: when `elemTy` is a scalar (`structFieldNames = []`)
    and `elemIdx * elemTy.byteWidth + elemTy.byteWidth > mem.bytes.size`, `writeDeviceBuffer`
    traps with `MSLOutcome.outOfBoundsWrite .device bufIdx elemIdx`. -/
theorem oob_device_write_caught (g : MSLGroupState) (bufIdx : Nat) (elemTy : MSLType)
    (elemIdx : Nat) (val : BitVec 64) (fields : List (String × BitVec 64)) (mem : ByteMemory)
    (h_scalar : structFieldNames g.structs elemTy = [])
    (h_w : aggregateByteWidth g.structs elemTy = elemTy.byteWidth)
    (h_buf : g.deviceBuffers.lookup bufIdx = some mem)
    (h_oob : mem.bytes.size < elemIdx * elemTy.byteWidth + elemTy.byteWidth) :
    writeDeviceBuffer g bufIdx elemTy elemIdx val fields =
      .outOfBoundsWrite .device bufIdx elemIdx := by
  unfold writeDeviceBuffer storeTypedElem
  rw [h_buf, h_w, h_scalar]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  unfold ByteMemory.storeBits
  have hNotLe : ¬ (elemIdx * elemTy.byteWidth + elemTy.byteWidth ≤ mem.bytes.size) :=
    Nat.not_le_of_gt h_oob
  simp [hNotLe]

/-- Out-of-bounds read on a `thread` local array (`arr[idx]` with `idx ≥ slots.length`) traps
    with `MSLOutcome.outOfBoundsLoad .thread 0 idx`. -/
theorem oob_thread_array_load_traps (g : MSLGroupState) (th : MSLThreadState)
    (arrName : String) (slots : List MSLLocalSlot) (idx : BitVec 64)
    (h_arr : th.locals.lookupArray? arrName = some slots)
    (h_oob : slots.length ≤ idx.toNat) :
    evalMSLExpr g th (.index arrName (.immU64 idx)) =
      .outOfBoundsLoad .thread 0 idx.toNat := by
  have hNone : slots[idx.toNat]? = none := List.getElem?_eq_none h_oob
  simp [evalMSLExpr, evalExprWithCall, bindEval, h_arr, hNone, propagateErr]

/-- Out-of-bounds write to a `thread` local array (`arr[idx] = v` with `idx ≥ slots.length`)
    traps with `MSLOutcome.outOfBoundsWrite .thread 0 idx`. -/
theorem oob_thread_array_write_traps (g : MSLGroupState) (th : MSLThreadState)
    (arrName : String) (slots : List MSLLocalSlot) (idx val : BitVec 64)
    (rest : List MSLStmt)
    (h_arr : th.locals.lookupArray? arrName = some slots)
    (h_oob : slots.length ≤ idx.toNat) :
    execNonBarrierStmt g th (.indexAssign arrName (.immU64 idx) (.immU64 val)) rest =
      .outOfBoundsWrite .thread 0 idx.toNat := by
  have hNotLt : ¬ (idx.toNat < slots.length) := Nat.not_lt.mpr h_oob
  simp [execNonBarrierStmt, execStmtWithCall, evalExprWithCall, updateArraySlot, h_arr, hNotLt]

private theorem promote_ulong_ulong : promoteMSLArithType .ulong .ulong = .ulong := rfl
private theorem promote_int_int : promoteMSLArithType .int .int = .int := rfl
private theorem promote_float_float : promoteMSLArithType .float .float = .float := rfl
private theorem cast_ulong_ulong (v : BitVec 64) : evalMSLCast .ulong .ulong v = .ok v := rfl
private theorem cast_float_float (v : BitVec 64) :
    evalMSLCast .float .float v = .ok (v &&& 0xFFFF_FFFF#64) := rfl

/-- Division by zero traps with `MSLOutcome.divisionByZero` rather than returning `0`. -/
theorem msl_div_zero_traps (g : MSLGroupState) (th : MSLThreadState)
    (rx ry : String) (vx : BitVec 64)
    (h_rx : th.locals.lookup? rx = some vx)
    (h_tyx : th.locals.lookupType? rx = some .ulong)
    (h_ry : th.locals.lookup? ry = some 0#64)
    (h_tyy : th.locals.lookupType? ry = some .ulong) :
    evalMSLExpr g th (.div (.var rx) (.var ry)) = .divisionByZero := by
  simp [evalMSLExpr, evalExprWithCall, bindEval, finishBin, inferExprType,
    promote_ulong_ulong, MSLType.isVector, cast_ulong_ulong,
    evalTypedBin, propagateErr, h_rx, h_tyx, h_ry, h_tyy]

/-- Signed 32-bit `INT32_MIN / -1` traps with `MSLOutcome.signedDivOverflow`. -/
theorem msl_signed_div_overflow_traps (g : MSLGroupState) (th : MSLThreadState)
    (rx ry : String)
    (h_rx : th.locals.lookup? rx = some 2147483648#64)
    (h_tyx : th.locals.lookupType? rx = some .int)
    (h_ry : th.locals.lookup? ry = some 4294967295#64)
    (h_tyy : th.locals.lookupType? ry = some .int) :
    evalMSLExpr g th (.div (.var rx) (.var ry)) = .signedDivOverflow := by
  have hCast1 : evalMSLCast .int .int 2147483648#64 = .ok 2147483648#64 := rfl
  have hCast2 : evalMSLCast .int .int 4294967295#64 = .ok 4294967295#64 := rfl
  have hDiv : evalTypedBin .int .div 2147483648#64 4294967295#64 = .signedDivOverflow := rfl
  simp [evalMSLExpr, evalExprWithCall, bindEval, finishBin, inferExprType,
    promote_int_int, MSLType.isVector, hCast1, hCast2, hDiv, propagateErr,
    h_rx, h_tyx, h_ry, h_tyy]

/-- Production C++ ternary `((ry != 0UL) ? (rx / ry) : 0UL)` short-circuits `rx / ry` when
    `ry == 0` and safely returns `0#64` even without evaluating `rx`. -/
theorem msl_guarded_div_zero_safe (g : MSLGroupState) (th : MSLThreadState)
    (rx ry : String)
    (h_ry : th.locals.lookup? ry = some 0#64)
    (h_ty : th.locals.lookupType? ry = some .ulong) :
    evalMSLExpr g th
      (.select (.ne (.var ry) (.immU64 0#64)) (.div (.var rx) (.var ry)) (.immU64 0#64)) =
      .ok 0#64 := by
  have hCmp : evalTypedCmp .ulong .ne 0#64 0#64 = .ok 0#64 := rfl
  simp [evalMSLExpr, evalExprWithCall, bindEval, finishCmp, inferExprType,
    promote_ulong_ulong, cast_ulong_ulong, hCmp, h_ry, h_ty]

/-- Mutant `M9` soundness witness: replacing C++ short-circuit `?:` with Metal's eager
    `select(0UL, rx / ry, ry != 0UL)` evaluates `rx / ry` when `ry == 0` and traps with
    `MSLOutcome.divisionByZero`. -/
theorem msl_builtinSelect_eager_div_zero_traps (g : MSLGroupState) (th : MSLThreadState)
    (rx ry : String) (vx : BitVec 64)
    (h_rx : th.locals.lookup? rx = some vx)
    (h_tyx : th.locals.lookupType? rx = some .ulong)
    (h_ry : th.locals.lookup? ry = some 0#64)
    (h_tyy : th.locals.lookupType? ry = some .ulong) :
    evalMSLExpr g th
      (.builtinSelect (.immU64 0#64) (.div (.var rx) (.var ry)) (.ne (.var ry) (.immU64 0#64))) =
      .divisionByZero := by
  simp [evalMSLExpr, evalExprWithCall, bindEval, finishBin, inferExprType,
    promote_ulong_ulong, MSLType.isVector, cast_ulong_ulong,
    evalTypedBin, propagateErr, h_rx, h_tyx, h_ry, h_tyy]

/-- Short-circuit logical AND (`&&`): `false && rhs` returns `0#64` (`false`) without evaluating
    `rhs` (even when `rhs` is `1UL / 0UL`). -/
theorem msl_logAnd_short_circuits_false (g : MSLGroupState) (th : MSLThreadState)
    (rhs : MSLExpr) :
    evalMSLExpr g th (.logAnd (.immBool false) rhs) = .ok 0#64 := rfl

/-- Short-circuit logical OR (`||`): `true || rhs` returns `1#64` (`true`) without evaluating
    `rhs` (even when `rhs` is `1UL / 0UL`). -/
theorem msl_logOr_short_circuits_true (g : MSLGroupState) (th : MSLThreadState)
    (rhs : MSLExpr) :
    evalMSLExpr g th (.logOr (.immBool true) rhs) = .ok 1#64 := rfl

/-- Floating-point remainder (`%`) is rejected with `MSLOutcome.unsupportedFloatOp` instead of
    silently applying integer modulo to IEEE-754 bit patterns. -/
theorem msl_float_rem_unsupported (g : MSLGroupState) (th : MSLThreadState)
    (rx ry : String) (vx vy : BitVec 64)
    (h_rx : th.locals.lookup? rx = some vx)
    (h_tyx : th.locals.lookupType? rx = some .float)
    (h_ry : th.locals.lookup? ry = some vy)
    (h_tyy : th.locals.lookupType? ry = some .float) :
    evalMSLExpr g th (.rem (.var rx) (.var ry)) = .unsupportedFloatOp "float remainder" := by
  simp [evalMSLExpr, evalExprWithCall, bindEval, finishBin, inferExprType,
    promote_float_float, MSLType.isVector, cast_float_float, evalTypedBin, propagateErr,
    h_rx, h_tyx, h_ry, h_tyy]

/-- Shifting a 32-bit `uint` by an amount `≥ 32` traps with `MSLOutcome.shiftOutOfRange`. -/
theorem msl_uint_shift_ge_width_traps (g : MSLGroupState) (th : MSLThreadState)
    (rx : String) (vx amt : BitVec 64)
    (h_rx : th.locals.lookup? rx = some vx)
    (h_ty : th.locals.lookupType? rx = some .uint)
    (h_ge : 32 ≤ amt.toNat) :
    evalMSLExpr g th (.shl (.var rx) (.immU64 amt)) = .shiftOutOfRange := by
  simp [evalMSLExpr, evalExprWithCall, bindEval, finishShift, inferExprType,
    MSLType.isFloat, MSLType.isVector, MSLType.bitWidth, propagateErr, h_rx, h_ty, h_ge]

/-- Usual arithmetic conversion rank: `uint` + `ulong` promotes to 64-bit `.ulong` rather than
    truncating the 64-bit operand to 32-bit `.uint`. -/
theorem promoteMSLArithType_uint_ulong :
    promoteMSLArithType .uint .ulong = .ulong := rfl

/-- Mixed `uint + ulong` arithmetic preserves full 64-bit precision (`1u + 0x1_0000_0000UL`). -/
theorem msl_uint_add_ulong_promotes :
    let ls := (MSLLocals.empty.setTyped "u" .uint 1#64).setTyped "w" .ulong 0x1_0000_0000#64
    let g : MSLGroupState := { gridDim := {}, groupDim := {}, groupId := {} }
    let th : MSLThreadState := { tid := {}, locals := ls }
    evalMSLExpr g th (.add (.var "u") (.var "w")) = .ok 0x1_0000_0001#64 := rfl

/-- Arithmetic right shift (`>>`) on signed 32-bit `.int` sign-extends the high bit
    (`-8 >> 1 = -4`, represented masked to 32 bits as `0xFFFF_FFFC#64`). -/
theorem msl_signed_int_shr_sign_extends :
    let ls := MSLLocals.empty.setTyped "x" .int 0xFFFF_FFF8#64
    let g : MSLGroupState := { gridDim := {}, groupDim := {}, groupId := {} }
    let th : MSLThreadState := { tid := {}, locals := ls }
    evalMSLExpr g th (.shr (.var "x") (.immU64 1#64)) = .ok 0xFFFF_FFFC#64 := rfl

/-- Multi-lane `ulong2` store/load roundtrip preserves both `.x` and `.y` 64-bit lanes. -/
theorem ulong2_store_load_roundtrip :
    let m0 := ByteMemory.zeros 16
    let flds := [("x", 0x0123_4567_89AB_CDEF#64), ("y", 0xFEDC_BA98_7654_3210#64)]
    (storeTypedElem [] m0 .ulong2 0 0x0123_4567_89AB_CDEF#64 flds).bind
      (fun m1 => loadTypedElem [] m1 .ulong2 0) =
      some (0x0123_4567_89AB_CDEF#64, flds) := rfl

/-- Multi-lane `uint4` store/load roundtrip preserves all four 32-bit lanes (`x, y, z, w`). -/
theorem uint4_store_load_roundtrip :
    let m0 := ByteMemory.zeros 16
    let flds := [("x", 11#64), ("y", 22#64), ("z", 33#64), ("w", 44#64)]
    (storeTypedElem [] m0 .uint4 0 11#64 flds).bind
      (fun m1 => loadTypedElem [] m1 .uint4 0) =
      some (11#64, flds) := rfl

/-- Componentwise `ulong2` XOR (`a ^ b`) computes XOR independently on `.x` and `.y`. -/
theorem ulong2_componentwise_xor :
    let g : MSLGroupState := { gridDim := {}, groupDim := {}, groupId := {} }
    let ls0 := bindValue [] MSLLocals.empty "a" .ulong2 0xAA#64 [("x", 0xAA#64), ("y", 0xFF00#64)]
    let ls1 := bindValue [] ls0 "b" .ulong2 0x0F#64 [("x", 0x0F#64), ("y", 0x0FF0#64)]
    evalExprWithCall kernelCallEval 64 g {} ls1 [] (.bitXor (.var "a") (.var "b")) =
      .ok { value := 0xA5#64, fields := [("x", 0xA5#64), ("y", 0xF0F0#64)],
            locals := ls1, log := [] } := rfl

/-- Disjoint byte ranges never race: recording an access whose byte span lies strictly after a
    prior epoch entry succeeds without triggering `MSLOutcome.dataRace`. -/
theorem recordEpochAccess_disjoint_ok (a : MSLAccess) (tid : Dim3) (tgt : MSLMemTarget)
    (sp : MSLAddressSpace) (addr width : Nat) (isWrite isAtomic : Bool)
    (h_disj : a.addr + a.width ≤ addr) :
    recordEpochAccess [a] tid tgt sp addr width isWrite isAtomic =
      .ok [{ tid, target := tgt, addr, width, isWrite, isAtomic }, a] := by
  have hNo : ¬ (addr < a.addr + a.width ∧ a.addr < addr + width) := by omega
  simp [recordEpochAccess, findDataRace?, findDataRaceGo, rangesOverlap, hNo]

/-- Overlapping unsynchronized cross-thread non-atomic write/access on the same memory target
    traps with `MSLOutcome.dataRace`. -/
theorem recordEpochAccess_overlap_races (a : MSLAccess) (tid : Dim3) (tgt : MSLMemTarget)
    (sp : MSLAddressSpace) (addr width : Nat)
    (h_diff : (tid != a.tid) = true)
    (h_tgt : tgt = a.target)
    (h_ov1 : addr < a.addr + a.width)
    (h_ov2 : a.addr < addr + width) :
    recordEpochAccess [a] tid tgt sp addr width true false =
      .dataRace sp (Nat.max addr a.addr) := by
  subst tgt
  have hTgt : (a.target == a.target) = true := by
    cases a.target with
    | deviceBuf idx => change (idx == idx) = true; simp
    | threadgroupArr nm => change (nm == nm) = true; simp
  have hOv : decide (addr < a.addr + a.width ∧ a.addr < addr + width) = true :=
    decide_eq_true ⟨h_ov1, h_ov2⟩
  simp [recordEpochAccess, findDataRace?, findDataRaceGo, rangesOverlap, h_diff, hTgt, hOv]

/-- Concurrent atomic operations (`isAtomic = true` on both accesses) on the same address by
    distinct threads in the same barrier epoch NEVER trigger `MSLOutcome.dataRace`. -/
theorem recordEpochAccess_atomic_pair_compatible (a : MSLAccess) (tid : Dim3) (tgt : MSLMemTarget)
    (sp : MSLAddressSpace) (addr width : Nat)
    (h_atom : a.isAtomic = true) :
    recordEpochAccess [a] tid tgt sp addr width true true =
      .ok [{ tid, target := tgt, addr, width, isWrite := true, isAtomic := true }, a] := by
  simp [recordEpochAccess, findDataRace?, findDataRaceGo, h_atom]

/-- Mixing an atomic write (`isAtomic = true`) with a non-atomic access (`a.isAtomic = false`) on
    overlapping bytes by distinct threads in the same barrier epoch traps with `.dataRace`. -/
theorem recordEpochAccess_atomic_vs_nonatomic_races (a : MSLAccess) (tid : Dim3)
    (tgt : MSLMemTarget) (sp : MSLAddressSpace) (addr width : Nat)
    (h_diff : (tid != a.tid) = true)
    (h_tgt : tgt = a.target)
    (h_nonatom : a.isAtomic = false)
    (h_ov1 : addr < a.addr + a.width)
    (h_ov2 : a.addr < addr + width) :
    recordEpochAccess [a] tid tgt sp addr width true true =
      .dataRace sp (Nat.max addr a.addr) := by
  subst tgt
  have hTgt : (a.target == a.target) = true := by
    cases a.target with
    | deviceBuf idx => change (idx == idx) = true; simp
    | threadgroupArr nm => change (nm == nm) = true; simp
  have hOv : decide (addr < a.addr + a.width ∧ a.addr < addr + width) = true :=
    decide_eq_true ⟨h_ov1, h_ov2⟩
  simp [recordEpochAccess, findDataRace?, findDataRaceGo, rangesOverlap,
    h_diff, hTgt, h_nonatom, hOv]

/-- Uniform `threadgroupBarrier` synchronization: when a non-empty threadgroup has every thread
    parked at `threadgroup_barrier`, `stepGroupBarrier` converges cleanly, advancing all threads
    past the barrier and clearing `epochLog`. -/
theorem threadgroupBarrier_uniform_converges (g : MSLGroupState)
    (h_nonempty : g.threads.isEmpty = false)
    (h_uniform : g.threads.all threadAtBarrier = true) :
    stepGroupBarrier g =
      .ok { g with threads := g.threads.map advanceBarrierThread, epochLog := [] } := by
  unfold stepGroupBarrier
  simp [h_nonempty, h_uniform]

/-- Divergent `threadgroupBarrier` detection: if the threadgroup is empty or at least one thread
    is not parked at `threadgroup_barrier` when barrier synchronization is attempted,
    `stepGroupBarrier` traps with `MSLOutcome.barrierDivergence`. -/
theorem threadgroupBarrier_divergent_errors (g : MSLGroupState)
    (h_div : (!g.threads.isEmpty && g.threads.all threadAtBarrier) = false) :
    stepGroupBarrier g = .barrierDivergence := by
  unfold stepGroupBarrier
  have hFalse : ¬ ((!g.threads.isEmpty && g.threads.all threadAtBarrier) = true) := by
    rw [h_div]; decide
  exact ite_eq_right_iff.mpr fun h => False.elim (hFalse h)

private theorem stepSimdgroup_preserves_const (g g' : MSLGroupState) (sgId : Nat)
    (h : stepSimdgroup g sgId = .ok g') :
    g'.constantBuffers = g.constantBuffers := by
  unfold stepSimdgroup at h
  dsimp only at h
  cases hLive : g.threads.filter (fun th => !th.halted && simdgroupOf g.groupDim th.tid == sgId) with
  | nil => simp [hLive] at h
  | cons leader rest =>
    simp [hLive] at h
    cases hStmts : leader.stmts with
    | nil => simp [hStmts] at h
    | cons hd tl =>
      cases hd <;> simp [hStmts] at h
      case simdShuffleXor =>
        cases hCS : collectSimdShuffle g sgId g.epochLog g.threads <;>
          simp [hCS, propagateErr] at h
        rw [← h]
      case simdSum declTy dst leaderSrc =>
        cases hCS : collectSimdSum g sgId (inferExprType g leader.locals leaderSrc)
            g.epochLog g.threads <;>
          simp [hCS, propagateErr] at h
        rw [← h]

private theorem stepFirstReady_preserves_const (g : MSLGroupState) :
    ∀ (pre suf : List MSLThreadState) (progressed : Bool) (g' : MSLGroupState),
      stepFirstReadyThread g pre suf = .ok (progressed, g') →
      g'.constantBuffers = g.constantBuffers
  | _, [], _, g', h => by
    simp [stepFirstReadyThread] at h
    rw [← h.2]
  | pre, th :: suf, progressed, g', h => by
    unfold stepFirstReadyThread at h
    split at h
    · exact stepFirstReady_preserves_const g (th :: pre) suf progressed g' h
    · cases hStmts : th.stmts with
      | nil =>
        simp [hStmts] at h
        rw [← h.2]
      | cons s rest =>
        simp [hStmts] at h
        cases hExec : execNonBarrierStmt g th s rest <;>
          simp [hExec, propagateErr] at h
        case ok pair =>
          rw [← h.2]
          exact exec_preserves_constant_buffers g th s rest pair.1 pair.2 hExec

private theorem stepGroup_preserves_const (g g' : MSLGroupState) (done : Bool)
    (hStep : stepGroup g = .ok (done, g')) :
    g'.constantBuffers = g.constantBuffers := by
  unfold stepGroup at hStep
  split at hStep
  · simp at hStep
    exact congrArg MSLGroupState.constantBuffers hStep.2.symm
  · cases hReady : stepFirstReadyThread g [] g.threads <;>
      simp [hReady, propagateErr] at hStep
    case ok rpair =>
      rcases rpair with ⟨progressed, gMid⟩
      have hC1 := stepFirstReady_preserves_const g [] g.threads progressed gMid hReady
      cases progressed with
      | true =>
        simp at hStep
        exact (congrArg MSLGroupState.constantBuffers hStep.2.symm).trans hC1
      | false =>
        simp at hStep
        cases hFind : gMid.threads.find? (fun th => !th.halted && threadAtSimdOp th) with
        | some th =>
          simp [hFind] at hStep
          cases hSimd : stepSimdgroup gMid (simdgroupOf gMid.groupDim th.tid) <;>
            simp [hSimd] at hStep
          case ok synced =>
            have hEq1 := congrArg MSLGroupState.constantBuffers hStep.2.symm
            have hEq2 := stepSimdgroup_preserves_const gMid synced _ hSimd
            exact (hEq1.trans hEq2).trans hC1
        | none =>
          simp [hFind] at hStep
          cases hBar : stepGroupBarrier gMid <;> simp [hBar] at hStep
          case ok synced =>
            have hEq1 := congrArg MSLGroupState.constantBuffers hStep.2.symm
            unfold stepGroupBarrier at hBar
            split at hBar <;> simp at hBar
            have hEq2 : synced.constantBuffers = gMid.constantBuffers := by rw [← hBar]
            exact (hEq1.trans hEq2).trans hC1

/-- Multi-step `constant` buffer immutability: running an entire threadgroup for any `fuel`
    budget preserves `constantBuffers` unchanged. -/
theorem runGroup_preserves_constant_buffers (fuel : Nat) (g g' : MSLGroupState)
    (h : runGroup fuel g = .ok g') :
    g'.constantBuffers = g.constantBuffers := by
  induction fuel generalizing g with
  | zero =>
    unfold runGroup at h
    split at h <;> simp at h
    exact congrArg MSLGroupState.constantBuffers h.symm
  | succ f ih =>
    unfold runGroup at h
    cases hStep : stepGroup g <;> simp [hStep, propagateErr] at h
    case ok pair =>
      rcases pair with ⟨done, gNext⟩
      have hStepConst := stepGroup_preserves_const g gNext done hStep
      cases done with
      | true =>
        simp at h
        exact (congrArg MSLGroupState.constantBuffers h.symm).trans hStepConst
      | false =>
        simp at h
        exact (ih gNext h).trans hStepConst

/-- Halted threadgroup fixed-point: once all threads in `g` have halted, `runGroup` returns
    `.ok g` for every step budget `fuel`. -/
theorem runGroup_halted (fuel : Nat) (g : MSLGroupState)
    (h_halted : g.threads.all (·.halted) = true) :
    runGroup fuel g = .ok g := by
  cases fuel with
  | zero =>
    unfold runGroup
    simp [h_halted]
  | succ f =>
    unfold runGroup stepGroup
    simp [h_halted]

/-- Monotone fuel stability of `runGroup`: once `runGroup f1 g` reaches a terminal
    (non-`fuelExhausted`) outcome `out`, any larger step budget `f2 ≥ f1` reaches the exact same
    terminal outcome `out`. -/
theorem runGroup_mono_fuel (f1 f2 : Nat) (g : MSLGroupState)
    (out : MSLOutcome MSLGroupState)
    (h1 : runGroup f1 g = out)
    (h_term : out ≠ .fuelExhausted)
    (h_le : f1 ≤ f2) :
    runGroup f2 g = out := by
  induction f1 generalizing f2 g with
  | zero =>
    unfold runGroup at h1
    cases hAll : g.threads.all (·.halted)
    · simp [hAll] at h1
      exact False.elim (h_term h1.symm)
    · simp [hAll] at h1
      rw [runGroup_halted f2 g hAll]
      exact h1
  | succ f1' ih =>
    cases f2 with
    | zero => omega
    | succ f2' =>
      have hLe' : f1' ≤ f2' := Nat.le_of_succ_le_succ h_le
      unfold runGroup at h1 ⊢
      cases hStep : stepGroup g <;> simp [hStep, propagateErr] at h1 ⊢
      case ok pair =>
        rcases pair with ⟨done, g'⟩
        cases done with
        | true =>
          simp at h1 ⊢
          exact h1
        | false =>
          simp at h1 ⊢
          exact ih f2' g' h1 hLe'
      all_goals exact h1

/-- Fuel-independent operational determinism of the Metal SIMT threadgroup semantics (`runGroup`):
    any two executions from the same initial `MSLGroupState` under arbitrary step budgets `f1`
    and `f2` that both reach terminal (non-`fuelExhausted`) outcomes produce identical results. -/
theorem runGroup_deterministic (f1 f2 : Nat) (g : MSLGroupState)
    (out1 out2 : MSLOutcome MSLGroupState)
    (h1 : runGroup f1 g = out1)
    (h2 : runGroup f2 g = out2)
    (hne1 : out1 ≠ .fuelExhausted)
    (hne2 : out2 ≠ .fuelExhausted) :
    out1 = out2 := by
  by_cases hLe : f1 ≤ f2
  · have hMono := runGroup_mono_fuel f1 f2 g out1 h1 hne1 hLe
    exact hMono.symm.trans h2
  · have hLe2 : f2 ≤ f1 := by omega
    have hMono := runGroup_mono_fuel f2 f1 g out2 h2 hne2 hLe2
    exact h1.symm.trans hMono

/-- Pass 2 of `simd_sum` distributes the pre-evaluated reduction without adding or dropping
    threads (and without invoking expression evaluation). -/
theorem distributeSimdSum_length (g : MSLGroupState) (sgId : Nat)
    (samples : List (Dim3 × SimdSumSample)) (total : BitVec 64)
    (ths : List MSLThreadState) :
    (distributeSimdSum g sgId samples total ths).length = ths.length := by
  induction ths with
  | nil => rfl
  | cons th rest ih =>
    simp only [distributeSimdSum]
    split
    · cases samples.lookup th.tid <;> simp [ih]
    · simp [ih]

/-- Pass 2 of `simd_shuffle_xor` distributes the pre-evaluated partner values without adding or
    dropping threads (and without invoking expression evaluation). -/
theorem distributeSimdShuffle_length (g : MSLGroupState) (sgId : Nat)
    (samples : List (Dim3 × SimdShuffleSample))
    (laneVals : List (Nat × (BitVec 64 × List (String × BitVec 64))))
    (ths : List MSLThreadState) :
    (distributeSimdShuffle g sgId samples laneVals ths).length = ths.length := by
  induction ths with
  | nil => rfl
  | cons th rest ih =>
    simp only [distributeSimdShuffle]
    split
    · cases samples.lookup th.tid <;> simp [ih]
    · simp [ih]

/-- 1:1 injectivity of `ppMSLAddressSpace`: distinct MSL address spaces render to distinct tokens. -/
theorem ppMSLAddressSpace_injective (s1 s2 : MSLAddressSpace)
    (h : ppMSLAddressSpace s1 = ppMSLAddressSpace s2) :
    s1 = s2 := by
  cases s1 <;> cases s2 <;> first | rfl | exact absurd h (by decide)

/-- Read-only `device const` pointers render with the explicit `device const <T>*` qualifier. -/
theorem ppMSLType_device_const_pointer (elem : MSLType) :
    ppMSLType (.pointer .device true elem) = "device const " ++ ppMSLType elem ++ "*" := rfl

/-- Vector constructor `.structLit .ulong2 (cons a (cons b nil))` renders with Metal call syntax
    `ulong2(...)` rather than C struct brace syntax `{ ... }`. -/
theorem ppMSLExpr_ulong2_constructor (a b : MSLExpr) :
    ppMSLExpr (.structLit .ulong2 (.cons a (.cons b .nil))) =
      "ulong2(" ++ ppMSLExpr a ++ ", " ++ ppMSLExpr b ++ ")" := rfl

private theorem charList_isPrefixOf_append :
    ∀ (xs ys : List Char), List.isPrefixOf xs (xs ++ ys) = true
  | [], _ => rfl
  | x :: xs, ys => by
    simp [charList_isPrefixOf_append xs ys]

/-- Structural header well-formedness of `ppMSLModule`: every rendered Metal module begins with
    `#include <metal_stdlib>\nusing namespace metal;`. -/
theorem ppMSLModule_header_prefix (m : MSLModule) :
    List.isPrefixOf ppMSLModuleHeader.toList (ppMSLModule m).toList = true := by
  unfold ppMSLModule
  cases (m.structs.map ppMSLStructDecl ++ m.funcs.map ppMSLFuncDecl ++ m.kernels.map ppMSLKernel) with
  | nil =>
    rw [String.toList_append]
    exact charList_isPrefixOf_append _ _
  | cons b bs =>
    simp only [String.append_assoc, String.toList_append]
    exact charList_isPrefixOf_append _ _

/-- Structural signature well-formedness of `ppMSLKernel`: every rendered compute kernel begins
    with `kernel void <name>(\n`. -/
theorem ppMSLKernel_signature_prefix (k : MSLKernelDecl) :
    List.isPrefixOf (ppMSLKernelSignaturePrefix k.name).toList (ppMSLKernel k).toList = true := by
  unfold ppMSLKernel
  simp only [String.append_assoc, String.toList_append]
  exact charList_isPrefixOf_append _ _

private theorem getLast_append_singleton (xs : List Char) (c : Char) :
    (xs ++ [c]).getLast? = some c := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    cases rest with
    | nil => rfl
    | cons y ys => exact ih

private theorem semicolon_toList_eq : ";".toList = [';'] := by decide

/-- Structural well-formedness of `ppMSLStmt` on `threadgroupBarrier`: renders a semicolon-terminated
    `threadgroup_barrier(mem_flags::mem_threadgroup);` statement for any indentation prefix. -/
theorem ppMSLStmt_barrier_semicolon (indent : String) :
    (ppMSLStmt indent .threadgroupBarrier).toList.getLast? = some ';' := by
  unfold ppMSLStmt
  simp only [String.append_assoc, String.toList_append, semicolon_toList_eq]
  rw [← List.append_assoc]
  exact getLast_append_singleton _ ';'

theorem writeLEAux_size (bs : Array UInt8) (addr : Nat) (val : BitVec 64) (w : Nat) :
    (ByteMemory.writeLEAux bs addr val w).size = bs.size := by
  induction w generalizing bs with
  | zero => rfl
  | succ k ih =>
    simp only [ByteMemory.writeLEAux]
    rw [ih, Array.size_setIfInBounds]

theorem writeLEAux_getElem?_outside (bs : Array UInt8) (addr : Nat) (val : BitVec 64) (w j : Nat)
    (hout : j < addr ∨ addr + w ≤ j) :
    (ByteMemory.writeLEAux bs addr val w)[j]? = bs[j]? := by
  induction w generalizing bs with
  | zero => rfl
  | succ k ih =>
    simp only [ByteMemory.writeLEAux]
    rw [ih _ (by omega)]
    by_cases hj : j < bs.size
    · have hj' : j < (bs.setIfInBounds (addr + k)
          (UInt8.ofNat ((val >>> (k * 8)).toNat % 256))).size := by
        rw [Array.size_setIfInBounds]; exact hj
      rw [Array.getElem?_eq_getElem hj', Array.getElem?_eq_getElem hj,
        Array.getElem_setIfInBounds (hj := hj)]
      split
      · omega
      · rfl
    · have hj' : ¬ j < (bs.setIfInBounds (addr + k)
          (UInt8.ofNat ((val >>> (k * 8)).toNat % 256))).size := by
        rw [Array.size_setIfInBounds]; exact hj
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt hj'),
        Array.getElem?_eq_none (Nat.le_of_not_lt hj)]

theorem writeLEAux_getElem?_inside (bs : Array UInt8) (addr : Nat) (val : BitVec 64) (w i : Nat)
    (hi : i < w) (hbound : addr + w ≤ bs.size) :
    (ByteMemory.writeLEAux bs addr val w)[addr + i]? =
      some (UInt8.ofNat ((val >>> (i * 8)).toNat % 256)) := by
  induction w generalizing bs with
  | zero => omega
  | succ k ih =>
    simp only [ByteMemory.writeLEAux]
    by_cases hik : i = k
    · subst hik
      rw [writeLEAux_getElem?_outside _ addr val i (addr + i) (Or.inr (Nat.le_refl _))]
      have hin : addr + i < bs.size := by omega
      have hin' : addr + i < (bs.setIfInBounds (addr + i)
          (UInt8.ofNat ((val >>> (i * 8)).toNat % 256))).size := by
        rw [Array.size_setIfInBounds]; exact hin
      rw [Array.getElem?_eq_getElem hin', Array.getElem_setIfInBounds (hj := hin)]
      split
      · rfl
      · omega
    · exact ih _ (by omega) (by rw [Array.size_setIfInBounds]; omega)

theorem readLEAux_eq_of_getElem?_eq (bs1 bs2 : Array UInt8) (addr w : Nat)
    (heq : ∀ i, i < w → bs1[addr + i]? = bs2[addr + i]?) :
    ByteMemory.readLEAux { bytes := bs1 } addr w =
      ByteMemory.readLEAux { bytes := bs2 } addr w := by
  induction w with
  | zero => rfl
  | succ k ih =>
    have ihk := ih (fun i hi => heq i (by omega))
    have hbk : ({ bytes := bs1 } : ByteMemory).bytes[addr + k]? =
        ({ bytes := bs2 } : ByteMemory).bytes[addr + k]? :=
      heq k (Nat.lt_succ_self k)
    simp only [ByteMemory.readLEAux, hbk, ihk]

theorem readLEAux_succ_of_eq (m : ByteMemory) (addr k : Nat) (b : UInt8) (rest : BitVec 64)
    (hb : m.bytes[addr + k]? = some b)
    (hr : ByteMemory.readLEAux m addr k = some rest) :
    ByteMemory.readLEAux m addr (k + 1) =
      some (rest ||| (BitVec.ofNat 64 b.toNat <<< (k * 8))) := by
  simp only [ByteMemory.readLEAux, hb, hr]

theorem readLEAux_of_bytes_8 (m : ByteMemory) (addr : Nat) (val : BitVec 64)
    (hget : ∀ i, i < 8 → m.bytes[addr + i]? =
      some (UInt8.ofNat ((val >>> (i * 8)).toNat % 256))) :
    ByteMemory.readLEAux m addr 8 = some val := by
  have h0 : ByteMemory.readLEAux m addr 0 = some 0#64 := rfl
  have h1 := readLEAux_succ_of_eq m addr 0 _ _ (hget 0 (by decide)) h0
  have h2 := readLEAux_succ_of_eq m addr 1 _ _ (hget 1 (by decide)) h1
  have h3 := readLEAux_succ_of_eq m addr 2 _ _ (hget 2 (by decide)) h2
  have h4 := readLEAux_succ_of_eq m addr 3 _ _ (hget 3 (by decide)) h3
  have h5 := readLEAux_succ_of_eq m addr 4 _ _ (hget 4 (by decide)) h4
  have h6 := readLEAux_succ_of_eq m addr 5 _ _ (hget 5 (by decide)) h5
  have h7 := readLEAux_succ_of_eq m addr 6 _ _ (hget 6 (by decide)) h6
  have h8 := readLEAux_succ_of_eq m addr 7 _ _ (hget 7 (by decide)) h7
  rw [h8]
  congr 1
  have hb : ∀ (k : Nat),
      BitVec.ofNat 64 (UInt8.ofNat ((val >>> (k * 8)).toNat % 256)).toNat =
      (val >>> (k * 8)) &&& 0xFF#64 := by
    intro k
    apply BitVec.eq_of_toNat_eq
    have h256 : 0 < 256 := by decide
    have hn : (UInt8.ofNat ((val >>> (k * 8)).toNat % 256)).toNat =
        (val >>> (k * 8)).toNat % 256 := by
      simp [Nat.mod_eq_of_lt (Nat.mod_lt _ h256)]
    have hand : ((val >>> (k * 8)) &&& 0xFF#64).toNat = (val >>> (k * 8)).toNat % 256 := by
      rw [BitVec.toNat_and]
      exact Nat.and_two_pow_sub_one_eq_mod (val >>> (k * 8)).toNat 8
    rw [BitVec.toNat_ofNat, hn, hand]
    have hlt64 : (val >>> (k * 8)).toNat % 256 < 2 ^ 64 :=
      Nat.lt_trans (Nat.mod_lt _ h256) (by decide)
    exact Nat.mod_eq_of_lt hlt64
  rw [hb 0, hb 1, hb 2, hb 3, hb 4, hb 5, hb 6, hb 7]
  bv_decide

theorem readLEAux_writeLEAux_8 (bs : Array UInt8) (addr : Nat) (val : BitVec 64)
    (w : Nat) (hw : w = 8) (hbound : addr + w ≤ bs.size) :
    ByteMemory.readLEAux { bytes := ByteMemory.writeLEAux bs addr val w } addr w = some val := by
  have hget : ∀ i, i < 8 →
      ({ bytes := ByteMemory.writeLEAux bs addr val w } : ByteMemory).bytes[addr + i]? =
        some (UInt8.ofNat ((val >>> (i * 8)).toNat % 256)) := by
    intro i hi
    change (ByteMemory.writeLEAux bs addr val w)[addr + i]? = _
    exact writeLEAux_getElem?_inside bs addr val w i (by omega) hbound
  have h8 := readLEAux_of_bytes_8 { bytes := ByteMemory.writeLEAux bs addr val w } addr val hget
  simpa [hw] using h8

theorem fillU64Words_size (bs : Array UInt8) (idx : Nat) (words : List (BitVec 64)) :
    (ByteMemory.fillU64Words bs idx words).size = bs.size := by
  induction words generalizing bs idx with
  | nil => rfl
  | cons w rest ih =>
    simp only [ByteMemory.fillU64Words]
    rw [ih, writeLEAux_size]

theorem fillU64Words_getElem?_before (bs : Array UInt8) (idx : Nat) (words : List (BitVec 64))
    (j : Nat) (hbefore : j < idx * 8) :
    (ByteMemory.fillU64Words bs idx words)[j]? = bs[j]? := by
  induction words generalizing bs idx with
  | nil => rfl
  | cons w rest ih =>
    simp only [ByteMemory.fillU64Words]
    rw [ih _ (idx + 1) (by omega)]
    exact writeLEAux_getElem?_outside bs (idx * 8) w 8 j (Or.inl hbefore)

theorem fillU64Words_readLEAux (bs : Array UInt8) (idx : Nat) (words : List (BitVec 64))
    (k : Nat) (hk : k < words.length)
    (hbound : (idx + words.length) * 8 ≤ bs.size) :
    ByteMemory.readLEAux { bytes := ByteMemory.fillU64Words bs idx words }
      ((idx + k) * 8) 8 = some words[k] := by
  induction words generalizing bs idx k with
  | nil => simp at hk
  | cons w rest ih =>
    cases k with
    | zero =>
      simp only [ByteMemory.fillU64Words, Nat.add_zero, List.getElem_cons_zero]
      have hw : idx * 8 + 8 ≤ bs.size := by simp at hbound; omega
      let bs0 := ByteMemory.writeLEAux bs (idx * 8) w 8
      let bs1 := ByteMemory.fillU64Words bs0 (idx + 1) rest
      have heq : ByteMemory.readLEAux { bytes := bs1 } (idx * 8) 8 =
          ByteMemory.readLEAux { bytes := bs0 } (idx * 8) 8 :=
        readLEAux_eq_of_getElem?_eq bs1 bs0 (idx * 8) 8
          (fun i hi => fillU64Words_getElem?_before bs0 (idx + 1) rest (idx * 8 + i) (by omega))
      exact heq.trans (readLEAux_writeLEAux_8 bs (idx * 8) w 8 rfl hw)
    | succ k' =>
      simp only [ByteMemory.fillU64Words, List.getElem_cons_succ]
      have hrew : (idx + (k' + 1)) * 8 = ((idx + 1) + k') * 8 := by omega
      rw [hrew]
      exact ih (ByteMemory.writeLEAux bs (idx * 8) w 8) (idx + 1) k'
        (by simp at hk; omega)
        (by rw [writeLEAux_size]; simp at hbound ⊢; omega)

theorem ofU64Words_size (words : List (BitVec 64)) :
    (ByteMemory.ofU64Words words).bytes.size = words.length * 8 := by
  simp [ByteMemory.ofU64Words, fillU64Words_size]

theorem ofU64Words_readU64Word (words : List (BitVec 64)) (k : Nat) (hk : k < words.length) :
    (ByteMemory.ofU64Words words).readU64Word? k = some words[k] := by
  unfold ByteMemory.readU64Word? ByteMemory.loadBits ByteMemory.ofU64Words
  have hsz : (ByteMemory.fillU64Words (Array.replicate (words.length * 8) (0 : UInt8)) 0 words).size =
      words.length * 8 := by
    rw [fillU64Words_size, Array.size_replicate]
  dsimp only
  rw [hsz]
  have hle : k * 8 + 8 ≤ words.length * 8 := by omega
  simp only [gt_iff_lt, Nat.zero_lt_succ, decide_true, Bool.true_and, decide_eq_true hle, ite_true]
  simpa using fillU64Words_readLEAux (Array.replicate (words.length * 8) (0 : UInt8)) 0 words k hk (by simp)

theorem storeBits_8_eq (m : ByteMemory) (idx : Nat) (val : BitVec 64)
    (hbound : idx * 8 + 8 ≤ m.bytes.size) :
    m.storeBits (idx * 8) 8 val = some { bytes := ByteMemory.writeLEAux m.bytes (idx * 8) val 8 } := by
  unfold ByteMemory.storeBits
  simp only [gt_iff_lt, Nat.zero_lt_succ, decide_true, Bool.true_and, decide_eq_true hbound, ite_true]

theorem storeBits_8_size (m m' : ByteMemory) (idx : Nat) (val : BitVec 64)
    (h : m.storeBits (idx * 8) 8 val = some m') :
    m'.bytes.size = m.bytes.size := by
  unfold ByteMemory.storeBits at h
  simp only [gt_iff_lt, Nat.zero_lt_succ, decide_true, Bool.true_and] at h
  cases hcond : decide (idx * 8 + 8 ≤ m.bytes.size) <;> rw [hcond] at h
  · cases h
  · simp only [ite_true, Option.some.injEq] at h
    rw [← h, writeLEAux_size]

theorem storeBits_8_read_same (m m' : ByteMemory) (idx : Nat) (val : BitVec 64)
    (h : m.storeBits (idx * 8) 8 val = some m') :
    m'.readU64Word? idx = some val := by
  unfold ByteMemory.storeBits at h
  simp only [gt_iff_lt, Nat.zero_lt_succ, decide_true, Bool.true_and] at h
  cases hcond : decide (idx * 8 + 8 ≤ m.bytes.size) <;> rw [hcond] at h
  · cases h
  · simp only [ite_true, Option.some.injEq] at h
    have hbound : idx * 8 + 8 ≤ m.bytes.size := of_decide_eq_true hcond
    rw [← h]
    unfold ByteMemory.readU64Word? ByteMemory.loadBits
    dsimp only
    rw [writeLEAux_size]
    simp only [gt_iff_lt, Nat.zero_lt_succ, decide_true, Bool.true_and, hcond, ite_true]
    exact readLEAux_writeLEAux_8 m.bytes (idx * 8) val 8 rfl hbound

theorem storeBits_8_read_ne (m m' : ByteMemory) (idx j : Nat)
    (val : BitVec 64) (hne : j ≠ idx)
    (h : m.storeBits (idx * 8) 8 val = some m') :
    m'.readU64Word? j = m.readU64Word? j := by
  unfold ByteMemory.storeBits at h
  simp only [gt_iff_lt, Nat.zero_lt_succ, decide_true, Bool.true_and] at h
  cases hcond : decide (idx * 8 + 8 ≤ m.bytes.size) <;> rw [hcond] at h
  · cases h
  · simp only [ite_true, Option.some.injEq] at h
    rw [← h]
    unfold ByteMemory.readU64Word? ByteMemory.loadBits
    dsimp only
    rw [writeLEAux_size]
    simp only [gt_iff_lt, Nat.zero_lt_succ, decide_true, Bool.true_and]
    cases hjc : decide (j * 8 + 8 ≤ m.bytes.size)
    · simp only [Bool.false_eq_true, ite_false]
    · simp only [ite_true]
      cases m with
      | mk bs =>
        exact readLEAux_eq_of_getElem?_eq (ByteMemory.writeLEAux bs (idx * 8) val 8) bs (j * 8) 8
          (fun i hi => writeLEAux_getElem?_outside bs (idx * 8) val 8 (j * 8 + i) (by omega))

theorem promoteMSLArithType_ulong : promoteMSLArithType .ulong .ulong = .ulong := rfl

theorem finishBin_ulong_op (g : MSLGroupState) (a b : MSLExpr) (op : MSLBin)
    (ls : MSLLocals) (log : List MSLAccess) (va vb : BitVec 64)
    (fa fb : List (String × BitVec 64))
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    finishBin g a b op
      { value := va, fields := fa, locals := ls, log := log }
      { value := vb, fields := fb, locals := ls, log := log } =
      match evalTypedBin .ulong op va vb with
      | .ok v => .ok { value := v, locals := ls, log := log }
      | err => propagateErr err := by
  simp only [finishBin, hta, htb, promoteMSLArithType_ulong]
  rfl

theorem finishBitwise_ulong_op (g : MSLGroupState) (a b : MSLExpr)
    (op : BitVec 64 → BitVec 64 → BitVec 64)
    (ls : MSLLocals) (log : List MSLAccess) (va vb : BitVec 64)
    (fa fb : List (String × BitVec 64))
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    finishBitwise g a b op
      { value := va, fields := fa, locals := ls, log := log }
      { value := vb, fields := fb, locals := ls, log := log } =
      .ok { value := op va vb, locals := ls, log := log } := by
  simp [finishBitwise, hta, htb, promoteMSLArithType_ulong,
    MSLType.isFloat, MSLType.isVector, evalMSLCast, MSLType.isSigned, maskForType]

theorem finishCmp_ulong_op (g : MSLGroupState) (a b : MSLExpr) (op : MSLCmp)
    (ls : MSLLocals) (log : List MSLAccess) (va vb : BitVec 64)
    (fa fb : List (String × BitVec 64))
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    finishCmp g a b op
      { value := va, fields := fa, locals := ls, log := log }
      { value := vb, fields := fb, locals := ls, log := log } =
      match evalTypedCmp .ulong op va vb with
      | .ok v => .ok { value := v, locals := ls, log := log }
      | err => propagateErr err := by
  simp only [finishCmp, hta, htb, promoteMSLArithType_ulong]
  rfl

theorem finishShift_ulong_op (g : MSLGroupState) (a : MSLExpr) (right : Bool)
    (ls : MSLLocals) (log : List MSLAccess) (va vb : BitVec 64)
    (fa fb : List (String × BitVec 64))
    (hta : inferExprType g ls a = .ulong) (hlt : vb.toNat < 64) :
    finishShift g a right
      { value := va, fields := fa, locals := ls, log := log }
      { value := vb, fields := fb, locals := ls, log := log } =
      .ok { value := if right then va >>> vb.toNat else va <<< vb.toNat, locals := ls, log := log } := by
  have hge : ¬ (64 ≤ vb.toNat) := by omega
  cases right <;>
    simp [finishShift, hta, MSLType.isFloat, MSLType.isVector, MSLType.isSigned,
      MSLType.bitWidth, maskForType, hge]

theorem finishShift_long_sar_op (g : MSLGroupState) (a : MSLExpr)
    (ls : MSLLocals) (log : List MSLAccess) (va vb : BitVec 64)
    (fa fb : List (String × BitVec 64))
    (hta : inferExprType g ls a = .long) (hlt : vb.toNat < 64) :
    finishShift g a true
      { value := va, fields := fa, locals := ls, log := log }
      { value := vb, fields := fb, locals := ls, log := log } =
      .ok { value := va.sshiftRight vb.toNat, locals := ls, log := log } := by
  have hge : ¬ (64 ≤ vb.toNat) := by omega
  simp [finishShift, hta, MSLType.isFloat, MSLType.isVector, MSLType.isSigned,
    MSLType.bitWidth, maskForType, hge]

theorem lookup_setAssoc_same (xs : List (String × BitVec 64)) (k : String) (v : BitVec 64) :
    (MSLLocals.setAssoc xs k v).lookup k = some v := by
  induction xs with
  | nil => simp [MSLLocals.setAssoc]
  | cons hd tl ih =>
    cases hd with
    | mk k' v' =>
      simp only [MSLLocals.setAssoc]
      cases hk : k' == k
      · have hk' : (k == k') = false := by rw [BEq.comm]; exact hk
        simp only [Bool.false_eq_true, ite_false, List.lookup, hk']
        exact ih
      · simp only [ite_true, List.lookup, beq_self_eq_true]

theorem lookup_setAssoc_ne (xs : List (String × BitVec 64)) (k k' : String) (v : BitVec 64)
    (hne : k' ≠ k) :
    (MSLLocals.setAssoc xs k v).lookup k' = xs.lookup k' := by
  have hbeq : (k' == k) = false := beq_false_of_ne hne
  induction xs with
  | nil => simp only [MSLLocals.setAssoc, List.lookup, hbeq]
  | cons hd tl ih =>
    cases hd with
    | mk hk hv =>
      simp only [MSLLocals.setAssoc]
      cases h1 : hk == k
      · simp only [Bool.false_eq_true, ite_false, List.lookup]
        cases h2 : k' == hk
        · exact ih
        · rfl
      · have hk_eq : hk = k := beq_iff_eq.mp h1
        subst hk_eq
        simp only [ite_true, List.lookup, hbeq]

theorem lookup_setTypeAssoc_same (xs : List (String × MSLType)) (k : String) (t : MSLType) :
    (MSLLocals.setTypeAssoc xs k t).lookup k = some t := by
  induction xs with
  | nil => simp [MSLLocals.setTypeAssoc]
  | cons hd tl ih =>
    cases hd with
    | mk k' t' =>
      simp only [MSLLocals.setTypeAssoc]
      cases hk : k' == k
      · have hk' : (k == k') = false := by rw [BEq.comm]; exact hk
        simp only [Bool.false_eq_true, ite_false, List.lookup, hk']
        exact ih
      · simp only [ite_true, List.lookup, beq_self_eq_true]

theorem setTyped_lookup_same (ls : MSLLocals) (name : String) (ty : MSLType) (v : BitVec 64) :
    (ls.setTyped name ty v).lookup? name = some v ∧
    (ls.setTyped name ty v).lookupType? name = some ty := by
  simp only [MSLLocals.setTyped, MSLLocals.lookup?, MSLLocals.lookupType?]
  exact ⟨lookup_setAssoc_same ls.vars name v, lookup_setTypeAssoc_same ls.types name ty⟩

theorem lookup_setTypeAssoc_ne (xs : List (String × MSLType)) (k k' : String) (t : MSLType)
    (hne : k' ≠ k) :
    (MSLLocals.setTypeAssoc xs k t).lookup k' = xs.lookup k' := by
  have hbeq : (k' == k) = false := beq_false_of_ne hne
  induction xs with
  | nil => simp only [MSLLocals.setTypeAssoc, List.lookup, hbeq]
  | cons hd tl ih =>
    cases hd with
    | mk hk ht =>
      simp only [MSLLocals.setTypeAssoc]
      cases h1 : hk == k
      · simp only [Bool.false_eq_true, ite_false, List.lookup]
        cases h2 : k' == hk
        · exact ih
        · rfl
      · have hk_eq : hk = k := beq_iff_eq.mp h1
        subst hk_eq
        simp only [ite_true, List.lookup, hbeq]

theorem setTyped_lookup_ne (ls : MSLLocals) (name name' : String) (ty : MSLType) (v : BitVec 64)
    (hne : name' ≠ name) :
    (ls.setTyped name ty v).lookup? name' = ls.lookup? name' ∧
    (ls.setTyped name ty v).lookupType? name' = ls.lookupType? name' := by
  simp only [MSLLocals.setTyped, MSLLocals.lookup?, MSLLocals.lookupType?]
  exact ⟨lookup_setAssoc_ne ls.vars name name' v hne, lookup_setTypeAssoc_ne ls.types name name' ty hne⟩

theorem evalTypedBin_ulong (op : MSLBin) (va vb : BitVec 64) :
    evalTypedBin .ulong op va vb =
      match op with
      | .div => if vb == 0#64 then .divisionByZero else .ok (va / vb)
      | .rem => if vb == 0#64 then .divisionByZero else .ok (va % vb)
      | .add => .ok (va + vb)
      | .sub => .ok (va - vb)
      | .mul => .ok (va * vb) := by
  simp only [evalTypedBin, maskForType]
  cases op <;> rfl

theorem evalTypedCmp_ulong (op : MSLCmp) (va vb : BitVec 64) :
    evalTypedCmp .ulong op va vb =
      .ok (match op with
        | .eq => if va == vb then 1#64 else 0#64
        | .ne => if va != vb then 1#64 else 0#64
        | .lt => if BitVec.ult va vb then 1#64 else 0#64
        | .le => if BitVec.ule va vb then 1#64 else 0#64
        | .gt => if BitVec.ult vb va then 1#64 else 0#64
        | .ge => if BitVec.ule vb va then 1#64 else 0#64) := by
  simp only [evalTypedCmp, maskForType]
  cases op <;> rfl


private def unDigit (c : Char) : Nat := c.toNat - '0'.toNat
private def parseDigits : List Char → Nat → Nat
  | [], acc => acc
  | c :: cs, acc => parseDigits cs (acc * 10 + unDigit c)

private theorem unDigit_digitChar (d : Nat) (h : d < 10) :
    unDigit (Nat.digitChar d) = d := by
  match d, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => rfl

private theorem parseDigits_toDigitsCore :
    ∀ (fuel n : Nat) (cs : List Char), n < fuel →
      parseDigits (Nat.toDigitsCore 10 fuel n cs) 0 = parseDigits cs n
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, n, cs, hfuel => by
    unfold Nat.toDigitsCore
    dsimp only
    have hmod : n % 10 < 10 := Nat.mod_lt n (by decide)
    have hchar : unDigit (Nat.digitChar (n % 10)) = n % 10 := unDigit_digitChar (n % 10) hmod
    split
    · rename_i hdiv0
      have hn : n = n % 10 := by omega
      simp [parseDigits, hchar]
      rw [← hn]
    · rename_i hdiv0
      have hlt : n / 10 < fuel := by omega
      rw [parseDigits_toDigitsCore fuel (n / 10) (Nat.digitChar (n % 10) :: cs) hlt]
      have hdiv : n / 10 * 10 + n % 10 = n := by omega
      simp [parseDigits, hchar, hdiv]

theorem toString_nat_inj (a b : Nat) (h : toString a = toString b) : a = b := by
  have h1 : (Nat.repr a).toList = (Nat.repr b).toList := congrArg String.toList h
  simp only [Nat.repr, String.toList_ofList, Nat.toDigits] at h1
  have ha := parseDigits_toDigitsCore (a + 1) a [] (Nat.lt_succ_self a)
  have hb := parseDigits_toDigitsCore (b + 1) b [] (Nat.lt_succ_self b)
  rw [h1] at ha
  simpa [parseDigits] using ha.symm.trans hb

theorem prefix_nat_inj (pre : String) (a b : Nat)
    (h : pre ++ toString a = pre ++ toString b) : a = b := by
  have h1 : (pre ++ toString a).toList = (pre ++ toString b).toList := congrArg String.toList h
  simp only [String.toList_append] at h1
  exact toString_nat_inj a b (String.ext_iff.mpr (List.append_cancel_left h1))

private theorem devBuf_beq_false {a b : Nat} (hne : a ≠ b) :
    (MSLMemTarget.deviceBuf a == MSLMemTarget.deviceBuf b) = false := by
  change (a == b) = false
  exact beq_false_of_ne hne

def SimtLogInv (nIn lo hi : Nat) (a : MSLAccess) : Prop :=
  (∃ k < nIn, a.target = .deviceBuf k ∧ a.isWrite = false) ∨
  (a.target = .deviceBuf nIn ∧ a.width = 8 ∧ ∃ idx, lo ≤ idx ∧ idx < hi ∧ a.addr = idx * 8)

theorem simtLogInv_mono {nIn lo hi lo' hi' : Nat} {a : MSLAccess}
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') (h : SimtLogInv nIn lo hi a) :
    SimtLogInv nIn lo' hi' a := by
  rcases h with h1 | ⟨ht, hw, idx, h1, h2, ha⟩
  · exact Or.inl h1
  · exact Or.inr ⟨ht, hw, idx, by omega, by omega, ha⟩

theorem findDataRaceGo_read_none (tid : Dim3) (k nIn lo hi addr : Nat) (hk : k < nIn) :
    ∀ (log : List MSLAccess), (∀ a ∈ log, SimtLogInv nIn lo hi a) →
      findDataRaceGo tid (.deviceBuf k) addr 8 false false log = none
  | [], _ => rfl
  | a :: rest, hlog => by
    have ha := hlog a (.head rest)
    have hrest := findDataRaceGo_read_none tid k nIn lo hi addr hk rest (fun x hx => hlog x (.tail a hx))
    unfold findDataRaceGo
    rcases ha with ⟨k', _, htk, hwf⟩ | ⟨htn, _, _, _, _, _⟩
    · simp [hwf, hrest]
    · have hne : (MSLMemTarget.deviceBuf k == a.target) = false := by
        rw [htn]; exact devBuf_beq_false (by omega)
      simp [hne, hrest]

theorem recordEpochAccess_read_ok (log : List MSLAccess) (tid : Dim3)
    (k nIn lo hi addr : Nat) (hk : k < nIn)
    (hlog : ∀ a ∈ log, SimtLogInv nIn lo hi a) :
    recordEpochAccess log tid (.deviceBuf k) .device addr 8 false false =
      .ok ({ tid, target := .deviceBuf k, addr, width := 8, isWrite := false, isAtomic := false } :: log) ∧
    ∀ a ∈ ({ tid, target := .deviceBuf k, addr, width := 8, isWrite := false, isAtomic := false } : MSLAccess) :: log,
      SimtLogInv nIn lo hi a := by
  unfold recordEpochAccess findDataRace?
  rw [findDataRaceGo_read_none tid k nIn lo hi addr hk log hlog]
  refine ⟨rfl, ?_⟩
  intro a ha
  rcases List.mem_cons.mp ha with rfl | hmem
  · exact Or.inl ⟨k, hk, rfl, rfl⟩
  · exact hlog a hmem

theorem findDataRaceGo_write_none (tid : Dim3) (nIn lo hi : Nat) :
    ∀ (log : List MSLAccess), (∀ a ∈ log, SimtLogInv nIn lo hi a) →
      findDataRaceGo tid (.deviceBuf nIn) (hi * 8) 8 true false log = none
  | [], _ => rfl
  | a :: rest, hlog => by
    have ha := hlog a (.head rest)
    have hrest := findDataRaceGo_write_none tid nIn lo hi rest (fun x hx => hlog x (.tail a hx))
    unfold findDataRaceGo
    rcases ha with ⟨k, hk, htk, _⟩ | ⟨htn, hw, idx, _, hlt, haddr⟩
    · have hne : (MSLMemTarget.deviceBuf nIn == a.target) = false := by
        rw [htk]; exact devBuf_beq_false (by omega)
      simp [hne, hrest]
    · have hov : rangesOverlap (hi * 8) 8 a.addr a.width = false := by
        rw [haddr, hw]; unfold rangesOverlap; simp; omega
      simp [hov, hrest]

theorem recordEpochAccess_write_ok (log : List MSLAccess) (tid : Dim3)
    (nIn lo hi : Nat) (hle : lo ≤ hi)
    (hlog : ∀ a ∈ log, SimtLogInv nIn lo hi a) :
    recordEpochAccess log tid (.deviceBuf nIn) .device (hi * 8) 8 true false =
      .ok ({ tid, target := .deviceBuf nIn, addr := hi * 8, width := 8, isWrite := true, isAtomic := false } :: log) ∧
    ∀ a ∈ ({ tid, target := .deviceBuf nIn, addr := hi * 8, width := 8, isWrite := true, isAtomic := false } : MSLAccess) :: log,
      SimtLogInv nIn lo (hi + 1) a := by
  unfold recordEpochAccess findDataRace?
  rw [findDataRaceGo_write_none tid nIn lo hi log hlog]
  refine ⟨rfl, ?_⟩
  intro a ha
  rcases List.mem_cons.mp ha with rfl | hmem
  · exact Or.inr ⟨rfl, rfl, hi, hle, Nat.lt_succ_self hi, rfl⟩
  · exact simtLogInv_mono (Nat.le_refl lo) (Nat.le_succ hi) (hlog a hmem)

theorem findCrossGroupRace_none (nIn mid hi : Nat) (b : MSLAccess)
    (hb : SimtLogInv nIn mid hi b) :
    ∀ (prior : List MSLAccess), (∀ a ∈ prior, SimtLogInv nIn 0 mid a) →
      findCrossGroupRace? b.target b.addr b.width b.isWrite b.isAtomic prior = none
  | [], _ => rfl
  | a :: rest, hprior => by
    have ha := hprior a (.head rest)
    have hrest := findCrossGroupRace_none nIn mid hi b hb rest (fun x hx => hprior x (.tail a hx))
    unfold findCrossGroupRace?
    rcases hb with ⟨kb, hkb, htb, hwfb⟩ | ⟨htb, hwb, idxb, hmidb, _, haddrb⟩
    · rcases ha with ⟨_, _, _, hwfa⟩ | ⟨hta, _, _, _, _, _⟩
      · simp [hwfb, hwfa]
        rw [← hwfb]
        exact hrest
      · have hne : (b.target == a.target) = false := by
          rw [htb, hta]; exact devBuf_beq_false (by omega)
        simp [hne, hrest]
    · rcases ha with ⟨ka, hka, hta, _⟩ | ⟨hta, hwa, idxa, _, hlta, haddra⟩
      · have hne : (b.target == a.target) = false := by
          rw [htb, hta]; exact devBuf_beq_false (by omega)
        simp [hne, hrest]
      · have hov : rangesOverlap b.addr b.width a.addr a.width = false := by
          rw [haddrb, hwb, haddra, hwa]; unfold rangesOverlap; simp; omega
        simp [hov, hrest]

theorem checkCrossGroupDeviceLog_ok (nIn mid hi : Nat) (hmid : mid ≤ hi)
    (prior : List MSLAccess) (hprior : ∀ a ∈ prior, SimtLogInv nIn 0 mid a) :
    ∀ (grp : List MSLAccess), (∀ b ∈ grp, SimtLogInv nIn mid hi b) →
      checkCrossGroupDeviceLog prior grp = .ok () ∧
      ∀ x ∈ grp ++ prior, SimtLogInv nIn 0 hi x
  | [], _ =>
    ⟨rfl, fun x hx => by
      simp only [List.nil_append] at hx
      exact simtLogInv_mono (Nat.le_refl 0) hmid (hprior x hx)⟩
  | b :: rest, hgrp => by
    have hb := hgrp b (.head rest)
    have ⟨hok, hall⟩ := checkCrossGroupDeviceLog_ok nIn mid hi hmid prior hprior rest
      (fun x hx => hgrp x (.tail b hx))
    unfold checkCrossGroupDeviceLog
    have hnone := findCrossGroupRace_none nIn mid hi b hb prior hprior
    have hcond : (if !isDeviceAccess b then checkCrossGroupDeviceLog prior rest
        else match findCrossGroupRace? b.target b.addr b.width b.isWrite b.isAtomic prior with
          | some conflictAddr => .dataRace .device conflictAddr
          | none => checkCrossGroupDeviceLog prior rest) = .ok () := by
      rw [hnone]
      split <;> exact hok
    refine ⟨hcond, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact simtLogInv_mono (Nat.zero_le mid) (Nat.le_refl hi) hb
    · exact hall x hmem

theorem stepFirstReadyThread_exec (g : MSLGroupState) (th th' : MSLThreadState)
    (g' : MSLGroupState) (stmt : MSLStmt) (rest : List MSLStmt)
    (hhalted : th.halted = false) (hbar : threadAtBarrier th = false)
    (hsimd : threadAtSimdOp th = false) (hstmts : th.stmts = stmt :: rest)
    (hexec : execNonBarrierStmt g th stmt rest = .ok (th', g')) :
    ∀ (done pre todo : List MSLThreadState),
      (∀ d ∈ done, d.halted = true) →
      stepFirstReadyThread g pre (done ++ (th :: todo)) =
        .ok (true, { g' with threads := pre.reverse ++ done ++ (th' :: todo) })
  | [], pre, todo, _ => by
    simp only [List.nil_append, List.append_nil, stepFirstReadyThread,
      hhalted, hbar, hsimd, Bool.or_false, Bool.false_eq_true, ite_false, hstmts, hexec]
  | d :: ds, pre, todo, hdone => by
    have hd : d.halted = true := hdone d (.head ds)
    have ih := stepFirstReadyThread_exec g th th' g' stmt rest hhalted hbar hsimd hstmts hexec
      ds (d :: pre) todo (fun x hx => hdone x (.tail d hx))
    simp only [List.cons_append, stepFirstReadyThread, hd, Bool.true_or, ite_true]
    rw [ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem list_all_halted_false {done todo : List MSLThreadState} {th : MSLThreadState}
    (h : th.halted = false) :
    (done ++ (th :: todo)).all (·.halted) = false := by
  induction done with
  | nil => simp [h]
  | cons d ds ih => simp [ih]

theorem runGroupWithDeviceLog_step_stmt (f : Nat) (g g' : MSLGroupState)
    (done todo : List MSLThreadState) (th th' : MSLThreadState)
    (stmt : MSLStmt) (rest : List MSLStmt)
    (hthreads : g.threads = done ++ (th :: todo))
    (hdone : ∀ d ∈ done, d.halted = true)
    (hhalted : th.halted = false) (hbar : threadAtBarrier th = false)
    (hsimd : threadAtSimdOp th = false) (hstmts : th.stmts = stmt :: rest)
    (hexec : execNonBarrierStmt g th stmt rest = .ok (th', g'))
    (hlog : g'.epochLog.isEmpty = true → g.epochLog.isEmpty = true) :
    runGroupWithDeviceLog (f + 1) g [] =
      runGroupWithDeviceLog f { g' with threads := done ++ (th' :: todo) } [] := by
  have hall : g.threads.all (·.halted) = false := by
    rw [hthreads]; exact list_all_halted_false hhalted
  have hfirst : stepFirstReadyThread g [] g.threads =
      .ok (true, { g' with threads := done ++ (th' :: todo) }) := by
    rw [hthreads]
    simpa using stepFirstReadyThread_exec g th th' g' stmt rest hhalted hbar hsimd hstmts hexec done [] todo hdone
  have hstep : stepGroup g = .ok (false, { g' with threads := done ++ (th' :: todo) }) := by
    unfold stepGroup
    rw [hall]
    simp only [Bool.false_eq_true, ite_false, hfirst]
  have hsaved : ((!g.epochLog.isEmpty && g'.epochLog.isEmpty) = false) := by
    cases hge : g'.epochLog.isEmpty
    · simp
    · simp [hlog hge]
  rw [runGroupWithDeviceLog]
  rw [hstep]
  simp only [hsaved, Bool.false_eq_true, ite_false]

theorem runGroupWithDeviceLog_all_halted (fuel : Nat) (g : MSLGroupState)
    (hall : g.threads.all (·.halted) = true) :
    runGroupWithDeviceLog fuel g [] = .ok (g, g.epochLog.filter isDeviceAccess) := by
  cases fuel with
  | zero =>
    unfold runGroupWithDeviceLog
    simp [hall]
  | succ f =>
    unfold runGroupWithDeviceLog stepGroup
    simp [hall]


theorem ev_var_bound (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (name : String) (bv : BitVec 64)
    (hl : ls.lookup? name = some bv) (ht : ls.lookupType? name = some .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.var name) =
      .ok { value := bv, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall]
  simp only [hl, ht]
  rfl

theorem ev_cast_ulong_from_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a : MSLExpr) (bv : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := bv, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.cast .ulong a) =
      .ok { value := bv, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hta]
  rfl

theorem ev_cast_ulong_from_bool (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a : MSLExpr) (bv : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := bv, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .bool) :
    evalExprWithCall callEval fuel g tid ls log (.cast .ulong a) =
      .ok { value := if bv != 0#64 then 1#64 else 0#64, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hta]
  rfl

theorem ev_bitnot_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a : MSLExpr) (bv : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := bv, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.bitNot a) =
      .ok { value := ~~~bv, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hta]
  rfl

theorem ev_add_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.add a b) =
      .ok { value := va + vb, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  rw [finishBin_ulong_op g a b .add ls log va vb [] [] hta htb]
  rfl

theorem ev_sub_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.sub a b) =
      .ok { value := va - vb, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  rw [finishBin_ulong_op g a b .sub ls log va vb [] [] hta htb]
  rfl

theorem ev_mul_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.mul a b) =
      .ok { value := va * vb, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  rw [finishBin_ulong_op g a b .mul ls log va vb [] [] hta htb]
  rfl

theorem ev_div_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong)
    (hnz : (vb == 0#64) = false) :
    evalExprWithCall callEval fuel g tid ls log (.div a b) =
      .ok { value := va / vb, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  rw [finishBin_ulong_op g a b .div ls log va vb [] [] hta htb, evalTypedBin_ulong]
  simp only [hnz, Bool.false_eq_true, ite_false]

theorem ev_rem_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong)
    (hnz : (vb == 0#64) = false) :
    evalExprWithCall callEval fuel g tid ls log (.rem a b) =
      .ok { value := va % vb, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  rw [finishBin_ulong_op g a b .rem ls log va vb [] [] hta htb, evalTypedBin_ulong]
  simp only [hnz, Bool.false_eq_true, ite_false]

theorem ev_bitand_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.bitAnd a b) =
      .ok { value := va &&& vb, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  exact finishBitwise_ulong_op g a b (· &&& ·) ls log va vb [] [] hta htb

theorem ev_bitor_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.bitOr a b) =
      .ok { value := va ||| vb, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  exact finishBitwise_ulong_op g a b (· ||| ·) ls log va vb [] [] hta htb

theorem ev_bitxor_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.bitXor a b) =
      .ok { value := va ^^^ vb, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  exact finishBitwise_ulong_op g a b (· ^^^ ·) ls log va vb [] [] hta htb

theorem ev_shl_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (hlt : vb.toNat < 64) :
    evalExprWithCall callEval fuel g tid ls log (.shl a b) =
      .ok { value := va <<< vb.toNat, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  simpa using finishShift_ulong_op g a false ls log va vb [] [] hta hlt

theorem ev_shr_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (hlt : vb.toNat < 64) :
    evalExprWithCall callEval fuel g tid ls log (.shr a b) =
      .ok { value := va >>> vb.toNat, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  simpa using finishShift_ulong_op g a true ls log va vb [] [] hta hlt

theorem ev_sar_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong)
    (hlt : vb.toNat < 64) :
    evalExprWithCall callEval fuel g tid ls log (.cast .ulong (.shr (.cast .long a) b)) =
      .ok { value := va.sshiftRight vb.toNat, fields := [], locals := ls, log := log } := by
  have hcast : evalExprWithCall callEval fuel g tid ls log (.cast .long a) =
      .ok { value := va, fields := [], locals := ls, log := log } := by
    rw [evalExprWithCall, ha]
    simp only [bindEval, hta]
    rfl
  have hshr : evalExprWithCall callEval fuel g tid ls log (.shr (.cast .long a) b) =
      .ok { value := va.sshiftRight vb.toNat, fields := [], locals := ls, log := log } := by
    rw [evalExprWithCall, hcast]
    simp only [bindEval, hb]
    exact finishShift_long_sar_op g (.cast .long a) ls log va vb [] [] rfl hlt
  rw [evalExprWithCall, hshr]
  simp only [bindEval, inferExprType, htb]
  rfl

theorem ev_eq_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.eq a b) =
      .ok { value := if va == vb then 1#64 else 0#64, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  rw [finishCmp_ulong_op g a b .eq ls log va vb [] [] hta htb, evalTypedCmp_ulong]

theorem ev_ne_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.ne a b) =
      .ok { value := if va != vb then 1#64 else 0#64, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  rw [finishCmp_ulong_op g a b .ne ls log va vb [] [] hta htb, evalTypedCmp_ulong]

theorem ev_lt_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.lt a b) =
      .ok { value := if BitVec.ult va vb then 1#64 else 0#64, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  rw [finishCmp_ulong_op g a b .lt ls log va vb [] [] hta htb, evalTypedCmp_ulong]

theorem ev_le_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.le a b) =
      .ok { value := if BitVec.ule va vb then 1#64 else 0#64, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  rw [finishCmp_ulong_op g a b .le ls log va vb [] [] hta htb, evalTypedCmp_ulong]

theorem ev_ge_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.ge a b) =
      .ok { value := if BitVec.ule vb va then 1#64 else 0#64, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb]
  rw [finishCmp_ulong_op g a b .ge ls log va vb [] [] hta htb, evalTypedCmp_ulong]

theorem ev_select_true (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (c t f : MSLExpr) (bv : BitVec 64)
    (hc : evalExprWithCall callEval fuel g tid ls log c =
      .ok { value := bv, fields := [], locals := ls, log := log })
    (hnz : bv != 0#64) :
    evalExprWithCall callEval fuel g tid ls log (.select c t f) =
      evalExprWithCall callEval fuel g tid ls log t := by
  rw [evalExprWithCall, hc]
  simp only [bindEval, hnz, ite_true]

theorem ev_select_false (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (c t f : MSLExpr) (bv : BitVec 64)
    (hc : evalExprWithCall callEval fuel g tid ls log c =
      .ok { value := bv, fields := [], locals := ls, log := log })
    (hz : (bv != 0#64) = false) :
    evalExprWithCall callEval fuel g tid ls log (.select c t f) =
      evalExprWithCall callEval fuel g tid ls log f := by
  rw [evalExprWithCall, hc]
  simp only [bindEval, hz, Bool.false_eq_true, ite_false]


theorem loadTypedElem_ulong (structs : List MSLStructDecl) (mem : ByteMemory) (elemIdx : Nat) :
    loadTypedElem structs mem .ulong (elemIdx * 8) =
      (mem.readU64Word? elemIdx).map (fun v => (v, [])) := by
  unfold loadTypedElem ByteMemory.readU64Word?
  have hfn : structFieldNames structs .ulong = [] := rfl
  have hbw : MSLType.ulong.byteWidth = 8 := rfl
  simp only [hfn, hbw, maskForType]
  cases mem.loadBits (elemIdx * 8) 8 <;> rfl

theorem storeTypedElem_ulong (structs : List MSLStructDecl) (mem : ByteMemory) (byteAddr : Nat)
    (val : BitVec 64) (fields : List (String × BitVec 64)) :
    storeTypedElem structs mem .ulong byteAddr val fields =
      mem.storeBits byteAddr 8 val := by
  unfold storeTypedElem
  have hfn : structFieldNames structs .ulong = [] := rfl
  simp only [hfn]
  rfl

theorem lookup_setIndexedMem_same (bufs : List (Nat × ByteMemory)) (idx : Nat) (mem : ByteMemory) :
    (setIndexedMem bufs idx mem).lookup idx = some mem := by
  induction bufs with
  | nil => simp [setIndexedMem]
  | cons hd tl ih =>
    rcases hd with ⟨idx', mem'⟩
    unfold setIndexedMem
    by_cases h : idx' = idx
    · subst h; simp
    · have hbf : (idx' == idx) = false := beq_false_of_ne h
      have hbf2 : (idx == idx') = false := beq_false_of_ne (Ne.symm h)
      simp [hbf, List.lookup, hbf2, ih]

theorem lookup_setIndexedMem_ne (bufs : List (Nat × ByteMemory)) (idx idx' : Nat)
    (mem : ByteMemory) (hne : idx' ≠ idx) :
    (setIndexedMem bufs idx mem).lookup idx' = bufs.lookup idx' := by
  induction bufs with
  | nil =>
    have hbf : (idx' == idx) = false := beq_false_of_ne hne
    simp [setIndexedMem, List.lookup, hbf]
  | cons hd tl ih =>
    rcases hd with ⟨k, m⟩
    unfold setIndexedMem
    by_cases hk : k = idx
    · subst hk
      have hbf : (idx' == k) = false := beq_false_of_ne hne
      simp [List.lookup, hbf]
    · have hbf : (k == idx) = false := beq_false_of_ne hk
      simp only [hbf, Bool.false_eq_true, ite_false, List.lookup]
      cases idx' == k
      · exact ih
      · rfl

theorem ev_clz_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a : MSLExpr) (bv : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := bv, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.clz a) =
      .ok { value := BitVec.ofNat 64 bv.clz.toNat, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  dsimp only [bindEval]
  rw [hta]
  have htr : bv.setWidth 64 = bv := BitVec.setWidth_eq bv
  dsimp only [MSLType.isFloat, MSLType.bitWidth, maskForType, BitVec.truncate]
  rw [htr]
  rfl

theorem ev_var_gid_uint (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (cx : Nat) (hcx : cx < 2 ^ 32)
    (hl : ls.lookup? "gid" = some (BitVec.ofNat 64 cx))
    (ht : ls.lookupType? "gid" = some .uint) :
    evalExprWithCall callEval fuel g tid ls log (.var "gid") =
      .ok { value := BitVec.ofNat 64 cx, fields := [], locals := ls, log := log } ∧
    evalExprWithCall callEval fuel g tid ls log (.cast .ulong (.var "gid")) =
      .ok { value := BitVec.ofNat 64 cx, fields := [], locals := ls, log := log } := by
  have hvar : evalExprWithCall callEval fuel g tid ls log (.var "gid") =
      .ok { value := BitVec.ofNat 64 cx, fields := [], locals := ls, log := log } := by
    rw [evalExprWithCall]
    simp only [hl, ht]
    rfl
  refine ⟨hvar, ?_⟩
  rw [evalExprWithCall, hvar]
  simp only [bindEval, inferExprType, ht]
  have hcast : evalMSLCast .ulong .uint (BitVec.ofNat 64 cx) = .ok (BitVec.ofNat 64 cx) := by
    have hmask : BitVec.ofNat 64 cx &&& 0xFFFF_FFFF#64 = BitVec.ofNat 64 cx := by
      apply BitVec.eq_of_toNat_eq
      change (cx % 2 ^ 64) &&& 4294967295 = cx % 2 ^ 64
      have hmod64 : cx % 2 ^ 64 = cx := Nat.mod_eq_of_lt (by omega)
      rw [hmod64]
      have h4 : (4294967295 : Nat) = 2 ^ 32 - 1 := by decide
      rw [h4, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_eq_of_lt hcx
    show MSLOutcome.ok (BitVec.ofNat 64 cx &&& 0xFFFF_FFFF#64) = MSLOutcome.ok (BitVec.ofNat 64 cx)
    rw [hmask]
  rw [hcast]

theorem ev_var_const_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (name : String) (bufIdx : Nat) (bv : BitVec 64)
    (hln : ls.lookup? name = none) (hlt : ls.lookupType? name = none)
    (hb : g.bindings.lookup name = some (.constantScalar bufIdx .ulong))
    (hc : g.constantBuffers.lookup bufIdx = some (ByteMemory.ofU64Words [bv])) :
    evalExprWithCall callEval fuel g tid ls log (.var name) =
      .ok { value := bv, fields := [], locals := ls, log := log } ∧
    inferExprType g ls (.var name) = .ulong := by
  have hload : loadTypedElem g.structs (ByteMemory.ofU64Words [bv]) .ulong 0 = some (bv, []) := by
    have h0 : (0 : Nat) = 0 * 8 := rfl
    rw [h0, loadTypedElem_ulong]
    have hw := ofU64Words_readU64Word [bv] 0 (by simp)
    simp only [hw, List.getElem_cons_zero, Option.map]
  refine ⟨?_, ?_⟩
  · rw [evalExprWithCall]
    simp only [hln, hb, hc, hload]
  · simp only [inferExprType, hlt, hb]

theorem ev_index_dev_read (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (target : String) (idxExpr : MSLExpr)
    (k nIn lo hi elemIdx : Nat) (words : List (BitVec 64))
    (hidx : evalExprWithCall callEval fuel g tid ls log idxExpr =
      .ok { value := BitVec.ofNat 64 elemIdx, fields := [], locals := ls, log := log })
    (helemLt : elemIdx < words.length)
    (hwLen : words.length < 2 ^ 64)
    (harr : ls.lookupArray? target = none)
    (hbind : g.bindings.lookup target = some (.deviceBuf k true .ulong))
    (hdev : g.deviceBuffers.lookup k = some (ByteMemory.ofU64Words words))
    (hk : k < nIn)
    (hlog : ∀ a ∈ log, SimtLogInv nIn lo hi a) :
    ∃ log',
      evalExprWithCall callEval fuel g tid ls log (.index target idxExpr) =
        .ok { value := words[elemIdx], fields := [], locals := ls, log := log' } ∧
      (∀ a ∈ log', SimtLogInv nIn lo hi a) ∧
      log'.isEmpty = false := by
  have htoNat : (BitVec.ofNat 64 elemIdx).toNat = elemIdx := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans helemLt hwLen)]
  have ⟨hrec, hlog'⟩ := recordEpochAccess_read_ok log tid k nIn lo hi (elemIdx * 8) hk hlog
  have hload : loadTypedElem g.structs (ByteMemory.ofU64Words words) .ulong (elemIdx * 8) =
      some (words[elemIdx], []) := by
    rw [loadTypedElem_ulong, ofU64Words_readU64Word words elemIdx helemLt]
    rfl
  refine ⟨{ tid, target := .deviceBuf k, addr := elemIdx * 8, width := 8, isWrite := false, isAtomic := false } :: log, ?_, hlog', rfl⟩
  rw [evalExprWithCall, hidx]
  simp only [bindEval, harr, htoNat, readBoundElement, hbind, hdev, aggregateByteWidth]
  have hbw : MSLType.ulong.byteWidth = 8 := rfl
  simp only [hbw, hrec, hload]

theorem exec_indexAssign_dev_write (g : MSLGroupState) (th : MSLThreadState)
    (rest : List MSLStmt) (idxExpr rhs : MSLExpr)
    (nIn lo elemIdx len : Nat) (val : BitVec 64)
    (log1 : List MSLAccess) (outMem : ByteMemory)
    (hidx : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog idxExpr =
      .ok { value := BitVec.ofNat 64 elemIdx, fields := [], locals := th.locals, log := g.epochLog })
    (hrhs : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog rhs =
      .ok { value := val, fields := [], locals := th.locals, log := log1 })
    (helemLt : elemIdx < len) (hlen64 : len * 8 ≤ 2 ^ 64)
    (harr : th.locals.lookupArray? "out" = none)
    (hbind : g.bindings.lookup "out" = some (.deviceBuf nIn false .ulong))
    (hdev : g.deviceBuffers.lookup nIn = some outMem)
    (hsize : outMem.bytes.size = len * 8)
    (hle : lo ≤ elemIdx)
    (hlog1 : ∀ a ∈ log1, SimtLogInv nIn lo elemIdx a) :
    ∃ outMem' log2,
      execNonBarrierStmt g th (.indexAssign "out" idxExpr rhs) rest =
        .ok ({ th with stmts := rest },
             { g with epochLog := log2, deviceBuffers := setIndexedMem g.deviceBuffers nIn outMem' }) ∧
      outMem'.bytes.size = len * 8 ∧
      outMem'.readU64Word? elemIdx = some val ∧
      (∀ j, j ≠ elemIdx → outMem'.readU64Word? j = outMem.readU64Word? j) ∧
      (∀ a ∈ log2, SimtLogInv nIn lo (elemIdx + 1) a) ∧
      log2.isEmpty = false := by
  have htoNat : (BitVec.ofNat 64 elemIdx).toNat = elemIdx := by
    have hlt : elemIdx < 2 ^ 64 := by omega
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have ⟨hrec, hlog2⟩ := recordEpochAccess_write_ok log1 th.tid nIn lo elemIdx hle hlog1
  have hstore : outMem.storeBits (elemIdx * 8) 8 val =
      some { bytes := ByteMemory.writeLEAux outMem.bytes (elemIdx * 8) val 8 } := by
    exact storeBits_8_eq outMem elemIdx val (by rw [hsize]; omega)
  let outMem' : ByteMemory := { bytes := ByteMemory.writeLEAux outMem.bytes (elemIdx * 8) val 8 }
  let entry : MSLAccess := { tid := th.tid, target := .deviceBuf nIn, addr := elemIdx * 8, width := 8, isWrite := true, isAtomic := false }
  refine ⟨outMem', entry :: log1, ?_, ?_, ?_, ?_, hlog2, rfl⟩
  · unfold execNonBarrierStmt
    dsimp only [execStmtWithCall]
    rw [hidx]
    have hag : aggregateByteWidth g.structs .ulong = 8 := rfl
    simp only [hrhs, htoNat, harr, execIndexWrite, hbind, hag, hrec,
      writeDeviceBuffer, hdev, storeTypedElem_ulong, hstore]
    rfl
  · rw [writeLEAux_size, hsize]
  · exact storeBits_8_read_same outMem outMem' elemIdx val hstore
  · intro j hj
    exact storeBits_8_read_ne outMem outMem' elemIdx j val hj hstore


theorem ev_logOr_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log }) :
    evalExprWithCall callEval fuel g tid ls log (.logOr a b) =
      .ok { value := if (va != 0#64) || (vb != 0#64) then 1#64 else 0#64,
            fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  dsimp only [bindEval]
  cases hva : (va != 0#64)
  · simp only [Bool.false_eq_true, ite_false, Bool.false_or, hb]
    cases hvb : (vb == 0#64)
    · have hne : (vb != 0#64) = true := by simpa [bne_iff_ne, beq_iff_eq] using hvb
      simp [hne]
    · have hne : (vb != 0#64) = false := by
        cases h : (vb != 0#64)
        · rfl
        · rw [bne_iff_ne] at h; rw [beq_iff_eq] at hvb; exact absurd hvb h
      simp [hne]
  · simp

theorem exec_varDecl_ulong (g : MSLGroupState) (th : MSLThreadState)
    (rest : List MSLStmt) (name : String) (rhs : MSLExpr)
    (val : BitVec 64) (log1 : List MSLAccess)
    (hrhsNotConst : ∀ src, rhs = .var src → ∀ idx ty, g.bindings.lookup src ≠ some (.constantScalar idx ty))
    (hrhs : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog rhs =
      .ok { value := val, fields := [], locals := th.locals, log := log1 }) :
    execNonBarrierStmt g th (.varDecl .ulong name rhs) rest =
      .ok ({ th with locals := th.locals.setTyped name .ulong val, stmts := rest },
           { g with epochLog := log1 }) := by
  unfold execNonBarrierStmt
  dsimp only [execStmtWithCall]
  have hbc : ∀ idx ty, (match g.bindings.lookup name with
      | none => match rhs with | .var src => g.bindings.lookup src | _ => none
      | some _ => none) ≠ some (.constantScalar idx ty) := by
    intro idx ty
    cases g.bindings.lookup name with
    | none =>
      cases rhs with
      | var src => exact hrhsNotConst src rfl idx ty
      | _ => intro h; cases h
    | some _ => intro h; cases h
  split
  · rename_i idx ty hcs
    exact absurd hcs (hbc idx ty)
  · simp only [hrhs, bindValue, maskForType, List.foldl]

theorem exec_ifElse_step (g : MSLGroupState) (th : MSLThreadState)
    (rest : List MSLStmt) (cond : MSLExpr) (thenBr elseBr : MSLBlock)
    (cval : BitVec 64) (log1 : List MSLAccess)
    (hc : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog cond =
      .ok { value := cval, fields := [], locals := th.locals, log := log1 }) :
    execNonBarrierStmt g th (.ifElse cond thenBr elseBr) rest =
      .ok ({ th with stmts := (if cval != 0#64 then thenBr.toList else elseBr.toList) ++ rest },
           { g with epochLog := log1 }) := by
  unfold execNonBarrierStmt
  dsimp only [execStmtWithCall]
  rw [hc]

theorem exec_returnStmt_step (g : MSLGroupState) (th : MSLThreadState) (rest : List MSLStmt) :
    execNonBarrierStmt g th .returnStmt rest =
      .ok ({ th with stmts := [], halted := true }, g) := rfl


def stdKernelParams (nIn : Nat) : List MSLParamDecl :=
  (List.range nIn).map (fun i =>
    { ty := .pointer .device true .ulong, name := s!"in{i}", attr := some (.buffer i) }) ++
  [ { ty := .pointer .device false .ulong, name := "out", attr := some (.buffer nIn) }
  , { ty := .ref .constant .ulong, name := "n", attr := some (.buffer (nIn + 1)) }
  , { ty := .uint, name := "gid", attr := some .threadPositionInGrid } ]

def stdBindings (nIn : Nat) : List (String × MSLBufferBinding) :=
  (List.range nIn).map (fun i => (s!"in{i}", MSLBufferBinding.deviceBuf i true .ulong)) ++
    [("out", .deviceBuf nIn false .ulong), ("n", .constantScalar (nIn + 1) .ulong)]

theorem in_ne_lit (i : Nat) :
    s!"in{i}" ≠ "out" ∧ s!"in{i}" ≠ "n" ∧ s!"in{i}" ≠ "gid" ∧ s!"in{i}" ≠ "gid64" := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> {
    intro h
    have hc := congrArg (fun s => s.toList.head?) h
    simp [toString] at hc
  }

theorem in_ne_var (i id : Nat) : s!"in{i}" ≠ s!"v{id}" := by
  intro h
  have hc := congrArg (fun s => s.toList.head?) h
  simp [toString] at hc

theorem var_ne_special (id : Nat) :
    s!"v{id}" ≠ "out" ∧ s!"v{id}" ≠ "n" ∧ s!"v{id}" ≠ "gid" ∧ s!"v{id}" ≠ "gid64" := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> {
    intro h
    have hc := congrArg (fun s => s.toList.head?) h
    simp [toString] at hc
  }

theorem buildKernelBindings_std (k : MSLKernelDecl) (nIn : Nat)
    (hparams : k.params = stdKernelParams nIn) (hshared : k.sharedDecls = []) :
    buildKernelBindings k = stdBindings nIn := by
  let bindFn := fun (p : MSLParamDecl) =>
    match p.attr, p.ty with
    | some (.buffer idx), .pointer .device isConst elemTy =>
      some (p.name, MSLBufferBinding.deviceBuf idx isConst elemTy)
    | some (.buffer idx), .pointer .constant _ elemTy =>
      some (p.name, MSLBufferBinding.constantBuf idx elemTy)
    | some (.buffer idx), .ref .constant elemTy =>
      some (p.name, MSLBufferBinding.constantScalar idx elemTy)
    | some (.buffer _), .pointer .threadgroup _ elemTy =>
      some (p.name, MSLBufferBinding.threadgroupArr p.name elemTy)
    | _, _ => none
  change k.params.filterMap bindFn ++ k.sharedDecls.map (fun s => (s.name, .threadgroupArr s.name s.elemTy)) = stdBindings nIn
  rw [hparams, hshared, List.map_nil, List.append_nil]
  unfold stdKernelParams stdBindings
  rw [List.filterMap_append]
  have h1 : ∀ xs : List Nat,
      (xs.map (fun i =>
        ({ ty := .pointer .device true .ulong, name := s!"in{i}", attr := some (.buffer i) } : MSLParamDecl))).filterMap bindFn =
      xs.map (fun i => (s!"in{i}", MSLBufferBinding.deviceBuf i true .ulong)) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons, List.filterMap_cons, bindFn]
      rw [ih]
  rw [h1 (List.range nIn)]
  rfl

private theorem lookup_mapIn_lt :
    ∀ (nIn j : Nat), j < nIn →
      ((List.range nIn).map (fun i => (s!"in{i}", MSLBufferBinding.deviceBuf i true .ulong))).lookup s!"in{j}" =
        some (.deviceBuf j true .ulong)
  | 0, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, j, hj => by
    rw [List.range_succ, List.map_append, List.lookup_append]
    by_cases hjn : j = n
    · subst hjn
      have hnone : ((List.range j).map (fun i => (s!"in{i}", MSLBufferBinding.deviceBuf i true .ulong))).lookup s!"in{j}" = none := by
        rw [List.lookup_eq_none_iff]
        intro ⟨k, v⟩ hmem
        rw [List.mem_map] at hmem
        rcases hmem with ⟨i, hi, heq⟩
        cases heq
        rw [List.mem_range] at hi
        simp only [bne_iff_ne, ne_eq]
        intro heqS
        have hij := prefix_nat_inj "in" j i (by simpa [toString] using heqS)
        omega
      rw [hnone]
      simp
    · rw [lookup_mapIn_lt n j (by omega)]
      rfl

private theorem lookup_mapIn_other (nIn : Nat) (s : String)
    (hne : ∀ i < nIn, s ≠ s!"in{i}") :
    ((List.range nIn).map (fun i => (s!"in{i}", MSLBufferBinding.deviceBuf i true .ulong))).lookup s = none := by
  rw [List.lookup_eq_none_iff]
  intro ⟨k, v⟩ hmem
  rw [List.mem_map] at hmem
  rcases hmem with ⟨i, hi, heq⟩
  cases heq
  rw [List.mem_range] at hi
  simpa [bne_iff_ne] using hne i hi

theorem stdBindings_lookup_in (nIn j : Nat) (hj : j < nIn) :
    (stdBindings nIn).lookup s!"in{j}" = some (.deviceBuf j true .ulong) := by
  unfold stdBindings
  rw [List.lookup_append, lookup_mapIn_lt nIn j hj]
  rfl

theorem stdBindings_lookup_out (nIn : Nat) :
    (stdBindings nIn).lookup "out" = some (.deviceBuf nIn false .ulong) := by
  unfold stdBindings
  rw [List.lookup_append, lookup_mapIn_other nIn "out" (fun i _ => (in_ne_lit i).1.symm)]
  rfl

theorem stdBindings_lookup_n (nIn : Nat) :
    (stdBindings nIn).lookup "n" = some (.constantScalar (nIn + 1) .ulong) := by
  unfold stdBindings
  rw [List.lookup_append, lookup_mapIn_other nIn "n" (fun i _ => (in_ne_lit i).2.1.symm)]
  rfl

theorem stdBindings_lookup_none (nIn : Nat) (s : String)
    (hin : ∀ i < nIn, s ≠ s!"in{i}") (hout : s ≠ "out") (hn : s ≠ "n") :
    (stdBindings nIn).lookup s = none := by
  unfold stdBindings
  rw [List.lookup_append, lookup_mapIn_other nIn s hin]
  simp [List.lookup, beq_false_of_ne hout, beq_false_of_ne hn]

theorem initThreadLocals_std (k : MSLKernelDecl) (g0 : MSLGroupState) (tid : Dim3) (nIn : Nat)
    (hparams : k.params = stdKernelParams nIn) :
    initThreadLocals k g0 tid =
      initBuiltinLocal MSLLocals.empty "gid" .uint
        (g0.groupId.x * g0.groupDim.x + tid.x,
         g0.groupId.y * g0.groupDim.y + tid.y,
         g0.groupId.z * g0.groupDim.z + tid.z) := by
  let stepFn := fun (acc : MSLLocals) (p : MSLParamDecl) =>
    match p.attr with
    | some (.buffer _) | none => acc
    | some attr => initBuiltinLocal acc p.name p.ty (evalBuiltinCoords g0 tid attr)
  change k.params.foldl stepFn MSLLocals.empty = _
  rw [hparams]
  unfold stdKernelParams
  rw [List.foldl_append]
  have hfoldIn : ∀ xs : List Nat,
      (xs.map (fun i =>
        ({ ty := .pointer .device true .ulong, name := s!"in{i}", attr := some (.buffer i) } : MSLParamDecl))).foldl
        stepFn MSLLocals.empty = MSLLocals.empty := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons, List.foldl_cons, stepFn]; exact ih
  rw [hfoldIn (List.range nIn)]
  rfl

theorem initBuiltinLocal_gid_props (cx : Nat) (hcx : cx < 2 ^ 32) :
    let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
    ls.lookup? "gid" = some (BitVec.ofNat 64 cx) ∧
    ls.lookupType? "gid" = some .uint ∧
    ls.arrays = [] ∧
    (∀ s, s ≠ "gid" → ls.lookup? s = none ∧ ls.lookupType? s = none) := by
  have hmask : maskForType .uint (BitVec.ofNat 64 cx) = BitVec.ofNat 64 cx := by
    change BitVec.ofNat 64 cx &&& 0xFFFF_FFFF#64 = BitVec.ofNat 64 cx
    apply BitVec.eq_of_toNat_eq
    change (cx % 2 ^ 64) &&& 4294967295 = cx % 2 ^ 64
    have h64 : cx < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt h64]
    have h4 : (4294967295 : Nat) = 2 ^ 32 - 1 := by decide
    rw [h4, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hcx]
  dsimp only [initBuiltinLocal, MSLLocals.setField, MSLLocals.setTyped, MSLLocals.empty,
    MSLLocals.setAssoc, MSLLocals.setTypeAssoc]
  rw [hmask]
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro s hs
  simp [MSLLocals.lookup?, MSLLocals.lookupType?, List.lookup, beq_false_of_ne hs]

theorem dim3_coords_1d (m : Nat) :
    ({ x := m, y := 1, z := 1 } : Dim3).coords =
      (List.range m).map (fun x => ({ x := x, y := 0, z := 0 } : Dim3)) := by
  unfold Dim3.coords
  simp [List.range_succ]


def LaneInnerSpec (nIn len stepsInner : Nat)
    (inWords : Nat → List (BitVec 64)) (specWord : Nat → BitVec 64)
    (inner : List MSLStmt) : Prop :=
  ∀ (g : MSLGroupState) (done todo : List MSLThreadState)
    (cx tx lo f : Nat) (outMem : ByteMemory),
    cx < len → cx < 2 ^ 32 → len * 8 ≤ 2 ^ 64 → lo ≤ cx → stepsInner + 1 ≤ f →
    g.structs = [] → g.funcs = [] → g.bindings = stdBindings nIn →
    g.constantBuffers = [(nIn + 1, ByteMemory.ofU64Words [BitVec.ofNat 64 len])] →
    (∀ j < nIn, g.deviceBuffers.lookup j = some (ByteMemory.ofU64Words (inWords j)) ∧
      (inWords j).length = len) →
    g.deviceBuffers.lookup nIn = some outMem →
    outMem.bytes.size = len * 8 →
    (∀ a ∈ g.epochLog, SimtLogInv nIn lo cx a) →
    (∀ d ∈ done, d.halted = true) →
    g.threads = done ++ (
      { tid := { x := tx, y := 0, z := 0 }
        locals := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
        stmts := inner ++ [.returnStmt]
        halted := false } :: todo) →
    ∃ (f' : Nat) (thH : MSLThreadState) (g' : MSLGroupState) (outMem' : ByteMemory),
      runGroupWithDeviceLog f g [] = runGroupWithDeviceLog f' g' [] ∧
      f - (stepsInner + 1) ≤ f' ∧
      thH.halted = true ∧
      g'.threads = done ++ (thH :: todo) ∧
      g'.structs = [] ∧ g'.funcs = [] ∧ g'.bindings = stdBindings nIn ∧
      g'.constantBuffers = g.constantBuffers ∧
      (∀ j < nIn, g'.deviceBuffers.lookup j = some (ByteMemory.ofU64Words (inWords j))) ∧
      g'.deviceBuffers.lookup nIn = some outMem' ∧
      outMem'.bytes.size = len * 8 ∧
      outMem'.readU64Word? cx = some (specWord cx) ∧
      (∀ i, i ≠ cx → outMem'.readU64Word? i = outMem.readU64Word? i) ∧
      (∀ a ∈ g'.epochLog, SimtLogInv nIn lo (cx + 1) a)

theorem laneInner_storeOut (nIn len : Nat)
    (inWords : Nat → List (BitVec 64)) (specWord : Nat → BitVec 64)
    (compute : MSLExpr)
    (hEval : ∀ (g : MSLGroupState) (tid : Dim3) (cx lo : Nat),
      cx < len → cx < 2 ^ 32 → len * 8 ≤ 2 ^ 64 → lo ≤ cx →
      g.structs = [] → g.funcs = [] → g.bindings = stdBindings nIn →
      g.constantBuffers = [(nIn + 1, ByteMemory.ofU64Words [BitVec.ofNat 64 len])] →
      (∀ j < nIn, g.deviceBuffers.lookup j = some (ByteMemory.ofU64Words (inWords j)) ∧
        (inWords j).length = len) →
      (∀ a ∈ g.epochLog, SimtLogInv nIn lo cx a) →
      let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
      ∃ log1,
        evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog compute =
          .ok { value := specWord cx, fields := [], locals := ls, log := log1 } ∧
        (∀ a ∈ log1, SimtLogInv nIn lo cx a)) :
    LaneInnerSpec nIn len 1 inWords specWord [.indexAssign "out" (.var "gid") compute] := by
  intro g done todo cx tx lo f outMem hcxLen hcx32 hlen64 hlo hf
    hstr hfn hbind hconst hin hout hsize hlog hdone hthreads
  let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
  let tid : Dim3 := { x := tx, y := 0, z := 0 }
  let th0 : MSLThreadState := { tid, locals := ls, stmts := [.indexAssign "out" (.var "gid") compute, .returnStmt], halted := false }
  have ⟨hlkGid, htyGid, hArr, _⟩ := initBuiltinLocal_gid_props cx hcx32
  have ⟨hvarGid, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog cx hcx32 hlkGid htyGid
  obtain ⟨log1, hrhs, hlog1⟩ := hEval g tid cx lo hcxLen hcx32 hlen64 hlo hstr hfn hbind hconst hin hlog
  have hArrOut : ls.lookupArray? "out" = none := by
    dsimp only [ls]; simp [MSLLocals.lookupArray?, hArr]
  have hBindOut : g.bindings.lookup "out" = some (.deviceBuf nIn false .ulong) := by
    rw [hbind]; exact stdBindings_lookup_out nIn
  obtain ⟨outMem', log2, hexecW, hsize', hreadCx, hreadNe, hlog2, hneEmpty⟩ :=
    exec_indexAssign_dev_write g th0 [.returnStmt] (.var "gid") compute nIn lo cx len (specWord cx) log1 outMem
      hvarGid hrhs hcxLen hlen64 hArrOut hBindOut hout hsize hlo hlog1
  have hf1 : f = (f - 2) + 1 + 1 := by omega
  let th1 : MSLThreadState := { th0 with stmts := [.returnStmt] }
  let g1 : MSLGroupState := { g with epochLog := log2, deviceBuffers := setIndexedMem g.deviceBuffers nIn outMem', threads := done ++ (th1 :: todo) }
  have hstep1 : runGroupWithDeviceLog f g [] = runGroupWithDeviceLog ((f - 2) + 1) g1 [] := by
    rw [hf1]
    exact runGroupWithDeviceLog_step_stmt ((f - 2) + 1) g
      { g with epochLog := log2, deviceBuffers := setIndexedMem g.deviceBuffers nIn outMem' }
      done todo th0 th1 (.indexAssign "out" (.var "gid") compute) [.returnStmt]
      hthreads hdone rfl rfl rfl rfl hexecW (by intro h; simp [hneEmpty] at h)
  let th2 : MSLThreadState := { th1 with stmts := [], halted := true }
  let g2 : MSLGroupState := { g1 with threads := done ++ (th2 :: todo) }
  have hstep2 : runGroupWithDeviceLog ((f - 2) + 1) g1 [] = runGroupWithDeviceLog (f - 2) g2 [] :=
    runGroupWithDeviceLog_step_stmt (f - 2) g1 g1 done todo th1 th2 .returnStmt []
      rfl hdone rfl rfl rfl rfl (exec_returnStmt_step g1 th1 []) id
  refine ⟨f - 2, th2, g2, outMem', hstep1.trans hstep2, Nat.le_refl _, rfl, rfl,
    hstr, hfn, hbind, rfl, ?_, ?_, hsize', hreadCx, hreadNe, hlog2⟩
  · intro j hj
    dsimp only [g2, g1]
    rw [lookup_setIndexedMem_ne g.deviceBuffers nIn j outMem' (by omega)]
    exact (hin j hj).1
  · dsimp only [g2, g1]
    exact lookup_setIndexedMem_same g.deviceBuffers nIn outMem'

theorem laneInner_ifElse_storeOut (nIn len : Nat)
    (inWords : Nat → List (BitVec 64)) (specWord : Nat → BitVec 64)
    (cond thenExpr elseExpr : MSLExpr) (takeThen : Nat → Bool)
    (hCond : ∀ (g : MSLGroupState) (tid : Dim3) (cx lo : Nat),
      cx < len → cx < 2 ^ 32 → len * 8 ≤ 2 ^ 64 → lo ≤ cx →
      g.structs = [] → g.funcs = [] → g.bindings = stdBindings nIn →
      g.constantBuffers = [(nIn + 1, ByteMemory.ofU64Words [BitVec.ofNat 64 len])] →
      (∀ j < nIn, g.deviceBuffers.lookup j = some (ByteMemory.ofU64Words (inWords j)) ∧
        (inWords j).length = len) →
      (∀ a ∈ g.epochLog, SimtLogInv nIn lo cx a) →
      let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
      ∃ (cval : BitVec 64) (log1 : List MSLAccess),
        evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog cond =
          .ok { value := cval, fields := [], locals := ls, log := log1 } ∧
        (cval != 0#64) = takeThen cx ∧
        (log1.isEmpty = true → g.epochLog.isEmpty = true) ∧
        (∀ a ∈ log1, SimtLogInv nIn lo cx a))
    (hBranch : ∀ (g : MSLGroupState) (tid : Dim3) (cx lo : Nat),
      cx < len → cx < 2 ^ 32 → len * 8 ≤ 2 ^ 64 → lo ≤ cx →
      g.structs = [] → g.funcs = [] → g.bindings = stdBindings nIn →
      g.constantBuffers = [(nIn + 1, ByteMemory.ofU64Words [BitVec.ofNat 64 len])] →
      (∀ j < nIn, g.deviceBuffers.lookup j = some (ByteMemory.ofU64Words (inWords j)) ∧
        (inWords j).length = len) →
      (∀ a ∈ g.epochLog, SimtLogInv nIn lo cx a) →
      let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
      ∃ log2,
        evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog
          (if takeThen cx then thenExpr else elseExpr) =
          .ok { value := specWord cx, fields := [], locals := ls, log := log2 } ∧
        (∀ a ∈ log2, SimtLogInv nIn lo cx a)) :
    LaneInnerSpec nIn len 2 inWords specWord
      [.ifElse cond (.cons (.indexAssign "out" (.var "gid") thenExpr) .nil)
                    (.cons (.indexAssign "out" (.var "gid") elseExpr) .nil)] := by
  intro g done todo cx tx lo f outMem hcxLen hcx32 hlen64 hlo hf
    hstr hfn hbind hconst hin hout hsize hlog hdone hthreads
  let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
  let tid : Dim3 := { x := tx, y := 0, z := 0 }
  let stmtIf : MSLStmt := .ifElse cond (.cons (.indexAssign "out" (.var "gid") thenExpr) .nil)
                                       (.cons (.indexAssign "out" (.var "gid") elseExpr) .nil)
  let th0 : MSLThreadState := { tid, locals := ls, stmts := [stmtIf, .returnStmt], halted := false }
  obtain ⟨cval, log1, hcondEv, hcvalEq, hlog1Emp, hlog1⟩ :=
    hCond g tid cx lo hcxLen hcx32 hlen64 hlo hstr hfn hbind hconst hin hlog
  have hexecIf := exec_ifElse_step g th0 [.returnStmt] cond
    (.cons (.indexAssign "out" (.var "gid") thenExpr) .nil)
    (.cons (.indexAssign "out" (.var "gid") elseExpr) .nil) cval log1 hcondEv
  let chosen := if takeThen cx then thenExpr else elseExpr
  have hbrEq : (if cval != 0#64 then
      (MSLBlock.cons (.indexAssign "out" (.var "gid") thenExpr) .nil).toList
    else
      (MSLBlock.cons (.indexAssign "out" (.var "gid") elseExpr) .nil).toList) ++ [.returnStmt] =
    [.indexAssign "out" (.var "gid") chosen, .returnStmt] := by
    dsimp only [chosen]
    rw [hcvalEq]
    cases takeThen cx <;> rfl
  let th1 : MSLThreadState := { th0 with stmts := [.indexAssign "out" (.var "gid") chosen, .returnStmt] }
  let g1 : MSLGroupState := { g with epochLog := log1, threads := done ++ (th1 :: todo) }
  have hf1 : f = (f - 3) + 1 + 1 + 1 := by omega
  have hstep1 : runGroupWithDeviceLog f g [] = runGroupWithDeviceLog ((f - 3) + 1 + 1) g1 [] := by
    rw [hf1]
    rw [hbrEq] at hexecIf
    exact runGroupWithDeviceLog_step_stmt ((f - 3) + 1 + 1) g { g with epochLog := log1 }
      done todo th0 th1 stmtIf [.returnStmt] hthreads hdone rfl rfl rfl rfl hexecIf hlog1Emp
  have ⟨hlkGid, htyGid, hArr, _⟩ := initBuiltinLocal_gid_props cx hcx32
  have ⟨hvarGid, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g1) g1 tid ls g1.epochLog cx hcx32 hlkGid htyGid
  obtain ⟨log2, hrhs1, hlog2⟩ :=
    hBranch g1 tid cx lo hcxLen hcx32 hlen64 hlo hstr hfn hbind hconst hin hlog1
  have hArrOut : ls.lookupArray? "out" = none := by
    dsimp only [ls]; simp [MSLLocals.lookupArray?, hArr]
  have hBindOut : g1.bindings.lookup "out" = some (.deviceBuf nIn false .ulong) := by
    dsimp only [g1]; rw [hbind]; exact stdBindings_lookup_out nIn
  obtain ⟨outMem', log3, hexecW, hsize', hreadCx, hreadNe, hlog3, hneEmpty⟩ :=
    exec_indexAssign_dev_write g1 th1 [.returnStmt] (.var "gid") chosen nIn lo cx len (specWord cx) log2 outMem
      hvarGid hrhs1 hcxLen hlen64 hArrOut hBindOut hout hsize hlo hlog2
  let th2 : MSLThreadState := { th1 with stmts := [.returnStmt] }
  let g2 : MSLGroupState := { g1 with epochLog := log3, deviceBuffers := setIndexedMem g1.deviceBuffers nIn outMem', threads := done ++ (th2 :: todo) }
  have hstep2 : runGroupWithDeviceLog ((f - 3) + 1 + 1) g1 [] = runGroupWithDeviceLog ((f - 3) + 1) g2 [] :=
    runGroupWithDeviceLog_step_stmt ((f - 3) + 1) g1
      { g1 with epochLog := log3, deviceBuffers := setIndexedMem g1.deviceBuffers nIn outMem' }
      done todo th1 th2 (.indexAssign "out" (.var "gid") chosen) [.returnStmt]
      rfl hdone rfl rfl rfl rfl hexecW (by intro h; simp [hneEmpty] at h)
  let th3 : MSLThreadState := { th2 with stmts := [], halted := true }
  let g3 : MSLGroupState := { g2 with threads := done ++ (th3 :: todo) }
  have hstep3 : runGroupWithDeviceLog ((f - 3) + 1) g2 [] = runGroupWithDeviceLog (f - 3) g3 [] :=
    runGroupWithDeviceLog_step_stmt (f - 3) g2 g2 done todo th2 th3 .returnStmt []
      rfl hdone rfl rfl rfl rfl (exec_returnStmt_step g2 th2 []) id
  refine ⟨f - 3, th3, g3, outMem', (hstep1.trans hstep2).trans hstep3, Nat.le_refl _, rfl, rfl,
    hstr, hfn, hbind, rfl, ?_, ?_, hsize', hreadCx, hreadNe, hlog3⟩
  · intro j hj
    dsimp only [g3, g2, g1]
    rw [lookup_setIndexedMem_ne g.deviceBuffers nIn j outMem' (by omega)]
    exact (hin j hj).1
  · dsimp only [g3, g2, g1]
    exact lookup_setIndexedMem_same g.deviceBuffers nIn outMem'

private theorem nodup_getElem_inj :
    ∀ {xs : List Nat} (_ : xs.Nodup) {i j : Nat} (hi : i < xs.length) (hj : j < xs.length),
      xs[i] = xs[j] → i = j
  | [], _, _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | x :: xs, hnd, 0, 0, _, _, _ => rfl
  | x :: xs, hnd, 0, j + 1, _, hj, heq => by
    rw [List.nodup_cons] at hnd
    have hx : x = xs[j]'(Nat.lt_of_succ_lt_succ hj) := heq
    have hmem : xs[j]'(Nat.lt_of_succ_lt_succ hj) ∈ xs := List.getElem_mem _
    rw [← hx] at hmem
    exact absurd hmem hnd.1
  | x :: xs, hnd, i + 1, 0, hi, _, heq => by
    rw [List.nodup_cons] at hnd
    have hx : xs[i]'(Nat.lt_of_succ_lt_succ hi) = x := heq
    have hmem : xs[i]'(Nat.lt_of_succ_lt_succ hi) ∈ xs := List.getElem_mem _
    rw [hx] at hmem
    exact absurd hmem hnd.1
  | x :: xs, hnd, i + 1, j + 1, hi, hj, heq => by
    rw [List.nodup_cons] at hnd
    exact congrArg Nat.succ (nodup_getElem_inj hnd.2 (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) heq)

private theorem lookup_loads_step (inVars : List Nat) (inWords : Nat → List (BitVec 64))
    (len cx : Nat) (hcxLen : cx < len)
    (hinLen : ∀ j < inVars.length, (inWords j).length = len)
    (hnodup : inVars.Nodup) :
    ∀ (rem k0 : Nat) (g : MSLGroupState) (done todo : List MSLThreadState)
      (ls : MSLLocals) (tx lo f : Nat),
      k0 + rem = inVars.length →
      cx < 2 ^ 32 → len * 8 ≤ 2 ^ 64 →
      rem ≤ f →
      g.structs = [] → g.funcs = [] → g.bindings = stdBindings inVars.length →
      (∀ j < inVars.length, g.deviceBuffers.lookup j = some (ByteMemory.ofU64Words (inWords j))) →
      (∀ a ∈ g.epochLog, SimtLogInv inVars.length lo cx a) →
      (∀ d ∈ done, d.halted = true) →
      ls.lookup? "gid" = some (BitVec.ofNat 64 cx) →
      ls.lookupType? "gid" = some .uint →
      ls.arrays = [] →
      ls.lookup? "gid64" = some (BitVec.ofNat 64 cx) →
      ls.lookupType? "gid64" = some .ulong →
      (∀ j < k0, ∃ (hj : j < inVars.length) (hc : cx < (inWords j).length),
        ls.lookup? s!"v{inVars[j]}" = some ((inWords j)[cx]) ∧
        ls.lookupType? s!"v{inVars[j]}" = some .ulong) →
      ∀ (tail : List MSLStmt),
      g.threads = done ++ (
        { tid := { x := tx, y := 0, z := 0 }
          locals := ls
          stmts := ((List.range rem).map (fun d =>
            let k := k0 + d
            MSLStmt.varDecl .ulong s!"v{inVars[k]?.getD 0}" (.index s!"in{k}" (.var "gid")))) ++ tail
          halted := false } :: todo) →
      ∃ (g' : MSLGroupState) (ls' : MSLLocals),
        runGroupWithDeviceLog f g [] = runGroupWithDeviceLog (f - rem) g' [] ∧
        g'.threads = done ++ (
          { tid := { x := tx, y := 0, z := 0 }, locals := ls', stmts := tail, halted := false } :: todo) ∧
        g'.structs = [] ∧ g'.funcs = [] ∧ g'.bindings = stdBindings inVars.length ∧
        g'.constantBuffers = g.constantBuffers ∧
        g'.deviceBuffers = g.deviceBuffers ∧
        (∀ a ∈ g'.epochLog, SimtLogInv inVars.length lo cx a) ∧
        ls'.lookup? "gid" = some (BitVec.ofNat 64 cx) ∧
        ls'.lookupType? "gid" = some .uint ∧
        ls'.arrays = [] ∧
        ls'.lookup? "gid64" = some (BitVec.ofNat 64 cx) ∧
        ls'.lookupType? "gid64" = some .ulong ∧
        (∀ j (hj : j < inVars.length), ∃ (hc : cx < (inWords j).length),
          ls'.lookup? s!"v{inVars[j]}" = some ((inWords j)[cx]) ∧
          ls'.lookupType? s!"v{inVars[j]}" = some .ulong)
  | 0, k0, g, done, todo, ls, tx, lo, f, hk0, _, _, _, hstr, hfn, hbind, _, hlog, _, hgidV, hgidT, harr, hgid64V, hgid64T, hprev, tail, hthreads => by
    have hkEq : k0 = inVars.length := by omega
    refine ⟨g, ls, by simp, by simpa using hthreads, hstr, hfn, hbind, rfl, rfl, hlog,
      hgidV, hgidT, harr, hgid64V, hgid64T, ?_⟩
    intro j hj
    rcases hprev j (by omega) with ⟨_, hc, hv, ht⟩
    exact ⟨hc, hv, ht⟩
  | rem + 1, k0, g, done, todo, ls, tx, lo, f, hk0, hcx32, hlen64, hf, hstr, hfn, hbind, hinDev, hlog, hdone, hgidV, hgidT, harr, hgid64V, hgid64T, hprev, tail, hthreads => by
    have hk0Lt : k0 < inVars.length := by omega
    have hgetD : inVars[k0]?.getD 0 = inVars[k0] := by simp [hk0Lt]
    let id0 := inVars[k0]
    let tid : Dim3 := { x := tx, y := 0, z := 0 }
    let restLoads := (List.range rem).map (fun d =>
      let k := (k0 + 1) + d
      MSLStmt.varDecl .ulong s!"v{inVars[k]?.getD 0}" (.index s!"in{k}" (.var "gid")))
    have hrangeMap : ((List.range (rem + 1)).map (fun d =>
        let k := k0 + d
        MSLStmt.varDecl .ulong s!"v{inVars[k]?.getD 0}" (.index s!"in{k}" (.var "gid")))) ++ tail =
        MSLStmt.varDecl .ulong s!"v{id0}" (.index s!"in{k0}" (.var "gid")) :: (restLoads ++ tail) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.add_zero, hgetD, List.cons_append]
      congr 1
      congr 1
      apply List.map_congr_left
      intro d _
      dsimp only [Function.comp, Nat.succ_eq_add_one]
      have ha : k0 + (d + 1) = (k0 + 1) + d := by omega
      rw [ha]
    let th0 : MSLThreadState := { tid, locals := ls, stmts := MSLStmt.varDecl .ulong s!"v{id0}" (.index s!"in{k0}" (.var "gid")) :: (restLoads ++ tail), halted := false }
    have hthreads0 : g.threads = done ++ (th0 :: todo) := by
      rw [hthreads, hrangeMap]
    have ⟨hvarGid, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog cx hcx32 hgidV hgidT
    have hwLen0 : (inWords k0).length = len := hinLen k0 hk0Lt
    have hc0 : cx < (inWords k0).length := by omega
    have hw64 : (inWords k0).length < 2 ^ 64 := by omega
    have harrIn : ls.lookupArray? s!"in{k0}" = none := by simp [MSLLocals.lookupArray?, harr]
    have hbindIn : g.bindings.lookup s!"in{k0}" = some (.deviceBuf k0 true .ulong) := by
      rw [hbind]; exact stdBindings_lookup_in inVars.length k0 hk0Lt
    obtain ⟨log1, hreadEv, hlog1, hneEmp⟩ :=
      ev_index_dev_read kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog s!"in{k0}" (.var "gid")
        k0 inVars.length lo cx cx (inWords k0) hvarGid hc0 hw64 harrIn hbindIn (hinDev k0 hk0Lt) hk0Lt hlog
    have hexecDecl := exec_varDecl_ulong g th0 (restLoads ++ tail) s!"v{id0}" (.index s!"in{k0}" (.var "gid"))
      ((inWords k0)[cx]) log1 (by intro _ h; cases h) hreadEv
    let ls1 := ls.setTyped s!"v{id0}" .ulong ((inWords k0)[cx])
    let th1 : MSLThreadState := { tid, locals := ls1, stmts := restLoads ++ tail, halted := false }
    let g1 : MSLGroupState := { g with epochLog := log1, threads := done ++ (th1 :: todo) }
    have hf1 : f = (f - 1) + 1 := by omega
    have hstep1 : runGroupWithDeviceLog f g [] = runGroupWithDeviceLog (f - 1) g1 [] := by
      rw [hf1]
      exact runGroupWithDeviceLog_step_stmt (f - 1) g { g with epochLog := log1 }
        done todo th0 th1 (.varDecl .ulong s!"v{id0}" (.index s!"in{k0}" (.var "gid"))) (restLoads ++ tail)
        hthreads0 hdone rfl rfl rfl rfl hexecDecl (by intro h; simp [hneEmp] at h)
    have hneGid := (var_ne_special id0).2.2.1.symm
    have hneGid64 := (var_ne_special id0).2.2.2.symm
    have hgid1 := setTyped_lookup_ne ls s!"v{id0}" "gid" .ulong ((inWords k0)[cx]) hneGid
    have hgid641 := setTyped_lookup_ne ls s!"v{id0}" "gid64" .ulong ((inWords k0)[cx]) hneGid64
    have hprev1 : ∀ j < k0 + 1, ∃ (hj : j < inVars.length) (hc : cx < (inWords j).length),
        ls1.lookup? s!"v{inVars[j]}" = some ((inWords j)[cx]) ∧
        ls1.lookupType? s!"v{inVars[j]}" = some .ulong := by
      intro j hj
      by_cases hjk : j = k0
      · subst hjk
        have hsame := setTyped_lookup_same ls s!"v{id0}" .ulong ((inWords j)[cx])
        exact ⟨hk0Lt, hc0, hsame.1, hsame.2⟩
      · have hjLt : j < k0 := by omega
        rcases hprev j hjLt with ⟨hjIn, hcj, hvj, htj⟩
        have hneIdx : inVars[j] ≠ inVars[k0] := by
          intro heqVal
          exact hjk (nodup_getElem_inj hnodup hjIn hk0Lt heqVal)
        have hneStr : s!"v{inVars[j]}" ≠ s!"v{id0}" := fun hs =>
          hneIdx (prefix_nat_inj "v" inVars[j] id0 (by simpa [toString] using hs))
        have hneL := setTyped_lookup_ne ls s!"v{id0}" s!"v{inVars[j]}" .ulong ((inWords k0)[cx]) hneStr
        exact ⟨hjIn, hcj, hneL.1.trans hvj, hneL.2.trans htj⟩
    obtain ⟨g2, ls2, hstepRest, hth2, hstr2, hfn2, hbind2, hconst2, hdev2, hlog2,
            hgid2V, hgid2T, harr2, hgid642V, hgid642T, hallVars⟩ :=
      lookup_loads_step inVars inWords len cx hcxLen hinLen hnodup rem (k0 + 1) g1 done todo ls1 tx lo (f - 1)
        (by omega) hcx32 hlen64 (by omega) hstr hfn hbind hinDev hlog1 hdone
        (hgid1.1.trans hgidV) (hgid1.2.trans hgidT) harr (hgid641.1.trans hgid64V) (hgid641.2.trans hgid64T)
        hprev1 tail rfl
    have hfSub : f - 1 - rem = f - (rem + 1) := by omega
    rw [hfSub] at hstepRest
    exact ⟨g2, ls2, hstep1.trans hstepRest, hth2, hstr2, hfn2, hbind2, hconst2, hdev2, hlog2,
      hgid2V, hgid2T, harr2, hgid642V, hgid642T, hallVars⟩

theorem laneInner_varDecls_storeOut (inVars : List Nat) (len : Nat)
    (inWords : Nat → List (BitVec 64)) (specWord : Nat → BitVec 64)
    (rhs : MSLExpr) (hnodup : inVars.Nodup)
    (hRhs : ∀ (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals) (cx : Nat),
      cx < len → cx < 2 ^ 32 →
      ls.lookup? "gid64" = some (BitVec.ofNat 64 cx) →
      ls.lookupType? "gid64" = some .ulong →
      (∀ j (hj : j < inVars.length) (hc : cx < (inWords j).length),
        ls.lookup? s!"v{inVars[j]}" = some ((inWords j)[cx]) ∧
        ls.lookupType? s!"v{inVars[j]}" = some .ulong) →
      evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog rhs =
        .ok { value := specWord cx, fields := [], locals := ls, log := g.epochLog }) :
    LaneInnerSpec inVars.length len (inVars.length + 2) inWords specWord
      ([MSLStmt.varDecl .ulong "gid64" (.cast .ulong (.var "gid"))] ++
        (List.range inVars.length).map (fun k =>
          MSLStmt.varDecl .ulong s!"v{inVars[k]?.getD 0}" (.index s!"in{k}" (.var "gid"))) ++
        [MSLStmt.indexAssign "out" (.var "gid") rhs]) := by
  intro g done todo cx tx lo f outMem hcxLen hcx32 hlen64 hlo hf
    hstr hfn hbind hconst hin hout hsize hlog hdone hthreads
  let ls0 := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
  let tid : Dim3 := { x := tx, y := 0, z := 0 }
  let loads := (List.range inVars.length).map (fun d =>
    let k := 0 + d
    MSLStmt.varDecl .ulong s!"v{inVars[k]?.getD 0}" (.index s!"in{k}" (.var "gid")))
  have hloadsEq : (List.range inVars.length).map (fun k =>
      MSLStmt.varDecl .ulong s!"v{inVars[k]?.getD 0}" (.index s!"in{k}" (.var "gid"))) = loads := by
    apply List.map_congr_left
    intro d _; simp
  let tailW : List MSLStmt := [MSLStmt.indexAssign "out" (.var "gid") rhs, .returnStmt]
  let th0 : MSLThreadState :=
    { tid, locals := ls0
      stmts := MSLStmt.varDecl .ulong "gid64" (.cast .ulong (.var "gid")) :: (loads ++ tailW)
      halted := false }
  have hthreads0 : g.threads = done ++ (th0 :: todo) := by
    rw [hthreads, hloadsEq]
    simp [List.append_assoc, tailW, th0, ls0, tid]
  have ⟨hlkGid0, htyGid0, harr0, _⟩ := initBuiltinLocal_gid_props cx hcx32
  have ⟨_, hcastGid0⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls0 g.epochLog cx hcx32 hlkGid0 htyGid0
  have hexecGid64 := exec_varDecl_ulong g th0 (loads ++ tailW) "gid64" (.cast .ulong (.var "gid"))
    (BitVec.ofNat 64 cx) g.epochLog (by intro _ h; cases h) hcastGid0
  let ls1 := ls0.setTyped "gid64" .ulong (BitVec.ofNat 64 cx)
  let th1 : MSLThreadState := { tid, locals := ls1, stmts := loads ++ tailW, halted := false }
  let g1 : MSLGroupState := { g with threads := done ++ (th1 :: todo) }
  have hfStep0 : f = (f - 1) + 1 := by omega
  have hstep0 : runGroupWithDeviceLog f g [] = runGroupWithDeviceLog (f - 1) g1 [] := by
    rw [hfStep0]
    exact runGroupWithDeviceLog_step_stmt (f - 1) g g done todo th0 th1
      (.varDecl .ulong "gid64" (.cast .ulong (.var "gid"))) (loads ++ tailW)
      hthreads0 hdone rfl rfl rfl rfl hexecGid64 id
  have hneG64 : ("gid" : String) ≠ "gid64" := by decide
  have hgid1 := setTyped_lookup_ne ls0 "gid64" "gid" .ulong (BitVec.ofNat 64 cx) hneG64
  have hgid641 := setTyped_lookup_same ls0 "gid64" .ulong (BitVec.ofNat 64 cx)
  obtain ⟨g2, ls2, hstepLoads, hth2, hstr2, hfn2, hbind2, hconst2, hdev2, hlog2,
          hgid2V, hgid2T, harr2, hgid642V, hgid642T, hallVars⟩ :=
    lookup_loads_step inVars inWords len cx hcxLen (fun j hj => (hin j hj).2) hnodup
      inVars.length 0 g1 done todo ls1 tx lo (f - 1) (by omega) hcx32 hlen64 (by omega)
      hstr hfn hbind (fun j hj => (hin j hj).1) hlog hdone
      (hgid1.1.trans hlkGid0) (hgid1.2.trans htyGid0) harr0 hgid641.1 hgid641.2
      (fun _ hj => absurd hj (Nat.not_lt_zero _)) tailW rfl
  let th2 : MSLThreadState := { tid, locals := ls2, stmts := tailW, halted := false }
  have ⟨hvarGid2, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g2) g2 tid ls2 g2.epochLog cx hcx32 hgid2V hgid2T
  have hrhs2 := hRhs g2 tid ls2 cx hcxLen hcx32 hgid642V hgid642T
    (fun j hj _ => by rcases hallVars j hj with ⟨_, hv, ht⟩; exact ⟨hv, ht⟩)
  have harrOut2 : ls2.lookupArray? "out" = none := by simp [MSLLocals.lookupArray?, harr2]
  have hbindOut2 : g2.bindings.lookup "out" = some (.deviceBuf inVars.length false .ulong) := by
    rw [hbind2]; exact stdBindings_lookup_out inVars.length
  have hout2 : g2.deviceBuffers.lookup inVars.length = some outMem := by
    rw [hdev2]; exact hout
  obtain ⟨outMem', log3, hexecW, hsize', hreadCx, hreadNe, hlog3, hneEmp⟩ :=
    exec_indexAssign_dev_write g2 th2 [.returnStmt] (.var "gid") rhs inVars.length lo cx len (specWord cx)
      g2.epochLog outMem hvarGid2 hrhs2 hcxLen hlen64 harrOut2 hbindOut2 hout2 hsize hlo hlog2
  let fRem := f - (inVars.length + 3)
  have hfRemEq : f - 1 - inVars.length = fRem + 1 + 1 := by omega
  let th3 : MSLThreadState := { th2 with stmts := [.returnStmt] }
  let g3 : MSLGroupState := { g2 with epochLog := log3, deviceBuffers := setIndexedMem g2.deviceBuffers inVars.length outMem', threads := done ++ (th3 :: todo) }
  have hstepW : runGroupWithDeviceLog (f - 1 - inVars.length) g2 [] = runGroupWithDeviceLog (fRem + 1) g3 [] := by
    rw [hfRemEq]
    exact runGroupWithDeviceLog_step_stmt (fRem + 1) g2
      { g2 with epochLog := log3, deviceBuffers := setIndexedMem g2.deviceBuffers inVars.length outMem' }
      done todo th2 th3 (.indexAssign "out" (.var "gid") rhs) [.returnStmt]
      hth2 hdone rfl rfl rfl rfl hexecW (by intro h; simp [hneEmp] at h)
  let th4 : MSLThreadState := { th3 with stmts := [], halted := true }
  let g4 : MSLGroupState := { g3 with threads := done ++ (th4 :: todo) }
  have hstepRet : runGroupWithDeviceLog (fRem + 1) g3 [] = runGroupWithDeviceLog fRem g4 [] :=
    runGroupWithDeviceLog_step_stmt fRem g3 g3 done todo th3 th4 .returnStmt []
      rfl hdone rfl rfl rfl rfl (exec_returnStmt_step g3 th3 []) id
  refine ⟨fRem, th4, g4, outMem', ((hstep0.trans hstepLoads).trans hstepW).trans hstepRet,
    Nat.le_refl _, rfl, rfl, hstr2, hfn2, hbind2, hconst2, ?_, ?_, hsize', hreadCx, hreadNe, hlog3⟩
  · intro j hj
    dsimp only [g4, g3]
    rw [lookup_setIndexedMem_ne g2.deviceBuffers inVars.length j outMem' (by omega), hdev2]
    exact (hin j hj).1
  · dsimp only [g4, g3]
    exact lookup_setIndexedMem_same g2.deviceBuffers inVars.length outMem'

private theorem mslBlock_toList_ofList : ∀ (xs : List MSLStmt), (MSLBlock.ofList xs).toList = xs
  | [] => rfl
  | _ :: xs => congrArg (_ :: ·) (mslBlock_toList_ofList xs)

private theorem runGroup_guarded_lanes (nIn len groupSize gx stepsInner : Nat)
    (inWords : Nat → List (BitVec 64)) (specWord : Nat → BitVec 64)
    (inner : List MSLStmt)
    (hInner : LaneInnerSpec nIn len stepsInner inWords specWord inner)
    (hlen64 : len * 8 ≤ 2 ^ 64) :
    let body := [MSLStmt.ifElse (.lt (.cast .ulong (.var "gid")) (.var "n")) (MSLBlock.ofList inner) .nil, .returnStmt]
    let mkLane := fun tx => ({
      tid := { x := tx, y := 0, z := 0 }
      locals := initBuiltinLocal MSLLocals.empty "gid" .uint (gx * groupSize + tx, 0, 0)
      stmts := body
      halted := false } : MSLThreadState)
    ∀ (rem tx0 f : Nat) (g : MSLGroupState) (done : List MSLThreadState) (outMem0 outMem : ByteMemory),
      tx0 + rem = groupSize →
      (gx + 1) * groupSize < 2 ^ 32 →
      rem * (stepsInner + 2) ≤ f →
      g.structs = [] → g.funcs = [] → g.bindings = stdBindings nIn →
      g.constantBuffers = [(nIn + 1, ByteMemory.ofU64Words [BitVec.ofNat 64 len])] →
      (∀ j < nIn, g.deviceBuffers.lookup j = some (ByteMemory.ofU64Words (inWords j)) ∧
        (inWords j).length = len) →
      g.deviceBuffers.lookup nIn = some outMem →
      outMem.bytes.size = len * 8 →
      (∀ i < len,
        (gx * groupSize ≤ i ∧ i < gx * groupSize + tx0 → outMem.readU64Word? i = some (specWord i)) ∧
        (¬ (gx * groupSize ≤ i ∧ i < gx * groupSize + tx0) → outMem.readU64Word? i = outMem0.readU64Word? i)) →
      (∀ a ∈ g.epochLog, SimtLogInv nIn (min len (gx * groupSize)) (min len (gx * groupSize + tx0)) a) →
      (∀ d ∈ done, d.halted = true) →
      g.threads = done ++ (List.range rem).map (fun d => mkLane (tx0 + d)) →
      ∃ (gFinal : MSLGroupState) (outMemFinal : ByteMemory),
        runGroupWithDeviceLog f g [] = .ok (gFinal, gFinal.epochLog.filter isDeviceAccess) ∧
        (∀ j < nIn, gFinal.deviceBuffers.lookup j = some (ByteMemory.ofU64Words (inWords j))) ∧
        gFinal.deviceBuffers.lookup nIn = some outMemFinal ∧
        outMemFinal.bytes.size = len * 8 ∧
        (∀ i < len,
          (gx * groupSize ≤ i ∧ i < (gx + 1) * groupSize → outMemFinal.readU64Word? i = some (specWord i)) ∧
          (¬ (gx * groupSize ≤ i ∧ i < (gx + 1) * groupSize) → outMemFinal.readU64Word? i = outMem0.readU64Word? i)) ∧
        (∀ a ∈ gFinal.epochLog.filter isDeviceAccess,
          SimtLogInv nIn (min len (gx * groupSize)) (min len ((gx + 1) * groupSize)) a)
  | 0, tx0, f, g, done, outMem0, outMem, htx, _, _, _, _, _, _, hin, hout, hsize, hwords, hlog, hdone, hthreads => by
    have htxEq : tx0 = groupSize := by omega
    have hcxEq : gx * groupSize + tx0 = (gx + 1) * groupSize := by rw [Nat.succ_mul]; omega
    have hallH : g.threads.all (·.halted) = true := by
      rw [hthreads, List.range_zero, List.map_nil, List.append_nil, List.all_eq_true]
      exact hdone
    refine ⟨g, outMem, runGroupWithDeviceLog_all_halted f g hallH,
      fun j hj => (hin j hj).1, hout, hsize, ?_, ?_⟩
    · intro i hi
      rw [← hcxEq]
      exact hwords i hi
    · intro a ha
      rw [List.mem_filter] at ha
      rw [← hcxEq]
      exact hlog a ha.1
  | rem + 1, tx0, f, g, done, outMem0, outMem, htx, hgrid32, hf, hstr, hfn, hbind, hconst, hin, hout, hsize, hwords, hlog, hdone, hthreads => by
    let body := [MSLStmt.ifElse (.lt (.cast .ulong (.var "gid")) (.var "n")) (MSLBlock.ofList inner) .nil, .returnStmt]
    let mkLane := fun tx => ({
      tid := { x := tx, y := 0, z := 0 }
      locals := initBuiltinLocal MSLLocals.empty "gid" .uint (gx * groupSize + tx, 0, 0)
      stmts := body
      halted := false } : MSLThreadState)
    let cx := gx * groupSize + tx0
    have hcx32 : cx < 2 ^ 32 := by
      have : cx < (gx + 1) * groupSize := by dsimp [cx]; rw [Nat.succ_mul]; omega
      omega
    let todo := (List.range rem).map (fun d => mkLane ((tx0 + 1) + d))
    have hmapSplit : (List.range (rem + 1)).map (fun d => mkLane (tx0 + d)) = mkLane tx0 :: todo := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.add_zero]
      congr 1
      apply List.map_congr_left
      intro d _
      dsimp only [Function.comp, Nat.succ_eq_add_one]
      have ha : tx0 + (d + 1) = (tx0 + 1) + d := by omega
      rw [ha]
    let th0 := mkLane tx0
    have hthreads0 : g.threads = done ++ (th0 :: todo) := by
      rw [hthreads, hmapSplit]
    let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
    let tid : Dim3 := { x := tx0, y := 0, z := 0 }
    have ⟨hlkGid, htyGid, _, hotherNone⟩ := initBuiltinLocal_gid_props cx hcx32
    have ⟨_, hcastGid⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog cx hcx32 hlkGid htyGid
    have hnNone := hotherNone "n" (by decide)
    have hbindN : g.bindings.lookup "n" = some (.constantScalar (nIn + 1) .ulong) := by
      rw [hbind]; exact stdBindings_lookup_n nIn
    have hconstN : g.constantBuffers.lookup (nIn + 1) = some (ByteMemory.ofU64Words [BitVec.ofNat 64 len]) := by
      rw [hconst]; simp
    have ⟨hevN, htyN⟩ := ev_var_const_ulong kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog
      "n" (nIn + 1) (BitVec.ofNat 64 len) hnNone.1 hnNone.2 hbindN hconstN
    have htyCast : inferExprType g ls (.cast .ulong (.var "gid")) = .ulong := rfl
    have hevLt := ev_lt_ulong kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog
      (.cast .ulong (.var "gid")) (.var "n") (BitVec.ofNat 64 cx) (BitVec.ofNat 64 len)
      hcastGid hevN htyCast htyN
    have hexecGuard := exec_ifElse_step g th0 [.returnStmt]
      (.lt (.cast .ulong (.var "gid")) (.var "n")) (MSLBlock.ofList inner) .nil
      (if BitVec.ult (BitVec.ofNat 64 cx) (BitVec.ofNat 64 len) then 1#64 else 0#64) g.epochLog hevLt
    have hultEq : BitVec.ult (BitVec.ofNat 64 cx) (BitVec.ofNat 64 len) = decide (cx < len) := by
      have hlenLt64 : len < 2 ^ 64 := by omega
      have hcxLt64 : cx < 2 ^ 64 := by omega
      simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcxLt64, Nat.mod_eq_of_lt hlenLt64]
    have hfOne : 1 ≤ f := by
      have : 1 * (stepsInner + 2) ≤ (rem + 1) * (stepsInner + 2) := Nat.mul_le_mul_right _ (by omega)
      omega
    have hfSplit : f = (f - 1) + 1 := by omega
    by_cases hcxLt : cx < len
    · have hcondNz : ((if BitVec.ult (BitVec.ofNat 64 cx) (BitVec.ofNat 64 len) then (1#64 : BitVec 64) else 0#64) != 0#64) = true := by
        rw [hultEq, decide_eq_true hcxLt]; rfl
      have htoList : (MSLBlock.ofList inner).toList = inner := mslBlock_toList_ofList inner
      let th1 : MSLThreadState := { tid, locals := ls, stmts := inner ++ [.returnStmt], halted := false }
      let g1 : MSLGroupState := { g with threads := done ++ (th1 :: todo) }
      have hstepG : runGroupWithDeviceLog f g [] = runGroupWithDeviceLog (f - 1) g1 [] := by
        rw [hfSplit]
        simp only [hcondNz, ite_true, htoList] at hexecGuard
        exact runGroupWithDeviceLog_step_stmt (f - 1) g g done todo th0 th1
          (.ifElse (.lt (.cast .ulong (.var "gid")) (.var "n")) (MSLBlock.ofList inner) .nil) [.returnStmt]
          hthreads0 hdone rfl rfl rfl rfl hexecGuard id
      have hminLo : min len (gx * groupSize) = gx * groupSize := Nat.min_eq_right (by dsimp [cx] at hcxLt; omega)
      have hminCx : min len cx = cx := Nat.min_eq_right (Nat.le_of_lt hcxLt)
      have hminCx1 : min len (gx * groupSize + (tx0 + 1)) = cx + 1 := by
        have : gx * groupSize + (tx0 + 1) = cx + 1 := by dsimp [cx]; omega
        rw [this]
        exact Nat.min_eq_right (by omega)
      have hlogIn : ∀ a ∈ g1.epochLog, SimtLogInv nIn (gx * groupSize) cx a := by
        intro a ha
        have h0 := hlog a ha
        rwa [hminLo, hminCx] at h0
      have hfIn : stepsInner + 1 ≤ f - 1 := by
        have : (rem + 1) * (stepsInner + 2) = rem * (stepsInner + 2) + (stepsInner + 2) := Nat.succ_mul rem (stepsInner + 2)
        omega
      obtain ⟨f', thH, g2, outMem', hstepIn, hfRem, hthH, hth2, hstr2, hfn2, hbind2, hconst2,
              hin2, hout2, hsize2, hreadCx, hreadNe, hlog2⟩ :=
        hInner g1 done todo cx tx0 (gx * groupSize) (f - 1) outMem hcxLt hcx32 hlen64
          (by dsimp [cx]; omega) hfIn hstr hfn hbind hconst hin hout hsize hlogIn hdone rfl
      have hthreadsNext : g2.threads = (done ++ [thH]) ++ todo := by
        rw [hth2, List.append_assoc]; rfl
      have hdoneNext : ∀ d ∈ done ++ [thH], d.halted = true := by
        intro d hd
        rcases List.mem_append.mp hd with h1 | h2
        · exact hdone d h1
        · rw [List.mem_singleton.mp h2]; exact hthH
      have hfNext : rem * (stepsInner + 2) ≤ f' := by
        have : (rem + 1) * (stepsInner + 2) = rem * (stepsInner + 2) + (stepsInner + 2) := Nat.succ_mul rem (stepsInner + 2)
        omega
      have hwordsNext : ∀ i < len,
          (gx * groupSize ≤ i ∧ i < gx * groupSize + (tx0 + 1) → outMem'.readU64Word? i = some (specWord i)) ∧
          (¬ (gx * groupSize ≤ i ∧ i < gx * groupSize + (tx0 + 1)) → outMem'.readU64Word? i = outMem0.readU64Word? i) := by
        intro i hi
        by_cases hicx : i = cx
        · subst hicx
          refine ⟨fun _ => hreadCx, fun hnot => absurd ⟨by dsimp [cx]; omega, by dsimp [cx]; omega⟩ hnot⟩
        · rw [hreadNe i hicx]
          rcases hwords i hi with ⟨hw1, hw2⟩
          refine ⟨fun ⟨h1, h2⟩ => hw1 ⟨h1, by dsimp [cx] at hicx; omega⟩,
                  fun hnot => hw2 (fun ⟨h1, h2⟩ => hnot ⟨h1, by omega⟩)⟩
      have hlogNext : ∀ a ∈ g2.epochLog, SimtLogInv nIn (min len (gx * groupSize)) (min len (gx * groupSize + (tx0 + 1))) a := by
        rw [hminLo, hminCx1]
        exact hlog2
      obtain ⟨gF, outMemF, hrest, hinF, houtF, hsizeF, hwordsF, hlogF⟩ :=
        runGroup_guarded_lanes nIn len groupSize gx stepsInner inWords specWord inner hInner hlen64
          rem (tx0 + 1) f' g2 (done ++ [thH]) outMem0 outMem' (by omega) hgrid32 hfNext
          hstr2 hfn2 hbind2 (hconst2.trans hconst) (fun j hj => ⟨hin2 j hj, (hin j hj).2⟩)
          hout2 hsize2 hwordsNext hlogNext hdoneNext hthreadsNext
      exact ⟨gF, outMemF, (hstepG.trans hstepIn).trans hrest, hinF, houtF, hsizeF, hwordsF, hlogF⟩
    · have hcondZ : ((if BitVec.ult (BitVec.ofNat 64 cx) (BitVec.ofNat 64 len) then (1#64 : BitVec 64) else 0#64) != 0#64) = false := by
        rw [hultEq, decide_eq_false hcxLt]; rfl
      let th1 : MSLThreadState := { tid, locals := ls, stmts := [.returnStmt], halted := false }
      let g1 : MSLGroupState := { g with threads := done ++ (th1 :: todo) }
      have hstepG : runGroupWithDeviceLog f g [] = runGroupWithDeviceLog (f - 1) g1 [] := by
        rw [hfSplit]
        simp only [hcondZ, Bool.false_eq_true, ite_false] at hexecGuard
        exact runGroupWithDeviceLog_step_stmt (f - 1) g g done todo th0 th1
          (.ifElse (.lt (.cast .ulong (.var "gid")) (.var "n")) (MSLBlock.ofList inner) .nil) [.returnStmt]
          hthreads0 hdone rfl rfl rfl rfl hexecGuard id
      have hfTwo : f - 1 = (f - 2) + 1 := by
        have : 1 * (stepsInner + 2) ≤ (rem + 1) * (stepsInner + 2) := Nat.mul_le_mul_right _ (by omega)
        omega
      let th2 : MSLThreadState := { th1 with stmts := [], halted := true }
      let g2 : MSLGroupState := { g1 with threads := done ++ (th2 :: todo) }
      have hstepR : runGroupWithDeviceLog (f - 1) g1 [] = runGroupWithDeviceLog (f - 2) g2 [] := by
        rw [hfTwo]
        exact runGroupWithDeviceLog_step_stmt (f - 2) g1 g1 done todo th1 th2 .returnStmt []
          rfl hdone rfl rfl rfl rfl (exec_returnStmt_step g1 th1 []) id
      have hthreadsNext : g2.threads = (done ++ [th2]) ++ todo := by
        dsimp only [g2]; rw [List.append_assoc]; rfl
      have hdoneNext : ∀ d ∈ done ++ [th2], d.halted = true := by
        intro d hd
        rcases List.mem_append.mp hd with h1 | h2
        · exact hdone d h1
        · rw [List.mem_singleton.mp h2]
      have hfNext : rem * (stepsInner + 2) ≤ f - 2 := by
        have : (rem + 1) * (stepsInner + 2) = rem * (stepsInner + 2) + (stepsInner + 2) := Nat.succ_mul rem (stepsInner + 2)
        omega
      have hwordsNext : ∀ i < len,
          (gx * groupSize ≤ i ∧ i < gx * groupSize + (tx0 + 1) → outMem.readU64Word? i = some (specWord i)) ∧
          (¬ (gx * groupSize ≤ i ∧ i < gx * groupSize + (tx0 + 1)) → outMem.readU64Word? i = outMem0.readU64Word? i) := by
        intro i hi
        have hiLtCx : i < cx := by omega
        rcases hwords i hi with ⟨hw1, hw2⟩
        refine ⟨fun ⟨h1, _⟩ => hw1 ⟨h1, hiLtCx⟩, fun hnot => hw2 (fun ⟨h1, _⟩ => hnot ⟨h1, by dsimp [cx] at hiLtCx; omega⟩)⟩
      have hminEq : min len (gx * groupSize + (tx0 + 1)) = min len cx := by dsimp [cx] at hcxLt ⊢; omega
      have hlogNext : ∀ a ∈ g2.epochLog, SimtLogInv nIn (min len (gx * groupSize)) (min len (gx * groupSize + (tx0 + 1))) a := by
        rw [hminEq]; exact hlog
      obtain ⟨gF, outMemF, hrest, hinF, houtF, hsizeF, hwordsF, hlogF⟩ :=
        runGroup_guarded_lanes nIn len groupSize gx stepsInner inWords specWord inner hInner hlen64
          rem (tx0 + 1) (f - 2) g2 (done ++ [th2]) outMem0 outMem (by omega) hgrid32 hfNext
          hstr hfn hbind hconst hin hout hsize hwordsNext hlogNext hdoneNext hthreadsNext
      exact ⟨gF, outMemF, (hstepG.trans hstepR).trans hrest, hinF, houtF, hsizeF, hwordsF, hlogF⟩

private theorem evalMSLKernelLoop_guarded_groups (nIn len nGroups groupSize stepsInner fuelPerGroup : Nat)
    (k : MSLKernelDecl) (inWords : Nat → List (BitVec 64)) (specWord : Nat → BitVec 64)
    (inner : List MSLStmt)
    (hparams : k.params = stdKernelParams nIn)
    (hshared : k.sharedDecls = [])
    (hbody : k.body = [MSLStmt.ifElse (.lt (.cast .ulong (.var "gid")) (.var "n")) (MSLBlock.ofList inner) .nil, .returnStmt])
    (hInner : LaneInnerSpec nIn len stepsInner inWords specWord inner)
    (hlen64 : len * 8 ≤ 2 ^ 64)
    (hgrid32 : nGroups * groupSize < 2 ^ 32)
    (hfuel : groupSize * (stepsInner + 2) ≤ fuelPerGroup) :
    let gridDim : Dim3 := { x := nGroups, y := 1, z := 1 }
    let groupDim : Dim3 := { x := groupSize, y := 1, z := 1 }
    let constBufs := [(nIn + 1, ByteMemory.ofU64Words [BitVec.ofNat 64 len])]
    ∀ (rem gx0 : Nat) (devBufs : List (Nat × ByteMemory)) (outMem : ByteMemory)
      (priorLog : List MSLAccess),
      gx0 + rem = nGroups →
      (∀ j < nIn, devBufs.lookup j = some (ByteMemory.ofU64Words (inWords j)) ∧
        (inWords j).length = len) →
      devBufs.lookup nIn = some outMem →
      outMem.bytes.size = len * 8 →
      (∀ i < len, i < gx0 * groupSize → outMem.readU64Word? i = some (specWord i)) →
      (∀ a ∈ priorLog, SimtLogInv nIn 0 (min len (gx0 * groupSize)) a) →
      ∃ (devBufsF : List (Nat × ByteMemory)) (outMemF : ByteMemory),
        evalMSLKernelLoop fuelPerGroup k gridDim groupDim constBufs [] [] devBufs priorLog
          ((List.range rem).map (fun d => ({ x := gx0 + d, y := 0, z := 0 } : Dim3))) = .ok devBufsF ∧
        devBufsF.lookup nIn = some outMemF ∧
        (∀ i < len, i < nGroups * groupSize → outMemF.readU64Word? i = some (specWord i))
  | 0, gx0, devBufs, outMem, priorLog, hgx, _, hout, _, hwords, _ => by
    have hgxEq : gx0 = nGroups := by omega
    subst hgxEq
    refine ⟨devBufs, outMem, rfl, hout, hwords⟩
  | rem + 1, gx0, devBufs, outMem, priorLog, hgx, hin, hout, hsize, hwords, hprior => by
    let gridDim : Dim3 := { x := nGroups, y := 1, z := 1 }
    let groupDim : Dim3 := { x := groupSize, y := 1, z := 1 }
    let constBufs := [(nIn + 1, ByteMemory.ofU64Words [BitVec.ofNat 64 len])]
    have hmapG : (List.range (rem + 1)).map (fun d => ({ x := gx0 + d, y := 0, z := 0 } : Dim3)) =
        { x := gx0, y := 0, z := 0 } :: (List.range rem).map (fun d => ({ x := (gx0 + 1) + d, y := 0, z := 0 } : Dim3)) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.add_zero]
      congr 1
      apply List.map_congr_left
      intro d _
      dsimp only [Function.comp, Nat.succ_eq_add_one]
      have ha : gx0 + (d + 1) = (gx0 + 1) + d := by omega
      rw [ha]
    let g0 := initGroupState k gridDim groupDim { x := gx0, y := 0, z := 0 } devBufs constBufs [] [] fuelPerGroup
    have hgx1Lt : (gx0 + 1) * groupSize < 2 ^ 32 := by
      have hle : (gx0 + 1) * groupSize ≤ nGroups * groupSize := Nat.mul_le_mul_right groupSize (by omega)
      omega
    have hbind0 : g0.bindings = stdBindings nIn := by
      dsimp only [g0, initGroupState]
      exact buildKernelBindings_std k nIn hparams hshared
    let body := [MSLStmt.ifElse (.lt (.cast .ulong (.var "gid")) (.var "n")) (MSLBlock.ofList inner) .nil, .returnStmt]
    let mkLane := fun tx => ({
      tid := { x := tx, y := 0, z := 0 }
      locals := initBuiltinLocal MSLLocals.empty "gid" .uint (gx0 * groupSize + tx, 0, 0)
      stmts := body
      halted := false } : MSLThreadState)
    have hthreads0 : g0.threads = [] ++ (List.range groupSize).map (fun d => mkLane (0 + d)) := by
      dsimp only [g0, initGroupState]
      rw [dim3_coords_1d groupSize, List.map_map, List.nil_append]
      apply List.map_congr_left
      intro tx _
      dsimp only [Function.comp, Nat.zero_add, mkLane, body]
      rw [← hbody, initThreadLocals_std k _ _ nIn hparams]
      dsimp only [groupDim]
      simp [Nat.zero_add]
    obtain ⟨gFinal, outMem1, hrunG, hin1, hout1, hsize1, hwords1, hlog1⟩ :=
      runGroup_guarded_lanes nIn len groupSize gx0 stepsInner inWords specWord inner hInner hlen64
        groupSize 0 fuelPerGroup g0 [] outMem outMem (by omega) hgx1Lt hfuel
        rfl rfl hbind0 rfl hin hout hsize
        (fun i _ => ⟨fun ⟨h1, h2⟩ => absurd h2 (by omega), fun _ => rfl⟩)
        (fun _ h => nomatch h) (fun _ h => nomatch h) hthreads0
    have hloLe : min len (gx0 * groupSize) ≤ min len ((gx0 + 1) * groupSize) := by
      have : gx0 * groupSize ≤ (gx0 + 1) * groupSize := Nat.mul_le_mul_right groupSize (by omega)
      omega
    have ⟨hcross, hpriorNext⟩ := checkCrossGroupDeviceLog_ok nIn (min len (gx0 * groupSize))
      (min len ((gx0 + 1) * groupSize)) hloLe priorLog hprior
      (gFinal.epochLog.filter isDeviceAccess) hlog1
    have hwordsNext : ∀ i < len, i < (gx0 + 1) * groupSize → outMem1.readU64Word? i = some (specWord i) := by
      intro i hi hiLt
      by_cases hge : gx0 * groupSize ≤ i
      · exact (hwords1 i hi).1 ⟨hge, hiLt⟩
      · rw [(hwords1 i hi).2 (fun ⟨h1, _⟩ => hge h1)]
        exact hwords i hi (by omega)
    obtain ⟨devBufsF, outMemF, hrest, houtF, hwordsF⟩ :=
      evalMSLKernelLoop_guarded_groups nIn len nGroups groupSize stepsInner fuelPerGroup k inWords specWord inner
        hparams hshared hbody hInner hlen64 hgrid32 hfuel
        rem (gx0 + 1) gFinal.deviceBuffers outMem1 ((gFinal.epochLog.filter isDeviceAccess) ++ priorLog)
        (by omega) (fun j hj => ⟨hin1 j hj, (hin j hj).2⟩) hout1 hsize1 hwordsNext hpriorNext
    refine ⟨devBufsF, outMemF, ?_, houtF, hwordsF⟩
    rw [hmapG]
    change (match runGroupWithDeviceLog fuelPerGroup g0 [] with
      | .ok (gFinal, groupDevLog) =>
        match checkCrossGroupDeviceLog priorLog groupDevLog with
        | .ok () =>
          evalMSLKernelLoop fuelPerGroup k gridDim groupDim constBufs [] [] gFinal.deviceBuffers
            (groupDevLog ++ priorLog) ((List.range rem).map (fun d => ({ x := (gx0 + 1) + d, y := 0, z := 0 } : Dim3)))
        | err => propagateErr err
      | err => propagateErr err) = .ok devBufsF
    rw [hrunG]
    dsimp only
    rw [hcross]
    exact hrest

theorem evalMSLKernel_guarded_1d (nIn len nGroups groupSize stepsInner fuelPerGroup : Nat)
    (k : MSLKernelDecl) (inBufs : List (Nat × ByteMemory))
    (inWords : Nat → List (BitVec 64)) (specWord : Nat → BitVec 64)
    (inner : List MSLStmt)
    (hparams : k.params = stdKernelParams nIn)
    (hshared : k.sharedDecls = [])
    (hbody : k.body = [MSLStmt.ifElse (.lt (.cast .ulong (.var "gid")) (.var "n")) (MSLBlock.ofList inner) .nil, .returnStmt])
    (hInner : LaneInnerSpec nIn len stepsInner inWords specWord inner)
    (hlen64 : len * 8 ≤ 2 ^ 64)
    (hlenCov : len ≤ nGroups * groupSize)
    (hgrid32 : nGroups * groupSize < 2 ^ 32)
    (hfuel : groupSize * (stepsInner + 2) ≤ fuelPerGroup)
    (hinLookup : ∀ j < nIn, inBufs.lookup j = some (ByteMemory.ofU64Words (inWords j)) ∧
      (inWords j).length = len)
    (hinOutNone : inBufs.lookup nIn = none) :
    ∃ (devBufsF : List (Nat × ByteMemory)) (outMemF : ByteMemory),
      evalMSLKernel fuelPerGroup k { x := nGroups, y := 1, z := 1 } { x := groupSize, y := 1, z := 1 }
        (inBufs ++ [(nIn, ByteMemory.zeros (len * 8))])
        [(nIn + 1, ByteMemory.ofU64Words [BitVec.ofNat 64 len])] [] [] = .ok devBufsF ∧
      devBufsF.lookup nIn = some outMemF ∧
      (∀ i < len, outMemF.readU64Word? i = some (specWord i)) := by
  let devBufs0 := inBufs ++ [(nIn, ByteMemory.zeros (len * 8))]
  have hin0 : ∀ j < nIn, devBufs0.lookup j = some (ByteMemory.ofU64Words (inWords j)) ∧
      (inWords j).length = len := by
    intro j hj
    rcases hinLookup j hj with ⟨hlk, hlenJ⟩
    refine ⟨?_, hlenJ⟩
    dsimp only [devBufs0]
    rw [List.lookup_append, hlk]
    rfl
  have hout0 : devBufs0.lookup nIn = some (ByteMemory.zeros (len * 8)) := by
    dsimp only [devBufs0]
    rw [List.lookup_append, hinOutNone]
    simp
  have hsize0 : (ByteMemory.zeros (len * 8)).bytes.size = len * 8 := by
    simp [ByteMemory.zeros]
  obtain ⟨devBufsF, outMemF, hloop, houtF, hwordsF⟩ :=
    evalMSLKernelLoop_guarded_groups nIn len nGroups groupSize stepsInner fuelPerGroup k inWords specWord inner
      hparams hshared hbody hInner hlen64 hgrid32 hfuel
      nGroups 0 devBufs0 (ByteMemory.zeros (len * 8)) [] (by omega)
      hin0 hout0 hsize0 (fun _ _ h => absurd h (by simp)) (fun _ h => nomatch h)
  refine ⟨devBufsF, outMemF, ?_, houtF, fun i hi => hwordsF i hi (by omega)⟩
  unfold evalMSLKernel
  rw [dim3_coords_1d nGroups]
  have hmap0 : (List.range nGroups).map (fun x => ({ x := x, y := 0, z := 0 } : Dim3)) =
      (List.range nGroups).map (fun d => ({ x := 0 + d, y := 0, z := 0 } : Dim3)) := by
    apply List.map_congr_left
    intro d _; simp
  rw [hmap0]
  exact hloop



theorem ev_add_ulong_log (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log0 log1 log2 : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log0 a =
      .ok { value := va, fields := [], locals := ls, log := log1 })
    (hb : evalExprWithCall callEval fuel g tid ls log1 b =
      .ok { value := vb, fields := [], locals := ls, log := log2 })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log0 (.add a b) =
      .ok { value := va + vb, fields := [], locals := ls, log := log2 } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb, finishBin, hta, htb, promoteMSLArithType_ulong]
  rfl

theorem ev_mul_ulong_log (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log0 log1 log2 : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log0 a =
      .ok { value := va, fields := [], locals := ls, log := log1 })
    (hb : evalExprWithCall callEval fuel g tid ls log1 b =
      .ok { value := vb, fields := [], locals := ls, log := log2 })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log0 (.mul a b) =
      .ok { value := va * vb, fields := [], locals := ls, log := log2 } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb, finishBin, hta, htb, promoteMSLArithType_ulong]
  rfl

theorem ev_logOr_bool (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (ba bb : Bool)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := if ba then 1#64 else 0#64, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := if bb then 1#64 else 0#64, fields := [], locals := ls, log := log }) :
    evalExprWithCall callEval fuel g tid ls log (.logOr a b) =
      .ok { value := if ba || bb then 1#64 else 0#64, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  cases ba
  · simp only [bindEval, hb]
    cases bb <;> rfl
  · simp only [bindEval]
    rfl

private theorem ev_std_in_log (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (name : String)
    (nIn k idx lo hi : Nat) (words : List (BitVec 64)) (idxExpr : MSLExpr)
    (hname : name = s!"in{k}")
    (hk : k < nIn) (hidxLt : idx < words.length) (hw64 : words.length < 2 ^ 64)
    (hbind : g.bindings = stdBindings nIn)
    (hdev : g.deviceBuffers.lookup k = some (ByteMemory.ofU64Words words))
    (hArr : ls.arrays = [])
    (hlog : ∀ a ∈ log, SimtLogInv nIn lo hi a)
    (hidx : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g tid ls log idxExpr =
      .ok { value := BitVec.ofNat 64 idx, fields := [], locals := ls, log := log }) :
    ∃ log',
      evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g tid ls log (.index name idxExpr) =
        .ok { value := words[idx], fields := [], locals := ls, log := log' } ∧
      inferExprType g ls (.index name idxExpr) = .ulong ∧
      (∀ a ∈ log', SimtLogInv nIn lo hi a) := by
  subst hname
  have harrK : ls.lookupArray? s!"in{k}" = none := by simp [MSLLocals.lookupArray?, hArr]
  have hbindK : g.bindings.lookup s!"in{k}" = some (.deviceBuf k true .ulong) := by
    rw [hbind]; exact stdBindings_lookup_in nIn k hk
  have ⟨log', hread, hlog', _⟩ := ev_index_dev_read kernelCallEval (effectiveCalleeFuel g) g tid ls
    log s!"in{k}" idxExpr k nIn lo hi idx words hidx hidxLt hw64 harrK hbindK hdev hk hlog
  refine ⟨log', hread, ?_, hlog'⟩
  simp only [inferExprType, harrK, hbindK]

private theorem ev_imm_ulong (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (bv : BitVec 64) :
    evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g tid ls log (.immU64 bv) =
      .ok { value := bv, fields := [], locals := ls, log := log } ∧
    inferExprType g ls (.immU64 bv) = .ulong := by
  refine ⟨?_, rfl⟩
  rw [evalExprWithCall]

private theorem infer_add_ulong (g : MSLGroupState) (ls : MSLLocals) (a b : MSLExpr)
    (ha : inferExprType g ls a = .ulong) (hb : inferExprType g ls b = .ulong) :
    inferExprType g ls (.add a b) = .ulong := by
  change promoteMSLArithType (inferExprType g ls a) (inferExprType g ls b) = .ulong
  rw [ha, hb]
  rfl

private theorem infer_mul_ulong (g : MSLGroupState) (ls : MSLLocals) (a b : MSLExpr)
    (ha : inferExprType g ls a = .ulong) (hb : inferExprType g ls b = .ulong) :
    inferExprType g ls (.mul a b) = .ulong := by
  change promoteMSLArithType (inferExprType g ls a) (inferExprType g ls b) = .ulong
  rw [ha, hb]
  rfl

theorem laneInner_mapScaleAdd (len : Nat) (scale bias : BitVec 64)
    (inWords : Nat → List (BitVec 64)) :
    LaneInnerSpec 1 len 1 inWords
      (fun cx =>
        if h : cx < (inWords 0).length then (inWords 0)[cx] * scale + bias else 0#64)
      [.indexAssign "out" (.var "gid")
        (.add (.mul (.index "in0" (.var "gid")) (.immU64 scale)) (.immU64 bias))] := by
  apply laneInner_storeOut
  intro g tid cx lo hcxLen hcx32 hlen64 _ _ _ hbind _ hin hlog
  let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
  have ⟨hlkGid, htyGid, hArr, _⟩ := initBuiltinLocal_gid_props cx hcx32
  have ⟨hvarGid, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog cx hcx32 hlkGid htyGid
  rcases hin 0 (by omega) with ⟨hdev0, hlen0⟩
  have hcx0 : cx < (inWords 0).length := by omega
  obtain ⟨log1, hin0, htin0, hlog1⟩ := ev_std_in_log g tid ls g.epochLog "in0" 1 0 cx lo cx
    (inWords 0) (.var "gid") rfl (by omega) hcx0 (by omega) hbind hdev0 hArr hlog hvarGid
  have ⟨hscale, htscale⟩ := ev_imm_ulong g tid ls log1 scale
  have hmul := ev_mul_ulong_log kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog log1 log1
    (.index "in0" (.var "gid")) (.immU64 scale) ((inWords 0)[cx]) scale hin0 hscale htin0 htscale
  have htmul := infer_mul_ulong g ls _ _ htin0 htscale
  have ⟨hbias, htbias⟩ := ev_imm_ulong g tid ls log1 bias
  have hadd := ev_add_ulong_log kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog log1 log1
    (.mul (.index "in0" (.var "gid")) (.immU64 scale)) (.immU64 bias)
    ((inWords 0)[cx] * scale) bias hmul hbias htmul htbias
  refine ⟨log1, ?_, hlog1⟩
  rw [dite_eq_left_of_eq_true (eq_true hcx0)]
  exact hadd

theorem laneInner_zipAdd (len : Nat) (inWords : Nat → List (BitVec 64)) :
    LaneInnerSpec 2 len 1 inWords
      (fun cx =>
        if h0 : cx < (inWords 0).length then
          if h1 : cx < (inWords 1).length then (inWords 0)[cx] + (inWords 1)[cx] else 0#64
        else 0#64)
      [.indexAssign "out" (.var "gid") (.add (.index "in0" (.var "gid")) (.index "in1" (.var "gid")))] := by
  apply laneInner_storeOut
  intro g tid cx lo hcxLen hcx32 hlen64 _ _ _ hbind _ hin hlog
  let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
  have ⟨hlkGid, htyGid, hArr, _⟩ := initBuiltinLocal_gid_props cx hcx32
  rcases hin 0 (by omega) with ⟨hdev0, hlen0⟩
  rcases hin 1 (by omega) with ⟨hdev1, hlen1⟩
  have hcx0 : cx < (inWords 0).length := by omega
  have hcx1 : cx < (inWords 1).length := by omega
  have ⟨hvarGid0, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog cx hcx32 hlkGid htyGid
  obtain ⟨log1, hin0, htin0, hlog1⟩ := ev_std_in_log g tid ls g.epochLog "in0" 2 0 cx lo cx
    (inWords 0) (.var "gid") rfl (by omega) hcx0 (by omega) hbind hdev0 hArr hlog hvarGid0
  have ⟨hvarGid1, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls log1 cx hcx32 hlkGid htyGid
  obtain ⟨log2, hin1, htin1, hlog2⟩ := ev_std_in_log g tid ls log1 "in1" 2 1 cx lo cx
    (inWords 1) (.var "gid") rfl (by omega) hcx1 (by omega) hbind hdev1 hArr hlog1 hvarGid1
  have hadd := ev_add_ulong_log kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog log1 log2
    (.index "in0" (.var "gid")) (.index "in1" (.var "gid")) ((inWords 0)[cx]) ((inWords 1)[cx])
    hin0 hin1 htin0 htin1
  refine ⟨log2, ?_, hlog2⟩
  rw [dite_eq_left_of_eq_true (eq_true hcx0), dite_eq_left_of_eq_true (eq_true hcx1)]
  exact hadd

theorem laneInner_zipMul (len : Nat) (inWords : Nat → List (BitVec 64)) :
    LaneInnerSpec 2 len 1 inWords
      (fun cx =>
        if h0 : cx < (inWords 0).length then
          if h1 : cx < (inWords 1).length then (inWords 0)[cx] * (inWords 1)[cx] else 0#64
        else 0#64)
      [.indexAssign "out" (.var "gid") (.mul (.index "in0" (.var "gid")) (.index "in1" (.var "gid")))] := by
  apply laneInner_storeOut
  intro g tid cx lo hcxLen hcx32 hlen64 _ _ _ hbind _ hin hlog
  let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
  have ⟨hlkGid, htyGid, hArr, _⟩ := initBuiltinLocal_gid_props cx hcx32
  rcases hin 0 (by omega) with ⟨hdev0, hlen0⟩
  rcases hin 1 (by omega) with ⟨hdev1, hlen1⟩
  have hcx0 : cx < (inWords 0).length := by omega
  have hcx1 : cx < (inWords 1).length := by omega
  have ⟨hvarGid0, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog cx hcx32 hlkGid htyGid
  obtain ⟨log1, hin0, htin0, hlog1⟩ := ev_std_in_log g tid ls g.epochLog "in0" 2 0 cx lo cx
    (inWords 0) (.var "gid") rfl (by omega) hcx0 (by omega) hbind hdev0 hArr hlog hvarGid0
  have ⟨hvarGid1, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls log1 cx hcx32 hlkGid htyGid
  obtain ⟨log2, hin1, htin1, hlog2⟩ := ev_std_in_log g tid ls log1 "in1" 2 1 cx lo cx
    (inWords 1) (.var "gid") rfl (by omega) hcx1 (by omega) hbind hdev1 hArr hlog1 hvarGid1
  have hmul := ev_mul_ulong_log kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog log1 log2
    (.index "in0" (.var "gid")) (.index "in1" (.var "gid")) ((inWords 0)[cx]) ((inWords 1)[cx])
    hin0 hin1 htin0 htin1
  refine ⟨log2, ?_, hlog2⟩
  rw [dite_eq_left_of_eq_true (eq_true hcx0), dite_eq_left_of_eq_true (eq_true hcx1)]
  exact hmul

theorem laneInner_saxpy (len : Nat) (alpha : BitVec 64) (inWords : Nat → List (BitVec 64)) :
    LaneInnerSpec 2 len 1 inWords
      (fun cx =>
        if h0 : cx < (inWords 0).length then
          if h1 : cx < (inWords 1).length then alpha * (inWords 0)[cx] + (inWords 1)[cx] else 0#64
        else 0#64)
      [.indexAssign "out" (.var "gid")
        (.add (.mul (.immU64 alpha) (.index "in0" (.var "gid"))) (.index "in1" (.var "gid")))] := by
  apply laneInner_storeOut
  intro g tid cx lo hcxLen hcx32 hlen64 _ _ _ hbind _ hin hlog
  let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
  have ⟨hlkGid, htyGid, hArr, _⟩ := initBuiltinLocal_gid_props cx hcx32
  rcases hin 0 (by omega) with ⟨hdev0, hlen0⟩
  rcases hin 1 (by omega) with ⟨hdev1, hlen1⟩
  have hcx0 : cx < (inWords 0).length := by omega
  have hcx1 : cx < (inWords 1).length := by omega
  have ⟨halpha, htalpha⟩ := ev_imm_ulong g tid ls g.epochLog alpha
  have ⟨hvarGid0, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog cx hcx32 hlkGid htyGid
  obtain ⟨log1, hin0, htin0, hlog1⟩ := ev_std_in_log g tid ls g.epochLog "in0" 2 0 cx lo cx
    (inWords 0) (.var "gid") rfl (by omega) hcx0 (by omega) hbind hdev0 hArr hlog hvarGid0
  have hmul := ev_mul_ulong_log kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog g.epochLog log1
    (.immU64 alpha) (.index "in0" (.var "gid")) alpha ((inWords 0)[cx]) halpha hin0 htalpha htin0
  have htmul := infer_mul_ulong g ls _ _ htalpha htin0
  have ⟨hvarGid1, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls log1 cx hcx32 hlkGid htyGid
  obtain ⟨log2, hin1, htin1, hlog2⟩ := ev_std_in_log g tid ls log1 "in1" 2 1 cx lo cx
    (inWords 1) (.var "gid") rfl (by omega) hcx1 (by omega) hbind hdev1 hArr hlog1 hvarGid1
  have hadd := ev_add_ulong_log kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog log1 log2
    (.mul (.immU64 alpha) (.index "in0" (.var "gid"))) (.index "in1" (.var "gid"))
    (alpha * (inWords 0)[cx]) ((inWords 1)[cx]) hmul hin1 htmul htin1
  refine ⟨log2, ?_, hlog2⟩
  rw [dite_eq_left_of_eq_true (eq_true hcx0), dite_eq_left_of_eq_true (eq_true hcx1)]
  exact hadd

theorem laneInner_stencil1D3Pt (len : Nat) (wL wC wR : BitVec 64)
    (inWords : Nat → List (BitVec 64)) :
    let i := MSLExpr.cast .ulong (.var "gid")
    let edge := MSLExpr.logOr (.eq i (.immU64 0#64)) (.ge (.add i (.immU64 1#64)) (.var "n"))
    let center := MSLExpr.index "in0" (.var "gid")
    let interior := MSLExpr.add (.add
      (.mul (.immU64 wL) (.index "in0" (.sub i (.immU64 1#64))))
      (.mul (.immU64 wC) center))
      (.mul (.immU64 wR) (.index "in0" (.add i (.immU64 1#64))))
    LaneInnerSpec 1 len 2 inWords
      (fun cx =>
        if cx == 0 || cx + 1 >= len then
          if h0 : cx < (inWords 0).length then (inWords 0)[cx] else 0#64
        else
          if hL : cx - 1 < (inWords 0).length then
            if hC : cx < (inWords 0).length then
              if hR : cx + 1 < (inWords 0).length then
                wL * (inWords 0)[cx - 1] + wC * (inWords 0)[cx] + wR * (inWords 0)[cx + 1]
              else 0#64
            else 0#64
          else 0#64)
      [.ifElse edge (.cons (.indexAssign "out" (.var "gid") center) .nil)
                    (.cons (.indexAssign "out" (.var "gid") interior) .nil)] := by
  let i := MSLExpr.cast .ulong (.var "gid")
  let edge := MSLExpr.logOr (.eq i (.immU64 0#64)) (.ge (.add i (.immU64 1#64)) (.var "n"))
  let center := MSLExpr.index "in0" (.var "gid")
  let interior := MSLExpr.add (.add
    (.mul (.immU64 wL) (.index "in0" (.sub i (.immU64 1#64))))
    (.mul (.immU64 wC) center))
    (.mul (.immU64 wR) (.index "in0" (.add i (.immU64 1#64))))
  apply laneInner_ifElse_storeOut 1 len inWords _ edge center interior (fun cx => cx == 0 || decide (len ≤ cx + 1))
  · intro g tid cx lo hcxLen hcx32 hlen64 _ _ _ hbind hconst _ hlog0
    let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
    have ⟨hlkGid, htyGid, _, hotherNone⟩ := initBuiltinLocal_gid_props cx hcx32
    have ⟨_, hcastGid⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog cx hcx32 hlkGid htyGid
    have hti : inferExprType g ls i = .ulong := rfl
    have ⟨hu0, htu0⟩ := ev_imm_ulong g tid ls g.epochLog 0#64
    have heq0 := ev_eq_ulong kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog
      i (.immU64 0#64) (BitVec.ofNat 64 cx) 0#64 hcastGid hu0 hti htu0
    have ⟨hu1, htu1⟩ := ev_imm_ulong g tid ls g.epochLog 1#64
    have hadd1 := ev_add_ulong kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog
      i (.immU64 1#64) (BitVec.ofNat 64 cx) 1#64 hcastGid hu1 hti htu1
    have htadd1 := infer_add_ulong g ls _ _ hti htu1
    have hnNone := hotherNone "n" (by decide)
    have hbindN : g.bindings.lookup "n" = some (.constantScalar 2 .ulong) := by
      rw [hbind]; exact stdBindings_lookup_n 1
    have hconstN : g.constantBuffers.lookup 2 = some (ByteMemory.ofU64Words [BitVec.ofNat 64 len]) := by
      rw [hconst]; simp
    have ⟨hevN, htyN⟩ := ev_var_const_ulong kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog
      "n" 2 (BitVec.ofNat 64 len) hnNone.1 hnNone.2 hbindN hconstN
    have hge := ev_ge_ulong kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog
      (.add i (.immU64 1#64)) (.var "n") (BitVec.ofNat 64 cx + 1#64) (BitVec.ofNat 64 len)
      hadd1 hevN htadd1 htyN
    have hor := ev_logOr_bool kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog
      (.eq i (.immU64 0#64)) (.ge (.add i (.immU64 1#64)) (.var "n"))
      (BitVec.ofNat 64 cx == 0#64) (BitVec.ule (BitVec.ofNat 64 len) (BitVec.ofNat 64 cx + 1#64))
      heq0 hge
    have hcxEq0 : (BitVec.ofNat 64 cx == 0#64) = (cx == 0) := by
      have hcx64 : cx < 2 ^ 64 := by omega
      cases cx with
      | zero => rfl
      | succ c =>
        have hneBv : BitVec.ofNat 64 (c + 1) ≠ 0#64 := by
          intro heqBv
          have htn : (BitVec.ofNat 64 (c + 1)).toNat = 0 := congrArg BitVec.toNat heqBv
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcx64] at htn
          omega
        exact beq_eq_false_iff_ne.mpr hneBv
    have hgeEq : BitVec.ule (BitVec.ofNat 64 len) (BitVec.ofNat 64 cx + 1#64) = decide (len ≤ cx + 1) := by
      have hlenLt64 : len < 2 ^ 64 := by omega
      have hcx1Lt64 : cx + 1 < 2 ^ 64 := by omega
      have hsum : BitVec.ofNat 64 cx + 1#64 = BitVec.ofNat 64 (cx + 1) := by
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cx < 2 ^ 64), Nat.mod_eq_of_lt hcx1Lt64]
      rw [hsum]
      simp [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlenLt64, Nat.mod_eq_of_lt hcx1Lt64]
    refine ⟨if (cx == 0 || decide (len ≤ cx + 1)) then 1#64 else 0#64, g.epochLog, ?_, ?_, id, hlog0⟩
    · rw [hcxEq0, hgeEq] at hor
      exact hor
    · cases (cx == 0 || decide (len ≤ cx + 1)) <;> rfl
  · intro g tid cx lo hcxLen hcx32 hlen64 _ _ _ hbind _ hin hlog
    let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
    have ⟨hlkGid, htyGid, hArr, _⟩ := initBuiltinLocal_gid_props cx hcx32
    rcases hin 0 (by omega) with ⟨hdev0, hlen0⟩
    have hcx0 : cx < (inWords 0).length := by omega
    by_cases hedge : (cx == 0 || decide (len ≤ cx + 1)) = true
    · simp only [hedge, ge_iff_le, ite_true, dite_eq_left_of_eq_true (eq_true hcx0)]
      have ⟨hvarGid, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog cx hcx32 hlkGid htyGid
      obtain ⟨log1, hinC, _, hlog1⟩ := ev_std_in_log g tid ls g.epochLog "in0" 1 0 cx lo cx
        (inWords 0) (.var "gid") rfl (by omega) hcx0 (by omega) hbind hdev0 hArr hlog hvarGid
      exact ⟨log1, hinC, hlog1⟩
    · have hedgeF : (cx == 0 || decide (len ≤ cx + 1)) = false := Bool.eq_false_iff.mpr hedge
      have hcxPos : 0 < cx := by
        cases cx with
        | zero => simp at hedgeF
        | succ c => omega
      have hcx1LtLen : cx + 1 < len := by
        rcases Bool.or_eq_false_iff.mp hedgeF with ⟨_, h2⟩
        simp only [decide_eq_false_iff_not] at h2
        omega
      have hL : cx - 1 < (inWords 0).length := by omega
      have hR : cx + 1 < (inWords 0).length := by omega
      simp only [hedgeF, ge_iff_le, Bool.false_eq_true, ite_false,
        dite_eq_left_of_eq_true (eq_true hL), dite_eq_left_of_eq_true (eq_true hcx0), dite_eq_left_of_eq_true (eq_true hR)]
      have hti : inferExprType g ls i = .ulong := rfl
      -- 1) wL * in0[i - 1]
      have ⟨hwL0, htwL⟩ := ev_imm_ulong g tid ls g.epochLog wL
      have ⟨_, hcast0⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog cx hcx32 hlkGid htyGid
      have ⟨hu1_0, htu1⟩ := ev_imm_ulong g tid ls g.epochLog 1#64
      have hsub1 := ev_sub_ulong kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog
        i (.immU64 1#64) (BitVec.ofNat 64 cx) 1#64 hcast0 hu1_0 hti htu1
      have hsubEq : BitVec.ofNat 64 cx - 1#64 = BitVec.ofNat 64 (cx - 1) := by
        apply BitVec.eq_of_toNat_eq
        have hcx64 : cx < 2 ^ 64 := by omega
        have hcxm64 : cx - 1 < 2 ^ 64 := by omega
        simp [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcx64, Nat.mod_eq_of_lt hcxm64]
        omega
      rw [hsubEq] at hsub1
      obtain ⟨log1, hinL, htinL, hlog1⟩ := ev_std_in_log g tid ls g.epochLog "in0" 1 0 (cx - 1) lo cx
        (inWords 0) (.sub i (.immU64 1#64)) rfl (by omega) hL (by omega) hbind hdev0 hArr hlog hsub1
      have hmulL := ev_mul_ulong_log kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog g.epochLog log1
        (.immU64 wL) (.index "in0" (.sub i (.immU64 1#64))) wL ((inWords 0)[cx - 1]) hwL0 hinL htwL htinL
      have htmulL := infer_mul_ulong g ls _ _ htwL htinL
      -- 2) wC * in0[gid]
      have ⟨hwC1, htwC⟩ := ev_imm_ulong g tid ls log1 wC
      have ⟨hvarGid1, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls log1 cx hcx32 hlkGid htyGid
      obtain ⟨log2, hinC, htinC, hlog2⟩ := ev_std_in_log g tid ls log1 "in0" 1 0 cx lo cx
        (inWords 0) (.var "gid") rfl (by omega) hcx0 (by omega) hbind hdev0 hArr hlog1 hvarGid1
      have hmulC := ev_mul_ulong_log kernelCallEval (effectiveCalleeFuel g) g tid ls log1 log1 log2
        (.immU64 wC) center wC ((inWords 0)[cx]) hwC1 hinC htwC htinC
      have htmulC := infer_mul_ulong g ls _ _ htwC htinC
      have haddLC := ev_add_ulong_log kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog log1 log2
        (.mul (.immU64 wL) (.index "in0" (.sub i (.immU64 1#64)))) (.mul (.immU64 wC) center)
        (wL * (inWords 0)[cx - 1]) (wC * (inWords 0)[cx]) hmulL hmulC htmulL htmulC
      have htaddLC := infer_add_ulong g ls _ _ htmulL htmulC
      -- 3) wR * in0[i + 1]
      have ⟨hwR2, htwR⟩ := ev_imm_ulong g tid ls log2 wR
      have ⟨_, hcast2⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls log2 cx hcx32 hlkGid htyGid
      have ⟨hu1_2, _⟩ := ev_imm_ulong g tid ls log2 1#64
      have hadd1 := ev_add_ulong kernelCallEval (effectiveCalleeFuel g) g tid ls log2
        i (.immU64 1#64) (BitVec.ofNat 64 cx) 1#64 hcast2 hu1_2 hti htu1
      have haddEq : BitVec.ofNat 64 cx + 1#64 = BitVec.ofNat 64 (cx + 1) := by
        apply BitVec.eq_of_toNat_eq
        have hcx64 : cx < 2 ^ 64 := by omega
        have hcxp64 : cx + 1 < 2 ^ 64 := by omega
        simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcx64, Nat.mod_eq_of_lt hcxp64]
      rw [haddEq] at hadd1
      obtain ⟨log3, hinR, htinR, hlog3⟩ := ev_std_in_log g tid ls log2 "in0" 1 0 (cx + 1) lo cx
        (inWords 0) (.add i (.immU64 1#64)) rfl (by omega) hR (by omega) hbind hdev0 hArr hlog2 hadd1
      have hmulR := ev_mul_ulong_log kernelCallEval (effectiveCalleeFuel g) g tid ls log2 log2 log3
        (.immU64 wR) (.index "in0" (.add i (.immU64 1#64))) wR ((inWords 0)[cx + 1]) hwR2 hinR htwR htinR
      have htmulR := infer_mul_ulong g ls _ _ htwR htinR
      have haddAll := ev_add_ulong_log kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog log2 log3
        (.add (.mul (.immU64 wL) (.index "in0" (.sub i (.immU64 1#64)))) (.mul (.immU64 wC) center))
        (.mul (.immU64 wR) (.index "in0" (.add i (.immU64 1#64))))
        (wL * (inWords 0)[cx - 1] + wC * (inWords 0)[cx]) (wR * (inWords 0)[cx + 1])
        haddLC hmulR htaddLC htmulR
      exact ⟨log3, haddAll, hlog3⟩



private theorem bv_and_63_lt (x : BitVec 64) : (x &&& 63#64).toNat < 64 := by
  have h : BitVec.ult (x &&& 63#64) 64#64 = true := by bv_decide
  simpa [BitVec.ult] using h

theorem ev_div_guarded_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList → MSLOutcome MSLEval) (fuel : Nat) (g : MSLGroupState)
    (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a = .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b = .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log
      (.select (.eq b (.immU64 0#64)) (.immU64 0#64) (.div a b)) =
      .ok { value := va / vb, fields := [], locals := ls, log := log } := by
  have hu0 : evalExprWithCall callEval fuel g tid ls log (.immU64 0#64) =
      .ok { value := 0#64, fields := [], locals := ls, log := log } := by
    rw [evalExprWithCall]
  have heq0 := ev_eq_ulong callEval fuel g tid ls log b (.immU64 0#64) vb 0#64 hb hu0 htb rfl
  cases hvb0 : (vb == 0#64)
  · exact (ev_select_false callEval fuel g tid ls log _ _ _ _ heq0 (by simp [hvb0])).trans
      (ev_div_ulong callEval fuel g tid ls log a b va vb ha hb hta htb hvb0)
  · have hv0 : vb = 0#64 := eq_of_beq hvb0
    subst hv0
    have hdiv0 : va / 0#64 = 0#64 := by bv_decide
    rw [hdiv0]
    exact (ev_select_true callEval fuel g tid ls log _ _ _ _ heq0 rfl).trans hu0

theorem ev_mod_guarded_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList → MSLOutcome MSLEval) (fuel : Nat) (g : MSLGroupState)
    (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a = .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b = .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log
      (.select (.eq b (.immU64 0#64)) a (.rem a b)) =
      .ok { value := va % vb, fields := [], locals := ls, log := log } := by
  have hu0 : evalExprWithCall callEval fuel g tid ls log (.immU64 0#64) =
      .ok { value := 0#64, fields := [], locals := ls, log := log } := by
    rw [evalExprWithCall]
  have heq0 := ev_eq_ulong callEval fuel g tid ls log b (.immU64 0#64) vb 0#64 hb hu0 htb rfl
  cases hvb0 : (vb == 0#64)
  · exact (ev_select_false callEval fuel g tid ls log _ _ _ _ heq0 (by simp [hvb0])).trans
      (ev_rem_ulong callEval fuel g tid ls log a b va vb ha hb hta htb hvb0)
  · have hv0 : vb = 0#64 := eq_of_beq hvb0
    subst hv0
    have hmod0 : va % 0#64 = va := by bv_decide
    rw [hmod0]
    exact (ev_select_true callEval fuel g tid ls log _ _ _ _ heq0 rfl).trans ha

theorem ev_shl_masked_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList → MSLOutcome MSLEval) (fuel : Nat) (g : MSLGroupState)
    (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a = .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b = .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log
      (.shl a (.bitAnd b (.immU64 63#64))) =
      .ok { value := va <<< (vb &&& 63#64).toNat, fields := [], locals := ls, log := log } := by
  have hu63 : evalExprWithCall callEval fuel g tid ls log (.immU64 63#64) =
      .ok { value := 63#64, fields := [], locals := ls, log := log } := by
    rw [evalExprWithCall]
  have hm := ev_bitand_ulong callEval fuel g tid ls log b (.immU64 63#64) vb 63#64 hb hu63 htb rfl
  exact ev_shl_ulong callEval fuel g tid ls log a _ va (vb &&& 63#64) ha hm hta (bv_and_63_lt vb)

theorem ev_shr_masked_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList → MSLOutcome MSLEval) (fuel : Nat) (g : MSLGroupState)
    (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a = .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b = .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log
      (.shr a (.bitAnd b (.immU64 63#64))) =
      .ok { value := va >>> (vb &&& 63#64).toNat, fields := [], locals := ls, log := log } := by
  have hu63 : evalExprWithCall callEval fuel g tid ls log (.immU64 63#64) =
      .ok { value := 63#64, fields := [], locals := ls, log := log } := by
    rw [evalExprWithCall]
  have hm := ev_bitand_ulong callEval fuel g tid ls log b (.immU64 63#64) vb 63#64 hb hu63 htb rfl
  exact ev_shr_ulong callEval fuel g tid ls log a _ va (vb &&& 63#64) ha hm hta (bv_and_63_lt vb)

theorem ev_sar_masked_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList → MSLOutcome MSLEval) (fuel : Nat) (g : MSLGroupState)
    (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a = .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b = .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log
      (.cast .ulong (.shr (.cast .long a) (.bitAnd b (.immU64 63#64)))) =
      .ok { value := BitVec.sshiftRight va (vb &&& 63#64).toNat, fields := [], locals := ls, log := log } := by
  have hu63 : evalExprWithCall callEval fuel g tid ls log (.immU64 63#64) =
      .ok { value := 63#64, fields := [], locals := ls, log := log } := by
    rw [evalExprWithCall]
  have hm := ev_bitand_ulong callEval fuel g tid ls log b (.immU64 63#64) vb 63#64 hb hu63 htb rfl
  have htm : inferExprType g ls (.bitAnd b (.immU64 63#64)) = .ulong := by
    change promoteMSLArithType (inferExprType g ls b) .ulong = .ulong
    rw [htb]
    rfl
  exact ev_sar_ulong callEval fuel g tid ls log a _ va (vb &&& 63#64) ha hm hta htm (bv_and_63_lt vb)

theorem ev_eor3_compound_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList → MSLOutcome MSLEval) (fuel : Nat) (g : MSLGroupState)
    (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a = .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b = .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log
      (.bitXor (.bitXor a (.shr b (.immU64 32#64))) (.bitAnd b (.immU64 0xffffffff#64))) =
      .ok { value := (va ^^^ (vb >>> (32#64).toNat)) ^^^ (vb &&& 0xffffffff#64), fields := [], locals := ls, log := log } := by
  have hu32 : evalExprWithCall callEval fuel g tid ls log (.immU64 32#64) =
      .ok { value := 32#64, fields := [], locals := ls, log := log } := by
    rw [evalExprWithCall]
  have huff : evalExprWithCall callEval fuel g tid ls log (.immU64 0xffffffff#64) =
      .ok { value := 0xffffffff#64, fields := [], locals := ls, log := log } := by
    rw [evalExprWithCall]
  have hshr := ev_shr_ulong callEval fuel g tid ls log b (.immU64 32#64) vb 32#64 hb hu32 htb (by decide)
  have htshr : inferExprType g ls (.shr b (.immU64 32#64)) = .ulong := by
    change promoteMSLArithType (inferExprType g ls b) .ulong = .ulong
    rw [htb]
    rfl
  have hxor1 := ev_bitxor_ulong callEval fuel g tid ls log a _ va (vb >>> (32#64).toNat) ha hshr hta htshr
  have htxor1 : inferExprType g ls (.bitXor a (.shr b (.immU64 32#64))) = .ulong := by
    change promoteMSLArithType (inferExprType g ls a) (inferExprType g ls (.shr b (.immU64 32#64))) = .ulong
    rw [hta, htshr]
    rfl
  have hand := ev_bitand_ulong callEval fuel g tid ls log b (.immU64 0xffffffff#64) vb 0xffffffff#64 hb huff htb rfl
  have htand : inferExprType g ls (.bitAnd b (.immU64 0xffffffff#64)) = .ulong := by
    change promoteMSLArithType (inferExprType g ls b) .ulong = .ulong
    rw [htb]
    rfl
  exact ev_bitxor_ulong callEval fuel g tid ls log _ _ _ _ hxor1 hand htxor1 htand

theorem ev_eq_cast_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList → MSLOutcome MSLEval) (fuel : Nat) (g : MSLGroupState)
    (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a = .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b = .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.cast .ulong (.eq a b)) =
      .ok { value := if va == vb then 1#64 else 0#64, fields := [], locals := ls, log := log } := by
  have hcmp := ev_eq_ulong callEval fuel g tid ls log a b va vb ha hb hta htb
  have hcast := ev_cast_ulong_from_bool callEval fuel g tid ls log (.eq a b) _ hcmp rfl
  cases h : (va == vb)
  · simp only [h] at hcast ⊢; exact hcast
  · simp only [h] at hcast ⊢; exact hcast

theorem ev_lt_cast_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList → MSLOutcome MSLEval) (fuel : Nat) (g : MSLGroupState)
    (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a = .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b = .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.cast .ulong (.lt a b)) =
      .ok { value := if BitVec.ult va vb then 1#64 else 0#64, fields := [], locals := ls, log := log } := by
  have hcmp := ev_lt_ulong callEval fuel g tid ls log a b va vb ha hb hta htb
  have hcast := ev_cast_ulong_from_bool callEval fuel g tid ls log (.lt a b) _ hcmp rfl
  cases h : BitVec.ult va vb
  · simp only [h] at hcast ⊢; exact hcast
  · simp only [h] at hcast ⊢; exact hcast

theorem ev_le_cast_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList → MSLOutcome MSLEval) (fuel : Nat) (g : MSLGroupState)
    (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a = .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b = .ok { value := vb, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.cast .ulong (.le a b)) =
      .ok { value := if BitVec.ule va vb then 1#64 else 0#64, fields := [], locals := ls, log := log } := by
  have hcmp := ev_le_ulong callEval fuel g tid ls log a b va vb ha hb hta htb
  have hcast := ev_cast_ulong_from_bool callEval fuel g tid ls log (.le a b) _ hcmp rfl
  cases h : BitVec.ule va vb
  · simp only [h] at hcast ⊢; exact hcast
  · simp only [h] at hcast ⊢; exact hcast



theorem ev_neg_zero_sub_ulong
    (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess)
    (a : MSLExpr) (va : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a = .ok { value := va, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.sub (.immU64 0#64) a) =
      .ok { value := 0#64 - va, fields := [], locals := ls, log := log } := by
  have hu0 : evalExprWithCall callEval fuel g tid ls log (.immU64 0#64) =
      .ok { value := 0#64, fields := [], locals := ls, log := log } := by
    rw [evalExprWithCall]
  exact ev_sub_ulong callEval fuel g tid ls log (.immU64 0#64) a 0#64 va hu0 ha rfl hta

theorem ev_fma_compound_ulong
    (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess)
    (a b c : MSLExpr) (va vb vc : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a = .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b = .ok { value := vb, fields := [], locals := ls, log := log })
    (hc : evalExprWithCall callEval fuel g tid ls log c = .ok { value := vc, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) (htc : inferExprType g ls c = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.add (.mul a b) c) =
      .ok { value := va * vb + vc, fields := [], locals := ls, log := log } := by
  have hmul := ev_mul_ulong callEval fuel g tid ls log a b va vb ha hb hta htb
  have htmul : inferExprType g ls (.mul a b) = .ulong := by
    change promoteMSLArithType (inferExprType g ls a) (inferExprType g ls b) = .ulong
    rw [hta, htb]; rfl
  exact ev_add_ulong callEval fuel g tid ls log (.mul a b) c (va * vb) vc hmul hc htmul htc

theorem ev_select_ne_zero
    (callEval : Nat → MSLGroupState → Dim3 → MSLLocals → List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals) (log : List MSLAccess)
    (c t f : MSLExpr) (vc vt vf : BitVec 64)
    (hc : evalExprWithCall callEval fuel g tid ls log c = .ok { value := vc, fields := [], locals := ls, log := log })
    (ht : evalExprWithCall callEval fuel g tid ls log t = .ok { value := vt, fields := [], locals := ls, log := log })
    (hf : evalExprWithCall callEval fuel g tid ls log f = .ok { value := vf, fields := [], locals := ls, log := log })
    (htc : inferExprType g ls c = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.select (.ne c (.immU64 0#64)) t f) =
      .ok { value := if vc != 0#64 then vt else vf, fields := [], locals := ls, log := log } := by
  have hu0 : evalExprWithCall callEval fuel g tid ls log (.immU64 0#64) =
      .ok { value := 0#64, fields := [], locals := ls, log := log } := by
    rw [evalExprWithCall]
  have hne0 := ev_ne_ulong callEval fuel g tid ls log c (.immU64 0#64) vc 0#64 hc hu0 htc rfl
  cases hnz : (vc != 0#64)
  · simp only [Bool.false_eq_true, ite_false]
    exact (ev_select_false callEval fuel g tid ls log _ t f _ hne0 (by simp [hnz])).trans hf
  · simp only [ite_true]
    exact (ev_select_true callEval fuel g tid ls log _ t f _ hne0 (by simp [hnz])).trans ht

theorem infer_bin_ulong (g : MSLGroupState) (ls : MSLLocals) (a b : MSLExpr)
    (ha : inferExprType g ls a = .ulong) (hb : inferExprType g ls b = .ulong) :
    inferExprType g ls (.add a b) = .ulong ∧
    inferExprType g ls (.sub a b) = .ulong ∧
    inferExprType g ls (.mul a b) = .ulong ∧
    inferExprType g ls (.div a b) = .ulong ∧
    inferExprType g ls (.rem a b) = .ulong ∧
    inferExprType g ls (.bitAnd a b) = .ulong ∧
    inferExprType g ls (.bitOr a b) = .ulong ∧
    inferExprType g ls (.bitXor a b) = .ulong ∧
    inferExprType g ls (.shl a b) = .ulong ∧
    inferExprType g ls (.shr a b) = .ulong := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    change promoteMSLArithType (inferExprType g ls a) (inferExprType g ls b) = .ulong
    rw [ha, hb]
    rfl

theorem infer_select_ulong (g : MSLGroupState) (ls : MSLLocals) (c t f : MSLExpr)
    (ht : inferExprType g ls t = .ulong) :
    inferExprType g ls (.select c t f) = .ulong := ht



theorem shl_bv_eq_u64 (a b : UInt64) :
    a.toBitVec <<< (b.toBitVec &&& 63#64).toNat = (a <<< b).toBitVec := by
  have h : (a <<< b).toBitVec = a.toBitVec <<< (b.toBitVec % 64#64) := rfl
  rw [h, ← BitVec.shiftLeft_eq']
  generalize a.toBitVec = x; generalize b.toBitVec = y
  bv_decide

theorem shr_bv_eq_u64 (a b : UInt64) :
    a.toBitVec >>> (b.toBitVec &&& 63#64).toNat = (a >>> b).toBitVec := by
  have h : (a >>> b).toBitVec = a.toBitVec >>> (b.toBitVec % 64#64) := rfl
  rw [h, ← BitVec.ushiftRight_eq']
  generalize a.toBitVec = x; generalize b.toBitVec = y
  bv_decide

theorem sar_bv_eq_u64 (x y : UInt64) :
    BitVec.sshiftRight x.toBitVec (y.toBitVec &&& 63#64).toNat =
      (let sh := y &&& 63
       let signBit := (x >>> 63) &&& 1
       let shifted := x >>> sh
       if signBit != 0 && sh != 0 then shifted ||| (0xffffffffffffffff <<< (64 - sh)) else shifted).toBitVec := by
  have hs : x.toBitVec.sshiftRight (y.toBitVec &&& 63#64).toNat =
      BitVec.sshiftRight' x.toBitVec (y.toBitVec &&& 63#64) := rfl
  rw [hs]
  dsimp only
  split
  · rename_i hcond
    have hc : (((x.toBitVec >>> 63#64) &&& 1#64) != 0#64 && (y.toBitVec &&& 63#64) != 0#64) = true := hcond
    change BitVec.sshiftRight' x.toBitVec (y.toBitVec &&& 63#64) =
      (x.toBitVec >>> ((y.toBitVec &&& 63#64) % 64#64)) |||
        (0xffffffffffffffff#64 <<< ((64#64 - (y.toBitVec &&& 63#64)) % 64#64))
    bv_decide
  · rename_i hcond
    have hc : ¬(((x.toBitVec >>> 63#64) &&& 1#64) != 0#64 && (y.toBitVec &&& 63#64) != 0#64) = true := hcond
    change BitVec.sshiftRight' x.toBitVec (y.toBitVec &&& 63#64) =
      x.toBitVec >>> ((y.toBitVec &&& 63#64) % 64#64)
    bv_decide

theorem eq_bv_iff (x y : UInt64) : (x.toBitVec == y.toBitVec) = (x == y) := by
  cases h : (x == y)
  · cases h2 : (x.toBitVec == y.toBitVec)
    · rfl
    · rw [UInt64.eq_of_toBitVec_eq (eq_of_beq h2), beq_self_eq_true] at h; cases h
  · rw [eq_of_beq h]; simp

theorem u64_ofNat_toBitVec (cx : Nat) (h : cx < 2 ^ 32) :
    cx.toUInt64.toBitVec = BitVec.ofNat 64 cx := by
  have h64 : cx < 2 ^ 64 := by omega
  apply BitVec.eq_of_toNat_eq
  simp [UInt64.toNat_ofNat', Nat.mod_eq_of_lt h64]

theorem laneInnerSpec_congr {nIn len stepsInner : Nat}
    {inWords : Nat → List (BitVec 64)} {sw1 sw2 : Nat → BitVec 64}
    {inner : List MSLStmt}
    (hspec : LaneInnerSpec nIn len stepsInner inWords sw1 inner)
    (heq : ∀ cx < len, sw1 cx = sw2 cx) :
    LaneInnerSpec nIn len stepsInner inWords sw2 inner := by
  intro g done todo cx tx lo f outMem hcxLen hcx32 hlen64 hlo hf
    hstr hfn hbind hconst hin hout hsize hlog hdone hthreads
  obtain ⟨f', thH, g', outMem', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
    hspec g done todo cx tx lo f outMem hcxLen hcx32 hlen64 hlo hf
      hstr hfn hbind hconst hin hout hsize hlog hdone hthreads
  rw [heq cx hcxLen] at h12
  exact ⟨f', thH, g', outMem', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩


theorem eor3_bv_eq_u64 (a b : UInt64) :
    (a.toBitVec ^^^ (b.toBitVec >>> (32#64).toNat)) ^^^ (b.toBitVec &&& 0xffffffff#64) =
      ((a ^^^ (b >>> 32)) ^^^ (b &&& 0xffffffff)).toBitVec := by
  have h : ((a ^^^ (b >>> 32)) ^^^ (b &&& 0xffffffff)).toBitVec =
      (a.toBitVec ^^^ (b.toBitVec >>> 32#64)) ^^^ (b.toBitVec &&& 0xffffffff#64) := rfl
  rw [h]; generalize a.toBitVec = x; generalize b.toBitVec = y
  bv_decide

end LeanNative.Backend.MetalAst
