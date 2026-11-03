import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Backend.MLIRGPU

namespace LeanNative.Backend.Hybrid

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend.MLIRGPU

/-- Apple A15 / Apple7 Metal 3.0 unified-memory zero-copy dispatch floor (`262144` elements = 2 MB `uint64_t`),
    where the 4-core Apple7 GPU amortizes the ~60 µs Metal command buffer dispatch over 2P+4E NEON cores. -/
def metalDispatchFloor : Nat := 262144

/-- Apple Silicon / iOS unified-memory VM page size (`16384` B = 16 KB) required for zero-copy `MTLBuffer`s. -/
def metalPageBytes : Nat := 16384

/-- Pure scalar Apple7 Metal 3.0 unified-memory zero-copy vs NEON CPU cost router gate (`verifyBackendChoice`). -/
@[inline]
def verifyBackendChoice
    (tripCount : UInt64)
    (isControlHeavy hasMetalGpu isPageAligned chosenBackend : UInt8) : UInt8 :=
  if (chosenBackend == 1 && isControlHeavy == 0 && hasMetalGpu == 1 && isPageAligned == 1 && 262144 ≤ tripCount) ||
     (chosenBackend == 0 && (isControlHeavy == 1 || hasMetalGpu == 0 || isPageAligned == 0 || tripCount < 262144)) then 1 else 0

/-- Memory transfer / coherency strategy between host CPU and accelerator device. -/
inductive TransferMode where
  | unifiedMemoryZeroCopy   -- Grace-Blackwell / Apple Silicon coherent unified memory + async prefetch
  | pinnedAsyncHostToDevice -- Explicit pinned H2D/D2H async stream transfer
  | hostOnlyFallback        -- Pure CPU execution (no device transfer)
  deriving Repr, DecidableEq, Inhabited, BEq

namespace TransferMode

def toString : TransferMode → String
  | .unifiedMemoryZeroCopy   => "UnifiedMemoryZeroCopy"
  | .pinnedAsyncHostToDevice => "PinnedAsyncHostToDevice"
  | .hostOnlyFallback        => "HostOnlyFallback"

instance : ToString TransferMode := ⟨toString⟩

end TransferMode

/-- Unified 4-target hardware accelerator placement for `lean-native` × `turbo-lean`. -/
inductive ComputeTarget where
  | cpuSimd         -- Local AVX2 / ARM64 NEON zero-boxing SIMD
  | gpuCudaPtx      -- Local or remote NVIDIA CUDA PTX 8.0 (`sm_80`/`sm_89`/`sm_90`/`sm_121`)
  | gpuMetal        -- Apple Silicon Metal Shading Language
  | tpuXlaStableHLO -- Google Cloud TPU v5e/v6e XLA StableHLO / Pallas (128x128 MXU + 128x8 VPU)
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Canonical 5-target search backend enum unifying CPU SIMD, CUDA GB10, Apple Metal,
    remote Cloud TPU, and FPGA LSC2 across `lean-native` and `turbo-lean`. -/
inductive SearchBackend where
  | CpuSimd
  | CudaGb10
  | Metal
  | TpuRemote
  | FpgaLsc2
  deriving Repr, DecidableEq, Inhabited, BEq

namespace SearchBackend
def toString : SearchBackend → String
  | .CpuSimd   => "cpu_simd"
  | .CudaGb10  => "cuda_gb10"
  | .Metal     => "metal"
  | .TpuRemote => "tpu_remote"
  | .FpgaLsc2  => "fpga_lsc2"
instance : ToString SearchBackend := ⟨toString⟩

def ofComputeTarget : ComputeTarget → SearchBackend
  | .cpuSimd         => .CpuSimd
  | .gpuCudaPtx      => .CudaGb10
  | .gpuMetal        => .Metal
  | .tpuXlaStableHLO => .TpuRemote

def toComputeTarget : SearchBackend → ComputeTarget
  | .CpuSimd   => .cpuSimd
  | .CudaGb10  => .gpuCudaPtx
  | .Metal     => .gpuMetal
  | .TpuRemote => .tpuXlaStableHLO
  | .FpgaLsc2  => .cpuSimd
end SearchBackend

namespace ComputeTarget
def toString : ComputeTarget → String
  | .cpuSimd         => "cpu_simd"
  | .gpuCudaPtx      => "gpu_cuda_ptx"
  | .gpuMetal        => "gpu_metal"
  | .tpuXlaStableHLO => "tpu_xla_stablehlo"
instance : ToString ComputeTarget := ⟨toString⟩
end ComputeTarget

/-- Select the optimal hardware target given workload shape and available hardware backends. -/
def selectOptimalComputeTarget
    (tripCount : Nat)
    (isMatrixContraction : Bool)
    (is256BitWorkload : Bool)
    (isControlHeavy : Bool)
    (hasTpu : Bool)
    (hasCudaGpu : Bool)
    (hasMetalGpu : Bool := false) : ComputeTarget :=
  if isControlHeavy || tripCount < 4096 then
    .cpuSimd
  else if isMatrixContraction && hasTpu then
    .tpuXlaStableHLO
  else if is256BitWorkload && hasCudaGpu then
    .gpuCudaPtx
  else if hasTpu then
    .tpuXlaStableHLO
  else if hasCudaGpu then
    .gpuCudaPtx
  else if hasMetalGpu then
    let ctrlFlag : UInt8 := if isControlHeavy then 1 else 0
    if verifyBackendChoice tripCount.toUInt64 ctrlFlag 1 1 1 == 1 then .gpuMetal else .cpuSimd
  else
    .cpuSimd

/-- Select the certified Apple A15 (`iPhone 13 mini`) compute target (`.gpuMetal` vs `.cpuSimd`),
    gated by `verifyBackendChoice` (`leannative_verify_backend_choice`). -/
def selectAppleA15Target (tripCount : Nat) (isControlHeavy hasMetalGpu isPageAligned : Bool) : ComputeTarget :=
  let ctrlFlag : UInt8 := if isControlHeavy then 1 else 0
  let metalFlag : UInt8 := if hasMetalGpu then 1 else 0
  let alignFlag : UInt8 := if isPageAligned then 1 else 0
  if verifyBackendChoice tripCount.toUInt64 ctrlFlag metalFlag alignFlag 1 == 1 then
    .gpuMetal
  else
    .cpuSimd

/-- Select the canonical 5-target `SearchBackend` given workload shape and available accelerators. -/
def selectOptimalSearchBackend
    (tripCount : Nat)
    (isMatrixContraction : Bool)
    (is256BitWorkload : Bool)
    (isControlHeavy : Bool)
    (hasTpu : Bool)
    (hasCudaGpu : Bool)
    (hasMetalGpu : Bool := false)
    (hasFpgaLsc2 : Bool := false) : SearchBackend :=
  if isControlHeavy || tripCount < 4096 then
    .CpuSimd
  else if hasFpgaLsc2 && is256BitWorkload then
    .FpgaLsc2
  else
    SearchBackend.ofComputeTarget
      (selectOptimalComputeTarget tripCount isMatrixContraction is256BitWorkload isControlHeavy hasTpu hasCudaGpu hasMetalGpu)

/-- Classify an `LNIRDecl` and select its optimal hardware target based on `extractParForRegions`,
    256-bit parameter/return types, and GPU compatibility analysis. -/
def classifyDeclComputeTarget
    (d : LNIRDecl)
    (tripCount : Nat)
    (hasTpu hasCudaGpu : Bool)
    (hasMetalGpu : Bool := false) : ComputeTarget :=
  let regions := extractParForRegions d.body
  let isMatrixContraction :=
    d.name == "matmul_tiled_u64" || (d.name.splitOn "matmul").length > 1 ||
    regions.any (fun (_, _, _, _, k) =>
      match k with
      | .dotProduct => d.name == "matmul_tiled_u64"
      | _ => false)
  let is256BitWorkload :=
    d.retTy.is256Bit ||
    d.params.any (fun p => p.ty == .u256 || p.ty == .i256 || p.ty == .storageMap || p.ty.is256Bit) ||
    regions.any (fun (_, _, _, elemTy, _) => elemTy == .u256 || elemTy == .i256 || elemTy.is256Bit)
  let isControlHeavy := !(analyzeGpuCompatibility d).1
  selectOptimalComputeTarget tripCount isMatrixContraction is256BitWorkload isControlHeavy hasTpu hasCudaGpu hasMetalGpu

/-!
# Typed host-device buffers, strided address spans, launch geometry, and operational RC lifecycle

Formal dispatch and `HeapState` reference-count contract shared across CPU+PTX, CPU+Metal,
and CPU+StableHLO hybrid execution plans.
-/

/-- Direction of an explicit host-device transfer. -/
inductive TransferDirection where
  | hostToDevice
  | deviceToHost
  | inOut
  deriving Repr, DecidableEq, Inhabited

/-- Whether a buffer binding writes to device/host memory (`deviceToHost` or `inOut`). -/
def isMutableTransfer : TransferDirection → Bool
  | .hostToDevice => false
  | .deviceToHost | .inOut => true

/-- Three-dimensional launch extent. Every component is a number of threads or blocks. -/
structure Dim3 where
  x : Nat
  y : Nat
  z : Nat
  deriving Repr, DecidableEq, Inhabited

namespace Dim3

/-- Product of the three extents. -/
def volume (d : Dim3) : Nat := d.x * d.y * d.z

/-- Every component is nonzero, so a linearized index has a unique coordinate triple. -/
def allPositive (d : Dim3) : Prop := d.x ≠ 0 ∧ d.y ≠ 0 ∧ d.z ≠ 0

end Dim3

/-- Ownership state of one host allocation relative to an in-flight device stream. -/
inductive RcOwnership where
  | borrowedByDevice
  | pinnedHostRef
  | uniqueOutBuffer
  deriving Repr, DecidableEq, Inhabited

/-- One host allocation participating in a hybrid launch. -/
structure DeviceBufferDesc where
  name : String
  elemBytes : Nat
  numElems : Nat
  byteStride : Nat
  baseAlign : Nat
  direction : TransferDirection
  zeroCopy : Bool
  rc : Nat
  baseAddr : Nat
  ownership : RcOwnership
  bufId : Nat := 0
  deriving Repr, DecidableEq, Inhabited

namespace DeviceBufferDesc

/-- Exact physical byte span of a strided buffer:
    `0` when `numElems = 0`, else `(numElems - 1) * byteStride + elemBytes`. -/
def byteSpan (b : DeviceBufferDesc) : Nat :=
  if b.numElems = 0 then 0 else (b.numElems - 1) * b.byteStride + b.elemBytes

/-- Physical byte address of byte `byteOff` inside element `elemIdx`. -/
def elemByteAddr (b : DeviceBufferDesc) (elemIdx byteOff : Nat) : Nat :=
  b.baseAddr + elemIdx * b.byteStride + byteOff

/-- Checked physical byte span bounded by 64-bit unsigned address space (`< 2^64`). -/
def checkedBytes (b : DeviceBufferDesc) : Option Nat :=
  if b.elemBytes = 0 ∨ b.byteStride < b.elemBytes then none
  else if b.numElems = 0 then some 0
  else if b.byteStride = 0 then none
  else if b.numElems - 1 ≤ (2 ^ 64 - 1) / b.byteStride then
    let lastOff := (b.numElems - 1) * b.byteStride
    if lastOff + b.elemBytes < 2 ^ 64 then some (lastOff + b.elemBytes) else none
  else none

/-- Half-open device address upper bound `baseAddr + checkedBytes`. -/
def addressEnd (b : DeviceBufferDesc) : Nat :=
  b.baseAddr + b.checkedBytes.getD 0

/-- Geometry required before any transfer or zero-copy binding is admitted:
    positive alignment and element size, `elemBytes ≤ byteStride`, aligned stride and base address,
    non-overflowing strided `checkedBytes` (`< 2^64`), and no 64-bit pointer wrap (`baseAddr + span ≤ 2^64`). -/
def geometryOk (b : DeviceBufferDesc) : Prop :=
  b.baseAlign ≠ 0 ∧ b.elemBytes ≠ 0 ∧ b.elemBytes ≤ b.byteStride ∧
  b.byteStride % b.baseAlign = 0 ∧ b.baseAddr % b.baseAlign = 0 ∧
  ∃ span, b.checkedBytes = some span ∧ b.baseAddr + span ≤ 2 ^ 64

/-- Target-aware geometry: enforces 16 KB (`16384` B) page alignment on `.gpuMetal` zero-copy buffers. -/
def targetGeometryOk (target : ComputeTarget) (b : DeviceBufferDesc) : Prop :=
  b.geometryOk ∧ (target = .gpuMetal ∧ b.zeroCopy = true → b.baseAddr % metalPageBytes = 0)

/-- A read-only input may be borrowed; every written buffer must be uniquely owned (`rc = 1`). -/
def ownershipOk (b : DeviceBufferDesc) : Prop :=
  match b.direction with
  | .hostToDevice => b.rc ≥ 1 ∧ (b.ownership = .borrowedByDevice ∨ b.ownership = .pinnedHostRef)
  | .deviceToHost => b.rc = 1 ∧ b.ownership = .uniqueOutBuffer
  | .inOut => b.rc = 1 ∧ b.ownership = .uniqueOutBuffer

/-- Canonical `TransferMode` selected by `b.zeroCopy`. -/
def transferMode (b : DeviceBufferDesc) : TransferMode :=
  if b.zeroCopy then .unifiedMemoryZeroCopy else .pinnedAsyncHostToDevice

end DeviceBufferDesc

/-- Boolean form of one buffer's geometry precondition. -/
def bufferGeometryOk (b : DeviceBufferDesc) : Bool :=
  b.baseAlign != 0 && b.elemBytes != 0 && b.elemBytes ≤ b.byteStride &&
  b.byteStride % b.baseAlign == 0 && b.baseAddr % b.baseAlign == 0 &&
  match b.checkedBytes with
  | none => false
  | some span => b.baseAddr + span ≤ 2 ^ 64

/-- Target-aware boolean buffer geometry precondition (`16384` B page alignment for `.gpuMetal` zero-copy). -/
def targetBufferGeometryOk (target : ComputeTarget) (b : DeviceBufferDesc) : Bool :=
  bufferGeometryOk b && (!(target == .gpuMetal && b.zeroCopy) || b.baseAddr % metalPageBytes == 0)

/-- Boolean form of one buffer's ownership precondition. -/
def bufferOwnershipOk (b : DeviceBufferDesc) : Bool :=
  match b.direction with
  | .hostToDevice => b.rc != 0 && (b.ownership == .borrowedByDevice || b.ownership == .pinnedHostRef)
  | .deviceToHost => b.rc == 1 && b.ownership == .uniqueOutBuffer
  | .inOut => b.rc == 1 && b.ownership == .uniqueOutBuffer

/-- Two half-open address intervals do not overlap. -/
def addressIntervalsDisjoint (a0 a1 b0 b1 : Nat) : Prop :=
  a1 ≤ b0 ∨ b1 ≤ a0

/-- Two distinct kernel argument slots are alias-safe iff BOTH are read-only `.hostToDevice` inputs,
    or they carry distinct slot names with strictly disjoint strided address intervals.
    Distinct argument slots may NEVER alias a mutable `.deviceToHost` or `.inOut` buffer. -/
def disjointBuffers (a b : DeviceBufferDesc) : Prop :=
  (a.direction = .hostToDevice ∧ b.direction = .hostToDevice) ∨
  (a.name ≠ b.name ∧ addressIntervalsDisjoint a.baseAddr a.addressEnd b.baseAddr b.addressEnd)

/-- Pairwise alias checker aligned with `disjointBuffers`. -/
def bufferAliasPairOk (a b : DeviceBufferDesc) : Bool :=
  (a.direction == .hostToDevice && b.direction == .hostToDevice) ||
  (a.name != b.name && (a.addressEnd ≤ b.baseAddr || b.addressEnd ≤ a.baseAddr))

/-- Boolean form of the pairwise output-alias precondition across distinct parameter slots. -/
def bufferAliasOk : List DeviceBufferDesc → Bool
  | [] => true
  | a :: rest => (rest.all fun b => bufferAliasPairOk a b) && bufferAliasOk rest

/-- Operational failure modes of `pinBufferStep -> launchKernelStep -> syncDeviceStep -> releaseBufferStep`. -/
inductive HybridLifecycleError where
  | bufferNotFound (bufId : Nat)
  | invalidGeometry (name : String)
  | nonExclusiveMutable (bufId : Nat)
  | zeroCopyMismatch (name : String)
  | unpinnedDeviceAccess (bufId : Nat)
  | heapError (err : UBError)
  deriving Repr, DecidableEq, Inhabited

/-- Whether `mode` agrees with `b.zeroCopy` (`hostOnlyFallback` accepts both). -/
def transferModeCompatible (mode : TransferMode) (b : DeviceBufferDesc) : Bool :=
  match mode with
  | .unifiedMemoryZeroCopy => b.zeroCopy
  | .pinnedAsyncHostToDevice => !b.zeroCopy
  | .hostOnlyFallback => true

/-- Step 1 (`pin`): verify buffer geometry, `TransferMode` coherency, live `ArrayBuffer` membership (`rc ≥ 1`),
    and unique ownership (`rc = 1`) for mutable buffers before acquiring a transfer pin via `HeapState.incRefBuf`. -/
def pinBufferStep (mode : TransferMode) (b : DeviceBufferDesc) (st : HeapState) :
    Except HybridLifecycleError HeapState :=
  if !bufferGeometryOk b then
    .error (.invalidGeometry b.name)
  else if !transferModeCompatible mode b then
    .error (.zeroCopyMismatch b.name)
  else
    match st.findBuffer b.bufId with
    | none => .error (.bufferNotFound b.bufId)
    | some buf =>
      if isMutableTransfer b.direction && st.getBufRefCount buf != 1 then
        .error (.nonExclusiveMutable b.bufId)
      else
        match st.incRefBuf b.bufId 1 with
        | .ok st' => .ok st'
        | .error err => .error (.heapError err)

/-- Step 2 (`launch`): require `TransferMode` coherency and an active transfer pin (`rc ≥ 2`) in `HeapState`. -/
def launchKernelStep (mode : TransferMode) (b : DeviceBufferDesc) (st : HeapState) :
    Except HybridLifecycleError HeapState :=
  if !transferModeCompatible mode b then
    .error (.zeroCopyMismatch b.name)
  else
    match st.findBuffer b.bufId with
    | none => .error (.bufferNotFound b.bufId)
    | some buf =>
      if st.getBufRefCount buf < 2 then
        .error (.unpinnedDeviceAccess b.bufId)
      else
        .ok st

/-- Step 3 (`sync`): verify the buffer remains live with an active pin (`rc ≥ 2`) through stream completion. -/
def syncDeviceStep (mode : TransferMode) (b : DeviceBufferDesc) (st : HeapState) :
    Except HybridLifecycleError HeapState :=
  if !transferModeCompatible mode b then
    .error (.zeroCopyMismatch b.name)
  else
    match st.findBuffer b.bufId with
    | none => .error (.bufferNotFound b.bufId)
    | some buf =>
      if st.getBufRefCount buf < 2 then
        .error (.unpinnedDeviceAccess b.bufId)
      else
        .ok st

/-- Step 4 (`release`): require an active pin (`rc ≥ 2`) so `HeapState.decRefBuf` never frees the host buffer,
    restoring the exact pre-pin reference count (`rc₀ ≥ 1`, and `exclusive = true` when `rc₀ = 1`). -/
def releaseBufferStep (mode : TransferMode) (b : DeviceBufferDesc) (st : HeapState) :
    Except HybridLifecycleError HeapState :=
  if !transferModeCompatible mode b then
    .error (.zeroCopyMismatch b.name)
  else
    match st.findBuffer b.bufId with
    | none => .error (.bufferNotFound b.bufId)
    | some buf =>
      if st.getBufRefCount buf < 2 then
        .error (.unpinnedDeviceAccess b.bufId)
      else
        match st.decRefBuf b.bufId 1 with
        | .ok st' => .ok st'
        | .error err => .error (.heapError err)

/-- Complete 4-step operational transfer & kernel RC lifecycle (`pin -> launch -> sync -> release`) on `HeapState`. -/
def execHybridTransferLifecycle (mode : TransferMode) (b : DeviceBufferDesc) (st : HeapState) :
    Except HybridLifecycleError HeapState := do
  let stPinned ← pinBufferStep mode b st
  let stLaunched ← launchKernelStep mode b stPinned
  let stSynced ← syncDeviceStep mode b stLaunched
  releaseBufferStep mode b stSynced

/-- Operational RC conservation predicate over `HeapState`: for any heap containing `buf₀` at `b.bufId`
    with `getBufRefCount = b.rc` and geometry `bufferGeometryOk b = true`, `execHybridTransferLifecycle`
    succeeds, elevates `rc` to `b.rc + 1 ≥ 2` while active, and restores `b.rc` (with `exclusive = true`
    and `b.rc = 1` on mutable outputs) upon release. -/
def rcConserved (b : DeviceBufferDesc) : Prop :=
  bufferGeometryOk b = true →
  ∀ (st : HeapState) (buf₀ : ArrayBuffer),
    st.findBuffer b.bufId = some buf₀ →
    st.getBufRefCount buf₀ = b.rc →
    ∃ stPinned stFinal bufPinned bufFinal,
      pinBufferStep b.transferMode b st = .ok stPinned ∧
      execHybridTransferLifecycle b.transferMode b st = .ok stFinal ∧
      stPinned.findBuffer b.bufId = some bufPinned ∧
      stFinal.findBuffer b.bufId = some bufFinal ∧
      stPinned.getBufRefCount bufPinned = b.rc + 1 ∧
      2 ≤ stPinned.getBufRefCount bufPinned ∧
      stFinal.getBufRefCount bufFinal = b.rc ∧
      bufFinal.data = buf₀.data ∧
      (isMutableTransfer b.direction = true → bufFinal.exclusive = true ∧ b.rc = 1)

/-- Launch request checked by `validateHybridDispatch`. -/
structure HybridLaunchRequest where
  kernelName : String
  target : ComputeTarget
  workloadElems : Nat
  maxThreadsPerBlock : Nat
  gridDim : Dim3
  blockDim : Dim3
  buffers : List DeviceBufferDesc
  tailGuarded : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Accepted launch plan. Its fields are exactly the validated request fields. -/
structure HybridDispatchPlan where
  kernelName : String
  target : ComputeTarget
  workloadElems : Nat
  gridThreads : Nat
  buffers : List DeviceBufferDesc
  tailGuarded : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Total threads launched by the grid. -/
def gridThreadsOf (req : HybridLaunchRequest) : Nat :=
  req.gridDim.volume * req.blockDim.volume

/-- Global thread id `(block, lane)` is below the launched thread count. -/
def globalThreadId (req : HybridLaunchRequest) (block lane : Nat) : Nat :=
  block * req.blockDim.volume + lane

/-- The tail guard `gid < workloadElems` covers every element exactly through the workload bound. -/
def tailGuardCovers (req : HybridLaunchRequest) : Prop :=
  req.tailGuarded ∧ req.workloadElems ≤ gridThreadsOf req ∧
  ∀ gid, gid < req.workloadElems → gid < gridThreadsOf req

/-- Grid geometry is nonzero and every block fits the device limit. -/
def validLaunchGeometry (req : HybridLaunchRequest) : Prop :=
  req.gridDim.allPositive ∧ req.blockDim.allPositive ∧
  req.blockDim.volume ≤ req.maxThreadsPerBlock ∧
  (req.tailGuarded ∧ req.workloadElems ≤ gridThreadsOf req ∨
    ¬ req.tailGuarded ∧ gridThreadsOf req = req.workloadElems)

/-- Every distinct pair of buffers in the launch schedule satisfies `disjointBuffers`. -/
def buffersDisjoint : List DeviceBufferDesc → Prop
  | [] => True
  | a :: rest => (∀ b ∈ rest, disjointBuffers a b) ∧ buffersDisjoint rest

/-- Every buffer satisfies target-aware geometry and direction-based RC ownership. -/
def buffersOwned (target : ComputeTarget) : List DeviceBufferDesc → Prop
  | [] => True
  | b :: rest => b.targetGeometryOk target ∧ b.ownershipOk ∧ buffersOwned target rest

/-- Why a hybrid launch was rejected. -/
inductive HybridDispatchError where
  | zeroGrid
  | blockTooLarge
  | incompleteCoverage
  | bufferGeometry
  | ownership
  | aliasedOutput
  deriving Repr, DecidableEq, Inhabited

/-- Boolean form of the grid precondition. -/
def launchGeometryOk (req : HybridLaunchRequest) : Bool :=
  req.gridDim.x != 0 && req.gridDim.y != 0 && req.gridDim.z != 0 &&
  req.blockDim.x != 0 && req.blockDim.y != 0 && req.blockDim.z != 0 &&
  req.blockDim.volume ≤ req.maxThreadsPerBlock &&
  ((req.tailGuarded && req.workloadElems ≤ gridThreadsOf req) ||
    (!req.tailGuarded && gridThreadsOf req == req.workloadElems))

/-- Admit a launch only when geometry, coverage, target alignment, ownership, and output aliasing all hold. -/
def validateHybridDispatch (req : HybridLaunchRequest) : Except HybridDispatchError HybridDispatchPlan :=
  if !launchGeometryOk req &&
      (req.gridDim.x = 0 || req.gridDim.y = 0 || req.gridDim.z = 0 ||
        req.blockDim.x = 0 || req.blockDim.y = 0 || req.blockDim.z = 0) then
    .error .zeroGrid
  else if !launchGeometryOk req && req.maxThreadsPerBlock < req.blockDim.volume then
    .error .blockTooLarge
  else if !launchGeometryOk req then
    .error .incompleteCoverage
  else if req.buffers.any fun b => !targetBufferGeometryOk req.target b then
    .error .bufferGeometry
  else if req.buffers.any fun b => !bufferOwnershipOk b then
    .error .ownership
  else if !bufferAliasOk req.buffers then
    .error .aliasedOutput
  else
    .ok {
      kernelName := req.kernelName
      target := req.target
      workloadElems := req.workloadElems
      gridThreads := gridThreadsOf req
      buffers := req.buffers
      tailGuarded := req.tailGuarded
    }

/-- Soundness invariant guaranteed for every accepted `HybridDispatchPlan`. -/
def hybridDispatchSound (req : HybridLaunchRequest) (plan : HybridDispatchPlan) : Prop :=
  validLaunchGeometry req ∧ buffersOwned req.target req.buffers ∧ buffersDisjoint req.buffers ∧
  plan.target = req.target ∧
  plan.gridThreads = gridThreadsOf req ∧ plan.workloadElems = req.workloadElems ∧
  plan.buffers = req.buffers ∧
  (req.tailGuarded → req.workloadElems ≤ plan.gridThreads) ∧
  (∀ gid, req.tailGuarded → gid < req.workloadElems →
    ∃ block lane, block < req.gridDim.volume ∧ lane < req.blockDim.volume ∧
      globalThreadId req block lane = gid) ∧
  (∀ block lane, block < req.gridDim.volume → lane < req.blockDim.volume →
    globalThreadId req block lane < plan.gridThreads) ∧
  (∀ b ∈ req.buffers, rcConserved b)

/-- Build and validate a canonical `HybridDispatchPlan` for an `LNIRDecl` via `validateHybridDispatch`. -/
def buildHybridDispatchPlan
    (target : ComputeTarget)
    (minGpuElements : Nat)
    (preferUnifiedMemory : Bool)
    (d : LNIRDecl) : Except HybridDispatchError HybridDispatchPlan :=
  let effElems :=
    if target == .gpuMetal then Nat.max (Nat.max minGpuElements metalDispatchFloor) 256
    else Nat.max minGpuElements 256
  let numInputs : Nat :=
    match extractParForRegions d.body with
    | [(_, _, _, .i64, .zipAdd)] | [(_, _, _, .i64, .zipMul)]
    | [(_, _, _, .i64, .dotProduct)] | [(_, _, _, .i64, .saxpy _)] => 2
    | _ => 1
  let rawSpan := effElems * 8
  let pageAlignedSpan := ((rawSpan + metalPageBytes - 1) / metalPageBytes) * metalPageBytes
  let slotSpan := Nat.max metalPageBytes pageAlignedSpan
  let zeroCopy := target == .gpuMetal || preferUnifiedMemory
  let inOwnership : RcOwnership := if zeroCopy then .pinnedHostRef else .borrowedByDevice
  let inputs : List DeviceBufferDesc := (List.range numInputs).map fun idx => {
    name := s!"in{idx}"
    elemBytes := 8
    numElems := effElems
    byteStride := 8
    baseAlign := 8
    direction := .hostToDevice
    zeroCopy := zeroCopy
    rc := 1
    baseAddr := (idx + 1) * slotSpan
    ownership := inOwnership
    bufId := idx
  }
  let outElems :=
    match extractParForRegions d.body with
    | [(_, _, _, .i64, .dotProduct)] => 1
    | _ => effElems
  let output : DeviceBufferDesc := {
    name := "out"
    elemBytes := 8
    numElems := outElems
    byteStride := 8
    baseAlign := 8
    direction := .deviceToHost
    zeroCopy := zeroCopy
    rc := 1
    baseAddr := (numInputs + 1) * slotSpan
    ownership := .uniqueOutBuffer
    bufId := numInputs
  }
  let gridBlocks := (effElems + 255) / 256
  validateHybridDispatch {
    kernelName := s!"lean_native_hybrid_{d.name}"
    target := target
    workloadElems := effElems
    maxThreadsPerBlock := 1024
    gridDim := { x := Nat.max 1 gridBlocks, y := 1, z := 1 }
    blockDim := { x := 256, y := 1, z := 1 }
    buffers := inputs ++ [output]
    tailGuarded := true
  }

/-!
# Module partitioning and validated host dispatch glue emission
-/

/-- Per-declaration host-to-device / unified-memory transfer and synchronization schedule item. -/
structure TransferAction where
  declName             : String
  bufferVars           : List VarId
  mode                 : TransferMode
  minElements          : Nat
  requiresHostCowCheck : Bool
  syncPoint            : String
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Complete hybrid CPU/GPU partitioning plan for an `LNIRModule`. -/
structure HybridPartitionPlan where
  moduleName       : String
  gpuDecls         : List LNIRDecl
  cpuOnlyDecls     : List LNIRDecl
  minGpuElements   : Nat := 65536
  transferSchedule : List TransferAction
  diagnostics      : List (String × List String) := []
  deriving Repr, Inhabited, BEq

/-- Collect all buffer/pointer parameter `VarId`s in an `LNIRDecl`. -/
def collectBufferParams (d : LNIRDecl) : List VarId :=
  d.params.foldl (fun acc p =>
    match p.ty with
    | .sarray _ | .rawPtr _ => acc ++ [p.id]
    | _ => acc
  ) []

/-- Check whether an `LNIRCode` performs a host-side COW exclusivity check (`sarrayEnsureExclusive`). -/
partial def hasCowCheck (code : LNIRCode) : Bool :=
  match code with
  | .letBind _ _ (.sarrayEnsureExclusive _ _) _ => true
  | .letBind _ _ _ k => hasCowCheck k
  | .rawStore _ _ _ _ k => hasCowCheck k
  | .incRef _ _ k => hasCowCheck k
  | .decRef _ _ k => hasCowCheck k
  | .ite _ t e => hasCowCheck t || hasCowCheck e
  | .seqFor _ _ _ _ _ _ s k => hasCowCheck s || hasCowCheck k
  | .parFor _ _ _ _ _ k => hasCowCheck k
  | .ret _ => false
  | .unreachable => false

/-- Partition an `LNIRModule` into GPU-offloadable declarations (`gpuDecls`),
    CPU-only declarations (`cpuOnlyDecls`), and an explicit `transferSchedule`
    gated by `analyzeGpuCompatibility` AND `buildHybridDispatchPlan` (`validateHybridDispatch`). -/
def partitionModule (m : LNIRModule) (minGpuElements : Nat := 65536)
    (preferUnifiedMemory : Bool := true) : HybridPartitionPlan :=
  let mode : TransferMode :=
    if preferUnifiedMemory then .unifiedMemoryZeroCopy else .pinnedAsyncHostToDevice
  let (gpuDecls, cpuOnlyDecls, schedule, diags) :=
    m.decls.foldl (fun (gAcc, cAcc, sAcc, dAcc) d =>
      let (ok, reasons) := analyzeGpuCompatibility d
      let loweringErrors := match extractParForRegions d.body with
        | [(_, _, _, .i64, kernel)] => match kernel with
          | .customScalar _ _ _ => ["customScalar PTX lowering is unsupported"]
          | _ => []
        | _ => ["hybrid dispatch requires one i64 parFor region"]
      let dispatchErrors := match buildHybridDispatchPlan .gpuCudaPtx minGpuElements preferUnifiedMemory d with
        | .ok _ => []
        | .error err => [s!"validateHybridDispatch rejected plan: {repr err}"]
      let allErrors := reasons ++ loweringErrors ++ dispatchErrors
      if ok && allErrors.isEmpty then
        let action : TransferAction := {
          declName             := d.name
          bufferVars           := collectBufferParams d
          mode                 := mode
          minElements          := minGpuElements
          requiresHostCowCheck := true || hasCowCheck d.body
          syncPoint            := s!"cuStreamSynchronize(stream_{d.name})"
        }
        (gAcc ++ [d], cAcc, sAcc ++ [action], dAcc)
      else
        (gAcc, cAcc ++ [d], sAcc, dAcc ++ [(d.name, allErrors)])
    ) ([], [], [], [])
  {
    moduleName       := m.moduleName
    gpuDecls         := gpuDecls
    cpuOnlyDecls     := cpuOnlyDecls
    minGpuElements   := minGpuElements
    transferSchedule := schedule
    diagnostics      := diags
  }

/-- Emit C host dispatch glue for a single GPU-partitioned declaration, gated by `buildHybridDispatchPlan`
    and enforcing runtime 64-bit byte-overflow checks, `lean_is_exclusive` (`m_rc == 1`) output COW exclusivity,
    and strict output/input pointer range disjointness before GPU or CPU execution. -/
def emitDeclHostGlue (minGpuElements : Nat) (actionOpt : Option TransferAction) (d : LNIRDecl) : String :=
  let preferUnified := match actionOpt with
    | some act => act.mode != .pinnedAsyncHostToDevice
    | none => true
  match buildHybridDispatchPlan .gpuCudaPtx minGpuElements preferUnified d with
  | .error err =>
    s!"#error \"validateHybridDispatch failed for {d.name}: {repr err}\""
  | .ok vplan =>
    let modeComment := match actionOpt with
      | some act =>
        let cow := act.requiresHostCowCheck
        s!"/* TransferMode: {act.mode}, minElements: {act.minElements}, " ++
          s!"gridThreads: {vplan.gridThreads}, COW-exclusivity-check: {cow}, " ++
          s!"sync: {act.syncPoint} */"
      | none =>
        s!"/* TransferMode: UnifiedMemoryZeroCopy, minElements: {minGpuElements}, " ++
          s!"gridThreads: {vplan.gridThreads} */"
    let mkGlue (sig nullChk sizeVar : String) (numBufs : Nat) (outIsScalar : Bool)
        (inPtrs : List String) (gpuCall cpuFallback : String) : String :=
      let outCapGuard :=
        if outIsScalar then "if (out->m_size == 0) return -1;"
        else s!"if (out->m_size < n) return -1;"
      let outBytesExpr := if outIsScalar then "sizeof(uint64_t)" else "bytes"
      let aliasChecks := String.intercalate "\n" (inPtrs.map fun p =>
        s!"    if (!lean_native_ranges_disjoint(out->m_data, {outBytesExpr}, {p}->m_data, bytes)) return -1;")
      String.intercalate "\n" [
        s!"int lean_native_hybrid_dispatch_{d.name}({sig}) \{",
        s!"    {modeComment}",
        s!"    if ({nullChk}) return -1;",
        "    if (!lean_native_sarray_is_exclusive(out)) return -1;",
        s!"    size_t n = {sizeVar}->m_size;",
        s!"    {outCapGuard}",
        s!"    if (n > SIZE_MAX / (sizeof(uint64_t) * {numBufs}ULL)) return -1;",
        "    size_t bytes = n * sizeof(uint64_t);",
        aliasChecks,
        s!"    if (n >= {minGpuElements}ULL && lean_native_gpu_available() && lean_native_gpu_has_headroom(bytes * {numBufs}ULL)) \{",
        s!"{gpuCall}",
        "        if (rc == 0) return 0;",
        "    }",
        s!"{cpuFallback}",
        "    return 0;",
        "}"
      ]
    let cForHeader : List String := [
      "    for (size_t i = 0;",
      "         i < n;",
      "         ++i) {"
    ]
    match extractParForRegions d.body with
    | [(_, _, _, .i64, .mapScaleAdd scale bias)] =>
      let sig := "lean_native_sarray_u64* out, const lean_native_sarray_u64* in0"
      let gpuCall :=
        "        int rc = lean_native_hybrid_map_scale_add_u64(\n" ++
        s!"            out->m_data, in0->m_data, (uint64_t){scale}ULL, (uint64_t){bias}ULL, n);"
      let cpuFallback := String.intercalate "\n" (cForHeader ++ [
        s!"        out->m_data[i] = in0->m_data[i] * (uint64_t){scale}ULL + (uint64_t){bias}ULL;",
        "    }"
      ])
      mkGlue sig "!out || !in0" "in0" 2 false ["in0"] gpuCall cpuFallback
    | [(_, _, _, .i64, .zipAdd)] =>
      let sig :=
        "lean_native_sarray_u64* out, const lean_native_sarray_u64* in0, " ++
        "const lean_native_sarray_u64* in1"
      let nullChk := "!out || !in0 || !in1 || in1->m_size < in0->m_size"
      let gpuCall := "        int rc = lean_native_hybrid_zip_add_u64(out->m_data, in0->m_data, in1->m_data, n);"
      let cpuFallback := String.intercalate "\n" (cForHeader ++ [
        "        out->m_data[i] = in0->m_data[i] + in1->m_data[i];",
        "    }"
      ])
      mkGlue sig nullChk "in0" 3 false ["in0", "in1"] gpuCall cpuFallback
    | [(_, _, _, .i64, .zipMul)] =>
      let sig :=
        "lean_native_sarray_u64* out, const lean_native_sarray_u64* in0, " ++
        "const lean_native_sarray_u64* in1"
      let nullChk := "!out || !in0 || !in1 || in1->m_size < in0->m_size"
      let gpuCall := String.intercalate "\n" [
        "        void* args[4] = {",
        "            (void*)&out->m_data, (void*)&in0->m_data, (void*)&in1->m_data, (void*)&n",
        "        };",
        "        int rc = lean_native_launch_ptx_kernel(\"lean_native_kernel_zip_mul\", args, n);"
      ]
      let cpuFallback := String.intercalate "\n" (cForHeader ++ [
        "        out->m_data[i] = in0->m_data[i] * in1->m_data[i];",
        "    }"
      ])
      mkGlue sig nullChk "in0" 3 false ["in0", "in1"] gpuCall cpuFallback
    | [(_, _, _, .i64, .dotProduct)] =>
      let sig :=
        "lean_native_sarray_u64* out, const lean_native_sarray_u64* in0, " ++
        "const lean_native_sarray_u64* in1"
      let nullChk := "!out || !in0 || !in1 || out->m_size == 0 || in1->m_size < in0->m_size"
      let gpuCall :=
        "        int rc = lean_native_hybrid_dot_product_u64(&out->m_data[0], in0->m_data, in1->m_data, n);"
      let cpuFallback :=
        "    lean_native_cpu_dot_product_u64(&out->m_data[0], in0->m_data, in1->m_data, n);"
      mkGlue sig nullChk "in0" 2 true ["in0", "in1"] gpuCall cpuFallback
    | [(_, _, _, .i64, .saxpy alphaBits)] =>
      let sig :=
        "lean_native_sarray_u64* out, const lean_native_sarray_u64* x, " ++
        "const lean_native_sarray_u64* y"
      let nullChk := "!out || !x || !y || y->m_size < x->m_size"
      let gpuCall :=
        "        int rc = lean_native_hybrid_saxpy_u64(\n" ++
        s!"            out->m_data, x->m_data, y->m_data, (uint64_t){alphaBits}ULL, n);"
      let cpuFallback := String.intercalate "\n" (cForHeader ++ [
        s!"        out->m_data[i] = (uint64_t){alphaBits}ULL * x->m_data[i] + y->m_data[i];",
        "    }"
      ])
      mkGlue sig nullChk "x" 3 false ["x", "y"] gpuCall cpuFallback
    | [(_, _, _, .i64, .stencil1D3Pt wLeft wCenter wRight)] =>
      let sig := "lean_native_sarray_u64* out, const lean_native_sarray_u64* in0"
      let gpuCall :=
        "        int rc = lean_native_hybrid_stencil1d_u64(\n" ++
        s!"            out->m_data, in0->m_data, (uint64_t){wLeft}ULL, " ++
        s!"(uint64_t){wCenter}ULL, (uint64_t){wRight}ULL, n);"
      let cpuFallback := String.intercalate "\n" (cForHeader ++ [
        "        if (i == 0 || i + 1 >= n) {",
        "            out->m_data[i] = in0->m_data[i];",
        "        } else {",
        s!"            out->m_data[i] = in0->m_data[i - 1] * {wLeft}ULL +",
        s!"                in0->m_data[i] * {wCenter}ULL + in0->m_data[i + 1] * {wRight}ULL;",
        "        }",
        "    }"
      ])
      mkGlue sig "!out || !in0" "in0" 2 false ["in0"] gpuCall cpuFallback
    | _ => s!"#error \"unsupported hybrid dispatch for {d.name}\""

/-- Generate C/LLVM host dispatch glue (`emitHybridHostGlue`) from a `HybridPartitionPlan`.
    Every emitted kernel wrapper is validated through `buildHybridDispatchPlan` (`validateHybridDispatch`)
    and emits runtime COW (`lean_is_exclusive`), 64-bit byte-overflow, and output/input alias guards. -/
def emitHybridHostGlue (plan : HybridPartitionPlan) : String :=
  let header := String.intercalate "\n" [
    "/*",
    s!" * LeanNative Hybrid CPU/GPU Host Dispatch Glue for Module: {plan.moduleName}",
    s!" * Adaptive GPU Offload Threshold: minGpuElements = {plan.minGpuElements}",
    s!" * GPU-Partitioned Declarations ({plan.gpuDecls.length}): " ++
      String.intercalate ", " (plan.gpuDecls.map (·.name)),
    s!" * CPU-Only Declarations ({plan.cpuOnlyDecls.length}): " ++
      String.intercalate ", " (plan.cpuOnlyDecls.map (·.name)),
    " */",
    "#include \"lean_native_runtime.h\"",
    "#include <stddef.h>",
    "#include <stdint.h>",
    "",
    s!"#ifndef LEAN_NATIVE_MIN_GPU_ELEMENTS",
    s!"#define LEAN_NATIVE_MIN_GPU_ELEMENTS {plan.minGpuElements}ULL",
    "#endif",
    "#ifndef lean_native_sarray_is_exclusive",
    "#define lean_native_sarray_is_exclusive(arr) (lean_is_exclusive((lean_object*)(arr)))",
    "#endif",
    "static inline int lean_native_ranges_disjoint(const void* out_ptr, size_t out_bytes, const void* in_ptr, size_t in_bytes) {",
    "    uintptr_t out_data = (uintptr_t)out_ptr;",
    "    uintptr_t in_data = (uintptr_t)in_ptr;",
    "    if (out_data > UINTPTR_MAX - out_bytes || in_data > UINTPTR_MAX - in_bytes) return 0;",
    "    return (out_data + out_bytes <= in_data || in_data + in_bytes <= out_data) ? 1 : 0;",
    "}"
  ]

  let scheduleSummary :=
    if plan.transferSchedule.isEmpty then
      "/* No GPU transfer schedule entries (all declarations CPU-only). */"
    else
      let lines := plan.transferSchedule.map fun act =>
        let bufs := String.intercalate "," (act.bufferVars.map fun v => s!"%v{v}")
        let cow := act.requiresHostCowCheck
        s!" *   - {act.declName}: buffers=[{bufs}] mode={act.mode} " ++
          s!"minElements={act.minElements} cowCheck={cow} sync={act.syncPoint}"
      "/*\n * Transfer Schedule:\n" ++ String.intercalate "\n" lines ++ "\n */"

  let declGlues := plan.gpuDecls.map fun d =>
    let actOpt := plan.transferSchedule.find? (fun a => a.declName == d.name)
    emitDeclHostGlue plan.minGpuElements actOpt d

  String.intercalate "\n\n" ([header, scheduleSummary] ++ declGlues) ++ "\n"

/-- Explicit Metal 3.0 buffer binding contract for a generated compute kernel. -/
structure MetalKernelBindingSpec where
  kernelName       : String
  inputBufferNames : List String
  outputBufferName : String
  scalarF16Name?   : Option String := none
  lenParamName     : String := "n"
  elemBytes        : Nat := 8
  deriving Repr, DecidableEq, Inhabited

namespace MetalKernelBindingSpec

def numInputs (s : MetalKernelBindingSpec) : Nat := s.inputBufferNames.length

def outBufferIdx (s : MetalKernelBindingSpec) : Nat := s.numInputs

def scalarF16BufferIdx? (s : MetalKernelBindingSpec) : Option Nat :=
  s.scalarF16Name?.map (fun _ => s.numInputs + 1)

def nBufferIdx (s : MetalKernelBindingSpec) : Nat :=
  match s.scalarF16Name? with
  | some _ => s.numInputs + 2
  | none   => s.numInputs + 1

end MetalKernelBindingSpec

/-- Canonical binding contract for `lean_native_kernel_saxpy_f16`:
    `x -> buffer(0)`, `y -> buffer(1)`, `out -> buffer(2)`, `alpha -> buffer(3)`, `n -> buffer(4)`. -/
def saxpyF16MetalBindingSpec : MetalKernelBindingSpec := {
  kernelName       := "lean_native_kernel_saxpy_f16"
  inputBufferNames := ["x", "y"]
  outputBufferName := "out"
  scalarF16Name?   := some "alpha"
  lenParamName     := "n"
  elemBytes        := 2
}

/-- Derive the exact `MetalKernelBindingSpec` for an `LNIRDecl` matching `emitMetalDeclKernel`. -/
def declMetalBindingSpec (d : LNIRDecl) : MetalKernelBindingSpec :=
  let fnName := s!"lean_native_metal_decl_{d.name}"
  if d.name == "dot_product_u64" then
    { kernelName := fnName, inputBufferNames := ["in0", "in1"], outputBufferName := "out_lo", lenParamName := "n", elemBytes := 8 }
  else if d.name == "matmul_tiled_u64" then
    { kernelName := fnName, inputBufferNames := ["A", "B"], outputBufferName := "C", lenParamName := "dim", elemBytes := 8 }
  else
    match extractParForRegions d.body with
    | [(_, _, _, .i64, .saxpy _)] =>
      { kernelName := fnName, inputBufferNames := ["x", "y"], outputBufferName := "out", lenParamName := "n", elemBytes := 8 }
    | [(_, _, _, .i64, .mapScaleAdd _ _)] | [(_, _, _, .i64, .stencil1D3Pt _ _ _)] =>
      { kernelName := fnName, inputBufferNames := ["in0"], outputBufferName := "out", lenParamName := "n", elemBytes := 8 }
    | [(_, _, _, .i64, .zipAdd)] | [(_, _, _, .i64, .zipMul)] =>
      { kernelName := fnName, inputBufferNames := ["in0", "in1"], outputBufferName := "out", lenParamName := "n", elemBytes := 8 }
    | _ =>
      let nIn := if d.params.isEmpty then 1 else Nat.min 2 d.params.length
      let inNames := (List.range nIn).map (fun idx => s!"in{idx}")
      { kernelName := fnName, inputBufferNames := inNames, outputBufferName := "out", lenParamName := "n", elemBytes := 8 }

/-- Verify that the `.metal` kernel signature for `spec.kernelName` and the corresponding per-function
    Objective-C host dispatch slice (`lean_native_metal_dispatch_1d`, `lean_native_metal_dispatch_binary_1d`,
    or `lean_native_metal_dispatch_saxpy_f16`) + per-declaration wrapper (`lean_native_metal_zerocopy_<decl>`)
    agree on every `[[buffer(i)]]` parameter name, buffer variable, and index (`0 .. spec.nBufferIdx`). -/
def verifyMetalBindingContract (spec : MetalKernelBindingSpec) (msl hostGlue : String) : Bool :=
  let dispatchFnName :=
    if spec.scalarF16Name?.isSome then "lean_native_metal_dispatch_saxpy_f16"
    else if spec.numInputs >= 2 then "lean_native_metal_dispatch_binary_1d"
    else "lean_native_metal_dispatch_1d"
  let dispatchSlice := match hostGlue.splitOn s!"static inline int {dispatchFnName}(" with
    | _ :: afterFn :: _ => (afterFn.splitOn "\n}\n").headD ((afterFn.splitOn "\n#endif").headD "")
    | _ => ""
  let wrapperOk : Bool :=
    if spec.kernelName.startsWith "lean_native_metal_decl_" then
      let declName := (spec.kernelName.drop 23).toString
      match hostGlue.splitOn s!"int lean_native_metal_zerocopy_{declName}(" with
      | _ :: afterWrap :: _ =>
        let wrapSlice := (afterWrap.splitOn "\n}").headD ""
        (wrapSlice.splitOn s!"{dispatchFnName}(\"{spec.kernelName}\"").length > 1
      | _ => false
    else if spec.scalarF16Name?.isSome then
      (dispatchSlice.splitOn s!"@\"{spec.kernelName}\"").length > 1
    else true
  match msl.splitOn s!"kernel void {spec.kernelName}(" with
  | _ :: afterHdr :: _ =>
    if dispatchSlice.isEmpty || !wrapperOk then false
    else
      let sigBlock := (afterHdr.splitOn ") {").headD ""
      let expectedInBuf (idx : Nat) : String :=
        if spec.scalarF16Name?.isSome then (if idx == 0 then "bufX" else "bufY")
        else s!"bufIn{idx}"
      let inputsOk := (List.range spec.numInputs).zip spec.inputBufferNames |>.all fun (idx, nm) =>
        (sigBlock.splitOn s!"{nm} [[buffer({idx})]]").length > 1 &&
        (dispatchSlice.splitOn s!"[enc setBuffer:{expectedInBuf idx} offset:0 atIndex:{idx}]").length > 1
      let outOk :=
        (sigBlock.splitOn s!"{spec.outputBufferName} [[buffer({spec.outBufferIdx})]]").length > 1 &&
        (dispatchSlice.splitOn s!"[enc setBuffer:bufOut offset:0 atIndex:{spec.outBufferIdx}]").length > 1
      let scalarOk := match spec.scalarF16Name?, spec.scalarF16BufferIdx? with
        | some sName, some sIdx =>
          (sigBlock.splitOn s!"{sName} [[buffer({sIdx})]]").length > 1 &&
          (dispatchSlice.splitOn s!"[enc setBytes:&alpha_f16_bits length:sizeof(uint16_t) atIndex:{sIdx}]").length > 1
        | _, _ =>
          (dispatchSlice.splitOn "alpha_f16_bits").length == 1
      let lenOk :=
        (sigBlock.splitOn s!"{spec.lenParamName} [[buffer({spec.nBufferIdx})]]").length > 1 &&
        (dispatchSlice.splitOn s!"[enc setBytes:&n_u64 length:sizeof(uint64_t) atIndex:{spec.nBufferIdx}]").length > 1 &&
        (dispatchSlice.splitOn s!"atIndex:{spec.nBufferIdx + 1}]").length == 1
      inputsOk && outOk && scalarOk && lenOk
  | _ => false

/-- Emit 16 KB page-aligned Apple7 Metal 3.0 unified-memory zero-copy host dispatch glue (`emitMetalZeroCopyHostGlue`).
    Uses `posix_memalign(&ptr, 16384, aligned_bytes)` (`16384` B page boundary required by iOS/Apple Silicon VM),
    gates every declaration wrapper through `buildHybridDispatchPlan .gpuMetal`, and enforces overflow,
    non-aliasing (`out_data + aligned_bytes <= in_data || in_data + aligned_bytes <= out_data`), and
    16 KB page-alignment guards before `MTLResourceStorageModeShared` zero-copy binding. -/
def emitMetalZeroCopyHostGlue (plan : HybridPartitionPlan) : String :=
  let effMin := Nat.max plan.minGpuElements metalDispatchFloor
  let header := String.intercalate "\n" [
    s!"// LeanNative Apple7 Metal 3.0 Unified-Memory Zero-Copy Host Glue for Module: {plan.moduleName}",
    s!"// Certified by leannative_verify_backend_choice (metalDispatchFloor = {effMin}, pageAlign = {metalPageBytes} B)",
    "#include <stddef.h>\n#include <stdint.h>\n#include <stdlib.h>",
    "#ifdef __OBJC__\n#import <Metal/Metal.h>\n#endif\n",
    s!"#define LEAN_NATIVE_METAL_PAGE_SIZE {metalPageBytes}ULL",
    s!"#define LEAN_NATIVE_METAL_MIN_ELEMENTS {effMin}ULL\n",
    "static inline size_t lean_native_align16k(size_t bytes) {",
    "    return (bytes + 16383ULL) & ~16383ULL;",
    "}\n",
    "static inline void* lean_native_alloc_shared16k(size_t bytes) {",
    "    void* ptr = NULL;",
    "    size_t aligned = lean_native_align16k(bytes == 0 ? 16384ULL : bytes);",
    "    if (posix_memalign(&ptr, 16384ULL, aligned) != 0) return NULL;",
    "    return ptr;",
    "}\n",
    "static inline int lean_native_metal_route_admissible(\n" ++
      "    const void* out_ptr, size_t out_capacity, const void* in0_ptr,\n" ++
      "    size_t in0_capacity, size_t elem_bytes, size_t n) {",
    "    if (!out_ptr || !in0_ptr || elem_bytes == 0ULL || n < LEAN_NATIVE_METAL_MIN_ELEMENTS) return 0;",
    "    if (n > (SIZE_MAX - 16383ULL) / elem_bytes) return 0;",
    "    size_t aligned_bytes = lean_native_align16k(n * elem_bytes);",
    "    if (out_capacity < aligned_bytes || in0_capacity < aligned_bytes) return 0;",
    "    uintptr_t out_data = (uintptr_t)out_ptr;",
    "    uintptr_t in_data = (uintptr_t)in0_ptr;",
    "    if (out_data > UINTPTR_MAX - aligned_bytes || in_data > UINTPTR_MAX - aligned_bytes) return 0;",
    "    if (!(out_data + aligned_bytes <= in_data || in_data + aligned_bytes <= out_data)) return 0;",
    "    return (((out_data | in_data | out_capacity | in0_capacity) & 16383ULL) == 0ULL) ? 1 : 0;",
    "}\n",
    "#ifdef __OBJC__",
    "static inline id<MTLBuffer> lean_native_metal_buffer_nocopy(\n" ++
      "    id<MTLDevice> dev, void* ptr, size_t bytes, size_t capacity) {",
    "    if (!dev || !ptr || (((uintptr_t)ptr & 16383ULL) != 0ULL)) return nil;",
    "    size_t aligned = lean_native_align16k(bytes);",
    "    if (capacity < aligned || (capacity & 16383ULL) != 0ULL) return nil;",
    "    return [dev newBufferWithBytesNoCopy:ptr length:aligned " ++
      "options:MTLResourceStorageModeShared\n" ++
      "        deallocator:nil];",
    "}\n",
    "/* Unary 1D kernel contract: in0 -> buffer(0), out -> buffer(1), n -> buffer(2) */",
    "static inline int lean_native_metal_dispatch_1d(\n" ++
      "    const char* kernel_name, void* out_ptr, size_t out_capacity,\n" ++
      "    const void* in0_ptr, size_t in0_capacity, size_t elem_bytes, size_t n) {",
    "    if (!lean_native_metal_route_admissible(out_ptr, out_capacity, in0_ptr, in0_capacity, elem_bytes, n)) return 1;",
    "    @autoreleasepool {",
    "        id<MTLDevice> dev = MTLCreateSystemDefaultDevice();",
    "        if (!dev) return 1;",
    "        id<MTLCommandQueue> queue = [dev newCommandQueue];",
    "        if (!queue) return 1;",
    "        id<MTLLibrary> lib = [dev newDefaultLibrary];",
    "        if (!lib) return 1;",
    "        NSString* fnName = [NSString stringWithUTF8String:kernel_name];",
    "        id<MTLFunction> fn = [lib newFunctionWithName:fnName];",
    "        if (!fn) return 1;",
    "        NSError* err = nil;",
    "        id<MTLComputePipelineState> pso = [dev newComputePipelineStateWithFunction:fn error:&err];",
    "        if (!pso || err) return 1;",
    "        size_t total_bytes = n * elem_bytes;",
    "        id<MTLBuffer> bufIn0 = lean_native_metal_buffer_nocopy(dev, (void*)in0_ptr, total_bytes, in0_capacity);",
    "        id<MTLBuffer> bufOut = lean_native_metal_buffer_nocopy(dev, out_ptr, total_bytes, out_capacity);",
    "        if (!bufIn0 || !bufOut) return 1;",
    "        id<MTLCommandBuffer> cmd = [queue commandBuffer];",
    "        if (!cmd) return 1;",
    "        id<MTLComputeCommandEncoder> enc = [cmd computeCommandEncoder];",
    "        if (!enc) return 1;",
    "        uint64_t n_u64 = (uint64_t)n;",
    "        [enc setComputePipelineState:pso];",
    "        [enc setBuffer:bufIn0 offset:0 atIndex:0];",
    "        [enc setBuffer:bufOut offset:0 atIndex:1];",
    "        [enc setBytes:&n_u64 length:sizeof(uint64_t) atIndex:2];",
    "        NSUInteger maxTgs = [pso maxTotalThreadsPerThreadgroup];",
    "        NSUInteger tgs = (maxTgs > 256) ? 256 : (maxTgs == 0 ? 1 : maxTgs);",
    "        [enc dispatchThreads:MTLSizeMake(n, 1, 1) threadsPerThreadgroup:MTLSizeMake(tgs, 1, 1)];",
    "        [enc endEncoding];",
    "        [cmd commit];",
    "        [cmd waitUntilCompleted];",
    "        return ([cmd status] == MTLCommandBufferStatusCompleted) ? 0 : 1;",
    "    }",
    "}\n",
    "/* Binary 1D kernel contract: in0 -> buffer(0), in1 -> buffer(1), out -> buffer(2), n -> buffer(3) */",
    "static inline int lean_native_metal_dispatch_binary_1d(\n" ++
      "    const char* kernel_name, void* out_ptr, size_t out_capacity,\n" ++
      "    const void* in0_ptr, size_t in0_capacity, const void* in1_ptr,\n" ++
      "    size_t in1_capacity, size_t elem_bytes, size_t n) {",
    "    if (!lean_native_metal_route_admissible(out_ptr, out_capacity, in0_ptr, in0_capacity, elem_bytes, n)) return 1;",
    "    if (!lean_native_metal_route_admissible(out_ptr, out_capacity, in1_ptr, in1_capacity, elem_bytes, n)) return 1;",
    "    @autoreleasepool {",
    "        id<MTLDevice> dev = MTLCreateSystemDefaultDevice();",
    "        if (!dev) return 1;",
    "        id<MTLCommandQueue> queue = [dev newCommandQueue];",
    "        if (!queue) return 1;",
    "        id<MTLLibrary> lib = [dev newDefaultLibrary];",
    "        if (!lib) return 1;",
    "        NSString* fnName = [NSString stringWithUTF8String:kernel_name];",
    "        id<MTLFunction> fn = [lib newFunctionWithName:fnName];",
    "        if (!fn) return 1;",
    "        NSError* err = nil;",
    "        id<MTLComputePipelineState> pso = [dev newComputePipelineStateWithFunction:fn error:&err];",
    "        if (!pso || err) return 1;",
    "        size_t total_bytes = n * elem_bytes;",
    "        id<MTLBuffer> bufIn0 = lean_native_metal_buffer_nocopy(dev, (void*)in0_ptr, total_bytes, in0_capacity);",
    "        id<MTLBuffer> bufIn1 = lean_native_metal_buffer_nocopy(dev, (void*)in1_ptr, total_bytes, in1_capacity);",
    "        id<MTLBuffer> bufOut = lean_native_metal_buffer_nocopy(dev, out_ptr, total_bytes, out_capacity);",
    "        if (!bufIn0 || !bufIn1 || !bufOut) return 1;",
    "        id<MTLCommandBuffer> cmd = [queue commandBuffer];",
    "        if (!cmd) return 1;",
    "        id<MTLComputeCommandEncoder> enc = [cmd computeCommandEncoder];",
    "        if (!enc) return 1;",
    "        uint64_t n_u64 = (uint64_t)n;",
    "        [enc setComputePipelineState:pso];",
    "        [enc setBuffer:bufIn0 offset:0 atIndex:0];",
    "        [enc setBuffer:bufIn1 offset:0 atIndex:1];",
    "        [enc setBuffer:bufOut offset:0 atIndex:2];",
    "        [enc setBytes:&n_u64 length:sizeof(uint64_t) atIndex:3];",
    "        NSUInteger maxTgs = [pso maxTotalThreadsPerThreadgroup];",
    "        NSUInteger tgs = (maxTgs > 256) ? 256 : (maxTgs == 0 ? 1 : maxTgs);",
    "        [enc dispatchThreads:MTLSizeMake(n, 1, 1) threadsPerThreadgroup:MTLSizeMake(tgs, 1, 1)];",
    "        [enc endEncoding];",
    "        [cmd commit];",
    "        [cmd waitUntilCompleted];",
    "        return ([cmd status] == MTLCommandBufferStatusCompleted) ? 0 : 1;",
    "    }",
    "}\n",
    "/* SAXPY FP16 kernel contract (lean_native_kernel_saxpy_f16): " ++
      "x -> buffer(0), y -> buffer(1), out -> buffer(2), alpha -> buffer(3), n -> buffer(4) */",
    "static inline int lean_native_metal_dispatch_saxpy_f16(\n" ++
      "    void* out_ptr, size_t out_capacity, const void* x_ptr, size_t x_capacity,\n" ++
      "    const void* y_ptr, size_t y_capacity, uint16_t alpha_f16_bits, size_t n) {",
    "    if (!lean_native_metal_route_admissible(out_ptr, out_capacity, x_ptr, x_capacity, sizeof(uint16_t), n)) return 1;",
    "    if (!lean_native_metal_route_admissible(out_ptr, out_capacity, y_ptr, y_capacity, sizeof(uint16_t), n)) return 1;",
    "    @autoreleasepool {",
    "        id<MTLDevice> dev = MTLCreateSystemDefaultDevice();",
    "        if (!dev) return 1;",
    "        id<MTLCommandQueue> queue = [dev newCommandQueue];",
    "        if (!queue) return 1;",
    "        id<MTLLibrary> lib = [dev newDefaultLibrary];",
    "        if (!lib) return 1;",
    "        id<MTLFunction> fn = [lib newFunctionWithName:@\"lean_native_kernel_saxpy_f16\"];",
    "        if (!fn) return 1;",
    "        NSError* err = nil;",
    "        id<MTLComputePipelineState> pso = [dev newComputePipelineStateWithFunction:fn error:&err];",
    "        if (!pso || err) return 1;",
    "        size_t total_bytes = n * sizeof(uint16_t);",
    "        id<MTLBuffer> bufX = lean_native_metal_buffer_nocopy(dev, (void*)x_ptr, total_bytes, x_capacity);",
    "        id<MTLBuffer> bufY = lean_native_metal_buffer_nocopy(dev, (void*)y_ptr, total_bytes, y_capacity);",
    "        id<MTLBuffer> bufOut = lean_native_metal_buffer_nocopy(dev, out_ptr, total_bytes, out_capacity);",
    "        if (!bufX || !bufY || !bufOut) return 1;",
    "        id<MTLCommandBuffer> cmd = [queue commandBuffer];",
    "        if (!cmd) return 1;",
    "        id<MTLComputeCommandEncoder> enc = [cmd computeCommandEncoder];",
    "        if (!enc) return 1;",
    "        uint64_t n_u64 = (uint64_t)n;",
    "        [enc setComputePipelineState:pso];",
    "        [enc setBuffer:bufX offset:0 atIndex:0];",
    "        [enc setBuffer:bufY offset:0 atIndex:1];",
    "        [enc setBuffer:bufOut offset:0 atIndex:2];",
    "        [enc setBytes:&alpha_f16_bits length:sizeof(uint16_t) atIndex:3];",
    "        [enc setBytes:&n_u64 length:sizeof(uint64_t) atIndex:4];",
    "        NSUInteger maxTgs = [pso maxTotalThreadsPerThreadgroup];",
    "        NSUInteger tgs = (maxTgs > 256) ? 256 : (maxTgs == 0 ? 1 : maxTgs);",
    "        [enc dispatchThreads:MTLSizeMake(n, 1, 1) threadsPerThreadgroup:MTLSizeMake(tgs, 1, 1)];",
    "        [enc endEncoding];",
    "        [cmd commit];",
    "        [cmd waitUntilCompleted];",
    "        return ([cmd status] == MTLCommandBufferStatusCompleted) ? 0 : 1;",
    "    }",
    "}",
    "#endif\n",
    "int lean_native_metal_zerocopy_saxpy_f16(\n" ++
      "    void* out_ptr, size_t out_capacity, const void* x_ptr, size_t x_capacity,\n" ++
      "    const void* y_ptr, size_t y_capacity, uint16_t alpha_f16_bits, size_t n) {",
    "    if (!lean_native_metal_route_admissible(out_ptr, out_capacity, x_ptr, x_capacity, sizeof(uint16_t), n)) return 1;",
    "    if (!lean_native_metal_route_admissible(out_ptr, out_capacity, y_ptr, y_capacity, sizeof(uint16_t), n)) return 1;",
    "#ifdef __OBJC__",
    "    return lean_native_metal_dispatch_saxpy_f16(\n" ++
      "        out_ptr, out_capacity, x_ptr, x_capacity, y_ptr, y_capacity, alpha_f16_bits, n);",
    "#else",
    "    (void)alpha_f16_bits;",
    "    return 1;",
    "#endif",
    "}"
  ]
  let declGlues := plan.gpuDecls.map fun d =>
    match buildHybridDispatchPlan .gpuMetal effMin true d with
    | .error err =>
      s!"#error \"validateHybridDispatch failed for Metal zero-copy {d.name}: {repr err}\""
    | .ok vplan =>
      let spec := declMetalBindingSpec d
      if spec.numInputs >= 2 then
        String.intercalate "\n" [
          s!"/* Validated Metal Zero-Copy Plan: {vplan.kernelName}, " ++
            s!"minElems={vplan.workloadElems}, gridThreads={vplan.gridThreads} */",
          s!"int lean_native_metal_zerocopy_{d.name}(" ++
            "void* out_ptr, size_t out_capacity, const void* in0_ptr, size_t in0_capacity, " ++
            "\n    const void* in1_ptr, size_t in1_capacity, size_t n) {",
          "    if (!lean_native_metal_route_admissible(out_ptr, out_capacity, in0_ptr, in0_capacity, sizeof(uint64_t), n)) return 1;",
          "    if (!lean_native_metal_route_admissible(out_ptr, out_capacity, in1_ptr, in1_capacity, sizeof(uint64_t), n)) return 1;",
          "#ifdef __OBJC__",
          s!"    return lean_native_metal_dispatch_binary_1d(\"{spec.kernelName}\", " ++
            "out_ptr, out_capacity, in0_ptr, in0_capacity,\n" ++
            "        in1_ptr, in1_capacity, sizeof(uint64_t), n);",
          "#else",
          "    return 1; /* Non-ObjC TU -> fallback to ARM64 NEON CPU SIMD */",
          "#endif",
          "}"
        ]
      else
        String.intercalate "\n" [
          s!"/* Validated Metal Zero-Copy Plan: {vplan.kernelName}, " ++
            s!"minElems={vplan.workloadElems}, gridThreads={vplan.gridThreads} */",
          s!"int lean_native_metal_zerocopy_{d.name}(" ++
            "void* out_ptr, size_t out_capacity,\n" ++
            "    const void* in0_ptr, size_t in0_capacity, size_t n) {",
          "    if (!lean_native_metal_route_admissible(out_ptr, out_capacity, in0_ptr, in0_capacity, sizeof(uint64_t), n)) {",
          "        return 1; /* Route rejected by cost/alignment/capacity/alias gate -> CPU SIMD fallback */",
          "    }",
          "#ifdef __OBJC__",
          s!"    return lean_native_metal_dispatch_1d(\"{spec.kernelName}\", " ++
            "out_ptr, out_capacity,\n" ++
            "        in0_ptr, in0_capacity, sizeof(uint64_t), n);",
          "#else",
          "    return 1; /* Non-ObjC TU -> fallback to ARM64 NEON CPU SIMD */",
          "#endif",
          "}"
        ]
  String.intercalate "\n\n" (header :: declGlues) ++ "\n"

/-- CPU+PTX, CPU+Metal, or CPU+StableHLO plan retained for executable tests. -/
structure HybridTargetPlan where
  target : ComputeTarget
  request : HybridLaunchRequest
  source : String
  deriving Repr, Inhabited

/-- Build one representative request for a compute target.
    `.gpuMetal` honors `metalDispatchFloor` (`262144` elements = 2 MB) and `16384`-byte page alignment. -/
def sampleHybridRequest (target : ComputeTarget) : HybridLaunchRequest :=
  let elems := if target == .gpuMetal then metalDispatchFloor else 256
  let gridX := elems / 256
  let outBase := if target == .gpuMetal then 0x400000 else 4096
  let input : DeviceBufferDesc := {
    name := "in0", elemBytes := 8, numElems := elems, byteStride := 8, baseAlign := 8,
    direction := .hostToDevice, zeroCopy := target == .gpuMetal, rc := 2, baseAddr := 0,
    ownership := .pinnedHostRef, bufId := 0
  }
  let output : DeviceBufferDesc := {
    name := "out", elemBytes := 8, numElems := elems, byteStride := 8, baseAlign := 8,
    direction := .deviceToHost, zeroCopy := target == .gpuMetal, rc := 1, baseAddr := outBase,
    ownership := .uniqueOutBuffer, bufId := 1
  }
  {
    kernelName := s!"lean_native_hybrid_{target}", target, workloadElems := elems,
    maxThreadsPerBlock := 1024, gridDim := { x := gridX, y := 1, z := 1 },
    blockDim := { x := 256, y := 1, z := 1 }, buffers := [input, output], tailGuarded := true
  }

/-- Concrete dispatch plans for the three hybrid backends. -/
def hybridTargetPlans : List HybridTargetPlan :=
  [ { target := .gpuCudaPtx, request := sampleHybridRequest .gpuCudaPtx,
      source := "cpu+ptx stream: pin inputs, launch grid, synchronize, release" },
    { target := .gpuMetal, request := sampleHybridRequest .gpuMetal,
      source := "cpu+metal unified memory: 16KB page-aligned zero-copy buffers at metalDispatchFloor, tail-guarded gid < n" },
    { target := .tpuXlaStableHLO, request := sampleHybridRequest .tpuXlaStableHLO,
      source := "cpu+stablehlo: disjoint host outputs returned at rc = 1" } ]

end LeanNative.Backend.Hybrid

namespace LeanNative.Backend
  export Hybrid (
    ComputeTarget
    SearchBackend
    TransferMode
    TransferAction
    HybridPartitionPlan
    TransferDirection
    isMutableTransfer
    Dim3
    RcOwnership
    DeviceBufferDesc
    HybridLifecycleError
    HybridLaunchRequest
    HybridDispatchPlan
    HybridDispatchError
    HybridTargetPlan
    MetalKernelBindingSpec
    saxpyF16MetalBindingSpec
    declMetalBindingSpec
    verifyMetalBindingContract
    metalDispatchFloor
    metalPageBytes
    selectOptimalComputeTarget
    selectAppleA15Target
    selectOptimalSearchBackend
    classifyDeclComputeTarget
    pinBufferStep
    launchKernelStep
    syncDeviceStep
    releaseBufferStep
    execHybridTransferLifecycle
    validateHybridDispatch
    buildHybridDispatchPlan
    hybridDispatchSound
    rcConserved
    partitionModule
    emitHybridHostGlue
    emitMetalZeroCopyHostGlue
    sampleHybridRequest
    hybridTargetPlans
  )
end LeanNative.Backend
