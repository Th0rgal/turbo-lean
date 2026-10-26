import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Backend.MLIRGPU

namespace LeanNative.Backend.Hybrid

open LeanNative.IR
open LeanNative.Backend.MLIRGPU

/-- Apple A15 / Apple7 Metal 3.0 unified-memory zero-copy dispatch floor (`262144` elements = 2 MB `uint64_t`),
    where the 4-core Apple7 GPU amortizes the ~60 µs Metal command buffer dispatch over 2P+4E NEON cores. -/
def metalDispatchFloor : Nat := 262144

/-- Pure scalar Apple7 Metal 3.0 unified-memory zero-copy vs NEON CPU cost router gate (`verifyBackendChoice`). -/
@[inline]
def verifyBackendChoice
    (tripCount : UInt64)
    (isControlHeavy hasMetalGpu isPageAligned chosenBackend : UInt8) : UInt8 :=
  if (chosenBackend == 1 && isControlHeavy == 0 && hasMetalGpu == 1 && isPageAligned == 1 && 262144 ≤ tripCount) ||
     (chosenBackend == 0 && (isControlHeavy == 1 || hasMetalGpu == 0 || isPageAligned == 0 || tripCount < 262144)) then 1 else 0

/-- Memory transfer / coherency strategy between host CPU and CUDA GPU. -/
inductive TransferMode where
  | unifiedMemoryZeroCopy   -- Grace-Blackwell coherent unified memory + async prefetch
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
    with adaptive dispatch threshold `minGpuElements` (default `65536`). -/
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
      if ok && loweringErrors.isEmpty then
        let action : TransferAction := {
          declName             := d.name
          bufferVars           := collectBufferParams d
          mode                 := mode
          minElements          := minGpuElements
          requiresHostCowCheck := hasCowCheck d.body
          syncPoint            := s!"cuStreamSynchronize(stream_{d.name})"
        }
        (gAcc ++ [d], cAcc, sAcc ++ [action], dAcc)
      else
        (gAcc, cAcc ++ [d], sAcc, dAcc ++ [(d.name, reasons ++ loweringErrors)])
    ) ([], [], [], [])
  {
    moduleName       := m.moduleName
    gpuDecls         := gpuDecls
    cpuOnlyDecls     := cpuOnlyDecls
    minGpuElements   := minGpuElements
    transferSchedule := schedule
    diagnostics      := diags
  }

/-- Emit C host dispatch glue for a single GPU-partitioned declaration.
    Selects the PTX GPU kernel when `n >= minGpuElements && lean_native_gpu_available()`
    and falls back to the LLVM CPU SIMD implementation otherwise. -/
def emitDeclHostGlue (minGpuElements : Nat) (actionOpt : Option TransferAction) (d : LNIRDecl) : String :=
  let modeComment := match actionOpt with
    | some act =>
      s!"/* TransferMode: {act.mode}, minElements: {act.minElements}, COW-exclusivity-check: {act.requiresHostCowCheck}, sync: {act.syncPoint} */"
    | none =>
      s!"/* TransferMode: UnifiedMemoryZeroCopy, minElements: {minGpuElements} */"
  let mkGlue (sig nullChk sizeVar : String) (numBufs : Nat) (gpuCall cpuFallback : String) : String :=
    String.intercalate "\n" [
      s!"int lean_native_hybrid_dispatch_{d.name}({sig}) \{",
      s!"    {modeComment}",
      s!"    if ({nullChk}) return -1;\n    size_t n = {sizeVar}->m_size;",
      s!"    if (n >= {minGpuElements}ULL && lean_native_gpu_available() && lean_native_gpu_has_headroom(n * sizeof(uint64_t) * {numBufs}u)) \{",
      s!"{gpuCall}",
      "        if (rc == 0) return 0;",
      "    }",
      s!"{cpuFallback}",
      "    return 0;",
      "}"
    ]
  match extractParForRegions d.body with
  | [(_, _, _, .i64, .mapScaleAdd scale bias)] =>
    mkGlue "lean_native_sarray_u64* out, const lean_native_sarray_u64* in0" "!out || !in0" "in0" 2
      s!"        int rc = lean_native_hybrid_map_scale_add_u64(out->m_data, in0->m_data, (uint64_t){scale}ULL, (uint64_t){bias}ULL, n);"
      s!"    for (size_t i = 0; i < n; ++i) \{\n        out->m_data[i] = in0->m_data[i] * (uint64_t){scale}ULL + (uint64_t){bias}ULL;\n    }"
  | [(_, _, _, .i64, .zipAdd)] =>
    mkGlue "lean_native_sarray_u64* out, const lean_native_sarray_u64* in0, const lean_native_sarray_u64* in1" "!out || !in0 || !in1" "in0" 3
      "        int rc = lean_native_hybrid_zip_add_u64(out->m_data, in0->m_data, in1->m_data, n);"
      "    for (size_t i = 0; i < n; ++i) {\n        out->m_data[i] = in0->m_data[i] + in1->m_data[i];\n    }"
  | [(_, _, _, .i64, .zipMul)] =>
    mkGlue "lean_native_sarray_u64* out, const lean_native_sarray_u64* in0, const lean_native_sarray_u64* in1" "!out || !in0 || !in1" "in0" 3
      "        void* args[4] = { (void*)&out->m_data, (void*)&in0->m_data, (void*)&in1->m_data, (void*)&n };\n        int rc = lean_native_launch_ptx_kernel(\"lean_native_kernel_zip_mul\", args, n);"
      "    for (size_t i = 0; i < n; ++i) {\n        out->m_data[i] = in0->m_data[i] * in1->m_data[i];\n    }"
  | [(_, _, _, .i64, .dotProduct)] =>
    mkGlue "lean_native_sarray_u64* out, const lean_native_sarray_u64* in0, const lean_native_sarray_u64* in1" "!out || !in0 || !in1 || out->m_size == 0" "in0" 2
      "        int rc = lean_native_hybrid_dot_product_u64(&out->m_data[0], in0->m_data, in1->m_data, n);"
      "    lean_native_cpu_dot_product_u64(&out->m_data[0], in0->m_data, in1->m_data, n);"
  | [(_, _, _, .i64, .saxpy alphaBits)] =>
    mkGlue "lean_native_sarray_u64* out, const lean_native_sarray_u64* x, const lean_native_sarray_u64* y" "!out || !x || !y" "x" 3
      s!"        int rc = lean_native_hybrid_saxpy_u64(out->m_data, x->m_data, y->m_data, (uint64_t){alphaBits}ULL, n);"
      s!"    for (size_t i = 0; i < n; ++i) \{\n        out->m_data[i] = (uint64_t){alphaBits}ULL * x->m_data[i] + y->m_data[i];\n    }"
  | [(_, _, _, .i64, .stencil1D3Pt wLeft wCenter wRight)] =>
    mkGlue "lean_native_sarray_u64* out, const lean_native_sarray_u64* in0" "!out || !in0" "in0" 2
      s!"        int rc = lean_native_hybrid_stencil1d_u64(out->m_data, in0->m_data, (uint64_t){wLeft}ULL, (uint64_t){wCenter}ULL, (uint64_t){wRight}ULL, n);"
      s!"    for (size_t i = 0; i < n; ++i) \{\n        if (i == 0 || i + 1 >= n) \{\n            out->m_data[i] = in0->m_data[i];\n        } else \{\n            out->m_data[i] = in0->m_data[i - 1] * {wLeft}ULL + in0->m_data[i] * {wCenter}ULL + in0->m_data[i + 1] * {wRight}ULL;\n        }\n    }"
  | _ => s!"#error \"unsupported hybrid dispatch for {d.name}\""

/-- Generate C/LLVM host dispatch glue (`emitHybridHostGlue`) from a `HybridPartitionPlan`.
    Automatically selects GPU execution when `N >= minGpuElements` and a CUDA device is available,
    and falls back to the optimized LLVM CPU implementation otherwise. -/
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
    "#endif"
  ]

  let scheduleSummary :=
    if plan.transferSchedule.isEmpty then
      "/* No GPU transfer schedule entries (all declarations CPU-only). */"
    else
      let lines := plan.transferSchedule.map fun act =>
        let bufs := String.intercalate "," (act.bufferVars.map fun v => s!"%v{v}")
        s!" *   - {act.declName}: buffers=[{bufs}] mode={act.mode} minElements={act.minElements} cowCheck={act.requiresHostCowCheck} sync={act.syncPoint}"
      "/*\n * Transfer Schedule:\n" ++ String.intercalate "\n" lines ++ "\n */"

  let declGlues := plan.gpuDecls.map fun d =>
    let actOpt := plan.transferSchedule.find? (fun a => a.declName == d.name)
    emitDeclHostGlue plan.minGpuElements actOpt d

  String.intercalate "\n\n" ([header, scheduleSummary] ++ declGlues) ++ "\n"

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
    | [(_, _, _, .i64, .mapScaleAdd _ _)] =>
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
    Uses `posix_memalign(&ptr, 16384, aligned_bytes)` (`16384` B page boundary required by iOS/Apple Silicon VM)
    and `[device newBufferWithBytesNoCopy:ptr length:aligned_bytes options:MTLResourceStorageModeShared deallocator:nil]`
    so CPU and Apple7 GPU share physical unified DRAM with zero H2D/D2H copy overhead.
    Returns `0` when the Metal compute pipeline executes to `MTLCommandBufferStatusCompleted`,
    or `1` when routing/initialization/execution falls back to ARM64 NEON CPU SIMD. -/
def emitMetalZeroCopyHostGlue (plan : HybridPartitionPlan) : String :=
  let effMin := Nat.max plan.minGpuElements metalDispatchFloor
  let header := String.intercalate "\n" [
    s!"// LeanNative Apple7 Metal 3.0 Unified-Memory Zero-Copy Host Glue for Module: {plan.moduleName}",
    s!"// Certified by leannative_verify_backend_choice (metalDispatchFloor = {effMin}, pageAlign = 16384 B)",
    "#include <stddef.h>\n#include <stdint.h>\n#include <stdlib.h>",
    "#ifdef __OBJC__\n#import <Metal/Metal.h>\n#endif\n",
    s!"#define LEAN_NATIVE_METAL_PAGE_SIZE 16384ULL",
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
    "static inline int lean_native_metal_route_admissible(const void* out_ptr, size_t out_capacity, const void* in0_ptr, size_t in0_capacity, size_t elem_bytes, size_t n) {",
    "    if (!out_ptr || !in0_ptr || elem_bytes == 0ULL || n < LEAN_NATIVE_METAL_MIN_ELEMENTS) return 0;",
    "    if (n > (SIZE_MAX - 16383ULL) / elem_bytes) return 0;",
    "    size_t aligned_bytes = lean_native_align16k(n * elem_bytes);",
    "    if (out_capacity < aligned_bytes || in0_capacity < aligned_bytes) return 0;",
    "    return ((((uintptr_t)out_ptr | (uintptr_t)in0_ptr | out_capacity | in0_capacity) & 16383ULL) == 0ULL) ? 1 : 0;",
    "}\n",
    "#ifdef __OBJC__",
    "static inline id<MTLBuffer> lean_native_metal_buffer_nocopy(id<MTLDevice> dev, void* ptr, size_t bytes, size_t capacity) {",
    "    if (!dev || !ptr || (((uintptr_t)ptr & 16383ULL) != 0ULL)) return nil;",
    "    size_t aligned = lean_native_align16k(bytes);",
    "    if (capacity < aligned || (capacity & 16383ULL) != 0ULL) return nil;",
    "    return [dev newBufferWithBytesNoCopy:ptr length:aligned options:MTLResourceStorageModeShared deallocator:nil];",
    "}\n",
    "/* Unary 1D kernel contract: in0 -> buffer(0), out -> buffer(1), n -> buffer(2) */",
    "static inline int lean_native_metal_dispatch_1d(const char* kernel_name, void* out_ptr, size_t out_capacity, const void* in0_ptr, size_t in0_capacity, size_t elem_bytes, size_t n) {",
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
    "static inline int lean_native_metal_dispatch_binary_1d(const char* kernel_name, void* out_ptr, size_t out_capacity, const void* in0_ptr, size_t in0_capacity, const void* in1_ptr, size_t in1_capacity, size_t elem_bytes, size_t n) {",
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
    "/* SAXPY FP16 kernel contract (lean_native_kernel_saxpy_f16): x -> buffer(0), y -> buffer(1), out -> buffer(2), alpha -> buffer(3), n -> buffer(4) */",
    "static inline int lean_native_metal_dispatch_saxpy_f16(void* out_ptr, size_t out_capacity, const void* x_ptr, size_t x_capacity, const void* y_ptr, size_t y_capacity, uint16_t alpha_f16_bits, size_t n) {",
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
    "int lean_native_metal_zerocopy_saxpy_f16(void* out_ptr, size_t out_capacity, const void* x_ptr, size_t x_capacity, const void* y_ptr, size_t y_capacity, uint16_t alpha_f16_bits, size_t n) {",
    "    if (!lean_native_metal_route_admissible(out_ptr, out_capacity, x_ptr, x_capacity, sizeof(uint16_t), n)) return 1;",
    "    if (!lean_native_metal_route_admissible(out_ptr, out_capacity, y_ptr, y_capacity, sizeof(uint16_t), n)) return 1;",
    "#ifdef __OBJC__",
    "    return lean_native_metal_dispatch_saxpy_f16(out_ptr, out_capacity, x_ptr, x_capacity, y_ptr, y_capacity, alpha_f16_bits, n);",
    "#else",
    "    (void)alpha_f16_bits;",
    "    return 1;",
    "#endif",
    "}"
  ]
  let declGlues := plan.gpuDecls.map fun d =>
    let spec := declMetalBindingSpec d
    if spec.numInputs >= 2 then
      String.intercalate "\n" [
        s!"int lean_native_metal_zerocopy_{d.name}(void* out_ptr, size_t out_capacity, const void* in0_ptr, size_t in0_capacity, const void* in1_ptr, size_t in1_capacity, size_t n) \{",
        "    if (!lean_native_metal_route_admissible(out_ptr, out_capacity, in0_ptr, in0_capacity, sizeof(uint64_t), n)) return 1;",
        "    if (!lean_native_metal_route_admissible(out_ptr, out_capacity, in1_ptr, in1_capacity, sizeof(uint64_t), n)) return 1;",
        "#ifdef __OBJC__",
        s!"    return lean_native_metal_dispatch_binary_1d(\"{spec.kernelName}\", out_ptr, out_capacity, in0_ptr, in0_capacity, in1_ptr, in1_capacity, sizeof(uint64_t), n);",
        "#else",
        "    return 1; /* Non-ObjC TU -> fallback to ARM64 NEON CPU SIMD */",
        "#endif",
        "}"
      ]
    else
      String.intercalate "\n" [
        s!"int lean_native_metal_zerocopy_{d.name}(void* out_ptr, size_t out_capacity, const void* in0_ptr, size_t in0_capacity, size_t n) \{",
        "    if (!lean_native_metal_route_admissible(out_ptr, out_capacity, in0_ptr, in0_capacity, sizeof(uint64_t), n)) {",
        "        return 1; /* Route rejected by cost/alignment/capacity gate -> CPU SIMD fallback */",
        "    }",
        "#ifdef __OBJC__",
        s!"    return lean_native_metal_dispatch_1d(\"{spec.kernelName}\", out_ptr, out_capacity, in0_ptr, in0_capacity, sizeof(uint64_t), n);",
        "#else",
        "    return 1; /* Non-ObjC TU -> fallback to ARM64 NEON CPU SIMD */",
        "#endif",
        "}"
      ]
  String.intercalate "\n\n" (header :: declGlues) ++ "\n"

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

end LeanNative.Backend.Hybrid

namespace LeanNative.Backend
  export Hybrid (
    ComputeTarget
    SearchBackend
    MetalKernelBindingSpec
    saxpyF16MetalBindingSpec
    declMetalBindingSpec
    verifyMetalBindingContract
    metalDispatchFloor
    selectOptimalComputeTarget
    selectAppleA15Target
    selectOptimalSearchBackend
    classifyDeclComputeTarget
    emitMetalZeroCopyHostGlue
  )
end LeanNative.Backend
