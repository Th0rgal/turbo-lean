import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Backend.MLIRGPU

namespace LeanNative.Backend.Hybrid

open LeanNative.IR
open LeanNative.Backend.MLIRGPU

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

end LeanNative.Backend.Hybrid

namespace LeanNative.Backend
  export Hybrid (
    ComputeTarget
    SearchBackend
    selectOptimalComputeTarget
    selectOptimalSearchBackend
    classifyDeclComputeTarget
  )
end LeanNative.Backend
