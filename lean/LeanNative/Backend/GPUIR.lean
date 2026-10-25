import LeanNative.IR.Types
import LeanNative.IR.AST

namespace LeanNative.Backend.GPUIR

open LeanNative.IR

/-- Target hardware/shading-language backend for GPU kernel lowering. -/
inductive GPUBackendTarget where
  | cudaPTX
  | mlirNVVM
  | appleMetal
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Unified GPU kernel archetype shared across NVIDIA PTX 8.0, MLIR/NVVM, and Apple Metal MSL 3.0. -/
inductive GPUKernelArchetype where
  | mapScaleAddU64
  | zipAddU64
  | zipMulU64
  | saxpyU64
  | stencil1D3PtU64
  | dotReduceSharedU64
  | matmulTiled16x16U64
  | saxpyF64
  | mapScaleAddF64
  | fmaF32
  | evmU256Batch
  | fastCheckFuzzU256
  | declCustom (declName : String) (hasSharedMem : Bool) (is256Bit : Bool)
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Unified descriptor for a GPU compute kernel across CUDA PTX, MLIR/NVVM, and Apple Metal. -/
structure GPUKernelDescriptor where
  symbolName     : String
  archetype      : GPUKernelArchetype
  blockThreads   : Nat
  sharedMemBytes : Nat
  uses256Bit     : Bool
  bufferCount    : Nat
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Check whether an `LNIRType` is supported for GPU kernel parameters, locals, or buffers. -/
def isTypeGpuSupported (ty : LNIRType) : Bool :=
  ty.isGpuCompatible

/-- Inspect an `LNIRExpr` for constructs incompatible with GPU execution.
    Returns a list of diagnostic reasons if incompatible (empty list means compatible). -/
def checkExprGpuCompatibility (e : LNIRExpr) : List String :=
  let reqScalar (opName : String) (ty : LNIRType) : List String :=
    if ty.isUnboxedScalar then [] else [s!"{opName} element type {reprStr ty} is not an unboxed scalar"]
  match e with
  | .scalar _ | .constU256 _ | .mulDivDown _ _ _ | .mulDivUp _ _ _
  | .storageLoad _ _ | .storageStore _ _ _ | .mkTuple _ | .projTuple _ _ | .sarrayLen _ => []
  | .allocCtor tag _ _ => [s!"heap constructor allocation (allocCtor tag={tag}) is not allowed on GPU"]
  | .ctorGetObj _ _ => ["boxed object field projection (ctorGetObj) is not allowed on GPU"]
  | .ctorGetScalar _ _ ty => if isTypeGpuSupported ty then [] else [s!"ctorGetScalar has non-GPU type {reprStr ty}"]
  | .isExclusive _ => ["reference-count exclusivity check (isExclusive) is a host-only operation"]
  | .sarrayDataPtr _ elemTy => reqScalar "sarrayDataPtr" elemTy
  | .sarrayEnsureExclusive _ _ => ["COW buffer cloning (sarrayEnsureExclusive) must execute on host before kernel launch"]
  | .sarrayGet _ _ elemTy => reqScalar "sarrayGet" elemTy
  | .sarraySet _ _ _ elemTy => reqScalar "sarraySet" elemTy
  | .rawLoad _ _ elemTy => reqScalar "rawLoad" elemTy
  | .boxScalar _ _ => ["scalar boxing (boxScalar) allocates on the Lean heap and cannot run on GPU"]
  | .unboxScalar _ _ => ["scalar unboxing (unboxScalar) accesses a boxed heap pointer and cannot run on GPU"]
  | .call fnName _ retTy isExtern =>
    if isExtern then [s!"external CPU FFI call '{fnName}' cannot be offloaded to GPU"]
    else if !isTypeGpuSupported retTy then [s!"call to '{fnName}' returns non-GPU type {reprStr retTy}"]
    else []

/-- Recursively check an `LNIRCode` block for GPU compatibility violations. -/
partial def checkCodeGpuCompatibility (code : LNIRCode) : List String :=
  match code with
  | .letBind dst ty val k =>
    let tyErrs :=
      if isTypeGpuSupported ty then []
      else [s!"let-binding %v{dst} has non-GPU-compatible type {reprStr ty}"]
    let valErrs :=
      match val with
      | .sarrayEnsureExclusive _ elemTy =>
        if elemTy.isUnboxedScalar then []
        else [s!"sarrayEnsureExclusive element type {reprStr elemTy} is not an unboxed scalar"]
      | _ => checkExprGpuCompatibility val
    tyErrs ++ valErrs ++ checkCodeGpuCompatibility k
  | .rawStore _ _ _ elemTy k =>
    let elemErrs :=
      if elemTy.isUnboxedScalar then []
      else [s!"rawStore element type {reprStr elemTy} is not an unboxed scalar"]
    elemErrs ++ checkCodeGpuCompatibility k
  | .incRef objVar count k =>
    [s!"reference counting (incRef %v{objVar} by {count}) is not allowed in GPU kernels"] ++
      checkCodeGpuCompatibility k
  | .decRef objVar count k =>
    [s!"reference counting (decRef %v{objVar} by {count}) is not allowed in GPU kernels"] ++
      checkCodeGpuCompatibility k
  | .ite _ thenBranch elseBranch =>
    checkCodeGpuCompatibility thenBranch ++ checkCodeGpuCompatibility elseBranch
  | .seqFor _ _ _ _ _ accTy stepBody k =>
    let accErrs :=
      if isTypeGpuSupported accTy then []
      else [s!"seqFor accumulator type {reprStr accTy} is not GPU-compatible"]
    accErrs ++ checkCodeGpuCompatibility stepBody ++ checkCodeGpuCompatibility k
  | .parFor _ _ _ elemTy _ k =>
    let elemErrs :=
      if elemTy.isUnboxedScalar then []
      else [s!"parFor element type {reprStr elemTy} is not an unboxed scalar"]
    elemErrs ++ checkCodeGpuCompatibility k
  | .ret _ => []
  | .unreachable => []

/-- True if `code` contains any GPU-incompatible operations (heap allocation, RC, external FFI). -/
def codeHasGpuBlocker (code : LNIRCode) : Bool :=
  !(checkCodeGpuCompatibility code).isEmpty

/-- Extract all `(outVar, lenVar, inputs, elemTy, kernel)` regions from an `LNIRCode` tree. -/
partial def extractParForRegions (code : LNIRCode) :
    List (VarId × VarId × List VarId × LNIRType × ParallelKernelKind) :=
  match code with
  | .letBind _ _ _ k | .rawStore _ _ _ _ k | .incRef _ _ k | .decRef _ _ k => extractParForRegions k
  | .ite _ t e | .seqFor _ _ _ _ _ _ t e => extractParForRegions t ++ extractParForRegions e
  | .parFor outVar lenVar inputs elemTy kernel k =>
    (outVar, lenVar, inputs, elemTy, kernel) :: extractParForRegions k
  | .ret _ | .unreachable => []

/-- Check whether an `LNIRCode` contains at least one `parFor` data-parallel region. -/
def containsParFor (code : LNIRCode) : Bool :=
  !(extractParForRegions code).isEmpty

/-- Automatic GPU suitability analyzer for an `LNIRDecl` shared across PTX, MLIR/NVVM, and Metal.
    Checks parameter/return types (`isTypeGpuSupported`), verifies the absence of
    heap allocations (`allocCtor`), reference counting (`incRef`/`decRef`), and external CPU calls,
    and returns `(isCompatible, diagnostics)`. -/
def analyzeDeclGpuSuitability (d : LNIRDecl) : Bool × List String :=
  let paramErrs := d.params.foldl (fun acc p =>
    if isTypeGpuSupported p.ty then acc
    else acc ++ [s!"parameter '{p.name}' (%v{p.id}) has non-GPU type {reprStr p.ty}"]) []
  let retErrs :=
    if isTypeGpuSupported d.retTy || d.retTy == .unit then []
    else [s!"return type {reprStr d.retTy} is not GPU-compatible"]
  let bodyErrs := checkCodeGpuCompatibility d.body
  let allErrs := paramErrs ++ retErrs ++ bodyErrs
  let hasParallelOrCand := d.isGpuCand || containsParFor d.body
  if !allErrs.isEmpty then
    (false, allErrs)
  else if !hasParallelOrCand then
    (false, ["declaration has no parFor region and is not marked isGpuCand"])
  else
    (true, [])

private def mkDesc (sym : String) (arch : GPUKernelArchetype) (bufs : Nat)
    (shmem : Nat := 0) (u256 : Bool := false) : GPUKernelDescriptor :=
  { symbolName := sym, archetype := arch, blockThreads := 256,
    sharedMemBytes := shmem, uses256Bit := u256, bufferCount := bufs }

/-- Built-in standard GPU kernel descriptors emitted for every module. -/
def builtinGPUDescriptors : List GPUKernelDescriptor := [
  mkDesc "lean_native_kernel_map_scale_add" .mapScaleAddU64 5,
  mkDesc "lean_native_kernel_zip_add" .zipAddU64 4,
  mkDesc "lean_native_kernel_zip_mul" .zipMulU64 4,
  mkDesc "lean_native_kernel_saxpy" .saxpyU64 5,
  mkDesc "lean_native_kernel_stencil1d" .stencil1D3PtU64 6,
  mkDesc "lean_native_kernel_dot_reduce_u64" .dotReduceSharedU64 4 2048,
  mkDesc "lean_native_kernel_matmul_tiled_u64" .matmulTiled16x16U64 4 4096,
  mkDesc "lean_native_kernel_saxpy_f64" .saxpyF64 5,
  mkDesc "lean_native_kernel_map_scale_add_f64" .mapScaleAddF64 5,
  mkDesc "lean_native_kernel_fma_f32" .fmaF32 5,
  mkDesc "lean_native_kernel_evm_u256_batch" .evmU256Batch 4 0 true,
  mkDesc "lean_native_fastcheck_metal_kernel" .fastCheckFuzzU256 5 0 true
]

/-- Lower an `LNIRModule` into a list of unified `GPUKernelDescriptor` records covering all
    built-in archetypes and GPU-compatible per-declaration kernels. -/
def lowerModuleToGPUDescriptors (m : LNIRModule) : List GPUKernelDescriptor :=
  let declDescs := m.decls.foldl (fun acc d =>
    let (ok, _) := analyzeDeclGpuSuitability d
    if !ok then acc
    else
      let is256 := d.retTy.is256Bit || d.params.any (fun p => p.ty.is256Bit || p.ty == .storageMap)
      let regions := extractParForRegions d.body
      let hasDot := d.name == "dot_product_u64" || regions.any (fun (_, _, _, _, k) =>
        match k with | .dotProduct => true | _ => false)
      let hasMatmul := d.name == "matmul_tiled_u64"
      let hasShared := hasDot || hasMatmul
      let sharedBytes := if hasMatmul then 4096 else if hasDot then 2048 else 0
      let bufCount := if d.params.isEmpty then 3 else d.params.length + 1
      acc ++ [{
        symbolName     := s!"lean_native_decl_{d.name}"
        archetype      := .declCustom d.name hasShared is256
        blockThreads   := 256
        sharedMemBytes := sharedBytes
        uses256Bit     := is256
        bufferCount    := bufCount
      }]
  ) []
  builtinGPUDescriptors ++ declDescs

end LeanNative.Backend.GPUIR
