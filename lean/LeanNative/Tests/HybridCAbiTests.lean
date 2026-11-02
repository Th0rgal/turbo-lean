import LeanNative.Driver.CAbiEmit
import LeanNative.Backend.Hybrid
import LeanNative.Backend.Metal
import LeanNative.Backend.MLIRGPU
import LeanNative.Proofs.HybridCAbiProofs

namespace LeanNative.Tests.HybridCAbiTests

open LeanNative.IR
open LeanNative.Driver.CoreCLI
open LeanNative.Backend.Hybrid
open LeanNative.Backend.MLIRGPU
open LeanNative.Backend.Metal
open LeanNative.Proofs.HybridCAbi

def mixedStructSpecs : List C99FieldSpec :=
  [ { name := "tag", ty := .u8 },
    { name := "flags", ty := .u16 },
    { name := "count", ty := .u64 },
    { name := "tail", ty := .u32 } ]

#guard match computeC99StructLayout "lean_native_packet_t" mixedStructSpecs with
  | some layout =>
    layout.structAlign == 8 &&
    layout.structSize == 24 &&
    layout.fields.map (fun f => (f.name, f.offset, f.size, f.align)) ==
      [("tag", 0, 1, 1), ("flags", 2, 2, 2), ("count", 8, 8, 8), ("tail", 16, 4, 4)]
  | none => false

#guard c99AlignUp 17 0 == none
#guard c99AlignUp 17 8 == some 24

def sampleFnSigs : List C99FnSig :=
  [ { cSymbol := "lean_native_scale_slice",
      params := [{ name := "data", ty := .ptr }, { name := "len", ty := .usize }, { name := "alpha", ty := .f64 }],
      retTy := .u32 } ]

#guard match emitValidatedC99Bundle [("lean_native_packet_t", mixedStructSpecs)] sampleFnSigs with
  | some (hdr, shim) =>
    (hdr.splitOn "typedef struct lean_native_packet_t {").length > 1 &&
    (hdr.splitOn "uint64_t count; /* offset 8, size 8, align 8 */").length > 1 &&
    (hdr.splitOn "sizeof(lean_native_packet_t) = 24; alignof(lean_native_packet_t) = 8").length > 1 &&
    (hdr.splitOn "uint32_t lean_native_scale_slice(void* data, size_t len, double alpha);").length > 1 &&
    (shim.splitOn "uint32_t lean_native_scale_slice_c99_shim(void* data, size_t len, double alpha)").length > 1 &&
    (shim.splitOn "return lean_native_scale_slice(data, len, alpha);").length > 1
  | none => false

#guard checkedByteLen 1024 8 == some 8192
#guard checkedByteLen (2 ^ 62) 8 == none

#guard validateC99Slice { dataPtr := some 0x4000, len := 64, byteStride := 8, elemSize := 8, align := 8 } == true
#guard validateC99Slice { dataPtr := none, len := 0, byteStride := 8, elemSize := 8, align := 8 } == true
#guard validateC99Slice { dataPtr := none, len := 4, byteStride := 8, elemSize := 8, align := 8 } == false
#guard validateC99Slice { dataPtr := some 0x4000, len := 4, byteStride := 6, elemSize := 4, align := 4 } == false
#guard validateC99Slice { dataPtr := some 0x4000, len := 4, byteStride := 8, elemSize := 8, align := 0 } == false
#guard validateC99Slice { dataPtr := some 0x4000, len := 2 ^ 62, byteStride := 8, elemSize := 8, align := 8 } == false

def backingBytes : ByteArray := ByteArray.mk #[10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]
def sampleByteView : C99ByteView := { bytes := backingBytes, base := 4, len := 2, elemSize := 4 }

#guard match marshalSlice sampleByteView with
  | some payload =>
    payload == ByteArray.mk #[14, 15, 16, 17, 18, 19, 20, 21] &&
    unmarshalSlice backingBytes 4 payload == some backingBytes
  | none => false

#guard marshalSlice { bytes := backingBytes, base := 8, len := 2, elemSize := 4 } == none

def backingFloats : FloatArray := FloatArray.mk #[1.5, 2.5, 3.5, 4.5, 5.5]
def sampleFloatView : C99FloatView := { floats := backingFloats, base := 1, len := 3 }

#guard match marshalFloatSlice sampleFloatView with
  | some payload =>
    payload == #[2.5, 3.5, 4.5] &&
    unmarshalFloatSlice backingFloats 1 payload == some backingFloats
  | none => false

#guard hybridTargetPlans.length == 3
#guard hybridTargetPlans.all fun tp =>
  match validateHybridDispatch tp.request with
  | .ok plan =>
    plan.target == tp.target &&
    plan.gridThreads == 256 &&
    plan.workloadElems == 256 &&
    plan.buffers.length == 2
  | .error _ => false

def sampleHybridModule : LNIRModule := {
  moduleName := "HybridCAbiE2E"
  decls := [
    { name := "scale_add_u64"
      params := [{ id := 0, name := "x", ty := .sarray .i64 }]
      retTy := .sarray .i64
      body := .parFor 1 0 [0] .i64 (.mapScaleAdd 5 3) (.ret 1) }
  ]
}

def samplePartition : HybridPartitionPlan := partitionModule sampleHybridModule 65536 true

#guard samplePartition.gpuDecls.length == 1
#guard ((emitHybridHostGlue samplePartition).splitOn "lean_native_hybrid_dispatch_scale_add_u64").length > 1
#guard ((emitMetalZeroCopyHostGlue samplePartition).splitOn "MTLResourceStorageModeShared").length > 1
#guard ((emitMetalModule sampleHybridModule).splitOn "kernel void lean_native_metal_decl_scale_add_u64").length > 1
#guard ((emitPTXModule sampleHybridModule).splitOn ".visible .entry").length > 1
#guard ((emitStableHLOModule sampleHybridModule).splitOn "stablehlo").length > 1

def ptxBaseReq : HybridLaunchRequest := sampleHybridRequest .gpuCudaPtx

def isDispatchErr (r : Except HybridDispatchError HybridDispatchPlan) (expected : HybridDispatchError) : Bool :=
  match r with
  | .error err => decide (err = expected)
  | .ok _ => false

#guard isDispatchErr (validateHybridDispatch { ptxBaseReq with gridDim := { x := 0, y := 1, z := 1 } }) .zeroGrid
#guard isDispatchErr (validateHybridDispatch { ptxBaseReq with blockDim := { x := 2048, y := 1, z := 1 } }) .blockTooLarge
#guard isDispatchErr (validateHybridDispatch { ptxBaseReq with workloadElems := 512, tailGuarded := true }) .incompleteCoverage
#guard isDispatchErr (validateHybridDispatch { ptxBaseReq with workloadElems := 200, tailGuarded := false }) .incompleteCoverage

def unalignedBuf : DeviceBufferDesc := {
  name := "bad_align", elemBytes := 8, numElems := 256, byteStride := 8, baseAlign := 16,
  direction := .hostToDevice, zeroCopy := false, rc := 1, baseAddr := 8, ownership := .borrowedByDevice
}

#guard isDispatchErr (validateHybridDispatch { ptxBaseReq with buffers := [unalignedBuf] }) .bufferGeometry

def sharedOutBuf : DeviceBufferDesc := {
  name := "shared_out", elemBytes := 8, numElems := 256, byteStride := 8, baseAlign := 8,
  direction := .deviceToHost, zeroCopy := false, rc := 2, baseAddr := 4096, ownership := .uniqueOutBuffer
}

#guard isDispatchErr (validateHybridDispatch { ptxBaseReq with buffers := [sharedOutBuf] }) .ownership

def aliasedInBuf : DeviceBufferDesc := {
  name := "in_overlap", elemBytes := 8, numElems := 256, byteStride := 8, baseAlign := 8,
  direction := .hostToDevice, zeroCopy := false, rc := 1, baseAddr := 0, ownership := .borrowedByDevice
}
def aliasedOutBuf : DeviceBufferDesc := {
  name := "out_overlap", elemBytes := 8, numElems := 256, byteStride := 8, baseAlign := 8,
  direction := .deviceToHost, zeroCopy := false, rc := 1, baseAddr := 1024, ownership := .uniqueOutBuffer
}

#guard isDispatchErr (validateHybridDispatch { ptxBaseReq with buffers := [aliasedInBuf, aliasedOutBuf] }) .aliasedOutput

def inPlaceBuf : DeviceBufferDesc := {
  name := "io0", elemBytes := 8, numElems := 256, byteStride := 16, baseAlign := 16,
  direction := .inOut, zeroCopy := true, rc := 1, baseAddr := 16384, ownership := .uniqueOutBuffer
}

#guard match validateHybridDispatch { (sampleHybridRequest .gpuMetal) with
    workloadElems := 200, buffers := [inPlaceBuf, inPlaceBuf] } with
  | .ok plan =>
    plan.gridThreads == 256 &&
    rcNetDelta (rcPhaseOf inPlaceBuf) == 0 &&
    rcNetDelta (rcPhaseOf aliasedInBuf) == 0 &&
    (rcPhaseOf aliasedInBuf).whileActive == some 2 &&
    (rcPhaseOf inPlaceBuf).afterRelease == 1
  | .error _ => false

end LeanNative.Tests.HybridCAbiTests
