import LeanNative.Driver.CAbiEmit
import LeanNative.Backend.Hybrid
import LeanNative.Backend.Metal
import LeanNative.Backend.MLIRGPU
import LeanNative.Proofs.HybridCAbiProofs
import LeanNative.Semantics.Value

namespace LeanNative.Tests.HybridCAbiTests

open LeanNative.IR
open LeanNative.Semantics
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
      params := [
        { name := "data", ty := .ptr },
        { name := "len", ty := .usize },
        { name := "alpha", ty := .f64 }
      ],
      retTy := some .u32 },
    { cSymbol := "lean_native_flush_slice",
      params := [{ name := "slice", ty := .mutSlice }],
      retTy := none } ]

#guard match emitValidatedC99Bundle [("lean_native_packet_t", mixedStructSpecs)] sampleFnSigs with
  | some (hdr, shim) =>
    (hdr.splitOn "typedef struct lean_native_packet_t {").length > 1 &&
    (hdr.splitOn "uint64_t count; /* offset 8, size 8, align 8 */").length > 1 &&
    (hdr.splitOn "sizeof(lean_native_packet_t) = 24; alignof(lean_native_packet_t) = 8").length > 1 &&
    (hdr.splitOn "_Static_assert(sizeof(lean_native_packet_t) == 24,").length > 1 &&
    (hdr.splitOn "_Static_assert(_Alignof(lean_native_packet_t) == 8,").length > 1 &&
    (hdr.splitOn "_Static_assert(offsetof(lean_native_packet_t, count) == 8,").length > 1 &&
    (hdr.splitOn "uint32_t lean_native_scale_slice(void* data, size_t len, double alpha);").length > 1 &&
    (hdr.splitOn "void lean_native_flush_slice(lean_native_mut_slice_t slice);").length > 1 &&
    (shim.splitOn "uint32_t lean_native_scale_slice_c99_shim(void* data, size_t len, double alpha)").length > 1 &&
    (shim.splitOn "return lean_native_scale_slice(data, len, alpha);").length > 1 &&
    (shim.splitOn "void lean_native_flush_slice_c99_shim(lean_native_mut_slice_t slice)").length > 1 &&
    (shim.splitOn "  lean_native_flush_slice(slice);").length > 1
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
    unmarshalSlice sampleByteView payload == some backingBytes
  | none => false

#guard marshalSlice { bytes := backingBytes, base := 8, len := 2, elemSize := 4 } == none

/-- Strided view (`byteStride = 4 > elemSize = 2`): only the addressed bytes are packed and restored. -/
def stridedByteView : C99ByteView :=
  { bytes := backingBytes, base := 0, len := 3, byteStride := 4, elemSize := 2, align := 1 }

#guard match marshalSlice stridedByteView with
  | some payload =>
    payload == ByteArray.mk #[10, 11, 14, 15, 18, 19] &&
    unmarshalSlice stridedByteView payload == some backingBytes
  | none => false

#guard match computeC99StructLayout "lean_native_flat_slice_t" flatSliceFieldSpecs .bits32 with
  | some layout => layout.structAlign == 4 && layout.structSize == 12
  | none => false

#guard checkedStridedSpan (2 ^ 30) 8 8 .bits32 == none
#guard checkedStridedSpan 4 8 8 .bits32 == some 32

def backingFloats : FloatArray := FloatArray.mk #[1.5, 2.5, 3.5, 4.5, 5.5]
def sampleFloatView : C99FloatView := { floats := backingFloats, base := 1, len := 3 }

#guard match marshalFloatSlice sampleFloatView with
  | some payload =>
    payload == #[2.5, 3.5, 4.5] &&
    unmarshalFloatSlice backingFloats 1 payload == some backingFloats
  | none => false

#guard hybridTargetPlans.length == 3
#guard hybridTargetPlans.all fun tp =>
  let expectedElems := if tp.target == .gpuMetal then metalDispatchFloor else 256
  match validateHybridDispatch tp.request with
  | .ok plan =>
    plan.target == tp.target &&
    plan.gridThreads == expectedElems &&
    plan.workloadElems == expectedElems &&
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

def metalUnalignedPageBuf : DeviceBufferDesc := {
  name := "metal_unaligned_page", elemBytes := 8, numElems := metalDispatchFloor, byteStride := 8, baseAlign := 8,
  direction := .hostToDevice, zeroCopy := true, rc := 2, baseAddr := 4096, ownership := .pinnedHostRef
}

#guard isDispatchErr (validateHybridDispatch { (sampleHybridRequest .gpuMetal) with buffers := [metalUnalignedPageBuf] }) .bufferGeometry

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
  | .ok _ => false
  | .error err => err == .aliasedOutput

/-- Operational RC lifecycle: pinning a unique live buffer raises `rc` from 1 to 2 and the full
    `pin -> launch -> sync -> release` cycle restores `rc = 1` and `exclusive = true`. -/
def lifecycleHeap : HeapState :=
  { buffers := [{ id := inPlaceBuf.bufId, data := #[7], exclusive := true }], nextId := inPlaceBuf.bufId + 1 }

#guard match pinBufferStep inPlaceBuf.transferMode inPlaceBuf lifecycleHeap with
  | .ok stPinned =>
    match stPinned.findBuffer inPlaceBuf.bufId with
    | some buf => stPinned.getBufRefCount buf == 2
    | none => false
  | .error _ => false

#guard match execHybridTransferLifecycle inPlaceBuf.transferMode inPlaceBuf lifecycleHeap with
  | .ok stFinal =>
    match stFinal.findBuffer inPlaceBuf.bufId with
    | some buf => stFinal.getBufRefCount buf == 1 && buf.exclusive == true && buf.data == #[7]
    | none => false
  | .error _ => false

/-- End-to-end LNIR C-ABI signature coverage across scalar, pointer, 256-bit, and unit types:
    every `moduleToCAbiSigs` entry converts cleanly through `CAbiBindingSig.toC99FnSig` (`some fnSig`). -/
def diverseCAbiModule : LNIRModule := {
  moduleName := "DiverseCAbi"
  decls := [
    { name := "kern_sarray"
      params := [
        { id := 0, name := "x", ty := .sarray .i64 },
        { id := 1, name := "len", ty := .usize },
        { id := 2, name := "alpha", ty := .f64 },
        { id := 3, name := "beta", ty := .f32 },
        { id := 4, name := "flag", ty := .i1 },
        { id := 5, name := "word", ty := .u256 }
      ]
      retTy := .i32
      body := .ret 4 },
    { name := "kern_void_sink"
      params := [
        { id := 0, name := "u", ty := .unit },
        { id := 1, name := "h", ty := .i16 }
      ]
      retTy := .unit
      body := .ret 0 }
  ]
}

#guard (moduleToCAbiSigs sampleHybridModule).all (fun s => s.toC99FnSig.isSome)
#guard (moduleToCAbiSigs diverseCAbiModule).all (fun s => s.toC99FnSig.isSome)
#guard ((emitCAbiHeader diverseCAbiModule .x86_64).splitOn "sizeof(lean_native_flat_slice_t) == 24").length > 1
#guard ((emitCAbiHeader diverseCAbiModule .wasm32).splitOn "sizeof(lean_native_flat_slice_t) == 12").length > 1
#guard ((emitCAbiHeader diverseCAbiModule .wasm32).splitOn "#if defined(__wasm32__)").length > 1

#guard execValidatedSliceHostCall stridedByteView id == some backingBytes
#guard execValidatedSliceHostCall stridedByteView
    (fun packed => ByteArray.mk (packed.data.map (· + 1))) ==
  some (ByteArray.mk #[11, 12, 12, 13, 15, 16, 16, 17, 19, 20, 20, 21])
#guard execValidatedSliceHostCall { stridedByteView with align := 0 } id == none
#guard execValidatedSliceHostCall { stridedByteView with base := 1, align := 4 } id == none

def bundleStructsForClang : List (String × List C99FieldSpec) :=
  [ ("lean_native_flat_slice_t", flatSliceFieldSpecs),
    ("lean_native_mut_slice_t", mutSliceFieldSpecs),
    ("lean_native_packet_t", mixedStructSpecs) ]

def stripPragmaOnce (src : String) : String :=
  String.intercalate "\n" ((src.splitOn "\n").filter (fun ln => ln.trimAscii.toString != "#pragma once"))

def runClangC11ConformanceSuite : IO Unit := do
  let some (hdr64, shim64) := emitValidatedC99Bundle bundleStructsForClang sampleFnSigs .bits64
    | throw <| IO.userError "emitValidatedC99Bundle .bits64 returned none"
  let some (hdr32, shim32) := emitValidatedC99Bundle bundleStructsForClang sampleFnSigs .bits32
    | throw <| IO.userError "emitValidatedC99Bundle .bits32 returned none"
  let modHdr64 := stripPragmaOnce (emitCAbiHeader diverseCAbiModule .x86_64)
  let modHdr32 := stripPragmaOnce (emitCAbiHeader diverseCAbiModule .wasm32)
  let dualHdr := stripPragmaOnce (emitCAbiHeaderFromSigs (moduleToCAbiSigs diverseCAbiModule))
  let checks : List (String × String × TargetArch) := [
    ("bundle-hdr-64", stripPragmaOnce hdr64, .x86_64),
    ("bundle-shim-64", shim64, .x86_64),
    ("bundle-combined-64", stripPragmaOnce hdr64 ++ "\n" ++ shim64, .x86_64),
    ("bundle-hdr-32", stripPragmaOnce hdr32, .wasm32),
    ("bundle-shim-32", shim32, .wasm32),
    ("bundle-combined-32", stripPragmaOnce hdr32 ++ "\n" ++ shim32, .wasm32),
    ("emitCAbiHeader-x86_64", modHdr64, .x86_64),
    ("emitCAbiHeader-wasm32", modHdr32, .wasm32),
    ("emitCAbiHeaderFromSigs-dual-x86_64", dualHdr, .x86_64),
    ("emitCAbiHeaderFromSigs-dual-wasm32", dualHdr, .wasm32)
  ]
  for (label, src, arch) in checks do
    let (ok, err) ← c11SyntaxCheck src arch
    if !ok then
      throw <| IO.userError s!"clang C11 syntax/layout check failed for {label} ({arch.triple}): {err}"

#eval runClangC11ConformanceSuite

end LeanNative.Tests.HybridCAbiTests
