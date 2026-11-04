import LeanNative.IR.UnboxedRegion
import LeanNative.Proofs.UnboxedRegionProofs
import LeanNative.Transform.OwnershipRC

namespace LeanNative.Tests

open LeanNative.IR
open LeanNative.Transform
open LeanNative.Backend.LLVMAst

def sampleLayout : UnboxedStructLayout :=
  mkUnboxedStructLayout "pair" [{ name := "x", kind := .u64 }, { name := "y", kind := .u32 }]

def sampleSlice : BorrowedRegionSlice :=
  { ptrVar := 7
    view := { backingLen := 16, offset := 4, len := 12 }
    own := .borrowed }

def sampleCode : LNIRCode :=
  .letBind 0 .i64 (.call "lean_mark_mt" [1] .i64 false)
    (.incRef 2 0 (.decRef 3 1 (.ret 4)))

#guard layoutWellFormed sampleLayout = true
#guard sampleLayout.headerBytes = 0
#guard sampleLayout.stride = 16
#guard sampleLayout.align = 8
#guard unboxedVsHeapHeader sampleLayout = true
#guard borrowedSliceValid sampleSlice = true
#guard (borrowedSliceSub sampleSlice 2 4).isSome = true
#guard (borrowedSliceSub sampleSlice 8 8).isNone = true
#guard PortableSimdKind.v4i64.bitWidth = 256
#guard portableSimdWidthPreserved .v2i64 = true
#guard portableSimdWidthPreserved .v4i64 = true
#guard portableSimdWidthPreserved .v4f64 = true
#guard portableSimdWidthPreserved .v16i8 = true
#guard lowerUnboxedRegionRcFree 0 1 2 sampleLayout sampleSlice 5 = true
#guard checkThreadLocalNonEscaping 9 (.ret 4) = true
#guard checkThreadLocalNonEscaping 4 (.ret 4) = false
#guard checkSendableTransfer 9 (.ret 4) 1 = true
#guard checkSendableTransfer 9 (.ret 4) 2 = false
#guard (elideMarkMtAndZeroRc sampleCode == .decRef 3 1 (.ret 4))
#guard (simdLaneGet (simdLaneSet [.bits .i64 1#64, .bits .i64 2#64] 0 (.bits .i64 9#64)) 0
    == some (.bits .i64 9#64))

end LeanNative.Tests
