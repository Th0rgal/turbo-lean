import LeanNative.IR.UnboxedRegion
import LeanNative.Proofs.CertChecker
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

def sampleShadowCode : LNIRCode :=
  .incRef 1 2
    (.letBind 1 .objPtr (.allocCtor 0 [] [])
      (.decRef 1 1 (.ret 1)))

def sampleChannel : SendableChannelState :=
  { senderOwned := [10, 11], inFlight := [], receiverOwned := [20] }

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
def sampleAlignedSlice : BorrowedRegionSlice :=
  { ptrVar := 7
    view := { backingLen := 16, offset := 8, len := 8 }
    own := .borrowed }

def packedU32Layout : UnboxedStructLayout :=
  mkUnboxedStructLayout "u32_pair" [{ name := "a", kind := .u32 }, { name := "b", kind := .u32 }]

#guard lowerUnboxedRegionRcFree 0 1 2 sampleLayout sampleSlice 5 = true
#guard (lowerBorrowedSliceLoad 0 2 1 sampleSlice (.ret 0)).isNone = true
#guard (lowerBorrowedSliceLoad 0 2 1 sampleAlignedSlice (.ret 0)).isSome = true
#guard packedU32Layout.stride = 8
#guard checkThreadLocalNonEscaping 9 (.ret 4) = true
#guard checkThreadLocalNonEscaping 4 (.ret 4) = false
#guard checkThreadLocalNonEscaping 1 (.letBind 0 .i64 (.call "lean_mark_mt" [1] .i64 false) (.ret 2)) = true
#guard checkThreadLocalNonEscaping 1 (.letBind 0 .i64 (.scalar (.var 1)) (.ret 0)) = false
#guard (emitMarkMtHeader "old" (.reg "p") 9 (.ret 4)).isEmpty = true
#guard (emitMarkMtHeader "old" (.reg "p") 4 (.ret 4)).length = 1
#guard (sendSlot sampleChannel 10 9 (.ret 4) 0 true).isSome = true
#guard (sendSlot sampleChannel 10 9 (.ret 4) 2 false).isSome = true
#guard (sendSlot sampleChannel 10 4 (.ret 4) 0 true).isNone = true
#guard (sendSlot sampleChannel 99 9 (.ret 4) 0 true).isNone = true
#guard (match sendSlot sampleChannel 10 9 (.ret 4) 0 true with
  | some ch1 => match recvSlot ch1 10 with
    | some (slot, ch2) => slot.mode == .uniqueZeroCopy && channelDisjoint ch2
    | none => false
  | none => false) = true
#guard (elideMarkMtAndZeroRc sampleCode ==
  .letBind 0 .i64 (.scalar (.constU64 0)) (.decRef 3 1 (.ret 4)))
#guard (elideBorrowedAndThreadLocalRC 1 sampleShadowCode ==
  .letBind 1 .objPtr (.allocCtor 0 [] []) (.decRef 1 1 (.ret 1)))
#guard LeanNative.Proofs.isRegisteredTheorem verifiedThreadLocalRCContract.theoremRef = true
#guard (lowerSimdBuildVec "v" .v2i64 [.constInt .i64 5#64, .constInt .i64 9#64]).length = 2
#guard (lowerBorrowedSliceLoad 0 2 1
  { sampleAlignedSlice with view := { sampleAlignedSlice.view with offset := 1 } }
  (.ret 0)).isNone = true
#guard (lowerUnboxedFieldStore 0 1 2 3
  { field := { name := "x", kind := .u32 }, offset := 0, size := 4, align := 4 }
  (.ret 0)).isSome = true
#guard checkThreadLocalNonEscaping 1
  (.letBind 2 .objPtr (.call "lean_native_ensure_exclusive" [1] .objPtr false) (.ret 2)) = false
#guard checkThreadLocalNonEscaping 1 (.letBind 2 .objPtr (.projTuple 1 0) (.ret 2)) = false
#guard checkThreadLocalNonEscaping 1 (.letBind 2 .objPtr (.allocCtor 0 [1] []) (.ret 0)) = false
#guard checkThreadLocalNonEscaping 1 (.letBind 2 .i64 (.sarrayLen 1) (.ret 2)) = true
#guard (match recvSlot sampleChannel 10 with | some _ => true | none => false) = false
#guard (match sendSlot sampleChannel 10 9 (.ret 4) 0 true with
  | some ch1 => match recvSlot ch1 10 with
    | some (_, ch2) =>
      ch2.inFlight.any (·.objId == 10) == false && ch2.receiverOwned.contains 10
    | none => false
  | none => false) = true

end LeanNative.Tests
