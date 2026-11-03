import LeanNative.Backend.MetalLower
import LeanNative.Backend.MetalAst

namespace LeanNative.Tests.MetalLowerTests

open LeanNative.IR
open LeanNative.Backend.MetalAst
open LeanNative.Backend.MetalLower

def hasSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

def runMetal1D (k : ParallelKernelKind) (inputs : List (List UInt64)) (len : Nat) :
    MSLOutcome (List (BitVec 64)) :=
  let kern := lowerKind "test_metal" k
  let inBufs := (List.range inputs.length).map fun j =>
    let ws := (inputs[j]?.getD []).map UInt64.toBitVec
    (j, ByteMemory.ofU64Words ws)
  let devBufs := mkDeviceBuffers inBufs (kernelArity k) len
  let constBufs := mkConstLenBuffers (kernelArity k) len
  let grid : Dim3 := { x := 1, y := 1, z := 1 }
  let grp : Dim3 := { x := Nat.max 1 len, y := 1, z := 1 }
  match evalMSLKernel (groupStepsForKind (Nat.max 1 len) k) kern grid grp devBufs constBufs [] [] with
  | .ok bufsF =>
    match bufsF.lookup (kernelArity k) with
    | some outMem =>
      .ok ((List.range len).map fun i => (outMem.readU64Word? i).getD 0#64)
    | none => .unboundIdentifier "out"
  | .divisionByZero => .divisionByZero
  | .fuelExhausted => .fuelExhausted
  | _ => .unboundIdentifier "err"

#guard runMetal1D (.mapScaleAdd 3 7) [[10, 20]] 2 == .ok [37#64, 67#64]
#guard runMetal1D .zipAdd [[4, 9], [5, 11]] 2 == .ok [9#64, 20#64]
#guard runMetal1D .zipMul [[4, 9], [5, 11]] 2 == .ok [20#64, 99#64]
#guard runMetal1D (.saxpy 5) [[2, 3], [7, 8]] 2 == .ok [17#64, 23#64]
#guard runMetal1D (.stencil1D3Pt 1 2 1) [[10, 20, 30]] 3 == .ok [10#64, 80#64, 30#64]
#guard runMetal1D (.customScalar 0 [1, 2] (.binOp .div (.var 1) (.var 2))) [[18, 7], [3, 0]] 2 ==
  .ok [6#64, 0#64]
#guard runMetal1D (.customScalar 0 [1, 2] (.binOp .shl (.var 1) (.var 2))) [[1, 1], [32, 65]] 2 ==
  .ok [4294967296#64, 2#64]
#guard hasSubstr (ppLowered "k_div" (.customScalar 0 [1, 2] (.binOp .div (.var 1) (.var 2)))) "?"
#guard evalMSLKernel 9
    (metalMutantM9Kernel "m9" 0 [1, 2] (.binOp .div (.var 1) (.var 2)))
    { x := 1, y := 1, z := 1 } { x := 1, y := 1, z := 1 }
    (mkDeviceBuffers [(0, ByteMemory.ofU64Words [7#64]), (1, ByteMemory.ofU64Words [0#64])] 2 1)
    (mkConstLenBuffers 2 1) [] [] == .divisionByZero

end LeanNative.Tests.MetalLowerTests
