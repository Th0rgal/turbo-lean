import LeanNative.Backend.PTXLower
import LeanNative.Backend.PTXAst

namespace LeanNative.Tests.PTXLowerTests

open LeanNative.IR
open LeanNative.Backend.PTXAst
open LeanNative.Backend.PTXLower

def hasSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

def runPTX1D (k : ParallelKernelKind) (inputs : List (List UInt64)) (len : Nat) :
    PTXOutcome (List (BitVec 64)) :=
  let kern := lowerKind "test_ptx" k
  let inWords := inputs.map (·.map UInt64.toBitVec)
  let nIn := kernelArity k
  let gMem := mkPTXGlobalMem inWords nIn len
  let pMem := mkPTXParamMem nIn len
  let grid : Dim3 := { x := 1, y := 1, z := 1 }
  let blk : Dim3 := { x := Nat.max 1 len, y := 1, z := 1 }
  match evalPTXKernel (ctaStepsForKind (Nat.max 1 len) k) kern grid blk gMem pMem with
  | .ok gFinal =>
    .ok ((List.range len).map fun i => (gFinal.loadBits (nIn * len * 8 + i * 8) 8).getD 0#64)
  | .fuelExhausted => .fuelExhausted
  | .divisionByZero => .divisionByZero
  | _ => .unboundReg "err"

#guard runPTX1D (.mapScaleAdd 3 7) [[10, 20]] 2 == .ok [37#64, 67#64]
#guard runPTX1D .zipAdd [[4, 9], [5, 11]] 2 == .ok [9#64, 20#64]
#guard runPTX1D .zipMul [[4, 9], [5, 11]] 2 == .ok [20#64, 99#64]
#guard runPTX1D (.saxpy 5) [[2, 3], [7, 8]] 2 == .ok [17#64, 23#64]
#guard runPTX1D (.stencil1D3Pt 1 2 1) [[10, 20, 30]] 3 == .ok [10#64, 80#64, 30#64]
#guard runPTX1D (.customScalar 0 [1, 2] (.binOp .sub (.var 1) (.var 2))) [[1, 9], [2, 4]] 2 ==
  .ok [18446744073709551615#64, 5#64]
#guard runPTX1D (.customScalar 0 [1, 2] (.binOp .lt (.var 1) (.var 2))) [[3, 2], [3, 5]] 2 ==
  .ok [0#64, 1#64]
#guard runPTX1D (.customScalar 0 [1, 2] (.binOp .div (.var 1) (.var 2))) [[18, 7], [3, 0]] 2 ==
  .ok [6#64, 0#64]
#guard runPTX1D (.customScalar 0 [1, 2] (.binOp .shl (.var 1) (.var 2))) [[1, 1], [32, 65]] 2 ==
  .ok [4294967296#64, 2#64]
#guard hasSubstr (ppLowered "k_sub" (.customScalar 0 [1, 2] (.binOp .sub (.var 1) (.var 2)))) "sub.u64"
#guard hasSubstr (ppLowered "k_lt" (.customScalar 0 [1, 2] (.binOp .lt (.var 1) (.var 2)))) "setp.lt.u64"

end LeanNative.Tests.PTXLowerTests
