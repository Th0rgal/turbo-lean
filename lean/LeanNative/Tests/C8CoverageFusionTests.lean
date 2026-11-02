import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.IR.ClosureADT
import LeanNative.IR.SliceView
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Transform.KernelFusion
import LeanNative.Transform.Plugins
import LeanNative.Proofs.CertChecker

namespace LeanNative.Tests.C8CoverageFusionTests

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Transform
open LeanNative.Proofs

/-! ## C8 End-to-End `#guard` Suite: Rich Language Coverage & Verified Loop/Kernel Fusion -/

/-- Helper to extract `(outData, nextId)` from an `.sarrayId` evaluation result. -/
def runSarrayEval (env : VarEnv) (st : HeapState) (code : LNIRCode) : Option (Array UInt64 × Nat) :=
  match evalCode 64 env st code with
  | .ok (.sarrayId bid, st') =>
    (st'.findBuffer bid).map fun b => (b.data, st'.nextId)
  | _ => none

/-- Helper to extract `(u64Val, nextId)` from a scalar `.u64` evaluation result. -/
def runU64Eval (env : VarEnv) (st : HeapState) (code : LNIRCode) : Option (UInt64 × Nat) :=
  match evalCode 64 env st code with
  | .ok (.u64 v, st') => some (v, st'.nextId)
  | _ => none

/-! ### 1. Multi-Stage `parFor` Kernel Fusion & Intra-Kernel Specialization -/

def baseHeap : HeapState :=
  { buffers :=
      [ { id := 1, exclusive := true, data := #[5, 6, 7, 8] }
      , { id := 2, exclusive := true, data := #[10, 20, 30, 40] }
      , { id := 3, exclusive := true, data := #[1, 2, 3, 4] } ]
  , nextId := 10 }

def fusionEnv : VarEnv :=
  (((VarEnv.empty.bind 0 (.u64 4)).bind 1 (.sarrayId 1)).bind 2 (.sarrayId 2)).bind 3 (.sarrayId 3)

/-- 2-stage pipeline: `tmp := mapScaleAdd 3 5 src1; out := mapScaleAdd 2 7 tmp`. -/
def twoStageParFor : LNIRCode :=
  .parFor 11 0 [1] .i64 (.mapScaleAdd 3 5)
    (.parFor 12 0 [11] .i64 (.mapScaleAdd 2 7)
      (.ret 12))

/-- 2-stage pipeline with intermediate RC cleanup `decRef 11 1` after consumer. -/
def twoStageRcParFor : LNIRCode :=
  .parFor 11 0 [1] .i64 (.mapScaleAdd 3 5)
    (.parFor 12 0 [11] .i64 (.mapScaleAdd 2 7)
      (.decRef 11 1 (.ret 12)))

def twoStageFused : LNIRCode := fuseParForCode twoStageParFor

#guard countParForLaunches twoStageParFor == 2
#guard countParForLaunches twoStageFused == 1
#guard countParForLaunches (fuseParForCode twoStageRcParFor) == 2
-- Unfused allocates 2 buffers (`nextId`: 10 -> 12); fused allocates 1 buffer (`nextId`: 10 -> 11)
-- with identical output elements `(x * 3 + 5) * 2 + 7 = x * 6 + 17` on `#[5, 6, 7, 8]`:
#guard runSarrayEval fusionEnv baseHeap twoStageParFor == some (#[47, 53, 59, 65], 12)
#guard runSarrayEval fusionEnv baseHeap twoStageFused == some (#[47, 53, 59, 65], 11)

/-- 3-stage pipeline: `t1 := mapScaleAdd 2 1 src1; t2 := saxpy 3 t1 src2; out := zipAdd t2 src3`. -/
def threeStageParFor : LNIRCode :=
  .parFor 11 0 [1] .i64 (.mapScaleAdd 2 1)
    (.parFor 12 0 [11, 2] .i64 (.saxpy 3)
      (.parFor 13 0 [12, 3] .i64 .zipAdd
        (.ret 13)))

def threeStageFused : LNIRCode := fuseParForCode threeStageParFor

#guard countParForLaunches threeStageParFor == 3
#guard countParForLaunches threeStageFused == 1
-- Unfused allocates 3 buffers (`nextId` = 13); fused allocates 1 buffer (`nextId` = 11):
#guard runSarrayEval fusionEnv baseHeap threeStageParFor == some (#[44, 61, 78, 95], 13)
#guard runSarrayEval fusionEnv baseHeap threeStageFused == some (#[44, 61, 78, 95], 11)

/-- Hazard guard: when `tmpVar = 11` escapes into the return tuple, fusion is rejected. -/
def escapingTmpParFor : LNIRCode :=
  .parFor 11 0 [1] .i64 (.mapScaleAdd 3 5)
    (.parFor 12 0 [11] .i64 (.mapScaleAdd 2 7)
      (.letBind 13 (.tuple [.sarray .i64, .sarray .i64]) (.mkTuple [11, 12]) (.ret 13)))

#guard countParForLaunches (fuseParForCode escapingTmpParFor) == 2

/-- Hazard guard: stencil stage `.stencil1D3Pt` reads neighbor indices `i - 1, i + 1` and is not fused. -/
def stencilHazardParFor : LNIRCode :=
  .parFor 11 0 [1] .i64 (.mapScaleAdd 3 5)
    (.parFor 12 0 [11] .i64 (.stencil1D3Pt 1 2 1) (.ret 12))

#guard countParForLaunches (fuseParForCode stencilHazardParFor) == 2

/-- Intra-kernel specialization via segregated `builtinKernelFusionPlugin` (`verifyOptPluginGate`):
    specializes `.customScalar` `x * 4 + 9` into `.mapScaleAdd 4 9` (`declScalarCost`: `5 -> 0`). -/
def unspecializedDecl : LNIRDecl :=
  { name := "custom_affine_kernel"
  , params := [{ id := 1, name := "src", ty := .sarray .i64 }]
  , retTy := .sarray .i64
  , body := .letBind 0 .i64 (.sarrayLen 1)
      (.parFor 2 0 [1] .i64
        (.customScalar 50 [51] (.binOp .add (.binOp .mul (.var 51) (.constU64 4)) (.constU64 9)))
        (.ret 2)) }

#guard (let (d', accepted, _) := applyVerifiedOptPlugin .x86_64 true (builtinKernelFusionPlugin .x86_64) unspecializedDecl
        accepted && declScalarCost .x86_64 d' < declScalarCost .x86_64 unspecializedDecl)

/-! ### 2. Closure Capture, Defunctionalization, Higher-Order `seqFor`, & Multi-Constructor ADT `match` -/

/-- Closure capturing `bias = 10` folded across `[0, 4)` via `lowerClosureSeqFor`:
    computes `sum_{i=0..3} (i + bias) = 10 + 11 + 12 + 13 = 46`. -/
def closureFoldCode : LNIRCode :=
  let clSpec : ClosureSpec := { codeIdx := 0, fields := [{ src := 0, ty := .i64 }] }
  lowerClosureAlloc 1 clSpec
    (.letBind 2 .i64 (.scalar (.constU64 0))
      (.letBind 3 .i64 (.scalar (.constU64 4))
        (.letBind 4 .i64 (.scalar (.constU64 0))
          (lowerClosureSeqFor 5 2 3 6 4 .i64
            (lowerClosureGetField 7 .i64 1 0
              (.letBind 8 .i64 (.scalar (.binOp .add (.var 5) (.var 7)))
                (.letBind 9 .i64 (.scalar (.binOp .add (.var 6) (.var 8)))
                  (.ret 9))))
            (.ret 6)))))

#guard runU64Eval (VarEnv.empty.bind 0 (.u64 10)) .empty closureFoldCode == some (46, 1)

/-- Multi-constructor ADT `Shape` (`tag 0`: Empty, `tag 1`: Square(s), `tag 2`: Rect(w, h))
    lowered via `lowerAdtMatch` and evaluated on all three constructors. -/
def evalShapeArea (scrut : VarId) : LNIRCode :=
  lowerAdtMatch scrut 20 30
    [ { tag := 0, fields := [], body := .letBind 40 .i64 (.scalar (.constU64 0)) (.ret 40) }
    , { tag := 1, fields := [{ src := 41, ty := .i64 }],
        body := .letBind 42 .i64 (.scalar (.binOp .mul (.var 41) (.var 41))) (.ret 42) }
    , { tag := 2, fields := [{ src := 43, ty := .i64 }, { src := 44, ty := .i64 }],
        body := .letBind 45 .i64 (.scalar (.binOp .mul (.var 43) (.var 44))) (.ret 45) } ]
    .unreachable

def runShapeTag1 : Option (UInt64 × Nat) :=
  let code : LNIRCode :=
    .letBind 1 .i64 (.scalar (.constU64 7))
      (.letBind 2 .objPtr (.allocCtor 1 [1] []) (evalShapeArea 2))
  runU64Eval .empty .empty code

def runShapeTag2 : Option (UInt64 × Nat) :=
  let code : LNIRCode :=
    .letBind 1 .i64 (.scalar (.constU64 6))
      (.letBind 2 .i64 (.scalar (.constU64 9))
        (.letBind 3 .objPtr (.allocCtor 2 [1, 2] []) (evalShapeArea 3)))
  runU64Eval .empty .empty code

def runShapeTag0 : Option (UInt64 × Nat) :=
  runU64Eval (VarEnv.empty.bind 2 (.tuple [.u64 0])) .empty (evalShapeArea 2)

#guard runShapeTag0 == some (0, 0)
#guard runShapeTag1 == some (49, 1)
#guard runShapeTag2 == some (54, 1)

/-! ### 3. Zero-Copy `ByteArraySlice` & `FloatArraySlice` Views, Sub-Slices, & Fold Reductions -/

def sliceBackingHeap : HeapState :=
  { buffers := [{ id := 1, exclusive := true, data := #[100, 10, 20, 30, 40, 200] }], nextId := 5 }

def parentByteSlice : TypedSliceView := mkByteArraySlice 1 6 1 4
def parentFloatSlice : TypedSliceView := mkFloatArraySlice 1 6 2 3

#guard checkSliceViewValid parentByteSlice == true
#guard checkSliceViewValid parentFloatSlice == true
-- Checked nested sub-slice `[1, 1 + 2)` inside `parentByteSlice` (`offset = 2, len = 2`):
#guard (checkedSubSlice parentByteSlice 1 2).map (fun s => (s.view.offset, s.view.len)) == some (2, 2)
-- Out-of-bounds sub-slice `[2, 2 + 3)` inside length-4 slice is rejected (`none`):
#guard checkedSubSlice parentByteSlice 2 3 == none

-- Zero-copy read at index 2 of `parentByteSlice` (`data[1 + 2] = 30`), allocating 0 buffers (`nextId = 5`):
#guard runU64Eval ((VarEnv.empty.bind 1 (.sarrayId 1)).bind 2 (.u64 2)) sliceBackingHeap
  (lowerSliceGet 3 4 parentByteSlice 2 (.ret 3)) == some (30, 5)

-- Zero-copy raw-pointer load on `parentFloatSlice` at index 1 (`data[2 + 1] = 30`), allocating 0 buffers:
#guard runU64Eval ((VarEnv.empty.bind 1 (.rawPtrId 1)).bind 2 (.u64 1)) sliceBackingHeap
  (lowerSliceRawLoad 3 4 parentFloatSlice 2 (.ret 3)) == some (30, 5)

-- Zero-copy fold reduction over `parentByteSlice` (`10 + 20 + 30 + 40 = 100`), allocating 0 buffers (`nextId = 5`):
#guard runU64Eval (VarEnv.empty.bind 1 (.sarrayId 1)) sliceBackingHeap
  (lowerSliceFold parentByteSlice 0 10 11 12 13 14 15 16 17 (.ret 14)) == some (100, 5)

/-! ### 4. Certificate Registry & Pass Wiring Checks -/

#guard isRegisteredTheorem "LeanNative.Proofs.fuseParForKernels_sound" == true
#guard isRegisteredTheorem "LeanNative.Proofs.specializeKernelCode_refines" == true
#guard isRegisteredTheorem "LeanNative.Proofs.defunctionalizeClosure_sound" == true
#guard isRegisteredTheorem "LeanNative.Proofs.lowerAdtMatch_sound" == true
#guard isRegisteredTheorem "LeanNative.Proofs.subSliceBounds_no_oob" == true
#guard isRegisteredTheorem "LeanNative.Proofs.lowerSliceFold_sound" == true
#guard (kernelFusionPass.runDecl { name := "twoStage", params := [], retTy := .sarray .i64, body := twoStageParFor }).2.changed == true

end LeanNative.Tests.C8CoverageFusionTests
