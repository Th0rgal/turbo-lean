import B2.SpecCore
import LeanNative.IR.Codec

/-! Q4 probe: the smallest UInt64 benchmark kernel, `collatz_steps`, against the F₆₄ spec. -/

namespace B2.Kernel
open LeanNative.IR LeanNative.Semantics

/-- `collatz_steps` is in the fragment F₆₄ (decided by the kernel, no `native_decide`). -/
theorem collatz_in_F : declF LeanNative.IR.Codec.collatzStepsDecl = true := by decide

/-- Reference value from the real LNIR evaluator: `n = 3`, `steps = 5` iterates
`acc ↦ (3·acc + 1) / 2` five times: 3 → 5 → 8 → 12 → 18 → 27. -/
theorem collatz_eval_3_5 :
    (match evalCode 0 (entryEnv LeanNative.IR.Codec.collatzStepsDecl [.u64 3, .u64 5]) emptyHeap
      LeanNative.IR.Codec.collatzStepsDecl.body with
     | .ok (.u64 r, _) => some r
     | _ => none) = some 27 := by
  decide

end B2.Kernel
