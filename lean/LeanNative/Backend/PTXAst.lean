import LeanNative.Backend.PTXAst.Syntax
import LeanNative.Backend.PTXAst.Eval
import LeanNative.Backend.PTXAst.Proofs

/-!
# Genuine NVIDIA CUDA PTX 8.0 AST, Independent SIMT Semantics & 1:1 Pretty-Printer (`C2b`)

Umbrella module re-exporting:
- `LeanNative.Backend.PTXAst.Syntax`: typed PTX 8.0 ISA AST (`PTXType`, `StateSpace`, `SpecialReg`,
  `PTXOperand`, `PTXInstr` including `atom.add`/`atom.cas`/`shfl.sync.bfly.b32`, `PTXKernel`, `PTXModule`).
- `LeanNative.Backend.PTXAst.Eval`: independent SIMT operational semantics (declared-register width &
  initialization checks, separated `globalMem`/`sharedMem`/`constMem`/`localMem`/`paramMem`, atomic vs
  non-atomic barrier-epoch race detection, warp shuffles, CTA barriers, and 1:1 pretty-printer), with
  zero imports from `LeanNative.Semantics.*`.
- `LeanNative.Backend.PTXAst.Proofs`: kernel-checked SIMT theorems (`0 sorryAx`, `strict-proofs` clean).
-/
