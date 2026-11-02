import LeanNative.Backend.MetalAst.Syntax
import LeanNative.Backend.MetalAst.Eval
import LeanNative.Backend.MetalAst.Proofs

/-!
# Genuine Apple Metal MSL 3.0 AST, Independent SIMT Semantics & 1:1 Pretty-Printer (`C2b`)

Umbrella module re-exporting:
- `LeanNative.Backend.MetalAst.Syntax`: typed Metal Shading Language (MSL 3.0) compute AST
  (`MSLAddressSpace`, `MSLType`, `MSLAttr`, `MSLExpr` including `.deref` and short-circuiting
  `.logAnd`/`.logOr`, `MSLStmt` including `.arrayDecl`, `.derefAssign`, `.atomicFetchAdd`,
  `.atomicExchange`, `.simdShuffleXor`, `.simdSum`, `MSLKernelDecl`, `MSLModule`).
- `LeanNative.Backend.MetalAst.Eval`: independent SIMT operational semantics (multi-lane vector and
  user struct storage, C++/MSL integer rank promotion, signed arithmetic shifts, `thread` local
  arrays and pass-by-reference write-back, single-pass simdgroup collectives, atomic vs non-atomic
  barrier-epoch race tracking, depth-10 helper calls with threaded fuel, and 1:1 pretty-printer),
  with zero imports from `LeanNative.Semantics.*`.
- `LeanNative.Backend.MetalAst.Proofs`: kernel-checked SIMT theorems (`0 sorryAx`, `strict-proofs` clean).
-/
