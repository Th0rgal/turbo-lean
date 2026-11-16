import Lean
import LeanNative.Driver.EvalLCNFCLI

/-!
# H1.1 Differential Tests: `RealLCNFSemantics` vs. Stock Lean Evaluation
-/

namespace LeanNative.Tests.EvalLCNFCLITests

#eval show IO Unit from do
  let rc ← LeanNative.Driver.EvalLCNFCLI.run ["--self-test"]
  if rc != 0 then
    throw <| IO.userError s!"EvalLCNFCLI --self-test failed with exit code {rc}"

end LeanNative.Tests.EvalLCNFCLITests
