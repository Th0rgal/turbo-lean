import Lean
import LeanNative.Driver.EvalLCNFCLI

/-!
# H1.1 `eval-lcnf --self-test` CLI Entrypoint Test

The `--self-test` CLI entrypoint passes on the stock corpus (exit status `0`).

Kept separate from `EvalLCNFCLITests`: every in-process snippet elaboration re-imports `Lean`
(~400 MB that is never released), and `--self-test` re-runs the corpus and the compiled-reference
probe, so running it in its own module keeps each module's `lean` process under the untrusted-CI
`-M 4096` limit.
-/

namespace LeanNative.Tests.EvalLCNFSelfTestCLITests

#eval show IO Unit from do
  let rc ← LeanNative.Driver.EvalLCNFCLI.run ["--self-test"]
  if rc != 0 then
    throw <| IO.userError s!"EvalLCNFCLI --self-test failed with exit code {rc}"

end LeanNative.Tests.EvalLCNFSelfTestCLITests
