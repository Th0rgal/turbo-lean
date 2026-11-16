import Lean
import LeanNative.Driver.EvalLCNFCLI

/-!
# H1.1 Differential Tests: `RealLCNFSemantics` vs. Stock Lean Evaluation

Verifies that `LeanNative.Driver.EvalLCNFCLI` evaluates elaborated `.impure` LCNF
declarations via `RealLCNFSemantics.evalRealLCNFDecl` and matches stock Lean evaluation
with `mismatch_count == 0`, while reporting `compared_count`, `skipped_count` by reason,
and `constructs_covered`.
-/

namespace LeanNative.Tests.EvalLCNFCLITests

open LeanNative.Driver.EvalLCNFCLI

#eval show IO Unit from do
  let rep ← runBuiltinCorpusIO
  IO.println rep.formatSummary
  if rep.mismatchCount != 0 then
    throw <| IO.userError s!"expected mismatch_count == 0, got {rep.mismatchCount}"
  if rep.comparedCount < 11 then
    throw <| IO.userError s!"expected compared_count >= 11, got {rep.comparedCount}"
  if rep.comparedVectors < 90 then
    throw <| IO.userError s!"expected compared_vectors >= 90, got {rep.comparedVectors}"
  if rep.skippedCount < 4 then
    throw <| IO.userError s!"expected skipped_count >= 4, got {rep.skippedCount}"
  for reqReason in ["non_computable", "io", "higher_order_or_closures", "unsupported_construct"] do
    let cnt := (rep.skippedByReason.find? (fun (k, _) => k == reqReason)).map Prod.snd |>.getD 0
    if cnt == 0 then
      throw <| IO.userError s!"expected non-zero skip count for reason `{reqReason}`"
  for reqConstruct in ["let_fap", "fap_scalar_binop", "let_lit", "jp", "jmp", "cases_adt", "let_oproj", "let_sproj", "let_ctor", "return"] do
    let cnt := (rep.constructsCovered.find? (fun (k, _) => k == reqConstruct)).map Prod.snd |>.getD 0
    if cnt == 0 then
      throw <| IO.userError s!"expected non-zero construct coverage for `{reqConstruct}`"
  let rc ← LeanNative.Driver.EvalLCNFCLI.run ["--self-test"]
  if rc != 0 then
    throw <| IO.userError s!"EvalLCNFCLI --self-test failed with exit code {rc}"

end LeanNative.Tests.EvalLCNFCLITests
