import Lean
import LeanNative.Driver.EvalLCNFCLI

/-!
# H1.1 Differential Tests: `RealLCNFSemantics` vs. Lean Compiled & Kernel Reference Evaluation

Verifies:
1. Positive parity on the built-in corpus (`mismatch_count == 0`, compiled IR reference used per declaration,
   `agreed_failure_count` tracked separately from `mismatch_count`, `reference_evaluates_project_refuses_count`
   reported explicitly, per-reason skip names, and construct counts matching asserted kinds).
2. Killing mutant test: flipping a `UInt64` binary operation on the project side via `TestOnlyFaultHook`
   (not exposed on the CLI) produces `mismatch_count > 0` and non-zero exit status `1` on the exact same corpus.
3. Agreed-failure classification: both sides failing in the same failure class increments `agreed_failure_count`
   with `mismatch_count == 0`, while discordant failure classes increment `mismatch_count`.
-/

namespace LeanNative.Tests.EvalLCNFCLITests

open LeanNative.Driver.EvalLCNFCLI

#eval show IO Unit from do
  -- 1. Baseline corpus run
  let rep ← runBuiltinCorpusIO
  IO.println rep.formatSummary
  if rep.mismatchCount != 0 then
    throw <| IO.userError s!"expected mismatch_count == 0, got {rep.mismatchCount}"
  if rep.comparedCount < 12 then
    throw <| IO.userError s!"expected compared_count >= 12, got {rep.comparedCount}"
  if rep.comparedVectors < 100 then
    throw <| IO.userError s!"expected compared_vectors >= 100, got {rep.comparedVectors}"
  if rep.skippedCount < 4 then
    throw <| IO.userError s!"expected skipped_count >= 4, got {rep.skippedCount}"
  if rep.referenceEvaluatesProjectRefusesCount == 0 then
    throw <| IO.userError "expected reference_evaluates_project_refuses_count > 0 for skipped computable declarations"
  for (dName, refUsed) in rep.declReferences do
    if refUsed != "compiled_ir_and_kernel_reduction" && refUsed != "compiled_ir" then
      throw <| IO.userError s!"expected compiled reference for `{dName}`, got `{refUsed}`"
  for reqReason in ["non_computable", "io", "higher_order_or_closures", "unsupported_construct"] do
    let cnt := (rep.skippedByReason.find? (fun (k, _) => k == reqReason)).map Prod.snd |>.getD 0
    if cnt == 0 then
      throw <| IO.userError s!"expected non-zero skip count for reason `{reqReason}`"
    let names := (rep.skippedNamesByReason.find? (fun (k, _) => k == reqReason)).map Prod.snd |>.getD []
    if names.length != cnt then
      throw <| IO.userError s!"expected skippedNamesByReason[{reqReason}] length {cnt}, got {names.length}"
  let assertedConstructs := [
    "let_fap", "fap_scalar_binop", "let_lit", "lit_uint64", "lit_uint8", "lit_uint16",
    "fap_cast_or_other", "fap_uint_unary", "fap_bool_unary_or_cast",
    "jp", "jmp", "cases_adt", "alt_ctor",
    "let_oproj", "let_sproj", "let_ctor", "ctor_obj_fields",
    "let_box", "let_unbox", "return"
  ]
  for reqConstruct in assertedConstructs do
    let cnt := (rep.constructsCovered.find? (fun (k, _) => k == reqConstruct)).map Prod.snd |>.getD 0
    if cnt == 0 then
      throw <| IO.userError s!"expected non-zero construct coverage for `{reqConstruct}`"
  if rep.constructsCovered.length != assertedConstructs.length then
    throw <| IO.userError s!"expected constructs_covered count ({rep.constructsCovered.length}) == asserted count ({assertedConstructs.length})"

  -- 2. Killing test (test-only fault hook, unreachable from normal CLI flags):
  -- Flipping UInt64.add -> UInt64.sub on the project interpreter side MUST produce mismatches and exit status != 0.
  let (killRep, killRc) ← runBuiltinCorpusWithFaultForTesting .flipUInt64AddToSub
  IO.println s!"[eval-lcnf-kill-test] exit_code={killRc} mismatch_count={killRep.mismatchCount}"
  if killRep.mismatchCount == 0 then
    throw <| IO.userError "killing test failed: mutated project interpreter produced mismatch_count == 0"
  if killRc == 0 then
    throw <| IO.userError "killing test failed: mutated project interpreter returned exit status 0"

  -- 3. Agreed-failure vs discordant-failure unit check
  let agreedRep ← runFailureClassificationSelfTestIO
  if agreedRep.agreedFailureCount == 0 || agreedRep.mismatchCount != 0 then
    throw <| IO.userError s!"expected agreed_failure_count > 0 and mismatch_count == 0, got agreed={agreedRep.agreedFailureCount}, mismatch={agreedRep.mismatchCount}"

  -- 4. Normal CLI entrypoint check
  let rc ← LeanNative.Driver.EvalLCNFCLI.run ["--self-test"]
  if rc != 0 then
    throw <| IO.userError s!"EvalLCNFCLI --self-test failed with exit code {rc}"

end LeanNative.Tests.EvalLCNFCLITests
