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
4. The `--self-test` gate accepts the stock corpus report and rejects the mutated corpus report
   (the `--self-test` CLI entrypoint itself runs in `EvalLCNFSelfTestCLITests`).
5. Single-field `structure` wrappers (unboxed by LCNF) and fielded multi-constructor ADTs (tag probe at
   `{keyRoot}_t`) are compared, not skipped, with `mismatch_count == 0`.
6. Merged multi-report JSON keeps skip accounting, and an all-skipped report is never a pass.
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

  -- 4. The `--self-test` gate rejects the killing-mutant corpus report. Every in-process snippet
  --    elaboration re-imports `Lean` (~400 MB that is never released), so the probe runs once and is
  --    shared with section 5, and the `--self-test` CLI entrypoint (which re-runs the corpus and the
  --    probe) is exercised in its own module, `EvalLCNFSelfTestCLITests`, keeping each module's
  --    `lean` process under the untrusted-CI `-M 4096` limit.
  let (compiledRef, kernelRef) ← compiledReferenceSelfProbeIO
  if !(selfTestFailures rep agreedRep compiledRef kernelRef).isEmpty then
    throw <| IO.userError "self-test gate rejected the stock corpus report"
  if (selfTestFailures killRep agreedRep compiledRef kernelRef).isEmpty then
    throw <| IO.userError "self-test gate accepted the killing-mutant corpus report"

  -- 5. Reviewer point B1, evidence half: the compiled-IR reference really executes Lean's
  --    compiled evaluator. `CompiledRefProbe.probeSum` is an `opaque` constant, so kernel
  --    reduction cannot unfold it, while Lean's compiled evaluator computes the exact value
  --    124750 — the reference can be neither kernel reduction nor a stub.
  match compiledRef, kernelRef with
  | .ok cv, .error _ =>
    if cv != CanonicalVal.uint64 124750 then
      throw <| IO.userError s!"B1: compiled reference returned wrong value on kernel-opaque probe: {repr cv}"
  | _, _ =>
    throw <| IO.userError s!"B1: expected compiled-reference success and kernel-reduction failure on the kernel-opaque probe, got compiled={repr compiledRef} kernel={repr kernelRef}"

  -- 6. Reviewer point B1, failing half: the driver module must reach the reference without
  --    `@[implemented_by]` opaque wrappers or `unsafe` reference declarations — the repository
  --    hygiene & axiom gate (`turbo-lean ci-verify`) refuses both in changed source files.
  let driverCandidates ← (["LeanNative/Driver/EvalLCNFCLI.lean", "lean/LeanNative/Driver/EvalLCNFCLI.lean"] :
      List System.FilePath).filterM (fun p => p.pathExists)
  let some driverPath := driverCandidates.head? |
    throw <| IO.userError "B1: could not locate EvalLCNFCLI.lean source for the hygiene scan"
  let driverSrc ← IO.FS.readFile driverPath
  if driverSrc.contains "@[implemented_by" then
    throw <| IO.userError "B1: driver declares `@[implemented_by]` reference wrappers; the hygiene gate refuses them in source files"
  if driverSrc.contains "CompiledUnsafe" then
    throw <| IO.userError "B1: driver declares `unsafe` compiled-reference wrappers; the hygiene gate refuses `unsafe` declarations in source files"

  -- 7. Reviewer points 2 & 4: fielded multi-constructor ADT results (tag probe `{keyRoot}_t`,
  --    fields `{keyRoot}_c{cidx}f{j}`) and single-field structure wrappers (unboxed to their
  --    field by LCNF) are compared against the compiled reference without mismatches. A probe
  --    key-layout drift now surfaces as a `probe_failure` mismatch instead of a silent fallback.
  let witnessSrc := "namespace EvalLCNFReviewWitness

structure Meters where
  val : UInt64

inductive Shape where
  | circle (r : UInt64)
  | rect (w h : UInt64)
  | empty

@[noinline] def metersScale (m : Meters) (k : UInt64) : Meters := ⟨m.val * k + 1⟩

@[noinline] def metersVal (m : Meters) : UInt64 := m.val ^^^ 5

@[noinline] def shapeArea (s : Shape) : UInt64 :=
  match s with
  | .circle r => 3 * r * r
  | .rect w h => w * h
  | .empty => 0

-- `k` keeps every arm input-dependent: a constant arm (`.circle 1`) is hoisted into a
-- `_closed` aux constant, which the project interpreter refuses as an external call.
@[noinline] def shapeGrow (s : Shape) (k : UInt64) : Shape :=
  match s with
  | .circle r => .rect r (r + k)
  | .rect w h => .circle (w + h)
  | .empty => .circle k

end EvalLCNFReviewWitness
"
  let tmpBase := (← IO.getEnv "TMPDIR").getD "/tmp"
  let witnessPath := s!"{tmpBase}/eval-lcnf-review-witness-{← IO.monoMsNow}.lean"
  IO.FS.writeFile witnessPath witnessSrc
  let witnessRep ← tryFinally (runDifferentialOnSourceFile witnessPath) (IO.FS.removeFile witnessPath)
  IO.println witnessRep.formatSummary
  if witnessRep.mismatchCount != 0 then
    throw <| IO.userError s!"review witness: expected mismatch_count == 0, got {witnessRep.mismatchCount}"
  for d in ["metersScale", "metersVal", "shapeArea", "shapeGrow"] do
    let full := s!"EvalLCNFReviewWitness.{d}"
    if !witnessRep.comparedDecls.contains full then
      throw <| IO.userError s!"review witness: `{full}` was not compared (skipped: {witnessRep.skippedDecls.map (·.1)})"
    match witnessRep.declReferences.find? (·.1 == full) with
    | some (_, "compiled_ir_and_kernel_reduction") | some (_, "compiled_ir") => pure ()
    | other => throw <| IO.userError s!"review witness: expected compiled reference for `{full}`, got {other.map (·.2)}"

  -- 8. Reviewer point 5: merged JSON carries skip accounting; an all-skipped report is not a pass.
  let merged := mergedReportsToJson [rep, witnessRep]
  match merged.getObjValAs? Nat "skipped_count", merged.getObjValAs? String "verdict" with
  | .ok n, .ok "pass" =>
    if n != rep.skippedCount + witnessRep.skippedCount then
      throw <| IO.userError s!"merged JSON skipped_count={n}, expected {rep.skippedCount + witnessRep.skippedCount}"
  | _, _ => throw <| IO.userError s!"merged JSON lacks skipped_count or a pass verdict: {merged.compress}"
  let allSkipped := summarizeOutcomes "AllSkipped"
    [.skipped "onlyDecl" .io "IO declaration" false]
  if allSkipped.verdict != "no_comparisons" || exitStatusForReports [allSkipped] == 0 then
    throw <| IO.userError "all-skipped report must not pass"

end LeanNative.Tests.EvalLCNFCLITests
