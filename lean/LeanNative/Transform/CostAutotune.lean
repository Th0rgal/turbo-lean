import LeanNative.Transform.Pass
import LeanNative.Transform.Superopt
import LeanNative.Spec

namespace LeanNative.Transform

open LeanNative.IR

export _root_.LeanNative.Spec (CorpusTimingSample meetsOnePercentE2EGain corpusProdBaseline
  corpusProdCandidate meetsCorpusGeomeanOnePercentGain CandidateAblationSample
  candidateAblationSurvives keepSiteByAblations)

structure OpTimingSample where
  operation : String
  elapsedNs : Nat
  iterations : Nat
  deriving Repr, DecidableEq, Inhabited, BEq

def canonicalTimingOperation : String → String
  | "add" | "sub" | "addSub" | "add_sub" => "add_sub"
  | "bitAnd" | "bitOr" | "bitXor" | "not" | "neg" => "bitwise"
  | "shl" | "shr" | "sar" => "shift"
  | "eq" | "lt" | "le" => "cmp"
  | "div" | "mod" | "divMod" | "div_mod" => "div_mod"
  | "addChecked256" | "subChecked256" | "addSubChecked256" | "add_sub_checked256" =>
    "add_sub_checked256"
  | "mulChecked256" | "mul_checked256" => "mul_checked256"
  | operation => operation

def operationMedianNs? (samples : List OpTimingSample) (operation : String) : Option Nat :=
  let values := samples.filterMap fun s =>
    if s.iterations > 0 && s.elapsedNs > 0 &&
        canonicalTimingOperation s.operation == canonicalTimingOperation operation then
      some (max 1 (s.elapsedNs / s.iterations))
    else none
  let sorted := values.mergeSort (fun a b => a ≤ b)
  if sorted.isEmpty then none
  else
    let upper := sorted[sorted.length / 2]?.getD 1
    let lower := sorted[(sorted.length - 1) / 2]?.getD 1
    some ((lower + upper) / 2)

def calibrateHardwareProfile (base : HardwareCostProfile) (samples : List OpTimingSample) :
    HardwareCostProfile :=
  let unit := (operationMedianNs? samples "add_sub").getD 1
  let cost := fun operation preset =>
    match operationMedianNs? samples operation with
    | some ns => max 1 (ns / unit)
    | none => max 1 preset
  { base with
    addSubCost := cost "add_sub" base.addSubCost
    bitwiseCost := cost "bitwise" base.bitwiseCost
    shiftCost := cost "shift" base.shiftCost
    cmpCost := cost "cmp" base.cmpCost
    mulCost := cost "mul" base.mulCost
    divModCost := cost "div_mod" base.divModCost
    fmaCost := cost "fma" base.fmaCost
    selectCost := cost "select" base.selectCost
    clz256Cost := cost "clz256" base.clz256Cost
    addSubChecked256Cost := cost "add_sub_checked256" base.addSubChecked256Cost
    mulChecked256Cost := cost "mul_checked256" base.mulChecked256Cost
    minGpuElements := max 1 base.minGpuElements
    gpuBlockThreads := max 1 base.gpuBlockThreads
    matmulTileDim := max 1 base.matmulTileDim }

def HardwareCostProfile.toJson (p : HardwareCostProfile) : String :=
  let strings := [
    ("profile_id", p.profileId), ("target", p.target.toString),
    ("llvm_target_cpu", p.llvmTargetCpu), ("sm_arch", p.smArch)]
  let numbers := [
    ("add_sub_cost", p.addSubCost), ("bitwise_cost", p.bitwiseCost),
    ("shift_cost", p.shiftCost), ("cmp_cost", p.cmpCost),
    ("mul_cost", p.mulCost), ("div_mod_cost", p.divModCost),
    ("fma_cost", p.fmaCost), ("select_cost", p.selectCost),
    ("clz256_cost", p.clz256Cost), ("add_sub_checked256_cost", p.addSubChecked256Cost),
    ("mul_checked256_cost", p.mulChecked256Cost), ("min_gpu_elements", p.minGpuElements),
    ("gpu_block_threads", p.gpuBlockThreads), ("matmul_tile_dim", p.matmulTileDim)]
  let selection := match p.keptSites? with
    | none => []
    | some sites => ["\"kept_sites\":[" ++ String.intercalate "," (sites.map fun (decl, site) =>
        "{\"decl\":\"" ++ jsonEscape decl ++ "\",\"site\":" ++ toString site ++ "}") ++ "]"]
  "{" ++ String.intercalate "," (
    strings.map (fun (key, value) => "\"" ++ key ++ "\":\"" ++ jsonEscape value ++ "\"") ++
    numbers.map (fun (key, value) => "\"" ++ key ++ "\":" ++ toString value) ++ selection) ++ "}"

def superoptModuleWithProfile (p : HardwareCostProfile) (m : LNIRModule) : LNIRModule × SuperoptReport :=
  let (candidate, report, _) := superoptModuleSelective p
    (fun decl idx => p.keptSites?.all (fun sites => sites.contains (decl, idx))) m
  (candidate, report)

def keepDeclSiteByAblations (ablations : List CandidateAblationSample) (decl : String)
    (expectedPairs : Nat := 1) : Nat → Bool :=
  fun idx => keepSiteByAblations (ablations.filter (fun s => s.declName == decl)) idx expectedPairs

/-- Greedy backward elimination: discard only the last failing site, then remeasure.
The oracle returns canonical workload times and applied rewrite count for a retained subset.
Only final survivors and the failing sample from each elimination round are returned. -/
def ablateSitesLeaveOneOut {M : Type → Type} [Monad M]
    (measure : List (String × Nat) → M (List Nat × Nat))
    (sites : List (String × Nat)) : M (List Nat × List CandidateAblationSample) :=
  go (sites.length + 1) sites []
where
  go : Nat → List (String × Nat) → List CandidateAblationSample →
      M (List Nat × List CandidateAblationSample)
    | 0, _, pruned => do return ((← measure []).1, pruned)
    | fuel + 1, retained, pruned => do
      let (retTimes, retHits) ← measure retained
      let samples ← retained.mapM fun site => do
        let (minusTimes, minusHits) ← measure (retained.filter (· != site))
        pure {
          siteIdx := site.2, declName := site.1,
          baselineNs := minusTimes.foldl (· + ·) 0,
          soloCandidateNs := retTimes.foldl (· + ·) 0, hits := retHits - minusHits,
          workloadPairs := minusTimes.zip retTimes : CandidateAblationSample }
      match samples.reverse.find? (fun s => !candidateAblationSurvives s) with
      | none => return (retTimes, pruned ++ samples)
      | some failed =>
        go fuel (retained.filter (· != (failed.declName, failed.siteIdx))) (pruned ++ [failed])

structure CalibrationReceipt where
  profile : HardwareCostProfile
  accepted : Bool
  baselineNs : Nat
  candidateNs : Nat
  hits : Nat
  sitesConsidered : Nat := 0
  sitesPruned : Nat := 0
  report : Option SuperoptReport := none
  deriving Repr, DecidableEq, Inhabited, BEq

def aggregateCorpusTimings (corpus : List CorpusTimingSample) : CorpusTimingSample :=
  corpus.foldl (fun total sample =>
    { baselineNs := total.baselineNs + sample.baselineNs
      candidateNs := total.candidateNs + sample.candidateNs
      hits := total.hits + sample.hits })
    { baselineNs := 0, candidateNs := 0, hits := 0 }

def corpusCalibrationReceipt (p : HardwareCostProfile) (corpus : List CorpusTimingSample)
    (rewriteHits : Nat) (report : Option SuperoptReport := none)
    (sitesConsidered : Nat := rewriteHits) (sitesPruned : Nat := 0) : CalibrationReceipt :=
  let totals := aggregateCorpusTimings corpus
  { profile := p
    accepted := meetsCorpusGeomeanOnePercentGain corpus && rewriteHits > 0 && totals.hits > 0
    baselineNs := totals.baselineNs
    candidateNs := totals.candidateNs
    hits := totals.hits
    sitesConsidered := sitesConsidered
    sitesPruned := sitesPruned
    report := report }

def pruneCandidatesByAblation (p : HardwareCostProfile) (corpus : List CorpusTimingSample)
    (m : LNIRModule) (ablations : List CandidateAblationSample := []) :
    LNIRModule × CalibrationReceipt :=
  let keepIdx := fun decl => keepDeclSiteByAblations ablations decl corpus.length
  let (candidate, report, totalSites) := superoptModuleSelective p keepIdx m
  let pruned := totalSites - report.rewritesApplied
  let sites := m.decls.flatMap fun d =>
    let (_, _, count) := superoptDeclSelective p "" (fun _ => true) d 0
    (List.range count).filterMap fun idx => if keepIdx d.name idx then some (d.name, idx) else none
  let selected := { p with keptSites? := some sites }
  let receipt := corpusCalibrationReceipt selected corpus report.rewritesApplied (some report) totalSites pruned
  (if receipt.accepted then candidate else m, receipt)

def pruneCandidateByAmdahl (p : HardwareCostProfile) (corpus : List CorpusTimingSample)
    (m : LNIRModule) (ablations : List CandidateAblationSample := []) :
    LNIRModule × CalibrationReceipt :=
  pruneCandidatesByAblation p corpus m ablations

def autotuneSuperoptModule (base : HardwareCostProfile) (samples : List OpTimingSample)
    (corpus : List CorpusTimingSample) (m : LNIRModule)
    (ablations : List CandidateAblationSample := []) : LNIRModule × CalibrationReceipt :=
  let p := calibrateHardwareProfile base samples
  let (candidate, receipt) := pruneCandidatesByAblation p corpus m ablations
  (candidate, { receipt with profile :=
    if receipt.accepted then receipt.profile else { base with keptSites? := some [] } })

def autotuneDeclWithAmdahl (base : HardwareCostProfile) (samples : List OpTimingSample)
    (corpus : List CorpusTimingSample) (d : LNIRDecl)
    (ablations : List CandidateAblationSample := []) : LNIRDecl × CalibrationReceipt :=
  let p := calibrateHardwareProfile base samples
  let declAblations := ablations.filter (fun s => s.declName == d.name)
  let keepIdx := fun idx => keepSiteByAblations declAblations idx corpus.length
  let (candidate, records, totalSites) :=
    superoptDeclSelective p s!"{p.target.toString}:{p.profileId}" keepIdx d 0
  let declHits := (aggregateCorpusTimings (corpus.filter (fun s => s.declName == d.name))).hits
  let pruned := totalSites - records.length
  let sites := (List.range totalSites).filterMap fun idx =>
    if keepIdx idx then some (d.name, idx) else none
  let selected := { p with keptSites? := some sites }
  let receipt := corpusCalibrationReceipt selected corpus (if declHits > 0 then records.length else 0)
    none totalSites pruned
  (if receipt.accepted then candidate else d,
    { receipt with profile := if receipt.accepted then selected else { base with keptSites? := some [] } })

def calibrationPreset : String → Option HardwareCostProfile
  | "zen5" => some { HardwareCostProfile.forTarget .x86_64 with
      profileId := "x86_64_zen5_avx512", llvmTargetCpu := "znver5" }
  | "x86_64" => some (HardwareCostProfile.forTarget .x86_64)
  | "arm64" => some (HardwareCostProfile.forTarget .arm64)
  | "neoverse" => some { HardwareCostProfile.forTarget .arm64 with
      profileId := "arm64_grace_neoverse_v2", llvmTargetCpu := "neoverse-v2" }
  | "scaleway" => some { HardwareCostProfile.forTarget .arm64 with
      profileId := "arm64_scaleway_neoverse", llvmTargetCpu := "neoverse-n1" }
  | "rtx4090" => some { HardwareCostProfile.forTarget .cuda_ptx with
      profileId := "cuda_ada_rtx4090_sm89", smArch := "sm_89" }
  | "sm_89" => some { HardwareCostProfile.forTarget .cuda_ptx with
      profileId := "cuda_ada_sm89", smArch := "sm_89" }
  | "sm_90" => some { HardwareCostProfile.forTarget .cuda_ptx with
      profileId := "cuda_hopper_sm90", smArch := "sm_90" }
  | _ => none

def autotuneCodeWithAmdahl (base : HardwareCostProfile) (samples : List OpTimingSample)
    (corpus : List CorpusTimingSample) (ablations : List CandidateAblationSample := [])
    (c : LNIRCode) (declName : String := "autotune") : LNIRCode :=
  let p := calibrateHardwareProfile base samples
  let keepIdx := keepDeclSiteByAblations ablations declName corpus.length
  let (candidate, records, totalSites) :=
    superoptCodeSelective p s!"{p.target.toString}:{p.profileId}" declName keepIdx c 0
  let pruned := totalSites - records.length
  let receipt := corpusCalibrationReceipt p corpus records.length none totalSites pruned
  if receipt.accepted then candidate else c

def verifiedCostAutotuneContract (base : HardwareCostProfile) (samples : List OpTimingSample)
    (corpus : List CorpusTimingSample) (ablations : List CandidateAblationSample := [])
    (h : ∀ c : LNIRCode,
      LeanNative.Semantics.CodeRefines c (autotuneCodeWithAmdahl base samples corpus ablations c)) :
    VerifiedCodePassContract where
  name := "CostAutotune"
  theoremRef := "LeanNative.Proofs.autotuneCodeWithAmdahl_sound"
  notes := "Hardware-calibrated superoptimization gated by exact >= 1% Amdahl & ablation pruning"
  runCode := autotuneCodeWithAmdahl base samples corpus ablations
  sound := h

end LeanNative.Transform
