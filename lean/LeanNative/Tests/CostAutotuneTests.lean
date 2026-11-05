import LeanNative.Core

namespace LeanNative.Tests.CostAutotuneTests

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Proofs
open LeanNative.Transform

def zen5Preset : HardwareCostProfile :=
  (calibrationPreset "zen5").getD (HardwareCostProfile.forTarget .x86_64)

def neoversePreset : HardwareCostProfile :=
  (calibrationPreset "neoverse").getD (HardwareCostProfile.forTarget .arm64)

def scalewayPreset : HardwareCostProfile :=
  (calibrationPreset "scaleway").getD (HardwareCostProfile.forTarget .arm64)

def rtx4090Preset : HardwareCostProfile :=
  (calibrationPreset "rtx4090").getD (HardwareCostProfile.forTarget .cuda_ptx)

def sm89Preset : HardwareCostProfile :=
  (calibrationPreset "sm_89").getD (HardwareCostProfile.forTarget .cuda_ptx)

def sm90Preset : HardwareCostProfile :=
  (calibrationPreset "sm_90").getD (HardwareCostProfile.forTarget .cuda_ptx)

def zen5Samples : List OpTimingSample :=
  [ { operation := "add", elapsedNs := 100, iterations := 100 }
  , { operation := "add", elapsedNs := 100, iterations := 100 }
  , { operation := "add", elapsedNs := 900, iterations := 100 }
  , { operation := "bitwise", elapsedNs := 100, iterations := 100 }
  , { operation := "shift", elapsedNs := 100, iterations := 100 }
  , { operation := "cmp", elapsedNs := 100, iterations := 100 }
  , { operation := "mul", elapsedNs := 300, iterations := 100 }
  , { operation := "div", elapsedNs := 1800, iterations := 100 }
  , { operation := "fma", elapsedNs := 400, iterations := 100 }
  , { operation := "select", elapsedNs := 200, iterations := 100 }
  , { operation := "clz256", elapsedNs := 300, iterations := 100 }
  , { operation := "add_sub_checked256", elapsedNs := 400, iterations := 100 }
  , { operation := "mul_checked256", elapsedNs := 600, iterations := 100 }
  , { operation := "min_gpu_elements", elapsedNs := 131072, iterations := 1 }
  , { operation := "gpu_block_threads", elapsedNs := 512, iterations := 1 }
  , { operation := "matmul_tile_dim", elapsedNs := 32, iterations := 1 } ]

def cudaHeavyFmaSamples : List OpTimingSample :=
  [ { operation := "add", elapsedNs := 100, iterations := 100 }
  , { operation := "mul", elapsedNs := 200, iterations := 100 }
  , { operation := "fma", elapsedNs := 200, iterations := 100 } ]

def slowFmaSamples : List OpTimingSample :=
  [ { operation := "add", elapsedNs := 100, iterations := 100 }
  , { operation := "mul", elapsedNs := 200, iterations := 100 }
  , { operation := "fma", elapsedNs := 500, iterations := 100 } ]

def fmaDecl : LNIRDecl := {
  name := "autotune_fma"
  params := [ { id := 0, name := "a", ty := .i64, borrow := false }
            , { id := 1, name := "b", ty := .i64, borrow := false }
            , { id := 2, name := "c", ty := .i64, borrow := false } ]
  retTy := .i64
  assurance := .verifiedKernelProof
  isGpuCand := false
  body := .letBind 3 .i64 (.scalar (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))) (.ret 3)
}

def noopDecl : LNIRDecl := {
  name := "autotune_noop"
  params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
  retTy := .i64
  assurance := .verifiedKernelProof
  isGpuCand := false
  body := .ret 0
}

def fmaModule : LNIRModule := { moduleName := "LeanNative.Tests.AutotuneFma", decls := [fmaDecl] }
def noopModule : LNIRModule := { moduleName := "LeanNative.Tests.AutotuneNoop", decls := [noopDecl] }

def evalDeclU64 (d : LNIRDecl) (a b c : UInt64) : Option UInt64 :=
  let env := (((VarEnv.empty).bind 0 (.u64 a)).bind 1 (.u64 b)).bind 2 (.u64 c)
  match evalCode 64 env HeapState.empty d.body with
  | .ok (.u64 v, _) => some v
  | _ => none

#guard zen5Preset.target == .x86_64
#guard neoversePreset.target == .arm64
#guard scalewayPreset.target == .arm64
#guard rtx4090Preset.target == .cuda_ptx
#guard sm89Preset.smArch == "sm_89"
#guard sm90Preset.smArch == "sm_90"

#guard (let cal := calibrateHardwareProfile zen5Preset zen5Samples
        cal.target == .x86_64 && cal.mulCost == 3 && cal.divModCost == 18 &&
        cal.fmaCost == 4 && cal.minGpuElements == zen5Preset.minGpuElements &&
        cal.gpuBlockThreads == zen5Preset.gpuBlockThreads && cal.matmulTileDim == zen5Preset.matmulTileDim)

#guard (let cal := calibrateHardwareProfile zen5Preset zen5Samples
        HardwareCostProfile.fromJson? cal.toJson == some cal)
#guard (HardwareCostProfile.fromJson? neoversePreset.toJson == some neoversePreset)
#guard (HardwareCostProfile.fromJson? scalewayPreset.toJson == some scalewayPreset)
#guard (HardwareCostProfile.fromJson? rtx4090Preset.toJson == some rtx4090Preset)
#guard (HardwareCostProfile.fromJson? sm90Preset.toJson == some sm90Preset)

#guard (let fastP := calibrateHardwareProfile sm90Preset cudaHeavyFmaSamples
        let slowP := calibrateHardwareProfile zen5Preset slowFmaSamples
        let (fastM, fastRep) := superoptModuleWithProfile fastP fmaModule
        let (slowM, slowRep) := superoptModuleWithProfile slowP fmaModule
        fastRep.rewritesApplied == 1 && slowRep.rewritesApplied == 0 && fastM != slowM)

#guard meetsOnePercentE2EGain 1000 990 == true
#guard meetsOnePercentE2EGain 1000 991 == false
#guard meetsOnePercentE2EGain 0 0 == false

#guard (let falsePositiveCorpus : List CorpusTimingSample :=
          [ { baselineNs := 10000, candidateNs := 9700, hits := 1, declName := "k0" }
          , { baselineNs := 100, candidateNs := 200, hits := 1, declName := "k1" } ]
        let totals := aggregateCorpusTimings falsePositiveCorpus
        let (m', r) := autotuneSuperoptModule sm90Preset cudaHeavyFmaSamples falsePositiveCorpus fmaModule
        meetsOnePercentE2EGain totals.baselineNs totals.candidateNs == true &&
        meetsCorpusGeomeanOnePercentGain falsePositiveCorpus == false &&
         r.accepted == false && m' == fmaModule && r.profile == { sm90Preset with keptSites? := some [] })

#guard (let validGeomeanCorpus : List CorpusTimingSample :=
          [ { baselineNs := 1000, candidateNs := 980, hits := 1, declName := "k0" }
          , { baselineNs := 1000, candidateNs := 995, hits := 1, declName := "k1" } ]
        meetsCorpusGeomeanOnePercentGain validGeomeanCorpus == true)

#guard (let (m', r) := autotuneSuperoptModule sm90Preset cudaHeavyFmaSamples
          [{ baselineNs := 1000, candidateNs := 990, hits := 1 }] fmaModule
          [{ siteIdx := 0, declName := "autotune_fma", baselineNs := 1000, soloCandidateNs := 980, workloadPairs := [(1000, 980)] }]
        r.accepted == true && m' != fmaModule &&
        r.profile == { calibrateHardwareProfile sm90Preset cudaHeavyFmaSamples with
          keptSites? := some [("autotune_fma", 0)] })

#guard (let (m', r) := autotuneSuperoptModule sm90Preset cudaHeavyFmaSamples
          [{ baselineNs := 1000, candidateNs := 991, hits := 1 }] fmaModule
        r.accepted == false && m' == fmaModule && r.profile == { sm90Preset with keptSites? := some [] })

#guard (let (m', r) := autotuneSuperoptModule sm90Preset cudaHeavyFmaSamples
          [{ baselineNs := 1000, candidateNs := 900, hits := 0 }] fmaModule
        r.accepted == false && m' == fmaModule && r.profile == { sm90Preset with keptSites? := some [] })

#guard (let (m', r) := autotuneSuperoptModule sm90Preset cudaHeavyFmaSamples
          [{ baselineNs := 1000, candidateNs := 900, hits := 1 }] noopModule
        r.accepted == false && m' == noopModule && r.profile == { sm90Preset with keptSites? := some [] })

def fmaDecl2 : LNIRDecl := { fmaDecl with name := "autotune_fma_2" }
def twoDeclMod : LNIRModule := { moduleName := "LeanNative.Tests.TwoSiteAblation", decls := [fmaDecl, fmaDecl2] }

-- Both sites alone and together cost 980ns: eliminate B, then remeasure A against 1000ns.
#guard [980, 995, 1000].all fun ns =>
  let sites := [(fmaDecl.name, 0), (fmaDecl2.name, 0)]
  let (times, ablations) := (ablateSitesLeaveOneOut (M := Id)
    (fun kept => pure ([if kept.isEmpty then 1000 else ns], kept.length)) sites).run
  let (_, r) := autotuneSuperoptModule sm90Preset cudaHeavyFmaSamples
    [{ baselineNs := 1000, candidateNs := times.head!, hits := 1 }] twoDeclMod ablations
  ablations.length == 2 && r.sitesConsidered == 2 &&
    r.sitesPruned == (if ns == 980 then 1 else 2) && r.accepted == (ns == 980) &&
    ablations.head!.declName == fmaDecl2.name &&
    ablations.head!.workloadPairs == [(ns, ns)] &&
    ablations[1]!.workloadPairs == [(1000, ns)]

#guard (ablateSitesLeaveOneOut (M := Id) (fun _ => pure ([1000], 0)) []).run == ([1000], [])
#guard (let (_, samples) := (ablateSitesLeaveOneOut (M := Id)
          (fun kept => pure ([if kept.isEmpty then 1000 else 900], 0)) [("zero_hits", 0)]).run
        samples.length == 1 && !candidateAblationSurvives samples.head!)
#guard isRegisteredTheorem "LeanNative.Proofs.ablateSitesLeaveOneOut_sound"

#guard (let ablations : List CandidateAblationSample :=
          [{ siteIdx := 0, declName := fmaDecl.name, baselineNs := 1000, soloCandidateNs := 980, workloadPairs := [(1000, 980)] },
           { siteIdx := 0, declName := fmaDecl2.name, baselineNs := 1000, soloCandidateNs := 995, workloadPairs := [(1000, 995)] }]
        let (candidate, receipt) := autotuneSuperoptModule sm90Preset cudaHeavyFmaSamples
          [{ baselineNs := 1000, candidateNs := 980, hits := 1 }] twoDeclMod ablations
        match HardwareCostProfile.fromJson? receipt.profile.toJson with
        | none => false
        | some profile => receipt.accepted && (superoptModuleWithProfile profile twoDeclMod).1 == candidate &&
            candidate.decls[1]! == fmaDecl2 && candidate.decls[0]! != fmaDecl)

#guard !keepSiteByAblations [] 0
#guard !candidateAblationSurvives { siteIdx := 0, baselineNs := 1000, soloCandidateNs := 980 }
#guard [0, 1, 7, 8, 9].all fun count =>
  let corpus : List CorpusTimingSample := List.replicate 8
    { baselineNs := 1000, candidateNs := 980, hits := 1, declName := fmaDecl.name }
  let ablations : List CandidateAblationSample :=
    [{ siteIdx := 0, declName := fmaDecl.name, baselineNs := 8000,
       soloCandidateNs := 7840, workloadPairs := List.replicate count (1000, 980) }]
  let (_, moduleReceipt) := autotuneSuperoptModule sm90Preset cudaHeavyFmaSamples corpus fmaModule ablations
  let (_, declReceipt) := autotuneDeclWithAmdahl sm90Preset cudaHeavyFmaSamples corpus fmaDecl ablations
  moduleReceipt.accepted == (count == 8) && declReceipt.accepted == (count == 8) &&
    (autotuneCodeWithAmdahl sm90Preset cudaHeavyFmaSamples corpus ablations fmaDecl.body fmaDecl.name !=
      fmaDecl.body) == (count == 8)
#guard !candidateAblationSurvives {
  siteIdx := 0, baselineNs := 10700, soloCandidateNs := 10400,
  workloadPairs := (10000, 9000) :: List.replicate 7 (100, 200) }
#guard !candidateAblationSurvives {
  siteIdx := 0, baselineNs := 1000, soloCandidateNs := 900, hits := 0 }
#guard !candidateAblationSurvives {
  siteIdx := 0, baselineNs := 1000, soloCandidateNs := 900, workloadPairs := [(1000, 0)] }
#guard candidateAblationSurvives {
  siteIdx := 0, baselineNs := 1000, soloCandidateNs := 980,
  workloadPairs := List.replicate 8 (1000, 980) }
#guard (let pass := costAutotunePassFor sm90Preset cudaHeavyFmaSamples
          [{ baselineNs := 1000, candidateNs := 980, hits := 1, declName := "autotune_fma" }]
          [{ siteIdx := 0, declName := "autotune_fma", baselineNs := 1000, soloCandidateNs := 980, workloadPairs := [(1000, 980)] }]
        (pass.runDecl fmaDecl2).1 == fmaDecl2)

#guard (let abls : List CandidateAblationSample :=
          [ { siteIdx := 0, declName := "autotune_fma", baselineNs := 1000, soloCandidateNs := 980, workloadPairs := [(1000, 980)] }
          , { siteIdx := 0, declName := "autotune_fma_2", baselineNs := 1000, soloCandidateNs := 995, workloadPairs := [(1000, 995)] } ]
        let (m', r) := autotuneSuperoptModule sm90Preset cudaHeavyFmaSamples
          [{ baselineNs := 1000, candidateNs := 985, hits := 1 }] twoDeclMod abls
        r.accepted == true && r.sitesConsidered == 2 && r.sitesPruned == 1 &&
        m'.decls.length == 2 && m'.decls[0]! != fmaDecl && m'.decls[1]! == fmaDecl2)

#guard (let allPrunedAbls : List CandidateAblationSample :=
          [ { siteIdx := 0, declName := "autotune_fma", baselineNs := 1000, soloCandidateNs := 995, workloadPairs := [(1000, 995)] } ]
        let (m', r) := autotuneSuperoptModule sm90Preset cudaHeavyFmaSamples
          [{ baselineNs := 1000, candidateNs := 980, hits := 1 }] fmaModule allPrunedAbls
        r.accepted == false && r.sitesConsidered == 1 && r.sitesPruned == 1 &&
        m' == fmaModule && r.profile == { sm90Preset with keptSites? := some [] })

#guard (let m := mkCanonicalBenchmarkModule8
        let mutatedEvm := m.decls.map fun d =>
          if d.name == "evm_muldiv_wad_u256" then
            { d with body := .letBind 99 .u256 (.constU256 (UInt256.ofUInt64 42)) (.ret 99) }
          else d
        !(LeanNative.Driver.CostAutotuneCLI.verifyAndAccumulateCorpus m { m with decls := mutatedEvm } 8).isOk)

#guard (let m := mkCanonicalBenchmarkModule8
        let mutatedSarray := m.decls.map fun d =>
          if d.name == "saxpy_kernel" then
            { d with body := .ret 0 }
          else d
        !(LeanNative.Driver.CostAutotuneCLI.verifyAndAccumulateCorpus m { m with decls := mutatedSarray } 8).isOk)

#guard (let (d', r) := autotuneDeclWithAmdahl sm90Preset cudaHeavyFmaSamples
          [{ baselineNs := 1000, candidateNs := 990, hits := 1, declName := "autotune_fma" }] fmaDecl
          [{ siteIdx := 0, declName := "autotune_fma", baselineNs := 1000, soloCandidateNs := 980, workloadPairs := [(1000, 980)] }]
        r.accepted == true && r.profile.keptSites? == some [(fmaDecl.name, 0)] &&
        (superoptModuleWithProfile r.profile fmaModule).1.decls == [d'] &&
        evalDeclU64 fmaDecl 7 11 13 == evalDeclU64 d' 7 11 13 &&
        evalDeclU64 d' 7 11 13 == some 90)

#guard (let (d', cert) := costAutotunePass.runDecl fmaDecl
        cert.changed == false && d' == fmaDecl && cert.assurance == .verifiedKernelProof)

#guard (let (d', r) := autotuneDeclWithAmdahl sm90Preset cudaHeavyFmaSamples
          [{ baselineNs := 1000, candidateNs := 991, hits := 1, declName := fmaDecl.name }] fmaDecl
          [{ siteIdx := 0, declName := fmaDecl.name, baselineNs := 1000, soloCandidateNs := 980,
             workloadPairs := [(1000, 980)] }]
        !r.accepted && d' == fmaDecl && r.profile.keptSites? == some [] &&
        (superoptModuleWithProfile r.profile fmaModule).1 == fmaModule)

#guard (let calPass := costAutotunePassFor sm90Preset cudaHeavyFmaSamples
          [{ baselineNs := 1000, candidateNs := 990, hits := 1, declName := "autotune_fma" }]
          [{ siteIdx := 0, declName := "autotune_fma", baselineNs := 1000, soloCandidateNs := 980, workloadPairs := [(1000, 980)] }]
        let (d', cert) := calPass.runDecl fmaDecl
        cert.changed == true && d' != fmaDecl && cert.assurance == .verifiedKernelProof &&
        evalDeclU64 fmaDecl 7 11 13 == evalDeclU64 d' 7 11 13)

#guard (let subPass := costAutotunePassFor sm90Preset cudaHeavyFmaSamples
          [{ baselineNs := 1000, candidateNs := 991, hits := 1 }]
        let (d', cert) := subPass.runDecl fmaDecl
        cert.changed == false && d' == fmaDecl && cert.assurance == .verifiedKernelProof)

#guard (let m := mkCanonicalBenchmarkModule8
        (LeanNative.Driver.CostAutotuneCLI.verifyAndAccumulateCorpus m m 128).isOk)

#guard (let m := mkCanonicalBenchmarkModule8
        let mutatedDecls := m.decls.map fun d =>
          if d.name == "collatz_steps" then
            { d with body := .letBind 99 .i64 (.scalar (.constU64 777777)) (.ret 99) }
          else d
        let badMod : LNIRModule := { m with decls := mutatedDecls }
        !(LeanNative.Driver.CostAutotuneCLI.verifyAndAccumulateCorpus m badMod 128).isOk)

#guard isRegisteredTheorem "LeanNative.Proofs.calibrateHardwareProfile_preserves_target" == true
#guard isRegisteredTheorem "LeanNative.Proofs.meetsOnePercentE2EGain_iff" == true
#guard isRegisteredTheorem "LeanNative.Proofs.meetsOnePercentE2EGain_rejects_subthreshold" == true
#guard isRegisteredTheorem "LeanNative.Proofs.meetsCorpusGeomeanOnePercentGain_iff" == true
#guard isRegisteredTheorem "LeanNative.Proofs.meetsCorpusGeomeanOnePercentGain_rejects_summed_false_positive" == true
#guard isRegisteredTheorem "LeanNative.Proofs.superoptCodeSelective_sound" == true
#guard isRegisteredTheorem "LeanNative.Proofs.superoptDeclSelective_sound" == true
#guard isRegisteredTheorem "LeanNative.Proofs.superoptModuleSelective_sound" == true
#guard isRegisteredTheorem "LeanNative.Proofs.superoptModuleWithCalibratedProfile_sound" == true
#guard isRegisteredTheorem "LeanNative.Proofs.autotuneCodeWithAmdahl_sound" == true
#guard isRegisteredTheorem "LeanNative.Proofs.autotuneCodeWithAmdahl_uncalibrated_preserves" == true
#guard isRegisteredTheorem "LeanNative.Proofs.autotuneDeclWithAmdahl_sound" == true
#guard isRegisteredTheorem "LeanNative.Proofs.autotuneSuperoptModule_sound" == true
#guard isRegisteredTheorem "LeanNative.Proofs.costAutotune_amdahl_gate_nonvacuous" == true

end LeanNative.Tests.CostAutotuneTests
