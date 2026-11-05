import LeanNative.Transform.CostAutotune
import LeanNative.Proofs.SuperoptSoundness

set_option autoImplicit false

namespace LeanNative.Proofs

open LeanNative.IR LeanNative.Semantics LeanNative.Transform
open LeanNative.Spec

theorem calibrateHardwareProfile_preserves_target (base : HardwareCostProfile)
    (samples : List OpTimingSample) :
    let p := calibrateHardwareProfile base samples
    p.target = base.target ∧ p.profileId = base.profileId ∧
    p.llvmTargetCpu = base.llvmTargetCpu ∧ p.smArch = base.smArch ∧
    0 < p.addSubCost ∧ 0 < p.bitwiseCost ∧ 0 < p.shiftCost ∧ 0 < p.cmpCost ∧
    0 < p.mulCost ∧ 0 < p.divModCost ∧ 0 < p.fmaCost ∧ 0 < p.selectCost ∧
    0 < p.clz256Cost ∧ 0 < p.addSubChecked256Cost ∧ 0 < p.mulChecked256Cost ∧
    0 < p.minGpuElements ∧ 0 < p.gpuBlockThreads ∧ 0 < p.matmulTileDim ∧
    p.minGpuElements = max 1 base.minGpuElements ∧
    p.gpuBlockThreads = max 1 base.gpuBlockThreads ∧ p.matmulTileDim = max 1 base.matmulTileDim := by
  have max_one_pos (n : Nat) : 0 < max 1 n := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 n)
  have cost_pos (op : String) (preset unit : Nat) :
      0 < (match operationMedianNs? samples op with
        | some ns => max 1 (ns / unit)
        | none => max 1 preset) := by
    split <;> exact max_one_pos _
  dsimp only [calibrateHardwareProfile]
  exact ⟨rfl, rfl, rfl, rfl, cost_pos _ _ _, cost_pos _ _ _, cost_pos _ _ _,
    cost_pos _ _ _, cost_pos _ _ _, cost_pos _ _ _, cost_pos _ _ _, cost_pos _ _ _,
    cost_pos _ _ _, cost_pos _ _ _, cost_pos _ _ _, max_one_pos _, max_one_pos _,
    max_one_pos _, rfl, rfl, rfl⟩

theorem meetsOnePercentE2EGain_iff (b c : Nat) :
    meetsOnePercentE2EGain b c = true ↔ 0 < b ∧ c * 100 ≤ b * 99 := by
  simp [meetsOnePercentE2EGain]

theorem meetsOnePercentE2EGain_rejects_subthreshold (b c : Nat)
    (h : b * 99 < c * 100) : meetsOnePercentE2EGain b c = false := by
  simp [meetsOnePercentE2EGain, Nat.not_le.mpr h]

theorem meetsCorpusGeomeanOnePercentGain_iff (corpus : List CorpusTimingSample) :
    meetsCorpusGeomeanOnePercentGain corpus = true ↔
      corpus ≠ [] ∧
      (∀ s ∈ corpus, 0 < s.baselineNs ∧ 0 < s.candidateNs) ∧
      corpusProdCandidate corpus * (100 ^ corpus.length) ≤
        corpusProdBaseline corpus * (99 ^ corpus.length) := by
  simp [meetsCorpusGeomeanOnePercentGain, Bool.and_assoc]

theorem meetsCorpusGeomeanOnePercentGain_rejects_summed_false_positive :
    let corpus := [
      CorpusTimingSample.mk 10000 9700 1 "k0",
      CorpusTimingSample.mk 100 200 1 "k1"
    ]
    let totals := aggregateCorpusTimings corpus
    meetsOnePercentE2EGain totals.baselineNs totals.candidateNs = true ∧
    meetsCorpusGeomeanOnePercentGain corpus = false := by
  decide

theorem superoptModuleWithProfile_sound (p : HardwareCostProfile) (m : LNIRModule) :
    ∀ d ∈ m.decls, ∃ d' ∈ (superoptModuleWithProfile p m).1.decls, CodeRefines d.body d'.body := by
  unfold superoptModuleWithProfile
  exact superoptModuleSelective_sound p
    (fun decl idx => p.keptSites?.all (fun sites => sites.contains (decl, idx))) m

theorem superoptModuleWithCalibratedProfile_sound (base : HardwareCostProfile)
    (samples : List OpTimingSample) (m : LNIRModule) :
    ∀ d ∈ m.decls,
      ∃ d' ∈ (superoptModuleWithProfile (calibrateHardwareProfile base samples) m).1.decls,
        CodeRefines d.body d'.body :=
  superoptModuleWithProfile_sound (calibrateHardwareProfile base samples) m

theorem autotuneCodeWithAmdahl_sound (base : HardwareCostProfile)
    (samples : List OpTimingSample) (corpus : List CorpusTimingSample)
    (ablations : List CandidateAblationSample := []) (c : LNIRCode) (declName : String := "autotune") :
    CodeRefines c (autotuneCodeWithAmdahl base samples corpus ablations c declName) := by
  unfold autotuneCodeWithAmdahl
  dsimp only []
  split
  · exact superoptCodeSelective_sound _ _ _ _ c 0
  · exact CodeRefines.refl _

theorem autotuneCodeWithAmdahl_uncalibrated_preserves (base : HardwareCostProfile)
    (samples : List OpTimingSample) (ablations : List CandidateAblationSample := [])
    (c : LNIRCode) :
    autotuneCodeWithAmdahl base samples [] ablations c = c := by
  simp [autotuneCodeWithAmdahl, corpusCalibrationReceipt, meetsCorpusGeomeanOnePercentGain]

theorem autotuneDeclWithAmdahl_sound (base : HardwareCostProfile)
    (samples : List OpTimingSample) (corpus : List CorpusTimingSample) (d : LNIRDecl)
    (ablations : List CandidateAblationSample := []) :
    CodeRefines d.body (autotuneDeclWithAmdahl base samples corpus d ablations).1.body := by
  unfold autotuneDeclWithAmdahl
  dsimp only []
  have gate (accept : Bool) (candidate : LNIRDecl) (h : CodeRefines d.body candidate.body) :
      CodeRefines d.body (if accept then candidate else d).body := by
    cases accept
    · exact CodeRefines.refl _
    · exact h
  exact gate _ _ (superoptDeclSelective_sound _ _ _ d 0)

theorem autotuneSuperoptModule_sound (base : HardwareCostProfile)
    (samples : List OpTimingSample) (corpus : List CorpusTimingSample) (m : LNIRModule)
    (ablations : List CandidateAblationSample := []) :
    ∀ d ∈ m.decls, ∃ d' ∈ (autotuneSuperoptModule base samples corpus m ablations).1.decls,
      CodeRefines d.body d'.body := by
  intro d hd
  unfold autotuneSuperoptModule pruneCandidatesByAblation
  dsimp only []
  split
  · exact superoptModuleSelective_sound (calibrateHardwareProfile base samples)
      (fun decl => keepDeclSiteByAblations ablations decl corpus.length) m _ d hd
  · exact ⟨d, hd, CodeRefines.refl _⟩

theorem ablateSitesLeaveOneOut_sound (p : HardwareCostProfile) (m : LNIRModule)
    (measure : List (String × Nat) → Id (List Nat × Nat)) (sites : List (String × Nat))
    (expectedPairs : Nat) :
    let samples := (ablateSitesLeaveOneOut measure sites).run.2
    ∀ d ∈ m.decls, ∃ d' ∈ (superoptModuleSelective p
      (fun decl => keepDeclSiteByAblations samples decl expectedPairs) m).1.decls, CodeRefines d.body d'.body := by
  exact superoptModuleSelective_sound p _ m

theorem costAutotune_amdahl_gate_nonvacuous :
    let base := HardwareCostProfile.forTarget .x86_64
    let p := calibrateHardwareProfile base []
    let e := ScalarExpr.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)
    let fused := ScalarExpr.fma (.var 0) (.var 1) (.var 2)
    let d : LNIRDecl := {
      name := "fma", params := [], retTy := .i64
      body := .letBind 3 .i64 (.scalar e) (.ret 3) }
    let m : LNIRModule := { moduleName := "amdahl", decls := [d] }
    let good := autotuneSuperoptModule base []
      [CorpusTimingSample.mk 1000 990 1 ""] m
      [{ siteIdx := 0, declName := "fma", baselineNs := 1000, soloCandidateNs := 980, workloadPairs := [(1000, 980)] }]
    let bad := autotuneSuperoptModule base []
      [CorpusTimingSample.mk 1000 991 1 ""] m
      [{ siteIdx := 0, declName := "fma", baselineNs := 1000, soloCandidateNs := 980, workloadPairs := [(1000, 980)] }]
    let ablatedReject := autotuneSuperoptModule base []
      [CorpusTimingSample.mk 1000 990 1 ""] m
      [CandidateAblationSample.mk 0 "fma" 1000 995 1 [(1000, 995)]]
    scalarExprCostWithProfile p fused < scalarExprCostWithProfile p e ∧
    good.2.accepted = true ∧
    bad.2.accepted = false ∧
    ablatedReject.2.accepted = false ∧
    good.1.decls.map (·.body) = [.letBind 3 .i64 (.scalar fused) (.ret 3)] ∧
    bad.1 = m ∧
    ablatedReject.1 = m ∧
    good.2.profile.keptSites? = some [("fma", 0)] ∧
    bad.2.profile = { base with keptSites? := some [] } ∧
    ablatedReject.2.profile = { base with keptSites? := some [] } ∧
    good.2.report.map (·.rewritesApplied) = some 1 ∧
    bad.2.report.map (·.rewritesApplied) = some 1 ∧
    ablatedReject.2.sitesPruned = 1 := by
  have hp : calibrateHardwareProfile (HardwareCostProfile.forTarget .x86_64) [] =
      HardwareCostProfile.forTarget .x86_64 := by
    simp [calibrateHardwareProfile, operationMedianNs?, HardwareCostProfile.forTarget]
  have hv0 : synthesizeCandidates .x86_64 (.var 0) = [.var 0] := by
    rw [synthesizeCandidates.eq_def]; decide
  have hv1 : synthesizeCandidates .x86_64 (.var 1) = [.var 1] := by
    rw [synthesizeCandidates.eq_def]; decide
  have hv2 : synthesizeCandidates .x86_64 (.var 2) = [.var 2] := by
    rw [synthesizeCandidates.eq_def]; decide
  have hmul : synthesizeCandidates .x86_64 (.binOp .mul (.var 0) (.var 1)) =
      [.binOp .mul (.var 0) (.var 1)] := by
    rw [synthesizeCandidates.eq_def]
    simp only [hv0, hv1]
    decide
  have hcands : synthesizeCandidates .x86_64
      (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)) =
      [.fma (.var 0) (.var 1) (.var 2),
       .binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)] := by
    rw [synthesizeCandidates.eq_def]
    simp only [hmul, hv2]
    decide
  have hso (lbl : String) :
      ∃ r : SuperoptRewriteRecord,
        superoptScalarExprCore (HardwareCostProfile.forTarget .x86_64) lbl "fma"
          (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)) =
          (.fma (.var 0) (.var 1) (.var 2), some r) := by
    unfold superoptScalarExprCore
    have htgt : (HardwareCostProfile.forTarget .x86_64).target = .x86_64 := rfl
    simp only [htgt, hcands, List.foldl]
    have hstep1 :
        (checkSuperoptScalarVerified
            (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))
            (.fma (.var 0) (.var 1) (.var 2)) &&
          fastCheckScalarEquiv
            (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))
            (.fma (.var 0) (.var 1) (.var 2)) &&
          symCheckScalarEquiv
            (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))
            (.fma (.var 0) (.var 1) (.var 2)) &&
          decide (scalarExprCostWithProfile (HardwareCostProfile.forTarget .x86_64)
              (.fma (.var 0) (.var 1) (.var 2)) <
            scalarExprCostWithProfile (HardwareCostProfile.forTarget .x86_64)
              (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)))) = true := by decide
    have hstep2 :
        (checkSuperoptScalarVerified
            (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))
            (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)) &&
          fastCheckScalarEquiv
            (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))
            (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)) &&
          symCheckScalarEquiv
            (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))
            (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)) &&
          decide (scalarExprCostWithProfile (HardwareCostProfile.forTarget .x86_64)
              (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)) <
            scalarExprCostWithProfile (HardwareCostProfile.forTarget .x86_64)
              (.fma (.var 0) (.var 1) (.var 2)))) = false := by decide
    have hguard :
        ((ScalarExpr.fma (.var 0) (.var 1) (.var 2) !=
            ScalarExpr.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)) &&
          decide (scalarExprCostWithProfile (HardwareCostProfile.forTarget .x86_64)
              (.fma (.var 0) (.var 1) (.var 2)) <
            scalarExprCostWithProfile (HardwareCostProfile.forTarget .x86_64)
              (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)))) = true := by decide
    simp only [hstep1, hstep2, ite_true]
    exact ⟨_, rfl⟩
  let lbl :=
    toString (HardwareCostProfile.forTarget .x86_64).target.toString ++
      toString ":" ++
      toString (HardwareCostProfile.forTarget .x86_64).profileId
  have hlbl :
      toString (HardwareCostProfile.forTarget .x86_64).target.toString ++
        toString ":" ++
        toString (HardwareCostProfile.forTarget .x86_64).profileId =
        lbl := rfl
  rcases hso lbl with ⟨r, hr⟩
  rcases hso "" with ⟨r0, hr0⟩
  have hcodeKeep :
      superoptCodeSelective (HardwareCostProfile.forTarget .x86_64) lbl "fma"
        (fun idx => keepSiteByAblations [CandidateAblationSample.mk 0 "fma" 1000 980 1 [(1000, 980)]] idx)
        (.letBind 3 .i64 (.scalar (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))) (.ret 3)) 0 =
      (.letBind 3 .i64 (.scalar (.fma (.var 0) (.var 1) (.var 2))) (.ret 3), [r], 1) := by
    rw [superoptCodeSelective, hr]
    simp [superoptCodeSelective, keepSiteByAblations, candidateAblationSurvives,
      meetsCorpusGeomeanOnePercentGain, corpusProdBaseline, corpusProdCandidate]
  have hcodePrune :
      superoptCodeSelective (HardwareCostProfile.forTarget .x86_64) lbl "fma"
        (fun idx => keepSiteByAblations [CandidateAblationSample.mk 0 "fma" 1000 995 1 [(1000, 995)]] idx)
        (.letBind 3 .i64 (.scalar (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))) (.ret 3)) 0 =
      (.letBind 3 .i64 (.scalar (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))) (.ret 3), [], 1) := by
    rw [superoptCodeSelective, hr]
    simp [superoptCodeSelective, keepSiteByAblations, candidateAblationSurvives,
      meetsCorpusGeomeanOnePercentGain, corpusProdBaseline, corpusProdCandidate]
  have hcost :
      scalarExprCostWithProfile (HardwareCostProfile.forTarget .x86_64)
        (.fma (.var 0) (.var 1) (.var 2)) <
      scalarExprCostWithProfile (HardwareCostProfile.forTarget .x86_64)
        (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)) := by decide
  have hdeclKeep :
      superoptDeclSelective (HardwareCostProfile.forTarget .x86_64) lbl
        (fun idx => keepSiteByAblations [CandidateAblationSample.mk 0 "fma" 1000 980 1 [(1000, 980)]] idx)
        { name := "fma", params := [], retTy := .i64,
          body := .letBind 3 .i64
            (.scalar (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))) (.ret 3) } 0 =
      ({ name := "fma", params := [], retTy := .i64,
         body := .letBind 3 .i64 (.scalar (.fma (.var 0) (.var 1) (.var 2))) (.ret 3),
         assurance := .verifiedKernelProof }, [r], 1) := by
    unfold superoptDeclSelective
    dsimp only []
    rw [hcodeKeep]
    rfl
  have hdeclPrune :
      superoptDeclSelective (HardwareCostProfile.forTarget .x86_64) lbl
        (fun idx => keepSiteByAblations [CandidateAblationSample.mk 0 "fma" 1000 995 1 [(1000, 995)]] idx)
        { name := "fma", params := [], retTy := .i64,
          body := .letBind 3 .i64
            (.scalar (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))) (.ret 3) } 0 =
      ({ name := "fma", params := [], retTy := .i64,
         body := .letBind 3 .i64
           (.scalar (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))) (.ret 3),
         assurance := .verifiedKernelProof }, [], 1) := by
    unfold superoptDeclSelective
    dsimp only []
    rw [hcodePrune]
    rfl
  dsimp only []
  simp only [autotuneSuperoptModule, hp]
  simp only [pruneCandidatesByAblation, superoptModuleSelective,
    List.foldl, List.nil_append, hlbl]
  unfold keepDeclSiteByAblations
  dsimp only [List.length]
  simp only [List.filter_cons, List.filter_nil, beq_self_eq_true, ite_true]
  rw [hdeclKeep, hdeclPrune]
  simp [corpusCalibrationReceipt, meetsCorpusGeomeanOnePercentGain,
    corpusProdBaseline, corpusProdCandidate, aggregateCorpusTimings, hcost,
    superoptDeclSelective, superoptCodeSelective, keepSiteByAblations, candidateAblationSurvives,
    hlbl, hr, hr0]


end LeanNative.Proofs
