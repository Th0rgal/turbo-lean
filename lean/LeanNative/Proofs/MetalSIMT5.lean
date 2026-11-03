import LeanNative.Proofs.MetalSIMT4

namespace LeanNative.Proofs.MetalSIMT

open LeanNative.Backend.MetalAst

private theorem evalMSLKernelLoop_guarded_groups (nIn len nGroups groupSize stepsInner fuelPerGroup : Nat)
    (k : MSLKernelDecl) (inWords : Nat → List (BitVec 64)) (specWord : Nat → BitVec 64)
    (inner : List MSLStmt)
    (hparams : k.params = stdKernelParams nIn)
    (hshared : k.sharedDecls = [])
    (hbody : k.body = [MSLStmt.ifElse (.lt (.cast .ulong (.var "gid")) (.var "n")) (MSLBlock.ofList inner) .nil, .returnStmt])
    (hInner : LaneInnerSpec nIn len stepsInner inWords specWord inner)
    (hlen64 : len * 8 ≤ 2 ^ 64)
    (hgrid32 : nGroups * groupSize < 2 ^ 32)
    (hfuel : groupSize * (stepsInner + 2) ≤ fuelPerGroup) :
    let gridDim : Dim3 := { x := nGroups, y := 1, z := 1 }
    let groupDim : Dim3 := { x := groupSize, y := 1, z := 1 }
    let constBufs := [(nIn + 1, ByteMemory.ofU64Words [BitVec.ofNat 64 len])]
    ∀ (rem gx0 : Nat) (devBufs : List (Nat × ByteMemory)) (outMem : ByteMemory)
      (priorLog : List MSLAccess),
      gx0 + rem = nGroups →
      (∀ j < nIn, devBufs.lookup j = some (ByteMemory.ofU64Words (inWords j)) ∧
        (inWords j).length = len) →
      devBufs.lookup nIn = some outMem →
      outMem.bytes.size = len * 8 →
      (∀ i < len, i < gx0 * groupSize → outMem.readU64Word? i = some (specWord i)) →
      (∀ a ∈ priorLog, SimtLogInv nIn 0 (min len (gx0 * groupSize)) a) →
      ∃ (devBufsF : List (Nat × ByteMemory)) (outMemF : ByteMemory),
        evalMSLKernelLoop fuelPerGroup k gridDim groupDim constBufs [] [] devBufs priorLog
          ((List.range rem).map (fun d => ({ x := gx0 + d, y := 0, z := 0 } : Dim3))) = .ok devBufsF ∧
        devBufsF.lookup nIn = some outMemF ∧
        (∀ i < len, i < nGroups * groupSize → outMemF.readU64Word? i = some (specWord i))
  | 0, gx0, devBufs, outMem, priorLog, hgx, _, hout, _, hwords, _ => by
    have hgxEq : gx0 = nGroups := by omega
    subst hgxEq
    refine ⟨devBufs, outMem, rfl, hout, hwords⟩
  | rem + 1, gx0, devBufs, outMem, priorLog, hgx, hin, hout, hsize, hwords, hprior => by
    let gridDim : Dim3 := { x := nGroups, y := 1, z := 1 }
    let groupDim : Dim3 := { x := groupSize, y := 1, z := 1 }
    let constBufs := [(nIn + 1, ByteMemory.ofU64Words [BitVec.ofNat 64 len])]
    have hmapG : (List.range (rem + 1)).map (fun d => ({ x := gx0 + d, y := 0, z := 0 } : Dim3)) =
        { x := gx0, y := 0, z := 0 } :: (List.range rem).map (fun d => ({ x := (gx0 + 1) + d, y := 0, z := 0 } : Dim3)) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.add_zero]
      congr 1
      apply List.map_congr_left
      intro d _
      dsimp only [Function.comp, Nat.succ_eq_add_one]
      have ha : gx0 + (d + 1) = (gx0 + 1) + d := by omega
      rw [ha]
    let g0 := initGroupState k gridDim groupDim { x := gx0, y := 0, z := 0 } devBufs constBufs [] [] fuelPerGroup
    have hgx1Lt : (gx0 + 1) * groupSize < 2 ^ 32 := by
      have hle : (gx0 + 1) * groupSize ≤ nGroups * groupSize := Nat.mul_le_mul_right groupSize (by omega)
      omega
    have hbind0 : g0.bindings = stdBindings nIn := by
      dsimp only [g0, initGroupState]
      exact buildKernelBindings_std k nIn hparams hshared
    let body := [MSLStmt.ifElse (.lt (.cast .ulong (.var "gid")) (.var "n")) (MSLBlock.ofList inner) .nil, .returnStmt]
    let mkLane := fun tx => ({
      tid := { x := tx, y := 0, z := 0 }
      locals := initBuiltinLocal MSLLocals.empty "gid" .uint (gx0 * groupSize + tx, 0, 0)
      stmts := body
      halted := false } : MSLThreadState)
    have hthreads0 : g0.threads = [] ++ (List.range groupSize).map (fun d => mkLane (0 + d)) := by
      dsimp only [g0, initGroupState]
      rw [dim3_coords_1d groupSize, List.map_map, List.nil_append]
      apply List.map_congr_left
      intro tx _
      dsimp only [Function.comp, Nat.zero_add, mkLane, body]
      rw [← hbody, initThreadLocals_std k _ _ nIn hparams]
      dsimp only [groupDim]
      simp [Nat.zero_add]
    obtain ⟨gFinal, outMem1, hrunG, hin1, hout1, hsize1, hwords1, hlog1⟩ :=
      runGroup_guarded_lanes nIn len groupSize gx0 stepsInner inWords specWord inner hInner hlen64
        groupSize 0 fuelPerGroup g0 [] outMem outMem (by omega) hgx1Lt hfuel
        rfl rfl hbind0 rfl hin hout hsize
        (fun i _ => ⟨fun ⟨h1, h2⟩ => absurd h2 (by omega), fun _ => rfl⟩)
        (fun _ h => nomatch h) (fun _ h => nomatch h) hthreads0
    have hloLe : min len (gx0 * groupSize) ≤ min len ((gx0 + 1) * groupSize) := by
      have : gx0 * groupSize ≤ (gx0 + 1) * groupSize := Nat.mul_le_mul_right groupSize (by omega)
      omega
    have ⟨hcross, hpriorNext⟩ := checkCrossGroupDeviceLog_ok nIn (min len (gx0 * groupSize))
      (min len ((gx0 + 1) * groupSize)) hloLe priorLog hprior
      (gFinal.epochLog.filter isDeviceAccess) hlog1
    have hwordsNext : ∀ i < len, i < (gx0 + 1) * groupSize → outMem1.readU64Word? i = some (specWord i) := by
      intro i hi hiLt
      by_cases hge : gx0 * groupSize ≤ i
      · exact (hwords1 i hi).1 ⟨hge, hiLt⟩
      · rw [(hwords1 i hi).2 (fun ⟨h1, _⟩ => hge h1)]
        exact hwords i hi (by omega)
    obtain ⟨devBufsF, outMemF, hrest, houtF, hwordsF⟩ :=
      evalMSLKernelLoop_guarded_groups nIn len nGroups groupSize stepsInner fuelPerGroup k inWords specWord inner
        hparams hshared hbody hInner hlen64 hgrid32 hfuel
        rem (gx0 + 1) gFinal.deviceBuffers outMem1 ((gFinal.epochLog.filter isDeviceAccess) ++ priorLog)
        (by omega) (fun j hj => ⟨hin1 j hj, (hin j hj).2⟩) hout1 hsize1 hwordsNext hpriorNext
    refine ⟨devBufsF, outMemF, ?_, houtF, hwordsF⟩
    rw [hmapG]
    change (match runGroupWithDeviceLog fuelPerGroup g0 [] with
      | .ok (gFinal, groupDevLog) =>
        match checkCrossGroupDeviceLog priorLog groupDevLog with
        | .ok () =>
          evalMSLKernelLoop fuelPerGroup k gridDim groupDim constBufs [] [] gFinal.deviceBuffers
            (groupDevLog ++ priorLog) ((List.range rem).map (fun d => ({ x := (gx0 + 1) + d, y := 0, z := 0 } : Dim3)))
        | err => propagateErr err
      | err => propagateErr err) = .ok devBufsF
    rw [hrunG]
    dsimp only
    rw [hcross]
    exact hrest

theorem evalMSLKernel_guarded_1d (nIn len nGroups groupSize stepsInner fuelPerGroup : Nat)
    (k : MSLKernelDecl) (inBufs : List (Nat × ByteMemory))
    (inWords : Nat → List (BitVec 64)) (specWord : Nat → BitVec 64)
    (inner : List MSLStmt)
    (hparams : k.params = stdKernelParams nIn)
    (hshared : k.sharedDecls = [])
    (hbody : k.body = [MSLStmt.ifElse (.lt (.cast .ulong (.var "gid")) (.var "n")) (MSLBlock.ofList inner) .nil, .returnStmt])
    (hInner : LaneInnerSpec nIn len stepsInner inWords specWord inner)
    (hlen64 : len * 8 ≤ 2 ^ 64)
    (hlenCov : len ≤ nGroups * groupSize)
    (hgrid32 : nGroups * groupSize < 2 ^ 32)
    (hfuel : groupSize * (stepsInner + 2) ≤ fuelPerGroup)
    (hinLookup : ∀ j < nIn, inBufs.lookup j = some (ByteMemory.ofU64Words (inWords j)) ∧
      (inWords j).length = len)
    (hinOutNone : inBufs.lookup nIn = none) :
    ∃ (devBufsF : List (Nat × ByteMemory)) (outMemF : ByteMemory),
      evalMSLKernel fuelPerGroup k { x := nGroups, y := 1, z := 1 } { x := groupSize, y := 1, z := 1 }
        (inBufs ++ [(nIn, ByteMemory.zeros (len * 8))])
        [(nIn + 1, ByteMemory.ofU64Words [BitVec.ofNat 64 len])] [] [] = .ok devBufsF ∧
      devBufsF.lookup nIn = some outMemF ∧
      (∀ i < len, outMemF.readU64Word? i = some (specWord i)) := by
  let devBufs0 := inBufs ++ [(nIn, ByteMemory.zeros (len * 8))]
  have hin0 : ∀ j < nIn, devBufs0.lookup j = some (ByteMemory.ofU64Words (inWords j)) ∧
      (inWords j).length = len := by
    intro j hj
    rcases hinLookup j hj with ⟨hlk, hlenJ⟩
    refine ⟨?_, hlenJ⟩
    dsimp only [devBufs0]
    rw [List.lookup_append, hlk]
    rfl
  have hout0 : devBufs0.lookup nIn = some (ByteMemory.zeros (len * 8)) := by
    dsimp only [devBufs0]
    rw [List.lookup_append, hinOutNone]
    simp
  have hsize0 : (ByteMemory.zeros (len * 8)).bytes.size = len * 8 := by
    simp [ByteMemory.zeros]
  obtain ⟨devBufsF, outMemF, hloop, houtF, hwordsF⟩ :=
    evalMSLKernelLoop_guarded_groups nIn len nGroups groupSize stepsInner fuelPerGroup k inWords specWord inner
      hparams hshared hbody hInner hlen64 hgrid32 hfuel
      nGroups 0 devBufs0 (ByteMemory.zeros (len * 8)) [] (by omega)
      hin0 hout0 hsize0 (fun _ _ h => absurd h (by simp)) (fun _ h => nomatch h)
  refine ⟨devBufsF, outMemF, ?_, houtF, fun i hi => hwordsF i hi (by omega)⟩
  unfold evalMSLKernel
  rw [dim3_coords_1d nGroups]
  have hmap0 : (List.range nGroups).map (fun x => ({ x := x, y := 0, z := 0 } : Dim3)) =
      (List.range nGroups).map (fun d => ({ x := 0 + d, y := 0, z := 0 } : Dim3)) := by
    apply List.map_congr_left
    intro d _; simp
  rw [hmap0]
  exact hloop



theorem ev_add_ulong_log (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log0 log1 log2 : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log0 a =
      .ok { value := va, fields := [], locals := ls, log := log1 })
    (hb : evalExprWithCall callEval fuel g tid ls log1 b =
      .ok { value := vb, fields := [], locals := ls, log := log2 })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log0 (.add a b) =
      .ok { value := va + vb, fields := [], locals := ls, log := log2 } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb, finishBin, hta, htb, promoteMSLArithType_ulong]
  rfl

theorem ev_mul_ulong_log (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log0 log1 log2 : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log0 a =
      .ok { value := va, fields := [], locals := ls, log := log1 })
    (hb : evalExprWithCall callEval fuel g tid ls log1 b =
      .ok { value := vb, fields := [], locals := ls, log := log2 })
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    evalExprWithCall callEval fuel g tid ls log0 (.mul a b) =
      .ok { value := va * vb, fields := [], locals := ls, log := log2 } := by
  rw [evalExprWithCall, ha]
  simp only [bindEval, hb, finishBin, hta, htb, promoteMSLArithType_ulong]
  rfl

theorem ev_logOr_bool (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (ba bb : Bool)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := if ba then 1#64 else 0#64, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := if bb then 1#64 else 0#64, fields := [], locals := ls, log := log }) :
    evalExprWithCall callEval fuel g tid ls log (.logOr a b) =
      .ok { value := if ba || bb then 1#64 else 0#64, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  cases ba
  · simp only [bindEval, hb]
    cases bb <;> rfl
  · simp only [bindEval]
    rfl

private theorem ev_std_in_log (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (name : String)
    (nIn k idx lo hi : Nat) (words : List (BitVec 64)) (idxExpr : MSLExpr)
    (hname : name = s!"in{k}")
    (hk : k < nIn) (hidxLt : idx < words.length) (hw64 : words.length < 2 ^ 64)
    (hbind : g.bindings = stdBindings nIn)
    (hdev : g.deviceBuffers.lookup k = some (ByteMemory.ofU64Words words))
    (hArr : ls.arrays = [])
    (hlog : ∀ a ∈ log, SimtLogInv nIn lo hi a)
    (hidx : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g tid ls log idxExpr =
      .ok { value := BitVec.ofNat 64 idx, fields := [], locals := ls, log := log }) :
    ∃ log',
      evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g tid ls log (.index name idxExpr) =
        .ok { value := words[idx], fields := [], locals := ls, log := log' } ∧
      inferExprType g ls (.index name idxExpr) = .ulong ∧
      (∀ a ∈ log', SimtLogInv nIn lo hi a) := by
  subst hname
  have harrK : ls.lookupArray? s!"in{k}" = none := by simp [MSLLocals.lookupArray?, hArr]
  have hbindK : g.bindings.lookup s!"in{k}" = some (.deviceBuf k true .ulong) := by
    rw [hbind]; exact stdBindings_lookup_in nIn k hk
  have ⟨log', hread, hlog', _⟩ := ev_index_dev_read kernelCallEval (effectiveCalleeFuel g) g tid ls
    log s!"in{k}" idxExpr k nIn lo hi idx words hidx hidxLt hw64 harrK hbindK hdev hk hlog
  refine ⟨log', hread, ?_, hlog'⟩
  simp only [inferExprType, harrK, hbindK]

private theorem ev_imm_ulong (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (bv : BitVec 64) :
    evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g tid ls log (.immU64 bv) =
      .ok { value := bv, fields := [], locals := ls, log := log } ∧
    inferExprType g ls (.immU64 bv) = .ulong := by
  refine ⟨?_, rfl⟩
  rw [evalExprWithCall]

private theorem infer_add_ulong (g : MSLGroupState) (ls : MSLLocals) (a b : MSLExpr)
    (ha : inferExprType g ls a = .ulong) (hb : inferExprType g ls b = .ulong) :
    inferExprType g ls (.add a b) = .ulong := by
  change promoteMSLArithType (inferExprType g ls a) (inferExprType g ls b) = .ulong
  rw [ha, hb]
  rfl

private theorem infer_mul_ulong (g : MSLGroupState) (ls : MSLLocals) (a b : MSLExpr)
    (ha : inferExprType g ls a = .ulong) (hb : inferExprType g ls b = .ulong) :
    inferExprType g ls (.mul a b) = .ulong := by
  change promoteMSLArithType (inferExprType g ls a) (inferExprType g ls b) = .ulong
  rw [ha, hb]
  rfl

theorem laneInner_mapScaleAdd (len : Nat) (scale bias : BitVec 64)
    (inWords : Nat → List (BitVec 64)) :
    LaneInnerSpec 1 len 1 inWords
      (fun cx =>
        if h : cx < (inWords 0).length then (inWords 0)[cx] * scale + bias else 0#64)
      [.indexAssign "out" (.var "gid")
        (.add (.mul (.index "in0" (.var "gid")) (.immU64 scale)) (.immU64 bias))] := by
  apply laneInner_storeOut
  intro g tid cx lo hcxLen hcx32 hlen64 _ _ _ hbind _ hin hlog
  let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
  have ⟨hlkGid, htyGid, hArr, _⟩ := initBuiltinLocal_gid_props cx hcx32
  have ⟨hvarGid, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog cx hcx32 hlkGid htyGid
  rcases hin 0 (by omega) with ⟨hdev0, hlen0⟩
  have hcx0 : cx < (inWords 0).length := by omega
  obtain ⟨log1, hin0, htin0, hlog1⟩ := ev_std_in_log g tid ls g.epochLog "in0" 1 0 cx lo cx
    (inWords 0) (.var "gid") rfl (by omega) hcx0 (by omega) hbind hdev0 hArr hlog hvarGid
  have ⟨hscale, htscale⟩ := ev_imm_ulong g tid ls log1 scale
  have hmul := ev_mul_ulong_log kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog log1 log1
    (.index "in0" (.var "gid")) (.immU64 scale) ((inWords 0)[cx]) scale hin0 hscale htin0 htscale
  have htmul := infer_mul_ulong g ls _ _ htin0 htscale
  have ⟨hbias, htbias⟩ := ev_imm_ulong g tid ls log1 bias
  have hadd := ev_add_ulong_log kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog log1 log1
    (.mul (.index "in0" (.var "gid")) (.immU64 scale)) (.immU64 bias)
    ((inWords 0)[cx] * scale) bias hmul hbias htmul htbias
  refine ⟨log1, ?_, hlog1⟩
  rw [dite_eq_left_of_eq_true (eq_true hcx0)]
  exact hadd

theorem laneInner_zipAdd (len : Nat) (inWords : Nat → List (BitVec 64)) :
    LaneInnerSpec 2 len 1 inWords
      (fun cx =>
        if h0 : cx < (inWords 0).length then
          if h1 : cx < (inWords 1).length then (inWords 0)[cx] + (inWords 1)[cx] else 0#64
        else 0#64)
      [.indexAssign "out" (.var "gid") (.add (.index "in0" (.var "gid")) (.index "in1" (.var "gid")))] := by
  apply laneInner_storeOut
  intro g tid cx lo hcxLen hcx32 hlen64 _ _ _ hbind _ hin hlog
  let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
  have ⟨hlkGid, htyGid, hArr, _⟩ := initBuiltinLocal_gid_props cx hcx32
  rcases hin 0 (by omega) with ⟨hdev0, hlen0⟩
  rcases hin 1 (by omega) with ⟨hdev1, hlen1⟩
  have hcx0 : cx < (inWords 0).length := by omega
  have hcx1 : cx < (inWords 1).length := by omega
  have ⟨hvarGid0, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog cx hcx32 hlkGid htyGid
  obtain ⟨log1, hin0, htin0, hlog1⟩ := ev_std_in_log g tid ls g.epochLog "in0" 2 0 cx lo cx
    (inWords 0) (.var "gid") rfl (by omega) hcx0 (by omega) hbind hdev0 hArr hlog hvarGid0
  have ⟨hvarGid1, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls log1 cx hcx32 hlkGid htyGid
  obtain ⟨log2, hin1, htin1, hlog2⟩ := ev_std_in_log g tid ls log1 "in1" 2 1 cx lo cx
    (inWords 1) (.var "gid") rfl (by omega) hcx1 (by omega) hbind hdev1 hArr hlog1 hvarGid1
  have hadd := ev_add_ulong_log kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog log1 log2
    (.index "in0" (.var "gid")) (.index "in1" (.var "gid")) ((inWords 0)[cx]) ((inWords 1)[cx])
    hin0 hin1 htin0 htin1
  refine ⟨log2, ?_, hlog2⟩
  rw [dite_eq_left_of_eq_true (eq_true hcx0), dite_eq_left_of_eq_true (eq_true hcx1)]
  exact hadd

theorem laneInner_zipMul (len : Nat) (inWords : Nat → List (BitVec 64)) :
    LaneInnerSpec 2 len 1 inWords
      (fun cx =>
        if h0 : cx < (inWords 0).length then
          if h1 : cx < (inWords 1).length then (inWords 0)[cx] * (inWords 1)[cx] else 0#64
        else 0#64)
      [.indexAssign "out" (.var "gid") (.mul (.index "in0" (.var "gid")) (.index "in1" (.var "gid")))] := by
  apply laneInner_storeOut
  intro g tid cx lo hcxLen hcx32 hlen64 _ _ _ hbind _ hin hlog
  let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
  have ⟨hlkGid, htyGid, hArr, _⟩ := initBuiltinLocal_gid_props cx hcx32
  rcases hin 0 (by omega) with ⟨hdev0, hlen0⟩
  rcases hin 1 (by omega) with ⟨hdev1, hlen1⟩
  have hcx0 : cx < (inWords 0).length := by omega
  have hcx1 : cx < (inWords 1).length := by omega
  have ⟨hvarGid0, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog cx hcx32 hlkGid htyGid
  obtain ⟨log1, hin0, htin0, hlog1⟩ := ev_std_in_log g tid ls g.epochLog "in0" 2 0 cx lo cx
    (inWords 0) (.var "gid") rfl (by omega) hcx0 (by omega) hbind hdev0 hArr hlog hvarGid0
  have ⟨hvarGid1, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls log1 cx hcx32 hlkGid htyGid
  obtain ⟨log2, hin1, htin1, hlog2⟩ := ev_std_in_log g tid ls log1 "in1" 2 1 cx lo cx
    (inWords 1) (.var "gid") rfl (by omega) hcx1 (by omega) hbind hdev1 hArr hlog1 hvarGid1
  have hmul := ev_mul_ulong_log kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog log1 log2
    (.index "in0" (.var "gid")) (.index "in1" (.var "gid")) ((inWords 0)[cx]) ((inWords 1)[cx])
    hin0 hin1 htin0 htin1
  refine ⟨log2, ?_, hlog2⟩
  rw [dite_eq_left_of_eq_true (eq_true hcx0), dite_eq_left_of_eq_true (eq_true hcx1)]
  exact hmul

theorem laneInner_saxpy (len : Nat) (alpha : BitVec 64) (inWords : Nat → List (BitVec 64)) :
    LaneInnerSpec 2 len 1 inWords
      (fun cx =>
        if h0 : cx < (inWords 0).length then
          if h1 : cx < (inWords 1).length then alpha * (inWords 0)[cx] + (inWords 1)[cx] else 0#64
        else 0#64)
      [.indexAssign "out" (.var "gid")
        (.add (.mul (.immU64 alpha) (.index "in0" (.var "gid"))) (.index "in1" (.var "gid")))] := by
  apply laneInner_storeOut
  intro g tid cx lo hcxLen hcx32 hlen64 _ _ _ hbind _ hin hlog
  let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
  have ⟨hlkGid, htyGid, hArr, _⟩ := initBuiltinLocal_gid_props cx hcx32
  rcases hin 0 (by omega) with ⟨hdev0, hlen0⟩
  rcases hin 1 (by omega) with ⟨hdev1, hlen1⟩
  have hcx0 : cx < (inWords 0).length := by omega
  have hcx1 : cx < (inWords 1).length := by omega
  have ⟨halpha, htalpha⟩ := ev_imm_ulong g tid ls g.epochLog alpha
  have ⟨hvarGid0, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog cx hcx32 hlkGid htyGid
  obtain ⟨log1, hin0, htin0, hlog1⟩ := ev_std_in_log g tid ls g.epochLog "in0" 2 0 cx lo cx
    (inWords 0) (.var "gid") rfl (by omega) hcx0 (by omega) hbind hdev0 hArr hlog hvarGid0
  have hmul := ev_mul_ulong_log kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog g.epochLog log1
    (.immU64 alpha) (.index "in0" (.var "gid")) alpha ((inWords 0)[cx]) halpha hin0 htalpha htin0
  have htmul := infer_mul_ulong g ls _ _ htalpha htin0
  have ⟨hvarGid1, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls log1 cx hcx32 hlkGid htyGid
  obtain ⟨log2, hin1, htin1, hlog2⟩ := ev_std_in_log g tid ls log1 "in1" 2 1 cx lo cx
    (inWords 1) (.var "gid") rfl (by omega) hcx1 (by omega) hbind hdev1 hArr hlog1 hvarGid1
  have hadd := ev_add_ulong_log kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog log1 log2
    (.mul (.immU64 alpha) (.index "in0" (.var "gid"))) (.index "in1" (.var "gid"))
    (alpha * (inWords 0)[cx]) ((inWords 1)[cx]) hmul hin1 htmul htin1
  refine ⟨log2, ?_, hlog2⟩
  rw [dite_eq_left_of_eq_true (eq_true hcx0), dite_eq_left_of_eq_true (eq_true hcx1)]
  exact hadd

theorem laneInner_stencil1D3Pt (len : Nat) (wL wC wR : BitVec 64)
    (inWords : Nat → List (BitVec 64)) :
    let i := MSLExpr.cast .ulong (.var "gid")
    let edge := MSLExpr.logOr (.eq i (.immU64 0#64)) (.ge (.add i (.immU64 1#64)) (.var "n"))
    let center := MSLExpr.index "in0" (.var "gid")
    let interior := MSLExpr.add (.add
      (.mul (.immU64 wL) (.index "in0" (.sub i (.immU64 1#64))))
      (.mul (.immU64 wC) center))
      (.mul (.immU64 wR) (.index "in0" (.add i (.immU64 1#64))))
    LaneInnerSpec 1 len 2 inWords
      (fun cx =>
        if cx == 0 || cx + 1 >= len then
          if h0 : cx < (inWords 0).length then (inWords 0)[cx] else 0#64
        else
          if hL : cx - 1 < (inWords 0).length then
            if hC : cx < (inWords 0).length then
              if hR : cx + 1 < (inWords 0).length then
                wL * (inWords 0)[cx - 1] + wC * (inWords 0)[cx] + wR * (inWords 0)[cx + 1]
              else 0#64
            else 0#64
          else 0#64)
      [.ifElse edge (.cons (.indexAssign "out" (.var "gid") center) .nil)
                    (.cons (.indexAssign "out" (.var "gid") interior) .nil)] := by
  let i := MSLExpr.cast .ulong (.var "gid")
  let edge := MSLExpr.logOr (.eq i (.immU64 0#64)) (.ge (.add i (.immU64 1#64)) (.var "n"))
  let center := MSLExpr.index "in0" (.var "gid")
  let interior := MSLExpr.add (.add
    (.mul (.immU64 wL) (.index "in0" (.sub i (.immU64 1#64))))
    (.mul (.immU64 wC) center))
    (.mul (.immU64 wR) (.index "in0" (.add i (.immU64 1#64))))
  apply laneInner_ifElse_storeOut 1 len inWords _ edge center interior (fun cx => cx == 0 || decide (len ≤ cx + 1))
  · intro g tid cx lo hcxLen hcx32 hlen64 _ _ _ hbind hconst _ hlog0
    let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
    have ⟨hlkGid, htyGid, _, hotherNone⟩ := initBuiltinLocal_gid_props cx hcx32
    have ⟨_, hcastGid⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog cx hcx32 hlkGid htyGid
    have hti : inferExprType g ls i = .ulong := rfl
    have ⟨hu0, htu0⟩ := ev_imm_ulong g tid ls g.epochLog 0#64
    have heq0 := ev_eq_ulong kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog
      i (.immU64 0#64) (BitVec.ofNat 64 cx) 0#64 hcastGid hu0 hti htu0
    have ⟨hu1, htu1⟩ := ev_imm_ulong g tid ls g.epochLog 1#64
    have hadd1 := ev_add_ulong kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog
      i (.immU64 1#64) (BitVec.ofNat 64 cx) 1#64 hcastGid hu1 hti htu1
    have htadd1 := infer_add_ulong g ls _ _ hti htu1
    have hnNone := hotherNone "n" (by decide)
    have hbindN : g.bindings.lookup "n" = some (.constantScalar 2 .ulong) := by
      rw [hbind]; exact stdBindings_lookup_n 1
    have hconstN : g.constantBuffers.lookup 2 = some (ByteMemory.ofU64Words [BitVec.ofNat 64 len]) := by
      rw [hconst]; simp
    have ⟨hevN, htyN⟩ := ev_var_const_ulong kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog
      "n" 2 (BitVec.ofNat 64 len) hnNone.1 hnNone.2 hbindN hconstN
    have hge := ev_ge_ulong kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog
      (.add i (.immU64 1#64)) (.var "n") (BitVec.ofNat 64 cx + 1#64) (BitVec.ofNat 64 len)
      hadd1 hevN htadd1 htyN
    have hor := ev_logOr_bool kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog
      (.eq i (.immU64 0#64)) (.ge (.add i (.immU64 1#64)) (.var "n"))
      (BitVec.ofNat 64 cx == 0#64) (BitVec.ule (BitVec.ofNat 64 len) (BitVec.ofNat 64 cx + 1#64))
      heq0 hge
    have hcxEq0 : (BitVec.ofNat 64 cx == 0#64) = (cx == 0) := by
      have hcx64 : cx < 2 ^ 64 := by omega
      cases cx with
      | zero => rfl
      | succ c =>
        have hneBv : BitVec.ofNat 64 (c + 1) ≠ 0#64 := by
          intro heqBv
          have htn : (BitVec.ofNat 64 (c + 1)).toNat = 0 := congrArg BitVec.toNat heqBv
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcx64] at htn
          omega
        exact beq_eq_false_iff_ne.mpr hneBv
    have hgeEq : BitVec.ule (BitVec.ofNat 64 len) (BitVec.ofNat 64 cx + 1#64) = decide (len ≤ cx + 1) := by
      have hlenLt64 : len < 2 ^ 64 := by omega
      have hcx1Lt64 : cx + 1 < 2 ^ 64 := by omega
      have hsum : BitVec.ofNat 64 cx + 1#64 = BitVec.ofNat 64 (cx + 1) := by
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cx < 2 ^ 64), Nat.mod_eq_of_lt hcx1Lt64]
      rw [hsum]
      simp [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlenLt64, Nat.mod_eq_of_lt hcx1Lt64]
    refine ⟨if (cx == 0 || decide (len ≤ cx + 1)) then 1#64 else 0#64, g.epochLog, ?_, ?_, id, hlog0⟩
    · rw [hcxEq0, hgeEq] at hor
      exact hor
    · cases (cx == 0 || decide (len ≤ cx + 1)) <;> rfl
  · intro g tid cx lo hcxLen hcx32 hlen64 _ _ _ hbind _ hin hlog
    let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
    have ⟨hlkGid, htyGid, hArr, _⟩ := initBuiltinLocal_gid_props cx hcx32
    rcases hin 0 (by omega) with ⟨hdev0, hlen0⟩
    have hcx0 : cx < (inWords 0).length := by omega
    by_cases hedge : (cx == 0 || decide (len ≤ cx + 1)) = true
    · simp only [hedge, ge_iff_le, ite_true, dite_eq_left_of_eq_true (eq_true hcx0)]
      have ⟨hvarGid, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog cx hcx32 hlkGid htyGid
      obtain ⟨log1, hinC, _, hlog1⟩ := ev_std_in_log g tid ls g.epochLog "in0" 1 0 cx lo cx
        (inWords 0) (.var "gid") rfl (by omega) hcx0 (by omega) hbind hdev0 hArr hlog hvarGid
      exact ⟨log1, hinC, hlog1⟩
    · have hedgeF : (cx == 0 || decide (len ≤ cx + 1)) = false := Bool.eq_false_iff.mpr hedge
      have hcxPos : 0 < cx := by
        cases cx with
        | zero => simp at hedgeF
        | succ c => omega
      have hcx1LtLen : cx + 1 < len := by
        rcases Bool.or_eq_false_iff.mp hedgeF with ⟨_, h2⟩
        simp only [decide_eq_false_iff_not] at h2
        omega
      have hL : cx - 1 < (inWords 0).length := by omega
      have hR : cx + 1 < (inWords 0).length := by omega
      simp only [hedgeF, ge_iff_le, Bool.false_eq_true, ite_false,
        dite_eq_left_of_eq_true (eq_true hL), dite_eq_left_of_eq_true (eq_true hcx0), dite_eq_left_of_eq_true (eq_true hR)]
      have hti : inferExprType g ls i = .ulong := rfl
      -- 1) wL * in0[i - 1]
      have ⟨hwL0, htwL⟩ := ev_imm_ulong g tid ls g.epochLog wL
      have ⟨_, hcast0⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog cx hcx32 hlkGid htyGid
      have ⟨hu1_0, htu1⟩ := ev_imm_ulong g tid ls g.epochLog 1#64
      have hsub1 := ev_sub_ulong kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog
        i (.immU64 1#64) (BitVec.ofNat 64 cx) 1#64 hcast0 hu1_0 hti htu1
      have hsubEq : BitVec.ofNat 64 cx - 1#64 = BitVec.ofNat 64 (cx - 1) := by
        apply BitVec.eq_of_toNat_eq
        have hcx64 : cx < 2 ^ 64 := by omega
        have hcxm64 : cx - 1 < 2 ^ 64 := by omega
        simp [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcx64, Nat.mod_eq_of_lt hcxm64]
        omega
      rw [hsubEq] at hsub1
      obtain ⟨log1, hinL, htinL, hlog1⟩ := ev_std_in_log g tid ls g.epochLog "in0" 1 0 (cx - 1) lo cx
        (inWords 0) (.sub i (.immU64 1#64)) rfl (by omega) hL (by omega) hbind hdev0 hArr hlog hsub1
      have hmulL := ev_mul_ulong_log kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog g.epochLog log1
        (.immU64 wL) (.index "in0" (.sub i (.immU64 1#64))) wL ((inWords 0)[cx - 1]) hwL0 hinL htwL htinL
      have htmulL := infer_mul_ulong g ls _ _ htwL htinL
      -- 2) wC * in0[gid]
      have ⟨hwC1, htwC⟩ := ev_imm_ulong g tid ls log1 wC
      have ⟨hvarGid1, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls log1 cx hcx32 hlkGid htyGid
      obtain ⟨log2, hinC, htinC, hlog2⟩ := ev_std_in_log g tid ls log1 "in0" 1 0 cx lo cx
        (inWords 0) (.var "gid") rfl (by omega) hcx0 (by omega) hbind hdev0 hArr hlog1 hvarGid1
      have hmulC := ev_mul_ulong_log kernelCallEval (effectiveCalleeFuel g) g tid ls log1 log1 log2
        (.immU64 wC) center wC ((inWords 0)[cx]) hwC1 hinC htwC htinC
      have htmulC := infer_mul_ulong g ls _ _ htwC htinC
      have haddLC := ev_add_ulong_log kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog log1 log2
        (.mul (.immU64 wL) (.index "in0" (.sub i (.immU64 1#64)))) (.mul (.immU64 wC) center)
        (wL * (inWords 0)[cx - 1]) (wC * (inWords 0)[cx]) hmulL hmulC htmulL htmulC
      have htaddLC := infer_add_ulong g ls _ _ htmulL htmulC
      -- 3) wR * in0[i + 1]
      have ⟨hwR2, htwR⟩ := ev_imm_ulong g tid ls log2 wR
      have ⟨_, hcast2⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls log2 cx hcx32 hlkGid htyGid
      have ⟨hu1_2, _⟩ := ev_imm_ulong g tid ls log2 1#64
      have hadd1 := ev_add_ulong kernelCallEval (effectiveCalleeFuel g) g tid ls log2
        i (.immU64 1#64) (BitVec.ofNat 64 cx) 1#64 hcast2 hu1_2 hti htu1
      have haddEq : BitVec.ofNat 64 cx + 1#64 = BitVec.ofNat 64 (cx + 1) := by
        apply BitVec.eq_of_toNat_eq
        have hcx64 : cx < 2 ^ 64 := by omega
        have hcxp64 : cx + 1 < 2 ^ 64 := by omega
        simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcx64, Nat.mod_eq_of_lt hcxp64]
      rw [haddEq] at hadd1
      obtain ⟨log3, hinR, htinR, hlog3⟩ := ev_std_in_log g tid ls log2 "in0" 1 0 (cx + 1) lo cx
        (inWords 0) (.add i (.immU64 1#64)) rfl (by omega) hR (by omega) hbind hdev0 hArr hlog2 hadd1
      have hmulR := ev_mul_ulong_log kernelCallEval (effectiveCalleeFuel g) g tid ls log2 log2 log3
        (.immU64 wR) (.index "in0" (.add i (.immU64 1#64))) wR ((inWords 0)[cx + 1]) hwR2 hinR htwR htinR
      have htmulR := infer_mul_ulong g ls _ _ htwR htinR
      have haddAll := ev_add_ulong_log kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog log2 log3
        (.add (.mul (.immU64 wL) (.index "in0" (.sub i (.immU64 1#64)))) (.mul (.immU64 wC) center))
        (.mul (.immU64 wR) (.index "in0" (.add i (.immU64 1#64))))
        (wL * (inWords 0)[cx - 1] + wC * (inWords 0)[cx]) (wR * (inWords 0)[cx + 1])
        haddLC hmulR htaddLC htmulR
      exact ⟨log3, haddAll, hlog3⟩




end LeanNative.Proofs.MetalSIMT
