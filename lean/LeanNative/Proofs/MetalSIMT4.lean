import LeanNative.Proofs.MetalSIMT3

namespace LeanNative.Proofs.MetalSIMT

open LeanNative.Backend.MetalAst

theorem laneInner_storeOut (nIn len : Nat)
    (inWords : Nat → List (BitVec 64)) (specWord : Nat → BitVec 64)
    (compute : MSLExpr)
    (hEval : ∀ (g : MSLGroupState) (tid : Dim3) (cx lo : Nat),
      cx < len → cx < 2 ^ 32 → len * 8 ≤ 2 ^ 64 → lo ≤ cx →
      g.structs = [] → g.funcs = [] → g.bindings = stdBindings nIn →
      g.constantBuffers = [(nIn + 1, ByteMemory.ofU64Words [BitVec.ofNat 64 len])] →
      (∀ j < nIn, g.deviceBuffers.lookup j = some (ByteMemory.ofU64Words (inWords j)) ∧
        (inWords j).length = len) →
      (∀ a ∈ g.epochLog, SimtLogInv nIn lo cx a) →
      let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
      ∃ log1,
        evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog compute =
          .ok { value := specWord cx, fields := [], locals := ls, log := log1 } ∧
        (∀ a ∈ log1, SimtLogInv nIn lo cx a)) :
    LaneInnerSpec nIn len 1 inWords specWord [.indexAssign "out" (.var "gid") compute] := by
  intro g done todo cx tx lo f outMem hcxLen hcx32 hlen64 hlo hf
    hstr hfn hbind hconst hin hout hsize hlog hdone hthreads
  let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
  let tid : Dim3 := { x := tx, y := 0, z := 0 }
  let th0 : MSLThreadState := { tid, locals := ls, stmts := [.indexAssign "out" (.var "gid") compute, .returnStmt], halted := false }
  have ⟨hlkGid, htyGid, hArr, _⟩ := initBuiltinLocal_gid_props cx hcx32
  have ⟨hvarGid, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog cx hcx32 hlkGid htyGid
  obtain ⟨log1, hrhs, hlog1⟩ := hEval g tid cx lo hcxLen hcx32 hlen64 hlo hstr hfn hbind hconst hin hlog
  have hArrOut : ls.lookupArray? "out" = none := by
    dsimp only [ls]; simp [MSLLocals.lookupArray?, hArr]
  have hBindOut : g.bindings.lookup "out" = some (.deviceBuf nIn false .ulong) := by
    rw [hbind]; exact stdBindings_lookup_out nIn
  obtain ⟨outMem', log2, hexecW, hsize', hreadCx, hreadNe, hlog2, hneEmpty⟩ :=
    exec_indexAssign_dev_write g th0 [.returnStmt] (.var "gid") compute nIn lo cx len (specWord cx) log1 outMem
      hvarGid hrhs hcxLen hlen64 hArrOut hBindOut hout hsize hlo hlog1
  have hf1 : f = (f - 2) + 1 + 1 := by omega
  let th1 : MSLThreadState := { th0 with stmts := [.returnStmt] }
  let g1 : MSLGroupState :=
    { g with epochLog := log2, deviceBuffers := setIndexedMem g.deviceBuffers nIn outMem', threads := done ++ (th1 :: todo) }
  have hstep1 : runGroupWithDeviceLog f g [] = runGroupWithDeviceLog ((f - 2) + 1) g1 [] := by
    rw [hf1]
    exact runGroupWithDeviceLog_step_stmt ((f - 2) + 1) g
      { g with epochLog := log2, deviceBuffers := setIndexedMem g.deviceBuffers nIn outMem' }
      done todo th0 th1 (.indexAssign "out" (.var "gid") compute) [.returnStmt]
      hthreads hdone rfl rfl rfl rfl hexecW (by intro h; simp [hneEmpty] at h)
  let th2 : MSLThreadState := { th1 with stmts := [], halted := true }
  let g2 : MSLGroupState := { g1 with threads := done ++ (th2 :: todo) }
  have hstep2 : runGroupWithDeviceLog ((f - 2) + 1) g1 [] = runGroupWithDeviceLog (f - 2) g2 [] :=
    runGroupWithDeviceLog_step_stmt (f - 2) g1 g1 done todo th1 th2 .returnStmt []
      rfl hdone rfl rfl rfl rfl (exec_returnStmt_step g1 th1 []) id
  refine ⟨f - 2, th2, g2, outMem', hstep1.trans hstep2, Nat.le_refl _, rfl, rfl,
    hstr, hfn, hbind, rfl, ?_, ?_, hsize', hreadCx, hreadNe, hlog2⟩
  · intro j hj
    dsimp only [g2, g1]
    rw [lookup_setIndexedMem_ne g.deviceBuffers nIn j outMem' (by omega)]
    exact (hin j hj).1
  · dsimp only [g2, g1]
    exact lookup_setIndexedMem_same g.deviceBuffers nIn outMem'

theorem laneInner_ifElse_storeOut (nIn len : Nat)
    (inWords : Nat → List (BitVec 64)) (specWord : Nat → BitVec 64)
    (cond thenExpr elseExpr : MSLExpr) (takeThen : Nat → Bool)
    (hCond : ∀ (g : MSLGroupState) (tid : Dim3) (cx lo : Nat),
      cx < len → cx < 2 ^ 32 → len * 8 ≤ 2 ^ 64 → lo ≤ cx →
      g.structs = [] → g.funcs = [] → g.bindings = stdBindings nIn →
      g.constantBuffers = [(nIn + 1, ByteMemory.ofU64Words [BitVec.ofNat 64 len])] →
      (∀ j < nIn, g.deviceBuffers.lookup j = some (ByteMemory.ofU64Words (inWords j)) ∧
        (inWords j).length = len) →
      (∀ a ∈ g.epochLog, SimtLogInv nIn lo cx a) →
      let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
      ∃ (cval : BitVec 64) (log1 : List MSLAccess),
        evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog cond =
          .ok { value := cval, fields := [], locals := ls, log := log1 } ∧
        (cval != 0#64) = takeThen cx ∧
        (log1.isEmpty = true → g.epochLog.isEmpty = true) ∧
        (∀ a ∈ log1, SimtLogInv nIn lo cx a))
    (hBranch : ∀ (g : MSLGroupState) (tid : Dim3) (cx lo : Nat),
      cx < len → cx < 2 ^ 32 → len * 8 ≤ 2 ^ 64 → lo ≤ cx →
      g.structs = [] → g.funcs = [] → g.bindings = stdBindings nIn →
      g.constantBuffers = [(nIn + 1, ByteMemory.ofU64Words [BitVec.ofNat 64 len])] →
      (∀ j < nIn, g.deviceBuffers.lookup j = some (ByteMemory.ofU64Words (inWords j)) ∧
        (inWords j).length = len) →
      (∀ a ∈ g.epochLog, SimtLogInv nIn lo cx a) →
      let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
      ∃ log2,
        evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog
          (if takeThen cx then thenExpr else elseExpr) =
          .ok { value := specWord cx, fields := [], locals := ls, log := log2 } ∧
        (∀ a ∈ log2, SimtLogInv nIn lo cx a)) :
    LaneInnerSpec nIn len 2 inWords specWord
      [.ifElse cond (.cons (.indexAssign "out" (.var "gid") thenExpr) .nil)
                    (.cons (.indexAssign "out" (.var "gid") elseExpr) .nil)] := by
  intro g done todo cx tx lo f outMem hcxLen hcx32 hlen64 hlo hf
    hstr hfn hbind hconst hin hout hsize hlog hdone hthreads
  let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
  let tid : Dim3 := { x := tx, y := 0, z := 0 }
  let stmtIf : MSLStmt := .ifElse cond (.cons (.indexAssign "out" (.var "gid") thenExpr) .nil)
                                       (.cons (.indexAssign "out" (.var "gid") elseExpr) .nil)
  let th0 : MSLThreadState := { tid, locals := ls, stmts := [stmtIf, .returnStmt], halted := false }
  obtain ⟨cval, log1, hcondEv, hcvalEq, hlog1Emp, hlog1⟩ :=
    hCond g tid cx lo hcxLen hcx32 hlen64 hlo hstr hfn hbind hconst hin hlog
  have hexecIf := exec_ifElse_step g th0 [.returnStmt] cond
    (.cons (.indexAssign "out" (.var "gid") thenExpr) .nil)
    (.cons (.indexAssign "out" (.var "gid") elseExpr) .nil) cval log1 hcondEv
  let chosen := if takeThen cx then thenExpr else elseExpr
  have hbrEq : (if cval != 0#64 then
      (MSLBlock.cons (.indexAssign "out" (.var "gid") thenExpr) .nil).toList
    else
      (MSLBlock.cons (.indexAssign "out" (.var "gid") elseExpr) .nil).toList) ++ [.returnStmt] =
    [.indexAssign "out" (.var "gid") chosen, .returnStmt] := by
    dsimp only [chosen]
    rw [hcvalEq]
    cases takeThen cx <;> rfl
  let th1 : MSLThreadState := { th0 with stmts := [.indexAssign "out" (.var "gid") chosen, .returnStmt] }
  let g1 : MSLGroupState := { g with epochLog := log1, threads := done ++ (th1 :: todo) }
  have hf1 : f = (f - 3) + 1 + 1 + 1 := by omega
  have hstep1 : runGroupWithDeviceLog f g [] = runGroupWithDeviceLog ((f - 3) + 1 + 1) g1 [] := by
    rw [hf1]
    rw [hbrEq] at hexecIf
    exact runGroupWithDeviceLog_step_stmt ((f - 3) + 1 + 1) g { g with epochLog := log1 }
      done todo th0 th1 stmtIf [.returnStmt] hthreads hdone rfl rfl rfl rfl hexecIf hlog1Emp
  have ⟨hlkGid, htyGid, hArr, _⟩ := initBuiltinLocal_gid_props cx hcx32
  have ⟨hvarGid, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g1) g1 tid ls g1.epochLog cx hcx32 hlkGid htyGid
  obtain ⟨log2, hrhs1, hlog2⟩ :=
    hBranch g1 tid cx lo hcxLen hcx32 hlen64 hlo hstr hfn hbind hconst hin hlog1
  have hArrOut : ls.lookupArray? "out" = none := by
    dsimp only [ls]; simp [MSLLocals.lookupArray?, hArr]
  have hBindOut : g1.bindings.lookup "out" = some (.deviceBuf nIn false .ulong) := by
    dsimp only [g1]; rw [hbind]; exact stdBindings_lookup_out nIn
  obtain ⟨outMem', log3, hexecW, hsize', hreadCx, hreadNe, hlog3, hneEmpty⟩ :=
    exec_indexAssign_dev_write g1 th1 [.returnStmt] (.var "gid") chosen nIn lo cx len (specWord cx) log2 outMem
      hvarGid hrhs1 hcxLen hlen64 hArrOut hBindOut hout hsize hlo hlog2
  let th2 : MSLThreadState := { th1 with stmts := [.returnStmt] }
  let g2 : MSLGroupState :=
    { g1 with epochLog := log3, deviceBuffers := setIndexedMem g1.deviceBuffers nIn outMem', threads := done ++ (th2 :: todo) }
  have hstep2 : runGroupWithDeviceLog ((f - 3) + 1 + 1) g1 [] = runGroupWithDeviceLog ((f - 3) + 1) g2 [] :=
    runGroupWithDeviceLog_step_stmt ((f - 3) + 1) g1
      { g1 with epochLog := log3, deviceBuffers := setIndexedMem g1.deviceBuffers nIn outMem' }
      done todo th1 th2 (.indexAssign "out" (.var "gid") chosen) [.returnStmt]
      rfl hdone rfl rfl rfl rfl hexecW (by intro h; simp [hneEmpty] at h)
  let th3 : MSLThreadState := { th2 with stmts := [], halted := true }
  let g3 : MSLGroupState := { g2 with threads := done ++ (th3 :: todo) }
  have hstep3 : runGroupWithDeviceLog ((f - 3) + 1) g2 [] = runGroupWithDeviceLog (f - 3) g3 [] :=
    runGroupWithDeviceLog_step_stmt (f - 3) g2 g2 done todo th2 th3 .returnStmt []
      rfl hdone rfl rfl rfl rfl (exec_returnStmt_step g2 th2 []) id
  refine ⟨f - 3, th3, g3, outMem', (hstep1.trans hstep2).trans hstep3, Nat.le_refl _, rfl, rfl,
    hstr, hfn, hbind, rfl, ?_, ?_, hsize', hreadCx, hreadNe, hlog3⟩
  · intro j hj
    dsimp only [g3, g2, g1]
    rw [lookup_setIndexedMem_ne g.deviceBuffers nIn j outMem' (by omega)]
    exact (hin j hj).1
  · dsimp only [g3, g2, g1]
    exact lookup_setIndexedMem_same g.deviceBuffers nIn outMem'

private theorem nodup_getElem_inj :
    ∀ {xs : List Nat} (_ : xs.Nodup) {i j : Nat} (hi : i < xs.length) (hj : j < xs.length),
      xs[i] = xs[j] → i = j
  | [], _, _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | x :: xs, hnd, 0, 0, _, _, _ => rfl
  | x :: xs, hnd, 0, j + 1, _, hj, heq => by
    rw [List.nodup_cons] at hnd
    have hx : x = xs[j]'(Nat.lt_of_succ_lt_succ hj) := heq
    have hmem : xs[j]'(Nat.lt_of_succ_lt_succ hj) ∈ xs := List.getElem_mem _
    rw [← hx] at hmem
    exact absurd hmem hnd.1
  | x :: xs, hnd, i + 1, 0, hi, _, heq => by
    rw [List.nodup_cons] at hnd
    have hx : xs[i]'(Nat.lt_of_succ_lt_succ hi) = x := heq
    have hmem : xs[i]'(Nat.lt_of_succ_lt_succ hi) ∈ xs := List.getElem_mem _
    rw [hx] at hmem
    exact absurd hmem hnd.1
  | x :: xs, hnd, i + 1, j + 1, hi, hj, heq => by
    rw [List.nodup_cons] at hnd
    exact congrArg Nat.succ (nodup_getElem_inj hnd.2 (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) heq)

private theorem lookup_loads_step (inVars : List Nat) (inWords : Nat → List (BitVec 64))
    (len cx : Nat) (hcxLen : cx < len)
    (hinLen : ∀ j < inVars.length, (inWords j).length = len)
    (hnodup : inVars.Nodup) :
    ∀ (rem k0 : Nat) (g : MSLGroupState) (done todo : List MSLThreadState)
      (ls : MSLLocals) (tx lo f : Nat),
      k0 + rem = inVars.length →
      cx < 2 ^ 32 → len * 8 ≤ 2 ^ 64 →
      rem ≤ f →
      g.structs = [] → g.funcs = [] → g.bindings = stdBindings inVars.length →
      (∀ j < inVars.length, g.deviceBuffers.lookup j = some (ByteMemory.ofU64Words (inWords j))) →
      (∀ a ∈ g.epochLog, SimtLogInv inVars.length lo cx a) →
      (∀ d ∈ done, d.halted = true) →
      ls.lookup? "gid" = some (BitVec.ofNat 64 cx) →
      ls.lookupType? "gid" = some .uint →
      ls.arrays = [] →
      ls.lookup? "gid64" = some (BitVec.ofNat 64 cx) →
      ls.lookupType? "gid64" = some .ulong →
      (∀ j < k0, ∃ (hj : j < inVars.length) (hc : cx < (inWords j).length),
        ls.lookup? s!"v{inVars[j]}" = some ((inWords j)[cx]) ∧
        ls.lookupType? s!"v{inVars[j]}" = some .ulong) →
      ∀ (tail : List MSLStmt),
      g.threads = done ++ (
        { tid := { x := tx, y := 0, z := 0 }
          locals := ls
          stmts := ((List.range rem).map (fun d =>
            let k := k0 + d
            MSLStmt.varDecl .ulong s!"v{inVars[k]?.getD 0}" (.index s!"in{k}" (.var "gid")))) ++ tail
          halted := false } :: todo) →
      ∃ (g' : MSLGroupState) (ls' : MSLLocals),
        runGroupWithDeviceLog f g [] = runGroupWithDeviceLog (f - rem) g' [] ∧
        g'.threads = done ++ (
          { tid := { x := tx, y := 0, z := 0 }, locals := ls', stmts := tail, halted := false } :: todo) ∧
        g'.structs = [] ∧ g'.funcs = [] ∧ g'.bindings = stdBindings inVars.length ∧
        g'.constantBuffers = g.constantBuffers ∧
        g'.deviceBuffers = g.deviceBuffers ∧
        (∀ a ∈ g'.epochLog, SimtLogInv inVars.length lo cx a) ∧
        ls'.lookup? "gid" = some (BitVec.ofNat 64 cx) ∧
        ls'.lookupType? "gid" = some .uint ∧
        ls'.arrays = [] ∧
        ls'.lookup? "gid64" = some (BitVec.ofNat 64 cx) ∧
        ls'.lookupType? "gid64" = some .ulong ∧
        (∀ j (hj : j < inVars.length), ∃ (hc : cx < (inWords j).length),
          ls'.lookup? s!"v{inVars[j]}" = some ((inWords j)[cx]) ∧
          ls'.lookupType? s!"v{inVars[j]}" = some .ulong)
  | 0, k0, g, done, todo, ls, tx, lo, f, hk0, _, _, _, hstr, hfn, hbind, _,
      hlog, _, hgidV, hgidT, harr, hgid64V, hgid64T, hprev, tail, hthreads => by
    have hkEq : k0 = inVars.length := by omega
    refine ⟨g, ls, by simp, by simpa using hthreads, hstr, hfn, hbind, rfl, rfl, hlog,
      hgidV, hgidT, harr, hgid64V, hgid64T, ?_⟩
    intro j hj
    rcases hprev j (by omega) with ⟨_, hc, hv, ht⟩
    exact ⟨hc, hv, ht⟩
  | rem + 1, k0, g, done, todo, ls, tx, lo, f, hk0, hcx32, hlen64, hf, hstr, hfn, hbind,
      hinDev, hlog, hdone, hgidV, hgidT, harr, hgid64V, hgid64T, hprev, tail, hthreads => by
    have hk0Lt : k0 < inVars.length := by omega
    have hgetD : inVars[k0]?.getD 0 = inVars[k0] := by simp [hk0Lt]
    let id0 := inVars[k0]
    let tid : Dim3 := { x := tx, y := 0, z := 0 }
    let restLoads := (List.range rem).map (fun d =>
      let k := (k0 + 1) + d
      MSLStmt.varDecl .ulong s!"v{inVars[k]?.getD 0}" (.index s!"in{k}" (.var "gid")))
    have hrangeMap : ((List.range (rem + 1)).map (fun d =>
        let k := k0 + d
        MSLStmt.varDecl .ulong s!"v{inVars[k]?.getD 0}" (.index s!"in{k}" (.var "gid")))) ++ tail =
        MSLStmt.varDecl .ulong s!"v{id0}" (.index s!"in{k0}" (.var "gid")) :: (restLoads ++ tail) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.add_zero, hgetD, List.cons_append]
      congr 1
      congr 1
      apply List.map_congr_left
      intro d _
      dsimp only [Function.comp, Nat.succ_eq_add_one]
      have ha : k0 + (d + 1) = (k0 + 1) + d := by omega
      rw [ha]
    let th0 : MSLThreadState :=
      { tid
        locals := ls
        stmts := MSLStmt.varDecl .ulong s!"v{id0}" (.index s!"in{k0}" (.var "gid")) ::
          (restLoads ++ tail)
        halted := false }
    have hthreads0 : g.threads = done ++ (th0 :: todo) := by
      rw [hthreads, hrangeMap]
    have ⟨hvarGid, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog cx hcx32 hgidV hgidT
    have hwLen0 : (inWords k0).length = len := hinLen k0 hk0Lt
    have hc0 : cx < (inWords k0).length := by omega
    have hw64 : (inWords k0).length < 2 ^ 64 := by omega
    have harrIn : ls.lookupArray? s!"in{k0}" = none := by simp [MSLLocals.lookupArray?, harr]
    have hbindIn : g.bindings.lookup s!"in{k0}" = some (.deviceBuf k0 true .ulong) := by
      rw [hbind]; exact stdBindings_lookup_in inVars.length k0 hk0Lt
    obtain ⟨log1, hreadEv, hlog1, hneEmp⟩ :=
      ev_index_dev_read kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog s!"in{k0}" (.var "gid")
        k0 inVars.length lo cx cx (inWords k0) hvarGid hc0 hw64 harrIn hbindIn (hinDev k0 hk0Lt) hk0Lt hlog
    have hexecDecl := exec_varDecl_ulong g th0 (restLoads ++ tail) s!"v{id0}" (.index s!"in{k0}" (.var "gid"))
      ((inWords k0)[cx]) log1 (by intro _ h; cases h) hreadEv
    let ls1 := ls.setTyped s!"v{id0}" .ulong ((inWords k0)[cx])
    let th1 : MSLThreadState := { tid, locals := ls1, stmts := restLoads ++ tail, halted := false }
    let g1 : MSLGroupState := { g with epochLog := log1, threads := done ++ (th1 :: todo) }
    have hf1 : f = (f - 1) + 1 := by omega
    have hstep1 : runGroupWithDeviceLog f g [] = runGroupWithDeviceLog (f - 1) g1 [] := by
      rw [hf1]
      exact runGroupWithDeviceLog_step_stmt (f - 1) g { g with epochLog := log1 }
        done todo th0 th1 (.varDecl .ulong s!"v{id0}" (.index s!"in{k0}" (.var "gid"))) (restLoads ++ tail)
        hthreads0 hdone rfl rfl rfl rfl hexecDecl (by intro h; simp [hneEmp] at h)
    have hneGid := (var_ne_special id0).2.2.1.symm
    have hneGid64 := (var_ne_special id0).2.2.2.symm
    have hgid1 := setTyped_lookup_ne ls s!"v{id0}" "gid" .ulong ((inWords k0)[cx]) hneGid
    have hgid641 := setTyped_lookup_ne ls s!"v{id0}" "gid64" .ulong ((inWords k0)[cx]) hneGid64
    have hprev1 : ∀ j < k0 + 1, ∃ (hj : j < inVars.length) (hc : cx < (inWords j).length),
        ls1.lookup? s!"v{inVars[j]}" = some ((inWords j)[cx]) ∧
        ls1.lookupType? s!"v{inVars[j]}" = some .ulong := by
      intro j hj
      by_cases hjk : j = k0
      · subst hjk
        have hsame := setTyped_lookup_same ls s!"v{id0}" .ulong ((inWords j)[cx])
        exact ⟨hk0Lt, hc0, hsame.1, hsame.2⟩
      · have hjLt : j < k0 := by omega
        rcases hprev j hjLt with ⟨hjIn, hcj, hvj, htj⟩
        have hneIdx : inVars[j] ≠ inVars[k0] := by
          intro heqVal
          exact hjk (nodup_getElem_inj hnodup hjIn hk0Lt heqVal)
        have hneStr : s!"v{inVars[j]}" ≠ s!"v{id0}" := fun hs =>
          hneIdx (prefix_nat_inj "v" inVars[j] id0 (by simpa [toString] using hs))
        have hneL := setTyped_lookup_ne ls s!"v{id0}" s!"v{inVars[j]}" .ulong ((inWords k0)[cx]) hneStr
        exact ⟨hjIn, hcj, hneL.1.trans hvj, hneL.2.trans htj⟩
    obtain ⟨g2, ls2, hstepRest, hth2, hstr2, hfn2, hbind2, hconst2, hdev2, hlog2,
            hgid2V, hgid2T, harr2, hgid642V, hgid642T, hallVars⟩ :=
      lookup_loads_step inVars inWords len cx hcxLen hinLen hnodup rem (k0 + 1) g1 done todo ls1 tx lo (f - 1)
        (by omega) hcx32 hlen64 (by omega) hstr hfn hbind hinDev hlog1 hdone
        (hgid1.1.trans hgidV) (hgid1.2.trans hgidT) harr (hgid641.1.trans hgid64V) (hgid641.2.trans hgid64T)
        hprev1 tail rfl
    have hfSub : f - 1 - rem = f - (rem + 1) := by omega
    rw [hfSub] at hstepRest
    exact ⟨g2, ls2, hstep1.trans hstepRest, hth2, hstr2, hfn2, hbind2, hconst2, hdev2, hlog2,
      hgid2V, hgid2T, harr2, hgid642V, hgid642T, hallVars⟩

theorem laneInner_varDecls_storeOut (inVars : List Nat) (len : Nat)
    (inWords : Nat → List (BitVec 64)) (specWord : Nat → BitVec 64)
    (rhs : MSLExpr) (hnodup : inVars.Nodup)
    (hRhs : ∀ (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals) (cx : Nat),
      cx < len → cx < 2 ^ 32 →
      ls.lookup? "gid64" = some (BitVec.ofNat 64 cx) →
      ls.lookupType? "gid64" = some .ulong →
      (∀ j (hj : j < inVars.length) (hc : cx < (inWords j).length),
        ls.lookup? s!"v{inVars[j]}" = some ((inWords j)[cx]) ∧
        ls.lookupType? s!"v{inVars[j]}" = some .ulong) →
      evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog rhs =
        .ok { value := specWord cx, fields := [], locals := ls, log := g.epochLog }) :
    LaneInnerSpec inVars.length len (inVars.length + 2) inWords specWord
      ([MSLStmt.varDecl .ulong "gid64" (.cast .ulong (.var "gid"))] ++
        (List.range inVars.length).map (fun k =>
          MSLStmt.varDecl .ulong s!"v{inVars[k]?.getD 0}" (.index s!"in{k}" (.var "gid"))) ++
        [MSLStmt.indexAssign "out" (.var "gid") rhs]) := by
  intro g done todo cx tx lo f outMem hcxLen hcx32 hlen64 hlo hf
    hstr hfn hbind hconst hin hout hsize hlog hdone hthreads
  let ls0 := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
  let tid : Dim3 := { x := tx, y := 0, z := 0 }
  let loads := (List.range inVars.length).map (fun d =>
    let k := 0 + d
    MSLStmt.varDecl .ulong s!"v{inVars[k]?.getD 0}" (.index s!"in{k}" (.var "gid")))
  have hloadsEq : (List.range inVars.length).map (fun k =>
      MSLStmt.varDecl .ulong s!"v{inVars[k]?.getD 0}" (.index s!"in{k}" (.var "gid"))) = loads := by
    apply List.map_congr_left
    intro d _; simp
  let tailW : List MSLStmt := [MSLStmt.indexAssign "out" (.var "gid") rhs, .returnStmt]
  let th0 : MSLThreadState :=
    { tid, locals := ls0
      stmts := MSLStmt.varDecl .ulong "gid64" (.cast .ulong (.var "gid")) :: (loads ++ tailW)
      halted := false }
  have hthreads0 : g.threads = done ++ (th0 :: todo) := by
    rw [hthreads, hloadsEq]
    simp [List.append_assoc, tailW, th0, ls0, tid]
  have ⟨hlkGid0, htyGid0, harr0, _⟩ := initBuiltinLocal_gid_props cx hcx32
  have ⟨_, hcastGid0⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls0 g.epochLog cx hcx32 hlkGid0 htyGid0
  have hexecGid64 := exec_varDecl_ulong g th0 (loads ++ tailW) "gid64" (.cast .ulong (.var "gid"))
    (BitVec.ofNat 64 cx) g.epochLog (by intro _ h; cases h) hcastGid0
  let ls1 := ls0.setTyped "gid64" .ulong (BitVec.ofNat 64 cx)
  let th1 : MSLThreadState := { tid, locals := ls1, stmts := loads ++ tailW, halted := false }
  let g1 : MSLGroupState := { g with threads := done ++ (th1 :: todo) }
  have hfStep0 : f = (f - 1) + 1 := by omega
  have hstep0 : runGroupWithDeviceLog f g [] = runGroupWithDeviceLog (f - 1) g1 [] := by
    rw [hfStep0]
    exact runGroupWithDeviceLog_step_stmt (f - 1) g g done todo th0 th1
      (.varDecl .ulong "gid64" (.cast .ulong (.var "gid"))) (loads ++ tailW)
      hthreads0 hdone rfl rfl rfl rfl hexecGid64 id
  have hneG64 : ("gid" : String) ≠ "gid64" := by decide
  have hgid1 := setTyped_lookup_ne ls0 "gid64" "gid" .ulong (BitVec.ofNat 64 cx) hneG64
  have hgid641 := setTyped_lookup_same ls0 "gid64" .ulong (BitVec.ofNat 64 cx)
  obtain ⟨g2, ls2, hstepLoads, hth2, hstr2, hfn2, hbind2, hconst2, hdev2, hlog2,
          hgid2V, hgid2T, harr2, hgid642V, hgid642T, hallVars⟩ :=
    lookup_loads_step inVars inWords len cx hcxLen (fun j hj => (hin j hj).2) hnodup
      inVars.length 0 g1 done todo ls1 tx lo (f - 1) (by omega) hcx32 hlen64 (by omega)
      hstr hfn hbind (fun j hj => (hin j hj).1) hlog hdone
      (hgid1.1.trans hlkGid0) (hgid1.2.trans htyGid0) harr0 hgid641.1 hgid641.2
      (fun _ hj => absurd hj (Nat.not_lt_zero _)) tailW rfl
  let th2 : MSLThreadState := { tid, locals := ls2, stmts := tailW, halted := false }
  have ⟨hvarGid2, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g2) g2 tid ls2 g2.epochLog cx hcx32 hgid2V hgid2T
  have hrhs2 := hRhs g2 tid ls2 cx hcxLen hcx32 hgid642V hgid642T
    (fun j hj _ => by rcases hallVars j hj with ⟨_, hv, ht⟩; exact ⟨hv, ht⟩)
  have harrOut2 : ls2.lookupArray? "out" = none := by simp [MSLLocals.lookupArray?, harr2]
  have hbindOut2 : g2.bindings.lookup "out" = some (.deviceBuf inVars.length false .ulong) := by
    rw [hbind2]; exact stdBindings_lookup_out inVars.length
  have hout2 : g2.deviceBuffers.lookup inVars.length = some outMem := by
    rw [hdev2]; exact hout
  obtain ⟨outMem', log3, hexecW, hsize', hreadCx, hreadNe, hlog3, hneEmp⟩ :=
    exec_indexAssign_dev_write g2 th2 [.returnStmt] (.var "gid") rhs inVars.length lo cx len (specWord cx)
      g2.epochLog outMem hvarGid2 hrhs2 hcxLen hlen64 harrOut2 hbindOut2 hout2 hsize hlo hlog2
  let fRem := f - (inVars.length + 3)
  have hfRemEq : f - 1 - inVars.length = fRem + 1 + 1 := by omega
  let th3 : MSLThreadState := { th2 with stmts := [.returnStmt] }
  let g3 : MSLGroupState :=
    { g2 with epochLog := log3, deviceBuffers := setIndexedMem g2.deviceBuffers inVars.length outMem', threads := done ++ (th3 :: todo) }
  have hstepW : runGroupWithDeviceLog (f - 1 - inVars.length) g2 [] = runGroupWithDeviceLog (fRem + 1) g3 [] := by
    rw [hfRemEq]
    exact runGroupWithDeviceLog_step_stmt (fRem + 1) g2
      { g2 with epochLog := log3, deviceBuffers := setIndexedMem g2.deviceBuffers inVars.length outMem' }
      done todo th2 th3 (.indexAssign "out" (.var "gid") rhs) [.returnStmt]
      hth2 hdone rfl rfl rfl rfl hexecW (by intro h; simp [hneEmp] at h)
  let th4 : MSLThreadState := { th3 with stmts := [], halted := true }
  let g4 : MSLGroupState := { g3 with threads := done ++ (th4 :: todo) }
  have hstepRet : runGroupWithDeviceLog (fRem + 1) g3 [] = runGroupWithDeviceLog fRem g4 [] :=
    runGroupWithDeviceLog_step_stmt fRem g3 g3 done todo th3 th4 .returnStmt []
      rfl hdone rfl rfl rfl rfl (exec_returnStmt_step g3 th3 []) id
  refine ⟨fRem, th4, g4, outMem', ((hstep0.trans hstepLoads).trans hstepW).trans hstepRet,
    Nat.le_refl _, rfl, rfl, hstr2, hfn2, hbind2, hconst2, ?_, ?_, hsize', hreadCx, hreadNe, hlog3⟩
  · intro j hj
    dsimp only [g4, g3]
    rw [lookup_setIndexedMem_ne g2.deviceBuffers inVars.length j outMem' (by omega), hdev2]
    exact (hin j hj).1
  · dsimp only [g4, g3]
    exact lookup_setIndexedMem_same g2.deviceBuffers inVars.length outMem'

theorem mslBlock_toList_ofList : ∀ (xs : List MSLStmt), (MSLBlock.ofList xs).toList = xs
  | [] => rfl
  | _ :: xs => congrArg (_ :: ·) (mslBlock_toList_ofList xs)

theorem runGroup_guarded_lanes (nIn len groupSize gx stepsInner : Nat)
    (inWords : Nat → List (BitVec 64)) (specWord : Nat → BitVec 64)
    (inner : List MSLStmt)
    (hInner : LaneInnerSpec nIn len stepsInner inWords specWord inner)
    (hlen64 : len * 8 ≤ 2 ^ 64) :
    let body := [MSLStmt.ifElse (.lt (.cast .ulong (.var "gid")) (.var "n")) (MSLBlock.ofList inner) .nil, .returnStmt]
    let mkLane := fun tx => ({
      tid := { x := tx, y := 0, z := 0 }
      locals := initBuiltinLocal MSLLocals.empty "gid" .uint (gx * groupSize + tx, 0, 0)
      stmts := body
      halted := false } : MSLThreadState)
    ∀ (rem tx0 f : Nat) (g : MSLGroupState) (done : List MSLThreadState) (outMem0 outMem : ByteMemory),
      tx0 + rem = groupSize →
      (gx + 1) * groupSize < 2 ^ 32 →
      rem * (stepsInner + 2) ≤ f →
      g.structs = [] → g.funcs = [] → g.bindings = stdBindings nIn →
      g.constantBuffers = [(nIn + 1, ByteMemory.ofU64Words [BitVec.ofNat 64 len])] →
      (∀ j < nIn, g.deviceBuffers.lookup j = some (ByteMemory.ofU64Words (inWords j)) ∧
        (inWords j).length = len) →
      g.deviceBuffers.lookup nIn = some outMem →
      outMem.bytes.size = len * 8 →
      (∀ i < len,
        (gx * groupSize ≤ i ∧ i < gx * groupSize + tx0 → outMem.readU64Word? i = some (specWord i)) ∧
        (¬ (gx * groupSize ≤ i ∧ i < gx * groupSize + tx0) → outMem.readU64Word? i = outMem0.readU64Word? i)) →
      (∀ a ∈ g.epochLog, SimtLogInv nIn (min len (gx * groupSize)) (min len (gx * groupSize + tx0)) a) →
      (∀ d ∈ done, d.halted = true) →
      g.threads = done ++ (List.range rem).map (fun d => mkLane (tx0 + d)) →
      ∃ (gFinal : MSLGroupState) (outMemFinal : ByteMemory),
        runGroupWithDeviceLog f g [] = .ok (gFinal, gFinal.epochLog.filter isDeviceAccess) ∧
        (∀ j < nIn, gFinal.deviceBuffers.lookup j = some (ByteMemory.ofU64Words (inWords j))) ∧
        gFinal.deviceBuffers.lookup nIn = some outMemFinal ∧
        outMemFinal.bytes.size = len * 8 ∧
        (∀ i < len,
          (gx * groupSize ≤ i ∧ i < (gx + 1) * groupSize → outMemFinal.readU64Word? i = some (specWord i)) ∧
          (¬ (gx * groupSize ≤ i ∧ i < (gx + 1) * groupSize) → outMemFinal.readU64Word? i = outMem0.readU64Word? i)) ∧
        (∀ a ∈ gFinal.epochLog.filter isDeviceAccess,
          SimtLogInv nIn (min len (gx * groupSize)) (min len ((gx + 1) * groupSize)) a)
  | 0, tx0, f, g, done, outMem0, outMem, htx, _, _, _, _, _, _, hin, hout, hsize, hwords, hlog, hdone, hthreads => by
    have htxEq : tx0 = groupSize := by omega
    have hcxEq : gx * groupSize + tx0 = (gx + 1) * groupSize := by rw [Nat.succ_mul]; omega
    have hallH : g.threads.all (·.halted) = true := by
      rw [hthreads, List.range_zero, List.map_nil, List.append_nil, List.all_eq_true]
      exact hdone
    refine ⟨g, outMem, runGroupWithDeviceLog_all_halted f g hallH,
      fun j hj => (hin j hj).1, hout, hsize, ?_, ?_⟩
    · intro i hi
      rw [← hcxEq]
      exact hwords i hi
    · intro a ha
      rw [List.mem_filter] at ha
      rw [← hcxEq]
      exact hlog a ha.1
  | rem + 1, tx0, f, g, done, outMem0, outMem, htx, hgrid32, hf, hstr, hfn, hbind,
      hconst, hin, hout, hsize, hwords, hlog, hdone, hthreads => by
    let body := [MSLStmt.ifElse (.lt (.cast .ulong (.var "gid")) (.var "n")) (MSLBlock.ofList inner) .nil, .returnStmt]
    let mkLane := fun tx => ({
      tid := { x := tx, y := 0, z := 0 }
      locals := initBuiltinLocal MSLLocals.empty "gid" .uint (gx * groupSize + tx, 0, 0)
      stmts := body
      halted := false } : MSLThreadState)
    let cx := gx * groupSize + tx0
    have hcx32 : cx < 2 ^ 32 := by
      have : cx < (gx + 1) * groupSize := by dsimp [cx]; rw [Nat.succ_mul]; omega
      omega
    let todo := (List.range rem).map (fun d => mkLane ((tx0 + 1) + d))
    have hmapSplit : (List.range (rem + 1)).map (fun d => mkLane (tx0 + d)) = mkLane tx0 :: todo := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.add_zero]
      congr 1
      apply List.map_congr_left
      intro d _
      dsimp only [Function.comp, Nat.succ_eq_add_one]
      have ha : tx0 + (d + 1) = (tx0 + 1) + d := by omega
      rw [ha]
    let th0 := mkLane tx0
    have hthreads0 : g.threads = done ++ (th0 :: todo) := by
      rw [hthreads, hmapSplit]
    let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
    let tid : Dim3 := { x := tx0, y := 0, z := 0 }
    have ⟨hlkGid, htyGid, _, hotherNone⟩ := initBuiltinLocal_gid_props cx hcx32
    have ⟨_, hcastGid⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog cx hcx32 hlkGid htyGid
    have hnNone := hotherNone "n" (by decide)
    have hbindN : g.bindings.lookup "n" = some (.constantScalar (nIn + 1) .ulong) := by
      rw [hbind]; exact stdBindings_lookup_n nIn
    have hconstN : g.constantBuffers.lookup (nIn + 1) = some (ByteMemory.ofU64Words [BitVec.ofNat 64 len]) := by
      rw [hconst]; simp
    have ⟨hevN, htyN⟩ := ev_var_const_ulong kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog
      "n" (nIn + 1) (BitVec.ofNat 64 len) hnNone.1 hnNone.2 hbindN hconstN
    have htyCast : inferExprType g ls (.cast .ulong (.var "gid")) = .ulong := rfl
    have hevLt := ev_lt_ulong kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog
      (.cast .ulong (.var "gid")) (.var "n") (BitVec.ofNat 64 cx) (BitVec.ofNat 64 len)
      hcastGid hevN htyCast htyN
    have hexecGuard := exec_ifElse_step g th0 [.returnStmt]
      (.lt (.cast .ulong (.var "gid")) (.var "n")) (MSLBlock.ofList inner) .nil
      (if BitVec.ult (BitVec.ofNat 64 cx) (BitVec.ofNat 64 len) then 1#64 else 0#64) g.epochLog hevLt
    have hultEq : BitVec.ult (BitVec.ofNat 64 cx) (BitVec.ofNat 64 len) = decide (cx < len) := by
      have hlenLt64 : len < 2 ^ 64 := by omega
      have hcxLt64 : cx < 2 ^ 64 := by omega
      simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcxLt64, Nat.mod_eq_of_lt hlenLt64]
    have hfOne : 1 ≤ f := by
      have : 1 * (stepsInner + 2) ≤ (rem + 1) * (stepsInner + 2) := Nat.mul_le_mul_right _ (by omega)
      omega
    have hfSplit : f = (f - 1) + 1 := by omega
    by_cases hcxLt : cx < len
    · have hcondNz : ((if BitVec.ult (BitVec.ofNat 64 cx) (BitVec.ofNat 64 len) then (1#64 : BitVec 64) else 0#64) != 0#64) = true := by
        rw [hultEq, decide_eq_true hcxLt]; rfl
      have htoList : (MSLBlock.ofList inner).toList = inner := mslBlock_toList_ofList inner
      let th1 : MSLThreadState := { tid, locals := ls, stmts := inner ++ [.returnStmt], halted := false }
      let g1 : MSLGroupState := { g with threads := done ++ (th1 :: todo) }
      have hstepG : runGroupWithDeviceLog f g [] = runGroupWithDeviceLog (f - 1) g1 [] := by
        rw [hfSplit]
        simp only [hcondNz, ite_true, htoList] at hexecGuard
        exact runGroupWithDeviceLog_step_stmt (f - 1) g g done todo th0 th1
          (.ifElse (.lt (.cast .ulong (.var "gid")) (.var "n")) (MSLBlock.ofList inner) .nil) [.returnStmt]
          hthreads0 hdone rfl rfl rfl rfl hexecGuard id
      have hminLo : min len (gx * groupSize) = gx * groupSize := Nat.min_eq_right (by dsimp [cx] at hcxLt; omega)
      have hminCx : min len cx = cx := Nat.min_eq_right (Nat.le_of_lt hcxLt)
      have hminCx1 : min len (gx * groupSize + (tx0 + 1)) = cx + 1 := by
        have : gx * groupSize + (tx0 + 1) = cx + 1 := by dsimp [cx]; omega
        rw [this]
        exact Nat.min_eq_right (by omega)
      have hlogIn : ∀ a ∈ g1.epochLog, SimtLogInv nIn (gx * groupSize) cx a := by
        intro a ha
        have h0 := hlog a ha
        rwa [hminLo, hminCx] at h0
      have hfIn : stepsInner + 1 ≤ f - 1 := by
        have : (rem + 1) * (stepsInner + 2) = rem * (stepsInner + 2) + (stepsInner + 2) := Nat.succ_mul rem (stepsInner + 2)
        omega
      obtain ⟨f', thH, g2, outMem', hstepIn, hfRem, hthH, hth2, hstr2, hfn2, hbind2, hconst2,
              hin2, hout2, hsize2, hreadCx, hreadNe, hlog2⟩ :=
        hInner g1 done todo cx tx0 (gx * groupSize) (f - 1) outMem hcxLt hcx32 hlen64
          (by dsimp [cx]; omega) hfIn hstr hfn hbind hconst hin hout hsize hlogIn hdone rfl
      have hthreadsNext : g2.threads = (done ++ [thH]) ++ todo := by
        rw [hth2, List.append_assoc]; rfl
      have hdoneNext : ∀ d ∈ done ++ [thH], d.halted = true := by
        intro d hd
        rcases List.mem_append.mp hd with h1 | h2
        · exact hdone d h1
        · rw [List.mem_singleton.mp h2]; exact hthH
      have hfNext : rem * (stepsInner + 2) ≤ f' := by
        have : (rem + 1) * (stepsInner + 2) = rem * (stepsInner + 2) + (stepsInner + 2) := Nat.succ_mul rem (stepsInner + 2)
        omega
      have hwordsNext : ∀ i < len,
          (gx * groupSize ≤ i ∧ i < gx * groupSize + (tx0 + 1) → outMem'.readU64Word? i = some (specWord i)) ∧
          (¬ (gx * groupSize ≤ i ∧ i < gx * groupSize + (tx0 + 1)) → outMem'.readU64Word? i = outMem0.readU64Word? i) := by
        intro i hi
        by_cases hicx : i = cx
        · subst hicx
          refine ⟨fun _ => hreadCx, fun hnot => absurd ⟨by dsimp [cx]; omega, by dsimp [cx]; omega⟩ hnot⟩
        · rw [hreadNe i hicx]
          rcases hwords i hi with ⟨hw1, hw2⟩
          refine ⟨fun ⟨h1, h2⟩ => hw1 ⟨h1, by dsimp [cx] at hicx; omega⟩,
                  fun hnot => hw2 (fun ⟨h1, h2⟩ => hnot ⟨h1, by omega⟩)⟩
      have hlogNext : ∀ a ∈ g2.epochLog, SimtLogInv nIn (min len (gx * groupSize)) (min len (gx * groupSize + (tx0 + 1))) a := by
        rw [hminLo, hminCx1]
        exact hlog2
      obtain ⟨gF, outMemF, hrest, hinF, houtF, hsizeF, hwordsF, hlogF⟩ :=
        runGroup_guarded_lanes nIn len groupSize gx stepsInner inWords specWord inner hInner hlen64
          rem (tx0 + 1) f' g2 (done ++ [thH]) outMem0 outMem' (by omega) hgrid32 hfNext
          hstr2 hfn2 hbind2 (hconst2.trans hconst) (fun j hj => ⟨hin2 j hj, (hin j hj).2⟩)
          hout2 hsize2 hwordsNext hlogNext hdoneNext hthreadsNext
      exact ⟨gF, outMemF, (hstepG.trans hstepIn).trans hrest, hinF, houtF, hsizeF, hwordsF, hlogF⟩
    · have hcondZ : ((if BitVec.ult (BitVec.ofNat 64 cx) (BitVec.ofNat 64 len) then (1#64 : BitVec 64) else 0#64) != 0#64) = false := by
        rw [hultEq, decide_eq_false hcxLt]; rfl
      let th1 : MSLThreadState := { tid, locals := ls, stmts := [.returnStmt], halted := false }
      let g1 : MSLGroupState := { g with threads := done ++ (th1 :: todo) }
      have hstepG : runGroupWithDeviceLog f g [] = runGroupWithDeviceLog (f - 1) g1 [] := by
        rw [hfSplit]
        simp only [hcondZ, Bool.false_eq_true, ite_false] at hexecGuard
        exact runGroupWithDeviceLog_step_stmt (f - 1) g g done todo th0 th1
          (.ifElse (.lt (.cast .ulong (.var "gid")) (.var "n")) (MSLBlock.ofList inner) .nil) [.returnStmt]
          hthreads0 hdone rfl rfl rfl rfl hexecGuard id
      have hfTwo : f - 1 = (f - 2) + 1 := by
        have : 1 * (stepsInner + 2) ≤ (rem + 1) * (stepsInner + 2) := Nat.mul_le_mul_right _ (by omega)
        omega
      let th2 : MSLThreadState := { th1 with stmts := [], halted := true }
      let g2 : MSLGroupState := { g1 with threads := done ++ (th2 :: todo) }
      have hstepR : runGroupWithDeviceLog (f - 1) g1 [] = runGroupWithDeviceLog (f - 2) g2 [] := by
        rw [hfTwo]
        exact runGroupWithDeviceLog_step_stmt (f - 2) g1 g1 done todo th1 th2 .returnStmt []
          rfl hdone rfl rfl rfl rfl (exec_returnStmt_step g1 th1 []) id
      have hthreadsNext : g2.threads = (done ++ [th2]) ++ todo := by
        dsimp only [g2]; rw [List.append_assoc]; rfl
      have hdoneNext : ∀ d ∈ done ++ [th2], d.halted = true := by
        intro d hd
        rcases List.mem_append.mp hd with h1 | h2
        · exact hdone d h1
        · rw [List.mem_singleton.mp h2]
      have hfNext : rem * (stepsInner + 2) ≤ f - 2 := by
        have : (rem + 1) * (stepsInner + 2) = rem * (stepsInner + 2) + (stepsInner + 2) := Nat.succ_mul rem (stepsInner + 2)
        omega
      have hwordsNext : ∀ i < len,
          (gx * groupSize ≤ i ∧ i < gx * groupSize + (tx0 + 1) → outMem.readU64Word? i = some (specWord i)) ∧
          (¬ (gx * groupSize ≤ i ∧ i < gx * groupSize + (tx0 + 1)) → outMem.readU64Word? i = outMem0.readU64Word? i) := by
        intro i hi
        have hiLtCx : i < cx := by omega
        rcases hwords i hi with ⟨hw1, hw2⟩
        refine ⟨fun ⟨h1, _⟩ => hw1 ⟨h1, hiLtCx⟩, fun hnot => ?_⟩
        refine hw2 (fun ⟨h1, _⟩ => hnot ⟨h1, ?_⟩)
        dsimp [cx] at hiLtCx
        omega
      have hminEq : min len (gx * groupSize + (tx0 + 1)) = min len cx := by dsimp [cx] at hcxLt ⊢; omega
      have hlogNext : ∀ a ∈ g2.epochLog, SimtLogInv nIn (min len (gx * groupSize)) (min len (gx * groupSize + (tx0 + 1))) a := by
        rw [hminEq]; exact hlog
      obtain ⟨gF, outMemF, hrest, hinF, houtF, hsizeF, hwordsF, hlogF⟩ :=
        runGroup_guarded_lanes nIn len groupSize gx stepsInner inWords specWord inner hInner hlen64
          rem (tx0 + 1) (f - 2) g2 (done ++ [th2]) outMem0 outMem (by omega) hgrid32 hfNext
          hstr hfn hbind hconst hin hout hsize hwordsNext hlogNext hdoneNext hthreadsNext
      exact ⟨gF, outMemF, (hstepG.trans hstepR).trans hrest, hinF, houtF, hsizeF, hwordsF, hlogF⟩


end LeanNative.Proofs.MetalSIMT
