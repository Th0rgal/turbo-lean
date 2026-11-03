import LeanNative.Backend.MetalLower
import LeanNative.Proofs.MetalLowerProofs

namespace LeanNative.Proofs.MetalMutantProofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend
open LeanNative.Backend.MetalAst
open LeanNative.Backend.MetalLower
open LeanNative.Proofs
open LeanNative.Proofs.MetalSIMT
open LeanNative.Proofs.MetalLowerSpec
open LeanNative.Proofs.MetalLowerProofs

/-- Non-vacuity witness for `lowerToMetal_evalMSLKernel_sound`: a concrete 2-element
`customScalar` kernel `(x[gid] <<< 32) + (y[gid] / z[gid])` with a zero divisor in lane 1
lowers to `MetalAst`, satisfies all preconditions of `lowerToMetal_evalMSLKernel_sound`,
and executes in `evalMSLKernel` to produce `[1 <<< 32 + 18 / 3, 2 <<< 32 + 0]`. -/
theorem lowerToMetal_nonvacuous :
    ∃ (k : ParallelKernelKind) (env : VarEnv) (st : HeapState)
      (inBufs devBufsF : List (Nat × ByteMemory))
      (elems : List UInt64) (kern : MSLKernelDecl) (outMemF : ByteMemory),
      wfMetalKernel k = true ∧
      packInputDeviceBuffers env st [10, 11, 12] 2 = some inBufs ∧
      lowerToMetal "nv_metal" k = { kernels := [kern], structs := [], funcs := [] } ∧
      evalParKernelLoop env st [10, 11, 12] 2 k (List.range 2) = .ok elems ∧
      elems = [4294967302, 8589934592] ∧
      evalMSLKernel (groupStepsForKind 2 k) kern
        { x := 1, y := 1, z := 1 } { x := 2, y := 1, z := 1 }
        (mkDeviceBuffers inBufs (kernelArity k) 2)
        (mkConstLenBuffers (kernelArity k) 2) [] [] = .ok devBufsF ∧
      devBufsF.lookup (kernelArity k) = some outMemF ∧
      outMemF.readU64Word? 0 = some (4294967302#64) ∧
      outMemF.readU64Word? 1 = some (8589934592#64) := by
  let k : ParallelKernelKind :=
    .customScalar 0 [1, 2, 3]
      (.binOp .add
        (.binOp .shl (.var 1) (.constU64 32))
        (.binOp .div (.var 2) (.var 3)))
  let env : VarEnv :=
    (((VarEnv.empty.bind 10 (.sarrayId 1)).bind 11 (.sarrayId 2)).bind 12 (.sarrayId 3))
  let st : HeapState :=
    { buffers :=
        [ { id := 1, exclusive := true, data := #[1, 2] }
        , { id := 2, exclusive := true, data := #[18, 99] }
        , { id := 3, exclusive := true, data := #[3, 0] } ]
      nextId := 4 }
  have hwf : wfMetalKernel k = true := rfl
  cases hpack : packInputDeviceBuffers env st [10, 11, 12] 2 with
  | none =>
    exfalso
    revert hpack
    simp [packInputDeviceBuffers, packInputDeviceBuffersGo, packOneDeviceBuffer, env, st,
      VarEnv.bind, HeapState.findBuffer]
  | some inBufs =>
    have hlen : ([10, 11, 12] : List VarId).length = kernelArity k := rfl
    have hcov : 2 ≤ 1 * 2 := by omega
    have h32 : 1 * 2 < 2 ^ 32 := by omega
    rcases lowerToMetal_evalMSLKernel_sound env st [10, 11, 12] "nv_metal" k 2 1 2 inBufs
        hwf hlen hpack hcov h32 with
      ⟨elems, kern, devBufsF, outMemF, hlow, hloop, helen, hmsl, hout, hwords⟩
    have hmod : lowerToMetal "nv_metal" k = { kernels := [kern], structs := [], funcs := [] } := by
      have hk : lowerKind "nv_metal" k = kern := List.singleton_inj.mp hlow
      simp [lowerToMetal, hk]
    have hloopEq : evalParKernelLoop env st [10, 11, 12] 2 k (List.range 2) =
        .ok [4294967302, 8589934592] := rfl
    have heqElems : elems = [4294967302, 8589934592] := by
      cases hloop.symm.trans hloopEq
      rfl
    subst heqElems
    exact ⟨k, env, st, inBufs, devBufsF, [4294967302, 8589934592], kern, outMemF,
      hwf, hpack, hmod, hloop, rfl, hmsl, hout, hwords 0 (by omega), hwords 1 (by omega)⟩

/-- `M9` kill (`Metal.lean` line 174): stripping the zero-divisor guard
`((rs == 0UL) ? 0UL : (ls / rs))` -> `(ls / rs)` causes `evalMSLKernel` to trap with
`.divisionByZero` on `(7, 0)`, whereas `lowerKind` succeeds and writes `0#64`. -/
theorem metal_mutant_m9_killed :
    let body := ScalarExpr.binOp .div (.var 1) (.var 2)
    let k := ParallelKernelKind.customScalar 0 [1, 2] body
    let inBufs := [(0, ByteMemory.ofU64Words [7#64]), (1, ByteMemory.ofU64Words [0#64])]
    let devBufs := mkDeviceBuffers inBufs 2 1
    let constBufs := mkConstLenBuffers 2 1
    let grid : Dim3 := { x := 1, y := 1, z := 1 }
    let grp : Dim3 := { x := 1, y := 1, z := 1 }
    evalMSLKernel 9 (metalMutantM9Kernel "m9" 0 [1, 2] body) grid grp devBufs constBufs [] [] =
      .divisionByZero ∧
    evalMSLKernel 9 (lowerKind "m9" k) grid grp devBufs constBufs [] [] ≠
      evalMSLKernel 9 (metalMutantM9Kernel "m9" 0 [1, 2] body) grid grp devBufs constBufs [] [] := by
  intro body k inBufs devBufs constBufs grid grp
  let env : VarEnv := ((VarEnv.empty.bind 10 (.sarrayId 1)).bind 11 (.sarrayId 2))
  let st : HeapState :=
    { buffers :=
        [ { id := 1, exclusive := true, data := #[7] }
        , { id := 2, exclusive := true, data := #[0] } ]
      nextId := 3 }
  cases hpack : packInputDeviceBuffers env st [10, 11] 1 with
  | none =>
    exfalso
    revert hpack
    simp [packInputDeviceBuffers, packInputDeviceBuffersGo, packOneDeviceBuffer, env, st,
      VarEnv.bind, HeapState.findBuffer]
  | some inBufs' =>
  have hinEq : inBufs' = inBufs := by
    revert hpack
    simp [packInputDeviceBuffers, packInputDeviceBuffersGo, packOneDeviceBuffer, indexDeviceBuffers,
      env, st, inBufs, VarEnv.bind, HeapState.findBuffer]
    exact Eq.symm
  subst hinEq
  have hwf9 : wfMetalKernel k = true := rfl
  have hlen9 : ([10, 11] : List VarId).length = kernelArity k := rfl
  rcases lowerToMetal_evalMSLKernel_sound env st [10, 11] "m9" k 1 1 1 inBufs
      hwf9 hlen9 hpack (by omega) (by omega) with
    ⟨_, kern, devBufsF, _, hlow, _, _, hmsl, _, _⟩
  have hk : kern = lowerKind "m9" k := (List.singleton_inj.mp hlow).symm
  subst hk
  have hfg9 : groupStepsForKind 1 k = 9 := rfl
  have hka9 : kernelArity k = 2 := rfl
  rw [hfg9, hka9] at hmsl
  have htrap : evalMSLKernel 9 (metalMutantM9Kernel "m9" 0 [1, 2] body) grid grp devBufs constBufs [] [] =
      .divisionByZero := by
    let g0 := initGroupState (metalMutantM9Kernel "m9" 0 [1, 2] body) grid grp
      { x := 0, y := 0, z := 0 } devBufs constBufs [] [] 9
    have hbind0 : g0.bindings = stdBindings 2 :=
      buildKernelBindings_std (metalMutantM9Kernel "m9" 0 [1, 2] body) 2 rfl rfl
    let inner : List MSLStmt :=
      [ .varDecl .ulong "gid64" (.cast .ulong (.var "gid"))
      , .varDecl .ulong "v1" (.index "in0" (.var "gid"))
      , .varDecl .ulong "v2" (.index "in1" (.var "gid"))
      , .indexAssign "out" (.var "gid") (.div (.var "v1") (.var "v2")) ]
    let ls0 := initBuiltinLocal MSLLocals.empty "gid" .uint (0, 0, 0)
    let tid0 : Dim3 := { x := 0, y := 0, z := 0 }
    let th0 : MSLThreadState :=
      { tid := tid0, locals := ls0
        stmts := [.ifElse (.lt (.cast .ulong (.var "gid")) (.var "n")) (MSLBlock.ofList inner) .nil, .returnStmt]
        halted := false }
    have hth0 : g0.threads = [] ++ [th0] := by
      dsimp only [g0, initGroupState]
      rw [dim3_coords_1d 1]
      simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil]
      rw [initThreadLocals_std (metalMutantM9Kernel "m9" 0 [1, 2] body) _ _ 2 rfl]
      rfl
    have ⟨hlkGid0, htyGid0, harr0, hother0⟩ := initBuiltinLocal_gid_props 0 (by omega)
    have ⟨_, hcastGid0⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g0) g0 tid0 ls0 [] 0 (by omega) hlkGid0 htyGid0
    have hnNone := hother0 "n" (by decide)
    have hbindN : g0.bindings.lookup "n" = some (.constantScalar 3 .ulong) := by
      rw [hbind0]; exact stdBindings_lookup_n 2
    have hconstN : g0.constantBuffers.lookup 3 = some (ByteMemory.ofU64Words [1#64]) := by
      dsimp only [g0, initGroupState, constBufs, mkConstLenBuffers]
      simp [List.lookup]
    have ⟨hevN, htyN⟩ := ev_var_const_ulong kernelCallEval (effectiveCalleeFuel g0) g0 tid0 ls0 []
      "n" 3 1#64 hnNone.1 hnNone.2 hbindN hconstN
    have hevLt := ev_lt_ulong kernelCallEval (effectiveCalleeFuel g0) g0 tid0 ls0 []
      (.cast .ulong (.var "gid")) (.var "n") 0#64 1#64 hcastGid0 hevN rfl htyN
    have hexecIf := exec_ifElse_step g0 th0 [.returnStmt]
      (.lt (.cast .ulong (.var "gid")) (.var "n")) (MSLBlock.ofList inner) .nil 1#64 [] hevLt
    let th1 : MSLThreadState := { tid := tid0, locals := ls0, stmts := inner ++ [.returnStmt], halted := false }
    let g1 : MSLGroupState := { g0 with threads := [th1] }
    have hstep0 : runGroupWithDeviceLog 9 g0 [] = runGroupWithDeviceLog 8 g1 [] :=
      runGroupWithDeviceLog_step_stmt 8 g0 g0 [] [] th0 th1 _ [.returnStmt]
        hth0 (fun _ h => nomatch h) rfl rfl rfl rfl hexecIf id
    have ⟨_, hcastGid1⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g1) g1 tid0 ls0 [] 0 (by omega) hlkGid0 htyGid0
    have hexecG64 := exec_varDecl_ulong g1 th1
      [.varDecl .ulong "v1" (.index "in0" (.var "gid")),
       .varDecl .ulong "v2" (.index "in1" (.var "gid")),
       .indexAssign "out" (.var "gid") (.div (.var "v1") (.var "v2")), .returnStmt]
      "gid64" (.cast .ulong (.var "gid")) 0#64 []
      (fun _ h => nomatch h) hcastGid1
    let ls1 := ls0.setTyped "gid64" .ulong 0#64
    let th2 : MSLThreadState :=
      { tid := tid0, locals := ls1
        stmts := [.varDecl .ulong "v1" (.index "in0" (.var "gid")),
                  .varDecl .ulong "v2" (.index "in1" (.var "gid")),
                  .indexAssign "out" (.var "gid") (.div (.var "v1") (.var "v2")), .returnStmt]
        halted := false }
    let g2 : MSLGroupState := { g1 with threads := [th2] }
    have hstep1 : runGroupWithDeviceLog 8 g1 [] = runGroupWithDeviceLog 7 g2 [] :=
      runGroupWithDeviceLog_step_stmt 7 g1 g1 [] [] th1 th2 _ _
        rfl (fun _ h => nomatch h) rfl rfl rfl rfl hexecG64 id
    have hgid1 := setTyped_lookup_ne ls0 "gid64" "gid" .ulong 0#64 (by decide)
    have ⟨hvarGid2, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g2) g2 tid0 ls1 [] 0 (by omega)
      (hgid1.1.trans hlkGid0) (hgid1.2.trans htyGid0)
    have hbindIn0 : g2.bindings.lookup "in0" = some (.deviceBuf 0 true .ulong) := by
      dsimp [g2, g1]; rw [hbind0]; exact stdBindings_lookup_in 2 0 (by omega)
    have hdevIn0 : g2.deviceBuffers.lookup 0 = some (ByteMemory.ofU64Words [7#64]) := by
      dsimp only [g2, g1, g0, initGroupState, devBufs, mkDeviceBuffers, inBufs]
      simp
    have harr1 : ls1.lookupArray? "in0" = none := by
      dsimp only [ls1, MSLLocals.setTyped, MSLLocals.lookupArray?]
      rw [harr0]
      rfl
    obtain ⟨logA, hread0, hlogA, hneA⟩ := ev_index_dev_read kernelCallEval (effectiveCalleeFuel g2) g2 tid0 ls1 []
      "in0" (.var "gid") 0 2 0 0 0 [7#64] hvarGid2 (by simp) (by simp)
      harr1 hbindIn0 hdevIn0 (by omega) (fun _ h => nomatch h)
    have hexecV1 := exec_varDecl_ulong g2 th2
      [.varDecl .ulong "v2" (.index "in1" (.var "gid")),
       .indexAssign "out" (.var "gid") (.div (.var "v1") (.var "v2")), .returnStmt]
      "v1" (.index "in0" (.var "gid")) 7#64 logA
      (fun _ h => nomatch h) hread0
    let ls2 := ls1.setTyped "v1" .ulong 7#64
    let th3 : MSLThreadState :=
      { tid := tid0, locals := ls2
        stmts := [.varDecl .ulong "v2" (.index "in1" (.var "gid")),
                  .indexAssign "out" (.var "gid") (.div (.var "v1") (.var "v2")), .returnStmt]
        halted := false }
    let g3 : MSLGroupState := { g2 with epochLog := logA, threads := [th3] }
    have hstep2 : runGroupWithDeviceLog 7 g2 [] = runGroupWithDeviceLog 6 g3 [] :=
      runGroupWithDeviceLog_step_stmt 6 g2 { g2 with epochLog := logA } [] [] th2 th3 _ _
        rfl (fun _ h => nomatch h) rfl rfl rfl rfl hexecV1 (by intro h; simp [hneA] at h)
    have hgid2 := setTyped_lookup_ne ls1 "v1" "gid" .ulong 7#64 (by decide)
    have ⟨hvarGid3, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g3) g3 tid0 ls2 logA 0 (by omega)
      (hgid2.1.trans (hgid1.1.trans hlkGid0)) (hgid2.2.trans (hgid1.2.trans htyGid0))
    have hbindIn1 : g3.bindings.lookup "in1" = some (.deviceBuf 1 true .ulong) := by
      dsimp [g3, g2, g1]; rw [hbind0]; exact stdBindings_lookup_in 2 1 (by omega)
    have hdevIn1 : g3.deviceBuffers.lookup 1 = some (ByteMemory.ofU64Words [0#64]) := by
      dsimp only [g3, g2, g1, g0, initGroupState, devBufs, mkDeviceBuffers, inBufs, List.append]
      simp [List.lookup]
    have harr2 : ls2.lookupArray? "in1" = none := by
      dsimp only [ls2, ls1, MSLLocals.setTyped, MSLLocals.lookupArray?]
      rw [harr0]
      rfl
    obtain ⟨logB, hread1, _, hneB⟩ := ev_index_dev_read kernelCallEval (effectiveCalleeFuel g3) g3 tid0 ls2 logA
      "in1" (.var "gid") 1 2 0 0 0 [0#64] hvarGid3 (by simp) (by simp)
      harr2 hbindIn1 hdevIn1 (by omega) hlogA
    have hexecV2 := exec_varDecl_ulong g3 th3
      [.indexAssign "out" (.var "gid") (.div (.var "v1") (.var "v2")), .returnStmt]
      "v2" (.index "in1" (.var "gid")) 0#64 logB
      (fun _ h => nomatch h) hread1
    let ls3 := ls2.setTyped "v2" .ulong 0#64
    let th4 : MSLThreadState :=
      { tid := tid0, locals := ls3
        stmts := [.indexAssign "out" (.var "gid") (.div (.var "v1") (.var "v2")), .returnStmt]
        halted := false }
    let g4 : MSLGroupState := { g3 with epochLog := logB, threads := [th4] }
    have hstep3 : runGroupWithDeviceLog 6 g3 [] = runGroupWithDeviceLog 5 g4 [] :=
      runGroupWithDeviceLog_step_stmt 5 g3 { g3 with epochLog := logB } [] [] th3 th4 _ _
        rfl (fun _ h => nomatch h) rfl rfl rfl rfl hexecV2 (by intro h; simp [hneB] at h)
    have hgid3 := setTyped_lookup_ne ls2 "v2" "gid" .ulong 0#64 (by decide)
    have ⟨hvarGid4, _⟩ := ev_var_gid_uint kernelCallEval (effectiveCalleeFuel g4) g4 tid0 ls3 logB 0 (by omega)
      (hgid3.1.trans (hgid2.1.trans (hgid1.1.trans hlkGid0)))
      (hgid3.2.trans (hgid2.2.trans (hgid1.2.trans htyGid0)))
    have hv1Ne := setTyped_lookup_ne ls2 "v2" "v1" .ulong 0#64 (by decide)
    have hv1Same := setTyped_lookup_same ls1 "v1" .ulong 7#64
    have hv2Same := setTyped_lookup_same ls2 "v2" .ulong 0#64
    have hevV1 := ev_var_bound kernelCallEval (effectiveCalleeFuel g4) g4 tid0 ls3 logB "v1" 7#64
      (hv1Ne.1.trans hv1Same.1) (hv1Ne.2.trans hv1Same.2)
    have hevV2 := ev_var_bound kernelCallEval (effectiveCalleeFuel g4) g4 tid0 ls3 logB "v2" 0#64
      hv2Same.1 hv2Same.2
    have hdivTrap : evalExprWithCall kernelCallEval (effectiveCalleeFuel g4) g4 tid0 ls3 logB
        (.div (.var "v1") (.var "v2")) = .divisionByZero := by
      rw [evalExprWithCall, hevV1]
      dsimp only [bindEval]
      rw [hevV2]
      dsimp only
      have htv1 : inferExprType g4 ls3 (.var "v1") = .ulong := by
        simp only [inferExprType]; rw [hv1Ne.2.trans hv1Same.2]
      have htv2 : inferExprType g4 ls3 (.var "v2") = .ulong := by
        simp only [inferExprType]; rw [hv2Same.2]
      rw [finishBin_ulong_op g4 (.var "v1") (.var "v2") .div ls3 logB 7#64 0#64 [] [] htv1 htv2, evalTypedBin_ulong]
      rfl
    have hstmtTrap : execNonBarrierStmt g4 th4 (.indexAssign "out" (.var "gid") (.div (.var "v1") (.var "v2")))
        [.returnStmt] = .divisionByZero := by
      unfold execNonBarrierStmt
      dsimp only [execStmtWithCall, th4]
      rw [hvarGid4]
      dsimp only
      rw [hdivTrap]
      rfl
    have hstepTrap : stepGroup g4 = .divisionByZero := by
      unfold stepGroup
      have hallF : g4.threads.all (·.halted) = false := by
        dsimp only [g4, th4]; rfl
      rw [hallF]
      simp only [Bool.false_eq_true, ite_false]
      have hfirstTrap : stepFirstReadyThread g4 [] g4.threads = .divisionByZero := by
        have hg4th : g4.threads = [th4] := rfl
        have hth4h : th4.halted = false := rfl
        have hth4b : threadAtBarrier th4 = false := rfl
        have hth4s : threadAtSimdOp th4 = false := rfl
        have hth4st : th4.stmts = .indexAssign "out" (.var "gid") (.div (.var "v1") (.var "v2")) :: [.returnStmt] := rfl
        rw [hg4th]
        simp only [stepFirstReadyThread, hth4h, hth4b, hth4s, Bool.or_false,
          Bool.false_eq_true, ite_false, hth4st, hstmtTrap, propagateErr]
      rw [hfirstTrap]
      rfl
    have hrunTrap : runGroupWithDeviceLog 5 g4 [] = .divisionByZero := by
      unfold runGroupWithDeviceLog
      rw [hstepTrap]
      rfl
    unfold evalMSLKernel
    rw [dim3_coords_1d 1]
    simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, evalMSLKernelLoop]
    rw [show initGroupState (metalMutantM9Kernel "m9" 0 [1, 2] body) grid grp
      { x := 0, y := 0, z := 0 } devBufs constBufs [] [] 9 = g0 from rfl]
    rw [hstep0, hstep1, hstep2, hstep3, hrunTrap]
    rfl
  refine ⟨htrap, ?_⟩
  rw [hmsl, htrap]
  intro h
  nomatch h

/-- `M10` kill (`Metal.lean` line 182): narrowing the 64-bit shift mask
`({ls} << ({rs} & 63UL))` -> `({ls} << ({rs} & 31UL))` changes `evalMSLKernel` output on
`(1, 32)` from `1 <<< 32` (`4294967296#64`) to `1 <<< 0` (`1#64`). -/
theorem metal_mutant_m10_killed :
    let body := ScalarExpr.binOp .shl (.var 1) (.var 2)
    let k := ParallelKernelKind.customScalar 0 [1, 2] body
    let inBufs := [(0, ByteMemory.ofU64Words [1#64]), (1, ByteMemory.ofU64Words [32#64])]
    let devBufs := mkDeviceBuffers inBufs 2 1
    let constBufs := mkConstLenBuffers 2 1
    let grid : Dim3 := { x := 1, y := 1, z := 1 }
    let grp : Dim3 := { x := 1, y := 1, z := 1 }
    (∃ bufsS outS,
      evalMSLKernel 9 (lowerKind "m10" k) grid grp devBufs constBufs [] [] = .ok bufsS ∧
      bufsS.lookup 2 = some outS ∧
      outS.readU64Word? 0 = some 4294967296#64) ∧
    (∃ bufsM outM,
      evalMSLKernel 9 (metalMutantM10Kernel "m10" 0 [1, 2] body) grid grp devBufs constBufs [] [] = .ok bufsM ∧
      bufsM.lookup 2 = some outM ∧
      outM.readU64Word? 0 = some 1#64) ∧
    evalMSLKernel 9 (lowerKind "m10" k) grid grp devBufs constBufs [] [] ≠
      evalMSLKernel 9 (metalMutantM10Kernel "m10" 0 [1, 2] body) grid grp devBufs constBufs [] [] := by
  intro body k inBufs devBufs constBufs grid grp
  let env : VarEnv := ((VarEnv.empty.bind 10 (.sarrayId 1)).bind 11 (.sarrayId 2))
  let st : HeapState :=
    { buffers :=
        [ { id := 1, exclusive := true, data := #[1] }
        , { id := 2, exclusive := true, data := #[32] } ]
      nextId := 3 }
  cases hpack : packInputDeviceBuffers env st [10, 11] 1 with
  | none =>
    exfalso
    revert hpack
    simp [packInputDeviceBuffers, packInputDeviceBuffersGo, packOneDeviceBuffer, env, st,
      VarEnv.bind, HeapState.findBuffer]
  | some inBufs' =>
  have hinEq : inBufs' = inBufs := by
    revert hpack
    simp [packInputDeviceBuffers, packInputDeviceBuffersGo, packOneDeviceBuffer, indexDeviceBuffers,
      env, st, inBufs, VarEnv.bind, HeapState.findBuffer]
    exact Eq.symm
  subst hinEq
  have hwf10 : wfMetalKernel k = true := rfl
  have hlen10 : ([10, 11] : List VarId).length = kernelArity k := rfl
  rcases lowerToMetal_evalMSLKernel_sound env st [10, 11] "m10" k 1 1 1 inBufs
      hwf10 hlen10 hpack (by omega) (by omega) with
    ⟨elems, kern, bufsS, outS, hlow, hloop, helen, hs, hlS, hwordsS⟩
  have hk : kern = lowerKind "m10" k := (List.singleton_inj.mp hlow).symm
  subst hk
  have hfg10 : groupStepsForKind 1 k = 9 := rfl
  have hka10 : kernelArity k = 2 := rfl
  rw [hfg10, hka10] at hs
  rw [hka10] at hlS
  have hloopEq : evalParKernelLoop env st [10, 11] 1 k (List.range 1) = .ok [4294967296] := rfl
  have heqElems : elems = [4294967296] := by
    cases hloop.symm.trans hloopEq
    rfl
  subst heqElems
  have hwS : outS.readU64Word? 0 = some 4294967296#64 := hwordsS 0 (by simp)
  let inWords : Nat → List (BitVec 64) := fun j => if j = 0 then [1#64] else [32#64]
  have hinLookup : ∀ j < 2, inBufs.lookup j = some (ByteMemory.ofU64Words (inWords j)) ∧
      (inWords j).length = 1 := by
    intro j hj
    match j with
    | 0 => refine ⟨by dsimp only [inBufs, inWords]; simp [List.lookup], rfl⟩
    | 1 => refine ⟨by dsimp only [inBufs, inWords]; simp [List.lookup], rfl⟩
    | n + 2 => omega
  have hinOutNone : inBufs.lookup 2 = none := by
    dsimp only [inBufs]; simp [List.lookup]
  have hInnerM : LaneInnerSpec 2 1 4 inWords (fun _ => 1#64)
      ([MSLStmt.varDecl .ulong "gid64" (.cast .ulong (.var "gid"))] ++
        (List.range 2).map (fun m =>
          MSLStmt.varDecl .ulong s!"v{[1, 2][m]?.getD 0}" (.index s!"in{m}" (.var "gid"))) ++
        [MSLStmt.indexAssign "out" (.var "gid") (.shl (.var "v1") (.bitAnd (.var "v2") (.immU64 31#64)))]) := by
    apply laneInner_varDecls_storeOut [1, 2] 1 inWords (fun _ => 1#64)
      (.shl (.var "v1") (.bitAnd (.var "v2") (.immU64 31#64))) (by decide)
    intro g tid ls cx hcxLen _ _ _ hvars
    have hcEq : cx = 0 := by omega
    subst hcEq
    have ⟨hv1, ht1⟩ := hvars 0 (by decide) (by simp [inWords])
    have ⟨hv2, ht2⟩ := hvars 1 (by decide) (by simp [inWords])
    have hv1' : ls.lookup? "v1" = some 1#64 := hv1
    have ht1' : ls.lookupType? "v1" = some .ulong := ht1
    have hv2' : ls.lookup? "v2" = some 32#64 := hv2
    have ht2' : ls.lookupType? "v2" = some .ulong := ht2
    have hev1 := ev_var_bound kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog "v1" 1#64 hv1' ht1'
    have hev2 := ev_var_bound kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog "v2" 32#64 hv2' ht2'
    have hu31 : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog (.immU64 31#64) =
        .ok { value := 31#64, fields := [], locals := ls, log := g.epochLog } := by
      rw [evalExprWithCall]
    have htv1 : inferExprType g ls (.var "v1") = .ulong := by
      simp only [inferExprType]; rw [ht1']
    have htv2 : inferExprType g ls (.var "v2") = .ulong := by
      simp only [inferExprType]; rw [ht2']
    have hand := ev_bitand_ulong kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog
      (.var "v2") (.immU64 31#64) 32#64 31#64 hev2 hu31 htv2 rfl
    have h32_31 : (32#64 &&& 31#64 : BitVec 64) = 0#64 := rfl
    rw [h32_31] at hand
    exact ev_shl_ulong kernelCallEval (effectiveCalleeFuel g) g tid ls g.epochLog
      (.var "v1") _ 1#64 0#64 hev1 hand htv1 (by decide)
  obtain ⟨bufsM, outM, hm, hlM, hwordsM⟩ :=
    evalMSLKernel_guarded_1d 2 1 1 1 4 9 (metalMutantM10Kernel "m10" 0 [1, 2] body)
      inBufs inWords (fun _ => 1#64) _ rfl rfl rfl hInnerM (by omega) (by omega) (by omega) (by omega)
      hinLookup hinOutNone
  have hwM : outM.readU64Word? 0 = some 1#64 := hwordsM 0 (by omega)
  have hm' : evalMSLKernel 9 (metalMutantM10Kernel "m10" 0 [1, 2] body) grid grp devBufs constBufs [] [] = .ok bufsM := hm
  refine ⟨⟨bufsS, outS, hs, hlS, hwS⟩, ⟨bufsM, outM, hm', hlM, hwM⟩, ?_⟩
  rw [hs, hm']
  intro h
  injection h with hbufEq
  rw [hbufEq] at hlS
  have houtEq : outS = outM := Option.some.inj (hlS.symm.trans hlM)
  rw [houtEq] at hwS
  have hvalEq : (4294967296#64 : BitVec 64) = 1#64 := Option.some.inj (hwS.symm.trans hwM)
  exact absurd hvalEq (by decide)

end LeanNative.Proofs.MetalMutantProofs
