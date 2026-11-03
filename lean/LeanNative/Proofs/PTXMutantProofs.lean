import LeanNative.Backend.PTXLower
import LeanNative.Proofs.PTXLowerProofs

/-!
# PTX Lowering Non-Vacuity & Mutant-Kill Proofs (`LeanNative.Proofs.PTXMutantProofs`)

Proves:
1. `lowerToPTX_nonvacuous`: concrete 2-element `customScalar` witness executing end-to-end
   through `lowerToPTX_evalPTXKernel_sound` with zero divisor and subtraction lanes.
2. `ptx_mutant_m7_killed`: formal separation killing B-3 mutant `M7` (`sub.u64` operand swap).
3. `ptx_mutant_m8_killed`: formal separation killing B-3 mutant `M8` (`setp.lt.u64` -> `setp.le.u64`).
-/

namespace LeanNative.Proofs.PTXMutantProofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend
open LeanNative.Backend.PTXAst
open LeanNative.Proofs.PTXSIMT
open LeanNative.Backend.PTXLower
open LeanNative.Proofs.PTXScalarProofs
open LeanNative.Proofs.PTXLowerProofs

private theorem midBody_loads_pureExec
    (nP nR nRd nIn len di : Nat) (doneLbl : String) (el : List PTXStmt)
    (inWords : Nat → List (BitVec 64)) (hlen : ∀ j < nIn, (inWords j).length = len)
    (outFn : Nat → BitVec 64)
    (hp : 0 < nP) (_hr : 2 < nR) (hInRd : 7 + nIn ≤ nRd)
    (houn : (nIn + 1) * len * 8 ≤ 2 ^ 64)
    (hexEl : ∀ (gid : Nat) (_ : gid < len) (rf : PTXRegFile),
      RegTyped rf nP nR nRd →
      (∀ k < nIn, rf.regs.lookup s!"%rd{7 + k}" = some (.scalar ((inWords k)[gid]?.getD 0#64))) →
      ∃ rf' : PTXRegFile,
        RegFramePres 7 rf rf' ∧
        rf'.regs.lookup s!"%rd{di}" = some (.scalar (outFn gid)) ∧
        PureExec el nP nR nRd rf rf') :
    MidBodySpec nP nR nRd nIn len di (4 * nIn + el.length) doneLbl
      (loadsUpTo nIn ++ el) inWords hlen outFn := by
  intro blockSize ctaId tx cta done todo saved allowedLanes gid
    _ _ hpm _ _ _ hgidLt hdone hloadAll hlog
  let epilogue : List PTXStmt :=
    [.instr none (.stGlobal .u64 (.regOffset "%rd6" 0) (.reg s!"%rd{di}")),
     .label doneLbl, .instr none .ret]
  let stmts := stdGidSetup doneLbl ++ (loadsUpTo nIn ++ el) ++ epilogue
  have hrt0 : RegTyped (PTXRegFile.ofRegDecls (stdKernelRegs nP nR nRd)) nP nR nRd :=
    initRegs_typed nP nR nRd hp (by omega) (by omega)
  let rfG := (gidLane blockSize ctaId (PTXRegFile.ofRegDecls (stdKernelRegs nP nR nRd))
    0 tx gid nIn len).regs
  have hrtG : RegTyped rfG nP nR nRd := gidLane_typed blockSize ctaId hrt0 0 tx gid nIn len
  have hlk5 : rfG.regs.lookup "%rd5" = some (.scalar (BitVec.ofNat 64 (gid * 8))) :=
    gidLane_lookup_off blockSize ctaId _ 0 tx gid nIn len
  have hlk6 : rfG.regs.lookup "%rd6" =
      some (.scalar (BitVec.ofNat 64 (nIn * len * 8 + gid * 8))) :=
    gidLane_lookup_out blockSize ctaId _ 0 tx gid nIn len
  let wordAt : Nat → BitVec 64 := fun k => (inWords k)[gid]?.getD 0#64
  have hloadW : ∀ k < nIn, cta.globalMem.loadBits (k * len * 8 + gid * 8) 8 = some (wordAt k) := by
    intro k hk
    have hc : gid < (inWords k).length := by rw [hlen k hk]; exact hgidLt
    simpa [wordAt, List.getElem?_eq_getElem hc] using hloadAll k hk gid hgidLt
  obtain ⟨logM, ⟨hlogM⟩, hrunLoads⟩ := run_loadsUpTo nIn len gid tx wordAt cta done todo
    saved allowedLanes (laneOf1D blockSize ctaId) hpm hgidLt hdone hloadW houn
    nIn (stdGidSetup doneLbl) (el ++ epilogue) rfG nP nR nRd (Nat.le_refl _) hrtG
    hInRd hlk5 hlog
  let rfL := rfLoads wordAt nIn rfG
  have hrtL : RegTyped rfL nP nR nRd := rfLoads_regTyped wordAt hrtG nIn
  obtain ⟨rfFinal, hframe, hlkDi, hpure⟩ :=
    hexEl gid hgidLt rfL hrtL (fun k hk => rfLoads_lookup_input wordAt rfG nIn k hk)
  have hrtFinal : RegTyped rfFinal nP nR nRd := regFrame_regTyped hframe hrtL
  have hlk6Final : rfFinal.regs.lookup "%rd6" =
      some (.scalar (BitVec.ofNat 64 (nIn * len * 8 + gid * 8))) := by
    have hr6 : s!"%rd{6}" = "%rd6" := rfl
    rw [← hr6]
    exact (hframe.rd_eq 6 (by omega)).trans
      ((rfLoads_lookup_lt7 wordAt rfG (by omega) nIn).trans (by rw [hr6]; exact hlk6))
  refine ⟨4 * nIn + el.length, Nat.le_refl _, rfFinal, logM,
    hrtFinal, hlk6Final, hlkDi, hlogM, fun f => ?_⟩
  rw [gidLane_eq_laneAt blockSize ctaId _ 0 tx gid nIn len rfl]
  have hfSplit : f + (4 * nIn + el.length) = (f + el.length) + 4 * nIn := by omega
  have hstLoads : stdGidSetup doneLbl ++ loadsUpTo nIn ++ (el ++ epilogue) = stmts := by
    simp [stmts, List.append_assoc]
  have hpreLen : (stdGidSetup doneLbl).length = 13 := rfl
  have hrunL := hrunLoads (f + el.length)
  rw [hstLoads, hpreLen] at hrunL
  have hslice : SliceAt stmts el (13 + 4 * nIn) := by
    have hstMid : stmts = (stdGidSetup doneLbl ++ loadsUpTo nIn) ++ el ++ epilogue := by
      simp [stmts, List.append_assoc]
    have hlenMid : (stdGidSetup doneLbl ++ loadsUpTo nIn).length = 13 + 4 * nIn := by
      rw [List.length_append, loadsUpTo_length]; rfl
    rw [hstMid, ← hlenMid]
    exact sliceAt_mid_split _ _ _
  have hrunEl := hpure hrtL f stmts { cta with epochLog := logM } done todo 0 tx
    (13 + 4 * nIn) saved hdone hslice
  have hpcEnd : (13 + 4 * nIn) + el.length = 13 + (loadsUpTo nIn ++ el).length := by
    rw [List.length_append, loadsUpTo_length]; omega
  rw [hpcEnd] at hrunEl
  change runCTAWithGlobalLog (f + (4 * nIn + el.length)) stmts _ saved =
    runCTAWithGlobalLog f stmts _ saved
  rw [hfSplit, hrunL]
  exact hrunEl

/-- Non-vacuity witness for `lowerToPTX_evalPTXKernel_sound`: a concrete 2-element
`customScalar` kernel `(x[gid] - y[gid]) + (y[gid] / z[gid])` with a zero divisor in lane 1
lowers to `PTXAst`, satisfies all preconditions of `lowerToPTX_evalPTXKernel_sound`,
and executes in `evalPTXKernel` to produce `[10 - 3 + 3 / 3, 20 - 5 + 5 / 0]` (`[8, 15]`). -/
theorem lowerToPTX_nonvacuous :
    ∃ (k : ParallelKernelKind) (env : VarEnv) (st : HeapState)
      (inWords : List (List (BitVec 64)))
      (elems : List UInt64) (kern : PTXKernel) (gFinal : ByteMemory),
      wfPTXKernel k = true ∧
      packInputWordLists env st 2 [10, 11, 12] = some inWords ∧
      lowerToPTX "nv_ptx" k = { kernels := [kern] } ∧
      evalParKernelLoop env st [10, 11, 12] 2 k (List.range 2) = .ok elems ∧
      elems = [8, 15] ∧
      evalPTXKernel (ctaStepsForKind 2 k) kern
        { x := 1, y := 1, z := 1 } { x := 2, y := 1, z := 1 }
        (mkPTXGlobalMem inWords (kernelArity k) 2)
        (mkPTXParamMem (kernelArity k) 2) = .ok gFinal ∧
      gFinal.loadBits (kernelArity k * 2 * 8 + 0 * 8) 8 = some 8#64 ∧
      gFinal.loadBits (kernelArity k * 2 * 8 + 1 * 8) 8 = some 15#64 := by
  let k : ParallelKernelKind :=
    .customScalar 0 [1, 2, 3]
      (.binOp .add
        (.binOp .sub (.var 1) (.var 2))
        (.binOp .div (.var 2) (.var 3)))
  let env : VarEnv :=
    (((VarEnv.empty.bind 10 (.sarrayId 1)).bind 11 (.sarrayId 2)).bind 12 (.sarrayId 3))
  let st : HeapState :=
    { buffers :=
        [ { id := 1, exclusive := true, data := #[10, 20] }
        , { id := 2, exclusive := true, data := #[3, 5] }
        , { id := 3, exclusive := true, data := #[3, 0] } ]
      nextId := 4 }
  have hwf : wfPTXKernel k = true := rfl
  cases hpack : packInputWordLists env st 2 [10, 11, 12] with
  | none =>
    exfalso
    revert hpack
    simp [packInputWordLists, env, st, VarEnv.bind, HeapState.findBuffer]
  | some inWords =>
    have harity : ([10, 11, 12] : List VarId).length = kernelArity k := rfl
    rcases lowerToPTX_evalPTXKernel_sound env st [10, 11, 12] "nv_ptx" k 2 1 2 inWords
        hwf harity hpack (by omega) (by omega) (by omega) (by decide) with
      ⟨elems, kern, gFinal, hlow, hloop, _, hptx, hwords⟩
    have hmod : lowerToPTX "nv_ptx" k = { kernels := [kern] } := by
      have hk : lowerKind "nv_ptx" k = kern := List.singleton_inj.mp hlow
      simp [lowerToPTX, hk]
    have hloopEq : evalParKernelLoop env st [10, 11, 12] 2 k (List.range 2) = .ok [8, 15] := rfl
    have heqElems : elems = [8, 15] := by
      cases hloop.symm.trans hloopEq
      rfl
    subst heqElems
    exact ⟨k, env, st, inWords, [8, 15], kern, gFinal,
      hwf, hpack, hmod, hloop, rfl, hptx, hwords 0 (by omega), hwords 1 (by omega)⟩

/-- `M7` kill (`MLIRGPU.lean` line 358): swapping `.sub` operands
`sub.u64 dst, lReg, rReg;` -> `sub.u64 dst, rReg, lReg;` changes `evalPTXKernel` output
on `(1, 2)` from `1 - 2` (`0xFFFF_FFFF_FFFF_FFFF#64`) to `2 - 1` (`1#64`). -/
theorem ptx_mutant_m7_killed :
    let body := ScalarExpr.binOp .sub (.var 1) (.var 2)
    let k := ParallelKernelKind.customScalar 0 [1, 2] body
    let inWords : List (List (BitVec 64)) := [[1#64], [2#64]]
    let gMem := mkPTXGlobalMem inWords 2 1
    let pMem := mkPTXParamMem 2 1
    let grid : Dim3 := { x := 1, y := 1, z := 1 }
    let blk : Dim3 := { x := 1, y := 1, z := 1 }
    (∃ gS,
      evalPTXKernel 26 (lowerKind "m7" k) grid blk gMem pMem = .ok gS ∧
      gS.loadBits 16 8 = some 18446744073709551615#64) ∧
    (∃ gM,
      evalPTXKernel 26 (ptxMutantM7Kernel "m7" 0 [1, 2] body) grid blk gMem pMem = .ok gM ∧
      gM.loadBits 16 8 = some 1#64) ∧
    evalPTXKernel 26 (lowerKind "m7" k) grid blk gMem pMem ≠
      evalPTXKernel 26 (ptxMutantM7Kernel "m7" 0 [1, 2] body) grid blk gMem pMem := by
  intro body k inWords gMem pMem grid blk
  let env : VarEnv := ((VarEnv.empty.bind 10 (.sarrayId 1)).bind 11 (.sarrayId 2))
  let st : HeapState :=
    { buffers :=
        [ { id := 1, exclusive := true, data := #[1] }
        , { id := 2, exclusive := true, data := #[2] } ]
      nextId := 3 }
  cases hpack : packInputWordLists env st 1 [10, 11] with
  | none =>
    exfalso
    revert hpack
    simp [packInputWordLists, env, st, VarEnv.bind, HeapState.findBuffer]
  | some inWords' =>
    have hinEq : inWords' = inWords := by
      revert hpack
      simp [packInputWordLists, env, st, inWords, VarEnv.bind, HeapState.findBuffer]
      exact Eq.symm
    subst hinEq
    have hwf7 : wfPTXKernel k = true := rfl
    have harity7 : ([10, 11] : List VarId).length = kernelArity k := rfl
    rcases lowerToPTX_evalPTXKernel_sound env st [10, 11] "m7" k 1 1 1 inWords
        hwf7 harity7 hpack (by omega) (by omega) (by omega) (by decide) with
      ⟨elems, kern, gS, hlow, hloop, _, hs, hwordsS⟩
    have hk : kern = lowerKind "m7" k := (List.singleton_inj.mp hlow).symm
    subst hk
    have hfuel7 : ctaStepsForKind 1 k = 26 := rfl
    have hka7 : kernelArity k = 2 := rfl
    rw [hfuel7, hka7] at hs
    have hloopEq : evalParKernelLoop env st [10, 11] 1 k (List.range 1) =
        .ok [18446744073709551615] := rfl
    have heqElems : elems = [18446744073709551615] := by
      cases hloop.symm.trans hloopEq
      rfl
    subst heqElems
    have hwS : gS.loadBits 16 8 = some 18446744073709551615#64 := by
      simpa [hka7] using hwordsS 0 (by simp)
    let wordAt : Nat → List (BitVec 64) := fun j => inWords[j]?.getD []
    have hwordLen : ∀ j < 2, (wordAt j).length = 1 := by
      intro j hj
      match j with
      | 0 => rfl
      | 1 => rfl
      | n + 2 => omega
    let elM7 : List PTXStmt := [ins (.sub .u64 "%rd9" (.reg "%rd8") (.reg "%rd7"))]
    have hMidM : MidBodySpec 1 3 10 2 1 9 (4 * 2 + elM7.length) "$L_done_m7"
        (loadsUpTo 2 ++ elM7) wordAt hwordLen (fun _ => 1#64) := by
      apply midBody_loads_pureExec 1 3 10 2 1 9 "$L_done_m7" elM7 wordAt hwordLen
        (fun _ => 1#64) (by omega) (by omega) (by omega) (by omega)
      intro gid hgid rf _ hinputs
      have hgid0 : gid = 0 := by omega
      subst hgid0
      have hl7 : rf.regs.lookup "%rd7" = some (.scalar 1#64) := hinputs 0 (by omega)
      have hl8 : rf.regs.lookup "%rd8" = some (.scalar 2#64) := hinputs 1 (by omega)
      refine ⟨rf.setScalarRaw "%rd9" 1#64,
        regFrame_setRd rf (by omega : 7 ≤ 9) 1#64,
        lookup_rd_self rf 9 1#64, ?_⟩
      exact pureExec_single (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
        fun s c t hrf hrtT => by
          have hex := exec_sub_rd s c t hrtT 9 8 7 (by omega) (by omega) (by omega) 2#64 1#64
            (by rw [hrf]; exact hl8) (by rw [hrf]; exact hl7)
          have hsub : (2#64 - 1#64 : BitVec 64) = 1#64 := rfl
          rw [hsub, hrf] at hex
          exact hex
    have hnoLblM : ∀ s ∈ loadsUpTo 2 ++ elM7, s ≠ .label "$L_done_m7" := by
      intro s hs
      rcases List.mem_append.mp hs with h1 | h2
      · exact loadsUpTo_no_label 2 "$L_done_m7" s h1
      · simp only [elM7, List.mem_singleton, ins] at h2; subst h2; simp
    obtain ⟨gM, hm, hwordsM⟩ :=
      evalPTXKernel_guarded_1d 1 3 10 2 1 1 1 9 9 26
        (ptxMutantM7Kernel "m7" 0 [1, 2] body) "$L_done_m7" (loadsUpTo 2 ++ elM7)
        wordAt hwordLen (fun _ => 1#64) rfl rfl rfl
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) hnoLblM hMidM
    have hm' : evalPTXKernel 26 (ptxMutantM7Kernel "m7" 0 [1, 2] body) grid blk gMem pMem = .ok gM := by
      dsimp only [gMem, pMem]
      rw [mkPTXGlobalMem_eq_pack, mkPTXParamMem_eq_std]
      exact hm
    have hwM : gM.loadBits 16 8 = some 1#64 := by simpa using hwordsM 0 (by omega)
    refine ⟨⟨gS, hs, hwS⟩, ⟨gM, hm', hwM⟩, ?_⟩
    rw [hs, hm']
    intro h
    injection h with hgEq
    rw [hgEq] at hwS
    have hvalEq : (18446744073709551615#64 : BitVec 64) = 1#64 := Option.some.inj (hwS.symm.trans hwM)
    exact absurd hvalEq (by decide)

/-- `M8` kill (`MLIRGPU.lean` line 433): weakening `.lt` predicate from
`setp.lt.u64` to `setp.le.u64` changes `evalPTXKernel` output on `(3, 3)`
from `0#64` to `1#64`. -/
theorem ptx_mutant_m8_killed :
    let body := ScalarExpr.binOp .lt (.var 1) (.var 2)
    let k := ParallelKernelKind.customScalar 0 [1, 2] body
    let inWords : List (List (BitVec 64)) := [[3#64], [3#64]]
    let gMem := mkPTXGlobalMem inWords 2 1
    let pMem := mkPTXParamMem 2 1
    let grid : Dim3 := { x := 1, y := 1, z := 1 }
    let blk : Dim3 := { x := 1, y := 1, z := 1 }
    (∃ gS,
      evalPTXKernel 27 (lowerKind "m8" k) grid blk gMem pMem = .ok gS ∧
      gS.loadBits 16 8 = some 0#64) ∧
    (∃ gM,
      evalPTXKernel 27 (ptxMutantM8Kernel "m8" 0 [1, 2] body) grid blk gMem pMem = .ok gM ∧
      gM.loadBits 16 8 = some 1#64) ∧
    evalPTXKernel 27 (lowerKind "m8" k) grid blk gMem pMem ≠
      evalPTXKernel 27 (ptxMutantM8Kernel "m8" 0 [1, 2] body) grid blk gMem pMem := by
  intro body k inWords gMem pMem grid blk
  let env : VarEnv := ((VarEnv.empty.bind 10 (.sarrayId 1)).bind 11 (.sarrayId 2))
  let st : HeapState :=
    { buffers :=
        [ { id := 1, exclusive := true, data := #[3] }
        , { id := 2, exclusive := true, data := #[3] } ]
      nextId := 3 }
  cases hpack : packInputWordLists env st 1 [10, 11] with
  | none =>
    exfalso
    revert hpack
    simp [packInputWordLists, env, st, VarEnv.bind, HeapState.findBuffer]
  | some inWords' =>
    have hinEq : inWords' = inWords := by
      revert hpack
      simp [packInputWordLists, env, st, inWords, VarEnv.bind, HeapState.findBuffer]
      exact Eq.symm
    subst hinEq
    have hwf8 : wfPTXKernel k = true := rfl
    have harity8 : ([10, 11] : List VarId).length = kernelArity k := rfl
    rcases lowerToPTX_evalPTXKernel_sound env st [10, 11] "m8" k 1 1 1 inWords
        hwf8 harity8 hpack (by omega) (by omega) (by omega) (by decide) with
      ⟨elems, kern, gS, hlow, hloop, _, hs, hwordsS⟩
    have hk : kern = lowerKind "m8" k := (List.singleton_inj.mp hlow).symm
    subst hk
    have hfuel8 : ctaStepsForKind 1 k = 27 := rfl
    have hka8 : kernelArity k = 2 := rfl
    rw [hfuel8, hka8] at hs
    have hloopEq : evalParKernelLoop env st [10, 11] 1 k (List.range 1) = .ok [0] := rfl
    have heqElems : elems = [0] := by
      cases hloop.symm.trans hloopEq
      rfl
    subst heqElems
    have hwS : gS.loadBits 16 8 = some 0#64 := by
      simpa [hka8] using hwordsS 0 (by simp)
    let wordAt : Nat → List (BitVec 64) := fun j => inWords[j]?.getD []
    have hwordLen : ∀ j < 2, (wordAt j).length = 1 := by
      intro j hj
      match j with
      | 0 => rfl
      | 1 => rfl
      | n + 2 => omega
    let elM8 : List PTXStmt :=
      [ ins (.setp .le .u64 "%p1" (.reg "%rd7") (.reg "%rd8"))
      , ins (.selp .u64 "%rd9" (i64 1) (i64 0) "%p1") ]
    have hMidM : MidBodySpec 2 3 10 2 1 9 (4 * 2 + elM8.length) "$L_done_m8"
        (loadsUpTo 2 ++ elM8) wordAt hwordLen (fun _ => 1#64) := by
      apply midBody_loads_pureExec 2 3 10 2 1 9 "$L_done_m8" elM8 wordAt hwordLen
        (fun _ => 1#64) (by omega) (by omega) (by omega) (by omega)
      intro gid hgid rf _ hinputs
      have hgid0 : gid = 0 := by omega
      subst hgid0
      have hl7 : rf.regs.lookup s!"%rd{7}" = some (.scalar 3#64) := hinputs 0 (by omega)
      have hl8 : rf.regs.lookup s!"%rd{8}" = some (.scalar 3#64) := hinputs 1 (by omega)
      obtain ⟨rf', hf9, hlk9, hpure⟩ :=
        exec_tail_cmp .le (nP := 2) (nR := 3) (nRd := 10) (di := 9) (li := 7) (ri := 8) (pi := 1)
          (by omega) (by omega) (by omega) (by omega) 3#64 3#64 rf hl7 hl8
      have hcmp : (if evalPTXCmp .le .u64 3#64 3#64 then (1#64 : BitVec 64) else 0#64) = 1#64 := rfl
      rw [hcmp] at hlk9
      exact ⟨rf', regFrame_trans (regFrame_refl 7 rf) hf9 (by omega), hlk9, hpure⟩
    have hnoLblM : ∀ s ∈ loadsUpTo 2 ++ elM8, s ≠ .label "$L_done_m8" := by
      intro s hs
      rcases List.mem_append.mp hs with h1 | h2
      · exact loadsUpTo_no_label 2 "$L_done_m8" s h1
      · simp only [elM8, List.mem_cons, List.mem_nil_iff, or_false, ins] at h2
        rcases h2 with rfl | rfl <;> simp
    obtain ⟨gM, hm, hwordsM⟩ :=
      evalPTXKernel_guarded_1d 2 3 10 2 1 1 1 9 10 27
        (ptxMutantM8Kernel "m8" 0 [1, 2] body) "$L_done_m8" (loadsUpTo 2 ++ elM8)
        wordAt hwordLen (fun _ => 1#64) rfl rfl rfl
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) hnoLblM hMidM
    have hm' : evalPTXKernel 27 (ptxMutantM8Kernel "m8" 0 [1, 2] body) grid blk gMem pMem = .ok gM := by
      dsimp only [gMem, pMem]
      rw [mkPTXGlobalMem_eq_pack, mkPTXParamMem_eq_std]
      exact hm
    have hwM : gM.loadBits 16 8 = some 1#64 := by simpa using hwordsM 0 (by omega)
    refine ⟨⟨gS, hs, hwS⟩, ⟨gM, hm', hwM⟩, ?_⟩
    rw [hs, hm']
    intro h
    injection h with hgEq
    rw [hgEq] at hwS
    have hvalEq : (0#64 : BitVec 64) = 1#64 := Option.some.inj (hwS.symm.trans hwM)
    exact absurd hvalEq (by decide)

end LeanNative.Proofs.PTXMutantProofs
