import LeanNative.Proofs.PTXLowerProofs3

/-!
# End-to-End `LNIR` -> `PTXAst` Lowering Soundness (`LeanNative.Proofs.PTXLowerProofs`)

Proves `lowerToPTX_evalPTXKernel_sound`: for every well-formed `wfPTXKernel k` whose input
array buffers are packed via `packInputWordLists`, `LNIR.evalParKernelLoop` succeeds over
`0 .. len - 1` and `PTXAst.evalPTXKernel` on the lowered kernel in `lowerToPTX name k`
terminates without intra-CTA or cross-CTA data races, writing the exact 64-bit word
`elems[i].toBitVec` at every output element `i < len` (`0 sorryAx`, `0 ofReduceBool`).
-/

namespace LeanNative.Proofs.PTXLowerProofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend
open LeanNative.Backend.PTXAst
open LeanNative.Proofs.PTXSIMT
open LeanNative.Backend.PTXLower
open LeanNative.Proofs.PTXScalarProofs

private theorem packInputWordLists_props (env : VarEnv) (st : HeapState) (len : Nat) :
    ∀ (inputs : List VarId) (ws : List (List (BitVec 64))),
      packInputWordLists env st len inputs = some ws →
      ws.length = inputs.length ∧
      (∀ j < inputs.length, ∃ (words : List (BitVec 64)),
        ws[j]? = some words ∧ words.length = len ∧
        ∀ i (_ : i < len) (hwi : i < words.length),
          ∃ x : UInt64, readParInput env st inputs j i = .ok x ∧ words[i] = x.toBitVec)
  | [], ws, h => by
    simp only [packInputWordLists, Option.some.injEq] at h; subst h
    exact ⟨rfl, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | v :: rest, ws, h => by
    unfold packInputWordLists at h
    cases hv : env v with
    | none => simp [hv] at h
    | some val =>
      cases val <;> simp [hv] at h
      all_goals
        rename_i bid
        cases ht : packInputWordLists env st len rest with
        | none => simp [ht] at h
        | some tail =>
          rw [ht] at h; dsimp only at h
          cases hfind : st.findBuffer bid with
          | none => simp [hfind] at h
          | some buf =>
            rw [hfind] at h; dsimp only at h
            split at h
            · rename_i hlenLe
              simp only [Option.some.injEq] at h; subst h
              rcases packInputWordLists_props env st len rest tail ht with ⟨hlenTail, hmid⟩
              refine ⟨by simp [hlenTail], fun j hj => ?_⟩
              cases j with
              | zero =>
                let words := (List.range len).map fun i => (buf.data[i]?.getD 0).toBitVec
                refine ⟨words, by simp [words], by simp [words], fun i hi _ => ?_⟩
                have hiBuf : i < buf.data.size := Nat.lt_of_lt_of_le hi hlenLe
                refine ⟨buf.data[i], ?_, by simp [words, Array.getElem?_eq_getElem hiBuf]⟩
                unfold readParInput; simp [hv, HeapState.readElem, hfind, hiBuf]
              | succ j' =>
                simp only [List.length_cons] at hj
                rcases hmid j' (by omega) with ⟨words, hlk, hwlen, hread⟩
                refine ⟨words, by simp [hlk], hwlen, fun i hi hwi => ?_⟩
                rcases hread i hi hwi with ⟨x, hr, hw⟩
                refine ⟨x, ?_, hw⟩
                unfold readParInput at hr ⊢; simp only [List.getElem?_cons_succ]
                cases hget : rest[j']? with
                | none => rw [hget] at hr; cases hr
                | some _ => rw [hget] at hr; exact hr
            · cases h

private theorem loadsUpTo_no_doneLbl (name : String) (n : Nat) :
    ∀ s ∈ loadsUpTo n, s ≠ .label s!"$L_done_{name}" :=
  loadsUpTo_no_label n _

private theorem midBody_no_label_append {doneLbl : String} {m1 m2 : List PTXStmt}
    (h1 : ∀ s ∈ m1, s ≠ .label doneLbl) (h2 : ∀ s ∈ m2, s ≠ .label doneLbl) :
    ∀ s ∈ m1 ++ m2, s ≠ .label doneLbl := by
  intro s hs
  rcases List.mem_append.mp hs with hm | hm
  · exact h1 s hm
  · exact h2 s hm

private theorem lowerScalar_no_doneLbl (varOf : Nat → Option PReg) (boundVars : List Nat)
    (e0 : PEnv) (expr : ScalarExpr) (s : Bool)
    (hsort : inferScalarSort boundVars expr = some s)
    (hvar : ∀ id ∈ boundVars, ∃ k < e0.nextRd, varOf id = some (.rd k))
    (doneLbl : String) :
    ∀ st ∈ (lowerScalar varOf e0 expr).1, st ≠ .label doneLbl :=
  (lowerScalar_bounds_no_label varOf boundVars e0 expr s hsort hvar).2.2.2.2 doneLbl

private theorem evalParKernelLoop_of_all (env : VarEnv) (st : HeapState) (inputs : List VarId)
    (len : Nat) (k : ParallelKernelKind) (specU64 : Nat → UInt64) :
    ∀ (idxs : List Nat), (∀ i ∈ idxs, evalParKernelElem env st inputs len k i = .ok (specU64 i)) →
      ∃ elems : List UInt64, evalParKernelLoop env st inputs len k idxs = .ok elems ∧ elems = idxs.map specU64
  | [], _ => ⟨[], rfl, rfl⟩
  | i :: is, hall => by
    obtain ⟨xs, hxs, hmap⟩ :=
      evalParKernelLoop_of_all env st inputs len k specU64 is (fun j hj => hall j (.tail i hj))
    refine ⟨specU64 i :: xs, ?_, by simp [hmap]⟩
    unfold evalParKernelLoop; rw [hall i (.head is), hxs]

/-- End-to-end 1D SIMT lowering soundness (`LNIR.ParallelKernelKind` -> `PTXAst.PTXModule`):
for every well-formed `wfPTXKernel k` whose input array buffers are packed via
`packInputWordLists`, `LNIR.evalParKernelLoop` succeeds over `0 .. len - 1` and
`PTXAst.evalPTXKernel` on the lowered kernel in `lowerToPTX name k` terminates without
intra-CTA or cross-CTA data races, writing the exact 64-bit word `elems[i].toBitVec` at
every output element `i < len`. -/
theorem lowerToPTX_evalPTXKernel_sound
    (env : VarEnv) (st : HeapState) (inputs : List VarId) (name : String) (k : ParallelKernelKind)
    (len nBlocks blockSize : Nat) (inWords : List (List (BitVec 64)))
    (hwf : wfPTXKernel k = true) (harity : inputs.length = kernelArity k)
    (hpack : packInputWordLists env st len inputs = some inWords)
    (hlenCov : len ≤ nBlocks * blockSize)
    (hnBlk32 : nBlocks < 2 ^ 32) (hblk32 : blockSize < 2 ^ 32)
    (houn : (kernelArity k + 1) * len * 8 ≤ 2 ^ 64) :
    ∃ (elems : List UInt64) (kern : PTXKernel) (gFinal : ByteMemory),
      (lowerToPTX name k).kernels = [kern] ∧
      evalParKernelLoop env st inputs len k (List.range len) = .ok elems ∧ elems.length = len ∧
      evalPTXKernel (ctaStepsForKind blockSize k) kern
        { x := nBlocks, y := 1, z := 1 } { x := blockSize, y := 1, z := 1 }
        (mkPTXGlobalMem inWords (kernelArity k) len) (mkPTXParamMem (kernelArity k) len) = .ok gFinal ∧
      (∀ (i : Nat) (hi : i < elems.length),
        gFinal.loadBits (kernelArity k * len * 8 + i * 8) 8 = some (elems[i]'hi).toBitVec) := by
  rcases packInputWordLists_props env st len inputs inWords hpack with ⟨hwsLen, hmid⟩
  let wordAt : Nat → List (BitVec 64) := fun j => inWords[j]?.getD []
  have hwordLen : ∀ j < kernelArity k, (wordAt j).length = len := by
    intro j hj
    rcases hmid j (by omega) with ⟨words, hlk, hwlen, _⟩
    simp only [wordAt, hlk]
    exact hwlen
  have hreadElem : ∀ j < kernelArity k, ∀ i < len,
      ∃ (hc : i < (wordAt j).length) (x : UInt64),
        readParInput env st inputs j i = .ok x ∧ (wordAt j)[i]'hc = x.toBitVec := by
    intro j hj i hi
    rcases hmid j (by omega) with ⟨words, hlk, hwlen, hrd⟩
    rcases hrd i hi (by omega) with ⟨x, hrx, hwx⟩
    have hc : i < (wordAt j).length := by simp [wordAt, hlk, hwlen, hi]
    refine ⟨hc, x, hrx, ?_⟩
    simp [wordAt, hlk, hwx]
  let specU64 : Nat → UInt64 := fun i =>
    match evalParKernelElem env st inputs len k i with
    | .ok v => v
    | .error _ => 0
  have ⟨nP, nR, nRd, vi, maxMid, mid, hp, hr, hr6, hvi, hregs, hbody, hnoLbl, hfuel, hMid, helemAll⟩ :
      ∃ (nP nR nRd vi maxMid : Nat) (mid : List PTXStmt),
        0 < nP ∧ 2 < nR ∧ 6 < nRd ∧ vi < nRd ∧
        (lowerKind name k).regDecls = stdKernelRegs nP nR nRd ∧
        (lowerKind name k).body = stdGidSetup s!"$L_done_{name}" ++ mid ++
          [.instr none (.stGlobal .u64 (.regOffset "%rd6" 0) (.reg s!"%rd{vi}")),
           .label s!"$L_done_{name}", .instr none .ret] ∧
        (∀ s ∈ mid, s ≠ .label s!"$L_done_{name}") ∧
        blockSize * (16 + maxMid) + 1 ≤ ctaStepsForKind blockSize k ∧
        MidBodySpec nP nR nRd (kernelArity k) len vi maxMid s!"$L_done_{name}" mid wordAt hwordLen
          (fun i => (specU64 i).toBitVec) ∧
        (∀ i < len, evalParKernelElem env st inputs len k i = .ok (specU64 i)) := by
    cases k with
    | mapScaleAdd scale bias =>
      refine ⟨1, 3, 9, 8, 5, stdLoadIn 0 "%rd7" ++
          [ins (.mad .lo .u64 "%rd8" (.reg "%rd7") (.immU64 scale.toBitVec) (.immU64 bias.toBitVec))],
        by omega, by omega, by omega, by omega,
        rfl, ?_, ?_, by simp [ctaStepsForKind, maxMidStepsForKind], ?_, ?_⟩
      · simp only [lowerKind, kernelOf, gidSetup_eq_std, loadIn_eq_std, List.append_assoc, ins]
        rfl
      · intro s hs
        simp only [stdLoadIn, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, ins] at hs
        rcases hs with (rfl | rfl | rfl | rfl) | rfl <;> simp
      · refine midBodySpec_congr (midBody_mapScaleAdd len scale bias _ wordAt hwordLen houn) (fun cx hcx => ?_)
        rcases hreadElem 0 (by simp [kernelArity]) cx hcx with ⟨hc0, x, hrx, hwx⟩
        simp [specU64, evalParKernelElem, hrx, dite_eq_left_of_eq_true (eq_true hc0), hwx]
      · intro i hi
        rcases hreadElem 0 (by simp [kernelArity]) i hi with ⟨_, x, hrx, _⟩
        simp [specU64, evalParKernelElem, hrx]
    | zipAdd =>
      refine ⟨1, 3, 10, 9, 9, stdLoadIn 0 "%rd7" ++ stdLoadIn 1 "%rd8" ++
          [ins (.add .none .u64 "%rd9" (.reg "%rd7") (.reg "%rd8"))],
        by omega, by omega, by omega, by omega,
        rfl, ?_, ?_, by simp [ctaStepsForKind, maxMidStepsForKind], ?_, ?_⟩
      · simp only [lowerKind, kernelOf, gidSetup_eq_std, loadIn_eq_std, List.append_assoc, ins]
        rfl
      · intro s hs
        simp only [stdLoadIn, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, ins] at hs
        rcases hs with ((rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)) | rfl <;> simp
      · refine midBodySpec_congr (midBody_zipAdd len _ wordAt hwordLen houn) (fun cx hcx => ?_)
        rcases hreadElem 0 (by simp [kernelArity]) cx hcx with ⟨hc0, x, hrx, hwx⟩
        rcases hreadElem 1 (by simp [kernelArity]) cx hcx with ⟨hc1, y, hry, hwy⟩
        simp [specU64, evalParKernelElem, hrx, hry, dite_eq_left_of_eq_true (eq_true hc0),
          dite_eq_left_of_eq_true (eq_true hc1), hwx, hwy]
      · intro i hi
        rcases hreadElem 0 (by simp [kernelArity]) i hi with ⟨_, x, hrx, _⟩
        rcases hreadElem 1 (by simp [kernelArity]) i hi with ⟨_, y, hry, _⟩
        simp [specU64, evalParKernelElem, hrx, hry]
    | zipMul | dotProduct =>
      refine ⟨1, 3, 10, 9, 9, stdLoadIn 0 "%rd7" ++ stdLoadIn 1 "%rd8" ++
          [ins (.mul .lo .u64 "%rd9" (.reg "%rd7") (.reg "%rd8"))],
        by omega, by omega, by omega, by omega,
        rfl, ?_, ?_, by simp [ctaStepsForKind, maxMidStepsForKind], ?_, ?_⟩
      · simp only [lowerKind, kernelOf, gidSetup_eq_std, loadIn_eq_std, List.append_assoc, ins]
        rfl
      · intro s hs
        simp only [stdLoadIn, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, ins] at hs
        rcases hs with ((rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)) | rfl <;> simp
      · refine midBodySpec_congr (midBody_zipMul len _ wordAt hwordLen houn) (fun cx hcx => ?_)
        rcases hreadElem 0 (by simp [kernelArity]) cx hcx with ⟨hc0, x, hrx, hwx⟩
        rcases hreadElem 1 (by simp [kernelArity]) cx hcx with ⟨hc1, y, hry, hwy⟩
        simp [specU64, evalParKernelElem, hrx, hry, dite_eq_left_of_eq_true (eq_true hc0),
          dite_eq_left_of_eq_true (eq_true hc1), hwx, hwy]
      · intro i hi
        rcases hreadElem 0 (by simp [kernelArity]) i hi with ⟨_, x, hrx, _⟩
        rcases hreadElem 1 (by simp [kernelArity]) i hi with ⟨_, y, hry, _⟩
        simp [specU64, evalParKernelElem, hrx, hry]
    | saxpy alpha =>
      refine ⟨1, 3, 10, 9, 9, stdLoadIn 0 "%rd7" ++ stdLoadIn 1 "%rd8" ++
          [ins (.mad .lo .u64 "%rd9" (.reg "%rd7") (.immU64 alpha.toBitVec) (.reg "%rd8"))],
        by omega, by omega, by omega, by omega,
        rfl, ?_, ?_, by simp [ctaStepsForKind, maxMidStepsForKind], ?_, ?_⟩
      · simp only [lowerKind, kernelOf, gidSetup_eq_std, loadIn_eq_std, List.append_assoc, ins]
        rfl
      · intro s hs
        simp only [stdLoadIn, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, ins] at hs
        rcases hs with ((rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)) | rfl <;> simp
      · refine midBodySpec_congr (midBody_saxpy len alpha _ wordAt hwordLen houn) (fun cx hcx => ?_)
        rcases hreadElem 0 (by simp [kernelArity]) cx hcx with ⟨hc0, x, hrx, hwx⟩
        rcases hreadElem 1 (by simp [kernelArity]) cx hcx with ⟨hc1, y, hry, hwy⟩
        simp [specU64, evalParKernelElem, hrx, hry, dite_eq_left_of_eq_true (eq_true hc0),
          dite_eq_left_of_eq_true (eq_true hc1), hwx, hwy, BitVec.mul_comm]
      · intro i hi
        rcases hreadElem 0 (by simp [kernelArity]) i hi with ⟨_, x, hrx, _⟩
        rcases hreadElem 1 (by simp [kernelArity]) i hi with ⟨_, y, hry, _⟩
        simp [specU64, evalParKernelElem, hrx, hry]
    | stencil1D3Pt wL wC wR =>
      have hst : ∀ cx < len, ∃ v : UInt64,
          evalParKernelElem env st inputs len (.stencil1D3Pt wL wC wR) cx = .ok v ∧
          (if (cx == 0 || decide (len ≤ cx + 1)) = true then
            if h0 : cx < (wordAt 0).length then (wordAt 0)[cx] else 0#64
          else if hL : cx - 1 < (wordAt 0).length then
            if hC : cx < (wordAt 0).length then
              if hR : cx + 1 < (wordAt 0).length then
                wL.toBitVec * (wordAt 0)[cx - 1] + wC.toBitVec * (wordAt 0)[cx] +
                  wR.toBitVec * (wordAt 0)[cx + 1]
              else 0#64 else 0#64 else 0#64) = v.toBitVec := by
        intro cx hcx
        rcases hreadElem 0 (by simp [kernelArity]) cx hcx with ⟨hcC, xC, hrC, hwC⟩
        cases hedge : (cx == 0 || decide (cx + 1 ≥ len))
        · have hcxPos : 0 < cx := by cases cx with | zero => simp at hedge | succ _ => omega
          have hcx1Lt : cx + 1 < len := by
            rcases Bool.or_eq_false_iff.mp hedge with ⟨_, h2⟩; simp only [decide_eq_false_iff_not] at h2; omega
          rcases hreadElem 0 (by simp [kernelArity]) (cx - 1) (by omega) with ⟨hcL, xL, hrL, hwL⟩
          rcases hreadElem 0 (by simp [kernelArity]) (cx + 1) hcx1Lt with ⟨hcR, xR, hrR, hwR⟩
          simp only [ge_iff_le] at hedge
          exact ⟨wL * xL + wC * xC + wR * xR, by simp [evalParKernelElem, hedge, hrL, hrC, hrR],
            by rw [ite_eq_right Bool.false_ne_true, dite_eq_left hcL, dite_eq_left hcC, dite_eq_left hcR,
              hwL, hwC, hwR]; rfl⟩
        · simp only [ge_iff_le] at hedge
          exact ⟨xC, by simp [evalParKernelElem, hedge, hrC], by rw [ite_eq_left rfl, dite_eq_left hcC, hwC]⟩
      refine ⟨3, 3, 13, 7, 15, stencilMid s!"$L_boundary_{name}" wL wC wR,
        by omega, by omega, by omega, by omega, rfl, ?_,
        stencilMid_no_doneLbl name wL wC wR,
        by simp [ctaStepsForKind, maxMidStepsForKind], ?_, ?_⟩
      · have hmid : stencilMid s!"$L_boundary_{name}" wL wC wR =
            [ ins (.ldParam .u64 "%rd8" "param_in0")
            , ins (.cvtaToGlobal .u64 "%rd8" (.reg "%rd8"))
            , ins (.add .none .u64 "%rd8" (.reg "%rd8") (.reg "%rd5"))
            , ins (.ldGlobal .u64 "%rd7" (.regOffset "%rd8" 0))
            , ins (.setp .eq .u64 "%p1" (.reg "%rd2") (i64 0))
            , ins (.add .none .u64 "%rd9" (.reg "%rd2") (i64 1))
            , ins (.setp .ge .u64 "%p2" (.reg "%rd9") (.reg "%rd3"))
            , ins (.bitOr .pred "%p1" (.reg "%p1") (.reg "%p2"))
            , .instr (some { predReg := "%p1" }) (.bra s!"$L_boundary_{name}")
            , ins (.ldGlobal .u64 "%rd10" (.regOffset "%rd8" (-8)))
            , ins (.ldGlobal .u64 "%rd11" (.regOffset "%rd8" 8))
            , ins (.mul .lo .u64 "%rd12" (.reg "%rd10") (.immU64 wL.toBitVec))
            , ins (.mad .lo .u64 "%rd12" (.reg "%rd7") (.immU64 wC.toBitVec) (.reg "%rd12"))
            , ins (.mad .lo .u64 "%rd7" (.reg "%rd11") (.immU64 wR.toBitVec) (.reg "%rd12"))
            , .label s!"$L_boundary_{name}" ] := rfl
        simp only [lowerKind, kernelOf, gidSetup_eq_std, hmid, List.append_assoc, ins]
        rfl
      · refine midBodySpec_congr (midBody_stencil1D3Pt len name wL wC wR wordAt hwordLen houn) (fun cx hcx => ?_)
        rcases hst cx hcx with ⟨v, hv, hsw⟩
        dsimp only [specU64]; rw [hv]; exact hsw
      · intro i hi
        rcases hst i hi with ⟨v, hv, _⟩
        dsimp only [specU64]; rw [hv]
    | customScalar idxVar inVars body =>
      simp only [wfPTXKernel, Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_exists] at hwf
      rcases hwf with ⟨⟨hnodup, hnotMem⟩, ⟨s, hsort⟩⟩
      simp only [kernelArity] at harity hwordLen hreadElem houn ⊢
      have hCS := midBody_customScalar env st inputs idxVar inVars body name s len wordAt hwordLen
        harity hreadElem houn hnodup hnotMem hsort
      dsimp only at hCS
      rcases hLS : lowerScalar (customVarOf idxVar inVars) (baseEnv inVars.length) body with ⟨el, res, penv⟩
      have hbnd := lowerScalar_bounds_no_label (customVarOf idxVar inVars) (idxVar :: inVars)
        (baseEnv inVars.length) body s hsort (customVarOf_bound_all idxVar inVars hnodup hnotMem)
      simp only [hLS] at hbnd hCS
      rcases hbnd with ⟨hleRd, hleR, hleP, ⟨di, hdiLt, rfl⟩, hnoL⟩
      simp only [regIdx] at hCS
      have hBaseP : (baseEnv inVars.length).nextP = 1 := rfl
      refine ⟨penv.nextP, Nat.max 3 penv.nextR, Nat.max 7 penv.nextRd, di,
        4 * inVars.length + el.length, loadsUpTo inVars.length ++ el,
        by omega, Nat.lt_of_lt_of_le (by omega) (Nat.le_max_left 3 penv.nextR),
        Nat.lt_of_lt_of_le (by omega) (Nat.le_max_left 7 penv.nextRd),
        Nat.lt_of_lt_of_le hdiLt (Nat.le_max_right 7 penv.nextRd),
        by simp [lowerKind, hLS, kernelOf, stdKernelRegs],
        by simp [lowerKind, hLS, kernelOf, gidSetup_eq_std, loadsUpTo, List.append_assoc, iOp, ins, PReg.name],
        midBody_no_label_append (loadsUpTo_no_doneLbl name inVars.length) (hnoL _),
        by simp [ctaStepsForKind, maxMidStepsForKind, hLS], ?_, ?_⟩
      · refine midBodySpec_congr hCS (fun cx hcx => ?_)
        have helem := evalParKernelElem_customScalar_ok env st inputs idxVar inVars body s len cx
          wordAt harity (fun j hj => hreadElem j (by omega) cx hcx) hnodup hnotMem hsort
        rcases helem with ⟨v, hv⟩
        simp [specU64, hv]
      · intro i hi
        rcases evalParKernelElem_customScalar_ok env st inputs idxVar inVars body s len i wordAt harity
            (fun j hj => hreadElem j (by omega) i hi) hnodup hnotMem hsort with ⟨v, hv⟩
        simp [specU64, hv]
  have hlocal : (lowerKind name k).localBytes = 0 := by cases k <;> rfl
  have hmemEq : mkPTXGlobalMem inWords (kernelArity k) len =
      packGlobalBuffers (kernelArity k) len wordAt :=
    mkPTXGlobalMem_eq_pack _ _ _
  have hparamEq : mkPTXParamMem (kernelArity k) len = stdParamMem (kernelArity k) len :=
    mkPTXParamMem_eq_std _ _
  obtain ⟨gFinal, hev, hwords⟩ :=
    evalPTXKernel_guarded_1d nP nR nRd (kernelArity k) len nBlocks blockSize vi maxMid
      (ctaStepsForKind blockSize k) (lowerKind name k) s!"$L_done_{name}" mid wordAt hwordLen
      (fun i => (specU64 i).toBitVec) hregs hlocal hbody hp hr hr6 hvi houn hlenCov hnBlk32 hblk32
      hfuel hnoLbl hMid
  obtain ⟨elems, hloop, heqMap⟩ := evalParKernelLoop_of_all env st inputs len k specU64 (List.range len)
    (fun i hi => helemAll i (List.mem_range.mp hi))
  refine ⟨elems, lowerKind name k, gFinal, rfl, hloop, by simp [heqMap], ?_, ?_⟩
  · rw [hmemEq, hparamEq]; exact hev
  · intro i hi
    have hiLen : i < len := by simpa [heqMap] using hi
    have hget : elems[i]'hi = specU64 i := by subst heqMap; simp
    rw [hget, hwords i hiLen]

end LeanNative.Proofs.PTXLowerProofs
