import LeanNative.Proofs.PTXLowerProofs2

/-!
# `customScalar` `MidBodySpec` Proofs (`LeanNative.Proofs.PTXLowerProofs3`)

Proves `MidBodySpec` and `evalParKernelElem` totality for `.customScalar` (arbitrary-arity
`loadsUpTo` loop + `lowerScalar` expression evaluation) (`0 sorryAx`, `0 ofReduceBool`).
-/

namespace LeanNative.Proofs.PTXLowerProofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend
open LeanNative.Backend.PTXAst
open LeanNative.Proofs.PTXSIMT
open LeanNative.Backend.PTXLower
open LeanNative.Proofs.PTXScalarProofs

def regIdx : PReg → Nat
  | .rd n => n
  | .r n => n

def loadsUpTo (n : Nat) : List PTXStmt :=
  (List.range n).foldl (fun acc k => acc ++ loadIn k s!"%rd{7 + k}") []

theorem loadsUpTo_step (n : Nat) :
    loadsUpTo (n + 1) = loadsUpTo n ++ loadIn n s!"%rd{7 + n}" := by
  rw [loadsUpTo, loadsUpTo, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem loadsUpTo_length (n : Nat) : (loadsUpTo n).length = 4 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [loadsUpTo_step, List.length_append, ih, loadIn_eq_std, stdLoadIn]
    simp [Nat.mul_add]

theorem loadsUpTo_no_label (n : Nat) (lbl : String) :
    ∀ s ∈ loadsUpTo n, s ≠ .label lbl := by
  induction n with
  | zero => intro _ h; simp [loadsUpTo] at h
  | succ n ih =>
    rw [loadsUpTo_step]
    intro s hs
    rcases List.mem_append.mp hs with h1 | h2
    · exact ih s h1
    · rw [loadIn_eq_std] at h2
      simp only [stdLoadIn, List.mem_cons, List.mem_nil_iff, or_false] at h2
      rcases h2 with rfl | rfl | rfl | rfl <;> simp

def rfLoads (wordAt : Nat → BitVec 64) : Nat → PTXRegFile → PTXRegFile
  | 0, rf => rf
  | m + 1, rf => rfSet (rfLoads wordAt m rf) s!"%rd{7 + m}" (wordAt m)

theorem rfLoads_regTyped (wordAt : Nat → BitVec 64) {nP nR nRd : Nat} {rf : PTXRegFile}
    (hrt : RegTyped rf nP nR nRd) :
    ∀ m, RegTyped (rfLoads wordAt m rf) nP nR nRd
  | 0 => hrt
  | m + 1 => regTyped_rfSet (rfLoads_regTyped wordAt hrt m) s!"%rd{7 + m}" (wordAt m)

theorem rfLoads_lookup_lt7 (wordAt : Nat → BitVec 64) (rf : PTXRegFile) {r : Nat} (hr : r < 7) :
    ∀ m, (rfLoads wordAt m rf).regs.lookup s!"%rd{r}" = rf.regs.lookup s!"%rd{r}"
  | 0 => rfl
  | m + 1 => by
    dsimp only [rfLoads]
    rw [lookup_rfSet_ne _ s!"%rd{7 + m}" s!"%rd{r}" _
      (fun h => (by omega : 7 + m ≠ r) (regName_inj "%rd" (7 + m) r h.symm))]
    exact rfLoads_lookup_lt7 wordAt rf hr m

theorem rfLoads_lookup_input (wordAt : Nat → BitVec 64) (rf : PTXRegFile) :
    ∀ (m k : Nat), k < m →
      (rfLoads wordAt m rf).regs.lookup s!"%rd{7 + k}" = some (.scalar (wordAt k))
  | 0, _, hk => nomatch hk
  | m + 1, k, hk => by
    dsimp only [rfLoads]
    by_cases hkM : k = m
    · subst hkM; exact lookup_rfSet_self _ _ _
    · rw [lookup_rfSet_ne _ s!"%rd{7 + m}" s!"%rd{7 + k}" _
        (fun h => hkM (Nat.add_left_cancel (regName_inj "%rd" (7 + k) (7 + m) h)))]
      exact rfLoads_lookup_input wordAt rf m k (by omega)

theorem run_loadsUpTo
    (nIn len gid tx : Nat) (wordAt : Nat → BitVec 64)
    (cta : PTXCTAState) (done todo : List PTXThreadState) (saved : List MemAccessLog)
    (allowedLanes : Nat → Prop) (laneOf : Dim3 → Nat)
    (hpm : cta.paramMem = stdParamMem nIn len)
    (hgidLt : gid < len)
    (hdone : ∀ t ∈ done, t.halted = true)
    (hloadW : ∀ k < nIn, cta.globalMem.loadBits (k * len * 8 + gid * 8) 8 = some (wordAt k))
    (houn : (nIn + 1) * len * 8 ≤ 2 ^ 64) :
    ∀ (m : Nat) (pre suf : List PTXStmt) (rf : PTXRegFile) (nP nR nRd : Nat),
      m ≤ nIn →
      RegTyped rf nP nR nRd →
      7 + m ≤ nRd →
      rf.regs.lookup "%rd5" = some (.scalar (BitVec.ofNat 64 (gid * 8))) →
      SafePTXLog (nIn * len * 8) len allowedLanes laneOf cta.epochLog →
      ∃ logM : List MemAccessLog,
        PTXLogOk (nIn * len * 8) len allowedLanes laneOf logM ∧
        ∀ f,
          runCTAWithGlobalLog (f + 4 * m) (pre ++ loadsUpTo m ++ suf)
            { cta with threads := done ++ (laneAt 0 tx pre.length rf false :: todo) } saved =
          runCTAWithGlobalLog f (pre ++ loadsUpTo m ++ suf)
            { cta with
              threads := done ++ (laneAt 0 tx (pre.length + 4 * m) (rfLoads wordAt m rf) false :: todo)
              epochLog := logM } saved := by
  intro m
  induction m with
  | zero =>
    intro pre suf rf _ _ _ _ _ _ _ hlog
    refine ⟨cta.epochLog, ⟨hlog⟩, fun _ => ?_⟩
    simp [loadsUpTo, rfLoads]
  | succ m ih =>
    intro pre suf rf nP nR nRd hm hrt hrd hlk5 hlog
    let preM := pre ++ loadsUpTo m
    rcases ih pre (loadIn m s!"%rd{7 + m}" ++ suf) rf nP nR nRd (by omega) hrt
        (by omega) hlk5 hlog with ⟨logM, ⟨hlogM⟩, hrunM⟩
    have hrtM : RegTyped (rfLoads wordAt m rf) nP nR nRd := rfLoads_regTyped wordAt hrt m
    have hlk5M : (rfLoads wordAt m rf).regs.lookup "%rd5" =
        some (.scalar (BitVec.ofNat 64 (gid * 8))) := by
      have hr5 : s!"%rd{5}" = "%rd5" := rfl
      rw [← hr5, rfLoads_lookup_lt7 wordAt rf (by omega) m, hr5]
      exact hlk5
    have hparam : cta.paramMem.lookupParam? s!"param_in{m}" =
        some (BitVec.ofNat 64 (m * len * 8)) := by
      rw [hpm]; exact stdParamMem_lookup_in nIn len m (by omega)
    let entry : MemAccessLog := {
      tid := { x := tx, y := 0, z := 0 }, space := .global,
      addr := m * len * 8 + gid * 8, width := 8, isWrite := false, isAtomic := false }
    obtain ⟨_, hlogL⟩ := run_stdLoadIn 0 preM suf { cta with epochLog := logM } done todo hrtM
      0 tx m (7 + m) gid nIn len (wordAt m) allowedLanes laneOf (by omega) (by omega) (by omega)
      (by omega) hgidLt houn hdone saved hlk5M hparam (hloadW m (by omega)) hlogM
    refine ⟨entry :: logM, hlogL, fun f => ?_⟩
    obtain ⟨hrunLf, _⟩ := run_stdLoadIn f preM suf { cta with epochLog := logM } done todo hrtM
      0 tx m (7 + m) gid nIn len (wordAt m) allowedLanes laneOf (by omega) (by omega) (by omega)
      (by omega) hgidLt houn hdone saved hlk5M hparam (hloadW m (by omega)) hlogM
    have hrunM' := hrunM (f + 4)
    have hsplit1 : pre ++ loadsUpTo m ++ (loadIn m s!"%rd{7 + m}" ++ suf) =
        pre ++ loadsUpTo (m + 1) ++ suf := by
      rw [loadsUpTo_step]; simp [List.append_assoc]
    have hsplit2 : preM ++ stdLoadIn m s!"%rd{7 + m}" ++ suf =
        pre ++ loadsUpTo (m + 1) ++ suf := by
      rw [loadsUpTo_step, loadIn_eq_std]; simp [preM, List.append_assoc]
    have hpreL : preM.length = pre.length + 4 * m := by
      simp [preM, loadsUpTo_length]
    have hpcEnd : pre.length + 4 * m + 4 = pre.length + 4 * (m + 1) := by omega
    have hf4 : f + 4 * (m + 1) = (f + 4) + 4 * m := by omega
    rw [hsplit1] at hrunM'
    rw [hsplit2, hpreL, hpcEnd] at hrunLf
    rw [hf4]
    exact hrunM'.trans hrunLf

theorem nodup_idxOf_getElem (xs : List Nat) (hnd : xs.Nodup) (k : Nat) (hk : k < xs.length) :
    xs.idxOf? xs[k] = some k := by
  induction xs generalizing k with
  | nil => nomatch hk
  | cons x rest ih =>
    rcases List.nodup_cons.mp hnd with ⟨hnot, hndR⟩
    cases k with
    | zero => simp [List.idxOf?_cons]
    | succ k' =>
      have hk' : k' < rest.length := by simp at hk; omega
      have hne : rest[k']'hk' ≠ x := fun h => hnot (h ▸ List.getElem_mem hk')
      have hbeq : (x == rest[k']'hk') = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
      simp only [List.getElem_cons_succ, List.idxOf?_cons, hbeq]
      exact congrArg (fun o => Option.map (fun n => n + 1) o) (ih hndR k' hk')

private theorem idxOf?_eq_some_mem {xs : List Nat} {id k : Nat}
    (h : xs.idxOf? id = some k) : id ∈ xs := by
  induction xs generalizing k with
  | nil => simp [List.idxOf?] at h
  | cons x rest ih =>
    simp only [List.idxOf?_cons] at h
    cases hx : (x == id)
    · rw [hx] at h
      simp only [Bool.false_eq_true, ite_false, Option.map_eq_some_iff] at h
      rcases h with ⟨k', hk', _⟩
      exact .tail x (ih hk')
    · exact (beq_iff_eq.mp hx) ▸ .head rest

theorem customVarOf_props (idxVar : Nat) (inVars : List VarId) (hnd : inVars.Nodup)
    (hnot : idxVar ∉ inVars) :
    (customVarOf idxVar inVars idxVar = some (.rd 2)) ∧
    (∀ k (hk : k < inVars.length), customVarOf idxVar inVars inVars[k] = some (.rd (7 + k))) ∧
    (∀ id, id ≠ idxVar → id ∉ inVars → customVarOf idxVar inVars id = none) := by
  refine ⟨by simp [customVarOf], ?_, ?_⟩
  · intro k hk
    have hne : inVars[k] ≠ idxVar := fun h => hnot (h ▸ List.getElem_mem hk)
    have hbeq : (inVars[k] == idxVar) = false := beq_eq_false_iff_ne.mpr hne
    simp only [customVarOf, hbeq, Bool.false_eq_true, ite_false, nodup_idxOf_getElem inVars hnd k hk]
  · intro id hne hnot'
    have hbeq : (id == idxVar) = false := beq_eq_false_iff_ne.mpr hne
    simp only [customVarOf, hbeq, Bool.false_eq_true, ite_false]
    cases h : inVars.idxOf? id with
    | none => rfl
    | some k => exact False.elim (hnot' (idxOf?_eq_some_mem h))

private theorem varEnvMatchesPTX_append_one (curEnv : VarEnv) (varOf : Nat → Option PReg)
    (rdBound : Nat) (rf : PTXRegFile) (iv : VarId) (regK : Nat) (x : UInt64)
    (hk : regK < rdBound) (hvo : varOf iv = some (.rd regK))
    (hlk : rf.regs.lookup s!"%rd{regK}" = some (.scalar x.toBitVec))
    (vs : List VarId) (hnot : iv ∉ vs)
    (hcur : varEnvMatchesPTX curEnv varOf vs rdBound rf) :
    varEnvMatchesPTX (curEnv.bind iv (.u64 x)) varOf (vs ++ [iv]) rdBound rf := by
  intro id hid
  rcases List.mem_append.mp hid with hvs | hiv
  · have hne : id ≠ iv := fun heq => hnot (heq ▸ hvs)
    rcases hcur id hvs with ⟨k, xu, hk', hvo', he', hlk'⟩
    exact ⟨k, xu, hk', hvo',
      (VarEnv.bind_ne curEnv iv id (.u64 x) (beq_eq_false_iff_ne.mpr hne)).trans he', hlk'⟩
  · simp only [List.mem_singleton] at hiv; subst hiv
    exact ⟨regK, x, hk, hvo, VarEnv.bind_self curEnv id (.u64 x), hlk⟩

private theorem bindCustomParInputs_ptx (env : VarEnv) (st : HeapState) (inputs : List VarId)
    (gid : Nat) (inWords : Nat → List (BitVec 64))
    (hread : ∀ j < inputs.length, ∃ (hc : gid < (inWords j).length) (x : UInt64),
      readParInput env st inputs j gid = .ok x ∧ (inWords j)[gid]'hc = x.toBitVec)
    (varOf : Nat → Option PReg) (rdBound : Nat) (rf : PTXRegFile) :
    ∀ (rem : List VarId) (k0 : Nat) (curEnv : VarEnv) (idxVar : VarId) (prior : List VarId),
      k0 + rem.length = inputs.length →
      (idxVar :: (prior ++ rem)).Nodup →
      varEnvMatchesPTX curEnv varOf (idxVar :: prior) rdBound rf →
      (∀ m (hm : m < rem.length),
        7 + (k0 + m) < rdBound ∧
        varOf (rem[m]'hm) = some (.rd (7 + (k0 + m))) ∧
        ∃ (hc : gid < (inWords (k0 + m)).length),
          rf.regs.lookup s!"%rd{7 + (k0 + m)}" = some (.scalar ((inWords (k0 + m))[gid]'hc))) →
      ∃ kEnv : VarEnv,
        bindCustomParInputs env st inputs gid curEnv k0 rem = .ok kEnv ∧
        varEnvMatchesPTX kEnv varOf (idxVar :: (prior ++ rem)) rdBound rf
  | [], _, curEnv, _, _, _, _, hcur, _ => by
    simp only [List.append_nil, bindCustomParInputs]
    exact ⟨curEnv, rfl, hcur⟩
  | iv :: rest, k0, curEnv, idxVar, prior, hklen, hnd, hcur, hrem => by
    simp only [List.length_cons] at hklen
    rcases hread k0 (by omega) with ⟨_, x0, hr0, hw0⟩
    rcases hrem 0 (by simp) with ⟨hreg0, hvo0, _, hlk0⟩
    simp only [Nat.add_zero, List.getElem_cons_zero] at hreg0 hvo0 hlk0
    rw [hw0] at hlk0
    have hndCons := List.nodup_cons.mp hnd
    have hivNeIdx : iv ≠ idxVar := fun heq => hndCons.1 (heq ▸ List.mem_append_right prior (.head rest))
    have hivNotHead : iv ∉ (idxVar :: prior) := by
      rcases List.nodup_append.mp hndCons.2 with ⟨_, _, hdisj⟩
      intro hm; rcases List.mem_cons.mp hm with h1 | h2
      · exact hivNeIdx h1
      · exact hdisj iv h2 iv (.head rest) rfl
    have hnext := varEnvMatchesPTX_append_one curEnv varOf rdBound rf iv (7 + k0) x0
      hreg0 hvo0 hlk0 (idxVar :: prior) hivNotHead hcur
    simp only [List.cons_append] at hnext
    have happEq : prior ++ (iv :: rest) = (prior ++ [iv]) ++ rest := by simp
    rw [happEq] at hnd ⊢
    obtain ⟨kEnv, hbindRest, hmatchFinal⟩ :=
      bindCustomParInputs_ptx env st inputs gid inWords hread varOf rdBound rf
        rest (k0 + 1) (curEnv.bind iv (.u64 x0)) idxVar (prior ++ [iv]) (by omega) hnd hnext
        (fun m hm => by
          rcases hrem (m + 1) (by simp; omega) with ⟨hrm, hvom, hcm, hlkm⟩
          have hadd : k0 + (m + 1) = (k0 + 1) + m := by omega
          simp only [List.getElem_cons_succ, hadd] at hrm hvom hcm hlkm
          exact ⟨hrm, hvom, hcm, hlkm⟩)
    exact ⟨kEnv, by unfold bindCustomParInputs; rw [hr0]; exact hbindRest, hmatchFinal⟩

theorem evalParKernelElem_customScalar_ok
    (env : VarEnv) (st : HeapState) (inputs : List VarId)
    (idxVar : Nat) (inVars : List VarId) (body : ScalarExpr)
    (s : Bool) (len i : Nat)
    (inWords : Nat → List (BitVec 64))
    (harity : inputs.length = inVars.length)
    (hread : ∀ j < inVars.length,
      ∃ (hc : i < (inWords j).length) (x : UInt64),
        readParInput env st inputs j i = .ok x ∧ (inWords j)[i]'hc = x.toBitVec)
    (hnd : inVars.Nodup) (hnot : idxVar ∉ inVars)
    (hsort : inferScalarSort (idxVar :: inVars) body = some s) :
    ∃ v : UInt64, evalParKernelElem env st inputs len (.customScalar idxVar inVars body) i = .ok v := by
  have hndAll : (idxVar :: inVars).Nodup := List.nodup_cons.mpr ⟨hnot, hnd⟩
  rcases customVarOf_props idxVar inVars hnd hnot with ⟨hvoIdx, hvoIn, _⟩
  let wordAt : Nat → BitVec 64 := fun k => (inWords k)[i]?.getD 0#64
  let rf0 := rfSet (PTXRegFile.ofRegDecls []) "%rd2" (BitVec.ofNat 64 i)
  let rfL := rfLoads wordAt inVars.length rf0
  have hlk2 : rfL.regs.lookup "%rd2" = some (.scalar i.toUInt64.toBitVec) := by
    have hr2 : s!"%rd{2}" = "%rd2" := rfl
    rw [← hr2, rfLoads_lookup_lt7 wordAt rf0 (by omega) inVars.length, hr2, lookup_rfSet_self]
    rfl
  have hcur0 : varEnvMatchesPTX (env.bind idxVar (.u64 i.toUInt64)) (customVarOf idxVar inVars)
      [idxVar] (7 + inVars.length) rfL := by
    intro id hid
    simp only [List.mem_singleton] at hid; subst hid
    exact ⟨2, i.toUInt64, by omega, hvoIdx, VarEnv.bind_self env id _, hlk2⟩
  have hrem0 : ∀ m (hm : m < inVars.length),
      7 + (0 + m) < 7 + inVars.length ∧
      customVarOf idxVar inVars (inVars[m]'hm) = some (.rd (7 + (0 + m))) ∧
      ∃ (hc : i < (inWords (0 + m)).length),
        rfL.regs.lookup s!"%rd{7 + (0 + m)}" = some (.scalar ((inWords (0 + m))[i]'hc)) := by
    intro m hm
    simp only [Nat.zero_add]
    rcases hread m hm with ⟨hc, _, _, _⟩
    refine ⟨by omega, hvoIn m hm, hc, ?_⟩
    rw [rfLoads_lookup_input wordAt rf0 inVars.length m hm]
    simp [wordAt, List.getElem?_eq_getElem hc]
  obtain ⟨kEnv, hbind, hmatch⟩ :=
    bindCustomParInputs_ptx env st inputs i inWords (fun j hj => hread j (by omega))
      (customVarOf idxVar inVars) (7 + inVars.length) rfL inVars 0
      (env.bind idxVar (.u64 i.toUInt64)) idxVar [] (by omega) hndAll hcur0 hrem0
  simp only [List.nil_append] at hmatch
  have henv : ∀ id ∈ idxVar :: inVars, ∃ (k : Nat) (x : UInt64),
      customVarOf idxVar inVars id = some (.rd k) ∧ kEnv id = some (.u64 x) :=
    fun id hid => let ⟨k, x, _, hvo, he, _⟩ := hmatch id hid; ⟨k, x, hvo, he⟩
  obtain ⟨val, _, hevBody, hvs, _⟩ :=
    lowerScalar_eval_sound kEnv (customVarOf idxVar inVars) (idxVar :: inVars) henv body s hsort
  cases s with
  | false =>
    rcases valOfSort_false hvs with ⟨v, rfl, _⟩
    exact ⟨v, by simp [evalParKernelElem, hbind, hevBody]⟩
  | true =>
    rcases valOfSort_true hvs with ⟨b, rfl, _⟩
    exact ⟨if b then 1 else 0, by simp [evalParKernelElem, hbind, hevBody]⟩

theorem customVarOf_bound_all (idxVar : Nat) (inVars : List VarId)
    (hnd : inVars.Nodup) (hnot : idxVar ∉ inVars) :
    ∀ id ∈ idxVar :: inVars, ∃ k < (baseEnv inVars.length).nextRd,
      customVarOf idxVar inVars id = some (.rd k) := by
  rcases customVarOf_props idxVar inVars hnd hnot with ⟨hvoIdx, hvoIn, _⟩
  intro id hid
  rcases List.mem_cons.mp hid with rfl | hmem
  · exact ⟨2, by simp [baseEnv]; omega, hvoIdx⟩
  · rcases List.mem_iff_getElem.mp hmem with ⟨k, hk, rfl⟩
    exact ⟨7 + k, by simp [baseEnv]; omega, hvoIn k hk⟩

/-- `MidBodySpec` for `.customScalar idxVar inVars body`. -/
theorem midBody_customScalar
    (env : VarEnv) (st : HeapState) (inputs : List VarId)
    (idxVar : Nat) (inVars : List VarId) (body : ScalarExpr)
    (name : String) (s : Bool) (len : Nat)
    (inWords : Nat → List (BitVec 64)) (hlen : ∀ j < inVars.length, (inWords j).length = len)
    (harity : inputs.length = inVars.length)
    (hread : ∀ j < inVars.length, ∀ i < len,
      ∃ (hc : i < (inWords j).length) (x : UInt64),
        readParInput env st inputs j i = .ok x ∧ (inWords j)[i]'hc = x.toBitVec)
    (houn : (inVars.length + 1) * len * 8 ≤ 2 ^ 64)
    (hnd : inVars.Nodup) (hnot : idxVar ∉ inVars)
    (hsort : inferScalarSort (idxVar :: inVars) body = some s) :
    let out := lowerScalar (customVarOf idxVar inVars) (baseEnv inVars.length) body
    MidBodySpec out.2.2.nextP (Nat.max 3 out.2.2.nextR) (Nat.max 7 out.2.2.nextRd)
      inVars.length len (regIdx out.2.1) (4 * inVars.length + out.1.length)
      s!"$L_done_{name}" (loadsUpTo inVars.length ++ out.1) inWords hlen
      (fun gid =>
        match evalParKernelElem env st inputs len (.customScalar idxVar inVars body) gid with
        | .ok v => v.toBitVec
        | .error _ => 0#64) := by
  have hbnd := lowerScalar_bounds_no_label (customVarOf idxVar inVars) (idxVar :: inVars)
    (baseEnv inVars.length) body s hsort (customVarOf_bound_all idxVar inVars hnd hnot)
  rcases hLS : lowerScalar (customVarOf idxVar inVars) (baseEnv inVars.length) body with ⟨el, res, penv⟩
  simp only [hLS] at hbnd ⊢
  rcases hbnd with ⟨hleRd, hleR, hleP, ⟨di, hdi, rfl⟩, _⟩
  dsimp only [regIdx]
  intro blockSize ctaId tx cta done todo saved allowedLanes gid
    _ _ hpm _ _ _ hgidLt hdone hloadAll hlog
  let nP := penv.nextP
  let nR := Nat.max 3 penv.nextR
  let nRd := Nat.max 7 penv.nextRd
  have hnR3 : 3 ≤ nR := Nat.le_max_left 3 penv.nextR
  have hnRp : penv.nextR ≤ nR := Nat.le_max_right 3 penv.nextR
  have hnRd7 : 7 ≤ nRd := Nat.le_max_left 7 penv.nextRd
  have hnRdp : penv.nextRd ≤ nRd := Nat.le_max_right 7 penv.nextRd
  let doneLbl := s!"$L_done_{name}"
  let loads := loadsUpTo inVars.length
  let epilogue : List PTXStmt :=
    [.instr none (.stGlobal .u64 (.regOffset "%rd6" 0) (.reg s!"%rd{di}")),
     .label doneLbl, .instr none .ret]
  let stmts := stdGidSetup doneLbl ++ (loads ++ el) ++ epilogue
  have hrt0 : RegTyped (PTXRegFile.ofRegDecls (stdKernelRegs nP nR nRd)) nP nR nRd :=
    initRegs_typed nP nR nRd (by simp [baseEnv] at hleP; omega) (by omega) (by omega)
  let rfG := (gidLane blockSize ctaId (PTXRegFile.ofRegDecls (stdKernelRegs nP nR nRd))
    0 tx gid inVars.length len).regs
  have hrtG : RegTyped rfG nP nR nRd := gidLane_typed blockSize ctaId hrt0 0 tx gid inVars.length len
  have hlk2 : rfG.regs.lookup "%rd2" = some (.scalar (BitVec.ofNat 64 gid)) :=
    gidLane_lookup_gid blockSize ctaId _ 0 tx gid inVars.length len
  have hlk5 : rfG.regs.lookup "%rd5" = some (.scalar (BitVec.ofNat 64 (gid * 8))) :=
    gidLane_lookup_off blockSize ctaId _ 0 tx gid inVars.length len
  have hlk6 : rfG.regs.lookup "%rd6" =
      some (.scalar (BitVec.ofNat 64 (inVars.length * len * 8 + gid * 8))) :=
    gidLane_lookup_out blockSize ctaId _ 0 tx gid inVars.length len
  let wordAt : Nat → BitVec 64 := fun k => (inWords k)[gid]?.getD 0#64
  have hloadW : ∀ k < inVars.length,
      cta.globalMem.loadBits (k * len * 8 + gid * 8) 8 = some (wordAt k) := by
    intro k hk
    have hc : gid < (inWords k).length := by rw [hlen k hk]; exact hgidLt
    have hl := hloadAll k hk gid hgidLt
    simpa [wordAt, List.getElem?_eq_getElem hc] using hl
  obtain ⟨logM, ⟨hlogM⟩, hrunLoads⟩ := run_loadsUpTo inVars.length len gid tx wordAt cta done todo
    saved allowedLanes (laneOf1D blockSize ctaId) hpm hgidLt hdone hloadW houn
    inVars.length (stdGidSetup doneLbl) (el ++ epilogue) rfG nP nR nRd (Nat.le_refl _) hrtG
    (by simp [baseEnv] at hleRd; omega) hlk5 hlog
  let rfL := rfLoads wordAt inVars.length rfG
  have hndAll : (idxVar :: inVars).Nodup := List.nodup_cons.mpr ⟨hnot, hnd⟩
  rcases customVarOf_props idxVar inVars hnd hnot with ⟨hvoIdx, hvoIn, _⟩
  have hlk2L : rfL.regs.lookup "%rd2" = some (.scalar gid.toUInt64.toBitVec) := by
    have hr2 : s!"%rd{2}" = "%rd2" := rfl
    rw [← hr2, rfLoads_lookup_lt7 wordAt rfG (by omega) inVars.length, hr2, hlk2]
    rfl
  have hcur0 : varEnvMatchesPTX (env.bind idxVar (.u64 gid.toUInt64)) (customVarOf idxVar inVars)
      [idxVar] (7 + inVars.length) rfL := by
    intro id hid
    simp only [List.mem_singleton] at hid; subst hid
    exact ⟨2, gid.toUInt64, by omega, hvoIdx, VarEnv.bind_self env id _, hlk2L⟩
  have hrem0 : ∀ m (hm : m < inVars.length),
      7 + (0 + m) < 7 + inVars.length ∧
      customVarOf idxVar inVars (inVars[m]'hm) = some (.rd (7 + (0 + m))) ∧
      ∃ (hc : gid < (inWords (0 + m)).length),
        rfL.regs.lookup s!"%rd{7 + (0 + m)}" = some (.scalar ((inWords (0 + m))[gid]'hc)) := by
    intro m hm
    simp only [Nat.zero_add]
    have hc : gid < (inWords m).length := by rw [hlen m hm]; exact hgidLt
    refine ⟨by omega, hvoIn m hm, hc, ?_⟩
    rw [rfLoads_lookup_input wordAt rfG inVars.length m hm]
    simp [wordAt, List.getElem?_eq_getElem hc]
  obtain ⟨kEnv, hbind, hmatch⟩ :=
    bindCustomParInputs_ptx env st inputs gid inWords (fun j hj => hread j (by omega) gid hgidLt)
      (customVarOf idxVar inVars) (7 + inVars.length) rfL inVars 0
      (env.bind idxVar (.u64 gid.toUInt64)) idxVar [] (by omega) hndAll hcur0 hrem0
  simp only [List.nil_append] at hmatch
  have henv : ∀ id ∈ idxVar :: inVars, ∃ (k : Nat) (x : UInt64),
      customVarOf idxVar inVars id = some (.rd k) ∧ kEnv id = some (.u64 x) :=
    fun id hid => let ⟨k, x, _, hvo, he, _⟩ := hmatch id hid; ⟨k, x, hvo, he⟩
  obtain ⟨val, bv, hevBody, hvs, hExFn⟩ :=
    lowerScalar_eval_sound kEnv (customVarOf idxVar inVars) (idxVar :: inVars) henv body s hsort
  have hEx := hExFn (baseEnv inVars.length) nP nR nRd rfL hmatch
  simp only [hLS] at hEx
  obtain ⟨di', rfFinal, hresEq, _, hframe, hlkDi, hpure⟩ :=
    hEx (by omega) (by omega) (by omega)
  cases hresEq
  have hrtFinal : RegTyped rfFinal nP nR nRd :=
    regFrame_regTyped hframe (rfLoads_regTyped wordAt hrtG inVars.length)
  have hlk6Final : rfFinal.regs.lookup "%rd6" =
      some (.scalar (BitVec.ofNat 64 (inVars.length * len * 8 + gid * 8))) := by
    have hr6 : s!"%rd{6}" = "%rd6" := rfl
    rw [← hr6]
    exact (hframe.rd_eq 6 (by simp [baseEnv]; omega)).trans
      ((rfLoads_lookup_lt7 wordAt rfG (by omega) inVars.length).trans (by rw [hr6]; exact hlk6))
  have hbvEq : bv = (match evalParKernelElem env st inputs len (.customScalar idxVar inVars body) gid with
      | .ok v => v.toBitVec
      | .error _ => 0#64) := by
    cases s with
    | false =>
      rcases valOfSort_false hvs with ⟨v, rfl, rfl⟩
      simp [evalParKernelElem, hbind, hevBody]
    | true =>
      rcases valOfSort_true hvs with ⟨b, rfl, rfl⟩
      simp only [evalParKernelElem, hbind, hevBody]
      cases b <;> rfl
  rw [hbvEq] at hlkDi
  refine ⟨4 * inVars.length + el.length, Nat.le_refl _, rfFinal, logM,
    hrtFinal, hlk6Final, hlkDi, hlogM, fun f => ?_⟩
  rw [gidLane_eq_laneAt blockSize ctaId _ 0 tx gid inVars.length len rfl]
  have hfSplit : f + (4 * inVars.length + el.length) = (f + el.length) + 4 * inVars.length := by omega
  have hstLoads : stdGidSetup doneLbl ++ loads ++ (el ++ epilogue) = stmts := by
    simp [stmts, List.append_assoc]
  have hpreLen : (stdGidSetup doneLbl).length = 13 := rfl
  have hrunL := hrunLoads (f + el.length)
  rw [hstLoads, hpreLen] at hrunL
  have hslice : SliceAt stmts el (13 + 4 * inVars.length) := by
    have hstMid : stmts = (stdGidSetup doneLbl ++ loads) ++ el ++ epilogue := by
      simp [stmts, List.append_assoc]
    have hlenMid : (stdGidSetup doneLbl ++ loads).length = 13 + 4 * inVars.length := by
      rw [List.length_append, loadsUpTo_length]; rfl
    rw [hstMid, ← hlenMid]
    exact sliceAt_mid_split _ _ _
  have hrunEl := hpure (rfLoads_regTyped wordAt hrtG inVars.length) f stmts
    { cta with epochLog := logM } done todo 0 tx (13 + 4 * inVars.length) saved hdone hslice
  have hpcEnd : (13 + 4 * inVars.length) + el.length = 13 + (loads ++ el).length := by
    rw [List.length_append, loadsUpTo_length]; omega
  rw [hpcEnd] at hrunEl
  change runCTAWithGlobalLog (f + (4 * inVars.length + el.length)) stmts _ saved =
    runCTAWithGlobalLog f stmts _ saved
  rw [hfSplit, hrunL]
  exact hrunEl

end LeanNative.Proofs.PTXLowerProofs
