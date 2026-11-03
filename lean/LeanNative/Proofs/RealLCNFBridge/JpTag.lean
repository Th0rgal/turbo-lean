import LeanNative.Proofs.RealLCNFBridge.StepMono

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

private theorem getActiveCtor_clear (st : RealBridgeState) (vid w : VarId) :
    RealBridgeState.getActiveCtor? { activeCtor := st.activeCtor.filter (fun (v, _) => v != vid) } w =
      if w == vid then none else st.getActiveCtor? w := by
  by_cases h : w = vid
  · subst h
    unfold RealBridgeState.getActiveCtor?
    have hnone : ∀ (l : List (VarId × Lean.Name)) (q : VarId),
        (l.filter (fun (v, _) => v != q)).find? (fun (v, _) => v == q) = none := by
      intro l q; induction l with
      | nil => rfl
      | cons hd tl ih =>
        rcases hd with ⟨v, c⟩; dsimp only [List.filter]
        cases hvu : (v != q)
        · exact ih
        · dsimp only [List.find?]
          have hvu' : (v == q) = false := by revert hvu; simp [bne]
          rw [hvu']; exact ih
    simp only [beq_self_eq_true, ↓reduceIte]; rw [hnone]; rfl
  · simp only [nat_beq_false h, Bool.false_eq_true, ↓reduceIte]
    exact getActiveCtor_filter_ne st.activeCtor vid w h

private theorem bridgeInv_applyJpOne (st_m : RealBridgeState) (lenv_m : LEnv) (venv_m : VarEnv)
    (fvarId : Lean.FVarId) (freshVid : VarId) (pTy : LNIRType) (v : Val)
    (hinv_m : BridgeStateInv st_m lenv_m venv_m)
    (hfreshLt : freshVid < st_m.nextVarId)
    (hfreshGt : ∀ y vid, st_m.lookupFVar? y = some vid → vid < freshVid) :
    BridgeStateInv
      { (st_m.setVarType freshVid pTy) with
        fvarMap := (fvarId, freshVid) :: st_m.fvarMap.filter (fun (f, _) => f != fvarId)
        activeCtor := st_m.activeCtor.filter (fun (w, _) => w != freshVid) }
      (lenv_m.bind fvarId v none (some pTy))
      (venv_m.bind freshVid v) := by
  let st_next : RealBridgeState :=
    { (st_m.setVarType freshVid pTy) with
      fvarMap := (fvarId, freshVid) :: st_m.fvarMap.filter (fun (f, _) => f != fvarId)
      activeCtor := st_m.activeCtor.filter (fun (w, _) => w != freshVid) }
  have hluEq : ∀ y, st_next.lookupFVar? y = if y == fvarId then some freshVid else st_m.lookupFVar? y :=
    fun y => lookupFVar_cons st_m.fvarMap fvarId y freshVid
  have htyEq : ∀ w, st_next.getVarType w = if w == freshVid then pTy else st_m.getVarType w :=
    fun w => getVarType_setVarType st_m freshVid w pTy
  have hctorEq : ∀ w, st_next.getActiveCtor? w = if w == freshVid then none else st_m.getActiveCtor? w :=
    fun w => getActiveCtor_clear st_m freshVid w
  refine ⟨fun y vid hy => ?_, fun y vid hy => ?_, fun y vid hy => ?_, fun y vid hy => ?_,
    fun y1 y2 vid hy1 hy2 => ?_, fun j ps body hj => hinv_m.jp_sync j ps body hj⟩
  · rw [hluEq] at hy
    cases hyx : (y == fvarId) <;> rw [hyx] at hy
    · simp only [Bool.false_eq_true, ↓reduceIte] at hy; exact hinv_m.fvar_lt y vid hy
    · simp only [↓reduceIte] at hy; injection hy with hvid
      rw [← hvid]; exact hfreshLt
  · rw [hluEq] at hy
    cases hyx : (y == fvarId) <;> rw [hyx] at hy
    · simp only [Bool.false_eq_true, ↓reduceIte] at hy
      have hlt : vid < freshVid := hfreshGt y vid hy
      rcases hinv_m.fvar_val y vid hy with ⟨hL, hV⟩
      dsimp only [LEnv.bind]; rw [hyx, venv_bind_fresh venv_m freshVid vid hlt v]
      exact ⟨hL, hV⟩
    · simp only [↓reduceIte] at hy; injection hy with hvid; rw [← hvid]
      dsimp only [LEnv.bind]; rw [hyx, VarEnv.bind_self]
      exact ⟨rfl, rfl⟩
  · rw [hluEq] at hy
    cases hyx : (y == fvarId) <;> rw [hyx] at hy
    · simp only [Bool.false_eq_true, ↓reduceIte] at hy
      have hlt : vid < freshVid := hfreshGt y vid hy
      dsimp only [LEnv.bind]; rw [hyx, htyEq, nat_beq_false (Nat.ne_of_lt hlt)]; simp only [Bool.false_eq_true, ↓reduceIte]
      exact hinv_m.fvar_ty y vid hy
    · simp only [↓reduceIte] at hy; injection hy with hvid; rw [← hvid]
      dsimp only [LEnv.bind]; rw [hyx, htyEq, beq_self_eq_true]; rfl
  · rw [hluEq] at hy
    cases hyx : (y == fvarId) <;> rw [hyx] at hy
    · simp only [Bool.false_eq_true, ↓reduceIte] at hy
      have hlt : vid < freshVid := hfreshGt y vid hy
      dsimp only [LEnv.bind]; rw [hyx, hctorEq, nat_beq_false (Nat.ne_of_lt hlt)]; simp only [Bool.false_eq_true, ↓reduceIte]
      exact hinv_m.fvar_ctor y vid hy
    · simp only [↓reduceIte] at hy; injection hy with hvid; rw [← hvid]
      dsimp only [LEnv.bind]; rw [hyx, hctorEq, beq_self_eq_true]; rfl
  · rw [hluEq] at hy1 hy2
    cases hy1x : (y1 == fvarId) <;> rw [hy1x] at hy1
    · simp only [Bool.false_eq_true, ↓reduceIte] at hy1
      cases hy2x : (y2 == fvarId) <;> rw [hy2x] at hy2
      · simp only [Bool.false_eq_true, ↓reduceIte] at hy2
        exact hinv_m.fvar_inj y1 y2 vid hy1 hy2
      · simp only [↓reduceIte] at hy2; injection hy2 with hvid; rw [← hvid] at hy1
        exact False.elim (Nat.lt_irrefl _ (hfreshGt y1 freshVid hy1))
    · simp only [↓reduceIte] at hy1; injection hy1 with hvid; rw [← hvid] at hy2
      cases hy2x : (y2 == fvarId) <;> rw [hy2x] at hy2
      · simp only [Bool.false_eq_true, ↓reduceIte] at hy2
        exact False.elim (Nat.lt_irrefl _ (hfreshGt y2 freshVid hy2))
      · exact (beq_iff_eq.mp hy1x).trans (beq_iff_eq.mp hy2x).symm

theorem bindJpCallArgsPure_rel (ctx : RealBridgeCtx) (venv0 : VarEnv) (base : VarId)
    (ps : List (Lean.Compiler.LCNF.Param .impure)) (as_ : List (Lean.Compiler.LCNF.Arg .impure))
    (st0 st1 : RealBridgeState) (lenv : LEnv)
    (binds : List (Lean.FVarId × VarId × LNIRType × Option VarId))
    (hbase : base ≤ st0.nextVarId)
    (hfvarBase : ∀ y vid, st0.lookupFVar? y = some vid → vid < base)
    (hinv : BridgeStateInv st0 lenv venv0)
    (h : bindJpCallArgsPure ctx st0 ps as_ = .ok (binds, st1)) :
    ∃ vs, evalJpArgs lenv.vals as_ = .ok vs ∧
      st1.fvarMap = st0.fvarMap ∧ st1.activeCtor = st0.activeCtor ∧ st1.jpDecls = st0.jpDecls ∧
      st0.nextVarId ≤ st1.nextVarId ∧
      (∀ u, u < st0.nextVarId → st1.getVarType u = st0.getVarType u) ∧
      (∀ (st_m : RealBridgeState) (lenv_m : LEnv) (venv_m : VarEnv) (cur : VarId)
         (fuel : Nat) (hst : HeapState) (body : LNIRCode),
        BridgeStateInv st_m lenv_m venv_m →
        base ≤ cur → cur ≤ st0.nextVarId → st_m.nextVarId = st1.nextVarId →
        (∀ x vid, st_m.lookupFVar? x = some vid → vid < cur) →
        (∀ u, u < base → venv_m u = venv0 u) →
        ∃ lenv' venv',
          bindJpParams ctx lenv.tys lenv_m ps as_ vs = .ok lenv' ∧
          BridgeStateInv (applyJpParamMapPure st_m binds) lenv' venv' ∧
          evalCode fuel venv_m hst (wrapJpCallBindsPure binds body) = evalCode fuel venv' hst body) := by
  induction ps generalizing as_ st0 st1 binds with
  | nil =>
    cases as_ with
    | cons _ _ => exact nomatch h
    | nil =>
      injection h with hp; rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
      refine ⟨[], rfl, rfl, rfl, rfl, Nat.le_refl _, fun _ _ => rfl, ?_⟩
      intro st_m lenv_m venv_m _ _ _ _ hinv_m _ _ _ _ _
      exact ⟨lenv_m, venv_m, rfl, hinv_m, rfl⟩
  | cons p ps ih =>
    cases as_ with
    | nil => exact nomatch h
    | cons a as_ =>
      let rawPTy := lowerGroundImpureTypeWith ctx p.type
      have hArgOpt : ∃ (pTy : LNIRType) (argVid? : Option VarId) (v : Val)
          (rest : List (Lean.FVarId × VarId × LNIRType × Option VarId)),
          bindJpCallArgsPure ctx (st0.freshVar pTy).2 ps as_ = .ok (rest, st1) ∧
          binds = (p.fvarId, (st0.freshVar pTy).1, pTy, argVid?) :: rest ∧
          evalJpArg lenv.vals a = .ok v ∧
          pTy = jpParamType ctx lenv.tys p a ∧
          (∀ venv_m : VarEnv, (∀ u, u < base → venv_m u = venv0 u) →
            match argVid? with
            | some argVid => venv_m argVid = some v
            | none => v = .u64 0) := by
        cases a with
        | erased =>
          dsimp only [bindJpCallArgsPure, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
          let pTy := if !ctx.allowStage1DHeap && isHeapPtrType rawPTy then .i64 else rawPTy
          cases hr : bindJpCallArgsPure ctx (st0.freshVar pTy).2 ps as_ with
          | error _ => rw [hr] at h; exact nomatch h
          | ok pr =>
            rw [hr] at h; injection h with hp
            rcases Prod.mk.inj hp with ⟨hb, hs⟩; subst hs
            exact ⟨pTy, none, .u64 0, pr.1, hr, hb.symm, rfl, rfl, fun _ _ => rfl⟩
        | type _ _ =>
          dsimp only [bindJpCallArgsPure, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
          let pTy := if !ctx.allowStage1DHeap && isHeapPtrType rawPTy then .i64 else rawPTy
          cases hr : bindJpCallArgsPure ctx (st0.freshVar pTy).2 ps as_ with
          | error _ => rw [hr] at h; exact nomatch h
          | ok pr =>
            rw [hr] at h; injection h with hp
            rcases Prod.mk.inj hp with ⟨hb, hs⟩; subst hs
            exact ⟨pTy, none, .u64 0, pr.1, hr, hb.symm, rfl, rfl, fun _ _ => rfl⟩
        | fvar x =>
          dsimp only [bindJpCallArgsPure, Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map] at h
          cases ha : lowerRealArg ctx st0 (.fvar x) true with
          | error _ => rw [ha] at h; exact nomatch h
          | ok pa =>
            rw [ha] at h; rcases pa with ⟨argVid, stA⟩
            rcases lowerRealArg_sound ctx st0 lenv venv0 (.fvar x) true argVid stA hinv ha with
              ⟨x', v, hxEq, hluX, hevalA, hvArg, htyX, hstA⟩
            injection hxEq with hx'; subst hx'
            subst stA; dsimp only at h
            let pTy :=
              if isUnboxedScalarOrTuple (st0.getVarType argVid) && isHeapPtrType rawPTy then
                st0.getVarType argVid
              else rawPTy
            cases hr : bindJpCallArgsPure ctx (st0.freshVar pTy).2 ps as_ with
            | error _ => rw [hr] at h; exact nomatch h
            | ok pr =>
              rw [hr] at h; injection h with hp
              rcases Prod.mk.inj hp with ⟨hb, hs⟩; subst hs
              refine ⟨pTy, some argVid, v, pr.1, hr, hb.symm, ?_, ?_, fun venv_m hvenvBase => ?_⟩
              · dsimp only [evalArg] at hevalA; dsimp only [evalJpArg]; exact hevalA
              · dsimp only [jpParamType, pTy, rawPTy]; rw [htyX]
              · exact (hvenvBase argVid (hfvarBase x argVid hluX)).trans hvArg
      rcases hArgOpt with ⟨pTy, argVid?, v, rest, hr, rfl, hevalA, hpTyEq, hvOpt⟩
      rcases freshVar_spec st0 pTy with ⟨hfv1, hfvNext, hfvTy, hfvLu, hfvCtor, _⟩
      let st2 := (st0.freshVar pTy).2
      have hbase2 : base ≤ st2.nextVarId := Nat.le_trans hbase (by rw [hfvNext]; exact Nat.le_succ _)
      have hfvarBase2 : ∀ y vid, st2.lookupFVar? y = some vid → vid < base := by
        intro y vid hy; rw [hfvLu] at hy; exact hfvarBase y vid hy
      have hinv2 : BridgeStateInv st2 lenv venv0 :=
        bridgeInv_ext st0 st2 lenv venv0 hinv (by rw [hfvNext]; exact Nat.le_succ _)
          (fun u hu => by rw [hfvTy u, nat_beq_false (Nat.ne_of_lt hu)]; rfl) rfl (fun u _ => hfvCtor u) rfl
      rcases ih as_ st2 st1 rest hbase2 hfvarBase2 hinv2 hr with
        ⟨vs, hevalRest, hfm, hac, hjp, hnextR, htyR, hstepRest⟩
      refine ⟨v :: vs, by simp [evalJpArgs, hevalA, hevalRest], hfm, hac, hjp,
        Nat.le_trans (by rw [hfvNext]; exact Nat.le_succ _) hnextR,
        fun u hu => by
          rw [htyR u (by rw [hfvNext]; exact Nat.lt_succ_of_lt hu), hfvTy u, nat_beq_false (Nat.ne_of_lt hu)]
          rfl,
        ?_⟩
      intro st_m lenv_m venv_m cur fuel hst body hinv_m hcurGe hcurLe hstmNext hstmLt hvenvBase
      let freshVid := (st0.freshVar pTy).1
      have hfreshEq : freshVid = st0.nextVarId := hfv1
      have hfreshLtStm : freshVid < st_m.nextVarId := by
        rw [hfreshEq, hstmNext]
        exact Nat.lt_of_lt_of_le (by rw [hfvNext]; exact Nat.lt_succ_self _) hnextR
      have hfreshGtStm : ∀ y vid, st_m.lookupFVar? y = some vid → vid < freshVid := by
        intro y vid hy; rw [hfreshEq]; exact Nat.lt_of_lt_of_le (hstmLt y vid hy) hcurLe
      let st_m1 : RealBridgeState :=
        { (st_m.setVarType freshVid pTy) with
          fvarMap := (p.fvarId, freshVid) :: st_m.fvarMap.filter (fun (f, _) => f != p.fvarId)
          activeCtor := st_m.activeCtor.filter (fun (w, _) => w != freshVid) }
      let lenv_m1 := lenv_m.bind p.fvarId v none (some pTy)
      let venv_m1 := venv_m.bind freshVid v
      have hinv_m1 : BridgeStateInv st_m1 lenv_m1 venv_m1 :=
        bridgeInv_applyJpOne st_m lenv_m venv_m p.fvarId freshVid pTy v hinv_m hfreshLtStm hfreshGtStm
      have hstm1Lt : ∀ y vid, st_m1.lookupFVar? y = some vid → vid < st2.nextVarId := by
        intro y vid hy
        have hlu1 := lookupFVar_cons st_m.fvarMap p.fvarId y freshVid
        change st_m1.lookupFVar? y = _ at hlu1; rw [hlu1] at hy
        cases hyp : (y == p.fvarId) <;> rw [hyp] at hy
        · simp only [Bool.false_eq_true, ↓reduceIte] at hy
          rw [hfvNext]; exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (hstmLt y vid hy) hcurLe)
        · simp only [↓reduceIte] at hy; injection hy with hvEq; rw [← hvEq, hfreshEq, hfvNext]
          exact Nat.lt_succ_self _
      have hvenv1Base : ∀ u, u < base → venv_m1 u = venv0 u := by
        intro u hu
        have huLtFresh : u < freshVid := by rw [hfreshEq]; exact Nat.lt_of_lt_of_le hu hbase
        exact (venv_bind_fresh venv_m freshVid u huLtFresh v).trans (hvenvBase u hu)
      rcases hstepRest st_m1 lenv_m1 venv_m1 st2.nextVarId fuel hst body
          hinv_m1 hbase2 (Nat.le_refl _) hstmNext hstm1Lt hvenv1Base with
        ⟨lenv', venv', hbindRest, hinvFinal, hevalWrap⟩
      have hbindHead : bindJpParams ctx lenv.tys lenv_m (p :: ps) (a :: as_) (v :: vs) = .ok lenv' := by
        dsimp only [bindJpParams]
        rw [← hpTyEq]
        exact hbindRest
      refine ⟨lenv', venv', hbindHead, hinvFinal, ?_⟩
      have hvM := hvOpt venv_m hvenvBase
      cases argVid? with
      | none =>
        subst hvM
        dsimp only [wrapJpCallBindsPure, evalCode, evalExpr, evalScalarExpr]
        exact hevalWrap
      | some argVid =>
        dsimp only [wrapJpCallBindsPure, evalCode, evalExpr, evalScalarExpr]
        rw [hvM]; exact hevalWrap

theorem bridgeInv_venv_agree (st : RealBridgeState) (lenv : LEnv) (venv venv' : VarEnv)
    (hinv : BridgeStateInv st lenv venv) (hagree : ∀ u, u < st.nextVarId → venv' u = venv u) :
    BridgeStateInv st lenv venv' := by
  refine ⟨hinv.fvar_lt, fun x vid hx => ?_, hinv.fvar_ty, hinv.fvar_ctor, hinv.fvar_inj, hinv.jp_sync⟩
  rw [hagree vid (hinv.fvar_lt x vid hx)]; exact hinv.fvar_val x vid hx

theorem bridgeInv_freshVar (st : RealBridgeState) (lenv : LEnv) (venv : VarEnv)
    (ty : LNIRType) (val : Val) (hinv : BridgeStateInv st lenv venv) :
    BridgeStateInv (st.freshVar ty).2 lenv (venv.bind (st.freshVar ty).1 val) := by
  rcases freshVar_spec st ty with ⟨hfv1, hfvNext, hfvTy, _, hfvCtor, _⟩
  rw [hfv1]
  exact bridgeInv_ext st (st.freshVar ty).2 lenv (venv.bind st.nextVarId val)
    (bridgeInv_venv_agree st lenv venv (venv.bind st.nextVarId val) hinv
      (fun u hu => venv_bind_fresh venv st.nextVarId u hu val))
    (by rw [hfvNext]; exact Nat.le_succ _)
    (fun u hu => by rw [hfvTy u, nat_beq_false (Nat.ne_of_lt hu)]; rfl) rfl (fun u _ => hfvCtor u) rfl

theorem varEnv_bind_comm (venv : VarEnv) (a b : VarId) (va vb : Val) (hne : a ≠ b) :
    (venv.bind a va).bind b vb = (venv.bind b vb).bind a va := by
  funext u
  dsimp only [VarEnv.bind]
  cases hub : (u == b)
  · cases hua : (u == a) <;> rfl
  · have hb : u = b := beq_iff_eq.mp hub; subst hb
    rw [nat_beq_false hne.symm]; rfl

theorem lenv_bind_withCtor (lenv : LEnv) (x : Lean.FVarId) (val : Val)
    (c : Lean.Name) (ty : LNIRType) :
    (lenv.bind x val none (some ty)).withCtor x c = lenv.bind x val (some c) (some ty) := by
  cases lenv; dsimp only [LEnv.bind, LEnv.withCtor]
  congr 1; funext y
  cases y == x <;> rfl

theorem lowerRefOpPure_sound (fuel : Nat) (isInc : Bool) (vid : VarId) (vt : LNIRType)
    (n : Nat) (kCode code' : LNIRCode) (lenv : LEnv) (venv : VarEnv) (hst hst1 hst' : HeapState)
    (x : Lean.FVarId) (val v : Val)
    (hty : lenv.tys x = some vt) (hvalL : lenv.vals x = some val) (hvalV : venv vid = some val)
    (hrop : lowerRefOpPure isInc vid vt n kCode = .ok code')
    (hrc : applyRc isInc lenv hst x n = .ok hst1)
    (hk : evalCode fuel venv hst1 kCode = .ok (v, hst')) :
    evalCode fuel venv hst code' = .ok (v, hst') := by
  unfold lowerRefOpPure at hrop; unfold applyRc at hrc
  have hisHeap : lenv.isHeapVar x = isHeapPtrType vt := by dsimp only [LEnv.isHeapVar]; rw [hty]
  cases hunb : isUnboxedScalarOrTuple vt
  · rw [hunb] at hrop
    cases hhp : isHeapPtrType vt
    · rw [hhp] at hrop; exact nomatch hrop
    · rw [hhp] at hrop hisHeap
      rw [hisHeap] at hrc; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hvalL] at hrc
      cases isInc
      · injection hrop with hc; subst code'
        change (match hst.evalDecRef venv vid n with
          | .ok st' => evalCode fuel venv st' kCode
          | .error err => .error err) = .ok (v, hst')
        unfold HeapState.evalDecRef; rw [hvalV]
        cases val with
        | objPtr objId => simp only [Bool.false_eq_true, ↓reduceIte] at hrc ⊢; rw [hrc]; exact hk
        | sarrayId bufId => simp only [Bool.false_eq_true, ↓reduceIte] at hrc ⊢; rw [hrc]; exact hk
        | _ =>
          dsimp only at hrc ⊢; injection hrc with hs
          subst hst1; exact hk
      · injection hrop with hc; subst code'
        change (match hst.evalIncRef venv vid n with
          | .ok st' => evalCode fuel venv st' kCode
          | .error err => .error err) = .ok (v, hst')
        unfold HeapState.evalIncRef; rw [hvalV]
        cases val with
        | objPtr objId => simp only [↓reduceIte] at hrc ⊢; rw [hrc]; exact hk
        | sarrayId bufId => simp only [↓reduceIte] at hrc ⊢; rw [hrc]; exact hk
        | _ =>
          dsimp only at hrc ⊢; injection hrc with hs
          subst hst1; exact hk
  · rw [hunb] at hrop; injection hrop with hc; subst code'
    rw [hisHeap, unboxed_not_heap vt hunb] at hrc
    injection hrc with hs; subst hst1; exact hk

private theorem evalCode_ite_asBool (fuel : Nat) (venv : VarEnv) (hst : HeapState)
    (condVar : VarId) (cond : Val) (b : Bool) (thenB elseB : LNIRCode)
    (hcond : venv condVar = some cond) (hb : asBool cond = .ok b) :
    evalCode fuel venv hst (.ite condVar thenB elseB) =
      if b then evalCode fuel venv hst thenB else evalCode fuel venv hst elseB := by
  dsimp only [evalCode]; rw [hcond]
  cases cond with
  | bool b0 =>
    injection hb with heq; subst b0
    cases b <;> rfl
  | u64 n => injection hb with heq; subst b; rfl
  | u256 w => injection hb with heq; subst b; rfl
  | _ => exact nomatch hb

theorem bridgeInv_empty : BridgeStateInv {} LEnv.empty VarEnv.empty where
  fvar_lt _ _ h := nomatch h
  fvar_val _ _ h := nomatch h
  fvar_ty _ _ h := nomatch h
  fvar_ctor _ _ h := nomatch h
  fvar_inj _ _ _ h _ := nomatch h
  jp_sync _ _ _ h := nomatch h

theorem internRealParams_sound (ctx : RealBridgeCtx) (ps : List (Lean.Compiler.LCNF.Param .impure)) :
    ∀ (args : List Val) (st : RealBridgeState) (lenv lenv' : LEnv) (venv : VarEnv),
      BridgeStateInv st lenv venv →
      bindParams ctx true lenv ps args = .ok lenv' →
      BridgeStateInv (internRealParams ctx st ps).2 lenv'
        (((internRealParams ctx st ps).1.zip args).foldl (fun acc (p, val) => acc.bind p.id val) venv) := by
  induction ps with
  | nil =>
    intro args st lenv lenv' venv hinv hbind
    cases args with
    | nil => injection hbind with he; subst lenv'; exact hinv
    | cons _ _ => exact nomatch hbind
  | cons p ps ih =>
    intro args st lenv lenv' venv hinv hbind
    cases args with
    | nil => exact nomatch hbind
    | cons a as_ =>
      dsimp only [internRealParams, RealBridgeState.internFVar, ↓reduceIte, List.zip, List.zipWith, List.foldl]
      dsimp only [bindParams, ↓reduceIte] at hbind
      exact ih as_ (st.allocFreshFVar p.fvarId (ctx.lowerParamType p)).2
        (lenv.bind p.fvarId a none (some (ctx.lowerParamType p))) lenv'
        (venv.bind st.nextVarId a)
        (bridgeInv_bind_fresh st lenv venv p.fvarId (ctx.lowerParamType p) a hinv) hbind

theorem discr_env_inv (st : RealBridgeState) (lenv : LEnv) (venv : VarEnv)
    (discr? : Option Lean.FVarId) (cname : Lean.Name) :
    BridgeStateInv st lenv venv →
    (∀ dx, discr? = some dx → (st.lookupFVar? dx).isSome = true) →
    let stIn := match discr?.bind st.lookupFVar? with
      | some dv => st.setActiveCtor dv cname | none => st
    let envIn := match discr? with
      | some dx => if (lenv.vals dx).isSome then lenv.withCtor dx cname else lenv
      | none => lenv
    BridgeStateInv stIn envIn venv ∧ stIn.nextVarId = st.nextVarId ∧
      (∀ u, stIn.getVarType u = st.getVarType u) := by
  intro hinv hdiscr
  cases discr? with
  | none => exact ⟨hinv, rfl, fun _ => rfl⟩
  | some dx =>
    have hsome := hdiscr dx rfl
    cases hlu : st.lookupFVar? dx with
    | none => rw [hlu] at hsome; cases hsome
    | some dv =>
      rcases hinv.fvar_val dx dv hlu with ⟨hveq, hvSome⟩
      have his : (lenv.vals dx).isSome = true := by rw [hveq]; exact hvSome
      dsimp only [Option.bind]; rw [hlu, his]; dsimp only [↓reduceIte]
      exact ⟨bridgeInv_setActiveCtor st lenv venv dv cname dx hinv hlu, rfl, fun _ => rfl⟩

theorem tag_branch_sound (fuel : Nat) (ctx : RealBridgeCtx) (lenv envIn : LEnv)
    (venv : VarEnv) (hst hst' : HeapState) (v cond : Val)
    (condVar : VarId) (condTy : LNIRType) (cidx : Nat) (isBool : Bool) (idx : Nat)
    (discr? : Option Lean.FVarId) (rest : List (Lean.Compiler.LCNF.Alt .impure))
    (altCode : Lean.Compiler.LCNF.Code .impure)
    (yesCode noCode code : LNIRCode) (st2 st' : RealBridgeState)
    (hi1 : lnirTypeEq condTy .i1 = true → isBool = true)
    (hcondV : venv condVar = some cond)
    (hyes : ∀ venvY, (∀ u, u < st2.nextVarId → venvY u = venv u) →
      evalStep fuel ctx envIn hst (.inl altCode) = .ok (v, hst') →
      evalCode (fuel + 1) venvY hst yesCode = .ok (v, hst'))
    (hno : ∀ venvN, (∀ u, u < st2.nextVarId → venvN u = venv u) →
      evalStep fuel ctx lenv hst (.inr (cond, isBool, idx + 1, discr?, rest)) = .ok (v, hst') →
      evalCode (fuel + 1) venvN hst noCode = .ok (v, hst'))
    (hbr : (if isBool || lnirTypeEq condTy .i1 then
        (Except.ok ((lowerTagBranchPure condVar condTy cidx isBool 0 yesCode noCode).1, st2) :
          Except String (LNIRCode × RealBridgeState))
      else
        Except.ok ((lowerTagBranchPure condVar condTy cidx isBool (st2.freshVar .i1).1 yesCode noCode).1,
          (st2.freshVar .i1).2)) = Except.ok (code, st'))
     (hev : (if isBool then
         match asBool cond with
         | .ok b =>
           if cidx == 0 then
             if b then evalStep fuel ctx lenv hst (.inr (cond, isBool, idx + 1, discr?, rest))
             else evalStep fuel ctx envIn hst (.inl altCode)
           else if cidx == 1 then
             if b then evalStep fuel ctx envIn hst (.inl altCode)
             else evalStep fuel ctx lenv hst (.inr (cond, isBool, idx + 1, discr?, rest))
           else evalStep fuel ctx lenv hst (.inr (cond, isBool, idx + 1, discr?, rest))
         | .error e => .error e
       else
         match cond with
         | .u64 n =>
           if n == cidx.toUInt64 then evalStep fuel ctx envIn hst (.inl altCode)
           else evalStep fuel ctx lenv hst (.inr (cond, isBool, idx + 1, discr?, rest))
         | _ => .error (.typeError "evalBinOp: invalid operand types")) = .ok (v, hst')) :
     evalCode (fuel + 1) venv hst code = .ok (v, hst') := by
  cases isBool
  · have hnotI1 : lnirTypeEq condTy .i1 = false := by
      cases h : lnirTypeEq condTy .i1
      · rfl
      · exact nomatch hi1 h
    rw [hnotI1] at hbr
    simp only [Bool.or_false, Bool.false_eq_true, ↓reduceIte, lowerTagBranchPure, hnotI1] at hbr hev
    injection hbr with hp; rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
    cases cond with
    | u64 n =>
      change (match evalExpr venv hst (.scalar (.binOp .eq (.var condVar) (.constU64 cidx.toUInt64))) with
        | .ok (b, hst1) => evalCode (fuel + 1) (venv.bind (st2.freshVar .i1).1 b) hst1 (.ite (st2.freshVar .i1).1 yesCode noCode)
        | .error err => .error err) = .ok (v, hst')
      rw [(freshVar_spec st2 .i1).1]
      dsimp only [evalExpr, evalScalarExpr]; rw [hcondV]; dsimp only [evalBinOp, ↓reduceIte]
      let cmpVar := st2.nextVarId
      cases hn : (n == cidx.toUInt64) <;> simp only [hn, Bool.false_eq_true, ↓reduceIte] at hev ⊢
      · dsimp only [evalCode]; rw [VarEnv.bind_self]
        exact hno (venv.bind cmpVar (.bool false))
          (fun u hu => venv_bind_fresh venv cmpVar u hu (.bool false)) hev
      · dsimp only [evalCode]; rw [VarEnv.bind_self]
        exact hyes (venv.bind cmpVar (.bool true))
          (fun u hu => venv_bind_fresh venv cmpVar u hu (.bool true)) hev
    | _ => exact nomatch hev
  · simp only [Bool.true_or, ↓reduceIte, lowerTagBranchPure] at hbr hev
    injection hbr with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
    cases hab : asBool cond with
    | error _ => rw [hab] at hev; exact nomatch hev
    | ok b =>
      rw [hab] at hev
      cases hc0 : (cidx == 0)
      · simp only [hc0, Bool.false_eq_true, ↓reduceIte] at hev ⊢
        cases hc1 : (cidx == 1)
        · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hev ⊢
          exact hno venv (fun _ _ => rfl) hev
        · simp only [hc1, ↓reduceIte] at hev ⊢
          rw [evalCode_ite_asBool (fuel + 1) venv hst condVar cond b yesCode noCode hcondV hab]
          cases b <;> simp only [↓reduceIte, Bool.false_eq_true] at hev ⊢
          · exact hno venv (fun _ _ => rfl) hev
          · exact hyes venv (fun _ _ => rfl) hev
      · simp only [hc0, ↓reduceIte] at hev ⊢
        rw [evalCode_ite_asBool (fuel + 1) venv hst condVar cond b noCode yesCode hcondV hab]
        cases b <;> simp only [↓reduceIte, Bool.false_eq_true] at hev ⊢
        · exact hyes venv (fun _ _ => rfl) hev
        · exact hno venv (fun _ _ => rfl) hev


end LeanNative.Proofs
