import LeanNative.Proofs.RealLCNFBridge.StepCases

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

theorem evalVarList_venv_agree :
    ∀ (vids : List VarId) (venv venv' : VarEnv) (base : VarId),
      (∀ u ∈ vids, u < base) →
      (∀ u, u < base → venv' u = venv u) →
      evalVarList venv' vids = evalVarList venv vids
  | [], _, _, _, _, _ => rfl
  | v0 :: vs, venv, venv', base, hmem, hagree => by
    dsimp only [evalVarList]
    have hv0 : venv' v0 = venv v0 := hagree v0 (hmem v0 (.head _))
    rw [hv0]
    cases venv v0 with
    | none => rfl
    | some _ =>
      rw [evalVarList_venv_agree vs venv venv' base (fun u hu => hmem u (.tail _ hu)) hagree]

theorem lowerRealArgList_lt (ctx : RealBridgeCtx) (allowObj : Bool) :
    ∀ (args : List (Lean.Compiler.LCNF.Arg .impure)) (st st1 : RealBridgeState)
      (lenv : LEnv) (venv : VarEnv) (vids : List VarId),
      BridgeStateInv st lenv venv →
      lowerRealArgList ctx st allowObj args = .ok (vids, st1) →
      ∀ u ∈ vids, u < st.nextVarId
  | [], _, _, _, _, vids, _, h, u, hu => by
    injection h with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩; cases hu
  | a :: rest, st, st1, lenv, venv, vids, hinv, h, u, hu => by
    unfold lowerRealArgList at h
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases ha : lowerRealArg ctx st a allowObj with
    | error _ => rw [ha] at h; exact nomatch h
    | ok pa =>
      rw [ha] at h; rcases pa with ⟨v0, stA⟩; dsimp only at h
      rcases lowerRealArg_sound ctx st lenv venv a allowObj v0 stA hinv ha with
        ⟨x0, _, _, hlu0, _, _, _, hstEq⟩
      rw [hstEq] at h
      cases hr : lowerRealArgList ctx st allowObj rest with
      | error _ => rw [hr] at h; exact nomatch h
      | ok pr =>
        rw [hr] at h; injection h with hp
        rcases Prod.mk.inj hp with ⟨hvidEq, _⟩; subst hvidEq
        cases List.mem_cons.mp hu with
        | inl hhd => rw [hhd]; exact hinv.fvar_lt x0 v0 hlu0
        | inr htl => exact lowerRealArgList_lt ctx allowObj rest st pr.2 lenv venv pr.1 hinv hr u htl

theorem allocZeroScalarSlotsPure_rel :
    ∀ (slots : List (Option Nat × LNIRType)) (st : RealBridgeState) (lenv : LEnv) (venv : VarEnv)
      (fuel : Nat) (hst : HeapState),
      BridgeStateInv st lenv venv →
      ∃ venvZ,
        BridgeStateInv (allocZeroScalarSlotsPure st slots).2 lenv venvZ ∧
        (∀ u, u < st.nextVarId → venvZ u = venv u) ∧
        evalVarList venvZ ((allocZeroScalarSlotsPure st slots).1.map Prod.fst) =
          .ok (slots.map fun _ => Val.u64 0) ∧
        ∀ body, evalCode (fuel + 1) venv hst
            (wrapZeroScalarSlotsPure (allocZeroScalarSlotsPure st slots).1 body) =
          evalCode (fuel + 1) venvZ hst body
  | [], st, _, venv, _, _, hinv =>
    ⟨venv, hinv, fun _ _ => rfl, rfl, fun _ => rfl⟩
  | (_, sTy) :: rest, st, lenv, venv, fuel, hst, hinv => by
    dsimp only [allocZeroScalarSlotsPure, wrapZeroScalarSlotsPure]
    rcases freshVar_spec st sTy with ⟨hfv1, hfvNext, _, _, _, _⟩
    let z := (st.freshVar sTy).1
    let st1 := (st.freshVar sTy).2
    let venv1 := venv.bind z (.u64 0)
    have hinv1 : BridgeStateInv st1 lenv venv1 :=
      bridgeInv_freshVar st lenv venv sTy (.u64 0) hinv
    rcases allocZeroScalarSlotsPure_rel rest st1 lenv venv1 fuel hst hinv1 with
      ⟨venvZ, hinvZ, hagree1, hvlRest, hwrapRest⟩
    have hzLt1 : z < st1.nextVarId := by
      dsimp only [z, st1]; rw [hfv1, hfvNext]; exact Nat.lt_succ_self _
    have hzZ : venvZ z = some (.u64 0) :=
      (hagree1 z hzLt1).trans (VarEnv.bind_self venv z (.u64 0))
    refine ⟨venvZ, hinvZ, fun u hu => ?_, ?_, fun body => ?_⟩
    · have huLtZ : u < z := by dsimp only [z]; rw [hfv1]; exact hu
      have huLt1 : u < st1.nextVarId := Nat.lt_trans huLtZ hzLt1
      exact (hagree1 u huLt1).trans (venv_bind_fresh venv z u huLtZ (.u64 0))
    · dsimp only [List.map, evalVarList]
      rw [hzZ, hvlRest]
    · dsimp only [evalCode, evalExpr, evalScalarExpr]
      exact hwrapRest body

theorem lowerScalarSlotCtor_sound (fuel : Nat) (ctx : RealBridgeCtx)
    (ih : ∀ (st st' : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
      (target : Lean.Compiler.LCNF.Code .impure ⊕
        (VarId × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure)))
      (code : LNIRCode),
      BridgeStateInv st lenv venv →
      lowerImpureStepPure fuel ctx st target = .ok (code, st') →
      (match target with
       | .inl c => evalStep fuel ctx lenv hst (.inl c) = .ok (v, hst')
       | .inr (condVar, isBool, idx, discr?, alts) =>
         condVar < st.nextVarId ∧
         (∀ dx, discr? = some dx → (st.lookupFVar? dx).isSome = true) ∧
         (lnirTypeEq (st.getVarType condVar) .i1 = true → isBool = true) ∧
         ∃ cond, venv condVar = some cond ∧
           evalStep fuel ctx lenv hst (.inr (cond, isBool, idx, discr?, alts)) = .ok (v, hst')) →
      evalCode fuel venv hst code = .ok (v, hst'))
    (st st' : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
    (fvarId : Lean.FVarId) (declTy : Lean.Expr)
    (info : Lean.Compiler.LCNF.CtorInfo) (args : Array (Lean.Compiler.LCNF.Arg .impure))
    (himp : Lean.Compiler.LCNF.Purity.impure = .impure)
    (k : Lean.Compiler.LCNF.Code .impure) (code : LNIRCode)
    (hinv : BridgeStateInv st lenv venv)
    (hsc : (ctx.allowStage1DHeap && (info.usize > 0 || info.ssize > 0)) = true)
    (h_lower : (do
      let some spec := ctx.findLayout? info.name
        | throw s!"[lean-native] Unknown constructor layout `{info.name}`"
      if args.size != spec.objSlots then
        throw s!"[lean-native] Ctor `{info.name}` expected {spec.objSlots} object args, got {args.size}"
      let (objVars, st1) ← lowerRealArgList ctx st true args.toList
      let objTys := objVars.map st1.getVarType
      if !(objTys.all fun t => isSupportedStage1BScalarOrTuple t ctx.arch || isHeapPtrType t) then
        throw s!"[lean-native] Unsupported object field type in `{info.name}`"
      let (zeros, stZ) := allocZeroScalarSlotsPure st1 spec.scalarSlots
      let (dst, st2) := stZ.allocFreshFVar fvarId .objPtr
      let st2' := st2.setActiveCtor dst info.name
      let (kCode, st3) ← lowerImpureStepPure fuel ctx st2' (.inl k)
      return (wrapZeroScalarSlotsPure zeros
        (.letBind dst .objPtr (.allocCtor spec.cidx objVars (zeros.map Prod.fst)) kCode), st3) :
        Except String (LNIRCode × RealBridgeState)) = .ok (code, st'))
    (h_eval : evalStep (fuel + 1) ctx lenv hst
      (.inl (.let { fvarId := fvarId, binderName := .anonymous, type := declTy,
                    value := .ctor info args himp } k)) = .ok (v, hst')) :
    evalCode (fuel + 1) venv hst code = .ok (v, hst') := by
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
    MonadExcept.throw, MonadExceptOf.throw, throwThe] at h_lower
  dsimp only [evalStep, evalLetValue] at h_eval
  rw [hsc] at h_eval; simp only [↓reduceIte] at h_eval
  cases hlay : ctx.findLayout? info.name <;> rw [hlay] at h_lower h_eval
  · exact nomatch h_lower
  · rename_i spec; dsimp only at h_lower h_eval
    cases har : (args.size != spec.objSlots) <;>
      simp only [har, ↓reduceIte, Bool.false_eq_true] at h_lower h_eval
    · cases hargL : lowerRealArgList ctx st true args.toList with
      | error _ => rw [hargL] at h_lower; exact nomatch h_lower
      | ok pa =>
        rw [hargL] at h_lower; rcases pa with ⟨objVars, st1⟩; dsimp only at h_lower
        rcases lowerRealArgList_sound ctx st lenv venv true args.toList objVars st1 hinv hargL with
          ⟨vs, hevalArgs, hvarList, _, hst1Eq, _⟩
        have hltVars := lowerRealArgList_lt ctx true args.toList st st1 lenv venv objVars hinv hargL
        subst st1
        rw [hevalArgs] at h_eval; dsimp only at h_eval
        cases htyOk : (!(objVars.map st.getVarType).all
            (fun t => isSupportedStage1BScalarOrTuple t ctx.arch || isHeapPtrType t)) <;>
          simp only [htyOk, ↓reduceIte, Bool.false_eq_true] at h_lower
        · rcases allocZeroScalarSlotsPure_rel spec.scalarSlots st lenv venv fuel hst hinv with
            ⟨venvZ, hinvZ, hagreeZ, hvlZeros, hwrapZ⟩
          let zeros := (allocZeroScalarSlotsPure st spec.scalarSlots).1
          let stZ := (allocZeroScalarSlotsPure st spec.scalarSlots).2
          let dst := (stZ.allocFreshFVar fvarId .objPtr).1
          let st2 := (stZ.allocFreshFVar fvarId .objPtr).2
          let st2' := st2.setActiveCtor dst info.name
          have hdstEq : dst = stZ.nextVarId := rfl
          have hluDst : st2.lookupFVar? fvarId = some dst := by
            dsimp only [st2, dst]; rw [lookupFVar_allocFresh, beq_self_eq_true]; rfl
          have hobjZ : evalVarList venvZ objVars = .ok vs :=
            (evalVarList_venv_agree objVars venv venvZ st.nextVarId hltVars hagreeZ).trans hvarList
          cases hk : lowerImpureStepPure fuel ctx st2' (.inl k) with
          | error _ => rw [hk] at h_lower; exact nomatch h_lower
          | ok pk =>
            rw [hk] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
            rw [hwrapZ]
            let zvals := spec.scalarSlots.map fun _ => Val.u64 0
            cases hempty : (vs.isEmpty && zvals.isEmpty)
            · dsimp only [zvals] at hempty
              rw [hempty] at h_eval; simp only [Bool.false_eq_true, ↓reduceIte] at h_eval
              cases hwf : (!vs.all Val.wfField)
              · rw [hwf] at h_eval; simp only [Bool.false_eq_true, ↓reduceIte] at h_eval
                let allocRes := hst.allocHeapCtor spec.cidx vs zvals
                have hallocEval : evalExpr venvZ hst
                    (.allocCtor spec.cidx objVars (zeros.map Prod.fst)) =
                    .ok (.objPtr allocRes.1, allocRes.2) := by
                  dsimp only [evalExpr]; rw [hobjZ, hvlZeros]
                  change (if (vs.isEmpty && zvals.isEmpty) then _ else _) = _
                  rw [hempty, hwf]; rfl
                have hinv2 : BridgeStateInv st2
                    (lenv.bind fvarId (.objPtr allocRes.1) none (some .objPtr))
                    (venvZ.bind dst (.objPtr allocRes.1)) :=
                  bridgeInv_bind_fresh stZ lenv venvZ fvarId .objPtr (.objPtr allocRes.1) hinvZ
                have hinv2' : BridgeStateInv st2'
                    (lenv.bind fvarId (.objPtr allocRes.1) (some info.name) (some .objPtr))
                    (venvZ.bind dst (.objPtr allocRes.1)) := by
                  rw [← lenv_bind_withCtor]
                  exact bridgeInv_setActiveCtor st2 _ _ dst info.name fvarId hinv2 hluDst
                have hEvalK : evalStep fuel ctx
                    (lenv.bind fvarId (.objPtr allocRes.1) (some info.name) (some .objPtr))
                    allocRes.2 (.inl k) = .ok (v, hst') := h_eval
                have hkEval := evalCode_fuel_mono_step fuel pk.1 _ allocRes.2 v hst'
                  (ih st2' pk.2 _ _ allocRes.2 hst' v (.inl k) pk.1 hinv2' hk hEvalK)
                dsimp only [evalCode]; rw [hallocEval]; exact hkEval
              · rw [hwf] at h_eval; simp only [↓reduceIte] at h_eval; exact nomatch h_eval
            · dsimp only [zvals] at hempty
              rw [hempty] at h_eval; simp only [↓reduceIte] at h_eval
              let tupVal : Val := .tuple [.u64 spec.cidx.toUInt64]
              have hallocEval : evalExpr venvZ hst
                  (.allocCtor spec.cidx objVars (zeros.map Prod.fst)) = .ok (tupVal, hst) := by
                dsimp only [evalExpr]; rw [hobjZ, hvlZeros]
                change (if (vs.isEmpty && zvals.isEmpty) then _ else _) = _
                rw [hempty]; rfl
              have hinv2 : BridgeStateInv st2
                  (lenv.bind fvarId tupVal none (some .objPtr))
                  (venvZ.bind dst tupVal) :=
                bridgeInv_bind_fresh stZ lenv venvZ fvarId .objPtr tupVal hinvZ
              have hinv2' : BridgeStateInv st2'
                  (lenv.bind fvarId tupVal (some info.name) (some .objPtr))
                  (venvZ.bind dst tupVal) := by
                rw [← lenv_bind_withCtor]
                exact bridgeInv_setActiveCtor st2 _ _ dst info.name fvarId hinv2 hluDst
              have hEvalK : evalStep fuel ctx
                  (lenv.bind fvarId tupVal (some info.name) (some .objPtr))
                  hst (.inl k) = .ok (v, hst') := h_eval
              have hkEval := evalCode_fuel_mono_step fuel pk.1 _ hst v hst'
                (ih st2' pk.2 _ _ hst hst' v (.inl k) pk.1 hinv2' hk hEvalK)
              dsimp only [evalCode]; rw [hallocEval]; exact hkEval
        · exact nomatch h_lower
    · exact nomatch h_lower

theorem lowerSetTag_sound (fuel : Nat) (ctx : RealBridgeCtx)
    (ih : ∀ (st st' : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
      (target : Lean.Compiler.LCNF.Code .impure ⊕
        (VarId × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure)))
      (code : LNIRCode),
      BridgeStateInv st lenv venv →
      lowerImpureStepPure fuel ctx st target = .ok (code, st') →
      (match target with
       | .inl c => evalStep fuel ctx lenv hst (.inl c) = .ok (v, hst')
       | .inr (condVar, isBool, idx, discr?, alts) =>
         condVar < st.nextVarId ∧
         (∀ dx, discr? = some dx → (st.lookupFVar? dx).isSome = true) ∧
         (lnirTypeEq (st.getVarType condVar) .i1 = true → isBool = true) ∧
         ∃ cond, venv condVar = some cond ∧
           evalStep fuel ctx lenv hst (.inr (cond, isBool, idx, discr?, alts)) = .ok (v, hst')) →
      evalCode fuel venv hst code = .ok (v, hst'))
    (st st' : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
    (x : Lean.FVarId) (cidx : Nat) (k : Lean.Compiler.LCNF.Code .impure)
    (himp : Lean.Compiler.LCNF.Purity.impure = .impure) (code : LNIRCode)
    (hinv : BridgeStateInv st lenv venv)
    (h_lower : lowerImpureStepPure (fuel + 1) ctx st (.inl (.setTag x cidx k himp)) = .ok (code, st'))
    (h_eval : evalStep (fuel + 1) ctx lenv hst (.inl (.setTag x cidx k himp)) = .ok (v, hst')) :
    evalCode (fuel + 1) venv hst code = .ok (v, hst') := by
  dsimp only [lowerImpureStepPure] at h_lower
  dsimp only [evalStep] at h_eval
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
    MonadExcept.throw, MonadExceptOf.throw, throwThe] at h_lower
  cases hv : st.lookupBoundFVar x <;> rw [hv] at h_lower
  · exact nomatch h_lower
  · rename_i objVid; dsimp only at h_lower
    rcases lookupBoundFVar_inv st lenv venv x objVid hinv hv with
      ⟨hluX, hobjLt, ⟨val, hvalL, hvalV⟩, _, hctorL⟩
    rw [hvalL] at h_eval
    cases hhp : (!(ctx.allowStage1DHeap && isHeapPtrType (st.getVarType objVid))) <;>
      simp only [hhp, ↓reduceIte, Bool.false_eq_true] at h_lower
    · have hresEq : lenv.resolveCtor? ctx x = st.resolveHeapCtor? ctx objVid x := by
        dsimp [LEnv.resolveCtor?, RealBridgeState.resolveHeapCtor?]; rw [hctorL]
      rw [hresEq] at h_eval
      let nextCtor? : Option Lean.Name :=
        match st.resolveHeapCtor? ctx objVid x with
        | some cur => if ctx.hasSiblingEntry cur then ctx.findSiblingCtor? cur cidx else none
        | none => none
      let st1 := st.setActiveCtorOpt objVid nextCtor?
      let st2 := (st1.freshVar .i64).2
      let st3 := (st2.freshVar .unit).2
      have h_lower' :
          ∃ pk, lowerImpureStepPure fuel ctx st3 (.inl k) = .ok pk ∧
            code = .letBind (st1.freshVar .i64).1 .i64 (.scalar (.constU64 cidx.toUInt64))
              (.letBind (st2.freshVar .unit).1 .unit
                (.call "lean_native_ctor_set_tag" [objVid, (st1.freshVar .i64).1] .unit false) pk.1) ∧
            st' = pk.2 := by
        dsimp only [st1, st2, st3, nextCtor?]
        cases hrc : st.resolveHeapCtor? ctx objVid x
        · rw [hrc] at h_lower; dsimp only at h_lower ⊢
          cases hk : lowerImpureStepPure fuel ctx
              (((st.setActiveCtorOpt objVid none).freshVar .i64).2.freshVar .unit).2 (.inl k)
          · rw [hk] at h_lower; exact nomatch h_lower
          · rw [hk] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨hc, hs⟩
            exact ⟨_, rfl, hc.symm, hs.symm⟩
        · rename_i cur
          rw [hrc] at h_lower; dsimp only at h_lower ⊢
          cases hhs : ctx.hasSiblingEntry cur
          · rw [hhs] at h_lower; simp only [Bool.false_eq_true, ↓reduceIte] at h_lower ⊢
            cases hk : lowerImpureStepPure fuel ctx
                (((st.setActiveCtorOpt objVid none).freshVar .i64).2.freshVar .unit).2 (.inl k)
            · rw [hk] at h_lower; exact nomatch h_lower
            · rw [hk] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨hc, hs⟩
              exact ⟨_, rfl, hc.symm, hs.symm⟩
          · rw [hhs] at h_lower; simp only [↓reduceIte] at h_lower ⊢
            cases hfs : ctx.findSiblingCtor? cur cidx
            · rw [hfs] at h_lower; exact nomatch h_lower
            · rename_i nextC
              rw [hfs] at h_lower; dsimp only at h_lower ⊢
              cases hk : lowerImpureStepPure fuel ctx
                  (((st.setActiveCtorOpt objVid (some nextC)).freshVar .i64).2.freshVar .unit).2 (.inl k)
              · rw [hk] at h_lower; exact nomatch h_lower
              · rw [hk] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨hc, hs⟩
                exact ⟨_, rfl, hc.symm, hs.symm⟩
      rcases h_lower' with ⟨pk, hk, rfl, rfl⟩
      cases val with
      | objPtr objId =>
        dsimp only at h_eval
        change (match hst.setHeapObjTagExclusive objId (cidx.toUInt64).toNat with
          | .ok st' => evalStep fuel ctx (lenv.withCtorOpt x nextCtor?) st' (.inl k)
          | .error e => .error e) = .ok (v, hst') at h_eval
        cases hset : hst.setHeapObjTagExclusive objId (cidx.toUInt64).toNat with
        | error _ => rw [hset] at h_eval; exact nomatch h_eval
        | ok hst1 =>
          rw [hset] at h_eval
          have hst1Next : st1.nextVarId = st.nextVarId := by
            dsimp only [st1]; cases nextCtor? <;> rfl
          have hinv1 : BridgeStateInv st1 (lenv.withCtorOpt x nextCtor?) venv :=
            bridgeInv_setActiveCtorOpt st lenv venv objVid nextCtor? x hinv hluX
          let venv1 := venv.bind (st1.freshVar .i64).1 (.u64 cidx.toUInt64)
          let venv2 := venv1.bind (st2.freshVar .unit).1 .unit
          have hinv3 : BridgeStateInv st3 (lenv.withCtorOpt x nextCtor?) venv2 :=
            bridgeInv_freshVar st2 (lenv.withCtorOpt x nextCtor?) venv1 .unit .unit
              (bridgeInv_freshVar st1 (lenv.withCtorOpt x nextCtor?) venv .i64 (.u64 cidx.toUInt64) hinv1)
          have hkEval := evalCode_fuel_mono_step fuel pk.1 venv2 hst1 v hst'
            (ih st3 pk.2 (lenv.withCtorOpt x nextCtor?) venv2 hst1 hst' v (.inl k) pk.1 hinv3 hk h_eval)
          have htagId : (st1.freshVar .i64).1 = st.nextVarId :=
            (freshVar_spec st1 .i64).1.trans hst1Next
          have hobjV1 : venv1 objVid = some (.objPtr objId) := by
            dsimp only [venv1]; rw [htagId, venv_bind_fresh venv st.nextVarId objVid hobjLt]; exact hvalV
          have htagV1 : venv1 (st1.freshVar .i64).1 = some (.u64 cidx.toUInt64) :=
            VarEnv.bind_self _ _ _
          have hcall : evalExpr venv1 hst
              (.call "lean_native_ctor_set_tag" [objVid, (st1.freshVar .i64).1] .unit false) =
              .ok (.unit, hst1) := by
            have hvl : evalVarList venv1 [objVid, (st1.freshVar .i64).1] =
                .ok [.objPtr objId, .u64 cidx.toUInt64] := by
              simp only [evalVarList, hobjV1, htagV1]
            dsimp only [evalExpr]; rw [hvl]
            change (hst.setHeapObjTagExclusive objId (cidx.toUInt64).toNat).map (Val.unit, ·) =
              .ok (Val.unit, hst1)
            rw [hset]; rfl
          change (match evalExpr venv hst (.scalar (.constU64 cidx.toUInt64)) with
            | .ok (tv, hst0) => evalCode (fuel + 1) (venv.bind (st1.freshVar .i64).1 tv) hst0
                (.letBind (st2.freshVar .unit).1 .unit
                  (.call "lean_native_ctor_set_tag" [objVid, (st1.freshVar .i64).1] .unit false) pk.1)
            | .error e => .error e) = .ok (v, hst')
          dsimp only [evalExpr, evalScalarExpr]
          dsimp only [evalCode]; rw [hcall]; exact hkEval
      | _ => exact nomatch h_eval
    · exact nomatch h_lower

private theorem lowerLetNonScalarCtor_sound (fuel : Nat) (ctx : RealBridgeCtx)
    (ih : ∀ (st st' : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
      (target : Lean.Compiler.LCNF.Code .impure ⊕
        (VarId × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure)))
      (code : LNIRCode),
      BridgeStateInv st lenv venv →
      lowerImpureStepPure fuel ctx st target = .ok (code, st') →
      (match target with
       | .inl c => evalStep fuel ctx lenv hst (.inl c) = .ok (v, hst')
       | .inr (condVar, isBool, idx, discr?, alts) =>
         condVar < st.nextVarId ∧
         (∀ dx, discr? = some dx → (st.lookupFVar? dx).isSome = true) ∧
         (lnirTypeEq (st.getVarType condVar) .i1 = true → isBool = true) ∧
         ∃ cond, venv condVar = some cond ∧
           evalStep fuel ctx lenv hst (.inr (cond, isBool, idx, discr?, alts)) = .ok (v, hst')) →
      evalCode fuel venv hst code = .ok (v, hst'))
    (st st' : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
    (decl : Lean.Compiler.LCNF.LetDecl .impure) (k : Lean.Compiler.LCNF.Code .impure) (code : LNIRCode)
    (hinv : BridgeStateInv st lenv venv)
    (hnoScCtor : ∀ info args h, decl.value = .ctor info args h →
      (ctx.allowStage1DHeap && (info.usize > 0 || info.ssize > 0)) = false)
    (h_lower : (do
      let rawDeclTy := lowerGroundImpureTypeWith ctx decl.type
      let (rhs, st1) ← lowerImpureLetValuePure ctx st decl.value rawDeclTy
      let isBox := match decl.value with | .box _ _ _ => true | _ => false
      let ty := inferImpureRhsTypePure st1 rhs rawDeclTy isBox
      let (dst, st2) := st1.allocFreshFVar decl.fvarId ty
      let st2' := match decl.value with
        | .ctor info _ _ => if lnirTypeEq ty .objPtr then st2.setActiveCtor dst info.name else st2
        | _ => st2
      match rhs with
      | .isExclusive _ =>
        let (exclVar, st3) := st2'.freshVar .i1
        let (kCode, st4) ← lowerImpureStepPure fuel ctx st3 (.inl k)
        return (.letBind exclVar .i1 rhs (.letBind dst .i1 (.scalar (.unaryOp .not (.var exclVar))) kCode), st4)
      | _ =>
        let (kCode, st3) ← lowerImpureStepPure fuel ctx st2' (.inl k)
        return (.letBind dst ty rhs kCode, st3) : Except String (LNIRCode × RealBridgeState)) = .ok (code, st'))
    (h_eval : evalStep (fuel + 1) ctx lenv hst (.inl (.let decl k)) = .ok (v, hst')) :
    evalCode (fuel + 1) venv hst code = .ok (v, hst') := by
  dsimp only [evalStep] at h_eval
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
  let rawDeclTy := lowerGroundImpureTypeWith ctx decl.type
  cases hl : lowerImpureLetValuePure ctx st decl.value rawDeclTy with
  | error _ => rw [hl] at h_lower; exact nomatch h_lower
  | ok pl =>
    rw [hl] at h_lower; rcases pl with ⟨rhs, st1⟩
    cases hev : evalLetValue ctx lenv hst decl.value rawDeclTy with
    | error _ => rw [hev] at h_eval; exact nomatch h_eval
    | ok pev =>
      rw [hev] at h_eval; rcases pev with ⟨val, hst1, ctor?⟩; dsimp only at h_eval h_lower
      have hst1Eq := lowerImpureLetValuePure_st_eq ctx st st1 decl.value rawDeclTy rhs hl
      subst st1
      rcases lowerImpureLetValuePure_sound ctx st lenv venv hst hst1 decl.value rawDeclTy rhs st val ctor?
          hnoScCtor hinv hl hev with ⟨_, hrhsEval, htyEq, hctorEq⟩
      let ty := inferImpureRhsTypePure st rhs rawDeclTy
        (match decl.value with | .box _ _ _ => true | _ => false)
      have hEvalK : evalStep fuel ctx
          (lenv.bind decl.fvarId val
            (match decl.value with | .ctor _ _ _ => if lnirTypeEq ty .objPtr then ctor? else none | _ => none)
            (some ty))
          hst1 (.inl k) = .ok (v, hst') := by
        have htyEq' : ty = _ := htyEq
        have hEqEnv :
            lenv.bind decl.fvarId val
              (match decl.value with
               | .ctor _ _ _ => if lnirTypeEq ty .objPtr then ctor? else none
               | _ => none)
              (some ty) = _ :=
          congrArg (fun t =>
            lenv.bind decl.fvarId val
              (match decl.value with
               | .ctor _ _ _ => if lnirTypeEq t .objPtr then ctor? else none
               | _ => none)
              (some t)) htyEq'
        rw [hEqEnv]; exact h_eval
      let st2 := (st.allocFreshFVar decl.fvarId ty).2
      let dst := (st.allocFreshFVar decl.fvarId ty).1
      have hinv2 : BridgeStateInv st2 (lenv.bind decl.fvarId val none (some ty)) (venv.bind dst val) :=
        bridgeInv_bind_fresh st lenv venv decl.fvarId ty val hinv
      let st2' := match decl.value with
        | .ctor info _ _ => if lnirTypeEq ty .objPtr then st2.setActiveCtor dst info.name else st2
        | _ => st2
      let storedCtor := match decl.value with
        | .ctor _ _ _ => if lnirTypeEq ty .objPtr then ctor? else none
        | _ => none
      have hinv2' : BridgeStateInv st2' (lenv.bind decl.fvarId val storedCtor (some ty)) (venv.bind dst val) := by
        dsimp only [st2', storedCtor]
        cases hdv : decl.value with
        | ctor info args hh =>
          dsimp only
          cases hobj : lnirTypeEq ty .objPtr
          · simp only [Bool.false_eq_true, ↓reduceIte]; exact hinv2
          · simp only [↓reduceIte]
            have hct : ctor? = some info.name := by
              apply hctorEq info args hh hdv
              dsimp only [ty] at hobj; rw [hdv] at hobj; exact hobj
            rw [hct, ← lenv_bind_withCtor]
            have hluDst : st2.lookupFVar? decl.fvarId = some dst := by
              dsimp only [st2, dst]; rw [lookupFVar_allocFresh, beq_self_eq_true]; rfl
            exact bridgeInv_setActiveCtor st2 (lenv.bind decl.fvarId val none (some ty))
              (venv.bind dst val) dst info.name decl.fvarId hinv2 hluDst
        | _ => exact hinv2
      have hst2Next : st2'.nextVarId = st.nextVarId + 1 := by
        dsimp only [st2']; cases decl.value <;> try rfl
        cases lnirTypeEq ty .objPtr <;> rfl
      clear hl htyEq hctorEq
      cases rhs with
      | isExclusive objVar =>
        dsimp only at h_lower hrhsEval
        rcases hrhsEval with ⟨b, hexclEval, rfl⟩
        split at h_lower
        · exact nomatch h_lower
        · rename_i pk hk
          injection h_lower with hp; rcases Prod.mk.inj hp with ⟨hcodeEq, _⟩
          have hkClean : lowerImpureStepPure fuel ctx (st2'.freshVar .i1).2 (.inl k) = .ok pk := hk
          have hexclId : (st2'.freshVar .i1).1 = st2'.nextVarId := (freshVar_spec st2' .i1).1
          have hne : st2'.nextVarId ≠ dst := by
            change st2'.nextVarId ≠ st.nextVarId
            rw [hst2Next]; exact Nat.ne_of_gt (Nat.lt_succ_self _)
          have hinv3 : BridgeStateInv (st2'.freshVar .i1).2
              (lenv.bind decl.fvarId (.bool (!b)) storedCtor (some ty))
              ((venv.bind (st2'.freshVar .i1).1 (.bool b)).bind dst (.bool (!b))) := by
            rw [hexclId, varEnv_bind_comm venv st2'.nextVarId dst (.bool b) (.bool (!b)) hne, ← hexclId]
            exact bridgeInv_freshVar st2' _ (venv.bind dst (.bool (!b))) .i1 (.bool b) hinv2'
          have hkEval := evalCode_fuel_mono_step fuel pk.1 _ hst1 v hst'
            (ih (st2'.freshVar .i1).2 pk.2 _ _ hst1 hst' v (.inl k) pk.1 hinv3 hkClean hEvalK)
          rw [← hcodeEq]
          dsimp only [evalCode]; rw [hexclEval]
          dsimp only [evalCode, evalExpr, evalScalarExpr]
          rw [VarEnv.bind_self]; dsimp only [evalUnaryOp]
          exact hkEval
      | _ =>
        dsimp only at h_lower hrhsEval
        split at h_lower
        · exact nomatch h_lower
        · rename_i pk hk
          injection h_lower with hp; rcases Prod.mk.inj hp with ⟨hcodeEq, _⟩
          have hkClean : lowerImpureStepPure fuel ctx st2' (.inl k) = .ok pk := hk
          have hkEval := evalCode_fuel_mono_step fuel pk.1 (venv.bind dst val) hst1 v hst'
            (ih st2' pk.2 _ (venv.bind dst val) hst1 hst' v (.inl k) pk.1 hinv2' hkClean hEvalK)
          rw [← hcodeEq]; dsimp only [evalCode]
          rw [hrhsEval]; exact hkEval

theorem lowerLetStep_sound (fuel : Nat) (ctx : RealBridgeCtx)
    (ih : ∀ (st st' : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
      (target : Lean.Compiler.LCNF.Code .impure ⊕
        (VarId × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure)))
      (code : LNIRCode),
      BridgeStateInv st lenv venv →
      lowerImpureStepPure fuel ctx st target = .ok (code, st') →
      (match target with
       | .inl c => evalStep fuel ctx lenv hst (.inl c) = .ok (v, hst')
       | .inr (condVar, isBool, idx, discr?, alts) =>
         condVar < st.nextVarId ∧
         (∀ dx, discr? = some dx → (st.lookupFVar? dx).isSome = true) ∧
         (lnirTypeEq (st.getVarType condVar) .i1 = true → isBool = true) ∧
         ∃ cond, venv condVar = some cond ∧
           evalStep fuel ctx lenv hst (.inr (cond, isBool, idx, discr?, alts)) = .ok (v, hst')) →
      evalCode fuel venv hst code = .ok (v, hst'))
    (st st' : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
    (decl : Lean.Compiler.LCNF.LetDecl .impure) (k : Lean.Compiler.LCNF.Code .impure) (code : LNIRCode)
    (hinv : BridgeStateInv st lenv venv)
    (h_lower : lowerImpureStepPure (fuel + 1) ctx st (.inl (.let decl k)) = .ok (code, st'))
    (h_eval : evalStep (fuel + 1) ctx lenv hst (.inl (.let decl k)) = .ok (v, hst')) :
    evalCode (fuel + 1) venv hst code = .ok (v, hst') := by
  dsimp only [lowerImpureStepPure] at h_lower
  rcases decl with ⟨fvarId, binderName, declTy, lv⟩
  cases hlv : lv with
  | ctor info args himp =>
    subst hlv; dsimp only at h_lower
    cases hsc : (ctx.allowStage1DHeap && (info.usize > 0 || info.ssize > 0))
    · rw [hsc] at h_lower; simp only [Bool.false_eq_true, ↓reduceIte] at h_lower
      apply lowerLetNonScalarCtor_sound fuel ctx ih st st' lenv venv hst hst' v
        ⟨fvarId, binderName, declTy, .ctor info args himp⟩ k code hinv
        (fun _ _ _ h => by cases h; exact hsc) _ h_eval
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower ⊢
      cases hl : lowerImpureLetValuePure ctx st (.ctor info args himp) (lowerGroundImpureTypeWith ctx declTy)
      · rw [hl] at h_lower; exact nomatch h_lower
      · rename_i pl; rw [hl] at h_lower; dsimp only at h_lower ⊢
        have h_eval0 : evalStep (fuel + 1) ctx lenv hst
            (.inl (.let ⟨fvarId, binderName, declTy, .ctor info args himp⟩ k)) = .ok (v, hst') := h_eval
        dsimp only [evalStep] at h_eval0
        cases hev : evalLetValue ctx lenv hst (.ctor info args himp) (lowerGroundImpureTypeWith ctx declTy)
        · rw [hev] at h_eval0; exact nomatch h_eval0
        · rename_i pev
          have hnotEx : ∀ u, pl.1 ≠ .isExclusive u := by
            intro u hex
            dsimp only [lowerImpureLetValuePure] at hl
            dsimp only [evalLetValue] at hev
            rw [hsc] at hev; simp only [Bool.false_eq_true, ↓reduceIte] at hev
            rcases lowerRealCtor_sound ctx st lenv venv info.name info.cidx args.toList
                (lowerGroundImpureTypeWith ctx declTy) pl.1 pl.2 pev.1 hst pev.2.1 pev.2.2 hinv hl hev with
              ⟨_, _, hempC, hneC⟩
            cases hb : args.toList.isEmpty
            · rcases hneC hb with ⟨_, he, _⟩ | ⟨_, _, _, _, he, _⟩ <;> (rw [hex] at he; exact nomatch he)
            · rcases hempC hb with ⟨⟨_, he, _⟩, _⟩; rw [hex] at he; exact nomatch he
          rcases pl with ⟨rhs, st1⟩; dsimp only at h_lower hnotEx ⊢
          cases hrhs : rhs
          all_goals (try exact False.elim (hnotEx _ hrhs))
          all_goals (rw [hrhs] at h_lower; exact h_lower)
    · rw [hsc] at h_lower; simp only [↓reduceIte] at h_lower
      exact lowerScalarSlotCtor_sound fuel ctx ih st st' lenv venv hst hst' v
        fvarId declTy info args himp k code hinv hsc h_lower h_eval
  | fap fnName args himp =>
    subst hlv; dsimp only at h_lower
    cases hloc : ctx.findLocalCallee? fnName with
    | some sym =>
      dsimp only [evalStep, evalLetValue] at h_eval
      rw [hloc] at h_eval; simp only [Option.isSome, ↓reduceIte] at h_eval
      exact nomatch h_eval
    | none =>
      rw [hloc] at h_lower; dsimp only at h_lower
      apply lowerLetNonScalarCtor_sound fuel ctx ih st st' lenv venv hst hst' v
        ⟨fvarId, binderName, declTy, .fap fnName args himp⟩ k code hinv
        (fun _ _ _ h => nomatch h) _ h_eval
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower ⊢
      cases hl : lowerImpureLetValuePure ctx st (.fap fnName args himp) (lowerGroundImpureTypeWith ctx declTy)
      · rw [hl] at h_lower; exact nomatch h_lower
      · rename_i pl; rw [hl] at h_lower; dsimp only at h_lower ⊢
        have h_eval0 : evalStep (fuel + 1) ctx lenv hst
            (.inl (.let ⟨fvarId, binderName, declTy, .fap fnName args himp⟩ k)) = .ok (v, hst') := h_eval
        dsimp only [evalStep] at h_eval0
        cases hev : evalLetValue ctx lenv hst (.fap fnName args himp) (lowerGroundImpureTypeWith ctx declTy)
        · rw [hev] at h_eval0; exact nomatch h_eval0
        · rename_i pev
          have hnotEx : ∀ u, pl.1 ≠ .isExclusive u := by
            intro u hex
            have hl0 := hl
            dsimp only [lowerImpureLetValuePure, Bind.bind, Except.bind] at hl0
            cases ha : lowerRealArgList ctx st false args.toList
            · rw [ha] at hl0; exact nomatch hl0
            · rename_i pa; rw [ha] at hl0; dsimp only at hl0
              cases hi : lowerCanonicalIntrinsicPure? fnName pa.1 (lowerGroundImpureTypeWith ctx declTy)
                  (pa.1.map pa.2.getVarType) (ctx.findLocalCallee? fnName).isSome ctx.arch ctx.gfSimdIntrinsics
              · rw [hi] at hl0; exact nomatch hl0
              · rename_i e0; rw [hi] at hl0
                injection hl0 with hp; rcases Prod.mk.inj hp with ⟨he0, _⟩
                rcases lowerCanonicalIntrinsicPure_sound ctx st lenv venv hst pev.2.1 fnName args himp
                    pa.1 pa.2 (lowerGroundImpureTypeWith ctx declTy) e0 pev.1 pev.2.2 hinv ha hi hev with
                  ⟨_, _, _, _, se, hse, _⟩
                rw [he0, hex] at hse; exact nomatch hse
          rcases pl with ⟨rhs, st1⟩; dsimp only at h_lower hnotEx ⊢
          cases hrhs : rhs
          all_goals (try exact False.elim (hnotEx _ hrhs))
          all_goals (rw [hrhs] at h_lower; exact h_lower)
  | _ =>
    subst hlv
    exact lowerLetNonScalarCtor_sound fuel ctx ih st st' lenv venv hst hst' v
      ⟨fvarId, binderName, declTy, _⟩ k code hinv
      (fun _ _ _ h => by cases h) h_lower h_eval

end LeanNative.Proofs
