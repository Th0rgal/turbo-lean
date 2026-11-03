import LeanNative.Proofs.RealLCNFBridge.JpTag

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

theorem lowerStepInr_sound (fuel : Nat) (ctx : RealBridgeCtx)
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
    (condVar : VarId) (isBool : Bool) (idx : Nat) (discr? : Option Lean.FVarId)
    (alts : List (Lean.Compiler.LCNF.Alt .impure)) (code : LNIRCode) (cond : Val)
    (hinv : BridgeStateInv st lenv venv)
    (h_lower : lowerImpureStepPure (fuel + 1) ctx st (.inr (condVar, isBool, idx, discr?, alts)) = .ok (code, st'))
    (hcondLt : condVar < st.nextVarId)
    (hdiscr : ∀ dx, discr? = some dx → (st.lookupFVar? dx).isSome = true)
    (hi1 : lnirTypeEq (st.getVarType condVar) .i1 = true → isBool = true)
    (hcondV : venv condVar = some cond)
    (h_eval : evalStep (fuel + 1) ctx lenv hst (.inr (cond, isBool, idx, discr?, alts)) = .ok (v, hst')) :
    evalCode (fuel + 1) venv hst code = .ok (v, hst') := by
  dsimp only [lowerImpureStepPure] at h_lower
  dsimp only [evalStep] at h_eval
  cases alts with
  | nil => exact nomatch h_eval
  | cons alt rest =>
    cases rest with
    | nil =>
      cases alt with
      | alt cn ps c _ =>
        dsimp only at h_lower h_eval
        cases hemp : (!ps.isEmpty) <;> simp only [hemp, ↓reduceIte, Bool.false_eq_true] at h_lower
        · exact evalCode_fuel_mono_step fuel code venv hst v hst'
            (ih st st' lenv venv hst hst' v (.inl c) code hinv h_lower h_eval)
        · exact nomatch h_lower
      | ctorAlt info c _ =>
        dsimp only at h_lower h_eval
        rcases discr_env_inv st lenv venv discr? info.name hinv hdiscr with ⟨hinvIn, _⟩
        change (match lowerImpureStepPure fuel ctx
            (match discr?.bind st.lookupFVar? with
             | some dv => st.setActiveCtor dv info.name | none => st)
            (.inl c) with
          | Except.ok (c0, stOut) =>
            Except.ok (c0, ({ stOut with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls } : RealBridgeState))
          | Except.error e => Except.error e) = Except.ok (code, st') at h_lower
        cases hc : lowerImpureStepPure fuel ctx
            (match discr?.bind st.lookupFVar? with
             | some dv => st.setActiveCtor dv info.name | none => st)
            (.inl c) with
        | error _ => rw [hc] at h_lower; exact nomatch h_lower
        | ok pr =>
          rw [hc] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
          exact evalCode_fuel_mono_step fuel pr.1 venv hst v hst'
            (ih _ pr.2 _ venv hst hst' v (.inl c) pr.1 hinvIn hc h_eval)
      | default c =>
        exact evalCode_fuel_mono_step fuel code venv hst v hst'
          (ih st st' lenv venv hst hst' v (.inl c) code hinv h_lower h_eval)
    | cons alt2 rest2 =>
      cases alt with
      | default c =>
        exact evalCode_fuel_mono_step fuel code venv hst v hst'
          (ih st st' lenv venv hst hst' v (.inl c) code hinv h_lower h_eval)
      | ctorAlt info c _ =>
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
        dsimp only at h_eval
        rcases discr_env_inv st lenv venv discr? info.name hinv hdiscr with ⟨hinvIn, hnextIn, htyIn⟩
        cases hD : discr?.bind st.lookupFVar? with
        | none =>
          rw [hD] at h_lower hinvIn hnextIn htyIn; dsimp only at h_lower hinvIn hnextIn htyIn
          cases h1 : lowerImpureStepPure fuel ctx st (.inl c) with
          | error _ => rw [h1] at h_lower; exact nomatch h_lower
          | ok p1 =>
            rw [h1] at h_lower; rcases p1 with ⟨yesCode, st1⟩; dsimp only at h_lower
            rcases lowerImpureStepPure_mono fuel ctx st st1 (.inl c) yesCode h1 with ⟨hn1, ht1⟩
            have hinv1R : BridgeStateInv
                { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                lenv venv :=
              bridgeInv_ext st _ lenv venv hinv hn1 (fun u hu => ht1 u hu) rfl (fun _ _ => rfl) rfl
            cases h2 : lowerImpureStepPure fuel ctx
                { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                (.inr (condVar, isBool, idx + 1, discr?, alt2 :: rest2)) with
            | error _ => rw [h2] at h_lower; exact nomatch h_lower
            | ok p2 =>
              rw [h2] at h_lower; rcases p2 with ⟨noCode, st2⟩; dsimp only at h_lower
              rcases lowerImpureStepPure_mono fuel ctx
                  { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                  st2 (.inr (condVar, isBool, idx + 1, discr?, alt2 :: rest2)) noCode h2 with ⟨hn2, _⟩
              have hgeBase : st.nextVarId ≤ st2.nextVarId := Nat.le_trans hn1 hn2
              have hyes : ∀ venvY, (∀ u, u < st2.nextVarId → venvY u = venv u) →
                  evalStep fuel ctx
                    (match discr? with
                     | some dx => if (lenv.vals dx).isSome then lenv.withCtor dx info.name else lenv
                     | none => lenv)
                    hst (.inl c) = .ok (v, hst') →
                  evalCode (fuel + 1) venvY hst yesCode = .ok (v, hst') := by
                intro venvY hge hev
                exact evalCode_fuel_mono_step fuel yesCode venvY hst v hst'
                  (ih st st1 _ venvY hst hst' v (.inl c) yesCode
                    (bridgeInv_venv_agree st _ venv venvY hinvIn
                      (fun u hu => hge u (Nat.lt_of_lt_of_le hu hgeBase))) h1 hev)
              have hno : ∀ venvN, (∀ u, u < st2.nextVarId → venvN u = venv u) →
                  evalStep fuel ctx lenv hst (.inr (cond, isBool, idx + 1, discr?, alt2 :: rest2)) =
                    .ok (v, hst') →
                  evalCode (fuel + 1) venvN hst noCode = .ok (v, hst') := by
                intro venvN hge hev
                exact evalCode_fuel_mono_step fuel noCode venvN hst v hst'
                  (ih { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                    st2 lenv venvN hst hst' v
                    (.inr (condVar, isBool, idx + 1, discr?, alt2 :: rest2)) noCode
                    (bridgeInv_venv_agree _ lenv venv venvN hinv1R
                      (fun u hu => hge u (Nat.lt_of_lt_of_le hu hn2))) h2
                    ⟨Nat.lt_of_lt_of_le hcondLt hn1, fun dx hdx => by
                      have := hdiscr dx hdx
                      change (st.lookupFVar? dx).isSome = true at this
                      simp only [RealBridgeState.lookupFVar?]; exact this,
                     fun h => hi1 (by
                       have hty1R : st1.getVarType condVar = st.getVarType condVar := ht1 condVar hcondLt
                       change lnirTypeEq (st1.getVarType condVar) .i1 = true at h
                       rw [hty1R] at h; exact h),
                     cond, by rw [hge condVar (Nat.lt_of_lt_of_le hcondLt hgeBase)]; exact hcondV, hev⟩)
              exact tag_branch_sound fuel ctx lenv
                (match discr? with
                 | some dx => if (lenv.vals dx).isSome then lenv.withCtor dx info.name else lenv
                 | none => lenv)
                venv hst hst' v cond condVar
                (st.getVarType condVar) info.cidx isBool idx discr? (alt2 :: rest2) c
                yesCode noCode code st2 st' hi1 hcondV hyes hno h_lower h_eval
        | some dv =>
          rw [hD] at h_lower hinvIn hnextIn htyIn; dsimp only at h_lower hinvIn hnextIn htyIn
          let stIn := st.setActiveCtor dv info.name
          cases h1 : lowerImpureStepPure fuel ctx stIn (.inl c) with
          | error _ => rw [h1] at h_lower; exact nomatch h_lower
          | ok p1 =>
            rw [h1] at h_lower; rcases p1 with ⟨yesCode, st1⟩; dsimp only at h_lower
            rcases lowerImpureStepPure_mono fuel ctx stIn st1 (.inl c) yesCode h1 with ⟨hn1, ht1⟩
            have hbase1 : st.nextVarId ≤ st1.nextVarId := hn1
            have hinv1R : BridgeStateInv
                { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                lenv venv :=
              bridgeInv_ext st _ lenv venv hinv hbase1
                (fun u hu => ht1 u hu) rfl (fun _ _ => rfl) rfl
            cases h2 : lowerImpureStepPure fuel ctx
                { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                (.inr (condVar, isBool, idx + 1, discr?, alt2 :: rest2)) with
            | error _ => rw [h2] at h_lower; exact nomatch h_lower
            | ok p2 =>
              rw [h2] at h_lower; rcases p2 with ⟨noCode, st2⟩; dsimp only at h_lower
              rcases lowerImpureStepPure_mono fuel ctx
                  { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                  st2 (.inr (condVar, isBool, idx + 1, discr?, alt2 :: rest2)) noCode h2 with ⟨hn2, _⟩
              have hgeBase : st.nextVarId ≤ st2.nextVarId := Nat.le_trans hbase1 hn2
              have hyes : ∀ venvY, (∀ u, u < st2.nextVarId → venvY u = venv u) →
                  evalStep fuel ctx
                    (match discr? with
                     | some dx => if (lenv.vals dx).isSome then lenv.withCtor dx info.name else lenv
                     | none => lenv)
                    hst (.inl c) = .ok (v, hst') →
                  evalCode (fuel + 1) venvY hst yesCode = .ok (v, hst') := by
                intro venvY hge hev
                exact evalCode_fuel_mono_step fuel yesCode venvY hst v hst'
                  (ih stIn st1 _ venvY hst hst' v (.inl c) yesCode
                    (bridgeInv_venv_agree stIn _ venv venvY hinvIn
                      (fun u hu => hge u (Nat.lt_of_lt_of_le hu hgeBase))) h1 hev)
              have hno : ∀ venvN, (∀ u, u < st2.nextVarId → venvN u = venv u) →
                  evalStep fuel ctx lenv hst (.inr (cond, isBool, idx + 1, discr?, alt2 :: rest2)) =
                    .ok (v, hst') →
                  evalCode (fuel + 1) venvN hst noCode = .ok (v, hst') := by
                intro venvN hge hev
                exact evalCode_fuel_mono_step fuel noCode venvN hst v hst'
                  (ih { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                    st2 lenv venvN hst hst' v
                    (.inr (condVar, isBool, idx + 1, discr?, alt2 :: rest2)) noCode
                    (bridgeInv_venv_agree _ lenv venv venvN hinv1R
                      (fun u hu => hge u (Nat.lt_of_lt_of_le hu hn2))) h2
                    ⟨Nat.lt_of_lt_of_le hcondLt hbase1, fun dx hdx => by
                      have := hdiscr dx hdx
                      change (st.lookupFVar? dx).isSome = true at this
                      simp only [RealBridgeState.lookupFVar?]; exact this,
                     fun h => hi1 (by
                       have hty1R : st1.getVarType condVar = st.getVarType condVar := ht1 condVar hcondLt
                       change lnirTypeEq (st1.getVarType condVar) .i1 = true at h
                       rw [hty1R] at h; exact h),
                     cond, by rw [hge condVar (Nat.lt_of_lt_of_le hcondLt hgeBase)]; exact hcondV, hev⟩)
              exact tag_branch_sound fuel ctx lenv
                (match discr? with
                 | some dx => if (lenv.vals dx).isSome then lenv.withCtor dx info.name else lenv
                 | none => lenv)
                venv hst hst' v cond condVar
                (st.getVarType condVar) info.cidx isBool idx discr? (alt2 :: rest2) c
                yesCode noCode code st2 st' hi1 hcondV hyes hno h_lower h_eval
      | alt ctorName params c _ =>
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw,
          MonadExceptOf.throw, throwThe] at h_lower
        dsimp only at h_eval
        cases hemp : (!params.isEmpty) <;> simp only [hemp, ↓reduceIte, Bool.false_eq_true] at h_lower
        · cases h1 : lowerImpureStepPure fuel ctx st (.inl c) with
          | error _ => rw [h1] at h_lower; exact nomatch h_lower
          | ok p1 =>
            rw [h1] at h_lower; rcases p1 with ⟨yesCode, st1⟩; dsimp only at h_lower
            rcases lowerImpureStepPure_mono fuel ctx st st1 (.inl c) yesCode h1 with ⟨hn1, ht1⟩
            have hinv1R : BridgeStateInv
                { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                lenv venv :=
              bridgeInv_ext st _ lenv venv hinv hn1
                (fun u hu => by change st1.getVarType u = st.getVarType u; exact ht1 u hu) rfl
                (fun _ _ => rfl) rfl
            cases h2 : lowerImpureStepPure fuel ctx
                { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                (.inr (condVar, isBool, idx + 1, discr?, alt2 :: rest2)) with
            | error _ => rw [h2] at h_lower; exact nomatch h_lower
            | ok p2 =>
              rw [h2] at h_lower; rcases p2 with ⟨noCode, st2⟩; dsimp only at h_lower
              rcases lowerImpureStepPure_mono fuel ctx
                  { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                  st2 (.inr (condVar, isBool, idx + 1, discr?, alt2 :: rest2)) noCode h2 with ⟨hn2, ht2⟩
              have hcondLt2 : condVar < st2.nextVarId := Nat.lt_of_lt_of_le hcondLt (Nat.le_trans hn1 hn2)
              have hgeBase : st.nextVarId ≤ st2.nextVarId := Nat.le_trans hn1 hn2
              have hyes : ∀ venvY, (∀ u, u < st2.nextVarId → venvY u = venv u) →
                  evalStep fuel ctx lenv hst (.inl c) = .ok (v, hst') →
                  evalCode (fuel + 1) venvY hst yesCode = .ok (v, hst') := by
                intro venvY hge hev
                exact evalCode_fuel_mono_step fuel yesCode venvY hst v hst'
                  (ih st st1 lenv venvY hst hst' v (.inl c) yesCode
                    (bridgeInv_venv_agree st lenv venv venvY hinv
                      (fun u hu => hge u (Nat.lt_of_lt_of_le hu hgeBase))) h1 hev)
              have hno : ∀ venvN, (∀ u, u < st2.nextVarId → venvN u = venv u) →
                  evalStep fuel ctx lenv hst (.inr (cond, isBool, idx + 1, discr?, alt2 :: rest2)) =
                    .ok (v, hst') →
                  evalCode (fuel + 1) venvN hst noCode = .ok (v, hst') := by
                intro venvN hge hev
                exact evalCode_fuel_mono_step fuel noCode venvN hst v hst'
                  (ih { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                    st2 lenv venvN hst hst' v
                    (.inr (condVar, isBool, idx + 1, discr?, alt2 :: rest2)) noCode
                    (bridgeInv_venv_agree _ lenv venv venvN hinv1R
                      (fun u hu => hge u (Nat.lt_of_lt_of_le hu hn2))) h2
                    ⟨Nat.lt_of_lt_of_le hcondLt hn1, fun dx hdx => by
                      have := hdiscr dx hdx
                      change (st.lookupFVar? dx).isSome = true at this
                      simp only [RealBridgeState.lookupFVar?]; exact this,
                     fun h => hi1 (by
                       have hty1R : st1.getVarType condVar = st.getVarType condVar := ht1 condVar hcondLt
                       change lnirTypeEq (st1.getVarType condVar) .i1 = true at h
                       rw [hty1R] at h; exact h),
                     cond, by rw [hge condVar (Nat.lt_of_lt_of_le hcondLt hgeBase)]; exact hcondV, hev⟩)
              exact tag_branch_sound fuel ctx lenv lenv venv hst hst' v cond condVar
                (st.getVarType condVar) ((ctx.findNullaryCtor? ctorName).getD idx) isBool idx discr?
                (alt2 :: rest2) c yesCode noCode code st2 st' hi1 hcondV hyes hno
                h_lower h_eval
        · exact nomatch h_lower

theorem evalCtorWriteStep_sound (fuel : Nat) (st : RealBridgeState) (venv : VarEnv)
    (hst hst1 hst' : HeapState) (v : Val) (objVid valVid : VarId) (objId : Nat)
    (slot : Nat) (yVal : Val) (isObj : Bool) (kCode : LNIRCode)
    (hobjLt : objVid < st.nextVarId) (hvalLt : valVid < st.nextVarId)
    (hvalV : venv objVid = some (.objPtr objId)) (hyValV : venv valVid = some yVal)
    (hwf : writeField hst objId (slot.toUInt64).toNat yVal isObj = .ok hst1)
    (hkEval : evalCode (fuel + 1)
      ((venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64)).bind ((st.freshVar .i64).2.freshVar .unit).1 .unit)
      hst1 kCode = .ok (v, hst')) :
    evalCode (fuel + 1) venv hst
      (.letBind (st.freshVar .i64).1 .i64 (.scalar (.constU64 slot.toUInt64))
        (.letBind ((st.freshVar .i64).2.freshVar .unit).1 .unit
          (.call (if isObj then "lean_native_ctor_set" else "lean_native_ctor_set_scalar")
            [objVid, (st.freshVar .i64).1, valVid] .unit false) kCode)) =
      .ok (v, hst') := by
  have hidxId : (st.freshVar .i64).1 = st.nextVarId := (freshVar_spec st .i64).1
  let venv1 := venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64)
  have hobjV1 : venv1 objVid = some (.objPtr objId) := by
    dsimp only [venv1]
    rw [hidxId, venv_bind_fresh venv st.nextVarId objVid hobjLt]
    exact hvalV
  have hvalV1 : venv1 valVid = some yVal := by
    dsimp only [venv1]
    rw [hidxId, venv_bind_fresh venv st.nextVarId valVid hvalLt]
    exact hyValV
  have hidxV1 : venv1 (st.freshVar .i64).1 = some (.u64 slot.toUInt64) :=
    VarEnv.bind_self _ _ _
  have hvl : evalVarList venv1 [objVid, (st.freshVar .i64).1, valVid] =
      .ok [.objPtr objId, .u64 slot.toUInt64, yVal] := by
    simp only [evalVarList, hobjV1, hidxV1, hvalV1]
  have hcall : evalExpr venv1 hst
      (.call (if isObj then "lean_native_ctor_set" else "lean_native_ctor_set_scalar")
        [objVid, (st.freshVar .i64).1, valVid] .unit false) = .ok (.unit, hst1) := by
    cases isObj
    · dsimp only [Bool.false_eq_true, ↓reduceIte, evalExpr]
      rw [hvl]
      change (hst.writeHeapObjFieldExclusive objId (slot.toUInt64).toNat yVal false).map (Val.unit, ·) =
        .ok (Val.unit, hst1)
      unfold writeField at hwf
      rw [hwf]; rfl
    · dsimp only [↓reduceIte, evalExpr]
      rw [hvl]
      change (hst.writeHeapObjFieldExclusive objId (slot.toUInt64).toNat yVal true).map (Val.unit, ·) =
        .ok (Val.unit, hst1)
      unfold writeField at hwf
      rw [hwf]; rfl
  change (match evalExpr venv hst (.scalar (.constU64 slot.toUInt64)) with
    | .ok (iv, hst0) => evalCode (fuel + 1) (venv.bind (st.freshVar .i64).1 iv) hst0
        (.letBind ((st.freshVar .i64).2.freshVar .unit).1 .unit
          (.call (if isObj then "lean_native_ctor_set" else "lean_native_ctor_set_scalar")
            [objVid, (st.freshVar .i64).1, valVid] .unit false) kCode)
    | .error e => .error e) = .ok (v, hst')
  dsimp only [evalExpr, evalScalarExpr]
  dsimp only [evalCode]
  change (match evalExpr venv1 hst
      (.call (if isObj then "lean_native_ctor_set" else "lean_native_ctor_set_scalar")
        [objVid, (st.freshVar .i64).1, valVid] .unit false) with
    | .ok (u, hst0) => evalCode (fuel + 1) (venv1.bind ((st.freshVar .i64).2.freshVar .unit).1 u) hst0 kCode
    | .error e => .error e) = .ok (v, hst')
  rw [hcall]
  exact hkEval

end LeanNative.Proofs
