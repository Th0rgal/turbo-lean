import LeanNative.Proofs.RealLCNFBridge.StateInv

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

theorem lowerImpureStepPure_mono (fuel : Nat) (ctx : RealBridgeCtx) (st st' : RealBridgeState)
    (target : Lean.Compiler.LCNF.Code .impure ⊕
      (VarId × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure)))
    (code : LNIRCode)
    (h : lowerImpureStepPure fuel ctx st target = .ok (code, st')) :
    st.nextVarId ≤ st'.nextVarId ∧
    (∀ u, u < st.nextVarId → st'.getVarType u = st.getVarType u) := by
  induction fuel generalizing st st' target code with
  | zero => exact nomatch h
  | succ fuel ih =>
    dsimp only [lowerImpureStepPure] at h
    cases target with
    | inr t =>
      rcases t with ⟨condVar, isBool, idx, discr?, alts⟩
      cases alts with
      | nil => injection h with hp; rcases Prod.mk.inj hp with ⟨_, rfl⟩; exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
      | cons alt rest =>
        cases rest with
        | nil =>
          cases alt with
          | alt cn ps c _ =>
            dsimp only at h
            cases hemp : (!ps.isEmpty) <;> simp only [hemp, ↓reduceIte, Bool.false_eq_true] at h
            · exact ih st st' (.inl c) code h
            · exact nomatch h
          | ctorAlt info c _ =>
            dsimp only at h
            let stIn := match discr? >>= st.lookupFVar? with | some dv => st.setActiveCtor dv info.name | none => st
            have hstIn : stIn.nextVarId = st.nextVarId ∧ ∀ u, stIn.getVarType u = st.getVarType u := by
              dsimp only [stIn]; cases (discr? >>= st.lookupFVar?) <;> exact ⟨rfl, fun _ => rfl⟩
            cases hc : lowerImpureStepPure fuel ctx stIn (.inl c) with
            | error _ =>
              change (match lowerImpureStepPure fuel ctx stIn (.inl c) with
                | Except.ok (c0, stOut) =>
                  Except.ok (c0, { stOut with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls })
                | Except.error e => Except.error e) = Except.ok (code, st') at h
              rw [hc] at h; exact nomatch h
            | ok pr =>
              change (match lowerImpureStepPure fuel ctx stIn (.inl c) with
                | Except.ok (c0, stOut) =>
                  Except.ok (c0, { stOut with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls })
                | Except.error e => Except.error e) = Except.ok (code, st') at h
              rw [hc] at h; injection h with hp; rcases Prod.mk.inj hp with ⟨_, rfl⟩
              rcases ih stIn pr.2 (.inl c) pr.1 hc with ⟨hn, ht⟩
              exact ⟨by rw [← hstIn.1]; exact hn, fun u hu => (ht u (by rw [hstIn.1]; exact hu)).trans (hstIn.2 u)⟩
          | default c => exact ih st st' (.inl c) code h
        | cons alt2 rest2 =>
          cases alt with
          | default c => exact ih st st' (.inl c) code h
          | ctorAlt info c _ =>
            dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
            cases hD : (discr?.bind st.lookupFVar?) with
            | none =>
              rw [hD] at h; dsimp only at h
              cases h1 : lowerImpureStepPure fuel ctx st (.inl c) with
              | error _ => rw [h1] at h; exact nomatch h
              | ok p1 =>
                rw [h1] at h; rcases p1 with ⟨yesCode, st1⟩; dsimp only at h
                rcases ih st st1 (.inl c) yesCode h1 with ⟨hn1, ht1⟩
                let st1R : RealBridgeState := { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                have hbase1 : st.nextVarId ≤ st1R.nextVarId := by change st.nextVarId ≤ st1.nextVarId; exact hn1
                cases h2 : lowerImpureStepPure fuel ctx st1R (.inr (condVar, isBool, idx + 1, discr?, alt2 :: rest2)) with
                | error _ => rw [h2] at h; exact nomatch h
                | ok p2 =>
                  rw [h2] at h; rcases p2 with ⟨noCode, st2⟩; dsimp only at h
                  rcases ih st1R st2 (.inr (condVar, isBool, idx + 1, discr?, alt2 :: rest2)) noCode h2 with ⟨hn2, ht2⟩
                  have hn3 : st.nextVarId ≤ st2.nextVarId := Nat.le_trans hbase1 hn2
                  have hty2 : ∀ u, u < st.nextVarId → st2.getVarType u = st.getVarType u := fun u hu => by
                    rw [ht2 u (Nat.lt_of_lt_of_le hu hbase1)]; exact ht1 u hu
                  cases hb : (isBool || lnirTypeEq (st.getVarType condVar) .i1) <;> simp only [hb, ↓reduceIte, Bool.false_eq_true] at h
                  · injection h with hp; rcases Prod.mk.inj hp with ⟨_, rfl⟩
                    rcases freshVar_spec st2 .i1 with ⟨_, hfn, hft, _, _, _⟩
                    exact ⟨Nat.le_trans hn3 (by rw [hfn]; exact Nat.le_succ _), fun u hu => by
                      rw [hft u, nat_beq_false (Nat.ne_of_lt (Nat.lt_of_lt_of_le hu hn3))]; exact hty2 u hu⟩
                  · injection h with hp; rcases Prod.mk.inj hp with ⟨_, rfl⟩
                    exact ⟨hn3, hty2⟩
            | some dv =>
              rw [hD] at h; dsimp only at h
              let stIn := st.setActiveCtor dv info.name
              have hstIn : stIn.nextVarId = st.nextVarId ∧ ∀ u, stIn.getVarType u = st.getVarType u := ⟨rfl, fun _ => rfl⟩
              cases h1 : lowerImpureStepPure fuel ctx stIn (.inl c) with
              | error _ => rw [h1] at h; exact nomatch h
              | ok p1 =>
                rw [h1] at h; rcases p1 with ⟨yesCode, st1⟩; dsimp only at h
                rcases ih stIn st1 (.inl c) yesCode h1 with ⟨hn1, ht1⟩
                let st1R : RealBridgeState := { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                have hbase1 : st.nextVarId ≤ st1R.nextVarId := by change stIn.nextVarId ≤ st1.nextVarId; exact hn1
                cases h2 : lowerImpureStepPure fuel ctx st1R (.inr (condVar, isBool, idx + 1, discr?, alt2 :: rest2)) with
                | error _ => rw [h2] at h; exact nomatch h
                | ok p2 =>
                  rw [h2] at h; rcases p2 with ⟨noCode, st2⟩; dsimp only at h
                  rcases ih st1R st2 (.inr (condVar, isBool, idx + 1, discr?, alt2 :: rest2)) noCode h2 with ⟨hn2, ht2⟩
                  have hn3 : st.nextVarId ≤ st2.nextVarId := Nat.le_trans hbase1 hn2
                  have hty2 : ∀ u, u < st.nextVarId → st2.getVarType u = st.getVarType u := fun u hu => by
                    rw [ht2 u (Nat.lt_of_lt_of_le hu hbase1)]; exact (ht1 u (by rw [hstIn.1]; exact hu)).trans (hstIn.2 u)
                  cases hb : (isBool || lnirTypeEq (st.getVarType condVar) .i1) <;> simp only [hb, ↓reduceIte, Bool.false_eq_true] at h
                  · injection h with hp; rcases Prod.mk.inj hp with ⟨_, rfl⟩
                    rcases freshVar_spec st2 .i1 with ⟨_, hfn, hft, _, _, _⟩
                    exact ⟨Nat.le_trans hn3 (by rw [hfn]; exact Nat.le_succ _), fun u hu => by
                      rw [hft u, nat_beq_false (Nat.ne_of_lt (Nat.lt_of_lt_of_le hu hn3))]; exact hty2 u hu⟩
                  · injection h with hp; rcases Prod.mk.inj hp with ⟨_, rfl⟩
                    exact ⟨hn3, hty2⟩
          | alt cn ps c _ =>
            dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, MonadExceptOf.throw, throwThe] at h
            cases hemp : (!ps.isEmpty) <;> simp only [hemp, ↓reduceIte, Bool.false_eq_true] at h
            · cases h1 : lowerImpureStepPure fuel ctx st (.inl c) with
              | error _ => rw [h1] at h; exact nomatch h
              | ok p1 =>
                rw [h1] at h; rcases p1 with ⟨yesCode, st1⟩; dsimp only at h
                rcases ih st st1 (.inl c) yesCode h1 with ⟨hn1, ht1⟩
                let st1R : RealBridgeState := { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                have hbase1 : st.nextVarId ≤ st1R.nextVarId := by change st.nextVarId ≤ st1.nextVarId; exact hn1
                cases h2 : lowerImpureStepPure fuel ctx st1R (.inr (condVar, isBool, idx + 1, discr?, alt2 :: rest2)) with
                | error _ => rw [h2] at h; exact nomatch h
                | ok p2 =>
                  rw [h2] at h; rcases p2 with ⟨noCode, st2⟩; dsimp only at h
                  rcases ih st1R st2 (.inr (condVar, isBool, idx + 1, discr?, alt2 :: rest2)) noCode h2 with ⟨hn2, ht2⟩
                  have hty2 : ∀ u, u < st.nextVarId → st2.getVarType u = st.getVarType u := fun u hu =>
                    (ht2 u (Nat.lt_of_lt_of_le hu hbase1)).trans (ht1 u hu)
                  cases hb : (isBool || lnirTypeEq (st.getVarType condVar) .i1) <;> simp only [hb, ↓reduceIte, Bool.false_eq_true] at h
                  · injection h with hp; rcases Prod.mk.inj hp with ⟨_, rfl⟩
                    rcases freshVar_spec st2 .i1 with ⟨_, hfn, hft, _, _, _⟩
                    have hn3 : st.nextVarId ≤ st2.nextVarId := Nat.le_trans hbase1 hn2
                    exact ⟨Nat.le_trans hn3 (by rw [hfn]; exact Nat.le_succ _), fun u hu => by
                      rw [hft u, nat_beq_false (Nat.ne_of_lt (Nat.lt_of_lt_of_le hu hn3))]; exact hty2 u hu⟩
                  · injection h with hp; rcases Prod.mk.inj hp with ⟨_, rfl⟩
                    exact ⟨Nat.le_trans hbase1 hn2, hty2⟩
            · exact nomatch h
    | inl c =>
      cases c with
      | «return» x =>
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
        cases hv : st.lookupBoundFVar x <;> rw [hv] at h
        · exact nomatch h
        · injection h with hp; rcases Prod.mk.inj hp with ⟨_, rfl⟩; exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
      | unreach _ => injection h with hp; rcases Prod.mk.inj hp with ⟨_, rfl⟩; exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
      | «fun» _ _ _ => exact nomatch h
      | «let» decl k =>
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, MonadExceptOf.throw, throwThe] at h
        let rawDeclTy := lowerGroundImpureTypeWith ctx decl.type
        have hInternMono : ∀ (stB : RealBridgeState) (t : LNIRType),
            st.nextVarId ≤ stB.nextVarId →
            (∀ u, u < st.nextVarId → stB.getVarType u = st.getVarType u) →
            st.nextVarId < (stB.allocFreshFVar decl.fvarId t).2.nextVarId ∧
            ∀ u, u < st.nextVarId → (stB.allocFreshFVar decl.fvarId t).2.getVarType u = st.getVarType u := by
          intro stB t hnb htb
          refine ⟨Nat.lt_of_le_of_lt hnb (Nat.lt_succ_self _), fun u hu => ?_⟩
          rw [getVarType_allocFresh, nat_beq_false (Nat.ne_of_lt (Nat.lt_of_lt_of_le hu hnb)), htb u hu]
          rfl
        have hStepMono : ∀ (stM : RealBridgeState),
            (st.nextVarId < stM.nextVarId ∧ ∀ u, u < st.nextVarId → stM.getVarType u = st.getVarType u) →
            (stM.nextVarId ≤ st'.nextVarId ∧ ∀ u, u < stM.nextVarId → st'.getVarType u = stM.getVarType u) →
            st.nextVarId ≤ st'.nextVarId ∧ ∀ u, u < st.nextVarId → st'.getVarType u = st.getVarType u := by
          intro stM ⟨hlt, hm2⟩ ⟨hnk, htk⟩
          exact ⟨Nat.le_trans (Nat.le_of_lt hlt) hnk, fun u hu => (htk u (Nat.lt_trans hu hlt)).trans (hm2 u hu)⟩
        cases hdv : decl.value with
        | ctor info args hp =>
          rw [hdv] at h; dsimp only at h
          cases hsc : (ctx.allowStage1DHeap && (info.usize > 0 || info.ssize > 0)) <;>
            simp only [hsc, ↓reduceIte, Bool.false_eq_true] at h
          · cases hl : lowerImpureLetValuePure ctx st (.ctor info args hp) rawDeclTy with
            | error _ => rw [hl] at h; exact nomatch h
            | ok p1 =>
              rw [hl] at h; rcases p1 with ⟨rhs, st1⟩
              have hst1 := lowerImpureLetValuePure_st_eq ctx st st1 (.ctor info args hp) rawDeclTy rhs hl; subst st1
              dsimp only at h
              let ty := inferImpureRhsTypePure st rhs rawDeclTy false
              let st2 := (st.allocFreshFVar decl.fvarId ty).2
              let st2' := if lnirTypeEq ty .objPtr then st2.setActiveCtor (st.allocFreshFVar decl.fvarId ty).1 info.name else st2
              have hst2' : st.nextVarId < st2'.nextVarId ∧ ∀ u, u < st.nextVarId → st2'.getVarType u = st.getVarType u := by
                dsimp only [st2']; cases lnirTypeEq ty .objPtr <;> exact hInternMono st ty (Nat.le_refl _) (fun _ _ => rfl)
              cases hk : lowerImpureStepPure fuel ctx st2' (.inl k) with
              | error _ => rw [hk] at h; exact nomatch h
              | ok pk =>
                rw [hk] at h; injection h with hp2; rcases Prod.mk.inj hp2 with ⟨_, rfl⟩
                exact hStepMono st2' hst2' (ih st2' pk.2 (.inl k) pk.1 hk)
          · cases hlay : ctx.findLayout? info.name <;> rw [hlay] at h
            · exact nomatch h
            · rename_i spec; dsimp only at h
              cases har : (args.size != spec.objSlots) <;> simp only [har, ↓reduceIte, Bool.false_eq_true] at h
              · cases hargL : lowerRealArgList ctx st true args.toList with
                | error _ => rw [hargL] at h; exact nomatch h
                | ok pa =>
                  rw [hargL] at h; rcases pa with ⟨objVars, st1⟩
                  have hst1 := lowerRealArgList_st_eq ctx true args.toList st st1 objVars hargL; subst st1
                  dsimp only at h
                  cases hok : (!(objVars.map st.getVarType).all fun t =>
                      isSupportedStage1BScalarOrTuple t ctx.arch || isHeapPtrType t) <;>
                    simp only [hok, ↓reduceIte, Bool.false_eq_true] at h
                  · rcases allocZeroScalarSlotsPure_mono spec.scalarSlots st with ⟨hnZ, htZ, _, _, _⟩
                    let stZ := (allocZeroScalarSlotsPure st spec.scalarSlots).2
                    have hst2 := hInternMono stZ .objPtr hnZ htZ
                    let st2' := (stZ.allocFreshFVar decl.fvarId .objPtr).2.setActiveCtor
                      (stZ.allocFreshFVar decl.fvarId .objPtr).1 info.name
                    cases hk : lowerImpureStepPure fuel ctx st2' (.inl k) with
                    | error _ => rw [hk] at h; exact nomatch h
                    | ok pk =>
                      rw [hk] at h; injection h with hp2; rcases Prod.mk.inj hp2 with ⟨_, rfl⟩
                      exact hStepMono st2' hst2 (ih st2' pk.2 (.inl k) pk.1 hk)
                  · exact nomatch h
              · exact nomatch h
        | fap fnName args hp =>
          rw [hdv] at h; dsimp only at h
          cases hloc : ctx.findLocalCallee? fnName <;> rw [hloc] at h
          · dsimp only at h
            cases hl : lowerImpureLetValuePure ctx st (.fap fnName args hp) rawDeclTy with
            | error _ => rw [hl] at h; exact nomatch h
            | ok p1 =>
              rw [hl] at h; rcases p1 with ⟨rhs, st1⟩
              have hst1 := lowerImpureLetValuePure_st_eq ctx st st1 (.fap fnName args hp) rawDeclTy rhs hl; subst st1
              dsimp only at h
              let ty := inferImpureRhsTypePure st rhs rawDeclTy false
              have hst2 := hInternMono st ty (Nat.le_refl _) (fun _ _ => rfl)
              cases hk : lowerImpureStepPure fuel ctx (st.allocFreshFVar decl.fvarId ty).2 (.inl k) with
              | error _ => rw [hk] at h; exact nomatch h
              | ok pk =>
                rw [hk] at h; injection h with hp2; rcases Prod.mk.inj hp2 with ⟨_, rfl⟩
                exact hStepMono _ hst2 (ih _ pk.2 (.inl k) pk.1 hk)
          · rename_i sym; dsimp only at h
            cases hca : lowerCallArgsWithErasedPure ctx st args.toList with
            | error _ => rw [hca] at h; exact nomatch h
            | ok pca =>
              rw [hca] at h; rcases pca with ⟨argVars, zeroBinds, st1⟩; dsimp only at h
              rcases lowerCallArgsWithErasedPure_mono ctx args.toList st st1 argVars zeroBinds hca with ⟨hn1, ht1⟩
              have hst2 := hInternMono st1 rawDeclTy hn1 ht1
              cases hk : lowerImpureStepPure fuel ctx (st1.allocFreshFVar decl.fvarId rawDeclTy).2 (.inl k) with
              | error _ => rw [hk] at h; exact nomatch h
              | ok pk =>
                rw [hk] at h; injection h with hp2; rcases Prod.mk.inj hp2 with ⟨_, rfl⟩
                exact hStepMono _ hst2 (ih _ pk.2 (.inl k) pk.1 hk)
        | _ =>
          rw [hdv] at h; dsimp only at h
          cases hl : lowerImpureLetValuePure ctx st _ rawDeclTy with
          | error _ => rw [hl] at h; exact nomatch h
          | ok p1 =>
            rw [hl] at h; rcases p1 with ⟨rhs, st1⟩
            have hst1 := lowerImpureLetValuePure_st_eq ctx st st1 _ rawDeclTy rhs hl; subst st1
            dsimp only at h
            split at h
            · cases hk : lowerImpureStepPure fuel ctx ((st.allocFreshFVar decl.fvarId _).2.freshVar .i1).2 (.inl k) with
              | error _ => rw [hk] at h; exact nomatch h
              | ok pk =>
                rw [hk] at h; injection h with hp2; rcases Prod.mk.inj hp2 with ⟨_, rfl⟩
                refine hStepMono _ ⟨?_, fun u hu => ?_⟩ (ih _ pk.2 (.inl k) pk.1 hk)
                · exact Nat.lt_trans (hInternMono st _ (Nat.le_refl _) (fun _ _ => rfl)).1 (Nat.lt_succ_self _)
                · rw [(freshVar_spec _ .i1).2.2.1 u,
                      nat_beq_false (Nat.ne_of_lt (Nat.lt_trans hu (hInternMono st _ (Nat.le_refl _) (fun _ _ => rfl)).1)),
                      getVarType_allocFresh, nat_beq_false (Nat.ne_of_lt hu)]
                  rfl
            · cases hk : lowerImpureStepPure fuel ctx (st.allocFreshFVar decl.fvarId _).2 (.inl k) with
              | error _ => rw [hk] at h; exact nomatch h
              | ok pk =>
                rw [hk] at h; injection h with hp2; rcases Prod.mk.inj hp2 with ⟨_, rfl⟩
                exact hStepMono _ (hInternMono st _ (Nat.le_refl _) (fun _ _ => rfl)) (ih _ pk.2 (.inl k) pk.1 hk)
      | inc x n _ _ k _ =>
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
        cases hv : st.lookupBoundFVar x <;> rw [hv] at h
        · exact nomatch h
        · rename_i vid; dsimp only at h
          cases hk : lowerImpureStepPure fuel ctx st (.inl k) with
          | error _ => rw [hk] at h; exact nomatch h
          | ok pk =>
            rw [hk] at h; dsimp only at h
            cases hr : lowerRefOpPure true vid (st.getVarType vid) n pk.1 <;> rw [hr] at h
            · exact nomatch h
            · injection h with hp; rcases Prod.mk.inj hp with ⟨_, rfl⟩; exact ih st pk.2 (.inl k) pk.1 hk
      | dec x n _ _ _ k _ =>
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
        cases hv : st.lookupBoundFVar x <;> rw [hv] at h
        · exact nomatch h
        · rename_i vid; dsimp only at h
          cases hk : lowerImpureStepPure fuel ctx st (.inl k) with
          | error _ => rw [hk] at h; exact nomatch h
          | ok pk =>
            rw [hk] at h; dsimp only at h
            cases hr : lowerRefOpPure false vid (st.getVarType vid) n pk.1 <;> rw [hr] at h
            · exact nomatch h
            · injection h with hp; rcases Prod.mk.inj hp with ⟨_, rfl⟩; exact ih st pk.2 (.inl k) pk.1 hk
      | del x k _ =>
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
        cases hv : st.lookupBoundFVar x <;> rw [hv] at h
        · exact nomatch h
        · rename_i vid; dsimp only at h
          cases hhp : (ctx.allowStage1DHeap && isHeapPtrType (st.getVarType vid)) <;> simp only [hhp, ↓reduceIte, Bool.false_eq_true] at h
          · cases hk : lowerImpureStepPure fuel ctx st (.inl k) with
            | error _ => rw [hk] at h; exact nomatch h
            | ok pk =>
              rw [hk] at h; dsimp only at h
              cases hr : lowerRefOpPure false vid (st.getVarType vid) 1 pk.1 <;> rw [hr] at h
              · exact nomatch h
              · injection h with hp; rcases Prod.mk.inj hp with ⟨_, rfl⟩; exact ih st pk.2 (.inl k) pk.1 hk
          · rcases freshVar_spec st .unit with ⟨_, hfn, hft, _, _, _⟩
            cases hk : lowerImpureStepPure fuel ctx (st.freshVar .unit).2 (.inl k) with
            | error _ => rw [hk] at h; exact nomatch h
            | ok pk =>
              rw [hk] at h; injection h with hp; rcases Prod.mk.inj hp with ⟨_, rfl⟩
              rcases ih (st.freshVar .unit).2 pk.2 (.inl k) pk.1 hk with ⟨hnk, htk⟩
              exact ⟨Nat.le_trans (by rw [hfn]; exact Nat.le_succ _) hnk, fun u hu => by
                rw [htk u (Nat.lt_of_lt_of_le hu (by rw [hfn]; exact Nat.le_succ _)), hft u,
                  nat_beq_false (Nat.ne_of_lt hu)]; rfl⟩
      | setTag x cidx k _ =>
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, MonadExceptOf.throw, throwThe] at h
        cases hv : st.lookupBoundFVar x <;> rw [hv] at h
        · exact nomatch h
        · rename_i vid; dsimp only at h
          cases hhp : (!(ctx.allowStage1DHeap && isHeapPtrType (st.getVarType vid))) <;>
            simp only [hhp, ↓reduceIte, Bool.false_eq_true] at h
          · have hcont : ∀ (nc? : Option Lean.Name) (pk : LNIRCode × RealBridgeState),
                lowerImpureStepPure fuel ctx
                  (((st.setActiveCtorOpt vid nc?).freshVar .i64).2.freshVar .unit).2 (.inl k) = .ok pk →
                st' = pk.2 →
                st.nextVarId ≤ st'.nextVarId ∧ ∀ u, u < st.nextVarId → st'.getVarType u = st.getVarType u := by
              intro nc? pk hk hstEq
              subst hstEq
              let st1 := st.setActiveCtorOpt vid nc?
              have hst1N : st1.nextVarId = st.nextVarId := by dsimp [st1]; cases nc? <;> rfl
              have hst1T : ∀ u, st1.getVarType u = st.getVarType u := by
                intro u; dsimp [st1]
                cases nc? <;> rfl
              let st2 := (st1.freshVar .i64).2
              let st3 := (st2.freshVar .unit).2
              rcases freshVar_spec st1 .i64 with ⟨_, hfn2, hft2, _, _, _⟩
              rcases freshVar_spec st2 .unit with ⟨_, hfn3, hft3, _, _, _⟩
              rcases ih st3 pk.2 (.inl k) pk.1 hk with ⟨hnk, htk⟩
              have hn3 : st3.nextVarId = st.nextVarId + 2 := by
                change (st2.freshVar .unit).2.nextVarId = _; rw [hfn3, hfn2, hst1N]
              refine ⟨Nat.le_trans (by rw [hn3]; exact Nat.le_add_right _ _) hnk, fun u hu => ?_⟩
              rw [htk u (by rw [hn3]; exact Nat.lt_add_right 2 hu)]
              change (st2.freshVar .unit).2.getVarType u = st.getVarType u
              rw [hft3 u, nat_beq_false (by rw [hfn2, hst1N]; exact Nat.ne_of_lt (Nat.lt_succ_of_lt hu))]
              change (st1.freshVar .i64).2.getVarType u = st.getVarType u
              rw [hft2 u, nat_beq_false (by rw [hst1N]; exact Nat.ne_of_lt hu)]; exact hst1T u
            cases hrc : st.resolveHeapCtor? ctx vid x with
            | none =>
              rw [hrc] at h; dsimp only at h
              cases hk : lowerImpureStepPure fuel ctx
                  (((st.setActiveCtorOpt vid none).freshVar .i64).2.freshVar .unit).2 (.inl k) with
              | error _ => rw [hk] at h; exact nomatch h
              | ok pk => rw [hk] at h; injection h with hp; exact hcont none pk hk (Prod.mk.inj hp).2.symm
            | some cur =>
              rw [hrc] at h; dsimp only at h
              cases hhs : ctx.hasSiblingEntry cur <;> simp only [hhs, ↓reduceIte, Bool.false_eq_true] at h
              · cases hk : lowerImpureStepPure fuel ctx
                    (((st.setActiveCtorOpt vid none).freshVar .i64).2.freshVar .unit).2 (.inl k) with
                | error _ => rw [hk] at h; exact nomatch h
                | ok pk => rw [hk] at h; injection h with hp; exact hcont none pk hk (Prod.mk.inj hp).2.symm
              · cases hfs : ctx.findSiblingCtor? cur cidx with
                | none => rw [hfs] at h; exact nomatch h
                | some nextC =>
                  rw [hfs] at h; dsimp only at h
                  cases hk : lowerImpureStepPure fuel ctx
                      (((st.setActiveCtorOpt vid (some nextC)).freshVar .i64).2.freshVar .unit).2 (.inl k) with
                  | error _ => rw [hk] at h; exact nomatch h
                  | ok pk => rw [hk] at h; injection h with hp; exact hcont (some nextC) pk hk (Prod.mk.inj hp).2.symm
          · exact nomatch h
      | oset x idx y k _ =>
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, MonadExceptOf.throw, throwThe] at h
        cases hv : st.lookupBoundFVar x <;> rw [hv] at h
        · exact nomatch h
        · rename_i vid; dsimp only at h
          cases hhp : (ctx.allowStage1DHeap && isHeapPtrType (st.getVarType vid)) <;> simp only [hhp, ↓reduceIte, Bool.false_eq_true] at h
          · cases hunb : isUnboxedScalarOrTuple (st.getVarType vid) <;> simp only [hunb, ↓reduceIte, Bool.false_eq_true] at h
            · exact nomatch h
            · exact ih st st' (.inl k) code h
          · cases hy : lowerRealArg ctx st y true with
            | error _ => rw [hy] at h; exact nomatch h
            | ok py =>
              rw [hy] at h; rcases py with ⟨valVid, stY⟩
              have hstY := lowerRealArg_st_eq ctx st stY y true valVid hy; subst stY
              dsimp only at h
              let st3 := (st.freshVar .i64).2
              let st4 := (st3.freshVar .unit).2
              rcases freshVar_spec st .i64 with ⟨_, hfn3, hft3, _, _, _⟩
              rcases freshVar_spec st3 .unit with ⟨_, hfn4, hft4, _, _, _⟩
              cases hk : lowerImpureStepPure fuel ctx st4 (.inl k) with
              | error _ => rw [hk] at h; exact nomatch h
              | ok pk =>
                rw [hk] at h; injection h with hp; rcases Prod.mk.inj hp with ⟨_, rfl⟩
                rcases ih st4 pk.2 (.inl k) pk.1 hk with ⟨hnk, htk⟩
                have hn4 : st4.nextVarId = st.nextVarId + 2 := by
                  change (st3.freshVar .unit).2.nextVarId = _; rw [hfn4, hfn3]
                exact ⟨Nat.le_trans (by rw [hn4]; exact Nat.le_add_right _ _) hnk, fun u hu => by
                  rw [htk u (by rw [hn4]; exact Nat.lt_add_right 2 hu)]
                  change (st3.freshVar .unit).2.getVarType u = st.getVarType u
                  rw [hft4 u, nat_beq_false (by rw [hfn3]; exact Nat.ne_of_lt (Nat.lt_succ_of_lt hu))]
                  change (st.freshVar .i64).2.getVarType u = st.getVarType u
                  rw [hft3 u, nat_beq_false (Nat.ne_of_lt hu)]; rfl⟩
      | uset x idx y k _ =>
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, MonadExceptOf.throw, throwThe] at h
        cases hv : st.lookupBoundFVar x <;> rw [hv] at h
        · exact nomatch h
        · rename_i vid; dsimp only at h
          split at h
          · exact nomatch h
          · cases hc : st.resolveHeapCtor? ctx vid x <;> rw [hc] at h
            · exact nomatch h
            · rename_i cname; dsimp only at h
              cases hlay : ctx.findLayout? cname <;> rw [hlay] at h
              · exact nomatch h
              · rename_i spec; dsimp only at h
                cases hsl : spec.usizeSlot? idx <;> rw [hsl] at h
                · exact nomatch h
                · rename_i slp; dsimp only at h
                  cases hy : st.lookupBoundFVar y <;> rw [hy] at h
                  · exact nomatch h
                  · dsimp only at h
                    let st3 := (st.freshVar .i64).2
                    let st4 := (st3.freshVar .unit).2
                    rcases freshVar_spec st .i64 with ⟨_, hfn3, hft3, _, _, _⟩
                    rcases freshVar_spec st3 .unit with ⟨_, hfn4, hft4, _, _, _⟩
                    cases hk : lowerImpureStepPure fuel ctx st4 (.inl k) with
                    | error _ => rw [hk] at h; exact nomatch h
                    | ok pk =>
                      rw [hk] at h; injection h with hp; rcases Prod.mk.inj hp with ⟨_, rfl⟩
                      rcases ih st4 pk.2 (.inl k) pk.1 hk with ⟨hnk, htk⟩
                      have hn4 : st4.nextVarId = st.nextVarId + 2 := by
                        change (st3.freshVar .unit).2.nextVarId = _; rw [hfn4, hfn3]
                      exact ⟨Nat.le_trans (by rw [hn4]; exact Nat.le_add_right _ _) hnk, fun u hu => by
                        rw [htk u (by rw [hn4]; exact Nat.lt_add_right 2 hu)]
                        change (st3.freshVar .unit).2.getVarType u = st.getVarType u
                        rw [hft4 u, nat_beq_false (by rw [hfn3]; exact Nat.ne_of_lt (Nat.lt_succ_of_lt hu))]
                        change (st.freshVar .i64).2.getVarType u = st.getVarType u
                        rw [hft3 u, nat_beq_false (Nat.ne_of_lt hu)]; rfl⟩
      | sset x n off y _ k _ =>
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, MonadExceptOf.throw, throwThe] at h
        cases hv : st.lookupBoundFVar x <;> rw [hv] at h
        · exact nomatch h
        · rename_i vid; dsimp only at h
          split at h
          · exact nomatch h
          · cases hc : st.resolveHeapCtor? ctx vid x <;> rw [hc] at h
            · exact nomatch h
            · rename_i cname; dsimp only at h
              cases hlay : ctx.findLayout? cname <;> rw [hlay] at h
              · exact nomatch h
              · rename_i spec; dsimp only at h
                cases hsl : spec.scalarSlot? n off <;> rw [hsl] at h
                · exact nomatch h
                · rename_i slp; dsimp only at h
                  cases hy : st.lookupBoundFVar y <;> rw [hy] at h
                  · exact nomatch h
                  · dsimp only at h
                    let st3 := (st.freshVar .i64).2
                    let st4 := (st3.freshVar .unit).2
                    rcases freshVar_spec st .i64 with ⟨_, hfn3, hft3, _, _, _⟩
                    rcases freshVar_spec st3 .unit with ⟨_, hfn4, hft4, _, _, _⟩
                    cases hk : lowerImpureStepPure fuel ctx st4 (.inl k) with
                    | error _ => rw [hk] at h; exact nomatch h
                    | ok pk =>
                      rw [hk] at h; injection h with hp; rcases Prod.mk.inj hp with ⟨_, rfl⟩
                      rcases ih st4 pk.2 (.inl k) pk.1 hk with ⟨hnk, htk⟩
                      have hn4 : st4.nextVarId = st.nextVarId + 2 := by
                        change (st3.freshVar .unit).2.nextVarId = _; rw [hfn4, hfn3]
                      exact ⟨Nat.le_trans (by rw [hn4]; exact Nat.le_add_right _ _) hnk, fun u hu => by
                        rw [htk u (by rw [hn4]; exact Nat.lt_add_right 2 hu)]
                        change (st3.freshVar .unit).2.getVarType u = st.getVarType u
                        rw [hft4 u, nat_beq_false (by rw [hfn3]; exact Nat.ne_of_lt (Nat.lt_succ_of_lt hu))]
                        change (st.freshVar .i64).2.getVarType u = st.getVarType u
                        rw [hft3 u, nat_beq_false (Nat.ne_of_lt hu)]; rfl⟩
      | cases cs =>
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, MonadExceptOf.throw, throwThe] at h
        cases hv : st.lookupBoundFVar cs.discr <;> rw [hv] at h
        · exact nomatch h
        · rename_i condVar; dsimp only at h
          cases hhp : ((ctx.allowStage1DHeap || cs.typeName == ``Bool) && isHeapPtrType (st.getVarType condVar)) <;>
            simp only [hhp, ↓reduceIte, Bool.false_eq_true] at h
          · cases hsc : (!isSupportedStage1BScalarType (st.getVarType condVar) ctx.arch) <;>
              simp only [hsc, ↓reduceIte, Bool.false_eq_true] at h
            · exact ih st st' _ code h
            · exact nomatch h
          · rcases freshVar_spec st .i64 with ⟨_, hfn, hft, _, _, _⟩
            cases hk : lowerImpureStepPure fuel ctx (st.freshVar .i64).2
                (.inr ((st.freshVar .i64).1, false, 0, some cs.discr, orderAltsPure cs.alts.toList)) with
            | error _ => rw [hk] at h; exact nomatch h
            | ok pk =>
              rw [hk] at h; injection h with hp; rcases Prod.mk.inj hp with ⟨_, rfl⟩
              rcases ih (st.freshVar .i64).2 pk.2 _ pk.1 hk with ⟨hnk, htk⟩
              exact ⟨Nat.le_trans (by rw [hfn]; exact Nat.le_succ _) hnk, fun u hu => by
                rw [htk u (Nat.lt_of_lt_of_le hu (by rw [hfn]; exact Nat.le_succ _)), hft u,
                  nat_beq_false (Nat.ne_of_lt hu)]; rfl⟩
      | jp decl k =>
        cases hrec : hasJmpToPure fuel decl.fvarId (.inl decl.value) <;> simp only [hrec, ↓reduceIte, Bool.false_eq_true] at h
        · exact ih (st.setJpDecl decl.fvarId decl.params.toList decl.value) st' (.inl k) code h
        · exact nomatch h
      | jmp fvarId args =>
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, MonadExceptOf.throw, throwThe] at h
        cases hjp : st.lookupJp? fvarId <;> rw [hjp] at h
        · exact nomatch h
        · rename_i jpPair; rcases jpPair with ⟨jpParams, jpBody⟩; dsimp only at h
          cases hb : bindJpCallArgsPure ctx st jpParams args.toList with
          | error _ => rw [hb] at h; exact nomatch h
          | ok pb =>
            rw [hb] at h; rcases pb with ⟨binds, st1⟩; dsimp only at h
            rcases bindJpCallArgsPure_mono ctx jpParams args.toList st st1 binds hb with ⟨hnextB, htyB, hmemB⟩
            let stIn := applyJpParamMapPure st1 binds
            rcases applyJpParamMapPure_mono st.nextVarId binds st1 hnextB (fun b hmb => (hmemB b hmb).1) with ⟨hnextIn, htyIn⟩
            cases hbody : lowerImpureStepPure fuel ctx stIn (.inl jpBody) with
            | error _ => rw [hbody] at h; exact nomatch h
            | ok pOut =>
              rw [hbody] at h; injection h with hp; rcases Prod.mk.inj hp with ⟨_, rfl⟩
              rcases ih stIn pOut.2 (.inl jpBody) pOut.1 hbody with ⟨hnextOut, htyOut⟩
              refine ⟨Nat.le_trans hnextB (by rw [← hnextIn]; exact hnextOut), fun u hu => ?_⟩
              change pOut.2.getVarType u = st.getVarType u
              have huIn : u < stIn.nextVarId := by rw [hnextIn]; exact Nat.lt_of_lt_of_le hu hnextB
              rw [htyOut u huIn, htyIn u hu, htyB u hu]


end LeanNative.Proofs
