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
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
        cases hl : lowerImpureLetValuePure ctx st decl.value (lowerGroundImpureType decl.type) with
        | error _ => rw [hl] at h; exact nomatch h
        | ok p1 =>
          rw [hl] at h; rcases p1 with ⟨rhs, st1⟩
          have hst1 := lowerImpureLetValuePure_st_eq ctx st st1 decl.value (lowerGroundImpureType decl.type) rhs hl; subst st1
          dsimp only at h
          have hInternMono : ∀ (t : LNIRType),
              (st.allocFreshFVar decl.fvarId t).2.nextVarId = st.nextVarId + 1 ∧
              ∀ u, u < st.nextVarId → (st.allocFreshFVar decl.fvarId t).2.getVarType u = st.getVarType u := fun t =>
            ⟨rfl, fun u hu => by rw [getVarType_allocFresh, nat_beq_false (Nat.ne_of_lt hu)]; rfl⟩
          have hStepMono : ∀ (stM : RealBridgeState),
              (stM.nextVarId = st.nextVarId + 1 ∧ ∀ u, u < st.nextVarId → stM.getVarType u = st.getVarType u) →
              (stM.nextVarId ≤ st'.nextVarId ∧ ∀ u, u < stM.nextVarId → st'.getVarType u = stM.getVarType u) →
              st.nextVarId ≤ st'.nextVarId ∧ ∀ u, u < st.nextVarId → st'.getVarType u = st.getVarType u := by
            intro stM ⟨hm1, hm2⟩ ⟨hnk, htk⟩
            have hlt : st.nextVarId < stM.nextVarId := by rw [hm1]; exact Nat.lt_succ_self _
            exact ⟨Nat.le_trans (Nat.le_of_lt hlt) hnk, fun u hu => (htk u (Nat.lt_trans hu hlt)).trans (hm2 u hu)⟩
          have hFreshMono : ∀ (stM : RealBridgeState),
              (stM.nextVarId = st.nextVarId + 1 ∧ ∀ u, u < st.nextVarId → stM.getVarType u = st.getVarType u) →
              ((stM.freshVar .i1).2.nextVarId ≤ st'.nextVarId ∧
                ∀ u, u < (stM.freshVar .i1).2.nextVarId → st'.getVarType u = (stM.freshVar .i1).2.getVarType u) →
              st.nextVarId ≤ st'.nextVarId ∧ ∀ u, u < st.nextVarId → st'.getVarType u = st.getVarType u := by
            intro stM ⟨hm1, hm2⟩ ⟨hnk, htk⟩
            rcases freshVar_spec stM .i1 with ⟨_, hfn, hft, _, _, _⟩
            have hlt0 : st.nextVarId < stM.nextVarId := by rw [hm1]; exact Nat.lt_succ_self _
            have hlt : st.nextVarId < (stM.freshVar .i1).2.nextVarId := by rw [hfn]; exact Nat.lt_trans hlt0 (Nat.lt_succ_self _)
            exact ⟨Nat.le_trans (Nat.le_of_lt hlt) hnk, fun u hu => by
              rw [htk u (Nat.lt_trans hu hlt), hft u, nat_beq_false (Nat.ne_of_lt (Nat.lt_trans hu hlt0))]; exact hm2 u hu⟩
          split at h
          · split at h
            · exact nomatch h
            · rename_i pk hk
              injection h with hp2; rcases Prod.mk.inj hp2 with ⟨_, rfl⟩
              refine hFreshMono _ ?_ (ih _ pk.2 (.inl k) pk.1 hk)
              cases decl.value <;> exact hInternMono _
          · rename_i hne
            split at h
            · exact nomatch h
            · rename_i pk hk
              injection h with hp2; rcases Prod.mk.inj hp2 with ⟨_, rfl⟩
              refine hStepMono _ ?_ (ih _ pk.2 (.inl k) pk.1 hk)
              clear hk ih hne
              cases decl.value <;> try exact hInternMono _
              dsimp only
              cases lnirTypeEq (inferImpureRhsTypePure st rhs (lowerGroundImpureType decl.type) false) .objPtr <;> exact hInternMono _
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
          · let st2 := (st.freshVar .i64).2
            let st3 := (st2.freshVar .unit).2
            rcases freshVar_spec st .i64 with ⟨_, hfn2, hft2, _, _, _⟩
            rcases freshVar_spec st2 .unit with ⟨_, hfn3, hft3, _, _, _⟩
            cases hk : lowerImpureStepPure fuel ctx st3 (.inl k) with
            | error _ => rw [hk] at h; exact nomatch h
            | ok pk =>
              rw [hk] at h; injection h with hp; rcases Prod.mk.inj hp with ⟨_, rfl⟩
              rcases ih st3 pk.2 (.inl k) pk.1 hk with ⟨hnk, htk⟩
              have hn3 : st3.nextVarId = st.nextVarId + 2 := by
                change (st2.freshVar .unit).2.nextVarId = _; rw [hfn3, hfn2]
              exact ⟨Nat.le_trans (by rw [hn3]; exact Nat.le_add_right _ _) hnk, fun u hu => by
                rw [htk u (by rw [hn3]; exact Nat.lt_add_right 2 hu)]
                change (st2.freshVar .unit).2.getVarType u = st.getVarType u
                rw [hft3 u, nat_beq_false (by rw [hfn2]; exact Nat.ne_of_lt (Nat.lt_succ_of_lt hu))]
                change (st.freshVar .i64).2.getVarType u = st.getVarType u
                rw [hft2 u, nat_beq_false (Nat.ne_of_lt hu)]; rfl⟩
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
          · cases hc : st.getActiveCtor? vid <;> rw [hc] at h
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
          · cases hc : st.getActiveCtor? vid <;> rw [hc] at h
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
          cases hhp : (ctx.allowStage1DHeap && cs.typeName != ``Bool && isHeapPtrType (st.getVarType condVar)) <;>
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
