import LeanNative.Proofs.RealLCNFBridge.LetValue

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

theorem evalCode_fuel_mono_step (f : Nat) : ∀ (c : LNIRCode) (venv : VarEnv) (hst : HeapState) (v : Val) (hst' : HeapState),
    evalCode f venv hst c = .ok (v, hst') → evalCode (f + 1) venv hst c = .ok (v, hst')
  | .letBind dst _ val k, venv, hst, v, hst', h => by
    dsimp only [evalCode] at h ⊢
    cases he : evalExpr venv hst val with
    | error _ => rw [he] at h; exact nomatch h
    | ok p => rw [he] at h; exact evalCode_fuel_mono_step f k (venv.bind dst p.1) p.2 v hst' h
  | .rawStore pv iv vv elemTy k, venv, hst, v, hst', h => by
    dsimp only [evalCode] at h ⊢
    cases hp : venv pv <;> cases hi : venv iv <;>
      cases hv : venv vv <;> simp only [hp, hi, hv] at h <;> try contradiction
    rename_i vp vi vv0
    cases vp <;> cases vi <;>
      cases vv0 <;> simp only at h ⊢ <;> try contradiction
    all_goals (
      rename_i bufId idx val
      cases hw : hst.writeElemExclusive bufId idx.toNat (maskElemVal elemTy val) <;> simp only [hw] at h ⊢
      · contradiction
      · rename_i hst1; exact evalCode_fuel_mono_step f k venv hst1 v hst' h)
  | .incRef ov cnt k, venv, hst, v, hst', h => by
    dsimp only [evalCode] at h ⊢
    cases he : hst.evalIncRef venv ov cnt with
    | error _ => rw [he] at h; exact nomatch h
    | ok hst1 => rw [he] at h; exact evalCode_fuel_mono_step f k venv hst1 v hst' h
  | .decRef ov cnt k, venv, hst, v, hst', h => by
    dsimp only [evalCode] at h ⊢
    cases he : hst.evalDecRef venv ov cnt with
    | error _ => rw [he] at h; exact nomatch h
    | ok hst1 => rw [he] at h; exact evalCode_fuel_mono_step f k venv hst1 v hst' h
  | .ite cv t e, venv, hst, v, hst', h => by
    dsimp only [evalCode] at h ⊢
    cases hc : venv cv <;> rw [hc] at h
    · exact nomatch h
    · rename_i vc; cases vc with
      | bool b => cases b <;> exact evalCode_fuel_mono_step f _ venv hst v hst' h
      | u64 n => by_cases hn : n != 0 <;> simp only [hn, ↓reduceIte, Bool.false_eq_true] at h ⊢ <;>
          exact evalCode_fuel_mono_step f _ venv hst v hst' h
      | u256 w => by_cases hw : w != UInt256.zero <;> simp only [hw, ↓reduceIte, Bool.false_eq_true] at h ⊢ <;>
          exact evalCode_fuel_mono_step f _ venv hst v hst' h
      | _ => exact nomatch h
  | .seqFor idxVar loVar hiVar accVar accInit _ stepBody k, venv, hst, v, hst', h => by
    dsimp only [evalCode] at h ⊢
    cases hlo : venv loVar <;> cases hhi : venv hiVar <;>
      cases hain : venv accInit <;> simp only [hlo, hhi, hain] at h <;> try contradiction
    rename_i vlo vhi initVal
    cases vlo <;> cases vhi <;>
      simp only at h ⊢ <;> try contradiction
    rename_i lo hi
    have hloop : ∀ cnt cur acc env0 st0 r,
        evalSeqLoop cnt cur idxVar accVar acc env0 st0 (fun se ss => evalCode f se ss stepBody) = .ok r →
        evalSeqLoop cnt cur idxVar accVar acc env0 st0 (fun se ss => evalCode (f + 1) se ss stepBody) = .ok r := by
      intro cnt; induction cnt with
      | zero => intro _ _ _ _ _ hr; exact hr
      | succ cnt' ihc =>
        intro cur acc env0 st0 r hr; dsimp only [evalSeqLoop] at hr ⊢
        cases hs : evalCode f ((env0.bind idxVar (.u64 cur.toUInt64)).bind accVar acc) st0 stepBody with
        | error _ => rw [hs] at hr; exact nomatch hr
        | ok pr =>
          rw [hs] at hr
          rw [evalCode_fuel_mono_step f stepBody _ st0 pr.1 pr.2 hs]
          exact ihc (cur + 1) pr.1 env0 pr.2 r hr
    cases hl : evalSeqLoop (hi.toNat - lo.toNat) lo.toNat idxVar accVar initVal venv hst
        (fun se ss => evalCode f se ss stepBody) with
    | error _ => rw [hl] at h; exact nomatch h
    | ok pr =>
      rw [hl] at h; rw [hloop _ _ _ _ _ pr hl]
      exact evalCode_fuel_mono_step f k (venv.bind accVar pr.1) pr.2 v hst' h
  | .parFor outVar lenVar inputs elemTy kernel k, venv, hst, v, hst', h => by
    dsimp only [evalCode] at h ⊢
    have hpf : ∀ r, evalParFor f venv hst lenVar inputs kernel elemTy = .ok r →
        evalParFor (f + 1) venv hst lenVar inputs kernel elemTy = .ok r := by
      intro r hp; unfold evalParFor at hp ⊢
      cases hl : venv lenVar <;> rw [hl] at hp
      · exact nomatch hp
      · rename_i vl
        cases vl with
        | u64 n =>
          dsimp only at hp ⊢
          by_cases hgt : n.toNat > f
          · simp only [hgt, ↓reduceIte] at hp; exact nomatch hp
          · have hgt' : ¬(n.toNat > f + 1) := by omega
            simp only [hgt, hgt', ↓reduceIte] at hp ⊢; exact hp
        | _ => exact nomatch hp
    cases hp : evalParFor f venv hst lenVar inputs kernel elemTy with
    | error _ => rw [hp] at h; exact nomatch h
    | ok pr =>
      rw [hp] at h; rw [hpf pr hp]
      exact evalCode_fuel_mono_step f k (venv.bind outVar pr.1) pr.2 v hst' h
  | .ret _, _, _, _, _, h => h
  | .unreachable, _, _, _, _, h => h

theorem bridgeInv_ext (st st' : RealBridgeState) (lenv : LEnv) (venv : VarEnv)
    (hinv : BridgeStateInv st lenv venv)
    (hnext : st.nextVarId ≤ st'.nextVarId)
    (hty : ∀ u, u < st.nextVarId → st'.getVarType u = st.getVarType u)
    (hlu : st'.fvarMap = st.fvarMap)
    (hctor : ∀ u, u < st.nextVarId → st'.getActiveCtor? u = st.getActiveCtor? u)
    (hjp : st'.jpDecls = st.jpDecls) :
    BridgeStateInv st' lenv venv := by
  have hluf : ∀ x, st'.lookupFVar? x = st.lookupFVar? x := fun x => by simp [RealBridgeState.lookupFVar?, hlu]
  have hjpf : ∀ j, st'.lookupJp? j = st.lookupJp? j := fun j => by simp [RealBridgeState.lookupJp?, hjp]
  refine ⟨fun x vid hx => ?_, fun x vid hx => ?_, fun x vid hx => ?_, fun x vid hx => ?_,
    fun x1 x2 vid hx1 hx2 => ?_, fun j ps body hj => ?_⟩
  · rw [hluf] at hx; exact Nat.lt_of_lt_of_le (hinv.fvar_lt x vid hx) hnext
  · rw [hluf] at hx; exact hinv.fvar_val x vid hx
  · rw [hluf] at hx; rw [hinv.fvar_ty x vid hx, hty vid (hinv.fvar_lt x vid hx)]
  · rw [hluf] at hx; rw [hinv.fvar_ctor x vid hx, hctor vid (hinv.fvar_lt x vid hx)]
  · rw [hluf] at hx1 hx2; exact hinv.fvar_inj x1 x2 vid hx1 hx2
  · rw [hjpf] at hj; exact hinv.jp_sync j ps body hj

theorem lowerRealArg_st_eq (ctx : RealBridgeCtx) (st st1 : RealBridgeState)
    (arg : Lean.Compiler.LCNF.Arg .impure) (allowObj : Bool) (vid : VarId)
    (h : lowerRealArg ctx st arg allowObj = .ok (vid, st1)) : st1 = st := by
  cases arg with
  | erased | type _ _ => exact nomatch h
  | fvar x =>
    unfold lowerRealArg at h
    cases hv : st.lookupFVar? x <;> simp only [hv] at h
    · exact nomatch h
    · split at h
      · injection h with hp; exact (Prod.mk.inj hp).2.symm
      · exact nomatch h

theorem lowerRealArgList_st_eq (ctx : RealBridgeCtx) (allowObj : Bool) :
    ∀ (args : List (Lean.Compiler.LCNF.Arg .impure)) (st st1 : RealBridgeState) (vids : List VarId),
      lowerRealArgList ctx st allowObj args = .ok (vids, st1) → st1 = st
  | [], st, st1, _, h => by injection h with hp; exact (Prod.mk.inj hp).2.symm
  | a :: rest, st, st1, _, h => by
    unfold lowerRealArgList at h; dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases ha : lowerRealArg ctx st a allowObj with
    | error _ => rw [ha] at h; exact nomatch h
    | ok p1 =>
      rw [ha] at h; rcases p1 with ⟨v0, stA⟩
      have hstA := lowerRealArg_st_eq ctx st stA a allowObj v0 ha; subst stA
      dsimp only at h
      cases hr : lowerRealArgList ctx st allowObj rest with
      | error _ => rw [hr] at h; exact nomatch h
      | ok p2 =>
        rw [hr] at h; dsimp only at h; injection h with hp
        exact (Prod.mk.inj hp).2.symm.trans (lowerRealArgList_st_eq ctx allowObj rest st p2.2 p2.1 hr)

private theorem lowerRealCtor_st_eq (ctx : RealBridgeCtx) (st st1 : RealBridgeState)
    (ctorName : Lean.Name) (cidx : Nat) (args : List (Lean.Compiler.LCNF.Arg .impure)) (retTy : LNIRType)
    (expr : LNIRExpr) (h : lowerRealCtor ctx st ctorName cidx args retTy = .ok (expr, st1)) : st1 = st := by
  unfold lowerRealCtor at h
  cases hempty : args.isEmpty <;> simp only [hempty, ↓reduceIte, Bool.false_eq_true] at h
  · have htup : ∀ e s, (match ctx.findTupleArity? ctorName with
        | some numFields =>
          let dropCnt := if args.length > numFields then args.length - numFields else 0
          match lowerRealArgList ctx st true (args.drop dropCnt) with
          | Except.error e => Except.error e
          | Except.ok (argVars, st1) =>
            let argTys := argVars.map st1.getVarType
            if argVars.isEmpty || !(argTys.all fun t => isSupportedStage1BScalarType t ctx.arch || isHeapPtrType t) then
              Except.error s!"[lean-native] Unsupported non-scalar or nested tuple/constructor fields in `{ctorName}`"
            else Except.ok (LNIRExpr.mkTuple argVars, st1)
        | none =>
          Except.error s!"[lean-native] Unsupported payload-carrying constructor `{ctorName}` in Stage 1B") =
          Except.ok (e, s) → s = st := by
      intro e s ht
      cases hfa : ctx.findTupleArity? ctorName <;> simp only [hfa] at ht
      · exact nomatch ht
      · rename_i nf
        cases hl : lowerRealArgList ctx st true (args.drop (if args.length > nf then args.length - nf else 0)) with
        | error _ => rw [hl] at ht; exact nomatch ht
        | ok p =>
          rw [hl] at ht; dsimp only at ht
          split at ht
          · exact nomatch ht
          · injection ht with hp; exact (Prod.mk.inj hp).2.symm.trans (lowerRealArgList_st_eq ctx true _ st p.2 p.1 hl)
    cases hall : ctx.allowStage1DHeap <;> simp only [hall, ↓reduceIte, Bool.false_eq_true] at h
    · exact htup expr st1 h
    · cases hfl : ctx.findLayout? ctorName <;> simp only [hfl] at h
      · exact htup expr st1 h
      · rename_i spec
        split at h
        · exact nomatch h
        · cases hl : lowerRealArgList ctx st true (args.drop (if args.length > spec.objSlots then args.length - spec.objSlots else 0)) with
          | error _ => rw [hl] at h; exact nomatch h
          | ok p =>
            rw [hl] at h; dsimp only at h
            split at h
            · injection h with hp; exact (Prod.mk.inj hp).2.symm.trans (lowerRealArgList_st_eq ctx true _ st p.2 p.1 hl)
            · exact htup expr st1 h
  · cases hc1 : (ctorName == ``Bool.false) <;> simp only [hc1, ↓reduceIte, Bool.false_eq_true] at h
    · cases hc2 : (ctorName == ``Bool.true) <;> simp only [hc2, ↓reduceIte, Bool.false_eq_true] at h
      · cases hc3 : (ctorName == ``Unit.unit || ctorName == ``PUnit.unit) <;> simp only [hc3, ↓reduceIte, Bool.false_eq_true] at h
        · cases hfn : ctx.findNullaryCtor? ctorName <;> simp only [hfn] at h
          · exact nomatch h
          · split at h
            · injection h with hp; exact (Prod.mk.inj hp).2.symm
            · exact nomatch h
        · injection h with hp; exact (Prod.mk.inj hp).2.symm
      · injection h with hp; exact (Prod.mk.inj hp).2.symm
    · injection h with hp; exact (Prod.mk.inj hp).2.symm

theorem lowerImpureLetValuePure_st_eq (ctx : RealBridgeCtx) (st st1 : RealBridgeState)
    (lv : Lean.Compiler.LCNF.LetValue .impure) (retTy : LNIRType) (expr : LNIRExpr)
    (h : lowerImpureLetValuePure ctx st lv retTy = .ok (expr, st1)) : st1 = st := by
  cases lv with
  | lit l =>
    unfold lowerImpureLetValuePure at h; dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases hl : lowerLitValuePure l retTy ctx.arch true <;> rw [hl] at h
    · exact nomatch h
    · injection h with hp; exact (Prod.mk.inj hp).2.symm
  | erased => injection h with hp; exact (Prod.mk.inj hp).2.symm
  | ctor info args _ => exact lowerRealCtor_st_eq ctx st st1 info.name info.cidx args.toList retTy expr h
  | reuse slot info _ args _ =>
    unfold lowerImpureLetValuePure at h; dsimp only [Bind.bind, Except.bind] at h
    cases hs : st.lookupBoundFVar slot <;> rw [hs] at h
    · exact nomatch h
    · dsimp only at h; split at h
      · exact lowerRealCtor_st_eq ctx st st1 info.name info.cidx args.toList retTy expr h
      · exact nomatch h
  | fap fn args _ =>
    unfold lowerImpureLetValuePure at h; dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases hsl : lowerSliceCallPure? st fn args.toList retTy (ctx.findLocalCallee? fn).isSome ctx.arch with
    | some sliceIntr =>
      rw [hsl] at h; injection h with hp; exact (Prod.mk.inj hp).2.symm
    | none =>
      rw [hsl] at h; dsimp only at h
      cases hl : lowerRealArgList ctx st false args.toList with
      | error _ => rw [hl] at h; exact nomatch h
      | ok p =>
        rw [hl] at h; dsimp only at h
        cases hi : lowerCanonicalIntrinsicPure? fn p.1 retTy (p.1.map p.2.getVarType)
            (ctx.findLocalCallee? fn).isSome ctx.arch ctx.gfSimdIntrinsics <;> rw [hi] at h
        · exact nomatch h
        · injection h with hp; exact (Prod.mk.inj hp).2.symm.trans (lowerRealArgList_st_eq ctx false args.toList st p.2 p.1 hl)
  | pap _ _ _ => exact nomatch h
  | fvar x args =>
    unfold lowerImpureLetValuePure at h; dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases hemp : (!args.isEmpty) <;> simp only [hemp, ↓reduceIte, Bool.false_eq_true] at h
    · cases hs : st.lookupBoundFVar x <;> rw [hs] at h
      · exact nomatch h
      · injection h with hp; exact (Prod.mk.inj hp).2.symm
    · exact nomatch h
  | oproj idx x _ =>
    dsimp only [lowerImpureLetValuePure, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases hs : st.lookupBoundFVar x <;> rw [hs] at h
    · exact nomatch h
    · rename_i vid; dsimp only at h
      cases hvt : st.getVarType vid <;> rw [hvt] at h <;>
        first | (injection h with hp; exact (Prod.mk.inj hp).2.symm) | exact nomatch h
  | uproj idx x _ =>
    dsimp only [lowerImpureLetValuePure, Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, MonadExceptOf.throw] at h
    cases hs : st.lookupBoundFVar x <;> rw [hs] at h
    · exact nomatch h
    · rename_i vid; dsimp only at h
      cases hvt : st.getVarType vid with
      | tuple _ => rw [hvt] at h; injection h with hp; exact (Prod.mk.inj hp).2.symm
      | _ =>
        rw [hvt] at h; dsimp only at h
        split at h
        · exact nomatch h
        · cases hc : st.resolveHeapCtor? ctx vid x with
          | none => rw [hc] at h; exact nomatch h
          | some cname =>
            rw [hc] at h; dsimp only at h
            cases hlay : ctx.findLayout? cname with
            | none => rw [hlay] at h; exact nomatch h
            | some spec =>
              rw [hlay] at h; dsimp only at h
              cases hsl : spec.usizeSlot? idx with
              | none => rw [hsl] at h; exact nomatch h
              | some slp => rw [hsl] at h; injection h with hp; exact (Prod.mk.inj hp).2.symm
  | sproj n off x _ =>
    dsimp only [lowerImpureLetValuePure, Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, MonadExceptOf.throw] at h
    cases hs : st.lookupBoundFVar x <;> rw [hs] at h
    · exact nomatch h
    · rename_i vid; dsimp only at h
      cases hvt : st.getVarType vid with
      | tuple _ => rw [hvt] at h; injection h with hp; exact (Prod.mk.inj hp).2.symm
      | _ =>
        rw [hvt] at h; dsimp only at h
        split at h
        · exact nomatch h
        · cases hc : st.resolveHeapCtor? ctx vid x with
          | none => rw [hc] at h; exact nomatch h
          | some cname =>
            rw [hc] at h; dsimp only at h
            cases hlay : ctx.findLayout? cname with
            | none => rw [hlay] at h; exact nomatch h
            | some spec =>
              rw [hlay] at h; dsimp only at h
              cases hsl : spec.scalarSlot? n off with
              | none => rw [hsl] at h; exact nomatch h
              | some slp =>
                rw [hsl] at h; dsimp only at h
                cases hteq : (!lnirTypeEq retTy slp.2) <;> rw [hteq] at h
                · exact (Prod.mk.inj (Except.ok.inj h)).2.symm
                · exact nomatch h
  | box _ x _ | unbox x _ =>
    unfold lowerImpureLetValuePure at h; dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases hs : st.lookupBoundFVar x <;> rw [hs] at h
    · exact nomatch h
    · rename_i vid; dsimp only at h
      cases hok : (isUnboxedScalarOrTuple (st.getVarType vid) || isHeapPtrType (st.getVarType vid)) <;>
        simp only [hok, ↓reduceIte, Bool.false_eq_true] at h
      · exact nomatch h
      · injection h with hp; exact (Prod.mk.inj hp).2.symm
  | isShared x _ =>
    unfold lowerImpureLetValuePure at h; dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases hs : st.lookupBoundFVar x <;> rw [hs] at h
    · exact nomatch h
    · rename_i vid; dsimp only at h
      cases h1 : isUnboxedScalarOrTuple (st.getVarType vid) <;> simp only [h1, ↓reduceIte, Bool.false_eq_true] at h
      · cases h2 : (ctx.allowStage1DHeap && isHeapPtrType (st.getVarType vid)) <;> simp only [h2, ↓reduceIte, Bool.false_eq_true] at h
        · exact nomatch h
        · injection h with hp; exact (Prod.mk.inj hp).2.symm
      · injection h with hp; exact (Prod.mk.inj hp).2.symm
  | reset _ x _ =>
    unfold lowerImpureLetValuePure at h; dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases hs : st.lookupBoundFVar x <;> rw [hs] at h
    · exact nomatch h
    · rename_i vid; dsimp only at h
      cases h1 : isUnboxedScalarOrTuple (st.getVarType vid) <;> simp only [h1, ↓reduceIte, Bool.false_eq_true] at h
      · exact nomatch h
      · injection h with hp; exact (Prod.mk.inj hp).2.symm
  | proj _ _ _ hp | const _ _ _ hp => cases hp

theorem nat_beq_false {a b : Nat} (h : a ≠ b) : (a == b) = false :=
  beq_eq_false_iff_ne.mpr h

theorem lookupFVar_allocFresh (st : RealBridgeState) (x y : Lean.FVarId) (ty : LNIRType) :
    (st.allocFreshFVar x ty).2.lookupFVar? y = if y == x then some st.nextVarId else st.lookupFVar? y := by
  unfold RealBridgeState.allocFreshFVar; exact lookupFVar_cons st.fvarMap x y st.nextVarId

theorem getVarType_allocFresh (st : RealBridgeState) (x : Lean.FVarId) (ty : LNIRType) (u : VarId) :
    (st.allocFreshFVar x ty).2.getVarType u = if u == st.nextVarId then ty else st.getVarType u := by
  unfold RealBridgeState.allocFreshFVar; exact getVarType_setVarType st st.nextVarId u ty

private theorem getActiveCtor_allocFresh (st : RealBridgeState) (x : Lean.FVarId) (ty : LNIRType) (u : VarId) :
    (st.allocFreshFVar x ty).2.getActiveCtor? u = if u == st.nextVarId then none else st.getActiveCtor? u := by
  by_cases h : u = st.nextVarId
  · subst h
    unfold RealBridgeState.allocFreshFVar RealBridgeState.getActiveCtor?
    have hnone : ∀ (l : List (VarId × Lean.Name)) (w : VarId),
        (l.filter (fun (v, _) => v != w)).find? (fun (v, _) => v == w) = none := by
      intro l w; induction l with
      | nil => rfl
      | cons hd tl ih =>
        rcases hd with ⟨v, c⟩; dsimp only [List.filter]
        cases hvu : (v != w)
        · exact ih
        · dsimp only [List.find?]
          have hvu' : (v == w) = false := by revert hvu; simp [bne]
          rw [hvu']; exact ih
    simp only [beq_self_eq_true, ↓reduceIte]; rw [hnone]; rfl
  · simp only [nat_beq_false h, Bool.false_eq_true, ↓reduceIte]
    exact getActiveCtor_filter_ne st.activeCtor st.nextVarId u h

theorem freshVar_spec (st : RealBridgeState) (ty : LNIRType) :
    (st.freshVar ty).1 = st.nextVarId ∧ (st.freshVar ty).2.nextVarId = st.nextVarId + 1 ∧
    (∀ u, (st.freshVar ty).2.getVarType u = if u == st.nextVarId then ty else st.getVarType u) ∧
    (∀ y, (st.freshVar ty).2.lookupFVar? y = st.lookupFVar? y) ∧
    (∀ u, (st.freshVar ty).2.getActiveCtor? u = st.getActiveCtor? u) ∧
    (∀ j, (st.freshVar ty).2.lookupJp? j = st.lookupJp? j) := by
  unfold RealBridgeState.freshVar
  exact ⟨rfl, rfl, fun u => getVarType_setVarType st st.nextVarId u ty, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem venv_bind_fresh (venv : VarEnv) (base : VarId) (u : VarId) (hu : u < base) (v : Val) :
    (venv.bind base v) u = venv u :=
  VarEnv.bind_ne venv base u v (nat_beq_false (Nat.ne_of_lt hu))

theorem bridgeInv_bind_fresh (st : RealBridgeState) (lenv : LEnv) (venv : VarEnv)
    (x : Lean.FVarId) (ty : LNIRType) (val : Val)
    (hinv : BridgeStateInv st lenv venv) :
    BridgeStateInv (st.allocFreshFVar x ty).2
      (lenv.bind x val none (some ty)) (venv.bind st.nextVarId val) := by
  refine ⟨fun y vid hy => ?_, fun y vid hy => ?_, fun y vid hy => ?_, fun y vid hy => ?_,
    fun y1 y2 vid hy1 hy2 => ?_, fun j ps body hj => ?_⟩
  · rw [lookupFVar_allocFresh] at hy
    cases hyx : (y == x) <;> rw [hyx] at hy
    · exact Nat.lt_trans (hinv.fvar_lt y vid hy) (Nat.lt_succ_self st.nextVarId)
    · injection hy with hvid; rw [← hvid]; exact Nat.lt_succ_self st.nextVarId
  · rw [lookupFVar_allocFresh] at hy
    cases hyx : (y == x) <;> rw [hyx] at hy
    · simp only [Bool.false_eq_true, ↓reduceIte] at hy
      rcases hinv.fvar_val y vid hy with ⟨hL, hV⟩
      have hlt : vid < st.nextVarId := hinv.fvar_lt y vid hy
      dsimp only [LEnv.bind]; rw [hyx, venv_bind_fresh venv st.nextVarId vid hlt val]
      exact ⟨hL, hV⟩
    · simp only [↓reduceIte] at hy; injection hy with hvid; rw [← hvid]
      dsimp only [LEnv.bind]; rw [hyx, VarEnv.bind_self]
      exact ⟨rfl, rfl⟩
  · rw [lookupFVar_allocFresh] at hy
    cases hyx : (y == x) <;> rw [hyx] at hy
    · simp only [Bool.false_eq_true, ↓reduceIte] at hy
      have hlt : vid < st.nextVarId := hinv.fvar_lt y vid hy
      dsimp only [LEnv.bind]; rw [hyx, getVarType_allocFresh, nat_beq_false (Nat.ne_of_lt hlt)]
      exact hinv.fvar_ty y vid hy
    · simp only [↓reduceIte] at hy; injection hy with hvid; rw [← hvid]
      dsimp only [LEnv.bind]; rw [hyx, getVarType_allocFresh, beq_self_eq_true]
      rfl
  · rw [lookupFVar_allocFresh] at hy
    cases hyx : (y == x) <;> rw [hyx] at hy
    · simp only [Bool.false_eq_true, ↓reduceIte] at hy
      have hlt : vid < st.nextVarId := hinv.fvar_lt y vid hy
      dsimp only [LEnv.bind]; rw [hyx, getActiveCtor_allocFresh, nat_beq_false (Nat.ne_of_lt hlt)]
      exact hinv.fvar_ctor y vid hy
    · simp only [↓reduceIte] at hy; injection hy with hvid; rw [← hvid]
      dsimp only [LEnv.bind]; rw [hyx, getActiveCtor_allocFresh, beq_self_eq_true]
      rfl
  · rw [lookupFVar_allocFresh] at hy1 hy2
    cases hy1x : (y1 == x) <;> rw [hy1x] at hy1
    · cases hy2x : (y2 == x) <;> rw [hy2x] at hy2
      · exact hinv.fvar_inj y1 y2 vid hy1 hy2
      · injection hy2 with hvid; rw [← hvid] at hy1
        exact False.elim (Nat.lt_irrefl _ (hinv.fvar_lt y1 st.nextVarId hy1))
    · injection hy1 with hvid; rw [← hvid] at hy2
      cases hy2x : (y2 == x) <;> rw [hy2x] at hy2
      · exact False.elim (Nat.lt_irrefl _ (hinv.fvar_lt y2 st.nextVarId hy2))
      · exact (beq_iff_eq.mp hy1x).trans (beq_iff_eq.mp hy2x).symm
  · exact hinv.jp_sync j ps body hj

theorem bridgeInv_setActiveCtor (st : RealBridgeState) (lenv : LEnv) (venv : VarEnv)
    (vid : VarId) (cn : Lean.Name) (x : Lean.FVarId)
    (hinv : BridgeStateInv st lenv venv)
    (hx : st.lookupFVar? x = some vid) :
    BridgeStateInv (st.setActiveCtor vid cn) (lenv.withCtor x cn) venv := by
  refine ⟨hinv.fvar_lt, hinv.fvar_val, hinv.fvar_ty, fun y v hy => ?_, hinv.fvar_inj, hinv.jp_sync⟩
  have hy' : st.lookupFVar? y = some v := hy
  cases hyx : (y == x)
  · have hne : v ≠ vid := by
      intro hvEq; rw [hvEq] at hy'
      have : y = x := hinv.fvar_inj y x vid hy' hx
      rw [← this, beq_self_eq_true] at hyx; cases hyx
    simp [LEnv.withCtor, hyx, getActiveCtor_setActiveCtor, nat_beq_false hne, hinv.fvar_ctor y v hy']
  · rw [beq_iff_eq.mp hyx] at hy'; rw [hx] at hy'
    injection hy' with hvidEq; rw [← hvidEq]
    simp only [LEnv.withCtor, hyx, getActiveCtor_setActiveCtor, beq_self_eq_true, ↓reduceIte]

theorem bridgeInv_setActiveCtorOpt (st : RealBridgeState) (lenv : LEnv) (venv : VarEnv)
    (vid : VarId) (cn? : Option Lean.Name) (x : Lean.FVarId)
    (hinv : BridgeStateInv st lenv venv)
    (hx : st.lookupFVar? x = some vid) :
    BridgeStateInv (st.setActiveCtorOpt vid cn?) (lenv.withCtorOpt x cn?) venv := by
  cases cn? with
  | some cn => exact bridgeInv_setActiveCtor st lenv venv vid cn x hinv hx
  | none =>
    refine ⟨hinv.fvar_lt, hinv.fvar_val, hinv.fvar_ty, fun y v hy => ?_, hinv.fvar_inj, hinv.jp_sync⟩
    have hy' : st.lookupFVar? y = some v := hy
    cases hyx : (y == x)
    · have hne : v ≠ vid := by
        intro hvEq; rw [hvEq] at hy'
        have : y = x := hinv.fvar_inj y x vid hy' hx
        rw [← this, beq_self_eq_true] at hyx; cases hyx
      dsimp only [LEnv.withCtorOpt, RealBridgeState.setActiveCtorOpt]
      rw [hyx]; simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hinv.fvar_ctor y v hy']
      exact (getActiveCtor_filter_ne st.activeCtor vid v hne).symm
    · rw [beq_iff_eq.mp hyx] at hy'; rw [hx] at hy'
      injection hy' with hvidEq; rw [← hvidEq]
      dsimp only [LEnv.withCtorOpt, RealBridgeState.setActiveCtorOpt]
      rw [hyx]; simp only [↓reduceIte]
      unfold RealBridgeState.getActiveCtor?
      have hnone : ∀ (l : List (VarId × Lean.Name)) (q : VarId),
          (l.filter (fun (w, _) => w != q)).find? (fun (w, _) => w == q) = none := by
        intro l q; induction l with
        | nil => rfl
        | cons hd tl ih =>
          rcases hd with ⟨w, c⟩; dsimp only [List.filter]
          cases hwu : (w != q)
          · exact ih
          · dsimp only [List.find?]
            have hwu' : (w == q) = false := by revert hwu; simp [bne]
            rw [hwu']; exact ih
      rw [hnone]; rfl

theorem bridgeInv_setJp (st : RealBridgeState) (lenv : LEnv) (venv : VarEnv)
    (j : Lean.FVarId) (ps : List (Lean.Compiler.LCNF.Param .impure)) (body : Lean.Compiler.LCNF.Code .impure)
    (hinv : BridgeStateInv st lenv venv) :
    BridgeStateInv (st.setJpDecl j ps body)
      (lenv.bindJp j { params := ps, code := body }) venv := by
  refine ⟨hinv.fvar_lt, hinv.fvar_val, hinv.fvar_ty, hinv.fvar_ctor, hinv.fvar_inj, fun q ps' body' hq => ?_⟩
  rw [lookupJp_setJpDecl] at hq
  cases hqj : (q == j) <;> rw [hqj] at hq
  · simp only [Bool.false_eq_true, ↓reduceIte] at hq
    simp [LEnv.bindJp, hqj, hinv.jp_sync q ps' body' hq]
  · simp only [↓reduceIte] at hq; injection hq with hp
    rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
    simp [LEnv.bindJp, hqj]

theorem allocZeroScalarSlotsPure_mono :
    ∀ (slots : List (Option Nat × LNIRType)) (st : RealBridgeState),
      let (_, st1) := allocZeroScalarSlotsPure st slots
      st.nextVarId ≤ st1.nextVarId ∧
      (∀ u, u < st.nextVarId → st1.getVarType u = st.getVarType u) ∧
      st1.fvarMap = st.fvarMap ∧
      st1.activeCtor = st.activeCtor ∧
      st1.jpDecls = st.jpDecls
  | [], st => ⟨Nat.le_refl _, fun _ _ => rfl, rfl, rfl, rfl⟩
  | (_, ty) :: rest, st => by
    dsimp only [allocZeroScalarSlotsPure]
    rcases freshVar_spec st ty with ⟨_, hfvNext, hfvTy, _, _, _⟩
    have hst1Eq : (st.freshVar ty).2.fvarMap = st.fvarMap ∧
        (st.freshVar ty).2.activeCtor = st.activeCtor ∧
        (st.freshVar ty).2.jpDecls = st.jpDecls := ⟨rfl, rfl, rfl⟩
    rcases allocZeroScalarSlotsPure_mono rest (st.freshVar ty).2 with ⟨hnR, htR, hfR, haR, hjR⟩
    have hbase : st.nextVarId ≤ (st.freshVar ty).2.nextVarId := by rw [hfvNext]; exact Nat.le_succ _
    refine ⟨Nat.le_trans hbase hnR, fun u hu => ?_, hfR.trans hst1Eq.1, haR.trans hst1Eq.2.1, hjR.trans hst1Eq.2.2⟩
    rw [htR u (Nat.lt_of_lt_of_le hu hbase), hfvTy u, nat_beq_false (Nat.ne_of_lt hu)]; rfl

theorem lowerCallArgsWithErasedPure_mono (ctx : RealBridgeCtx) :
    ∀ (args : List (Lean.Compiler.LCNF.Arg .impure)) (st st1 : RealBridgeState)
      (vs : List VarId) (zs : List (VarId × LNIRType)),
      lowerCallArgsWithErasedPure ctx st args = .ok (vs, zs, st1) →
      st.nextVarId ≤ st1.nextVarId ∧
      (∀ u, u < st.nextVarId → st1.getVarType u = st.getVarType u)
  | [], st, st1, _, _, h => by
    injection h with hp; rcases Prod.mk.inj hp with ⟨_, hp2⟩; rcases Prod.mk.inj hp2 with ⟨_, rfl⟩
    exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
  | a :: rest, st, st1, vs, zs, h => by
    unfold lowerCallArgsWithErasedPure at h
    cases a with
    | erased | type _ _ =>
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      rcases freshVar_spec st .unit with ⟨_, hfvNext, hfvTy, _, _, _⟩
      cases hr : lowerCallArgsWithErasedPure ctx (st.freshVar .unit).2 rest with
      | error _ => rw [hr] at h; exact nomatch h
      | ok pr =>
        rw [hr] at h; dsimp only at h; injection h with hp
        rcases Prod.mk.inj hp with ⟨_, hp2⟩; rcases Prod.mk.inj hp2 with ⟨_, rfl⟩
        rcases lowerCallArgsWithErasedPure_mono ctx rest (st.freshVar .unit).2 pr.2.2 pr.1 pr.2.1 hr with ⟨hnR, htR⟩
        have hbase : st.nextVarId ≤ (st.freshVar .unit).2.nextVarId := by rw [hfvNext]; exact Nat.le_succ _
        refine ⟨Nat.le_trans hbase hnR, fun u hu => ?_⟩
        rw [htR u (Nat.lt_of_lt_of_le hu hbase), hfvTy u, nat_beq_false (Nat.ne_of_lt hu)]; rfl
    | fvar x =>
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      cases ha : lowerRealArg ctx st (.fvar x) true with
      | error _ => rw [ha] at h; exact nomatch h
      | ok pa =>
        rw [ha] at h; rcases pa with ⟨v0, stA⟩
        have hstA := lowerRealArg_st_eq ctx st stA (.fvar x) true v0 ha; subst stA
        dsimp only at h
        cases hr : lowerCallArgsWithErasedPure ctx st rest with
        | error _ => rw [hr] at h; exact nomatch h
        | ok pr =>
          rw [hr] at h; dsimp only at h; injection h with hp
          rcases Prod.mk.inj hp with ⟨_, hp2⟩; rcases Prod.mk.inj hp2 with ⟨_, rfl⟩
          exact lowerCallArgsWithErasedPure_mono ctx rest st pr.2.2 pr.1 pr.2.1 hr

theorem bindJpCallArgsPure_mono (ctx : RealBridgeCtx) :
    ∀ (ps : List (Lean.Compiler.LCNF.Param .impure)) (as_ : List (Lean.Compiler.LCNF.Arg .impure))
      (st st1 : RealBridgeState) (binds : List (Lean.FVarId × VarId × LNIRType × Option VarId)),
      bindJpCallArgsPure ctx st ps as_ = .ok (binds, st1) →
      st.nextVarId ≤ st1.nextVarId ∧
      (∀ u, u < st.nextVarId → st1.getVarType u = st.getVarType u) ∧
      (∀ b ∈ binds, st.nextVarId ≤ b.2.1 ∧ b.2.1 < st1.nextVarId)
  | [], [], st, st1, binds, h => by
    injection h with hp; rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
    exact ⟨Nat.le_refl _, fun _ _ => rfl, fun _ hb => nomatch hb⟩
  | [], _ :: _, _, _, _, h => by exact nomatch h
  | _ :: _, [], _, _, _, h => by exact nomatch h
  | p :: ps, a :: as_, st, st1, binds, h => by
    unfold bindJpCallArgsPure at h
    let rawPTy := lowerGroundImpureTypeWith ctx p.type
    have hex : ∃ (pTy : LNIRType) (argOpt : Option VarId)
        (pr : List (Lean.FVarId × VarId × LNIRType × Option VarId) × RealBridgeState),
        bindJpCallArgsPure ctx (st.freshVar pTy).2 ps as_ = .ok pr ∧
        binds = (p.fvarId, (st.freshVar pTy).1, pTy, argOpt) :: pr.1 ∧ st1 = pr.2 := by
      cases a with
      | erased =>
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
        let pTy := if !ctx.allowStage1DHeap && isHeapPtrType rawPTy then .i64 else rawPTy
        cases hr : bindJpCallArgsPure ctx (st.freshVar pTy).2 ps as_ with
        | error _ => rw [hr] at h; exact nomatch h
        | ok pr =>
          rw [hr] at h; injection h with hp; rcases Prod.mk.inj hp with ⟨hb, hs⟩
          exact ⟨pTy, none, pr, hr, hb.symm, hs.symm⟩
      | type _ _ =>
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
        let pTy := if !ctx.allowStage1DHeap && isHeapPtrType rawPTy then .i64 else rawPTy
        cases hr : bindJpCallArgsPure ctx (st.freshVar pTy).2 ps as_ with
        | error _ => rw [hr] at h; exact nomatch h
        | ok pr =>
          rw [hr] at h; injection h with hp; rcases Prod.mk.inj hp with ⟨hb, hs⟩
          exact ⟨pTy, none, pr, hr, hb.symm, hs.symm⟩
      | fvar x =>
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map] at h
        cases ha : lowerRealArg ctx st (.fvar x) true with
        | error _ => rw [ha] at h; exact nomatch h
        | ok pa =>
          rw [ha] at h; rcases pa with ⟨v0, stA⟩
          have hstA := lowerRealArg_st_eq ctx st stA (.fvar x) true v0 ha; subst stA
          dsimp only at h
          let pTy := if isUnboxedScalarOrTuple (st.getVarType v0) && isHeapPtrType rawPTy then st.getVarType v0 else rawPTy
          cases hr : bindJpCallArgsPure ctx (st.freshVar pTy).2 ps as_ with
          | error _ => rw [hr] at h; exact nomatch h
          | ok pr =>
            rw [hr] at h; injection h with hp; rcases Prod.mk.inj hp with ⟨hb, hs⟩
            exact ⟨pTy, some v0, pr, hr, hb.symm, hs.symm⟩
    rcases hex with ⟨pTy, argOpt, pr, hr, rfl, rfl⟩
    rcases freshVar_spec st pTy with ⟨hfv1, hfvNext, hfvTy, _, _, _⟩
    have hbaseSt : st.nextVarId ≤ (st.freshVar pTy).2.nextVarId := by rw [hfvNext]; exact Nat.le_succ _
    rcases bindJpCallArgsPure_mono ctx ps as_ (st.freshVar pTy).2 pr.2 pr.1 hr with ⟨hnextR, htyR, hmemR⟩
    refine ⟨Nat.le_trans hbaseSt hnextR, fun u hu => ?_, fun b hb => ?_⟩
    · rw [htyR u (Nat.lt_of_lt_of_le hu hbaseSt), hfvTy u, nat_beq_false (Nat.ne_of_lt hu)]; rfl
    · cases List.mem_cons.mp hb with
      | inl hhead =>
        subst hhead; dsimp only; rw [hfv1]
        exact ⟨Nat.le_refl _, Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hnextR⟩
      | inr htail =>
        rcases hmemR b htail with ⟨hlo, hhi⟩
        exact ⟨Nat.le_trans (Nat.le_succ _) hlo, hhi⟩

theorem applyJpParamMapPure_mono (base : VarId) :
    ∀ (binds : List (Lean.FVarId × VarId × LNIRType × Option VarId)) (st : RealBridgeState),
      base ≤ st.nextVarId →
      (∀ b ∈ binds, base ≤ b.2.1) →
      (applyJpParamMapPure st binds).nextVarId = st.nextVarId ∧
      (∀ u, u < base → (applyJpParamMapPure st binds).getVarType u = st.getVarType u)
  | [], st, _, _ => ⟨rfl, fun _ _ => rfl⟩
  | (fvarId, freshVid, pTy, argVid) :: rest, st, hbase, hmem => by
    dsimp only [applyJpParamMapPure]
    have hfvGe : base ≤ freshVid := (hmem (fvarId, freshVid, pTy, argVid) (.head _))
    let st1 : RealBridgeState := { (st.setVarType freshVid pTy) with
      fvarMap := (fvarId, freshVid) :: st.fvarMap.filter (fun (f, _) => f != fvarId)
      activeCtor := st.activeCtor.filter (fun (v, _) => v != freshVid) }
    have hst1Next : st1.nextVarId = st.nextVarId := rfl
    rcases applyJpParamMapPure_mono base rest st1 (by rw [hst1Next]; exact hbase) (fun b hb => hmem b (.tail _ hb)) with ⟨hn, ht⟩
    refine ⟨hn.trans hst1Next, fun u hu => ?_⟩
    rw [ht u hu]
    change (st.setVarType freshVid pTy).getVarType u = st.getVarType u
    rw [getVarType_setVarType, nat_beq_false (Nat.ne_of_lt (Nat.lt_of_lt_of_le hu hfvGe))]; rfl


end LeanNative.Proofs
