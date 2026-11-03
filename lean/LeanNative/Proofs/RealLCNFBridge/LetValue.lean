import LeanNative.Proofs.RealLCNFBridge.CtorIntrinsic

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

theorem lookupBoundFVar_inv (st : RealBridgeState) (lenv : LEnv) (venv : VarEnv)
    (x : Lean.FVarId) (vid : VarId) (hinv : BridgeStateInv st lenv venv)
    (h : st.lookupBoundFVar x = .ok vid) :
    st.lookupFVar? x = some vid ∧ vid < st.nextVarId ∧
    (∃ val, lenv.vals x = some val ∧ venv vid = some val) ∧
    lenv.tys x = some (st.getVarType vid) ∧
    lenv.ctors x = st.getActiveCtor? vid := by
  unfold RealBridgeState.lookupBoundFVar at h
  cases hlu : st.lookupFVar? x with
  | none => rw [hlu] at h; exact nomatch h
  | some v0 =>
    rw [hlu] at h; injection h with hv; subst v0
    rcases hinv.fvar_val x vid hlu with ⟨hveq, his⟩
    cases hvv : venv vid with
    | none => rw [hvv] at his; cases his
    | some val =>
      exact ⟨rfl, hinv.fvar_lt x vid hlu, ⟨val, hveq.trans hvv, rfl⟩,
        hinv.fvar_ty x vid hlu, hinv.fvar_ctor x vid hlu⟩

private theorem inferRhs_scalar_nonVar (st : RealBridgeState) (se : ScalarExpr) (rawTy : LNIRType)
    (hnv : ∀ u, se ≠ .var u) :
    inferImpureRhsTypePure st (.scalar se) rawTy false =
      if isUnboxedScalarOrTuple rawTy then rawTy else .i64 := by
  cases se <;> first | rfl | exact False.elim (hnv _ rfl)

theorem unboxed_not_heap (vt : LNIRType) (h : isUnboxedScalarOrTuple vt = true) :
    isHeapPtrType vt = false := by
  cases vt <;> first | rfl | cases h

private theorem tuple_not_objPtr (fs : List LNIRType) : lnirTypeEq (.tuple fs) .objPtr = false := by
  cases h : lnirTypeEq (.tuple fs) .objPtr
  · rfl
  · exact False.elim (by cases lnirTypeEq_sound _ _ h)

private theorem unboxedOrI64_not_objPtr (rawTy : LNIRType) :
    lnirTypeEq (if isUnboxedScalarOrTuple rawTy then rawTy else .i64) .objPtr = false := by
  cases rawTy with
  | tuple fs => split <;> first | rfl | exact tuple_not_objPtr fs
  | _ => rfl

private theorem evalCtorGet_fieldGet_match (venv : VarEnv) (hst hst' : HeapState)
    (vid : VarId) (val : Val) (idx : Nat) (isObj : Bool) (v : Val) (ctor? : Option Lean.Name)
    (hvalV : venv vid = some val)
    (ho : (match val with
      | .objPtr objId => (hst.liveHeapObj objId).bind fun o =>
          (fieldGet (if isObj then o.objFields else o.scalarFields) idx).map (·, hst, none)
      | .tuple (_ :: vals) => (fieldGet vals idx).map (·, hst, none)
      | .tuple [] => .error (.outOfBounds idx 0)
      | _ => .error (.typeError "ctorGet expects heap constructor or constructor tuple")) = .ok (v, hst', ctor?)) :
    evalCtorGet venv hst vid idx isObj = .ok (v, hst') := by
  unfold evalCtorGet
  rw [hvalV]
  cases val with
  | objPtr objId =>
    dsimp only at ho ⊢
    cases hlive : hst.liveHeapObj objId with
    | error _ => rw [hlive] at ho; exact nomatch ho
    | ok o =>
      rw [hlive] at ho; dsimp only [Bind.bind, Except.bind, Functor.map, Except.map, fieldGet] at ho ⊢
      cases hf : (if isObj then o.objFields else o.scalarFields)[idx]? with
      | none => rw [hf] at ho; exact nomatch ho
      | some fv =>
        rw [hf] at ho; dsimp only at ho ⊢; injection ho with hp
        rcases Prod.mk.inj hp with ⟨rfl, hp2⟩; rcases Prod.mk.inj hp2 with ⟨rfl, _⟩; rfl
  | tuple vs =>
    cases vs with
    | nil => exact nomatch ho
    | cons _ vals =>
      dsimp only [Functor.map, Except.map, fieldGet] at ho ⊢
      cases hf : vals[idx]? with
      | none => rw [hf] at ho; exact nomatch ho
      | some fv =>
        rw [hf] at ho; dsimp only at ho ⊢; injection ho with hp
        rcases Prod.mk.inj hp with ⟨rfl, hp2⟩; rcases Prod.mk.inj hp2 with ⟨rfl, _⟩; rfl
  | _ => exact nomatch ho

/-- Soundness of pure `LetValue .impure` lowering (`lowerImpureLetValuePure`) against `evalLetValue`. -/
theorem lowerImpureLetValuePure_sound (ctx : RealBridgeCtx) (st : RealBridgeState) (lenv : LEnv)
    (venv : VarEnv) (hst hst' : HeapState) (lv : Lean.Compiler.LCNF.LetValue .impure)
    (rawTy : LNIRType) (expr : LNIRExpr) (st1 : RealBridgeState)
    (v : Val) (ctor? : Option Lean.Name) :
    let expectedTy := match lv with
      | .ctor info args _ | .reuse _ info _ args _ =>
        if args.isEmpty then (if isUnboxedScalarOrTuple rawTy then rawTy else .i64)
        else if ctor?.isSome then .objPtr
        else match ctx.findTupleArity? info.name with
          | some numFields =>
            .tuple ((args.toList.drop (if args.size > numFields then args.size - numFields else 0)).map fun
              | .fvar x => (lenv.tys x).getD .objPtr
              | _ => .objPtr)
          | none => rawTy
      | .box _ x _ =>
        if isUnboxedScalarOrTuple ((lenv.tys x).getD .objPtr) then (lenv.tys x).getD .objPtr else .i64
      | .fvar x _ | .unbox x _ | .reset _ x _ =>
        if isUnboxedScalarOrTuple rawTy then rawTy
        else if isUnboxedScalarOrTuple ((lenv.tys x).getD .objPtr) then (lenv.tys x).getD .objPtr else rawTy
      | .oproj idx x _ =>
        match (lenv.tys x).getD .objPtr with
        | .tuple fs => if isUnboxedScalarOrTuple rawTy then rawTy else fs[idx]?.getD .i64
        | _ => rawTy
      | .uproj idx x _ =>
        match (lenv.tys x).getD .objPtr with
        | .tuple fs => if isUnboxedScalarOrTuple rawTy then rawTy else fs[idx]?.getD .i64
        | _ => rawTy
      | .sproj _ off x _ =>
        match (lenv.tys x).getD .objPtr with
        | .tuple fs => if isUnboxedScalarOrTuple rawTy then rawTy else fs[off]?.getD .i64
        | _ => rawTy
      | .isShared x _ =>
        if isUnboxedScalarOrTuple ((lenv.tys x).getD .objPtr) then
          if isUnboxedScalarOrTuple rawTy then rawTy else .i64
        else .i1
      | .lit _ | .erased =>
        if isUnboxedScalarOrTuple rawTy then rawTy else .i64
      | .fap _ _ _ =>
        if isUnboxedScalarOrTuple rawTy then rawTy else .i64
      | .pap _ _ _ => rawTy
    let isBox := match lv with | .box _ _ _ => true | _ => false
    BridgeStateInv st lenv venv →
    lowerImpureLetValuePure ctx st lv rawTy = .ok (expr, st1) →
    evalLetValue ctx lenv hst lv rawTy = .ok (v, hst', ctor?) →
    st1 = st ∧
    (match expr with
     | .isExclusive _ => ∃ b, evalExpr venv hst expr = .ok (.bool b, hst') ∧ v = .bool (!b)
     | _ => evalExpr venv hst expr = .ok (v, hst')) ∧
    inferImpureRhsTypePure st expr rawTy isBox = expectedTy ∧
    (∀ info args h, lv = .ctor info args h →
      lnirTypeEq (inferImpureRhsTypePure st expr rawTy false) .objPtr = true →
      ctor? = some info.name) := by
  intro expectedTy isBox hinv h_lower h_eval
  dsimp only [expectedTy, isBox]
  cases lv with
  | lit litVal =>
    dsimp only [lowerImpureLetValuePure, Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
    dsimp only [evalLetValue, Functor.map, Except.map] at h_eval
    cases hl : lowerLitValuePure litVal rawTy ctx.arch true with
    | error _ => rw [hl] at h_lower; exact nomatch h_lower
    | ok e0 =>
      rw [hl] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
      cases he : evalLit ctx.arch litVal rawTy true with
      | error _ => rw [he] at h_eval; exact nomatch h_eval
      | ok v0 =>
        rw [he] at h_eval; injection h_eval with hp2
        rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, rfl⟩
        rcases lowerLitValuePure_sound ctx.arch litVal rawTy true e0 v0 venv hst hl he with ⟨heval, se, rfl, hnv⟩
        exact ⟨rfl, heval, inferRhs_scalar_nonVar st se rawTy hnv, fun _ _ _ hc => nomatch hc⟩
  | erased =>
    dsimp only [lowerImpureLetValuePure, Pure.pure, Except.pure] at h_lower
    dsimp only [evalLetValue] at h_eval
    injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
    injection h_eval with hp2; rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, rfl, fun _ _ _ hc => nomatch hc⟩
  | fvar x args =>
    dsimp only [lowerImpureLetValuePure, Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
    dsimp only [evalLetValue] at h_eval
    cases hemp : (!args.isEmpty)
    · simp only [hemp, Bool.false_eq_true, ↓reduceIte] at h_lower h_eval
      cases hb : st.lookupBoundFVar x with
      | error _ => rw [hb] at h_lower; exact nomatch h_lower
      | ok vid =>
        rw [hb] at h_lower; dsimp only at h_lower
        injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
        rcases lookupBoundFVar_inv st lenv venv x vid hinv hb with ⟨_, _, ⟨val, hvalL, hvalV⟩, htyL, _⟩
        rw [hvalL] at h_eval; injection h_eval with hp2
        rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, rfl⟩
        exact ⟨rfl, evalExpr_scalar venv hst (.var vid) val (evalScalar_var venv vid val hvalV),
          by simp [inferImpureRhsTypePure, htyL], fun _ _ _ hc => nomatch hc⟩
    · simp [hemp] at h_eval
  | ctor info args h =>
    dsimp only [lowerImpureLetValuePure] at h_lower
    dsimp only [evalLetValue] at h_eval
    rcases lowerRealCtor_sound ctx st lenv venv info.name info.cidx args.toList rawTy expr st1 v hst hst' ctor? hinv h_lower h_eval with
      ⟨heval, rfl, hemptyCase, hnonEmptyCase⟩
    have hempEq : args.isEmpty = args.toList.isEmpty := by
      cases args with | mk l => dsimp [Array.isEmpty, Array.size]; cases l <;> rfl
    cases hemp : args.toList.isEmpty
    · rcases hnonEmptyCase hemp with ⟨argVars, rfl, rfl⟩ | ⟨numFields, argVars, hfind, rfl, rfl, hmap⟩
      · refine ⟨rfl, heval, ?_, fun info' _ _ hc _ => by cases hc; rfl⟩
        simp [inferImpureRhsTypePure, hempEq, hemp]
      · refine ⟨rfl, heval, ?_, fun _ _ _ _ hty => False.elim (by cases lnirTypeEq_sound _ _ hty)⟩
        have hsize : args.size = args.toList.length := rfl
        dsimp only [inferImpureRhsTypePure, Bool.false_eq_true, ↓reduceIte, Option.isSome]
        rw [hempEq, hemp, hfind, hsize, hmap]; rfl
    · rcases hemptyCase hemp with ⟨⟨se, rfl, hnv⟩, rfl⟩
      refine ⟨rfl, heval, ?_, fun _ _ _ _ hty => ?_⟩
      · simp [hempEq, hemp, inferRhs_scalar_nonVar st1 se rawTy hnv]
      · rw [inferRhs_scalar_nonVar st1 se rawTy hnv, unboxedOrI64_not_objPtr rawTy] at hty; cases hty
  | reuse slotFVar info upd args h =>
    dsimp only [lowerImpureLetValuePure, Bind.bind, Except.bind] at h_lower
    dsimp only [evalLetValue] at h_eval
    cases hb : st.lookupBoundFVar slotFVar with
    | error _ => rw [hb] at h_lower; exact nomatch h_lower
    | ok sv =>
      rw [hb] at h_lower; dsimp only at h_lower
      cases hunb : isUnboxedScalarOrTuple (st.getVarType sv)
      · rw [hunb] at h_lower; exact nomatch h_lower
      · rw [hunb] at h_lower; simp only [↓reduceIte] at h_lower
        rcases lowerRealCtor_sound ctx st lenv venv info.name info.cidx args.toList rawTy expr st1 v hst hst' ctor? hinv h_lower h_eval with
          ⟨heval, rfl, hemptyCase, hnonEmptyCase⟩
        have hempEq : args.isEmpty = args.toList.isEmpty := by
          cases args with | mk l => dsimp [Array.isEmpty, Array.size]; cases l <;> rfl
        cases hemp : args.toList.isEmpty
        · rcases hnonEmptyCase hemp with ⟨argVars, rfl, rfl⟩ | ⟨numFields, argVars, hfind, rfl, rfl, hmap⟩
          · exact ⟨rfl, heval, by simp [inferImpureRhsTypePure, hempEq, hemp], fun _ _ _ hc => nomatch hc⟩
          · have hsize : args.size = args.toList.length := rfl
            refine ⟨rfl, heval, ?_, fun _ _ _ hc => nomatch hc⟩
            dsimp only [inferImpureRhsTypePure, Bool.false_eq_true, ↓reduceIte, Option.isSome]
            rw [hempEq, hemp, hfind, hsize, hmap]; rfl
        · rcases hemptyCase hemp with ⟨⟨se, rfl, hnv⟩, rfl⟩
          exact ⟨rfl, heval, by simp [hempEq, hemp, inferRhs_scalar_nonVar st1 se rawTy hnv], fun _ _ _ hc => nomatch hc⟩
  | oproj idx x h =>
    dsimp only [lowerImpureLetValuePure, Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
    dsimp only [evalLetValue] at h_eval
    cases hb : st.lookupBoundFVar x with
    | error _ => rw [hb] at h_lower; exact nomatch h_lower
    | ok vid =>
      rw [hb] at h_lower; dsimp only at h_lower
      rcases lookupBoundFVar_inv st lenv venv x vid hinv hb with ⟨_, _, ⟨val, hvalL, hvalV⟩, htyL, _⟩
      have hisTup : lenv.isTupleVar x = (match st.getVarType vid with | .tuple _ => true | _ => false) := by
        dsimp [LEnv.isTupleVar]; rw [htyL]
        cases st.getVarType vid <;> rfl
      cases hvt : st.getVarType vid with
      | tuple fs =>
        rw [hvt] at h_lower hisTup; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
        rw [hisTup, hvalL] at h_eval
        refine ⟨rfl, ?_, by simp [inferImpureRhsTypePure, hvt, htyL], fun _ _ _ hc => nomatch hc⟩
        dsimp only [evalExpr]; rw [hvalV]
        cases val with
        | tuple vs =>
          dsimp only [↓reduceIte, Functor.map, Except.map, fieldGet] at h_eval ⊢
          cases hf : vs[idx]? with
          | none => rw [hf] at h_eval; exact nomatch h_eval
          | some fv =>
            rw [hf] at h_eval; dsimp only at h_eval ⊢; injection h_eval with hp2
            rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, _⟩; rfl
        | _ => simp at h_eval
      | objPtr | taggedPtr =>
        rw [hvt] at h_lower hisTup; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
        rw [hisTup, hvalL] at h_eval
        refine ⟨rfl, ?_, by simp [inferImpureRhsTypePure, hvt, htyL], fun _ _ _ hc => nomatch hc⟩
        dsimp only [evalExpr]
        apply evalCtorGet_fieldGet_match venv hst hst' vid val idx true v ctor? hvalV
        cases val with
        | objPtr _ => dsimp only [Bool.false_eq_true, ↓reduceIte] at h_eval ⊢; exact h_eval
        | tuple vs => cases vs <;> dsimp only [Bool.false_eq_true, ↓reduceIte] at h_eval ⊢ <;> exact h_eval
        | _ => simp at h_eval
      | _ => rw [hvt] at h_lower; exact nomatch h_lower
  | uproj idx x h =>
    dsimp only [lowerImpureLetValuePure, Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
    dsimp only [evalLetValue] at h_eval
    cases hb : st.lookupBoundFVar x with
    | error _ => rw [hb] at h_lower; exact nomatch h_lower
    | ok vid =>
      rw [hb] at h_lower; dsimp only at h_lower
      rcases lookupBoundFVar_inv st lenv venv x vid hinv hb with ⟨_, _, ⟨val, hvalL, hvalV⟩, htyL, hctorL⟩
      have hisTup : lenv.isTupleVar x = (match st.getVarType vid with | .tuple _ => true | _ => false) := by
        dsimp [LEnv.isTupleVar]; rw [htyL]
        cases st.getVarType vid <;> rfl
      cases hvt : st.getVarType vid with
      | tuple fs =>
        rw [hvt] at h_lower hisTup; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
        rw [hisTup, hvalL] at h_eval
        refine ⟨rfl, ?_, by simp [inferImpureRhsTypePure, hvt, htyL], fun _ _ _ hc => nomatch hc⟩
        dsimp only [evalExpr]; rw [hvalV]
        cases val with
        | tuple vs =>
          dsimp only [↓reduceIte, fieldGet, Functor.map, Except.map] at h_eval ⊢
          cases hf : vs[idx]? with
          | none => simp [hf] at h_eval
          | some fv =>
            simp only [hf, ↓reduceIte] at h_eval ⊢; injection h_eval with hp2
            rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, _⟩; rfl
        | _ => simp at h_eval
      | _ =>
        rw [hvt] at h_lower hisTup; dsimp only at h_lower
        split at h_lower
        · exact nomatch h_lower
        · cases hcname : st.getActiveCtor? vid with
          | none => rw [hcname] at h_lower; exact nomatch h_lower
          | some cname =>
            rw [hcname] at h_lower; dsimp only at h_lower
            cases hlay : ctx.findLayout? cname with
            | none => rw [hlay] at h_lower; exact nomatch h_lower
            | some spec =>
              rw [hlay] at h_lower; dsimp only at h_lower
              cases hsl : spec.usizeSlot? idx with
              | none => rw [hsl] at h_lower; exact nomatch h_lower
              | some slPair =>
                rcases slPair with ⟨slot, ty⟩
                rw [hsl] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
                rw [hisTup, hvalL] at h_eval
                refine ⟨rfl, ?_, by simp [inferImpureRhsTypePure, htyL, hvt], fun _ _ _ hc => nomatch hc⟩
                dsimp only [evalExpr]
                apply evalCtorGet_fieldGet_match venv hst hst' vid val slot false v ctor? hvalV
                rw [hctorL, hcname] at h_eval; dsimp only [Bind.bind, Option.bind] at h_eval
                rw [hlay] at h_eval; dsimp only at h_eval
                rw [hsl] at h_eval; dsimp only at h_eval
                cases val with
                | objPtr _ => dsimp only [Bool.false_eq_true, ↓reduceIte] at h_eval ⊢; exact h_eval
                | tuple vs => cases vs <;> dsimp only [Bool.false_eq_true, ↓reduceIte] at h_eval ⊢ <;> exact h_eval
                | _ => simp at h_eval
  | sproj n off x h =>
    dsimp only [lowerImpureLetValuePure, Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
    dsimp only [evalLetValue] at h_eval
    cases hb : st.lookupBoundFVar x with
    | error _ => rw [hb] at h_lower; exact nomatch h_lower
    | ok vid =>
      rw [hb] at h_lower; dsimp only at h_lower
      rcases lookupBoundFVar_inv st lenv venv x vid hinv hb with ⟨_, _, ⟨val, hvalL, hvalV⟩, htyL, hctorL⟩
      have hisTup : lenv.isTupleVar x = (match st.getVarType vid with | .tuple _ => true | _ => false) := by
        dsimp [LEnv.isTupleVar]; rw [htyL]
        cases st.getVarType vid <;> rfl
      cases hvt : st.getVarType vid with
      | tuple fs =>
        rw [hvt] at h_lower hisTup; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
        rw [hisTup, hvalL] at h_eval
        refine ⟨rfl, ?_, by simp [inferImpureRhsTypePure, hvt, htyL], fun _ _ _ hc => nomatch hc⟩
        dsimp only [evalExpr]; rw [hvalV]
        cases val with
        | tuple vs =>
          dsimp only [↓reduceIte, fieldGet, Functor.map, Except.map] at h_eval ⊢
          cases hf : vs[off]? with
          | none => simp [hf] at h_eval
          | some fv =>
            simp only [hf, ↓reduceIte] at h_eval ⊢; injection h_eval with hp2
            rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, _⟩; rfl
        | _ => simp at h_eval
      | _ =>
        rw [hvt] at h_lower hisTup; dsimp only at h_lower
        split at h_lower
        · exact nomatch h_lower
        · cases hcname : st.getActiveCtor? vid with
          | none => rw [hcname] at h_lower; exact nomatch h_lower
          | some cname =>
            rw [hcname] at h_lower; dsimp only at h_lower
            cases hlay : ctx.findLayout? cname with
            | none => rw [hlay] at h_lower; exact nomatch h_lower
            | some spec =>
              rw [hlay] at h_lower; dsimp only at h_lower
              cases hsl : spec.scalarSlot? n off with
              | none => rw [hsl] at h_lower; exact nomatch h_lower
              | some slPair =>
                rcases slPair with ⟨slot, ty⟩
                rw [hsl] at h_lower; dsimp only at h_lower
                cases hteq : (!lnirTypeEq rawTy ty)
                · rw [hteq] at h_lower; simp only [Bool.false_eq_true, ↓reduceIte] at h_lower
                  injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
                  rw [hisTup, hvalL] at h_eval
                  refine ⟨rfl, ?_, by simp [inferImpureRhsTypePure, htyL, hvt], fun _ _ _ hc => nomatch hc⟩
                  dsimp only [evalExpr]
                  apply evalCtorGet_fieldGet_match venv hst hst' vid val slot false v ctor? hvalV
                  rw [hctorL, hcname] at h_eval; dsimp only [Bind.bind, Option.bind] at h_eval
                  rw [hlay] at h_eval; dsimp only at h_eval
                  rw [hsl] at h_eval; dsimp only at h_eval
                  cases val with
                  | objPtr _ => dsimp only [Bool.false_eq_true, ↓reduceIte] at h_eval ⊢; exact h_eval
                  | tuple vs => cases vs <;> dsimp only [Bool.false_eq_true, ↓reduceIte] at h_eval ⊢ <;> exact h_eval
                  | _ => simp at h_eval
                · rw [hteq] at h_lower; exact nomatch h_lower
  | fap fn args h =>
    dsimp only [lowerImpureLetValuePure, Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
    cases hargL : lowerRealArgList ctx st false args.toList with
    | error _ => rw [hargL] at h_lower; exact nomatch h_lower
    | ok pair =>
      rcases pair with ⟨argVars, stA⟩
      rw [hargL] at h_lower; dsimp only at h_lower
      cases hintr : lowerCanonicalIntrinsicPure? fn argVars rawTy (argVars.map stA.getVarType) false ctx.arch with
      | none => rw [hintr] at h_lower; exact nomatch h_lower
      | some e0 =>
        rw [hintr] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
        rcases lowerCanonicalIntrinsicPure_sound ctx st lenv venv hst hst' fn args h argVars stA
            rawTy e0 v ctor? hinv hargL hintr h_eval with
          ⟨heval, rfl, rfl, rfl, se, rfl, hnv⟩
        exact ⟨rfl, heval, inferRhs_scalar_nonVar stA se rawTy hnv, fun _ _ _ hc => nomatch hc⟩
  | pap fn _ _ =>
    dsimp only [evalLetValue] at h_eval; exact nomatch h_eval
  | proj _ _ _ h | const _ _ _ h => cases h
  | box _ x _ =>
    dsimp only [lowerImpureLetValuePure, Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
    dsimp only [evalLetValue] at h_eval
    cases hb : st.lookupBoundFVar x with
    | error _ => rw [hb] at h_lower; exact nomatch h_lower
    | ok vid =>
      rw [hb] at h_lower; dsimp only at h_lower
      cases hok : (isUnboxedScalarOrTuple (st.getVarType vid) || isHeapPtrType (st.getVarType vid))
      · rw [hok] at h_lower; exact nomatch h_lower
      · rw [hok] at h_lower; simp only [↓reduceIte] at h_lower
        injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
        rcases lookupBoundFVar_inv st lenv venv x vid hinv hb with ⟨_, _, ⟨val, hvalL, hvalV⟩, htyL, _⟩
        rw [hvalL] at h_eval; injection h_eval with hp2
        rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, rfl⟩
        exact ⟨rfl, evalExpr_scalar venv hst (.var vid) val (evalScalar_var venv vid val hvalV),
          by simp [inferImpureRhsTypePure, htyL], fun _ _ _ hc => nomatch hc⟩
  | unbox x _ =>
    dsimp only [lowerImpureLetValuePure, Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
    dsimp only [evalLetValue] at h_eval
    cases hb : st.lookupBoundFVar x with
    | error _ => rw [hb] at h_lower; exact nomatch h_lower
    | ok vid =>
      rw [hb] at h_lower; dsimp only at h_lower
      cases hok : (isUnboxedScalarOrTuple (st.getVarType vid) || isHeapPtrType (st.getVarType vid))
      · rw [hok] at h_lower; exact nomatch h_lower
      · rw [hok] at h_lower; simp only [↓reduceIte] at h_lower
        injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
        rcases lookupBoundFVar_inv st lenv venv x vid hinv hb with ⟨_, _, ⟨val, hvalL, hvalV⟩, htyL, _⟩
        rw [hvalL] at h_eval; injection h_eval with hp2
        rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, rfl⟩
        exact ⟨rfl, evalExpr_scalar venv hst (.var vid) val (evalScalar_var venv vid val hvalV),
          by simp [inferImpureRhsTypePure, htyL], fun _ _ _ hc => nomatch hc⟩
  | reset _ x _ =>
    dsimp only [lowerImpureLetValuePure, Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
    dsimp only [evalLetValue] at h_eval
    cases hb : st.lookupBoundFVar x with
    | error _ => rw [hb] at h_lower; exact nomatch h_lower
    | ok vid =>
      rw [hb] at h_lower; dsimp only at h_lower
      cases hok : isUnboxedScalarOrTuple (st.getVarType vid)
      · rw [hok] at h_lower; exact nomatch h_lower
      · rw [hok] at h_lower; simp only [↓reduceIte] at h_lower
        injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
        rcases lookupBoundFVar_inv st lenv venv x vid hinv hb with ⟨_, _, ⟨val, hvalL, hvalV⟩, htyL, _⟩
        rw [hvalL] at h_eval; injection h_eval with hp2
        rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, rfl⟩
        exact ⟨rfl, evalExpr_scalar venv hst (.var vid) val (evalScalar_var venv vid val hvalV),
          by simp [inferImpureRhsTypePure, htyL], fun _ _ _ hc => nomatch hc⟩
  | isShared x _ =>
    dsimp only [lowerImpureLetValuePure, Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
    dsimp only [evalLetValue] at h_eval
    cases hb : st.lookupBoundFVar x with
    | error _ => rw [hb] at h_lower; exact nomatch h_lower
    | ok vid =>
      rw [hb] at h_lower; dsimp only at h_lower
      rcases lookupBoundFVar_inv st lenv venv x vid hinv hb with ⟨_, _, ⟨val, hvalL, hvalV⟩, htyL, _⟩
      cases hunb : isUnboxedScalarOrTuple (st.getVarType vid)
      · rw [hunb] at h_lower; simp only [Bool.false_eq_true, ↓reduceIte] at h_lower
        cases hhp : (ctx.allowStage1DHeap && isHeapPtrType (st.getVarType vid))
        · rw [hhp] at h_lower; exact nomatch h_lower
        · rw [hhp] at h_lower; simp only [↓reduceIte] at h_lower
          injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
          have hisH : lenv.isHeapVar x = true := by
            dsimp [LEnv.isHeapVar]; rw [htyL]; exact (Bool.and_eq_true_iff.mp hhp).2
          rw [hisH] at h_eval; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h_eval
          rw [hvalL] at h_eval
          refine ⟨rfl, ?_, by simp [inferImpureRhsTypePure, htyL, hunb], fun _ _ _ hc => nomatch hc⟩
          dsimp only [evalExpr]; rw [hvalV]
          cases val with
          | objPtr objId =>
            dsimp only at h_eval ⊢
            cases hrc : (hst.getObjRefCount objId == 0)
            · simp only [hrc, Bool.false_eq_true, ↓reduceIte] at h_eval ⊢
              injection h_eval with hp2; rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, _⟩
              exact ⟨hst.getObjRefCount objId == 1, rfl, rfl⟩
            · simp [hrc] at h_eval
          | sarrayId bufId =>
            dsimp only at h_eval ⊢
            cases hbuf : hst.findBuffer bufId with
            | none => simp [hbuf] at h_eval
            | some buf =>
              simp only [hbuf] at h_eval ⊢; injection h_eval with hp2
              rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, _⟩
              exact ⟨buf.exclusive, rfl, rfl⟩
          | _ =>
            injection h_eval with hp2; rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, _⟩
            exact ⟨true, rfl, rfl⟩
      · rw [hunb] at h_lower; simp only [↓reduceIte] at h_lower
        injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
        have hisH : lenv.isHeapVar x = false := by
          dsimp [LEnv.isHeapVar]; rw [htyL]; exact unboxed_not_heap _ hunb
        rw [hisH] at h_eval; simp only [Bool.not_false, ↓reduceIte] at h_eval
        injection h_eval with hp2; rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, _⟩
        exact ⟨rfl, rfl, by simp [inferImpureRhsTypePure, htyL, hunb], fun _ _ _ hc => nomatch hc⟩


end LeanNative.Proofs
