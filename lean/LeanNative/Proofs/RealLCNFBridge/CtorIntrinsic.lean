import LeanNative.Proofs.RealLCNFBridge.UnaryCast

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

private theorem lowerRealCtor_nullary (ctx : RealBridgeCtx) (st : RealBridgeState) (lenv : LEnv) (venv : VarEnv)
    (ctorName : Lean.Name) (cidx : Nat) (retTy : LNIRType) (expr : LNIRExpr) (st' : RealBridgeState)
    (v : Val) (hst hst' : HeapState) (ctor? : Option Lean.Name)
    (h_lower : lowerRealCtor ctx st ctorName cidx [] retTy = .ok (expr, st'))
    (h_eval : evalCtorVal ctx lenv hst ctorName cidx [] retTy = .ok (v, hst', ctor?)) :
    evalExpr venv hst expr = .ok (v, hst') ∧ st' = st ∧ hst' = hst ∧ ctor? = none ∧
      (∃ se, expr = .scalar se ∧ ∀ u, se ≠ .var u) := by
  unfold lowerRealCtor at h_lower; unfold evalCtorVal at h_eval
  dsimp only [List.isEmpty, ↓reduceIte] at h_lower h_eval
  by_cases hf : ctorName == ``Bool.false
  · simp [hf] at h_lower h_eval
    cases h_i1 : lnirTypeEq retTy .i1 <;> simp [h_i1] at h_lower h_eval <;>
      rcases h_lower with ⟨rfl, rfl⟩ <;> rcases h_eval with ⟨rfl, rfl, rfl⟩ <;>
      exact ⟨rfl, rfl, rfl, rfl, _, rfl, fun _ h => nomatch h⟩
  · by_cases ht : ctorName == ``Bool.true
    · simp [hf, ht] at h_lower h_eval
      cases h_i1 : lnirTypeEq retTy .i1 <;> simp [h_i1] at h_lower h_eval <;>
        rcases h_lower with ⟨rfl, rfl⟩ <;> rcases h_eval with ⟨rfl, rfl, rfl⟩ <;>
        exact ⟨rfl, rfl, rfl, rfl, _, rfl, fun _ h => nomatch h⟩
    · by_cases hu : ctorName == ``Unit.unit || ctorName == ``PUnit.unit
      · simp [hf, ht, hu] at h_lower h_eval
        rcases h_lower with ⟨rfl, rfl⟩; rcases h_eval with ⟨rfl, rfl, rfl⟩
        exact ⟨rfl, rfl, rfl, rfl, _, rfl, fun _ h => nomatch h⟩
      · simp only [hf, ht, hu, Bool.false_eq_true, ↓reduceIte] at h_lower h_eval
        cases hnull : ctx.findNullaryCtor? ctorName with
        | none => simp [hnull] at h_lower
        | some c =>
          rw [hnull] at h_lower; dsimp only at h_lower
          cases hok : (lnirTypeEq retTy .i8 || lnirTypeEq retTy .i16 || lnirTypeEq retTy .i1 ||
              (ctx.allowStage1DHeap && isHeapPtrType retTy))
          · rw [hok] at h_lower; exact nomatch h_lower
          · simp only [hok, ↓reduceIte] at h_lower
            cases h_i1 : lnirTypeEq retTy .i1 <;> simp [h_i1] at h_lower h_eval <;>
              rcases h_lower with ⟨rfl, rfl⟩ <;> rcases h_eval with ⟨rfl, rfl, rfl⟩ <;>
              exact ⟨rfl, rfl, rfl, rfl, _, rfl, fun _ h => nomatch h⟩

/-- General `lowerRealCtor` soundness across nullary scalars/enums, Stage 1D heap `allocCtor`, and `mkTuple`. -/
theorem lowerRealCtor_sound (ctx : RealBridgeCtx) (st : RealBridgeState) (lenv : LEnv) (venv : VarEnv)
    (ctorName : Lean.Name) (cidx : Nat) (args : List (Lean.Compiler.LCNF.Arg .impure))
    (retTy : LNIRType) (expr : LNIRExpr) (st' : RealBridgeState) (v : Val) (hst hst' : HeapState)
    (ctor? : Option Lean.Name)
    (hinv : BridgeStateInv st lenv venv)
    (h_lower : lowerRealCtor ctx st ctorName cidx args retTy = .ok (expr, st'))
    (h_eval : evalCtorVal ctx lenv hst ctorName cidx args retTy = .ok (v, hst', ctor?)) :
    evalExpr venv hst expr = .ok (v, hst') ∧ st' = st ∧
      (args.isEmpty = true → (∃ se, expr = .scalar se ∧ ∀ u, se ≠ .var u) ∧ ctor? = none) ∧
      (args.isEmpty = false →
        (∃ argVars, expr = .allocCtor cidx argVars [] ∧ ctor? = some ctorName) ∨
        (∃ numFields argVars, ctx.findTupleArity? ctorName = some numFields ∧ ctor? = none ∧
          expr = .mkTuple argVars ∧
          let dropCnt := if args.length > numFields then args.length - numFields else 0
          argVars.map st.getVarType = (args.drop dropCnt).map (fun | .fvar x => (lenv.tys x).getD .objPtr | _ => .objPtr))) := by
  cases args with
  | nil =>
    rcases lowerRealCtor_nullary ctx st lenv venv ctorName cidx retTy expr st' v hst hst' ctor? h_lower h_eval with
      ⟨he, hst_eq, _, hc, hse⟩
    exact ⟨he, hst_eq, fun _ => ⟨hse, hc⟩, fun h => nomatch h⟩
  | cons a0 as_ =>
    unfold lowerRealCtor at h_lower; unfold evalCtorVal at h_eval
    let heapSpec? : Option RcCtorLayoutSpec :=
      if ctx.allowStage1DHeap then
        match ctx.findLayout? ctorName with
        | some spec =>
          let dropCnt := if (a0 :: as_).length > spec.objSlots then (a0 :: as_).length - spec.objSlots else 0
          let fArgs := (a0 :: as_).drop dropCnt
          let fTys := fArgs.map fun | .fvar x => (lenv.tys x).getD .objPtr | _ => .objPtr
          if spec.scalarSlots.isEmpty && !fArgs.isEmpty &&
              fTys.all (fun t => isSupportedStage1BScalarOrTuple t ctx.arch || isHeapPtrType t) then
            some spec
          else none
        | none => none
      else none
    have h_eval' : (match heapSpec? with
      | some spec =>
        let dropCnt := if (a0 :: as_).length > spec.objSlots then (a0 :: as_).length - spec.objSlots else 0
        let fArgs := (a0 :: as_).drop dropCnt
        match evalArgs lenv.vals fArgs with
        | .ok vs =>
          if vs.isEmpty then Except.ok (Val.tuple [.u64 (wordOf cidx)], hst, some ctorName)
          else if !(vs.all Val.wfField) then
            Except.error (UBError.typeError "allocCtor: object field is a tuple owning an edge")
          else
            let (oid, hst1) := hst.allocHeapCtor cidx vs []
            Except.ok (.objPtr oid, hst1, some ctorName)
        | .error e => Except.error e
      | none =>
        match ctx.findTupleArity? ctorName with
        | some numFields =>
          let dropCnt := if (a0 :: as_).length > numFields then (a0 :: as_).length - numFields else 0
          match evalArgs lenv.vals ((a0 :: as_).drop dropCnt) with
          | .ok vs => Except.ok (.tuple vs, hst, none)
          | .error e => Except.error e
        | none => Except.error (.unsupportedCall s!"ctor {ctorName}")) = .ok (v, hst', ctor?) := by
      dsimp only [List.isEmpty] at h_eval
      exact h_eval
    let lowerTuple : Except String (LNIRExpr × RealBridgeState) :=
      match ctx.findTupleArity? ctorName with
      | some numFields =>
        let dropCnt := if (a0 :: as_).length > numFields then (a0 :: as_).length - numFields else 0
        match lowerRealArgList ctx st true ((a0 :: as_).drop dropCnt) with
        | .error e => .error e
        | .ok (argVars, st1) =>
          let argTys := argVars.map st1.getVarType
          if argVars.isEmpty || !(argTys.all fun t => isSupportedStage1BScalarType t ctx.arch || isHeapPtrType t) then
            .error s!"[lean-native] Unsupported non-scalar or nested tuple/constructor fields in `{ctorName}`"
          else .ok (.mkTuple argVars, st1)
      | none => .error s!"[lean-native] Unsupported payload-carrying constructor `{ctorName}` in Stage 1B"
    have h_lower' : (if ctx.allowStage1DHeap then
        match ctx.findLayout? ctorName with
        | none => lowerTuple
        | some spec =>
          if !spec.scalarSlots.isEmpty then
            .error s!"[lean-native] Unsupported scalar-slot constructor `{ctorName}` outside the impure layout lowering"
          else
            let dropCnt := if (a0 :: as_).length > spec.objSlots then (a0 :: as_).length - spec.objSlots else 0
            match lowerRealArgList ctx st true ((a0 :: as_).drop dropCnt) with
            | .error e => .error e
            | .ok (argVars, st1) =>
              let argTys := argVars.map st1.getVarType
              if !argVars.isEmpty && argTys.all (fun t => isSupportedStage1BScalarOrTuple t ctx.arch || isHeapPtrType t) then
                .ok (.allocCtor cidx argVars [], st1)
              else lowerTuple
      else lowerTuple) = .ok (expr, st') := by
      dsimp only [List.isEmpty] at h_lower
      exact h_lower
    have htuple : heapSpec? = none → lowerTuple = .ok (expr, st') →
        evalExpr venv hst expr = .ok (v, hst') ∧ st' = st ∧
          ((∃ argVars, expr = .allocCtor cidx argVars [] ∧ ctor? = some ctorName) ∨
           (∃ numFields argVars, ctx.findTupleArity? ctorName = some numFields ∧ ctor? = none ∧
             expr = .mkTuple argVars ∧
             let dropCnt := if (a0 :: as_).length > numFields then (a0 :: as_).length - numFields else 0
             argVars.map st.getVarType = ((a0 :: as_).drop dropCnt).map
               (fun | .fvar x => (lenv.tys x).getD .objPtr | _ => .objPtr))) := by
      intro hheapNone hlt
      rw [hheapNone] at h_eval'; dsimp only at h_eval'
      dsimp only [lowerTuple] at hlt
      cases hta : ctx.findTupleArity? ctorName with
      | none => rw [hta] at hlt; exact nomatch hlt
      | some numFields =>
        rw [hta] at hlt h_eval'; dsimp only at hlt h_eval'
        cases hargL : lowerRealArgList ctx st true
            ((a0 :: as_).drop (if (a0 :: as_).length > numFields then (a0 :: as_).length - numFields else 0)) with
        | error _ => rw [hargL] at hlt; exact nomatch hlt
        | ok pair =>
          rcases pair with ⟨argVars, st1⟩
          rw [hargL] at hlt; dsimp only at hlt
          rcases lowerRealArgList_sound ctx st lenv venv true _ argVars st1 hinv hargL with
            ⟨vs, hevalArgs, hvarList, _, hst1_eq, hmap⟩
          rw [hst1_eq] at hlt
          cases hcond : (argVars.isEmpty || !(argVars.map st.getVarType).all
              (fun t => isSupportedStage1BScalarType t ctx.arch || isHeapPtrType t))
          · rw [hcond] at hlt; simp only [Bool.false_eq_true, ↓reduceIte] at hlt
            injection hlt with hp; rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
            rw [hevalArgs] at h_eval'; dsimp only at h_eval'
            injection h_eval' with hp2; rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, rfl⟩
            exact ⟨by simp [evalExpr, hvarList], rfl, Or.inr ⟨numFields, argVars, rfl, rfl, rfl, hmap⟩⟩
          · rw [hcond] at hlt; exact nomatch hlt
    have hnoneA : (a0 :: as_).isEmpty = true →
        (∃ se, expr = .scalar se ∧ ∀ u, se ≠ .var u) ∧ ctor? = none := fun h => False.elim (by cases h)
    cases hst1d : ctx.allowStage1DHeap
    · simp only [hst1d, Bool.false_eq_true, ↓reduceIte] at h_lower'
      rcases htuple (by simp [heapSpec?, hst1d]) h_lower' with ⟨he, hst_eq, hdisj⟩
      exact ⟨he, hst_eq, hnoneA, fun _ => hdisj⟩
    · simp only [hst1d, ↓reduceIte] at h_lower'
      cases hlay : ctx.findLayout? ctorName with
      | none =>
        rw [hlay] at h_lower'; dsimp only at h_lower'
        rcases htuple (by simp [heapSpec?, hst1d, hlay]) h_lower' with ⟨he, hst_eq, hdisj⟩
        exact ⟨he, hst_eq, hnoneA, fun _ => hdisj⟩
      | some spec =>
        rw [hlay] at h_lower'; dsimp only at h_lower'
        cases hsc : spec.scalarSlots.isEmpty
        · simp only [hsc, Bool.not_false, ↓reduceIte] at h_lower'; exact nomatch h_lower'
        · simp only [hsc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h_lower'
          cases hargL : lowerRealArgList ctx st true
              ((a0 :: as_).drop (if (a0 :: as_).length > spec.objSlots then (a0 :: as_).length - spec.objSlots else 0)) with
          | error _ => rw [hargL] at h_lower'; exact nomatch h_lower'
          | ok pair =>
            rcases pair with ⟨argVars, st1⟩
            rw [hargL] at h_lower'; dsimp only at h_lower'
            rcases lowerRealArgList_sound ctx st lenv venv true _ argVars st1 hinv hargL with
              ⟨vs, hevalArgs, hvarList, hlen, hst1_eq, hmap⟩
            rw [hst1_eq] at h_lower'
            have hemptyEq : argVars.isEmpty =
                ((a0 :: as_).drop
                  (if (a0 :: as_).length > spec.objSlots then (a0 :: as_).length - spec.objSlots else 0)).isEmpty := by
              cases argVars <;>
                cases hd : (a0 :: as_).drop
                  (if (a0 :: as_).length > spec.objSlots then (a0 :: as_).length - spec.objSlots else 0) <;>
                first | rfl | (rw [hd] at hlen; cases hlen)
            cases hcond : (!argVars.isEmpty && (argVars.map st.getVarType).all
                (fun t => isSupportedStage1BScalarOrTuple t ctx.arch || isHeapPtrType t))
            · rw [hcond] at h_lower'; simp only [Bool.false_eq_true, ↓reduceIte] at h_lower'
              let fArgs := (a0 :: as_).drop
                (if (a0 :: as_).length > spec.objSlots then (a0 :: as_).length - spec.objSlots else 0)
              have hheapNone : heapSpec? = none := by
                dsimp only [heapSpec?]
                simp only [hst1d, hlay, hsc, Bool.true_and, ↓reduceIte]
                have hcondF : (!fArgs.isEmpty &&
                    (fArgs.map fun x => match x with | .fvar x => (lenv.tys x).getD .objPtr | _ => .objPtr).all
                    (fun t => isSupportedStage1BScalarOrTuple t ctx.arch || isHeapPtrType t)) = false := by
                  dsimp only [fArgs]
                  rw [← hemptyEq]
                  exact Eq.trans (congrArg (fun l => !argVars.isEmpty &&
                    l.all fun t => isSupportedStage1BScalarOrTuple t ctx.arch || isHeapPtrType t) hmap.symm) hcond
                rw [hcondF]; rfl
              rcases htuple hheapNone h_lower' with ⟨he, hst_eq, hdisj⟩
              exact ⟨he, hst_eq, hnoneA, fun _ => hdisj⟩
            · rw [hcond] at h_lower'; simp only [↓reduceIte] at h_lower'
              injection h_lower' with hp; rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
              let fArgs := (a0 :: as_).drop
                (if (a0 :: as_).length > spec.objSlots then (a0 :: as_).length - spec.objSlots else 0)
              have hheapSome : heapSpec? = some spec := by
                dsimp only [heapSpec?]
                simp only [hst1d, hlay, hsc, Bool.true_and, ↓reduceIte]
                have hcondT : (!fArgs.isEmpty &&
                    (fArgs.map fun x => match x with | .fvar x => (lenv.tys x).getD .objPtr | _ => .objPtr).all
                    (fun t => isSupportedStage1BScalarOrTuple t ctx.arch || isHeapPtrType t)) = true := by
                  dsimp only [fArgs]
                  rw [← hemptyEq]
                  exact Eq.trans (congrArg (fun l => !argVars.isEmpty &&
                    l.all fun t => isSupportedStage1BScalarOrTuple t ctx.arch || isHeapPtrType t) hmap.symm) hcond
                rw [hcondT]; rfl
              rw [hheapSome] at h_eval'; dsimp only at h_eval'
              rw [hevalArgs] at h_eval'; dsimp only at h_eval'
              have hvsNe : vs.isEmpty = false := by
                rcases Bool.and_eq_true_iff.mp hcond with ⟨hneA, _⟩
                cases argVars with
                | nil => simp at hneA
                | cons v0 vr =>
                  dsimp only [evalVarList] at hvarList
                  cases hv0 : venv v0 with
                  | none => rw [hv0] at hvarList; exact nomatch hvarList
                  | some val0 =>
                    rw [hv0] at hvarList
                    cases hvr : evalVarList venv vr with
                    | error _ => rw [hvr] at hvarList; exact nomatch hvarList
                    | ok vals =>
                      rw [hvr] at hvarList; injection hvarList with hvs
                      subst hvs; rfl
              rw [hvsNe] at h_eval'; simp only [Bool.false_eq_true, ↓reduceIte] at h_eval'
              cases hwf : (!vs.all Val.wfField)
              · simp only [hwf, Bool.false_eq_true, ↓reduceIte] at h_eval'
                injection h_eval' with hp2; rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, rfl⟩
                refine ⟨?_, rfl, hnoneA, fun _ => Or.inl ⟨argVars, rfl, rfl⟩⟩
                simp only [evalExpr, hvarList, evalVarList, hvsNe, Bool.false_and, hwf, Bool.false_eq_true, ↓reduceIte]
              · simp [hwf] at h_eval'

/-- `lowerCanonicalIntrinsicPure?` agrees with `.fap` evaluation on all binary, GF/SIMD, boolean, unary, and cast intrinsics. -/
theorem lowerCanonicalIntrinsicPure_sound (ctx : RealBridgeCtx) (st : RealBridgeState) (lenv : LEnv)
    (venv : VarEnv) (hst hst' : HeapState) (fn : Lean.Name)
    (args : Array (Lean.Compiler.LCNF.Arg .impure)) (himp : Lean.Compiler.LCNF.Purity.impure = .impure)
    (argVars : List VarId) (st1 : RealBridgeState)
    (retTy : LNIRType) (expr : LNIRExpr) (v : Val) (ctor? : Option Lean.Name)
    (hinv : BridgeStateInv st lenv venv)
    (hargL : lowerRealArgList ctx st false args.toList = .ok (argVars, st1))
    (hs : lowerCanonicalIntrinsicPure? fn argVars retTy (argVars.map st1.getVarType)
      (ctx.findLocalCallee? fn).isSome ctx.arch ctx.gfSimdIntrinsics = some expr)
    (ho : evalLetValue ctx lenv hst (.fap fn args himp) retTy = .ok (v, hst', ctor?)) :
    evalExpr venv hst expr = .ok (v, hst') ∧ st1 = st ∧ hst' = hst ∧ ctor? = none ∧
      (∃ se, expr = .scalar se ∧ ∀ u, se ≠ .var u) := by
  rcases lowerRealArgList_sound ctx st lenv venv false args.toList argVars st1 hinv hargL with
    ⟨vs, hevalArgs, hvarList, hlen, rfl, hmap⟩
  unfold lowerCanonicalIntrinsicPure? at hs
  dsimp only [evalLetValue] at ho
  cases hloc : (ctx.findLocalCallee? fn).isSome
  · rw [hloc] at hs ho; simp only [Bool.false_eq_true, ↓reduceIte] at hs ho
    cases hlist : args.toList with
    | nil => rw [hlist] at hlen; cases argVars <;> simp at hlen hs
    | cons a rest1 =>
      cases rest1 with
      | nil =>
        rw [hlist] at hlen hmap hevalArgs ho hargL
        cases argVars with
        | nil => simp at hlen
        | cons varg restV =>
          cases restV with
          | cons _ _ => simp at hlen
          | nil =>
            dsimp only [List.map] at hmap
            injection hmap with htyA _
            cases a with
            | type _ => dsimp [lowerRealArgList, lowerRealArg] at hargL; exact nomatch hargL
            | erased => dsimp [lowerRealArgList, lowerRealArg] at hargL; exact nomatch hargL
            | fvar xA =>
              have htyA' : st1.getVarType varg = (lenv.tys xA).getD .objPtr := htyA
              simp only [List.map, htyA'] at hs
              dsimp only at ho; dsimp only [evalArgs] at hevalArgs
              cases heA : evalArg lenv.vals (.fvar xA) with
              | error _ => simp [heA] at hevalArgs
              | ok va =>
                rw [heA] at ho; dsimp only at ho
                simp only [heA] at hevalArgs; injection hevalArgs with hvsEq
                subst hvsEq
                dsimp only [evalVarList] at hvarList
                cases hvA : venv varg with
                | none => simp [hvA] at hvarList
                | some va' =>
                  simp only [hvA] at hvarList; injection hvarList with hvaEq
                  rcases List.cons.inj hvaEq with ⟨hva, _⟩; subst hva
                  cases hcall : evalUnaryOrCastCall? ctx.arch fn va' ((lenv.tys xA).getD .objPtr) retTy with
                  | none => rw [hcall] at ho; exact nomatch ho
                  | some res =>
                    rw [hcall] at ho; dsimp only [Functor.map, Except.map] at ho
                    cases res with
                    | error _ => exact nomatch ho
                    | ok v0 =>
                      injection ho with hp2; rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, rfl⟩
                      rcases lowerUnaryAndCast_sound venv hst ctx.arch fn varg _ retTy va' expr v0 hvA hs hcall with ⟨he, hse⟩
                      exact ⟨he, rfl, rfl, rfl, hse⟩
      | cons b rest2 =>
        cases rest2 with
        | cons _ _ =>
          rw [hlist] at hlen
          cases argVars with
          | nil => simp at hlen
          | cons _ r1 => cases r1 with | nil => simp at hlen | cons _ r2 => cases r2 <;> simp at hlen hs
        | nil =>
          rw [hlist] at hlen hmap hevalArgs ho hargL
          cases argVars with
          | nil => simp at hlen
          | cons vl r1 =>
            cases r1 with
            | nil => simp at hlen
            | cons vr r2 =>
              cases r2 with
              | cons _ _ => simp at hlen
              | nil =>
                dsimp only [List.map] at hmap
                injection hmap with htA hmap2; injection hmap2 with htB _
                cases a with
                | type _ => dsimp [lowerRealArgList, lowerRealArg] at hargL; exact nomatch hargL
                | erased => dsimp [lowerRealArgList, lowerRealArg] at hargL; exact nomatch hargL
                | fvar xA =>
                  cases b with
                  | type _ =>
                    dsimp [evalArgs, evalArg] at hevalArgs
                    cases hvx : lenv.vals xA <;>
                      (rw [hvx] at hevalArgs; exact nomatch hevalArgs)
                  | erased =>
                    dsimp [evalArgs, evalArg] at hevalArgs
                    cases hvx : lenv.vals xA <;>
                      (rw [hvx] at hevalArgs; exact nomatch hevalArgs)
                  | fvar xB =>
                    have htA' : st1.getVarType vl = (lenv.tys xA).getD .objPtr := htA
                    have htB' : st1.getVarType vr = (lenv.tys xB).getD .objPtr := htB
                    simp only [List.map, htA', htB'] at hs
                    dsimp only [evalArgs] at hevalArgs
                    cases heA : evalArg lenv.vals (.fvar xA) with
                    | error _ => simp [heA] at hevalArgs
                    | ok va =>
                      cases heB : evalArg lenv.vals (.fvar xB) with
                      | error _ => simp [heA, heB] at hevalArgs
                      | ok vb =>
                        simp only [heA, heB] at hevalArgs ho; injection hevalArgs with hvsEq
                        subst hvsEq
                        dsimp only [evalVarList] at hvarList
                        cases hvL : venv vl with
                        | none => simp [hvL] at hvarList
                        | some va' =>
                          cases hvR : venv vr with
                          | none => simp [hvL, hvR] at hvarList
                          | some vb' =>
                            simp only [hvL, hvR] at hvarList; injection hvarList with hvEq
                            rcases List.cons.inj hvEq with ⟨hva, hvEq2⟩
                            rcases List.cons.inj hvEq2 with ⟨hvb, _⟩
                            subst hva; subst hvb
                            have hgfEq : (ctx.gfSimdIntrinsics.find? (fun (n, _) => n == fn)).map Prod.snd =
                                ctx.findGfSimd? fn := rfl
                            rw [hgfEq] at hs
                            cases hgf : ctx.findGfSimd? fn with
                            | some gfOp =>
                              rw [hgf] at hs ho; dsimp only at hs ho
                              cases hgfTy : (lnirTypeEq retTy .i64 && lnirTypeEq ((lenv.tys xA).getD .objPtr) .i64 &&
                                  lnirTypeEq ((lenv.tys xB).getD .objPtr) .i64)
                              · rw [hgfTy] at ho; exact nomatch ho
                              · rw [hgfTy] at ho; simp only [↓reduceIte] at ho
                                rcases Bool.and_eq_true_iff.mp hgfTy with ⟨hretA, htBi64⟩
                                rcases Bool.and_eq_true_iff.mp hretA with ⟨hreti64, htAi64⟩
                                have hgfCond : (lnirTypeEq retTy .i64 &&
                                    ([((lenv.tys xA).getD .objPtr), ((lenv.tys xB).getD .objPtr)].isEmpty ||
                                      lnirTypeListEq [((lenv.tys xA).getD .objPtr), ((lenv.tys xB).getD .objPtr)]
                                        [.i64, .i64])) = true := by
                                  dsimp [lnirTypeListEq]; simp [hreti64, htAi64, htBi64]
                                rw [hgfCond] at hs; simp only [↓reduceIte] at hs
                                injection hs with hexp; subst hexp
                                cases hgfev : evalGfSimd gfOp va' vb' with
                                | error _ => rw [hgfev] at ho; exact nomatch ho
                                | ok v0 =>
                                  rw [hgfev] at ho; dsimp only [Functor.map, Except.map] at ho
                                  injection ho with hp2
                                  rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩
                                  rcases Prod.mk.inj hp3 with ⟨rfl, rfl⟩
                                  have hevalS : evalScalarExpr venv (.binOp gfOp (.var vl) (.var vr)) = .ok v0 := by
                                    rw [evalScalar_binOp venv gfOp (.var vl) (.var vr) va' vb'
                                      (evalScalar_var venv vl va' hvL) (evalScalar_var venv vr vb' hvR)]
                                    cases gfOp with
                                    | clmul64 | clmul64Hi | gf2Affine | eor3 =>
                                      dsimp [evalGfSimd, evalBinOp] at hgfev ⊢
                                      cases va' <;> cases vb' <;> first | exact hgfev | exact nomatch hgfev
                                    | _ => exact nomatch hgfev
                                  exact ⟨evalExpr_scalar venv hst _ v0 hevalS, rfl, rfl, rfl,
                                    .binOp gfOp (.var vl) (.var vr), rfl, fun _ h => nomatch h⟩
                            | none =>
                              rw [hgf] at hs ho; dsimp only at hs ho
                              cases hbin : lookupCanonicalTypedBinOp? fn with
                              | some pairOp =>
                                rcases pairOp with ⟨opTy, op⟩
                                rw [hbin] at hs ho; dsimp only at hs ho
                                cases hteq : (lnirTypeEq ((lenv.tys xA).getD .objPtr) opTy && lnirTypeEq ((lenv.tys xB).getD .objPtr) opTy)
                                · rw [hteq] at ho; exact nomatch ho
                                · rw [hteq] at ho; simp only [↓reduceIte] at ho
                                  have hlistEq :
                                      lnirTypeListEq [(lenv.tys xA).getD .objPtr, (lenv.tys xB).getD .objPtr]
                                        [opTy, opTy] = true := by
                                    dsimp [lnirTypeListEq]; simp [hteq]
                                  rw [hlistEq] at hs
                                  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Functor.map, Option.map] at hs
                                  cases hse : lowerScalarIntrinsicExpr? op vl vr opTy retTy ctx.arch with
                                  | none => rw [hse] at hs; exact nomatch hs
                                  | some se =>
                                    rw [hse] at hs; injection hs with hseEq; subst hseEq
                                    cases hwb : wordBin ctx.arch op opTy retTy va' vb' with
                                    | error _ => rw [hwb] at ho; exact nomatch ho
                                    | ok v0 =>
                                      rw [hwb] at ho; dsimp only [Functor.map, Except.map] at ho
                                      injection ho with hp2
                                      rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩
                                      rcases Prod.mk.inj hp3 with ⟨rfl, rfl⟩
                                      rcases lowerScalarIntrinsicExpr_sound venv ctx.arch op opTy retTy
                                          vl vr va' vb' se v0 hvL hvR hse hwb with ⟨hevalS, hnv⟩
                                      exact ⟨evalExpr_scalar venv hst se v0 hevalS, rfl, rfl, rfl, se, rfl, hnv⟩
                              | none =>
                                rw [hbin] at hs ho; dsimp only at hs ho
                                cases hbb : evalBoolBinCall? fn va' vb' ((lenv.tys xA).getD .objPtr) ((lenv.tys xB).getD .objPtr) retTy with
                                | none => rw [hbb] at ho; exact nomatch ho
                                | some res =>
                                  rw [hbb] at ho; dsimp only at ho
                                  cases res with
                                  | error _ => exact nomatch ho
                                  | ok v0 =>
                                    dsimp only [Functor.map, Except.map] at ho
                                    injection ho with hp2
                                    rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩
                                    rcases Prod.mk.inj hp3 with ⟨rfl, rfl⟩
                                    rcases lowerBoolBinIntrinsic_sound venv hst fn vl vr _ _ retTy
                                        va' vb' expr v0 hvL hvR hs hbb with ⟨he, hse⟩
                                    exact ⟨he, rfl, rfl, rfl, hse⟩
  · rw [hloc] at hs; simp at hs


end LeanNative.Proofs
