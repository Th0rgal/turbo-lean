import LeanNative.Proofs.SymbolicTVCodeHelpers

namespace LeanNative.Proofs
set_option maxHeartbeats 40000

open LeanNative.IR
open LeanNative.Semantics

/-!
# Code-Level Denotational Soundness of `symExecCode` (`LeanNative.Proofs.SymbolicTVCodeSoundness`)

Proves that `symExecCode` preserves exact concrete denotation (`denoteSymExpr`) over
straight-line pure 64-bit SSA `LNIRCode` (`symExecCode_pureU64_denotes`) and that normalized
`symExecCode` return equality discharges concrete `evalCode` equivalence (`symExecCode_pureU64_eval_eq`)
and `CodeRefines` on well-typed `.u64` parameter environments (`symExecCode_pureU64_codeRefines_on_u64Env`).
-/

theorem list_lookup_filter_ne (xs : List (VarId × SymStateVal)) (dst id : VarId)
    (hne : id ≠ dst) :
    (xs.filter (fun p => p.1 != dst)).lookup id = xs.lookup id := by
  induction xs with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨k, val⟩
    by_cases hkd : (k == dst) = true
    · have hk_eq : k = dst := eq_of_beq hkd
      subst hk_eq
      have hik : (id == k) = false := beq_false_of_ne hne
      simp [List.filter, List.lookup, hik, ih]
    · simp only [Bool.not_eq_true] at hkd
      simp only [List.filter, bne, hkd, Bool.not_false, List.lookup]
      cases id == k
      · exact ih
      · rfl

theorem SymExecState.lookupVar_bindVar_same (st : SymExecState) (dst : VarId) (sv : SymStateVal) :
    (st.bindVar dst sv).lookupVar dst = sv := by
  simp [SymExecState.bindVar, SymExecState.lookupVar]

theorem SymExecState.lookupVar_bindVar_ne (st : SymExecState) (dst id : VarId) (sv : SymStateVal)
    (hne : id ≠ dst) :
    (st.bindVar dst sv).lookupVar id = st.lookupVar id := by
  have hik : (id == dst) = false := beq_false_of_ne hne
  simp only [SymExecState.bindVar, SymExecState.lookupVar, List.lookup, hik]
  rw [list_lookup_filter_ne st.vars dst id hne]

theorem list_contains_cons_filter_other (xs : List VarId) (v p : VarId)
    (hp : xs.contains p = true) :
    (v :: xs.filter (· != v)).contains p = true := by
  by_cases hpv : p = v
  · subst hpv; simp
  · simp only [List.contains_eq_mem, decide_eq_true_eq] at hp ⊢
    exact List.mem_cons_of_mem v (List.mem_filter.mpr ⟨hp, bne_iff_ne.mpr hpv⟩)

theorem symExpr_matchTuple_eq_of_not_tuple {α : Type} (s : SymExpr) (t : List SymExpr → α) (e : α)
    (hnt : isTupleSymExpr s = false) :
    matchTupleSymExpr s t e = e := by
  cases s with
  | tuple _ => simp [isTupleSymExpr] at hnt
  | _ => rfl

theorem SymExecState.isDefinitelyHeapRoot_false_of_clean
    {st : SymExecState}
    (hbuf : st.bufAliases = []) (halloc : st.allocRoots = [])
    (hsarr : st.sarrayVars = []) (hobj : st.objPtrVars = [])
    (hrefc : st.refCounts = []) (hrce : st.rcExprs = [])
    (hexcl : st.exclusiveBufs = [])
    (hnotup : ∀ v : VarId, isTupleSymExpr (st.lookupVar v).expr = false)
    (id : VarId) :
    st.isDefinitelyHeapRoot id = false := by
  have hnil : ([] : List VarId).contains id = false := rfl
  have hm := symExpr_matchTuple_eq_of_not_tuple (st.lookupVar id).expr (fun _ => !st.typedTuples.contains id) false (hnotup id)
  unfold SymExecState.isDefinitelyHeapRoot SymExecState.resolveBuf
  rw [hbuf]
  dsimp only [List.lookup]
  rw [halloc, hsarr, hobj, hrefc, hrce, hexcl, hnil]
  change (if (false || false || false || false || false || false) = true then true
    else matchTupleSymExpr (st.lookupVar id).expr (fun _ => !st.typedTuples.contains id) false) = false
  rw [hm]
  rfl

theorem SymExecState.markU64Var_clean
    {st : SymExecState} (dst : VarId)
    (hbuf : st.bufAliases = []) (halloc : st.allocRoots = [])
    (hsarr : st.sarrayVars = []) (hobj : st.objPtrVars = [])
    (hbool : st.boolVars = []) (hu256 : st.u256Vars = [])
    (hnotup : ∀ v : VarId, isTupleSymExpr (st.lookupVar v).expr = false) :
    st.markU64Var dst =
      { st with u64Vars := dst :: st.u64Vars.filter (· != dst), boolVars := [], u256Vars := [] } := by
  have hnil : ([] : List VarId).contains dst = false := rfl
  have hm := symExpr_matchTuple_eq_of_not_tuple (st.lookupVar dst).expr (fun _ => !st.typedTuples.contains dst) false (hnotup dst)
  have hres : st.resolveBuf dst = dst := by unfold SymExecState.resolveBuf; rw [hbuf]; rfl
  unfold SymExecState.markU64Var
  rw [hres]
  have hcond : (st.allocRoots.contains dst || st.sarrayVars.contains dst || st.objPtrVars.contains dst ||
      matchTupleSymExpr (st.lookupVar dst).expr (fun _ => !st.typedTuples.contains dst) false) = false := by
    rw [halloc, hsarr, hobj, hnil, hm]
    rfl
  change (if (st.allocRoots.contains dst || st.sarrayVars.contains dst || st.objPtrVars.contains dst ||
      matchTupleSymExpr (st.lookupVar dst).expr (fun _ => !st.typedTuples.contains dst) false) = true then st
    else
      { st with
        boolVars := st.boolVars.filter (· != dst)
        u64Vars := dst :: st.u64Vars.filter (· != dst)
        u256Vars := st.u256Vars.filter (· != dst) }) = _
  rw [hcond, hbool, hu256]
  rfl

theorem scalarExprMentionsHeapRoot_false_of_clean
    {st : SymExecState}
    (hbuf : st.bufAliases = []) (halloc : st.allocRoots = [])
    (hsarr : st.sarrayVars = []) (hobj : st.objPtrVars = [])
    (hrefc : st.refCounts = []) (hrce : st.rcExprs = [])
    (hexcl : st.exclusiveBufs = [])
    (hnotup : ∀ v : VarId, isTupleSymExpr (st.lookupVar v).expr = false) :
    ∀ (e : ScalarExpr), scalarExprMentionsHeapRoot st e = false
  | .constU64 _ | .constBool _ => rfl
  | .var id =>
    SymExecState.isDefinitelyHeapRoot_false_of_clean hbuf halloc hsarr hobj hrefc hrce hexcl hnotup id
  | .unaryOp _ a =>
    scalarExprMentionsHeapRoot_false_of_clean hbuf halloc hsarr hobj hrefc hrce hexcl hnotup a
  | .binOp _ l r => by
    simp [scalarExprMentionsHeapRoot,
      scalarExprMentionsHeapRoot_false_of_clean hbuf halloc hsarr hobj hrefc hrce hexcl hnotup l,
      scalarExprMentionsHeapRoot_false_of_clean hbuf halloc hsarr hobj hrefc hrce hexcl hnotup r]
  | .select c t f | .fma c t f => by
    simp [scalarExprMentionsHeapRoot,
      scalarExprMentionsHeapRoot_false_of_clean hbuf halloc hsarr hobj hrefc hrce hexcl hnotup c,
      scalarExprMentionsHeapRoot_false_of_clean hbuf halloc hsarr hobj hrefc hrce hexcl hnotup t,
      scalarExprMentionsHeapRoot_false_of_clean hbuf halloc hsarr hobj hrefc hrce hexcl hnotup f]

theorem expandHeapExpr_clean_id
    {params : List VarId} {st : SymExecState}
    (hbuf : st.bufAliases = []) (halloc : st.allocRoots = [])
    (hrefc : st.refCounts = []) (hrce : st.rcExprs = [])
    (hnotup : ∀ v : VarId, isTupleSymExpr (st.lookupVar v).expr = false)
    (d : Nat) (s : SymExpr) (hp : isPureU64SymExprIn params s = true) :
    st.expandHeapExpr d s = s := by
  cases d with
  | zero => rfl
  | succ d' =>
    cases s with
    | constU64 _ | unaryOp _ _ | binOp _ _ _ => rfl
    | symVar id =>
      have hnil : ([] : List VarId).contains id = false := rfl
      have hm := symExpr_matchTuple_eq_of_not_tuple (st.lookupVar id).expr (fun _ => true) false (hnotup id)
      unfold SymExecState.expandHeapExpr SymExecState.resolveBuf
      rw [hbuf]
      dsimp only [List.lookup]
      rw [halloc, hrefc, hrce, hnil]
      dsimp only [List.lookup, Option.isSome]
      have hcond : (false || false || false ||
          (!st.typedTuples.contains id &&
            matchTupleSymExpr (st.lookupVar id).expr (fun _ => true) false)) = false := by
        rw [hm, Bool.and_false]
        rfl
      change (if (false || false || false ||
          (!st.typedTuples.contains id &&
            matchTupleSymExpr (st.lookupVar id).expr (fun _ => true) false)) = true then _ else SymExpr.symVar id) = SymExpr.symVar id
      rw [hcond]
      rfl
    | constU256 _ | constBool _ | allocTag _ | rcSym _ _ | ctorTag _ _ | ctorLen _ _ _
    | sarrayLen _ | mulDiv256 _ _ _ _ | ite _ _ _ | tuple _ | bufElem _ _ _ | unit =>
      simp [isPureU64SymExprIn] at hp

theorem PureU64SymState.afterCleanBindU64
    {ω0 : SymValuation} {params bound : List VarId} {st : SymExecState} {env : VarEnv}
    (hst : PureU64SymState ω0 params bound st env)
    (dst : VarId) (sv : SymStateVal) (n : UInt64)
    (hnoub : sv.noUB = true)
    (hpIn : isPureU64SymExprIn params sv.expr = true)
    (hden : denoteSymExpr ω0 sv.expr = .ok (.u64 n)) :
    let stMarked : SymExecState :=
      { st with u64Vars := dst :: st.u64Vars.filter (· != dst), boolVars := [], u256Vars := [] }
    PureU64SymState ω0 params (dst :: bound) (stMarked.bindVar dst sv) (env.bind dst (.u64 n)) := by
  rcases hst with ⟨hbuf, halloc, hsarr, hobj, hext, htup, hrefc, hrce, hexcl, hbool, hu256,
    hubSt, hnoubSt, hunsupSt, hexhSt, hnotup, hpar, hbound⟩
  dsimp only []
  let stMarked : SymExecState :=
    { st with u64Vars := dst :: st.u64Vars.filter (· != dst), boolVars := [], u256Vars := [] }
  refine ⟨hbuf, halloc, hsarr, hobj, hext, htup, hrefc, hrce, hexcl, rfl, rfl, ?_, ?_, hunsupSt, hexhSt, ?_, ?_, ?_⟩
  · simp [SymExecState.bindVar, hnoub, hubSt]
  · simp [SymExecState.bindVar, hnoub, hnoubSt]
  · intro v
    by_cases hvd : v = dst
    · subst hvd
      rw [SymExecState.lookupVar_bindVar_same]
      exact isPureU64SymExprIn_not_tuple hpIn
    · rw [SymExecState.lookupVar_bindVar_ne stMarked dst v sv hvd]
      exact hnotup v
  · intro p hp
    obtain ⟨hu, hw⟩ := hpar p hp
    exact ⟨list_contains_cons_filter_other st.u64Vars dst p hu, hw⟩
  · intro id hid
    rw [List.contains_cons] at hid
    by_cases hidd : id = dst
    · subst hidd
      exact ⟨n, VarEnv.bind_self env id (.u64 n),
        by rw [SymExecState.lookupVar_bindVar_same]; exact hnoub,
        by rw [SymExecState.lookupVar_bindVar_same]; exact hpIn,
        by rw [SymExecState.lookupVar_bindVar_same]; exact hden⟩
    · have hbeqF : (id == dst) = false := beq_false_of_ne hidd
      rw [hbeqF, Bool.false_or] at hid
      obtain ⟨ni, henvi, hnoubi, hpIni, hdeni⟩ := hbound id hid
      refine ⟨ni, ?_, ?_, ?_, ?_⟩
      · rw [VarEnv.bind_ne env dst id (.u64 n) hbeqF]
        exact henvi
      · rw [SymExecState.lookupVar_bindVar_ne stMarked dst id sv hidd]
        exact hnoubi
      · rw [SymExecState.lookupVar_bindVar_ne stMarked dst id sv hidd]
        exact hpIni
      · rw [SymExecState.lookupVar_bindVar_ne stMarked dst id sv hidd]
        exact hdeni

theorem symEvalExpr_nonVar_ssaPureU64_eq
    {ω0 : SymValuation} {params bound : List VarId} {st : SymExecState} {env : VarEnv}
    (hst : PureU64SymState ω0 params bound st env)
    (dst : VarId)
    (se : ScalarExpr) (hnotVar : ∀ id, se ≠ .var id)
    (hpure : isPureU64ScalarExpr se = true)
    (hall : scalarExprAllBound bound se = true) :
    ∃ n : UInt64,
      evalScalarExpr env se = .ok (.u64 n) ∧
      PureU64SymState ω0 params (dst :: bound)
        (symEvalExpr (st.clearAlias dst) dst .i64 (.scalar se))
        (env.bind dst (.u64 n)) := by
  obtain ⟨n, heval, hunsup, hub, hnoub, hpIn, hsort, hden⟩ :=
    symEvalScalarRes_ssaPureU64_sound hst se hpure hall
  refine ⟨n, heval, ?_⟩
  rcases hst with ⟨hbuf, halloc, hsarr, hobj, hext, htup, hrefc, hrce, hexcl, hbool, hu256,
    hubSt, hnoubSt, hunsupSt, hexhSt, hnotup, hpar, hbound⟩
  have hstOrig : PureU64SymState ω0 params bound st env :=
    ⟨hbuf, halloc, hsarr, hobj, hext, htup, hrefc, hrce, hexcl, hbool, hu256,
      hubSt, hnoubSt, hunsupSt, hexhSt, hnotup, hpar, hbound⟩
  have hclear : st.clearAlias dst = st := by
    cases st
    simp at hbuf
    subst hbuf
    rfl
  have hresNone : resolveScalarRoot? st se = (none, true, true, false) := by
    cases se with
    | var id => exact False.elim (hnotVar id rfl)
    | select _ _ _ => simp [isPureU64ScalarExpr] at hpure
    | constU64 _ | constBool _ | unaryOp _ _ | binOp _ _ _ | fma _ _ _ => rfl
  have hmentF : scalarExprMentionsHeapRoot st se = false :=
    scalarExprMentionsHeapRoot_false_of_clean hbuf halloc hsarr hobj hrefc hrce hexcl hnotup se
  have hmark : st.markU64Var dst =
      { st with u64Vars := dst :: st.u64Vars.filter (· != dst), boolVars := [], u256Vars := [] } :=
    SymExecState.markU64Var_clean dst hbuf halloc hsarr hobj hbool hu256 hnotup
  have hunmarkEq : (st.markU64Var dst).unmarkTypedTuple dst =
      { st with u64Vars := dst :: st.u64Vars.filter (· != dst), boolVars := [], u256Vars := [] } := by
    rw [hmark]
    unfold SymExecState.unmarkTypedTuple
    cases st
    simp at htup
    subst htup
    rfl
  have hsort1 : symExprScalarSort? st (symEvalScalarRes st se).val.expr = some 1 := hsort
  have hnotTupMatch :
      matchTupleSymExpr (symEvalScalarRes st se).val.expr
        (fun _ => (st.markU64Var dst).markTypedTuple dst) ((st.markU64Var dst).unmarkTypedTuple dst) =
      { st with u64Vars := dst :: st.u64Vars.filter (· != dst), boolVars := [], u256Vars := [] } :=
    (symExpr_matchTuple_eq_of_not_tuple (symEvalScalarRes st se).val.expr
      (fun _ => (st.markU64Var dst).markTypedTuple dst) ((st.markU64Var dst).unmarkTypedTuple dst)
      (isPureU64SymExprIn_not_tuple hpIn)).trans hunmarkEq
  have hvalEq : { (symEvalScalarRes st se).val with noUB := true } = (symEvalScalarRes st se).val := by
    cases hsr : (symEvalScalarRes st se).val
    rw [hsr] at hnoub
    dsimp only at hnoub
    subst hnoub
    rfl
  rw [hclear, symEvalExpr.eq_def]
  dsimp only [callSlotKind]
  have hptrF : (some false == some true) = false := rfl
  rw [hresNone]
  dsimp only []
  rw [hptrF, hunsup, hmentF, hsort1, hclear]
  change PureU64SymState ω0 params (dst :: bound)
    (let stReq := (matchTupleSymExpr (symEvalScalarRes st se).val.expr
        (fun _ => (st.markU64Var dst).markTypedTuple dst) ((st.markU64Var dst).unmarkTypedTuple dst)).requireUbCond
        (symEvalScalarRes st se).ubCond
     let stB := stReq.bindVar dst { (symEvalScalarRes st se).val with noUB := true }
     { stB with ubCond := stReq.ubCond, noUB := stReq.noUB && (symEvalScalarRes st se).val.noUB })
    (env.bind dst (.u64 n))
  rw [hnotTupMatch, hub]
  have hreq :
      ({ st with u64Vars := dst :: st.u64Vars.filter (· != dst), boolVars := [], u256Vars := [] } :
        SymExecState).requireUbCond (.constBool true) =
      { st with u64Vars := dst :: st.u64Vars.filter (· != dst), boolVars := [], u256Vars := [] } := rfl
  rw [hreq, hvalEq]
  have hrecEq :
      (let stReq : SymExecState :=
         { st with u64Vars := dst :: st.u64Vars.filter (· != dst), boolVars := [], u256Vars := [] }
       let stB := stReq.bindVar dst (symEvalScalarRes st se).val
       { stB with ubCond := stReq.ubCond, noUB := stReq.noUB && (symEvalScalarRes st se).val.noUB }) =
      ({ st with u64Vars := dst :: st.u64Vars.filter (· != dst), boolVars := [], u256Vars := [] } :
        SymExecState).bindVar dst (symEvalScalarRes st se).val := by
    dsimp only [SymExecState.bindVar]
    rw [hnoub]
    rfl
  rw [hrecEq]
  exact hstOrig.afterCleanBindU64 dst (symEvalScalarRes st se).val n hnoub hpIn hden

theorem symEvalExpr_var_ssaPureU64_eq
    {ω0 : SymValuation} {params bound : List VarId} {st : SymExecState} {env : VarEnv}
    (hst : PureU64SymState ω0 params bound st env)
    (dst : VarId)
    (src : VarId) (hsrc : bound.contains src = true) :
    ∃ n : UInt64,
      evalScalarExpr env (.var src) = .ok (.u64 n) ∧
      PureU64SymState ω0 params (dst :: bound)
        (symEvalExpr st dst .i64 (.scalar (.var src)))
        (env.bind dst (.u64 n)) := by
  rcases hst with ⟨hbuf, halloc, hsarr, hobj, hext, htup, hrefc, hrce, hexcl, hbool, hu256,
    hubSt, hnoubSt, hunsupSt, hexhSt, hnotup, hpar, hbound⟩
  have hstOrig : PureU64SymState ω0 params bound st env :=
    ⟨hbuf, halloc, hsarr, hobj, hext, htup, hrefc, hrce, hexcl, hbool, hu256,
      hubSt, hnoubSt, hunsupSt, hexhSt, hnotup, hpar, hbound⟩
  obtain ⟨n, henv, hnoub, hpIn, hden⟩ := hbound src hsrc
  have hsort : symExprScalarSort? st (st.lookupVar src).expr = some 1 :=
    symExprScalarSort_of_isPureU64SymExprIn st params hbool (fun p hp => (hpar p hp).1) _ hpIn
  refine ⟨n, by simp [evalScalarExpr, henv], ?_⟩
  have hclear : st.clearAlias dst = st := by
    cases st
    simp at hbuf
    subst hbuf
    rfl
  have hresSrc : st.resolveBuf src = src := by simp [SymExecState.resolveBuf, hbuf]
  have hroot : resolveScalarRoot? st (.var src) = (some src, (st.lookupVar src).nonPoison, true, false) := by
    simp [resolveScalarRoot?, hresSrc, hnoub]
  have hdefF : st.isDefinitelyHeapRoot src = false :=
    SymExecState.isDefinitelyHeapRoot_false_of_clean hbuf halloc hsarr hobj hrefc hrce hexcl hnotup src
  have hmark : st.markU64Var dst =
      { st with u64Vars := dst :: st.u64Vars.filter (· != dst), boolVars := [], u256Vars := [] } :=
    SymExecState.markU64Var_clean dst hbuf halloc hsarr hobj hbool hu256 hnotup
  have hunmarkEq : (st.markU64Var dst).unmarkTypedTuple dst =
      { st with u64Vars := dst :: st.u64Vars.filter (· != dst), boolVars := [], u256Vars := [] } := by
    rw [hmark]
    unfold SymExecState.unmarkTypedTuple
    cases st
    simp at htup
    subst htup
    rfl
  have hnilSrc : ([] : List VarId).contains src = false := rfl
  rw [symEvalExpr.eq_def]
  dsimp only [callSlotKind]
  have hptrF : (some false == some true) = false := rfl
  rw [hroot]
  dsimp only []
  rw [hptrF, hdefF, hclear]
  have hbr1 : (if ((src != dst) && (false || false)) = true then st.aliasBuf dst src
      else if (!false && !false) = true then st else st) = st := by
    cases src != dst <;> rfl
  rw [hbr1, hdefF]
  simp only [Bool.not_false, Bool.true_and, ↓reduceIte]
  rw [hsort, htup, hnilSrc]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hunmarkEq]
  let stMarked : SymExecState :=
    { st with u64Vars := dst :: st.u64Vars.filter (· != dst), boolVars := [], u256Vars := [] }
  have hheapObjF : stMarked.isHeapObjectRoot src = false := by
    unfold SymExecState.isHeapObjectRoot SymExecState.resolveBuf
    have hbM : stMarked.bufAliases = [] := hbuf
    have heM : stMarked.extSeenRoots = [] := hext
    rw [hbM]; dsimp only [List.lookup]
    have hdM : stMarked.isDefinitelyHeapRoot src = false :=
      SymExecState.isDefinitelyHeapRoot_false_of_clean hbuf halloc hsarr hobj hrefc hrce hexcl hnotup src
    rw [hdM, heM, hnilSrc]; rfl
  rw [hheapObjF]
  simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte, Bool.and_true]
  have handSelf : ((st.lookupVar src).nonPoison && (st.lookupVar src).nonPoison) = (st.lookupVar src).nonPoison :=
    Bool.and_self _
  rw [handSelf]
  have hsvEq : { expr := (st.lookupVar src).expr, nonPoison := (st.lookupVar src).nonPoison, noUB := (st.lookupVar src).noUB } =
      st.lookupVar src := by cases st.lookupVar src; rfl
  rw [hsvEq]
  exact hstOrig.afterCleanBindU64 dst (st.lookupVar src) n hnoub hpIn hden

/-- Code-level denotational soundness of `symExecCode` over straight-line pure 64-bit SSA `LNIRCode`:
    for any `evalFuel : Nat` and any `symFuel ≥ codeStepDepth c`, both `evalCode evalFuel` and
    `symExecCode symFuel` succeed without exhaustion or UB, and `denoteSymExpr ω0 retExpr`
    evaluates to the exact concrete `.u64` result returned by `evalCode evalFuel`. -/
theorem symExecCode_pureU64_denotes :
    ∀ (c : LNIRCode) (evalFuel symFuel unrollBound : Nat) (ω0 : SymValuation) (params bound : List VarId)
      (st : SymExecState) (env : VarEnv) (heap : HeapState),
      isSSAPureU64Code bound c = true →
      codeStepDepth c ≤ symFuel →
      PureU64SymState ω0 params bound st env →
      ∃ n : UInt64,
        evalCode evalFuel env heap c = .ok (.u64 n, heap) ∧
        let (st', retExpr) := symExecCode symFuel unrollBound st c true
        st'.symExhausted = false ∧
        st'.symUnsupported = false ∧
        st'.noUB = true ∧
        st'.ubCond = .constBool true ∧
        isPureU64SymExprIn params retExpr = true ∧
        denoteSymExpr ω0 retExpr = .ok (.u64 n) := by
  intro c
  induction c with
  | ret v =>
    intro evalFuel symFuel unrollBound ω0 params bound st env heap hssa hfuel hst
    cases symFuel with
    | zero => simp [codeStepDepth] at hfuel
    | succ fuel' =>
      simp only [isSSAPureU64Code] at hssa
      rcases hst with ⟨hbuf, halloc, hsarr, hobj, hext, htup, hrefc, hrce, hexcl, hbool, hu256,
        hubSt, hnoubSt, hunsupSt, hexhSt, hnotup, hpar, hbound⟩
      obtain ⟨n, henv, hnoub, hpIn, hden⟩ := hbound v hssa
      have hparVal : ∀ id : VarId, params.contains id = true → ∃ m : UInt64, ω0.varVal id = some (.u64 m) :=
        fun id hid => (hpar id hid).2
      obtain ⟨n2, hden1, hdenNorm⟩ := normSymExpr_pureU64_denotes params ω0 (st.lookupVar v).expr hpIn hparVal
      have hn_eq : n2 = n := by
        rw [hden] at hden1
        injection hden1 with h1
        injection h1 with h2
        exact h2.symm
      subst hn_eq
      have hexp : st.expandHeapExpr 16 (st.lookupVar v).expr = (st.lookupVar v).expr :=
        expandHeapExpr_clean_id hbuf halloc hrefc hrce hnotup 16 (st.lookupVar v).expr hpIn
      have hresV : st.resolveBuf v = v := by simp [SymExecState.resolveBuf, hbuf]
      have hnilV : ([] : List VarId).contains v = false := rfl
      have hretSeedEq :
          matchTupleSymExpr (st.lookupVar v).expr
            (fun _ => if (!st.typedTuples.contains v) = true then SymExpr.symVar v else (st.lookupVar v).expr)
            (st.lookupVar v).expr = (st.lookupVar v).expr :=
        symExpr_matchTuple_eq_of_not_tuple (st.lookupVar v).expr
          (fun _ => if (!st.typedTuples.contains v) = true then SymExpr.symVar v else (st.lookupVar v).expr)
          (st.lookupVar v).expr (hnotup v)
      refine ⟨n2, by simp [evalCode, henv], ?_⟩
      have hsymRet : symExecCode (fuel' + 1) unrollBound st (.ret v) true =
          ({ st with noUB := st.noUB && (st.lookupVar v).noUB, nonPoison := st.nonPoison && (st.lookupVar v).nonPoison },
           normSymExpr (st.lookupVar v).expr) := by
        rw [symExecCode.eq_def]
        dsimp only []
        rw [hresV, halloc, hnilV]
        have horF : (false || (!true && st.isHeapObjectRoot v)) = false := rfl
        rw [horF]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact Prod.ext rfl (congrArg normSymExpr ((congrArg (st.expandHeapExpr 16) hretSeedEq).trans hexp))
      rw [hsymRet]
      exact ⟨hexhSt, hunsupSt, by simp [hnoubSt, hnoub], hubSt,
        normSymExpr_pureU64In params _ hpIn, hdenNorm⟩
  | letBind dst ty val k ih =>
    intro evalFuel symFuel unrollBound ω0 params bound st env heap hssa hfuel hst
    cases ty <;> try (cases val <;> cases hssa)
    cases val <;> try cases hssa
    rename_i se
    cases symFuel with
    | zero => simp [codeStepDepth] at hfuel
    | succ fuel' =>
      change (!(bound.contains dst) && scalarExprAllBound bound se && isPureU64ScalarExpr se &&
        isSSAPureU64Code (dst :: bound) k) = true at hssa
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hssa
      rcases hssa with ⟨⟨⟨_, hall⟩, hpure⟩, hkSsa⟩
      simp only [codeStepDepth, Nat.add_le_add_iff_right] at hfuel
      cases hse : se with
      | select _ _ _ | constBool _ | fma _ _ _ =>
        rw [hse] at hpure; simp [isPureU64ScalarExpr] at hpure
      | var src =>
        rw [hse] at hall
        simp only [scalarExprAllBound] at hall
        obtain ⟨nv, hevalV, hst1⟩ := symEvalExpr_var_ssaPureU64_eq hst dst src hall
        obtain ⟨n, hevalK, ihK⟩ :=
          ih evalFuel fuel' unrollBound ω0 params (dst :: bound)
            (symEvalExpr st dst .i64 (.scalar (.var src))) (env.bind dst (.u64 nv)) heap hkSsa hfuel hst1
        refine ⟨n, ?_, ?_⟩
        · simp only [evalCode, evalExpr, hevalV]; exact hevalK
        · rw [symExecCode.eq_def]; dsimp only []; exact ihK
      | constU64 v =>
        rw [hse] at hpure hall
        obtain ⟨nv, hevalV, hst1⟩ :=
          symEvalExpr_nonVar_ssaPureU64_eq hst dst (.constU64 v) (fun _ h => by cases h) hpure hall
        obtain ⟨n, hevalK, ihK⟩ :=
          ih evalFuel fuel' unrollBound ω0 params (dst :: bound)
            (symEvalExpr (st.clearAlias dst) dst .i64 (.scalar (.constU64 v))) (env.bind dst (.u64 nv)) heap hkSsa hfuel hst1
        refine ⟨n, ?_, ?_⟩
        · simp only [evalCode, evalExpr, hevalV]; exact hevalK
        · rw [symExecCode.eq_def]; dsimp only [callSlotKind, resolveScalarRoot?, Bool.and_true, ↓reduceIte]; exact ihK
      | unaryOp op a =>
        rw [hse] at hpure hall
        obtain ⟨nv, hevalV, hst1⟩ :=
          symEvalExpr_nonVar_ssaPureU64_eq hst dst (.unaryOp op a) (fun _ h => by cases h) hpure hall
        obtain ⟨n, hevalK, ihK⟩ :=
          ih evalFuel fuel' unrollBound ω0 params (dst :: bound)
            (symEvalExpr (st.clearAlias dst) dst .i64 (.scalar (.unaryOp op a))) (env.bind dst (.u64 nv)) heap hkSsa hfuel hst1
        refine ⟨n, ?_, ?_⟩
        · simp only [evalCode, evalExpr, hevalV]; exact hevalK
        · rw [symExecCode.eq_def]; dsimp only [callSlotKind, resolveScalarRoot?, Bool.and_true, ↓reduceIte]; exact ihK
      | binOp op l r =>
        rw [hse] at hpure hall
        obtain ⟨nv, hevalV, hst1⟩ :=
          symEvalExpr_nonVar_ssaPureU64_eq hst dst (.binOp op l r) (fun _ h => by cases h) hpure hall
        obtain ⟨n, hevalK, ihK⟩ :=
          ih evalFuel fuel' unrollBound ω0 params (dst :: bound)
            (symEvalExpr (st.clearAlias dst) dst .i64 (.scalar (.binOp op l r))) (env.bind dst (.u64 nv)) heap hkSsa hfuel hst1
        refine ⟨n, ?_, ?_⟩
        · simp only [evalCode, evalExpr, hevalV]; exact hevalK
        · rw [symExecCode.eq_def]; dsimp only [callSlotKind, resolveScalarRoot?, Bool.and_true, ↓reduceIte]; exact ihK
  | rawStore _ _ _ _ _ | incRef _ _ _ | decRef _ _ _ | ite _ _ _
  | seqFor _ _ _ _ _ _ _ _ | parFor _ _ _ _ _ _ | unreachable =>
    intro _ _ _ _ _ _ _ _ _ hssa _ _; cases hssa

/-- Equality of normalized `symExecCode` return expressions over straight-line pure 64-bit SSA `LNIRCode`
    discharges concrete `evalCode` observational equivalence for ANY `evalFuel : Nat` on every
    well-typed `.u64` parameter environment. -/
theorem symExecCode_pureU64_eval_eq
    (src tgt : LNIRCode) (evalFuel symFuel unrollBound : Nat) (params : List VarId)
    (st : SymExecState) (env : VarEnv) (heap : HeapState)
    (hssaSrc : isSSAPureU64Code params src = true)
    (hssaTgt : isSSAPureU64Code params tgt = true)
    (hfuelSrc : codeStepDepth src ≤ symFuel)
    (hfuelTgt : codeStepDepth tgt ≤ symFuel)
    (hst : PureU64SymState (SymValuation.ofVarEnv env) params params st env)
    (hretEq : (symExecCode symFuel unrollBound st src true).2 = (symExecCode symFuel unrollBound st tgt true).2) :
    evalCode evalFuel env heap tgt = evalCode evalFuel env heap src ∧
    ∃ n : UInt64, evalCode evalFuel env heap src = .ok (.u64 n, heap) := by
  obtain ⟨nSrc, hevalSrc, _, _, _, _, _, hdenSrc⟩ :=
    symExecCode_pureU64_denotes src evalFuel symFuel unrollBound (SymValuation.ofVarEnv env) params params st env heap hssaSrc hfuelSrc hst
  obtain ⟨nTgt, hevalTgt, _, _, _, _, _, hdenTgt⟩ :=
    symExecCode_pureU64_denotes tgt evalFuel symFuel unrollBound (SymValuation.ofVarEnv env) params params st env heap hssaTgt hfuelTgt hst
  have hdenSrc' : denoteSymExpr (SymValuation.ofVarEnv env) (symExecCode symFuel unrollBound st src true).2 = .ok (.u64 nSrc) := hdenSrc
  have hdenTgt' : denoteSymExpr (SymValuation.ofVarEnv env) (symExecCode symFuel unrollBound st tgt true).2 = .ok (.u64 nTgt) := hdenTgt
  rw [hretEq] at hdenSrc'
  rw [hdenSrc'] at hdenTgt'
  injection hdenTgt' with hvalEq
  injection hvalEq with hnEq
  subst hnEq
  exact ⟨hevalTgt.trans hevalSrc.symm, ⟨nSrc, hevalSrc⟩⟩

/-- Forward-refinement corollary (`evalCode` forward simulation on `.u64` parameter environments):
    whenever `symExecCode` produces equal normalized return expressions on `src` and `tgt`,
    every successful `evalCode fuel env heap src = .ok (v, heap')` evaluates identically in `tgt`. -/
theorem symExecCode_pureU64_codeRefines_on_u64Env
    (src tgt : LNIRCode) (symFuel unrollBound : Nat) (params : List VarId)
    (st : SymExecState)
    (hssaSrc : isSSAPureU64Code params src = true)
    (hssaTgt : isSSAPureU64Code params tgt = true)
    (hfuelSrc : codeStepDepth src ≤ symFuel)
    (hfuelTgt : codeStepDepth tgt ≤ symFuel)
    (hretEq : (symExecCode symFuel unrollBound st src true).2 = (symExecCode symFuel unrollBound st tgt true).2) :
    ∀ (fuel : Nat) (env : VarEnv) (heap : HeapState) (v : Val) (heap' : HeapState),
      PureU64SymState (SymValuation.ofVarEnv env) params params st env →
      evalCode fuel env heap src = .ok (v, heap') →
      evalCode fuel env heap tgt = .ok (v, heap') := by
  intro fuel env heap v heap' hst hsrc
  have heq := (symExecCode_pureU64_eval_eq src tgt fuel symFuel unrollBound params st env heap
    hssaSrc hssaTgt hfuelSrc hfuelTgt hst hretEq).1
  exact heq.trans hsrc

end LeanNative.Proofs
