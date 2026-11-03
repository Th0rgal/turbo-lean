import LeanNative.IR.RealLCNFBridge
import LeanNative.IR.RealLCNFSemantics
import LeanNative.Semantics.Eval

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

/-- Invariant linking pure `RealBridgeState` to source `LEnv` and target `VarEnv`. -/
structure BridgeStateInv (st : RealBridgeState) (lenv : LEnv) (venv : VarEnv) : Prop where
  fvar_lt   : ∀ x vid, st.lookupFVar? x = some vid → vid < st.nextVarId
  fvar_val  : ∀ x vid, st.lookupFVar? x = some vid → lenv.vals x = venv vid ∧ (venv vid).isSome
  fvar_ty   : ∀ x vid, st.lookupFVar? x = some vid → lenv.tys x = some (st.getVarType vid)
  fvar_ctor : ∀ x vid, st.lookupFVar? x = some vid → lenv.ctors x = st.getActiveCtor? vid
  fvar_inj  : ∀ x1 x2 vid, st.lookupFVar? x1 = some vid → st.lookupFVar? x2 = some vid → x1 = x2
  jp_sync   : ∀ j ps body, st.lookupJp? j = some (ps, body) →
                lenv.jps j = some { params := ps, code := body }

private theorem lnirTypeEqFuel_sound : ∀ fuel (a b : LNIRType), lnirTypeEqFuel fuel a b = true → a = b
  | 0, _, _, h => False.elim (by cases h)
  | fuel + 1, a, b, h => by
    cases a <;> cases b <;> try rfl
    all_goals try exact congrArg LNIRType.sarray (lnirTypeEqFuel_sound fuel _ _ h)
    all_goals try exact congrArg LNIRType.rawPtr (lnirTypeEqFuel_sound fuel _ _ h)
    all_goals try (unfold lnirTypeEqFuel at h; cases h)
    all_goals try (rename_i ys; cases ys <;> unfold lnirTypeEqFuel at h <;> cases h)
    all_goals try (rename_i ys _; cases ys <;> unfold lnirTypeEqFuel at h <;> cases h)
    rename_i xs ys
    cases xs <;> cases ys
    · rfl
    · unfold lnirTypeEqFuel at h; cases h
    · unfold lnirTypeEqFuel at h; cases h
    · rename_i x xs' y ys'
      dsimp only [lnirTypeEqFuel] at h
      rcases Bool.and_eq_true_iff.mp h with ⟨h1, h2⟩
      rw [lnirTypeEqFuel_sound fuel x y h1, LNIRType.tuple.inj (lnirTypeEqFuel_sound fuel (.tuple xs') (.tuple ys') h2)]

private theorem lnirTypeEq_sound (a b : LNIRType) (h : lnirTypeEq a b = true) : a = b :=
  lnirTypeEqFuel_sound 32 a b h

private theorem evalExpr_scalar (venv : VarEnv) (hst : HeapState) (se : ScalarExpr) (v : Val)
    (h : evalScalarExpr venv se = .ok v) :
    evalExpr venv hst (.scalar se) = .ok (v, hst) := by simp only [evalExpr, h]

private theorem evalScalar_var (venv : VarEnv) (vid : VarId) (v : Val) (h : venv vid = some v) :
    evalScalarExpr venv (.var vid) = .ok v := by simp only [evalScalarExpr, h]

private theorem evalScalar_binOp (venv : VarEnv) (op : BinOp) (a b : ScalarExpr) (va vb : Val)
    (ha : evalScalarExpr venv a = .ok va) (hb : evalScalarExpr venv b = .ok vb) :
    evalScalarExpr venv (.binOp op a b) = evalBinOp op va vb := by simp only [evalScalarExpr, ha, hb]

private theorem evalScalar_unaryOp (venv : VarEnv) (op : UnaryOp) (a : ScalarExpr) (va : Val)
    (ha : evalScalarExpr venv a = .ok va) :
    evalScalarExpr venv (.unaryOp op a) = evalUnaryOp op va := by simp only [evalScalarExpr, ha]

private theorem evalScalar_select_bool (venv : VarEnv) (c t e : ScalarExpr) (b : Bool)
    (hc : evalScalarExpr venv c = .ok (.bool b)) :
    evalScalarExpr venv (.select c t e) = if b then evalScalarExpr venv t else evalScalarExpr venv e := by
  cases b <;> simp only [evalScalarExpr, hc, ↓reduceIte, Bool.false_eq_true]

private theorem maskOf_eq (arch : TargetArch) (ty : LNIRType) (mask : UInt64)
    (hm : scalarWidthMask? ty arch = some mask) : maskOf arch ty = mask.toBitVec := by
  cases ty with
  | i8 | i16 | i32 | i64 => injection hm with h; subst h; rfl
  | usize =>
    unfold scalarWidthMask? at hm; cases hus : archSupportsUSize arch
    · simp only [hus, Bool.false_eq_true, ↓reduceIte] at hm; exact nomatch hm
    · simp only [hus, ↓reduceIte] at hm; injection hm with h; subst h; cases arch <;> rfl
  | _ => exact nomatch hm

private theorem shiftMaskOf_eq (arch : TargetArch) (ty : LNIRType) (sMask : UInt64)
    (hm : scalarShiftMask? ty arch = some sMask) : shiftMaskOf arch ty = sMask.toBitVec := by
  cases ty with
  | i8 | i16 | i32 | i64 => injection hm with h; subst h; rfl
  | usize =>
    unfold scalarShiftMask? at hm; cases hus : archSupportsUSize arch
    · simp only [hus, Bool.false_eq_true, ↓reduceIte] at hm; exact nomatch hm
    · simp only [hus, ↓reduceIte] at hm; injection hm with h; subst h; cases arch <;> rfl
  | _ => exact nomatch hm

private theorem u64_and_lt (x m : UInt64) (k : Nat) (hmk : m.toNat < 2 ^ k) (hk : 2 ^ k ≤ 64) :
    (x &&& m).toNat < 64 := by
  rw [UInt64.toNat_and]; exact Nat.lt_of_lt_of_le (Nat.and_lt_two_pow x.toNat hmk) hk

private theorem sMask_lt_64 (arch : TargetArch) (ty : LNIRType) (sMask : UInt64)
    (hm : scalarShiftMask? ty arch = some sMask) (h63 : (sMask == 63) = false) (x : UInt64) :
    (x &&& sMask).toNat < 64 := by
  cases ty with
  | i8 => injection hm with h; subst h; exact u64_and_lt x 7 3 (by decide) (by decide)
  | i16 => injection hm with h; subst h; exact u64_and_lt x 15 4 (by decide) (by decide)
  | i32 => injection hm with h; subst h; exact u64_and_lt x 31 5 (by decide) (by decide)
  | i64 => injection hm with h; subst h; exact False.elim (by cases h63)
  | usize =>
    unfold scalarShiftMask? at hm; cases hus : archSupportsUSize arch
    · simp only [hus, Bool.false_eq_true, ↓reduceIte] at hm; exact nomatch hm
    · simp only [hus, ↓reduceIte] at hm; injection hm with h; subst h
      cases arch with
      | wasm32 => exact u64_and_lt x 31 5 (by decide) (by decide)
      | _ => exact False.elim (by cases h63)
  | _ => exact nomatch hm

private theorem wrapBool_sound (venv : VarEnv) (cmp : ScalarExpr) (retTy : LNIRType)
    (se : ScalarExpr) (b : Bool) (v : Val)
    (hs : (if lnirTypeEq retTy .i1 then some cmp
           else if lnirTypeEq retTy .i8 then some (.select cmp (.constU64 1) (.constU64 0))
           else none) = some se)
    (ho : wrapBoolOut b retTy = .ok v) (hc : evalScalarExpr venv cmp = .ok (.bool b)) :
    evalScalarExpr venv se = .ok v := by
  unfold wrapBoolOut at ho
  cases h1 : lnirTypeEq retTy .i1
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hs ho
    cases h8 : lnirTypeEq retTy .i8
    · simp only [h8, Bool.false_eq_true, ↓reduceIte] at hs; cases hs
    · simp only [h8, ↓reduceIte] at hs ho; cases hs; cases ho
      simp only [evalScalarExpr, hc]; cases b <;> rfl
  · simp only [h1, ↓reduceIte] at hs ho; cases hs; cases ho; exact hc

private theorem evalMaskedVar (venv : VarEnv) (vid : VarId) (n mask : UInt64) (arch : TargetArch) (ty : LNIRType)
    (hvid : venv vid = some (.u64 n)) (hm : scalarWidthMask? ty arch = some mask) :
    evalScalarExpr venv (if mask == 0xFFFFFFFFFFFFFFFF then .var vid else .binOp .bitAnd (.var vid) (.constU64 mask)) =
      .ok (.u64 (UInt64.ofBitVec (masked arch ty n.toBitVec))) := by
  have hm' := maskOf_eq arch ty mask hm
  have hval : UInt64.ofBitVec (masked arch ty n.toBitVec) = n &&& mask := by unfold masked; rw [hm']; rfl
  rw [hval]
  cases hall : (mask == 0xFFFFFFFFFFFFFFFF)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [evalScalar_binOp venv .bitAnd (.var vid) (.constU64 mask) (.u64 n) (.u64 mask)
          (evalScalar_var venv vid (.u64 n) hvid) rfl]; rfl
  · simp only [↓reduceIte]; have hm1 : mask = 0xFFFFFFFFFFFFFFFF := eq_of_beq hall; subst hm1
    have hand : (n &&& 0xFFFFFFFFFFFFFFFF) = n := UInt64.eq_of_toBitVec_eq BitVec.and_allOnes
    rw [hand]; exact evalScalar_var venv vid (.u64 n) hvid

private theorem evalMaskOut (venv : VarEnv) (raw : ScalarExpr) (w : BitVec 64) (mask : UInt64)
    (arch : TargetArch) (ty : LNIRType)
    (hraw : evalScalarExpr venv raw = .ok (.u64 (UInt64.ofBitVec w)))
    (hm : scalarWidthMask? ty arch = some mask) :
    evalScalarExpr venv (if mask == 0xFFFFFFFFFFFFFFFF then raw else .binOp .bitAnd raw (.constU64 mask)) =
      .ok (ofWord (masked arch ty w)) := by
  have hm' := maskOf_eq arch ty mask hm
  have hval : masked arch ty w = w &&& mask.toBitVec := by unfold masked; rw [hm']
  rw [hval]
  cases hall : (mask == 0xFFFFFFFFFFFFFFFF)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [evalScalar_binOp venv .bitAnd raw (.constU64 mask) (.u64 (UInt64.ofBitVec w)) (.u64 mask) hraw rfl]; rfl
  · simp only [↓reduceIte]; have hm1 : mask = 0xFFFFFFFFFFFFFFFF := eq_of_beq hall; subst hm1
    have hand : w &&& (0xFFFFFFFFFFFFFFFF : UInt64).toBitVec = w := BitVec.and_allOnes
    rw [hand]; exact hraw

private theorem u64_shl_lt64 (w s : BitVec 64) (hs : s.toNat < 64) :
    (UInt64.ofBitVec w <<< UInt64.ofBitVec s).toBitVec = w <<< s := by
  change w <<< (s % 64#64) = w <<< s; rw [BitVec.umod_eq_of_lt hs]

private theorem u64_shr_lt64 (w s : BitVec 64) (hs : s.toNat < 64) :
    (UInt64.ofBitVec w >>> UInt64.ofBitVec s) = UInt64.ofBitVec (w >>> s) := by
  apply UInt64.eq_of_toBitVec_eq; change w >>> (s % 64#64) = w >>> s; rw [BitVec.umod_eq_of_lt hs]

private theorem fvarId_beq_iff (a b : Lean.FVarId) : (a == b) = true ↔ a = b := by
  cases a with | mk na => cases b with | mk nb =>
    change (na == nb) = true ↔ (⟨na⟩ : Lean.FVarId) = ⟨nb⟩; simp

private instance : LawfulBEq Lean.FVarId where
  eq_of_beq h := (fvarId_beq_iff _ _).mp h
  rfl {a} := (fvarId_beq_iff a a).mpr rfl

private theorem find_filter_ne {α : Type} (xs : List α) (p q : α → Bool)
    (hpq : ∀ a, p a = true → q a = true) : (xs.filter q).find? p = xs.find? p := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.filter]
    cases hp : p a
    · cases hq : q a <;> simp [List.find?, hp, ih]
    · rw [hpq a hp]; simp [List.find?, hp]

private theorem assoc_find_cons {K V : Type} [BEq K] [LawfulBEq K]
    (xs : List (K × V)) (k q : K) (v : V) :
    (((k, v) :: xs.filter (fun (x, _) => x != k)).find? (fun (x, _) => x == q)) =
      if q == k then some (k, v) else xs.find? (fun (x, _) => x == q) := by
  dsimp only [List.find?]
  by_cases hkq : (k == q) = true
  · have heq : k = q := beq_iff_eq.mp hkq; subst heq; simp
  · have hqk : (q == k) = false := by
      cases h : q == k
      · rfl
      · exact False.elim (hkq (beq_iff_eq.mpr (beq_iff_eq.mp h).symm))
    simp only [hkq, hqk, Bool.false_eq_true, ↓reduceIte]
    apply find_filter_ne; intro a ha
    have haq : a.1 = q := beq_iff_eq.mp ha; subst haq; simpa [bne] using hqk

private theorem lookupFVar_cons (fvarMap : List (Lean.FVarId × VarId)) (x y : Lean.FVarId) (vid : VarId) :
    RealBridgeState.lookupFVar? { fvarMap := (x, vid) :: fvarMap.filter (fun (f, _) => f != x) } y =
      if y == x then some vid else RealBridgeState.lookupFVar? { fvarMap := fvarMap } y := by
  unfold RealBridgeState.lookupFVar?; rw [assoc_find_cons]; cases y == x <;> rfl

private theorem getVarType_setVarType (st : RealBridgeState) (vid w : VarId) (ty : LNIRType) :
    (st.setVarType vid ty).getVarType w = if w == vid then ty else st.getVarType w := by
  unfold RealBridgeState.setVarType RealBridgeState.getVarType; rw [assoc_find_cons]; cases w == vid <;> rfl

private theorem getActiveCtor_setActiveCtor (st : RealBridgeState) (vid w : VarId) (c : Lean.Name) :
    (st.setActiveCtor vid c).getActiveCtor? w = if w == vid then some c else st.getActiveCtor? w := by
  unfold RealBridgeState.setActiveCtor RealBridgeState.getActiveCtor?; rw [assoc_find_cons]; cases w == vid <;> rfl

private theorem lookupJp_setJpDecl (st : RealBridgeState) (j q : Lean.FVarId)
    (ps : List (Lean.Compiler.LCNF.Param .impure)) (body : Lean.Compiler.LCNF.Code .impure) :
    (st.setJpDecl j ps body).lookupJp? q = if q == j then some (ps, body) else st.lookupJp? q := by
  unfold RealBridgeState.setJpDecl RealBridgeState.lookupJp?; rw [assoc_find_cons]; cases q == j <;> rfl

private theorem getActiveCtor_filter_ne (activeCtor : List (VarId × Lean.Name)) (vid w : VarId) (hw : w ≠ vid) :
    RealBridgeState.getActiveCtor? { activeCtor := activeCtor.filter (fun (v, _) => v != vid) } w =
      RealBridgeState.getActiveCtor? { activeCtor := activeCtor } w := by
  unfold RealBridgeState.getActiveCtor?; dsimp only; congr 1; apply find_filter_ne; intro a ha
  have haw : a.1 = w := beq_iff_eq.mp ha; subst haw; simp [bne, hw]

private theorem u64_and_allOnes (x : UInt64) : (x &&& 0xFFFFFFFFFFFFFFFF) = x :=
  UInt64.eq_of_toBitVec_eq BitVec.and_allOnes

private theorem u64_and_idem (x m : UInt64) : (x &&& m &&& m) = (x &&& m) := by
  apply UInt64.eq_of_toBitVec_eq
  change (x.toBitVec &&& m.toBitVec) &&& m.toBitVec = x.toBitVec &&& m.toBitVec
  rw [BitVec.and_assoc, BitVec.and_self]

/-- `lowerLitValuePure` agrees with the independent `evalLit` and emits a constant scalar expression. -/
theorem lowerLitValuePure_sound (arch : TargetArch) (lit : Lean.Compiler.LCNF.LitValue)
    (retTy : LNIRType) (allowObj : Bool) (expr : LNIRExpr) (v : Val)
    (venv : VarEnv) (hst : HeapState)
    (h_lower : lowerLitValuePure lit retTy arch allowObj = .ok expr)
    (h_eval : evalLit arch lit retTy allowObj = .ok v) :
    evalExpr venv hst expr = .ok (v, hst) ∧ (∃ se, expr = .scalar se ∧ ∀ u, se ≠ .var u) := by
  unfold lowerLitValuePure at h_lower; unfold evalLit at h_eval
  cases h_usize : (lnirTypeEq retTy .usize && !archSupportsUSize arch)
  · rw [h_usize] at h_lower h_eval
    dsimp only [↓reduceIte, bind, Except.bind, pure, Except.pure] at h_lower h_eval
    cases lit with
    | str _ => simp [throw, throwThe, MonadExceptOf.throw] at h_lower
    | uint8 x | uint16 x | uint32 x | uint64 x =>
      cases h_m : scalarWidthMask? retTy arch <;> cases h_i1 : lnirTypeEq retTy .i1 <;>
        simp [h_m, h_i1] at h_lower h_eval <;> subst h_lower <;> subst h_eval <;>
        exact ⟨rfl, _, rfl, fun _ h => nomatch h⟩
    | usize x =>
      cases h_sup : archSupportsUSize arch
      · simp [h_sup, throw, throwThe, MonadExceptOf.throw] at h_lower
      · have harch : masked arch .usize x.toBitVec = (x &&& archUSizeMask arch).toBitVec := by
          cases arch <;> simp [masked, maskOf, widthOf, TargetArch.isWasm, archUSizeMask] <;> rfl
        simp only [h_sup, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h_lower h_eval
        rw [harch] at h_eval
        cases h_m : scalarWidthMask? retTy arch <;> cases h_i1 : lnirTypeEq retTy .i1 <;>
          simp [h_m, h_i1] at h_lower h_eval <;> subst h_lower <;> subst h_eval <;>
          exact ⟨rfl, _, rfl, fun _ h => nomatch h⟩
    | nat n =>
      cases h_nat : ((lnirTypeEq retTy .taggedPtr || lnirTypeEq retTy .objPtr) && !allowObj)
      · rw [h_nat] at h_lower h_eval; dsimp only [↓reduceIte] at h_lower h_eval
        have hbv : BitVec.ofNat 64 (n % 2 ^ 64) = (n % 2 ^ 64).toUInt64.toBitVec := rfl
        rw [hbv] at h_eval
        cases h_m : scalarWidthMask? retTy arch <;> cases h_i1 : lnirTypeEq retTy .i1 <;>
          simp [h_m, h_i1, u64_and_allOnes, u64_and_idem] at h_lower h_eval <;>
          subst h_lower <;> subst h_eval <;> exact ⟨rfl, _, rfl, fun _ h => nomatch h⟩
      · rw [h_nat] at h_eval; simp at h_eval
  · rw [h_usize] at h_eval; simp at h_eval

/-- `lowerRealArg` on an `.fvar` returns the value and static type bound in `lenv` without mutating `st`. -/
theorem lowerRealArg_sound (ctx : RealBridgeCtx) (st : RealBridgeState) (lenv : LEnv) (venv : VarEnv)
    (arg : Lean.Compiler.LCNF.Arg .impure) (allowObj : Bool) (vid : VarId) (st' : RealBridgeState)
    (hinv : BridgeStateInv st lenv venv)
    (h_lower : lowerRealArg ctx st arg allowObj = .ok (vid, st')) :
    ∃ x v, arg = .fvar x ∧ st.lookupFVar? x = some vid ∧ evalArg lenv.vals arg = .ok v ∧
      venv vid = some v ∧ (lenv.tys x).getD .objPtr = st.getVarType vid ∧ st' = st := by
  cases arg with
  | erased | type _ _ => simp [lowerRealArg] at h_lower
  | fvar x =>
    unfold lowerRealArg at h_lower
    cases hv : st.lookupFVar? x with
    | none => simp [hv] at h_lower
    | some vid0 =>
      simp only [hv] at h_lower
      split at h_lower
      · injection h_lower with hpair; rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
        rcases hinv.fvar_val x vid0 hv with ⟨heq, hsome⟩
        have hty := hinv.fvar_ty x vid0 hv
        cases hsome' : venv vid0 with
        | none => simp [hsome'] at hsome
        | some v =>
          exact ⟨x, v, rfl, hv, by simp [evalArg, heq, hsome'], rfl, by simp [hty], rfl⟩
      · simp at h_lower

/-- `lowerRealArgList` lowers argument lists without mutating `st` and aligns `evalArgs` with `evalVarList`. -/
theorem lowerRealArgList_sound (ctx : RealBridgeCtx) (st : RealBridgeState) (lenv : LEnv) (venv : VarEnv)
    (allowObj : Bool) (args : List (Lean.Compiler.LCNF.Arg .impure))
    (argVars : List VarId) (st' : RealBridgeState)
    (hinv : BridgeStateInv st lenv venv)
    (h_lower : lowerRealArgList ctx st allowObj args = .ok (argVars, st')) :
    ∃ vs, evalArgs lenv.vals args = .ok vs ∧ evalVarList venv argVars = .ok vs ∧
      argVars.length = args.length ∧ st' = st ∧
      argVars.map st.getVarType = args.map (fun | .fvar x => (lenv.tys x).getD .objPtr | _ => .objPtr) := by
  induction args generalizing argVars st' with
  | nil =>
    simp only [lowerRealArgList] at h_lower
    injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
    exact ⟨[], rfl, rfl, rfl, rfl, rfl⟩
  | cons a rest ih =>
    unfold lowerRealArgList at h_lower
    dsimp only [bind, Except.bind, pure, Except.pure] at h_lower
    cases ha : lowerRealArg ctx st a allowObj with
    | error _ => simp [ha] at h_lower
    | ok pair1 =>
      rcases pair1 with ⟨vid, st1⟩
      simp only [ha] at h_lower
      rcases lowerRealArg_sound ctx st lenv venv a allowObj vid st1 hinv ha with
        ⟨x, v, rfl, _, hevalA, hv, htyA, hst1⟩
      subst st1
      cases hrest : lowerRealArgList ctx st allowObj rest with
      | error _ => rw [hrest] at h_lower; exact nomatch h_lower
      | ok pair2 =>
        rcases pair2 with ⟨vsVars, st2⟩
        rw [hrest] at h_lower; dsimp only at h_lower
        injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
        rcases ih vsVars st2 hrest with ⟨vs, hevalRest, hvarRest, hlen, rfl, hmap⟩
        refine ⟨v :: vs, ?_, ?_, by simp [hlen], rfl, by simp [htyA, hmap]⟩
        · simp [evalArgs, hevalA, hevalRest]
        · simp [evalVarList, hv, hvarRest]

/-- A lowered canonical scalar binary intrinsic evaluates to the same word `wordBin` produces. -/
theorem lowerScalarIntrinsicExpr_sound (venv : VarEnv) (arch : TargetArch) (op : BinOp)
    (ty retTy : LNIRType) (vl vr : VarId) (va vb : Val) (se : ScalarExpr) (v : Val)
    (hL : venv vl = some va) (hR : venv vr = some vb)
    (hs : lowerScalarIntrinsicExpr? op vl vr ty retTy arch = some se)
    (ho : wordBin arch op ty retTy va vb = .ok v) :
    evalScalarExpr venv se = .ok v ∧ (∀ u, se ≠ .var u) := by
  unfold lowerScalarIntrinsicExpr? at hs
  cases husz : (lnirTypeEq ty .usize || lnirTypeEq retTy .usize) && !archSupportsUSize arch
  · simp only [husz, Bool.false_eq_true, ↓reduceIte] at hs
    cases hi1 : lnirTypeEq ty .i1
    · simp only [hi1, Bool.false_eq_true, ↓reduceIte] at hs
      unfold wordBin at ho; simp only [hi1, Bool.false_eq_true, ↓reduceIte] at ho
      cases va with
      | u64 na =>
        cases vb with
        | u64 nb =>
          simp only [husz, Bool.false_eq_true, ↓reduceIte] at ho
          cases hm : scalarWidthMask? ty arch with
          | none => simp [hm] at hs
          | some mask =>
            simp only [hm] at hs
            cases hsm : scalarShiftMask? ty arch with
            | none => simp [hsm] at hs
            | some sMask =>
              simp only [hsm] at hs
              let lExpr : ScalarExpr := if mask == 0xFFFFFFFFFFFFFFFF then .var vl else .binOp .bitAnd (.var vl) (.constU64 mask)
              let rExpr : ScalarExpr := if mask == 0xFFFFFFFFFFFFFFFF then .var vr else .binOp .bitAnd (.var vr) (.constU64 mask)
              let am := masked arch ty na.toBitVec
              let bm := masked arch ty nb.toBitVec
              have hmaskL := evalMaskedVar venv vl na mask arch ty hL hm
              have hmaskR := evalMaskedVar venv vr nb mask arch ty hR hm
              have hnotVarMask : ∀ (r : ScalarExpr), (∀ u, r ≠ .var u) →
                  ∀ u, (if mask == 0xFFFFFFFFFFFFFFFF then r else .binOp .bitAnd r (.constU64 mask)) ≠ .var u := by
                intro r hr u; split
                · exact hr u
                · intro hc; exact nomatch hc
              have hnotVarWrap : ∀ (c : ScalarExpr) (e : ScalarExpr), (∀ u, c ≠ .var u) →
                  (if lnirTypeEq retTy .i1 then some c
                   else if lnirTypeEq retTy .i8 then some (.select c (.constU64 1) (.constU64 0))
                   else none) = some e → ∀ u, e ≠ .var u := by
                intro c e hc hw u
                cases h1 : lnirTypeEq retTy .i1 <;> simp only [h1, Bool.false_eq_true, ↓reduceIte] at hw
                · cases h8 : lnirTypeEq retTy .i8 <;> simp only [h8, Bool.false_eq_true, ↓reduceIte] at hw
                  · exact False.elim (by cases hw)
                  · injection hw with hw'; subst hw'; intro h; exact False.elim (by cases h)
                · injection hw with hw'; subst hw'; exact hc u
              cases op with
              | add | sub | mul | bitAnd | bitOr | bitXor =>
                cases hret : lnirTypeEq retTy ty
                · simp [hret] at ho
                · simp only [hret, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hs ho
                  injection hs with hse; subst hse; injection ho with hv; subst hv
                  refine ⟨evalMaskOut venv _ _ mask arch ty ?_ hm, hnotVarMask _ (fun _ h => nomatch h)⟩
                  rw [evalScalar_binOp _ _ _ _ _ _ hmaskL hmaskR]; rfl
              | div =>
                cases hret : lnirTypeEq retTy ty
                · simp [hret] at ho
                · simp only [hret, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hs ho
                  injection hs with hse; subst hse; injection ho with hv; subst hv
                  refine ⟨?_, fun _ h => nomatch h⟩
                  have hcmp : evalScalarExpr venv (.binOp .eq rExpr (.constU64 0)) = .ok (.bool (bm == 0#64)) := by
                    rw [evalScalar_binOp _ _ _ _ _ _ hmaskR rfl]; rfl
                  rw [evalScalar_select_bool venv _ _ _ (bm == 0#64) hcmp]
                  cases hz : (bm == 0#64)
                  · simp only [Bool.false_eq_true, ↓reduceIte]; rw [evalScalar_binOp _ _ _ _ _ _ hmaskL hmaskR]; rfl
                  · simp only [↓reduceIte]; rfl
              | mod =>
                cases hret : lnirTypeEq retTy ty
                · simp [hret] at ho
                · simp only [hret, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hs ho
                  injection hs with hse; subst hse; injection ho with hv; subst hv
                  refine ⟨?_, fun _ h => nomatch h⟩
                  have hcmp : evalScalarExpr venv (.binOp .eq rExpr (.constU64 0)) = .ok (.bool (bm == 0#64)) := by
                    rw [evalScalar_binOp _ _ _ _ _ _ hmaskR rfl]; rfl
                  rw [evalScalar_select_bool venv _ _ _ (bm == 0#64) hcmp]
                  cases hz : (bm == 0#64)
                  · simp only [Bool.false_eq_true, ↓reduceIte]; rw [evalScalar_binOp _ _ _ _ _ _ hmaskL hmaskR]; rfl
                  · simp only [↓reduceIte]; exact hmaskL
              | eq | lt | le =>
                exact ⟨wrapBool_sound venv _ retTy se _ v hs ho
                  (by rw [evalScalar_binOp _ _ _ _ _ _ hmaskL hmaskR]; rfl),
                  hnotVarWrap _ se (fun _ h => False.elim (by cases h)) hs⟩
              | shl =>
                cases hret : lnirTypeEq retTy ty
                · simp [hret] at ho
                · simp only [hret, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hs ho
                  injection hs with hse; subst hse
                  have hsm' := shiftMaskOf_eq arch ty sMask hsm
                  have h63eq : (shiftMaskOf arch ty == 63#64) = (sMask == 63) := by rw [hsm']; rfl
                  rw [h63eq] at ho
                  refine ⟨?_, hnotVarMask _ (fun _ h => nomatch h)⟩
                  cases h63 : (sMask == 63)
                  · simp only [h63, Bool.false_eq_true, ↓reduceIte] at ho ⊢
                    injection ho with hv; subst hv
                    have hsh := sMask_lt_64 arch ty sMask hsm h63 (UInt64.ofBitVec bm)
                    have hAmt : evalScalarExpr venv (.binOp .bitAnd rExpr (.constU64 sMask)) =
                        .ok (.u64 (UInt64.ofBitVec (bm &&& sMask.toBitVec))) := by
                      rw [evalScalar_binOp _ _ _ _ _ _ hmaskR rfl]; rfl
                    have hraw : evalScalarExpr venv (.binOp .shl lExpr (.binOp .bitAnd rExpr (.constU64 sMask))) =
                        .ok (.u64 (UInt64.ofBitVec am <<< UInt64.ofBitVec (bm &&& sMask.toBitVec))) := by
                      rw [evalScalar_binOp _ _ _ _ _ _ hmaskL hAmt]; rfl
                    have hout := evalMaskOut venv _ (UInt64.ofBitVec am <<< UInt64.ofBitVec (bm &&& sMask.toBitVec)).toBitVec
                      mask arch ty hraw hm
                    rw [u64_shl_lt64 am (bm &&& sMask.toBitVec) hsh, hsm'.symm] at hout; exact hout
                  · simp only [h63, ↓reduceIte] at ho ⊢
                    injection ho with hv; subst hv
                    exact evalMaskOut venv _ (UInt64.ofBitVec am <<< UInt64.ofBitVec bm).toBitVec mask arch ty
                      (by rw [evalScalar_binOp _ _ _ _ _ _ hmaskL hmaskR]; rfl) hm
              | shr =>
                cases hret : lnirTypeEq retTy ty
                · simp [hret] at ho
                · simp only [hret, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hs ho
                  injection hs with hse; subst hse
                  have hsm' := shiftMaskOf_eq arch ty sMask hsm
                  have h63eq : (shiftMaskOf arch ty == 63#64) = (sMask == 63) := by rw [hsm']; rfl
                  rw [h63eq] at ho
                  refine ⟨?_, fun _ h => nomatch h⟩
                  cases h63 : (sMask == 63)
                  · simp only [h63, Bool.false_eq_true, ↓reduceIte] at ho ⊢
                    injection ho with hv; subst hv
                    have hsh := sMask_lt_64 arch ty sMask hsm h63 (UInt64.ofBitVec bm)
                    have hAmt : evalScalarExpr venv (.binOp .bitAnd rExpr (.constU64 sMask)) =
                        .ok (.u64 (UInt64.ofBitVec (bm &&& sMask.toBitVec))) := by
                      rw [evalScalar_binOp _ _ _ _ _ _ hmaskR rfl]; rfl
                    have hout : evalScalarExpr venv (.binOp .shr lExpr (.binOp .bitAnd rExpr (.constU64 sMask))) =
                        .ok (.u64 (UInt64.ofBitVec am >>> UInt64.ofBitVec (bm &&& sMask.toBitVec))) := by
                      rw [evalScalar_binOp _ _ _ _ _ _ hmaskL hAmt]; rfl
                    rw [u64_shr_lt64 am (bm &&& sMask.toBitVec) hsh, hsm'.symm] at hout; exact hout
                  · simp only [h63, ↓reduceIte] at ho ⊢
                    injection ho with hv; subst hv
                    rw [evalScalar_binOp _ _ _ _ _ _ hmaskL hmaskR]; rfl
              | _ => simp at hs
        | _ => exact False.elim (by cases ho)
      | _ => exact False.elim (by cases ho)
    · simp only [hi1, ↓reduceIte] at hs
      unfold wordBin at ho; simp only [hi1, ↓reduceIte] at ho
      have hnotVarWrap : ∀ (c : ScalarExpr) (e : ScalarExpr), (∀ u, c ≠ .var u) →
          (if lnirTypeEq retTy .i1 then some c
           else if lnirTypeEq retTy .i8 then some (.select c (.constU64 1) (.constU64 0))
           else none) = some e → ∀ u, e ≠ .var u := by
        intro c e hc hw u
        cases h1 : lnirTypeEq retTy .i1 <;> simp only [h1, Bool.false_eq_true, ↓reduceIte] at hw
        · cases h8 : lnirTypeEq retTy .i8 <;> simp only [h8, Bool.false_eq_true, ↓reduceIte] at hw
          · exact False.elim (by cases hw)
          · injection hw with hw'; subst hw'; intro h; exact False.elim (by cases h)
        · injection hw with hw'; subst hw'; exact hc u
      cases va with
      | bool a =>
        cases vb with
        | bool b =>
          have hva := evalScalar_var venv vl (.bool a) hL
          have hvb := evalScalar_var venv vr (.bool b) hR
          cases op with
          | bitAnd =>
            exact ⟨wrapBool_sound venv _ retTy se (a && b) v hs ho
              (by rw [evalScalar_select_bool venv (.var vl) (.var vr) (.constBool false) a hva]; cases a; exact rfl; exact hvb),
              hnotVarWrap _ se (fun _ h => False.elim (by cases h)) hs⟩
          | bitOr =>
            exact ⟨wrapBool_sound venv _ retTy se (a || b) v hs ho
              (by rw [evalScalar_select_bool venv (.var vl) (.constBool true) (.var vr) a hva]; cases a; exact hvb; exact rfl),
              hnotVarWrap _ se (fun _ h => False.elim (by cases h)) hs⟩
          | bitXor =>
            exact ⟨wrapBool_sound venv _ retTy se (a != b) v hs ho
              (by rw [evalScalar_unaryOp venv .not _ (.bool (a == b)) (by rw [evalScalar_binOp _ _ _ _ _ _ hva hvb]; rfl)]; cases a <;> cases b <;> rfl),
              hnotVarWrap _ se (fun _ h => False.elim (by cases h)) hs⟩
          | eq =>
            exact ⟨wrapBool_sound venv _ retTy se (a == b) v hs ho
              (by rw [evalScalar_binOp _ _ _ _ _ _ hva hvb]; rfl),
              hnotVarWrap _ se (fun _ h => False.elim (by cases h)) hs⟩
          | _ => simp at hs
        | _ => exact False.elim (by cases op <;> cases ho)
      | _ => exact False.elim (by cases op <;> cases vb <;> cases ho)
  · simp only [husz, ↓reduceIte] at hs; exact False.elim (by cases hs)

private theorem toCond_sound (venv : VarEnv) (vid : VarId) (ty : LNIRType) (va : Val)
    (ce : ScalarExpr) (b : Bool) (hv : venv vid = some va)
    (hc : (if lnirTypeEq ty .i1 then some (.var vid)
           else if lnirTypeEq ty .i8 then some (.unaryOp .not (.binOp .eq (.binOp .bitAnd (.var vid) (.constU64 1)) (.constU64 0)))
           else none) = some ce)
    (hb : boolBitTyped va ty = some b) :
    evalScalarExpr venv ce = .ok (.bool b) := by
  unfold boolBitTyped at hb
  cases h1 : lnirTypeEq ty .i1
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hc hb
    cases h8 : lnirTypeEq ty .i8
    · simp [h8] at hc
    · simp only [h8, ↓reduceIte] at hc hb; injection hc with hc'; subst hc'
      cases va with
      | u64 n =>
        injection hb with hb'; subst hb'
        have hand : evalScalarExpr venv (.binOp .bitAnd (.var vid) (.constU64 1)) = .ok (.u64 (n &&& 1)) := by
          rw [evalScalar_binOp _ _ _ _ _ _ (evalScalar_var venv vid (.u64 n) hv) rfl]; rfl
        have heq : evalScalarExpr venv (.binOp .eq (.binOp .bitAnd (.var vid) (.constU64 1)) (.constU64 0)) =
            .ok (.bool ((n &&& 1) == 0)) := by rw [evalScalar_binOp _ _ _ _ _ _ hand rfl]; rfl
        rw [evalScalar_unaryOp venv .not _ (.bool ((n &&& 1) == 0)) heq]
        have hbn : (!(n &&& 1 == 0)) = (n &&& 1 != 0) := by simp [bne]
        simp [evalUnaryOp, hbn]
      | _ => exact nomatch hb
  · simp only [h1, ↓reduceIte] at hc hb; injection hc with hc'; subst hc'
    cases va with
    | bool b0 => injection hb with hb'; subst hb'; exact evalScalar_var venv vid (.bool b0) hv
    | _ => exact nomatch hb

private theorem wrapOutExpr_sound (venv : VarEnv) (hst : HeapState) (cmp : ScalarExpr) (retTy : LNIRType)
    (expr : LNIRExpr) (b : Bool) (v : Val) (hcmp : ∀ u, cmp ≠ .var u)
    (hs : (if lnirTypeEq retTy .i1 then some (LNIRExpr.scalar cmp)
           else if lnirTypeEq retTy .i8 then some (.scalar (.select cmp (.constU64 1) (.constU64 0)))
           else none) = some expr)
    (ho : wrapBoolOut b retTy = .ok v) (hc : evalScalarExpr venv cmp = .ok (.bool b)) :
    evalExpr venv hst expr = .ok (v, hst) ∧ (∃ se, expr = .scalar se ∧ ∀ u, se ≠ .var u) := by
  cases h1 : lnirTypeEq retTy .i1
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hs
    cases h8 : lnirTypeEq retTy .i8
    · simp [h8] at hs
    · simp only [h8, ↓reduceIte] at hs; injection hs with hs'; subst hs'
      refine ⟨evalExpr_scalar venv hst _ v (wrapBool_sound venv cmp retTy _ b v ?_ ho hc), _, rfl, fun _ h => nomatch h⟩
      simp [h1, h8]
  · simp only [h1, ↓reduceIte] at hs; injection hs with hs'; subst hs'
    refine ⟨evalExpr_scalar venv hst cmp v (wrapBool_sound venv cmp retTy cmp b v ?_ ho hc), cmp, rfl, hcmp⟩
    simp [h1]

/-- `lowerBoolBinIntrinsic?` agrees with `evalBoolBinCall?`. -/
theorem lowerBoolBinIntrinsic_sound (venv : VarEnv) (hst : HeapState) (fn : Lean.Name)
    (vl vr : VarId) (tL tR retTy : LNIRType) (va vb : Val) (expr : LNIRExpr) (v : Val)
    (hL : venv vl = some va) (hR : venv vr = some vb)
    (hs : lowerBoolBinIntrinsic? fn vl vr [tL, tR] retTy = some expr)
    (ho : evalBoolBinCall? fn va vb tL tR retTy = some (.ok v)) :
    evalExpr venv hst expr = .ok (v, hst) ∧ (∃ se, expr = .scalar se ∧ ∀ u, se ≠ .var u) := by
  unfold lowerBoolBinIntrinsic? at hs; unfold evalBoolBinCall? at ho
  dsimp only [bind, Option.bind] at hs
  cases hcL : (if lnirTypeEq tL .i1 then some (ScalarExpr.var vl)
               else if lnirTypeEq tL .i8 then some (.unaryOp .not (.binOp .eq (.binOp .bitAnd (.var vl) (.constU64 1)) (.constU64 0)))
               else none) with
  | none => simp [hcL] at hs
  | some cL =>
    simp only [hcL] at hs
    cases hcR : (if lnirTypeEq tR .i1 then some (ScalarExpr.var vr)
                 else if lnirTypeEq tR .i8 then some (.unaryOp .not (.binOp .eq (.binOp .bitAnd (.var vr) (.constU64 1)) (.constU64 0)))
                 else none) with
    | none => simp [hcR] at hs
    | some cR =>
      simp only [hcR] at hs
      have hguard_false : ((!lnirTypeEq tL .i1 && !lnirTypeEq tL .i8) || (!lnirTypeEq tR .i1 && !lnirTypeEq tR .i8) ||
          (!lnirTypeEq retTy .i1 && !lnirTypeEq retTy .i8)) = false →
          ∀ (op : Bool → Bool → Bool),
          (if (!lnirTypeEq tL .i1 && !lnirTypeEq tL .i8) || (!lnirTypeEq tR .i1 && !lnirTypeEq tR .i8) ||
              (!lnirTypeEq retTy .i1 && !lnirTypeEq retTy .i8) then none
           else match boolBitTyped va tL, boolBitTyped vb tR with
             | some a, some b => some (wrapBoolOut (op a b) retTy)
             | _, _ => some (.error (.typeError "boolean intrinsic expects typed bool or i8-encoded bool"))) = some (.ok v) →
          ∃ a b, boolBitTyped va tL = some a ∧ boolBitTyped vb tR = some b ∧ wrapBoolOut (op a b) retTy = .ok v := by
        intro hg op hop; rw [hg] at hop; simp only [Bool.false_eq_true, ↓reduceIte] at hop
        cases hbL : boolBitTyped va tL <;> cases hbR : boolBitTyped vb tR <;> simp [hbL, hbR] at hop
        exact ⟨_, _, rfl, rfl, hop⟩
      have hExt : ∀ (op : Bool → Bool → Bool),
          (if (!lnirTypeEq tL .i1 && !lnirTypeEq tL .i8) || (!lnirTypeEq tR .i1 && !lnirTypeEq tR .i8) ||
              (!lnirTypeEq retTy .i1 && !lnirTypeEq retTy .i8) then none
           else match boolBitTyped va tL, boolBitTyped vb tR with
             | some a, some b => some (wrapBoolOut (op a b) retTy)
             | _, _ => some (.error (.typeError "boolean intrinsic expects typed bool or i8-encoded bool"))) = some (.ok v) →
          ∃ a b, evalScalarExpr venv cL = .ok (.bool a) ∧ evalScalarExpr venv cR = .ok (.bool b) ∧ wrapBoolOut (op a b) retTy = .ok v := by
        intro op hop
        cases hg : ((!lnirTypeEq tL .i1 && !lnirTypeEq tL .i8) || (!lnirTypeEq tR .i1 && !lnirTypeEq tR .i8) ||
            (!lnirTypeEq retTy .i1 && !lnirTypeEq retTy .i8))
        · rcases hguard_false hg op hop with ⟨a, b, ha, hb, hw⟩
          exact ⟨a, b, toCond_sound venv vl tL va cL a hL hcL ha, toCond_sound venv vr tR vb cR b hR hcR hb, hw⟩
        · rw [hg] at hop; exact nomatch hop
      by_cases hand : fn == ``Bool.and
      · simp only [hand, ↓reduceIte] at hs ho; rcases hExt _ ho with ⟨a, b, ha, hb, hw⟩
        exact wrapOutExpr_sound venv hst _ retTy expr (a && b) v (fun _ h => False.elim (by cases h)) hs hw
          (by rw [evalScalar_select_bool venv cL cR (.constBool false) a ha]; cases a; exact rfl; exact hb)
      · by_cases hor : fn == ``Bool.or
        · simp only [hand, hor, Bool.false_eq_true, ↓reduceIte] at hs ho; rcases hExt _ ho with ⟨a, b, ha, hb, hw⟩
          exact wrapOutExpr_sound venv hst _ retTy expr (a || b) v (fun _ h => False.elim (by cases h)) hs hw
            (by rw [evalScalar_select_bool venv cL (.constBool true) cR a ha]; cases a; exact hb; exact rfl)
        · by_cases hxor : (fn == ``Bool.xor || fn == `Bool.bne || fn == `bne)
          · simp only [hand, hor, hxor, Bool.false_eq_true, ↓reduceIte] at hs ho; rcases hExt _ ho with ⟨a, b, ha, hb, hw⟩
            exact wrapOutExpr_sound venv hst _ retTy expr (a != b) v (fun _ h => False.elim (by cases h)) hs hw
              (by rw [evalScalar_unaryOp venv .not _ (.bool (a == b)) (by rw [evalScalar_binOp _ _ _ _ _ _ ha hb]; rfl)]; cases a <;> cases b <;> rfl)
          · by_cases hbeq : fn == ``Bool.beq
            · simp only [hand, hor, hxor, hbeq, Bool.false_eq_true, ↓reduceIte] at hs ho; rcases hExt _ ho with ⟨a, b, ha, hb, hw⟩
              exact wrapOutExpr_sound venv hst _ retTy expr (a == b) v (fun _ h => False.elim (by cases h)) hs hw
                (by rw [evalScalar_binOp _ _ _ _ _ _ ha hb]; rfl)
            · simp [hand, hor, hxor, hbeq] at hs

private theorem canonicalUIntCastWalk_spec (fuel : Nat) (fn : Lean.Name) (tyA retTy : LNIRType)
    (arch : TargetArch)
    (pairs : List (Lean.Name × LNIRType × UInt64 × Lean.Name × String × LNIRType × UInt64))
    (effMask : UInt64)
    (hw : canonicalUIntCastWalk fuel fn [tyA] retTy arch pairs = some effMask) :
    (∃ p ∈ pairs, fn = Lean.Name.str p.1 p.2.2.2.2.1) ∧
    ∀ va v, canonicalCastEval fuel
        (pairs.map (fun (src, sTy, sm, dst, suf, dTy, dm) => (src, sTy, sm.toBitVec, dst, suf, dTy, dm.toBitVec)))
        fn va tyA retTy = some (.ok v) →
      ∃ n, va = .u64 n ∧ v = .u64 (n &&& effMask) := by
  induction fuel generalizing pairs with
  | zero => exact nomatch hw
  | succ f ih =>
    cases pairs with
    | nil => exact nomatch hw
    | cons hd rest =>
      rcases hd with ⟨src, sTy, sm, dst, suf, dTy, dm⟩
      unfold canonicalUIntCastWalk at hw
      have hcond : (src != dst && fn == Lean.Name.str src suf && lnirTypeListEq [tyA] [sTy] && lnirTypeEq retTy dTy) =
          (src != dst && fn == Lean.Name.str src suf && lnirTypeEq tyA sTy && lnirTypeEq retTy dTy) := by
        simp [lnirTypeListEq]
      rw [hcond] at hw
      cases hc : (src != dst && fn == Lean.Name.str src suf && lnirTypeEq tyA sTy && lnirTypeEq retTy dTy)
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hw
        rcases ih rest hw with ⟨⟨p, hp, hfn⟩, heval⟩
        refine ⟨⟨p, List.mem_cons_of_mem _ hp, hfn⟩, fun va v hce => ?_⟩
        simp only [List.map, canonicalCastEval, hc, Bool.false_eq_true, ↓reduceIte] at hce
        exact heval va v hce
      · simp only [hc, ↓reduceIte] at hw; injection hw with hm; subst hm
        rcases Bool.and_eq_true_iff.mp hc with ⟨hc1, _⟩
        rcases Bool.and_eq_true_iff.mp hc1 with ⟨hc2, _⟩
        rcases Bool.and_eq_true_iff.mp hc2 with ⟨_, hfn⟩
        refine ⟨⟨(src, sTy, sm, dst, suf, dTy, dm), List.Mem.head _, beq_iff_eq.mp hfn⟩, fun va v hce => ?_⟩
        simp only [List.map, canonicalCastEval, hc, ↓reduceIte] at hce
        cases va with
        | u64 n =>
          injection hce with hok; injection hok with hv; subst hv
          refine ⟨n, rfl, congrArg Val.u64 ?_⟩
          apply UInt64.eq_of_toBitVec_eq
          by_cases h : sm ≤ dm
          · have hbv : sm.toBitVec.toNat ≤ dm.toBitVec.toNat := h
            have hmin : min sm dm = sm := by dsimp [Min.min]; split <;> first | rfl | contradiction
            have hite : (if sm.toBitVec.toNat ≤ dm.toBitVec.toNat then sm.toBitVec else dm.toBitVec) = sm.toBitVec := by
              split <;> first | rfl | contradiction
            simp only [hmin, UInt64.toBitVec_and, hite]
          · have hbv : ¬(sm.toBitVec.toNat ≤ dm.toBitVec.toNat) := h
            have hmin : min sm dm = dm := by dsimp [Min.min]; split <;> first | rfl | contradiction
            have hite : (if sm.toBitVec.toNat ≤ dm.toBitVec.toNat then sm.toBitVec else dm.toBitVec) = dm.toBitVec := by
              split <;> first | rfl | contradiction
            simp only [hmin, UInt64.toBitVec_and, hite]
        | _ => injection hce with herr; exact nomatch herr

/-- Unary and integer-cast intrinsics agree with `evalUnaryOrCastCall?`. -/
theorem lowerUnaryAndCast_sound (venv : VarEnv) (hst : HeapState) (arch : TargetArch)
    (fn : Lean.Name) (varg : VarId) (tyA retTy : LNIRType) (va : Val) (expr : LNIRExpr) (v : Val)
    (hA : venv varg = some va)
    (hs : (match canonicalUIntCastMask? fn [tyA] retTy arch with
           | some effMask => some (LNIRExpr.scalar (.binOp .bitAnd (.var varg) (.constU64 effMask)))
           | none => lowerUnaryScalarIntrinsic? fn varg [tyA] retTy arch) = some expr)
    (ho : evalUnaryOrCastCall? arch fn va tyA retTy = some (.ok v)) :
    evalExpr venv hst expr = .ok (v, hst) ∧ (∃ se, expr = .scalar se ∧ ∀ u, se ≠ .var u) := by
  cases hcast : canonicalUIntCastMask? fn [tyA] retTy arch with
  | some effMask =>
    rw [hcast] at hs; injection hs with hs'; subst hs'
    unfold canonicalUIntCastMask? at hcast
    let types : List (Lean.Name × String × LNIRType × UInt64) :=
      [(``UInt8, "toUInt8", .i8, 255), (``UInt16, "toUInt16", .i16, 65535),
       (``UInt32, "toUInt32", .i32, 4294967295), (``UInt64, "toUInt64", .i64, 18446744073709551615)] ++
      (if archSupportsUSize arch then [(``USize, "toUSize", .usize, archUSizeMask arch)] else [])
    let tPairs := types.flatMap fun (src, _, srcTy, srcMask) =>
      types.map fun (dst, toSuffix, dstTy, dstMask) => (src, srcTy, srcMask, dst, toSuffix, dstTy, dstMask)
    rcases canonicalUIntCastWalk_spec 64 fn tyA retTy arch tPairs effMask hcast with ⟨⟨p, hp, hfn⟩, heval⟩
    rcases p with ⟨srcN, sTy, sm, dstN, sufS, dTy, dm⟩
    dsimp only at hfn
    have hmem : (srcN == ``UInt8 || srcN == ``UInt16 || srcN == ``UInt32 || srcN == ``UInt64 || srcN == ``USize) = true ∧
        (sufS == "toUInt8" || sufS == "toUInt16" || sufS == "toUInt32" ||
         sufS == "toUInt64" || sufS == "toUSize") = true := by
      rcases List.mem_flatMap.mp hp with ⟨⟨s1, s2, s3, s4⟩, hs0, hp0⟩
      rcases List.mem_map.mp hp0 with ⟨⟨d1, d2, d3, d4⟩, hd0, heq⟩
      rcases Prod.mk.inj heq with ⟨rfl, hp1⟩
      rcases Prod.mk.inj hp1 with ⟨_, hp2⟩
      rcases Prod.mk.inj hp2 with ⟨_, hp3⟩
      rcases Prod.mk.inj hp3 with ⟨_, hp4⟩
      rcases Prod.mk.inj hp4 with ⟨rfl, _⟩
      constructor
      · simp only [types, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs0
        rcases hs0 with (hs1 | hs1 | hs1 | hs1) | hs1
        · cases hs1; rfl
        · cases hs1; rfl
        · cases hs1; rfl
        · cases hs1; rfl
        · cases arch <;> simp only [archSupportsUSize, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hs1 <;>
            (first | exact False.elim hs1 | (cases hs1; rfl))
      · simp only [types, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd0
        rcases hd0 with (hd1 | hd1 | hd1 | hd1) | hd1
        · cases hd1; rfl
        · cases hd1; rfl
        · cases hd1; rfl
        · cases hd1; rfl
        · cases arch <;> simp only [archSupportsUSize, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hd1 <;>
            (first | exact False.elim hd1 | (cases hd1; rfl))
    have hneS : ∀ (s2 : Lean.Name) (u2 : String), (srcN == s2) = false ∨ (sufS == u2) = false →
        (Lean.Name.str srcN sufS == Lean.Name.str s2 u2) = false := by
      intro s2 u2 hne
      cases he : (Lean.Name.str srcN sufS == Lean.Name.str s2 u2)
      · rfl
      · rcases Lean.Name.str.inj (beq_iff_eq.mp he) with ⟨rfl, rfl⟩; simp at hne
    have hsrcNeBool : (srcN == ``Bool) = false := by
      rcases hmem with ⟨h1, _⟩; simp only [Bool.or_eq_true, beq_iff_eq] at h1
      rcases h1 with (((rfl | rfl) | rfl) | rfl) | rfl <;> decide
    have hsufNe : (sufS == "complement") = false ∧ (sufS == "neg") = false := by
      rcases hmem with ⟨_, h2⟩; simp only [Bool.or_eq_true, beq_iff_eq] at h2
      rcases h2 with (((rfl | rfl) | rfl) | rfl) | rfl <;> decide
    subst hfn
    have hbF := fun u2 => hneS ``Bool u2 (Or.inl hsrcNeBool)
    have hcF := fun s2 => hneS s2 "complement" (Or.inr hsufNe.1)
    have hnF := fun s2 => hneS s2 "neg" (Or.inr hsufNe.2)
    have hd1 : (Lean.Name.str srcN sufS == ``Bool.not) = false := hbF "not"
    have hd2 : (Lean.Name.str srcN sufS == ``Bool.toUInt8 || Lean.Name.str srcN sufS == ``Bool.toUInt16 ||
        Lean.Name.str srcN sufS == ``Bool.toUInt32 || Lean.Name.str srcN sufS == ``Bool.toUInt64 ||
        Lean.Name.str srcN sufS == ``Bool.toUSize) = false := by
      simp [hbF "toUInt8", hbF "toUInt16", hbF "toUInt32", hbF "toUInt64", hbF "toUSize"]
    have hd3 : (if Lean.Name.str srcN sufS == ``UInt8.complement then some (LNIRType.i8, false)
         else if Lean.Name.str srcN sufS == ``UInt16.complement then some (.i16, false)
         else if Lean.Name.str srcN sufS == ``UInt32.complement then some (.i32, false)
         else if Lean.Name.str srcN sufS == ``UInt64.complement then some (.i64, false)
         else if Lean.Name.str srcN sufS == ``USize.complement then some (.usize, false)
         else if Lean.Name.str srcN sufS == ``UInt8.neg then some (.i8, true)
         else if Lean.Name.str srcN sufS == ``UInt16.neg then some (.i16, true)
         else if Lean.Name.str srcN sufS == ``UInt32.neg then some (.i32, true)
         else if Lean.Name.str srcN sufS == ``UInt64.neg then some (.i64, true)
         else if Lean.Name.str srcN sufS == ``USize.neg then some (.usize, true)
         else none) = none := by
      simp [hcF ``UInt8, hcF ``UInt16, hcF ``UInt32, hcF ``UInt64, hcF ``USize,
            hnF ``UInt8, hnF ``UInt16, hnF ``UInt32, hnF ``UInt64, hnF ``USize]
    unfold evalUnaryOrCastCall? at ho
    simp only [hd1, hd2, hd3, Bool.false_eq_true, ↓reduceIte] at ho
    have ho' : canonicalCastEval 64
        (tPairs.map (fun (src, sTy, sm, dst, suf, dTy, dm) => (src, sTy, sm.toBitVec, dst, suf, dTy, dm.toBitVec)))
        (Lean.Name.str srcN sufS) va tyA retTy = some (.ok v) := by
      cases arch <;> exact ho
    rcases heval va v ho' with ⟨n, rfl, rfl⟩
    refine ⟨evalExpr_scalar venv hst _ _ ?_, _, rfl, fun _ h => nomatch h⟩
    rw [evalScalar_binOp _ _ _ _ _ _ (evalScalar_var venv varg (.u64 n) hA) rfl]; rfl
  | none =>
    rw [hcast] at hs
    unfold lowerUnaryScalarIntrinsic? at hs; unfold evalUnaryOrCastCall? at ho
    by_cases hnot : fn == ``Bool.not
    · simp only [hnot, ↓reduceIte] at hs ho
      cases h1 : (lnirTypeEq tyA .i1 && lnirTypeEq retTy .i1)
      · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hs ho
        cases h8 : (lnirTypeEq tyA .i8 && lnirTypeEq retTy .i8)
        · simp [h8] at hs
        · simp only [h8, ↓reduceIte] at hs ho; injection hs with hs'; subst hs'
          cases va with
          | u64 n =>
            injection ho with hok; injection hok with hv; subst hv
            refine ⟨evalExpr_scalar venv hst _ _ ?_, _, rfl, fun _ h => nomatch h⟩
            have hand : evalScalarExpr venv (.binOp .bitAnd (.var varg) (.constU64 1)) = .ok (.u64 (n &&& 1)) := by
              rw [evalScalar_binOp _ _ _ _ _ _ (evalScalar_var venv varg (.u64 n) hA) rfl]; rfl
            have heq : evalScalarExpr venv (.binOp .eq (.binOp .bitAnd (.var varg) (.constU64 1)) (.constU64 0)) =
                .ok (.bool ((n &&& 1) == 0)) := by rw [evalScalar_binOp _ _ _ _ _ _ hand rfl]; rfl
            rw [evalScalar_select_bool venv _ _ _ ((n &&& 1) == 0) heq]
            cases (n &&& 1) == 0 <;> rfl
          | _ => injection ho with herr; exact nomatch herr
      · simp only [h1, ↓reduceIte] at hs ho; injection hs with hs'; subst hs'
        cases va with
        | bool b =>
          injection ho with hok; injection hok with hv; subst hv
          refine ⟨evalExpr_scalar venv hst _ _ ?_, _, rfl, fun _ h => nomatch h⟩
          rw [evalScalar_unaryOp venv .not _ (.bool b) (evalScalar_var venv varg (.bool b) hA)]; rfl
        | _ => injection ho with herr; exact nomatch herr
    · by_cases hb2u : (fn == ``Bool.toUInt8 || fn == ``Bool.toUInt16 ||
          fn == ``Bool.toUInt32 || fn == ``Bool.toUInt64 || fn == ``Bool.toUSize)
      · simp only [hnot, hb2u, Bool.false_eq_true, ↓reduceIte] at hs ho
        let expectedRet : LNIRType :=
          if fn == ``Bool.toUInt8 then .i8
          else if fn == ``Bool.toUInt16 then .i16
          else if fn == ``Bool.toUInt32 then .i32
          else if fn == ``Bool.toUInt64 then .i64
          else .usize
        have hs' : (if !((lnirTypeEq tyA .i1 || lnirTypeEq tyA .i8) && lnirTypeEq retTy expectedRet &&
            isSupportedStage1BScalarType expectedRet arch) then none
          else if lnirTypeEq tyA .i1 then some (.scalar (.select (.var varg) (.constU64 1) (.constU64 0)))
          else some (.scalar (.binOp .bitAnd (.var varg) (.constU64 1)))) = some expr := hs
        cases hg : ((lnirTypeEq tyA .i1 || lnirTypeEq tyA .i8) && lnirTypeEq retTy expectedRet && isSupportedStage1BScalarType expectedRet arch)
        · simp [hg] at hs'
        · simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hs'
          rcases Bool.and_eq_true_iff.mp hg with ⟨hg1, hsup⟩
          rcases Bool.and_eq_true_iff.mp hg1 with ⟨ht18, hretE⟩
          have ho' : (if !lnirTypeEq retTy expectedRet || !isSupportedStage1BScalarType expectedRet arch then none
            else if lnirTypeEq tyA .i1 then
              some <| match va with
                | .bool b => Except.ok (Val.u64 (if b then 1 else 0))
                | _ => Except.error (UBError.typeError "select condition must be bool, u64, or u256")
            else if lnirTypeEq tyA .i8 then
              some <| match va with
                | .u64 n => Except.ok (Val.u64 (n &&& 1))
                | _ => Except.error (UBError.typeError "bitAnd requires u64 or u256")
            else none) = some (.ok v) := by cases va <;> exact ho
          simp only [hretE, hsup, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at ho'
          cases hi1 : lnirTypeEq tyA .i1
          · simp only [hi1, Bool.false_or] at ht18
            simp only [hi1, ht18, Bool.false_eq_true, ↓reduceIte] at hs' ho'
            injection hs' with hse; subst hse
            cases va with
            | u64 n =>
              injection ho' with hok; injection hok with hv; subst hv
              refine ⟨evalExpr_scalar venv hst _ _ ?_, _, rfl, fun _ h => nomatch h⟩
              rw [evalScalar_binOp _ _ _ _ _ _ (evalScalar_var venv varg (.u64 n) hA) rfl]; rfl
            | _ => injection ho' with herr; exact nomatch herr
          · simp only [hi1, ↓reduceIte] at hs' ho'; injection hs' with hse; subst hse
            cases va with
            | bool b =>
              injection ho' with hok; injection hok with hv; subst hv
              refine ⟨evalExpr_scalar venv hst _ _ ?_, _, rfl, fun _ h => nomatch h⟩
              rw [evalScalar_select_bool venv (.var varg) (.constU64 1) (.constU64 0) b (evalScalar_var venv varg (.bool b) hA)]
              cases b <;> rfl
            | _ => injection ho' with herr; exact nomatch herr
      · simp only [hnot, hb2u, Bool.false_eq_true, ↓reduceIte] at hs ho
        let spec? : Option (LNIRType × Bool) :=
          if fn == ``UInt8.complement then some (.i8, false)
          else if fn == ``UInt16.complement then some (.i16, false)
          else if fn == ``UInt32.complement then some (.i32, false)
          else if fn == ``UInt64.complement then some (.i64, false)
          else if fn == ``USize.complement then some (.usize, false)
          else if fn == ``UInt8.neg then some (.i8, true)
          else if fn == ``UInt16.neg then some (.i16, true)
          else if fn == ``UInt32.neg then some (.i32, true)
          else if fn == ``UInt64.neg then some (.i64, true)
          else if fn == ``USize.neg then some (.usize, true)
          else none
        have hs' : (match spec? with
          | none => none
          | some (expectedTy, isNeg) =>
            if !(lnirTypeEq tyA expectedTy && lnirTypeEq retTy expectedTy) then none
            else match scalarWidthMask? expectedTy arch with
              | none => none
              | some mask =>
                let raw : ScalarExpr :=
                  if isNeg then .binOp .sub (.constU64 0) (.var varg) else .unaryOp .not (.var varg)
                some (.scalar (if mask == 0xFFFFFFFFFFFFFFFF then raw else .binOp .bitAnd raw (.constU64 mask)))) = some expr := hs
        cases hsp : spec? with
        | none => simp [hsp] at hs'
        | some pair =>
          rcases pair with ⟨opTy, isNeg⟩
          have ho' : (if !lnirTypeEq tyA opTy || !lnirTypeEq retTy opTy || !isSupportedStage1BScalarType opTy arch then none
            else
              some <| match va with
                | .u64 n =>
                  Except.ok (ofWord (masked arch opTy (if isNeg then 0#64 - n.toBitVec else ~~~n.toBitVec)))
                | _ =>
                  if isNeg then Except.error (UBError.typeError "evalBinOp: invalid operand types")
                  else Except.error (UBError.typeError "evalUnaryOp: invalid operand type")) = some (.ok v) := by
            dsimp only [spec?] at hsp; rw [hsp] at ho; exact ho
          simp only [hsp] at hs'
          cases htyEq : (lnirTypeEq tyA opTy && lnirTypeEq retTy opTy)
          · simp [htyEq] at hs'
          · rcases Bool.and_eq_true_iff.mp htyEq with ⟨hAop, hRop⟩
            simp only [hAop, hRop, Bool.true_and, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte] at hs' ho'
            cases hm : scalarWidthMask? opTy arch with
            | none => simp [hm] at hs'
            | some mask =>
              simp only [hm] at hs'; injection hs' with hse; subst hse
              cases hsup : isSupportedStage1BScalarType opTy arch
              · simp [hsup] at ho'
              · simp only [hsup, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ho'
                cases va with
                | u64 n =>
                  injection ho' with hok; injection hok with hv; subst hv
                  have hraw : evalScalarExpr venv (if isNeg then .binOp .sub (.constU64 0) (.var varg) else .unaryOp .not (.var varg)) =
                      .ok (.u64 (UInt64.ofBitVec (if isNeg then 0#64 - n.toBitVec else ~~~n.toBitVec))) := by
                    cases isNeg
                    · simp only [Bool.false_eq_true, ↓reduceIte]
                      rw [evalScalar_unaryOp venv .not _ (.u64 n) (evalScalar_var venv varg (.u64 n) hA)]; rfl
                    · simp only [↓reduceIte]
                      rw [evalScalar_binOp _ _ _ _ _ _ rfl (evalScalar_var venv varg (.u64 n) hA)]; rfl
                  have hnv : ∀ u, (if mask == 0xFFFFFFFFFFFFFFFF then
                      (if isNeg then ScalarExpr.binOp .sub (.constU64 0) (.var varg) else .unaryOp .not (.var varg))
                    else .binOp .bitAnd (if isNeg then .binOp .sub (.constU64 0) (.var varg) else .unaryOp .not (.var varg)) (.constU64 mask)) ≠ .var u := by
                    intro u; split
                    · cases isNeg <;> intro h <;> exact nomatch h
                    · intro h; exact nomatch h
                  exact ⟨evalExpr_scalar venv hst _ _ (evalMaskOut venv _ _ mask arch opTy hraw hm), _, rfl, hnv⟩
                | _ => injection ho' with herr; cases isNeg <;> exact nomatch herr

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
        cases hargL : lowerRealArgList ctx st true ((a0 :: as_).drop (if (a0 :: as_).length > numFields then (a0 :: as_).length - numFields else 0)) with
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
          cases hargL : lowerRealArgList ctx st true ((a0 :: as_).drop (if (a0 :: as_).length > spec.objSlots then (a0 :: as_).length - spec.objSlots else 0)) with
          | error _ => rw [hargL] at h_lower'; exact nomatch h_lower'
          | ok pair =>
            rcases pair with ⟨argVars, st1⟩
            rw [hargL] at h_lower'; dsimp only at h_lower'
            rcases lowerRealArgList_sound ctx st lenv venv true _ argVars st1 hinv hargL with
              ⟨vs, hevalArgs, hvarList, hlen, hst1_eq, hmap⟩
            rw [hst1_eq] at h_lower'
            have hemptyEq : argVars.isEmpty = ((a0 :: as_).drop (if (a0 :: as_).length > spec.objSlots then (a0 :: as_).length - spec.objSlots else 0)).isEmpty := by
              cases argVars <;> cases hd : (a0 :: as_).drop (if (a0 :: as_).length > spec.objSlots then (a0 :: as_).length - spec.objSlots else 0) <;>
                first | rfl | (rw [hd] at hlen; cases hlen)
            cases hcond : (!argVars.isEmpty && (argVars.map st.getVarType).all
                (fun t => isSupportedStage1BScalarOrTuple t ctx.arch || isHeapPtrType t))
            · rw [hcond] at h_lower'; simp only [Bool.false_eq_true, ↓reduceIte] at h_lower'
              have hcondF : (!(((a0 :: as_).drop (if (a0 :: as_).length > spec.objSlots then (a0 :: as_).length - spec.objSlots else 0)).isEmpty) &&
                  (((a0 :: as_).drop (if (a0 :: as_).length > spec.objSlots then (a0 :: as_).length - spec.objSlots else 0)).map
                    fun | .fvar x => (lenv.tys x).getD .objPtr | _ => .objPtr).all
                  (fun t => isSupportedStage1BScalarOrTuple t ctx.arch || isHeapPtrType t)) = false := by
                rw [← hemptyEq, ← hmap]; exact hcond
              have hheapNone : heapSpec? = none := by
                dsimp only [heapSpec?]
                simp only [hst1d, hlay, hsc, Bool.true_and, ↓reduceIte]
                rw [hcondF]; rfl
              rcases htuple hheapNone h_lower' with ⟨he, hst_eq, hdisj⟩
              exact ⟨he, hst_eq, hnoneA, fun _ => hdisj⟩
            · rw [hcond] at h_lower'; simp only [↓reduceIte] at h_lower'
              injection h_lower' with hp; rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
              have hcondT : (!(((a0 :: as_).drop (if (a0 :: as_).length > spec.objSlots then (a0 :: as_).length - spec.objSlots else 0)).isEmpty) &&
                  (((a0 :: as_).drop (if (a0 :: as_).length > spec.objSlots then (a0 :: as_).length - spec.objSlots else 0)).map
                    fun | .fvar x => (lenv.tys x).getD .objPtr | _ => .objPtr).all
                  (fun t => isSupportedStage1BScalarOrTuple t ctx.arch || isHeapPtrType t)) = true := by
                rw [← hemptyEq, ← hmap]; exact hcond
              have hheapSome : heapSpec? = some spec := by
                dsimp only [heapSpec?]
                simp only [hst1d, hlay, hsc, Bool.true_and, ↓reduceIte]
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
                    | ok vals => rw [hvr] at hvarList; injection hvarList with hvs; subst hvs; rfl
              rw [hvsNe] at h_eval'; simp only [Bool.false_eq_true, ↓reduceIte] at h_eval'
              cases hwf : (!vs.all Val.wfField)
              · simp only [hwf, Bool.false_eq_true, ↓reduceIte] at h_eval'
                injection h_eval' with hp2; rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, rfl⟩
                refine ⟨?_, rfl, hnoneA, fun _ => Or.inl ⟨argVars, rfl, rfl⟩⟩
                simp only [evalExpr, hvarList, evalVarList, hvsNe, Bool.false_and, hwf, Bool.false_eq_true, ↓reduceIte]
              · simp [hwf] at h_eval'

end LeanNative.Proofs
