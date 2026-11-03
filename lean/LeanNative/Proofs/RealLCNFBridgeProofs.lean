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

/-- `lowerCanonicalIntrinsicPure?` agrees with `.fap` evaluation on all binary, boolean, unary, and cast intrinsics. -/
theorem lowerCanonicalIntrinsicPure_sound (ctx : RealBridgeCtx) (st : RealBridgeState) (lenv : LEnv)
    (venv : VarEnv) (hst hst' : HeapState) (fn : Lean.Name)
    (args : Array (Lean.Compiler.LCNF.Arg .impure)) (himp : Lean.Compiler.LCNF.Purity.impure = .impure)
    (argVars : List VarId) (st1 : RealBridgeState)
    (retTy : LNIRType) (expr : LNIRExpr) (v : Val) (ctor? : Option Lean.Name)
    (hinv : BridgeStateInv st lenv venv)
    (hargL : lowerRealArgList ctx st false args.toList = .ok (argVars, st1))
    (hs : lowerCanonicalIntrinsicPure? fn argVars retTy (argVars.map st1.getVarType) false ctx.arch = some expr)
    (ho : evalLetValue ctx lenv hst (.fap fn args himp) retTy = .ok (v, hst', ctor?)) :
    evalExpr venv hst expr = .ok (v, hst') ∧ st1 = st ∧ hst' = hst ∧ ctor? = none ∧
      (∃ se, expr = .scalar se ∧ ∀ u, se ≠ .var u) := by
  rcases lowerRealArgList_sound ctx st lenv venv false args.toList argVars st1 hinv hargL with
    ⟨vs, hevalArgs, hvarList, hlen, rfl, hmap⟩
  unfold lowerCanonicalIntrinsicPure? at hs
  simp only [Bool.false_eq_true, ↓reduceIte] at hs
  dsimp only [evalLetValue] at ho
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
                          cases hbin : lookupCanonicalTypedBinOp? fn with
                          | some pairOp =>
                            rcases pairOp with ⟨opTy, op⟩
                            rw [hbin] at hs ho; dsimp only at hs ho
                            cases hteq : (lnirTypeEq ((lenv.tys xA).getD .objPtr) opTy && lnirTypeEq ((lenv.tys xB).getD .objPtr) opTy)
                            · rw [hteq] at ho; exact nomatch ho
                            · rw [hteq] at ho; simp only [↓reduceIte] at ho
                              have hlistEq : lnirTypeListEq [(lenv.tys xA).getD .objPtr, (lenv.tys xB).getD .objPtr] [opTy, opTy] = true := by
                                dsimp [lnirTypeListEq]; simp [hteq]
                              rw [hlistEq] at hs; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Functor.map, Option.map] at hs
                              cases hse : lowerScalarIntrinsicExpr? op vl vr opTy retTy ctx.arch with
                              | none => rw [hse] at hs; exact nomatch hs
                              | some se =>
                                rw [hse] at hs; injection hs with hseEq; subst hseEq
                                cases hwb : wordBin ctx.arch op opTy retTy va' vb' with
                                | error _ => rw [hwb] at ho; exact nomatch ho
                                | ok v0 =>
                                  rw [hwb] at ho; dsimp only [Functor.map, Except.map] at ho
                                  injection ho with hp2; rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, rfl⟩
                                  rcases lowerScalarIntrinsicExpr_sound venv ctx.arch op opTy retTy vl vr va' vb' se v0 hvL hvR hse hwb with ⟨hevalS, hnv⟩
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
                                injection ho with hp2; rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩; rcases Prod.mk.inj hp3 with ⟨rfl, rfl⟩
                                rcases lowerBoolBinIntrinsic_sound venv hst fn vl vr _ _ retTy va' vb' expr v0 hvL hvR hs hbb with ⟨he, hse⟩
                                exact ⟨he, rfl, rfl, rfl, hse⟩

private theorem lookupBoundFVar_inv (st : RealBridgeState) (lenv : LEnv) (venv : VarEnv)
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

private theorem unboxed_not_heap (vt : LNIRType) (h : isUnboxedScalarOrTuple vt = true) :
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
        dsimp [LEnv.isTupleVar]; rw [htyL]; cases st.getVarType vid <;> rfl
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
        dsimp [LEnv.isTupleVar]; rw [htyL]; cases st.getVarType vid <;> rfl
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
        dsimp [LEnv.isTupleVar]; rw [htyL]; cases st.getVarType vid <;> rfl
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
        rcases lowerCanonicalIntrinsicPure_sound ctx st lenv venv hst hst' fn args h argVars stA rawTy e0 v ctor? hinv hargL hintr h_eval with
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

private theorem evalCode_fuel_mono_step (f : Nat) : ∀ (c : LNIRCode) (venv : VarEnv) (hst : HeapState) (v : Val) (hst' : HeapState),
    evalCode f venv hst c = .ok (v, hst') → evalCode (f + 1) venv hst c = .ok (v, hst')
  | .letBind dst _ val k, venv, hst, v, hst', h => by
    dsimp only [evalCode] at h ⊢
    cases he : evalExpr venv hst val with
    | error _ => rw [he] at h; exact nomatch h
    | ok p => rw [he] at h; exact evalCode_fuel_mono_step f k (venv.bind dst p.1) p.2 v hst' h
  | .rawStore pv iv vv _ k, venv, hst, v, hst', h => by
    dsimp only [evalCode] at h ⊢
    cases hp : venv pv <;> cases hi : venv iv <;> cases hv : venv vv <;> simp only [hp, hi, hv] at h <;> try contradiction
    rename_i vp vi vv0
    cases vp <;> cases vi <;> cases vv0 <;> simp only at h ⊢ <;> try contradiction
    all_goals (
      rename_i bufId idx val
      cases hw : hst.writeElemExclusive bufId idx.toNat val <;> simp only [hw] at h ⊢
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
    cases hlo : venv loVar <;> cases hhi : venv hiVar <;> cases hain : venv accInit <;> simp only [hlo, hhi, hain] at h <;> try contradiction
    rename_i vlo vhi initVal
    cases vlo <;> cases vhi <;> simp only at h ⊢ <;> try contradiction
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
  | .parFor outVar lenVar inputs _ kernel k, venv, hst, v, hst', h => by
    dsimp only [evalCode] at h ⊢
    have hpf : ∀ r, evalParFor f venv hst lenVar inputs kernel = .ok r →
        evalParFor (f + 1) venv hst lenVar inputs kernel = .ok r := by
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
    cases hp : evalParFor f venv hst lenVar inputs kernel with
    | error _ => rw [hp] at h; exact nomatch h
    | ok pr =>
      rw [hp] at h; rw [hpf pr hp]
      exact evalCode_fuel_mono_step f k (venv.bind outVar pr.1) pr.2 v hst' h
  | .ret _, _, _, _, _, h => h
  | .unreachable, _, _, _, _, h => h

private theorem bridgeInv_ext (st st' : RealBridgeState) (lenv : LEnv) (venv : VarEnv)
    (hinv : BridgeStateInv st lenv venv)
    (hnext : st.nextVarId ≤ st'.nextVarId)
    (hty : ∀ u, u < st.nextVarId → st'.getVarType u = st.getVarType u)
    (hlu : st'.fvarMap = st.fvarMap)
    (hctor : ∀ u, u < st.nextVarId → st'.getActiveCtor? u = st.getActiveCtor? u)
    (hjp : st'.jpDecls = st.jpDecls) :
    BridgeStateInv st' lenv venv := by
  have hluf : ∀ x, st'.lookupFVar? x = st.lookupFVar? x := fun x => by simp [RealBridgeState.lookupFVar?, hlu]
  have hjpf : ∀ j, st'.lookupJp? j = st.lookupJp? j := fun j => by simp [RealBridgeState.lookupJp?, hjp]
  refine ⟨fun x vid hx => ?_, fun x vid hx => ?_, fun x vid hx => ?_, fun x vid hx => ?_, fun x1 x2 vid hx1 hx2 => ?_, fun j ps body hj => ?_⟩
  · rw [hluf] at hx; exact Nat.lt_of_lt_of_le (hinv.fvar_lt x vid hx) hnext
  · rw [hluf] at hx; exact hinv.fvar_val x vid hx
  · rw [hluf] at hx; rw [hinv.fvar_ty x vid hx, hty vid (hinv.fvar_lt x vid hx)]
  · rw [hluf] at hx; rw [hinv.fvar_ctor x vid hx, hctor vid (hinv.fvar_lt x vid hx)]
  · rw [hluf] at hx1 hx2; exact hinv.fvar_inj x1 x2 vid hx1 hx2
  · rw [hjpf] at hj; exact hinv.jp_sync j ps body hj

private theorem lowerRealArg_st_eq (ctx : RealBridgeCtx) (st st1 : RealBridgeState)
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

private theorem lowerRealArgList_st_eq (ctx : RealBridgeCtx) (allowObj : Bool) :
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
        | none => Except.error s!"[lean-native] Unsupported payload-carrying constructor `{ctorName}` in Stage 1B") = Except.ok (e, s) → s = st := by
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

private theorem lowerImpureLetValuePure_st_eq (ctx : RealBridgeCtx) (st st1 : RealBridgeState)
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
    cases hl : lowerRealArgList ctx st false args.toList with
    | error _ => rw [hl] at h; exact nomatch h
    | ok p =>
      rw [hl] at h; dsimp only at h
      cases hi : lowerCanonicalIntrinsicPure? fn p.1 retTy (p.1.map p.2.getVarType) false ctx.arch <;> rw [hi] at h
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
        · cases hc : st.getActiveCtor? vid with
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
        · cases hc : st.getActiveCtor? vid with
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
      cases hok : (isUnboxedScalarOrTuple (st.getVarType vid) || isHeapPtrType (st.getVarType vid)) <;> simp only [hok, ↓reduceIte, Bool.false_eq_true] at h
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

private theorem nat_beq_false {a b : Nat} (h : a ≠ b) : (a == b) = false :=
  beq_eq_false_iff_ne.mpr h

private theorem lookupFVar_allocFresh (st : RealBridgeState) (x y : Lean.FVarId) (ty : LNIRType) :
    (st.allocFreshFVar x ty).2.lookupFVar? y = if y == x then some st.nextVarId else st.lookupFVar? y := by
  unfold RealBridgeState.allocFreshFVar; exact lookupFVar_cons st.fvarMap x y st.nextVarId

private theorem getVarType_allocFresh (st : RealBridgeState) (x : Lean.FVarId) (ty : LNIRType) (u : VarId) :
    (st.allocFreshFVar x ty).2.getVarType u = if u == st.nextVarId then ty else st.getVarType u := by
  unfold RealBridgeState.allocFreshFVar; exact getVarType_setVarType st st.nextVarId u ty

private theorem getActiveCtor_allocFresh (st : RealBridgeState) (x : Lean.FVarId) (ty : LNIRType) (u : VarId) :
    (st.allocFreshFVar x ty).2.getActiveCtor? u = if u == st.nextVarId then none else st.getActiveCtor? u := by
  by_cases h : u = st.nextVarId
  · subst h
    unfold RealBridgeState.allocFreshFVar RealBridgeState.getActiveCtor?
    have hnone : ∀ (l : List (VarId × Lean.Name)) (w : VarId), (l.filter (fun (v, _) => v != w)).find? (fun (v, _) => v == w) = none := by
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

private theorem freshVar_spec (st : RealBridgeState) (ty : LNIRType) :
    (st.freshVar ty).1 = st.nextVarId ∧ (st.freshVar ty).2.nextVarId = st.nextVarId + 1 ∧
    (∀ u, (st.freshVar ty).2.getVarType u = if u == st.nextVarId then ty else st.getVarType u) ∧
    (∀ y, (st.freshVar ty).2.lookupFVar? y = st.lookupFVar? y) ∧
    (∀ u, (st.freshVar ty).2.getActiveCtor? u = st.getActiveCtor? u) ∧
    (∀ j, (st.freshVar ty).2.lookupJp? j = st.lookupJp? j) := by
  unfold RealBridgeState.freshVar
  exact ⟨rfl, rfl, fun u => getVarType_setVarType st st.nextVarId u ty, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

private theorem venv_bind_fresh (venv : VarEnv) (base : VarId) (u : VarId) (hu : u < base) (v : Val) :
    (venv.bind base v) u = venv u :=
  VarEnv.bind_ne venv base u v (nat_beq_false (Nat.ne_of_lt hu))

private theorem bridgeInv_bind_fresh (st : RealBridgeState) (lenv : LEnv) (venv : VarEnv)
    (x : Lean.FVarId) (ty : LNIRType) (val : Val)
    (hinv : BridgeStateInv st lenv venv) :
    BridgeStateInv (st.allocFreshFVar x ty).2
      (lenv.bind x val none (some ty)) (venv.bind st.nextVarId val) := by
  refine ⟨fun y vid hy => ?_, fun y vid hy => ?_, fun y vid hy => ?_, fun y vid hy => ?_, fun y1 y2 vid hy1 hy2 => ?_, fun j ps body hj => ?_⟩
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

private theorem bridgeInv_setActiveCtor (st : RealBridgeState) (lenv : LEnv) (venv : VarEnv)
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
  · rw [beq_iff_eq.mp hyx] at hy'; rw [hx] at hy'; injection hy' with hvidEq; rw [← hvidEq]
    simp only [LEnv.withCtor, hyx, getActiveCtor_setActiveCtor, beq_self_eq_true, ↓reduceIte]

private theorem bridgeInv_setJp (st : RealBridgeState) (lenv : LEnv) (venv : VarEnv)
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

private theorem bindJpCallArgsPure_mono (ctx : RealBridgeCtx) :
    ∀ (ps : List (Lean.Compiler.LCNF.Param .impure)) (as_ : List (Lean.Compiler.LCNF.Arg .impure))
      (st st1 : RealBridgeState) (binds : List (Lean.FVarId × VarId × LNIRType × VarId)),
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
    dsimp only [bindJpCallArgsPure, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases ha : lowerRealArg ctx st a true with
    | error _ => rw [ha] at h; exact nomatch h
    | ok pa =>
      rw [ha] at h; rcases pa with ⟨argVid, stA⟩
      have hstA := lowerRealArg_st_eq ctx st stA a true argVid ha; subst stA
      dsimp only at h
      let pTy := lowerGroundImpureType p.type
      rcases freshVar_spec st pTy with ⟨hfv1, hfvNext, hfvTy, _, _, _⟩
      cases hr : bindJpCallArgsPure ctx (st.freshVar pTy).2 ps as_ with
      | error _ => rw [hr] at h; exact nomatch h
      | ok pr =>
        rw [hr] at h; dsimp only at h; injection h with hp
        rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
        rcases bindJpCallArgsPure_mono ctx ps as_ (st.freshVar pTy).2 pr.2 pr.1 hr with ⟨hnextR, htyR, hmemR⟩
        have hbaseSt : st.nextVarId ≤ (st.freshVar pTy).2.nextVarId := by rw [hfvNext]; exact Nat.le_succ _
        refine ⟨Nat.le_trans hbaseSt hnextR, fun u hu => ?_, fun b hb => ?_⟩
        · rw [htyR u (Nat.lt_of_lt_of_le hu hbaseSt), hfvTy u, nat_beq_false (Nat.ne_of_lt hu)]; rfl
        · cases List.mem_cons.mp hb with
          | inl hhead => subst hhead; dsimp only; rw [hfv1]; exact ⟨Nat.le_refl _, Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hnextR⟩
          | inr htail =>
            rcases hmemR b htail with ⟨hlo, hhi⟩
            exact ⟨Nat.le_trans (Nat.le_succ _) hlo, hhi⟩

private theorem applyJpParamMapPure_mono (base : VarId) :
    ∀ (binds : List (Lean.FVarId × VarId × LNIRType × VarId)) (st : RealBridgeState),
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
            | error _ => change (match lowerImpureStepPure fuel ctx stIn (.inl c) with | Except.ok (c0, stOut) => Except.ok (c0, { stOut with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }) | Except.error e => Except.error e) = Except.ok (code, st') at h; rw [hc] at h; exact nomatch h
            | ok pr =>
              change (match lowerImpureStepPure fuel ctx stIn (.inl c) with | Except.ok (c0, stOut) => Except.ok (c0, { stOut with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }) | Except.error e => Except.error e) = Except.ok (code, st') at h
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
              ((stM.freshVar .i1).2.nextVarId ≤ st'.nextVarId ∧ ∀ u, u < (stM.freshVar .i1).2.nextVarId → st'.getVarType u = (stM.freshVar .i1).2.getVarType u) →
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
          cases hhp : (!(ctx.allowStage1DHeap && isHeapPtrType (st.getVarType vid))) <;> simp only [hhp, ↓reduceIte, Bool.false_eq_true] at h
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
            cases hk : lowerImpureStepPure fuel ctx (st.freshVar .i64).2 (.inr ((st.freshVar .i64).1, false, 0, some cs.discr, orderAltsPure cs.alts.toList)) with
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

private theorem getActiveCtor_clear (st : RealBridgeState) (vid w : VarId) :
    RealBridgeState.getActiveCtor? { activeCtor := st.activeCtor.filter (fun (v, _) => v != vid) } w =
      if w == vid then none else st.getActiveCtor? w := by
  by_cases h : w = vid
  · subst h
    unfold RealBridgeState.getActiveCtor?
    have hnone : ∀ (l : List (VarId × Lean.Name)) (q : VarId), (l.filter (fun (v, _) => v != q)).find? (fun (v, _) => v == q) = none := by
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
    · simp only [↓reduceIte] at hy; injection hy with hvid; rw [← hvid]; exact hfreshLt
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

private theorem bindJpCallArgsPure_rel (ctx : RealBridgeCtx) (venv0 : VarEnv) (base : VarId)
    (ps : List (Lean.Compiler.LCNF.Param .impure)) (as_ : List (Lean.Compiler.LCNF.Arg .impure))
    (st0 st1 : RealBridgeState) (lenv : LEnv)
    (binds : List (Lean.FVarId × VarId × LNIRType × VarId))
    (hbase : base ≤ st0.nextVarId)
    (hfvarBase : ∀ y vid, st0.lookupFVar? y = some vid → vid < base)
    (hinv : BridgeStateInv st0 lenv venv0)
    (h : bindJpCallArgsPure ctx st0 ps as_ = .ok (binds, st1)) :
    ∃ vs, evalArgs lenv.vals as_ = .ok vs ∧
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
          bindParams lenv_m ps vs = .ok lenv' ∧
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
      dsimp only [bindJpCallArgsPure, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      cases ha : lowerRealArg ctx st0 a true with
      | error _ => rw [ha] at h; exact nomatch h
      | ok pa =>
        rw [ha] at h; rcases pa with ⟨argVid, stA⟩
        rcases lowerRealArg_sound ctx st0 lenv venv0 a true argVid stA hinv ha with
          ⟨x, v, rfl, hluX, hevalA, hvArg, _, hstA⟩
        subst stA; dsimp only at h
        let pTy := lowerGroundImpureType p.type
        rcases freshVar_spec st0 pTy with ⟨hfv1, hfvNext, hfvTy, hfvLu, hfvCtor, _⟩
        let st2 := (st0.freshVar pTy).2
        have hbase2 : base ≤ st2.nextVarId := Nat.le_trans hbase (by rw [hfvNext]; exact Nat.le_succ _)
        have hfvarBase2 : ∀ y vid, st2.lookupFVar? y = some vid → vid < base := by
          intro y vid hy; rw [hfvLu] at hy; exact hfvarBase y vid hy
        have hinv2 : BridgeStateInv st2 lenv venv0 :=
          bridgeInv_ext st0 st2 lenv venv0 hinv (by rw [hfvNext]; exact Nat.le_succ _)
            (fun u hu => by rw [hfvTy u, nat_beq_false (Nat.ne_of_lt hu)]; rfl) rfl (fun u _ => hfvCtor u) rfl
        cases hr : bindJpCallArgsPure ctx st2 ps as_ with
        | error _ => rw [hr] at h; exact nomatch h
        | ok pr =>
          rw [hr] at h; dsimp only at h; injection h with hp; rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
          rcases ih as_ st2 pr.2 pr.1 hbase2 hfvarBase2 hinv2 hr with
            ⟨vs, hevalRest, hfm, hac, hjp, hnextR, htyR, hstepRest⟩
          refine ⟨v :: vs, by simp [evalArgs, hevalA, hevalRest], hfm, hac, hjp,
            Nat.le_trans (by rw [hfvNext]; exact Nat.le_succ _) hnextR,
            fun u hu => by
              rw [htyR u (by rw [hfvNext]; exact Nat.lt_succ_of_lt hu), hfvTy u, nat_beq_false (Nat.ne_of_lt hu)]
              rfl,
            ?_⟩
          intro st_m lenv_m venv_m cur fuel hst body hinv_m hcurGe hcurLe hstmNext hstmLt hvenvBase
          have hargLtBase : argVid < base := hfvarBase x argVid hluX
          have hvArg_m : venv_m argVid = some v := (hvenvBase argVid hargLtBase).trans hvArg
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
          have hcur1Ge : base ≤ st2.nextVarId := hbase2
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
          refine ⟨lenv', venv', hbindRest, hinvFinal, ?_⟩
          dsimp only [wrapJpCallBindsPure, evalCode, evalExpr, evalScalarExpr]
          rw [hvArg_m]; exact hevalWrap

private theorem bridgeInv_venv_agree (st : RealBridgeState) (lenv : LEnv) (venv venv' : VarEnv)
    (hinv : BridgeStateInv st lenv venv) (hagree : ∀ u, u < st.nextVarId → venv' u = venv u) :
    BridgeStateInv st lenv venv' := by
  refine ⟨hinv.fvar_lt, fun x vid hx => ?_, hinv.fvar_ty, hinv.fvar_ctor, hinv.fvar_inj, hinv.jp_sync⟩
  rw [hagree vid (hinv.fvar_lt x vid hx)]; exact hinv.fvar_val x vid hx

private theorem bridgeInv_freshVar (st : RealBridgeState) (lenv : LEnv) (venv : VarEnv)
    (ty : LNIRType) (val : Val) (hinv : BridgeStateInv st lenv venv) :
    BridgeStateInv (st.freshVar ty).2 lenv (venv.bind (st.freshVar ty).1 val) := by
  rcases freshVar_spec st ty with ⟨hfv1, hfvNext, hfvTy, _, hfvCtor, _⟩
  rw [hfv1]
  exact bridgeInv_ext st (st.freshVar ty).2 lenv (venv.bind st.nextVarId val)
    (bridgeInv_venv_agree st lenv venv (venv.bind st.nextVarId val) hinv
      (fun u hu => venv_bind_fresh venv st.nextVarId u hu val))
    (by rw [hfvNext]; exact Nat.le_succ _)
    (fun u hu => by rw [hfvTy u, nat_beq_false (Nat.ne_of_lt hu)]; rfl) rfl (fun u _ => hfvCtor u) rfl

private theorem varEnv_bind_comm (venv : VarEnv) (a b : VarId) (va vb : Val) (hne : a ≠ b) :
    (venv.bind a va).bind b vb = (venv.bind b vb).bind a va := by
  funext u
  dsimp only [VarEnv.bind]
  cases hub : (u == b)
  · cases hua : (u == a) <;> rfl
  · have hb : u = b := beq_iff_eq.mp hub; subst hb
    rw [nat_beq_false hne.symm]; rfl

private theorem lenv_bind_withCtor (lenv : LEnv) (x : Lean.FVarId) (val : Val)
    (c : Lean.Name) (ty : LNIRType) :
    (lenv.bind x val none (some ty)).withCtor x c = lenv.bind x val (some c) (some ty) := by
  cases lenv; dsimp only [LEnv.bind, LEnv.withCtor]; congr 1; funext y; cases y == x <;> rfl

private theorem lowerRefOpPure_sound (fuel : Nat) (isInc : Bool) (vid : VarId) (vt : LNIRType)
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
        | _ => dsimp only at hrc ⊢; injection hrc with hs; subst hst1; exact hk
      · injection hrop with hc; subst code'
        change (match hst.evalIncRef venv vid n with
          | .ok st' => evalCode fuel venv st' kCode
          | .error err => .error err) = .ok (v, hst')
        unfold HeapState.evalIncRef; rw [hvalV]
        cases val with
        | objPtr objId => simp only [↓reduceIte] at hrc ⊢; rw [hrc]; exact hk
        | sarrayId bufId => simp only [↓reduceIte] at hrc ⊢; rw [hrc]; exact hk
        | _ => dsimp only at hrc ⊢; injection hrc with hs; subst hst1; exact hk
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
  | bool b0 => injection hb with heq; subst b0; cases b <;> rfl
  | u64 n => injection hb with heq; subst b; rfl
  | u256 w => injection hb with heq; subst b; rfl
  | _ => exact nomatch hb

private theorem bridgeInv_empty : BridgeStateInv {} LEnv.empty VarEnv.empty where
  fvar_lt _ _ h := nomatch h
  fvar_val _ _ h := nomatch h
  fvar_ty _ _ h := nomatch h
  fvar_ctor _ _ h := nomatch h
  fvar_inj _ _ _ h _ := nomatch h
  jp_sync _ _ _ h := nomatch h

private theorem internRealParams_sound (ps : List (Lean.Compiler.LCNF.Param .impure)) :
    ∀ (args : List Val) (st : RealBridgeState) (lenv lenv' : LEnv) (venv : VarEnv),
      BridgeStateInv st lenv venv →
      bindParams lenv ps args = .ok lenv' →
      BridgeStateInv (internRealParams st ps).2 lenv'
        (((internRealParams st ps).1.zip args).foldl (fun acc (p, val) => acc.bind p.id val) venv) := by
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
      dsimp only [bindParams] at hbind
      exact ih as_ (st.allocFreshFVar p.fvarId (lowerGroundImpureType p.type)).2
        (lenv.bind p.fvarId a none (some (lowerGroundImpureType p.type))) lenv'
        (venv.bind st.nextVarId a)
        (bridgeInv_bind_fresh st lenv venv p.fvarId (lowerGroundImpureType p.type) a hinv) hbind

private theorem discr_env_inv (st : RealBridgeState) (lenv : LEnv) (venv : VarEnv)
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

private theorem tag_branch_sound (fuel : Nat) (ctx : RealBridgeCtx) (lenv envIn : LEnv)
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

private theorem lowerImpureStepPure_sound_aux (fuel : Nat) (ctx : RealBridgeCtx) :
    ∀ (st st' : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
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
      evalCode fuel venv hst code = .ok (v, hst') := by
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ _ h; exact nomatch h
  | succ fuel ih =>
    intro st st' lenv venv hst hst' v target code hinv h_lower h_side
    dsimp only [lowerImpureStepPure] at h_lower
    cases target with
    | inr t =>
      rcases t with ⟨condVar, isBool, idx, discr?, alts⟩
      rcases h_side with ⟨hcondLt, hdiscr, hi1, cond, hcondV, h_eval⟩
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
    | inl c =>
      have h_eval : evalStep (fuel + 1) ctx lenv hst (.inl c) = .ok (v, hst') := h_side
      cases c with
      | «return» x =>
        dsimp only [evalStep] at h_eval
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
        cases hv : st.lookupBoundFVar x <;> rw [hv] at h_lower
        · exact nomatch h_lower
        · rename_i vid; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
          rcases lookupBoundFVar_inv st lenv venv x vid hinv hv with ⟨_, _, ⟨val, hvalL, hvalV⟩, _, _⟩
          rw [hvalL] at h_eval; injection h_eval with hpv; rcases Prod.mk.inj hpv with ⟨rfl, rfl⟩
          dsimp only [evalCode]; rw [hvalV]
      | unreach _ => dsimp only [evalStep] at h_eval; exact nomatch h_eval
      | «fun» _ _ _ => dsimp only [evalStep] at h_eval; exact nomatch h_eval
      | «let» decl k =>
        dsimp only [evalStep] at h_eval
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
        cases hl : lowerImpureLetValuePure ctx st decl.value (lowerGroundImpureType decl.type) with
        | error _ => rw [hl] at h_lower; exact nomatch h_lower
        | ok pl =>
          rw [hl] at h_lower; rcases pl with ⟨rhs, st1⟩
          cases hev : evalLetValue ctx lenv hst decl.value (lowerGroundImpureType decl.type) with
          | error _ => rw [hev] at h_eval; exact nomatch h_eval
          | ok pev =>
            rw [hev] at h_eval; rcases pev with ⟨val, hst1, ctor?⟩; dsimp only at h_eval h_lower
            have hst1Eq := lowerImpureLetValuePure_st_eq ctx st st1 decl.value (lowerGroundImpureType decl.type) rhs hl
            subst st1
            rcases lowerImpureLetValuePure_sound ctx st lenv venv hst hst1 decl.value (lowerGroundImpureType decl.type) rhs st val ctor?
                hinv hl hev with ⟨_, hrhsEval, htyEq, hctorEq⟩
            let ty := inferImpureRhsTypePure st rhs (lowerGroundImpureType decl.type)
              (match decl.value with | .box _ _ _ => true | _ => false)
            have hEvalK : evalStep fuel ctx
                (lenv.bind decl.fvarId val
                  (match decl.value with | .ctor _ _ _ => if lnirTypeEq ty .objPtr then ctor? else none | _ => none)
                  (some ty))
                hst1 (.inl k) = .ok (v, hst') := by
              dsimp only [ty]
              simp only [htyEq]
              exact h_eval
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
                  rw [hexclId, varEnv_bind_comm venv st2'.nextVarId dst (.bool b) (.bool (!b)) hne]
                  rw [← hexclId]
                  exact bridgeInv_freshVar st2' _ (venv.bind dst (.bool (!b))) .i1 (.bool b) hinv2'
                have hkEval := evalCode_fuel_mono_step fuel pk.1 _ hst1 v hst'
                  (ih (st2'.freshVar .i1).2 pk.2 _ _ hst1 hst' v (.inl k) pk.1 hinv3 hkClean hEvalK)
                have hcodeClean : code = .letBind (st2'.freshVar .i1).1 .i1 (.isExclusive objVar)
                    (.letBind dst .i1 (.scalar (.unaryOp .not (.var (st2'.freshVar .i1).1))) pk.1) := hcodeEq.symm
                rw [hcodeClean]
                dsimp only [evalCode]
                rw [hexclEval]
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
                rw [← hcodeEq]; dsimp only [evalCode]; rw [hrhsEval]; exact hkEval
      | inc x n _ _ k _ =>
        dsimp only [evalStep] at h_eval
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
        cases hv : st.lookupBoundFVar x <;> rw [hv] at h_lower
        · exact nomatch h_lower
        · rename_i vid; dsimp only at h_lower
          rcases lookupBoundFVar_inv st lenv venv x vid hinv hv with ⟨_, _, ⟨val, hvalL, hvalV⟩, htyL, _⟩
          cases hrc : applyRc true lenv hst x n with
          | error _ => rw [hrc] at h_eval; exact nomatch h_eval
          | ok hst1 =>
            rw [hrc] at h_eval
            cases hk : lowerImpureStepPure fuel ctx st (.inl k) with
            | error _ => rw [hk] at h_lower; exact nomatch h_lower
            | ok pk =>
              rw [hk] at h_lower; dsimp only at h_lower
              cases hrop : lowerRefOpPure true vid (st.getVarType vid) n pk.1 <;> rw [hrop] at h_lower
              · exact nomatch h_lower
              · injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                exact lowerRefOpPure_sound (fuel + 1) true vid (st.getVarType vid) n pk.1 _ lenv venv hst hst1 hst'
                  x val v htyL hvalL hvalV hrop hrc
                  (evalCode_fuel_mono_step fuel pk.1 venv hst1 v hst' (ih st pk.2 lenv venv hst1 hst' v (.inl k) pk.1 hinv hk h_eval))
      | dec x n _ _ _ k _ =>
        dsimp only [evalStep] at h_eval
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
        cases hv : st.lookupBoundFVar x <;> rw [hv] at h_lower
        · exact nomatch h_lower
        · rename_i vid; dsimp only at h_lower
          rcases lookupBoundFVar_inv st lenv venv x vid hinv hv with ⟨_, _, ⟨val, hvalL, hvalV⟩, htyL, _⟩
          cases hrc : applyRc false lenv hst x n with
          | error _ => rw [hrc] at h_eval; exact nomatch h_eval
          | ok hst1 =>
            rw [hrc] at h_eval
            cases hk : lowerImpureStepPure fuel ctx st (.inl k) with
            | error _ => rw [hk] at h_lower; exact nomatch h_lower
            | ok pk =>
              rw [hk] at h_lower; dsimp only at h_lower
              cases hrop : lowerRefOpPure false vid (st.getVarType vid) n pk.1 <;> rw [hrop] at h_lower
              · exact nomatch h_lower
              · injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                exact lowerRefOpPure_sound (fuel + 1) false vid (st.getVarType vid) n pk.1 _ lenv venv hst hst1 hst'
                  x val v htyL hvalL hvalV hrop hrc
                  (evalCode_fuel_mono_step fuel pk.1 venv hst1 v hst' (ih st pk.2 lenv venv hst1 hst' v (.inl k) pk.1 hinv hk h_eval))
      | del x k _ =>
        dsimp only [evalStep] at h_eval
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
        cases hv : st.lookupBoundFVar x <;> rw [hv] at h_lower
        · exact nomatch h_lower
        · rename_i objVid; dsimp only at h_lower
          rcases lookupBoundFVar_inv st lenv venv x objVid hinv hv with ⟨_, _, ⟨val, hvalL, hvalV⟩, htyL, _⟩
          have hisHeap : lenv.isHeapVar x = isHeapPtrType (st.getVarType objVid) := by
            dsimp only [LEnv.isHeapVar]; rw [htyL]
          rw [hvalL, hisHeap] at h_eval
          cases hhp : (ctx.allowStage1DHeap && isHeapPtrType (st.getVarType objVid)) <;>
            simp only [hhp, ↓reduceIte, Bool.false_eq_true] at h_lower h_eval
          · cases hk : lowerImpureStepPure fuel ctx st (.inl k) with
            | error _ => rw [hk] at h_lower; exact nomatch h_lower
            | ok pk =>
              rw [hk] at h_lower; dsimp only at h_lower
              cases hrop : lowerRefOpPure false objVid (st.getVarType objVid) 1 pk.1 <;> rw [hrop] at h_lower
              · exact nomatch h_lower
              · injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                have hrcEq : ∃ hst1, applyRc false lenv hst x 1 = .ok hst1 ∧
                    evalStep fuel ctx lenv hst1 (.inl k) = .ok (v, hst') := by
                  unfold applyRc; rw [hisHeap, hvalL]
                  cases hih : isHeapPtrType (st.getVarType objVid) <;>
                    simp only [hih, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] at h_eval ⊢
                  · cases val <;> exact ⟨hst, rfl, h_eval⟩
                  · cases val with
                    | objPtr objId =>
                      dsimp only at h_eval ⊢
                      cases hd : hst.decRefObj objId 1 with
                      | error _ => rw [hd] at h_eval; exact nomatch h_eval
                      | ok hst1 => rw [hd] at h_eval; exact ⟨hst1, rfl, h_eval⟩
                    | sarrayId bufId =>
                      dsimp only at h_eval ⊢
                      cases hd : hst.decRefBuf bufId 1 with
                      | error _ => rw [hd] at h_eval; exact nomatch h_eval
                      | ok hst1 => rw [hd] at h_eval; exact ⟨hst1, rfl, h_eval⟩
                    | _ => exact ⟨hst, rfl, h_eval⟩
                rcases hrcEq with ⟨hst1, hrc, h_eval1⟩
                exact lowerRefOpPure_sound (fuel + 1) false objVid (st.getVarType objVid) 1 pk.1 _ lenv venv hst hst1 hst'
                  x val v htyL hvalL hvalV hrop hrc
                  (evalCode_fuel_mono_step fuel pk.1 venv hst1 v hst' (ih st pk.2 lenv venv hst1 hst' v (.inl k) pk.1 hinv hk h_eval1))
          · cases val with
            | objPtr objId =>
              dsimp only at h_eval
              cases hdel : hst.delObjShell objId with
              | error _ => rw [hdel] at h_eval; exact nomatch h_eval
              | ok hst1 =>
                rw [hdel] at h_eval
                cases hk : lowerImpureStepPure fuel ctx (st.freshVar .unit).2 (.inl k) with
                | error _ => rw [hk] at h_lower; exact nomatch h_lower
                | ok pk =>
                  rw [hk] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                  have hinv2 := bridgeInv_freshVar st lenv venv .unit .unit hinv
                  have hkEval := evalCode_fuel_mono_step fuel pk.1 _ hst1 v hst'
                    (ih (st.freshVar .unit).2 pk.2 lenv _ hst1 hst' v (.inl k) pk.1 hinv2 hk h_eval)
                  have hcall : evalExpr venv hst (.call "lean_native_del_obj" [objVid] .unit false) = .ok (.unit, hst1) := by
                    unfold evalExpr; dsimp only [evalVarList]; rw [hvalV]; dsimp only [↓reduceIte, Bool.false_eq_true]
                    rw [hdel]; rfl
                  dsimp only [evalCode]; rw [hcall]; exact hkEval
            | _ => exact nomatch h_eval
      | setTag x cidx k _ =>
        dsimp only [evalStep] at h_eval
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, MonadExceptOf.throw, throwThe] at h_lower
        cases hv : st.lookupBoundFVar x <;> rw [hv] at h_lower
        · exact nomatch h_lower
        · rename_i objVid; dsimp only at h_lower
          rcases lookupBoundFVar_inv st lenv venv x objVid hinv hv with ⟨_, hobjLt, ⟨val, hvalL, hvalV⟩, _, _⟩
          rw [hvalL] at h_eval
          cases hhp : (!(ctx.allowStage1DHeap && isHeapPtrType (st.getVarType objVid))) <;>
            simp only [hhp, ↓reduceIte, Bool.false_eq_true] at h_lower
          · cases val with
            | objPtr objId =>
              dsimp only at h_eval
              cases hset : hst.setHeapObjTagExclusive objId (cidx.toUInt64).toNat with
              | error _ => rw [hset] at h_eval; exact nomatch h_eval
              | ok hst1 =>
                rw [hset] at h_eval
                let st2 := (st.freshVar .i64).2
                let st3 := (st2.freshVar .unit).2
                cases hk : lowerImpureStepPure fuel ctx st3 (.inl k) with
                | error _ => rw [hk] at h_lower; exact nomatch h_lower
                | ok pk =>
                  rw [hk] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                  let venv1 := venv.bind (st.freshVar .i64).1 (.u64 cidx.toUInt64)
                  let venv2 := venv1.bind (st2.freshVar .unit).1 .unit
                  have hinv3 : BridgeStateInv st3 lenv venv2 :=
                    bridgeInv_freshVar st2 lenv venv1 .unit .unit
                      (bridgeInv_freshVar st lenv venv .i64 (.u64 cidx.toUInt64) hinv)
                  have hkEval := evalCode_fuel_mono_step fuel pk.1 venv2 hst1 v hst'
                    (ih st3 pk.2 lenv venv2 hst1 hst' v (.inl k) pk.1 hinv3 hk h_eval)
                  have htagId : (st.freshVar .i64).1 = st.nextVarId := (freshVar_spec st .i64).1
                  have hobjV1 : (venv.bind (st.freshVar .i64).1 (.u64 cidx.toUInt64)) objVid = some (.objPtr objId) := by
                    rw [htagId, venv_bind_fresh venv st.nextVarId objVid hobjLt]; exact hvalV
                  have htagV1 : (venv.bind (st.freshVar .i64).1 (.u64 cidx.toUInt64)) (st.freshVar .i64).1 = some (.u64 cidx.toUInt64) :=
                    VarEnv.bind_self _ _ _
                  have hcall : evalExpr (venv.bind (st.freshVar .i64).1 (.u64 cidx.toUInt64)) hst
                      (.call "lean_native_ctor_set_tag" [objVid, (st.freshVar .i64).1] .unit false) =
                      .ok (.unit, hst1) := by
                    have hvl : evalVarList (venv.bind (st.freshVar .i64).1 (.u64 cidx.toUInt64))
                        [objVid, (st.freshVar .i64).1] = .ok [.objPtr objId, .u64 cidx.toUInt64] := by
                      simp only [evalVarList, hobjV1, htagV1]
                    dsimp only [evalExpr]; rw [hvl]
                    change (hst.setHeapObjTagExclusive objId (cidx.toUInt64).toNat).map (Val.unit, ·) = .ok (Val.unit, hst1)
                    rw [hset]; rfl
                  change (match evalExpr venv hst (.scalar (.constU64 cidx.toUInt64)) with
                    | .ok (tv, hst0) => evalCode (fuel + 1) (venv.bind (st.freshVar .i64).1 tv) hst0
                        (.letBind (st2.freshVar .unit).1 .unit
                          (.call "lean_native_ctor_set_tag" [objVid, (st.freshVar .i64).1] .unit false) pk.1)
                    | .error e => .error e) = .ok (v, hst')
                  dsimp only [evalExpr, evalScalarExpr]
                  dsimp only [evalCode]; rw [hcall]; exact hkEval
            | _ => exact nomatch h_eval
          · exact nomatch h_lower
      | oset x idx y k _ =>
        dsimp only [evalStep] at h_eval
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, MonadExceptOf.throw, throwThe] at h_lower
        cases hv : st.lookupBoundFVar x <;> rw [hv] at h_lower
        · exact nomatch h_lower
        · rename_i objVid; dsimp only at h_lower
          rcases lookupBoundFVar_inv st lenv venv x objVid hinv hv with ⟨_, hobjLt, ⟨val, hvalL, hvalV⟩, htyL, _⟩
          have hisHeap : lenv.isHeapVar x = isHeapPtrType (st.getVarType objVid) := by
            dsimp only [LEnv.isHeapVar]; rw [htyL]
          cases hhp : (ctx.allowStage1DHeap && isHeapPtrType (st.getVarType objVid)) <;>
            simp only [hhp, ↓reduceIte, Bool.false_eq_true] at h_lower
          · cases hunb : isUnboxedScalarOrTuple (st.getVarType objVid) <;>
              simp only [hunb, ↓reduceIte, Bool.false_eq_true] at h_lower
            · exact nomatch h_lower
            · rw [hisHeap, unboxed_not_heap _ hunb] at h_eval
              simp only [Bool.not_false, ↓reduceIte] at h_eval
              exact evalCode_fuel_mono_step fuel code venv hst v hst'
                (ih st st' lenv venv hst hst' v (.inl k) code hinv h_lower h_eval)
          · have hhp2 : isHeapPtrType (st.getVarType objVid) = true := (Bool.and_eq_true _ _).mp hhp |>.2
            rw [hisHeap, hhp2, hvalL] at h_eval
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h_eval
            cases hy : lowerRealArg ctx st y true with
            | error _ => rw [hy] at h_lower; exact nomatch h_lower
            | ok py =>
              rw [hy] at h_lower; rcases py with ⟨valVid, stY⟩
              rcases lowerRealArg_sound ctx st lenv venv y true valVid stY hinv hy with
                ⟨yx, yVal, rfl, hluY, hevalY, hyValV, _, hstY⟩
              subst stY; dsimp only at h_lower
              have hvalLt : valVid < st.nextVarId := hinv.fvar_lt yx valVid hluY
              cases val with
              | objPtr objId =>
                dsimp only at h_eval; rw [hevalY] at h_eval; dsimp only at h_eval
                cases hwf : writeField hst objId (idx.toUInt64).toNat yVal true with
                | error _ => rw [hwf] at h_eval; exact nomatch h_eval
                | ok hst1 =>
                  rw [hwf] at h_eval
                  let st3 := (st.freshVar .i64).2
                  let st4 := (st3.freshVar .unit).2
                  cases hk : lowerImpureStepPure fuel ctx st4 (.inl k) with
                  | error _ => rw [hk] at h_lower; exact nomatch h_lower
                  | ok pk =>
                    rw [hk] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                    let venv1 := venv.bind (st.freshVar .i64).1 (.u64 idx.toUInt64)
                    let venv2 := venv1.bind (st3.freshVar .unit).1 .unit
                    have hinv4 : BridgeStateInv st4 lenv venv2 :=
                      bridgeInv_freshVar st3 lenv venv1 .unit .unit
                        (bridgeInv_freshVar st lenv venv .i64 (.u64 idx.toUInt64) hinv)
                    have hkEval := evalCode_fuel_mono_step fuel pk.1 venv2 hst1 v hst'
                      (ih st4 pk.2 lenv venv2 hst1 hst' v (.inl k) pk.1 hinv4 hk h_eval)
                    have hidxId : (st.freshVar .i64).1 = st.nextVarId := (freshVar_spec st .i64).1
                    have hobjV1 : (venv.bind (st.freshVar .i64).1 (.u64 idx.toUInt64)) objVid = some (.objPtr objId) := by
                      rw [hidxId, venv_bind_fresh venv st.nextVarId objVid hobjLt]; exact hvalV
                    have hvalV1 : (venv.bind (st.freshVar .i64).1 (.u64 idx.toUInt64)) valVid = some yVal := by
                      rw [hidxId, venv_bind_fresh venv st.nextVarId valVid hvalLt]; exact hyValV
                    have hidxV1 : (venv.bind (st.freshVar .i64).1 (.u64 idx.toUInt64)) (st.freshVar .i64).1 = some (.u64 idx.toUInt64) :=
                      VarEnv.bind_self _ _ _
                    have hcall : evalExpr (venv.bind (st.freshVar .i64).1 (.u64 idx.toUInt64)) hst
                        (.call "lean_native_ctor_set" [objVid, (st.freshVar .i64).1, valVid] .unit false) =
                        .ok (.unit, hst1) := by
                      have hvl : evalVarList (venv.bind (st.freshVar .i64).1 (.u64 idx.toUInt64))
                          [objVid, (st.freshVar .i64).1, valVid] = .ok [.objPtr objId, .u64 idx.toUInt64, yVal] := by
                        simp only [evalVarList, hobjV1, hidxV1, hvalV1]
                      dsimp only [evalExpr]; rw [hvl]
                      change (hst.writeHeapObjFieldExclusive objId (idx.toUInt64).toNat yVal true).map (Val.unit, ·) = .ok (Val.unit, hst1)
                      unfold writeField at hwf; rw [hwf]; rfl
                    change (match evalExpr venv hst (.scalar (.constU64 idx.toUInt64)) with
                      | .ok (iv, hst0) => evalCode (fuel + 1) (venv.bind (st.freshVar .i64).1 iv) hst0
                          (.letBind (st3.freshVar .unit).1 .unit
                            (.call "lean_native_ctor_set" [objVid, (st.freshVar .i64).1, valVid] .unit false) pk.1)
                      | .error e => .error e) = .ok (v, hst')
                    dsimp only [evalExpr, evalScalarExpr]
                    dsimp only [evalCode]; rw [hcall]; exact hkEval
              | _ => rw [hevalY] at h_eval; exact nomatch h_eval
      | uset x i y k _ =>
        dsimp only [evalStep] at h_eval
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, MonadExceptOf.throw, throwThe] at h_lower
        cases hv : st.lookupBoundFVar x <;> rw [hv] at h_lower
        · exact nomatch h_lower
        · rename_i objVid; dsimp only at h_lower
          rcases lookupBoundFVar_inv st lenv venv x objVid hinv hv with ⟨_, hobjLt, ⟨val, hvalL, hvalV⟩, _, hctorL⟩
          split at h_lower
          · exact nomatch h_lower
          · cases hc : st.getActiveCtor? objVid <;> rw [hc] at h_lower
            · exact nomatch h_lower
            · rename_i cname; dsimp only at h_lower
              cases hlay : ctx.findLayout? cname <;> rw [hlay] at h_lower
              · exact nomatch h_lower
              · rename_i spec; dsimp only at h_lower
                cases hsl : spec.usizeSlot? i <;> rw [hsl] at h_lower
                · exact nomatch h_lower
                · rename_i slp; rcases slp with ⟨slot, slotTy⟩; dsimp only at h_lower
                  cases hy : st.lookupBoundFVar y <;> rw [hy] at h_lower
                  · exact nomatch h_lower
                  · rename_i valVid; dsimp only at h_lower
                    rcases lookupBoundFVar_inv st lenv venv y valVid hinv hy with ⟨_, hvalLt, ⟨yVal, hyValL, hyValV⟩, _, _⟩
                    rw [hvalL, hyValL] at h_eval
                    cases val with
                    | objPtr objId =>
                      have hslEq : (lenv.ctors x >>= ctx.findLayout? >>= (·.usizeSlot? i)) = some (slot, slotTy) := by
                        rw [hctorL, hc]; dsimp only [Bind.bind, Option.bind]; rw [hlay]; dsimp only; exact hsl
                      dsimp only at h_eval; rw [hslEq] at h_eval; dsimp only at h_eval
                      cases hwf : writeField hst objId (slot.toUInt64).toNat yVal false with
                      | error _ => rw [hwf] at h_eval; exact nomatch h_eval
                      | ok hst1 =>
                        rw [hwf] at h_eval
                        let st3 := (st.freshVar .i64).2
                        let st4 := (st3.freshVar .unit).2
                        cases hk : lowerImpureStepPure fuel ctx st4 (.inl k) with
                        | error _ => rw [hk] at h_lower; exact nomatch h_lower
                        | ok pk =>
                          rw [hk] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                          let venv1 := venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64)
                          let venv2 := venv1.bind (st3.freshVar .unit).1 .unit
                          have hinv4 : BridgeStateInv st4 lenv venv2 :=
                            bridgeInv_freshVar st3 lenv venv1 .unit .unit
                              (bridgeInv_freshVar st lenv venv .i64 (.u64 slot.toUInt64) hinv)
                          have hkEval := evalCode_fuel_mono_step fuel pk.1 venv2 hst1 v hst'
                            (ih st4 pk.2 lenv venv2 hst1 hst' v (.inl k) pk.1 hinv4 hk h_eval)
                          have hidxId : (st.freshVar .i64).1 = st.nextVarId := (freshVar_spec st .i64).1
                          have hobjV1 : (venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64)) objVid = some (.objPtr objId) := by
                            rw [hidxId, venv_bind_fresh venv st.nextVarId objVid hobjLt]; exact hvalV
                          have hvalV1 : (venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64)) valVid = some yVal := by
                            rw [hidxId, venv_bind_fresh venv st.nextVarId valVid hvalLt]; exact hyValV
                          have hidxV1 : (venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64)) (st.freshVar .i64).1 = some (.u64 slot.toUInt64) :=
                            VarEnv.bind_self _ _ _
                          have hcall : evalExpr (venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64)) hst
                              (.call "lean_native_ctor_set_scalar" [objVid, (st.freshVar .i64).1, valVid] .unit false) =
                              .ok (.unit, hst1) := by
                            have hvl : evalVarList (venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64))
                                [objVid, (st.freshVar .i64).1, valVid] = .ok [.objPtr objId, .u64 slot.toUInt64, yVal] := by
                              simp only [evalVarList, hobjV1, hidxV1, hvalV1]
                            dsimp only [evalExpr]; rw [hvl]
                            change (hst.writeHeapObjFieldExclusive objId (slot.toUInt64).toNat yVal false).map (Val.unit, ·) = .ok (Val.unit, hst1)
                            unfold writeField at hwf; rw [hwf]; rfl
                          change (match evalExpr venv hst (.scalar (.constU64 slot.toUInt64)) with
                            | .ok (iv, hst0) => evalCode (fuel + 1) (venv.bind (st.freshVar .i64).1 iv) hst0
                                (.letBind (st3.freshVar .unit).1 .unit
                                  (.call "lean_native_ctor_set_scalar" [objVid, (st.freshVar .i64).1, valVid] .unit false) pk.1)
                            | .error e => .error e) = .ok (v, hst')
                          dsimp only [evalExpr, evalScalarExpr]
                          dsimp only [evalCode]; rw [hcall]; exact hkEval
                    | _ => exact nomatch h_eval
      | sset x n off y _ k _ =>
        dsimp only [evalStep] at h_eval
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, MonadExceptOf.throw, throwThe] at h_lower
        cases hv : st.lookupBoundFVar x <;> rw [hv] at h_lower
        · exact nomatch h_lower
        · rename_i objVid; dsimp only at h_lower
          rcases lookupBoundFVar_inv st lenv venv x objVid hinv hv with ⟨_, hobjLt, ⟨val, hvalL, hvalV⟩, _, hctorL⟩
          split at h_lower
          · exact nomatch h_lower
          · cases hc : st.getActiveCtor? objVid <;> rw [hc] at h_lower
            · exact nomatch h_lower
            · rename_i cname; dsimp only at h_lower
              cases hlay : ctx.findLayout? cname <;> rw [hlay] at h_lower
              · exact nomatch h_lower
              · rename_i spec; dsimp only at h_lower
                cases hsl : spec.scalarSlot? n off <;> rw [hsl] at h_lower
                · exact nomatch h_lower
                · rename_i slp; rcases slp with ⟨slot, sfTy⟩; dsimp only at h_lower
                  cases hy : st.lookupBoundFVar y <;> rw [hy] at h_lower
                  · exact nomatch h_lower
                  · rename_i valVid; dsimp only at h_lower
                    rcases lookupBoundFVar_inv st lenv venv y valVid hinv hy with ⟨_, hvalLt, ⟨yVal, hyValL, hyValV⟩, _, _⟩
                    rw [hvalL, hyValL] at h_eval
                    cases val with
                    | objPtr objId =>
                      have hslEq : (lenv.ctors x >>= ctx.findLayout? >>= (·.scalarSlot? n off)) = some (slot, sfTy) := by
                        rw [hctorL, hc]; dsimp only [Bind.bind, Option.bind]; rw [hlay]; dsimp only; exact hsl
                      dsimp only at h_eval; rw [hslEq] at h_eval; dsimp only at h_eval
                      cases hwf : writeField hst objId (slot.toUInt64).toNat yVal false with
                      | error _ => rw [hwf] at h_eval; exact nomatch h_eval
                      | ok hst1 =>
                        rw [hwf] at h_eval
                        let st3 := (st.freshVar .i64).2
                        let st4 := (st3.freshVar .unit).2
                        cases hk : lowerImpureStepPure fuel ctx st4 (.inl k) with
                        | error _ => rw [hk] at h_lower; exact nomatch h_lower
                        | ok pk =>
                          rw [hk] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                          let venv1 := venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64)
                          let venv2 := venv1.bind (st3.freshVar .unit).1 .unit
                          have hinv4 : BridgeStateInv st4 lenv venv2 :=
                            bridgeInv_freshVar st3 lenv venv1 .unit .unit
                              (bridgeInv_freshVar st lenv venv .i64 (.u64 slot.toUInt64) hinv)
                          have hkEval := evalCode_fuel_mono_step fuel pk.1 venv2 hst1 v hst'
                            (ih st4 pk.2 lenv venv2 hst1 hst' v (.inl k) pk.1 hinv4 hk h_eval)
                          have hidxId : (st.freshVar .i64).1 = st.nextVarId := (freshVar_spec st .i64).1
                          have hobjV1 : (venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64)) objVid = some (.objPtr objId) := by
                            rw [hidxId, venv_bind_fresh venv st.nextVarId objVid hobjLt]; exact hvalV
                          have hvalV1 : (venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64)) valVid = some yVal := by
                            rw [hidxId, venv_bind_fresh venv st.nextVarId valVid hvalLt]; exact hyValV
                          have hidxV1 : (venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64)) (st.freshVar .i64).1 = some (.u64 slot.toUInt64) :=
                            VarEnv.bind_self _ _ _
                          have hcall : evalExpr (venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64)) hst
                              (.call "lean_native_ctor_set_scalar" [objVid, (st.freshVar .i64).1, valVid] .unit false) =
                              .ok (.unit, hst1) := by
                            have hvl : evalVarList (venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64))
                                [objVid, (st.freshVar .i64).1, valVid] = .ok [.objPtr objId, .u64 slot.toUInt64, yVal] := by
                              simp only [evalVarList, hobjV1, hidxV1, hvalV1]
                            dsimp only [evalExpr]; rw [hvl]
                            change (hst.writeHeapObjFieldExclusive objId (slot.toUInt64).toNat yVal false).map (Val.unit, ·) = .ok (Val.unit, hst1)
                            unfold writeField at hwf; rw [hwf]; rfl
                          change (match evalExpr venv hst (.scalar (.constU64 slot.toUInt64)) with
                            | .ok (iv, hst0) => evalCode (fuel + 1) (venv.bind (st.freshVar .i64).1 iv) hst0
                                (.letBind (st3.freshVar .unit).1 .unit
                                  (.call "lean_native_ctor_set_scalar" [objVid, (st.freshVar .i64).1, valVid] .unit false) pk.1)
                            | .error e => .error e) = .ok (v, hst')
                          dsimp only [evalExpr, evalScalarExpr]
                          dsimp only [evalCode]; rw [hcall]; exact hkEval
                    | _ => exact nomatch h_eval
      | cases cs =>
        dsimp only [evalStep] at h_eval
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, MonadExceptOf.throw, throwThe] at h_lower
        cases hv : st.lookupBoundFVar cs.discr <;> rw [hv] at h_lower
        · exact nomatch h_lower
        · rename_i condVar; dsimp only at h_lower
          rcases lookupBoundFVar_inv st lenv venv cs.discr condVar hinv hv with
            ⟨hluC, hcondLt, ⟨discrVal, hvalL, hvalV⟩, htyL, _⟩
          have hisHeap : lenv.isHeapVar cs.discr = isHeapPtrType (st.getVarType condVar) := by
            dsimp only [LEnv.isHeapVar]; rw [htyL]
          rw [hvalL, hisHeap] at h_eval; dsimp only at h_eval
          cases hhp : (ctx.allowStage1DHeap && cs.typeName != ``Bool && isHeapPtrType (st.getVarType condVar)) <;>
            simp only [hhp, ↓reduceIte, Bool.false_eq_true] at h_lower h_eval
          · cases hsc : (!isSupportedStage1BScalarType (st.getVarType condVar) ctx.arch) <;>
              simp only [hsc, ↓reduceIte, Bool.false_eq_true] at h_lower
            · rw [htyL] at h_eval; dsimp only [Option.getD] at h_eval
              have hsideSc : condVar < st.nextVarId ∧
                  (∀ dx, (none : Option Lean.FVarId) = some dx → (st.lookupFVar? dx).isSome = true) ∧
                  (lnirTypeEq (st.getVarType condVar) .i1 = true →
                    (cs.typeName == ``Bool || lnirTypeEq (st.getVarType condVar) .i1) = true) ∧
                  ∃ cond, venv condVar = some cond ∧
                    evalStep fuel ctx lenv hst
                      (.inr (cond, cs.typeName == ``Bool || lnirTypeEq (st.getVarType condVar) .i1, 0, none,
                        orderAltsPure cs.alts.toList)) = .ok (v, hst') := by
                refine ⟨hcondLt, ?_, ?_, discrVal, hvalV, h_eval⟩
                · intro _ h; cases h
                · intro hi1; rw [hi1, Bool.or_true]
              exact evalCode_fuel_mono_step fuel code venv hst v hst'
                (ih st st' lenv venv hst hst' v
                  (.inr (condVar, cs.typeName == ``Bool || lnirTypeEq (st.getVarType condVar) .i1, 0, none, orderAltsPure cs.alts.toList))
                  code hinv h_lower hsideSc)
            · exact nomatch h_lower
          · cases htag : tagOf discrVal hst with
            | error _ => rw [htag] at h_eval; exact nomatch h_eval
            | ok tag =>
              rw [htag] at h_eval
              rcases freshVar_spec st .i64 with ⟨htagId, hfn2, hft2, hflu2, _, _⟩
              cases hk : lowerImpureStepPure fuel ctx (st.freshVar .i64).2
                  (.inr ((st.freshVar .i64).1, false, 0, some cs.discr, orderAltsPure cs.alts.toList)) with
              | error _ => rw [hk] at h_lower; exact nomatch h_lower
              | ok pk =>
                rw [hk] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                have hinv2 : BridgeStateInv (st.freshVar .i64).2 lenv (venv.bind (st.freshVar .i64).1 tag) :=
                  bridgeInv_freshVar st lenv venv .i64 tag hinv
                have hsideHp : (st.freshVar .i64).1 < (st.freshVar .i64).2.nextVarId ∧
                    (∀ dx, some cs.discr = some dx → ((st.freshVar .i64).2.lookupFVar? dx).isSome = true) ∧
                    (lnirTypeEq ((st.freshVar .i64).2.getVarType (st.freshVar .i64).1) .i1 = true → false = true) ∧
                    ∃ cond, (venv.bind (st.freshVar .i64).1 tag) (st.freshVar .i64).1 = some cond ∧
                      evalStep fuel ctx lenv hst
                        (.inr (cond, false, 0, some cs.discr, orderAltsPure cs.alts.toList)) = .ok (v, hst') := by
                  refine ⟨?_, ?_, ?_, tag, VarEnv.bind_self _ _ _, h_eval⟩
                  · rw [htagId, hfn2]; exact Nat.lt_succ_self _
                  · intro dx hdx; injection hdx with hd; subst dx; rw [hflu2, hluC]; rfl
                  · intro hi1; simp only [htagId, hft2 st.nextVarId, beq_self_eq_true, ↓reduceIte, lnirTypeEq, lnirTypeEqFuel] at hi1; exact hi1
                have hkEval := evalCode_fuel_mono_step fuel pk.1 (venv.bind (st.freshVar .i64).1 tag) hst v hst'
                  (ih (st.freshVar .i64).2 pk.2 lenv (venv.bind (st.freshVar .i64).1 tag) hst hst' v
                    (.inr ((st.freshVar .i64).1, false, 0, some cs.discr, orderAltsPure cs.alts.toList))
                    pk.1 hinv2 hk hsideHp)
                have hcall : evalExpr venv hst (.call "lean_native_ctor_tag" [condVar] .i64 false) = .ok (tag, hst) := by
                  unfold evalExpr; dsimp only [evalVarList]; rw [hvalV]; dsimp only [↓reduceIte, Bool.false_eq_true]
                  unfold tagOf at htag
                  cases discrVal with
                  | objPtr objId =>
                    dsimp only [Functor.map, Except.map] at htag ⊢
                    cases hl : hst.liveHeapObj objId with
                    | error _ => rw [hl] at htag; exact nomatch htag
                    | ok o => rw [hl] at htag; injection htag with ht; subst tag; rfl
                  | u64 n => injection htag with ht; subst tag; rfl
                  | bool b => injection htag with ht; subst tag; rfl
                  | tuple vs =>
                    cases vs with
                    | nil => exact nomatch htag
                    | cons v0 rest =>
                      cases v0 with
                      | u64 n => injection htag with ht; subst tag; rfl
                      | _ => exact nomatch htag
                  | _ => exact nomatch htag
                dsimp only [evalCode]; rw [hcall]; exact hkEval
      | jp decl k =>
        dsimp only [evalStep] at h_eval
        cases hrec : hasJmpToPure fuel decl.fvarId (.inl decl.value) <;>
          simp only [hrec, ↓reduceIte, Bool.false_eq_true] at h_lower h_eval
        · exact evalCode_fuel_mono_step fuel code venv hst v hst'
            (ih (st.setJpDecl decl.fvarId decl.params.toList decl.value) st'
              (lenv.bindJp decl.fvarId { params := decl.params.toList, code := decl.value })
              venv hst hst' v (.inl k) code
              (bridgeInv_setJp st lenv venv decl.fvarId decl.params.toList decl.value hinv) h_lower h_eval)
        · exact nomatch h_lower
      | jmp fvarId args =>
        dsimp only [evalStep] at h_eval
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, MonadExceptOf.throw, throwThe] at h_lower
        cases hjp : st.lookupJp? fvarId <;> rw [hjp] at h_lower
        · exact nomatch h_lower
        · rename_i jpPair; rcases jpPair with ⟨jpParams, jpBody⟩; dsimp only at h_lower
          rw [hinv.jp_sync fvarId jpParams jpBody hjp] at h_eval; dsimp only at h_eval
          cases hb : bindJpCallArgsPure ctx st jpParams args.toList with
          | error _ => rw [hb] at h_lower; exact nomatch h_lower
          | ok pb =>
            rw [hb] at h_lower; rcases pb with ⟨binds, st1⟩; dsimp only at h_lower
            rcases bindJpCallArgsPure_rel ctx venv st.nextVarId jpParams args.toList st st1 lenv binds
                (Nat.le_refl _) (fun y vid hy => hinv.fvar_lt y vid hy) hinv hb with
              ⟨vs, hevalArgs, hfm1, hac1, hjp1, hnext1, hty1, hstepJp⟩
            rw [hevalArgs] at h_eval; dsimp only at h_eval
            have hinvSt1 : BridgeStateInv st1 lenv venv :=
              bridgeInv_ext st st1 lenv venv hinv hnext1 hty1 hfm1
                (fun u _ => by simp only [RealBridgeState.getActiveCtor?, hac1]) hjp1
            have hst1Lt : ∀ x vid, st1.lookupFVar? x = some vid → vid < st.nextVarId := by
              intro x vid hx
              have hx' : st.lookupFVar? x = some vid := by simp only [RealBridgeState.lookupFVar?, hfm1] at hx; exact hx
              exact hinv.fvar_lt x vid hx'
            rcases hstepJp st1 lenv venv st.nextVarId (fuel + 1) hst
                (match lowerImpureStepPure fuel ctx (applyJpParamMapPure st1 binds) (.inl jpBody) with
                 | .ok (bc, _) => bc | .error _ => .unreachable)
                hinvSt1 (Nat.le_refl _) (Nat.le_refl _) rfl hst1Lt (fun _ _ => rfl) with
              ⟨lenv', venv', hbindP, hinvIn, hevalWrap⟩
            rw [hbindP] at h_eval; dsimp only at h_eval
            cases hbody : lowerImpureStepPure fuel ctx (applyJpParamMapPure st1 binds) (.inl jpBody) with
            | error _ => rw [hbody] at h_lower; exact nomatch h_lower
            | ok pbody =>
              rw [hbody] at h_lower hevalWrap; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
              rw [hevalWrap]
              exact evalCode_fuel_mono_step fuel pbody.1 venv' hst v hst'
                (ih (applyJpParamMapPure st1 binds) pbody.2 lenv' venv' hst hst' v (.inl jpBody) pbody.1 hinvIn hbody h_eval)

theorem lowerImpureStepPure_sound (fuel : Nat) (ctx : RealBridgeCtx) (st st' : RealBridgeState)
    (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
    (target : Lean.Compiler.LCNF.Code .impure ⊕
      (VarId × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure)))
    (code : LNIRCode) :
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
    evalCode fuel venv hst code = .ok (v, hst') :=
  lowerImpureStepPure_sound_aux fuel ctx st st' lenv venv hst hst' v target code

theorem lowerRealLCNFCode_sound (fuel : Nat) (ctx : RealBridgeCtx) (st : RealBridgeState)
    (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
    (code : Lean.Compiler.LCNF.Code .impure) (lnir : LNIRCode) (st' : RealBridgeState)
    (hinv : BridgeStateInv st lenv venv)
    (h_lower : lowerRealLCNFCode fuel ctx st code = .ok (lnir, st'))
    (h_eval : evalRealLCNFCode fuel ctx lenv hst code = .ok (v, hst')) :
    evalCode fuel venv hst lnir = .ok (v, hst') :=
  lowerImpureStepPure_sound fuel ctx st st' lenv venv hst hst' v (.inl code) lnir hinv h_lower h_eval

theorem lowerRealLCNFDecl_sound (fuel : Nat) (ctx : RealBridgeCtx)
    (decl : Lean.Compiler.LCNF.Decl .impure) (args : List Val) (hst hst' : HeapState) (v : Val)
    (d : LNIRDecl) (mangled : String)
    (h_lower : lowerRealLCNFDecl fuel ctx decl mangled = .ok d)
    (h_eval : evalRealLCNFDecl fuel ctx decl args hst = .ok (v, hst')) :
    evalCode fuel ((d.params.zip args).foldl (fun acc (p, val) => acc.bind p.id val) VarEnv.empty) hst d.body =
      .ok (v, hst') := by
  unfold lowerRealLCNFDecl at h_lower; unfold evalRealLCNFDecl at h_eval
  cases hdv : decl.value with
  | extern _ => rw [hdv] at h_eval; exact nomatch h_eval
  | code c =>
    rw [hdv] at h_lower h_eval
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower h_eval
    cases hbp : bindParams LEnv.empty decl.params.toList args with
    | error _ => rw [hbp] at h_eval; exact nomatch h_eval
    | ok lenv =>
      rw [hbp] at h_eval
      cases hlc : lowerRealLCNFCode fuel ctx (internRealParams {} decl.params.toList).2 c with
      | error _ => rw [hlc] at h_lower; exact nomatch h_lower
      | ok plc =>
        rw [hlc] at h_lower; injection h_lower with hd; subst d; dsimp only
        exact lowerRealLCNFCode_sound fuel ctx (internRealParams {} decl.params.toList).2 lenv _
          hst hst' v c plc.1 plc.2
          (internRealParams_sound decl.params.toList args {} LEnv.empty lenv VarEnv.empty bridgeInv_empty hbp)
          hlc h_eval

end LeanNative.Proofs
