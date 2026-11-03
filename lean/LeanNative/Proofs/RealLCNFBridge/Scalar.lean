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
    all_goals try (
      rename_i ys
      cases ys <;> unfold lnirTypeEqFuel at h <;> cases h)
    all_goals try (
      rename_i ys _
      cases ys <;> unfold lnirTypeEqFuel at h <;> cases h)
    rename_i xs ys
    cases xs <;> cases ys
    · rfl
    · unfold lnirTypeEqFuel at h; cases h
    · unfold lnirTypeEqFuel at h; cases h
    · rename_i x xs' y ys'
      dsimp only [lnirTypeEqFuel] at h
      rcases Bool.and_eq_true_iff.mp h with ⟨h1, h2⟩
      rw [lnirTypeEqFuel_sound fuel x y h1, LNIRType.tuple.inj (lnirTypeEqFuel_sound fuel (.tuple xs') (.tuple ys') h2)]

theorem lnirTypeEq_sound (a b : LNIRType) (h : lnirTypeEq a b = true) : a = b :=
  lnirTypeEqFuel_sound 32 a b h

theorem evalExpr_scalar (venv : VarEnv) (hst : HeapState) (se : ScalarExpr) (v : Val)
    (h : evalScalarExpr venv se = .ok v) :
    evalExpr venv hst (.scalar se) = .ok (v, hst) := by simp only [evalExpr, h]

theorem evalScalar_var (venv : VarEnv) (vid : VarId) (v : Val) (h : venv vid = some v) :
    evalScalarExpr venv (.var vid) = .ok v := by simp only [evalScalarExpr, h]

theorem evalScalar_binOp (venv : VarEnv) (op : BinOp) (a b : ScalarExpr) (va vb : Val)
    (ha : evalScalarExpr venv a = .ok va) (hb : evalScalarExpr venv b = .ok vb) :
    evalScalarExpr venv (.binOp op a b) = evalBinOp op va vb := by simp only [evalScalarExpr, ha, hb]

theorem evalScalar_unaryOp (venv : VarEnv) (op : UnaryOp) (a : ScalarExpr) (va : Val)
    (ha : evalScalarExpr venv a = .ok va) :
    evalScalarExpr venv (.unaryOp op a) = evalUnaryOp op va := by simp only [evalScalarExpr, ha]

theorem evalScalar_select_bool (venv : VarEnv) (c t e : ScalarExpr) (b : Bool)
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
    · simp only [hus, ↓reduceIte] at hm
      injection hm with h; subst h
      cases arch <;> rfl
  | _ => exact nomatch hm

private theorem shiftMaskOf_eq (arch : TargetArch) (ty : LNIRType) (sMask : UInt64)
    (hm : scalarShiftMask? ty arch = some sMask) : shiftMaskOf arch ty = sMask.toBitVec := by
  cases ty with
  | i8 | i16 | i32 | i64 => injection hm with h; subst h; rfl
  | usize =>
    unfold scalarShiftMask? at hm; cases hus : archSupportsUSize arch
    · simp only [hus, Bool.false_eq_true, ↓reduceIte] at hm; exact nomatch hm
    · simp only [hus, ↓reduceIte] at hm
      injection hm with h; subst h
      cases arch <;> rfl
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

theorem wrapBool_sound (venv : VarEnv) (cmp : ScalarExpr) (retTy : LNIRType)
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
  · simp only [h1, ↓reduceIte] at hs ho
    cases hs; cases ho; exact hc

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

theorem evalMaskOut (venv : VarEnv) (raw : ScalarExpr) (w : BitVec 64) (mask : UInt64)
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

theorem lookupFVar_cons (fvarMap : List (Lean.FVarId × VarId)) (x y : Lean.FVarId) (vid : VarId) :
    RealBridgeState.lookupFVar? { fvarMap := (x, vid) :: fvarMap.filter (fun (f, _) => f != x) } y =
      if y == x then some vid else RealBridgeState.lookupFVar? { fvarMap := fvarMap } y := by
  unfold RealBridgeState.lookupFVar?; rw [assoc_find_cons]
  cases y == x <;> rfl

theorem getVarType_setVarType (st : RealBridgeState) (vid w : VarId) (ty : LNIRType) :
    (st.setVarType vid ty).getVarType w = if w == vid then ty else st.getVarType w := by
  unfold RealBridgeState.setVarType RealBridgeState.getVarType; rw [assoc_find_cons]
  cases w == vid <;> rfl

theorem getActiveCtor_setActiveCtor (st : RealBridgeState) (vid w : VarId) (c : Lean.Name) :
    (st.setActiveCtor vid c).getActiveCtor? w = if w == vid then some c else st.getActiveCtor? w := by
  unfold RealBridgeState.setActiveCtor RealBridgeState.getActiveCtor?; rw [assoc_find_cons]
  cases w == vid <;> rfl

theorem lookupJp_setJpDecl (st : RealBridgeState) (j q : Lean.FVarId)
    (ps : List (Lean.Compiler.LCNF.Param .impure)) (body : Lean.Compiler.LCNF.Code .impure) :
    (st.setJpDecl j ps body).lookupJp? q = if q == j then some (ps, body) else st.lookupJp? q := by
  unfold RealBridgeState.setJpDecl RealBridgeState.lookupJp?; rw [assoc_find_cons]
  cases q == j <;> rfl

theorem getActiveCtor_filter_ne (activeCtor : List (VarId × Lean.Name)) (vid w : VarId) (hw : w ≠ vid) :
    RealBridgeState.getActiveCtor? { activeCtor := activeCtor.filter (fun (v, _) => v != vid) } w =
      RealBridgeState.getActiveCtor? { activeCtor := activeCtor } w := by
  unfold RealBridgeState.getActiveCtor?; dsimp only; congr 1
  apply find_filter_ne; intro a ha
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
        simp [h_m, h_i1] at h_lower h_eval <;>
          subst h_lower <;> subst h_eval <;>
          exact ⟨rfl, _, rfl, fun _ h => nomatch h⟩
    | usize x =>
      cases h_sup : archSupportsUSize arch
      · simp [h_sup, throw, throwThe, MonadExceptOf.throw] at h_lower
      · have harch : masked arch .usize x.toBitVec = (x &&& archUSizeMask arch).toBitVec := by
          cases arch <;> simp [masked, maskOf, widthOf, TargetArch.isWasm, archUSizeMask] <;> rfl
        simp only [h_sup, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h_lower h_eval
        rw [harch] at h_eval
        cases h_m : scalarWidthMask? retTy arch <;> cases h_i1 : lnirTypeEq retTy .i1 <;>
          simp [h_m, h_i1] at h_lower h_eval <;>
          subst h_lower <;> subst h_eval <;>
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
                  · injection hw with hw'; subst hw'
                    intro h; exact False.elim (by cases h)
                · injection hw with hw'; subst hw'; exact hc u
              cases op with
              | add | sub | mul | bitAnd | bitOr | bitXor =>
                cases hret : lnirTypeEq retTy ty
                · simp [hret] at ho
                · simp only [hret, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hs ho
                  injection hs with hse; subst hse
                  injection ho with hv; subst hv
                  refine ⟨evalMaskOut venv _ _ mask arch ty ?_ hm, hnotVarMask _ (fun _ h => nomatch h)⟩
                  rw [evalScalar_binOp _ _ _ _ _ _ hmaskL hmaskR]; rfl
              | div =>
                cases hret : lnirTypeEq retTy ty
                · simp [hret] at ho
                · simp only [hret, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hs ho
                  injection hs with hse; subst hse
                  injection ho with hv; subst hv
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
                  injection hs with hse; subst hse
                  injection ho with hv; subst hv
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
          · injection hw with hw'; subst hw'
            intro h; exact False.elim (by cases h)
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
              (by
                rw [evalScalar_select_bool venv (.var vl) (.var vr) (.constBool false) a hva]
                cases a
                · exact rfl
                · exact hvb),
              hnotVarWrap _ se (fun _ h => False.elim (by cases h)) hs⟩
          | bitOr =>
            exact ⟨wrapBool_sound venv _ retTy se (a || b) v hs ho
              (by
                rw [evalScalar_select_bool venv (.var vl) (.constBool true) (.var vr) a hva]
                cases a
                · exact hvb
                · exact rfl),
              hnotVarWrap _ se (fun _ h => False.elim (by cases h)) hs⟩
          | bitXor =>
            exact ⟨wrapBool_sound venv _ retTy se (a != b) v hs ho
              (by
                rw [evalScalar_unaryOp venv .not _ (.bool (a == b))
                  (by rw [evalScalar_binOp _ _ _ _ _ _ hva hvb]; rfl)]
                cases a <;> cases b <;> rfl),
              hnotVarWrap _ se (fun _ h => False.elim (by cases h)) hs⟩
          | eq =>
            exact ⟨wrapBool_sound venv _ retTy se (a == b) v hs ho
              (by rw [evalScalar_binOp _ _ _ _ _ _ hva hvb]; rfl),
              hnotVarWrap _ se (fun _ h => False.elim (by cases h)) hs⟩
          | _ => simp at hs
        | _ => exact False.elim (by cases op <;> cases ho)
      | _ => exact False.elim (by cases op <;> cases vb <;> cases ho)
  · simp only [husz, ↓reduceIte] at hs; exact False.elim (by cases hs)


end LeanNative.Proofs
