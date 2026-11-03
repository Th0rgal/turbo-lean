import LeanNative.Proofs.RealLCNFBridge.Scalar

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

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
          ∃ a b, evalScalarExpr venv cL = .ok (.bool a) ∧
            evalScalarExpr venv cR = .ok (.bool b) ∧ wrapBoolOut (op a b) retTy = .ok v := by
        intro op hop
        cases hg : ((!lnirTypeEq tL .i1 && !lnirTypeEq tL .i8) || (!lnirTypeEq tR .i1 && !lnirTypeEq tR .i8) ||
            (!lnirTypeEq retTy .i1 && !lnirTypeEq retTy .i8))
        · rcases hguard_false hg op hop with ⟨a, b, ha, hb, hw⟩
          exact ⟨a, b, toCond_sound venv vl tL va cL a hL hcL ha, toCond_sound venv vr tR vb cR b hR hcR hb, hw⟩
        · rw [hg] at hop; exact nomatch hop
      by_cases hand : fn == ``Bool.and
      · simp only [hand, ↓reduceIte] at hs ho; rcases hExt _ ho with ⟨a, b, ha, hb, hw⟩
        exact wrapOutExpr_sound venv hst _ retTy expr (a && b) v (fun _ h => False.elim (by cases h)) hs hw
          (by
            rw [evalScalar_select_bool venv cL cR (.constBool false) a ha]
            cases a
            · exact rfl
            · exact hb)
      · by_cases hor : fn == ``Bool.or
        · simp only [hand, hor, Bool.false_eq_true, ↓reduceIte] at hs ho; rcases hExt _ ho with ⟨a, b, ha, hb, hw⟩
          exact wrapOutExpr_sound venv hst _ retTy expr (a || b) v (fun _ h => False.elim (by cases h)) hs hw
            (by
              rw [evalScalar_select_bool venv cL (.constBool true) cR a ha]
              cases a
              · exact hb
              · exact rfl)
        · by_cases hxor : (fn == ``Bool.xor || fn == `Bool.bne || fn == `bne)
          · simp only [hand, hor, hxor, Bool.false_eq_true, ↓reduceIte] at hs ho; rcases hExt _ ho with ⟨a, b, ha, hb, hw⟩
            exact wrapOutExpr_sound venv hst _ retTy expr (a != b) v (fun _ h => False.elim (by cases h)) hs hw
              (by
                rw [evalScalar_unaryOp venv .not _ (.bool (a == b)) (by rw [evalScalar_binOp _ _ _ _ _ _ ha hb]; rfl)]
                cases a <;> cases b <;> rfl)
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
        · cases arch <;>
            simp only [archSupportsUSize, Bool.false_eq_true, ↓reduceIte,
              List.mem_cons, List.not_mem_nil, or_false] at hs1 <;>
            (first | exact False.elim hs1 | (cases hs1; rfl))
      · simp only [types, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd0
        rcases hd0 with (hd1 | hd1 | hd1 | hd1) | hd1
        · cases hd1; rfl
        · cases hd1; rfl
        · cases hd1; rfl
        · cases hd1; rfl
        · cases arch <;>
            simp only [archSupportsUSize, Bool.false_eq_true, ↓reduceIte,
              List.mem_cons, List.not_mem_nil, or_false] at hd1 <;>
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
        cases hg : ((lnirTypeEq tyA .i1 || lnirTypeEq tyA .i8) && lnirTypeEq retTy expectedRet &&
          isSupportedStage1BScalarType expectedRet arch)
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
                    else .binOp .bitAnd
                      (if isNeg then .binOp .sub (.constU64 0) (.var varg) else .unaryOp .not (.var varg))
                      (.constU64 mask)) ≠ .var u := by
                    intro u; split
                    · cases isNeg <;> intro h <;> exact nomatch h
                    · intro h; exact nomatch h
                  exact ⟨evalExpr_scalar venv hst _ _ (evalMaskOut venv _ _ mask arch opTy hraw hm), _, rfl, hnv⟩
                | _ => injection ho' with herr; cases isNeg <;> exact nomatch herr


end LeanNative.Proofs
