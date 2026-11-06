import LeanNative.Backend.StableHLOAst.Syntax
import LeanNative.Backend.StableHLOAst.Eval
import Std.Data.String.ToNat

namespace LeanNative.Backend.StableHLOAst

open LeanNative.IR

theorem stripPrefixChars_append (pre rest : List Char) :
    stripPrefixChars pre (pre ++ rest) = some rest := by
  induction pre <;> simp_all [stripPrefixChars]

theorem scanHLOFields_singleton_append (sep : Char) (field rest : List Char)
    (hn : sep ∉ field) (fuel : Nat) (hf : field.length < fuel) :
    scanHLOFields [sep] fuel (field ++ sep :: rest) =
      (scanHLOFields [sep] (fuel - field.length - 1) rest).map (fun fields => field :: fields) := by
  induction field generalizing fuel with
  | nil =>
    cases fuel with
    | zero => simp at hf
    | succ f =>
      simp only [scanHLOFields, stripPrefixChars, List.nil_append, List.isEmpty_cons,
        Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, List.length_nil, Nat.sub_zero,
        Nat.add_sub_cancel]
      cases scanHLOFields [sep] f rest <;> rfl
  | cons c cs ih =>
    cases fuel with
    | zero => simp at hf
    | succ f =>
      have hc : sep ≠ c := by simp_all
      have ht : sep ∉ cs := by simp_all
      simp only [List.cons_append, scanHLOFields, List.isEmpty_cons, Bool.false_eq_true,
        ↓reduceIte, stripPrefixChars, beq_iff_eq, hc]
      rw [ih ht f (by simpa using hf)]
      cases h : scanHLOFields [sep] (f - cs.length - 1) rest <;>
        simp [List.length_cons, Nat.succ_sub_succ_eq_sub, h]

theorem scanHLOFields_singleton_last (sep : Char) (field : List Char)
    (hn : sep ∉ field) (fuel : Nat) (hf : field.length < fuel) :
    scanHLOFields [sep] fuel field = some [field] := by
  induction field generalizing fuel with
  | nil => cases fuel <;> simp_all [scanHLOFields]
  | cons c cs ih =>
    cases fuel with
    | zero => simp at hf
    | succ f =>
      have hc : sep ≠ c := by simp_all
      have ht : sep ∉ cs := by simp_all
      simp [scanHLOFields, stripPrefixChars, hc, ih ht f (by simpa using hf)]

theorem scanHLOFields_intercalate (sep : Char) (fields : List (List Char))
    (hne : fields ≠ []) (hn : ∀ field ∈ fields, sep ∉ field)
    (fuel : Nat) (hf : (List.intercalate [sep] fields).length < fuel) :
    scanHLOFields [sep] fuel (List.intercalate [sep] fields) = some fields := by
  induction fields generalizing fuel with
  | nil => contradiction
  | cons field fields ih =>
    cases fields with
    | nil => simpa using scanHLOFields_singleton_last sep field (hn _ (by simp)) fuel (by simpa using hf)
    | cons next fields =>
      have he : List.intercalate [sep] (field :: next :: fields) =
          field ++ sep :: List.intercalate [sep] (next :: fields) := by
        simp [List.intercalate, List.intersperse]
      rw [he] at hf ⊢
      rw [scanHLOFields_singleton_append sep field _ (hn _ (by simp)) fuel (by simp at hf; omega)]
      rw [ih (by simp) (by intro x hx; exact hn x (by simp [hx])) _
        (by simp only [List.length_append, List.length_cons] at hf; omega)]
      rfl

theorem parseHLOFields_intercalate (sep : Char) (fields : List String)
    (hne : fields ≠ []) (hn : ∀ field ∈ fields, sep ∉ field.toList) :
    parseHLOFields (String.singleton sep) (String.intercalate (String.singleton sep) fields) =
      some fields := by
  unfold parseHLOFields
  have hs := scanHLOFields_intercalate sep (fields.map String.toList)
    (by simpa using hne) (by simpa using hn)
    ((List.intercalate [sep] (fields.map String.toList)).length + 1) (by omega)
  simpa [String.toList_intercalate, List.map_map] using congrArg
    (Option.map (List.map String.ofList)) hs

/-- Successful body parsing respects the printer's environment update at every step. -/
theorem parseBody_cons (tenv : TypeEnv) (line : String) (lines : List String)
    (op : StableHLOOp) (ops : List StableHLOOp)
    (hop : parseStableHLOOp tenv line = some op)
    (hrest : parseBody (bindResult tenv op) lines = some ops) :
    parseBody tenv (("    " ++ line) :: lines) = some (op :: ops) := by
  simp [parseBody, String.toList_append, hop, hrest]

/-- An identifier token recovers exactly its nonempty alphanumeric/underscore payload. -/
theorem parseSSAName_roundtrip (name : String) (hne : name.toList.isEmpty = false)
    (hchars : name.toList.all (fun c => c.isAlphanum || c == '_') = true) :
    parseSSAName ("%" ++ name) = some name := by
  simp [parseSSAName, String.toList_append, hne, hchars]

theorem CanonicalSSAName.parse_roundtrip (name : String) (h : CanonicalSSAName name) :
    parseSSAName ("%" ++ name) = some name :=
  parseSSAName_roundtrip name h.1 h.2

/-- Generated decimal suffixes preserve the SSA identifier alphabet. -/
theorem CanonicalSSAName.append_nat (pre : String) (h : CanonicalSSAName pre) (n : Nat) :
    CanonicalSSAName (pre ++ n.repr) := by
  have hd : n.repr.toList.all (fun c => c.isAlphanum || c == '_') = true := by
    apply List.all_eq_true.mpr
    intro c hc
    have hc := Nat.isDigit_of_mem_toDigits (b := 10) (n := n) (by omega) (by omega)
      (by simpa only [Nat.toList_repr] using hc)
    simp [Char.isAlphanum, hc]
  constructor
  · cases he : pre.toList with
    | nil => have := h.1; simp [he] at this
    | cons c cs => simp [String.toList_append, he]
  · rw [String.toList_append, List.all_append, h.2, hd]; rfl

/-- Canonicality is compositional with exactly the printer's SSA environment threading. -/
theorem CanonicalBody.append (tenv : TypeEnv) (xs ys : List StableHLOOp) :
    CanonicalBody tenv (xs ++ ys) ↔
      CanonicalBody tenv xs ∧ CanonicalBody (xs.foldl bindResult tenv) ys := by
  induction xs generalizing tenv with
  | nil => simp [CanonicalBody]
  | cons op ops ih => simp [CanonicalBody, ih, and_assoc]

/-- A closing tensor delimiter disambiguates `i1` from `i16`. -/
theorem parseElemType_roundtrip (ty : ElemType) (fuel : Nat) (rest : List Char) :
    parseElemType (fuel + 1) ((ppElemType ty).toList ++ '>' :: rest) =
      some (ty, '>' :: rest) := by
  cases ty <;> rfl

theorem ppElemType_injective_via_parser : Function.Injective ppElemType := by
  intro a b h
  have hp := congrArg (fun s : String => parseElemType 1 (s.toList ++ ['>'])) h
  simpa only [parseElemType_roundtrip, Option.some.injEq, Prod.mk.injEq, and_true] using hp

theorem parseElemType_complete (ty : ElemType) :
    parseElemType 1 (ppElemType ty).toList = some (ty, []) := by
  cases ty <;> rfl

theorem ppTensorType_fields (ty : TensorType) :
    ppTensorType ty = "tensor<" ++
      String.intercalate "x" (ty.shape.map Nat.repr ++ [ppElemType ty.elem]) ++ ">" := by
  cases ty with
  | mk shape elem =>
    cases shape with
    | nil => simp [ppTensorType, toString]
    | cons n ns =>
      rw [String.intercalate_append_of_ne_nil (by simp : (n :: ns).map Nat.repr ≠ [])
          (by simp : [ppElemType elem] ≠ [])]
      simp [ppTensorType, ppShape, toString, String.append_assoc]

theorem parseTensorType_roundtrip (ty : TensorType) :
    parseTensorType (ppTensorType ty) = some ty := by
  have hn (n : Nat) : 'x' ∉ n.repr.toList := by
    intro h
    have hd := Nat.isDigit_of_mem_toDigits (b := 10) (n := n) (by omega) (by omega)
      (by simpa only [Nat.toList_repr] using h)
    contradiction
  have he : 'x' ∉ (ppElemType ty.elem).toList := by cases ty.elem <;> decide
  have hs := parseHLOFields_intercalate 'x' (ty.shape.map Nat.repr ++ [ppElemType ty.elem])
    (by simp) (by
      intro field h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h; exact hn n
      · obtain rfl := List.mem_singleton.mp h; exact he)
  have hx : String.singleton 'x' = "x" := by decide
  rw [hx] at hs
  rw [ppTensorType_fields]
  simp only [parseTensorType, String.toList_append, String.reduceToList,
    List.cons_append, List.nil_append, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.reverse_reverse]
  simp only [String.ofList_toList]
  rw [hs]
  have hmap : ∀ xs : List Nat, xs.mapM (String.toNat? ∘ Nat.repr) = some xs := by
    intro xs
    induction xs <;> simp_all [List.mapM_cons, Function.comp_def]
  simp [parseElemType_complete, hmap]

theorem ppTensorType_injective : Function.Injective ppTensorType := by
  intro a b h
  have hp := congrArg parseTensorType h
  simpa only [parseTensorType_roundtrip, Option.some.injEq] using hp

theorem numElements_scalar (e : ElemType) :
    ({ shape := [], elem := e : TensorType }).numElements = 1 := rfl

theorem evalOp_constant_preserves_type (env : Env) (dst : String) (v : TensorVal)
    (h : v.data.size = v.ty.numElements) :
    ∃ env', evalOp env (.constant dst v) = .ok env' ∧ env' dst = some v := by
  unfold evalOp evalConstant
  simp [h, Env.bind]

theorem evalOp_preserves_tensorType (env : Env) (dst : String) (v : TensorVal)
    (h : v.wellFormed) :
    match evalOp env (.constant dst v) with
    | .ok env' => ∃ t, env' dst = some t ∧ t.ty = v.ty ∧ t.wellFormed
    | .error _ => False := by
  unfold TensorVal.wellFormed at h
  unfold evalOp evalConstant
  simp [h, Env.bind, TensorVal.wellFormed]

theorem reshape_invalid_volume_errors (env : Env) (dst src : String) (a : TensorVal)
    (outShape : List Nat) (hsrc : env src = some a)
    (hwf : a.data.size = a.ty.numElements)
    (hvol : a.ty.shape.foldl (· * ·) 1 ≠ outShape.foldl (· * ·) 1) :
    evalOp env (.reshape dst src outShape) =
      .error (.volumeMismatch (a.ty.shape.foldl (· * ·) 1) (outShape.foldl (· * ·) 1)) := by
  have hwf' : a.data.size = a.ty.shape.foldl (· * ·) 1 := by
    simpa [TensorType.numElements] using hwf
  unfold evalOp evalReshape reshapeData lookup checkWellFormed TensorType.numElements
  simp [hsrc, hwf', hvol, bind, Except.bind]

theorem maskWidth_idem (w : Nat) (x : BitVec 64) :
    maskWidth w (maskWidth w x) = maskWidth w x := by
  unfold maskWidth
  split
  · rfl
  · rename_i hge
    have hw : w ≤ 64 := Nat.le_of_lt (Nat.lt_of_not_ge hge)
    have hdvd : 2 ^ w ∣ 2 ^ 64 := ⟨2 ^ (64 - w), by rw [← Nat.pow_add, Nat.add_sub_of_le hw]⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ hdvd, Nat.mod_mod]

theorem maskWidth_add_left (w : Nat) (x y : BitVec 64) :
    maskWidth w (maskWidth w x + y) = maskWidth w (x + y) := by
  unfold maskWidth
  split
  · rfl
  · rename_i hge
    have hw : w < 64 := Nat.lt_of_not_ge hge
    have hlt64 : ∀ n, n % 2 ^ w < 2 ^ 64 := fun n =>
      Nat.lt_trans (Nat.mod_lt _ (Nat.two_pow_pos w)) (Nat.pow_lt_pow_right (by decide) hw)
    have hdvd : 2 ^ w ∣ 2 ^ 64 :=
      ⟨2 ^ (64 - w), by rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt hw)]⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat,
      BitVec.toNat_add, Nat.mod_eq_of_lt (hlt64 x.toNat),
      Nat.mod_mod_of_dvd _ hdvd, Nat.mod_mod_of_dvd _ hdvd, Nat.mod_add_mod]

theorem maskWidth_add_right (w : Nat) (x y : BitVec 64) :
    maskWidth w (x + maskWidth w y) = maskWidth w (x + y) := by
  rw [BitVec.add_comm x, maskWidth_add_left, BitVec.add_comm]

theorem elemBin_add_comm (e : ElemType) (x y : BitVec 64) :
    elemBin e (· + ·) x y = elemBin e (· + ·) y x := by
  unfold elemBin
  cases isFloat e
  · cases intBitWidth? e <;> simp [BitVec.add_comm]
  · simp

theorem elemBin_add_assoc (e : ElemType) (x y z : BitVec 64)
    (hf : isFloat e = false) (hw : (intBitWidth? e).isSome = true) :
    (do
      let xy ← elemBin e (· + ·) x y
      elemBin e (· + ·) xy z) =
    (do
      let yz ← elemBin e (· + ·) y z
      elemBin e (· + ·) x yz) := by
  unfold elemBin
  rcases hW : intBitWidth? e with _ | w
  · simp [hW] at hw
  · simp [hf, bind, Except.bind, maskWidth_idem, maskWidth_add_left, maskWidth_add_right,
      BitVec.add_assoc]

theorem zipMap_comm (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hf : ∀ x y, f x y = f y x) :
    ∀ (xs ys : List (BitVec 64)), xs.length = ys.length →
      (xs.zip ys).map (fun (x, y) => f x y) = (ys.zip xs).map (fun (x, y) => f x y)
  | [], [], _ => rfl
  | _ :: _, [], h => by cases h
  | [], _ :: _, h => by cases h
  | x :: xs, y :: ys, h => by
    simp [hf x y, zipMap_comm f hf xs ys (Nat.succ.inj h)]

theorem addAt_assoc (w : Nat) (a b c : BitVec 64) :
    addAt w (addAt w a b) c = addAt w a (addAt w b c) := by
  unfold addAt
  simp only [maskWidth_add_left, maskWidth_add_right, BitVec.add_assoc]

theorem zipWithTotal_comm (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hf : ∀ x y, f x y = f y x) (a b : Array (BitVec 64))
    (hlen : a.size = b.size) :
    zipWithTotal f a b = zipWithTotal f b a := by
  unfold zipWithTotal
  have hlist : a.toList.length = b.toList.length := by simp [hlen]
  rw [zipMap_comm f hf a.toList b.toList hlist]

theorem zipMap_assoc (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hf : ∀ x y z, f (f x y) z = f x (f y z)) :
    ∀ (xs ys zs : List (BitVec 64)), xs.length = ys.length → ys.length = zs.length →
      (((xs.zip ys).map (fun (x, y) => f x y)).zip zs).map (fun (x, y) => f x y) =
      (xs.zip ((ys.zip zs).map (fun (x, y) => f x y))).map (fun (x, y) => f x y)
  | [], [], [], _, _ => rfl
  | _ :: _, [], _, h1, _ => by cases h1
  | [], _ :: _, _, h1, _ => by cases h1
  | _ :: _, _ :: _, [], _, h2 => by cases h2
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    simp [hf x y z, zipMap_assoc f hf xs ys zs (Nat.succ.inj h1) (Nat.succ.inj h2)]

theorem zipWithTotal_assoc (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hf : ∀ x y z, f (f x y) z = f x (f y z))
    (a b c : Array (BitVec 64))
    (hab : a.size = b.size) (hbc : b.size = c.size) :
    zipWithTotal f (zipWithTotal f a b) c = zipWithTotal f a (zipWithTotal f b c) := by
  unfold zipWithTotal
  have hab' : a.toList.length = b.toList.length := by simp [hab]
  have hbc' : b.toList.length = c.toList.length := by simp [hbc]
  simp [zipMap_assoc f hf a.toList b.toList c.toList hab' hbc']

theorem stablehlo_add_comm (env : Env) (x y : TensorVal)
    (hx : env "x" = some x) (hy : env "y" = some y) (hty : x.ty = y.ty)
    (hwx : x.data.size = x.ty.numElements) (hwy : y.data.size = y.ty.numElements) :
    evalOp env (.add "d" "x" "y") = evalOp env (.add "d" "y" "x") := by
  have hlen : x.data.size = y.data.size := by rw [hwx, hwy, hty]
  unfold evalOp evalAdd lookup checkWellFormed
  simp [hx, hy, hty, hwx, hwy, bind, Except.bind]
  cases isFloat y.ty.elem
  · cases intBitWidth? y.ty.elem
    · rfl
    · rename_i w
      have hf : ∀ p q : BitVec 64, addAt w p q = addAt w q p := by
        intro p q
        unfold addAt
        simp [BitVec.add_comm]
      simp [zipWithTotal_comm _ hf _ _ hlen]
  · rfl

theorem stablehlo_add_assoc (env : Env) (x y z : TensorVal)
    (hx : env "x" = some x) (hy : env "y" = some y) (hz : env "z" = some z)
    (hty : x.ty = y.ty ∧ y.ty = z.ty)
    (hwx : x.data.size = x.ty.numElements)
    (hwy : y.data.size = y.ty.numElements)
    (hwz : z.data.size = z.ty.numElements)
    (hf : isFloat x.ty.elem = false) (hWsome : (intBitWidth? x.ty.elem).isSome = true) :
    (do
      let e1 ← evalOp env (.add "xy" "x" "y")
      let e2 ← evalOp e1 (.add "r" "xy" "z")
      pure (e2 "r")) =
    (do
      let e1 ← evalOp env (.add "yz" "y" "z")
      let e2 ← evalOp e1 (.add "r" "x" "yz")
      pure (e2 "r")) := by
  unfold evalOp evalAdd lookup checkWellFormed
  rcases hty with ⟨hty1, hty2⟩
  have hlen1 : x.data.size = y.data.size := by rw [hwx, hwy, hty1]
  have hlen2 : y.data.size = z.data.size := by rw [hwy, hwz, hty2]
  rcases hW : intBitWidth? x.ty.elem with _ | w
  · simp [hW] at hWsome
  · have hW' : intBitWidth? z.ty.elem = some w := by simpa [hty1, hty2] using hW
    have hf' : isFloat z.ty.elem = false := by simpa [hty1, hty2] using hf
    have hxy : (zipWithTotal (addAt w) x.data y.data).size = z.data.size := by
      unfold zipWithTotal
      simp [hlen1, hlen2]
    have hyz : (zipWithTotal (addAt w) y.data z.data).size = z.data.size := by
      unfold zipWithTotal
      simp [hlen2]
    simp [hx, hy, hz, hty1, hty2, hwx, hwy, hwz, hf', hW', Env.bind,
      bind, Except.bind, pure, Except.pure, hxy, hyz,
      zipWithTotal_assoc (addAt w) (addAt_assoc w) x.data y.data z.data hlen1 hlen2]

theorem evalOp_add_result_type (env : Env) (a b : TensorVal)
    (ha : env "a" = some a) (hb : env "b" = some b) (hty : a.ty = b.ty)
    (hwa : a.wellFormed) (hwb : b.wellFormed)
    (hf : isFloat a.ty.elem = false)
    (hW : (intBitWidth? a.ty.elem).isSome = true) :
    match evalOp env (.add "d" "a" "b") with
    | .ok env' => ∃ t, env' "d" = some t ∧ t.ty = a.ty ∧ t.wellFormed
    | .error _ => False := by
  unfold TensorVal.wellFormed at hwa hwb
  have hlen : a.data.size = b.data.size := by rw [hwa, hwb, hty]
  unfold evalOp evalAdd lookup checkWellFormed
  rcases hwidth : intBitWidth? a.ty.elem with _ | w
  · simp [hwidth] at hW
  · have hwidth' : intBitWidth? b.ty.elem = some w := by simpa [hty] using hwidth
    have hf' : isFloat b.ty.elem = false := by simpa [hty] using hf
    have hsz : (zipWithTotal (addAt w) a.data b.data).size = b.data.size := by
      unfold zipWithTotal
      simp [hlen]
    simp [ha, hb, hty, hwa, hwb, hf', hwidth', hsz, Env.bind, TensorVal.wellFormed,
      bind, Except.bind]

theorem isSigned_i1 : isSigned .i1 = false := rfl

theorem intBitWidth_float (e : ElemType) (h : isFloat e = true) : intBitWidth? e = none := by
  cases e <;> simp [isFloat, intBitWidth?] at *

theorem evalOps_nil (env : Env) : evalOps env [] = .ok env := rfl

theorem evalOps_singleton (env : Env) (op : StableHLOOp) :
    evalOps env [op] = evalOp env op := by
  have hex : ∀ (r : Except ShapeError Env), (r >>= fun e => Except.ok e) = r := by
    intro r
    cases r <;> rfl
  cases op <;> exact hex (evalOp env _)

end LeanNative.Backend.StableHLOAst
