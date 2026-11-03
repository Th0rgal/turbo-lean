import LeanNative.Proofs.StableHLOScalarLowerProofs

/-!
# 1-D `tensor<n x ui64>` StableHLO Operational Lemmas (`LeanNative.Proofs.StableHLOTensorProofs`)

Proves exact operational evaluation equations on `LeanNative.Backend.StableHLOAst` for
the 1-D tensor primitives emitted by `LeanNative.Backend.StableHLOLower`:
- `evalOp_broadcast_scalar` (`stablehlo.broadcast_in_dim` `0-D → 1-D`)
- `evalOp_add_vec` (`stablehlo.add` on `tensor<n x ui64>`)
- `evalOp_mul_vec` (`stablehlo.multiply` on `tensor<n x ui64>`)
- `evalOp_slice_one` (`stablehlo.slice` single-element `1-D → tensor<1 x ui64>`)
- `evalOp_reshape_vec1_to_scalar` / `evalOp_reshape_scalar_to_vec1` (`stablehlo.reshape`)
- `evalOp_dot_1d` (`stablehlo.dot_general` `1-D × 1-D → 0-D`)
-/

namespace LeanNative.Proofs

open LeanNative.Backend.StableHLOAst
open LeanNative.Backend.StableHLOLower

/-- Canonical 1-D `tensor<xs.size x ui64>` value wrapping an `Array UInt64`. -/
def mkVecUi64 (xs : Array UInt64) : TensorVal :=
  { ty := vecUi64Ty xs.size, data := xs.map UInt64.toBitVec }

theorem tensorVal_eq {a b : TensorVal} (hty : a.ty = b.ty) (hdata : a.data = b.data) :
    a = b := by
  cases a; cases b; simp_all

theorem checkWellFormed_mkVecUi64 (xs : Array UInt64) :
    checkWellFormed (mkVecUi64 xs) = .ok () := by
  simp [checkWellFormed, mkVecUi64, TensorType.numElements, vecUi64Ty]

theorem lookup_mkVecUi64 (tenv : Env) (r : String) (xs : Array UInt64)
    (h : tenv r = some (mkVecUi64 xs)) :
    lookup tenv r = .ok (mkVecUi64 xs) := by
  simp [lookup, h, checkWellFormed_mkVecUi64, Bind.bind, Except.bind]

theorem elemType_beq_refl (e : ElemType) : (e == e) = true := by
  cases e <;> rfl

theorem list_nat_beq_refl : (ns : List Nat) → (ns == ns) = true
  | [] => rfl
  | n :: ns => by
    change (n == n && (ns == ns)) = true
    rw [beq_self_eq_true, Bool.true_and]
    exact list_nat_beq_refl ns

theorem tensorType_beq_refl (ty : TensorType) : (ty == ty) = true := by
  rcases ty with ⟨shape, elem⟩
  change (shape == shape && elem == elem) = true
  rw [list_nat_beq_refl shape, elemType_beq_refl elem]
  rfl

theorem tensorType_bne_self (ty : TensorType) : (ty != ty) = false := by
  simp [bne, tensorType_beq_refl]

theorem maskWidth_ge64 (x : BitVec 64) : maskWidth 64 x = x := by
  simp [maskWidth]

theorem addAt_64 (x y : BitVec 64) : addAt 64 x y = x + y := by
  simp [addAt, maskWidth_ge64]

theorem list_zip_map_toBitVec (f : UInt64 → UInt64 → UInt64)
    (g : BitVec 64 → BitVec 64 → BitVec 64)
    (hfg : ∀ x y, g x.toBitVec y.toBitVec = (f x y).toBitVec) :
    ∀ (xs ys : List UInt64),
      ((xs.map UInt64.toBitVec).zip (ys.map UInt64.toBitVec)).map (fun p => g p.1 p.2) =
        ((xs.zip ys).map (fun p => f p.1 p.2)).map UInt64.toBitVec
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp [hfg x y, list_zip_map_toBitVec f g hfg xs ys]

theorem zipWithListM_ok (g : BitVec 64 → BitVec 64 → BitVec 64) :
    ∀ (xs ys : List (BitVec 64)), xs.length = ys.length →
      zipWithListM (fun x y => .ok (g x y)) xs ys =
        .ok ((xs.zip ys).map fun p => g p.1 p.2)
  | [], [], _ => rfl
  | _ :: _, [], h => by cases h
  | [], _ :: _, h => by cases h
  | x :: xs, y :: ys, h => by
    simp only [zipWithListM]
    change Except.bind (.ok (g x y)) (fun z =>
      Except.bind (zipWithListM (fun x y => .ok (g x y)) xs ys) (fun zs => .ok (z :: zs))) = _
    rw [zipWithListM_ok g xs ys (Nat.succ.inj h)]
    rfl

theorem foldlM_push_const (w : BitVec 64) :
    ∀ (is : List Nat) (acc : Array (BitVec 64)),
      is.foldlM (fun a _ => (do let v ← (.ok w : Except ShapeError (BitVec 64)); .ok (a.push v))) acc =
        .ok (acc ++ (List.replicate is.length w).toArray)
  | [], acc => by simp [List.foldlM, pure, Except.pure]
  | _ :: is, acc => by
    simp only [List.foldlM, List.length_cons, List.replicate_succ]
    change List.foldlM _ (acc.push w) is = _
    rw [foldlM_push_const w is (acc.push w)]
    congr 1
    apply Array.toList_inj.mp
    simp [Array.toList_append]

theorem mapRangeM_const (n : Nat) (w : BitVec 64) :
    mapRangeM n (fun _ => .ok w) = .ok ((List.replicate n w).toArray) := by
  unfold mapRangeM
  rw [foldlM_push_const w (List.range n) #[]]
  simp [List.length_range]

theorem evalOp_broadcast_scalar (tenv : Env) (d src : String) (n : Nat) (w : BitVec 64)
    (h : tenv src = some (mkScUi64 w)) :
    evalOp tenv (.broadcastInDim d src [n] []) =
      .ok (tenv.bind d (mkVecUi64 (List.replicate n (UInt64.ofBitVec w)).toArray)) := by
  have hbAt : broadcastAt [] [n] [] #[w] = fun _ => .ok w := by
    funext i
    simp [broadcastAt, flatIndex]
  change evalBroadcast tenv d src [n] [] = _
  unfold evalBroadcast
  rw [lookup_mkScUi64 _ _ _ h]
  change Except.bind (.ok (mkScUi64 w)) (fun a => _) = _
  dsimp only [mkScUi64, scUi64Ty, Except.bind]
  simp only [List.length_nil, dimsStrict, List.all_nil, List.zipIdx_nil, Bool.and_self,
    Bool.not_true, List.foldl_cons, List.foldl_nil, Nat.one_mul, hbAt, mapRangeM_const]
  change Except.ok (tenv.bind d { ty := vecUi64Ty n, data := (List.replicate n w).toArray }) = _
  congr 2
  unfold mkVecUi64
  apply tensorVal_eq
  · simp [vecUi64Ty]
  · apply Array.toList_inj.mp
    simp

theorem evalOp_add_vec (tenv : Env) (d a b : String) (xs ys : Array UInt64)
    (ha : tenv a = some (mkVecUi64 xs)) (hb : tenv b = some (mkVecUi64 ys))
    (hlen : xs.size = ys.size) :
    evalOp tenv (.add d a b) =
      .ok (tenv.bind d (mkVecUi64 ((xs.toList.zip ys.toList).map (fun p => p.1 + p.2)).toArray)) := by
  change evalAdd tenv d a b = _
  unfold evalAdd
  rw [lookup_mkVecUi64 _ _ _ ha, lookup_mkVecUi64 _ _ _ hb]
  change Except.bind (.ok (mkVecUi64 xs)) (fun x => Except.bind (.ok (mkVecUi64 ys)) (fun y => _)) = _
  dsimp only [Except.bind, mkVecUi64, vecUi64Ty]
  simp only [hlen, ↓reduceIte, isFloat, Bool.false_eq_true, intBitWidth?, Array.size_map]
  congr 2
  unfold zipWithTotal
  have hzip := list_zip_map_toBitVec (· + ·) (addAt 64)
    (fun x y => by rw [addAt_64]; exact (UInt64.toBitVec_add).symm) xs.toList ys.toList
  have hlenOut : ((xs.toList.zip ys.toList).map (fun p => p.1 + p.2)).length = ys.size := by
    simp [hlen]
  apply tensorVal_eq
  · simp [hlenOut]
  · apply Array.toList_inj.mp
    simp [hzip]

theorem evalOp_mul_vec (tenv : Env) (d a b : String) (xs ys : Array UInt64)
    (ha : tenv a = some (mkVecUi64 xs)) (hb : tenv b = some (mkVecUi64 ys))
    (hlen : xs.size = ys.size) :
    evalOp tenv (.multiply d a b) =
      .ok (tenv.bind d (mkVecUi64 ((xs.toList.zip ys.toList).map (fun p => p.1 * p.2)).toArray)) := by
  change evalMul tenv d a b = _
  unfold evalMul binSame zipWithM
  rw [lookup_mkVecUi64 _ _ _ ha, lookup_mkVecUi64 _ _ _ hb]
  change Except.bind (.ok (mkVecUi64 xs)) (fun a => Except.bind (.ok (mkVecUi64 ys)) (fun b => _)) = _
  dsimp only [Except.bind, mkVecUi64, vecUi64Ty]
  simp only [hlen, ↓reduceIte, Array.size_map]
  have hel : (fun x y => elemBin ElemType.ui64 (· * ·) x y) =
      (fun x y => .ok (x * y)) := by
    funext x y
    simp [elemBin, isFloat, intBitWidth?, maskWidth_ge64]
  rw [hel, zipWithListM_ok (· * ·) _ _ (by simp [hlen])]
  change Except.ok _ = _
  congr 2
  have hzip := list_zip_map_toBitVec (· * ·) (· * ·)
    (fun x y => (UInt64.toBitVec_mul).symm) xs.toList ys.toList
  have hlenOut : ((xs.toList.zip ys.toList).map (fun p => p.1 * p.2)).length = ys.size := by
    simp [hlen]
  apply tensorVal_eq
  · simp [hlenOut]
  · apply Array.toList_inj.mp
    simp [hzip]

theorem evalOp_slice_one (tenv : Env) (d src : String) (xs : Array UInt64) (idx : Nat)
    (h : tenv src = some (mkVecUi64 xs)) (hIdx : idx < xs.size) :
    evalOp tenv (.slice d src [idx] [idx + 1] [1]) =
      .ok (tenv.bind d (mkVecUi64 #[xs[idx]])) := by
  have hdim : sliceOutDim xs.size idx (idx + 1) 1 = some 1 := by
    unfold sliceOutDim
    have hc : (1 == 0 || decide (idx > idx + 1) || decide (idx + 1 > xs.size)) = false := by
      simp [Bool.or_eq_false_iff]; omega
    rw [hc]; simp only [Bool.false_eq_true, ↓reduceIte]
    congr 1; omega
  change evalSlice tenv d src [idx] [idx + 1] [1] = _
  unfold evalSlice sliceOne
  rw [lookup_mkVecUi64 _ _ _ h]
  change Except.bind (.ok (mkVecUi64 xs)) (fun a => _) = _
  dsimp only [Except.bind, mkVecUi64, vecUi64Ty]
  simp only [List.length_singleton, bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  have hod : sliceOutDims [xs.size] [idx] [idx + 1] [1] = .ok [1] := by
    simp [sliceOutDims, hdim, Bind.bind, Except.bind]
  rw [hod]
  have hsl : sliceAt [xs.size] [1] [idx] [1] (xs.map UInt64.toBitVec) 0 =
      .ok (xs[idx].toBitVec) := by
    unfold sliceAt sliceCoord unflat flatIndex
    simp [flatIndex, hIdx]
  have hm : mapRangeM 1 (sliceAt [xs.size] [1] [idx] [1] (xs.map UInt64.toBitVec)) =
      .ok #[xs[idx].toBitVec] := by
    unfold mapRangeM
    simp [List.range_one, List.foldlM, hsl, Bind.bind, Except.bind, pure, Except.pure]
  simp [Bind.bind, Except.bind, hm]

theorem evalOp_reshape_vec1_to_scalar (tenv : Env) (d src : String) (x : UInt64)
    (h : tenv src = some (mkVecUi64 #[x])) :
    evalOp tenv (.reshape d src []) =
      .ok (tenv.bind d (mkScUi64 x.toBitVec)) := by
  simp [evalOp, evalReshape, reshapeData, lookup_mkVecUi64 _ _ _ h, mkVecUi64, vecUi64Ty,
    mkScUi64, scUi64Ty, Bind.bind, Except.bind]

theorem evalOp_reshape_scalar_to_vec1 (tenv : Env) (d src : String) (x : UInt64)
    (h : tenv src = some (mkScUi64 x.toBitVec)) :
    evalOp tenv (.reshape d src [1]) =
      .ok (tenv.bind d (mkVecUi64 #[x])) := by
  simp [evalOp, evalReshape, reshapeData, lookup_mkScUi64 _ _ _ h, mkScUi64, scUi64Ty,
    mkVecUi64, vecUi64Ty, Bind.bind, Except.bind]

/-! ## 1-D `dot_general` (`[n] × [n] → []`) -/

theorem dotProductAt_1d (xs ys : Array UInt64) (n : Nat)
    (hx : xs.size = n) (hy : ys.size = n) (sum : BitVec 64) (j : Nat) (hj : j < n) :
    dotProductAt 64 [n] [n] [0] [0] [n]
        (xs.map UInt64.toBitVec) (ys.map UInt64.toBitVec) [] [] sum j =
      .ok (sum + (xs[j]'(by omega) * ys[j]'(by omega)).toBitVec) := by
  have hxlt : j < xs.size := by omega
  have hylt : j < ys.size := by omega
  unfold dotProductAt unflat gatherIdx axisAt flatIndex
  simp [List.range_one, Nat.mod_eq_of_lt hj, hj, flatIndex, hxlt, hylt,
    addAt_64, maskWidth_ge64, UInt64.toBitVec_mul]

theorem foldlM_add_ok (step : BitVec 64 → Nat → Except ShapeError (BitVec 64))
    (g : Nat → UInt64) :
    ∀ (is : List Nat) (acc : UInt64),
      (∀ j, j ∈ is → ∀ s, step s j = .ok (s + (g j).toBitVec)) →
      is.foldlM step acc.toBitVec = .ok ((is.foldl (fun a j => a + g j) acc).toBitVec)
  | [], acc, _ => by simp [List.foldlM, pure, Except.pure]
  | j :: is, acc, hstep => by
    simp only [List.foldlM, List.foldl_cons]
    have hj := hstep j (List.mem_cons_self ..) acc.toBitVec
    rw [hj]
    change is.foldlM step (acc.toBitVec + (g j).toBitVec) = _
    rw [← UInt64.toBitVec_add]
    exact foldlM_add_ok step g is (acc + g j)
      (fun i hi s => hstep i (List.mem_cons_of_mem j hi) s)

theorem range_map_bin_eq_zip_map (f : UInt64 → UInt64 → UInt64)
    (xs ys : Array UInt64) (n : Nat) (hx : xs.size = n) (hy : ys.size = n) :
    (List.range n).map (fun i => f (xs.getD i 0) (ys.getD i 0)) =
      (xs.toList.zip ys.toList).map (fun p => f p.1 p.2) := by
  apply List.ext_getElem
  · simp [hx, hy]
  · intro i h1 h2
    have hi : i < n := by simpa using h1
    have hxi : i < xs.size := by omega
    have hyi : i < ys.size := by omega
    simp [Array.getD, hxi, hyi]

theorem dotOperandOk_1d (n : Nat) : dotOperandOk [n] [] [0] = .ok [] := by
  rfl

theorem evalOp_dot_1d (tenv : Env) (d a b : String) (xs ys : Array UInt64)
    (ha : tenv a = some (mkVecUi64 xs)) (hb : tenv b = some (mkVecUi64 ys))
    (hlen : xs.size = ys.size) :
    evalOp tenv (.dotGeneral d a b [] [] [0] [0] []) =
      .ok (tenv.bind d (mkScUi64
        ((((xs.toList.zip ys.toList).map (fun p => p.1 * p.2)).foldl (· + ·) (0 : UInt64)).toBitVec))) := by
  have hx : xs.size = ys.size := hlen
  have hdot0 : dotAt 64 [] 0 0 [ys.size] [ys.size] [ys.size] [0] [0]
      (xs.map UInt64.toBitVec) (ys.map UInt64.toBitVec) 0 =
      .ok ((((xs.toList.zip ys.toList).map (fun p => p.1 * p.2)).foldl (· + ·) (0 : UInt64)).toBitVec) := by
    unfold dotAt
    simp only [unflat, List.take_nil, List.drop_nil, List.append_nil, List.foldl_cons,
      List.foldl_nil, Nat.one_mul]
    have hf := foldlM_add_ok
      (dotProductAt 64 [ys.size] [ys.size] [0] [0] [ys.size]
        (xs.map UInt64.toBitVec) (ys.map UInt64.toBitVec) [] [])
      (fun j => xs.getD j 0 * ys.getD j 0) (List.range ys.size) 0
      (fun j hj s => by
        have hjlt : j < ys.size := List.mem_range.mp hj
        have hxlt : j < xs.size := by omega
        rw [dotProductAt_1d xs ys ys.size hx rfl s j hjlt]
        simp [Array.getD, hxlt, hjlt])
    change (List.range ys.size).foldlM _ (0 : UInt64).toBitVec = _
    rw [hf, ← List.foldl_map (f := fun j => xs.getD j 0 * ys.getD j 0) (g := (· + ·)),
      range_map_bin_eq_zip_map (· * ·) xs ys ys.size hx rfl]
  have hm : mapRangeM 1 (dotAt 64 [] 0 0 [ys.size] [ys.size] [ys.size] [0] [0]
      (xs.map UInt64.toBitVec) (ys.map UInt64.toBitVec)) =
      .ok #[(((xs.toList.zip ys.toList).map (fun p => p.1 * p.2)).foldl (· + ·) (0 : UInt64)).toBitVec] := by
    unfold mapRangeM
    simp [List.range_one, List.foldlM, hdot0, Bind.bind, Except.bind, pure, Except.pure]
  simp [evalOp, evalDotGeneral, lookup_mkVecUi64 _ _ _ ha, lookup_mkVecUi64 _ _ _ hb,
    mkVecUi64, vecUi64Ty, hx, dotOperandOk_1d, isFloat, intBitWidth?, hm,
    mkScUi64, scUi64Ty, Bind.bind, Except.bind]
  rfl

/-! ## List Algebra Helpers for Vector Broadcasts -/

theorem zip_replicate_right_map (f : UInt64 → UInt64 → UInt64) (c : UInt64) :
    ∀ (xs : List UInt64),
      (xs.zip (List.replicate xs.length c)).map (fun p => f p.1 p.2) =
        xs.map (fun x => f x c)
  | [] => rfl
  | x :: xs => by
    simp [List.replicate_succ, zip_replicate_right_map f c xs]

theorem zip_replicate_left_map (f : UInt64 → UInt64 → UInt64) (c : UInt64) :
    ∀ (xs : List UInt64),
      ((List.replicate xs.length c).zip xs).map (fun p => f p.1 p.2) =
        xs.map (fun x => f c x)
  | [] => rfl
  | x :: xs => by
    simp [List.replicate_succ, zip_replicate_left_map f c xs]

theorem zip_map_left (g : UInt64 → UInt64) (f : UInt64 → UInt64 → UInt64) :
    ∀ (xs ys : List UInt64),
      ((xs.map g).zip ys).map (fun p => f p.1 p.2) =
        (xs.zip ys).map (fun p => f (g p.1) p.2)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp [zip_map_left g f xs ys]

theorem range_map_unary_eq_toList_map (f : UInt64 → UInt64) (xs : Array UInt64)
    (n : Nat) (hx : xs.size = n) :
    (List.range n).map (fun i => f (xs.getD i 0)) = xs.toList.map f := by
  apply List.ext_getElem
  · simp [hx]
  · intro i h1 _
    have hxi : i < xs.size := by simpa [hx] using h1
    simp [Array.getD, hxi]

end LeanNative.Proofs
