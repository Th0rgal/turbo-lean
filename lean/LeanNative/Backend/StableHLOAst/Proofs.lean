import LeanNative.Backend.StableHLOAst.Syntax
import LeanNative.Backend.StableHLOAst.Eval

namespace LeanNative.Backend.StableHLOAst

open LeanNative.IR

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
