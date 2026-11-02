import LeanNative.Driver.CAbiEmit
import LeanNative.Backend.Hybrid

namespace LeanNative.Proofs.HybridCAbi

open LeanNative.Semantics
open LeanNative.Driver.CoreCLI
open LeanNative.Backend.Hybrid

/-!
# Theorem Group 1: Width-parameterized C99 ABI struct layout soundness
-/

theorem c99AlignUp_spec (n a result : Nat) (h : c99AlignUp n a = some result) :
    a ≠ 0 ∧ a ∣ result ∧ n ≤ result := by
  unfold c99AlignUp at h
  by_cases ha : a = 0
  · simp [ha] at h
  · simp [ha] at h
    rcases h with rfl
    refine ⟨ha, Nat.dvd_mul_left a ((n + (a - 1)) / a), ?_⟩
    have hpos : 0 < a := Nat.pos_of_ne_zero ha
    have heucl := Nat.mod_add_div (n + (a - 1)) a
    have hmod : (n + (a - 1)) % a < a := Nat.mod_lt (n + (a - 1)) hpos
    have hcomm : a * ((n + (a - 1)) / a) = (n + (a - 1)) / a * a := Nat.mul_comm _ _
    omega

theorem c99Scalar_align_pos (ty : C99ScalarType) (width : ArchWidth) :
    ty.alignOf width ≠ 0 := by
  cases ty <;> cases width <;> decide

theorem c99Scalar_size_pos (ty : C99ScalarType) (width : ArchWidth) :
    0 < ty.sizeOf width := by
  cases ty <;> cases width <;> decide

theorem c99NatMax_ge (a b : Nat) : a ≤ c99NatMax a b ∧ b ≤ c99NatMax a b := by
  unfold c99NatMax
  split <;> omega

theorem placeC99Field_spec (off : Nat) (spec : C99FieldSpec) (width : ArchWidth)
    (f : C99FieldLayout) (nextOff : Nat)
    (h : placeC99Field off spec width = some (f, nextOff)) :
    f.isAligned ∧ f.size = f.ty.sizeOf width ∧ f.align = f.ty.alignOf width ∧
    off ≤ f.offset ∧ f.offset < f.byteEnd ∧ nextOff = f.byteEnd := by
  unfold placeC99Field at h
  cases hal : c99AlignUp off (spec.ty.alignOf width) with
  | none => simp [hal] at h
  | some aligned =>
    simp [hal] at h
    obtain ⟨rfl, rfl⟩ := h
    rcases c99AlignUp_spec off (spec.ty.alignOf width) aligned hal with ⟨ha, hdvd, hle⟩
    have hsz : 0 < spec.ty.sizeOf width := c99Scalar_size_pos spec.ty width
    refine ⟨⟨ha, Nat.mod_eq_zero_of_dvd hdvd⟩, rfl, rfl, hle, ?_, rfl⟩
    unfold C99FieldLayout.byteEnd
    simp
    omega

theorem placeC99FieldsFrom_spec (specs : List C99FieldSpec) (off maxA : Nat) (width : ArchWidth)
    (placed : List C99FieldLayout) (finalAlign : Nat)
    (hmax : maxA ≠ 0)
    (h : placeC99FieldsFrom specs off maxA width = some (placed, finalAlign)) :
    finalAlign ≠ 0 ∧ maxA ≤ finalAlign ∧
    (∀ f ∈ placed, f.isAligned ∧ f.size = f.ty.sizeOf width ∧ f.align = f.ty.alignOf width ∧ off ≤ f.offset) ∧
    fieldsPairwiseDisjoint placed := by
  induction specs generalizing off maxA placed finalAlign with
  | nil =>
    simp [placeC99FieldsFrom] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨hmax, Nat.le_refl _, ?_, trivial⟩
    intro f hf
    cases hf
  | cons spec rs ih =>
    unfold placeC99FieldsFrom at h
    cases hp : placeC99Field off spec width with
    | none => simp [hp] at h
    | some fn =>
      rcases fn with ⟨field, nextOff⟩
      simp [hp] at h
      cases hrest : placeC99FieldsFrom rs nextOff (c99NatMax maxA field.align) width with
      | none => simp [hrest] at h
      | some rf =>
        rcases rf with ⟨restFields, fa⟩
        simp [hrest] at h
        obtain ⟨rfl, rfl⟩ := h
        rcases placeC99Field_spec off spec width field nextOff hp with
          ⟨hal, hsz, halEq, hoffLe, hltEnd, hnextEq⟩
        have hmax' : c99NatMax maxA field.align ≠ 0 := by
          have := (c99NatMax_ge maxA field.align).1
          omega
        rcases ih nextOff (c99NatMax maxA field.align) restFields fa hmax' hrest with
          ⟨hfa0, hfaGe, hrestAll, hrestDisj⟩
        have hm1 := (c99NatMax_ge maxA field.align).1
        refine ⟨hfa0, Nat.le_trans hm1 hfaGe, ?_, ?_⟩
        · intro g hg
          simp at hg
          rcases hg with rfl | hgRest
          · exact ⟨hal, hsz, halEq, hoffLe⟩
          · rcases hrestAll g hgRest with ⟨ga, gs, gal, goff⟩
            have hle : off ≤ g.offset := by omega
            exact ⟨ga, gs, gal, hle⟩
        · refine ⟨?_, hrestDisj⟩
          intro g hg
          rcases hrestAll g hg with ⟨_, _, _, goff⟩
          unfold c99IntervalsDisjoint
          left
          omega

theorem c99OccupiedEnd_ge (fields : List C99FieldLayout) :
    ∀ f ∈ fields, f.byteEnd ≤ c99OccupiedEnd fields := by
  induction fields with
  | nil => intro f hf; cases hf
  | cons f fs ih =>
    intro g hg
    unfold c99OccupiedEnd
    have hm := c99NatMax_ge f.byteEnd (c99OccupiedEnd fs)
    simp at hg
    rcases hg with rfl | hgFs
    · exact hm.1
    · exact Nat.le_trans (ih g hgFs) hm.2

/-- Every `computeC99StructLayout` output across LP64 (`bits64`) and `wasm32` (`bits32`)
    satisfies natural field alignment (`f.align ∣ f.offset`), pairwise disjoint half-open field
    intervals `[offset, offset + size)`, `structSize` covering all fields, and `structAlign ∣ structSize`. -/
theorem computeC99StructLayout_sound (name : String) (specs : List C99FieldSpec)
    (width : ArchWidth) (layout : C99StructLayout)
    (h : computeC99StructLayout name specs width = some layout) :
    c99LayoutSound layout width := by
  unfold computeC99StructLayout placeC99Fields at h
  cases hp : placeC99FieldsFrom specs 0 1 width with
  | none => simp [hp] at h
  | some pm =>
    rcases pm with ⟨placed, maxAlign⟩
    simp [hp] at h
    cases hsz : c99AlignUp (c99OccupiedEnd placed) maxAlign with
    | none => simp [hsz] at h
    | some sz =>
      simp [hsz] at h
      subst h
      rcases placeC99FieldsFrom_spec specs 0 1 width placed maxAlign (by decide) hp with
        ⟨hma0, _, hall, hdisj⟩
      rcases c99AlignUp_spec (c99OccupiedEnd placed) maxAlign sz hsz with ⟨_, hdvd, hoccLe⟩
      refine ⟨hma0, hdvd, ?_, hdisj, ?_⟩
      · intro f hf
        rcases hall f hf with ⟨fa, fs, fal, _⟩
        exact ⟨fa, fs, fal⟩
      · intro f hf
        exact Nat.le_trans (c99OccupiedEnd_ge placed f hf) hoccLe

/-- Explicit divisibility projection (`field.align ∣ field.offset`) for every field in a computed C99 layout. -/
theorem computeC99StructLayout_field_align_dvd (name : String) (specs : List C99FieldSpec)
    (width : ArchWidth) (layout : C99StructLayout) (f : C99FieldLayout)
    (h : computeC99StructLayout name specs width = some layout) (hf : f ∈ layout.fields) :
    f.align ≠ 0 ∧ f.align ∣ f.offset := by
  rcases computeC99StructLayout_sound name specs width layout h with ⟨_, _, hall, _, _⟩
  rcases (hall f hf).1 with ⟨ha, hmod⟩
  exact ⟨ha, Nat.dvd_of_mod_eq_zero hmod⟩

/-- Dual-width C11 preprocessor guards (`emitSliceStaticAsserts`) strictly check `__wasm32__` and
    `__LP64__` / `_LP64` (without `UINTPTR_MAX` LLP64 fallback) and fail closed via `#error` on `#else`. -/
theorem emitSliceStaticAsserts_fail_closed (flat64 mut64 flat32 mut32 : C99StructLayout) :
    "#elif defined(__LP64__) || defined(_LP64)" ∈ emitSliceStaticAsserts flat64 mut64 flat32 mut32 ∧
    "#else" ∈ emitSliceStaticAsserts flat64 mut64 flat32 mut32 ∧
    "#error \"Unsupported ABI data model: LeanNative C-ABI requires LP64 or wasm32\"" ∈
      emitSliceStaticAsserts flat64 mut64 flat32 mut32 := by
  unfold emitSliceStaticAsserts
  refine ⟨by simp, by simp, by simp⟩

/-- Pinned-width C11 preprocessor guards (`emitPinnedSliceStaticAsserts`) emit the exact target guard
    (`__wasm32__` vs `__LP64__ || _LP64`) and fail closed via `#error` on `#else`. -/
theorem emitPinnedSliceStaticAsserts_fail_closed (flatLayout mutLayout : C99StructLayout)
    (width : ArchWidth) :
    "#else" ∈ emitPinnedSliceStaticAsserts flatLayout mutLayout width ∧
    (match width with
     | .bits32 =>
       "#if defined(__wasm32__)" ∈ emitPinnedSliceStaticAsserts flatLayout mutLayout width ∧
       "#error \"Mismatched or unsupported C-ABI target: pinned to wasm32 (32-bit)\"" ∈
         emitPinnedSliceStaticAsserts flatLayout mutLayout width
     | .bits64 =>
       "#if defined(__LP64__) || defined(_LP64)" ∈ emitPinnedSliceStaticAsserts flatLayout mutLayout width ∧
       "#error \"Mismatched or unsupported C-ABI target: pinned to LP64 (64-bit)\"" ∈
         emitPinnedSliceStaticAsserts flatLayout mutLayout width) := by
  cases width <;> unfold emitPinnedSliceStaticAsserts <;> exact ⟨by simp, by simp, by simp⟩

/-!
# Theorem Group 2: Overflow-free strided span & C99 byte/float slice marshaling roundtrip
-/

theorem archWidth_addrLimit_pos (width : ArchWidth) :
    0 < width.addrLimit ∧ width.maxAddr + 1 = width.addrLimit := by
  cases width <;> decide

/-- `checkedByteLen len elemBytes width = some total` guarantees exact product and `< width.addrLimit`. -/
theorem checkedByteLen_no_overflow (len elemBytes total : Nat) (width : ArchWidth)
    (h : checkedByteLen len elemBytes width = some total) :
    len * elemBytes = total ∧ total < width.addrLimit := by
  rcases archWidth_addrLimit_pos width with ⟨hpos, hmaxEq⟩
  unfold checkedByteLen at h
  by_cases he : elemBytes = 0
  · simp [he] at h
    subst h
    exact ⟨by simp [he], hpos⟩
  · simp [he] at h
    by_cases hlen : len ≤ width.maxAddr / elemBytes
    · simp [hlen] at h
      subst h
      refine ⟨rfl, ?_⟩
      have hmul : len * elemBytes ≤ (width.maxAddr / elemBytes) * elemBytes :=
        Nat.mul_le_mul_right elemBytes hlen
      have hbound : (width.maxAddr / elemBytes) * elemBytes ≤ width.maxAddr :=
        Nat.div_mul_le_self width.maxAddr elemBytes
      omega
    · simp [hlen] at h

/-- `checkedStridedSpan` guarantees `elemSize ≠ 0`, `elemSize ≤ stride`, exact physical byte span
    `(len - 1) * stride + elemSize` (`0` when `len = 0`), and `< width.addrLimit`. -/
theorem checkedStridedSpan_no_overflow (len stride elemSize span : Nat) (width : ArchWidth)
    (h : checkedStridedSpan len stride elemSize width = some span) :
    elemSize ≠ 0 ∧ elemSize ≤ stride ∧
    span = stridedByteSpan len stride elemSize ∧ span < width.addrLimit := by
  rcases archWidth_addrLimit_pos width with ⟨hpos, _⟩
  unfold checkedStridedSpan stridedByteSpan at *
  by_cases hbad : elemSize = 0 ∨ stride < elemSize
  · simp [hbad] at h
  · have he0 : elemSize ≠ 0 := fun hz => hbad (Or.inl hz)
    have hle : elemSize ≤ stride := by omega
    have hs0 : stride ≠ 0 := by omega
    by_cases hlen : len = 0
    · simp [hbad, hlen] at h
      subst h
      exact ⟨he0, hle, by simp [hlen], hpos⟩
    · by_cases hmul : len - 1 ≤ width.maxAddr / stride
      · by_cases hlt : (len - 1) * stride + elemSize < width.addrLimit
        · simp only [hbad, ↓reduceIte, hlen, hs0, hmul, hlt, Option.some.injEq] at h
          subst h
          exact ⟨he0, hle, by simp [hlen], hlt⟩
        · simp only [hbad, ↓reduceIte, hlen, hs0, hmul, hlt, reduceCtorEq] at h
      · simp only [hbad, ↓reduceIte, hlen, hs0, hmul, reduceCtorEq] at h

theorem strided_slot_in_bounds (base len stride elemSize span i : Nat)
    (hspan : span = stridedByteSpan len stride elemSize)
    (hi : i < len) :
    base + i * stride + elemSize ≤ base + span := by
  unfold stridedByteSpan at hspan
  have hlen0 : len ≠ 0 := by omega
  simp [hlen0] at hspan
  have hi_le : i ≤ len - 1 := by omega
  have hmul : i * stride ≤ (len - 1) * stride := Nat.mul_le_mul_right stride hi_le
  omega

theorem byteArray_splice_extract_id (b : ByteArray) (lo hi : Nat)
    (h1 : lo ≤ hi) (h2 : hi ≤ b.size) :
    b.extract 0 lo ++ b.extract lo hi ++ b.extract hi b.size = b := by
  apply ByteArray.ext
  rw [ByteArray.data_append, ByteArray.data_append, ByteArray.data_extract,
    ByteArray.data_extract, ByteArray.data_extract]
  have hbsz : b.size = b.data.size := rfl
  have hleft : b.data.extract 0 lo ++ b.data.extract lo hi = b.data.extract 0 hi := by
    rw [Array.extract_append_extract]
    have hmin : min 0 lo = 0 := by omega
    have hmax : max lo hi = hi := by omega
    rw [hmin, hmax]
  rw [hleft, Array.extract_append_extract]
  have hmin2 : min 0 hi = 0 := by omega
  have hmax2 : max hi b.data.size = b.data.size := by omega
  rw [hbsz, hmin2, hmax2]
  simp

theorem copyStridedElem_size (bytes : ByteArray) (base stride elemSize i : Nat)
    (hbound : base + i * stride + elemSize ≤ bytes.size) :
    (copyStridedElem bytes base stride elemSize i).size = elemSize := by
  unfold copyStridedElem
  rw [ByteArray.size_extract]
  omega

theorem marshalStridedGo_eq_append (bytes : ByteArray) (base stride elemSize k : Nat) (acc : ByteArray) :
    marshalStridedGo bytes base stride elemSize k acc =
      marshalStridedGo bytes base stride elemSize k ByteArray.empty ++ acc := by
  induction k generalizing acc with
  | zero =>
    unfold marshalStridedGo
    apply ByteArray.ext
    rw [ByteArray.data_append]
    have hemp : ByteArray.empty.data = #[] := rfl
    rw [hemp]
    simp
  | succ n ih =>
    unfold marshalStridedGo
    rw [ih (copyStridedElem bytes base stride elemSize n ++ acc),
        ih (copyStridedElem bytes base stride elemSize n ++ ByteArray.empty)]
    apply ByteArray.ext
    have hemp : ByteArray.empty.data = #[] := rfl
    simp only [ByteArray.data_append, hemp, Array.append_empty, Array.append_assoc]

theorem marshalStridedGo_empty_size (bytes : ByteArray) (base stride elemSize k : Nat)
    (hk : ∀ i < k, base + i * stride + elemSize ≤ bytes.size) :
    (marshalStridedGo bytes base stride elemSize k ByteArray.empty).size = k * elemSize := by
  induction k with
  | zero => unfold marshalStridedGo; simp only [Nat.zero_mul]; rfl
  | succ n ih =>
    unfold marshalStridedGo
    rw [marshalStridedGo_eq_append]
    rw [ByteArray.size_append, ih (fun i hi => hk i (Nat.lt_succ_of_lt hi)),
        ByteArray.size_append, copyStridedElem_size bytes base stride elemSize n (hk n (Nat.lt_succ_self n))]
    have hemp : ByteArray.empty.size = 0 := rfl
    have hsucc : (n + 1) * elemSize = n * elemSize + elemSize := Nat.succ_mul n elemSize
    omega

theorem byteArray_extract_mid (pre mid post : ByteArray) :
    (pre ++ mid ++ post).extract pre.size (pre.size + mid.size) = mid := by
  apply ByteArray.ext
  have hpre : pre.size = pre.data.size := rfl
  have hmid : mid.size = mid.data.size := rfl
  rw [ByteArray.data_extract, ByteArray.data_append, ByteArray.data_append, hpre, hmid]
  ext idx h1 h2
  · simp [Array.size_extract, Array.size_append]
  · simp [Array.getElem_extract]

theorem marshalStridedGo_extract_slot (bytes : ByteArray) (base stride elemSize k j : Nat) (acc : ByteArray)
    (hk : ∀ i < k, base + i * stride + elemSize ≤ bytes.size)
    (hj : j < k) :
    (marshalStridedGo bytes base stride elemSize k acc).extract (j * elemSize) (j * elemSize + elemSize) =
      copyStridedElem bytes base stride elemSize j := by
  induction k generalizing acc with
  | zero => omega
  | succ n ih =>
    unfold marshalStridedGo
    by_cases hjn : j < n
    · exact ih _ (fun i hi => hk i (Nat.lt_succ_of_lt hi)) hjn
    · have hjEq : j = n := by omega
      subst hjEq
      rw [marshalStridedGo_eq_append]
      have hpre := marshalStridedGo_empty_size bytes base stride elemSize j (fun i hi => hk i (Nat.lt_succ_of_lt hi))
      have hmid := copyStridedElem_size bytes base stride elemSize j (hk j (Nat.lt_succ_self j))
      have hassoc :
          marshalStridedGo bytes base stride elemSize j ByteArray.empty ++
            (copyStridedElem bytes base stride elemSize j ++ acc) =
          marshalStridedGo bytes base stride elemSize j ByteArray.empty ++
            copyStridedElem bytes base stride elemSize j ++ acc := by
        apply ByteArray.ext
        simp only [ByteArray.data_append, Array.append_assoc]
      have hex := byteArray_extract_mid
        (marshalStridedGo bytes base stride elemSize j ByteArray.empty)
        (copyStridedElem bytes base stride elemSize j)
        acc
      rw [hassoc, hpre, hmid] at *
      exact hex

theorem unmarshalStridedGo_roundtrip (bytes : ByteArray) (base stride elemSize k : Nat) (payload : ByteArray)
    (hk : ∀ i < k, base + i * stride + elemSize ≤ bytes.size)
    (hslots : ∀ j < k, payload.extract (j * elemSize) (j * elemSize + elemSize) =
      copyStridedElem bytes base stride elemSize j) :
    unmarshalStridedGo bytes base stride elemSize k payload = bytes := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold unmarshalStridedGo
    rw [ih (fun i hi => hk i (Nat.lt_succ_of_lt hi)) (fun j hj => hslots j (Nat.lt_succ_of_lt hj))]
    unfold writeStridedElem
    dsimp only
    rw [hslots n (Nat.lt_succ_self n)]
    unfold copyStridedElem
    exact byteArray_splice_extract_id bytes (base + n * stride) (base + n * stride + elemSize)
      (by omega) (hk n (Nat.lt_succ_self n))

/-- Valid strided `ByteArray` slice marshaling (`byteStride = elemSize` or arbitrary `byteStride ≥ elemSize`)
    succeeds, extracts every strided element cleanly into a packed payload of size `v.len * v.elemSize`,
    and `unmarshalSlice` round-trips back to the exact original backing `ByteArray`. -/
theorem marshal_unmarshal_byte_slice_roundtrip (v : C99ByteView)
    (hv : v.isValid) :
    ∃ payload,
      marshalSlice v = some payload ∧
      payload.size = v.len * v.elemSize ∧
      (∀ i < v.len,
        payload.extract (i * v.elemSize) (i * v.elemSize + v.elemSize) =
          v.bytes.extract (v.base + i * v.effectiveStride) (v.base + i * v.effectiveStride + v.elemSize)) ∧
      unmarshalSlice v payload = some v.bytes := by
  rcases hv with ⟨hal0, _, _, hmod, span, hspan, hbsize, hwlim⟩
  rcases checkedStridedSpan_no_overflow v.len v.effectiveStride v.elemSize span v.width hspan with
    ⟨_, _, hspanEq, _⟩
  have hk : ∀ i < v.len, v.base + i * v.effectiveStride + v.elemSize ≤ v.bytes.size := by
    intro i hi
    exact Nat.le_trans (strided_slot_in_bounds v.base v.len v.effectiveStride v.elemSize span i hspanEq hi) hbsize
  let payload := marshalStridedGo v.bytes v.base v.effectiveStride v.elemSize v.len ByteArray.empty
  have hpsize : payload.size = v.len * v.elemSize :=
    marshalStridedGo_empty_size v.bytes v.base v.effectiveStride v.elemSize v.len hk
  have hslots : ∀ j < v.len, payload.extract (j * v.elemSize) (j * v.elemSize + v.elemSize) =
      copyStridedElem v.bytes v.base v.effectiveStride v.elemSize j := by
    intro j hj
    exact marshalStridedGo_extract_slot v.bytes v.base v.effectiveStride v.elemSize v.len j ByteArray.empty hk hj
  refine ⟨payload, ?_, hpsize, ?_, ?_⟩
  · unfold marshalSlice
    simp [hspan, hal0, hmod, hbsize, hwlim, payload]
  · intro i hi
    exact hslots i hi
  · unfold unmarshalSlice
    simp only [hspan]
    have hcond :
        (v.align != 0 && v.base % v.align == 0 &&
          decide (v.base + span ≤ v.bytes.size) &&
          decide (v.base + span ≤ v.width.addrLimit) &&
          payload.size == v.len * v.elemSize) = true := by
      simp [hal0, hmod, hbsize, hwlim, hpsize]
    rw [ite_eq_left_iff.mpr fun hc => absurd hcond hc]
    congr 1
    exact unmarshalStridedGo_roundtrip v.bytes v.base v.effectiveStride v.elemSize v.len payload hk hslots

/-- Valid `FloatArray` (`double*`) slice marshaling succeeds and `unmarshalFloatSlice` round-trips identically. -/
theorem marshal_unmarshal_float_slice_roundtrip (v : C99FloatView)
    (hv : v.isValid) :
    ∃ payload,
      marshalFloatSlice v = some payload ∧
      payload.size = v.len ∧
      unmarshalFloatSlice v.floats v.base payload = some v.floats := by
  rcases hv with ⟨hchecked, hbound⟩
  refine ⟨v.floats.data.extract v.base (v.base + v.len), ?_, ?_, ?_⟩
  · unfold marshalFloatSlice
    simp [hchecked, hbound]
  · have hfsz : v.floats.size = v.floats.data.size := rfl
    simp [Array.size_extract]
    omega
  · unfold unmarshalFloatSlice
    have hfsz : v.floats.size = v.floats.data.size := rfl
    have hsize : (v.floats.data.extract v.base (v.base + v.len)).size = v.len := by
      simp [Array.size_extract]
      omega
    have hcond : v.base + (v.floats.data.extract v.base (v.base + v.len)).size ≤ v.floats.size := by omega
    rw [ite_eq_left_iff.mpr fun h => absurd hcond h]
    congr 1
    apply FloatArray.ext
    change v.floats.data.extract 0 v.base ++
        v.floats.data.extract v.base (v.base + v.len) ++
        v.floats.data.extract (v.base + (v.floats.data.extract v.base (v.base + v.len)).size) v.floats.size =
      v.floats.data
    rw [hsize]
    have h1 :
        v.floats.data.extract 0 v.base ++
          v.floats.data.extract v.base (v.base + v.len) =
        v.floats.data.extract 0 (v.base + v.len) := by
      rw [Array.extract_append_extract]
      have hmin : min 0 v.base = 0 := by omega
      have hmax : max v.base (v.base + v.len) = v.base + v.len := by omega
      rw [hmin, hmax]
    rw [h1, Array.extract_append_extract]
    have hmin2 : min 0 (v.base + v.len) = 0 := by omega
    have hmax2 : max (v.base + v.len) v.floats.data.size = v.floats.data.size := by omega
    rw [hfsz, hmin2, hmax2]
    simp

/-- `validateC99Slice s width = true` implies `validC99Slice s width`
    (aligned stride/elemSize, strided span within `width` and `backingBytes`, aligned non-wrapping `dataPtr`). -/
theorem validateC99Slice_sound (s : C99SliceDesc) (width : ArchWidth)
    (h : validateC99Slice s width = true) :
    validC99Slice s width := by
  unfold validateC99Slice at h
  rcases Bool.and_eq_true_iff.mp h with ⟨hpre, hmatch⟩
  rcases Bool.and_eq_true_iff.mp hpre with ⟨hpre4, h5⟩
  rcases Bool.and_eq_true_iff.mp hpre4 with ⟨hpre3, h4⟩
  rcases Bool.and_eq_true_iff.mp hpre3 with ⟨hpre2, h3⟩
  rcases Bool.and_eq_true_iff.mp hpre2 with ⟨h1, h2⟩
  cases hcs : checkedStridedSpan s.len s.byteStride s.elemSize width with
  | none => simp [hcs] at hmatch
  | some span =>
    rw [hcs] at hmatch
    rcases Bool.and_eq_true_iff.mp hmatch with ⟨hcap, hptr⟩
    refine ⟨bne_iff_ne.mp h1, bne_iff_ne.mp h2, of_decide_eq_true h3,
      beq_iff_eq.mp h4, beq_iff_eq.mp h5, span, hcs, ?_, ?_⟩
    · rcases Bool.or_eq_true_iff.mp hcap with hc0 | hcle
      · exact Or.inl (beq_iff_eq.mp hc0)
      · exact Or.inr (of_decide_eq_true hcle)
    · cases hp : s.dataPtr with
      | none =>
        simp [hp] at hptr ⊢
        exact hptr
      | some ptr =>
        simp [hp] at hptr ⊢
        rcases hptr with ⟨hp1, hp2⟩
        exact ⟨hp1, hp2⟩

/-- `execValidatedSliceHostCall v id` succeeds only when `validC99Slice v.toSliceDesc v.width`
    holds and restores `v.bytes` identically. -/
theorem execValidatedSliceHostCall_id_roundtrip (v : C99ByteView) (out : ByteArray)
    (h : execValidatedSliceHostCall v id = some out) :
    validC99Slice v.toSliceDesc v.width ∧ out = v.bytes := by
  unfold execValidatedSliceHostCall at h
  cases hv : validateC99Slice v.toSliceDesc v.width
  · simp [hv] at h
  · simp [hv] at h
    cases hm : marshalSlice v with
    | none => simp [hm] at h
    | some packedIn =>
      simp [hm] at h
      have hvalidDesc : validC99Slice v.toSliceDesc v.width :=
        validateC99Slice_sound v.toSliceDesc v.width hv
      unfold marshalSlice at hm
      cases hcs : checkedStridedSpan v.len v.effectiveStride v.elemSize v.width with
      | none => simp [hcs] at hm
      | some span =>
        simp [hcs] at hm
        obtain ⟨⟨⟨⟨ha, hmod⟩, hbSz⟩, hbLim⟩, rfl⟩ := hm
        have hnz : v.elemSize ≠ 0 ∧ v.elemSize ≤ v.effectiveStride := by
          unfold checkedStridedSpan at hcs
          by_cases hbad : v.elemSize = 0 ∨ v.effectiveStride < v.elemSize
          · simp [hbad] at hcs
          · omega
        have hvView : v.isValid :=
          ⟨ha, hnz.1, hnz.2, hmod, span, hcs, hbSz, hbLim⟩
        rcases marshal_unmarshal_byte_slice_roundtrip v hvView with ⟨payload, hm2, _, _, hunm⟩
        unfold marshalSlice at hm2
        simp [hcs, ha, hmod, hbSz, hbLim] at hm2
        subst hm2
        rw [hunm] at h
        injection h with hout
        exact ⟨hvalidDesc, hout.symm⟩

/-!
# Theorem Group 3: Strided elementwise non-overlap, operational HeapState RC lifecycle, and hybrid dispatch soundness
-/

theorem checkedBytes_spec (b : DeviceBufferDesc) (span : Nat)
    (h : b.checkedBytes = some span) :
    b.elemBytes ≠ 0 ∧ b.elemBytes ≤ b.byteStride ∧
    span = b.byteSpan ∧ span < 2 ^ 64 := by
  unfold DeviceBufferDesc.checkedBytes DeviceBufferDesc.byteSpan at *
  by_cases hbad : b.elemBytes = 0 ∨ b.byteStride < b.elemBytes
  · simp [hbad] at h
  · have he0 : b.elemBytes ≠ 0 := fun hz => hbad (Or.inl hz)
    have hle : b.elemBytes ≤ b.byteStride := by omega
    have hs0 : b.byteStride ≠ 0 := by omega
    by_cases hlen : b.numElems = 0
    · simp [hbad, hlen] at h
      subst h
      exact ⟨he0, hle, by simp [hlen], by decide⟩
    · by_cases hmul : b.numElems - 1 ≤ (2 ^ 64 - 1) / b.byteStride
      · by_cases hlt : (b.numElems - 1) * b.byteStride + b.elemBytes < 2 ^ 64
        · simp only [hbad, ↓reduceIte, hlen, hs0, hmul, hlt, Option.some.injEq] at h
          subst h
          exact ⟨he0, hle, by simp [hlen], hlt⟩
        · simp only [hbad, ↓reduceIte, hlen, hs0, hmul, hlt, reduceCtorEq] at h
      · simp only [hbad, ↓reduceIte, hlen, hs0, hmul, reduceCtorEq] at h

/-- Every physical byte `elemByteAddr b i k` (`i < b.numElems`, `k < b.elemBytes`) lies strictly inside
    the half-open interval `[b.baseAddr, b.addressEnd)`. -/
theorem elemByteAddr_in_addressInterval (b : DeviceBufferDesc) (i k : Nat)
    (hg : b.geometryOk) (hi : i < b.numElems) (hk : k < b.elemBytes) :
    b.baseAddr ≤ b.elemByteAddr i k ∧ b.elemByteAddr i k < b.addressEnd := by
  rcases hg with ⟨_, _, _, _, _, span, hchk, _⟩
  rcases checkedBytes_spec b span hchk with ⟨_, _, hspanEq, _⟩
  unfold DeviceBufferDesc.elemByteAddr DeviceBufferDesc.addressEnd
  rw [hchk]
  simp only [Option.getD_some]
  unfold DeviceBufferDesc.byteSpan at hspanEq
  have hlen0 : b.numElems ≠ 0 := by omega
  simp [hlen0] at hspanEq
  have hi_le : i ≤ b.numElems - 1 := by omega
  have hmul : i * b.byteStride ≤ (b.numElems - 1) * b.byteStride :=
    Nat.mul_le_mul_right b.byteStride hi_le
  omega

/-- Elementwise physical byte non-overlap: whenever two valid buffers satisfy `disjointBuffers a b`
    and at least one is mutable (`isMutableTransfer`), no byte of any strided element of `a` can equal
    any byte of any strided element of `b`. -/
theorem disjointBuffers_elemByteAddr_ne (a b : DeviceBufferDesc)
    (hga : a.geometryOk) (hgb : b.geometryOk)
    (hdisj : disjointBuffers a b)
    (hmut : isMutableTransfer a.direction = true ∨ isMutableTransfer b.direction = true)
    (i ka j kb : Nat)
    (hi : i < a.numElems) (hka : ka < a.elemBytes)
    (hj : j < b.numElems) (hkb : kb < b.elemBytes) :
    a.elemByteAddr i ka ≠ b.elemByteAddr j kb := by
  rcases elemByteAddr_in_addressInterval a i ka hga hi hka with ⟨haLo, haHi⟩
  rcases elemByteAddr_in_addressInterval b j kb hgb hj hkb with ⟨hbLo, hbHi⟩
  rcases hdisj with ⟨haRo, hbRo⟩ | ⟨_, hInt⟩
  · simp [haRo, hbRo, isMutableTransfer] at hmut
  · unfold addressIntervalsDisjoint at hInt
    omega

theorem launchGeometryOk_sound (req : HybridLaunchRequest) (h : launchGeometryOk req = true) :
    validLaunchGeometry req := by
  unfold launchGeometryOk validLaunchGeometry Dim3.allPositive gridThreadsOf Dim3.volume at *
  simp [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨gx, gy⟩, gz⟩, bx⟩, by_⟩, bz⟩, hmax⟩, hcov⟩
  refine ⟨⟨gx, gy, gz⟩, ⟨bx, by_, bz⟩, hmax, ?_⟩
  rcases hcov with htail | hnot
  · exact Or.inl htail
  · refine Or.inr ⟨?_, hnot.2⟩
    simp [hnot.1]

theorem bufferGeometryOk_sound (b : DeviceBufferDesc) (h : bufferGeometryOk b = true) :
    b.geometryOk := by
  unfold bufferGeometryOk at h
  rcases Bool.and_eq_true_iff.mp h with ⟨hpre, hmatch⟩
  rcases Bool.and_eq_true_iff.mp hpre with ⟨hpre4, h5⟩
  rcases Bool.and_eq_true_iff.mp hpre4 with ⟨hpre3, h4⟩
  rcases Bool.and_eq_true_iff.mp hpre3 with ⟨hpre2, h3⟩
  rcases Bool.and_eq_true_iff.mp hpre2 with ⟨h1, h2⟩
  cases hcs : b.checkedBytes with
  | none => simp [hcs] at hmatch
  | some span =>
    rw [hcs] at hmatch
    exact ⟨bne_iff_ne.mp h1, bne_iff_ne.mp h2, of_decide_eq_true h3,
      beq_iff_eq.mp h4, beq_iff_eq.mp h5, span, hcs, of_decide_eq_true hmatch⟩

theorem bufferGeometryOk_of_geometryOk (b : DeviceBufferDesc) (hg : b.geometryOk) :
    bufferGeometryOk b = true := by
  rcases hg with ⟨h1, h2, h3, h4, h5, span, hcs, h6⟩
  unfold bufferGeometryOk
  simp [h1, h2, h3, h4, h5, hcs, h6]

theorem targetBufferGeometryOk_sound (target : ComputeTarget) (b : DeviceBufferDesc)
    (h : targetBufferGeometryOk target b = true) :
    b.targetGeometryOk target := by
  unfold targetBufferGeometryOk at h
  rcases Bool.and_eq_true_iff.mp h with ⟨hg, hpage⟩
  refine ⟨bufferGeometryOk_sound b hg, ?_⟩
  intro ⟨ht, hzc⟩
  subst ht
  have hm : (ComputeTarget.gpuMetal == ComputeTarget.gpuMetal) = true := rfl
  rw [hm, hzc] at hpage
  simp at hpage
  exact hpage

theorem bufferOwnershipOk_sound (b : DeviceBufferDesc) (h : bufferOwnershipOk b = true) :
    b.ownershipOk := by
  unfold bufferOwnershipOk DeviceBufferDesc.ownershipOk at *
  cases hd : b.direction <;> simp [hd, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at h ⊢
  · exact ⟨Nat.pos_of_ne_zero h.1, h.2⟩
  · exact h
  · exact h

theorem buffersOwned_of_all (target : ComputeTarget) (buffers : List DeviceBufferDesc)
    (hg : ∀ b ∈ buffers, targetBufferGeometryOk target b = true)
    (ho : ∀ b ∈ buffers, bufferOwnershipOk b = true) :
    buffersOwned target buffers := by
  induction buffers with
  | nil => trivial
  | cons b rest ih =>
    refine ⟨targetBufferGeometryOk_sound target b (hg b (by simp)),
      bufferOwnershipOk_sound b (ho b (by simp)),
      ih (fun x hx => hg x (by simp [hx])) (fun x hx => ho x (by simp [hx]))⟩

theorem bufferAliasPairOk_sound (a b : DeviceBufferDesc) (h : bufferAliasPairOk a b = true) :
    disjointBuffers a b := by
  unfold bufferAliasPairOk disjointBuffers addressIntervalsDisjoint at *
  simp [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at h
  exact h

theorem bufferAliasOk_sound (buffers : List DeviceBufferDesc) (h : bufferAliasOk buffers = true) :
    buffersDisjoint buffers := by
  induction buffers with
  | nil => trivial
  | cons a rest ih =>
    unfold bufferAliasOk at h
    simp [Bool.and_eq_true, List.all_eq_true] at h
    rcases h with ⟨hpair, hrest⟩
    exact ⟨fun b hb => bufferAliasPairOk_sound a b (hpair b hb), ih hrest⟩

/-!
## Operational `HeapState` RC lifecycle lemmas (`pin -> launch -> sync -> release`)
-/

theorem find?_map_preserve_buf_id (bs : List ArrayBuffer) (bufId : Nat) (f : ArrayBuffer → ArrayBuffer)
    (hid : ∀ b, (f b).id = b.id) :
    (bs.map f).find? (fun b => b.id == bufId) = (bs.find? (fun b => b.id == bufId)).map f := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.map, List.find?, hid b]
    cases b.id == bufId <;> simp [ih]

theorem find?_setBufferExclusive (bs : List ArrayBuffer) (bufId : Nat) (excl : Bool) :
    (HeapState.setBufferExclusive bs bufId excl).find? (fun b => b.id == bufId) =
      (bs.find? (fun b => b.id == bufId)).map (fun b => if b.id == bufId then { b with exclusive := excl } else b) := by
  unfold HeapState.setBufferExclusive
  apply find?_map_preserve_buf_id
  intro b
  by_cases h : (b.id == bufId) = true <;> simp [h]

theorem find?_eq_some_id (bs : List ArrayBuffer) (bufId : Nat) (buf : ArrayBuffer)
    (h : bs.find? (fun b => b.id == bufId) = some buf) :
    buf.id = bufId := by
  have hp := List.find?_some h
  exact beq_iff_eq.mp hp

theorem find?_filter_self_none {α : Type} (xs : List α) (p : α → Bool) :
    (xs.filter (fun x => !p x)).find? p = none := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.filter]
    cases hp : p x <;> simp [hp, ih]

theorem find?_refCounts_filtered (refs : List (Bool × Nat × Nat)) (bufId : Nat) :
    (refs.filter (fun (isObj, id, _) => isObj || id != bufId)).find?
      (fun (isObj, id, _) => !isObj && id == bufId) = none := by
  have heq : (fun x : Bool × Nat × Nat => x.1 || x.2.1 != bufId) =
      (fun x : Bool × Nat × Nat => !(!x.1 && x.2.1 == bufId)) := by
    funext ⟨isObj, id, _⟩
    cases isObj <;> simp [bne]
  rw [heq]
  exact find?_filter_self_none refs (fun (isObj, id, _) => !isObj && id == bufId)

theorem getBufRefCount_pos (st : HeapState) (buf : ArrayBuffer) :
    1 ≤ st.getBufRefCount buf := by
  unfold HeapState.getBufRefCount
  cases buf.exclusive
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases st.refCounts.find? (fun (isObj, id, _) => !isObj && id == buf.id) with
    | none => simp
    | some entry =>
      rcases entry with ⟨_, _, rc⟩
      simp only [Nat.max_def]
      split <;> omega
  · simp

theorem incRefBuf_decRefBuf_one_roundtrip (st : HeapState) (bufId : Nat) (buf₀ : ArrayBuffer)
    (hfind : st.findBuffer bufId = some buf₀) :
    ∃ stPinned bufPinned,
      st.incRefBuf bufId 1 = .ok stPinned ∧
      stPinned.findBuffer bufId = some bufPinned ∧
      bufPinned = { buf₀ with exclusive := false } ∧
      stPinned.getBufRefCount bufPinned = st.getBufRefCount buf₀ + 1 ∧
      2 ≤ stPinned.getBufRefCount bufPinned ∧
      ∃ stFinal bufFinal,
        stPinned.decRefBuf bufId 1 = .ok stFinal ∧
        stFinal.findBuffer bufId = some bufFinal ∧
        bufFinal.data = buf₀.data ∧
        bufFinal.id = buf₀.id ∧
        stFinal.getBufRefCount bufFinal = st.getBufRefCount buf₀ ∧
        (st.getBufRefCount buf₀ = 1 → bufFinal.exclusive = true) := by
  have hid₀ : buf₀.id = bufId := find?_eq_some_id st.buffers bufId buf₀ hfind
  have hrcPos : 1 ≤ st.getBufRefCount buf₀ := getBufRefCount_pos st buf₀
  let rc₀ := st.getBufRefCount buf₀
  let refs' := st.refCounts.filter (fun (isObj, id, _) => isObj || id != bufId)
  let newRefs := if rc₀ + 1 ≤ 2 then refs' else (false, bufId, rc₀ + 1) :: refs'
  let stPinned : HeapState := { st with
    buffers := HeapState.setBufferExclusive st.buffers bufId false
    refCounts := newRefs }
  have hinc : st.incRefBuf bufId 1 = .ok stPinned := by
    unfold HeapState.incRefBuf
    simp [hfind, refs', newRefs, stPinned, rc₀]
  have hfindPinned : stPinned.findBuffer bufId = some { buf₀ with exclusive := false } := by
    unfold HeapState.findBuffer
    change (HeapState.setBufferExclusive st.buffers bufId false).find? _ = _
    rw [find?_setBufferExclusive, show st.buffers.find? (fun b => b.id == bufId) = some buf₀ from hfind]
    simp [hid₀]
  have hrcPinned : stPinned.getBufRefCount { buf₀ with exclusive := false } = rc₀ + 1 := by
    change
      (if false = true then 1
       else match stPinned.refCounts.find? (fun (isObj, id, _) => !isObj && id == buf₀.id) with
         | some (_, _, rc) => Nat.max 2 rc
         | none => 2) = rc₀ + 1
    simp only [stPinned, hid₀, Bool.false_eq_true, ↓reduceIte]
    by_cases hle2 : rc₀ + 1 ≤ 2
    · simp only [newRefs, hle2, ↓reduceIte]
      rw [find?_refCounts_filtered]
      dsimp only
      omega
    · simp only [newRefs, hle2, ↓reduceIte, List.find?]
      simp only [Bool.not_false, beq_self_eq_true, Bool.and_self]
      have hgt2 : 2 < rc₀ + 1 := by omega
      simp [Nat.max_eq_right (Nat.le_of_lt hgt2)]
  refine ⟨stPinned, { buf₀ with exclusive := false }, hinc, hfindPinned, rfl, hrcPinned, by omega, ?_⟩
  have hnotgt : ¬ (1 > rc₀ + 1) := by omega
  have hrcSub : rc₀ + 1 - 1 = rc₀ := by omega
  have hrefsIdem : newRefs.filter (fun (isObj, id, _) => isObj || id != bufId) = refs' := by
    by_cases hle2 : rc₀ + 1 ≤ 2
    · simp only [newRefs, hle2, ↓reduceIte, refs']
      rw [List.filter_filter]
      congr 1
      funext x
      simp
    · simp only [newRefs, hle2, ↓reduceIte, List.filter, refs']
      simp only [bne_self_eq_false, Bool.false_or]
      rw [List.filter_filter]
      congr 1
      funext x
      simp
  have hfindPList : stPinned.buffers.find? (fun b => b.id == bufId) =
      some { buf₀ with exclusive := false } := hfindPinned
  by_cases hrc1 : rc₀ = 1
  · let stFinal : HeapState := { stPinned with
      buffers := HeapState.setBufferExclusive stPinned.buffers bufId true
      refCounts := newRefs.filter (fun (isObj, id, _) => isObj || id != bufId) }
    have hdec : stPinned.decRefBuf bufId 1 = .ok stFinal := by
      unfold HeapState.decRefBuf
      rw [hfindPinned]
      simp only [Nat.one_ne_zero, beq_iff_eq, ↓reduceIte, hrcPinned, gt_iff_lt, hrc1]
      rfl
    have hfindFinal : stFinal.findBuffer bufId = some { buf₀ with exclusive := true } := by
      unfold HeapState.findBuffer
      change (HeapState.setBufferExclusive stPinned.buffers bufId true).find? _ = _
      rw [find?_setBufferExclusive, hfindPList]
      simp [hid₀]
    refine ⟨stFinal, { buf₀ with exclusive := true }, hdec, hfindFinal, rfl, rfl, ?_, fun _ => rfl⟩
    change (if true = true then 1 else _) = rc₀
    simp [hrc1]
  · by_cases hrc2 : rc₀ = 2
    · let stFinal : HeapState := { stPinned with
        buffers := HeapState.setBufferExclusive stPinned.buffers bufId false
        refCounts := newRefs.filter (fun (isObj, id, _) => isObj || id != bufId) }
      have hdec : stPinned.decRefBuf bufId 1 = .ok stFinal := by
        unfold HeapState.decRefBuf
        rw [hfindPinned]
        simp only [Nat.one_ne_zero, beq_iff_eq, ↓reduceIte, hrcPinned, gt_iff_lt, hrc2]
        rfl
      have hfindFinal : stFinal.findBuffer bufId = some { buf₀ with exclusive := false } := by
        unfold HeapState.findBuffer
        change (HeapState.setBufferExclusive stPinned.buffers bufId false).find? _ = _
        rw [find?_setBufferExclusive, hfindPList]
        simp [hid₀]
      refine ⟨stFinal, { buf₀ with exclusive := false }, hdec, hfindFinal, rfl, rfl, ?_, fun h1 => absurd h1 hrc1⟩
      change
        (if false = true then 1
         else match stFinal.refCounts.find? (fun (isObj, id, _) => !isObj && id == buf₀.id) with
           | some (_, _, rc) => Nat.max 2 rc
           | none => 2) = rc₀
      simp only [stFinal, hrefsIdem, hid₀, Bool.false_eq_true, ↓reduceIte]
      rw [find?_refCounts_filtered]
      dsimp only
      omega
    · let stFinal : HeapState := { stPinned with
        buffers := HeapState.setBufferExclusive stPinned.buffers bufId false
        refCounts := (false, bufId, rc₀) :: newRefs.filter (fun (isObj, id, _) => isObj || id != bufId) }
      have hdec : stPinned.decRefBuf bufId 1 = .ok stFinal := by
        unfold HeapState.decRefBuf
        rw [hfindPinned]
        simp only [Nat.one_ne_zero, beq_iff_eq, ↓reduceIte, hrcPinned, gt_iff_lt, hnotgt, hrcSub]
        simp [hrc1, hrc2, show rc₀ ≠ 0 by omega, stFinal, stPinned, hrefsIdem]
      have hfindFinal : stFinal.findBuffer bufId = some { buf₀ with exclusive := false } := by
        unfold HeapState.findBuffer
        change (HeapState.setBufferExclusive stPinned.buffers bufId false).find? _ = _
        rw [find?_setBufferExclusive, hfindPList]
        simp [hid₀]
      refine ⟨stFinal, { buf₀ with exclusive := false }, hdec, hfindFinal, rfl, rfl, ?_, fun h1 => absurd h1 hrc1⟩
      change
        (if false = true then 1
         else match stFinal.refCounts.find? (fun (isObj, id, _) => !isObj && id == buf₀.id) with
           | some (_, _, rc) => Nat.max 2 rc
           | none => 2) = rc₀
      simp only [stFinal, hid₀, Bool.false_eq_true, ↓reduceIte, List.find?,
        Bool.not_false, beq_self_eq_true, Bool.and_self]
      exact Nat.max_eq_right (by omega)

theorem transferModeCompatible_self (b : DeviceBufferDesc) :
    transferModeCompatible b.transferMode b = true := by
  unfold DeviceBufferDesc.transferMode transferModeCompatible
  cases b.zeroCopy <;> rfl

/-- Operational active-stream liveness: after `pinBufferStep`, the buffer remains live in `HeapState`
    with elevated reference count `rc₀ + 1 ≥ 2`, so both `launchKernelStep` and `syncDeviceStep` succeed
    without any premature host deallocation or unpinned access. -/
theorem execHybridTransferLifecycle_active_live (mode : TransferMode) (b : DeviceBufferDesc)
    (st : HeapState) (buf₀ : ArrayBuffer)
    (hg : bufferGeometryOk b = true)
    (hmode : transferModeCompatible mode b = true)
    (hfind : st.findBuffer b.bufId = some buf₀)
    (hmut : isMutableTransfer b.direction = true → st.getBufRefCount buf₀ = 1) :
    ∃ stPinned bufPinned,
      pinBufferStep mode b st = .ok stPinned ∧
      stPinned.findBuffer b.bufId = some bufPinned ∧
      stPinned.getBufRefCount bufPinned = st.getBufRefCount buf₀ + 1 ∧
      2 ≤ stPinned.getBufRefCount bufPinned ∧
      launchKernelStep mode b stPinned = .ok stPinned ∧
      syncDeviceStep mode b stPinned = .ok stPinned := by
  rcases incRefBuf_decRefBuf_one_roundtrip st b.bufId buf₀ hfind with
    ⟨stPinned, bufPinned, hinc, hfindP, _, hrcP, hge2, _⟩
  have hmutCheck : (isMutableTransfer b.direction && st.getBufRefCount buf₀ != 1) = false := by
    cases hm : isMutableTransfer b.direction
    · rfl
    · simp [hmut hm]
  have hpin : pinBufferStep mode b st = .ok stPinned := by
    unfold pinBufferStep
    simp [hg, hmode, hfind, hmutCheck, hinc]
  have hnotLt2 : ¬ (stPinned.getBufRefCount bufPinned < 2) := by omega
  have hlaunch : launchKernelStep mode b stPinned = .ok stPinned := by
    unfold launchKernelStep
    simp [hmode, hfindP, hnotLt2]
  have hsync : syncDeviceStep mode b stPinned = .ok stPinned := by
    unfold syncDeviceStep
    simp [hmode, hfindP, hnotLt2]
  exact ⟨stPinned, bufPinned, hpin, hfindP, hrcP, hge2, hlaunch, hsync⟩

/-- Operational RC preservation across `pin -> launch -> sync -> release`: `execHybridTransferLifecycle`
    succeeds and restores the exact initial `HeapState.getBufRefCount` and payload `data`. -/
theorem execHybridTransferLifecycle_preserves_rc (mode : TransferMode) (b : DeviceBufferDesc)
    (st : HeapState) (buf₀ : ArrayBuffer)
    (hg : bufferGeometryOk b = true)
    (hmode : transferModeCompatible mode b = true)
    (hfind : st.findBuffer b.bufId = some buf₀)
    (hmut : isMutableTransfer b.direction = true → st.getBufRefCount buf₀ = 1) :
    ∃ stFinal bufFinal,
      execHybridTransferLifecycle mode b st = .ok stFinal ∧
      stFinal.findBuffer b.bufId = some bufFinal ∧
      stFinal.getBufRefCount bufFinal = st.getBufRefCount buf₀ ∧
      bufFinal.data = buf₀.data ∧
      (st.getBufRefCount buf₀ = 1 → bufFinal.exclusive = true) := by
  rcases incRefBuf_decRefBuf_one_roundtrip st b.bufId buf₀ hfind with
    ⟨stPinned, bufPinned, hinc, hfindP, _, hrcP, hge2, stFinal, bufFinal, hdec, hfindF, hdataF, _, hrcF, hexclF⟩
  have hmutCheck : (isMutableTransfer b.direction && st.getBufRefCount buf₀ != 1) = false := by
    cases hm : isMutableTransfer b.direction
    · rfl
    · simp [hmut hm]
  have hpin : pinBufferStep mode b st = .ok stPinned := by
    unfold pinBufferStep
    simp [hg, hmode, hfind, hmutCheck, hinc]
  have hnotLt2 : ¬ (stPinned.getBufRefCount bufPinned < 2) := by omega
  have hlaunch : launchKernelStep mode b stPinned = .ok stPinned := by
    unfold launchKernelStep
    simp [hmode, hfindP, hnotLt2]
  have hsync : syncDeviceStep mode b stPinned = .ok stPinned := by
    unfold syncDeviceStep
    simp [hmode, hfindP, hnotLt2]
  have hrel : releaseBufferStep mode b stPinned = .ok stFinal := by
    unfold releaseBufferStep
    simp [hmode, hfindP, hnotLt2, hdec]
  have hexec : execHybridTransferLifecycle mode b st = .ok stFinal := by
    unfold execHybridTransferLifecycle
    simp [Bind.bind, Except.bind, hpin, hlaunch, hsync, hrel]
  exact ⟨stFinal, bufFinal, hexec, hfindF, hrcF, hdataF, hexclF⟩

/-- Operational exclusive-output guarantee: every mutable output (`.deviceToHost` or `.inOut`) admitted
    by `pinBufferStep` starts at `rc = 1` and exits `execHybridTransferLifecycle` uniquely owned (`rc = 1`, `exclusive = true`). -/
theorem execHybridTransferLifecycle_exclusive_out (mode : TransferMode) (b : DeviceBufferDesc)
    (st stFinal : HeapState)
    (hmut : isMutableTransfer b.direction = true)
    (hexec : execHybridTransferLifecycle mode b st = .ok stFinal) :
    ∃ buf₀ bufFinal,
      st.findBuffer b.bufId = some buf₀ ∧
      st.getBufRefCount buf₀ = 1 ∧
      stFinal.findBuffer b.bufId = some bufFinal ∧
      stFinal.getBufRefCount bufFinal = 1 ∧
      bufFinal.exclusive = true := by
  have hexecCopy := hexec
  unfold execHybridTransferLifecycle at hexecCopy
  simp only [Bind.bind, Except.bind] at hexecCopy
  cases hpin : pinBufferStep mode b st with
  | error e => simp [hpin] at hexecCopy
  | ok stPinned =>
    unfold pinBufferStep at hpin
    by_cases hg : bufferGeometryOk b = true
    · by_cases hm : transferModeCompatible mode b = true
      · cases hfind : st.findBuffer b.bufId with
        | none => simp [hg, hm, hfind] at hpin
        | some buf₀ =>
          by_cases hrc1 : st.getBufRefCount buf₀ = 1
          · rcases execHybridTransferLifecycle_preserves_rc mode b st buf₀ hg hm hfind (fun _ => hrc1) with
              ⟨stFinal', bufFinal, hexec', hfindF, hrcF, _, hexclF⟩
            rw [hexec'] at hexec
            injection hexec with hEq
            subst hEq
            exact ⟨buf₀, bufFinal, rfl, hrc1, hfindF, by rw [hrcF, hrc1], hexclF hrc1⟩
          · simp [hg, hm, hfind, hmut, hrc1] at hpin
      · simp [hg, hm] at hpin
    · simp [hg] at hpin

/-- `b.ownershipOk` implies operational `rcConserved b` across `HeapState` for `b.transferMode`. -/
theorem ownershipOk_implies_rcConserved (b : DeviceBufferDesc) (ho : b.ownershipOk) :
    rcConserved b := by
  intro hg st buf₀ hfind hrcEq
  have hmut : isMutableTransfer b.direction = true → st.getBufRefCount buf₀ = 1 := by
    intro hm
    unfold DeviceBufferDesc.ownershipOk at ho
    cases hd : b.direction <;> simp [hd, isMutableTransfer] at hm ho
    · omega
    · omega
  have hmutRc1 : isMutableTransfer b.direction = true → b.rc = 1 := by
    intro hm
    have := hmut hm
    omega
  have hmode : transferModeCompatible b.transferMode b = true := transferModeCompatible_self b
  rcases execHybridTransferLifecycle_active_live b.transferMode b st buf₀ hg hmode hfind hmut with
    ⟨stPinned, bufPinned, hpin, hfindP, hrcP, hge2, _, _⟩
  rcases execHybridTransferLifecycle_preserves_rc b.transferMode b st buf₀ hg hmode hfind hmut with
    ⟨stFinal, bufFinal, hexec, hfindF, hrcF, hdataF, hexclF⟩
  refine ⟨stPinned, stFinal, bufPinned, bufFinal, hpin, hexec, hfindP, hfindF, ?_, hge2, ?_, hdataF, ?_⟩
  · omega
  · omega
  · intro hm
    have hb1 : b.rc = 1 := hmutRc1 hm
    exact ⟨hexclF (by omega), hb1⟩

theorem buffersOwned_implies_rcConserved (target : ComputeTarget) (buffers : List DeviceBufferDesc)
    (ho : buffersOwned target buffers) :
    ∀ b ∈ buffers, rcConserved b := by
  induction buffers with
  | nil => intro b hb; cases hb
  | cons a rest ih =>
    rcases ho with ⟨_, haOwn, hrest⟩
    intro b hb
    simp at hb
    rcases hb with rfl | hbRest
    · exact ownershipOk_implies_rcConserved b haOwn
    · exact ih hrest b hbRest

/-- Global thread ID decomposition: every `(block, lane)` in bounds maps below `gridThreadsOf req`
    and is uniquely recoverable via quotient and remainder (`globalThreadId` bijection). -/
theorem globalThreadId_bijection (req : HybridLaunchRequest)
    (hgeom : validLaunchGeometry req) :
    (∀ block lane, block < req.gridDim.volume → lane < req.blockDim.volume →
      globalThreadId req block lane < gridThreadsOf req) ∧
    (∀ b1 l1 b2 l2,
      l1 < req.blockDim.volume → l2 < req.blockDim.volume →
      globalThreadId req b1 l1 = globalThreadId req b2 l2 →
      b1 = b2 ∧ l1 = l2) ∧
    (∀ gid, gid < gridThreadsOf req →
      ∃ block lane, block < req.gridDim.volume ∧ lane < req.blockDim.volume ∧
        globalThreadId req block lane = gid) := by
  rcases hgeom with ⟨_, ⟨bx, by_, bz⟩, _, _⟩
  have hbvol : 0 < req.blockDim.volume := by
    unfold Dim3.volume
    exact Nat.mul_pos (Nat.mul_pos (Nat.pos_of_ne_zero bx) (Nat.pos_of_ne_zero by_)) (Nat.pos_of_ne_zero bz)
  refine ⟨?_, ?_, ?_⟩
  · intro block lane hblk hlane
    unfold globalThreadId gridThreadsOf
    have hblk1 : block + 1 ≤ req.gridDim.volume := hblk
    have hmul : (block + 1) * req.blockDim.volume ≤ req.gridDim.volume * req.blockDim.volume :=
      Nat.mul_le_mul_right req.blockDim.volume hblk1
    have hexpand : (block + 1) * req.blockDim.volume = block * req.blockDim.volume + req.blockDim.volume :=
      Nat.succ_mul block req.blockDim.volume
    omega
  · intro b1 l1 b2 l2 hl1 hl2 heq
    unfold globalThreadId at heq
    have hdiv1 : (b1 * req.blockDim.volume + l1) / req.blockDim.volume = b1 := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hbvol, Nat.div_eq_of_lt hl1, Nat.zero_add]
    have hdiv2 : (b2 * req.blockDim.volume + l2) / req.blockDim.volume = b2 := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hbvol, Nat.div_eq_of_lt hl2, Nat.zero_add]
    have hbEq : b1 = b2 := by
      calc b1 = (b1 * req.blockDim.volume + l1) / req.blockDim.volume := hdiv1.symm
        _ = (b2 * req.blockDim.volume + l2) / req.blockDim.volume := by rw [heq]
        _ = b2 := hdiv2
    subst hbEq
    exact ⟨rfl, by omega⟩
  · intro gid hgid
    unfold gridThreadsOf at hgid
    refine ⟨gid / req.blockDim.volume, gid % req.blockDim.volume, ?_, Nat.mod_lt gid hbvol, ?_⟩
    · exact (Nat.div_lt_iff_lt_mul hbvol).mpr hgid
    · unfold globalThreadId
      have heucl := Nat.div_add_mod gid req.blockDim.volume
      have hcomm : req.blockDim.volume * (gid / req.blockDim.volume) =
          (gid / req.blockDim.volume) * req.blockDim.volume := Nat.mul_comm _ _
      omega

/-- `validateHybridDispatch req = .ok plan` implies valid launch geometry, target-aware buffer
    geometry (including `16384`-byte page alignment on `.gpuMetal` zero-copy), RC ownership,
    strict pairwise buffer disjointness across distinct slots unless both are read-only,
    tail-guarded global thread ID coverage for all `gid < workloadElems`, and operational
    `HeapState` RC lifecycle conservation (`pin -> launch -> sync -> release`). -/
theorem validateHybridDispatch_sound (req : HybridLaunchRequest) (plan : HybridDispatchPlan)
    (h : validateHybridDispatch req = .ok plan) :
    hybridDispatchSound req plan := by
  unfold validateHybridDispatch at h
  cases hlg : launchGeometryOk req
  · simp [hlg] at h
    split at h <;> try cases h
    split at h <;> cases h
  · simp [hlg] at h
    by_cases hbg : ∃ x ∈ req.buffers, targetBufferGeometryOk req.target x = false
    · simp [hbg] at h
    · simp [hbg] at h
      by_cases hbo : ∃ x ∈ req.buffers, bufferOwnershipOk x = false
      · simp [hbo] at h
      · simp [hbo] at h
        cases hba : bufferAliasOk req.buffers
        · simp [hba] at h
        · simp [hba] at h
          subst h
          have hgeom : validLaunchGeometry req := launchGeometryOk_sound req hlg
          have hgAll : ∀ b ∈ req.buffers, targetBufferGeometryOk req.target b = true := by
            intro b hb
            cases hgb : targetBufferGeometryOk req.target b
            · exact absurd ⟨b, hb, hgb⟩ hbg
            · rfl
          have hoAll : ∀ b ∈ req.buffers, bufferOwnershipOk b = true := by
            intro b hb
            cases hob : bufferOwnershipOk b
            · exact absurd ⟨b, hb, hob⟩ hbo
            · rfl
          have howned : buffersOwned req.target req.buffers :=
            buffersOwned_of_all req.target req.buffers hgAll hoAll
          have hdisj : buffersDisjoint req.buffers := bufferAliasOk_sound req.buffers hba
          rcases globalThreadId_bijection req hgeom with ⟨hbound, _, hsurj⟩
          have htailLe : req.tailGuarded → req.workloadElems ≤ gridThreadsOf req := by
            intro ht
            rcases hgeom with ⟨_, _, _, hcov⟩
            rcases hcov with ⟨_, hle⟩ | ⟨hnot, _⟩
            · exact hle
            · exact absurd ht hnot
          refine ⟨hgeom, howned, hdisj, rfl, rfl, rfl, rfl, htailLe, ?_, hbound,
            buffersOwned_implies_rcConserved req.target req.buffers howned⟩
          intro gid ht hgid
          have hltGrid : gid < gridThreadsOf req := Nat.lt_of_lt_of_le hgid (htailLe ht)
          exact hsurj gid hltGrid

end LeanNative.Proofs.HybridCAbi
