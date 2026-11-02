import LeanNative.Driver.CAbiEmit
import LeanNative.Backend.Hybrid

namespace LeanNative.Proofs.HybridCAbi

open LeanNative.Driver.CoreCLI
open LeanNative.Backend.Hybrid

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

theorem c99Scalar_align_pos (ty : C99ScalarType) : ty.alignOf ≠ 0 := by
  cases ty <;> decide

theorem c99Scalar_size_pos (ty : C99ScalarType) : 0 < ty.sizeOf := by
  cases ty <;> decide

theorem c99NatMax_ge (a b : Nat) : a ≤ c99NatMax a b ∧ b ≤ c99NatMax a b := by
  unfold c99NatMax
  split <;> omega

theorem placeC99Field_spec (off : Nat) (spec : C99FieldSpec) (f : C99FieldLayout) (nextOff : Nat)
    (h : placeC99Field off spec = some (f, nextOff)) :
    f.isAligned ∧ f.size = f.ty.sizeOf ∧ f.align = f.ty.alignOf ∧
    off ≤ f.offset ∧ f.offset < f.byteEnd ∧ nextOff = f.byteEnd := by
  unfold placeC99Field at h
  cases hal : c99AlignUp off spec.ty.alignOf with
  | none => simp [hal] at h
  | some aligned =>
    simp [hal] at h
    obtain ⟨rfl, rfl⟩ := h
    rcases c99AlignUp_spec off spec.ty.alignOf aligned hal with ⟨ha, hdvd, hle⟩
    have hsz : 0 < spec.ty.sizeOf := c99Scalar_size_pos spec.ty
    refine ⟨⟨ha, Nat.mod_eq_zero_of_dvd hdvd⟩, rfl, rfl, hle, ?_, rfl⟩
    unfold C99FieldLayout.byteEnd
    simp
    omega

theorem placeC99FieldsFrom_spec (specs : List C99FieldSpec) (off maxA : Nat)
    (placed : List C99FieldLayout) (finalAlign : Nat)
    (hmax : maxA ≠ 0)
    (h : placeC99FieldsFrom specs off maxA = some (placed, finalAlign)) :
    finalAlign ≠ 0 ∧ maxA ≤ finalAlign ∧
    (∀ f ∈ placed, f.isAligned ∧ f.size = f.ty.sizeOf ∧ f.align = f.ty.alignOf ∧ off ≤ f.offset) ∧
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
    cases hp : placeC99Field off spec with
    | none => simp [hp] at h
    | some fn =>
      rcases fn with ⟨field, nextOff⟩
      simp [hp] at h
      cases hrest : placeC99FieldsFrom rs nextOff (c99NatMax maxA field.align) with
      | none => simp [hrest] at h
      | some rf =>
        rcases rf with ⟨restFields, fa⟩
        simp [hrest] at h
        obtain ⟨rfl, rfl⟩ := h
        rcases placeC99Field_spec off spec field nextOff hp with
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

/-- Theorem group 1: Every `computeC99StructLayout` output satisfies natural field alignment
    (`f.align ∣ f.offset`), pairwise disjoint half-open field intervals `[offset, offset + size)`,
    `structSize` covering all fields, and `structAlign ∣ structSize` with `structAlign ≠ 0`. -/
theorem computeC99StructLayout_sound (name : String) (specs : List C99FieldSpec) (layout : C99StructLayout)
    (h : computeC99StructLayout name specs = some layout) :
    c99LayoutSound layout := by
  unfold computeC99StructLayout placeC99Fields at h
  cases hp : placeC99FieldsFrom specs 0 1 with
  | none => simp [hp] at h
  | some pm =>
    rcases pm with ⟨placed, maxAlign⟩
    simp [hp] at h
    cases hsz : c99AlignUp (c99OccupiedEnd placed) maxAlign with
    | none => simp [hsz] at h
    | some sz =>
      simp [hsz] at h
      subst h
      rcases placeC99FieldsFrom_spec specs 0 1 placed maxAlign (by decide) hp with
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
    (layout : C99StructLayout) (f : C99FieldLayout)
    (h : computeC99StructLayout name specs = some layout) (hf : f ∈ layout.fields) :
    f.align ≠ 0 ∧ f.align ∣ f.offset := by
  rcases computeC99StructLayout_sound name specs layout h with ⟨_, _, hall, _, _⟩
  rcases (hall f hf).1 with ⟨ha, hmod⟩
  exact ⟨ha, Nat.dvd_of_mod_eq_zero hmod⟩

/-- Theorem group 2a: `checkedByteLen len elemBytes = some total` guarantees exact product and no 64-bit unsigned overflow. -/
theorem checkedByteLen_no_overflow (len elemBytes total : Nat)
    (h : checkedByteLen len elemBytes = some total) :
    len * elemBytes = total ∧ total < 2 ^ 64 := by
  unfold checkedByteLen at h
  by_cases he : elemBytes = 0
  · simp [he] at h
    subst h
    simp [he]
  · simp [he] at h
    by_cases hlen : len ≤ (2 ^ 64 - 1) / elemBytes
    · simp [hlen] at h
      subst h
      refine ⟨rfl, ?_⟩
      have hmul : len * elemBytes ≤ ((2 ^ 64 - 1) / elemBytes) * elemBytes :=
        Nat.mul_le_mul_right elemBytes hlen
      have hbound : ((2 ^ 64 - 1) / elemBytes) * elemBytes ≤ 2 ^ 64 - 1 :=
        Nat.div_mul_le_self (2 ^ 64 - 1) elemBytes
      omega
    · simp [hlen] at h

/-- Theorem group 2b: Valid `ByteArray` slice marshaling succeeds and `unmarshalSlice` round-trips identically. -/
theorem marshal_unmarshal_byte_slice_roundtrip (v : C99ByteView)
    (hv : v.isValid) :
    ∃ payload,
      marshalSlice v = some payload ∧
      payload.size = v.len * v.elemSize ∧
      unmarshalSlice v.bytes v.base payload = some v.bytes := by
  rcases hv with ⟨_, hchecked, hbound⟩
  refine ⟨v.bytes.extract v.base (v.base + v.len * v.elemSize), ?_, ?_, ?_⟩
  · unfold marshalSlice
    simp [hchecked, hbound]
  · rw [ByteArray.size_extract]
    omega
  · unfold unmarshalSlice
    have hsize : (v.bytes.extract v.base (v.base + v.len * v.elemSize)).size = v.len * v.elemSize := by
      rw [ByteArray.size_extract]
      omega
    have hcond : v.base + (v.bytes.extract v.base (v.base + v.len * v.elemSize)).size ≤ v.bytes.size := by omega
    rw [ite_cond_eq_true _ _ (eq_true hcond)]
    congr 1
    apply ByteArray.ext
    rw [ByteArray.data_append, ByteArray.data_append, ByteArray.data_extract,
      ByteArray.data_extract, ByteArray.data_extract, hsize]
    have hbsz : v.bytes.size = v.bytes.data.size := rfl
    have h1 :
        v.bytes.data.extract 0 v.base ++
          v.bytes.data.extract v.base (v.base + v.len * v.elemSize) =
        v.bytes.data.extract 0 (v.base + v.len * v.elemSize) := by
      rw [Array.extract_append_extract]
      have hmin : min 0 v.base = 0 := by omega
      have hmax : max v.base (v.base + v.len * v.elemSize) = v.base + v.len * v.elemSize := by omega
      rw [hmin, hmax]
    rw [h1, Array.extract_append_extract]
    have hmin2 : min 0 (v.base + v.len * v.elemSize) = 0 := by omega
    have hmax2 : max (v.base + v.len * v.elemSize) v.bytes.data.size = v.bytes.data.size := by omega
    rw [hbsz, hmin2, hmax2]
    simp

/-- Theorem group 2c: Valid `FloatArray` (`double*`) slice marshaling succeeds and `unmarshalFloatSlice` round-trips identically. -/
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
    rw [ite_cond_eq_true _ _ (eq_true hcond)]
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

/-- Theorem group 2d: `validateC99Slice s = true` implies `validC99Slice s`
    (non-zero align/elemSize, aligned stride, non-null non-empty pointer, non-overflowing 64-bit byte size). -/
theorem validateC99Slice_sound (s : C99SliceDesc) (h : validateC99Slice s = true) :
    validC99Slice s := by
  unfold validateC99Slice at h
  simp [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

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
  unfold bufferGeometryOk DeviceBufferDesc.geometryOk at *
  simp [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem bufferOwnershipOk_sound (b : DeviceBufferDesc) (h : bufferOwnershipOk b = true) :
    b.ownershipOk := by
  unfold bufferOwnershipOk DeviceBufferDesc.ownershipOk at *
  cases hd : b.direction <;> simp [hd, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at h ⊢
  · exact ⟨Nat.pos_of_ne_zero h.1, h.2⟩
  · exact h
  · exact h

theorem buffersOwned_of_all (buffers : List DeviceBufferDesc)
    (hg : ∀ b ∈ buffers, bufferGeometryOk b = true)
    (ho : ∀ b ∈ buffers, bufferOwnershipOk b = true) :
    buffersOwned buffers := by
  induction buffers with
  | nil => trivial
  | cons b rest ih =>
    refine ⟨bufferGeometryOk_sound b (hg b (by simp)),
      bufferOwnershipOk_sound b (ho b (by simp)),
      ih (fun x hx => hg x (by simp [hx])) (fun x hx => ho x (by simp [hx]))⟩

theorem bufferAliasPairOk_sound (a b : DeviceBufferDesc) (h : bufferAliasPairOk a b = true) :
    disjointBuffers a b := by
  unfold bufferAliasPairOk disjointBuffers addressIntervalsDisjoint DeviceBufferDesc.addressEnd at *
  simp [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨hn, ha⟩, hb⟩ | hrest
  · exact Or.inl ⟨hn, ha, hb⟩
  · rcases hrest with (h1 | h2) | hro
    · exact Or.inr (Or.inl (Or.inl h1))
    · exact Or.inr (Or.inl (Or.inr h2))
    · exact Or.inr (Or.inr hro)

theorem bufferAliasOk_sound (buffers : List DeviceBufferDesc) (h : bufferAliasOk buffers = true) :
    buffersDisjoint buffers := by
  induction buffers with
  | nil => trivial
  | cons a rest ih =>
    unfold bufferAliasOk at h
    simp [Bool.and_eq_true, List.all_eq_true] at h
    rcases h with ⟨hpair, hrest⟩
    exact ⟨fun b hb => bufferAliasPairOk_sound a b (hpair b hb), ih hrest⟩

/-- Theorem group 3b: Lean RC conservation across `pin -> launch -> sync -> release` for every valid buffer. -/
theorem ownershipOk_implies_rcConserved (b : DeviceBufferDesc) (ho : b.ownershipOk) :
    rcConserved b := by
  unfold DeviceBufferDesc.ownershipOk at ho
  unfold rcConserved rcPhaseOf rcNetDelta
  cases hd : b.direction <;> simp [hd] at ho
  · rcases ho with ⟨hrc, hown⟩
    rcases hown with hown | hown <;> simp [hown] <;> omega
  · rcases ho with ⟨hrc, hown⟩
    simp [hown, hrc]
  · rcases ho with ⟨hrc, hown⟩
    simp [hown, hrc]

theorem buffersOwned_implies_rcConserved (buffers : List DeviceBufferDesc)
    (ho : buffersOwned buffers) :
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
    and is uniquely recoverable via quotient and remainder (`globalThreadId` injective). -/
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

/-- Theorem group 3a: `validateHybridDispatch req = .ok plan` implies valid launch geometry,
    buffer geometry & RC ownership, pairwise disjoint buffers (unless `InOut` or dual read-only),
    tail-guarded global thread ID coverage for all `gid < workloadElems`, and RC lifecycle conservation. -/
theorem validateHybridDispatch_sound (req : HybridLaunchRequest) (plan : HybridDispatchPlan)
    (h : validateHybridDispatch req = .ok plan) :
    hybridDispatchSound req plan := by
  unfold validateHybridDispatch at h
  cases hlg : launchGeometryOk req
  · simp [hlg] at h
    split at h <;> try cases h
    split at h <;> cases h
  · simp [hlg] at h
    by_cases hbg : ∃ x ∈ req.buffers, bufferGeometryOk x = false
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
          have hgAll : ∀ b ∈ req.buffers, bufferGeometryOk b = true := by
            intro b hb
            cases hgb : bufferGeometryOk b
            · exact absurd ⟨b, hb, hgb⟩ hbg
            · rfl
          have hoAll : ∀ b ∈ req.buffers, bufferOwnershipOk b = true := by
            intro b hb
            cases hob : bufferOwnershipOk b
            · exact absurd ⟨b, hb, hob⟩ hbo
            · rfl
          have howned : buffersOwned req.buffers := buffersOwned_of_all req.buffers hgAll hoAll
          have hdisj : buffersDisjoint req.buffers := bufferAliasOk_sound req.buffers hba
          rcases globalThreadId_bijection req hgeom with ⟨hbound, _, hsurj⟩
          have htailLe : req.tailGuarded → req.workloadElems ≤ gridThreadsOf req := by
            intro ht
            rcases hgeom with ⟨_, _, _, hcov⟩
            rcases hcov with ⟨_, hle⟩ | ⟨hnot, _⟩
            · exact hle
            · exact absurd ht hnot
          refine ⟨hgeom, howned, hdisj, rfl, rfl, rfl, htailLe, ?_, hbound,
            buffersOwned_implies_rcConserved req.buffers howned⟩
          intro gid ht hgid
          have hltGrid : gid < gridThreadsOf req := Nat.lt_of_lt_of_le hgid (htailLe ht)
          exact hsurj gid hltGrid

end LeanNative.Proofs.HybridCAbi
