import Lean
import LeanNative.Semantics.Value

namespace LeanNative.Proofs.HeapObjAbi

open LeanNative.Semantics

/-!
# Formal `lean.h` `HeapObj` ABI Layout, Boxing & RC Preservation (`HeapObjAbiProofs.lean`)

Track C6 machine-checked proofs (`0 sorryAx`, standard kernel axioms only — zero `ofReduceBool`,
`ofReduceNat`, or `trustCompiler`) covering the three core `include/lean/lean.h` ABI invariants:

1. **Tagged Immediate Boxing (`lean_box` / `lean_unbox` / `lean_is_scalar`)**:
   - Exact 63-bit round-trip `leanUnbox (leanBox n) = n ↔ n.toNat < 2 ^ 63`.
   - Tag-bit discrimination: `leanIsScalar (leanBox n) = true`, while every 8-byte aligned heap
     pointer (`addr.toNat % 8 = 0`, including `null = 0`) satisfies `leanIsScalar addr = false`,
     so boxed immediates and aligned heap pointers are disjoint (`leanBox n ≠ addr`).

2. **`lean_object` 8-Byte Header Packing & `lean_ctor_object` Payload Offsets**:
   - Bijective packing/unpacking of the 64-bit little-endian `lean_object` header
     (`m_rc : i32` at `[0..4)`, `m_cs_sz : u16` at `[4..6)`, `m_other : u8` at `[6..7)`,
     `m_tag : u8` at `[7..8)`), plus bit-slice isolation when updating `m_rc` or `m_tag`.
   - Pairwise byte-span disjointness across all four header fields, object pointer slots
     (`8 + 8 * idx`), and scalar payload bytes (`8 + 8 * numObjs + scalar_offset`).

3. **Reference Counting (`m_rc`) Preservation (Persistent, Unique Reset/Reuse/Set, Shared COW)**:
   - Persistent objects (`m_rc == 0`) are invariant under `stepIncRefHeader` and never deallocate
     under `stepDecRefHeader`; unique (`m_rc == 1`) `dec_ref` triggers deallocation while shared
     (`m_rc >_s 1`) `dec_ref` decrements without freeing.
   - Over `LeanNative.Semantics.HeapState`, Perceus / `lean.h` `cowWriteField` (in-place
     `writeHeapObjFieldExclusive` when `rc = 1`, copy-on-write clone + `rc - 1` when `rc ≥ 2`)
     produces the exact same constructor payload as `pureCloneWriteField` while preserving every
     live external alias under the RC uniqueness invariant `(rc = 1 → aliasId ≠ objId)`.
-/

/-! ## 1. `lean_box` / `lean_unbox` 63-Bit Immediate ABI & Alignment Disjointness -/

/-- `lean_box(n)` in `include/lean/lean.h`: `((size_t)(n) << 1) | 1`. -/
def leanBox (n : BitVec 64) : BitVec 64 :=
  (n <<< 1) ||| 1#64

/-- `lean_unbox(o)` in `include/lean/lean.h`: `(size_t)(o) >> 1`. -/
def leanUnbox (o : BitVec 64) : BitVec 64 :=
  o >>> 1

/-- `lean_is_scalar(o)` in `include/lean/lean.h`: `((size_t)(o) & 1) == 1`. -/
def leanIsScalar (o : BitVec 64) : Bool :=
  (o &&& 1#64) == 1#64

private theorem one64_getLsbD_pos (k : Nat) (hk : 1 ≤ k) :
    (1#64).getLsbD k = false := by
  have h1 : (1#64) = (1#1).setWidth 64 := rfl
  rw [h1, BitVec.getLsbD_setWidth]
  simp [BitVec.getLsbD_of_ge (1#1) k hk]

/-- Exact 63-bit round-trip: `lean_unbox(lean_box(n)) = n` for every `n < 2^63` (`LEAN_MAX_SMALL_NAT + 1`). -/
theorem unbox_box_id (n : BitVec 64) (h : n.toNat < 2 ^ 63) :
    leanUnbox (leanBox n) = n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold leanUnbox leanBox
  rw [BitVec.getLsbD_ushiftRight]
  by_cases hi63 : i < 63
  · have hi1 : 1 + i < 64 := by omega
    have hnot_lt : ¬(1 + i < 1) := by omega
    have hsub : 1 + i - 1 = i := by omega
    have h1_false : (1#64).getLsbD (1 + i) = false := one64_getLsbD_pos (1 + i) (by omega)
    simp only [hi, decide_true, Bool.true_and, BitVec.getLsbD_or, h1_false, Bool.or_false,
      BitVec.getLsbD_shiftLeft, hi1, hnot_lt, decide_false, Bool.not_false, hsub]
  · have hi_eq : i = 63 := by omega
    subst hi_eq
    have hlhs : (((n <<< 1) ||| 1#64).getLsbD (1 + 63)) = false :=
      BitVec.getLsbD_of_ge _ 64 (by omega)
    have hrhs : n.getLsbD 63 = false := by
      have hshr : (n >>> 63).toNat = 0 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        omega
      have hshr0 : n >>> 63 = 0#64 := BitVec.eq_of_toNat_eq hshr
      have hb0 := congrArg (fun x => x.getLsbD 0) hshr0
      rw [BitVec.getLsbD_ushiftRight] at hb0
      exact hb0
    simp only [hi, decide_true, Bool.true_and, hlhs, hrhs]

/-- Above `2^63`, `lean_box` truncates bit 63, so `lean_unbox(lean_box(n))` strictly loses information. -/
theorem unbox_box_ne_of_ge (n : BitVec 64) (h : 2 ^ 63 ≤ n.toNat) :
    leanUnbox (leanBox n) ≠ n := by
  intro heq
  have hlt := (leanBox n).isLt
  have hunbox : (leanUnbox (leanBox n)).toNat = (leanBox n).toNat / 2 := by
    unfold leanUnbox
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have heq_nat : (leanUnbox (leanBox n)).toNat = n.toNat := congrArg BitVec.toNat heq
  omega

/-- Necessary and sufficient 63-bit round-trip characterization of `lean_box` / `lean_unbox`. -/
theorem unbox_box_eq_iff (n : BitVec 64) :
    leanUnbox (leanBox n) = n ↔ n.toNat < 2 ^ 63 := by
  constructor
  · intro heq
    by_cases hlt : n.toNat < 2 ^ 63
    · exact hlt
    · exfalso
      exact unbox_box_ne_of_ge n (Nat.le_of_not_lt hlt) heq
  · exact unbox_box_id n

/-- Every `lean_box(n)` immediate sets bit 0, so `lean_is_scalar` evaluates to `true`. -/
theorem is_scalar_box_true (n : BitVec 64) :
    leanIsScalar (leanBox n) = true := by
  unfold leanIsScalar leanBox
  suffices h : (((n <<< 1) ||| 1#64) &&& 1#64) = 1#64 by
    rw [h]
    rfl
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_or]
  by_cases h0 : i = 0
  · subst h0
    simp
  · have h1 : (1#64).getLsbD i = false := one64_getLsbD_pos i (by omega)
    simp only [h1, Bool.and_false]

/-- Every 8-byte aligned heap address (`addr % 8 = 0`, including `null = 0`) has LSB `0`,
    so `lean_is_scalar` evaluates to `false`. -/
theorem is_scalar_aligned_ptr_false (addr : BitVec 64) (h_align : addr.toNat % 8 = 0) :
    leanIsScalar addr = false := by
  unfold leanIsScalar
  suffices h : (addr &&& 1#64) = 0#64 by
    rw [h]
    rfl
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change (addr.toNat &&& 1) = 0
  rw [Nat.and_one_is_mod]
  omega

/-- Tagged immediates (`lean_box(n)`) and 8-byte aligned heap pointers are strictly disjoint. -/
theorem box_ne_aligned_ptr (n addr : BitVec 64) (h_align : addr.toNat % 8 = 0) :
    leanBox n ≠ addr := by
  intro heq
  have h1 := is_scalar_box_true n
  have h2 := is_scalar_aligned_ptr_false addr h_align
  rw [heq] at h1
  rw [h1] at h2
  contradiction

/-! ## 2. `lean_object` 8-Byte Header Packing & `lean_ctor_object` Payload Offsets -/

/-- Exact 8-byte `lean_object` header (`include/lean/lean.h`, 64-bit little-endian):
    - `rc`    (`m_rc`, `int32_t`)   at bytes `[0, 4)`, bits `[0, 32)`
    - `csSz`  (`m_cs_sz`, `uint16_t`) at bytes `[4, 6)`, bits `[32, 48)`
    - `other` (`m_other`, `uint8_t`, `num_objs` on ctors) at bytes `[6, 7)`, bits `[48, 56)`
    - `tag`   (`m_tag`, `uint8_t`)  at bytes `[7, 8)`, bits `[56, 64)` -/
structure LeanObjectHeader where
  rc    : BitVec 32
  csSz  : BitVec 16
  other : BitVec 8
  tag   : BitVec 8
  deriving Repr, DecidableEq, Inhabited

/-- Pack `LeanObjectHeader` into its 64-bit little-endian header word (`tag ++ other ++ csSz ++ rc`). -/
def packHeader (h : LeanObjectHeader) : BitVec 64 :=
  (h.tag.setWidth 64 <<< 56) |||
  (h.other.setWidth 64 <<< 48) |||
  (h.csSz.setWidth 64 <<< 32) |||
  h.rc.setWidth 64

/-- Unpack a 64-bit little-endian `lean_object` header word into its four constituent fields. -/
def unpackHeader (w : BitVec 64) : LeanObjectHeader :=
  { rc    := w.extractLsb' 0 32
    csSz  := w.extractLsb' 32 16
    other := w.extractLsb' 48 8
    tag   := w.extractLsb' 56 8 }

private theorem getLsbD_zeroExtend_shiftLeft_64 {w : Nat} (x : BitVec w) (sh i : Nat) (hi : i < 64) :
    ((x.setWidth 64) <<< sh).getLsbD i =
      if sh ≤ i ∧ i < sh + w then x.getLsbD (i - sh) else false := by
  rw [BitVec.getLsbD_shiftLeft]
  simp only [hi, decide_true, Bool.true_and]
  by_cases hle : sh ≤ i
  · have hnot : ¬(i < sh) := Nat.not_lt.mpr hle
    simp only [hnot, decide_false, Bool.not_false, Bool.true_and, BitVec.getLsbD_setWidth,
      Nat.sub_lt_of_lt hi, decide_true, hle, true_and]
    by_cases hlt : i < sh + w
    · have hsub : i - sh < w := by omega
      simp [hlt]
    · have hge : w ≤ i - sh := by omega
      simp [hlt, BitVec.getLsbD_of_ge x (i - sh) hge]
  · have hlt : i < sh := Nat.lt_of_not_ge hle
    simp [hle, hlt]

private theorem getLsbD_setWidth_64 {w : Nat} (x : BitVec w) (i : Nat) (hi : i < 64) :
    (x.setWidth 64).getLsbD i = x.getLsbD i := by
  rw [BitVec.getLsbD_setWidth]
  simp [hi]

private theorem getLsbD_extractLsb'_of_lt {w : Nat} (x : BitVec w) (start len i : Nat) (hi : i < len) :
    (x.extractLsb' start len).getLsbD i = x.getLsbD (start + i) := by
  rw [BitVec.getLsbD_extractLsb']
  simp [hi]

theorem packHeader_rc_eq (h : LeanObjectHeader) :
    (packHeader h).extractLsb' 0 32 = h.rc := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi64 : i < 64 := by omega
  rw [getLsbD_extractLsb'_of_lt _ _ _ _ hi]
  simp only [Nat.zero_add, packHeader, BitVec.getLsbD_or,
    getLsbD_zeroExtend_shiftLeft_64 _ _ _ hi64, getLsbD_setWidth_64 _ _ hi64]
  have h1 : ¬(56 ≤ i ∧ i < 56 + 8) := by omega
  have h2 : ¬(48 ≤ i ∧ i < 48 + 8) := by omega
  have h3 : ¬(32 ≤ i ∧ i < 32 + 16) := by omega
  rw [if_neg h1, if_neg h2, if_neg h3]
  simp

theorem packHeader_csSz_eq (h : LeanObjectHeader) :
    (packHeader h).extractLsb' 32 16 = h.csSz := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi64 : 32 + i < 64 := by omega
  rw [getLsbD_extractLsb'_of_lt _ _ _ _ hi]
  simp only [packHeader, BitVec.getLsbD_or,
    getLsbD_zeroExtend_shiftLeft_64 _ _ _ hi64, getLsbD_setWidth_64 _ _ hi64]
  have h1 : ¬(56 ≤ 32 + i ∧ 32 + i < 56 + 8) := by omega
  have h2 : ¬(48 ≤ 32 + i ∧ 32 + i < 48 + 8) := by omega
  have h3 : 32 ≤ 32 + i ∧ 32 + i < 32 + 16 := by omega
  have hrc : h.rc.getLsbD (32 + i) = false := BitVec.getLsbD_of_ge h.rc (32 + i) (by omega)
  have hsub : 32 + i - 32 = i := by omega
  rw [if_neg h1, if_neg h2, if_pos h3, hsub, hrc]
  simp

theorem packHeader_other_eq (h : LeanObjectHeader) :
    (packHeader h).extractLsb' 48 8 = h.other := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi64 : 48 + i < 64 := by omega
  rw [getLsbD_extractLsb'_of_lt _ _ _ _ hi]
  simp only [packHeader, BitVec.getLsbD_or,
    getLsbD_zeroExtend_shiftLeft_64 _ _ _ hi64, getLsbD_setWidth_64 _ _ hi64]
  have h1 : ¬(56 ≤ 48 + i ∧ 48 + i < 56 + 8) := by omega
  have h2 : 48 ≤ 48 + i ∧ 48 + i < 48 + 8 := by omega
  have h3 : ¬(32 ≤ 48 + i ∧ 48 + i < 32 + 16) := by omega
  have hrc : h.rc.getLsbD (48 + i) = false := BitVec.getLsbD_of_ge h.rc (48 + i) (by omega)
  have hsub : 48 + i - 48 = i := by omega
  rw [if_neg h1, if_pos h2, if_neg h3, hsub, hrc]
  simp

theorem packHeader_tag_eq (h : LeanObjectHeader) :
    (packHeader h).extractLsb' 56 8 = h.tag := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi64 : 56 + i < 64 := by omega
  rw [getLsbD_extractLsb'_of_lt _ _ _ _ hi]
  simp only [packHeader, BitVec.getLsbD_or,
    getLsbD_zeroExtend_shiftLeft_64 _ _ _ hi64, getLsbD_setWidth_64 _ _ hi64]
  have h1 : 56 ≤ 56 + i ∧ 56 + i < 56 + 8 := by omega
  have h2 : ¬(48 ≤ 56 + i ∧ 56 + i < 48 + 8) := by omega
  have h3 : ¬(32 ≤ 56 + i ∧ 56 + i < 32 + 16) := by omega
  have hrc : h.rc.getLsbD (56 + i) = false := BitVec.getLsbD_of_ge h.rc (56 + i) (by omega)
  have hsub : 56 + i - 56 = i := by omega
  rw [if_pos h1, if_neg h2, if_neg h3, hsub, hrc]
  simp

/-- Unpacking a packed `LeanObjectHeader` recovers all four fields (`m_rc`, `m_cs_sz`, `m_other`, `m_tag`). -/
theorem unpack_pack_header_id (h : LeanObjectHeader) :
    unpackHeader (packHeader h) = h := by
  cases h
  simp [unpackHeader, packHeader_rc_eq, packHeader_csSz_eq, packHeader_other_eq, packHeader_tag_eq]

/-- Packing an unpacked 64-bit word reconstructs the exact original 8-byte header word. -/
theorem pack_unpack_header_id (w : BitVec 64) :
    packHeader (unpackHeader w) = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [packHeader, unpackHeader, BitVec.getLsbD_or,
    getLsbD_zeroExtend_shiftLeft_64 _ _ _ hi, getLsbD_setWidth_64 _ _ hi]
  by_cases h56 : 56 ≤ i
  · have h1 : 56 ≤ i ∧ i < 56 + 8 := by omega
    have h2 : ¬(48 ≤ i ∧ i < 48 + 8) := by omega
    have h3 : ¬(32 ≤ i ∧ i < 32 + 16) := by omega
    have hrc : (w.extractLsb' 0 32).getLsbD i = false :=
      BitVec.getLsbD_of_ge _ i (by omega)
    have htag : (w.extractLsb' 56 8).getLsbD (i - 56) = w.getLsbD i := by
      rw [getLsbD_extractLsb'_of_lt _ _ _ _ (by omega)]
      congr 1
      omega
    rw [if_pos h1, if_neg h2, if_neg h3, hrc, htag]
    simp
  · by_cases h48 : 48 ≤ i
    · have h1 : ¬(56 ≤ i ∧ i < 56 + 8) := by omega
      have h2 : 48 ≤ i ∧ i < 48 + 8 := by omega
      have h3 : ¬(32 ≤ i ∧ i < 32 + 16) := by omega
      have hrc : (w.extractLsb' 0 32).getLsbD i = false :=
        BitVec.getLsbD_of_ge _ i (by omega)
      have hoth : (w.extractLsb' 48 8).getLsbD (i - 48) = w.getLsbD i := by
        rw [getLsbD_extractLsb'_of_lt _ _ _ _ (by omega)]
        congr 1
        omega
      rw [if_neg h1, if_pos h2, if_neg h3, hrc, hoth]
      simp
    · by_cases h32 : 32 ≤ i
      · have h1 : ¬(56 ≤ i ∧ i < 56 + 8) := by omega
        have h2 : ¬(48 ≤ i ∧ i < 48 + 8) := by omega
        have h3 : 32 ≤ i ∧ i < 32 + 16 := by omega
        have hrc : (w.extractLsb' 0 32).getLsbD i = false :=
          BitVec.getLsbD_of_ge _ i (by omega)
        have hcs : (w.extractLsb' 32 16).getLsbD (i - 32) = w.getLsbD i := by
          rw [getLsbD_extractLsb'_of_lt _ _ _ _ (by omega)]
          congr 1
          omega
        rw [if_neg h1, if_neg h2, if_pos h3, hrc, hcs]
        simp
      · have h1 : ¬(56 ≤ i ∧ i < 56 + 8) := by omega
        have h2 : ¬(48 ≤ i ∧ i < 48 + 8) := by omega
        have h3 : ¬(32 ≤ i ∧ i < 32 + 16) := by omega
        have hrc : (w.extractLsb' 0 32).getLsbD i = w.getLsbD i := by
          rw [getLsbD_extractLsb'_of_lt _ _ _ _ (by omega)]
          simp
        rw [if_neg h1, if_neg h2, if_neg h3, hrc]
        simp

/-- Mutating `m_rc` (bytes `[0, 4)`) leaves the upper 32 bits (`m_cs_sz`, `m_other`, `m_tag`) untouched. -/
theorem update_rc_preserves_metadata_bits (h : LeanObjectHeader) (rc' : BitVec 32) :
    (packHeader { h with rc := rc' }).extractLsb' 32 32 = (packHeader h).extractLsb' 32 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi64 : 32 + i < 64 := by omega
  rw [getLsbD_extractLsb'_of_lt _ _ _ _ hi, getLsbD_extractLsb'_of_lt _ _ _ _ hi]
  simp only [packHeader, BitVec.getLsbD_or, getLsbD_zeroExtend_shiftLeft_64 _ _ _ hi64,
    getLsbD_setWidth_64 _ _ hi64]
  have hrc1 : rc'.getLsbD (32 + i) = false := BitVec.getLsbD_of_ge rc' (32 + i) (by omega)
  have hrc2 : h.rc.getLsbD (32 + i) = false := BitVec.getLsbD_of_ge h.rc (32 + i) (by omega)
  rw [hrc1, hrc2]

/-- `lean_ctor_set_tag` (byte `7`) leaves the lower 56 bits (`m_rc`, `m_cs_sz`, `m_other`) untouched. -/
theorem update_tag_preserves_prefix_bits (h : LeanObjectHeader) (tag' : BitVec 8) :
    (packHeader { h with tag := tag' }).extractLsb' 0 56 = (packHeader h).extractLsb' 0 56 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi64 : i < 64 := by omega
  rw [getLsbD_extractLsb'_of_lt _ _ _ _ hi, getLsbD_extractLsb'_of_lt _ _ _ _ hi]
  simp only [Nat.zero_add, packHeader, BitVec.getLsbD_or, getLsbD_zeroExtend_shiftLeft_64 _ _ _ hi64,
    getLsbD_setWidth_64 _ _ hi64]
  have hnot56 : ¬(56 ≤ i ∧ i < 56 + 8) := by omega
  rw [if_neg hnot56, if_neg hnot56]

/-- Byte offset of each of the 4 `lean_object` header fields (`0 ↦ m_rc`, `1 ↦ m_cs_sz`, `2 ↦ m_other`, `3 ↦ m_tag`). -/
def headerFieldOffset (f : Fin 4) : Nat :=
  if f.val = 0 then 0 else if f.val = 1 then 4 else if f.val = 2 then 6 else 7

/-- Byte width of each of the 4 `lean_object` header fields (`4`, `2`, `1`, `1`). -/
def headerFieldWidth (f : Fin 4) : Nat :=
  if f.val = 0 then 4 else if f.val = 1 then 2 else 1

/-- Byte `b` lies within `[off, off + width)`. -/
def inByteSpan (b off width : Nat) : Prop :=
  off ≤ b ∧ b < off + width

/-- Byte offset of boxed object pointer slot `idx` in `lean_ctor_object` (`8 + 8 * idx`). -/
def ctorObjByteOffset (idx : Nat) : Nat :=
  8 + 8 * idx

/-- Byte offset of a scalar field at `scalarOff` past `numObjs` pointer slots (`8 + 8 * numObjs + scalarOff`). -/
def ctorPayloadByteOffset (numObjs scalarOff : Nat) : Nat :=
  8 + 8 * numObjs + scalarOff

/-- Pairwise byte-span disjointness of the 4 `lean_object` header fields inside `[0, 8)`:
    if byte `b` lies in both field `f1` and field `f2`, then `f1 = f2`. -/
theorem header_fields_eq_of_overlap (f1 f2 : Fin 4) (b : Nat)
    (h1 : inByteSpan b (headerFieldOffset f1) (headerFieldWidth f1))
    (h2 : inByteSpan b (headerFieldOffset f2) (headerFieldWidth f2)) :
    f1 = f2 := by
  rcases f1 with ⟨v1, hv1⟩
  rcases f2 with ⟨v2, hv2⟩
  apply Fin.ext
  unfold inByteSpan headerFieldOffset headerFieldWidth at h1 h2
  have hc1 : v1 = 0 ∨ v1 = 1 ∨ v1 = 2 ∨ v1 = 3 := by omega
  have hc2 : v2 = 0 ∨ v2 = 1 ∨ v2 = 2 ∨ v2 = 3 := by omega
  rcases hc1 with rfl | rfl | rfl | rfl
  all_goals rcases hc2 with rfl | rfl | rfl | rfl
  all_goals simp_all
  all_goals omega

/-- Every `lean_object` header byte lies strictly below any constructor payload offset `8 + 8 * numObjs + scalarOff`. -/
theorem header_byte_lt_ctor_payload (f : Fin 4) (b numObjs scalarOff : Nat)
    (hf : inByteSpan b (headerFieldOffset f) (headerFieldWidth f)) :
    b < ctorPayloadByteOffset numObjs scalarOff := by
  rcases f with ⟨v, hv⟩
  unfold inByteSpan headerFieldOffset headerFieldWidth at hf
  unfold ctorPayloadByteOffset
  have hc : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  all_goals simp_all
  all_goals omega

/-- Pairwise byte-span disjointness of constructor object pointer slots `[8 + 8*i, 8 + 8*i + 8)`:
    for distinct slots `i ≠ j` and any intra-slot byte offsets `subI, subJ : Fin 8`, their addresses never alias. -/
theorem ctor_obj_slots_byte_disjoint (i j : Nat) (subI subJ : Fin 8) (hne : i ≠ j) :
    ctorObjByteOffset i + subI.val ≠ ctorObjByteOffset j + subJ.val := by
  have hi8 := subI.isLt
  have hj8 := subJ.isLt
  unfold ctorObjByteOffset
  omega

/-- Every byte `subOff : Fin 8` of object pointer slot `idx < numObjs` (`[8 + 8*idx, 16 + 8*idx)`) lies strictly
    below every scalar payload byte offset `8 + 8 * numObjs + scalarOff` (`HEAPOBJ_CONTRACT.md` C1.2). -/
theorem ctor_obj_lt_scalar_payload (idx numObjs scalarOff : Nat) (subOff : Fin 8)
    (hidx : idx < numObjs) :
    ctorObjByteOffset idx + subOff.val < ctorPayloadByteOffset numObjs scalarOff := by
  have hsub := subOff.isLt
  unfold ctorObjByteOffset ctorPayloadByteOffset
  omega

/-- `lean_ctor_get_usize(o, numObjs + k)` (`8 + 8 * (numObjs + k)`) coincides with `ctorPayloadByteOffset numObjs (8 * k)`. -/
theorem ctor_usize_slot_eq_payload_offset (numObjs k : Nat) :
    ctorObjByteOffset (numObjs + k) = ctorPayloadByteOffset numObjs (8 * k) := by
  unfold ctorObjByteOffset ctorPayloadByteOffset
  omega

/-! ## 3. `m_rc` Preservation: Persistent Objects, Unique Reset/Reuse/Set & Shared COW -/

/-- `lean_is_persistent(o)` (`m_rc == 0` in `lean.h`): static, region, or immortal runtime object. -/
def isPersistentRc (rc : BitVec 32) : Bool :=
  rc == 0#32

/-- `lean_is_exclusive(o)` (`m_rc == 1` in `lean.h`): uniquely owned heap object eligible for reset/reuse/in-place set. -/
def isExclusiveRc (rc : BitVec 32) : Bool :=
  rc == 1#32

/-- `lean_inc_ref_n(o, k)` header transition (matching `@lean_native_inc` in `Backend/LLVM.lean`):
    updates `m_rc` iff `0 <_s m_rc`, leaving persistent (`m_rc == 0`) and non-RC (`m_rc <_s 0`) objects untouched. -/
def stepIncRefHeader (h : LeanObjectHeader) (k : BitVec 32) : LeanObjectHeader :=
  if BitVec.slt 0#32 h.rc then { h with rc := h.rc + k } else h

/-- `lean_dec_ref(o)` header transition (matching `@lean_native_dec` in `Backend/LLVM.lean`):
    returns `(updatedHeader, shouldDealloc)`. Persistent (`m_rc == 0`) and non-positive `m_rc` never deallocate. -/
def stepDecRefHeader (h : LeanObjectHeader) : LeanObjectHeader × Bool :=
  if BitVec.slt 0#32 h.rc then
    let rc' := h.rc - 1#32
    ({ h with rc := rc' }, rc' == 0#32)
  else
    (h, false)

/-- `lean_inc_ref` on a persistent object (`m_rc == 0`) preserves the entire header unchanged (`m_rc == 0`). -/
theorem persistent_inc_ref_preserves_header (h : LeanObjectHeader) (k : BitVec 32)
    (hp : isPersistentRc h.rc = true) :
    stepIncRefHeader h k = h := by
  have hrc : h.rc = 0#32 := of_decide_eq_true hp
  unfold stepIncRefHeader
  rw [hrc]
  rfl

/-- `lean_dec_ref` on a persistent object (`m_rc == 0`) preserves `m_rc == 0` and never frees (`shouldDealloc = false`). -/
theorem persistent_dec_ref_never_frees (h : LeanObjectHeader)
    (hp : isPersistentRc h.rc = true) :
    stepDecRefHeader h = (h, false) := by
  have hrc : h.rc = 0#32 := of_decide_eq_true hp
  unfold stepDecRefHeader
  rw [hrc]
  rfl

/-- Any non-positive signed `m_rc` (`m_rc ≤_s 0`, covering persistent `0` and MT/compact `< 0`) never frees on `dec_ref`. -/
theorem nonpos_dec_ref_never_frees (h : LeanObjectHeader)
    (hnp : BitVec.slt 0#32 h.rc = false) :
    stepDecRefHeader h = (h, false) := by
  unfold stepDecRefHeader
  rw [hnp]
  rfl

/-- `lean_dec_ref` on a unique object (`m_rc == 1`) transitions `m_rc` to `0` and triggers deallocation (`true`). -/
theorem unique_dec_ref_triggers_free (h : LeanObjectHeader)
    (hu : isExclusiveRc h.rc = true) :
    stepDecRefHeader h = ({ h with rc := 0#32 }, true) := by
  have hrc : h.rc = 1#32 := of_decide_eq_true hu
  unfold stepDecRefHeader
  rw [hrc]
  rfl

/-- `lean_dec_ref` on a shared object (`1 <_s m_rc`) decrements `m_rc` to `m_rc - 1` without freeing (`false`). -/
theorem shared_dec_ref_stays_live (h : LeanObjectHeader)
    (hs : BitVec.slt 1#32 h.rc = true) :
    stepDecRefHeader h = ({ h with rc := h.rc - 1#32 }, false) := by
  have h1_lt : (1#32).toInt < h.rc.toInt := by
    unfold BitVec.slt at hs
    exact of_decide_eq_true hs
  have h0_lt : (0#32).toInt < h.rc.toInt := by
    have h01 : (0#32).toInt = 0 := rfl
    have h11 : (1#32).toInt = 1 := rfl
    omega
  have hpos : BitVec.slt 0#32 h.rc = true := by
    unfold BitVec.slt
    exact decide_eq_true h0_lt
  have hne0 : (h.rc - 1#32 == 0#32) = false := by
    cases hbeq : (h.rc - 1#32 == 0#32) with
    | false => rfl
    | true =>
      have heq0 : h.rc - 1#32 = 0#32 := of_decide_eq_true hbeq
      have hrc1 : h.rc = 1#32 := by
        have hadd := congrArg (· + 1#32) heq0
        simpa [BitVec.sub_add_cancel] using hadd
      rw [hrc1] at hs
      contradiction
  unfold stepDecRefHeader
  simp [hpos, hne0]

/-- `inc_ref` by `1` followed by `dec_ref` on a live positive `m_rc` (without signed 32-bit overflow) restores `h` without freeing. -/
theorem inc_then_dec_header_roundtrip (h : LeanObjectHeader)
    (hno_ovf : BitVec.slt 0#32 (h.rc + 1#32) = true)
    (hpos : BitVec.slt 0#32 h.rc = true) :
    stepDecRefHeader (stepIncRefHeader h 1#32) = (h, false) := by
  unfold stepIncRefHeader stepDecRefHeader
  simp only [hpos, ↓reduceIte, hno_ovf, BitVec.add_sub_cancel]
  have hne0 : (h.rc == 0#32) = false := by
    cases hbeq : (h.rc == 0#32) with
    | false => rfl
    | true =>
      have hz : h.rc = 0#32 := of_decide_eq_true hbeq
      rw [hz] at hpos
      contradiction
  simp [hne0]

/-! ### Operational Unique Reset/Reuse/Set vs Shared Copy-On-Write (`HeapState`) -/

/-- Observable constructor content `(tag, objFields, scalarFields)` independent of physical allocation ID. -/
def ctorPayload (o : HeapObj) : Nat × List Val × List Val :=
  (o.tag, o.objFields, o.scalarFields)

/-- Pure functional clone-and-decrement specification on `HeapState`:
    decrements `objId` by `1` (`setObjRc objId (rc - 1)`) and allocates a fresh `HeapObj` (`rc = 1`)
    holding the updated slot while leaving any remaining shared references at `objId` untouched. -/
def pureCloneWriteField (st : HeapState) (objId idx : Nat) (val : Val) (isObj : Bool := true) :
    Except UBError (Nat × HeapState) := do
  let obj ← st.liveHeapObj objId
  let fs := if isObj then obj.objFields else obj.scalarFields
  if isObj && !val.wfField then .error (.typeError "ctor_set: field value is a tuple owning an edge")
  else if idx < fs.length then
    let stDec := st.setObjRc objId (st.getObjRefCount objId - 1)
    let objFields' := if isObj then fs.set idx val else obj.objFields
    let scalarFields' := if isObj then obj.scalarFields else fs.set idx val
    .ok (stDec.allocHeapCtor obj.tag objFields' scalarFields')
  else .error (.outOfBounds idx fs.length)

/-- Perceus / `lean.h` reset-reuse-set / COW field update on `HeapState`:
    - Unique (`getObjRefCount objId == 1`): mutates `objId` in-place via `writeHeapObjFieldExclusive`
      with zero heap allocation (`outId = objId`).
    - Shared (`getObjRefCount objId ≥ 2`): performs copy-on-write via `pureCloneWriteField`. -/
def cowWriteField (st : HeapState) (objId idx : Nat) (val : Val) (isObj : Bool := true) :
    Except UBError (Nat × HeapState) := do
  let _ ← st.liveHeapObj objId
  if st.getObjRefCount objId == 1 then
    let st' ← st.writeHeapObjFieldExclusive objId idx val isObj
    .ok (objId, st')
  else
    pureCloneWriteField st objId idx val isObj

/-- Direct in-place `writeHeapObjFieldExclusive` on a shared live object (`rc ≥ 2`) fails with `.nonExclusiveWrite` (C4.2). -/
theorem shared_inplace_write_rejected (st : HeapState) (objId idx : Nat) (val : Val) (isObj : Bool)
    (obj : HeapObj) (h_find : st.findHeapObj objId = some obj) (h_shared : 2 ≤ st.getObjRefCount objId) :
    st.writeHeapObjFieldExclusive objId idx val isObj = .error (.nonExclusiveWrite objId) := by
  unfold HeapState.writeHeapObjFieldExclusive HeapState.mutateHeapObjExclusive HeapState.liveHeapObj
  have hrc0 : (st.getObjRefCount objId == 0) = false := by
    cases h : st.getObjRefCount objId == 0 with
    | false => rfl
    | true => have := of_decide_eq_true h; omega
  have hrc1 : (st.getObjRefCount objId != 1) = true := by
    cases h : st.getObjRefCount objId == 1 with
    | false => simp [bne, h]
    | true => have := of_decide_eq_true h; omega
  simp [hrc0, h_find, hrc1, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

private theorem findHeapObj_map_const_other (objs : List HeapObj) (objId aliasId : Nat) (obj' : HeapObj)
    (hne : aliasId ≠ objId) (h_id : obj'.id = objId) :
    (objs.map fun o => if o.id == objId then obj' else o).find? (·.id == aliasId) =
      objs.find? (·.id == aliasId) := by
  induction objs with
  | nil => rfl
  | cons hd tl ih =>
    by_cases h_eq : (hd.id == objId) = true
    · have hd_eq : hd.id = objId := of_decide_eq_true h_eq
      have h_obj'_ne : (obj'.id == aliasId) = false := by
        rw [h_id]
        cases h : objId == aliasId with
        | false => rfl
        | true => exfalso; exact hne (of_decide_eq_true h).symm
      have h_hd_ne : (hd.id == aliasId) = false := by
        rw [hd_eq]
        cases h : objId == aliasId with
        | false => rfl
        | true => exfalso; exact hne (of_decide_eq_true h).symm
      simp only [List.map, h_eq, ↓reduceIte, List.find?, h_obj'_ne, h_hd_ne]
      exact ih
    · have h_false : (hd.id == objId) = false := Bool.eq_false_iff.mpr h_eq
      simp only [List.map, h_false, Bool.false_eq_true, ↓reduceIte, List.find?]
      cases hd.id == aliasId
      · exact ih
      · rfl

private theorem findHeapObj_map_self (objs : List HeapObj) (objId : Nat) (obj' : HeapObj)
    (h_id : obj'.id = objId) :
    (objs.map fun o => if o.id == objId then obj' else o).find? (·.id == objId) =
      (objs.find? (·.id == objId)).map (fun _ => obj') := by
  induction objs with
  | nil => rfl
  | cons hd tl ih =>
    by_cases h_eq : (hd.id == objId) = true
    · have h_self : (obj'.id == objId) = true := by simp [h_id]
      simp only [List.map, h_eq, ↓reduceIte, List.find?, h_self, Option.map]
    · have h_false : (hd.id == objId) = false := Bool.eq_false_iff.mpr h_eq
      simp only [List.map, h_false, Bool.false_eq_true, ↓reduceIte, List.find?]
      exact ih

private theorem find_filter_ne_id (objs : List HeapObj) (dropId keepId : Nat) (hne : keepId ≠ dropId) :
    (objs.filter (fun o => o.id != dropId)).find? (·.id == keepId) =
      objs.find? (·.id == keepId) := by
  induction objs with
  | nil => rfl
  | cons hd tl ih =>
    by_cases h_drop : (hd.id != dropId) = true
    · simp only [List.filter, h_drop, List.find?]
      cases hd.id == keepId
      · exact ih
      · rfl
    · have h_drop_false : (hd.id != dropId) = false := Bool.eq_false_iff.mpr h_drop
      have hd_eq : hd.id = dropId := by
        cases h : hd.id == dropId with
        | false => simp [bne, h] at h_drop_false
        | true => exact of_decide_eq_true h
      have h_ne_keep : (hd.id == keepId) = false := by
        rw [hd_eq]
        cases h : dropId == keepId with
        | false => rfl
        | true => exfalso; exact hne (of_decide_eq_true h).symm
      simp only [List.filter, h_drop_false, List.find?, h_ne_keep]
      exact ih

private theorem find_id_eq (objs : List HeapObj) (objId : Nat) (obj : HeapObj)
    (h : objs.find? (·.id == objId) = some obj) : obj.id = objId := by
  induction objs with
  | nil => simp [List.find?] at h
  | cons hd tl ih =>
    by_cases heq : (hd.id == objId) = true
    · simp only [List.find?, heq] at h
      injection h with hobj
      subst hobj
      exact of_decide_eq_true heq
    · have hf : (hd.id == objId) = false := Bool.eq_false_iff.mpr heq
      simp only [List.find?, hf] at h
      exact ih h

/-- Extract the observable constructor payload `(tag, objFields, scalarFields)` at `(outId, st)`. -/
def observeOutPayload (res : Nat × HeapState) : Option (Nat × List Val × List Val) :=
  (res.2.findHeapObj res.1).map ctorPayload

/-- Unconditional payload equivalence between Perceus `cowWriteField` (in-place when `rc = 1`, COW when `rc ≥ 2`)
    and pure functional `pureCloneWriteField` across all `HeapState` inputs (including exact UB error parity). -/
theorem cowWriteField_matches_pureClone_payload (st : HeapState) (objId idx : Nat) (val : Val) (isObj : Bool) :
    Except.map observeOutPayload (cowWriteField st objId idx val isObj) =
      Except.map observeOutPayload (pureCloneWriteField st objId idx val isObj) := by
  unfold cowWriteField
  cases h_live : st.liveHeapObj objId with
  | error e =>
    unfold pureCloneWriteField
    simp [h_live, Bind.bind, Except.bind, Except.map]
  | ok obj =>
    have h_find : st.findHeapObj objId = some obj := by
      unfold HeapState.liveHeapObj at h_live
      by_cases h0 : st.getObjRefCount objId == 0
      · simp [h0] at h_live
      · simp [h0] at h_live
        cases hf : st.findHeapObj objId with
        | none => simp [hf] at h_live
        | some o =>
          simp [hf] at h_live
          subst h_live
          rfl
    have h_obj_id : obj.id = objId := find_id_eq st.heapObjs objId obj h_find
    by_cases h_rc1 : st.getObjRefCount objId == 1
    · have hrc_val : st.getObjRefCount objId = 1 := of_decide_eq_true h_rc1
      have hnot1 : (st.getObjRefCount objId != 1) = false := by simp [bne, hrc_val]
      simp only [h_live, Bind.bind, Except.bind, h_rc1, ↓reduceIte]
      unfold HeapState.writeHeapObjFieldExclusive HeapState.mutateHeapObjExclusive pureCloneWriteField
      simp only [h_live, Bind.bind, Except.bind, hnot1, Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
      by_cases hwf : isObj && !val.wfField
      · simp [hwf, Except.map]
      · simp only [hwf, Bool.false_eq_true, ↓reduceIte]
        by_cases hlt : idx < (if isObj then obj.objFields else obj.scalarFields).length
        · simp only [hlt, ↓reduceIte, Except.map, observeOutPayload]
          congr 1
          let updatedObj : HeapObj :=
            if isObj then { obj with objFields := (if isObj then obj.objFields else obj.scalarFields).set idx val }
            else { obj with scalarFields := (if isObj then obj.objFields else obj.scalarFields).set idx val }
          have hupd_id : updatedObj.id = objId := by
            cases isObj <;> simp [updatedObj, h_obj_id]
          have hfind_cow :
              ({ st with
                  heapObjs := st.heapObjs.map fun o =>
                    if o.id == objId then updatedObj else o } : HeapState).findHeapObj objId =
                some updatedObj := by
            unfold HeapState.findHeapObj
            dsimp only
            rw [findHeapObj_map_self st.heapObjs objId updatedObj hupd_id]
            unfold HeapState.findHeapObj at h_find
            rw [h_find]
            rfl
          let stFast : HeapState :=
            { st with heapObjs := st.heapObjs.map fun o => if o.id == objId then updatedObj else o }
          change (stFast.findHeapObj objId).map ctorPayload = _
          rw [hfind_cow]
          unfold HeapState.allocHeapCtor HeapState.findHeapObj
          simp only [List.find?, beq_self_eq_true, Option.map]
          cases isObj <;> simp [updatedObj, ctorPayload]
        · simp [hlt, Except.map]
    · simp [h_live, Bind.bind, Except.bind, h_rc1]

/-- Every successful `cowWriteField` yields an exclusively owned (`rc = 1`) output constructor handle. -/
theorem cowWriteField_result_exclusive (st : HeapState) (objId idx : Nat) (val : Val) (isObj : Bool)
    (outId : Nat) (st' : HeapState)
    (h_ok : cowWriteField st objId idx val isObj = .ok (outId, st')) :
    st'.getObjRefCount outId = 1 := by
  unfold cowWriteField at h_ok
  cases h_live : st.liveHeapObj objId with
  | error e =>
    simp [h_live, Bind.bind, Except.bind] at h_ok
  | ok obj =>
    by_cases h_rc1 : st.getObjRefCount objId == 1
    · have hrc_val : st.getObjRefCount objId = 1 := of_decide_eq_true h_rc1
      have hnot1 : (st.getObjRefCount objId != 1) = false := by simp [bne, hrc_val]
      simp only [h_live, Bind.bind, Except.bind, h_rc1, ↓reduceIte] at h_ok
      unfold HeapState.writeHeapObjFieldExclusive HeapState.mutateHeapObjExclusive at h_ok
      simp only [h_live, Bind.bind, Except.bind, hnot1, Bool.false_eq_true, ↓reduceIte,
        pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h_ok
      by_cases hwf : isObj && !val.wfField
      · simp [hwf, Bind.bind, Except.bind] at h_ok
      · simp only [hwf, Bool.false_eq_true, ↓reduceIte] at h_ok
        by_cases hlt : idx < (if isObj then obj.objFields else obj.scalarFields).length
        · simp only [hlt, ↓reduceIte, Bind.bind, Except.bind] at h_ok
          injection h_ok with hpair
          injection hpair with hout hst
          subst hout
          subst hst
          exact hrc_val
        · simp [hlt, Bind.bind, Except.bind] at h_ok
    · simp only [h_live, Bind.bind, Except.bind, h_rc1, Bool.false_eq_true, ↓reduceIte] at h_ok
      unfold pureCloneWriteField at h_ok
      simp only [h_live, Bind.bind, Except.bind] at h_ok
      by_cases hwf : isObj && !val.wfField
      · simp [hwf] at h_ok
      · simp only [hwf, Bool.false_eq_true, ↓reduceIte] at h_ok
        by_cases hlt : idx < (if isObj then obj.objFields else obj.scalarFields).length
        · simp only [hlt, ↓reduceIte] at h_ok
          injection h_ok with hpair
          injection hpair with hout hst
          subst hout
          subst hst
          unfold HeapState.getObjRefCount
          simp [List.find?]
        · simp [hlt] at h_ok

/-- Aliasing observational equivalence for `cowWriteField`:
    for every live external alias `aliasId ≤ st.nextId` satisfying the Perceus RC uniqueness invariant
    `(st.getObjRefCount objId = 1 → aliasId ≠ objId)` (which holds vacuously for `aliasId = objId` whenever
    `objId` is shared with `rc ≥ 2`), `cowWriteField` preserves `findHeapObj aliasId` unchanged! -/
theorem cowWriteField_preserves_live_alias (st : HeapState) (objId idx aliasId : Nat) (val : Val) (isObj : Bool)
    (outId : Nat) (st' : HeapState)
    (h_bound : aliasId ≤ st.nextId)
    (h_rc_inv : st.getObjRefCount objId = 1 → aliasId ≠ objId)
    (h_ok : cowWriteField st objId idx val isObj = .ok (outId, st')) :
    st'.findHeapObj aliasId = st.findHeapObj aliasId := by
  unfold cowWriteField at h_ok
  cases h_live : st.liveHeapObj objId with
  | error e =>
    simp [h_live, Bind.bind, Except.bind] at h_ok
  | ok obj =>
    by_cases h_rc1 : st.getObjRefCount objId == 1
    · have hrc_val : st.getObjRefCount objId = 1 := of_decide_eq_true h_rc1
      have hne : aliasId ≠ objId := h_rc_inv hrc_val
      simp only [h_live, Bind.bind, Except.bind, h_rc1, ↓reduceIte] at h_ok
      unfold HeapState.writeHeapObjFieldExclusive HeapState.mutateHeapObjExclusive at h_ok
      have hnot1 : (st.getObjRefCount objId != 1) = false := by simp [bne, hrc_val]
      simp only [h_live, Bind.bind, Except.bind, hnot1, Bool.false_eq_true, ↓reduceIte,
        pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h_ok
      by_cases hwf : isObj && !val.wfField
      · simp [hwf, Bind.bind, Except.bind] at h_ok
      · simp only [hwf, Bool.false_eq_true, ↓reduceIte] at h_ok
        by_cases hlt : idx < (if isObj then obj.objFields else obj.scalarFields).length
        · simp only [hlt, ↓reduceIte, Bind.bind, Except.bind] at h_ok
          injection h_ok with hpair
          injection hpair with _ hst
          subst hst
          have h_obj_id : obj.id = objId := by
            unfold HeapState.liveHeapObj at h_live
            by_cases h0 : st.getObjRefCount objId == 0
            · simp [h0] at h_live
            · simp [h0] at h_live
              cases hf : st.findHeapObj objId with
              | none => simp [hf] at h_live
              | some o =>
                simp [hf] at h_live
                subst h_live
                unfold HeapState.findHeapObj at hf
                exact find_id_eq st.heapObjs objId o hf
          let targetObj : HeapObj :=
            if isObj then { obj with objFields := (if isObj then obj.objFields else obj.scalarFields).set idx val }
            else { obj with scalarFields := (if isObj then obj.objFields else obj.scalarFields).set idx val }
          have ht_id : targetObj.id = objId := by cases isObj <;> simp [targetObj, h_obj_id]
          unfold HeapState.findHeapObj
          exact findHeapObj_map_const_other st.heapObjs objId aliasId targetObj hne ht_id
        · simp [hlt, Bind.bind, Except.bind] at h_ok
    · have hrc_ne0 : st.getObjRefCount objId ≠ 0 := by
        unfold HeapState.liveHeapObj at h_live
        intro h0
        simp [h0] at h_live
      have hrc_ne1 : st.getObjRefCount objId ≠ 1 := by
        intro h1
        simp [h1] at h_rc1
      have hrc_sub_pos : (st.getObjRefCount objId - 1 == 0) = false := by
        cases h : (st.getObjRefCount objId - 1 == 0) with
        | false => rfl
        | true =>
          have hsub0 := of_decide_eq_true h
          omega
      simp only [h_live, Bind.bind, Except.bind, h_rc1, Bool.false_eq_true, ↓reduceIte] at h_ok
      unfold pureCloneWriteField at h_ok
      simp only [h_live, Bind.bind, Except.bind] at h_ok
      by_cases hwf : isObj && !val.wfField
      · simp [hwf] at h_ok
      · simp only [hwf, Bool.false_eq_true, ↓reduceIte] at h_ok
        by_cases hlt : idx < (if isObj then obj.objFields else obj.scalarFields).length
        · simp only [hlt, ↓reduceIte] at h_ok
          injection h_ok with hpair
          injection hpair with _ hst
          subst hst
          have h_setrc_objs : (st.setObjRc objId (st.getObjRefCount objId - 1)).heapObjs = st.heapObjs := by
            unfold HeapState.setObjRc
            simp [hrc_sub_pos]
          have h_setrc_next : (st.setObjRc objId (st.getObjRefCount objId - 1)).nextId = st.nextId := by
            unfold HeapState.setObjRc
            simp [hrc_sub_pos]
          have hne_new : aliasId ≠ (st.setObjRc objId (st.getObjRefCount objId - 1)).nextId + 1 := by
            rw [h_setrc_next]
            omega
          have h_head_ne : (((st.setObjRc objId (st.getObjRefCount objId - 1)).nextId + 1 == aliasId)) = false := by
            cases h : ((st.setObjRc objId (st.getObjRefCount objId - 1)).nextId + 1 == aliasId) with
            | false => rfl
            | true => exfalso; exact hne_new (of_decide_eq_true h).symm
          unfold HeapState.findHeapObj
          simp only [List.find?, h_head_ne]
          rw [h_setrc_objs]
          exact find_filter_ne_id st.heapObjs ((st.setObjRc objId (st.getObjRefCount objId - 1)).nextId + 1) aliasId hne_new
        · simp [hlt] at h_ok

/-! ### In-Kernel Transitive Axiom Gate (`Lean.collectAxioms`) -/

/-- Complete list of Track C6 `HeapObj` ABI, layout, boxing, and RC preservation theorems. -/
def heapObjAbiAuditedTheorems : List Lean.Name :=
  [ ``unbox_box_id
  , ``unbox_box_ne_of_ge
  , ``unbox_box_eq_iff
  , ``is_scalar_box_true
  , ``is_scalar_aligned_ptr_false
  , ``box_ne_aligned_ptr
  , ``packHeader_rc_eq
  , ``packHeader_csSz_eq
  , ``packHeader_other_eq
  , ``packHeader_tag_eq
  , ``unpack_pack_header_id
  , ``pack_unpack_header_id
  , ``update_rc_preserves_metadata_bits
  , ``update_tag_preserves_prefix_bits
  , ``header_fields_eq_of_overlap
  , ``header_byte_lt_ctor_payload
  , ``ctor_obj_slots_byte_disjoint
  , ``ctor_obj_lt_scalar_payload
  , ``ctor_usize_slot_eq_payload_offset
  , ``persistent_inc_ref_preserves_header
  , ``persistent_dec_ref_never_frees
  , ``nonpos_dec_ref_never_frees
  , ``unique_dec_ref_triggers_free
  , ``shared_dec_ref_stays_live
  , ``inc_then_dec_header_roundtrip
  , ``shared_inplace_write_rejected
  , ``cowWriteField_matches_pureClone_payload
  , ``cowWriteField_result_exclusive
  , ``cowWriteField_preserves_live_alias
  ]

elab "#verify_heapobj_abi_axioms" : command => do
  Lean.Elab.Command.liftCoreM do
    let allowed : List Lean.Name := [``propext, ``Quot.sound, ``Classical.choice]
    let env ← Lean.getEnv
    for declName in heapObjAbiAuditedTheorems do
      if !env.contains declName then
        Lean.throwError s!"[HeapObjAbiProofs] missing theorem {declName}"
      let axs := (← Lean.collectAxioms declName).toList
      let disallowed := axs.filter (!allowed.contains ·)
      if !disallowed.isEmpty then
        Lean.throwError s!"[HeapObjAbiProofs] theorem {declName} uses disallowed axioms: {disallowed}"

#verify_heapobj_abi_axioms

end LeanNative.Proofs.HeapObjAbi
