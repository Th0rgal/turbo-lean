import Lean
import LeanNative.Proofs.HeapObjAbiProofs

namespace LeanNative.Proofs.HeapObjMtAbi

open LeanNative.Proofs.HeapObjAbi

/-!
# Multi-Threaded `m_rc`, Sticky Saturation, Linearity Bit & Big/Closure/External `HeapObj` Layout Proofs

Stage 5 formal ABI guarantees (`0 sorryAx`, standard kernel axioms only) complementing
`HeapObjAbiProofs.lean` across four `include/lean/lean.h` (`v4.35.0`) runtime contracts:

1. **Multi-Threaded (`m_rc < 0`) Reference Counting & Sticky Saturation (`lean.h:618-727`)**:
   - Exact unsigned-comparison equivalence of `lean_is_unstuck_mt` (`(unsigned)rc > (unsigned)LEAN_RC_STICKY`
     iff `LEAN_RC_STICKY <_s rc ∧ rc <_s 0`) and `lean_is_never_freed` (for non-`st` `rc ≤_s 0`,
     `(unsigned)rc <= (unsigned)LEAN_RC_STICKY_DROP` iff `rc == 0 ∨ rc ≤_s LEAN_RC_STICKY_DROP`).
   - `lean_mark_mt` negates positive single-threaded counts (`0 <_s rc`) into multi-threaded counts
     (`rc' = -rc <_s 0`), leaving persistent (`0`) and already-MT (`<_s 0`) headers untouched.
   - Multi-threaded `lean_inc_ref_n` (`1 ≤ n ≤ LEAN_RC_INC_MAX = 0x10000`) decrements `m_rc` toward
     `LEAN_RC_STICKY` (`INT_MIN + 0x10000000`) without ever wrapping past `INT_MIN` into positive `st`
     counts, and freezes once `rc ≤_s LEAN_RC_STICKY`.
   - Multi-threaded `lean_dec_ref` freezes at `rc ≤_s LEAN_RC_STICKY_DROP` (`INT_MIN + 0x20000000`)
     without freeing, triggers deallocation iff pre-state `rc == -1`, and otherwise steps `rc + 1 <_s 0`
     without crossing into persistent (`0`) or single-threaded (`> 0`) states.

2. **`LEAN_LINEAR_MARK_MASK` (`0x80u`) Bit-Slice Isolation (`lean.h:231, 779-787, 1214-1225`)**:
   - Marking an exclusive scalar array/array/string linear (`m_other |= 0x80u`) sets
     `lean_is_marked_linear_core` to `true`, preserves `lean_sarray_elem_size` (`m_other & ~0x80u`)
     for every valid `elem_size < 0x80`, and leaves `m_rc`, `m_cs_sz`, and `m_tag` bit-identical.

3. **Runtime Tag Partitioning & LP64 Byte Layouts (`lean.h:101-120, 206-239, 342-346`)**:
   - Mutual exclusivity of `lean_is_ctor` (`≤ 243`), `lean_is_closure` (`245`),
     `lean_is_big_object_tag` (`246..249`), and `lean_is_external` (`254`).
   - Exact LP64 field byte-span disjointness for `lean_sarray_object` / `lean_array_object` (`24`-byte prefix),
     `lean_string_object` (`32`-byte prefix), `lean_closure_object` (`m_header` `[0..8)`, `m_fun` `[8..16)`,
     `m_arity` `[16..18)`, `m_num_fixed` `[18..20)`, padding `[20..24)`, `m_objs[i]` `[24+8*i..32+8*i)`),
     and `lean_external_object` (`m_header` `[0..8)`, `m_class` `[8..16)`, `m_data` `[16..24)`).

4. **`lean_alloc_sarray_would_overflow` Checked Allocation Arithmetic (`lean.h:432-448, 1203-1211`)**:
   - `sarrayAllocWouldOverflow elemSize capacity = false` iff `24 + elemSize * capacity < 2 ^ 64`.
-/

/-! ## 1. Multi-Threaded `m_rc` Thresholds, Fast Unsigned Predicates & State Transitions -/

/-- `INT32_MIN` (`-2^31 = 0x80000000`) as a 32-bit two's-complement word. -/
def leanInt32Min : BitVec 32 := 0x80000000#32

/-- `LEAN_RC_STICKY` (`INT_MIN + 0x10000000 = 0x90000000`, `-1879048192`). -/
def leanRcSticky : BitVec 32 := 0x90000000#32

/-- `LEAN_RC_STICKY_DROP` (`INT_MIN + 0x20000000 = 0xA0000000`, `-1610612736`). -/
def leanRcStickyDrop : BitVec 32 := 0xA0000000#32

/-- `LEAN_RC_INC_MAX` (`0x10000 = 65536`) inline increment bound (`lean.h:679`). -/
def leanRcIncMax : BitVec 32 := 0x00010000#32

/-- `lean_is_st(o)`: `0 <_s m_rc` (`lean.h:622`). -/
def leanIsStRc (rc : BitVec 32) : Bool :=
  BitVec.slt 0#32 rc

/-- `lean_is_mt(o)`: `m_rc <_s 0` (`lean.h:618`). -/
def leanIsMtRc (rc : BitVec 32) : Bool :=
  BitVec.slt rc 0#32

/-- `lean_is_unstuck_mt(o)`: `(unsigned)rc > (unsigned)LEAN_RC_STICKY` (`lean.h:658`). -/
def leanIsUnstuckMtUnsigned (rc : BitVec 32) : Bool :=
  BitVec.ult leanRcSticky rc

/-- `lean_is_never_freed(o)` (under `!lean_is_st(o)`): `(unsigned)rc <= (unsigned)LEAN_RC_STICKY_DROP` (`lean.h:666`). -/
def leanIsNeverFreedUnsigned (rc : BitVec 32) : Bool :=
  BitVec.ule rc leanRcStickyDrop

/-- `lean_mark_mt` header transition (`runtime/object.cpp`): transitions positive single-threaded `m_rc`
    to `-m_rc` (so `-1` represents 1 MT reference), leaving persistent (`0`) and already-MT (`< 0`) counts unchanged. -/
def stepMarkMtHeader (h : LeanObjectHeader) : LeanObjectHeader :=
  if leanIsStRc h.rc then { h with rc := 0#32 - h.rc } else h

/-- Inline multi-threaded `lean_inc_ref_n(o, n)` transition for `1 ≤ n ≤ LEAN_RC_INC_MAX` (`lean.h:694-712`):
    if `st`, adds `n`; else if `lean_is_unstuck_mt`, atomically subtracts `n`; else leaves sticky/persistent `rc` frozen. -/
def stepMtIncRefHeader (h : LeanObjectHeader) (n : BitVec 32) : LeanObjectHeader :=
  if leanIsStRc h.rc then
    { h with rc := h.rc + n }
  else if leanIsUnstuckMtUnsigned h.rc then
    { h with rc := h.rc - n }
  else
    h

/-- Multi-threaded `lean_dec_ref` / `lean_dec_ref_cold` transition (`lean.h:721-727`):
    - If `1 <_s rc`, decrements `st` count to `rc - 1` without freeing (`false`).
    - If `rc == 1`, transitions to `0` and frees (`true`).
    - If `!lean_is_st(o)` and `lean_is_never_freed(o)` (`rc == 0` or `rc ≤_s LEAN_RC_STICKY_DROP`), stays frozen (`false`).
    - Otherwise (`LEAN_RC_STICKY_DROP <_s rc <_s 0`), atomically increments `rc` by `1` (`fetch_add(1)`),
      freeing iff pre-state `rc == -1`. -/
def stepMtDecRefHeader (h : LeanObjectHeader) : LeanObjectHeader × Bool :=
  if BitVec.slt 1#32 h.rc then
    ({ h with rc := h.rc - 1#32 }, false)
  else if h.rc == 1#32 then
    ({ h with rc := 0#32 }, true)
  else if leanIsNeverFreedUnsigned h.rc then
    (h, false)
  else
    let rc' := h.rc + 1#32
    ({ h with rc := rc' }, h.rc == (-1#32))

private theorem toInt_eq_of_msb (x : BitVec 32) :
    x.toInt = if x.toNat < 2 ^ 31 then (x.toNat : Int) else (x.toNat : Int) - 2 ^ 32 := by
  rw [BitVec.toInt_eq_toNat_cond]
  have hlt := x.isLt
  split <;> omega

/-- Trichotomy of `m_rc`: every 32-bit header count is in exactly one of `{st, persistent, mt}`. -/
theorem rc_mode_partition (rc : BitVec 32) :
    (leanIsStRc rc = true ∧ isPersistentRc rc = false ∧ leanIsMtRc rc = false) ∨
    (leanIsStRc rc = false ∧ isPersistentRc rc = true ∧ leanIsMtRc rc = false) ∨
    (leanIsStRc rc = false ∧ isPersistentRc rc = false ∧ leanIsMtRc rc = true) := by
  unfold leanIsStRc isPersistentRc leanIsMtRc BitVec.slt
  have h0_int : (0#32).toInt = 0 := rfl
  have h_zero_iff : (rc == 0#32) = true ↔ rc.toInt = 0 := by
    constructor
    · intro h
      have heq : rc = 0#32 := of_decide_eq_true h
      subst heq
      rfl
    · intro h
      have heq : rc = 0#32 := BitVec.eq_of_toInt_eq h
      subst heq
      rfl
  by_cases hgt : (0 : Int) < rc.toInt
  · left
    refine ⟨decide_eq_true hgt, ?_, ?_⟩
    · cases hbeq : (rc == 0#32) with
      | false => rfl
      | true => have := h_zero_iff.mp hbeq; omega
    · exact decide_eq_false (by omega)
  · by_cases heq0 : rc.toInt = 0
    · right; left
      refine ⟨decide_eq_false (by omega), h_zero_iff.mpr heq0, decide_eq_false (by omega)⟩
    · right; right
      have hlt : rc.toInt < 0 := by omega
      refine ⟨decide_eq_false (by omega), ?_, decide_eq_true hlt⟩
      cases hbeq : (rc == 0#32) with
      | false => rfl
      | true => have := h_zero_iff.mp hbeq; omega

/-- `lean.h`'s single-instruction unsigned check `(unsigned)rc > (unsigned)LEAN_RC_STICKY`
    is equivalent to `LEAN_RC_STICKY <_s rc ∧ rc <_s 0`. -/
theorem isUnstuckMt_unsigned_iff_signed (rc : BitVec 32) :
    leanIsUnstuckMtUnsigned rc = true ↔
      (BitVec.slt leanRcSticky rc = true ∧ leanIsMtRc rc = true) := by
  unfold leanIsUnstuckMtUnsigned leanIsMtRc BitVec.ult BitVec.slt
  have h_sticky_nat : leanRcSticky.toNat = 2415919104 := rfl
  have h_sticky_int : leanRcSticky.toInt = -1879048192 := rfl
  have h0_int : (0#32).toInt = 0 := rfl
  have h_rc_int := toInt_eq_of_msb rc
  have h_rc_lt := rc.isLt
  simp only [decide_eq_true_eq, h_sticky_nat, h_sticky_int, h0_int]
  split at h_rc_int <;> omega

/-- Under `!lean_is_st(o)` (`rc ≤_s 0`), `(unsigned)rc <= (unsigned)LEAN_RC_STICKY_DROP`
    holds iff `rc == 0` (persistent) or `rc ≤_s LEAN_RC_STICKY_DROP` (sticky-drop frozen). -/
theorem isNeverFreed_unsigned_iff_of_not_st (rc : BitVec 32)
    (hnot_st : leanIsStRc rc = false) :
    leanIsNeverFreedUnsigned rc = true ↔
      (rc = 0#32 ∨ BitVec.sle rc leanRcStickyDrop = true) := by
  unfold leanIsStRc BitVec.slt at hnot_st
  unfold leanIsNeverFreedUnsigned BitVec.ule BitVec.sle
  have h0_int : (0#32).toInt = 0 := rfl
  have hnot_pos : ¬((0 : Int) < rc.toInt) := of_decide_eq_false hnot_st
  have h_drop_nat : leanRcStickyDrop.toNat = 2684354560 := rfl
  have h_drop_int : leanRcStickyDrop.toInt = -1610612736 := rfl
  have h_rc_int := toInt_eq_of_msb rc
  have h_rc_lt := rc.isLt
  simp only [decide_eq_true_eq, h_drop_nat, h_drop_int]
  constructor
  · intro hule
    by_cases hz : rc.toNat = 0
    · left
      exact BitVec.eq_of_toNat_eq hz
    · right
      split at h_rc_int <;> omega
  · intro hor
    rcases hor with rfl | hsle
    · decide
    · split at h_rc_int <;> omega

/-- `lean_mark_mt` converts any positive single-threaded `m_rc` (`0 <_s rc`) into a strictly negative
    multi-threaded `m_rc` (`-rc <_s 0`) while preserving `csSz`, `other`, and `tag`. -/
theorem markMt_st_becomes_mt (h : LeanObjectHeader) (hst : leanIsStRc h.rc = true) :
    leanIsMtRc (stepMarkMtHeader h).rc = true ∧
    (stepMarkMtHeader h).csSz = h.csSz ∧
    (stepMarkMtHeader h).other = h.other ∧
    (stepMarkMtHeader h).tag = h.tag := by
  unfold stepMarkMtHeader
  rw [hst]
  simp only [↓reduceIte, and_self, and_true]
  unfold leanIsStRc BitVec.slt at hst
  unfold leanIsMtRc BitVec.slt
  have hpos : (0 : Int) < h.rc.toInt := of_decide_eq_true hst
  have h_rc_int := toInt_eq_of_msb h.rc
  have h_rc_lt := h.rc.isLt
  have h_sub_nat : (0#32 - h.rc).toNat = (2 ^ 32 - h.rc.toNat) % 2 ^ 32 := by
    rw [BitVec.toNat_sub]
    simp
  have h_sub_int := toInt_eq_of_msb (0#32 - h.rc)
  apply decide_eq_true
  change (0#32 - h.rc).toInt < 0
  split at h_rc_int
  · have hpos_nat : 0 < h.rc.toNat ∧ h.rc.toNat < 2 ^ 31 := by omega
    have hmod : (2 ^ 32 - h.rc.toNat) % 2 ^ 32 = 2 ^ 32 - h.rc.toNat :=
      Nat.mod_eq_of_lt (by omega)
    rw [h_sub_nat, hmod] at h_sub_int
    split at h_sub_int <;> omega
  · omega

/-- `lean_mark_mt` is idempotent on persistent (`0`) and already-MT (`<_s 0`) headers. -/
theorem markMt_non_st_idempotent (h : LeanObjectHeader) (hnot_st : leanIsStRc h.rc = false) :
    stepMarkMtHeader h = h := by
  unfold stepMarkMtHeader
  rw [hnot_st]
  rfl

/-- Sticky MT counts (`rc ≤_s LEAN_RC_STICKY`) and persistent counts (`rc == 0`) are fixed points of `stepMtIncRefHeader`. -/
theorem mt_inc_ref_sticky_frozen (h : LeanObjectHeader) (n : BitVec 32)
    (hnot_st : leanIsStRc h.rc = false)
    (hfrozen : leanIsUnstuckMtUnsigned h.rc = false) :
    stepMtIncRefHeader h n = h := by
  unfold stepMtIncRefHeader
  simp [hnot_st, hfrozen]

/-- Any inline multi-threaded increment `1 ≤ n ≤ LEAN_RC_INC_MAX` (`0x10000`) on an unstuck MT header
    (`LEAN_RC_STICKY <_s rc <_s 0`) stays strictly negative (`<_s 0`), never wrapping past `INT32_MIN` into `st` or `0`. -/
theorem mt_inc_ref_stays_mt_no_underflow (h : LeanObjectHeader) (n : BitVec 32)
    (hunstuck : leanIsUnstuckMtUnsigned h.rc = true)
    (hn_pos : 1 ≤ n.toNat)
    (hn_max : n.toNat ≤ leanRcIncMax.toNat) :
    leanIsMtRc (stepMtIncRefHeader h n).rc = true ∧
    BitVec.slt leanInt32Min (stepMtIncRefHeader h n).rc = true := by
  have ⟨h_gt_sticky, h_mt⟩ := (isUnstuckMt_unsigned_iff_signed h.rc).mp hunstuck
  have hnot_st : leanIsStRc h.rc = false := by
    rcases rc_mode_partition h.rc with ⟨_, _, hmt_f⟩ | ⟨hst_f, _, _⟩ | ⟨hst_f, _, _⟩
    · rw [h_mt] at hmt_f; contradiction
    · exact hst_f
    · exact hst_f
  unfold stepMtIncRefHeader
  simp only [hnot_st, Bool.false_eq_true, ↓reduceIte, hunstuck]
  unfold leanIsUnstuckMtUnsigned BitVec.ult at hunstuck
  have h_ult : 2415919104 < h.rc.toNat := of_decide_eq_true hunstuck
  have h_n_le : n.toNat ≤ 65536 := hn_max
  have h_rc_lt := h.rc.isLt
  have h_sub_nat : (h.rc - n).toNat = h.rc.toNat - n.toNat := by
    rw [BitVec.toNat_sub_of_le]
    exact BitVec.le_def.mpr (by omega)
  have h_sub_int := toInt_eq_of_msb (h.rc - n)
  rw [h_sub_nat] at h_sub_int
  have h_not_msb : ¬(h.rc.toNat - n.toNat < 2 ^ 31) := by omega
  simp only [h_not_msb, ↓reduceIte] at h_sub_int
  unfold leanIsMtRc BitVec.slt
  have h0_int : (0#32).toInt = 0 := rfl
  have hmin_int : leanInt32Min.toInt = -2147483648 := rfl
  constructor <;> apply decide_eq_true <;> omega

/-- Sticky-drop MT headers (`rc ≤_s LEAN_RC_STICKY_DROP`) never adjust `m_rc` and never deallocate under `stepMtDecRefHeader`. -/
theorem mt_dec_ref_sticky_drop_never_frees (h : LeanObjectHeader)
    (hsle : BitVec.sle h.rc leanRcStickyDrop = true) :
    stepMtDecRefHeader h = (h, false) := by
  have h_drop_int : leanRcStickyDrop.toInt = -1610612736 := rfl
  have h_le : h.rc.toInt ≤ -1610612736 := by
    unfold BitVec.sle at hsle
    have := of_decide_eq_true hsle
    omega
  have hnot_gt1 : BitVec.slt 1#32 h.rc = false := by
    unfold BitVec.slt
    have : (1#32).toInt = 1 := rfl
    exact decide_eq_false (by omega)
  have hnot_eq1 : (h.rc == 1#32) = false := by
    cases hbeq : (h.rc == 1#32) with
    | false => rfl
    | true =>
      have heq : h.rc = 1#32 := of_decide_eq_true hbeq
      rw [heq] at h_le
      contradiction
  have hnot_st : leanIsStRc h.rc = false := by
    unfold leanIsStRc BitVec.slt
    have : (0#32).toInt = 0 := rfl
    exact decide_eq_false (by omega)
  have hnf : leanIsNeverFreedUnsigned h.rc = true :=
    (isNeverFreed_unsigned_iff_of_not_st h.rc hnot_st).mpr (Or.inr hsle)
  unfold stepMtDecRefHeader
  simp [hnot_gt1, hnot_eq1, hnf]

/-- On the last MT reference (`m_rc == -1`), `stepMtDecRefHeader` transitions `m_rc` to `0` and triggers deallocation (`true`). -/
theorem mt_dec_ref_last_triggers_free (h : LeanObjectHeader)
    (hlast : h.rc = -1#32) :
    stepMtDecRefHeader h = ({ h with rc := 0#32 }, true) := by
  unfold stepMtDecRefHeader
  rw [hlast]
  rfl

/-- On a shared unstuck MT header (`LEAN_RC_STICKY_DROP <_s rc <_s -1`), `stepMtDecRefHeader`
    increments `m_rc` to `rc + 1 <_s 0` without freeing (`false`) and without crossing into `0` or `st > 0`. -/
theorem mt_dec_ref_shared_stays_mt_live (h : LeanObjectHeader)
    (hgt_drop : BitVec.slt leanRcStickyDrop h.rc = true)
    (hlt_neg1 : BitVec.slt h.rc (-1#32) = true) :
    stepMtDecRefHeader h = ({ h with rc := h.rc + 1#32 }, false) ∧
    leanIsMtRc (h.rc + 1#32) = true := by
  have h1 : -1610612736 < h.rc.toInt := by
    unfold BitVec.slt at hgt_drop
    simpa [leanRcStickyDrop] using of_decide_eq_true hgt_drop
  have h2 : h.rc.toInt < -1 := by
    unfold BitVec.slt at hlt_neg1
    have hneg1 : (-1#32 : BitVec 32).toInt = -1 := rfl
    have := of_decide_eq_true hlt_neg1
    omega
  have hnot_gt1 : BitVec.slt 1#32 h.rc = false := by
    unfold BitVec.slt; have : (1#32).toInt = 1 := rfl; exact decide_eq_false (by omega)
  have hnot_eq1 : (h.rc == 1#32) = false := by
    cases hb : (h.rc == 1#32) with
    | false => rfl
    | true => have heq := of_decide_eq_true hb; rw [heq] at h2; contradiction
  have hnot_eq_neg1 : (h.rc == -1#32) = false := by
    cases hb : (h.rc == -1#32) with
    | false => rfl
    | true => have heq := of_decide_eq_true hb; rw [heq] at h2; contradiction
  have h_rc_int := toInt_eq_of_msb h.rc
  have h_rc_lt := h.rc.isLt
  have hnot_msb : ¬(h.rc.toNat < 2 ^ 31) := by split at h_rc_int <;> omega
  simp only [hnot_msb, ↓reduceIte] at h_rc_int
  have hnf_false : leanIsNeverFreedUnsigned h.rc = false := by
    unfold leanIsNeverFreedUnsigned BitVec.ule
    have : leanRcStickyDrop.toNat = 2684354560 := rfl
    exact decide_eq_false (by omega)
  have h_add_nat : (h.rc + 1#32).toNat = h.rc.toNat + 1 := by
    rw [BitVec.toNat_add]
    have : (1#32).toNat = 1 := rfl
    rw [this, Nat.mod_eq_of_lt (by omega)]
  have h_add_int := toInt_eq_of_msb (h.rc + 1#32)
  rw [h_add_nat] at h_add_int
  have h_add_not_msb : ¬(h.rc.toNat + 1 < 2 ^ 31) := by omega
  simp only [h_add_not_msb, ↓reduceIte] at h_add_int
  refine ⟨?_, ?_⟩
  · unfold stepMtDecRefHeader
    simp only [hnot_gt1, Bool.false_eq_true, ↓reduceIte, hnot_eq1, hnf_false, hnot_eq_neg1]
  · unfold leanIsMtRc BitVec.slt
    have : (0#32).toInt = 0 := rfl
    exact decide_eq_true (by omega)

/-! ## 2. `LEAN_LINEAR_MARK_MASK` (`0x80u`) Bit-Slice Isolation in `m_other` -/

/-- `LEAN_LINEAR_MARK_MASK` (`0x80u` in `lean.h:231`). -/
def leanLinearMarkMask : BitVec 8 := 0x80#8

/-- `lean_is_marked_linear_core` (`(o->m_other & 0x80u) != 0` in `lean.h:779`). -/
def leanIsMarkedLinearHeader (h : LeanObjectHeader) : Bool :=
  (h.other &&& leanLinearMarkMask) != 0#8

/-- `lean_sarray_elem_size` (`o->m_other & ~0x80u` in `lean.h:1222`). -/
def leanSarrayElemSizeHeader (h : LeanObjectHeader) : BitVec 8 :=
  h.other &&& (~~~leanLinearMarkMask)

/-- `lean_mark_linear_core` (`o->m_other |= 0x80u` in `lean.h:784`). -/
def stepMarkLinearHeader (h : LeanObjectHeader) : LeanObjectHeader :=
  { h with other := h.other ||| leanLinearMarkMask }

/-- Setting `LEAN_LINEAR_MARK_MASK` marks the header linear while preserving `m_rc`, `m_cs_sz`, `m_tag`,
    and the 7-bit `lean_sarray_elem_size` (`elem_size < 0x80`). -/
theorem markLinear_preserves_elem_size_and_header (h : LeanObjectHeader) :
    leanIsMarkedLinearHeader (stepMarkLinearHeader h) = true ∧
    leanSarrayElemSizeHeader (stepMarkLinearHeader h) = leanSarrayElemSizeHeader h ∧
    (stepMarkLinearHeader h).rc = h.rc ∧
    (stepMarkLinearHeader h).csSz = h.csSz ∧
    (stepMarkLinearHeader h).tag = h.tag := by
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · unfold leanIsMarkedLinearHeader stepMarkLinearHeader leanLinearMarkMask
    have hmask : ((h.other ||| 0x80#8) &&& 0x80#8) = 0x80#8 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [BitVec.getLsbD_and, BitVec.getLsbD_or]
      by_cases h7 : i = 7
      · subst h7
        have ht : (0x80#8).getLsbD 7 = true := rfl
        simp only [ht, Bool.or_true, Bool.and_true]
      · have hf : (0x80#8).getLsbD i = false := by
          have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
          rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        simp only [hf, Bool.or_false, Bool.and_false]
    rw [hmask]
    decide
  · unfold leanSarrayElemSizeHeader stepMarkLinearHeader leanLinearMarkMask
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_and]
    by_cases h7 : i = 7
    · subst h7
      have hnt : (~~~0x80#8 : BitVec 8).getLsbD 7 = false := rfl
      simp only [hnt, Bool.and_false]
    · have hf : (0x80#8).getLsbD i = false := by
        have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp only [hf, Bool.or_false]

/-- Every valid scalar-array `elem_size < 0x80` (`lean_alloc_sarray` guard `lean.h:1214`) starts unmarked
    and round-trips identically through `leanSarrayElemSizeHeader` before and after `stepMarkLinearHeader`. -/
theorem sarray_elem_size_roundtrip_under_markLinear (h : LeanObjectHeader)
    (helem : h.other.toNat < 0x80) :
    leanIsMarkedLinearHeader h = false ∧
    leanSarrayElemSizeHeader h = h.other ∧
    leanSarrayElemSizeHeader (stepMarkLinearHeader h) = h.other := by
  have hbit7 : h.other.getLsbD 7 = false := by
    have hshr : (h.other >>> 7).toNat = 0 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      omega
    have h0 : h.other >>> 7 = 0#8 := BitVec.eq_of_toNat_eq hshr
    have hb := congrArg (fun x => x.getLsbD 0) h0
    rw [BitVec.getLsbD_ushiftRight] at hb
    exact hb
  have hand0 : (h.other &&& leanLinearMarkMask) = 0#8 := by
    unfold leanLinearMarkMask
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and]
    by_cases h7 : i = 7
    · subst h7
      have hf0 : (0#8).getLsbD 7 = false := rfl
      simp only [hbit7, Bool.false_and, hf0]
    · have hf : (0x80#8).getLsbD i = false := by
        have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hf0 : (0#8).getLsbD i = false := by
        have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp only [hf, Bool.and_false, hf0]
  have helem_eq : leanSarrayElemSizeHeader h = h.other := by
    unfold leanSarrayElemSizeHeader leanLinearMarkMask
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and]
    by_cases h7 : i = 7
    · subst h7
      have hnt : (~~~0x80#8 : BitVec 8).getLsbD 7 = false := rfl
      simp only [hbit7, hnt, Bool.and_false]
    · have hnt : (~~~0x80#8 : BitVec 8).getLsbD i = true := by
        have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp only [hnt, Bool.and_true]
  refine ⟨?_, helem_eq, ?_⟩
  · unfold leanIsMarkedLinearHeader
    rw [hand0]
    decide
  · rw [(markLinear_preserves_elem_size_and_header h).2.1, helem_eq]

/-! ## 3. Runtime Tag Partitioning & LP64 Closure / Big-Object / External Byte Layouts -/

def leanMaxCtorTag : Nat := 243
def leanClosureTag : Nat := 245
def leanArrayTag : Nat := 246
def leanStructArrayTag : Nat := 247
def leanScalarArrayTag : Nat := 248
def leanStringTag : Nat := 249
def leanExternalTag : Nat := 254

def isCtorTag (tag : UInt8) : Bool := tag.toNat ≤ leanMaxCtorTag
def isClosureTag (tag : UInt8) : Bool := tag.toNat == leanClosureTag
def isBigObjectTag (tag : UInt8) : Bool :=
  tag.toNat == leanArrayTag || tag.toNat == leanStructArrayTag ||
  tag.toNat == leanScalarArrayTag || tag.toNat == leanStringTag
def isExternalTag (tag : UInt8) : Bool := tag.toNat == leanExternalTag

/-- Runtime object tag classes (`ctor`, `closure`, `big_object`, `external`) are pairwise disjoint (`lean.h:101-120`). -/
theorem runtime_tag_classes_disjoint (tag : UInt8) :
    ¬(isCtorTag tag = true ∧ isClosureTag tag = true) ∧
    ¬(isCtorTag tag = true ∧ isBigObjectTag tag = true) ∧
    ¬(isCtorTag tag = true ∧ isExternalTag tag = true) ∧
    ¬(isClosureTag tag = true ∧ isBigObjectTag tag = true) ∧
    ¬(isClosureTag tag = true ∧ isExternalTag tag = true) ∧
    ¬(isBigObjectTag tag = true ∧ isExternalTag tag = true) := by
  unfold isCtorTag isClosureTag isBigObjectTag isExternalTag
  unfold leanMaxCtorTag leanClosureTag leanArrayTag leanStructArrayTag leanScalarArrayTag leanStringTag leanExternalTag
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  omega

/-- LP64 `lean_closure_object` (`lean.h:233-239`) fixed-field offsets and widths:
    `0`: `m_header` `[0, 8)`, `1`: `m_fun` `[8, 16)`, `2`: `m_arity` `[16, 18)`,
    `3`: `m_num_fixed` `[18, 20)`, `4`: LP64 tail padding `[20, 24)` before `lean_object * m_objs[]` at `24`. -/
def closureFixedOffset : Fin 5 → Nat
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 8
  | ⟨2, _⟩ => 16
  | ⟨3, _⟩ => 18
  | ⟨4, _⟩ => 20

def closureFixedWidth : Fin 5 → Nat
  | ⟨0, _⟩ => 8
  | ⟨1, _⟩ => 8
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 2
  | ⟨4, _⟩ => 4

/-- Byte offset of captured argument pointer `m_objs[idx]` in `lean_closure_object` on LP64 (`24 + 8 * idx`). -/
def closureArgByteOffset (idx : Nat) : Nat := 24 + 8 * idx

/-- All 5 fixed regions of `lean_closure_object` (`m_header`, `m_fun`, `m_arity`, `m_num_fixed`, LP64 align pad)
    are pairwise byte-disjoint and strictly precede every captured `m_objs[idx]` slot (`[24 + 8*idx, 32 + 8*idx)`). -/
theorem closure_layout_fields_disjoint (f₁ f₂ : Fin 5) (b idx : Nat)
    (h₁ : f₁.val < 5) :
    ((closureFixedOffset f₁ ≤ b ∧ b < closureFixedOffset f₁ + closureFixedWidth f₁) →
      (closureFixedOffset f₂ ≤ b ∧ b < closureFixedOffset f₂ + closureFixedWidth f₂) →
      f₁ = f₂) ∧
    ((closureFixedOffset f₁ ≤ b ∧ b < closureFixedOffset f₁ + closureFixedWidth f₁) →
      b < closureArgByteOffset idx) := by
  let _ := h₁
  rcases f₁ with ⟨v₁, hv₁⟩
  rcases f₂ with ⟨v₂, hv₂⟩
  unfold closureFixedOffset closureFixedWidth closureArgByteOffset
  have hc₁ : v₁ = 0 ∨ v₁ = 1 ∨ v₁ = 2 ∨ v₁ = 3 ∨ v₁ = 4 := by omega
  have hc₂ : v₂ = 0 ∨ v₂ = 1 ∨ v₂ = 2 ∨ v₂ = 3 ∨ v₂ = 4 := by omega
  constructor
  · intro hb₁ hb₂
    rcases hc₁ with rfl | rfl | rfl | rfl | rfl <;>
    rcases hc₂ with rfl | rfl | rfl | rfl | rfl <;>
    simp_all <;> omega
  · intro hb₁
    rcases hc₁ with rfl | rfl | rfl | rfl | rfl <;>
    simp_all <;> omega

/-- LP64 `lean_external_object` (`lean.h:342-346`) fields (`m_header` `[0..8)`, `m_class` `[8..16)`, `m_data` `[16..24)`)
    partition `[0, 24)` into three disjoint 8-byte pointer-aligned words. -/
def externalFieldOffset (f : Fin 3) : Nat := 8 * f.val

theorem external_layout_fields_disjoint (f₁ f₂ : Fin 3) (b : Nat)
    (hb₁ : externalFieldOffset f₁ ≤ b ∧ b < externalFieldOffset f₁ + 8)
    (hb₂ : externalFieldOffset f₂ ≤ b ∧ b < externalFieldOffset f₂ + 8) :
    f₁ = f₂ := by
  rcases f₁ with ⟨v₁, hv₁⟩
  rcases f₂ with ⟨v₂, hv₂⟩
  unfold externalFieldOffset at hb₁ hb₂
  ext
  omega

/-- LP64 `lean_sarray_object` (`sizeof == 24`: `m_header` `[0..8)`, `m_size` `[8..16)`, `m_capacity` `[16..24)`,
    `m_data[]` at `24 + elemSize * idx`) keeps header/metadata disjoint from every element byte. -/
def sarrayHeaderFieldOffset (f : Fin 3) : Nat := 8 * f.val
def sarrayElemByteOffset (elemSize idx subByte : Nat) : Nat := 24 + elemSize * idx + subByte

theorem sarray_header_and_elems_disjoint (f : Fin 3) (b elemSize idx subI j subJ : Nat)
    (hb : sarrayHeaderFieldOffset f ≤ b ∧ b < sarrayHeaderFieldOffset f + 8)
    (hsubI : subI < elemSize) (hsubJ : subJ < elemSize) (hne : idx ≠ j) :
    b < sarrayElemByteOffset elemSize idx subI ∧
    sarrayElemByteOffset elemSize idx subI ≠ sarrayElemByteOffset elemSize j subJ := by
  rcases f with ⟨vf, hvf⟩
  unfold sarrayHeaderFieldOffset at hb
  unfold sarrayElemByteOffset
  refine ⟨by omega, ?_⟩
  intro heq
  by_cases hlt : idx < j
  · have hle : idx + 1 ≤ j := by omega
    have hmul : elemSize * (idx + 1) ≤ elemSize * j := Nat.mul_le_mul_left elemSize hle
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega
  · have hgt : j + 1 ≤ idx := by omega
    have hmul : elemSize * (j + 1) ≤ elemSize * idx := Nat.mul_le_mul_left elemSize hgt
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega

/-! ## 4. `lean_alloc_sarray_would_overflow` Soundness (`lean.h:432-448, 1203-1211`) -/

/-- Executable model of `lean_alloc_sarray_would_overflow(elem_size, capacity)` on LP64 (`sizeof(lean_sarray_object) = 24`,
    `SIZE_MAX = 2^64 - 1`). -/
def sarrayAllocWouldOverflow64 (elemSize capacity : Nat) : Bool :=
  let sizeMax := 2 ^ 64 - 1
  if elemSize != 0 && capacity > sizeMax / elemSize then
    true
  else
    24 > sizeMax - elemSize * capacity

/-- `sarrayAllocWouldOverflow64 elemSize capacity = false` iff the total byte allocation
    `24 + elemSize * capacity` strictly fits in 64-bit `size_t` (`< 2^64`). -/
theorem sarrayAllocWouldOverflow64_false_iff (elemSize capacity : Nat) :
    sarrayAllocWouldOverflow64 elemSize capacity = false ↔
      24 + elemSize * capacity < 2 ^ 64 := by
  unfold sarrayAllocWouldOverflow64
  by_cases he0 : elemSize = 0
  · subst he0
    simp
  · have he_pos : 0 < elemSize := Nat.pos_of_ne_zero he0
    have hne_true : (elemSize != 0) = true := by simp [bne, he0]
    simp only [hne_true, Bool.true_and]
    by_cases hmul_ovf : capacity > (2 ^ 64 - 1) / elemSize
    · simp only [hmul_ovf, decide_true, ↓reduceIte, Bool.true_eq_false, false_iff]
      have hdiv_lt : (2 ^ 64 - 1) / elemSize + 1 ≤ capacity := by omega
      have hmul_ge : elemSize * ((2 ^ 64 - 1) / elemSize + 1) ≤ elemSize * capacity :=
        Nat.mul_le_mul_left elemSize hdiv_lt
      have hmod := Nat.div_add_mod (2 ^ 64 - 1) elemSize
      have hrem_lt : (2 ^ 64 - 1) % elemSize < elemSize := Nat.mod_lt _ he_pos
      rw [Nat.mul_add, Nat.mul_one] at hmul_ge
      omega
    · have hcap_le : capacity ≤ (2 ^ 64 - 1) / elemSize := Nat.le_of_not_gt hmul_ovf
      have hprod_le : elemSize * capacity ≤ 2 ^ 64 - 1 := by
        have h1 : elemSize * capacity ≤ elemSize * ((2 ^ 64 - 1) / elemSize) :=
          Nat.mul_le_mul_left elemSize hcap_le
        have h2 : elemSize * ((2 ^ 64 - 1) / elemSize) ≤ 2 ^ 64 - 1 := Nat.mul_div_le _ _
        omega
      simp only [hmul_ovf, decide_false, Bool.false_eq_true, ↓reduceIte, decide_eq_false_iff_not]
      omega

/-! ### In-Kernel Transitive Axiom Gate (`Lean.collectAxioms`) -/

def heapObjMtAbiAuditedTheorems : List Lean.Name :=
  [ ``rc_mode_partition
  , ``isUnstuckMt_unsigned_iff_signed
  , ``isNeverFreed_unsigned_iff_of_not_st
  , ``markMt_st_becomes_mt
  , ``markMt_non_st_idempotent
  , ``mt_inc_ref_sticky_frozen
  , ``mt_inc_ref_stays_mt_no_underflow
  , ``mt_dec_ref_sticky_drop_never_frees
  , ``mt_dec_ref_last_triggers_free
  , ``mt_dec_ref_shared_stays_mt_live
  , ``markLinear_preserves_elem_size_and_header
  , ``sarray_elem_size_roundtrip_under_markLinear
  , ``runtime_tag_classes_disjoint
  , ``closure_layout_fields_disjoint
  , ``external_layout_fields_disjoint
  , ``sarray_header_and_elems_disjoint
  , ``sarrayAllocWouldOverflow64_false_iff
  ]

elab "#verify_heapobj_mt_abi_axioms" : command => do
  Lean.Elab.Command.liftCoreM do
    let allowed : List Lean.Name := [``propext, ``Quot.sound, ``Classical.choice]
    let env ← Lean.getEnv
    for declName in heapObjMtAbiAuditedTheorems do
      if !env.contains declName then
        Lean.throwError s!"[HeapObjMtAbiProofs] missing theorem {declName}"
      let axs := (← Lean.collectAxioms declName).toList
      let disallowed := axs.filter (!allowed.contains ·)
      if !disallowed.isEmpty then
        Lean.throwError s!"[HeapObjMtAbiProofs] theorem {declName} uses disallowed axioms: {disallowed}"

#verify_heapobj_mt_abi_axioms

end LeanNative.Proofs.HeapObjMtAbi
