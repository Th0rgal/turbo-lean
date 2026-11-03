import LeanNative.Backend.PTXAst.Proofs

namespace LeanNative.Proofs.PTXSIMT

open LeanNative.Backend.PTXAst


private def unDigit (c : Char) : Nat := c.toNat - '0'.toNat
private def parseDigits : List Char → Nat → Nat
  | [], acc => acc
  | c :: cs, acc => parseDigits cs (acc * 10 + unDigit c)

private theorem unDigit_digitChar (d : Nat) (h : d < 10) :
    unDigit (Nat.digitChar d) = d := by
  match d, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => rfl

private theorem parseDigits_toDigitsCore :
    ∀ (fuel n : Nat) (cs : List Char) (_ : n < fuel),
      parseDigits (Nat.toDigitsCore 10 fuel n cs) 0 = parseDigits cs n
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, n, cs, hfuel => by
    unfold Nat.toDigitsCore; dsimp only
    have hchar := unDigit_digitChar (n % 10) (Nat.mod_lt n (by decide))
    split
    · have hn : n = n % 10 := by omega
      simp [parseDigits, hchar]; rw [← hn]
    · rw [parseDigits_toDigitsCore fuel (n / 10) (Nat.digitChar (n % 10) :: cs) (by omega)]
      have hdiv : n / 10 * 10 + n % 10 = n := by omega
      simp [parseDigits, hchar, hdiv]

theorem nat_repr_inj (a b : Nat) (h : toString a = toString b) : a = b := by
  have h1 : (Nat.repr a).toList = (Nat.repr b).toList := congrArg String.toList h
  simp only [Nat.repr, String.toList_ofList, Nat.toDigits] at h1
  have ha := parseDigits_toDigitsCore (a + 1) a [] (Nat.lt_succ_self a)
  have hb := parseDigits_toDigitsCore (b + 1) b [] (Nat.lt_succ_self b)
  rw [h1] at ha; simpa [parseDigits] using ha.symm.trans hb

theorem regName_inj (pre : String) (a b : Nat)
    (h : s!"{pre}{a}" = s!"{pre}{b}") : a = b := by
  have h1 : (pre ++ toString a).toList = (pre ++ toString b).toList := congrArg String.toList h
  simp only [String.toList_append] at h1
  exact nat_repr_inj a b (String.ext_iff.mpr (List.append_cancel_left h1))

private theorem digit_head_isDigit (n : Nat) :
    ∃ c cs, (toString n).toList = c :: cs ∧ c ≠ 'd' := by
  have hd : (toString n).toList = Nat.toDigits 10 n := by
    change (Nat.repr n).toList = Nat.toDigits 10 n; simp [Nat.repr]
  rw [hd]; unfold Nat.toDigits Nat.toDigitsCore; dsimp only
  have hmod : n % 10 < 10 := Nat.mod_lt n (by decide)
  have hne : Nat.digitChar (n % 10) ≠ 'd' := by
    match h : n % 10, hmod with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => decide
  split
  · exact ⟨_, [], rfl, hne⟩
  · have haux : ∀ (f m : Nat) (acc : List Char), acc ≠ [] →
        ∃ c cs, Nat.toDigitsCore 10 f m acc = c :: cs ∧
          (c ∈ acc ∨ ∃ d < 10, c = Nat.digitChar d) := by
      intro f; induction f with
      | zero =>
        intro _ acc hacc; cases acc with
        | nil => contradiction
        | cons c cs => exact ⟨c, cs, rfl, Or.inl (List.Mem.head cs)⟩
      | succ f' ih =>
        intro m acc _; unfold Nat.toDigitsCore; dsimp only
        have hm10 : m % 10 < 10 := Nat.mod_lt m (by decide)
        split
        · exact ⟨_, acc, rfl, Or.inr ⟨m % 10, hm10, rfl⟩⟩
        · rcases ih (m / 10) (Nat.digitChar (m % 10) :: acc) (by simp) with ⟨c, cs, heq, hmem⟩
          refine ⟨c, cs, heq, ?_⟩
          rcases hmem with h1 | h2
          · rcases List.mem_cons.mp h1 with rfl | hrest
            · exact Or.inr ⟨m % 10, hm10, rfl⟩
            · exact Or.inl hrest
          · exact Or.inr h2
    rcases haux n (n / 10) [Nat.digitChar (n % 10)] (by simp) with ⟨c, cs, heq, hmem⟩
    refine ⟨c, cs, heq, ?_⟩
    rcases hmem with h1 | ⟨d, hd, rfl⟩
    · rw [List.mem_singleton.mp h1]; exact hne
    · match d, hd with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => decide

theorem p_ne_r (i j : Nat) : s!"%p{i}" ≠ s!"%r{j}" := by
  intro h; have h1 := congrArg String.toList h
  simp only [toString, String.toList_append] at h1
  change ('%' :: 'p' :: (toString i).toList) = ('%' :: 'r' :: (toString j).toList) at h1
  injection h1 with _ h2; injection h2 with hpr _
  exact absurd hpr (by decide)

theorem p_ne_rd (i j : Nat) : s!"%p{i}" ≠ s!"%rd{j}" := by
  intro h; have h1 := congrArg String.toList h
  simp only [toString, String.toList_append] at h1
  change ('%' :: 'p' :: (toString i).toList) = ('%' :: 'r' :: 'd' :: (toString j).toList) at h1
  injection h1 with _ h2; injection h2 with hpr _
  exact absurd hpr (by decide)

theorem r_ne_rd (i j : Nat) : s!"%r{i}" ≠ s!"%rd{j}" := by
  intro h; have h1 := congrArg String.toList h
  simp only [toString, String.toList_append] at h1
  change ('%' :: 'r' :: (toString i).toList) = ('%' :: 'r' :: 'd' :: (toString j).toList) at h1
  injection h1 with _ h2; injection h2 with _ h3
  rcases digit_head_isDigit i with ⟨c, cs, hci, hcne⟩
  rw [hci] at h3; injection h3 with hcd _
  exact hcne hcd

theorem setAssoc_lookup_self {α : Type} (xs : List (String × α)) (k : String) (v : α) :
    (PTXRegFile.setAssoc xs k v).lookup k = some v := by
  induction xs with
  | nil => simp [PTXRegFile.setAssoc]
  | cons kv rest ih =>
    rcases kv with ⟨k', v'⟩; simp only [PTXRegFile.setAssoc]
    cases hk : (k' == k)
    · have hsy : (k == k') = false := by
        cases hs : (k == k')
        · rfl
        · rw [eq_of_beq hs, beq_self_eq_true] at hk; cases hk
      simp [List.lookup, hsy, ih]
    · simp

theorem setAssoc_lookup_ne {α : Type} (xs : List (String × α)) (k q : String) (v : α)
    (hne : q ≠ k) :
    (PTXRegFile.setAssoc xs k v).lookup q = xs.lookup q := by
  induction xs with
  | nil => simp [PTXRegFile.setAssoc, List.lookup, beq_eq_false_iff_ne.mpr hne]
  | cons kv rest ih =>
    rcases kv with ⟨k', v'⟩; simp only [PTXRegFile.setAssoc]
    cases hk : (k' == k)
    · simp [List.lookup, ih]
    · rw [eq_of_beq hk]; simp [List.lookup, beq_eq_false_iff_ne.mpr hne]

theorem foldl_setAssoc_miss {α : Type} (pairs init : List (String × α)) (q : String)
    (hnm : q ∉ pairs.map Prod.fst) :
    (pairs.foldl (fun a (n, t) => PTXRegFile.setAssoc a n t) init).lookup q = init.lookup q := by
  induction pairs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.mem_cons, not_or] at hnm; simp only [List.foldl]
    rw [ih _ hnm.2, setAssoc_lookup_ne init x.1 q x.2 hnm.1]

theorem foldl_setAssoc_lookup {α : Type} (pairs init : List (String × α)) (q : String) (v : α)
    (hmem : (q, v) ∈ pairs) (hnodup : (pairs.map Prod.fst).Nodup) :
    (pairs.foldl (fun acc (nm, ty) => PTXRegFile.setAssoc acc nm ty) init).lookup q = some v := by
  induction pairs generalizing init with
  | nil => nomatch hmem
  | cons hd tl ih =>
    rcases hd with ⟨nm, ty⟩
    rw [List.map_cons, List.nodup_cons] at hnodup; rcases hnodup with ⟨hnotMem, hndTl⟩
    simp only [List.foldl]
    rcases List.mem_cons.mp hmem with heq | htl
    · injection heq with hq hv; subst hq hv
      rw [foldl_setAssoc_miss tl _ q hnotMem, setAssoc_lookup_self]
    · exact ih _ htl hndTl

def stdPTXRegDecls (nP nR nRd : Nat) : List PTXRegDecl :=
  [ { ty := .pred, prefixName := "%p", count := nP }
  , { ty := .u32, prefixName := "%r", count := nR }
  , { ty := .u64, prefixName := "%rd", count := nRd } ]

def RegTyped (rf : PTXRegFile) (nP nR nRd : Nat) : Prop :=
  rf.enforceDecls = true ∧
  (∀ i < nP, rf.decls.lookup s!"%p{i}" = some .pred) ∧
  (∀ i < nR, rf.decls.lookup s!"%r{i}" = some .u32) ∧
  (∀ i < nRd, rf.decls.lookup s!"%rd{i}" = some .u64)

private theorem nodup_map_regName (pre : String) (n : Nat) :
    ((List.range n).map fun i => s!"{pre}{i}").Nodup := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.nodup_append]
    refine ⟨ih, by simp, ?_⟩
    intro a ha b hb hab
    rcases List.mem_map.mp ha with ⟨ia, hia, rfl⟩
    rw [List.map_singleton, List.mem_singleton] at hb; subst hb
    have hEq := regName_inj pre ia m hab
    exact absurd hEq (Nat.ne_of_lt (List.mem_range.mp hia))

theorem ofRegDecls_regTyped (nP nR nRd : Nat) (hp : 0 < nP) (hr : 0 < nR) (hrd : 0 < nRd) :
    RegTyped (PTXRegFile.ofRegDecls (stdPTXRegDecls nP nR nRd)) nP nR nRd := by
  let lp := (List.range nP).map fun i => (s!"%p{i}", PTXType.pred)
  let lr := (List.range nR).map fun i => (s!"%r{i}", PTXType.u32)
  let lrd := (List.range nRd).map fun i => (s!"%rd{i}", PTXType.u64)
  have hexp : (stdPTXRegDecls nP nR nRd).flatMap PTXRegFile.expandSingleRegDecl =
      lp ++ (lr ++ lrd) := by
    have hp0 : (nP == 0) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hp)
    have hr0 : (nR == 0) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hr)
    have hrd0 : (nRd == 0) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hrd)
    simp [stdPTXRegDecls, PTXRegFile.expandSingleRegDecl, hp0, hr0, hrd0, lp, lr, lrd]
  have hnd : ((lp ++ (lr ++ lrd)).map Prod.fst).Nodup := by
    simp only [List.map_append, List.map_map, Function.comp_def, lp, lr, lrd]
    rw [List.nodup_append]
    refine ⟨nodup_map_regName "%p" nP, ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨nodup_map_regName "%r" nR, nodup_map_regName "%rd" nRd, ?_⟩
      intro a ha b hb hab
      rcases List.mem_map.mp ha with ⟨ia, _, rfl⟩
      rcases List.mem_map.mp hb with ⟨ib, _, rfl⟩
      exact r_ne_rd ia ib hab
    · intro a ha b hb hab
      rcases List.mem_map.mp ha with ⟨ia, _, rfl⟩
      rcases List.mem_append.mp hb with hbr | hbrd
      · rcases List.mem_map.mp hbr with ⟨ib, _, rfl⟩; exact p_ne_r ia ib hab
      · rcases List.mem_map.mp hbrd with ⟨ib, _, rfl⟩; exact p_ne_rd ia ib hab
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro i hi
    unfold PTXRegFile.ofRegDecls; dsimp only; rw [hexp]
    exact foldl_setAssoc_lookup _ [] _ _ (List.mem_append_left _ (List.mem_map_of_mem (List.mem_range.mpr hi))) hnd
  · intro i hi
    unfold PTXRegFile.ofRegDecls; dsimp only; rw [hexp]
    exact foldl_setAssoc_lookup _ [] _ _
      (List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem (List.mem_range.mpr hi)))) hnd
  · intro i hi
    unfold PTXRegFile.ofRegDecls; dsimp only; rw [hexp]
    exact foldl_setAssoc_lookup _ [] _ _
      (List.mem_append_right _ (List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.mpr hi)))) hnd

private theorem writeLE_size (bs : Array UInt8) (addr : Nat) (val : BitVec 64) :
    ∀ k, (ByteMemory.writeLittleEndianAux bs addr val k).size = bs.size := by
  intro k; induction k generalizing bs with
  | zero => rfl
  | succ k ih =>
    unfold ByteMemory.writeLittleEndianAux; rw [ih]; exact Array.size_setIfInBounds ..

private theorem writeLE_get_outside (bs : Array UInt8) (addr : Nat) (val : BitVec 64) :
    ∀ k j, (j < addr ∨ addr + k ≤ j) →
      (ByteMemory.writeLittleEndianAux bs addr val k)[j]? = bs[j]? := by
  intro k; induction k generalizing bs with
  | zero => intros; rfl
  | succ k ih =>
    intro j hout; unfold ByteMemory.writeLittleEndianAux
    rw [ih _ j (by omega), Array.getElem?_setIfInBounds_ne (by omega)]

private theorem writeLE_get_inside (bs : Array UInt8) (addr : Nat) (val : BitVec 64) :
    ∀ k i, i < k → addr + k ≤ bs.size →
      (ByteMemory.writeLittleEndianAux bs addr val k)[addr + i]? =
        some (UInt8.ofNat ((val >>> (i * 8)).toNat % 256)) := by
  intro k; induction k generalizing bs with
  | zero => intro _ hi; exact absurd hi (Nat.not_lt_zero _)
  | succ k ih =>
    intro i hi hsz; unfold ByteMemory.writeLittleEndianAux
    by_cases hik : i = k
    · subst hik
      rw [writeLE_get_outside _ addr val i (addr + i) (by omega), Array.getElem?_setIfInBounds_self]
      exact ite_eq_left_iff.mpr fun hc => absurd (by omega) hc
    · exact ih _ i (by omega) (by rw [Array.size_setIfInBounds]; omega)

private theorem readLE_cong (m1 m2 : ByteMemory) (addr : Nat) :
    ∀ k, (∀ i < k, m1.bytes[addr + i]? = m2.bytes[addr + i]?) →
      ByteMemory.readLittleEndianAux m1 addr k = ByteMemory.readLittleEndianAux m2 addr k := by
  intro k; induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h; unfold ByteMemory.readLittleEndianAux
    rw [h k (by omega), ih (fun i hi => h i (by omega))]

private theorem byteBv_eq (val : BitVec 64) (n : Nat) :
    BitVec.ofNat 64 (UInt8.ofNat ((val >>> (n * 8)).toNat % 256)).toNat =
      (val >>> (n * 8)) &&& 0xFF#64 := by
  have hm : ((val >>> (n * 8)).toNat % 256) % UInt8.size = (val >>> (n * 8)).toNat % 256 :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))
  apply BitVec.eq_of_toNat_eq
  simp only [UInt8.toNat_ofNat', hm, BitVec.toNat_ofNat, BitVec.toNat_and]
  have hlt : (val >>> (n * 8)).toNat % 256 < 2 ^ 64 :=
    Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  rw [Nat.mod_eq_of_lt hlt]
  change (val >>> (n * 8)).toNat % 256 = (val >>> (n * 8)).toNat &&& 255
  exact (Nat.and_two_pow_sub_one_eq_mod _ 8).symm

def reconLE (val : BitVec 64) : Nat → BitVec 64
  | 0 => 0#64
  | n + 1 => reconLE val n ||| (((val >>> (n * 8)) &&& 0xFF#64) <<< (n * 8))

private theorem mask255_bit (d : Nat) (_ : d < 64) :
    (0xFF#64)[d] = decide (d < 8) := by
  rw [BitVec.getElem_eq_testBit_toNat]
  change (255 : Nat).testBit d = decide (d < 8)
  by_cases h8 : d < 8
  · match d, h8 with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl
  · have hlt2 : 255 < 2 ^ d := Nat.lt_of_lt_of_le (by decide : 255 < 2 ^ 8)
      (Nat.pow_le_pow_right (by decide) (by omega))
    simp [h8, Nat.testBit_lt_two_pow hlt2]

private theorem reconLE_bit (val : BitVec 64) :
    ∀ k (bit : Nat) (_ : bit < 64),
      (reconLE val k)[bit] = (decide (bit < k * 8) && val[bit]) := by
  intro k; induction k with
  | zero => intro _ _; simp [reconLE]
  | succ k ih =>
    intro bit hbit
    simp only [reconLE, BitVec.getElem_or, ih bit hbit,
      BitVec.getElem_shiftLeft, BitVec.getElem_and, BitVec.getElem_ushiftRight]
    by_cases h1 : bit < k * 8
    · have h2 : bit < (k + 1) * 8 := by omega
      simp [h1, h2]
    · have hmask := mask255_bit (bit - k * 8) (by omega)
      have hidx : k * 8 + (bit - k * 8) = bit := by omega
      have hlsb : val.getLsbD bit = val[bit] := by
        simp [BitVec.getLsbD, BitVec.getElem_eq_testBit_toNat]
      by_cases h2 : bit < (k + 1) * 8
      · have hd8 : bit - k * 8 < 8 := by omega
        simp [h1, h2, hmask, hd8, hidx, hlsb]
      · have hd8 : ¬ (bit - k * 8 < 8) := by omega
        simp [h1, h2, hmask, hd8]

private theorem reconLE_8 (val : BitVec 64) : reconLE val 8 = val := by
  ext bit hbit; rw [reconLE_bit val 8 bit hbit]; simp [decide_eq_true hbit]

theorem readLE_from_bytes (m : ByteMemory) (addr : Nat) (val : BitVec 64) :
    ∀ k, (∀ i < k, m.bytes[addr + i]? = some (UInt8.ofNat ((val >>> (i * 8)).toNat % 256))) →
      ByteMemory.readLittleEndianAux m addr k = some (reconLE val k) := by
  intro k; induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h; unfold ByteMemory.readLittleEndianAux reconLE
    rw [h k (by omega), ih (fun i hi => h i (by omega))]
    dsimp only; rw [byteBv_eq]

theorem storeBits_eq_some_and_size (m : ByteMemory) (addr : Nat) (val : BitVec 64)
    (h : addr + 8 ≤ m.bytes.size) :
    ∃ m', m.storeBits addr 8 val = some m' ∧ m'.bytes.size = m.bytes.size ∧
      m'.loadBits addr 8 = some val ∧
      ∀ a2, (a2 + 8 ≤ addr ∨ addr + 8 ≤ a2) → m'.loadBits a2 8 = m.loadBits a2 8 := by
  have hex : ∃ bs', m.storeBits addr 8 val = some { bytes := bs' } ∧
      bs'.size = m.bytes.size ∧
      (∀ i < 8, bs'[addr + i]? = some (UInt8.ofNat ((val >>> (i * 8)).toNat % 256))) ∧
      (∀ j, (j < addr ∨ addr + 8 ≤ j) → bs'[j]? = m.bytes[j]?) := by
    refine ⟨ByteMemory.writeLittleEndianAux m.bytes addr val 8, ?_, ?_, ?_, ?_⟩
    · unfold ByteMemory.storeBits; exact ite_eq_left_iff.mpr fun hc => absurd h hc
    · exact writeLE_size m.bytes addr val 8
    · intro i hi; exact writeLE_get_inside m.bytes addr val 8 i hi h
    · intro j hj; exact writeLE_get_outside m.bytes addr val 8 j hj
  rcases hex with ⟨bs', hst, hsz, hin, hout⟩
  refine ⟨{ bytes := bs' }, hst, hsz, ?_, ?_⟩
  · unfold ByteMemory.loadBits; dsimp only
    rw [hsz, ite_eq_left_iff.mpr fun hc => absurd h hc,
        readLE_from_bytes { bytes := bs' } addr val 8 hin, reconLE_8]
  · intro a2 hdisj
    unfold ByteMemory.loadBits
    dsimp only
    rw [hsz]
    split
    · exact readLE_cong _ _ a2 8 fun i hi => hout (a2 + i) (by omega)
    · rfl

private theorem fillU64Words_size (ws : List (BitVec 64)) :
    ∀ (bs : Array UInt8) (idx : Nat), (ByteMemory.fillU64Words bs idx ws).size = bs.size := by
  induction ws with
  | nil => intros; rfl
  | cons w rest ih =>
    intro bs idx; unfold ByteMemory.fillU64Words; rw [ih, writeLE_size]

private theorem fillU64Words_get_before (ws : List (BitVec 64)) :
    ∀ (bs : Array UInt8) (idx j : Nat), j < idx * 8 →
      (ByteMemory.fillU64Words bs idx ws)[j]? = bs[j]? := by
  induction ws with
  | nil => intros; rfl
  | cons w rest ih =>
    intro bs idx j hj; unfold ByteMemory.fillU64Words
    rw [ih _ (idx + 1) j (by omega)]
    exact writeLE_get_outside bs (idx * 8) w 8 j (Or.inl hj)

private theorem fillU64Words_get_word (ws : List (BitVec 64)) :
    ∀ (bs : Array UInt8) (base i b : Nat) (hi : i < ws.length),
      b < 8 → (base + ws.length) * 8 ≤ bs.size →
      (ByteMemory.fillU64Words bs base ws)[(base + i) * 8 + b]? =
        some (UInt8.ofNat (((ws[i]'hi) >>> (b * 8)).toNat % 256)) := by
  induction ws with
  | nil => intro _ _ _ _ hi; exact absurd hi (Nat.not_lt_zero _)
  | cons w rest ih =>
    intro bs base i b hi hb hsz; unfold ByteMemory.fillU64Words
    cases i with
    | zero =>
      have hb0 : (base + 0) * 8 + b = base * 8 + b := by omega
      rw [hb0, fillU64Words_get_before rest _ (base + 1) (base * 8 + b) (by omega)]
      exact writeLE_get_inside bs (base * 8) w 8 b hb (by simp only [List.length_cons] at hsz; omega)
    | succ i' =>
      have hi' : i' < rest.length := by simp only [List.length_cons] at hi; omega
      have hsz' : (base + 1 + rest.length) * 8 ≤ (ByteMemory.writeLittleEndianAux bs (base * 8) w 8).size := by
        rw [writeLE_size]; simp only [List.length_cons] at hsz; omega
      have heq : (base + (i' + 1)) * 8 + b = (base + 1 + i') * 8 + b := by omega
      rw [heq]; exact ih _ (base + 1) i' b hi' hb hsz'

theorem ofU64Words_size (ws : List (BitVec 64)) :
    (ByteMemory.ofU64Words ws).bytes.size = ws.length * 8 := by
  simp [ByteMemory.ofU64Words, fillU64Words_size]

theorem ofU64Words_loadBits (ws : List (BitVec 64)) (i : Nat) (hi : i < ws.length) :
    (ByteMemory.ofU64Words ws).loadBits (i * 8) 8 = some (ws[i]'hi) := by
  have hex : ∃ bs', ByteMemory.ofU64Words ws = { bytes := bs' } ∧
      bs'.size = ws.length * 8 ∧
      (∀ b < 8, bs'[i * 8 + b]? = some (UInt8.ofNat (((ws[i]'hi) >>> (b * 8)).toNat % 256))) := by
    refine ⟨ByteMemory.fillU64Words (Array.replicate (ws.length * 8) 0) 0 ws, rfl, ?_, ?_⟩
    · rw [fillU64Words_size, Array.size_replicate]
    · intro b hb
      simpa using fillU64Words_get_word ws (Array.replicate (ws.length * 8) 0) 0 i b hi hb (by simp)
  rcases hex with ⟨bs', heq, hsz, hin⟩
  rw [heq]; unfold ByteMemory.loadBits; dsimp only
  have hle : i * 8 + 8 ≤ ws.length * 8 := by omega
  rw [hsz, ite_eq_left_iff.mpr fun hc => absurd hle hc,
      readLE_from_bytes { bytes := bs' } (i * 8) (ws[i]'hi) 8 hin, reconLE_8]

private theorem walk_halted_prefix (stmts : List PTXStmt) (cta : PTXCTAState)
    (done suffix : List PTXThreadState) (hdone : ∀ t ∈ done, t.halted = true) :
    ∀ pref, stepFirstReadyThread stmts cta pref (done ++ suffix) =
      stepFirstReadyThread stmts cta (done.reverse ++ pref) suffix := by
  induction done with
  | nil => intro pref; simp
  | cons d ds ih =>
    intro pref
    have hd : d.halted = true := hdone d (List.Mem.head ds)
    have hds : ∀ t ∈ ds, t.halted = true := fun t ht => hdone t (List.Mem.tail d ht)
    simp only [List.cons_append, stepFirstReadyThread, hd, ite_true, List.reverse_cons, List.append_assoc]
    exact ih hds (d :: pref)

theorem step_non_barrier_instr (stmts : List PTXStmt) (cta : PTXCTAState)
    (done : List PTXThreadState) (th : PTXThreadState) (todo : List PTXThreadState)
    (guard : Option PTXPredGuard) (ins : PTXInstr)
    (th' : PTXThreadState) (gMem' sMem' : ByteMemory) (log' : List MemAccessLog)
    (hthreads : cta.threads = done ++ (th :: todo))
    (hdone : ∀ t ∈ done, t.halted = true)
    (hnh : th.halted = false)
    (hpc : stmts[th.pc]? = some (.instr guard ins))
    (hnBar : ∀ b, ins ≠ .barSync b)
    (hnShfl : ∀ d s o c m, ins ≠ .shflSyncBfly d s o c m)
    (hexec : execPredicatedInstr stmts cta th guard ins = .ok (th', gMem', sMem', log')) :
    stepCTA stmts cta = .ok (false, { cta with
      threads := done ++ (th' :: todo)
      globalMem := gMem'
      sharedMem := sMem'
      epochLog := log' }) := by
  have hallFalse : cta.threads.all (·.halted) = false := by
    rw [hthreads, List.all_append, List.all_cons, hnh]; simp
  have hstep1 : stepFirstReadyThread stmts cta [] cta.threads = .ok (true, { cta with
      threads := done ++ (th' :: todo), globalMem := gMem', sharedMem := sMem', epochLog := log' }) := by
    rw [hthreads, walk_halted_prefix stmts cta done (th :: todo) hdone []]
    unfold stepFirstReadyThread
    rw [hnh, hpc, List.append_nil, List.reverse_reverse]
    cases ins <;> try (
      dsimp only
      rw [hexec]
      rfl)
    · exfalso; exact hnBar _ rfl
    · exfalso; exact hnShfl _ _ _ _ _ rfl
  unfold stepCTA
  rw [hallFalse, hstep1]; rfl

theorem step_label (stmts : List PTXStmt) (cta : PTXCTAState)
    (done : List PTXThreadState) (th : PTXThreadState) (todo : List PTXThreadState)
    (lbl : String)
    (hthreads : cta.threads = done ++ (th :: todo))
    (hdone : ∀ t ∈ done, t.halted = true)
    (hnh : th.halted = false)
    (hpc : stmts[th.pc]? = some (.label lbl)) :
    stepCTA stmts cta = .ok (false, { cta with
      threads := done ++ ({ th with pc := th.pc + 1 } :: todo) }) := by
  have hallFalse : cta.threads.all (·.halted) = false := by
    rw [hthreads, List.all_append, List.all_cons, hnh]; simp
  have hstep1 : stepFirstReadyThread stmts cta [] cta.threads = .ok (true, { cta with
      threads := done ++ ({ th with pc := th.pc + 1 } :: todo) }) := by
    rw [hthreads, walk_halted_prefix stmts cta done (th :: todo) hdone []]
    simp [stepFirstReadyThread, hnh, hpc]
  unfold stepCTA
  rw [hallFalse, hstep1]; rfl

theorem runCTAWithGlobalLog_step_no_clear (f : Nat) (stmts : List PTXStmt)
    (cta cta' : PTXCTAState) (saved : List MemAccessLog)
    (hstep : stepCTA stmts cta = .ok (false, cta'))
    (hnoClear : cta.epochLog = [] ∨ cta'.epochLog ≠ []) :
    runCTAWithGlobalLog (f + 1) stmts cta saved =
      runCTAWithGlobalLog f stmts cta' saved := by
  have hcond : (!cta.epochLog.isEmpty && cta'.epochLog.isEmpty) = false := by
    rcases hnoClear with h1 | h2
    · simp [h1]
    · cases hc : cta'.epochLog with
      | nil => exact absurd hc h2
      | cons _ _ => simp
  conv => lhs; unfold runCTAWithGlobalLog
  rw [hstep]; dsimp only [PTXOutcome.bind]
  rw [hcond]
  rfl

theorem runCTAWithGlobalLog_done_halted (f : Nat) (stmts : List PTXStmt)
    (cta : PTXCTAState) (saved : List MemAccessLog)
    (hhalt : cta.threads.all (·.halted) = true) :
    runCTAWithGlobalLog (f + 1) stmts cta saved =
      .ok (cta, cta.epochLog.filter (fun e => e.space == .global) ++ saved) := by
  have hstep : stepCTA stmts cta = .ok (true, cta) := by
    unfold stepCTA; simp [hhalt]
  have hcond : (!cta.epochLog.isEmpty && cta.epochLog.isEmpty) = false := by
    cases cta.epochLog <;> rfl
  conv => lhs; unfold runCTAWithGlobalLog
  rw [hstep]; dsimp only [PTXOutcome.bind]
  rw [hcond]
  rfl

end LeanNative.Proofs.PTXSIMT
