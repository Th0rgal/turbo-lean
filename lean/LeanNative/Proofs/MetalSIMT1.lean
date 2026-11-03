import LeanNative.Backend.MetalAst.Proofs

namespace LeanNative.Proofs.MetalSIMT

open LeanNative.Backend.MetalAst

theorem writeLEAux_size (bs : Array UInt8) (addr : Nat) (val : BitVec 64) (w : Nat) :
    (ByteMemory.writeLEAux bs addr val w).size = bs.size := by
  induction w generalizing bs with
  | zero => rfl
  | succ k ih =>
    simp only [ByteMemory.writeLEAux]
    rw [ih, Array.size_setIfInBounds]

theorem writeLEAux_getElem?_outside (bs : Array UInt8) (addr : Nat) (val : BitVec 64) (w j : Nat)
    (hout : j < addr ∨ addr + w ≤ j) :
    (ByteMemory.writeLEAux bs addr val w)[j]? = bs[j]? := by
  induction w generalizing bs with
  | zero => rfl
  | succ k ih =>
    simp only [ByteMemory.writeLEAux]
    rw [ih _ (by omega)]
    by_cases hj : j < bs.size
    · have hj' : j < (bs.setIfInBounds (addr + k)
          (UInt8.ofNat ((val >>> (k * 8)).toNat % 256))).size := by
        rw [Array.size_setIfInBounds]; exact hj
      rw [Array.getElem?_eq_getElem hj', Array.getElem?_eq_getElem hj,
        Array.getElem_setIfInBounds (hj := hj)]
      split
      · omega
      · rfl
    · have hj' : ¬ j < (bs.setIfInBounds (addr + k)
          (UInt8.ofNat ((val >>> (k * 8)).toNat % 256))).size := by
        rw [Array.size_setIfInBounds]; exact hj
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt hj'),
        Array.getElem?_eq_none (Nat.le_of_not_lt hj)]

theorem writeLEAux_getElem?_inside (bs : Array UInt8) (addr : Nat) (val : BitVec 64) (w i : Nat)
    (hi : i < w) (hbound : addr + w ≤ bs.size) :
    (ByteMemory.writeLEAux bs addr val w)[addr + i]? =
      some (UInt8.ofNat ((val >>> (i * 8)).toNat % 256)) := by
  induction w generalizing bs with
  | zero => omega
  | succ k ih =>
    simp only [ByteMemory.writeLEAux]
    by_cases hik : i = k
    · subst hik
      rw [writeLEAux_getElem?_outside _ addr val i (addr + i) (Or.inr (Nat.le_refl _))]
      have hin : addr + i < bs.size := by omega
      have hin' : addr + i < (bs.setIfInBounds (addr + i)
          (UInt8.ofNat ((val >>> (i * 8)).toNat % 256))).size := by
        rw [Array.size_setIfInBounds]; exact hin
      rw [Array.getElem?_eq_getElem hin', Array.getElem_setIfInBounds (hj := hin)]
      split
      · rfl
      · omega
    · exact ih _ (by omega) (by rw [Array.size_setIfInBounds]; omega)

theorem readLEAux_eq_of_getElem?_eq (bs1 bs2 : Array UInt8) (addr w : Nat)
    (heq : ∀ i, i < w → bs1[addr + i]? = bs2[addr + i]?) :
    ByteMemory.readLEAux { bytes := bs1 } addr w =
      ByteMemory.readLEAux { bytes := bs2 } addr w := by
  induction w with
  | zero => rfl
  | succ k ih =>
    have ihk := ih (fun i hi => heq i (by omega))
    have hbk : ({ bytes := bs1 } : ByteMemory).bytes[addr + k]? =
        ({ bytes := bs2 } : ByteMemory).bytes[addr + k]? :=
      heq k (Nat.lt_succ_self k)
    simp only [ByteMemory.readLEAux, hbk, ihk]

theorem readLEAux_succ_of_eq (m : ByteMemory) (addr k : Nat) (b : UInt8) (rest : BitVec 64)
    (hb : m.bytes[addr + k]? = some b)
    (hr : ByteMemory.readLEAux m addr k = some rest) :
    ByteMemory.readLEAux m addr (k + 1) =
      some (rest ||| (BitVec.ofNat 64 b.toNat <<< (k * 8))) := by
  simp only [ByteMemory.readLEAux, hb, hr]

private def reconLE64 (val : BitVec 64) : Nat → BitVec 64
  | 0 => 0#64
  | n + 1 => reconLE64 val n ||| (((val >>> (n * 8)) &&& 0xFF#64) <<< (n * 8))

private theorem mask255_bit64 (d : Nat) (_ : d < 64) :
    (0xFF#64)[d] = decide (d < 8) := by
  rw [BitVec.getElem_eq_testBit_toNat]
  change (255 : Nat).testBit d = decide (d < 8)
  by_cases h8 : d < 8
  · match d, h8 with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl
  · have hlt2 : 255 < 2 ^ d := Nat.lt_of_lt_of_le (by decide : 255 < 2 ^ 8)
      (Nat.pow_le_pow_right (by decide) (by omega))
    simp [h8, Nat.testBit_lt_two_pow hlt2]

private theorem reconLE64_bit (val : BitVec 64) :
    ∀ k (bit : Nat) (_ : bit < 64),
      (reconLE64 val k)[bit] = (decide (bit < k * 8) && val[bit]) := by
  intro k; induction k with
  | zero => intro _ _; simp [reconLE64]
  | succ k ih =>
    intro bit hbit
    simp only [reconLE64, BitVec.getElem_or, ih bit hbit,
      BitVec.getElem_shiftLeft, BitVec.getElem_and, BitVec.getElem_ushiftRight]
    by_cases h1 : bit < k * 8
    · have h2 : bit < (k + 1) * 8 := by omega
      simp [h1, h2]
    · have hmask := mask255_bit64 (bit - k * 8) (by omega)
      have hidx : k * 8 + (bit - k * 8) = bit := by omega
      have hlsb : val.getLsbD bit = val[bit] := by
        simp [BitVec.getLsbD, BitVec.getElem_eq_testBit_toNat]
      by_cases h2 : bit < (k + 1) * 8
      · have hd8 : bit - k * 8 < 8 := by omega
        simp [h1, h2, hmask, hd8, hidx, hlsb]
      · have hd8 : ¬ (bit - k * 8 < 8) := by omega
        simp [h1, h2, hmask, hd8]

private theorem reconLE64_8 (val : BitVec 64) : reconLE64 val 8 = val := by
  ext bit hbit; rw [reconLE64_bit val 8 bit hbit]; simp [decide_eq_true hbit]

theorem readLEAux_of_bytes_8 (m : ByteMemory) (addr : Nat) (val : BitVec 64)
    (hget : ∀ i, i < 8 → m.bytes[addr + i]? =
      some (UInt8.ofNat ((val >>> (i * 8)).toNat % 256))) :
    ByteMemory.readLEAux m addr 8 = some val := by
  have hb : ∀ (k : Nat),
      BitVec.ofNat 64 (UInt8.ofNat ((val >>> (k * 8)).toNat % 256)).toNat =
      (val >>> (k * 8)) &&& 0xFF#64 := by
    intro k
    apply BitVec.eq_of_toNat_eq
    have h256 : 0 < 256 := by decide
    have hn : (UInt8.ofNat ((val >>> (k * 8)).toNat % 256)).toNat =
        (val >>> (k * 8)).toNat % 256 := by
      simp [Nat.mod_eq_of_lt (Nat.mod_lt _ h256)]
    have hand : ((val >>> (k * 8)) &&& 0xFF#64).toNat = (val >>> (k * 8)).toNat % 256 := by
      rw [BitVec.toNat_and]
      exact Nat.and_two_pow_sub_one_eq_mod (val >>> (k * 8)).toNat 8
    rw [BitVec.toNat_ofNat, hn, hand]
    have hlt64 : (val >>> (k * 8)).toNat % 256 < 2 ^ 64 :=
      Nat.lt_trans (Nat.mod_lt _ h256) (by decide)
    exact Nat.mod_eq_of_lt hlt64
  have haux : ∀ k, (∀ i < k, m.bytes[addr + i]? =
      some (UInt8.ofNat ((val >>> (i * 8)).toNat % 256))) →
      ByteMemory.readLEAux m addr k = some (reconLE64 val k) := by
    intro k; induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [readLEAux_succ_of_eq m addr k _ _ (hk k (by omega)) (ih fun i hi => hk i (by omega))]
      simp only [reconLE64, hb k]
  rw [haux 8 hget, reconLE64_8]

theorem readLEAux_writeLEAux_8 (bs : Array UInt8) (addr : Nat) (val : BitVec 64)
    (w : Nat) (hw : w = 8) (hbound : addr + w ≤ bs.size) :
    ByteMemory.readLEAux { bytes := ByteMemory.writeLEAux bs addr val w } addr w = some val := by
  have hget : ∀ i, i < 8 →
      ({ bytes := ByteMemory.writeLEAux bs addr val w } : ByteMemory).bytes[addr + i]? =
        some (UInt8.ofNat ((val >>> (i * 8)).toNat % 256)) := by
    intro i hi
    change (ByteMemory.writeLEAux bs addr val w)[addr + i]? = _
    exact writeLEAux_getElem?_inside bs addr val w i (by omega) hbound
  have h8 := readLEAux_of_bytes_8 { bytes := ByteMemory.writeLEAux bs addr val w } addr val hget
  simpa [hw] using h8

theorem fillU64Words_size (bs : Array UInt8) (idx : Nat) (words : List (BitVec 64)) :
    (ByteMemory.fillU64Words bs idx words).size = bs.size := by
  induction words generalizing bs idx with
  | nil => rfl
  | cons w rest ih =>
    simp only [ByteMemory.fillU64Words]
    rw [ih, writeLEAux_size]

theorem fillU64Words_getElem?_before (bs : Array UInt8) (idx : Nat) (words : List (BitVec 64))
    (j : Nat) (hbefore : j < idx * 8) :
    (ByteMemory.fillU64Words bs idx words)[j]? = bs[j]? := by
  induction words generalizing bs idx with
  | nil => rfl
  | cons w rest ih =>
    simp only [ByteMemory.fillU64Words]
    rw [ih _ (idx + 1) (by omega)]
    exact writeLEAux_getElem?_outside bs (idx * 8) w 8 j (Or.inl hbefore)

theorem fillU64Words_readLEAux (bs : Array UInt8) (idx : Nat) (words : List (BitVec 64))
    (k : Nat) (hk : k < words.length)
    (hbound : (idx + words.length) * 8 ≤ bs.size) :
    ByteMemory.readLEAux { bytes := ByteMemory.fillU64Words bs idx words }
      ((idx + k) * 8) 8 = some words[k] := by
  induction words generalizing bs idx k with
  | nil => simp at hk
  | cons w rest ih =>
    cases k with
    | zero =>
      simp only [ByteMemory.fillU64Words, Nat.add_zero, List.getElem_cons_zero]
      have hw : idx * 8 + 8 ≤ bs.size := by simp at hbound; omega
      let bs0 := ByteMemory.writeLEAux bs (idx * 8) w 8
      let bs1 := ByteMemory.fillU64Words bs0 (idx + 1) rest
      have heq : ByteMemory.readLEAux { bytes := bs1 } (idx * 8) 8 =
          ByteMemory.readLEAux { bytes := bs0 } (idx * 8) 8 :=
        readLEAux_eq_of_getElem?_eq bs1 bs0 (idx * 8) 8
          (fun i hi => fillU64Words_getElem?_before bs0 (idx + 1) rest (idx * 8 + i) (by omega))
      exact heq.trans (readLEAux_writeLEAux_8 bs (idx * 8) w 8 rfl hw)
    | succ k' =>
      simp only [ByteMemory.fillU64Words, List.getElem_cons_succ]
      have hrew : (idx + (k' + 1)) * 8 = ((idx + 1) + k') * 8 := by omega
      rw [hrew]
      exact ih (ByteMemory.writeLEAux bs (idx * 8) w 8) (idx + 1) k'
        (by simp at hk; omega)
        (by rw [writeLEAux_size]; simp at hbound ⊢; omega)

theorem ofU64Words_size (words : List (BitVec 64)) :
    (ByteMemory.ofU64Words words).bytes.size = words.length * 8 := by
  simp [ByteMemory.ofU64Words, fillU64Words_size]

theorem ofU64Words_readU64Word (words : List (BitVec 64)) (k : Nat) (hk : k < words.length) :
    (ByteMemory.ofU64Words words).readU64Word? k = some words[k] := by
  unfold ByteMemory.readU64Word? ByteMemory.loadBits ByteMemory.ofU64Words
  have hsz : (ByteMemory.fillU64Words (Array.replicate (words.length * 8) (0 : UInt8)) 0 words).size =
      words.length * 8 := by
    rw [fillU64Words_size, Array.size_replicate]
  dsimp only
  rw [hsz]
  have hle : k * 8 + 8 ≤ words.length * 8 := by omega
  simp only [gt_iff_lt, Nat.zero_lt_succ, decide_true, Bool.true_and, decide_eq_true hle, ite_true]
  simpa using fillU64Words_readLEAux (Array.replicate (words.length * 8) (0 : UInt8)) 0 words k hk (by simp)

theorem storeBits_8_eq (m : ByteMemory) (idx : Nat) (val : BitVec 64)
    (hbound : idx * 8 + 8 ≤ m.bytes.size) :
    m.storeBits (idx * 8) 8 val = some { bytes := ByteMemory.writeLEAux m.bytes (idx * 8) val 8 } := by
  unfold ByteMemory.storeBits
  simp only [gt_iff_lt, Nat.zero_lt_succ, decide_true, Bool.true_and, decide_eq_true hbound, ite_true]

theorem storeBits_8_size (m m' : ByteMemory) (idx : Nat) (val : BitVec 64)
    (h : m.storeBits (idx * 8) 8 val = some m') :
    m'.bytes.size = m.bytes.size := by
  unfold ByteMemory.storeBits at h
  simp only [gt_iff_lt, Nat.zero_lt_succ, decide_true, Bool.true_and] at h
  cases hcond : decide (idx * 8 + 8 ≤ m.bytes.size) <;> rw [hcond] at h
  · cases h
  · simp only [ite_true, Option.some.injEq] at h
    rw [← h, writeLEAux_size]

theorem storeBits_8_read_same (m m' : ByteMemory) (idx : Nat) (val : BitVec 64)
    (h : m.storeBits (idx * 8) 8 val = some m') :
    m'.readU64Word? idx = some val := by
  unfold ByteMemory.storeBits at h
  simp only [gt_iff_lt, Nat.zero_lt_succ, decide_true, Bool.true_and] at h
  cases hcond : decide (idx * 8 + 8 ≤ m.bytes.size) <;> rw [hcond] at h
  · cases h
  · simp only [ite_true, Option.some.injEq] at h
    have hbound : idx * 8 + 8 ≤ m.bytes.size := of_decide_eq_true hcond
    rw [← h]
    unfold ByteMemory.readU64Word? ByteMemory.loadBits
    dsimp only
    rw [writeLEAux_size]
    simp only [gt_iff_lt, Nat.zero_lt_succ, decide_true, Bool.true_and, hcond, ite_true]
    exact readLEAux_writeLEAux_8 m.bytes (idx * 8) val 8 rfl hbound

theorem storeBits_8_read_ne (m m' : ByteMemory) (idx j : Nat)
    (val : BitVec 64) (hne : j ≠ idx)
    (h : m.storeBits (idx * 8) 8 val = some m') :
    m'.readU64Word? j = m.readU64Word? j := by
  unfold ByteMemory.storeBits at h
  simp only [gt_iff_lt, Nat.zero_lt_succ, decide_true, Bool.true_and] at h
  cases hcond : decide (idx * 8 + 8 ≤ m.bytes.size) <;> rw [hcond] at h
  · cases h
  · simp only [ite_true, Option.some.injEq] at h
    rw [← h]
    unfold ByteMemory.readU64Word? ByteMemory.loadBits
    dsimp only
    rw [writeLEAux_size]
    simp only [gt_iff_lt, Nat.zero_lt_succ, decide_true, Bool.true_and]
    cases hjc : decide (j * 8 + 8 ≤ m.bytes.size)
    · simp only [Bool.false_eq_true, ite_false]
    · simp only [ite_true]
      cases m with
      | mk bs =>
        exact readLEAux_eq_of_getElem?_eq (ByteMemory.writeLEAux bs (idx * 8) val 8) bs (j * 8) 8
          (fun i hi => writeLEAux_getElem?_outside bs (idx * 8) val 8 (j * 8 + i) (by omega))

theorem promoteMSLArithType_ulong : promoteMSLArithType .ulong .ulong = .ulong := rfl

theorem finishBin_ulong_op (g : MSLGroupState) (a b : MSLExpr) (op : MSLBin)
    (ls : MSLLocals) (log : List MSLAccess) (va vb : BitVec 64)
    (fa fb : List (String × BitVec 64))
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    finishBin g a b op
      { value := va, fields := fa, locals := ls, log := log }
      { value := vb, fields := fb, locals := ls, log := log } =
      match evalTypedBin .ulong op va vb with
      | .ok v => .ok { value := v, locals := ls, log := log }
      | err => propagateErr err := by
  simp only [finishBin, hta, htb, promoteMSLArithType_ulong]
  rfl

theorem finishBitwise_ulong_op (g : MSLGroupState) (a b : MSLExpr)
    (op : BitVec 64 → BitVec 64 → BitVec 64)
    (ls : MSLLocals) (log : List MSLAccess) (va vb : BitVec 64)
    (fa fb : List (String × BitVec 64))
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    finishBitwise g a b op
      { value := va, fields := fa, locals := ls, log := log }
      { value := vb, fields := fb, locals := ls, log := log } =
      .ok { value := op va vb, locals := ls, log := log } := by
  simp [finishBitwise, hta, htb, promoteMSLArithType_ulong,
    MSLType.isFloat, MSLType.isVector, evalMSLCast, MSLType.isSigned, maskForType]

theorem finishCmp_ulong_op (g : MSLGroupState) (a b : MSLExpr) (op : MSLCmp)
    (ls : MSLLocals) (log : List MSLAccess) (va vb : BitVec 64)
    (fa fb : List (String × BitVec 64))
    (hta : inferExprType g ls a = .ulong) (htb : inferExprType g ls b = .ulong) :
    finishCmp g a b op
      { value := va, fields := fa, locals := ls, log := log }
      { value := vb, fields := fb, locals := ls, log := log } =
      match evalTypedCmp .ulong op va vb with
      | .ok v => .ok { value := v, locals := ls, log := log }
      | err => propagateErr err := by
  simp only [finishCmp, hta, htb, promoteMSLArithType_ulong]
  rfl

theorem finishShift_ulong_op (g : MSLGroupState) (a : MSLExpr) (right : Bool)
    (ls : MSLLocals) (log : List MSLAccess) (va vb : BitVec 64)
    (fa fb : List (String × BitVec 64))
    (hta : inferExprType g ls a = .ulong) (hlt : vb.toNat < 64) :
    finishShift g a right
      { value := va, fields := fa, locals := ls, log := log }
      { value := vb, fields := fb, locals := ls, log := log } =
      .ok { value := if right then va >>> vb.toNat else va <<< vb.toNat, locals := ls, log := log } := by
  have hge : ¬ (64 ≤ vb.toNat) := by omega
  cases right <;>
    simp [finishShift, hta, MSLType.isFloat, MSLType.isVector, MSLType.isSigned,
      MSLType.bitWidth, maskForType, hge]

theorem finishShift_long_sar_op (g : MSLGroupState) (a : MSLExpr)
    (ls : MSLLocals) (log : List MSLAccess) (va vb : BitVec 64)
    (fa fb : List (String × BitVec 64))
    (hta : inferExprType g ls a = .long) (hlt : vb.toNat < 64) :
    finishShift g a true
      { value := va, fields := fa, locals := ls, log := log }
      { value := vb, fields := fb, locals := ls, log := log } =
      .ok { value := va.sshiftRight vb.toNat, locals := ls, log := log } := by
  have hge : ¬ (64 ≤ vb.toNat) := by omega
  simp [finishShift, hta, MSLType.isFloat, MSLType.isVector, MSLType.isSigned,
    MSLType.bitWidth, maskForType, hge]

theorem lookup_setAssoc_same (xs : List (String × BitVec 64)) (k : String) (v : BitVec 64) :
    (MSLLocals.setAssoc xs k v).lookup k = some v := by
  induction xs with
  | nil => simp [MSLLocals.setAssoc]
  | cons hd tl ih =>
    cases hd with
    | mk k' v' =>
      simp only [MSLLocals.setAssoc]
      cases hk : k' == k
      · have hk' : (k == k') = false := by rw [BEq.comm]; exact hk
        simp only [Bool.false_eq_true, ite_false, List.lookup, hk']
        exact ih
      · simp only [ite_true, List.lookup, beq_self_eq_true]

theorem lookup_setAssoc_ne (xs : List (String × BitVec 64)) (k k' : String) (v : BitVec 64)
    (hne : k' ≠ k) :
    (MSLLocals.setAssoc xs k v).lookup k' = xs.lookup k' := by
  have hbeq : (k' == k) = false := beq_false_of_ne hne
  induction xs with
  | nil => simp only [MSLLocals.setAssoc, List.lookup, hbeq]
  | cons hd tl ih =>
    cases hd with
    | mk hk hv =>
      simp only [MSLLocals.setAssoc]
      cases h1 : hk == k
      · simp only [Bool.false_eq_true, ite_false, List.lookup]
        cases h2 : k' == hk
        · exact ih
        · rfl
      · have hk_eq : hk = k := beq_iff_eq.mp h1
        subst hk_eq
        simp only [ite_true, List.lookup, hbeq]

theorem lookup_setTypeAssoc_same (xs : List (String × MSLType)) (k : String) (t : MSLType) :
    (MSLLocals.setTypeAssoc xs k t).lookup k = some t := by
  induction xs with
  | nil => simp [MSLLocals.setTypeAssoc]
  | cons hd tl ih =>
    cases hd with
    | mk k' t' =>
      simp only [MSLLocals.setTypeAssoc]
      cases hk : k' == k
      · have hk' : (k == k') = false := by rw [BEq.comm]; exact hk
        simp only [Bool.false_eq_true, ite_false, List.lookup, hk']
        exact ih
      · simp only [ite_true, List.lookup, beq_self_eq_true]

theorem setTyped_lookup_same (ls : MSLLocals) (name : String) (ty : MSLType) (v : BitVec 64) :
    (ls.setTyped name ty v).lookup? name = some v ∧
    (ls.setTyped name ty v).lookupType? name = some ty := by
  simp only [MSLLocals.setTyped, MSLLocals.lookup?, MSLLocals.lookupType?]
  exact ⟨lookup_setAssoc_same ls.vars name v, lookup_setTypeAssoc_same ls.types name ty⟩

theorem lookup_setTypeAssoc_ne (xs : List (String × MSLType)) (k k' : String) (t : MSLType)
    (hne : k' ≠ k) :
    (MSLLocals.setTypeAssoc xs k t).lookup k' = xs.lookup k' := by
  have hbeq : (k' == k) = false := beq_false_of_ne hne
  induction xs with
  | nil => simp only [MSLLocals.setTypeAssoc, List.lookup, hbeq]
  | cons hd tl ih =>
    cases hd with
    | mk hk ht =>
      simp only [MSLLocals.setTypeAssoc]
      cases h1 : hk == k
      · simp only [Bool.false_eq_true, ite_false, List.lookup]
        cases h2 : k' == hk
        · exact ih
        · rfl
      · have hk_eq : hk = k := beq_iff_eq.mp h1
        subst hk_eq
        simp only [ite_true, List.lookup, hbeq]

theorem setTyped_lookup_ne (ls : MSLLocals) (name name' : String) (ty : MSLType) (v : BitVec 64)
    (hne : name' ≠ name) :
    (ls.setTyped name ty v).lookup? name' = ls.lookup? name' ∧
    (ls.setTyped name ty v).lookupType? name' = ls.lookupType? name' := by
  simp only [MSLLocals.setTyped, MSLLocals.lookup?, MSLLocals.lookupType?]
  exact ⟨lookup_setAssoc_ne ls.vars name name' v hne, lookup_setTypeAssoc_ne ls.types name name' ty hne⟩

theorem evalTypedBin_ulong (op : MSLBin) (va vb : BitVec 64) :
    evalTypedBin .ulong op va vb =
      match op with
      | .div => if vb == 0#64 then .divisionByZero else .ok (va / vb)
      | .rem => if vb == 0#64 then .divisionByZero else .ok (va % vb)
      | .add => .ok (va + vb)
      | .sub => .ok (va - vb)
      | .mul => .ok (va * vb) := by
  simp only [evalTypedBin, maskForType]
  cases op <;> rfl

theorem evalTypedCmp_ulong (op : MSLCmp) (va vb : BitVec 64) :
    evalTypedCmp .ulong op va vb =
      .ok (match op with
        | .eq => if va == vb then 1#64 else 0#64
        | .ne => if va != vb then 1#64 else 0#64
        | .lt => if BitVec.ult va vb then 1#64 else 0#64
        | .le => if BitVec.ule va vb then 1#64 else 0#64
        | .gt => if BitVec.ult vb va then 1#64 else 0#64
        | .ge => if BitVec.ule vb va then 1#64 else 0#64) := by
  simp only [evalTypedCmp, maskForType]
  cases op <;> rfl


private def unDigit (c : Char) : Nat := c.toNat - '0'.toNat
private def parseDigits : List Char → Nat → Nat
  | [], acc => acc
  | c :: cs, acc => parseDigits cs (acc * 10 + unDigit c)

private theorem unDigit_digitChar (d : Nat) (h : d < 10) :
    unDigit (Nat.digitChar d) = d := by
  match d, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => rfl

private theorem parseDigits_toDigitsCore :
    ∀ (fuel n : Nat) (cs : List Char), n < fuel →
      parseDigits (Nat.toDigitsCore 10 fuel n cs) 0 = parseDigits cs n
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, n, cs, hfuel => by
    unfold Nat.toDigitsCore
    dsimp only
    have hmod : n % 10 < 10 := Nat.mod_lt n (by decide)
    have hchar : unDigit (Nat.digitChar (n % 10)) = n % 10 := unDigit_digitChar (n % 10) hmod
    split
    · rename_i hdiv0
      have hn : n = n % 10 := by omega
      simp [parseDigits, hchar]
      rw [← hn]
    · rename_i hdiv0
      have hlt : n / 10 < fuel := by omega
      rw [parseDigits_toDigitsCore fuel (n / 10) (Nat.digitChar (n % 10) :: cs) hlt]
      have hdiv : n / 10 * 10 + n % 10 = n := by omega
      simp [parseDigits, hchar, hdiv]

theorem toString_nat_inj (a b : Nat) (h : toString a = toString b) : a = b := by
  have h1 : (Nat.repr a).toList = (Nat.repr b).toList := congrArg String.toList h
  simp only [Nat.repr, String.toList_ofList, Nat.toDigits] at h1
  have ha := parseDigits_toDigitsCore (a + 1) a [] (Nat.lt_succ_self a)
  have hb := parseDigits_toDigitsCore (b + 1) b [] (Nat.lt_succ_self b)
  rw [h1] at ha
  simpa [parseDigits] using ha.symm.trans hb

theorem prefix_nat_inj (pre : String) (a b : Nat)
    (h : pre ++ toString a = pre ++ toString b) : a = b := by
  have h1 : (pre ++ toString a).toList = (pre ++ toString b).toList := congrArg String.toList h
  simp only [String.toList_append] at h1
  exact toString_nat_inj a b (String.ext_iff.mpr (List.append_cancel_left h1))

theorem devBuf_beq_false {a b : Nat} (hne : a ≠ b) :
    (MSLMemTarget.deviceBuf a == MSLMemTarget.deviceBuf b) = false := by
  change (a == b) = false
  exact beq_false_of_ne hne


end LeanNative.Proofs.MetalSIMT
