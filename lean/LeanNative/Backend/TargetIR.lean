namespace LeanNative.Backend.TargetIR

abbrev RegName := String

abbrev BlockLabel := String

abbrev GlobalSym := String

abbrev AddrSpace := Nat

inductive IntWidth where
  | i1
  | i8
  | i16
  | i32
  | i64
  | i128
  | i256
  | i512
  deriving Repr, DecidableEq, Inhabited

namespace IntWidth

def bits : IntWidth → Nat
  | .i1 => 1
  | .i8 => 8
  | .i16 => 16
  | .i32 => 32
  | .i64 => 64
  | .i128 => 128
  | .i256 => 256
  | .i512 => 512

def byteSize : IntWidth → Nat
  | .i1 => 1
  | .i8 => 1
  | .i16 => 2
  | .i32 => 4
  | .i64 => 8
  | .i128 => 16
  | .i256 => 32
  | .i512 => 64

def naturalAlign : IntWidth → Nat
  | .i1 => 1
  | .i8 => 1
  | .i16 => 2
  | .i32 => 4
  | .i64 => 8
  | .i128 => 16
  | .i256 => 16
  | .i512 => 16

theorem naturalAlign_isPow2 (w : IntWidth) :
    (decide (0 < w.naturalAlign) && (w.naturalAlign &&& (w.naturalAlign - 1) == 0)) = true := by
  cases w <;> decide

def pp : IntWidth → String
  | .i1 => "i1"
  | .i8 => "i8"
  | .i16 => "i16"
  | .i32 => "i32"
  | .i64 => "i64"
  | .i128 => "i128"
  | .i256 => "i256"
  | .i512 => "i512"

theorem bits_pos (w : IntWidth) : 0 < w.bits := by
  cases w <;> decide

theorem byteSize_pos (w : IntWidth) : 0 < w.byteSize := by
  cases w <;> decide

theorem ppIntWidth_injective (w1 w2 : IntWidth)
    (h : w1.pp = w2.pp) : w1 = w2 := by
  cases w1 <;> cases w2
  all_goals
    simp [pp] at h
    try rfl

end IntWidth

inductive FloatWidth where
  | f32
  | f64
  deriving Repr, DecidableEq, Inhabited

namespace FloatWidth

def bits : FloatWidth → Nat
  | .f32 => 32
  | .f64 => 64

def byteSize : FloatWidth → Nat
  | .f32 => 4
  | .f64 => 8

def naturalAlign : FloatWidth → Nat
  | .f32 => 4
  | .f64 => 8

def pp : FloatWidth → String
  | .f32 => "float"
  | .f64 => "double"

theorem bits_eq_mul_eight (fw : FloatWidth) : fw.bits = 8 * fw.byteSize := by
  cases fw <;> rfl

theorem ppFloatWidth_injective (fw1 fw2 : FloatWidth)
    (h : fw1.pp = fw2.pp) : fw1 = fw2 := by
  cases fw1 <;> cases fw2
  all_goals
    simp [pp] at h
    try rfl

end FloatWidth

def isPow2 (a : Nat) : Bool :=
  decide (0 < a) && (a &&& (a - 1) == 0)

def nextPow2Aux (target : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | fuel + 1, acc =>
    if target ≤ acc then acc
    else nextPow2Aux target fuel (acc * 2)

def nextPow2 (n : Nat) : Nat :=
  if n ≤ 1 then 1 else nextPow2Aux n n 1

theorem nextPow2Aux_isPow2 (target fuel acc : Nat) (h : isPow2 acc = true) :
    isPow2 (nextPow2Aux target fuel acc) = true := by
  induction fuel generalizing acc with
  | zero => exact h
  | succ f ih =>
    simp only [nextPow2Aux]
    split
    · exact h
    · apply ih (acc * 2)
      unfold isPow2 at h ⊢
      rcases Bool.and_eq_true_iff.mp h with ⟨hpos, hand⟩
      have hp : 0 < acc := of_decide_eq_true hpos
      have ha0 : acc &&& (acc - 1) = 0 := beq_iff_eq.mp hand
      apply Bool.and_eq_true_iff.mpr
      refine ⟨decide_eq_true (by omega), beq_iff_eq.mpr ?_⟩
      have hdiv2 : ((acc * 2) &&& (acc * 2 - 1)) / 2 = acc &&& (acc - 1) := by
        have h1 : (acc * 2) / 2 = acc := by omega
        have h2 : (acc * 2 - 1) / 2 = acc - 1 := by omega
        have hd := @Nat.and_div_two_pow (acc * 2) (acc * 2 - 1) 1
        simp only [Nat.pow_one] at hd
        rw [hd, h1, h2]
      have hmod2 : ((acc * 2) &&& (acc * 2 - 1)) % 2 = 0 := by
        have hm := @Nat.and_mod_two_pow (acc * 2) (acc * 2 - 1) 1
        simp only [Nat.pow_one] at hm
        have heven : (acc * 2) % 2 = 0 := by omega
        rw [hm, heven, Nat.zero_and]
      omega

theorem nextPow2_isPow2 (n : Nat) : isPow2 (nextPow2 n) = true := by
  unfold nextPow2
  split
  · decide
  · exact nextPow2Aux_isPow2 n n 1 (by decide)

def isAligned (addr : BitVec 64) (align : Nat) : Bool :=
  isPow2 align && (addr.toNat % align == 0)

def rangesDisjoint (base1 sz1 base2 sz2 : Nat) : Bool :=
  decide (base1 + sz1 ≤ base2 ∨ base2 + sz2 ≤ base1)

theorem isAligned_one (addr : BitVec 64) :
    isAligned addr 1 = true := by
  simp [isAligned, isPow2, Nat.mod_one]

theorem isAligned_zero_false (addr : BitVec 64) :
    isAligned addr 0 = false := by
  rfl

theorem isAligned_add_multiple (addr : BitVec 64) (align k : Nat)
    (h_al : isAligned addr align = true)
    (h_fit : addr.toNat + k * align < 2 ^ 64) :
    isAligned (BitVec.ofNat 64 (addr.toNat + k * align)) align = true := by
  unfold isAligned at h_al ⊢
  rcases Bool.and_eq_true_iff.mp h_al with ⟨hp2, hmod⟩
  have hmod0 : addr.toNat % align = 0 := beq_iff_eq.mp hmod
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp2, beq_iff_eq.mpr ?_⟩
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_fit]
  rw [Nat.add_mul_mod_self_right, hmod0]

theorem rangesDisjoint_symm (b1 s1 b2 s2 : Nat) :
    rangesDisjoint b1 s1 b2 s2 = rangesDisjoint b2 s2 b1 s1 := by
  unfold rangesDisjoint
  by_cases h1 : b1 + s1 ≤ b2
  · simp [h1]
  · by_cases h2 : b2 + s2 ≤ b1 <;> simp [h1, h2]

theorem rangesDisjoint_ne_in_bounds (b1 s1 b2 s2 i j : Nat)
    (h_disj : rangesDisjoint b1 s1 b2 s2 = true)
    (hi : i < s1)
    (hj : j < s2) :
    b1 + i ≠ b2 + j := by
  unfold rangesDisjoint at h_disj
  have hor : b1 + s1 ≤ b2 ∨ b2 + s2 ≤ b1 := of_decide_eq_true h_disj
  omega

inductive MemByte where
  | init : BitVec 8 → MemByte
  | poisonByte : MemByte
  deriving Repr, DecidableEq, Inhabited

structure AllocBlock where
  base : Nat
  size : Nat
  align : Nat
  writable : Bool
  deriving Repr, DecidableEq, Inhabited

structure ByteMem where
  cells : List (Nat × MemByte) := []
  allocs : List AllocBlock := []
  nextAlloc : Nat := 4096
  deriving Repr, DecidableEq, Inhabited

namespace ByteMem

def empty : ByteMem := {}

def readCells (a : Nat) : List (Nat × MemByte) → Option MemByte
  | [] => none
  | (k, c) :: rest => if a == k then some c else readCells a rest

def readAt (m : ByteMem) (a : Nat) : Option MemByte :=
  readCells a m.cells

def writeAt (m : ByteMem) (a : Nat) (c : MemByte) : ByteMem :=
  { m with cells := (a, c) :: m.cells }

theorem readAt_writeAt_same (m : ByteMem) (a : Nat) (c : MemByte) :
    (m.writeAt a c).readAt a = some c := by
  simp [readAt, writeAt, readCells]

theorem readAt_writeAt_ne (m : ByteMem) (a1 a2 : Nat) (c : MemByte)
    (hne : a1 ≠ a2) :
    (m.writeAt a1 c).readAt a2 = m.readAt a2 := by
  have hbeq : (a2 == a1) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
  simp [readAt, writeAt, readCells, hbeq]

def writeBytesAt (m : ByteMem) (base : Nat) : List MemByte → ByteMem
  | [] => m
  | b :: bs => writeBytesAt (m.writeAt base b) (base + 1) bs

def readByte (m : ByteMem) (a : Nat) : MemByte :=
  match m.readAt a with
  | some b => b
  | none => .init 0#8

def readBytesAt (m : ByteMem) (base n : Nat) : List MemByte :=
  match n with
  | 0 => []
  | k + 1 => m.readByte base :: readBytesAt m (base + 1) k

theorem readBytesAt_length (m : ByteMem) (base n : Nat) :
    (m.readBytesAt base n).length = n := by
  induction n generalizing base with
  | zero => rfl
  | succ k ih =>
    simp [readBytesAt, ih]

theorem readAt_writeBytesAt_outside (m : ByteMem) (base : Nat) (bs : List MemByte) (q : Nat)
    (hout : q < base ∨ base + bs.length ≤ q) :
    (m.writeBytesAt base bs).readAt q = m.readAt q := by
  induction bs generalizing m base with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.length_cons] at hout
    have hne : base ≠ q := by omega
    have hout' : q < base + 1 ∨ (base + 1) + rest.length ≤ q := by omega
    simp only [writeBytesAt]
    rw [ih (m.writeAt base b) (base + 1) hout']
    exact readAt_writeAt_ne m base q b hne

theorem readBytesAt_writeBytesAt_same (m : ByteMem) (base : Nat) (bs : List MemByte) :
    (m.writeBytesAt base bs).readBytesAt base bs.length = bs := by
  induction bs generalizing m base with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.length_cons, writeBytesAt, readBytesAt]
    have hhead : ((m.writeAt base b).writeBytesAt (base + 1) rest).readByte base = b := by
      simp only [readByte]
      rw [readAt_writeBytesAt_outside (m.writeAt base b) (base + 1) rest base (Or.inl (by omega))]
      simp [readAt_writeAt_same]
    rw [hhead, ih (m.writeAt base b) (base + 1)]

theorem readBytesAt_writeBytesAt_disjoint (m : ByteMem) (b1 : Nat) (bs : List MemByte)
    (b2 n2 : Nat)
    (h_disj : rangesDisjoint b1 bs.length b2 n2 = true) :
    (m.writeBytesAt b1 bs).readBytesAt b2 n2 = m.readBytesAt b2 n2 := by
  have hor : b1 + bs.length ≤ b2 ∨ b2 + n2 ≤ b1 := of_decide_eq_true h_disj
  induction n2 generalizing b2 with
  | zero => rfl
  | succ k ih =>
    simp only [readBytesAt, readByte]
    have hout : b2 < b1 ∨ b1 + bs.length ≤ b2 := by omega
    have hdisj' : rangesDisjoint b1 bs.length (b2 + 1) k = true := by
      unfold rangesDisjoint
      exact decide_eq_true (by omega)
    have hor' : b1 + bs.length ≤ b2 + 1 ∨ b2 + 1 + k ≤ b1 := by omega
    rw [readAt_writeBytesAt_outside m b1 bs b2 hout, ih (b2 + 1) hdisj' hor']

def natToLEBytes : Nat → Nat → List (BitVec 8)
  | 0, _ => []
  | m + 1, x => BitVec.ofNat 8 (x % 256) :: natToLEBytes m (x / 256)

def natFromLEBytes : List (BitVec 8) → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * natFromLEBytes bs

theorem natFromLEBytes_lt (bs : List (BitVec 8)) :
    natFromLEBytes bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [natFromLEBytes]
  | cons b rest ih =>
    simp only [natFromLEBytes, List.length_cons, Nat.pow_succ]
    have hb : b.toNat < 256 := b.isLt
    omega

theorem natToLEBytes_length (n x : Nat) :
    (natToLEBytes n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ m ih => simp [natToLEBytes, ih]

theorem natToLEBytes_take (m k x : Nat) (h : k ≤ m) :
    (natToLEBytes m x).take k = natToLEBytes k x := by
  induction k generalizing m x with
  | zero => simp [natToLEBytes]
  | succ k' ih =>
    cases m with
    | zero => omega
    | succ m' =>
      simp only [natToLEBytes, List.take_succ_cons]
      rw [ih m' (x / 256) (by omega)]

theorem natToLEBytes_drop (m k x : Nat) (h : k ≤ m) :
    (natToLEBytes m x).drop k = natToLEBytes (m - k) (x / 256 ^ k) := by
  induction k generalizing m x with
  | zero => simp
  | succ k' ih =>
    cases m with
    | zero => omega
    | succ m' =>
      simp only [natToLEBytes, List.drop_succ_cons, Nat.succ_sub_succ_eq_sub]
      rw [ih m' (x / 256) (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_succ']

theorem natFromLEBytes_natToLEBytes_general (n x : Nat) :
    natFromLEBytes (natToLEBytes n x) = x % 256 ^ n := by
  induction n generalizing x with
  | zero => simp [natToLEBytes, natFromLEBytes, Nat.mod_one]
  | succ m ih =>
    simp only [natToLEBytes, natFromLEBytes, ih (x / 256)]
    have hmod8 : (BitVec.ofNat 8 (x % 256)).toNat = x % 256 := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (Nat.mod_lt x (by decide))
    rw [hmod8, Nat.pow_succ, Nat.mul_comm (256 ^ m) 256, Nat.mod_mul]

theorem natFromLEBytes_subslice (m off n x : Nat) (h : off + n ≤ m) :
    natFromLEBytes (((natToLEBytes m x).drop off).take n) = x / 256 ^ off % 256 ^ n := by
  rw [natToLEBytes_drop m off x (by omega), natToLEBytes_take (m - off) n (x / 256 ^ off) (by omega),
      natFromLEBytes_natToLEBytes_general]

theorem bits_le_eight_mul_byteSize (w : IntWidth) : w.bits ≤ 8 * w.byteSize := by
  cases w <;> decide

theorem pow256_eq (n : Nat) : 256 ^ n = 2 ^ (8 * n) := by
  have h256 : (256 : Nat) = 2 ^ 8 := by decide
  rw [h256, ← Nat.pow_mul]

theorem bits_le_byte_pow (w : IntWidth) : 2 ^ w.bits ≤ 256 ^ w.byteSize := by
  rw [pow256_eq]
  exact Nat.pow_le_pow_right (by decide) (bits_le_eight_mul_byteSize w)

def bvToLEBytes {k : Nat} (n : Nat) (v : BitVec k) : List (BitVec 8) :=
  natToLEBytes n v.toNat

def bvFromLEBytes (k : Nat) (bs : List (BitVec 8)) : BitVec k :=
  BitVec.ofNat k (natFromLEBytes bs)

theorem bvFromLEBytes_bvToLEBytes {k : Nat} (n : Nat) (v : BitVec k)
    (hk : k ≤ 8 * n) :
    bvFromLEBytes k (bvToLEBytes n v) = v := by
  unfold bvFromLEBytes bvToLEBytes
  have hpow : 2 ^ k ≤ 256 ^ n := by
    rw [pow256_eq]
    exact Nat.pow_le_pow_right (by decide) hk
  have hv : v.toNat < 256 ^ n := Nat.lt_of_lt_of_le v.isLt hpow
  rw [natFromLEBytes_natToLEBytes_general, Nat.mod_eq_of_lt hv, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem bvFromLEBytes_subslice {k : Nat} (m off n : Nat) (v : BitVec k)
    (h : off + n ≤ m) :
    bvFromLEBytes (8 * n) (((bvToLEBytes m v).drop off).take n) =
      BitVec.ofNat (8 * n) (v.toNat / 256 ^ off) := by
  unfold bvFromLEBytes bvToLEBytes
  rw [natFromLEBytes_subslice m off n v.toNat h, pow256_eq n]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat]

def initBytes : List (BitVec 8) → List MemByte
  | [] => []
  | b :: bs => .init b :: initBytes bs

def poisonBytes : Nat → List MemByte
  | 0 => []
  | k + 1 => .poisonByte :: poisonBytes k

def bytesToNat? : List MemByte → Option Nat
  | [] => some 0
  | .init b :: bs => do
    let rest ← bytesToNat? bs
    pure (b.toNat + 256 * rest)
  | .poisonByte :: _ => none

def bytesToBv? (k : Nat) (bs : List MemByte) : Option (BitVec k) :=
  (bytesToNat? bs).map (BitVec.ofNat k)

theorem initBytes_length (bs : List (BitVec 8)) :
    (initBytes bs).length = bs.length := by
  induction bs with
  | nil => rfl
  | cons b rest ih => simp [initBytes, ih]

theorem poisonBytes_length (n : Nat) :
    (poisonBytes n).length = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [poisonBytes, ih]

theorem bytesToNat?_initBytes (bs : List (BitVec 8)) :
    bytesToNat? (initBytes bs) = some (natFromLEBytes bs) := by
  induction bs with
  | nil => rfl
  | cons b rest ih => simp [initBytes, bytesToNat?, natFromLEBytes, ih]

theorem bytesToBv?_initBytes (k : Nat) (bs : List (BitVec 8)) :
    bytesToBv? k (initBytes bs) = some (bvFromLEBytes k bs) := by
  simp [bytesToBv?, bvFromLEBytes, bytesToNat?_initBytes]

def storeInt (m : ByteMem) (addr : BitVec 64) (w : IntWidth) (v : BitVec w.bits) : ByteMem :=
  m.writeBytesAt addr.toNat (initBytes (bvToLEBytes w.byteSize v))

def loadInt? (m : ByteMem) (addr : BitVec 64) (w : IntWidth) : Option (BitVec w.bits) :=
  bytesToBv? w.bits (m.readBytesAt addr.toNat w.byteSize)

def storePtr (m : ByteMem) (addr ptrVal : BitVec 64) : ByteMem :=
  m.storeInt addr .i64 ptrVal

def loadPtr? (m : ByteMem) (addr : BitVec 64) : Option (BitVec 64) :=
  m.loadInt? addr .i64

def storeFloatBits (m : ByteMem) (addr : BitVec 64) (fw : FloatWidth) (v : BitVec fw.bits) : ByteMem :=
  m.writeBytesAt addr.toNat (initBytes (bvToLEBytes fw.byteSize v))

def loadFloatBits? (m : ByteMem) (addr : BitVec 64) (fw : FloatWidth) : Option (BitVec fw.bits) :=
  bytesToBv? fw.bits (m.readBytesAt addr.toNat fw.byteSize)

def storePoison (m : ByteMem) (addr : BitVec 64) (n : Nat) : ByteMem :=
  m.writeBytesAt addr.toNat (poisonBytes n)

def isPoisonSlice (m : ByteMem) (addr : BitVec 64) (n : Nat) : Bool :=
  (m.readBytesAt addr.toNat n).any (fun b => b == .poisonByte)

theorem loadInt?_storeInt_same (m : ByteMem) (addr : BitVec 64) (w : IntWidth) (v : BitVec w.bits) :
    (m.storeInt addr w v).loadInt? addr w = some v := by
  simp only [storeInt, loadInt?]
  have hlen : (initBytes (bvToLEBytes w.byteSize v)).length = w.byteSize := by
    rw [initBytes_length, bvToLEBytes, natToLEBytes_length]
  have hrw := readBytesAt_writeBytesAt_same m addr.toNat (initBytes (bvToLEBytes w.byteSize v))
  rw [hlen] at hrw
  rw [hrw, bytesToBv?_initBytes, bvFromLEBytes_bvToLEBytes w.byteSize v (bits_le_eight_mul_byteSize w)]

theorem loadInt?_storeInt_disjoint (m : ByteMem) (a1 : BitVec 64) (w1 : IntWidth) (v : BitVec w1.bits)
    (a2 : BitVec 64) (w2 : IntWidth)
    (h_disj : rangesDisjoint a1.toNat w1.byteSize a2.toNat w2.byteSize = true) :
    (m.storeInt a1 w1 v).loadInt? a2 w2 = m.loadInt? a2 w2 := by
  simp only [storeInt, loadInt?]
  have hlen : (initBytes (bvToLEBytes w1.byteSize v)).length = w1.byteSize := by
    rw [initBytes_length, bvToLEBytes, natToLEBytes_length]
  rw [readBytesAt_writeBytesAt_disjoint m a1.toNat (initBytes (bvToLEBytes w1.byteSize v)) a2.toNat w2.byteSize]
  rw [hlen]
  exact h_disj

theorem readBytesAt_writeBytesAt_subslice (m : ByteMem) (base : Nat) (bs : List MemByte)
    (off n : Nat) (h : off + n ≤ bs.length) :
    (m.writeBytesAt base bs).readBytesAt (base + off) n = (bs.drop off).take n := by
  induction bs generalizing m base off n with
  | nil =>
    simp only [List.length_nil] at h
    have hn : n = 0 := by omega
    subst hn
    rfl
  | cons b rest ih =>
    simp only [List.length_cons] at h
    cases off with
    | zero =>
      simp only [Nat.add_zero, List.drop_zero]
      cases n with
      | zero => rfl
      | succ k =>
        simp only [writeBytesAt, readBytesAt, List.take_succ_cons]
        have hhead : ((m.writeAt base b).writeBytesAt (base + 1) rest).readByte base = b := by
          simp only [readByte]
          rw [readAt_writeBytesAt_outside (m.writeAt base b) (base + 1) rest base (Or.inl (by omega))]
          simp [readAt_writeAt_same]
        have htail := ih (m.writeAt base b) (base + 1) 0 k (by omega)
        simp only [Nat.add_zero, List.drop_zero] at htail
        rw [hhead, htail]
    | succ off' =>
      simp only [writeBytesAt, List.drop_succ_cons]
      have hadd : base + (off' + 1) = (base + 1) + off' := by omega
      rw [hadd]
      exact ih (m.writeAt base b) (base + 1) off' n (by omega)

theorem initBytes_drop (bs : List (BitVec 8)) (off : Nat) :
    (initBytes bs).drop off = initBytes (bs.drop off) := by
  induction bs generalizing off with
  | nil => simp [initBytes]
  | cons b rest ih =>
    cases off with
    | zero => rfl
    | succ off' => simp [initBytes, ih]

theorem initBytes_take (bs : List (BitVec 8)) (n : Nat) :
    (initBytes bs).take n = initBytes (bs.take n) := by
  induction bs generalizing n with
  | nil => simp [initBytes]
  | cons b rest ih =>
    cases n with
    | zero => rfl
    | succ k => simp [initBytes, ih]

theorem loadInt?_storeInt_subslice (m : ByteMem) (addr : BitVec 64)
    (wWide wNarrow : IntWidth) (v : BitVec wWide.bits) (off : Nat)
    (h_byte : wNarrow.bits = 8 * wNarrow.byteSize)
    (h_slice : off + wNarrow.byteSize ≤ wWide.byteSize)
    (h_fit : addr.toNat + off < 2 ^ 64) :
    (m.storeInt addr wWide v).loadInt? (BitVec.ofNat 64 (addr.toNat + off)) wNarrow =
      some (BitVec.ofNat wNarrow.bits (v.toNat / 256 ^ off)) := by
  simp only [storeInt, loadInt?]
  have haddr : (BitVec.ofNat 64 (addr.toNat + off)).toNat = addr.toNat + off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_fit]
  rw [haddr]
  have hlen : (initBytes (bvToLEBytes wWide.byteSize v)).length = wWide.byteSize := by
    rw [initBytes_length, bvToLEBytes, natToLEBytes_length]
  rw [readBytesAt_writeBytesAt_subslice m addr.toNat (initBytes (bvToLEBytes wWide.byteSize v))
        off wNarrow.byteSize (by omega)]
  rw [initBytes_drop, initBytes_take, bytesToBv?_initBytes]
  have hb := bvFromLEBytes_subslice wWide.byteSize off wNarrow.byteSize v h_slice
  rw [← h_byte] at hb
  rw [hb]

def alignUp (x align : Nat) : Nat :=
  if align ≤ 1 then x
  else
    let rem := x % align
    if rem == 0 then x else x + (align - rem)

theorem alignUp_ge (x align : Nat) : x ≤ alignUp x align := by
  unfold alignUp
  split
  · omega
  · dsimp only
    split <;> omega

theorem alignUp_mod_eq_zero (x align : Nat) (h_pos : 0 < align) :
    alignUp x align % align = 0 := by
  unfold alignUp
  by_cases h1 : align ≤ 1
  · have ha : align = 1 := by omega
    subst ha
    simp [Nat.mod_one]
  · simp only [h1, ↓reduceIte]
    by_cases hrem : x % align == 0
    · simp only [hrem, ↓reduceIte]
      exact beq_iff_eq.mp hrem
    · simp only [hrem, Bool.false_eq_true, ↓reduceIte]
      have hlt : x % align < align := Nat.mod_lt x h_pos
      have hdiv := Nat.div_add_mod x align
      have hmul : align * (x / align + 1) = align * (x / align) + align := Nat.mul_succ align (x / align)
      rw [show x + (align - x % align) = align * (x / align + 1) by omega]
      exact Nat.mul_mod_right _ _

def zeroBytes (n : Nat) : List MemByte :=
  List.replicate n (.init 0#8)

def effectiveAlign (align : Nat) : Nat :=
  if isPow2 align then align else 1

def allocAligned (m : ByteMem) (sizeBytes align : Nat) (writable : Bool := true) :
    Option (BitVec 64 × ByteMem) :=
  let base := alignUp (Nat.max m.nextAlloc 4096) (effectiveAlign align)
  let span := Nat.max sizeBytes 1
  if base + span < 2 ^ 64 then
    let block : AllocBlock :=
      { base := base, size := span, align := effectiveAlign align, writable := writable }
    let mZero := m.writeBytesAt base (zeroBytes span)
    some (BitVec.ofNat 64 base,
      { mZero with nextAlloc := base + span, allocs := block :: m.allocs })
  else
    none

def findAlloc (m : ByteMem) (addr : Nat) : Option AllocBlock :=
  m.allocs.find? (fun b => b.base ≤ addr && addr < b.base + b.size)

def accessInAlloc (m : ByteMem) (addr n : Nat) (needWrite : Bool) : Bool :=
  match m.findAlloc addr with
  | none => false
  | some b =>
    b.base ≤ addr && addr + n ≤ b.base + b.size && (!needWrite || b.writable)

def accessOk (m : ByteMem) (addr : BitVec 64) (n align : Nat) (needWrite : Bool) : Bool :=
  addr ≠ 0#64 && isAligned addr align && m.accessInAlloc addr.toNat n needWrite

def inboundsInAlloc (m : ByteMem) (basePtr : Nat) (resAddr : Int) : Bool :=
  if resAddr < 0 then false
  else
    let resNat := resAddr.toNat
    match m.allocs.find? (fun b => b.base ≤ basePtr && basePtr ≤ b.base + b.size) with
    | none => false
    | some b => b.base ≤ resNat && resNat ≤ b.base + b.size

theorem allocAligned_nonzero (m : ByteMem) (sz align : Nat) (writable : Bool)
    (ptr : BitVec 64) (m' : ByteMem)
    (h_alloc : m.allocAligned sz align writable = some (ptr, m')) :
    ptr ≠ 0#64 := by
  unfold allocAligned at h_alloc
  dsimp only at h_alloc
  split at h_alloc
  case isTrue hfit =>
    injection h_alloc with hpair
    injection hpair with hptr _
    subst hptr
    intro hzero
    have hnat : (BitVec.ofNat 64 (alignUp (Nat.max m.nextAlloc 4096) (effectiveAlign align))).toNat = 0 := by
      rw [hzero]; rfl
    rw [BitVec.toNat_ofNat] at hnat
    have hlt : alignUp (Nat.max m.nextAlloc 4096) (effectiveAlign align) < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hlt] at hnat
    have hge := alignUp_ge (Nat.max m.nextAlloc 4096) (effectiveAlign align)
    have hmax : 4096 ≤ Nat.max m.nextAlloc 4096 := Nat.le_max_right _ _
    omega
  case isFalse =>
    contradiction

theorem allocAligned_isAligned (m : ByteMem) (sz align : Nat) (writable : Bool)
    (ptr : BitVec 64) (m' : ByteMem)
    (h_pow : isPow2 align = true)
    (h_alloc : m.allocAligned sz align writable = some (ptr, m')) :
    isAligned ptr align = true := by
  unfold allocAligned effectiveAlign at h_alloc
  simp only [h_pow, ↓reduceIte] at h_alloc
  split at h_alloc
  case isTrue hfit =>
    injection h_alloc with hpair
    injection hpair with hptr _
    subst hptr
    have hpos : 0 < align := by
      unfold isPow2 at h_pow
      rcases Bool.and_eq_true_iff.mp h_pow with ⟨hp, _⟩
      exact of_decide_eq_true hp
    unfold isAligned
    apply Bool.and_eq_true_iff.mpr
    refine ⟨h_pow, beq_iff_eq.mpr ?_⟩
    have hlt : alignUp (Nat.max m.nextAlloc 4096) align < 2 ^ 64 := by omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    exact alignUp_mod_eq_zero (Nat.max m.nextAlloc 4096) align hpos
  case isFalse =>
    contradiction

theorem accessOk_null_false (m : ByteMem) (n align : Nat) (needWrite : Bool) :
    m.accessOk 0#64 n align needWrite = false := by
  simp [accessOk]

theorem accessOk_zero_align_false (m : ByteMem) (addr : BitVec 64) (n : Nat) (needWrite : Bool) :
    m.accessOk addr n 0 needWrite = false := by
  simp [accessOk, isAligned_zero_false]

theorem allocAligned_accessOk (m : ByteMem) (sz align : Nat) (writable : Bool)
    (ptr : BitVec 64) (m' : ByteMem)
    (h_pow : isPow2 align = true)
    (h_sz : 0 < sz)
    (h_alloc : m.allocAligned sz align writable = some (ptr, m')) :
    m'.accessOk ptr sz align writable = true := by
  have hnz := allocAligned_nonzero m sz align writable ptr m' h_alloc
  have hal := allocAligned_isAligned m sz align writable ptr m' h_pow h_alloc
  unfold accessOk
  simp only [hnz, ne_eq, not_false_eq_true, decide_true, hal, Bool.true_and]
  unfold allocAligned at h_alloc
  dsimp only at h_alloc
  split at h_alloc
  case isTrue hfit =>
    injection h_alloc with hpair
    injection hpair with hptr hm'
    subst hptr hm'
    have hspan : Nat.max sz 1 = sz := Nat.max_eq_left (by omega)
    have hbase_lt : alignUp (Nat.max m.nextAlloc 4096) (effectiveAlign align) < 2 ^ 64 := by omega
    have htoNat :
        (BitVec.ofNat 64 (alignUp (Nat.max m.nextAlloc 4096) (effectiveAlign align))).toNat =
          alignUp (Nat.max m.nextAlloc 4096) (effectiveAlign align) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbase_lt]
    unfold accessInAlloc findAlloc
    simp only [htoNat, hspan, List.find?_cons]
    have hlt : alignUp (Nat.max m.nextAlloc 4096) (effectiveAlign align) <
        alignUp (Nat.max m.nextAlloc 4096) (effectiveAlign align) + sz := by omega
    simp only [Nat.le_refl, decide_true, hlt, Bool.and_self]
    cases writable <;> rfl
  case isFalse =>
    contradiction

end ByteMem

inductive StepStatus (σ ρ : Type) where
  | cont : σ → StepStatus σ ρ
  | halt : ρ → StepStatus σ ρ
  | outOfFuel : StepStatus σ ρ
  | fault : String → StepStatus σ ρ
  deriving Repr, DecidableEq

def runFuelSteps {σ ρ : Type} (fuel : Nat) (step : σ → StepStatus σ ρ) (init : σ) : StepStatus σ ρ :=
  match fuel with
  | 0 => .outOfFuel
  | k + 1 =>
    match step init with
    | .cont next => runFuelSteps k step next
    | .halt res => .halt res
    | .outOfFuel => .outOfFuel
    | .fault msg => .fault msg

inductive StepFuel {σ ρ : Type} (step : σ → StepStatus σ ρ) : Nat → σ → StepStatus σ ρ → Prop where
  | zero (s : σ) : StepFuel step 0 s .outOfFuel
  | cont (k : Nat) (s next : σ) (out : StepStatus σ ρ) :
      step s = .cont next → StepFuel step k next out → StepFuel step (k + 1) s out
  | halt (k : Nat) (s : σ) (res : ρ) :
      step s = .halt res → StepFuel step (k + 1) s (.halt res)
  | outOfFuel (k : Nat) (s : σ) :
      step s = .outOfFuel → StepFuel step (k + 1) s .outOfFuel
  | fault (k : Nat) (s : σ) (msg : String) :
      step s = .fault msg → StepFuel step (k + 1) s (.fault msg)

theorem stepFuel_eq_runFuelSteps {σ ρ : Type} (fuel : Nat) (step : σ → StepStatus σ ρ)
    (s : σ) (out : StepStatus σ ρ)
    (h : StepFuel step fuel s out) :
    runFuelSteps fuel step s = out := by
  induction h with
  | zero => rfl
  | cont k s next out hstep _ ih =>
    simp [runFuelSteps, hstep, ih]
  | halt k s res hstep =>
    simp [runFuelSteps, hstep]
  | outOfFuel k s hstep =>
    simp [runFuelSteps, hstep]
  | fault k s msg hstep =>
    simp [runFuelSteps, hstep]

theorem runFuelSteps_deterministic {σ ρ : Type} (fuel : Nat) (step : σ → StepStatus σ ρ)
    (s : σ) (out1 out2 : StepStatus σ ρ)
    (h1 : StepFuel step fuel s out1)
    (h2 : StepFuel step fuel s out2) :
    out1 = out2 := by
  have e1 := stepFuel_eq_runFuelSteps fuel step s out1 h1
  have e2 := stepFuel_eq_runFuelSteps fuel step s out2 h2
  rw [← e1, e2]

theorem runFuelSteps_mono {σ ρ : Type} (f1 f2 : Nat) (step : σ → StepStatus σ ρ) (s : σ)
    (hle : f1 ≤ f2)
    (h_fin : runFuelSteps f1 step s ≠ .outOfFuel) :
    runFuelSteps f2 step s = runFuelSteps f1 step s := by
  induction f1 generalizing f2 s with
  | zero =>
    exfalso
    exact h_fin rfl
  | succ k ih =>
    cases f2 with
    | zero => omega
    | succ m =>
      have hkm : k ≤ m := by omega
      simp only [runFuelSteps] at h_fin ⊢
      cases hst : step s with
      | cont next =>
        rw [hst] at h_fin
        exact ih m next hkm h_fin
      | halt res => rfl
      | outOfFuel => rfl
      | fault msg => rfl

def digitChar : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | _ => '9'

def charDigit? : Char → Option Nat
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3 | '4' => some 4
  | '5' => some 5 | '6' => some 6 | '7' => some 7 | '8' => some 8 | '9' => some 9
  | _ => none

theorem charDigit?_digitChar (d : Nat) (hd : d < 10) :
    charDigit? (digitChar d) = some d := by
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => rfl
  | n + 10 => omega

def natDigitsAux : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    let d := digitChar (n % 10)
    if n < 10 then d :: acc
    else natDigitsAux fuel (n / 10) (d :: acc)

def natDigits (n : Nat) : List Char :=
  natDigitsAux (n + 1) n []

def ppInt (n : Nat) : String :=
  String.ofList (natDigits n)

def readDigits (acc : Nat) : List Char → Nat × List Char
  | [] => (acc, [])
  | c :: cs =>
    match charDigit? c with
    | some d => readDigits (acc * 10 + d) cs
    | none => (acc, c :: cs)

theorem readDigits_cons_digit (acc d : Nat) (hd : d < 10) (cs : List Char) :
    readDigits acc (digitChar d :: cs) = readDigits (acc * 10 + d) cs := by
  simp [readDigits, charDigit?_digitChar d hd]

theorem readDigits_natDigitsAux_zero (fuel n : Nat) (accDigits rest : List Char)
    (hfuel : n < fuel) :
    readDigits 0 (natDigitsAux fuel n accDigits ++ rest) =
      readDigits n (accDigits ++ rest) := by
  induction fuel generalizing n accDigits with
  | zero => omega
  | succ f ih =>
    simp only [natDigitsAux]
    have hmod : n % 10 < 10 := Nat.mod_lt n (by decide)
    by_cases hlt : n < 10
    · simp only [hlt, ↓reduceIte, List.cons_append, readDigits_cons_digit 0 (n % 10) hmod]
      have hmn : n % 10 = n := Nat.mod_eq_of_lt hlt
      simp [hmn]
    · simp only [hlt, ↓reduceIte]
      rw [ih (n / 10) (digitChar (n % 10) :: accDigits) (by omega)]
      simp only [List.cons_append, readDigits_cons_digit (n / 10) (n % 10) hmod]
      have hdiv : n / 10 * 10 + n % 10 = n := by omega
      rw [hdiv]

theorem readDigits_natDigits_delim (n : Nat) (c : Char) (cs : List Char)
    (h_stop : charDigit? c = none) :
    readDigits 0 (natDigits n ++ c :: cs) = (n, c :: cs) := by
  unfold natDigits
  rw [readDigits_natDigitsAux_zero (n + 1) n [] (c :: cs) (by omega)]
  simp [readDigits, h_stop]

theorem readDigits_natDigits_eof (n : Nat) :
    readDigits 0 (natDigits n) = (n, []) := by
  have h := readDigits_natDigitsAux_zero (n + 1) n [] [] (by omega)
  simp only [List.append_nil] at h
  unfold natDigits
  rw [h]
  rfl

end LeanNative.Backend.TargetIR
