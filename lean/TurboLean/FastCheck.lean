/-
  TurboLean.FastCheck: Native Perceus/FBIP Counterexample Search Engine
  Compiles via `lean --c` + `leanc -O3` to check candidate 256-bit arithmetic & storage lemmas
  at >14M states/s on 1 CPU core.
-/
namespace TurboLean.FastCheck

structure Word256 where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  deriving DecidableEq, Repr

@[inline]
def Word256.zero : Word256 := ⟨0, 0, 0, 0⟩

@[inline]
def Word256.max : Word256 :=
  ⟨0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF⟩

@[inline]
def Word256.addWithCarry (a b : Word256) : Word256 × Bool :=
  let s0 := a.w0 + b.w0
  let c0 : UInt64 := if s0 < a.w0 then 1 else 0
  let s1_a := a.w1 + b.w1
  let c1_a : Bool := s1_a < a.w1
  let s1 := s1_a + c0
  let c1_b : Bool := s1 < s1_a
  let c1 : UInt64 := if c1_a || c1_b then 1 else 0
  let s2_a := a.w2 + b.w2
  let c2_a : Bool := s2_a < a.w2
  let s2 := s2_a + c1
  let c2_b : Bool := s2 < s2_a
  let c2 : UInt64 := if c2_a || c2_b then 1 else 0
  let s3_a := a.w3 + b.w3
  let c3_a : Bool := s3_a < a.w3
  let s3 := s3_a + c2
  let c3_b : Bool := s3 < s3_a
  let overflow := c3_a || c3_b
  (⟨s0, s1, s2, s3⟩, overflow)

@[inline]
def Word256.subWithBorrow (a b : Word256) : Word256 × Bool :=
  let d0 := a.w0 - b.w0
  let b0 : UInt64 := if a.w0 < b.w0 then 1 else 0
  let d1_a := a.w1 - b.w1
  let b1_a : Bool := a.w1 < b.w1
  let d1 := d1_a - b0
  let b1_b : Bool := d1_a < b0
  let b1 : UInt64 := if b1_a || b1_b then 1 else 0
  let d2_a := a.w2 - b.w2
  let b2_a : Bool := a.w2 < b.w2
  let d2 := d2_a - b1
  let b2_b : Bool := d2_a < b1
  let b2 : UInt64 := if b2_a || b2_b then 1 else 0
  let d3_a := a.w3 - b.w3
  let b3_a : Bool := a.w3 < b.w3
  let d3 := d3_a - b2
  let b3_b : Bool := d3_a < b2
  let underflow := b3_a || b3_b
  (⟨d0, d1, d2, d3⟩, underflow)

theorem addWithCarry_zero_right (a : Word256) :
    (Word256.addWithCarry a Word256.zero).2 = false := by
  simp [Word256.addWithCarry, Word256.zero]

set_option maxHeartbeats 200000 in
  theorem addWithCarry_zero_left (a : Word256) :
      (Word256.addWithCarry Word256.zero a).2 = false := by
    simp only [Word256.addWithCarry, Word256.zero, UInt64.zero_add, UInt64.not_lt_zero,
      UInt64.add_zero, UInt64.lt_irrefl, decide_false, Bool.false_eq_true, ↓reduceIte, Bool.or_self]

theorem addWithCarry_comm_low (a b : Word256) :
    (Word256.addWithCarry a b).1.w0 = (Word256.addWithCarry b a).1.w0 := by
  simp [Word256.addWithCarry, UInt64.add_comm]

set_option maxHeartbeats 200000 in
  theorem subWithBorrow_zero_right (a : Word256) :
      Word256.subWithBorrow a Word256.zero = (a, false) := by
    rcases a with ⟨w0, w1, w2, w3⟩
    simp only [Word256.subWithBorrow, Word256.zero, UInt64.sub_zero, UInt64.not_lt_zero,
      decide_false, Bool.false_eq_true, ↓reduceIte, Bool.or_self]

set_option maxHeartbeats 200000 in
  theorem subWithBorrow_self_no_borrow (a : Word256) :
      (Word256.subWithBorrow a a).2 = false := by
    simp only [Word256.subWithBorrow, UInt64.sub_self, UInt64.lt_irrefl,
      decide_false, Bool.false_eq_true, ↓reduceIte, Bool.or_self]

@[inline]
def Word256.bitAnd (a b : Word256) : Word256 :=
  ⟨a.w0 &&& b.w0, a.w1 &&& b.w1, a.w2 &&& b.w2, a.w3 &&& b.w3⟩

@[inline]
def Word256.bitOr (a b : Word256) : Word256 :=
  ⟨a.w0 ||| b.w0, a.w1 ||| b.w1, a.w2 ||| b.w2, a.w3 ||| b.w3⟩

@[inline]
def Word256.bitXor (a b : Word256) : Word256 :=
  ⟨a.w0 ^^^ b.w0, a.w1 ^^^ b.w1, a.w2 ^^^ b.w2, a.w3 ^^^ b.w3⟩

def Word256.ext {a b : Word256}
    (h0 : a.w0 = b.w0) (h1 : a.w1 = b.w1) (h2 : a.w2 = b.w2) (h3 : a.w3 = b.w3) : a = b := by
  cases a; cases b; subst h0 h1 h2 h3; rfl

set_option maxHeartbeats 200000 in
  theorem bitAnd_self (a : Word256) :
      Word256.bitAnd a a = a :=
    Word256.ext UInt64.and_self UInt64.and_self UInt64.and_self UInt64.and_self

set_option maxHeartbeats 200000 in
  theorem bitOr_self (a : Word256) :
      Word256.bitOr a a = a :=
    Word256.ext UInt64.or_self UInt64.or_self UInt64.or_self UInt64.or_self

set_option maxHeartbeats 200000 in
  theorem bitAnd_comm (a b : Word256) :
      Word256.bitAnd a b = Word256.bitAnd b a :=
    Word256.ext (UInt64.and_comm _ _) (UInt64.and_comm _ _) (UInt64.and_comm _ _) (UInt64.and_comm _ _)

set_option maxHeartbeats 200000 in
  theorem bitOr_comm (a b : Word256) :
      Word256.bitOr a b = Word256.bitOr b a :=
    Word256.ext (UInt64.or_comm _ _) (UInt64.or_comm _ _) (UInt64.or_comm _ _) (UInt64.or_comm _ _)

set_option maxHeartbeats 200000 in
  theorem bitXor_comm (a b : Word256) :
      Word256.bitXor a b = Word256.bitXor b a :=
    Word256.ext (UInt64.xor_comm _ _) (UInt64.xor_comm _ _) (UInt64.xor_comm _ _) (UInt64.xor_comm _ _)

set_option maxHeartbeats 200000 in
  theorem bitAnd_zero_right (a : Word256) :
      Word256.bitAnd a Word256.zero = Word256.zero :=
    Word256.ext UInt64.and_zero UInt64.and_zero UInt64.and_zero UInt64.and_zero

set_option maxHeartbeats 200000 in
  theorem bitOr_zero_right (a : Word256) :
      Word256.bitOr a Word256.zero = a :=
    Word256.ext UInt64.or_zero UInt64.or_zero UInt64.or_zero UInt64.or_zero

set_option maxHeartbeats 200000 in
  theorem bitXor_zero_right (a : Word256) :
      Word256.bitXor a Word256.zero = a :=
    Word256.ext UInt64.xor_zero UInt64.xor_zero UInt64.xor_zero UInt64.xor_zero

set_option maxHeartbeats 200000 in
  theorem bitXor_self_zero (a : Word256) :
      Word256.bitXor a a = Word256.zero :=
    Word256.ext UInt64.xor_self UInt64.xor_self UInt64.xor_self UInt64.xor_self

set_option maxHeartbeats 200000 in
  theorem bitAnd_zero_left (a : Word256) :
      Word256.bitAnd Word256.zero a = Word256.zero :=
    Word256.ext UInt64.zero_and UInt64.zero_and UInt64.zero_and UInt64.zero_and

set_option maxHeartbeats 200000 in
  theorem bitOr_zero_left (a : Word256) :
      Word256.bitOr Word256.zero a = a :=
    Word256.ext UInt64.zero_or UInt64.zero_or UInt64.zero_or UInt64.zero_or

set_option maxHeartbeats 200000 in
  theorem bitXor_zero_left (a : Word256) :
      Word256.bitXor Word256.zero a = a :=
    Word256.ext UInt64.zero_xor UInt64.zero_xor UInt64.zero_xor UInt64.zero_xor

@[inline]
def Word256.bitNot (a : Word256) : Word256 :=
  ⟨~~~a.w0, ~~~a.w1, ~~~a.w2, ~~~a.w3⟩

set_option maxHeartbeats 200000 in
  theorem bitNot_zero_eq_max :
      Word256.bitNot Word256.zero = Word256.max :=
    rfl

set_option maxHeartbeats 200000 in
  theorem bitNot_max_eq_zero :
      Word256.bitNot Word256.max = Word256.zero :=
    rfl

set_option maxHeartbeats 200000 in
  theorem bitAnd_assoc (a b c : Word256) :
      Word256.bitAnd (Word256.bitAnd a b) c = Word256.bitAnd a (Word256.bitAnd b c) :=
    Word256.ext (UInt64.and_assoc _ _ _) (UInt64.and_assoc _ _ _) (UInt64.and_assoc _ _ _) (UInt64.and_assoc _ _ _)

set_option maxHeartbeats 200000 in
  theorem bitOr_assoc (a b c : Word256) :
      Word256.bitOr (Word256.bitOr a b) c = Word256.bitOr a (Word256.bitOr b c) :=
    Word256.ext (UInt64.or_assoc _ _ _) (UInt64.or_assoc _ _ _) (UInt64.or_assoc _ _ _) (UInt64.or_assoc _ _ _)

set_option maxHeartbeats 200000 in
  theorem bitXor_assoc (a b c : Word256) :
      Word256.bitXor (Word256.bitXor a b) c = Word256.bitXor a (Word256.bitXor b c) :=
    Word256.ext (UInt64.xor_assoc _ _ _) (UInt64.xor_assoc _ _ _) (UInt64.xor_assoc _ _ _) (UInt64.xor_assoc _ _ _)

set_option maxHeartbeats 200000 in
  theorem bitXor_cancel_right (a b : Word256) :
      Word256.bitXor (Word256.bitXor a b) b = a :=
    Word256.ext
      ((UInt64.xor_assoc _ _ _).trans ((congrArg (a.w0 ^^^ ·) UInt64.xor_self).trans UInt64.xor_zero))
      ((UInt64.xor_assoc _ _ _).trans ((congrArg (a.w1 ^^^ ·) UInt64.xor_self).trans UInt64.xor_zero))
      ((UInt64.xor_assoc _ _ _).trans ((congrArg (a.w2 ^^^ ·) UInt64.xor_self).trans UInt64.xor_zero))
      ((UInt64.xor_assoc _ _ _).trans ((congrArg (a.w3 ^^^ ·) UInt64.xor_self).trans UInt64.xor_zero))

set_option maxHeartbeats 200000 in
  theorem bitXor_cancel_left (a b : Word256) :
      Word256.bitXor b (Word256.bitXor b a) = a :=
    Word256.ext
      ((UInt64.xor_assoc _ _ _).symm.trans ((congrArg (· ^^^ a.w0) UInt64.xor_self).trans UInt64.zero_xor))
      ((UInt64.xor_assoc _ _ _).symm.trans ((congrArg (· ^^^ a.w1) UInt64.xor_self).trans UInt64.zero_xor))
      ((UInt64.xor_assoc _ _ _).symm.trans ((congrArg (· ^^^ a.w2) UInt64.xor_self).trans UInt64.zero_xor))
      ((UInt64.xor_assoc _ _ _).symm.trans ((congrArg (· ^^^ a.w3) UInt64.xor_self).trans UInt64.zero_xor))

@[inline]
def Word256.one : Word256 := ⟨1, 0, 0, 0⟩

set_option maxHeartbeats 200000 in
  theorem addWithCarry_zero_both :
      Word256.addWithCarry Word256.zero Word256.zero = (Word256.zero, false) :=
    rfl

set_option maxHeartbeats 200000 in
  theorem subWithBorrow_zero_both :
      Word256.subWithBorrow Word256.zero Word256.zero = (Word256.zero, false) :=
    rfl

set_option maxHeartbeats 200000 in
  theorem addWithCarry_max_one_overflow :
      Word256.addWithCarry Word256.max Word256.one = (Word256.zero, true) :=
    rfl

set_option maxHeartbeats 200000 in
  theorem subWithBorrow_zero_one_underflow :
      Word256.subWithBorrow Word256.zero Word256.one = (Word256.max, true) :=
    rfl

set_option maxHeartbeats 200000 in
  theorem bitNot_bitNot (a : Word256) :
      Word256.bitNot (Word256.bitNot a) = a :=
    Word256.ext UInt64.not_not UInt64.not_not UInt64.not_not UInt64.not_not

set_option maxHeartbeats 200000 in
  theorem bitNot_bitAnd (a b : Word256) :
      Word256.bitNot (Word256.bitAnd a b) = Word256.bitOr (Word256.bitNot a) (Word256.bitNot b) :=
    Word256.ext
      (congrArg UInt64.ofBitVec BitVec.not_and)
      (congrArg UInt64.ofBitVec BitVec.not_and)
      (congrArg UInt64.ofBitVec BitVec.not_and)
      (congrArg UInt64.ofBitVec BitVec.not_and)

set_option maxHeartbeats 200000 in
  theorem bitNot_bitOr (a b : Word256) :
      Word256.bitNot (Word256.bitOr a b) = Word256.bitAnd (Word256.bitNot a) (Word256.bitNot b) :=
    Word256.ext
      (congrArg UInt64.ofBitVec BitVec.not_or)
      (congrArg UInt64.ofBitVec BitVec.not_or)
      (congrArg UInt64.ofBitVec BitVec.not_or)
      (congrArg UInt64.ofBitVec BitVec.not_or)

set_option maxHeartbeats 200000 in
  theorem bitAnd_bitOr_distrib_left (a b c : Word256) :
      Word256.bitAnd a (Word256.bitOr b c) = Word256.bitOr (Word256.bitAnd a b) (Word256.bitAnd a c) :=
    Word256.ext
      (congrArg UInt64.ofBitVec BitVec.and_or_distrib_left)
      (congrArg UInt64.ofBitVec BitVec.and_or_distrib_left)
      (congrArg UInt64.ofBitVec BitVec.and_or_distrib_left)
      (congrArg UInt64.ofBitVec BitVec.and_or_distrib_left)

set_option maxHeartbeats 200000 in
  theorem bitAnd_bitOr_distrib_right (a b c : Word256) :
      Word256.bitAnd (Word256.bitOr a b) c = Word256.bitOr (Word256.bitAnd a c) (Word256.bitAnd b c) :=
    Word256.ext
      (congrArg UInt64.ofBitVec BitVec.and_or_distrib_right)
      (congrArg UInt64.ofBitVec BitVec.and_or_distrib_right)
      (congrArg UInt64.ofBitVec BitVec.and_or_distrib_right)
      (congrArg UInt64.ofBitVec BitVec.and_or_distrib_right)

set_option maxHeartbeats 200000 in
  theorem bitOr_bitAnd_distrib_left (a b c : Word256) :
      Word256.bitOr a (Word256.bitAnd b c) = Word256.bitAnd (Word256.bitOr a b) (Word256.bitOr a c) :=
    (bitNot_bitNot _).symm.trans <|
      (congrArg Word256.bitNot (bitNot_bitOr a (Word256.bitAnd b c))).trans <|
      (congrArg (fun x => Word256.bitNot (Word256.bitAnd (Word256.bitNot a) x)) (bitNot_bitAnd b c)).trans <|
      (congrArg Word256.bitNot (bitAnd_bitOr_distrib_left (Word256.bitNot a) (Word256.bitNot b) (Word256.bitNot c))).trans <|
      (bitNot_bitOr _ _).trans <|
      (congrArg (Word256.bitAnd · (Word256.bitNot (Word256.bitAnd (Word256.bitNot a) (Word256.bitNot c))))
        ((congrArg Word256.bitNot (bitNot_bitOr a b).symm).trans (bitNot_bitNot _))).trans <|
      congrArg (Word256.bitAnd (Word256.bitOr a b) ·)
        ((congrArg Word256.bitNot (bitNot_bitOr a c).symm).trans (bitNot_bitNot _))

set_option maxHeartbeats 200000 in
  theorem bitAnd_bitNot_self (a : Word256) :
      Word256.bitAnd a (Word256.bitNot a) = Word256.zero :=
    Word256.ext
      (congrArg UInt64.ofBitVec (BitVec.and_not_self a.w0.toBitVec))
      (congrArg UInt64.ofBitVec (BitVec.and_not_self a.w1.toBitVec))
      (congrArg UInt64.ofBitVec (BitVec.and_not_self a.w2.toBitVec))
      (congrArg UInt64.ofBitVec (BitVec.and_not_self a.w3.toBitVec))

set_option maxHeartbeats 200000 in
  theorem bitOr_bitNot_self (a : Word256) :
      Word256.bitOr a (Word256.bitNot a) = Word256.max :=
    Word256.ext
      (congrArg UInt64.ofBitVec (BitVec.or_not_self a.w0.toBitVec))
      (congrArg UInt64.ofBitVec (BitVec.or_not_self a.w1.toBitVec))
      (congrArg UInt64.ofBitVec (BitVec.or_not_self a.w2.toBitVec))
      (congrArg UInt64.ofBitVec (BitVec.or_not_self a.w3.toBitVec))

set_option maxHeartbeats 200000 in
  theorem bitXor_bitNot_self (a : Word256) :
      Word256.bitXor a (Word256.bitNot a) = Word256.max :=
    (congrArg (Word256.bitXor a)
      (Word256.ext
        (congrArg UInt64.ofBitVec BitVec.xor_allOnes.symm)
        (congrArg UInt64.ofBitVec BitVec.xor_allOnes.symm)
        (congrArg UInt64.ofBitVec BitVec.xor_allOnes.symm)
        (congrArg UInt64.ofBitVec BitVec.xor_allOnes.symm))).trans
      (bitXor_cancel_left Word256.max a)

set_option maxHeartbeats 200000 in
  theorem bitXor_max_right (a : Word256) :
      Word256.bitXor a Word256.max = Word256.bitNot a :=
    Word256.ext
      (congrArg UInt64.ofBitVec BitVec.xor_allOnes)
      (congrArg UInt64.ofBitVec BitVec.xor_allOnes)
      (congrArg UInt64.ofBitVec BitVec.xor_allOnes)
      (congrArg UInt64.ofBitVec BitVec.xor_allOnes)

set_option maxHeartbeats 200000 in
  theorem bitXor_max_left (a : Word256) :
      Word256.bitXor Word256.max a = Word256.bitNot a :=
    Word256.ext
      (congrArg UInt64.ofBitVec BitVec.allOnes_xor)
      (congrArg UInt64.ofBitVec BitVec.allOnes_xor)
      (congrArg UInt64.ofBitVec BitVec.allOnes_xor)
      (congrArg UInt64.ofBitVec BitVec.allOnes_xor)

set_option maxHeartbeats 200000 in
  theorem bitAnd_bitOr_absorb (a b : Word256) :
      Word256.bitAnd a (Word256.bitOr a b) = a :=
    (congrArg (Word256.bitAnd · (Word256.bitOr a b)) (bitOr_zero_right a).symm).trans <|
      (bitOr_bitAnd_distrib_left a Word256.zero b).symm.trans <|
      (congrArg (Word256.bitOr a) (bitAnd_zero_left b)).trans
        (bitOr_zero_right a)

set_option maxHeartbeats 200000 in
  theorem bitOr_bitAnd_absorb (a b : Word256) :
      Word256.bitOr a (Word256.bitAnd a b) = a :=
    (bitNot_bitNot _).symm.trans <|
      (congrArg Word256.bitNot (bitNot_bitOr a (Word256.bitAnd a b))).trans <|
      (congrArg (fun x => Word256.bitNot (Word256.bitAnd (Word256.bitNot a) x)) (bitNot_bitAnd a b)).trans <|
      (congrArg Word256.bitNot (bitAnd_bitOr_absorb (Word256.bitNot a) (Word256.bitNot b))).trans
        (bitNot_bitNot a)

set_option maxHeartbeats 200000 in
  theorem bitAnd_max_right (a : Word256) :
      Word256.bitAnd a Word256.max = a :=
    Word256.ext
      (congrArg UInt64.ofBitVec BitVec.and_allOnes)
      (congrArg UInt64.ofBitVec BitVec.and_allOnes)
      (congrArg UInt64.ofBitVec BitVec.and_allOnes)
      (congrArg UInt64.ofBitVec BitVec.and_allOnes)

set_option maxHeartbeats 200000 in
  theorem bitAnd_max_left (a : Word256) :
      Word256.bitAnd Word256.max a = a :=
    Word256.ext
      (congrArg UInt64.ofBitVec BitVec.allOnes_and)
      (congrArg UInt64.ofBitVec BitVec.allOnes_and)
      (congrArg UInt64.ofBitVec BitVec.allOnes_and)
      (congrArg UInt64.ofBitVec BitVec.allOnes_and)

set_option maxHeartbeats 200000 in
  theorem bitOr_max_right (a : Word256) :
      Word256.bitOr a Word256.max = Word256.max :=
    Word256.ext
      (congrArg UInt64.ofBitVec BitVec.or_allOnes)
      (congrArg UInt64.ofBitVec BitVec.or_allOnes)
      (congrArg UInt64.ofBitVec BitVec.or_allOnes)
      (congrArg UInt64.ofBitVec BitVec.or_allOnes)

set_option maxHeartbeats 200000 in
  theorem bitOr_max_left (a : Word256) :
      Word256.bitOr Word256.max a = Word256.max :=
    Word256.ext
      (congrArg UInt64.ofBitVec BitVec.allOnes_or)
      (congrArg UInt64.ofBitVec BitVec.allOnes_or)
      (congrArg UInt64.ofBitVec BitVec.allOnes_or)
      (congrArg UInt64.ofBitVec BitVec.allOnes_or)

@[inline]
def Word256.bitMux (mask a b : Word256) : Word256 :=
  Word256.bitOr (Word256.bitAnd a mask) (Word256.bitAnd b (Word256.bitNot mask))

set_option maxHeartbeats 200000 in
  theorem bitMux_zero_mask (a b : Word256) :
      Word256.bitMux Word256.zero a b = b :=
    (congrArg (Word256.bitOr · (Word256.bitAnd b (Word256.bitNot Word256.zero))) (bitAnd_zero_right a)).trans <|
      (bitOr_zero_left _).trans
        (bitAnd_max_right b)

set_option maxHeartbeats 200000 in
  theorem bitMux_max_mask (a b : Word256) :
      Word256.bitMux Word256.max a b = a :=
    (congrArg (Word256.bitOr (Word256.bitAnd a Word256.max) ·) (bitAnd_zero_right b)).trans <|
      (bitOr_zero_right _).trans
        (bitAnd_max_right a)

set_option maxHeartbeats 200000 in
  theorem bitMux_self (mask a : Word256) :
      Word256.bitMux mask a a = a :=
    (bitAnd_bitOr_distrib_left a mask (Word256.bitNot mask)).symm.trans <|
      (congrArg (Word256.bitAnd a) (bitOr_bitNot_self mask)).trans
        (bitAnd_max_right a)

set_option maxHeartbeats 200000 in
  theorem bitMux_bitNot_mask (mask a b : Word256) :
      Word256.bitMux (Word256.bitNot mask) a b = Word256.bitMux mask b a :=
    (congrArg (fun x => Word256.bitOr (Word256.bitAnd a (Word256.bitNot mask)) (Word256.bitAnd b x))
      (bitNot_bitNot mask)).trans
      (bitOr_comm _ _)

set_option maxHeartbeats 200000 in
  theorem bitMux_max_zero (mask : Word256) :
      Word256.bitMux mask Word256.max Word256.zero = mask :=
    (congrArg (Word256.bitOr (Word256.bitAnd Word256.max mask) ·) (bitAnd_zero_left (Word256.bitNot mask))).trans <|
      (bitOr_zero_right _).trans
        (bitAnd_max_left mask)

set_option maxHeartbeats 200000 in
  theorem bitMux_zero_max (mask : Word256) :
      Word256.bitMux mask Word256.zero Word256.max = Word256.bitNot mask :=
    (congrArg (Word256.bitOr · (Word256.bitAnd Word256.max (Word256.bitNot mask))) (bitAnd_zero_left mask)).trans <|
      (bitOr_zero_left _).trans
        (bitAnd_max_left (Word256.bitNot mask))

set_option maxHeartbeats 200000 in
  theorem bitMux_nested_left (mask a b c : Word256) :
      Word256.bitMux mask (Word256.bitMux mask a b) c = Word256.bitMux mask a c :=
    let hLeft : Word256.bitAnd (Word256.bitMux mask a b) mask = Word256.bitAnd a mask :=
      (bitAnd_bitOr_distrib_right (Word256.bitAnd a mask) (Word256.bitAnd b (Word256.bitNot mask)) mask).trans <|
        (congrArg (Word256.bitOr · (Word256.bitAnd (Word256.bitAnd b (Word256.bitNot mask)) mask))
          ((bitAnd_assoc a mask mask).trans (congrArg (Word256.bitAnd a) (bitAnd_self mask)))).trans <|
        (congrArg (Word256.bitOr (Word256.bitAnd a mask) ·)
          ((bitAnd_assoc b (Word256.bitNot mask) mask).trans
            ((congrArg (Word256.bitAnd b) ((bitAnd_comm (Word256.bitNot mask) mask).trans (bitAnd_bitNot_self mask))).trans
              (bitAnd_zero_right b)))).trans
          (bitOr_zero_right _)
    congrArg (Word256.bitOr · (Word256.bitAnd c (Word256.bitNot mask))) hLeft

set_option maxHeartbeats 200000 in
  theorem bitMux_nested_right (mask a b c : Word256) :
      Word256.bitMux mask a (Word256.bitMux mask b c) = Word256.bitMux mask a c :=
    (bitMux_bitNot_mask mask (Word256.bitMux mask b c) a).symm.trans <|
      (congrArg (fun x => Word256.bitMux (Word256.bitNot mask) x a) (bitMux_bitNot_mask mask c b).symm).trans <|
      (bitMux_nested_left (Word256.bitNot mask) c b a).trans
        (bitMux_bitNot_mask mask c a)

set_option maxHeartbeats 200000 in
  theorem bitMux_and_mask_left (mask a b : Word256) :
      Word256.bitMux mask (Word256.bitAnd a mask) b = Word256.bitMux mask a b :=
    congrArg (Word256.bitOr · (Word256.bitAnd b (Word256.bitNot mask)))
      ((bitAnd_assoc a mask mask).trans (congrArg (Word256.bitAnd a) (bitAnd_self mask)))

set_option maxHeartbeats 200000 in
  theorem bitMux_and_not_mask_right (mask a b : Word256) :
      Word256.bitMux mask a (Word256.bitAnd b (Word256.bitNot mask)) = Word256.bitMux mask a b :=
    congrArg (Word256.bitOr (Word256.bitAnd a mask) ·)
      ((bitAnd_assoc b (Word256.bitNot mask) (Word256.bitNot mask)).trans
        (congrArg (Word256.bitAnd b) (bitAnd_self (Word256.bitNot mask))))

set_option maxHeartbeats 200000 in
  theorem bitAnd_bitMux_distrib_left (mask a b c : Word256) :
      Word256.bitAnd c (Word256.bitMux mask a b) =
        Word256.bitMux mask (Word256.bitAnd c a) (Word256.bitAnd c b) :=
    (bitAnd_bitOr_distrib_left c (Word256.bitAnd a mask) (Word256.bitAnd b (Word256.bitNot mask))).trans <|
      (congrArg (Word256.bitOr · (Word256.bitAnd c (Word256.bitAnd b (Word256.bitNot mask))))
        (bitAnd_assoc c a mask).symm).trans
        (congrArg (Word256.bitOr (Word256.bitAnd (Word256.bitAnd c a) mask) ·)
          (bitAnd_assoc c b (Word256.bitNot mask)).symm)

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux (mask a b : Word256) :
      Word256.bitNot (Word256.bitMux mask a b) =
        Word256.bitMux mask (Word256.bitNot a) (Word256.bitNot b) :=
    let hBranch (m x y : Word256) :
        Word256.bitAnd (Word256.bitNot (Word256.bitMux m x y)) m = Word256.bitAnd (Word256.bitNot x) m :=
      (congrArg (Word256.bitAnd · m) (bitNot_bitOr (Word256.bitAnd x m) (Word256.bitAnd y (Word256.bitNot m)))).trans <|
        (bitAnd_assoc (Word256.bitNot (Word256.bitAnd x m)) (Word256.bitNot (Word256.bitAnd y (Word256.bitNot m))) m).trans <|
        (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd x m)) ·)
          ((congrArg (Word256.bitAnd · m)
            ((bitNot_bitAnd y (Word256.bitNot m)).trans
              (congrArg (Word256.bitOr (Word256.bitNot y)) (bitNot_bitNot m)))).trans
            ((bitAnd_comm (Word256.bitOr (Word256.bitNot y) m) m).trans
              ((congrArg (Word256.bitAnd m) (bitOr_comm (Word256.bitNot y) m)).trans
                (bitAnd_bitOr_absorb m (Word256.bitNot y)))))).trans <|
        (congrArg (Word256.bitAnd · m) (bitNot_bitAnd x m)).trans <|
        (bitAnd_bitOr_distrib_right (Word256.bitNot x) (Word256.bitNot m) m).trans <|
        (congrArg (Word256.bitOr (Word256.bitAnd (Word256.bitNot x) m))
          ((bitAnd_comm (Word256.bitNot m) m).trans (bitAnd_bitNot_self m))).trans
          (bitOr_zero_right _)
    (bitMux_self mask (Word256.bitNot (Word256.bitMux mask a b))).symm.trans <|
      (congrArg (Word256.bitOr · (Word256.bitAnd (Word256.bitNot (Word256.bitMux mask a b)) (Word256.bitNot mask)))
        (hBranch mask a b)).trans
        (congrArg (Word256.bitOr (Word256.bitAnd (Word256.bitNot a) mask) ·)
          ((congrArg (fun z => Word256.bitAnd (Word256.bitNot z) (Word256.bitNot mask))
            (bitMux_bitNot_mask mask b a).symm).trans
            (hBranch (Word256.bitNot mask) b a)))

set_option maxHeartbeats 200000 in
  theorem bitOr_bitMux_distrib_left (mask a b c : Word256) :
      Word256.bitOr c (Word256.bitMux mask a b) =
        Word256.bitMux mask (Word256.bitOr c a) (Word256.bitOr c b) :=
    let hDeMorganOr (x y : Word256) :
        Word256.bitNot (Word256.bitAnd (Word256.bitNot x) (Word256.bitNot y)) = Word256.bitOr x y :=
      (congrArg Word256.bitNot (bitNot_bitOr x y).symm).trans (bitNot_bitNot (Word256.bitOr x y))
    (bitNot_bitNot (Word256.bitOr c (Word256.bitMux mask a b))).symm.trans <|
      (congrArg Word256.bitNot (bitNot_bitOr c (Word256.bitMux mask a b))).trans <|
      (congrArg (fun z => Word256.bitNot (Word256.bitAnd (Word256.bitNot c) z)) (bitNot_bitMux mask a b)).trans <|
      (congrArg Word256.bitNot (bitAnd_bitMux_distrib_left mask (Word256.bitNot a) (Word256.bitNot b) (Word256.bitNot c))).trans <|
      (bitNot_bitMux mask (Word256.bitAnd (Word256.bitNot c) (Word256.bitNot a)) (Word256.bitAnd (Word256.bitNot c) (Word256.bitNot b))).trans <|
      (congrArg (fun z => Word256.bitMux mask z (Word256.bitNot (Word256.bitAnd (Word256.bitNot c) (Word256.bitNot b))))
        (hDeMorganOr c a)).trans
        (congrArg (Word256.bitMux mask (Word256.bitOr c a)) (hDeMorganOr c b))

set_option maxHeartbeats 200000 in
  theorem bitAnd_bitMux_distrib_right (mask a b c : Word256) :
      Word256.bitAnd (Word256.bitMux mask a b) c =
        Word256.bitMux mask (Word256.bitAnd a c) (Word256.bitAnd b c) :=
    (bitAnd_comm (Word256.bitMux mask a b) c).trans <|
      (bitAnd_bitMux_distrib_left mask a b c).trans <|
      (congrArg (fun x => Word256.bitMux mask x (Word256.bitAnd c b)) (bitAnd_comm c a)).trans
        (congrArg (Word256.bitMux mask (Word256.bitAnd a c)) (bitAnd_comm c b))

set_option maxHeartbeats 200000 in
  theorem bitOr_bitMux_distrib_right (mask a b c : Word256) :
      Word256.bitOr (Word256.bitMux mask a b) c =
        Word256.bitMux mask (Word256.bitOr a c) (Word256.bitOr b c) :=
    (bitOr_comm (Word256.bitMux mask a b) c).trans <|
      (bitOr_bitMux_distrib_left mask a b c).trans <|
      (congrArg (fun x => Word256.bitMux mask x (Word256.bitOr c b)) (bitOr_comm c a)).trans
        (congrArg (Word256.bitMux mask (Word256.bitOr a c)) (bitOr_comm c b))

set_option maxHeartbeats 200000 in
  theorem bitMux_true_left (mask b : Word256) :
      Word256.bitMux mask Word256.max b = Word256.bitOr mask b :=
    (congrArg (fun x => Word256.bitMux mask x b) (bitOr_max_left b).symm).trans <|
      (congrArg (Word256.bitMux mask (Word256.bitOr Word256.max b)) (bitOr_zero_left b).symm).trans <|
      (bitOr_bitMux_distrib_right mask Word256.max Word256.zero b).symm.trans
        (congrArg (Word256.bitOr · b) (bitMux_max_zero mask))

set_option maxHeartbeats 200000 in
  theorem bitMux_zero_left (mask b : Word256) :
      Word256.bitMux mask Word256.zero b = Word256.bitAnd b (Word256.bitNot mask) :=
    (congrArg (Word256.bitOr · (Word256.bitAnd b (Word256.bitNot mask))) (bitAnd_zero_left mask)).trans
      (bitOr_zero_left _)

set_option maxHeartbeats 200000 in
  theorem bitMux_zero_right (mask a : Word256) :
      Word256.bitMux mask a Word256.zero = Word256.bitAnd a mask :=
    (congrArg (Word256.bitOr (Word256.bitAnd a mask) ·) (bitAnd_zero_left (Word256.bitNot mask))).trans
      (bitOr_zero_right _)

set_option maxHeartbeats 200000 in
  theorem bitMux_max_right (mask a : Word256) :
      Word256.bitMux mask a Word256.max = Word256.bitOr a (Word256.bitNot mask) :=
    (bitMux_bitNot_mask mask Word256.max a).symm.trans <|
      (bitMux_true_left (Word256.bitNot mask) a).trans
        (bitOr_comm (Word256.bitNot mask) a)

set_option maxHeartbeats 200000 in
  theorem bitMux_mask_left (mask b : Word256) :
      Word256.bitMux mask mask b = Word256.bitOr mask b :=
    (congrArg (fun x => Word256.bitMux mask x b) (bitAnd_max_left mask).symm).trans <|
      (bitMux_and_mask_left mask Word256.max b).trans
        (bitMux_true_left mask b)

set_option maxHeartbeats 200000 in
  theorem bitMux_mask_right (mask a : Word256) :
      Word256.bitMux mask a mask = Word256.bitAnd a mask :=
    (congrArg (Word256.bitOr (Word256.bitAnd a mask) ·) (bitAnd_bitNot_self mask)).trans
      (bitOr_zero_right _)

set_option maxHeartbeats 200000 in
  theorem bitMux_bitNot_mask_left (mask b : Word256) :
      Word256.bitMux mask (Word256.bitNot mask) b = Word256.bitAnd b (Word256.bitNot mask) :=
    (congrArg (Word256.bitOr · (Word256.bitAnd b (Word256.bitNot mask)))
      ((bitAnd_comm (Word256.bitNot mask) mask).trans (bitAnd_bitNot_self mask))).trans
      (bitOr_zero_left _)

set_option maxHeartbeats 200000 in
  theorem bitMux_bitNot_mask_right (mask a : Word256) :
      Word256.bitMux mask a (Word256.bitNot mask) = Word256.bitOr a (Word256.bitNot mask) :=
    (bitMux_bitNot_mask mask (Word256.bitNot mask) a).symm.trans <|
      (bitMux_mask_left (Word256.bitNot mask) a).trans
        (bitOr_comm (Word256.bitNot mask) a)

set_option maxHeartbeats 200000 in
  theorem bitMux_mask_bitNot_mask (mask : Word256) :
      Word256.bitMux mask mask (Word256.bitNot mask) = Word256.max :=
    (bitMux_mask_left mask (Word256.bitNot mask)).trans (bitOr_bitNot_self mask)

  @[inline]
  def Word256.bitClearMask (x mask : Word256) : Word256 :=
    Word256.bitAnd x (Word256.bitNot mask)

  @[inline]
  def Word256.bitSetMask (x mask : Word256) : Word256 :=
    Word256.bitOr x mask

set_option maxHeartbeats 200000 in
  theorem bitClearMask_zero (x : Word256) :
      Word256.bitClearMask x Word256.zero = x :=
    bitAnd_max_right x

set_option maxHeartbeats 200000 in
  theorem bitClearMask_max (x : Word256) :
      Word256.bitClearMask x Word256.max = Word256.zero :=
    bitAnd_zero_right x

set_option maxHeartbeats 200000 in
  theorem bitClearMask_self (x : Word256) :
      Word256.bitClearMask x x = Word256.zero :=
    bitAnd_bitNot_self x

set_option maxHeartbeats 200000 in
  theorem bitClearMask_idempotent (x mask : Word256) :
      Word256.bitClearMask (Word256.bitClearMask x mask) mask = Word256.bitClearMask x mask :=
    (bitAnd_assoc x (Word256.bitNot mask) (Word256.bitNot mask)).trans
      (congrArg (Word256.bitAnd x) (bitAnd_self (Word256.bitNot mask)))

set_option maxHeartbeats 200000 in
  theorem bitSetMask_then_clearMask (x mask : Word256) :
      Word256.bitClearMask (Word256.bitSetMask x mask) mask = Word256.bitClearMask x mask :=
    (bitAnd_bitOr_distrib_right x mask (Word256.bitNot mask)).trans <|
      (congrArg (Word256.bitOr (Word256.bitClearMask x mask)) (bitAnd_bitNot_self mask)).trans
        (bitOr_zero_right (Word256.bitClearMask x mask))

set_option maxHeartbeats 200000 in
  theorem bitSetMask_zero (x : Word256) :
      Word256.bitSetMask x Word256.zero = x :=
    bitOr_zero_right x

set_option maxHeartbeats 200000 in
  theorem bitSetMask_max (x : Word256) :
      Word256.bitSetMask x Word256.max = Word256.max :=
    bitOr_max_right x

set_option maxHeartbeats 200000 in
  theorem bitSetMask_self (x : Word256) :
      Word256.bitSetMask x x = x :=
    bitOr_self x

set_option maxHeartbeats 200000 in
  theorem bitSetMask_idempotent (x mask : Word256) :
      Word256.bitSetMask (Word256.bitSetMask x mask) mask = Word256.bitSetMask x mask :=
    (bitOr_assoc x mask mask).trans
      (congrArg (Word256.bitOr x) (bitOr_self mask))

set_option maxHeartbeats 200000 in
  theorem bitClearMask_then_setMask (x mask : Word256) :
      Word256.bitSetMask (Word256.bitClearMask x mask) mask = Word256.bitSetMask x mask :=
    (congrArg (Word256.bitOr (Word256.bitClearMask x mask))
      ((bitAnd_max_left (Word256.bitNot (Word256.bitNot mask))).trans (bitNot_bitNot mask)).symm).trans <|
      (bitMux_max_right (Word256.bitNot mask) x).trans
        (congrArg (Word256.bitOr x) (bitNot_bitNot mask))

  @[inline]
  def Word256.bitFlipMask (x mask : Word256) : Word256 :=
    Word256.bitXor x mask

set_option maxHeartbeats 200000 in
  theorem bitFlipMask_zero (x : Word256) :
      Word256.bitFlipMask x Word256.zero = x :=
    bitXor_zero_right x

set_option maxHeartbeats 200000 in
  theorem bitFlipMask_max (x : Word256) :
      Word256.bitFlipMask x Word256.max = Word256.bitNot x :=
    bitXor_max_right x

set_option maxHeartbeats 200000 in
  theorem bitFlipMask_self (x : Word256) :
      Word256.bitFlipMask x x = Word256.zero :=
    bitXor_self_zero x

set_option maxHeartbeats 200000 in
  theorem bitFlipMask_involutive (x mask : Word256) :
      Word256.bitFlipMask (Word256.bitFlipMask x mask) mask = x :=
    bitXor_cancel_right x mask

set_option maxHeartbeats 200000 in
  theorem bitFlipMask_comm_masks (x m1 m2 : Word256) :
      Word256.bitFlipMask (Word256.bitFlipMask x m1) m2 =
        Word256.bitFlipMask (Word256.bitFlipMask x m2) m1 :=
    (bitXor_assoc x m1 m2).trans <|
      (congrArg (Word256.bitXor x) (bitXor_comm m1 m2)).trans
        (bitXor_assoc x m2 m1).symm

set_option maxHeartbeats 200000 in
  theorem bitSetMask_comm_masks (x m1 m2 : Word256) :
      Word256.bitSetMask (Word256.bitSetMask x m1) m2 =
        Word256.bitSetMask (Word256.bitSetMask x m2) m1 :=
    (bitOr_assoc x m1 m2).trans <|
      (congrArg (Word256.bitOr x) (bitOr_comm m1 m2)).trans
        (bitOr_assoc x m2 m1).symm

set_option maxHeartbeats 200000 in
  theorem bitClearMask_comm_masks (x m1 m2 : Word256) :
      Word256.bitClearMask (Word256.bitClearMask x m1) m2 =
        Word256.bitClearMask (Word256.bitClearMask x m2) m1 :=
    (bitAnd_assoc x (Word256.bitNot m1) (Word256.bitNot m2)).trans <|
      (congrArg (Word256.bitAnd x) (bitAnd_comm (Word256.bitNot m1) (Word256.bitNot m2))).trans
        (bitAnd_assoc x (Word256.bitNot m2) (Word256.bitNot m1)).symm

set_option maxHeartbeats 200000 in
  theorem bitMux_eq_setMask_of_max_left (mask x : Word256) :
      Word256.bitMux mask Word256.max x = Word256.bitSetMask x mask :=
    (bitMux_true_left mask x).trans (bitOr_comm mask x)

set_option maxHeartbeats 200000 in
  theorem bitMux_eq_clearMask_of_zero_left (mask x : Word256) :
      Word256.bitMux mask Word256.zero x = Word256.bitClearMask x mask :=
    bitMux_zero_left mask x

set_option maxHeartbeats 200000 in
  theorem bitFlipMask_bitNot_self (x : Word256) :
      Word256.bitFlipMask x (Word256.bitNot x) = Word256.max :=
    bitXor_bitNot_self x

set_option maxHeartbeats 200000 in
  theorem bitSetMask_absorb_clearMask (a mask : Word256) :
      Word256.bitSetMask (Word256.bitClearMask a mask) mask = Word256.bitSetMask a mask :=
    bitClearMask_then_setMask a mask

set_option maxHeartbeats 200000 in
  theorem bitClearMask_absorb_setMask (a mask : Word256) :
      Word256.bitClearMask (Word256.bitSetMask a mask) mask = Word256.bitClearMask a mask :=
    bitSetMask_then_clearMask a mask

set_option maxHeartbeats 200000 in
  theorem bitFlipMask_setMask_eq_clearMask (a mask : Word256) :
      Word256.bitFlipMask (Word256.bitSetMask a mask) mask = Word256.bitClearMask a mask :=
    let hLimb (x m : BitVec 64) : (x ||| m) ^^^ m = x &&& ~~~m :=
      BitVec.eq_of_getElem_eq fun i hi =>
        (BitVec.getElem_xor (x := x ||| m) (y := m) hi).trans <|
          (congrArg (· ^^ m[i]) (BitVec.getElem_or (x := x) (y := m) hi)).trans <|
          (show ((x[i] || m[i]) ^^ m[i]) = (x[i] && !m[i]) from
            match x[i], m[i] with | false, false | false, true | true, false | true, true => rfl).trans <|
          (congrArg (x[i] && ·) (BitVec.getElem_not (x := m) hi).symm).trans
            (BitVec.getElem_and (x := x) (y := ~~~m) hi).symm
    Word256.ext
      (congrArg UInt64.ofBitVec (hLimb a.w0.toBitVec mask.w0.toBitVec))
      (congrArg UInt64.ofBitVec (hLimb a.w1.toBitVec mask.w1.toBitVec))
      (congrArg UInt64.ofBitVec (hLimb a.w2.toBitVec mask.w2.toBitVec))
      (congrArg UInt64.ofBitVec (hLimb a.w3.toBitVec mask.w3.toBitVec))

set_option maxHeartbeats 200000 in
  theorem bitFlipMask_clearMask_eq_setMask (a mask : Word256) :
      Word256.bitFlipMask (Word256.bitClearMask a mask) mask = Word256.bitSetMask a mask :=
    (congrArg (Word256.bitFlipMask · mask) (bitFlipMask_setMask_eq_clearMask a mask).symm).trans
      (bitFlipMask_involutive (Word256.bitSetMask a mask) mask)

set_option maxHeartbeats 200000 in
  theorem bitMux_bitFlipMask_self (a mask : Word256) :
      Word256.bitMux a (Word256.bitFlipMask a mask) a = Word256.bitClearMask a mask :=
    let hLimb (x m : BitVec 64) : (x ^^^ m) &&& x = x &&& ~~~m :=
      BitVec.eq_of_getElem_eq fun i hi =>
        (BitVec.getElem_and (x := x ^^^ m) (y := x) hi).trans <|
          (congrArg (· && x[i]) (BitVec.getElem_xor (x := x) (y := m) hi)).trans <|
          (show ((x[i] ^^ m[i]) && x[i]) = (x[i] && !m[i]) from
            match x[i], m[i] with | false, false | false, true | true, false | true, true => rfl).trans <|
          (congrArg (x[i] && ·) (BitVec.getElem_not (x := m) hi).symm).trans
            (BitVec.getElem_and (x := x) (y := ~~~m) hi).symm
    (bitMux_mask_right a (Word256.bitFlipMask a mask)).trans <|
      Word256.ext
        (congrArg UInt64.ofBitVec (hLimb a.w0.toBitVec mask.w0.toBitVec))
        (congrArg UInt64.ofBitVec (hLimb a.w1.toBitVec mask.w1.toBitVec))
        (congrArg UInt64.ofBitVec (hLimb a.w2.toBitVec mask.w2.toBitVec))
        (congrArg UInt64.ofBitVec (hLimb a.w3.toBitVec mask.w3.toBitVec))

set_option maxHeartbeats 200000 in
  theorem bitMux_bitSetMask_left (mask a b : Word256) :
      Word256.bitMux mask (Word256.bitSetMask a mask) b = Word256.bitSetMask b mask :=
    let hLeft : Word256.bitAnd (Word256.bitSetMask a mask) mask = mask :=
      (bitAnd_comm (Word256.bitOr a mask) mask).trans <|
        (congrArg (Word256.bitAnd mask) (bitOr_comm a mask)).trans
          (bitAnd_bitOr_absorb mask a)
    (congrArg (Word256.bitOr · (Word256.bitAnd b (Word256.bitNot mask))) hLeft).trans <|
      (congrArg (Word256.bitOr · (Word256.bitAnd b (Word256.bitNot mask))) (bitAnd_self mask).symm).trans <|
      (bitMux_mask_left mask b).trans
        (bitOr_comm mask b)

set_option maxHeartbeats 200000 in
  theorem bitMux_bitClearMask_right (mask a b : Word256) :
      Word256.bitMux (Word256.bitNot mask) a (Word256.bitClearMask b mask) = Word256.bitClearMask a mask :=
    let hRight : Word256.bitAnd (Word256.bitClearMask b mask) (Word256.bitNot (Word256.bitNot mask)) = Word256.zero :=
      (congrArg (Word256.bitAnd (Word256.bitClearMask b mask)) (bitNot_bitNot mask)).trans <|
        (bitAnd_assoc b (Word256.bitNot mask) mask).trans <|
        (congrArg (Word256.bitAnd b) ((bitAnd_comm (Word256.bitNot mask) mask).trans (bitAnd_bitNot_self mask))).trans
          (bitAnd_zero_right b)
    (congrArg (Word256.bitOr (Word256.bitAnd a (Word256.bitNot mask)) ·) hRight).trans
      (bitOr_zero_right (Word256.bitClearMask a mask))

set_option maxHeartbeats 200000 in
  theorem bitSetMask_bitFlipMask_eq_setMask (a mask : Word256) :
      Word256.bitSetMask (Word256.bitFlipMask a mask) mask = Word256.bitSetMask a mask :=
    let hLimb (x m : BitVec 64) : (x ^^^ m) ||| m = x ||| m :=
      BitVec.eq_of_getElem_eq fun i hi =>
        (BitVec.getElem_or (x := x ^^^ m) (y := m) hi).trans <|
          (congrArg (· || m[i]) (BitVec.getElem_xor (x := x) (y := m) hi)).trans <|
          (show ((x[i] ^^ m[i]) || m[i]) = (x[i] || m[i]) from
            match x[i], m[i] with | false, false | false, true | true, false | true, true => rfl).trans
            (BitVec.getElem_or (x := x) (y := m) hi).symm
    Word256.ext
      (congrArg UInt64.ofBitVec (hLimb a.w0.toBitVec mask.w0.toBitVec))
      (congrArg UInt64.ofBitVec (hLimb a.w1.toBitVec mask.w1.toBitVec))
      (congrArg UInt64.ofBitVec (hLimb a.w2.toBitVec mask.w2.toBitVec))
      (congrArg UInt64.ofBitVec (hLimb a.w3.toBitVec mask.w3.toBitVec))

set_option maxHeartbeats 200000 in
  theorem bitClearMask_bitFlipMask_eq_clearMask (a mask : Word256) :
      Word256.bitClearMask (Word256.bitFlipMask a mask) mask = Word256.bitClearMask a mask :=
    (bitSetMask_then_clearMask (Word256.bitFlipMask a mask) mask).symm.trans <|
      (congrArg (Word256.bitClearMask · mask) (bitSetMask_bitFlipMask_eq_setMask a mask)).trans
        (bitSetMask_then_clearMask a mask)

set_option maxHeartbeats 200000 in
  theorem bitFlipMask_merge_masks (a m1 m2 : Word256) :
      Word256.bitFlipMask (Word256.bitFlipMask a m1) m2 =
        Word256.bitFlipMask a (Word256.bitXor m1 m2) :=
    bitXor_assoc a m1 m2

set_option maxHeartbeats 200000 in
  theorem bitSetMask_merge_masks (a m1 m2 : Word256) :
      Word256.bitSetMask (Word256.bitSetMask a m1) m2 =
        Word256.bitSetMask a (Word256.bitOr m1 m2) :=
    bitOr_assoc a m1 m2

set_option maxHeartbeats 200000 in
  theorem bitClearMask_merge_masks (a m1 m2 : Word256) :
      Word256.bitClearMask (Word256.bitClearMask a m1) m2 =
        Word256.bitClearMask a (Word256.bitOr m1 m2) :=
    (bitAnd_assoc a (Word256.bitNot m1) (Word256.bitNot m2)).trans
      (congrArg (Word256.bitAnd a) (bitNot_bitOr m1 m2).symm)

set_option maxHeartbeats 200000 in
  theorem bitMux_bitFlipMask_right (a mask : Word256) :
      Word256.bitMux a a (Word256.bitFlipMask a mask) = Word256.bitSetMask a mask :=
    let hLimb (x m : BitVec 64) : (x &&& x) ||| ((x ^^^ m) &&& ~~~x) = x ||| m :=
      BitVec.eq_of_getElem_eq fun i hi =>
        (BitVec.getElem_or (x := x &&& x) (y := (x ^^^ m) &&& ~~~x) hi).trans <|
          (congrArg (· || ((x ^^^ m) &&& ~~~x)[i]) (BitVec.getElem_and (x := x) (y := x) hi)).trans <|
          (congrArg ((x[i] && x[i]) || ·)
            ((BitVec.getElem_and (x := x ^^^ m) (y := ~~~x) hi).trans
              ((congrArg (· && (~~~x)[i]) (BitVec.getElem_xor (x := x) (y := m) hi)).trans
                (congrArg ((x[i] ^^ m[i]) && ·) (BitVec.getElem_not (x := x) hi))))).trans <|
          (show ((x[i] && x[i]) || ((x[i] ^^ m[i]) && !x[i])) = (x[i] || m[i]) from
            match x[i], m[i] with | false, false | false, true | true, false | true, true => rfl).trans
            (BitVec.getElem_or (x := x) (y := m) hi).symm
    Word256.ext
      (congrArg UInt64.ofBitVec (hLimb a.w0.toBitVec mask.w0.toBitVec))
      (congrArg UInt64.ofBitVec (hLimb a.w1.toBitVec mask.w1.toBitVec))
      (congrArg UInt64.ofBitVec (hLimb a.w2.toBitVec mask.w2.toBitVec))
      (congrArg UInt64.ofBitVec (hLimb a.w3.toBitVec mask.w3.toBitVec))

set_option maxHeartbeats 200000 in
  theorem bitMux_bitFlipMask_left (mask a : Word256) :
      Word256.bitMux mask (Word256.bitFlipMask a mask) a = Word256.bitFlipMask a mask :=
    let hLimb (x m : BitVec 64) : ((x ^^^ m) &&& m) ||| (x &&& ~~~m) = x ^^^ m :=
      BitVec.eq_of_getElem_eq fun i hi =>
        (BitVec.getElem_or (x := (x ^^^ m) &&& m) (y := x &&& ~~~m) hi).trans <|
          (congrArg (· || (x &&& ~~~m)[i])
            ((BitVec.getElem_and (x := x ^^^ m) (y := m) hi).trans
              (congrArg (· && m[i]) (BitVec.getElem_xor (x := x) (y := m) hi)))).trans <|
          (congrArg (((x[i] ^^ m[i]) && m[i]) || ·)
            ((BitVec.getElem_and (x := x) (y := ~~~m) hi).trans
              (congrArg (x[i] && ·) (BitVec.getElem_not (x := m) hi)))).trans <|
          (show (((x[i] ^^ m[i]) && m[i]) || (x[i] && !m[i])) = (x[i] ^^ m[i]) from
            match x[i], m[i] with | false, false | false, true | true, false | true, true => rfl).trans
            (BitVec.getElem_xor (x := x) (y := m) hi).symm
    Word256.ext
      (congrArg UInt64.ofBitVec (hLimb a.w0.toBitVec mask.w0.toBitVec))
      (congrArg UInt64.ofBitVec (hLimb a.w1.toBitVec mask.w1.toBitVec))
      (congrArg UInt64.ofBitVec (hLimb a.w2.toBitVec mask.w2.toBitVec))
      (congrArg UInt64.ofBitVec (hLimb a.w3.toBitVec mask.w3.toBitVec))

set_option maxHeartbeats 200000 in
  theorem bitSetMask_bitClearMask_same_mask (a m : Word256) :
      Word256.bitSetMask (Word256.bitClearMask a m) (Word256.bitAnd a m) = a :=
    (bitOr_comm (Word256.bitClearMask a m) (Word256.bitAnd a m)).trans
      (bitMux_self m a)

set_option maxHeartbeats 200000 in
  theorem bitSetMask_bitClearMask_disjoint_comm (a m1 m2 : Word256) :
      Word256.bitSetMask (Word256.bitClearMask a m1) (Word256.bitClearMask m2 m1) =
        Word256.bitClearMask (Word256.bitSetMask a (Word256.bitClearMask m2 m1)) m1 :=
    (congrArg (Word256.bitSetMask (Word256.bitClearMask a m1)) (bitClearMask_idempotent m2 m1).symm).trans
      (bitAnd_bitOr_distrib_right a (Word256.bitClearMask m2 m1) (Word256.bitNot m1)).symm

set_option maxHeartbeats 200000 in
  theorem bitMux_bitSetMask_right (mask a b : Word256) :
      Word256.bitMux mask a (Word256.bitSetMask b mask) = Word256.bitMux mask a b :=
    congrArg (Word256.bitOr (Word256.bitAnd a mask)) (bitSetMask_then_clearMask b mask)

set_option maxHeartbeats 200000 in
  theorem bitMux_bitClearMask_left (mask a b : Word256) :
      Word256.bitMux (Word256.bitNot mask) (Word256.bitClearMask a mask) b =
        Word256.bitMux (Word256.bitNot mask) a b :=
    (bitMux_bitNot_mask mask (Word256.bitClearMask a mask) b).trans <|
      (bitMux_and_not_mask_right mask b a).trans
        (bitMux_bitNot_mask mask a b).symm

set_option maxHeartbeats 200000 in
  theorem bitXor_bitSetMask_bitClearMask (a mask : Word256) :
      Word256.bitXor (Word256.bitSetMask a mask) (Word256.bitClearMask a mask) = mask :=
    (congrArg (Word256.bitXor (Word256.bitSetMask a mask)) (bitFlipMask_setMask_eq_clearMask a mask).symm).trans
      (bitXor_cancel_left mask (Word256.bitSetMask a mask))

set_option maxHeartbeats 200000 in
  theorem bitXor_bitClearMask_bitSetMask (a mask : Word256) :
      Word256.bitXor (Word256.bitClearMask a mask) (Word256.bitSetMask a mask) = mask :=
    (bitXor_comm (Word256.bitClearMask a mask) (Word256.bitSetMask a mask)).trans
      (bitXor_bitSetMask_bitClearMask a mask)

set_option maxHeartbeats 200000 in
  theorem bitAnd_bitSetMask_self (a mask : Word256) :
      Word256.bitAnd (Word256.bitSetMask a mask) mask = mask :=
    (bitAnd_comm (Word256.bitOr a mask) mask).trans <|
      (congrArg (Word256.bitAnd mask) (bitOr_comm a mask)).trans
        (bitAnd_bitOr_absorb mask a)

set_option maxHeartbeats 200000 in
  theorem bitAnd_bitClearMask_self (a mask : Word256) :
      Word256.bitAnd (Word256.bitClearMask a mask) mask = Word256.zero :=
    (bitAnd_assoc a (Word256.bitNot mask) mask).trans <|
      (congrArg (Word256.bitAnd a) ((bitAnd_comm (Word256.bitNot mask) mask).trans (bitAnd_bitNot_self mask))).trans
        (bitAnd_zero_right a)

set_option maxHeartbeats 200000 in
  theorem bitOr_bitSetMask_self (a mask : Word256) :
      Word256.bitOr (Word256.bitSetMask a mask) a = Word256.bitSetMask a mask :=
    (bitOr_comm (Word256.bitOr a mask) a).trans <|
      (bitOr_assoc a a mask).symm.trans
        (congrArg (Word256.bitOr · mask) (bitOr_self a))

set_option maxHeartbeats 200000 in
  theorem bitAnd_bitClearMask_orig (a mask : Word256) :
      Word256.bitAnd (Word256.bitClearMask a mask) a = Word256.bitClearMask a mask :=
    (bitAnd_comm (Word256.bitAnd a (Word256.bitNot mask)) a).trans <|
      (bitAnd_assoc a a (Word256.bitNot mask)).symm.trans
        (congrArg (Word256.bitAnd · (Word256.bitNot mask)) (bitAnd_self a))

set_option maxHeartbeats 200000 in
  theorem bitOr_bitClearMask_bitAnd_self (a mask : Word256) :
      Word256.bitOr (Word256.bitClearMask a mask) (Word256.bitAnd a mask) = a :=
    bitSetMask_bitClearMask_same_mask a mask

set_option maxHeartbeats 200000 in
  theorem bitAnd_bitSetMask_bitClearMask (a mask : Word256) :
      Word256.bitAnd (Word256.bitSetMask a mask) (Word256.bitClearMask a mask) =
        Word256.bitClearMask a mask :=
    (congrArg (Word256.bitAnd · (Word256.bitClearMask a mask)) (bitClearMask_then_setMask a mask).symm).trans <|
      (bitAnd_comm (Word256.bitOr (Word256.bitClearMask a mask) mask) (Word256.bitClearMask a mask)).trans
        (bitAnd_bitOr_absorb (Word256.bitClearMask a mask) mask)

set_option maxHeartbeats 200000 in
  theorem bitOr_bitSetMask_bitClearMask (a mask : Word256) :
      Word256.bitOr (Word256.bitSetMask a mask) (Word256.bitClearMask a mask) =
        Word256.bitSetMask a mask :=
    (congrArg (Word256.bitOr (Word256.bitSetMask a mask)) (bitSetMask_then_clearMask a mask).symm).trans
      (bitOr_bitAnd_absorb (Word256.bitSetMask a mask) (Word256.bitNot mask))

set_option maxHeartbeats 200000 in
  theorem bitSetMask_bitNot_mask_self (a : Word256) :
      Word256.bitSetMask a (Word256.bitNot a) = Word256.max :=
    bitOr_bitNot_self a

set_option maxHeartbeats 200000 in
  theorem bitClearMask_self_eq_zero (a : Word256) :
      Word256.bitClearMask a a = Word256.zero :=
    bitClearMask_self a

set_option maxHeartbeats 200000 in
  theorem bitSetMask_self_eq_self (a : Word256) :
      Word256.bitSetMask a a = a :=
    bitSetMask_self a

set_option maxHeartbeats 200000 in
  theorem bitFlipMask_self_eq_zero (a : Word256) :
      Word256.bitFlipMask a a = Word256.zero :=
    bitFlipMask_self a

set_option maxHeartbeats 200000 in
  theorem bitFlipMask_bitNot_mask_self (a : Word256) :
      Word256.bitFlipMask a (Word256.bitNot a) = Word256.max :=
    bitFlipMask_bitNot_self a

set_option maxHeartbeats 200000 in
  theorem bitSetMask_bitNot_self (a : Word256) :
      Word256.bitSetMask (Word256.bitNot a) a = Word256.max :=
    (bitOr_comm (Word256.bitNot a) a).trans (bitOr_bitNot_self a)

set_option maxHeartbeats 200000 in
  theorem bitClearMask_bitNot_self (a : Word256) :
      Word256.bitClearMask (Word256.bitNot a) a = Word256.bitNot a :=
    bitAnd_self (Word256.bitNot a)

set_option maxHeartbeats 200000 in
  theorem bitAnd_bitFlipMask_self (a mask : Word256) :
      Word256.bitAnd (Word256.bitFlipMask a mask) mask = Word256.bitClearMask mask a :=
    (bitMux_mask_right mask (Word256.bitFlipMask a mask)).symm.trans <|
      (congrArg (fun z => Word256.bitMux mask z mask) (bitXor_comm a mask)).trans
        (bitMux_bitFlipMask_self mask a)

set_option maxHeartbeats 200000 in
  theorem bitAnd_bitFlipMask_distrib (a m b : Word256) :
      Word256.bitAnd (Word256.bitFlipMask a m) b =
        Word256.bitXor (Word256.bitAnd a b) (Word256.bitAnd m b) :=
    let hLimb (x y z : BitVec 64) : (x ^^^ y) &&& z = (x &&& z) ^^^ (y &&& z) :=
      BitVec.eq_of_getElem_eq fun i hi =>
        (BitVec.getElem_and (x := x ^^^ y) (y := z) hi).trans <|
          (congrArg (· && z[i]) (BitVec.getElem_xor (x := x) (y := y) hi)).trans <|
          (show ((x[i] ^^ y[i]) && z[i]) = ((x[i] && z[i]) ^^ (y[i] && z[i])) from
            match x[i], y[i], z[i] with
            | false, false, false | false, false, true | false, true, false | false, true, true
            | true, false, false | true, false, true | true, true, false | true, true, true => rfl).trans <|
          (congrArg (· ^^ (y[i] && z[i])) (BitVec.getElem_and (x := x) (y := z) hi).symm).trans <|
          (congrArg ((x &&& z)[i] ^^ ·) (BitVec.getElem_and (x := y) (y := z) hi).symm).trans
            (BitVec.getElem_xor (x := x &&& z) (y := y &&& z) hi).symm
    Word256.ext
      (congrArg UInt64.ofBitVec (hLimb a.w0.toBitVec m.w0.toBitVec b.w0.toBitVec))
      (congrArg UInt64.ofBitVec (hLimb a.w1.toBitVec m.w1.toBitVec b.w1.toBitVec))
      (congrArg UInt64.ofBitVec (hLimb a.w2.toBitVec m.w2.toBitVec b.w2.toBitVec))
      (congrArg UInt64.ofBitVec (hLimb a.w3.toBitVec m.w3.toBitVec b.w3.toBitVec))

set_option maxHeartbeats 200000 in
  theorem bitFlipMask_bitAnd_self (a m : Word256) :
      Word256.bitFlipMask a (Word256.bitAnd a m) = Word256.bitClearMask a m :=
    (congrArg (Word256.bitXor a) (bitAnd_comm a m)).trans <|
      (congrArg (Word256.bitXor · (Word256.bitAnd m a)) (bitAnd_max_left a).symm).trans <|
      (bitAnd_bitFlipMask_distrib Word256.max m a).symm.trans <|
      (congrArg (Word256.bitAnd · a) (bitXor_max_left m)).trans
        (bitAnd_comm (Word256.bitNot m) a)

set_option maxHeartbeats 200000 in
  theorem bitFlipMask_bitClearMask_not (a m : Word256) :
      Word256.bitFlipMask a (Word256.bitClearMask m a) = Word256.bitSetMask a m :=
    (bitXor_comm a (Word256.bitClearMask m a)).trans <|
      (bitFlipMask_clearMask_eq_setMask m a).trans
        (bitOr_comm m a)

set_option maxHeartbeats 200000 in
  theorem bitOr_bitFlipMask_self (a m : Word256) :
      Word256.bitOr (Word256.bitFlipMask a m) m = Word256.bitSetMask a m :=
    bitSetMask_bitFlipMask_eq_setMask a m

set_option maxHeartbeats 200000 in
  theorem bitClearMask_bitFlipMask_self (a m : Word256) :
      Word256.bitClearMask (Word256.bitFlipMask a m) a = Word256.bitClearMask m a :=
    (congrArg (Word256.bitClearMask · a) (bitXor_comm a m)).trans
      (bitClearMask_bitFlipMask_eq_clearMask m a)

set_option maxHeartbeats 200000 in
  theorem bitMux_bitOr_mask (m1 m2 a b : Word256) :
      Word256.bitMux (Word256.bitOr m1 m2) a b =
        Word256.bitMux m2 a (Word256.bitMux m1 a b) :=
    let hA : Word256.bitOr (Word256.bitAnd a m2) (Word256.bitAnd (Word256.bitAnd a m1) (Word256.bitNot m2)) =
        Word256.bitAnd a (Word256.bitOr m1 m2) :=
      (congrArg (Word256.bitOr (Word256.bitAnd a m2)) (bitAnd_assoc a m1 (Word256.bitNot m2))).trans <|
        (bitAnd_bitOr_distrib_left a m2 (Word256.bitClearMask m1 m2)).symm.trans <|
        congrArg (Word256.bitAnd a)
          ((bitOr_comm m2 (Word256.bitClearMask m1 m2)).trans (bitClearMask_then_setMask m1 m2))
    let hB : Word256.bitAnd (Word256.bitAnd b (Word256.bitNot m1)) (Word256.bitNot m2) =
        Word256.bitAnd b (Word256.bitNot (Word256.bitOr m1 m2)) :=
      bitClearMask_merge_masks b m1 m2
    ((congrArg (Word256.bitOr (Word256.bitAnd a m2))
      (bitAnd_bitOr_distrib_right (Word256.bitAnd a m1) (Word256.bitAnd b (Word256.bitNot m1)) (Word256.bitNot m2))).trans <|
      (bitOr_assoc (Word256.bitAnd a m2) (Word256.bitAnd (Word256.bitAnd a m1) (Word256.bitNot m2))
        (Word256.bitAnd (Word256.bitAnd b (Word256.bitNot m1)) (Word256.bitNot m2))).symm.trans <|
      (congrArg (Word256.bitOr · (Word256.bitAnd (Word256.bitAnd b (Word256.bitNot m1)) (Word256.bitNot m2))) hA).trans
        (congrArg (Word256.bitOr (Word256.bitAnd a (Word256.bitOr m1 m2))) hB)).symm

set_option maxHeartbeats 200000 in
  theorem bitMux_bitAnd_mask (m1 m2 a b : Word256) :
      Word256.bitMux (Word256.bitAnd m1 m2) a b =
        Word256.bitMux m2 (Word256.bitMux m1 a b) b :=
    (bitMux_bitNot_mask (Word256.bitAnd m1 m2) b a).symm.trans <|
      (congrArg (fun m => Word256.bitMux m b a) (bitNot_bitAnd m1 m2)).trans <|
      (bitMux_bitOr_mask (Word256.bitNot m1) (Word256.bitNot m2) b a).trans <|
      (congrArg (Word256.bitMux (Word256.bitNot m2) b) (bitMux_bitNot_mask m1 b a)).trans
        (bitMux_bitNot_mask m2 b (Word256.bitMux m1 a b))

set_option maxHeartbeats 200000 in
  theorem bitSetMask_bitClearMask_absorb_same (a m : Word256) :
      Word256.bitSetMask (Word256.bitClearMask a m) (Word256.bitAnd a m) = a :=
    bitSetMask_bitClearMask_same_mask a m

set_option maxHeartbeats 200000 in
  theorem bitClearMask_bitSetMask_absorb_not (a m : Word256) :
      Word256.bitClearMask (Word256.bitSetMask a m) (Word256.bitClearMask m a) = a :=
    let hSet : Word256.bitSetMask a m = Word256.bitSetMask a (Word256.bitClearMask m a) :=
      (bitOr_comm a m).trans <|
        (bitClearMask_then_setMask m a).symm.trans
          (bitOr_comm (Word256.bitClearMask m a) a)
    (congrArg (Word256.bitClearMask · (Word256.bitClearMask m a)) hSet).trans <|
      (bitSetMask_then_clearMask a (Word256.bitClearMask m a)).trans <|
      (congrArg (Word256.bitAnd a)
        ((bitNot_bitAnd m (Word256.bitNot a)).trans
          ((congrArg (Word256.bitOr (Word256.bitNot m)) (bitNot_bitNot a)).trans
            (bitOr_comm (Word256.bitNot m) a)))).trans
        (bitAnd_bitOr_absorb a (Word256.bitNot m))

set_option maxHeartbeats 200000 in
  theorem bitFlipMask_bitFlipMask_merge (a m1 m2 : Word256) :
      Word256.bitFlipMask (Word256.bitFlipMask a m1) (Word256.bitXor m1 m2) =
        Word256.bitFlipMask a m2 :=
    (bitFlipMask_merge_masks a m1 (Word256.bitXor m1 m2)).trans
      (congrArg (Word256.bitFlipMask a) (bitXor_cancel_left m2 m1))

set_option maxHeartbeats 200000 in
  theorem bitMux_bitXor_mask_self (a b : Word256) :
      Word256.bitMux a b (Word256.bitXor a b) = b :=
    (congrArg (Word256.bitOr (Word256.bitAnd b a)) (bitClearMask_bitFlipMask_self a b)).trans
      (bitMux_self a b)

set_option maxHeartbeats 200000 in
  theorem bitMux_bitXor_mask_swap (a b : Word256) :
      Word256.bitMux b a (Word256.bitXor a b) = a :=
    (congrArg (Word256.bitMux b a) (bitXor_comm a b)).trans
      (bitMux_bitXor_mask_self b a)

set_option maxHeartbeats 200000 in
  theorem bitSetMask_bitOr_mask (a b c : Word256) :
      Word256.bitSetMask a (Word256.bitOr b c) =
        Word256.bitSetMask (Word256.bitSetMask a b) c :=
    (bitSetMask_merge_masks a b c).symm

set_option maxHeartbeats 200000 in
  theorem bitClearMask_bitOr_mask (a b c : Word256) :
      Word256.bitClearMask a (Word256.bitOr b c) =
        Word256.bitClearMask (Word256.bitClearMask a b) c :=
    (bitClearMask_merge_masks a b c).symm

set_option maxHeartbeats 200000 in
  theorem bitClearMask_bitAnd_mask_self (a b : Word256) :
      Word256.bitClearMask a (Word256.bitAnd a b) = Word256.bitClearMask a b :=
    (congrArg (Word256.bitAnd a) (bitNot_bitAnd a b)).trans <|
      (bitAnd_bitOr_distrib_left a (Word256.bitNot a) (Word256.bitNot b)).trans <|
      (congrArg (Word256.bitOr · (Word256.bitClearMask a b)) (bitAnd_bitNot_self a)).trans
        (bitOr_zero_left (Word256.bitClearMask a b))

  @[inline]
  def Word256.bitMaj (a b c : Word256) : Word256 :=
    Word256.bitOr (Word256.bitAnd a b) (Word256.bitOr (Word256.bitAnd b c) (Word256.bitAnd a c))

set_option maxHeartbeats 200000 in
  theorem bitMaj_idemp (a b : Word256) :
      Word256.bitMaj a a b = a :=
    (congrArg (Word256.bitOr · (Word256.bitOr (Word256.bitAnd a b) (Word256.bitAnd a b))) (bitAnd_self a)).trans <|
      (congrArg (Word256.bitOr a) (bitOr_self (Word256.bitAnd a b))).trans
        (bitOr_bitAnd_absorb a b)

set_option maxHeartbeats 200000 in
  theorem bitMaj_comm_left (a b c : Word256) :
      Word256.bitMaj a b c = Word256.bitMaj b a c :=
    (congrArg (Word256.bitOr · (Word256.bitOr (Word256.bitAnd b c) (Word256.bitAnd a c))) (bitAnd_comm a b)).trans
      (congrArg (Word256.bitOr (Word256.bitAnd b a)) (bitOr_comm (Word256.bitAnd b c) (Word256.bitAnd a c)))

set_option maxHeartbeats 200000 in
  theorem bitMaj_zero (a b : Word256) :
      Word256.bitMaj a b Word256.zero = Word256.bitAnd a b :=
    (congrArg (Word256.bitOr (Word256.bitAnd a b))
      ((congrArg (Word256.bitOr · (Word256.bitAnd a Word256.zero)) (bitAnd_zero_right b)).trans
        ((bitOr_zero_left (Word256.bitAnd a Word256.zero)).trans (bitAnd_zero_right a)))).trans
      (bitOr_zero_right (Word256.bitAnd a b))

set_option maxHeartbeats 200000 in
  theorem bitMaj_max (a b : Word256) :
      Word256.bitMaj a b Word256.max = Word256.bitOr a b :=
    let hRight : Word256.bitOr (Word256.bitAnd b Word256.max) (Word256.bitAnd a Word256.max) = Word256.bitOr b a :=
      (congrArg (Word256.bitOr · (Word256.bitAnd a Word256.max)) (bitAnd_max_right b)).trans
        (congrArg (Word256.bitOr b) (bitAnd_max_right a))
    let hAbsorb : Word256.bitOr (Word256.bitAnd a b) b = b :=
      (bitOr_comm (Word256.bitAnd a b) b).trans
        ((congrArg (Word256.bitOr b) (bitAnd_comm a b)).trans (bitOr_bitAnd_absorb b a))
    (congrArg (Word256.bitOr (Word256.bitAnd a b)) hRight).trans <|
      (bitOr_assoc (Word256.bitAnd a b) b a).symm.trans <|
      (congrArg (Word256.bitOr · a) hAbsorb).trans
        (bitOr_comm b a)

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitNot_right (a c : Word256) :
      Word256.bitMaj a (Word256.bitNot a) c = c :=
    (congrArg (Word256.bitOr · (Word256.bitOr (Word256.bitAnd (Word256.bitNot a) c) (Word256.bitAnd a c)))
      (bitAnd_bitNot_self a)).trans <|
      (bitOr_zero_left (Word256.bitOr (Word256.bitAnd (Word256.bitNot a) c) (Word256.bitAnd a c))).trans <|
      (bitAnd_bitOr_distrib_right (Word256.bitNot a) a c).symm.trans <|
      (congrArg (Word256.bitAnd · c) (bitSetMask_bitNot_self a)).trans
        (bitAnd_max_left c)

set_option maxHeartbeats 200000 in
  theorem bitMaj_idemp_right (a b : Word256) :
      Word256.bitMaj a b b = b :=
    let hAbsorb : Word256.bitOr b (Word256.bitAnd a b) = b :=
      (congrArg (Word256.bitOr b) (bitAnd_comm a b)).trans (bitOr_bitAnd_absorb b a)
    (congrArg (Word256.bitOr (Word256.bitAnd a b))
      ((congrArg (Word256.bitOr · (Word256.bitAnd a b)) (bitAnd_self b)).trans hAbsorb)).trans <|
      (bitOr_comm (Word256.bitAnd a b) b).trans hAbsorb

set_option maxHeartbeats 200000 in
  theorem bitMaj_idemp_outer (a b : Word256) :
      Word256.bitMaj a b a = a :=
    (bitMaj_comm_left a b a).trans (bitMaj_idemp_right b a)

set_option maxHeartbeats 200000 in
  theorem bitMaj_zero_left (b c : Word256) :
      Word256.bitMaj Word256.zero b c = Word256.bitAnd b c :=
    (congrArg (Word256.bitOr · (Word256.bitOr (Word256.bitAnd b c) (Word256.bitAnd Word256.zero c)))
      (bitAnd_zero_left b)).trans <|
      (bitOr_zero_left (Word256.bitOr (Word256.bitAnd b c) (Word256.bitAnd Word256.zero c))).trans <|
      (congrArg (Word256.bitOr (Word256.bitAnd b c)) (bitAnd_zero_left c)).trans
        (bitOr_zero_right (Word256.bitAnd b c))

set_option maxHeartbeats 200000 in
  theorem bitMaj_max_left (b c : Word256) :
      Word256.bitMaj Word256.max b c = Word256.bitOr b c :=
    (congrArg (Word256.bitOr · (Word256.bitOr (Word256.bitAnd b c) (Word256.bitAnd Word256.max c)))
      (bitAnd_max_left b)).trans <|
      (congrArg (Word256.bitOr b)
        (congrArg (Word256.bitOr (Word256.bitAnd b c)) (bitAnd_max_left c))).trans <|
      (bitOr_assoc b (Word256.bitAnd b c) c).symm.trans
        (congrArg (Word256.bitOr · c) (bitOr_bitAnd_absorb b c))

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitNot_mid (a c : Word256) :
      Word256.bitMaj a (Word256.bitNot a) c = c :=
    bitMaj_bitNot_right a c

set_option maxHeartbeats 200000 in
  theorem bitMaj_zero_mid (a c : Word256) :
      Word256.bitMaj a Word256.zero c = Word256.bitAnd a c :=
    (bitMaj_comm_left a Word256.zero c).trans (bitMaj_zero_left a c)

set_option maxHeartbeats 200000 in
  theorem bitMaj_max_mid (a c : Word256) :
      Word256.bitMaj a Word256.max c = Word256.bitOr a c :=
    (bitMaj_comm_left a Word256.max c).trans (bitMaj_max_left a c)

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitNot_left (a c : Word256) :
      Word256.bitMaj (Word256.bitNot a) a c = c :=
    (bitMaj_comm_left (Word256.bitNot a) a c).trans (bitMaj_bitNot_right a c)

set_option maxHeartbeats 200000 in
  theorem bitMaj_all_same (a : Word256) :
      Word256.bitMaj a a a = a :=
    bitMaj_idemp a a

set_option maxHeartbeats 200000 in
  theorem bitAnd_bitMaj_self (a b c : Word256) :
      Word256.bitAnd a (Word256.bitMaj a b c) = Word256.bitAnd a (Word256.bitOr b c) :=
    let X := Word256.bitAnd a b
    let Y := Word256.bitAnd b c
    let Z := Word256.bitAnd a c
    let hX : Word256.bitAnd a X = X :=
      (bitAnd_assoc a a b).symm.trans (congrArg (Word256.bitAnd · b) (bitAnd_self a))
    let hY : Word256.bitAnd a Y = Word256.bitAnd X c :=
      (bitAnd_assoc a b c).symm
    let hZ : Word256.bitAnd a Z = Z :=
      (bitAnd_assoc a a c).symm.trans (congrArg (Word256.bitAnd · c) (bitAnd_self a))
    let hYZ : Word256.bitAnd a (Word256.bitOr Y Z) = Word256.bitOr (Word256.bitAnd X c) Z :=
      (bitAnd_bitOr_distrib_left a Y Z).trans
        ((congrArg (Word256.bitOr · (Word256.bitAnd a Z)) hY).trans
          (congrArg (Word256.bitOr (Word256.bitAnd X c)) hZ))
    (bitAnd_bitOr_distrib_left a X (Word256.bitOr Y Z)).trans <|
      (congrArg (Word256.bitOr · (Word256.bitAnd a (Word256.bitOr Y Z))) hX).trans <|
      (congrArg (Word256.bitOr X) hYZ).trans <|
      (bitOr_assoc X (Word256.bitAnd X c) Z).symm.trans <|
      (congrArg (Word256.bitOr · Z) (bitOr_bitAnd_absorb X c)).trans
        (bitAnd_bitOr_distrib_left a b c).symm

set_option maxHeartbeats 200000 in
  theorem bitOr_bitMaj_self (a b c : Word256) :
      Word256.bitOr a (Word256.bitMaj a b c) = Word256.bitOr a (Word256.bitAnd b c) :=
    let X := Word256.bitAnd a b
    let Y := Word256.bitAnd b c
    let Z := Word256.bitAnd a c
    (bitOr_assoc a X (Word256.bitOr Y Z)).symm.trans <|
      (congrArg (Word256.bitOr · (Word256.bitOr Y Z)) (bitOr_bitAnd_absorb a b)).trans <|
      (congrArg (Word256.bitOr a) (bitOr_comm Y Z)).trans <|
      (bitOr_assoc a Z Y).symm.trans
        (congrArg (Word256.bitOr · Y) (bitOr_bitAnd_absorb a c))

set_option maxHeartbeats 200000 in
  theorem bitAnd_bitMaj_mid (a b c : Word256) :
      Word256.bitAnd b (Word256.bitMaj a b c) = Word256.bitAnd b (Word256.bitOr a c) :=
    (congrArg (Word256.bitAnd b) (bitMaj_comm_left a b c)).trans (bitAnd_bitMaj_self b a c)

set_option maxHeartbeats 200000 in
  theorem bitOr_bitMaj_mid (a b c : Word256) :
      Word256.bitOr b (Word256.bitMaj a b c) = Word256.bitOr b (Word256.bitAnd a c) :=
    (congrArg (Word256.bitOr b) (bitMaj_comm_left a b c)).trans (bitOr_bitMaj_self b a c)

set_option maxHeartbeats 200000 in
  theorem bitAnd_bitMaj_right (a b c : Word256) :
      Word256.bitAnd c (Word256.bitMaj a b c) = Word256.bitAnd c (Word256.bitOr a b) :=
    let X := Word256.bitAnd a b
    let Y := Word256.bitAnd b c
    let Z := Word256.bitAnd a c
    let hSwap : Word256.bitMaj a b c = Word256.bitMaj a c b :=
      (bitOr_comm X (Word256.bitOr Y Z)).trans <|
        (congrArg (Word256.bitOr · X) (bitOr_comm Y Z)).trans <|
        (bitOr_assoc Z Y X).trans
          (congrArg (Word256.bitOr Z) (congrArg (Word256.bitOr · X) (bitAnd_comm b c)))
    (congrArg (Word256.bitAnd c) hSwap).trans (bitAnd_bitMaj_mid a c b)

set_option maxHeartbeats 200000 in
  theorem bitOr_bitMaj_right (a b c : Word256) :
      Word256.bitOr c (Word256.bitMaj a b c) = Word256.bitOr c (Word256.bitAnd a b) :=
    let X := Word256.bitAnd a b
    let Y := Word256.bitAnd b c
    let Z := Word256.bitAnd a c
    let hSwap : Word256.bitMaj a b c = Word256.bitMaj a c b :=
      (bitOr_comm X (Word256.bitOr Y Z)).trans <|
        (congrArg (Word256.bitOr · X) (bitOr_comm Y Z)).trans <|
        (bitOr_assoc Z Y X).trans
          (congrArg (Word256.bitOr Z) (congrArg (Word256.bitOr · X) (bitAnd_comm b c)))
    (congrArg (Word256.bitOr c) hSwap).trans (bitOr_bitMaj_mid a c b)

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitAnd_absorb_left (a b c : Word256) :
      Word256.bitMaj a (Word256.bitAnd a b) c = Word256.bitAnd a (Word256.bitOr b c) :=
    let X := Word256.bitAnd a b
    let hX : Word256.bitAnd a X = X :=
      (bitAnd_assoc a a b).symm.trans (congrArg (Word256.bitAnd · b) (bitAnd_self a))
    (congrArg (Word256.bitOr · (Word256.bitOr (Word256.bitAnd X c) (Word256.bitAnd a c))) hX).trans <|
      (bitOr_assoc X (Word256.bitAnd X c) (Word256.bitAnd a c)).symm.trans <|
      (congrArg (Word256.bitOr · (Word256.bitAnd a c)) (bitOr_bitAnd_absorb X c)).trans
        (bitAnd_bitOr_distrib_left a b c).symm

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitOr_absorb_left (a b c : Word256) :
      Word256.bitMaj a (Word256.bitOr a b) c = Word256.bitOr a (Word256.bitAnd b c) :=
    let U := Word256.bitOr a b
    let Y := Word256.bitAnd b c
    let Z := Word256.bitAnd a c
    let hRight : Word256.bitOr (Word256.bitAnd U c) Z = Word256.bitOr Z Y :=
      (congrArg (Word256.bitOr · Z) (bitAnd_bitOr_distrib_right a b c)).trans <|
        (bitOr_comm (Word256.bitOr Z Y) Z).trans <|
        (bitOr_assoc Z Z Y).symm.trans
          (congrArg (Word256.bitOr · Y) (bitOr_self Z))
    (congrArg (Word256.bitOr · (Word256.bitOr (Word256.bitAnd U c) Z)) (bitAnd_bitOr_absorb a b)).trans <|
      (congrArg (Word256.bitOr a) hRight).trans <|
      (bitOr_assoc a Z Y).symm.trans
        (congrArg (Word256.bitOr · Y) (bitOr_bitAnd_absorb a c))

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitSetMask_left (a m b : Word256) :
      Word256.bitMaj (Word256.bitSetMask a m) m b = Word256.bitOr m (Word256.bitAnd a b) :=
    (bitMaj_comm_left (Word256.bitSetMask a m) m b).trans <|
      (congrArg (fun x => Word256.bitMaj m x b) (bitOr_comm a m)).trans
        (bitMaj_bitOr_absorb_left m a b)

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitClearMask_left (a m b : Word256) :
      Word256.bitMaj (Word256.bitClearMask a m) Word256.zero b = Word256.bitAnd (Word256.bitClearMask a m) b :=
    bitMaj_zero_mid (Word256.bitClearMask a m) b

set_option maxHeartbeats 200000 in
  theorem bitSetMask_bitMaj_self (a b c : Word256) :
      Word256.bitSetMask (Word256.bitMaj a b c) a = Word256.bitOr a (Word256.bitAnd b c) :=
    (bitOr_comm (Word256.bitMaj a b c) a).trans (bitOr_bitMaj_self a b c)

set_option maxHeartbeats 200000 in
  theorem bitClearMask_bitMaj_self (a b c : Word256) :
      Word256.bitClearMask (Word256.bitMaj a b c) a = Word256.bitClearMask (Word256.bitAnd b c) a :=
    let X := Word256.bitAnd a b
    let Y := Word256.bitAnd b c
    let Z := Word256.bitAnd a c
    let na := Word256.bitNot a
    let hX : Word256.bitAnd X na = Word256.zero :=
      (congrArg (Word256.bitAnd · na) (bitAnd_comm a b)).trans <|
        (bitAnd_assoc b a na).trans <|
        (congrArg (Word256.bitAnd b) (bitAnd_bitNot_self a)).trans
          (bitAnd_zero_right b)
    let hZ : Word256.bitAnd Z na = Word256.zero :=
      (congrArg (Word256.bitAnd · na) (bitAnd_comm a c)).trans <|
        (bitAnd_assoc c a na).trans <|
        (congrArg (Word256.bitAnd c) (bitAnd_bitNot_self a)).trans
          (bitAnd_zero_right c)
    (bitAnd_bitOr_distrib_right X (Word256.bitOr Y Z) na).trans <|
      (congrArg (Word256.bitOr · (Word256.bitAnd (Word256.bitOr Y Z) na)) hX).trans <|
      (bitOr_zero_left (Word256.bitAnd (Word256.bitOr Y Z) na)).trans <|
      (bitAnd_bitOr_distrib_right Y Z na).trans <|
      (congrArg (Word256.bitOr (Word256.bitAnd Y na)) hZ).trans
        (bitOr_zero_right (Word256.bitAnd Y na))

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitClearMask_right (a b m : Word256) :
      Word256.bitMaj a Word256.zero (Word256.bitClearMask b m) = Word256.bitAnd a (Word256.bitClearMask b m) :=
    bitMaj_zero_mid a (Word256.bitClearMask b m)

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitSetMask_right (a b m : Word256) :
      Word256.bitMaj a Word256.max (Word256.bitSetMask b m) = Word256.bitOr a (Word256.bitSetMask b m) :=
    bitMaj_max_mid a (Word256.bitSetMask b m)

set_option maxHeartbeats 200000 in
  theorem bitSetMask_bitMaj_mid (a b c : Word256) :
      Word256.bitSetMask (Word256.bitMaj a b c) b = Word256.bitOr b (Word256.bitAnd a c) :=
    (bitOr_comm (Word256.bitMaj a b c) b).trans (bitOr_bitMaj_mid a b c)

set_option maxHeartbeats 200000 in
  theorem bitSetMask_bitMaj_right (a b c : Word256) :
      Word256.bitSetMask (Word256.bitMaj a b c) c = Word256.bitOr c (Word256.bitAnd a b) :=
    (bitOr_comm (Word256.bitMaj a b c) c).trans (bitOr_bitMaj_right a b c)

set_option maxHeartbeats 200000 in
  theorem bitAnd_three_le_bitMaj (a b c : Word256) :
      Word256.bitAnd (Word256.bitAnd a b) (Word256.bitMaj a b c) = Word256.bitAnd a b :=
    bitAnd_bitOr_absorb (Word256.bitAnd a b) (Word256.bitOr (Word256.bitAnd b c) (Word256.bitAnd a c))

set_option maxHeartbeats 200000 in
  theorem bitMaj_le_bitOr_three (a b c : Word256) :
      Word256.bitOr (Word256.bitOr a (Word256.bitOr b c)) (Word256.bitMaj a b c) = Word256.bitOr a (Word256.bitOr b c) :=
    let M := Word256.bitMaj a b c
    (bitOr_assoc a (Word256.bitOr b c) M).trans <|
      congrArg (Word256.bitOr a)
        ((bitOr_assoc b c M).trans <|
          (congrArg (Word256.bitOr b) (bitOr_bitMaj_right a b c)).trans <|
          (congrArg (Word256.bitOr b) (bitOr_comm c (Word256.bitAnd a b))).trans <|
          (bitOr_assoc b (Word256.bitAnd a b) c).symm.trans <|
          (congrArg (fun x => Word256.bitOr (Word256.bitOr b x) c) (bitAnd_comm a b)).trans
            (congrArg (Word256.bitOr · c) (bitOr_bitAnd_absorb b a)))

set_option maxHeartbeats 200000 in
  theorem bitClearMask_bitMaj_mid (a b c : Word256) :
      Word256.bitClearMask (Word256.bitMaj a b c) b = Word256.bitClearMask (Word256.bitAnd a c) b :=
    (congrArg (Word256.bitClearMask · b) (bitMaj_comm_left a b c)).trans
      (bitClearMask_bitMaj_self b a c)

set_option maxHeartbeats 200000 in
  theorem bitClearMask_bitMaj_right (a b c : Word256) :
      Word256.bitClearMask (Word256.bitMaj a b c) c = Word256.bitClearMask (Word256.bitAnd a b) c :=
    let X := Word256.bitAnd a b
    let Y := Word256.bitAnd b c
    let Z := Word256.bitAnd a c
    let nc := Word256.bitNot c
    let hY : Word256.bitAnd Y nc = Word256.zero :=
      (bitAnd_assoc b c nc).trans <|
        (congrArg (Word256.bitAnd b) (bitAnd_bitNot_self c)).trans
          (bitAnd_zero_right b)
    let hZ : Word256.bitAnd Z nc = Word256.zero :=
      (bitAnd_assoc a c nc).trans <|
        (congrArg (Word256.bitAnd a) (bitAnd_bitNot_self c)).trans
          (bitAnd_zero_right a)
    let hYZ : Word256.bitAnd (Word256.bitOr Y Z) nc = Word256.zero :=
      (bitAnd_bitOr_distrib_right Y Z nc).trans <|
        (congrArg (Word256.bitOr · (Word256.bitAnd Z nc)) hY).trans <|
        (bitOr_zero_left (Word256.bitAnd Z nc)).trans hZ
    (bitAnd_bitOr_distrib_right X (Word256.bitOr Y Z) nc).trans <|
      (congrArg (Word256.bitOr (Word256.bitAnd X nc)) hYZ).trans
        (bitOr_zero_right (Word256.bitAnd X nc))

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitAnd_all_left (a b c : Word256) :
      Word256.bitMaj (Word256.bitAnd a b) b c = Word256.bitAnd b (Word256.bitOr a c) :=
    (bitMaj_comm_left (Word256.bitAnd a b) b c).trans <|
      (congrArg (fun x => Word256.bitMaj b x c) (bitAnd_comm a b)).trans
        (bitMaj_bitAnd_absorb_left b a c)

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitOr_all_left (a b c : Word256) :
      Word256.bitMaj (Word256.bitOr a b) b c = Word256.bitOr b (Word256.bitAnd a c) :=
    (bitMaj_comm_left (Word256.bitOr a b) b c).trans <|
      (congrArg (fun x => Word256.bitMaj b x c) (bitOr_comm a b)).trans
        (bitMaj_bitOr_absorb_left b a c)

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitAnd_all_right (a b c : Word256) :
      Word256.bitMaj a b (Word256.bitAnd a c) = Word256.bitAnd a (Word256.bitOr b c) :=
    let w := Word256.bitAnd a c
    let X := Word256.bitAnd a b
    let Y := Word256.bitAnd b w
    let Z := Word256.bitAnd a w
    let hSwap : Word256.bitMaj a b w = Word256.bitMaj a w b :=
      (bitOr_comm X (Word256.bitOr Y Z)).trans <|
        (congrArg (Word256.bitOr · X) (bitOr_comm Y Z)).trans <|
        (bitOr_assoc Z Y X).trans
          (congrArg (Word256.bitOr Z) (congrArg (Word256.bitOr · X) (bitAnd_comm b w)))
    hSwap.trans <|
      (bitMaj_bitAnd_absorb_left a c b).trans
        (congrArg (Word256.bitAnd a) (bitOr_comm c b))

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitOr_all_right (a b c : Word256) :
      Word256.bitMaj a b (Word256.bitOr a c) = Word256.bitOr a (Word256.bitAnd b c) :=
    let w := Word256.bitOr a c
    let X := Word256.bitAnd a b
    let Y := Word256.bitAnd b w
    let Z := Word256.bitAnd a w
    let hSwap : Word256.bitMaj a b w = Word256.bitMaj a w b :=
      (bitOr_comm X (Word256.bitOr Y Z)).trans <|
        (congrArg (Word256.bitOr · X) (bitOr_comm Y Z)).trans <|
        (bitOr_assoc Z Y X).trans
          (congrArg (Word256.bitOr Z) (congrArg (Word256.bitOr · X) (bitAnd_comm b w)))
    hSwap.trans <|
      (bitMaj_bitOr_absorb_left a c b).trans
        (congrArg (Word256.bitOr a) (bitAnd_comm c b))

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitAnd_all_mid (a b c : Word256) :
      Word256.bitMaj a (Word256.bitAnd b c) c = Word256.bitAnd c (Word256.bitOr a b) :=
    let v := Word256.bitAnd b c
    let X := Word256.bitAnd a v
    let Y := Word256.bitAnd v c
    let Z := Word256.bitAnd a c
    let hSwap : Word256.bitMaj a v c = Word256.bitMaj a c v :=
      (bitOr_comm X (Word256.bitOr Y Z)).trans <|
        (congrArg (Word256.bitOr · X) (bitOr_comm Y Z)).trans <|
        (bitOr_assoc Z Y X).trans
          (congrArg (Word256.bitOr Z) (congrArg (Word256.bitOr · X) (bitAnd_comm v c)))
    hSwap.trans <|
      (bitMaj_comm_left a c v).trans <|
      (congrArg (Word256.bitMaj c a) (bitAnd_comm b c)).trans
        (bitMaj_bitAnd_all_right c a b)

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitOr_all_mid (a b c : Word256) :
      Word256.bitMaj a (Word256.bitOr b c) c = Word256.bitOr c (Word256.bitAnd a b) :=
    let v := Word256.bitOr b c
    let X := Word256.bitAnd a v
    let Y := Word256.bitAnd v c
    let Z := Word256.bitAnd a c
    let hSwap : Word256.bitMaj a v c = Word256.bitMaj a c v :=
      (bitOr_comm X (Word256.bitOr Y Z)).trans <|
        (congrArg (Word256.bitOr · X) (bitOr_comm Y Z)).trans <|
        (bitOr_assoc Z Y X).trans
          (congrArg (Word256.bitOr Z) (congrArg (Word256.bitOr · X) (bitAnd_comm v c)))
    hSwap.trans <|
      (bitMaj_comm_left a c v).trans <|
      (congrArg (Word256.bitMaj c a) (bitOr_comm b c)).trans
        (bitMaj_bitOr_all_right c a b)

  @[inline]
  def Word256.bitParity (a b c : Word256) : Word256 :=
    Word256.bitXor (Word256.bitXor a b) c

set_option maxHeartbeats 200000 in
  theorem bitParity_self_left (a c : Word256) :
      Word256.bitParity a a c = c :=
    (congrArg (Word256.bitXor · c) (bitXor_self_zero a)).trans
      (bitXor_zero_left c)

set_option maxHeartbeats 200000 in
  theorem bitParity_self_right (a b : Word256) :
      Word256.bitParity a b b = a :=
    bitXor_cancel_right a b

set_option maxHeartbeats 200000 in
  theorem bitParity_self_outer (a b : Word256) :
      Word256.bitParity a b a = b :=
    (congrArg (Word256.bitXor · a) (bitXor_comm a b)).trans
      (bitXor_cancel_right b a)

set_option maxHeartbeats 200000 in
  theorem bitParity_zero_left (b c : Word256) :
      Word256.bitParity Word256.zero b c = Word256.bitXor b c :=
    congrArg (Word256.bitXor · c) (bitXor_zero_left b)

set_option maxHeartbeats 200000 in
  theorem bitParity_comm_left (a b c : Word256) :
      Word256.bitParity a b c = Word256.bitParity b a c :=
    congrArg (Word256.bitXor · c) (bitXor_comm a b)

set_option maxHeartbeats 200000 in
  theorem bitParity_zero_mid (a c : Word256) :
      Word256.bitParity a Word256.zero c = Word256.bitXor a c :=
    congrArg (Word256.bitXor · c) (bitXor_zero_right a)

set_option maxHeartbeats 200000 in
  theorem bitParity_zero_right (a b : Word256) :
      Word256.bitParity a b Word256.zero = Word256.bitXor a b :=
    bitXor_zero_right (Word256.bitXor a b)

set_option maxHeartbeats 200000 in
  theorem bitParity_all_same (a : Word256) :
      Word256.bitParity a a a = a :=
    bitParity_self_left a a

set_option maxHeartbeats 200000 in
  theorem bitParity_bitNot_self_left (a c : Word256) :
      Word256.bitParity a (Word256.bitNot a) c = Word256.bitNot c :=
    (congrArg (Word256.bitXor · c) (bitXor_bitNot_self a)).trans
      (bitXor_max_left c)

set_option maxHeartbeats 200000 in
  theorem bitParity_cancel_left (a b c : Word256) :
      Word256.bitXor a (Word256.bitParity a b c) = Word256.bitXor b c :=
    (bitXor_assoc a (Word256.bitXor a b) c).symm.trans
      (congrArg (Word256.bitXor · c) (bitXor_cancel_left b a))

set_option maxHeartbeats 200000 in
  theorem bitParity_cancel_mid (x y z : Word256) :
      Word256.bitParity x (Word256.bitParity x y z) z = y :=
    (congrArg (Word256.bitXor · z) (bitParity_cancel_left x y z)).trans
      (bitXor_cancel_right y z)

set_option maxHeartbeats 200000 in
  theorem bitParity_cancel_right (x y z : Word256) :
      Word256.bitParity x y (Word256.bitParity x y z) = z :=
    bitXor_cancel_left z (Word256.bitXor x y)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitNot_all (x y z : Word256) :
      Word256.bitParity (Word256.bitNot x) (Word256.bitNot y) (Word256.bitNot z) =
        Word256.bitNot (Word256.bitParity x y z) :=
    let hXY : Word256.bitXor (Word256.bitNot x) (Word256.bitNot y) = Word256.bitXor x y :=
      (congrArg (Word256.bitXor · (Word256.bitNot y)) (bitXor_max_right x).symm).trans <|
        (congrArg (Word256.bitXor (Word256.bitXor x Word256.max)) (bitXor_max_left y).symm).trans <|
        (bitXor_assoc x Word256.max (Word256.bitXor Word256.max y)).trans
          (congrArg (Word256.bitXor x) (bitXor_cancel_left y Word256.max))
    (congrArg (Word256.bitXor · (Word256.bitNot z)) hXY).trans <|
      (congrArg (Word256.bitXor (Word256.bitXor x y)) (bitXor_max_right z).symm).trans <|
      (bitXor_assoc (Word256.bitXor x y) z Word256.max).symm.trans
        (bitXor_max_right (Word256.bitParity x y z))

set_option maxHeartbeats 200000 in
  theorem bitAnd_bitParity_distrib (m x y z : Word256) :
      Word256.bitAnd m (Word256.bitParity x y z) =
        Word256.bitParity (Word256.bitAnd m x) (Word256.bitAnd m y) (Word256.bitAnd m z) :=
    let hAndXor (u v : Word256) : Word256.bitAnd m (Word256.bitXor u v) = Word256.bitXor (Word256.bitAnd m u) (Word256.bitAnd m v) :=
      (bitAnd_comm m (Word256.bitXor u v)).trans <|
        (bitAnd_bitFlipMask_distrib u v m).trans <|
        (congrArg (Word256.bitXor · (Word256.bitAnd v m)) (bitAnd_comm u m)).trans
          (congrArg (Word256.bitXor (Word256.bitAnd m u)) (bitAnd_comm v m))
    (hAndXor (Word256.bitXor x y) z).trans
      (congrArg (Word256.bitXor · (Word256.bitAnd m z)) (hAndXor x y))

set_option maxHeartbeats 200000 in
  theorem bitClearMask_bitParity_distrib (x y z m : Word256) :
      Word256.bitClearMask (Word256.bitParity x y z) m =
        Word256.bitParity (Word256.bitClearMask x m) (Word256.bitClearMask y m) (Word256.bitClearMask z m) :=
    (bitAnd_bitFlipMask_distrib (Word256.bitXor x y) z (Word256.bitNot m)).trans
      (congrArg (Word256.bitXor · (Word256.bitClearMask z m))
        (bitAnd_bitFlipMask_distrib x y (Word256.bitNot m)))

set_option maxHeartbeats 200000 in
  theorem bitParity_bitFlipMask_right (x y z m : Word256) :
      Word256.bitParity x y (Word256.bitFlipMask z m) =
        Word256.bitFlipMask (Word256.bitParity x y z) m :=
    (bitXor_assoc (Word256.bitXor x y) z m).symm

set_option maxHeartbeats 200000 in
  theorem bitParity_bitFlipMask_mid (x y z m : Word256) :
      Word256.bitParity x (Word256.bitFlipMask y m) z =
        Word256.bitFlipMask (Word256.bitParity x y z) m :=
    let xy := Word256.bitXor x y
    (congrArg (Word256.bitXor · z) (bitXor_assoc x y m).symm).trans <|
      (bitXor_assoc xy m z).trans <|
      (congrArg (Word256.bitXor xy) (bitXor_comm m z)).trans
        (bitXor_assoc xy z m).symm

set_option maxHeartbeats 200000 in
  theorem bitParity_bitFlipMask_left (x y z m : Word256) :
      Word256.bitParity (Word256.bitFlipMask x m) y z =
        Word256.bitFlipMask (Word256.bitParity x y z) m :=
    (bitParity_comm_left (Word256.bitFlipMask x m) y z).trans <|
      (bitParity_bitFlipMask_mid y x z m).trans
        (congrArg (Word256.bitFlipMask · m) (bitParity_comm_left y x z))

set_option maxHeartbeats 200000 in
  theorem bitParity_bitFlipMask_left_mid_cancel (x y z m : Word256) :
      Word256.bitParity (Word256.bitFlipMask x m) (Word256.bitFlipMask y m) z =
        Word256.bitParity x y z :=
    (bitParity_bitFlipMask_left x (Word256.bitFlipMask y m) z m).trans <|
      (congrArg (Word256.bitFlipMask · m) (bitParity_bitFlipMask_mid x y z m)).trans
        (bitFlipMask_involutive (Word256.bitParity x y z) m)

set_option maxHeartbeats 200000 in
  theorem bitXor_bitMaj_self_left_mid (x z : Word256) :
      Word256.bitXor (Word256.bitMaj x x z) (Word256.bitParity x x z) =
        Word256.bitXor x z :=
    (congrArg (Word256.bitXor · (Word256.bitParity x x z)) (bitMaj_idemp x z)).trans
      (congrArg (Word256.bitXor x) (bitParity_self_left x z))

set_option maxHeartbeats 200000 in
  theorem bitParity_bitFlipMask_mid_right_cancel (x y z m : Word256) :
      Word256.bitParity x (Word256.bitFlipMask y m) (Word256.bitFlipMask z m) =
        Word256.bitParity x y z :=
    (bitParity_bitFlipMask_mid x y (Word256.bitFlipMask z m) m).trans <|
      (congrArg (Word256.bitFlipMask · m) (bitParity_bitFlipMask_right x y z m)).trans
        (bitFlipMask_involutive (Word256.bitParity x y z) m)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitFlipMask_left_right_cancel (x y z m : Word256) :
      Word256.bitParity (Word256.bitFlipMask x m) y (Word256.bitFlipMask z m) =
        Word256.bitParity x y z :=
    (bitParity_bitFlipMask_left x y (Word256.bitFlipMask z m) m).trans <|
      (congrArg (Word256.bitFlipMask · m) (bitParity_bitFlipMask_right x y z m)).trans
        (bitFlipMask_involutive (Word256.bitParity x y z) m)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitFlipMask_all_three (x y z m : Word256) :
      Word256.bitParity (Word256.bitFlipMask x m) (Word256.bitFlipMask y m) (Word256.bitFlipMask z m) =
        Word256.bitFlipMask (Word256.bitParity x y z) m :=
    (bitParity_bitFlipMask_left_mid_cancel x y (Word256.bitFlipMask z m) m).trans
      (bitParity_bitFlipMask_right x y z m)

set_option maxHeartbeats 200000 in
  theorem bitXor_bitMaj_self_mid_right (x y : Word256) :
      Word256.bitXor (Word256.bitMaj x y y) (Word256.bitParity x y y) =
        Word256.bitXor x y :=
    (congrArg (Word256.bitXor · (Word256.bitParity x y y)) (bitMaj_idemp_right x y)).trans <|
      (congrArg (Word256.bitXor y) (bitParity_self_right x y)).trans
        (bitXor_comm y x)

set_option maxHeartbeats 200000 in
  theorem bitXor_bitMaj_self_left_right (x y : Word256) :
      Word256.bitXor (Word256.bitMaj x y x) (Word256.bitParity x y x) =
        Word256.bitXor x y :=
    (congrArg (Word256.bitXor · (Word256.bitParity x y x)) (bitMaj_idemp_outer x y)).trans
      (congrArg (Word256.bitXor x) (bitParity_self_outer x y))

set_option maxHeartbeats 200000 in
  theorem bitOr_bitParity_self_left_mid (x z : Word256) :
      Word256.bitOr (Word256.bitMaj x x z) (Word256.bitParity x x z) =
        Word256.bitOr x z :=
    (congrArg (Word256.bitOr · (Word256.bitParity x x z)) (bitMaj_idemp x z)).trans
      (congrArg (Word256.bitOr x) (bitParity_self_left x z))

set_option maxHeartbeats 200000 in
  theorem bitOr_bitParity_self_mid_right (x y : Word256) :
      Word256.bitOr (Word256.bitMaj x y y) (Word256.bitParity x y y) =
        Word256.bitOr x y :=
    (congrArg (Word256.bitOr · (Word256.bitParity x y y)) (bitMaj_idemp_right x y)).trans <|
      (congrArg (Word256.bitOr y) (bitParity_self_right x y)).trans
        (bitOr_comm y x)

set_option maxHeartbeats 200000 in
  theorem bitAnd_bitParity_self_left_mid (x z : Word256) :
      Word256.bitAnd (Word256.bitMaj x x z) (Word256.bitParity x x z) =
        Word256.bitAnd x z :=
    (congrArg (Word256.bitAnd · (Word256.bitParity x x z)) (bitMaj_idemp x z)).trans
      (congrArg (Word256.bitAnd x) (bitParity_self_left x z))

set_option maxHeartbeats 200000 in
  theorem bitAnd_bitParity_self_mid_right (x y : Word256) :
      Word256.bitAnd (Word256.bitMaj x y y) (Word256.bitParity x y y) =
        Word256.bitAnd x y :=
    (congrArg (Word256.bitAnd · (Word256.bitParity x y y)) (bitMaj_idemp_right x y)).trans <|
      (congrArg (Word256.bitAnd y) (bitParity_self_right x y)).trans
        (bitAnd_comm y x)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitSetMask_all_three (x y z m : Word256) :
      Word256.bitParity (Word256.bitSetMask x m) (Word256.bitSetMask y m) (Word256.bitSetMask z m) =
        Word256.bitSetMask (Word256.bitParity x y z) m :=
    let cx := Word256.bitClearMask x m
    let cy := Word256.bitClearMask y m
    let cz := Word256.bitClearMask z m
    (congrArg (fun a => Word256.bitParity a (Word256.bitSetMask y m) (Word256.bitSetMask z m))
      (bitFlipMask_clearMask_eq_setMask x m).symm).trans <|
      (congrArg (fun b => Word256.bitParity (Word256.bitFlipMask cx m) b (Word256.bitSetMask z m))
        (bitFlipMask_clearMask_eq_setMask y m).symm).trans <|
      (congrArg (Word256.bitParity (Word256.bitFlipMask cx m) (Word256.bitFlipMask cy m))
        (bitFlipMask_clearMask_eq_setMask z m).symm).trans <|
      (bitParity_bitFlipMask_all_three cx cy cz m).trans <|
      (congrArg (Word256.bitFlipMask · m) (bitClearMask_bitParity_distrib x y z m).symm).trans
        (bitFlipMask_clearMask_eq_setMask (Word256.bitParity x y z) m)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitSetMask_self_left_mid (x m z : Word256) :
      Word256.bitParity (Word256.bitSetMask x m) (Word256.bitSetMask x m) z = z :=
    bitParity_self_left (Word256.bitSetMask x m) z

set_option maxHeartbeats 200000 in
  theorem bitParity_bitClearMask_self_left_mid (x m z : Word256) :
      Word256.bitParity (Word256.bitClearMask x m) (Word256.bitClearMask x m) z = z :=
    bitParity_self_left (Word256.bitClearMask x m) z

set_option maxHeartbeats 200000 in
  theorem bitMux_bitParity_distrib (m a1 b1 c1 a2 b2 c2 : Word256) :
      Word256.bitMux m (Word256.bitParity a1 b1 c1) (Word256.bitParity a2 b2 c2) =
        Word256.bitParity (Word256.bitMux m a1 a2) (Word256.bitMux m b1 b2) (Word256.bitMux m c1 c2) :=
    let hMuxXor (u v : Word256) :
        Word256.bitMux m u v = Word256.bitXor (Word256.bitAnd u m) (Word256.bitClearMask v m) :=
      let A := Word256.bitClearMask v m
      let B := Word256.bitAnd u m
      let hClearAB : Word256.bitClearMask A B = A :=
        (bitClearMask_merge_masks v m B).trans
          (congrArg (Word256.bitClearMask v)
            ((congrArg (Word256.bitOr m) (bitAnd_comm u m)).trans (bitOr_bitAnd_absorb m u)))
      (bitOr_comm B A).trans <|
        (bitFlipMask_clearMask_eq_setMask A B).symm.trans <|
        (congrArg (Word256.bitXor · B) hClearAB).trans
          (bitXor_comm A B)
    let hXor4 (p q r s : Word256) :
        Word256.bitXor (Word256.bitXor p q) (Word256.bitXor r s) =
          Word256.bitXor (Word256.bitXor p r) (Word256.bitXor q s) :=
      (bitXor_assoc (Word256.bitXor p q) r s).symm.trans <|
        (congrArg (Word256.bitXor · s)
          ((bitXor_assoc p q r).trans
            ((congrArg (Word256.bitXor p) (bitXor_comm q r)).trans
              (bitXor_assoc p r q).symm))).trans
          (bitXor_assoc (Word256.bitXor p r) q s)
    let hMuxXorDistrib (u1 v1 u2 v2 : Word256) :
        Word256.bitMux m (Word256.bitXor u1 v1) (Word256.bitXor u2 v2) =
          Word256.bitXor (Word256.bitMux m u1 u2) (Word256.bitMux m v1 v2) :=
      (hMuxXor (Word256.bitXor u1 v1) (Word256.bitXor u2 v2)).trans <|
        (congrArg (Word256.bitXor · (Word256.bitClearMask (Word256.bitXor u2 v2) m))
          (bitAnd_bitFlipMask_distrib u1 v1 m)).trans <|
        (congrArg (Word256.bitXor (Word256.bitXor (Word256.bitAnd u1 m) (Word256.bitAnd v1 m)))
          (bitAnd_bitFlipMask_distrib u2 v2 (Word256.bitNot m))).trans <|
        (hXor4 (Word256.bitAnd u1 m) (Word256.bitAnd v1 m)
          (Word256.bitClearMask u2 m) (Word256.bitClearMask v2 m)).trans <|
        (congrArg (Word256.bitXor · (Word256.bitXor (Word256.bitAnd v1 m) (Word256.bitClearMask v2 m)))
          (hMuxXor u1 u2).symm).trans
          (congrArg (Word256.bitXor (Word256.bitMux m u1 u2)) (hMuxXor v1 v2).symm)
    (hMuxXorDistrib (Word256.bitXor a1 b1) c1 (Word256.bitXor a2 b2) c2).trans
      (congrArg (Word256.bitXor · (Word256.bitMux m c1 c2)) (hMuxXorDistrib a1 b1 a2 b2))

set_option maxHeartbeats 200000 in
  theorem bitParity_bitMux_self_branches (m x y z : Word256) :
      Word256.bitParity (Word256.bitMux m x y) (Word256.bitMux m x y) z = z :=
    bitParity_self_left (Word256.bitMux m x y) z

set_option maxHeartbeats 200000 in
  theorem bitParity_bitMux_complement_masks (m x y : Word256) :
      Word256.bitParity (Word256.bitMux m x y) (Word256.bitMux (Word256.bitNot m) x y) (Word256.bitXor x y) =
        Word256.zero :=
    let hMuxCompl :
        Word256.bitXor (Word256.bitMux m x y) (Word256.bitMux (Word256.bitNot m) x y) =
          Word256.bitXor x y :=
      (congrArg (Word256.bitXor (Word256.bitMux m x y)) (bitMux_bitNot_mask m x y)).trans <|
        (bitParity_zero_right (Word256.bitMux m x y) (Word256.bitMux m y x)).symm.trans <|
        (congrArg (Word256.bitParity (Word256.bitMux m x y) (Word256.bitMux m y x))
          (bitMux_self m Word256.zero).symm).trans <|
        (bitMux_bitParity_distrib m x y Word256.zero y x Word256.zero).symm.trans <|
        (congrArg (fun a => Word256.bitMux m a (Word256.bitParity y x Word256.zero))
          (bitParity_zero_right x y)).trans <|
        (congrArg (Word256.bitMux m (Word256.bitXor x y))
          ((bitParity_zero_right y x).trans (bitXor_comm y x))).trans
          (bitMux_self m (Word256.bitXor x y))
    (congrArg (Word256.bitXor · (Word256.bitXor x y)) hMuxCompl).trans
      (bitXor_self_zero (Word256.bitXor x y))

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitParity_self_left_mid (x z : Word256) :
      Word256.bitMaj (Word256.bitMaj x x z) (Word256.bitParity x x z) z = z :=
    (congrArg (fun a => Word256.bitMaj a (Word256.bitParity x x z) z) (bitMaj_idemp x z)).trans <|
      (congrArg (fun b => Word256.bitMaj x b z) (bitParity_self_left x z)).trans
        (bitMaj_idemp_right x z)

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitParity_self_mid_right (x y : Word256) :
      Word256.bitMaj (Word256.bitMaj x y y) (Word256.bitParity x y y) x = x :=
    (congrArg (fun a => Word256.bitMaj a (Word256.bitParity x y y) x) (bitMaj_idemp_right x y)).trans <|
      (congrArg (fun b => Word256.bitMaj y b x) (bitParity_self_right x y)).trans
        (bitMaj_idemp_right y x)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitMaj_self_left_mid (x z : Word256) :
      Word256.bitParity (Word256.bitMaj x x z) (Word256.bitParity x x z) z = x :=
    (congrArg (fun a => Word256.bitParity a (Word256.bitParity x x z) z) (bitMaj_idemp x z)).trans <|
      (congrArg (fun b => Word256.bitParity x b z) (bitParity_self_left x z)).trans
        (bitParity_self_right x z)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitMaj_self_mid_right (x y : Word256) :
      Word256.bitParity (Word256.bitMaj x y y) (Word256.bitParity x y y) x = y :=
    (congrArg (fun a => Word256.bitParity a (Word256.bitParity x y y) x) (bitMaj_idemp_right x y)).trans <|
      (congrArg (fun b => Word256.bitParity y b x) (bitParity_self_right x y)).trans
        (bitParity_self_right y x)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitNot_pair_left_mid (x y z : Word256) :
      Word256.bitParity (Word256.bitNot x) (Word256.bitNot y) z = Word256.bitParity x y z :=
    (congrArg (fun a => Word256.bitParity a (Word256.bitNot y) z) (bitXor_max_right x).symm).trans <|
      (congrArg (fun b => Word256.bitParity (Word256.bitFlipMask x Word256.max) b z) (bitXor_max_right y).symm).trans
        (bitParity_bitFlipMask_left_mid_cancel x y z Word256.max)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitNot_pair_mid_right (x y z : Word256) :
      Word256.bitParity x (Word256.bitNot y) (Word256.bitNot z) = Word256.bitParity x y z :=
    (congrArg (fun b => Word256.bitParity x b (Word256.bitNot z)) (bitXor_max_right y).symm).trans <|
      (congrArg (fun c => Word256.bitParity x (Word256.bitFlipMask y Word256.max) c) (bitXor_max_right z).symm).trans
        (bitParity_bitFlipMask_mid_right_cancel x y z Word256.max)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitNot_pair_left_right (x y z : Word256) :
      Word256.bitParity (Word256.bitNot x) y (Word256.bitNot z) = Word256.bitParity x y z :=
    (congrArg (fun a => Word256.bitParity a y (Word256.bitNot z)) (bitXor_max_right x).symm).trans <|
      (congrArg (fun c => Word256.bitParity (Word256.bitFlipMask x Word256.max) y c) (bitXor_max_right z).symm).trans
        (bitParity_bitFlipMask_left_right_cancel x y z Word256.max)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitSetMask_left_mid_clear_right (x y z m : Word256) :
      Word256.bitParity (Word256.bitSetMask x m) (Word256.bitSetMask y m) (Word256.bitClearMask z m) =
        Word256.bitClearMask (Word256.bitParity x y z) m :=
    let cx := Word256.bitClearMask x m
    let cy := Word256.bitClearMask y m
    let cz := Word256.bitClearMask z m
    (congrArg (fun a => Word256.bitParity a (Word256.bitSetMask y m) cz)
      (bitFlipMask_clearMask_eq_setMask x m).symm).trans <|
      (congrArg (fun b => Word256.bitParity (Word256.bitFlipMask cx m) b cz)
        (bitFlipMask_clearMask_eq_setMask y m).symm).trans <|
      (bitParity_bitFlipMask_left_mid_cancel cx cy cz m).trans
        (bitClearMask_bitParity_distrib x y z m).symm

set_option maxHeartbeats 200000 in
  theorem bitOr_bitParity_bitClearMask_bitAnd (x y z m : Word256) :
      Word256.bitOr (Word256.bitClearMask (Word256.bitParity x y z) m) (Word256.bitAnd (Word256.bitParity x y z) m) =
        Word256.bitParity x y z :=
    bitOr_bitClearMask_bitAnd_self (Word256.bitParity x y z) m

set_option maxHeartbeats 200000 in
  theorem bitXor_bitParity_bitClearMask_bitAnd (x y z m : Word256) :
      Word256.bitXor (Word256.bitClearMask (Word256.bitParity x y z) m) (Word256.bitAnd (Word256.bitParity x y z) m) =
        Word256.bitParity x y z :=
    let p := Word256.bitParity x y z
    (congrArg (Word256.bitXor · (Word256.bitAnd p m)) (bitFlipMask_bitAnd_self p m).symm).trans
      (bitXor_cancel_right p (Word256.bitAnd p m))

set_option maxHeartbeats 200000 in
  theorem bitOr_bitMaj_bitClearMask_bitAnd (x y z m : Word256) :
      Word256.bitOr (Word256.bitClearMask (Word256.bitMaj x y z) m) (Word256.bitAnd (Word256.bitMaj x y z) m) =
        Word256.bitMaj x y z :=
    bitOr_bitClearMask_bitAnd_self (Word256.bitMaj x y z) m

set_option maxHeartbeats 200000 in
  theorem bitXor_bitMaj_bitClearMask_bitAnd (x y z m : Word256) :
      Word256.bitXor (Word256.bitClearMask (Word256.bitMaj x y z) m) (Word256.bitAnd (Word256.bitMaj x y z) m) =
        Word256.bitMaj x y z :=
    let p := Word256.bitMaj x y z
    (congrArg (Word256.bitXor · (Word256.bitAnd p m)) (bitFlipMask_bitAnd_self p m).symm).trans
      (bitXor_cancel_right p (Word256.bitAnd p m))

set_option maxHeartbeats 200000 in
  theorem bitMux_bitMaj_distrib (m a1 b1 c1 a2 b2 c2 : Word256) :
      Word256.bitMux m (Word256.bitMaj a1 b1 c1) (Word256.bitMaj a2 b2 c2) =
        Word256.bitMaj (Word256.bitMux m a1 a2) (Word256.bitMux m b1 b2) (Word256.bitMux m c1 c2) :=
    let hMuxAnd (u1 v1 u2 v2 : Word256) :
        Word256.bitMux m (Word256.bitAnd u1 v1) (Word256.bitAnd u2 v2) =
          Word256.bitAnd (Word256.bitMux m u1 u2) (Word256.bitMux m v1 v2) :=
      ((bitAnd_bitMux_distrib_left m v1 v2 (Word256.bitMux m u1 u2)).trans <|
        (congrArg (fun x => Word256.bitMux m x (Word256.bitAnd (Word256.bitMux m u1 u2) v2))
          (bitAnd_bitMux_distrib_right m u1 u2 v1)).trans <|
        (bitMux_nested_left m (Word256.bitAnd u1 v1) (Word256.bitAnd u2 v1)
          (Word256.bitAnd (Word256.bitMux m u1 u2) v2)).trans <|
        (congrArg (Word256.bitMux m (Word256.bitAnd u1 v1))
          (bitAnd_bitMux_distrib_right m u1 u2 v2)).trans
          (bitMux_nested_right m (Word256.bitAnd u1 v1) (Word256.bitAnd u1 v2) (Word256.bitAnd u2 v2))).symm
    let hMuxOr (u1 v1 u2 v2 : Word256) :
        Word256.bitMux m (Word256.bitOr u1 v1) (Word256.bitOr u2 v2) =
          Word256.bitOr (Word256.bitMux m u1 u2) (Word256.bitMux m v1 v2) :=
      ((bitOr_bitMux_distrib_left m v1 v2 (Word256.bitMux m u1 u2)).trans <|
        (congrArg (fun x => Word256.bitMux m x (Word256.bitOr (Word256.bitMux m u1 u2) v2))
          (bitOr_bitMux_distrib_right m u1 u2 v1)).trans <|
        (bitMux_nested_left m (Word256.bitOr u1 v1) (Word256.bitOr u2 v1)
          (Word256.bitOr (Word256.bitMux m u1 u2) v2)).trans <|
        (congrArg (Word256.bitMux m (Word256.bitOr u1 v1))
          (bitOr_bitMux_distrib_right m u1 u2 v2)).trans
          (bitMux_nested_right m (Word256.bitOr u1 v1) (Word256.bitOr u1 v2) (Word256.bitOr u2 v2))).symm
    let ab1 := Word256.bitAnd a1 b1
    let bc1 := Word256.bitAnd b1 c1
    let ac1 := Word256.bitAnd a1 c1
    let ab2 := Word256.bitAnd a2 b2
    let bc2 := Word256.bitAnd b2 c2
    let ac2 := Word256.bitAnd a2 c2
    (hMuxOr ab1 (Word256.bitOr bc1 ac1) ab2 (Word256.bitOr bc2 ac2)).trans <|
      (congrArg (Word256.bitOr · (Word256.bitMux m (Word256.bitOr bc1 ac1) (Word256.bitOr bc2 ac2)))
        (hMuxAnd a1 b1 a2 b2)).trans <|
      congrArg (Word256.bitOr (Word256.bitAnd (Word256.bitMux m a1 a2) (Word256.bitMux m b1 b2)))
        ((hMuxOr bc1 ac1 bc2 ac2).trans <|
          (congrArg (Word256.bitOr · (Word256.bitMux m ac1 ac2)) (hMuxAnd b1 c1 b2 c2)).trans
            (congrArg (Word256.bitOr (Word256.bitAnd (Word256.bitMux m b1 b2) (Word256.bitMux m c1 c2)))
              (hMuxAnd a1 c1 a2 c2)))

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitMux_self_branches (m x y z : Word256) :
      Word256.bitMaj (Word256.bitMux m x y) (Word256.bitMux m x y) z = Word256.bitMux m x y :=
    bitMaj_idemp (Word256.bitMux m x y) z

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitSetMask_self_left_mid (x m z : Word256) :
      Word256.bitMaj (Word256.bitSetMask x m) (Word256.bitSetMask x m) z = Word256.bitSetMask x m :=
    bitMaj_idemp (Word256.bitSetMask x m) z

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitClearMask_self_left_mid (x m z : Word256) :
      Word256.bitMaj (Word256.bitClearMask x m) (Word256.bitClearMask x m) z = Word256.bitClearMask x m :=
    bitMaj_idemp (Word256.bitClearMask x m) z

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitFlipMask_self_left_mid (x m z : Word256) :
      Word256.bitMaj (Word256.bitFlipMask x m) (Word256.bitFlipMask x m) z = Word256.bitFlipMask x m :=
    bitMaj_idemp (Word256.bitFlipMask x m) z

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitSetMask_all_three (x y z m : Word256) :
      Word256.bitMaj (Word256.bitSetMask x m) (Word256.bitSetMask y m) (Word256.bitSetMask z m) =
        Word256.bitSetMask (Word256.bitMaj x y z) m :=
    (congrArg (fun a => Word256.bitMaj a (Word256.bitSetMask y m) (Word256.bitSetMask z m))
      (bitMux_eq_setMask_of_max_left m x).symm).trans <|
      (congrArg (fun b => Word256.bitMaj (Word256.bitMux m Word256.max x) b (Word256.bitSetMask z m))
        (bitMux_eq_setMask_of_max_left m y).symm).trans <|
      (congrArg (Word256.bitMaj (Word256.bitMux m Word256.max x) (Word256.bitMux m Word256.max y))
        (bitMux_eq_setMask_of_max_left m z).symm).trans <|
      (bitMux_bitMaj_distrib m Word256.max Word256.max Word256.max x y z).symm.trans <|
      (congrArg (fun a => Word256.bitMux m a (Word256.bitMaj x y z)) (bitMaj_all_same Word256.max)).trans
        (bitMux_eq_setMask_of_max_left m (Word256.bitMaj x y z))

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitClearMask_all_three (x y z m : Word256) :
      Word256.bitMaj (Word256.bitClearMask x m) (Word256.bitClearMask y m) (Word256.bitClearMask z m) =
        Word256.bitClearMask (Word256.bitMaj x y z) m :=
    (congrArg (fun a => Word256.bitMaj a (Word256.bitClearMask y m) (Word256.bitClearMask z m))
      (bitMux_eq_clearMask_of_zero_left m x).symm).trans <|
      (congrArg (fun b => Word256.bitMaj (Word256.bitMux m Word256.zero x) b (Word256.bitClearMask z m))
        (bitMux_eq_clearMask_of_zero_left m y).symm).trans <|
      (congrArg (Word256.bitMaj (Word256.bitMux m Word256.zero x) (Word256.bitMux m Word256.zero y))
        (bitMux_eq_clearMask_of_zero_left m z).symm).trans <|
      (bitMux_bitMaj_distrib m Word256.zero Word256.zero Word256.zero x y z).symm.trans <|
      (congrArg (fun a => Word256.bitMux m a (Word256.bitMaj x y z)) (bitMaj_all_same Word256.zero)).trans
        (bitMux_eq_clearMask_of_zero_left m (Word256.bitMaj x y z))

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitMux_complement_masks (m x y : Word256) :
      Word256.bitMaj (Word256.bitMux m x y) (Word256.bitMux (Word256.bitNot m) x y) (Word256.bitAnd x y) =
        Word256.bitAnd x y :=
    let xy := Word256.bitAnd x y
    let hMajAnd : Word256.bitMaj x y xy = xy :=
      (bitMaj_bitAnd_all_right x y y).trans (congrArg (Word256.bitAnd x) (bitOr_self y))
    (congrArg (fun b => Word256.bitMaj (Word256.bitMux m x y) b xy) (bitMux_bitNot_mask m x y)).trans <|
      (congrArg (Word256.bitMaj (Word256.bitMux m x y) (Word256.bitMux m y x)) (bitMux_self m xy).symm).trans <|
      (bitMux_bitMaj_distrib m x y xy y x xy).symm.trans <|
      (congrArg (fun a => Word256.bitMux m a (Word256.bitMaj y x xy)) hMajAnd).trans <|
      (congrArg (Word256.bitMux m xy) ((bitMaj_comm_left y x xy).trans hMajAnd)).trans
        (bitMux_self m xy)

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitSetMask_left_mid (x y z m : Word256) :
      Word256.bitMaj (Word256.bitSetMask x m) (Word256.bitSetMask y m) z =
        Word256.bitSetMask (Word256.bitMaj x y z) m :=
    (congrArg (fun a => Word256.bitMaj a (Word256.bitSetMask y m) z)
      (bitMux_eq_setMask_of_max_left m x).symm).trans <|
      (congrArg (fun b => Word256.bitMaj (Word256.bitMux m Word256.max x) b z)
        (bitMux_eq_setMask_of_max_left m y).symm).trans <|
      (congrArg (Word256.bitMaj (Word256.bitMux m Word256.max x) (Word256.bitMux m Word256.max y))
        (bitMux_self m z).symm).trans <|
      (bitMux_bitMaj_distrib m Word256.max Word256.max z x y z).symm.trans <|
      (congrArg (fun a => Word256.bitMux m a (Word256.bitMaj x y z)) (bitMaj_idemp Word256.max z)).trans
        (bitMux_eq_setMask_of_max_left m (Word256.bitMaj x y z))

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitClearMask_left_mid (x y z m : Word256) :
      Word256.bitMaj (Word256.bitClearMask x m) (Word256.bitClearMask y m) z =
        Word256.bitClearMask (Word256.bitMaj x y z) m :=
    (congrArg (fun a => Word256.bitMaj a (Word256.bitClearMask y m) z)
      (bitMux_eq_clearMask_of_zero_left m x).symm).trans <|
      (congrArg (fun b => Word256.bitMaj (Word256.bitMux m Word256.zero x) b z)
        (bitMux_eq_clearMask_of_zero_left m y).symm).trans <|
      (congrArg (Word256.bitMaj (Word256.bitMux m Word256.zero x) (Word256.bitMux m Word256.zero y))
        (bitMux_self m z).symm).trans <|
      (bitMux_bitMaj_distrib m Word256.zero Word256.zero z x y z).symm.trans <|
      (congrArg (fun a => Word256.bitMux m a (Word256.bitMaj x y z)) (bitMaj_idemp Word256.zero z)).trans
        (bitMux_eq_clearMask_of_zero_left m (Word256.bitMaj x y z))

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitSetMask_mid_right (x y z m : Word256) :
      Word256.bitMaj x (Word256.bitSetMask y m) (Word256.bitSetMask z m) =
        Word256.bitSetMask (Word256.bitMaj x y z) m :=
    (congrArg (fun a => Word256.bitMaj a (Word256.bitSetMask y m) (Word256.bitSetMask z m))
      (bitMux_self m x).symm).trans <|
      (congrArg (fun b => Word256.bitMaj (Word256.bitMux m x x) b (Word256.bitSetMask z m))
        (bitMux_eq_setMask_of_max_left m y).symm).trans <|
      (congrArg (Word256.bitMaj (Word256.bitMux m x x) (Word256.bitMux m Word256.max y))
        (bitMux_eq_setMask_of_max_left m z).symm).trans <|
      (bitMux_bitMaj_distrib m x Word256.max Word256.max x y z).symm.trans <|
      (congrArg (fun a => Word256.bitMux m a (Word256.bitMaj x y z)) (bitMaj_idemp_right x Word256.max)).trans
        (bitMux_eq_setMask_of_max_left m (Word256.bitMaj x y z))

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitClearMask_mid_right (x y z m : Word256) :
      Word256.bitMaj x (Word256.bitClearMask y m) (Word256.bitClearMask z m) =
        Word256.bitClearMask (Word256.bitMaj x y z) m :=
    (congrArg (fun a => Word256.bitMaj a (Word256.bitClearMask y m) (Word256.bitClearMask z m))
      (bitMux_self m x).symm).trans <|
      (congrArg (fun b => Word256.bitMaj (Word256.bitMux m x x) b (Word256.bitClearMask z m))
        (bitMux_eq_clearMask_of_zero_left m y).symm).trans <|
      (congrArg (Word256.bitMaj (Word256.bitMux m x x) (Word256.bitMux m Word256.zero y))
        (bitMux_eq_clearMask_of_zero_left m z).symm).trans <|
      (bitMux_bitMaj_distrib m x Word256.zero Word256.zero x y z).symm.trans <|
      (congrArg (fun a => Word256.bitMux m a (Word256.bitMaj x y z)) (bitMaj_idemp_right x Word256.zero)).trans
        (bitMux_eq_clearMask_of_zero_left m (Word256.bitMaj x y z))

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitSetMask_left_right (x y z m : Word256) :
      Word256.bitMaj (Word256.bitSetMask x m) y (Word256.bitSetMask z m) =
        Word256.bitSetMask (Word256.bitMaj x y z) m :=
    (congrArg (fun a => Word256.bitMaj a y (Word256.bitSetMask z m))
      (bitMux_eq_setMask_of_max_left m x).symm).trans <|
      (congrArg (fun b => Word256.bitMaj (Word256.bitMux m Word256.max x) b (Word256.bitSetMask z m))
        (bitMux_self m y).symm).trans <|
      (congrArg (Word256.bitMaj (Word256.bitMux m Word256.max x) (Word256.bitMux m y y))
        (bitMux_eq_setMask_of_max_left m z).symm).trans <|
      (bitMux_bitMaj_distrib m Word256.max y Word256.max x y z).symm.trans <|
      (congrArg (fun a => Word256.bitMux m a (Word256.bitMaj x y z)) (bitMaj_idemp_outer Word256.max y)).trans
        (bitMux_eq_setMask_of_max_left m (Word256.bitMaj x y z))

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitClearMask_left_right (x y z m : Word256) :
      Word256.bitMaj (Word256.bitClearMask x m) y (Word256.bitClearMask z m) =
        Word256.bitClearMask (Word256.bitMaj x y z) m :=
    (congrArg (fun a => Word256.bitMaj a y (Word256.bitClearMask z m))
      (bitMux_eq_clearMask_of_zero_left m x).symm).trans <|
      (congrArg (fun b => Word256.bitMaj (Word256.bitMux m Word256.zero x) b (Word256.bitClearMask z m))
        (bitMux_self m y).symm).trans <|
      (congrArg (Word256.bitMaj (Word256.bitMux m Word256.zero x) (Word256.bitMux m y y))
        (bitMux_eq_clearMask_of_zero_left m z).symm).trans <|
      (bitMux_bitMaj_distrib m Word256.zero y Word256.zero x y z).symm.trans <|
      (congrArg (fun a => Word256.bitMux m a (Word256.bitMaj x y z)) (bitMaj_idemp_outer Word256.zero y)).trans
        (bitMux_eq_clearMask_of_zero_left m (Word256.bitMaj x y z))

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitSetMask_left_clear_mid_right (x y z m : Word256) :
      Word256.bitMaj (Word256.bitSetMask x m) (Word256.bitClearMask y m) (Word256.bitClearMask z m) =
        Word256.bitClearMask (Word256.bitMaj x y z) m :=
    (congrArg (fun a => Word256.bitMaj a (Word256.bitClearMask y m) (Word256.bitClearMask z m))
      (bitMux_eq_setMask_of_max_left m x).symm).trans <|
      (congrArg (fun b => Word256.bitMaj (Word256.bitMux m Word256.max x) b (Word256.bitClearMask z m))
        (bitMux_eq_clearMask_of_zero_left m y).symm).trans <|
      (congrArg (Word256.bitMaj (Word256.bitMux m Word256.max x) (Word256.bitMux m Word256.zero y))
        (bitMux_eq_clearMask_of_zero_left m z).symm).trans <|
      (bitMux_bitMaj_distrib m Word256.max Word256.zero Word256.zero x y z).symm.trans <|
      (congrArg (fun a => Word256.bitMux m a (Word256.bitMaj x y z)) (bitMaj_idemp_right Word256.max Word256.zero)).trans
        (bitMux_eq_clearMask_of_zero_left m (Word256.bitMaj x y z))

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitClearMask_left_set_mid_right (x y z m : Word256) :
      Word256.bitMaj (Word256.bitClearMask x m) (Word256.bitSetMask y m) (Word256.bitSetMask z m) =
        Word256.bitSetMask (Word256.bitMaj x y z) m :=
    (congrArg (fun a => Word256.bitMaj a (Word256.bitSetMask y m) (Word256.bitSetMask z m))
      (bitMux_eq_clearMask_of_zero_left m x).symm).trans <|
      (congrArg (fun b => Word256.bitMaj (Word256.bitMux m Word256.zero x) b (Word256.bitSetMask z m))
        (bitMux_eq_setMask_of_max_left m y).symm).trans <|
      (congrArg (Word256.bitMaj (Word256.bitMux m Word256.zero x) (Word256.bitMux m Word256.max y))
        (bitMux_eq_setMask_of_max_left m z).symm).trans <|
      (bitMux_bitMaj_distrib m Word256.zero Word256.max Word256.max x y z).symm.trans <|
      (congrArg (fun a => Word256.bitMux m a (Word256.bitMaj x y z)) (bitMaj_idemp_right Word256.zero Word256.max)).trans
        (bitMux_eq_setMask_of_max_left m (Word256.bitMaj x y z))

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitParity_self_left_right (x y : Word256) :
      Word256.bitMaj (Word256.bitMaj x y x) (Word256.bitParity x y x) y = y :=
    (congrArg (fun a => Word256.bitMaj a (Word256.bitParity x y x) y) (bitMaj_idemp_outer x y)).trans <|
      (congrArg (fun b => Word256.bitMaj x b y) (bitParity_self_outer x y)).trans
        (bitMaj_idemp_right x y)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitMaj_self_left_right (x y : Word256) :
      Word256.bitParity (Word256.bitMaj x y x) (Word256.bitParity x y x) y = x :=
    (congrArg (fun a => Word256.bitParity a (Word256.bitParity x y x) y) (bitMaj_idemp_outer x y)).trans <|
      (congrArg (fun b => Word256.bitParity x b y) (bitParity_self_outer x y)).trans
        (bitParity_self_right x y)

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitClearMask_left_mid_set_right (x y z m : Word256) :
      Word256.bitMaj (Word256.bitClearMask x m) (Word256.bitClearMask y m) (Word256.bitSetMask z m) =
        Word256.bitClearMask (Word256.bitMaj x y z) m :=
    (congrArg (fun a => Word256.bitMaj a (Word256.bitClearMask y m) (Word256.bitSetMask z m))
      (bitMux_eq_clearMask_of_zero_left m x).symm).trans <|
      (congrArg (fun b => Word256.bitMaj (Word256.bitMux m Word256.zero x) b (Word256.bitSetMask z m))
        (bitMux_eq_clearMask_of_zero_left m y).symm).trans <|
      (congrArg (Word256.bitMaj (Word256.bitMux m Word256.zero x) (Word256.bitMux m Word256.zero y))
        (bitMux_eq_setMask_of_max_left m z).symm).trans <|
      (bitMux_bitMaj_distrib m Word256.zero Word256.zero Word256.max x y z).symm.trans <|
      (congrArg (fun a => Word256.bitMux m a (Word256.bitMaj x y z)) (bitMaj_idemp Word256.zero Word256.max)).trans
        (bitMux_eq_clearMask_of_zero_left m (Word256.bitMaj x y z))

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitSetMask_left_clear_mid_set_right (x y z m : Word256) :
      Word256.bitMaj (Word256.bitSetMask x m) (Word256.bitClearMask y m) (Word256.bitSetMask z m) =
        Word256.bitSetMask (Word256.bitMaj x y z) m :=
    (congrArg (fun a => Word256.bitMaj a (Word256.bitClearMask y m) (Word256.bitSetMask z m))
      (bitMux_eq_setMask_of_max_left m x).symm).trans <|
      (congrArg (fun b => Word256.bitMaj (Word256.bitMux m Word256.max x) b (Word256.bitSetMask z m))
        (bitMux_eq_clearMask_of_zero_left m y).symm).trans <|
      (congrArg (Word256.bitMaj (Word256.bitMux m Word256.max x) (Word256.bitMux m Word256.zero y))
        (bitMux_eq_setMask_of_max_left m z).symm).trans <|
      (bitMux_bitMaj_distrib m Word256.max Word256.zero Word256.max x y z).symm.trans <|
      (congrArg (fun a => Word256.bitMux m a (Word256.bitMaj x y z)) (bitMaj_idemp_outer Word256.max Word256.zero)).trans
        (bitMux_eq_setMask_of_max_left m (Word256.bitMaj x y z))

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitSetMask_left_mid_clear_right (x y z m : Word256) :
      Word256.bitMaj (Word256.bitSetMask x m) (Word256.bitSetMask y m) (Word256.bitClearMask z m) =
        Word256.bitSetMask (Word256.bitMaj x y z) m :=
    (congrArg (fun a => Word256.bitMaj a (Word256.bitSetMask y m) (Word256.bitClearMask z m))
      (bitMux_eq_setMask_of_max_left m x).symm).trans <|
      (congrArg (fun b => Word256.bitMaj (Word256.bitMux m Word256.max x) b (Word256.bitClearMask z m))
        (bitMux_eq_setMask_of_max_left m y).symm).trans <|
      (congrArg (Word256.bitMaj (Word256.bitMux m Word256.max x) (Word256.bitMux m Word256.max y))
        (bitMux_eq_clearMask_of_zero_left m z).symm).trans <|
      (bitMux_bitMaj_distrib m Word256.max Word256.max Word256.zero x y z).symm.trans <|
      (congrArg (fun a => Word256.bitMux m a (Word256.bitMaj x y z)) (bitMaj_idemp Word256.max Word256.zero)).trans
        (bitMux_eq_setMask_of_max_left m (Word256.bitMaj x y z))

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitClearMask_left_set_mid_clear_right (x y z m : Word256) :
      Word256.bitMaj (Word256.bitClearMask x m) (Word256.bitSetMask y m) (Word256.bitClearMask z m) =
        Word256.bitClearMask (Word256.bitMaj x y z) m :=
    (congrArg (fun a => Word256.bitMaj a (Word256.bitSetMask y m) (Word256.bitClearMask z m))
      (bitMux_eq_clearMask_of_zero_left m x).symm).trans <|
      (congrArg (fun b => Word256.bitMaj (Word256.bitMux m Word256.zero x) b (Word256.bitClearMask z m))
        (bitMux_eq_setMask_of_max_left m y).symm).trans <|
      (congrArg (Word256.bitMaj (Word256.bitMux m Word256.zero x) (Word256.bitMux m Word256.max y))
        (bitMux_eq_clearMask_of_zero_left m z).symm).trans <|
      (bitMux_bitMaj_distrib m Word256.zero Word256.max Word256.zero x y z).symm.trans <|
      (congrArg (fun a => Word256.bitMux m a (Word256.bitMaj x y z)) (bitMaj_idemp_outer Word256.zero Word256.max)).trans
        (bitMux_eq_clearMask_of_zero_left m (Word256.bitMaj x y z))

set_option maxHeartbeats 200000 in
  theorem bitOr_bitMaj_self_left_right (x y : Word256) :
      Word256.bitOr (Word256.bitMaj x y x) (Word256.bitParity x y x) =
        Word256.bitOr x y :=
    (congrArg (Word256.bitOr · (Word256.bitParity x y x)) (bitMaj_idemp_outer x y)).trans
      (congrArg (Word256.bitOr x) (bitParity_self_outer x y))

set_option maxHeartbeats 200000 in
  theorem bitAnd_bitMaj_self_left_right (x y : Word256) :
      Word256.bitAnd (Word256.bitMaj x y x) (Word256.bitParity x y x) =
        Word256.bitAnd x y :=
    (congrArg (Word256.bitAnd · (Word256.bitParity x y x)) (bitMaj_idemp_outer x y)).trans
      (congrArg (Word256.bitAnd x) (bitParity_self_outer x y))

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitNot_pair_left_mid_self (x z : Word256) :
      Word256.bitMaj (Word256.bitNot x) (Word256.bitNot x) z = Word256.bitNot x :=
    bitMaj_idemp (Word256.bitNot x) z

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitNot_pair_mid_right_self (x y : Word256) :
      Word256.bitMaj x (Word256.bitNot y) (Word256.bitNot y) = Word256.bitNot y :=
    bitMaj_idemp_right x (Word256.bitNot y)

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitNot_pair_left_right_self (x y : Word256) :
      Word256.bitMaj (Word256.bitNot x) y (Word256.bitNot x) = Word256.bitNot x :=
    bitMaj_idemp_outer (Word256.bitNot x) y

set_option maxHeartbeats 200000 in
  theorem bitParity_bitNot_pair_left_mid_self (x z : Word256) :
      Word256.bitParity (Word256.bitNot x) (Word256.bitNot x) z = z :=
    bitParity_self_left (Word256.bitNot x) z

set_option maxHeartbeats 200000 in
  theorem bitParity_bitNot_pair_mid_right_self (x y : Word256) :
      Word256.bitParity x (Word256.bitNot y) (Word256.bitNot y) = x :=
    bitParity_self_right x (Word256.bitNot y)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitNot_pair_left_right_self (x y : Word256) :
      Word256.bitParity (Word256.bitNot x) y (Word256.bitNot x) = y :=
    bitParity_self_outer (Word256.bitNot x) y

set_option maxHeartbeats 200000 in
  theorem bitParity_bitSetMask_mid_right_self (x y m : Word256) :
      Word256.bitParity x (Word256.bitSetMask y m) (Word256.bitSetMask y m) = x :=
    bitParity_self_right x (Word256.bitSetMask y m)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitClearMask_mid_right_self (x y m : Word256) :
      Word256.bitParity x (Word256.bitClearMask y m) (Word256.bitClearMask y m) = x :=
    bitParity_self_right x (Word256.bitClearMask y m)

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitSetMask_mid_right_self (x y m : Word256) :
      Word256.bitMaj x (Word256.bitSetMask y m) (Word256.bitSetMask y m) =
        Word256.bitSetMask y m :=
    bitMaj_idemp_right x (Word256.bitSetMask y m)

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitClearMask_mid_right_self (x y m : Word256) :
      Word256.bitMaj x (Word256.bitClearMask y m) (Word256.bitClearMask y m) =
        Word256.bitClearMask y m :=
    bitMaj_idemp_right x (Word256.bitClearMask y m)

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitFlipMask_mid_right_self (x y m : Word256) :
      Word256.bitMaj x (Word256.bitFlipMask y m) (Word256.bitFlipMask y m) =
        Word256.bitFlipMask y m :=
    bitMaj_idemp_right x (Word256.bitFlipMask y m)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitFlipMask_mid_right_self (x y m : Word256) :
      Word256.bitParity x (Word256.bitFlipMask y m) (Word256.bitFlipMask y m) = x :=
    bitParity_self_right x (Word256.bitFlipMask y m)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitSetMask_left_right_self (x y m : Word256) :
      Word256.bitParity (Word256.bitSetMask x m) y (Word256.bitSetMask x m) = y :=
    bitParity_self_outer (Word256.bitSetMask x m) y

set_option maxHeartbeats 200000 in
  theorem bitParity_bitClearMask_left_right_self (x y m : Word256) :
      Word256.bitParity (Word256.bitClearMask x m) y (Word256.bitClearMask x m) = y :=
    bitParity_self_outer (Word256.bitClearMask x m) y

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitSetMask_left_right_self (x y m : Word256) :
      Word256.bitMaj (Word256.bitSetMask x m) y (Word256.bitSetMask x m) =
        Word256.bitSetMask x m :=
    bitMaj_idemp_outer (Word256.bitSetMask x m) y

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitClearMask_left_right_self (x y m : Word256) :
      Word256.bitMaj (Word256.bitClearMask x m) y (Word256.bitClearMask x m) =
        Word256.bitClearMask x m :=
    bitMaj_idemp_outer (Word256.bitClearMask x m) y

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitFlipMask_left_right_self (x y m : Word256) :
      Word256.bitMaj (Word256.bitFlipMask x m) y (Word256.bitFlipMask x m) =
        Word256.bitFlipMask x m :=
    bitMaj_idemp_outer (Word256.bitFlipMask x m) y

set_option maxHeartbeats 200000 in
  theorem bitParity_bitFlipMask_left_right_self (x y m : Word256) :
      Word256.bitParity (Word256.bitFlipMask x m) y (Word256.bitFlipMask x m) = y :=
    bitParity_self_outer (Word256.bitFlipMask x m) y

set_option maxHeartbeats 200000 in
  theorem bitParity_bitFlipMask_left_mid_self (x z m : Word256) :
      Word256.bitParity (Word256.bitFlipMask x m) (Word256.bitFlipMask x m) z = z :=
    bitParity_self_left (Word256.bitFlipMask x m) z

set_option maxHeartbeats 200000 in
  theorem bitParity_bitClearMask_left_mid_set_right (x y z m : Word256) :
      Word256.bitParity (Word256.bitClearMask x m) (Word256.bitClearMask y m) (Word256.bitSetMask z m) =
        Word256.bitSetMask (Word256.bitParity x y z) m :=
    let cx := Word256.bitClearMask x m
    let cy := Word256.bitClearMask y m
    let cz := Word256.bitClearMask z m
    (congrArg (Word256.bitParity cx cy) (bitFlipMask_clearMask_eq_setMask z m).symm).trans <|
      (bitParity_bitFlipMask_right cx cy cz m).trans <|
      (congrArg (Word256.bitFlipMask · m) (bitClearMask_bitParity_distrib x y z m).symm).trans
        (bitFlipMask_clearMask_eq_setMask (Word256.bitParity x y z) m)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitSetMask_left_clear_mid_set_right (x y z m : Word256) :
      Word256.bitParity (Word256.bitSetMask x m) (Word256.bitClearMask y m) (Word256.bitSetMask z m) =
        Word256.bitClearMask (Word256.bitParity x y z) m :=
    let cx := Word256.bitClearMask x m
    let cy := Word256.bitClearMask y m
    let cz := Word256.bitClearMask z m
    (congrArg (fun a => Word256.bitParity a cy (Word256.bitSetMask z m))
      (bitFlipMask_clearMask_eq_setMask x m).symm).trans <|
      (congrArg (Word256.bitParity (Word256.bitFlipMask cx m) cy)
        (bitFlipMask_clearMask_eq_setMask z m).symm).trans <|
      (bitParity_bitFlipMask_left_right_cancel cx cy cz m).trans
        (bitClearMask_bitParity_distrib x y z m).symm

set_option maxHeartbeats 200000 in
  theorem bitParity_bitClearMask_left_set_mid_clear_right (x y z m : Word256) :
      Word256.bitParity (Word256.bitClearMask x m) (Word256.bitSetMask y m) (Word256.bitClearMask z m) =
        Word256.bitSetMask (Word256.bitParity x y z) m :=
    let cx := Word256.bitClearMask x m
    let cy := Word256.bitClearMask y m
    let cz := Word256.bitClearMask z m
    (congrArg (fun b => Word256.bitParity cx b cz)
      (bitFlipMask_clearMask_eq_setMask y m).symm).trans <|
      (bitParity_bitFlipMask_mid cx cy cz m).trans <|
      (congrArg (Word256.bitFlipMask · m) (bitClearMask_bitParity_distrib x y z m).symm).trans
        (bitFlipMask_clearMask_eq_setMask (Word256.bitParity x y z) m)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitSetMask_left_clear_mid_clear_right (x y z m : Word256) :
      Word256.bitParity (Word256.bitSetMask x m) (Word256.bitClearMask y m) (Word256.bitClearMask z m) =
        Word256.bitSetMask (Word256.bitParity x y z) m :=
    let cx := Word256.bitClearMask x m
    let cy := Word256.bitClearMask y m
    let cz := Word256.bitClearMask z m
    (congrArg (fun a => Word256.bitParity a cy cz)
      (bitFlipMask_clearMask_eq_setMask x m).symm).trans <|
      (bitParity_bitFlipMask_left cx cy cz m).trans <|
      (congrArg (Word256.bitFlipMask · m) (bitClearMask_bitParity_distrib x y z m).symm).trans
        (bitFlipMask_clearMask_eq_setMask (Word256.bitParity x y z) m)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitClearMask_left_set_mid_set_right (x y z m : Word256) :
      Word256.bitParity (Word256.bitClearMask x m) (Word256.bitSetMask y m) (Word256.bitSetMask z m) =
        Word256.bitClearMask (Word256.bitParity x y z) m :=
    let cx := Word256.bitClearMask x m
    let cy := Word256.bitClearMask y m
    let cz := Word256.bitClearMask z m
    (congrArg (fun b => Word256.bitParity cx b (Word256.bitSetMask z m))
      (bitFlipMask_clearMask_eq_setMask y m).symm).trans <|
      (congrArg (Word256.bitParity cx (Word256.bitFlipMask cy m))
        (bitFlipMask_clearMask_eq_setMask z m).symm).trans <|
      (bitParity_bitFlipMask_mid_right_cancel cx cy cz m).trans
        (bitClearMask_bitParity_distrib x y z m).symm

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitFlipMask_left_not_mid (x z m : Word256) :
      Word256.bitMaj (Word256.bitFlipMask x m) (Word256.bitNot (Word256.bitFlipMask x m)) z = z :=
    bitMaj_bitNot_right (Word256.bitFlipMask x m) z

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitSetMask_left_not_mid (x z m : Word256) :
      Word256.bitMaj (Word256.bitSetMask x m) (Word256.bitNot (Word256.bitSetMask x m)) z = z :=
    bitMaj_bitNot_right (Word256.bitSetMask x m) z

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitClearMask_left_not_mid (x z m : Word256) :
      Word256.bitMaj (Word256.bitClearMask x m) (Word256.bitNot (Word256.bitClearMask x m)) z = z :=
    bitMaj_bitNot_right (Word256.bitClearMask x m) z

set_option maxHeartbeats 200000 in
  theorem bitParity_bitSetMask_left_not_mid (x z m : Word256) :
      Word256.bitParity (Word256.bitSetMask x m) (Word256.bitNot (Word256.bitSetMask x m)) z =
        Word256.bitNot z :=
    bitParity_bitNot_self_left (Word256.bitSetMask x m) z

set_option maxHeartbeats 200000 in
  theorem bitParity_bitClearMask_left_not_mid (x z m : Word256) :
      Word256.bitParity (Word256.bitClearMask x m) (Word256.bitNot (Word256.bitClearMask x m)) z =
        Word256.bitNot z :=
    bitParity_bitNot_self_left (Word256.bitClearMask x m) z

set_option maxHeartbeats 200000 in
  theorem bitParity_bitFlipMask_left_not_mid (x z m : Word256) :
      Word256.bitParity (Word256.bitFlipMask x m) (Word256.bitNot (Word256.bitFlipMask x m)) z =
        Word256.bitNot z :=
    bitParity_bitNot_self_left (Word256.bitFlipMask x m) z

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitSetMask_mid_not_right (x y m : Word256) :
      Word256.bitMaj x (Word256.bitSetMask y m) (Word256.bitNot (Word256.bitSetMask y m)) = x :=
    let b := Word256.bitSetMask y m
    let nb := Word256.bitNot b
    (congrArg (Word256.bitOr (Word256.bitAnd x b))
      ((congrArg (Word256.bitOr · (Word256.bitAnd x nb)) (bitAnd_bitNot_self b)).trans
        (bitOr_zero_left (Word256.bitAnd x nb)))).trans
      (bitMux_self b x)

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitClearMask_mid_not_right (x y m : Word256) :
      Word256.bitMaj x (Word256.bitClearMask y m) (Word256.bitNot (Word256.bitClearMask y m)) = x :=
    let b := Word256.bitClearMask y m
    let nb := Word256.bitNot b
    (congrArg (Word256.bitOr (Word256.bitAnd x b))
      ((congrArg (Word256.bitOr · (Word256.bitAnd x nb)) (bitAnd_bitNot_self b)).trans
        (bitOr_zero_left (Word256.bitAnd x nb)))).trans
      (bitMux_self b x)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitSetMask_mid_not_right (x y m : Word256) :
      Word256.bitParity x (Word256.bitSetMask y m) (Word256.bitNot (Word256.bitSetMask y m)) =
        Word256.bitNot x :=
    let b := Word256.bitSetMask y m
    (bitXor_assoc x b (Word256.bitNot b)).trans <|
      (congrArg (Word256.bitXor x) (bitXor_bitNot_self b)).trans
        (bitXor_max_right x)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitClearMask_mid_not_right (x y m : Word256) :
      Word256.bitParity x (Word256.bitClearMask y m) (Word256.bitNot (Word256.bitClearMask y m)) =
        Word256.bitNot x :=
    let b := Word256.bitClearMask y m
    (bitXor_assoc x b (Word256.bitNot b)).trans <|
      (congrArg (Word256.bitXor x) (bitXor_bitNot_self b)).trans
        (bitXor_max_right x)

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitFlipMask_mid_not_right (x y m : Word256) :
      Word256.bitMaj x (Word256.bitFlipMask y m) (Word256.bitNot (Word256.bitFlipMask y m)) = x :=
    let b := Word256.bitFlipMask y m
    let nb := Word256.bitNot b
    (congrArg (Word256.bitOr (Word256.bitAnd x b))
      ((congrArg (Word256.bitOr · (Word256.bitAnd x nb)) (bitAnd_bitNot_self b)).trans
        (bitOr_zero_left (Word256.bitAnd x nb)))).trans
      (bitMux_self b x)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitFlipMask_mid_not_right (x y m : Word256) :
      Word256.bitParity x (Word256.bitFlipMask y m) (Word256.bitNot (Word256.bitFlipMask y m)) =
        Word256.bitNot x :=
    let b := Word256.bitFlipMask y m
    (bitXor_assoc x b (Word256.bitNot b)).trans <|
      (congrArg (Word256.bitXor x) (bitXor_bitNot_self b)).trans
        (bitXor_max_right x)

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitSetMask_left_not_right (x y m : Word256) :
      Word256.bitMaj (Word256.bitSetMask x m) y (Word256.bitNot (Word256.bitSetMask x m)) = y :=
    (bitMaj_comm_left (Word256.bitSetMask x m) y (Word256.bitNot (Word256.bitSetMask x m))).trans
      (bitMaj_bitSetMask_mid_not_right y x m)

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitClearMask_left_not_right (x y m : Word256) :
      Word256.bitMaj (Word256.bitClearMask x m) y (Word256.bitNot (Word256.bitClearMask x m)) = y :=
    (bitMaj_comm_left (Word256.bitClearMask x m) y (Word256.bitNot (Word256.bitClearMask x m))).trans
      (bitMaj_bitClearMask_mid_not_right y x m)

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitFlipMask_left_not_right (x y m : Word256) :
      Word256.bitMaj (Word256.bitFlipMask x m) y (Word256.bitNot (Word256.bitFlipMask x m)) = y :=
    (bitMaj_comm_left (Word256.bitFlipMask x m) y (Word256.bitNot (Word256.bitFlipMask x m))).trans
      (bitMaj_bitFlipMask_mid_not_right y x m)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitSetMask_left_not_right (x y m : Word256) :
      Word256.bitParity (Word256.bitSetMask x m) y (Word256.bitNot (Word256.bitSetMask x m)) =
        Word256.bitNot y :=
    (bitParity_comm_left (Word256.bitSetMask x m) y (Word256.bitNot (Word256.bitSetMask x m))).trans
      (bitParity_bitSetMask_mid_not_right y x m)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitClearMask_left_not_right (x y m : Word256) :
      Word256.bitParity (Word256.bitClearMask x m) y (Word256.bitNot (Word256.bitClearMask x m)) =
        Word256.bitNot y :=
    (bitParity_comm_left (Word256.bitClearMask x m) y (Word256.bitNot (Word256.bitClearMask x m))).trans
      (bitParity_bitClearMask_mid_not_right y x m)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitFlipMask_left_not_right (x y m : Word256) :
      Word256.bitParity (Word256.bitFlipMask x m) y (Word256.bitNot (Word256.bitFlipMask x m)) =
        Word256.bitNot y :=
    (bitParity_comm_left (Word256.bitFlipMask x m) y (Word256.bitNot (Word256.bitFlipMask x m))).trans
      (bitParity_bitFlipMask_mid_not_right y x m)

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitSetMask_not_left_not_mid (x z m : Word256) :
      Word256.bitMaj (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask x m)) z =
        Word256.bitNot (Word256.bitSetMask x m) :=
    bitMaj_bitNot_pair_left_mid_self (Word256.bitSetMask x m) z

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitClearMask_not_left_not_mid (x z m : Word256) :
      Word256.bitMaj (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask x m)) z =
        Word256.bitNot (Word256.bitClearMask x m) :=
    bitMaj_bitNot_pair_left_mid_self (Word256.bitClearMask x m) z

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitFlipMask_not_left_not_mid (x z m : Word256) :
      Word256.bitMaj (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask x m)) z =
        Word256.bitNot (Word256.bitFlipMask x m) :=
    bitMaj_bitNot_pair_left_mid_self (Word256.bitFlipMask x m) z

set_option maxHeartbeats 200000 in
  theorem bitParity_bitSetMask_not_left_not_mid (x z m : Word256) :
      Word256.bitParity (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask x m)) z = z :=
    bitParity_bitNot_pair_left_mid_self (Word256.bitSetMask x m) z

set_option maxHeartbeats 200000 in
  theorem bitParity_bitClearMask_not_left_not_mid (x z m : Word256) :
      Word256.bitParity (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask x m)) z = z :=
    bitParity_bitNot_pair_left_mid_self (Word256.bitClearMask x m) z

set_option maxHeartbeats 200000 in
  theorem bitParity_bitFlipMask_not_left_not_mid (x z m : Word256) :
      Word256.bitParity (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask x m)) z = z :=
    bitParity_bitNot_pair_left_mid_self (Word256.bitFlipMask x m) z

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitSetMask_not_mid_not_right (x y m : Word256) :
      Word256.bitMaj x (Word256.bitNot (Word256.bitSetMask y m)) (Word256.bitNot (Word256.bitSetMask y m)) =
        Word256.bitNot (Word256.bitSetMask y m) :=
    bitMaj_bitNot_pair_mid_right_self x (Word256.bitSetMask y m)

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitClearMask_not_mid_not_right (x y m : Word256) :
      Word256.bitMaj x (Word256.bitNot (Word256.bitClearMask y m)) (Word256.bitNot (Word256.bitClearMask y m)) =
        Word256.bitNot (Word256.bitClearMask y m) :=
    bitMaj_bitNot_pair_mid_right_self x (Word256.bitClearMask y m)

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitFlipMask_not_mid_not_right (x y m : Word256) :
      Word256.bitMaj x (Word256.bitNot (Word256.bitFlipMask y m)) (Word256.bitNot (Word256.bitFlipMask y m)) =
        Word256.bitNot (Word256.bitFlipMask y m) :=
    bitMaj_bitNot_pair_mid_right_self x (Word256.bitFlipMask y m)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitSetMask_not_mid_not_right (x y m : Word256) :
      Word256.bitParity x (Word256.bitNot (Word256.bitSetMask y m)) (Word256.bitNot (Word256.bitSetMask y m)) = x :=
    bitParity_bitNot_pair_mid_right_self x (Word256.bitSetMask y m)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitClearMask_not_mid_not_right (x y m : Word256) :
      Word256.bitParity x (Word256.bitNot (Word256.bitClearMask y m)) (Word256.bitNot (Word256.bitClearMask y m)) = x :=
    bitParity_bitNot_pair_mid_right_self x (Word256.bitClearMask y m)

set_option maxHeartbeats 200000 in
  theorem bitParity_bitFlipMask_not_mid_not_right (x y m : Word256) :
      Word256.bitParity x (Word256.bitNot (Word256.bitFlipMask y m)) (Word256.bitNot (Word256.bitFlipMask y m)) = x :=
    bitParity_bitNot_pair_mid_right_self x (Word256.bitFlipMask y m)

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitSetMask_not_left_not_right (x y m : Word256) :
      Word256.bitMaj (Word256.bitNot (Word256.bitSetMask x m)) y (Word256.bitNot (Word256.bitSetMask x m)) =
        Word256.bitNot (Word256.bitSetMask x m) :=
    bitMaj_bitNot_pair_left_right_self (Word256.bitSetMask x m) y

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitClearMask_not_left_not_right (x y m : Word256) :
      Word256.bitMaj (Word256.bitNot (Word256.bitClearMask x m)) y (Word256.bitNot (Word256.bitClearMask x m)) =
        Word256.bitNot (Word256.bitClearMask x m) :=
    bitMaj_bitNot_pair_left_right_self (Word256.bitClearMask x m) y

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitFlipMask_not_left_not_right (x y m : Word256) :
      Word256.bitMaj (Word256.bitNot (Word256.bitFlipMask x m)) y (Word256.bitNot (Word256.bitFlipMask x m)) =
        Word256.bitNot (Word256.bitFlipMask x m) :=
    bitMaj_bitNot_pair_left_right_self (Word256.bitFlipMask x m) y

set_option maxHeartbeats 200000 in
  theorem bitParity_bitSetMask_not_left_not_right (x y m : Word256) :
      Word256.bitParity (Word256.bitNot (Word256.bitSetMask x m)) y (Word256.bitNot (Word256.bitSetMask x m)) = y :=
    bitParity_bitNot_pair_left_right_self (Word256.bitSetMask x m) y

set_option maxHeartbeats 200000 in
  theorem bitParity_bitClearMask_not_left_not_right (x y m : Word256) :
      Word256.bitParity (Word256.bitNot (Word256.bitClearMask x m)) y (Word256.bitNot (Word256.bitClearMask x m)) = y :=
    bitParity_bitNot_pair_left_right_self (Word256.bitClearMask x m) y

set_option maxHeartbeats 200000 in
  theorem bitParity_bitFlipMask_not_left_not_right (x y m : Word256) :
      Word256.bitParity (Word256.bitNot (Word256.bitFlipMask x m)) y (Word256.bitNot (Word256.bitFlipMask x m)) = y :=
    bitParity_bitNot_pair_left_right_self (Word256.bitFlipMask x m) y

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitSetMask_not_left_not_mid_not_right (x m : Word256) :
      Word256.bitMaj (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask x m)) =
        Word256.bitNot (Word256.bitSetMask x m) :=
    bitMaj_all_same (Word256.bitNot (Word256.bitSetMask x m))

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitClearMask_not_left_not_mid_not_right (x m : Word256) :
      Word256.bitMaj (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask x m)) =
        Word256.bitNot (Word256.bitClearMask x m) :=
    bitMaj_all_same (Word256.bitNot (Word256.bitClearMask x m))

set_option maxHeartbeats 200000 in
  theorem bitMaj_bitFlipMask_not_left_not_mid_not_right (x m : Word256) :
      Word256.bitMaj (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask x m)) =
        Word256.bitNot (Word256.bitFlipMask x m) :=
    bitMaj_all_same (Word256.bitNot (Word256.bitFlipMask x m))

set_option maxHeartbeats 200000 in
  theorem bitParity_bitSetMask_not_left_not_mid_not_right (x m : Word256) :
      Word256.bitParity (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask x m)) =
        Word256.bitNot (Word256.bitSetMask x m) :=
    bitParity_all_same (Word256.bitNot (Word256.bitSetMask x m))

set_option maxHeartbeats 200000 in
  theorem bitParity_bitClearMask_not_left_not_mid_not_right (x m : Word256) :
      Word256.bitParity (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask x m)) =
        Word256.bitNot (Word256.bitClearMask x m) :=
    bitParity_all_same (Word256.bitNot (Word256.bitClearMask x m))

set_option maxHeartbeats 200000 in
  theorem bitParity_bitFlipMask_not_left_not_mid_not_right (x m : Word256) :
      Word256.bitParity (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask x m)) =
        Word256.bitNot (Word256.bitFlipMask x m) :=
    bitParity_all_same (Word256.bitNot (Word256.bitFlipMask x m))

set_option maxHeartbeats 200000 in
  theorem bitMux_bitSetMask_not_then_branch (x m b : Word256) :
      Word256.bitMux (Word256.bitSetMask x m) (Word256.bitNot (Word256.bitSetMask x m)) b =
        Word256.bitClearMask b (Word256.bitSetMask x m) :=
    bitMux_bitNot_mask_left (Word256.bitSetMask x m) b

set_option maxHeartbeats 200000 in
  theorem bitMux_bitClearMask_not_then_branch (x m b : Word256) :
      Word256.bitMux (Word256.bitClearMask x m) (Word256.bitNot (Word256.bitClearMask x m)) b =
        Word256.bitClearMask b (Word256.bitClearMask x m) :=
    bitMux_bitNot_mask_left (Word256.bitClearMask x m) b

set_option maxHeartbeats 200000 in
  theorem bitMux_bitFlipMask_not_then_branch (x m b : Word256) :
      Word256.bitMux (Word256.bitFlipMask x m) (Word256.bitNot (Word256.bitFlipMask x m)) b =
        Word256.bitClearMask b (Word256.bitFlipMask x m) :=
    bitMux_bitNot_mask_left (Word256.bitFlipMask x m) b

set_option maxHeartbeats 200000 in
  theorem bitMux_bitSetMask_not_else_branch (x m a : Word256) :
      Word256.bitMux (Word256.bitSetMask x m) a (Word256.bitNot (Word256.bitSetMask x m)) =
        Word256.bitSetMask a (Word256.bitNot (Word256.bitSetMask x m)) :=
    bitMux_bitNot_mask_right (Word256.bitSetMask x m) a

set_option maxHeartbeats 200000 in
  theorem bitMux_bitClearMask_not_else_branch (x m a : Word256) :
      Word256.bitMux (Word256.bitClearMask x m) a (Word256.bitNot (Word256.bitClearMask x m)) =
        Word256.bitSetMask a (Word256.bitNot (Word256.bitClearMask x m)) :=
    bitMux_bitNot_mask_right (Word256.bitClearMask x m) a

set_option maxHeartbeats 200000 in
  theorem bitMux_bitFlipMask_not_else_branch (x m a : Word256) :
      Word256.bitMux (Word256.bitFlipMask x m) a (Word256.bitNot (Word256.bitFlipMask x m)) =
        Word256.bitSetMask a (Word256.bitNot (Word256.bitFlipMask x m)) :=
    bitMux_bitNot_mask_right (Word256.bitFlipMask x m) a

set_option maxHeartbeats 200000 in
  theorem bitMux_bitSetMask_not_both_branches (m x : Word256) :
      Word256.bitMux m (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask x m)) =
        Word256.bitNot (Word256.bitSetMask x m) :=
    bitMux_self m (Word256.bitNot (Word256.bitSetMask x m))

set_option maxHeartbeats 200000 in
  theorem bitMux_bitClearMask_not_both_branches (m x : Word256) :
      Word256.bitMux m (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask x m)) =
        Word256.bitNot (Word256.bitClearMask x m) :=
    bitMux_self m (Word256.bitNot (Word256.bitClearMask x m))

set_option maxHeartbeats 200000 in
  theorem bitMux_bitFlipMask_not_both_branches (m x : Word256) :
      Word256.bitMux m (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask x m)) =
        Word256.bitNot (Word256.bitFlipMask x m) :=
    bitMux_self m (Word256.bitNot (Word256.bitFlipMask x m))

set_option maxHeartbeats 200000 in
  theorem bitMux_bitSetMask_not_cond (x m a b : Word256) :
      Word256.bitMux (Word256.bitNot (Word256.bitSetMask x m)) a b =
        Word256.bitMux (Word256.bitSetMask x m) b a :=
    bitMux_bitNot_mask (Word256.bitSetMask x m) a b

set_option maxHeartbeats 200000 in
  theorem bitMux_bitClearMask_not_cond (x m a b : Word256) :
      Word256.bitMux (Word256.bitNot (Word256.bitClearMask x m)) a b =
        Word256.bitMux (Word256.bitClearMask x m) b a :=
    bitMux_bitNot_mask (Word256.bitClearMask x m) a b

set_option maxHeartbeats 200000 in
  theorem bitMux_bitFlipMask_not_cond (x m a b : Word256) :
      Word256.bitMux (Word256.bitNot (Word256.bitFlipMask x m)) a b =
        Word256.bitMux (Word256.bitFlipMask x m) b a :=
    bitMux_bitNot_mask (Word256.bitFlipMask x m) a b

set_option maxHeartbeats 200000 in
  theorem bitMux_bitSetMask_not_cond_not_then (x m b : Word256) :
      Word256.bitMux (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask x m)) b =
        Word256.bitSetMask (Word256.bitNot (Word256.bitSetMask x m)) b :=
    bitMux_mask_left (Word256.bitNot (Word256.bitSetMask x m)) b

set_option maxHeartbeats 200000 in
  theorem bitMux_bitClearMask_not_cond_not_then (x m b : Word256) :
      Word256.bitMux (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask x m)) b =
        Word256.bitSetMask (Word256.bitNot (Word256.bitClearMask x m)) b :=
    bitMux_mask_left (Word256.bitNot (Word256.bitClearMask x m)) b

set_option maxHeartbeats 200000 in
  theorem bitMux_bitFlipMask_not_cond_not_then (x m b : Word256) :
      Word256.bitMux (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask x m)) b =
        Word256.bitSetMask (Word256.bitNot (Word256.bitFlipMask x m)) b :=
    bitMux_mask_left (Word256.bitNot (Word256.bitFlipMask x m)) b

set_option maxHeartbeats 200000 in
  theorem bitMux_bitSetMask_not_cond_not_else (x m a : Word256) :
      Word256.bitMux (Word256.bitNot (Word256.bitSetMask x m)) a (Word256.bitNot (Word256.bitSetMask x m)) =
        Word256.bitClearMask a (Word256.bitSetMask x m) :=
    bitMux_mask_right (Word256.bitNot (Word256.bitSetMask x m)) a

set_option maxHeartbeats 200000 in
  theorem bitMux_bitClearMask_not_cond_not_else (x m a : Word256) :
      Word256.bitMux (Word256.bitNot (Word256.bitClearMask x m)) a (Word256.bitNot (Word256.bitClearMask x m)) =
        Word256.bitClearMask a (Word256.bitClearMask x m) :=
    bitMux_mask_right (Word256.bitNot (Word256.bitClearMask x m)) a

set_option maxHeartbeats 200000 in
  theorem bitMux_bitFlipMask_not_cond_not_else (x m a : Word256) :
      Word256.bitMux (Word256.bitNot (Word256.bitFlipMask x m)) a (Word256.bitNot (Word256.bitFlipMask x m)) =
        Word256.bitClearMask a (Word256.bitFlipMask x m) :=
    bitMux_mask_right (Word256.bitNot (Word256.bitFlipMask x m)) a

set_option maxHeartbeats 200000 in
  theorem bitMux_bitSetMask_not_cond_not_both (x m : Word256) :
      Word256.bitMux (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask x m)) =
        Word256.bitNot (Word256.bitSetMask x m) :=
    bitMux_self (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask x m))

set_option maxHeartbeats 200000 in
  theorem bitMux_bitClearMask_not_cond_not_both (x m : Word256) :
      Word256.bitMux (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask x m)) =
        Word256.bitNot (Word256.bitClearMask x m) :=
    bitMux_self (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask x m))

set_option maxHeartbeats 200000 in
  theorem bitMux_bitFlipMask_not_cond_not_both (x m : Word256) :
      Word256.bitMux (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask x m)) =
        Word256.bitNot (Word256.bitFlipMask x m) :=
    bitMux_self (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask x m))

set_option maxHeartbeats 200000 in
  theorem bitAnd_bitSetMask_not_left_not_right (x m : Word256) :
      Word256.bitAnd (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask x m)) =
        Word256.bitNot (Word256.bitSetMask x m) :=
    bitAnd_self (Word256.bitNot (Word256.bitSetMask x m))

set_option maxHeartbeats 200000 in
  theorem bitAnd_bitClearMask_not_left_not_right (x m : Word256) :
      Word256.bitAnd (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask x m)) =
        Word256.bitNot (Word256.bitClearMask x m) :=
    bitAnd_self (Word256.bitNot (Word256.bitClearMask x m))

set_option maxHeartbeats 200000 in
  theorem bitAnd_bitFlipMask_not_left_not_right (x m : Word256) :
      Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask x m)) =
        Word256.bitNot (Word256.bitFlipMask x m) :=
    bitAnd_self (Word256.bitNot (Word256.bitFlipMask x m))

set_option maxHeartbeats 200000 in
  theorem bitOr_bitSetMask_not_left_not_right (x m : Word256) :
      Word256.bitOr (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask x m)) =
        Word256.bitNot (Word256.bitSetMask x m) :=
    bitOr_self (Word256.bitNot (Word256.bitSetMask x m))

set_option maxHeartbeats 200000 in
  theorem bitOr_bitClearMask_not_left_not_right (x m : Word256) :
      Word256.bitOr (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask x m)) =
        Word256.bitNot (Word256.bitClearMask x m) :=
    bitOr_self (Word256.bitNot (Word256.bitClearMask x m))

set_option maxHeartbeats 200000 in
  theorem bitOr_bitFlipMask_not_left_not_right (x m : Word256) :
      Word256.bitOr (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask x m)) =
        Word256.bitNot (Word256.bitFlipMask x m) :=
    bitOr_self (Word256.bitNot (Word256.bitFlipMask x m))

set_option maxHeartbeats 200000 in
  theorem bitXor_bitSetMask_not_left_not_right (x m : Word256) :
      Word256.bitXor (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask x m)) =
        Word256.zero :=
    bitXor_self_zero (Word256.bitNot (Word256.bitSetMask x m))

set_option maxHeartbeats 200000 in
  theorem bitXor_bitClearMask_not_left_not_right (x m : Word256) :
      Word256.bitXor (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask x m)) =
        Word256.zero :=
    bitXor_self_zero (Word256.bitNot (Word256.bitClearMask x m))

set_option maxHeartbeats 200000 in
  theorem bitXor_bitFlipMask_not_left_not_right (x m : Word256) :
      Word256.bitXor (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask x m)) =
        Word256.zero :=
    bitXor_self_zero (Word256.bitNot (Word256.bitFlipMask x m))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitAnd_bitSetMask_de_morgan (x y m : Word256) :
      Word256.bitNot (Word256.bitAnd (Word256.bitSetMask x m) (Word256.bitSetMask y m)) =
        Word256.bitOr (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m)) :=
    bitNot_bitAnd (Word256.bitSetMask x m) (Word256.bitSetMask y m)

set_option maxHeartbeats 200000 in
  theorem bitNot_bitOr_bitSetMask_de_morgan (x y m : Word256) :
      Word256.bitNot (Word256.bitOr (Word256.bitSetMask x m) (Word256.bitSetMask y m)) =
        Word256.bitAnd (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m)) :=
    bitNot_bitOr (Word256.bitSetMask x m) (Word256.bitSetMask y m)

set_option maxHeartbeats 200000 in
  theorem bitNot_bitAnd_bitClearMask_de_morgan (x y m : Word256) :
      Word256.bitNot (Word256.bitAnd (Word256.bitClearMask x m) (Word256.bitClearMask y m)) =
        Word256.bitOr (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m)) :=
    bitNot_bitAnd (Word256.bitClearMask x m) (Word256.bitClearMask y m)

set_option maxHeartbeats 200000 in
  theorem bitNot_bitOr_bitClearMask_de_morgan (x y m : Word256) :
      Word256.bitNot (Word256.bitOr (Word256.bitClearMask x m) (Word256.bitClearMask y m)) =
        Word256.bitAnd (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m)) :=
    bitNot_bitOr (Word256.bitClearMask x m) (Word256.bitClearMask y m)

set_option maxHeartbeats 200000 in
  theorem bitNot_bitAnd_bitFlipMask_de_morgan (x y m : Word256) :
      Word256.bitNot (Word256.bitAnd (Word256.bitFlipMask x m) (Word256.bitFlipMask y m)) =
        Word256.bitOr (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m)) :=
    bitNot_bitAnd (Word256.bitFlipMask x m) (Word256.bitFlipMask y m)

set_option maxHeartbeats 200000 in
  theorem bitNot_bitOr_bitFlipMask_de_morgan (x y m : Word256) :
      Word256.bitNot (Word256.bitOr (Word256.bitFlipMask x m) (Word256.bitFlipMask y m)) =
        Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m)) :=
    bitNot_bitOr (Word256.bitFlipMask x m) (Word256.bitFlipMask y m)

set_option maxHeartbeats 200000 in
  theorem bitNot_bitXor_bitSetMask_left (x y m : Word256) :
      Word256.bitNot (Word256.bitXor (Word256.bitSetMask x m) (Word256.bitSetMask y m)) =
        Word256.bitXor (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitSetMask y m) :=
    (bitXor_max_left (Word256.bitXor (Word256.bitSetMask x m) (Word256.bitSetMask y m))).symm.trans <|
      (bitXor_assoc Word256.max (Word256.bitSetMask x m) (Word256.bitSetMask y m)).symm.trans
        (congrArg (Word256.bitXor · (Word256.bitSetMask y m)) (bitXor_max_left (Word256.bitSetMask x m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitXor_bitClearMask_left (x y m : Word256) :
      Word256.bitNot (Word256.bitXor (Word256.bitClearMask x m) (Word256.bitClearMask y m)) =
        Word256.bitXor (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitClearMask y m) :=
    (bitXor_max_left (Word256.bitXor (Word256.bitClearMask x m) (Word256.bitClearMask y m))).symm.trans <|
      (bitXor_assoc Word256.max (Word256.bitClearMask x m) (Word256.bitClearMask y m)).symm.trans
        (congrArg (Word256.bitXor · (Word256.bitClearMask y m)) (bitXor_max_left (Word256.bitClearMask x m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitXor_bitFlipMask_left (x y m : Word256) :
      Word256.bitNot (Word256.bitXor (Word256.bitFlipMask x m) (Word256.bitFlipMask y m)) =
        Word256.bitXor (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitFlipMask y m) :=
    (bitXor_max_left (Word256.bitXor (Word256.bitFlipMask x m) (Word256.bitFlipMask y m))).symm.trans <|
      (bitXor_assoc Word256.max (Word256.bitFlipMask x m) (Word256.bitFlipMask y m)).symm.trans
        (congrArg (Word256.bitXor · (Word256.bitFlipMask y m)) (bitXor_max_left (Word256.bitFlipMask x m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitXor_bitSetMask_right (x y m : Word256) :
      Word256.bitNot (Word256.bitXor (Word256.bitSetMask x m) (Word256.bitSetMask y m)) =
        Word256.bitXor (Word256.bitSetMask x m) (Word256.bitNot (Word256.bitSetMask y m)) :=
    (bitXor_max_right (Word256.bitXor (Word256.bitSetMask x m) (Word256.bitSetMask y m))).symm.trans <|
      (bitXor_assoc (Word256.bitSetMask x m) (Word256.bitSetMask y m) Word256.max).trans
        (congrArg (Word256.bitXor (Word256.bitSetMask x m)) (bitXor_max_right (Word256.bitSetMask y m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitXor_bitClearMask_right (x y m : Word256) :
      Word256.bitNot (Word256.bitXor (Word256.bitClearMask x m) (Word256.bitClearMask y m)) =
        Word256.bitXor (Word256.bitClearMask x m) (Word256.bitNot (Word256.bitClearMask y m)) :=
    (bitXor_max_right (Word256.bitXor (Word256.bitClearMask x m) (Word256.bitClearMask y m))).symm.trans <|
      (bitXor_assoc (Word256.bitClearMask x m) (Word256.bitClearMask y m) Word256.max).trans
        (congrArg (Word256.bitXor (Word256.bitClearMask x m)) (bitXor_max_right (Word256.bitClearMask y m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitXor_bitFlipMask_right (x y m : Word256) :
      Word256.bitNot (Word256.bitXor (Word256.bitFlipMask x m) (Word256.bitFlipMask y m)) =
        Word256.bitXor (Word256.bitFlipMask x m) (Word256.bitNot (Word256.bitFlipMask y m)) :=
    (bitXor_max_right (Word256.bitXor (Word256.bitFlipMask x m) (Word256.bitFlipMask y m))).symm.trans <|
      (bitXor_assoc (Word256.bitFlipMask x m) (Word256.bitFlipMask y m) Word256.max).trans
        (congrArg (Word256.bitXor (Word256.bitFlipMask x m)) (bitXor_max_right (Word256.bitFlipMask y m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitXor_bitSetMask_not_left_not_right (x y m : Word256) :
      Word256.bitNot (Word256.bitXor (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m))) =
        Word256.bitXor (Word256.bitSetMask x m) (Word256.bitNot (Word256.bitSetMask y m)) :=
    (bitXor_max_left (Word256.bitXor (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m)))).symm.trans <|
      (bitXor_assoc Word256.max (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m))).symm.trans <|
        congrArg (Word256.bitXor · (Word256.bitNot (Word256.bitSetMask y m)))
          ((bitXor_max_left (Word256.bitNot (Word256.bitSetMask x m))).trans (bitNot_bitNot (Word256.bitSetMask x m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitXor_bitClearMask_not_left_not_right (x y m : Word256) :
      Word256.bitNot (Word256.bitXor (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m))) =
        Word256.bitXor (Word256.bitClearMask x m) (Word256.bitNot (Word256.bitClearMask y m)) :=
    (bitXor_max_left (Word256.bitXor (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m)))).symm.trans <|
      (bitXor_assoc Word256.max (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m))).symm.trans <|
        congrArg (Word256.bitXor · (Word256.bitNot (Word256.bitClearMask y m)))
          ((bitXor_max_left (Word256.bitNot (Word256.bitClearMask x m))).trans (bitNot_bitNot (Word256.bitClearMask x m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitXor_bitFlipMask_not_left_not_right (x y m : Word256) :
      Word256.bitNot (Word256.bitXor (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m))) =
        Word256.bitXor (Word256.bitFlipMask x m) (Word256.bitNot (Word256.bitFlipMask y m)) :=
    (bitXor_max_left (Word256.bitXor (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m)))).symm.trans <|
      (bitXor_assoc Word256.max (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m))).symm.trans <|
        congrArg (Word256.bitXor · (Word256.bitNot (Word256.bitFlipMask y m)))
          ((bitXor_max_left (Word256.bitNot (Word256.bitFlipMask x m))).trans (bitNot_bitNot (Word256.bitFlipMask x m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitSetMask_eq_bitClearMask_not (x m : Word256) :
      Word256.bitNot (Word256.bitSetMask x m) = Word256.bitClearMask (Word256.bitNot x) m :=
    bitNot_bitOr x m

set_option maxHeartbeats 200000 in
  theorem bitNot_bitClearMask_eq_bitSetMask_not (x m : Word256) :
      Word256.bitNot (Word256.bitClearMask x m) = Word256.bitSetMask (Word256.bitNot x) m :=
    (bitNot_bitAnd x (Word256.bitNot m)).trans
      (congrArg (Word256.bitOr (Word256.bitNot x)) (bitNot_bitNot m))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitFlipMask_comm (x m : Word256) :
      Word256.bitNot (Word256.bitFlipMask x m) = Word256.bitFlipMask (Word256.bitNot x) m :=
    (bitXor_max_left (Word256.bitXor x m)).symm.trans <|
      (bitXor_assoc Word256.max x m).symm.trans
        (congrArg (Word256.bitXor · m) (bitXor_max_left x))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMaj_bitSetMask_de_morgan (x y z m : Word256) :
      Word256.bitNot (Word256.bitMaj (Word256.bitSetMask x m) (Word256.bitSetMask y m) (Word256.bitSetMask z m)) =
        Word256.bitAnd
          (Word256.bitNot (Word256.bitAnd (Word256.bitSetMask x m) (Word256.bitSetMask y m)))
          (Word256.bitAnd
            (Word256.bitNot (Word256.bitAnd (Word256.bitSetMask y m) (Word256.bitSetMask z m)))
            (Word256.bitNot (Word256.bitAnd (Word256.bitSetMask x m) (Word256.bitSetMask z m)))) :=
    (bitNot_bitOr
      (Word256.bitAnd (Word256.bitSetMask x m) (Word256.bitSetMask y m))
      (Word256.bitOr
        (Word256.bitAnd (Word256.bitSetMask y m) (Word256.bitSetMask z m))
        (Word256.bitAnd (Word256.bitSetMask x m) (Word256.bitSetMask z m)))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd (Word256.bitSetMask x m) (Word256.bitSetMask y m))))
        (bitNot_bitOr
          (Word256.bitAnd (Word256.bitSetMask y m) (Word256.bitSetMask z m))
          (Word256.bitAnd (Word256.bitSetMask x m) (Word256.bitSetMask z m))))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMaj_bitClearMask_de_morgan (x y z m : Word256) :
      Word256.bitNot (Word256.bitMaj (Word256.bitClearMask x m) (Word256.bitClearMask y m) (Word256.bitClearMask z m)) =
        Word256.bitAnd
          (Word256.bitNot (Word256.bitAnd (Word256.bitClearMask x m) (Word256.bitClearMask y m)))
          (Word256.bitAnd
            (Word256.bitNot (Word256.bitAnd (Word256.bitClearMask y m) (Word256.bitClearMask z m)))
            (Word256.bitNot (Word256.bitAnd (Word256.bitClearMask x m) (Word256.bitClearMask z m)))) :=
    (bitNot_bitOr
      (Word256.bitAnd (Word256.bitClearMask x m) (Word256.bitClearMask y m))
      (Word256.bitOr
        (Word256.bitAnd (Word256.bitClearMask y m) (Word256.bitClearMask z m))
        (Word256.bitAnd (Word256.bitClearMask x m) (Word256.bitClearMask z m)))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd (Word256.bitClearMask x m) (Word256.bitClearMask y m))))
        (bitNot_bitOr
          (Word256.bitAnd (Word256.bitClearMask y m) (Word256.bitClearMask z m))
          (Word256.bitAnd (Word256.bitClearMask x m) (Word256.bitClearMask z m))))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMaj_bitFlipMask_de_morgan (x y z m : Word256) :
      Word256.bitNot (Word256.bitMaj (Word256.bitFlipMask x m) (Word256.bitFlipMask y m) (Word256.bitFlipMask z m)) =
        Word256.bitAnd
          (Word256.bitNot (Word256.bitAnd (Word256.bitFlipMask x m) (Word256.bitFlipMask y m)))
          (Word256.bitAnd
            (Word256.bitNot (Word256.bitAnd (Word256.bitFlipMask y m) (Word256.bitFlipMask z m)))
            (Word256.bitNot (Word256.bitAnd (Word256.bitFlipMask x m) (Word256.bitFlipMask z m)))) :=
    (bitNot_bitOr
      (Word256.bitAnd (Word256.bitFlipMask x m) (Word256.bitFlipMask y m))
      (Word256.bitOr
        (Word256.bitAnd (Word256.bitFlipMask y m) (Word256.bitFlipMask z m))
        (Word256.bitAnd (Word256.bitFlipMask x m) (Word256.bitFlipMask z m)))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd (Word256.bitFlipMask x m) (Word256.bitFlipMask y m))))
        (bitNot_bitOr
          (Word256.bitAnd (Word256.bitFlipMask y m) (Word256.bitFlipMask z m))
          (Word256.bitAnd (Word256.bitFlipMask x m) (Word256.bitFlipMask z m))))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitParity_bitSetMask_left (x y z m : Word256) :
      Word256.bitNot (Word256.bitParity (Word256.bitSetMask x m) (Word256.bitSetMask y m) (Word256.bitSetMask z m)) =
        Word256.bitParity (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitSetMask y m) (Word256.bitSetMask z m) :=
    (bitXor_max_left (Word256.bitParity (Word256.bitSetMask x m) (Word256.bitSetMask y m) (Word256.bitSetMask z m))).symm.trans <|
      (bitXor_assoc Word256.max (Word256.bitXor (Word256.bitSetMask x m) (Word256.bitSetMask y m)) (Word256.bitSetMask z m)).symm.trans <|
        congrArg (Word256.bitXor · (Word256.bitSetMask z m))
          ((bitXor_assoc Word256.max (Word256.bitSetMask x m) (Word256.bitSetMask y m)).symm.trans
            (congrArg (Word256.bitXor · (Word256.bitSetMask y m)) (bitXor_max_left (Word256.bitSetMask x m))))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitParity_bitClearMask_left (x y z m : Word256) :
      Word256.bitNot (Word256.bitParity (Word256.bitClearMask x m) (Word256.bitClearMask y m) (Word256.bitClearMask z m)) =
        Word256.bitParity (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitClearMask y m) (Word256.bitClearMask z m) :=
    (bitXor_max_left (Word256.bitParity (Word256.bitClearMask x m) (Word256.bitClearMask y m) (Word256.bitClearMask z m))).symm.trans <|
      (bitXor_assoc Word256.max (Word256.bitXor (Word256.bitClearMask x m) (Word256.bitClearMask y m)) (Word256.bitClearMask z m)).symm.trans <|
        congrArg (Word256.bitXor · (Word256.bitClearMask z m))
          ((bitXor_assoc Word256.max (Word256.bitClearMask x m) (Word256.bitClearMask y m)).symm.trans
            (congrArg (Word256.bitXor · (Word256.bitClearMask y m)) (bitXor_max_left (Word256.bitClearMask x m))))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitParity_bitFlipMask_left (x y z m : Word256) :
      Word256.bitNot (Word256.bitParity (Word256.bitFlipMask x m) (Word256.bitFlipMask y m) (Word256.bitFlipMask z m)) =
        Word256.bitParity (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitFlipMask y m) (Word256.bitFlipMask z m) :=
    (bitXor_max_left (Word256.bitParity (Word256.bitFlipMask x m) (Word256.bitFlipMask y m) (Word256.bitFlipMask z m))).symm.trans <|
      (bitXor_assoc Word256.max (Word256.bitXor (Word256.bitFlipMask x m) (Word256.bitFlipMask y m)) (Word256.bitFlipMask z m)).symm.trans <|
        congrArg (Word256.bitXor · (Word256.bitFlipMask z m))
          ((bitXor_assoc Word256.max (Word256.bitFlipMask x m) (Word256.bitFlipMask y m)).symm.trans
            (congrArg (Word256.bitXor · (Word256.bitFlipMask y m)) (bitXor_max_left (Word256.bitFlipMask x m))))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitParity_bitSetMask_mid (x y z m : Word256) :
      Word256.bitNot (Word256.bitParity (Word256.bitSetMask x m) (Word256.bitSetMask y m) (Word256.bitSetMask z m)) =
        Word256.bitParity (Word256.bitSetMask x m) (Word256.bitNot (Word256.bitSetMask y m)) (Word256.bitSetMask z m) :=
    (bitXor_max_left (Word256.bitParity (Word256.bitSetMask x m) (Word256.bitSetMask y m) (Word256.bitSetMask z m))).symm.trans <|
      (bitXor_assoc Word256.max (Word256.bitXor (Word256.bitSetMask x m) (Word256.bitSetMask y m)) (Word256.bitSetMask z m)).symm.trans <|
        congrArg (Word256.bitXor · (Word256.bitSetMask z m))
          ((bitXor_max_left (Word256.bitXor (Word256.bitSetMask x m) (Word256.bitSetMask y m))).trans
            (bitNot_bitXor_bitSetMask_right x y m))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitParity_bitClearMask_mid (x y z m : Word256) :
      Word256.bitNot (Word256.bitParity (Word256.bitClearMask x m) (Word256.bitClearMask y m) (Word256.bitClearMask z m)) =
        Word256.bitParity (Word256.bitClearMask x m) (Word256.bitNot (Word256.bitClearMask y m)) (Word256.bitClearMask z m) :=
    (bitXor_max_left (Word256.bitParity (Word256.bitClearMask x m) (Word256.bitClearMask y m) (Word256.bitClearMask z m))).symm.trans <|
      (bitXor_assoc Word256.max (Word256.bitXor (Word256.bitClearMask x m) (Word256.bitClearMask y m)) (Word256.bitClearMask z m)).symm.trans <|
        congrArg (Word256.bitXor · (Word256.bitClearMask z m))
          ((bitXor_max_left (Word256.bitXor (Word256.bitClearMask x m) (Word256.bitClearMask y m))).trans
            (bitNot_bitXor_bitClearMask_right x y m))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitParity_bitFlipMask_mid (x y z m : Word256) :
      Word256.bitNot (Word256.bitParity (Word256.bitFlipMask x m) (Word256.bitFlipMask y m) (Word256.bitFlipMask z m)) =
        Word256.bitParity (Word256.bitFlipMask x m) (Word256.bitNot (Word256.bitFlipMask y m)) (Word256.bitFlipMask z m) :=
    (bitXor_max_left (Word256.bitParity (Word256.bitFlipMask x m) (Word256.bitFlipMask y m) (Word256.bitFlipMask z m))).symm.trans <|
      (bitXor_assoc Word256.max (Word256.bitXor (Word256.bitFlipMask x m) (Word256.bitFlipMask y m)) (Word256.bitFlipMask z m)).symm.trans <|
        congrArg (Word256.bitXor · (Word256.bitFlipMask z m))
          ((bitXor_max_left (Word256.bitXor (Word256.bitFlipMask x m) (Word256.bitFlipMask y m))).trans
            (bitNot_bitXor_bitFlipMask_right x y m))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitParity_bitSetMask_right (x y z m : Word256) :
      Word256.bitNot (Word256.bitParity (Word256.bitSetMask x m) (Word256.bitSetMask y m) (Word256.bitSetMask z m)) =
        Word256.bitParity (Word256.bitSetMask x m) (Word256.bitSetMask y m) (Word256.bitNot (Word256.bitSetMask z m)) :=
    (bitXor_max_right (Word256.bitParity (Word256.bitSetMask x m) (Word256.bitSetMask y m) (Word256.bitSetMask z m))).symm.trans <|
      (bitXor_assoc (Word256.bitXor (Word256.bitSetMask x m) (Word256.bitSetMask y m)) (Word256.bitSetMask z m) Word256.max).trans
        (congrArg (Word256.bitXor (Word256.bitXor (Word256.bitSetMask x m) (Word256.bitSetMask y m)))
          (bitXor_max_right (Word256.bitSetMask z m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitParity_bitClearMask_right (x y z m : Word256) :
      Word256.bitNot (Word256.bitParity (Word256.bitClearMask x m) (Word256.bitClearMask y m) (Word256.bitClearMask z m)) =
        Word256.bitParity (Word256.bitClearMask x m) (Word256.bitClearMask y m) (Word256.bitNot (Word256.bitClearMask z m)) :=
    (bitXor_max_right (Word256.bitParity (Word256.bitClearMask x m) (Word256.bitClearMask y m) (Word256.bitClearMask z m))).symm.trans <|
      (bitXor_assoc (Word256.bitXor (Word256.bitClearMask x m) (Word256.bitClearMask y m)) (Word256.bitClearMask z m) Word256.max).trans
        (congrArg (Word256.bitXor (Word256.bitXor (Word256.bitClearMask x m) (Word256.bitClearMask y m)))
          (bitXor_max_right (Word256.bitClearMask z m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitParity_bitFlipMask_right (x y z m : Word256) :
      Word256.bitNot (Word256.bitParity (Word256.bitFlipMask x m) (Word256.bitFlipMask y m) (Word256.bitFlipMask z m)) =
        Word256.bitParity (Word256.bitFlipMask x m) (Word256.bitFlipMask y m) (Word256.bitNot (Word256.bitFlipMask z m)) :=
    (bitXor_max_right (Word256.bitParity (Word256.bitFlipMask x m) (Word256.bitFlipMask y m) (Word256.bitFlipMask z m))).symm.trans <|
      (bitXor_assoc (Word256.bitXor (Word256.bitFlipMask x m) (Word256.bitFlipMask y m)) (Word256.bitFlipMask z m) Word256.max).trans
        (congrArg (Word256.bitXor (Word256.bitXor (Word256.bitFlipMask x m) (Word256.bitFlipMask y m)))
          (bitXor_max_right (Word256.bitFlipMask z m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitParity_bitSetMask_not_left_not_mid (x y z m : Word256) :
      Word256.bitNot (Word256.bitParity (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m)) (Word256.bitSetMask z m)) =
        Word256.bitParity (Word256.bitSetMask x m) (Word256.bitNot (Word256.bitSetMask y m)) (Word256.bitSetMask z m) :=
    (bitXor_max_left (Word256.bitParity (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m)) (Word256.bitSetMask z m))).symm.trans <|
      (bitXor_assoc Word256.max (Word256.bitXor (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m))) (Word256.bitSetMask z m)).symm.trans <|
        congrArg (Word256.bitXor · (Word256.bitSetMask z m))
          ((bitXor_max_left (Word256.bitXor (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m)))).trans
            (bitNot_bitXor_bitSetMask_not_left_not_right x y m))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitParity_bitClearMask_not_left_not_mid (x y z m : Word256) :
      Word256.bitNot (Word256.bitParity (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m)) (Word256.bitClearMask z m)) =
        Word256.bitParity (Word256.bitClearMask x m) (Word256.bitNot (Word256.bitClearMask y m)) (Word256.bitClearMask z m) :=
    (bitXor_max_left (Word256.bitParity (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m)) (Word256.bitClearMask z m))).symm.trans <|
      (bitXor_assoc Word256.max (Word256.bitXor (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m))) (Word256.bitClearMask z m)).symm.trans <|
        congrArg (Word256.bitXor · (Word256.bitClearMask z m))
          ((bitXor_max_left (Word256.bitXor (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m)))).trans
            (bitNot_bitXor_bitClearMask_not_left_not_right x y m))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitParity_bitFlipMask_not_left_not_mid (x y z m : Word256) :
      Word256.bitNot (Word256.bitParity (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m)) (Word256.bitFlipMask z m)) =
        Word256.bitParity (Word256.bitFlipMask x m) (Word256.bitNot (Word256.bitFlipMask y m)) (Word256.bitFlipMask z m) :=
    (bitXor_max_left (Word256.bitParity (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m)) (Word256.bitFlipMask z m))).symm.trans <|
      (bitXor_assoc Word256.max (Word256.bitXor (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m))) (Word256.bitFlipMask z m)).symm.trans <|
        congrArg (Word256.bitXor · (Word256.bitFlipMask z m))
          ((bitXor_max_left (Word256.bitXor (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m)))).trans
            (bitNot_bitXor_bitFlipMask_not_left_not_right x y m))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux_bitSetMask_then (mask x m b : Word256) :
      Word256.bitNot (Word256.bitMux mask (Word256.bitSetMask x m) b) =
        Word256.bitMux mask (Word256.bitClearMask (Word256.bitNot x) m) (Word256.bitNot b) :=
    (bitNot_bitMux mask (Word256.bitSetMask x m) b).trans
      (congrArg (fun a => Word256.bitMux mask a (Word256.bitNot b))
        (bitNot_bitSetMask_eq_bitClearMask_not x m))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux_bitClearMask_then (mask x m b : Word256) :
      Word256.bitNot (Word256.bitMux mask (Word256.bitClearMask x m) b) =
        Word256.bitMux mask (Word256.bitSetMask (Word256.bitNot x) m) (Word256.bitNot b) :=
    (bitNot_bitMux mask (Word256.bitClearMask x m) b).trans
      (congrArg (fun a => Word256.bitMux mask a (Word256.bitNot b))
        (bitNot_bitClearMask_eq_bitSetMask_not x m))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux_bitFlipMask_then (mask x m b : Word256) :
      Word256.bitNot (Word256.bitMux mask (Word256.bitFlipMask x m) b) =
        Word256.bitMux mask (Word256.bitFlipMask (Word256.bitNot x) m) (Word256.bitNot b) :=
    (bitNot_bitMux mask (Word256.bitFlipMask x m) b).trans
      (congrArg (fun a => Word256.bitMux mask a (Word256.bitNot b))
        (bitNot_bitFlipMask_comm x m))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux_bitSetMask_else (mask a x m : Word256) :
      Word256.bitNot (Word256.bitMux mask a (Word256.bitSetMask x m)) =
        Word256.bitMux mask (Word256.bitNot a) (Word256.bitClearMask (Word256.bitNot x) m) :=
    (bitNot_bitMux mask a (Word256.bitSetMask x m)).trans
      (congrArg (Word256.bitMux mask (Word256.bitNot a))
        (bitNot_bitSetMask_eq_bitClearMask_not x m))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux_bitClearMask_else (mask a x m : Word256) :
      Word256.bitNot (Word256.bitMux mask a (Word256.bitClearMask x m)) =
        Word256.bitMux mask (Word256.bitNot a) (Word256.bitSetMask (Word256.bitNot x) m) :=
    (bitNot_bitMux mask a (Word256.bitClearMask x m)).trans
      (congrArg (Word256.bitMux mask (Word256.bitNot a))
        (bitNot_bitClearMask_eq_bitSetMask_not x m))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux_bitFlipMask_else (mask a x m : Word256) :
      Word256.bitNot (Word256.bitMux mask a (Word256.bitFlipMask x m)) =
        Word256.bitMux mask (Word256.bitNot a) (Word256.bitFlipMask (Word256.bitNot x) m) :=
    (bitNot_bitMux mask a (Word256.bitFlipMask x m)).trans
      (congrArg (Word256.bitMux mask (Word256.bitNot a))
        (bitNot_bitFlipMask_comm x m))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux_bitSetMask_cond (x m a b : Word256) :
      Word256.bitNot (Word256.bitMux (Word256.bitSetMask x m) a b) =
        Word256.bitMux (Word256.bitSetMask x m) (Word256.bitNot a) (Word256.bitNot b) :=
    bitNot_bitMux (Word256.bitSetMask x m) a b

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux_bitClearMask_cond (x m a b : Word256) :
      Word256.bitNot (Word256.bitMux (Word256.bitClearMask x m) a b) =
        Word256.bitMux (Word256.bitClearMask x m) (Word256.bitNot a) (Word256.bitNot b) :=
    bitNot_bitMux (Word256.bitClearMask x m) a b

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux_bitFlipMask_cond (x m a b : Word256) :
      Word256.bitNot (Word256.bitMux (Word256.bitFlipMask x m) a b) =
        Word256.bitMux (Word256.bitFlipMask x m) (Word256.bitNot a) (Word256.bitNot b) :=
    bitNot_bitMux (Word256.bitFlipMask x m) a b

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux_not_cond_swap (mask a b : Word256) :
      Word256.bitNot (Word256.bitMux (Word256.bitNot mask) a b) =
        Word256.bitMux mask (Word256.bitNot b) (Word256.bitNot a) :=
    (bitNot_bitMux (Word256.bitNot mask) a b).trans
      (bitMux_bitNot_mask mask (Word256.bitNot a) (Word256.bitNot b))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMaj_bitSetMask_left (x m b c : Word256) :
      Word256.bitNot (Word256.bitMaj (Word256.bitSetMask x m) b c) =
        Word256.bitAnd
          (Word256.bitNot (Word256.bitAnd (Word256.bitSetMask x m) b))
          (Word256.bitAnd
            (Word256.bitNot (Word256.bitAnd b c))
            (Word256.bitNot (Word256.bitAnd (Word256.bitSetMask x m) c))) :=
    (bitNot_bitOr
      (Word256.bitAnd (Word256.bitSetMask x m) b)
      (Word256.bitOr
        (Word256.bitAnd b c)
        (Word256.bitAnd (Word256.bitSetMask x m) c))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd (Word256.bitSetMask x m) b)))
        (bitNot_bitOr
          (Word256.bitAnd b c)
          (Word256.bitAnd (Word256.bitSetMask x m) c)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMaj_bitClearMask_left (x m b c : Word256) :
      Word256.bitNot (Word256.bitMaj (Word256.bitClearMask x m) b c) =
        Word256.bitAnd
          (Word256.bitNot (Word256.bitAnd (Word256.bitClearMask x m) b))
          (Word256.bitAnd
            (Word256.bitNot (Word256.bitAnd b c))
            (Word256.bitNot (Word256.bitAnd (Word256.bitClearMask x m) c))) :=
    (bitNot_bitOr
      (Word256.bitAnd (Word256.bitClearMask x m) b)
      (Word256.bitOr
        (Word256.bitAnd b c)
        (Word256.bitAnd (Word256.bitClearMask x m) c))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd (Word256.bitClearMask x m) b)))
        (bitNot_bitOr
          (Word256.bitAnd b c)
          (Word256.bitAnd (Word256.bitClearMask x m) c)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMaj_bitFlipMask_left (x m b c : Word256) :
      Word256.bitNot (Word256.bitMaj (Word256.bitFlipMask x m) b c) =
        Word256.bitAnd
          (Word256.bitNot (Word256.bitAnd (Word256.bitFlipMask x m) b))
          (Word256.bitAnd
            (Word256.bitNot (Word256.bitAnd b c))
            (Word256.bitNot (Word256.bitAnd (Word256.bitFlipMask x m) c))) :=
    (bitNot_bitOr
      (Word256.bitAnd (Word256.bitFlipMask x m) b)
      (Word256.bitOr
        (Word256.bitAnd b c)
        (Word256.bitAnd (Word256.bitFlipMask x m) c))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd (Word256.bitFlipMask x m) b)))
        (bitNot_bitOr
          (Word256.bitAnd b c)
          (Word256.bitAnd (Word256.bitFlipMask x m) c)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMaj_bitSetMask_mid (a x m c : Word256) :
      Word256.bitNot (Word256.bitMaj a (Word256.bitSetMask x m) c) =
        Word256.bitAnd
          (Word256.bitNot (Word256.bitAnd a (Word256.bitSetMask x m)))
          (Word256.bitAnd
            (Word256.bitNot (Word256.bitAnd (Word256.bitSetMask x m) c))
            (Word256.bitNot (Word256.bitAnd a c))) :=
    (bitNot_bitOr
      (Word256.bitAnd a (Word256.bitSetMask x m))
      (Word256.bitOr
        (Word256.bitAnd (Word256.bitSetMask x m) c)
        (Word256.bitAnd a c))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd a (Word256.bitSetMask x m))))
        (bitNot_bitOr
          (Word256.bitAnd (Word256.bitSetMask x m) c)
          (Word256.bitAnd a c)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMaj_bitClearMask_mid (a x m c : Word256) :
      Word256.bitNot (Word256.bitMaj a (Word256.bitClearMask x m) c) =
        Word256.bitAnd
          (Word256.bitNot (Word256.bitAnd a (Word256.bitClearMask x m)))
          (Word256.bitAnd
            (Word256.bitNot (Word256.bitAnd (Word256.bitClearMask x m) c))
            (Word256.bitNot (Word256.bitAnd a c))) :=
    (bitNot_bitOr
      (Word256.bitAnd a (Word256.bitClearMask x m))
      (Word256.bitOr
        (Word256.bitAnd (Word256.bitClearMask x m) c)
        (Word256.bitAnd a c))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd a (Word256.bitClearMask x m))))
        (bitNot_bitOr
          (Word256.bitAnd (Word256.bitClearMask x m) c)
          (Word256.bitAnd a c)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMaj_bitFlipMask_mid (a x m c : Word256) :
      Word256.bitNot (Word256.bitMaj a (Word256.bitFlipMask x m) c) =
        Word256.bitAnd
          (Word256.bitNot (Word256.bitAnd a (Word256.bitFlipMask x m)))
          (Word256.bitAnd
            (Word256.bitNot (Word256.bitAnd (Word256.bitFlipMask x m) c))
            (Word256.bitNot (Word256.bitAnd a c))) :=
    (bitNot_bitOr
      (Word256.bitAnd a (Word256.bitFlipMask x m))
      (Word256.bitOr
        (Word256.bitAnd (Word256.bitFlipMask x m) c)
        (Word256.bitAnd a c))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd a (Word256.bitFlipMask x m))))
        (bitNot_bitOr
          (Word256.bitAnd (Word256.bitFlipMask x m) c)
          (Word256.bitAnd a c)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMaj_bitSetMask_right (a b x m : Word256) :
      Word256.bitNot (Word256.bitMaj a b (Word256.bitSetMask x m)) =
        Word256.bitAnd
          (Word256.bitNot (Word256.bitAnd a b))
          (Word256.bitAnd
            (Word256.bitNot (Word256.bitAnd b (Word256.bitSetMask x m)))
            (Word256.bitNot (Word256.bitAnd a (Word256.bitSetMask x m)))) :=
    (bitNot_bitOr
      (Word256.bitAnd a b)
      (Word256.bitOr
        (Word256.bitAnd b (Word256.bitSetMask x m))
        (Word256.bitAnd a (Word256.bitSetMask x m)))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd a b)))
        (bitNot_bitOr
          (Word256.bitAnd b (Word256.bitSetMask x m))
          (Word256.bitAnd a (Word256.bitSetMask x m))))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMaj_bitClearMask_right (a b x m : Word256) :
      Word256.bitNot (Word256.bitMaj a b (Word256.bitClearMask x m)) =
        Word256.bitAnd
          (Word256.bitNot (Word256.bitAnd a b))
          (Word256.bitAnd
            (Word256.bitNot (Word256.bitAnd b (Word256.bitClearMask x m)))
            (Word256.bitNot (Word256.bitAnd a (Word256.bitClearMask x m)))) :=
    (bitNot_bitOr
      (Word256.bitAnd a b)
      (Word256.bitOr
        (Word256.bitAnd b (Word256.bitClearMask x m))
        (Word256.bitAnd a (Word256.bitClearMask x m)))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd a b)))
        (bitNot_bitOr
          (Word256.bitAnd b (Word256.bitClearMask x m))
          (Word256.bitAnd a (Word256.bitClearMask x m))))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMaj_bitFlipMask_right (a b x m : Word256) :
      Word256.bitNot (Word256.bitMaj a b (Word256.bitFlipMask x m)) =
        Word256.bitAnd
          (Word256.bitNot (Word256.bitAnd a b))
          (Word256.bitAnd
            (Word256.bitNot (Word256.bitAnd b (Word256.bitFlipMask x m)))
            (Word256.bitNot (Word256.bitAnd a (Word256.bitFlipMask x m)))) :=
    (bitNot_bitOr
      (Word256.bitAnd a b)
      (Word256.bitOr
        (Word256.bitAnd b (Word256.bitFlipMask x m))
        (Word256.bitAnd a (Word256.bitFlipMask x m)))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd a b)))
        (bitNot_bitOr
          (Word256.bitAnd b (Word256.bitFlipMask x m))
          (Word256.bitAnd a (Word256.bitFlipMask x m))))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMaj_bitSetMask_not_left_not_mid (x y z m : Word256) :
      Word256.bitNot (Word256.bitMaj (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m)) (Word256.bitSetMask z m)) =
        Word256.bitAnd
          (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m))))
          (Word256.bitAnd
            (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask y m)) (Word256.bitSetMask z m)))
            (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitSetMask z m)))) :=
    (bitNot_bitOr
      (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m)))
      (Word256.bitOr
        (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask y m)) (Word256.bitSetMask z m))
        (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitSetMask z m)))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m)))))
        (bitNot_bitOr
          (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask y m)) (Word256.bitSetMask z m))
          (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitSetMask z m))))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMaj_bitClearMask_not_left_not_mid (x y z m : Word256) :
      Word256.bitNot (Word256.bitMaj (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m)) (Word256.bitClearMask z m)) =
        Word256.bitAnd
          (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m))))
          (Word256.bitAnd
            (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask y m)) (Word256.bitClearMask z m)))
            (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitClearMask z m)))) :=
    (bitNot_bitOr
      (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m)))
      (Word256.bitOr
        (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask y m)) (Word256.bitClearMask z m))
        (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitClearMask z m)))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m)))))
        (bitNot_bitOr
          (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask y m)) (Word256.bitClearMask z m))
          (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitClearMask z m))))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMaj_bitFlipMask_not_left_not_mid (x y z m : Word256) :
      Word256.bitNot (Word256.bitMaj (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m)) (Word256.bitFlipMask z m)) =
        Word256.bitAnd
          (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m))))
          (Word256.bitAnd
            (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask y m)) (Word256.bitFlipMask z m)))
            (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitFlipMask z m)))) :=
    (bitNot_bitOr
      (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m)))
      (Word256.bitOr
        (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask y m)) (Word256.bitFlipMask z m))
        (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitFlipMask z m)))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m)))))
        (bitNot_bitOr
          (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask y m)) (Word256.bitFlipMask z m))
          (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitFlipMask z m))))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMaj_bitSetMask_not_mid_not_right (x y z m : Word256) :
      Word256.bitNot (Word256.bitMaj (Word256.bitSetMask x m) (Word256.bitNot (Word256.bitSetMask y m)) (Word256.bitNot (Word256.bitSetMask z m))) =
        Word256.bitAnd
          (Word256.bitNot (Word256.bitAnd (Word256.bitSetMask x m) (Word256.bitNot (Word256.bitSetMask y m))))
          (Word256.bitAnd
            (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask y m)) (Word256.bitNot (Word256.bitSetMask z m))))
            (Word256.bitNot (Word256.bitAnd (Word256.bitSetMask x m) (Word256.bitNot (Word256.bitSetMask z m))))) :=
    (bitNot_bitOr
      (Word256.bitAnd (Word256.bitSetMask x m) (Word256.bitNot (Word256.bitSetMask y m)))
      (Word256.bitOr
        (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask y m)) (Word256.bitNot (Word256.bitSetMask z m)))
        (Word256.bitAnd (Word256.bitSetMask x m) (Word256.bitNot (Word256.bitSetMask z m))))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd (Word256.bitSetMask x m) (Word256.bitNot (Word256.bitSetMask y m)))))
        (bitNot_bitOr
          (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask y m)) (Word256.bitNot (Word256.bitSetMask z m)))
          (Word256.bitAnd (Word256.bitSetMask x m) (Word256.bitNot (Word256.bitSetMask z m)))))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMaj_bitClearMask_not_mid_not_right (x y z m : Word256) :
      Word256.bitNot (Word256.bitMaj (Word256.bitClearMask x m) (Word256.bitNot (Word256.bitClearMask y m)) (Word256.bitNot (Word256.bitClearMask z m))) =
        Word256.bitAnd
          (Word256.bitNot (Word256.bitAnd (Word256.bitClearMask x m) (Word256.bitNot (Word256.bitClearMask y m))))
          (Word256.bitAnd
            (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask y m)) (Word256.bitNot (Word256.bitClearMask z m))))
            (Word256.bitNot (Word256.bitAnd (Word256.bitClearMask x m) (Word256.bitNot (Word256.bitClearMask z m))))) :=
    (bitNot_bitOr
      (Word256.bitAnd (Word256.bitClearMask x m) (Word256.bitNot (Word256.bitClearMask y m)))
      (Word256.bitOr
        (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask y m)) (Word256.bitNot (Word256.bitClearMask z m)))
        (Word256.bitAnd (Word256.bitClearMask x m) (Word256.bitNot (Word256.bitClearMask z m))))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd (Word256.bitClearMask x m) (Word256.bitNot (Word256.bitClearMask y m)))))
        (bitNot_bitOr
          (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask y m)) (Word256.bitNot (Word256.bitClearMask z m)))
          (Word256.bitAnd (Word256.bitClearMask x m) (Word256.bitNot (Word256.bitClearMask z m)))))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMaj_bitFlipMask_not_mid_not_right (x y z m : Word256) :
      Word256.bitNot (Word256.bitMaj (Word256.bitFlipMask x m) (Word256.bitNot (Word256.bitFlipMask y m)) (Word256.bitNot (Word256.bitFlipMask z m))) =
        Word256.bitAnd
          (Word256.bitNot (Word256.bitAnd (Word256.bitFlipMask x m) (Word256.bitNot (Word256.bitFlipMask y m))))
          (Word256.bitAnd
            (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask y m)) (Word256.bitNot (Word256.bitFlipMask z m))))
            (Word256.bitNot (Word256.bitAnd (Word256.bitFlipMask x m) (Word256.bitNot (Word256.bitFlipMask z m))))) :=
    (bitNot_bitOr
      (Word256.bitAnd (Word256.bitFlipMask x m) (Word256.bitNot (Word256.bitFlipMask y m)))
      (Word256.bitOr
        (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask y m)) (Word256.bitNot (Word256.bitFlipMask z m)))
        (Word256.bitAnd (Word256.bitFlipMask x m) (Word256.bitNot (Word256.bitFlipMask z m))))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd (Word256.bitFlipMask x m) (Word256.bitNot (Word256.bitFlipMask y m)))))
        (bitNot_bitOr
          (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask y m)) (Word256.bitNot (Word256.bitFlipMask z m)))
          (Word256.bitAnd (Word256.bitFlipMask x m) (Word256.bitNot (Word256.bitFlipMask z m)))))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMaj_bitSetMask_not_left_not_right (x y z m : Word256) :
      Word256.bitNot (Word256.bitMaj (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitSetMask y m) (Word256.bitNot (Word256.bitSetMask z m))) =
        Word256.bitAnd
          (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitSetMask y m)))
          (Word256.bitAnd
            (Word256.bitNot (Word256.bitAnd (Word256.bitSetMask y m) (Word256.bitNot (Word256.bitSetMask z m))))
            (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask z m))))) :=
    (bitNot_bitOr
      (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitSetMask y m))
      (Word256.bitOr
        (Word256.bitAnd (Word256.bitSetMask y m) (Word256.bitNot (Word256.bitSetMask z m)))
        (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask z m))))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitSetMask y m))))
        (bitNot_bitOr
          (Word256.bitAnd (Word256.bitSetMask y m) (Word256.bitNot (Word256.bitSetMask z m)))
          (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask z m)))))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMaj_bitClearMask_not_left_not_right (x y z m : Word256) :
      Word256.bitNot (Word256.bitMaj (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitClearMask y m) (Word256.bitNot (Word256.bitClearMask z m))) =
        Word256.bitAnd
          (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitClearMask y m)))
          (Word256.bitAnd
            (Word256.bitNot (Word256.bitAnd (Word256.bitClearMask y m) (Word256.bitNot (Word256.bitClearMask z m))))
            (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask z m))))) :=
    (bitNot_bitOr
      (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitClearMask y m))
      (Word256.bitOr
        (Word256.bitAnd (Word256.bitClearMask y m) (Word256.bitNot (Word256.bitClearMask z m)))
        (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask z m))))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitClearMask y m))))
        (bitNot_bitOr
          (Word256.bitAnd (Word256.bitClearMask y m) (Word256.bitNot (Word256.bitClearMask z m)))
          (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask z m)))))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMaj_bitFlipMask_not_left_not_right (x y z m : Word256) :
      Word256.bitNot (Word256.bitMaj (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitFlipMask y m) (Word256.bitNot (Word256.bitFlipMask z m))) =
        Word256.bitAnd
          (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitFlipMask y m)))
          (Word256.bitAnd
            (Word256.bitNot (Word256.bitAnd (Word256.bitFlipMask y m) (Word256.bitNot (Word256.bitFlipMask z m))))
            (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask z m))))) :=
    (bitNot_bitOr
      (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitFlipMask y m))
      (Word256.bitOr
        (Word256.bitAnd (Word256.bitFlipMask y m) (Word256.bitNot (Word256.bitFlipMask z m)))
        (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask z m))))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitFlipMask y m))))
        (bitNot_bitOr
          (Word256.bitAnd (Word256.bitFlipMask y m) (Word256.bitNot (Word256.bitFlipMask z m)))
          (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask z m)))))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMaj_bitSetMask_all_not (x y z m : Word256) :
      Word256.bitNot (Word256.bitMaj (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m)) (Word256.bitNot (Word256.bitSetMask z m))) =
        Word256.bitAnd
          (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m))))
          (Word256.bitAnd
            (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask y m)) (Word256.bitNot (Word256.bitSetMask z m))))
            (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask z m))))) :=
    (bitNot_bitOr
      (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m)))
      (Word256.bitOr
        (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask y m)) (Word256.bitNot (Word256.bitSetMask z m)))
        (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask z m))))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m)))))
        (bitNot_bitOr
          (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask y m)) (Word256.bitNot (Word256.bitSetMask z m)))
          (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask z m)))))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMaj_bitClearMask_all_not (x y z m : Word256) :
      Word256.bitNot (Word256.bitMaj (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m)) (Word256.bitNot (Word256.bitClearMask z m))) =
        Word256.bitAnd
          (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m))))
          (Word256.bitAnd
            (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask y m)) (Word256.bitNot (Word256.bitClearMask z m))))
            (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask z m))))) :=
    (bitNot_bitOr
      (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m)))
      (Word256.bitOr
        (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask y m)) (Word256.bitNot (Word256.bitClearMask z m)))
        (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask z m))))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m)))))
        (bitNot_bitOr
          (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask y m)) (Word256.bitNot (Word256.bitClearMask z m)))
          (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask z m)))))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMaj_bitFlipMask_all_not (x y z m : Word256) :
      Word256.bitNot (Word256.bitMaj (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m)) (Word256.bitNot (Word256.bitFlipMask z m))) =
        Word256.bitAnd
          (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m))))
          (Word256.bitAnd
            (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask y m)) (Word256.bitNot (Word256.bitFlipMask z m))))
            (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask z m))))) :=
    (bitNot_bitOr
      (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m)))
      (Word256.bitOr
        (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask y m)) (Word256.bitNot (Word256.bitFlipMask z m)))
        (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask z m))))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m)))))
        (bitNot_bitOr
          (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask y m)) (Word256.bitNot (Word256.bitFlipMask z m)))
          (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask z m)))))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitParity_bitSetMask_not_mid_not_right (x y z m : Word256) :
      Word256.bitNot (Word256.bitParity (Word256.bitSetMask x m) (Word256.bitNot (Word256.bitSetMask y m)) (Word256.bitNot (Word256.bitSetMask z m))) =
        Word256.bitParity (Word256.bitSetMask x m) (Word256.bitNot (Word256.bitSetMask y m)) (Word256.bitSetMask z m) :=
    (bitXor_max_right (Word256.bitParity (Word256.bitSetMask x m) (Word256.bitNot (Word256.bitSetMask y m)) (Word256.bitNot (Word256.bitSetMask z m)))).symm.trans <|
      (bitXor_assoc (Word256.bitXor (Word256.bitSetMask x m) (Word256.bitNot (Word256.bitSetMask y m))) (Word256.bitNot (Word256.bitSetMask z m)) Word256.max).trans <|
        congrArg (Word256.bitXor (Word256.bitXor (Word256.bitSetMask x m) (Word256.bitNot (Word256.bitSetMask y m))))
          ((bitXor_max_right (Word256.bitNot (Word256.bitSetMask z m))).trans (bitNot_bitNot (Word256.bitSetMask z m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitParity_bitClearMask_not_mid_not_right (x y z m : Word256) :
      Word256.bitNot (Word256.bitParity (Word256.bitClearMask x m) (Word256.bitNot (Word256.bitClearMask y m)) (Word256.bitNot (Word256.bitClearMask z m))) =
        Word256.bitParity (Word256.bitClearMask x m) (Word256.bitNot (Word256.bitClearMask y m)) (Word256.bitClearMask z m) :=
    (bitXor_max_right (Word256.bitParity (Word256.bitClearMask x m) (Word256.bitNot (Word256.bitClearMask y m)) (Word256.bitNot (Word256.bitClearMask z m)))).symm.trans <|
      (bitXor_assoc (Word256.bitXor (Word256.bitClearMask x m) (Word256.bitNot (Word256.bitClearMask y m))) (Word256.bitNot (Word256.bitClearMask z m)) Word256.max).trans <|
        congrArg (Word256.bitXor (Word256.bitXor (Word256.bitClearMask x m) (Word256.bitNot (Word256.bitClearMask y m))))
          ((bitXor_max_right (Word256.bitNot (Word256.bitClearMask z m))).trans (bitNot_bitNot (Word256.bitClearMask z m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitParity_bitFlipMask_not_mid_not_right (x y z m : Word256) :
      Word256.bitNot (Word256.bitParity (Word256.bitFlipMask x m) (Word256.bitNot (Word256.bitFlipMask y m)) (Word256.bitNot (Word256.bitFlipMask z m))) =
        Word256.bitParity (Word256.bitFlipMask x m) (Word256.bitNot (Word256.bitFlipMask y m)) (Word256.bitFlipMask z m) :=
    (bitXor_max_right (Word256.bitParity (Word256.bitFlipMask x m) (Word256.bitNot (Word256.bitFlipMask y m)) (Word256.bitNot (Word256.bitFlipMask z m)))).symm.trans <|
      (bitXor_assoc (Word256.bitXor (Word256.bitFlipMask x m) (Word256.bitNot (Word256.bitFlipMask y m))) (Word256.bitNot (Word256.bitFlipMask z m)) Word256.max).trans <|
        congrArg (Word256.bitXor (Word256.bitXor (Word256.bitFlipMask x m) (Word256.bitNot (Word256.bitFlipMask y m))))
          ((bitXor_max_right (Word256.bitNot (Word256.bitFlipMask z m))).trans (bitNot_bitNot (Word256.bitFlipMask z m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitParity_bitSetMask_not_left_not_right (x y z m : Word256) :
      Word256.bitNot (Word256.bitParity (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitSetMask y m) (Word256.bitNot (Word256.bitSetMask z m))) =
        Word256.bitParity (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitSetMask y m) (Word256.bitSetMask z m) :=
    (bitXor_max_right (Word256.bitParity (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitSetMask y m) (Word256.bitNot (Word256.bitSetMask z m)))).symm.trans <|
      (bitXor_assoc (Word256.bitXor (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitSetMask y m)) (Word256.bitNot (Word256.bitSetMask z m)) Word256.max).trans <|
        congrArg (Word256.bitXor (Word256.bitXor (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitSetMask y m)))
          ((bitXor_max_right (Word256.bitNot (Word256.bitSetMask z m))).trans (bitNot_bitNot (Word256.bitSetMask z m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitParity_bitClearMask_not_left_not_right (x y z m : Word256) :
      Word256.bitNot (Word256.bitParity (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitClearMask y m) (Word256.bitNot (Word256.bitClearMask z m))) =
        Word256.bitParity (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitClearMask y m) (Word256.bitClearMask z m) :=
    (bitXor_max_right (Word256.bitParity (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitClearMask y m) (Word256.bitNot (Word256.bitClearMask z m)))).symm.trans <|
      (bitXor_assoc (Word256.bitXor (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitClearMask y m)) (Word256.bitNot (Word256.bitClearMask z m)) Word256.max).trans <|
        congrArg (Word256.bitXor (Word256.bitXor (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitClearMask y m)))
          ((bitXor_max_right (Word256.bitNot (Word256.bitClearMask z m))).trans (bitNot_bitNot (Word256.bitClearMask z m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitParity_bitFlipMask_not_left_not_right (x y z m : Word256) :
      Word256.bitNot (Word256.bitParity (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitFlipMask y m) (Word256.bitNot (Word256.bitFlipMask z m))) =
        Word256.bitParity (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitFlipMask y m) (Word256.bitFlipMask z m) :=
    (bitXor_max_right (Word256.bitParity (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitFlipMask y m) (Word256.bitNot (Word256.bitFlipMask z m)))).symm.trans <|
      (bitXor_assoc (Word256.bitXor (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitFlipMask y m)) (Word256.bitNot (Word256.bitFlipMask z m)) Word256.max).trans <|
        congrArg (Word256.bitXor (Word256.bitXor (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitFlipMask y m)))
          ((bitXor_max_right (Word256.bitNot (Word256.bitFlipMask z m))).trans (bitNot_bitNot (Word256.bitFlipMask z m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitParity_bitSetMask_all_not (x y z m : Word256) :
      Word256.bitNot (Word256.bitParity (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m)) (Word256.bitNot (Word256.bitSetMask z m))) =
        Word256.bitParity (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m)) (Word256.bitSetMask z m) :=
    (bitXor_max_right (Word256.bitParity (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m)) (Word256.bitNot (Word256.bitSetMask z m)))).symm.trans <|
      (bitXor_assoc (Word256.bitXor (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m))) (Word256.bitNot (Word256.bitSetMask z m)) Word256.max).trans <|
        congrArg (Word256.bitXor (Word256.bitXor (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m))))
          ((bitXor_max_right (Word256.bitNot (Word256.bitSetMask z m))).trans (bitNot_bitNot (Word256.bitSetMask z m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitParity_bitClearMask_all_not (x y z m : Word256) :
      Word256.bitNot (Word256.bitParity (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m)) (Word256.bitNot (Word256.bitClearMask z m))) =
        Word256.bitParity (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m)) (Word256.bitClearMask z m) :=
    (bitXor_max_right (Word256.bitParity (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m)) (Word256.bitNot (Word256.bitClearMask z m)))).symm.trans <|
      (bitXor_assoc (Word256.bitXor (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m))) (Word256.bitNot (Word256.bitClearMask z m)) Word256.max).trans <|
        congrArg (Word256.bitXor (Word256.bitXor (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m))))
          ((bitXor_max_right (Word256.bitNot (Word256.bitClearMask z m))).trans (bitNot_bitNot (Word256.bitClearMask z m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitParity_bitFlipMask_all_not (x y z m : Word256) :
      Word256.bitNot (Word256.bitParity (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m)) (Word256.bitNot (Word256.bitFlipMask z m))) =
        Word256.bitParity (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m)) (Word256.bitFlipMask z m) :=
    (bitXor_max_right (Word256.bitParity (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m)) (Word256.bitNot (Word256.bitFlipMask z m)))).symm.trans <|
      (bitXor_assoc (Word256.bitXor (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m))) (Word256.bitNot (Word256.bitFlipMask z m)) Word256.max).trans <|
        congrArg (Word256.bitXor (Word256.bitXor (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m))))
          ((bitXor_max_right (Word256.bitNot (Word256.bitFlipMask z m))).trans (bitNot_bitNot (Word256.bitFlipMask z m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux_bitSetMask_not_then_not_else (mask x y m : Word256) :
      Word256.bitNot (Word256.bitMux mask (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m))) =
        Word256.bitMux mask (Word256.bitSetMask x m) (Word256.bitSetMask y m) :=
    (bitNot_bitMux mask (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m))).trans <|
      (congrArg (fun a => Word256.bitMux mask a (Word256.bitNot (Word256.bitNot (Word256.bitSetMask y m))))
        (bitNot_bitNot (Word256.bitSetMask x m))).trans
        (congrArg (Word256.bitMux mask (Word256.bitSetMask x m))
          (bitNot_bitNot (Word256.bitSetMask y m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux_bitClearMask_not_then_not_else (mask x y m : Word256) :
      Word256.bitNot (Word256.bitMux mask (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m))) =
        Word256.bitMux mask (Word256.bitClearMask x m) (Word256.bitClearMask y m) :=
    (bitNot_bitMux mask (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m))).trans <|
      (congrArg (fun a => Word256.bitMux mask a (Word256.bitNot (Word256.bitNot (Word256.bitClearMask y m))))
        (bitNot_bitNot (Word256.bitClearMask x m))).trans
        (congrArg (Word256.bitMux mask (Word256.bitClearMask x m))
          (bitNot_bitNot (Word256.bitClearMask y m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux_bitFlipMask_not_then_not_else (mask x y m : Word256) :
      Word256.bitNot (Word256.bitMux mask (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m))) =
        Word256.bitMux mask (Word256.bitFlipMask x m) (Word256.bitFlipMask y m) :=
    (bitNot_bitMux mask (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m))).trans <|
      (congrArg (fun a => Word256.bitMux mask a (Word256.bitNot (Word256.bitNot (Word256.bitFlipMask y m))))
        (bitNot_bitNot (Word256.bitFlipMask x m))).trans
        (congrArg (Word256.bitMux mask (Word256.bitFlipMask x m))
          (bitNot_bitNot (Word256.bitFlipMask y m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux_bitSetMask_not_cond_not_then (x y m b : Word256) :
      Word256.bitNot (Word256.bitMux (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m)) b) =
        Word256.bitMux (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitSetMask y m) (Word256.bitNot b) :=
    (bitNot_bitMux (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m)) b).trans
      (congrArg (fun a => Word256.bitMux (Word256.bitNot (Word256.bitSetMask x m)) a (Word256.bitNot b))
        (bitNot_bitNot (Word256.bitSetMask y m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux_bitClearMask_not_cond_not_then (x y m b : Word256) :
      Word256.bitNot (Word256.bitMux (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m)) b) =
        Word256.bitMux (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitClearMask y m) (Word256.bitNot b) :=
    (bitNot_bitMux (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m)) b).trans
      (congrArg (fun a => Word256.bitMux (Word256.bitNot (Word256.bitClearMask x m)) a (Word256.bitNot b))
        (bitNot_bitNot (Word256.bitClearMask y m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux_bitFlipMask_not_cond_not_then (x y m b : Word256) :
      Word256.bitNot (Word256.bitMux (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m)) b) =
        Word256.bitMux (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitFlipMask y m) (Word256.bitNot b) :=
    (bitNot_bitMux (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m)) b).trans
      (congrArg (fun a => Word256.bitMux (Word256.bitNot (Word256.bitFlipMask x m)) a (Word256.bitNot b))
        (bitNot_bitNot (Word256.bitFlipMask y m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux_bitSetMask_not_cond_not_else (x m a z : Word256) :
      Word256.bitNot (Word256.bitMux (Word256.bitNot (Word256.bitSetMask x m)) a (Word256.bitNot (Word256.bitSetMask z m))) =
        Word256.bitMux (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot a) (Word256.bitSetMask z m) :=
    (bitNot_bitMux (Word256.bitNot (Word256.bitSetMask x m)) a (Word256.bitNot (Word256.bitSetMask z m))).trans
      (congrArg (Word256.bitMux (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot a))
        (bitNot_bitNot (Word256.bitSetMask z m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux_bitClearMask_not_cond_not_else (x m a z : Word256) :
      Word256.bitNot (Word256.bitMux (Word256.bitNot (Word256.bitClearMask x m)) a (Word256.bitNot (Word256.bitClearMask z m))) =
        Word256.bitMux (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot a) (Word256.bitClearMask z m) :=
    (bitNot_bitMux (Word256.bitNot (Word256.bitClearMask x m)) a (Word256.bitNot (Word256.bitClearMask z m))).trans
      (congrArg (Word256.bitMux (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot a))
        (bitNot_bitNot (Word256.bitClearMask z m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux_bitFlipMask_not_cond_not_else (x m a z : Word256) :
      Word256.bitNot (Word256.bitMux (Word256.bitNot (Word256.bitFlipMask x m)) a (Word256.bitNot (Word256.bitFlipMask z m))) =
        Word256.bitMux (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot a) (Word256.bitFlipMask z m) :=
    (bitNot_bitMux (Word256.bitNot (Word256.bitFlipMask x m)) a (Word256.bitNot (Word256.bitFlipMask z m))).trans
      (congrArg (Word256.bitMux (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot a))
        (bitNot_bitNot (Word256.bitFlipMask z m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux_bitSetMask_all_not (x y z m : Word256) :
      Word256.bitNot (Word256.bitMux (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m)) (Word256.bitNot (Word256.bitSetMask z m))) =
        Word256.bitMux (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitSetMask y m) (Word256.bitSetMask z m) :=
    bitNot_bitMux_bitSetMask_not_then_not_else (Word256.bitNot (Word256.bitSetMask x m)) y z m

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux_bitClearMask_all_not (x y z m : Word256) :
      Word256.bitNot (Word256.bitMux (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m)) (Word256.bitNot (Word256.bitClearMask z m))) =
        Word256.bitMux (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitClearMask y m) (Word256.bitClearMask z m) :=
    bitNot_bitMux_bitClearMask_not_then_not_else (Word256.bitNot (Word256.bitClearMask x m)) y z m

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux_bitFlipMask_all_not (x y z m : Word256) :
      Word256.bitNot (Word256.bitMux (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m)) (Word256.bitNot (Word256.bitFlipMask z m))) =
        Word256.bitMux (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitFlipMask y m) (Word256.bitFlipMask z m) :=
    bitNot_bitMux_bitFlipMask_not_then_not_else (Word256.bitNot (Word256.bitFlipMask x m)) y z m

set_option maxHeartbeats 200000 in
  theorem bitNot_bitAnd_bitSetMask_not_left (x y m : Word256) :
      Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitSetMask y m)) =
        Word256.bitOr (Word256.bitSetMask x m) (Word256.bitNot (Word256.bitSetMask y m)) :=
    (bitNot_bitAnd (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitSetMask y m)).trans
      (congrArg (Word256.bitOr · (Word256.bitNot (Word256.bitSetMask y m)))
        (bitNot_bitNot (Word256.bitSetMask x m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitAnd_bitClearMask_not_left (x y m : Word256) :
      Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitClearMask y m)) =
        Word256.bitOr (Word256.bitClearMask x m) (Word256.bitNot (Word256.bitClearMask y m)) :=
    (bitNot_bitAnd (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitClearMask y m)).trans
      (congrArg (Word256.bitOr · (Word256.bitNot (Word256.bitClearMask y m)))
        (bitNot_bitNot (Word256.bitClearMask x m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitAnd_bitFlipMask_not_left (x y m : Word256) :
      Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitFlipMask y m)) =
        Word256.bitOr (Word256.bitFlipMask x m) (Word256.bitNot (Word256.bitFlipMask y m)) :=
    (bitNot_bitAnd (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitFlipMask y m)).trans
      (congrArg (Word256.bitOr · (Word256.bitNot (Word256.bitFlipMask y m)))
        (bitNot_bitNot (Word256.bitFlipMask x m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitAnd_bitSetMask_not_right (x y m : Word256) :
      Word256.bitNot (Word256.bitAnd (Word256.bitSetMask x m) (Word256.bitNot (Word256.bitSetMask y m))) =
        Word256.bitOr (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitSetMask y m) :=
    (bitNot_bitAnd (Word256.bitSetMask x m) (Word256.bitNot (Word256.bitSetMask y m))).trans
      (congrArg (Word256.bitOr (Word256.bitNot (Word256.bitSetMask x m)))
        (bitNot_bitNot (Word256.bitSetMask y m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitAnd_bitClearMask_not_right (x y m : Word256) :
      Word256.bitNot (Word256.bitAnd (Word256.bitClearMask x m) (Word256.bitNot (Word256.bitClearMask y m))) =
        Word256.bitOr (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitClearMask y m) :=
    (bitNot_bitAnd (Word256.bitClearMask x m) (Word256.bitNot (Word256.bitClearMask y m))).trans
      (congrArg (Word256.bitOr (Word256.bitNot (Word256.bitClearMask x m)))
        (bitNot_bitNot (Word256.bitClearMask y m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitAnd_bitFlipMask_not_right (x y m : Word256) :
      Word256.bitNot (Word256.bitAnd (Word256.bitFlipMask x m) (Word256.bitNot (Word256.bitFlipMask y m))) =
        Word256.bitOr (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitFlipMask y m) :=
    (bitNot_bitAnd (Word256.bitFlipMask x m) (Word256.bitNot (Word256.bitFlipMask y m))).trans
      (congrArg (Word256.bitOr (Word256.bitNot (Word256.bitFlipMask x m)))
        (bitNot_bitNot (Word256.bitFlipMask y m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitAnd_bitSetMask_both_not (x y m : Word256) :
      Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m))) =
        Word256.bitOr (Word256.bitSetMask x m) (Word256.bitSetMask y m) :=
    (bitNot_bitAnd (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m))).trans <|
      (congrArg (Word256.bitOr · (Word256.bitNot (Word256.bitNot (Word256.bitSetMask y m))))
        (bitNot_bitNot (Word256.bitSetMask x m))).trans
        (congrArg (Word256.bitOr (Word256.bitSetMask x m))
          (bitNot_bitNot (Word256.bitSetMask y m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitAnd_bitClearMask_both_not (x y m : Word256) :
      Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m))) =
        Word256.bitOr (Word256.bitClearMask x m) (Word256.bitClearMask y m) :=
    (bitNot_bitAnd (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m))).trans <|
      (congrArg (Word256.bitOr · (Word256.bitNot (Word256.bitNot (Word256.bitClearMask y m))))
        (bitNot_bitNot (Word256.bitClearMask x m))).trans
        (congrArg (Word256.bitOr (Word256.bitClearMask x m))
          (bitNot_bitNot (Word256.bitClearMask y m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitAnd_bitFlipMask_both_not (x y m : Word256) :
      Word256.bitNot (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m))) =
        Word256.bitOr (Word256.bitFlipMask x m) (Word256.bitFlipMask y m) :=
    (bitNot_bitAnd (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m))).trans <|
      (congrArg (Word256.bitOr · (Word256.bitNot (Word256.bitNot (Word256.bitFlipMask y m))))
        (bitNot_bitNot (Word256.bitFlipMask x m))).trans
        (congrArg (Word256.bitOr (Word256.bitFlipMask x m))
          (bitNot_bitNot (Word256.bitFlipMask y m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitOr_bitSetMask_not_left (x y m : Word256) :
      Word256.bitNot (Word256.bitOr (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitSetMask y m)) =
        Word256.bitAnd (Word256.bitSetMask x m) (Word256.bitNot (Word256.bitSetMask y m)) :=
    (bitNot_bitOr (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitSetMask y m)).trans
      (congrArg (Word256.bitAnd · (Word256.bitNot (Word256.bitSetMask y m)))
        (bitNot_bitNot (Word256.bitSetMask x m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitOr_bitClearMask_not_left (x y m : Word256) :
      Word256.bitNot (Word256.bitOr (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitClearMask y m)) =
        Word256.bitAnd (Word256.bitClearMask x m) (Word256.bitNot (Word256.bitClearMask y m)) :=
    (bitNot_bitOr (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitClearMask y m)).trans
      (congrArg (Word256.bitAnd · (Word256.bitNot (Word256.bitClearMask y m)))
        (bitNot_bitNot (Word256.bitClearMask x m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitOr_bitFlipMask_not_left (x y m : Word256) :
      Word256.bitNot (Word256.bitOr (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitFlipMask y m)) =
        Word256.bitAnd (Word256.bitFlipMask x m) (Word256.bitNot (Word256.bitFlipMask y m)) :=
    (bitNot_bitOr (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitFlipMask y m)).trans
      (congrArg (Word256.bitAnd · (Word256.bitNot (Word256.bitFlipMask y m)))
        (bitNot_bitNot (Word256.bitFlipMask x m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitOr_bitSetMask_not_right (x y m : Word256) :
      Word256.bitNot (Word256.bitOr (Word256.bitSetMask x m) (Word256.bitNot (Word256.bitSetMask y m))) =
        Word256.bitAnd (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitSetMask y m) :=
    (bitNot_bitOr (Word256.bitSetMask x m) (Word256.bitNot (Word256.bitSetMask y m))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitSetMask x m)))
        (bitNot_bitNot (Word256.bitSetMask y m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitOr_bitClearMask_not_right (x y m : Word256) :
      Word256.bitNot (Word256.bitOr (Word256.bitClearMask x m) (Word256.bitNot (Word256.bitClearMask y m))) =
        Word256.bitAnd (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitClearMask y m) :=
    (bitNot_bitOr (Word256.bitClearMask x m) (Word256.bitNot (Word256.bitClearMask y m))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitClearMask x m)))
        (bitNot_bitNot (Word256.bitClearMask y m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitOr_bitFlipMask_not_right (x y m : Word256) :
      Word256.bitNot (Word256.bitOr (Word256.bitFlipMask x m) (Word256.bitNot (Word256.bitFlipMask y m))) =
        Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitFlipMask y m) :=
    (bitNot_bitOr (Word256.bitFlipMask x m) (Word256.bitNot (Word256.bitFlipMask y m))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitFlipMask x m)))
        (bitNot_bitNot (Word256.bitFlipMask y m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitOr_bitSetMask_both_not (x y m : Word256) :
      Word256.bitNot (Word256.bitOr (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m))) =
        Word256.bitAnd (Word256.bitSetMask x m) (Word256.bitSetMask y m) :=
    (bitNot_bitOr (Word256.bitNot (Word256.bitSetMask x m)) (Word256.bitNot (Word256.bitSetMask y m))).trans <|
      (congrArg (Word256.bitAnd · (Word256.bitNot (Word256.bitNot (Word256.bitSetMask y m))))
        (bitNot_bitNot (Word256.bitSetMask x m))).trans
        (congrArg (Word256.bitAnd (Word256.bitSetMask x m))
          (bitNot_bitNot (Word256.bitSetMask y m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitOr_bitClearMask_both_not (x y m : Word256) :
      Word256.bitNot (Word256.bitOr (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m))) =
        Word256.bitAnd (Word256.bitClearMask x m) (Word256.bitClearMask y m) :=
    (bitNot_bitOr (Word256.bitNot (Word256.bitClearMask x m)) (Word256.bitNot (Word256.bitClearMask y m))).trans <|
      (congrArg (Word256.bitAnd · (Word256.bitNot (Word256.bitNot (Word256.bitClearMask y m))))
        (bitNot_bitNot (Word256.bitClearMask x m))).trans
        (congrArg (Word256.bitAnd (Word256.bitClearMask x m))
          (bitNot_bitNot (Word256.bitClearMask y m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitOr_bitFlipMask_both_not (x y m : Word256) :
      Word256.bitNot (Word256.bitOr (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m))) =
        Word256.bitAnd (Word256.bitFlipMask x m) (Word256.bitFlipMask y m) :=
    (bitNot_bitOr (Word256.bitNot (Word256.bitFlipMask x m)) (Word256.bitNot (Word256.bitFlipMask y m))).trans <|
      (congrArg (Word256.bitAnd · (Word256.bitNot (Word256.bitNot (Word256.bitFlipMask y m))))
        (bitNot_bitNot (Word256.bitFlipMask x m))).trans
        (congrArg (Word256.bitAnd (Word256.bitFlipMask x m))
          (bitNot_bitNot (Word256.bitFlipMask y m)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitOr_assoc_left_not (a b c : Word256) :
      Word256.bitNot (Word256.bitOr (Word256.bitOr (Word256.bitNot a) b) c) =
        Word256.bitAnd (Word256.bitAnd a (Word256.bitNot b)) (Word256.bitNot c) :=
    (bitNot_bitOr (Word256.bitOr (Word256.bitNot a) b) c).trans <|
      (congrArg (Word256.bitAnd · (Word256.bitNot c))
        (bitNot_bitOr (Word256.bitNot a) b)).trans
        (congrArg (fun x => Word256.bitAnd (Word256.bitAnd x (Word256.bitNot b)) (Word256.bitNot c))
          (bitNot_bitNot a))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitOr_assoc_mid_not (a b c : Word256) :
      Word256.bitNot (Word256.bitOr (Word256.bitOr a (Word256.bitNot b)) c) =
        Word256.bitAnd (Word256.bitAnd (Word256.bitNot a) b) (Word256.bitNot c) :=
    (bitNot_bitOr (Word256.bitOr a (Word256.bitNot b)) c).trans <|
      (congrArg (Word256.bitAnd · (Word256.bitNot c))
        (bitNot_bitOr a (Word256.bitNot b))).trans
        (congrArg (fun x => Word256.bitAnd (Word256.bitAnd (Word256.bitNot a) x) (Word256.bitNot c))
          (bitNot_bitNot b))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitOr_assoc_right_not (a b c : Word256) :
      Word256.bitNot (Word256.bitOr (Word256.bitOr a b) (Word256.bitNot c)) =
        Word256.bitAnd (Word256.bitAnd (Word256.bitNot a) (Word256.bitNot b)) c :=
    (bitNot_bitOr (Word256.bitOr a b) (Word256.bitNot c)).trans <|
      (congrArg (Word256.bitAnd · (Word256.bitNot (Word256.bitNot c)))
        (bitNot_bitOr a b)).trans
        (congrArg (Word256.bitAnd (Word256.bitAnd (Word256.bitNot a) (Word256.bitNot b)))
          (bitNot_bitNot c))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitOr_assoc_all_not (a b c : Word256) :
      Word256.bitNot (Word256.bitOr (Word256.bitOr (Word256.bitNot a) (Word256.bitNot b)) (Word256.bitNot c)) =
        Word256.bitAnd (Word256.bitAnd a b) c :=
    (bitNot_bitOr_assoc_right_not (Word256.bitNot a) (Word256.bitNot b) c).trans <|
      (congrArg (fun x => Word256.bitAnd (Word256.bitAnd x (Word256.bitNot (Word256.bitNot b))) c)
        (bitNot_bitNot a)).trans
        (congrArg (fun x => Word256.bitAnd (Word256.bitAnd a x) c)
          (bitNot_bitNot b))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitOr_bitAnd_distrib_not (a b c : Word256) :
      Word256.bitNot (Word256.bitOr a (Word256.bitAnd b c)) =
        Word256.bitOr (Word256.bitAnd (Word256.bitNot a) (Word256.bitNot b)) (Word256.bitAnd (Word256.bitNot a) (Word256.bitNot c)) :=
    (bitNot_bitOr a (Word256.bitAnd b c)).trans <|
      (congrArg (Word256.bitAnd (Word256.bitNot a)) (bitNot_bitAnd b c)).trans
        (bitAnd_bitOr_distrib_left (Word256.bitNot a) (Word256.bitNot b) (Word256.bitNot c))

end TurboLean.FastCheck
