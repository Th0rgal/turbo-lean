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

end TurboLean.FastCheck
