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

@[inline]
def Word256.bitMaj (a b c : Word256) : Word256 :=
  Word256.bitOr (Word256.bitAnd a b) (Word256.bitOr (Word256.bitAnd b c) (Word256.bitAnd a c))

@[inline]
def Word256.bitParity (a b c : Word256) : Word256 :=
  Word256.bitXor (Word256.bitXor a b) c

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux_not_cond_swap (mask a b : Word256) :
      Word256.bitNot (Word256.bitMux (Word256.bitNot mask) a b) =
        Word256.bitMux mask (Word256.bitNot b) (Word256.bitNot a) :=
    (bitNot_bitMux (Word256.bitNot mask) a b).trans
      (bitMux_bitNot_mask mask (Word256.bitNot a) (Word256.bitNot b))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux_not_cond_both_not (mask a b : Word256) :
      Word256.bitNot (Word256.bitMux (Word256.bitNot mask) (Word256.bitNot a) (Word256.bitNot b)) =
        Word256.bitMux mask b a :=
    (bitNot_bitMux_not_cond_swap mask (Word256.bitNot a) (Word256.bitNot b)).trans <|
      (congrArg (fun x => Word256.bitMux mask x (Word256.bitNot (Word256.bitNot a))) (bitNot_bitNot b)).trans
        (congrArg (Word256.bitMux mask b) (bitNot_bitNot a))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMaj_not_a_not_b (a b c : Word256) :
      Word256.bitNot (Word256.bitMaj (Word256.bitNot a) (Word256.bitNot b) c) =
        Word256.bitAnd
          (Word256.bitNot (Word256.bitAnd (Word256.bitNot a) (Word256.bitNot b)))
          (Word256.bitAnd
            (Word256.bitNot (Word256.bitAnd (Word256.bitNot b) c))
            (Word256.bitNot (Word256.bitAnd (Word256.bitNot a) c))) :=
    (bitNot_bitOr
      (Word256.bitAnd (Word256.bitNot a) (Word256.bitNot b))
      (Word256.bitOr
        (Word256.bitAnd (Word256.bitNot b) c)
        (Word256.bitAnd (Word256.bitNot a) c))).trans
      (congrArg (Word256.bitAnd (Word256.bitNot (Word256.bitAnd (Word256.bitNot a) (Word256.bitNot b))))
        (bitNot_bitOr
          (Word256.bitAnd (Word256.bitNot b) c)
          (Word256.bitAnd (Word256.bitNot a) c)))

set_option maxHeartbeats 200000 in
  theorem bitNot_bitParity_not_b_not_c (a b c : Word256) :
      Word256.bitNot (Word256.bitParity a (Word256.bitNot b) (Word256.bitNot c)) =
        Word256.bitParity a (Word256.bitNot b) c :=
    (bitXor_max_right (Word256.bitParity a (Word256.bitNot b) (Word256.bitNot c))).symm.trans <|
      (bitXor_assoc (Word256.bitXor a (Word256.bitNot b)) (Word256.bitNot c) Word256.max).trans <|
        congrArg (Word256.bitXor (Word256.bitXor a (Word256.bitNot b)))
          ((bitXor_max_right (Word256.bitNot c)).trans (bitNot_bitNot c))

end TurboLean.FastCheck
