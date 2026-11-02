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
  | .i256 => 8
  | .i512 => 8

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

inductive MemCell where
  | byte : BitVec 8 → MemCell
  | int : (w : IntWidth) → BitVec w.bits → MemCell
  | ptr : BitVec 64 → MemCell
  | floatBits : (fw : FloatWidth) → BitVec fw.bits → MemCell
  | poison : MemCell
  deriving Repr, DecidableEq, Inhabited

structure ByteMem where
  cells : List (Nat × MemCell) := []
  nextAlloc : Nat := 4096
  deriving Repr, DecidableEq, Inhabited

namespace ByteMem

def empty : ByteMem := {}

def readCells (a : Nat) : List (Nat × MemCell) → Option MemCell
  | [] => none
  | (k, c) :: rest => if a == k then some c else readCells a rest

def readAt (m : ByteMem) (a : Nat) : Option MemCell :=
  readCells a m.cells

def writeAt (m : ByteMem) (a : Nat) (c : MemCell) : ByteMem :=
  { m with cells := (a, c) :: m.cells }

theorem readAt_writeAt_same (m : ByteMem) (a : Nat) (c : MemCell) :
    (m.writeAt a c).readAt a = some c := by
  simp [readAt, writeAt, readCells]

theorem readAt_writeAt_ne (m : ByteMem) (a1 a2 : Nat) (c : MemCell)
    (hne : a1 ≠ a2) :
    (m.writeAt a1 c).readAt a2 = m.readAt a2 := by
  have hbeq : (a2 == a1) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
  simp [readAt, writeAt, readCells, hbeq]

def writeBytesAt (m : ByteMem) (base : Nat) : List (BitVec 8) → ByteMem
  | [] => m
  | b :: bs => writeBytesAt (m.writeAt base (.byte b)) (base + 1) bs

def readByte (m : ByteMem) (a : Nat) : BitVec 8 :=
  match m.readAt a with
  | some (.byte b) => b
  | _ => 0#8

def readBytesAt (m : ByteMem) (base n : Nat) : List (BitVec 8) :=
  match n with
  | 0 => []
  | k + 1 => m.readByte base :: readBytesAt m (base + 1) k

theorem readBytesAt_length (m : ByteMem) (base n : Nat) :
    (m.readBytesAt base n).length = n := by
  induction n generalizing base with
  | zero => rfl
  | succ k ih =>
    simp [readBytesAt, ih]

theorem readAt_writeBytesAt_outside (m : ByteMem) (base : Nat) (bs : List (BitVec 8)) (q : Nat)
    (hout : q < base ∨ base + bs.length ≤ q) :
    (m.writeBytesAt base bs).readAt q = m.readAt q := by
  induction bs generalizing m base with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.length_cons] at hout
    have hne : base ≠ q := by omega
    have hout' : q < base + 1 ∨ (base + 1) + rest.length ≤ q := by omega
    simp only [writeBytesAt]
    rw [ih (m.writeAt base (.byte b)) (base + 1) hout']
    exact readAt_writeAt_ne m base q (.byte b) hne

theorem readBytesAt_writeBytesAt_same (m : ByteMem) (base : Nat) (bs : List (BitVec 8)) :
    (m.writeBytesAt base bs).readBytesAt base bs.length = bs := by
  induction bs generalizing m base with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.length_cons, writeBytesAt, readBytesAt]
    have hhead : ((m.writeAt base (.byte b)).writeBytesAt (base + 1) rest).readByte base = b := by
      simp only [readByte]
      rw [readAt_writeBytesAt_outside (m.writeAt base (.byte b)) (base + 1) rest base (Or.inl (by omega))]
      simp [readAt_writeAt_same]
    rw [hhead, ih (m.writeAt base (.byte b)) (base + 1)]

theorem readBytesAt_writeBytesAt_disjoint (m : ByteMem) (b1 : Nat) (bs : List (BitVec 8))
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

def storeInt (m : ByteMem) (addr : BitVec 64) (w : IntWidth) (v : BitVec w.bits) : ByteMem :=
  m.writeAt addr.toNat (.int w v)

def loadInt (m : ByteMem) (addr : BitVec 64) (w : IntWidth) : BitVec w.bits :=
  match m.readAt addr.toNat with
  | some (.int w' v) =>
    if h : w' = w then h ▸ v else 0#w.bits
  | _ => 0#w.bits

def storePtr (m : ByteMem) (addr ptrVal : BitVec 64) : ByteMem :=
  m.writeAt addr.toNat (.ptr ptrVal)

def loadPtr (m : ByteMem) (addr : BitVec 64) : BitVec 64 :=
  match m.readAt addr.toNat with
  | some (.ptr p) => p
  | _ => 0#64

def storeFloatBits (m : ByteMem) (addr : BitVec 64) (fw : FloatWidth) (v : BitVec fw.bits) : ByteMem :=
  m.writeAt addr.toNat (.floatBits fw v)

def loadFloatBits (m : ByteMem) (addr : BitVec 64) (fw : FloatWidth) : BitVec fw.bits :=
  match m.readAt addr.toNat with
  | some (.floatBits fw' v) =>
    if h : fw' = fw then h ▸ v else 0#fw.bits
  | _ => 0#fw.bits

def storePoison (m : ByteMem) (addr : BitVec 64) : ByteMem :=
  m.writeAt addr.toNat .poison

def isPoisonCell (m : ByteMem) (addr : BitVec 64) : Bool :=
  match m.readAt addr.toNat with
  | some .poison => true
  | _ => false

theorem load_store_same (m : ByteMem) (addr : BitVec 64) (w : IntWidth) (v : BitVec w.bits) :
    (m.storeInt addr w v).loadInt addr w = v := by
  simp [storeInt, loadInt, readAt_writeAt_same]

theorem load_store_disjoint (m : ByteMem) (a1 : BitVec 64) (w1 : IntWidth) (v : BitVec w1.bits)
    (a2 : BitVec 64) (w2 : IntWidth)
    (h_disj : rangesDisjoint a1.toNat w1.byteSize a2.toNat w2.byteSize = true) :
    (m.storeInt a1 w1 v).loadInt a2 w2 = m.loadInt a2 w2 := by
  have hor : a1.toNat + w1.byteSize ≤ a2.toNat ∨ a2.toNat + w2.byteSize ≤ a1.toNat :=
    of_decide_eq_true h_disj
  have hne : a1.toNat ≠ a2.toNat := by
    have hpos1 := IntWidth.byteSize_pos w1
    have hpos2 := IntWidth.byteSize_pos w2
    omega
  simp [storeInt, loadInt, readAt_writeAt_ne m a1.toNat a2.toNat (.int w1 v) hne]

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

def zeroBytes (n : Nat) : List (BitVec 8) :=
  List.replicate n 0#8

def effectiveAlign (align : Nat) : Nat :=
  if isPow2 align then align else 1

def allocAligned (m : ByteMem) (sizeBytes align : Nat) : Option (BitVec 64 × ByteMem) :=
  let base := alignUp (Nat.max m.nextAlloc 4096) (effectiveAlign align)
  let span := Nat.max sizeBytes 1
  if base + span < 2 ^ 64 then
    let mZero := m.writeBytesAt base (zeroBytes span)
    some (BitVec.ofNat 64 base, { mZero with nextAlloc := base + span })
  else
    none

theorem allocAligned_nonzero (m : ByteMem) (sz align : Nat) (ptr : BitVec 64) (m' : ByteMem)
    (h_alloc : m.allocAligned sz align = some (ptr, m')) :
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

theorem allocAligned_isAligned (m : ByteMem) (sz align : Nat) (ptr : BitVec 64) (m' : ByteMem)
    (h_pow : isPow2 align = true)
    (h_alloc : m.allocAligned sz align = some (ptr, m')) :
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

end LeanNative.Backend.TargetIR
