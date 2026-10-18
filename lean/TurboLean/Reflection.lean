/-
  TurboLean.Reflection: Verified Boolean Reflection & Simp-Normal-Form Primitives
  Zero `sorry`, zero `native_decide`.
  Eliminates quadratic `DecidableEq` proof-term allocation in symbolic state lookup chains.
-/
namespace TurboLean.Reflection

inductive StorageKey where
  | slot (slot : Nat)
  | contractSlot (contract slot : Nat)
  | transient (slot : Nat)
  | addr (slot : Nat)
  | map (slot : Nat) (key : Nat)
  | mapUint (slot : Nat) (key : Nat)
  | map2 (slot : Nat) (key1 key2 : Nat)
  deriving DecidableEq, Repr

/-- Pure boolean equality on `StorageKey` using primitive `Nat.beq`, avoiding proof-term
    construction inside `DecidableEq` during kernel/elaborator `whnf` reduction. -/
def StorageKey.fastBeq : StorageKey → StorageKey → Bool
  | .slot a, .slot b => Nat.beq a b
  | .contractSlot c1 s1, .contractSlot c2 s2 => Nat.beq c1 c2 && Nat.beq s1 s2
  | .transient a, .transient b => Nat.beq a b
  | .addr a, .addr b => Nat.beq a b
  | .map s1 k1, .map s2 k2 => Nat.beq s1 s2 && Nat.beq k1 k2
  | .mapUint s1 k1, .mapUint s2 k2 => Nat.beq s1 s2 && Nat.beq k1 k2
  | .map2 s1 a1 b1, .map2 s2 a2 b2 => Nat.beq s1 s2 && Nat.beq a1 a2 && Nat.beq b1 b2
  | _, _ => false

theorem StorageKey.fastBeq_eq_true_iff (a b : StorageKey) :
    a.fastBeq b = true ↔ a = b := by
  cases a <;> cases b <;>
    simp [StorageKey.fastBeq, Nat.beq_eq, Bool.and_eq_true, and_assoc]

theorem StorageKey.fastBeq_refl (a : StorageKey) : a.fastBeq a = true :=
  (StorageKey.fastBeq_eq_true_iff a a).mpr rfl

instance : BEq StorageKey where
  beq := StorageKey.fastBeq

instance : LawfulBEq StorageKey where
  eq_of_beq := (StorageKey.fastBeq_eq_true_iff _ _).mp
  rfl := StorageKey.fastBeq_refl _

structure ContractState where
  storageWords : StorageKey → Nat
  sender : Nat := 0
  thisAddress : Nat := 0
  msgValue : Nat := 0
  blockTimestamp : Nat := 0

def getStorage (s : ContractState) (k : StorageKey) : Nat :=
  s.storageWords k

def setStorage (s : ContractState) (k : StorageKey) (v : Nat) : ContractState :=
  { s with storageWords := fun k' => if StorageKey.fastBeq k' k then v else s.storageWords k' }

theorem getStorage_setStorage_same {s : ContractState} {k : StorageKey} {v : Nat} :
    getStorage (setStorage s k v) k = v := by
  simp [getStorage, setStorage, StorageKey.fastBeq_refl]

theorem getStorage_setStorage_other {s : ContractState} {k k' : StorageKey} {v : Nat}
    (h : k' ≠ k) :
    getStorage (setStorage s k v) k' = getStorage s k' := by
  unfold getStorage setStorage
  dsimp only
  cases hbeq : StorageKey.fastBeq k' k
  · rfl
  · exfalso
    exact h ((StorageKey.fastBeq_eq_true_iff k' k).mp hbeq)

def applyUpdatesRev (s : ContractState) : List (StorageKey × Nat) → ContractState
  | [] => s
  | (k, v) :: rest => setStorage (applyUpdatesRev s rest) k v

def evalLookupRev (target : StorageKey) : List (StorageKey × Nat) → Option Nat
  | [] => none
  | (k, v) :: rest =>
      if StorageKey.fastBeq target k then some v
      else evalLookupRev target rest

/-- Formal soundness theorem 1: When the reflective evaluator returns `some val`,
    `getStorage` on the updated state is provably equal to `val`. -/
theorem lookup_chain_sound (s : ContractState) (ups : List (StorageKey × Nat))
    (target : StorageKey) (val : Nat)
    (h : evalLookupRev target ups = some val) :
    getStorage (applyUpdatesRev s ups) target = val := by
  induction ups with
  | nil =>
    contradiction
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [evalLookupRev] at h
    simp only [applyUpdatesRev, getStorage, setStorage]
    cases hbeq : StorageKey.fastBeq target k
    · simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact ih h
    · simp only [hbeq, ↓reduceIte, Option.some.injEq] at h ⊢
      exact h

/-- Formal soundness theorem 2: When the reflective evaluator returns `none`,
    `getStorage` on the updated state preserves the original storage value `getStorage s target`. -/
theorem lookup_chain_frame_sound (s : ContractState) (ups : List (StorageKey × Nat))
    (target : StorageKey)
    (h : evalLookupRev target ups = none) :
    getStorage (applyUpdatesRev s ups) target = getStorage s target := by
  induction ups with
  | nil =>
    rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [evalLookupRev] at h
    simp only [applyUpdatesRev, getStorage, setStorage]
    cases hbeq : StorageKey.fastBeq target k
    · simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact ih h
    · simp only [hbeq, ↓reduceIte] at h
      contradiction

theorem getStorage_setStorage_hit (s : ContractState) (k k' : StorageKey) (v : Nat)
    (h : StorageKey.fastBeq k' k = true := by rfl) :
    getStorage (setStorage s k v) k' = v := by
  unfold getStorage setStorage
  dsimp only
  rw [h]
  rfl

theorem getStorage_setStorage_miss (s : ContractState) (k k' : StorageKey) (v : Nat)
    (h : StorageKey.fastBeq k' k = false := by rfl) :
    getStorage (setStorage s k v) k' = getStorage s k' := by
  unfold getStorage setStorage
  dsimp only
  rw [h]
  rfl

end TurboLean.Reflection
