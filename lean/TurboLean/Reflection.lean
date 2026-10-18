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
  memoryWords : Nat → Nat := fun _ => 0
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

def getMemoryWord (s : ContractState) (offset : Nat) : Nat :=
  s.memoryWords offset

def setMemoryWord (s : ContractState) (offset : Nat) (v : Nat) : ContractState :=
  { s with memoryWords := fun offset' => if Nat.beq offset' offset then v else s.memoryWords offset' }

def applyMemUpdatesRev (s : ContractState) : List (Nat × Nat) → ContractState
  | [] => s
  | (offset, v) :: rest => setMemoryWord (applyMemUpdatesRev s rest) offset v

def evalMemLookupRev (target : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | (offset, v) :: rest =>
      if Nat.beq target offset then some v
      else evalMemLookupRev target rest

set_option maxHeartbeats 200000 in
  theorem mem_lookup_chain_sound (s : ContractState) (ups : List (Nat × Nat))
      (target : Nat) (val : Nat)
      (h : evalMemLookupRev target ups = some val) :
      getMemoryWord (applyMemUpdatesRev s ups) target = val := by
    induction ups with
    | nil =>
      contradiction
    | cons hd tl ih =>
      rcases hd with ⟨offset, v⟩
      simp only [evalMemLookupRev] at h
      simp only [applyMemUpdatesRev, getMemoryWord, setMemoryWord]
      cases hbeq : Nat.beq target offset
      · simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact ih h
      · simp only [hbeq, ↓reduceIte, Option.some.injEq] at h ⊢
        exact h

set_option maxHeartbeats 200000 in
  theorem mem_lookup_chain_frame_sound (s : ContractState) (ups : List (Nat × Nat))
      (target : Nat)
      (h : evalMemLookupRev target ups = none) :
      getMemoryWord (applyMemUpdatesRev s ups) target = getMemoryWord s target := by
    induction ups with
    | nil =>
      rfl
    | cons hd tl ih =>
      rcases hd with ⟨offset, v⟩
      simp only [evalMemLookupRev] at h
      simp only [applyMemUpdatesRev, getMemoryWord, setMemoryWord]
      cases hbeq : Nat.beq target offset
      · simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact ih h
      · simp only [hbeq, ↓reduceIte] at h
        contradiction

abbrev TransientState := Nat → Nat

def emptyTransient : TransientState := fun _ => 0

def clearTransient (_s : TransientState) : TransientState := emptyTransient

structure StorageUpdate where
  slot : Nat
  val : Nat
  deriving DecidableEq, Repr

def applyTStore (s : Nat → Nat) (slot val : Nat) : Nat → Nat :=
  fun k => if Nat.beq k slot then val else s k

def applyTStoreChain (s : Nat → Nat) : List StorageUpdate → (Nat → Nat)
  | [] => s
  | u :: rest => applyTStore (applyTStoreChain s rest) u.slot u.val

def evalTLoadChain (s : Nat → Nat) : List StorageUpdate → Nat → Nat
  | [], k => s k
  | u :: rest, k => if Nat.beq k u.slot then u.val else evalTLoadChain s rest k

def allSlotsDisjoint : List StorageUpdate → Nat → Bool
  | [], _ => true
  | u :: rest, k => (!Nat.beq k u.slot) && allSlotsDisjoint rest k

set_option maxHeartbeats 200000 in
  theorem tload_chain_sound (s : Nat → Nat) (upds : List StorageUpdate) (k : Nat) :
      evalTLoadChain s upds k = applyTStoreChain s upds k := by
    induction upds with
    | nil =>
      rfl
    | cons u rest ih =>
      simp only [evalTLoadChain, applyTStoreChain, applyTStore]
      cases hbeq : Nat.beq k u.slot
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact ih
      · simp only [↓reduceIte]

set_option maxHeartbeats 200000 in
  theorem tload_chain_frame_sound (s : Nat → Nat) (upds : List StorageUpdate) (k : Nat)
      (h : allSlotsDisjoint upds k = true) :
      applyTStoreChain s upds k = s k := by
    induction upds with
    | nil =>
      rfl
    | cons u rest ih =>
      simp only [allSlotsDisjoint, Bool.and_eq_true, Bool.not_eq_true'] at h
      rcases h with ⟨hneq, hrest⟩
      simp only [applyTStoreChain, applyTStore, hneq, Bool.false_eq_true, ↓reduceIte]
      exact ih hrest

set_option maxHeartbeats 200000 in
  theorem tload_empty_disjoint_zero (upds : List StorageUpdate) (k : Nat)
      (h : allSlotsDisjoint upds k = true) :
      applyTStoreChain (fun _ => 0) upds k = 0 := by
    exact tload_chain_frame_sound (fun _ => 0) upds k h

/-- Models EVM `CALLDATALOAD` over a list of populated `(offset, word)` entries,
    returning `0` for unpopulated offsets beyond `calldatasize`. -/
def getCalldataWord : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (off, v) :: rest, offset =>
      if Nat.beq offset off then v
      else getCalldataWord rest offset

set_option maxHeartbeats 200000 in
  theorem calldata_lookup_sound (entries : List (Nat × Nat)) (offset val : Nat)
      (h : evalMemLookupRev offset entries = some val) :
      getCalldataWord entries offset = val := by
    induction entries with
    | nil =>
      contradiction
    | cons hd tl ih =>
      rcases hd with ⟨off, v⟩
      simp only [evalMemLookupRev] at h
      simp only [getCalldataWord]
      cases hbeq : Nat.beq offset off
      · simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact ih h
      · simp only [hbeq, ↓reduceIte, Option.some.injEq] at h ⊢
        exact h

set_option maxHeartbeats 200000 in
  theorem calldata_miss_zero_sound (entries : List (Nat × Nat)) (offset : Nat)
      (h : evalMemLookupRev offset entries = none) :
      getCalldataWord entries offset = 0 := by
    induction entries with
    | nil =>
      rfl
    | cons hd tl ih =>
      rcases hd with ⟨off, v⟩
      simp only [evalMemLookupRev] at h
      simp only [getCalldataWord]
      cases hbeq : Nat.beq offset off
      · simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact ih h
      · simp only [hbeq, ↓reduceIte] at h
        contradiction

def transferMap (s : ContractState) (slot sender recipient amount : Nat) : ContractState :=
  let balSender := getStorage s (.map slot sender)
  let s1 := setStorage s (.map slot sender) (balSender - amount)
  let balRecipient := getStorage s1 (.map slot recipient)
  setStorage s1 (.map slot recipient) (balRecipient + amount)

set_option maxHeartbeats 200000 in
  theorem transferMap_slot_frame (s : ContractState) (slot sender recipient amount : Nat)
      (k : StorageKey)
      (hSender : StorageKey.fastBeq k (.map slot sender) = false)
      (hRecipient : StorageKey.fastBeq k (.map slot recipient) = false) :
      getStorage (transferMap s slot sender recipient amount) k = getStorage s k := by
    simp only [transferMap, getStorage, setStorage, hSender, hRecipient, Bool.false_eq_true, ↓reduceIte]

set_option maxHeartbeats 200000 in
  theorem transferMap_other_account_frame (s : ContractState) (slot sender recipient observer amount : Nat)
      (hSender : Nat.beq observer sender = false)
      (hRecipient : Nat.beq observer recipient = false) :
      getStorage (transferMap s slot sender recipient amount) (.map slot observer) =
        getStorage s (.map slot observer) := by
    simp only [transferMap, getStorage, setStorage, StorageKey.fastBeq, Nat.beq_refl, Bool.true_and,
      hSender, hRecipient, Bool.false_eq_true, ↓reduceIte]

set_option maxHeartbeats 200000 in
  theorem transferMap_self_preserve (s : ContractState) (slot account amount : Nat)
      (hLe : amount ≤ getStorage s (.map slot account)) :
      getStorage (transferMap s slot account account amount) (.map slot account) =
        getStorage s (.map slot account) := by
    simp only [transferMap, getStorage, setStorage, StorageKey.fastBeq_refl, ↓reduceIte]
    exact Nat.sub_add_cancel hLe

end TurboLean.Reflection
