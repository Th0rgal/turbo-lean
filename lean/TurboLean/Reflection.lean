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
    simp only [StorageKey.fastBeq, StorageKey.slot.injEq, StorageKey.contractSlot.injEq,
      StorageKey.transient.injEq, StorageKey.addr.injEq, StorageKey.map.injEq,
      StorageKey.mapUint.injEq, StorageKey.map2.injEq, Nat.beq_eq, Bool.and_eq_true,
      Bool.false_eq_true, and_assoc, reduceCtorEq]

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
      getStorage (transferMap s slot sender recipient amount) k = getStorage s k :=
    (getStorage_setStorage_miss _ _ _ _ hRecipient).trans
      (getStorage_setStorage_miss _ _ _ _ hSender)

set_option maxHeartbeats 200000 in
  theorem transferMap_other_account_frame (s : ContractState) (slot sender recipient observer amount : Nat)
      (hSender : Nat.beq observer sender = false)
      (hRecipient : Nat.beq observer recipient = false) :
      getStorage (transferMap s slot sender recipient amount) (.map slot observer) =
        getStorage s (.map slot observer) :=
    transferMap_slot_frame s slot sender recipient amount (.map slot observer)
      (by dsimp only [StorageKey.fastBeq]; rw [Nat.beq_refl, Bool.true_and, hSender])
      (by dsimp only [StorageKey.fastBeq]; rw [Nat.beq_refl, Bool.true_and, hRecipient])

set_option maxHeartbeats 200000 in
  theorem transferMap_self_preserve (s : ContractState) (slot account amount : Nat)
      (hLe : amount ≤ getStorage s (.map slot account)) :
      getStorage (transferMap s slot account account amount) (.map slot account) =
        getStorage s (.map slot account) :=
    (getStorage_setStorage_same).trans
      ((congrArg (· + amount) getStorage_setStorage_same).trans (Nat.sub_add_cancel hLe))

def approveMap2 (s : ContractState) (slot owner spender amount : Nat) : ContractState :=
  setStorage s (.map2 slot owner spender) amount

set_option maxHeartbeats 200000 in
  theorem approveMap2_hit (s : ContractState) (slot owner spender amount : Nat) :
      getStorage (approveMap2 s slot owner spender amount) (.map2 slot owner spender) = amount :=
    getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem approveMap2_other_owner_frame (s : ContractState) (slot owner otherOwner spender otherSpender amount : Nat)
      (h : Nat.beq otherOwner owner = false) :
      getStorage (approveMap2 s slot owner spender amount) (.map2 slot otherOwner otherSpender) =
        getStorage s (.map2 slot otherOwner otherSpender) :=
    getStorage_setStorage_miss s (.map2 slot owner spender) (.map2 slot otherOwner otherSpender) amount
      (by dsimp only [StorageKey.fastBeq]; rw [Nat.beq_refl, Bool.true_and, h, Bool.false_and])

set_option maxHeartbeats 200000 in
  theorem approveMap2_other_spender_frame (s : ContractState) (slot owner otherOwner spender otherSpender amount : Nat)
      (h : Nat.beq otherSpender spender = false) :
      getStorage (approveMap2 s slot owner spender amount) (.map2 slot otherOwner otherSpender) =
        getStorage s (.map2 slot otherOwner otherSpender) :=
    getStorage_setStorage_miss s (.map2 slot owner spender) (.map2 slot otherOwner otherSpender) amount
      (by dsimp only [StorageKey.fastBeq]; rw [Nat.beq_refl, Bool.true_and, h, Bool.and_false])

def getContractStorage (s : ContractState) (contract slot : Nat) : Nat :=
  getStorage s (.contractSlot contract slot)

def setContractStorage (s : ContractState) (contract slot val : Nat) : ContractState :=
  setStorage s (.contractSlot contract slot) val

set_option maxHeartbeats 200000 in
  theorem getContractStorage_setContractStorage_same (s : ContractState) (contract slot val : Nat) :
      getContractStorage (setContractStorage s contract slot val) contract slot = val :=
    getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem getContractStorage_other_contract_frame (s : ContractState) (c1 c2 s1 s2 val : Nat)
      (h : Nat.beq c2 c1 = false) :
      getContractStorage (setContractStorage s c1 s1 val) c2 s2 = getContractStorage s c2 s2 :=
    getStorage_setStorage_miss s (.contractSlot c1 s1) (.contractSlot c2 s2) val
      (by dsimp only [StorageKey.fastBeq]; rw [h, Bool.false_and])

set_option maxHeartbeats 200000 in
  theorem getContractStorage_other_slot_frame (s : ContractState) (c1 c2 s1 s2 val : Nat)
      (h : Nat.beq s2 s1 = false) :
      getContractStorage (setContractStorage s c1 s1 val) c2 s2 = getContractStorage s c2 s2 :=
    getStorage_setStorage_miss s (.contractSlot c1 s1) (.contractSlot c2 s2) val
      (by dsimp only [StorageKey.fastBeq]; rw [h, Bool.and_false])

def spendAllowanceMap2 (s : ContractState) (slot owner spender amount : Nat) : ContractState :=
  setStorage s (.map2 slot owner spender) (getStorage s (.map2 slot owner spender) - amount)

set_option maxHeartbeats 200000 in
  theorem spendAllowanceMap2_exact (s : ContractState) (slot owner spender amount : Nat) :
      getStorage (spendAllowanceMap2 s slot owner spender amount) (.map2 slot owner spender) =
        getStorage s (.map2 slot owner spender) - amount :=
    getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem spendAllowanceMap2_full_zero (s : ContractState) (slot owner spender : Nat) :
      getStorage (spendAllowanceMap2 s slot owner spender (getStorage s (.map2 slot owner spender)))
        (.map2 slot owner spender) = 0 :=
    (getStorage_setStorage_same).trans (Nat.sub_self _)

set_option maxHeartbeats 200000 in
  theorem approve_then_spendAllowance_exact (s : ContractState) (slot owner spender approved spent : Nat) :
      getStorage (spendAllowanceMap2 (approveMap2 s slot owner spender approved) slot owner spender spent)
        (.map2 slot owner spender) = approved - spent :=
    (getStorage_setStorage_same).trans (congrArg (· - spent) getStorage_setStorage_same)

def mintMap (s : ContractState) (slot recipient amount : Nat) : ContractState :=
  setStorage s (.map slot recipient) (getStorage s (.map slot recipient) + amount)

def burnMap (s : ContractState) (slot holder amount : Nat) : ContractState :=
  setStorage s (.map slot holder) (getStorage s (.map slot holder) - amount)

set_option maxHeartbeats 200000 in
  theorem mintMap_slot_frame (s : ContractState) (slot recipient amount : Nat)
      (k : StorageKey)
      (h : StorageKey.fastBeq k (.map slot recipient) = false) :
      getStorage (mintMap s slot recipient amount) k = getStorage s k :=
    getStorage_setStorage_miss _ _ _ _ h

set_option maxHeartbeats 200000 in
  theorem burnMap_slot_frame (s : ContractState) (slot holder amount : Nat)
      (k : StorageKey)
      (h : StorageKey.fastBeq k (.map slot holder) = false) :
      getStorage (burnMap s slot holder amount) k = getStorage s k :=
    getStorage_setStorage_miss _ _ _ _ h

set_option maxHeartbeats 200000 in
  theorem mintMap_other_account_frame (s : ContractState) (slot recipient observer amount : Nat)
      (h : Nat.beq observer recipient = false) :
      getStorage (mintMap s slot recipient amount) (.map slot observer) =
        getStorage s (.map slot observer) :=
    getStorage_setStorage_miss s (.map slot recipient) (.map slot observer) _
      (by dsimp only [StorageKey.fastBeq]; rw [Nat.beq_refl, Bool.true_and, h])

set_option maxHeartbeats 200000 in
  theorem burnMap_other_account_frame (s : ContractState) (slot holder observer amount : Nat)
      (h : Nat.beq observer holder = false) :
      getStorage (burnMap s slot holder amount) (.map slot observer) =
        getStorage s (.map slot observer) :=
    getStorage_setStorage_miss s (.map slot holder) (.map slot observer) _
      (by dsimp only [StorageKey.fastBeq]; rw [Nat.beq_refl, Bool.true_and, h])

set_option maxHeartbeats 200000 in
  theorem mint_then_burn_exact (s : ContractState) (slot account amount : Nat) :
      getStorage (burnMap (mintMap s slot account amount) slot account amount) (.map slot account) =
        getStorage s (.map slot account) :=
    (getStorage_setStorage_same).trans
      ((congrArg (· - amount) getStorage_setStorage_same).trans (Nat.add_sub_cancel _ _))

def batchTransferMap (s : ContractState) (slot fromAcc to1 to2 amt1 amt2 : Nat) : ContractState :=
  transferMap (transferMap s slot fromAcc to1 amt1) slot fromAcc to2 amt2

set_option maxHeartbeats 200000 in
  theorem batchTransferMap_slot_frame (s : ContractState) (slot fromAcc to1 to2 amt1 amt2 : Nat)
      (k : StorageKey)
      (hFrom : StorageKey.fastBeq k (.map slot fromAcc) = false)
      (hTo1 : StorageKey.fastBeq k (.map slot to1) = false)
      (hTo2 : StorageKey.fastBeq k (.map slot to2) = false) :
      getStorage (batchTransferMap s slot fromAcc to1 to2 amt1 amt2) k = getStorage s k :=
    (transferMap_slot_frame _ slot fromAcc to2 amt2 k hFrom hTo2).trans
      (transferMap_slot_frame s slot fromAcc to1 amt1 k hFrom hTo1)

set_option maxHeartbeats 200000 in
  theorem batchTransferMap_other_account_frame (s : ContractState)
      (slot fromAcc to1 to2 observer amt1 amt2 : Nat)
      (hFrom : Nat.beq observer fromAcc = false)
      (hTo1 : Nat.beq observer to1 = false)
      (hTo2 : Nat.beq observer to2 = false) :
      getStorage (batchTransferMap s slot fromAcc to1 to2 amt1 amt2) (.map slot observer) =
        getStorage s (.map slot observer) :=
    (transferMap_other_account_frame _ slot fromAcc to2 observer amt2 hFrom hTo2).trans
      (transferMap_other_account_frame s slot fromAcc to1 observer amt1 hFrom hTo1)

set_option maxHeartbeats 200000 in
  theorem batchTransferMap_self_both_preserve (s : ContractState) (slot account amt1 amt2 : Nat)
      (hLe1 : amt1 ≤ getStorage s (.map slot account))
      (hLe2 : amt2 ≤ getStorage s (.map slot account)) :
      getStorage (batchTransferMap s slot account account account amt1 amt2) (.map slot account) =
        getStorage s (.map slot account) :=
    let h1 := transferMap_self_preserve s slot account amt1 hLe1
    (transferMap_self_preserve (transferMap s slot account account amt1) slot account amt2 (h1.symm ▸ hLe2)).trans h1

def acquireTransientLock (s : ContractState) (lockSlot : Nat) : ContractState :=
  setStorage s (.transient lockSlot) 1

def releaseTransientLock (s : ContractState) (lockSlot : Nat) : ContractState :=
  setStorage s (.transient lockSlot) 0

def isTransientLocked (s : ContractState) (lockSlot : Nat) : Bool :=
  Nat.beq (getStorage s (.transient lockSlot)) 1

set_option maxHeartbeats 200000 in
  theorem acquireTransientLock_locked (s : ContractState) (lockSlot : Nat) :
      isTransientLocked (acquireTransientLock s lockSlot) lockSlot = true :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem acquire_then_release_unlocked (s : ContractState) (lockSlot : Nat) :
      isTransientLocked (releaseTransientLock (acquireTransientLock s lockSlot) lockSlot) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem acquireTransientLock_other_slot_frame (s : ContractState) (lockSlot otherSlot : Nat)
      (h : Nat.beq otherSlot lockSlot = false) :
      getStorage (acquireTransientLock s lockSlot) (.transient otherSlot) =
        getStorage s (.transient otherSlot) :=
    getStorage_setStorage_miss s (.transient lockSlot) (.transient otherSlot) 1 h

set_option maxHeartbeats 200000 in
  theorem acquireTransientLock_preserves_storage (s : ContractState) (lockSlot persistentSlot : Nat) :
      getStorage (acquireTransientLock s lockSlot) (.slot persistentSlot) =
        getStorage s (.slot persistentSlot) :=
    getStorage_setStorage_miss s (.transient lockSlot) (.slot persistentSlot) 1 rfl

def escrowDeposit (s : ContractState) (contract slot owner spender amount : Nat) : ContractState :=
  approveMap2 (setContractStorage s contract slot amount) slot owner spender amount

set_option maxHeartbeats 200000 in
  theorem escrowDeposit_allowance_hit (s : ContractState) (contract slot owner spender amount : Nat) :
      getStorage (escrowDeposit s contract slot owner spender amount) (.map2 slot owner spender) = amount :=
    getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem escrowDeposit_contract_hit (s : ContractState) (contract slot owner spender amount : Nat) :
      getContractStorage (escrowDeposit s contract slot owner spender amount) contract slot = amount :=
    (getStorage_setStorage_miss _ (.map2 slot owner spender) (.contractSlot contract slot) amount rfl).trans
      getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem escrowDeposit_other_contract_frame (s : ContractState)
      (c1 c2 slot s2 owner spender amount : Nat)
      (h : Nat.beq c2 c1 = false) :
      getContractStorage (escrowDeposit s c1 slot owner spender amount) c2 s2 =
        getContractStorage s c2 s2 :=
    (getStorage_setStorage_miss _ (.map2 slot owner spender) (.contractSlot c2 s2) amount rfl).trans
      (getContractStorage_other_contract_frame s c1 c2 slot s2 amount h)

set_option maxHeartbeats 200000 in
  theorem escrowDeposit_preserves_transient (s : ContractState)
      (contract slot owner spender amount tslot : Nat) :
      getStorage (escrowDeposit s contract slot owner spender amount) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (getStorage_setStorage_miss _ (.map2 slot owner spender) (.transient tslot) amount rfl).trans
      (getStorage_setStorage_miss s (.contractSlot contract slot) (.transient tslot) amount rfl)

def guardedTransferMap (s : ContractState) (lockSlot balSlot fromAcc toAcc amount : Nat) : ContractState :=
  releaseTransientLock (transferMap (acquireTransientLock s lockSlot) balSlot fromAcc toAcc amount) lockSlot

set_option maxHeartbeats 200000 in
  theorem guardedTransferMap_unlocked_after (s : ContractState)
      (lockSlot balSlot fromAcc toAcc amount : Nat) :
      isTransientLocked (guardedTransferMap s lockSlot balSlot fromAcc toAcc amount) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem guardedTransferMap_slot_frame (s : ContractState)
      (lockSlot balSlot fromAcc toAcc amount persistentSlot : Nat) :
      getStorage (guardedTransferMap s lockSlot balSlot fromAcc toAcc amount) (.slot persistentSlot) =
        getStorage s (.slot persistentSlot) :=
    (getStorage_setStorage_miss _ (.transient lockSlot) (.slot persistentSlot) 0 rfl).trans <|
      (transferMap_slot_frame _ balSlot fromAcc toAcc amount (.slot persistentSlot) rfl rfl).trans
        (getStorage_setStorage_miss s (.transient lockSlot) (.slot persistentSlot) 1 rfl)

set_option maxHeartbeats 200000 in
  theorem guardedTransferMap_other_account_frame (s : ContractState)
      (lockSlot balSlot fromAcc toAcc observer amount : Nat)
      (hFrom : Nat.beq observer fromAcc = false)
      (hTo : Nat.beq observer toAcc = false) :
      getStorage (guardedTransferMap s lockSlot balSlot fromAcc toAcc amount) (.map balSlot observer) =
        getStorage s (.map balSlot observer) :=
    (getStorage_setStorage_miss _ (.transient lockSlot) (.map balSlot observer) 0 rfl).trans <|
      (transferMap_other_account_frame _ balSlot fromAcc toAcc observer amount hFrom hTo).trans
        (getStorage_setStorage_miss s (.transient lockSlot) (.map balSlot observer) 1 rfl)

set_option maxHeartbeats 200000 in
  theorem guardedTransferMap_self_preserve (s : ContractState)
      (lockSlot balSlot account amount : Nat)
      (hLe : amount ≤ getStorage s (.map balSlot account)) :
      getStorage (guardedTransferMap s lockSlot balSlot account account amount) (.map balSlot account) =
        getStorage s (.map balSlot account) :=
    let hAcq := getStorage_setStorage_miss s (.transient lockSlot) (.map balSlot account) 1 rfl
    (getStorage_setStorage_miss _ (.transient lockSlot) (.map balSlot account) 0 rfl).trans <|
      (transferMap_self_preserve (acquireTransientLock s lockSlot) balSlot account amount (hAcq.symm ▸ hLe)).trans
        hAcq

def atomicSwapMap (s : ContractState) (slotA slotB alice bob amtA amtB : Nat) : ContractState :=
  transferMap (transferMap s slotA alice bob amtA) slotB bob alice amtB

set_option maxHeartbeats 200000 in
  theorem atomicSwapMap_other_slot_frame (s : ContractState)
      (slotA slotB otherSlot alice bob account amtA amtB : Nat)
      (hA : Nat.beq otherSlot slotA = false)
      (hB : Nat.beq otherSlot slotB = false) :
      getStorage (atomicSwapMap s slotA slotB alice bob amtA amtB) (.map otherSlot account) =
        getStorage s (.map otherSlot account) :=
    (transferMap_slot_frame _ slotB bob alice amtB (.map otherSlot account)
      ((congrArg (· && account.beq bob) hB).trans (Bool.false_and _))
      ((congrArg (· && account.beq alice) hB).trans (Bool.false_and _))).trans
      (transferMap_slot_frame s slotA alice bob amtA (.map otherSlot account)
        ((congrArg (· && account.beq alice) hA).trans (Bool.false_and _))
        ((congrArg (· && account.beq bob) hA).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem atomicSwapMap_other_account_frame (s : ContractState)
      (slot alice bob observer amtA amtB : Nat)
      (hAlice : Nat.beq observer alice = false)
      (hBob : Nat.beq observer bob = false) :
      getStorage (atomicSwapMap s slot slot alice bob amtA amtB) (.map slot observer) =
        getStorage s (.map slot observer) :=
    (transferMap_other_account_frame _ slot bob alice observer amtB hBob hAlice).trans
      (transferMap_other_account_frame s slot alice bob observer amtA hAlice hBob)

set_option maxHeartbeats 200000 in
  theorem atomicSwapMap_preserves_transient (s : ContractState)
      (slotA slotB alice bob amtA amtB tslot : Nat) :
      getStorage (atomicSwapMap s slotA slotB alice bob amtA amtB) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (transferMap_slot_frame _ slotB bob alice amtB (.transient tslot) rfl rfl).trans
      (transferMap_slot_frame s slotA alice bob amtA (.transient tslot) rfl rfl)

set_option maxHeartbeats 200000 in
  theorem atomicSwapMap_self_both_preserve (s : ContractState)
      (slotA slotB account amtA amtB : Nat)
      (hLeA : amtA ≤ getStorage s (.map slotA account))
      (hLeB : amtB ≤ getStorage (transferMap s slotA account account amtA) (.map slotB account)) :
      getStorage (atomicSwapMap s slotA slotB account account amtA amtB) (.map slotB account) =
        getStorage (transferMap s slotA account account amtA) (.map slotB account) ∧
      getStorage (transferMap s slotA account account amtA) (.map slotA account) =
        getStorage s (.map slotA account) :=
    ⟨transferMap_self_preserve (transferMap s slotA account account amtA) slotB account amtB hLeB,
     transferMap_self_preserve s slotA account amtA hLeA⟩

  def guardedAtomicSwapMap (s : ContractState) (lockSlot slotA slotB alice bob amtA amtB : Nat) : ContractState :=
    releaseTransientLock (atomicSwapMap (acquireTransientLock s lockSlot) slotA slotB alice bob amtA amtB) lockSlot

set_option maxHeartbeats 200000 in
  theorem guardedAtomicSwapMap_unlocked_after (s : ContractState)
      (lockSlot slotA slotB alice bob amtA amtB : Nat) :
      isTransientLocked (guardedAtomicSwapMap s lockSlot slotA slotB alice bob amtA amtB) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem guardedAtomicSwapMap_other_slot_frame (s : ContractState)
      (lockSlot slotA slotB otherSlot alice bob account amtA amtB : Nat)
      (hA : Nat.beq otherSlot slotA = false)
      (hB : Nat.beq otherSlot slotB = false) :
      getStorage (guardedAtomicSwapMap s lockSlot slotA slotB alice bob amtA amtB) (.map otherSlot account) =
        getStorage s (.map otherSlot account) :=
    (getStorage_setStorage_miss _ (.transient lockSlot) (.map otherSlot account) 0 rfl).trans <|
      (atomicSwapMap_other_slot_frame _ slotA slotB otherSlot alice bob account amtA amtB hA hB).trans
        (getStorage_setStorage_miss s (.transient lockSlot) (.map otherSlot account) 1 rfl)

set_option maxHeartbeats 200000 in
  theorem guardedAtomicSwapMap_other_account_frame (s : ContractState)
      (lockSlot slot alice bob observer amtA amtB : Nat)
      (hAlice : Nat.beq observer alice = false)
      (hBob : Nat.beq observer bob = false) :
      getStorage (guardedAtomicSwapMap s lockSlot slot slot alice bob amtA amtB) (.map slot observer) =
        getStorage s (.map slot observer) :=
    (getStorage_setStorage_miss _ (.transient lockSlot) (.map slot observer) 0 rfl).trans <|
      (atomicSwapMap_other_account_frame _ slot alice bob observer amtA amtB hAlice hBob).trans
        (getStorage_setStorage_miss s (.transient lockSlot) (.map slot observer) 1 rfl)

set_option maxHeartbeats 200000 in
  theorem guardedAtomicSwapMap_self_both_preserve (s : ContractState)
      (lockSlot slot account amtA amtB : Nat)
      (hLeA : amtA ≤ getStorage s (.map slot account))
      (hLeB : amtB ≤ getStorage s (.map slot account)) :
      getStorage (guardedAtomicSwapMap s lockSlot slot slot account account amtA amtB) (.map slot account) =
        getStorage s (.map slot account) :=
    let hAcq := getStorage_setStorage_miss s (.transient lockSlot) (.map slot account) 1 rfl
    let hStep1 := (transferMap_self_preserve (acquireTransientLock s lockSlot) slot account amtA (hAcq.symm ▸ hLeA)).trans hAcq
    (getStorage_setStorage_miss _ (.transient lockSlot) (.map slot account) 0 rfl).trans <|
      (transferMap_self_preserve (transferMap (acquireTransientLock s lockSlot) slot account account amtA) slot account amtB (hStep1.symm ▸ hLeB)).trans
        hStep1

  def flashMintBurnMap (s : ContractState) (balSlot borrower amount : Nat) : ContractState :=
    burnMap (mintMap s balSlot borrower amount) balSlot borrower amount

  def guardedFlashMintBurnMap (s : ContractState) (lockSlot balSlot borrower amount : Nat) : ContractState :=
    releaseTransientLock (flashMintBurnMap (acquireTransientLock s lockSlot) balSlot borrower amount) lockSlot

set_option maxHeartbeats 200000 in
  theorem flashMintBurnMap_borrower_restore (s : ContractState)
      (balSlot borrower amount : Nat) :
      getStorage (flashMintBurnMap s balSlot borrower amount) (.map balSlot borrower) =
        getStorage s (.map balSlot borrower) :=
    mint_then_burn_exact s balSlot borrower amount

set_option maxHeartbeats 200000 in
  theorem flashMintBurnMap_other_slot_frame (s : ContractState)
      (balSlot otherSlot borrower account amount : Nat)
      (h : Nat.beq otherSlot balSlot = false) :
      getStorage (flashMintBurnMap s balSlot borrower amount) (.map otherSlot account) =
        getStorage s (.map otherSlot account) :=
    let hMiss : StorageKey.fastBeq (.map otherSlot account) (.map balSlot borrower) = false :=
      (congrArg (· && account.beq borrower) h).trans (Bool.false_and _)
    (burnMap_slot_frame _ balSlot borrower amount (.map otherSlot account) hMiss).trans
      (mintMap_slot_frame s balSlot borrower amount (.map otherSlot account) hMiss)

set_option maxHeartbeats 200000 in
  theorem flashMintBurnMap_other_account_frame (s : ContractState)
      (balSlot borrower observer amount : Nat)
      (h : Nat.beq observer borrower = false) :
      getStorage (flashMintBurnMap s balSlot borrower amount) (.map balSlot observer) =
        getStorage s (.map balSlot observer) :=
    (burnMap_other_account_frame _ balSlot borrower observer amount h).trans
      (mintMap_other_account_frame s balSlot borrower observer amount h)

set_option maxHeartbeats 200000 in
  theorem guardedFlashMintBurnMap_borrower_restore (s : ContractState)
      (lockSlot balSlot borrower amount : Nat) :
      getStorage (guardedFlashMintBurnMap s lockSlot balSlot borrower amount) (.map balSlot borrower) =
        getStorage s (.map balSlot borrower) :=
    (getStorage_setStorage_miss _ (.transient lockSlot) (.map balSlot borrower) 0 rfl).trans <|
      (flashMintBurnMap_borrower_restore _ balSlot borrower amount).trans
        (getStorage_setStorage_miss s (.transient lockSlot) (.map balSlot borrower) 1 rfl)

  def releaseEscrowMap2 (s : ContractState) (allowSlot balSlot owner spender recipient amount : Nat) : ContractState :=
    transferMap (spendAllowanceMap2 s allowSlot owner spender amount) balSlot owner recipient amount

set_option maxHeartbeats 200000 in
  theorem releaseEscrowMap2_other_slot_frame (s : ContractState)
      (allowSlot balSlot otherSlot owner spender recipient account amount : Nat)
      (h : Nat.beq otherSlot balSlot = false) :
      getStorage (releaseEscrowMap2 s allowSlot balSlot owner spender recipient amount) (.map otherSlot account) =
        getStorage s (.map otherSlot account) :=
    (transferMap_slot_frame _ balSlot owner recipient amount (.map otherSlot account)
      ((congrArg (· && account.beq owner) h).trans (Bool.false_and _))
      ((congrArg (· && account.beq recipient) h).trans (Bool.false_and _))).trans
      (getStorage_setStorage_miss s (.map2 allowSlot owner spender) (.map otherSlot account) _ rfl)

set_option maxHeartbeats 200000 in
  theorem releaseEscrowMap2_other_owner_allowance_frame (s : ContractState)
      (allowSlot balSlot owner otherOwner spender otherSpender recipient amount : Nat)
      (h : Nat.beq otherOwner owner = false) :
      getStorage (releaseEscrowMap2 s allowSlot balSlot owner spender recipient amount) (.map2 allowSlot otherOwner otherSpender) =
        getStorage s (.map2 allowSlot otherOwner otherSpender) :=
    (transferMap_slot_frame _ balSlot owner recipient amount (.map2 allowSlot otherOwner otherSpender) rfl rfl).trans
      (approveMap2_other_owner_frame s allowSlot owner otherOwner spender otherSpender _ h)

set_option maxHeartbeats 200000 in
  theorem releaseEscrowMap2_preserves_transient (s : ContractState)
      (allowSlot balSlot owner spender recipient amount tslot : Nat) :
      getStorage (releaseEscrowMap2 s allowSlot balSlot owner spender recipient amount) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (transferMap_slot_frame _ balSlot owner recipient amount (.transient tslot) rfl rfl).trans
      (getStorage_setStorage_miss s (.map2 allowSlot owner spender) (.transient tslot) _ rfl)

set_option maxHeartbeats 200000 in
  theorem approve_then_releaseEscrowMap2_exact_allowance (s : ContractState)
      (allowSlot balSlot owner spender recipient approved spent : Nat) :
      getStorage (releaseEscrowMap2 (approveMap2 s allowSlot owner spender approved) allowSlot balSlot owner spender recipient spent)
        (.map2 allowSlot owner spender) = approved - spent :=
    (transferMap_slot_frame _ balSlot owner recipient spent (.map2 allowSlot owner spender) rfl rfl).trans
      (approve_then_spendAllowance_exact s allowSlot owner spender approved spent)

  def guardedReleaseEscrowMap2 (s : ContractState)
      (lockSlot allowSlot balSlot owner spender recipient amount : Nat) : ContractState :=
    releaseTransientLock (releaseEscrowMap2 (acquireTransientLock s lockSlot) allowSlot balSlot owner spender recipient amount) lockSlot

set_option maxHeartbeats 200000 in
  theorem guardedReleaseEscrowMap2_unlocked_after (s : ContractState)
      (lockSlot allowSlot balSlot owner spender recipient amount : Nat) :
      isTransientLocked (guardedReleaseEscrowMap2 s lockSlot allowSlot balSlot owner spender recipient amount) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem guardedReleaseEscrowMap2_other_slot_frame (s : ContractState)
      (lockSlot allowSlot balSlot otherSlot owner spender recipient account amount : Nat)
      (h : Nat.beq otherSlot balSlot = false) :
      getStorage (guardedReleaseEscrowMap2 s lockSlot allowSlot balSlot owner spender recipient amount) (.map otherSlot account) =
        getStorage s (.map otherSlot account) :=
    (getStorage_setStorage_miss _ (.transient lockSlot) (.map otherSlot account) 0 rfl).trans <|
      (releaseEscrowMap2_other_slot_frame _ allowSlot balSlot otherSlot owner spender recipient account amount h).trans
        (getStorage_setStorage_miss s (.transient lockSlot) (.map otherSlot account) 1 rfl)

set_option maxHeartbeats 200000 in
  theorem guardedReleaseEscrowMap2_other_owner_allowance_frame (s : ContractState)
      (lockSlot allowSlot balSlot owner otherOwner spender otherSpender recipient amount : Nat)
      (h : Nat.beq otherOwner owner = false) :
      getStorage (guardedReleaseEscrowMap2 s lockSlot allowSlot balSlot owner spender recipient amount) (.map2 allowSlot otherOwner otherSpender) =
        getStorage s (.map2 allowSlot otherOwner otherSpender) :=
    (getStorage_setStorage_miss _ (.transient lockSlot) (.map2 allowSlot otherOwner otherSpender) 0 rfl).trans <|
      (releaseEscrowMap2_other_owner_allowance_frame _ allowSlot balSlot owner otherOwner spender otherSpender recipient amount h).trans
        (getStorage_setStorage_miss s (.transient lockSlot) (.map2 allowSlot otherOwner otherSpender) 1 rfl)

set_option maxHeartbeats 200000 in
  theorem approve_then_guardedReleaseEscrowMap2_exact_allowance (s : ContractState)
      (lockSlot allowSlot balSlot owner spender recipient approved spent : Nat) :
      getStorage (guardedReleaseEscrowMap2 (approveMap2 s allowSlot owner spender approved) lockSlot allowSlot balSlot owner spender recipient spent)
        (.map2 allowSlot owner spender) = approved - spent :=
    (getStorage_setStorage_miss _ (.transient lockSlot) (.map2 allowSlot owner spender) 0 rfl).trans <|
      (transferMap_slot_frame _ balSlot owner recipient spent (.map2 allowSlot owner spender) rfl rfl).trans <|
      (getStorage_setStorage_same).trans
        (congrArg (· - spent)
          ((getStorage_setStorage_miss _ (.transient lockSlot) (.map2 allowSlot owner spender) 1 rfl).trans
            getStorage_setStorage_same))

  def feeTransferMap (s : ContractState)
      (balSlot sender recipient treasury netAmount feeAmount : Nat) : ContractState :=
    batchTransferMap s balSlot sender recipient treasury netAmount feeAmount

  def guardedFeeTransferMap (s : ContractState)
      (lockSlot balSlot sender recipient treasury netAmount feeAmount : Nat) : ContractState :=
    releaseTransientLock
      (feeTransferMap (acquireTransientLock s lockSlot) balSlot sender recipient treasury netAmount feeAmount)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem feeTransferMap_other_slot_frame (s : ContractState)
      (balSlot otherSlot sender recipient treasury account netAmount feeAmount : Nat)
      (h : Nat.beq otherSlot balSlot = false) :
      getStorage (feeTransferMap s balSlot sender recipient treasury netAmount feeAmount) (.map otherSlot account) =
        getStorage s (.map otherSlot account) :=
    batchTransferMap_slot_frame s balSlot sender recipient treasury netAmount feeAmount (.map otherSlot account)
      ((congrArg (· && account.beq sender) h).trans (Bool.false_and _))
      ((congrArg (· && account.beq recipient) h).trans (Bool.false_and _))
      ((congrArg (· && account.beq treasury) h).trans (Bool.false_and _))

set_option maxHeartbeats 200000 in
  theorem feeTransferMap_other_account_frame (s : ContractState)
      (balSlot sender recipient treasury observer netAmount feeAmount : Nat)
      (hSender : Nat.beq observer sender = false)
      (hRecipient : Nat.beq observer recipient = false)
      (hTreasury : Nat.beq observer treasury = false) :
      getStorage (feeTransferMap s balSlot sender recipient treasury netAmount feeAmount) (.map balSlot observer) =
        getStorage s (.map balSlot observer) :=
    batchTransferMap_other_account_frame s balSlot sender recipient treasury observer netAmount feeAmount
      hSender hRecipient hTreasury

set_option maxHeartbeats 200000 in
  theorem feeTransferMap_self_all_preserve (s : ContractState)
      (balSlot account netAmount feeAmount : Nat)
      (hLeNet : netAmount ≤ getStorage s (.map balSlot account))
      (hLeFee : feeAmount ≤ getStorage s (.map balSlot account)) :
      getStorage (feeTransferMap s balSlot account account account netAmount feeAmount) (.map balSlot account) =
        getStorage s (.map balSlot account) :=
    batchTransferMap_self_both_preserve s balSlot account netAmount feeAmount hLeNet hLeFee

set_option maxHeartbeats 200000 in
  theorem guardedFeeTransferMap_unlocked_after (s : ContractState)
      (lockSlot balSlot sender recipient treasury netAmount feeAmount : Nat) :
      isTransientLocked (guardedFeeTransferMap s lockSlot balSlot sender recipient treasury netAmount feeAmount) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def burnFeeTransferMap (s : ContractState)
      (balSlot sender recipient netAmount burnAmount : Nat) : ContractState :=
    burnMap (transferMap s balSlot sender recipient netAmount) balSlot sender burnAmount

  def guardedBurnFeeTransferMap (s : ContractState)
      (lockSlot balSlot sender recipient netAmount burnAmount : Nat) : ContractState :=
    releaseTransientLock
      (burnFeeTransferMap (acquireTransientLock s lockSlot) balSlot sender recipient netAmount burnAmount)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem burnFeeTransferMap_other_slot_frame (s : ContractState)
      (balSlot otherSlot sender recipient account netAmount burnAmount : Nat)
      (h : Nat.beq otherSlot balSlot = false) :
      getStorage (burnFeeTransferMap s balSlot sender recipient netAmount burnAmount) (.map otherSlot account) =
        getStorage s (.map otherSlot account) :=
    let hSender : StorageKey.fastBeq (.map otherSlot account) (.map balSlot sender) = false :=
      (congrArg (· && account.beq sender) h).trans (Bool.false_and _)
    let hRecipient : StorageKey.fastBeq (.map otherSlot account) (.map balSlot recipient) = false :=
      (congrArg (· && account.beq recipient) h).trans (Bool.false_and _)
    (burnMap_slot_frame _ balSlot sender burnAmount (.map otherSlot account) hSender).trans
      (transferMap_slot_frame s balSlot sender recipient netAmount (.map otherSlot account) hSender hRecipient)

set_option maxHeartbeats 200000 in
  theorem burnFeeTransferMap_other_account_frame (s : ContractState)
      (balSlot sender recipient observer netAmount burnAmount : Nat)
      (hSender : Nat.beq observer sender = false)
      (hRecipient : Nat.beq observer recipient = false) :
      getStorage (burnFeeTransferMap s balSlot sender recipient netAmount burnAmount) (.map balSlot observer) =
        getStorage s (.map balSlot observer) :=
    (burnMap_other_account_frame _ balSlot sender observer burnAmount hSender).trans
      (transferMap_other_account_frame s balSlot sender recipient observer netAmount hSender hRecipient)

set_option maxHeartbeats 200000 in
  theorem burnFeeTransferMap_preserves_transient (s : ContractState)
      (balSlot sender recipient netAmount burnAmount tslot : Nat) :
      getStorage (burnFeeTransferMap s balSlot sender recipient netAmount burnAmount) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (burnMap_slot_frame _ balSlot sender burnAmount (.transient tslot) rfl).trans
      (transferMap_slot_frame s balSlot sender recipient netAmount (.transient tslot) rfl rfl)

set_option maxHeartbeats 200000 in
  theorem guardedBurnFeeTransferMap_unlocked_after (s : ContractState)
      (lockSlot balSlot sender recipient netAmount burnAmount : Nat) :
      isTransientLocked (guardedBurnFeeTransferMap s lockSlot balSlot sender recipient netAmount burnAmount) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem guardedBurnFeeTransferMap_other_slot_frame (s : ContractState)
      (lockSlot balSlot otherSlot sender recipient account netAmount burnAmount : Nat)
      (h : Nat.beq otherSlot balSlot = false) :
      getStorage (guardedBurnFeeTransferMap s lockSlot balSlot sender recipient netAmount burnAmount) (.map otherSlot account) =
        getStorage s (.map otherSlot account) :=
    (getStorage_setStorage_miss _ (.transient lockSlot) (.map otherSlot account) 0 rfl).trans <|
      (burnFeeTransferMap_other_slot_frame _ balSlot otherSlot sender recipient account netAmount burnAmount h).trans
        (getStorage_setStorage_miss s (.transient lockSlot) (.map otherSlot account) 1 rfl)

  def stakeDepositMap (s : ContractState)
      (assetSlot shareSlot user vault amount shares : Nat) : ContractState :=
    mintMap (transferMap s assetSlot user vault amount) shareSlot user shares

  def stakeWithdrawMap (s : ContractState)
      (assetSlot shareSlot user vault amount shares : Nat) : ContractState :=
    transferMap (burnMap s shareSlot user shares) assetSlot vault user amount

  def guardedStakeDepositMap (s : ContractState)
      (lockSlot assetSlot shareSlot user vault amount shares : Nat) : ContractState :=
    releaseTransientLock
      (stakeDepositMap (acquireTransientLock s lockSlot) assetSlot shareSlot user vault amount shares)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem stakeDepositMap_other_slot_frame (s : ContractState)
      (assetSlot shareSlot otherSlot user vault account amount shares : Nat)
      (hAsset : Nat.beq otherSlot assetSlot = false)
      (hShare : Nat.beq otherSlot shareSlot = false) :
      getStorage (stakeDepositMap s assetSlot shareSlot user vault amount shares) (.map otherSlot account) =
        getStorage s (.map otherSlot account) :=
    (mintMap_slot_frame _ shareSlot user shares (.map otherSlot account)
      ((congrArg (· && account.beq user) hShare).trans (Bool.false_and _))).trans
      (transferMap_slot_frame s assetSlot user vault amount (.map otherSlot account)
        ((congrArg (· && account.beq user) hAsset).trans (Bool.false_and _))
        ((congrArg (· && account.beq vault) hAsset).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem stakeDepositMap_other_account_frame (s : ContractState)
      (slot user vault observer amount shares : Nat)
      (hUser : Nat.beq observer user = false)
      (hVault : Nat.beq observer vault = false) :
      getStorage (stakeDepositMap s slot slot user vault amount shares) (.map slot observer) =
        getStorage s (.map slot observer) :=
    (mintMap_other_account_frame _ slot user observer shares hUser).trans
      (transferMap_other_account_frame s slot user vault observer amount hUser hVault)

set_option maxHeartbeats 200000 in
  theorem stakeWithdrawMap_other_slot_frame (s : ContractState)
      (assetSlot shareSlot otherSlot user vault account amount shares : Nat)
      (hAsset : Nat.beq otherSlot assetSlot = false)
      (hShare : Nat.beq otherSlot shareSlot = false) :
      getStorage (stakeWithdrawMap s assetSlot shareSlot user vault amount shares) (.map otherSlot account) =
        getStorage s (.map otherSlot account) :=
    (transferMap_slot_frame _ assetSlot vault user amount (.map otherSlot account)
      ((congrArg (· && account.beq vault) hAsset).trans (Bool.false_and _))
      ((congrArg (· && account.beq user) hAsset).trans (Bool.false_and _))).trans
      (burnMap_slot_frame s shareSlot user shares (.map otherSlot account)
        ((congrArg (· && account.beq user) hShare).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem stakeWithdrawMap_other_account_frame (s : ContractState)
      (slot user vault observer amount shares : Nat)
      (hUser : Nat.beq observer user = false)
      (hVault : Nat.beq observer vault = false) :
      getStorage (stakeWithdrawMap s slot slot user vault amount shares) (.map slot observer) =
        getStorage s (.map slot observer) :=
    (transferMap_other_account_frame _ slot vault user observer amount hVault hUser).trans
      (burnMap_other_account_frame s slot user observer shares hUser)

set_option maxHeartbeats 200000 in
  theorem guardedStakeDepositMap_unlocked_after (s : ContractState)
      (lockSlot assetSlot shareSlot user vault amount shares : Nat) :
      isTransientLocked (guardedStakeDepositMap s lockSlot assetSlot shareSlot user vault amount shares) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def guardedStakeWithdrawMap (s : ContractState)
      (lockSlot assetSlot shareSlot user vault amount shares : Nat) : ContractState :=
    releaseTransientLock
      (stakeWithdrawMap (acquireTransientLock s lockSlot) assetSlot shareSlot user vault amount shares)
      lockSlot

  def stakeDepositThenWithdrawMap (s : ContractState)
      (assetSlot shareSlot user vault amount shares : Nat) : ContractState :=
    stakeWithdrawMap (stakeDepositMap s assetSlot shareSlot user vault amount shares) assetSlot shareSlot user vault amount shares

set_option maxHeartbeats 200000 in
  theorem stakeDepositMap_preserves_transient (s : ContractState)
      (assetSlot shareSlot user vault amount shares tslot : Nat) :
      getStorage (stakeDepositMap s assetSlot shareSlot user vault amount shares) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (mintMap_slot_frame _ shareSlot user shares (.transient tslot) rfl).trans
      (transferMap_slot_frame s assetSlot user vault amount (.transient tslot) rfl rfl)

set_option maxHeartbeats 200000 in
  theorem stakeWithdrawMap_preserves_transient (s : ContractState)
      (assetSlot shareSlot user vault amount shares tslot : Nat) :
      getStorage (stakeWithdrawMap s assetSlot shareSlot user vault amount shares) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (transferMap_slot_frame _ assetSlot vault user amount (.transient tslot) rfl rfl).trans
      (burnMap_slot_frame s shareSlot user shares (.transient tslot) rfl)

set_option maxHeartbeats 200000 in
  theorem guardedStakeWithdrawMap_unlocked_after (s : ContractState)
      (lockSlot assetSlot shareSlot user vault amount shares : Nat) :
      isTransientLocked (guardedStakeWithdrawMap s lockSlot assetSlot shareSlot user vault amount shares) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem stakeDepositThenWithdrawMap_other_slot_frame (s : ContractState)
      (assetSlot shareSlot otherSlot user vault account amount shares : Nat)
      (hAsset : Nat.beq otherSlot assetSlot = false)
      (hShare : Nat.beq otherSlot shareSlot = false) :
      getStorage (stakeDepositThenWithdrawMap s assetSlot shareSlot user vault amount shares) (.map otherSlot account) =
        getStorage s (.map otherSlot account) :=
    (stakeWithdrawMap_other_slot_frame _ assetSlot shareSlot otherSlot user vault account amount shares hAsset hShare).trans
      (stakeDepositMap_other_slot_frame s assetSlot shareSlot otherSlot user vault account amount shares hAsset hShare)

set_option maxHeartbeats 200000 in
  theorem stakeDepositThenWithdrawMap_other_account_frame (s : ContractState)
      (slot user vault observer amount shares : Nat)
      (hUser : Nat.beq observer user = false)
      (hVault : Nat.beq observer vault = false) :
      getStorage (stakeDepositThenWithdrawMap s slot slot user vault amount shares) (.map slot observer) =
        getStorage s (.map slot observer) :=
    (stakeWithdrawMap_other_account_frame _ slot user vault observer amount shares hUser hVault).trans
      (stakeDepositMap_other_account_frame s slot user vault observer amount shares hUser hVault)

  def guardedStakeDepositThenWithdrawMap (s : ContractState)
      (lockSlot assetSlot shareSlot user vault amount shares : Nat) : ContractState :=
    releaseTransientLock
      (stakeDepositThenWithdrawMap (acquireTransientLock s lockSlot) assetSlot shareSlot user vault amount shares)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem stakeDepositThenWithdrawMap_share_exact_restore (s : ContractState)
      (assetSlot shareSlot user vault amount shares : Nat)
      (hDisjoint : Nat.beq shareSlot assetSlot = false) :
      getStorage (stakeDepositThenWithdrawMap s assetSlot shareSlot user vault amount shares) (.map shareSlot user) =
        getStorage s (.map shareSlot user) :=
    let hVaultMiss : StorageKey.fastBeq (.map shareSlot user) (.map assetSlot vault) = false :=
      (congrArg (· && user.beq vault) hDisjoint).trans (Bool.false_and _)
    let hUserMiss : StorageKey.fastBeq (.map shareSlot user) (.map assetSlot user) = false :=
      (congrArg (· && user.beq user) hDisjoint).trans (Bool.false_and _)
    (transferMap_slot_frame _ assetSlot vault user amount (.map shareSlot user) hVaultMiss hUserMiss).trans <|
      (mint_then_burn_exact (transferMap s assetSlot user vault amount) shareSlot user shares).trans
        (transferMap_slot_frame s assetSlot user vault amount (.map shareSlot user) hUserMiss hVaultMiss)

set_option maxHeartbeats 200000 in
  theorem stakeDepositThenWithdrawMap_self_asset_preserve (s : ContractState)
      (assetSlot shareSlot account amount shares : Nat)
      (hDisjoint : Nat.beq assetSlot shareSlot = false)
      (hLe : amount ≤ getStorage s (.map assetSlot account)) :
      getStorage (stakeDepositThenWithdrawMap s assetSlot shareSlot account account amount shares) (.map assetSlot account) =
        getStorage s (.map assetSlot account) :=
    let hShareMiss : StorageKey.fastBeq (.map assetSlot account) (.map shareSlot account) = false :=
      (congrArg (· && account.beq account) hDisjoint).trans (Bool.false_and _)
    let hStep1 : getStorage (transferMap s assetSlot account account amount) (.map assetSlot account) =
        getStorage s (.map assetSlot account) :=
      transferMap_self_preserve s assetSlot account amount hLe
    let hStep2 : getStorage (burnMap (stakeDepositMap s assetSlot shareSlot account account amount shares) shareSlot account shares) (.map assetSlot account) =
        getStorage s (.map assetSlot account) :=
      (burnMap_slot_frame _ shareSlot account shares (.map assetSlot account) hShareMiss).trans <|
        (mintMap_slot_frame _ shareSlot account shares (.map assetSlot account) hShareMiss).trans
          hStep1
    (transferMap_self_preserve _ assetSlot account amount (hStep2.symm ▸ hLe)).trans hStep2

set_option maxHeartbeats 200000 in
  theorem stakeDepositThenWithdrawMap_preserves_transient (s : ContractState)
      (assetSlot shareSlot user vault amount shares tslot : Nat) :
      getStorage (stakeDepositThenWithdrawMap s assetSlot shareSlot user vault amount shares) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (stakeWithdrawMap_preserves_transient _ assetSlot shareSlot user vault amount shares tslot).trans
      (stakeDepositMap_preserves_transient s assetSlot shareSlot user vault amount shares tslot)

set_option maxHeartbeats 200000 in
  theorem guardedStakeDepositThenWithdrawMap_unlocked_after (s : ContractState)
      (lockSlot assetSlot shareSlot user vault amount shares : Nat) :
      isTransientLocked (guardedStakeDepositThenWithdrawMap s lockSlot assetSlot shareSlot user vault amount shares) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem guardedStakeDepositThenWithdrawMap_share_exact_restore (s : ContractState)
      (lockSlot assetSlot shareSlot user vault amount shares : Nat)
      (hDisjoint : Nat.beq shareSlot assetSlot = false) :
      getStorage (guardedStakeDepositThenWithdrawMap s lockSlot assetSlot shareSlot user vault amount shares) (.map shareSlot user) =
        getStorage s (.map shareSlot user) :=
    (getStorage_setStorage_miss _ (.transient lockSlot) (.map shareSlot user) 0 rfl).trans <|
      (stakeDepositThenWithdrawMap_share_exact_restore _ assetSlot shareSlot user vault amount shares hDisjoint).trans
        (getStorage_setStorage_miss s (.transient lockSlot) (.map shareSlot user) 1 rfl)

  def stakeWithdrawThenDepositMap (s : ContractState)
      (assetSlot shareSlot user vault amount shares : Nat) : ContractState :=
    stakeDepositMap (stakeWithdrawMap s assetSlot shareSlot user vault amount shares) assetSlot shareSlot user vault amount shares

  def guardedStakeWithdrawThenDepositMap (s : ContractState)
      (lockSlot assetSlot shareSlot user vault amount shares : Nat) : ContractState :=
    releaseTransientLock
      (stakeWithdrawThenDepositMap (acquireTransientLock s lockSlot) assetSlot shareSlot user vault amount shares)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem stakeWithdrawThenDepositMap_other_slot_frame (s : ContractState)
      (assetSlot shareSlot otherSlot user vault account amount shares : Nat)
      (hAsset : Nat.beq otherSlot assetSlot = false)
      (hShare : Nat.beq otherSlot shareSlot = false) :
      getStorage (stakeWithdrawThenDepositMap s assetSlot shareSlot user vault amount shares) (.map otherSlot account) =
        getStorage s (.map otherSlot account) :=
    (stakeDepositMap_other_slot_frame _ assetSlot shareSlot otherSlot user vault account amount shares hAsset hShare).trans
      (stakeWithdrawMap_other_slot_frame s assetSlot shareSlot otherSlot user vault account amount shares hAsset hShare)

set_option maxHeartbeats 200000 in
  theorem stakeWithdrawThenDepositMap_asset_exact_restore (s : ContractState)
      (assetSlot shareSlot user vault amount shares : Nat)
      (hDisjoint : Nat.beq assetSlot shareSlot = false)
      (hUserVault : Nat.beq user vault = false) :
      getStorage (stakeWithdrawThenDepositMap s assetSlot shareSlot user vault amount shares) (.map assetSlot user) =
        getStorage s (.map assetSlot user) :=
    let hShareMiss : StorageKey.fastBeq (.map assetSlot user) (.map shareSlot user) = false :=
      (congrArg (· && user.beq user) hDisjoint).trans (Bool.false_and _)
    let hVaultMiss : StorageKey.fastBeq (.map assetSlot user) (.map assetSlot vault) = false :=
      (congrArg (· && user.beq vault) (Nat.beq_refl assetSlot)).trans ((Bool.true_and _).trans hUserVault)
    let sBurn := burnMap s shareSlot user shares
    let sW1 := setStorage sBurn (.map assetSlot vault) (getStorage sBurn (.map assetSlot vault) - amount)
    let sW := stakeWithdrawMap s assetSlot shareSlot user vault amount shares
    let sD1 := setStorage sW (.map assetSlot user) (getStorage sW (.map assetSlot user) - amount)
    (mintMap_slot_frame _ shareSlot user shares (.map assetSlot user) hShareMiss).trans <|
      (getStorage_setStorage_miss sD1 (.map assetSlot vault) (.map assetSlot user) _ hVaultMiss).trans <|
      getStorage_setStorage_same.trans <|
      (congrArg (· - amount) getStorage_setStorage_same).trans <|
      (Nat.add_sub_cancel (getStorage sW1 (.map assetSlot user)) amount).trans <|
      (getStorage_setStorage_miss sBurn (.map assetSlot vault) (.map assetSlot user) _ hVaultMiss).trans
        (burnMap_slot_frame s shareSlot user shares (.map assetSlot user) hShareMiss)

set_option maxHeartbeats 200000 in
  theorem stakeWithdrawThenDepositMap_preserves_transient (s : ContractState)
      (assetSlot shareSlot user vault amount shares tslot : Nat) :
      getStorage (stakeWithdrawThenDepositMap s assetSlot shareSlot user vault amount shares) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (stakeDepositMap_preserves_transient _ assetSlot shareSlot user vault amount shares tslot).trans
      (stakeWithdrawMap_preserves_transient s assetSlot shareSlot user vault amount shares tslot)

set_option maxHeartbeats 200000 in
  theorem guardedStakeWithdrawThenDepositMap_unlocked_after (s : ContractState)
      (lockSlot assetSlot shareSlot user vault amount shares : Nat) :
      isTransientLocked (guardedStakeWithdrawThenDepositMap s lockSlot assetSlot shareSlot user vault amount shares) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem guardedStakeWithdrawThenDepositMap_other_slot_frame (s : ContractState)
      (lockSlot assetSlot shareSlot otherSlot user vault account amount shares : Nat)
      (hAsset : Nat.beq otherSlot assetSlot = false)
      (hShare : Nat.beq otherSlot shareSlot = false) :
      getStorage (guardedStakeWithdrawThenDepositMap s lockSlot assetSlot shareSlot user vault amount shares) (.map otherSlot account) =
        getStorage s (.map otherSlot account) :=
    (getStorage_setStorage_miss _ (.transient lockSlot) (.map otherSlot account) 0 rfl).trans <|
      (stakeWithdrawThenDepositMap_other_slot_frame _ assetSlot shareSlot otherSlot user vault account amount shares hAsset hShare).trans
        (getStorage_setStorage_miss s (.transient lockSlot) (.map otherSlot account) 1 rfl)

  def vaultHarvestMap (s : ContractState)
      (vaultAssetSlot treasuryShareSlot totalSharesSlot account yieldAssets feeShares : Nat) : ContractState :=
    mintMap
      (mintMap
        (mintMap s vaultAssetSlot account yieldAssets)
        treasuryShareSlot account feeShares)
      totalSharesSlot account feeShares

  def guardedVaultHarvestMap (s : ContractState)
      (lockSlot vaultAssetSlot treasuryShareSlot totalSharesSlot account yieldAssets feeShares : Nat) : ContractState :=
    releaseTransientLock
      (vaultHarvestMap (acquireTransientLock s lockSlot) vaultAssetSlot treasuryShareSlot totalSharesSlot account yieldAssets feeShares)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem vaultHarvestMap_other_slot_frame (s : ContractState)
      (vaultAssetSlot treasuryShareSlot totalSharesSlot otherSlot account observer yieldAssets feeShares : Nat)
      (hVault : Nat.beq otherSlot vaultAssetSlot = false)
      (hTreasury : Nat.beq otherSlot treasuryShareSlot = false)
      (hTotal : Nat.beq otherSlot totalSharesSlot = false) :
      getStorage (vaultHarvestMap s vaultAssetSlot treasuryShareSlot totalSharesSlot account yieldAssets feeShares) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (mintMap_slot_frame _ totalSharesSlot account feeShares (.map otherSlot observer)
      ((congrArg (· && observer.beq account) hTotal).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ treasuryShareSlot account feeShares (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hTreasury).trans (Bool.false_and _))).trans
        (mintMap_slot_frame s vaultAssetSlot account yieldAssets (.map otherSlot observer)
          ((congrArg (· && observer.beq account) hVault).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem vaultHarvestMap_total_shares_updated (s : ContractState)
      (vaultAssetSlot treasuryShareSlot totalSharesSlot account yieldAssets feeShares : Nat)
      (hTotalTreasury : Nat.beq totalSharesSlot treasuryShareSlot = false)
      (hTotalVault : Nat.beq totalSharesSlot vaultAssetSlot = false) :
      getStorage (vaultHarvestMap s vaultAssetSlot treasuryShareSlot totalSharesSlot account yieldAssets feeShares) (.map totalSharesSlot account) =
        getStorage s (.map totalSharesSlot account) + feeShares :=
    let hMissTreasury : StorageKey.fastBeq (.map totalSharesSlot account) (.map treasuryShareSlot account) = false :=
      (congrArg (· && account.beq account) hTotalTreasury).trans (Bool.false_and _)
    let hMissVault : StorageKey.fastBeq (.map totalSharesSlot account) (.map vaultAssetSlot account) = false :=
      (congrArg (· && account.beq account) hTotalVault).trans (Bool.false_and _)
    getStorage_setStorage_same.trans <|
      congrArg (· + feeShares)
        ((mintMap_slot_frame _ treasuryShareSlot account feeShares (.map totalSharesSlot account) hMissTreasury).trans
          (mintMap_slot_frame s vaultAssetSlot account yieldAssets (.map totalSharesSlot account) hMissVault))

set_option maxHeartbeats 200000 in
  theorem vaultHarvestMap_treasury_shares_updated (s : ContractState)
      (vaultAssetSlot treasuryShareSlot totalSharesSlot account yieldAssets feeShares : Nat)
      (hTreasuryTotal : Nat.beq treasuryShareSlot totalSharesSlot = false)
      (hTreasuryVault : Nat.beq treasuryShareSlot vaultAssetSlot = false) :
      getStorage (vaultHarvestMap s vaultAssetSlot treasuryShareSlot totalSharesSlot account yieldAssets feeShares) (.map treasuryShareSlot account) =
        getStorage s (.map treasuryShareSlot account) + feeShares :=
    let hMissTotal : StorageKey.fastBeq (.map treasuryShareSlot account) (.map totalSharesSlot account) = false :=
      (congrArg (· && account.beq account) hTreasuryTotal).trans (Bool.false_and _)
    let hMissVault : StorageKey.fastBeq (.map treasuryShareSlot account) (.map vaultAssetSlot account) = false :=
      (congrArg (· && account.beq account) hTreasuryVault).trans (Bool.false_and _)
    (mintMap_slot_frame _ totalSharesSlot account feeShares (.map treasuryShareSlot account) hMissTotal).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· + feeShares)
          (mintMap_slot_frame s vaultAssetSlot account yieldAssets (.map treasuryShareSlot account) hMissVault))

set_option maxHeartbeats 200000 in
  theorem vaultHarvestMap_vault_assets_updated (s : ContractState)
      (vaultAssetSlot treasuryShareSlot totalSharesSlot account yieldAssets feeShares : Nat)
      (hVaultTreasury : Nat.beq vaultAssetSlot treasuryShareSlot = false)
      (hVaultTotal : Nat.beq vaultAssetSlot totalSharesSlot = false) :
      getStorage (vaultHarvestMap s vaultAssetSlot treasuryShareSlot totalSharesSlot account yieldAssets feeShares) (.map vaultAssetSlot account) =
        getStorage s (.map vaultAssetSlot account) + yieldAssets :=
    let hMissTotal : StorageKey.fastBeq (.map vaultAssetSlot account) (.map totalSharesSlot account) = false :=
      (congrArg (· && account.beq account) hVaultTotal).trans (Bool.false_and _)
    let hMissTreasury : StorageKey.fastBeq (.map vaultAssetSlot account) (.map treasuryShareSlot account) = false :=
      (congrArg (· && account.beq account) hVaultTreasury).trans (Bool.false_and _)
    (mintMap_slot_frame _ totalSharesSlot account feeShares (.map vaultAssetSlot account) hMissTotal).trans <|
      (mintMap_slot_frame _ treasuryShareSlot account feeShares (.map vaultAssetSlot account) hMissTreasury).trans
        getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem guardedVaultHarvestMap_unlocked_after (s : ContractState)
      (lockSlot vaultAssetSlot treasuryShareSlot totalSharesSlot account yieldAssets feeShares : Nat) :
      isTransientLocked (guardedVaultHarvestMap s lockSlot vaultAssetSlot treasuryShareSlot totalSharesSlot account yieldAssets feeShares) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def vaultSlashMap (s : ContractState)
      (vaultAssetSlot insuranceReserveSlot totalSharesSlot account slashAssets reserveCover burnedShares : Nat) : ContractState :=
    burnMap
      (burnMap
        (burnMap s vaultAssetSlot account slashAssets)
        insuranceReserveSlot account reserveCover)
      totalSharesSlot account burnedShares

  def guardedVaultSlashMap (s : ContractState)
      (lockSlot vaultAssetSlot insuranceReserveSlot totalSharesSlot account slashAssets reserveCover burnedShares : Nat) : ContractState :=
    releaseTransientLock
      (vaultSlashMap (acquireTransientLock s lockSlot) vaultAssetSlot insuranceReserveSlot totalSharesSlot account slashAssets reserveCover burnedShares)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem vaultSlashMap_other_slot_frame (s : ContractState)
      (vaultAssetSlot insuranceReserveSlot totalSharesSlot otherSlot account observer slashAssets reserveCover burnedShares : Nat)
      (hVault : Nat.beq otherSlot vaultAssetSlot = false)
      (hReserve : Nat.beq otherSlot insuranceReserveSlot = false)
      (hTotal : Nat.beq otherSlot totalSharesSlot = false) :
      getStorage (vaultSlashMap s vaultAssetSlot insuranceReserveSlot totalSharesSlot account slashAssets reserveCover burnedShares) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (burnMap_slot_frame _ totalSharesSlot account burnedShares (.map otherSlot observer)
      ((congrArg (· && observer.beq account) hTotal).trans (Bool.false_and _))).trans <|
      (burnMap_slot_frame _ insuranceReserveSlot account reserveCover (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hReserve).trans (Bool.false_and _))).trans
        (burnMap_slot_frame s vaultAssetSlot account slashAssets (.map otherSlot observer)
          ((congrArg (· && observer.beq account) hVault).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem vaultSlashMap_total_shares_updated (s : ContractState)
      (vaultAssetSlot insuranceReserveSlot totalSharesSlot account slashAssets reserveCover burnedShares : Nat)
      (hTotalReserve : Nat.beq totalSharesSlot insuranceReserveSlot = false)
      (hTotalVault : Nat.beq totalSharesSlot vaultAssetSlot = false) :
      getStorage (vaultSlashMap s vaultAssetSlot insuranceReserveSlot totalSharesSlot account slashAssets reserveCover burnedShares) (.map totalSharesSlot account) =
        getStorage s (.map totalSharesSlot account) - burnedShares :=
    let hMissReserve : StorageKey.fastBeq (.map totalSharesSlot account) (.map insuranceReserveSlot account) = false :=
      (congrArg (· && account.beq account) hTotalReserve).trans (Bool.false_and _)
    let hMissVault : StorageKey.fastBeq (.map totalSharesSlot account) (.map vaultAssetSlot account) = false :=
      (congrArg (· && account.beq account) hTotalVault).trans (Bool.false_and _)
    getStorage_setStorage_same.trans <|
      congrArg (· - burnedShares)
        ((burnMap_slot_frame _ insuranceReserveSlot account reserveCover (.map totalSharesSlot account) hMissReserve).trans
          (burnMap_slot_frame s vaultAssetSlot account slashAssets (.map totalSharesSlot account) hMissVault))

set_option maxHeartbeats 200000 in
  theorem vaultSlashMap_insurance_reserve_updated (s : ContractState)
      (vaultAssetSlot insuranceReserveSlot totalSharesSlot account slashAssets reserveCover burnedShares : Nat)
      (hReserveTotal : Nat.beq insuranceReserveSlot totalSharesSlot = false)
      (hReserveVault : Nat.beq insuranceReserveSlot vaultAssetSlot = false) :
      getStorage (vaultSlashMap s vaultAssetSlot insuranceReserveSlot totalSharesSlot account slashAssets reserveCover burnedShares) (.map insuranceReserveSlot account) =
        getStorage s (.map insuranceReserveSlot account) - reserveCover :=
    let hMissTotal : StorageKey.fastBeq (.map insuranceReserveSlot account) (.map totalSharesSlot account) = false :=
      (congrArg (· && account.beq account) hReserveTotal).trans (Bool.false_and _)
    let hMissVault : StorageKey.fastBeq (.map insuranceReserveSlot account) (.map vaultAssetSlot account) = false :=
      (congrArg (· && account.beq account) hReserveVault).trans (Bool.false_and _)
    (burnMap_slot_frame _ totalSharesSlot account burnedShares (.map insuranceReserveSlot account) hMissTotal).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· - reserveCover)
          (burnMap_slot_frame s vaultAssetSlot account slashAssets (.map insuranceReserveSlot account) hMissVault))

set_option maxHeartbeats 200000 in
  theorem vaultSlashMap_vault_assets_updated (s : ContractState)
      (vaultAssetSlot insuranceReserveSlot totalSharesSlot account slashAssets reserveCover burnedShares : Nat)
      (hVaultReserve : Nat.beq vaultAssetSlot insuranceReserveSlot = false)
      (hVaultTotal : Nat.beq vaultAssetSlot totalSharesSlot = false) :
      getStorage (vaultSlashMap s vaultAssetSlot insuranceReserveSlot totalSharesSlot account slashAssets reserveCover burnedShares) (.map vaultAssetSlot account) =
        getStorage s (.map vaultAssetSlot account) - slashAssets :=
    let hMissTotal : StorageKey.fastBeq (.map vaultAssetSlot account) (.map totalSharesSlot account) = false :=
      (congrArg (· && account.beq account) hVaultTotal).trans (Bool.false_and _)
    let hMissReserve : StorageKey.fastBeq (.map vaultAssetSlot account) (.map insuranceReserveSlot account) = false :=
      (congrArg (· && account.beq account) hVaultReserve).trans (Bool.false_and _)
    (burnMap_slot_frame _ totalSharesSlot account burnedShares (.map vaultAssetSlot account) hMissTotal).trans <|
      (burnMap_slot_frame _ insuranceReserveSlot account reserveCover (.map vaultAssetSlot account) hMissReserve).trans
        getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem guardedVaultSlashMap_unlocked_after (s : ContractState)
      (lockSlot vaultAssetSlot insuranceReserveSlot totalSharesSlot account slashAssets reserveCover burnedShares : Nat) :
      isTransientLocked (guardedVaultSlashMap s lockSlot vaultAssetSlot insuranceReserveSlot totalSharesSlot account slashAssets reserveCover burnedShares) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def vaultSlashThenHarvestMap (s : ContractState)
      (vaultAssetSlot insuranceReserveSlot treasuryShareSlot totalSharesSlot account slashAssets reserveCover burnedShares : Nat) : ContractState :=
    vaultHarvestMap
      (vaultSlashMap s vaultAssetSlot insuranceReserveSlot totalSharesSlot account slashAssets reserveCover burnedShares)
      vaultAssetSlot treasuryShareSlot totalSharesSlot account slashAssets burnedShares

  def guardedVaultSlashThenHarvestMap (s : ContractState)
      (lockSlot vaultAssetSlot insuranceReserveSlot treasuryShareSlot totalSharesSlot account slashAssets reserveCover burnedShares : Nat) : ContractState :=
    releaseTransientLock
      (vaultSlashThenHarvestMap (acquireTransientLock s lockSlot) vaultAssetSlot insuranceReserveSlot treasuryShareSlot totalSharesSlot account slashAssets reserveCover burnedShares)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem vaultSlashThenHarvestMap_other_slot_frame (s : ContractState)
      (vaultAssetSlot insuranceReserveSlot treasuryShareSlot totalSharesSlot otherSlot account observer slashAssets reserveCover burnedShares : Nat)
      (hVault : Nat.beq otherSlot vaultAssetSlot = false)
      (hReserve : Nat.beq otherSlot insuranceReserveSlot = false)
      (hTreasury : Nat.beq otherSlot treasuryShareSlot = false)
      (hTotal : Nat.beq otherSlot totalSharesSlot = false) :
      getStorage (vaultSlashThenHarvestMap s vaultAssetSlot insuranceReserveSlot treasuryShareSlot totalSharesSlot account slashAssets reserveCover burnedShares) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (vaultHarvestMap_other_slot_frame _ vaultAssetSlot treasuryShareSlot totalSharesSlot otherSlot account observer slashAssets burnedShares hVault hTreasury hTotal).trans
      (vaultSlashMap_other_slot_frame s vaultAssetSlot insuranceReserveSlot totalSharesSlot otherSlot account observer slashAssets reserveCover burnedShares hVault hReserve hTotal)

set_option maxHeartbeats 200000 in
  theorem vaultSlashThenHarvestMap_total_shares_exact_restore (s : ContractState)
      (vaultAssetSlot insuranceReserveSlot treasuryShareSlot totalSharesSlot account slashAssets reserveCover burnedShares : Nat)
      (hTotalTreasury : Nat.beq totalSharesSlot treasuryShareSlot = false)
      (hTotalReserve : Nat.beq totalSharesSlot insuranceReserveSlot = false)
      (hTotalVault : Nat.beq totalSharesSlot vaultAssetSlot = false)
      (hLe : burnedShares ≤ getStorage s (.map totalSharesSlot account)) :
      getStorage (vaultSlashThenHarvestMap s vaultAssetSlot insuranceReserveSlot treasuryShareSlot totalSharesSlot account slashAssets reserveCover burnedShares) (.map totalSharesSlot account) =
        getStorage s (.map totalSharesSlot account) :=
    (vaultHarvestMap_total_shares_updated _ vaultAssetSlot treasuryShareSlot totalSharesSlot account slashAssets burnedShares hTotalTreasury hTotalVault).trans <|
      (congrArg (· + burnedShares)
        (vaultSlashMap_total_shares_updated s vaultAssetSlot insuranceReserveSlot totalSharesSlot account slashAssets reserveCover burnedShares hTotalReserve hTotalVault)).trans
        (Nat.sub_add_cancel hLe)

set_option maxHeartbeats 200000 in
  theorem vaultSlashThenHarvestMap_vault_assets_exact_restore (s : ContractState)
      (vaultAssetSlot insuranceReserveSlot treasuryShareSlot totalSharesSlot account slashAssets reserveCover burnedShares : Nat)
      (hVaultTreasury : Nat.beq vaultAssetSlot treasuryShareSlot = false)
      (hVaultReserve : Nat.beq vaultAssetSlot insuranceReserveSlot = false)
      (hVaultTotal : Nat.beq vaultAssetSlot totalSharesSlot = false)
      (hLe : slashAssets ≤ getStorage s (.map vaultAssetSlot account)) :
      getStorage (vaultSlashThenHarvestMap s vaultAssetSlot insuranceReserveSlot treasuryShareSlot totalSharesSlot account slashAssets reserveCover burnedShares) (.map vaultAssetSlot account) =
        getStorage s (.map vaultAssetSlot account) :=
    (vaultHarvestMap_vault_assets_updated _ vaultAssetSlot treasuryShareSlot totalSharesSlot account slashAssets burnedShares hVaultTreasury hVaultTotal).trans <|
      (congrArg (· + slashAssets)
        (vaultSlashMap_vault_assets_updated s vaultAssetSlot insuranceReserveSlot totalSharesSlot account slashAssets reserveCover burnedShares hVaultReserve hVaultTotal)).trans
        (Nat.sub_add_cancel hLe)

set_option maxHeartbeats 200000 in
  theorem vaultSlashThenHarvestMap_preserves_transient (s : ContractState)
      (vaultAssetSlot insuranceReserveSlot treasuryShareSlot totalSharesSlot account slashAssets reserveCover burnedShares tslot : Nat) :
      getStorage (vaultSlashThenHarvestMap s vaultAssetSlot insuranceReserveSlot treasuryShareSlot totalSharesSlot account slashAssets reserveCover burnedShares) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (mintMap_slot_frame _ totalSharesSlot account burnedShares (.transient tslot) rfl).trans <|
      (mintMap_slot_frame _ treasuryShareSlot account burnedShares (.transient tslot) rfl).trans <|
      (mintMap_slot_frame _ vaultAssetSlot account slashAssets (.transient tslot) rfl).trans <|
      (burnMap_slot_frame _ totalSharesSlot account burnedShares (.transient tslot) rfl).trans <|
      (burnMap_slot_frame _ insuranceReserveSlot account reserveCover (.transient tslot) rfl).trans
        (burnMap_slot_frame s vaultAssetSlot account slashAssets (.transient tslot) rfl)

set_option maxHeartbeats 200000 in
  theorem guardedVaultSlashThenHarvestMap_unlocked_after (s : ContractState)
      (lockSlot vaultAssetSlot insuranceReserveSlot treasuryShareSlot totalSharesSlot account slashAssets reserveCover burnedShares : Nat) :
      isTransientLocked (guardedVaultSlashThenHarvestMap s lockSlot vaultAssetSlot insuranceReserveSlot treasuryShareSlot totalSharesSlot account slashAssets reserveCover burnedShares) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def vaultRebalanceMap (s : ContractState)
      (strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep : Nat) : ContractState :=
    mintMap
      (mintMap
        (burnMap s strategyASlot account rebalanceAmount)
        strategyBSlot account rebalanceAmount)
      epochSlot account epochStep

  def guardedVaultRebalanceMap (s : ContractState)
      (lockSlot strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep : Nat) : ContractState :=
    releaseTransientLock
      (vaultRebalanceMap (acquireTransientLock s lockSlot) strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem vaultRebalanceMap_other_slot_frame (s : ContractState)
      (strategyASlot strategyBSlot epochSlot otherSlot account observer rebalanceAmount epochStep : Nat)
      (hStratA : Nat.beq otherSlot strategyASlot = false)
      (hStratB : Nat.beq otherSlot strategyBSlot = false)
      (hEpoch : Nat.beq otherSlot epochSlot = false) :
      getStorage (vaultRebalanceMap s strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (mintMap_slot_frame _ epochSlot account epochStep (.map otherSlot observer)
      ((congrArg (· && observer.beq account) hEpoch).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ strategyBSlot account rebalanceAmount (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hStratB).trans (Bool.false_and _))).trans
        (burnMap_slot_frame s strategyASlot account rebalanceAmount (.map otherSlot observer)
          ((congrArg (· && observer.beq account) hStratA).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem vaultRebalanceMap_epoch_updated (s : ContractState)
      (strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep : Nat)
      (hEpochStratB : Nat.beq epochSlot strategyBSlot = false)
      (hEpochStratA : Nat.beq epochSlot strategyASlot = false) :
      getStorage (vaultRebalanceMap s strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep) (.map epochSlot account) =
        getStorage s (.map epochSlot account) + epochStep :=
    let hMissStratB : StorageKey.fastBeq (.map epochSlot account) (.map strategyBSlot account) = false :=
      (congrArg (· && account.beq account) hEpochStratB).trans (Bool.false_and _)
    let hMissStratA : StorageKey.fastBeq (.map epochSlot account) (.map strategyASlot account) = false :=
      (congrArg (· && account.beq account) hEpochStratA).trans (Bool.false_and _)
    getStorage_setStorage_same.trans <|
      congrArg (· + epochStep)
        ((mintMap_slot_frame _ strategyBSlot account rebalanceAmount (.map epochSlot account) hMissStratB).trans
          (burnMap_slot_frame s strategyASlot account rebalanceAmount (.map epochSlot account) hMissStratA))

set_option maxHeartbeats 200000 in
  theorem vaultRebalanceMap_strategyB_updated (s : ContractState)
      (strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep : Nat)
      (hStratBEpoch : Nat.beq strategyBSlot epochSlot = false)
      (hStratBStratA : Nat.beq strategyBSlot strategyASlot = false) :
      getStorage (vaultRebalanceMap s strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep) (.map strategyBSlot account) =
        getStorage s (.map strategyBSlot account) + rebalanceAmount :=
    let hMissEpoch : StorageKey.fastBeq (.map strategyBSlot account) (.map epochSlot account) = false :=
      (congrArg (· && account.beq account) hStratBEpoch).trans (Bool.false_and _)
    let hMissStratA : StorageKey.fastBeq (.map strategyBSlot account) (.map strategyASlot account) = false :=
      (congrArg (· && account.beq account) hStratBStratA).trans (Bool.false_and _)
    (mintMap_slot_frame _ epochSlot account epochStep (.map strategyBSlot account) hMissEpoch).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· + rebalanceAmount)
          (burnMap_slot_frame s strategyASlot account rebalanceAmount (.map strategyBSlot account) hMissStratA))

set_option maxHeartbeats 200000 in
  theorem vaultRebalanceMap_strategyA_updated (s : ContractState)
      (strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep : Nat)
      (hStratAStratB : Nat.beq strategyASlot strategyBSlot = false)
      (hStratAEpoch : Nat.beq strategyASlot epochSlot = false) :
      getStorage (vaultRebalanceMap s strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep) (.map strategyASlot account) =
        getStorage s (.map strategyASlot account) - rebalanceAmount :=
    let hMissEpoch : StorageKey.fastBeq (.map strategyASlot account) (.map epochSlot account) = false :=
      (congrArg (· && account.beq account) hStratAEpoch).trans (Bool.false_and _)
    let hMissStratB : StorageKey.fastBeq (.map strategyASlot account) (.map strategyBSlot account) = false :=
      (congrArg (· && account.beq account) hStratAStratB).trans (Bool.false_and _)
    (mintMap_slot_frame _ epochSlot account epochStep (.map strategyASlot account) hMissEpoch).trans <|
      (mintMap_slot_frame _ strategyBSlot account rebalanceAmount (.map strategyASlot account) hMissStratB).trans
        getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem guardedVaultRebalanceMap_unlocked_after (s : ContractState)
      (lockSlot strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep : Nat) :
      isTransientLocked (guardedVaultRebalanceMap s lockSlot strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def vaultRebalanceRoundTripMap (s : ContractState)
      (strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep1 epochStep2 : Nat) : ContractState :=
    vaultRebalanceMap
      (vaultRebalanceMap s strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep1)
      strategyBSlot strategyASlot epochSlot account rebalanceAmount epochStep2

  def guardedVaultRebalanceRoundTripMap (s : ContractState)
      (lockSlot strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep1 epochStep2 : Nat) : ContractState :=
    releaseTransientLock
      (vaultRebalanceRoundTripMap (acquireTransientLock s lockSlot) strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep1 epochStep2)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem vaultRebalanceRoundTripMap_other_slot_frame (s : ContractState)
      (strategyASlot strategyBSlot epochSlot otherSlot account observer rebalanceAmount epochStep1 epochStep2 : Nat)
      (hStratA : Nat.beq otherSlot strategyASlot = false)
      (hStratB : Nat.beq otherSlot strategyBSlot = false)
      (hEpoch : Nat.beq otherSlot epochSlot = false) :
      getStorage (vaultRebalanceRoundTripMap s strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep1 epochStep2) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (vaultRebalanceMap_other_slot_frame _ strategyBSlot strategyASlot epochSlot otherSlot account observer rebalanceAmount epochStep2 hStratB hStratA hEpoch).trans
      (vaultRebalanceMap_other_slot_frame s strategyASlot strategyBSlot epochSlot otherSlot account observer rebalanceAmount epochStep1 hStratA hStratB hEpoch)

set_option maxHeartbeats 200000 in
  theorem vaultRebalanceRoundTripMap_strategyA_exact_restore (s : ContractState)
      (strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep1 epochStep2 : Nat)
      (hStratAStratB : Nat.beq strategyASlot strategyBSlot = false)
      (hStratAEpoch : Nat.beq strategyASlot epochSlot = false)
      (hLe : rebalanceAmount ≤ getStorage s (.map strategyASlot account)) :
      getStorage (vaultRebalanceRoundTripMap s strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep1 epochStep2) (.map strategyASlot account) =
        getStorage s (.map strategyASlot account) :=
    (vaultRebalanceMap_strategyB_updated _ strategyBSlot strategyASlot epochSlot account rebalanceAmount epochStep2 hStratAEpoch hStratAStratB).trans <|
      (congrArg (· + rebalanceAmount)
        (vaultRebalanceMap_strategyA_updated s strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep1 hStratAStratB hStratAEpoch)).trans
        (Nat.sub_add_cancel hLe)

set_option maxHeartbeats 200000 in
  theorem vaultRebalanceRoundTripMap_epoch_double_updated (s : ContractState)
      (strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep1 epochStep2 : Nat)
      (hEpochStratA : Nat.beq epochSlot strategyASlot = false)
      (hEpochStratB : Nat.beq epochSlot strategyBSlot = false) :
      getStorage (vaultRebalanceRoundTripMap s strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep1 epochStep2) (.map epochSlot account) =
        (getStorage s (.map epochSlot account) + epochStep1) + epochStep2 :=
    (vaultRebalanceMap_epoch_updated _ strategyBSlot strategyASlot epochSlot account rebalanceAmount epochStep2 hEpochStratA hEpochStratB).trans
      (congrArg (· + epochStep2)
        (vaultRebalanceMap_epoch_updated s strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep1 hEpochStratB hEpochStratA))

set_option maxHeartbeats 200000 in
  theorem vaultRebalanceRoundTripMap_preserves_transient (s : ContractState)
      (strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep1 epochStep2 tslot : Nat) :
      getStorage (vaultRebalanceRoundTripMap s strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep1 epochStep2) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (mintMap_slot_frame _ epochSlot account epochStep2 (.transient tslot) rfl).trans <|
      (mintMap_slot_frame _ strategyASlot account rebalanceAmount (.transient tslot) rfl).trans <|
      (burnMap_slot_frame _ strategyBSlot account rebalanceAmount (.transient tslot) rfl).trans <|
      (mintMap_slot_frame _ epochSlot account epochStep1 (.transient tslot) rfl).trans <|
      (mintMap_slot_frame _ strategyBSlot account rebalanceAmount (.transient tslot) rfl).trans
        (burnMap_slot_frame s strategyASlot account rebalanceAmount (.transient tslot) rfl)

set_option maxHeartbeats 200000 in
  theorem guardedVaultRebalanceRoundTripMap_unlocked_after (s : ContractState)
      (lockSlot strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep1 epochStep2 : Nat) :
      isTransientLocked (guardedVaultRebalanceRoundTripMap s lockSlot strategyASlot strategyBSlot epochSlot account rebalanceAmount epochStep1 epochStep2) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def vaultLiquidateMap (s : ContractState)
      (borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot treasuryCollateralSlot account repaidDebt seizedCollateral liquidatorReward protocolPenalty : Nat) : ContractState :=
    mintMap
      (mintMap
        (burnMap
          (burnMap s borrowerDebtSlot account repaidDebt)
          borrowerCollateralSlot account seizedCollateral)
        liquidatorCollateralSlot account liquidatorReward)
      treasuryCollateralSlot account protocolPenalty

  def guardedVaultLiquidateMap (s : ContractState)
      (lockSlot borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot treasuryCollateralSlot account repaidDebt seizedCollateral liquidatorReward protocolPenalty : Nat) : ContractState :=
    releaseTransientLock
      (vaultLiquidateMap (acquireTransientLock s lockSlot) borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot treasuryCollateralSlot account repaidDebt seizedCollateral liquidatorReward protocolPenalty)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem vaultLiquidateMap_other_slot_frame (s : ContractState)
      (borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot treasuryCollateralSlot otherSlot account observer repaidDebt seizedCollateral liquidatorReward protocolPenalty : Nat)
      (hDebt : Nat.beq otherSlot borrowerDebtSlot = false)
      (hColl : Nat.beq otherSlot borrowerCollateralSlot = false)
      (hLiq : Nat.beq otherSlot liquidatorCollateralSlot = false)
      (hTreas : Nat.beq otherSlot treasuryCollateralSlot = false) :
      getStorage (vaultLiquidateMap s borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot treasuryCollateralSlot account repaidDebt seizedCollateral liquidatorReward protocolPenalty) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (mintMap_slot_frame _ treasuryCollateralSlot account protocolPenalty (.map otherSlot observer)
      ((congrArg (· && observer.beq account) hTreas).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ liquidatorCollateralSlot account liquidatorReward (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hLiq).trans (Bool.false_and _))).trans <|
      (burnMap_slot_frame _ borrowerCollateralSlot account seizedCollateral (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hColl).trans (Bool.false_and _))).trans
        (burnMap_slot_frame s borrowerDebtSlot account repaidDebt (.map otherSlot observer)
          ((congrArg (· && observer.beq account) hDebt).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem vaultLiquidateMap_treasury_updated (s : ContractState)
      (borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot treasuryCollateralSlot account repaidDebt seizedCollateral liquidatorReward protocolPenalty : Nat)
      (hTreasLiq : Nat.beq treasuryCollateralSlot liquidatorCollateralSlot = false)
      (hTreasColl : Nat.beq treasuryCollateralSlot borrowerCollateralSlot = false)
      (hTreasDebt : Nat.beq treasuryCollateralSlot borrowerDebtSlot = false) :
      getStorage (vaultLiquidateMap s borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot treasuryCollateralSlot account repaidDebt seizedCollateral liquidatorReward protocolPenalty) (.map treasuryCollateralSlot account) =
        getStorage s (.map treasuryCollateralSlot account) + protocolPenalty :=
    let hMissLiq : StorageKey.fastBeq (.map treasuryCollateralSlot account) (.map liquidatorCollateralSlot account) = false :=
      (congrArg (· && account.beq account) hTreasLiq).trans (Bool.false_and _)
    let hMissColl : StorageKey.fastBeq (.map treasuryCollateralSlot account) (.map borrowerCollateralSlot account) = false :=
      (congrArg (· && account.beq account) hTreasColl).trans (Bool.false_and _)
    let hMissDebt : StorageKey.fastBeq (.map treasuryCollateralSlot account) (.map borrowerDebtSlot account) = false :=
      (congrArg (· && account.beq account) hTreasDebt).trans (Bool.false_and _)
    getStorage_setStorage_same.trans <|
      congrArg (· + protocolPenalty)
        ((mintMap_slot_frame _ liquidatorCollateralSlot account liquidatorReward (.map treasuryCollateralSlot account) hMissLiq).trans
          ((burnMap_slot_frame _ borrowerCollateralSlot account seizedCollateral (.map treasuryCollateralSlot account) hMissColl).trans
            (burnMap_slot_frame s borrowerDebtSlot account repaidDebt (.map treasuryCollateralSlot account) hMissDebt)))

set_option maxHeartbeats 200000 in
  theorem vaultLiquidateMap_liquidator_updated (s : ContractState)
      (borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot treasuryCollateralSlot account repaidDebt seizedCollateral liquidatorReward protocolPenalty : Nat)
      (hLiqTreas : Nat.beq liquidatorCollateralSlot treasuryCollateralSlot = false)
      (hLiqColl : Nat.beq liquidatorCollateralSlot borrowerCollateralSlot = false)
      (hLiqDebt : Nat.beq liquidatorCollateralSlot borrowerDebtSlot = false) :
      getStorage (vaultLiquidateMap s borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot treasuryCollateralSlot account repaidDebt seizedCollateral liquidatorReward protocolPenalty) (.map liquidatorCollateralSlot account) =
        getStorage s (.map liquidatorCollateralSlot account) + liquidatorReward :=
    let hMissTreas : StorageKey.fastBeq (.map liquidatorCollateralSlot account) (.map treasuryCollateralSlot account) = false :=
      (congrArg (· && account.beq account) hLiqTreas).trans (Bool.false_and _)
    let hMissColl : StorageKey.fastBeq (.map liquidatorCollateralSlot account) (.map borrowerCollateralSlot account) = false :=
      (congrArg (· && account.beq account) hLiqColl).trans (Bool.false_and _)
    let hMissDebt : StorageKey.fastBeq (.map liquidatorCollateralSlot account) (.map borrowerDebtSlot account) = false :=
      (congrArg (· && account.beq account) hLiqDebt).trans (Bool.false_and _)
    (mintMap_slot_frame _ treasuryCollateralSlot account protocolPenalty (.map liquidatorCollateralSlot account) hMissTreas).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· + liquidatorReward)
          ((burnMap_slot_frame _ borrowerCollateralSlot account seizedCollateral (.map liquidatorCollateralSlot account) hMissColl).trans
            (burnMap_slot_frame s borrowerDebtSlot account repaidDebt (.map liquidatorCollateralSlot account) hMissDebt)))

set_option maxHeartbeats 200000 in
  theorem vaultLiquidateMap_borrower_collateral_updated (s : ContractState)
      (borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot treasuryCollateralSlot account repaidDebt seizedCollateral liquidatorReward protocolPenalty : Nat)
      (hCollTreas : Nat.beq borrowerCollateralSlot treasuryCollateralSlot = false)
      (hCollLiq : Nat.beq borrowerCollateralSlot liquidatorCollateralSlot = false)
      (hCollDebt : Nat.beq borrowerCollateralSlot borrowerDebtSlot = false) :
      getStorage (vaultLiquidateMap s borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot treasuryCollateralSlot account repaidDebt seizedCollateral liquidatorReward protocolPenalty) (.map borrowerCollateralSlot account) =
        getStorage s (.map borrowerCollateralSlot account) - seizedCollateral :=
    let hMissTreas : StorageKey.fastBeq (.map borrowerCollateralSlot account) (.map treasuryCollateralSlot account) = false :=
      (congrArg (· && account.beq account) hCollTreas).trans (Bool.false_and _)
    let hMissLiq : StorageKey.fastBeq (.map borrowerCollateralSlot account) (.map liquidatorCollateralSlot account) = false :=
      (congrArg (· && account.beq account) hCollLiq).trans (Bool.false_and _)
    let hMissDebt : StorageKey.fastBeq (.map borrowerCollateralSlot account) (.map borrowerDebtSlot account) = false :=
      (congrArg (· && account.beq account) hCollDebt).trans (Bool.false_and _)
    (mintMap_slot_frame _ treasuryCollateralSlot account protocolPenalty (.map borrowerCollateralSlot account) hMissTreas).trans <|
      (mintMap_slot_frame _ liquidatorCollateralSlot account liquidatorReward (.map borrowerCollateralSlot account) hMissLiq).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· - seizedCollateral)
          (burnMap_slot_frame s borrowerDebtSlot account repaidDebt (.map borrowerCollateralSlot account) hMissDebt))

set_option maxHeartbeats 200000 in
  theorem guardedVaultLiquidateMap_unlocked_after (s : ContractState)
      (lockSlot borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot treasuryCollateralSlot account repaidDebt seizedCollateral liquidatorReward protocolPenalty : Nat) :
      isTransientLocked (guardedVaultLiquidateMap s lockSlot borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot treasuryCollateralSlot account repaidDebt seizedCollateral liquidatorReward protocolPenalty) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def vaultFlashLoanMap (s : ContractState)
      (vaultLiquiditySlot borrowerSlot feeReserveSlot account loanAmount repayAmount flashFee : Nat) : ContractState :=
    mintMap
      (mintMap
        (burnMap
          (mintMap
            (burnMap s vaultLiquiditySlot account loanAmount)
            borrowerSlot account loanAmount)
          borrowerSlot account repayAmount)
        vaultLiquiditySlot account loanAmount)
      feeReserveSlot account flashFee

  def guardedVaultFlashLoanMap (s : ContractState)
      (lockSlot vaultLiquiditySlot borrowerSlot feeReserveSlot account loanAmount repayAmount flashFee : Nat) : ContractState :=
    releaseTransientLock
      (vaultFlashLoanMap (acquireTransientLock s lockSlot) vaultLiquiditySlot borrowerSlot feeReserveSlot account loanAmount repayAmount flashFee)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem vaultFlashLoanMap_other_slot_frame (s : ContractState)
      (vaultLiquiditySlot borrowerSlot feeReserveSlot otherSlot account observer loanAmount repayAmount flashFee : Nat)
      (hLiq : Nat.beq otherSlot vaultLiquiditySlot = false)
      (hBor : Nat.beq otherSlot borrowerSlot = false)
      (hFee : Nat.beq otherSlot feeReserveSlot = false) :
      getStorage (vaultFlashLoanMap s vaultLiquiditySlot borrowerSlot feeReserveSlot account loanAmount repayAmount flashFee) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (mintMap_slot_frame _ feeReserveSlot account flashFee (.map otherSlot observer)
      ((congrArg (· && observer.beq account) hFee).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ vaultLiquiditySlot account loanAmount (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hLiq).trans (Bool.false_and _))).trans <|
      (burnMap_slot_frame _ borrowerSlot account repayAmount (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hBor).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ borrowerSlot account loanAmount (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hBor).trans (Bool.false_and _))).trans
        (burnMap_slot_frame s vaultLiquiditySlot account loanAmount (.map otherSlot observer)
          ((congrArg (· && observer.beq account) hLiq).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem vaultFlashLoanMap_fee_reserve_updated (s : ContractState)
      (vaultLiquiditySlot borrowerSlot feeReserveSlot account loanAmount repayAmount flashFee : Nat)
      (hFeeLiq : Nat.beq feeReserveSlot vaultLiquiditySlot = false)
      (hFeeBor : Nat.beq feeReserveSlot borrowerSlot = false) :
      getStorage (vaultFlashLoanMap s vaultLiquiditySlot borrowerSlot feeReserveSlot account loanAmount repayAmount flashFee) (.map feeReserveSlot account) =
        getStorage s (.map feeReserveSlot account) + flashFee :=
    let hMissLiq : StorageKey.fastBeq (.map feeReserveSlot account) (.map vaultLiquiditySlot account) = false :=
      (congrArg (· && account.beq account) hFeeLiq).trans (Bool.false_and _)
    let hMissBor : StorageKey.fastBeq (.map feeReserveSlot account) (.map borrowerSlot account) = false :=
      (congrArg (· && account.beq account) hFeeBor).trans (Bool.false_and _)
    getStorage_setStorage_same.trans <|
      congrArg (· + flashFee)
        ((mintMap_slot_frame _ vaultLiquiditySlot account loanAmount (.map feeReserveSlot account) hMissLiq).trans
          ((burnMap_slot_frame _ borrowerSlot account repayAmount (.map feeReserveSlot account) hMissBor).trans
            ((mintMap_slot_frame _ borrowerSlot account loanAmount (.map feeReserveSlot account) hMissBor).trans
              (burnMap_slot_frame s vaultLiquiditySlot account loanAmount (.map feeReserveSlot account) hMissLiq))))

set_option maxHeartbeats 200000 in
  theorem vaultFlashLoanMap_liquidity_exact_restore (s : ContractState)
      (vaultLiquiditySlot borrowerSlot feeReserveSlot account loanAmount repayAmount flashFee : Nat)
      (hLiqFee : Nat.beq vaultLiquiditySlot feeReserveSlot = false)
      (hLiqBor : Nat.beq vaultLiquiditySlot borrowerSlot = false)
      (hLe : loanAmount ≤ getStorage s (.map vaultLiquiditySlot account)) :
      getStorage (vaultFlashLoanMap s vaultLiquiditySlot borrowerSlot feeReserveSlot account loanAmount repayAmount flashFee) (.map vaultLiquiditySlot account) =
        getStorage s (.map vaultLiquiditySlot account) :=
    let hMissFee : StorageKey.fastBeq (.map vaultLiquiditySlot account) (.map feeReserveSlot account) = false :=
      (congrArg (· && account.beq account) hLiqFee).trans (Bool.false_and _)
    let hMissBor : StorageKey.fastBeq (.map vaultLiquiditySlot account) (.map borrowerSlot account) = false :=
      (congrArg (· && account.beq account) hLiqBor).trans (Bool.false_and _)
    (mintMap_slot_frame _ feeReserveSlot account flashFee (.map vaultLiquiditySlot account) hMissFee).trans <|
      getStorage_setStorage_same.trans <|
        (congrArg (· + loanAmount)
          ((burnMap_slot_frame _ borrowerSlot account repayAmount (.map vaultLiquiditySlot account) hMissBor).trans
            ((mintMap_slot_frame _ borrowerSlot account loanAmount (.map vaultLiquiditySlot account) hMissBor).trans
              getStorage_setStorage_same))).trans
          (Nat.sub_add_cancel hLe)

set_option maxHeartbeats 200000 in
  theorem vaultFlashLoanMap_preserves_transient (s : ContractState)
      (vaultLiquiditySlot borrowerSlot feeReserveSlot account loanAmount repayAmount flashFee tslot : Nat) :
      getStorage (vaultFlashLoanMap s vaultLiquiditySlot borrowerSlot feeReserveSlot account loanAmount repayAmount flashFee) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (mintMap_slot_frame _ feeReserveSlot account flashFee (.transient tslot) rfl).trans <|
      (mintMap_slot_frame _ vaultLiquiditySlot account loanAmount (.transient tslot) rfl).trans <|
      (burnMap_slot_frame _ borrowerSlot account repayAmount (.transient tslot) rfl).trans <|
      (mintMap_slot_frame _ borrowerSlot account loanAmount (.transient tslot) rfl).trans
        (burnMap_slot_frame s vaultLiquiditySlot account loanAmount (.transient tslot) rfl)

set_option maxHeartbeats 200000 in
  theorem guardedVaultFlashLoanMap_unlocked_after (s : ContractState)
      (lockSlot vaultLiquiditySlot borrowerSlot feeReserveSlot account loanAmount repayAmount flashFee : Nat) :
      isTransientLocked (guardedVaultFlashLoanMap s lockSlot vaultLiquiditySlot borrowerSlot feeReserveSlot account loanAmount repayAmount flashFee) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def ammSwapWithFeeMap (s : ContractState)
      (traderInSlot reserveInSlot reserveOutSlot traderOutSlot feeAccumulatorSlot account amountIn poolInDelta amountOut protocolFee : Nat) : ContractState :=
    mintMap
      (mintMap
        (burnMap
          (mintMap
            (burnMap s traderInSlot account amountIn)
            reserveInSlot account poolInDelta)
          reserveOutSlot account amountOut)
        traderOutSlot account amountOut)
      feeAccumulatorSlot account protocolFee

  def guardedAmmSwapWithFeeMap (s : ContractState)
      (lockSlot traderInSlot reserveInSlot reserveOutSlot traderOutSlot feeAccumulatorSlot account amountIn poolInDelta amountOut protocolFee : Nat) : ContractState :=
    releaseTransientLock
      (ammSwapWithFeeMap (acquireTransientLock s lockSlot) traderInSlot reserveInSlot reserveOutSlot traderOutSlot feeAccumulatorSlot account amountIn poolInDelta amountOut protocolFee)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem ammSwapWithFeeMap_other_slot_frame (s : ContractState)
      (traderInSlot reserveInSlot reserveOutSlot traderOutSlot feeAccumulatorSlot otherSlot account observer amountIn poolInDelta amountOut protocolFee : Nat)
      (hTrIn : Nat.beq otherSlot traderInSlot = false)
      (hResIn : Nat.beq otherSlot reserveInSlot = false)
      (hResOut : Nat.beq otherSlot reserveOutSlot = false)
      (hTrOut : Nat.beq otherSlot traderOutSlot = false)
      (hFee : Nat.beq otherSlot feeAccumulatorSlot = false) :
      getStorage (ammSwapWithFeeMap s traderInSlot reserveInSlot reserveOutSlot traderOutSlot feeAccumulatorSlot account amountIn poolInDelta amountOut protocolFee) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (mintMap_slot_frame _ feeAccumulatorSlot account protocolFee (.map otherSlot observer)
      ((congrArg (· && observer.beq account) hFee).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ traderOutSlot account amountOut (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hTrOut).trans (Bool.false_and _))).trans <|
      (burnMap_slot_frame _ reserveOutSlot account amountOut (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hResOut).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ reserveInSlot account poolInDelta (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hResIn).trans (Bool.false_and _))).trans
        (burnMap_slot_frame s traderInSlot account amountIn (.map otherSlot observer)
          ((congrArg (· && observer.beq account) hTrIn).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem ammSwapWithFeeMap_fee_accumulator_updated (s : ContractState)
      (traderInSlot reserveInSlot reserveOutSlot traderOutSlot feeAccumulatorSlot account amountIn poolInDelta amountOut protocolFee : Nat)
      (hFeeTrOut : Nat.beq feeAccumulatorSlot traderOutSlot = false)
      (hFeeResOut : Nat.beq feeAccumulatorSlot reserveOutSlot = false)
      (hFeeResIn : Nat.beq feeAccumulatorSlot reserveInSlot = false)
      (hFeeTrIn : Nat.beq feeAccumulatorSlot traderInSlot = false) :
      getStorage (ammSwapWithFeeMap s traderInSlot reserveInSlot reserveOutSlot traderOutSlot feeAccumulatorSlot account amountIn poolInDelta amountOut protocolFee) (.map feeAccumulatorSlot account) =
        getStorage s (.map feeAccumulatorSlot account) + protocolFee :=
    let hMissTrOut : StorageKey.fastBeq (.map feeAccumulatorSlot account) (.map traderOutSlot account) = false :=
      (congrArg (· && account.beq account) hFeeTrOut).trans (Bool.false_and _)
    let hMissResOut : StorageKey.fastBeq (.map feeAccumulatorSlot account) (.map reserveOutSlot account) = false :=
      (congrArg (· && account.beq account) hFeeResOut).trans (Bool.false_and _)
    let hMissResIn : StorageKey.fastBeq (.map feeAccumulatorSlot account) (.map reserveInSlot account) = false :=
      (congrArg (· && account.beq account) hFeeResIn).trans (Bool.false_and _)
    let hMissTrIn : StorageKey.fastBeq (.map feeAccumulatorSlot account) (.map traderInSlot account) = false :=
      (congrArg (· && account.beq account) hFeeTrIn).trans (Bool.false_and _)
    getStorage_setStorage_same.trans <|
      congrArg (· + protocolFee)
        ((mintMap_slot_frame _ traderOutSlot account amountOut (.map feeAccumulatorSlot account) hMissTrOut).trans
          ((burnMap_slot_frame _ reserveOutSlot account amountOut (.map feeAccumulatorSlot account) hMissResOut).trans
            ((mintMap_slot_frame _ reserveInSlot account poolInDelta (.map feeAccumulatorSlot account) hMissResIn).trans
              (burnMap_slot_frame s traderInSlot account amountIn (.map feeAccumulatorSlot account) hMissTrIn))))

set_option maxHeartbeats 200000 in
  theorem ammSwapWithFeeMap_trader_out_updated (s : ContractState)
      (traderInSlot reserveInSlot reserveOutSlot traderOutSlot feeAccumulatorSlot account amountIn poolInDelta amountOut protocolFee : Nat)
      (hTrOutFee : Nat.beq traderOutSlot feeAccumulatorSlot = false)
      (hTrOutResOut : Nat.beq traderOutSlot reserveOutSlot = false)
      (hTrOutResIn : Nat.beq traderOutSlot reserveInSlot = false)
      (hTrOutTrIn : Nat.beq traderOutSlot traderInSlot = false) :
      getStorage (ammSwapWithFeeMap s traderInSlot reserveInSlot reserveOutSlot traderOutSlot feeAccumulatorSlot account amountIn poolInDelta amountOut protocolFee) (.map traderOutSlot account) =
        getStorage s (.map traderOutSlot account) + amountOut :=
    let hMissFee : StorageKey.fastBeq (.map traderOutSlot account) (.map feeAccumulatorSlot account) = false :=
      (congrArg (· && account.beq account) hTrOutFee).trans (Bool.false_and _)
    let hMissResOut : StorageKey.fastBeq (.map traderOutSlot account) (.map reserveOutSlot account) = false :=
      (congrArg (· && account.beq account) hTrOutResOut).trans (Bool.false_and _)
    let hMissResIn : StorageKey.fastBeq (.map traderOutSlot account) (.map reserveInSlot account) = false :=
      (congrArg (· && account.beq account) hTrOutResIn).trans (Bool.false_and _)
    let hMissTrIn : StorageKey.fastBeq (.map traderOutSlot account) (.map traderInSlot account) = false :=
      (congrArg (· && account.beq account) hTrOutTrIn).trans (Bool.false_and _)
    (mintMap_slot_frame _ feeAccumulatorSlot account protocolFee (.map traderOutSlot account) hMissFee).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· + amountOut)
          ((burnMap_slot_frame _ reserveOutSlot account amountOut (.map traderOutSlot account) hMissResOut).trans
            ((mintMap_slot_frame _ reserveInSlot account poolInDelta (.map traderOutSlot account) hMissResIn).trans
              (burnMap_slot_frame s traderInSlot account amountIn (.map traderOutSlot account) hMissTrIn))))

set_option maxHeartbeats 200000 in
  theorem ammSwapWithFeeMap_reserve_out_updated (s : ContractState)
      (traderInSlot reserveInSlot reserveOutSlot traderOutSlot feeAccumulatorSlot account amountIn poolInDelta amountOut protocolFee : Nat)
      (hResOutFee : Nat.beq reserveOutSlot feeAccumulatorSlot = false)
      (hResOutTrOut : Nat.beq reserveOutSlot traderOutSlot = false)
      (hResOutResIn : Nat.beq reserveOutSlot reserveInSlot = false)
      (hResOutTrIn : Nat.beq reserveOutSlot traderInSlot = false) :
      getStorage (ammSwapWithFeeMap s traderInSlot reserveInSlot reserveOutSlot traderOutSlot feeAccumulatorSlot account amountIn poolInDelta amountOut protocolFee) (.map reserveOutSlot account) =
        getStorage s (.map reserveOutSlot account) - amountOut :=
    let hMissFee : StorageKey.fastBeq (.map reserveOutSlot account) (.map feeAccumulatorSlot account) = false :=
      (congrArg (· && account.beq account) hResOutFee).trans (Bool.false_and _)
    let hMissTrOut : StorageKey.fastBeq (.map reserveOutSlot account) (.map traderOutSlot account) = false :=
      (congrArg (· && account.beq account) hResOutTrOut).trans (Bool.false_and _)
    let hMissResIn : StorageKey.fastBeq (.map reserveOutSlot account) (.map reserveInSlot account) = false :=
      (congrArg (· && account.beq account) hResOutResIn).trans (Bool.false_and _)
    let hMissTrIn : StorageKey.fastBeq (.map reserveOutSlot account) (.map traderInSlot account) = false :=
      (congrArg (· && account.beq account) hResOutTrIn).trans (Bool.false_and _)
    (mintMap_slot_frame _ feeAccumulatorSlot account protocolFee (.map reserveOutSlot account) hMissFee).trans <|
      (mintMap_slot_frame _ traderOutSlot account amountOut (.map reserveOutSlot account) hMissTrOut).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· - amountOut)
          ((mintMap_slot_frame _ reserveInSlot account poolInDelta (.map reserveOutSlot account) hMissResIn).trans
            (burnMap_slot_frame s traderInSlot account amountIn (.map reserveOutSlot account) hMissTrIn)))

set_option maxHeartbeats 200000 in
  theorem guardedAmmSwapWithFeeMap_unlocked_after (s : ContractState)
      (lockSlot traderInSlot reserveInSlot reserveOutSlot traderOutSlot feeAccumulatorSlot account amountIn poolInDelta amountOut protocolFee : Nat) :
      isTransientLocked (guardedAmmSwapWithFeeMap s lockSlot traderInSlot reserveInSlot reserveOutSlot traderOutSlot feeAccumulatorSlot account amountIn poolInDelta amountOut protocolFee) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def ammAddLiquidityMap (s : ContractState)
      (providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp : Nat) : ContractState :=
    mintMap
      (mintMap
        (mintMap
          (mintMap
            (burnMap
              (burnMap s providerToken0Slot account amount0)
              providerToken1Slot account amount1)
            reserve0Slot account amount0)
          reserve1Slot account amount1)
        providerLpSlot account mintedLp)
      totalLpSupplySlot account mintedLp

  def guardedAmmAddLiquidityMap (s : ContractState)
      (lockSlot providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp : Nat) : ContractState :=
    releaseTransientLock
      (ammAddLiquidityMap (acquireTransientLock s lockSlot) providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem ammAddLiquidityMap_other_slot_frame (s : ContractState)
      (providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot otherSlot account observer amount0 amount1 mintedLp : Nat)
      (hTok0 : Nat.beq otherSlot providerToken0Slot = false)
      (hTok1 : Nat.beq otherSlot providerToken1Slot = false)
      (hRes0 : Nat.beq otherSlot reserve0Slot = false)
      (hRes1 : Nat.beq otherSlot reserve1Slot = false)
      (hProvLp : Nat.beq otherSlot providerLpSlot = false)
      (hTotLp : Nat.beq otherSlot totalLpSupplySlot = false) :
      getStorage (ammAddLiquidityMap s providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (mintMap_slot_frame _ totalLpSupplySlot account mintedLp (.map otherSlot observer)
      ((congrArg (· && observer.beq account) hTotLp).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ providerLpSlot account mintedLp (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hProvLp).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ reserve1Slot account amount1 (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hRes1).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ reserve0Slot account amount0 (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hRes0).trans (Bool.false_and _))).trans <|
      (burnMap_slot_frame _ providerToken1Slot account amount1 (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hTok1).trans (Bool.false_and _))).trans
        (burnMap_slot_frame s providerToken0Slot account amount0 (.map otherSlot observer)
          ((congrArg (· && observer.beq account) hTok0).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem ammAddLiquidityMap_total_lp_updated (s : ContractState)
      (providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp : Nat)
      (hTotProvLp : Nat.beq totalLpSupplySlot providerLpSlot = false)
      (hTotRes1 : Nat.beq totalLpSupplySlot reserve1Slot = false)
      (hTotRes0 : Nat.beq totalLpSupplySlot reserve0Slot = false)
      (hTotTok1 : Nat.beq totalLpSupplySlot providerToken1Slot = false)
      (hTotTok0 : Nat.beq totalLpSupplySlot providerToken0Slot = false) :
      getStorage (ammAddLiquidityMap s providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp) (.map totalLpSupplySlot account) =
        getStorage s (.map totalLpSupplySlot account) + mintedLp :=
    let hMissProvLp : StorageKey.fastBeq (.map totalLpSupplySlot account) (.map providerLpSlot account) = false :=
      (congrArg (· && account.beq account) hTotProvLp).trans (Bool.false_and _)
    let hMissRes1 : StorageKey.fastBeq (.map totalLpSupplySlot account) (.map reserve1Slot account) = false :=
      (congrArg (· && account.beq account) hTotRes1).trans (Bool.false_and _)
    let hMissRes0 : StorageKey.fastBeq (.map totalLpSupplySlot account) (.map reserve0Slot account) = false :=
      (congrArg (· && account.beq account) hTotRes0).trans (Bool.false_and _)
    let hMissTok1 : StorageKey.fastBeq (.map totalLpSupplySlot account) (.map providerToken1Slot account) = false :=
      (congrArg (· && account.beq account) hTotTok1).trans (Bool.false_and _)
    let hMissTok0 : StorageKey.fastBeq (.map totalLpSupplySlot account) (.map providerToken0Slot account) = false :=
      (congrArg (· && account.beq account) hTotTok0).trans (Bool.false_and _)
    getStorage_setStorage_same.trans <|
      congrArg (· + mintedLp)
        ((mintMap_slot_frame _ providerLpSlot account mintedLp (.map totalLpSupplySlot account) hMissProvLp).trans
          ((mintMap_slot_frame _ reserve1Slot account amount1 (.map totalLpSupplySlot account) hMissRes1).trans
            ((mintMap_slot_frame _ reserve0Slot account amount0 (.map totalLpSupplySlot account) hMissRes0).trans
              ((burnMap_slot_frame _ providerToken1Slot account amount1 (.map totalLpSupplySlot account) hMissTok1).trans
                (burnMap_slot_frame s providerToken0Slot account amount0 (.map totalLpSupplySlot account) hMissTok0)))))

set_option maxHeartbeats 200000 in
  theorem ammAddLiquidityMap_provider_lp_updated (s : ContractState)
      (providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp : Nat)
      (hProvTotLp : Nat.beq providerLpSlot totalLpSupplySlot = false)
      (hProvRes1 : Nat.beq providerLpSlot reserve1Slot = false)
      (hProvRes0 : Nat.beq providerLpSlot reserve0Slot = false)
      (hProvTok1 : Nat.beq providerLpSlot providerToken1Slot = false)
      (hProvTok0 : Nat.beq providerLpSlot providerToken0Slot = false) :
      getStorage (ammAddLiquidityMap s providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp) (.map providerLpSlot account) =
        getStorage s (.map providerLpSlot account) + mintedLp :=
    let hMissTotLp : StorageKey.fastBeq (.map providerLpSlot account) (.map totalLpSupplySlot account) = false :=
      (congrArg (· && account.beq account) hProvTotLp).trans (Bool.false_and _)
    let hMissRes1 : StorageKey.fastBeq (.map providerLpSlot account) (.map reserve1Slot account) = false :=
      (congrArg (· && account.beq account) hProvRes1).trans (Bool.false_and _)
    let hMissRes0 : StorageKey.fastBeq (.map providerLpSlot account) (.map reserve0Slot account) = false :=
      (congrArg (· && account.beq account) hProvRes0).trans (Bool.false_and _)
    let hMissTok1 : StorageKey.fastBeq (.map providerLpSlot account) (.map providerToken1Slot account) = false :=
      (congrArg (· && account.beq account) hProvTok1).trans (Bool.false_and _)
    let hMissTok0 : StorageKey.fastBeq (.map providerLpSlot account) (.map providerToken0Slot account) = false :=
      (congrArg (· && account.beq account) hProvTok0).trans (Bool.false_and _)
    (mintMap_slot_frame _ totalLpSupplySlot account mintedLp (.map providerLpSlot account) hMissTotLp).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· + mintedLp)
          ((mintMap_slot_frame _ reserve1Slot account amount1 (.map providerLpSlot account) hMissRes1).trans
            ((mintMap_slot_frame _ reserve0Slot account amount0 (.map providerLpSlot account) hMissRes0).trans
              ((burnMap_slot_frame _ providerToken1Slot account amount1 (.map providerLpSlot account) hMissTok1).trans
                (burnMap_slot_frame s providerToken0Slot account amount0 (.map providerLpSlot account) hMissTok0)))))

set_option maxHeartbeats 200000 in
  theorem ammAddLiquidityMap_reserve1_updated (s : ContractState)
      (providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp : Nat)
      (hRes1TotLp : Nat.beq reserve1Slot totalLpSupplySlot = false)
      (hRes1ProvLp : Nat.beq reserve1Slot providerLpSlot = false)
      (hRes1Res0 : Nat.beq reserve1Slot reserve0Slot = false)
      (hRes1Tok1 : Nat.beq reserve1Slot providerToken1Slot = false)
      (hRes1Tok0 : Nat.beq reserve1Slot providerToken0Slot = false) :
      getStorage (ammAddLiquidityMap s providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp) (.map reserve1Slot account) =
        getStorage s (.map reserve1Slot account) + amount1 :=
    let hMissTotLp : StorageKey.fastBeq (.map reserve1Slot account) (.map totalLpSupplySlot account) = false :=
      (congrArg (· && account.beq account) hRes1TotLp).trans (Bool.false_and _)
    let hMissProvLp : StorageKey.fastBeq (.map reserve1Slot account) (.map providerLpSlot account) = false :=
      (congrArg (· && account.beq account) hRes1ProvLp).trans (Bool.false_and _)
    let hMissRes0 : StorageKey.fastBeq (.map reserve1Slot account) (.map reserve0Slot account) = false :=
      (congrArg (· && account.beq account) hRes1Res0).trans (Bool.false_and _)
    let hMissTok1 : StorageKey.fastBeq (.map reserve1Slot account) (.map providerToken1Slot account) = false :=
      (congrArg (· && account.beq account) hRes1Tok1).trans (Bool.false_and _)
    let hMissTok0 : StorageKey.fastBeq (.map reserve1Slot account) (.map providerToken0Slot account) = false :=
      (congrArg (· && account.beq account) hRes1Tok0).trans (Bool.false_and _)
    (mintMap_slot_frame _ totalLpSupplySlot account mintedLp (.map reserve1Slot account) hMissTotLp).trans <|
      (mintMap_slot_frame _ providerLpSlot account mintedLp (.map reserve1Slot account) hMissProvLp).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· + amount1)
          ((mintMap_slot_frame _ reserve0Slot account amount0 (.map reserve1Slot account) hMissRes0).trans
            ((burnMap_slot_frame _ providerToken1Slot account amount1 (.map reserve1Slot account) hMissTok1).trans
              (burnMap_slot_frame s providerToken0Slot account amount0 (.map reserve1Slot account) hMissTok0))))

set_option maxHeartbeats 200000 in
  theorem guardedAmmAddLiquidityMap_unlocked_after (s : ContractState)
      (lockSlot providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp : Nat) :
      isTransientLocked (guardedAmmAddLiquidityMap s lockSlot providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def ammRemoveLiquidityMap (s : ContractState)
      (providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 burnedLp : Nat) : ContractState :=
    mintMap
      (mintMap
        (burnMap
          (burnMap
            (burnMap
              (burnMap s providerLpSlot account burnedLp)
              totalLpSupplySlot account burnedLp)
            reserve0Slot account amount0)
          reserve1Slot account amount1)
        providerToken0Slot account amount0)
      providerToken1Slot account amount1

  def guardedAmmRemoveLiquidityMap (s : ContractState)
      (lockSlot providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 burnedLp : Nat) : ContractState :=
    releaseTransientLock
      (ammRemoveLiquidityMap (acquireTransientLock s lockSlot) providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 burnedLp)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem ammRemoveLiquidityMap_other_slot_frame (s : ContractState)
      (providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot otherSlot account observer amount0 amount1 burnedLp : Nat)
      (hTok0 : Nat.beq otherSlot providerToken0Slot = false)
      (hTok1 : Nat.beq otherSlot providerToken1Slot = false)
      (hRes0 : Nat.beq otherSlot reserve0Slot = false)
      (hRes1 : Nat.beq otherSlot reserve1Slot = false)
      (hProvLp : Nat.beq otherSlot providerLpSlot = false)
      (hTotLp : Nat.beq otherSlot totalLpSupplySlot = false) :
      getStorage (ammRemoveLiquidityMap s providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 burnedLp) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (mintMap_slot_frame _ providerToken1Slot account amount1 (.map otherSlot observer)
      ((congrArg (· && observer.beq account) hTok1).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ providerToken0Slot account amount0 (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hTok0).trans (Bool.false_and _))).trans <|
      (burnMap_slot_frame _ reserve1Slot account amount1 (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hRes1).trans (Bool.false_and _))).trans <|
      (burnMap_slot_frame _ reserve0Slot account amount0 (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hRes0).trans (Bool.false_and _))).trans <|
      (burnMap_slot_frame _ totalLpSupplySlot account burnedLp (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hTotLp).trans (Bool.false_and _))).trans
        (burnMap_slot_frame s providerLpSlot account burnedLp (.map otherSlot observer)
          ((congrArg (· && observer.beq account) hProvLp).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem ammRemoveLiquidityMap_provider_token1_updated (s : ContractState)
      (providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 burnedLp : Nat)
      (hTok1Tok0 : Nat.beq providerToken1Slot providerToken0Slot = false)
      (hTok1Res1 : Nat.beq providerToken1Slot reserve1Slot = false)
      (hTok1Res0 : Nat.beq providerToken1Slot reserve0Slot = false)
      (hTok1TotLp : Nat.beq providerToken1Slot totalLpSupplySlot = false)
      (hTok1ProvLp : Nat.beq providerToken1Slot providerLpSlot = false) :
      getStorage (ammRemoveLiquidityMap s providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 burnedLp) (.map providerToken1Slot account) =
        getStorage s (.map providerToken1Slot account) + amount1 :=
    let hMissTok0 : StorageKey.fastBeq (.map providerToken1Slot account) (.map providerToken0Slot account) = false :=
      (congrArg (· && account.beq account) hTok1Tok0).trans (Bool.false_and _)
    let hMissRes1 : StorageKey.fastBeq (.map providerToken1Slot account) (.map reserve1Slot account) = false :=
      (congrArg (· && account.beq account) hTok1Res1).trans (Bool.false_and _)
    let hMissRes0 : StorageKey.fastBeq (.map providerToken1Slot account) (.map reserve0Slot account) = false :=
      (congrArg (· && account.beq account) hTok1Res0).trans (Bool.false_and _)
    let hMissTotLp : StorageKey.fastBeq (.map providerToken1Slot account) (.map totalLpSupplySlot account) = false :=
      (congrArg (· && account.beq account) hTok1TotLp).trans (Bool.false_and _)
    let hMissProvLp : StorageKey.fastBeq (.map providerToken1Slot account) (.map providerLpSlot account) = false :=
      (congrArg (· && account.beq account) hTok1ProvLp).trans (Bool.false_and _)
    getStorage_setStorage_same.trans <|
      congrArg (· + amount1)
        ((mintMap_slot_frame _ providerToken0Slot account amount0 (.map providerToken1Slot account) hMissTok0).trans
          ((burnMap_slot_frame _ reserve1Slot account amount1 (.map providerToken1Slot account) hMissRes1).trans
            ((burnMap_slot_frame _ reserve0Slot account amount0 (.map providerToken1Slot account) hMissRes0).trans
              ((burnMap_slot_frame _ totalLpSupplySlot account burnedLp (.map providerToken1Slot account) hMissTotLp).trans
                (burnMap_slot_frame s providerLpSlot account burnedLp (.map providerToken1Slot account) hMissProvLp)))))

set_option maxHeartbeats 200000 in
  theorem ammRemoveLiquidityMap_provider_token0_updated (s : ContractState)
      (providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 burnedLp : Nat)
      (hTok0Tok1 : Nat.beq providerToken0Slot providerToken1Slot = false)
      (hTok0Res1 : Nat.beq providerToken0Slot reserve1Slot = false)
      (hTok0Res0 : Nat.beq providerToken0Slot reserve0Slot = false)
      (hTok0TotLp : Nat.beq providerToken0Slot totalLpSupplySlot = false)
      (hTok0ProvLp : Nat.beq providerToken0Slot providerLpSlot = false) :
      getStorage (ammRemoveLiquidityMap s providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 burnedLp) (.map providerToken0Slot account) =
        getStorage s (.map providerToken0Slot account) + amount0 :=
    let hMissTok1 : StorageKey.fastBeq (.map providerToken0Slot account) (.map providerToken1Slot account) = false :=
      (congrArg (· && account.beq account) hTok0Tok1).trans (Bool.false_and _)
    let hMissRes1 : StorageKey.fastBeq (.map providerToken0Slot account) (.map reserve1Slot account) = false :=
      (congrArg (· && account.beq account) hTok0Res1).trans (Bool.false_and _)
    let hMissRes0 : StorageKey.fastBeq (.map providerToken0Slot account) (.map reserve0Slot account) = false :=
      (congrArg (· && account.beq account) hTok0Res0).trans (Bool.false_and _)
    let hMissTotLp : StorageKey.fastBeq (.map providerToken0Slot account) (.map totalLpSupplySlot account) = false :=
      (congrArg (· && account.beq account) hTok0TotLp).trans (Bool.false_and _)
    let hMissProvLp : StorageKey.fastBeq (.map providerToken0Slot account) (.map providerLpSlot account) = false :=
      (congrArg (· && account.beq account) hTok0ProvLp).trans (Bool.false_and _)
    (mintMap_slot_frame _ providerToken1Slot account amount1 (.map providerToken0Slot account) hMissTok1).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· + amount0)
          ((burnMap_slot_frame _ reserve1Slot account amount1 (.map providerToken0Slot account) hMissRes1).trans
            ((burnMap_slot_frame _ reserve0Slot account amount0 (.map providerToken0Slot account) hMissRes0).trans
              ((burnMap_slot_frame _ totalLpSupplySlot account burnedLp (.map providerToken0Slot account) hMissTotLp).trans
                (burnMap_slot_frame s providerLpSlot account burnedLp (.map providerToken0Slot account) hMissProvLp)))))

set_option maxHeartbeats 200000 in
  theorem ammRemoveLiquidityMap_reserve1_updated (s : ContractState)
      (providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 burnedLp : Nat)
      (hRes1Tok1 : Nat.beq reserve1Slot providerToken1Slot = false)
      (hRes1Tok0 : Nat.beq reserve1Slot providerToken0Slot = false)
      (hRes1Res0 : Nat.beq reserve1Slot reserve0Slot = false)
      (hRes1TotLp : Nat.beq reserve1Slot totalLpSupplySlot = false)
      (hRes1ProvLp : Nat.beq reserve1Slot providerLpSlot = false) :
      getStorage (ammRemoveLiquidityMap s providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 burnedLp) (.map reserve1Slot account) =
        getStorage s (.map reserve1Slot account) - amount1 :=
    let hMissTok1 : StorageKey.fastBeq (.map reserve1Slot account) (.map providerToken1Slot account) = false :=
      (congrArg (· && account.beq account) hRes1Tok1).trans (Bool.false_and _)
    let hMissTok0 : StorageKey.fastBeq (.map reserve1Slot account) (.map providerToken0Slot account) = false :=
      (congrArg (· && account.beq account) hRes1Tok0).trans (Bool.false_and _)
    let hMissRes0 : StorageKey.fastBeq (.map reserve1Slot account) (.map reserve0Slot account) = false :=
      (congrArg (· && account.beq account) hRes1Res0).trans (Bool.false_and _)
    let hMissTotLp : StorageKey.fastBeq (.map reserve1Slot account) (.map totalLpSupplySlot account) = false :=
      (congrArg (· && account.beq account) hRes1TotLp).trans (Bool.false_and _)
    let hMissProvLp : StorageKey.fastBeq (.map reserve1Slot account) (.map providerLpSlot account) = false :=
      (congrArg (· && account.beq account) hRes1ProvLp).trans (Bool.false_and _)
    (mintMap_slot_frame _ providerToken1Slot account amount1 (.map reserve1Slot account) hMissTok1).trans <|
      (mintMap_slot_frame _ providerToken0Slot account amount0 (.map reserve1Slot account) hMissTok0).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· - amount1)
          ((burnMap_slot_frame _ reserve0Slot account amount0 (.map reserve1Slot account) hMissRes0).trans
            ((burnMap_slot_frame _ totalLpSupplySlot account burnedLp (.map reserve1Slot account) hMissTotLp).trans
              (burnMap_slot_frame s providerLpSlot account burnedLp (.map reserve1Slot account) hMissProvLp))))

set_option maxHeartbeats 200000 in
  theorem guardedAmmRemoveLiquidityMap_unlocked_after (s : ContractState)
      (lockSlot providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 burnedLp : Nat) :
      isTransientLocked (guardedAmmRemoveLiquidityMap s lockSlot providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 burnedLp) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def ammLiquidityRoundTripMap (s : ContractState)
      (providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp : Nat) : ContractState :=
    ammRemoveLiquidityMap
      (ammAddLiquidityMap s providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp)
      providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp

  def guardedAmmLiquidityRoundTripMap (s : ContractState)
      (lockSlot providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp : Nat) : ContractState :=
    releaseTransientLock
      (ammLiquidityRoundTripMap (acquireTransientLock s lockSlot) providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem ammLiquidityRoundTripMap_other_slot_frame (s : ContractState)
      (providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot otherSlot account observer amount0 amount1 mintedLp : Nat)
      (hTok0 : Nat.beq otherSlot providerToken0Slot = false)
      (hTok1 : Nat.beq otherSlot providerToken1Slot = false)
      (hRes0 : Nat.beq otherSlot reserve0Slot = false)
      (hRes1 : Nat.beq otherSlot reserve1Slot = false)
      (hProvLp : Nat.beq otherSlot providerLpSlot = false)
      (hTotLp : Nat.beq otherSlot totalLpSupplySlot = false) :
      getStorage (ammLiquidityRoundTripMap s providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (ammRemoveLiquidityMap_other_slot_frame _ providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot otherSlot account observer amount0 amount1 mintedLp hTok0 hTok1 hRes0 hRes1 hProvLp hTotLp).trans
      (ammAddLiquidityMap_other_slot_frame s providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot otherSlot account observer amount0 amount1 mintedLp hTok0 hTok1 hRes0 hRes1 hProvLp hTotLp)

set_option maxHeartbeats 200000 in
  theorem ammLiquidityRoundTripMap_provider_token1_exact_restore (s : ContractState)
      (providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp : Nat)
      (hTok1Tok0 : Nat.beq providerToken1Slot providerToken0Slot = false)
      (hTok1Res1 : Nat.beq providerToken1Slot reserve1Slot = false)
      (hTok1Res0 : Nat.beq providerToken1Slot reserve0Slot = false)
      (hTok1TotLp : Nat.beq providerToken1Slot totalLpSupplySlot = false)
      (hTok1ProvLp : Nat.beq providerToken1Slot providerLpSlot = false)
      (hLe : amount1 ≤ getStorage s (.map providerToken1Slot account)) :
      getStorage (ammLiquidityRoundTripMap s providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp) (.map providerToken1Slot account) =
        getStorage s (.map providerToken1Slot account) :=
    let hMissTok0 : StorageKey.fastBeq (.map providerToken1Slot account) (.map providerToken0Slot account) = false :=
      (congrArg (· && account.beq account) hTok1Tok0).trans (Bool.false_and _)
    let hMissRes1 : StorageKey.fastBeq (.map providerToken1Slot account) (.map reserve1Slot account) = false :=
      (congrArg (· && account.beq account) hTok1Res1).trans (Bool.false_and _)
    let hMissRes0 : StorageKey.fastBeq (.map providerToken1Slot account) (.map reserve0Slot account) = false :=
      (congrArg (· && account.beq account) hTok1Res0).trans (Bool.false_and _)
    let hMissTotLp : StorageKey.fastBeq (.map providerToken1Slot account) (.map totalLpSupplySlot account) = false :=
      (congrArg (· && account.beq account) hTok1TotLp).trans (Bool.false_and _)
    let hMissProvLp : StorageKey.fastBeq (.map providerToken1Slot account) (.map providerLpSlot account) = false :=
      (congrArg (· && account.beq account) hTok1ProvLp).trans (Bool.false_and _)
    (ammRemoveLiquidityMap_provider_token1_updated _ providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp hTok1Tok0 hTok1Res1 hTok1Res0 hTok1TotLp hTok1ProvLp).trans <|
      (congrArg (· + amount1)
        ((mintMap_slot_frame _ totalLpSupplySlot account mintedLp (.map providerToken1Slot account) hMissTotLp).trans
          ((mintMap_slot_frame _ providerLpSlot account mintedLp (.map providerToken1Slot account) hMissProvLp).trans
            ((mintMap_slot_frame _ reserve1Slot account amount1 (.map providerToken1Slot account) hMissRes1).trans
              ((mintMap_slot_frame _ reserve0Slot account amount0 (.map providerToken1Slot account) hMissRes0).trans
                (getStorage_setStorage_same.trans
                  (congrArg (· - amount1)
                    (burnMap_slot_frame s providerToken0Slot account amount0 (.map providerToken1Slot account) hMissTok0)))))))).trans
        (Nat.sub_add_cancel hLe)

set_option maxHeartbeats 200000 in
  theorem ammLiquidityRoundTripMap_reserve1_exact_restore (s : ContractState)
      (providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp : Nat)
      (hRes1Tok1 : Nat.beq reserve1Slot providerToken1Slot = false)
      (hRes1Tok0 : Nat.beq reserve1Slot providerToken0Slot = false)
      (hRes1Res0 : Nat.beq reserve1Slot reserve0Slot = false)
      (hRes1TotLp : Nat.beq reserve1Slot totalLpSupplySlot = false)
      (hRes1ProvLp : Nat.beq reserve1Slot providerLpSlot = false) :
      getStorage (ammLiquidityRoundTripMap s providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp) (.map reserve1Slot account) =
        getStorage s (.map reserve1Slot account) :=
    (ammRemoveLiquidityMap_reserve1_updated _ providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp hRes1Tok1 hRes1Tok0 hRes1Res0 hRes1TotLp hRes1ProvLp).trans <|
      (congrArg (· - amount1)
        (ammAddLiquidityMap_reserve1_updated s providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp hRes1TotLp hRes1ProvLp hRes1Res0 hRes1Tok1 hRes1Tok0)).trans
        (Nat.add_sub_cancel (getStorage s (.map reserve1Slot account)) amount1)

set_option maxHeartbeats 200000 in
  theorem ammLiquidityRoundTripMap_preserves_transient (s : ContractState)
      (providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp tslot : Nat) :
      getStorage (ammLiquidityRoundTripMap s providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (mintMap_slot_frame _ providerToken1Slot account amount1 (.transient tslot) rfl).trans <|
      (mintMap_slot_frame _ providerToken0Slot account amount0 (.transient tslot) rfl).trans <|
      (burnMap_slot_frame _ reserve1Slot account amount1 (.transient tslot) rfl).trans <|
      (burnMap_slot_frame _ reserve0Slot account amount0 (.transient tslot) rfl).trans <|
      (burnMap_slot_frame _ totalLpSupplySlot account mintedLp (.transient tslot) rfl).trans <|
      (burnMap_slot_frame _ providerLpSlot account mintedLp (.transient tslot) rfl).trans <|
      (mintMap_slot_frame _ totalLpSupplySlot account mintedLp (.transient tslot) rfl).trans <|
      (mintMap_slot_frame _ providerLpSlot account mintedLp (.transient tslot) rfl).trans <|
      (mintMap_slot_frame _ reserve1Slot account amount1 (.transient tslot) rfl).trans <|
      (mintMap_slot_frame _ reserve0Slot account amount0 (.transient tslot) rfl).trans <|
      (burnMap_slot_frame _ providerToken1Slot account amount1 (.transient tslot) rfl).trans
        (burnMap_slot_frame s providerToken0Slot account amount0 (.transient tslot) rfl)

set_option maxHeartbeats 200000 in
  theorem guardedAmmLiquidityRoundTripMap_unlocked_after (s : ContractState)
      (lockSlot providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp : Nat) :
      isTransientLocked (guardedAmmLiquidityRoundTripMap s lockSlot providerToken0Slot providerToken1Slot reserve0Slot reserve1Slot providerLpSlot totalLpSupplySlot account amount0 amount1 mintedLp) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def ammMultiHopSwapMap (s : ContractState)
      (traderASlot reserveA1Slot reserveB1Slot reserveB2Slot reserveC2Slot traderCSlot account amountInA midAmountB amountOutC : Nat) : ContractState :=
    mintMap
      (burnMap
        (mintMap
          (burnMap
            (mintMap
              (burnMap s traderASlot account amountInA)
              reserveA1Slot account amountInA)
            reserveB1Slot account midAmountB)
          reserveB2Slot account midAmountB)
        reserveC2Slot account amountOutC)
      traderCSlot account amountOutC

  def guardedAmmMultiHopSwapMap (s : ContractState)
      (lockSlot traderASlot reserveA1Slot reserveB1Slot reserveB2Slot reserveC2Slot traderCSlot account amountInA midAmountB amountOutC : Nat) : ContractState :=
    releaseTransientLock
      (ammMultiHopSwapMap (acquireTransientLock s lockSlot) traderASlot reserveA1Slot reserveB1Slot reserveB2Slot reserveC2Slot traderCSlot account amountInA midAmountB amountOutC)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem ammMultiHopSwapMap_other_slot_frame (s : ContractState)
      (traderASlot reserveA1Slot reserveB1Slot reserveB2Slot reserveC2Slot traderCSlot otherSlot account observer amountInA midAmountB amountOutC : Nat)
      (hTrA : Nat.beq otherSlot traderASlot = false)
      (hResA1 : Nat.beq otherSlot reserveA1Slot = false)
      (hResB1 : Nat.beq otherSlot reserveB1Slot = false)
      (hResB2 : Nat.beq otherSlot reserveB2Slot = false)
      (hResC2 : Nat.beq otherSlot reserveC2Slot = false)
      (hTrC : Nat.beq otherSlot traderCSlot = false) :
      getStorage (ammMultiHopSwapMap s traderASlot reserveA1Slot reserveB1Slot reserveB2Slot reserveC2Slot traderCSlot account amountInA midAmountB amountOutC) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (mintMap_slot_frame _ traderCSlot account amountOutC (.map otherSlot observer)
      ((congrArg (· && observer.beq account) hTrC).trans (Bool.false_and _))).trans <|
      (burnMap_slot_frame _ reserveC2Slot account amountOutC (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hResC2).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ reserveB2Slot account midAmountB (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hResB2).trans (Bool.false_and _))).trans <|
      (burnMap_slot_frame _ reserveB1Slot account midAmountB (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hResB1).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ reserveA1Slot account amountInA (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hResA1).trans (Bool.false_and _))).trans
        (burnMap_slot_frame s traderASlot account amountInA (.map otherSlot observer)
          ((congrArg (· && observer.beq account) hTrA).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem ammMultiHopSwapMap_traderC_updated (s : ContractState)
      (traderASlot reserveA1Slot reserveB1Slot reserveB2Slot reserveC2Slot traderCSlot account amountInA midAmountB amountOutC : Nat)
      (hTrCResC2 : Nat.beq traderCSlot reserveC2Slot = false)
      (hTrCResB2 : Nat.beq traderCSlot reserveB2Slot = false)
      (hTrCResB1 : Nat.beq traderCSlot reserveB1Slot = false)
      (hTrCResA1 : Nat.beq traderCSlot reserveA1Slot = false)
      (hTrCTrA : Nat.beq traderCSlot traderASlot = false) :
      getStorage (ammMultiHopSwapMap s traderASlot reserveA1Slot reserveB1Slot reserveB2Slot reserveC2Slot traderCSlot account amountInA midAmountB amountOutC) (.map traderCSlot account) =
        getStorage s (.map traderCSlot account) + amountOutC :=
    let hMissResC2 : StorageKey.fastBeq (.map traderCSlot account) (.map reserveC2Slot account) = false :=
      (congrArg (· && account.beq account) hTrCResC2).trans (Bool.false_and _)
    let hMissResB2 : StorageKey.fastBeq (.map traderCSlot account) (.map reserveB2Slot account) = false :=
      (congrArg (· && account.beq account) hTrCResB2).trans (Bool.false_and _)
    let hMissResB1 : StorageKey.fastBeq (.map traderCSlot account) (.map reserveB1Slot account) = false :=
      (congrArg (· && account.beq account) hTrCResB1).trans (Bool.false_and _)
    let hMissResA1 : StorageKey.fastBeq (.map traderCSlot account) (.map reserveA1Slot account) = false :=
      (congrArg (· && account.beq account) hTrCResA1).trans (Bool.false_and _)
    let hMissTrA : StorageKey.fastBeq (.map traderCSlot account) (.map traderASlot account) = false :=
      (congrArg (· && account.beq account) hTrCTrA).trans (Bool.false_and _)
    getStorage_setStorage_same.trans <|
      congrArg (· + amountOutC)
        ((burnMap_slot_frame _ reserveC2Slot account amountOutC (.map traderCSlot account) hMissResC2).trans
          ((mintMap_slot_frame _ reserveB2Slot account midAmountB (.map traderCSlot account) hMissResB2).trans
            ((burnMap_slot_frame _ reserveB1Slot account midAmountB (.map traderCSlot account) hMissResB1).trans
              ((mintMap_slot_frame _ reserveA1Slot account amountInA (.map traderCSlot account) hMissResA1).trans
                (burnMap_slot_frame s traderASlot account amountInA (.map traderCSlot account) hMissTrA)))))

set_option maxHeartbeats 200000 in
  theorem ammMultiHopSwapMap_reserveC2_updated (s : ContractState)
      (traderASlot reserveA1Slot reserveB1Slot reserveB2Slot reserveC2Slot traderCSlot account amountInA midAmountB amountOutC : Nat)
      (hResC2TrC : Nat.beq reserveC2Slot traderCSlot = false)
      (hResC2ResB2 : Nat.beq reserveC2Slot reserveB2Slot = false)
      (hResC2ResB1 : Nat.beq reserveC2Slot reserveB1Slot = false)
      (hResC2ResA1 : Nat.beq reserveC2Slot reserveA1Slot = false)
      (hResC2TrA : Nat.beq reserveC2Slot traderASlot = false) :
      getStorage (ammMultiHopSwapMap s traderASlot reserveA1Slot reserveB1Slot reserveB2Slot reserveC2Slot traderCSlot account amountInA midAmountB amountOutC) (.map reserveC2Slot account) =
        getStorage s (.map reserveC2Slot account) - amountOutC :=
    let hMissTrC : StorageKey.fastBeq (.map reserveC2Slot account) (.map traderCSlot account) = false :=
      (congrArg (· && account.beq account) hResC2TrC).trans (Bool.false_and _)
    let hMissResB2 : StorageKey.fastBeq (.map reserveC2Slot account) (.map reserveB2Slot account) = false :=
      (congrArg (· && account.beq account) hResC2ResB2).trans (Bool.false_and _)
    let hMissResB1 : StorageKey.fastBeq (.map reserveC2Slot account) (.map reserveB1Slot account) = false :=
      (congrArg (· && account.beq account) hResC2ResB1).trans (Bool.false_and _)
    let hMissResA1 : StorageKey.fastBeq (.map reserveC2Slot account) (.map reserveA1Slot account) = false :=
      (congrArg (· && account.beq account) hResC2ResA1).trans (Bool.false_and _)
    let hMissTrA : StorageKey.fastBeq (.map reserveC2Slot account) (.map traderASlot account) = false :=
      (congrArg (· && account.beq account) hResC2TrA).trans (Bool.false_and _)
    (mintMap_slot_frame _ traderCSlot account amountOutC (.map reserveC2Slot account) hMissTrC).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· - amountOutC)
          ((mintMap_slot_frame _ reserveB2Slot account midAmountB (.map reserveC2Slot account) hMissResB2).trans
            ((burnMap_slot_frame _ reserveB1Slot account midAmountB (.map reserveC2Slot account) hMissResB1).trans
              ((mintMap_slot_frame _ reserveA1Slot account amountInA (.map reserveC2Slot account) hMissResA1).trans
                (burnMap_slot_frame s traderASlot account amountInA (.map reserveC2Slot account) hMissTrA)))))

set_option maxHeartbeats 200000 in
  theorem ammMultiHopSwapMap_reserveB2_updated (s : ContractState)
      (traderASlot reserveA1Slot reserveB1Slot reserveB2Slot reserveC2Slot traderCSlot account amountInA midAmountB amountOutC : Nat)
      (hResB2TrC : Nat.beq reserveB2Slot traderCSlot = false)
      (hResB2ResC2 : Nat.beq reserveB2Slot reserveC2Slot = false)
      (hResB2ResB1 : Nat.beq reserveB2Slot reserveB1Slot = false)
      (hResB2ResA1 : Nat.beq reserveB2Slot reserveA1Slot = false)
      (hResB2TrA : Nat.beq reserveB2Slot traderASlot = false) :
      getStorage (ammMultiHopSwapMap s traderASlot reserveA1Slot reserveB1Slot reserveB2Slot reserveC2Slot traderCSlot account amountInA midAmountB amountOutC) (.map reserveB2Slot account) =
        getStorage s (.map reserveB2Slot account) + midAmountB :=
    let hMissTrC : StorageKey.fastBeq (.map reserveB2Slot account) (.map traderCSlot account) = false :=
      (congrArg (· && account.beq account) hResB2TrC).trans (Bool.false_and _)
    let hMissResC2 : StorageKey.fastBeq (.map reserveB2Slot account) (.map reserveC2Slot account) = false :=
      (congrArg (· && account.beq account) hResB2ResC2).trans (Bool.false_and _)
    let hMissResB1 : StorageKey.fastBeq (.map reserveB2Slot account) (.map reserveB1Slot account) = false :=
      (congrArg (· && account.beq account) hResB2ResB1).trans (Bool.false_and _)
    let hMissResA1 : StorageKey.fastBeq (.map reserveB2Slot account) (.map reserveA1Slot account) = false :=
      (congrArg (· && account.beq account) hResB2ResA1).trans (Bool.false_and _)
    let hMissTrA : StorageKey.fastBeq (.map reserveB2Slot account) (.map traderASlot account) = false :=
      (congrArg (· && account.beq account) hResB2TrA).trans (Bool.false_and _)
    (mintMap_slot_frame _ traderCSlot account amountOutC (.map reserveB2Slot account) hMissTrC).trans <|
      (burnMap_slot_frame _ reserveC2Slot account amountOutC (.map reserveB2Slot account) hMissResC2).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· + midAmountB)
          ((burnMap_slot_frame _ reserveB1Slot account midAmountB (.map reserveB2Slot account) hMissResB1).trans
            ((mintMap_slot_frame _ reserveA1Slot account amountInA (.map reserveB2Slot account) hMissResA1).trans
              (burnMap_slot_frame s traderASlot account amountInA (.map reserveB2Slot account) hMissTrA))))

set_option maxHeartbeats 200000 in
  theorem guardedAmmMultiHopSwapMap_unlocked_after (s : ContractState)
      (lockSlot traderASlot reserveA1Slot reserveB1Slot reserveB2Slot reserveC2Slot traderCSlot account amountInA midAmountB amountOutC : Nat) :
      isTransientLocked (guardedAmmMultiHopSwapMap s lockSlot traderASlot reserveA1Slot reserveB1Slot reserveB2Slot reserveC2Slot traderCSlot account amountInA midAmountB amountOutC) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def ammTwapOracleUpdateMap (s : ContractState)
      (price0CumulativeSlot price1CumulativeSlot lastTimestampSlot observationIndexSlot account price0Delta price1Delta newTimestamp indexStep : Nat) : ContractState :=
    mintMap
      (setStorage
        (mintMap
          (mintMap s price0CumulativeSlot account price0Delta)
          price1CumulativeSlot account price1Delta)
        (.map lastTimestampSlot account)
        newTimestamp)
      observationIndexSlot account indexStep

  def guardedAmmTwapOracleUpdateMap (s : ContractState)
      (lockSlot price0CumulativeSlot price1CumulativeSlot lastTimestampSlot observationIndexSlot account price0Delta price1Delta newTimestamp indexStep : Nat) : ContractState :=
    releaseTransientLock
      (ammTwapOracleUpdateMap (acquireTransientLock s lockSlot) price0CumulativeSlot price1CumulativeSlot lastTimestampSlot observationIndexSlot account price0Delta price1Delta newTimestamp indexStep)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem ammTwapOracleUpdateMap_other_slot_frame (s : ContractState)
      (price0CumulativeSlot price1CumulativeSlot lastTimestampSlot observationIndexSlot otherSlot account observer price0Delta price1Delta newTimestamp indexStep : Nat)
      (hP0 : Nat.beq otherSlot price0CumulativeSlot = false)
      (hP1 : Nat.beq otherSlot price1CumulativeSlot = false)
      (hTs : Nat.beq otherSlot lastTimestampSlot = false)
      (hIdx : Nat.beq otherSlot observationIndexSlot = false) :
      getStorage (ammTwapOracleUpdateMap s price0CumulativeSlot price1CumulativeSlot lastTimestampSlot observationIndexSlot account price0Delta price1Delta newTimestamp indexStep) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (mintMap_slot_frame _ observationIndexSlot account indexStep (.map otherSlot observer)
      ((congrArg (· && observer.beq account) hIdx).trans (Bool.false_and _))).trans <|
      (getStorage_setStorage_miss _ (.map lastTimestampSlot account) (.map otherSlot observer) newTimestamp
        ((congrArg (· && observer.beq account) hTs).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ price1CumulativeSlot account price1Delta (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hP1).trans (Bool.false_and _))).trans
        (mintMap_slot_frame s price0CumulativeSlot account price0Delta (.map otherSlot observer)
          ((congrArg (· && observer.beq account) hP0).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem ammTwapOracleUpdateMap_observation_index_updated (s : ContractState)
      (price0CumulativeSlot price1CumulativeSlot lastTimestampSlot observationIndexSlot account price0Delta price1Delta newTimestamp indexStep : Nat)
      (hIdxTs : Nat.beq observationIndexSlot lastTimestampSlot = false)
      (hIdxP1 : Nat.beq observationIndexSlot price1CumulativeSlot = false)
      (hIdxP0 : Nat.beq observationIndexSlot price0CumulativeSlot = false) :
      getStorage (ammTwapOracleUpdateMap s price0CumulativeSlot price1CumulativeSlot lastTimestampSlot observationIndexSlot account price0Delta price1Delta newTimestamp indexStep) (.map observationIndexSlot account) =
        getStorage s (.map observationIndexSlot account) + indexStep :=
    let hMissTs : StorageKey.fastBeq (.map observationIndexSlot account) (.map lastTimestampSlot account) = false :=
      (congrArg (· && account.beq account) hIdxTs).trans (Bool.false_and _)
    let hMissP1 : StorageKey.fastBeq (.map observationIndexSlot account) (.map price1CumulativeSlot account) = false :=
      (congrArg (· && account.beq account) hIdxP1).trans (Bool.false_and _)
    let hMissP0 : StorageKey.fastBeq (.map observationIndexSlot account) (.map price0CumulativeSlot account) = false :=
      (congrArg (· && account.beq account) hIdxP0).trans (Bool.false_and _)
    getStorage_setStorage_same.trans <|
      congrArg (· + indexStep)
        ((getStorage_setStorage_miss _ (.map lastTimestampSlot account) (.map observationIndexSlot account) newTimestamp hMissTs).trans
          ((mintMap_slot_frame _ price1CumulativeSlot account price1Delta (.map observationIndexSlot account) hMissP1).trans
            (mintMap_slot_frame s price0CumulativeSlot account price0Delta (.map observationIndexSlot account) hMissP0)))

set_option maxHeartbeats 200000 in
  theorem ammTwapOracleUpdateMap_timestamp_updated (s : ContractState)
      (price0CumulativeSlot price1CumulativeSlot lastTimestampSlot observationIndexSlot account price0Delta price1Delta newTimestamp indexStep : Nat)
      (hTsIdx : Nat.beq lastTimestampSlot observationIndexSlot = false) :
      getStorage (ammTwapOracleUpdateMap s price0CumulativeSlot price1CumulativeSlot lastTimestampSlot observationIndexSlot account price0Delta price1Delta newTimestamp indexStep) (.map lastTimestampSlot account) =
        newTimestamp :=
    let hMissIdx : StorageKey.fastBeq (.map lastTimestampSlot account) (.map observationIndexSlot account) = false :=
      (congrArg (· && account.beq account) hTsIdx).trans (Bool.false_and _)
    (mintMap_slot_frame _ observationIndexSlot account indexStep (.map lastTimestampSlot account) hMissIdx).trans
      getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem ammTwapOracleUpdateMap_price1_cumulative_updated (s : ContractState)
      (price0CumulativeSlot price1CumulativeSlot lastTimestampSlot observationIndexSlot account price0Delta price1Delta newTimestamp indexStep : Nat)
      (hP1Idx : Nat.beq price1CumulativeSlot observationIndexSlot = false)
      (hP1Ts : Nat.beq price1CumulativeSlot lastTimestampSlot = false)
      (hP1P0 : Nat.beq price1CumulativeSlot price0CumulativeSlot = false) :
      getStorage (ammTwapOracleUpdateMap s price0CumulativeSlot price1CumulativeSlot lastTimestampSlot observationIndexSlot account price0Delta price1Delta newTimestamp indexStep) (.map price1CumulativeSlot account) =
        getStorage s (.map price1CumulativeSlot account) + price1Delta :=
    let hMissIdx : StorageKey.fastBeq (.map price1CumulativeSlot account) (.map observationIndexSlot account) = false :=
      (congrArg (· && account.beq account) hP1Idx).trans (Bool.false_and _)
    let hMissTs : StorageKey.fastBeq (.map price1CumulativeSlot account) (.map lastTimestampSlot account) = false :=
      (congrArg (· && account.beq account) hP1Ts).trans (Bool.false_and _)
    let hMissP0 : StorageKey.fastBeq (.map price1CumulativeSlot account) (.map price0CumulativeSlot account) = false :=
      (congrArg (· && account.beq account) hP1P0).trans (Bool.false_and _)
    (mintMap_slot_frame _ observationIndexSlot account indexStep (.map price1CumulativeSlot account) hMissIdx).trans <|
      (getStorage_setStorage_miss _ (.map lastTimestampSlot account) (.map price1CumulativeSlot account) newTimestamp hMissTs).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· + price1Delta)
          (mintMap_slot_frame s price0CumulativeSlot account price0Delta (.map price1CumulativeSlot account) hMissP0))

set_option maxHeartbeats 200000 in
  theorem guardedAmmTwapOracleUpdateMap_unlocked_after (s : ContractState)
      (lockSlot price0CumulativeSlot price1CumulativeSlot lastTimestampSlot observationIndexSlot account price0Delta price1Delta newTimestamp indexStep : Nat) :
      isTransientLocked (guardedAmmTwapOracleUpdateMap s lockSlot price0CumulativeSlot price1CumulativeSlot lastTimestampSlot observationIndexSlot account price0Delta price1Delta newTimestamp indexStep) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def ammConcentratedTickCrossMap (s : ContractState)
      (activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta feeGrowthGlobal0 feeGrowthGlobal1 nextTick : Nat) : ContractState :=
    let s1 := mintMap s activeLiquiditySlot account liquidityNetDelta
    let s2 := setStorage s1 (.map feeGrowthOutside0Slot account) (feeGrowthGlobal0 - getStorage s1 (.map feeGrowthOutside0Slot account))
    let s3 := setStorage s2 (.map feeGrowthOutside1Slot account) (feeGrowthGlobal1 - getStorage s2 (.map feeGrowthOutside1Slot account))
    setStorage s3 (.map currentTickSlot account) nextTick

  def guardedAmmConcentratedTickCrossMap (s : ContractState)
      (lockSlot activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta feeGrowthGlobal0 feeGrowthGlobal1 nextTick : Nat) : ContractState :=
    releaseTransientLock
      (ammConcentratedTickCrossMap (acquireTransientLock s lockSlot) activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta feeGrowthGlobal0 feeGrowthGlobal1 nextTick)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem ammConcentratedTickCrossMap_other_slot_frame (s : ContractState)
      (activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot otherSlot account observer liquidityNetDelta feeGrowthGlobal0 feeGrowthGlobal1 nextTick : Nat)
      (hLiq : Nat.beq otherSlot activeLiquiditySlot = false)
      (hFg0 : Nat.beq otherSlot feeGrowthOutside0Slot = false)
      (hFg1 : Nat.beq otherSlot feeGrowthOutside1Slot = false)
      (hTick : Nat.beq otherSlot currentTickSlot = false) :
      getStorage (ammConcentratedTickCrossMap s activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta feeGrowthGlobal0 feeGrowthGlobal1 nextTick) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (getStorage_setStorage_miss _ (.map currentTickSlot account) (.map otherSlot observer) nextTick
      ((congrArg (· && observer.beq account) hTick).trans (Bool.false_and _))).trans <|
      (getStorage_setStorage_miss _ (.map feeGrowthOutside1Slot account) (.map otherSlot observer) _
        ((congrArg (· && observer.beq account) hFg1).trans (Bool.false_and _))).trans <|
      (getStorage_setStorage_miss _ (.map feeGrowthOutside0Slot account) (.map otherSlot observer) _
        ((congrArg (· && observer.beq account) hFg0).trans (Bool.false_and _))).trans
        (mintMap_slot_frame s activeLiquiditySlot account liquidityNetDelta (.map otherSlot observer)
          ((congrArg (· && observer.beq account) hLiq).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem ammConcentratedTickCrossMap_current_tick_updated (s : ContractState)
      (activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta feeGrowthGlobal0 feeGrowthGlobal1 nextTick : Nat) :
      getStorage (ammConcentratedTickCrossMap s activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta feeGrowthGlobal0 feeGrowthGlobal1 nextTick) (.map currentTickSlot account) =
        nextTick :=
    getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem ammConcentratedTickCrossMap_fee_growth_outside1_updated (s : ContractState)
      (activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta feeGrowthGlobal0 feeGrowthGlobal1 nextTick : Nat)
      (hFg1Tick : Nat.beq feeGrowthOutside1Slot currentTickSlot = false)
      (hFg1Fg0 : Nat.beq feeGrowthOutside1Slot feeGrowthOutside0Slot = false)
      (hFg1Liq : Nat.beq feeGrowthOutside1Slot activeLiquiditySlot = false) :
      getStorage (ammConcentratedTickCrossMap s activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta feeGrowthGlobal0 feeGrowthGlobal1 nextTick) (.map feeGrowthOutside1Slot account) =
        feeGrowthGlobal1 - getStorage s (.map feeGrowthOutside1Slot account) :=
    let hMissTick : StorageKey.fastBeq (.map feeGrowthOutside1Slot account) (.map currentTickSlot account) = false :=
      (congrArg (· && account.beq account) hFg1Tick).trans (Bool.false_and _)
    let hMissFg0 : StorageKey.fastBeq (.map feeGrowthOutside1Slot account) (.map feeGrowthOutside0Slot account) = false :=
      (congrArg (· && account.beq account) hFg1Fg0).trans (Bool.false_and _)
    let hMissLiq : StorageKey.fastBeq (.map feeGrowthOutside1Slot account) (.map activeLiquiditySlot account) = false :=
      (congrArg (· && account.beq account) hFg1Liq).trans (Bool.false_and _)
    (getStorage_setStorage_miss _ (.map currentTickSlot account) (.map feeGrowthOutside1Slot account) nextTick hMissTick).trans <|
      getStorage_setStorage_same.trans
        (congrArg (feeGrowthGlobal1 - ·)
          ((getStorage_setStorage_miss _ (.map feeGrowthOutside0Slot account) (.map feeGrowthOutside1Slot account) _ hMissFg0).trans
            (mintMap_slot_frame s activeLiquiditySlot account liquidityNetDelta (.map feeGrowthOutside1Slot account) hMissLiq)))

set_option maxHeartbeats 200000 in
  theorem ammConcentratedTickCrossMap_fee_growth_outside0_updated (s : ContractState)
      (activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta feeGrowthGlobal0 feeGrowthGlobal1 nextTick : Nat)
      (hFg0Tick : Nat.beq feeGrowthOutside0Slot currentTickSlot = false)
      (hFg0Fg1 : Nat.beq feeGrowthOutside0Slot feeGrowthOutside1Slot = false)
      (hFg0Liq : Nat.beq feeGrowthOutside0Slot activeLiquiditySlot = false) :
      getStorage (ammConcentratedTickCrossMap s activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta feeGrowthGlobal0 feeGrowthGlobal1 nextTick) (.map feeGrowthOutside0Slot account) =
        feeGrowthGlobal0 - getStorage s (.map feeGrowthOutside0Slot account) :=
    let hMissTick : StorageKey.fastBeq (.map feeGrowthOutside0Slot account) (.map currentTickSlot account) = false :=
      (congrArg (· && account.beq account) hFg0Tick).trans (Bool.false_and _)
    let hMissFg1 : StorageKey.fastBeq (.map feeGrowthOutside0Slot account) (.map feeGrowthOutside1Slot account) = false :=
      (congrArg (· && account.beq account) hFg0Fg1).trans (Bool.false_and _)
    let hMissLiq : StorageKey.fastBeq (.map feeGrowthOutside0Slot account) (.map activeLiquiditySlot account) = false :=
      (congrArg (· && account.beq account) hFg0Liq).trans (Bool.false_and _)
    (getStorage_setStorage_miss _ (.map currentTickSlot account) (.map feeGrowthOutside0Slot account) nextTick hMissTick).trans <|
      (getStorage_setStorage_miss _ (.map feeGrowthOutside1Slot account) (.map feeGrowthOutside0Slot account) _ hMissFg1).trans <|
      getStorage_setStorage_same.trans
        (congrArg (feeGrowthGlobal0 - ·)
          (mintMap_slot_frame s activeLiquiditySlot account liquidityNetDelta (.map feeGrowthOutside0Slot account) hMissLiq))

set_option maxHeartbeats 200000 in
  theorem guardedAmmConcentratedTickCrossMap_unlocked_after (s : ContractState)
      (lockSlot activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta feeGrowthGlobal0 feeGrowthGlobal1 nextTick : Nat) :
      isTransientLocked (guardedAmmConcentratedTickCrossMap s lockSlot activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta feeGrowthGlobal0 feeGrowthGlobal1 nextTick) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def ammConcentratedTickCrossRoundTripMap (s : ContractState)
      (activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta1 liquidityNetDelta2 feeGrowthGlobal0 feeGrowthGlobal1 midTick origTick : Nat) : ContractState :=
    ammConcentratedTickCrossMap
      (ammConcentratedTickCrossMap s activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta1 feeGrowthGlobal0 feeGrowthGlobal1 midTick)
      activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta2 feeGrowthGlobal0 feeGrowthGlobal1 origTick

  def guardedAmmConcentratedTickCrossRoundTripMap (s : ContractState)
      (lockSlot activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta1 liquidityNetDelta2 feeGrowthGlobal0 feeGrowthGlobal1 midTick origTick : Nat) : ContractState :=
    releaseTransientLock
      (ammConcentratedTickCrossRoundTripMap (acquireTransientLock s lockSlot) activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta1 liquidityNetDelta2 feeGrowthGlobal0 feeGrowthGlobal1 midTick origTick)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem ammConcentratedTickCrossRoundTripMap_other_slot_frame (s : ContractState)
      (activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot otherSlot account observer liquidityNetDelta1 liquidityNetDelta2 feeGrowthGlobal0 feeGrowthGlobal1 midTick origTick : Nat)
      (hLiq : Nat.beq otherSlot activeLiquiditySlot = false)
      (hFg0 : Nat.beq otherSlot feeGrowthOutside0Slot = false)
      (hFg1 : Nat.beq otherSlot feeGrowthOutside1Slot = false)
      (hTick : Nat.beq otherSlot currentTickSlot = false) :
      getStorage (ammConcentratedTickCrossRoundTripMap s activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta1 liquidityNetDelta2 feeGrowthGlobal0 feeGrowthGlobal1 midTick origTick) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (ammConcentratedTickCrossMap_other_slot_frame _ activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot otherSlot account observer liquidityNetDelta2 feeGrowthGlobal0 feeGrowthGlobal1 origTick hLiq hFg0 hFg1 hTick).trans
      (ammConcentratedTickCrossMap_other_slot_frame s activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot otherSlot account observer liquidityNetDelta1 feeGrowthGlobal0 feeGrowthGlobal1 midTick hLiq hFg0 hFg1 hTick)

set_option maxHeartbeats 200000 in
  theorem ammConcentratedTickCrossRoundTripMap_current_tick_restored (s : ContractState)
      (activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta1 liquidityNetDelta2 feeGrowthGlobal0 feeGrowthGlobal1 midTick origTick : Nat) :
      getStorage (ammConcentratedTickCrossRoundTripMap s activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta1 liquidityNetDelta2 feeGrowthGlobal0 feeGrowthGlobal1 midTick origTick) (.map currentTickSlot account) =
        origTick :=
    getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem ammConcentratedTickCrossRoundTripMap_fee_growth_outside1_exact_restore (s : ContractState)
      (activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta1 liquidityNetDelta2 feeGrowthGlobal0 feeGrowthGlobal1 midTick origTick : Nat)
      (hFg1Tick : Nat.beq feeGrowthOutside1Slot currentTickSlot = false)
      (hFg1Fg0 : Nat.beq feeGrowthOutside1Slot feeGrowthOutside0Slot = false)
      (hFg1Liq : Nat.beq feeGrowthOutside1Slot activeLiquiditySlot = false)
      (hCancel : feeGrowthGlobal1 - (feeGrowthGlobal1 - getStorage s (.map feeGrowthOutside1Slot account)) = getStorage s (.map feeGrowthOutside1Slot account)) :
      getStorage (ammConcentratedTickCrossRoundTripMap s activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta1 liquidityNetDelta2 feeGrowthGlobal0 feeGrowthGlobal1 midTick origTick) (.map feeGrowthOutside1Slot account) =
        getStorage s (.map feeGrowthOutside1Slot account) :=
    (ammConcentratedTickCrossMap_fee_growth_outside1_updated _ activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta2 feeGrowthGlobal0 feeGrowthGlobal1 origTick hFg1Tick hFg1Fg0 hFg1Liq).trans <|
      (congrArg (feeGrowthGlobal1 - ·)
        (ammConcentratedTickCrossMap_fee_growth_outside1_updated s activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta1 feeGrowthGlobal0 feeGrowthGlobal1 midTick hFg1Tick hFg1Fg0 hFg1Liq)).trans
        hCancel

set_option maxHeartbeats 200000 in
  theorem ammConcentratedTickCrossRoundTripMap_preserves_transient (s : ContractState)
      (activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta1 liquidityNetDelta2 feeGrowthGlobal0 feeGrowthGlobal1 midTick origTick tslot : Nat) :
      getStorage (ammConcentratedTickCrossRoundTripMap s activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta1 liquidityNetDelta2 feeGrowthGlobal0 feeGrowthGlobal1 midTick origTick) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (getStorage_setStorage_miss _ (.map currentTickSlot account) (.transient tslot) origTick rfl).trans <|
      (getStorage_setStorage_miss _ (.map feeGrowthOutside1Slot account) (.transient tslot) _ rfl).trans <|
      (getStorage_setStorage_miss _ (.map feeGrowthOutside0Slot account) (.transient tslot) _ rfl).trans <|
      (mintMap_slot_frame _ activeLiquiditySlot account liquidityNetDelta2 (.transient tslot) rfl).trans <|
      (getStorage_setStorage_miss _ (.map currentTickSlot account) (.transient tslot) midTick rfl).trans <|
      (getStorage_setStorage_miss _ (.map feeGrowthOutside1Slot account) (.transient tslot) _ rfl).trans <|
      (getStorage_setStorage_miss _ (.map feeGrowthOutside0Slot account) (.transient tslot) _ rfl).trans
        (mintMap_slot_frame s activeLiquiditySlot account liquidityNetDelta1 (.transient tslot) rfl)

set_option maxHeartbeats 200000 in
  theorem guardedAmmConcentratedTickCrossRoundTripMap_unlocked_after (s : ContractState)
      (lockSlot activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta1 liquidityNetDelta2 feeGrowthGlobal0 feeGrowthGlobal1 midTick origTick : Nat) :
      isTransientLocked (guardedAmmConcentratedTickCrossRoundTripMap s lockSlot activeLiquiditySlot feeGrowthOutside0Slot feeGrowthOutside1Slot currentTickSlot account liquidityNetDelta1 liquidityNetDelta2 feeGrowthGlobal0 feeGrowthGlobal1 midTick origTick) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def ammCollectPositionFeesMap (s : ContractState)
      (tokensOwed0Slot tokensOwed1Slot poolFeeReserve0Slot poolFeeReserve1Slot recipientToken0Slot recipientToken1Slot account collected0 collected1 : Nat) : ContractState :=
    mintMap
      (mintMap
        (burnMap
          (burnMap
            (burnMap
              (burnMap s tokensOwed0Slot account collected0)
              tokensOwed1Slot account collected1)
            poolFeeReserve0Slot account collected0)
          poolFeeReserve1Slot account collected1)
        recipientToken0Slot account collected0)
      recipientToken1Slot account collected1

  def guardedAmmCollectPositionFeesMap (s : ContractState)
      (lockSlot tokensOwed0Slot tokensOwed1Slot poolFeeReserve0Slot poolFeeReserve1Slot recipientToken0Slot recipientToken1Slot account collected0 collected1 : Nat) : ContractState :=
    releaseTransientLock
      (ammCollectPositionFeesMap (acquireTransientLock s lockSlot) tokensOwed0Slot tokensOwed1Slot poolFeeReserve0Slot poolFeeReserve1Slot recipientToken0Slot recipientToken1Slot account collected0 collected1)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem ammCollectPositionFeesMap_other_slot_frame (s : ContractState)
      (tokensOwed0Slot tokensOwed1Slot poolFeeReserve0Slot poolFeeReserve1Slot recipientToken0Slot recipientToken1Slot otherSlot account observer collected0 collected1 : Nat)
      (hOwed0 : Nat.beq otherSlot tokensOwed0Slot = false)
      (hOwed1 : Nat.beq otherSlot tokensOwed1Slot = false)
      (hRes0 : Nat.beq otherSlot poolFeeReserve0Slot = false)
      (hRes1 : Nat.beq otherSlot poolFeeReserve1Slot = false)
      (hRec0 : Nat.beq otherSlot recipientToken0Slot = false)
      (hRec1 : Nat.beq otherSlot recipientToken1Slot = false) :
      getStorage (ammCollectPositionFeesMap s tokensOwed0Slot tokensOwed1Slot poolFeeReserve0Slot poolFeeReserve1Slot recipientToken0Slot recipientToken1Slot account collected0 collected1) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (mintMap_slot_frame _ recipientToken1Slot account collected1 (.map otherSlot observer)
      ((congrArg (· && observer.beq account) hRec1).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ recipientToken0Slot account collected0 (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hRec0).trans (Bool.false_and _))).trans <|
      (burnMap_slot_frame _ poolFeeReserve1Slot account collected1 (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hRes1).trans (Bool.false_and _))).trans <|
      (burnMap_slot_frame _ poolFeeReserve0Slot account collected0 (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hRes0).trans (Bool.false_and _))).trans <|
      (burnMap_slot_frame _ tokensOwed1Slot account collected1 (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hOwed1).trans (Bool.false_and _))).trans
        (burnMap_slot_frame s tokensOwed0Slot account collected0 (.map otherSlot observer)
          ((congrArg (· && observer.beq account) hOwed0).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem ammCollectPositionFeesMap_recipient_token1_updated (s : ContractState)
      (tokensOwed0Slot tokensOwed1Slot poolFeeReserve0Slot poolFeeReserve1Slot recipientToken0Slot recipientToken1Slot account collected0 collected1 : Nat)
      (hRec1Rec0 : Nat.beq recipientToken1Slot recipientToken0Slot = false)
      (hRec1Res1 : Nat.beq recipientToken1Slot poolFeeReserve1Slot = false)
      (hRec1Res0 : Nat.beq recipientToken1Slot poolFeeReserve0Slot = false)
      (hRec1Owed1 : Nat.beq recipientToken1Slot tokensOwed1Slot = false)
      (hRec1Owed0 : Nat.beq recipientToken1Slot tokensOwed0Slot = false) :
      getStorage (ammCollectPositionFeesMap s tokensOwed0Slot tokensOwed1Slot poolFeeReserve0Slot poolFeeReserve1Slot recipientToken0Slot recipientToken1Slot account collected0 collected1) (.map recipientToken1Slot account) =
        getStorage s (.map recipientToken1Slot account) + collected1 :=
    let hMissRec0 : StorageKey.fastBeq (.map recipientToken1Slot account) (.map recipientToken0Slot account) = false :=
      (congrArg (· && account.beq account) hRec1Rec0).trans (Bool.false_and _)
    let hMissRes1 : StorageKey.fastBeq (.map recipientToken1Slot account) (.map poolFeeReserve1Slot account) = false :=
      (congrArg (· && account.beq account) hRec1Res1).trans (Bool.false_and _)
    let hMissRes0 : StorageKey.fastBeq (.map recipientToken1Slot account) (.map poolFeeReserve0Slot account) = false :=
      (congrArg (· && account.beq account) hRec1Res0).trans (Bool.false_and _)
    let hMissOwed1 : StorageKey.fastBeq (.map recipientToken1Slot account) (.map tokensOwed1Slot account) = false :=
      (congrArg (· && account.beq account) hRec1Owed1).trans (Bool.false_and _)
    let hMissOwed0 : StorageKey.fastBeq (.map recipientToken1Slot account) (.map tokensOwed0Slot account) = false :=
      (congrArg (· && account.beq account) hRec1Owed0).trans (Bool.false_and _)
    getStorage_setStorage_same.trans <|
      congrArg (· + collected1)
        ((mintMap_slot_frame _ recipientToken0Slot account collected0 (.map recipientToken1Slot account) hMissRec0).trans
          ((burnMap_slot_frame _ poolFeeReserve1Slot account collected1 (.map recipientToken1Slot account) hMissRes1).trans
            ((burnMap_slot_frame _ poolFeeReserve0Slot account collected0 (.map recipientToken1Slot account) hMissRes0).trans
              ((burnMap_slot_frame _ tokensOwed1Slot account collected1 (.map recipientToken1Slot account) hMissOwed1).trans
                (burnMap_slot_frame s tokensOwed0Slot account collected0 (.map recipientToken1Slot account) hMissOwed0)))))

set_option maxHeartbeats 200000 in
  theorem ammCollectPositionFeesMap_recipient_token0_updated (s : ContractState)
      (tokensOwed0Slot tokensOwed1Slot poolFeeReserve0Slot poolFeeReserve1Slot recipientToken0Slot recipientToken1Slot account collected0 collected1 : Nat)
      (hRec0Rec1 : Nat.beq recipientToken0Slot recipientToken1Slot = false)
      (hRec0Res1 : Nat.beq recipientToken0Slot poolFeeReserve1Slot = false)
      (hRec0Res0 : Nat.beq recipientToken0Slot poolFeeReserve0Slot = false)
      (hRec0Owed1 : Nat.beq recipientToken0Slot tokensOwed1Slot = false)
      (hRec0Owed0 : Nat.beq recipientToken0Slot tokensOwed0Slot = false) :
      getStorage (ammCollectPositionFeesMap s tokensOwed0Slot tokensOwed1Slot poolFeeReserve0Slot poolFeeReserve1Slot recipientToken0Slot recipientToken1Slot account collected0 collected1) (.map recipientToken0Slot account) =
        getStorage s (.map recipientToken0Slot account) + collected0 :=
    let hMissRec1 : StorageKey.fastBeq (.map recipientToken0Slot account) (.map recipientToken1Slot account) = false :=
      (congrArg (· && account.beq account) hRec0Rec1).trans (Bool.false_and _)
    let hMissRes1 : StorageKey.fastBeq (.map recipientToken0Slot account) (.map poolFeeReserve1Slot account) = false :=
      (congrArg (· && account.beq account) hRec0Res1).trans (Bool.false_and _)
    let hMissRes0 : StorageKey.fastBeq (.map recipientToken0Slot account) (.map poolFeeReserve0Slot account) = false :=
      (congrArg (· && account.beq account) hRec0Res0).trans (Bool.false_and _)
    let hMissOwed1 : StorageKey.fastBeq (.map recipientToken0Slot account) (.map tokensOwed1Slot account) = false :=
      (congrArg (· && account.beq account) hRec0Owed1).trans (Bool.false_and _)
    let hMissOwed0 : StorageKey.fastBeq (.map recipientToken0Slot account) (.map tokensOwed0Slot account) = false :=
      (congrArg (· && account.beq account) hRec0Owed0).trans (Bool.false_and _)
    (mintMap_slot_frame _ recipientToken1Slot account collected1 (.map recipientToken0Slot account) hMissRec1).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· + collected0)
          ((burnMap_slot_frame _ poolFeeReserve1Slot account collected1 (.map recipientToken0Slot account) hMissRes1).trans
            ((burnMap_slot_frame _ poolFeeReserve0Slot account collected0 (.map recipientToken0Slot account) hMissRes0).trans
              ((burnMap_slot_frame _ tokensOwed1Slot account collected1 (.map recipientToken0Slot account) hMissOwed1).trans
                (burnMap_slot_frame s tokensOwed0Slot account collected0 (.map recipientToken0Slot account) hMissOwed0)))))

set_option maxHeartbeats 200000 in
  theorem ammCollectPositionFeesMap_pool_fee_reserve1_updated (s : ContractState)
      (tokensOwed0Slot tokensOwed1Slot poolFeeReserve0Slot poolFeeReserve1Slot recipientToken0Slot recipientToken1Slot account collected0 collected1 : Nat)
      (hRes1Rec1 : Nat.beq poolFeeReserve1Slot recipientToken1Slot = false)
      (hRes1Rec0 : Nat.beq poolFeeReserve1Slot recipientToken0Slot = false)
      (hRes1Res0 : Nat.beq poolFeeReserve1Slot poolFeeReserve0Slot = false)
      (hRes1Owed1 : Nat.beq poolFeeReserve1Slot tokensOwed1Slot = false)
      (hRes1Owed0 : Nat.beq poolFeeReserve1Slot tokensOwed0Slot = false) :
      getStorage (ammCollectPositionFeesMap s tokensOwed0Slot tokensOwed1Slot poolFeeReserve0Slot poolFeeReserve1Slot recipientToken0Slot recipientToken1Slot account collected0 collected1) (.map poolFeeReserve1Slot account) =
        getStorage s (.map poolFeeReserve1Slot account) - collected1 :=
    let hMissRec1 : StorageKey.fastBeq (.map poolFeeReserve1Slot account) (.map recipientToken1Slot account) = false :=
      (congrArg (· && account.beq account) hRes1Rec1).trans (Bool.false_and _)
    let hMissRec0 : StorageKey.fastBeq (.map poolFeeReserve1Slot account) (.map recipientToken0Slot account) = false :=
      (congrArg (· && account.beq account) hRes1Rec0).trans (Bool.false_and _)
    let hMissRes0 : StorageKey.fastBeq (.map poolFeeReserve1Slot account) (.map poolFeeReserve0Slot account) = false :=
      (congrArg (· && account.beq account) hRes1Res0).trans (Bool.false_and _)
    let hMissOwed1 : StorageKey.fastBeq (.map poolFeeReserve1Slot account) (.map tokensOwed1Slot account) = false :=
      (congrArg (· && account.beq account) hRes1Owed1).trans (Bool.false_and _)
    let hMissOwed0 : StorageKey.fastBeq (.map poolFeeReserve1Slot account) (.map tokensOwed0Slot account) = false :=
      (congrArg (· && account.beq account) hRes1Owed0).trans (Bool.false_and _)
    (mintMap_slot_frame _ recipientToken1Slot account collected1 (.map poolFeeReserve1Slot account) hMissRec1).trans <|
      (mintMap_slot_frame _ recipientToken0Slot account collected0 (.map poolFeeReserve1Slot account) hMissRec0).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· - collected1)
          ((burnMap_slot_frame _ poolFeeReserve0Slot account collected0 (.map poolFeeReserve1Slot account) hMissRes0).trans
            ((burnMap_slot_frame _ tokensOwed1Slot account collected1 (.map poolFeeReserve1Slot account) hMissOwed1).trans
              (burnMap_slot_frame s tokensOwed0Slot account collected0 (.map poolFeeReserve1Slot account) hMissOwed0))))

set_option maxHeartbeats 200000 in
  theorem guardedAmmCollectPositionFeesMap_unlocked_after (s : ContractState)
      (lockSlot tokensOwed0Slot tokensOwed1Slot poolFeeReserve0Slot poolFeeReserve1Slot recipientToken0Slot recipientToken1Slot account collected0 collected1 : Nat) :
      isTransientLocked (guardedAmmCollectPositionFeesMap s lockSlot tokensOwed0Slot tokensOwed1Slot poolFeeReserve0Slot poolFeeReserve1Slot recipientToken0Slot recipientToken1Slot account collected0 collected1) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def lendingBorrowMap (s : ContractState)
      (borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot account newBorrowIndex borrowAmount : Nat) : ContractState :=
    mintMap
      (burnMap
        (mintMap
          (mintMap
            (setStorage s (.map borrowIndexSlot account) newBorrowIndex)
            userPrincipalDebtSlot account borrowAmount)
          totalBorrowsSlot account borrowAmount)
        poolLiquiditySlot account borrowAmount)
      borrowerAssetSlot account borrowAmount

  def guardedLendingBorrowMap (s : ContractState)
      (lockSlot borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot account newBorrowIndex borrowAmount : Nat) : ContractState :=
    releaseTransientLock
      (lendingBorrowMap (acquireTransientLock s lockSlot) borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot account newBorrowIndex borrowAmount)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem lendingBorrowMap_other_slot_frame (s : ContractState)
      (borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot otherSlot account observer newBorrowIndex borrowAmount : Nat)
      (hIdx : Nat.beq otherSlot borrowIndexSlot = false)
      (hDebt : Nat.beq otherSlot userPrincipalDebtSlot = false)
      (hTot : Nat.beq otherSlot totalBorrowsSlot = false)
      (hLiq : Nat.beq otherSlot poolLiquiditySlot = false)
      (hAss : Nat.beq otherSlot borrowerAssetSlot = false) :
      getStorage (lendingBorrowMap s borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot account newBorrowIndex borrowAmount) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (mintMap_slot_frame _ borrowerAssetSlot account borrowAmount (.map otherSlot observer)
      ((congrArg (· && observer.beq account) hAss).trans (Bool.false_and _))).trans <|
      (burnMap_slot_frame _ poolLiquiditySlot account borrowAmount (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hLiq).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ totalBorrowsSlot account borrowAmount (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hTot).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ userPrincipalDebtSlot account borrowAmount (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hDebt).trans (Bool.false_and _))).trans
        (getStorage_setStorage_miss s (.map borrowIndexSlot account) (.map otherSlot observer) newBorrowIndex
          ((congrArg (· && observer.beq account) hIdx).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem lendingBorrowMap_borrower_asset_updated (s : ContractState)
      (borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot account newBorrowIndex borrowAmount : Nat)
      (hAssLiq : Nat.beq borrowerAssetSlot poolLiquiditySlot = false)
      (hAssTot : Nat.beq borrowerAssetSlot totalBorrowsSlot = false)
      (hAssDebt : Nat.beq borrowerAssetSlot userPrincipalDebtSlot = false)
      (hAssIdx : Nat.beq borrowerAssetSlot borrowIndexSlot = false) :
      getStorage (lendingBorrowMap s borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot account newBorrowIndex borrowAmount) (.map borrowerAssetSlot account) =
        getStorage s (.map borrowerAssetSlot account) + borrowAmount :=
    let hMissLiq : StorageKey.fastBeq (.map borrowerAssetSlot account) (.map poolLiquiditySlot account) = false :=
      (congrArg (· && account.beq account) hAssLiq).trans (Bool.false_and _)
    let hMissTot : StorageKey.fastBeq (.map borrowerAssetSlot account) (.map totalBorrowsSlot account) = false :=
      (congrArg (· && account.beq account) hAssTot).trans (Bool.false_and _)
    let hMissDebt : StorageKey.fastBeq (.map borrowerAssetSlot account) (.map userPrincipalDebtSlot account) = false :=
      (congrArg (· && account.beq account) hAssDebt).trans (Bool.false_and _)
    let hMissIdx : StorageKey.fastBeq (.map borrowerAssetSlot account) (.map borrowIndexSlot account) = false :=
      (congrArg (· && account.beq account) hAssIdx).trans (Bool.false_and _)
    getStorage_setStorage_same.trans <|
      congrArg (· + borrowAmount)
        ((burnMap_slot_frame _ poolLiquiditySlot account borrowAmount (.map borrowerAssetSlot account) hMissLiq).trans
          ((mintMap_slot_frame _ totalBorrowsSlot account borrowAmount (.map borrowerAssetSlot account) hMissTot).trans
            ((mintMap_slot_frame _ userPrincipalDebtSlot account borrowAmount (.map borrowerAssetSlot account) hMissDebt).trans
              (getStorage_setStorage_miss s (.map borrowIndexSlot account) (.map borrowerAssetSlot account) newBorrowIndex hMissIdx))))

set_option maxHeartbeats 200000 in
  theorem lendingBorrowMap_pool_liquidity_updated (s : ContractState)
      (borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot account newBorrowIndex borrowAmount : Nat)
      (hLiqAss : Nat.beq poolLiquiditySlot borrowerAssetSlot = false)
      (hLiqTot : Nat.beq poolLiquiditySlot totalBorrowsSlot = false)
      (hLiqDebt : Nat.beq poolLiquiditySlot userPrincipalDebtSlot = false)
      (hLiqIdx : Nat.beq poolLiquiditySlot borrowIndexSlot = false) :
      getStorage (lendingBorrowMap s borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot account newBorrowIndex borrowAmount) (.map poolLiquiditySlot account) =
        getStorage s (.map poolLiquiditySlot account) - borrowAmount :=
    let hMissAss : StorageKey.fastBeq (.map poolLiquiditySlot account) (.map borrowerAssetSlot account) = false :=
      (congrArg (· && account.beq account) hLiqAss).trans (Bool.false_and _)
    let hMissTot : StorageKey.fastBeq (.map poolLiquiditySlot account) (.map totalBorrowsSlot account) = false :=
      (congrArg (· && account.beq account) hLiqTot).trans (Bool.false_and _)
    let hMissDebt : StorageKey.fastBeq (.map poolLiquiditySlot account) (.map userPrincipalDebtSlot account) = false :=
      (congrArg (· && account.beq account) hLiqDebt).trans (Bool.false_and _)
    let hMissIdx : StorageKey.fastBeq (.map poolLiquiditySlot account) (.map borrowIndexSlot account) = false :=
      (congrArg (· && account.beq account) hLiqIdx).trans (Bool.false_and _)
    (mintMap_slot_frame _ borrowerAssetSlot account borrowAmount (.map poolLiquiditySlot account) hMissAss).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· - borrowAmount)
          ((mintMap_slot_frame _ totalBorrowsSlot account borrowAmount (.map poolLiquiditySlot account) hMissTot).trans
            ((mintMap_slot_frame _ userPrincipalDebtSlot account borrowAmount (.map poolLiquiditySlot account) hMissDebt).trans
              (getStorage_setStorage_miss s (.map borrowIndexSlot account) (.map poolLiquiditySlot account) newBorrowIndex hMissIdx))))

set_option maxHeartbeats 200000 in
  theorem lendingBorrowMap_total_borrows_updated (s : ContractState)
      (borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot account newBorrowIndex borrowAmount : Nat)
      (hTotAss : Nat.beq totalBorrowsSlot borrowerAssetSlot = false)
      (hTotLiq : Nat.beq totalBorrowsSlot poolLiquiditySlot = false)
      (hTotDebt : Nat.beq totalBorrowsSlot userPrincipalDebtSlot = false)
      (hTotIdx : Nat.beq totalBorrowsSlot borrowIndexSlot = false) :
      getStorage (lendingBorrowMap s borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot account newBorrowIndex borrowAmount) (.map totalBorrowsSlot account) =
        getStorage s (.map totalBorrowsSlot account) + borrowAmount :=
    let hMissAss : StorageKey.fastBeq (.map totalBorrowsSlot account) (.map borrowerAssetSlot account) = false :=
      (congrArg (· && account.beq account) hTotAss).trans (Bool.false_and _)
    let hMissLiq : StorageKey.fastBeq (.map totalBorrowsSlot account) (.map poolLiquiditySlot account) = false :=
      (congrArg (· && account.beq account) hTotLiq).trans (Bool.false_and _)
    let hMissDebt : StorageKey.fastBeq (.map totalBorrowsSlot account) (.map userPrincipalDebtSlot account) = false :=
      (congrArg (· && account.beq account) hTotDebt).trans (Bool.false_and _)
    let hMissIdx : StorageKey.fastBeq (.map totalBorrowsSlot account) (.map borrowIndexSlot account) = false :=
      (congrArg (· && account.beq account) hTotIdx).trans (Bool.false_and _)
    (mintMap_slot_frame _ borrowerAssetSlot account borrowAmount (.map totalBorrowsSlot account) hMissAss).trans <|
      (burnMap_slot_frame _ poolLiquiditySlot account borrowAmount (.map totalBorrowsSlot account) hMissLiq).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· + borrowAmount)
          ((mintMap_slot_frame _ userPrincipalDebtSlot account borrowAmount (.map totalBorrowsSlot account) hMissDebt).trans
            (getStorage_setStorage_miss s (.map borrowIndexSlot account) (.map totalBorrowsSlot account) newBorrowIndex hMissIdx)))

set_option maxHeartbeats 200000 in
  theorem guardedLendingBorrowMap_unlocked_after (s : ContractState)
      (lockSlot borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot account newBorrowIndex borrowAmount : Nat) :
      isTransientLocked (guardedLendingBorrowMap s lockSlot borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot account newBorrowIndex borrowAmount) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def lendingRepayMap (s : ContractState)
      (borrowerAssetSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot interestReserveSlot account repayTotal repaidPrincipal accruedInterest : Nat) : ContractState :=
    mintMap
      (mintMap
        (burnMap
          (burnMap
            (burnMap s borrowerAssetSlot account repayTotal)
            userPrincipalDebtSlot account repaidPrincipal)
          totalBorrowsSlot account repaidPrincipal)
        poolLiquiditySlot account repaidPrincipal)
      interestReserveSlot account accruedInterest

  def guardedLendingRepayMap (s : ContractState)
      (lockSlot borrowerAssetSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot interestReserveSlot account repayTotal repaidPrincipal accruedInterest : Nat) : ContractState :=
    releaseTransientLock
      (lendingRepayMap (acquireTransientLock s lockSlot) borrowerAssetSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot interestReserveSlot account repayTotal repaidPrincipal accruedInterest)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem lendingRepayMap_other_slot_frame (s : ContractState)
      (borrowerAssetSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot interestReserveSlot otherSlot account observer repayTotal repaidPrincipal accruedInterest : Nat)
      (hAss : Nat.beq otherSlot borrowerAssetSlot = false)
      (hDebt : Nat.beq otherSlot userPrincipalDebtSlot = false)
      (hTot : Nat.beq otherSlot totalBorrowsSlot = false)
      (hLiq : Nat.beq otherSlot poolLiquiditySlot = false)
      (hInt : Nat.beq otherSlot interestReserveSlot = false) :
      getStorage (lendingRepayMap s borrowerAssetSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot interestReserveSlot account repayTotal repaidPrincipal accruedInterest) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (mintMap_slot_frame _ interestReserveSlot account accruedInterest (.map otherSlot observer)
      ((congrArg (· && observer.beq account) hInt).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ poolLiquiditySlot account repaidPrincipal (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hLiq).trans (Bool.false_and _))).trans <|
      (burnMap_slot_frame _ totalBorrowsSlot account repaidPrincipal (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hTot).trans (Bool.false_and _))).trans <|
      (burnMap_slot_frame _ userPrincipalDebtSlot account repaidPrincipal (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hDebt).trans (Bool.false_and _))).trans
        (burnMap_slot_frame s borrowerAssetSlot account repayTotal (.map otherSlot observer)
          ((congrArg (· && observer.beq account) hAss).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem lendingRepayMap_interest_reserve_updated (s : ContractState)
      (borrowerAssetSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot interestReserveSlot account repayTotal repaidPrincipal accruedInterest : Nat)
      (hIntLiq : Nat.beq interestReserveSlot poolLiquiditySlot = false)
      (hIntTot : Nat.beq interestReserveSlot totalBorrowsSlot = false)
      (hIntDebt : Nat.beq interestReserveSlot userPrincipalDebtSlot = false)
      (hIntAss : Nat.beq interestReserveSlot borrowerAssetSlot = false) :
      getStorage (lendingRepayMap s borrowerAssetSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot interestReserveSlot account repayTotal repaidPrincipal accruedInterest) (.map interestReserveSlot account) =
        getStorage s (.map interestReserveSlot account) + accruedInterest :=
    let hMissLiq : StorageKey.fastBeq (.map interestReserveSlot account) (.map poolLiquiditySlot account) = false :=
      (congrArg (· && account.beq account) hIntLiq).trans (Bool.false_and _)
    let hMissTot : StorageKey.fastBeq (.map interestReserveSlot account) (.map totalBorrowsSlot account) = false :=
      (congrArg (· && account.beq account) hIntTot).trans (Bool.false_and _)
    let hMissDebt : StorageKey.fastBeq (.map interestReserveSlot account) (.map userPrincipalDebtSlot account) = false :=
      (congrArg (· && account.beq account) hIntDebt).trans (Bool.false_and _)
    let hMissAss : StorageKey.fastBeq (.map interestReserveSlot account) (.map borrowerAssetSlot account) = false :=
      (congrArg (· && account.beq account) hIntAss).trans (Bool.false_and _)
    getStorage_setStorage_same.trans <|
      congrArg (· + accruedInterest)
        ((mintMap_slot_frame _ poolLiquiditySlot account repaidPrincipal (.map interestReserveSlot account) hMissLiq).trans
          ((burnMap_slot_frame _ totalBorrowsSlot account repaidPrincipal (.map interestReserveSlot account) hMissTot).trans
            ((burnMap_slot_frame _ userPrincipalDebtSlot account repaidPrincipal (.map interestReserveSlot account) hMissDebt).trans
              (burnMap_slot_frame s borrowerAssetSlot account repayTotal (.map interestReserveSlot account) hMissAss))))

set_option maxHeartbeats 200000 in
  theorem lendingRepayMap_pool_liquidity_updated (s : ContractState)
      (borrowerAssetSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot interestReserveSlot account repayTotal repaidPrincipal accruedInterest : Nat)
      (hLiqInt : Nat.beq poolLiquiditySlot interestReserveSlot = false)
      (hLiqTot : Nat.beq poolLiquiditySlot totalBorrowsSlot = false)
      (hLiqDebt : Nat.beq poolLiquiditySlot userPrincipalDebtSlot = false)
      (hLiqAss : Nat.beq poolLiquiditySlot borrowerAssetSlot = false) :
      getStorage (lendingRepayMap s borrowerAssetSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot interestReserveSlot account repayTotal repaidPrincipal accruedInterest) (.map poolLiquiditySlot account) =
        getStorage s (.map poolLiquiditySlot account) + repaidPrincipal :=
    let hMissInt : StorageKey.fastBeq (.map poolLiquiditySlot account) (.map interestReserveSlot account) = false :=
      (congrArg (· && account.beq account) hLiqInt).trans (Bool.false_and _)
    let hMissTot : StorageKey.fastBeq (.map poolLiquiditySlot account) (.map totalBorrowsSlot account) = false :=
      (congrArg (· && account.beq account) hLiqTot).trans (Bool.false_and _)
    let hMissDebt : StorageKey.fastBeq (.map poolLiquiditySlot account) (.map userPrincipalDebtSlot account) = false :=
      (congrArg (· && account.beq account) hLiqDebt).trans (Bool.false_and _)
    let hMissAss : StorageKey.fastBeq (.map poolLiquiditySlot account) (.map borrowerAssetSlot account) = false :=
      (congrArg (· && account.beq account) hLiqAss).trans (Bool.false_and _)
    (mintMap_slot_frame _ interestReserveSlot account accruedInterest (.map poolLiquiditySlot account) hMissInt).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· + repaidPrincipal)
          ((burnMap_slot_frame _ totalBorrowsSlot account repaidPrincipal (.map poolLiquiditySlot account) hMissTot).trans
            ((burnMap_slot_frame _ userPrincipalDebtSlot account repaidPrincipal (.map poolLiquiditySlot account) hMissDebt).trans
              (burnMap_slot_frame s borrowerAssetSlot account repayTotal (.map poolLiquiditySlot account) hMissAss))))

set_option maxHeartbeats 200000 in
  theorem lendingRepayMap_total_borrows_updated (s : ContractState)
      (borrowerAssetSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot interestReserveSlot account repayTotal repaidPrincipal accruedInterest : Nat)
      (hTotInt : Nat.beq totalBorrowsSlot interestReserveSlot = false)
      (hTotLiq : Nat.beq totalBorrowsSlot poolLiquiditySlot = false)
      (hTotDebt : Nat.beq totalBorrowsSlot userPrincipalDebtSlot = false)
      (hTotAss : Nat.beq totalBorrowsSlot borrowerAssetSlot = false) :
      getStorage (lendingRepayMap s borrowerAssetSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot interestReserveSlot account repayTotal repaidPrincipal accruedInterest) (.map totalBorrowsSlot account) =
        getStorage s (.map totalBorrowsSlot account) - repaidPrincipal :=
    let hMissInt : StorageKey.fastBeq (.map totalBorrowsSlot account) (.map interestReserveSlot account) = false :=
      (congrArg (· && account.beq account) hTotInt).trans (Bool.false_and _)
    let hMissLiq : StorageKey.fastBeq (.map totalBorrowsSlot account) (.map poolLiquiditySlot account) = false :=
      (congrArg (· && account.beq account) hTotLiq).trans (Bool.false_and _)
    let hMissDebt : StorageKey.fastBeq (.map totalBorrowsSlot account) (.map userPrincipalDebtSlot account) = false :=
      (congrArg (· && account.beq account) hTotDebt).trans (Bool.false_and _)
    let hMissAss : StorageKey.fastBeq (.map totalBorrowsSlot account) (.map borrowerAssetSlot account) = false :=
      (congrArg (· && account.beq account) hTotAss).trans (Bool.false_and _)
    (mintMap_slot_frame _ interestReserveSlot account accruedInterest (.map totalBorrowsSlot account) hMissInt).trans <|
      (mintMap_slot_frame _ poolLiquiditySlot account repaidPrincipal (.map totalBorrowsSlot account) hMissLiq).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· - repaidPrincipal)
          ((burnMap_slot_frame _ userPrincipalDebtSlot account repaidPrincipal (.map totalBorrowsSlot account) hMissDebt).trans
            (burnMap_slot_frame s borrowerAssetSlot account repayTotal (.map totalBorrowsSlot account) hMissAss)))

set_option maxHeartbeats 200000 in
  theorem guardedLendingRepayMap_unlocked_after (s : ContractState)
      (lockSlot borrowerAssetSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot interestReserveSlot account repayTotal repaidPrincipal accruedInterest : Nat) :
      isTransientLocked (guardedLendingRepayMap s lockSlot borrowerAssetSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot interestReserveSlot account repayTotal repaidPrincipal accruedInterest) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def lendingBorrowThenRepayMap (s : ContractState)
      (borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot interestReserveSlot account newBorrowIndex borrowAmount repayTotal accruedInterest : Nat) : ContractState :=
    lendingRepayMap
      (lendingBorrowMap s borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot account newBorrowIndex borrowAmount)
      borrowerAssetSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot interestReserveSlot account repayTotal borrowAmount accruedInterest

  def guardedLendingBorrowThenRepayMap (s : ContractState)
      (lockSlot borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot interestReserveSlot account newBorrowIndex borrowAmount repayTotal accruedInterest : Nat) : ContractState :=
    releaseTransientLock
      (lendingBorrowThenRepayMap (acquireTransientLock s lockSlot) borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot interestReserveSlot account newBorrowIndex borrowAmount repayTotal accruedInterest)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem lendingBorrowThenRepayMap_other_slot_frame (s : ContractState)
      (borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot interestReserveSlot otherSlot account observer newBorrowIndex borrowAmount repayTotal accruedInterest : Nat)
      (hIdx : Nat.beq otherSlot borrowIndexSlot = false)
      (hDebt : Nat.beq otherSlot userPrincipalDebtSlot = false)
      (hTot : Nat.beq otherSlot totalBorrowsSlot = false)
      (hLiq : Nat.beq otherSlot poolLiquiditySlot = false)
      (hAss : Nat.beq otherSlot borrowerAssetSlot = false)
      (hInt : Nat.beq otherSlot interestReserveSlot = false) :
      getStorage (lendingBorrowThenRepayMap s borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot interestReserveSlot account newBorrowIndex borrowAmount repayTotal accruedInterest) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (lendingRepayMap_other_slot_frame _ borrowerAssetSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot interestReserveSlot otherSlot account observer repayTotal borrowAmount accruedInterest hAss hDebt hTot hLiq hInt).trans
      (lendingBorrowMap_other_slot_frame s borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot otherSlot account observer newBorrowIndex borrowAmount hIdx hDebt hTot hLiq hAss)

set_option maxHeartbeats 200000 in
  theorem lendingBorrowThenRepayMap_pool_liquidity_exact_restore (s : ContractState)
      (borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot interestReserveSlot account newBorrowIndex borrowAmount repayTotal accruedInterest : Nat)
      (hLiqInt : Nat.beq poolLiquiditySlot interestReserveSlot = false)
      (hLiqAss : Nat.beq poolLiquiditySlot borrowerAssetSlot = false)
      (hLiqTot : Nat.beq poolLiquiditySlot totalBorrowsSlot = false)
      (hLiqDebt : Nat.beq poolLiquiditySlot userPrincipalDebtSlot = false)
      (hLiqIdx : Nat.beq poolLiquiditySlot borrowIndexSlot = false)
      (hLe : borrowAmount ≤ getStorage s (.map poolLiquiditySlot account)) :
      getStorage (lendingBorrowThenRepayMap s borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot interestReserveSlot account newBorrowIndex borrowAmount repayTotal accruedInterest) (.map poolLiquiditySlot account) =
        getStorage s (.map poolLiquiditySlot account) :=
    (lendingRepayMap_pool_liquidity_updated _ borrowerAssetSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot interestReserveSlot account repayTotal borrowAmount accruedInterest hLiqInt hLiqTot hLiqDebt hLiqAss).trans <|
      (congrArg (· + borrowAmount)
        (lendingBorrowMap_pool_liquidity_updated s borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot account newBorrowIndex borrowAmount hLiqAss hLiqTot hLiqDebt hLiqIdx)).trans
        (Nat.sub_add_cancel hLe)

set_option maxHeartbeats 200000 in
  theorem lendingBorrowThenRepayMap_total_borrows_exact_restore (s : ContractState)
      (borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot interestReserveSlot account newBorrowIndex borrowAmount repayTotal accruedInterest : Nat)
      (hTotInt : Nat.beq totalBorrowsSlot interestReserveSlot = false)
      (hTotAss : Nat.beq totalBorrowsSlot borrowerAssetSlot = false)
      (hTotLiq : Nat.beq totalBorrowsSlot poolLiquiditySlot = false)
      (hTotDebt : Nat.beq totalBorrowsSlot userPrincipalDebtSlot = false)
      (hTotIdx : Nat.beq totalBorrowsSlot borrowIndexSlot = false) :
      getStorage (lendingBorrowThenRepayMap s borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot interestReserveSlot account newBorrowIndex borrowAmount repayTotal accruedInterest) (.map totalBorrowsSlot account) =
        getStorage s (.map totalBorrowsSlot account) :=
    (lendingRepayMap_total_borrows_updated _ borrowerAssetSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot interestReserveSlot account repayTotal borrowAmount accruedInterest hTotInt hTotLiq hTotDebt hTotAss).trans <|
      (congrArg (· - borrowAmount)
        (lendingBorrowMap_total_borrows_updated s borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot account newBorrowIndex borrowAmount hTotAss hTotLiq hTotDebt hTotIdx)).trans
        (Nat.add_sub_cancel (getStorage s (.map totalBorrowsSlot account)) borrowAmount)

set_option maxHeartbeats 200000 in
  theorem lendingBorrowThenRepayMap_preserves_transient (s : ContractState)
      (borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot interestReserveSlot account newBorrowIndex borrowAmount repayTotal accruedInterest tslot : Nat) :
      getStorage (lendingBorrowThenRepayMap s borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot interestReserveSlot account newBorrowIndex borrowAmount repayTotal accruedInterest) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (mintMap_slot_frame _ interestReserveSlot account accruedInterest (.transient tslot) rfl).trans <|
      (mintMap_slot_frame _ poolLiquiditySlot account borrowAmount (.transient tslot) rfl).trans <|
      (burnMap_slot_frame _ totalBorrowsSlot account borrowAmount (.transient tslot) rfl).trans <|
      (burnMap_slot_frame _ userPrincipalDebtSlot account borrowAmount (.transient tslot) rfl).trans <|
      (burnMap_slot_frame _ borrowerAssetSlot account repayTotal (.transient tslot) rfl).trans <|
      (mintMap_slot_frame _ borrowerAssetSlot account borrowAmount (.transient tslot) rfl).trans <|
      (burnMap_slot_frame _ poolLiquiditySlot account borrowAmount (.transient tslot) rfl).trans <|
      (mintMap_slot_frame _ totalBorrowsSlot account borrowAmount (.transient tslot) rfl).trans <|
      (mintMap_slot_frame _ userPrincipalDebtSlot account borrowAmount (.transient tslot) rfl).trans
        (getStorage_setStorage_miss s (.map borrowIndexSlot account) (.transient tslot) newBorrowIndex rfl)

set_option maxHeartbeats 200000 in
  theorem guardedLendingBorrowThenRepayMap_unlocked_after (s : ContractState)
      (lockSlot borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot interestReserveSlot account newBorrowIndex borrowAmount repayTotal accruedInterest : Nat) :
      isTransientLocked (guardedLendingBorrowThenRepayMap s lockSlot borrowIndexSlot userPrincipalDebtSlot totalBorrowsSlot poolLiquiditySlot borrowerAssetSlot interestReserveSlot account newBorrowIndex borrowAmount repayTotal accruedInterest) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def lendingLiquidateCollateralMap (s : ContractState)
      (poolLiquiditySlot totalBorrowsSlot borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot account repayAmount seizeCollateral : Nat) : ContractState :=
    mintMap
      (burnMap
        (burnMap
          (burnMap
            (mintMap s poolLiquiditySlot account repayAmount)
            totalBorrowsSlot account repayAmount)
          borrowerDebtSlot account repayAmount)
        borrowerCollateralSlot account seizeCollateral)
      liquidatorCollateralSlot account seizeCollateral

  def guardedLendingLiquidateCollateralMap (s : ContractState)
      (lockSlot poolLiquiditySlot totalBorrowsSlot borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot account repayAmount seizeCollateral : Nat) : ContractState :=
    releaseTransientLock
      (lendingLiquidateCollateralMap (acquireTransientLock s lockSlot) poolLiquiditySlot totalBorrowsSlot borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot account repayAmount seizeCollateral)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem lendingLiquidateCollateralMap_other_slot_frame (s : ContractState)
      (poolLiquiditySlot totalBorrowsSlot borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot otherSlot account observer repayAmount seizeCollateral : Nat)
      (hPool : Nat.beq otherSlot poolLiquiditySlot = false)
      (hTot : Nat.beq otherSlot totalBorrowsSlot = false)
      (hDebt : Nat.beq otherSlot borrowerDebtSlot = false)
      (hBCol : Nat.beq otherSlot borrowerCollateralSlot = false)
      (hLCol : Nat.beq otherSlot liquidatorCollateralSlot = false) :
      getStorage (lendingLiquidateCollateralMap s poolLiquiditySlot totalBorrowsSlot borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot account repayAmount seizeCollateral) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (mintMap_slot_frame _ liquidatorCollateralSlot account seizeCollateral (.map otherSlot observer)
      ((congrArg (· && observer.beq account) hLCol).trans (Bool.false_and _))).trans <|
      (burnMap_slot_frame _ borrowerCollateralSlot account seizeCollateral (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hBCol).trans (Bool.false_and _))).trans <|
      (burnMap_slot_frame _ borrowerDebtSlot account repayAmount (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hDebt).trans (Bool.false_and _))).trans <|
      (burnMap_slot_frame _ totalBorrowsSlot account repayAmount (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hTot).trans (Bool.false_and _))).trans
        (mintMap_slot_frame s poolLiquiditySlot account repayAmount (.map otherSlot observer)
          ((congrArg (· && observer.beq account) hPool).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem lendingLiquidateCollateralMap_liquidator_collateral_updated (s : ContractState)
      (poolLiquiditySlot totalBorrowsSlot borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot account repayAmount seizeCollateral : Nat)
      (hLColBCol : Nat.beq liquidatorCollateralSlot borrowerCollateralSlot = false)
      (hLColDebt : Nat.beq liquidatorCollateralSlot borrowerDebtSlot = false)
      (hLColTot : Nat.beq liquidatorCollateralSlot totalBorrowsSlot = false)
      (hLColPool : Nat.beq liquidatorCollateralSlot poolLiquiditySlot = false) :
      getStorage (lendingLiquidateCollateralMap s poolLiquiditySlot totalBorrowsSlot borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot account repayAmount seizeCollateral) (.map liquidatorCollateralSlot account) =
        getStorage s (.map liquidatorCollateralSlot account) + seizeCollateral :=
    let hMissBCol : StorageKey.fastBeq (.map liquidatorCollateralSlot account) (.map borrowerCollateralSlot account) = false :=
      (congrArg (· && account.beq account) hLColBCol).trans (Bool.false_and _)
    let hMissDebt : StorageKey.fastBeq (.map liquidatorCollateralSlot account) (.map borrowerDebtSlot account) = false :=
      (congrArg (· && account.beq account) hLColDebt).trans (Bool.false_and _)
    let hMissTot : StorageKey.fastBeq (.map liquidatorCollateralSlot account) (.map totalBorrowsSlot account) = false :=
      (congrArg (· && account.beq account) hLColTot).trans (Bool.false_and _)
    let hMissPool : StorageKey.fastBeq (.map liquidatorCollateralSlot account) (.map poolLiquiditySlot account) = false :=
      (congrArg (· && account.beq account) hLColPool).trans (Bool.false_and _)
    getStorage_setStorage_same.trans <|
      congrArg (· + seizeCollateral)
        ((burnMap_slot_frame _ borrowerCollateralSlot account seizeCollateral (.map liquidatorCollateralSlot account) hMissBCol).trans
          ((burnMap_slot_frame _ borrowerDebtSlot account repayAmount (.map liquidatorCollateralSlot account) hMissDebt).trans
            ((burnMap_slot_frame _ totalBorrowsSlot account repayAmount (.map liquidatorCollateralSlot account) hMissTot).trans
              (mintMap_slot_frame s poolLiquiditySlot account repayAmount (.map liquidatorCollateralSlot account) hMissPool))))

set_option maxHeartbeats 200000 in
  theorem lendingLiquidateCollateralMap_borrower_collateral_reduced (s : ContractState)
      (poolLiquiditySlot totalBorrowsSlot borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot account repayAmount seizeCollateral : Nat)
      (hBColLCol : Nat.beq borrowerCollateralSlot liquidatorCollateralSlot = false)
      (hBColDebt : Nat.beq borrowerCollateralSlot borrowerDebtSlot = false)
      (hBColTot : Nat.beq borrowerCollateralSlot totalBorrowsSlot = false)
      (hBColPool : Nat.beq borrowerCollateralSlot poolLiquiditySlot = false) :
      getStorage (lendingLiquidateCollateralMap s poolLiquiditySlot totalBorrowsSlot borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot account repayAmount seizeCollateral) (.map borrowerCollateralSlot account) =
        getStorage s (.map borrowerCollateralSlot account) - seizeCollateral :=
    let hMissLCol : StorageKey.fastBeq (.map borrowerCollateralSlot account) (.map liquidatorCollateralSlot account) = false :=
      (congrArg (· && account.beq account) hBColLCol).trans (Bool.false_and _)
    let hMissDebt : StorageKey.fastBeq (.map borrowerCollateralSlot account) (.map borrowerDebtSlot account) = false :=
      (congrArg (· && account.beq account) hBColDebt).trans (Bool.false_and _)
    let hMissTot : StorageKey.fastBeq (.map borrowerCollateralSlot account) (.map totalBorrowsSlot account) = false :=
      (congrArg (· && account.beq account) hBColTot).trans (Bool.false_and _)
    let hMissPool : StorageKey.fastBeq (.map borrowerCollateralSlot account) (.map poolLiquiditySlot account) = false :=
      (congrArg (· && account.beq account) hBColPool).trans (Bool.false_and _)
    (mintMap_slot_frame _ liquidatorCollateralSlot account seizeCollateral (.map borrowerCollateralSlot account) hMissLCol).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· - seizeCollateral)
          ((burnMap_slot_frame _ borrowerDebtSlot account repayAmount (.map borrowerCollateralSlot account) hMissDebt).trans
            ((burnMap_slot_frame _ totalBorrowsSlot account repayAmount (.map borrowerCollateralSlot account) hMissTot).trans
              (mintMap_slot_frame s poolLiquiditySlot account repayAmount (.map borrowerCollateralSlot account) hMissPool))))

set_option maxHeartbeats 200000 in
  theorem lendingLiquidateCollateralMap_preserves_transient (s : ContractState)
      (poolLiquiditySlot totalBorrowsSlot borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot account repayAmount seizeCollateral tslot : Nat) :
      getStorage (lendingLiquidateCollateralMap s poolLiquiditySlot totalBorrowsSlot borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot account repayAmount seizeCollateral) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (mintMap_slot_frame _ liquidatorCollateralSlot account seizeCollateral (.transient tslot) rfl).trans <|
      (burnMap_slot_frame _ borrowerCollateralSlot account seizeCollateral (.transient tslot) rfl).trans <|
      (burnMap_slot_frame _ borrowerDebtSlot account repayAmount (.transient tslot) rfl).trans <|
      (burnMap_slot_frame _ totalBorrowsSlot account repayAmount (.transient tslot) rfl).trans
        (mintMap_slot_frame s poolLiquiditySlot account repayAmount (.transient tslot) rfl)

set_option maxHeartbeats 200000 in
  theorem guardedLendingLiquidateCollateralMap_unlocked_after (s : ContractState)
      (lockSlot poolLiquiditySlot totalBorrowsSlot borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot account repayAmount seizeCollateral : Nat) :
      isTransientLocked (guardedLendingLiquidateCollateralMap s lockSlot poolLiquiditySlot totalBorrowsSlot borrowerDebtSlot borrowerCollateralSlot liquidatorCollateralSlot account repayAmount seizeCollateral) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def lendingAccrueInterestMap (s : ContractState)
      (totalBorrowsSlot totalReservesSlot borrowIndexSlot lastUpdateBlockSlot account accruedInterest reserveShare currentBlock : Nat) : ContractState :=
    setStorage
      (mintMap
        (mintMap
          (mintMap s totalBorrowsSlot account accruedInterest)
          totalReservesSlot account reserveShare)
        borrowIndexSlot account accruedInterest)
      (.map lastUpdateBlockSlot account)
      currentBlock

  def guardedLendingAccrueInterestMap (s : ContractState)
      (lockSlot totalBorrowsSlot totalReservesSlot borrowIndexSlot lastUpdateBlockSlot account accruedInterest reserveShare currentBlock : Nat) : ContractState :=
    releaseTransientLock
      (lendingAccrueInterestMap (acquireTransientLock s lockSlot) totalBorrowsSlot totalReservesSlot borrowIndexSlot lastUpdateBlockSlot account accruedInterest reserveShare currentBlock)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem lendingAccrueInterestMap_other_slot_frame (s : ContractState)
      (totalBorrowsSlot totalReservesSlot borrowIndexSlot lastUpdateBlockSlot otherSlot account observer accruedInterest reserveShare currentBlock : Nat)
      (hTot : Nat.beq otherSlot totalBorrowsSlot = false)
      (hRes : Nat.beq otherSlot totalReservesSlot = false)
      (hIdx : Nat.beq otherSlot borrowIndexSlot = false)
      (hBlk : Nat.beq otherSlot lastUpdateBlockSlot = false) :
      getStorage (lendingAccrueInterestMap s totalBorrowsSlot totalReservesSlot borrowIndexSlot lastUpdateBlockSlot account accruedInterest reserveShare currentBlock) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (getStorage_setStorage_miss _ (.map lastUpdateBlockSlot account) (.map otherSlot observer) currentBlock
      ((congrArg (· && observer.beq account) hBlk).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ borrowIndexSlot account accruedInterest (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hIdx).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ totalReservesSlot account reserveShare (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hRes).trans (Bool.false_and _))).trans
        (mintMap_slot_frame s totalBorrowsSlot account accruedInterest (.map otherSlot observer)
          ((congrArg (· && observer.beq account) hTot).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem lendingAccrueInterestMap_last_update_block_updated (s : ContractState)
      (totalBorrowsSlot totalReservesSlot borrowIndexSlot lastUpdateBlockSlot account accruedInterest reserveShare currentBlock : Nat) :
      getStorage (lendingAccrueInterestMap s totalBorrowsSlot totalReservesSlot borrowIndexSlot lastUpdateBlockSlot account accruedInterest reserveShare currentBlock) (.map lastUpdateBlockSlot account) =
        currentBlock :=
    getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem lendingAccrueInterestMap_borrow_index_updated (s : ContractState)
      (totalBorrowsSlot totalReservesSlot borrowIndexSlot lastUpdateBlockSlot account accruedInterest reserveShare currentBlock : Nat)
      (hIdxBlk : Nat.beq borrowIndexSlot lastUpdateBlockSlot = false)
      (hIdxRes : Nat.beq borrowIndexSlot totalReservesSlot = false)
      (hIdxTot : Nat.beq borrowIndexSlot totalBorrowsSlot = false) :
      getStorage (lendingAccrueInterestMap s totalBorrowsSlot totalReservesSlot borrowIndexSlot lastUpdateBlockSlot account accruedInterest reserveShare currentBlock) (.map borrowIndexSlot account) =
        getStorage s (.map borrowIndexSlot account) + accruedInterest :=
    let hMissBlk : StorageKey.fastBeq (.map borrowIndexSlot account) (.map lastUpdateBlockSlot account) = false :=
      (congrArg (· && account.beq account) hIdxBlk).trans (Bool.false_and _)
    let hMissRes : StorageKey.fastBeq (.map borrowIndexSlot account) (.map totalReservesSlot account) = false :=
      (congrArg (· && account.beq account) hIdxRes).trans (Bool.false_and _)
    let hMissTot : StorageKey.fastBeq (.map borrowIndexSlot account) (.map totalBorrowsSlot account) = false :=
      (congrArg (· && account.beq account) hIdxTot).trans (Bool.false_and _)
    (getStorage_setStorage_miss _ (.map lastUpdateBlockSlot account) (.map borrowIndexSlot account) currentBlock hMissBlk).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· + accruedInterest)
          ((mintMap_slot_frame _ totalReservesSlot account reserveShare (.map borrowIndexSlot account) hMissRes).trans
            (mintMap_slot_frame s totalBorrowsSlot account accruedInterest (.map borrowIndexSlot account) hMissTot)))

set_option maxHeartbeats 200000 in
  theorem lendingAccrueInterestMap_preserves_transient (s : ContractState)
      (totalBorrowsSlot totalReservesSlot borrowIndexSlot lastUpdateBlockSlot account accruedInterest reserveShare currentBlock tslot : Nat) :
      getStorage (lendingAccrueInterestMap s totalBorrowsSlot totalReservesSlot borrowIndexSlot lastUpdateBlockSlot account accruedInterest reserveShare currentBlock) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (getStorage_setStorage_miss _ (.map lastUpdateBlockSlot account) (.transient tslot) currentBlock rfl).trans <|
      (mintMap_slot_frame _ borrowIndexSlot account accruedInterest (.transient tslot) rfl).trans <|
      (mintMap_slot_frame _ totalReservesSlot account reserveShare (.transient tslot) rfl).trans
        (mintMap_slot_frame s totalBorrowsSlot account accruedInterest (.transient tslot) rfl)

set_option maxHeartbeats 200000 in
  theorem guardedLendingAccrueInterestMap_unlocked_after (s : ContractState)
      (lockSlot totalBorrowsSlot totalReservesSlot borrowIndexSlot lastUpdateBlockSlot account accruedInterest reserveShare currentBlock : Nat) :
      isTransientLocked (guardedLendingAccrueInterestMap s lockSlot totalBorrowsSlot totalReservesSlot borrowIndexSlot lastUpdateBlockSlot account accruedInterest reserveShare currentBlock) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def governanceQueueProposalMap (s : ContractState)
      (proposalEtaSlot proposalTargetSlot proposalValueSlot proposalCountSlot account eta target value : Nat) : ContractState :=
    mintMap
      (setStorage
        (setStorage
          (setStorage s (.map proposalEtaSlot account) eta)
          (.map proposalTargetSlot account) target)
        (.map proposalValueSlot account) value)
      proposalCountSlot account 1

  def governanceExecuteProposalMap (s : ContractState)
      (proposalExecutedSlot vaultBalanceSlot recipientBalanceSlot account value : Nat) : ContractState :=
    setStorage
      (mintMap
        (burnMap s vaultBalanceSlot account value)
        recipientBalanceSlot account value)
      (.map proposalExecutedSlot account) 1

  def guardedGovernanceExecuteProposalMap (s : ContractState)
      (lockSlot proposalExecutedSlot vaultBalanceSlot recipientBalanceSlot account value : Nat) : ContractState :=
    releaseTransientLock
      (governanceExecuteProposalMap (acquireTransientLock s lockSlot) proposalExecutedSlot vaultBalanceSlot recipientBalanceSlot account value)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem governanceQueueProposalMap_other_slot_frame (s : ContractState)
      (proposalEtaSlot proposalTargetSlot proposalValueSlot proposalCountSlot otherSlot account observer eta target value : Nat)
      (hEta : Nat.beq otherSlot proposalEtaSlot = false)
      (hTgt : Nat.beq otherSlot proposalTargetSlot = false)
      (hVal : Nat.beq otherSlot proposalValueSlot = false)
      (hCnt : Nat.beq otherSlot proposalCountSlot = false) :
      getStorage (governanceQueueProposalMap s proposalEtaSlot proposalTargetSlot proposalValueSlot proposalCountSlot account eta target value) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (mintMap_slot_frame _ proposalCountSlot account 1 (.map otherSlot observer)
      ((congrArg (· && observer.beq account) hCnt).trans (Bool.false_and _))).trans <|
      (getStorage_setStorage_miss _ (.map proposalValueSlot account) (.map otherSlot observer) value
        ((congrArg (· && observer.beq account) hVal).trans (Bool.false_and _))).trans <|
      (getStorage_setStorage_miss _ (.map proposalTargetSlot account) (.map otherSlot observer) target
        ((congrArg (· && observer.beq account) hTgt).trans (Bool.false_and _))).trans
        (getStorage_setStorage_miss s (.map proposalEtaSlot account) (.map otherSlot observer) eta
          ((congrArg (· && observer.beq account) hEta).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem governanceQueueProposalMap_proposal_count_incremented (s : ContractState)
      (proposalEtaSlot proposalTargetSlot proposalValueSlot proposalCountSlot account eta target value : Nat)
      (hCntVal : Nat.beq proposalCountSlot proposalValueSlot = false)
      (hCntTgt : Nat.beq proposalCountSlot proposalTargetSlot = false)
      (hCntEta : Nat.beq proposalCountSlot proposalEtaSlot = false) :
      getStorage (governanceQueueProposalMap s proposalEtaSlot proposalTargetSlot proposalValueSlot proposalCountSlot account eta target value) (.map proposalCountSlot account) =
        getStorage s (.map proposalCountSlot account) + 1 :=
    let hMissVal : StorageKey.fastBeq (.map proposalCountSlot account) (.map proposalValueSlot account) = false :=
      (congrArg (· && account.beq account) hCntVal).trans (Bool.false_and _)
    let hMissTgt : StorageKey.fastBeq (.map proposalCountSlot account) (.map proposalTargetSlot account) = false :=
      (congrArg (· && account.beq account) hCntTgt).trans (Bool.false_and _)
    let hMissEta : StorageKey.fastBeq (.map proposalCountSlot account) (.map proposalEtaSlot account) = false :=
      (congrArg (· && account.beq account) hCntEta).trans (Bool.false_and _)
    getStorage_setStorage_same.trans
      (congrArg (· + 1)
        ((getStorage_setStorage_miss _ (.map proposalValueSlot account) (.map proposalCountSlot account) value hMissVal).trans
          ((getStorage_setStorage_miss _ (.map proposalTargetSlot account) (.map proposalCountSlot account) target hMissTgt).trans
            (getStorage_setStorage_miss s (.map proposalEtaSlot account) (.map proposalCountSlot account) eta hMissEta))))

set_option maxHeartbeats 200000 in
  theorem governanceQueueProposalMap_eta_recorded (s : ContractState)
      (proposalEtaSlot proposalTargetSlot proposalValueSlot proposalCountSlot account eta target value : Nat)
      (hEtaCnt : Nat.beq proposalEtaSlot proposalCountSlot = false)
      (hEtaVal : Nat.beq proposalEtaSlot proposalValueSlot = false)
      (hEtaTgt : Nat.beq proposalEtaSlot proposalTargetSlot = false) :
      getStorage (governanceQueueProposalMap s proposalEtaSlot proposalTargetSlot proposalValueSlot proposalCountSlot account eta target value) (.map proposalEtaSlot account) =
        eta :=
    let hMissCnt : StorageKey.fastBeq (.map proposalEtaSlot account) (.map proposalCountSlot account) = false :=
      (congrArg (· && account.beq account) hEtaCnt).trans (Bool.false_and _)
    let hMissVal : StorageKey.fastBeq (.map proposalEtaSlot account) (.map proposalValueSlot account) = false :=
      (congrArg (· && account.beq account) hEtaVal).trans (Bool.false_and _)
    let hMissTgt : StorageKey.fastBeq (.map proposalEtaSlot account) (.map proposalTargetSlot account) = false :=
      (congrArg (· && account.beq account) hEtaTgt).trans (Bool.false_and _)
    (mintMap_slot_frame _ proposalCountSlot account 1 (.map proposalEtaSlot account) hMissCnt).trans <|
      (getStorage_setStorage_miss _ (.map proposalValueSlot account) (.map proposalEtaSlot account) value hMissVal).trans <|
      (getStorage_setStorage_miss _ (.map proposalTargetSlot account) (.map proposalEtaSlot account) target hMissTgt).trans
        getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem governanceQueueProposalMap_preserves_transient (s : ContractState)
      (proposalEtaSlot proposalTargetSlot proposalValueSlot proposalCountSlot account eta target value tslot : Nat) :
      getStorage (governanceQueueProposalMap s proposalEtaSlot proposalTargetSlot proposalValueSlot proposalCountSlot account eta target value) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (mintMap_slot_frame _ proposalCountSlot account 1 (.transient tslot) rfl).trans <|
      (getStorage_setStorage_miss _ (.map proposalValueSlot account) (.transient tslot) value rfl).trans <|
      (getStorage_setStorage_miss _ (.map proposalTargetSlot account) (.transient tslot) target rfl).trans
        (getStorage_setStorage_miss s (.map proposalEtaSlot account) (.transient tslot) eta rfl)

set_option maxHeartbeats 200000 in
  theorem guardedGovernanceExecuteProposalMap_unlocked_after (s : ContractState)
      (lockSlot proposalExecutedSlot vaultBalanceSlot recipientBalanceSlot account value : Nat) :
      isTransientLocked (guardedGovernanceExecuteProposalMap s lockSlot proposalExecutedSlot vaultBalanceSlot recipientBalanceSlot account value) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def governanceDelegateVotesMap (s : ContractState)
      (fromDelegateVotesSlot toDelegateVotesSlot delegatorDelegateSlot account newDelegate weight : Nat) : ContractState :=
    setStorage
      (mintMap
        (burnMap s fromDelegateVotesSlot account weight)
        toDelegateVotesSlot account weight)
      (.map delegatorDelegateSlot account)
      newDelegate

  def guardedGovernanceDelegateVotesMap (s : ContractState)
      (lockSlot fromDelegateVotesSlot toDelegateVotesSlot delegatorDelegateSlot account newDelegate weight : Nat) : ContractState :=
    releaseTransientLock
      (governanceDelegateVotesMap (acquireTransientLock s lockSlot) fromDelegateVotesSlot toDelegateVotesSlot delegatorDelegateSlot account newDelegate weight)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem governanceDelegateVotesMap_other_slot_frame (s : ContractState)
      (fromDelegateVotesSlot toDelegateVotesSlot delegatorDelegateSlot otherSlot account observer newDelegate weight : Nat)
      (hFrom : Nat.beq otherSlot fromDelegateVotesSlot = false)
      (hTo : Nat.beq otherSlot toDelegateVotesSlot = false)
      (hDel : Nat.beq otherSlot delegatorDelegateSlot = false) :
      getStorage (governanceDelegateVotesMap s fromDelegateVotesSlot toDelegateVotesSlot delegatorDelegateSlot account newDelegate weight) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (getStorage_setStorage_miss _ (.map delegatorDelegateSlot account) (.map otherSlot observer) newDelegate
      ((congrArg (· && observer.beq account) hDel).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ toDelegateVotesSlot account weight (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hTo).trans (Bool.false_and _))).trans
        (burnMap_slot_frame s fromDelegateVotesSlot account weight (.map otherSlot observer)
          ((congrArg (· && observer.beq account) hFrom).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem governanceDelegateVotesMap_delegate_recorded (s : ContractState)
      (fromDelegateVotesSlot toDelegateVotesSlot delegatorDelegateSlot account newDelegate weight : Nat) :
      getStorage (governanceDelegateVotesMap s fromDelegateVotesSlot toDelegateVotesSlot delegatorDelegateSlot account newDelegate weight) (.map delegatorDelegateSlot account) =
        newDelegate :=
    getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem governanceDelegateVotesMap_to_votes_increased (s : ContractState)
      (fromDelegateVotesSlot toDelegateVotesSlot delegatorDelegateSlot account newDelegate weight : Nat)
      (hToDel : Nat.beq toDelegateVotesSlot delegatorDelegateSlot = false)
      (hToFrom : Nat.beq toDelegateVotesSlot fromDelegateVotesSlot = false) :
      getStorage (governanceDelegateVotesMap s fromDelegateVotesSlot toDelegateVotesSlot delegatorDelegateSlot account newDelegate weight) (.map toDelegateVotesSlot account) =
        getStorage s (.map toDelegateVotesSlot account) + weight :=
    let hMissDel : StorageKey.fastBeq (.map toDelegateVotesSlot account) (.map delegatorDelegateSlot account) = false :=
      (congrArg (· && account.beq account) hToDel).trans (Bool.false_and _)
    let hMissFrom : StorageKey.fastBeq (.map toDelegateVotesSlot account) (.map fromDelegateVotesSlot account) = false :=
      (congrArg (· && account.beq account) hToFrom).trans (Bool.false_and _)
    (getStorage_setStorage_miss _ (.map delegatorDelegateSlot account) (.map toDelegateVotesSlot account) newDelegate hMissDel).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· + weight)
          (burnMap_slot_frame s fromDelegateVotesSlot account weight (.map toDelegateVotesSlot account) hMissFrom))

set_option maxHeartbeats 200000 in
  theorem governanceDelegateVotesMap_preserves_transient (s : ContractState)
      (fromDelegateVotesSlot toDelegateVotesSlot delegatorDelegateSlot account newDelegate weight tslot : Nat) :
      getStorage (governanceDelegateVotesMap s fromDelegateVotesSlot toDelegateVotesSlot delegatorDelegateSlot account newDelegate weight) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (getStorage_setStorage_miss _ (.map delegatorDelegateSlot account) (.transient tslot) newDelegate rfl).trans <|
      (mintMap_slot_frame _ toDelegateVotesSlot account weight (.transient tslot) rfl).trans
        (burnMap_slot_frame s fromDelegateVotesSlot account weight (.transient tslot) rfl)

set_option maxHeartbeats 200000 in
  theorem guardedGovernanceDelegateVotesMap_unlocked_after (s : ContractState)
      (lockSlot fromDelegateVotesSlot toDelegateVotesSlot delegatorDelegateSlot account newDelegate weight : Nat) :
      isTransientLocked (guardedGovernanceDelegateVotesMap s lockSlot fromDelegateVotesSlot toDelegateVotesSlot delegatorDelegateSlot account newDelegate weight) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def governanceCastVoteMap (s : ContractState)
      (forVotesSlot againstVotesSlot voterReceiptSlot account forWeight againstWeight : Nat) : ContractState :=
    setStorage
      (mintMap
        (mintMap s forVotesSlot account forWeight)
        againstVotesSlot account againstWeight)
      (.map voterReceiptSlot account)
      1

  def guardedGovernanceCastVoteMap (s : ContractState)
      (lockSlot forVotesSlot againstVotesSlot voterReceiptSlot account forWeight againstWeight : Nat) : ContractState :=
    releaseTransientLock
      (governanceCastVoteMap (acquireTransientLock s lockSlot) forVotesSlot againstVotesSlot voterReceiptSlot account forWeight againstWeight)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem governanceCastVoteMap_other_slot_frame (s : ContractState)
      (forVotesSlot againstVotesSlot voterReceiptSlot otherSlot account observer forWeight againstWeight : Nat)
      (hFor : Nat.beq otherSlot forVotesSlot = false)
      (hAgainst : Nat.beq otherSlot againstVotesSlot = false)
      (hRec : Nat.beq otherSlot voterReceiptSlot = false) :
      getStorage (governanceCastVoteMap s forVotesSlot againstVotesSlot voterReceiptSlot account forWeight againstWeight) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (getStorage_setStorage_miss _ (.map voterReceiptSlot account) (.map otherSlot observer) 1
      ((congrArg (· && observer.beq account) hRec).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ againstVotesSlot account againstWeight (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hAgainst).trans (Bool.false_and _))).trans
        (mintMap_slot_frame s forVotesSlot account forWeight (.map otherSlot observer)
          ((congrArg (· && observer.beq account) hFor).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem governanceCastVoteMap_receipt_recorded (s : ContractState)
      (forVotesSlot againstVotesSlot voterReceiptSlot account forWeight againstWeight : Nat) :
      getStorage (governanceCastVoteMap s forVotesSlot againstVotesSlot voterReceiptSlot account forWeight againstWeight) (.map voterReceiptSlot account) =
        1 :=
    getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem governanceCastVoteMap_against_votes_updated (s : ContractState)
      (forVotesSlot againstVotesSlot voterReceiptSlot account forWeight againstWeight : Nat)
      (hAgainstRec : Nat.beq againstVotesSlot voterReceiptSlot = false)
      (hAgainstFor : Nat.beq againstVotesSlot forVotesSlot = false) :
      getStorage (governanceCastVoteMap s forVotesSlot againstVotesSlot voterReceiptSlot account forWeight againstWeight) (.map againstVotesSlot account) =
        getStorage s (.map againstVotesSlot account) + againstWeight :=
    let hMissRec : StorageKey.fastBeq (.map againstVotesSlot account) (.map voterReceiptSlot account) = false :=
      (congrArg (· && account.beq account) hAgainstRec).trans (Bool.false_and _)
    let hMissFor : StorageKey.fastBeq (.map againstVotesSlot account) (.map forVotesSlot account) = false :=
      (congrArg (· && account.beq account) hAgainstFor).trans (Bool.false_and _)
    (getStorage_setStorage_miss _ (.map voterReceiptSlot account) (.map againstVotesSlot account) 1 hMissRec).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· + againstWeight)
          (mintMap_slot_frame s forVotesSlot account forWeight (.map againstVotesSlot account) hMissFor))

set_option maxHeartbeats 200000 in
  theorem governanceCastVoteMap_preserves_transient (s : ContractState)
      (forVotesSlot againstVotesSlot voterReceiptSlot account forWeight againstWeight tslot : Nat) :
      getStorage (governanceCastVoteMap s forVotesSlot againstVotesSlot voterReceiptSlot account forWeight againstWeight) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (getStorage_setStorage_miss _ (.map voterReceiptSlot account) (.transient tslot) 1 rfl).trans <|
      (mintMap_slot_frame _ againstVotesSlot account againstWeight (.transient tslot) rfl).trans
        (mintMap_slot_frame s forVotesSlot account forWeight (.transient tslot) rfl)

set_option maxHeartbeats 200000 in
  theorem guardedGovernanceCastVoteMap_unlocked_after (s : ContractState)
      (lockSlot forVotesSlot againstVotesSlot voterReceiptSlot account forWeight againstWeight : Nat) :
      isTransientLocked (guardedGovernanceCastVoteMap s lockSlot forVotesSlot againstVotesSlot voterReceiptSlot account forWeight againstWeight) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def governanceCancelProposalMap (s : ContractState)
      (proposalStateSlot proposalEtaSlot activeProposalsSlot account : Nat) : ContractState :=
    burnMap
      (setStorage
        (setStorage s (.map proposalStateSlot account) 2)
        (.map proposalEtaSlot account) 0)
      activeProposalsSlot account 1

  def guardedGovernanceCancelProposalMap (s : ContractState)
      (lockSlot proposalStateSlot proposalEtaSlot activeProposalsSlot account : Nat) : ContractState :=
    releaseTransientLock
      (governanceCancelProposalMap (acquireTransientLock s lockSlot) proposalStateSlot proposalEtaSlot activeProposalsSlot account)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem governanceCancelProposalMap_other_slot_frame (s : ContractState)
      (proposalStateSlot proposalEtaSlot activeProposalsSlot otherSlot account observer : Nat)
      (hState : Nat.beq otherSlot proposalStateSlot = false)
      (hEta : Nat.beq otherSlot proposalEtaSlot = false)
      (hAct : Nat.beq otherSlot activeProposalsSlot = false) :
      getStorage (governanceCancelProposalMap s proposalStateSlot proposalEtaSlot activeProposalsSlot account) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (burnMap_slot_frame _ activeProposalsSlot account 1 (.map otherSlot observer)
      ((congrArg (· && observer.beq account) hAct).trans (Bool.false_and _))).trans <|
      (getStorage_setStorage_miss _ (.map proposalEtaSlot account) (.map otherSlot observer) 0
        ((congrArg (· && observer.beq account) hEta).trans (Bool.false_and _))).trans
        (getStorage_setStorage_miss s (.map proposalStateSlot account) (.map otherSlot observer) 2
          ((congrArg (· && observer.beq account) hState).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem governanceCancelProposalMap_active_proposals_decremented (s : ContractState)
      (proposalStateSlot proposalEtaSlot activeProposalsSlot account : Nat)
      (hActEta : Nat.beq activeProposalsSlot proposalEtaSlot = false)
      (hActState : Nat.beq activeProposalsSlot proposalStateSlot = false) :
      getStorage (governanceCancelProposalMap s proposalStateSlot proposalEtaSlot activeProposalsSlot account) (.map activeProposalsSlot account) =
        getStorage s (.map activeProposalsSlot account) - 1 :=
    let hMissEta : StorageKey.fastBeq (.map activeProposalsSlot account) (.map proposalEtaSlot account) = false :=
      (congrArg (· && account.beq account) hActEta).trans (Bool.false_and _)
    let hMissState : StorageKey.fastBeq (.map activeProposalsSlot account) (.map proposalStateSlot account) = false :=
      (congrArg (· && account.beq account) hActState).trans (Bool.false_and _)
    getStorage_setStorage_same.trans
      (congrArg (· - 1)
        ((getStorage_setStorage_miss _ (.map proposalEtaSlot account) (.map activeProposalsSlot account) 0 hMissEta).trans
          (getStorage_setStorage_miss s (.map proposalStateSlot account) (.map activeProposalsSlot account) 2 hMissState)))

set_option maxHeartbeats 200000 in
  theorem governanceCancelProposalMap_eta_cleared (s : ContractState)
      (proposalStateSlot proposalEtaSlot activeProposalsSlot account : Nat)
      (hEtaAct : Nat.beq proposalEtaSlot activeProposalsSlot = false) :
      getStorage (governanceCancelProposalMap s proposalStateSlot proposalEtaSlot activeProposalsSlot account) (.map proposalEtaSlot account) =
        0 :=
    let hMissAct : StorageKey.fastBeq (.map proposalEtaSlot account) (.map activeProposalsSlot account) = false :=
      (congrArg (· && account.beq account) hEtaAct).trans (Bool.false_and _)
    (burnMap_slot_frame _ activeProposalsSlot account 1 (.map proposalEtaSlot account) hMissAct).trans
      getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem governanceCancelProposalMap_preserves_transient (s : ContractState)
      (proposalStateSlot proposalEtaSlot activeProposalsSlot account tslot : Nat) :
      getStorage (governanceCancelProposalMap s proposalStateSlot proposalEtaSlot activeProposalsSlot account) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (burnMap_slot_frame _ activeProposalsSlot account 1 (.transient tslot) rfl).trans <|
      (getStorage_setStorage_miss _ (.map proposalEtaSlot account) (.transient tslot) 0 rfl).trans
        (getStorage_setStorage_miss s (.map proposalStateSlot account) (.transient tslot) 2 rfl)

set_option maxHeartbeats 200000 in
  theorem guardedGovernanceCancelProposalMap_unlocked_after (s : ContractState)
      (lockSlot proposalStateSlot proposalEtaSlot activeProposalsSlot account : Nat) :
      isTransientLocked (guardedGovernanceCancelProposalMap s lockSlot proposalStateSlot proposalEtaSlot activeProposalsSlot account) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def bridgeLockAndMintMap (s : ContractState)
      (senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot nonceSlot account amount : Nat) : ContractState :=
    mintMap
      (mintMap
        (mintMap
          (mintMap
            (burnMap s senderBalanceSlot account amount)
            sourceVaultSlot account amount)
          destSupplySlot account amount)
        recipientMintedSlot account amount)
      nonceSlot account 1

  def guardedBridgeLockAndMintMap (s : ContractState)
      (lockSlot senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot nonceSlot account amount : Nat) : ContractState :=
    releaseTransientLock
      (bridgeLockAndMintMap (acquireTransientLock s lockSlot) senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot nonceSlot account amount)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem bridgeLockAndMintMap_other_slot_frame (s : ContractState)
      (senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot nonceSlot otherSlot account observer amount : Nat)
      (hSnd : Nat.beq otherSlot senderBalanceSlot = false)
      (hSrc : Nat.beq otherSlot sourceVaultSlot = false)
      (hDst : Nat.beq otherSlot destSupplySlot = false)
      (hRcp : Nat.beq otherSlot recipientMintedSlot = false)
      (hNnc : Nat.beq otherSlot nonceSlot = false) :
      getStorage (bridgeLockAndMintMap s senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot nonceSlot account amount) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (mintMap_slot_frame _ nonceSlot account 1 (.map otherSlot observer)
      ((congrArg (· && observer.beq account) hNnc).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ recipientMintedSlot account amount (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hRcp).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ destSupplySlot account amount (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hDst).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ sourceVaultSlot account amount (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hSrc).trans (Bool.false_and _))).trans
        (burnMap_slot_frame s senderBalanceSlot account amount (.map otherSlot observer)
          ((congrArg (· && observer.beq account) hSnd).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem bridgeLockAndMintMap_nonce_incremented (s : ContractState)
      (senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot nonceSlot account amount : Nat)
      (hNncRcp : Nat.beq nonceSlot recipientMintedSlot = false)
      (hNncDst : Nat.beq nonceSlot destSupplySlot = false)
      (hNncSrc : Nat.beq nonceSlot sourceVaultSlot = false)
      (hNncSnd : Nat.beq nonceSlot senderBalanceSlot = false) :
      getStorage (bridgeLockAndMintMap s senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot nonceSlot account amount) (.map nonceSlot account) =
        getStorage s (.map nonceSlot account) + 1 :=
    let hMissRcp : StorageKey.fastBeq (.map nonceSlot account) (.map recipientMintedSlot account) = false :=
      (congrArg (· && account.beq account) hNncRcp).trans (Bool.false_and _)
    let hMissDst : StorageKey.fastBeq (.map nonceSlot account) (.map destSupplySlot account) = false :=
      (congrArg (· && account.beq account) hNncDst).trans (Bool.false_and _)
    let hMissSrc : StorageKey.fastBeq (.map nonceSlot account) (.map sourceVaultSlot account) = false :=
      (congrArg (· && account.beq account) hNncSrc).trans (Bool.false_and _)
    let hMissSnd : StorageKey.fastBeq (.map nonceSlot account) (.map senderBalanceSlot account) = false :=
      (congrArg (· && account.beq account) hNncSnd).trans (Bool.false_and _)
    getStorage_setStorage_same.trans
      (congrArg (· + 1)
        ((mintMap_slot_frame _ recipientMintedSlot account amount (.map nonceSlot account) hMissRcp).trans
          ((mintMap_slot_frame _ destSupplySlot account amount (.map nonceSlot account) hMissDst).trans
            ((mintMap_slot_frame _ sourceVaultSlot account amount (.map nonceSlot account) hMissSrc).trans
              (burnMap_slot_frame s senderBalanceSlot account amount (.map nonceSlot account) hMissSnd)))))

set_option maxHeartbeats 200000 in
  theorem bridgeLockAndMintMap_recipient_minted_updated (s : ContractState)
      (senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot nonceSlot account amount : Nat)
      (hRcpNnc : Nat.beq recipientMintedSlot nonceSlot = false)
      (hRcpDst : Nat.beq recipientMintedSlot destSupplySlot = false)
      (hRcpSrc : Nat.beq recipientMintedSlot sourceVaultSlot = false)
      (hRcpSnd : Nat.beq recipientMintedSlot senderBalanceSlot = false) :
      getStorage (bridgeLockAndMintMap s senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot nonceSlot account amount) (.map recipientMintedSlot account) =
        getStorage s (.map recipientMintedSlot account) + amount :=
    let hMissNnc : StorageKey.fastBeq (.map recipientMintedSlot account) (.map nonceSlot account) = false :=
      (congrArg (· && account.beq account) hRcpNnc).trans (Bool.false_and _)
    let hMissDst : StorageKey.fastBeq (.map recipientMintedSlot account) (.map destSupplySlot account) = false :=
      (congrArg (· && account.beq account) hRcpDst).trans (Bool.false_and _)
    let hMissSrc : StorageKey.fastBeq (.map recipientMintedSlot account) (.map sourceVaultSlot account) = false :=
      (congrArg (· && account.beq account) hRcpSrc).trans (Bool.false_and _)
    let hMissSnd : StorageKey.fastBeq (.map recipientMintedSlot account) (.map senderBalanceSlot account) = false :=
      (congrArg (· && account.beq account) hRcpSnd).trans (Bool.false_and _)
    (mintMap_slot_frame _ nonceSlot account 1 (.map recipientMintedSlot account) hMissNnc).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· + amount)
          ((mintMap_slot_frame _ destSupplySlot account amount (.map recipientMintedSlot account) hMissDst).trans
            ((mintMap_slot_frame _ sourceVaultSlot account amount (.map recipientMintedSlot account) hMissSrc).trans
              (burnMap_slot_frame s senderBalanceSlot account amount (.map recipientMintedSlot account) hMissSnd))))

set_option maxHeartbeats 200000 in
  theorem bridgeLockAndMintMap_preserves_transient (s : ContractState)
      (senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot nonceSlot account amount tslot : Nat) :
      getStorage (bridgeLockAndMintMap s senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot nonceSlot account amount) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (mintMap_slot_frame _ nonceSlot account 1 (.transient tslot) rfl).trans <|
      (mintMap_slot_frame _ recipientMintedSlot account amount (.transient tslot) rfl).trans <|
      (mintMap_slot_frame _ destSupplySlot account amount (.transient tslot) rfl).trans <|
      (mintMap_slot_frame _ sourceVaultSlot account amount (.transient tslot) rfl).trans
        (burnMap_slot_frame s senderBalanceSlot account amount (.transient tslot) rfl)

set_option maxHeartbeats 200000 in
  theorem guardedBridgeLockAndMintMap_unlocked_after (s : ContractState)
      (lockSlot senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot nonceSlot account amount : Nat) :
      isTransientLocked (guardedBridgeLockAndMintMap s lockSlot senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot nonceSlot account amount) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def bridgeBurnAndReleaseMap (s : ContractState)
      (burnerMintedSlot destSupplySlot sourceVaultSlot recipientBalanceSlot burnNonceSlot account amount : Nat) : ContractState :=
    mintMap
      (mintMap
        (burnMap
          (burnMap
            (burnMap s burnerMintedSlot account amount)
            destSupplySlot account amount)
          sourceVaultSlot account amount)
        recipientBalanceSlot account amount)
      burnNonceSlot account 1

  def guardedBridgeBurnAndReleaseMap (s : ContractState)
      (lockSlot burnerMintedSlot destSupplySlot sourceVaultSlot recipientBalanceSlot burnNonceSlot account amount : Nat) : ContractState :=
    releaseTransientLock
      (bridgeBurnAndReleaseMap (acquireTransientLock s lockSlot) burnerMintedSlot destSupplySlot sourceVaultSlot recipientBalanceSlot burnNonceSlot account amount)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem bridgeBurnAndReleaseMap_other_slot_frame (s : ContractState)
      (burnerMintedSlot destSupplySlot sourceVaultSlot recipientBalanceSlot burnNonceSlot otherSlot account observer amount : Nat)
      (hBrn : Nat.beq otherSlot burnerMintedSlot = false)
      (hDst : Nat.beq otherSlot destSupplySlot = false)
      (hSrc : Nat.beq otherSlot sourceVaultSlot = false)
      (hRcp : Nat.beq otherSlot recipientBalanceSlot = false)
      (hNnc : Nat.beq otherSlot burnNonceSlot = false) :
      getStorage (bridgeBurnAndReleaseMap s burnerMintedSlot destSupplySlot sourceVaultSlot recipientBalanceSlot burnNonceSlot account amount) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (mintMap_slot_frame _ burnNonceSlot account 1 (.map otherSlot observer)
      ((congrArg (· && observer.beq account) hNnc).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ recipientBalanceSlot account amount (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hRcp).trans (Bool.false_and _))).trans <|
      (burnMap_slot_frame _ sourceVaultSlot account amount (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hSrc).trans (Bool.false_and _))).trans <|
      (burnMap_slot_frame _ destSupplySlot account amount (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hDst).trans (Bool.false_and _))).trans
        (burnMap_slot_frame s burnerMintedSlot account amount (.map otherSlot observer)
          ((congrArg (· && observer.beq account) hBrn).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem bridgeBurnAndReleaseMap_burn_nonce_incremented (s : ContractState)
      (burnerMintedSlot destSupplySlot sourceVaultSlot recipientBalanceSlot burnNonceSlot account amount : Nat)
      (hNncRcp : Nat.beq burnNonceSlot recipientBalanceSlot = false)
      (hNncSrc : Nat.beq burnNonceSlot sourceVaultSlot = false)
      (hNncDst : Nat.beq burnNonceSlot destSupplySlot = false)
      (hNncBrn : Nat.beq burnNonceSlot burnerMintedSlot = false) :
      getStorage (bridgeBurnAndReleaseMap s burnerMintedSlot destSupplySlot sourceVaultSlot recipientBalanceSlot burnNonceSlot account amount) (.map burnNonceSlot account) =
        getStorage s (.map burnNonceSlot account) + 1 :=
    let hMissRcp : StorageKey.fastBeq (.map burnNonceSlot account) (.map recipientBalanceSlot account) = false :=
      (congrArg (· && account.beq account) hNncRcp).trans (Bool.false_and _)
    let hMissSrc : StorageKey.fastBeq (.map burnNonceSlot account) (.map sourceVaultSlot account) = false :=
      (congrArg (· && account.beq account) hNncSrc).trans (Bool.false_and _)
    let hMissDst : StorageKey.fastBeq (.map burnNonceSlot account) (.map destSupplySlot account) = false :=
      (congrArg (· && account.beq account) hNncDst).trans (Bool.false_and _)
    let hMissBrn : StorageKey.fastBeq (.map burnNonceSlot account) (.map burnerMintedSlot account) = false :=
      (congrArg (· && account.beq account) hNncBrn).trans (Bool.false_and _)
    getStorage_setStorage_same.trans
      (congrArg (· + 1)
        ((mintMap_slot_frame _ recipientBalanceSlot account amount (.map burnNonceSlot account) hMissRcp).trans
          ((burnMap_slot_frame _ sourceVaultSlot account amount (.map burnNonceSlot account) hMissSrc).trans
            ((burnMap_slot_frame _ destSupplySlot account amount (.map burnNonceSlot account) hMissDst).trans
              (burnMap_slot_frame s burnerMintedSlot account amount (.map burnNonceSlot account) hMissBrn)))))

set_option maxHeartbeats 200000 in
  theorem bridgeBurnAndReleaseMap_recipient_balance_updated (s : ContractState)
      (burnerMintedSlot destSupplySlot sourceVaultSlot recipientBalanceSlot burnNonceSlot account amount : Nat)
      (hRcpNnc : Nat.beq recipientBalanceSlot burnNonceSlot = false)
      (hRcpSrc : Nat.beq recipientBalanceSlot sourceVaultSlot = false)
      (hRcpDst : Nat.beq recipientBalanceSlot destSupplySlot = false)
      (hRcpBrn : Nat.beq recipientBalanceSlot burnerMintedSlot = false) :
      getStorage (bridgeBurnAndReleaseMap s burnerMintedSlot destSupplySlot sourceVaultSlot recipientBalanceSlot burnNonceSlot account amount) (.map recipientBalanceSlot account) =
        getStorage s (.map recipientBalanceSlot account) + amount :=
    let hMissNnc : StorageKey.fastBeq (.map recipientBalanceSlot account) (.map burnNonceSlot account) = false :=
      (congrArg (· && account.beq account) hRcpNnc).trans (Bool.false_and _)
    let hMissSrc : StorageKey.fastBeq (.map recipientBalanceSlot account) (.map sourceVaultSlot account) = false :=
      (congrArg (· && account.beq account) hRcpSrc).trans (Bool.false_and _)
    let hMissDst : StorageKey.fastBeq (.map recipientBalanceSlot account) (.map destSupplySlot account) = false :=
      (congrArg (· && account.beq account) hRcpDst).trans (Bool.false_and _)
    let hMissBrn : StorageKey.fastBeq (.map recipientBalanceSlot account) (.map burnerMintedSlot account) = false :=
      (congrArg (· && account.beq account) hRcpBrn).trans (Bool.false_and _)
    (mintMap_slot_frame _ burnNonceSlot account 1 (.map recipientBalanceSlot account) hMissNnc).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· + amount)
          ((burnMap_slot_frame _ sourceVaultSlot account amount (.map recipientBalanceSlot account) hMissSrc).trans
            ((burnMap_slot_frame _ destSupplySlot account amount (.map recipientBalanceSlot account) hMissDst).trans
              (burnMap_slot_frame s burnerMintedSlot account amount (.map recipientBalanceSlot account) hMissBrn))))

set_option maxHeartbeats 200000 in
  theorem bridgeBurnAndReleaseMap_preserves_transient (s : ContractState)
      (burnerMintedSlot destSupplySlot sourceVaultSlot recipientBalanceSlot burnNonceSlot account amount tslot : Nat) :
      getStorage (bridgeBurnAndReleaseMap s burnerMintedSlot destSupplySlot sourceVaultSlot recipientBalanceSlot burnNonceSlot account amount) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (mintMap_slot_frame _ burnNonceSlot account 1 (.transient tslot) rfl).trans <|
      (mintMap_slot_frame _ recipientBalanceSlot account amount (.transient tslot) rfl).trans <|
      (burnMap_slot_frame _ sourceVaultSlot account amount (.transient tslot) rfl).trans <|
      (burnMap_slot_frame _ destSupplySlot account amount (.transient tslot) rfl).trans
        (burnMap_slot_frame s burnerMintedSlot account amount (.transient tslot) rfl)

set_option maxHeartbeats 200000 in
  theorem guardedBridgeBurnAndReleaseMap_unlocked_after (s : ContractState)
      (lockSlot burnerMintedSlot destSupplySlot sourceVaultSlot recipientBalanceSlot burnNonceSlot account amount : Nat) :
      isTransientLocked (guardedBridgeBurnAndReleaseMap s lockSlot burnerMintedSlot destSupplySlot sourceVaultSlot recipientBalanceSlot burnNonceSlot account amount) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def bridgeLockMintThenBurnReleaseMap (s : ContractState)
      (senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot lockNonceSlot burnNonceSlot account amount : Nat) : ContractState :=
    bridgeBurnAndReleaseMap
      (bridgeLockAndMintMap s senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot lockNonceSlot account amount)
      recipientMintedSlot destSupplySlot sourceVaultSlot senderBalanceSlot burnNonceSlot account amount

  def guardedBridgeLockMintThenBurnReleaseMap (s : ContractState)
      (lockSlot senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot lockNonceSlot burnNonceSlot account amount : Nat) : ContractState :=
    releaseTransientLock
      (bridgeLockMintThenBurnReleaseMap (acquireTransientLock s lockSlot) senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot lockNonceSlot burnNonceSlot account amount)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem bridgeLockMintThenBurnReleaseMap_other_slot_frame (s : ContractState)
      (senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot lockNonceSlot burnNonceSlot otherSlot account observer amount : Nat)
      (hSnd : Nat.beq otherSlot senderBalanceSlot = false)
      (hSrc : Nat.beq otherSlot sourceVaultSlot = false)
      (hDst : Nat.beq otherSlot destSupplySlot = false)
      (hRcp : Nat.beq otherSlot recipientMintedSlot = false)
      (hLNnc : Nat.beq otherSlot lockNonceSlot = false)
      (hBNnc : Nat.beq otherSlot burnNonceSlot = false) :
      getStorage (bridgeLockMintThenBurnReleaseMap s senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot lockNonceSlot burnNonceSlot account amount) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (bridgeBurnAndReleaseMap_other_slot_frame _ recipientMintedSlot destSupplySlot sourceVaultSlot senderBalanceSlot burnNonceSlot otherSlot account observer amount hRcp hDst hSrc hSnd hBNnc).trans
      (bridgeLockAndMintMap_other_slot_frame s senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot lockNonceSlot otherSlot account observer amount hSnd hSrc hDst hRcp hLNnc)

set_option maxHeartbeats 200000 in
  theorem bridgeLockMintThenBurnReleaseMap_sender_balance_exact_restore (s : ContractState)
      (senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot lockNonceSlot burnNonceSlot account amount : Nat)
      (hSndBNnc : Nat.beq senderBalanceSlot burnNonceSlot = false)
      (hSndLNnc : Nat.beq senderBalanceSlot lockNonceSlot = false)
      (hSndRcp : Nat.beq senderBalanceSlot recipientMintedSlot = false)
      (hSndDst : Nat.beq senderBalanceSlot destSupplySlot = false)
      (hSndSrc : Nat.beq senderBalanceSlot sourceVaultSlot = false)
      (hLe : amount ≤ getStorage s (.map senderBalanceSlot account)) :
      getStorage (bridgeLockMintThenBurnReleaseMap s senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot lockNonceSlot burnNonceSlot account amount) (.map senderBalanceSlot account) =
        getStorage s (.map senderBalanceSlot account) :=
    let hMissLNnc : StorageKey.fastBeq (.map senderBalanceSlot account) (.map lockNonceSlot account) = false :=
      (congrArg (· && account.beq account) hSndLNnc).trans (Bool.false_and _)
    let hMissRcp : StorageKey.fastBeq (.map senderBalanceSlot account) (.map recipientMintedSlot account) = false :=
      (congrArg (· && account.beq account) hSndRcp).trans (Bool.false_and _)
    let hMissDst : StorageKey.fastBeq (.map senderBalanceSlot account) (.map destSupplySlot account) = false :=
      (congrArg (· && account.beq account) hSndDst).trans (Bool.false_and _)
    let hMissSrc : StorageKey.fastBeq (.map senderBalanceSlot account) (.map sourceVaultSlot account) = false :=
      (congrArg (· && account.beq account) hSndSrc).trans (Bool.false_and _)
    (bridgeBurnAndReleaseMap_recipient_balance_updated _ recipientMintedSlot destSupplySlot sourceVaultSlot senderBalanceSlot burnNonceSlot account amount hSndBNnc hSndSrc hSndDst hSndRcp).trans <|
      (congrArg (· + amount)
        ((mintMap_slot_frame _ lockNonceSlot account 1 (.map senderBalanceSlot account) hMissLNnc).trans
          ((mintMap_slot_frame _ recipientMintedSlot account amount (.map senderBalanceSlot account) hMissRcp).trans
            ((mintMap_slot_frame _ destSupplySlot account amount (.map senderBalanceSlot account) hMissDst).trans
              ((mintMap_slot_frame _ sourceVaultSlot account amount (.map senderBalanceSlot account) hMissSrc).trans
                getStorage_setStorage_same))))).trans
        (Nat.sub_add_cancel hLe)

set_option maxHeartbeats 200000 in
  theorem bridgeLockMintThenBurnReleaseMap_source_vault_exact_restore (s : ContractState)
      (senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot lockNonceSlot burnNonceSlot account amount : Nat)
      (hSrcBNnc : Nat.beq sourceVaultSlot burnNonceSlot = false)
      (hSrcLNnc : Nat.beq sourceVaultSlot lockNonceSlot = false)
      (hSrcRcp : Nat.beq sourceVaultSlot recipientMintedSlot = false)
      (hSrcDst : Nat.beq sourceVaultSlot destSupplySlot = false)
      (hSrcSnd : Nat.beq sourceVaultSlot senderBalanceSlot = false) :
      getStorage (bridgeLockMintThenBurnReleaseMap s senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot lockNonceSlot burnNonceSlot account amount) (.map sourceVaultSlot account) =
        getStorage s (.map sourceVaultSlot account) :=
    let hMissBNnc : StorageKey.fastBeq (.map sourceVaultSlot account) (.map burnNonceSlot account) = false :=
      (congrArg (· && account.beq account) hSrcBNnc).trans (Bool.false_and _)
    let hMissLNnc : StorageKey.fastBeq (.map sourceVaultSlot account) (.map lockNonceSlot account) = false :=
      (congrArg (· && account.beq account) hSrcLNnc).trans (Bool.false_and _)
    let hMissRcp : StorageKey.fastBeq (.map sourceVaultSlot account) (.map recipientMintedSlot account) = false :=
      (congrArg (· && account.beq account) hSrcRcp).trans (Bool.false_and _)
    let hMissDst : StorageKey.fastBeq (.map sourceVaultSlot account) (.map destSupplySlot account) = false :=
      (congrArg (· && account.beq account) hSrcDst).trans (Bool.false_and _)
    let hMissSnd : StorageKey.fastBeq (.map sourceVaultSlot account) (.map senderBalanceSlot account) = false :=
      (congrArg (· && account.beq account) hSrcSnd).trans (Bool.false_and _)
    (mintMap_slot_frame _ burnNonceSlot account 1 (.map sourceVaultSlot account) hMissBNnc).trans <|
      (mintMap_slot_frame _ senderBalanceSlot account amount (.map sourceVaultSlot account) hMissSnd).trans <|
      getStorage_setStorage_same.trans <|
      (congrArg (· - amount)
        ((burnMap_slot_frame _ destSupplySlot account amount (.map sourceVaultSlot account) hMissDst).trans
          ((burnMap_slot_frame _ recipientMintedSlot account amount (.map sourceVaultSlot account) hMissRcp).trans
            ((mintMap_slot_frame _ lockNonceSlot account 1 (.map sourceVaultSlot account) hMissLNnc).trans
              ((mintMap_slot_frame _ recipientMintedSlot account amount (.map sourceVaultSlot account) hMissRcp).trans
                ((mintMap_slot_frame _ destSupplySlot account amount (.map sourceVaultSlot account) hMissDst).trans
                  (getStorage_setStorage_same.trans
                    (congrArg (· + amount)
                      (burnMap_slot_frame s senderBalanceSlot account amount (.map sourceVaultSlot account) hMissSnd))))))))).trans
        (Nat.add_sub_cancel (getStorage s (.map sourceVaultSlot account)) amount)

set_option maxHeartbeats 200000 in
  theorem bridgeLockMintThenBurnReleaseMap_preserves_transient (s : ContractState)
      (senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot lockNonceSlot burnNonceSlot account amount tslot : Nat) :
      getStorage (bridgeLockMintThenBurnReleaseMap s senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot lockNonceSlot burnNonceSlot account amount) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (bridgeBurnAndReleaseMap_preserves_transient _ recipientMintedSlot destSupplySlot sourceVaultSlot senderBalanceSlot burnNonceSlot account amount tslot).trans
      (bridgeLockAndMintMap_preserves_transient s senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot lockNonceSlot account amount tslot)

set_option maxHeartbeats 200000 in
  theorem guardedBridgeLockMintThenBurnReleaseMap_unlocked_after (s : ContractState)
      (lockSlot senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot lockNonceSlot burnNonceSlot account amount : Nat) :
      isTransientLocked (guardedBridgeLockMintThenBurnReleaseMap s lockSlot senderBalanceSlot sourceVaultSlot destSupplySlot recipientMintedSlot lockNonceSlot burnNonceSlot account amount) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def bridgeRelayWithFeeMap (s : ContractState)
      (sourceVaultSlot relayerRewardSlot protocolTreasurySlot recipientBalanceSlot account grossAmount relayerFee protocolFee : Nat) : ContractState :=
    mintMap
      (mintMap
        (mintMap
          (burnMap s sourceVaultSlot account grossAmount)
          relayerRewardSlot account relayerFee)
        protocolTreasurySlot account protocolFee)
      recipientBalanceSlot account (grossAmount - relayerFee - protocolFee)

  def guardedBridgeRelayWithFeeMap (s : ContractState)
      (lockSlot sourceVaultSlot relayerRewardSlot protocolTreasurySlot recipientBalanceSlot account grossAmount relayerFee protocolFee : Nat) : ContractState :=
    releaseTransientLock
      (bridgeRelayWithFeeMap (acquireTransientLock s lockSlot) sourceVaultSlot relayerRewardSlot protocolTreasurySlot recipientBalanceSlot account grossAmount relayerFee protocolFee)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem bridgeRelayWithFeeMap_other_slot_frame (s : ContractState)
      (sourceVaultSlot relayerRewardSlot protocolTreasurySlot recipientBalanceSlot otherSlot account observer grossAmount relayerFee protocolFee : Nat)
      (hSrc : Nat.beq otherSlot sourceVaultSlot = false)
      (hRel : Nat.beq otherSlot relayerRewardSlot = false)
      (hTrs : Nat.beq otherSlot protocolTreasurySlot = false)
      (hRcp : Nat.beq otherSlot recipientBalanceSlot = false) :
      getStorage (bridgeRelayWithFeeMap s sourceVaultSlot relayerRewardSlot protocolTreasurySlot recipientBalanceSlot account grossAmount relayerFee protocolFee) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (mintMap_slot_frame _ recipientBalanceSlot account (grossAmount - relayerFee - protocolFee) (.map otherSlot observer)
      ((congrArg (· && observer.beq account) hRcp).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ protocolTreasurySlot account protocolFee (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hTrs).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ relayerRewardSlot account relayerFee (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hRel).trans (Bool.false_and _))).trans
        (burnMap_slot_frame s sourceVaultSlot account grossAmount (.map otherSlot observer)
          ((congrArg (· && observer.beq account) hSrc).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem bridgeRelayWithFeeMap_recipient_balance_updated (s : ContractState)
      (sourceVaultSlot relayerRewardSlot protocolTreasurySlot recipientBalanceSlot account grossAmount relayerFee protocolFee : Nat)
      (hRcpTrs : Nat.beq recipientBalanceSlot protocolTreasurySlot = false)
      (hRcpRel : Nat.beq recipientBalanceSlot relayerRewardSlot = false)
      (hRcpSrc : Nat.beq recipientBalanceSlot sourceVaultSlot = false) :
      getStorage (bridgeRelayWithFeeMap s sourceVaultSlot relayerRewardSlot protocolTreasurySlot recipientBalanceSlot account grossAmount relayerFee protocolFee) (.map recipientBalanceSlot account) =
        getStorage s (.map recipientBalanceSlot account) + (grossAmount - relayerFee - protocolFee) :=
    let hMissTrs : StorageKey.fastBeq (.map recipientBalanceSlot account) (.map protocolTreasurySlot account) = false :=
      (congrArg (· && account.beq account) hRcpTrs).trans (Bool.false_and _)
    let hMissRel : StorageKey.fastBeq (.map recipientBalanceSlot account) (.map relayerRewardSlot account) = false :=
      (congrArg (· && account.beq account) hRcpRel).trans (Bool.false_and _)
    let hMissSrc : StorageKey.fastBeq (.map recipientBalanceSlot account) (.map sourceVaultSlot account) = false :=
      (congrArg (· && account.beq account) hRcpSrc).trans (Bool.false_and _)
    getStorage_setStorage_same.trans
      (congrArg (· + (grossAmount - relayerFee - protocolFee))
        ((mintMap_slot_frame _ protocolTreasurySlot account protocolFee (.map recipientBalanceSlot account) hMissTrs).trans
          ((mintMap_slot_frame _ relayerRewardSlot account relayerFee (.map recipientBalanceSlot account) hMissRel).trans
            (burnMap_slot_frame s sourceVaultSlot account grossAmount (.map recipientBalanceSlot account) hMissSrc))))

set_option maxHeartbeats 200000 in
  theorem bridgeRelayWithFeeMap_protocol_treasury_updated (s : ContractState)
      (sourceVaultSlot relayerRewardSlot protocolTreasurySlot recipientBalanceSlot account grossAmount relayerFee protocolFee : Nat)
      (hTrsRcp : Nat.beq protocolTreasurySlot recipientBalanceSlot = false)
      (hTrsRel : Nat.beq protocolTreasurySlot relayerRewardSlot = false)
      (hTrsSrc : Nat.beq protocolTreasurySlot sourceVaultSlot = false) :
      getStorage (bridgeRelayWithFeeMap s sourceVaultSlot relayerRewardSlot protocolTreasurySlot recipientBalanceSlot account grossAmount relayerFee protocolFee) (.map protocolTreasurySlot account) =
        getStorage s (.map protocolTreasurySlot account) + protocolFee :=
    let hMissRcp : StorageKey.fastBeq (.map protocolTreasurySlot account) (.map recipientBalanceSlot account) = false :=
      (congrArg (· && account.beq account) hTrsRcp).trans (Bool.false_and _)
    let hMissRel : StorageKey.fastBeq (.map protocolTreasurySlot account) (.map relayerRewardSlot account) = false :=
      (congrArg (· && account.beq account) hTrsRel).trans (Bool.false_and _)
    let hMissSrc : StorageKey.fastBeq (.map protocolTreasurySlot account) (.map sourceVaultSlot account) = false :=
      (congrArg (· && account.beq account) hTrsSrc).trans (Bool.false_and _)
    (mintMap_slot_frame _ recipientBalanceSlot account (grossAmount - relayerFee - protocolFee) (.map protocolTreasurySlot account) hMissRcp).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· + protocolFee)
          ((mintMap_slot_frame _ relayerRewardSlot account relayerFee (.map protocolTreasurySlot account) hMissRel).trans
            (burnMap_slot_frame s sourceVaultSlot account grossAmount (.map protocolTreasurySlot account) hMissSrc)))

set_option maxHeartbeats 200000 in
  theorem bridgeRelayWithFeeMap_preserves_transient (s : ContractState)
      (sourceVaultSlot relayerRewardSlot protocolTreasurySlot recipientBalanceSlot account grossAmount relayerFee protocolFee tslot : Nat) :
      getStorage (bridgeRelayWithFeeMap s sourceVaultSlot relayerRewardSlot protocolTreasurySlot recipientBalanceSlot account grossAmount relayerFee protocolFee) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (mintMap_slot_frame _ recipientBalanceSlot account (grossAmount - relayerFee - protocolFee) (.transient tslot) rfl).trans <|
      (mintMap_slot_frame _ protocolTreasurySlot account protocolFee (.transient tslot) rfl).trans <|
      (mintMap_slot_frame _ relayerRewardSlot account relayerFee (.transient tslot) rfl).trans
        (burnMap_slot_frame s sourceVaultSlot account grossAmount (.transient tslot) rfl)

set_option maxHeartbeats 200000 in
  theorem guardedBridgeRelayWithFeeMap_unlocked_after (s : ContractState)
      (lockSlot sourceVaultSlot relayerRewardSlot protocolTreasurySlot recipientBalanceSlot account grossAmount relayerFee protocolFee : Nat) :
      isTransientLocked (guardedBridgeRelayWithFeeMap s lockSlot sourceVaultSlot relayerRewardSlot protocolTreasurySlot recipientBalanceSlot account grossAmount relayerFee protocolFee) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def bridgeChallengeFraudProofMap (s : ContractState)
      (batchStatusSlot proverBondSlot challengerRewardSlot insuranceFundSlot account slashAmount challengerShare : Nat) : ContractState :=
    mintMap
      (mintMap
        (burnMap
          (setStorage s (.map batchStatusSlot account) 3)
          proverBondSlot account slashAmount)
        challengerRewardSlot account challengerShare)
      insuranceFundSlot account (slashAmount - challengerShare)

  def guardedBridgeChallengeFraudProofMap (s : ContractState)
      (lockSlot batchStatusSlot proverBondSlot challengerRewardSlot insuranceFundSlot account slashAmount challengerShare : Nat) : ContractState :=
    releaseTransientLock
      (bridgeChallengeFraudProofMap (acquireTransientLock s lockSlot) batchStatusSlot proverBondSlot challengerRewardSlot insuranceFundSlot account slashAmount challengerShare)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem bridgeChallengeFraudProofMap_other_slot_frame (s : ContractState)
      (batchStatusSlot proverBondSlot challengerRewardSlot insuranceFundSlot otherSlot account observer slashAmount challengerShare : Nat)
      (hSt : Nat.beq otherSlot batchStatusSlot = false)
      (hBnd : Nat.beq otherSlot proverBondSlot = false)
      (hChl : Nat.beq otherSlot challengerRewardSlot = false)
      (hIns : Nat.beq otherSlot insuranceFundSlot = false) :
      getStorage (bridgeChallengeFraudProofMap s batchStatusSlot proverBondSlot challengerRewardSlot insuranceFundSlot account slashAmount challengerShare) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (mintMap_slot_frame _ insuranceFundSlot account (slashAmount - challengerShare) (.map otherSlot observer)
      ((congrArg (· && observer.beq account) hIns).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ challengerRewardSlot account challengerShare (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hChl).trans (Bool.false_and _))).trans <|
      (burnMap_slot_frame _ proverBondSlot account slashAmount (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hBnd).trans (Bool.false_and _))).trans
        (getStorage_setStorage_miss s (.map batchStatusSlot account) (.map otherSlot observer) 3
          ((congrArg (· && observer.beq account) hSt).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem bridgeChallengeFraudProofMap_insurance_fund_updated (s : ContractState)
      (batchStatusSlot proverBondSlot challengerRewardSlot insuranceFundSlot account slashAmount challengerShare : Nat)
      (hInsChl : Nat.beq insuranceFundSlot challengerRewardSlot = false)
      (hInsBnd : Nat.beq insuranceFundSlot proverBondSlot = false)
      (hInsSt : Nat.beq insuranceFundSlot batchStatusSlot = false) :
      getStorage (bridgeChallengeFraudProofMap s batchStatusSlot proverBondSlot challengerRewardSlot insuranceFundSlot account slashAmount challengerShare) (.map insuranceFundSlot account) =
        getStorage s (.map insuranceFundSlot account) + (slashAmount - challengerShare) :=
    let hMissChl : StorageKey.fastBeq (.map insuranceFundSlot account) (.map challengerRewardSlot account) = false :=
      (congrArg (· && account.beq account) hInsChl).trans (Bool.false_and _)
    let hMissBnd : StorageKey.fastBeq (.map insuranceFundSlot account) (.map proverBondSlot account) = false :=
      (congrArg (· && account.beq account) hInsBnd).trans (Bool.false_and _)
    let hMissSt : StorageKey.fastBeq (.map insuranceFundSlot account) (.map batchStatusSlot account) = false :=
      (congrArg (· && account.beq account) hInsSt).trans (Bool.false_and _)
    getStorage_setStorage_same.trans
      (congrArg (· + (slashAmount - challengerShare))
        ((mintMap_slot_frame _ challengerRewardSlot account challengerShare (.map insuranceFundSlot account) hMissChl).trans
          ((burnMap_slot_frame _ proverBondSlot account slashAmount (.map insuranceFundSlot account) hMissBnd).trans
            (getStorage_setStorage_miss s (.map batchStatusSlot account) (.map insuranceFundSlot account) 3 hMissSt))))

set_option maxHeartbeats 200000 in
  theorem bridgeChallengeFraudProofMap_challenger_reward_updated (s : ContractState)
      (batchStatusSlot proverBondSlot challengerRewardSlot insuranceFundSlot account slashAmount challengerShare : Nat)
      (hChlIns : Nat.beq challengerRewardSlot insuranceFundSlot = false)
      (hChlBnd : Nat.beq challengerRewardSlot proverBondSlot = false)
      (hChlSt : Nat.beq challengerRewardSlot batchStatusSlot = false) :
      getStorage (bridgeChallengeFraudProofMap s batchStatusSlot proverBondSlot challengerRewardSlot insuranceFundSlot account slashAmount challengerShare) (.map challengerRewardSlot account) =
        getStorage s (.map challengerRewardSlot account) + challengerShare :=
    let hMissIns : StorageKey.fastBeq (.map challengerRewardSlot account) (.map insuranceFundSlot account) = false :=
      (congrArg (· && account.beq account) hChlIns).trans (Bool.false_and _)
    let hMissBnd : StorageKey.fastBeq (.map challengerRewardSlot account) (.map proverBondSlot account) = false :=
      (congrArg (· && account.beq account) hChlBnd).trans (Bool.false_and _)
    let hMissSt : StorageKey.fastBeq (.map challengerRewardSlot account) (.map batchStatusSlot account) = false :=
      (congrArg (· && account.beq account) hChlSt).trans (Bool.false_and _)
    (mintMap_slot_frame _ insuranceFundSlot account (slashAmount - challengerShare) (.map challengerRewardSlot account) hMissIns).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· + challengerShare)
          ((burnMap_slot_frame _ proverBondSlot account slashAmount (.map challengerRewardSlot account) hMissBnd).trans
            (getStorage_setStorage_miss s (.map batchStatusSlot account) (.map challengerRewardSlot account) 3 hMissSt)))

set_option maxHeartbeats 200000 in
  theorem bridgeChallengeFraudProofMap_preserves_transient (s : ContractState)
      (batchStatusSlot proverBondSlot challengerRewardSlot insuranceFundSlot account slashAmount challengerShare tslot : Nat) :
      getStorage (bridgeChallengeFraudProofMap s batchStatusSlot proverBondSlot challengerRewardSlot insuranceFundSlot account slashAmount challengerShare) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (mintMap_slot_frame _ insuranceFundSlot account (slashAmount - challengerShare) (.transient tslot) rfl).trans <|
      (mintMap_slot_frame _ challengerRewardSlot account challengerShare (.transient tslot) rfl).trans <|
      (burnMap_slot_frame _ proverBondSlot account slashAmount (.transient tslot) rfl).trans
        (getStorage_setStorage_miss s (.map batchStatusSlot account) (.transient tslot) 3 rfl)

set_option maxHeartbeats 200000 in
  theorem guardedBridgeChallengeFraudProofMap_unlocked_after (s : ContractState)
      (lockSlot batchStatusSlot proverBondSlot challengerRewardSlot insuranceFundSlot account slashAmount challengerShare : Nat) :
      isTransientLocked (guardedBridgeChallengeFraudProofMap s lockSlot batchStatusSlot proverBondSlot challengerRewardSlot insuranceFundSlot account slashAmount challengerShare) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def bridgeFinalizeBatchMap (s : ContractState)
      (batchStatusSlot proverBondSlot proverBalanceSlot finalizedRootSlot account stateRoot unbondAmount : Nat) : ContractState :=
    setStorage
      (mintMap
        (burnMap
          (setStorage s (.map batchStatusSlot account) 4)
          proverBondSlot account unbondAmount)
        proverBalanceSlot account unbondAmount)
      (.map finalizedRootSlot account) stateRoot

  def guardedBridgeFinalizeBatchMap (s : ContractState)
      (lockSlot batchStatusSlot proverBondSlot proverBalanceSlot finalizedRootSlot account stateRoot unbondAmount : Nat) : ContractState :=
    releaseTransientLock
      (bridgeFinalizeBatchMap (acquireTransientLock s lockSlot) batchStatusSlot proverBondSlot proverBalanceSlot finalizedRootSlot account stateRoot unbondAmount)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem bridgeFinalizeBatchMap_other_slot_frame (s : ContractState)
      (batchStatusSlot proverBondSlot proverBalanceSlot finalizedRootSlot otherSlot account observer stateRoot unbondAmount : Nat)
      (hSt : Nat.beq otherSlot batchStatusSlot = false)
      (hBnd : Nat.beq otherSlot proverBondSlot = false)
      (hBal : Nat.beq otherSlot proverBalanceSlot = false)
      (hRoot : Nat.beq otherSlot finalizedRootSlot = false) :
      getStorage (bridgeFinalizeBatchMap s batchStatusSlot proverBondSlot proverBalanceSlot finalizedRootSlot account stateRoot unbondAmount) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (getStorage_setStorage_miss _ (.map finalizedRootSlot account) (.map otherSlot observer) stateRoot
      ((congrArg (· && observer.beq account) hRoot).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ proverBalanceSlot account unbondAmount (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hBal).trans (Bool.false_and _))).trans <|
      (burnMap_slot_frame _ proverBondSlot account unbondAmount (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hBnd).trans (Bool.false_and _))).trans
        (getStorage_setStorage_miss s (.map batchStatusSlot account) (.map otherSlot observer) 4
          ((congrArg (· && observer.beq account) hSt).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem bridgeFinalizeBatchMap_finalized_root_recorded (s : ContractState)
      (batchStatusSlot proverBondSlot proverBalanceSlot finalizedRootSlot account stateRoot unbondAmount : Nat) :
      getStorage (bridgeFinalizeBatchMap s batchStatusSlot proverBondSlot proverBalanceSlot finalizedRootSlot account stateRoot unbondAmount) (.map finalizedRootSlot account) = stateRoot :=
    getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem bridgeFinalizeBatchMap_prover_balance_updated (s : ContractState)
      (batchStatusSlot proverBondSlot proverBalanceSlot finalizedRootSlot account stateRoot unbondAmount : Nat)
      (hBalRoot : Nat.beq proverBalanceSlot finalizedRootSlot = false)
      (hBalBnd : Nat.beq proverBalanceSlot proverBondSlot = false)
      (hBalSt : Nat.beq proverBalanceSlot batchStatusSlot = false) :
      getStorage (bridgeFinalizeBatchMap s batchStatusSlot proverBondSlot proverBalanceSlot finalizedRootSlot account stateRoot unbondAmount) (.map proverBalanceSlot account) =
        getStorage s (.map proverBalanceSlot account) + unbondAmount :=
    let hMissRoot : StorageKey.fastBeq (.map proverBalanceSlot account) (.map finalizedRootSlot account) = false :=
      (congrArg (· && account.beq account) hBalRoot).trans (Bool.false_and _)
    let hMissBnd : StorageKey.fastBeq (.map proverBalanceSlot account) (.map proverBondSlot account) = false :=
      (congrArg (· && account.beq account) hBalBnd).trans (Bool.false_and _)
    let hMissSt : StorageKey.fastBeq (.map proverBalanceSlot account) (.map batchStatusSlot account) = false :=
      (congrArg (· && account.beq account) hBalSt).trans (Bool.false_and _)
    (getStorage_setStorage_miss _ (.map finalizedRootSlot account) (.map proverBalanceSlot account) stateRoot hMissRoot).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· + unbondAmount)
          ((burnMap_slot_frame _ proverBondSlot account unbondAmount (.map proverBalanceSlot account) hMissBnd).trans
            (getStorage_setStorage_miss s (.map batchStatusSlot account) (.map proverBalanceSlot account) 4 hMissSt)))

set_option maxHeartbeats 200000 in
  theorem bridgeFinalizeBatchMap_preserves_transient (s : ContractState)
      (batchStatusSlot proverBondSlot proverBalanceSlot finalizedRootSlot account stateRoot unbondAmount tslot : Nat) :
      getStorage (bridgeFinalizeBatchMap s batchStatusSlot proverBondSlot proverBalanceSlot finalizedRootSlot account stateRoot unbondAmount) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (getStorage_setStorage_miss _ (.map finalizedRootSlot account) (.transient tslot) stateRoot rfl).trans <|
      (mintMap_slot_frame _ proverBalanceSlot account unbondAmount (.transient tslot) rfl).trans <|
      (burnMap_slot_frame _ proverBondSlot account unbondAmount (.transient tslot) rfl).trans
        (getStorage_setStorage_miss s (.map batchStatusSlot account) (.transient tslot) 4 rfl)

set_option maxHeartbeats 200000 in
  theorem guardedBridgeFinalizeBatchMap_unlocked_after (s : ContractState)
      (lockSlot batchStatusSlot proverBondSlot proverBalanceSlot finalizedRootSlot account stateRoot unbondAmount : Nat) :
      isTransientLocked (guardedBridgeFinalizeBatchMap s lockSlot batchStatusSlot proverBondSlot proverBalanceSlot finalizedRootSlot account stateRoot unbondAmount) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def perpOpenPositionMap (s : ContractState)
      (traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot traderEntryPriceSlot openInterestSlot account marginAmount notionalSize entryPrice : Nat) : ContractState :=
    mintMap
      (setStorage
        (mintMap
          (mintMap
            (burnMap s traderCollateralSlot account marginAmount)
            vaultMarginPoolSlot account marginAmount)
          traderPositionSizeSlot account notionalSize)
        (.map traderEntryPriceSlot account) entryPrice)
      openInterestSlot account notionalSize

  def guardedPerpOpenPositionMap (s : ContractState)
      (lockSlot traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot traderEntryPriceSlot openInterestSlot account marginAmount notionalSize entryPrice : Nat) : ContractState :=
    releaseTransientLock
      (perpOpenPositionMap (acquireTransientLock s lockSlot) traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot traderEntryPriceSlot openInterestSlot account marginAmount notionalSize entryPrice)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem perpOpenPositionMap_other_slot_frame (s : ContractState)
      (traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot traderEntryPriceSlot openInterestSlot otherSlot account observer marginAmount notionalSize entryPrice : Nat)
      (hCol : Nat.beq otherSlot traderCollateralSlot = false)
      (hMrg : Nat.beq otherSlot vaultMarginPoolSlot = false)
      (hPos : Nat.beq otherSlot traderPositionSizeSlot = false)
      (hPrc : Nat.beq otherSlot traderEntryPriceSlot = false)
      (hOi : Nat.beq otherSlot openInterestSlot = false) :
      getStorage (perpOpenPositionMap s traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot traderEntryPriceSlot openInterestSlot account marginAmount notionalSize entryPrice) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (mintMap_slot_frame _ openInterestSlot account notionalSize (.map otherSlot observer)
      ((congrArg (· && observer.beq account) hOi).trans (Bool.false_and _))).trans <|
      (getStorage_setStorage_miss _ (.map traderEntryPriceSlot account) (.map otherSlot observer) entryPrice
        ((congrArg (· && observer.beq account) hPrc).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ traderPositionSizeSlot account notionalSize (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hPos).trans (Bool.false_and _))).trans <|
      (mintMap_slot_frame _ vaultMarginPoolSlot account marginAmount (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hMrg).trans (Bool.false_and _))).trans
        (burnMap_slot_frame s traderCollateralSlot account marginAmount (.map otherSlot observer)
          ((congrArg (· && observer.beq account) hCol).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem perpOpenPositionMap_open_interest_increased (s : ContractState)
      (traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot traderEntryPriceSlot openInterestSlot account marginAmount notionalSize entryPrice : Nat)
      (hOiPrc : Nat.beq openInterestSlot traderEntryPriceSlot = false)
      (hOiPos : Nat.beq openInterestSlot traderPositionSizeSlot = false)
      (hOiMrg : Nat.beq openInterestSlot vaultMarginPoolSlot = false)
      (hOiCol : Nat.beq openInterestSlot traderCollateralSlot = false) :
      getStorage (perpOpenPositionMap s traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot traderEntryPriceSlot openInterestSlot account marginAmount notionalSize entryPrice) (.map openInterestSlot account) =
        getStorage s (.map openInterestSlot account) + notionalSize :=
    let hMissPrc : StorageKey.fastBeq (.map openInterestSlot account) (.map traderEntryPriceSlot account) = false :=
      (congrArg (· && account.beq account) hOiPrc).trans (Bool.false_and _)
    let hMissPos : StorageKey.fastBeq (.map openInterestSlot account) (.map traderPositionSizeSlot account) = false :=
      (congrArg (· && account.beq account) hOiPos).trans (Bool.false_and _)
    let hMissMrg : StorageKey.fastBeq (.map openInterestSlot account) (.map vaultMarginPoolSlot account) = false :=
      (congrArg (· && account.beq account) hOiMrg).trans (Bool.false_and _)
    let hMissCol : StorageKey.fastBeq (.map openInterestSlot account) (.map traderCollateralSlot account) = false :=
      (congrArg (· && account.beq account) hOiCol).trans (Bool.false_and _)
    getStorage_setStorage_same.trans
      (congrArg (· + notionalSize)
        ((getStorage_setStorage_miss _ (.map traderEntryPriceSlot account) (.map openInterestSlot account) entryPrice hMissPrc).trans
          ((mintMap_slot_frame _ traderPositionSizeSlot account notionalSize (.map openInterestSlot account) hMissPos).trans
            ((mintMap_slot_frame _ vaultMarginPoolSlot account marginAmount (.map openInterestSlot account) hMissMrg).trans
              (burnMap_slot_frame s traderCollateralSlot account marginAmount (.map openInterestSlot account) hMissCol)))))

set_option maxHeartbeats 200000 in
  theorem perpOpenPositionMap_entry_price_recorded (s : ContractState)
      (traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot traderEntryPriceSlot openInterestSlot account marginAmount notionalSize entryPrice : Nat)
      (hPrcOi : Nat.beq traderEntryPriceSlot openInterestSlot = false) :
      getStorage (perpOpenPositionMap s traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot traderEntryPriceSlot openInterestSlot account marginAmount notionalSize entryPrice) (.map traderEntryPriceSlot account) =
        entryPrice :=
    let hMissOi : StorageKey.fastBeq (.map traderEntryPriceSlot account) (.map openInterestSlot account) = false :=
      (congrArg (· && account.beq account) hPrcOi).trans (Bool.false_and _)
    (mintMap_slot_frame _ openInterestSlot account notionalSize (.map traderEntryPriceSlot account) hMissOi).trans
      getStorage_setStorage_same

set_option maxHeartbeats 200000 in
  theorem perpOpenPositionMap_preserves_transient (s : ContractState)
      (traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot traderEntryPriceSlot openInterestSlot account marginAmount notionalSize entryPrice tslot : Nat) :
      getStorage (perpOpenPositionMap s traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot traderEntryPriceSlot openInterestSlot account marginAmount notionalSize entryPrice) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (mintMap_slot_frame _ openInterestSlot account notionalSize (.transient tslot) rfl).trans <|
      (getStorage_setStorage_miss _ (.map traderEntryPriceSlot account) (.transient tslot) entryPrice rfl).trans <|
      (mintMap_slot_frame _ traderPositionSizeSlot account notionalSize (.transient tslot) rfl).trans <|
      (mintMap_slot_frame _ vaultMarginPoolSlot account marginAmount (.transient tslot) rfl).trans
        (burnMap_slot_frame s traderCollateralSlot account marginAmount (.transient tslot) rfl)

set_option maxHeartbeats 200000 in
  theorem guardedPerpOpenPositionMap_unlocked_after (s : ContractState)
      (lockSlot traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot traderEntryPriceSlot openInterestSlot account marginAmount notionalSize entryPrice : Nat) :
      isTransientLocked (guardedPerpOpenPositionMap s lockSlot traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot traderEntryPriceSlot openInterestSlot account marginAmount notionalSize entryPrice) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

  def perpClosePositionMap (s : ContractState)
      (traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot openInterestSlot account closeNotional marginReturn pnlPayout : Nat) : ContractState :=
    mintMap
      (burnMap
        (burnMap
          (burnMap s traderPositionSizeSlot account closeNotional)
          openInterestSlot account closeNotional)
        vaultMarginPoolSlot account (marginReturn + pnlPayout))
      traderCollateralSlot account (marginReturn + pnlPayout)

  def guardedPerpClosePositionMap (s : ContractState)
      (lockSlot traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot openInterestSlot account closeNotional marginReturn pnlPayout : Nat) : ContractState :=
    releaseTransientLock
      (perpClosePositionMap (acquireTransientLock s lockSlot) traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot openInterestSlot account closeNotional marginReturn pnlPayout)
      lockSlot

set_option maxHeartbeats 200000 in
  theorem perpClosePositionMap_other_slot_frame (s : ContractState)
      (traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot openInterestSlot otherSlot account observer closeNotional marginReturn pnlPayout : Nat)
      (hPos : Nat.beq otherSlot traderPositionSizeSlot = false)
      (hOi : Nat.beq otherSlot openInterestSlot = false)
      (hMrg : Nat.beq otherSlot vaultMarginPoolSlot = false)
      (hCol : Nat.beq otherSlot traderCollateralSlot = false) :
      getStorage (perpClosePositionMap s traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot openInterestSlot account closeNotional marginReturn pnlPayout) (.map otherSlot observer) =
        getStorage s (.map otherSlot observer) :=
    (mintMap_slot_frame _ traderCollateralSlot account (marginReturn + pnlPayout) (.map otherSlot observer)
      ((congrArg (· && observer.beq account) hCol).trans (Bool.false_and _))).trans <|
      (burnMap_slot_frame _ vaultMarginPoolSlot account (marginReturn + pnlPayout) (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hMrg).trans (Bool.false_and _))).trans <|
      (burnMap_slot_frame _ openInterestSlot account closeNotional (.map otherSlot observer)
        ((congrArg (· && observer.beq account) hOi).trans (Bool.false_and _))).trans
        (burnMap_slot_frame s traderPositionSizeSlot account closeNotional (.map otherSlot observer)
          ((congrArg (· && observer.beq account) hPos).trans (Bool.false_and _)))

set_option maxHeartbeats 200000 in
  theorem perpClosePositionMap_trader_collateral_updated (s : ContractState)
      (traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot openInterestSlot account closeNotional marginReturn pnlPayout : Nat)
      (hColMrg : Nat.beq traderCollateralSlot vaultMarginPoolSlot = false)
      (hColOi : Nat.beq traderCollateralSlot openInterestSlot = false)
      (hColPos : Nat.beq traderCollateralSlot traderPositionSizeSlot = false) :
      getStorage (perpClosePositionMap s traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot openInterestSlot account closeNotional marginReturn pnlPayout) (.map traderCollateralSlot account) =
        getStorage s (.map traderCollateralSlot account) + (marginReturn + pnlPayout) :=
    let hMissMrg : StorageKey.fastBeq (.map traderCollateralSlot account) (.map vaultMarginPoolSlot account) = false :=
      (congrArg (· && account.beq account) hColMrg).trans (Bool.false_and _)
    let hMissOi : StorageKey.fastBeq (.map traderCollateralSlot account) (.map openInterestSlot account) = false :=
      (congrArg (· && account.beq account) hColOi).trans (Bool.false_and _)
    let hMissPos : StorageKey.fastBeq (.map traderCollateralSlot account) (.map traderPositionSizeSlot account) = false :=
      (congrArg (· && account.beq account) hColPos).trans (Bool.false_and _)
    getStorage_setStorage_same.trans
      (congrArg (· + (marginReturn + pnlPayout))
        ((burnMap_slot_frame _ vaultMarginPoolSlot account (marginReturn + pnlPayout) (.map traderCollateralSlot account) hMissMrg).trans
          ((burnMap_slot_frame _ openInterestSlot account closeNotional (.map traderCollateralSlot account) hMissOi).trans
            (burnMap_slot_frame s traderPositionSizeSlot account closeNotional (.map traderCollateralSlot account) hMissPos))))

set_option maxHeartbeats 200000 in
  theorem perpClosePositionMap_vault_margin_pool_reduced (s : ContractState)
      (traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot openInterestSlot account closeNotional marginReturn pnlPayout : Nat)
      (hMrgCol : Nat.beq vaultMarginPoolSlot traderCollateralSlot = false)
      (hMrgOi : Nat.beq vaultMarginPoolSlot openInterestSlot = false)
      (hMrgPos : Nat.beq vaultMarginPoolSlot traderPositionSizeSlot = false) :
      getStorage (perpClosePositionMap s traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot openInterestSlot account closeNotional marginReturn pnlPayout) (.map vaultMarginPoolSlot account) =
        getStorage s (.map vaultMarginPoolSlot account) - (marginReturn + pnlPayout) :=
    let hMissCol : StorageKey.fastBeq (.map vaultMarginPoolSlot account) (.map traderCollateralSlot account) = false :=
      (congrArg (· && account.beq account) hMrgCol).trans (Bool.false_and _)
    let hMissOi : StorageKey.fastBeq (.map vaultMarginPoolSlot account) (.map openInterestSlot account) = false :=
      (congrArg (· && account.beq account) hMrgOi).trans (Bool.false_and _)
    let hMissPos : StorageKey.fastBeq (.map vaultMarginPoolSlot account) (.map traderPositionSizeSlot account) = false :=
      (congrArg (· && account.beq account) hMrgPos).trans (Bool.false_and _)
    (mintMap_slot_frame _ traderCollateralSlot account (marginReturn + pnlPayout) (.map vaultMarginPoolSlot account) hMissCol).trans <|
      getStorage_setStorage_same.trans
        (congrArg (· - (marginReturn + pnlPayout))
          ((burnMap_slot_frame _ openInterestSlot account closeNotional (.map vaultMarginPoolSlot account) hMissOi).trans
            (burnMap_slot_frame s traderPositionSizeSlot account closeNotional (.map vaultMarginPoolSlot account) hMissPos)))

set_option maxHeartbeats 200000 in
  theorem perpClosePositionMap_preserves_transient (s : ContractState)
      (traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot openInterestSlot account closeNotional marginReturn pnlPayout tslot : Nat) :
      getStorage (perpClosePositionMap s traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot openInterestSlot account closeNotional marginReturn pnlPayout) (.transient tslot) =
        getStorage s (.transient tslot) :=
    (mintMap_slot_frame _ traderCollateralSlot account (marginReturn + pnlPayout) (.transient tslot) rfl).trans <|
      (burnMap_slot_frame _ vaultMarginPoolSlot account (marginReturn + pnlPayout) (.transient tslot) rfl).trans <|
      (burnMap_slot_frame _ openInterestSlot account closeNotional (.transient tslot) rfl).trans
        (burnMap_slot_frame s traderPositionSizeSlot account closeNotional (.transient tslot) rfl)

set_option maxHeartbeats 200000 in
  theorem guardedPerpClosePositionMap_unlocked_after (s : ContractState)
      (lockSlot traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot openInterestSlot account closeNotional marginReturn pnlPayout : Nat) :
      isTransientLocked (guardedPerpClosePositionMap s lockSlot traderCollateralSlot vaultMarginPoolSlot traderPositionSizeSlot openInterestSlot account closeNotional marginReturn pnlPayout) lockSlot = false :=
    congrArg (Nat.beq · 1) getStorage_setStorage_same

end TurboLean.Reflection
