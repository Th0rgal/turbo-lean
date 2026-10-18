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

end TurboLean.Reflection
