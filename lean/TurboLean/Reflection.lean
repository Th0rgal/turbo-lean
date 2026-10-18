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

end TurboLean.Reflection
