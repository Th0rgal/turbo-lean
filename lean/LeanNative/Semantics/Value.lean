import LeanNative.IR.Types
import LeanNative.IR.AST

namespace LeanNative.Semantics

open LeanNative.IR

/-- Formal runtime value domain for LNIR operational & denotational evaluation
    (including 256-bit `UInt256` EVM words and `storageMapId` persistent storage maps). -/
inductive Val where
  | u64          : UInt64 → Val
  | u256         : UInt256 → Val
  | bool         : Bool → Val
  | tuple        : List Val → Val
  | objPtr       : Nat → Val
  | sarrayId     : Nat → Val
  | rawPtrId     : Nat → Val
  | storageMapId : Nat → Val
  | unit         : Val
  deriving Repr, Inhabited

namespace Val

mutual
  def beq : Val → Val → Bool
    | .u64 a, .u64 b => a == b
    | .u256 a, .u256 b => a == b
    | .bool a, .bool b => a == b
    | .tuple as, .tuple bs => beqList as bs
    | .objPtr a, .objPtr b => a == b
    | .sarrayId a, .sarrayId b => a == b
    | .rawPtrId a, .rawPtrId b => a == b
    | .storageMapId a, .storageMapId b => a == b
    | .unit, .unit => true
    | _, _ => false

  def beqList : List Val → List Val → Bool
    | [], [] => true
    | a :: as, b :: bs => beq a b && beqList as bs
    | _, _ => false
end

instance : BEq Val := ⟨Val.beq⟩

mutual
  def decEq : (a b : Val) → Decidable (a = b)
    | .u64 a, .u64 b =>
      if h : a = b then isTrue (congrArg Val.u64 h) else isFalse (fun h' => Val.noConfusion h' h)
    | .u256 a, .u256 b =>
      if h : a = b then isTrue (congrArg Val.u256 h) else isFalse (fun h' => Val.noConfusion h' h)
    | .bool a, .bool b =>
      if h : a = b then isTrue (congrArg Val.bool h) else isFalse (fun h' => Val.noConfusion h' h)
    | .tuple as, .tuple bs =>
      match decEqList as bs with
      | isTrue h => isTrue (congrArg Val.tuple h)
      | isFalse h => isFalse (fun h' => Val.noConfusion h' h)
    | .objPtr a, .objPtr b =>
      if h : a = b then isTrue (congrArg Val.objPtr h) else isFalse (fun h' => Val.noConfusion h' h)
    | .sarrayId a, .sarrayId b =>
      if h : a = b then isTrue (congrArg Val.sarrayId h) else isFalse (fun h' => Val.noConfusion h' h)
    | .rawPtrId a, .rawPtrId b =>
      if h : a = b then isTrue (congrArg Val.rawPtrId h) else isFalse (fun h' => Val.noConfusion h' h)
    | .storageMapId a, .storageMapId b =>
      if h : a = b then isTrue (congrArg Val.storageMapId h) else isFalse (fun h' => Val.noConfusion h' h)
    | .unit, .unit => isTrue rfl
    | .u64 _, .u256 _ | .u64 _, .bool _ | .u64 _, .tuple _ | .u64 _, .objPtr _ | .u64 _, .sarrayId _ | .u64 _, .rawPtrId _ | .u64 _, .storageMapId _ | .u64 _, .unit
    | .u256 _, .u64 _ | .u256 _, .bool _ | .u256 _, .tuple _ | .u256 _, .objPtr _ | .u256 _, .sarrayId _ | .u256 _, .rawPtrId _ | .u256 _, .storageMapId _ | .u256 _, .unit
    | .bool _, .u64 _ | .bool _, .u256 _ | .bool _, .tuple _ | .bool _, .objPtr _ | .bool _, .sarrayId _ | .bool _, .rawPtrId _ | .bool _, .storageMapId _ | .bool _, .unit
    | .tuple _, .u64 _ | .tuple _, .u256 _ | .tuple _, .bool _ | .tuple _, .objPtr _ | .tuple _, .sarrayId _ | .tuple _, .rawPtrId _ | .tuple _, .storageMapId _ | .tuple _, .unit
    | .objPtr _, .u64 _ | .objPtr _, .u256 _ | .objPtr _, .bool _ | .objPtr _, .tuple _ | .objPtr _, .sarrayId _ | .objPtr _, .rawPtrId _ | .objPtr _, .storageMapId _ | .objPtr _, .unit
    | .sarrayId _, .u64 _ | .sarrayId _, .u256 _ | .sarrayId _, .bool _ | .sarrayId _, .tuple _ | .sarrayId _, .objPtr _ | .sarrayId _, .rawPtrId _ | .sarrayId _, .storageMapId _ | .sarrayId _, .unit
    | .rawPtrId _, .u64 _ | .rawPtrId _, .u256 _ | .rawPtrId _, .bool _ | .rawPtrId _, .tuple _ | .rawPtrId _, .objPtr _ | .rawPtrId _, .sarrayId _ | .rawPtrId _, .storageMapId _ | .rawPtrId _, .unit
    | .storageMapId _, .u64 _ | .storageMapId _, .u256 _ | .storageMapId _, .bool _ | .storageMapId _, .tuple _ | .storageMapId _, .objPtr _ | .storageMapId _, .sarrayId _ | .storageMapId _, .rawPtrId _ | .storageMapId _, .unit
    | .unit, .u64 _ | .unit, .u256 _ | .unit, .bool _ | .unit, .tuple _ | .unit, .objPtr _ | .unit, .sarrayId _ | .unit, .rawPtrId _ | .unit, .storageMapId _ =>
      isFalse (fun h => by cases h)

  def decEqList : (as bs : List Val) → Decidable (as = bs)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (fun h => by cases h)
    | _ :: _, [] => isFalse (fun h => by cases h)
    | a :: as, b :: bs =>
      match decEq a b, decEqList as bs with
      | isTrue h1, isTrue h2 => isTrue (by subst h1 h2; rfl)
      | isFalse h1, _ => isFalse (fun h => by cases h; exact h1 rfl)
      | _, isFalse h2 => isFalse (fun h => by cases h; exact h2 rfl)
end

instance : DecidableEq Val := Val.decEq

mutual
  theorem beq_refl : ∀ (v : Val), Val.beq v v = true
    | .u64 a => by simp [Val.beq]
    | .u256 a => by simp [Val.beq]
    | .bool a => by simp [Val.beq]
    | .tuple as => by simp [Val.beq, beqList_refl as]
    | .objPtr a => by simp [Val.beq]
    | .sarrayId a => by simp [Val.beq]
    | .rawPtrId a => by simp [Val.beq]
    | .storageMapId a => by simp [Val.beq]
    | .unit => rfl

  theorem beqList_refl : ∀ (vs : List Val), Val.beqList vs vs = true
    | [] => rfl
    | v :: vs => by simp [Val.beqList, beq_refl v, beqList_refl vs]
end

@[simp]
theorem beq_self (v : Val) : (v == v) = true :=
  beq_refl v

end Val

/-- Explicit undefined behavior / runtime trap conditions in LNIR semantics. -/
inductive UBError where
  | unboundVar         : VarId → UBError
  | typeError          : String → UBError
  | outOfBounds        : Nat → Nat → UBError
  | nonExclusiveWrite  : Nat → UBError
  | divisionByZero     : UBError
  | arithmeticOverflow : String → UBError
  | useAfterFree       : Nat → UBError
  | unsupportedCall    : String → UBError
  deriving Repr, DecidableEq, Inhabited, BEq

/-- SSA/ANF variable environment mapping `VarId` to optional runtime values. -/
abbrev VarEnv := VarId → Option Val

namespace VarEnv

/-- Empty variable environment where all variables are unbound. -/
def empty : VarEnv := fun _ => none

/-- Bind variable `x` to value `v` in environment `env`. -/
def bind (env : VarEnv) (x : VarId) (v : Val) : VarEnv :=
  fun y => if y == x then some v else env y

@[simp]
theorem bind_apply (env : VarEnv) (x y : VarId) (v : Val) :
    (env.bind x v) y = if y == x then some v else env y := rfl

@[simp]
theorem bind_self (env : VarEnv) (x : VarId) (v : Val) :
    (env.bind x v) x = some v := by
  simp [bind]

theorem bind_ne (env : VarEnv) (x y : VarId) (v : Val) (h : (y == x) = false) :
    (env.bind x v) y = env y := by
  simp [bind, h]

end VarEnv

/-- Model of a contiguous unboxed scalar array (`lean_sarray_object`) in the heap. -/
structure ArrayBuffer where
  id        : Nat
  exclusive : Bool
  data      : Array UInt64
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Model of a 256-bit EVM/Verity persistent key-value storage map (`uint256 -> uint256`).
    Uninitialized slots default to `UInt256.zero` per EVM SLOAD semantics. -/
structure StorageMapBuffer where
  id      : Nat
  entries : List (UInt256 × UInt256) := []
  deriving Repr, DecidableEq, Inhabited, BEq

namespace StorageMapBuffer

def lookupSlot (m : StorageMapBuffer) (slot : UInt256) : UInt256 :=
  match m.entries.find? (fun (k, _) => k == slot) with
  | some (_, v) => v
  | none => UInt256.zero

def writeSlot (m : StorageMapBuffer) (slot val : UInt256) : StorageMapBuffer :=
  { m with entries := (slot, val) :: m.entries.filter (fun (k, _) => k != slot) }

@[simp]
theorem lookupSlot_writeSlot_same (m : StorageMapBuffer) (slot val : UInt256) :
    (m.writeSlot slot val).lookupSlot slot = val := by
  simp [writeSlot, lookupSlot]

theorem lookupSlot_writeSlot_ne (m : StorageMapBuffer) (slot1 slot2 val : UInt256)
    (hne : (slot1 == slot2) = false) :
    (m.writeSlot slot1 val).lookupSlot slot2 = m.lookupSlot slot2 := by
  unfold writeSlot lookupSlot
  simp only [List.find?, hne]
  induction m.entries with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    by_cases hk1 : (k != slot1) = true
    · simp only [List.filter, hk1, List.find?]
      cases k == slot2
      · exact ih
      · rfl
    · have hk_eq : (k == slot1) = true := by
        cases h : k == slot1
        · simp [bne, h] at hk1
        · rfl
      have hk2 : (k == slot2) = false := by
        have heq1 : k = slot1 := of_decide_eq_true hk_eq
        subst heq1
        exact hne
      simp only [List.filter, hk1, List.find?, hk2]
      exact ih

end StorageMapBuffer

structure HeapObj where
  id           : Nat
  tag          : Nat
  objFields    : List Val
  scalarFields : List Val
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Abstract heap state tracking contiguous scalar array buffers, EVM storage maps, allocation IDs, and reference counts.
    `refCounts` stores `(isObj, id, rc)` where `isObj = false` tracks `.sarrayId` buffers with `rc ≥ 3`
    (`rc = 1` and `rc = 2` are represented canonically by `buf.exclusive = true` and `buf.exclusive = false`
    with no entry in `refCounts`), and `isObj = true` tracks `.objPtr` heap objects in a disjoint key space. -/
structure HeapState where
  buffers     : List ArrayBuffer
  nextId      : Nat
  storageMaps : List StorageMapBuffer := []
  refCounts   : List (Bool × Nat × Nat) := []
  objects     : List HeapObj := []
  deriving Repr, DecidableEq, Inhabited, BEq

namespace HeapState

def empty : HeapState :=
  { buffers := [], nextId := 0, storageMaps := [], refCounts := [], objects := [] }

def findObject (st : HeapState) (objId : Nat) : Option HeapObj :=
  st.objects.find? (fun o => o.id == objId)

def allocCtor (st : HeapState) (tag : Nat) (objFields scalarFields : List Val) : Val × HeapState :=
  let objId := st.nextId + 1
  let obj : HeapObj := { id := objId, tag := tag, objFields := objFields, scalarFields := scalarFields }
  let refs' := st.refCounts.filter (fun (isObj, id, _) => !isObj || id != objId)
  let objs' := st.objects.filter (fun o => o.id != objId)
  (.objPtr objId, { st with nextId := objId, refCounts := (true, objId, 1) :: refs', objects := obj :: objs' })

/-- Look up an `ArrayBuffer` by its buffer identifier. -/
def findBuffer (st : HeapState) (bufId : Nat) : Option ArrayBuffer :=
  st.buffers.find? (fun b => b.id == bufId)

/-- Update an existing `ArrayBuffer` in the heap state. -/
def updateBuffer (st : HeapState) (buf : ArrayBuffer) : HeapState :=
  { st with
    buffers := st.buffers.map (fun b => if b.id == buf.id then buf else b) }

/-- Look up the current reference count of a live `ArrayBuffer` (`1` when `exclusive = true`,
    `2` when `exclusive = false` and absent from `refCounts`, or `rc ≥ 3` from `refCounts`). -/
def getBufRefCount (st : HeapState) (buf : ArrayBuffer) : Nat :=
  if buf.exclusive then 1
  else
    match st.refCounts.find? (fun (isObj, id, _) => !isObj && id == buf.id) with
    | some (_, _, rc) => Nat.max 2 rc
    | none => 2

/-- Set the `exclusive` flag on buffer `bufId` inside `bs`. -/
def setBufferExclusive (bs : List ArrayBuffer) (bufId : Nat) (excl : Bool) : List ArrayBuffer :=
  bs.map (fun b => if b.id == bufId then { b with exclusive := excl } else b)

/-- Increment the reference count of `.sarrayId bufId` by `count`, failing with `useAfterFree` if `bufId` is not live. -/
def incRefBuf (st : HeapState) (bufId count : Nat) : Except UBError HeapState :=
  match st.findBuffer bufId with
  | none => .error (.useAfterFree bufId)
  | some buf =>
    if count == 0 then .ok st
    else
      let rc' := st.getBufRefCount buf + count
      let refs' := st.refCounts.filter (fun (isObj, id, _) => isObj || id != bufId)
      let newRefs := if rc' <= 2 then refs' else (false, bufId, rc') :: refs'
      .ok { st with
        buffers := setBufferExclusive st.buffers bufId false
        refCounts := newRefs }

/-- Decrement the reference count of `.sarrayId bufId` by `count`, freeing the buffer at `rc = 0`,
    restoring `exclusive = true` at `rc = 1`, or failing with `useAfterFree` on freed/underflowed buffers. -/
def decRefBuf (st : HeapState) (bufId count : Nat) : Except UBError HeapState :=
  match st.findBuffer bufId with
  | none => .error (.useAfterFree bufId)
  | some buf =>
    if count == 0 then .ok st
    else
      let rc := st.getBufRefCount buf
      if count > rc then .error (.useAfterFree bufId)
      else
        let rc' := rc - count
        let refs' := st.refCounts.filter (fun (isObj, id, _) => isObj || id != bufId)
        if rc' == 0 then
          .ok { st with
            buffers := st.buffers.filter (fun b => b.id != bufId)
            refCounts := refs' }
        else if rc' == 1 then
          .ok { st with
            buffers := setBufferExclusive st.buffers bufId true
            refCounts := refs' }
        else if rc' == 2 then
          .ok { st with
            buffers := setBufferExclusive st.buffers bufId false
            refCounts := refs' }
        else
          .ok { st with
            buffers := setBufferExclusive st.buffers bufId false
            refCounts := (false, bufId, rc') :: refs' }

/-- Look up the current reference count of `.objPtr objId` in the object key space (`0` if unknown or freed). -/
def getObjRefCount (st : HeapState) (objId : Nat) : Nat :=
  match st.refCounts.find? (fun (isObj, id, _) => isObj && id == objId) with
  | some (_, _, rc) => rc
  | none => 0

/-- Allocate/register a live `.objPtr objId` with initial reference count `1`. -/
def allocObj (st : HeapState) (objId : Nat) : HeapState :=
  let refs' := st.refCounts.filter (fun (isObj, id, _) => !isObj || id != objId)
  { st with refCounts := (true, objId, 1) :: refs' }

/-- Increment the reference count of `.objPtr objId` by `count`, failing with `useAfterFree` if unknown or freed (`rc = 0`). -/
def incRefObj (st : HeapState) (objId count : Nat) : Except UBError HeapState :=
  let rc := st.getObjRefCount objId
  if rc == 0 then .error (.useAfterFree objId)
  else if count == 0 then .ok st
  else
    let rc' := rc + count
    let refs' := st.refCounts.filter (fun (isObj, id, _) => !isObj || id != objId)
    .ok { st with refCounts := (true, objId, rc') :: refs' }

def delObjShell (st : HeapState) (objId : Nat) : Except UBError HeapState :=
  let rc := st.getObjRefCount objId
  if rc == 0 then .error (.useAfterFree objId)
  else if rc != 1 then .error (.nonExclusiveWrite objId)
  else
    let refs' := st.refCounts.filter (fun (isObj, id, _) => !isObj || id != objId)
    let objs' := st.objects.filter (fun o => o.id != objId)
    .ok { st with refCounts := refs', objects := objs' }

mutual
  def decRefObjFuel : Nat → HeapState → Nat → Nat → Except UBError HeapState
    | 0, st, objId, count =>
      let rc := st.getObjRefCount objId
      if rc == 0 || count > rc then .error (.useAfterFree objId)
      else if count == 0 then .ok st
      else
        let rc' := rc - count
        let refs' := st.refCounts.filter (fun (isObj, id, _) => !isObj || id != objId)
        let objs' := st.objects.filter (fun o => o.id != objId)
        if rc' == 0 then .ok { st with refCounts := refs', objects := objs' }
        else .ok { st with refCounts := (true, objId, rc') :: refs' }
    | fuel + 1, st, objId, count =>
      let rc := st.getObjRefCount objId
      if rc == 0 || count > rc then .error (.useAfterFree objId)
      else if count == 0 then .ok st
      else
        let rc' := rc - count
        let refs' := st.refCounts.filter (fun (isObj, id, _) => !isObj || id != objId)
        if rc' == 0 then
          let children := (st.findObject objId).map (·.objFields) |>.getD []
          let st0 := { st with refCounts := refs', objects := st.objects.filter (fun o => o.id != objId) }
          decRefValsFuel fuel st0 children
        else
          .ok { st with refCounts := (true, objId, rc') :: refs' }

  def decRefValsFuel : Nat → HeapState → List Val → Except UBError HeapState
    | _, st, [] => .ok st
    | 0, st, _ :: _ => .ok st
    | fuel + 1, st, v :: vs =>
      let step : Except UBError HeapState :=
        match v with
        | .objPtr cid => decRefObjFuel fuel st cid 1
        | .sarrayId bid => st.decRefBuf bid 1
        | .tuple tvs => decRefValsFuel fuel st tvs
        | _ => .ok st
      match step with
      | .ok st1 => decRefValsFuel fuel st1 vs
      | .error e => .error e
end

def decRefObj (st : HeapState) (objId count : Nat) : Except UBError HeapState :=
  decRefObjFuel (st.objects.length * 12 + 12) st objId count

/-- Evaluate an `incRef` instruction on variable `objVar` in `env`. -/
def evalIncRef (st : HeapState) (env : VarEnv) (objVar : VarId) (count : Nat) : Except UBError HeapState :=
  match env objVar with
  | none => .error (.unboundVar objVar)
  | some (.sarrayId bufId) => st.incRefBuf bufId count
  | some (.objPtr objId) => st.incRefObj objId count
  | some _ => .ok st

/-- Evaluate a `decRef` instruction on variable `objVar` in `env`. -/
def evalDecRef (st : HeapState) (env : VarEnv) (objVar : VarId) (count : Nat) : Except UBError HeapState :=
  match env objVar with
  | none => .error (.unboundVar objVar)
  | some (.sarrayId bufId) => st.decRefBuf bufId count
  | some (.objPtr objId) => st.decRefObj objId count
  | some _ => .ok st

@[simp]
theorem incRefObj_decRefObj_cancel (bufs : List ArrayBuffer) (nid objId count : Nat) :
    let st : HeapState := { buffers := bufs, nextId := nid, refCounts := [(true, objId, 1)] }
    (match st.incRefObj objId count with
     | .ok st1 => st1.decRefObj objId count
     | .error e => .error e) = .ok st := by
  cases count with
  | zero => simp [incRefObj, decRefObj, decRefObjFuel, getObjRefCount]
  | succ c =>
    simp [incRefObj, decRefObj, decRefObjFuel, getObjRefCount, Nat.add_sub_cancel 1 (c + 1)]

@[simp]
theorem decRefBuf_one_frees_buffer (bufId nextId : Nat) (data : Array UInt64) :
    let st : HeapState := { buffers := [{ id := bufId, exclusive := true, data := data }], nextId := nextId }
    st.decRefBuf bufId 1 = .ok { buffers := [], nextId := nextId } := by
  simp [decRefBuf, findBuffer, getBufRefCount]

@[simp]
theorem decRefBuf_none_error (st : HeapState) (bufId count : Nat)
    (h_none : st.findBuffer bufId = none) :
    st.decRefBuf bufId count = .error (.useAfterFree bufId) := by
  unfold decRefBuf; rw [h_none]

@[simp]
theorem incRefBuf_none_error (st : HeapState) (bufId count : Nat)
    (h_none : st.findBuffer bufId = none) :
    st.incRefBuf bufId count = .error (.useAfterFree bufId) := by
  unfold incRefBuf; rw [h_none]

/-- Ensure that buffer `bufId` is marked exclusive (`m_rc == 1` / copy-on-write). -/
def ensureExclusive (st : HeapState) (bufId : Nat) : Except UBError HeapState :=
  match st.findBuffer bufId with
  | none => .error (.typeError s!"unknown sarray buffer {bufId}")
  | some _ =>
    .ok { st with
      buffers := st.buffers.map (fun b => if b.id == bufId then { b with exclusive := true } else b) }

/-- Read an element at `idx` from buffer `bufId`. -/
def readElem (st : HeapState) (bufId : Nat) (idx : Nat) : Except UBError UInt64 :=
  match st.findBuffer bufId with
  | none => .error (.typeError s!"unknown sarray buffer {bufId}")
  | some buf =>
    if h : idx < buf.data.size then
      .ok buf.data[idx]
    else
      .error (.outOfBounds idx buf.data.size)

/-- Write an element in-place at `idx` in buffer `bufId`, requiring `exclusive == true`. -/
def writeElemExclusive (st : HeapState) (bufId : Nat) (idx : Nat) (val : UInt64) : Except UBError HeapState :=
  match st.findBuffer bufId with
  | none => .error (.typeError s!"unknown sarray buffer {bufId}")
  | some buf =>
    if !buf.exclusive then
      .error (.nonExclusiveWrite bufId)
    else if _h : idx < buf.data.size then
      .ok { st with
        buffers := st.buffers.map (fun b => if b.id == bufId then { b with data := b.data.set! idx val } else b) }
    else
      .error (.outOfBounds idx buf.data.size)

/-- Read a 256-bit slot from EVM storage map `mapId` (uninitialized maps/slots return `UInt256.zero`). -/
def storageLoad (st : HeapState) (mapId : Nat) (slot : UInt256) : UInt256 :=
  match st.storageMaps.find? (fun m => m.id == mapId) with
  | some m => m.lookupSlot slot
  | none => UInt256.zero

/-- Write a 256-bit value to `slot` in EVM storage map `mapId`. -/
def storageStore (st : HeapState) (mapId : Nat) (slot val : UInt256) : HeapState :=
  match st.storageMaps.find? (fun m => m.id == mapId) with
  | some m =>
    let m' : StorageMapBuffer := { id := mapId, entries := (slot, val) :: m.entries.filter (fun (k, _) => k != slot) }
    { st with storageMaps := m' :: st.storageMaps.filter (fun x => x.id != mapId) }
  | none =>
    let m' : StorageMapBuffer := { id := mapId, entries := [(slot, val)] }
    { st with storageMaps := m' :: st.storageMaps }

@[simp]
theorem storageLoad_after_storageStore_same (st : HeapState) (mapId : Nat) (slot val : UInt256) :
    (st.storageStore mapId slot val).storageLoad mapId slot = val := by
  unfold storageStore storageLoad
  cases st.storageMaps.find? (fun m => m.id == mapId) <;>
    simp [StorageMapBuffer.lookupSlot]

theorem storageLoad_after_storageStore_ne (st : HeapState) (mapId : Nat) (slot1 slot2 val : UInt256)
    (hne : (slot1 == slot2) = false) :
    (st.storageStore mapId slot1 val).storageLoad mapId slot2 = st.storageLoad mapId slot2 := by
  unfold storageStore storageLoad
  cases hfind : st.storageMaps.find? (fun m => m.id == mapId) with
  | none =>
    simp [StorageMapBuffer.lookupSlot, hne]
  | some m =>
    simp only [List.find?, beq_self_eq_true]
    exact StorageMapBuffer.lookupSlot_writeSlot_ne m slot1 slot2 val hne

end HeapState

end LeanNative.Semantics
