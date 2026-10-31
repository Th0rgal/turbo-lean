import Lean
import LeanNative.Semantics.Eval
import LeanNative.Proofs.SymbolicTV
import LeanNative.Backend.LLVM
import LeanNative.IR.Bridge

/-!
# HeapObj step-5b regressions (D1, PR #300)

Executable regressions for the 5b fixes that are not part of the clause table owned by
`LeanNative.Tests.HeapObjContract` (#292): Bridge scalar-slot lowering (C1.2), `uset`/`sset`/`setTag`
exclusivity (C4.2), total-or-error recursive release (C3/C5), and fail-closed SymbolicTV on source fuel
and RC exhaustion (C6.3). Every check is a `#guard` (or `#guard_msgs`) on a non-constant predicate that
reaches the evaluator, heap ops, Bridge or translation validator.
-/

namespace LeanNative.Tests.HeapObj5b

open LeanNative.IR LeanNative.Semantics LeanNative.Proofs

/-! ## Fixtures -/

def childId : Nat := 1

/-- Heap holding one live child object `childId` with reference count `rc`. -/
def heapWithChild (rc : Nat) : HeapState :=
  let st0 := { HeapState.empty with nextId := childId }.allocObj childId
  match st0.incRefObj childId (rc - 1) with
  | .ok st => st
  | .error _ => st0

def idxZero : VarId := 22
def idxFive : VarId := 25

/-- `x0 ↦ child`, `x20 ↦ 42`, `x21 ↦ 43`, `x22 ↦ 0`, `x25 ↦ 5`. -/
def env0 : VarEnv :=
  [(0, .objPtr childId), (20, .u64 42), (21, .u64 43), (idxZero, .u64 0), (idxFive, .u64 5)].foldl
    (fun (e : VarEnv) (x, v) => e.bind x v) VarEnv.empty

def retZero : LNIRCode := .letBind 99 .i64 (.scalar (.constU64 0)) (.ret 99)

def run (st : HeapState) (code : LNIRCode) : Except UBError (Val × HeapState) :=
  evalCode 4096 env0 st code

def retVal? (r : Except UBError (Val × HeapState)) : Option Val :=
  match r with | .ok (v, _) => some v | .error _ => none

def isUseAfterFree : Except UBError (Val × HeapState) → Bool
  | .error (.useAfterFree _) => true
  | _ => false

def isNonExclusiveWrite : Except UBError (Val × HeapState) → Bool
  | .error (.nonExclusiveWrite _) => true
  | _ => false

/-! ## C1.2 Bridge scalar-slot lowering (`getCtorLayout`) -/

/-- Mixed-scalar ADT (`usize`, `UInt64`, `UInt8` slots) lowered by the Bridge under `--allow-rc-adt`. -/
inductive ScalarProbe where
  | mk (b : UInt8) (c : UInt64) (d : USize)
  | z (q : UInt32)

@[noinline] def scalarProbeMk (k : UInt64) : ScalarProbe := .mk k.toUInt8 (k * 3) k.toUSize

@[noinline] def scalarProbeSum : ScalarProbe → UInt64
  | .mk b c d => b.toUInt64 + c + d.toUInt64
  | .z q => q.toUInt64

/-- Bridge-lowered bodies of `scalarProbeMk` / `scalarProbeSum`. -/
def scalarProbeDecls : Lean.CoreM (List LNIRDecl) :=
  return (← LeanNative.IR.ingestModuleDecls #[``scalarProbeMk, ``scalarProbeSum] "HeapObj5b" .x86_64 true).decls

/-- Run the lowered constructor on `k`, read every scalar slot, then run the lowered matcher on the result. -/
def scalarProbeRun (ds : List LNIRDecl) (k : UInt64) : Option (List Val × Val) := do
  let mk ← ds.find? (·.name.endsWith "scalarProbeMk")
  let sum ← ds.find? (·.name.endsWith "scalarProbeSum")
  let (o, st) ← (evalCode 4096 (VarEnv.empty.bind 0 (.u64 k)) .empty mk.body).toOption
  let env := VarEnv.empty.bind 1 o
  let slots ← [0, 1, 2].mapM fun i => (evalCtorGet env st 1 i false).toOption.map Prod.fst
  let p ← sum.params.head?
  let (r, _) ← (evalCode 4096 (VarEnv.empty.bind p.id o) st sum.body).toOption
  return (slots, r)

/-- Scalar ctor fields land in `getCtorLayout` slots (`usize` first, then `off`-ordered `uintN`:
    `d ↦ 0`, `c ↦ 1`, `b ↦ 2`) and projections read them back from the same slots. -/
def scalarLoweringFollowsLayout (ds : List LNIRDecl) : Bool :=
  [0, 5, 0x1_0107].all fun k =>
    scalarProbeRun ds k == some ([.u64 k, .u64 (k * 3), .u64 (k &&& 0xFF)], .u64 ((k &&& 0xFF) + k * 3 + k))

-- REGRESSION(layout_bridge_scalar_slot_lowering)
/-- info: true -/
#guard_msgs in
#eval show Lean.CoreM Bool from return scalarLoweringFollowsLayout (← scalarProbeDecls)

/-- Without `allowRcAdt` the Bridge does not lower the RC-ADT constructor (fail-closed, C4). -/
def scalarProbeRejectedByDefault : Lean.CoreM Bool := do
  try
    let m ← LeanNative.IR.ingestModuleDecls #[``scalarProbeMk] "HeapObj5b" .x86_64 false
    return m.findRcAdtDecl?.isSome || m.decls.all (·.assurance == .unsupported)
  catch _ => return true

-- REGRESSION(rc_adt_gate_default_off)
/-- info: true -/
#guard_msgs in
#eval scalarProbeRejectedByDefault

/-! ## C3 / C5 total-or-error release -/

/-- `x1 := allocCtor 0 [x0 × k] []; decRef x1 1; ret 0`. -/
def ownEdges (k : Nat) : LNIRCode :=
  .letBind 1 .objPtr (.allocCtor 0 (List.replicate k 0) []) (.decRef 1 1 retZero)

/-- P-cert C3: the 100-owning-edge parent frees the child (or is `.error`), never `ok` with a live child. -/
def ownEdgesContract (k : Nat) : Bool :=
  match run (heapWithChild k) (ownEdges k) with
  | .ok (_, st) => st.getObjRefCount childId == 0
  | .error _ => true

-- REGRESSION(c3_100_owning_edges)
#guard ownEdgesContract 100
#guard (List.range 8).all fun k => ownEdgesContract (k + 1)

def c3Heap : HeapState :=
  ((heapWithChild 100).allocHeapCtor 0 (List.replicate 100 (.objPtr childId)) []).2
def chainHeap : HeapState :=
  (List.range 3).foldl (fun st _ => (st.allocHeapCtor 0 [.objPtr st.nextId] []).2) (heapWithChild 1)

/-- `decRefObjFuel`: `B` units (103 for C3, 8 for the 4-chain) release completely; every smaller fuel is
    exactly `.fuelExhausted`, never a partial `.ok`. -/
def decRefFuelMatchesBound : Bool :=
  [(c3Heap, c3Heap.nextId, 103), (chainHeap, chainHeap.nextId, 8)].all fun (st, root, b) =>
    (match st.decRefObjFuel b root 1 with
     | .ok st' => st'.getObjRefCount childId == 0 && st'.heapObjs.isEmpty | .error _ => false) &&
    (List.range b).all fun f => match st.decRefObjFuel f root 1 with | .error .fuelExhausted => true | _ => false

-- REGRESSION(decref_fuel_exhausted_never_partial)
#guard decRefFuelMatchesBound
#guard c3Heap.releaseFuelBound ≥ 103 && chainHeap.releaseFuelBound ≥ 8

/-- A malformed cyclic heap (object `2` owns itself). -/
def cyclicHeap : HeapState :=
  { HeapState.empty with
    nextId := 2, refCounts := [(true, 2, 1)], heapObjs := [{ id := 2, tag := 0, objFields := [.objPtr 2], scalarFields := [] }] }

def cyclicReleaseIsError : Bool :=
  match cyclicHeap.decRefObj 2 1 with
  | .error _ => true
  | .ok _ => false

-- REGRESSION(decref_cycle_is_error)
#guard cyclicReleaseIsError

/-! ## C4.2 exclusivity of in-place scalar / tag mutation -/

def withCtor (shareCount : Nat) (op : LNIRExpr) : Except UBError (Val × HeapState) :=
  run (heapWithChild 1) (.letBind 1 .objPtr (.allocCtor 0 [0] [20])
    (.incRef 1 shareCount (.letBind 3 .unit op (.ret 3))))

def onFreedCtor (op : LNIRExpr) : Except UBError (Val × HeapState) :=
  run (heapWithChild 1) (.letBind 1 .objPtr (.allocCtor 0 [0] [20]) (.decRef 1 1 (.letBind 3 .unit op (.ret 3))))

def mutateThenRead (shareCount : Nat) (op read : LNIRExpr) : Except UBError (Val × HeapState) :=
  run (heapWithChild 1) (.letBind 1 .objPtr (.allocCtor 0 [0] [20])
    (.incRef 1 shareCount (.letBind 3 .unit op (.letBind 4 .i64 read (.ret 4)))))

def scalarSet : LNIRExpr := .call "lean_native_ctor_set_scalar" [1, idxZero, 21] .unit

/-- `uset`/`sset`: exclusive ⇒ scalar slot updated, object slot untouched; shared ⇒ `nonExclusiveWrite`;
    freed ⇒ `useAfterFree`; out-of-range ⇒ `outOfBounds 5 1`. -/
def scalarSetContract : Bool :=
  retVal? (mutateThenRead 0 scalarSet (.ctorGetScalar 1 0 .i64)) == some (.u64 43) &&
  retVal? (mutateThenRead 0 scalarSet (.ctorGetObj 1 0)) == some (.objPtr childId) &&
  isNonExclusiveWrite (withCtor 1 scalarSet) && isUseAfterFree (onFreedCtor scalarSet) &&
  (match withCtor 0 (.call "lean_native_ctor_set_scalar" [1, idxFive, 21] .unit) with
   | .error (.outOfBounds 5 1) => true | _ => false)

-- REGRESSION(ctor_set_scalar_slot)
#guard scalarSetContract

def setTag : LNIRExpr := .call "lean_native_ctor_set_tag" [1, 21] .unit

/-- `setTag`: exclusive ⇒ new tag `43`, fields unchanged; shared ⇒ `nonExclusiveWrite`; freed ⇒ `useAfterFree`. -/
def setTagContract : Bool :=
  retVal? (mutateThenRead 0 setTag (.call "lean_native_ctor_tag" [1] .i64)) == some (.u64 43) &&
  retVal? (mutateThenRead 0 setTag (.ctorGetScalar 1 0 .i64)) == some (.u64 42) &&
  isNonExclusiveWrite (withCtor 1 setTag) && isUseAfterFree (onFreedCtor setTag)

-- REGRESSION(set_tag_exclusive_shared_freed)
#guard setTagContract

/-! ## C6.3 SymbolicTV fails closed on source exhaustion -/

def scalarDecl (name : String) (body : LNIRCode) : LNIRDecl :=
  { name := name, params := [{ id := 0, name := "x", ty := .i64 }], retTy := .i64, body := body }

/-- `x1 := x0 * 64; x2 := parFor (len x1) [x0]; ret x0`. Calibrated against the validator's fuel floor
    (`Nat.max fuel 256`): concrete evaluation at 256 exhausts its `parFor` budget for some samples. -/
def fuelHungry : LNIRDecl :=
  scalarDecl "fh" (.letBind 1 .i64 (.scalar (.binOp .mul (.var 0) (.constU64 64)))
    (.parFor 2 1 [0] .i64 (.mapScaleAdd 1 0) (.ret 0)))

/-- Number of the 64 concrete samples on which the source hits evaluator fuel exhaustion at 256. -/
def fuelHungryExhausted : Nat :=
  ((List.range 64).filter fun i =>
    let (env, st) := buildDeclSample fuelHungry i
    match evalCode 256 env st fuelHungry.body with | .error .fuelExhausted => true | _ => false).length

/-- A decl whose source exhausts evaluator fuel on some sample does not validate. -/
def symtvSourceFuelExhaustionFailsClosed : Bool := !(validateTranslationDecl fuelHungry fuelHungry).passed

-- REGRESSION(symtv_source_fuel_exhaustion_fails_closed_calibrated)
#guard fuelHungryExhausted > 0
#guard symtvSourceFuelExhaustionFailsClosed

/-- RC exhaustion uses the same distinguished `.fuelExhausted` the validator classifies as a failed sample;
    the malformed cyclic heap is `.error` through `evalCode`, never `.ok`. -/
def rcExhaustionIsDistinguished : Bool :=
  (match c3Heap.decRefObjFuel 50 c3Heap.nextId 1 with | .error .fuelExhausted => true | _ => false) &&
  (match evalCode 4096 ((VarEnv.empty).bind 0 (.objPtr 2)) cyclicHeap (.decRef 0 1 (.ret 0)) with
   | .error _ => true | .ok _ => false)

-- REGRESSION(symtv_rc_exhaustion_sample_fails_closed)
#guard rcExhaustionIsDistinguished

end LeanNative.Tests.HeapObj5b
