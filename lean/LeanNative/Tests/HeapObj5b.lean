import Lean
import LeanNative.Semantics.Eval
import LeanNative.Proofs.SymbolicTV
import LeanNative.Backend.LLVM
import LeanNative.IR.Bridge
import LeanNative.Driver.BuildExe

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

/-! ## C1.1 SymbolicTV models a fieldless ctor as the evaluator's immediate `.tuple [tag]` -/

/-- `x1 := allocCtor 3 [] []; incRef x1 1; if x0 == 999 then (isExclusive x1 | false) else true`, with balanced
    `decRef x1 2` on both branches. The fieldless ctor is immediate, so `isExclusive` is `true` after `incRef`. -/
def nullaryExclDecl (rareFalse : Bool) : LNIRDecl :=
  { name := "nullary_ctor_excl", params := [{ id := 0, name := "x", ty := .i64 }], retTy := .i1, body :=
    .letBind 1 .objPtr (.allocCtor 3 [] []) (.incRef 1 1
      (.letBind 2 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 999)))
        (.ite 2
          (.letBind 3 .i1 (if rareFalse then .scalar (.constBool false) else .isExclusive 1) (.decRef 1 2 (.ret 3)))
          (.letBind 3 .i1 (.scalar (.constBool true)) (.decRef 1 2 (.ret 3)))))) }

def nullaryExclAt999 (rareFalse : Bool) : Option Val :=
  retVal? (evalCode 4096 (VarEnv.empty.bind 0 (.u64 999)) .empty (nullaryExclDecl rareFalse).body)

/-- Concrete source is `true` and target `false` on `x = 999`, so replacing the rare-branch `isExclusive` with
    `false` must be rejected; the unchanged decl still validates (the check is not vacuous). -/
def nullaryCtorTvContract : Bool :=
  nullaryExclAt999 false == some (.bool true) && nullaryExclAt999 true == some (.bool false) &&
  !(validateTranslationDecl (nullaryExclDecl false) (nullaryExclDecl true)).passed &&
  (validateTranslationDecl (nullaryExclDecl false) (nullaryExclDecl false)).passed

-- REGRESSION(symtv_nullary_ctor_immediate_exclusive)
#guard nullaryCtorTvContract

/-! ## C4/C5 `build-exe` gate: RC-ADT and unsupported LLVM calls are rejected before emission -/

def gateMod (body : LNIRCode) (retTy : LNIRType := .i64) : LNIRModule :=
  { moduleName := "build_exe_gate", decls := [{ name := "f", params := [{ id := 0, name := "x", ty := .i64 }], retTy, body }] }

/-- An RC-ADT decl, an external call and a `ctorGetScalar` are each rejected; a scalar decl passes. -/
def buildExeGateContract : Bool :=
  let rcAdt := gateMod (.letBind 1 .objPtr (.allocCtor 0 [] [0]) (.ret 1)) .objPtr
  let extCall := gateMod (.letBind 1 .i64 (.call "puts" [0] .i64 true) (.ret 1))
  let scalar := gateMod (.letBind 1 .i64 (.scalar (.binOp .add (.var 0) (.constU64 1))) (.ret 1))
  (buildExeLLVMGate? rcAdt rcAdt).isSome &&
  (buildExeLLVMGate? scalar extCall).isSome &&
  (buildExeLLVMGate? scalar scalar).isNone

-- REGRESSION(build_exe_llvm_gate_fail_closed)
#guard buildExeGateContract

/-! ## C1.1 / C4.2 SymbolicTV write-space separation (`objFields` vs `scalarFields` vs `ctorTag`) -/

/-- Guard an external `.objPtr` parameter (`id = 0`) with `isExclusive` and rare `x == 999` (`id = 1`)
    so concrete sampling hits the defined exclusive path on small seeds while `999` exercises the
    in-place mutation path symbolically without returning the mutated object. -/
def extRareExclGuard (mutBody : LNIRCode) : LNIRCode :=
  .letBind 10 .i1 (.isExclusive 0)
    (.ite 10
      (.letBind 11 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999)))
        (.ite 11 mutBody retZero))
      retZero)

def objAndScalarSlot0Decl (dropFirst : Bool) (scalarFirst : Bool) : LNIRDecl :=
  let writeObj : LNIRCode → LNIRCode := fun k =>
    .letBind 13 .unit (.call "lean_native_ctor_set" [0, 12, 2] .unit) k
  let writeScalar : LNIRCode → LNIRCode := fun k =>
    .letBind 14 .unit (.call "lean_native_ctor_set_scalar" [0, 12, 3] .unit) k
  let mutSeq : LNIRCode :=
    if scalarFirst then
      if dropFirst then writeObj retZero else writeScalar (writeObj retZero)
    else
      if dropFirst then writeScalar retZero else writeObj (writeScalar retZero)
  { name := "ctor_write_spaces"
    params := [ { id := 0, name := "o", ty := .objPtr }
              , { id := 1, name := "x", ty := .i64 }
              , { id := 2, name := "child", ty := .objPtr }
              , { id := 3, name := "sc", ty := .i64 } ]
    retTy := .i64
    body := .letBind 12 .i64 (.scalar (.constU64 0)) (extRareExclGuard mutSeq) }

/-- C1.1/C4.2: `ctor_set` on object slot `0` and `ctor_set_scalar` on scalar slot `0` mutate disjoint
    index spaces; dropping either write in either order must fail `memWritesEquiv`, while commuting the
    two independent slot-`0` writes on the same exclusive object must validate! -/
def ctorWriteSpaceSeparationContract : Bool :=
  let bothObjThenSc := objAndScalarSlot0Decl false false
  let onlySc := objAndScalarSlot0Decl true false
  let bothScThenObj := objAndScalarSlot0Decl false true
  let onlyObj := objAndScalarSlot0Decl true true
  let rDropObj := validateTranslationDecl bothObjThenSc onlySc
  let rDropSc := validateTranslationDecl bothScThenObj onlyObj
  let rCommute := validateTranslationDecl bothObjThenSc bothScThenObj
  !rDropObj.memWritesEquiv && !rDropObj.passed &&
  !rDropSc.memWritesEquiv && !rDropSc.passed &&
  rCommute.memWritesEquiv && rCommute.passed

-- REGRESSION(symtv_ctor_obj_vs_scalar_write_space_disjoint)
#guard ctorWriteSpaceSeparationContract

def setTagSideEffectDecl (tagVal : UInt64) (doSetTag : Bool) (requireExcl : Bool := true) : LNIRDecl :=
  let tagWrite : LNIRCode :=
    .letBind 12 .i64 (.scalar (.constU64 tagVal))
      (.letBind 13 .unit (.call "lean_native_ctor_set_tag" [0, 12] .unit) retZero)
  let body : LNIRCode :=
    if !doSetTag then
      if requireExcl then extRareExclGuard retZero else retZero
    else if requireExcl then
      extRareExclGuard tagWrite
    else
      .letBind 11 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 999))) (.ite 11 tagWrite retZero)
  { name := "ctor_set_tag_tv"
    params := [{ id := 0, name := "o", ty := .objPtr }, { id := 1, name := "x", ty := .i64 }]
    retTy := .i64
    body := body }

def setTagThenReadDecl (useConst : Bool) : LNIRDecl :=
  { name := "ctor_set_tag_read"
    params := [{ id := 0, name := "x", ty := .i64 }]
    retTy := .i64
    body :=
      .letBind 1 .objPtr (.allocCtor 2 [] [0])
        (.letBind 2 .i64 (.scalar (.constU64 7))
          (.letBind 3 .unit (.call "lean_native_ctor_set_tag" [1, 2] .unit)
            (.letBind 4 .i64 (if useConst then .scalar (.constU64 7) else .call "lean_native_ctor_tag" [1] .i64)
              (.letBind 5 .i64 (.ctorGetScalar 1 0 .i64)
                (.letBind 6 .i64 (.scalar (.binOp .add (.var 4) (.var 5)))
                  (.decRef 1 1 (.ret 6))))))) }

/-- C4.2: `lean_native_ctor_set_tag` is modeled in `SymbolicTV` without `symUnsupported`, distinguishes
    unreturned tag mutations via `.ctorTag` write space, rejects unguarded non-exclusive target `setTag`
    (`ubRefines = false`), and folds subsequent `lean_native_ctor_tag` reads while preserving fields. -/
def symtvSetTagContract : Bool :=
  let set7 := setTagSideEffectDecl 7 true true
  let set9 := setTagSideEffectDecl 9 true true
  let noop := setTagSideEffectDecl 7 false true
  let unguardedSet7 := setTagSideEffectDecl 7 true false
  let plainNoop := setTagSideEffectDecl 7 false false
  let rSame := validateTranslationDecl set7 set7
  let rDrop := validateTranslationDecl set7 noop
  let rDiffTag := validateTranslationDecl set7 set9
  let rExcl := validateTranslationDecl plainNoop unguardedSet7
  let rFold := validateTranslationDecl (setTagThenReadDecl false) (setTagThenReadDecl true)
  rSame.passed &&
  !rDrop.memWritesEquiv && !rDrop.passed &&
  !rDiffTag.memWritesEquiv && !rDiffTag.passed &&
  !rExcl.ubRefines && !rExcl.passed &&
  rFold.passed

-- REGRESSION(symtv_ctor_set_tag_modeled_and_tracked)
#guard symtvSetTagContract

def nullarySetTagDecl : LNIRDecl :=
  { name := "nullary_set_tag"
    params := [{ id := 0, name := "x", ty := .i64 }]
    retTy := .i64
    body :=
      .letBind 1 .objPtr (.allocCtor 0 [] [])
        (.letBind 2 .i1 (.scalar (.binOp .eq (.var 0) (.constU64 999)))
          (.ite 2
            (.letBind 3 .i64 (.scalar (.constU64 5))
              (.letBind 4 .unit (.call "lean_native_ctor_set_tag" [1, 3] .unit) retZero))
            retZero)) }

def symtvNullarySetTagIsUB : Bool :=
  let noop : LNIRDecl := { nullarySetTagDecl with body := retZero }
  let r := validateTranslationDecl noop nullarySetTagDecl
  !r.ubRefines && !r.passed

-- REGRESSION(symtv_nullary_ctor_set_tag_ub)
#guard symtvNullarySetTagIsUB

def extSetTagInBranchDecl (tagVal : UInt64) : LNIRDecl :=
  { name := "ext_set_tag_branch"
    params := [{ id := 0, name := "o", ty := .objPtr }, { id := 1, name := "c", ty := .i64 }]
    retTy := .i64
    body :=
      .letBind 2 .i1 (.isExclusive 0)
        (.ite 2
          (.letBind 3 .i1 (.scalar (.binOp .eq (.var 1) (.constU64 1)))
            (.ite 3
              (.letBind 4 .i64 (.scalar (.constU64 tagVal))
                (.letBind 5 .unit (.call "lean_native_ctor_set_tag" [0, 4] .unit) retZero))
              retZero))
          retZero) }

def symtvExtBranchSetTagTracked : Bool :=
  let d1 := extSetTagInBranchDecl 3
  let d2 := extSetTagInBranchDecl 4
  let rDiff := validateTranslationDecl d1 d2
  let rSame := validateTranslationDecl d1 d1
  !rDiff.memWritesEquiv && !rDiff.passed && rSame.passed

-- REGRESSION(symtv_ext_branch_ctor_set_tag_tracked)
#guard symtvExtBranchSetTagTracked

end LeanNative.Tests.HeapObj5b
