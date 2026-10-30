import Lean
import LeanNative.Semantics.Eval
import LeanNative.Proofs.SymbolicTV
import LeanNative.Backend.LLVM

/-!
# HeapObj contract regressions (`docs/HEAPOBJ_CONTRACT.md`, D1 step 5a)

Executable invariants for the heap-object contract, phrased against the LNIR API on `main`
(`allocCtor tag objFields scalarFields`, `ctorGetObj`, `ctorGetScalar`, `incRef`/`decRef`,
`isExclusive`) and the `HeapState` operations in `Semantics/Value.lean`.

Conventions (machine-checked by `scripts/ci_verify.sh`):
* every regression is introduced by a `-- REGRESSION(<name>)` marker whose `<name>` appears in the
  clause → regression table of `docs/HEAPOBJ_CONTRACT.md`;
* a regression that `main` does not satisfy yet is an explicit expected failure: it carries the marker
  `-- XFAIL(heapobj-contract): flips in 5b` and asserts *today's wrong behaviour* (`#guard !contract`
  and/or `#guard_msgs` pinning today's output). When 5b fixes the defect the assertion breaks the
  build, forcing the xfail to be flipped into a passing `#guard contract`. Nothing is skipped.
-/

namespace LeanNative.Tests.HeapObjContract

open LeanNative.IR LeanNative.Semantics LeanNative.Proofs

/-! ## Fixtures -/

/-- Object id of the shared child used by the owning-edge fixtures. -/
def childId : Nat := 1

/-- Heap holding one live child object `childId` with reference count `rc` (`nextId := childId`,
    so later allocations never collide with it). -/
def heapWithChild (rc : Nat) : HeapState :=
  let st0 := { HeapState.empty with nextId := childId }.allocObj childId
  match st0.incRefObj childId (rc - 1) with
  | .ok st => st
  | .error _ => st0

/-- Variable holding the explicit field index `0` (used by the `ctor_set` fixtures). -/
def idxZero : VarId := 22

/-- Environment: `x0 ↦ child`, `x20 ↦ 42`, `x21 ↦ 43`, `x22 ↦ 0` (index var). -/
def env0 : VarEnv :=
  (((VarEnv.empty.bind 0 (.objPtr childId)).bind 20 (.u64 42)).bind 21 (.u64 43)).bind idxZero (.u64 0)

/-- Return the constant `0` (keeps continuations independent of heap results). -/
def retZero : LNIRCode := .letBind 99 .i64 (.scalar (.constU64 0)) (.ret 99)

def run (st : HeapState) (code : LNIRCode) : Except UBError (Val × HeapState) :=
  evalCode 4096 env0 st code

def showRes : Except UBError (Val × HeapState) → String
  | .ok (v, _) => s!"ok {reprStr v}"
  | .error e => s!"error {reprStr e}"

/-! ## C1 layout indexing: `ctorGetObj i` ↦ `objFields[i]`, `ctorGetScalar i ty` ↦ `scalarFields[i]` -/

/-- `x1 := allocCtor 5 [x0] [x20, x21]; x2 := get x1; ret x2`. -/
def probeMixed (get : LNIRExpr) : Except UBError (Val × HeapState) :=
  run (heapWithChild 1) (.letBind 1 .objPtr (.allocCtor 5 [0] [20, 21]) (.letBind 2 .i64 get (.ret 2)))

def retVal? (r : Except UBError (Val × HeapState)) : Option Val :=
  match r with | .ok (v, _) => some v | .error _ => none

-- REGRESSION(layout_ctorGetObj_indexes_objFields)
#guard retVal? (probeMixed (.ctorGetObj 1 0)) == some (.objPtr childId)

-- REGRESSION(layout_scalar_only_ctor_indexes_scalarFields)
#guard retVal? (run (heapWithChild 1)
  (.letBind 1 .objPtr (.allocCtor 5 [] [20, 21]) (.letBind 2 .i64 (.ctorGetScalar 1 1 .i64) (.ret 2))))
  == some (.u64 43)

/-- Contract: in a mixed ctor, `ctorGetScalar i` reads `scalarFields[i]` (never an object slot). -/
def scalarSlotIndexing : Bool :=
  retVal? (probeMixed (.ctorGetScalar 1 0 .i64)) == some (.u64 42) &&
  retVal? (probeMixed (.ctorGetScalar 1 1 .i64)) == some (.u64 43)

-- REGRESSION(layout_scalar_slot_indexing)
-- XFAIL(heapobj-contract): flips in 5b — `main` indexes the flat list `objFields ++ scalarFields`.
#guard !scalarSlotIndexing
/-- info: ok LeanNative.Semantics.Val.objPtr 1 | ok LeanNative.Semantics.Val.u64 42 -/
#guard_msgs in
#eval IO.println s!"{showRes (probeMixed (.ctorGetScalar 1 0 .i64))} | {showRes (probeMixed (.ctorGetScalar 1 1 .i64))}"

/-- Contract: `ctorGetObj i` with `i ≥ |objFields|` is `outOfBounds`, never a scalar slot. -/
def objIndexBounded : Bool :=
  match probeMixed (.ctorGetObj 1 1) with
  | .error (.outOfBounds _ _) => true
  | _ => false

-- REGRESSION(layout_ctorGetObj_out_of_objFields_is_error)
-- XFAIL(heapobj-contract): flips in 5b — `main` lets `ctorGetObj 1` alias `scalarFields[0]`.
#guard !objIndexBounded
/-- info: ok LeanNative.Semantics.Val.u64 42 -/
#guard_msgs in
#eval IO.println (showRes (probeMixed (.ctorGetObj 1 1)))

/-- Lean runtime layout pin: object slots first, then `usize` slots, then scalars sorted by size
    (descending) at byte offsets relative to the end of the `usize` area. `scalarFields` follow this
    order, so `ctorGetScalar i` lowers to `lean_ctor_get_usize(o, numObjs + i)` for `i < numUsize` and to
    `lean_ctor_get_uintN(o, 8 * (numObjs + numUsize) + off_i)` otherwise. -/
structure LayoutProbe where
  a : Nat
  b : UInt8
  c : UInt64
  d : USize

-- REGRESSION(layout_lean_runtime_offsets)
/--
info: objs=1 usize=1 ssize=9
object 0
scalar size=1 off=8 UInt8
scalar size=8 off=0 UInt64
usize 1
-/
#guard_msgs in
open Lean Compiler LCNF in
#eval show CoreM Unit from do
  let l ← getCtorLayout ``LayoutProbe.mk
  IO.println s!"objs={l.ctorInfo.size} usize={l.ctorInfo.usize} ssize={l.ctorInfo.ssize}"
  for f in l.fieldInfo do
    IO.println (match f with
      | .object i _ => s!"object {i}"
      | .usize i => s!"usize {i}"
      | .scalar sz off ty => s!"scalar size={sz} off={off} {ty}"
      | _ => "erased")

/-! ## C2 tagged immediates -/

/-- `2^63`: the smallest `UInt64` that does not fit the in-pointer `lean_box` payload (`LEAN_MAX_SMALL_NAT`). -/
def highBit : UInt64 := 0x8000000000000000

/-- `x1 := boxScalar x0 ty; x2 := unboxScalar x1 ty; ret x2` and the `lean_native_box_u64` call form. -/
def boxRoundTrip (v : UInt64) : List (Option Val) :=
  let env := VarEnv.empty.bind 0 (.u64 v)
  [ retVal? (evalCode 16 env .empty
      (.letBind 1 .objPtr (.boxScalar 0 .i64) (.letBind 2 .i64 (.unboxScalar 1 .i64) (.ret 2)))),
    retVal? (evalCode 16 env .empty
      (.letBind 1 .objPtr (.call "lean_native_box_u64" [0] .objPtr)
        (.letBind 2 .i64 (.call "lean_native_unbox_u64" [1] .i64) (.ret 2)))) ]

/-- The physical in-pointer box `lean_box(n) = (n << 1) | 1` and `lean_unbox(p) = p >> 1` on 64-bit words. -/
def inPtrRoundTrip (v : UInt64) : UInt64 := ((v <<< 1) ||| 1) >>> 1

-- REGRESSION(box_abstract_high_bit_roundtrip)
-- Abstract boxing is the identity for every value (incl. `2^63`, `2^64 − 1`); the in-pointer payload
-- range is exactly `[0, 2^63)`, so `2^63` is the boundary where a physical heap box is required.
#guard [0, 1, highBit - 1, highBit, highBit + 1, 0xFFFFFFFFFFFFFFFF].all fun v =>
  boxRoundTrip v == [some (.u64 v), some (.u64 v)]
#guard inPtrRoundTrip (highBit - 1) == highBit - 1 && inPtrRoundTrip highBit == 0 &&
  inPtrRoundTrip 0xFFFFFFFF == 0xFFFFFFFF

/-- `boxScalar x0 ty` for a scalar parameter of LNIR type `ty`, emitted in optimized LLVM mode. -/
def boxIR (ty : LNIRType) : String :=
  LeanNative.Backend.LLVM.emitDeclLLVM true
    { name := "bx", params := [{ id := 0, name := "x", ty := ty }], retTy := .objPtr,
      body := .letBind 1 .objPtr (.boxScalar 0 ty) (.ret 1) }

/-- The in-pointer `lean_box` lowering (`shl 1`, `or 1`, `inttoptr`). -/
def isInPtrBox (ir : String) : Bool :=
  ir.contains "shl i64" && ir.contains "inttoptr i64"

-- REGRESSION(codegen_box_small_scalar_in_pointer)
#guard [LNIRType.i1, .i8, .i16, .i32].all (isInPtrBox ∘ boxIR)

/-- Contract (C2.1 table): boxing a `UInt64` must use a heap scalar object (`lean_box_uint64`), never the
    in-pointer tag, because values `≥ 2^63` do not fit the payload. -/
def u64BoxIsHeap : Bool := !isInPtrBox (boxIR .i64)

-- REGRESSION(codegen_box_u64_high_bit)
-- XFAIL(heapobj-contract): flips in 5b — `main` boxes `i64` in-pointer (`shl 1 | 1`), dropping bit 63.
#guard !u64BoxIsHeap

-- REGRESSION(tagged_immediate_rc_noop)
#guard [Val.u64 7, .bool true, .unit].all fun v =>
  let env := VarEnv.empty.bind 0 v
  let st := heapWithChild 1
  (match st.evalIncRef env 0 3, st.evalDecRef env 0 3 with
   | .ok s1, .ok s2 => s1 == st && s2 == st
   | _, _ => false)

-- REGRESSION(tagged_immediate_isExclusive_true)
#guard retVal? (evalExpr (VarEnv.empty.bind 0 (.u64 7)) HeapState.empty (.isExclusive 0))
  == some (.bool true)

-- REGRESSION(nullary_ctor_is_immediate)
#guard match run (heapWithChild 1) (.letBind 1 .objPtr (.allocCtor 3 [] []) (.incRef 1 1 (.decRef 1 2 retZero))) with
  | .ok (_, st) => st.refCounts == (heapWithChild 1).refCounts
  | .error _ => false

def objParam : LNIRParam := { id := 0, name := "o", ty := .objPtr }
def mkDecl (name : String) (body : LNIRCode) : LNIRDecl :=
  { name := name, params := [objParam], retTy := .i64, body := body }

-- REGRESSION(codegen_rc_checks_tag_bit)
#guard (LeanNative.Backend.LLVM.emitDeclLLVM true (mkDecl "rc" (.incRef 0 1 (.decRef 0 1 retZero)))).contains "rc_tagged"
#guard (LeanNative.Backend.LLVM.emitRuntimeAndCAbiHelpers false).contains "%is_scalar = icmp ne i64 %tag, 0"

/-- Contract: `isExclusive` on a `tobject` must test null / tag bit before loading `m_rc`. -/
def isExclusiveCodegenTagChecked : Bool :=
  let ir := LeanNative.Backend.LLVM.emitDeclLLVM true (mkDecl "isx" (.letBind 1 .i64 (.isExclusive 0) (.ret 1)))
  ir.contains "and i64" && ir.contains "icmp eq ptr"

-- REGRESSION(codegen_isExclusive_checks_tag_bit)
-- XFAIL(heapobj-contract): flips in 5b — LLVM emits a direct `load i32` from the object pointer (P-cert C5).
#guard !isExclusiveCodegenTagChecked

/-- Contract: a nullary ctor with tag `t` is emitted as `lean_box(t)` (`inttoptr (2t+1)`), never `null`. -/
def nullaryCtorCodegenBoxed : Bool :=
  let d : LNIRDecl := { name := "nul", params := [], retTy := .objPtr,
                        body := .letBind 1 .objPtr (.allocCtor 3 [] []) (.ret 1) }
  (LeanNative.Backend.LLVM.emitDeclLLVM true d).contains "inttoptr i64 7"

-- REGRESSION(codegen_nullary_ctor_boxed)
-- XFAIL(heapobj-contract): flips in 5b — LLVM stores `null` for every nullary `allocCtor`.
#guard !nullaryCtorCodegenBoxed

/-! ## C3 owning-edge multiplicity & decRef total-or-error -/

/-- `x1 := allocCtor 0 [x0 × k] []; decRef x1 1; ret 0`: the caller transfers `k` owned references to
    the child into the parent, then drops the parent. -/
def ownEdges (k : Nat) : LNIRCode :=
  .letBind 1 .objPtr (.allocCtor 0 (List.replicate k 0) []) (.decRef 1 1 retZero)

def runOwnEdges (k : Nat) : Except UBError (Val × HeapState) := run (heapWithChild k) (ownEdges k)

def showOwnEdges (k : Nat) : String :=
  match runOwnEdges k with
  | .ok (_, st) => s!"ok childRc={st.getObjRefCount childId}"
  | .error e => s!"error {reprStr e}"

/-- Contract (total-or-error): either every owning edge is released (child freed) or `.error`. -/
def ownEdgesContract (k : Nat) : Bool :=
  match runOwnEdges k with
  | .ok (_, st) => st.getObjRefCount childId == 0
  | .error _ => true

-- REGRESSION(rc_repeated_edges_arith)
#guard (List.range 6).all fun k =>
  let st := heapWithChild (k + 1)
  let stepped : Except UBError HeapState :=
    (List.range (k + 1)).foldl (fun (acc : Except UBError HeapState) _ => acc.bind (·.decRefObj childId 1)) (.ok st)
  (match stepped, st.decRefObj childId (k + 1) with
   | .ok s1, .ok s2 => s1.getObjRefCount childId == 0 && s1 == s2 &&
       (match s1.decRefObj childId 1 with | .error (.useAfterFree _) => true | _ => false)
   | _, _ => false)

-- REGRESSION(decref_freed_or_underflow_is_error)
#guard match (heapWithChild 2).decRefObj childId 3, HeapState.empty.decRefObj childId 1 with
  | .error (.useAfterFree 1), .error (.useAfterFree 1) => true
  | _, _ => false

-- REGRESSION(rc_repeated_owning_edges_released)
-- XFAIL(heapobj-contract): flips in 5b — dropping the parent releases none of its owning edges.
#guard !(ownEdgesContract 2) && !(ownEdgesContract 3)
/-- info: ok childRc=2 | ok childRc=3 -/
#guard_msgs in
#eval IO.println s!"{showOwnEdges 2} | {showOwnEdges 3}"

-- REGRESSION(c3_100_owning_edges)
-- XFAIL(heapobj-contract): flips in 5b — P-cert C3: decRef returns `ok` with live child references
-- (`main`: childRc=100, nothing released; #277: childRc=65 after fuel truncation).
#guard !(ownEdgesContract 100)
/-- info: ok childRc=100 -/
#guard_msgs in
#eval IO.println (showOwnEdges 100)

/-! ### C5.2/C5.3 fuel bound: executable reference for the counting rule

`RHeap` lists `(id, rc, objFields)` for every live object. `release fuel h [root]` pops one worklist entry
per fuel unit and charges one more unit per object freed. It never traverses tuples, and rejects tuples that
own an edge (C5.2 well-formedness). This is a test oracle for the *counting rule* of the contract, not a model
of `HeapState`. 5b's `decRefObjFuel` must agree with it on these shapes. -/

abbrev RHeap := List (Nat × Nat × List Val)

def owns : Val → Bool
  | .objPtr _ | .sarrayId _ => true
  | .tuple vs => vs.attach.any fun ⟨v, _⟩ => owns v
  | _ => false

def RHeap.rc (h : RHeap) (o : Nat) : Nat := ((h.find? (·.1 == o)).map (·.2.1)).getD 0
def RHeap.fields (h : RHeap) (o : Nat) : List Val := ((h.find? (·.1 == o)).map (·.2.2)).getD []
def RHeap.setRc (h : RHeap) (o rc : Nat) : RHeap := h.map fun e => if e.1 == o then (o, rc, e.2.2) else e

def release : Nat → RHeap → List Val → Except String RHeap
  | _, h, [] => .ok h
  | 0, _, _ :: _ => .error "fuelExhausted"
  | f + 1, h, e :: rest =>
    match e with
    | .objPtr o =>
      match h.rc o with
      | 0 => .error "useAfterFree"
      | 1 => match f with
        | 0 => .error "fuelExhausted"
        | f' + 1 => release f' (h.setRc o 0) (h.fields o ++ rest)
      | n + 2 => release f (h.setRc o (n + 1)) rest
    | .tuple vs => if owns (.tuple vs) then .error "nestedTupleOwnership" else release f h rest
    | _ => release f h rest  -- scalars, immediates; `.sarrayId` goes to `decRefBuf` (not modelled here)

/-- `B(heap) = 1 + Σ_o (1 + |o.objFields|)`. -/
def fuelBound (h : RHeap) : Nat := 1 + (h.map fun e => 1 + e.2.2.length).sum

/-- Shapes in which dropping `root` (rc 1) frees every object. -/
def fuelShapes : List RHeap :=
  [ -- P-cert C3: parent 0 with 100 edges to child 1 (rc 100)
    [(0, 1, List.replicate 100 (.objPtr 1)), (1, 100, [])],
    -- chain 0 → 1 → 2 → 3 → 4
    (List.range 5).map fun i => (i, 1, if i < 4 then [.objPtr (i + 1)] else []),
    -- diamond 0 → {1, 2} → 3
    [(0, 1, [.objPtr 1, .objPtr 2]), (1, 1, [.objPtr 3]), (2, 1, [.objPtr 3]), (3, 2, [])],
    -- mixed fields: repeated edge, scalar, fieldless-ctor immediate, sarray edge
    [(0, 1, [.objPtr 1, .u64 5, .tuple [.u64 0], .sarrayId 7, .objPtr 1]), (1, 2, [.u64 9])] ]

def allFreed (h : RHeap) : Bool := h.all (·.2.1 == 0)

-- REGRESSION(fuel_bound_boundary)
-- `B` units release completely; `B − 1` units give `fuelExhausted`, never a partial `ok`.
#guard fuelBound (fuelShapes.headD []) == 103
#guard fuelShapes.all fun h =>
  (match release (fuelBound h) h [.objPtr 0] with | .ok h' => allFreed h' | .error _ => false) &&
  (match release (fuelBound h - 1) h [.objPtr 0] with | .error "fuelExhausted" => true | _ => false)
-- nested tuple ownership is ill-formed and is rejected, not traversed
#guard match release 100 [(0, 1, [.tuple [.u64 0, .objPtr 1]]), (1, 1, [])] [.objPtr 0] with
  | .error "nestedTupleOwnership" => true | _ => false

/-- Contract (C5.2): `allocCtor` rejects an `objFields` entry that is a tuple owning an edge. -/
def nestedTupleOwnershipRejected : Bool :=
  match run (heapWithChild 1) (.letBind 1 .objPtr (.allocCtor 0 [0] [])
      (.letBind 2 .objPtr (.allocCtor 0 [1] []) (.ret 2))) with
  | .error (.typeError _) => true
  | _ => false

-- REGRESSION(wf_objFields_no_nested_tuple_ownership)
-- XFAIL(heapobj-contract): flips in 5b — `main`'s `allocCtor` is a flat tuple, so a ctor field nests the
-- child ctor (and its owning edge) inline.
#guard !nestedTupleOwnershipRejected

/-- Chain `x0 (child) ← x1 ← x2 ← x3`, then drop the root: the full release must free the child. -/
def chainDrop : LNIRCode :=
  .letBind 1 .objPtr (.allocCtor 0 [0] [])
    (.letBind 2 .objPtr (.allocCtor 0 [1] []) (.letBind 3 .objPtr (.allocCtor 0 [2] []) (.decRef 3 1 retZero)))

/-- Contract (C5.1, total-or-error) on `main`'s actual release path (`evalCode → evalDecRef → decRefObj`),
    for every evaluator fuel in `0..64`: `.error`, or `.ok` with the whole chain released. -/
def chainReleaseTotalOrError : Bool :=
  (List.range 65).all fun fuel =>
    match evalCode fuel env0 (heapWithChild 1) chainDrop with
    | .ok (_, st) => st.getObjRefCount childId == 0
    | .error _ => true

-- REGRESSION(decref_chain_total_or_error)
-- XFAIL(heapobj-contract): flips in 5b — `main`'s `decRef` of a ctor value is a no-op `ok`, leaving
-- the transitively owned child live at every fuel (a partial release reported as success).
#guard !chainReleaseTotalOrError
/-- info: ok childRc=1 -/
#guard_msgs in
#eval IO.println (match evalCode 0 env0 (heapWithChild 1) chainDrop with
  | .ok (_, st) => s!"ok childRc={st.getObjRefCount childId}" | .error e => s!"error {reprStr e}")

-- UNCOVERED(C5.1-fuelExhausted-ctor): `main` has no recursive release and no fuel-bounded helper, so no
-- behaviour can reach a fuel-exhaustion error; the counting rule is pinned by `fuel_bound_boundary`.
-- UNCOVERED(C5.4-underfueled-helper): `decRefObjFuel`/`decRefValsFuel` do not exist on `main`; 5b adds the
-- helper and a regression "underfuelled call ⇒ `.error .fuelExhausted`, never partial `.ok`".

/-! ## C4 exclusivity: `ctor_set` / `del` only when `rc == 1`, else UB error -/

-- REGRESSION(exclusive_write_sarray_shared_is_ub)
#guard match ({ HeapState.empty with buffers := [{ id := 3, exclusive := false, data := #[1, 2] }] }).writeElemExclusive 3 0 9 with
  | .error (.nonExclusiveWrite 3) => true
  | _ => false

/-- `x1 := allocCtor 0 [x0] [x20]; incRef x1 shareCount; x3 := op …; ret x3`. -/
def withCtor (shareCount : Nat) (op : LNIRExpr) : Except UBError (Val × HeapState) :=
  run (heapWithChild 1) (.letBind 1 .objPtr (.allocCtor 0 [0] [20])
    (.incRef 1 shareCount (.letBind 3 .unit op (.ret 3))))

/-- Contract: `isExclusive` on a heap object with `rc == 2` is `false`. -/
def isExclusiveSharedFalse : Bool := retVal? (withCtor 1 (.isExclusive 1)) == some (.bool false)

-- REGRESSION(isExclusive_shared_obj_false)
-- XFAIL(heapobj-contract): flips in 5b — `main` answers `true` for every non-sarray value.
#guard !isExclusiveSharedFalse

def isNonExclusiveWrite : Except UBError (Val × HeapState) → Bool
  | .error (.nonExclusiveWrite _) => true
  | _ => false

/-- `ctor_set x1[x22 = 0] := x21` on `x1 := allocCtor 0 [x0] [x20]`. The index var `x22` is bound to `0`,
    an in-bounds object slot, so the only thing that differs between the shared and exclusive cases is `rc`. -/
def ctorSet : LNIRExpr := .call "lean_native_ctor_set" [1, idxZero, 21] .unit

/-- `withCtor shareCount (ctor_set …)`, then read field `0` back. -/
def ctorSetThenRead (shareCount : Nat) : Except UBError (Val × HeapState) :=
  run (heapWithChild 1) (.letBind 1 .objPtr (.allocCtor 0 [0] [20])
    (.incRef 1 shareCount (.letBind 3 .unit ctorSet (.letBind 4 .i64 (.ctorGetObj 1 0) (.ret 4)))))

/-- Contract (C4.2 shared): `rc == 2` ⇒ exactly `.nonExclusiveWrite`, not `outOfBounds`, `unsupportedCall`
    or any other reason. -/
def ctorSetSharedIsUB : Bool := isNonExclusiveWrite (withCtor 1 ctorSet)

/-- Contract (C4.2 exclusive): `rc == 1` ⇒ `ok`, and field `0` now holds the written value `43`. -/
def ctorSetExclusiveUpdates : Bool := retVal? (ctorSetThenRead 0) == some (.u64 43)

-- REGRESSION(ctor_set_shared_is_ub)
-- XFAIL(heapobj-contract): flips in 5b — `lean_native_ctor_set` is not an LNIR operation on `main`;
-- today's failure reason is `unsupportedCall`, not the required `nonExclusiveWrite`.
#guard !ctorSetSharedIsUB
/-- info: error LeanNative.Semantics.UBError.unsupportedCall "lean_native_ctor_set" -/
#guard_msgs in
#eval IO.println (showRes (withCtor 1 ctorSet))

-- REGRESSION(ctor_set_exclusive_ok)
-- XFAIL(heapobj-contract): flips in 5b — an exclusive (`rc == 1`) `ctor_set` must succeed and update field 0.
#guard !ctorSetExclusiveUpdates
/-- info: error LeanNative.Semantics.UBError.unsupportedCall "lean_native_ctor_set" -/
#guard_msgs in
#eval IO.println (showRes (ctorSetThenRead 0))

-- REGRESSION(del_shared_is_ub)
-- XFAIL(heapobj-contract): flips in 5b — `lean_native_del_obj` is not an LNIR operation on `main`.
#guard !isNonExclusiveWrite (withCtor 1 (.call "lean_native_del_obj" [1] .unit))
/-- info: error LeanNative.Semantics.UBError.unsupportedCall "lean_native_del_obj" -/
#guard_msgs in
#eval IO.println (showRes (withCtor 1 (.call "lean_native_del_obj" [1] .unit)))

/-! ## C5 SymbolicTV obligations: fuel / RC exhaustion ⇒ `passed = false` -/

def scalarDecl (name : String) (body : LNIRCode) : LNIRDecl :=
  { name := name, params := [{ id := 0, name := "x", ty := .i64 }], retTy := .i64, body := body }

-- REGRESSION(symtv_rejects_wrong_result)
#guard !(validateTranslationDecl (scalarDecl "f" (.ret 0))
  (scalarDecl "f" (.letBind 1 .i64 (.scalar (.constU64 2)) (.ret 1)))).passed

/-- A straight-line body longer than the symbolic executor's fuel (256 steps). -/
def longBody : Nat → LNIRCode
  | 0 => .ret 0
  | n + 1 => .letBind (n + 1000) .i64 (.scalar (.constU64 n.toUInt64)) (longBody n)

-- REGRESSION(symtv_fuel_exhaustion_fails_closed)
-- XFAIL(heapobj-contract): flips in 5b — `symExecCode` silently returns `.unit` at fuel 0 and the
-- identical-but-unexplored decls pass.
#guard (validateTranslationDecl (scalarDecl "long" (longBody 300)) (scalarDecl "long" (longBody 300))).passed

-- REGRESSION(symtv_rc_effects_fail_closed)
-- XFAIL(heapobj-contract): flips in 5b — symbolic execution ignores `incRef`/`decRef`, so dropping an
-- owned `decRef` (a leak) validates; RC tracking that is absent or exhausted must give `passed = false`.
#guard (validateTranslationDecl
  { name := "drop", params := [objParam, { id := 1, name := "x", ty := .i64 }], retTy := .i64, body := .decRef 0 1 (.ret 1) }
  { name := "drop", params := [objParam, { id := 1, name := "x", ty := .i64 }], retTy := .i64, body := .ret 1 }).passed

end LeanNative.Tests.HeapObjContract
