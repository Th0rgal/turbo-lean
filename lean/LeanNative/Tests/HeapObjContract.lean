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

/-- `x1 := allocCtor 5 [x0] [x20]; ret x1`: the result and the new heap. -/
def allocOne : Except UBError (Val × HeapState) :=
  run (heapWithChild 1) (.letBind 1 .objPtr (.allocCtor 5 [0] [20]) (.ret 1))

/-- Contract (C1.1): a ctor with fields allocates a live `HeapObj` (`.objPtr o`, `rc o == 1`). -/
def allocLiveRcOne : Bool :=
  match allocOne with
  | .ok (.objPtr o, st) => st.getObjRefCount o == 1
  | _ => false

-- REGRESSION(layout_alloc_live_rc_one)
-- XFAIL(heapobj-contract): flips in 5b — `main`'s `allocCtor` is an immediate tuple with no heap cell.
#guard !allocLiveRcOne
/--
info: ok LeanNative.Semantics.Val.tuple
  [LeanNative.Semantics.Val.u64 5, LeanNative.Semantics.Val.objPtr 1, LeanNative.Semantics.Val.u64 42]
-/
#guard_msgs in
#eval IO.println (showRes allocOne)

/-- Contract (C1.1): `ctorGetScalar i` with `i ≥ |scalarFields|` is `outOfBounds i |scalarFields|`. -/
def scalarOOBBounded : Bool :=
  match probeMixed (.ctorGetScalar 1 2 .i64) with
  | .error (.outOfBounds 2 2) => true
  | _ => false

-- REGRESSION(layout_scalar_oob_is_error)
-- XFAIL(heapobj-contract): flips in 5b — `main` bounds the index by the flat length (3), so index 2 reads
-- `scalarFields[1]`.
#guard !scalarOOBBounded
/-- info: ok LeanNative.Semantics.Val.u64 43 -/
#guard_msgs in
#eval IO.println (showRes (probeMixed (.ctorGetScalar 1 2 .i64)))

/-- `x1 := allocCtor 5 [x0] [x20]; decRef x1 1; x2 := get x1; ret x2`: read through a freed object. -/
def readAfterFree (get : LNIRExpr) : Except UBError (Val × HeapState) :=
  run (heapWithChild 1) (.letBind 1 .objPtr (.allocCtor 5 [0] [20]) (.decRef 1 1 (.letBind 2 .i64 get (.ret 2))))

def isUseAfterFree : Except UBError (Val × HeapState) → Bool
  | .error (.useAfterFree _) => true
  | _ => false

/-- Contract (C1.1): `ctorGetObj` / `ctorGetScalar` on a freed object is `.useAfterFree`. -/
def freedReadsAreUAF : Bool :=
  isUseAfterFree (readAfterFree (.ctorGetObj 1 0)) && isUseAfterFree (readAfterFree (.ctorGetScalar 1 0 .i64))

-- REGRESSION(layout_freed_read_is_error)
-- XFAIL(heapobj-contract): flips in 5b — the immediate tuple survives `decRef`, so both reads succeed.
#guard !freedReadsAreUAF
/-- info: ok LeanNative.Semantics.Val.objPtr 1 | ok LeanNative.Semantics.Val.objPtr 1 -/
#guard_msgs in
#eval IO.println s!"{showRes (readAfterFree (.ctorGetObj 1 0))} | {showRes (readAfterFree (.ctorGetScalar 1 0 .i64))}"

/-- Lean runtime layout pin: object slots first, then `usize` slots, then the scalar fields, sorted
    by ascending byte offset `off_i` relative to the end of the `usize` area (Lean places wider scalars at
    lower offsets; `getCtorLayout` itself returns fields in declaration order). `scalarFields` follow this
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

/-! ### C2.3 structural guard-before-load check on emitted LLVM IR

`guardedDerefs ir fn ptrs` parses function `@fn` into basic blocks and returns one entry per instruction that
dereferences the object pointer (`load`/`store`/`atomicrmw`/`getelementptr` whose *address* operand is the
pointer or an SSA reload of its slot). The entry is `true` iff, in the CFG, every path from `entry` to that
block crosses a **non-null edge** (the false edge of `icmp eq ptr P, null`) **and** an **untagged edge** (the
edge on which `(ptrtoint P) & 1 == 0`). Both are checked by cutting those edges and testing reachability. A
dereference in the block that performs the test (before its branch) is therefore unguarded. -/
namespace IRCheck

def words (s : String) : List String :=
  ((s.replace "," " ").splitOn " ").filter (· != "")

/-- Body lines of `define … @fn(…) … {` up to its closing `}`. -/
def fnLines (ir fn : String) : List String :=
  match (ir.splitOn "\n").dropWhile (fun l => !(l.startsWith "define" && (l.splitOn s!"@{fn}(").length > 1)) with
  | [] => []
  | _ :: rest => rest.takeWhile (· != "}")

/-- `(label, instructions)` in program order; the first block is `entry`. -/
def blocks (ls : List String) : List (String × List String) :=
  (ls.foldl (fun acc l =>
    if !l.startsWith " " && l.endsWith ":" then (String.ofList (l.toList.dropLast), []) :: acc
    else match acc with
      | (b, is) :: rest => (b, is ++ [l]) :: rest
      | [] => [("entry", [l])]) []).reverse

/-- Address operand of a dereferencing instruction, if any. -/
def derefAddr (l : String) : Option String :=
  let segs := l.splitOn ", "
  let w0 := words (segs.headD "")
  let addrSeg := match segs[1]? with | some s => (match words s with | ["ptr", a] | "ptr" :: a :: _ => some a | _ => none) | none => none
  if w0.contains "atomicrmw" then w0.getLast?
  else if w0.contains "load" || w0.contains "getelementptr" || w0.head? == some "store" then addrSeg
  else none

def label (s : String) : String := String.ofList (s.toList.drop 1)

/-- One `true`/`false` (guarded or not) per dereference of `seeds` or any `load ptr, ptr <slot>` alias. -/
def guardedDerefs (ir fn : String) (seeds slots : List String) : List Bool := Id.run do
  let bs := blocks (fnLines ir fn)
  let insts := bs.flatMap (·.2)
  let ptrs := seeds ++ insts.filterMap fun l => match words l with
    | [d, "=", "load", "ptr", "ptr", s, "align", _] => if slots.contains s then some d else none
    | _ => none
  let pints := insts.filterMap fun l => match words l with
    | [d, "=", "ptrtoint", "ptr", p, "to", "i64"] => if ptrs.contains p then some d else none
    | _ => none
  let tbits := insts.filterMap fun l => match words l with
    | [d, "=", "and", "i64", x, "1"] => if pints.contains x then some d else none
    | _ => none
  -- (cond, polarity on which the pointer is non-null) / (cond, polarity on which it is untagged)
  let nonNull := insts.filterMap fun l => match words l with
    | [d, "=", "icmp", "eq", "ptr", p, "null"] => if ptrs.contains p then some (d, false) else none
    | [d, "=", "icmp", "ne", "ptr", p, "null"] => if ptrs.contains p then some (d, true) else none
    | _ => none
  let untagged := insts.filterMap fun l => match words l with
    | [d, "=", "icmp", "ne", "i64", t, "0"] => if tbits.contains t then some (d, false) else none
    | [d, "=", "icmp", "eq", "i64", t, "0"] => if tbits.contains t then some (d, true) else none
    | _ => none
  let edges : List (String × String × Option (String × Bool)) := bs.flatMap fun (b, is) =>
    is.flatMap fun l => match words l with
      | ["br", "label", t] => [(b, label t, none)]
      | ["br", "i1", c, "label", t, "label", e] => [(b, label t, some (c, true)), (b, label e, some (c, false))]
      | _ => []
  let reach (cut : List (String × Bool)) : List String := Id.run do
    let mut seen := ["entry"]
    for _ in bs do
      for (a, b, c) in edges do
        if seen.contains a && !seen.contains b && !(c.any cut.contains) then seen := b :: seen
    return seen
  let rNN := reach nonNull
  let rUT := reach untagged
  return bs.flatMap fun (b, is) => is.filterMap fun l => (derefAddr l).bind fun a =>
    if ptrs.contains a then some (!rNN.contains b && !rUT.contains b) else none

/-- Non-vacuous: at least one dereference, and every dereference is guarded. -/
def allGuarded (ds : List Bool) : Bool := !ds.isEmpty && ds.all id

end IRCheck

def emitOpt (d : LNIRDecl) : String := LeanNative.Backend.LLVM.emitDeclLLVM true d
def declDerefs (d : LNIRDecl) : List Bool := IRCheck.guardedDerefs (emitOpt d) d.name ["%arg_v0"] ["%slot_v0"]

-- self-test of the checker: an unguarded load and a guarded one
#guard IRCheck.guardedDerefs "define i64 @t(ptr %p) {\nentry:\n  %v = load i32, ptr %p, align 4\n  ret i64 0\n}" "t" ["%p"] [] == [false]
#guard IRCheck.guardedDerefs ("define i64 @t(ptr %p) {\nentry:\n  %n = icmp eq ptr %p, null\n  br i1 %n, label %d, label %c\n" ++
  "c:\n  %i = ptrtoint ptr %p to i64\n  %b = and i64 %i, 1\n  %s = icmp ne i64 %b, 0\n  br i1 %s, label %d, label %u\n" ++
  "u:\n  %v = load i32, ptr %p, align 4\n  br label %d\nd:\n  ret i64 0\n}") "t" ["%p"] [] == [true]

-- REGRESSION(codegen_rc_checks_tag_bit)
-- Structural: inline RC (`incRef`/`decRef`) and the `lean_native_inc`/`lean_native_dec` helpers dereference
-- `m_rc` only in blocks dominated by a non-null edge and an untagged edge.
#guard IRCheck.allGuarded (declDerefs (mkDecl "rc" (.incRef 0 1 (.decRef 0 1 retZero))))
#guard ["lean_native_inc", "lean_native_dec"].all fun fn =>
  IRCheck.allGuarded (IRCheck.guardedDerefs (LeanNative.Backend.LLVM.emitRuntimeAndCAbiHelpers false) fn ["%obj"] [])

def isxDecl : LNIRDecl := mkDecl "isx" (.letBind 1 .i64 (.isExclusive 0) (.ret 1))

/-- Contract: `isExclusive` on a `tobject` tests null and the tag bit before loading `m_rc` (structural). -/
def isExclusiveCodegenTagChecked : Bool := IRCheck.allGuarded (declDerefs isxDecl)

-- REGRESSION(codegen_isExclusive_checks_tag_bit)
-- XFAIL(heapobj-contract): flips in 5b — LLVM emits a direct `load i32` from the object pointer (P-cert C5).
#guard !isExclusiveCodegenTagChecked
#guard declDerefs isxDecl == [false]

/-- A field projection on a `taggedPtr` parameter. -/
def projDecl : LNIRDecl :=
  { name := "prj", params := [{ objParam with ty := .taggedPtr }], retTy := .objPtr,
    body := .letBind 1 .objPtr (.ctorGetObj 0 0) (.ret 1) }

/-- Contract (C2.3): a projection on a `taggedPtr` loads the field, and only behind the null/tag guard. -/
def projectionGuardedLoad : Bool := IRCheck.allGuarded (declDerefs projDecl)

-- REGRESSION(codegen_projection_guarded_field_load)
-- XFAIL(heapobj-contract): flips in 5b — `ctorGetObj` emits no field load at all (it copies the object
-- pointer), so there is neither a field read nor a guard.
#guard !projectionGuardedLoad
#guard declDerefs projDecl == []

-- REGRESSION(codegen_tag_read_rejected)
-- C2.3 fallback, tag reads: `main` has no tag-read lowering, so a decl reading the tag is rejected by
-- `findUnsupportedLLVMCallInCode` instead of being emitted with an unguarded `m_tag` load.
#guard LeanNative.Backend.LLVM.findUnsupportedLLVMCallInCode []
  (.letBind 1 .i64 (.call "lean_native_ctor_tag" [0] .i64) (.ret 1)) == some "lean_native_ctor_tag"

/-- Contract (C2.3 fallback): every decl is either emitted with all dereferences guarded, or rejected. -/
def unguardedDeclRejected (d : LNIRDecl) : Bool :=
  (declDerefs d).all id || (LeanNative.Backend.LLVM.findUnsupportedLLVMCallInCode [] d.body).isSome

-- REGRESSION(codegen_unguarded_decl_rejected)
-- XFAIL(heapobj-contract): flips in 5b — the `isExclusive` decl is emitted with an unguarded load and
-- `findUnsupportedLLVMCallInCode` returns `none`.
#guard !unguardedDeclRejected isxDecl
#guard (LeanNative.Backend.LLVM.findUnsupportedLLVMCallInCode [] isxDecl.body).isNone

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

/-- `x1 := allocCtor 0 [x0] []; incRef x1 1; x2 := allocCtor 0 [x1, x1] []; decRef x2 1`: a grandparent
    with two edges to a parent that owns the child. -/
def grandparentDrop : LNIRCode :=
  .letBind 1 .objPtr (.allocCtor 0 [0] [])
    (.incRef 1 1 (.letBind 2 .objPtr (.allocCtor 0 [1, 1] []) (.decRef 2 1 retZero)))

/-- Contract (C3.2, recursive): dropping the grandparent releases both edges to the parent, which frees it,
    which releases its edge to the child (`rc child = 0`), or the whole thing is `.error`. -/
def recursiveReleaseBeyondParent : Bool :=
  match run (heapWithChild 1) grandparentDrop with
  | .ok (_, st) => st.getObjRefCount childId == 0
  | .error _ => true

-- REGRESSION(rc_recursive_release_grandchild)
-- XFAIL(heapobj-contract): flips in 5b — no release recurses, so the grandchild stays live.
#guard !recursiveReleaseBeyondParent
/-- info: ok childRc=1 -/
#guard_msgs in
#eval IO.println (match run (heapWithChild 1) grandparentDrop with
  | .ok (_, st) => s!"ok childRc={st.getObjRefCount childId}" | .error e => s!"error {reprStr e}")

/-- Heap with one exclusive (`rc = 1`) sarray buffer `3`, bound to `x23`. -/
def heapWithBuf : HeapState := { HeapState.empty with buffers := [{ id := 3, exclusive := true, data := #[1, 2] }] }

/-- `x1 := allocCtor 0 [x23] []; decRef x1 1; ret 0` with `x23 ↦ .sarrayId 3`. -/
def sarrayEdgeDrop : Except UBError (Val × HeapState) :=
  evalCode 4096 (env0.bind 23 (.sarrayId 3)) heapWithBuf
    (.letBind 1 .objPtr (.allocCtor 0 [23] []) (.decRef 1 1 retZero))

/-- Contract (C3.2, `.sarrayId` edge): dropping the parent releases the buffer through `decRefBuf` (freed). -/
def sarrayEdgeReleased : Bool :=
  match sarrayEdgeDrop with
  | .ok (_, st) => (st.findBuffer 3).isNone
  | .error _ => true

-- REGRESSION(rc_sarray_edge_released)
-- XFAIL(heapobj-contract): flips in 5b — the buffer owned through a ctor field is never released.
#guard !sarrayEdgeReleased
-- non-vacuity: a direct `decRef` of the same buffer does free it
#guard match heapWithBuf.decRefBuf 3 1 with | .ok st => (st.findBuffer 3).isNone | .error _ => false

-- REGRESSION(incref_freed_is_error)
-- C3.3: `incRef` on a freed object is `.useAfterFree` (release path: `decRef x0 1; incRef x0 1`).
#guard match run (heapWithChild 1) (.decRef 0 1 (.incRef 0 1 retZero)) with
  | .error (.useAfterFree 1) => true
  | _ => false

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

/-- `x1 := allocCtor 0 [x0] [x20]; decRef x1 1; x3 := op; ret x3`: `op` on a freed object. -/
def onFreedCtor (op : LNIRExpr) : Except UBError (Val × HeapState) :=
  run (heapWithChild 1) (.letBind 1 .objPtr (.allocCtor 0 [0] [20]) (.decRef 1 1 (.letBind 3 .unit op (.ret 3))))

-- REGRESSION(isExclusive_freed_is_error)
-- XFAIL(heapobj-contract): flips in 5b — C4.1: `isExclusive` on a freed object must be `.useAfterFree`;
-- `main` answers `true`.
#guard !isUseAfterFree (onFreedCtor (.isExclusive 1))
/-- info: ok LeanNative.Semantics.Val.bool true -/
#guard_msgs in
#eval IO.println (showRes (onFreedCtor (.isExclusive 1)))

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

/-- Contract (C4.2 freed): `ctor_set` and `del` on a freed object are `.useAfterFree` (not
    `nonExclusiveWrite`, not `unsupportedCall`). -/
def freedMutationIsUAF : Bool :=
  isUseAfterFree (onFreedCtor ctorSet) && isUseAfterFree (onFreedCtor (.call "lean_native_del_obj" [1] .unit))

-- REGRESSION(mutation_freed_is_error)
-- XFAIL(heapobj-contract): flips in 5b — neither operation exists on `main` (`unsupportedCall`).
#guard !freedMutationIsUAF
/-- info: error LeanNative.Semantics.UBError.unsupportedCall "lean_native_ctor_set" | error LeanNative.Semantics.UBError.unsupportedCall "lean_native_del_obj" -/
#guard_msgs in
#eval IO.println s!"{showRes (onFreedCtor ctorSet)} | {showRes (onFreedCtor (.call "lean_native_del_obj" [1] .unit))}"

/-! ## C6 SymbolicTV obligations: fuel / RC exhaustion ⇒ `passed = false` -/

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

/-- `x1 := x0 * 32; x2 := parFor (len x1) [x0]; ret x0`. Concrete evaluation (fuel 128) exhausts its
    `parFor` budget for every sample with `x0 ≥ 5` and succeeds otherwise. -/
def fuelHungry : LNIRDecl :=
  scalarDecl "fh" (.letBind 1 .i64 (.scalar (.binOp .mul (.var 0) (.constU64 32)))
    (.parFor 2 1 [0] .i64 (.mapScaleAdd 1 0) (.ret 0)))

/-- Number of the 64 concrete samples on which the *source* hits evaluator fuel exhaustion. -/
def fuelHungryExhausted : Nat :=
  ((List.range 64).filter fun i =>
    let (env, st) := buildDeclSample fuelHungry i
    match evalCode 128 env st fuelHungry.body with | .error (.outOfBounds _ 128) => true | _ => false).length

-- REGRESSION(symtv_source_fuel_exhaustion_fails_closed)
-- XFAIL(heapobj-contract): flips in 5b — C6.3: samples where the source exhausts evaluator fuel are
-- counted as "source UB" (vacuous), so the decl still passes. The contract requires `passed = false`.
#guard fuelHungryExhausted > 0
#guard (validateTranslationDecl fuelHungry fuelHungry).passed

-- UNCOVERED(C6.3-rc-exhaustion-sample): `main`'s `evalCode` has no RC/heap-exhaustion error (there is no
-- recursive release), so no concrete sample can produce one; 5b adds it with `fuelExhausted`.

end LeanNative.Tests.HeapObjContract
