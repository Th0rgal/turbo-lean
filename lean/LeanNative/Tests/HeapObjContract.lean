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
  `-- XFAIL(heapobj-contract): flips in 5b`, and its **first** command is `#guard !<pred>` where `<pred>` is a
  `def <pred> : Bool := …` of this module, documented `/-- Contract … -/`, whose **elaborated** value
  (zeta/beta/whnf-reduced with the roots opaque, by a Lean meta check in `ci_verify.sh`) is not a `Bool` literal
  and still reaches the evaluator / heap ops / LLVM emitter / translation validator. Further
  `#guard`/`#guard_msgs` lines pin today's output. The doc table names that `#guard !<pred>` per XFAIL row.
  When 5b fixes the defect the assertion breaks the build, forcing the xfail to be flipped into a passing
  `#guard <pred>`. Nothing is skipped. `ci_verify.sh` rejects `#guard true`-style guards and self-tests that.
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

/-- Variable holding a malformed field value: a tuple that owns an edge (C5.2). -/
def malformedVar : VarId := 24

/-- Variable holding the out-of-range field index `5`. -/
def idxFive : VarId := 25

/-- Environment: `x0 ↦ child`, `x20 ↦ 42`, `x21 ↦ 43`, `x22 ↦ 0` (index var),
    `x24 ↦ .tuple [.u64 0, .objPtr child]` (malformed field), `x25 ↦ 5` (index var). -/
def env0 : VarEnv :=
  [(0, .objPtr childId), (20, .u64 42), (21, .u64 43), (idxZero, .u64 0),
   (malformedVar, .tuple [.u64 0, .objPtr childId]), (idxFive, .u64 5)].foldl
    (fun (e : VarEnv) (x, v) => e.bind x v) VarEnv.empty

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
-- Holds since #280: `allocCtor` with fields allocates a live heap object (`allocHeapCtor`, `rc = 1`).
#guard allocLiveRcOne

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
-- Holds since #280: both reads through the freed heap object are `useAfterFree`.
#guard freedReadsAreUAF

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

-- UNCOVERED(C1.2-scalar-lowering): `main`'s emitter has no `getCtorLayout`-driven `lean_ctor_get_usize`/`_uintN`
-- lowering; only the Lean layout itself is pinned (`layout_lean_runtime_offsets`).

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

/-! ### C2.3 structural checks on emitted LLVM IR

`guardedDerefs ir fn ptrs` parses function `@fn` into basic blocks and returns one entry per instruction that
dereferences the object pointer (`load`/`store`/`atomicrmw`/`getelementptr` whose *address* operand is the
pointer or an SSA reload of its slot). The entry is `true` iff, in the CFG, every path from `entry` to that
block crosses a **non-null edge** (the false edge of `icmp eq ptr P, null`) **and** an **untagged edge** (the
edge on which `(ptrtoint P) & 1 == 0`). Both are checked by cutting those edges and testing reachability. A
dereference in the block that performs the test (before its branch) is therefore unguarded.

The positive codegen predicates (`heapBoxCarries`, `inPtrBoxCarries`, `projectionLoadsField`) follow the
*returned* value back through slot reloads (`load T, ptr %slot` ↦ the last non-initialising `store … , ptr %slot`
preceding it in the same block, else the rejecting `uninitOrigin`),
`phi` operands and value-preserving casts, to its **origins** (the defining instructions that produce it). Every
origin must be of the required kind; an empty origin set (e.g. no `ret`) is a rejection. -/
namespace IRCheck

def words (s : String) : List String :=
  ((s.replace "," " ").splitOn " ").filter (· != "")

/-- `words` that also splits call parentheses and `phi` brackets. -/
def toks (s : String) : List String :=
  words ((((s.replace "(" " ").replace ")" " ").replace "[" " ").replace "]" " ")

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

/-- Parsed function: blocks, the object pointer and its slot reloads, and the blocks reachable from `entry`
    without crossing a non-null edge (`rNN`) / an untagged edge (`rUT`). -/
structure Fn where
  bs : List (String × List String)
  ptrs : List String
  rNN : List String
  rUT : List String

def parseFn (ir fn : String) (seeds slots : List String) : Fn := Id.run do
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
  return { bs, ptrs, rNN := reach nonNull, rUT := reach untagged }

/-- Block `b` is reachable only through a non-null edge and an untagged edge. -/
def Fn.guarded (f : Fn) (b : String) : Bool := !f.rNN.contains b && !f.rUT.contains b

def Fn.insts (f : Fn) : List String := f.bs.flatMap (·.2)

/-- Tokens of the instruction defining SSA name `x`, and its block. -/
def Fn.defOf (f : Fn) (x : String) : Option (List String × String) :=
  f.bs.findSome? fun (b, is) => is.findSome? fun l => match toks l with
    | d :: "=" :: rest => if d == x then some (rest, b) else none
    | _ => none

def Fn.isSlot (f : Fn) (x : String) : Bool :=
  match f.defOf x with | some ("alloca" :: _, _) => true | _ => false

/-- Order-aware, block-local reaching store of the reload `x` of `slot`: the value of the **last** `store … , ptr
    slot` preceding `x`'s defining instruction **in `x`'s own basic block**. `none` (⇒ `uninitOrigin`) when no such
    store exists in that block (stores in other blocks are ignored, conservatively) or when it is the
    zero-initialising store that directly follows the slot's `alloca`. -/
def Fn.reachingStore (f : Fn) (slot x : String) : Option String :=
  (f.bs.findSome? fun (_, is) =>
    let pre := is.takeWhile fun l => match toks l with | d :: "=" :: _ => d != x | _ => true
    if pre.length == is.length then none else
    some <| (pre.zip ("" :: pre)).foldl (fun acc (l, prev) => match toks l with
      | ["store", _, v, "ptr", a, "align", _] | ["store", _, v, "ptr", a] =>
        if a != slot then acc
        else if (match toks prev with | d :: "=" :: "alloca" :: _ => d == slot | _ => false) then none else some v
      | _ => acc) none).join

/-- Rejecting origin of a reload with no reaching store (`Fn.reachingStore`): it is not an SSA name, so it is
    never a parameter, a box, or a guarded load. -/
def uninitOrigin : String := "<uninit>"

/-- Origins of SSA value `x`: follow slot reloads (to their block-local reaching store only), `phi`, and
    value-preserving casts (`zext`/`sext`/`bitcast`, plus `and _, 1` when `bool1` holds, i.e. `Bool`
    normalisation). A reload without a reaching store contributes `uninitOrigin`, never an empty origin list. -/
def Fn.origins (f : Fn) (bool1 : Bool) : Nat → String → List String
  | 0, x => [x]
  | n + 1, x => match f.defOf x with
    | some (["load", _, "ptr", a, "align", _], _) | some (["load", _, "ptr", a], _) =>
      if f.isSlot a then match f.reachingStore a x with
        | none => [uninitOrigin]
        | some v => f.origins bool1 n v
      else [x]
    | some ("phi" :: _ :: ins, _) =>
      ((ins.zipIdx.filterMap fun (v, i) => if i % 2 == 0 then some v else none).flatMap (f.origins bool1 n)).eraseDups
    | some ([c, _, v, "to", _], _) =>
      if ["zext", "sext", "bitcast"].contains c then f.origins bool1 n v else [x]
    | some (["and", _, v, "1"], _) => if bool1 then f.origins bool1 n v else [x]
    | _ => [x]

/-- Origins of every `ret` operand (empty when the function has no value-returning `ret`). -/
def Fn.retOrigins (f : Fn) : List String :=
  (f.insts.filterMap fun l => match toks l with | ["ret", _, v] => some v | _ => none).flatMap (f.origins false 64)

/-- `v` carries the value of parameter `arg`: `v` has at least one origin and **every** origin of `v` (through
    slot reloads, `phi` and value-preserving casts) is `arg`. A `phi` joining `arg` with a constant, another value,
    or a reload of an initialisation-only slot is rejected. -/
def Fn.carries (f : Fn) (arg v : String) : Bool :=
  let os := f.origins true 64 v
  !os.isEmpty && os.all (· == arg)

/-- `call … @name(args)` ⇒ `(name, args)`. -/
def callOf (ts : List String) : Option (String × List String) :=
  match ts.dropWhile (fun t => !t.startsWith "@") with
  | fn :: args => if ts.contains "call" then some (String.ofList (fn.toList.drop 1), args) else none
  | [] => none

/-- Byte offset of a `getelementptr` on base `p` (`i8`-indexed bytes, or `ptr`/`i64`-indexed words). -/
def gepOffset (ts : List String) (p : String) : Option Nat :=
  match ts.filter (· != "inbounds") with
  | ["getelementptr", "i8", "ptr", b, "i64", k] => if b == p then k.toNat? else none
  | ["getelementptr", ty, "ptr", b, "i64", k] =>
    if b == p && (ty == "ptr" || ty == "i64") then k.toNat?.map (8 * ·) else none
  | _ => none

def heapBoxFns : List String := ["lean_box_uint64", "lean_box_usize", "lean_box_float", "lean_box_float32"]

/-- Byte offset of the scalar payload of a scalar box from the object pointer (C1 layout): the 8-byte header,
    then `objFields · 8` object slots, then the scalar at scalar offset `0` (a box has one scalar field). -/
def boxPayloadOffset (objFields : Nat) : Nat := 8 + 8 * objFields

/-- Origin `o` is a heap scalar box of `arg`: either `o = call @lean_box_{uint64,usize,float,float32}(… arg …)`, or
    `o = call @lean_alloc_ctor(i32 tag, i32 objFields, i32 ssz)` followed by a store of `arg` **at the scalar
    payload** `boxPayloadOffset objFields`: a `store` through a `getelementptr` on `o` at that byte offset, or
    `lean_ctor_set_*(o, off, arg)` with `off = 8 · objFields` (`lean_ctor_set_*` offsets are relative to the
    field area, after the header). A store to `o` itself (offset 0, the header) is rejected. -/
def Fn.isHeapBoxOf (f : Fn) (arg o : String) : Bool :=
  match f.defOf o with
  | some (ts, _) => match callOf ts with
    | some (fn, args) =>
      if heapBoxFns.contains fn then args.any (f.carries arg)
      else match fn, args with
        | "lean_alloc_ctor", ["i32", _, "i32", k, "i32", _] => match k.toNat? with
          | some nObj => f.insts.any fun l =>
            let ts := toks l
            (match ts with
             | ["store", _, v, "ptr", a, "align", _] | ["store", _, v, "ptr", a] =>
               f.carries arg v && match f.defOf a with
                 | some (gts, _) => gepOffset gts o == some (boxPayloadOffset nObj) | none => false
             | _ => false) ||
            (match callOf ts with
             | some (g, ["ptr", p, _, off, _, v]) =>
               g.startsWith "lean_ctor_set_" && p == o && off.toNat? == some (8 * nObj) && f.carries arg v
             | _ => false)
          | none => false
        | _, _ => false
    | none => false
  | none => false

/-- Origin `o` is an in-pointer `lean_box(arg)`: `inttoptr (or (shl arg 1) 1)`. -/
def Fn.isInPtrBoxOf (f : Fn) (arg o : String) : Bool :=
  match f.defOf o with
  | some (["inttoptr", "i64", y, "to", "ptr"], _) => match f.defOf y with
    | some (["or", "i64", z, "1"], _) => match f.defOf z with
      | some (["shl", "i64", w, "1"], _) => f.carries arg w
      | _ => false
    | _ => false
  | _ => false

/-- Positive heap-box check: the function returns, and every origin of every returned value is a heap scalar box
    carrying `arg`. Rejects `ret ptr null`, the in-pointer `shl 1 | 1` form, and a box of a value other than `arg`. -/
def heapBoxCarries (ir fn arg : String) : Bool :=
  let f := parseFn ir fn [] []
  let os := f.retOrigins
  !os.isEmpty && os.all (f.isHeapBoxOf arg)

/-- Positive in-pointer check: every origin of every returned value is `lean_box(arg)`. -/
def inPtrBoxCarries (ir fn arg : String) : Bool :=
  let f := parseFn ir fn [] []
  let os := f.retOrigins
  !os.isEmpty && os.all (f.isInPtrBoxOf arg)

/-- Origin `o` is a field load at byte offset `off` from the object pointer, in a guarded block:
    `%A = getelementptr … ptr P, … off` with `P` the object pointer, then `o = load T, ptr %A` behind the guard. -/
def Fn.isGuardedFieldLoad (f : Fn) (off : Nat) (o : String) : Bool :=
  match f.defOf o with
  | some (["load", _, "ptr", a, "align", _], b) | some (["load", _, "ptr", a], b) =>
    f.guarded b && match f.defOf a with
      | some (ts, _) => f.ptrs.any fun p => gepOffset ts p == some off
      | none => false
  | _ => false

/-- Positive projection check: every origin of the returned value is a guarded load from `P + off`. Rejects a
    copy of the object pointer, a `getelementptr` with no load, a load at the wrong offset, and an unguarded load. -/
def projectionLoadsField (ir fn : String) (seeds slots : List String) (off : Nat) : Bool :=
  let f := parseFn ir fn seeds slots
  let os := f.retOrigins
  !os.isEmpty && os.all (f.isGuardedFieldLoad off)

/-- One `true`/`false` (guarded or not) per dereference of `seeds` or any `load ptr, ptr <slot>` alias. -/
def guardedDerefs (ir fn : String) (seeds slots : List String) : List Bool :=
  let f := parseFn ir fn seeds slots
  f.bs.flatMap fun (b, is) => is.filterMap fun l => (derefAddr l).bind fun a =>
    if f.ptrs.contains a then some (f.guarded b) else none

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

/-! ### C2.1 boxing codegen (positive dataflow predicates, see `IRCheck.heapBoxCarries`) -/

/-- `boxScalar x0 ty` for a scalar parameter of LNIR type `ty`, emitted in optimized LLVM mode. -/
def boxIR (ty : LNIRType) : String :=
  LeanNative.Backend.LLVM.emitDeclLLVM true
    { name := "bx", params := [{ id := 0, name := "x", ty := ty }], retTy := .objPtr,
      body := .letBind 1 .objPtr (.boxScalar 0 ty) (.ret 1) }

/-- The emitted box of `ty` returns a heap scalar object carrying the parameter `%arg_v0`. -/
def boxIsHeap (ty : LNIRType) : Bool := IRCheck.heapBoxCarries (boxIR ty) "bx" "%arg_v0"
/-- The emitted box of `ty` returns `lean_box(%arg_v0)` = `inttoptr ((x << 1) | 1)`. -/
def boxIsInPtr (ty : LNIRType) : Bool := IRCheck.inPtrBoxCarries (boxIR ty) "bx" "%arg_v0"

/-- A hand-written `@bx(i64 %arg_v0)` whose `entry` block is `body`. -/
def bxIR (body : String) : String := "define ptr @bx(i64 %arg_v0) {\nentry:\n" ++ body ++ "}\n"
def heapOK (body : String) : Bool := IRCheck.heapBoxCarries (bxIR body) "bx" "%arg_v0"

-- self-test of the heap-box predicate: positive forms accepted
#guard heapOK "  %b = call ptr @lean_box_uint64(i64 %arg_v0)\n  ret ptr %b\n"
#guard heapOK ("  %o = call ptr @lean_alloc_ctor(i32 0, i32 0, i32 8)\n  %f = getelementptr i8, ptr %o, i64 8\n" ++
  "  store i64 %arg_v0, ptr %f, align 8\n  ret ptr %o\n")
#guard heapOK ("  %o = call ptr @lean_alloc_ctor(i32 0, i32 0, i32 8)\n" ++
  "  call void @lean_ctor_set_uint64(ptr %o, i32 0, i64 %arg_v0)\n  ret ptr %o\n")
-- self-test: NEGATIVE forms rejected — `null` return; in-pointer `shl 1 | 1`; box of a constant (value not
-- carried); allocation without storing the value; a `phi` that may return `null`; no `ret` at all.
#guard !heapOK "  ret ptr null\n"
#guard !heapOK ("  %s = shl i64 %arg_v0, 1\n  %t = or i64 %s, 1\n  %p = inttoptr i64 %t to ptr\n  ret ptr %p\n")
#guard !heapOK "  %b = call ptr @lean_box_uint64(i64 0)\n  ret ptr %b\n"
#guard !heapOK "  %o = call ptr @lean_alloc_ctor(i32 0, i32 0, i32 8)\n  ret ptr %o\n"
#guard !heapOK ("  %b = call ptr @lean_box_uint64(i64 %arg_v0)\n  br label %j\nj:\n" ++
  "  %r = phi ptr [ %b, %entry ], [ null, %x ]\n  ret ptr %r\n")
#guard !heapOK "  %b = call ptr @lean_box_uint64(i64 %arg_v0)\n  unreachable\n"
-- self-test (quorum r3): a boxed value with SOME but not ALL origins equal to the parameter is rejected — the
-- `phi` may box the constant `0`; an allocation that stores the parameter at offset 0 (over the header) instead of
-- the scalar payload `boxPayloadOffset objFields` is rejected (direct store, GEP 0, `lean_ctor_set_*` at the
-- wrong field-area offset, and GEP 8 when `objFields = 1` puts the payload at 16).
#guard !heapOK ("  br label %j\nb:\n  br label %j\nj:\n  %v = phi i64 [ %arg_v0, %entry ], [ 0, %b ]\n" ++
  "  %r = call ptr @lean_box_uint64(i64 %v)\n  ret ptr %r\n")
#guard !heapOK ("  %o = call ptr @lean_alloc_ctor(i32 0, i32 0, i32 8)\n" ++
  "  store i64 %arg_v0, ptr %o, align 8\n  ret ptr %o\n")
#guard !heapOK ("  %o = call ptr @lean_alloc_ctor(i32 0, i32 0, i32 8)\n  %f = getelementptr i8, ptr %o, i64 0\n" ++
  "  store i64 %arg_v0, ptr %f, align 8\n  ret ptr %o\n")
#guard !heapOK ("  %o = call ptr @lean_alloc_ctor(i32 0, i32 1, i32 8)\n  %f = getelementptr i8, ptr %o, i64 8\n" ++
  "  store i64 %arg_v0, ptr %f, align 8\n  ret ptr %o\n")
#guard !heapOK ("  %o = call ptr @lean_alloc_ctor(i32 0, i32 1, i32 8)\n" ++
  "  call void @lean_ctor_set_uint64(ptr %o, i32 0, i64 %arg_v0)\n  ret ptr %o\n")
-- self-test (quorum r4): provenance must be non-empty — a reload of a slot whose only store is its initialising
-- one (boxes `0`) is rejected, and so is a `phi` joining the parameter with such a reload.
#guard !heapOK ("  %slot = alloca i64, align 8\n  store i64 0, ptr %slot, align 8\n" ++
  "  %v = load i64, ptr %slot, align 8\n  %b = call ptr @lean_box_uint64(i64 %v)\n  ret ptr %b\n")
#guard !heapOK ("  %slot = alloca i64, align 8\n  store i64 0, ptr %slot, align 8\n  br label %j\nb:\n" ++
  "  %u = load i64, ptr %slot, align 8\n  br label %j\nj:\n  %v = phi i64 [ %arg_v0, %entry ], [ %u, %b ]\n" ++
  "  %r = call ptr @lean_box_uint64(i64 %v)\n  ret ptr %r\n")
-- self-test (quorum r5): slot reloads are order-aware — a store of the parameter AFTER the reload does not reach
-- it (boxes `0`), nor does one in another block.
#guard !heapOK ("  %slot = alloca i64, align 8\n  store i64 0, ptr %slot, align 8\n  %v = load i64, ptr %slot, align 8\n" ++
  "  store i64 %arg_v0, ptr %slot, align 8\n  %b = call ptr @lean_box_uint64(i64 %v)\n  ret ptr %b\n")
#guard !heapOK ("  %slot = alloca i64, align 8\n  store i64 0, ptr %slot, align 8\n  store i64 %arg_v0, ptr %slot, align 8\n" ++
  "  br label %j\nj:\n  %v = load i64, ptr %slot, align 8\n  %b = call ptr @lean_box_uint64(i64 %v)\n  ret ptr %b\n")
-- while a reload of a slot that is (re)stored with the parameter after initialisation is still accepted.
#guard heapOK ("  %slot = alloca i64, align 8\n  store i64 0, ptr %slot, align 8\n  store i64 %arg_v0, ptr %slot, align 8\n" ++
  "  %v = load i64, ptr %slot, align 8\n  %b = call ptr @lean_box_uint64(i64 %v)\n  ret ptr %b\n")
-- and the layout offset is honoured: with one object field the payload at 16 / field-area offset 8 is accepted;
-- a `phi` whose every incoming value is the parameter (through a cast) is accepted.
#guard heapOK ("  %o = call ptr @lean_alloc_ctor(i32 0, i32 1, i32 8)\n  %f = getelementptr i8, ptr %o, i64 16\n" ++
  "  store i64 %arg_v0, ptr %f, align 8\n  ret ptr %o\n")
#guard heapOK ("  %o = call ptr @lean_alloc_ctor(i32 0, i32 1, i32 8)\n" ++
  "  call void @lean_ctor_set_uint64(ptr %o, i32 8, i64 %arg_v0)\n  ret ptr %o\n")
#guard heapOK ("  %c = bitcast i64 %arg_v0 to i64\n  br label %j\nb:\n  br label %j\nj:\n" ++
  "  %v = phi i64 [ %arg_v0, %entry ], [ %c, %b ]\n  %r = call ptr @lean_box_uint64(i64 %v)\n  ret ptr %r\n")
-- self-test of the in-pointer predicate: accepts `lean_box(x)`, rejects `lean_box(0)` and `null`
#guard IRCheck.inPtrBoxCarries (bxIR "  %s = shl i64 %arg_v0, 1\n  %t = or i64 %s, 1\n  %p = inttoptr i64 %t to ptr\n  ret ptr %p\n") "bx" "%arg_v0"
#guard !IRCheck.inPtrBoxCarries (bxIR "  %s = shl i64 0, 1\n  %t = or i64 %s, 1\n  %p = inttoptr i64 %t to ptr\n  ret ptr %p\n") "bx" "%arg_v0"
#guard !IRCheck.inPtrBoxCarries (bxIR "  ret ptr null\n") "bx" "%arg_v0"

-- REGRESSION(codegen_box_small_scalar_in_pointer)
-- Positive: for `i1/i8/i16/i32` every returned value is `inttoptr ((x << 1) | 1)` of the parameter.
#guard [LNIRType.i1, .i8, .i16, .i32].all boxIsInPtr

/-- Contract (C2.1 table): boxing a `UInt64` must return a heap scalar object (`lean_box_uint64`, or an allocation
    storing the value), never the in-pointer tag, because values `≥ 2^63` do not fit the payload. -/
def u64BoxIsHeap : Bool := boxIsHeap .i64

-- REGRESSION(codegen_box_u64_high_bit)
-- XFAIL(heapobj-contract): flips in 5b — `main` boxes `i64` in-pointer (`shl 1 | 1`), dropping bit 63.
#guard !u64BoxIsHeap
#guard boxIsInPtr .i64

/-- Contract (C2.1 table): `USize` is boxed as a heap scalar object (`lean_box_usize`). -/
def usizeBoxIsHeap : Bool := boxIsHeap .usize

-- REGRESSION(codegen_box_usize_heap)
-- XFAIL(heapobj-contract): flips in 5b — `main` boxes `usize` in-pointer (`shl 1 | 1`).
#guard !usizeBoxIsHeap
#guard boxIsInPtr .usize

/-- Contract (C2.1 table): `Float` is boxed as a heap scalar object (`lean_box_float`). -/
def floatBoxIsHeap : Bool := boxIsHeap .f64

-- REGRESSION(codegen_box_float_heap)
-- XFAIL(heapobj-contract): flips in 5b — `main` boxes `f64` in-pointer (`shl 1 | 1`).
#guard !floatBoxIsHeap
#guard boxIsInPtr .f64

/-- Contract (C2.1 table): `Float32` is boxed as a heap scalar object (`lean_box_float32`). -/
def float32BoxIsHeap : Bool := boxIsHeap .f32

-- REGRESSION(codegen_box_float32_heap)
-- XFAIL(heapobj-contract): flips in 5b — `main` boxes `f32` in-pointer (`shl 1 | 1`).
#guard !float32BoxIsHeap
#guard boxIsInPtr .f32

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

/-- Byte offset of object field `i` in a `lean_ctor_object` (`lean_ctor_get(o, i)`): the 8-byte header
    (`m_rc : i32`, `m_cs_sz : u16`, `m_other : u8`, `m_tag : u8`), then `i` pointer-sized slots. -/
def objFieldOffset (i : Nat) : Nat := 8 + 8 * i

/-- Contract (C2.3): a projection on a `taggedPtr` returns a value loaded from `P + objFieldOffset 0`, and the
    load is behind the null/tag guard (`IRCheck.projectionLoadsField`). -/
def projectionGuardedLoad : Bool :=
  IRCheck.projectionLoadsField (emitOpt projDecl) projDecl.name ["%arg_v0"] ["%slot_v0"] (objFieldOffset 0)

/-- A hand-written `@prj(ptr %p)`: `entry`/`c` run the null/tag guard and branch to `u` (heap path, `heapPath`)
    or to the immediate path `d0`, which traps (`unreachable`: projecting an immediate is UB). -/
def prjIR (heapPath : String) : String :=
  "define ptr @prj(ptr %p) {\nentry:\n  %n = icmp eq ptr %p, null\n  br i1 %n, label %d0, label %c\n" ++
  "c:\n  %i = ptrtoint ptr %p to i64\n  %b = and i64 %i, 1\n  %s = icmp ne i64 %b, 0\n  br i1 %s, label %d0, label %u\n" ++
  "u:\n" ++ heapPath ++ "d0:\n  unreachable\n}\n"
def prjOK (heapPath : String) (off : Nat := 8) : Bool := IRCheck.projectionLoadsField (prjIR heapPath) "prj" ["%p"] [] off

-- self-test of the projection predicate: byte- and word-indexed guarded loads at offset 8 are accepted
#guard prjOK "  %a = getelementptr inbounds i8, ptr %p, i64 8\n  %r = load ptr, ptr %a, align 8\n  ret ptr %r\n"
#guard prjOK "  %a = getelementptr ptr, ptr %p, i64 1\n  %r = load ptr, ptr %a, align 8\n  ret ptr %r\n"
-- self-test: NEGATIVE forms rejected — copy of the object pointer; guarded GEP with no load (address returned);
-- load at the wrong offset (`m_rc` at 0, field 1 at 16); load whose result is not the returned value;
-- unguarded load (in `entry`, before the guard); `null` return; the field load joined (`phi`) with the raw
-- pointer; an immediate path that returns `null` instead of trapping.
#guard !prjOK ("  %a = getelementptr inbounds i8, ptr %p, i64 8\n  %f = load ptr, ptr %a, align 8\n  br label %j\n" ++
  "j:\n  %r = phi ptr [ %f, %u ], [ %p, %c ]\n  ret ptr %r\n")
#guard !IRCheck.projectionLoadsField ((prjIR ("  %a = getelementptr inbounds i8, ptr %p, i64 8\n" ++
  "  %r = load ptr, ptr %a, align 8\n  ret ptr %r\n")).replace "unreachable" "ret ptr null") "prj" ["%p"] [] 8
#guard !prjOK "  ret ptr %p\n"
#guard !prjOK "  %a = getelementptr inbounds i8, ptr %p, i64 8\n  ret ptr %a\n"
#guard !prjOK "  %a = getelementptr inbounds i8, ptr %p, i64 0\n  %r = load ptr, ptr %a, align 8\n  ret ptr %r\n"
#guard !prjOK "  %a = getelementptr inbounds i8, ptr %p, i64 16\n  %r = load ptr, ptr %a, align 8\n  ret ptr %r\n"
#guard !prjOK "  %a = getelementptr inbounds i8, ptr %p, i64 8\n  %r = load ptr, ptr %a, align 8\n  ret ptr %p\n"
#guard !prjOK "  ret ptr null\n"
#guard !IRCheck.projectionLoadsField ("define ptr @prj(ptr %p) {\nentry:\n  %a = getelementptr i8, ptr %p, i64 8\n" ++
  "  %r = load ptr, ptr %a, align 8\n  ret ptr %r\n}\n") "prj" ["%p"] [] 8
-- and the offset parameter is honoured: field 1 at offset 16 is accepted when asked for
#guard prjOK "  %a = getelementptr inbounds i8, ptr %p, i64 16\n  %r = load ptr, ptr %a, align 8\n  ret ptr %r\n" 16

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

/-- Contract (C2.3 fallback) on the `isExclusive` decl: guarded or rejected. -/
def isxDeclGuardedOrRejected : Bool := unguardedDeclRejected isxDecl

-- REGRESSION(codegen_unguarded_decl_rejected)
-- XFAIL(heapobj-contract): flips in 5b — the `isExclusive` decl is emitted with an unguarded load and
-- `findUnsupportedLLVMCallInCode` returns `none`.
#guard !isxDeclGuardedOrRejected
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

/-- Contract (C3.2/C5.1 total-or-error): either every owning edge is released (child freed) or `.error`. -/
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

/-- Contract (C3.2): 2 and 3 repeated owning edges are all released (or `.error`). -/
def repeatedEdgesReleased : Bool := ownEdgesContract 2 || ownEdgesContract 3

-- REGRESSION(rc_repeated_owning_edges_released)
-- Holds since #280: dropping the parent releases every one of its 2 (resp. 3) owning edges.
#guard repeatedEdgesReleased

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
-- Holds since #280: the release recurses through the parent and frees the grandchild.
#guard recursiveReleaseBeyondParent

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
-- Holds since #280: the buffer owned through a ctor field is released through `decRefBuf`.
#guard sarrayEdgeReleased
-- non-vacuity: a direct `decRef` of the same buffer does free it
#guard match heapWithBuf.decRefBuf 3 1 with | .ok st => (st.findBuffer 3).isNone | .error _ => false

-- REGRESSION(incref_freed_is_error)
-- C3.3: `incRef` on a freed object is `.useAfterFree` (release path: `decRef x0 1; incRef x0 1`).
#guard match run (heapWithChild 1) (.decRef 0 1 (.incRef 0 1 retZero)) with
  | .error (.useAfterFree 1) => true
  | _ => false

/-- Contract (C3.4 / C5.1): the P-cert C3 reproducer (100 owning edges) frees the child or is `.error`. -/
def pcertC3Released : Bool := ownEdgesContract 100

-- REGRESSION(c3_100_owning_edges)
-- Holds since #280: P-cert C3 frees the child (before #280 `main` left childRc=100; #277 left childRc=65).
#guard pcertC3Released

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

/-- `x1 := allocCtor 0 [x24] []; ret x1`, where `x24 ↦ .tuple [.u64 0, .objPtr childId]` is an explicitly
    malformed field value: a tuple that owns an edge (C5.2). -/
def allocMalformedField : Except UBError (Val × HeapState) :=
  run (heapWithChild 1) (.letBind 1 .objPtr (.allocCtor 0 [malformedVar] []) (.ret 1))

/-- Contract (C5.2): `allocCtor` rejects an `objFields` entry that is a tuple owning an edge, with `typeError`. -/
def nestedTupleOwnershipRejected : Bool :=
  match allocMalformedField with
  | .error (.typeError _) => true
  | _ => false

-- REGRESSION(wf_objFields_no_nested_tuple_ownership)
-- XFAIL(heapobj-contract): flips in 5b — `main`'s `allocCtor` accepts the owning tuple and stores it as a field
-- of a fresh heap object instead of rejecting it.
#guard !nestedTupleOwnershipRejected
/-- info: ok LeanNative.Semantics.Val.objPtr 2 -/
#guard_msgs in
#eval IO.println (showRes allocMalformedField)

/-- `x1 := allocCtor 0 [x0] []; x2 := allocCtor 0 [x1] []; x3 := x2.obj[0]; x4 := x3.obj[0]; ret x4`: a ctor
    owning another ctor (valid nesting: on `main` the field is the inline ctor tuple, under 5b an `.objPtr`). -/
def validCtorNesting : Except UBError (Val × HeapState) :=
  run (heapWithChild 1) (.letBind 1 .objPtr (.allocCtor 0 [0] []) (.letBind 2 .objPtr (.allocCtor 0 [1] [])
    (.letBind 3 .objPtr (.ctorGetObj 2 0) (.letBind 4 .objPtr (.ctorGetObj 3 0) (.ret 4)))))

-- REGRESSION(wf_objFields_ctor_nesting_accepted)
-- C5.2: ctor-to-ctor nesting is well-formed; it is accepted and the grandchild edge reads back.
#guard retVal? validCtorNesting == some (.objPtr childId)

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
-- Holds since #280 at every evaluator fuel in `0..64`: `.error`, or `.ok` with the child freed.
#guard chainReleaseTotalOrError

-- UNCOVERED(C5.1-fuelExhausted-ctor): `main` (#280) releases recursively, but `UBError` has no `fuelExhausted`
-- constructor and `decRefObjFuel 0 st _ _ = .ok st`, so there is no distinguished exhaustion error to assert; on
-- well-formed heaps `decRefObj`'s fuel (`|heapObjs| + 1`) covers the release depth. The counting rule is pinned by
-- `fuel_bound_boundary`; 5b adds `.fuelExhausted` and its regression.
-- UNCOVERED(C5.4-underfueled-helper): `main`'s `decRefObjFuel` (#280) returns a partial `.ok st` at fuel 0 (no
-- `fuelExhausted` constructor exists); `decRefValsFuel` does not exist. 5b adds the regression "underfuelled call
-- ⇒ `.error .fuelExhausted`, never partial `.ok`".

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
-- Holds since #280: `isExclusive` on a heap object with `rc == 2` is `false`.
#guard isExclusiveSharedFalse

/-- `x1 := allocCtor 0 [x0] [x20]; decRef x1 1; x3 := op; ret x3`: `op` on a freed object. -/
def onFreedCtor (op : LNIRExpr) : Except UBError (Val × HeapState) :=
  run (heapWithChild 1) (.letBind 1 .objPtr (.allocCtor 0 [0] [20]) (.decRef 1 1 (.letBind 3 .unit op (.ret 3))))

/-- Contract (C4.1): `isExclusive` on a freed object is `.useAfterFree`. -/
def isExclusiveFreedIsUAF : Bool := isUseAfterFree (onFreedCtor (.isExclusive 1))

-- REGRESSION(isExclusive_freed_is_error)
-- Holds since #280: C4.1, `isExclusive` on a freed object is `.useAfterFree`.
#guard isExclusiveFreedIsUAF

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
-- Holds since #280 (`writeHeapObjFieldExclusive`): a shared `ctor_set` is exactly `nonExclusiveWrite`.
#guard ctorSetSharedIsUB

-- REGRESSION(ctor_set_exclusive_ok)
-- Holds since #280: an exclusive (`rc == 1`) `ctor_set` succeeds and updates field 0.
#guard ctorSetExclusiveUpdates

/-- Contract (C4.2 shared `del`): `rc == 2` ⇒ exactly `.nonExclusiveWrite`. -/
def delSharedIsUB : Bool := isNonExclusiveWrite (withCtor 1 (.call "lean_native_del_obj" [1] .unit))

-- REGRESSION(del_shared_is_ub)
-- XFAIL(heapobj-contract): flips in 5b — `lean_native_del_obj` is not an LNIR operation on `main`.
#guard !delSharedIsUB
/-- info: error LeanNative.Semantics.UBError.unsupportedCall "lean_native_del_obj" -/
#guard_msgs in
#eval IO.println (showRes (withCtor 1 (.call "lean_native_del_obj" [1] .unit)))

/-- `x1 := allocCtor 0 [x0] [x20]; x3 := del x1; ret x1` (exclusive, `rc x1 == 1`). -/
def delExclusive : Except UBError (Val × HeapState) :=
  run (heapWithChild 1) (.letBind 1 .objPtr (.allocCtor 0 [0] [20])
    (.letBind 3 .unit (.call "lean_native_del_obj" [1] .unit) (.ret 1)))

/-- Contract (C4.2 `del`, LCNF `Code.del` / `lean_del_object`): an exclusive `del` succeeds, frees the shell
    (`rc o == 0`) and does **not** release its fields: the child it owned keeps `rc == 1`. -/
def delExclusivePreservesFields : Bool :=
  match delExclusive with
  | .ok (.objPtr o, st) => o != childId && st.getObjRefCount o == 0 && st.getObjRefCount childId == 1
  | _ => false

-- REGRESSION(del_exclusive_preserves_fields)
-- XFAIL(heapobj-contract): flips in 5b — `lean_native_del_obj` is not an LNIR operation on `main`.
#guard !delExclusivePreservesFields
/-- info: error LeanNative.Semantics.UBError.unsupportedCall "lean_native_del_obj" -/
#guard_msgs in
#eval IO.println (showRes delExclusive)

/-- `ctor_set x1[x25 = 5] := x21` on the exclusive `x1 := allocCtor 0 [x0] [x20]` (only 1 object slot). -/
def ctorSetOOB : Except UBError (Val × HeapState) := withCtor 0 (.call "lean_native_ctor_set" [1, idxFive, 21] .unit)

/-- Contract (C4.2): an exclusive `ctor_set` at an index outside `objFields` is `outOfBounds 5 1`. -/
def ctorSetOOBIsError : Bool :=
  match ctorSetOOB with
  | .error (.outOfBounds 5 1) => true
  | _ => false

-- REGRESSION(ctor_set_out_of_bounds_is_error)
-- XFAIL(heapobj-contract): flips in 5b — `main` bounds the index by the flat field list (`objFields ++
-- scalarFields`, length 2), not by `objFields` (length 1).
#guard !ctorSetOOBIsError
/-- info: error LeanNative.Semantics.UBError.outOfBounds 5 2 -/
#guard_msgs in
#eval IO.println (showRes ctorSetOOB)

/-- `ctor_set x1[x22 = 0] := x24` with `x24 ↦ .tuple [.u64 0, .objPtr child]` on an exclusive ctor. -/
def ctorSetMalformed : Except UBError (Val × HeapState) :=
  withCtor 0 (.call "lean_native_ctor_set" [1, idxZero, malformedVar] .unit)

/-- Contract (C5.2 via C4.2): `ctor_set` of a nested owning tuple into an object slot is `typeError`. -/
def ctorSetNestedTupleRejected : Bool :=
  match ctorSetMalformed with
  | .error (.typeError _) => true
  | _ => false

-- REGRESSION(ctor_set_nested_tuple_ownership_rejected)
-- XFAIL(heapobj-contract): flips in 5b — `main`'s `ctor_set` accepts the owning tuple and writes it in place.
#guard !ctorSetNestedTupleRejected
/-- info: ok LeanNative.Semantics.Val.unit -/
#guard_msgs in
#eval IO.println (showRes ctorSetMalformed)

-- UNCOVERED(C4.2-uset-sset): `main` has no scalar-slot `ctor_set` (`uset`/`sset`) call name, so scalar-slot
-- bounds and exclusivity cannot be exercised.
-- UNCOVERED(C4.2-setTag): `main` has no `setTag` / `lean_ctor_set_tag` operation and no call name for it;
-- 5b adds it with the same exclusive / shared / freed regressions as `ctor_set`.

/-- Contract (C4.2 freed): `ctor_set` and `del` on a freed object are `.useAfterFree` (not
    `nonExclusiveWrite`, not `unsupportedCall`). -/
def freedMutationIsUAF : Bool :=
  isUseAfterFree (onFreedCtor ctorSet) && isUseAfterFree (onFreedCtor (.call "lean_native_del_obj" [1] .unit))

-- REGRESSION(mutation_freed_is_error)
-- XFAIL(heapobj-contract): flips in 5b — `ctor_set` on a freed object is already `useAfterFree` (#280), but
-- `lean_native_del_obj` does not exist on `main` (`unsupportedCall`).
#guard !freedMutationIsUAF
/-- info: error LeanNative.Semantics.UBError.useAfterFree 2 | error LeanNative.Semantics.UBError.unsupportedCall "lean_native_del_obj" -/
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

/-- Contract (C6.1): a decl longer than the symbolic fuel is not validated (`passed = false`). -/
def symtvFuelExhaustionFailsClosed : Bool :=
  !(validateTranslationDecl (scalarDecl "long" (longBody 300)) (scalarDecl "long" (longBody 300))).passed

-- REGRESSION(symtv_fuel_exhaustion_fails_closed)
-- XFAIL(heapobj-contract): flips in 5b — `symExecCode` silently returns `.unit` at fuel 0 and the
-- identical-but-unexplored decls pass.
#guard !symtvFuelExhaustionFailsClosed

/-- Contract (C6.2): dropping an owned `decRef` (a leak) does not validate (`passed = false`). -/
def symtvRcEffectsFailClosed : Bool :=
  !(validateTranslationDecl
    { name := "drop", params := [objParam, { id := 1, name := "x", ty := .i64 }], retTy := .i64, body := .decRef 0 1 (.ret 1) }
    { name := "drop", params := [objParam, { id := 1, name := "x", ty := .i64 }], retTy := .i64, body := .ret 1 }).passed

-- REGRESSION(symtv_rc_effects_fail_closed)
-- Holds since #280: the validator tracks RC effects, so dropping an owned `decRef` (a leak) does not validate.
#guard symtvRcEffectsFailClosed

/-- `x1 := x0 * 64; x2 := parFor (len x1) [x0]; ret x0`. Calibrated against the validator's concrete fuel floor
    (`checkDeclConcreteRefinement` evaluates at `Nat.max fuel 256`): at fuel 256 the `parFor` budget is exhausted
    on the samples with `64 · x0 > 256` and evaluation succeeds otherwise. -/
def fuelHungry : LNIRDecl :=
  scalarDecl "fh" (.letBind 1 .i64 (.scalar (.binOp .mul (.var 0) (.constU64 64)))
    (.parFor 2 1 [0] .i64 (.mapScaleAdd 1 0) (.ret 0)))

/-- Concrete evaluation of the *source* at evaluator fuel `fuel` on sample `i`. -/
def fuelHungrySample (fuel i : Nat) : Except UBError (Val × HeapState) :=
  let (env, st) := buildDeclSample fuelHungry i
  evalCode fuel env st fuelHungry.body

/-- Number of the 64 concrete samples on which the source exhausts evaluator fuel at the validator's floor 256:
    `.error` at fuel 256 but `.ok` at ample fuel, so the error is fuel exhaustion and not UB of the program.
    Defined behaviourally, independent of the constructor that reports it (`main`: `.outOfBounds len 256`;
    5b: `.fuelExhausted`, pinned below). -/
def fuelHungryExhausted : Nat :=
  ((List.range 64).filter fun i =>
    (fuelHungrySample 256 i matches .error _) && (fuelHungrySample 65536 i matches .ok _)).length

/-- Contract (C6.3): a decl whose source exhausts evaluator fuel on some sample does not validate. -/
def symtvSourceFuelExhaustionFailsClosed : Bool := !(validateTranslationDecl fuelHungry fuelHungry).passed

-- REGRESSION(symtv_source_fuel_exhaustion_fails_closed)
-- XFAIL(heapobj-contract): flips in 5b — C6.3: samples where the source exhausts evaluator fuel (at the
-- validator's floor 256) are counted as "source UB" (vacuous), so the decl still passes. The contract requires
-- `passed = false`. The pin shows that `main` reports the exhaustion as `.outOfBounds 320 256`; on flip it becomes
-- the distinguished `.fuelExhausted` (5b).
#guard !symtvSourceFuelExhaustionFailsClosed
#guard fuelHungryExhausted > 0
/-- info: error LeanNative.Semantics.UBError.outOfBounds 320 256 -/
#guard_msgs in
#eval IO.println (showRes (fuelHungrySample 256 0))

-- UNCOVERED(C6.3-rc-exhaustion-sample): `main`'s `evalCode` has no RC/heap-exhaustion error (#280's release
-- returns `.ok` when its fuel runs out), so no concrete sample can produce one; 5b adds it with `fuelExhausted`.

end LeanNative.Tests.HeapObjContract
