# HeapObj Contract (D1 step 5a)

Status: **normative** for every Stage 1D heap-object change (the 5b unification of #277 and #280 and
anything after it). Source decision: `mission/specs:specs/D1-heapobj-decision.md` (quorum round 2,
option 5); evidence: `mission/specs:specs/P-cert-summary.md` (P-cert v3, findings C1–C5).

This contract describes the semantics that LNIR heap objects **must** have. It does not change the model.
Clauses are checked by named regressions in
[`lean/LeanNative/Tests/HeapObjContract.lean`](../lean/LeanNative/Tests/HeapObjContract.lean) (§8). Not every
clause is covered: sub-clauses that no behaviour on `main` can exercise are listed explicitly as **UNCOVERED**
(§8, "UNCOVERED clauses") with the reason, and are not counted as checked. That module
is built by `lake build` (it is part of the `LeanNative` library glob), and `scripts/ci_verify.sh` checks
that it stays in sync with the table in §8.

`main` (as of this PR) has no Stage 1D heap: `allocCtor` evaluates to the flat immediate tuple
`.tuple (tag :: objFields ++ scalarFields)`, `decRefObj` never visits children, and there is no
`ctor_set` or `del` operation. Clauses that `main` violates are recorded as explicit **expected failures**
(§8, column "today"). 5b must flip every one of them.

## Terminology

| Term | Meaning |
|---|---|
| `HeapObj` | `{ id, tag, objFields : List Val, scalarFields : List Val }`. This is #277's split model, which 5b adopts. #280's flat `fields` is replaced. |
| owning edge | One entry of `objFields` that holds an `.objPtr c`. A parent holds one reference to `c` per entry. |
| `rc o` | `HeapState.getObjRefCount o`. `0` means freed or unknown. |
| exclusive | `rc o == 1` on a live heap object (Lean's `lean_is_exclusive`). See "Model vs. runtime" below. |
| tagged immediate | A `tobject` whose physical representation is an in-pointer `lean_box(n)` (low bit set), not a heap pointer. Which abstract values are tagged immediates depends on their type (§C2.1). |
| abstract scalar | A semantic `Val` (`.u64`, `.bool`, `.unit`). It carries no representation. `boxScalar`/`unboxScalar` are the identity on it, for every width and value, including `v ≥ 2^63`. |

### Model vs. runtime

The model's `rc` and exclusivity are abstractions of the Lean 4.35.0 runtime (`lean.h`), not copies of it:

* **`rc == 0`.** In the model, `rc o == 0` means freed (or never allocated), and every access is `useAfterFree`.
  In the runtime, `m_rc == 0` is a **live persistent** object (compacted region / `lean_mark_persistent`), and
  `m_rc < 0` is multi-threaded. Model objects are always single-threaded and never persistent. 5b must not lower
  "`rc o == 0` ⇒ error" into a runtime `m_rc == 0` check.
* **`lean_is_exclusive` is heap-only.** It is `lean_is_st(o) && o->m_rc == 1` and dereferences `o`. Its callers
  (LCNF `LetValue.isShared` → `!lean_is_exclusive`, and `LetValue.reset` in `EmitC`) only apply it to heap pointers. A persistent object (`m_rc == 0`) reports *not*
  exclusive, so it is copied, never mutated in place.
* **`isExclusive` of an immediate = `true` is an LNIR extension.** Lean never calls `lean_is_exclusive` on a
  `lean_box(n)` (it would crash). LNIR defines it as `true` (§C2.2) so that `isExclusive` is total on `tobject`.
  The emitter must realise this as the immediate branch of the C2.3 guard, never as a load.

## C1. Layout indexing

1. `allocCtor tag objFields scalarFields` allocates one `HeapObj` with `rc = 1`. **Exception (fieldless
   ctor):** when `objFields = scalarFields = []` (more generally, `getCtorLayout` reports
   `size = usize = ssize = 0`), nothing is allocated. The result is the immediate `.tuple [.u64 tag]`
   (`lean_box(tag)`, §C2.1), which has no `rc` entry and is not a `HeapObj`. The two field lists are
   **separate index spaces**:
   * `ctorGetObj o i` reads `objFields[i]`. If `i ≥ |objFields|` the result is `.error (.outOfBounds i |objFields|)`.
     It never reads a scalar slot.
   * `ctorGetScalar o i ty` reads `scalarFields[i]`. If `i ≥ |scalarFields|` the result is `.error (.outOfBounds …)`.
     Index `i` never counts object slots.
   * Reading through a freed object (`rc o == 0`) is `.error (.useAfterFree o)`.
2. Mapping to the Lean runtime (`lean.h`, `getCtorLayout`, v4.35.0). A ctor with `n` object slots,
   `u` `usize` slots and scalar area `ssize` is laid out as `[n × lean_object*][u × size_t][scalars]`.
   Each non-`usize` scalar field `i` sits at byte offset `off_i` relative to the end of the `usize` area
   (Lean assigns wider scalars lower offsets).
   * `ctorGetObj o i` ⇔ `lean_ctor_get(o, i)` (LCNF `LetValue.oproj i`), for `0 ≤ i < n`.
   * `scalarFields` order is the `usize` slots first, then the scalar fields **sorted by ascending byte offset
     `off_i`**. This is not `getCtorLayout`'s list order: `getCtorLayout` returns fields in declaration order,
     each tagged with its `off_i`. The lowering sorts by `off_i`.
     * For `i < u`: `ctorGetScalar o i .usize` ⇔ `lean_ctor_get_usize(o, n + i)` (LCNF `LetValue.uproj (n+i)`).
     * Otherwise, `ctorGetScalar o i ty` ⇔ `lean_ctor_get_uint{8,16,32,64}` / `_float` / `_float32` at byte offset
       `sizeof(void*) * (n + u) + off_i` (LCNF `LetValue.sproj (n+u) off_i`). `ty` must equal the slot's IR type.
   * The lowering must take `n`, `u` and `off_i` from `Lean.Compiler.LCNF.getCtorLayout`. It must not guess
     them from `numFields`. (#277's `getRcCtorLayoutSpecM` does this; 5b keeps it.)
3. `LNIR` never addresses a ctor field through a flat `objFields ++ scalarFields` index.

## C2. Tagged immediates

1. Representation. The abstract value and its physical representation are separate. The semantics
   (`boxScalar`, `unboxScalar`, `lean_native_box_u64`) treats boxing as the identity on the abstract scalar.
   The emitter must pick the physical box from the **type**, exactly as Lean 4.35.0 does
   (`ImpureType.Lean.Expr.boxOpName` in `LCNF/EmitC.lean`; `lean.h`):

   | Lean type | LNIR type | box op | physical representation (64-bit) |
   |---|---|---|---|
   | `Bool`, `UInt8`, `UInt16` (and any enum-like ctor) | `i1`, `i8`, `i16` | `lean_box` | in-pointer tagged immediate |
   | `UInt32` | `i32` | `lean_box_uint32` | in-pointer tagged immediate (heap ctor on 32-bit targets) |
   | `UInt64` | `i64` | `lean_box_uint64` | heap scalar object: `lean_alloc_ctor(0, 0, 8)`, `rc = 1` |
   | `USize` | `usize` | `lean_box_usize` | heap scalar object: `lean_alloc_ctor(0, 0, sizeof(size_t))` |
   | `Float` | `f64` | `lean_box_float` | heap scalar object: `lean_alloc_ctor(0, 0, 8)` |
   | `Float32` | `f32` | `lean_box_float32` | heap scalar object: `lean_alloc_ctor(0, 0, 4)` |

   * In-pointer payload range: `lean_box(n) = (n << 1) | 1` is only defined for
     `0 ≤ n ≤ LEAN_MAX_SMALL_NAT = SIZE_MAX >> 1` (`2^63 − 1` on 64-bit). Every type in the `lean_box` rows has
     values `< 2^32`, so they always fit. A `UInt64`/`USize` value `≥ 2^63` does **not** fit. Boxing it in-pointer
     drops bit 63 (`lean_unbox(lean_box(2^63)) = 0`). This is why those types use a heap cell.
   * A heap scalar object is an ordinary ctor with `objFields = []` and one scalar slot. It has an `rc`, takes part in
     RC, and is never a tagged immediate.
   * A nullary ctor with tag `t` (more generally, any ctor whose `getCtorLayout` has `size = usize = ssize = 0`)
     is `lean_box(t)`. It is never `null` and never a heap allocation. In the semantics it is an immediate
     (`.tuple [.u64 t]`). It has no `rc` entry (see §C1.1 for the fieldless-ctor exception).
   * `UInt64`/`USize`/`Float` **fields** of a ctor are never boxed. They live unboxed in `scalarFields`.
   * `main`'s LLVM backend lowers every `boxScalar`/`lean_native_box_u64` to the in-pointer `shl 1 | 1`, whatever the
   type. That is correct for `i1/i8/i16/i32` and wrong for `i64`/`usize` values `≥ 2^63` and for `f64`/`f32`
   (xfails `codegen_box_u64_high_bit`, `codegen_box_usize_heap`, `codegen_box_float_heap`,
   `codegen_box_float32_heap`).
2. Semantics: `incRef`/`decRef` on an immediate is a no-op `ok` that leaves the state unchanged.
   `isExclusive` on an immediate is `true`.
3. Codegen obligations. Before any access to `m_rc`, `m_tag` or a field of a `tobject`, emitted code must test
   `ptr == null` and `(ptrtoint ptr) & 1`, and take the immediate path when either holds. This covers:
   * RC inc/dec. This is already done inline (`rc_tagged`) and in the `lean_native_inc`/`lean_native_dec` helpers.
   * `isExclusive`. Today this is a direct `load i32` (P-cert C5, xfail).
   * tag reads (`lean_native_ctor_tag`) and field projections on `taggedPtr`.

   A backend that cannot emit the check must reject the declaration (`findUnsupportedLLVMCallInCode` returns `some`
   for any `objPtr`/`taggedPtr` decl it cannot lower, C5 in 5b). It must not emit untagged loads.

   The codegen regressions check this **structurally**, not by substring. `IRCheck.guardedDerefs` splits the
   emitted function into basic blocks. For every `load`/`store`/`atomicrmw`/`getelementptr` whose address is the
   object pointer (or a reload of its slot), it requires that every CFG path from `entry` to that block crosses
   the non-null edge of `icmp eq ptr P, null` **and** the untagged edge of `(ptrtoint P) & 1`. The check is
   non-vacuous: at least one dereference must exist. It also self-tests on a guarded and an unguarded snippet.

   The boxing and projection regressions are **positive** dataflow checks, not "absence of the wrong pattern".
   They follow every returned value back through slot reloads, `phi` operands and value-preserving casts to its
   origins, and require every origin to be of the right kind:
   * `IRCheck.heapBoxCarries`: each origin is `call @lean_box_{uint64,usize,float,float32}(…)` on an argument
     carrying the boxed parameter, or a `lean_alloc_*` call into which the parameter is stored
     (`store`/`getelementptr` on the result, or `lean_ctor_set_*`). `IRCheck.inPtrBoxCarries`: each origin is
     `inttoptr ((x << 1) | 1)` of the parameter.
   * `IRCheck.projectionLoadsField`: each origin is a `load` from a `getelementptr` on the object pointer at the
     byte offset of the field (`8 + 8·i` for `lean_ctor_get(o, i)`), in a block behind the null/tag guard.

   Both have negative self-tests on hand-written wrong IR, which they must reject: `ret ptr null`, the in-pointer
   form, a box of a constant, an allocation without a store of the value, a `phi` that may yield `null`, no `ret`;
   for projections, a pointer copy, a guarded GEP with no load, wrong offsets (`0`, `16`), an unreturned load,
   an unguarded load, `ret ptr null`, and a `phi` joining the field with the raw pointer.

## C3. Owning-edge multiplicity

1. Each occurrence of `.objPtr c` in `objFields` is one owned reference. `allocCtor` consumes the caller's references.
   A ctor holding `c` `k` times accounts for exactly `k` units of `rc c`.
2. When a parent's `rc` reaches `0`, its object is freed and **every** owning edge is released. That means exactly `k`
   decrements of `c` for `k` edges, recursively. Each decrement that reaches `0` frees that child in turn.
   Scalars and immediates in fields are skipped. `.sarrayId` edges use `decRefBuf`.
3. `decRef o k` with `k > rc o`, or with `rc o == 0`, is `.error (.useAfterFree o)`. `incRef` on a freed object is the same.
4. The P-cert C3 reproducer is normative. Take a parent with 100 owning edges to one child, where the child has
   `rc = 100` from those edges alone. `decRef parent 1` must either free the child (`rc child = 0`) or return `.error`.
   It must never return `ok` with the child still live. #277 returned `ok` with child `rc = 65`.

## C4. Exclusivity

1. `isExclusive o` on a live heap object is `rc o == 1`. On a freed object it is `.error (.useAfterFree o)`.
2. In-place mutation is allowed **only** when `rc o == 1`:
   * `lean_native_ctor_set o i v`: field update / Perceus reuse (#280). In LCNF this is `Code.oset` (and
     `Code.uset`/`Code.sset` for scalar slots). `ExpandResetReuse` produces these on the fast path of the
     `LetValue.reset`/`LetValue.reuse` pair, behind a `LetValue.isShared` test;
   * `lean_native_del_obj o`: free the shell without releasing its fields (#277 `delObjShell`). In LCNF this is
     `Code.del` (`EmitC`: `lean_del_object`). Contrast `Code.dec`, which is `lean_dec`/`lean_dec_ref` and releases
     fields recursively (C3.2);
   * any future `Code.setTag` (`lean_ctor_set_tag`).

   If `rc o ≥ 2`, the operation is `.error (.nonExclusiveWrite o)`. If `rc o == 0`, it is `.error (.useAfterFree o)`.
   An index outside `objFields` (respectively `scalarFields`) is `.error (.outOfBounds …)`.
   Shared mutation is UB in the semantics and is never a silent copy.
3. `main` lacks both operations: `lean_native_ctor_set` and `lean_native_del_obj` evaluate to `unsupportedCall`.
   The xfail stubs in §8 name them, and 5b activates them.

## C5. `decRef` is total-or-error

1. Recursive release is fuel-bounded, because a `HeapState` heap is acyclic but has unbounded depth. The result is
   either the **complete** release or an explicit `.error`. If fuel runs out, the result is `.error`. 5b must add
   `UBError.fuelExhausted` (or an equivalent distinguished constructor) and return it.
   Returning `.ok` with a partially released graph is forbidden. Both #277's `decRefValsFuel 0 _ (_ :: _) = .ok st`
   and #280's `decRefObjFuel 0 st _ _ = .ok st` violate this.
2. Well-formedness: **no nested tuple ownership.** Every entry of a heap object's `objFields` is either an owning
   edge (`.objPtr c`, `.sarrayId b`) or a non-owning immediate (a scalar, or a fieldless ctor `.tuple [.u64 t]`).
   A `.tuple` that contains an owning edge at any depth is ill-formed as a field. `allocCtor` (and `ctor_set`) must
   reject it with `.error (.typeError …)`. A ctor that owns another ctor holds it as `.objPtr`, never inline.
   This rule is what makes the bound below exact, because the release never recurses into tuples.
   (`main` violates it: its `allocCtor` accepts a variable bound to the malformed `.tuple [.u64 0, .objPtr c]`
   and embeds it inline. Xfail `wf_objFields_no_nested_tuple_ownership`. Valid ctor-to-ctor nesting stays accepted:
   `wf_objFields_ctor_nesting_accepted`.)
3. Fuel bound. One fuel unit is charged per `objFields` entry popped from the release worklist (owning or not,
   including the root edge of the `decRef`), plus one unit per object freed. Tuples are not traversed (by 2).
   Each object is freed at most once, so a complete release of any acyclic well-formed heap needs at most
   `B(heap) = 1 + Σ_{o ∈ heap} (1 + |o.objFields|)` units, with equality when every object is freed.
   `decRefObj` must supply at least `B(heap)`. With that bound, `.error .fuelExhausted` is unreachable on
   well-formed heaps and only signals a malformed heap (e.g. a cycle).
   The P-cert C3 shape needs `1 + (1 + 100) + (1 + 0) = 103` units.
   #277's `12 · |objects| + 12` (= 36) and #280's `|heapObjs| + 1` (= 3) are both below this bound.
   The executable reference `release` in the test module implements this counting. Regression
   `fuel_bound_boundary` checks that `B` units suffice and `B − 1` units give `fuelExhausted` on the C3, chain,
   diamond and mixed-field shapes.
4. Exposed helpers (`decRefObjFuel`, `decRefValsFuel`) carry the same total-or-error contract for **any** fuel
   argument, including underfueled calls.

## C6. SymbolicTV obligations

`validateTranslationDecl src tgt` must report `passed = false` whenever its analysis was incomplete for either side:

1. symbolic-execution fuel exhaustion (`symExecCode` at fuel `0`). Today this silently yields `.unit`;
2. RC/heap tracking exhaustion, such as #280's `updateRefCountFuel 0 … = markUnsupported` or heap-expansion depth.
   The same applies to any RC effect the symbolic model does not track. For example, a dropped `decRef` must not
   validate as equivalent;
3. any concrete sample whose `evalCode` returns a fuel or RC-exhaustion error on the source. That sample counts as
   non-vacuous failure, not as "source UB".

Exhaustion is never a vacuous pass.

## Out of scope for 5a

No change to `Semantics/Value.lean`, `Semantics/Eval.lean`, the bridge, the emitters or `SymbolicTV`.
5b owns all model and emitter work: the switch to `HeapObj { objFields, scalarFields }`, the `--allow-rc-adt`
fail-closed gates (C4/C5 of P-cert), the `getCtorLayout` scalar-slot lowering, and `del`/`setTag`/`ctor_set`.

## 8. Clause → regression table

All names refer to `-- REGRESSION(<name>)` markers in `lean/LeanNative/Tests/HeapObjContract.lean`.
**pass** means the regression is a positive `#guard` that holds on `main`. **XFAIL** means it carries
`-- XFAIL(heapobj-contract): flips in 5b` and asserts today's wrong behaviour: first `#guard !<pred>` (named in the
last column) on a contract predicate over the evaluator/emitter/validator, then optionally `#guard_msgs` pinning
today's output. When 5b fixes the defect, the xfail breaks the build until someone flips it.

| Clause | Regression | today | XFAIL expectation |
|---|---|---|---|
| C1.1 obj index space | `layout_ctorGetObj_indexes_objFields` | pass | — |
| C1.1 scalar index space | `layout_scalar_only_ctor_indexes_scalarFields` | pass | — |
| C1.1 scalar-slot indexing (mixed ctor) | `layout_scalar_slot_indexing` | XFAIL | `#guard !scalarSlotIndexing` |
| C1.1 obj index bounded by `objFields` | `layout_ctorGetObj_out_of_objFields_is_error` | XFAIL | `#guard !objIndexBounded` |
| C1.1 ctor with fields allocates a live `HeapObj`, `rc = 1` | `layout_alloc_live_rc_one` | XFAIL | `#guard !allocLiveRcOne` |
| C1.1 scalar index bounded by `scalarFields` | `layout_scalar_oob_is_error` | XFAIL | `#guard !scalarOOBBounded` |
| C1.1 reads of a freed object are `useAfterFree` | `layout_freed_read_is_error` | XFAIL | `#guard !freedReadsAreUAF` |
| C1.2 Lean runtime offsets | `layout_lean_runtime_offsets` | pass | — |
| C2.1 abstract boxing is identity incl. `2^63`; in-pointer range `[0, 2^63)` | `box_abstract_high_bit_roundtrip` | pass | — |
| C2.1 `i1/i8/i16/i32` boxed in-pointer (returns `lean_box(x)`) | `codegen_box_small_scalar_in_pointer` | pass | — |
| C2.1 `UInt64` boxed as heap scalar carrying the value (`2^63` regression) | `codegen_box_u64_high_bit` | XFAIL | `#guard !u64BoxIsHeap` |
| C2.1 `USize` boxed as heap scalar carrying the value | `codegen_box_usize_heap` | XFAIL | `#guard !usizeBoxIsHeap` |
| C2.1 `Float` boxed as heap scalar carrying the value | `codegen_box_float_heap` | XFAIL | `#guard !floatBoxIsHeap` |
| C2.1 `Float32` boxed as heap scalar carrying the value | `codegen_box_float32_heap` | XFAIL | `#guard !float32BoxIsHeap` |
| C2.2 RC on immediates is a no-op | `tagged_immediate_rc_noop` | pass | — |
| C2.2 `isExclusive` immediate | `tagged_immediate_isExclusive_true` | pass | — |
| C2.1 nullary ctor is immediate | `nullary_ctor_is_immediate` | pass | — |
| C2.3 RC codegen checks tag bit | `codegen_rc_checks_tag_bit` | pass | — |
| C2.3 `isExclusive` codegen checks tag bit (P-cert C5) | `codegen_isExclusive_checks_tag_bit` | XFAIL | `#guard !isExclusiveCodegenTagChecked` |
| C2.3 projection returns a guarded load from `P + 8 + 8·i` (structural) | `codegen_projection_guarded_field_load` | XFAIL | `#guard !projectionGuardedLoad` |
| C2.3 fallback: tag reads with no lowering are rejected | `codegen_tag_read_rejected` | pass | — |
| C2.3 fallback: a decl with an unguarded dereference is rejected | `codegen_unguarded_decl_rejected` | XFAIL | `#guard !isxDeclGuardedOrRejected` |
| C2.1 nullary ctor emitted as `lean_box(t)` | `codegen_nullary_ctor_boxed` | XFAIL | `#guard !nullaryCtorCodegenBoxed` |
| C3.3 RC arithmetic over repeated decrements | `rc_repeated_edges_arith` | pass | — |
| C3.3 freed / underflow is error | `decref_freed_or_underflow_is_error` | pass | — |
| C3.2 repeated owning edges released | `rc_repeated_owning_edges_released` | XFAIL | `#guard !repeatedEdgesReleased` |
| C3.2 release recurses beyond parent/leaf (grandchild) | `rc_recursive_release_grandchild` | XFAIL | `#guard !recursiveReleaseBeyondParent` |
| C3.2 `.sarrayId` owning edge released via `decRefBuf` | `rc_sarray_edge_released` | XFAIL | `#guard !sarrayEdgeReleased` |
| C3.3 `incRef` on a freed object is `useAfterFree` | `incref_freed_is_error` | pass | — |
| C3.4 / C5.1 P-cert C3 reproducer (100 edges) | `c3_100_owning_edges` | XFAIL | `#guard !pcertC3Released` |
| C5.3 fuel bound `B` exact (`B` ok, `B − 1` exhausts) on C3/chain/diamond/mixed | `fuel_bound_boundary` | pass | — |
| C5.2 nested tuple ownership is ill-formed (`allocCtor` of a malformed `.tuple [.u64 0, .objPtr c]` field is `typeError`) | `wf_objFields_no_nested_tuple_ownership` | XFAIL | `#guard !nestedTupleOwnershipRejected` |
| C5.2 ctor-to-ctor nesting is well-formed and accepted | `wf_objFields_ctor_nesting_accepted` | pass | — |
| C5.1 release path total-or-error (chain, every evaluator fuel 0..64) | `decref_chain_total_or_error` | XFAIL | `#guard !chainReleaseTotalOrError` |
| C4.2 shared write is UB (sarray precedent) | `exclusive_write_sarray_shared_is_ub` | pass | — |
| C4.1 `isExclusive` of shared object is false | `isExclusive_shared_obj_false` | XFAIL | `#guard !isExclusiveSharedFalse` |
| C4.1 `isExclusive` of a freed object is `useAfterFree` | `isExclusive_freed_is_error` | XFAIL | `#guard !isExclusiveFreedIsUAF` |
| C4.2 shared `ctor_set` is UB | `ctor_set_shared_is_ub` | XFAIL | `#guard !ctorSetSharedIsUB` |
| C4.2 exclusive `ctor_set` succeeds | `ctor_set_exclusive_ok` | XFAIL | `#guard !ctorSetExclusiveUpdates` |
| C4.2 shared `del` is UB | `del_shared_is_ub` | XFAIL | `#guard !delSharedIsUB` |
| C4.2 `ctor_set` / `del` on a freed object is `useAfterFree` | `mutation_freed_is_error` | XFAIL | `#guard !freedMutationIsUAF` |
| C4.2 exclusive `del` frees the shell and preserves references owned by its fields | `del_exclusive_preserves_fields` | XFAIL | `#guard !delExclusivePreservesFields` |
| C4.2 out-of-bounds `ctor_set` is `outOfBounds i (length objFields)` | `ctor_set_out_of_bounds_is_error` | XFAIL | `#guard !ctorSetOOBIsError` |
| C5.2 via C4.2 `ctor_set` of a nested owning tuple is `typeError` | `ctor_set_nested_tuple_ownership_rejected` | XFAIL | `#guard !ctorSetNestedTupleRejected` |
| C6 rejects wrong result | `symtv_rejects_wrong_result` | pass | — |
| C6.1 fuel exhaustion ⇒ `passed = false` | `symtv_fuel_exhaustion_fails_closed` | XFAIL | `#guard !symtvFuelExhaustionFailsClosed` |
| C6.2 untracked RC effects ⇒ `passed = false` | `symtv_rc_effects_fail_closed` | XFAIL | `#guard !symtvRcEffectsFailClosed` |
| C6.3 source evaluator-fuel exhaustion counts as failure, not source UB | `symtv_source_fuel_exhaustion_fails_closed` | XFAIL | `#guard !symtvSourceFuelExhaustionFailsClosed` |

To flip an xfail in 5b:
1. Replace `#guard !p` with `#guard p`.
2. Replace each pinned `#guard_msgs` output with the contract output, or delete it.
3. Remove the `XFAIL` marker.
4. Change "today" to **pass** and the expectation column to `—` in this table.

`ci_verify.sh` validates each XFAIL as a structured executable expectation. It fails if:
* the table and the module disagree on the set of names, on which names are XFAIL, or on the
  "XFAIL expectation" column;
* an XFAIL's first command is not `#guard !<pred>`, or `<pred>` is not a module `def <pred> : Bool := …` with a
  `/-- Contract … -/` docstring, or its body is a constant, or it does not reach (through the module's own defs)
  one of `evalCode`, `evalExpr`, the `HeapState` RC/write operations, `emitDeclLLVM`,
  `emitRuntimeAndCAbiHelpers`, `findUnsupportedLLVMCallInCode`, `validateTranslationDecl` or `getCtorLayout`;
* any line of the module is a trivial guard (`#guard true`, `#guard !false`, …);
* a regression has no `#guard`/`#guard_msgs` at all.

Before checking the module, the script runs a self-test that feeds it malformed XFAILs (`#guard true`,
`#guard !false`, a constant predicate, a predicate that touches no evaluator, a positive `#guard pred`, an undefined
predicate, a predicate without a `Contract` docstring, a regression without a guard). Each must be rejected.

### UNCOVERED clauses

Some clauses have no behaviour on `main` that a regression can observe, because the operation, helper or code path
does not exist yet. Such a clause is listed here and marked `-- UNCOVERED(<id>)` in the module, together with
the reason. Nothing here is counted as covered. 5b must replace each entry with a regression in the table above.
`ci_verify.sh` fails if this list and the module's `UNCOVERED` markers disagree.

| UNCOVERED id | Why no regression on `main` |
|---|---|
| `C5.1-fuelExhausted-ctor` | `main` has no recursive release, so no input reaches fuel exhaustion; the counting rule is pinned by `fuel_bound_boundary`. |
| `C5.4-underfueled-helper` | `decRefObjFuel` / `decRefValsFuel` do not exist on `main`. |
| `C1.2-scalar-lowering` | `main`'s emitter has no `getCtorLayout`-driven `lean_ctor_get_usize`/`_uintN` lowering; only the Lean layout itself is pinned (`layout_lean_runtime_offsets`). |
| `C4.2-uset-sset` | `main` has no scalar-slot `ctor_set` (`uset`/`sset`) call name, so scalar-slot bounds and exclusivity cannot be exercised. |
| `C4.2-setTag` | `main` has no `setTag` / `lean_ctor_set_tag` operation or call name, so there is nothing to call. |
| `C6.3-rc-exhaustion-sample` | `main`'s `evalCode` has no RC/heap-exhaustion error (no recursive release), so no concrete sample can produce one. |
