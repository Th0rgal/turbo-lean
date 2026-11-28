# H3.2 / H3.3 runtime objects: architecture spec (`docs/H3_RUNTIME_OBJECTS.md`)

> **Purpose**: the decision record for how `LNIR` represents Lean runtime objects (`Nat`, `String`,
> `Array`/`HashMap`, closures and partial applications, the `IO` world token), where the trusted base
> stops for each, and the acceptance gate of every H3.2/H3.3 leaf PR. It is the design input to the H3
> step "runtime objects (`Nat`, `Array`, `String`, external `Init` calls), where the trusted base is
> really decided; closures and partial application; `IO`" (`roadmap/HORIZONS.md`, "H3 — Later").
>
> **Status**: proposed. It changes no theorem contract in `roadmap/VALIDATION_CONTRACTS.md`, no line of
> `docs/TRUSTED_BASE.md` and no row of `roadmap/HORIZONS.md`. §7 lists the trusted-base entries this
> design adds. They are to be merged into `docs/TRUSTED_BASE.md` §7 by the first leaf that lands code
> (H3.2-0), not here.
>
> **Provenance** (2026-11-28):
> - Code facts are from `main` at `e7097d6e`.
> - Census facts are from `benchmarks/h3_con_leche_census.json` (PR `#509`, scope `exe_closure`,
>   `leanprover/con-leche@501589f5`, `leanprover/lean4:v4.35.0`).
> - Runtime ABI facts are from the pinned toolchain's `include/lean/lean.h` and `src/lean/Init/**`, and
>   from `lean -c` output for a probe file (§1.3).
> - Every claim cites a file and line, or the command that shows it.

---

## 0. Decisions at a glance

| Family | `LNIRType` | `Val` / heap model | Proved in Lean | Trusted C ABI (shim → `lean.h`) | Leaves |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `Nat` | `.taggedPtr` (unchanged) | **new** `Val.nat : Nat → Val`, width-free, non-owning, RC no-op | lowering; `rt` entry = `Nat.*` Lean definition (`rfl` laws); RC no-op is sound because no `lean_nat_*` mutates in place | `lean_nat_{add,sub,mul,div,mod,dec_eq,dec_lt,dec_le}`, `lean_uint64_of_nat`, `lean_usize_of_nat`, `lean_uint64_to_nat`, `lean_usize_to_nat`; GMP | H3.2-N1, N2 |
| `String` | `.objPtr` | `HeapObj` with **new** `kind := .string`, `scalarFields = [.str s]` (**new** non-owning payload `Val.str : String → Val`) | lowering; RC/ownership per signature table; `rt` entry = Lean definition where one exists | `lean_mk_string_unchecked`/static literal, `lean_string_{append,push,length,utf8_byte_size,dec_eq,dec_lt,utf8_get,utf8_next,utf8_extract}`; `lean_string_hash` (**opaque oracle**) | H3.2-S1, S2 |
| `Array` (objects) | `.objPtr` (**fixes** today's `.sarray α`) | `HeapObj` with `kind := .array`, elements = `objFields` (owning edges) | lowering; copy-on-write = `lean_ensure_exclusive_array`; release via existing `decRefValsFuel` | `lean_mk_empty_array`, `lean_array_{get_size,fget,get_borrowed,fset,set,push}`, `lean_copy_expand_array` | H3.2-A1 |
| `HashMap`/`HashSet` | none of its own | ordinary Lean code over A1 + recursive inductives (H3.1) + `hash` | the same as any user code (L2/L3 calls) | none beyond A1, S1 (`lean_string_hash`), N2 | H3.2-A2 |
| external `Init` calls | — | closed `RuntimeTable` (§2.2) | classification is total and fail-closed | only names in `RuntimeTable` | H3.2-X |
| Closures / PAP | `.objPtr` | `HeapObj` with `kind := .closure`, `scalarFields = [.fnRef sym, .u64 arity]`, `objFields` = fixed args; **new** `Val.fnRef : String → Val` | lowering of `LetValue.pap` / `.fvar` application; `applyClosure` model; `___boxed` wrapper refines its native function | `lean_alloc_closure`, `lean_closure_set`, `lean_apply_1`…`lean_apply_16`, `lean_apply_n` / `lean_apply_m` (refused in C1) | H3.3-C1, C2 |
| `IO` world | `.unit` (erased) | `EST.Out` = ordinary `.ctor` `HeapObj`; **new** `HeapState.world : WorldModel` | erasure of `Void σ`; `EST.Out` layout; `bind` sequencing | `lean_get_stdout` + stream closure, `lean_io_prim_handle_put_str`; all other IO prims `Unsupported` | H3.3-IO1, IO2 |

Each "new" item is an additive constructor or field with a default, so existing construction sites and
proofs need no change (§2.1). Everything outside the table returns `Unsupported` and goes to the stock
backend, per the H1 rule (`roadmap/HORIZONS.md`, H1: "what the proof does not cover returns
`Unsupported` and is compiled by the stock backend").

---

## 1. Ground truth

### 1.1 What `con-leche` needs (census, `exe_closure`)

1,875 computational declarations out of 3,691, in 124 modules and 56,202 lines. 21 are blocker-free.

| Blocker | Decls | Share | Subcategories (overlapping) | Consequence for this spec |
| :--- | ---: | ---: | :--- | :--- |
| `big_nat` | 1,753 | 93.5% | `nat_type_or_op` 855, `via_type` 1,647 | Most `Nat` is carried in structure fields (`with_nat_field` 95 types), so storing and passing must work before arithmetic does. N1 covers both. |
| `string` | 1,529 | 81.6% | `string` 115, `string_literal` 373, `char` 8, `via_type` 1,472 | Strings are mostly carried, through `ConLeche.Name`. S1 (literals, carry, `==`, `<`, `hash`, `append`) comes first; UTF-8 position ops (S2) come later. |
| `recursive_inductive` | 1,481 | 79.0% | `local` 969 (`ConLeche.{Expr,Level,Name}`), `core_list` 227, `via_type` 1,363 | Prerequisite H3.1 (PR `#508`, reset/reuse core calculus) plus the bridge. This spec assumes it and does not specify it. |
| `array_hashmap` | 1,005 | 53.6% | `array` 208, `byte_array` 185, `hash_map` 41, `hash_set` 7, `via_type` 821 | `ByteArray` is already `.sarray .i8` (`TypesAndSigs.lean:208`). `Array` of objects is the gap (§3.3). |
| `closure_pap` | 718 | 38.3% | `lambda` 383, `higher_order_binder` 193, `via_type` 326 | H3.3-C1/C2. |
| `external_init_call` | 251 | 13.4% | `Std` 53, `List` 44, `IO` 42, `Nat` 34, `USize` 32, `System` 19, `Array` 18, `Lean` 18, `String` 11, `Bool` 10, `Prod` 10, `ByteArray` 7 | A lower bound: dot calls are not resolved. H3.2-X classifies them. |
| `reset_reuse` | 201 | 10.7% | `match_and_rebuild` 199, `manual_exclusive` 2 | H3.1. The array copy-on-write (§3.3) uses the same exclusivity rule. |
| `io` | 86 | 4.6% | `IO` 53, `IO.FS` 13, `IO.Ref` 5, `IO.Promise` 2, `Elab.*` 4, `Std.Mutex`/`Std.Async`/`IO.Process` 1 each, `via_type` 62 | IO1/IO2 cover plain `IO` and stdout. `IO.Ref`, `IO.Promise`, `IO.FS`, `IO.Process`, `Std.Mutex`, `Std.Async` and `Elab` stay `Unsupported`. |

`categories_per_declaration` = `{0: 21, 1: 92, 2: 187, 3: 520, 4: 488, 5: 401, 6: 123, 7: 41, 8: 2}`.
So 1,854 of 1,875 (98.9%) hit at least one blocker and 1,055 (56.3%) hit four or more. **No single
family unlocks a large share on its own.** Leaves are therefore ranked by what they unblock for the
families after them, and each leaf is accepted on its own corpus, not on `con-leche` lowering counts.
The `con-leche` number is the H3 exit metric (§6), not a per-leaf gate.

### 1.2 What `main` has today (`e7097d6e`)

- `LNIRType` (`lean/LeanNative/IR/Types.lean:479`) has `objPtr`, `taggedPtr`, `sarray elem` and
  `rawPtr elem`. It has no string, closure or boxed-array type.
- `Val` (`lean/LeanNative/Semantics/Value.lean:10`) has nine constructors: `u64`, `u256`, `bool`,
  `tuple`, `objPtr`, `sarrayId`, `rawPtrId`, `storageMapId`, `unit`. It has no `Nat`, string or code
  pointer.
- `HeapObj` (`Value.lean:167`) is `{ id, tag, objFields, scalarFields }`. Release is
  `decRefValsFuel` (`Value.lean:392`), which is total-or-error (HEAPOBJ_CONTRACT C5).
- `evalExpr` refuses every extern call: `.call fnName args _retTy isExtern` → `if isExtern then .error
  (.unsupportedCall fnName)` (`lean/LeanNative/Semantics/Eval.lean:392-396`). Non-extern calls go
  through `FuncTable := String → Option FnSem` (`Eval.lean:219`). Ten runtime intrinsics are interpreted
  before that (`builtinCallNames`, `Eval.lean:222`).
- Type lowering (`lowerImpureType`, `lean/LeanNative/IR/BridgeHelpers/TypesAndSigs.lean:177`) maps
  `Nat ↦ .taggedPtr` (`:200`), `ByteArray ↦ .sarray .i8` (`:208`) and **`Array α ↦ .sarray (lower α)`**
  (`:210`). `validateSupportedTypeM` rejects runtime `Nat`, `tobject` and function types with
  `Unsupported` (`TypesAndSigs.lean:339-342`).
- **Finding.** `Array α ↦ .sarray _` is wrong for every `α`. In the runtime, `Array α` is always a
  `lean_array_object` (kind tag `LeanArray = 246`) of boxed `lean_object*` elements, even for
  `Array UInt64`. Only `ByteArray`/`FloatArray` are `LeanScalarArray = 248` (`lean.h:104,106`). An
  `Array`-typed value modelled as an `ArrayBuffer` of packed `UInt64` (`Value.lean:110`) has the wrong
  element layout. This document does not establish whether such a value can reach LLVM emission today.
  H3.2-A1 removes the mapping and adds a regression test (§3.3).
- Closures: `lean/LeanNative/IR/ClosureADT.lean` defunctionalizes *statically known* closures into
  `.allocCtor` plus tag dispatch (C8). It does not model the `lean_closure_object` runtime layout. It
  stays as an optimization for known closures (§3.5).

### 1.3 What the pinned runtime actually does (`v4.35.0`)

Facts from `include/lean/lean.h`:

- Object kinds:
  - `LeanMaxCtorTag 243`, `LeanClosure 245`, `LeanArray 246`, `LeanScalarArray 248`, `LeanString 249`,
    `LeanMPZ 250` (`lean.h:101-108`).
  - `LEAN_MAX_SMALL_NAT = SIZE_MAX >> 1` (`lean.h:1615`): `2^63 − 1` on LP64 and `2^31 − 1` on ILP32
    (`TargetArch.isILP32`).
  - `LEAN_CLOSURE_MAX_ARGS 16` (`lean.h:31`).
- Some ABI entry points are `static inline` and are **not linkable symbols**:
  - `lean_nat_add`, `lean_nat_sub`, `lean_nat_mul`, `lean_nat_div`, `lean_nat_mod`, `lean_nat_dec_*`
    (`lean.h:1658-1776`);
  - `lean_array_get_size`, `lean_array_fget`, `lean_array_get_borrowed`, `lean_array_fset`,
    `lean_array_set` (`lean.h:1058-1159`);
  - `lean_string_length`, `lean_string_utf8_byte_size`, `lean_string_dec_eq`, `lean_string_dec_lt`
    (`lean.h:1458-1504`);
  - `lean_alloc_closure`, `lean_closure_set` (`lean.h:957,971`);
  - `lean_io_result_mk_ok`, `lean_io_mk_world` (`lean.h:3168,3190`).

  Only `lean_nat_big_*`, `lean_array_push`, `lean_copy_expand_array`, `lean_string_{append,push,
  utf8_get,utf8_next,utf8_extract,lt,hash}` and `lean_apply_*` are `LEAN_EXPORT`.

Ownership, from `lean_obj_arg` (owned) vs `b_lean_obj_arg` (borrowed) in `lean.h`, matched by `@&` in
`Init`:

- `Nat.add : (@& Nat) → (@& Nat) → Nat` (`Init/Prelude.lean:1887`).
- `String.append : String → (@& String) → String` (`Init/Data/String/Defs.lean:93`).
- `Array.set! (xs : Array α) (i : @& Nat) (v : α)` (`Init/Data/Array/Set.lean:54`).
- `String.hash` is `opaque`, with no Lean body (`Init/Prelude.lean:4829`). So is
  `Array.get!InternalBorrowed` (`Prelude.lean:3456`).

Calling convention, from `lean -c` on a probe (`def hello (s : String) : IO Unit := IO.println (s ++
"!")`, `def mkAdder (k : Nat) : Nat → Nat := fun x => x + k`, an `Array.set!` use):

- The native `IO` function takes **no world argument**: `lean_object* l_hello(lean_object*)`.
- Its `l_hello___boxed(lean_object*, lean_object*)` takes and ignores the world.
- Through a closure, the world is passed as `lean_box(0)`: `lean_apply_2(putStr, s, lean_box(0))`, where
  `putStr` is field 4 of the `lean_get_stdout()` stream.
- `l_mkAdder___boxed` calls `l_mkAdder` and then `lean_dec`s both args. The native function borrows them
  (inferred), and the boxed wrapper owns them.
- `Array.set!` lowers to `lean_array_set` and `a[i]!` to `lean_array_get_borrowed`. Both are
  `static inline`.
- `EST ε σ α := Void σ → EST.Out ε σ α`, with `EST.Out.ok : α → Void σ → _` and `.error : ε → Void σ → _`
  (`Init/System/ST.lean:68-76`). `Void σ` is erased, so `ok a` is ctor 0 with one object field, which is
  exactly `lean_io_result_mk_ok` (`lean_alloc_ctor(0, 1, 0)`, `lean.h:3190`).

---

## 2. Cross-cutting design

### 2.1 One object model: `HeapObj.kind`

All runtime objects except `Nat` are `HeapObj`s, distinguished by a new field:

```lean
inductive ObjKind where | ctor | closure | array | string
  deriving Repr, DecidableEq, Inhabited, BEq
def ObjKind.leanTag : ObjKind → Option Nat   -- lean.h m_tag of the kind
  | .ctor => none | .closure => some 245 | .array => some 246 | .string => some 249

structure HeapObj where
  id : Nat; tag : Nat; objFields : List Val; scalarFields : List Val
  kind : ObjKind := .ctor          -- NEW, defaulted: every existing `{ id, tag, objFields, scalarFields }` is unchanged
```

```lean
inductive Val where
  | ... (nine existing constructors, unchanged)
  | nat   : Nat → Val      -- NEW (H3.2-N1)
  | str   : String → Val   -- NEW (H3.2-S1), payload only: appears only inside a `.string` object's scalarFields
  | fnRef : String → Val   -- NEW (H3.3-C1), payload only: the code symbol of a `.closure` object
```

Rules:

- **K1.** `Val.owns` is unchanged. `nat`, `str` and `fnRef` own nothing, so `decRefValsFuel` releases
  arrays and closures through `objFields` with no new code.
- **K2.** `lean_native_ctor_tag`, `ctorGetObj`, `ctorGetScalar`, `isExclusive` and reset/reuse accept only
  `kind = .ctor`. Any other kind is `.typeError`. A reuse token from a `.ctor` cell can never become an
  array or closure.
- **K3.** Each new `Val` constructor adds one arm to `Val.beq`, `HeapObj.decEqVal` (with its cross arms)
  and `beq_refl`.
  - `evalIncRef`/`evalDecRef` on `.nat` already take the `some _ => .ok st` branch, so they need no edit.
  - `.str`/`.fnRef` in an environment variable are a `.typeError` in every consuming position. Only
    `.objPtr` of the right kind is a string or closure value.
- **K4.** Model `rc` keeps the HEAPOBJ_CONTRACT "Model vs. runtime" caveat. A string literal or other
  closed constant evaluates to a fresh `rc = 1` object, while the runtime uses a persistent
  `m_rc = 0` static (probe: `l_hello___closed__0_value … .m_rc = 0`). Because every consumer of a
  persistent object copies and never mutates it, the two are observationally equal. The emitter must not
  turn model `rc` into an `m_rc` test.

### 2.2 External calls: a closed `RuntimeTable`

```lean
/-- Reference semantics of one Lean runtime entry point. -/
structure RuntimeEntry where
  sym   : String               -- the lean.h / Init @[extern] name, e.g. "lean_nat_add"
  shim  : String               -- linkable symbol the LLVM backend calls, e.g. "lean_native_rt_nat_add"
  sig   : List ArgMode × RetMode  -- ArgMode := owned | borrowed | scalar ty; RetMode := owned | scalar ty
  sem   : FnSem                -- List Val → HeapState → Except UBError (Val × HeapState)
abbrev RuntimeTable := String → Option RuntimeEntry
```

- **R1.** `evalExpr` handles `.call f args _ true` as `match rt f with | some e => e.sem vals st | none =>
  .error (.unsupportedCall f)`. The `RuntimeTable` is a new explicit argument next to `funcs`. The table
  is a single `def leanRuntimeTable` in a new `lean/LeanNative/Semantics/Runtime/` directory, with one
  file per family. `RealLCNFSemantics` consults **the same** `rt`. The bridge theorem becomes
  `lowerRealLCNFDecl_sound_rt (rt) …`, in the shape of `lowerRealLCNFDecl_sound`
  (`Proofs/RealLCNFBridgeProofs.lean:507`) with `rt` universally quantified. It is therefore relative to
  the runtime, by construction, and does not depend on any entry being correct.
- **R2.** The lowerer emits `isExtern := true` only for `sym ∈ leanRuntimeTable` (one decidable
  membership check). An `@[extern]`/`@[implemented_by]` callee outside the table is `Unsupported`.
- **R3. Ownership is in the table and is proved, not assumed.** For each entry, `sem` must:
  - consume each `owned` argument exactly once, by a `decRef` or by moving it into the result;
  - leave `borrowed` arguments' `rc` unchanged;
  - return a result with exactly one fresh reference.

  This is `theorem rt_respects_sig (e ∈ leanRuntimeTable)`. The lowerer's RC insertion reads `sig`, the
  same object, so the two cannot disagree.
- **R4. `sig` is checked against `lean.h` and `Init`.** `scripts/h3_runtime_sig_check.py` (H3.2-0)
  parses the pinned `lean.h` prototypes (`lean_obj_arg` / `b_lean_obj_arg` / `u_lean_obj_arg` / scalar)
  and the `@&` binders of the matching `Init` `@[extern]` declarations. It fails on any disagreement
  with the exported `sig` JSON (`lean-native runtime-table --json`). This takes signature agreement out
  of the trusted base.
- **R5. Shim.** The LLVM backend never calls a `lean.h` name directly, because the `static inline` ones
  have no symbol (§1.3). It calls `lean_native_rt_<name>`, defined once in
  `crates/turbo-lean/runtime/lean_native_rt.c` (H3.2-0). Each definition is one line that forwards to the
  `lean.h` function of the same name, compiled with `#include <lean/lean.h>` from the pinned toolchain.
  The shim is generated from the table (`lean-native runtime-table --emit-shim`) and is in the trusted
  base (§7, T2).
- **R6. Opaque entries.** Some entries have no Lean definition: `String.hash`, every IO primitive,
  `Array.get!InternalBorrowed`. Their `sem` is a field of an **oracle record** `RtOracle` that is passed to
  `leanRuntimeTable`, for example `hashStr : String → UInt64`. Theorems quantify over the oracle. The
  differential harness instantiates it by calling the real runtime through `@[extern]` from the Lean
  evaluator side. No law about an opaque entry is stated or assumed beyond determinism.

### 2.3 Assurance accounting

By the existing definition, `AssuranceLevel.unverifiedFallback` is "Uses external C/Rust FFI
(`@[extern]`)" (`Types.lean`, `AssuranceLevel`). A declaration whose body calls any `RuntimeTable` entry
is therefore `unverifiedFallback`, and this spec does not redefine that. Coverage reports add one
column, `proved_modulo_runtime`. It holds the declarations whose lowering is covered by
`lowerRealLCNFDecl_sound_rt` and that call only table entries, each listed in
`runtime_externs_assumed`. The H3 exit (§6) counts this column. It is never reported as L4.

### 2.4 Calling convention

- **CC1.** Each lowered decl `f` whose params are not all `owned`-boxed also gets `f___boxed`. In the
  boxed wrapper, every param is `lean_object*` and owned. It unboxes scalars, calls `f` and `decRef`s each
  param that `f` borrows. This matches the probe's `l_mkAdder___boxed`. The wrapper is ordinary `LNIRCode`
  and is proved by the existing call simulation (L2). Only a `___boxed` symbol may appear in `.fnRef`.
- **CC2.** IO decls take no world parameter natively. In `f___boxed`, the world is one extra `.unit`
  param that is ignored. At a closure call site, the world is the immediate `.tuple [.u64 0]`
  (`lean_box(0)`, HEAPOBJ C2.1).

---

## 3. Families

Each subsection gives the representation, the split between proved and trusted, and the leaves. The
gate template that every leaf instantiates is in §4.

### 3.1 `Nat` (93.5%)

**Representation.**
- `LNIRType.taggedPtr`, unchanged. `Val.nat n` for every `n`, with no small/big split in the model: the
  split is a runtime representation (`lean_box` iff `n ≤ LEAN_MAX_SMALL_NAT`, else `LeanMPZ`) that LNIR
  semantics does not observe.
- The type validation rejection of `Nat` (`TypesAndSigs.lean:341`) is lifted for `Nat` only.
- Literals: `LitValue.nat n` lowers to `.call "lean_native_rt_nat_lit" [] .taggedPtr true` when
  `n > LEAN_MAX_SMALL_NAT(arch)`, with `n` carried in the decl's constant pool. Otherwise it lowers to
  `boxScalar` of the `u64`.

**Proved in Lean.**
- Each `rt` entry is the `Init` definition:
  - `rt_nat_add : sem [.nat a, .nat b] st = .ok (.nat (a + b), st)`, and likewise `sub`
    (saturating: `a - b = 0` when `b > a`), `mul`, `div` (`n / 0 = 0`), `mod` (`n % 0 = n`),
    `dec_eq`/`dec_lt`/`dec_le` → `.bool`.
  - All are `rfl`/`simp` facts, which pin the model to `Nat`'s Lean definition.
- **RC is a no-op on `.nat`, and this is sound.** No `lean_nat_*` entry has a `u_lean_obj_arg` or tests
  exclusivity: all `Nat` arguments are `b_lean_obj_arg` (`lean.h:1658-1776`), so sharing is unobservable.
  The obligation is `theorem nat_entries_borrow_all : ∀ e ∈ natEntries, e.sig.1.all (· = .borrowed)`,
  checked against `lean.h` by R4.
- Lowering: `LetValue.fap Nat.add [a, b]` ↦ `.call "lean_nat_add" [a, b] .taggedPtr true`, covered by
  `lowerRealLCNFDecl_sound_rt`.

**Trusted** (§7 T1, T4):
- the small-nat fast paths of `lean.h` and `lean_nat_big_*` / `lean_nat_overflow_mul` on GMP agree with
  `Nat`;
- `lean_uint64_of_nat` is `n % 2^64` (big path `lean_uint64_of_big_nat`);
- `lean_usize_of_nat` is `n % 2^w`.

**Not covered in H3.2 (stays `Unsupported`).** `Nat.pow`, `Nat.log2`, `Nat.shiftLeft`/`shiftRight`,
`Nat.land`/`lor`/`xor`, `Nat.gcd`, `Nat.repr`. Each is one later table row with the same gate.

**Leaves.**
- **H3.2-N1 Nat core.** `Val.nat`; entries `add sub mul div mod dec_eq dec_lt dec_le`; literals; `Nat`
  fields in ctors.
  - Corpus: `tests/h3/nat_core.lean`, ≥ 40 decls. It must include the operand vectors
    `{0, 1, 2^63−2, 2^63−1, 2^63, 2^64−1, 2^64, 2^128+1, 10^40}` × the eight ops, so that every
    small→big and big→small transition is hit, plus `sub` underflow, `div`/`mod` by zero, and a structure
    with two `Nat` fields stored, projected and compared.
  - Mutants: `add→sub` in `rt_nat_add`; `sub` non-saturating; `div0 = 1`.
  - ILP32 leg: `wasm32` evaluator only, with vectors around `2^31`.
- **H3.2-N2 Nat conversions.** `lean_uint64_of_nat`, `lean_usize_of_nat`, `lean_uint64_to_nat`,
  `lean_usize_to_nat`; `Nat.toUInt64`, `UInt64.toNat`, `USize.ofNat`, `USize.toNat`.
  - These unblock `qualified:USize` (32) and the HashMap index (A2).
  - Vectors: `2^64 + 5` → `5`, and `2^64 − 1` round trip.
  - Mutant: `of_nat` saturating instead of wrapping.

### 3.2 `String` (81.6%)

**Representation.**
- `LNIRType.objPtr`. A string value is `.objPtr id`, with
  `HeapObj { kind := .string, tag := 0, objFields := [], scalarFields := [.str s] }`.
- `lowerImpureType` gains `String ↦ .objPtr` and `Char ↦ .i32`. `Char` is `uint32_t` in the ABI
  (`lean_string_push(lean_obj_arg, uint32_t)`, `lean.h:1456`).
- Literals become fresh `rc = 1` objects (K4). The LLVM side emits a persistent static `lean_string_object`
  with the probe's layout (`m_tag = 249`, `m_rc = 0`, `m_size`, `m_capacity`, `m_length`, `m_data`). The
  size and length fields come from a proved Lean function `utf8Layout : String → (size × length)`.

**Ownership.** Taken from `lean.h`:
- `append`: `(owned, borrowed) → owned` (`lean.h:1457`);
- `push`: `(owned, u32) → owned` (`:1456`);
- `length`, `utf8_byte_size`, `dec_eq`, `dec_lt`, `hash`: all borrowed;
- `utf8_get`: `(borrowed, borrowed Nat) → u32` (`:1461`);
- `utf8_next`: `(borrowed, borrowed) → owned Nat`;
- `utf8_extract`: `(borrowed, borrowed, borrowed) → owned` (`:1479,1494`).

**Proved in Lean.**
- Each non-opaque entry equals its `Init` definition on `.str` payloads: `String.append`, `String.push`,
  `String.length`, `String.utf8ByteSize`, `==`, `<`, `String.Pos.Raw.get`, `.next`, `String.extract`.
- `rt_respects_sig` for the `owned` first argument of `append`/`push`. In the model, `rc = 1` mutates the
  payload in place and `rc > 1` copies: inc nothing, dec the source once, allocate a fresh object. This
  mirrors `lean_string_append`'s exclusivity check without trusting it.
- `utf8Layout` matches `String.utf8ByteSize` and `String.length`.

**Trusted.**
- The C implementations agree with the `Init` definitions on valid UTF-8 (T1).
- `lean_string_hash` is an opaque oracle (R6). No law is stated, so `HashMap` correctness never depends
  on a hash law, only on determinism.

**Leaves.**
- **H3.2-S1 String carry + compare + build.** Covers: kind `.string`; `Val.str`; literals (static emit);
  `append`, `push`, `length`, `utf8_byte_size`, `dec_eq`, `dec_lt`, `hash`; `String` fields in ctors (the
  `Name` shape).
  - Corpus: `tests/h3/string_core.lean`, ≥ 40 decls. It must include `""`, ASCII, 2-, 3- and 4-byte
    UTF-8 code points, a 1 MiB built string (push loop, which exercises in-place growth when exclusive),
    an `append` on a shared string (the copy path, with `rc = 2` forced by keeping the original live),
    lexicographic `<` on common prefixes, and `hash` of equal strings built two ways.
  - Mutants: `append` ignores exclusivity (mutates a shared string); `dec_lt` on byte length;
    `utf8Layout` length = byte size.
- **H3.2-S2 UTF-8 positions.** `utf8_get`, `utf8_next`, `utf8_extract`; `String.Pos.Raw` as
  `.taggedPtr` `Nat`.
  - Vectors: positions inside a multi-byte code point (the runtime returns `default`/rounds; the
    reference is the `Init` definition), past-the-end, `extract` with `b > e`.
  - Mutant: `next` += 1 byte instead of the code-point width.

### 3.3 `Array` (objects) and `HashMap` (53.6%)

**Representation.**
- `LNIRType.objPtr`. An array value is `.objPtr id`, with
  `HeapObj { kind := .array, tag := 0, objFields := elems, scalarFields := [] }`.
- `lowerImpureType` line `:210` becomes `Array _ ↦ .objPtr`. `ByteArray`/`FloatArray` stay `.sarray`.
- Elements are owning edges when they are `.objPtr` and immediates otherwise (`.nat`, boxed scalars as
  `.u64` per HEAPOBJ C2). C3 multiplicity holds as is: an array holding the same object twice holds two
  references.

**Ownership** (`lean.h:1058-1198`):
- `get_size`, `fget`, `get_borrowed` borrow the array and the index. `fget` returns an **owned** element
  (an inc of the field). `get_borrowed` returns a borrowed one, and the lowerer must not `decRef` it.
- `fset`/`set` take `(owned arr, borrowed idx, owned val) → owned`;
- `push` takes `(owned, owned) → owned`.

**Copy-on-write model.**
`arrayEnsureExclusive st a`: when `rc a = 1`, it is `a`. Otherwise it allocates `a'` with the same
`objFields`, `incRef`s each owning element once, and `decRef`s `a` once. This is
`lean_ensure_exclusive_array` / `lean_copy_expand_array` (`lean.h:1120-1125`). `fset` is
`ensureExclusive` followed by an in-place slot write. The old element is released through
`decRefValsFuel`.

- Out of bounds: `fset` with `h : i < size` cannot fail. `set!` out of bounds returns the array unchanged
  (the `Init` definition). `get!` out of bounds returns the `Inhabited` default and **does not** model
  the runtime's `lean_panic_fn` message. `panic` output is excluded from the differential comparison.
  Only the value is compared.

**Proved in Lean.**
- Each entry equals the `Init` `Array` definition (`Array.set`, `Array.push`, `Array.size`,
  `Array.getInternal`) on the element list.
- `rt_respects_sig`.
- `arrayEnsureExclusive` preserves the C3 owning-edge count of every object other than `a`.
- Release of an array releases each element exactly once (an instance of C5 totality).

**HashMap / HashSet.**
- No dedicated runtime. `Std.HashMap` is Lean code over `Array` of `AssocList` buckets (recursive
  inductive, H3.1), a `Nat` size, `USize` indexing and `Hashable.hash`.
- A2 adds **no** table entries beyond A1 + N2 + S1 (`lean_string_hash`) and, if a decl calls it,
  `lean_hashmap_mk_idx` (`lean.h:3418`, `(owned Nat, u64) → usize`).
- Correctness is the L2/L3 call proofs applied to `Std` code that lowers through this path.

**Leaves.**
- **H3.2-A1 Object arrays.** Covers: kind `.array`; entries `mk_empty_array`, `get_size`, `fget`,
  `get_borrowed`, `fset`, `set`, `push`, `copy_expand_array`; the `:210` fix.
  - Regression `array_uint64_is_boxed`: lowering `def f (a : Array UInt64) : UInt64 := a[0]!` must
    produce `.objPtr`-typed `a`, never `.sarray`.
  - Corpus: `tests/h3/array_core.lean`, ≥ 40 decls. It must include an exclusive `set` loop (in place,
    which LSan proves leak-free), a shared `set` (copy; the original is unchanged and observed after),
    `push` past capacity, `Array (Array Nat)` nested release, `Array String`, an array holding one object
    twice, and `get!` out of bounds on `Array Nat`.
  - Mutants: `fset` skips `ensureExclusive`; `fget` returns borrowed (missing inc, so ASan
    heap-use-after-free); copy forgets element inc.
- **H3.2-A2 HashMap/HashSet.** Corpus: `tests/h3/hashmap_core.lean`, ≥ 20 decls.
  - Keys `Nat`, `String`, `UInt64`. Covers `insert`, `get?`, `contains`, `erase`, `fold`, and resize past
    the initial bucket count. It includes a `HashMap String Nat` keyed by `Name`-like strings.
  - Mutant: bucket index ignores the high hash bits (still correct: the differential must **agree**, as a
    test that the oracle carries no law); `insert` drops the size increment (must be killed).

### 3.4 External `Init` calls (13.4%)

**H3.2-X Init call classification.**
- For every constant `c` called from a decl that the lowerer sees, the lowerer computes `initClass c ∈`:
  - `{tableEntry, leanBody, unsupported}`.
  - `tableEntry` iff `c` has `@[extern sym]` with `sym ∈ leanRuntimeTable`.
  - `leanBody` iff `c` has no `@[extern]`/`@[implemented_by]` and its LCNF lowers through the proved
    path. It is then compiled **by this compiler** as an ordinary L2/L3 callee in the same module, not
    linked to the stock `libInit` symbol `l_<c>`.
  - `unsupported` otherwise: the caller is `Unsupported`.
- Linking the stock `libInit` `l_<c>` would put Lean's own code generator in the trusted base. That is a
  separate, opt-in fallback, `stock_init_link`, with assurance `unverifiedFallback`. It is **not** part of
  H3.2.
- Gate:
  - `lean-native eval-lcnf --json` on `tests/h3/init_calls.lean` (≥ 1 decl per census qualifier: `Std`,
    `List`, `Nat`, `USize`, `Array`, `String`, `Bool`, `Prod`, `ByteArray`) gives `mismatch_count == 0`.
  - A generated `benchmarks/h3_init_call_classes.json` lists `{c, class, reason}` for every `Init`
    constant reachable from `con-leche` `exe_closure`, with no entry missing (schema check).
- Mutant: `initClass` returns `leanBody` for an `@[implemented_by]` constant (must be killed by a
  differential vector where the two bodies differ, e.g. `Array.foldl` / `implemented_by` loop).

### 3.5 Closures and partial application (38.3%)

**Representation.**
- `LNIRType.objPtr`. A closure value is `.objPtr id`, with
  `HeapObj { kind := .closure, tag := 0, objFields := fixed, scalarFields := [.fnRef sym, .u64 arity] }`.
  Here `sym` is a `___boxed` symbol (CC1) and `fixed.length < arity ≤ 16`.
- Function types are lifted from the `validateSupportedTypeM` rejection (`TypesAndSigs.lean:341`).
- `LetValue.pap f args` ↦ `.call "lean_native_rt_alloc_closure" …` followed by `closure_set` of each
  arg.
- `LetValue.fvar g args` (applying an unknown function value) ↦ `.call "lean_apply_<n>" (g :: args)
  .objPtr true` for `1 ≤ n ≤ 16`.
- Known closures keep `ClosureADT.specializeKnownClosure`. The proof obligation is that the specialized
  direct call refines `applyClosure` on the allocated closure.

**Apply model** (`applyClosure fuel funcs rt st c args`, Lean, total-or-error). Let `k = fixed.length`,
`a = arity`, `n = args.length`, all args owned, `c` owned.
- `k + n < a`: allocate a new closure with `fixed ++ args`, `incRef` each `fixed` owning edge, and
  `decRef c`.
- `k + n = a`: `incRef` each `fixed` owning edge, `decRef c`, then call `funcs sym (fixed ++ args)`.
  The callee is a `___boxed` wrapper, which owns all args.
- `k + n > a`: saturate with the first `a − k` args as above, then `applyClosure` the result to the
  remaining args. This uses one fuel unit, and a non-closure result is `.typeError`.

**Proved in Lean.**
- Lowering of `pap`/`fvar`-application.
- `applyClosure` respects ownership (each arg consumed once, `c` consumed once).
- `___boxed` wrapper refinement (CC1).
- `specializeKnownClosure` refinement.
- `applyClosure` with `k + n = a` and `fixed = []` equals a direct call. This lemma links H3.3 to L2.

**Trusted** (T1): `lean_apply_<n>` dispatch in `libleanrt` implements `applyClosure`, including the
under- and over-application split. `lean_alloc_closure` / `lean_closure_set` layout (inline, through the
shim).

**Leaves.**
- **H3.3-C1 Exact-arity closures.**
  - Covers: kind `.closure`; `Val.fnRef`; `___boxed` emission; `alloc_closure`, `closure_set`,
    `apply_1`…`apply_16` restricted to `k + n = a`. Every other case is `Unsupported` at lowering when
    `k`, `n` and `a` are static. When they are not static, the model's `applyClosure` still handles all
    cases. Arity above 16 is `Unsupported`.
  - Corpus: `tests/h3/closure_exact.lean`, ≥ 30 decls. It must include a closure capturing a `Nat`, a
    `String` and an `Array`; `List.map`/`Array.map` with a lambda; a closure stored in a structure field
    and applied twice (shared, `rc = 2`); a closure over a borrowed param (the boxed wrapper must `dec`);
    and arity 16.
  - Mutants: boxed wrapper omits the `dec` of a borrowed param (LSan leak); `applyClosure` forgets the
    `fixed` inc (ASan UAF on the shared closure).
- **H3.3-C2 Partial and over-application.** Removes the `k + n = a` restriction. Adds `lean_apply_n` /
  `lean_apply_m` for `n > 16` only if the corpus needs it; otherwise they stay `Unsupported`.
  - Corpus: `tests/h3/closure_pap.lean`, ≥ 30 decls. It must include a curried 3-arg function applied
    1+1+1, 2+1 and 1+2; over-application returning a closure (`fun x => fun y => …` applied to 2 args);
    and a PAP of a PAP.
  - Mutant: under-application appends args before `fixed`.

### 3.6 `IO` world token (4.6%)

**Representation.**
- `IO.RealWorld` / `Void σ` ↦ `.unit` (`lowerImpureType` already maps `lcVoid ↦ .unit`,
  `TypesAndSigs.lean`). It is erased from native signatures (CC2).
- `EST.Out.ok a` / `.error e` are ordinary `.ctor` `HeapObj`s: tag 0 or 1, one object field (§1.3). They
  need no new kind.
- New field `HeapState.world : WorldModel := {}`, with
  `structure WorldModel where stdout : ByteArray := .empty; stderr : ByteArray := .empty`.
  Additive and defaulted, like `storageMaps`.

**Entries.**
- `lean_get_stdout : () → owned FS.Stream`. The stream is a `.ctor` object whose field 4 (`putStr`,
  as the probe shows) is a `.closure` over the `___boxed` symbol `lean_native_rt_stdout_put_str`.
- That symbol appends the UTF-8 bytes of its string argument to `world.stdout` and returns
  `EST.Out.ok ()`.
- `lean_io_prim_handle_put_str : (borrowed Handle, borrowed String) → owned EST.Out` only for
  the stdout/stderr handles. Any other handle is `.unsupportedCall`.
- Through the closure path, IO1 depends on C1.

**Proved in Lean.**
- Erasure: a decl with a `Void σ` param lowers to a native signature without it, and its `___boxed`
  wrapper ignores it (CC1/CC2).
- The `EST.Out` layout equals `lean_io_result_mk_ok`/`mk_error` (ctor tag, one field).
- `bind` sequencing: `world.stdout` after `a >>= b` = after `a`, then after `b`. This follows from
  ordinary ANF order in `evalCode`, so there is no new proof machinery.

**Trusted** (T5): `libleanrt`'s stdout stream writes exactly the bytes it is given, with no
reordering, through `fwrite`/libuv. Buffering and flush timing are outside the model. The differential
compares the full stdout after exit.

**Out of scope (`Unsupported`).** `IO.Ref` (`ST.Ref`, `lean_st_ref_*`), `IO.Promise`, `IO.FS` beyond
stdout/stderr, `IO.Process`, `Std.Mutex`, `Std.Async`, every `Elab.*` monad, `IO.monoNanosNow`
(nondeterministic), `IO.getRandomBytes`. Their direct census subcategories sum to 27 of the 86 IO decls
(13 + 5 + 4 + 2 + 1 + 1 + 1, overlapping). Each is a later table row with its own world-model field.

**Leaves.**
- **H3.3-IO1 Stdout IO.** Covers the world erasure, `EST.Out`, `lean_get_stdout`, `IO.print`/`println`,
  and `main : IO Unit` / `IO UInt32` exit code.
  - Corpus: `tests/h3/io_stdout.lean`, ≥ 15 decls/executables. It must include `println` in a
    `for … in` loop over an `Array String`, non-ASCII output, and a 1 MiB output.
  - Mutant: two `println`s swapped in the lowering of `bind` (must be killed: stdout differs).
- **H3.3-IO2 IO errors.** Covers `EST.Out.error`, `throw (IO.userError s)`, `try … catch`, and
  `main` returning an error (exit code 1, message on stderr).
  - Corpus: `tests/h3/io_error.lean`, ≥ 10 decls.
  - Mutant: `catch` drops the error payload.

---

## 4. Leaf acceptance gate (template)

Every leaf above is one PR and is accepted only when **all** of G1–G6 hold at the PR's head SHA.
Leaf-specific corpora, vectors and mutants are given in §3.

| # | Gate | Command | Pass condition |
| :- | :--- | :--- | :--- |
| G1 | Build + axioms | `lake build` (in `lean/`) and `lean-native audit-axioms --json` | Build green. No new axiom; 0 `sorryAx` in `Proofs/H3/**` and `Semantics/Runtime/**`. Every theorem named in the leaf's §3 entry exists. |
| G2 | Source differential | `lean-native eval-lcnf --json --fuel 65536 tests/h3/<leaf>.lean` | `mismatch_count == 0`; `compared_count ≥` the corpus floor in §3; no decl tagged `-- @h3-target` in `skipped_names_by_reason`. `RealLCNFSemantics` + `leanRuntimeTable` agree with Lean's compiled evaluator. |
| G3 | Native differential | `python3 scripts/h3_runtime_diff.py --leaf <id> --json` (H3.2-0) | Per corpus file: Lean reference `lean -c` + `leanc` vs `lean-native build-exe` linked with `lean_native_rt.c` and the pinned `libleanrt`, built with `clang -O1 -fsanitize=address,undefined -fno-omit-frame-pointer`, `ASAN_OPTIONS=detect_leaks=1`. JSON `{leaf, compared_count, mismatch_count, asan_errors, ubsan_errors, lsan_leaks, mutants_total, mutants_killed}` with `mismatch_count = asan_errors = ubsan_errors = lsan_leaks = 0`. Byte-identical stdout and identical exit code. |
| G4 | Model vs native | the same script, `--leg lnir` | For each `@h3-target` decl, `evalCode` (LNIR, with the oracle instantiated by the real runtime) agrees with the native run on every vector. This closes the gap between the proved model and the emitted code that G2 alone does not test. |
| G5 | Mutants | the same script, `--mutants` | `mutants_killed == mutants_total`. Each mutant listed in §3 is killed by G2, G3 or G4 (or by a proof, recorded as a `*_killed` theorem in `Proofs/H3/`, as `Proofs/H1/` does). The one listed *must-agree* mutant (A2 bucket index) must **not** be killed. |
| G6 | Signatures + docs | `python3 scripts/h3_runtime_sig_check.py` (H3.2-0) and `python3 scripts/sync_docs_inventory.py --check` | 0 disagreements between `leanRuntimeTable.sig`, `lean.h` and `Init` `@&`. Docs inventory in sync. |

The CI wiring is one new fragment, `scripts/contract.d/36_h3_runtime_diff.sh`, which runs G3–G6 for
every leaf merged so far. It is added by H3.2-0 and extended one line per leaf.

### 4.1 H3.2-0 Runtime substrate (first leaf, no family)

- **Adds**:
  - `ObjKind` + `HeapObj.kind`, defaulted (§2.1);
  - the `RuntimeTable` / `RtOracle` plumbing through `evalExpr`, `evalCode` and `RealLCNFSemantics`, with
    an **empty** table (§2.2);
  - `lowerRealLCNFDecl_sound_rt`;
  - the shim generator, `lean-native runtime-table --json` / `--emit-shim`;
  - `scripts/h3_runtime_diff.py`, `scripts/h3_runtime_sig_check.py` and `contract.d/36`;
  - the §7 entries merged into `docs/TRUSTED_BASE.md` §7, once `#503`/`#506` have landed.
- **Acceptance**:
  - G1;
  - `lowerRealLCNFDecl_sound` is derivable from `lowerRealLCNFDecl_sound_rt` at the empty table (a
    theorem, so the H1 statement is not weakened);
  - the existing `SpecLocked.lean` hash and `35_h1_mutant_matrix.sh` are unchanged and green;
  - with an empty table, G2 on the existing H1 corpus gives the same `compared_count`/`mismatch_count` as
    on `main`;
  - `h3_runtime_diff.py --self-test` kills a planted mismatch, a planted ASan error and a planted leak.

---

## 5. Order and dependencies

```
H3.1 (#508 core calculus → bridge RC for recursive inductives)
  └─► H3.2-0 substrate ─┬─► N1 ─► N2 ─┐
                        ├─► S1 ─► S2  ├─► A2 HashMap ─┐
                        ├─► A1 ───────┘               ├─► H3.2-X Init classes
                        └─► C1 ─► C2                  │
                              └─► IO1 ─► IO2 ◄────────┘ (IO1 needs S1 + C1)
```

N1, S1, A1 and C1 are independent after H3.2-0 and can run in parallel, because each adds one `ObjKind`
or `Val` constructor and one table file. Every merge touches `Value.lean` and the shared `Val` instance
arms (K3). These conflicts are mechanical; resolve them by rebasing, not by merging the leaves.

## 6. H3.2/H3.3 exit

All leaves merged. Then `benchmarks/h3_con_leche_lowering.json` is generated, by lowering `con-leche`
`exe_closure` at the census pin. It reports:
- `computational = 1875`;
- `proved = ` the decls lowered through the proved path with no table entry;
- `proved_modulo_runtime` (§2.3);
- `unsupported_by_reason`.

It is ratcheted (non-decreasing) the same way as `H1_COVERAGE_RATCHET`. No target number is set here.
The census (§1.1) shows that the four-plus-blocker mass (1,055 decls) moves only once N1, S1, A1, C1 and
H3.1 have all landed, so an earlier target would be arbitrary.

## 7. Trusted-base entries this design adds (for `docs/TRUSTED_BASE.md` §7)

- **T1 Runtime entries.** For each `e ∈ leanRuntimeTable` with a Lean definition: the pinned `libleanrt`
  / `lean.h` implementation of `e.sym` computes `e.sem` on the stated domain. This is tested by G2–G4.
  It is not proved.
- **T2 Shim.** `lean_native_rt.c` forwards each call unchanged. It is generated, one line per entry, and
  compiled against the pinned `lean.h`.
- **T3 Signatures.** None. R4 checks them mechanically, which is why they are not trusted.
- **T4 GMP.** `lean_nat_big_*` and `LeanMPZ` arithmetic, through the GMP that the toolchain is built with.
- **T5 Opaque oracles.** `lean_string_hash`, `Array.get!InternalBorrowed` and the stdout stream. Only
  determinism is relied on. No algebraic law about an oracle appears in any theorem.
- **Unchanged.** Lean's kernel, the LLVM printer and LLVM (`docs/TRUSTED_BASE.md` §1, §5, §6). H3.2 adds
  no dependence on Lean's code generator, because `stock_init_link` (§3.4) is excluded.
