# BendRT Exploration Roadmap (`BRT0`–`BRT6`)

> **Status of this document: an exploratory proposal, not a locked contract.**
> Nothing here modifies [`GOALS.md`](./GOALS.md),
> [`VALIDATION_CONTRACTS.md`](./VALIDATION_CONTRACTS.md), or
> [`CONFORMANCE_SUITE.md`](./CONFORMANCE_SUITE.md). Items use the `BRT0`–`BRT6`
> prefix to stay disjoint from [`OPEN_CHALLENGES.md`](./OPEN_CHALLENGES.md)
> (`A1`–`A5`, `B1`–`B5`), CI shadow-semantics `Track B0`
> ([`docs/SHADOW_SEMANTICS.md`](../docs/SHADOW_SEMANTICS.md)), and emitter
> mutation gate `B-3`. Now that both `C1`–`C8` (`Lean 4 -> Target IR`,
> `#327`–`#338`) and Next-Gen `D0`–`D6` (`#345`–`#361`; see
> [`docs/BENCH_RUST_PARITY.md`](../docs/BENCH_RUST_PARITY.md)) plus the Stage
> 2/3 & M5 target bridges (`#381`, `#388`, `#394`–`#399`) are merged on `main`,
> this document specifies the concrete fragments of Bend 2's runtime and
> compiler (`bendlang/bend` `v2.0.39`) worth evaluating next—each with the exact
> assumption that makes it legal under `lean.h`
> ([`docs/HEAPOBJ_CONTRACT.md`](../docs/HEAPOBJ_CONTRACT.md)), its relationship
> to merged `D0`–`D6`, and the `Contract V1–V5` + Rule 7 (`ΔE2E >= 1%`) gates
> required to keep it.

## Why this exists

Bend 2 (`bendlang/bend`, `bend2/comp.ts` + `bend2/bend.ts`, `v2.0.39`) is a
whole-program compiler from an **affine** calculus (`BendTT`) to one C file that
compiles as the host runtime, the CPU worker pool, and the Metal/CUDA GPU kernel
at once (`BendRT`). Reading `comp.ts` directly (rather than the README) shows
that its runtime performance comes from five specific mechanisms:

1. **Layout by fixpoint, not by declaration (`lay_of` / `lay_pack`, `comp.ts:732–809`).**
   Every closed datatype gets a word layout over `"w32" | "w64" | "box"`: a
   `w32` tag word iff there is more than one constructor, then fields overlaid
   at the first word where they fit, widening `w32 < w64 < box`. Anything
   recursive, or wider than `WIDE = 247` words, collapses to one `box`. `Nat`
   is a bare `w64` immediate up to `2^48 − 1`.
2. **One 64-bit word for every value (`term_make`, `comp.ts:3819–3896`).**
   Values pack `tag:8 | aux:16 | loc:40`, with `RFC_BIT` at bit 63 across six
   tags (`PAK CTR CLO BUF TSK ARR`). A `PAK` carries its payload directly in
   `loc`, so `U32`, `F32`, `Bool`, and nullary/single-`w32` constructors occupy
   one register with zero heap traffic (`term_triv`). Heap nodes have no object
   header; only when a constructor crosses a duplication boundary does
   `rfc_wrap` allocate a 1-word redirect refcount cell `(loc << 24) | cnt`.
3. **Borrow vs. own and hotness decided by monotone fixpoint (`c_units` / `facts_hot` / `brw_of`, `comp.ts:1040–1045`, `1260–1342`, `2707–2718`).**
   `c_units` re-emits until `FL.facts` stops growing. Every `box` parameter
   starts optimistically borrowed; `fact_add("own")` flips it only if a
   reachable segment stores or returns it where it can outlive the frame (`lent`
   / `lends`, closed by `graph_close`). `brw_of` elides all refcount traffic on
   parameters that remain borrowed, while `sc.spares` (`comp.ts:869–874`,
   `1455–1459`) reuses freed size-class slots in place across tail arms.
4. **Functions are segments, and a tail call is a register-pinned jump (`WL_CASE` / `WL_JMP`, `comp.ts:2748–2774`, `3263–3268`, `4319–4350`).**
   On the host, every segment is a `preserve_none` function (with a dummy `rp`
   slot at argument 6 so `rax` stays free for the tail target) and `WL_JMP` is
   `__attribute__((musttail)) return`; `emit_body` inlines single-site callees.
   Even self-tail loops emit `musttail` rather than `for (;;)` because Clang
   hoists constants poorly across large loop-switch state machines. On the
   device, the same `WL_CASE` macros expand to `case` arms of one stackless
   `switch (fid)` inside `bend_dev`, backed by a strided explicit stack
   `sp[(long)I * CUBE]`.
5. **Dual-mode `seq` forks and fixed-geometry ring scheduling (`emit_fork` / `monk_step` / `bend_dev`, `comp.ts:2421–2490`, `4243–4608`).**
   A multi-binding `let` emits *dual-mode* code gated on `if (!seq)`: in
   parallel Grow mode (`seq == 0`), each binding becomes a `TAG_TSK` pushed into
   a per-lane ring (`CUBE_T = 128` lanes × `128` groups = `16,384` rings, with
   `ring_flip` transposing producer/consumer coordinates) and a join task whose
   `rem` counter decrements via `a32_sub_rel` (`task_deliver`). Once the
   frontier is full, workers flip to `seq == 1` and run the exact same code
   sequentially on the stack with zero task allocations. `fid_nofk` marks
   fork-free callees statically so Grow lanes run leaves inline, and `row_grow`
   waits `1 ms` on CPU before dealing work across rows.

None of these can be copied verbatim into `LeanNative`, and the reason is
structural: Lean 4 is **not affine**. Values are shared by default, `Nat` is
arbitrary-precision, constructors carry arbitrary scalar payloads, and the
runtime ABI (`lean.h`, [`docs/HEAPOBJ_CONTRACT.md`](../docs/HEAPOBJ_CONTRACT.md),
closed to `54/54 PASS` in `C6` `#331`) fixes heap layout for FFI with
`libleanshared`. This document therefore isolates the fragments of BendRT that
survive contact with Lean's ABI and extend merged `D0`–`D6` without violating any
`C1`–`C8` invariant.

## Alignment with Merged `C1`–`C8`, `D0`–`D6`, and Open Challenges

| Exploration Item | Builds on (`main`) | Relation to Merged `D0`–`D6` & Open Challenges | Core Mechanism |
| :--- | :--- | :--- | :--- |
| **`BRT0`: Tail-Segment & `JoinPoint` IR** | `C3` (`LLVMLower`), `C8` (`ClosureADT`), `D5` (`AsyncStateMachine.lean`, `#348`) | Post-`D5` generalization (`D5` lowered non-escaping `IO` coroutines as `.tuple [.i64, .i64, .i64]` loops over `seqFor`/`ite`) | Explicit `tailCall` + `JoinPoint` view over `LNIR` + multi-decl call-table semantics (`evalDeclEnv`) feeding CPU `musttail` and mutual-tail state machines. |
| **`BRT1`: Word-Resident Scalar/Enum Unboxing** | `C4` (`RealLCNFBridge`), `C6` (`HeapObj` `54/54` PASS), `BridgeHelpers.lean` | Extends `D0`/`D2` (`UnboxedRegion.lean`, `#347`) | Mechanical `getCtorLayout` predicate (`l.ctorInfo.size = 0 ∧ l.ctorInfo.usize = 0 ∧ l.ctorInfo.ssize ≤ 4` on 64-bit) packing multi-ctor small-scalar ADTs into tagged immediates (`0` heap allocs, `0` RC). |
| **`BRT2`: `musttail` + `preserve_nonecc` Lowering** | `C2`/`C3a` (`LLVMAst` + `LLVMLowerProofs`), `#381`/`#399` (`lean-mlir-bridge`), `BRT0` | Post-`D4`/`D5` CPU tail-call lowering (dependent on CPU `BRT0`, independent of GPU `D6`) | Lower internal `BRT0` tail-call SCCs in `LLVMAst` / `LLVM.lean` to `musttail call preserve_nonecc` for $O(1)$ stack depth and register-pinned state threading. |
| **`BRT3`: Interprocedural Borrow & Slot-Reuse Fixpoint** | `C6` (`HeapObjAbiProofs`), `D1` (`ProofRetention.lean`, `#352`), `D2` (`OwnershipRC.lean`, `#347`), `BRT0` | Directly extends `D2`'s `OwnershipRC.lean` + `D1` exclusivity | Greatest-fixpoint SCC borrow inference (`LNIRParam.borrow`) eliding `Val.objPtr` RC traffic on non-escaping parameters + `sc.spares`-style size-matched `HeapObj` constructor slot reuse. |
| **`BRT4`: Dual-Mode (`!seq`) Commuting Fork-Join** | `C7` (`Hybrid.lean`), `D2` (`SendableSlot` in `UnboxedRegion.lean`), `LeanSys.Par`, `BRT0`, `BRT3` | Post-`D2` CPU task-parallel runtime | Commutativity-checked (`PairwiseDisjointEffects ∧ AllCapturedSendable`) fork-join using Bend's `if (!seq)` saturation toggle, `fid_nofk` leaf inlining, and `1 ms` lazy steal window. |
| **`BRT5`: Multi-Region `parFor` GPU Turn Batching (Study)** | `C3b` (`PTX`/`Metal`), `C7` (`Hybrid`), `C8` (`KernelFusion`), `D4` (`CostAutotune.lean`, `#358`) | Uses `D4` autotuner; orthogonal to `D6` (`PTXAst` barrier generations, `#354`) | Corpus measurement of sub-`metalDispatchFloor` (`262,144`) unfused `parFor` chains to decide whether multi-pass command-buffer batching clears `ΔE2E >= 1%`. |
| **`BRT6`: First-Order Structural Witnesses (Study)** | Track A (`#301`, `#318`), `ElabAudit.lean`, `#394` (`con-leche-bridge`) | Feeds [`OPEN_CHALLENGES.md`](./OPEN_CHALLENGES.md) `Challenge B1` & `Challenge B2` (`G1`/`G2`) | Keep `HeaderPin` and `LNIR_EXPR_V1` CAS proof-term witnesses strictly structural and unification-free, matching `bendtt.lean` `--verdict`. |

## What is deliberately not proposed

- **No change to `HeapObj` or the `lean.h` ABI.** `term_make`'s 40-bit `loc` and
  headerless `RFC_BIT` redirect cells contradict
  [`docs/HEAPOBJ_CONTRACT.md`](../docs/HEAPOBJ_CONTRACT.md) §C2 (a `UInt64 ≥ 2^63`
  is a heap cell precisely because `lean_box` only has 63 payload bits). Layout
  stays Lean's, except inside explicit `D2` unboxed-region layouts
  (`LeanNative/IR/UnboxedRegion.lean`: `UnboxedStructLayout` /
  `BorrowedRegionSlice`).
- **No replacement of Perceus RC by source-level affine quantities.**
  `LeanNative/Transform/OwnershipRC.lean` (`D2`) and
  `LeanNative/Frontend/ProofRetention.lean` (`D1`) already discharge thread-local
  `lean_mark_mt`, non-owning scalar/slice scope RC, and retained `exclusiveObj`
  facts. Bend's interprocedural "borrowed means no refcount" property must
  likewise be *derived* from `LNIR` escape certificates, never assumed from a
  user quantity annotation Lean 4 does not check.
- **No second IR and no shadow stubs (`AGENTS.md` Rule 8).** Every single-decl
  code pass inhabits `VerifiedCodePassContract`, `VerifiedTransformContract`, or
  `VerifiedTVPassContract` (`LeanNative/Transform/Pass.lean`;
  [`VALIDATION_CONTRACTS.md`](./VALIDATION_CONTRACTS.md) V2) over real
  `LNIRCode` / `LLVMAst` types (and multi-declaration passes over `List LNIRDecl`
  inhabit a module-level refinement contract), with `0` local shadow namespaces.
- **No Bend-style single C translation unit.** `C1` (`#327`) locked the formal
  boundary at `Lean 4 -> Target IR`. `clang`/`ptxas`/Metal remain downstream
  TCB; we only refine the typed Target IR (`LLVMAst`, `PTXAst`, `MetalAst`,
  `StableHLOAst`) handed to them.

## How an exploration item is accepted

A `BRT*` code item merges to `main` only when all four gates hold:

1. **Formal Soundness (`Contract V2` + `AxiomAudit`)**: It inhabits
   `VerifiedCodePassContract`, `VerifiedTransformContract`,
   `VerifiedTVPassContract` (or their multi-decl `ModuleRefines` counterpart), or
   extends `LLVMLowerProofs` with `0 sorryAx`, `0 native_decide`, and `0` shadow
   allowlist entries (`scripts/check_shadow_semantics.lean`).
2. **Mutant Kills (`Contract V3`)**: At least 3 semantic/boundary mutants in
   `MutantSuite.lean` (plus `scripts/emitter_mutants.json` /
   `scripts/emitter_mutants.py` for `BRT2`) are killed.
3. **3-Way Differential Conformance (`Contract V5`)**:
   `scripts/verify_roadmap_contract.sh` passes with 100% bitwise output parity
   against `lean -c` and `evalCode`, plus `0` ASan/UBSan or RC-leak regressions.
4. **End-to-End Amdahl Ratchet (`AGENTS.md` Rule 7)**: Measured `ΔE2E >= 1%`
   geomean speedup on the canonical corpus, or the pass is pruned (`ΔLOC <= 0`).

---

## BRT0 — Segment IR: explicit tail calls, `JoinPoint`s, and module call semantics

**Builds on:** `C3` (`#334`, `#336`), `C8` (`#335`), merged `D5` (`#348`). **Feeds:** `BRT2`, `BRT3`, `BRT4`.

### The idea

`emit_body` in `comp.ts` never emits an ordinary C call for intra-book control
flow. Every definition is partitioned into `Seg` blocks ending in `WL_JMP`
(tail jump), `WL_RETN` (return), or `return jt` (fork suspension), while
`loop_of` identifies tail-call SCCs.

In `LeanNative`, `LNIRCode` (`lean/LeanNative/IR/AST.lean`) has nine
constructors (`letBind`, `rawStore`, `incRef`, `decRef`, `ite`, `seqFor`,
`parFor`, `ret`, `unreachable`), while `.call` is an `LNIRExpr` inside
`letBind`. Merged `D5` (`lean/LeanNative/Transform/AsyncStateMachine.lean`)
lowered non-escaping `IO` coroutines into stackless `(tag, state, payload)`
`.tuple [.i64, .i64, .i64]` loops over `seqFor`/`ite` without general tail-call
segmentation, so `Backend/LLVM.lean` and `Backend/LLVMLower.lean` still emit
ordinary stack-frame `call` instructions for self-recursive and mutually
recursive functions.

### The representation & semantic prerequisite

To preserve exhaustive pattern matching across existing `LNIRCode` passes and
honor the `ΔLOC <= 0` ratchet, represent segmented control flow as a canonical
`SegmentCalls` view (reusing `JoinPointId := Nat` from
`lean/LeanNative/IR/Types.lean`) rather than bloating `LNIRCode` across GPU/TV
modules:

```lean
structure JoinPoint where
  id        : JoinPointId
  remaining : Nat        -- number of forked arms before `cont` runs
  cont      : LNIRCode

-- Tail-position transfer: `join = none` is a pure tail call;
-- `join = some jp` is one arm of a structured fork-join.
| tailCall (callee : String) (args : List VarId) (retTy : LNIRType)
    (join : Option JoinPoint)
```

**Non-vacuity prerequisite (`Contract V2`):** `evalExpr` in
`lean/LeanNative/Semantics/Eval.lean` currently handles only built-in
`lean_native_*` / `lean_mark_mt` runtime intrinsics on `.call` and returns
`.error (.unsupportedCall fnName)` for user functions. Proving a transformation
over user `.call`s against single-body `evalCode` alone would be vacuously true
on `.unsupportedCall`. `BRT0` must therefore first define a fuel-bounded
module call-table evaluator `evalDeclEnv` (`List LNIRDecl → String → List Val →
Nat → ...`, mirroring `LLVMAst/Eval.lean`'s `runCallWith`) with positive
`satWitness` executions in `MutantSuite.lean`.

### Proof obligation

For `join = none`, evaluation under `evalDeclEnv` steps directly to the callee
body under the rebound parameter environment without growing continuation depth:

```lean
theorem segmentCalls_sound (decls : List LNIRDecl) :
    ModuleRefines decls (segmentCalls decls)
```

Any `.call` whose result feeds anything other than an immediate `.ret` stays an
ordinary `.letBind _ _ (.call ..)` (fail-closed).

### Acceptance

- `evalDeclEnv` positive `satWitness`es + `segmentCalls_sound` registered in
  `lean/LeanNative/Proofs/AxiomAudit.lean` (`0 sorryAx`, `strict-proofs` clean).
- `Bridge.lean` remains $\le 350$ LOC; pass lives in
  `lean/LeanNative/Transform/SegmentCalls.lean`.

---

## BRT1 — Word-resident scalar/enum unboxing via `getCtorLayout`

**Builds on:** `C4` (`#337`), `C6` (`#331`, `HeapObj` `54/54` PASS), `D2` (`#347`). **Extends:** `BridgeHelpers.lean` & `UnboxedRegion.lean`.

### The idea

In `comp.ts:859–861`, any constructor whose live layout is empty or a single
`w32` lowers to `term_pak(cid, payload)` (`TAG_PAK`) — a 64-bit immediate value
with zero heap allocation and zero RC traffic.

In `LeanNative`, `lean/LeanNative/IR/BridgeHelpers.lean` already unboxes two
cases:
1. Nullary non-recursive enums (`nullaryEnumScalarType?` $\to$ `.i8` / `.i16`,
   matching `lean_box(tag)` in `docs/HEAPOBJ_CONTRACT.md` §C1.1 & §C2.1).
2. Single-constructor flat-scalar structures (`singleCtorFlatFieldTypes?` $\to$
   `.tuple fTys`).

However, **multi-constructor** non-recursive inductives where at least one arm
carries small scalar payloads (`1..4` bytes — e.g. `Option Bool`,
`Option UInt32`, `Except UInt8 UInt16`, small lexer tokens, tagged state-machine
results) still allocate a `HeapObj` via `lean_alloc_ctor` and pay
`incRef`/`decRef` when passed across functions.

### Mechanical predicate

On a 64-bit target, a closed multi-constructor non-recursive inductive `I` is
**word-resident** for an internal `LeanNative` specialization boundary when
every constructor layout `l ← Lean.Compiler.LCNF.getCtorLayout ctorName` of `I`
satisfies:
- `l.ctorInfo.size = 0` (zero `lean_object*` slots — GC/RC never scans inside),
- `l.ctorInfo.usize = 0`, and
- `l.ctorInfo.ssize ≤ 4` bytes, with `tagBits + 8 * maxSsize ≤ 63` so
  `(payload << tagBits) | l.ctorInfo.cidx` fits inside an unboxed 64-bit word
  (or strictly below `LEAN_MAX_SMALL_NAT = 2^63 - 1`).

At public `lean.h` C-ABI boundaries (`C7` / `HybridCAbiProofs`), values convert
back to standard `HeapObj` layout unless covered by an explicit `D2`
`UnboxedStructLayout` / `BorrowedRegionSlice` boundary
(`lean/LeanNative/IR/UnboxedRegion.lean`).

### Proof obligation

Because the source program allocates short-lived `HeapObj`s while the target
computes purely on `.i64`/`.u64` scalars, soundness pairs observational value
refinement with a companion heap-leak-freedom relation `PreservesFinalHeapDelta`
(new in `Semantics/Refinement.lean` / `WordUnboxProofs.lean`):

```lean
theorem unboxWordResident_sound (d : LNIRDecl) (h : IsWordResidentInternal d) :
    CodeRefines d.body (unboxWordResident d).body ∧
    PreservesFinalHeapDelta d.body (unboxWordResident d).body
```

The second conjunct backs the ASan/RC-leak gate: it states that the unboxed path
leaves the same net surviving heap cardinality as the allocating source after RC
reclamation.

### Traps & mutant requirements

1. **32-bit target width**: `UInt32` does not fit in `lean_box` on 32-bit targets
   (`docs/HEAPOBJ_CONTRACT.md` §C2.1); predicate must require `targetBits == 64`.
2. **Mixed object/scalar arms**: One constructor having `l.ctorInfo.size > 0`
   forces the entire inductive to stay on the standard `HeapObj` path unless
   guarded by the `ptr & 1` immediate tag bit (`C2.3`).
3. **Mutants (`MutantSuite.lean`)**: (a) constructor with 1 `objPtr` field,
   (b) `l.ctorInfo.ssize = 8` (`UInt64` $\ge 2^{63}$ high-bit truncation), and
   (c) 32-bit target config — all 3 must fail closed.

---

## BRT2 — `musttail` + `preserve_nonecc` lowering in `LLVMAst`

**Builds on:** `C2`/`C3a` (`LLVMAst` + `LLVMLower.lean`, `#329`, `#336`), Stage 2C (`#381`, `#399`), `BRT0`.

### The idea

`comp.ts` compiles every host segment as `PRESERVE(preserve_none)` and every
segment transition as `__attribute__((musttail)) return WL_<fid>(WL_ALL)`,
inserting a dummy parameter at slot 6 (`comp.ts:2754–2756`) so `rax` remains
unclobbered for indirect tail jumps.

In `LeanNative`, `lean/LeanNative/Backend/LLVMAst/Syntax.lean` already defines
`CallingConv` (`.ccc | .fastcc | .coldcc`) and carries `(cc : CallingConv := .ccc)`
on both `LLVMInstr.call` and `LLVMFn` (with `LLVMAst/Eval.lean` trapping on
`fn.cc != callCc`), but `Backend/LLVM.lean` and `Backend/LLVMLower.lean` emit
neither `preserve_nonecc` nor `musttail`. Self-recursive and mutually recursive
scalar/state-machine functions therefore rely on LLVM's opportunistic tail-call
optimization or consume $O(N)$ stack frames.

### The lowering

1. Extend `CallingConv` in `lean/LeanNative/Backend/LLVMAst/Syntax.lean` with
   `| preserveNone` (`preserve_nonecc`) and add `(tailKind : TailKind := .none)`
   (`none | tail | musttail`) to `LLVMInstr.call`, enforcing LLVM's `musttail`
   invariants (matching caller/callee calling convention and return type,
   followed immediately by `ret`) in `LLVMAst/Eval.lean`.
2. Synchronize the byte-identical mirror under
   `verification/lean-mlir-bridge/LeanNative/Backend/LLVMAst/{Syntax.lean,Eval.lean}`
   required by `scripts/check_lean_mlir_bridge_sync.py` (`#381`/`#399`).
3. Lower internal `BRT0` tail-call SCCs with matching signatures to
   `musttail call preserve_nonecc`, keeping standard C ABI (`ccc`) thin entry
   wrappers for exported symbols (`C7`).

### Proof obligation

Prove both semantic preservation in `LLVMAst.Eval` (tracking an explicit
call-stack frame-depth watermark in `runCallWith` / `execFn` so `musttail`
reuses the current frame at depth $d$ instead of growing to $d + 1$) and
structural lowering soundness in `LLVMLowerProofs`:

```lean
theorem lowerTailSCC_musttail_sound (scc : List LNIRDecl) (h : ValidTailSCC scc) :
    LLVMSCCRefines scc (lowerTailSCCToLLVM scc)
```

### Acceptance

- Registered in `AxiomAudit.lean` (`0 sorryAx`), `scripts/shadow_allowlist.json`
  stays empty, and `python3 scripts/check_lean_mlir_bridge_sync.py` passes.
- Add emitter mutant `M12` to `scripts/emitter_mutants.json` (run via
  `scripts/emitter_mutants.py` over `Backend/LLVM.lean`) + `MutantSuite.lean`
  verifying that dropping `musttail` or mismatching `preserve_nonecc` between
  caller and callee is killed.
- Must clear `ΔE2E >= 1%` on recursive workloads / state machines or be pruned.

---

## BRT3 — Interprocedural borrow fixpoint & size-class slot reuse

**Builds on:** `C6` (`#331`), `D1` (`ProofRetention.lean`, `#352`), `D2` (`OwnershipRC.lean`, `#347`), `BRT0`.

### The idea

Merged `D2` (`lean/LeanNative/Transform/OwnershipRC.lean`) proves
intra-procedural alias/escape analysis (`tlCodeEscapesWith`), thread-local
`lean_mark_mt` elision (`optimizeThreadLocalOwnershipRC_sound`), and non-owning
scalar/slice scope RC elision (`elideBorrowedAndThreadLocalRC_sound`), while
merged `D1` (`lean/LeanNative/Frontend/ProofRetention.lean`) discharges
surface-retained `exclusiveObj` facts. However, three gaps remain in
`OwnershipRC.lean`:
- `tlExprEscapesWith` treats *every* non-intrinsic `.call` as escaping, leaving
  `LNIRParam.borrow : Bool` (`lean/LeanNative/IR/AST.lean`) uninferred across
  call SCCs;
- `valIsNonOwning` is `false` for `Val.objPtr`, so borrowed heap parameters
  still pay `incRef`/`decRef` across recursive read-only traversals; and
- dead uniquely-owned constructors are still freed and reallocated rather than
  reused in place.

`comp.ts` closes both gaps through two compact mechanisms:
1. **Whole-SCC borrow greatest fixpoint (`c_units` + `brw_of`, `comp.ts:1040`, `2708–2718`)**:
   Parameters start borrowed and only flip to owned (`fact_add("own")`) if the
   transitive closure of `lends` reaches a heap store or return. Because it is a
   greatest fixpoint ("borrowed until proven escaping"), recursive read-only
   functions (`List.lookup`, `RBNode.find`, AST walkers) keep their `Val.objPtr`
   parameters borrowed across recursive calls.
2. **Scoped spare-slot reuse (`sc.spares`, `comp.ts:869–874`, `1455–1459`)**:
   When a uniquely owned constructor (`rc == 1` / `isExclusive`) is consumed in
   a branch, a subsequent `allocCtor` with matching object-slot count and scalar
   byte size reuses the allocation in place via `lean_native_ctor_set` /
   `lean_native_ctor_set_scalar` / `lean_native_ctor_set_tag`.

### The analysis & proof obligation

Extend `OwnershipRC.lean` (rather than introducing a parallel pass) with
`borrowedParams : List LNIRDecl → List ((String × Nat) × Bool)` computed via
monotone finite-lattice iteration over the module call graph, and prove over
`BRT0`'s multi-declaration evaluator:

```lean
theorem elideBorrowedRC_sound (decls : List LNIRDecl) :
    ModuleRefines decls (elideBorrowedAndReuse decls)
```

`borrowedParams` itself stays outside the trusted reasoning core if
`elideBorrowedAndReuse` validates the computed assignment with a decidable
`IsValidBorrowAssignment` certificate check (`SpeculativeGate` / `Contract V2`).

### Trap

Never trust surface `@[borrow]` annotations without verifying non-escape in
`LNIR`: external calls (`LNIRExpr.call` with `isExtern = true`) with unknown
borrow contracts must conservatively mark passed `Val.objPtr` arguments as
escaping unless covered by `C7`'s verified `HybridCAbiProofs` contracts.

---

## BRT4 — Dual-mode (`!seq`) commuting fork-join on CPU workers

**Builds on:** `C7` (`#328`, `#333`), `D2` (`SendableSlot` in `UnboxedRegion.lean`, `#347`), `LeanSys.Par`, `BRT0`, `BRT3`. **Sequenced last among code items.**

### The idea

`parFor` in `lean/LeanNative/Backend/GPUIR.lean` rightly rejects heap allocation
(`allocCtor`), object projections (`ctorGetObj`), and RC (`incRef`/`decRef`) on
SIMT GPUs. That leaves divide-and-conquer CPU workloads over trees/ASTs
sequential inside `LNIR`, even though `LeanSys.Par` (`parMapChunks`,
`parMapMicroChunks`, `WorkerBudget`, C-ABI `leansys_verify_par_chunk` /
`leansys_verify_worker_budget`) already provides verified work partitioning.

Bend's `emit_fork` (`comp.ts:2421–2490`) and `monk_step` (`comp.ts:4441–4481`)
show how to lower task parallelism to C/LLVM workers without paying
task-allocation overhead when cores are saturated:
- Emit dual-mode branches `if (!seq)`: only allocate a join frame (`remaining`
  atomic countdown) when worker queues are under-saturated (`seq == 0`); once
  saturated (`seq == 1`), run the exact same arms sequentially on the stack.
- Statically tag fork-free callees (`fid_nofk`, `comp.ts:2737`) so leaf calls
  never touch the work queue.
- Delay cross-thread stealing by a `1 ms` monotonic-clock grace window
  (`row_grow`, `comp.ts:4661`) so sub-millisecond calls pay zero synchronization.

### Soundness side condition

Concurrent execution of `LNIRCode` arms refines sequential execution only when
arms have disjoint heap/memory effects (`rawStore`, `sarraySet`, `storageStore`,
and mutating `HeapObj` intrinsics `lean_native_ctor_set*` /
`lean_native_del_obj`) and every captured heap object satisfies `D2`'s
sendable/MT ownership contract (`SendableSlot` / `lean_mark_mt` in
`lean/LeanNative/IR/UnboxedRegion.lean`, so single-threaded `m_rc > 0` headers
are never raced):

```lean
theorem forkJoinDualMode_sound (arms : List LNIRCode) (cont : LNIRCode)
    (h_comm : PairwiseDisjointEffects arms)
    (h_send : AllCapturedSendable arms) :
    CodeRefines (evalSeqArms arms cont) (evalDualModeFork arms cont)
```

When `PairwiseDisjointEffects` or `AllCapturedSendable` fails to decide `true`,
lowering silently falls back to `BRT0` sequential evaluation.

---

## BRT5 — Study: GPU multi-pass turn batching vs. `metalDispatchFloor`

**Builds on:** `C3b` (`#334`), `C7` (`#328`), `C8` (`#335`), merged `D4` (`CostAutotune.lean`, `#358`). **Orthogonal to:** `D6` (`PTXAst/Proofs.lean` & `PTXDeclProofs.lean`, `#354`).

### Question to resolve

`lean/LeanNative/Backend/Hybrid.lean` enforces `metalDispatchFloor = 262144`
elements (~2 MB `uint64_t`, with CPU SIMD below `4096`) per `parFor` because a
single Metal command buffer / CUDA launch costs ~30–60 µs. `C8` (`#335`) already
added `fuseParForKernels_sound` for fusible producer-consumer loops (and `D6`
`#354` formalized intra-kernel CTA barrier generations), while Bend's `bend_dev`
(`comp.ts:4534–4608`) amortizes host launch overhead across *unfused* stages by
encoding multiple passes into one command buffer / frontier turn (`turn_groups`).

Before writing any runtime code:
1. Measure on `Batteries`, `SciLean`, and `turbo-lean`'s `fast-check` workloads
   what fraction of `GPUIR.extractParForRegions` outputs remain non-fusible
   after `C8` *and* fall in `[4096, 262144)`.
2. Benchmark on Apple Silicon Metal + CUDA (`rtx4090` via `D4`'s
   `lean/LeanNative/Transform/CostAutotune.lean`) whether multi-kernel
   command-buffer encoding beats NEON/AVX2 CPU SIMD in that window by
   $\ge 1\%$ E2E (see baseline methodology in
   [`docs/BENCH_RUST_PARITY.md`](../docs/BENCH_RUST_PARITY.md)).
3. Record a 2-page go/no-go note; if $< 1\%$, close without adding runtime LOC.

---

## BRT6 — Study: first-order structural witnesses for `G1` / `G2`

**Builds on:** Track A (`#301`, `#318`), `TurboLean/ConLeche.lean`, `TurboLean/ElabAudit.lean`, `#394` (`verification/con-leche-bridge/`). **Feeds:** [`OPEN_CHALLENGES.md`](./OPEN_CHALLENGES.md) `Challenge B1` & `Challenge B2` (`G1`/`M2` & `G2`/`M3`).

### Architectural takeaway from `bendtt.lean` + `checker-eval`

In `bendlang/checker-eval`, Claude Opus 5.5 scored **0/20** blind vs. **20/20**
with `bend` checker feedback, backed by a ~177 KB Lean 4 kernel (`bendtt.lean`)
that re-verifies definitions via `--verdict`. What makes `--verdict` fast and
unspoofable is not Bend's affine type theory—it is that the witness format has
**zero metavariable unification, zero typeclass search, and zero tactic state**:
checking is structural recursion over explicit terms.

Now that `#394` pinned real upstream `leanprover/con-leche` + `lean4lean` in
`verification/con-leche-bridge/ConLecheBridge/Soundness.lean` (`--tier C3`
`.olean` gate), as `turbo-lean` completes `Challenge B1` (`G1`/`M2`) and
`Challenge B2` (`G2`/`M3`: `HeaderPin` + `LNIR_EXPR_V1` warm CAS proof-term
replay in `TurboStore`, distinct from `LeanNative/IR/Codec.lean`'s
`LNIR_WIRE_V1` module codec):
- **Do** require every cached `LNIR_EXPR_V1` (`"LNE1"`) witness in `TurboStore`
  to be a fully elaborated, universe-instantiated kernel `Expr` DAG checkable in
  $< 1\text{ ms}$ by pure structural kernel typing (`replayCASProofBlob` /
  `cas_proof_replay_sound` / `con-leche`) without invoking `Lean.Elab`, with
  zero affine or interaction-net quantities.
- **Do** keep `HeaderPin` (`header_pin_prevents_statement_spoofing`) strictly
  first-order over explicit binder telescopes and `statement-v1`
  `kernel_type_hash` (`#318`).

---

## Suggested execution order

| Order | Item | Kind | Prerequisite | Target Modules |
| :--- | :--- | :--- | :--- | :--- |
| 1 | **`BRT5`** | measurement study | `C8`, `D4` (merged) | `docs/` / `Transform/CostAutotune.lean` calibration notes |
| 2 | **`BRT6`** | design note | `ElabAudit`, `#318`, `#394` (merged) | `OPEN_CHALLENGES.md` `Challenge B2` (`G2`/`M3`) witness spec |
| 3 | **`BRT0`** | semantics + transform | `C3`, `C8`, `D5` (merged) | `Semantics/Eval.lean` (`evalDeclEnv`), `Transform/SegmentCalls.lean` |
| 4 | **`BRT2`** | backend lowering | `BRT0` + `lean-mlir-bridge` sync | `Backend/LLVMAst/`, `LLVMLower.lean`, `LLVM.lean`, `verification/lean-mlir-bridge/` |
| 5 | **`BRT1`** | unboxing pass | `C6`, `D2` (merged) | `IR/BridgeHelpers.lean`, `Transform/`, `Proofs/` |
| 6 | **`BRT3`** | RC & reuse pass | `C6`, `D1`, `D2` (merged), `BRT0` | `Transform/OwnershipRC.lean`, `Proofs/` |
| 7 | **`BRT4`** | parallel runtime | `D2` (merged), `BRT0`, `BRT3` | `Backend/Hybrid.lean`, `Backend/C.lean`, `Backend/LLVMLower.lean` |

## Explicitly rejected ideas from Bend 2

- **40-bit `loc` pointers and headerless `RFC_BIT` redirect cells (`comp.ts:3819–3896`)**:
  Incompatible with `lean.h`, `libleanshared` FFI, 64-bit `UInt64` boxing rules
  (`docs/HEAPOBJ_CONTRACT.md` §C2.1), and `C6`.
- **Adding affine quantity annotations (`0` / `1` / `2`) or `Type : Type` to Lean**:
  Bend needs `0`-quantities to recover logical consistency in `BendTT` despite
  `Type : Type` and negative datatypes. Lean 4 already has `Prop` erasure,
  predicative universes, and LCNF `.mono` erasure; modifying the type theory
  would fork Lean.
- **Single-source C macro polyglot (`runtime_c` `#embed __FILE__`, `comp.ts:3141–3422`)**:
  Violates `C1`–`C3`, which prove lowering directly against typed `LLVMAst`,
  `PTXAst`, `MetalAst`, and `StableHLOAst` operational semantics rather than
  interpolating raw C preprocessor strings.
- **Per-lane custom slab banks (`ALC_AT` / `bank_pack`, `comp.ts:3692–3808`) on the Lean heap**:
  Bend's runtime owns a single flat `mmap` `CORPUS` shared with the GPU with no
  external runtime. `LeanNative` interoperates zero-copy with Lean's allocator;
  maintaining a second allocator over `lean_object*` pointers would corrupt RC
  and region persistence (`m_rc == 0`).
