# BendRT Exploration Roadmap (`B0`–`B6`)

> **Status of this document: an exploratory proposal, not a locked contract.**
> Nothing here modifies [`GOALS.md`](./GOALS.md),
> [`VALIDATION_CONTRACTS.md`](./VALIDATION_CONTRACTS.md),
> [`CONFORMANCE_SUITE.md`](./CONFORMANCE_SUITE.md), or
> [`docs/ROADMAP.md`](../docs/ROADMAP.md). Now that `C1`–`C8` (`Lean 4 -> Target
> IR`) are merged on `main` (`#327`–`#338`), this document specifies the
> concrete fragments of Bend 2's runtime and compiler (`bendlang/bend`
> `v2.0.39`) worth evaluating alongside the Next-Gen `D0`–`D5` tracks—each with
> the exact assumption that makes it legal under `lean.h`, its relationship to
> `D1`–`D5`, and the `Contract V1–V5` + Rule 7 (`ΔE2E >= 1%`) gates required to
> keep it.

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
survive contact with Lean's ABI and reinforce `D1`–`D5` without violating any
`C1`–`C8` invariant.

## Alignment with `C1`–`C8` (Merged) and `D1`–`D5` (Next-Gen)

| Exploration Item | Builds on (`main`) | Reinforces Next-Gen Track | Core Mechanism |
| :--- | :--- | :--- | :--- |
| **`B0`: Tail-Segment & `JoinPoint` IR** | `C3` (`LLVMLower`, `PTXAst`, `MetalAst`), `C8` (`ClosureADT`) | **`D5`** (Zero-Alloc Stackless Async) | Explicit `tailCall` + `JoinPoint` representation over `LNIRCode` enabling both CPU `musttail` and stackless state-machine lowering. |
| **`B1`: Word-Resident Scalar/Enum Unboxing** | `C4` (`RealLCNFBridge`), `C6` (`HeapObj` `54/54` PASS) | **`D2`** (Unboxed Regions) | Mechanical `getCtorLayout` predicate (`size = 0 ∧ usize = 0 ∧ ssize ≤ 4` on 64-bit) packing small payload ADTs into tagged immediates (`0` heap allocs, `0` RC). |
| **`B2`: `musttail` + `preserve_nonecc` Lowering** | `C2`/`C3a` (`LLVMAst` + `LLVMLowerProofs`), `B0` | **`D4` / `D5`** | Lower scalar/unboxed tail-call cycles in `LLVMAst` / `LLVM.lean` to `musttail call preserve_nonecc` for $O(1)$ stack and register-pinned state threading. |
| **`B3`: Interprocedural Borrow & Slot-Reuse Fixpoint** | `C6` (`HeapObjAbiProofs`), `OwnershipRC.lean`, `B0` | **`D1`** (Proof-Carrying LCNF) & **`D2`** (Thread-Local Ownership) | Monotone call-graph escape fixpoint (`escapes v code`) eliding non-zero-delta `incRef`/`decRef` pairs on non-escaping parameters + `sc.spares`-style size-matched `reset`/`reuse`. |
| **`B4`: Dual-Mode (`!seq`) Commuting Fork-Join** | `C7` (`Hybrid.lean`), `B0`, `B3` | **`D2` / `D5`** | Commutativity-checked (`commute a b`) fork-join over `LeanSys.Par` / worker threads using Bend's `if (!seq)` saturation toggle, `fid_nofk` leaf inlining, and `1 ms` lazy steal threshold. |
| **`B5`: Multi-Region `parFor` GPU Turn Batching (Study)** | `C3b` (`PTX`/`Metal`), `C7` (`Hybrid`), `C8` (`KernelFusion`) | **`D4`** (Hardware-in-the-Loop Cost Autotuning) | Corpus measurement of sub-`metalDispatchFloor` (`262,144`) `parFor` chains to decide whether multi-pass command-buffer batching clears `ΔE2E >= 1%`. |
| **`B6`: First-Order Structural Witnesses (Study)** | Track A (`#301`, `#318`), `ElabAudit.lean`, `ConLeche.lean` | **`G1` / `G2`** (`M2` / `M3`) | Keep `HeaderPin` and `LNIR_EXPR_V1` CAS proof replay strictly structural and unification-free, matching `bendtt.lean` `--verdict`. |

## What is deliberately not proposed

- **No change to `HeapObj` or the `lean.h` ABI.** `term_make`'s 40-bit `loc` and
  headerless `RFC_BIT` redirect cells contradict
  [`docs/HEAPOBJ_CONTRACT.md`](../docs/HEAPOBJ_CONTRACT.md) §C2 (a `UInt64 ≥ 2^63`
  is a heap cell precisely because `lean_box` only has 63 payload bits). Layout
  stays Lean's, except inside explicit `D2` `@[unboxed_region]` scopes.
- **No replacement of Perceus RC by source-level affine quantities.**
  `OwnershipRC.lean` currently elides `incRef`/`decRef` of delta zero. Bend's
  "borrowed means no refcount" property must be *derived* from `LNIR` escape
  facts (or `D1` `ProofRetention` invariants), never assumed from a user
  quantity annotation Lean 4 does not check.
- **No second IR and no shadow stubs (`AGENTS.md` Rule 8).** Every code pass
  inhabits `VerifiedCodePassContract` or `VerifiedTVPassContract`
  ([`VALIDATION_CONTRACTS.md`](./VALIDATION_CONTRACTS.md) V2) over the real
  `LNIRCode` / `LLVMAst` types, with `0` local shadow namespaces.
- **No Bend-style single C translation unit.** `C1` (`#327`) locked the formal
  boundary at `Lean 4 -> Target IR`. `clang`/`ptxas`/Metal remain downstream
  TCB; we only refine the typed Target IR (`LLVMAst`, `PTXAst`, `MetalAst`,
  `StableHLOAst`) handed to them.

## How an exploration item is accepted

A `B*` code item merges to `main` only when all four gates hold:

1. **Formal Soundness (`Contract V2` + `AxiomAudit`)**: It inhabits
   `VerifiedCodePassContract`, `VerifiedTVPassContract`, or extends
   `LLVMLowerProofs` with `0 sorryAx`, `0 native_decide`, and `0` shadow
   allowlist entries (`scripts/check_shadow_semantics.lean`).
2. **Mutant Kills (`Contract V3`)**: At least 3 semantic/boundary mutants in
   `MutantSuite.lean` (or `scripts/emitter_mutants.py` for `B2`) are killed.
3. **3-Way Differential Conformance (`Contract V5`)**:
   `scripts/verify_roadmap_contract.sh` passes with 100% bitwise output parity
   against `lean -c` and `evalCode`, plus `0` ASan/UBSan or RC-leak regressions.
4. **End-to-End Amdahl Ratchet (`AGENTS.md` Rule 7)**: Measured `ΔE2E >= 1%`
   geomean speedup on the canonical corpus, or the pass is pruned (`ΔLOC <= 0`).

---

## B0 — Segment IR: explicit tail calls and `JoinPoint`s in `LNIR`

**Builds on:** `C3` (`#334`, `#336`), `C8` (`#335`). **Feeds:** `B2`, `B3`, `B4`, and `D5`.

### The idea

`emit_body` in `comp.ts` never emits an ordinary C call for intra-book control
flow. Every definition is partitioned into `Seg` blocks ending in `WL_JMP`
(tail jump), `WL_RETN` (return), or `return jt` (fork suspension), while
`loop_of` identifies tail-call SCCs.

In `LeanNative`, `LNIRCode` has `letBind`, `ite`, `seqFor`, `parFor`, and `ret`,
while `.call` is an `LNIRExpr` inside `letBind`. Consequently, `Backend/LLVM.lean`
and `Backend/LLVMLower.lean` treat recursive tail calls as ordinary stack-frame
calls, and `D5` (`AsyncStateMachine.lean`) lacks a canonical tail-continuation
node to lower into state transitions.

### The IR extension

Introduce a dedicated tail-transfer terminator (or canonical `SegmentCalls`
view over `LNIRCode` if `ΔLOC` favors keeping `LNIRCode` closed):

```lean
structure JoinPoint where
  id        : Nat
  remaining : Nat        -- number of forked arms before `cont` runs
  cont      : LNIRCode

-- Tail-position transfer: `join = none` is a pure tail call;
-- `join = some jp` is one arm of a structured fork-join.
| tailCall (callee : String) (args : List VarId) (retTy : LNIRType)
    (join : Option JoinPoint)
```

### Proof obligation

For `join = none`, evaluation under `evalDeclEnv` steps directly to the callee
body under the rebound parameter environment without growing continuation depth:

```lean
theorem segmentCalls_sound (d : LNIRDecl) :
    CodeRefines d.body (segmentCalls d).body
```

Any `.call` whose result feeds anything other than an immediate `.ret` stays an
ordinary `.letBind _ _ (.call ..)` (fail-closed).

### Acceptance

- `segmentCalls_sound` registered in `lean/LeanNative/Proofs/AxiomAudit.lean` (`0 sorryAx`).
- `Bridge.lean` remains $\le 350$ LOC; pass lives in `lean/LeanNative/Transform/SegmentCalls.lean` (or directly inside `D5`'s `AsyncStateMachine.lean`).

---

## B1 — Word-resident scalar/enum unboxing via `getCtorLayout`

**Builds on:** `C4` (`#337`), `C6` (`#331`, `HeapObj` `54/54` PASS). **Feeds:** `D2` (`UnboxedRegion.lean`).

### The idea

In `comp.ts:859–861`, any constructor whose live layout is empty or a single
`w32` lowers to `term_pak(cid, payload)` (`TAG_PAK`) — a 64-bit immediate value
with zero heap allocation and zero RC traffic.

In Lean 4 (`docs/HEAPOBJ_CONTRACT.md` §C1.1 & §C2.1), nullary constructors
(`size = usize = ssize = 0`) are already immediate `lean_box(tag)`. However,
non-recursive inductives whose constructors carry *only* small scalar payloads
(`Bool`, `UInt8`, `UInt16`, `UInt32` — e.g. `Option Bool`, `Ordering`-tagged
results, small lexer tokens, state-machine states) still allocate a `HeapObj` via
`lean_alloc_ctor` and pay `incRef`/`decRef` when passed polymorphically or
across module boundaries.

### Mechanical predicate

On a 64-bit target, a closed non-recursive inductive `I` is **word-resident**
for an internal `LeanNative` specialization boundary when every constructor `c`
of `I` satisfies `Lean.Compiler.LCNF.getCtorLayout`:
- `c.size = 0` (zero `lean_object*` slots — GC never scans inside),
- `c.usize = 0`, and
- `c.ssize ≤ 4` bytes (so `(payload << tagBits) | tag` fits strictly below
  `LEAN_MAX_SMALL_NAT = 2^63 - 1`, or inside an unboxed `.i64` word).

At public `lean.h` C-ABI boundaries (`C7`), values convert back to standard
`HeapObj` layout unless marked `@[unboxed_region]` (`D2`).

### Proof obligation

Because the source program allocates short-lived `HeapObj`s while the target
computes purely on `.u64` scalars, soundness pairs observational value
refinement with heap-leak freedom:

```lean
theorem unboxWordResident_sound (d : LNIRDecl) (h : IsWordResidentInternal d) :
    CodeRefines d.body (unboxWordResident d).body ∧
    PreservesFinalHeapDelta d.body (unboxWordResident d).body
```

The second conjunct is what backs the ASan/RC-leak gate: it states that the
unboxed path leaves the same net surviving heap cardinality as the allocating
source after RC reclamation.

### Traps & mutant requirements

1. **32-bit target width**: `UInt32` does not fit in `lean_box` on 32-bit targets
   (`docs/HEAPOBJ_CONTRACT.md` §C2.1); predicate must require `targetBits == 64`.
2. **Mixed object/scalar arms**: One constructor having `size > 0` forces the
   entire inductive to stay on the standard `HeapObj` path unless guarded by the
   `ptr & 1` immediate tag bit (`C2.3`).
3. **Mutants (`MutantSuite.lean`)**: (a) constructor with 1 `objPtr` field,
   (b) `ssize = 8` (`UInt64` $\ge 2^{63}$ high-bit truncation), and (c) 32-bit
   target config — all 3 must fail closed.

---

## B2 — `musttail` + `preserve_nonecc` lowering in `LLVMAst`

**Builds on:** `C2`/`C3a` (`LLVMAst` + `LLVMLower.lean`, `#329`, `#336`), `B0`. **Feeds:** `D4`, `D5`.

### The idea

`comp.ts` compiles every host segment as `PRESERVE(preserve_none)` and every
segment transition as `__attribute__((musttail)) return WL_<fid>(WL_ALL)`,
inserting a dummy parameter at slot 6 (`comp.ts:2754–2756`) so `rax` remains
unclobbered for indirect tail jumps.

In `LeanNative`, `Backend/LLVM.lean` and `Backend/LLVMLower.lean` currently emit
zero `musttail` or `preserve_nonecc` attributes. Self-recursive and mutually
recursive scalar/state-machine functions lowered by `C4` or `D5` either rely on
LLVM's opportunistic tail-call optimization (which breaks under subtle ABI or
caller-saved register mismatches) or consume $O(N)$ stack frames.

### The lowering

1. Extend `LeanNative/Backend/LLVMAst/Syntax.lean` call instructions and
   function headers with an explicit calling convention (`cc : CallConv`, adding
   `.preserveNone` alongside `.ccc`) and tail marker (`tailKind : TailKind`,
   adding `.musttail`).
2. Lower internal `B0` tail-call SCCs with matching signatures to
   `musttail call preserve_nonecc`, keeping standard C ABI (`ccc`) thin entry
   wrappers for exported symbols (`C7`).

### Proof obligation

Prove both semantic preservation in `LLVMAst.Eval` (modeling `musttail` with
bounded/zero call-stack growth in `execFn`) and structural emission in
`LLVMLowerProofs`:

```lean
theorem lowerTailSCC_musttail_sound (scc : List LNIRDecl) (h : ValidTailSCC scc) :
    LLVMSCCRefines scc (lowerTailSCCToLLVM scc)
```

### Acceptance

- Registered in `AxiomAudit.lean` (`0 sorryAx`), `scripts/shadow_allowlist.json` stays empty.
- Add emitter mutant `M12` to `scripts/emitter_mutants.py` verifying that
  dropping `musttail` or mismatching `preserve_nonecc` between caller and callee
  is caught.
- Must clear `ΔE2E >= 1%` on recursive workloads / `D5` state machines or be
  restricted strictly to `D5` coroutines.

---

## B3 — Interprocedural borrow fixpoint & size-class slot reuse

**Builds on:** `C6` (`#331`), `OwnershipRC.lean`, `B0`. **Directly implements part of:** `D1` & `D2`.

### The idea

`LeanNative/Transform/OwnershipRC.lean` currently proves `elideAndMutateRC_sound`,
which only deletes literal zero-delta `incRef v 0` / `decRef v 0` instructions.
Meanwhile, `comp.ts` achieves near-zero atomic RC traffic on pure functional
traversals through two tiny mechanisms:
1. **Whole-SCC borrow fixpoint (`c_units` + `brw_of`, `comp.ts:1040`, `2708–2718`)**:
   Parameters start borrowed and only flip to owned (`fact_add("own")`) if the
   transitive closure of `lends` reaches a heap store or return. Because it is a
   greatest fixpoint ("borrowed until proven escaping"), recursive read-only
   functions (`List.lookup`, `RBNode.find`, AST walkers) keep their parameters
   borrowed across recursive calls—whereas a single-pass syntactic check sees
   the recursive call and conservatively assumes escape.
2. **Scoped spare-slot reuse (`sc.spares`, `comp.ts:869–874`, `1455–1459`)**:
   When a uniquely owned constructor (`isExclusive` / `ctr_take`) is matched in
   tail position, its deallocation is pushed onto `sc.spares` and immediately
   reused by a subsequent `allocCtor` of the same layout (`n` object slots,
   matching scalar area), turning free + alloc into in-place field stores.

### The analysis & proof obligation

Compute `borrowedParams : List LNIRDecl → Map (String × Nat) Bool` via monotone
finite-lattice iteration over the module's `LNIRDecl` call graph, and prove:

```lean
theorem elideBorrowedRC_sound (decls : List LNIRDecl) :
    ModuleRefines decls (elideBorrowedAndReuse decls)
```

Note that `borrowedParams` itself does not even need its fixpoint search trusted
if `elideBorrowedAndReuse` validates the computed borrow certificate via an
inductive `IsValidBorrowAssignment` check (`SpeculativeGate` / `Contract V2`).

### Trap

Never trust surface `@[borrow]` annotations without verifying non-escape in
`LNIR`: FFI externs (`isExtern = true`) with unknown borrow contracts must
conservatively mark passed object arguments as escaping unless covered by `C7`'s
verified `HybridCAbiProofs` contracts.

---

## B4 — Dual-mode (`!seq`) commuting fork-join on the CPU worker pool

**Builds on:** `C7` (`#328`, `#333`), `B0`, `B3`. **Sequenced last among code items.**

### The idea

`parFor` in `GPUIR.lean` rightly rejects heap allocation (`allocCtor`), object
projections (`ctorGetObj`), and RC (`incRef`/`decRef`) on SIMT GPUs. That leaves
divide-and-conquer CPU workloads over trees/ASTs (such as parallel sub-term
analysis or independent proof-obligation waves in `turbo-lean-native`)
sequential inside `LNIR`.

Bend's `emit_fork` (`comp.ts:2421–2490`) and `monk_step` (`comp.ts:4441–4481`)
show how to run task parallelism without paying task-allocation overhead when
cores are busy:
- Emit dual-mode branches `if (!seq)`: only allocate a join frame (`remaining`
  atomic countdown) when worker rings are under-saturated (`seq == 0`); once
  saturated (`seq == 1`), run the exact same arms sequentially on the stack.
- Statically tag fork-free callees (`fid_nofk`, `comp.ts:2737`) so leaf calls
  never touch the work queue.
- Delay cross-thread stealing by a `1 ms` monotonic-clock grace window
  (`row_grow`, `comp.ts:4661`) so sub-millisecond calls pay zero synchronization.

### Soundness side condition

Concurrent execution of `LNIRCode` arms refines sequential execution only when
arms commute on shared mutable state (`rawStore`, `sarraySet`, `storageStore`,
and non-thread-safe single-threaded `m_rc > 0` `HeapObj` headers—requiring `D2`'s
thread-local/sendable ownership proof so shared inputs are either immutable/persistent
or disjointly owned):

```lean
theorem forkJoinDualMode_sound (arms : List LNIRCode) (cont : LNIRCode)
    (h_comm : PairwiseDisjointEffects arms)
    (h_send : AllCapturedSendable arms) :
    CodeRefines (evalSeqArms arms cont) (evalDualModeFork arms cont)
```

When `PairwiseDisjointEffects` or `AllCapturedSendable` fails to decide `true`,
lowering silently falls back to `B0` sequential evaluation.

---

## B5 — Study: GPU multi-pass turn batching vs. `metalDispatchFloor`

**Builds on:** `C3b` (`#334`), `C7` (`#328`), `C8` (`#335`). **Feeds:** `D4` (`CostAutotune.lean`).

### Question to resolve

`Hybrid.lean` enforces `metalDispatchFloor = 262144` elements (~2 MB `uint64_t`)
per `parFor` because a single Metal command buffer / CUDA launch costs ~30–60 µs.
`C8` (`#335`) already added `fuseParForKernels_sound` for fusible producer-consumer
loops, while Bend's `bend_dev` (`comp.ts:4534–4608`) amortizes launch overhead
across *unfused* stages by encoding multiple passes into one persistent command
buffer / frontier turn (`turn_groups`).

Before writing any code:
1. Measure on `Batteries`, `SciLean`, and `turbo-lean`'s `fast-check` workloads
   what fraction of `GPUIR.extractParForRegions` outputs remain non-fusible
   after `C8` *and* fall between `4,096` and `262,144` elements.
2. Benchmark on Apple Silicon Metal + CUDA (`rtx4090` via `D4`) whether command-buffer
   multi-kernel encoding beats NEON/AVX2 CPU SIMD in that window by $\ge 1\%$ E2E.
3. Record a 2-page go/no-go note; if $< 1\%$, close without adding runtime LOC.

---

## B6 — Study: first-order structural witnesses for `G1` / `G2`

**Builds on:** Track A (`#301`, `#318`), `TurboLean/ConLeche.lean`, `TurboLean/ElabAudit.lean`. **Feeds:** `G1` (`M2`) & `G2` (`M3`).

### Architectural takeaway from `bendtt.lean` + `checker-eval`

In `bendlang/checker-eval`, Claude Opus 5.5 scored **0/20** blind vs. **20/20**
with `bend` checker feedback, backed by a ~177 KB Lean 4 kernel (`bendtt.lean`)
that re-verifies definitions via `--verdict`. What makes `--verdict` fast and
unspoofable is not Bend's affine type theory—it is that the witness format has
**zero metavariable unification, zero typeclass search, and zero tactic state**:
checking is structural recursion over explicit terms.

As `turbo-lean` wires `M2` (upstream `con-leche` `.olean` verification) and `M3`
(`HeaderPin` + `LNIR_EXPR_V1` warm CAS proof-term replay):
- **Do** require every cached `LNIR_EXPR_V1` witness in `TurboStore` to be a
  fully elaborated, universe-instantiated kernel `Expr` DAG checkable in $< 1\text{ ms}$
  by pure structural kernel typing (`Kernel.Environment.replay` / `con-leche`)
  without invoking `Lean.Elab`.
- **Do** keep `HeaderPin` (`header_pin_prevents_statement_spoofing`) strictly
  first-order over explicit binder telescopes and `statement-v1`
  `kernel_type_hash` (`#318`).

---

## Suggested execution order

| Order | Item | Kind | Prerequisite | Target Modules |
| :--- | :--- | :--- | :--- | :--- |
| 1 | **`B5`** | measurement study | `C8` (merged) | `docs/` / `D4` calibration notes |
| 2 | **`B6`** | design note | `ElabAudit` / `#318` (merged) | `G1`/`G2` (`M2`/`M3`) witness spec |
| 3 | **`B0`** | IR / transform | `C3`, `C8` (merged) | `lean/LeanNative/Transform/SegmentCalls.lean` (or `D5`) |
| 4 | **`B2`** | backend lowering | `B0` | `lean/LeanNative/Backend/LLVMAst/`, `LLVMLower.lean`, `LLVM.lean` |
| 5 | **`B1`** | unboxing pass | `C6` (merged) | `lean/LeanNative/Transform/`, `lean/LeanNative/Proofs/` |
| 6 | **`B3`** | RC & reuse pass | `C6` (merged), `B0` | `lean/LeanNative/Transform/OwnershipRC.lean` (with `D1`/`D2`) |
| 7 | **`B4`** | parallel runtime | `B0`, `B3`, `D2` | `lean/LeanNative/Backend/Hybrid.lean`, `Driver/Worker.lean` |

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
