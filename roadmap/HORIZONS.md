# Sequencing: three horizons (`roadmap/HORIZONS.md`)

> **Scope**: the order in which the goals in [`GOALS.md`](./GOALS.md) are worked, and why. It adds no theorem contract and changes none in [`VALIDATION_CONTRACTS.md`](./VALIDATION_CONTRACTS.md). Numbers are measured on `main` at `94dbd70` (2026-11-15) and are point-in-time.

Source: Thomas's roadmap note of 2026-11-14 (prove Lean → IR first; build faster, hypothesis: pure-Lean kernel compiled by `LeanNative`, GPU if it pays; accelerator plugins last).

| Horizon | Outcome | Goals it draws on |
| :--- | :--- | :--- |
| **H1 (now)** | One formally proven path from Lean (`LCNF`) to `LNIR`. Every other path is deleted or fails closed to the stock Lean backend. | `G3.1`, `G3.2`, `G4` |
| **H2 (next)** | Builds are faster, measured end to end. The pure-Lean kernel compiled by the H1 path is the first real workload. | `G1`, `G2`, issues `#407`–`#443` |
| **H3 (later)** | Compiler performance through zero-TCB accelerator plugins driven by telemetry; the remaining backends get proofs. | `G3.3`, `G4`, `G5`, Track A |

---

## Where the compiler stands

| Part | Size | Proof state |
| :--- | ---: | :--- |
| `lean/LeanNative` total | 187 files, 114k LOC | 0 `sorry`, 0 `axiom` |
| `IR/Bridge.lean` | 245 LOC | entry point; delegates to the paths below |
| `IR/RealLCNFBridge.lean` + `RealLCNFSemantics.lean` | 2,051 LOC | refinement proved for scalars, flat tuples, bounded Stage-1D ADTs, against an in-repo `LCNF` semantics |
| `IR/BridgeHelpers.lean` | 2,357 LOC | lowering helpers outside the proved subset |
| `Backend/` | 32 files, 31k LOC | typed AST printers proved on subsets; string emitters remain |
| `Driver/CoreCLI.lean` | 11 `compile-*` / `emit-*` commands | one frontend, many emission paths |

`Bridge.lean` rejects, with `Unsupported …`: higher-order and escaping local functions, partial application, returning closures, signed `Int*` / `ISize`, `@[extern]` declarations, non-scalar external calls, and self tail recursion without a qualified loop lowering.

Two facts drive the plan:

1. **The proved lowering and the lowering that runs are not yet the same object.** A proof about a subset next to 2,357 LOC of unproved helpers proves less than it seems to.
2. **The source semantics is trusted and in-repo.** `RealLCNFSemantics` is what "correct" means; nothing proves it matches what Lean executes.

---

## H1 — One proven path, Lean → `LNIR`

### Principle: a narrow waist that fails closed

```
LCNF.Decl ──lowerDecl──► Except Unsupported LNIRDecl      (one function, total, no IO)
                │
                └─ Unsupported ─► stock Lean C backend for that declaration
```

- **One lowering function.** `lowerDecl` is the only way `LNIR` is produced from Lean. No flag, stage or command selects another lowering.
- **One theorem.** `lower_refines : lowerDecl d = .ok d' → Refines (evalLCNF d) (evalLNIR d')`, stated once and hash-pinned like the `V` contracts.
- **Fail closed, never fall through.** What the proof does not cover returns a typed `Unsupported` and that declaration is compiled by the stock Lean backend. An unproved fast path is not an option the driver has.
- **Delete, don't keep.** A helper whose cases are covered by the proved path is removed in the same PR (`ΔLOC ≤ 0`, principle 5 of the README).
- **Backends frozen.** During H1 only the LLVM path through the proved `LLVMAst` printer is maintained. PTX, Metal, StableHLO, Hybrid and C-ABI emission are labelled *unverified tier* in `--help` and receive no features until H3.

### Tracks, in order

| Track | Work | Accept |
| :--- | :--- | :--- |
| **H1.0 Inventory** (read-only) | A generated matrix: each `LCNF` constructor and primitive × {proved, lowered unproved, rejected}. Coverage on three corpora: `con-leche`, `Batteries`, the C1 run tests (share of declarations that lower, and which rejection stops each of the rest). | Matrix is produced by a script in CI, not written by hand. |
| **H1.1 Attack the semantics** | Differential test of `RealLCNFSemantics` (as an interpreter) against stock Lean execution on the C1 corpus and a grammar fuzzer. Every divergence is a semantics bug to fix before anything is proved on top. | `mismatch_count == 0` on the corpus; divergences reduced into regression tests. |
| **H1.2 Single path** | Route every ingest through the proved lowering. Unproved helper cases become `Unsupported`. Delete what is now dead. | `Bridge.lean` has one callee; coverage from H1.0 does not drop on the proved subset; `ΔLOC < 0`. |
| **H1.3 Widen, one constructor at a time** | Order set by the H1.0 rejection counts on `con-leche` (expected: general recursion, closures and partial application, join points and `letrec`, signed integers). Each constructor is one leaf theorem with a frozen statement. | Leaf kernel-checked, `0 sorryAx`; the coverage number moves. |
| **H1.4 Close** | Compose the leaves into `lower_refines`. Mutate the lowerer and the statement (meta-spec): each mutant must be killed by the proof or the differential test. | Theorem pinned; mutant kill matrix in CI. |

**Exit of H1**: `con-leche` (≈1,700 LOC of pure Lean) lowers through `lowerDecl` with no `Unsupported`, and the LLVM build of it agrees with the stock-compiled binary on every `.olean` of the corpus.

### What makes this reliable

- **The trusted base is written down.** One file lists it: Lean's kernel, the `LCNF` semantics, the `LNIR` semantics, the LLVM printer, LLVM itself. A PR that grows it says so.
- **Trusted definitions are tested, since they cannot be proved.** H1.1 for the source side, the 3-way conformance suite (`G5`) for the target side.
- **Statements are frozen before proofs.** A leaf whose statement turns out false is recorded as a false goal and restated under the spec-change rules; it is not proved around.
- **The compiler checks itself.** Once `con-leche` compiles natively, the native kernel re-checks the compiler's own correctness proofs in CI, beside the C++ kernel (`--kernel both`).

---

## H2 — Build faster

### Measure first

The methodology is to find every bottleneck of the loop before optimizing one. The first H2 track is therefore a measurement, on a fixed corpus (`Batteries`, `PFR`, one `Mathlib` slice), of where wall time goes: import, elaboration, kernel check, compiled-import audit, I/O, process start. `B2` already states that cold elaboration dominates; the phase timings from `#408` make that a number.

**Every H2 track states its kill criterion with its target.** A change that does not move the end-to-end number on the corpus is deleted.

### Candidates, ranked by expected gain against risk

| # | Idea | Why it should pay | Risk / open question |
| :-- | :--- | :--- | :--- |
| 1 | **Do not elaborate what is already proved.** `LNIR_EXPR_V1` CAS proof replay (`#452`) on warm hits. | Removes the dominant phase on unchanged declarations. | Hit rate on real edit sequences is unmeasured. |
| 2 | **Stop redoing work.** Issues `#407`, `#433`, `#438`–`#440`: imports rebuilt per call, taint that disables reuse, closure copies. | Pure waste, already diagnosed. | None beyond the fixes themselves. |
| 3 | **Check declarations in parallel.** With the import prefix fixed, kernel checks are independent. `con-leche --jobs`, CoW zygote forks. | Scales with cores on replay-heavy commands (`ci-verify`, `pr-verify`, `--kernel both`). | Bounded by RAM, not cores; needs `#435` (caps reaching replay workers). |
| 4 | **Native pure-Lean kernel.** `con-leche` compiled by the H1 path, tuned for this one workload (arena allocation, hash-consed `Expr`, unboxed `Level`/`Name` ids). | A second, independent kernel that is cheap enough to always run; gives H1 its acceptance workload and H3 its benchmark. | Gains only where kernel time is a real share (measurement above). Upstream reports 0.69× the C++ kernel's instructions already. |
| 5 | **Distributed and remote reuse.** Content-addressed `.olean` and proof CAS shared across machines; prebuild on `lean.ci`. | Cold builds become downloads. | Trust: every reused artifact must be re-checked or carry a receipt. |
| 6 | **Faster elaboration itself.** Instance and `simp`-set caches kept across forks, tactic blocks elaborated speculatively in parallel, per-tactic profiles fed back to authors. | Attacks the dominant phase on cold builds. | Largest design surface; needs the profile first. |
| 7 | **GPU.** | See below. | See below. |

### GPU: a feasibility track, not a plan

Type checking is `whnf`, definitional equality and substitution over pointer-linked terms with data-dependent control flow. That is a poor fit for a GPU, and no result we know of shows a kernel checker gaining from one. The parts of a build that do fit are narrower:

- hashing and content addressing of `.olean` regions and CAS objects (batched BLAKE3);
- bit-parallel evaluation of closed, decidable terms (`decide`, `bv_decide`-shaped goals) across many inputs;
- bulk structural hashing for hash-consing large `Expr` DAGs.

One read-only feasibility track measures the share of build time these cover on the corpus. **Kill criterion**: under 10% of wall time addressable, or under 2× end to end on a prototype, and the track closes with its numbers recorded.

---

## H3 — Compiler performance by accelerator plugins

Starts when H1 has closed. Until then, Track A in [`OPEN_CHALLENGES.md`](./OPEN_CHALLENGES.md) stays open to outside contributions but is not staffed.

- **Plugins stay outside the trusted base.** An accelerator proposes (`rewritten_proof`, `LNIR_WIRE_V1` rewrite, cost profile); the kernel or the total `SymbolicTV` checker disposes. A wrong plugin costs time, never soundness.
- **Telemetry picks the work.** Per-pass and per-kernel timings, recorded locally by default, rank which pass or plugin is worth writing. The native kernel from H2 is the standing benchmark.
- **A pass that does not move the benchmark is deleted.**
- **Then the remaining backends.** PTX, Metal, StableHLO and the upstream bridges (`lean-mlir`, `LNSym`, `sail-riscv-lean`, `G3.3`) move from the unverified tier to proved, one target at a time, in the order telemetry says they are used.

---

## What this changes in the existing queue

- `G3.1` and `G3.2` become H1 and move ahead of all backend work.
- `G3.3` bridge extensions and `G4` emitter unification pause until H3, except fixes.
- `G1` (`con-leche` over real `.olean`) continues: it is the H1 exit workload and H2 candidate 4.
- The performance issues `#407`–`#443` and `G2` replay are H2 candidates 1–2 and continue.
- `G5` conformance continues: it is how the trusted semantics are tested.
