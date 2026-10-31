# B2: LNIR → CLIF → AArch64

Specification, not a completed correctness claim. Baseline: turbo-lean
`4966384`, clifv `5018b9509dc124154dbe08a5bd85862595d8eab7` (Lean
4.34.1). The compiler tree uses Lean 4.35.0. The target theorem is
`FV/E2E/FinalDirect.lean:23`, `E2E.backend_correct_final_of_lower`.

## Fragment F64 and entry contract

Pure, well-scoped, well-typed scalar LNIR: `i64` (UInt64) and `i1`
(Bool), scalar `letBind`, `ite`, bounded `seqFor`, and `ret`.
Scalar expressions include constants, variables, wrapping arithmetic,
unsigned division/remainder, bitwise operations, masked shifts,
comparisons, negation/not, select, and multiply-add. This covers
`LeanNative.IR.Codec.collatzStepsDecl` and needs no heap or call semantics.
The old `B2.SpecCore.declF` checks syntax only; successful lowering must
also check variable binding and operand/result types. It must reject
unsupported declarations with `Except.error`, never silently approximate.
In particular the evaluator's mixed-type simplifications (e.g. bool +
u64 zero) are not a license to compile ill-typed scalar programs.
Arguments must have the declared types and arity, including canonical
booleans. No theorem quantifies over arbitrary untyped argument lists.

`evalCode` is the existing LNIR semantics, not an evaluator defined via
the lowering. Its fuel argument does not bound evaluation: it recurses
structurally, with `seqFor` executing `hi.toNat - lo.toNat` steps. The loop
body receives the index and current accumulator; its `ret` returns the
next accumulator. The continuation receives only the final accumulator
in the outer environment. Empty/reversed ranges return the initial
accumulator. Binding/shadowing must follow `VarEnv.bind` exactly.

## Value relation

`Val.u64 n` corresponds to CLIF `⟨i64, n.toBitVec⟩`;
`Val.bool b` corresponds to `⟨i8, if b then 1#8 else 0#8⟩`.
Argument lists correspond pointwise with equal length and declared types.
Every function has exactly one scalar result. Scalar evaluation leaves
the LNIR heap unchanged; generated code has no memory effects.

## Division/remainder: total, with no DivGuarded premise

The actual lemmas in `B2/ProbeClif.lean` establish

```
evalBinOp .div (.u64 x) (.u64 0) = .ok (.u64 0)
evalBinOp .mod (.u64 x) (.u64 0) = .ok (.u64 x)
```

CLIF `Clif.Sem.udiv` and `urem` instead return `.error .intDivz` on
zero. Correct lowering uses `z = (y == 0)`, `safe = select(z, 1, y)`,
`q = udiv(x, safe)` or `r = urem(x, safe)`, and then
`select(z, 0, q)` or `select(z, x, r)`. A select around an unguarded
division is insufficient because CLIF evaluates instructions eagerly.
Prove this against the two existing semantics for every UInt64 x,y.
No DivGuarded run assumption remains. A constant power-of-two divisor
may instead use shift/mask with a proved identity. For collatz_steps,
division by two can therefore emit no CLIF `.div` at all.

## Executable lowering and identity of proved/emitted code

`lowerDecl : LNIRDecl → Except String Clif.Function` belongs under
`lean/LeanNative/Backend/`, and the compiler entrypoint must call that
same definition. Fresh CLIF SSA registers and block IDs are independent
of LNIR variable IDs; a typed environment resolves LNIR bindings.

* `letBind`: emit expression instructions, extend the environment, lower
  the continuation in the current block.
* `ite`: terminate with `brif`; lower each branch using the same outer
  environment and return continuation.
* `seqFor`: jump to a header with `(index, accumulator)` block parameters;
  unsigned `index < hi` branches to body/exit. The body return jumps
  back with `(index + 1, nextAccumulator)`. The exit resumes the outer
  continuation with the final accumulator. The index cannot overflow on
  a taken iteration because it is strictly below a UInt64 upper bound.
* `ret`: emit function `return`, or jump to the enclosing loop's return
  continuation. Nested loops must preserve this distinction.

Vendor byte-identical copies of this implementation and its LNIR
AST/Types/Value/Eval (plus Codec for the benchmark) into
`research/b2-proofs/vendor/`. CI must hash/compare each source pair and
fail on missing files or drift; it must also pin/check the clifv revision.
The version boundary is a source-identity claim, not permission for a
second implementation or a shadow CLIF AST. Any compiler integration or
Lean-version incompatibility remains an explicit incomplete requirement.

## Obligations and the exact backend boundary

| Obligation | Required fact | Discharge strategy |
| --- | --- | --- |
| O1 | Every successful F64 lowering has `Compile.functionE f = true` | Generic proof; executable validation may be part of lowering, with a generic soundness theorem. |
| O2 | `f.sig.params.map (·.ty) = d.params.map (clifTy ·.ty)` and returns `[clifTy d.retTy]` | Generic proof from constructor. |
| O3 | A successful, typed LNIR evaluation yields a CLIF `.returned [rv] m` at some sufficient fuel, with related result | Generic structural simulation if feasible; otherwise collatz_steps for all typed inputs first. Concrete examples are not this obligation. |
| O4 | Reachable lowered runs never trap or get stuck, and establish `TrapsExplicit env p cs` | Generic if feasible, otherwise collatz_steps first. No-trap alone does not exclude stuck. Fuel exhaustion is allowed. |
| O5 | Backend subset, dominance/scope, and actual compilation pipeline equations | Check collatz_steps with kernel `decide`; generalize later. |
| O6 | Discharge absent-call/try/TLS/extern/indirect and trap contracts | Generic structural absence where possible; concrete kernel checks for collatz_steps. |
| O7 | Compose O3–O6 with the backend theorem and extract the scalar result in AArch64 x0 | collatz_steps first, with only the backend's real machine/run premises remaining. |

`backend_correct_final_of_lower` takes the following exact groups:

1. `hsub : InSubset p f`, `hd : dominatedB f = true`,
   `hs : lowerScopeB f = true` (O1/O5). The public `Clif.runWith` simulation
   requires `p.func? f.name = some f`, because it looks up the entry by name.
   The backend theorem instead starts from `ClifEntry f args cs`, which
   already identifies the function in the active frame. For this call-free
   function, its initialized `runLoop` needs no further program lookup.
2. Pipeline equations `hl : lowerFunction f = .ok vc`,
   `hp : Backend.prepare vc = .ok vcp`,
   `hch : checkAlloc vcp rf = .ok ()`,
   `ha : lowerRFunc vcp rf = .ok af`,
   `he : emitFunc k af = .ok fa`, `hla : fa.layout = .ok fb` (O5).
   Produce actual artifacts/allocation, not existential assumptions that
   merely restate successful compilation. V1–V3 are discharged by clifv
   from dominance/scope; V4 is the allocation check.
3. `hC`, `hCT`, `hTls`, `hX`, `hXI`: respectively `CalleeOk`,
   conditionally `CalleeTryOk`, conditionally `TlsOk`, `XCallsOk`,
   `XCallsIndOk` for precisely the sites/signatures in that theorem (O6).
   Empty externs/signatures discharge `hX`/`hXI`; no prepared call sites
   discharge `CalleeOk.os`. Its unconditional `.pc` and `.ext` clauses
   remain explicit hook/program-preservation premises. Absence of try/TLS
   sites discharges `hCT`/`hTls`. `TrapsExplicit.of_tryFree` handles the
   try-free case provided its other real premises are met.
4. `hsym`, `hslot`, `hent : AbiEntry`, `hres : StackAvail`,
   `hbe : BodyEntry`, `hargs : ArgsIn`, `hcs : ClifEntry`, and
   `hrel : Rel.holds` are the backend's symbol, layout, machine-entry,
   stack, argument, and initial state relation contracts. Keep these
   explicit, with the same `frameW`/`RAFrame.compute` expressions as the
   source theorem. O2 connects typed LNIR arguments to `ArgsIn`.
5. `htr : TrapsExplicit env p cs` (O4/O6), then CLIF fuel. Its conclusion
   is `ArmRefines fb base ra (ArmStepX X H fa) s
   (Clif.runLoop env p fuel cs)`. This is not yet LNIR correctness.
   O3 supplies the returned CLIF result; unfold the returned case of
   `ArmRefines` to obtain `ArmRet` and `XHolds rv (xreg 0 ...)` (O7).

`explicitTrapInst` identifies `.div`, but absence of `.div` alone is not
a proof of semantic no-trap/no-stuck for arbitrary instructions or states.
Use the actual reachable-state and try-free lemmas. Do not assume a
stronger semantic theorem than clifv provides.

## Trusted base and reporting

Lean kernel plus `propext`, `Quot.sound`, and `Classical.choice` only in
the transitive axiom audit of each claimed result. No `native_decide`,
`sorryAx`, added axioms, invented semantics, or downstream modifications
to eth-act/clifv. Trust the stated source semantics, source identity CI,
Lean compilation/runtime, and the backend's explicit machine, hook,
ABI, and memory contracts; the theorem does not prove hardware or the
loader. Audit the actual theorem closure, not all imported declarations
(the dependency contains unrelated native-decided examples).

`research/B2-status.md` records O1–O7 individually as PROVED (with axiom
evidence), SORRY (incomplete), or BLOCKED, including
`BLOCKED_MISSING_DEPENDENCY` with source evidence when appropriate.
The old Lean draft is a historical statement sketch, not proof evidence.
Push checkpoints at least every 30 minutes. Never open/merge a PR.

Out of scope: heap/RC, calls, parFor, 256-bit arithmetic, GPU/SIMD,
frontend Lean-to-LNIR correctness, and replacing all existing backends.
