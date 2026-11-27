import LeanNative.Semantics.EvalRec
import LeanNative.IR.RealLCNFRecSemantics
import LeanNative.Proofs.RealLCNFBridgeProofs
import LeanNative.Proofs.RealLCNFBridge.CallsF

/-!
## L3 contract (roadmap/HORIZONS.md, H1 rung L3 "Recursion and loops")

Authoritative row (`roadmap/HORIZONS.md`): "L3 Recursion and loops — Fuel-indexed calls;
`LNIR` gets a join-point / loop construct that replaces inlining a join point at every jump.
Self and mutual recursion proved. | Needs the theorem statement redesigned, not one more
case." Leaf row: files `IR/AST.lean`, `Proofs/LowerRec.lean`; needs L2; accept inherited
from L2: "leaf `0 sorryAx`; matrix moves".

This is the contract-first statement of the exact signatures L3 states for recursion and
loops, in the L1/L2 form (`RealLCNFBridgeProofs.lean:13-127`, `LowerCalls.lean:1-294`): a
doc-block contract rather than `sorry` skeletons, because the repo gates hold `0 sorryAx`
on every commit. Part I lands proved, verbatim, in the follow-up commits of this same
leaf. Part II freezes the recursion-headline signatures H1.4 builds against; its proofs
are sequenced after the L2 lane's F-proofs merge (the reason is named there — it is a
pipeline-sequencing fact at the bytes, not an unprovability).

Status (2026-11-26): Part I is PROVED at the end of this file — the 14 theorems
with the statements below plus the four lemmas amendment 2 adds, registered in
`AxiomAudit.lean` (874 → 892; L2's raise landed first), each depending only on `propext`,
`Classical.choice` and `Quot.sound`; the executable guards are in
`Tests/RealLCNFRecTests.lean`. Two shape notes. `DeclEnvLowersR` is a conjunction of
recursive `Prop`s (the positional clauses `DeclEnvLowersPosR` and per-entry `CtxMapsEnvR`
coherence): the strict-proofs policy forbids a new `inductive` under `Proofs/` (L2's
`DeclEnvLowers` has the same shape for the same reason). `reservedRuntimeCallee` is
defined as L2's `reservedRuntimeName`, so the two lanes share one predicate. Part II is
NOT proved and stays OPEN: amendment 3 fixed the step rule its first refutation rested
on, and the remaining work is listed in "Part II status" below.

Pipeline note: this leaf was cut against the L2 CONTRACT; L2 has since landed its F-stack,
and Part I is proved against the landed definitions: `FuncEnv` and `evalCodeF`
(`Semantics/Eval.lean`), `DeclEnv`, `evalStepF` and `evalRealLCNFDeclF`
(`IR/RealLCNFCallSemantics.lean`), `reservedRuntimeName` with its non-capture lemmas and
the per-case step mirrors (`Proofs/RealLCNFBridge/CallsF.lean`, imported here), and
`CtxMapsEnv`, `DeclEnvLowers` and the proved headline `lowerRealLCNFDecl_soundF`
(`Proofs/LowerCalls.lean`). L2 dropped its contract's `CodeRefinesF`, which had no
consumer once the compression post-pass was removed (`LowerCalls.lean`'s definitions
paragraph). Nothing here edits L2's files or proves L2's theorems. L1 removed
the post-pass (`applyValidatedCompression` is defined nowhere in the tree), so the
driver-shaped soundness statement is `lowerRealLCNFDecl_sound` and this contract names no
post-pass symbol. The sha-pinned files (`scripts/lcnf_coverage_results.json` pins
`IR/RealLCNFSemantics.lean`, `IR/RealLCNFBridge.lean`, `IR/Bridge.lean`,
`IR/BridgeHelpers*.lean`, `Proofs/RealLCNFBridgeProofs.lean`) are read, cited and proved
ABOUT, never edited; every new definition goes in new files, as L2's layering prescribes.

Amendment (2026-11-26; names unchanged, entry/hypothesis shape only): environment
ENTRIES carry their own context and lowering fuel. The driver builds a PER-DECLARATION
`RealBridgeCtx` — `buildRealBridgeCtxM` derives `paramTypeMap`, `allowStage1DHeap`,
`ctorLayouts` and `typeOverrides` from each declaration's own code
(`BridgeHelpers/RealBridgeCtxAndSlices.lean:276-531`) — so a `DeclEnvLowersR` fixing ONE
`ctx` and ONE `fuel` across every entry, and a call rule running the callee under the
CALLER'S `ctx`, would describe module environments the driver never builds; the first cut
of this contract did exactly that. Amended shape: `DeclEnvLowersR` is indexed by
`List (Decl .impure × RealBridgeCtx × Nat)` with the per-entry lowering hypothesis
`lowerRealLCNFDecl fuel_i ctx_i sd ld.name = .ok ld`; the R evaluators take
`Δ : List (Decl .impure × RealBridgeCtx)` (`declEnvR` projects the lowering environment
onto it) and run a callee's body under ITS OWN paired context, the caller's `ctx` binder
governing only the caller's own clauses; the EVALUATION fuel stays the single step budget
— distinct from the per-entry LOWERING fuel, never per-entry. `CodeRefinesR` (the LNIR
side carries no `RealBridgeCtx`) and `lowerRealLCNFDecl_soundR_base` (already one
declaration with its own context and the pointwise freshness hypothesis) are unchanged;
every Part II frozen name stays. The L2 lane applied the same-shape correction to its
`DeclEnv`/`DeclEnvLowers` (entries `Decl × RealBridgeCtx × Nat`), so the two lanes stay
parallel and the fold meets one entry shape.

Amendment 2 (2026-11-26; a devil's-advocate review, five
findings folded before the Part II statements freeze):

- F1, coherence (the Part II statements were false as first frozen). The source rule
  looks a callee up by Lean name (`lookupDeclRec? Δ fn`), the target by mangled symbol
  (`lookupFuncRec? Φ sym` with `ctx.findLocalCallee? fn = some sym`), and the first cut
  of `DeclEnvLowersR` related only each entry's OWN name to its own lowered name.
  Witness: `Δ = [(A, ctxA, _), (B, ctxB, _)]`, `Φ = [ldA "A", ldB "B"]`, each entry's
  context correct, but the top context maps `A ↦ "B"`; the body `let x := A (); ret x`
  runs A on the source side and B on the target side. Fixed as L2 fixed the same gap:
  `CtxMapsEnvR ctx Δ Φ` (position by position, a context that maps a source name maps it
  to that position's lowered name) is required per entry, for the entry's own context,
  inside `DeclEnvLowersR`, and as `h_map` for the top caller in every Part II statement.
  It ranges over the WHOLE lists, not the tail as in L2: R's lookup is not stratified,
  and a recursive call reaches earlier entries. `lookupDeclRec?_align` and
  `declEnvLowersR_lookup_align` prove the hypotheses suffice: at a coherent call site the
  two lookups land on one position, the LNIR entry there is the lowering of the source
  entry there, and the callee's own context coheres again, so its nested call sites
  align too. Rejected: the strong equality `ctx.findLocalCallee? sd.name = some ld.name`
  at every position (L2's review showed it fails for a call chain under per-declaration
  `localCallees`, where a context need not know every name).
- F4, strict arity. `evalCodeR`'s call arm bound parameters by `zip`, so extra arguments
  were dropped and missing ones stayed unbound; L2's `evalCodeF` errors on a count
  mismatch because the source side's `bindParams` is strict. The call arm now errors
  `.typeError "call arity mismatch"` when `vals.length ≠ ld.params.length`, and
  `evalCodeR_call_unfold`'s right-hand side states the check, so the two lanes' LNIR call
  rules agree. Guard: a two-argument call to a one-parameter callee errors
  (`Tests/RealLCNFRecTests.lean`, family 5); an empty argument list would not pin it,
  since the unbound parameter errors either way.
- F2, fuel monotonicity. One evaluation fuel with per-entry lowering fuel needs
  `evalStepR` monotone in fuel (L2 avoided the obligation with per-entry evaluation
  fuel). Proved: `evalStepR_fuel_mono`, with `hasJmpToPure_false_succ`. The review's worry
  that a deeper search could turn an accepted join point into a "recursive join point"
  error runs the other way at the bytes: `hasJmpToPure 0` answers `true`, so more fuel can
  only turn a "recursive" verdict into "non-recursive". Rejected: per-entry evaluation
  fuel. Under the full environment a self-call would re-enter at the same entry fuel, so
  the evaluator would have no decreasing measure and a diverging source program no budget
  to exhaust.
- F3, one non-capture lemma. `evalExpr_call_ok_reserved` is proved from L2's
  `FuncEnv.callTarget?_of_evalExpr_ok` through the definitional alias, instead of listing
  the intrinsic names by hand, so a change to `reservedRuntimeName` or to `evalExpr`'s
  intrinsic set moves one proof, not two.
- F5, this block. The pipeline note, the `reservedRuntimeCallee` and `DeclEnvLowersR`
  contract text, the audit pin and the Part II sequencing text below describe the landed
  code.

Amendment 3 (2026-11-26; the Part II status decision, and
review findings 1-2): the resolved local-call rule binds the call result at the
caller's declared lowered type `rawTy`. Until this amendment it bound at
`if isUnboxedScalarOrTuple rawTy then rawTy else .i64`, the unresolved `.fap` arm's
fallback, while the lowering allocates the destination at `rawTy` itself
(`IR/RealLCNFBridge.lean`, the `.fap` arm with `ctx.findLocalCallee? fnName = some sym`)
and L2's `evalStepF` binds at `some rawTy`. The witness is guard family 6 of
`Tests/RealLCNFRecTests.lean`: callee `l3_mk x = ObjBox.left (box x)` returns a fresh
object, caller `l3_use x = let o := l3_mk x; dec o; 0`, one context with heap lowering
on, `ObjBox.left`'s layout, and `l3_mk` local. Under the old rule the source run stored `o`
at `.i64`, its `dec` was a no-op, and the run returned `0` with the object live, while the
lowered caller under `Φ` and L2's run returned `0` with it freed. Under the amended rule
the three runs agree exactly on value and heap; the family-6 guards fail at the old rule
and pass at this one. The Part I statement `evalStepR_localCall_unfold` pinned the old
binding, so its right-hand side changes with the rule: a frozen statement changes here
because the semantics it described were wrong. Its continuation was
`evalStepR Δ fuel ctx (env.bind decl.fvarId v none (some (if isUnboxedScalarOrTuple
(lowerGroundImpureTypeWith ctx decl.type) then lowerGroundImpureTypeWith ctx decl.type
else .i64))) st' (.inl k)` and is now
`evalStepR Δ fuel ctx (env.bind decl.fvarId v none (some (lowerGroundImpureTypeWith ctx
decl.type))) st' (.inl k)`. Nothing else moved, and the build of the amendment's commit
checked it: `evalStepR_nil` never reaches the arm (an empty `Δ` misses),
`evalStepR_fuel_mono`'s unchanged proof script re-ran green against the new rule, and
every earlier guard's call result is `UInt64`, whose lowered type the old rule kept.
Rejected: keeping the `.i64` binding with a warning, which would have certified a step
rule that leaks objects on heap-typed local calls to keep a refutation of the headline
standing.

Amendment 4 (2026-11-26; a review, three rows):

- `DeclEnvLowersPosR` drops its per-entry clause `ctx.findLocalCallee? sd.name = some
  ld.name` (each entry's own context knows its own name). No proof used it, the maps-to
  half is already in the per-entry `CtxMapsEnvR`, L2's `DeclEnvLowers` has no such
  clause, and it excluded the suite's own even/odd environment, whose contexts know only
  their partner, contradicting F1's reason for rejecting the strong equality. A Part II
  case that needs a name to be present states it where it is used.
- The arity guard gains the too-few direction with the exact error: a two-parameter
  callee whose body reads only the first parameter, called with one argument, must end
  on "call arity mismatch". A `≤` mutant of the check passed the two earlier guards.
- `evalStepR_fuel_mono` keeps its lockstep search; its docstring says how the script
  fails when `evalStepR` changes, and amendment 3's claim that the rule change left it
  untouched is a checked fact. `evalExpr_call_ok_reserved` and `lookupDeclRec?_align`
  use `simp only`, like the rest of the file.

### What the AST actually carries for recursion and loops (read first, stated only if it exists)

- `LNIRExpr.call fn args retTy isExtern` (`IR/AST.lean:80`) — the one LNIR construct a
  recursive source call lowers to. The driver's context maps the declaration's OWN name:
  `buildRealBridgeCtxM` builds `localCallees` from
  `(st.localDeclNames.push st.selfDeclName)` (`BridgeHelpers/RealBridgeCtxAndSlices.lean:304-317`),
  so a SELF call is lowered today (`lowerImpureStepPure`, `.fap` arm with
  `ctx.findLocalCallee? fnName = some sym`, `IR/RealLCNFBridge.lean:722-729`) and sits in
  the matrix as `LetValue.fap.local_call` / `lowered_unproved` — vacuous because
  `evalLetValue` errors `.unsupportedCall` on every ctx-local call
  (`IR/RealLCNFSemantics.lean:563-565`). Mutual calls lower the same way when both names
  are in `localCallees`.
- `LNIRCode.seqFor` (`IR/AST.lean:98`) — the bounded counted loop LNIR already has;
  `evalCode` evaluates it structurally. No LCNF construct lowers to it on the proved path;
  it needs no L3 change and gets fuel-R mirrors like every other clause.
- `Lean.Compiler.LCNF.Code.jp/.jmp` — source-side join points. Non-recursive ones are
  proved (L1). RECURSIVE ones — the LCNF spelling of a loop — are rejected at the bytes by
  BOTH pinned artifacts: the lowering errors
  (`IR/RealLCNFBridge.lean:858-860`) and the semantics errors
  (`IR/RealLCNFSemantics.lean:840-842`), each gated on `hasJmpToPure`
  (`IR/RealLCNFShared.lean:267-285`). Part I pins that fail-closed behavior as kernel
  theorems; replacing it with loop IR is the named exclusion E2 below.
- `Lean.Compiler.LCNF.Code.fun` — the letrec-shaped local-function construct — carries
  `(h : pu = .pure := by purity_tac)` (toolchain `Lean/Compiler/LCNF/Basic.lean:382`), so
  it is UNINHABITABLE in the `.impure` phase this pipeline lowers. There is nothing
  non-vacuous to state; exclusion E1.

### The L3 redesign: fuel-indexed calls over the FULL environment

L2's F-semantics runs a callee under the STRICT SUFFIX of the environment
(`FuncEnv.lookup?` pairs the hit with its tail), so chains of forward calls evaluate and a
self or backward call misses — termination is lexicographic on `(Φ.length, code)` and the
simulation can induct on the stratification. That statement shape cannot speak about
recursion at all; HORIZONS says L3 "needs the theorem statement redesigned, not one more
case". The redesign: the callee runs under the WHOLE environment, and the budget is FUEL —
a `Φ`-bound call consumes one unit, so `fuel` bounds the depth of environment-call nesting
and self/mutual recursion evaluates. Lookup returns the hit alone (no suffix); termination
is lexicographic on `(fuel, code)` on the LNIR side and structural on `fuel` on the LCNF
side (where `evalStep` already burns fuel at every step).

### New definitions (Part I; land with the proofs in this leaf)

In `lean/LeanNative/Semantics/EvalRec.lean` (NEW file; namespace `LeanNative.Semantics`;
imports `LeanNative.Semantics.Eval` and `LeanNative.IR.AST` only — no bridge import).
`List LNIRDecl` is spelled out rather than L2's `FuncEnv` abbrev so this file cannot
collide with L2's append to `Eval.lean`; the two spellings are definitionally one type and
the fold may unify them.

```
/-- First declaration named `fn`. The hit alone — the callee re-runs under the SAME
    full environment, which is what admits self and mutual recursion. -/
def lookupFuncRec? : List LNIRDecl → String → Option LNIRDecl

def evalCodeR (Φ : List LNIRDecl) : Nat → VarEnv → HeapState → LNIRCode →
    Except UBError (Val × HeapState)
```

`evalCodeR` mirrors `evalCode` clause for clause (same `evalExpr`, same `evalSeqLoop` /
`evalParFor` helpers, every same-fuel recursive occurrence at the same `Φ`) with ONE new
rule: on `.letBind dst ty (.call fn args retTy false) k` with
`lookupFuncRec? Φ fn = some ld`,

- at fuel `0`: `.error .fuelExhausted` (the budget check comes FIRST, before `args` are
  read — the evaluator budget shape of `evalParFor`, never source UB);
- at fuel `fuel' + 1`: `evalVarList env args`; an argument count other than
  `ld.params.length` is `.error (.typeError "call arity mismatch")` (amendment 2, below);
  otherwise the callee body
  `evalCodeR Φ fuel' ((ld.params.zip vals).foldl (fun acc (p, val) => acc.bind p.id val)
  VarEnv.empty) st ld.body` — the declaration-entry binding convention of
  `lowerRealLCNFDecl_sound` — and on `.ok (v, st')` the continuation
  `evalCodeR Φ (fuel' + 1) (env.bind dst v) st' k` at the ORIGINAL fuel. Fuel counts
  Φ-call DEPTH, not call count: sequential calls at one level each see the same budget.

An extern call (`isExtern = true`), a lookup miss, and every non-call binding delegate to
`evalExpr` exactly as `evalCode` does, so `Φ = []` is the old evaluator by theorem
(`evalCodeR_nil`). Termination: `termination_by` lexicographic `(fuel, code)`.

In `lean/LeanNative/IR/RealLCNFRecSemantics.lean` (NEW file; namespace
`LeanNative.IR.RealLCNFSemantics`; imports `LeanNative.IR.RealLCNFSemantics` only, so the
H1.1 separation pin (`Tests/RealLCNFSeparationPin.lean`) is preserved — the same layering
L2 contracts for its `IR/RealLCNFCallSemantics.lean`, which this file does not touch).
Environment entries are PAIRS carrying each callee's own context, per the amendment note:

```
/-- First entry whose declaration's `.name` is `fn`. The hit alone (no suffix), paired
    with the callee's own context. -/
def lookupDeclRec? : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx) → Lean.Name →
    Option (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx)

def evalStepR (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx)) (fuel : Nat)
    (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
    (target : Lean.Compiler.LCNF.Code .impure ⊕
      (Val × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure))) :
    Except UBError (Val × HeapState)

def evalRealLCNFCodeR (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx))
    (fuel : Nat) (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
    (code : Lean.Compiler.LCNF.Code .impure) : Except UBError (Val × HeapState)

def evalRealLCNFDeclR (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx))
    (fuel : Nat) (ctx : RealBridgeCtx) (decl : Lean.Compiler.LCNF.Decl .impure)
    (args : List Val) (st : HeapState := HeapState.empty) : Except UBError (Val × HeapState)
```

`evalStepR` mirrors `evalStep` clause for clause (same fuel-structural recursion with
`.error .fuelExhausted` at `0`, same `evalLetValue`, same `storedTy`/`storedCtor`
machinery, same join-point, `cases`, rc and mutation handling, every recursive occurrence
at the step's decremented fuel, the same `Δ` and — on the caller's own clauses — the same
`ctx`) with ONE new rule, replacing exactly the arm the old semantics deliberately errors
on: on `.let decl k` with `decl.value = .fap fn args _` and
`(ctx.findLocalCallee? fn).isSome`,

- `lookupDeclRec? Δ fn = some (sd, sdCtx)`: `evalArgs env.vals args.toList`; `sd.value`
  must be `.code c` (`.extern _` errors `.unsupportedCall fn.toString`); then
  `bindParams sdCtx true LEnv.empty sd.params.toList vals` (the declaration-entry
  convention of `evalRealLCNFDecl`, under the CALLEE'S OWN context); the callee body runs
  as `evalStepR Δ fuel sdCtx env' st (.inl c)` at the step's decremented fuel UNDER THE
  FULL `Δ` and the callee's paired `sdCtx` — the differences from L2's rule, and what
  makes a self or mutual call evaluate under the context the driver actually builds for
  that callee; its `.ok (v, st')` binds into the caller at `storedTy := rawTy`, no ctor
  (`rawTy` from the CALLER'S `ctx`: the type the lowering allocates the destination at,
  as L2's `evalStepF` binds; amendment 3), and continues with `k` at the decremented fuel
  under `Δ` and the caller's `ctx`.
- lookup miss: `.error (.unsupportedCall fn.toString)` — byte-for-byte the old behavior,
  so `Δ = []` is the old semantics (theorem `evalStepR_nil`).

`evalRealLCNFCodeR`/`evalRealLCNFDeclR` mirror `evalRealLCNFCode`/`evalRealLCNFDecl` over
`evalStepR`.

In this file, namespace `LeanNative.Proofs`:

```
/-- Reserved runtime symbols `evalExpr` interprets as intrinsics
    (`lean_native_*`, `lean_mark_mt`); a lowered local callee must not shadow them.
    Defined as L2's `reservedRuntimeName` (`RealLCNFBridge/CallsF.lean`): one predicate
    under the L3 spelling, so the lanes cannot disagree on it. -/
def reservedRuntimeCallee (s : String) : Bool := reservedRuntimeName s

/-- The evaluation-side environment of a lowering environment: each entry keeps its
    declaration and its own context; the per-entry LOWERING fuel is a lowering-time
    quantity, not an evaluation input (the evaluation fuel stays the single step
    budget). -/
def declEnvR (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx × Nat)) :
    List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx) :=
  Δ.map fun e => (e.1, e.2.1)

/-- A context's mangled-name map COHERES with an environment pairing, position by
    position: WHEN it maps a source declaration's name, it maps it to the lowered
    declaration's name at the same position (L2's `CtxMapsEnv`, for the R entry shape;
    amendment 2, F1). Length-mismatched lists cohere never. -/
def CtxMapsEnvR (ctx : RealBridgeCtx) :
    List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx × Nat) → List LNIRDecl → Prop
  | [], [] => True
  | (sd, _, _) :: Δ, ld :: Φ =>
      (∀ m, ctx.findLocalCallee? sd.name = some m → m = ld.name) ∧ CtxMapsEnvR ctx Δ Φ
  | _, _ => False

/-- The positional clauses: the lowering hypothesis holds at the entry's own context and
    fuel, lowered names are unreserved, and no later lowered name repeats an earlier one.
    Whether a context knows a name is left to the coherence clause (amendment 4). -/
def DeclEnvLowersPosR :
    List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx × Nat) → List LNIRDecl → Prop
  | [], [] => True
  | (sd, ctx, fuel) :: Δ, ld :: Φ =>
      lowerRealLCNFDecl fuel ctx sd ld.name = .ok ld ∧
      reservedRuntimeCallee ld.name = false ∧
      (∀ ld' ∈ Φ, ld'.name ≠ ld.name) ∧
      DeclEnvLowersPosR Δ Φ
  | _, _ => False

/-- Pointwise "Δ lowers to Φ" for the FULL-environment semantics, with PER-ENTRY context
    and lowering fuel (the driver builds a per-declaration `RealBridgeCtx`; amendment 1):
    the positional clauses, and every entry's own context coheres with the WHOLE pairing.
    Name freshness alone cannot align a lookup keyed on a Lean name with one keyed on a
    mangled symbol; coherence pins the symbol a context resolves to the position the
    source lookup lands on, and freshness keeps every other position from matching it
    (`declEnvLowersR_lookup_align`). Recursive `Prop`s, not an `inductive`: the
    strict-proofs scope admits no new `inductive` under `Proofs/`. -/
def DeclEnvLowersR (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx × Nat))
    (Φ : List LNIRDecl) : Prop :=
  DeclEnvLowersPosR Δ Φ ∧ ∀ e ∈ Δ, CtxMapsEnvR e.2.1 Δ Φ

/-- `CodeRefines` with the recursion-capable environment (the L3 form of refinement). -/
def CodeRefinesR (Φ : List LNIRDecl) (src tgt : LNIRCode) : Prop :=
  ∀ fuel env st v st', evalCodeR Φ fuel env st src = .ok (v, st') →
    evalCodeR Φ fuel env st tgt = .ok (v, st')
```

### Part I — theorems proved by this leaf (14, plus amendment 2's four; appended to `AxiomAudit.lean`, 874 → 892 at the proving tip)

Conservativity — the old semantics is the empty-environment instance:

```
theorem evalCodeR_nil (fuel : Nat) (env : VarEnv) (st : HeapState) (c : LNIRCode) :
    evalCodeR [] fuel env st c = evalCode fuel env st c

theorem evalStepR_nil (fuel : Nat) (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
    (target : Lean.Compiler.LCNF.Code .impure ⊕
      (Val × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure))) :
    evalStepR [] fuel ctx env st target = evalStep fuel ctx env st target

theorem evalRealLCNFDeclR_nil (fuel : Nat) (ctx : RealBridgeCtx)
    (decl : Lean.Compiler.LCNF.Decl .impure) (args : List Val) (st : HeapState) :
    evalRealLCNFDeclR [] fuel ctx decl args st = evalRealLCNFDecl fuel ctx decl args st
```

The redesigned statement's structural lemma — fuel monotonicity of the recursion-capable
evaluator (`evalCode_fuel_mono_step`'s successor; where the old lemma is one structural
pass, this one is a genuine induction on the call-depth budget):

```
theorem evalCodeR_fuel_mono (Φ : List LNIRDecl) (fuel : Nat) (env : VarEnv)
    (st : HeapState) (c : LNIRCode) (v : Val) (st' : HeapState) :
    evalCodeR Φ fuel env st c = .ok (v, st') → evalCodeR Φ (fuel + 1) env st c = .ok (v, st')
```

The call rule, pinned as kernel equations (kills call-as-noop, wrong-env, wrong-fuel and
skip-the-budget mutants at the statement level):

```
theorem evalCodeR_call_fuel_zero (Φ : List LNIRDecl) (env : VarEnv) (st : HeapState)
    (dst : VarId) (ty : LNIRType) (fn : String) (args : List VarId) (retTy : LNIRType)
    (k : LNIRCode) (ld : LNIRDecl) (hlk : lookupFuncRec? Φ fn = some ld) :
    evalCodeR Φ 0 env st (.letBind dst ty (.call fn args retTy false) k) =
      .error .fuelExhausted

theorem evalCodeR_call_unfold (Φ : List LNIRDecl) (fuel : Nat) (env : VarEnv)
    (st : HeapState) (dst : VarId) (ty : LNIRType) (fn : String) (args : List VarId)
    (retTy : LNIRType) (k : LNIRCode) (ld : LNIRDecl)
    (hlk : lookupFuncRec? Φ fn = some ld) :
    evalCodeR Φ (fuel + 1) env st (.letBind dst ty (.call fn args retTy false) k) =
      match evalVarList env args with
      | .error e => .error e
      | .ok vals =>
        if vals.length = ld.params.length then
          match evalCodeR Φ fuel
              ((ld.params.zip vals).foldl (fun acc (p, val) => acc.bind p.id val) VarEnv.empty)
              st ld.body with
          | .error e => .error e
          | .ok (v, st') => evalCodeR Φ (fuel + 1) (env.bind dst v) st' k
        else .error (.typeError "call arity mismatch")

theorem evalStepR_localCall_unfold (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx))
    (fuel : Nat) (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
    (decl : Lean.Compiler.LCNF.LetDecl .impure) (k : Lean.Compiler.LCNF.Code .impure)
    (fn : Lean.Name) (args : Array (Lean.Compiler.LCNF.Arg .impure))
    (sd : Lean.Compiler.LCNF.Decl .impure) (sdCtx : RealBridgeCtx)
    (hval : decl.value = .fap fn args rfl)
    (hloc : (ctx.findLocalCallee? fn).isSome = true)
    (hlk : lookupDeclRec? Δ fn = some (sd, sdCtx)) :
    evalStepR Δ (fuel + 1) ctx env st (.inl (.let decl k)) =
      match evalArgs env.vals args.toList with
      | .error e => .error e
      | .ok vals =>
        match sd.value with
        | .extern _ => .error (.unsupportedCall fn.toString)
        | .code c =>
          match bindParams sdCtx true LEnv.empty sd.params.toList vals with
          | .error e => .error e
          | .ok env' =>
            match evalStepR Δ fuel sdCtx env' st (.inl c) with
            | .error e => .error e
            | .ok (v, st') =>
              evalStepR Δ fuel ctx
                (env.bind decl.fvarId v none (some (lowerGroundImpureTypeWith ctx decl.type)))
                st' (.inl k)

theorem evalStepR_localCall_miss (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx))
    (fuel : Nat) (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
    (decl : Lean.Compiler.LCNF.LetDecl .impure) (k : Lean.Compiler.LCNF.Code .impure)
    (fn : Lean.Name) (args : Array (Lean.Compiler.LCNF.Arg .impure))
    (hval : decl.value = .fap fn args rfl)
    (hloc : (ctx.findLocalCallee? fn).isSome = true)
    (hlk : lookupDeclRec? Δ fn = none) :
    evalStepR Δ (fuel + 1) ctx env st (.inl (.let decl k)) =
      .error (.unsupportedCall fn.toString)
```

Environment-extension conservativity — a run of the call-free semantics is untouched by
ANY environment of unreserved names (what makes the redesigned statement conservative over
the whole L1-proved corpus):

```
theorem evalExpr_call_ok_reserved (env : VarEnv) (st : HeapState) (fn : String)
    (args : List VarId) (retTy : LNIRType) (isExt : Bool) (r : Val × HeapState)
    (h : evalExpr env st (.call fn args retTy isExt) = .ok r) :
    reservedRuntimeCallee fn = true

theorem evalCodeR_extend_of_ok (Φ : List LNIRDecl) (fuel : Nat) (env : VarEnv)
    (st : HeapState) (c : LNIRCode) (v : Val) (st' : HeapState)
    (hfresh : ∀ ld ∈ Φ, reservedRuntimeCallee ld.name = false)
    (h : evalCode fuel env st c = .ok (v, st')) :
    evalCodeR Φ fuel env st c = .ok (v, st')

theorem DeclEnvLowersR.fresh
    (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx × Nat)) (Φ : List LNIRDecl)
    (h : DeclEnvLowersR Δ Φ) :
    ∀ ld ∈ Φ, reservedRuntimeCallee ld.name = false

theorem lowerRealLCNFDecl_soundR_base (fuel : Nat) (ctx : RealBridgeCtx)
    (Φ : List LNIRDecl)
    (decl : Lean.Compiler.LCNF.Decl .impure) (args : List Val) (hst hst' : HeapState)
    (v : Val) (d : LNIRDecl) (mangled : String)
    (hfresh : ∀ ld ∈ Φ, reservedRuntimeCallee ld.name = false)
    (h_lower : lowerRealLCNFDecl fuel ctx decl mangled = .ok d)
    (h_eval : evalRealLCNFDecl fuel ctx decl args hst = .ok (v, hst')) :
    evalCodeR Φ fuel
      ((d.params.zip args).foldl (fun acc (p, val) => acc.bind p.id val) VarEnv.empty)
      hst d.body = .ok (v, hst')
```

`lowerRealLCNFDecl_soundR_base` is the no-regression half of the redesign: every
declaration L1's `lowerRealLCNFDecl_sound` covers satisfies the R-shaped conclusion under
every well-named environment (with `Φ = []` and `evalCodeR_nil` it collapses to L1's
statement), so H1.4 can state its mutant matrix against the R-form alone. Its freshness
hypothesis is the pointwise consequence of `DeclEnvLowersR` (`DeclEnvLowersR.fresh`), kept
in the weaker pointwise form so the theorem carries no droppable structure.

Fail-closed honesty for the loop constructs the pinned files reject (the kernel-checked
record that `Code.jp.recursive` stays `rejected` at these bytes — stated ABOUT the pinned
definitions, editing nothing):

```
theorem evalStep_recursive_jp_unsupported (fuel : Nat) (ctx : RealBridgeCtx) (env : LEnv)
    (st : HeapState) (decl : Lean.Compiler.LCNF.FunDecl .impure)
    (k : Lean.Compiler.LCNF.Code .impure)
    (h : hasJmpToPure fuel decl.fvarId (.inl decl.value) = true) :
    evalStep (fuel + 1) ctx env st (.inl (.jp decl k)) =
      .error (.unsupportedCall "recursive join point")

theorem lowerImpureStepPure_recursive_jp_rejected (fuel : Nat) (ctx : RealBridgeCtx)
    (st : RealBridgeState) (decl : Lean.Compiler.LCNF.FunDecl .impure)
    (k : Lean.Compiler.LCNF.Code .impure)
    (h : hasJmpToPure fuel decl.fvarId (.inl decl.value) = true) :
    lowerImpureStepPure (fuel + 1) ctx st (.inl (.jp decl k)) =
      .error s!"[lean-native] unsupported recursive join point `{decl.fvarId.name}`: no qualified loop lowering"
```

Amendment 2's four, registered with the 14 (F2: fuel monotonicity of the LCNF evaluator;
F1: the lookup alignment the coherence hypotheses buy):

```
theorem hasJmpToPure_false_succ :
    ∀ (fuel : Nat) (t : Lean.FVarId)
      (target : Lean.Compiler.LCNF.Code .impure ⊕ List (Lean.Compiler.LCNF.Alt .impure)),
      hasJmpToPure fuel t target = false → hasJmpToPure (fuel + 1) t target = false

theorem evalStepR_fuel_mono (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx)) :
    ∀ (fuel : Nat) (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
      (target : Lean.Compiler.LCNF.Code .impure ⊕
        (Val × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure)))
      (r : Val × HeapState),
      evalStepR Δ fuel ctx env st target = .ok r →
      evalStepR Δ (fuel + 1) ctx env st target = .ok r

theorem lookupDeclRec?_align :
    ∀ (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx × Nat)) (Φ : List LNIRDecl),
      DeclEnvLowersPosR Δ Φ →
      ∀ (ctx : RealBridgeCtx) (fn : Lean.Name) (sym : String)
        (sd : Lean.Compiler.LCNF.Decl .impure) (sdCtx : RealBridgeCtx),
      CtxMapsEnvR ctx Δ Φ → ctx.findLocalCallee? fn = some sym →
      lookupDeclRec? (declEnvR Δ) fn = some (sd, sdCtx) →
      ∃ fuelD ld, (sd, sdCtx, fuelD) ∈ Δ ∧ lookupFuncRec? Φ sym = some ld ∧
        lowerRealLCNFDecl fuelD sdCtx sd ld.name = .ok ld

theorem declEnvLowersR_lookup_align
    (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx × Nat)) (Φ : List LNIRDecl)
    (h : DeclEnvLowersR Δ Φ) (ctx : RealBridgeCtx) (fn : Lean.Name) (sym : String)
    (sd : Lean.Compiler.LCNF.Decl .impure) (sdCtx : RealBridgeCtx)
    (hmap : CtxMapsEnvR ctx Δ Φ) (hsym : ctx.findLocalCallee? fn = some sym)
    (hlk : lookupDeclRec? (declEnvR Δ) fn = some (sd, sdCtx)) :
    ∃ fuelD ld, lookupFuncRec? Φ sym = some ld ∧
      lowerRealLCNFDecl fuelD sdCtx sd ld.name = .ok ld ∧ CtxMapsEnvR sdCtx Δ Φ
```

Expected helper lemmas landing with the proofs (shapes not frozen by this contract):
`lookupFuncRec?_mem` / `lookupDeclRec?_mem` (a hit is a member with that name),
`evalSeqLoop_mono_of_step_mono` (pointwise transport through the loop closure),
`evalParFor_fuel_mono`, and the `evalStepR` fuel-monotonicity pair
(`evalStepR_fuel_mono` with the `hasJmpToPure` false-antitonicity sublemma L2's contract
also names) — the last is Part II's helper and may land there instead.

Landed with the proofs: `lookupFuncRec?_mem` / `lookupDeclRec?_mem` (with the semantics),
`evalSeqLoop_mono_of_step_mono`, `evalParFor_fuel_mono`, `evalCodeRAux_nil`,
`evalLetValue_fap_local`, and one LNIR simulation lemma in place of two per-arm
inductions: `letHeadR` is the value a `.letBind` binds at one level of `evalCodeR`
(`evalCodeRAux_letBind` rewrites every `.letBind` arm onto it), and `evalCodeRAux_sim`
says a level simulates any level whose let heads reproduce its successful ones at a budget
at least as large; `evalCodeR_fuel_mono` instantiates it through `letHeadR_mono`, and
`evalCodeR_extend_of_ok` through `letHeadR_of_evalExpr_ok`. The `evalStepR`
fuel-monotonicity pair landed with amendment 2 (statements above), proved by a lockstep
unfolding of the two runs rather than per-arm lemmas.

Executable guards land in `lean/LeanNative/Tests/RealLCNFRecTests.lean` (NEW file; L2's
`Tests/RealLCNFCallTests.lean` is untouched): a self-recursive declaration
(countdown-accumulate) whose `evalRealLCNFDeclR` result is wrong unless the callee body
re-enters (kills call-as-noop mutants), the same declaration exhausting fuel at too-small
a budget (`.error .fuelExhausted`, never a wrong `.ok`), a two-declaration MUTUAL pair
(even/odd-style) evaluating through `Δ` with both orders of `Δ`, the `Δ = [] / Φ = []`
runs equal to the old evaluators on a call-bearing body, an `evalCodeR` run of a lowered
self-call body under `Φ = [d]`, and the strict-arity pin of amendment 2.

### Part II — the recursion headline, stated for the fold (signatures as amended; not
### proved, see "Part II status")

The step-level forward simulation with recursion-capable environments on both sides, and
its code- and declaration-level corollaries. These are the L3 names H1.4 dispatches on:

```
theorem lowerImpureStepPure_soundR (fuel : Nat) (ctx : RealBridgeCtx)
    (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx × Nat)) (Φ : List LNIRDecl)
    (st st' : RealBridgeState)
    (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
    (target : Lean.Compiler.LCNF.Code .impure ⊕
      (VarId × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure)))
    (code : LNIRCode) :
    DeclEnvLowersR Δ Φ →
    CtxMapsEnvR ctx Δ Φ →
    BridgeStateInv st lenv venv →
    lowerImpureStepPure fuel ctx st target = .ok (code, st') →
    (match target with
      | .inl c => evalStepR (declEnvR Δ) fuel ctx lenv hst (.inl c) = .ok (v, hst')
      | .inr (condVar, isBool, idx, discr?, alts) =>
        condVar < st.nextVarId ∧
        (∀ dx, discr? = some dx → (st.lookupFVar? dx).isSome = true) ∧
        (lnirTypeEq (st.getVarType condVar) .i1 = true → isBool = true) ∧
        ∃ cond, venv condVar = some cond ∧
          evalStepR (declEnvR Δ) fuel ctx lenv hst (.inr (cond, isBool, idx, discr?, alts)) = .ok (v, hst')) →
    evalCodeR Φ fuel venv hst code = .ok (v, hst')

theorem lowerRealLCNFCode_soundR (fuel : Nat) (ctx : RealBridgeCtx)
    (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx × Nat)) (Φ : List LNIRDecl)
    (st : RealBridgeState)
    (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
    (code : Lean.Compiler.LCNF.Code .impure) (lnir : LNIRCode) (st' : RealBridgeState)
    (h_env : DeclEnvLowersR Δ Φ)
    (h_map : CtxMapsEnvR ctx Δ Φ)
    (h_inv : BridgeStateInv st lenv venv)
    (h_lower : lowerRealLCNFCode fuel ctx st code = .ok (lnir, st'))
    (h_eval : evalRealLCNFCodeR (declEnvR Δ) fuel ctx lenv hst code = .ok (v, hst')) :
    evalCodeR Φ fuel venv hst lnir = .ok (v, hst')

theorem lowerRealLCNFDecl_soundR (fuel : Nat) (ctx : RealBridgeCtx)
    (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx × Nat)) (Φ : List LNIRDecl)
    (decl : Lean.Compiler.LCNF.Decl .impure) (args : List Val) (hst hst' : HeapState)
    (v : Val) (d : LNIRDecl) (mangled : String)
    (h_env : DeclEnvLowersR Δ Φ)
    (h_map : CtxMapsEnvR ctx Δ Φ)
    (h_lower : lowerRealLCNFDecl fuel ctx decl mangled = .ok d)
    (h_eval : evalRealLCNFDeclR (declEnvR Δ) fuel ctx decl args hst = .ok (v, hst')) :
    evalCodeR Φ fuel
      ((d.params.zip args).foldl (fun acc (p, val) => acc.bind p.id val) VarEnv.empty)
      hst d.body = .ok (v, hst')
```

`lowerRealLCNFDecl_soundR` is the L3 headline: `decl`'s own name may be in `ctx` and in
`Δ` (the driver puts it there), so `h_eval` runs SELF and MUTUAL recursion, bounded by
fuel, and the conclusion is the lowered body's run under the lowered environment — the
"self and mutual recursion proved" cell of the HORIZONS row. With `Δ = []`,
`evalRealLCNFDeclR_nil` collapses it to L1's `lowerRealLCNFDecl_sound` shape, and Part I's
`lowerRealLCNFDecl_soundR_base` is its already-proved restriction to old-semantics runs.

Why Part II's proofs were sequenced (superseded by "Part II status" below; kept as the
record): `lowerImpureStepPure_soundR`'s induction needs every per-case lemma of the L1
simulation stack (`Proofs/RealLCNFBridge/{CtorIntrinsic,CtorScalarCall,JpTag,LetValue,
Scalar,StateInv,StepCases,StepMono,UnaryCast}.lean` plus the aux in
`RealLCNFBridgeProofs.lean`, 5,441 lines when this contract was cut) restated against an
environment-carrying target semantics, and the L2 lane was landing that restatement for F
at the time; an independent R-restatement would have forked one proof stack into two
concurrent rewrites. Candidate resolutions as recorded then: (a) R-twin the landed
F-stack; (b) parameterize the per-case stack over the call rule so F and R instantiate
one proof; (c) prove R independently (forks the stack; rejected). L2 has since landed its
stack with the per-case step mirrors "parameterized over the call rule, L3's recorded
option (b)" (`LowerCalls.lean`'s helper paragraph): per `RealLCNFBridge/CallsF.lean`'s
header the call rule enters through hypothesis parameters, and the mirrors still conclude
in `evalStepF`/`evalCodeF`. The F-to-R embeddings, stated for the fold as first cut (an
F-run is an R-run with the stratification depth paid as fuel; both are refuted below):

```
theorem evalCodeF_toR (Φ : FuncEnv) (fuel : Nat) (env : VarEnv) (st : HeapState)
    (c : LNIRCode) (v : Val) (st' : HeapState) :
    evalCodeF Φ fuel env st c = .ok (v, st') →
    evalCodeR Φ (fuel + Φ.length) env st c = .ok (v, st')

theorem evalRealLCNFDeclF_toR (Δ : DeclEnv) (fuel : Nat) (ctx : RealBridgeCtx)
    (decl : Lean.Compiler.LCNF.Decl .impure) (args : List Val) (st : HeapState)
    (v : Val) (st' : HeapState) :
    evalRealLCNFDeclF Δ fuel ctx decl args st = .ok (v, st') →
    evalRealLCNFDeclR (declEnvR Δ) fuel ctx decl args st = .ok (v, st')
```

(As cut, this contract said the second needs no fuel padding: on the LCNF side both
semantics burn the step budget identically, and R's lookup is a superset of F's
stratified lookup on `DeclEnvLowersR` environments, whose names are duplicate-free. Its
`Δ : DeclEnv` is L2's, entries `Decl × RealBridgeCtx × Nat`, so `declEnvR` applies to it
unchanged. Reason 2 below refutes the remark.)

#### Part II status (2026-11-26): open; the semantic refutation is fixed

L2's F-stack has merged (`Proofs/LowerCalls.lean` proves `lowerRealLCNFDecl_soundF`), so
the sequencing reason above no longer holds, and the statements above carry the coherence
hypotheses a review found missing (amendment 2, F1; `declEnvLowersR_lookup_align`
proves them enough for the call case's lookup step). This section's first status refuted
the headline over the landed `evalStepR`; amendment 3 fixed the step rule that refutation
rested on. What stands, each point pinned by a committed guard of
`Tests/RealLCNFRecTests.lean`:

1. The headline's counterexample no longer applies. It was a heap-typed local-call result
   stored at `.i64` on the source side and at `rawTy` on the LNIR side, so a `dec` freed
   the object on the LNIR side only. With the result bound at `rawTy`, the source run,
   L2's run and the lowered run of that module agree exactly on value and heap (family 6).
   The headline is not proved; no counterexample to it is known at these bytes.
2. `evalRealLCNFDeclF_toR` as written is false for fuel. L2's per-entry amendment runs an
   F callee at its ENTRY fuel, while R runs it at the caller's decremented step fuel, so
   at a step budget the caller's own steps fit and the callee's do not, the F-run
   succeeds and the R-run at the same budget ends on it (family 8: a three-addition callee
   with entry fuel 64 under a caller at budget 3). The contract's "needs no fuel padding"
   remark does not hold. The heap half of this item's first refutation is gone: family 6
   compares the F and R runs and they agree.
3. `evalCodeF_toR` does not elaborate (it passes a `FuncEnv`, a list of declaration/fuel
   pairs since L2's amendment, where `evalCodeR` takes `List LNIRDecl`), and with the
   projection `Φ.map Prod.fst` it is false for repeated names: with two entries named `f`,
   the first calling `f` and the second returning `7`, the F-run returns `7` (the nested
   call resolves in the strict suffix) and the R-run ends on its call budget at every
   fuel, since every nested call re-resolves to the first entry (family 7).

The open work, for the fold owner:

- Restate L2's step stack over R: the per-case mirrors in `RealLCNFBridge/CallsF.lean`
  conclude in `evalStepF`/`evalCodeF`, so their conclusions move to `evalStepR`/`evalCodeR`
  with the call-rule hypotheses instantiated by R's rule, and the U6 induction in
  `LowerCalls.lean` is twinned (about 2,600 lines together).
- Meet the two fuels in the call case. A callee's lowering ran at its entry fuel `fuel_j`;
  its body is evaluated at the caller's decremented step fuel. Both evaluators are monotone
  in their budget (`evalStepR_fuel_mono`, `evalCodeR_fuel_mono`, proved). Not stated here:
  monotonicity of the pinned lowering in its fuel (a lowering that succeeds at `fuel_j`
  returns the same declaration at any larger fuel), or a simulation stated for a lowering
  fuel at least the evaluation fuel. Which of these the induction takes, and whether the
  LNIR fuel of the conclusion stays the source fuel, is the first design decision.
- Restate the two embeddings with a distinct-names hypothesis (family 7's environment
  violates it) and a fuel bound covering the entry fuels (family 8's run violates it).

### Named exclusions (recorded, not silently dropped)

- E1 `Code.fun` (letrec-shaped local functions): uninhabitable in the `.impure` phase at
  these bytes (`h : pu = .pure`, toolchain `LCNF/Basic.lean:382`), so any theorem over it
  is vacuous and none is stated. Local functions and closures are H3 runtime-objects work.
- E2 Recursive join points / the LNIR loop construct: the HORIZONS cell "`LNIR` gets a
  join-point / loop construct that replaces inlining a join point at every jump" requires
  (i) a new `LNIRCode` constructor in `IR/AST.lean`, (ii) a lowering that emits it where
  `lowerImpureStepPure` today errors on `hasJmpToPure`, and (iii) the semantics arm —
  (ii) and the matching source-semantics change live in sha-pinned files
  (`IR/RealLCNFBridge.lean`, `IR/RealLCNFSemantics.lean`), and every LNIR backend,
  `canonicalDeBruijn`/`freshenBinders`/`nodeSize`, and the SymbolicTV stack case over
  `LNIRCode`, so the constructor alone ripples through the audited proof surface. This
  leaf pins the fail-closed behavior instead (the two `_recursive_jp_` theorems) and
  records the loop IR as the follow-up that starts with the matrix owner's re-pin. The
  `Code.jp.recursive` matrix row therefore stays `rejected` — honestly — in this leaf.
- E3 `LetValue.pap` and higher-order `.fvar` calls: closures; rejected at the bytes; H3.
- E4 Erased arguments at local-call sites: `evalArgs` errors on `.erased`, so the R-run
  hypothesis covers call sites whose arguments are all runtime fvars — the same bound
  L2's F-rule has. The lowering zero-binds erased positions
  (`lowerCallArgsWithErasedPure`); extending the semantics' argument convention to match
  is recorded for the fold, not promised here.
- E5 Mutual-cycle declarations in the MEASUREMENT: `scripts/lcnf_coverage.py` counts them
  `rejected_not_lowered` with reason `mutual_cycle` upstream of the lowering, so moving
  those two C1 entries needs the measurement driver (H1.0's file) to attempt them once
  `lowerRealLCNFDecl_soundR` exists; the semantics and statement here already admit
  cyclic `Δ`. Recorded as a handoff to the matrix owner, as L2 recorded its
  reclassification.
- E6 Driver-shaped R-forms: none stated. L1 removed the driver's compression
  post-pass (a review proved it never changes any declaration), so the driver-shaped
  statement is `lowerRealLCNFDecl_sound`, whose R-form IS Part II's
  `lowerRealLCNFDecl_soundR`. One standing caution for consumers of
  `CodeRefinesR`: the generic transfer `CodeRefines src tgt → CodeRefinesR Φ src tgt` is
  FALSE — `src = .letBind x ty (.call f [] ty false) (.ret x)` with `f` bound in `Φ` has
  no env-free `.ok` run, so env-free `CodeRefines src tgt` holds for EVERY `tgt`, while
  `CodeRefinesR Φ src tgt` fails for any `tgt` that disagrees with the call's result. An
  env-free certificate transfers only along call-free runs; `evalCodeR_extend_of_ok` is
  the sound direction.

### Acceptance (quoted) and gates

- "leaf `0 sorryAx`": every Part I theorem lands kernel-checked; the 14 names and
  amendment 2's four are appended to `AxiomAudit.lean`'s `auditedTheoremNames` with the
  pinned count raised exactly (874 → 892; L2's raise for its own set landed first, the
  additive convention L2's contract records).
- "matrix moves": Part I makes the `LetValue.fap.local_call` row's vacuity REMOVABLE for
  recursive callees (the semantics now runs them) and Part II's headline is the condition
  `scripts/lcnf_coverage.py`'s methodology needs to reclassify self/mutual-recursive
  declarations out of `lowered_unproved`; the reclassification commit is the matrix
  owner's, once the headline lands (a handoff, not silently claimed; this leaf edits no
  sha-pinned coverage input). `Code.jp.recursive` stays `rejected` per E2.
- Gates: `(cd lean && lake build TurboLean LeanNative)` ("Build completed successfully");
  `turbo-lean --json audit-spec lean/TurboLean/Spec.lean` (98/98) and
  `lean/LeanNative/Spec.lean` (124/124) — both files untouched by this leaf;
  `turbo-lean --json audit-spec --policy strict-proofs lean/TurboLean/ConLeche.lean` (7/7);
  the contract.d batch
  `turbo-lean --json audit-spec --policy strict-proofs lean/LeanNative/Proofs/
  lean/LeanNative/Transform/ lean/TurboLean/ConLeche.lean lean/TurboLean/ElabAudit.lean`
  (this file is inside the walked directory, so the batch gates it with no CI edit;
  0 vacuous, 0 trivial, 0 stub_defs, 0 forbidden_scope_decls);
  `python3 scripts/sync_docs_inventory.py --check` (the Spec counts do not move).
-/

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

/-! ### Part I definitions -/

/-- Reserved runtime symbols `evalExpr` interprets as intrinsics (`lean_native_*`,
    `lean_mark_mt`); a lowered local callee must not shadow them. The lanes fold onto
    ONE predicate: this is L2's `reservedRuntimeName` (`RealLCNFBridge/CallsF.lean`)
    under the L3 contract's spelling, so the two names cannot disagree. -/
def reservedRuntimeCallee (s : String) : Bool := reservedRuntimeName s

/-- The evaluation-side environment of a lowering environment: each entry keeps its
    declaration and its own context; the per-entry LOWERING fuel is a lowering-time
    quantity, not an evaluation input (the evaluation fuel stays the single step
    budget). -/
def declEnvR (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx × Nat)) :
    List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx) :=
  Δ.map fun e => (e.1, e.2.1)

/-- A context's mangled-name map COHERES with an environment pairing, position by
    position: WHEN it maps a source declaration's name, it maps it to the lowered
    declaration's name at the same position (L2's `CtxMapsEnv`, for the R entry shape).
    This is what ties a call site's source lookup, by Lean name, to its LNIR lookup, by
    mangled symbol; length-mismatched lists cohere never. -/
def CtxMapsEnvR (ctx : RealBridgeCtx) :
    List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx × Nat) → List LNIRDecl → Prop
  | [], [] => True
  | (sd, _, _) :: Δ, ld :: Φ =>
      (∀ m, ctx.findLocalCallee? sd.name = some m → m = ld.name) ∧ CtxMapsEnvR ctx Δ Φ
  | _, _ => False

/-- The positional clauses of `DeclEnvLowersR`: the lowering hypothesis holds at the
    entry's own context and fuel, lowered names are unreserved, and no later lowered name
    repeats an earlier one. Whether a context knows a name is left to the coherence clause
    (`CtxMapsEnvR`; amendment 4 dropped a per-entry "knows its own name" clause no proof
    used). A recursive `Prop` (strict-proofs scope admits no new `inductive` under
    `Proofs/`, the shape L2's `DeclEnvLowers` takes for the same reason);
    length-mismatched lists relate never. -/
def DeclEnvLowersPosR :
    List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx × Nat) → List LNIRDecl → Prop
  | [], [] => True
  | (sd, ctx, fuel) :: Δ, ld :: Φ =>
      lowerRealLCNFDecl fuel ctx sd ld.name = .ok ld ∧
      reservedRuntimeCallee ld.name = false ∧
      (∀ ld' ∈ Φ, ld'.name ≠ ld.name) ∧
      DeclEnvLowersPosR Δ Φ
  | _, _ => False

/-- Pointwise "Δ lowers to Φ" for the FULL-environment semantics, with PER-ENTRY context
    and lowering fuel: the positional clauses, and every entry's own context coheres with
    the WHOLE pairing (`CtxMapsEnvR`). Name freshness alone cannot align a lookup keyed on
    a Lean name with one keyed on a mangled symbol; coherence pins the symbol a context
    resolves to the position the source lookup lands on, and freshness then keeps every
    other position from matching it (`declEnvLowersR_lookup_align`). Coherence is over the
    whole lists, not the tail, because a recursive call may reach an earlier entry. -/
def DeclEnvLowersR (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx × Nat))
    (Φ : List LNIRDecl) : Prop :=
  DeclEnvLowersPosR Δ Φ ∧ ∀ e ∈ Δ, CtxMapsEnvR e.2.1 Δ Φ

/-- `CodeRefines` with the recursion-capable environment (the L3 form of refinement). -/
def CodeRefinesR (Φ : List LNIRDecl) (src tgt : LNIRCode) : Prop :=
  ∀ fuel env st v st', evalCodeR Φ fuel env st src = .ok (v, st') →
    evalCodeR Φ fuel env st tgt = .ok (v, st')

/-! ### Helpers on the LNIR side -/

/-- The value one level of `evalCodeR` binds for `.letBind _ _ val _`, before its
    continuation runs: a non-extern call that `Φ` resolves runs its callee in the slot
    below (and is the budget error at the spent level), every other expression is
    `evalExpr`'s. -/
def letHeadR (Φ : List LNIRDecl)
    (callee? : Option (VarEnv → HeapState → LNIRCode → Except UBError (Val × HeapState)))
    (env : VarEnv) (st : HeapState) (val : LNIRExpr) : Except UBError (Val × HeapState) :=
  match val with
  | .call fn args retTy false =>
    match lookupFuncRec? Φ fn with
    | some ld =>
      match callee? with
      | none => .error .fuelExhausted
      | some callee =>
        match evalVarList env args with
        | .ok vals =>
          if vals.length = ld.params.length then
            callee ((ld.params.zip vals).foldl (fun acc (p, val) => acc.bind p.id val) VarEnv.empty)
              st ld.body
          else .error (.typeError "call arity mismatch")
        | .error err => .error err
    | none => evalExpr env st (.call fn args retTy false)
  | _ => evalExpr env st val

/-- Every `.letBind` arm of `evalCodeRAux` runs `letHeadR` and continues on its value. -/
theorem evalCodeRAux_letBind (Φ : List LNIRDecl) (budget : Nat)
    (callee? : Option (VarEnv → HeapState → LNIRCode → Except UBError (Val × HeapState)))
    (env : VarEnv) (st : HeapState) (dst : VarId) (ty : LNIRType) (val : LNIRExpr)
    (k : LNIRCode) :
    evalCodeRAux Φ budget callee? env st (.letBind dst ty val k) =
      match letHeadR Φ callee? env st val with
      | .ok (v, st') => evalCodeRAux Φ budget callee? (env.bind dst v) st' k
      | .error err => .error err := by
  cases val <;> try rfl
  case call fn args retTy isExt =>
    cases isExt
    · dsimp only [evalCodeRAux, letHeadR]
      cases lookupFuncRec? Φ fn <;> try rfl
      cases callee? <;> try rfl
      dsimp only
      cases evalVarList env args with
      | error _ => rfl
      | ok vals =>
        dsimp only
        split <;> rfl
    · rfl

/-- With no environment the let head is `evalExpr`'s, whatever the callee slot holds. -/
theorem letHeadR_nil
    (callee? : Option (VarEnv → HeapState → LNIRCode → Except UBError (Val × HeapState)))
    (env : VarEnv) (st : HeapState) (val : LNIRExpr) :
    letHeadR [] callee? env st val = evalExpr env st val := by
  unfold letHeadR
  split <;> rfl

/-- Pointwise transport through the `seqFor` loop closure: a step evaluator that
    reproduces every successful step of another reproduces every successful loop. -/
theorem evalSeqLoop_mono_of_step_mono
    (f g : VarEnv → HeapState → Except UBError (Val × HeapState))
    (hfg : ∀ se ss r, f se ss = .ok r → g se ss = .ok r) (idxVar accVar : VarId) :
    ∀ (count cur : Nat) (acc : Val) (env : VarEnv) (st : HeapState) (r : Val × HeapState),
      evalSeqLoop count cur idxVar accVar acc env st f = .ok r →
      evalSeqLoop count cur idxVar accVar acc env st g = .ok r
  | 0, _, _, _, _, _, h => h
  | count + 1, cur, acc, env, st, r, h => by
    dsimp only [evalSeqLoop] at h ⊢
    cases hs : f ((env.bind idxVar (.u64 cur.toUInt64)).bind accVar acc) st with
    | error _ => rw [hs] at h; exact nomatch h
    | ok pr =>
      rw [hs] at h
      rw [hfg _ _ pr hs]
      exact evalSeqLoop_mono_of_step_mono f g hfg idxVar accVar count (cur + 1) pr.1 env pr.2 r h

/-- `evalParFor`'s budget is an upper bound on the loop length only: a larger budget
    reproduces every successful run. -/
theorem evalParFor_fuel_mono (b b' : Nat) (hb : b ≤ b') (env : VarEnv) (st : HeapState)
    (lenVar : VarId) (inputs : List VarId) (kernel : ParallelKernelKind) (elemTy : LNIRType)
    (r : Val × HeapState) (h : evalParFor b env st lenVar inputs kernel elemTy = .ok r) :
    evalParFor b' env st lenVar inputs kernel elemTy = .ok r := by
  unfold evalParFor at h ⊢
  cases hl : env lenVar <;> rw [hl] at h
  · exact nomatch h
  · rename_i vl
    cases vl with
    | u64 n =>
      dsimp only at h ⊢
      by_cases hgt : n.toNat > b
      · simp only [hgt, ↓reduceIte] at h; exact nomatch h
      · have hgt' : ¬(n.toNat > b') := by omega
        simp only [hgt, hgt', ↓reduceIte] at h ⊢; exact h
    | _ => exact nomatch h

/-- At `Φ = []` every level of the recursion-capable evaluator is `evalCode` at its
    budget, whatever the callee slot holds: no call resolves. -/
theorem evalCodeRAux_nil (budget : Nat)
    (callee? : Option (VarEnv → HeapState → LNIRCode → Except UBError (Val × HeapState)))
    (env : VarEnv) (st : HeapState) (c : LNIRCode) :
    evalCodeRAux [] budget callee? env st c = evalCode budget env st c := by
  -- The two evaluators' arms elaborate to distinct matcher constants, so each arm closes
  -- by `rfl` once the recursive occurrences are rewritten.
  induction c generalizing env st with
  | letBind dst ty val k ih =>
    unfold evalCodeRAux evalCode
    split
    · simp only [lookupFuncRec?, ih] <;> rfl
    · simp only [ih] <;> rfl
  | rawStore ptrVar idxVar valVar elemTy k ih =>
    unfold evalCodeRAux evalCode
    simp only [ih] <;> rfl
  | incRef objVar count k ih =>
    unfold evalCodeRAux evalCode
    simp only [ih] <;> rfl
  | decRef objVar count k ih =>
    unfold evalCodeRAux evalCode
    simp only [ih] <;> rfl
  | ite condVar t e iht ihe =>
    unfold evalCodeRAux evalCode
    simp only [iht, ihe] <;> rfl
  | seqFor idxVar loVar hiVar accVar accInit accTy stepBody k ihStep ihK =>
    unfold evalCodeRAux evalCode
    simp only [ihStep, ihK] <;> rfl
  | parFor outVar lenVar inputs elemTy kernel k ih =>
    unfold evalCodeRAux evalCode
    simp only [ih] <;> rfl
  | ret v => rfl
  | unreachable => rfl

/-! ### Part I — conservativity: the old semantics is the empty-environment instance -/

theorem evalCodeR_nil (fuel : Nat) (env : VarEnv) (st : HeapState) (c : LNIRCode) :
    evalCodeR [] fuel env st c = evalCode fuel env st c := by
  cases fuel with
  | zero => exact evalCodeRAux_nil 0 none env st c
  | succ n => exact evalCodeRAux_nil (n + 1) (some (evalCodeR [] n)) env st c

/-- `evalLetValue` on a `ctx`-local `.fap` is the deliberate `.unsupportedCall` refusal
    the R rule replaces (`RealLCNFSemantics.lean`, the `.fap` arm's first test). -/
theorem evalLetValue_fap_local (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
    (fn : Lean.Name) (args : Array (Lean.Compiler.LCNF.Arg .impure)) (ty : LNIRType)
    (hloc : (ctx.findLocalCallee? fn).isSome = true) :
    evalLetValue ctx env st (.fap fn args rfl) ty = .error (.unsupportedCall fn.toString) := by
  unfold evalLetValue
  simp only [hloc, ↓reduceIte]

theorem evalStepR_nil (fuel : Nat) (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
    (target : Lean.Compiler.LCNF.Code .impure ⊕
      (Val × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure))) :
    evalStepR [] fuel ctx env st target = evalStep fuel ctx env st target := by
  induction fuel generalizing ctx env st target with
  | zero => simp only [evalStepR, evalStep]
  | succ fuel ih =>
    unfold evalStepR evalStep
    cases target with
    | inr p =>
      obtain ⟨cond, isBool, idx, discr?, alts⟩ := p
      simp only [ih]
      rfl
    | inl code =>
      cases code
      case «let» decl k =>
        simp only [ih, lookupDeclRec?]
        obtain ⟨fvarId, binderName, type, value⟩ := decl
        cases value
        case fap fn args h =>
          cases h
          dsimp only
          by_cases hloc : (ctx.findLocalCallee? fn).isSome = true
          · simp only [hloc, ↓reduceIte, evalLetValue_fap_local ctx env st fn args _ hloc]
          · simp only [hloc, Bool.false_eq_true, ↓reduceIte]
            rfl
        all_goals first | rfl | (dsimp only; rfl)
      all_goals (simp only [ih]; try rfl)

theorem evalRealLCNFDeclR_nil (fuel : Nat) (ctx : RealBridgeCtx)
    (decl : Lean.Compiler.LCNF.Decl .impure) (args : List Val) (st : HeapState) :
    evalRealLCNFDeclR [] fuel ctx decl args st = evalRealLCNFDecl fuel ctx decl args st := by
  unfold evalRealLCNFDeclR evalRealLCNFDecl evalRealLCNFCodeR evalRealLCNFCode
  cases decl.value with
  | extern _ => rfl
  | code c =>
    cases bindParams ctx true LEnv.empty decl.params.toList args with
    | ok env => exact evalStepR_nil fuel ctx env st (.inl c)
    | error _ => rfl

/-! ### Part I — fuel monotonicity of the recursion-capable evaluator -/

/-- One level of `evalCodeR` simulates another whose let heads reproduce its successful
    let heads, at a budget at least as large: every arm but `.letBind` is `evalCode`'s and
    reads the budget only as `evalParFor`'s length bound. Fuel monotonicity and
    environment extension are its two instances. -/
theorem evalCodeRAux_sim (Φ1 Φ2 : List LNIRDecl) (b1 b2 : Nat) (hb : b1 ≤ b2)
    (c1 c2 : Option (VarEnv → HeapState → LNIRCode → Except UBError (Val × HeapState)))
    (hhead : ∀ env st val r, letHeadR Φ1 c1 env st val = .ok r →
      letHeadR Φ2 c2 env st val = .ok r) :
    ∀ (c : LNIRCode) (env : VarEnv) (st : HeapState) (r : Val × HeapState),
      evalCodeRAux Φ1 b1 c1 env st c = .ok r → evalCodeRAux Φ2 b2 c2 env st c = .ok r
  | .letBind dst ty val k, env, st, r, h => by
    rw [evalCodeRAux_letBind] at h ⊢
    cases hh : letHeadR Φ1 c1 env st val with
    | error _ => rw [hh] at h; exact nomatch h
    | ok p =>
      rw [hh] at h; rw [hhead env st val p hh]; dsimp only at h ⊢
      exact evalCodeRAux_sim Φ1 Φ2 b1 b2 hb c1 c2 hhead k (env.bind dst p.1) p.2 r h
  | .rawStore pv iv vv elemTy k, env, st, r, h => by
    dsimp only [evalCodeRAux] at h ⊢
    cases hp : env pv <;> cases hi : env iv <;>
      cases hv : env vv <;> simp only [hp, hi, hv] at h <;> try contradiction
    rename_i vp vi vv0
    cases vp <;> cases vi <;>
      cases vv0 <;> simp only at h ⊢ <;> try contradiction
    all_goals (
      rename_i bufId idx val
      cases hw : st.writeElemExclusive bufId idx.toNat (maskElemVal elemTy val) <;>
        simp only [hw] at h ⊢
      · contradiction
      · rename_i st1; exact evalCodeRAux_sim Φ1 Φ2 b1 b2 hb c1 c2 hhead k env st1 r h)
  | .incRef ov cnt k, env, st, r, h => by
    dsimp only [evalCodeRAux] at h ⊢
    cases he : st.evalIncRef env ov cnt with
    | error _ => rw [he] at h; exact nomatch h
    | ok st1 => rw [he] at h; exact evalCodeRAux_sim Φ1 Φ2 b1 b2 hb c1 c2 hhead k env st1 r h
  | .decRef ov cnt k, env, st, r, h => by
    dsimp only [evalCodeRAux] at h ⊢
    cases he : st.evalDecRef env ov cnt with
    | error _ => rw [he] at h; exact nomatch h
    | ok st1 => rw [he] at h; exact evalCodeRAux_sim Φ1 Φ2 b1 b2 hb c1 c2 hhead k env st1 r h
  | .ite cv t e, env, st, r, h => by
    dsimp only [evalCodeRAux] at h ⊢
    cases hcv : env cv <;> rw [hcv] at h
    · exact nomatch h
    · rename_i vc; cases vc with
      | bool b => cases b <;> exact evalCodeRAux_sim Φ1 Φ2 b1 b2 hb c1 c2 hhead _ env st r h
      | u64 n => by_cases hn : n != 0 <;> simp only [hn, ↓reduceIte, Bool.false_eq_true] at h ⊢ <;>
          exact evalCodeRAux_sim Φ1 Φ2 b1 b2 hb c1 c2 hhead _ env st r h
      | u256 w => by_cases hw : w != UInt256.zero <;>
          simp only [hw, ↓reduceIte, Bool.false_eq_true] at h ⊢ <;>
          exact evalCodeRAux_sim Φ1 Φ2 b1 b2 hb c1 c2 hhead _ env st r h
      | _ => exact nomatch h
  | .seqFor idxVar loVar hiVar accVar accInit _ stepBody k, env, st, r, h => by
    dsimp only [evalCodeRAux] at h ⊢
    cases hlo : env loVar <;> cases hhi : env hiVar <;>
      cases hain : env accInit <;> simp only [hlo, hhi, hain] at h <;> try contradiction
    rename_i vlo vhi initVal
    cases vlo <;> cases vhi <;>
      simp only at h ⊢ <;> try contradiction
    rename_i lo hi
    have hloop := evalSeqLoop_mono_of_step_mono
      (fun se ss => evalCodeRAux Φ1 b1 c1 se ss stepBody)
      (fun se ss => evalCodeRAux Φ2 b2 c2 se ss stepBody)
      (fun se ss r' hr => evalCodeRAux_sim Φ1 Φ2 b1 b2 hb c1 c2 hhead stepBody se ss r' hr)
      idxVar accVar
    cases hl : evalSeqLoop (hi.toNat - lo.toNat) lo.toNat idxVar accVar initVal env st
        (fun se ss => evalCodeRAux Φ1 b1 c1 se ss stepBody) with
    | error _ => rw [hl] at h; exact nomatch h
    | ok pr =>
      rw [hl] at h; rw [hloop _ _ _ _ _ pr hl]
      exact evalCodeRAux_sim Φ1 Φ2 b1 b2 hb c1 c2 hhead k (env.bind accVar pr.1) pr.2 r h
  | .parFor outVar lenVar inputs elemTy kernel k, env, st, r, h => by
    dsimp only [evalCodeRAux] at h ⊢
    cases hp : evalParFor b1 env st lenVar inputs kernel elemTy with
    | error _ => rw [hp] at h; exact nomatch h
    | ok pr =>
      rw [hp] at h
      rw [evalParFor_fuel_mono b1 b2 hb env st lenVar inputs kernel elemTy pr hp]
      exact evalCodeRAux_sim Φ1 Φ2 b1 b2 hb c1 c2 hhead k (env.bind outVar pr.1) pr.2 r h
  | .ret _, _, _, _, h => by
    dsimp only [evalCodeRAux] at h ⊢; exact h
  | .unreachable, _, _, _, h => by
    dsimp only [evalCodeRAux] at h ⊢; exact h

/-- A callee slot that reproduces every successful callee run of another reproduces every
    successful let head of the same environment. -/
theorem letHeadR_mono (Φ : List LNIRDecl)
    (c1 c2 : Option (VarEnv → HeapState → LNIRCode → Except UBError (Val × HeapState)))
    (hc : ∀ f1, c1 = some f1 → ∃ f2, c2 = some f2 ∧
      ∀ env st code r, f1 env st code = .ok r → f2 env st code = .ok r)
    (env : VarEnv) (st : HeapState) (val : LNIRExpr) (r : Val × HeapState)
    (h : letHeadR Φ c1 env st val = .ok r) : letHeadR Φ c2 env st val = .ok r := by
  cases val <;> try exact h
  case call fn args retTy isExt =>
    cases isExt
    · dsimp only [letHeadR] at h ⊢
      cases hlk : lookupFuncRec? Φ fn with
      | none => rw [hlk] at h; exact h
      | some ld =>
        rw [hlk] at h
        cases hc1 : c1 with
        | none => rw [hc1] at h; exact nomatch h
        | some f1 =>
          obtain ⟨f2, hc2, hf⟩ := hc f1 hc1
          rw [hc1] at h; rw [hc2]; dsimp only at h ⊢
          cases hvl : evalVarList env args with
          | error _ => rw [hvl] at h; exact nomatch h
          | ok vals =>
            rw [hvl] at h; dsimp only at h ⊢
            by_cases hl : vals.length = ld.params.length
            · simp only [hl, ↓reduceIte] at h ⊢; exact hf _ _ _ r h
            · simp only [hl, ↓reduceIte] at h; exact nomatch h
    · exact h

theorem evalCodeR_fuel_mono (Φ : List LNIRDecl) (fuel : Nat) (env : VarEnv)
    (st : HeapState) (c : LNIRCode) (v : Val) (st' : HeapState) :
    evalCodeR Φ fuel env st c = .ok (v, st') → evalCodeR Φ (fuel + 1) env st c = .ok (v, st') := by
  induction fuel generalizing env st c v st' with
  | zero =>
    exact evalCodeRAux_sim Φ Φ 0 1 (Nat.zero_le 1) none (some (evalCodeR Φ 0))
      (letHeadR_mono Φ none _ (fun _ h1 => nomatch h1)) c env st (v, st')
  | succ n ih =>
    refine evalCodeRAux_sim Φ Φ (n + 1) (n + 1 + 1) (Nat.le_succ _) (some (evalCodeR Φ n))
      (some (evalCodeR Φ (n + 1))) (letHeadR_mono Φ _ _ ?_) c env st (v, st')
    intro f1 h1
    injection h1 with h1
    subst h1
    exact ⟨_, rfl, fun env st code r hr => by obtain ⟨a, b⟩ := r; exact ih env st code a b hr⟩

/-- A `false` recursive-join-point verdict survives more fuel: `hasJmpToPure 0` answers
    `true` (an exhausted search counts as recursive), so `false` is a completed search,
    and a deeper one finds the same nothing. This is the direction the `evalStepR`
    monotonicity below needs: a `.jp` the source run accepted at fuel `n` is accepted at
    `n + 1`. -/
theorem hasJmpToPure_false_succ :
    ∀ (fuel : Nat) (t : Lean.FVarId)
      (target : Lean.Compiler.LCNF.Code .impure ⊕ List (Lean.Compiler.LCNF.Alt .impure)),
      hasJmpToPure fuel t target = false → hasJmpToPure (fuel + 1) t target = false
  | 0, _, _, h => by rw [hasJmpToPure.eq_1] at h; exact nomatch h
  | fuel + 1, t, target, h => by
    rw [hasJmpToPure.eq_def] at h ⊢
    dsimp only at h ⊢
    have ih := hasJmpToPure_false_succ fuel t
    cases target with
    | inr alts =>
      cases alts with
      | nil => exact h
      | cons alt rest =>
        dsimp only at h ⊢
        rw [Bool.or_eq_false_iff] at h ⊢
        exact ⟨ih _ h.1, ih _ h.2⟩
    | inl code =>
      cases code <;> dsimp only at h ⊢ <;>
        first
        | exact h
        | exact ih _ h
        | (rw [Bool.or_eq_false_iff] at h ⊢; exact ⟨ih _ h.1, ih _ h.2⟩)

/-- Fuel monotonicity of the recursion-capable LCNF evaluator: a successful run keeps its
    result with one more unit of step budget. The two sides unfold in lockstep (`split`
    the hypothesis, replay its equation into the goal); the discriminants agree except at
    the two places that read the budget — the resolved callee's run, upgraded by the
    induction hypothesis, and the recursive-join-point gate, upgraded by
    `hasJmpToPure_false_succ`. The script searches the unfolding rather than naming arms,
    so it re-checks itself on every change to `evalStepR`: a new discriminant that reads
    the budget makes it fail at build time with a leftover goal, never silently, and that
    arm then needs its own case (amendment 3's rule change re-ran it green unchanged). -/
theorem evalStepR_fuel_mono (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx)) :
    ∀ (fuel : Nat) (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
      (target : Lean.Compiler.LCNF.Code .impure ⊕
        (Val × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure)))
      (r : Val × HeapState),
      evalStepR Δ fuel ctx env st target = .ok r →
      evalStepR Δ (fuel + 1) ctx env st target = .ok r
  | 0, _, _, _, _, _, h => by rw [evalStepR.eq_1] at h; cases h
  | fuel + 1, ctx, env, st, target, r, h => by
    rw [evalStepR.eq_def] at h ⊢
    dsimp only at h ⊢
    repeat' (first
      | (cases h; done)
      | exact h
      | exact evalStepR_fuel_mono Δ fuel _ _ _ _ _ h
      | (rename_i hcall; simp only [evalStepR_fuel_mono Δ fuel _ _ _ _ _ hcall])
      | (split at h <;> (try simp only [Bool.not_eq_true] at *) <;>
          (try subst_vars) <;>
          (try simp only [*, hasJmpToPure_false_succ fuel, ↓reduceIte, Bool.false_eq_true] at h ⊢)))

/-! ### Part I — the call rule, pinned as kernel equations -/

theorem evalCodeR_call_fuel_zero (Φ : List LNIRDecl) (env : VarEnv) (st : HeapState)
    (dst : VarId) (ty : LNIRType) (fn : String) (args : List VarId) (retTy : LNIRType)
    (k : LNIRCode) (ld : LNIRDecl) (hlk : lookupFuncRec? Φ fn = some ld) :
    evalCodeR Φ 0 env st (.letBind dst ty (.call fn args retTy false) k) =
      .error .fuelExhausted := by
  show evalCodeRAux Φ 0 none env st (.letBind dst ty (.call fn args retTy false) k) = _
  dsimp only [evalCodeRAux]
  rw [hlk]

theorem evalCodeR_call_unfold (Φ : List LNIRDecl) (fuel : Nat) (env : VarEnv)
    (st : HeapState) (dst : VarId) (ty : LNIRType) (fn : String) (args : List VarId)
    (retTy : LNIRType) (k : LNIRCode) (ld : LNIRDecl)
    (hlk : lookupFuncRec? Φ fn = some ld) :
    evalCodeR Φ (fuel + 1) env st (.letBind dst ty (.call fn args retTy false) k) =
      match evalVarList env args with
      | .error e => .error e
      | .ok vals =>
        if vals.length = ld.params.length then
          match evalCodeR Φ fuel
              ((ld.params.zip vals).foldl (fun acc (p, val) => acc.bind p.id val) VarEnv.empty)
              st ld.body with
          | .error e => .error e
          | .ok (v, st') => evalCodeR Φ (fuel + 1) (env.bind dst v) st' k
        else .error (.typeError "call arity mismatch") := by
  show evalCodeRAux Φ (fuel + 1) (some (evalCodeR Φ fuel)) env st
    (.letBind dst ty (.call fn args retTy false) k) = _
  dsimp only [evalCodeRAux]
  rw [hlk]
  dsimp only
  cases evalVarList env args with
  | error e => rfl
  | ok vals =>
    dsimp only
    by_cases hl : vals.length = ld.params.length
    · simp only [hl, ↓reduceIte]
      cases evalCodeR Φ fuel ((ld.params.zip vals).foldl (fun acc (p, val) => acc.bind p.id val)
          VarEnv.empty) st ld.body with
      | error e => rfl
      | ok p => rfl
    · simp only [hl, ↓reduceIte]

theorem evalStepR_localCall_unfold (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx))
    (fuel : Nat) (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
    (decl : Lean.Compiler.LCNF.LetDecl .impure) (k : Lean.Compiler.LCNF.Code .impure)
    (fn : Lean.Name) (args : Array (Lean.Compiler.LCNF.Arg .impure))
    (sd : Lean.Compiler.LCNF.Decl .impure) (sdCtx : RealBridgeCtx)
    (hval : decl.value = .fap fn args rfl)
    (hloc : (ctx.findLocalCallee? fn).isSome = true)
    (hlk : lookupDeclRec? Δ fn = some (sd, sdCtx)) :
    evalStepR Δ (fuel + 1) ctx env st (.inl (.let decl k)) =
      match evalArgs env.vals args.toList with
      | .error e => .error e
      | .ok vals =>
        match sd.value with
        | .extern _ => .error (.unsupportedCall fn.toString)
        | .code c =>
          match bindParams sdCtx true LEnv.empty sd.params.toList vals with
          | .error e => .error e
          | .ok env' =>
            match evalStepR Δ fuel sdCtx env' st (.inl c) with
            | .error e => .error e
            | .ok (v, st') =>
              evalStepR Δ fuel ctx
                (env.bind decl.fvarId v none (some (lowerGroundImpureTypeWith ctx decl.type)))
                st' (.inl k) := by
  rw [evalStepR.eq_def]
  simp only [hval, hloc, hlk, ↓reduceIte]
  rfl

theorem evalStepR_localCall_miss (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx))
    (fuel : Nat) (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
    (decl : Lean.Compiler.LCNF.LetDecl .impure) (k : Lean.Compiler.LCNF.Code .impure)
    (fn : Lean.Name) (args : Array (Lean.Compiler.LCNF.Arg .impure))
    (hval : decl.value = .fap fn args rfl)
    (hloc : (ctx.findLocalCallee? fn).isSome = true)
    (hlk : lookupDeclRec? Δ fn = none) :
    evalStepR Δ (fuel + 1) ctx env st (.inl (.let decl k)) =
      .error (.unsupportedCall fn.toString) := by
  rw [evalStepR.eq_def]
  simp only [hval, hloc, hlk, ↓reduceIte]

/-! ### Part I — environment-extension conservativity -/

theorem evalExpr_call_ok_reserved (env : VarEnv) (st : HeapState) (fn : String)
    (args : List VarId) (retTy : LNIRType) (isExt : Bool) (r : Val × HeapState)
    (h : evalExpr env st (.call fn args retTy isExt) = .ok r) :
    reservedRuntimeCallee fn = true := by
  cases isExt
  · -- L2's non-capture lemma, applied to a one-entry environment named `fn`: such an
    -- environment captures the call unless `fn` is reserved, and an environment of
    -- unreserved names captures no call `evalExpr` succeeds on.
    cases hres : reservedRuntimeCallee fn with
    | true => rfl
    | false =>
      have hnone := FuncEnv.callTarget?_of_evalExpr_ok
        (Φ := [({ name := fn, params := [], retTy := retTy, body := .unreachable }, 0)])
        (fun p hp => by rw [List.mem_singleton] at hp; subst hp; exact hres) h
      simp only [FuncEnv.callTarget?, FuncEnv.lookup?, BEq.rfl, ↓reduceIte, Option.map_some,
        reduceCtorEq] at hnone
  · -- `evalExpr` refuses every extern call.
    dsimp only [evalExpr] at h
    cases hvl : evalVarList env args <;> rw [hvl] at h <;> simp only [↓reduceIte, reduceCtorEq] at h

/-- Under an environment of unreserved names every successful `evalExpr` is the let head,
    whatever the callee slot holds: a call `evalExpr` succeeds on names a reserved
    intrinsic, which no entry captures. -/
theorem letHeadR_of_evalExpr_ok (Φ : List LNIRDecl)
    (hfresh : ∀ ld ∈ Φ, reservedRuntimeCallee ld.name = false)
    (callee? : Option (VarEnv → HeapState → LNIRCode → Except UBError (Val × HeapState)))
    (env : VarEnv) (st : HeapState) (val : LNIRExpr) (r : Val × HeapState)
    (h : evalExpr env st val = .ok r) : letHeadR Φ callee? env st val = .ok r := by
  cases val <;> try exact h
  case call fn args retTy isExt =>
    cases isExt
    · have hmiss : lookupFuncRec? Φ fn = none := by
        cases hlk : lookupFuncRec? Φ fn with
        | none => rfl
        | some ld =>
          obtain ⟨hm, hn⟩ := lookupFuncRec?_mem Φ fn ld hlk
          have h1 := hfresh ld hm
          rw [hn, evalExpr_call_ok_reserved env st fn args retTy false r h] at h1
          exact nomatch h1
      dsimp only [letHeadR]
      rw [hmiss]
      exact h
    · exact h

theorem evalCodeR_extend_of_ok (Φ : List LNIRDecl) (fuel : Nat) (env : VarEnv)
    (st : HeapState) (c : LNIRCode) (v : Val) (st' : HeapState)
    (hfresh : ∀ ld ∈ Φ, reservedRuntimeCallee ld.name = false)
    (h : evalCode fuel env st c = .ok (v, st')) :
    evalCodeR Φ fuel env st c = .ok (v, st') := by
  rw [← evalCodeRAux_nil fuel none] at h
  have hhead : ∀ c2 env st val r, letHeadR [] none env st val = .ok r →
      letHeadR Φ c2 env st val = .ok r := fun c2 env st val r hr =>
    letHeadR_of_evalExpr_ok Φ hfresh c2 env st val r (by rwa [letHeadR_nil] at hr)
  cases fuel with
  | zero => exact evalCodeRAux_sim [] Φ 0 0 (Nat.le_refl 0) none none (hhead none) c env st _ h
  | succ n =>
    exact evalCodeRAux_sim [] Φ (n + 1) (n + 1) (Nat.le_refl _) none (some (evalCodeR Φ n))
      (hhead _) c env st _ h

/-- Every lowered name the positional clauses admit is unreserved. -/
theorem DeclEnvLowersPosR.fresh :
    ∀ (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx × Nat)) (Φ : List LNIRDecl),
      DeclEnvLowersPosR Δ Φ → ∀ ld ∈ Φ, reservedRuntimeCallee ld.name = false
  | [], [], _, _, hm => nomatch hm
  | [], _ :: _, h, _, _ => nomatch h
  | _ :: _, [], h, _, _ => nomatch h
  | (_, _, _) :: Δ, _ :: Φ, h, ld, hm => by
    obtain ⟨_, hres, _, htail⟩ := h
    cases hm with
    | head => exact hres
    | tail _ hm => exact DeclEnvLowersPosR.fresh Δ Φ htail ld hm

theorem DeclEnvLowersR.fresh
    (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx × Nat)) (Φ : List LNIRDecl)
    (h : DeclEnvLowersR Δ Φ) :
    ∀ ld ∈ Φ, reservedRuntimeCallee ld.name = false :=
  DeclEnvLowersPosR.fresh Δ Φ h.1

/-- At a call site whose context resolves `fn` to `sym` and coheres with the pairing, the
    source lookup by Lean name and the LNIR lookup by mangled symbol land on ONE position:
    coherence pins `sym` to the lowered name where the source lookup stops, and the
    pairwise freshness of lowered names keeps every earlier position from matching it. -/
theorem lookupDeclRec?_align :
    ∀ (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx × Nat)) (Φ : List LNIRDecl),
      DeclEnvLowersPosR Δ Φ →
      ∀ (ctx : RealBridgeCtx) (fn : Lean.Name) (sym : String)
        (sd : Lean.Compiler.LCNF.Decl .impure) (sdCtx : RealBridgeCtx),
      CtxMapsEnvR ctx Δ Φ → ctx.findLocalCallee? fn = some sym →
      lookupDeclRec? (declEnvR Δ) fn = some (sd, sdCtx) →
      ∃ fuelD ld, (sd, sdCtx, fuelD) ∈ Δ ∧ lookupFuncRec? Φ sym = some ld ∧
        lowerRealLCNFDecl fuelD sdCtx sd ld.name = .ok ld
  | [], [], _, _, _, _, _, _, _, _, hlk => nomatch hlk
  | [], _ :: _, h, _, _, _, _, _, _, _, _ => nomatch h
  | _ :: _, [], h, _, _, _, _, _, _, _, _ => nomatch h
  | (sd0, c0, f0) :: Δ, ld0 :: Φ, hpos, ctx, fn, sym, sd, sdCtx, hmap, hsym, hlk => by
    obtain ⟨hlow, _, hfresh, hpos'⟩ := hpos
    obtain ⟨hhead, hmap'⟩ := hmap
    simp only [declEnvR, List.map_cons] at hlk
    dsimp only [lookupDeclRec?] at hlk
    split at hlk
    · next hb =>
      injection hlk with hlk
      cases hlk
      have hsym0 : sym = ld0.name := hhead sym (by rw [eq_of_beq hb]; exact hsym)
      refine ⟨f0, ld0, List.mem_cons_self .., ?_, hlow⟩
      simp only [lookupFuncRec?, hsym0, BEq.rfl, ↓reduceIte]
    · obtain ⟨fuelD, ld, hmem, hlkΦ, hlow'⟩ :=
        lookupDeclRec?_align Δ Φ hpos' ctx fn sym sd sdCtx hmap' hsym hlk
      refine ⟨fuelD, ld, List.mem_cons_of_mem _ hmem, ?_, hlow'⟩
      obtain ⟨hm, hn⟩ := lookupFuncRec?_mem Φ sym ld hlkΦ
      have hne : (ld0.name == sym) = false := by
        cases hb : (ld0.name == sym) with
        | false => rfl
        | true => exact absurd (by rw [hn, eq_of_beq hb]) (hfresh ld hm)
      simp only [lookupFuncRec?, hne, Bool.false_eq_true, ↓reduceIte]
      exact hlkΦ

/-- The alignment the recursion headline's call case consumes: under an admitted
    environment, a coherent call site resolves to the LOWERING of the callee its source
    lookup finds, at that entry's own context and fuel, and that callee's own context
    coheres with the whole pairing again, so its nested call sites align too. -/
theorem declEnvLowersR_lookup_align
    (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx × Nat)) (Φ : List LNIRDecl)
    (h : DeclEnvLowersR Δ Φ) (ctx : RealBridgeCtx) (fn : Lean.Name) (sym : String)
    (sd : Lean.Compiler.LCNF.Decl .impure) (sdCtx : RealBridgeCtx)
    (hmap : CtxMapsEnvR ctx Δ Φ) (hsym : ctx.findLocalCallee? fn = some sym)
    (hlk : lookupDeclRec? (declEnvR Δ) fn = some (sd, sdCtx)) :
    ∃ fuelD ld, lookupFuncRec? Φ sym = some ld ∧
      lowerRealLCNFDecl fuelD sdCtx sd ld.name = .ok ld ∧ CtxMapsEnvR sdCtx Δ Φ := by
  obtain ⟨fuelD, ld, hmem, hlkΦ, hlow⟩ :=
    lookupDeclRec?_align Δ Φ h.1 ctx fn sym sd sdCtx hmap hsym hlk
  exact ⟨fuelD, ld, hlkΦ, hlow, h.2 _ hmem⟩

theorem lowerRealLCNFDecl_soundR_base (fuel : Nat) (ctx : RealBridgeCtx)
    (Φ : List LNIRDecl)
    (decl : Lean.Compiler.LCNF.Decl .impure) (args : List Val) (hst hst' : HeapState)
    (v : Val) (d : LNIRDecl) (mangled : String)
    (hfresh : ∀ ld ∈ Φ, reservedRuntimeCallee ld.name = false)
    (h_lower : lowerRealLCNFDecl fuel ctx decl mangled = .ok d)
    (h_eval : evalRealLCNFDecl fuel ctx decl args hst = .ok (v, hst')) :
    evalCodeR Φ fuel
      ((d.params.zip args).foldl (fun acc (p, val) => acc.bind p.id val) VarEnv.empty)
      hst d.body = .ok (v, hst') :=
  evalCodeR_extend_of_ok Φ fuel _ hst d.body v hst' hfresh
    (lowerRealLCNFDecl_sound fuel ctx decl args hst hst' v d mangled h_lower h_eval)

/-! ### Part I — fail-closed honesty for recursive join points (pinned files, unedited) -/

theorem evalStep_recursive_jp_unsupported (fuel : Nat) (ctx : RealBridgeCtx) (env : LEnv)
    (st : HeapState) (decl : Lean.Compiler.LCNF.FunDecl .impure)
    (k : Lean.Compiler.LCNF.Code .impure)
    (h : hasJmpToPure fuel decl.fvarId (.inl decl.value) = true) :
    evalStep (fuel + 1) ctx env st (.inl (.jp decl k)) =
      .error (.unsupportedCall "recursive join point") := by
  rw [evalStep.eq_def]
  simp only [h, ↓reduceIte]

theorem lowerImpureStepPure_recursive_jp_rejected (fuel : Nat) (ctx : RealBridgeCtx)
    (st : RealBridgeState) (decl : Lean.Compiler.LCNF.FunDecl .impure)
    (k : Lean.Compiler.LCNF.Code .impure)
    (h : hasJmpToPure fuel decl.fvarId (.inl decl.value) = true) :
    lowerImpureStepPure (fuel + 1) ctx st (.inl (.jp decl k)) =
      .error s!"[lean-native] unsupported recursive join point `{decl.fvarId.name}`: no qualified loop lowering" := by
  rw [lowerImpureStepPure.eq_def]
  simp only [h, ↓reduceIte]

end LeanNative.Proofs
