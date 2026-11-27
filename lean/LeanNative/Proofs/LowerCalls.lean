import LeanNative.IR.RealLCNFBridge
import LeanNative.IR.RealLCNFCallSemantics
import LeanNative.Proofs.RealLCNFBridgeProofs
import LeanNative.Proofs.RealLCNFBridge.CallsF

/-!
## L2 contract (roadmap/HORIZONS.md, H1 rung L2 "Calls")

Authoritative row (`roadmap/HORIZONS.md`): "L2 Calls — Both semantics take a function
environment. Non-recursive calls between declarations are proved. | Without it the theorem
is empty for almost all real code." Leaf row: files `Semantics/Eval.lean`,
`Proofs/LowerCalls.lean`; needs L1, H1.F; accept "leaf `0 sorryAx`; matrix moves".

Contract-first statement, in the same form as the L1 contract
(`RealLCNFBridgeProofs.lean:10-125`). The contract commit of this leaf is 415256b1 (the
doc-only form of this block); a review round reshaped the environments to
per-declaration entries — the signatures below are the corrected ones L3 builds against.
This leaf was pipelined on the L1 contract (fa715a8a) and folded onto the landed L1 merge
(e8a4c1aa). Nothing here changes the arity of any existing evaluator — the function
environments arrive as a conservative layer whose empty instance is the old semantics by
theorem (`evalCodeF_nil`, `evalStepF_nil`, `evalRealLCNFDeclF_nil`, landed WITH the
definitions). H1.F's pin (`SpecLocked.lean`) freezes `lowerRealLCNFDecl_sound`, which
this leaf does not touch.

### What L2 closes (the vacuity the matrix records)

`lowerRealLCNFDecl` already lowers a call to another local user function
(`LetValue.fap fn args` with `ctx.findLocalCallee? fn = some sym`, emitted as
`.letBind dst rawDeclTy (.call sym argVars rawDeclTy false) k`,
`IR/RealLCNFBridge.lean:723-729`), but `RealLCNFSemantics.evalLetValue` deliberately
returns `.error (.unsupportedCall fn.toString)` whenever `(ctx.findLocalCallee? fn).isSome`,
so `lowerRealLCNFDecl_sound`'s forward simulation is vacuous for every declaration that
calls a local helper (`scripts/lcnf_coverage.py` methodology:
`lowered_vacuous_local_call`, classified under `lowered_unproved` "until rung L2 adds a
function environment to both semantics"). L2 adds that environment to both semantics and
proves the lowering of non-recursive local calls sound end to end.

### Per-declaration entries

The driver builds a SEPARATE context and fuel for each declaration
(`ingestImpureDeclViaReal`: `paramTypeMap` is keyed on the declaration's own parameter
`FVarId`s, `allowStage1DHeap` is per-declaration, `ctorLayouts`/`tupleStructCtors` are
seeded only from constructors that appear in that declaration, `typeOverrides` from its
own type expressions). A callee evaluated under the CALLER's context would describe a
module the driver never emits — concretely, a callee `uset`/`sset` on a constructor the
caller never mentions misses `ctx.findLayout?` and falls back to the raw slot index. So
environment entries carry their declaration's own context and fuel, the call rule runs
the callee under them, and `DeclEnvLowers` requires the per-entry lowering. On the LNIR
side the entries carry the fuel (`evalCodeF` takes no context), and a call with the wrong
argument count errors (review F4 — the source side's `bindParams` is strict).

### New definitions

In `lean/LeanNative/Semantics/Eval.lean` (append-only; namespace `LeanNative.Semantics`):
`FuncEnv := List (LNIRDecl × Nat)`; `FuncEnv.lookup?` (first match by name, paired with
the STRICT SUFFIX after it); `FuncEnv.callTarget?`; `LNIRExpr.isCall` and `callFreeCode`
(no `.call` at all — the predicate under which the environment is irrelevant,
`evalCodeF_callFree`); and `evalCodeF (Φ : FuncEnv) (fuel : Nat) : VarEnv → HeapState →
LNIRCode → Except UBError (Val × HeapState)`, mirroring `evalCode` clause for clause with
ONE new rule: a let-bound non-extern `.call` whose symbol is bound in `Φ` evaluates the
callee body under the strict suffix at the ENTRY's own fuel, with the declaration-entry
binding convention `(ld.params.zip vals).foldl (fun acc (p, val) => acc.bind p.id val)
VarEnv.empty`, erroring on an argument-count mismatch. The environment is stratified —
a callee body runs under the strict suffix after its entry — so INSIDE an
environment-run callee, a self or backward call misses the lookup under the
pairwise-fresh names `DeclEnvLowers` admits and keeps the old `evalExpr` behavior; a
top-level body whose own declaration is an entry of the environment resolves its
self-call ONCE against that entry before the unrolled occurrence misses (depth-1
unrolling — the proofs below need no decl-not-in-environment hypothesis, they induct on
the environment structure). Termination is lexicographic on `(Φ.length, code)`.

In `lean/LeanNative/IR/RealLCNFCallSemantics.lean` (NEW file; namespace
`LeanNative.IR.RealLCNFSemantics`; imports `LeanNative.IR.RealLCNFSemantics` only, so the
H1.1 separation pin is preserved; a new file rather than an append because
`scripts/lcnf_coverage_results.json` sha-pins `IR/RealLCNFSemantics.lean`):
`DeclEnv := List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx × Nat)`;
`DeclEnv.lookup?`; `DeclEnv.callTarget?`; `evalStepF (Δ : DeclEnv) (fuel : Nat)
(ctx : RealBridgeCtx) (env : LEnv) (st : HeapState) (target : ...)`, mirroring `evalStep`
clause for clause with ONE new rule, replacing exactly the arm the old semantics
deliberately errors on: a `.let` whose value is `.fap fn args _` with
`(ctx.findLocalCallee? fn).isSome` (the call site's gate is the CALLER's map — the map
the lowerer consulted when it emitted the call) and `fn` bound in `Δ` runs the callee
declaration under the ENTRY's own context and fuel and the strict suffix
(`bindParams ctxD true LEnv.empty`, the declaration-entry convention; `.extern` errors).
A lookup miss keeps the old `.error (.unsupportedCall fn.toString)` byte for byte.
Termination is lexicographic on `(Δ.length, fuel)`. `evalRealLCNFCodeF` /
`evalRealLCNFDeclF` mirror the entry points.

In this file (namespace `LeanNative.Proofs`): `CtxMapsEnv` and `DeclEnvLowers` —
definitions below (`reservedRuntimeName` lives with the non-capture lemmas in
`RealLCNFBridge/CallsF.lean`, imported here; the duplicate definition this file briefly
carried is dropped). The contract's `CodeRefinesF` was defined for the two gate
restatements; with the post-pass removed (next section) it had NO consumer, so it is
DROPPED rather than kept as dead surface — a future gate that needs the L2 form of
refinement states it at its use site over `evalCodeF Φ`.

### The gate restatements: removed with the post-pass (decision record)

The L1 contract block said L2 "restates them with that one extra binder", which included
environment-generalized forms of the two `applyValidatedCompression` theorems. That was
not provable as one-extra-binder work, and the mismatch was reported rather than silently
patched: `runSymbolicValidatedDecl` accepts via `symbolicCodeRefines`, whose default
`letBind` arm compares non-scalar right-hand sides with `lnirExprEvalEq`
(`SymbolicTVRefinesDefs.lean:297-303`), and `lnirExprEvalEq` returns `true` on matching
`.call` pairs (`:61-62`) — measured on the pre-guard gate: a call-bearing pair with a
commuted scalar tail was ACCEPTED with the assurance downgrade. The checker's guarantee
(`symbolicValidatedDeclOpt_sound`) is env-free and vacuous past the first `Φ`-bound call,
and the generic transfer `CodeRefines → CodeRefinesF` is false. An interim ruling (a
call-free guard in the gate) was implemented, measured, and then superseded the same day:
a review proved the compression post-pass never changes any declaration (straight-line
early-returns; `ite` candidates are the rejected fresh-collapse shape; the tuple branch
is unreachable), so L1 REMOVES `applyValidatedCompression` entirely — the
rung's "proved, validated by a proved checker, or removed" taken at "removed". The two
restatements (`applyValidatedCompression_refinesF`, `lowerRealLCNFDecl_driver_soundF`)
therefore cease to exist; `lowerRealLCNFDecl_soundF` below is the L2 headline. The
guard's record (edits, red measurement, repin fixtures) is preserved for the L1 lane in
`l2-probes/guard-b.patch` and `l2-probes/red-gate.lean`.

### Theorems proved by this leaf (the L2 contract L3 builds against)

Conservativity — the old semantics is the empty-environment instance (landed with the
definitions, per review F6):

```
theorem evalCodeF_nil (fuel : Nat) (env : VarEnv) (st : HeapState) (c : LNIRCode) :
    evalCodeF [] fuel env st c = evalCode fuel env st c

theorem evalStepF_nil (fuel : Nat) (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
    (target : Lean.Compiler.LCNF.Code .impure ⊕
      (Val × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure))) :
    evalStepF [] fuel ctx env st target = evalStep fuel ctx env st target

theorem evalRealLCNFDeclF_nil (fuel : Nat) (ctx : RealBridgeCtx)
    (decl : Lean.Compiler.LCNF.Decl .impure) (args : List Val) (st : HeapState) :
    evalRealLCNFDeclF [] fuel ctx decl args st = evalRealLCNFDecl fuel ctx decl args st
```

Call-free conservativity — on call-free code the environment is irrelevant:

```
theorem evalCodeF_callFree (Φ : FuncEnv) (fuel : Nat) (env : VarEnv) (st : HeapState)
    (c : LNIRCode) (h : callFreeCode c = true) :
    evalCodeF Φ fuel env st c = evalCode fuel env st c
```

Step-level forward simulation with both environments (the L2 workhorse; extends
`lowerImpureStepPure_sound` with the environment binders, the per-entry `DeclEnvLowers`
hypothesis and the caller-map coherence hypothesis — hypothesis shape otherwise verbatim
from L1):

```
theorem lowerImpureStepPure_soundF (fuel : Nat) (ctx : RealBridgeCtx)
    (Δ : DeclEnv) (Φ : FuncEnv) (st st' : RealBridgeState)
    (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
    (target : Lean.Compiler.LCNF.Code .impure ⊕
      (VarId × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure)))
    (code : LNIRCode) :
    DeclEnvLowers Δ Φ →
    CtxMapsEnv ctx Δ Φ →
    BridgeStateInv st lenv venv →
    lowerImpureStepPure fuel ctx st target = .ok (code, st') →
    (match target with
      | .inl c => evalStepF Δ fuel ctx lenv hst (.inl c) = .ok (v, hst')
      | .inr (condVar, isBool, idx, discr?, alts) =>
        condVar < st.nextVarId ∧
        (∀ dx, discr? = some dx → (st.lookupFVar? dx).isSome = true) ∧
        (lnirTypeEq (st.getVarType condVar) .i1 = true → isBool = true) ∧
        ∃ cond, venv condVar = some cond ∧
          evalStepF Δ fuel ctx lenv hst (.inr (cond, isBool, idx, discr?, alts)) = .ok (v, hst')) →
    evalCodeF Φ fuel venv hst code = .ok (v, hst')
```

Code- and declaration-level corollaries (extend `lowerRealLCNFCode_sound` /
`lowerRealLCNFDecl_sound` the same way):

```
theorem lowerRealLCNFCode_soundF (fuel : Nat) (ctx : RealBridgeCtx)
    (Δ : DeclEnv) (Φ : FuncEnv) (st : RealBridgeState)
    (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
    (code : Lean.Compiler.LCNF.Code .impure) (lnir : LNIRCode) (st' : RealBridgeState)
    (h_env : DeclEnvLowers Δ Φ)
    (h_map : CtxMapsEnv ctx Δ Φ)
    (h_inv : BridgeStateInv st lenv venv)
    (h_lower : lowerRealLCNFCode fuel ctx st code = .ok (lnir, st'))
    (h_eval : evalRealLCNFCodeF Δ fuel ctx lenv hst code = .ok (v, hst')) :
    evalCodeF Φ fuel venv hst lnir = .ok (v, hst')

theorem lowerRealLCNFDecl_soundF (fuel : Nat) (ctx : RealBridgeCtx)
    (Δ : DeclEnv) (Φ : FuncEnv)
    (decl : Lean.Compiler.LCNF.Decl .impure) (args : List Val) (hst hst' : HeapState)
    (v : Val) (d : LNIRDecl) (mangled : String)
    (h_env : DeclEnvLowers Δ Φ)
    (h_map : CtxMapsEnv ctx Δ Φ)
    (h_lower : lowerRealLCNFDecl fuel ctx decl mangled = .ok d)
    (h_eval : evalRealLCNFDeclF Δ fuel ctx decl args hst = .ok (v, hst')) :
    evalCodeF Φ fuel
      ((d.params.zip args).foldl (fun acc (p, val) => acc.bind p.id val) VarEnv.empty)
      hst d.body = .ok (v, hst')
```

`lowerRealLCNFDecl_soundF` is the L2 headline: with `Δ = []` and `Φ = []`,
`DeclEnvLowers [] []` and `CtxMapsEnv ctx [] []` hold and `evalRealLCNFDeclF_nil`
collapses it to L1's `lowerRealLCNFDecl_sound` shape, so it is the strict generalization
the L1 contract names. The per-entry fuels make the call case of the proof apply the
declaration-level statement directly at the callee's own `(fuel_i, ctx_i)` — no
source-side fuel monotonicity is needed. The helper lemmas landed as expected:
`FuncEnv.lookup?_length` / `DeclEnv.lookup?_length` (strict-suffix decrease, with the
evaluators), `evalCodeF_fuel_mono_step` and the per-case step mirrors (parameterized
over the call rule, L3's recorded option (b)) in `RealLCNFBridge/CallsF.lean`, and the
lookup-alignment lemma below (`declEnvLowers_lookup_align`: at a resolved call site the
caller-map hit plus per-position coherence pins the mangled symbol to the aligned
entry's name, and the tail-freshness clause keeps every earlier lowered name distinct,
so the two lookups land on the same position with the aligned suffixes). The three
headline theorems are PROVED at the end of this file; no case resisted
parameterization. Two byte-level findings recorded while proving the call case:
`lowerCallArgsWithErasedPure` preserves argument counts in general (each arm conses
exactly one variable; an erased argument contributes a fresh zero-bound `.unit`
variable — `RealLCNFBridge.lean:576-589`), and `evalArg` ERRORS on an erased/`type`
argument (`.typeError "erased runtime argument"`) rather than producing `.u64 0`, so a
source-side `evalArgs` success forces every argument of a resolved call to be `.fvar`
and the zero-bind list empty — `lowerCallArgs_align` below therefore covers exactly the
shape the SOURCE SEMANTICS accepts, which is narrower than what the lowerer emits: a
resolved local call with an erased or `type` argument goes through the zero-bind path
in the lowering but errors on the source side (`evalArgs` at
`RealLCNFCallSemantics.lean:204` via `evalArg` at `RealLCNFSemantics.lean:317`), so the
soundness theorem says nothing about such calls and they STAY `lowered_unproved`
(option 2: recorded in the coverage handoff below rather than given
placeholder semantics, which would be a semantics change outside this unit).

### Acceptance (quoted) and gates

- "leaf `0 sorryAx`": every theorem in the proved set lands kernel-checked; the leaf's
  theorems are appended to `AxiomAudit.lean`'s `auditedTheoremNames` with the pinned
  count raised exactly.
- "matrix moves": the semantics and proofs landed here are the condition
  `scripts/lcnf_coverage.py`'s methodology names for reclassifying
  `lowered_vacuous_local_call` rows out of `lowered_unproved` — for resolved calls whose
  arguments are all `.fvar`. Coverage handoff: a resolved local
  call with an erased or `type` argument is NOT covered by the theorem (the source
  semantics errors on it, paragraph above), so such rows stay `lowered_unproved` and the
  matrix owner reclassifies only the all-`.fvar` rows. That script and its committed
  results are H1.0's files; the handoff is lead-accepted and the commit is the matrix
  owner's, once this leaf merges.
- Gates: `(cd lean && lake build TurboLean LeanNative)` (the new modules are in the
  `LeanNative` lib's `.andSubmodules` glob);
  `turbo-lean --json audit-spec lean/TurboLean/Spec.lean` (98/98) and
  `lean/LeanNative/Spec.lean` (124/124) — both files untouched by this leaf;
  `turbo-lean --json audit-spec --policy strict-proofs lean/LeanNative/Proofs/LowerCalls.lean`
  (ok; 0 vacuous, 0 trivial, 0 droppable hypotheses) — this file is added to
  `scripts/ci_verify.sh`'s strict-proofs loop in this leaf (one-line list addition, lead's
  scope assignment); `python3 scripts/sync_docs_inventory.py --check`. Executable guards
  for the call semantics land in `lean/LeanNative/Tests/RealLCNFCallTests.lean`: a
  two-declaration environment where the caller's result is wrong unless the callee body
  actually runs; a call-arity mismatch errors; a nested chain whose middle declaration
  resolves its own callee only under ITS entry context (with a caller-context negative
  control, pinning review F1's fix); a callee that exhausts its own entry fuel while the
  ambient fuel is ample (pinning the per-entry fuel); a self-call that resolves ONCE —
  a depth-1 STOP run (the suffix-exercised branch carries no call) is ok, and the
  depth-2 miss keeps the old `.unsupportedCall`-shaped error; and `Δ = [] / Φ = []`
  runs equal to the old evaluators.
-/

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

/-- The given (caller) context's mangled-name map COHERES with the environment pairing:
    position by position, WHEN it maps the source declaration's name it maps it to the
    lowered declaration's name (partial coherence; review F1 of e82678627: the strong
    equality `findLocalCallee? sd.name = some ld.name` fails for an `a → b → c` chain
    under per-declaration `localCallees` — the top context need not know `c`, which is
    exactly test 3b's environment). The top-level theorems take it for the top caller's
    context; `DeclEnvLowers` carries it per entry for that entry's OWN context, so
    nested call sites resolve against the same pairing; at a RESOLVED call site the
    caller's map hit plus this coherence pins the mangled symbol to the entry's name,
    and the pairwise freshness clause then lands the `Φ` lookup at the same position. -/
def CtxMapsEnv (ctx : RealBridgeCtx) : DeclEnv → FuncEnv → Prop
  | [], [] => True
  | (sd, _, _) :: Δ, (ld, _) :: Φ =>
      (∀ m, ctx.findLocalCallee? sd.name = some m → m = ld.name) ∧ CtxMapsEnv ctx Δ Φ
  | _, _ => False

/-- Pointwise "Δ lowers to Φ": positionally, each source declaration lowers UNDER ITS OWN
    context and fuel (the driver builds per-declaration contexts) to
    the corresponding LNIR declaration at the same fuel, mangled names are fresh
    (unreserved, not repeated later in `Φ`), the entry's own context maps the TAIL
    pairing (so the entry's nested call sites resolve), and the tails relate. A recursive
    `Prop` (strict-proofs scope admits no new `inductive`); destructure with
    `obtain`/`And` and induct on the list structure. -/
def DeclEnvLowers : DeclEnv → FuncEnv → Prop
  | [], [] => True
  | (sd, ctxD, fuelD) :: Δ, (ld, fuelL) :: Φ =>
      fuelL = fuelD ∧
      lowerRealLCNFDecl fuelD ctxD sd ld.name = .ok ld ∧
      reservedRuntimeName ld.name = false ∧
      (∀ p ∈ Φ, p.1.name ≠ ld.name) ∧
      CtxMapsEnv ctxD Δ Φ ∧
      DeclEnvLowers Δ Φ
  | _, _ => False

/-! ### Conservativity: the old semantics is the empty-environment instance -/

theorem FuncEnv.callTarget?_nil (e : LNIRExpr) :
    LeanNative.Semantics.FuncEnv.callTarget? [] e = none := by
  cases e <;> try rfl
  case call fn args ty ext => cases ext <;> rfl

theorem DeclEnv.callTarget?_nil (ctx : RealBridgeCtx)
    (lv : Lean.Compiler.LCNF.LetValue .impure) :
    LeanNative.IR.RealLCNFSemantics.DeclEnv.callTarget? [] ctx lv = none := by
  cases lv <;> rfl

theorem evalCodeF_nil (fuel : Nat) (env : VarEnv) (st : HeapState) (c : LNIRCode) :
    evalCodeF [] fuel env st c = evalCode fuel env st c := by
  induction c generalizing env st with
  | letBind dst ty val k ih =>
    unfold evalCodeF evalCode
    split
    · rename_i heq
      rw [FuncEnv.callTarget?_nil] at heq
      exact nomatch heq
    · simp only [ih]
  | rawStore ptrVar idxVar valVar elemTy k ih =>
    unfold evalCodeF evalCode
    simp only [ih]
  | incRef objVar count k ih =>
    unfold evalCodeF evalCode
    simp only [ih]
  | decRef objVar count k ih =>
    unfold evalCodeF evalCode
    simp only [ih]
  | ite condVar t e iht ihe =>
    unfold evalCodeF evalCode
    simp only [iht, ihe]
  | seqFor idxVar loVar hiVar accVar accInit accTy stepBody k ihStep ihK =>
    unfold evalCodeF evalCode
    simp only [ihStep, ihK]
  | parFor outVar lenVar inputs elemTy kernel k ih =>
    unfold evalCodeF evalCode
    simp only [ih]
  | ret v => simp only [evalCodeF, evalCode]
  | unreachable => simp only [evalCodeF, evalCode]

theorem evalStepF_nil (fuel : Nat) (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
    (target : Lean.Compiler.LCNF.Code .impure ⊕
      (Val × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure))) :
    evalStepF [] fuel ctx env st target = evalStep fuel ctx env st target := by
  induction fuel generalizing env st target with
  | zero => simp only [evalStepF, evalStep]
  | succ fuel ih =>
    unfold evalStepF evalStep
    cases target with
    | inr p =>
      obtain ⟨cond, isBool, idx, discr?, alts⟩ := p
      simp only [ih]
      rfl
    | inl code =>
      cases code
      case «let» decl k =>
        -- Iota-reduce the ground matchers on `Sum.inl (.let decl k)` first (simp's
        -- matcher reduction; `unfold` leaves them stuck), then split the
        -- `callTarget?` matcher — it cannot be rewritten under its `hc` binder —
        -- and refute the some-branch with the nil lemma.
        simp only [ih]
        split
        · rename_i hc
          rw [DeclEnv.callTarget?_nil] at hc
          exact nomatch hc
        · try simp only [ih]
          try rfl
      all_goals (simp only [ih]; try rfl)

theorem evalRealLCNFDeclF_nil (fuel : Nat) (ctx : RealBridgeCtx)
    (decl : Lean.Compiler.LCNF.Decl .impure) (args : List Val) (st : HeapState) :
    evalRealLCNFDeclF [] fuel ctx decl args st = evalRealLCNFDecl fuel ctx decl args st := by
  unfold evalRealLCNFDeclF evalRealLCNFDecl evalRealLCNFCodeF evalRealLCNFCode
  cases decl.value with
  | extern _ => rfl
  | code c =>
    cases bindParams ctx true LEnv.empty decl.params.toList args with
    | ok env => exact evalStepF_nil fuel ctx env st (.inl c)
    | error _ => rfl

/-! ### Call-free conservativity: on call-free code the environment is irrelevant -/

theorem FuncEnv.callTarget?_of_not_isCall {e : LNIRExpr} (h : (!e.isCall) = true)
    (Φ : FuncEnv) : LeanNative.Semantics.FuncEnv.callTarget? Φ e = none := by
  cases e <;> first | rfl | exact nomatch h

theorem evalCodeF_callFree (Φ : FuncEnv) (fuel : Nat) (env : VarEnv) (st : HeapState)
    (c : LNIRCode) (h : callFreeCode c = true) :
    evalCodeF Φ fuel env st c = evalCode fuel env st c := by
  induction c generalizing env st with
  | letBind dst ty val k ih =>
    unfold evalCodeF evalCode
    simp only [callFreeCode, Bool.and_eq_true] at h
    split
    · rename_i heq
      rw [FuncEnv.callTarget?_of_not_isCall h.1] at heq
      exact nomatch heq
    · simp only [ih _ _ h.2]
  | rawStore ptrVar idxVar valVar elemTy k ih =>
    unfold evalCodeF evalCode
    simp only [callFreeCode] at h
    simp only [ih _ _ h]
  | incRef objVar count k ih =>
    unfold evalCodeF evalCode
    simp only [callFreeCode] at h
    simp only [ih _ _ h]
  | decRef objVar count k ih =>
    unfold evalCodeF evalCode
    simp only [callFreeCode] at h
    simp only [ih _ _ h]
  | ite condVar t e iht ihe =>
    unfold evalCodeF evalCode
    simp only [callFreeCode, Bool.and_eq_true] at h
    simp only [iht _ _ h.1, ihe _ _ h.2]
  | seqFor idxVar loVar hiVar accVar accInit accTy stepBody k ihStep ihK =>
    unfold evalCodeF evalCode
    simp only [callFreeCode, Bool.and_eq_true] at h
    simp only [ihStep _ _ h.1, ihK _ _ h.2]
  | parFor outVar lenVar inputs elemTy kernel k ih =>
    unfold evalCodeF evalCode
    simp only [callFreeCode] at h
    simp only [ih _ _ h]
  | ret v => simp only [evalCodeF, evalCode]
  | unreachable => simp only [evalCodeF, evalCode]

/-! ### U6: lookup alignment, the environment-length induction, the headline theorems

The fuel induction inside `lowerImpureStepPure_soundF_aux` mirrors L1's
`lowerImpureStepPure_sound_aux` arm for arm (the `RealLCNFBridge/CallsF.lean` mirrors
carry the per-case work); the ONE new obligation is `lowerLetStep_soundF`'s `hcall`,
discharged with the alignment lemmas below and the OUTER induction hypothesis (on the
environment length) at the strictly shorter aligned suffixes. The per-entry fuels make
the callee's obligation exactly the declaration-level statement at `(fuelD, ctxD)` — no
source-side fuel monotonicity. -/

/-- Every lowered declaration an admitted environment carries is unreserved — the
    `hres` input of the CallsF mirrors, read off `DeclEnvLowers` clause by clause. -/
theorem declEnvLowers_reserved : ∀ (Δ : DeclEnv) (Φ : FuncEnv), DeclEnvLowers Δ Φ →
    ∀ p ∈ Φ, reservedRuntimeName p.1.name = false
  | [], [], _, _, hp => nomatch hp
  | _ :: _, [], _, _, hp => nomatch hp
  | [], _ :: _, h, _, _ => nomatch h
  | (_, _, _) :: Δ, (_, _) :: Φ, h, p, hp => by
    obtain ⟨_, _, hres0, _, _, htail⟩ := h
    cases hp with
    | head => exact hres0
    | tail _ hp => exact declEnvLowers_reserved Δ Φ htail p hp

/-- The entry `FuncEnv.lookup?` returns is a member of the environment, and its name is
    the queried symbol (the `beq`-hit clause). -/
theorem funcEnv_lookup?_mem_name : ∀ (Φ : FuncEnv) (fn : String) (p : LNIRDecl × Nat)
    (Φ' : FuncEnv), LeanNative.Semantics.FuncEnv.lookup? Φ fn = some (p, Φ') →
    p ∈ Φ ∧ p.1.name = fn
  | [], _, _, _, h => nomatch h
  | p0 :: Φ, fn, p, Φ', h => by
    unfold LeanNative.Semantics.FuncEnv.lookup? at h
    split at h
    · rename_i hbe
      injection h with h
      rcases Prod.mk.inj h with ⟨rfl, rfl⟩
      exact ⟨.head _, eq_of_beq hbe⟩
    · rcases funcEnv_lookup?_mem_name Φ fn p Φ' h with ⟨hmem, hname⟩
      exact ⟨.tail _ hmem, hname⟩

/-- The lookup-alignment lemma (contract-named): at a RESOLVED call site (the caller's
    map knows `fn`), a `DeclEnv.lookup?` hit lands `FuncEnv.lookup?` on the
    corresponding position. The per-position coherence (`CtxMapsEnv`) pins the mangled
    symbol to that entry's lowered name, and the tail-freshness clause of
    `DeclEnvLowers` keeps every earlier lowered name distinct from it, so neither lookup
    stops early on the other's entry; the returned suffixes are the positionally aligned
    ones, still related by `DeclEnvLowers` and by the entry's own `CtxMapsEnv`. -/
theorem declEnvLowers_lookup_align :
    ∀ (Δ : DeclEnv) (Φ : FuncEnv) (ctx : RealBridgeCtx) (fn : Lean.Name) (sym : String)
      (sd : Lean.Compiler.LCNF.Decl .impure) (ctxD : RealBridgeCtx) (fuelD : Nat)
      (Δ' : DeclEnv),
      DeclEnvLowers Δ Φ → CtxMapsEnv ctx Δ Φ →
      LeanNative.IR.RealLCNFSemantics.DeclEnv.lookup? Δ fn = some ((sd, ctxD, fuelD), Δ') →
      ctx.findLocalCallee? fn = some sym →
      ∃ (ld : LNIRDecl) (Φ' : FuncEnv),
        LeanNative.Semantics.FuncEnv.lookup? Φ sym = some ((ld, fuelD), Φ') ∧
        lowerRealLCNFDecl fuelD ctxD sd ld.name = .ok ld ∧
        DeclEnvLowers Δ' Φ' ∧ CtxMapsEnv ctxD Δ' Φ'
  | [], _, _, _, _, _, _, _, _, _, _, hlu, _ => nomatch hlu
  | _ :: _, [], _, _, _, _, _, _, _, hΔΦ, _, _, _ => nomatch hΔΦ
  | (sd0, ctxD0, fuelD0) :: Δ, (ld0, fuelL0) :: Φ, ctx, fn, sym, sd, ctxD, fuelD, Δ',
      hΔΦ, hmap, hlu, hloc => by
    obtain ⟨hfuel0, hlow0, _, hfresh0, hmapD0, htail⟩ := hΔΦ
    obtain ⟨hmapHead, hmapTail⟩ := hmap
    unfold LeanNative.IR.RealLCNFSemantics.DeclEnv.lookup? at hlu
    split at hlu
    · rename_i hbe
      injection hlu with hlu
      rcases Prod.mk.inj hlu with ⟨hp, rfl⟩
      rcases Prod.mk.inj hp with ⟨rfl, hp2⟩
      rcases Prod.mk.inj hp2 with ⟨rfl, rfl⟩
      have hsym : sym = ld0.name := hmapHead sym (by rw [eq_of_beq hbe]; exact hloc)
      subst hsym
      refine ⟨ld0, Φ, ?_, hlow0, htail, hmapD0⟩
      unfold LeanNative.Semantics.FuncEnv.lookup?
      simp only [beq_self_eq_true, ↓reduceIte, hfuel0]
    · rename_i hbe
      rcases declEnvLowers_lookup_align Δ Φ ctx fn sym sd ctxD fuelD Δ' htail hmapTail hlu hloc with
        ⟨ld, Φ', hluF, hlow, hΔ', hmap'⟩
      refine ⟨ld, Φ', ?_, hlow, hΔ', hmap'⟩
      unfold LeanNative.Semantics.FuncEnv.lookup?
      have hne : (ld0.name == sym) = false := by
        rcases funcEnv_lookup?_mem_name Φ sym (ld, fuelD) Φ' hluF with ⟨hmem, hname⟩
        exact beq_eq_false_iff_ne.mpr (fun h => hfresh0 (ld, fuelD) hmem (hname.trans h.symm))
      rw [hne]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact hluF

/-- `bindParams` is strict on arity: a success forces equal lengths (review item — the
    fact behind the arity side condition of `evalCodeF`'s call rule). -/
theorem bindParams_ok_length : ∀ (ctx : RealBridgeCtx) (tl : Bool) (env env' : LEnv)
    (ps : List (Lean.Compiler.LCNF.Param .impure)) (vs : List Val),
    bindParams ctx tl env ps vs = .ok env' → vs.length = ps.length
  | _, _, _, _, [], [], _ => rfl
  | _, _, _, _, [], _ :: _, h => nomatch h
  | _, _, _, _, _ :: _, [], h => nomatch h
  | ctx, tl, env, env', _ :: ps, _ :: vs, h => by
    unfold bindParams at h
    exact congrArg Nat.succ (bindParams_ok_length ctx tl _ env' ps vs h)

/-- `internRealParams` preserves the parameter count (review item, 3-line induction). -/
theorem internRealParams_length : ∀ (ctx : RealBridgeCtx) (st : RealBridgeState)
    (ps : List (Lean.Compiler.LCNF.Param .impure)),
    (internRealParams ctx st ps).1.length = ps.length
  | _, _, [] => rfl
  | ctx, st, p :: ps => by
    dsimp only [internRealParams]
    exact congrArg Nat.succ (internRealParams_length ctx _ ps)

/-- Parameter-count lemma (review item): a successful declaration lowering keeps the
    source arity — `lowerRealLCNFDecl` builds its parameter list with
    `internRealParams`, which conses exactly one `LNIRParam` per source parameter. The
    strict arity check of the lowered call rests on it. -/
theorem lowerRealLCNFDecl_params_length (fuel : Nat) (ctx : RealBridgeCtx)
    (decl : Lean.Compiler.LCNF.Decl .impure) (mangled : String) (d : LNIRDecl)
    (h : lowerRealLCNFDecl fuel ctx decl mangled = .ok d) :
    d.params.length = decl.params.size := by
  unfold lowerRealLCNFDecl at h
  cases hdv : decl.value with
  | extern _ => rw [hdv] at h; exact nomatch h
  | code c =>
    rw [hdv] at h
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases hlc : lowerRealLCNFCode fuel ctx (internRealParams ctx {} decl.params.toList).2 c with
    | error _ => rw [hlc] at h; exact nomatch h
    | ok plc =>
      rw [hlc] at h; injection h with hd
      subst d
      dsimp only
      rw [internRealParams_length]
      simp

/-- Argument alignment for a RESOLVED local call (the main new fact of the call case):
    `evalArg` errors on an erased/`type` argument, so a source-side `evalArgs` success
    forces every argument to be `.fvar`; on those `lowerCallArgsWithErasedPure` is
    `lowerRealArg` pointwise (state unchanged, no zero-binds), and the lowered argument
    variables read back exactly the source values under the invariant. In general the
    lowering preserves argument counts (each arm conses exactly one variable; an erased
    argument contributes a fresh zero-bound `.unit` variable), so the `zeroBinds = []`
    conclusion here covers exactly the reachable shape. -/
theorem lowerCallArgs_align (ctx : RealBridgeCtx) (st : RealBridgeState)
    (lenv : LEnv) (venv : VarEnv) (hinv : BridgeStateInv st lenv venv) :
    ∀ (args : List (Lean.Compiler.LCNF.Arg .impure)) (argVars : List VarId)
      (zeroBinds : List (VarId × LNIRType)) (st1 : RealBridgeState) (vals : List Val),
      lowerCallArgsWithErasedPure ctx st args = .ok (argVars, zeroBinds, st1) →
      evalArgs lenv.vals args = .ok vals →
      zeroBinds = [] ∧ st1 = st ∧ evalVarList venv argVars = .ok vals ∧
        vals.length = args.length
  | [], argVars, zeroBinds, st1, vals, hl, he => by
    dsimp only [lowerCallArgsWithErasedPure] at hl
    dsimp only [evalArgs] at he
    injection hl with hl
    injection he with he
    rcases Prod.mk.inj hl with ⟨rfl, hl2⟩
    rcases Prod.mk.inj hl2 with ⟨rfl, rfl⟩
    subst he
    exact ⟨rfl, rfl, rfl, rfl⟩
  | a :: rest, argVars, zeroBinds, st1, vals, hl, he => by
    cases a with
    | erased =>
      dsimp only [evalArgs, evalArg] at he
      exact nomatch he
    | type _ _ =>
      dsimp only [evalArgs, evalArg] at he
      exact nomatch he
    | fvar x =>
      dsimp only [lowerCallArgsWithErasedPure, Bind.bind, Except.bind, Pure.pure, Except.pure] at hl
      cases ha : lowerRealArg ctx st (.fvar x) true with
      | error _ => rw [ha] at hl; exact nomatch hl
      | ok pa =>
        rw [ha] at hl
        rcases pa with ⟨vid, stA⟩
        rcases lowerRealArg_sound ctx st lenv venv (.fvar x) true vid stA hinv ha with
          ⟨x', v, hxEq, _, hevalA, hvArg, _, hstA⟩
        injection hxEq with hx'
        subst hx'
        subst stA
        dsimp only at hl
        cases hr : lowerCallArgsWithErasedPure ctx st rest with
        | error _ => rw [hr] at hl; exact nomatch hl
        | ok pr =>
          rw [hr] at hl
          rcases pr with ⟨vs0, zs0, st2⟩
          dsimp only at hl
          injection hl with hl
          rcases Prod.mk.inj hl with ⟨rfl, hl2⟩
          rcases Prod.mk.inj hl2 with ⟨rfl, rfl⟩
          dsimp only [evalArgs] at he
          cases hA : evalArg lenv.vals (.fvar x) with
          | error _ => rw [hA] at he; exact nomatch he
          | ok v0 =>
            rw [hA] at he
            cases hR : evalArgs lenv.vals rest with
            | error _ => rw [hR] at he; exact nomatch he
            | ok vsR =>
              rw [hR] at he
              dsimp only at he
              injection he with he
              subst he
              have hv0 : v0 = v := by
                have hvv := hevalA.symm.trans hA
                injection hvv with hvv
                exact hvv.symm
              subst hv0
              rcases lowerCallArgs_align ctx st lenv venv hinv rest vs0 zs0 st2 vsR hr hR with
                ⟨rfl, rfl, hvlR, hlenR⟩
              refine ⟨rfl, rfl, ?_, ?_⟩
              · dsimp only [evalVarList]
                rw [hvArg, hvlR]
              · dsimp only [List.length]
                rw [hlenR]

/-- Mirror of `lowerRefOpPure_sound` (JpTag) at a fixed `Φ`: the produced code is the
    continuation itself or an `.incRef`/`.decRef` wrapper, none of which consults the
    environment, so the peel goes through the unfolding equation on `evalCodeF`'s
    clause-identical arms. -/
theorem lowerRefOpPure_soundF (Φ : FuncEnv) (fuel : Nat) (isInc : Bool) (vid : VarId) (vt : LNIRType)
    (n : Nat) (kCode code' : LNIRCode) (lenv : LEnv) (venv : VarEnv) (hst hst1 hst' : HeapState)
    (x : Lean.FVarId) (val v : Val)
    (hty : lenv.tys x = some vt) (hvalL : lenv.vals x = some val) (hvalV : venv vid = some val)
    (hrop : lowerRefOpPure isInc vid vt n kCode = .ok code')
    (hrc : applyRc isInc lenv hst x n = .ok hst1)
    (hk : evalCodeF Φ fuel venv hst1 kCode = .ok (v, hst')) :
    evalCodeF Φ fuel venv hst code' = .ok (v, hst') := by
  unfold lowerRefOpPure at hrop; unfold applyRc at hrc
  have hisHeap : lenv.isHeapVar x = isHeapPtrType vt := by dsimp only [LEnv.isHeapVar]; rw [hty]
  cases hunb : isUnboxedScalarOrTuple vt
  · rw [hunb] at hrop
    cases hhp : isHeapPtrType vt
    · rw [hhp] at hrop; exact nomatch hrop
    · rw [hhp] at hrop hisHeap
      rw [hisHeap] at hrc; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hvalL] at hrc
      cases isInc
      · injection hrop with hc; subst code'
        rw [evalCodeF.eq_def]
        simp only [Bool.false_eq_true, ↓reduceIte]
        unfold HeapState.evalDecRef
        rw [hvalV]
        cases val with
        | objPtr objId => simp only [Bool.false_eq_true, ↓reduceIte] at hrc ⊢; rw [hrc]; exact hk
        | sarrayId bufId => simp only [Bool.false_eq_true, ↓reduceIte] at hrc ⊢; rw [hrc]; exact hk
        | _ =>
          dsimp only at hrc ⊢; injection hrc with hs
          subst hst1; exact hk
      · injection hrop with hc; subst code'
        rw [evalCodeF.eq_def]
        simp only [↓reduceIte]
        unfold HeapState.evalIncRef
        rw [hvalV]
        cases val with
        | objPtr objId => simp only [↓reduceIte] at hrc ⊢; rw [hrc]; exact hk
        | sarrayId bufId => simp only [↓reduceIte] at hrc ⊢; rw [hrc]; exact hk
        | _ =>
          dsimp only at hrc ⊢; injection hrc with hs
          subst hst1; exact hk
  · rw [hunb] at hrop; injection hrop with hc; subst code'
    rw [hisHeap, unboxed_not_heap vt hunb] at hrc
    injection hrc with hs; subst hst1; exact hk

/-- The declaration-level statement derived from a given step-level statement at the
    SAME environment pair — the mirror of `lowerRealLCNFDecl_sound`'s proof, consumed
    both by the call case of the induction (at the aligned suffixes) and by the public
    `lowerRealLCNFDecl_soundF`. -/
private theorem declF_of_stepF (Δ : DeclEnv) (Φ : FuncEnv) (fuel : Nat) (ctx : RealBridgeCtx)
    (hstep : ∀ (st st' : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
      (target : Lean.Compiler.LCNF.Code .impure ⊕
        (VarId × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure)))
      (code : LNIRCode),
      BridgeStateInv st lenv venv →
      lowerImpureStepPure fuel ctx st target = .ok (code, st') →
      (match target with
       | .inl c => evalStepF Δ fuel ctx lenv hst (.inl c) = .ok (v, hst')
       | .inr (condVar, isBool, idx, discr?, alts) =>
         condVar < st.nextVarId ∧
         (∀ dx, discr? = some dx → (st.lookupFVar? dx).isSome = true) ∧
         (lnirTypeEq (st.getVarType condVar) .i1 = true → isBool = true) ∧
         ∃ cond, venv condVar = some cond ∧
           evalStepF Δ fuel ctx lenv hst (.inr (cond, isBool, idx, discr?, alts)) = .ok (v, hst')) →
      evalCodeF Φ fuel venv hst code = .ok (v, hst'))
    (decl : Lean.Compiler.LCNF.Decl .impure) (args : List Val) (hst hst' : HeapState)
    (v : Val) (d : LNIRDecl) (mangled : String)
    (h_lower : lowerRealLCNFDecl fuel ctx decl mangled = .ok d)
    (h_eval : evalRealLCNFDeclF Δ fuel ctx decl args hst = .ok (v, hst')) :
    evalCodeF Φ fuel
      ((d.params.zip args).foldl (fun acc (p, val) => acc.bind p.id val) VarEnv.empty)
      hst d.body = .ok (v, hst') := by
  unfold lowerRealLCNFDecl at h_lower
  unfold evalRealLCNFDeclF at h_eval
  cases hdv : decl.value with
  | extern _ => rw [hdv] at h_eval; exact nomatch h_eval
  | code c =>
    rw [hdv] at h_lower h_eval
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower h_eval
    cases hbp : bindParams ctx true LEnv.empty decl.params.toList args with
    | error _ => rw [hbp] at h_eval; exact nomatch h_eval
    | ok lenv =>
      rw [hbp] at h_eval
      have h_eval' : evalStepF Δ fuel ctx lenv hst (.inl c) = .ok (v, hst') := h_eval
      cases hlc : lowerRealLCNFCode fuel ctx (internRealParams ctx {} decl.params.toList).2 c with
      | error _ => rw [hlc] at h_lower; exact nomatch h_lower
      | ok plc =>
        rw [hlc] at h_lower; injection h_lower with hd
        subst d; dsimp only
        exact hstep (internRealParams ctx {} decl.params.toList).2 plc.2 lenv _
          hst hst' v (.inl c) plc.1
          (internRealParams_sound ctx decl.params.toList args {} LEnv.empty lenv VarEnv.empty
            bridgeInv_empty hbp)
          hlc h_eval'

set_option maxHeartbeats 1600000 in
/-- The environment-length induction: the step-level statement for every pair
    `(Δ, Φ)` shorter than `n`, with the fuel induction mirroring L1 inside. -/
private theorem lowerImpureStepPure_soundF_aux :
    ∀ (n : Nat) (Δ : DeclEnv) (Φ : FuncEnv), Δ.length < n →
    DeclEnvLowers Δ Φ → ∀ (ctx : RealBridgeCtx), CtxMapsEnv ctx Δ Φ → ∀ (fuel : Nat),
    ∀ (st st' : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
      (target : Lean.Compiler.LCNF.Code .impure ⊕
        (VarId × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure)))
      (code : LNIRCode),
      BridgeStateInv st lenv venv →
      lowerImpureStepPure fuel ctx st target = .ok (code, st') →
      (match target with
       | .inl c => evalStepF Δ fuel ctx lenv hst (.inl c) = .ok (v, hst')
       | .inr (condVar, isBool, idx, discr?, alts) =>
         condVar < st.nextVarId ∧
         (∀ dx, discr? = some dx → (st.lookupFVar? dx).isSome = true) ∧
         (lnirTypeEq (st.getVarType condVar) .i1 = true → isBool = true) ∧
         ∃ cond, venv condVar = some cond ∧
           evalStepF Δ fuel ctx lenv hst (.inr (cond, isBool, idx, discr?, alts)) = .ok (v, hst')) →
      evalCodeF Φ fuel venv hst code = .ok (v, hst') := by
  intro n
  induction n with
  | zero => intro Δ Φ hlen; exact absurd hlen (Nat.not_lt_zero _)
  | succ n ihn =>
    intro Δ Φ hlen hΔΦ ctx hmap
    have hres : ∀ p ∈ Φ, reservedRuntimeName p.1.name = false := declEnvLowers_reserved Δ Φ hΔΦ
    intro fuel
    induction fuel with
    | zero => intro st st' lenv venv hst hst' v target code _ h _; exact nomatch h
    | succ fuel ihf =>
      intro st st' lenv venv hst hst' v target code hinv h_lower h_side
      cases target with
      | inr t =>
        rcases t with ⟨condVar, isBool, idx, discr?, alts⟩
        rcases h_side with ⟨hcondLt, hdiscr, hi1, cond, hcondV, h_eval⟩
        exact lowerStepInr_soundF Δ Φ fuel ctx ihf st st' lenv venv hst hst' v
          condVar isBool idx discr? alts code cond hinv h_lower hcondLt hdiscr hi1 hcondV h_eval
      | inl c =>
        have h_eval : evalStepF Δ (fuel + 1) ctx lenv hst (.inl c) = .ok (v, hst') := h_side
        cases c with
        | «let» decl k =>
          refine lowerLetStep_soundF Δ Φ hres fuel ctx ihf st st' lenv venv hst hst' v decl k code hinv
            ?_ h_lower h_eval
          -- The resolved-local-call obligation: the one arm L1's semantics errors on.
          intro fvarId binderName declTy fnName argsA himp sym hloc h_lower' h_eval'
          rw [evalStepF.eq_def] at h_eval'
          simp only at h_eval'
          split at h_eval'
          · rename_i sd ctxD fuelD Δ' argsE hc
            -- Decompose the source call-target hit: a `lookup?` hit plus the caller-map gate.
            simp only [LeanNative.IR.RealLCNFSemantics.DeclEnv.callTarget?] at hc
            cases hl : LeanNative.IR.RealLCNFSemantics.DeclEnv.lookup? Δ fnName with
            | none => rw [hl] at hc; exact nomatch hc
            | some pΔ =>
              rcases pΔ with ⟨⟨sd0, ctxD0, fuelD0⟩, Δ0⟩
              rw [hl] at hc
              simp only at hc
              rw [hloc] at hc
              simp only [Option.isSome_some, ↓reduceIte] at hc
              injection hc with hc
              rcases Prod.mk.inj hc with ⟨hp, hc2⟩
              rcases Prod.mk.inj hp with ⟨rfl, hp2⟩
              rcases Prod.mk.inj hp2 with ⟨rfl, rfl⟩
              rcases Prod.mk.inj hc2 with ⟨rfl, rfl⟩
              -- Source side: arguments, parameter binding, the callee body, the continuation.
              cases hargsE : evalArgs lenv.vals argsA.toList with
              | error _ => rw [hargsE] at h_eval'; exact nomatch h_eval'
              | ok vals =>
                rw [hargsE] at h_eval'
                dsimp only at h_eval'
                -- Lowering side: argument lowering, fresh destination, continuation.
                dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower'
                cases hargsL : lowerCallArgsWithErasedPure ctx st argsA.toList with
                | error _ => rw [hargsL] at h_lower'; exact nomatch h_lower'
                | ok pargs =>
                  rw [hargsL] at h_lower'
                  rcases pargs with ⟨argVars, zeroBinds, st1⟩
                  dsimp only at h_lower'
                  cases hk : lowerImpureStepPure fuel ctx
                      (st1.allocFreshFVar fvarId (lowerGroundImpureTypeWith ctx declTy)).2 (.inl k) with
                  | error _ => rw [hk] at h_lower'; exact nomatch h_lower'
                  | ok pk =>
                    rw [hk] at h_lower'
                    injection h_lower' with hp'
                    rcases Prod.mk.inj hp' with ⟨hcodeEq, _⟩
                    rcases lowerCallArgs_align ctx st lenv venv hinv argsA.toList argVars zeroBinds st1
                        vals hargsL hargsE with ⟨rfl, rfl, hvl, _⟩
                    -- Align the two lookups and collect the entry facts.
                    rcases declEnvLowers_lookup_align Δ Φ ctx fnName sym sd0 ctxD0 fuelD0 Δ0
                        hΔΦ hmap hl hloc with ⟨ld, Φ', hluF, hlowD, hΔ'Φ', hmapD'⟩
                    -- Continue the source side through the callee.
                    cases hbp : bindParams ctxD0 true LEnv.empty sd0.params.toList vals with
                    | error _ => rw [hbp] at h_eval'; exact nomatch h_eval'
                    | ok envCallee =>
                      rw [hbp] at h_eval'
                      cases hsv : sd0.value with
                      | extern _ => rw [hsv] at h_eval'; exact nomatch h_eval'
                      | code cBody =>
                        rw [hsv] at h_eval'
                        dsimp only at h_eval'
                        cases hcallee : evalStepF Δ0 fuelD0 ctxD0 envCallee hst (.inl cBody) with
                        | error _ => rw [hcallee] at h_eval'; exact nomatch h_eval'
                        | ok pr1 =>
                          rw [hcallee] at h_eval'
                          rcases pr1 with ⟨v1, hstMid⟩
                          dsimp only at h_eval'
                          -- The arity check of the lowered call succeeds.
                          have hlenOk : vals.length = ld.params.length := by
                            rw [bindParams_ok_length ctxD0 true LEnv.empty envCallee sd0.params.toList vals hbp,
                              lowerRealLCNFDecl_params_length fuelD0 ctxD0 sd0 ld.name ld hlowD]
                            simp
                          -- The callee: the declaration-level statement at the aligned
                          -- suffixes, from the OUTER induction hypothesis.
                          have hΔ0len : Δ0.length < n :=
                            Nat.lt_of_lt_of_le
                              (LeanNative.IR.RealLCNFSemantics.DeclEnv.lookup?_length Δ fnName _ Δ0 hl)
                              (Nat.lt_succ_iff.mp hlen)
                          have hdeclEval : evalRealLCNFDeclF Δ0 fuelD0 ctxD0 sd0 vals hst = .ok (v1, hstMid) := by
                            unfold evalRealLCNFDeclF
                            rw [hsv]
                            dsimp only
                            rw [hbp]
                            exact hcallee
                          have hdecl := declF_of_stepF Δ0 Φ' fuelD0 ctxD0
                            (ihn Δ0 Φ' hΔ0len hΔ'Φ' ctxD0 hmapD' fuelD0)
                            sd0 vals hst hstMid v1 ld ld.name hlowD hdeclEval
                          -- Assemble the lowered run.
                          rw [← hcodeEq]
                          dsimp only [wrapZeroScalarSlotsPure]
                          rw [evalCodeF_letBind]
                          have hct : LeanNative.Semantics.FuncEnv.callTarget? Φ
                              (.call sym argVars (lowerGroundImpureTypeWith ctx declTy) false) =
                              some ((ld, fuelD0), Φ', argVars) := by
                            simp only [LeanNative.Semantics.FuncEnv.callTarget?]
                            rw [hluF]
                            rfl
                          rw [hct]
                          dsimp only
                          rw [hvl]
                          dsimp only
                          rw [if_pos hlenOk]
                          rw [hdecl]
                          dsimp only
                          -- The continuation under the fresh destination binding.
                          have hinv2 : BridgeStateInv
                              (st1.allocFreshFVar fvarId (lowerGroundImpureTypeWith ctx declTy)).2
                              (lenv.bind fvarId v1 none (some (lowerGroundImpureTypeWith ctx declTy)))
                              (venv.bind st1.nextVarId v1) :=
                            bridgeInv_bind_fresh st1 lenv venv fvarId
                              (lowerGroundImpureTypeWith ctx declTy) v1 hinv
                          exact evalCodeF_fuel_mono_step Φ fuel pk.1 _ hstMid v hst'
                            (ihf (st1.allocFreshFVar fvarId (lowerGroundImpureTypeWith ctx declTy)).2 pk.2
                              (lenv.bind fvarId v1 none (some (lowerGroundImpureTypeWith ctx declTy)))
                              (venv.bind st1.nextVarId v1) hstMid hst' v (.inl k) pk.1 hinv2 hk h_eval')
          · rename_i hc
            -- The caller's map knows `fn` but `Δ` misses: the deliberate old error.
            have hlv : evalLetValue ctx lenv hst (.fap fnName argsA himp)
                (lowerGroundImpureTypeWith ctx declTy) = .error (.unsupportedCall fnName.toString) := by
              dsimp only [evalLetValue]
              rw [hloc]
              simp only [Option.isSome_some, ↓reduceIte]
            rw [hlv] at h_eval'
            exact nomatch h_eval'
        | setTag x cidx k himp =>
          exact lowerSetTag_soundF Δ Φ hres fuel ctx ihf st st' lenv venv hst hst' v x cidx k himp
            code hinv h_lower h_eval
        | «return» x =>
          dsimp only [lowerImpureStepPure] at h_lower
          rw [evalStepF.eq_def] at h_eval
          simp only at h_eval
          dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
          cases hv : st.lookupBoundFVar x <;> rw [hv] at h_lower
          · exact nomatch h_lower
          · rename_i vid; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
            rcases lookupBoundFVar_inv st lenv venv x vid hinv hv with ⟨_, _, ⟨val, hvalL, hvalV⟩, _, _⟩
            rw [hvalL] at h_eval; injection h_eval with hpv; rcases Prod.mk.inj hpv with ⟨rfl, rfl⟩
            rw [evalCodeF.eq_def]
            simp only
            rw [hvalV]
        | unreach _ =>
          rw [evalStepF.eq_def] at h_eval
          simp only at h_eval
          exact nomatch h_eval
        | «fun» _ _ _ =>
          rw [evalStepF.eq_def] at h_eval
          simp only at h_eval
          exact nomatch h_eval
        | inc x n' _ _ k _ =>
          dsimp only [lowerImpureStepPure] at h_lower
          rw [evalStepF.eq_def] at h_eval
          simp only at h_eval
          dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
          cases hv : st.lookupBoundFVar x <;> rw [hv] at h_lower
          · exact nomatch h_lower
          · rename_i vid; dsimp only at h_lower
            rcases lookupBoundFVar_inv st lenv venv x vid hinv hv with ⟨_, _, ⟨val, hvalL, hvalV⟩, htyL, _⟩
            cases hrc : applyRc true lenv hst x n' with
            | error _ => rw [hrc] at h_eval; exact nomatch h_eval
            | ok hst1 =>
              rw [hrc] at h_eval
              cases hk : lowerImpureStepPure fuel ctx st (.inl k) with
              | error _ => rw [hk] at h_lower; exact nomatch h_lower
              | ok pk =>
                rw [hk] at h_lower; dsimp only at h_lower
                cases hrop : lowerRefOpPure true vid (st.getVarType vid) n' pk.1 <;> rw [hrop] at h_lower
                · exact nomatch h_lower
                · injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                  exact lowerRefOpPure_soundF Φ (fuel + 1) true vid (st.getVarType vid) n' pk.1 _
                    lenv venv hst hst1 hst' x val v htyL hvalL hvalV hrop hrc
                    (evalCodeF_fuel_mono_step Φ fuel pk.1 venv hst1 v hst'
                      (ihf st pk.2 lenv venv hst1 hst' v (.inl k) pk.1 hinv hk h_eval))
        | dec x n' _ _ _ k _ =>
          dsimp only [lowerImpureStepPure] at h_lower
          rw [evalStepF.eq_def] at h_eval
          simp only at h_eval
          dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
          cases hv : st.lookupBoundFVar x <;> rw [hv] at h_lower
          · exact nomatch h_lower
          · rename_i vid; dsimp only at h_lower
            rcases lookupBoundFVar_inv st lenv venv x vid hinv hv with ⟨_, _, ⟨val, hvalL, hvalV⟩, htyL, _⟩
            cases hrc : applyRc false lenv hst x n' with
            | error _ => rw [hrc] at h_eval; exact nomatch h_eval
            | ok hst1 =>
              rw [hrc] at h_eval
              cases hk : lowerImpureStepPure fuel ctx st (.inl k) with
              | error _ => rw [hk] at h_lower; exact nomatch h_lower
              | ok pk =>
                rw [hk] at h_lower; dsimp only at h_lower
                cases hrop : lowerRefOpPure false vid (st.getVarType vid) n' pk.1 <;> rw [hrop] at h_lower
                · exact nomatch h_lower
                · injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                  exact lowerRefOpPure_soundF Φ (fuel + 1) false vid (st.getVarType vid) n' pk.1 _
                    lenv venv hst hst1 hst' x val v htyL hvalL hvalV hrop hrc
                    (evalCodeF_fuel_mono_step Φ fuel pk.1 venv hst1 v hst'
                      (ihf st pk.2 lenv venv hst1 hst' v (.inl k) pk.1 hinv hk h_eval))
        | del x k _ =>
          dsimp only [lowerImpureStepPure] at h_lower
          rw [evalStepF.eq_def] at h_eval
          simp only at h_eval
          dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
          cases hv : st.lookupBoundFVar x <;> rw [hv] at h_lower
          · exact nomatch h_lower
          · rename_i objVid; dsimp only at h_lower
            rcases lookupBoundFVar_inv st lenv venv x objVid hinv hv with ⟨_, _, ⟨val, hvalL, hvalV⟩, htyL, _⟩
            have hisHeap : lenv.isHeapVar x = isHeapPtrType (st.getVarType objVid) := by
              dsimp only [LEnv.isHeapVar]; rw [htyL]
            rw [hvalL, hisHeap] at h_eval
            cases hhp : (ctx.allowStage1DHeap && isHeapPtrType (st.getVarType objVid)) <;>
              simp only [hhp, ↓reduceIte, Bool.false_eq_true] at h_lower h_eval
            · cases hk : lowerImpureStepPure fuel ctx st (.inl k) with
              | error _ => rw [hk] at h_lower; exact nomatch h_lower
              | ok pk =>
                rw [hk] at h_lower; dsimp only at h_lower
                cases hrop : lowerRefOpPure false objVid (st.getVarType objVid) 1 pk.1 <;> rw [hrop] at h_lower
                · exact nomatch h_lower
                · injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                  have hrcEq : ∃ hst1, applyRc false lenv hst x 1 = .ok hst1 ∧
                      evalStepF Δ fuel ctx lenv hst1 (.inl k) = .ok (v, hst') := by
                    unfold applyRc; rw [hisHeap, hvalL]
                    cases hih : isHeapPtrType (st.getVarType objVid) <;>
                      simp only [hih, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] at h_eval ⊢
                    · cases val <;> exact ⟨hst, rfl, h_eval⟩
                    · cases val with
                      | objPtr objId =>
                        dsimp only at h_eval ⊢
                        cases hd : hst.decRefObj objId 1 with
                        | error _ => rw [hd] at h_eval; exact nomatch h_eval
                        | ok hst1 => rw [hd] at h_eval; exact ⟨hst1, rfl, h_eval⟩
                      | sarrayId bufId =>
                        dsimp only at h_eval ⊢
                        cases hd : hst.decRefBuf bufId 1 with
                        | error _ => rw [hd] at h_eval; exact nomatch h_eval
                        | ok hst1 => rw [hd] at h_eval; exact ⟨hst1, rfl, h_eval⟩
                      | _ => exact ⟨hst, rfl, h_eval⟩
                  rcases hrcEq with ⟨hst1, hrc, h_eval1⟩
                  exact lowerRefOpPure_soundF Φ (fuel + 1) false objVid (st.getVarType objVid) 1 pk.1 _
                    lenv venv hst hst1 hst' x val v htyL hvalL hvalV hrop hrc
                    (evalCodeF_fuel_mono_step Φ fuel pk.1 venv hst1 v hst'
                      (ihf st pk.2 lenv venv hst1 hst' v (.inl k) pk.1 hinv hk h_eval1))
            · cases val with
              | objPtr objId =>
                dsimp only at h_eval
                cases hdel : hst.delObjShell objId with
                | error _ => rw [hdel] at h_eval; exact nomatch h_eval
                | ok hst1 =>
                  rw [hdel] at h_eval
                  cases hk : lowerImpureStepPure fuel ctx (st.freshVar .unit).2 (.inl k) with
                  | error _ => rw [hk] at h_lower; exact nomatch h_lower
                  | ok pk =>
                    rw [hk] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                    have hinv2 := bridgeInv_freshVar st lenv venv .unit .unit hinv
                    have hkEval := evalCodeF_fuel_mono_step Φ fuel pk.1 _ hst1 v hst'
                      (ihf (st.freshVar .unit).2 pk.2 lenv _ hst1 hst' v (.inl k) pk.1 hinv2 hk h_eval)
                    have hcall : evalExpr venv hst (.call "lean_native_del_obj" [objVid] .unit false) =
                        .ok (.unit, hst1) := by
                      unfold evalExpr; dsimp only [evalVarList]
                      rw [hvalV]; dsimp only [↓reduceIte, Bool.false_eq_true]
                      rw [hdel]; rfl
                    rw [evalCodeF_letBind_evalExpr
                      (FuncEnv.callTarget?_reserved (fn := "lean_native_del_obj")
                        (by first | rfl | decide | simp [reservedRuntimeName]) hres
                        [objVid] .unit false)]
                    rw [hcall]
                    exact hkEval
              | _ => exact nomatch h_eval
        | oset x idx y k _ =>
          dsimp only [lowerImpureStepPure] at h_lower
          rw [evalStepF.eq_def] at h_eval
          simp only at h_eval
          dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw,
            MonadExceptOf.throw, throwThe] at h_lower
          cases hv : st.lookupBoundFVar x <;> rw [hv] at h_lower
          · exact nomatch h_lower
          · rename_i objVid; dsimp only at h_lower
            rcases lookupBoundFVar_inv st lenv venv x objVid hinv hv with ⟨_, hobjLt, ⟨val, hvalL, hvalV⟩, htyL, _⟩
            have hisHeap : lenv.isHeapVar x = isHeapPtrType (st.getVarType objVid) := by
              dsimp only [LEnv.isHeapVar]; rw [htyL]
            cases hhp : (ctx.allowStage1DHeap && isHeapPtrType (st.getVarType objVid)) <;>
              simp only [hhp, ↓reduceIte, Bool.false_eq_true] at h_lower
            · cases hunb : isUnboxedScalarOrTuple (st.getVarType objVid) <;>
                simp only [hunb, ↓reduceIte, Bool.false_eq_true] at h_lower
              · exact nomatch h_lower
              · rw [hisHeap, unboxed_not_heap _ hunb] at h_eval
                simp only [Bool.not_false, ↓reduceIte] at h_eval
                exact evalCodeF_fuel_mono_step Φ fuel code venv hst v hst'
                  (ihf st st' lenv venv hst hst' v (.inl k) code hinv h_lower h_eval)
            · have hhp2 : isHeapPtrType (st.getVarType objVid) = true := (Bool.and_eq_true _ _).mp hhp |>.2
              rw [hisHeap, hhp2, hvalL] at h_eval
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h_eval
              cases hy : lowerRealArg ctx st y true with
              | error _ => rw [hy] at h_lower; exact nomatch h_lower
              | ok py =>
                rw [hy] at h_lower; rcases py with ⟨valVid, stY⟩
                rcases lowerRealArg_sound ctx st lenv venv y true valVid stY hinv hy with
                  ⟨yx, yVal, rfl, hluY, hevalY, hyValV, _, hstY⟩
                subst stY; dsimp only at h_lower
                have hvalLt : valVid < st.nextVarId := hinv.fvar_lt yx valVid hluY
                cases val with
                | objPtr objId =>
                  dsimp only at h_eval; rw [hevalY] at h_eval; dsimp only at h_eval
                  cases hwf : writeField hst objId (idx.toUInt64).toNat yVal true with
                  | error _ => rw [hwf] at h_eval; exact nomatch h_eval
                  | ok hst1 =>
                    rw [hwf] at h_eval
                    cases hk : lowerImpureStepPure fuel ctx ((st.freshVar .i64).2.freshVar .unit).2 (.inl k) with
                    | error _ => rw [hk] at h_lower; exact nomatch h_lower
                    | ok pk =>
                      rw [hk] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                      have hinv4 : BridgeStateInv ((st.freshVar .i64).2.freshVar .unit).2 lenv
                          ((venv.bind (st.freshVar .i64).1 (.u64 idx.toUInt64)).bind
                            ((st.freshVar .i64).2.freshVar .unit).1 .unit) :=
                        bridgeInv_freshVar (st.freshVar .i64).2 lenv
                          (venv.bind (st.freshVar .i64).1 (.u64 idx.toUInt64)) .unit .unit
                          (bridgeInv_freshVar st lenv venv .i64 (.u64 idx.toUInt64) hinv)
                      have hkEval := evalCodeF_fuel_mono_step Φ fuel pk.1 _ hst1 v hst'
                        (ihf ((st.freshVar .i64).2.freshVar .unit).2 pk.2 lenv _ hst1 hst' v
                          (.inl k) pk.1 hinv4 hk h_eval)
                      exact evalCtorWriteStep_soundF Φ hres fuel st venv hst hst1 hst' v objVid valVid
                        objId idx yVal true pk.1 hobjLt hvalLt hvalV hyValV hwf hkEval
                | _ => rw [hevalY] at h_eval; exact nomatch h_eval
        | uset x i y k _ =>
          dsimp only [lowerImpureStepPure] at h_lower
          rw [evalStepF.eq_def] at h_eval
          simp only at h_eval
          dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw,
            MonadExceptOf.throw, throwThe] at h_lower
          cases hv : st.lookupBoundFVar x <;> rw [hv] at h_lower
          · exact nomatch h_lower
          · rename_i objVid; dsimp only at h_lower
            rcases lookupBoundFVar_inv st lenv venv x objVid hinv hv with ⟨_, hobjLt, ⟨val, hvalL, hvalV⟩, _, hctorL⟩
            have hresEq : lenv.resolveCtor? ctx x = st.resolveHeapCtor? ctx objVid x := by
              dsimp [LEnv.resolveCtor?, RealBridgeState.resolveHeapCtor?]; rw [hctorL]
            split at h_lower
            · exact nomatch h_lower
            · cases hc : st.resolveHeapCtor? ctx objVid x <;> rw [hc] at h_lower
              · exact nomatch h_lower
              · rename_i cname; dsimp only at h_lower
                cases hlay : ctx.findLayout? cname <;> rw [hlay] at h_lower
                · exact nomatch h_lower
                · rename_i spec; dsimp only at h_lower
                  cases hsl : spec.usizeSlot? i <;> rw [hsl] at h_lower
                  · exact nomatch h_lower
                  · rename_i slp; rcases slp with ⟨slot, slotTy⟩; dsimp only at h_lower
                    cases hy : st.lookupBoundFVar y <;> rw [hy] at h_lower
                    · exact nomatch h_lower
                    · rename_i valVid; dsimp only at h_lower
                      rcases lookupBoundFVar_inv st lenv venv y valVid hinv hy with
                        ⟨_, hvalLt, ⟨yVal, hyValL, hyValV⟩, _, _⟩
                      rw [hvalL, hyValL] at h_eval
                      cases val with
                      | objPtr objId =>
                        have hslEq : (lenv.resolveCtor? ctx x >>= ctx.findLayout? >>= (·.usizeSlot? i)) =
                            some (slot, slotTy) := by
                          rw [hresEq, hc]; dsimp only [Bind.bind, Option.bind]
                          rw [hlay]; dsimp only; exact hsl
                        dsimp only at h_eval; rw [hslEq] at h_eval; dsimp only at h_eval
                        cases hwf : writeField hst objId (slot.toUInt64).toNat yVal false with
                        | error _ => rw [hwf] at h_eval; exact nomatch h_eval
                        | ok hst1 =>
                          rw [hwf] at h_eval
                          cases hk : lowerImpureStepPure fuel ctx ((st.freshVar .i64).2.freshVar .unit).2 (.inl k) with
                          | error _ => rw [hk] at h_lower; exact nomatch h_lower
                          | ok pk =>
                            rw [hk] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                            have hinv4 : BridgeStateInv ((st.freshVar .i64).2.freshVar .unit).2 lenv
                                ((venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64)).bind
                                  ((st.freshVar .i64).2.freshVar .unit).1 .unit) :=
                              bridgeInv_freshVar (st.freshVar .i64).2 lenv
                                (venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64)) .unit .unit
                                (bridgeInv_freshVar st lenv venv .i64 (.u64 slot.toUInt64) hinv)
                            have hkEval := evalCodeF_fuel_mono_step Φ fuel pk.1 _ hst1 v hst'
                              (ihf ((st.freshVar .i64).2.freshVar .unit).2 pk.2 lenv _ hst1 hst' v
                                (.inl k) pk.1 hinv4 hk h_eval)
                            exact evalCtorWriteStep_soundF Φ hres fuel st venv hst hst1 hst' v objVid valVid
                              objId slot yVal false pk.1 hobjLt hvalLt hvalV hyValV hwf hkEval
                      | _ => exact nomatch h_eval
        | sset x nn off y _ k _ =>
          dsimp only [lowerImpureStepPure] at h_lower
          rw [evalStepF.eq_def] at h_eval
          simp only at h_eval
          dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw,
            MonadExceptOf.throw, throwThe] at h_lower
          cases hv : st.lookupBoundFVar x <;> rw [hv] at h_lower
          · exact nomatch h_lower
          · rename_i objVid; dsimp only at h_lower
            rcases lookupBoundFVar_inv st lenv venv x objVid hinv hv with ⟨_, hobjLt, ⟨val, hvalL, hvalV⟩, _, hctorL⟩
            have hresEq : lenv.resolveCtor? ctx x = st.resolveHeapCtor? ctx objVid x := by
              dsimp [LEnv.resolveCtor?, RealBridgeState.resolveHeapCtor?]; rw [hctorL]
            split at h_lower
            · exact nomatch h_lower
            · cases hc : st.resolveHeapCtor? ctx objVid x <;> rw [hc] at h_lower
              · exact nomatch h_lower
              · rename_i cname; dsimp only at h_lower
                cases hlay : ctx.findLayout? cname <;> rw [hlay] at h_lower
                · exact nomatch h_lower
                · rename_i spec; dsimp only at h_lower
                  cases hsl : spec.scalarSlot? nn off <;> rw [hsl] at h_lower
                  · exact nomatch h_lower
                  · rename_i slp; rcases slp with ⟨slot, sfTy⟩; dsimp only at h_lower
                    cases hy : st.lookupBoundFVar y <;> rw [hy] at h_lower
                    · exact nomatch h_lower
                    · rename_i valVid; dsimp only at h_lower
                      rcases lookupBoundFVar_inv st lenv venv y valVid hinv hy with
                        ⟨_, hvalLt, ⟨yVal, hyValL, hyValV⟩, _, _⟩
                      rw [hvalL, hyValL] at h_eval
                      cases val with
                      | objPtr objId =>
                        have hslEq : (lenv.resolveCtor? ctx x >>= ctx.findLayout? >>= (·.scalarSlot? nn off)) =
                            some (slot, sfTy) := by
                          rw [hresEq, hc]; dsimp only [Bind.bind, Option.bind]
                          rw [hlay]; dsimp only; exact hsl
                        dsimp only at h_eval; rw [hslEq] at h_eval; dsimp only at h_eval
                        cases hwf : writeField hst objId (slot.toUInt64).toNat yVal false with
                        | error _ => rw [hwf] at h_eval; exact nomatch h_eval
                        | ok hst1 =>
                          rw [hwf] at h_eval
                          cases hk : lowerImpureStepPure fuel ctx ((st.freshVar .i64).2.freshVar .unit).2 (.inl k) with
                          | error _ => rw [hk] at h_lower; exact nomatch h_lower
                          | ok pk =>
                            rw [hk] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                            have hinv4 : BridgeStateInv ((st.freshVar .i64).2.freshVar .unit).2 lenv
                                ((venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64)).bind
                                  ((st.freshVar .i64).2.freshVar .unit).1 .unit) :=
                              bridgeInv_freshVar (st.freshVar .i64).2 lenv
                                (venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64)) .unit .unit
                                (bridgeInv_freshVar st lenv venv .i64 (.u64 slot.toUInt64) hinv)
                            have hkEval := evalCodeF_fuel_mono_step Φ fuel pk.1 _ hst1 v hst'
                              (ihf ((st.freshVar .i64).2.freshVar .unit).2 pk.2 lenv _ hst1 hst' v
                                (.inl k) pk.1 hinv4 hk h_eval)
                            exact evalCtorWriteStep_soundF Φ hres fuel st venv hst hst1 hst' v objVid valVid
                              objId slot yVal false pk.1 hobjLt hvalLt hvalV hyValV hwf hkEval
                      | _ => exact nomatch h_eval
        | cases cs =>
          dsimp only [lowerImpureStepPure] at h_lower
          rw [evalStepF.eq_def] at h_eval
          simp only at h_eval
          dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw,
            MonadExceptOf.throw, throwThe] at h_lower
          cases hv : st.lookupBoundFVar cs.discr <;> rw [hv] at h_lower
          · exact nomatch h_lower
          · rename_i condVar; dsimp only at h_lower
            rcases lookupBoundFVar_inv st lenv venv cs.discr condVar hinv hv with
              ⟨hluC, hcondLt, ⟨discrVal, hvalL, hvalV⟩, htyL, _⟩
            have hisHeap : lenv.isHeapVar cs.discr = isHeapPtrType (st.getVarType condVar) := by
              dsimp only [LEnv.isHeapVar]; rw [htyL]
            rw [hvalL, hisHeap] at h_eval; dsimp only at h_eval
            cases hhp : ((ctx.allowStage1DHeap || cs.typeName == ``Bool) && isHeapPtrType (st.getVarType condVar)) <;>
              simp only [hhp, ↓reduceIte, Bool.false_eq_true] at h_lower h_eval
            · cases hsc : (!isSupportedStage1BScalarType (st.getVarType condVar) ctx.arch) <;>
                simp only [hsc, ↓reduceIte, Bool.false_eq_true] at h_lower
              · rw [htyL] at h_eval; dsimp only [Option.getD] at h_eval
                have hsideSc : condVar < st.nextVarId ∧
                    (∀ dx, (none : Option Lean.FVarId) = some dx → (st.lookupFVar? dx).isSome = true) ∧
                    (lnirTypeEq (st.getVarType condVar) .i1 = true →
                      (cs.typeName == ``Bool || lnirTypeEq (st.getVarType condVar) .i1) = true) ∧
                    ∃ cond, venv condVar = some cond ∧
                      evalStepF Δ fuel ctx lenv hst
                        (.inr (cond, cs.typeName == ``Bool || lnirTypeEq (st.getVarType condVar) .i1, 0, none,
                          orderAltsPure cs.alts.toList)) = .ok (v, hst') := by
                  refine ⟨hcondLt, ?_, ?_, discrVal, hvalV, h_eval⟩
                  · intro _ h; cases h
                  · intro hi1; rw [hi1, Bool.or_true]
                exact evalCodeF_fuel_mono_step Φ fuel code venv hst v hst'
                  (ihf st st' lenv venv hst hst' v
                    (.inr (condVar, cs.typeName == ``Bool || lnirTypeEq (st.getVarType condVar) .i1, 0, none,
                      orderAltsPure cs.alts.toList))
                    code hinv h_lower hsideSc)
              · exact nomatch h_lower
            · cases htag : tagOf discrVal hst with
              | error _ => rw [htag] at h_eval; exact nomatch h_eval
              | ok tag =>
                rw [htag] at h_eval
                rcases freshVar_spec st .i64 with ⟨htagId, hfn2, hft2, hflu2, _, _⟩
                cases hk : lowerImpureStepPure fuel ctx (st.freshVar .i64).2
                    (.inr ((st.freshVar .i64).1, false, 0, some cs.discr, orderAltsPure cs.alts.toList)) with
                | error _ => rw [hk] at h_lower; exact nomatch h_lower
                | ok pk =>
                  rw [hk] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                  have hinv2 : BridgeStateInv (st.freshVar .i64).2 lenv (venv.bind (st.freshVar .i64).1 tag) :=
                    bridgeInv_freshVar st lenv venv .i64 tag hinv
                  have hsideHp : (st.freshVar .i64).1 < (st.freshVar .i64).2.nextVarId ∧
                      (∀ dx, some cs.discr = some dx → ((st.freshVar .i64).2.lookupFVar? dx).isSome = true) ∧
                      (lnirTypeEq ((st.freshVar .i64).2.getVarType (st.freshVar .i64).1) .i1 = true → false = true) ∧
                      ∃ cond, (venv.bind (st.freshVar .i64).1 tag) (st.freshVar .i64).1 = some cond ∧
                        evalStepF Δ fuel ctx lenv hst
                          (.inr (cond, false, 0, some cs.discr, orderAltsPure cs.alts.toList)) = .ok (v, hst') := by
                    refine ⟨?_, ?_, ?_, tag, VarEnv.bind_self _ _ _, h_eval⟩
                    · rw [htagId, hfn2]; exact Nat.lt_succ_self _
                    · intro dx hdx
                      injection hdx with hd; subst dx
                      rw [hflu2, hluC]; rfl
                    · intro hi1
                      simp only [htagId, hft2 st.nextVarId, beq_self_eq_true, ↓reduceIte,
                        lnirTypeEq, lnirTypeEqFuel] at hi1
                      exact hi1
                  have hkEval := evalCodeF_fuel_mono_step Φ fuel pk.1 (venv.bind (st.freshVar .i64).1 tag) hst v hst'
                    (ihf (st.freshVar .i64).2 pk.2 lenv (venv.bind (st.freshVar .i64).1 tag) hst hst' v
                      (.inr ((st.freshVar .i64).1, false, 0, some cs.discr, orderAltsPure cs.alts.toList))
                      pk.1 hinv2 hk hsideHp)
                  have hcall : evalExpr venv hst (.call "lean_native_ctor_tag" [condVar] .i64 false) =
                      .ok (tag, hst) := by
                    unfold evalExpr; dsimp only [evalVarList]
                    rw [hvalV]; dsimp only [↓reduceIte, Bool.false_eq_true]
                    unfold tagOf at htag
                    cases discrVal with
                    | objPtr objId =>
                      dsimp only [Functor.map, Except.map] at htag ⊢
                      cases hl : hst.liveHeapObj objId with
                      | error _ => rw [hl] at htag; exact nomatch htag
                      | ok o =>
                        rw [hl] at htag; injection htag with ht
                        subst tag; rfl
                    | u64 n' => injection htag with ht; subst tag; rfl
                    | bool b => injection htag with ht; subst tag; rfl
                    | tuple vs =>
                      cases vs with
                      | nil => exact nomatch htag
                      | cons v0 rest =>
                        cases v0 with
                        | u64 n' => injection htag with ht; subst tag; rfl
                        | _ => exact nomatch htag
                    | _ => exact nomatch htag
                  rw [evalCodeF_letBind_evalExpr
                    (FuncEnv.callTarget?_reserved (fn := "lean_native_ctor_tag")
                      (by first | rfl | decide | simp [reservedRuntimeName]) hres
                      [condVar] .i64 false)]
                  rw [hcall]
                  exact hkEval
        | jp decl k =>
          dsimp only [lowerImpureStepPure] at h_lower
          rw [evalStepF.eq_def] at h_eval
          simp only at h_eval
          cases hrec : hasJmpToPure fuel decl.fvarId (.inl decl.value) <;>
            simp only [hrec, ↓reduceIte, Bool.false_eq_true] at h_lower h_eval
          · exact evalCodeF_fuel_mono_step Φ fuel code venv hst v hst'
              (ihf (st.setJpDecl decl.fvarId decl.params.toList decl.value) st'
                (lenv.bindJp decl.fvarId { params := decl.params.toList, code := decl.value })
                venv hst hst' v (.inl k) code
                (bridgeInv_setJp st lenv venv decl.fvarId decl.params.toList decl.value hinv) h_lower h_eval)
          · exact nomatch h_lower
        | jmp fvarId args =>
          dsimp only [lowerImpureStepPure] at h_lower
          rw [evalStepF.eq_def] at h_eval
          simp only at h_eval
          dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw,
            MonadExceptOf.throw, throwThe] at h_lower
          cases hjp : st.lookupJp? fvarId <;> rw [hjp] at h_lower
          · exact nomatch h_lower
          · rename_i jpPair; rcases jpPair with ⟨jpParams, jpBody⟩; dsimp only at h_lower
            rw [hinv.jp_sync fvarId jpParams jpBody hjp] at h_eval; dsimp only at h_eval
            cases hb : bindJpCallArgsPure ctx st jpParams args.toList with
            | error _ => rw [hb] at h_lower; exact nomatch h_lower
            | ok pb =>
              rw [hb] at h_lower; rcases pb with ⟨binds, st1⟩; dsimp only at h_lower
              rcases bindJpCallArgsPure_relF Φ ctx venv st.nextVarId jpParams args.toList st st1 lenv binds
                  (Nat.le_refl _) (fun y vid hy => hinv.fvar_lt y vid hy) hinv hb with
                ⟨vs, hevalArgs, hfm1, hac1, hjp1, hnext1, hty1, hstepJp⟩
              rw [hevalArgs] at h_eval; dsimp only at h_eval
              have hinvSt1 : BridgeStateInv st1 lenv venv :=
                bridgeInv_ext st st1 lenv venv hinv hnext1 hty1 hfm1
                  (fun u _ => by simp only [RealBridgeState.getActiveCtor?, hac1]) hjp1
              have hst1Lt : ∀ x vid, st1.lookupFVar? x = some vid → vid < st.nextVarId := by
                intro x vid hx
                have hx' : st.lookupFVar? x = some vid := by
                  simp only [RealBridgeState.lookupFVar?, hfm1] at hx; exact hx
                exact hinv.fvar_lt x vid hx'
              rcases hstepJp st1 lenv venv st.nextVarId (fuel + 1) hst
                  (match lowerImpureStepPure fuel ctx (applyJpParamMapPure st1 binds) (.inl jpBody) with
                   | .ok (bc, _) => bc | .error _ => .unreachable)
                  hinvSt1 (Nat.le_refl _) (Nat.le_refl _) rfl hst1Lt (fun _ _ => rfl) with
                ⟨lenv', venv', hbindP, hinvIn, hevalWrap⟩
              rw [hbindP] at h_eval; dsimp only at h_eval
              cases hbody : lowerImpureStepPure fuel ctx (applyJpParamMapPure st1 binds) (.inl jpBody) with
              | error _ => rw [hbody] at h_lower; exact nomatch h_lower
              | ok pbody =>
                rw [hbody] at h_lower hevalWrap; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                rw [hevalWrap]
                exact evalCodeF_fuel_mono_step Φ fuel pbody.1 venv' hst v hst'
                  (ihf (applyJpParamMapPure st1 binds) pbody.2 lenv' venv' hst hst' v (.inl jpBody)
                    pbody.1 hinvIn hbody h_eval)

/-! ### The L2 headline theorems (the contract L3 builds against) -/

/-- Step-level forward simulation with both environments (the L2 workhorse; the
    contract's statement verbatim). With `Δ = []` and `Φ = []` the two environment
    hypotheses are trivial and `evalStepF_nil`/`evalCodeF_nil` collapse it to L1's
    `lowerImpureStepPure_sound`. -/
theorem lowerImpureStepPure_soundF (fuel : Nat) (ctx : RealBridgeCtx)
    (Δ : DeclEnv) (Φ : FuncEnv) (st st' : RealBridgeState)
    (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
    (target : Lean.Compiler.LCNF.Code .impure ⊕
      (VarId × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure)))
    (code : LNIRCode) :
    DeclEnvLowers Δ Φ →
    CtxMapsEnv ctx Δ Φ →
    BridgeStateInv st lenv venv →
    lowerImpureStepPure fuel ctx st target = .ok (code, st') →
    (match target with
      | .inl c => evalStepF Δ fuel ctx lenv hst (.inl c) = .ok (v, hst')
      | .inr (condVar, isBool, idx, discr?, alts) =>
        condVar < st.nextVarId ∧
        (∀ dx, discr? = some dx → (st.lookupFVar? dx).isSome = true) ∧
        (lnirTypeEq (st.getVarType condVar) .i1 = true → isBool = true) ∧
        ∃ cond, venv condVar = some cond ∧
          evalStepF Δ fuel ctx lenv hst (.inr (cond, isBool, idx, discr?, alts)) = .ok (v, hst')) →
    evalCodeF Φ fuel venv hst code = .ok (v, hst') :=
  fun hΔΦ hmap hinv h_lower h_side =>
    lowerImpureStepPure_soundF_aux (Δ.length + 1) Δ Φ (Nat.lt_succ_self _) hΔΦ ctx hmap fuel
      st st' lenv venv hst hst' v target code hinv h_lower h_side

/-- Code-level corollary (the contract's statement verbatim). -/
theorem lowerRealLCNFCode_soundF (fuel : Nat) (ctx : RealBridgeCtx)
    (Δ : DeclEnv) (Φ : FuncEnv) (st : RealBridgeState)
    (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
    (code : Lean.Compiler.LCNF.Code .impure) (lnir : LNIRCode) (st' : RealBridgeState)
    (h_env : DeclEnvLowers Δ Φ)
    (h_map : CtxMapsEnv ctx Δ Φ)
    (h_inv : BridgeStateInv st lenv venv)
    (h_lower : lowerRealLCNFCode fuel ctx st code = .ok (lnir, st'))
    (h_eval : evalRealLCNFCodeF Δ fuel ctx lenv hst code = .ok (v, hst')) :
    evalCodeF Φ fuel venv hst lnir = .ok (v, hst') :=
  lowerImpureStepPure_soundF fuel ctx Δ Φ st st' lenv venv hst hst' v (.inl code) lnir
    h_env h_map h_inv h_lower h_eval

/-- Declaration-level corollary — the L2 headline (the contract's statement verbatim).
    With `Δ = []` and `Φ = []`, `DeclEnvLowers [] []` and `CtxMapsEnv ctx [] []` hold
    trivially and `evalRealLCNFDeclF_nil` collapses it to L1's
    `lowerRealLCNFDecl_sound` shape, so it is the strict generalization the L1 contract
    names. -/
theorem lowerRealLCNFDecl_soundF (fuel : Nat) (ctx : RealBridgeCtx)
    (Δ : DeclEnv) (Φ : FuncEnv)
    (decl : Lean.Compiler.LCNF.Decl .impure) (args : List Val) (hst hst' : HeapState)
    (v : Val) (d : LNIRDecl) (mangled : String)
    (h_env : DeclEnvLowers Δ Φ)
    (h_map : CtxMapsEnv ctx Δ Φ)
    (h_lower : lowerRealLCNFDecl fuel ctx decl mangled = .ok d)
    (h_eval : evalRealLCNFDeclF Δ fuel ctx decl args hst = .ok (v, hst')) :
    evalCodeF Φ fuel
      ((d.params.zip args).foldl (fun acc (p, val) => acc.bind p.id val) VarEnv.empty)
      hst d.body = .ok (v, hst') :=
  declF_of_stepF Δ Φ fuel ctx
    (fun st st' lenv venv hst hst' v target code hinv h_lower h_side =>
      lowerImpureStepPure_soundF fuel ctx Δ Φ st st' lenv venv hst hst' v target code
        h_env h_map hinv h_lower h_side)
    decl args hst hst' v d mangled h_lower h_eval

end LeanNative.Proofs
