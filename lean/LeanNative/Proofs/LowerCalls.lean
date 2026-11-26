import LeanNative.IR.RealLCNFBridge
import LeanNative.IR.RealLCNFCallSemantics
import LeanNative.Proofs.RealLCNFBridgeProofs

/-!
## L2 contract (roadmap/HORIZONS.md, H1 rung L2 "Calls") — w-l2

Authoritative row (`roadmap/HORIZONS.md`): "L2 Calls — Both semantics take a function
environment. Non-recursive calls between declarations are proved. | Without it the theorem
is empty for almost all real code." Leaf row: files `Semantics/Eval.lean`,
`Proofs/LowerCalls.lean`; needs L1, H1.F; accept "leaf `0 sorryAx`; matrix moves".

Contract-first statement, in the same form as the L1 contract
(`RealLCNFBridgeProofs.lean:10-125`). The contract commit of this leaf is 415256b1 (the
doc-only form of this block); review e89404a9 (F1, F4, F5) reshaped the environments to
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

### Per-declaration entries (review e89404a9 F1)

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
VarEnv.empty`, erroring on an argument-count mismatch. The environment is stratified, so
a call resolves only against strictly later entries; under the pairwise-fresh name
environments `DeclEnvLowers` admits, a self or backward call misses the lookup and keeps
the old `evalExpr` behavior. Termination is lexicographic on `(Φ.length, code)`.

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

In this file (namespace `LeanNative.Proofs`): `reservedRuntimeName`, `CtxMapsEnv`,
`DeclEnvLowers` and `CodeRefinesF` — definitions below.

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
is unreachable), so L1 fix round 1 REMOVES `applyValidatedCompression` entirely — the
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
source-side fuel monotonicity is needed. Expected helper lemmas landing with the proofs
(shapes not frozen by this contract): `FuncEnv.lookup?_length` / `DeclEnv.lookup?_length`
(strict-suffix decrease, landed with the evaluators), `evalCodeF_fuel_mono_step` (mirror
of `evalCode_fuel_mono_step`, same `Φ`), and a lookup-alignment lemma for
`DeclEnvLowers`/`CtxMapsEnv` (tail-freshness makes `FuncEnv.lookup?` and
`DeclEnv.lookup?` find corresponding positions with related suffixes). Where the restated
per-case lemmas are mechanical, they are parameterized over the call rule (L3's recorded
option (b)) so L3's fuel-indexed semantics can instantiate them; a case that resists
parameterization stays F-specific and is named in the leaf report.

### Acceptance (quoted) and gates

- "leaf `0 sorryAx`": every theorem in the proved set lands kernel-checked; the leaf's
  theorems are appended to `AxiomAudit.lean`'s `auditedTheoremNames` with the pinned
  count raised exactly.
- "matrix moves": the semantics and proofs landed here are exactly what
  `scripts/lcnf_coverage.py`'s methodology names as the condition for reclassifying
  `lowered_vacuous_local_call` out of `lowered_unproved`. That script and its committed
  results are H1.0's files; the reclassification handoff is lead-accepted and the commit
  is the matrix owner's, once this leaf merges.
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
  ambient fuel is ample (pinning the per-entry fuel); a self-call that falls to the old
  `.unsupportedCall` behavior; and `Δ = [] / Φ = []` runs equal to the old evaluators.
-/

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

/-- Reserved runtime symbols `evalExpr` interprets as intrinsics (`lean_native_*`,
    `lean_mark_mt`); a lowered local callee must not shadow them (clause of
    `DeclEnvLowers`), so the `Φ`-first lookup in `evalCodeF` never captures an intrinsic
    call the lowering emitted. -/
def reservedRuntimeName (s : String) : Bool :=
  s.startsWith "lean_native_" || s == "lean_mark_mt"

/-- The given (caller) context's mangled-name map agrees with the environment pairing:
    position by position it maps the source declaration's name to the lowered
    declaration's name. The top-level theorems take it for the top caller's context;
    `DeclEnvLowers` carries it per entry for that entry's OWN context, so nested call
    sites resolve against the same pairing. -/
def CtxMapsEnv (ctx : RealBridgeCtx) : DeclEnv → FuncEnv → Prop
  | [], [] => True
  | (sd, _, _) :: Δ, (ld, _) :: Φ =>
      ctx.findLocalCallee? sd.name = some ld.name ∧ CtxMapsEnv ctx Δ Φ
  | _, _ => False

/-- Pointwise "Δ lowers to Φ": positionally, each source declaration lowers UNDER ITS OWN
    context and fuel (review e89404a9 F1 — the driver builds per-declaration contexts) to
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

/-- `CodeRefines` with the function-environment binder (the L2 form of refinement). -/
def CodeRefinesF (Φ : FuncEnv) (src tgt : LNIRCode) : Prop :=
  ∀ fuel env st v st', evalCodeF Φ fuel env st src = .ok (v, st') →
    evalCodeF Φ fuel env st tgt = .ok (v, st')

theorem CodeRefinesF.refl (Φ : FuncEnv) (c : LNIRCode) : CodeRefinesF Φ c c :=
  fun _ _ _ _ _ h => h

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

end LeanNative.Proofs
