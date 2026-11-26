/-!
## L2 contract (roadmap/HORIZONS.md, H1 rung L2 "Calls") — w-l2

Authoritative row (`roadmap/HORIZONS.md`): "L2 Calls — Both semantics take a function
environment. Non-recursive calls between declarations are proved. | Without it the theorem
is empty for almost all real code." Leaf row: files `Semantics/Eval.lean`,
`Proofs/LowerCalls.lean`; needs L1, H1.F; accept "leaf `0 sorryAx`; matrix moves".

This is the contract-first statement of the exact signatures L2 proves in this leaf, in the
same form as the L1 contract (`RealLCNFBridgeProofs.lean:10-125`): a doc-block contract
rather than `sorry` skeletons, because the repo gates hold `0 sorryAx` on every commit.
The theorems land proved, verbatim, in the follow-up commits of this same leaf. The L3
lane (recursion and loops; fuel-indexed calls and the join-point/loop construct) builds
against these names and binder shapes.

Pipeline note: this leaf is cut against the L1 CONTRACT (fa715a8a); L1's proofs land in a
sibling lane. Nothing here edits L1's contract block, proves L1's theorems, or changes the
arity of any existing evaluator — the L1 contract's `evalCode fuel env hst body` and
`evalRealLCNFDecl fuel ctx decl args hst` shapes stay exactly as stated there, and the
function environments arrive as a conservative layer whose empty instance is the old
semantics by theorem (`evalCodeF_nil`, `evalStepF_nil`, `evalRealLCNFDeclF_nil` below).
H1.F's hash pin (`SpecLocked.lean`) is not in the tree at this tip; this leaf neither
creates nor edits it.

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

### New definitions

In `lean/LeanNative/Semantics/Eval.lean` (append-only — no existing line changes;
namespace `LeanNative.Semantics`):

```
abbrev FuncEnv := List LNIRDecl

/-- First declaration named `fn`, paired with the STRICT SUFFIX of the environment
    after it (the stratified tail the callee body runs under). -/
def FuncEnv.lookup? : FuncEnv → String → Option (LNIRDecl × FuncEnv)

def evalCodeF (Φ : FuncEnv) (fuel : Nat) : VarEnv → HeapState → LNIRCode →
    Except UBError (Val × HeapState)
```

`evalCodeF` mirrors `evalCode` clause for clause (same instruction semantics, same
`evalExpr`, same loop helpers, every recursive occurrence at the same `Φ`) with ONE new
rule: on `.letBind dst ty (.call fn args retTy false) k`, when
`FuncEnv.lookup? Φ fn = some (ld, Φ')`, the call evaluates as

```
match evalVarList env args with
| .ok vals =>
  match evalCodeF Φ' fuel
      ((ld.params.zip vals).foldl (fun acc (p, val) => acc.bind p.id val) VarEnv.empty)
      st ld.body with
  | .ok (v, st') => evalCodeF Φ fuel (env.bind dst v) st' k
  | .error err => .error err
| .error err => .error err
```

— the declaration-entry binding convention of `lowerRealLCNFDecl_sound`'s conclusion. The
callee body runs under the strict suffix `Φ'`, so the environment is stratified: chains of
non-recursive calls evaluate, while a self or backward call misses the lookup and falls to
the old `evalExpr` path (which errors `.unsupportedCall`). An extern call
(`isExtern = true`) or a lookup miss delegates to `evalExpr` exactly as `evalCode` does.
`fuel` passes to the callee unchanged (pass-through, as everywhere in `evalCode`);
fuel-indexed calls are L3's redesign. Termination is lexicographic on
`(Φ.length, code)`, with the strict-suffix length lemma for `FuncEnv.lookup?`.

In `lean/LeanNative/IR/RealLCNFCallSemantics.lean` (NEW file; namespace
`LeanNative.IR.RealLCNFSemantics`; imports `LeanNative.IR.RealLCNFSemantics` only, so the
H1.1 separation pin (`Tests/RealLCNFSeparationPin.lean`) is preserved. A new file rather
than an append because `scripts/lcnf_coverage_results.json` sha-pins
`IR/RealLCNFSemantics.lean`):

```
abbrev DeclEnv := List (Lean.Compiler.LCNF.Decl .impure)

/-- First declaration whose `.name` is `fn`, paired with the strict suffix after it. -/
def DeclEnv.lookup? : DeclEnv → Lean.Name → Option (Lean.Compiler.LCNF.Decl .impure × DeclEnv)

def evalStepF (Δ : DeclEnv) (fuel : Nat) (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
    (target : Lean.Compiler.LCNF.Code .impure ⊕
      (Val × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure))) :
    Except UBError (Val × HeapState)

def evalRealLCNFCodeF (Δ : DeclEnv) (fuel : Nat) (ctx : RealBridgeCtx) (env : LEnv)
    (st : HeapState) (code : Lean.Compiler.LCNF.Code .impure) :
    Except UBError (Val × HeapState)

def evalRealLCNFDeclF (Δ : DeclEnv) (fuel : Nat) (ctx : RealBridgeCtx)
    (decl : Lean.Compiler.LCNF.Decl .impure) (args : List Val)
    (st : HeapState := HeapState.empty) : Except UBError (Val × HeapState)
```

`evalStepF` mirrors `evalStep` clause for clause (same fuel recursion, same
`evalLetValue`, same `storedTy`/`storedCtor` machinery, same join-point and `cases`
handling, every recursive occurrence at the same `Δ`) with ONE new rule, replacing exactly
the arm the old semantics deliberately errors on: on `.let decl k` with
`decl.value = .fap fn args _` and `(ctx.findLocalCallee? fn).isSome`,

- `DeclEnv.lookup? Δ fn = some (sd, Δ')`: `evalArgs env.vals args.toList`, then
  `bindParams ctx true LEnv.empty sd.params.toList vals` (the declaration-entry convention
  of `evalRealLCNFDecl`); `sd.value` must be `.code c` (`.extern _` errors
  `.unsupportedCall`); the callee body runs as `evalStepF Δ' fuel ctx env' st (.inl c)` at
  the step's decremented fuel; its `.ok (v, st')` binds into the caller exactly as the old
  `.fap` arm would (`storedTy := if isUnboxedScalarOrTuple rawTy then rawTy else .i64`, no
  ctor) and continues with `k` under `Δ`.
- lookup miss: `.error (.unsupportedCall fn.toString)` — byte-for-byte the old behavior,
  so `Δ = []` is the old semantics (theorem `evalStepF_nil`).

`evalRealLCNFCodeF`/`evalRealLCNFDeclF` mirror `evalRealLCNFCode`/`evalRealLCNFDecl` over
`evalStepF`.

In this file, namespace `LeanNative.Proofs`:

```
/-- Reserved runtime symbols `evalExpr` interprets as intrinsics
    (`lean_native_*`, `lean_mark_mt`); a lowered local callee must not shadow them. -/
def reservedRuntimeName (s : String) : Bool

/-- Pointwise "Δ lowers to Φ": positionally, each source declaration lowers (with the
    driver's mangled-name map `ctx.localCallees`) to the corresponding LNIR declaration,
    mangled names are fresh (unreserved, no duplicates), and the tails relate. -/
inductive DeclEnvLowers (fuel : Nat) (ctx : RealBridgeCtx) : DeclEnv → FuncEnv → Prop
  | nil : DeclEnvLowers fuel ctx [] []
  | cons : ∀ {sd : Lean.Compiler.LCNF.Decl .impure} {ld : LNIRDecl} {Δ : DeclEnv} {Φ : FuncEnv},
      ctx.findLocalCallee? sd.name = some ld.name →
      lowerRealLCNFDecl fuel ctx sd ld.name = .ok ld →
      reservedRuntimeName ld.name = false →
      (∀ ld' ∈ Φ, ld'.name ≠ ld.name) →
      DeclEnvLowers fuel ctx Δ Φ →
      DeclEnvLowers fuel ctx (sd :: Δ) (ld :: Φ)

/-- `CodeRefines` with the function-environment binder (the L2 form of refinement). -/
def CodeRefinesF (Φ : FuncEnv) (src tgt : LNIRCode) : Prop :=
  ∀ fuel env st v st', evalCodeF Φ fuel env st src = .ok (v, st') →
    evalCodeF Φ fuel env st tgt = .ok (v, st')
```

### Theorems proved by this leaf (the L2 contract L3 builds against)

Conservativity — the old semantics is the empty-environment instance:

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

Step-level forward simulation with both environments (the L2 workhorse; extends
`lowerImpureStepPure_sound` with the two environment binders and the `DeclEnvLowers`
hypothesis — hypothesis shape otherwise verbatim from L1):

```
theorem lowerImpureStepPure_soundF (fuel : Nat) (ctx : RealBridgeCtx)
    (Δ : DeclEnv) (Φ : FuncEnv) (st st' : RealBridgeState)
    (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
    (target : Lean.Compiler.LCNF.Code .impure ⊕
      (VarId × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure)))
    (code : LNIRCode) :
    DeclEnvLowers fuel ctx Δ Φ →
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
`lowerRealLCNFDecl_sound` with the same two binders and hypothesis):

```
theorem lowerRealLCNFCode_soundF (fuel : Nat) (ctx : RealBridgeCtx)
    (Δ : DeclEnv) (Φ : FuncEnv) (st : RealBridgeState)
    (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
    (code : Lean.Compiler.LCNF.Code .impure) (lnir : LNIRCode) (st' : RealBridgeState)
    (h_env : DeclEnvLowers fuel ctx Δ Φ)
    (h_inv : BridgeStateInv st lenv venv)
    (h_lower : lowerRealLCNFCode fuel ctx st code = .ok (lnir, st'))
    (h_eval : evalRealLCNFCodeF Δ fuel ctx lenv hst code = .ok (v, hst')) :
    evalCodeF Φ fuel venv hst lnir = .ok (v, hst')

theorem lowerRealLCNFDecl_soundF (fuel : Nat) (ctx : RealBridgeCtx)
    (Δ : DeclEnv) (Φ : FuncEnv)
    (decl : Lean.Compiler.LCNF.Decl .impure) (args : List Val) (hst hst' : HeapState)
    (v : Val) (d : LNIRDecl) (mangled : String)
    (h_env : DeclEnvLowers fuel ctx Δ Φ)
    (h_lower : lowerRealLCNFDecl fuel ctx decl mangled = .ok d)
    (h_eval : evalRealLCNFDeclF Δ fuel ctx decl args hst = .ok (v, hst')) :
    evalCodeF Φ fuel
      ((d.params.zip args).foldl (fun acc (p, val) => acc.bind p.id val) VarEnv.empty)
      hst d.body = .ok (v, hst') :=
```

`lowerRealLCNFDecl_soundF` is the L2 headline: with `Δ = []`, `DeclEnvLowers fuel ctx [] []`
holds and `evalRealLCNFDeclF_nil` collapses it to L1's `lowerRealLCNFDecl_sound` shape, so
it is the strict one-extra-binder generalization the L1 contract names. Expected helper
lemmas landing with the proofs (shapes not frozen by this contract):
`FuncEnv.lookup?_length` / `DeclEnv.lookup?_length` (strict-suffix decrease),
`evalCodeF_fuel_mono_step` (mirror of `evalCode_fuel_mono_step`), `evalStepF_fuel_mono`
(with a `hasJmpToPure` antitonicity sublemma), and a lookup-alignment lemma for
`DeclEnvLowers` (the tail-freshness clause makes `FuncEnv.lookup?` and `DeclEnv.lookup?`
find corresponding positions and related suffixes).

### Stated for the fold; BLOCKED on a named contract mismatch (reported to the operator)

The L1 contract block says L2 "restates them with that one extra binder — the names below
stay", i.e. also environment-generalized forms of L1's two theorems over
`applyValidatedCompression` (an L1 definition that is not yet in this tree):

```
theorem applyValidatedCompression_refinesF (Φ : FuncEnv) (d : LNIRDecl) (cand : LNIRCode) :
    (applyValidatedCompression d cand).params = d.params ∧
    CodeRefinesF Φ d.body (applyValidatedCompression d cand).body

theorem lowerRealLCNFDecl_driver_soundF (fuel : Nat) (ctx : RealBridgeCtx)
    (Δ : DeclEnv) (Φ : FuncEnv)
    (decl : Lean.Compiler.LCNF.Decl .impure) (args : List Val) (hst hst' : HeapState)
    (v : Val) (d : LNIRDecl) (mangled : String) (cand : LNIRCode)
    (h_env : DeclEnvLowers fuel ctx Δ Φ)
    (h_lower : lowerRealLCNFDecl fuel ctx decl mangled = .ok d)
    (h_eval : evalRealLCNFDeclF Δ fuel ctx decl args hst = .ok (v, hst')) :
    evalCodeF Φ fuel
      (((applyValidatedCompression d cand).params.zip args).foldl
        (fun acc (p, val) => acc.bind p.id val) VarEnv.empty)
      hst (applyValidatedCompression d cand).body = .ok (v, hst')
```

These two are NOT promised by this leaf, for a reason at the bytes of the gate L1 builds
on: `runSymbolicValidatedDecl` accepts via `symbolicCodeRefines`, whose default `letBind`
arm compares non-scalar right-hand sides with `lnirExprEvalEq`
(`SymbolicTVRefinesDefs.lean:297-303`), and `lnirExprEvalEq` returns `true` on matching
`.call` pairs (`SymbolicTVRefinesDefs.lean:61-62`). So the checker can accept a
call-bearing `d.body`/`cand` pair, while its soundness (`symbolicValidatedDeclOpt_sound`)
yields only the env-free `CodeRefines`, which is vacuous past the first `Φ`-bound call
(env-free `evalCode` errors there). The generic transfer `CodeRefines src tgt →
CodeRefinesF Φ src tgt` is FALSE: `src = .letBind x ty (.call f [] ty false) (.ret x)`
with `f` bound in `Φ` has no env-free `.ok` run, so env-free `CodeRefines src tgt` holds
for EVERY `tgt`, while `CodeRefinesF Φ src tgt` fails for any `tgt` that disagrees with
the call's result. Proving the two theorems above therefore needs the symbolic-TV
refinement soundness stack re-proved against `evalCodeF` — not "one extra binder". The
candidate resolutions (the operator's / the L1 fold's call, not this leaf's): (a) an
F-soundness leaf for the symbolic-TV stack; (b) `applyValidatedCompression` additionally
requires a call-free `d.body` (an L1-owned definition change making both theorems provable
as stated); (c) the driver bypasses compression for call-bearing bodies. The statements
are recorded here so L3 sees the intended names; they land once the mismatch is resolved.

### Acceptance (quoted) and gates

- "leaf `0 sorryAx`": every theorem in the proved set above lands kernel-checked; the
  leaf's theorems are appended to `AxiomAudit.lean`'s `auditedTheoremNames` with the
  pinned count raised exactly (863 → 863 + the number of theorems added; the L1 lane
  raises the same pin for its two theorems, so the fold resolves both raises additively).
- "matrix moves": the semantics and proofs landed here are exactly what
  `scripts/lcnf_coverage.py`'s methodology names as the condition for reclassifying
  `lowered_vacuous_local_call` out of `lowered_unproved`. That script and its committed
  results are H1.0's files and this leaf's non-goals; the reclassification commit is the
  matrix owner's, once this leaf merges. Recorded as a handoff, not silently claimed.
- Gates: `(cd lean && lake build TurboLean LeanNative)`;
  `turbo-lean --json audit-spec lean/TurboLean/Spec.lean` (98/98) and
  `lean/LeanNative/Spec.lean` (124/124) — both files untouched by this leaf;
  `turbo-lean --json audit-spec --policy strict-proofs lean/LeanNative/Proofs/LowerCalls.lean`
  (ok; 0 vacuous, 0 trivial, 0 droppable hypotheses) — adding this file to
  `scripts/ci_verify.sh`'s strict-proofs loop is the CI owner's follow-up (CI edits are
  this leaf's non-goals); `python3 scripts/sync_docs_inventory.py --check`. Executable
  guards for the call semantics land in `lean/LeanNative/Tests/RealLCNFCallTests.lean`
  (new file): a two-declaration environment where the caller's result is wrong unless the
  callee body actually runs (kills call-as-noop mutants), a self-call that falls to the
  old `.unsupportedCall` behavior, and a `Δ = [] / Φ = []` run equal to the old evaluators.
-/
