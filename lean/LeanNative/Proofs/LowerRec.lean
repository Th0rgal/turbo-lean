/-!
## L3 contract (roadmap/HORIZONS.md, H1 rung L3 "Recursion and loops") — w-l3

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

Pipeline note: this leaf is cut against the L2 CONTRACT (`Proofs/LowerCalls.lean`,
415256b1); L2's definitions (`FuncEnv`, `evalCodeF`, `DeclEnv`, `evalStepF`,
`evalRealLCNFDeclF`, `DeclEnvLowers`, `CodeRefinesF`, `reservedRuntimeName`) are not in
the tree at this tip — only their contract is. Nothing here edits L2's files
(`Semantics/Eval.lean` stays append-only for L2; `IR/RealLCNFCallSemantics.lean` and
`Tests/RealLCNFCallTests.lean` stay L2's to create), proves L2's theorems, or states
R-forms of anything outside L2's non-BLOCKED contracted set. The driver's compression
post-pass surface is being removed by the L1 fix round (a review proved it never changes
any declaration), so the driver-shaped soundness statement reduces to
`lowerRealLCNFDecl_sound` and this contract names no post-pass symbol; this worktree
merges `main` again once the L1 fix round and L2 land, before its final proofs commit.
The sha-pinned files (`scripts/lcnf_coverage_results.json` pins
`IR/RealLCNFSemantics.lean`, `IR/RealLCNFBridge.lean`, `IR/Bridge.lean`,
`IR/BridgeHelpers*.lean`, `Proofs/RealLCNFBridgeProofs.lean`) are read, cited and proved
ABOUT, never edited; every new definition goes in new files, as L2's layering prescribes.

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
- at fuel `fuel' + 1`: `evalVarList env args`, then the callee body
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
L2 contracts for its `IR/RealLCNFCallSemantics.lean`, which this file does not touch):

```
/-- First declaration whose `.name` is `fn`. The hit alone (no suffix). -/
def lookupDeclRec? : List (Lean.Compiler.LCNF.Decl .impure) → Lean.Name →
    Option (Lean.Compiler.LCNF.Decl .impure)

def evalStepR (Δ : List (Lean.Compiler.LCNF.Decl .impure)) (fuel : Nat)
    (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
    (target : Lean.Compiler.LCNF.Code .impure ⊕
      (Val × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure))) :
    Except UBError (Val × HeapState)

def evalRealLCNFCodeR (Δ : List (Lean.Compiler.LCNF.Decl .impure)) (fuel : Nat)
    (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
    (code : Lean.Compiler.LCNF.Code .impure) : Except UBError (Val × HeapState)

def evalRealLCNFDeclR (Δ : List (Lean.Compiler.LCNF.Decl .impure)) (fuel : Nat)
    (ctx : RealBridgeCtx) (decl : Lean.Compiler.LCNF.Decl .impure) (args : List Val)
    (st : HeapState := HeapState.empty) : Except UBError (Val × HeapState)
```

`evalStepR` mirrors `evalStep` clause for clause (same fuel-structural recursion with
`.error .fuelExhausted` at `0`, same `evalLetValue`, same `storedTy`/`storedCtor`
machinery, same join-point, `cases`, rc and mutation handling, every recursive occurrence
at the step's decremented fuel and the same `Δ`) with ONE new rule, replacing exactly the
arm the old semantics deliberately errors on: on `.let decl k` with
`decl.value = .fap fn args _` and `(ctx.findLocalCallee? fn).isSome`,

- `lookupDeclRec? Δ fn = some sd`: `evalArgs env.vals args.toList`; `sd.value` must be
  `.code c` (`.extern _` errors `.unsupportedCall fn.toString`); then
  `bindParams ctx true LEnv.empty sd.params.toList vals` (the declaration-entry convention
  of `evalRealLCNFDecl`); the callee body runs as `evalStepR Δ fuel ctx env' st (.inl c)`
  at the step's decremented fuel UNDER THE FULL `Δ` — the one difference from L2's rule,
  and what makes a self or mutual call evaluate; its `.ok (v, st')` binds into the caller
  exactly as the old `.fap` arm would (`storedTy := if isUnboxedScalarOrTuple rawTy then
  rawTy else .i64`, no ctor) and continues with `k` at the decremented fuel under `Δ`.
- lookup miss: `.error (.unsupportedCall fn.toString)` — byte-for-byte the old behavior,
  so `Δ = []` is the old semantics (theorem `evalStepR_nil`).

`evalRealLCNFCodeR`/`evalRealLCNFDeclR` mirror `evalRealLCNFCode`/`evalRealLCNFDecl` over
`evalStepR`.

In this file, namespace `LeanNative.Proofs`:

```
/-- Reserved runtime symbols `evalExpr` interprets as intrinsics
    (`lean_native_*`, `lean_mark_mt`); a lowered local callee must not shadow them.
    Same predicate L2's contract names `reservedRuntimeName`; this leaf spells it
    `reservedRuntimeCallee` so the two lanes cannot collide on one declaration name —
    the fold keeps one spelling. -/
def reservedRuntimeCallee (s : String) : Bool

/-- Pointwise "Δ lowers to Φ" for the FULL-environment semantics. Clause-for-clause the
    shape of L2's `DeclEnvLowers` (pointwise lowering under the driver's mangled-name map,
    unreserved names, tail freshness): tail freshness over the whole list plus the
    functionality of `ctx.findLocalCallee?` is exactly what makes `lookupDeclRec?` and
    `lookupFuncRec?` find corresponding positions WITHOUT stratification. -/
inductive DeclEnvLowersR (fuel : Nat) (ctx : RealBridgeCtx) :
    List (Lean.Compiler.LCNF.Decl .impure) → List LNIRDecl → Prop
  | nil : DeclEnvLowersR fuel ctx [] []
  | cons : ∀ {sd : Lean.Compiler.LCNF.Decl .impure} {ld : LNIRDecl}
      {Δ : List (Lean.Compiler.LCNF.Decl .impure)} {Φ : List LNIRDecl},
      ctx.findLocalCallee? sd.name = some ld.name →
      lowerRealLCNFDecl fuel ctx sd ld.name = .ok ld →
      reservedRuntimeCallee ld.name = false →
      (∀ ld' ∈ Φ, ld'.name ≠ ld.name) →
      DeclEnvLowersR fuel ctx Δ Φ →
      DeclEnvLowersR fuel ctx (sd :: Δ) (ld :: Φ)

/-- `CodeRefines` with the recursion-capable environment (the L3 form of refinement). -/
def CodeRefinesR (Φ : List LNIRDecl) (src tgt : LNIRCode) : Prop :=
  ∀ fuel env st v st', evalCodeR Φ fuel env st src = .ok (v, st') →
    evalCodeR Φ fuel env st tgt = .ok (v, st')
```

### Part I — theorems proved by this leaf (14; appended to `AxiomAudit.lean`, 865 → 879)

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
        match evalCodeR Φ fuel
            ((ld.params.zip vals).foldl (fun acc (p, val) => acc.bind p.id val) VarEnv.empty)
            st ld.body with
        | .error e => .error e
        | .ok (v, st') => evalCodeR Φ (fuel + 1) (env.bind dst v) st' k

theorem evalStepR_localCall_unfold (Δ : List (Lean.Compiler.LCNF.Decl .impure))
    (fuel : Nat) (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
    (decl : Lean.Compiler.LCNF.LetDecl .impure) (k : Lean.Compiler.LCNF.Code .impure)
    (fn : Lean.Name) (args : Array (Lean.Compiler.LCNF.Arg .impure))
    (sd : Lean.Compiler.LCNF.Decl .impure)
    (hval : decl.value = .fap fn args rfl)
    (hloc : (ctx.findLocalCallee? fn).isSome = true)
    (hlk : lookupDeclRec? Δ fn = some sd) :
    evalStepR Δ (fuel + 1) ctx env st (.inl (.let decl k)) =
      match evalArgs env.vals args.toList with
      | .error e => .error e
      | .ok vals =>
        match sd.value with
        | .extern _ => .error (.unsupportedCall fn.toString)
        | .code c =>
          match bindParams ctx true LEnv.empty sd.params.toList vals with
          | .error e => .error e
          | .ok env' =>
            match evalStepR Δ fuel ctx env' st (.inl c) with
            | .error e => .error e
            | .ok (v, st') =>
              evalStepR Δ fuel ctx
                (env.bind decl.fvarId v none
                  (some (if isUnboxedScalarOrTuple (lowerGroundImpureTypeWith ctx decl.type)
                         then lowerGroundImpureTypeWith ctx decl.type else .i64)))
                st' (.inl k)

theorem evalStepR_localCall_miss (Δ : List (Lean.Compiler.LCNF.Decl .impure))
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

theorem DeclEnvLowersR.fresh (fuel : Nat) (ctx : RealBridgeCtx)
    (Δ : List (Lean.Compiler.LCNF.Decl .impure)) (Φ : List LNIRDecl)
    (h : DeclEnvLowersR fuel ctx Δ Φ) :
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

Expected helper lemmas landing with the proofs (shapes not frozen by this contract):
`lookupFuncRec?_mem` / `lookupDeclRec?_mem` (a hit is a member with that name),
`evalSeqLoop_mono_of_step_mono` (pointwise transport through the loop closure),
`evalParFor_fuel_mono`, and the `evalStepR` fuel-monotonicity pair
(`evalStepR_fuel_mono` with the `hasJmpToPure` false-antitonicity sublemma L2's contract
also names) — the last is Part II's helper and may land there instead.

Executable guards land in `lean/LeanNative/Tests/RealLCNFRecTests.lean` (NEW file; L2's
planned `Tests/RealLCNFCallTests.lean` is untouched): a self-recursive declaration
(countdown-accumulate) whose `evalRealLCNFDeclR` result is wrong unless the callee body
re-enters (kills call-as-noop mutants), the same declaration exhausting fuel at too-small
a budget (`.error .fuelExhausted`, never a wrong `.ok`), a two-declaration MUTUAL pair
(even/odd-style) evaluating through `Δ` with both orders of `Δ`, the `Δ = [] / Φ = []`
runs equal to the old evaluators on a call-bearing body, and an `evalCodeR` run of a
lowered self-call body under `Φ = [d]`.

### Part II — the recursion headline, stated for the fold (signatures frozen; proofs
### sequenced after the L2 lane's F-stack merges)

The step-level forward simulation with recursion-capable environments on both sides, and
its code- and declaration-level corollaries. These are the L3 names H1.4 dispatches on:

```
theorem lowerImpureStepPure_soundR (fuel : Nat) (ctx : RealBridgeCtx)
    (Δ : List (Lean.Compiler.LCNF.Decl .impure)) (Φ : List LNIRDecl)
    (st st' : RealBridgeState)
    (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
    (target : Lean.Compiler.LCNF.Code .impure ⊕
      (VarId × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure)))
    (code : LNIRCode) :
    DeclEnvLowersR fuel ctx Δ Φ →
    BridgeStateInv st lenv venv →
    lowerImpureStepPure fuel ctx st target = .ok (code, st') →
    (match target with
      | .inl c => evalStepR Δ fuel ctx lenv hst (.inl c) = .ok (v, hst')
      | .inr (condVar, isBool, idx, discr?, alts) =>
        condVar < st.nextVarId ∧
        (∀ dx, discr? = some dx → (st.lookupFVar? dx).isSome = true) ∧
        (lnirTypeEq (st.getVarType condVar) .i1 = true → isBool = true) ∧
        ∃ cond, venv condVar = some cond ∧
          evalStepR Δ fuel ctx lenv hst (.inr (cond, isBool, idx, discr?, alts)) = .ok (v, hst')) →
    evalCodeR Φ fuel venv hst code = .ok (v, hst')

theorem lowerRealLCNFCode_soundR (fuel : Nat) (ctx : RealBridgeCtx)
    (Δ : List (Lean.Compiler.LCNF.Decl .impure)) (Φ : List LNIRDecl)
    (st : RealBridgeState)
    (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
    (code : Lean.Compiler.LCNF.Code .impure) (lnir : LNIRCode) (st' : RealBridgeState)
    (h_env : DeclEnvLowersR fuel ctx Δ Φ)
    (h_inv : BridgeStateInv st lenv venv)
    (h_lower : lowerRealLCNFCode fuel ctx st code = .ok (lnir, st'))
    (h_eval : evalRealLCNFCodeR Δ fuel ctx lenv hst code = .ok (v, hst')) :
    evalCodeR Φ fuel venv hst lnir = .ok (v, hst')

theorem lowerRealLCNFDecl_soundR (fuel : Nat) (ctx : RealBridgeCtx)
    (Δ : List (Lean.Compiler.LCNF.Decl .impure)) (Φ : List LNIRDecl)
    (decl : Lean.Compiler.LCNF.Decl .impure) (args : List Val) (hst hst' : HeapState)
    (v : Val) (d : LNIRDecl) (mangled : String)
    (h_env : DeclEnvLowersR fuel ctx Δ Φ)
    (h_lower : lowerRealLCNFDecl fuel ctx decl mangled = .ok d)
    (h_eval : evalRealLCNFDeclR Δ fuel ctx decl args hst = .ok (v, hst')) :
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

Why Part II's proofs are sequenced, at the bytes: `lowerImpureStepPure_soundR`'s induction
needs every per-case lemma of the L1 simulation stack
(`Proofs/RealLCNFBridge/{CtorIntrinsic,CtorScalarCall,JpTag,LetValue,Scalar,StateInv,
StepCases,StepMono,UnaryCast}.lean` plus the aux in `RealLCNFBridgeProofs.lean` —
5,441 lines at this tip) restated against an environment-carrying target semantics; every
one of those lemmas concludes in `evalCode`/`evalStep` and is monomorphic in the
semantics. The L2 lane is landing exactly that restatement for F in its own follow-up
commits right now. Cutting an independent R-restatement of the same 5,441 lines in this
leaf would fork one proof stack into two concurrent rewrites that the fold must then
reconcile line by line — the same hazard HORIZONS marks with "do not run in parallel" on
shared files. The sequencing is recorded here the way L2 recorded its own deferred pair:
the names and binders above are frozen for H1.4; the proofs are follow-up commits of the
L3 lane once L2's F-stack merges. Candidate resolutions (the fold owner's call, not this
leaf's): (a) default — R-twin the landed F-stack (mechanical: the per-case bodies differ
only in the lookup rule, full-env-at-decremented-fuel against strict-suffix); (b)
parameterize the per-case stack over the call rule so F and R instantiate one proof; (c)
prove R independently now (forks the stack; rejected above). Also stated for the fold,
elaborable only once L2's definitions exist — the F-to-R embeddings that make the two
semantics one ladder (an F-run is an R-run with the stratification depth paid as fuel):

```
theorem evalCodeF_toR (Φ : FuncEnv) (fuel : Nat) (env : VarEnv) (st : HeapState)
    (c : LNIRCode) (v : Val) (st' : HeapState) :
    evalCodeF Φ fuel env st c = .ok (v, st') →
    evalCodeR Φ (fuel + Φ.length) env st c = .ok (v, st')

theorem evalRealLCNFDeclF_toR (Δ : DeclEnv) (fuel : Nat) (ctx : RealBridgeCtx)
    (decl : Lean.Compiler.LCNF.Decl .impure) (args : List Val) (st : HeapState)
    (v : Val) (st' : HeapState) :
    evalRealLCNFDeclF Δ fuel ctx decl args st = .ok (v, st') →
    evalRealLCNFDeclR Δ fuel ctx decl args st = .ok (v, st')
```

(The second needs no fuel padding: on the LCNF side both semantics burn the step budget
identically and R's lookup is a superset of F's stratified lookup on `DeclEnvLowersR`
environments, whose names are duplicate-free.)

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
- E6 Driver-shaped R-forms: none stated. The driver's compression post-pass surface is
  being removed by the L1 fix round (a review proved it never changes any declaration),
  so the driver-shaped statement reduces to `lowerRealLCNFDecl_sound`, whose R-form IS
  Part II's `lowerRealLCNFDecl_soundR`. One standing caution for consumers of
  `CodeRefinesR`: the generic transfer `CodeRefines src tgt → CodeRefinesR Φ src tgt` is
  FALSE — `src = .letBind x ty (.call f [] ty false) (.ret x)` with `f` bound in `Φ` has
  no env-free `.ok` run, so env-free `CodeRefines src tgt` holds for EVERY `tgt`, while
  `CodeRefinesR Φ src tgt` fails for any `tgt` that disagrees with the call's result. An
  env-free certificate transfers only along call-free runs; `evalCodeR_extend_of_ok` is
  the sound direction.

### Acceptance (quoted) and gates

- "leaf `0 sorryAx`": every Part I theorem lands kernel-checked; the 14 names are appended
  to `AxiomAudit.lean`'s `auditedTheoremNames` with the pinned count raised exactly
  (865 → 879 at this tip; the L2 lane raises the same pin for its own set, so the fold
  resolves the raises additively, the convention L2's contract records).
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
