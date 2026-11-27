import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.ToImpureType
import LeanNative.IR.RealLCNFBridge
import LeanNative.IR.RealLCNFSemantics

namespace LeanNative.Proofs.LowerRefines

open Lean
open Lean.Compiler.LCNF
open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

/-!
## H1.4 — Mutant kill matrix for the proved lowering path (roadmap/HORIZONS.md)

Authoritative row (`roadmap/HORIZONS.md`): "H1.4 Mutant kill matrix; coverage number
published | `Proofs/LowerRefines.lean` | L3 | mutants in CI | M". This file is the matrix's
record and the home of the executable pins that close its cheap survivors.

### Why this exists

The H1 proof stack's value is that a meaning-changing edit to the lowering stops the build:
either a theorem over `lowerRealLCNFDecl` / `lowerImpureStepPure` fails to elaborate
(`Proofs/RealLCNFBridgeProofs.lean` and `Proofs/RealLCNFBridge/*.lean`, the L1 stack the
L2/L3 contracts extend toward `lowerRealLCNFDecl_soundF` / `lowerRealLCNFDecl_soundR`), or
an executable `#guard` catches it (`Tests/*.lean`, this file). H1.4 MEASURES that claim
instead of asserting it.

### Methodology (`scripts/proof_mutant_matrix.py`, harness r1)

Each mutant is one small semantic edit at a mechanically enumerated site in
`IR/RealLCNFBridge.lean` (the lowering) or `IR/RealLCNFShared.lean` (the helpers the
lowering shares with the independent semantics — the differential's shared trusted
component). 31 explicit operators over the brief's six classes: operand swap, constant
off-by-one, branch-condition flip, dropped statement, wrong constructor/tag, swapped
arguments; 60 sites at the pinned file sha256s (the harness fails closed on drift and on a
working tree that differs from the measured commit — the same honesty rule as
`scripts/lcnf_coverage_results.json`). Mutations apply only in a throwaway `git worktree`
under `.h14-mutants/`, seeded from the local `lean/.lake` cache, with a pristine `build`
snapshot restored before every mutant; the committed originals are never touched. The kill
signal is a failed `lake build LeanNative` of the proofs/Tests closure; a mutant whose own
module fails to elaborate is NOT_APPLICABLE (stillborn); a build timeout is TIMEOUT and an
OOM / infrastructure failure is INFRA — all three are unmeasured, never kills. Builds run
in their own process group (SIGKILLed whole on timeout), each scratch gets a private
TMPDIR, infra signatures are only consulted on failed builds, every finished mutant is
checkpointed to a progress JSONL (resumable), and a harness exception is an ERROR row.
The harness `--self-test` drives planted always-survives / always-killed / stillborn /
timeout / OOM controls through the real two-stage `run_one`; CI
(`.github/workflows/nightly-conformance.yml`, job `proof-mutant-sample`) runs that
self-test plus a pinned KILLED subset nightly; the full matrix runs behind `--full`.

### Measurement record, including what the earlier harness got wrong

Two full 60-mutant passes ran under the earlier classifier (pass 1 at 69fde31a, pass 2 at
7d824a06; both read "58/60" with 0 stillborn / 0 infra) and DISAGREED on which mutants
survived. The root cause is measured, not guessed: two Tests modules run elaboration-time
`#eval` IO against SHARED temp paths, so a concurrent build (another matrix worker, or any
sibling checkout building this library on the same host) fails them for reasons unrelated
to the mutant. `Tests/EvalLCNFCLITests.lean` writes a fixed-name fixture under `$TMPDIR`
(the host-shared `/tmp` for every earlier-pass worker): pass 2's artifact records
`EvalLCNFCLITests.lean:21:0: no such file or directory` as the `first_error` on all three
of its `EvalLCNFCLITests` "kills", and a 3-repetition re-run reproduced that false kill
LIVE, alternating between two concurrently built mutants with scheduling.
`Tests/StochasticEvolveTests.lean` hard-coded the LITERAL path
`/tmp/stochastic-evolve-integrity.tlpack` for its tamper/no-tamper pack pair, so even
TMPDIR-isolated workers collided — one worker's tampered pack overwrites another's clean
pack ("pack integrity regression") or the cleanup removes it mid-read (ENOENT); a
3-repetition isolated re-run recorded both texts, non-deterministically, on the three
retTy mutants (1-2 of 3 identical runs each). Every kill attributed to either module in
those earlier passes is therefore environment, not the mutant; per the non-inflation rule
("a mutant killed only by flakiness or build nondeterminism is SURVIVED") neither earlier
number is reused. The fixes: the r1 harness gives every scratch a private TMPDIR and
TURBO_LEAN_HOME, and this leaf's Tests edit gives the pack fixture a per-run unique name under `$TMPDIR`
with `finally` cleanup, collision-free even under one shared TMPDIR. The number of record
comes from the fixed harness over the fixed tree, measured at commit 267d0d2c with a
3-repetition determinism read of all five implicated ids first (identical verdicts 3/3
each: four KILLED by this file's pins, the budget mutant SURVIVED 3/3):

  COVERAGE: 59/60 mutants killed (98.3%); denominator 60 = every enumerated mutant
  (0 stillborn, 0 infra, 0 timeout, 0 error). The one survivor is
  `RB-rettyfuel-offby1-00`, recorded in disposition 5 below. Full table with
  per-mutant kill attribution: `scripts/proof_mutant_matrix_results.json`
  (toolchain leanprover/lean4:v4.35.0). At 267d0d2c, 7 of the 59 kills attributed to
  this file (`LeanNative.Proofs.LowerRefines`) as the first failing module: the six
  findings closed in this record plus `RB-fvarlookup-flip-00`, whose inverted fvar
  lookup Pin 3's lowering fixture also reaches — attribution names lake's FIRST
  failure, so a mutant that several modules kill is credited to whichever elaborates
  first.

  RE-MEASURED on 2026-11-26, after L2's
  `Tests/RealLCNFCallTests.lean` and L3's `Tests/RealLCNFRecTests.lean` joined the
  closure (both are absent at 267d0d2c): 59/60 again, every mutant's outcome identical
  to the 267d0d2c run, the same survivor. The results JSON now records this run. In it
  the six findings above still attribute here first, `RB-fvarlookup-flip-00` is first
  reported from `Tests/RealLCNFCallTests.lean`, and five kills are first reported from
  L3's guards in `Tests/RealLCNFRecTests.lean`.

The five implicated mutants and their dispositions:

1. `RS-orderalts-id-00` (`IR/RealLCNFShared.lean:155`, `orderAltsPure` made the identity):
   a SHARED-helper mutant — the lowering and the independent semantics order alternatives
   through the same definition, so the differential stays symmetric and no theorem
   concludes anything the reorder changes. CLOSED HERE: a direct shape pin on
   `orderAltsPure` (constructor alternatives precede `.default`, both input orders).
2. `RS-tupleguard-oror-00` (`IR/RealLCNFShared.lean:106`, `isUnboxedScalarOrTuple`'s
   `&&` to `||`): same shared-helper symmetry. CLOSED HERE: direct pins on the predicate
   (`.tuple []` and `.tuple [.objPtr]` are not unboxed scalar tuples; a flat scalar tuple
   is).
3. `RB-retpin-flip-00` (`IR/RealLCNFBridge.lean:884`, `inferReturnedTypePure` keyed on
   `dst != rv`): retTy is metadata — `lowerRealLCNFDecl_sound`'s conclusion never mentions
   it, and the executable parity guards compare evaluation results, not declared types.
   CLOSED HERE: direct pins on `inferReturnedTypePure`'s binder keying.
4. `RB-ite-swap-03` (`IR/RealLCNFBridge.lean:890`, the `.ite _ t e` MATCH PATTERN's
   binders swapped, so inference recurses else-first): same metadata blind spot. CLOSED
   HERE: a direct pin on the then-branch-first `<|>` order with branches of different
   inferred types.
5. `RB-rettyfuel-offby1-00` (`IR/RealLCNFBridge.lean:914`, the `fuel + 16` inference
   budget raised to `fuel + 17`): SURVIVED — recorded, not closed. NARROWEST STATEMENT:
   nothing constrains `inferReturnedTypePure`'s budget headroom; distinguishing `+ 16`
   from `+ 17` needs a lowered body whose letBind depth exceeds the lowering fuel plus 16,
   which only join-point inlining blowup can produce, and no proof or guard constrains the
   inferred `retTy` on such bodies (the soundness theorems never mention `retTy`; the
   parity guards compare values). A cheap pin would have to hard-code a 17-deep
   jp-inlining fixture against one budget constant — brittle, and it would constrain the
   constant, not a behavior; recorded instead.

The two pass-1-only survivors, each a real finding (the repo rule: a surviving mutant
means untested, never defended), stay closed by this file's pins:

6. `RS-jmpdetect-false-00` (`IR/RealLCNFShared.lean:283`): `hasJmpToPure`'s `.jmp` arm
   forced to `false`, so the recursive-join-point detector never fires. NARROWEST
   STATEMENT of what survived: no proof or guard distinguished the NAMED fail-closed
   rejection ("unsupported recursive join point", `IR/RealLCNFBridge.lean:858-860`) from
   generic fuel exhaustion — the detector sits in the SHARED file, the semantics gate
   mutates symmetrically (`IR/RealLCNFSemantics.lean:840-842`), both sides still error on
   recursive join points via the fuel bound, so the forward simulation holds and
   `Tests/RealLCNFBridgeTests.lean`'s `.isOk == false` pin cannot tell the two errors
   apart. The L3 contract (`Proofs/LowerRec.lean`) freezes exactly this behavior as the
   kernel theorems `lowerImpureStepPure_recursive_jp_rejected` /
   `evalStep_recursive_jp_unsupported` (its exclusion E2: `Code.jp.recursive` stays
   honestly `rejected`); those land with the L3 lane. CLOSED HERE executably.
7. `RB-restore-drop-03` (`IR/RealLCNFBridge.lean:874`): the `.jmp` arm's bridge-state
   restore (`fvarMap`/`activeCtor`/`jpDecls` back to their saved copies) dropped.
   NARROWEST STATEMENT: the mutant is OUTPUT-equivalent through every consumer at these
   bytes — a `.jmp` is terminal in its block, every enclosing `cases`-alternative arm
   re-restores the same three fields from its own saved copies (the restores that
   `Proofs.RealLCNFBridge.StepMono` kills as `RB-restore-drop-00/01/02`), and the
   declaration entry discards the final state — so no theorem concludes anything the
   drop changes, and no guard read the returned state. CLOSED HERE executably.

### Constraints, assumptions, limits

- Enumeration covers `IR/RealLCNFBridge.lean` + `IR/RealLCNFShared.lean`. The other
  proved-path helper files (`IR/BridgeHelpers/*.lean`, driver context construction) are
  NOT enumerated in this matrix; extending the operator set to them is follow-up work for
  the matrix owner, not silently claimed.
- A kill is attributed to the FIRST failing module lake reports; later failures behind it
  are not enumerated.
- `Tests/EvalLCNFCLITests.lean`'s elaboration-time IO uses fixed-name files under
  `$TMPDIR` and shells into the CLI, so its verdict is only deterministic when nothing
  else builds this library under the same TMPDIR concurrently. The r1 harness isolates
  TMPDIR per scratch, and this leaf re-pointed `Tests/StochasticEvolveTests.lean`'s pack
  fixture from a literal `/tmp` to a per-run UNIQUE name under `$TMPDIR` with `finally`
  cleanup (measured false kills; see the record above), so that fixture no longer
  collides even between two builds sharing one TMPDIR. A unique-name fixture inside
  EvalLCNFCLITests itself is the H1.1 file owner's fix, recorded here as a handoff, not
  edited by this leaf; until it lands, two plain single-TMPDIR builds of this library on
  one host can still fail each other's elaboration through THAT module — a repo-wide
  flake independent of this matrix.
- The matrix measures the closure at its recorded commit; it is re-measured (and the
  script's pins re-set) whenever the two enumerated files change — they are sha-pinned in
  the harness exactly so a stale matrix fails closed instead of reading as current.
- Equivalent-mutant risk: `RB-restore-drop-03`'s equivalence argument above is over the
  enumerated consumers at these bytes, not a theorem; the pin below constrains the
  contract rather than relying on that argument.

### Executable pins

No new theorems (so `AxiomAudit.lean`'s pinned count is untouched by this leaf — the L2
and L3 lanes are raising it concurrently for their own sets); every pin is a `#guard`
over the real lowering, elaborated on every `lake build LeanNative`, in the mutant
harness's kill closure, and none performs IO or touches TMPDIR.
-/

private def fv (n : Nat) : FVarId := { name := .num `x n }

private def mkParam (n : Nat) (ty : Expr) (borrow : Bool := false) : Param .impure :=
  { fvarId := fv n, binderName := .num `p n, type := ty, borrow := borrow }

private def mkLet (n : Nat) (ty : Expr) (val : LetValue .impure) : LetDecl .impure :=
  { fvarId := fv n, binderName := .num `v n, type := ty, value := val }

private def mkDecl (name : Name) (params : Array (Param .impure)) (retTy : Expr)
    (body : Code .impure) : Decl .impure :=
  { name := name
    levelParams := []
    type := retTy
    params := params
    value := .code body
    inlineAttr? := none }

private def u64Ty : Expr := ImpureType.uint64

/-! ### Pin 1 — the recursive-join-point detector (`hasJmpToPure`) fires
Kills `RS-jmpdetect-false-00`: with the `.jmp` arm forced `false` the detector never
reports a self-jump. Positive and negative cases, direct and behind a `let`. -/

#guard hasJmpToPure 32 (fv 10) (.inl (.jmp (fv 10) #[])) == true
#guard hasJmpToPure 32 (fv 10) (.inl (.jmp (fv 11) #[])) == false
#guard hasJmpToPure 32 (fv 10)
  (.inl (.let (mkLet 1 u64Ty (.lit (.uint64 0))) (.jmp (fv 10) #[.fvar (fv 1)]))) == true
#guard hasJmpToPure 32 (fv 10) (.inl (.return (fv 1))) == false

/-! ### Pin 2 — recursive join points are rejected by NAME, fail-closed, on both pinned
artifacts (the behavior the L3 contract's E2 freezes). A detector that never fires still
errors via the fuel bound, so `isOk == false` alone cannot see the difference; these pins
check the named rejection itself, on the lowering and on the independent semantics. -/

private def recJpFixture : Decl .impure :=
  let jpLoop : FunDecl .impure :=
    FunDecl.mk (fv 10) `jp_loop #[mkParam 11 u64Ty] u64Ty (.jmp (fv 10) #[.fvar (fv 11)])
  mkDecl `h14_rec_jp #[mkParam 1 u64Ty] u64Ty <|
    .jp jpLoop (.jmp (fv 10) #[.fvar (fv 1)])

#guard match lowerRealLCNFDecl 32 { arch := .x86_64 } recJpFixture with
  | .error e => e.startsWith "[lean-native] unsupported recursive join point"
  | .ok _ => false

#guard match evalRealLCNFDecl 32 { arch := .x86_64 } recJpFixture [.u64 1] with
  | .error (.unsupportedCall m) => m == "recursive join point"
  | _ => false

/-! ### Pin 3 — the `.jmp` arm's state contract: the returned `RealBridgeState` carries the
SAVED `fvarMap`/`activeCtor`/`jpDecls`, not the join-point body's overrides.
Kills `RB-restore-drop-03`. The enclosing-alternative restores masked this drop from every
output-level check (see the matrix record above); this pin reads the arm's own output. -/

private def jmpPreState : RealBridgeState :=
  let st0 : RealBridgeState := {}
  let (_, st1) := st0.internFVar (fv 1) .i64 true
  st1.setJpDecl (fv 10) [mkParam 11 u64Ty]
    (.let (mkLet 12 u64Ty (.lit (.uint64 7))) (.return (fv 12)))

#guard match lowerImpureStepPure 32 { arch := .x86_64 } jmpPreState
    (.inl (.jmp (fv 10) #[.fvar (fv 1)])) with
  | .ok (_, stOut) =>
      stOut.fvarMap == jmpPreState.fvarMap &&
      stOut.activeCtor == jmpPreState.activeCtor &&
      stOut.jpDecls.map (fun e => e.1) == jmpPreState.jpDecls.map (fun e => e.1)
  | .error _ => false

/-! ### Pin 4 — `orderAltsPure` puts every constructor alternative before `.default`.
Kills `RS-orderalts-id-00` deterministically (the earlier "kill" was the TMPDIR collision;
the lowering and the semantics share this definition, so the differential cannot see it). -/

private def altCtorTrue : Alt .impure :=
  .ctorAlt { name := ``Bool.true, cidx := 1, size := 0, usize := 0, ssize := 0 }
    (.return (fv 1)) rfl

private def altDefault : Alt .impure := .default (.return (fv 2))

#guard match orderAltsPure [altDefault, altCtorTrue] with
  | [.ctorAlt _ _ _, .default _] => true
  | _ => false
#guard match orderAltsPure [altCtorTrue, altDefault] with
  | [.ctorAlt _ _ _, .default _] => true
  | _ => false

/-! ### Pin 5 — `isUnboxedScalarOrTuple` admits exactly non-empty all-scalar tuples.
Kills `RS-tupleguard-oror-00` (`&&` to `||` admits `.tuple []` and heap-field tuples). -/

#guard isUnboxedScalarOrTuple (.tuple [.i64, .f64]) == true
#guard isUnboxedScalarOrTuple (.tuple []) == false
#guard isUnboxedScalarOrTuple (.tuple [.objPtr]) == false

/-! ### Pin 6 — `inferReturnedTypePure` keys on the returned binder and prefers the
then-branch. Kills `RB-retpin-flip-00` (keyed on `dst != rv`) and `RB-ite-swap-03` (the
`.ite` match binders swapped, recursing else-first): retTy is metadata no soundness
theorem mentions, so only a direct pin constrains the inference. -/

#guard inferReturnedTypePure 8 (.letBind 1 .i64 (.scalar (.constU64 0)) (.ret 1))
  == some .i64
#guard inferReturnedTypePure 8 (.letBind 1 .i64 (.scalar (.constU64 0)) (.ret 0))
  == none
#guard inferReturnedTypePure 8
    (.ite 0 (.letBind 1 .i64 (.scalar (.constU64 0)) (.ret 1))
            (.letBind 2 .f64 (.scalar (.constU64 0)) (.ret 2)))
  == some .i64

end LeanNative.Proofs.LowerRefines
