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
## H1.4 — Mutant kill matrix for the proved lowering path (roadmap/HORIZONS.md) — w-h14

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

### Methodology (`scripts/proof_mutant_matrix.py`)

Each mutant is one small semantic edit at a mechanically enumerated site in
`IR/RealLCNFBridge.lean` (the lowering) or `IR/RealLCNFShared.lean` (the helpers the
lowering shares with the independent semantics — the differential's shared trusted
component). 31 explicit operators over the brief's six classes: operand swap, constant
off-by-one, branch-condition flip, dropped statement, wrong constructor/tag, swapped
arguments; 60 sites at the pinned file sha256s (the harness fails closed on drift, the
same honesty rule as `scripts/lcnf_coverage_results.json`). Mutations apply only in a
throwaway `git worktree` under `.h14-mutants/`, seeded from the local `lean/.lake` cache,
with a pristine `build` snapshot restored before every mutant; the committed originals are
never touched. The kill signal is a failed `lake build LeanNative` of the proofs/Tests
closure; a mutant whose own module fails to elaborate is NOT_APPLICABLE (stillborn), and
infrastructure signatures are INFRA (unmeasured), never kills. The harness `--self-test`
drives planted always-survives / always-killed / stillborn / infra controls through the
real classifier; CI (`.github/workflows/nightly-conformance.yml`, job
`proof-mutant-sample`) runs that self-test plus a pinned KILLED subset nightly; the full
matrix runs behind `--full`.

### The matrix (full table: `scripts/proof_mutant_matrix_results.json`)

Measured at commit d1c2254d (pass 1, BEFORE this file's guards existed), 60 valid mutants,
0 stillborn, 0 infra: 58 KILLED / 2 SURVIVED. Kills attribute to both designed signals —
theorem modules (`Proofs.RealLCNFBridge.{Scalar, JpTag, StepMono, StateInv, UnaryCast,
CtorIntrinsic, CtorScalarCall, LetValue}`) and executable guards
(`Tests.{HeapObjContract, EvalLCNFCLITests, ProofRetentionTests, HeapObj5b}`). By
category: operand-swap 6/6, swapped-args 2/2, const-offby1 7/7, wrong-ctor-tag 11/11,
branch-flip 20/21, dropped-stmt 12/13.

The two pass-1 survivors, each a real finding (the repo rule: a surviving mutant means
untested, never defended), and what this file does about them:

1. `RS-jmpdetect-false-00` (`IR/RealLCNFShared.lean:283`): `hasJmpToPure`'s `.jmp` arm
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
   honestly `rejected`); those land with the L3 lane. CLOSED HERE executably: the
   detector pins and the named-rejection pins below fail on the mutant.
2. `RB-restore-drop-03` (`IR/RealLCNFBridge.lean:874`): the `.jmp` arm's bridge-state
   restore (`fvarMap`/`activeCtor`/`jpDecls` back to their saved copies) dropped.
   NARROWEST STATEMENT: the mutant is OUTPUT-equivalent through every consumer at these
   bytes — a `.jmp` is terminal in its block, every enclosing `cases`-alternative arm
   re-restores the same three fields from its own saved copies (the restores that
   `Proofs.RealLCNFBridge.StepMono` killed as `RB-restore-drop-00/01/02`), and the
   declaration entry discards the final state — so no theorem concludes anything the
   drop changes, and no guard read the returned state. CLOSED HERE executably: the
   state-contract pin below checks the arm's documented restore on the returned
   `RealBridgeState` directly.

With this file's guards in the closure, the confirmation pass over the same 60 sites
reads 60/60 KILLED (0 stillborn, 0 infra) — the published H1.4 coverage number:

  COVERAGE: 60/60 mutants killed (100.0%); denominator 60 = all enumerated mutants
  (0 stillborn, 0 infra); 58/60 (96.7%) killed by the pre-existing proof stack and
  guards alone, the 2 pass-1 survivors above killed by this file's pins.

### Constraints, assumptions, limits

- Enumeration covers `IR/RealLCNFBridge.lean` + `IR/RealLCNFShared.lean`. The other
  proved-path helper files (`IR/BridgeHelpers/*.lean`, driver context construction) are
  NOT enumerated in this matrix; extending the operator set to them is follow-up work for
  the matrix owner, not silently claimed.
- A kill is attributed to the FIRST failing module lake reports; later failures behind it
  are not enumerated.
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
harness's kill closure.
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

end LeanNative.Proofs.LowerRefines
