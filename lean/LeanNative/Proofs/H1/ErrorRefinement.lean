import LeanNative.Proofs.H1.SpecLocked

/-!
# W1E (`H1-ERR`): error preservation for the H1 `LCNF → LNIR` lowering

`SpecLocked.lean` locks forward simulation on *successful* source runs. This file asks what the
lowering does on *failing* source runs.

* Refutation: the naive statement "every source error is an `LNIR` error" is false.
  `evalRealLCNFDecl` binds parameters with `bindParams`, which rejects surplus arguments with
  `typeError "join point arity mismatch"`; `evalLNIRDecl` binds with `List.zip`, which drops them.
  Four arguments to `selectDecl` make the source fail and the lowered code return `.ok`
  (`naiveErrorPreservation_false`).
* Universal consequences of `specLocked`: the lowered code never fails where the source succeeds
  (`noSpuriousError`), two successful runs agree (`outcomeAgree`), and every lowered run either
  matches the source or the source failed (`lowered_ok_or_source_error`).
* Corrected statement: `H1ErrorPreservation` adds `args.length = decl.params.size` and excludes
  `fuelExhausted` (the two evaluators spend fuel at different rates). It holds on `selectDecl`,
  where the two outcomes are equal for every 3-argument call (`select_outcome_eq`,
  `select_errorPreservation`), and it is not vacuous there (`select_error_witness`).
-/

namespace LeanNative.Proofs.H1

open Lean Lean.Compiler.LCNF
open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

/-! ## The naive statement and its refutation -/

/-- Naive error preservation: an accepted declaration whose source run fails also fails when
    lowered (with any error). -/
def NaiveErrorPreservation (lower : Lowerer) : Prop :=
  ∀ (fuel : Nat) (ctx : RealBridgeCtx) (decl : Decl .impure) (mangled : String) (d : LNIRDecl)
    (args : List Val) (hst : HeapState) (e : UBError),
    lower fuel ctx decl mangled = .ok d →
    evalRealLCNFDecl fuel ctx decl args hst = .error e →
    ∃ e', evalLNIRDecl fuel d args hst = .error e'

/-- One surplus argument: `selectDecl` has three parameters. -/
def selectArgsExtra : List Val := [.bool true, .u64 5, .u64 9, .u64 0]

theorem select_src_extra :
    evalRealLCNFDecl selectFuel selectCtx selectDecl selectArgsExtra HeapState.empty =
      .error (.typeError "join point arity mismatch") := rfl

theorem select_tgt_extra : ∀ d,
    lowerRealLCNFDecl selectFuel selectCtx selectDecl "h1f_select" = .ok d →
    evalLNIRDecl selectFuel d selectArgsExtra HeapState.empty = .ok (.u64 5, HeapState.empty) :=
  fun _ h => by
    cases h
    rfl

/-- The naive statement fails for the driver's lowerer: the source rejects a surplus argument,
    the lowered code ignores it. -/
theorem naiveErrorPreservation_false :
    ¬ NaiveErrorPreservation (lowerRealLCNFDecl · · · ·) := fun h => by
  obtain ⟨e', he'⟩ := h _ _ _ _ _ _ _ _ rfl select_src_extra
  rw [select_tgt_extra _ rfl] at he'
  cases he'

/-! ## Universal consequences of `specLocked` -/

/-- No spurious errors: where the source succeeds, the lowered code does not fail. -/
theorem noSpuriousError (fuel : Nat) (ctx : RealBridgeCtx) (decl : Decl .impure)
    (mangled : String) (d : LNIRDecl) (args : List Val) (hst : HeapState)
    (r : Val × HeapState) (e : UBError)
    (hlow : lowerRealLCNFDecl fuel ctx decl mangled = .ok d)
    (hsrc : evalRealLCNFDecl fuel ctx decl args hst = .ok r) :
    evalLNIRDecl fuel d args hst ≠ .error e := by
  rw [specLocked fuel ctx decl mangled d args hst r.2 r.1 hlow hsrc]
  exact fun h => by cases h

/-- Two successful runs (source and lowered) return the same value and heap. -/
theorem outcomeAgree (fuel : Nat) (ctx : RealBridgeCtx) (decl : Decl .impure)
    (mangled : String) (d : LNIRDecl) (args : List Val) (hst : HeapState)
    (r r' : Val × HeapState)
    (hlow : lowerRealLCNFDecl fuel ctx decl mangled = .ok d)
    (hsrc : evalRealLCNFDecl fuel ctx decl args hst = .ok r)
    (htgt : evalLNIRDecl fuel d args hst = .ok r') : r = r' := by
  rw [specLocked fuel ctx decl mangled d args hst r.2 r.1 hlow hsrc] at htgt
  cases htgt
  rfl

/-- Every run of an accepted declaration either reproduces the source outcome or the source
    failed. -/
theorem lowered_ok_or_source_error (fuel : Nat) (ctx : RealBridgeCtx) (decl : Decl .impure)
    (mangled : String) (d : LNIRDecl) (args : List Val) (hst : HeapState)
    (hlow : lowerRealLCNFDecl fuel ctx decl mangled = .ok d) :
    (∃ r, evalRealLCNFDecl fuel ctx decl args hst = .ok r ∧ evalLNIRDecl fuel d args hst = .ok r) ∨
      ∃ e, evalRealLCNFDecl fuel ctx decl args hst = .error e := by
  cases hsrc : evalRealLCNFDecl fuel ctx decl args hst with
  | error e => exact .inr ⟨e, rfl⟩
  | ok r => exact .inl ⟨r, rfl, specLocked fuel ctx decl mangled d args hst r.2 r.1 hlow hsrc⟩

/-! ## The corrected statement -/

/-- Error preservation on one declaration: with exactly one argument per parameter, every
    non-`fuelExhausted` source error is the lowered error. -/
def H1ErrorPreservationOn (lower : Lowerer) (fuel : Nat) (ctx : RealBridgeCtx)
    (decl : Decl .impure) (mangled : String) : Prop :=
  ∀ (d : LNIRDecl) (args : List Val) (hst : HeapState) (e : UBError),
    lower fuel ctx decl mangled = .ok d →
    args.length = decl.params.size →
    e ≠ .fuelExhausted →
    evalRealLCNFDecl fuel ctx decl args hst = .error e →
    evalLNIRDecl fuel d args hst = .error e

/-- The corrected H1 error-preservation statement, over all declarations. -/
def H1ErrorPreservation (lower : Lowerer) : Prop :=
  ∀ fuel ctx decl mangled, H1ErrorPreservationOn lower fuel ctx decl mangled

/-! ## Witnesses on `selectDecl` -/

/-- On `selectDecl`, every 3-argument run has the same outcome, success or failure, before and
    after lowering. -/
theorem select_outcome_eq (c x y : Val) (hst : HeapState) : ∀ d,
    lowerRealLCNFDecl selectFuel selectCtx selectDecl "h1f_select" = .ok d →
    evalLNIRDecl selectFuel d [c, x, y] hst =
      evalRealLCNFDecl selectFuel selectCtx selectDecl [c, x, y] hst := fun _ h => by
  cases h
  cases c with
  | bool b => cases b <;> rfl
  | u64 n => simp [evalLNIRDecl, evalRealLCNFDecl] <;> rfl
  | u256 w => simp [evalLNIRDecl, evalRealLCNFDecl] <;> rfl
  | _ => rfl

/-- The corrected statement holds on `selectDecl`. -/
theorem select_errorPreservation :
    H1ErrorPreservationOn (lowerRealLCNFDecl · · · ·) selectFuel selectCtx selectDecl
      "h1f_select" := by
  intro d args hst e hlow hlen _ hsrc
  match args, hlen with
  | [c, x, y], _ => exact (select_outcome_eq c x y hst d hlow).trans hsrc

/-- The source error of `selectDecl` on a non-boolean scrutinee. -/
def selectScrutineeError : UBError := .typeError "ite condition must be bool, u64, or u64"

theorem select_src_unit :
    evalRealLCNFDecl selectFuel selectCtx selectDecl [.unit, .u64 5, .u64 9] HeapState.empty =
      .error selectScrutineeError := rfl

/-- Non-vacuity: a well-arity call of `selectDecl` on a non-boolean scrutinee fails at the source
    with a non-`fuelExhausted` error, and the lowered code fails with the same error. -/
theorem select_error_witness :
    ∃ d e, lowerRealLCNFDecl selectFuel selectCtx selectDecl "h1f_select" = .ok d ∧
      e ≠ UBError.fuelExhausted ∧
      evalRealLCNFDecl selectFuel selectCtx selectDecl [.unit, .u64 5, .u64 9]
        HeapState.empty = .error e ∧
      evalLNIRDecl selectFuel d [.unit, .u64 5, .u64 9] HeapState.empty = .error e := by
  have hne : selectScrutineeError ≠ UBError.fuelExhausted := fun h => by cases h
  refine ⟨_, selectScrutineeError, rfl, hne, select_src_unit, ?_⟩
  exact select_errorPreservation _ _ _ _ rfl rfl hne select_src_unit

end LeanNative.Proofs.H1
