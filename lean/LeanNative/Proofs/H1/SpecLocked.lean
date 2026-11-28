import LeanNative.Proofs.RealLCNFBridgeProofs

/-!
# H1.F: frozen statement of the H1 `LCNF → LNIR` theorem (`SpecLocked.lean`, Contract V1)

`H1ForwardSim lower` is the H1 theorem shape (`roadmap/HORIZONS.md`, H1): forward simulation on
successful runs. Whenever `lower` accepts a real `Lean.Compiler.LCNF.Decl .impure` and
`RealLCNFSemantics` evaluates it to `(v, hst')`, the lowered `LNIR` declaration, run by
`LeanNative.Semantics.evalCode` from its own parameter list, returns the same `(v, hst')` at the same
fuel. `SpecLocked` fixes `lower := lowerRealLCNFDecl`, the function the driver calls
(`ingestImpureDeclViaReal`); it is discharged by `lowerRealLCNFDecl_sound` with no glue.

Non-vacuity: `posWitness` is a real declaration on which both hypotheses hold.
Tightness: each `negWitness*` is a lowerer mutant that `H1ForwardSim` rejects, refuted on the same
declaration (`0 sorryAx`, `0 native_decide`, no new axioms; every concrete run is closed by `rfl`).

Witnesses avoid `let` on purpose: `lowerGroundImpureType` compares `Lean.Expr` with the `opaque`
`Lean.Expr.eqv`, so the lowered type of a `let` has no kernel-provable value. They use parameter types
from `RealBridgeCtx.paramTypeMap` and `cases`/`return` only.

L2/L3 may change the statement (function environment, fuel-indexed calls); that is a re-lock, not an
edit: a new statement, new witnesses, a new pinned hash.
-/

namespace LeanNative.Proofs.H1

open Lean Lean.Compiler.LCNF
open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

/-- Signature of a lowerer: the driver's `lowerRealLCNFDecl fuel ctx decl mangledSymbol`. -/
abbrev Lowerer := Nat → RealBridgeCtx → Decl .impure → String → Except String LNIRDecl

/-- Run a lowered declaration: bind `d.params` to `args` left to right, then `evalCode d.body`. -/
def evalLNIRDecl (fuel : Nat) (d : LNIRDecl) (args : List Val) (hst : HeapState) :
    Except UBError (Val × HeapState) :=
  evalCode fuel ((d.params.zip args).foldl (fun acc (p, val) => acc.bind p.id val) VarEnv.empty) hst d.body

/-- The H1 statement: forward simulation of `RealLCNFSemantics` by `LNIR` on successful runs. -/
def H1ForwardSim (lower : Lowerer) : Prop :=
  ∀ (fuel : Nat) (ctx : RealBridgeCtx) (decl : Decl .impure) (mangled : String) (d : LNIRDecl)
    (args : List Val) (hst hst' : HeapState) (v : Val),
    lower fuel ctx decl mangled = .ok d →
    evalRealLCNFDecl fuel ctx decl args hst = .ok (v, hst') →
    evalLNIRDecl fuel d args hst = .ok (v, hst')

/-- The locked H1 specification, for the driver's lowering function. -/
def SpecLocked : Prop := H1ForwardSim (lowerRealLCNFDecl · · · ·)

theorem specLocked : SpecLocked := fun fuel ctx decl mangled d args hst hst' v =>
  lowerRealLCNFDecl_sound fuel ctx decl args hst hst' v d mangled

/-! ## Witness declaration: `h1f_select (b : Bool) (x y : UInt64) := if b then x else y` -/

def fv (n : Nat) : FVarId := { name := .num `h1f n }

def mkParam (n : Nat) (ty : Expr) : Param .impure :=
  { fvarId := fv n, binderName := .num `p n, type := ty, borrow := false }

def boolAlt (cidx : Nat) (k : Code .impure) : Alt .impure :=
  .ctorAlt { name := if cidx == 0 then ``Bool.false else ``Bool.true, cidx, size := 0, usize := 0, ssize := 0 } k rfl

def selectDecl : Decl .impure :=
  { name := `h1f_select, levelParams := [], type := ImpureType.uint64, inlineAttr? := none
    params := #[mkParam 1 (mkConst ``Bool), mkParam 2 ImpureType.uint64, mkParam 3 ImpureType.uint64]
    value := .code (.cases (Cases.mk ``Bool ImpureType.uint64 (fv 1)
      #[boolAlt 0 (.return (fv 3)), boolAlt 1 (.return (fv 2))])) }

/-- Parameter types as the driver records them (`buildRealBridgeCtxM … paramTypeMap`). -/
def selectCtx : RealBridgeCtx := { paramTypeMap := [(fv 1, .i1), (fv 2, .i64), (fv 3, .i64)] }

def selectFuel : Nat := 8

def selectArgs (b : Bool) : List Val := [.bool b, .u64 5, .u64 9]

theorem select_lowered_body :
    (lowerRealLCNFDecl selectFuel selectCtx selectDecl "h1f_select").map LNIRDecl.body =
      .ok (.ite 0 (.ret 1) (.ret 2)) := rfl

theorem select_src (b : Bool) :
    evalRealLCNFDecl selectFuel selectCtx selectDecl (selectArgs b) HeapState.empty =
      .ok (.u64 (if b then 5 else 9), HeapState.empty) := by
  cases b <;> rfl

/-- Non-vacuity: the real lowerer accepts `selectDecl`, the source run succeeds, and the locked
    conclusion is the concrete value `5`. -/
theorem posWitness :
    ∃ d, lowerRealLCNFDecl selectFuel selectCtx selectDecl "h1f_select" = .ok d ∧
      evalRealLCNFDecl selectFuel selectCtx selectDecl (selectArgs true) HeapState.empty =
        .ok (.u64 5, HeapState.empty) ∧
      evalLNIRDecl selectFuel d (selectArgs true) HeapState.empty = .ok (.u64 5, HeapState.empty) :=
  ⟨_, rfl, select_src true, specLocked _ _ _ _ _ _ _ _ _ rfl (select_src true)⟩

/-! ## Lowerer mutants -/

/-- Post-compose the real lowerer with a corruption of its output. -/
def mutate (f : LNIRDecl → LNIRDecl) : Lowerer :=
  fun fuel ctx decl mangled => (lowerRealLCNFDecl fuel ctx decl mangled).map f

/-- A mutant is killed when one accepted, source-successful run of it breaks the conclusion. -/
theorem killed_of_run {f : LNIRDecl → LNIRDecl} (b : Bool) {r : Except UBError (Val × HeapState)}
    (hrun : ∀ d, lowerRealLCNFDecl selectFuel selectCtx selectDecl "h1f_select" = .ok d →
      evalLNIRDecl selectFuel (f d) (selectArgs b) HeapState.empty = r)
    (hne : r ≠ .ok (.u64 (if b then 5 else 9), HeapState.empty)) :
    ¬ H1ForwardSim (mutate f) := fun h =>
  hne <| (hrun _ rfl).symm.trans (h _ _ _ _ _ _ _ _ _ rfl (select_src b))

/-- Mutant 1 (inverted condition): swap both arms of every `ite`. -/
def swapIte : LNIRCode → LNIRCode
  | .letBind x ty e k => .letBind x ty e (swapIte k)
  | .rawStore p i v ty k => .rawStore p i v ty (swapIte k)
  | .incRef x n k => .incRef x n (swapIte k)
  | .decRef x n k => .decRef x n (swapIte k)
  | .ite c t e => .ite c (swapIte e) (swapIte t)
  | .seqFor i lo hi a ai ty s k => .seqFor i lo hi a ai ty (swapIte s) (swapIte k)
  | .parFor o n xs ty kk k => .parFor o n xs ty kk (swapIte k)
  | c => c

/-- Mutant 2 (wrong return value): every `ret x` returns the next SSA variable `x + 1`. -/
def shiftRet : LNIRCode → LNIRCode
  | .letBind x ty e k => .letBind x ty e (shiftRet k)
  | .rawStore p i v ty k => .rawStore p i v ty (shiftRet k)
  | .incRef x n k => .incRef x n (shiftRet k)
  | .decRef x n k => .decRef x n (shiftRet k)
  | .ite c t e => .ite c (shiftRet t) (shiftRet e)
  | .seqFor i lo hi a ai ty s k => .seqFor i lo hi a ai ty (shiftRet s) (shiftRet k)
  | .parFor o n xs ty kk k => .parFor o n xs ty kk (shiftRet k)
  | .ret x => .ret (x + 1)
  | c => c

def negWitnessInvertedBranch : LNIRDecl → LNIRDecl := fun d => { d with body := swapIte d.body }

def negWitnessWrongReturn : LNIRDecl → LNIRDecl := fun d => { d with body := shiftRet d.body }

/-- Mutant 3 (dropped binding): the first parameter is never bound in the `LNIR` environment. -/
def negWitnessDroppedParam : LNIRDecl → LNIRDecl := fun d => { d with params := d.params.drop 1 }

/-- Mutant 4 (wrong scrutinee): the condition of a top-level `ite` reads the next variable. -/
def negWitnessWrongScrutinee : LNIRDecl → LNIRDecl := fun d =>
  { d with body := match d.body with | .ite c t e => .ite (c + 1) t e | b => b }

theorem negWitnessInvertedBranch_killed : ¬ H1ForwardSim (mutate negWitnessInvertedBranch) :=
  killed_of_run true (r := .ok (.u64 9, HeapState.empty))
    (fun _ h => by cases h; rfl) (by simp)

theorem negWitnessWrongReturn_killed : ¬ H1ForwardSim (mutate negWitnessWrongReturn) :=
  killed_of_run true (r := .ok (.u64 9, HeapState.empty))
    (fun _ h => by cases h; rfl) (by simp)

theorem negWitnessDroppedParam_killed : ¬ H1ForwardSim (mutate negWitnessDroppedParam) :=
  killed_of_run true (r := .error (.unboundVar 0)) (fun _ h => by cases h; rfl) (by simp)

theorem negWitnessWrongScrutinee_killed : ¬ H1ForwardSim (mutate negWitnessWrongScrutinee) :=
  killed_of_run false (r := .ok (.u64 5, HeapState.empty))
    (fun _ h => by cases h; rfl) (by simp)

end LeanNative.Proofs.H1
