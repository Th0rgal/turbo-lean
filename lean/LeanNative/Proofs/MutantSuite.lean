import LeanNative.Semantics.Eval

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics

/-!
# Contract V3: Mandatory 3-Mutant Kill Matrix (`MutantSuite.lean`)

Each mutant is a concrete buggy `LNIRCode` / `ScalarExpr` / `HeapState` program over the real
operational semantics (`LeanNative.Semantics.Eval`). Executable boolean checkers are verified
at elaboration time via `#guard` and proved in-kernel via `decide` (`0 sorryAx`, `0 native_decide`).
-/

/-- Concrete environment shared by the off-by-one and algebraic mutants:
    `%0 = 0` (`lo`), `%1 = 4` (`hi`), `%2 = 1` (`shift`). -/
def mutantEnv : VarEnv :=
  VarEnv.empty.bind 0 (.u64 0) |>.bind 1 (.u64 4) |>.bind 2 (.u64 1)

/-- Fuel large enough for the concrete loops (`hi - lo = 4`). -/
def mutantFuel : Nat := 16

/-- Loop step: `acc' = acc + 1`. -/
def loopStepInc : LNIRCode :=
  .letBind 10 .i64 (.scalar (.binOp .add (.var 4) (.constU64 1))) (.ret 10)

/-- Unmutated `seqFor`: iterations `lo ..< hi`, i.e. count `hi.toNat - lo.toNat`. -/
def loopUnmutated : LNIRCode :=
  .letBind 3 .i64 (.scalar (.constU64 0))
    (.seqFor 5 0 1 4 3 .i64 loopStepInc (.ret 4))

/-- Mutant 1 (Off-by-One Loop Boundary Error): trip count is `(hi - 1) - lo` instead of `hi - lo`. -/
def loopOffByOne : LNIRCode :=
  .letBind 9 .i64 (.scalar (.binOp .sub (.var 1) (.constU64 1)))
    (.letBind 3 .i64 (.scalar (.constU64 0))
      (.seqFor 5 0 9 4 3 .i64 loopStepInc (.ret 4)))

/-- Killed iff the mutant's accumulator differs from the unmutated loop on `(fuel, env, st)`. -/
def mutant1Killed (fuel : Nat) (env : VarEnv) (st : HeapState) : Bool :=
  match evalCode fuel env st loopUnmutated, evalCode fuel env st loopOffByOne with
  | .ok (vGood, _), .ok (vBad, _) => !(vGood == vBad)
  | _, _ => false

#guard mutant1Killed mutantFuel mutantEnv HeapState.empty = true

theorem mutant1_off_by_one_killed (fuel : Nat) (h_fuel : fuel = mutantFuel) :
    mutant1Killed fuel mutantEnv HeapState.empty = true := by
  subst h_fuel
  decide

/-- Shared `Array UInt64` buffer (`exclusive := false`, representing `rc > 1`). -/
def sharedBuf : ArrayBuffer :=
  { id := 7, exclusive := false, data := #[10, 20, 30, 40] }

def sharedHeap : HeapState :=
  { buffers := [sharedBuf], nextId := 7 }

/-- `%0` and `%1` both alias buffer `7`, `%2 = 0` (index), `%3 = 99` (store value). -/
def aliasEnv : VarEnv :=
  VarEnv.empty.bind 0 (.sarrayId 7) |>.bind 1 (.sarrayId 7)
    |>.bind 2 (.u64 0) |>.bind 3 (.u64 99)

/-- Mutant 2 (Alias / Exclusivity Violation): `sarrayDataPtr` + unguarded `rawStore` on a shared buffer. -/
def rawStoreAliasMutant : LNIRCode :=
  .letBind 4 (.rawPtr .i64) (.sarrayDataPtr 0 .i64)
    (.rawStore 4 2 3 .i64 (.ret 4))

/-- Spec-compliant path: `sarraySet` performs copy-on-write via `ensureExclusive` and succeeds. -/
def sarraySetCow : LNIRCode :=
  .letBind 4 (.sarray .i64) (.sarraySet 0 2 3 .i64) (.ret 4)

def mutant2Killed (fuel : Nat) (env : VarEnv) (st : HeapState) : Bool :=
  match evalCode fuel env st rawStoreAliasMutant, evalCode fuel env st sarraySetCow with
  | .error (.nonExclusiveWrite _), .ok _ => true
  | _, _ => false

#guard mutant2Killed mutantFuel aliasEnv sharedHeap = true

theorem mutant2_exclusivity_violation_killed (st : HeapState) (h_st : st = sharedHeap) :
    mutant2Killed mutantFuel aliasEnv st = true := by
  subst h_st
  decide

/-- Unmutated scalar expression: `1 <<< 3 = 8`. -/
def scalarShl : ScalarExpr :=
  .binOp .shl (.constU64 1) (.constU64 3)

/-- Mutant 3 (Algebraic / Semantic Swap): `.shl` replaced by `.shr` (`1 >>> 3 = 0`). -/
def scalarShrMutant : ScalarExpr :=
  .binOp .shr (.constU64 1) (.constU64 3)

def codeShl : LNIRCode :=
  .letBind 0 .i64 (.scalar scalarShl) (.ret 0)

def codeShrMutant : LNIRCode :=
  .letBind 0 .i64 (.scalar scalarShrMutant) (.ret 0)

def mutant3Killed (env : VarEnv) (fuel : Nat) (st : HeapState) : Bool :=
  match evalScalarExpr env scalarShl, evalScalarExpr env scalarShrMutant with
  | .ok vShl, .ok vShr =>
    !(vShl == vShr) &&
      match evalCode fuel env st codeShl, evalCode fuel env st codeShrMutant with
      | .ok (cShl, _), .ok (cShr, _) => !(cShl == cShr)
      | _, _ => false
  | _, _ => false

#guard mutant3Killed VarEnv.empty mutantFuel HeapState.empty = true

theorem mutant3_algebraic_swap_killed (fuel : Nat) (h_fuel : fuel = mutantFuel) :
    mutant3Killed VarEnv.empty fuel HeapState.empty = true := by
  subst h_fuel
  decide

/-- Aggregate kill matrix predicate: all 3 mandatory AST mutants are killed. -/
def allThreeMandatoryMutantsKilled (fuel : Nat) : Bool :=
  mutant1Killed fuel mutantEnv HeapState.empty &&
    mutant2Killed fuel aliasEnv sharedHeap &&
    mutant3Killed VarEnv.empty fuel HeapState.empty

#guard allThreeMandatoryMutantsKilled mutantFuel = true

theorem all_three_mandatory_mutants_killed (fuel : Nat) (h_fuel : fuel = mutantFuel) :
    allThreeMandatoryMutantsKilled fuel = true := by
  subst h_fuel
  decide

end LeanNative.Proofs
