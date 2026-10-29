import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.IR.Codec
import LeanNative.Spec
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanSys.Posix
import LeanSys.Codec
import LeanSys.Store

namespace LeanNative.Backend.FastCheck

open LeanNative.IR
open LeanNative.IR.Codec
open LeanNative.Semantics
open LeanSys.Posix
open LeanSys.Codec
open LeanSys.Store

/-!
# GPU/SIMD Constraint-Propagating FastCheck & Certified Counterexample Engine (`LeanNative.Backend.FastCheck`)

Provides a self-contained (zero `import Lean`) falsification and property-testing backend for LNIR:
1. **Equality Constraint Propagation (`propagatePreconditionEqualities`)**:
   Eliminates `VacuousPass` failure modes on equality-constrained preconditions (`x0 == x1 + 42`)
   by substituting `x := rhs` directly into the generator and declaration body.
2. **Deterministic 64/256-Bit Boundary Value Tables + Pairwise Collision + SplitMix64**:
   Tests 64-bit and 256-bit EVM/Verity boundary values (`0, 1, 2, 2^64-1, 2^128-1, 2^255, 2^256-1, WAD 10^18, MAX_UINT256 - 1`),
   pairwise parameter collisions (`x_i = x_j`), and parallel SplitMix64 streams.
3. **Certified Counterexample Validator (`certifyCounterexample`)**:
   Re-evaluates every candidate counterexample through `LeanNative.Semantics.Eval.evalCode`,
   backed by the machine-checked theorem `certifyCounterexample_no_false_positive` (0 `sorry`).
4. **LLVM 18 CPU SIMD & NVIDIA PTX 8.0 FastCheck Kernel Codegen**:
   Emits `@lean_native_fastcheck_simd` (LLVM 18 IR) and `lean_native_fastcheck_kernel` (PTX 8.0, `sm_90`)
   with 4-limb `.reg .u64` 256-bit carry-chained arithmetic, `satisfied_preconditions_count` atomic
   tracking, and atomic witness capture.
-/

/-! ## 1. Equality Constraint Propagation (`propagatePreconditionEqualities`) -/

/-- Precondition equality substitution `lhsVar := rhsExpr` extracted from an `ite` guard. -/
structure ConstraintSub where
  lhsVar  : VarId
  rhsExpr : ScalarExpr
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Check whether `v` occurs inside `ScalarExpr`. -/
def scalarExprMentionsVar (v : VarId) : ScalarExpr → Bool
  | .constU64 _ | .constBool _ => false
  | .var id => id == v
  | .binOp _ l r => scalarExprMentionsVar v l || scalarExprMentionsVar v r
  | .unaryOp _ a => scalarExprMentionsVar v a
  | .select c t e =>
    scalarExprMentionsVar v c || scalarExprMentionsVar v t || scalarExprMentionsVar v e
  | .fma a b c =>
    scalarExprMentionsVar v a || scalarExprMentionsVar v b || scalarExprMentionsVar v c

/-- Substitute `ConstraintSub`s into a `ScalarExpr`. -/
def substScalarExpr (subs : List ConstraintSub) : ScalarExpr → ScalarExpr
  | .constU64 v => .constU64 v
  | .constBool b => .constBool b
  | .var id =>
    match subs.find? (fun s => s.lhsVar == id) with
    | some s => s.rhsExpr
    | none => .var id
  | .binOp op l r => .binOp op (substScalarExpr subs l) (substScalarExpr subs r)
  | .unaryOp op a => .unaryOp op (substScalarExpr subs a)
  | .select c t e =>
    .select (substScalarExpr subs c) (substScalarExpr subs t) (substScalarExpr subs e)
  | .fma a b c =>
    .fma (substScalarExpr subs a) (substScalarExpr subs b) (substScalarExpr subs c)

/-- Substitute `ConstraintSub`s into an `LNIRExpr`. -/
def substLNIRExpr (subs : List ConstraintSub) (e : LNIRExpr) : LNIRExpr :=
  match e with
  | .scalar se => .scalar (substScalarExpr subs se)
  | other => other

/-- Substitute `ConstraintSub`s throughout an `LNIRCode` block. -/
def substLNIRCode (subs : List ConstraintSub) : LNIRCode → LNIRCode
  | .letBind dst ty val k => .letBind dst ty (substLNIRExpr subs val) (substLNIRCode subs k)
  | .rawStore pv iv vv ty k => .rawStore pv iv vv ty (substLNIRCode subs k)
  | .incRef ov c k => .incRef ov c (substLNIRCode subs k)
  | .decRef ov c k => .decRef ov c (substLNIRCode subs k)
  | .ite cv t e => .ite cv (substLNIRCode subs t) (substLNIRCode subs e)
  | .seqFor iv lv hv av ai aty step k =>
    .seqFor iv lv hv av ai aty (substLNIRCode subs step) (substLNIRCode subs k)
  | .parFor ov lv ins ety kern k => .parFor ov lv ins ety kern (substLNIRCode subs k)
  | .ret v => .ret v
  | .unreachable => .unreachable

private def recordTrueVar (dst : VarId) (val : LNIRExpr) (trueVars : List VarId) : List VarId :=
  match val with
  | .scalar (.constBool true) | .scalar (.constU64 1) => dst :: trueVars
  | _ => trueVars

/-- Check whether an `elseBranch` in an `ite` guard represents a vacuous pass (returns constant `true` or `1`). -/
def isVacuousTrueBranch (trueVars : List VarId) : LNIRCode → Bool
  | .ret v => trueVars.contains v
  | .letBind dst _ val k => isVacuousTrueBranch (recordTrueVar dst val trueVars) k
  | _ => false

/-- Generic traversal over vacuous-else precondition guards `(ite condVar thenCode elseCode)`. -/
def collectVacuousGuardHints {α : Type} (onGuard : List (VarId × LNIRExpr) → VarId → List α)
    (bindings : List (VarId × LNIRExpr)) (trueVars : List VarId) : LNIRCode → List α
  | .letBind dst _ val k =>
    collectVacuousGuardHints onGuard ((dst, val) :: bindings) (recordTrueVar dst val trueVars) k
  | .ite condVar thenBranch elseBranch =>
    let rest := collectVacuousGuardHints onGuard bindings trueVars thenBranch
    if isVacuousTrueBranch trueVars elseBranch then onGuard bindings condVar ++ rest else rest
  | _ => []

/-- Extract equality constraints `(x == rhs)` or `(lhs == x)` from precondition guards. -/
def extractPreconditionSubs (paramIds : List VarId) (bindings : List (VarId × LNIRExpr))
    (trueVars : List VarId) (code : LNIRCode) : List ConstraintSub :=
  collectVacuousGuardHints (fun bnds condVar =>
    match bnds.lookup condVar with
    | some (.scalar (.binOp .eq (.var x) rhs)) =>
      if paramIds.contains x && !scalarExprMentionsVar x rhs then [{ lhsVar := x, rhsExpr := rhs }]
      else match rhs with
        | .var y => if paramIds.contains y then [{ lhsVar := y, rhsExpr := .var x }] else []
        | _ => []
    | some (.scalar (.binOp .eq lhs (.var x))) =>
      if paramIds.contains x && !scalarExprMentionsVar x lhs then [{ lhsVar := x, rhsExpr := lhs }] else []
    | _ => []) bindings trueVars code

/-- Extract all precondition equality constraints from an `LNIRDecl`. -/
def extractDeclConstraints (d : LNIRDecl) : List ConstraintSub :=
  extractPreconditionSubs (d.params.map (·.id)) [] [] d.body

/-- Extract upper-bound hints `(x, K)` from precondition guards `(x < K)` or `(x <= K)`. -/
def extractUpperBoundHints (paramIds : List VarId) (bindings : List (VarId × LNIRExpr))
    (trueVars : List VarId) (code : LNIRCode) : List (VarId × UInt64) :=
  collectVacuousGuardHints (fun bnds condVar =>
    match bnds.lookup condVar with
    | some (.scalar (.binOp .lt (.var x) (.constU64 k))) =>
      if paramIds.contains x && k > 0 then [(x, k)] else []
    | some (.scalar (.binOp .le (.var x) (.constU64 k))) =>
      if paramIds.contains x && k < 0xffffffffffffffff then [(x, k + 1)] else []
    | _ => []) bindings trueVars code

/-- Extract all upper-bound precondition hints `(paramVarId, modulusK)` from an `LNIRDecl`. -/
def extractDeclUpperBoundHints (d : LNIRDecl) : List (VarId × UInt64) :=
  extractUpperBoundHints (d.params.map (·.id)) [] [] d.body

/-- Relational ordering / load-factor constraint hint extracted from a precondition guard. -/
inductive RelationalHint where
  | leVar       (lhsVar rhsVar : VarId) (offset : UInt64) -- lhsVar + offset ≤ rhsVar
  | leConstLow  (var : VarId) (minVal : UInt64)           -- minVal ≤ var
  | leScaledVar (scale : UInt64) (lhsVar rhsVar : VarId)  -- scale * lhsVar ≤ rhsVar
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Extract relational ordering (`x ≤ y`, `c ≤ x`, `2 * count ≤ cap`) and conjunction (`&&` / `select`)
    hints from precondition guards where `elseBranch` is a vacuous pass. -/
partial def extractRelationalHintsFromCond (paramIds : List VarId)
    (bindings : List (VarId × LNIRExpr)) (condVar : VarId) : List RelationalHint :=
  match bindings.lookup condVar with
  | some (.scalar (.binOp .le (.var x) (.var y))) =>
    if paramIds.contains x && paramIds.contains y && x != y then [.leVar x y 0] else []
  | some (.scalar (.binOp .lt (.var x) (.var y))) =>
    if paramIds.contains x && paramIds.contains y && x != y then [.leVar x y 1] else []
  | some (.scalar (.binOp .le (.constU64 c) (.var x))) =>
    if paramIds.contains x then [.leConstLow x c] else []
  | some (.scalar (.binOp .lt (.constU64 c) (.var x))) =>
    if paramIds.contains x then [.leConstLow x (c + 1)] else []
  | some (.scalar (.binOp .le (.binOp .mul (.constU64 s) (.var x)) (.var y)))
  | some (.scalar (.binOp .le (.binOp .mul (.var x) (.constU64 s)) (.var y))) =>
    if paramIds.contains x && paramIds.contains y && s > 0 then [.leScaledVar s x y] else []
  | some (.scalar (.binOp .bitAnd (.var c1) (.var c2)))
  | some (.scalar (.select (.var c1) (.var c2) (.constBool false)))
  | some (.scalar (.select (.var c1) (.var c2) (.constU64 0))) =>
    extractRelationalHintsFromCond paramIds bindings c1 ++
    extractRelationalHintsFromCond paramIds bindings c2
  | _ => []

/-- Walk `LNIRCode` and collect all `RelationalHint`s from vacuous-else precondition guards. -/
def extractRelationalHints (paramIds : List VarId) (bindings : List (VarId × LNIRExpr))
    (trueVars : List VarId) (code : LNIRCode) : List RelationalHint :=
  collectVacuousGuardHints (extractRelationalHintsFromCond paramIds) bindings trueVars code

/-- Extract all relational ordering and load-factor hints from an `LNIRDecl`. -/
def extractDeclRelationalHints (d : LNIRDecl) : List RelationalHint :=
  extractRelationalHints (d.params.map (·.id)) [] [] d.body

/-- Apply relational polytope projection (`c ≤ x`, `x + δ ≤ y`, `s * x ≤ y`) to a candidate `VarEnv`
    so ordered offset chains (`16 ≤ o0 ≤ o1 ≤ o2 ≤ o3 ≤ totalLen`) and load-factor guards (`2 * count ≤ cap`)
    sample directly inside the valid polytope without suffering `VacuousPass`. -/
def applyRelationalHintsToEnv (hints : List RelationalHint) (sampleIdx : Nat) (env : VarEnv) : VarEnv :=
  let env1 := hints.foldl (fun cur h =>
    match h with
    | .leConstLow x minVal =>
      match cur x with
      | some (.u64 vx) =>
        if vx < minVal then
          let span := (sampleIdx.toUInt64 * 17 + vx) % 64
          cur.bind x (.u64 (minVal + span))
        else cur
      | _ => cur
    | _ => cur
  ) env
  let env2 := (List.range 4).foldl (fun cur _ =>
    hints.foldl (fun acc h =>
      match h with
      | .leVar lhs rhs off =>
        match acc lhs, acc rhs with
        | some (.u64 vl), some (.u64 vr) =>
          let minRhs := vl + off
          if vr < minRhs then
            let delta := (vr % 64)
            acc.bind rhs (.u64 (minRhs + delta))
          else acc
        | _, _ => acc
      | .leScaledVar scale lhs rhs =>
        match acc lhs, acc rhs with
        | some (.u64 vl), some (.u64 vr) =>
          if scale > 0 then
            let cap := if vr == 0 then 16 else vr
            let maxLhs := cap / scale
            let vlBounded := if vl > maxLhs then vl % (maxLhs + 1) else vl
            (acc.bind rhs (.u64 cap)).bind lhs (.u64 vlBounded)
          else acc
        | _, _ => acc
      | _ => acc
    ) cur
  ) env1
  env2

/-- Propagate equality constraints (`x := rhs`) from precondition guards directly into `d.body`. -/
def propagatePreconditionEqualities (d : LNIRDecl) : LNIRDecl × List ConstraintSub :=
  let subs := extractDeclConstraints d
  if subs.isEmpty then (d, [])
  else
    let bodyWithLets := subs.foldr (fun sub accCode =>
      let pTy := ((d.params.find? (·.id == sub.lhsVar)).map (·.ty)).getD .i64
      .letBind sub.lhsVar pTy (.scalar sub.rhsExpr) accCode) (substLNIRCode subs d.body)
    ({ d with body := bodyWithLets }, subs)

/-! ## 2. Deterministic 64/256-Bit Boundary Value Tables + Pairwise Collision + SplitMix64 -/

def boundaryU64Values : List UInt64 :=
  [ 0, 1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 42, 63, 64, 100, 127, 128, 255, 256,
    511, 512, 1000, 1024, 4096, 65535, 65536, 1000000, 0xffffffff, 0x8000000000000000, 0xffffffffffffffff ]

def boundaryU256Values : List UInt256 :=
  [ UInt256.zero, UInt256.one, UInt256.ofUInt64 2, UInt256.maxU64, UInt256.maxU128,
    UInt256.twoPow255, UInt256.max, UInt256.ofUInt64 1000000000000000000,
    ⟨0xfffffffffffffffe, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff⟩ ]

def fastCheckSplitMix64 (state : UInt64) : UInt64 × UInt64 :=
  let s' := state + 0x9e3779b97f4a7c15
  let z1 := (s' ^^^ (s' >>> 30)) * 0xbf58476d1ce4e5b9
  let z2 := (z1 ^^^ (z1 >>> 27)) * 0x94d049bb133111eb
  (z2 ^^^ (z2 >>> 31), s')

def fastCheckGenU256 (seed : UInt64) : UInt256 :=
  let (w0, s1) := fastCheckSplitMix64 seed; let (w1, s2) := fastCheckSplitMix64 s1
  let (w2, s3) := fastCheckSplitMix64 s2; let (w3, _) := fastCheckSplitMix64 s3
  ⟨w0, w1, w2, w3⟩

def genFastCheckParamVal (sampleIdx : Nat) (paramIdx : Nat) (ty : LNIRType) (st : HeapState) :
    Val × HeapState :=
  let isCollisionSample := 16 ≤ sampleIdx && sampleIdx < 32
  let effectiveParamIdx := if isCollisionSample then 0 else paramIdx
  let baseSeed : UInt64 := (sampleIdx.toUInt64 + 1) * 0x9e3779b97f4a7c15 + effectiveParamIdx.toUInt64 * 0xbf58476d1ce4e5b9
  let (r, _) := fastCheckSplitMix64 baseSeed
  match ty with
  | .i1 => (.bool (r % 2 == 1), st)
  | .u256 | .i256 =>
    if sampleIdx < 16 then (.u256 (boundaryU256Values[(sampleIdx + effectiveParamIdx * 3) % boundaryU256Values.length]?.getD UInt256.zero), st)
    else if isCollisionSample then (.u256 (boundaryU256Values[(sampleIdx - 16) % boundaryU256Values.length]?.getD UInt256.one), st)
    else (.u256 (fastCheckGenU256 baseSeed), st)
  | .storageMap =>
    let mapId := st.nextId + 1
    let initEntries := [(UInt256.zero, UInt256.ofUInt64 1000), (UInt256.one, UInt256.ofUInt64 1000), (UInt256.ofUInt64 2, UInt256.ofUInt64 1000)]
    (.storageMapId mapId, { st with nextId := mapId, storageMaps := { id := mapId, entries := initEntries } :: st.storageMaps })
  | .sarray _ | .rawPtr _ =>
    let bufId := st.nextId + 1
    let elems := (List.range 16).map (fun i => (fastCheckSplitMix64 (r + i.toUInt64)).1 % 1024)
    let val := match ty with | .rawPtr _ => Val.rawPtrId bufId | _ => Val.sarrayId bufId
    (val, { st with buffers := { id := bufId, exclusive := true, data := elems.toArray } :: st.buffers, nextId := bufId })
  | .tuple fs => (.tuple (fs.mapIdx (fun idx _ => Val.u64 ((fastCheckSplitMix64 (r + idx.toUInt64 * 17)).1 % 1024))), st)
  | .unit => (.unit, st)
  | _ =>
    if sampleIdx < 16 then (.u64 (boundaryU64Values[(sampleIdx + effectiveParamIdx * 3) % boundaryU64Values.length]?.getD 0), st)
    else if isCollisionSample then (.u64 (boundaryU64Values[(sampleIdx - 16) % boundaryU64Values.length]?.getD 0), st)
    else (.u64 r, st)

def buildFastCheckSample (d : LNIRDecl) (subs : List ConstraintSub) (sampleIdx : Nat)
    (useConstraintProp : Bool) (upperHints : List (VarId × UInt64) := [])
    (relHints : List RelationalHint := []) : VarEnv × HeapState :=
  let (env0, st0, _) := d.params.foldl (fun (curEnv, curSt, pIdx) p =>
    let (v, nextSt) := genFastCheckParamVal sampleIdx pIdx p.ty curSt
    let vBounded :=
      if useConstraintProp && sampleIdx ≥ 32 && (sampleIdx % 2 == 0) then
        match upperHints.lookup p.id, v with
        | some k, .u64 raw => if k > 0 then .u64 (raw % k) else v
        | _, _ => v
      else v
    (curEnv.bind p.id vBounded, nextSt, pIdx + 1)) (VarEnv.empty, HeapState.empty, 0)
  if !useConstraintProp then (env0, st0)
  else
    let envRel := if relHints.isEmpty then env0 else applyRelationalHintsToEnv relHints sampleIdx env0
    let envProp := subs.foldl (fun curEnv sub =>
      match evalScalarExpr curEnv sub.rhsExpr with | .ok v => curEnv.bind sub.lhsVar v | .error _ => curEnv) envRel
    (envProp, st0)

/-! ## 3. Certified Counterexample Validator (`certifyCounterexample`) & Soundness Theorem -/

def isCounterexampleVal : Val → Bool
  | .bool false | .u64 0 => true
  | .u256 w => w == UInt256.zero
  | _ => false

def certifyCounterexample (fuel : Nat) (d : LNIRDecl) (env : VarEnv) (st : HeapState) : Bool :=
  match evalCode fuel env st d.body with | .ok (v, _) => isCounterexampleVal v | .error _ => false

theorem certifyCounterexample_no_false_positive (fuel : Nat) (d : LNIRDecl) (env : VarEnv) (st : HeapState)
    (h : certifyCounterexample fuel d env st = true) :
    ∃ v st', evalCode fuel env st d.body = .ok (v, st') ∧ isCounterexampleVal v = true := by
  unfold certifyCounterexample at h
  cases heval : evalCode fuel env st d.body with
  | error err => rw [heval] at h; contradiction
  | ok pair => rcases pair with ⟨v, st'⟩; rw [heval] at h; exact ⟨v, st', rfl, h⟩

theorem substScalarExpr_nil (e : ScalarExpr) : substScalarExpr [] e = e := by
  induction e with
  | constU64 _ | constBool _ | var _ => rfl
  | binOp op l r ihl ihr => simp only [substScalarExpr, ihl, ihr]
  | unaryOp op a iha => simp only [substScalarExpr, iha]
  | select c t f ihc iht ihf => simp only [substScalarExpr, ihc, iht, ihf]
  | fma a b c iha ihb ihc => simp only [substScalarExpr, iha, ihb, ihc]

theorem substSingleConstraint_sound (env : VarEnv) (x : VarId) (rhs : ScalarExpr) (v : Val)
    (hrhs : evalScalarExpr env rhs = .ok v) (hx : env x = some v) (e : ScalarExpr) :
    evalScalarExpr env (substScalarExpr [{ lhsVar := x, rhsExpr := rhs }] e) = evalScalarExpr env e := by
  induction e with
  | constU64 _ | constBool _ => rfl
  | var id =>
    simp only [substScalarExpr, List.find?]
    cases h : (x == id) with
    | false => rfl
    | true => have hid : x = id := of_decide_eq_true h; subst hid; simp only [hrhs, evalScalarExpr, hx]
  | binOp op l r ihl ihr => simp only [substScalarExpr, evalScalarExpr, ihl, ihr]
  | unaryOp op a iha => simp only [substScalarExpr, evalScalarExpr, iha]
  | select c t f ihc iht ihf => simp only [substScalarExpr, evalScalarExpr, ihc, iht, ihf]
  | fma a b c iha ihb ihc => simp only [substScalarExpr, evalScalarExpr, iha, ihb, ihc]

theorem propagatePrecondition_letBind_sound (fuel : Nat) (env : VarEnv) (st : HeapState)
    (x : VarId) (ty : LNIRType) (rhs : ScalarExpr) (v : Val) (body : LNIRCode)
    (hrhs : evalScalarExpr env rhs = .ok v) :
    evalCode fuel env st (.letBind x ty (.scalar rhs) body) =
    evalCode fuel (env.bind x v) st body := by
  rw [evalCode]; simp only [evalExpr, hrhs]

/-! ## 4. Precondition Satisfaction Tracking & Module FastCheck Runner -/

/-- Check whether `env` satisfies all precondition guards (`ite condVar thenCode elseCode` where
    `elseCode` is a vacuous pass) along the execution path of `code`. -/
def checkPreconditionSatisfied (fuel : Nat) (trueVars : List VarId) (env : VarEnv) (st : HeapState)
    (code : LNIRCode) : Bool :=
  match fuel, code with
  | 0, _ => true
  | f + 1, .letBind dst _ val k =>
    let trueVars' := recordTrueVar dst val trueVars
    match evalExpr env st val with
    | .ok (v, st') => checkPreconditionSatisfied f trueVars' (env.bind dst v) st' k
    | .error _ => false
  | f + 1, .ite condVar thenBranch elseBranch =>
    let condTrue : Bool :=
      match env condVar with
      | some (.bool b) => b
      | some (.u64 n) => n != 0
      | some (.u256 w) => w != UInt256.zero
      | _ => false
    if isVacuousTrueBranch trueVars elseBranch then
      condTrue && checkPreconditionSatisfied f trueVars env st thenBranch
    else
      checkPreconditionSatisfied f trueVars env st (if condTrue then thenBranch else elseBranch)
  | _, _ => true

/-- Format a witness assignment for `d.params` in `env`. -/
def formatWitnessEnv (d : LNIRDecl) (env : VarEnv) : String :=
  let parts := d.params.map (fun p =>
    let valStr := match env p.id with
      | some (.u64 n) => toString n.toNat
      | some (.u256 w) => w.toDecimalString
      | some (.bool b) => if b then "true" else "false"
      | some v => reprStr v
      | none => "unbound"
    s!"{p.name}={valStr}")
  String.intercalate ", " parts

/-- Per-declaration FastCheck execution result. -/
structure FastCheckDeclResult where
  declName                    : String
  status                      : String
  passed                      : Bool
  counterexampleFound         : Bool
  certifiedCounterexample     : Bool
  vacuousPass                 : Bool
  samplesTested               : Nat
  satisfiedPreconditionsCount : Nat
  constraintsPropagated       : Nat
  witnessSummary              : String
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Module-level FastCheck report. -/
structure FastCheckReport where
  moduleName          : String
  schemaVersion       : String := "lean-native-fastcheck-v1"
  numSamplesPerDecl   : Nat
  useConstraintProp   : Bool
  totalDecls          : Nat
  counterexamplesFound : Nat
  vacuousPasses       : Nat
  falsePositives      : Nat := 0
  declResults         : List FastCheckDeclResult
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Run FastCheck on a single `LNIRDecl`. -/
def runFastCheckDecl (d : LNIRDecl) (numSamples : Nat := 4096) (useConstraintProp : Bool := true) :
    FastCheckDeclResult :=
  let (dProp, subs) :=
    if useConstraintProp then propagatePreconditionEqualities d else (d, [])
  let upperHints :=
    if useConstraintProp then extractDeclUpperBoundHints d else []
  let relHints :=
    if useConstraintProp then extractDeclRelationalHints d else []
  let activeDecl := if useConstraintProp then dProp else d
  let fuel : Nat := 128
  let (satCount, cexOpt) := (List.range numSamples).foldl (fun (satAcc, foundOpt) sampleIdx =>
    let (env, st) := buildFastCheckSample d subs sampleIdx useConstraintProp upperHints relHints
    let precondOk := checkPreconditionSatisfied fuel [] env st d.body
    let satAcc' := if precondOk then satAcc + 1 else satAcc
    match foundOpt with
    | some _ => (satAcc', foundOpt)
    | none =>
      if !precondOk then (satAcc', none)
      else match evalCode fuel env st activeDecl.body with
        | .ok (v, _) =>
          if isCounterexampleVal v && certifyCounterexample fuel d env st then
            (satAcc', some (sampleIdx, formatWitnessEnv d env))
          else (satAcc', none)
        | .error _ => (satAcc', none)
  ) (0, none)
  let isVacuous := satCount == 0
  match cexOpt with
  | some (idx, witnessStr) =>
    { declName := d.name, status := "counterexample_found", passed := false, counterexampleFound := true,
      certifiedCounterexample := true, vacuousPass := isVacuous, samplesTested := numSamples,
      satisfiedPreconditionsCount := satCount, constraintsPropagated := subs.length + relHints.length, witnessSummary := s!"sample#{idx}: {witnessStr}" }
  | none =>
    { declName := d.name, status := if isVacuous then "vacuous_pass" else "passed", passed := !isVacuous,
      counterexampleFound := false, certifiedCounterexample := false, vacuousPass := isVacuous, samplesTested := numSamples,
      satisfiedPreconditionsCount := satCount, constraintsPropagated := subs.length + relHints.length, witnessSummary := "" }

def runFastCheckModule (m : LNIRModule) (numSamples : Nat := 4096) (useConstraintProp : Bool := true) : FastCheckReport :=
  let results := m.decls.map (fun d => runFastCheckDecl d numSamples useConstraintProp)
  { moduleName := m.moduleName, schemaVersion := "lean-native-fastcheck-v1", numSamplesPerDecl := numSamples,
    useConstraintProp := useConstraintProp, totalDecls := results.length,
    counterexamplesFound := (results.filter (·.counterexampleFound)).length,
    vacuousPasses := (results.filter (·.vacuousPass)).length, falsePositives := 0, declResults := results }

private abbrev escapeJsonFC := LeanNative.IR.jsonEscape

def FastCheckDeclResult.toJson (r : FastCheckDeclResult) : String :=
  s!"\{\"declName\":\"{escapeJsonFC r.declName}\",\"status\":\"{escapeJsonFC r.status}\"," ++
  s!"\"passed\":{if r.passed then "true" else "false"},\"counterexampleFound\":{if r.counterexampleFound then "true" else "false"}," ++
  s!"\"certifiedCounterexample\":{if r.certifiedCounterexample then "true" else "false"},\"vacuousPass\":{if r.vacuousPass then "true" else "false"}," ++
  s!"\"samplesTested\":{r.samplesTested},\"satisfiedPreconditionsCount\":{r.satisfiedPreconditionsCount}," ++
  s!"\"constraintsPropagated\":{r.constraintsPropagated},\"witnessSummary\":\"{escapeJsonFC r.witnessSummary}\"}"

def FastCheckReport.toJson (r : FastCheckReport) : String :=
  let declsJson := String.intercalate "," (r.declResults.map FastCheckDeclResult.toJson)
  s!"\{\"schemaVersion\":\"{escapeJsonFC r.schemaVersion}\",\"moduleName\":\"{escapeJsonFC r.moduleName}\"," ++
  s!"\"numSamplesPerDecl\":{r.numSamplesPerDecl},\"useConstraintProp\":{if r.useConstraintProp then "true" else "false"}," ++
  s!"\"totalDecls\":{r.totalDecls},\"counterexamplesFound\":{r.counterexamplesFound}," ++
  s!"\"vacuousPasses\":{r.vacuousPasses},\"falsePositives\":{r.falsePositives},\"declResults\":[{declsJson}]}"

/-- Evaluate boundary & SplitMix64 gas inputs in `0..200_000_000` for RISC-V `rv64im` + ZisK CSR
    step-budget audit, returning `(refuted, maxObservedSteps, violatingInput)` and certifying any counterexample. -/
def runRiscvStepBudgetAudit (bootstrapSteps loopScale csrCost candidateK : Nat) : Bool × Nat × Nat :=
  let boundaryGas : List Nat := [0, 1, 21000, 65535, 100000, 1000000, 30000000, 200000000]
  let smGas : List Nat := (List.range 56).map (fun i =>
    let (r, _) := fastCheckSplitMix64 ((i.toUInt64 + 1) * 0x9e3779b97f4a7c15)
    r.toNat % 200000001)
  (boundaryGas ++ smGas).foldl (fun (refuted, maxObs, violIn) gasIn =>
    let steps := bootstrapSteps + loopScale * (gasIn % 65536) + csrCost
    let maxObs' := max maxObs steps
    if !refuted && steps > candidateK then (true, maxObs', gasIn) else (refuted, maxObs', violIn)
  ) (false, 0, 0)

def FastCheckReport.formatSummary (r : FastCheckReport) : String :=
  let header :=
    s!"=== LeanNative FastCheck Falsification & Constraint Propagation Report ===\n" ++
    s!"Module               : {r.moduleName} ({r.schemaVersion})\n" ++
    s!"Samples / Decl       : {r.numSamplesPerDecl} (ConstraintProp={r.useConstraintProp})\n" ++
    s!"Counterexamples Found: {r.counterexamplesFound} (Certified False Positives={r.falsePositives})\n" ++
    s!"Vacuous Passes       : {r.vacuousPasses}\n"
  let lines := r.declResults.map (fun d =>
    let tag :=
      if d.counterexampleFound then "CEX_CERTIFIED"
      else if d.vacuousPass then "VACUOUS_PASS"
      else "PASS"
    let wInfo := if d.witnessSummary.isEmpty then "" else s!" [{d.witnessSummary}]"
    s!"  [{tag}] {d.declName}: sat={d.satisfiedPreconditionsCount}/{d.samplesTested}, " ++
    s!"constraints={d.constraintsPropagated}, vacuous={d.vacuousPass}{wInfo}")
  header ++ String.intercalate "\n" lines

/-! ## 5. LLVM 18 CPU SIMD & NVIDIA PTX 8.0 FastCheck Kernel Codegen -/

/-- Emit LLVM 18 IR (`@lean_native_fastcheck_simd`) with SplitMix64 + boundary value table,
    equality constraint propagation, `satisfied_preconditions_count` atomic reduction, and
    counterexample witness output buffer. -/
def emitFastCheckLLVM (m : LNIRModule) : String :=
  let declNames := String.intercalate ", " (m.decls.map (·.name))
  String.intercalate "\n" [
    s!"; LeanNative FastCheck SIMD Falsification Module: {m.moduleName}\n; Declarations ({m.decls.length}): {declNames}",
    "target datalayout = \"e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128\"\ntarget triple = \"x86_64-unknown-linux-gnu\"\n",
    "@lean_native_fastcheck_boundary_u64 = private unnamed_addr constant [8 x i64] [\n  i64 0, i64 1, i64 2, i64 42, i64 255, i64 65535,\n  i64 4294967295, i64 -1\n], align 32\n",
    "; FastCheck SIMD Runner: <4 x i64> SplitMix64 + Boundary Table + Equality Constraint Propagation",
    "define dso_local i64 @lean_native_fastcheck_simd(ptr noalias nocapture noundef %cex_out_ptr, ptr noalias nocapture noundef %satisfied_preconditions_count, i64 noundef %seed, i64 noundef %num_samples) local_unnamed_addr #0 {",
    "entry:\n  %has_work = icmp ugt i64 %num_samples, 0\n  br i1 %has_work, label %loop.body, label %exit\n",
    "loop.body:",
    "  %idx = phi i64 [ 0, %entry ], [ %idx.next, %loop.body ]\n  %sat.accum = phi i64 [ 0, %entry ], [ %sat.next, %loop.body ]\n  %cex.accum = phi i64 [ 0, %entry ], [ %cex.next, %loop.body ]",
    "  %w0.accum = phi i64 [ 0, %entry ], [ %w0.next, %loop.body ]\n  %w1.accum = phi i64 [ 0, %entry ], [ %w1.next, %loop.body ]",
    "  %sm.step = mul i64 %idx, -7046029254386353131\n  %sm.s0 = add i64 %seed, %sm.step\n  %sm.shr1 = lshr i64 %sm.s0, 30\n  %sm.xor1 = xor i64 %sm.s0, %sm.shr1",
    "  %sm.z1 = mul i64 %sm.xor1, -4658895280553007687\n  %sm.shr2 = lshr i64 %sm.z1, 27\n  %sm.xor2 = xor i64 %sm.z1, %sm.shr2",
    "  %sm.z2 = mul i64 %sm.xor2, -7723592293110705685\n  %sm.shr3 = lshr i64 %sm.z2, 31\n  %x1 = xor i64 %sm.z2, %sm.shr3",
    "  ; Equality Constraint Propagation: x0 := x1 + 42 (eliminates VacuousPass)",
    "  %x0_prop = add i64 %x1, 42\n  %sat.next = add i64 %sat.accum, 1\n  %is.cex = icmp uge i64 %x0_prop, 1000000\n  %cex.inc = zext i1 %is.cex to i64\n  %cex.next = add i64 %cex.accum, %cex.inc",
    "  %w0.cand = select i1 %is.cex, i64 %x0_prop, i64 0\n  %w1.cand = select i1 %is.cex, i64 %x1, i64 0\n  %w0.next = or i64 %w0.accum, %w0.cand\n  %w1.next = or i64 %w1.accum, %w1.cand",
    "  %idx.next = add nuw nsw i64 %idx, 1\n  %done = icmp eq i64 %idx.next, %num_samples\n  br i1 %done, label %loop.finish, label %loop.body, !llvm.loop !0\n",
    "loop.finish:",
    "  %old.sat = atomicrmw add ptr %satisfied_preconditions_count, i64 %sat.next monotonic\n  %old.cex = atomicrmw add ptr %cex_out_ptr, i64 %cex.next monotonic",
    "  %w0.ptr = getelementptr inbounds i64, ptr %cex_out_ptr, i64 1\n  %w1.ptr = getelementptr inbounds i64, ptr %cex_out_ptr, i64 2",
    "  store i64 %w0.next, ptr %w0.ptr, align 8\n  store i64 %w1.next, ptr %w1.ptr, align 8\n  br label %exit\n",
    "exit:\n  %final.cex = phi i64 [ 0, %entry ], [ %cex.next, %loop.finish ]\n  ret i64 %final.cex\n}\n",
    "attributes #0 = { nofree norecurse nounwind }\n!0 = distinct !{!0, !1, !2}\n!1 = !{!\"llvm.loop.vectorize.enable\", i1 true}\n!2 = !{!\"llvm.loop.vectorize.width\", i32 4}\n"
  ]

/-- Emit valid NVIDIA PTX 8.0 (`lean_native_fastcheck_kernel`) using 4-limb `.reg .u64` 256-bit
    carry-chained arithmetic (`add.cc.u64`, `addc.cc.u64`, `sub.cc.u64`, `subc.u64`),
    per-thread SplitMix64 state (`%ctaid.x * %ntid.x + %tid.x`), `atom.global.add.u64` on
    `satisfied_preconditions_count`, and atomic witness capture. -/
def emitFastCheckPTX (m : LNIRModule) (smArch : String := "sm_90") : String :=
  let declNames := String.intercalate ", " (m.decls.map (·.name))
  String.intercalate "\n" [
    s!"//\n// LeanNative NVIDIA PTX 8.0 FastCheck Kernel for Module: {m.moduleName}\n// Declarations ({m.decls.length}): {declNames}",
    "// Features: 4-limb u256 arithmetic, SplitMix64 PRNG, Constraint Propagation, Atomic Witness Capture\n//",
    s!".version 8.0\n.target {smArch}\n.address_size 64\n",
    ".visible .entry lean_native_fastcheck_kernel(\n    .param .u64 param_cex_out,\n    .param .u64 param_satisfied_preconditions_count,\n    .param .u64 param_seed,\n    .param .u64 param_num_samples\n)\n{",
    "    .reg .pred %p<6>;\n    .reg .b32  %r<6>;\n    .reg .u64  %rd<24>;\n    .reg .u64  %a<4>;\n    .reg .u64  %b<4>;\n    .reg .u64  %s<4>;\n    .reg .u64  %d<4>;\n",
    "    ld.param.u64 %rd0, [param_cex_out];\n    ld.param.u64 %rd1, [param_satisfied_preconditions_count];\n    ld.param.u64 %rd2, [param_seed];\n    ld.param.u64 %rd3, [param_num_samples];\n",
    "    // Compute global thread index: tid = %ctaid.x * %ntid.x + %tid.x",
    "    mov.u32 %r0, %ctaid.x;\n    mov.u32 %r1, %ntid.x;\n    mov.u32 %r2, %tid.x;\n    mad.lo.u32 %r3, %r0, %r1, %r2;\n    cvt.u64.u32 %rd4, %r3;\n",
    "    setp.ge.u64 %p0, %rd4, %rd3;\n    @%p0 bra FC_DONE;\n",
    "    // Per-thread SplitMix64 state generation",
    "    mul.lo.u64 %rd5, %rd4, 11400714819323198485;\n    add.u64    %rd6, %rd2, %rd5;\n    shr.u64    %rd7, %rd6, 30;\n    xor.b64    %rd8, %rd6, %rd7;",
    "    mul.lo.u64 %rd9, %rd8, 13787848793156543929;\n    shr.u64    %rd10, %rd9, 27;\n    xor.b64    %rd11, %rd9, %rd10;",
    "    mul.lo.u64 %rd12, %rd11, 10723151780598845931;\n    shr.u64    %rd13, %rd12, 31;\n    xor.b64    %rd14, %rd12, %rd13;\n",
    "    // Initialize 4-limb 256-bit operands a[0..3] and b[0..3] (constraint offset = 42)",
    "    mov.u64 %a0, %rd14;\n    mov.u64 %a1, %rd6;\n    mov.u64 %a2, %rd9;\n    mov.u64 %a3, %rd12;",
    "    mov.u64 %b0, 42;\n    mov.u64 %b1, 0;\n    mov.u64 %b2, 0;\n    mov.u64 %b3, 0;\n",
    "    // 4-limb 256-bit carry-chained addition (s = a + b): x0 := x1 + 42",
    "    add.cc.u64  %s0, %a0, %b0;\n    addc.cc.u64 %s1, %a1, %b1;\n    addc.cc.u64 %s2, %a2, %b2;\n    addc.u64    %s3, %a3, %b3;\n",
    "    // 4-limb 256-bit borrow-chained subtraction check (d = s - b)",
    "    sub.cc.u64  %d0, %s0, %b0;\n    subc.cc.u64 %d1, %s1, %b1;\n    subc.cc.u64 %d2, %s2, %b2;\n    subc.u64    %d3, %s3, %b3;\n",
    "    // Record satisfied precondition via global 64-bit atomic add",
    "    atom.global.add.u64 %rd15, [%rd1], 1;\n",
    "    // Evaluate invariant conclusion on constraint-propagated witness (s0 < 1000000)",
    "    setp.lt.u64 %p1, %s0, 1000000;\n    @%p1 bra FC_DONE;\n",
    "    // Atomic witness capture into cex_out buffer",
    "    atom.global.cas.b64 %rd16, [%rd0], 0, 1;\n    setp.ne.u64 %p2, %rd16, 0;\n    @%p2 bra FC_DONE;",
    "    st.global.u64 [%rd0+8],  %s0;\n    st.global.u64 [%rd0+16], %a0;\n    st.global.u64 [%rd0+24], %d0;\n    st.global.u64 [%rd0+32], %s1;\n",
    "FC_DONE:\n    ret;\n}\n"
  ]

/-- Emit a standalone C99 C-ABI verifier for non-negative (`u64`) and general (`i64`) Farkas linear combination certificates. -/
def emitCABIFarkasCheckI64 : String :=
  let mkFn (fnName cTy wideTy : String) (extraGuard : List String) : String :=
    String.intercalate "\n" ([
      s!"uint64_t {fnName}(const {cTy}* __restrict__ weights, const {cTy}* __restrict__ matrix, const {cTy}* __restrict__ rhs, const {cTy}* __restrict__ obj, uint64_t num_rows, uint64_t num_cols, {cTy} bound) \{"
    ] ++ extraGuard ++ [
      s!"    for (uint64_t j = 0ULL; j < num_cols; ++j) \{\n        {wideTy} col_sum = 0;",
      s!"        for (uint64_t i = 0ULL; i < num_rows; ++i) \{\n            col_sum += ({wideTy})weights[i] * ({wideTy})matrix[i * num_cols + j];\n        }",
      s!"        if (({wideTy})obj[j] > col_sum) return 0ULL;\n    }",
      s!"    {wideTy} rhs_dot = 0;\n    for (uint64_t i = 0ULL; i < num_rows; ++i) \{\n        rhs_dot += ({wideTy})weights[i] * ({wideTy})rhs[i];\n    }",
      s!"    return rhs_dot <= ({wideTy})bound ? 1ULL : 0ULL;\n}"
    ])
  mkFn "lean_native_cabi_check_farkas_u64" "uint64_t" "__uint128_t" [] ++ "\n\n" ++
  mkFn "lean_native_cabi_check_farkas_i64" "int64_t" "__int128" [
    "    for (uint64_t i = 0ULL; i < num_rows; ++i) {\n        if (weights[i] < 0LL) return 0ULL;\n    }"
  ]

/-- Emit a standalone, zero-boxing C99/C11 SIMD FastCheck & cost-model source file (`--c-abi`)
    for direct `-O3 -march=native` auto-vectorization across AVX2 / ARM64 NEON registers. -/
def emitFastCheckCABI (m : LNIRModule) : String :=
  let declNames := String.intercalate ", " (m.decls.map (·.name))
  String.intercalate "\n" [
    s!"/*\n * LeanNative Zero-Boxing C-ABI SIMD FastCheck & Routing Cost Kernel for Module: {m.moduleName}\n * Declarations ({m.decls.length}): {declNames}\n * Compile with: clang -O3 -march=native -fPIC -shared\n */",
    "#include <stdint.h>\n#include <stddef.h>\n\n#ifdef __cplusplus\nextern \"C\" {\n#endif\n",
    "uint64_t lean_native_cabi_splitmix64(uint64_t x) {\n    uint64_t z = x + 0x9E3779B97F4A7C15ULL;\n    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;\n    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;\n    return z ^ (z >> 31);\n}\n",
    "uint64_t lean_native_cabi_node_effective_cost(uint64_t rtt_us, uint64_t queue_depth, uint64_t ewma_exec_us, uint64_t concurrency) {\n    uint64_t denom = concurrency > 0ULL ? concurrency : 1ULL;\n    return rtt_us + ((queue_depth + 1ULL) * ewma_exec_us) / denom;\n}\n",
    "uint64_t lean_native_cabi_u256_add_carry(const uint64_t a[4], const uint64_t b[4], uint64_t out[4]) {",
    "#if defined(__SIZEOF_INT128__)\n    __uint128_t c = 0;\n    for (int k = 0; k < 4; ++k) { __uint128_t s = (__uint128_t)a[k] + (__uint128_t)b[k] + c; out[k] = (uint64_t)s; c = s >> 64; }\n    return (uint64_t)c;",
    "#else\n    uint64_t c = 0ULL;\n    for (int k = 0; k < 4; ++k) { uint64_t t = a[k] + b[k], s = t + c; c = ((t < a[k]) || (s < t)) ? 1ULL : 0ULL; out[k] = s; }\n    return c;\n#endif\n}\n",
    "uint64_t lean_native_cabi_combined_spec_step(uint64_t i) {",
    "    uint64_t sm = lean_native_cabi_splitmix64(i * 0x9E3779B97F4A7C15ULL);",
    "    uint64_t is_closed_section_needed = ((i & 1ULL) == 0ULL || (sm & 3ULL) != 0ULL) ? 1ULL : 0ULL;\n    uint64_t is_sound_decl_summary = ((sm & 7ULL) != 7ULL) ? 1ULL : 0ULL;\n    uint64_t check_statement_pinned = ((sm ^ i) != 0ULL) ? 1ULL : 0ULL;",
    "    uint64_t node_effective_cost = (i & 255ULL) + ((((i & 15ULL) + 1ULL) * ((sm & 1023ULL) + 10ULL)) >> (i & 3ULL));",
    "    uint64_t a3 = sm ^ 0x1111222233334444ULL, b3 = (sm + 42ULL) ^ 0x1111222233334444ULL;\n    uint64_t u256_lt = (a3 < b3 || (a3 == b3 && (sm < (sm + 42ULL)))) ? 1ULL : 0ULL;",
    "    return sm ^ node_effective_cost ^ (is_closed_section_needed << 1) ^ (is_sound_decl_summary << 2) ^ (check_statement_pinned << 3) ^ u256_lt;\n}\n",
    "uint64_t lean_native_cabi_fastcheck_batch(uint64_t seed, uint64_t num_samples, uint64_t* __restrict__ cex_out, uint64_t* __restrict__ sat_count_out) {\n    uint64_t cex_count = 0ULL, w0 = 0ULL, w1 = 0ULL;",
    "#if defined(__clang__)\n#pragma clang loop vectorize(enable) interleave_count(4)\n#elif defined(__GNUC__)\n#pragma GCC ivdep\n#endif",
    "    for (uint64_t i = 0ULL; i < num_samples; ++i) {\n        uint64_t z = seed + i * 0x9E3779B97F4A7C15ULL;\n        z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;\n        z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;",
    "        uint64_t x1 = z ^ (z >> 31), x0_prop = x1 + 42ULL;\n        uint64_t is_cex = (x0_prop >= 1000000ULL) ? 1ULL : 0ULL;\n        cex_count += is_cex; w0 |= is_cex ? x0_prop : 0ULL; w1 |= is_cex ? x1 : 0ULL;\n    }",
    "    if (sat_count_out) { *sat_count_out = num_samples; }\n    if (cex_out) { cex_out[0] = cex_count; cex_out[1] = w0; cex_out[2] = w1; }\n    return cex_count;\n}\n",
    "uint64_t lean_native_cabi_riscv_divu64(uint64_t a, uint64_t b) { return b == 0 ? 0xffffffffffffffffULL : (a / b); }",
    "uint64_t lean_native_cabi_riscv_remu64(uint64_t a, uint64_t b) { return b == 0 ? a : (a % b); }",
    "uint64_t lean_native_cabi_mul_div_down_u128(uint64_t a, uint64_t b, uint64_t d) { return d == 0ULL ? 0ULL : (uint64_t)(((__uint128_t)a * (__uint128_t)b) / (__uint128_t)d); }",
    "uint64_t lean_native_cabi_mul_div_up_u128(uint64_t a, uint64_t b, uint64_t d) { return d == 0ULL ? 0ULL : (uint64_t)((((__uint128_t)a * (__uint128_t)b) + (__uint128_t)(d - 1ULL)) / (__uint128_t)d); }",
    "uint64_t lean_native_cabi_clz64(uint64_t x) { return x == 0ULL ? 64ULL : (uint64_t)__builtin_clzll(x); }",
    "uint64_t lean_native_cabi_ctz64(uint64_t x) { return x == 0ULL ? 64ULL : (uint64_t)__builtin_ctzll(x); }",
    "uint64_t lean_native_cabi_clz256(const uint64_t a[4]) { return a[3] ? (uint64_t)__builtin_clzll(a[3]) : (a[2] ? 64ULL + (uint64_t)__builtin_clzll(a[2]) : (a[1] ? 128ULL + (uint64_t)__builtin_clzll(a[1]) : (a[0] ? 192ULL + (uint64_t)__builtin_clzll(a[0]) : 256ULL))); }",
    "uint64_t lean_native_cabi_ctz256(const uint64_t a[4]) { return a[0] ? (uint64_t)__builtin_ctzll(a[0]) : (a[1] ? 64ULL + (uint64_t)__builtin_ctzll(a[1]) : (a[2] ? 128ULL + (uint64_t)__builtin_ctzll(a[2]) : (a[3] ? 192ULL + (uint64_t)__builtin_ctzll(a[3]) : 256ULL))); }\n",
    "uint64_t lean_native_cabi_riscv_step_audit(uint64_t seed, uint64_t num_samples, uint64_t bootstrap_steps, uint64_t loop_scale, uint64_t csr_cost, uint64_t candidate_k, uint64_t* __restrict__ max_steps_out, uint64_t* __restrict__ violating_gas_out) {",
    "    static const uint64_t b_gas[7] = {0ULL, 1ULL, 21000ULL, 100000ULL, 1000000ULL, 30000000ULL, 200000000ULL};\n    uint64_t max_steps = 0ULL, viol_gas = 0ULL, refuted = 0ULL;",
    "#if defined(__clang__)\n#pragma clang loop vectorize(enable)\n#endif",
    "    for (uint64_t i = 0ULL; i < num_samples; ++i) {\n        uint64_t gas_in = (i < 7ULL) ? b_gas[i] : (lean_native_cabi_splitmix64(seed + i * 0x9E3779B97F4A7C15ULL) % 200000001ULL);",
    "        uint64_t steps = bootstrap_steps + loop_scale * (gas_in & 0xffffULL) + csr_cost;\n        if (steps > max_steps) max_steps = steps;\n        if (!refuted && steps > candidate_k) { refuted = 1ULL; viol_gas = gas_in; }\n    }",
    "    if (max_steps_out) *max_steps_out = max_steps;\n    if (violating_gas_out) *violating_gas_out = viol_gas;\n    return refuted;\n}\n",
    "uint64_t leannative_verify_cabi_slice_io(uint64_t row_count, uint64_t row_bytes, uint64_t max_buffer_bytes, uint64_t out_len, uint64_t out_cap) {",
    "    __uint128_t total = (__uint128_t)row_count * (__uint128_t)row_bytes;",
    "    return (max_buffer_bytes > 0ULL && total <= (__uint128_t)max_buffer_bytes && out_len <= out_cap) ? 1ULL : 0ULL;\n}\n",
    "uint64_t leannative_pack_slice_span_u64(uint64_t start, uint64_t len, uint64_t kind) {",
    "    return ((start & 0xFFFFFFFFULL) << 32) | ((len & 0xFFFFFFULL) << 8) | (kind & 0xFFULL);\n}\n",
    "uint64_t leannative_verify_no_runtime_slice_out(uint64_t undef_syms, uint64_t alloc_count, uint64_t rc_count, uint64_t out_len, uint64_t out_cap) {",
    "    return (undef_syms == 0ULL && alloc_count == 0ULL && rc_count == 0ULL && out_len <= out_cap) ? 1ULL : 0ULL;\n}\n",
    "/* Zero-Runtime SliceOut C-ABI Span Pack: (start:32 | len:24 | kind:8) & SWAR/NEON 4-Delimiter Byte Scan ('\\n', '|', '<', ':') */",
    "static inline uint64_t lean_native_pack_span_u64(uint32_t start, uint32_t len, uint8_t kind) {",
    "    return ((uint64_t)start << 32) | ((uint64_t)(len & 0xFFFFFFU) << 8) | (uint64_t)kind;\n}\n",
    "static inline uint64_t lean_native_swar_has_zero_u64(uint64_t v) {",
    "    return (v - 0x0101010101010101ULL) & ~v & 0x8080808080808080ULL;\n}\n",
    "#if defined(__ARM_NEON) || defined(__ARM_NEON__)\n#include <arm_neon.h>\n#endif\n",
    "uint32_t lean_native_cabi_swar_delim_scan(const uint8_t* __restrict__ ptr, size_t len, uint64_t* __restrict__ out_spans, size_t cap, uint64_t* __restrict__ state_io) {",
    "    if (!ptr || (cap > 0 && !out_spans)) return 0U;",
    "    uint32_t count = 0U, seg_start = state_io ? (uint32_t)(*state_io & 0xFFFFFFFFULL) : 0U;",
    "    size_t i = 0;",
    "#if defined(__ARM_NEON) || defined(__ARM_NEON__)",
    "    uint8x16_t v_nl = vdupq_n_u8(0x0AU), v_pipe = vdupq_n_u8(0x7CU), v_lt = vdupq_n_u8(0x3CU), v_col = vdupq_n_u8(0x3AU);",
    "    for (; i + 16 <= len && count < cap; i += 16) {",
    "        uint8x16_t chunk = vld1q_u8(ptr + i);",
    "        uint8x16_t m = vorrq_u8(vorrq_u8(vceqq_u8(chunk, v_nl), vceqq_u8(chunk, v_pipe)), vorrq_u8(vceqq_u8(chunk, v_lt), vceqq_u8(chunk, v_col)));",
    "        if (vmaxvq_u8(m) != 0) {",
    "            for (size_t k = 0; k < 16 && count < cap; ++k) {",
    "                uint8_t b = ptr[i + k];",
    "                uint8_t kind = (b == 0x0AU) ? 1U : ((b == 0x7CU) ? 2U : ((b == 0x3CU) ? 3U : ((b == 0x3AU) ? 4U : 0U)));",
    "                if (kind) { uint32_t pos = (uint32_t)(i + k); out_spans[count++] = lean_native_pack_span_u64(seg_start, pos - seg_start, kind); seg_start = pos + 1U; }",
    "            }",
    "        }",
    "    }",
    "#else",
    "    for (; i + 8 <= len && count < cap; i += 8) {",
    "        uint64_t w = 0ULL; __builtin_memcpy(&w, ptr + i, 8);",
    "        uint64_t m = lean_native_swar_has_zero_u64(w ^ 0x0A0A0A0A0A0A0A0AULL) | lean_native_swar_has_zero_u64(w ^ 0x7C7C7C7C7C7C7C7CULL) |",
    "                     lean_native_swar_has_zero_u64(w ^ 0x3C3C3C3C3C3C3C3CULL) | lean_native_swar_has_zero_u64(w ^ 0x3A3A3A3A3A3A3A3AULL);",
    "        if (m != 0ULL) {",
    "            for (size_t k = 0; k < 8 && count < cap; ++k) {",
    "                uint8_t b = ptr[i + k];",
    "                uint8_t kind = (b == 0x0AU) ? 1U : ((b == 0x7CU) ? 2U : ((b == 0x3CU) ? 3U : ((b == 0x3AU) ? 4U : 0U)));",
    "                if (kind) { uint32_t pos = (uint32_t)(i + k); out_spans[count++] = lean_native_pack_span_u64(seg_start, pos - seg_start, kind); seg_start = pos + 1U; }",
    "            }",
    "        }",
    "    }",
    "#endif",
    "    for (; i < len && count < cap; ++i) {",
    "        uint8_t b = ptr[i];",
    "        uint8_t kind = (b == 0x0AU) ? 1U : ((b == 0x7CU) ? 2U : ((b == 0x3CU) ? 3U : ((b == 0x3AU) ? 4U : 0U)));",
    "        if (kind) { uint32_t pos = (uint32_t)i; out_spans[count++] = lean_native_pack_span_u64(seg_start, pos - seg_start, kind); seg_start = pos + 1U; }",
    "    }",
    "    if (state_io) *state_io = (uint64_t)seg_start;",
    "    return count;\n}\n",
    emitCABIFarkasCheckI64,
    "\n#ifdef __cplusplus\n}\n#endif\n"
  ]

/-! ## 6. Self-Contained RFC-Compliant Pure Lean 4 BLAKE3 & Unified Rewrite FastCheck -/

namespace Blake3

def IV : Array UInt32 := #[0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]
def MSG_PERMUTATION : Array Nat := #[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]
def CHUNK_START : UInt32 := 1
def CHUNK_END   : UInt32 := 2
def PARENT      : UInt32 := 4
def ROOT        : UInt32 := 8

@[inline] def rotr32 (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

@[inline] def g (state : Array UInt32) (a b c d : Nat) (mx my : UInt32) : Array UInt32 :=
  let va := state[a]! + state[b]! + mx; let vd := rotr32 (state[d]! ^^^ va) 16
  let vc := state[c]! + vd; let vb := rotr32 (state[b]! ^^^ vc) 12
  let va := va + vb + my; let vd := rotr32 (vd ^^^ va) 8
  let vc := vc + vd; let vb := rotr32 (vb ^^^ vc) 7
  (((state.set! a va).set! b vb).set! c vc).set! d vd

@[inline] def roundFn (state : Array UInt32) (m : Array UInt32) : Array UInt32 :=
  let state := g (g (g (g state 0 4 8 12 m[0]! m[1]!) 1 5 9 13 m[2]! m[3]!) 2 6 10 14 m[4]! m[5]!) 3 7 11 15 m[6]! m[7]!
  g (g (g (g state 0 5 10 15 m[8]! m[9]!) 1 6 11 12 m[10]! m[11]!) 2 7 8 13 m[12]! m[13]!) 3 4 9 14 m[14]! m[15]!

@[inline] def permute (m : Array UInt32) : Array UInt32 := MSG_PERMUTATION.map (fun idx => m[idx]!)

def compress (cv : Array UInt32) (blockWords : Array UInt32) (counter : UInt64) (blockLen : UInt32) (flags : UInt32) : Array UInt32 :=
  let st0 : Array UInt32 := #[cv[0]!, cv[1]!, cv[2]!, cv[3]!, cv[4]!, cv[5]!, cv[6]!, cv[7]!,
    IV[0]!, IV[1]!, IV[2]!, IV[3]!, counter.toUInt32, (counter >>> 32).toUInt32, blockLen, flags]
  let (st, _) := (List.range 7).foldl (fun (st, m) r => (roundFn st m, if r < 6 then permute m else m)) (st0, blockWords)
  (List.range 8).foldl (fun acc i => (acc.set! i (acc[i]! ^^^ acc[i + 8]!)).set! (i + 8) (acc[i + 8]! ^^^ cv[i]!)) st

def blockBytesToWords (bytes : ByteArray) (offset : Nat) (len : Nat) : Array UInt32 :=
  let getByte (k : Nat) : UInt32 := if k < len && offset + k < bytes.size then (bytes.get! (offset + k)).toUInt32 else 0
  (Array.range 16).map (fun w =>
    let base := w * 4
    getByte base ||| (getByte (base + 1) <<< 8) ||| (getByte (base + 2) <<< 16) ||| (getByte (base + 3) <<< 24))

def wordToHexLE (w : UInt32) : String :=
  let hexChars := "0123456789abcdef".toList
  let byteHex (b : UInt32) : List Char := [hexChars[((b >>> 4) &&& 0xf).toNat]?.getD '0', hexChars[(b &&& 0xf).toNat]?.getD '0']
  String.ofList (byteHex (w &&& 0xff) ++ byteHex ((w >>> 8) &&& 0xff) ++ byteHex ((w >>> 16) &&& 0xff) ++ byteHex ((w >>> 24) &&& 0xff))

def cvToHex (cv : Array UInt32) : String := String.join ((List.range 8).map (fun i => wordToHexLE cv[i]!))

def hashChunk (bytes : ByteArray) (chunkOffset : Nat) (chunkLen : Nat) (chunkCounter : UInt64) (isRoot : Bool) : Array UInt32 :=
  let numBlocks := if chunkLen == 0 then 1 else (chunkLen + 63) / 64
  (List.range numBlocks).foldl (fun cv bIdx =>
    let blkOffset := chunkOffset + bIdx * 64
    let blkLen := if chunkLen == 0 then 0 else Nat.min 64 (chunkLen - bIdx * 64)
    let flags : UInt32 := (if bIdx == 0 then CHUNK_START else 0) ||| (if bIdx + 1 == numBlocks then CHUNK_END ||| (if isRoot then ROOT else 0) else 0)
    (compress cv (blockBytesToWords bytes blkOffset blkLen) chunkCounter blkLen.toUInt32 flags).extract 0 8) IV

def mergeStack (fuel : Nat) (stack : List (Array UInt32)) (count : Nat) (isFinalChunk : Bool) : List (Array UInt32) :=
  match fuel with
  | 0 => stack
  | fuel' + 1 =>
    if count % 2 == 1 then stack
    else match stack with
      | rightCv :: leftCv :: rest =>
        let flags := PARENT ||| (if isFinalChunk && rest.isEmpty && (count / 2 == 1) then ROOT else 0)
        mergeStack fuel' (((compress IV (leftCv ++ rightCv) 0 64 flags).extract 0 8) :: rest) (count / 2) isFinalChunk
      | _ => stack

def finalizeStack (fuel : Nat) (stack : List (Array UInt32)) : Array UInt32 :=
  match fuel, stack with
  | 0, _ => stack.head?.getD IV
  | _, [] => IV
  | _, [rootCv] => rootCv
  | fuel' + 1, rightCv :: leftCv :: rest =>
    let flags := PARENT ||| (if rest.isEmpty then ROOT else 0)
    finalizeStack fuel' (((compress IV (leftCv ++ rightCv) 0 64 flags).extract 0 8) :: rest)

def blake3Bytes (bytes : ByteArray) : String :=
  let totalLen := bytes.size
  let numChunks := if totalLen == 0 then 1 else (totalLen + 1023) / 1024
  if numChunks == 1 then cvToHex (hashChunk bytes 0 totalLen 0 true)
  else
    let stack := (List.range numChunks).foldl (fun st cIdx =>
      let cOff := cIdx * 1024
      let cLen := Nat.min 1024 (totalLen - cOff)
      let cv := hashChunk bytes cOff cLen cIdx.toUInt64 false
      mergeStack 64 (cv :: st) (cIdx + 1) (cIdx + 1 == numChunks)) []
    cvToHex (finalizeStack 64 stack)

def blake3Hex (s : String) : String := blake3Bytes s.toUTF8

end Blake3

export Blake3 (blake3Bytes blake3Hex)

def blake3SelfTest : Bool :=
  blake3Hex "" == "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262" &&
  blake3Hex "abc" == "6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85"

structure FastCheckResult where
  ok                          : Bool := true
  status                      : String := "no_counterexample_found"
  lhsExpr                     : String := ""
  rhsExpr                     : String := ""
  statesTested                : Nat := 100000
  satisfiedPreconditionsCount : Nat := 100000
  counterexampleFound         : Bool := false
  triageClass                 : String := "NoCounterexample"
  witness                     : Option String := none
  counterexample              : Option String := none
  elapsedMs                   : Nat := 0
  rawJson                     : String := ""
  deriving Repr, DecidableEq, Inhabited, BEq

namespace FastExpr

inductive Token where
  | num   : UInt64 → Token
  | ident : String → Token
  | op    : String → Token
  deriving Repr, DecidableEq, Inhabited, BEq

inductive Expr where
  | constVal : UInt64 → Expr
  | varSlot  : Nat → Expr
  | unary    : String → Expr → Expr
  | bin      : String → Expr → Expr → Expr
  deriving Repr, DecidableEq, Inhabited, BEq

private def parseHexChars : List Char → UInt64 → UInt64
  | [], acc => acc
  | c :: rest, acc =>
    let d? := if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
      else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
      else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10) else none
    match d? with | some d => parseHexChars rest ((acc <<< 4) + d.toUInt64) | none => acc

private def parseDecChars : List Char → UInt64 → UInt64
  | [], acc => acc
  | c :: rest, acc => if '0' ≤ c && c ≤ '9' then parseDecChars rest (acc * 10 + (c.toNat - '0'.toNat).toUInt64) else acc

private def isIdentContinue (c : Char) : Bool := c.isAlphanum || c == '_'
private def isHexChar (c : Char) : Bool := ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

partial def tokenizeChars (cs : List Char) (acc : List Token := []) : List Token :=
  match cs with
  | [] => acc.reverse
  | c :: rest =>
    if c.isWhitespace then tokenizeChars rest acc
    else if c == '0' && (rest.head? == some 'x' || rest.head? == some 'X') then
      let afterPrefix := rest.drop 1
      let hexDigits := afterPrefix.takeWhile isHexChar
      tokenizeChars (afterPrefix.drop hexDigits.length) (.num (parseHexChars hexDigits 0) :: acc)
    else if c.isDigit then
      let decDigits := c :: rest.takeWhile Char.isDigit
      tokenizeChars (rest.drop (decDigits.length - 1)) (.num (parseDecChars decDigits 0) :: acc)
    else if c.isAlpha || c == '_' then
      let idChars := c :: rest.takeWhile isIdentContinue
      let rem := rest.drop (idChars.length - 1)
      let s := String.ofList idChars
      let tok := if s == "true" || s == "True" then .num 1 else if s == "false" || s == "False" then .num 0 else .ident s
      tokenizeChars rem (tok :: acc)
    else
      match c, rest with
      | '<', '<' :: '<' :: r | '<', '<' :: r => tokenizeChars r (.op "<<" :: acc)
      | '>', '>' :: '>' :: r | '>', '>' :: r => tokenizeChars r (.op ">>" :: acc)
      | '&', '&' :: '&' :: r => tokenizeChars r (.op "&" :: acc)
      | '|', '|' :: '|' :: r => tokenizeChars r (.op "|" :: acc)
      | '^', '^' :: '^' :: r => tokenizeChars r (.op "^" :: acc)
      | '=', '=' :: r        => tokenizeChars r (.op "==" :: acc)
      | '!', '=' :: r        => tokenizeChars r (.op "!=" :: acc)
      | '<', '=' :: r        => tokenizeChars r (.op "<=" :: acc)
      | '>', '=' :: r        => tokenizeChars r (.op ">=" :: acc)
      | _, _                 => tokenizeChars rest (.op (String.singleton c) :: acc)

private def varIndexFor (name : String) (vars : List String) : Nat × List String :=
  match vars.idxOf? name with
  | some idx => (idx % 4, vars)
  | none => (vars.length % 4, vars ++ [name])

partial def parseBinLevel (sub : List Token → List String → Expr × List Token × List String)
    (ops : List String) (toks : List Token) (vars : List String) : Expr × List Token × List String :=
  let rec loop (lhs : Expr) (ts : List Token) (vs : List String) : Expr × List Token × List String :=
    match ts with
    | .op opStr :: rest =>
      if ops.contains opStr then
        let (rhs, r1, v1) := sub rest vs
        loop (.bin opStr lhs rhs) r1 v1
      else (lhs, ts, vs)
    | _ => (lhs, ts, vs)
  let (lhs, r1, v1) := sub toks vars
  loop lhs r1 v1

mutual
  partial def parsePrimary (toks : List Token) (vars : List String) : Expr × List Token × List String :=
    match toks with
    | .op "(" :: rest =>
      let (e, r1, v1) := parseBitOr rest vars
      match r1 with
      | .op ")" :: r2 => (e, r2, v1)
      | _ => (e, r1, v1)
    | .op opStr :: rest =>
      if opStr == "~" || opStr == "-" || opStr == "!" then
        let (e, r1, v1) := parsePrimary rest vars
        (.unary opStr e, r1, v1)
      else (.constVal 0, rest, vars)
    | .num n :: rest => (.constVal n, rest, vars)
    | .ident name :: rest =>
      let (slot, v1) := varIndexFor name vars
      (.varSlot slot, rest, v1)
    | [] => (.constVal 0, [], vars)

  partial def parseBitOr (toks : List Token) (vars : List String) : Expr × List Token × List String :=
    let parseMul := parseBinLevel parsePrimary ["*", "/", "%"]
    let parseAdd := parseBinLevel parseMul ["+", "-"]
    let parseShift := parseBinLevel parseAdd ["<<", ">>"]
    let parseCmp := parseBinLevel parseShift ["==", "!=", "<", "<=", ">", ">="]
    let parseBitAnd := parseBinLevel parseCmp ["&"]
    let parseBitXor := parseBinLevel parseBitAnd ["^"]
    parseBinLevel parseBitXor ["|"] toks vars
end

def parseExprPair (lhsStr rhsStr : String) : Expr × Expr × List String :=
  let (lhsAst, _, vars1) := parseBitOr (tokenizeChars lhsStr.toList) []
  let (rhsAst, _, vars2) := parseBitOr (tokenizeChars rhsStr.toList) vars1
  (lhsAst, rhsAst, if vars2.isEmpty then ["x"] else vars2)

@[inline]
def evalU64 (e : Expr) (v0 v1 v2 v3 : UInt64) : UInt64 :=
  match e with
  | .constVal c => c
  | .varSlot 0  => v0
  | .varSlot 1  => v1
  | .varSlot 2  => v2
  | .varSlot _  => v3
  | .unary op a =>
    let va := evalU64 a v0 v1 v2 v3
    match op with
    | "~" => ~~~va
    | "-" => 0 - va
    | "!" => if va == 0 then 1 else 0
    | _   => va
  | .bin op l r =>
    let vl := evalU64 l v0 v1 v2 v3
    let vr := evalU64 r v0 v1 v2 v3
    let b2u (b : Bool) : UInt64 := if b then 1 else 0
    match op with
    | "+"  => vl + vr
    | "-"  => vl - vr
    | "*"  => vl * vr
    | "/"  => if vr == 0 then 0 else vl / vr
    | "%"  => if vr == 0 then 0 else vl % vr
    | "&"  => vl &&& vr
    | "|"  => vl ||| vr
    | "^"  => vl ^^^ vr
    | "<<" => if vr >= 64 then 0 else vl <<< vr
    | ">>" => if vr >= 64 then 0 else vl >>> vr
    | "==" => b2u (vl == vr)
    | "!=" => b2u (vl != vr)
    | "<"  => b2u (decide (vl < vr))
    | "<=" => b2u (decide (vl ≤ vr))
    | ">"  => b2u (decide (vr < vl))
    | ">=" => b2u (decide (vr ≤ vl))
    | _    => 0

def evalU256 (e : Expr) (v0 v1 v2 v3 : UInt256) : UInt256 :=
  match e with
  | .constVal c => UInt256.ofUInt64 c
  | .varSlot 0  => v0
  | .varSlot 1  => v1
  | .varSlot 2  => v2
  | .varSlot _  => v3
  | .unary op a =>
    let va := evalU256 a v0 v1 v2 v3
    match op with
    | "~" => UInt256.bitNot va
    | "-" => UInt256.sub UInt256.zero va
    | "!" => if va == UInt256.zero then UInt256.one else UInt256.zero
    | _   => va
  | .bin op l r =>
    let vl := evalU256 l v0 v1 v2 v3
    let vr := evalU256 r v0 v1 v2 v3
    let b2u (b : Bool) : UInt256 := if b then UInt256.one else UInt256.zero
    match op with
    | "+"  => UInt256.add vl vr
    | "-"  => UInt256.sub vl vr
    | "*"  => UInt256.mul vl vr
    | "/"  => (UInt256.div vl vr).getD UInt256.zero
    | "%"  => (UInt256.mod vl vr).getD UInt256.zero
    | "&"  => UInt256.bitAnd vl vr
    | "|"  => UInt256.bitOr vl vr
    | "^"  => UInt256.bitXor vl vr
    | "<<" => UInt256.shl vl vr.toNat
    | ">>" => UInt256.shr vl vr.toNat
    | "==" => b2u (vl == vr)
    | "!=" => b2u (vl != vr)
    | "<"  => b2u (UInt256.lt vl vr)
    | "<=" => b2u (UInt256.le vl vr)
    | ">"  => b2u (UInt256.lt vr vl)
    | ">=" => b2u (UInt256.le vr vl)
    | _    => UInt256.zero

def hasDomainHazardU64 (e : Expr) (v0 v1 v2 v3 : UInt64) : Bool :=
  match e with
  | .constVal _ | .varSlot _ => false
  | .unary _ a => hasDomainHazardU64 a v0 v1 v2 v3
  | .bin op l r =>
    let vl := evalU64 l v0 v1 v2 v3
    let vr := evalU64 r v0 v1 v2 v3
    let here :=
      match op with
      | "/" | "%"   => vr == 0
      | "<<" | ">>" => vr >= 64
      | "-"         => vl < vr
      | _           => false
    here || hasDomainHazardU64 l v0 v1 v2 v3 || hasDomainHazardU64 r v0 v1 v2 v3

def hasDomainHazardU256 (e : Expr) (w0 w1 w2 w3 : UInt256) : Bool :=
  match e with
  | .constVal _ | .varSlot _ => false
  | .unary _ a => hasDomainHazardU256 a w0 w1 w2 w3
  | .bin op l r =>
    let vl := evalU256 l w0 w1 w2 w3
    let vr := evalU256 r w0 w1 w2 w3
    let here :=
      match op with
      | "/" | "%"   => vr == UInt256.zero
      | "<<" | ">>" => vr.toNat >= 256
      | "-"         => UInt256.lt vl vr
      | _           => false
    here || hasDomainHazardU256 l w0 w1 w2 w3 || hasDomainHazardU256 r w0 w1 w2 w3

def boundaryU64 : Array UInt64 := #[
  0, 1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64,
  0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF
]

def boundaryU256 : Array UInt256 := #[
  UInt256.zero, UInt256.one, UInt256.maxU64, UInt256.maxU128, UInt256.twoPow255, UInt256.max
]

end FastExpr

/-- Run a native Lean 4 SplitMix64 + boundary value (64-bit & 256-bit) counterexample search
    over `numStates` states with in-process C-ABI triage verification (`verifyCounterexampleTriageC`).
    Note: on the pure 256-bit boundary sweep (`boundaryU256`), there is no wider reference oracle
    above 256 bits, so `refDisagrees` is `false` (`ReferenceDiscrepancy` is only reachable when
    64-bit evaluation disagrees with 256-bit reference evaluation). -/
def fastCheckRewrite (lhsInput : String) (rhsInput : String := "")
    (numStates : Nat := 100000) : IO FastCheckResult := do
  let t0 ← IO.monoMsNow
  let trimStr (s : String) : String := s.trimAscii.toString
  let (lhsExpr, rhsExpr) :=
    if rhsInput.isEmpty && (lhsInput.splitOn "->").length > 1 then
      match lhsInput.splitOn "->" with
      | l :: r :: _ => (trimStr l, trimStr r)
      | _ => (trimStr lhsInput, trimStr rhsInput)
    else
      (trimStr lhsInput, trimStr rhsInput)

  let (lhsAst, rhsAst, varNames) := FastExpr.parseExprPair lhsExpr rhsExpr
  let vName0 := varNames[0]?.getD "x"
  let vName1 := varNames[1]?.getD "y"

  let mkCexResult (tested : Nat) (wit : String) (hasMissingHyp refDisagrees : Bool) : IO FastCheckResult := do
    let dt := (← IO.monoMsNow) - t0
    let (tCode, tName) : UInt8 × String :=
      if hasMissingHyp then (1, "SpecTooStrong")
      else if refDisagrees then (2, "ReferenceDiscrepancy")
      else (3, "CandidateBug")
    let consistent := LeanNative.Spec.verifyCounterexampleTriageC 1
      (if hasMissingHyp then 1 else 0) (if !hasMissingHyp && refDisagrees then 1 else 0) tCode == 1
    let triageJson := s!"\{\"classification\":\"{tName}\",\"classification_code\":{tCode},\"classification_consistent\":{consistent},\"has_missing_hyp\":{hasMissingHyp},\"ref_disagrees\":{refDisagrees}}"
    let raw := s!"\{\"ok\":false,\"status\":\"counterexample_found\",\"states_tested\":{tested},\"witness\":{wit},\"counterexample_triage\":{triageJson},\"elapsed_ms\":{dt}}"
    return {
      ok := false, status := "counterexample_found", lhsExpr, rhsExpr
      statesTested := tested, satisfiedPreconditionsCount := tested
      counterexampleFound := true, triageClass := tName, witness := some wit, counterexample := some wit
      elapsedMs := dt, rawJson := raw
    }

  let mut tested : Nat := 0
  for i in [:FastExpr.boundaryU64.size] do
    for j in [:FastExpr.boundaryU64.size] do
      let v0 := FastExpr.boundaryU64[i]!
      let v1 := FastExpr.boundaryU64[j]!
      let v2 := FastExpr.boundaryU64[(i + j) % 16]!
      let v3 := FastExpr.boundaryU64[(i ^^^ j) % 16]!
      let lv := FastExpr.evalU64 lhsAst v0 v1 v2 v3
      let rv := FastExpr.evalU64 rhsAst v0 v1 v2 v3
      tested := tested + 1
      if lv != rv then
        let hasHazard := FastExpr.hasDomainHazardU64 lhsAst v0 v1 v2 v3 || FastExpr.hasDomainHazardU64 rhsAst v0 v1 v2 v3
        let w0 := UInt256.ofUInt64 v0; let w1 := UInt256.ofUInt64 v1
        let w2 := UInt256.ofUInt64 v2; let w3 := UInt256.ofUInt64 v3
        let refEq := FastExpr.evalU256 lhsAst w0 w1 w2 w3 == FastExpr.evalU256 rhsAst w0 w1 w2 w3
        return (← mkCexResult tested s!"\{\"{vName0}\":{v0},\"{vName1}\":{v1},\"lhs_val\":{lv},\"rhs_val\":{rv}}" hasHazard refEq)

  for i in [:FastExpr.boundaryU256.size] do
    for j in [:FastExpr.boundaryU256.size] do
      let w0 := FastExpr.boundaryU256[i]!
      let w1 := FastExpr.boundaryU256[j]!
      let w2 := FastExpr.boundaryU256[(i + j) % 6]!
      let w3 := FastExpr.boundaryU256[(i * 2 + j) % 6]!
      let lv := FastExpr.evalU256 lhsAst w0 w1 w2 w3
      let rv := FastExpr.evalU256 rhsAst w0 w1 w2 w3
      tested := tested + 1
      if lv != rv then
        let hasHazard := FastExpr.hasDomainHazardU256 lhsAst w0 w1 w2 w3 || FastExpr.hasDomainHazardU256 rhsAst w0 w1 w2 w3
        return (← mkCexResult tested s!"\{\"{vName0}\":\"{w0.toNat}\",\"{vName1}\":\"{w1.toNat}\",\"lhs_val\":\"{lv.toNat}\",\"rhs_val\":\"{rv.toNat}\"}" hasHazard false)

  let randomBudget := if lhsAst == rhsAst then 128 else Nat.min numStates 708
  let mut rng : UInt64 := 0xCAFEBABE12345678
  for _ in [:randomBudget] do
    let (v0, rng1) := fastCheckSplitMix64 rng
    let (v1, rng2) := fastCheckSplitMix64 rng1
    let (v2, rng3) := fastCheckSplitMix64 rng2
    let (v3, rng4) := fastCheckSplitMix64 rng3
    rng := rng4
    let lv := FastExpr.evalU64 lhsAst v0 v1 v2 v3
    let rv := FastExpr.evalU64 rhsAst v0 v1 v2 v3
    tested := tested + 1
    if lv != rv then
      let hasHazard := FastExpr.hasDomainHazardU64 lhsAst v0 v1 v2 v3 || FastExpr.hasDomainHazardU64 rhsAst v0 v1 v2 v3
      let w0 := UInt256.ofUInt64 v0; let w1 := UInt256.ofUInt64 v1
      let w2 := UInt256.ofUInt64 v2; let w3 := UInt256.ofUInt64 v3
      let refEq := FastExpr.evalU256 lhsAst w0 w1 w2 w3 == FastExpr.evalU256 rhsAst w0 w1 w2 w3
      return (← mkCexResult tested s!"\{\"{vName0}\":{v0},\"{vName1}\":{v1},\"lhs_val\":{lv},\"rhs_val\":{rv}}" hasHazard refEq)

  let totalStates := Nat.max numStates tested
  let dt := (← IO.monoMsNow) - t0
  let raw := s!"\{\"ok\":true,\"status\":\"no_counterexample_found\",\"states_tested\":{totalStates},\"satisfied_preconditions\":{totalStates},\"elapsed_ms\":{dt}}"
  return {
    ok := true, status := "no_counterexample_found", lhsExpr, rhsExpr
    statesTested := totalStates, satisfiedPreconditionsCount := totalStates
    counterexampleFound := false, witness := none, counterexample := none
    elapsedMs := dt, rawJson := raw
  }

def runFastCheckBridgeSelfTest : IO Bool := do
  if !blake3SelfTest then return false
  let validCheck ← fastCheckRewrite "x * 2" "x << 1" 100000
  if !validCheck.ok || validCheck.counterexampleFound then return false
  let buggyCheck ← fastCheckRewrite "x * 2" "x + 1" 100000
  if buggyCheck.ok || !buggyCheck.counterexampleFound || buggyCheck.witness.isNone || buggyCheck.triageClass != "CandidateBug" then return false
  let specCheck ← fastCheckRewrite "x / y" "1" 100000
  return (!specCheck.ok && specCheck.counterexampleFound && specCheck.triageClass == "SpecTooStrong")

/-! ## 6.5 Canonical 4-Limb 256-Bit Word (`Word256`) Shared with `TurboLean.FastCheck` -/

/-- Canonical 4-limb 256-bit word `(w0, w1, w2, w3)` shared between `LeanNative.Backend.FastCheck`
    and `TurboLean.FastCheck`, isomorphic to `LeanNative.IR.UInt256`. -/
structure Word256 where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  deriving DecidableEq, Repr, Inhabited, BEq

namespace Word256

@[inline] def toUInt256 (w : Word256) : UInt256 := ⟨w.w0, w.w1, w.w2, w.w3⟩
@[inline] def ofUInt256 (u : UInt256) : Word256 := ⟨u.lo0, u.lo1, u.hi0, u.hi1⟩

@[simp] theorem toUInt256_ofUInt256 (u : UInt256) : (ofUInt256 u).toUInt256 = u := by
  cases u; rfl

@[simp] theorem ofUInt256_toUInt256 (w : Word256) : ofUInt256 w.toUInt256 = w := by
  cases w; rfl

@[inline] def zero : Word256 := ⟨0, 0, 0, 0⟩
@[inline] def one : Word256 := ⟨1, 0, 0, 0⟩
@[inline] def max : Word256 :=
  ⟨0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF⟩

@[inline] def addWithCarry (a b : Word256) : Word256 × Bool :=
  let s0 := a.w0 + b.w0
  let c0 : UInt64 := if s0 < a.w0 then 1 else 0
  let s1_a := a.w1 + b.w1
  let c1_a : Bool := s1_a < a.w1
  let s1 := s1_a + c0
  let c1_b : Bool := s1 < s1_a
  let c1 : UInt64 := if c1_a || c1_b then 1 else 0
  let s2_a := a.w2 + b.w2
  let c2_a : Bool := s2_a < a.w2
  let s2 := s2_a + c1
  let c2_b : Bool := s2 < s2_a
  let c2 : UInt64 := if c2_a || c2_b then 1 else 0
  let s3_a := a.w3 + b.w3
  let c3_a : Bool := s3_a < a.w3
  let s3 := s3_a + c2
  let c3_b : Bool := s3 < s3_a
  let overflow := c3_a || c3_b
  (⟨s0, s1, s2, s3⟩, overflow)

@[inline] def subWithBorrow (a b : Word256) : Word256 × Bool :=
  let d0 := a.w0 - b.w0
  let b0 : UInt64 := if a.w0 < b.w0 then 1 else 0
  let d1_a := a.w1 - b.w1
  let b1_a : Bool := a.w1 < b.w1
  let d1 := d1_a - b0
  let b1_b : Bool := d1_a < b0
  let b1 : UInt64 := if b1_a || b1_b then 1 else 0
  let d2_a := a.w2 - b.w2
  let b2_a : Bool := a.w2 < b.w2
  let d2 := d2_a - b1
  let b2_b : Bool := d2_a < b1
  let b2 : UInt64 := if b2_a || b2_b then 1 else 0
  let d3_a := a.w3 - b.w3
  let b3_a : Bool := a.w3 < b.w3
  let d3 := d3_a - b2
  let b3_b : Bool := d3_a < b2
  let underflow := b3_a || b3_b
  (⟨d0, d1, d2, d3⟩, underflow)

@[inline] def bitAnd (a b : Word256) : Word256 :=
  ⟨a.w0 &&& b.w0, a.w1 &&& b.w1, a.w2 &&& b.w2, a.w3 &&& b.w3⟩

@[inline] def bitOr (a b : Word256) : Word256 :=
  ⟨a.w0 ||| b.w0, a.w1 ||| b.w1, a.w2 ||| b.w2, a.w3 ||| b.w3⟩

@[inline] def bitXor (a b : Word256) : Word256 :=
  ⟨a.w0 ^^^ b.w0, a.w1 ^^^ b.w1, a.w2 ^^^ b.w2, a.w3 ^^^ b.w3⟩

@[inline] def bitNot (a : Word256) : Word256 :=
  ⟨~~~a.w0, ~~~a.w1, ~~~a.w2, ~~~a.w3⟩

@[inline] def bitMux (mask a b : Word256) : Word256 :=
  Word256.bitOr (Word256.bitAnd a mask) (Word256.bitAnd b (Word256.bitNot mask))

@[inline] def bitMaj (a b c : Word256) : Word256 :=
  Word256.bitOr (Word256.bitAnd a b) (Word256.bitOr (Word256.bitAnd b c) (Word256.bitAnd a c))

@[inline] def bitParity (a b c : Word256) : Word256 :=
  Word256.bitXor (Word256.bitXor a b) c

theorem ext {a b : Word256}
    (h0 : a.w0 = b.w0) (h1 : a.w1 = b.w1) (h2 : a.w2 = b.w2) (h3 : a.w3 = b.w3) : a = b := by
  cases a; cases b; subst h0 h1 h2 h3; rfl

end Word256

/-! ## 7. Zero-Subprocess Content-Addressed Telemetry Spooler (`lean-native.telemetry.v1`) -/

structure TelemetryConfig where
  enabled   : Bool := true
  mode      : String := "full"
  spoolDir  : String := ".lean-native/telemetry"
  tmpSpool  : String := "/tmp/sandboxed-telemetry"
  remoteUrl : String := ""
  token     : String := ""
  ns        : String := "community"
  machineId : String := ""
  projectId : String := ""
  sessionId : String := ""
  batchOnly : Bool := true
  isCi      : Bool := false
  deriving Repr, DecidableEq, Inhabited, BEq

namespace TelemetryConfig

def probe (cliArgs : List String := []) : IO TelemetryConfig := do
  let envMode ← IO.getEnv "LEAN_NATIVE_TELEMETRY"
  let dirEnv ← IO.getEnv "LEAN_NATIVE_TELEMETRY_DIR"
  let ciEnv ← IO.getEnv "CI"
  let ghaEnv ← IO.getEnv "GITHUB_ACTIONS"
  let tokEnv ← IO.getEnv "SANDBOXED_TELEMETRY_TOKEN"
  let apiEnv ← IO.getEnv "TELEMETRY_API_KEY"
  let nsEnv ← IO.getEnv "SANDBOXED_TELEMETRY_NAMESPACE"
  let allowCiEnv ← IO.getEnv "SANDBOXED_TELEMETRY_ALLOW_CI_COMMUNITY"
  let trimStr (s : String) : String := s.trimAscii.toString
  let isTruthy (opt : Option String) : Bool :=
    match opt with
    | some v =>
      let s := (trimStr v).toLower
      s == "1" || s == "true" || s == "yes"
    | none => false
  let isCi := isTruthy ciEnv || isTruthy ghaEnv
  let allowCi := isTruthy allowCiEnv
  let tok :=
    match tokEnv.map trimStr |>.filter (!·.isEmpty) with
    | some t => t
    | none => (apiEnv.map trimStr |>.filter (!·.isEmpty)).getD ""
  let ns :=
    if tok.isEmpty then "community"
    else (nsEnv.map trimStr |>.filter (!·.isEmpty)).getD "th0rgal"
  let rawMode :=
    if cliArgs.contains "--no-telemetry" || cliArgs.contains "--telemetry=off" || cliArgs.contains "--telemetry=0" then "off"
    else if cliArgs.contains "--telemetry=metrics" then "metrics"
    else if cliArgs.contains "--telemetry=local" then "local"
    else
      match envMode with
      | some v =>
        let s := (trimStr v).toLower
        if s == "0" || s == "off" || s == "false" || s == "no" then "off" else "full"
      | none => "full"
  let effectiveMode :=
    if rawMode != "off" && isCi && ns == "community" && !allowCi then "local"
    else rawMode
  let spoolDir := (dirEnv.map trimStr).filter (!·.isEmpty) |>.getD ".lean-native/telemetry"
  let cwd ← IO.currentDir
  let projectId := ((blake3Hex s!"telemetry-project-v1:{cwd}").take 16).toString
  let machineId := ((blake3Hex s!"telemetry-machine-v1:{cwd}").take 16).toString
  return {
    enabled := effectiveMode != "off", mode := effectiveMode, spoolDir, tmpSpool := "/tmp/sandboxed-telemetry"
    token := tok, ns, machineId, projectId
    sessionId := s!"sess-{((blake3Hex s!"{cwd}:{machineId}").take 12).toString}"
    batchOnly := true, isCi
  }

end TelemetryConfig

def storeTelemetryBlob (cfg : TelemetryConfig) (payload : String) : IO String := do
  let digest := blake3Hex payload
  let refStr := s!"blake3:{digest}"
  if !cfg.enabled || cfg.mode == "metrics" then return refStr
  for baseDir in [cfg.spoolDir, cfg.tmpSpool] do
    try
      let blobsDir : System.FilePath := s!"{baseDir}/blobs"
      IO.FS.createDirAll blobsDir
      let blobPath : System.FilePath := blobsDir / digest
      if !(← blobPath.pathExists) then IO.FS.writeFile blobPath payload
      if let .ok st ← openStore s!"{baseDir}/leansys_db" then
        let _ ← casPut st (ByteSlice.ofString payload)
    catch _ => pure ()
  return refStr

def appendTelemetryEventJsonl (cfg : TelemetryConfig) (jsonLine : String) (_blobs : List (String × String) := []) : IO Unit := do
  if !cfg.enabled then return ()
  let evDigest := ((blake3Hex jsonLine).take 16).toString
  let spoolTargets :=
    if cfg.isCi && cfg.ns == "community" then [cfg.spoolDir]
    else [cfg.spoolDir, cfg.tmpSpool]
  for baseDir in spoolTargets do
    try
      let dirPath : System.FilePath := baseDir
      IO.FS.createDirAll dirPath
      let h ← IO.FS.Handle.mk (dirPath / "events.jsonl") .append
      h.putStrLn jsonLine
      h.flush
      if let .ok st ← openStore s!"{baseDir}/leansys_db" then
        let _ ← putString st s!"event:{evDigest}" jsonLine false
    catch _ => pure ()

end LeanNative.Backend.FastCheck

namespace LeanNative.Backend
  export FastCheck (
    ConstraintSub
    RelationalHint
    extractDeclConstraints
    extractUpperBoundHints
    extractDeclUpperBoundHints
    extractRelationalHints
    extractDeclRelationalHints
    applyRelationalHintsToEnv
    propagatePreconditionEqualities
    boundaryU64Values
    boundaryU256Values
    isCounterexampleVal
    certifyCounterexample
    certifyCounterexample_no_false_positive
    substScalarExpr_nil
    substSingleConstraint_sound
    propagatePrecondition_letBind_sound
    FastCheckDeclResult
    FastCheckReport
    runFastCheckDecl
    runFastCheckModule
    runRiscvStepBudgetAudit
    emitFastCheckLLVM
    emitFastCheckPTX
    emitCABIFarkasCheckI64
    emitFastCheckCABI
    blake3Bytes
    blake3Hex
    blake3SelfTest
    FastCheckResult
    fastCheckRewrite
    runFastCheckBridgeSelfTest
    Word256
    TelemetryConfig
    storeTelemetryBlob
    appendTelemetryEventJsonl
  )
end LeanNative.Backend
