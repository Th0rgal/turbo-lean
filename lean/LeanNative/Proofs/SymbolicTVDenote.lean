import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.Proofs.SymbolicTV

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics

/-!
# Concrete Denotation of `SymExpr` (`LeanNative.Proofs.SymbolicTVDenote`)

Assigns a concrete `Val` to a `SymExpr` under a `SymValuation`, using the locked
operational semantics (`evalBinOp`, `evalUnaryOp`, `UInt256.mulDivDown` / `mulDivUp`)
directly. Every rewrite proved sound in `SymbolicTVSoundness` is stated against this
denotation, so `TranslationValidated` is no longer an uninterpreted TCB claim.
-/

/-- Concrete assignment of symbolic inputs (`symVar`, `rcSym`, `ctorTag`, `ctorLen`,
    `sarrayLen`, `bufElem`) to runtime values. -/
structure SymValuation where
  varVal      : VarId → Option Val := fun _ => none
  rcVal       : Nat → VarId → Option UInt64 := fun _ _ => none
  ctorTagVal  : Nat → VarId → Option UInt64 := fun _ _ => none
  ctorLenVal  : Bool → Nat → VarId → Option UInt64 := fun _ _ _ => none
  sarrayLenVal : VarId → Option UInt64 := fun _ => none
  bufElemVal  : MemWriteSpace → VarId → Val → Option Val := fun _ _ _ => none
  deriving Inhabited

namespace SymValuation

/-- Bind variable `id` to `v` in a valuation (every field is referenced). -/
def bindVar (ω : SymValuation) (id : VarId) (v : Val) : SymValuation :=
  { ω with varVal := fun y => if y == id then some v else ω.varVal y }

end SymValuation

/-- Interpret a boolean-valued `Val` as a branch condition, exactly as
    `evalScalarExpr` (`select`) and `evalCode` (`.ite`) do. -/
def condIsTrue? : Val → Option Bool
  | .bool b => some b
  | .u64 n => some (n != 0)
  | .u256 w => some (w != UInt256.zero)
  | _ => none

mutual
  /-- Concrete denotation of a symbolic value expression under valuation `ω`. -/
  def denoteSymExpr (ω : SymValuation) : SymExpr → Except UBError Val
    | .constU64 v => .ok (.u64 v)
    | .constU256 w => .ok (.u256 w)
    | .constBool b => .ok (.bool b)
    | .symVar id =>
      match ω.varVal id with
      | some v => .ok v
      | none => .error (.unboundVar id)
    | .allocTag id =>
      match ω.varVal id with
      | some v => .ok v
      | none => .ok .unit
    | .rcSym ep id =>
      match ω.rcVal ep id with
      | some n => .ok (.u64 n)
      | none => .error (.unboundVar id)
    | .ctorTag ep id =>
      match ω.ctorTagVal ep id with
      | some n => .ok (.u64 n)
      | none => .error (.unboundVar id)
    | .ctorLen sc ep id =>
      match ω.ctorLenVal sc ep id with
      | some n => .ok (.u64 n)
      | none => .error (.unboundVar id)
    | .sarrayLen id =>
      match ω.sarrayLenVal id with
      | some n => .ok (.u64 n)
      | none => .error (.unboundVar id)
    | .mulDiv256 isUp a b d =>
      match denoteSymExpr ω a, denoteSymExpr ω b, denoteSymExpr ω d with
      | .ok va, .ok vb, .ok vd =>
        match va.toU256?, vb.toU256?, vd.toU256? with
        | some wa, some wb, some wd =>
          match (if isUp then UInt256.mulDivUp else UInt256.mulDivDown) wa wb wd with
          | some q => .ok (.u256 q)
          | none => .error (if wd == UInt256.zero then .divisionByZero else .arithmeticOverflow "mulDiv256")
        | _, _, _ => .error (.typeError "denoteSymExpr: mulDiv256 expects u256/u64")
      | .error err, _, _ => .error err
      | .ok _, .error err, _ => .error err
      | .ok _, .ok _, .error err => .error err
    | .binOp op l r =>
      match denoteSymExpr ω l, denoteSymExpr ω r with
      | .ok vl, .ok vr => evalBinOp op vl vr
      | .error err, _ => .error err
      | .ok _, .error err => .error err
    | .unaryOp op a =>
      match denoteSymExpr ω a with
      | .ok v => evalUnaryOp op v
      | .error err => .error err
    | .ite c t e =>
      match denoteSymExpr ω c with
      | .ok vc =>
        match condIsTrue? vc with
        | some true => denoteSymExpr ω t
        | some false => denoteSymExpr ω e
        | none => .error (.typeError "denoteSymExpr: ite condition")
      | .error err => .error err
    | .tuple fs =>
      match denoteSymExprList ω fs with
      | .ok vs => .ok (.tuple vs)
      | .error err => .error err
    | .bufElem sp b idx =>
      match denoteSymExpr ω idx with
      | .ok vi =>
        match ω.bufElemVal sp b vi with
        | some v => .ok v
        | none => .error (.unboundVar b)
      | .error err => .error err
    | .unit => .ok .unit

  /-- Concrete denotation of a list of symbolic expressions under valuation `ω`. -/
  def denoteSymExprList (ω : SymValuation) : List SymExpr → Except UBError (List Val)
    | [] => .ok []
    | e :: es =>
      match denoteSymExpr ω e, denoteSymExprList ω es with
      | .ok v, .ok vs => .ok (v :: vs)
      | .error err, _ => .error err
      | .ok _, .error err => .error err
end

/-- Two symbolic expressions denote equal values under every valuation. -/
def SymExprDenoteEq (a b : SymExpr) : Prop :=
  ∀ ω : SymValuation, denoteSymExpr ω a = denoteSymExpr ω b

/-- Forward refinement of symbolic expressions: every defined denotation of `a` is a
    defined denotation of `b` with the same value (errors may only be removed). -/
def SymExprDenoteRefines (a b : SymExpr) : Prop :=
  ∀ ω : SymValuation, ∀ v : Val, denoteSymExpr ω a = .ok v → denoteSymExpr ω b = .ok v

/-- A symbolic expression denotes a value of a definite scalar sort (`0` bool, `1` u64,
    `2` u256) under valuation `ω`. -/
def denotesSort (ω : SymValuation) (e : SymExpr) (s : Nat) : Prop :=
  match denoteSymExpr ω e with
  | .ok (.bool _) => s = sortBool
  | .ok (.u64 _) => s = sortU64
  | .ok (.u256 _) => s = sortU256
  | _ => False

/-- `e` denotes a 64-bit word under every valuation that defines it. -/
def denotesU64 (e : SymExpr) : Prop :=
  ∀ ω : SymValuation, ∀ v : Val, denoteSymExpr ω e = .ok v → ∃ n : UInt64, v = .u64 n

/-- `e` denotes a boolean under every valuation that defines it. -/
def denotesBool (e : SymExpr) : Prop :=
  ∀ ω : SymValuation, ∀ v : Val, denoteSymExpr ω e = .ok v → ∃ b : Bool, v = .bool b

/-- `e` denotes a 256-bit word under every valuation that defines it. -/
def denotesU256 (e : SymExpr) : Prop :=
  ∀ ω : SymValuation, ∀ v : Val, denoteSymExpr ω e = .ok v → ∃ w : UInt256, v = .u256 w

/-- Embed a pure `ScalarExpr` directly into `SymExpr` without symbolic normalization. -/
def scalarToSymExpr : ScalarExpr → SymExpr
  | .constU64 v => .constU64 v
  | .constBool b => .constBool b
  | .var id => .symVar id
  | .binOp op l r => .binOp op (scalarToSymExpr l) (scalarToSymExpr r)
  | .unaryOp op a => .unaryOp op (scalarToSymExpr a)
  | .select c t e => .ite (scalarToSymExpr c) (scalarToSymExpr t) (scalarToSymExpr e)
  | .fma a b c => .binOp .add (.binOp .mul (scalarToSymExpr a) (scalarToSymExpr b)) (scalarToSymExpr c)

/-- Build a canonical scalar valuation directly from a `VarEnv`. -/
def SymValuation.ofVarEnv (env : VarEnv) : SymValuation :=
  { varVal := env }

/-- A symbolic execution state agrees with a concrete valuation: every tracked variable
    denotes exactly its bound runtime value, and tracked sorts match that value. -/
def stateAgrees (st : SymExecState) (ω : SymValuation) (env : VarEnv) : Prop :=
  (∀ id : VarId, env id = ω.varVal id) ∧
  (∀ id : VarId, ∀ sv : SymStateVal, st.vars.lookup id = some sv →
    ∃ v : Val, ω.varVal id = some v ∧ denoteSymExpr ω sv.expr = .ok v) ∧
  (∀ id : VarId, st.u64Vars.contains id = true →
    ∃ n : UInt64, ω.varVal id = some (.u64 n)) ∧
  (∀ id : VarId, st.boolVars.contains id = true →
    ∃ b : Bool, ω.varVal id = some (.bool b)) ∧
  (∀ id : VarId, st.u256Vars.contains id = true →
    ∃ w : UInt256, ω.varVal id = some (.u256 w))

/-- Symbolic UB condition `c` holds concretely under valuation `ω`. -/
def ubCondHolds (ω : SymValuation) (c : SymExpr) : Prop :=
  denoteSymExpr ω c = .ok (.bool true)

/-- Symbolic execution of scalar expression `se` in state `st` agrees with the locked
    operational evaluator on every agreeing valuation whose UB condition holds. -/
def symEvalScalarResSound (st : SymExecState) (se : ScalarExpr) : Prop :=
  ∀ ω : SymValuation, ∀ env : VarEnv,
    stateAgrees st ω env → ubCondHolds ω (symEvalScalarRes st se).ubCond →
      (symEvalScalarRes st se).unsupported = false →
        evalScalarExpr env se = denoteSymExpr ω (symEvalScalarRes st se).val.expr

/-- Symbolic execution of code `c` refines the locked operational semantics whenever the
    analysis is complete (not exhausted, not unsupported) and the UB condition holds. -/
def symExecCodeSound (fuel unroll : Nat) (st : SymExecState) (c : LNIRCode) : Prop :=
  ∀ ω : SymValuation, ∀ env : VarEnv, ∀ st0 : HeapState, ∀ v : Val, ∀ st1 : HeapState,
    stateAgrees st ω env →
    let (st', ret) := symExecCode fuel unroll st c true
    st'.symExhausted = false → st'.symUnsupported = false →
    ubCondHolds ω st'.ubCond →
    evalCode fuel env st0 c = .ok (v, st1) →
    denoteSymExpr ω ret = .ok v

/-- Declaration-level symbolic validation is sound: a passing `validateTranslationDecl`
    with `numSamples` concrete checks guarantees complete (non-exhausted, supported) symbolic
    summaries and semantic return equivalence on all valuations satisfying the source UB guard. -/
def validateTranslationDeclSound (src tgt : LNIRDecl) (numSamples : Nat := 64) : Prop :=
  let r := validateTranslationDecl src tgt numSamples
  let sharedSynBase := Nat.max (declSynVarBase src) (declSynVarBase tgt)
  let sSrc := symExecDecl 4 src (some sharedSynBase)
  let sTgt := symExecDecl 4 tgt (some sharedSynBase)
  r.passed = true →
    sSrc.symExhausted = false ∧ sTgt.symExhausted = false ∧
    (src.params == tgt.params && src.retTy == tgt.retTy && src.body == tgt.body ||
      (sSrc.symUnsupported == false && sTgt.symUnsupported == false)) = true ∧
    (!sSrc.noUB || sTgt.noUB) = true ∧
    (!sSrc.nonPoison || sTgt.nonPoison) = true ∧
    sSrc.reachable = sTgt.reachable ∧
    r.concreteRefines = true

/-- Predicate that `env` binds every variable referenced in `e` to a concrete `.u64` value. -/
def envBindsVarsU64 (env : VarEnv) : ScalarExpr → Prop
  | .constU64 _ | .constBool _ => True
  | .var id => ∃ n : UInt64, env id = some (.u64 n)
  | .binOp _ l r => envBindsVarsU64 env l ∧ envBindsVarsU64 env r
  | .unaryOp _ a => envBindsVarsU64 env a
  | .select c t e | .fma c t e =>
    envBindsVarsU64 env c ∧ envBindsVarsU64 env t ∧ envBindsVarsU64 env e

/-- Predicate that a scalar symbolic state `st` maps every bound concrete variable in `env`
    to a non-UB `u64`-sorted symbolic expression denoting the same `.u64` value. -/
def stateAgreesU64 (st : SymExecState) (env : VarEnv) : Prop :=
  ∀ id : VarId, ∀ v : Val, env id = some v →
    ∃ n : UInt64, v = .u64 n ∧
      (st.lookupVar id).noUB = true ∧
      denoteSymExpr (SymValuation.ofVarEnv env) (st.lookupVar id).expr = .ok (.u64 n) ∧
      symExprScalarSort? st (st.lookupVar id).expr = some sortU64

/-- Predicate that a pure scalar expression uses only canonical 64-bit arithmetic, bitwise,
    and shift operators (`add`, `sub`, `mul`, `div`, `mod`, `bitAnd`, `bitOr`, `bitXor`,
    `shl`, `shr`, `clmul64`, `clmul64Hi`, `gf2Affine`, `eor3`, `not`, `neg`) over variables and 64-bit constants. -/
def isPureU64ScalarExpr : ScalarExpr → Bool
  | .constU64 _ | .var _ => true
  | .constBool _ | .select _ _ _ | .fma _ _ _ => false
  | .unaryOp .not a | .unaryOp .neg a => isPureU64ScalarExpr a
  | .unaryOp .clz256 _ => false
  | .binOp op l r =>
    (match op with
     | .add | .sub | .mul | .div | .mod | .bitAnd | .bitOr | .bitXor
     | .shl | .shr | .clmul64 | .clmul64Hi | .gf2Affine | .eor3 => true
     | .sar | .eq | .lt | .le | .addChecked256 | .subChecked256 | .mulChecked256 => false) &&
    isPureU64ScalarExpr l && isPureU64ScalarExpr r

/-- Predicate that a symbolic expression uses only canonical 64-bit arithmetic, bitwise,
    and shift operators over `u64`-bound symbolic variables in `vars` and 64-bit constants. -/
def isPureU64SymExprIn (vars : List VarId) : SymExpr → Bool
  | .constU64 _ => true
  | .symVar id => vars.contains id
  | .unaryOp .not a | .unaryOp .neg a => isPureU64SymExprIn vars a
  | .binOp op l r =>
    (match op with
     | .add | .sub | .mul | .div | .mod | .bitAnd | .bitOr | .bitXor
     | .shl | .shr | .clmul64 | .clmul64Hi | .gf2Affine | .eor3 => true
     | .sar | .eq | .lt | .le | .addChecked256 | .subChecked256 | .mulChecked256 => false) &&
    isPureU64SymExprIn vars l && isPureU64SymExprIn vars r
  | _ => false

/-- Every expression in `xs` denotes a `.bool` value under `ω`. -/
def allBoolAtoms (ω : SymValuation) : List SymExpr → Prop
  | [] => True
  | x :: xs => (∃ b : Bool, denoteSymExpr ω x = .ok (.bool b)) ∧ allBoolAtoms ω xs

/-- Conjunction evaluation of a list of boolean symbolic atoms under `ω`. -/
def evalBoolAtoms (ω : SymValuation) : List SymExpr → Except UBError Bool
  | [] => .ok true
  | x :: xs =>
    match denoteSymExpr ω x, evalBoolAtoms ω xs with
    | .ok (.bool b1), .ok b2 => .ok (b1 && b2)
    | .ok _, _ => .error (.typeError "evalBoolAtoms: non-bool atom")
    | .error err, _ => .error err

end LeanNative.Proofs
