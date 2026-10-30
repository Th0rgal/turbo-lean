import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval

namespace LCNF

open LeanNative.IR
open LeanNative.Semantics

/-!
# Formalized Lean 4 LCNF (`Lean.Compiler.LCNF`) Operational Subset (`LeanNative.IR.LCNF`)

Provides the formal syntax (`LCNF.LetValue`, `LCNF.Code`, `LCNF.Env`), independent operational
semantics (`LCNF.evalLetValue`, `LCNF.evalLCNF`), and partial lowering pass (`LCNF.lowerLetValue`,
`LCNF.lowerCode`) to `LNIRCode` for Milestone M4 (`lowerLCNFCode_sound`).
-/

/-- Formalized LCNF right-hand-side let-binding expressions (`LCNF.LetValue`). -/
inductive LetValue where
  | litU64          : UInt64 → LetValue
  | litBool         : Bool → LetValue
  | litU256         : UInt256 → LetValue
  | fvar            : VarId → LetValue
  | binOp           : BinOp → VarId → VarId → LetValue
  | unaryOp         : UnaryOp → VarId → LetValue
  | mkPair          : VarId → VarId → LetValue
  | projTuple       : VarId → Nat → LetValue
  | sarrayLen       : VarId → LetValue
  | sarrayGet       : VarId → VarId → LNIRType → LetValue
  | sarraySet       : VarId → VarId → VarId → LNIRType → LetValue
  | unsupportedCall : String → LetValue
  deriving Repr, Inhabited, BEq

/-- Formalized LCNF ANF code blocks (`LCNF.Code`).
    Note that `.casesBool discr falseBranch trueBranch` follows Lean LCNF `Bool` constructor
    ordering (`Bool.false` = ctor 0 first, `Bool.true` = ctor 1 second), whereas `LNIRCode.ite`
    orders `thenBranch` (`true`) before `elseBranch` (`false`). -/
inductive Code where
  | letBind   : VarId → LNIRType → LetValue → Code → Code
  | inc       : VarId → Nat → Code → Code
  | dec       : VarId → Nat → Code → Code
  | casesBool : VarId → Code → Code → Code
  | return    : VarId → Code
  | unreach   : Code
  deriving Repr, Inhabited, BEq

/-- LCNF variable environment mapping free variable IDs (`VarId`) to runtime values. -/
abbrev Env := VarId → Option Val

namespace Env

def bind (env : Env) (x : VarId) (v : Val) : Env :=
  fun y => if y == x then some v else env y

end Env

/-- Independent operational evaluation of `LCNF.LetValue` over `LCNF.Env` and `HeapState`. -/
def evalLetValue (env : Env) (st : HeapState) : LetValue → Except UBError (Val × HeapState)
  | .litU64 n => .ok (.u64 n, st)
  | .litBool b => .ok (.bool b, st)
  | .litU256 w => .ok (.u256 w, st)
  | .fvar x =>
    match env x with
    | some v => .ok (v, st)
    | none => .error (.unboundVar x)
  | .binOp op aVar bVar =>
    match env aVar, env bVar with
    | some va, some vb =>
      match evalBinOp op va vb with
      | .ok v => .ok (v, st)
      | .error err => .error err
    | none, _ => .error (.unboundVar aVar)
    | some _, none => .error (.unboundVar bVar)
  | .unaryOp op aVar =>
    match env aVar with
    | some va =>
      match evalUnaryOp op va with
      | .ok v => .ok (v, st)
      | .error err => .error err
    | none => .error (.unboundVar aVar)
  | .mkPair aVar bVar =>
    match env aVar, env bVar with
    | some va, some vb => .ok (.tuple [va, vb], st)
    | none, _ => .error (.unboundVar aVar)
    | some _, none => .error (.unboundVar bVar)
  | .projTuple tupleVar idx =>
    match env tupleVar with
    | some (.tuple vals) =>
      match vals[idx]? with
      | some v => .ok (v, st)
      | none => .error (.outOfBounds idx vals.length)
    | some (.objPtr objId) =>
      if st.getObjRefCount objId == 0 then .error (.useAfterFree objId)
      else match st.findObject objId with
      | some obj =>
        if idx == 0 then .ok (.u64 obj.tag.toUInt64, st)
        else .error (.outOfBounds idx 1)
      | none => .error (.useAfterFree objId)
    | some (.u64 v) =>
      if idx == 0 then .ok (.u64 v, st) else .error (.outOfBounds idx 1)
    | some _ => .error (.typeError "projTuple expects tuple value")
    | none => .error (.unboundVar tupleVar)
  | .sarrayLen arrVar =>
    match env arrVar with
    | some (.sarrayId bufId) =>
      match st.findBuffer bufId with
      | some buf => .ok (.u64 buf.data.size.toUInt64, st)
      | none => .error (.typeError s!"unknown sarray buffer {bufId}")
    | some _ => .error (.typeError "sarrayLen expects sarrayId")
    | none => .error (.unboundVar arrVar)
  | .sarrayGet arrVar idxVar _elemTy =>
    match env arrVar, env idxVar with
    | some (.sarrayId bufId), some (.u64 idx) =>
      match st.readElem bufId idx.toNat with
      | .ok v => .ok (.u64 v, st)
      | .error err => .error err
    | none, _ => .error (.unboundVar arrVar)
    | _, none => .error (.unboundVar idxVar)
    | _, _ => .error (.typeError "sarrayGet expects sarrayId and u64 index")
  | .sarraySet arrVar idxVar valVar _elemTy =>
    match env arrVar, env idxVar, env valVar with
    | some (.sarrayId bufId), some (.u64 idx), some (.u64 val) =>
      match st.ensureExclusive bufId with
      | .ok st1 =>
        match st1.writeElemExclusive bufId idx.toNat val with
        | .ok st2 => .ok (.sarrayId bufId, st2)
        | .error err => .error err
      | .error err => .error err
    | none, _, _ => .error (.unboundVar arrVar)
    | _, none, _ => .error (.unboundVar idxVar)
    | _, _, none => .error (.unboundVar valVar)
    | _, _, _ => .error (.typeError "sarraySet expects sarrayId, u64 index, and u64 value")
  | .unsupportedCall fnName =>
    .error (.unsupportedCall fnName)

/-- Independent operational evaluator for `LCNF.Code` (`evalLCNF`), defined directly on `LCNF.Code`
    without referencing `lowerCode` or `evalCode`. -/
def evalLCNF (env : Env) (st : HeapState) (code : Code) (fuel : Nat) : Except UBError (Val × HeapState) :=
  match code with
  | .letBind dst _ty val k =>
    match evalLetValue env st val with
    | .ok (v, st') => evalLCNF (Env.bind env dst v) st' k fuel
    | .error err => .error err
  | .inc objVar count k =>
    match st.evalIncRef env objVar count with
    | .ok st' => evalLCNF env st' k fuel
    | .error err => .error err
  | .dec objVar count k =>
    match st.evalDecRef env objVar count with
    | .ok st' => evalLCNF env st' k fuel
    | .error err => .error err
  | .casesBool discr falseBranch trueBranch =>
    match env discr with
    | some (.bool true) => evalLCNF env st trueBranch fuel
    | some (.bool false) => evalLCNF env st falseBranch fuel
    | some (.u64 n) =>
      if n != 0 then evalLCNF env st trueBranch fuel
      else evalLCNF env st falseBranch fuel
    | some (.u256 w) =>
      if w != UInt256.zero then evalLCNF env st trueBranch fuel
      else evalLCNF env st falseBranch fuel
    | some _ => .error (.typeError "ite condition must be bool, u64, or u64")
    | none => .error (.unboundVar discr)
  | .return v =>
    match env v with
    | some val => .ok (val, st)
    | none => .error (.unboundVar v)
  | .unreach =>
    .error (.typeError "reached unreachable code")

/-- Lower an `LCNF.LetValue` into an `LNIRExpr`, rejecting `.unsupportedCall` with a descriptive error. -/
def lowerLetValue : LetValue → Except String LNIRExpr
  | .litU64 n => .ok (.scalar (.constU64 n))
  | .litBool b => .ok (.scalar (.constBool b))
  | .litU256 w => .ok (.constU256 w)
  | .fvar x => .ok (.scalar (.var x))
  | .binOp op aVar bVar => .ok (.scalar (.binOp op (.var aVar) (.var bVar)))
  | .unaryOp op aVar => .ok (.scalar (.unaryOp op (.var aVar)))
  | .mkPair aVar bVar => .ok (.mkTuple [aVar, bVar])
  | .projTuple tupleVar idx => .ok (.projTuple tupleVar idx)
  | .sarrayLen arrVar => .ok (.sarrayLen arrVar)
  | .sarrayGet arrVar idxVar elemTy => .ok (.sarrayGet arrVar idxVar elemTy)
  | .sarraySet arrVar idxVar valVar elemTy => .ok (.sarraySet arrVar idxVar valVar elemTy)
  | .unsupportedCall fnName => .error s!"unsupported LCNF call: {fnName}"

/-- Lower an `LCNF.Code` block into `LNIRCode`, translating `.casesBool discr falseBranch trueBranch`
    into `.ite discr trueBranch' falseBranch'` and rejecting unsupported calls. -/
def lowerCode : Code → Except String LNIRCode
  | .letBind dst ty val k =>
    match lowerLetValue val, lowerCode k with
    | .ok expr, .ok k' => .ok (.letBind dst ty expr k')
    | .error err, _ => .error err
    | .ok _, .error err => .error err
  | .inc objVar count k =>
    match lowerCode k with
    | .ok k' => .ok (.incRef objVar count k')
    | .error err => .error err
  | .dec objVar count k =>
    match lowerCode k with
    | .ok k' => .ok (.decRef objVar count k')
    | .error err => .error err
  | .casesBool discr falseBranch trueBranch =>
    match lowerCode falseBranch, lowerCode trueBranch with
    | .ok fb', .ok tb' => .ok (.ite discr tb' fb')
    | .error err, _ => .error err
    | .ok _, .error err => .error err
  | .return v => .ok (.ret v)
  | .unreach => .ok .unreachable

end LCNF
