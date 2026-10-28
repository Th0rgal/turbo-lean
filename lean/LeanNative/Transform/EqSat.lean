import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.Proofs.PeepholeProofs
import LeanNative.Transform.Pass

namespace LeanNative.Transform

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Proofs

/-!
# Declarative Equality-Saturation / Rewrite Table Pass (`LeanNative.Transform.EqSat`)

Milestone M4 (Engine 1): Modularizes declarative expression rewrite rules (`VerifiedExprRule`)
and lifts them across all 9 `LNIRCode` constructors via `applyRewriteTable`, certified by
`LeanNative.Proofs.applyRewriteTable_sound` (`0 sorryAx`, `Contract V2`).
-/

/-- Canonical verified scalar peephole & binary constant-folding rule wrapped as a `VerifiedExprRule`. -/
def canonicalScalarVerifiedRule : VerifiedExprRule where
  name  := "CanonicalScalarPeepholeAndConstFold"
  apply := LeanNative.Proofs.rewriteLNIRExprVerified
  sound := LeanNative.Proofs.rewriteLNIRExprVerified_sound

/-- Default declarative rewrite table (`List VerifiedExprRule`) for `EqSat`. -/
def defaultEqSatRules : List VerifiedExprRule :=
  [canonicalScalarVerifiedRule]

/-- Apply the declarative `EqSat` rewrite table across an `LNIRCode` block. -/
def optimizeEqSatCode (rules : List VerifiedExprRule := defaultEqSatRules) (code : LNIRCode) : LNIRCode :=
  LeanNative.Proofs.applyRewriteTable rules code

/-- Machine-checked soundness theorem (`optimizeEqSatCode_sound`):
    for any rule table `rules : List VerifiedExprRule`, `optimizeEqSatCode rules code`
    refines `code` (`CodeRefines code (optimizeEqSatCode rules code)`). -/
theorem optimizeEqSatCode_sound (rules : List VerifiedExprRule) (code : LNIRCode) :
    CodeRefines code (optimizeEqSatCode rules code) :=
  LeanNative.Proofs.applyRewriteTable_sound rules code

/-- Machine-checked `VerifiedCodePassContract` (`Contract V2`) for the declarative `EqSat` pass. -/
def verifiedEqSatContract (rules : List VerifiedExprRule := defaultEqSatRules) : VerifiedCodePassContract where
  name       := "EqSat"
  theoremRef := "LeanNative.Proofs.applyRewriteTable_sound"
  notes      := "Declarative Equality-Saturation / VerifiedExprRule table congruence pass over LNIRCode"
  runCode    := optimizeEqSatCode rules
  sound      := optimizeEqSatCode_sound rules

/-- Verified `TransformPass` constructed directly from `verifiedEqSatContract`. -/
def eqSatPass (rules : List VerifiedExprRule := defaultEqSatRules) : TransformPass :=
  TransformPass.ofVerifiedContract (verifiedEqSatContract rules)

/-- Machine-checked theorem: `eqSatPass` refines the body of every declaration. -/
theorem eqSatPass_body_refines (rules : List VerifiedExprRule) (d : LNIRDecl) :
    CodeRefines d.body ((eqSatPass rules).runDecl d).1.body :=
  TransformPass.ofVerifiedContract_body_refines (verifiedEqSatContract rules) d

end LeanNative.Transform

namespace LeanNative.IR

def maxVarIdInScalarExpr : ScalarExpr → VarId
  | .constU64 _ | .constBool _ => 0
  | .var id => id
  | .binOp _ l r => max (maxVarIdInScalarExpr l) (maxVarIdInScalarExpr r)
  | .unaryOp _ a => maxVarIdInScalarExpr a
  | .select c t e => max (maxVarIdInScalarExpr c) (max (maxVarIdInScalarExpr t) (maxVarIdInScalarExpr e))
  | .fma a b c => max (maxVarIdInScalarExpr a) (max (maxVarIdInScalarExpr b) (maxVarIdInScalarExpr c))

def maxVarIdInExpr : LNIRExpr → VarId
  | .scalar se => maxVarIdInScalarExpr se
  | .constU256 _ => 0
  | .mkTuple vs => vs.foldl max 0
  | .allocCtor _ objs scals => max (objs.foldl max 0) (scals.foldl max 0)
  | .projTuple tv _ | .ctorGetObj tv _ | .ctorGetScalar tv _ _ | .isExclusive tv
  | .sarrayLen tv | .sarrayDataPtr tv _ | .sarrayEnsureExclusive tv _
  | .boxScalar tv _ | .unboxScalar tv _ => tv
  | .storageLoad pv iv | .sarrayGet pv iv _ | .rawLoad pv iv _ => max pv iv
  | .mulDivDown av bv cv | .mulDivUp av bv cv | .storageStore av bv cv | .sarraySet av bv cv _ =>
    max av (max bv cv)
  | .call _ args _ _ => args.foldl max 0

partial def maxVarIdInCode : LNIRCode → VarId
  | .letBind dst _ val k => max dst (max (maxVarIdInExpr val) (maxVarIdInCode k))
  | .rawStore pv iv vv _ k => max (max pv iv) (max vv (maxVarIdInCode k))
  | .incRef ov _ k | .decRef ov _ k => max ov (maxVarIdInCode k)
  | .ite cv t e => max cv (max (maxVarIdInCode t) (maxVarIdInCode e))
  | .seqFor iv lv hv av ai _ s k => max (max iv lv) (max (max hv av) (max ai (max (maxVarIdInCode s) (maxVarIdInCode k))))
  | .parFor ov lv ins _ _ k => max (max ov lv) (max (ins.foldl max 0) (maxVarIdInCode k))
  | .ret v => v
  | .unreachable => 0

def maxVarIdInDecl (d : LNIRDecl) : VarId :=
  max (d.params.foldl (fun acc p => max acc p.id) 0) (maxVarIdInCode d.body)

partial def codeCallsDecl (fnName : String) : LNIRCode → Bool
  | .letBind _ _ (.call callee _ _ _) k => callee == fnName || codeCallsDecl fnName k
  | .letBind _ _ _ k | .rawStore _ _ _ _ k | .incRef _ _ k | .decRef _ _ k | .parFor _ _ _ _ _ k => codeCallsDecl fnName k
  | .ite _ t e | .seqFor _ _ _ _ _ _ t e => codeCallsDecl fnName t || codeCallsDecl fnName e
  | .ret _ | .unreachable => false

/-- Strict eligibility check matching `spliceInlinedBody` 1-to-1: only accepts `.scalar`,
    `.mkTuple`, `.projTuple`, `.ite`, and `.ret` so unsupported forms are never dropped. -/
partial def isSimpleInlinableBody (_selfName : String) : LNIRCode → Bool
  | .letBind _ _ (.scalar _) k => isSimpleInlinableBody _selfName k
  | .letBind _ _ (.mkTuple _) k => isSimpleInlinableBody _selfName k
  | .letBind _ _ (.projTuple _ _) k => isSimpleInlinableBody _selfName k
  | .ite _ t e => isSimpleInlinableBody _selfName t && isSimpleInlinableBody _selfName e
  | .ret _ => true
  | _ => false

def renameScalarExpr (paramMap : List (VarId × VarId)) (offset : VarId) : ScalarExpr → ScalarExpr
  | .constU64 v => .constU64 v | .constBool b => .constBool b
  | .var id => .var ((paramMap.lookup id).getD (id + offset))
  | .binOp op l r => .binOp op (renameScalarExpr paramMap offset l) (renameScalarExpr paramMap offset r)
  | .unaryOp op a => .unaryOp op (renameScalarExpr paramMap offset a)
  | .select c t f => .select (renameScalarExpr paramMap offset c) (renameScalarExpr paramMap offset t) (renameScalarExpr paramMap offset f)
  | .fma a b c => .fma (renameScalarExpr paramMap offset a) (renameScalarExpr paramMap offset b) (renameScalarExpr paramMap offset c)

private def renameVarId (paramMap : List (VarId × VarId)) (offset : VarId) (v : VarId) : VarId :=
  (paramMap.lookup v).getD (v + offset)

partial def spliceInlinedBody (paramMap : List (VarId × VarId)) (offset : VarId)
    (dst : VarId) (dstTy : LNIRType) (cont : LNIRCode) : LNIRCode → LNIRCode
  | .letBind bDst bTy (.scalar se) k =>
    .letBind (bDst + offset) bTy (.scalar (renameScalarExpr paramMap offset se))
      (spliceInlinedBody paramMap offset dst dstTy cont k)
  | .letBind bDst bTy (.mkTuple fs) k =>
    .letBind (bDst + offset) bTy (.mkTuple (fs.map (renameVarId paramMap offset)))
      (spliceInlinedBody paramMap offset dst dstTy cont k)
  | .letBind bDst bTy (.projTuple tv idx) k =>
    .letBind (bDst + offset) bTy (.projTuple (renameVarId paramMap offset tv) idx)
      (spliceInlinedBody paramMap offset dst dstTy cont k)
  | .ite cv t e =>
    .ite (renameVarId paramMap offset cv)
      (spliceInlinedBody paramMap offset dst dstTy cont t)
      (spliceInlinedBody paramMap offset dst dstTy cont e)
  | .ret rv => .letBind dst dstTy (.scalar (.var (renameVarId paramMap offset rv))) cont
  | _ => cont

partial def inlineLocalHelperCalls (helpers : List LNIRDecl) (nextOffset : VarId) : LNIRCode → LNIRCode
  | .letBind dst ty (.call callee args retTy isExt) k =>
    if isExt then
      .letBind dst ty (.call callee args retTy isExt) (inlineLocalHelperCalls helpers (nextOffset + 128) k)
    else
      match helpers.find? (fun h => h.name == callee && h.params.length == args.length) with
      | some hDecl =>
        let stepSpan := maxVarIdInDecl hDecl + 128
        let k' := inlineLocalHelperCalls helpers (nextOffset + stepSpan) k
        spliceInlinedBody ((hDecl.params.map (·.id)).zip args) nextOffset dst ty k' hDecl.body
      | none =>
        .letBind dst ty (.call callee args retTy isExt) (inlineLocalHelperCalls helpers (nextOffset + 128) k)
  | .letBind dst ty val k => .letBind dst ty val (inlineLocalHelperCalls helpers nextOffset k)
  | .rawStore pv iv vv ty k => .rawStore pv iv vv ty (inlineLocalHelperCalls helpers nextOffset k)
  | .incRef ov c k => .incRef ov c (inlineLocalHelperCalls helpers nextOffset k)
  | .decRef ov c k => .decRef ov c (inlineLocalHelperCalls helpers nextOffset k)
  | .ite cv t e => .ite cv (inlineLocalHelperCalls helpers nextOffset t) (inlineLocalHelperCalls helpers (nextOffset + 256) e)
  | .seqFor iv lv hv av ai aty step k =>
    .seqFor iv lv hv av ai aty (inlineLocalHelperCalls helpers nextOffset step) (inlineLocalHelperCalls helpers (nextOffset + 256) k)
  | .parFor ov lv ins ety kern k => .parFor ov lv ins ety kern (inlineLocalHelperCalls helpers nextOffset k)
  | .ret v => .ret v
  | .unreachable => .unreachable

private def inlineLocalDefsOnce (m : LNIRModule) : LNIRModule :=
  let helpers := m.decls.filter (fun d => isSimpleInlinableBody d.name d.body)
  if helpers.isEmpty then m
  else
    let decls' := m.decls.map (fun d =>
      let baseOff := maxVarIdInDecl d + 1000
      { d with body := inlineLocalHelperCalls helpers baseOff d.body }
    )
    { m with decls := decls' }

def normalizeAndInlineLocalDefs (m : LNIRModule) : LNIRModule :=
  let m1 := inlineLocalDefsOnce m
  let m2 := inlineLocalDefsOnce m1
  let m3 := inlineLocalDefsOnce m2
  inlineLocalDefsOnce m3

end LeanNative.IR
