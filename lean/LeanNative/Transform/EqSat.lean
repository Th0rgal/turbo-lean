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

/-- Strict eligibility check matching `spliceInlinedBodyM` 1-to-1: accepts `.scalar`,
    `.mkTuple`, `.projTuple`, `.ctorGetObj`, `.incRef`, `.decRef`, `.ite`, `.ret`, and
    `.unreachable` so unsupported forms are never dropped. -/
partial def isSimpleInlinableBody (_selfName : String) : LNIRCode → Bool
  | .letBind _ _ (.scalar _) k | .letBind _ _ (.mkTuple _) k
  | .letBind _ _ (.projTuple _ _) k | .letBind _ _ (.ctorGetObj _ _) k
  | .incRef _ _ k | .decRef _ _ k => isSimpleInlinableBody _selfName k
  | .ite _ t e => isSimpleInlinableBody _selfName t && isSimpleInlinableBody _selfName e
  | .ret _ | .unreachable => true
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

partial def inferReturnedType : LNIRCode → Option LNIRType
  | .letBind dst ty _ (.ret rv) => if dst == rv then some ty else none
  | .letBind _ _ _ k | .rawStore _ _ _ _ k | .incRef _ _ k | .decRef _ _ k | .parFor _ _ _ _ _ k =>
    inferReturnedType k
  | .ite _ t e => inferReturnedType t <|> inferReturnedType e
  | _ => none

partial def spliceInlinedBodyM (paramMap : List (VarId × VarId)) (unboxedLocal : List VarId) (offset : VarId)
    (retCont : VarId → StateM VarId LNIRCode) : LNIRCode → StateM VarId LNIRCode
  | .letBind bDst bTy (.scalar se) k => do
    let isUbSe := match se with | .var sv => unboxedLocal.contains sv | _ => true
    let effBTy := if isUbSe && (bTy == .objPtr || bTy == .taggedPtr) then .i64 else bTy
    let ub' := if effBTy.isUnboxedScalar || isUbSe then bDst :: unboxedLocal else unboxedLocal
    return .letBind (bDst + offset) effBTy (.scalar (renameScalarExpr paramMap offset se))
      (← spliceInlinedBodyM paramMap ub' offset retCont k)
  | .letBind bDst bTy (.mkTuple fs) k => do
    return .letBind (bDst + offset) bTy (.mkTuple (fs.map (renameVarId paramMap offset)))
      (← spliceInlinedBodyM paramMap (bDst :: unboxedLocal) offset retCont k)
  | .letBind bDst bTy (.projTuple tv idx) k => do
    let isUbTv := unboxedLocal.contains tv
    let effBTy := if isUbTv && (bTy == .objPtr || bTy == .taggedPtr) then .i64 else bTy
    let ub' := if effBTy.isUnboxedScalar || isUbTv then bDst :: unboxedLocal else unboxedLocal
    return .letBind (bDst + offset) effBTy (.projTuple (renameVarId paramMap offset tv) idx)
      (← spliceInlinedBodyM paramMap ub' offset retCont k)
  | .letBind bDst bTy (.ctorGetObj cv idx) k => do
    return .letBind (bDst + offset) bTy (.ctorGetObj (renameVarId paramMap offset cv) idx)
      (← spliceInlinedBodyM paramMap unboxedLocal offset retCont k)
  | .incRef ov c k => do
    if unboxedLocal.contains ov then spliceInlinedBodyM paramMap unboxedLocal offset retCont k
    else return .incRef (renameVarId paramMap offset ov) c (← spliceInlinedBodyM paramMap unboxedLocal offset retCont k)
  | .decRef ov c k => do
    if unboxedLocal.contains ov then spliceInlinedBodyM paramMap unboxedLocal offset retCont k
    else return .decRef (renameVarId paramMap offset ov) c (← spliceInlinedBodyM paramMap unboxedLocal offset retCont k)
  | .ite cv t e => do
    return .ite (renameVarId paramMap offset cv)
      (← spliceInlinedBodyM paramMap unboxedLocal offset retCont t)
      (← spliceInlinedBodyM paramMap unboxedLocal offset retCont e)
  | .ret rv => retCont (renameVarId paramMap offset rv)
  | _ => return .unreachable

partial def freshenClonedCont (code : LNIRCode) (subst : List (VarId × VarId) := []) : StateM VarId LNIRCode := do
  let rwVar (v : VarId) : VarId := (subst.lookup v).getD v
  let rec rwScalar : ScalarExpr → ScalarExpr
    | .constU64 v => .constU64 v | .constBool b => .constBool b | .var id => .var (rwVar id)
    | .binOp op l r => .binOp op (rwScalar l) (rwScalar r) | .unaryOp op a => .unaryOp op (rwScalar a)
    | .select c t e => .select (rwScalar c) (rwScalar t) (rwScalar e)
    | .fma a b c => .fma (rwScalar a) (rwScalar b) (rwScalar c)
  let rwExpr : LNIRExpr → LNIRExpr
    | .scalar se => .scalar (rwScalar se) | .constU256 w => .constU256 w
    | .mulDivDown a b d => .mulDivDown (rwVar a) (rwVar b) (rwVar d)
    | .mulDivUp a b d => .mulDivUp (rwVar a) (rwVar b) (rwVar d)
    | .storageLoad m s => .storageLoad (rwVar m) (rwVar s)
    | .storageStore m s v => .storageStore (rwVar m) (rwVar s) (rwVar v)
    | .mkTuple fs => .mkTuple (fs.map rwVar) | .projTuple tv idx => .projTuple (rwVar tv) idx
    | .allocCtor tag ofs sfs => .allocCtor tag (ofs.map rwVar) (sfs.map rwVar)
    | .ctorGetObj cv idx => .ctorGetObj (rwVar cv) idx | .ctorGetScalar cv idx ty => .ctorGetScalar (rwVar cv) idx ty
    | .isExclusive ov => .isExclusive (rwVar ov) | .sarrayLen av => .sarrayLen (rwVar av)
    | .sarrayDataPtr av et => .sarrayDataPtr (rwVar av) et | .sarrayEnsureExclusive av et => .sarrayEnsureExclusive (rwVar av) et
    | .sarrayGet av iv et => .sarrayGet (rwVar av) (rwVar iv) et
    | .sarraySet av iv vv et => .sarraySet (rwVar av) (rwVar iv) (rwVar vv) et
    | .rawLoad pv iv et => .rawLoad (rwVar pv) (rwVar iv) et
    | .boxScalar vv ty => .boxScalar (rwVar vv) ty | .unboxScalar bv ty => .unboxScalar (rwVar bv) ty
    | .call fn args rty ext => .call fn (args.map rwVar) rty ext
  match code with
  | .letBind dst ty val k =>
    let val' := rwExpr val
    let freshDst ← get; set (freshDst + 1)
    return .letBind freshDst ty val' (← freshenClonedCont k ((dst, freshDst) :: subst))
  | .rawStore pv iv vv et k =>
    return .rawStore (rwVar pv) (rwVar iv) (rwVar vv) et (← freshenClonedCont k subst)
  | .incRef ov c k => return .incRef (rwVar ov) c (← freshenClonedCont k subst)
  | .decRef ov c k => return .decRef (rwVar ov) c (← freshenClonedCont k subst)
  | .ite cv t e =>
    return .ite (rwVar cv) (← freshenClonedCont t subst) (← freshenClonedCont e subst)
  | .seqFor iv lv hv av ai aty step k =>
    let fIv ← get; let fAv := fIv + 1; set (fIv + 2)
    return .seqFor fIv (rwVar lv) (rwVar hv) fAv (rwVar ai) aty
      (← freshenClonedCont step ((av, fAv) :: (iv, fIv) :: subst))
      (← freshenClonedCont k ((av, fAv) :: subst))
  | .parFor ov lv ins et kern k =>
    let fOv ← get; set (fOv + 1)
    let kern' ← match kern with
      | .customScalar idxVar inVars body => do
        let fIdx ← get
        let fIns := (List.range inVars.length).map (fun i => fIdx + 1 + i)
        set (fIdx + 1 + inVars.length)
        let kSubst := (inVars.zip fIns) ++ ((idxVar, fIdx) :: subst)
        let rec rwK : ScalarExpr → ScalarExpr
          | .constU64 v => .constU64 v | .constBool b => .constBool b | .var id => .var ((kSubst.lookup id).getD id)
          | .binOp op l r => .binOp op (rwK l) (rwK r) | .unaryOp op a => .unaryOp op (rwK a)
          | .select c t e => .select (rwK c) (rwK t) (rwK e) | .fma a b c => .fma (rwK a) (rwK b) (rwK c)
        pure (.customScalar fIdx fIns (rwK body))
      | other => pure other
    return .parFor fOv (rwVar lv) (ins.map rwVar) et kern' (← freshenClonedCont k ((ov, fOv) :: subst))
  | .ret v => return .ret (rwVar v)
  | .unreachable => return .unreachable

partial def codeNodeSize : LNIRCode → Nat
  | .letBind _ _ _ k | .rawStore _ _ _ _ k | .incRef _ _ k | .decRef _ _ k | .parFor _ _ _ _ _ k => 1 + codeNodeSize k
  | .ite _ t e | .seqFor _ _ _ _ _ _ t e => 1 + codeNodeSize t + codeNodeSize e
  | .ret _ | .unreachable => 1

partial def codeHasIte : LNIRCode → Bool
  | .ite _ _ _ => true
  | .letBind _ _ _ k | .rawStore _ _ _ _ k | .incRef _ _ k | .decRef _ _ k | .parFor _ _ _ _ _ k => codeHasIte k
  | .seqFor _ _ _ _ _ _ t e => codeHasIte t || codeHasIte e
  | .ret _ | .unreachable => false

private def copyReturnedResultM (dst : VarId) (dstTy : LNIRType) (unboxedVars : List VarId)
    (cont : LNIRCode) (rv' : VarId) : StateM VarId LNIRCode := do
  let freshDst ← get; set (freshDst + 1)
  let cont' ← freshenClonedCont cont [(dst, freshDst)]
  match dstTy with
  | .tuple fieldTys =>
    let base ← get
    set (base + fieldTys.length + 1)
    let projVars := (List.range fieldTys.length).map (fun i => base + i)
    return (projVars.zip (fieldTys.zip (List.range fieldTys.length))).foldr
      (fun (pv, (fty, idx)) acc => .letBind pv fty (.projTuple rv' idx) acc)
      (.letBind freshDst dstTy (.mkTuple projVars) cont')
  | _ =>
    let effDstTy := if unboxedVars.contains dst && !dstTy.isUnboxedScalar then .i64 else dstTy
    return .letBind freshDst effDstTy (.scalar (.var rv')) cont'

partial def inlineLocalHelperCallsM (helpers : List LNIRDecl)
    (tupleAliases : List (VarId × LNIRType) := []) (unboxedVars : List VarId := []) :
    LNIRCode → StateM VarId LNIRCode
  | .letBind dst ty (.call callee args retTy isExt) k => do
    if isExt then
      return .letBind dst ty (.call callee args retTy isExt) (← inlineLocalHelperCallsM helpers tupleAliases unboxedVars k)
    else
      match helpers.find? (fun h => h.name == callee && h.params.length == args.length) with
      | some hDecl =>
        let effTy := match inferReturnedType hDecl.body with | some (.tuple fs) => .tuple fs | _ => ty
        let unboxed' := if effTy.isUnboxedScalar || effTy matches (.tuple _) then dst :: unboxedVars else unboxedVars
        if codeHasIte hDecl.body && codeNodeSize hDecl.body * codeNodeSize k > 65536 then
          return .letBind dst ty (.call callee args retTy isExt) (← inlineLocalHelperCallsM helpers tupleAliases unboxedVars k)
        let aliases' := match effTy with | .tuple _ => (dst, effTy) :: tupleAliases | _ => tupleAliases
        let k' ← inlineLocalHelperCallsM helpers aliases' unboxed' k
        if codeHasIte hDecl.body && codeNodeSize hDecl.body * codeNodeSize k' > 65536 then
          let kUnaliased ← inlineLocalHelperCallsM helpers tupleAliases unboxedVars k
          return .letBind dst ty (.call callee args retTy isExt) kUnaliased
        let curOffset ← get
        let bodyMax := maxVarIdInDecl hDecl
        set (curOffset + bodyMax + 16)
        let paramMap := (hDecl.params.map (·.id)).zip args
        let unboxedParams := (hDecl.params.zip args).filterMap fun (p, a) =>
          if unboxedVars.contains a || p.ty.isUnboxedScalar then some p.id else none
        spliceInlinedBodyM paramMap unboxedParams curOffset (copyReturnedResultM dst effTy unboxed' k') hDecl.body
      | none =>
        return .letBind dst ty (.call callee args retTy isExt) (← inlineLocalHelperCallsM helpers tupleAliases unboxedVars k)
  | .letBind dst ty (.ctorGetObj cv idx) k => do
    let val' := if (tupleAliases.lookup cv).isSome then LNIRExpr.projTuple cv idx else .ctorGetObj cv idx
    let ty' := match tupleAliases.lookup cv with | some (.tuple fs) => fs[idx]?.getD ty | _ => ty
    let unboxed' := if ty'.isUnboxedScalar then dst :: unboxedVars else unboxedVars
    return .letBind dst ty' val' (← inlineLocalHelperCallsM helpers tupleAliases unboxed' k)
  | .incRef ov c k => do
    if (tupleAliases.lookup ov).isSome || unboxedVars.contains ov then
      inlineLocalHelperCallsM helpers tupleAliases unboxedVars k
    else return .incRef ov c (← inlineLocalHelperCallsM helpers tupleAliases unboxedVars k)
  | .decRef ov c k => do
    if (tupleAliases.lookup ov).isSome || unboxedVars.contains ov then
      inlineLocalHelperCallsM helpers tupleAliases unboxedVars k
    else return .decRef ov c (← inlineLocalHelperCallsM helpers tupleAliases unboxedVars k)
  | .letBind dst ty val k => do
    let isUbVal := match val with
      | .scalar (.var sv) => unboxedVars.contains sv
      | .scalar _ | .mkTuple _ => true
      | .projTuple tv idx =>
        match tupleAliases.lookup tv with
        | some (.tuple fs) => (fs[idx]?.getD ty).isUnboxedScalar
        | _ => ty.isUnboxedScalar
      | _ => false
    let ty' := if isUbVal && (ty == .objPtr || ty == .taggedPtr) then .i64 else ty
    let unboxed' := if ty'.isUnboxedScalar || ty' matches (.tuple _) || isUbVal then dst :: unboxedVars else unboxedVars
    return .letBind dst ty' val (← inlineLocalHelperCallsM helpers tupleAliases unboxed' k)
  | .rawStore pv iv vv ty k => return .rawStore pv iv vv ty (← inlineLocalHelperCallsM helpers tupleAliases unboxedVars k)
  | .ite cv t e =>
    return .ite cv (← inlineLocalHelperCallsM helpers tupleAliases unboxedVars t) (← inlineLocalHelperCallsM helpers tupleAliases unboxedVars e)
  | .seqFor iv lv hv av ai aty step k =>
    return .seqFor iv lv hv av ai aty
      (← inlineLocalHelperCallsM helpers tupleAliases (iv :: unboxedVars) step)
      (← inlineLocalHelperCallsM helpers tupleAliases unboxedVars k)
  | .parFor ov lv ins ety kern k => return .parFor ov lv ins ety kern (← inlineLocalHelperCallsM helpers tupleAliases unboxedVars k)
  | .ret v => return .ret v
  | .unreachable => return .unreachable

def inlineLocalHelperCalls (helpers : List LNIRDecl) (initUnboxed : List VarId) (nextOffset : VarId) (c : LNIRCode) : LNIRCode :=
  (inlineLocalHelperCallsM helpers [] initUnboxed c).run' nextOffset

private def inlineLocalDefsOnce (m : LNIRModule) : LNIRModule :=
  let helpers := m.decls.filter (fun d => isSimpleInlinableBody d.name d.body)
  if helpers.isEmpty then m
  else
    let decls' := m.decls.map (fun d =>
      let initUb := d.params.filterMap fun p => if p.ty.isUnboxedScalar || p.ty matches (.tuple _) then some p.id else none
      let baseOff := maxVarIdInDecl d + 1000
      { d with body := inlineLocalHelperCalls helpers initUb baseOff d.body }
    )
    { m with decls := decls' }

partial def scalarExprIsTrapFree : ScalarExpr → Bool
  | .constU64 _ | .constBool _ | .var _ => true
  | .binOp .div _ _ | .binOp .mod _ _
  | .binOp .addChecked256 _ _ | .binOp .subChecked256 _ _ | .binOp .mulChecked256 _ _ => false
  | .binOp _ l r => scalarExprIsTrapFree l && scalarExprIsTrapFree r
  | .unaryOp _ a => scalarExprIsTrapFree a
  | .select c t e | .fma c t e => scalarExprIsTrapFree c && scalarExprIsTrapFree t && scalarExprIsTrapFree e

partial def compressTupleIteCodeAux (tupEnv : List (VarId × List VarId)) :
    LNIRCode → StateM VarId (Option (List LNIRType × List (VarId × LNIRType × ScalarExpr) × List ScalarExpr))
  | .letBind dst (.tuple fTys) (.mkTuple fVars) (.ret rv) => do
    if dst == rv && !fTys.isEmpty && fTys.length == fVars.length &&
        fTys.all (fun t => t.isUnboxedScalar || t == .taggedPtr) then
      return some (fTys, [], fVars.map .var)
    else return none
  | .letBind dst (.tuple fTys) (.mkTuple fVars) rest => do
    if !fTys.isEmpty && fTys.length == fVars.length &&
        fTys.all (fun t => t.isUnboxedScalar || t == .taggedPtr) then
      compressTupleIteCodeAux ((dst, fVars) :: tupEnv) rest
    else return none
  | .letBind dst ty (.projTuple tv idx) rest => do
    match (tupEnv.lookup tv).bind (·[idx]?) with
    | some srcVar =>
      let some (fTys, binds, exprs) ← compressTupleIteCodeAux tupEnv rest | return none
      return some (fTys, (dst, ty, .var srcVar) :: binds, exprs)
    | none => return none
  | .letBind dst ty (.scalar se) rest => do
    if scalarExprIsTrapFree se then
      let some (fTys, binds, exprs) ← compressTupleIteCodeAux tupEnv rest | return none
      return some (fTys, (dst, ty, se) :: binds, exprs)
    else return none
  | .incRef _ _ rest | .decRef _ _ rest => compressTupleIteCodeAux tupEnv rest
  | .ite cv t e => do
    let some (tTys, tBinds, tExprs) ← compressTupleIteCodeAux tupEnv t | return none
    let some (eTys, eBinds, eExprs) ← compressTupleIteCodeAux tupEnv e | return none
    if tTys.length != eTys.length || tExprs.length != eExprs.length then return none
    let boundT := tBinds.map fun (d, _, _) => d
    if !(eBinds.all fun (d, _, _) => !boundT.contains d) then return none
    let mut selBinds : List (VarId × LNIRType × ScalarExpr) := []
    let mut selExprs : List ScalarExpr := []
    for ((tt, et), (te, ee)) in (tTys.zip eTys).zip (tExprs.zip eExprs) do
      let oTy := if tt == et && tt.isUnboxedScalar then tt else .i64
      let sv ← get; set (sv + 1)
      selBinds := selBinds ++ [(sv, oTy, .select (.var cv) te ee)]
      selExprs := selExprs ++ [.var sv]
    let outTys := (tTys.zip eTys).map fun (tt, et) => if tt == et && tt.isUnboxedScalar then tt else .i64
    return some (outTys, tBinds ++ eBinds ++ selBinds, selExprs)
  | _ => return none

def compressTupleIteCodeM (c : LNIRCode) := compressTupleIteCodeAux [] c

def flattenInlinedHelperBody (d : LNIRDecl) : LNIRDecl :=
  if !codeHasIte d.body then d
  else
    let startId := maxVarIdInDecl d + 16
    match (compressTupleIteCodeM d.body).run startId with
    | (some (outTys, binds, exprs), nextId) =>
      let fieldVars := (List.range exprs.length).map (fun i => nextId + i)
      let tupVar := nextId + exprs.length
      let copyTail := ((fieldVars.zip outTys).zip exprs).foldr
        (fun ((fv, fty), fe) acc => LNIRCode.letBind fv fty (.scalar fe) acc)
        (.letBind tupVar (.tuple outTys) (.mkTuple fieldVars) (.ret tupVar))
      { d with body := binds.foldr (fun (dst, ty, se) acc => .letBind dst ty (.scalar se) acc) copyTail }
    | (none, _) => d

def normalizeAndInlineLocalDefs (m : LNIRModule) : LNIRModule :=
  let step (cur : LNIRModule) : LNIRModule :=
    let helpers := cur.decls.filter (fun d => isSimpleInlinableBody d.name d.body)
    if helpers.isEmpty then cur
    else
      { cur with decls := cur.decls.map fun d =>
        let initUb := d.params.filterMap fun p => if p.ty.isUnboxedScalar || p.ty matches (.tuple _) then some p.id else none
        let cand := inlineLocalHelperCalls helpers initUb (maxVarIdInDecl d + 1000) d.body
        let d' := if codeNodeSize cand > 16384 then d else { d with body := cand }
        flattenInlinedHelperBody d' }
  let rec loop (fuel : Nat) (cur : LNIRModule) : LNIRModule :=
    match fuel with
    | 0 => cur
    | f + 1 =>
      let next := step cur
      if next == cur then cur else loop f next
  loop 6 m

end LeanNative.IR
