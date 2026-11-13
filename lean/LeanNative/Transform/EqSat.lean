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
  | .letBind _ _ (.call fn _ _ false) k => fn != _selfName && isSimpleInlinableBody _selfName k
  | .seqFor _ _ _ _ _ _ step k => isSimpleInlinableBody _selfName step && isSimpleInlinableBody _selfName k
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
    let paramMap' := paramMap.filter fun (kId, _) => kId != bDst
    return .letBind (bDst + offset) effBTy (.scalar (renameScalarExpr paramMap offset se))
      (← spliceInlinedBodyM paramMap' ub' offset retCont k)
  | .letBind bDst bTy (.mkTuple fs) k => do
    let paramMap' := paramMap.filter fun (kId, _) => kId != bDst
    return .letBind (bDst + offset) bTy (.mkTuple (fs.map (renameVarId paramMap offset)))
      (← spliceInlinedBodyM paramMap' (bDst :: unboxedLocal) offset retCont k)
  | .letBind bDst bTy (.projTuple tv idx) k => do
    let isUbTv := unboxedLocal.contains tv
    let effBTy := if isUbTv && (bTy == .objPtr || bTy == .taggedPtr) then .i64 else bTy
    let ub' := if effBTy.isUnboxedScalar || isUbTv then bDst :: unboxedLocal else unboxedLocal
    let paramMap' := paramMap.filter fun (kId, _) => kId != bDst
    return .letBind (bDst + offset) effBTy (.projTuple (renameVarId paramMap offset tv) idx)
      (← spliceInlinedBodyM paramMap' ub' offset retCont k)
  | .letBind bDst bTy (.ctorGetObj cv idx) k => do
    let paramMap' := paramMap.filter fun (kId, _) => kId != bDst
    return .letBind (bDst + offset) bTy (.ctorGetObj (renameVarId paramMap offset cv) idx)
      (← spliceInlinedBodyM paramMap' unboxedLocal offset retCont k)
  | .letBind bDst bTy (.call fn args rty ext) k => do
    let paramMap' := paramMap.filter fun (v, _) => v != bDst
    return .letBind (bDst + offset) bTy (.call fn (args.map (renameVarId paramMap offset)) rty ext)
      (← spliceInlinedBodyM paramMap' unboxedLocal offset retCont k)
  | .seqFor iv lo hi av ai aty step k => do
    let iv' := iv + offset
    let av' := av + offset
    let loopMap := (iv, iv') :: (av, av') :: paramMap
    let step' ← spliceInlinedBodyM loopMap (iv :: unboxedLocal) offset (fun v => pure (.ret v)) step
    let k' ← spliceInlinedBodyM ((av, av') :: paramMap) unboxedLocal offset retCont k
    return .seqFor iv' (renameVarId paramMap offset lo) (renameVarId paramMap offset hi)
      av' (renameVarId paramMap offset ai) aty step' k'
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

def freshenClonedCont (code : LNIRCode) (subst : List (VarId × VarId) := []) :
    StateM VarId LNIRCode :=
  code.freshenBinders subst

abbrev codeNodeSize : LNIRCode → Nat := LNIRCode.nodeSize

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
    return .ite cv
      (← inlineLocalHelperCallsM helpers tupleAliases unboxedVars t)
      (← inlineLocalHelperCallsM helpers tupleAliases unboxedVars e)
  | .seqFor iv lv hv av ai aty step k =>
    return .seqFor iv lv hv av ai aty
      (← inlineLocalHelperCallsM helpers tupleAliases (iv :: unboxedVars) step)
      (← inlineLocalHelperCallsM helpers tupleAliases unboxedVars k)
  | .parFor ov lv ins ety kern k => return .parFor ov lv ins ety kern (← inlineLocalHelperCallsM helpers tupleAliases unboxedVars k)
  | .ret v => return .ret v
  | .unreachable => return .unreachable

def inlineLocalHelperCalls (helpers : List LNIRDecl) (initUnboxed : List VarId) (nextOffset : VarId) (c : LNIRCode) : LNIRCode :=
  (inlineLocalHelperCallsM helpers [] initUnboxed c).run' nextOffset

partial def scalarExprIsTrapFree : ScalarExpr → Bool
  | .constU64 _ | .constBool _ | .var _ => true
  | .binOp .div _ _ | .binOp .mod _ _
  | .binOp .addChecked256 _ _ | .binOp .subChecked256 _ _ | .binOp .mulChecked256 _ _ => false
  | .binOp _ l r => scalarExprIsTrapFree l && scalarExprIsTrapFree r
  | .unaryOp _ a => scalarExprIsTrapFree a
  | .select c t e | .fma c t e => scalarExprIsTrapFree c && scalarExprIsTrapFree t && scalarExprIsTrapFree e

private def freeVarsScalarExpr (bound : List VarId) (acc : List VarId) : ScalarExpr → List VarId
  | .constU64 _ | .constBool _ => acc
  | .var id => if bound.contains id || acc.contains id then acc else id :: acc
  | .binOp _ l r => freeVarsScalarExpr bound (freeVarsScalarExpr bound acc l) r
  | .unaryOp _ a => freeVarsScalarExpr bound acc a
  | .select c t e | .fma c t e =>
    freeVarsScalarExpr bound (freeVarsScalarExpr bound (freeVarsScalarExpr bound acc c) t) e

private def freeVarsExpr (bound : List VarId) (acc : List VarId) : LNIRExpr → List VarId
  | .scalar se => freeVarsScalarExpr bound acc se
  | .constU256 _ => acc
  | .mkTuple vs => vs.foldl (fun a v => if bound.contains v || a.contains v then a else v :: a) acc
  | .allocCtor _ objs scals =>
    (objs ++ scals).foldl (fun a v => if bound.contains v || a.contains v then a else v :: a) acc
  | .projTuple tv _ | .ctorGetObj tv _ | .ctorGetScalar tv _ _ | .isExclusive tv
  | .sarrayLen tv | .sarrayDataPtr tv _ | .sarrayEnsureExclusive tv _
  | .boxScalar tv _ | .unboxScalar tv _ =>
    if bound.contains tv || acc.contains tv then acc else tv :: acc
  | .storageLoad pv iv | .sarrayGet pv iv _ | .rawLoad pv iv _ =>
    [pv, iv].foldl (fun a v => if bound.contains v || a.contains v then a else v :: a) acc
  | .mulDivDown av bv cv | .mulDivUp av bv cv | .storageStore av bv cv | .sarraySet av bv cv _ =>
    [av, bv, cv].foldl (fun a v => if bound.contains v || a.contains v then a else v :: a) acc
  | .call _ args _ _ =>
    args.foldl (fun a v => if bound.contains v || a.contains v then a else v :: a) acc

partial def freeVarsInCode (bound : List VarId := []) (acc : List VarId := []) : LNIRCode → List VarId
  | .letBind dst _ val k =>
    let acc1 := freeVarsExpr bound acc val
    freeVarsInCode (dst :: bound) acc1 k
  | .rawStore pv iv vv _ k =>
    let acc1 := [pv, iv, vv].foldl (fun a v => if bound.contains v || a.contains v then a else v :: a) acc
    freeVarsInCode bound acc1 k
  | .incRef ov _ k | .decRef ov _ k =>
    let acc1 := if bound.contains ov || acc.contains ov then acc else ov :: acc
    freeVarsInCode bound acc1 k
  | .ite cv t e =>
    let acc1 := if bound.contains cv || acc.contains cv then acc else cv :: acc
    freeVarsInCode bound (freeVarsInCode bound acc1 t) e
  | .seqFor iv lv hv av ai _ s k =>
    let acc1 := [lv, hv, ai].foldl (fun a v => if bound.contains v || a.contains v then a else v :: a) acc
    let acc2 := freeVarsInCode (iv :: av :: bound) acc1 s
    freeVarsInCode (av :: bound) acc2 k
  | .parFor ov lv ins _ _ k =>
    let acc1 := (lv :: ins).foldl (fun a v => if bound.contains v || a.contains v then a else v :: a) acc
    freeVarsInCode (ov :: bound) acc1 k
  | .ret v => if bound.contains v || acc.contains v then acc else v :: acc
  | .unreachable => acc

partial def compressTupleIteCodeAux (tupEnv : List (VarId × List VarId)) (forbid : List VarId) :
    LNIRCode → StateM VarId (Option (List LNIRType × List (VarId × LNIRType × ScalarExpr) × List ScalarExpr))
  | .letBind dst (.tuple fTys) (.mkTuple fVars) (.ret rv) => do
    if dst == rv && !fTys.isEmpty && fTys.length == fVars.length &&
        fTys.all (fun t => t.isUnboxedScalar || t == .taggedPtr) then
      return some (fTys, [], fVars.map .var)
    else return none
  | .letBind dst (.tuple fTys) (.mkTuple fVars) rest => do
    if !forbid.contains dst && !fTys.isEmpty && fTys.length == fVars.length &&
        fTys.all (fun t => t.isUnboxedScalar || t == .taggedPtr) then
      compressTupleIteCodeAux ((dst, fVars) :: tupEnv) (dst :: forbid) rest
    else return none
  | .letBind dst ty (.projTuple tv idx) rest => do
    if forbid.contains dst then return none
    match (tupEnv.lookup tv).bind (·[idx]?) with
    | some srcVar =>
      let some (fTys, binds, exprs) ← compressTupleIteCodeAux tupEnv (dst :: forbid) rest | return none
      if binds.any (fun (d, _, _) => d == dst) then return none
      return some (fTys, (dst, ty, .var srcVar) :: binds, exprs)
    | none => return none
  | .letBind dst ty (.scalar se) rest => do
    if !forbid.contains dst && scalarExprIsTrapFree se then
      let some (fTys, binds, exprs) ← compressTupleIteCodeAux tupEnv (dst :: forbid) rest | return none
      if binds.any (fun (d, _, _) => d == dst) then return none
      return some (fTys, (dst, ty, se) :: binds, exprs)
    else return none
  | .incRef _ _ rest | .decRef _ _ rest => compressTupleIteCodeAux tupEnv forbid rest
  | .ite cv t e => do
    let forbid' := if forbid.contains cv then forbid else cv :: forbid
    let some (tTys, tBinds, tExprs) ← compressTupleIteCodeAux tupEnv forbid' t | return none
    let forbidE := tBinds.foldl (fun acc (d, _, _) => if acc.contains d then acc else d :: acc) forbid'
    let some (eTys, eBinds, eExprs) ← compressTupleIteCodeAux tupEnv forbidE e | return none
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

def compressTupleIteCodeM (forbid : List VarId) (c : LNIRCode) := compressTupleIteCodeAux [] forbid c

def compressScalarIteCodeAux (forbid : List VarId) :
    LNIRCode → StateM VarId (Option (LNIRType × List (VarId × LNIRType × ScalarExpr) × ScalarExpr))
  | .ret rv => return some (.i64, [], .var rv)
  | .letBind dst ty (.scalar se) rest => do
    if !forbid.contains dst && ty.isUnboxedScalar && scalarExprIsTrapFree se then
      let some (rTy, binds, expr) ← compressScalarIteCodeAux (dst :: forbid) rest | return none
      if binds.any (fun (d, _, _) => d == dst) then return none
      let effRTy := if rest matches (.ret _) && rTy == .i64 then ty else rTy
      return some (effRTy, (dst, ty, se) :: binds, expr)
    else return none
  | .incRef _ _ rest | .decRef _ _ rest => compressScalarIteCodeAux forbid rest
  | .ite cv t e => do
    let forbid' := if forbid.contains cv then forbid else cv :: forbid
    let some (tTy, tBinds, tExpr) ← compressScalarIteCodeAux forbid' t | return none
    let forbidE := tBinds.foldl (fun acc (d, _, _) => if acc.contains d then acc else d :: acc) forbid'
    let some (eTy, eBinds, eExpr) ← compressScalarIteCodeAux forbidE e | return none
    let boundT := tBinds.map fun (d, _, _) => d
    if !(eBinds.all fun (d, _, _) => !boundT.contains d) then return none
    let oTy := if tTy == eTy && tTy.isUnboxedScalar then tTy else .i64
    let sv ← get; set (sv + 1)
    return some (oTy, tBinds ++ eBinds ++ [(sv, oTy, .select (.var cv) tExpr eExpr)], .var sv)
  | _ => return none

private def substScalarExprVars (subst : List (VarId × ScalarExpr)) : ScalarExpr → ScalarExpr
  | .constU64 v => .constU64 v
  | .constBool b => .constBool b
  | .var id => (subst.lookup id).getD (.var id)
  | .binOp op l r => .binOp op (substScalarExprVars subst l) (substScalarExprVars subst r)
  | .unaryOp op a => .unaryOp op (substScalarExprVars subst a)
  | .select c t e =>
    .select (substScalarExprVars subst c) (substScalarExprVars subst t) (substScalarExprVars subst e)
  | .fma a b c =>
    .fma (substScalarExprVars subst a) (substScalarExprVars subst b) (substScalarExprVars subst c)

private def scalarExprRefs (acc : List VarId) : ScalarExpr → List VarId
  | .constU64 _ | .constBool _ => acc
  | .var id => id :: acc
  | .binOp _ l r => scalarExprRefs (scalarExprRefs acc l) r
  | .unaryOp _ a => scalarExprRefs acc a
  | .select c t e | .fma c t e => scalarExprRefs (scalarExprRefs (scalarExprRefs acc c) t) e

private def dedupAndPruneScalarBinds
    (binds : List (VarId × LNIRType × ScalarExpr)) (roots : List VarId)
    : List (VarId × LNIRType × ScalarExpr) × List (VarId × ScalarExpr) :=
  let initAcc : List (VarId × LNIRType × ScalarExpr) × List (VarId × ScalarExpr) × List (LNIRType × ScalarExpr × VarId) :=
    ([], [], [])
  let (keptRev, subst, _) := binds.foldl
    (fun (accBinds, curSubst, seenExprs) (dst, ty, se) =>
      let se' := match substScalarExprVars curSubst se with
        | .select (.constBool true) t _ => t
        | .select (.constBool false) _ e => e
        | .select (.constU64 c) t e => if c != 0 then t else e
        | .select _ t e => if t == e then t else substScalarExprVars curSubst se
        | other => other
      match se' with
      | .constU64 _ | .constBool _ | .var _ =>
        (accBinds, (dst, se') :: curSubst, seenExprs)
      | _ =>
        match seenExprs.find? (fun (t0, e0, _) => t0 == ty && e0 == se') with
        | some (_, _, prevDst) =>
          (accBinds, (dst, .var prevDst) :: curSubst, seenExprs)
        | none =>
          ((dst, ty, se') :: accBinds, curSubst, (ty, se', dst) :: seenExprs))
    initAcc
  let mappedRoots : List VarId := roots.foldl (fun acc r => scalarExprRefs acc ((subst.lookup r).getD (.var r))) []
  let initLive : List VarId × List (VarId × LNIRType × ScalarExpr) := (mappedRoots, [])
  let (_, liveBinds) := keptRev.foldl
    (fun (liveSet, out) (dst, ty, se) =>
      if liveSet.contains dst then
        (scalarExprRefs liveSet se, (dst, ty, se) :: out)
      else (liveSet, out))
    initLive
  (liveBinds, subst)

private def gateDeclWithSymbolicTV (src cand : LNIRDecl) : LNIRDecl :=
  if cand.body == src.body then src
  else if (LeanNative.Proofs.validateTranslationDecl src cand 64).passed then
    let effAssurance := AssuranceLevel.combine src.assurance .translationValidated
    { cand with assurance := effAssurance }
  else src

def flattenInlinedHelperBody (d : LNIRDecl) : LNIRDecl :=
  if !codeHasIte d.body then d
  else
    let initForbid := freeVarsInCode [] (d.params.map (·.id)) d.body
    let candDecl :=
      if d.retTy matches (.tuple _) then
        let startId := maxVarIdInDecl d + 16
        match (compressTupleIteCodeM initForbid d.body).run startId with
        | (some (outTys, binds, exprs), nextId) =>
          let fieldVars := (List.range exprs.length).map (fun i => nextId + i)
          let tupVar := nextId + exprs.length
          let allBinds := binds ++ ((fieldVars.zip outTys).zip exprs).map fun ((fv, fty), fe) => (fv, fty, fe)
          let (pruned, subst) := dedupAndPruneScalarBinds allBinds fieldVars
          let finalFieldVars := fieldVars.map fun fv =>
            match subst.lookup fv with
            | some (.var sv) => sv
            | _ => fv
          let needCopyBinds := (fieldVars.zip outTys).filterMap fun (fv, fty) =>
            match subst.lookup fv with
            | some (.constU64 v) => some (fv, fty, ScalarExpr.constU64 v)
            | some (.constBool b) => some (fv, fty, ScalarExpr.constBool b)
            | _ => none
          let tail := LNIRCode.letBind tupVar (.tuple outTys) (.mkTuple finalFieldVars) (.ret tupVar)
          { d with body := (pruned ++ needCopyBinds).foldr (fun (dst, ty, se) acc => LNIRCode.letBind dst ty (.scalar se) acc) tail }
        | (none, _) => d
      else if d.retTy.isUnboxedScalar then
        let startId := maxVarIdInDecl d + 16
        match (compressScalarIteCodeAux initForbid d.body).run startId with
        | (some (_, binds, resExpr), nextId) =>
          let allBinds := binds ++ [(nextId, d.retTy, resExpr)]
          let (pruned, subst) := dedupAndPruneScalarBinds allBinds [nextId]
          match subst.lookup nextId with
          | some (.var rv) =>
            { d with body := pruned.foldr (fun (dst, ty, se) acc => LNIRCode.letBind dst ty (.scalar se) acc) (.ret rv) }
          | some finalExpr =>
            let tail := LNIRCode.letBind nextId d.retTy (.scalar finalExpr) (.ret nextId)
            { d with body := pruned.foldr (fun (dst, ty, se) acc => LNIRCode.letBind dst ty (.scalar se) acc) tail }
          | none =>
            { d with body := pruned.foldr (fun (dst, ty, se) acc => LNIRCode.letBind dst ty (.scalar se) acc) (.ret nextId) }
        | (none, _) => d
      else d
    gateDeclWithSymbolicTV d candDecl

def normalizeAndInlineLocalDefs (m : LNIRModule) : LNIRModule :=
  let step (cur : LNIRModule) : LNIRModule :=
    let helpers := (cur.decls.filter (fun d => isSimpleInlinableBody d.name d.body)).map flattenInlinedHelperBody
    if helpers.isEmpty then cur
    else
      { cur with decls := cur.decls.map fun d =>
        let initUb := d.params.filterMap fun p => if p.ty.isUnboxedScalar || p.ty matches (.tuple _) then some p.id else none
        let cand := inlineLocalHelperCalls helpers initUb (maxVarIdInDecl d + 1000) d.body
        let d' :=
          if cand == d.body || codeNodeSize cand > 16384 then d
          else if codeCallsDecl d.name d.body && !codeCallsDecl d.name cand then d
          else { d with body := cand }
        flattenInlinedHelperBody d' }
  let rec loop (fuel : Nat) (cur : LNIRModule) : LNIRModule :=
    match fuel with
    | 0 => cur
    | f + 1 =>
      let next := step cur
      if next == cur then cur else loop f next
  loop 6 m

end LeanNative.IR
