import Lean.Elab.Command
import Lean.Elab.App
import Lean.Elab.PreDefinition.Structural.Main
import Lean.Elab.PreDefinition.WF.Main
import Lean.Elab.PreDefinition.PartialFixpoint.Main
import Lean.Data.Json
import Lean.Util.CollectAxioms
import Lean.Replay
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.CSimpAttr
import Lean.Compiler.InlineAttrs
import Lean.Compiler.Specialize
import Lean.Compiler.ExportAttr
import Lean.Compiler.NoncomputableAttr
import Lean.Compiler.ModPkgExt
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.ToDecl
import Lean.Compiler.LCNF.Main
import Lean.Compiler.LCNF.Passes
import Lean.Compiler.LCNF.AlphaEqv
import Lean.Compiler.LCNF.SpecInfo
import Lean.Compiler.LCNF.Simp.ConstantFold
import Lean.Compiler.LCNF.PrettyPrinter
import Lean.Compiler.IR.CompilerM
import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Instances
import Lean.Meta.CoeAttr
import Lean.Meta.Tactic.Ext
import Lean.Meta.Tactic.Grind.Attr
import Lean.Meta.Match.MatchPatternAttr
import Lean.Meta.CompletionName
import Lean.Meta.RecExt
import Lean.Compiler.LCNF.MonoTypes
import Lean.Compiler.LCNF.ToImpureType
import Lean.Linter.Deprecated
import Lean.DeprecatedModule
import Lake.Load.Lean.Elab
import Std.Data.HashMap
import TurboLean.Blake3
import TurboLean.StatementHash
import TurboLean.ZygoteFork

import TurboLean.ZygoteWorker.Env
import TurboLean.ZygoteWorker.Wire

open Lean Elab

namespace TurboLean.ZygoteWorker

/-- Check whether an axiom name belongs to `{propext, Quot.sound, Classical.choice}`. -/
def isAllowedStandardAxiom (ax : Name) : Bool :=
  ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice

/-- `*`-glob match (`*` matches any, possibly empty, run of characters). -/
partial def globMatch : List Char → List Char → Bool
  | [], s => s.isEmpty
  | '*' :: p, s => globMatch p s || match s with | [] => false | _ :: t => globMatch ('*' :: p) t
  | c :: p, s => match s with | d :: t => c == d && globMatch p t | [] => false

/-- Standard axioms plus the project allowlist (`[axioms] allow` in `turbo-lean.toml`), which the
    host passes as comma-separated `*` globs in `TURBO_LEAN_ALLOWED_AXIOMS`; never `sorryAx` or `Lean.trustCompiler`. -/
def isAllowedAxiom (patterns : List String) (ax : Name) : Bool :=
  isAllowedStandardAxiom ax ||
    (ax != Name.mkSimple ("sor" ++ "ryAx") &&
     ax != Name.mkStr2 "Lean" ("trust" ++ "Compiler") &&
     patterns.any (globMatch ·.toList ax.toString.toList))

/-- Structural alpha/binder-insensitive `Expr` equality modulo `letE` `nondep` flags and binder names/infos
    (in Lean 4.35, `let x := v; b` in a theorem signature elaborates with `nondep := true` in `thmInfo.type`
    and `nondep := false` inside the `sorryAx` motive of an explicit stub). -/
partial def exprEqModLetNondep : Expr → Expr → Bool
  | .bvar i, .bvar j => i == j
  | .fvar i, .fvar j => i == j
  | .mvar i, .mvar j => i == j
  | .sort u, .sort v => u == v
  | .const n us, .const m vs => n == m && us == vs
  | .app f a, .app g b => exprEqModLetNondep f g && exprEqModLetNondep a b
  | .lam _ d1 b1 _, .lam _ d2 b2 _ => exprEqModLetNondep d1 d2 && exprEqModLetNondep b1 b2
  | .forallE _ d1 b1 _, .forallE _ d2 b2 _ => exprEqModLetNondep d1 d2 && exprEqModLetNondep b1 b2
  | .letE _ t1 v1 b1 _, .letE _ t2 v2 b2 _ =>
    exprEqModLetNondep t1 t2 && exprEqModLetNondep v1 v2 && exprEqModLetNondep b1 b2
  | .lit l1, .lit l2 => l1 == l2
  | .mdata _ e1, e2 => exprEqModLetNondep e1 e2
  | e1, .mdata _ e2 => exprEqModLetNondep e1 e2
  | .proj n1 i1 e1, .proj n2 i2 e2 => n1 == n2 && i1 == i2 && exprEqModLetNondep e1 e2
  | _, _ => false

/-- `value` is `fun xs => sorryAx (Name → body) false label` (or legacy `sorryAx body false`) for
    `type = ∀ xs, body`, binder domains matching. -/
partial def isExplicitSorryBody (value type : Expr) : Bool :=
  match value, type with
  | .lam _ d b _, .forallE _ d' b' _ => exprEqModLetNondep d d' && isExplicitSorryBody b b'
  | v, ty =>
    let args := v.getAppArgs
    v.getAppFn.isConstOf (Name.mkSimple ("sor" ++ "ryAx")) && args.size ≥ 2 &&
      args[1]!.isConstOf ``Bool.false &&
      ((args.size == 2 && exprEqModLetNondep args[0]! ty) || (args.size == 3 && match args[0]! with
        | .forallE _ d b _ => d.isConstOf ``Lean.Name && exprEqModLetNondep b (ty.liftLooseBVars 0 1)
        | _ => false))

/-- A prefix stub as the host's shard builder emits it, elaborated to
    the explicit (non-synthetic) incomplete-proof term of `isExplicitSorryBody`. Elaboration errors and
    tactics such as `admitGoal` yield synthetic stubs and never qualify. -/
def isExplicitSorryStub (cinfo : ConstantInfo) : Bool :=
  match cinfo with
  | .thmInfo v => isExplicitSorryBody v.value v.type
  | _ => false

def canonicalComponent (s : String) : String :=
  if s.any (fun c => c == '.' || c == '«' || c == '»') then s!"«{s}»" else s

def canonicalName : Name → String
  | .anonymous => ""
  | .str .anonymous s => canonicalComponent s
  | .str p s => s!"{canonicalName p}.{canonicalComponent s}"
  | .num .anonymous n => s!"{n}"
  | .num p n => s!"{canonicalName p}.{n}"

/-- Collect transitive kernel axioms reachable from `rootName` in `afterEnv`,
    without traversing into the stubbed proof bodies (`v.value`) of `.thmInfo` declarations
    that were already present in `beforeMap` or that `opaqueStub` marks opaque. -/
def collectDeclAxioms (beforeMap : Lean.PHashMap Name ConstantInfo) (afterEnv : Environment) (rootName : Name)
    (opaqueStub : Name → Bool := fun _ => false)
    (localModIdx? : Option ModuleIdx := none) : Array Name := Id.run do
  let afterMap := afterEnv.constants.map₂
  let mut todo : Array Name := #[rootName]
  let mut visited : Std.HashMap Name Bool := {}
  let mut axioms : Array Name := #[]
  let mut axiomSeen : Std.HashMap Name Bool := {}
  while !todo.isEmpty do
    let curr := todo.back!
    todo := todo.pop
    if visited[curr]?.getD false then
      continue
    visited := visited.insert curr true
    let localCinfo? := match afterMap.find? curr with
      | some ci => some ci
      | none =>
        match localModIdx? with
        | some mIdx => if afterEnv.getModuleIdxFor? curr == some mIdx then afterEnv.find? curr else none
        | none => none
    match localCinfo? with
    | some cinfo =>
      match cinfo with
      | .axiomInfo v =>
        if !(axiomSeen[curr]?.getD false) then
          axiomSeen := axiomSeen.insert curr true
          axioms := axioms.push curr
        for c in v.type.getUsedConstants do
          if !(visited[c]?.getD false) then
            todo := todo.push c
      | .thmInfo v =>
        for c in v.type.getUsedConstants do
          if !(visited[c]?.getD false) then
            todo := todo.push c
        if !beforeMap.contains curr && !opaqueStub curr then
          for c in v.value.getUsedConstants do
            if !(visited[c]?.getD false) then
              todo := todo.push c
      | .defnInfo v =>
        for c in v.type.getUsedConstants do
          if !(visited[c]?.getD false) then
            todo := todo.push c
        if !opaqueStub curr then
          for c in v.value.getUsedConstants do
            if !(visited[c]?.getD false) then
              todo := todo.push c
      | .opaqueInfo v =>
        for c in v.type.getUsedConstants do
          if !(visited[c]?.getD false) then
            todo := todo.push c
        if !opaqueStub curr then
          for c in v.value.getUsedConstants do
            if !(visited[c]?.getD false) then
              todo := todo.push c
      | .inductInfo v =>
        for c in v.type.getUsedConstants do
          if !(visited[c]?.getD false) then
            todo := todo.push c
        for ctor in v.ctors do
          if !(visited[ctor]?.getD false) then
            todo := todo.push ctor
      | .ctorInfo v =>
        for c in v.type.getUsedConstants do
          if !(visited[c]?.getD false) then
            todo := todo.push c
      | .recInfo v =>
        for c in v.type.getUsedConstants do
          if !(visited[c]?.getD false) then
            todo := todo.push c
      | .quotInfo _ => pure ()
    | none =>
      let impCinfo? := afterEnv.find? curr
      let isOutlineMod := match afterEnv.getModuleIdxFor? curr with
        | some mIdx => (afterEnv.header.moduleNames[mIdx.toNat]?).any (fun m => m.toString.startsWith "_TurboOutline_")
        | none => false
      let isImportedOutlineStub := opaqueStub curr && isOutlineMod && impCinfo?.any isExplicitSorryStub
      if isImportedOutlineStub then
        if let some (.thmInfo tv) := impCinfo? then
          for c in tv.type.getUsedConstants do
            if !(visited[c]?.getD false) then
              todo := todo.push c
      else
        let impAxioms : Array Name := Id.run ((Lean.collectAxioms curr : ReaderT Environment Id (Array Name)).run afterEnv)
        for ax in impAxioms do
          if !(axiomSeen[ax]?.getD false) then
            axiomSeen := axiomSeen.insert ax true
            axioms := axioms.push ax
  return axioms

section RecAudit
open Meta

def hydrateOnePersistentExt {α β σ : Type} [Inhabited σ]
    (ext : PersistentEnvExtension α β σ) (env : Environment) : IO Environment := do
  let s := ext.toEnvExtension.getState env (asyncMode := .sync)
  let newState ← ext.addImportedFn s.importedEntries { env, opts := {} }
  return ext.toEnvExtension.setState env { s with state := newState } (asyncMode := .sync)

def hydrateMetaAuditEnv (env0 : Environment) : IO Environment := do
  let mut e := env0
  e ← hydrateOnePersistentExt Lean.classExtension e
  e ← hydrateOnePersistentExt Lean.Meta.instanceExtension.ext e
  e ← hydrateOnePersistentExt Lean.Meta.defaultInstanceExtension e
  e ← hydrateOnePersistentExt Lean.reducibilityExtraExt.ext e
  hydrateOnePersistentExt Lean.Meta.Match.Extension.extension e

def hydrateRecAuditEnv (env0 : Environment) : IO Environment := do
  if Lean.classExtension.getState env0 |>.outParamMap.contains ``Monad then
    return env0
  let e ← hydrateMetaAuditEnv env0
  let e ← hydrateOnePersistentExt Lean.Elab.WF.wfPreprocessSimpExtension.ext e
  return e.setMainModule e.mainModule

def isCoreRecCombinator (env : Environment) (c : Name) : Bool :=
  (env.getModuleIdxFor? c).any fun idx =>
    (env.header.moduleNames[idx.toNat]?).any fun m => m.getRoot == `Init || m.getRoot == `Lean

def checkRecAuditThmDecl (patterns : List String) (levelParams : List Name) (type value : Expr)
    (localAxioms : Array Name := #[])
    (opaqueStub : Name → Bool := fun _ => false)
    (allowSorry : Bool := false)
    (localModIdx? : Option ModuleIdx := none) : MetaM Unit := do
  let sorryAxName := Name.mkSimple ("sor" ++ "ryAx")
  let name ← mkFreshUserName `_recAuditThm
  addDecl (.thmDecl { name, levelParams, type, value })
  let env ← getEnv
  let axs := collectDeclAxioms {} env name opaqueStub localModIdx?
  unless axs.all (fun ax =>
      localAxioms.contains ax || isAllowedAxiom patterns ax || (allowSorry && ax == sorryAxName)) do
    throwError "disallowed axiom in recursion proof"

def checkRecAuditDefEqKernel (patterns : List String) (levelParams : List Name) (lhs rhs : Expr)
    (opaqueStub : Name → Bool := fun _ => false)
    (allowSorry : Bool := false)
    (localModIdx? : Option ModuleIdx := none) : MetaM Unit := do
  let goal ← Meta.mkEq lhs rhs
  let proof ← Meta.mkFreshExprSyntheticOpaqueMVar goal
  Meta.withTransparency .all <| withOptions (Meta.smartUnfolding.set · false) proof.mvarId!.refl
  let proof ← instantiateMVars proof
  checkRecAuditThmDecl patterns levelParams goal proof #[] opaqueStub allowSorry localModIdx?

def unfoldCliqueAuxThms (fresh : Array Name) (e : Expr) : CoreM Expr := withoutExporting do
  let env ← getEnv
  Core.transform e
    (pre := fun sub => sub.withAppRev fun f revArgs => do
      if f.isConst && revArgs.any (fun a => (a.find? fun x => x.isConst && fresh.contains x.constName!).isSome) then
        if let some info@(.thmInfo _) := env.find? f.constName! then
          return .visit <| (← instantiateValueLevelParams info f.constLevels! (allowOpaque := true)).betaRev revArgs
      return .continue)

def reconstructStructuralClique (preDefs : Array PreDefinition) (perms : FixedParamPerms)
    (xs : Array Expr) (infos : Array Structural.RecArgInfo) : MetaM (Array Expr) := do
  let values ← preDefs.mapIdxM (perms.perms[·]!.instantiateLambda ·.value xs)
  let types ← preDefs.mapIdxM (perms.perms[·]!.instantiateForall ·.type xs)
  let ind ← getConstInfoInduct infos[0]!.indGroupInst.all[0]!
  let positions : Structural.Positions := .groupAndSort (·.indIdx) infos (Array.range ind.numTypeFormers)
  let isPred ← Meta.forallTelescopeReducing ind.type fun _ r => pure r.isProp
  let withMotives (k : Array Expr → Array Expr → MetaM (Array Expr)) : MetaM (Array Expr) := do
    if isPred then
      Structural.withFunTypes values fun funTypes => do
        let motives ← infos.mapIdxM fun i r => Structural.mkIndPredBRecOnMotive r values[i]! funTypes[i]!
        k funTypes motives
    else
      let motives ← infos.mapIdxM fun i r => Structural.mkBRecOnMotive r values[i]! types[i]!
      k #[] motives
  withMotives fun funTypes motives => do
    let brec ← Structural.mkBRecOnConst infos positions motives isPred
    let fTypes ← Structural.inferBRecOnFTypes infos positions brec
    let fs ← infos.mapIdxM fun i r => do
      if isPred then
        let (f, matchers) ← withoutModifyingEnv do
          preDefs.forM addAsAxiom
          Structural.mkIndPredBRecOnF infos positions r values[i]! fTypes[i]! (brec 0).getAppArgs
        matchers.forM (·)
        return f
      else
        withoutModifyingEnv do
          preDefs.forM addAsAxiom
          Structural.mkBRecOnF infos positions r values[i]! fTypes[i]!
    let fs ← fs.mapM fun f => eraseRecAppSyntaxExpr f
    let dummy := mkAppN (brec 0) (.replicate (ind.numIndices + 1) default)
    let packedTypes ← Meta.inferArgumentTypesN positions.size dummy
    let packed ← positions.mapMwith (PProdN.mkLambdas · ·) packedTypes fs
    let result ← infos.mapIdxM fun i r => Structural.mkBRecOnApp positions i brec packed funTypes r values[i]!
    values.mapIdxM fun i v => Meta.lambdaTelescope v fun ys _ =>
      Meta.mkLambdaFVars (perms.perms[i]!.buildArgs xs ys) (result[i]!.beta ys)

def checkStructuralClique (patterns : List String) (peers : Array Name) (fresh : Array Name) (defs : Array PreDefinition)
    (opaqueStub : Name → Bool := fun _ => false)
    (allowSorry : Bool := false)
    (localModIdx? : Option ModuleIdx := none) : MetaM Bool := do
  try
    withoutModifyingEnv do
      let defs ← withoutModifyingEnv do
        defs.forM addAsAxiom
        defs.mapM fun d => do
          let v ← unfoldCliqueAuxThms fresh d.value
          return { d with value := (← Structural.preprocess v fresh 0) }
      let perms ← withoutModifyingEnv do
        defs.forM addAsAxiom
        let info ← getFixedParamsInfo defs
        for params in info.graph do
          for param in params do
            if let some mapping := param then
              unless mapping[0]?.join.isSome do throwError "disconnected clique"
        getFixedParamPerms defs
      perms.perms[0]!.forallTelescope defs[0]!.type fun xs => do
        let values ← defs.mapIdxM (perms.perms[·]!.instantiateLambda ·.value xs)
        let candidates ← withoutModifyingEnv do
          defs.forM addAsAxiom
          Structural.findRecArgCandidates fresh perms xs values (defs.map fun _ => none)
        for candidate in candidates.candidates do
          try
            let ok ← withoutModifyingEnv do
              let (perms', xs', erased) := perms.erase xs (candidate.comb.map (·.indicesAndRecArgPos))
              let infos := candidate.comb.mapIdx fun i r => { r with fixedParamPerm := perms'.perms[i]! }
              for r in infos do
                for indParam in r.indGroupInst.params do
                  for y in erased do
                    if (← dependsOn indParam y) then throwError "index in fixed param"
              withErasedFVars erased do
                let result ← reconstructStructuralClique defs perms' xs' infos
                return (some result)
            if let some result := ok then
              withoutModifyingEnv do
                for i in [:peers.size] do
                  let ci ← getConstInfoDefn peers[i]!
                  checkRecAuditDefEqKernel patterns ci.levelParams ci.value result[i]! opaqueStub allowSorry localModIdx?
              return true
          catch _ => pure ()
        return false
  catch _ =>
    return false

def auditIsForallMotive (matcherApp : Meta.MatcherApp) : MetaM (Option Expr) :=
  Meta.lambdaBoundedTelescope matcherApp.motive matcherApp.discrs.size fun xs t =>
    if xs.size == matcherApp.discrs.size && t.isForall && !t.bindingBody!.hasLooseBVar 0 then
      return some (← Meta.mkLambdaFVars xs t.bindingBody!)
    else
      return none

def auditSplitMatchOrCasesOn (mvarId : MVarId) (e : Expr) (matcherInfo : Meta.MatcherInfo) : MetaM (List MVarId) := do
  if (← Meta.isMatcherApp e) then
    Meta.Split.splitMatch mvarId e
  else
    let discr := e.getAppArgs[matcherInfo.numParams + matcherInfo.numDiscrs]!
    unless discr.isFVar do throwError "expected fvar discr"
    let subgoals ← mvarId.cases discr.fvarId!
    return subgoals.map (·.mvarId) |>.toList

def existingAuditMatchArgPusher? (matcherName : Name) : MetaM (Option Name) := do
  let env ← getEnv
  let userMatcher := privateToUserName matcherName
  let candidates : Array Name :=
    match env.getModuleIdxFor? matcherName with
    | some idx =>
      match env.header.moduleNames[idx.toNat]? with
      | some modName => #[mkPrivateNameCore modName userMatcher ++ `_arg_pusher, mkPrivateName env matcherName ++ `_arg_pusher]
      | none => #[mkPrivateName env matcherName ++ `_arg_pusher]
    | none => #[mkPrivateName env matcherName ++ `_arg_pusher]
  for cand in candidates do
    if let some (.thmInfo _) := env.find? cand then
      return some cand
  return none

def mkAuditMatchArgPusher (matcherName : Name) (matcherInfo : Meta.MatcherInfo) : MetaM Name := do
  if let some existing ← existingAuditMatchArgPusher? matcherName then
    return existing
  let name ← mkFreshUserName `_recAuditArgPusher
  let matcherVal ← getConstVal matcherName
  Meta.forallBoundedTelescope matcherVal.type (some (matcherInfo.numParams + 1)) fun xs _ => do
    let params := xs[*...matcherInfo.numParams]
    let motive' := xs[matcherInfo.numParams]!
    let u ← mkFreshUserName `u
    let v ← mkFreshUserName `v
    withLocalDeclD `α (.sort (.param u)) fun alpha => do
    withLocalDeclD `β (← mkArrow alpha (.sort (.param v))) fun beta => do
    withLocalDeclD `f (.forallE `x alpha (mkApp beta (.bvar 0)) .default) fun f => do
    let relType ← forallTelescope (← inferType motive') fun xs _ =>
      mkForallFVars xs (.forallE `x alpha (.sort 0) .default)
    withLocalDeclD `rel relType fun rel => do
    let motive ← forallTelescope (← inferType motive') fun xs _ => do
      let motiveBody := mkAppN motive' xs
      let extraArgType := .forallE `y alpha (.forallE `h (mkAppN rel (xs.push (.bvar 0))) (mkApp beta (.bvar 1)) .default) .default
      let motiveBody ← mkArrow extraArgType motiveBody
      mkLambdaFVars xs motiveBody
    let uElim ← Meta.lambdaBoundedTelescope motive matcherInfo.numDiscrs fun _ motiveBody => Meta.getLevel motiveBody
    let us := matcherVal.levelParams ++ [u, v]
    let matcherLevels' := matcherVal.levelParams.map mkLevelParam
    let matcherLevels ← match matcherInfo.uElimPos? with
      | none =>
        unless uElim.isZero do throwError "unexpected non-zero motive"
        pure matcherLevels'
      | some pos => pure <| (matcherLevels'.toArray.set! pos uElim).toList
    let lhs := mkApp (mkAppN (.const matcherName matcherLevels) params) motive
    let rhs := mkApp (mkAppN (.const matcherName matcherLevels') params) motive'
    Meta.forallBoundedTelescope (← Meta.inferType lhs) matcherInfo.numDiscrs fun discrs _ => do
    let lhs := mkAppN lhs discrs
    let rhs := mkAppN rhs discrs
    Meta.forallBoundedTelescope (← Meta.inferType lhs) matcherInfo.numAlts fun alts _ => do
    let lhs := mkAppN lhs alts
    let mut rhs := rhs
    for alt in alts, altNumParams in matcherInfo.altNumParams do
      let alt' ← Meta.forallBoundedTelescope (← Meta.inferType alt) altNumParams fun ys altBodyType => do
        unless altBodyType.isForall do throwError "expected forall in alt"
        let altArg ← Meta.forallBoundedTelescope altBodyType.bindingDomain! (some 2) fun ys _ =>
          Meta.mkLambdaFVars ys (.app f ys[0]!)
        Meta.mkLambdaFVars ys (mkAppN alt (ys.push altArg))
      rhs := mkApp rhs alt'
    let extraArg := .lam `y alpha (.lam `h (mkAppN rel (discrs.push (.bvar 0))) (mkApp f (.bvar 1)) .default) .default
    let lhs := mkApp lhs extraArg
    let goal ← Meta.mkEq lhs rhs
    let value ← Meta.mkFreshExprSyntheticOpaqueMVar goal
    let mvarIds ← auditSplitMatchOrCasesOn value.mvarId! rhs matcherInfo
    for mvarId in mvarIds do
      mvarId.refl
    let value ← instantiateMVars value
    let allVars := params ++ #[motive', alpha, beta, f, rel] ++ discrs ++ alts
    let type ← Meta.mkForallFVars allVars goal
    let value ← Meta.mkLambdaFVars allVars value
    addDecl <| Declaration.thmDecl { name, levelParams := us, type, value }
    return name

def auditPushMatcherArgProc : Meta.Simp.Simproc := fun e => do
  let e := e.headBeta
  let some matcherApp ← Meta.matchMatcherApp? e (alsoCasesOn := true) | return .continue
  let some fArg := matcherApp.remaining[0]? | return .continue
  unless fArg.isLambda && fArg.bindingBody!.isLambda && fArg.bindingBody!.bindingBody!.isApp do return .continue
  if fArg.bindingBody!.bindingBody!.hasLooseBVar 0 then return .continue
  unless fArg.bindingBody!.bindingBody!.appArg! == .bvar 1 do return .continue
  if fArg.bindingBody!.bindingBody!.appFn!.hasLooseBVar 1 then return .continue
  let fExpr := fArg.bindingBody!.bindingBody!.appFn!
  let fExprType ← Meta.withTransparency .all (Meta.whnfForall (← Meta.inferType fExpr))
  unless fExprType.isForall do return .continue
  let alpha := fExprType.bindingDomain!
  let beta := .lam fExprType.bindingName! fExprType.bindingDomain! fExprType.bindingBody! .default
  let some motive' ← auditIsForallMotive matcherApp | return .continue
  let rel ← Meta.lambdaTelescope matcherApp.motive fun xs motiveBody =>
    let motiveBodyArg := motiveBody.bindingDomain!
    Meta.mkLambdaFVars xs (.lam motiveBodyArg.bindingName! motiveBodyArg.bindingDomain! motiveBodyArg.bindingBody!.bindingDomain! .default)
  let argPusher ← mkAuditMatchArgPusher matcherApp.matcherName matcherApp.toMatcherInfo
  let proof ← Meta.withTransparency .all <| Meta.mkAppOptM
    argPusher ((matcherApp.params ++ #[motive', alpha, beta, fExpr, rel] ++ matcherApp.discrs ++ matcherApp.alts).map some)
  let some (_, _, rhs) := (← Meta.inferType proof).eq? | throwError "expected equality"
  let step : Meta.Simp.Result := { expr := rhs, proof? := some proof }
  let step ← step.addExtraArgs matcherApp.remaining[1...*]
  return .continue (some step)

def declMatchesAuditScope (env : Environment) (beforeMap : Lean.PHashMap Name ConstantInfo)
    (modIdx? : Option ModuleIdx) (name : Name) : Bool :=
  match modIdx? with
  | some modIdx => env.getModuleIdxFor? name == some modIdx
  | none => env.constants.map₂.contains name && !beforeMap.contains name

def checkWFClique (patterns : List String) (beforeMap : Lean.PHashMap Name ConstantInfo) (modIdx? : Option ModuleIdx)
    (peers : Array Name) (fresh : Array Name) (defs : Array PreDefinition)
    (opaqueStub : Name → Bool := fun _ => false)
    (allowSorry : Bool := false) : MetaM Bool := do
  try
    withoutModifyingEnv do
      let defs ← defs.mapM fun d => return { d with value := (← WF.floatRecApp d.value) }
      let (perms, argsPacker, unaryPreDef) ← withoutModifyingEnv do
        defs.forM addAsAxiom
        let info ← getFixedParamsInfo defs
        for params in info.graph do
          for param in params do
            if let some mapping := param then
              unless mapping[0]?.join.isSome do throwError "disconnected clique"
        let perms ← getFixedParamPerms defs
        let varNamess ← defs.mapIdxM fun i d => WF.varyingVarNames perms i d
        for vns in varNamess do
          if vns.isEmpty then throwError "no varying args"
        let argsPacker : ArgsPacker := { varNamess }
        let defs' ← defs.mapM fun d => return { d with value := (← unfoldCliqueAuxThms fresh d.value) }
        let unaryPreDef ← WF.packMutual perms argsPacker defs'
        return (perms, argsPacker, unaryPreDef)
      let nonRecName : Name :=
        if perms.fixedArePrefix && argsPacker.onlyOneUnary then
          peers[0]!
        else if argsPacker.numFuncs > 1 then
          peers[0]! ++ `_mutual
        else
          peers[0]! ++ `_unary
      let env ← getEnv
      unless declMatchesAuditScope env beforeMap modIdx? nonRecName &&
             !(Lean.isExtern env nonRecName) &&
             (Lean.Compiler.getImplementedBy? env nonRecName).isNone do
        return false
      let nonRecCi ← getConstInfoDefn nonRecName
      unless nonRecCi.safety == .safe && nonRecCi.levelParams == defs[0]!.levelParams do
        return false
      checkRecAuditDefEqKernel patterns nonRecCi.levelParams nonRecCi.type unaryPreDef.type opaqueStub allowSorry modIdx?
      if nonRecName != peers[0]! then
        let freshUnary ← mkFreshUserName `_recAuditUnary
        let expectedDefs ← WF.preDefsFromUnaryNonRec perms argsPacker
          (defs.mapIdx fun i d => { d with declName := peers[i]! })
          { unaryPreDef with declName := freshUnary }
        for i in [:peers.size] do
          let ci ← getConstInfoDefn peers[i]!
          let expectedVal := expectedDefs[i]!.value.replace fun sub =>
            if sub.isConstOf freshUnary then some (.const nonRecName sub.constLevels!) else none
          checkRecAuditDefEqKernel patterns ci.levelParams ci.value expectedVal opaqueStub allowSorry modIdx?
      let (_, wfPreprocessProof) ← withoutModifyingEnv do
        addAsAxiom unaryPreDef
        let r ← WF.preprocess unaryPreDef.value
        return (r.expr, r)
      Meta.lambdaTelescope nonRecCi.value fun fixedArgs fixBody => do
        unless fixedArgs.size == perms.numFixed do return false
        let fn := fixBody.getAppFn
        let args := fixBody.getAppArgs
        let F ←
          if fn.isConstOf ``WellFounded.fix && args.size == 5 && isCoreRecCombinator env ``WellFounded.fix then
            pure args[4]!
          else if fn.isConstOf ``WellFounded.Nat.fix && args.size == 4 && isCoreRecCombinator env ``WellFounded.Nat.fix then
            pure args[3]!
          else
            throwError "not a WF fix body"
        Meta.withLocalDeclD (← mkFreshUserName `_wfRecFn) unaryPreDef.type fun g => do
          let preprocessed ← instantiateLambda wfPreprocessProof.expr fixedArgs
          Meta.lambdaBoundedTelescope preprocessed 1 fun xs rhsOpen => do
            unless xs.size == 1 do throwError "expected packed arg"
            let x := xs[0]!
            let rhsOpen := rhsOpen.replace fun sub =>
              if sub.isConstOf unaryPreDef.declName then some g else none
            let gFixed := mkAppN g fixedArgs
            let ftype := (← Meta.inferType (mkApp F x)).bindingDomain!
            let f' ← Meta.forallBoundedTelescope ftype (some 2) fun ys _ =>
              Meta.mkLambdaFVars ys (.app gFixed ys[0]!)
            let lhsOpen := mkApp2 F x f'
            let eqOpen ← Meta.mkEq lhsOpen rhsOpen
            let main ← Meta.mkFreshExprSyntheticOpaqueMVar eqOpen
            let ctx ← Meta.Simp.mkContext (config := { dsimp := false, etaStruct := .none, letToHave := false, singlePass := true })
            let methods : Meta.Simp.Methods := { pre := auditPushMatcherArgProc }
            let mvarId? : Option MVarId ← main.mvarId!.withContext do
              let target ← instantiateMVars (← main.mvarId!.getType)
              let (r, _) ← Meta.Simp.main target ctx (methods := methods)
              if r.expr.isTrue then
                match r.proof? with
                | some proof => main.mvarId!.assign (← Meta.mkOfEqTrue proof)
                | none => main.mvarId!.assign (mkConst ``True.intro)
                pure none
              else
                pure (some (← Meta.applySimpResultToTarget main.mvarId! target r))
            if let some mvarId' := mvarId? then
              Meta.withTransparency .all <| withOptions (Meta.smartUnfolding.set · false) mvarId'.refl
            let openProof ← instantiateMVars main
            let allVars := #[g] ++ fixedArgs ++ #[x]
            let thmType ← Meta.mkForallFVars allVars eqOpen
            let thmVal ← Meta.mkLambdaFVars allVars openProof
            checkRecAuditThmDecl patterns nonRecCi.levelParams thmType thmVal #[] opaqueStub allowSorry modIdx?
            Meta.lambdaTelescope unaryPreDef.value fun uxs ubody => do
              addAsAxiom unaryPreDef
              let pStep ← wfPreprocessProof.addExtraArgs uxs
              let rawEq ← Meta.mkEq ubody pStep.expr
              let rawProof ← match pStep.proof? with
                | some pr => pure pr
                | none =>
                  let m ← Meta.mkFreshExprSyntheticOpaqueMVar rawEq
                  Meta.withTransparency .all <| withOptions (Meta.smartUnfolding.set · false) m.mvarId!.refl
                  instantiateMVars m
              let rawThmType ← Meta.mkForallFVars uxs rawEq
              let rawThmVal ← Meta.mkLambdaFVars uxs rawProof
              checkRecAuditThmDecl patterns nonRecCi.levelParams rawThmType rawThmVal #[unaryPreDef.declName] opaqueStub allowSorry modIdx?
            return true
  catch _ =>
    return false

def checkPFClique (patterns : List String) (beforeMap : Lean.PHashMap Name ConstantInfo) (modIdx? : Option ModuleIdx)
    (peers : Array Name) (fresh : Array Name) (defs : Array PreDefinition)
    (opaqueStub : Name → Bool := fun _ => false)
    (allowSorry : Bool := false) : MetaM Bool := do
  try
    withoutModifyingEnv do
      let defs ← withoutModifyingEnv do
        defs.forM addAsAxiom
        defs.mapM fun d => return { d with value := (← unfoldCliqueAuxThms fresh d.value) }
      let perms ← withoutModifyingEnv do
        defs.forM addAsAxiom
        let info ← getFixedParamsInfo defs
        for params in info.graph do
          for param in params do
            if let some mapping := param then
              unless mapping[0]?.join.isSome do throwError "disconnected clique"
        getFixedParamPerms defs
      let nonRecName : Name :=
        if defs.size == 1 && perms.fixedArePrefix then
          peers[0]!
        else
          peers[0]! ++ `mutual
      let env ← getEnv
      unless declMatchesAuditScope env beforeMap modIdx? nonRecName &&
             !(Lean.isExtern env nonRecName) &&
             (Lean.Compiler.getImplementedBy? env nonRecName).isNone do
        return false
      let nonRecCi ← getConstInfoDefn nonRecName
      unless nonRecCi.safety == .safe && nonRecCi.levelParams == defs[0]!.levelParams do
        return false
      perms.perms[0]!.forallTelescope defs[0]!.type fun fixedArgs => do
        let types ← defs.mapIdxM (perms.perms[·]!.instantiateForall ·.type fixedArgs)
        let packedType ← PProdN.pack 0 types
        let expectedNonRecType ← Meta.mkForallFVars fixedArgs packedType
        checkRecAuditDefEqKernel patterns nonRecCi.levelParams nonRecCi.type expectedNonRecType opaqueStub allowSorry modIdx?
        if nonRecName != peers[0]! then
          for fidx in [:peers.size] do
            let ci ← getConstInfoDefn peers[fidx]!
            let expectedWrapper ← Meta.forallBoundedTelescope ci.type perms.perms[fidx]!.size fun params _ => do
              let fixed := perms.perms[fidx]!.pickFixed params
              let varying := perms.perms[fidx]!.pickVarying params
              let us := nonRecCi.levelParams.map mkLevelParam
              let val := mkAppN (mkConst nonRecName us) fixed
              let val := PProdN.proj peers.size fidx packedType val
              let val := mkAppN val varying
              Meta.mkLambdaFVars (etaReduce := true) params val
            checkRecAuditDefEqKernel patterns ci.levelParams ci.value expectedWrapper opaqueStub allowSorry modIdx?
        let expectedFs ← withoutExporting do defs.mapIdxM fun funIdx preDef => do
          let body ← perms.perms[funIdx]!.instantiateLambda preDef.value fixedArgs
          Meta.withLocalDeclD (← mkFreshUserName `f) packedType fun f => do
            let body' ← withoutModifyingEnv do
              defs.forM addAsAxiom
              let t ← Meta.inferType f
              Meta.transform body fun sub => sub.withApp fun fn args => do
                let some idx := fn.constName?.bind (fresh.idxOf? ·) | return .continue
                let varying := perms.perms[idx]!.pickVarying args
                return .continue (mkAppN (PProdN.proj fresh.size idx t f) varying)
            Meta.mkLambdaFVars #[f] body'.headBeta
        let expectedPackedF ← Meta.withLocalDeclD (← mkFreshUserName `f) packedType fun f => do
          let packed ← PProdN.mk 0 (expectedFs.map (·.beta #[f]))
          Meta.mkLambdaFVars #[f] packed
        let nonRecBody ← instantiateLambda nonRecCi.value fixedArgs
        let fn := nonRecBody.getAppFn
        let args := nonRecBody.getAppArgs
        unless (fn.isConstOf ``Lean.Order.fix || fn.isConstOf ``Lean.Order.lfp_monotone) &&
               args.size == 4 && isCoreRecCombinator env fn.constName! do
          return false
        let actualF := args[2]!
        let eqF ← Meta.mkEq actualF expectedPackedF
        let proof ← Meta.mkFreshExprSyntheticOpaqueMVar eqF
        Meta.withTransparency .all <| withOptions (Meta.smartUnfolding.set · false) proof.mvarId!.refl
        let proof ← instantiateMVars proof
        let thmType ← Meta.mkForallFVars fixedArgs eqF
        let thmVal ← Meta.mkLambdaFVars fixedArgs proof
        checkRecAuditThmDecl patterns nonRecCi.levelParams thmType thmVal #[] opaqueStub allowSorry modIdx?
        return true
  catch _ =>
    return false

def checkRecursionCliqueMeta (patterns : List String) (beforeMap : Lean.PHashMap Name ConstantInfo)
    (modIdx? : Option ModuleIdx) (peers : Array Name)
    (opaqueStub : Name → Bool := fun _ => false)
    (allowSorry : Bool := false) : MetaM Bool := withoutExporting do
  let fresh ← peers.mapM fun _ => mkFreshUserName `_recAuditPeer
  let rename (e : Expr) : Expr := e.replace fun sub => do
    let .const n us := sub | none
    let base := (Compiler.isUnsafeRecName? n).getD n
    let i ← peers.idxOf? base
    return .const fresh[i]! us
  let mut defs : Array PreDefinition := #[]
  for i in [:peers.size] do
    let ci ← getConstInfoDefn peers[i]!
    let u ← getConstInfoDefn (Compiler.mkUnsafeRecName peers[i]!)
    let rawVal := rename u.value
    let val ← Core.transform rawVal fun sub => do
      if sub.isApp && sub.getAppFn.isLambda && sub.getAppArgs.all fun arg => arg.getAppFn.isConst && fresh.contains arg.getAppFn.constName! then
        return .visit sub.headBeta
      else
        return .continue
    defs := defs.push { (default : PreDefinition) with
      declName := fresh[i]!, type := ci.type, value := val, levelParams := ci.levelParams }
  if (← checkStructuralClique patterns peers fresh defs opaqueStub allowSorry modIdx?) then return true
  if (← checkWFClique patterns beforeMap modIdx? peers fresh defs opaqueStub allowSorry) then return true
  if (← checkPFClique patterns beforeMap modIdx? peers fresh defs opaqueStub allowSorry) then return true
  return false

partial def isCompilerPartialRecDefn (env : Environment) (hydratedEnvRef : IO.Ref (Option Environment))
    (cliqueCacheRef : IO.Ref (Std.HashMap (Option ModuleIdx × Name) Bool))
    (patterns : List String) (beforeMap : Lean.PHashMap Name ConstantInfo)
    (modIdx? : Option ModuleIdx) (cinfo : ConstantInfo)
    (visiting : Array (Option ModuleIdx × Name) := #[])
    (opaqueStub : Name → Bool := fun _ => false)
    (allowSorry : Bool := false) : IO Bool := do
  let .defnInfo dVal := cinfo | return false
  if dVal.safety != .partial ||
     dVal.all.isEmpty ||
     Lean.isExtern env dVal.name ||
     (Lean.Compiler.getImplementedBy? env dVal.name).isSome then
    return false
  let some baseName := Lean.Compiler.isUnsafeRecName? dVal.name | return false
  if !dVal.all.contains dVal.name || !declMatchesAuditScope env beforeMap modIdx? baseName then
    return false
  let mut peers : Array Name := #[]
  for twin in dVal.all do
    let some peer := Lean.Compiler.isUnsafeRecName? twin | return false
    if peers.contains peer then
      return false
    if !declMatchesAuditScope env beforeMap modIdx? twin ||
       !declMatchesAuditScope env beforeMap modIdx? peer ||
       Lean.isExtern env twin ||
       (Lean.Compiler.getImplementedBy? env twin).isSome ||
       Lean.isExtern env peer ||
       (Lean.Compiler.getImplementedBy? env peer).isSome then
      return false
    match env.find? twin with
    | some (.defnInfo uVal) =>
      if uVal.safety != .partial || uVal.all != dVal.all || uVal.levelParams != dVal.levelParams then
        return false
    | _ => return false
    peers := peers.push peer
  let cacheKey := (modIdx?, peers[0]!)
  if let some cached := (← cliqueCacheRef.get)[cacheKey]? then
    return cached
  if visiting.contains cacheKey then
    return false
  let recordResult (ok : Bool) : IO Bool := do
    cliqueCacheRef.modify (·.insert cacheKey ok)
    return ok
  let mut allOpaque := true
  let mut allSafeDefn := true
  for peer in peers do
    let twin := Lean.Compiler.mkUnsafeRecName peer
    let some (.defnInfo uVal) := env.find? twin | return (← recordResult false)
    match env.find? peer with
    | some (.opaqueInfo oVal) =>
      allSafeDefn := false
      if oVal.isUnsafe || oVal.levelParams != uVal.levelParams || oVal.type != uVal.type then
        return (← recordResult false)
    | some (.defnInfo bVal) =>
      allOpaque := false
      if bVal.safety != .safe || bVal.levelParams != uVal.levelParams || bVal.type != uVal.type then
        return (← recordResult false)
    | _ => return (← recordResult false)
  if allOpaque then
    return (← recordResult true)
  if !allSafeDefn then
    return (← recordResult false)
  let nextVisiting := visiting.push cacheKey
  for peer in peers do
    let twin := Lean.Compiler.mkUnsafeRecName peer
    let some (.defnInfo uVal) := env.find? twin | return (← recordResult false)
    for c in uVal.value.getUsedConstants do
      if let some refPeer := Lean.Compiler.isUnsafeRecName? c then
        if !peers.contains refPeer then
          let some refCi := env.find? c | return (← recordResult false)
          let refScope? := env.getModuleIdxFor? c
          let refBeforeMap := if refScope?.isSome then ({} : Lean.PHashMap Name ConstantInfo) else beforeMap
          let refStub := if refScope? == modIdx? then opaqueStub else fun _ => false
          let refAllowSorry := if refScope? == modIdx? then allowSorry else false
          unless (← isCompilerPartialRecDefn env hydratedEnvRef cliqueCacheRef patterns refBeforeMap refScope? refCi nextVisiting refStub refAllowSorry) do
            return (← recordResult false)
  let hydratedEnv ← match ← hydratedEnvRef.get with
    | some hEnv => pure hEnv
    | none =>
      let hEnv ← hydrateRecAuditEnv env
      hydratedEnvRef.set (some hEnv)
      pure hEnv
  let opts := maxHeartbeats.set {} 8000000
  let ok ← try
    let (res, _) ← (Meta.MetaM.run' (withCurrHeartbeats <| checkRecursionCliqueMeta patterns beforeMap modIdx? peers opaqueStub allowSorry)).toIO
      { fileName := "<recursion-audit>", fileMap := default, options := opts,
        maxRecDepth := 100000, maxHeartbeats := Core.getMaxHeartbeats opts }
      { env := hydratedEnv }
    pure res
  catch _ =>
    pure false
  recordResult ok

end RecAudit

/-- Unescaped components of a host declaration name (`.`-separated, `«…»` quoting). -/
def hostNameComponents (s : String) : List String := Id.run do
  let mut comps : Array String := #[]
  let mut cur := ""
  let mut quoted := false
  for c in s.toList do
    if c == '«' then quoted := true
    else if c == '»' then quoted := false
    else if c == '.' && !quoted then
      comps := comps.push cur
      cur := ""
    else cur := cur.push c
  return (comps.push cur).toList

/-- Unescaped components of `n`, with any `private` prefix removed. -/
def userNameComponents (n : Name) : List String :=
  (privateToUserName n).components.map (·.toString (escape := false))

/-- Parse a host target/stub string into `(exactRoot, components)`. `_root_.<qname>` anchors at root. -/
def parseHostTarget (s : String) : Bool × List String :=
  if s.startsWith "_root_." then (true, hostNameComponents (s.drop 7).toString)
  else (false, hostNameComponents s)

def parseExactRootName (s : String) : Option Name :=
  if !s.startsWith "_root_." then none
  else
    let comps := hostNameComponents (s.drop 7).toString
    if comps.isEmpty || comps.any String.isEmpty then none
    else some (comps.foldl Name.mkStr Name.anonymous)

def hasFastVerifyComp (n : Name) : Bool :=
  (userNameComponents n).any (·.startsWith "_turbo_verify_")

def kernelThmTypesAlphaEq (origVal genVal : TheoremVal) : Bool :=
  origVal.levelParams.length == genVal.levelParams.length &&
    (if origVal.levelParams == genVal.levelParams then genVal.type == origVal.type
     else genVal.type.instantiateLevelParams genVal.levelParams (origVal.levelParams.map Level.param) == origVal.type)

def parseFastVerifyMapEntries (fastMap : List (String × String)) : Option (List (Name × Name)) := Id.run do
  let mut parsed : List (Name × Name) := []
  let mut seenOrig : Std.HashSet Name := {}
  let mut seenGen : Std.HashSet Name := {}
  for (origStr, genStr) in fastMap do
    match parseExactRootName origStr, parseExactRootName genStr with
    | some origName, some genName =>
      if hasFastVerifyComp origName || !hasFastVerifyComp genName ||
         seenOrig.contains origName || seenGen.contains genName then
        return none
      seenOrig := seenOrig.insert origName
      seenGen := seenGen.insert genName
      parsed := (origName, genName) :: parsed
    | _, _ => return none
  return some parsed.reverse

def validateFastVerifyKernelMap
    (env : Environment)
    (newNames : Array Name)
    (isImportedOrig : Name → Bool)
    (exempt : Name → Bool)
    (fastMap : List (String × String)) : List String := Id.run do
  let some entries := parseFastVerifyMapEntries fastMap
    | return ["[TurboLean.KernelGate] invalid or non-bijective fast-verify declaration map"]
  let mut violations : List String := []
  let genCompsList := entries.map fun (_, genName) => (genName, userNameComponents genName)
  for n in newNames do
    if hasFastVerifyComp n then
      let nc := userNameComponents n
      let mapped := genCompsList.any fun (_, gc) => gc.isPrefixOf nc
      if !mapped then
        violations := violations ++
          [s!"[TurboLean.KernelGate] unmapped `_turbo_verify_` declaration `{n}` in shard"]
  for (origName, genName) in entries do
    if !isImportedOrig origName then
      violations := violations ++
        [s!"[TurboLean.KernelGate] fast-verify original `{origName}` is not an imported declaration"]
    else
      match env.find? origName with
      | some (.thmInfo origVal) =>
        if !newNames.contains genName || exempt genName then
          violations := violations ++
            [s!"[TurboLean.KernelGate] fast-verify generated theorem `{genName}` (for `{origName}`) is missing or stubbed"]
        else
          match env.find? genName with
          | some (.thmInfo genVal) =>
            if !kernelThmTypesAlphaEq origVal genVal then
              violations := violations ++
                [s!"[TurboLean.KernelGate] fast-verify kernel statement mismatch between `{genName}` and `{origName}`"]
          | _ =>
            violations := violations ++
              [s!"[TurboLean.KernelGate] fast-verify generated `{genName}` (for `{origName}`) is not a theorem"]
      | _ =>
        violations := violations ++
          [s!"[TurboLean.KernelGate] fast-verify original `{origName}` is missing or not a theorem in imported environment"]
  return violations

def nameMatchesHostTargetPrefix (comps : List String) (exactRoot : Bool) (tc : List String) : Bool :=
  !tc.isEmpty && (List.range comps.length).any fun i =>
    let pre := comps.take (i + 1)
    if exactRoot then pre == tc else tc.isSuffixOf pre

def nameMatchesHostTargetExact (comps : List String) (exactRoot : Bool) (tc : List String) : Bool :=
  !tc.isEmpty && (if exactRoot then comps == tc else tc.isSuffixOf comps)

/-- Whether new declaration `n` belongs to one of the host-named check `targets`: the target itself,
    its auxiliary declarations (`t.proof_1`, `t.match_1`), a `private` copy, or an explicitly mapped fast-olean rename. -/
def ownedByTarget (targets : List String) (fastMap : List (String × String)) (n : Name) : Bool :=
  let comps := userNameComponents n
  let mappedEntries := parseFastVerifyMapEntries fastMap |>.getD []
  targets.any fun t =>
    let (exactRoot, tc) := parseHostTarget t
    nameMatchesHostTargetPrefix comps exactRoot tc ||
      mappedEntries.any fun (origName, genName) =>
        nameMatchesHostTargetExact (userNameComponents origName) exactRoot tc &&
          (userNameComponents genName).isPrefixOf comps

/-- Kernel declarations of `consts` matching parsed host stub `(exactRoot, sc)`. -/
def stubNameHits (consts : Array ConstantInfo) (exactRoot : Bool) (sc : List String) : Array ConstantInfo :=
  consts.filter fun c =>
    c.isTheorem &&
      let comps := userNameComponents c.name
      !sc.isEmpty && (if exactRoot then comps == sc else sc.isSuffixOf comps)

/-- A host stub list (`stubs`, each entry once per source stub) resolved to kernel names, with the
    cardinality check of `collectStubDecls`: an entry named `k` times may match at most `k` theorems.
    More (a metaprogram injecting another theorem under the same user name) is a violation and exempts
    nothing for that ambiguous stub name. -/
def resolveStubNames (consts : Array ConstantInfo) (stubs : List String) : Std.HashSet Name × List String := Id.run do
  let mut out : Std.HashSet Name := {}
  let mut violations : List String := []
  let mut counts : Std.HashMap (Bool × List String) (Nat × String) := {}
  for e in stubs do
    let key := parseHostTarget e
    let (k, repr) := counts[key]?.getD (0, e)
    counts := counts.insert key (k + 1, repr)
  for ((exactRoot, ec), (k, repr)) in counts.toArray do
    let hits := stubNameHits consts exactRoot ec
    if hits.size ≤ k then
      out := hits.foldl (·.insert ·.name) out
    else
      violations := violations ++
        [s!"[TurboLean.KernelGate] prefix stub `{repr}` is ambiguous: {hits.map (·.name)}"]
  return (out, violations)

/-- Kernel names newly elaborated in `env` (`map₂`) or imported from `_TurboOutline_*` modules
    exempt from the `sorryAx` gate: host stubs (`stubs`) whose value is an explicit `sorry`
    (`isExplicitSorryStub`), never a host target. `violations` is non-empty when any stub name is
    ambiguous (which exempts nothing at all). -/
def stubExemptSet (env : Environment) (stubs targets : List String)
    (fastMap : List (String × String) := []) : Std.HashSet Name × List String :=
  if stubs.isEmpty then ({}, [])
  else
    let consts := Id.run do
      let mut cs := env.constants.map₂.foldl (fun acc _ c => acc.push c) #[]
      for modIdx in [0 : env.header.moduleNames.size] do
        let modName := env.header.moduleNames[modIdx]!
        if modName.toString.startsWith "_TurboOutline_" then
          if let some mData := env.header.moduleData[modIdx]? then
            for c in mData.constants do
              if !env.constants.map₂.contains c.name then
                cs := cs.push c
      return cs
    let (named, violations) := resolveStubNames consts stubs
    if !violations.isEmpty then ({}, violations)
    else
      let exempt := named.fold (init := ({} : Std.HashSet Name)) fun acc n =>
        if !ownedByTarget targets fastMap n && (env.find? n).any isExplicitSorryStub then acc.insert n else acc
      (exempt, [])

/-- Whether the stubbed prefix checkpoint `prefixEnv` holds any `sorryAx`-dependent declaration
    that this final run does not exempt (a checkpoint is shared by requests with other stubs and targets). -/
def unexemptPrefixStub (prefixEnv : Environment) (stubs targets : List String)
    (fastMap : List (String × String) := []) : Bool :=
  let sorryAxName := Name.mkSimple ("sor" ++ "ryAx")
  let (exempt, violations) := stubExemptSet prefixEnv stubs targets fastMap
  !violations.isEmpty || prefixEnv.constants.map₂.foldl (fun acc n _ =>
    acc || (!exempt.contains n &&
      (collectDeclAxioms {} prefixEnv n exempt.contains).contains sorryAxName)) false

/-- Whether `env` declares host name `t` directly or via an explicitly validated `fastMap` entry. -/
def declaresHostName (env : Environment) (fastMap : List (String × String)) (t : String) : Bool :=
  let (exactRoot, tc) := parseHostTarget t
  let mappedEntries := parseFastVerifyMapEntries fastMap |>.getD []
  !tc.isEmpty && (
    env.constants.map₂.foldl (fun acc n _ => acc ||
      nameMatchesHostTargetExact (userNameComponents n) exactRoot tc) false ||
    mappedEntries.any fun (origName, genName) =>
      nameMatchesHostTargetExact (userNameComponents origName) exactRoot tc &&
        env.constants.map₂.contains genName)

/-- Keep policy diagnostics actionable without changing their stable violation prefixes. -/
def kernelPolicyHint (policy : String) (name : Name) : String :=
  s!"; configure [{policy}] allow = [\"{Lean.privateToUserName name}\"] in turbo-lean.toml"

/-- In-kernel soundness gate auditing all newly added declarations in `afterEnv.constants.map₂`
    (relative to `beforeEnv.constants.map₂`) for unapproved axioms, compiler-trusted evaluation,
    extern/implemented_by bypasses, nested inductives (sea-monster risk), and prior-environment tampering. -/
def auditNewKernelDecls
    (beforeEnv afterEnv : Environment)
    (stubExempt : Name → Bool := fun _ => false)
    (allowSorry : Bool := false) : IO (Bool × List String × List String) := do
  let sorryAxName := Name.mkSimple ("sor" ++ "ryAx")
  let unsfTag := "un" ++ "safe"
  let beforeMap := beforeEnv.constants.map₂
  let afterMap := afterEnv.constants.map₂
  let patterns := (((← IO.getEnv "TURBO_LEAN_ALLOWED_AXIOMS").getD "").splitOn ",").filterMap fun p =>
    let t := p.trimAscii.toString
    if t.isEmpty then none else some t
  let mut violations : List String := []
  let mut sorryDecls : List String := []
  let mut seenSorry : Std.HashMap String Bool := {}
  let priorTampered := beforeMap.foldl (fun bad oldName oldInfo =>
    if bad then true
    else match afterMap.find? oldName with
      | some newInfo => !(newInfo.type == oldInfo.type)
      | none => true) false
  if priorTampered then
    violations := violations ++ ["[TurboLean.KernelGate] proof shard tampered with prior environment declaration"]
  let newDecls := afterMap.foldl (fun acc name cinfo =>
    if !beforeMap.contains name then (name, cinfo) :: acc else acc) []
  let orderedNewDecls := newDecls.reverse
  let hydratedEnvRef ← IO.mkRef (none : Option Environment)
  let cliqueCacheRef ← IO.mkRef ({} : Std.HashMap (Option ModuleIdx × Name) Bool)
  for (name, cinfo) in orderedNewDecls do
    if cinfo.isUnsafe then
      violations := violations ++ [s!"[TurboLean.KernelGate] {unsfTag} declaration `{name}` is forbidden"]
    if (cinfo.isPartial || (Lean.Compiler.isUnsafeRecName? name).isSome) &&
       !(← isCompilerPartialRecDefn afterEnv hydratedEnvRef cliqueCacheRef patterns beforeMap none cinfo #[] stubExempt allowSorry) then
      violations := violations ++ [s!"[TurboLean.KernelGate] forged or unpaired _unsafe_rec/partial declaration `{name}` is forbidden"]
    let isNestedInd := match cinfo with
      | .inductInfo iVal => iVal.isNested
      | _ => false
    if isNestedInd then
      violations := violations ++ [s!"[TurboLean.KernelGate] nested inductive type `{name}` (sea-monster risk) is forbidden in theorem shards"]
    if Lean.isExtern afterEnv name || (Lean.Compiler.getImplementedBy? afterEnv name).isSome then
      violations := violations ++ [s!"[TurboLean.KernelGate] extern/implemented_by bypass on `{name}` is forbidden"]
    let csimpSt := Lean.Compiler.CSimp.ext.getState afterEnv
    if csimpSt.thmNames.contains name || csimpSt.map.contains name then
      violations := violations ++ [s!"[TurboLean.KernelGate] csimp replacement bypass on `{name}` is forbidden"]
    let axs := collectDeclAxioms beforeMap afterEnv name stubExempt
    for ax in axs do
      if !isAllowedAxiom patterns ax then
        if !(stubExempt name && ax == sorryAxName) then
          if allowSorry && ax == sorryAxName then
            let userNm := canonicalName (Lean.privateToUserName name)
            if !userNm.isEmpty && !(userNm.splitOn "._").length > 1 && !(userNm.splitOn "_proof_").length > 1 && !(seenSorry[userNm]?.getD false) then
              seenSorry := seenSorry.insert userNm true
              sorryDecls := sorryDecls ++ [userNm]
            else if sorryDecls.isEmpty && !userNm.isEmpty && !(seenSorry[userNm]?.getD false) then
              seenSorry := seenSorry.insert userNm true
              sorryDecls := sorryDecls ++ [userNm]
          else
            violations := violations ++ [s!"[TurboLean.KernelGate] declaration `{name}` transitively depends on disallowed axiom `{ax}`"]
  return (violations.isEmpty, violations, sorryDecls)

end TurboLean.ZygoteWorker
