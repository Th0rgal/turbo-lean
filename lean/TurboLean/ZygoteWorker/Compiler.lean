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
import TurboLean.ZygoteWorker.KernelAudit
import TurboLean.ZygoteWorker.StatementHashing
import TurboLean.ZygoteWorker.Signature
import TurboLean.ZygoteWorker.Replay

open Lean Elab

namespace TurboLean.ZygoteWorker

def isWhitelistedInitExecUnsafe (env : Environment) (modIdx : ModuleIdx) (cinfo : ConstantInfo) : Bool :=
  if !cinfo.isUnsafe then false
  else match cinfo.value? with
    | some (.const ``Lean.enableInitializersExecution []) =>
      cinfo.type == .app (.const ``BaseIO []) (.const ``Unit []) &&
      env.getModuleIdxFor? cinfo.name == some modIdx
    | _ => false

def isWhitelistedInitExecBridge (env : Environment) (modIdx : ModuleIdx) (declName : Name) : Bool :=
  if Lean.isExtern env declName then false
  else match Lean.Compiler.getImplementedBy? env declName with
    | some implName =>
      match env.find? implName, env.find? declName with
      | some implInfo, some declInfo =>
        declInfo.type == implInfo.type &&
        isWhitelistedInitExecUnsafe env modIdx implInfo
      | _, _ => false
    | none => false

/-- Forbidden axioms reachable from each root; the values of `opaqueStubs` (validated prefix stubs,
    whose proofs are verified separately) are not traversed. -/
def collectForbiddenAxiomsByDecl (env : Environment) (roots : Array Name) (patterns : List String := [])
    (opaqueStubs : Std.HashSet Name := {}) : Std.HashMap Name (Array Name) := Id.run do
  let mut memo : Std.HashMap Name (Array Name) := {}
  let mut visiting : Std.HashMap Name Bool := {}
  let mut stack : Array (Name × Bool) := #[]
  for r in roots do
    if !memo.contains r then
      stack := stack.push (r, false)
  while !stack.isEmpty do
    let (curr, processed) := stack.back!
    stack := stack.pop
    if memo.contains curr then
      continue
    match env.find? curr with
    | none =>
      memo := memo.insert curr #[]
    | some cinfo =>
      let deps : Array Name := match cinfo with
        | .axiomInfo _ => #[]
        | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
        | .thmInfo v =>
          if opaqueStubs.contains curr then v.type.getUsedConstants
          else v.type.getUsedConstants ++ v.value.getUsedConstants
        | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
        | .quotInfo _ => #[]
        | .ctorInfo v => v.type.getUsedConstants
        | .recInfo v => v.type.getUsedConstants
        | .inductInfo v =>
          Id.run do
            let mut cs := v.type.getUsedConstants
            for ctor in v.ctors do
              cs := cs.push ctor
            return cs
      if !processed then
        visiting := visiting.insert curr true
        stack := stack.push (curr, true)
        for d in deps do
          if !memo.contains d && !(visiting[d]?.getD false) then
            stack := stack.push (d, false)
      else
        let mut axArr : Array Name := #[]
        match cinfo with
        | .axiomInfo _ =>
          if !isAllowedAxiom patterns curr then
            axArr := axArr.push curr
        | _ => pure ()
        for d in deps do
          if let some dAxs := memo[d]? then
            for ax in dAxs do
              if !axArr.contains ax then
                axArr := axArr.push ax
        memo := memo.insert curr axArr
  return memo

def nestedContainerAllowlist : Array Name := #[``List, ``Array, ``Option, ``Prod]

partial def nestedOccurrencesAllowed (selfNames : List Name) (e : Expr) : Bool :=
  let mentionsSelf (x : Expr) : Bool := (x.find? fun y => y.isConst && selfNames.contains y.constName!).isSome
  match e with
  | .forallE _ d b _ => nestedOccurrencesAllowed selfNames d && nestedOccurrencesAllowed selfNames b
  | .lam _ d b _ => nestedOccurrencesAllowed selfNames d && nestedOccurrencesAllowed selfNames b
  | .mdata _ b => nestedOccurrencesAllowed selfNames b
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    let headOk := match fn with
      | .const c _ => selfNames.contains c || !args.any mentionsSelf || nestedContainerAllowlist.contains c
      | _ => !args.any mentionsSelf
    headOk && args.all (nestedOccurrencesAllowed selfNames)
  | _ => true

def nestedInductiveAllowed (env : Environment) (iVal : InductiveVal) : Bool :=
  iVal.all.all fun indName =>
    match env.find? indName with
    | some (.inductInfo jVal) => jVal.ctors.all fun ctor =>
        (env.find? ctor).any fun c => nestedOccurrencesAllowed iVal.all c.type
    | _ => false

def isKernelConstantReachable (env : Environment) (src dst : Name) : Bool := Id.run do
  let mut visited : Std.HashSet Name := {}
  let mut work : Array Name := #[src]
  while !work.isEmpty do
    let curr := work.back!
    work := work.pop
    if curr == dst then
      return true
    if visited.contains curr then
      continue
    visited := visited.insert curr
    if let some (.defnInfo dVal) := env.find? curr then
      for c in dVal.value.getUsedConstants do
        if !visited.contains c then
          work := work.push c
  return false

def csimpCandidatePair? (ci : ConstantInfo) : Option (Name × Name) :=
  match ci.type.eq? with
  | some (_, .const f us, .const g vs) =>
    let set := Std.HashSet.ofList us
    if f != g && set.size == us.length && set.all Level.isParam && us == vs then
      some (f, g)
    else
      none
  | _ => none

def csimpReplacementPair? (env : Environment) (ci : ConstantInfo) : Option (Name × Name) := do
  let (f, g) ← csimpCandidatePair? ci
  let fi ← env.find? f
  let gi ← env.find? g
  match ci.type.eq? with
  | some (_, .const _ us, _) =>
    if us.all (fun | .param p => ci.levelParams.contains p | _ => false) &&
       us.length == ci.levelParams.length && us.length == fi.levelParams.length &&
       us.length == gi.levelParams.length then
      some (f, g)
    else
      none
  | _ => none

def compilerAuditCodeViolations (env : Environment) : List String := Id.run do
  let mut out := []
  for i in [:env.header.moduleNames.size] do
    let modIdx : ModuleIdx := i
    let modName := env.header.moduleNames[i]!
    for entries in #[Lean.Compiler.LCNF.Simp.ConstantFold.folderExt.getModuleEntries env modIdx,
        Lean.Compiler.LCNF.Simp.ConstantFold.folderExt.getModuleEntries (level := .private) env modIdx,
        Lean.Compiler.LCNF.Simp.ConstantFold.folderExt.getModuleIREntries env modIdx] do
      for entry in entries do
        out := out ++ [s!"[TurboLean.KernelGate] custom constant folder `{entry.folderDeclName}` in `{modName}` cannot be executed during compiler audit"]
    for entries in #[Lean.Compiler.LCNF.passManagerExt.getModuleEntries env modIdx,
        Lean.Compiler.LCNF.passManagerExt.getModuleEntries (level := .private) env modIdx,
        Lean.Compiler.LCNF.passManagerExt.getModuleIREntries env modIdx] do
      for entry in entries do
        out := out ++ [s!"[TurboLean.KernelGate] custom compiler pass installer `{entry}` in `{modName}` cannot be executed during compiler audit"]
  return out.eraseDups

def hydrateCompilerAuditEnv (env0 : Environment) : IO Environment := do
  let codeViolations := compilerAuditCodeViolations env0
  unless codeViolations.isEmpty do
    throw <| IO.userError (String.intercalate "\n" codeViolations)
  let mut e ← hydrateMetaAuditEnv env0
  e ← hydrateOnePersistentExt Lean.Compiler.CSimp.ext.ext e
  e ← hydrateOnePersistentExt Lean.Compiler.inlineAttrs.ext e
  e ← hydrateOnePersistentExt Lean.Compiler.nospecializeAttr.ext e
  e ← hydrateOnePersistentExt Lean.Compiler.weakSpecializeAttr.ext e
  e ← hydrateOnePersistentExt Lean.Compiler.specializeAttr.ext e
  e ← hydrateOnePersistentExt Lean.Compiler.implementedByAttr.ext e
  e ← hydrateOnePersistentExt Lean.Compiler.LCNF.specExtension e
  e := Lean.Compiler.LCNF.Simp.ConstantFold.folderExt.modifyState e
    (fun _ => ([], Lean.Compiler.LCNF.Simp.ConstantFold.builtinFolders))
  e := Lean.Compiler.LCNF.passManagerExt.modifyState e
    (fun _ => ([], Lean.Compiler.LCNF.builtinPassManager))
  for ext in (← Lean.persistentEnvExtensionsRef.get) do
    if #[`Lean.Compiler.LCNF.impureTypeExt, `Lean.Compiler.LCNF.trivialStructureInfoExt].contains
        (Lean.privateToUserName ext.name) then
      e ← hydrateOnePersistentExt ext e
  return e.setMainModule e.mainModule

def compilerAuditEligible (declName : Name) : CoreM Bool := do
  let env ← getEnv
  if Lean.isNoncomputable env declName || Lean.isNoncomputable env (Lean.Compiler.mkUnsafeRecName declName) then
    return false
  Lean.Compiler.LCNF.shouldGenerateCode declName

def runPureLcnfPass : Lean.Compiler.LCNF.Pass → Array (Lean.Compiler.LCNF.Decl .pure) →
    Lean.Compiler.LCNF.CompilerM (Array (Lean.Compiler.LCNF.Decl .pure))
  | { phase := .base, phaseOut := .base, run, .. }, cur =>
    Lean.Compiler.LCNF.withPhase .base (run cur)
  | _, cur => pure cur

def compileSingleBaseLcnfDecl (env : Environment) (declName : Name) :
    IO (Option (Lean.Compiler.LCNF.Decl .pure)) := do
  let action : Lean.Compiler.LCNF.CompilerM (Option (Lean.Compiler.LCNF.Decl .pure)) :=
    Lean.withAtLeastMaxRecDepth 8192 do
      unless ← compilerAuditEligible declName do return none
      let some info ← Lean.Compiler.LCNF.getDeclInfo? declName | return none
      let names := info.all.toArray.map fun n => (Lean.Compiler.isUnsafeRecName? n).getD n
      let names ← names.filterM (fun n => compilerAuditEligible n)
      let initDecls ← names.mapM Lean.Compiler.LCNF.toDecl
      let mut cur := Lean.Compiler.LCNF.markRecDecls initDecls
      let pm ← Lean.Compiler.LCNF.getPassManager
      let mut saved : Option (Lean.Compiler.LCNF.Decl .pure) := none
      for pass in pm.basePasses do
        if pass.name == `saveBase then
          for d in cur do
            if d.name == declName then
              saved := some (← Lean.Compiler.LCNF.normalizeFVarIds d)
          break
        else
          cur ← runPureLcnfPass pass cur
      return saved
  try
    let (res, _) ← Core.CoreM.toIO (Lean.Compiler.LCNF.CompilerM.run action)
      { fileName := "<csimp-audit>", fileMap := default, maxHeartbeats := 0 } { env }
    return res
  catch _ =>
    return none

def compileSingleToLcnfDecl (env : Environment) (declName : Name) :
    IO (Option (Lean.Compiler.LCNF.Decl .pure)) := do
  try
    let (d, _) ← Core.CoreM.toIO
      (Lean.Compiler.LCNF.CompilerM.run (Lean.withAtLeastMaxRecDepth 8192 do
        unless ← compilerAuditEligible declName do return none
        return some (← Lean.Compiler.LCNF.toDecl declName)))
      { fileName := "<csimp-audit>", fileMap := default, maxHeartbeats := 0 } { env }
    return d
  catch _ =>
    return none

def lcnfDeclAlphaEqv (d1 d2 : Lean.Compiler.LCNF.Decl .pure) : Bool :=
  match d1.value, d2.value with
  | .code c1, .code c2 =>
    ReaderT.run (Lean.Compiler.LCNF.AlphaEqv.withParams d1.params d2.params
      (Lean.Compiler.LCNF.AlphaEqv.eqv c1 c2)) ∅
  | .extern e1, .extern e2 => e1 == e2
  | _, _ => false

def isSpecGeneratedConstPair (f1 f2 : Name) : Bool :=
  let s1 := f1.toString.splitOn "._at_."
  let s2 := f2.toString.splitOn "._at_."
  s1.length > 1 && s2.length > 1 && s1[0]! == s2[0]!

partial def lcnfPureAlphaEqvModuloSpec (c1 c2 : Lean.Compiler.LCNF.Code .pure) :
    Lean.Compiler.LCNF.AlphaEqv.EqvM Bool := do
  match c1, c2 with
  | .let d1 k1, .let d2 k2 =>
    let valEq ← match d1.value, d2.value with
      | .const f1 us1 as1 _, .const f2 us2 as2 _ =>
        pure ((f1 == f2 || isSpecGeneratedConstPair f1 f2) && us1 == us2) <&&>
          Lean.Compiler.LCNF.AlphaEqv.eqvArgs as1 as2
      | v1, v2 => Lean.Compiler.LCNF.AlphaEqv.eqvLetValue (pu := .pure) v1 v2
    pure valEq <&&> Lean.Compiler.LCNF.AlphaEqv.eqvType d1.type d2.type <&&>
      Lean.Compiler.LCNF.AlphaEqv.withFVar d1.fvarId d2.fvarId (lcnfPureAlphaEqvModuloSpec k1 k2)
  | .fun d1 k1 _, .fun d2 k2 _ | .jp d1 k1, .jp d2 k2 =>
    Lean.Compiler.LCNF.AlphaEqv.eqvType d1.type d2.type <&&>
    Lean.Compiler.LCNF.AlphaEqv.withParams d1.params d2.params (lcnfPureAlphaEqvModuloSpec d1.value d2.value) <&&>
    Lean.Compiler.LCNF.AlphaEqv.withFVar d1.fvarId d2.fvarId (lcnfPureAlphaEqvModuloSpec k1 k2)
  | .cases cs1, .cases cs2 =>
    if cs1.typeName != cs2.typeName || cs1.alts.size != cs2.alts.size then return false
    unless (← Lean.Compiler.LCNF.AlphaEqv.eqvFVar cs1.discr cs2.discr) do return false
    unless (← Lean.Compiler.LCNF.AlphaEqv.eqvType cs1.resultType cs2.resultType) do return false
    let a1 := Lean.Compiler.LCNF.AlphaEqv.sortAlts cs1.alts
    let a2 := Lean.Compiler.LCNF.AlphaEqv.sortAlts cs2.alts
    for alt1 in a1, alt2 in a2 do
      match alt1, alt2 with
      | .alt ctor1 ps1 k1 _, .alt ctor2 ps2 k2 _ =>
        unless ctor1 == ctor2 do return false
        unless (← Lean.Compiler.LCNF.AlphaEqv.withParams ps1 ps2 (lcnfPureAlphaEqvModuloSpec k1 k2)) do return false
      | .default k1, .default k2 =>
        unless (← lcnfPureAlphaEqvModuloSpec k1 k2) do return false
      | _, _ => return false
    return true
  | .return x1, .return x2 => Lean.Compiler.LCNF.AlphaEqv.eqvFVar x1 x2
  | .jmp j1 as1, .jmp j2 as2 =>
    Lean.Compiler.LCNF.AlphaEqv.eqvFVar j1 j2 <&&> Lean.Compiler.LCNF.AlphaEqv.eqvArgs as1 as2
  | .unreach t1, .unreach t2 => Lean.Compiler.LCNF.AlphaEqv.eqvType t1 t2
  | _, _ => return false

def lcnfDeclAlphaEqvModuloSpec (d1 d2 : Lean.Compiler.LCNF.Decl .pure) : Bool :=
  if lcnfDeclAlphaEqv d1 d2 then true
  else match d1.value, d2.value with
  | .code c1, .code c2 =>
    ReaderT.run (Lean.Compiler.LCNF.AlphaEqv.withParams d1.params d2.params
      (lcnfPureAlphaEqvModuloSpec c1 c2)) ∅
  | _, _ => false

def isOpaqueBaseStub (d : Lean.Compiler.LCNF.Decl .pure) : Bool :=
  match d.value with
  | .extern data => data.entries == [.opaque]
  | _ => false

#guard isOpaqueBaseStub { (default : Lean.Compiler.LCNF.Decl .pure) with
  value := .extern { entries := [.opaque] } }
#guard !isOpaqueBaseStub { (default : Lean.Compiler.LCNF.Decl .pure) with
  value := .extern { entries := [.standard `all "audit_test"] } }
#guard !isOpaqueBaseStub { (default : Lean.Compiler.LCNF.Decl .pure) with
  value := .code (.unreach (.sort .zero)) }

def collectModuleStoredBaseDecls (env : Environment) (modIdx : ModuleIdx) :
    Std.HashMap Name (Lean.Compiler.LCNF.Decl .pure) := Id.run do
  let mut out : Std.HashMap Name (Lean.Compiler.LCNF.Decl .pure) := {}
  for entries in #[Lean.Compiler.LCNF.baseExt.getModuleEntries env modIdx,
      Lean.Compiler.LCNF.baseExt.getModuleEntries (level := .private) env modIdx,
      Lean.Compiler.LCNF.baseExt.getModuleIREntries env modIdx] do
    for b in entries do
      if !isOpaqueBaseStub b then
        out := out.insert b.name b
  return out

partial def collectLcnfPureConsts (c : Lean.Compiler.LCNF.Code .pure) (acc : Std.HashSet Name := {}) : Std.HashSet Name :=
  match c with
  | .let d k =>
    let acc := match d.value with
      | .const declName _ _ => acc.insert declName
      | _ => acc
    collectLcnfPureConsts k acc
  | .fun d k | .jp d k => collectLcnfPureConsts k (collectLcnfPureConsts d.value acc)
  | .cases cs =>
    cs.alts.foldl (fun a alt => match alt with | .alt _ _ k | .default k => collectLcnfPureConsts k a) acc
  | .return _ | .jmp _ _ | .unreach _ => acc

partial def collectIrFnBodyCalls (b : Lean.IR.FnBody) (acc : Std.HashSet Name := {}) : Std.HashSet Name :=
  match b with
  | .vdecl _ _ (.fap c _) rest | .vdecl _ _ (.pap c _) rest => collectIrFnBodyCalls rest (acc.insert c)
  | .vdecl _ _ _ rest => collectIrFnBodyCalls rest acc
  | .jdecl _ _ v rest => collectIrFnBodyCalls rest (collectIrFnBodyCalls v acc)
  | .set _ _ _ rest | .setTag _ _ rest | .uset _ _ _ rest | .sset _ _ _ _ _ rest
  | .inc _ _ _ _ rest | .dec _ _ _ _ rest | .del _ rest => collectIrFnBodyCalls rest acc
  | .case _ _ _ alts => alts.foldl (fun a alt => match alt with | .ctor _ b | .default b => collectIrFnBodyCalls b a) acc
  | .ret _ | .jmp _ _ | .unreachable => acc

def collectCompiledCodeConsts (env : Environment) (declName : Name) : Std.HashSet Name := Id.run do
  let mut out : Std.HashSet Name := {}
  if let some b := Lean.Compiler.LCNF.getDeclCore? env Lean.Compiler.LCNF.baseExt declName then
    if let .code code := b.value then
      out := collectLcnfPureConsts code out
  if let some d := Lean.IR.findEnvDecl env declName then
    if let .fdecl (body := body) .. := d then
      out := collectIrFnBodyCalls body out
  if let some modIdx := env.getModuleIdxFor? declName then
    for d in Lean.IR.declMapExt.getModuleIREntries env modIdx do
      if d.name == declName then
        if let .fdecl (body := body) .. := d then
          out := collectIrFnBodyCalls body out
  return out

def safeUnsafeCallWrapperParent? (env : Environment) (modIdx : ModuleIdx) (cinfo : ConstantInfo) : Option ConstantInfo :=
  let suffixName (nm : Name) : Option (Name × String) :=
    match nm with
    | .str p s =>
      if s.startsWith "unsafe_" && !(s.startsWith "unsafe_impl_") && (s.drop 7).toNat?.isSome then
        some (p, s)
      else
        none
    | _ => none
  if !cinfo.isUnsafe ||
     Lean.isExtern env cinfo.name ||
     (Lean.Compiler.getImplementedBy? env cinfo.name).isSome ||
     env.getModuleIdxFor? cinfo.name != some modIdx then
    none
  else
    match suffixName (Lean.privateToUserName cinfo.name) with
    | some (parentUser, _) =>
      (env.header.moduleData[modIdx.toNat]?).bind fun mdata =>
        mdata.constants.find? fun pc =>
          pc.name != cinfo.name &&
          !(Lean.isExtern env pc.name) &&
          (Lean.Compiler.getImplementedBy? env pc.name).isNone &&
          (pc.name == parentUser || Lean.privateToUserName pc.name == parentUser)
    | none => none

def safeUnsafeCallWrapperBridgeParent? (env : Environment) (modIdx : ModuleIdx) (declName : Name) : Option ConstantInfo :=
  let isImplSuffix (nm : Name) : Bool :=
    match nm with
    | .str _ s => s.startsWith "unsafe_impl_" && (s.drop 12).toNat?.isSome
    | _ => false
  if Lean.isExtern env declName || !(isImplSuffix (Lean.privateToUserName declName)) then none
  else match Lean.Compiler.getImplementedBy? env declName with
    | some implName =>
      match env.find? implName, env.find? declName with
      | some implInfo, some declInfo =>
        if !declInfo.isUnsafe && declInfo.type == implInfo.type then
          safeUnsafeCallWrapperParent? env modIdx implInfo
        else
          none
      | _, _ => none
    | none => none

def isPinnedFfiOpaque (env : Environment) (ffiAllow : Array (Name × Name × String)) (modIdx : ModuleIdx) (cinfo : ConstantInfo) : Bool :=
  match cinfo with
  | .opaqueInfo _ | .defnInfo _ =>
    !cinfo.isUnsafe &&
      (Lean.Compiler.getImplementedBy? env cinfo.name).isNone &&
      env.getModuleIdxFor? cinfo.name == some modIdx &&
      (env.header.moduleNames[modIdx.toNat]?).any fun m =>
        (Lean.getExternNameFor env `c cinfo.name).any fun sym =>
          -- A private extern is listed under its user-facing name; module and symbol still pin it.
          ffiAllow.contains (m, cinfo.name, sym) ||
            ffiAllow.contains (m, Lean.privateToUserName cinfo.name, sym)
  | _ => false

/-- Validated prefix stubs of a compiled shard module (`consts`): the host names each stub by its
    source name (`stubOk`, once per stub; matched by unescaped name-component suffix, `resolveStubNames`).
    An entry named `k` times must match at most `k` module theorems, whatever their values (more, e.g. one
    injected by a metaprogram next to a stub a macro turned into a proof, is a violation); of those, the
    ones whose kernel value is an explicit `sorry` (`isExplicitSorryStub`) are exempt. -/
def collectStubDecls (consts : Array ConstantInfo) (stubOk : Array String) :
    Std.HashSet Name × List String :=
  let (named, violations) := resolveStubNames consts stubOk.toList
  let out := named.fold (init := ({} : Std.HashSet Name)) fun acc n =>
    if consts.any fun c => c.name == n && isExplicitSorryStub c then acc.insert n else acc
  (out, violations)

/-- Recheck the complete (most private) module data against only its imports, as in
    LeanChecker.replayFromImports. Importing the target itself would trust its declarations
    without checking their types. Both module and shard audits call this same gate. -/
def readAuditedModulePartsAt (file : System.FilePath) (label : String) : IO (ModuleData × ModuleData) := do
  let mut files := #[file]
  let server := OLeanLevel.server.adjustFileName file
  if ← server.pathExists then
    files := files.push server
    let privateFile := OLeanLevel.private.adjustFileName file
    if ← privateFile.pathExists then
      files := files.push privateFile
  let parts ← readModuleDataParts files
  if h : parts.size = 0 then
    throw <| IO.userError s!"missing module data for `{label}`"
  else
    return (parts[0].1, parts[parts.size - 1].1)

def readAuditedModuleParts (moduleName : Name) : IO (ModuleData × ModuleData) := do
  let file ← findOLean moduleName
  readAuditedModulePartsAt file s!"{moduleName}"

def dupTheoremMatch (ci existing : ConstantInfo) : Bool :=
  match ci, existing with
  | .thmInfo info, .thmInfo info' =>
    info.name == info'.name &&
    info.type == info'.type &&
    info.levelParams == info'.levelParams &&
    info.all == info'.all
  | _, _ => false

def verifyProofIrrelevantOleanUpdate (moduleName : Name) (oldPath newPath : System.FilePath) : IO Unit := do
  if moduleName.isAnonymous then
    throw <| IO.userError "invalid empty module name for proof-irrelevant `.olean` check"
  let (oldMod, oldFull) ← readAuditedModulePartsAt oldPath s!"{moduleName}:old"
  let (newMod, newFull) ← readAuditedModulePartsAt newPath s!"{moduleName}:new"
  if oldMod.isModule != newMod.isModule || oldMod.imports != newMod.imports then
    throw <| IO.userError s!"`{moduleName}` imports or module header changed"
  let checkMap (label : String) (oldData newData : ModuleData) : IO Unit := do
    if oldData.constNames.size != oldData.constants.size || newData.constNames.size != newData.constants.size then
      throw <| IO.userError s!"`{moduleName}` ({label}) malformed constNames/constants size"
    let mut newMap : Std.HashMap Name ConstantInfo := {}
    for n in newData.constNames, ci in newData.constants do
      newMap := newMap.insert n ci
    for n in oldData.constNames, oldCi in oldData.constants do
      let some newCi := newMap[n]?
        | throw <| IO.userError s!"`{moduleName}` ({label}) dropped constant `{n}`"
      if !(dupTheoremMatch newCi oldCi || eqConstantInfo newCi oldCi) then
        throw <| IO.userError s!"`{moduleName}` ({label}) changed kernel signature/definition of `{n}`"
    let mut oldSet : NameSet := {}
    for n in oldData.constNames do
      oldSet := oldSet.insert n
    let expectedPrivPrefix := Name.mkNum (Lean.privateHeader ++ moduleName) 0
    for n in newData.constNames, newCi in newData.constants do
      if !oldSet.contains n then
        if !(newCi matches .thmInfo _) then
          throw <| IO.userError s!"`{moduleName}` ({label}) added non-theorem constant `{n}`"
        let privOk := Lean.privatePrefix? n == some expectedPrivPrefix
        if !privOk then
          throw <| IO.userError s!"`{moduleName}` ({label}) added non-private constant `{n}`"
  checkMap "exported" oldMod newMod
  checkMap "private" oldFull newFull

def replayAuditedModule (moduleName : Name) : IO Unit := do
  let (mod, full) ← readAuditedModuleParts moduleName
  let (_, imports) ← importModulesCore mod.imports |>.run
  let base ← finalizeImport imports mod.imports {} 0 false false (isModule := true)
  if (base.getModuleIdx? moduleName).isSome then
    throw <| IO.userError s!"`{moduleName}` appears in its own transitive import closure"
  let mut constants : Std.HashMap Name ConstantInfo := {}
  let mut dupProofChecks : Array TheoremVal := #[]
  for name in full.constNames, ci in full.constants do
    if let some existing := base.find? name then
      if eqConstantInfo ci existing then
        pure ()
      else if dupTheoremMatch ci existing then
        if let .thmInfo info := ci then
          dupProofChecks := dupProofChecks.push info
      else
        throw <| IO.userError s!"`{moduleName}` redeclares imported constant `{name}`"
    constants := constants.insert name ci
  let kenv ← replayKernelConstants constants base
  for i in [:dupProofChecks.size] do
    let tv := dupProofChecks[i]!
    let freshName := Name.mkNum (Name.mkStr `_turbo_dup_check (toString moduleName)) i
    let decl := Declaration.thmDecl { tv with name := freshName, all := [freshName] }
    match checkKernelDecl kenv decl with
    | .ok _ => pure ()
    | .error ex =>
      let msg ← ex.toMessageData {} |>.toString
      throw <| IO.userError s!"duplicate realized theorem `{tv.name}` in `{moduleName}` failed kernel check: {msg}"

/-- Recheck a contiguous topological slice of modules against only their frontier imports outside
    `moduleNames`, verifying fail-closed that none of `moduleNames` was imported into `base`
    without kernel replay. -/
def replayAuditedModuleClosure (moduleNames : Array Name) : IO Unit := do
  if moduleNames.isEmpty then
    return
  if h : moduleNames.size = 1 then
    replayAuditedModule moduleNames[0]
    return
  let mut targetSet : NameSet := {}
  for m in moduleNames do
    if m.isAnonymous then
      throw <| IO.userError "invalid empty/anonymous module name in replay closure"
    targetSet := targetSet.insert m
  let mut frontierImports : Array Import := #[]
  let mut seenFrontier : NameSet := {}
  let mut fullModules : Array (Name × ModuleData) := #[]
  for modName in moduleNames do
    let (mod, full) ← readAuditedModuleParts modName
    fullModules := fullModules.push (modName, full)
    for imp in mod.imports do
      if !targetSet.contains imp.module && !seenFrontier.contains imp.module then
        seenFrontier := seenFrontier.insert imp.module
        frontierImports := frontierImports.push imp
  let (_, imports) ← importModulesCore frontierImports |>.run
  let base ← finalizeImport imports frontierImports {} 0 false false (isModule := true)
  for modName in moduleNames do
    if (base.getModuleIdx? modName).isSome then
      throw <| IO.userError s!"replay closure topological invariant violated: `{modName}` imported into base environment"
  let mut constants : Std.HashMap Name ConstantInfo := {}
  let mut dupProofChecks : Array (Name × TheoremVal) := #[]
  for (modName, full) in fullModules do
    for name in full.constNames, ci in full.constants do
      if let some existing := base.find? name then
        if eqConstantInfo ci existing then
          pure ()
        else if dupTheoremMatch ci existing then
          if let .thmInfo info := ci then
            dupProofChecks := dupProofChecks.push (modName, info)
        else
          throw <| IO.userError s!"`{modName}` redeclares imported constant `{name}`"
      else if let some prev := constants[name]? then
        if eqConstantInfo ci prev then
          pure ()
        else if dupTheoremMatch ci prev then
          if let .thmInfo info := ci then
            if let .thmInfo prevInfo := prev then
              dupProofChecks := dupProofChecks.push (modName, prevInfo)
            dupProofChecks := dupProofChecks.push (modName, info)
          constants := constants.insert name ci
        else
          throw <| IO.userError s!"`{modName}` redeclares closure constant `{name}`"
      else
        constants := constants.insert name ci
  let kenv ← replayKernelConstants constants base
  for i in [:dupProofChecks.size] do
    let (modName, tv) := dupProofChecks[i]!
    let freshName := Name.mkNum (Name.mkStr `_turbo_dup_check (toString modName)) i
    let decl := Declaration.thmDecl { tv with name := freshName, all := [freshName] }
    match checkKernelDecl kenv decl with
    | .ok _ => pure ()
    | .error ex =>
      let msg ← ex.toMessageData {} |>.toString
      throw <| IO.userError s!"duplicate realized theorem `{tv.name}` in `{modName}` failed kernel check: {msg}"

def auditImportedModulesInEnv (env : Environment) (targets : Array (String × Name))
    (ffiAllow : Array (Name × Name × String) := #[])
    (patterns : List String := []) (csimpPatterns : List String := [])
    (stubs : Std.HashSet Name := {})
    (unsafePatterns : List String := []) (implByPatterns : List String := [])
    (skipChildReplay : Bool := false)
    (allowSorry : Bool := false) (isImportAudit : Bool := false) :
    IO (List String × List String × List (String × String × String)) := do
  let codeViolations := compilerAuditCodeViolations env
  unless codeViolations.isEmpty do return (codeViolations, [], [])
  let sorryAxName := Name.mkSimple ("sor" ++ "ryAx")
  let app := (← IO.appPath).toString
  let nameMatchesPolicy := fun (pats : List String) (name : Name) =>
    let raw := name.toString.toList
    let usr := (Lean.privateToUserName name).toString.toList
    pats.any fun p =>
      let pl := p.toList
      globMatch pl raw || globMatch pl usr
  let unsafeAllowed := fun name : Name =>
    (Lean.Compiler.isUnsafeRecName? name).isNone && nameMatchesPolicy unsafePatterns name
  let implByAllowed := fun name : Name =>
    !(Lean.isExtern env name) && nameMatchesPolicy implByPatterns name
  let hydratedEnvRef ← IO.mkRef (none : Option Environment)
  let compilerEnvRef ← IO.mkRef (none : Option Environment)
  let getCompilerAuditEnv : IO Environment := do
    if let some ce ← compilerEnvRef.get then return ce
    let ce ← hydrateCompilerAuditEnv env
    compilerEnvRef.set (some ce)
    return ce
  let cliqueCacheRef ← IO.mkRef ({} : Std.HashMap (Option ModuleIdx × Name) Bool)
  let csimpCliqueCacheRef ← IO.mkRef ({} : Std.HashMap (Option ModuleIdx × Name) Bool)
  let sysrootLibPrefix? : Option String ← try
    let libDir ← IO.FS.realPath ((← Lean.findSysroot) / "lib" / "lean")
    let s := libDir.toString
    pure (some (if s.endsWith "/" then s else s ++ "/"))
  catch _ =>
    pure none
  let sysrootCache ← IO.mkRef ({} : Std.HashMap Name Bool)
  let isSysrootMod (moduleName : Name) : IO Bool := do
    if let some ok := (← sysrootCache.get)[moduleName]? then return ok
    let ok ← match sysrootLibPrefix? with
      | none => pure false
      | some pfx =>
        try
          let p ← IO.FS.realPath (← Lean.findOLean moduleName)
          pure (p.toString.startsWith pfx)
        catch _ =>
          pure false
    sysrootCache.modify (·.insert moduleName ok)
    return ok
  let replayCache ← IO.mkRef ({} : Std.HashMap Name Bool)
  let replayErrors ← IO.mkRef ({} : Std.HashMap Name String)
  let replayOnce (moduleName : Name) : IO Bool := do
    if let some ok := (← replayCache.get)[moduleName]? then return ok
    let child ← IO.Process.output {
      cmd := app, args := #["--kernel-replay-module", moduleName.toString]
    }
    let ok := child.exitCode == 0
    replayCache.modify (·.insert moduleName ok)
    if !ok then replayErrors.modify (·.insert moduleName s!"kernel replay child exited {child.exitCode}: {child.stderr}")
    return ok
  let closureCache ← IO.mkRef ({} : Std.HashMap Name Bool)
  let replayNonSysrootClosure (rootMod : Name) : IO Bool := do
    if let some ok := (← closureCache.get)[rootMod]? then return ok
    let mut seenMods : Std.HashSet Name := {}
    let mut stack := #[rootMod]
    let mut allOk := true
    while !stack.isEmpty && allOk do
      let m := stack.back!
      stack := stack.pop
      if seenMods.contains m then continue
      seenMods := seenMods.insert m
      if ← isSysrootMod m then continue
      unless ← replayOnce m do
        allOk := false
        break
      if let some mIdx := env.getModuleIdx? m then
        if h : mIdx.toNat < env.header.moduleData.size then
          for imp in env.header.moduleData[mIdx.toNat].imports do
            if !seenMods.contains imp.module then
              stack := stack.push imp.module
    closureCache.modify (·.insert rootMod allOk)
    return allOk
  let dupThmExtrasRef ← IO.mkRef (none : Option (Std.HashMap Name (Array (ModuleIdx × Array Name))))
  let getDupThmExtras : IO (Std.HashMap Name (Array (ModuleIdx × Array Name))) := do
    if let some m ← dupThmExtrasRef.get then return m
    let mut m : Std.HashMap Name (Array (ModuleIdx × Array Name)) := {}
    for i in [:env.header.moduleData.size] do
      let mIdx : ModuleIdx := i
      for ci in env.header.moduleData[i]!.constants do
        if let .thmInfo tv := ci then
          if env.getModuleIdxFor? ci.name != some mIdx then
            let used := tv.type.getUsedConstants ++ tv.value.getUsedConstants
            m := m.insert ci.name ((m[ci.name]?.getD #[]).push (mIdx, used))
    dupThmExtrasRef.set (some m)
    return m
  let mut allCSimpEntries : Array (Option ModuleIdx × Lean.Compiler.CSimp.Entry) := #[]
  for i in [:env.header.moduleData.size] do
    let mIdx : ModuleIdx := i
    for scEntry in Lean.Compiler.CSimp.ext.ext.getModuleEntries env mIdx do
      let entry := match scEntry with | .global e | .scoped _ e => e
      allCSimpEntries := allCSimpEntries.push (some mIdx, entry)
  let globalCSimp := Lean.Compiler.CSimp.ext.getState env
  let scopedCSimp := (Lean.Compiler.CSimp.ext.ext.getState env).scopedEntries.map
  for (_, entry) in globalCSimp.map do
    allCSimpEntries := allCSimpEntries.push (none, entry)
  for (_, entries) in scopedCSimp do
    for entry in entries.toArray do
      allCSimpEntries := allCSimpEntries.push (none, entry)
  let mut csimpByFrom : Std.HashMap Name (Array Lean.Compiler.CSimp.Entry) := {}
  if isImportAudit then
    for (_, entry) in allCSimpEntries do
      csimpByFrom := csimpByFrom.insert entry.fromDeclName ((csimpByFrom[entry.fromDeclName]?.getD #[]).push entry)
  let verifiedCache ← IO.mkRef ({} : Std.HashMap Name Bool)
  let verifiedCSimp (name : Name) : IO Bool := do
    if skipChildReplay then return false
    if let some ok := (← verifiedCache.get)[name]? then return ok
    let check : IO Bool := do
      let some (.thmInfo tv) := env.find? name | return false
      let some (lhs, rhs) := csimpReplacementPair? env (.thmInfo tv) | return false
      if !(collectDeclAxioms {} env name).all isAllowedStandardAxiom then return false
      let dupExtras ← getDupThmExtras
      let mut seen : Std.HashSet Name := {}
      let mut work := #[name, lhs, rhs]
      while !work.isEmpty do
        let n := work.back!
        work := work.pop
        if seen.contains n then continue
        seen := seen.insert n
        let some ci := env.find? n | return false
        if ci.isUnsafe then return false
        if ci matches .axiomInfo _ then
          if !isAllowedStandardAxiom n then return false
        if !(collectDeclAxioms {} env n).all isAllowedStandardAxiom then return false
        if let .inductInfo iv := ci then
          if iv.isUnsafe || (iv.isNested && !nestedInductiveAllowed env iv) then return false
        let isCoreInit ← match env.getModuleIdxFor? n with
          | some idx =>
            match env.header.moduleNames[idx.toNat]? with
            | some modName =>
              if modName.getRoot == `Init && (← isSysrootMod modName) then
                pure true
              else
                unless ← replayNonSysrootClosure modName do return false
                if (Lean.Compiler.getImplementedBy? env n).isSome && !implByAllowed n then return false
                if (safeUnsafeCallWrapperBridgeParent? env idx n).isSome && !implByAllowed n then return false
                if Lean.isExtern env n && !isPinnedFfiOpaque env ffiAllow idx ci then return false
                if (ci.isPartial || (Lean.Compiler.isUnsafeRecName? n).isSome) &&
                   !(← isCompilerPartialRecDefn env hydratedEnvRef csimpCliqueCacheRef [] {} (some idx) ci #[] (fun _ => false) false) then
                  return false
                pure false
            | none => return false
          | none =>
            if ci matches .quotInfo _ then pure true else return false
        if !isCoreInit && (Lean.Compiler.isUnsafeRecName? n).isNone then
          let twin := Lean.Compiler.mkUnsafeRecName n
          if (env.find? twin).isSome && !seen.contains twin then
            work := work.push twin
        for used in ci.getUsedConstantsAsSet.toArray do
          if !seen.contains used then work := work.push used
        if let .inductInfo iv := ci then
          for ctor in iv.ctors do
            if !seen.contains ctor then work := work.push ctor
        if let some extras := dupExtras[n]? then
          for (rIdx, rUsed) in extras do
            let some rMod := env.header.moduleNames[rIdx.toNat]? | return false
            unless ← replayNonSysrootClosure rMod do return false
            for u in rUsed do
              if !seen.contains u then work := work.push u
        if let some nextEntries := csimpByFrom[n]? then
          for ne in nextEntries do
            let some nci := env.find? ne.thmName | return false
            if !nci.isTheorem then return false
            if csimpReplacementPair? env nci != some (ne.fromDeclName, ne.toDeclName) then return false
            if !seen.contains ne.thmName then work := work.push ne.thmName
            if !seen.contains ne.toDeclName then work := work.push ne.toDeclName
      return true
    let ok ← check
    verifiedCache.modify (·.insert name ok)
    return ok
  let csimpAllowed (name : Name) : IO Bool := do
    if nameMatchesPolicy csimpPatterns name then return true
    if isImportAudit then verifiedCSimp name else pure false
  let unsfTag := "un" ++ "safe"
  let mut violations : List String := []
  let mut sorryDecls : List String := []
  let mut seenSorry : Std.HashMap String Bool := {}
  let mut targetIdxs : Std.HashMap ModuleIdx String := {}
  let mut allRoots : Array Name := #[]
  if !skipChildReplay then
    for (rawStr, nm) in targets do
      unless ← replayOnce nm do
        violations := violations ++ [s!"[TurboLean.KernelReplay] independent kernel re-check of `{rawStr}` failed: {(← replayErrors.get)[nm]?.getD ""}"]
  for (_, nm) in targets do
    if let some modIdx := env.getModuleIdx? nm then
      if h : modIdx.toNat < env.header.moduleData.size then
        let mdata := env.header.moduleData[modIdx.toNat]
        for cinfo in mdata.constants do
          allRoots := allRoots.push cinfo.name
          if let .thmInfo tv := cinfo then
            if !stubs.contains cinfo.name && env.getModuleIdxFor? cinfo.name != some modIdx then
              for u in tv.type.getUsedConstants ++ tv.value.getUsedConstants do
                allRoots := allRoots.push u
        for extraName in mdata.extraConstNames do
          allRoots := allRoots.push extraName
  let axMap := collectForbiddenAxiomsByDecl env allRoots patterns stubs
  let kernelCone : Std.HashSet Name := Id.run do
    if !isImportAudit then return {}
    let mut work := allRoots.filter fun n => (env.find? n).any fun ci =>
      !ci.isUnsafe
    for (_, entry) in allCSimpEntries do
      if (env.find? entry.thmName).any (!·.isUnsafe) then work := work.push entry.thmName
      if (env.find? entry.fromDeclName).any (!·.isUnsafe) then work := work.push entry.fromDeclName
      if (env.find? entry.toDeclName).any (!·.isUnsafe) then work := work.push entry.toDeclName
    let mut seen : Std.HashSet Name := {}
    while !work.isEmpty do
      let n := work.back!
      work := work.pop
      if seen.contains n then continue
      seen := seen.insert n
      if let some ci := env.find? n then
        for used in ci.getUsedConstantsAsSet.toArray do
          if !seen.contains used then work := work.push used
        if let .inductInfo iv := ci then
          for ctor in iv.ctors do
            if !seen.contains ctor then work := work.push ctor
    return seen
  let auditHelper := fun n => !isImportAudit || kernelCone.contains n
  let findOwnerInfo (callerName : Name) : Option ConstantInfo :=
    match env.find? callerName with
    | some ci => some ci
    | none =>
      let rec findKernelOwner (nm : Name) : Option ConstantInfo :=
        match nm with
        | .str p _ | .num p _ =>
          if p.isAnonymous then none
          else match env.find? p with
            | some ci => some ci
            | none => findKernelOwner p
        | .anonymous => none
      findKernelOwner callerName
  let auditModuleLocalCSimp (modIdx : ModuleIdx) (modLabel : String)
      (csimpCandidates : Array (Name × Name × Name))
      (importedScopedCands : Array (Name × Name × Name) := #[]) : IO (List String) := do
    if csimpCandidates.isEmpty && importedScopedCands.isEmpty then return []
    let mut modExportedCSimp : Std.HashSet Name := {}
    for scEntry in Lean.Compiler.CSimp.ext.ext.getModuleEntries env modIdx do
      let entry := match scEntry with | .global e | .scoped _ e => e
      modExportedCSimp := modExportedCSimp.insert entry.thmName
    let localCands := (csimpCandidates.filter fun (thmName, _, _) => !modExportedCSimp.contains thmName) ++ importedScopedCands
    if localCands.isEmpty then return []
    let mut out : List String := []
    let mut seenLocalHit : Std.HashSet (Name × Name) := {}
    let emitHit (thmName lhs rhs callerName : Name) (acc : List String) (seen : Std.HashSet (Name × Name)) :
        List String × Std.HashSet (Name × Name) :=
      if seen.contains (thmName, callerName) then (acc, seen)
      else
        (acc ++ [s!"[TurboLean.KernelGate] local csimp replacement `{thmName}` ({lhs} -> {rhs}) rewrote compiled code of `{callerName}` in `{modLabel}`{kernelPolicyHint "csimp" thmName}"],
         seen.insert (thmName, callerName))
    let storedBaseMap := collectModuleStoredBaseDecls env modIdx
    let mut reachCache : Std.HashMap (Name × Name) Bool := {}
    for (_, lhs, rhs) in localCands do
      if !reachCache.contains (lhs, rhs) then
        reachCache := reachCache.insert (lhs, rhs) (isKernelConstantReachable env lhs rhs)
    let isReachableCached (u v : Name) : Bool := reachCache[(u, v)]?.getD false
    let mdata := env.header.moduleData[modIdx.toNat]!
    let mut callerNames : Array Name := #[]
    let mut seenCallers : Std.HashSet Name := {}
    let pushCaller (nm : Name) (arr : Array Name) (seen : Std.HashSet Name) : Array Name × Std.HashSet Name :=
      if seen.contains nm then (arr, seen) else (arr.push nm, seen.insert nm)
    for callerInfo in mdata.constants do
      let (a, s) := pushCaller callerInfo.name callerNames seenCallers
      callerNames := a; seenCallers := s
    for (bName, _) in storedBaseMap do
      let (a, s) := pushCaller bName callerNames seenCallers
      callerNames := a; seenCallers := s
    for irDecl in Lean.IR.declMapExt.getModuleEntries env modIdx do
      let (a, s) := pushCaller irDecl.name callerNames seenCallers
      callerNames := a; seenCallers := s
    for irDecl in Lean.IR.declMapExt.getModuleIREntries env modIdx do
      let (a, s) := pushCaller irDecl.name callerNames seenCallers
      callerNames := a; seenCallers := s
    for callerName in callerNames do
      let compiledConsts := match storedBaseMap[callerName]? with
        | some { value := .code code, .. } => collectLcnfPureConsts code
        | _ => collectCompiledCodeConsts env callerName
      let ownerInfo? := findOwnerInfo callerName
      let ownerName := ownerInfo?.map ConstantInfo.name |>.getD callerName
      let kernelConsts := ownerInfo?.map ConstantInfo.getUsedConstantsAsSet |>.getD {}
      if !compiledConsts.isEmpty then
        for (thmName, lhs, rhs) in localCands do
          if ownerName != lhs && ownerName != rhs then
            let fwdHit := !isReachableCached lhs rhs &&
                          (kernelConsts.isEmpty || (kernelConsts.contains lhs && !kernelConsts.contains rhs)) &&
                          (compiledConsts.contains rhs || compiledConsts.contains (Lean.Compiler.mkUnsafeRecName rhs))
            if fwdHit then
              let (o, s) := emitHit thmName lhs rhs callerName out seenLocalHit
              out := o; seenLocalHit := s
    let mut envMod ← getCompilerAuditEnv
    for scEntry in Lean.Compiler.CSimp.ext.ext.getModuleEntries envMod modIdx do
      match scEntry with
      | .global b => envMod := Lean.Compiler.CSimp.ext.addEntry envMod b
      | .scoped ns b =>
        envMod := Lean.Compiler.CSimp.ext.addScopedEntry envMod ns b
        envMod := Lean.ScopedEnvExtension.activateScoped Lean.Compiler.CSimp.ext envMod ns
    for (callerName, bStored) in storedBaseMap do
      if (env.find? callerName).isSome then
        let ownerName := (findOwnerInfo callerName).map ConstantInfo.name |>.getD callerName
        match ← compileSingleToLcnfDecl envMod callerName with
        | none => pure ()
        | some tdBase =>
          let mut activeCands : Array (Name × Name × Name) := #[]
          for (thmName, lhs, rhs) in localCands do
            if !seenLocalHit.contains (thmName, callerName) && ownerName != lhs && ownerName != rhs then
              let envCand := Lean.Compiler.CSimp.ext.addEntry envMod
                { fromDeclName := lhs, toDeclName := rhs, thmName := thmName }
              let changed := match ← compileSingleToLcnfDecl envCand callerName with
                | none => false
                | some tdCand => !lcnfDeclAlphaEqv tdBase tdCand
              if changed then
                activeCands := activeCands.push (thmName, lhs, rhs)
          if !activeCands.isEmpty then
            match ← compileSingleBaseLcnfDecl envMod callerName with
            | none =>
              out := out ++ [s!"[TurboLean.KernelGate] failed to reconstruct stored base declaration `{callerName}` in `{modLabel}` for local csimp audit"]
            | some rd =>
              if !lcnfDeclAlphaEqvModuloSpec bStored rd then
                for (thmName, lhs, rhs) in activeCands do
                  let (o, s) := emitHit thmName lhs rhs callerName out seenLocalHit
                  out := o; seenLocalHit := s
    return out
  for (rawStr, nm) in targets do
    match env.getModuleIdx? nm with
    | none =>
      violations := violations ++ [s!"[TurboLean.KernelGate] module `{rawStr}` missing from imported environment"]
    | some modIdx =>
      targetIdxs := targetIdxs.insert modIdx rawStr
      if h : modIdx.toNat < env.header.moduleData.size then
        let mdata := env.header.moduleData[modIdx.toNat]
        let mut csimpCandidates : Array (Name × Name × Name) := #[]
        for cinfo in mdata.constants do
          let declName := cinfo.name
          match cinfo with
          | .axiomInfo _ =>
            if !isAllowedAxiom patterns declName then
              violations := violations ++ [s!"[TurboLean.KernelGate] custom axiom `{declName}` in `{rawStr}` is forbidden"]
          | .inductInfo iVal =>
            if iVal.isUnsafe then
              violations := violations ++ [s!"[TurboLean.KernelGate] {unsfTag} inductive `{declName}` in `{rawStr}` is forbidden"]
            if iVal.isNested && !nestedInductiveAllowed env iVal then
              violations := violations ++ [s!"[TurboLean.KernelGate] nested inductive type `{declName}` (sea-monster risk) through a non-core container in `{rawStr}` is forbidden"]
          | _ => pure ()
          if let some (lhs, rhs) := csimpCandidatePair? cinfo then
            let isStrict := (csimpReplacementPair? env cinfo).isSome
            if !cinfo.isTheorem || !isStrict || !(← csimpAllowed declName) then
              csimpCandidates := csimpCandidates.push (declName, lhs, rhs)
          if cinfo.isUnsafe && auditHelper declName &&
             !isWhitelistedInitExecUnsafe env modIdx cinfo &&
             !((safeUnsafeCallWrapperParent? env modIdx cinfo).any (fun pc => unsafeAllowed pc.name)) &&
             !unsafeAllowed declName then
            let usesUnsafeInd := cinfo.getUsedConstantsAsSet.any fun u =>
              match env.find? u with
              | some (.inductInfo iv) => iv.isUnsafe
              | _ => false
            let canAllowUnsafe := (cinfo matches .defnInfo _ | .opaqueInfo _) &&
              (Lean.Compiler.isUnsafeRecName? declName).isNone && !usesUnsafeInd
            let hint := if canAllowUnsafe then kernelPolicyHint unsfTag declName else ""
            violations := violations ++ [s!"[TurboLean.KernelGate] {unsfTag} declaration `{declName}` in `{rawStr}` is forbidden{hint}"]
          if (cinfo.isPartial || (Lean.Compiler.isUnsafeRecName? declName).isSome) &&
             !(← isCompilerPartialRecDefn env hydratedEnvRef cliqueCacheRef patterns {} (some modIdx) cinfo #[] stubs.contains allowSorry) then
            violations := violations ++ [s!"[TurboLean.KernelGate] forged or unpaired _unsafe_rec/partial declaration `{declName}` in `{rawStr}` is forbidden"]
          if (Lean.isExtern env declName || (Lean.Compiler.getImplementedBy? env declName).isSome) &&
             !isWhitelistedInitExecBridge env modIdx declName &&
             !((safeUnsafeCallWrapperBridgeParent? env modIdx declName).any (fun pc => unsafeAllowed pc.name)) &&
             !isPinnedFfiOpaque env ffiAllow modIdx cinfo &&
             !implByAllowed declName then
            let hint := if !Lean.isExtern env declName && (Lean.Compiler.getImplementedBy? env declName).isSome then kernelPolicyHint "implemented_by" declName else ""
            violations := violations ++ [s!"[TurboLean.KernelGate] extern/implemented_by bypass on `{declName}` in `{rawStr}` is forbidden{hint}"]
          let cinfoAxs : Array Name := Id.run do
            let mut acc := axMap[declName]?.getD #[]
            match cinfo with
            | .thmInfo tv =>
              if !stubs.contains declName then
                for u in tv.type.getUsedConstants ++ tv.value.getUsedConstants do
                  if let some ciU := env.find? u then
                    if ciU matches .axiomInfo _ && !isAllowedAxiom patterns u && !acc.contains u then
                      acc := acc.push u
                  for ax in axMap[u]?.getD #[] do
                    if !acc.contains ax then
                      acc := acc.push ax
            | _ => pure ()
            return acc
          for ax in cinfoAxs do
            if allowSorry && ax == sorryAxName && !stubs.contains declName then
              let userNm := canonicalName (Lean.privateToUserName declName)
              if !userNm.isEmpty && !((userNm.splitOn "._").length > 1) && !((userNm.splitOn "_proof_").length > 1) && !(seenSorry[userNm]?.getD false) then
                seenSorry := seenSorry.insert userNm true
                sorryDecls := sorryDecls ++ [userNm]
              else if sorryDecls.isEmpty && !userNm.isEmpty && !(seenSorry[userNm]?.getD false) then
                seenSorry := seenSorry.insert userNm true
                sorryDecls := sorryDecls ++ [userNm]
            else if !(allowSorry && ax == sorryAxName) then
              violations := violations ++ [s!"[TurboLean.KernelGate] declaration `{declName}` in `{rawStr}` transitively depends on disallowed axiom `{ax}`"]
        let mut importedScopedCands : Array (Name × Name × Name) := #[]
        for i in [:env.header.moduleData.size] do
          let mIdx : ModuleIdx := i
          if mIdx != modIdx then
            if let some ownerMod := env.header.moduleNames[i]? then
              if !(ownerMod.getRoot == `Init && (← isSysrootMod ownerMod)) then
                for scEntry in Lean.Compiler.CSimp.ext.ext.getModuleEntries env mIdx do
                  if let .scoped _ entry := scEntry then
                    let matchesEntry := (env.find? entry.thmName).any fun ci =>
                      match csimpReplacementPair? env ci with
                      | some (lhs, rhs) => lhs == entry.fromDeclName && rhs == entry.toDeclName
                      | _ => false
                    if !((env.find? entry.thmName).any (·.isTheorem) && matchesEntry && (← csimpAllowed entry.thmName)) then
                      importedScopedCands := importedScopedCands.push (entry.thmName, entry.fromDeclName, entry.toDeclName)
        violations := violations ++ (← auditModuleLocalCSimp modIdx rawStr csimpCandidates importedScopedCands)
        for extraName in mdata.extraConstNames do
          if (Lean.isExtern env extraName || (Lean.Compiler.getImplementedBy? env extraName).isSome) &&
             !isWhitelistedInitExecBridge env modIdx extraName &&
             !((safeUnsafeCallWrapperBridgeParent? env modIdx extraName).any (fun pc => unsafeAllowed pc.name)) &&
             !((env.find? extraName).any (isPinnedFfiOpaque env ffiAllow modIdx)) &&
             !implByAllowed extraName then
            let hint := if !Lean.isExtern env extraName && (Lean.Compiler.getImplementedBy? env extraName).isSome then kernelPolicyHint "implemented_by" extraName else ""
            violations := violations ++ [s!"[TurboLean.KernelGate] extern/implemented_by bypass on auxiliary `{extraName}` in `{rawStr}` is forbidden{hint}"]
      else
        violations := violations ++ [s!"[TurboLean.KernelGate] module `{rawStr}` index out of bounds"]
  if isImportAudit then
    let mut allUnallowedScoped : Array (ModuleIdx × (Name × Name × Name)) := #[]
    for i in [:env.header.moduleData.size] do
      let mIdx : ModuleIdx := i
      if let some ownerMod := env.header.moduleNames[i]? then
        if !(ownerMod.getRoot == `Init && (← isSysrootMod ownerMod)) then
          for scEntry in Lean.Compiler.CSimp.ext.ext.getModuleEntries env mIdx do
            if let .scoped _ entry := scEntry then
              let matchesEntry := (env.find? entry.thmName).any fun ci =>
                match csimpReplacementPair? env ci with
                | some (lhs, rhs) => lhs == entry.fromDeclName && rhs == entry.toDeclName
                | _ => false
              if !((env.find? entry.thmName).any (·.isTheorem) && matchesEntry && (← csimpAllowed entry.thmName)) then
                allUnallowedScoped := allUnallowedScoped.push (mIdx, (entry.thmName, entry.fromDeclName, entry.toDeclName))
    for i in [:env.header.moduleData.size] do
      let depIdx : ModuleIdx := i
      if !targetIdxs.contains depIdx then
        let some depModName := env.header.moduleNames[i]? | continue
        if !(← isSysrootMod depModName) then
          let mut depCands : Array (Name × Name × Name) := #[]
          for cinfo in env.header.moduleData[i]!.constants do
            if let some (lhs, rhs) := csimpCandidatePair? cinfo then
              let isStrict := (csimpReplacementPair? env cinfo).isSome
              if !cinfo.isTheorem || !isStrict || !(← csimpAllowed cinfo.name) then
                depCands := depCands.push (cinfo.name, lhs, rhs)
          let depScoped := allUnallowedScoped.filterMap fun (mIdx, c) => if mIdx != depIdx then some c else none
          if !depCands.isEmpty || !depScoped.isEmpty then
            violations := violations ++ (← auditModuleLocalCSimp depIdx depModName.toString depCands depScoped)
  let mut seenCSimp : Std.HashSet (Name × Name × Name) := {}
  let entryTouchesTarget (e : Lean.Compiler.CSimp.Entry) : Bool :=
    [e.thmName, e.fromDeclName, e.toDeclName].any fun nm =>
      match env.getModuleIdxFor? nm with
      | some idx => targetIdxs.contains idx
      | none => false
  let defaultTargetLabel := targets[0]?.map Prod.fst |>.getD "<import>"
  let checkCSimpEntry (e : Lean.Compiler.CSimp.Entry) (ownerModIdx? : Option ModuleIdx := none) : IO (List String) := do
    if !isImportAudit && !(ownerModIdx?.any targetIdxs.contains || entryTouchesTarget e) then
      return []
    if isImportAudit && !(ownerModIdx?.any targetIdxs.contains || entryTouchesTarget e) then
      if let some ownerIdx := ownerModIdx? then
        if let some ownerMod := env.header.moduleNames[ownerIdx.toNat]? then
          if ownerMod.getRoot == `Init && (← isSysrootMod ownerMod) then
            return []
    let matchesEntry := (env.find? e.thmName).any fun ci =>
      match csimpReplacementPair? env ci with
      | some (lhs, rhs) => lhs == e.fromDeclName && rhs == e.toDeclName
      | _ => false
    if (env.find? e.thmName).any (·.isTheorem) && matchesEntry && (← csimpAllowed e.thmName) then
      return []
    let mut out : List String := []
    let mut seenMod : Std.HashMap ModuleIdx Bool := {}
    let candidateIdxs := (match ownerModIdx? with | some idx => [idx] | none => []) ++
      ([e.thmName, e.fromDeclName, e.toDeclName].filterMap (env.getModuleIdxFor? ·))
    for idx in candidateIdxs do
      if !(seenMod[idx]?.getD false) then
        if let some modLabel := targetIdxs[idx]? then
          seenMod := seenMod.insert idx true
          out := out ++ [s!"[TurboLean.KernelGate] csimp replacement `{e.thmName}` ({e.fromDeclName} -> {e.toDeclName}) touching `{modLabel}` is forbidden{kernelPolicyHint "csimp" e.thmName}"]
    if out.isEmpty && isImportAudit then
      let modLabel := (ownerModIdx?.bind fun idx => env.header.moduleNames[idx.toNat]?.map Name.toString).getD defaultTargetLabel
      out := [s!"[TurboLean.KernelGate] csimp replacement `{e.thmName}` ({e.fromDeclName} -> {e.toDeclName}) touching `{modLabel}` is forbidden{kernelPolicyHint "csimp" e.thmName}"]
    return out
  let mut activeCSimpEntries : List (String × String × String) := []
  for (ownerModIdx?, entry) in allCSimpEntries do
    let key := (entry.thmName, entry.fromDeclName, entry.toDeclName)
    if !seenCSimp.contains key && (isImportAudit || ownerModIdx?.any targetIdxs.contains || entryTouchesTarget entry) then
      seenCSimp := seenCSimp.insert key
      activeCSimpEntries := activeCSimpEntries ++ [(entry.thmName.toString, entry.fromDeclName.toString, entry.toDeclName.toString)]
      violations := violations ++ (← checkCSimpEntry entry ownerModIdx?)
  return (violations, sorryDecls, activeCSimpEntries)

/-- Audit a single compiled shard module: like `auditModuleSlice`, but exempts validated prefix
    stubs named in `stubOk` and also returns the module's non-stub theorems (plus their canonical
    `statement-v1` kernel type hashes), read from the kernel environment (never from elaboration
    output) so the host can confirm every audited target was actually declared with the expected
    kernel type. -/
def auditShardModule (target : String × Name) (ffiAllow : Array (Name × Name × String))
    (stubOk : Array String) (fastMap : List (String × String) := [])
    (allowSorry : Bool := false) :
    IO (List String × Array String × List (String × String) × List String × List (String × String × String)) := do
  let patterns := (((← IO.getEnv "TURBO_LEAN_ALLOWED_AXIOMS").getD "").splitOn ",").filterMap fun p =>
    let t := p.trimAscii.toString
    if t.isEmpty then none else some t
  let csimpPatterns := (((← IO.getEnv "TURBO_LEAN_ALLOWED_CSIMP").getD "").splitOn ",").filterMap fun p =>
    let t := p.trimAscii.toString
    if t.isEmpty then none else some t
  let unsafePatterns := (((← IO.getEnv "TURBO_LEAN_ALLOWED_UNSAFE").getD "").splitOn ",").filterMap fun p =>
    let t := p.trimAscii.toString
    if t.isEmpty then none else some t
  let implByPatterns := (((← IO.getEnv "TURBO_LEAN_ALLOWED_IMPLEMENTED_BY").getD "").splitOn ",").filterMap fun p =>
    let t := p.trimAscii.toString
    if t.isEmpty then none else some t
  try
    let env ← Lean.importModules #[{ module := target.2, importAll := true }] {} 0 #[] true false .private
    let targetModIdx? := env.getModuleIdx? target.2
    let consts := match targetModIdx? with
      | some modIdx => (env.header.moduleData[modIdx.toNat]?).map (·.constants) |>.getD #[]
      | none => #[]
    let (stubs, stubViolations) := collectStubDecls consts stubOk
    let constNames := consts.map (·.name)
    let isImportedOrig := fun (origName : Name) =>
      match env.getModuleIdxFor? origName with
      | some idx => some idx != targetModIdx?
      | none => false
    let fastViolations := validateFastVerifyKernelMap env constNames isImportedOrig stubs.contains fastMap
    let mappedGenToOrig : Std.HashMap Name Name :=
      (parseFastVerifyMapEntries fastMap |>.getD []).foldl (fun acc (origN, genN) => acc.insert genN origN) {}
    let mut decls : Array String := #[]
    let mut declTypes : List (String × String) := []
    let mut seen : Std.HashMap String Bool := {}
    for c in consts do
      if c.isTheorem && !stubs.contains c.name then
        let canonName := mappedGenToOrig[c.name]?.getD c.name
        let userNm := canonicalName (Lean.privateToUserName canonName)
        let rawNm := canonicalName c.name
        decls := decls.push userNm
        let h := kernelStatementHash c (some target.2)
        if !(seen[userNm]?.getD false) then
          seen := seen.insert userNm true
          declTypes := declTypes ++ [(userNm, h)]
        if rawNm != userNm && !(seen[rawNm]?.getD false) then
          seen := seen.insert rawNm true
          declTypes := declTypes ++ [(rawNm, h)]
    let (impViolations, impSorryDecls, impCSimpEntries) ← auditImportedModulesInEnv env #[target] ffiAllow patterns csimpPatterns stubs unsafePatterns implByPatterns false allowSorry
    return (stubViolations ++ fastViolations ++ impViolations, decls, declTypes, impSorryDecls, impCSimpEntries)
  catch e =>
    return ([s!"[TurboLean.KernelGate] failed to import `{target.1}` for audit: {e}"], #[], [], [], [])

def auditModuleSlice (slice : Array (String × Name)) (ffiAllow : Array (Name × Name × String) := #[])
    (skipChildReplay : Bool := false) (allowSorry : Bool := false)
    (isImportAudit : Bool := false) : IO (List String × List (String × String × String)) := do
  if slice.isEmpty then
    return ([], [])
  let patterns := (((← IO.getEnv "TURBO_LEAN_ALLOWED_AXIOMS").getD "").splitOn ",").filterMap fun p =>
    let t := p.trimAscii.toString
    if t.isEmpty then none else some t
  let csimpPatterns := (((← IO.getEnv "TURBO_LEAN_ALLOWED_CSIMP").getD "").splitOn ",").filterMap fun p =>
    let t := p.trimAscii.toString
    if t.isEmpty then none else some t
  let unsafePatterns := (((← IO.getEnv "TURBO_LEAN_ALLOWED_UNSAFE").getD "").splitOn ",").filterMap fun p =>
    let t := p.trimAscii.toString
    if t.isEmpty then none else some t
  let implByPatterns := (((← IO.getEnv "TURBO_LEAN_ALLOWED_IMPLEMENTED_BY").getD "").splitOn ",").filterMap fun p =>
    let t := p.trimAscii.toString
    if t.isEmpty then none else some t
  let imports : Array Import := slice.map fun (_, nm) =>
    ({ module := nm, importAll := true } : Import)
  let batchRes ← try
    let env ← Lean.importModules imports {} 0 #[] true false .private
    pure (Except.ok env)
  catch e =>
    pure (Except.error (toString e))
  match batchRes with
  | .ok env =>
    let (vs, _, csimpEntries) ← auditImportedModulesInEnv env slice ffiAllow patterns csimpPatterns {} unsafePatterns implByPatterns skipChildReplay allowSorry isImportAudit
    return (vs, csimpEntries)
  | .error errMsg =>
    if slice.size == 1 then
      let (rawStr, _) := slice[0]!
      return ([s!"[TurboLean.KernelGate] failed to import `{rawStr}` for audit: {errMsg}"], [])
    -- Compacted `.olean` import regions are never unmapped within a single OS process; bisecting
    -- `Lean.importModules` in-process would accumulate mappings across retries and exhaust the
    -- untrusted 8 GiB `RLIMIT_DATA` cap. Spawn fresh OS child processes for each half instead.
    let app := (← IO.appPath).toString
    let ffiFlags : Array String := ffiAllow.map fun (m, d, sym) =>
      s!"--ffi-allow={m}={d}={sym}"
    let replayFlags : Array String := if skipChildReplay then #["--skip-child-replay"] else #[]
    let sorryFlags : Array String := if allowSorry then #["--allow-sorry"] else #[]
    let importFlags : Array String := if isImportAudit then #["--audit-imports"] else #[]
    let runSubSlice (sub : Array (String × Name)) : IO (List String × List (String × String × String)) := do
      let modFlags := sub.map (·.1)
      let child ← IO.Process.output {
        cmd := app
        args := #["--audit-modules"] ++ importFlags ++ replayFlags ++ sorryFlags ++ ffiFlags ++ modFlags
      }
      let lastJson? := (child.stdout.splitOn "\n").reverse.find? fun l =>
        let t := l.trimAscii.toString
        t.startsWith "{" && t.endsWith "}"
      if child.exitCode == 0 then
        let subCSimp : List (String × String × String) := Id.run do
          let some jl := lastJson? | return []
          let .ok j := Lean.Json.parse jl | return []
          let .ok arr := j.getObjValAs? (Array (String × String × String)) "csimp_entries" | return []
          return arr.toList
        return ([], subCSimp)
      let detail := (lastJson?.getD child.stdout).trimAscii.toString
      let errTail := child.stderr.trimAscii.toString
      let summary := if detail.isEmpty then errTail else if errTail.isEmpty then detail else s!"{detail} ({errTail})"
      return ([s!"[TurboLean.KernelGate] sub-batch audit failed (exit {child.exitCode}) on {modFlags.toList}: {summary}"], [])
    let mid := slice.size / 2
    let (v1, c1) ← runSubSlice (slice.extract 0 mid)
    let (v2, c2) ← runSubSlice (slice.extract mid slice.size)
    return (v1 ++ v2, c1 ++ c2)

def auditCompiledModules (modNames : List String) (ffiAllow : Array (Name × Name × String) := #[])
    (skipChildReplay : Bool := false) (allowSorry : Bool := false)
    (isImportAudit : Bool := false) : IO (Bool × List String × List (String × String × String)) := do
  let mut parsed : Array (String × Name) := #[]
  let mut initViolations : List String := []
  for raw in modNames do
    let trimmed := raw.trimAscii.toString
    if !trimmed.isEmpty then
      let nm := parseModuleName trimmed
      if nm.isAnonymous then
        initViolations := initViolations ++ [s!"[TurboLean.KernelGate] invalid empty/anonymous module name `{raw}`"]
      else
        parsed := parsed.push (trimmed, nm)
  if parsed.isEmpty then
    return (initViolations.isEmpty, initViolations, [])
  let (sliceViolations, csimpEntries) ← auditModuleSlice parsed ffiAllow skipChildReplay allowSorry isImportAudit
  let allViolations := initViolations ++ sliceViolations
  return (allViolations.isEmpty, allViolations, csimpEntries)

end TurboLean.ZygoteWorker
