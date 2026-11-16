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

open Lean Elab

namespace TurboLean.ZygoteWorker

set_option hygiene false in
local elab "#emit_zygote_toolchain_shims" : command => do
  let env ← getEnv
  Command.elabCommand (← if env.contains `Lean.Kernel.Environment.replay then
    `(command| def replayKernelConstants (constants : Std.HashMap Name ConstantInfo)
        (env : Environment) : IO Kernel.Environment :=
      Kernel.Environment.replay constants env.toKernelEnv)
    else
    `(command| def replayKernelConstants (constants : Std.HashMap Name ConstantInfo)
        (env : Environment) : IO Kernel.Environment := do
      return (← Environment.replay constants env).toKernelEnv))
  let rec arity : Expr → Nat
    | .forallE _ _ b _ => arity b + 1
    | _ => 0
  let some addDecl := env.find? `Lean.Kernel.Environment.addDeclCore
    | throwError "missing kernel declaration checker"
  Command.elabCommand (← if arity addDecl.type == 5 then
    `(command| def checkKernelDecl (env : Kernel.Environment) (decl : Declaration) :=
      env.addDeclCore 0 0 decl (cancelTk? := none))
    else
    `(command| def checkKernelDecl (env : Kernel.Environment) (decl : Declaration) :=
      env.addDeclCore 0 decl (cancelTk? := none)))
  Command.elabCommand (← if env.contains `Lean.ImportArtifacts.ofArrays then
    `(command| def publicImportArtifacts (oleanParts irParts : Array System.FilePath) : ImportArtifacts :=
      ImportArtifacts.ofArrays #[oleanParts, irParts])
    else
    `(command| def publicImportArtifacts (oleanParts _irParts : Array System.FilePath) : ImportArtifacts :=
      ImportArtifacts.ofArray oleanParts))
  Command.elabCommand (← if env.contains `Lean.ReducibilityStatus.instanceReducible then
    `(command| private def formatReducibilityStatus : ReducibilityStatus → String
      | .reducible => "reducible"
      | .semireducible => "semireducible"
      | .irreducible => "irreducible"
      | .implicitReducible => "implicit_reducible"
      | .instanceReducible => "instance_reducible")
    else
    `(command| private def formatReducibilityStatus : ReducibilityStatus → String
      | .reducible => "reducible"
      | .semireducible => "semireducible"
      | .irreducible => "irreducible"
      | .implicitReducible => "implicit_reducible"))
  let some monoType := env.find? `Lean.Compiler.LCNF.monoTypeExt
    | throwError "missing monomorphic type extension"
  let hasMonoEntries := monoType.type.getAppFn.isConstOf `Lean.MapDeclarationExtension
  Command.elabCommand (← if hasMonoEntries then
    `(command| def monoTypeModuleEntries (env : Environment) (idx : ModuleIdx) : Array (Name × Expr) :=
      Compiler.LCNF.monoTypeExt.getModuleEntries env idx)
    else
    `(command| def monoTypeModuleEntries (_ : Environment) (_ : ModuleIdx) : Array (Name × Expr) := #[]))
  Command.elabCommand (← `(command| def hasMonoTypeModuleEntries : Bool := $(quote hasMonoEntries)))
  Command.elabCommand (← if env.contains `Lean.MessageData.ofOriginatingSyntax then
    `(command| def originatingMessage? : MessageData → Option MessageData
      | .ofOriginatingSyntax _ inner => some inner
      | _ => none)
    else
    `(command| def originatingMessage? (_ : MessageData) : Option MessageData := none))

#emit_zygote_toolchain_shims


private def formatInlineAttr (i : Option Compiler.InlineAttributeKind) : String :=
  match i with
  | none => "none"
  | some .inline => "inline"
  | some .noinline => "noinline"
  | some .macroInline => "macro_inline"
  | some .alwaysInline => "always_inline"
  | some .inlineIfReduce => "inline_if_reduce"

private def formatHintsStr : ReducibilityHints → String
  | .opaque => "opaque"
  | .abbrev => "abbrev"
  | .regular h => s!"regular:{h.toNat}"

private def formatQuotStr : QuotKind → String
  | .type => "type"
  | .ctor => "ctor"
  | .lift => "lift"
  | .ind => "ind"

private def formatConstantExportPayload (c : ConstantInfo) (localMod? : Option Name) : (String × String × String) :=
  let norm := TurboLean.StatementHash.normalizeLocalPrivateName localMod?
  let stmtHash := kernelStatementHash c localMod?
  match c with
  | .defnInfo v =>
    let valJson := TurboLean.StatementHash.node "defn-val-v1" #[
      TurboLean.StatementHash.exprJson norm v.value,
      toJson (formatHintsStr v.hints),
      toJson (reprStr v.safety)
    ]
    ("def_exposed", stmtHash, TurboLean.Blake3.blake3Bytes valJson.compress.toUTF8)
  | .opaqueInfo v =>
    let valJson := TurboLean.StatementHash.node "opaque-val-v1" #[
      TurboLean.StatementHash.exprJson norm v.value,
      toJson v.isUnsafe
    ]
    ("opaque", stmtHash, TurboLean.Blake3.blake3Bytes valJson.compress.toUTF8)
  | .thmInfo _ => ("theorem", stmtHash, "")
  | .axiomInfo v => ("axiom_or_unexposed", stmtHash, if v.isUnsafe then "un" ++ "safe" else "")
  | .quotInfo v => ("quot", stmtHash, formatQuotStr v.kind)
  | .inductInfo v =>
    let indJson := TurboLean.StatementHash.node "induct-v1" #[
      toJson v.numParams,
      toJson v.numIndices,
      toJson (v.all.map (TurboLean.StatementHash.nameJson norm)),
      toJson (v.ctors.map (TurboLean.StatementHash.nameJson norm)),
      toJson v.numNested,
      toJson v.isRec,
      toJson v.isUnsafe,
      toJson v.isReflexive
    ]
    ("inductive", stmtHash, TurboLean.Blake3.blake3Bytes indJson.compress.toUTF8)
  | .ctorInfo v =>
    let ctorJson := TurboLean.StatementHash.node "ctor-v1" #[
      TurboLean.StatementHash.nameJson norm v.induct,
      toJson v.cidx,
      toJson v.numParams,
      toJson v.numFields,
      toJson v.isUnsafe
    ]
    ("ctor", stmtHash, TurboLean.Blake3.blake3Bytes ctorJson.compress.toUTF8)
  | .recInfo v =>
    let recJson := TurboLean.StatementHash.node "rec-v1" #[
      toJson (v.all.map (TurboLean.StatementHash.nameJson norm)),
      toJson v.numParams,
      toJson v.numIndices,
      toJson v.numMotives,
      toJson v.numMinors,
      toJson v.k,
      toJson v.isUnsafe,
      toJson (v.rules.map fun r =>
        TurboLean.StatementHash.node "rule" #[
          TurboLean.StatementHash.nameJson norm r.ctor,
          toJson r.nfields,
          TurboLean.StatementHash.exprJson norm r.rhs
        ])
    ]
    ("rec", stmtHash, TurboLean.Blake3.blake3Bytes recJson.compress.toUTF8)

private def formatAttrKind : AttributeKind → String
  | .global => "global"
  | .local => "local"
  | .scoped => "scoped"

private def formatDiscrKey (norm : Name → Name) : Meta.DiscrTree.Key → String
  | .star => "*"
  | .other => "other"
  | .arrow => "->"
  | .lit (.natVal n) => s!"nat:{n}"
  | .lit (.strVal s) => s!"str:{jsonEscape s}"
  | .fvar fid a => s!"fvar:{canonicalName (norm fid.name)}/{a}"
  | .const n a => s!"const:{canonicalName (norm n)}/{a}"
  | .proj s i a => s!"proj:{canonicalName (norm s)}.{i}/{a}"

private def formatInstanceEntry (norm : Name → Name) (scopeTag : String) (e : Meta.InstanceEntry) : String :=
  let gname := match e.globalName? with
    | some n => canonicalName (norm n)
    | none => ""
  let valStr := (TurboLean.StatementHash.exprJson norm e.val).compress
  let valHash := TurboLean.Blake3.blake3Bytes valStr.toUTF8
  let keysStr := String.intercalate "," (e.keys.toList.map (formatDiscrKey norm))
  let ordStr := String.intercalate "," (e.synthOrder.toList.map toString)
  s!"{scopeTag}:g={gname}:p={e.priority}:k={formatAttrKind e.attrKind}:ord=[{ordStr}]:keys=[{keysStr}]:val={valHash}"

private def formatSimpEntry (norm : Name → Name) (scopeTag : String) (se : Meta.SimpEntry) : String :=
  match se with
  | .thm t =>
    let origStr := match t.origin with
      | .decl n ph inv => s!"decl:{canonicalName (norm n)}:{reprStr ph}:{inv}"
      | .fvar fid => s!"fvar:{canonicalName (norm fid.name)}"
      | .stx id _ => s!"stx:{canonicalName (norm id)}"
      | .other n => s!"other:{canonicalName (norm n)}"
    let proofHash := TurboLean.Blake3.blake3Bytes (TurboLean.StatementHash.exprJson norm t.proof).compress.toUTF8
    let keysStr := String.intercalate "," (t.keys.toList.map (formatDiscrKey norm))
    let lparams := String.intercalate "," (t.levelParams.toList.map (fun u => canonicalName (norm u)))
    s!"{scopeTag}:thm:{origStr}:prio={t.priority}:post={t.post}:perm={t.perm}:rfl={t.rfl}:lvls=[{lparams}]:keys=[{keysStr}]:pf={proofHash}"
  | .toUnfold d => s!"{scopeTag}:unfold:{canonicalName (norm d)}"
  | .toUnfoldThms n thms =>
    s!"{scopeTag}:unfoldThms:{canonicalName (norm n)}:{String.intercalate "," (thms.toList.map (fun x => canonicalName (norm x)))}"

private def formatExternEntry (e : ExternEntry) : String :=
  match e with
  | .adhoc b => s!"adhoc:{canonicalName b}"
  | .inline b pat => s!"inline:{canonicalName b}:{jsonEscape pat}"
  | .standard b fn => s!"std:{canonicalName b}:{jsonEscape fn}"
  | .opaque => "opaque"

private def formatConstKind : ConstantKind → String
  | .defn => "defn"
  | .thm => "thm"
  | .axiom => "axiom"
  | .opaque => "opaque"
  | .quot => "quot"
  | .induct => "induct"
  | .ctor => "ctor"
  | .recursor => "rec"

private def formatCoeFnType : Meta.CoeFnType → String
  | .coe => "coe"
  | .coeFun => "coeFun"
  | .coeSort => "coeSort"

private def formatHeadIndex (norm : Name → Name) : HeadIndex → String
  | .fvar id => s!"fvar:{canonicalName id.name}"
  | .mvar id => s!"mvar:{canonicalName id.name}"
  | .const nm => s!"const:{canonicalName (norm nm)}"
  | .proj sn idx => s!"proj:{canonicalName (norm sn)}:{idx}"
  | .lit (.natVal n) => s!"nat:{n}"
  | .lit (.strVal s) => s!"str:{jsonEscape s}"
  | .sort => "sort"
  | .lam => "lam"
  | .forallE => "forallE"

private def formatGrindEntry (norm : Name → Name) (scopeTag : String) (e : Meta.Grind.Entry) : String :=
  match e with
  | .ext d => s!"{scopeTag}:ext:{canonicalName (norm d)}"
  | .funCC d => s!"{scopeTag}:funCC:{canonicalName (norm d)}"
  | .cases d eager => s!"{scopeTag}:cases:{canonicalName (norm d)}:{eager}"
  | .ematch thm =>
    let orig := canonicalName (norm thm.origin.key)
    let pfHash := TurboLean.Blake3.blake3Bytes (TurboLean.StatementHash.exprJson norm thm.proof).compress.toUTF8
    let pats := String.intercalate "," (thm.patterns.map fun p =>
      TurboLean.Blake3.blake3Bytes (TurboLean.StatementHash.exprJson norm p).compress.toUTF8)
    let syms := String.intercalate "," (thm.symbols.map (formatHeadIndex norm))
    s!"{scopeTag}:ematch:{orig}:np={thm.numParams}:min={thm.minIndexable}:kind={reprStr thm.kind}:syms=[{syms}]:pats=[{pats}]:pf={pfHash}"
  | .inj thm =>
    let orig := canonicalName (norm thm.origin.key)
    let pfHash := TurboLean.Blake3.blake3Bytes (TurboLean.StatementHash.exprJson norm thm.proof).compress.toUTF8
    let syms := String.intercalate "," (thm.symbols.map (formatHeadIndex norm))
    s!"{scopeTag}:inj:{orig}:syms=[{syms}]:pf={pfHash}"

private def formatLcnfSignature {pu : Compiler.LCNF.Purity} (norm : Name → Name) (sig : Compiler.LCNF.Signature pu) : String :=
  let lvls := String.intercalate "," (sig.levelParams.map (fun u => canonicalName (norm u)))
  let tyHash := TurboLean.Blake3.blake3Bytes (TurboLean.StatementHash.exprJson norm sig.type).compress.toUTF8
  let paramsStr := String.intercalate "," (sig.params.toList.map fun p =>
    let pTy := TurboLean.Blake3.blake3Bytes (TurboLean.StatementHash.exprJson norm p.type).compress.toUTF8
    s!"{pTy}:{p.borrow}")
  s!"{canonicalName (norm sig.name)}:lvls=[{lvls}]:ty={tyHash}:safe={sig.safe}:params=[{paramsStr}]"

private def formatLcnfDeclIO (env : Environment) (norm : Name → Name) (phase : Compiler.LCNF.Phase) (d : Compiler.LCNF.Decl .pure) : IO String := do
  let sigPart := formatLcnfSignature norm d.toSignature
  let inl := formatInlineAttr d.inlineAttr?
  let valTag ← match d.value with
    | .extern ex =>
      let ents := String.intercalate "," (ex.entries.map formatExternEntry)
      pure s!"extern:[{ents}]"
    | .code _ =>
      let coreCtx : Core.Context := { fileName := "<pubsig>", fileMap := FileMap.ofString "" }
      let coreState : Core.State := { env := env }
      try
        let (fmt, _) ← (Compiler.LCNF.ppDecl' d phase).toIO coreCtx coreState
        let txt := fmt.pretty
        pure s!"code:{TurboLean.Blake3.blake3Bytes txt.toUTF8}"
      catch e =>
        throw (IO.userError s!"failed to format LCNF decl `{d.name}`: {e.toString}")
  return s!"{sigPart}:rec={d.recursive}:inl={inl}:{valTag}"

private def formatNoConfusionInfo : NoConfusionInfo → String
  | .regular arity lhs rhs => s!"reg:{arity}:{lhs}:{rhs}"
  | .perCtor arity fields => s!"ctor:{arity}:{fields}"

private def formatTrivialStructOpt (norm : Name → Name) : Option Compiler.LCNF.TrivialStructureInfo → String
  | none => "none"
  | some tsi => s!"some:{canonicalName (norm tsi.ctorName)}:{tsi.numParams}:{tsi.fieldIdx}"

private def formatCtorFieldInfo (norm : Name → Name) : Compiler.LCNF.CtorFieldInfo → String
  | .erased => "erased"
  | .void => "void"
  | .usize i => s!"usize:{i}"
  | .object i ty =>
    let tyH := TurboLean.Blake3.blake3Bytes (TurboLean.StatementHash.exprJson norm ty).compress.toUTF8
    s!"obj:{i}:{tyH}"
  | .scalar sz off ty =>
    let tyH := TurboLean.Blake3.blake3Bytes (TurboLean.StatementHash.exprJson norm ty).compress.toUTF8
    s!"scalar:{sz}:{off}:{tyH}"

private def isWhitelistedPublicSigExtName (extStr : String) : Bool :=
  extStr == "Lean.Meta.simpExtension"
  || extStr == "Lean.Compiler.CSimp.ext"
  || extStr == "Lean.Meta.instanceExtension"
  || extStr == "Lean.Meta.defaultInstanceExtension"
  || extStr == "Lean.classExtension"
  || extStr == "_private.Lean.Structure.0.Lean.structureExt"
  || extStr == "Lean.projectionFnInfoExt"
  || extStr == "Lean.protectedExt"
  || extStr == "Lean.noConfusionExt"
  || extStr == "Lean.auxRecExt"
  || extStr == "_private.Lean.AuxRecursor.0.Lean.sparseCasesOnExt"
  || extStr == "recExt"
  || extStr == "reducibilityCore"
  || extStr == "reducibilityExtra"
  || extStr == "Lean.defeqAttr"
  || extStr == "Lean.backwardDefeqAttr"
  || extStr == "Lean.Compiler.inlineAttrs"
  || extStr == "Lean.externAttr"
  || extStr == "Lean.Compiler.implementedByAttr"
  || extStr == "Lean.exportAttr"
  || extStr == "Lean.Compiler.specializeAttr"
  || extStr == "Lean.Compiler.nospecializeAttr"
  || extStr == "Lean.Compiler.weakSpecializeAttr"
  || extStr == "Lean.matchPatternAttr"
  || extStr == "Lean.Linter.deprecatedAttr"
  || extStr == "Lean.deprecatedModuleExt"
  || extStr == "Lean.Elab.Term.elabAsElim"
  || extStr == "Lean.Meta.Ext.extExtension"
  || extStr == "Lean.Meta.coeExt"
  || extStr == "Lean.Meta.Grind.grindExt"
  || extStr == "Lean.Meta.completionBlackListExt"
  || extStr == "_private.Lean.OriginalConstKind.0.Lean.privateConstKindsExt"
  || extStr == "Lean.noncomputableExt"
  || extStr == "Lean.aliasExtension"
  || extStr == "_private.Lean.ResolveName.0.Lean.aliasExtension"
  || extStr == "_private.Lean.Namespace.0.Lean.namespacesExt"
  || extStr == "_private.Lean.Compiler.ModPkgExt.0.Lean.modPkgExt"
  || extStr == "Lean.IR.declMapExt"
  || extStr == "Lean.Compiler.LCNF.baseExt"
  || extStr == "Lean.Compiler.LCNF.monoExt"
  || extStr == "Lean.Compiler.LCNF.impureSigExt"
  || (hasMonoTypeModuleEntries && extStr == "Lean.Compiler.LCNF.monoTypeExt")
  || extStr == "_private.Lean.Compiler.LCNF.MonoTypes.0.Lean.Compiler.LCNF.trivialStructureInfoExt"
  || extStr == "_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.impureTypeExt"
  || extStr == "_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.impureTrivialStructureInfoExt"
  || extStr == "_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.ctorLayoutExt"
  || extStr == "_private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt"

def dumpPublicSignatureJson (modStr : String) : IO String := do
  let nm := parseModuleName modStr
  if nm.isAnonymous then
    throw (IO.userError s!"invalid module name `{modStr}`")
  let oleanPath ← Lean.findOLean nm
  let srvPath := System.FilePath.mk (oleanPath.toString ++ ".server")
  let irPath := oleanPath.withExtension "ir"
  let irSigPath := System.FilePath.mk (irPath.toString ++ ".sig")
  let hasSrv ← srvPath.pathExists
  let hasIrSig ← irSigPath.pathExists
  let hasIr ← irPath.pathExists
  let oleanParts := if hasSrv then #[oleanPath, srvPath] else #[oleanPath]
  let irParts := if hasIrSig then (if hasIr then #[irSigPath, irPath] else #[irSigPath]) else #[]
  let arts : NameMap ImportArtifacts :=
    (∅ : NameMap ImportArtifacts).insert nm (publicImportArtifacts oleanParts irParts)
  let env ← Lean.importModules #[{ module := nm, isExported := true, importAll := false }] {} 0 #[] true false .exported arts
  let some idx := env.getModuleIdx? nm | throw (IO.userError s!"module `{modStr}` not imported")
  let md := env.header.moduleData[idx.toNat]!
  let isMod := md.isModule
  let norm := TurboLean.StatementHash.normalizeLocalPrivateName (some nm)
  let mut hasOpaqueExt := false
  let mut hasNamespacesExt := false
  let mut hasExportedAxiomsExt := false
  let mut aliasMap : Std.HashMap Name (Array String) := {}
  let mut allExportedAliases : Array String := #[]
  let mut reducibilityExtraEntries : Array String := #[]
  let mut nsExtOpt : Option (PersistentEnvExtension EnvExtensionEntry EnvExtensionEntry EnvExtensionState) := none
  let mut axExtOpt : Option (PersistentEnvExtension EnvExtensionEntry EnvExtensionEntry EnvExtensionState) := none
  for pExt in (← persistentEnvExtensionsRef.get) do
    let pNameStr := canonicalName pExt.name
    if pNameStr == "_private.Lean.Namespace.0.Lean.namespacesExt" then
      nsExtOpt := some pExt
    else if pNameStr == "_private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt" then
      axExtOpt := some pExt
  let mut privExtCounts : Array String := #[]
  for (extName, arr) in md.entries do
    if arr.size > 0 then
      let extStr := canonicalName extName
      if !isWhitelistedPublicSigExtName extStr then
        hasOpaqueExt := true
      if extStr == "_private.Lean.Structure.0.Lean.structureExt"
        || extStr == "_private.Lean.AuxRecursor.0.Lean.sparseCasesOnExt"
        || extStr == "_private.Lean.OriginalConstKind.0.Lean.privateConstKindsExt"
        || extStr == "_private.Lean.Compiler.LCNF.MonoTypes.0.Lean.Compiler.LCNF.trivialStructureInfoExt"
        || extStr == "_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.impureTypeExt"
        || extStr == "_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.impureTrivialStructureInfoExt"
        || extStr == "_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.ctorLayoutExt" then
        privExtCounts := privExtCounts.push s!"{extStr}:{arr.size}"
      if extStr == "_private.Lean.Namespace.0.Lean.namespacesExt" then
        hasNamespacesExt := true
      else if extStr == "Lean.aliasExtension" || extStr == "_private.Lean.ResolveName.0.Lean.aliasExtension" then
        for (alName, origName) in (Lean.aliasExtension.getModuleEntries env idx) do
          let alCanon := canonicalName (norm alName)
          let origCanon := canonicalName (norm origName)
          let prot := Lean.isProtected env origName
          allExportedAliases := allExportedAliases.push s!"{alCanon}->{origCanon}:p={prot}"
          if !prot then
            let cur := aliasMap[origName]?.getD #[]
            aliasMap := aliasMap.insert origName (cur.push alCanon)
      else if extStr == "_private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt" then
        hasExportedAxiomsExt := true
      else if extStr == "reducibilityExtra" then
        for entry in (Lean.reducibilityExtraExt.ext.getModuleEntries env idx) do
          match entry with
          | .global (dName, st) =>
            reducibilityExtraEntries := reducibilityExtraEntries.push s!"global:{canonicalName (norm dName)}:{formatReducibilityStatus st}"
          | .scoped ns (dName, st) =>
            reducibilityExtraEntries := reducibilityExtraEntries.push s!"scoped:{canonicalName (norm ns)}:{canonicalName (norm dName)}:{formatReducibilityStatus st}"
  let mut nsArr : Array String := #[]
  if hasNamespacesExt then
    match nsExtOpt with
    | some nsExt =>
      let modOnlyEntries := (Array.replicate env.header.moduleData.size #[]).set! idx.toNat (nsExt.getModuleEntries env idx)
      let nsState ← nsExt.addImportedFn modOnlyEntries { env := env, opts := {} }
      let nsEnv := nsExt.setState env nsState
      for nsName in nsEnv.getNamespaces do
        nsArr := nsArr.push (canonicalName (norm nsName))
    | none =>
      hasOpaqueExt := true
  let mut axEnv? : Option Environment := none
  if hasExportedAxiomsExt || isMod then
    match axExtOpt with
    | some axExt =>
      let allAxEntries := (Array.range env.header.moduleData.size).map fun mIdx =>
        axExt.getModuleEntries env mIdx
      let axState ← axExt.addImportedFn allAxEntries { env := env, opts := {} }
      axEnv? := some (axExt.setState env axState)
    | none =>
      hasOpaqueExt := true
  let mut expImports : Array String := #[]
  for imp in md.imports do
    if imp.isExported || !isMod then
      let tag := s!"{canonicalName imp.module}:e={imp.isExported}:m={imp.isMeta}:a={imp.importAll}"
      expImports := expImports.push tag
  let modPkgStr := match env.getModulePackageByIdx? idx with
    | some pkg => pkg
    | none => ""
  let depModStr := match env.getDeprecatedModuleByIdx? idx with
    | some dm => s!"some:{jsonEscape (dm.message?.getD "")}:{jsonEscape (dm.since?.getD "")}"
    | none => "none"
  let simpEntries := (Meta.simpExtension.ext.getModuleEntries env idx).map fun entry =>
    match entry with
    | .global se => formatSimpEntry norm "global" se
    | .scoped ns se => formatSimpEntry norm s!"scoped:{canonicalName (norm ns)}" se
  let csimpEntries := (Compiler.CSimp.ext.ext.getModuleEntries env idx).map fun entry =>
    match entry with
    | .global e => s!"global:{canonicalName (norm e.fromDeclName)}->{canonicalName (norm e.toDeclName)}:{canonicalName (norm e.thmName)}"
    | .scoped ns e => s!"scoped:{canonicalName (norm ns)}:{canonicalName (norm e.fromDeclName)}->{canonicalName (norm e.toDeclName)}:{canonicalName (norm e.thmName)}"
  let instEntries := (Meta.instanceExtension.ext.getModuleEntries env idx).map fun entry =>
    match entry with
    | .global ie => formatInstanceEntry norm "global" ie
    | .scoped ns ie => formatInstanceEntry norm s!"scoped:{canonicalName (norm ns)}" ie
  let defInstEntries := (Meta.defaultInstanceExtension.getModuleEntries env idx).map fun di =>
    s!"{canonicalName (norm di.className)}:{canonicalName (norm di.instanceName)}:{di.priority}"
  let clsEntries := (Lean.classExtension.getModuleEntries env idx).map fun ce =>
    let op := String.intercalate "," (ce.outParams.toList.map toString)
    let olp := String.intercalate "," (ce.outLevelParams.toList.map toString)
    s!"{canonicalName (norm ce.name)}:out=[{op}]:outLvl=[{olp}]"
  let extThmEntries := (Meta.Ext.extExtension.ext.getModuleEntries env idx).map fun entry =>
    match entry with
    | .global et =>
      let ks := String.intercalate "," (et.keys.toList.map (formatDiscrKey norm))
      s!"global:{canonicalName (norm et.declName)}:p={et.priority}:keys=[{ks}]"
    | .scoped ns et =>
      let ks := String.intercalate "," (et.keys.toList.map (formatDiscrKey norm))
      s!"scoped:{canonicalName (norm ns)}:{canonicalName (norm et.declName)}:p={et.priority}:keys=[{ks}]"
  let coeEntries := (Meta.coeExt.ext.getModuleEntries env idx).map fun entry =>
    match entry with
    | .global (fn, ci) => s!"global:{canonicalName (norm fn)}:{ci.numArgs}:{ci.coercee}:{formatCoeFnType ci.type}"
    | .scoped ns (fn, ci) => s!"scoped:{canonicalName (norm ns)}:{canonicalName (norm fn)}:{ci.numArgs}:{ci.coercee}:{formatCoeFnType ci.type}"
  let grindEntries := (Meta.Grind.grindExt.ext.getModuleEntries env idx).map fun entry =>
    match entry with
    | .global ge => formatGrindEntry norm "global" ge
    | .scoped ns ge => formatGrindEntry norm s!"scoped:{canonicalName (norm ns)}" ge
  let irDeclEntries := (IR.declMapExt.getModuleEntries env idx).map fun d =>
    let irHash := TurboLean.Blake3.blake3Bytes (toString d).toUTF8
    s!"{canonicalName (norm d.name)}:{irHash}"
  let mut lcnfBaseEntries : Array String := #[]
  for bd in Compiler.LCNF.baseExt.getModuleEntries env idx do
    lcnfBaseEntries := lcnfBaseEntries.push (← formatLcnfDeclIO env norm .base bd)
  let mut lcnfMonoEntries : Array String := #[]
  for mdDecl in Compiler.LCNF.monoExt.getModuleEntries env idx do
    lcnfMonoEntries := lcnfMonoEntries.push (← formatLcnfDeclIO env norm .mono mdDecl)
  let lcnfImpureSigEntries := ((Compiler.LCNF.impureSigExt.getModuleEntries env idx).map (formatLcnfSignature norm)).qsort (· < ·)
  let lcnfMonoTypeEntries := ((monoTypeModuleEntries env idx).map fun (dName, mTy) =>
    let mTyHash := TurboLean.Blake3.blake3Bytes (TurboLean.StatementHash.exprJson norm mTy).compress.toUTF8
    s!"{canonicalName (norm dName)}:{mTyHash}").qsort (· < ·)
  let matchPatEntries := ((Lean.matchPatternAttr.ext.getModuleEntries env idx).map (fun dName => canonicalName (norm dName))).qsort (· < ·)
  let defeqEntries := ((Lean.defeqAttr.ext.getModuleEntries env idx).map (fun dName => canonicalName (norm dName))).qsort (· < ·)
  let bwdDefeqEntries := ((Lean.backwardDefeqAttr.ext.getModuleEntries env idx).map (fun dName => canonicalName (norm dName))).qsort (· < ·)
  let inlineEntries := ((Compiler.inlineAttrs.ext.getModuleEntries env idx).map fun (dName, ik) =>
    s!"{canonicalName (norm dName)}:{formatInlineAttr (some ik)}").qsort (· < ·)
  let externEntries := ((Lean.externAttr.ext.getModuleEntries env idx).map fun (dName, ed) =>
    s!"{canonicalName (norm dName)}:[{String.intercalate "," (ed.entries.map formatExternEntry)}]").qsort (· < ·)
  let implByEntries := ((Compiler.implementedByAttr.ext.getModuleEntries env idx).map fun (dName, tgt) =>
    s!"{canonicalName (norm dName)}->{canonicalName (norm tgt)}").qsort (· < ·)
  let exportEntries := ((Lean.exportAttr.ext.getModuleEntries env idx).map fun (dName, expNm) =>
    s!"{canonicalName (norm dName)}->{canonicalName expNm}").qsort (· < ·)
  let specEntries := ((Compiler.specializeAttr.ext.getModuleEntries env idx).map fun (dName, args) =>
    s!"{canonicalName (norm dName)}:[{String.intercalate "," (args.toList.map toString)}]").qsort (· < ·)
  let nospecEntries := ((Compiler.nospecializeAttr.ext.getModuleEntries env idx).map (fun dName => canonicalName (norm dName))).qsort (· < ·)
  let weakSpecEntries := ((Compiler.weakSpecializeAttr.ext.getModuleEntries env idx).map (fun dName => canonicalName (norm dName))).qsort (· < ·)
  let deprEntries := ((Linter.deprecatedAttr.ext.getModuleEntries env idx).map fun (dName, de) =>
    let nn := match de.newName? with | some x => canonicalName (norm x) | none => ""
    s!"{canonicalName (norm dName)}:{nn}:{jsonEscape (de.text?.getD "")}:{jsonEscape (de.since?.getD "")}").qsort (· < ·)
  let elabElimEntries := ((Elab.Term.elabAsElim.ext.getModuleEntries env idx).map (fun dName => canonicalName (norm dName))).qsort (· < ·)
  let compBlEntries := ((PersistentEnvExtension.getModuleEntries Meta.completionBlackListExt env idx).map (fun dName => canonicalName (norm dName))).qsort (· < ·)
  let protEntries := ((PersistentEnvExtension.getModuleEntries Lean.protectedExt env idx).map (fun dName => canonicalName (norm dName))).qsort (· < ·)
  let noConfEntries := ((Lean.noConfusionExt.getModuleEntries env idx).map fun (dName, nci) =>
    s!"{canonicalName (norm dName)}:{formatNoConfusionInfo nci}").qsort (· < ·)
  let auxRecEntries := ((PersistentEnvExtension.getModuleEntries Lean.auxRecExt env idx).map (fun dName => canonicalName (norm dName))).qsort (· < ·)
  let recExtEntries := ((PersistentEnvExtension.getModuleEntries Meta.recExt env idx).map (fun dName => canonicalName (norm dName))).qsort (· < ·)
  let redCoreEntries := ((Lean.reducibilityCoreExt.getModuleEntries env idx).map fun (dName, st) =>
    s!"{canonicalName (norm dName)}:{formatReducibilityStatus st}").qsort (· < ·)
  let noncompEntries := ((PersistentEnvExtension.getModuleEntries Lean.noncomputableExt env idx).map (fun dName => canonicalName (norm dName))).qsort (· < ·)
  let projFnEntries := ((Lean.projectionFnInfoExt.getModuleEntries env idx).map fun (dName, pi) =>
    s!"{canonicalName (norm dName)}:{canonicalName (norm pi.ctorName)}:{pi.numParams}:{pi.i}:{pi.fromClass}").qsort (· < ·)
  reducibilityExtraEntries := reducibilityExtraEntries.qsort (· < ·)
  privExtCounts := privExtCounts.qsort (· < ·)
  let mut matchedStructureCount : Nat := 0
  let mut matchedSparseCasesCount : Nat := 0
  let mut matchedPrivConstKindCount : Nat := 0
  for c in md.constants do
    if (Lean.getStructureInfo? env c.name).isSome then
      matchedStructureCount := matchedStructureCount + 1
    if Lean.isSparseCasesOn env c.name then
      matchedSparseCasesCount := matchedSparseCasesCount + 1
    if (Lean.getOriginalConstKind? env c.name).isSome then
      matchedPrivConstKindCount := matchedPrivConstKindCount + 1
  for (extName, arr) in md.entries do
    if arr.size > 0 then
      let extStr := canonicalName extName
      if extStr == "_private.Lean.Structure.0.Lean.structureExt" && arr.size != matchedStructureCount then
        hasOpaqueExt := true
      else if extStr == "_private.Lean.AuxRecursor.0.Lean.sparseCasesOnExt" && arr.size != matchedSparseCasesCount then
        hasOpaqueExt := true
      else if extStr == "_private.Lean.OriginalConstKind.0.Lean.privateConstKindsExt" && arr.size > matchedPrivConstKindCount then
        hasOpaqueExt := true
  nsArr := nsArr.qsort (· < ·)
  allExportedAliases := allExportedAliases.qsort (· < ·)
  let mut declJsons : Array String := #[]
  let coreCtxPub : Core.Context := { fileName := "<pubsig>", fileMap := FileMap.ofString "" }
  let coreStatePub : Core.State := { env := env }
  let mut sigPieces : Array String := #[
    s!"olean-pubsig:v2|mod={canonicalName nm}|is_module={isMod}|pkg={modPkgStr}|dep_mod={depModStr}",
    s!"imports={String.intercalate ";" expImports.toList}",
    s!"namespaces={String.intercalate ";" nsArr.toList}",
    s!"aliases={String.intercalate ";" allExportedAliases.toList}",
    s!"reducibility_core={String.intercalate ";" redCoreEntries.toList}",
    s!"reducibility_extra={String.intercalate ";" reducibilityExtraEntries.toList}",
    s!"simp={String.intercalate ";" simpEntries.toList}",
    s!"csimp={String.intercalate ";" csimpEntries.toList}",
    s!"instances={String.intercalate ";" instEntries.toList}",
    s!"default_instances={String.intercalate ";" defInstEntries.toList}",
    s!"classes={String.intercalate ";" clsEntries.toList}",
    s!"ext_thms={String.intercalate ";" extThmEntries.toList}",
    s!"coes={String.intercalate ";" coeEntries.toList}",
    s!"grind={String.intercalate ";" grindEntries.toList}",
    s!"match_pattern={String.intercalate ";" matchPatEntries.toList}",
    s!"defeq={String.intercalate ";" defeqEntries.toList}",
    s!"bwd_defeq={String.intercalate ";" bwdDefeqEntries.toList}",
    s!"inline_attrs={String.intercalate ";" inlineEntries.toList}",
    s!"extern_attrs={String.intercalate ";" externEntries.toList}",
    s!"implemented_by={String.intercalate ";" implByEntries.toList}",
    s!"export_attrs={String.intercalate ";" exportEntries.toList}",
    s!"specialize={String.intercalate ";" specEntries.toList}",
    s!"nospecialize={String.intercalate ";" nospecEntries.toList}",
    s!"weak_specialize={String.intercalate ";" weakSpecEntries.toList}",
    s!"deprecated={String.intercalate ";" deprEntries.toList}",
    s!"elab_as_elim={String.intercalate ";" elabElimEntries.toList}",
    s!"completion_blacklist={String.intercalate ";" compBlEntries.toList}",
    s!"protected={String.intercalate ";" protEntries.toList}",
    s!"no_confusion={String.intercalate ";" noConfEntries.toList}",
    s!"aux_rec={String.intercalate ";" auxRecEntries.toList}",
    s!"rec_ext={String.intercalate ";" recExtEntries.toList}",
    s!"noncomputable={String.intercalate ";" noncompEntries.toList}",
    s!"proj_fns={String.intercalate ";" projFnEntries.toList}",
    s!"ir_decls={String.intercalate ";" irDeclEntries.toList}",
    s!"lcnf_base={String.intercalate ";" lcnfBaseEntries.toList}",
    s!"lcnf_mono={String.intercalate ";" lcnfMonoEntries.toList}",
    s!"lcnf_impure_sig={String.intercalate ";" lcnfImpureSigEntries.toList}",
    s!"lcnf_mono_type={String.intercalate ";" lcnfMonoTypeEntries.toList}",
    s!"priv_ext_counts={String.intercalate ";" privExtCounts.toList}"
  ]
  for c in md.constants do
    let cname := canonicalName c.name
    let (kind, stmtHash, bodyHash) := formatConstantExportPayload c (some nm)
    let red := formatReducibilityStatus (Lean.getReducibilityStatusCore env c.name)
    let inl := formatInlineAttr (Compiler.getInlineAttribute? env c.name)
    let extDataStr := match Lean.getExternAttrData? env c.name with
      | some ed => String.intercalate "," (ed.entries.map formatExternEntry)
      | none => ""
    let expNameStr := match Lean.getExportNameFor? env c.name with
      | some en => canonicalName en
      | none => ""
    let implBy := match Compiler.getImplementedBy? env c.name with
      | some tgt => canonicalName (norm tgt)
      | none => ""
    let specFlags := s!"{Compiler.hasSpecializeAttribute env c.name}:{Compiler.hasNospecializeAttribute env c.name}"
    let protFlag := Lean.isProtected env c.name
    let noConfFlag := Lean.isNoConfusion env c.name
    let auxRecFlag := Lean.isAuxRecursor env c.name
    let sparseCasesFlag := Lean.isSparseCasesOn env c.name
    let recCoreFlag := Lean.isRecCore env c.name
    let noncompFlag := Lean.isNoncomputable env c.name
    let matchPatFlag := Lean.hasMatchPatternAttribute env c.name
    let elabElimFlag := Elab.Term.elabAsElim.hasTag env c.name
    let defeqFlag := Lean.defeqAttr.hasTag env c.name
    let bwdDefeqFlag := Lean.backwardDefeqAttr.hasTag env c.name
    let compBlFlag := Meta.completionBlackListExt.isTagged env c.name
    let origKindStr := match Lean.getOriginalConstKind? env c.name with
      | some ck => formatConstKind ck
      | none => ""
    let projStr := match env.getProjectionFnInfo? c.name with
      | some pi => s!"{canonicalName (norm pi.ctorName)}:{pi.numParams}:{pi.i}:{pi.fromClass}"
      | none => ""
    let structStr := match Lean.getStructureInfo? env c.name with
      | some si =>
        let fnames := String.intercalate "," (si.fieldNames.toList.map canonicalName)
        let finfos := String.intercalate "," (si.fieldInfo.toList.map fun (fi : StructureFieldInfo) =>
          let sub := match fi.subobject? with | some sn => canonicalName (norm sn) | none => ""
          let ap := match fi.autoParam? with
            | some e => TurboLean.Blake3.blake3Bytes (TurboLean.StatementHash.exprJson norm e).compress.toUTF8
            | none => ""
          s!"{canonicalName fi.fieldName}:{canonicalName (norm fi.projFn)}:{sub}:{reprStr fi.binderInfo}:{ap}")
        let pinfos := String.intercalate "," (si.parentInfo.toList.map fun (pi : StructureParentInfo) =>
          s!"{canonicalName (norm pi.structName)}:{pi.subobject}:{canonicalName (norm pi.projFn)}")
        s!"fn=[{fnames}]:fi=[{finfos}]:pi=[{pinfos}]"
      | none => ""
    let deprStr := match Linter.deprecatedAttr.getParam? env c.name with
      | some de =>
        let nn := match de.newName? with | some x => canonicalName (norm x) | none => ""
        s!"some:{nn}:{jsonEscape (de.text?.getD "")}:{jsonEscape (de.since?.getD "")}"
      | none => ""
    let mut lcnfTypeInfoStr := ""
    match c with
    | .inductInfo _ =>
      let (trivMono, _) ← (Compiler.LCNF.hasTrivialStructure? c.name).toIO coreCtxPub coreStatePub
      let (trivImp, _) ← (Compiler.LCNF.hasTrivialImpureStructure? c.name).toIO coreCtxPub coreStatePub
      let impTyStr ← try
          let (impTy, _) ← (Compiler.LCNF.nameToImpureType c.name).toIO coreCtxPub coreStatePub
          pure (TurboLean.Blake3.blake3Bytes (TurboLean.StatementHash.exprJson norm impTy).compress.toUTF8)
        catch _ =>
          pure "uncompiled"
      lcnfTypeInfoStr := s!"ind:{formatTrivialStructOpt norm trivMono}:{formatTrivialStructOpt norm trivImp}:{impTyStr}"
    | .ctorInfo _ =>
      let ctorLayStr ← try
          let (cl, _) ← (Compiler.LCNF.getCtorLayout c.name).toIO coreCtxPub coreStatePub
          let fStr := String.intercalate "," (cl.fieldInfo.toList.map (formatCtorFieldInfo norm))
          pure s!"{canonicalName (norm cl.ctorInfo.name)}:{cl.ctorInfo.cidx}:{cl.ctorInfo.size}:{cl.ctorInfo.usize}:{cl.ctorInfo.ssize}:[{fStr}]"
        catch _ =>
          pure "uncompiled"
      lcnfTypeInfoStr := s!"ctor:{ctorLayStr}"
    | _ => pure ()
    let aliases := ((aliasMap[c.name]?.getD #[]).qsort (· < ·)).toList
    let aliasStr := String.intercalate "," aliases
    let axs : Array Name := match axEnv? with
      | some aenv =>
        Id.run ((Lean.collectAxioms c.name : ReaderT Environment Id (Array Name)).run aenv)
      | none =>
        collectDeclAxioms {} env c.name
    let mut allAxioms : Array String := #[]
    for ax in axs do
      allAxioms := allAxioms.push (canonicalName (norm ax))
      if !isAllowedStandardAxiom ax then
        hasOpaqueExt := true
    let allAxStr := String.intercalate "," (allAxioms.qsort (· < ·)).toList
    sigPieces := sigPieces.push s!"c:{cname}|{kind}|{stmtHash}|{bodyHash}|red={red}|inl={inl}|ext=[{extDataStr}]|exp={expNameStr}|impl={implBy}|spec={specFlags}|flags={protFlag},{noConfFlag},{auxRecFlag},{sparseCasesFlag},{recCoreFlag},{noncompFlag},{matchPatFlag},{elabElimFlag},{defeqFlag},{bwdDefeqFlag},{compBlFlag}|orig={origKindStr}|proj={projStr}|struct={structStr}|depr={deprStr}|lcnfty={lcnfTypeInfoStr}|alias=[{aliasStr}]|axioms=[{allAxStr}]"
    declJsons := declJsons.push s!"\{\"name\":\"{jsonEscape cname}\",\"kind\":\"{jsonEscape kind}\",\"type_hash\":\"{jsonEscape stmtHash}\",\"body_hash\":\"{jsonEscape bodyHash}\",\"reducibility\":\"{jsonEscape red}\",\"inline\":\"{jsonEscape inl}\"}"
  let pubDigest := TurboLean.Blake3.blake3Bytes (String.intercalate "\n" sigPieces.toList).toUTF8
  return s!"\{\"ok\":true,\"module\":\"{jsonEscape (canonicalName nm)}\",\"is_module\":{isMod},\"has_opaque_ext\":{hasOpaqueExt},\"public_sig_digest\":\"{pubDigest}\",\"exported_imports\":[{jsonStrList expImports.toList}],\"simp_entries\":[{jsonStrList simpEntries.toList}],\"csimp_entries\":[{jsonStrList csimpEntries.toList}],\"instance_entries\":[{jsonStrList instEntries.toList}],\"decls\":[{String.intercalate "," declJsons.toList}]}"

end TurboLean.ZygoteWorker
