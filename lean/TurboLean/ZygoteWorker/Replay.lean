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

open Lean Elab

namespace TurboLean.ZygoteWorker

/-- Count unique `Expr` DAG nodes (deduplicated by `Expr.hash`) up to `maxNodes` in `O(|DAG|)` time. -/
def countExprDagNodes (root : Expr) (maxNodes : Nat := 100000) : Nat := Id.run do
  let mut stack : Array Expr := #[root]
  let mut seen : Std.HashMap UInt64 Bool := {}
  let mut count : Nat := 0
  while !stack.isEmpty && count < maxNodes do
    let e := stack.back!
    stack := stack.pop
    let h := e.hash
    if seen[h]?.getD false then
      continue
    seen := seen.insert h true
    count := count + 1
    match e with
    | .app f a =>
      stack := stack.push f
      stack := stack.push a
    | .lam _ d b _ =>
      stack := stack.push d
      stack := stack.push b
    | .forallE _ d b _ =>
      stack := stack.push d
      stack := stack.push b
    | .letE _ t v b _ =>
      stack := stack.push t
      stack := stack.push v
      stack := stack.push b
    | .mdata _ b =>
      stack := stack.push b
    | .proj _ _ b =>
      stack := stack.push b
    | _ => pure ()
  return count

/-- Strip leading universal/arrow binders (`forallE`) to expose the conclusion `Expr`. -/
partial def stripForallConcl (e : Expr) : Expr :=
  match e with
  | .forallE _ _ body _ => stripForallConcl body
  | .mdata _ b => stripForallConcl b
  | _ => e

/-- Extract the head symbol of the conclusion of the first newly added theorem/definition. -/
def extractNewDeclGoalHead (beforeEnv afterEnv : Environment) : String := Id.run do
  let beforeMap := beforeEnv.constants.map₂
  let afterMap := afterEnv.constants.map₂
  for (_, cinfo) in afterMap.toList do
    if !beforeMap.contains cinfo.name then
      let concl := stripForallConcl cinfo.type
      match concl.getAppFn with
      | .const nm _ => return nm.toString
      | .sort _ => return "Sort"
      | .forallE .. => return "Forall"
      | _ => return "Expr"
  return "None"

/-- Count total unique kernel `Expr` DAG nodes across newly added `.thmInfo` and `.defnInfo` declarations. -/
def countNewDeclExprNodes (beforeEnv afterEnv : Environment) : Nat := Id.run do
  let beforeMap := beforeEnv.constants.map₂
  let afterMap := afterEnv.constants.map₂
  let newDecls := afterMap.foldl (fun acc name cinfo =>
    if !beforeMap.contains name then (name, cinfo) :: acc else acc) []
  let mut total : Nat := 0
  for (_, cinfo) in newDecls do
    match cinfo with
    | .thmInfo v =>
      total := total + countExprDagNodes v.type + countExprDagNodes v.value
    | .defnInfo v =>
      total := total + countExprDagNodes v.type + countExprDagNodes v.value
    | _ => pure ()
  return total

/-- Collect up to 32 distinct non-internal constant names directly referenced in the kernel proof/value
    terms (`v.value.getUsedConstants`) of newly added `.thmInfo` and `.defnInfo` declarations. -/
def collectNewDeclUsedConstants (beforeEnv afterEnv : Environment) : Array String := Id.run do
  let sorryAxName := Name.mkSimple ("sor" ++ "ryAx")
  let beforeMap := beforeEnv.constants.map₂
  let afterMap := afterEnv.constants.map₂
  let newDecls := afterMap.foldl (fun acc name cinfo =>
    if !beforeMap.contains name then (name, cinfo) :: acc else acc) []
  let mut seen : Std.HashMap String Bool := {}
  let mut out : Array String := #[]
  for (declName, cinfo) in newDecls.reverse do
    let usedConsts : Array Name := match cinfo with
      | .thmInfo v => v.value.getUsedConstants
      | .defnInfo v => v.value.getUsedConstants
      | _ => #[]
    for c in usedConsts do
      if out.size >= 32 then
        break
      if isAllowedStandardAxiom c || c == sorryAxName || c == declName then
        continue
      let cs := c.toString
      if (cs.splitOn "._").length > 1 || (cs.splitOn "_proof_").length > 1 || (cs.splitOn "match_").length > 1 then
        continue
      if !(seen[cs]?.getD false) then
        seen := seen.insert cs true
        out := out.push cs
  return out

def eqConstantInfo (a b : ConstantInfo) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && a.type == b.type &&
  match a, b with
  | .axiomInfo a, .axiomInfo b => a.isUnsafe == b.isUnsafe
  | .defnInfo a, .defnInfo b =>
    a.value == b.value && a.safety == b.safety && a.all == b.all &&
      (match a.hints, b.hints with
       | .opaque, .opaque | .abbrev, .abbrev => true
       | .regular a, .regular b => a == b
       | _, _ => false)
  | .thmInfo a, .thmInfo b => a.value == b.value && a.all == b.all
  | .opaqueInfo a, .opaqueInfo b =>
    a.value == b.value && a.isUnsafe == b.isUnsafe && a.all == b.all
  | .quotInfo a, .quotInfo b =>
    match a.kind, b.kind with
    | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
    | _, _ => false
  | .inductInfo a, .inductInfo b =>
    a.numParams == b.numParams && a.numIndices == b.numIndices && a.all == b.all &&
    a.ctors == b.ctors && a.numNested == b.numNested && a.isRec == b.isRec &&
    a.isUnsafe == b.isUnsafe && a.isReflexive == b.isReflexive
  | .ctorInfo a, .ctorInfo b =>
    a.induct == b.induct && a.cidx == b.cidx && a.numParams == b.numParams &&
    a.numFields == b.numFields && a.isUnsafe == b.isUnsafe
  | .recInfo a, .recInfo b =>
    a.all == b.all && a.numParams == b.numParams && a.numIndices == b.numIndices &&
    a.numMotives == b.numMotives && a.numMinors == b.numMinors && a.k == b.k &&
    a.isUnsafe == b.isUnsafe && a.rules.length == b.rules.length &&
    (a.rules.zip b.rules).all fun (a, b) => a.ctor == b.ctor && a.nfields == b.nfields && a.rhs == b.rhs
  | _, _ => false
/-- Independent kernel replay. `IO.processCommands` honors source-level options such as
    `set_option debug.skipKernelTC true` (or `set_option … in`), and these options persist in cached
    prefix `Command.State`s. So every declaration added since `beforeEnv` is sent to the kernel again,
    starting from `beforeEnv`'s kernel environment with checking forced on and ignoring all elaboration
    options (`Lean.Environment.replay` replays against `toKernelEnv` via `addDeclCore` directly). Inductive types are re-added
    and their constructors and recursors must match the regenerated ones exactly. The replay skips
    non-safe declarations (`auditNewKernelDecls` rejects them) and `partial` ones (the kernel never
    lets a safe declaration refer to them). Changing a constant that existed before the request also
    fails the check. Returns the errors; an empty list means the replay succeeded. -/
def kernelReplayNewDecls (beforeEnv afterEnv : Environment) : IO (List String) := do
  let beforeMap := beforeEnv.constants.map₂
  let afterMap := afterEnv.constants.map₂
  let mut errs : List String := []
  for (name, oldInfo) in beforeMap.toList do
    match afterMap.find? name with
    | some newInfo =>
      if !eqConstantInfo newInfo oldInfo then
        errs := errs ++ [s!"[TurboLean.KernelReplay] declaration `{name}` from the checked prefix was replaced"]
    | none =>
      errs := errs ++ [s!"[TurboLean.KernelReplay] declaration `{name}` from the checked prefix is missing"]
  let newConsts : Std.HashMap Name ConstantInfo := afterMap.foldl (fun acc name cinfo =>
    if beforeMap.contains name then acc else acc.insert name cinfo) {}
  for (name, _) in newConsts.toList do
    if beforeEnv.contains name then
      errs := errs ++ [s!"[TurboLean.KernelReplay] declaration `{name}` redeclares an imported constant"]
  if !errs.isEmpty || newConsts.isEmpty then
    return errs
  try
    let _ ← replayKernelConstants newConsts beforeEnv
    return []
  catch e =>
    return [s!"[TurboLean.KernelReplay] independent kernel re-check failed: {e}"]



/-- Collect `(declName, kernelStatementHash)` for newly added `.thmInfo` declarations between
    `beforeEnv` and `afterEnv`, keyed by user-facing name (and raw kernel name if private, plus
    any mapped `fastMap` original name).
    When `includeStubs` is `false`, explicit prefix/coalesced stubs (`isExplicitSorryStub`)
    are excluded so only verified theorems are attested. -/
def collectNewTheoremTypeHashes
    (beforeEnv afterEnv : Environment)
    (includeStubs : Bool := true)
    (fastMap : List (String × String) := []) : List (String × String) := Id.run do
  let beforeMap := beforeEnv.constants.map₂
  let afterMap := afterEnv.constants.map₂
  let newDecls := afterMap.foldl (fun acc name cinfo =>
    if !beforeMap.contains name then (name, cinfo) :: acc else acc) []
  let localMod? : Option Name := if afterEnv.mainModule.isAnonymous then none else some afterEnv.mainModule
  let mappedGenToOrig : Std.HashMap Name Name :=
    (parseFastVerifyMapEntries fastMap |>.getD []).foldl (fun acc (origN, genN) => acc.insert genN origN) {}
  let mut seen : Std.HashMap String Bool := {}
  let mut out : List (String × String) := []
  for (_, cinfo) in newDecls.reverse do
    if (cinfo matches .thmInfo _) && (includeStubs || !isExplicitSorryStub cinfo) then
      let h := kernelStatementHash cinfo localMod?
      let userNm := canonicalName (Lean.privateToUserName cinfo.name)
      if !(seen[userNm]?.getD false) then
        seen := seen.insert userNm true
        out := out ++ [(userNm, h)]
      let rawNm := canonicalName cinfo.name
      if rawNm != userNm && !(seen[rawNm]?.getD false) then
        seen := seen.insert rawNm true
        out := out ++ [(rawNm, h)]
      if let some origName := mappedGenToOrig[cinfo.name]? then
        let origNm := canonicalName origName
        if !(seen[origNm]?.getD false) then
          seen := seen.insert origNm true
          out := out ++ [(origNm, h)]
  return out

/-- Elaborate and kernel-typecheck `code` starting from an immutable `baseState : Command.State`
    without mutating `baseState`. With `allowStub`, host-listed `sorry` stubs are exempt from the `sorryAx`
    gate (in a `finalRun`, only the kernel names `stubExemptSet` resolves the host `stubs` to, never a
    `stubTargets` declaration, and never when a stub name is ambiguous), and a `finalRun` also rejects a
    checkpoint stub it does not exempt (`unexemptPrefixStub`).
    Returns `(ok, elapsed_us, heartbeats, proof_term_nodes, error_messages, all_messages, captured_stdout, used_constants, decl_types, sorry_decls, next_clean_state)`. -/
def runCommandsFromState
    (baseState : Command.State)
    (code : String)
    (fileName : String := "<zygote-shard>")
    (allowStub : Bool := false)
    (evalMode : Bool := false)
    (stubTargets : List String := [])
    (stubs : List String := [])
    (finalRun : Bool := true)
    (strictPrefix : Bool := false)
    (requiredTargets : Option (List String) := none)
    (fastMap : List (String × String) := [])
    (includeStubsInDeclTypes : Bool := false)
    (allowSorry : Bool := false) : IO (Bool × Nat × Nat × Nat × List String × List String × String × List String × List (String × String) × List String × Command.State) := do
  let t0 ← IO.monoNanosNow
  let hb0 ← IO.getNumHeartbeats
  -- `warningAsError` is never rewritten: a stubbed prefix only drops its stub diagnostics (below),
  -- so the checkpoint keeps the file's and the command line's warning policy for the target.
  let inputCtx := Parser.mkInputContext code fileName
  let initState : Command.State := { baseState with messages := {} }
  let (capturedStdout, s) ← IO.FS.withIsolatedStreams (IO.processCommands inputCtx {} initState) (isolateStderr := false)
  let hb1 ← IO.getNumHeartbeats
  let heartbeats := hb1 - hb0
  let forbiddenToken := "sor" ++ "ry"
  let sorryWarnPhrase := "declaration uses '" ++ forbiddenToken ++ "'"
  let sorryWarnBacktick := "declaration uses `" ++ forbiddenToken ++ "`"
  let mut errs : List String := []
  let mut allMessages : List String := []
  for msg in s.commandState.messages.toList do
    let txt ← msg.data.toString
    let isSorryDiag := (txt.splitOn sorryWarnPhrase).length > 1 || (txt.splitOn sorryWarnBacktick).length > 1
    let sevStr := match msg.severity with
      | .error => "error"
      | .warning => "warning"
      | .information => "info"
    -- Eval mode is a drop-in for `lean <file>`: print each message with Lean's own
    -- `Message.toString`, as the command line does (error-kind tag such as
    -- `error(lean.unknownIdentifier):`, caption, no position prefix for `info`,
    -- trailing newline), so the bytes match `lean <file>` verbatim.
    let formatted ← if evalMode then msg.toString
      else pure s!"{msg.fileName}:{msg.pos.line}:{msg.pos.column}: {sevStr}: {txt.trimAsciiEnd.toString}"
    allMessages := allMessages ++ [formatted]
    if msg.severity == .error then
      if !((allowStub || allowSorry) && !evalMode && isSorryDiag) then
        errs := errs ++ [formatted]
    else if !evalMode && !allowStub && !allowSorry && msg.severity == .warning && isSorryDiag then
      errs := errs ++ [s!"forbidden token detected: {txt}"]
  let mut usedConstants : List String := []
  let mut proofTermNodes : Nat := 0
  let mut declTypes : List (String × String) := []
  let mut sorryDecls : List String := []
  if allMessages.any isRuntimePanicText then
    errs := errs ++ [runtimePanicErr]
  -- Primary gate: re-check every new declaration in the kernel, independently of the options the
  -- elaborator ran under. Checkpoints are only cached after this passes, so prefix declarations are
  -- covered by induction (each prefix/delta replay starts from an already replayed environment).
  errs := errs ++ (← kernelReplayNewDecls baseState.env s.commandState.env)
  if !evalMode then
    let (exempt, stubViolations) :=
      if allowStub && finalRun then stubExemptSet s.commandState.env stubs stubTargets fastMap else ({}, [])
    let stubExempt := fun (n : Name) =>
      allowStub && (if finalRun then
        if includeStubsInDeclTypes then (s.commandState.env.find? n).any isExplicitSorryStub else exempt.contains n
      else (s.commandState.env.find? n).any isExplicitSorryStub)
    let (_, kernelErrs, newSorryDecls) ← auditNewKernelDecls baseState.env s.commandState.env stubExempt allowSorry
    errs := errs ++ kernelErrs
    sorryDecls := newSorryDecls
    if finalRun && allowStub && !includeStubsInDeclTypes && !stubViolations.isEmpty then
      errs := errs ++ stubViolations
    if finalRun && !includeStubsInDeclTypes then
      let allNewNames := s.commandState.env.constants.map₂.foldl (fun acc name _ => acc.push name) #[]
      let isImportedOrig := fun (origName : Name) =>
        !s.commandState.env.constants.map₂.contains origName && (s.commandState.env.find? origName).isSome
      let fastViolations :=
        validateFastVerifyKernelMap s.commandState.env allNewNames isImportedOrig exempt.contains fastMap
      errs := errs ++ fastViolations
    if finalRun && !includeStubsInDeclTypes && !allowSorry && (allowStub || strictPrefix) &&
        unexemptPrefixStub baseState.env (if allowStub then stubs else []) stubTargets fastMap then
      errs := errs ++ ["[TurboLean.KernelGate] stubbed prefix holds a `sorry` theorem this check does not exempt"]
    else if finalRun && !includeStubsInDeclTypes && allowSorry then
      let sorryAxName := Name.mkSimple ("sor" ++ "ryAx")
      let (prefExempt, prefViol) := stubExemptSet baseState.env (if allowStub then stubs else []) stubTargets fastMap
      if allowStub && !prefViol.isEmpty then
        errs := errs ++ prefViol
      else
        for (pName, _) in baseState.env.constants.map₂.toList do
          if !prefExempt.contains pName &&
              (collectDeclAxioms {} baseState.env pName prefExempt.contains).contains sorryAxName then
            let userNm := canonicalName (Lean.privateToUserName pName)
            if !userNm.isEmpty && !((userNm.splitOn "._").length > 1) && !((userNm.splitOn "_proof_").length > 1) && !sorryDecls.contains userNm then
              sorryDecls := sorryDecls ++ [userNm]
    -- An elaborator could drop a checked declaration, leaving nothing for the gate to audit.
    let noNewDecls := s.commandState.env.constants.map₂.foldl
      (fun empty name _ => empty && baseState.env.constants.map₂.contains name) true
    let reqTargets := requiredTargets.getD stubTargets
    if finalRun && !includeStubsInDeclTypes &&
        ((!reqTargets.isEmpty && !reqTargets.all (declaresHostName s.commandState.env fastMap)) ||
          (reqTargets.isEmpty && !stubTargets.isEmpty && noNewDecls)) then
      errs := errs ++ ["[TurboLean.KernelGate] a checked declaration is missing from the elaborated environment"]
    usedConstants := (collectNewDeclUsedConstants baseState.env s.commandState.env).toList
    proofTermNodes := countNewDeclExprNodes baseState.env s.commandState.env
    declTypes := collectNewTheoremTypeHashes baseState.env s.commandState.env (includeStubsInDeclTypes || allowSorry) fastMap
  let t1 ← IO.monoNanosNow
  let elapsedUs := (t1 - t0) / 1000
  let cleanNextState : Command.State := { s.commandState with messages := {} }
  return (errs.isEmpty, elapsedUs, heartbeats, proofTermNodes, errs, allMessages, capturedStdout, usedConstants, declTypes, sorryDecls, cleanNextState)

/-- Atomically serialize `finalEnv` (and any module-system companions `.olean.server`, `.olean.private`, `.ir`, `.ir.sig`)
    to `oleanPath` after verifying `mainModule == modName`, kernel-replaying all declarations added since `baseEnv`,
    and auditing for zero forbidden axioms (`reduceBool`, `trustCompiler`, plus `sorryAx` unless `allowOutlineStubs = true`,
    in which case ONLY validated explicit prefix stubs passing `isExplicitSorryStub` may reference `sorryAx`). -/
def writeAuditedModuleOlean
    (baseEnv finalEnv : Environment)
    (modName : Name)
    (oleanPath : System.FilePath)
    (allowOutlineStubs : Bool := false) : IO Bool := do
  if modName.isAnonymous || finalEnv.mainModule != modName then
    return false
  if !(← kernelReplayNewDecls baseEnv finalEnv).isEmpty then
    return false
  let stubExempt := fun (n : Name) =>
    allowOutlineStubs && (finalEnv.find? n).any isExplicitSorryStub
  let (clean, kErrs, _) ← auditNewKernelDecls baseEnv finalEnv stubExempt false
  if !clean || !kErrs.isEmpty then
    return false
  if let some parent := oleanPath.parent then
    IO.FS.createDirAll parent
  let pid ← IO.Process.getPID
  let ts ← IO.monoNanosNow
  let tmpBase := oleanPath.withExtension s!"zygote_tmp_{pid}_{ts}.olean"
  let cleanupTmp : IO Unit := do
    for p in [
      tmpBase,
      System.FilePath.mk s!"{tmpBase}.server",
      System.FilePath.mk s!"{tmpBase}.private",
      tmpBase.withExtension "ir",
      tmpBase.withExtension "ir.sig"
    ] do
      try IO.FS.removeFile p catch _ => pure ()
  try
    Lean.writeModule finalEnv tmpBase
    if finalEnv.header.isModule then
      let pairs : List (System.FilePath × System.FilePath) := [
        (System.FilePath.mk s!"{tmpBase}.server", System.FilePath.mk s!"{oleanPath}.server"),
        (System.FilePath.mk s!"{tmpBase}.private", System.FilePath.mk s!"{oleanPath}.private"),
        (tmpBase.withExtension "ir.sig", oleanPath.withExtension "ir.sig"),
        (tmpBase.withExtension "ir", oleanPath.withExtension "ir"),
        (tmpBase, oleanPath)
      ]
      for (srcP, dstP) in pairs do
        if ← srcP.pathExists then
          IO.FS.rename srcP dstP
    else
      IO.FS.rename tmpBase oleanPath
    return true
  catch _ =>
    cleanupTmp
    return false

def writeVerifiedModuleOlean (baseEnv finalEnv : Environment) (modName : Name) (oleanPath : System.FilePath) : IO Bool :=
  writeAuditedModuleOlean baseEnv finalEnv modName oleanPath false

def writeVerifiedOutlineOlean (baseEnv finalEnv : Environment) (modName : Name) (oleanPath : System.FilePath) : IO Bool :=
  writeAuditedModuleOlean baseEnv finalEnv modName oleanPath true

/-- Parse every command; scopes, options and local modifiers require checkpoint replay. -/
def environmentOnlyPrefix (env : Environment) (code : String) : Bool := Id.run do
  let ctx := Parser.mkInputContext code "<compact-prefix>"
  let mut state : Parser.ModuleParserState := {}
  while !ctx.atEnd state.pos do
    let (syn, next, msgs) := Parser.parseCommand ctx { env := env, options := {} } state {}
    if next.pos == state.pos || msgs.hasErrors then return false
    if syn.isOfKind ``Lean.Parser.Command.eoi then break
    if !syn.isOfKind ``Lean.Parser.Command.declaration then return false
    -- Only a doc comment is harmless. Inspect every modifier, not just attributes.
    if (syn[0].getArgs.extract 1 syn[0].getNumArgs).any (fun s => s.getNumArgs > 0) then return false
    if (syn.find? fun s => s.isOfKind ``Lean.Parser.Term.attrKind && s[0].getNumArgs > 0).isSome then return false
    state := next
  return true

def compactPrefix? (baseEnv finalEnv : Environment) (imports : Array Import) (level : OLeanLevel) : IO (Option Environment) := do
  if finalEnv.constants.map₂.foldl (fun bad n _ => bad ||
      (canonicalName (Lean.privateToUserName n)).startsWith "_turbo_verify_") false then return none
  let (clean, _, _) ← auditNewKernelDecls baseEnv finalEnv (fun _ => false) false
  if !clean then return none
  let oldPath ← searchPathRef.get
  let mut result := none
  let some staging ← IO.getEnv "TURBO_LEAN_STAGING_DIR" | return none
  let pid ← IO.Process.getPID
  let stamp ← IO.monoNanosNow
  let modName := Name.mkSimple s!"TurboPrefix_{pid}_{stamp}"
  let path := System.FilePath.mk staging / s!"{modName}.olean"
  try
    if ← writeVerifiedModuleOlean baseEnv (finalEnv.setMainModule modName) modName path then
      searchPathRef.set (System.FilePath.mk staging :: oldPath)
      try discard <| Lake.importModulesUsingCache #[{ module := .anonymous }] {} 0 catch _ => pure ()
      result := some (← Lean.importModules (imports.push { module := modName }) {} 1025 #[] false true level)
  catch _ => pure ()
  searchPathRef.set oldPath
  for ext in ["", ".server", ".private", ".ir", ".ir.sig", ".olean", ".olean.server", ".olean.private"] do
    try IO.FS.removeFile (System.FilePath.mk s!"{staging}/{modName}{ext}") catch _ => pure ()
  return result

/-- Elaborate and kernel-typecheck `bodyCode` on top of an immutable `baseEnv : Lean.Environment`
    without mutating `baseEnv`.
    Returns `(ok, elapsed_us, heartbeats, proof_term_nodes, error_messages, all_messages, captured_stdout, used_constants, decl_types, sorry_decls)`. -/
def checkShardWithEnv
    (baseEnv : Environment)
    (bodyCode : String)
    (allowStub : Bool := false)
    (evalMode : Bool := false)
    (fileName : String := "<zygote-shard>")
    (emitOlean? : Option (Name × System.FilePath) := none)
    (encodedLeanArgs : String := "")
    (stubTargets : List String := [])
    (stubs : List String := [])
    (requiredTargets : Option (List String) := none)
    (fastMap : List (String × String) := [])
    (includeStubsInDeclTypes : Bool := false)
    (allowSorry : Bool := false)
    (emitOutlineOlean : Bool := false) : IO (Bool × Nat × Nat × Nat × List String × List String × String × List String × List (String × String) × List String) := do
  -- Eval mode elaborates with the options `Lean.Elab.runFrontend` forces on the command
  -- line (snapshot reporting and asynchronous elaboration); check mode keeps `{}`.
  let initOpts : Options := if evalMode then
      Elab.async.setIfNotSet (Lean.internal.cmdlineSnapshots.setIfNotSet {} true) true
    else {}
  let opts ← applyEncodedLeanArgs initOpts encodedLeanArgs
  let env ← match emitOlean? with
    | some (modName, _) => pure (if modName.isAnonymous then baseEnv else baseEnv.setMainModule modName)
    | none =>
      if evalMode then do
        let mainMod ← deriveEvalMainModule fileName
        pure (if mainMod.isAnonymous then baseEnv else baseEnv.setMainModule mainMod)
      else pure baseEnv
  let baseState := Command.mkState env {} (← withToolchainSatSolver opts)
  let (ok, elapsedUs, heartbeats, proofTermNodes, errs, allMessages, capturedStdout, usedConstants, declTypes, sorryDecls, finalSt) ←
    runCommandsFromState baseState bodyCode fileName (allowStub || emitOutlineOlean) evalMode stubTargets stubs
      (requiredTargets := requiredTargets) (fastMap := fastMap) (includeStubsInDeclTypes := includeStubsInDeclTypes)
      (allowSorry := allowSorry)
  let mut finalOk := ok
  let mut finalErrs := errs
  if finalOk then
    if let some (modName, oleanPath) := emitOlean? then
      if emitOutlineOlean then
        if allowSorry || evalMode then
          finalOk := false
          finalErrs := finalErrs ++ ["emit_outline_olean rejected allow_sorry or eval mode"]
        else
          let wrote ← writeVerifiedOutlineOlean baseEnv finalSt.env modName oleanPath
          if !wrote then
            finalOk := false
            finalErrs := finalErrs ++ ["emit_outline_olean failed module identity or kernel hygiene gate"]
      else if allowStub || allowSorry || evalMode then
        finalOk := false
        finalErrs := finalErrs ++ ["emit_olean rejected stubbed or eval mode"]
      else
        let wrote ← writeVerifiedModuleOlean baseEnv finalSt.env modName oleanPath
        if !wrote then
          finalOk := false
          finalErrs := finalErrs ++ ["emit_olean failed module identity or kernel hygiene gate"]
  return (finalOk, elapsedUs, heartbeats, proofTermNodes, finalErrs, allMessages, capturedStdout, usedConstants, declTypes, sorryDecls)

/-- Serialize a candidate or shard evaluation tuple into a tab-separated line for forked child IPC. -/
def serializeForkCandResult
    (ok : Bool) (elabUs hbs nodes : Nat)
    (errs msgs : List String) (outStr : String)
    (used : List String) (declTypes : List (String × String))
    (sorryDecls : List String := []) : ByteArray :=
  let fields : List String := [
    if ok then "1" else "0",
    toString elabUs,
    toString hbs,
    toString nodes,
    encodeHexList errs,
    encodeHexList msgs,
    encodeStringToHex outStr,
    encodeHexList used,
    encodeHexPairs declTypes,
    encodeHexList sorryDecls
  ]
  (String.intercalate "\t" fields).toUTF8

/-- Parse a serialized forked child payload back into the evaluation tuple. -/
def deserializeForkCandResult (ba : ByteArray)
    : Option (Bool × Nat × Nat × Nat × List String × List String × String × List String × List (String × String) × List String) :=
  match String.fromUTF8? ba with
  | none => none
  | some raw =>
    let cols := raw.trimAscii.toString.splitOn "\t"
    if cols.length < 9 then none
    else
      let ok := (cols[0]?.getD "0") == "1"
      let elabUs := (cols[1]?.getD "0").toNat?.getD 0
      let hbs := (cols[2]?.getD "0").toNat?.getD 0
      let nodes := (cols[3]?.getD "0").toNat?.getD 0
      let errs := decodeHexList (cols[4]?.getD "")
      let msgs := decodeHexList (cols[5]?.getD "")
      let outStr := decodeHexToString (cols[6]?.getD "")
      let used := decodeHexList (cols[7]?.getD "")
      let declTypes := decodeHexPairs (cols[8]?.getD "")
      let sorryDecls := decodeHexList (cols[9]?.getD "")
      some (ok, elabUs, hbs, nodes, errs, msgs, outStr, used, declTypes, sorryDecls)

/-- Execute `checkShardWithEnv` in a CoW-forked child over compacted `baseEnv` (`m_rc == 0`),
    preventing elaboration heap allocations from growing the long-lived parent Zygote RSS. -/
def checkShardWithEnvForked
    (baseEnv : Environment)
    (bodyCode : String)
    (allowStub : Bool := false)
    (evalMode : Bool := false)
    (fileName : String := "<zygote-shard>")
    (emitOlean? : Option (Name × System.FilePath) := none)
    (encodedLeanArgs : String := "")
    (stubTargets : List String := [])
    (stubs : List String := [])
    (requiredTargets : Option (List String) := none)
    (fastMap : List (String × String) := [])
    (includeStubsInDeclTypes : Bool := false)
    (allowSorry : Bool := false)
    (emitOutlineOlean : Bool := false) : IO (Bool × Nat × Nat × Nat × List String × List String × String × List String × List (String × String) × List String) := do
  let (childCleanExit, payload) ← TurboLean.ZygoteFork.runIsolatedInFork 2 do
    let (ok, us, hbs, nodes, errs, msgs, outS, used, dts, sds) ←
      checkShardWithEnv baseEnv bodyCode allowStub evalMode fileName emitOlean? encodedLeanArgs stubTargets stubs
        (requiredTargets := requiredTargets) (fastMap := fastMap) (includeStubsInDeclTypes := includeStubsInDeclTypes)
        (allowSorry := allowSorry) (emitOutlineOlean := emitOutlineOlean)
    return serializeForkCandResult ok us hbs nodes errs msgs outS used dts sds
  match deserializeForkCandResult payload with
  | some res =>
    if childCleanExit then return res
    else
      let (_, us, hbs, nodes, errs, msgs, outS, used, dts, sds) := res
      let mergedErrs := if errs.isEmpty then ["[TurboLean.ZygoteFork] forked shard child exited non-zero"] else errs
      return (false, us, hbs, nodes, mergedErrs, msgs, outS, used, dts, sds)
  | none =>
    return (false, 0, 0, 0, ["[TurboLean.ZygoteFork] forked shard child crashed or produced empty payload"], [], "", [], [], [])

/-- Run a `batch_fission` sub-shard loop using `evalSub` and return `(ok, elabUs, hbs, nodes, verifiedCount, outStr, msgs, errs, used, declTypes)`. -/
def runBatchFissionSubs (hexSubs : List String)
    (evalSub : String → IO (Bool × Nat × Nat × Nat × List String × List String × String × List String × List (String × String)))
    : IO (Bool × Nat × Nat × Nat × Nat × String × List String × List String × List String × List (String × String)) := do
  let mut batchOk := true
  let mut totalElabUs : Nat := 0
  let mut totalHbs : Nat := 0
  let mut totalNodes : Nat := 0
  let mut allErrs : List String := []
  let mut allMsgs : List String := []
  let mut allOut : String := ""
  let mut allUsed : List String := []
  let mut allDeclTypes : List (String × String) := []
  let mut verifiedCount : Nat := 0
  for hexSub in hexSubs do
    let subCode := decodeHexToString hexSub
    let (subOk, subElabUs, subHbs, subNodes, subErrs, subMsgs, subOut, subUsed, subDeclTypes) ← evalSub subCode
    totalElabUs := totalElabUs + subElabUs
    totalHbs := totalHbs + subHbs
    totalNodes := totalNodes + subNodes
    allMsgs := allMsgs ++ subMsgs
    allOut := allOut ++ subOut
    for c in subUsed do
      if !allUsed.contains c then allUsed := allUsed ++ [c]
    for (dn, dh) in subDeclTypes do
      if !(allDeclTypes.any (fun (k, _) => k == dn)) then
        allDeclTypes := allDeclTypes ++ [(dn, dh)]
    if subOk then verifiedCount := verifiedCount + 1
    else batchOk := false; allErrs := allErrs ++ subErrs; break
  return (batchOk, totalElabUs, totalHbs, totalNodes, verifiedCount, allOut, allMsgs, allErrs, allUsed, allDeclTypes)

/-- Sequential fallback for `race_candidates` (used for 0/1 candidates or when `TURBO_LEAN_ZYGOTE_FORK=0`). -/
def runRaceCandidatesSubsSequential (hexSubs : List String)
    (evalCand : String → IO (Bool × Nat × Nat × Nat × List String × List String × String × List String × List (String × String)))
    (abortOnFirstFail : Bool := false)
    : IO (Bool × String × Nat × Nat × Nat × Nat × String × List String × List String × List String × List (String × String)) := do
  let mut raceOk := false
  let mut winningIdx? : Option Nat := none
  let mut totalElabUs : Nat := 0
  let mut totalHbs : Nat := 0
  let mut winNodes : Nat := 0
  let mut lastErrs : List String := []
  let mut winMsgs : List String := []
  let mut winOut : String := ""
  let mut winUsed : List String := []
  let mut winDeclTypes : List (String × String) := []
  let mut candIdx : Nat := 0
  for hexCand in hexSubs do
    let candCode := decodeHexToString hexCand
    let (candOk, candElabUs, candHbs, candNodes, candErrs, candMsgs, candOut, candUsed, candDeclTypes) ← evalCand candCode
    totalElabUs := totalElabUs + candElabUs
    totalHbs := totalHbs + candHbs
    -- A runtime panic poisons the whole process: abort the race and fail the request even if an
    -- earlier candidate already won.
    if candErrs.contains runtimePanicErr then
      raceOk := false; winningIdx? := none; lastErrs := candErrs; winMsgs := candMsgs; winOut := candOut
      winUsed := []; winDeclTypes := []; winNodes := 0
      break
    if candOk then
      let isBetter := !raceOk || (candNodes > 0 && (winNodes == 0 || candNodes < winNodes))
      if isBetter then
        raceOk := true; winningIdx? := some candIdx; winNodes := candNodes
        winMsgs := candMsgs; winOut := candOut; winUsed := candUsed; winDeclTypes := candDeclTypes; lastErrs := []
      if candNodes <= 500 || totalElabUs >= 8000 then break
      candIdx := candIdx + 1
    else
      if !raceOk then
        lastErrs := candErrs; winMsgs := candMsgs; winOut := candOut
      candIdx := candIdx + 1
      if abortOnFirstFail then break
  let winIdxJson := match winningIdx? with | some idx => toString idx | none => "null"
  return (raceOk, winIdxJson, totalElabUs, totalHbs, winNodes, if raceOk then 1 else 0, winOut, winMsgs, lastErrs, winUsed, winDeclTypes)

/-- Parallel `race_candidates` across POSIX CoW-forked children over compacted `baseEnv` (`m_rc == 0`),
    bounded by `min(available_parallelism, 4)`.
    - Children never touch parent `stdin`, `stdout`, or file locks; each writes its verdict to a private pipe and `_exit(0)`s.
    - First child passing `auditNewKernelDecls` (`0 sorryAx`) immediately `SIGKILL`s still-running slower siblings and reaps all PIDs.
    - Any child reporting `runtimePanicErr` poisons and fails the entire request even if another candidate won. -/
def runRaceCandidatesSubs (hexSubs : List String)
    (evalCandSequential : String → IO (Bool × Nat × Nat × Nat × List String × List String × String × List String × List (String × String)))
    (abortOnFirstFail : Bool := false)
    (forkEvalCand? : Option (String → IO (Bool × Nat × Nat × Nat × List String × List String × String × List String × List (String × String))) := none)
    : IO (Bool × String × Nat × Nat × Nat × Nat × String × List String × List String × List String × List (String × String)) := do
  let forkEnabled ← TurboLean.ZygoteFork.isForkEnabled
  let maxJobs ← TurboLean.ZygoteFork.raceForkConcurrency
  let hasPotentiallyPanickingCand := hexSubs.any fun hs =>
    let sc := decodeHexToString hs
    (sc.splitOn "panic!").length > 1 || (sc.splitOn "lcUnreachable").length > 1
  match forkEvalCand? with
  | some forkEvalCand =>
    if !forkEnabled || maxJobs <= 1 || hexSubs.length <= 1 || hasPotentiallyPanickingCand then
      runRaceCandidatesSubsSequential hexSubs evalCandSequential abortOnFirstFail
    else
      let candArr := hexSubs.toArray
      let numCands := candArr.size
      let mut nextLaunch : Nat := 0
      -- Active children: `(pid, candIdx, readFd)`
      let mut active : Array (UInt32 × Nat × UInt32) := #[]
      let mut stopLaunching := false
      let mut raceOk := false
      let mut winningIdx? : Option Nat := none
      let mut totalElabUs : Nat := 0
      let mut totalHbs : Nat := 0
      let mut winNodes : Nat := 0
      let mut lastErrs : List String := []
      let mut winMsgs : List String := []
      let mut winOut : String := ""
      let mut winUsed : List String := []
      let mut winDeclTypes : List (String × String) := []
      let mut sawPanic := false

      let spawnOne := fun (cIdx : Nat) (openReadFds : Array UInt32) => do
        let candCode := decodeHexToString candArr[cIdx]!
        let (rFd, wFd) ← TurboLean.ZygoteFork.posixPipe
        let pid ← try
            TurboLean.ZygoteFork.spawnQuiescedForkChild 1 do
              TurboLean.ZygoteFork.posixClose rFd
              for otherFd in openReadFds do
                TurboLean.ZygoteFork.posixClose otherFd
              let (cOk, cUs, cHbs, cNodes, cErrs, cMsgs, cOut, cUsed, cDts) ← forkEvalCand candCode
              let payload := serializeForkCandResult cOk cUs cHbs cNodes cErrs cMsgs cOut cUsed cDts []
              let wrote ← TurboLean.ZygoteFork.posixWriteAll wFd payload
              TurboLean.ZygoteFork.posixClose wFd
              return (if wrote then 0 else 2)
          catch e =>
            TurboLean.ZygoteFork.posixClose rFd
            TurboLean.ZygoteFork.posixClose wFd
            throw e
        TurboLean.ZygoteFork.posixClose wFd
        return (pid, cIdx, rFd)

      while (nextLaunch < numCands && !stopLaunching) || !active.isEmpty do
        while !stopLaunching && nextLaunch < numCands && active.size < maxJobs do
          let openR := active.map (fun (_, _, fd) => fd)
          let entry ← spawnOne nextLaunch openR
          active := active.push entry
          nextLaunch := nextLaunch + 1

        if !active.isEmpty then
          let (reapedPid, rawSt) ← TurboLean.ZygoteFork.posixWaitPid 0
          if reapedPid == 0 then
            -- Defensive drain if no child could be waited
            for (_, _, fd) in active do
              TurboLean.ZygoteFork.posixClose fd
            active := #[]
            stopLaunching := true
          else
            let matched? := active.findIdx? (fun (p, _, _) => p == reapedPid)
            match matched? with
            | none => pure ()
            | some slotIdx =>
              let (_, cIdx, rFd) := active[slotIdx]!
              active := active.eraseIdxIfInBounds slotIdx
              let payload ← TurboLean.ZygoteFork.posixReadAll rFd 65536
              TurboLean.ZygoteFork.posixClose rFd
              let exitedZero := TurboLean.ZygoteFork.waitStatusExitedZero rawSt
              match deserializeForkCandResult payload with
              | some (candOkRaw, candElabUs, candHbs, candNodes, candErrs, candMsgs, candOut, candUsed, candDeclTypes, _) =>
                let candOk := candOkRaw && exitedZero
                totalElabUs := totalElabUs + candElabUs
                totalHbs := totalHbs + candHbs
                if candErrs.contains runtimePanicErr then
                  sawPanic := true
                  stopLaunching := true
                  raceOk := false
                  winningIdx? := none
                  lastErrs := candErrs
                  winMsgs := candMsgs
                  winOut := candOut
                  winUsed := []
                  winDeclTypes := []
                  winNodes := 0
                  for (sibPid, _, _) in active do
                    TurboLean.ZygoteFork.posixKillSigkill sibPid
                else if !sawPanic && candOk then
                  let isBetter := !raceOk || (candNodes > 0 && (winNodes == 0 || candNodes < winNodes))
                  if isBetter then
                    raceOk := true
                    winningIdx? := some cIdx
                    winNodes := candNodes
                    winMsgs := candMsgs
                    winOut := candOut
                    winUsed := candUsed
                    winDeclTypes := candDeclTypes
                    lastErrs := []
                  stopLaunching := true
                  for (sibPid, _, _) in active do
                    TurboLean.ZygoteFork.posixKillSigkill sibPid
                else if !sawPanic && !raceOk then
                  if !candErrs.isEmpty then
                    lastErrs := candErrs
                    winMsgs := candMsgs
                    winOut := candOut
                  if abortOnFirstFail then
                    stopLaunching := true
                    for (sibPid, _, _) in active do
                      TurboLean.ZygoteFork.posixKillSigkill sibPid
              | none =>
                if !sawPanic && !raceOk && lastErrs.isEmpty then
                  lastErrs := ["[TurboLean.ZygoteFork] race candidate child exited before producing verdict"]

      let winIdxJson := match winningIdx? with | some idx => toString idx | none => "null"
      return (raceOk, winIdxJson, totalElabUs, totalHbs, winNodes, if raceOk then 1 else 0, winOut, winMsgs, lastErrs, winUsed, winDeclTypes)
  | none =>
    runRaceCandidatesSubsSequential hexSubs evalCandSequential abortOnFirstFail

end TurboLean.ZygoteWorker
