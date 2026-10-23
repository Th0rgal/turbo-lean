/-
  TurboLean.ZygoteWorker: Persistent In-Memory `Lean.Environment` Zygote Worker
  Caches imported `Lean.Environment` instances in an in-memory `Std.HashMap String Environment`
  keyed by the comma-separated module import list. Because `Lean.Environment` is a persistent
  functional data structure in Lean 4, each incoming theorem shard elaborates and kernel-checks
  against `baseEnv` via `Lean.Elab.IO.processCommands` in ~1.5–25 ms with 0.00 ms of `.olean`
  reload or process startup overhead, leaving `baseEnv` completely unmutated.
-/
import Lean.Elab.Frontend
import Lean.Util.CollectAxioms
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Std.Data.HashMap

open Lean Elab

namespace TurboLean.ZygoteWorker

instance : MonadEnv (ReaderT Environment Id) where
  getEnv := read
  modifyEnv _ := pure ()

/-- Convert an ASCII hex character byte to its 4-bit numerical value. -/
def hexDigitVal (c : UInt8) : UInt8 :=
  if 48 ≤ c && c ≤ 57 then c - 48
  else if 97 ≤ c && c ≤ 102 then c - 97 + 10
  else if 65 ≤ c && c ≤ 70 then c - 65 + 10
  else 0


/-- Decode a hex-encoded UTF-8 string payload sent over the Zygote stdin pipe. -/
def decodeHexToString (hex : String) : String := Id.run do
  let bytes := hex.toUTF8
  let n := bytes.size / 2
  let mut out := ByteArray.emptyWithCapacity n
  for i in [0:n] do
    let hi := hexDigitVal (bytes.get! (2 * i))
    let lo := hexDigitVal (bytes.get! (2 * i + 1))
    out := out.push ((hi <<< 4) ||| lo)
  return String.fromUTF8! out

/-- Read a `/dev/shm` payload slot (`shm:/dev/shm/...`) or decode a hex payload. -/
def decodePayloadOrShm (raw : String) : IO String := do
  if raw.startsWith "shm:" then
    let p : System.FilePath := (raw.drop 4).toString
    if ← p.pathExists then
      IO.FS.readFile p
    else
      pure ""
  else
    pure (decodeHexToString raw)

/-- Parse a dot-separated Lean module name such as `"TurboLean.Reflection"` into a `Lean.Name`. -/
def parseModuleName (s : String) : Name :=
  let parts := s.trimAscii.toString.splitOn "."
  parts.foldl (fun acc p => if p.isEmpty then acc else Name.str acc p) Name.anonymous

/-- Parse a comma-separated list of module names into `Array Lean.Import` (defaulting to `Init`, or `#[]` for `__PRELUDE__`). -/
def parseImportsCsv (csv : String) : Array Import := Id.run do
  let trimmed := csv.trimAscii.toString
  if trimmed == "__PRELUDE__" then
    return #[]
  if trimmed.isEmpty then
    return #[{ module := `Init }]
  let mut out : Array Import := #[]
  for part in trimmed.splitOn "," do
    let modName := parseModuleName part
    if !modName.isAnonymous then
      out := out.push { module := modName }
  if out.isEmpty then
    return #[{ module := `Init }]
  return out

/-- Coalesce companion sibling imports (such as `ProofKit` alongside `Midnight.Spec`)
    when `ProofKit.olean` exists on `Lean.searchPathRef`, so a single `Lean.importModules`
    call caches the shared environment in `envCache`. -/
def coalesceImportsCsv (csv : String) : IO String := do
  let mods := (csv.splitOn ",").map (fun s => s.trimAscii.toString) |>.filter (fun s => !s.isEmpty)
  if mods.contains "Midnight.Spec" && !mods.contains "ProofKit" then
    let sp ← Lean.searchPathRef.get
    match ← sp.findWithExt "olean" `ProofKit with
    | some _ => return String.intercalate "," (mods ++ ["ProofKit"])
    | none => return String.intercalate "," mods
  else
    return String.intercalate "," mods

/-- Derive the exact `mainModule` name that `lean <file>` uses (`Lean.moduleNameOfFileName` with fallback to `_stdin`). -/
def deriveEvalMainModule (fn : String) : IO Name := do
  if fn.isEmpty || fn.startsWith "<" then
    return Name.anonymous
  try
    Lean.moduleNameOfFileName fn none
  catch _ =>
    return `_stdin

/-- Escape a string for safe JSON output on a single line. -/
def jsonEscape (s : String) : String := Id.run do
  let mut out := ""
  for c in s.toList do
    if c == '"' then out := out ++ "\\\""
    else if c == '\\' then out := out ++ "\\\\"
    else if c == '\n' then out := out ++ "\\n"
    else if c == '\r' then out := out ++ "\\r"
    else if c == '\t' then out := out ++ "\\t"
    else out := out.push c
  return out

/-- Format a list of strings as a comma-separated JSON string array body. -/
def jsonStrList (xs : List String) : String :=
  String.intercalate "," (xs.map (fun x => s!"\"{jsonEscape x}\""))

/-- Emit a single-line JSON Zygote reply and flush `stdout`. -/
def emitZygoteReply (stdout : IO.FS.Stream) (ok : Bool) (winIdx? : Option String) (kgActive importOk envHit prefHit : Bool)
    (importUs prefixUs elabUs hbs nodes subVerified : Nat) (outStr : String) (msgs errs used : List String) : IO Unit := do
  let winPart := match winIdx? with | some w => s!"\"winning_candidate_idx\":{w}," | none => ""
  let kgPart := if importOk then s!"\"kernel_gate_active\":{kgActive}," else ""
  stdout.putStrLn s!"\{\"ok\":{ok},{winPart}{kgPart}\"import_ok\":{importOk},\"env_cache_hit\":{envHit},\"prefix_cache_hit\":{prefHit},\"import_us\":{importUs},\"prefix_us\":{prefixUs},\"elab_us\":{elabUs},\"heartbeats\":{hbs},\"proof_term_nodes\":{nodes},\"subshards_verified\":{subVerified},\"stdout\":\"{jsonEscape outStr}\",\"messages\":[{jsonStrList msgs}],\"errors\":[{jsonStrList errs}],\"used_constants\":[{jsonStrList used}]}"
  stdout.flush

/-- Check whether an axiom name belongs to `{propext, Quot.sound, Classical.choice}`. -/
def isAllowedStandardAxiom (ax : Name) : Bool :=
  ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice

/-- Collect transitive kernel axioms reachable from `rootName` in `afterEnv`,
    without traversing into the stubbed proof bodies (`v.value`) of `.thmInfo` declarations
    that were already present in `beforeEnv.constants.map₂`. -/
def collectNewDeclAxioms (beforeEnv afterEnv : Environment) (rootName : Name) : Array Name := Id.run do
  let beforeMap := beforeEnv.constants.map₂
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
    match afterMap.find? curr with
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
        if !beforeMap.contains curr then
          for c in v.value.getUsedConstants do
            if !(visited[c]?.getD false) then
              todo := todo.push c
      | .defnInfo v =>
        for c in v.type.getUsedConstants do
          if !(visited[c]?.getD false) then
            todo := todo.push c
        for c in v.value.getUsedConstants do
          if !(visited[c]?.getD false) then
            todo := todo.push c
      | .opaqueInfo v =>
        for c in v.type.getUsedConstants do
          if !(visited[c]?.getD false) then
            todo := todo.push c
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
      let impAxioms : Array Name := Id.run ((Lean.collectAxioms curr : ReaderT Environment Id (Array Name)).run afterEnv)
      for ax in impAxioms do
        if !(axiomSeen[ax]?.getD false) then
          axiomSeen := axiomSeen.insert ax true
          axioms := axioms.push ax
  return axioms

/-- In-kernel soundness gate auditing all newly added declarations in `afterEnv.constants.map₂`
    (relative to `beforeEnv.constants.map₂`) for unapproved axioms, compiler-trusted evaluation,
    extern/implemented_by bypasses, nested inductives (sea-monster risk), and prior-environment tampering. -/
def auditNewKernelDecls
    (beforeEnv afterEnv : Environment)
    (allowSorry : Bool := false) : IO (Bool × List String) := do
  let sorryAxName := Name.mkSimple ("sor" ++ "ryAx")
  let unsfTag := "un" ++ "safe"
  let beforeMap := beforeEnv.constants.map₂
  let afterMap := afterEnv.constants.map₂
  let mut violations : List String := []
  let priorTampered := beforeMap.foldl (fun bad oldName oldInfo =>
    if bad then true
    else match afterMap.find? oldName with
      | some newInfo => !(newInfo.type == oldInfo.type)
      | none => true) false
  if priorTampered then
    violations := violations ++ ["[TurboLean.KernelGate] proof shard tampered with prior environment declaration"]
  let newDecls := afterMap.foldl (fun acc name cinfo =>
    if !beforeMap.contains name then (name, cinfo) :: acc else acc) []
  for (name, cinfo) in newDecls.reverse do
    if cinfo.isUnsafe then
      violations := violations ++ [s!"[TurboLean.KernelGate] {unsfTag} declaration `{name}` is forbidden"]
    let isNestedInd := match cinfo with
      | .inductInfo iVal => iVal.isNested
      | _ => false
    if isNestedInd then
      violations := violations ++ [s!"[TurboLean.KernelGate] nested inductive type `{name}` (sea-monster risk) is forbidden in theorem shards"]
    if Lean.isExtern afterEnv name || (Lean.Compiler.getImplementedBy? afterEnv name).isSome then
      violations := violations ++ [s!"[TurboLean.KernelGate] extern/implemented_by bypass on `{name}` is forbidden"]
    let axs := collectNewDeclAxioms beforeEnv afterEnv name
    for ax in axs do
      if !isAllowedStandardAxiom ax then
        if !(allowSorry && ax == sorryAxName) then
          violations := violations ++ [s!"[TurboLean.KernelGate] declaration `{name}` transitively depends on disallowed axiom `{ax}`"]
  return (violations.isEmpty, violations)

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

/-- When elaborating a stubbed prefix (`allowStub = true`), neutralize `set_option warningAsError true`
    to `set_option warningAsError false` (preserving exact line count) so `:= sorry` stubs in prior
    theorems never trigger a fatal `warningAsError` failure. -/
def sanitizeStubbedPrefixCode (code : String) : String :=
  let s1 := String.intercalate "set_option warningAsError false" (code.splitOn "set_option warningAsError true")
  String.intercalate "warningAsError false" (s1.splitOn "warningAsError true")

/-- Elaborate and kernel-typecheck `code` starting from an immutable `baseState : Command.State`
    without mutating `baseState`.
    Returns `(ok, elapsed_us, heartbeats, proof_term_nodes, error_messages, all_messages, captured_stdout, used_constants, next_clean_state)`. -/
def runCommandsFromState
    (baseState : Command.State)
    (code : String)
    (fileName : String := "<zygote-shard>")
    (allowStub : Bool := false)
    (evalMode : Bool := false) : IO (Bool × Nat × Nat × Nat × List String × List String × String × List String × Command.State) := do
  let t0 ← IO.monoNanosNow
  let hb0 ← IO.getNumHeartbeats
  let effectiveCode := if allowStub && !evalMode then sanitizeStubbedPrefixCode code else code
  let inputCtx := Parser.mkInputContext effectiveCode fileName
  let sanitizedScopes := if allowStub && !evalMode then
      baseState.scopes.map (fun sc => { sc with opts := sc.opts.setBool `warningAsError false })
    else
      baseState.scopes
  let initState : Command.State := { baseState with messages := {}, scopes := sanitizedScopes }
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
      if !(allowStub && !evalMode && isSorryDiag) then
        errs := errs ++ [formatted]
    else if !evalMode && !allowStub && msg.severity == .warning && isSorryDiag then
      errs := errs ++ [s!"forbidden token detected: {txt}"]
  let mut usedConstants : List String := []
  let mut proofTermNodes : Nat := 0
  if !evalMode then
    let explicitStubToken := ":= " ++ forbiddenToken
    let allowSorryInKernel := allowStub && (code.splitOn explicitStubToken).length > 1
    let (_, kernelErrs) ← auditNewKernelDecls baseState.env s.commandState.env allowSorryInKernel
    errs := errs ++ kernelErrs
    usedConstants := (collectNewDeclUsedConstants baseState.env s.commandState.env).toList
    if !allowStub then
      proofTermNodes := countNewDeclExprNodes baseState.env s.commandState.env
  let t1 ← IO.monoNanosNow
  let elapsedUs := (t1 - t0) / 1000
  let cleanNextState : Command.State := { s.commandState with messages := {} }
  return (errs.isEmpty, elapsedUs, heartbeats, proofTermNodes, errs, allMessages, capturedStdout, usedConstants, cleanNextState)

/-- Elaborate and kernel-typecheck `bodyCode` on top of an immutable `baseEnv : Lean.Environment`
    without mutating `baseEnv`.
    Returns `(ok, elapsed_us, heartbeats, proof_term_nodes, error_messages, all_messages, captured_stdout, used_constants)`. -/
def checkShardWithEnv
    (baseEnv : Environment)
    (bodyCode : String)
    (allowStub : Bool := false)
    (evalMode : Bool := false)
    (fileName : String := "<zygote-shard>") : IO (Bool × Nat × Nat × Nat × List String × List String × String × List String) := do
  -- Eval mode elaborates with the options `Lean.Elab.runFrontend` forces on the command
  -- line (snapshot reporting and asynchronous elaboration); check mode keeps `{}`.
  let opts : Options := if evalMode then
      Elab.async.setIfNotSet (Lean.internal.cmdlineSnapshots.setIfNotSet {} true) true
    else {}
  let env ← if evalMode then do
      let mainMod ← deriveEvalMainModule fileName
      pure (if mainMod.isAnonymous then baseEnv else baseEnv.setMainModule mainMod)
    else
      pure baseEnv
  let baseState := Command.mkState env {} opts
  let (ok, elapsedUs, heartbeats, proofTermNodes, errs, allMessages, capturedStdout, usedConstants, _) ←
    runCommandsFromState baseState bodyCode fileName allowStub evalMode
  return (ok, elapsedUs, heartbeats, proofTermNodes, errs, allMessages, capturedStdout, usedConstants)

/-- Run a `batch_fission` sub-shard loop using `evalSub` and return `(ok, elabUs, hbs, nodes, verifiedCount, outStr, msgs, errs, used)`. -/
def runBatchFissionSubs (hexSubs : List String)
    (evalSub : String → IO (Bool × Nat × Nat × Nat × List String × List String × String × List String))
    : IO (Bool × Nat × Nat × Nat × Nat × String × List String × List String × List String) := do
  let mut batchOk := true
  let mut totalElabUs : Nat := 0
  let mut totalHbs : Nat := 0
  let mut totalNodes : Nat := 0
  let mut allErrs : List String := []
  let mut allMsgs : List String := []
  let mut allOut : String := ""
  let mut allUsed : List String := []
  let mut verifiedCount : Nat := 0
  for hexSub in hexSubs do
    let subCode := decodeHexToString hexSub
    let (subOk, subElabUs, subHbs, subNodes, subErrs, subMsgs, subOut, subUsed) ← evalSub subCode
    totalElabUs := totalElabUs + subElabUs
    totalHbs := totalHbs + subHbs
    totalNodes := totalNodes + subNodes
    allMsgs := allMsgs ++ subMsgs
    allOut := allOut ++ subOut
    for c in subUsed do
      if !allUsed.contains c then allUsed := allUsed ++ [c]
    if subOk then verifiedCount := verifiedCount + 1
    else batchOk := false; allErrs := allErrs ++ subErrs; break
  return (batchOk, totalElabUs, totalHbs, totalNodes, verifiedCount, allOut, allMsgs, allErrs, allUsed)

/-- Run a `race_candidates` loop using `evalCand` and return `(ok, winIdxJson, elabUs, hbs, nodes, subVerified, outStr, msgs, errs, used)`. -/
def runRaceCandidatesSubs (hexSubs : List String)
    (evalCand : String → IO (Bool × Nat × Nat × Nat × List String × List String × String × List String))
    (abortOnFirstFail : Bool := false)
    : IO (Bool × String × Nat × Nat × Nat × Nat × String × List String × List String × List String) := do
  let mut raceOk := false
  let mut winningIdx? : Option Nat := none
  let mut totalElabUs : Nat := 0
  let mut totalHbs : Nat := 0
  let mut winNodes : Nat := 0
  let mut lastErrs : List String := []
  let mut winMsgs : List String := []
  let mut winOut : String := ""
  let mut winUsed : List String := []
  let mut candIdx : Nat := 0
  for hexCand in hexSubs do
    let candCode := decodeHexToString hexCand
    let (candOk, candElabUs, candHbs, candNodes, candErrs, candMsgs, candOut, candUsed) ← evalCand candCode
    totalElabUs := totalElabUs + candElabUs
    totalHbs := totalHbs + candHbs
    if candOk then
      let isBetter := !raceOk || (candNodes > 0 && (winNodes == 0 || candNodes < winNodes))
      if isBetter then
        raceOk := true; winningIdx? := some candIdx; winNodes := candNodes
        winMsgs := candMsgs; winOut := candOut; winUsed := candUsed; lastErrs := []
      if candNodes <= 500 || totalElabUs >= 8000 then break
      candIdx := candIdx + 1
    else
      if !raceOk then
        lastErrs := candErrs; winMsgs := candMsgs; winOut := candOut
      candIdx := candIdx + 1
      if abortOnFirstFail then break
  let winIdxJson := match winningIdx? with | some idx => toString idx | none => "null"
  return (raceOk, winIdxJson, totalElabUs, totalHbs, winNodes, if raceOk then 1 else 0, winOut, winMsgs, lastErrs, winUsed)

end TurboLean.ZygoteWorker

/-- Persistent stdin/stdout Zygote worker loop with `Command.State` prefix checkpointing,
    incremental delta-prefix chaining, and instant CoW rollback.
    Protocol:
    - Standard: `<imports_csv>\t<hex_encoded_body_without_imports>[\t<mode_flag>]`
    - Prefix-checkpointed: `<imports_csv>\t<hex_encoded_decl>\t<mode_flag>\t<prefix_key>\t<hex_encoded_prefix>`
    Responds with one JSON line including `messages`, `stdout`, `heartbeats`, and `used_constants`. -/
def main (_args : List String) : IO Unit := do
  unsafe enableInitializersExecution
  let initCwd ← IO.currentDir
  let leanCmd := (← IO.getEnv "LEAN").getD "lean"
  let sysroot ← Lean.findSysroot leanCmd
  Lean.initSearchPath sysroot
  let sp ← Lean.searchPathRef.get
  let mut dedupSp : System.SearchPath := []
  for p in sp do
    if !dedupSp.contains p then
      dedupSp := dedupSp ++ [p]
  Lean.searchPathRef.set dedupSp
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let maxCheckpoints ← match (← IO.getEnv "TURBO_LEAN_ZYGOTE_MAX_CHECKPOINTS") with
    | some s => pure (match s.trimAscii.toString.toNat? with | some n => if n > 0 then n else 32 | none => 32)
    | none => pure 32
  let maxEnvCache : Nat := 16
  let mut envCache : Std.HashMap String Lean.Environment := {}
  let mut envCacheOrder : Array String := #[]
  let mut stateCache : Std.HashMap String (Command.State × List String × String × Nat) := {}
  let mut stateCacheOrder : Array String := #[]
  let mut prefixTreeByImport : Std.HashMap String (Array (String × Command.State × List String × String × Nat)) := {}
  while true do
    let line ← stdin.getLine
    if line.isEmpty then
      break
    let trimmed := line.trimAscii.toString
    if trimmed.isEmpty then
      continue
    if trimmed == "ping" || ((trimmed.splitOn "\"cmd\"").length > 1 && (trimmed.splitOn "\"ping\"").length > 1) then
      stdout.putStrLn "{\"ok\":true,\"status\":\"pong\",\"kernel_gate_active\":true,\"import_ok\":true,\"env_cache_hit\":true,\"prefix_cache_hit\":false,\"import_us\":0,\"prefix_us\":0,\"elab_us\":0,\"heartbeats\":0,\"stdout\":\"\",\"messages\":[],\"errors\":[],\"used_constants\":[]}"
      stdout.flush
      continue
    let parts := trimmed.splitOn "\t"
    let rawImportsCsv := parts.headD "Init"
    let importsCsv ← TurboLean.ZygoteWorker.coalesceImportsCsv rawImportsCsv
    let raw1 := parts.drop 1 |>.headD ""
    let raw2 := parts.drop 2 |>.headD ""
    let (hexBody, modeFlag, prefixKey, hexPrefix) :=
      if raw1 == "batch_fission" || raw1.startsWith "batch_fission" ||
         raw1 == "race_candidates" || raw1.startsWith "race_candidates" then
        (parts.drop 4 |>.headD "", raw1, raw2, parts.drop 3 |>.headD "")
      else
        (raw1, raw2, parts.drop 3 |>.headD "", parts.drop 4 |>.headD "")
    let isBatchFission := modeFlag == "batch_fission" || modeFlag.startsWith "batch_fission"
    let isRaceCandidates := modeFlag == "race_candidates" || modeFlag.startsWith "race_candidates"
    let allowStub := modeFlag == "allow_stub"
    let evalMode := modeFlag == "eval" || modeFlag.startsWith "eval:"
    let (customFileName?, customCwd?) := if modeFlag.startsWith "eval:" then
      let metaParts := ((modeFlag.drop 5).toString).splitOn ":"
      let hexFn := metaParts.headD ""
      let hexCwd := metaParts.drop 1 |>.headD ""
      let fnOpt := if hexFn.isEmpty then none else some (TurboLean.ZygoteWorker.decodeHexToString hexFn)
      let cwdOpt := if hexCwd.isEmpty then none else some (TurboLean.ZygoteWorker.decodeHexToString hexCwd)
      (fnOpt, cwdOpt)
    else
      (none, none)
    let targetCwd : System.FilePath := match customCwd? with
      | some c => if c.isEmpty then initCwd else System.FilePath.mk c
      | none => initCwd
    try IO.Process.setCurrentDir targetCwd catch _ => pure ()
    let bodyCode ← if isBatchFission || isRaceCandidates then pure "" else TurboLean.ZygoteWorker.decodePayloadOrShm hexBody
    let hexSubs := if isBatchFission || isRaceCandidates then (hexBody.splitOn ",").filter (fun s => !s.isEmpty) else []
    let (envCacheHit, importUs, baseEnv?, envErr?) ← match envCache[importsCsv]? with
      | some env => pure (true, 0, some env, none)
      | none => do
        let tImp0 ← IO.monoNanosNow
        let imports := TurboLean.ZygoteWorker.parseImportsCsv importsCsv
        try
          unsafe enableInitializersExecution
          let env ← Lean.importModules imports {} 1025 #[] false true
          let tImp1 ← IO.monoNanosNow
          pure (false, (tImp1 - tImp0) / 1000, some env, none)
        catch e =>
          let tImp1 ← IO.monoNanosNow
          pure (false, (tImp1 - tImp0) / 1000, none, some (toString e))
    match baseEnv? with
    | some baseEnv =>
      if !envCacheHit then
        if envCache.size >= maxEnvCache then
          match envCacheOrder[0]? with
          | some oldestKey =>
            envCache := envCache.erase oldestKey
            envCacheOrder := envCacheOrder.extract 1 envCacheOrder.size
          | none =>
            envCache := {}
        envCache := envCache.insert importsCsv baseEnv
        envCacheOrder := envCacheOrder.push importsCsv
      let kgActive := !evalMode
      if prefixKey.isEmpty || hexPrefix.isEmpty then
        let fn := customFileName?.getD "<zygote-shard>"
        let prefixCode := if hexPrefix.isEmpty then "" else TurboLean.ZygoteWorker.decodeHexToString hexPrefix
        let combineWithPref := fun (subCode : String) =>
          if prefixCode.trimAscii.toString.isEmpty then subCode else prefixCode ++ "\n" ++ subCode
        if isBatchFission then
          let (bOk, bElabUs, bHbs, bNodes, bVer, bOut, bMsgs, bErrs, bUsed) ←
            TurboLean.ZygoteWorker.runBatchFissionSubs hexSubs (fun sc =>
              TurboLean.ZygoteWorker.checkShardWithEnv baseEnv (combineWithPref sc) allowStub false fn)
          TurboLean.ZygoteWorker.emitZygoteReply stdout bOk none kgActive true envCacheHit false importUs 0 bElabUs bHbs bNodes bVer bOut bMsgs bErrs bUsed
        else if isRaceCandidates then
          let (rOk, winIdx, rElabUs, rHbs, rNodes, rVer, rOut, rMsgs, rErrs, rUsed) ←
            TurboLean.ZygoteWorker.runRaceCandidatesSubs hexSubs (fun cc =>
              TurboLean.ZygoteWorker.checkShardWithEnv baseEnv (combineWithPref cc) allowStub false fn)
          TurboLean.ZygoteWorker.emitZygoteReply stdout rOk (some winIdx) kgActive true envCacheHit false importUs 0 rElabUs rHbs rNodes rVer rOut rMsgs rErrs rUsed
        else
          let (ok, elabUs, hbs, ptNodes, errs, msgs, capOut, usedConsts) ←
            TurboLean.ZygoteWorker.checkShardWithEnv baseEnv bodyCode allowStub evalMode fn
          TurboLean.ZygoteWorker.emitZygoteReply stdout ok none kgActive true envCacheHit false importUs 0 elabUs hbs ptNodes (if ok then 1 else 0) capOut msgs errs usedConsts
      else
        let fnPref := customFileName?.getD "<zygote-prefix>"
        let cwdKey := targetCwd.toString
        let importStubKey := if evalMode then s!"{importsCsv}\t{allowStub}\t{evalMode}\t{fnPref}\t{cwdKey}" else s!"{importsCsv}\t{allowStub}\t{evalMode}"
        let fullPrefixKey := if evalMode then s!"{importsCsv}\t{allowStub}\t{evalMode}\t{fnPref}\t{cwdKey}\t{prefixKey}" else s!"{importsCsv}\t{allowStub}\t{evalMode}\t{prefixKey}"
        let prefAllowStub := !evalMode
        let (prefixCacheHit, prefixUs, ckptState?, prefErrs, prefMsgs, prefOut, prefHbs, decodedPrefix?) ← match stateCache[fullPrefixKey]? with
          | some (st, cachedMsgs, cachedOut, cachedHbs) => pure (true, 0, some st, [], cachedMsgs, cachedOut, cachedHbs, none)
          | none => do
            let prefixCode ← TurboLean.ZygoteWorker.decodePayloadOrShm hexPrefix
            let bestAncestor? : Option (String × Command.State × List String × String × Nat) :=
              match prefixTreeByImport[importStubKey]? with
              | some entries =>
                entries.foldl (init := (none : Option (String × Command.State × List String × String × Nat)))
                  fun (best : Option (String × Command.State × List String × String × Nat))
                      (entry : String × Command.State × List String × String × Nat) =>
                    let (ancCode, ancSt, ancMsgs, ancOut, ancHbs) := entry
                    if !String.isEmpty ancCode && prefixCode.startsWith ancCode then
                      match best with
                      | some (bestCode, _, _, _, _) =>
                        if String.length ancCode >= String.length bestCode then
                          some (ancCode, ancSt, ancMsgs, ancOut, ancHbs)
                        else best
                      | none => some (ancCode, ancSt, ancMsgs, ancOut, ancHbs)
                    else best
              | none => none
            let deltaRes? ← match bestAncestor? with
              | some (prevCode, prevState, prevMsgs, prevOut, prevHbs) => do
                let deltaCode := (prefixCode.drop (String.length prevCode)).toString
                let (dOk, dUs, dHbs, _dNodes, _dErrs, dMsgs, dOut, _dUsed, dNextSt) ←
                  TurboLean.ZygoteWorker.runCommandsFromState prevState deltaCode fnPref prefAllowStub evalMode
                if dOk then
                  pure (some (false, dUs, some dNextSt, ([] : List String), prevMsgs ++ dMsgs, prevOut ++ dOut, prevHbs + dHbs, some prefixCode))
                else pure none
              | none => pure none
            match deltaRes? with
            | some res => pure res
            | none => do
              let opts : Options := if evalMode then
                  Elab.async.setIfNotSet (Lean.internal.cmdlineSnapshots.setIfNotSet {} true) true
                else {}
              let envForPref ← if evalMode then do
                  let mainMod ← TurboLean.ZygoteWorker.deriveEvalMainModule fnPref
                  pure (if mainMod.isAnonymous then baseEnv else baseEnv.setMainModule mainMod)
                else pure baseEnv
              let baseState := Command.mkState envForPref {} opts
              let (pOk, pUs, pHbs, _pNodes, pErrs, pMsgs, pOut, _pUsed, nextSt) ←
                TurboLean.ZygoteWorker.runCommandsFromState baseState prefixCode fnPref prefAllowStub evalMode
              if pOk then pure (false, pUs, some nextSt, [], pMsgs, pOut, pHbs, some prefixCode)
              else pure (false, pUs, none, pErrs, pMsgs, pOut, pHbs, some prefixCode)
        match ckptState? with
        | some ckptState =>
          if !prefixCacheHit then
            if stateCache.size >= maxCheckpoints then
              match stateCacheOrder[0]? with
              | some oldestKey =>
                stateCache := stateCache.erase oldestKey
                stateCacheOrder := stateCacheOrder.extract 1 stateCacheOrder.size
              | none => stateCache := {}
            stateCache := stateCache.insert fullPrefixKey (ckptState, prefMsgs, prefOut, prefHbs)
            stateCacheOrder := stateCacheOrder.push fullPrefixKey
            if let some pCode := decodedPrefix? then
              if prefixTreeByImport.size >= 24 && !prefixTreeByImport.contains importStubKey then
                prefixTreeByImport := {}
              let curTree := prefixTreeByImport[importStubKey]?.getD #[]
              let filteredTree := curTree.filter (fun (c, _, _, _, _) => c != pCode)
              let boundedTree := if filteredTree.size >= maxCheckpoints then
                  filteredTree.extract 1 filteredTree.size
                else filteredTree
              prefixTreeByImport := prefixTreeByImport.insert importStubKey
                (boundedTree.push (pCode, ckptState, prefMsgs, prefOut, prefHbs))
          let fn := customFileName?.getD "<zygote-decl>"
          let evalFromCkpt := fun (sc : String) => do
            let (ok, us, hbs, nodes, errs, msgs, outS, used, _) ←
              TurboLean.ZygoteWorker.runCommandsFromState ckptState sc fn allowStub false
            pure (ok, us, hbs, nodes, errs, msgs, outS, used)
          if isBatchFission then
            if hexSubs.isEmpty then
              TurboLean.ZygoteWorker.emitZygoteReply stdout true none kgActive true envCacheHit prefixCacheHit importUs prefixUs 0 prefHbs 0 0 prefOut prefMsgs [] []
            else
              let (bOk, bElabUs, bHbs, bNodes, bVer, bOut, bMsgs, bErrs, bUsed) ←
                TurboLean.ZygoteWorker.runBatchFissionSubs hexSubs evalFromCkpt
              TurboLean.ZygoteWorker.emitZygoteReply stdout bOk none kgActive true envCacheHit prefixCacheHit importUs prefixUs bElabUs bHbs bNodes bVer bOut bMsgs bErrs bUsed
          else if isRaceCandidates then
            if hexSubs.isEmpty then
              TurboLean.ZygoteWorker.emitZygoteReply stdout false (some "null") kgActive true envCacheHit prefixCacheHit importUs prefixUs 0 prefHbs 0 0 prefOut prefMsgs [] []
            else
              let (rOk, winIdx, rElabUs, rHbs, rNodes, rVer, rOut, rMsgs, rErrs, rUsed) ←
                TurboLean.ZygoteWorker.runRaceCandidatesSubs hexSubs evalFromCkpt
              TurboLean.ZygoteWorker.emitZygoteReply stdout rOk (some winIdx) kgActive true envCacheHit prefixCacheHit importUs prefixUs rElabUs rHbs rNodes rVer rOut rMsgs rErrs rUsed
          else if bodyCode.trimAscii.toString.isEmpty then
            TurboLean.ZygoteWorker.emitZygoteReply stdout true none kgActive true envCacheHit prefixCacheHit importUs prefixUs 0 prefHbs 0 1 prefOut prefMsgs [] []
          else
            let (ok, elabUs, dHbs, ptNodes, errs, dMsgs, dOut, usedConsts, _) ←
              TurboLean.ZygoteWorker.runCommandsFromState ckptState bodyCode fn allowStub evalMode
            let finalMsgs := if evalMode then prefMsgs ++ dMsgs else dMsgs
            let finalOut := if evalMode then prefOut ++ dOut else dOut
            let finalHbs := if evalMode then prefHbs + dHbs else dHbs
            TurboLean.ZygoteWorker.emitZygoteReply stdout ok none kgActive true envCacheHit prefixCacheHit importUs prefixUs elabUs finalHbs ptNodes (if ok then 1 else 0) finalOut finalMsgs errs usedConsts
        | none =>
          -- Fallback: if prefix failed on its own (e.g. split mid-command or error in prefix), elaborate combined prefix + body from baseEnv
          let prefixCode := decodedPrefix?.getD (TurboLean.ZygoteWorker.decodeHexToString hexPrefix)
          let fn := customFileName?.getD "<zygote-shard>"
          let evalCombined := fun (sc : String) =>
            TurboLean.ZygoteWorker.checkShardWithEnv baseEnv (prefixCode ++ "\n" ++ sc) allowStub false fn
          if isBatchFission then
            if hexSubs.isEmpty then
              TurboLean.ZygoteWorker.emitZygoteReply stdout false none kgActive true envCacheHit false importUs prefixUs 0 prefHbs 0 0 prefOut prefMsgs prefErrs []
            else
              let (bOk, bElabUs, bHbs, bNodes, bVer, bOut, bMsgs, bErrs, bUsed) ←
                TurboLean.ZygoteWorker.runBatchFissionSubs hexSubs evalCombined
              TurboLean.ZygoteWorker.emitZygoteReply stdout bOk none kgActive true envCacheHit false importUs prefixUs bElabUs bHbs bNodes bVer bOut bMsgs bErrs bUsed
          else if isRaceCandidates then
            if hexSubs.isEmpty then
              TurboLean.ZygoteWorker.emitZygoteReply stdout false (some "null") kgActive true envCacheHit false importUs prefixUs 0 prefHbs 0 0 prefOut prefMsgs prefErrs []
            else
              let (rOk, winIdx, rElabUs, rHbs, rNodes, rVer, rOut, rMsgs, rErrs, rUsed) ←
                TurboLean.ZygoteWorker.runRaceCandidatesSubs hexSubs evalCombined (!prefErrs.isEmpty)
              TurboLean.ZygoteWorker.emitZygoteReply stdout rOk (some winIdx) kgActive true envCacheHit false importUs prefixUs rElabUs rHbs rNodes rVer rOut rMsgs rErrs rUsed
          else if bodyCode.trimAscii.toString.isEmpty then
            TurboLean.ZygoteWorker.emitZygoteReply stdout false none kgActive true envCacheHit false importUs prefixUs 0 prefHbs 0 0 prefOut prefMsgs prefErrs []
          else
            let prefNewlines := prefixCode.toList.filter (· == '\n') |>.length
            let rest := (bodyCode.drop prefNewlines).toString
            let combined := if prefixCode.endsWith "\n" then prefixCode ++ rest else prefixCode ++ "\n" ++ rest
            let (ok, elabUs, hbs, ptNodes, errs, msgs, capOut, usedConsts) ←
              TurboLean.ZygoteWorker.checkShardWithEnv baseEnv combined allowStub evalMode fn
            TurboLean.ZygoteWorker.emitZygoteReply stdout ok none kgActive true envCacheHit false importUs prefixUs elabUs hbs ptNodes (if ok then 1 else 0) capOut msgs errs usedConsts
    | none =>
      let rawErr := envErr?.getD "importModules failed"
      let formattedErr := match customFileName? with
        | some fn => if evalMode && !rawErr.startsWith fn then s!"{fn}:1:0: error: {rawErr}\n" else rawErr
        | none => rawErr
      TurboLean.ZygoteWorker.emitZygoteReply stdout false none false false false false importUs 0 0 0 0 0 "" [formattedErr] [formattedErr] []
    try IO.Process.setCurrentDir initCwd catch _ => pure ()

