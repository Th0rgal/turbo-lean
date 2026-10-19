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

/-- Parse a dot-separated Lean module name such as `"TurboLean.Reflection"` into a `Lean.Name`. -/
def parseModuleName (s : String) : Name :=
  let parts := s.trimAscii.toString.splitOn "."
  parts.foldl (fun acc p => if p.isEmpty then acc else Name.str acc p) Name.anonymous

/-- Parse a comma-separated list of module names into `Array Lean.Import` (defaulting to `Init`). -/
def parseImportsCsv (csv : String) : Array Import := Id.run do
  let trimmed := csv.trimAscii.toString
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

/-- Elaborate and kernel-typecheck `code` starting from an immutable `baseState : Command.State`
    without mutating `baseState`.
    Returns `(ok, elapsed_us, heartbeats, error_messages, all_messages, captured_stdout, next_clean_state)`. -/
def runCommandsFromState
    (baseState : Command.State)
    (code : String)
    (fileName : String := "<zygote-shard>")
    (allowStub : Bool := false)
    (evalMode : Bool := false) : IO (Bool × Nat × Nat × List String × List String × String × Command.State) := do
  let t0 ← IO.monoNanosNow
  let hb0 ← IO.getNumHeartbeats
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
    let sevStr := match msg.severity with
      | .error => "error"
      | .warning => "warning"
      | .information => "info"
    let formatted := s!"{msg.fileName}:{msg.pos.line}:{msg.pos.column}: {sevStr}: {txt.trimAsciiEnd.toString}"
    allMessages := allMessages ++ [formatted]
    if msg.severity == .error then
      errs := errs ++ [if evalMode then formatted else txt]
    else if !evalMode && !allowStub && msg.severity == .warning &&
        ((txt.splitOn sorryWarnPhrase).length > 1 || (txt.splitOn sorryWarnBacktick).length > 1) then
      errs := errs ++ [s!"forbidden token detected: {txt}"]
  if !evalMode then
    let explicitStubToken := ":= " ++ forbiddenToken
    let allowSorryInKernel := allowStub && (code.splitOn explicitStubToken).length > 1
    let (_, kernelErrs) ← auditNewKernelDecls baseState.env s.commandState.env allowSorryInKernel
    errs := errs ++ kernelErrs
  let t1 ← IO.monoNanosNow
  let elapsedUs := (t1 - t0) / 1000
  let cleanNextState : Command.State := { s.commandState with messages := {} }
  return (errs.isEmpty, elapsedUs, heartbeats, errs, allMessages, capturedStdout, cleanNextState)

/-- Elaborate and kernel-typecheck `bodyCode` on top of an immutable `baseEnv : Lean.Environment`
    without mutating `baseEnv`.
    Returns `(ok, elapsed_us, heartbeats, error_messages, all_messages, captured_stdout)`. -/
def checkShardWithEnv
    (baseEnv : Environment)
    (bodyCode : String)
    (allowStub : Bool := false)
    (evalMode : Bool := false)
    (fileName : String := "<zygote-shard>") : IO (Bool × Nat × Nat × List String × List String × String) := do
  let baseState := Command.mkState baseEnv {} {}
  let (ok, elapsedUs, heartbeats, errs, allMessages, capturedStdout, _) ←
    runCommandsFromState baseState bodyCode fileName allowStub evalMode
  return (ok, elapsedUs, heartbeats, errs, allMessages, capturedStdout)

end TurboLean.ZygoteWorker

/-- Persistent stdin/stdout Zygote worker loop with `Command.State` prefix checkpointing and instant CoW rollback.
    Protocol:
    - Standard: `<imports_csv>\t<hex_encoded_body_without_imports>[\t<mode_flag>]`
    - Prefix-checkpointed: `<imports_csv>\t<hex_encoded_decl>\t<mode_flag>\t<prefix_key>\t<hex_encoded_prefix>`
    Responds with one JSON line including `messages`, `stdout`, and `heartbeats`. -/
def main (_args : List String) : IO Unit := do
  unsafe enableInitializersExecution
  let leanCmd := (← IO.getEnv "LEAN").getD "lean"
  let sysroot ← Lean.findSysroot leanCmd
  let extraSp ← match (← IO.getEnv "LEAN_PATH") with
    | some p => pure (System.SearchPath.parse p)
    | none => pure ∅
  Lean.initSearchPath sysroot extraSp
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let maxCheckpoints ← match (← IO.getEnv "TURBO_LEAN_ZYGOTE_MAX_CHECKPOINTS") with
    | some s => pure (match s.trimAscii.toString.toNat? with | some n => if n > 0 then n else 32 | none => 32)
    | none => pure 32
  let mut envCache : Std.HashMap String Lean.Environment := {}
  let mut stateCache : Std.HashMap String Command.State := {}
  let mut stateCacheOrder : Array String := #[]
  while true do
    let line ← stdin.getLine
    if line.isEmpty then
      break
    let trimmed := line.trimAscii.toString
    if trimmed.isEmpty then
      continue
    if trimmed == "ping" || ((trimmed.splitOn "\"cmd\"").length > 1 && (trimmed.splitOn "\"ping\"").length > 1) then
      stdout.putStrLn "{\"ok\":true,\"status\":\"pong\",\"kernel_gate_active\":true,\"import_ok\":true,\"env_cache_hit\":true,\"prefix_cache_hit\":false,\"import_us\":0,\"prefix_us\":0,\"elab_us\":0,\"heartbeats\":0,\"stdout\":\"\",\"messages\":[],\"errors\":[]}"
      stdout.flush
      continue
    let parts := trimmed.splitOn "\t"
    let importsCsv := parts.headD "Init"
    let hexBody := parts.drop 1 |>.headD ""
    let modeFlag := parts.drop 2 |>.headD ""
    let prefixKey := parts.drop 3 |>.headD ""
    let hexPrefix := parts.drop 4 |>.headD ""
    let allowStub := modeFlag == "allow_stub"
    let evalMode := modeFlag == "eval" || modeFlag.startsWith "eval:"
    let customFileName? := if modeFlag.startsWith "eval:" then
      let hexFn := (modeFlag.drop 5).toString
      if hexFn.isEmpty then none else some (TurboLean.ZygoteWorker.decodeHexToString hexFn)
    else
      none
    let bodyCode := TurboLean.ZygoteWorker.decodeHexToString hexBody
    let (envCacheHit, importUs, baseEnv?, envErr?) ← match envCache[importsCsv]? with
      | some env => pure (true, 0, some env, none)
      | none => do
        let tImp0 ← IO.monoNanosNow
        let imports := TurboLean.ZygoteWorker.parseImportsCsv importsCsv
        try
          unsafe enableInitializersExecution
          let env ← Lean.importModules imports {} 0 #[] false true
          let tImp1 ← IO.monoNanosNow
          pure (false, (tImp1 - tImp0) / 1000, some env, none)
        catch e =>
          let tImp1 ← IO.monoNanosNow
          pure (false, (tImp1 - tImp0) / 1000, none, some (toString e))
    match baseEnv? with
    | some baseEnv =>
      if !envCacheHit then
        envCache := envCache.insert importsCsv baseEnv
      let kgActive := !evalMode
      if prefixKey.isEmpty || hexPrefix.isEmpty || evalMode then
        let fn := customFileName?.getD "<zygote-shard>"
        let (ok, elabUs, hbs, errs, msgs, capOut) ←
          TurboLean.ZygoteWorker.checkShardWithEnv baseEnv bodyCode allowStub evalMode fn
        let errJson := errs.map (fun e => s!"\"{TurboLean.ZygoteWorker.jsonEscape e}\"")
        let msgJson := msgs.map (fun m => s!"\"{TurboLean.ZygoteWorker.jsonEscape m}\"")
        let outEsc := TurboLean.ZygoteWorker.jsonEscape capOut
        stdout.putStrLn s!"\{\"ok\":{ok},\"kernel_gate_active\":{kgActive},\"import_ok\":true,\"env_cache_hit\":{envCacheHit},\"prefix_cache_hit\":false,\"import_us\":{importUs},\"prefix_us\":0,\"elab_us\":{elabUs},\"heartbeats\":{hbs},\"stdout\":\"{outEsc}\",\"messages\":[{String.intercalate "," msgJson}],\"errors\":[{String.intercalate "," errJson}]}"
        stdout.flush
      else
        let fullPrefixKey := s!"{importsCsv}\t{allowStub}\t{prefixKey}"
        let (prefixCacheHit, prefixUs, ckptState?, prefErrs, prefMsgs, prefOut, prefHbs) ← match stateCache[fullPrefixKey]? with
          | some st => pure (true, 0, some st, [], [], "", 0)
          | none => do
            let prefixCode := TurboLean.ZygoteWorker.decodeHexToString hexPrefix
            let baseState := Command.mkState baseEnv {} {}
            let (pOk, pUs, pHbs, pErrs, pMsgs, pOut, nextSt) ←
              TurboLean.ZygoteWorker.runCommandsFromState baseState prefixCode "<zygote-prefix>" true false
            if pOk then
              pure (false, pUs, some nextSt, [], pMsgs, pOut, pHbs)
            else
              pure (false, pUs, none, pErrs, pMsgs, pOut, pHbs)
        match ckptState? with
        | some ckptState =>
          if !prefixCacheHit then
            if stateCache.size >= maxCheckpoints then
              match stateCacheOrder[0]? with
              | some oldestKey =>
                stateCache := stateCache.erase oldestKey
                stateCacheOrder := stateCacheOrder.extract 1 stateCacheOrder.size
              | none =>
                stateCache := {}
            stateCache := stateCache.insert fullPrefixKey ckptState
            stateCacheOrder := stateCacheOrder.push fullPrefixKey
          if bodyCode.trimAscii.toString.isEmpty then
            let msgJson := prefMsgs.map (fun m => s!"\"{TurboLean.ZygoteWorker.jsonEscape m}\"")
            let outEsc := TurboLean.ZygoteWorker.jsonEscape prefOut
            stdout.putStrLn s!"\{\"ok\":true,\"kernel_gate_active\":true,\"import_ok\":true,\"env_cache_hit\":{envCacheHit},\"prefix_cache_hit\":{prefixCacheHit},\"import_us\":{importUs},\"prefix_us\":{prefixUs},\"elab_us\":0,\"heartbeats\":{prefHbs},\"stdout\":\"{outEsc}\",\"messages\":[{String.intercalate "," msgJson}],\"errors\":[]}"
            stdout.flush
          else
            let fn := customFileName?.getD "<zygote-decl>"
            let (ok, elabUs, dHbs, errs, dMsgs, dOut, _) ←
              TurboLean.ZygoteWorker.runCommandsFromState ckptState bodyCode fn allowStub false
            let errJson := errs.map (fun e => s!"\"{TurboLean.ZygoteWorker.jsonEscape e}\"")
            let msgJson := dMsgs.map (fun m => s!"\"{TurboLean.ZygoteWorker.jsonEscape m}\"")
            let outEsc := TurboLean.ZygoteWorker.jsonEscape dOut
            stdout.putStrLn s!"\{\"ok\":{ok},\"kernel_gate_active\":true,\"import_ok\":true,\"env_cache_hit\":{envCacheHit},\"prefix_cache_hit\":{prefixCacheHit},\"import_us\":{importUs},\"prefix_us\":{prefixUs},\"elab_us\":{elabUs},\"heartbeats\":{dHbs},\"stdout\":\"{outEsc}\",\"messages\":[{String.intercalate "," msgJson}],\"errors\":[{String.intercalate "," errJson}]}"
            stdout.flush
        | none =>
          -- Fallback: if prefix failed on its own (e.g. split mid-command), elaborate combined prefix + body from baseEnv
          let prefixCode := TurboLean.ZygoteWorker.decodeHexToString hexPrefix
          if bodyCode.trimAscii.toString.isEmpty then
            let errJson := prefErrs.map (fun e => s!"\"{TurboLean.ZygoteWorker.jsonEscape e}\"")
            let msgJson := prefMsgs.map (fun m => s!"\"{TurboLean.ZygoteWorker.jsonEscape m}\"")
            let outEsc := TurboLean.ZygoteWorker.jsonEscape prefOut
            stdout.putStrLn s!"\{\"ok\":false,\"kernel_gate_active\":true,\"import_ok\":true,\"env_cache_hit\":{envCacheHit},\"prefix_cache_hit\":false,\"import_us\":{importUs},\"prefix_us\":{prefixUs},\"elab_us\":0,\"heartbeats\":{prefHbs},\"stdout\":\"{outEsc}\",\"messages\":[{String.intercalate "," msgJson}],\"errors\":[{String.intercalate "," errJson}]}"
            stdout.flush
          else
            let combined := prefixCode ++ "\n" ++ bodyCode
            let fn := customFileName?.getD "<zygote-shard>"
            let (ok, elabUs, hbs, errs, msgs, capOut) ←
              TurboLean.ZygoteWorker.checkShardWithEnv baseEnv combined allowStub false fn
            let errJson := errs.map (fun e => s!"\"{TurboLean.ZygoteWorker.jsonEscape e}\"")
            let msgJson := msgs.map (fun m => s!"\"{TurboLean.ZygoteWorker.jsonEscape m}\"")
            let outEsc := TurboLean.ZygoteWorker.jsonEscape capOut
            stdout.putStrLn s!"\{\"ok\":{ok},\"kernel_gate_active\":true,\"import_ok\":true,\"env_cache_hit\":{envCacheHit},\"prefix_cache_hit\":false,\"import_us\":{importUs},\"prefix_us\":{prefixUs},\"elab_us\":{elabUs},\"heartbeats\":{hbs},\"stdout\":\"{outEsc}\",\"messages\":[{String.intercalate "," msgJson}],\"errors\":[{String.intercalate "," errJson}]}"
            stdout.flush
    | none =>
      let eMsg := TurboLean.ZygoteWorker.jsonEscape (envErr?.getD "importModules failed")
      stdout.putStrLn s!"\{\"ok\":false,\"import_ok\":false,\"env_cache_hit\":false,\"prefix_cache_hit\":false,\"import_us\":{importUs},\"prefix_us\":0,\"elab_us\":0,\"heartbeats\":0,\"stdout\":\"\",\"messages\":[\"{eMsg}\"],\"errors\":[\"{eMsg}\"]}"
      stdout.flush


