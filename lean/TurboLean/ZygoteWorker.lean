/-
  TurboLean.ZygoteWorker: Persistent In-Memory `Lean.Environment` Zygote Worker
  Caches imported `Lean.Environment` instances in an in-memory `Std.HashMap String Environment`
  keyed by the comma-separated module import list. Because `Lean.Environment` is a persistent
  functional data structure in Lean 4, each incoming theorem shard elaborates and kernel-checks
  against `baseEnv` via `Lean.Elab.IO.processCommands` in ~1.5–25 ms with 0.00 ms of `.olean`
  reload or process startup overhead, leaving `baseEnv` completely unmutated.
-/
import Lean.Elab.Frontend
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
import TurboLean.ZygoteWorker.Compiler
import TurboLean.ZygoteWorker.Hotspots

open Lean Elab


/-- Persistent stdin/stdout Zygote worker loop with `Command.State` prefix checkpointing,
    incremental delta-prefix chaining, and instant CoW rollback.
    Protocol:
    - Standard: `<imports_csv>\t<hex_encoded_body_without_imports>[\t<mode_flag>]`
    - Prefix-checkpointed: `<imports_csv>\t<hex_encoded_decl>\t<mode_flag>\t<prefix_key>\t<hex_encoded_prefix>`
    Responds with one JSON line including `messages`, `stdout`, `heartbeats`, and `used_constants`. -/
def main (args : List String) : IO Unit := do
  let initCwd ← IO.currentDir
  let leanCmd := (← IO.getEnv "LEAN").getD "lean"
  let sysroot ← Lean.findSysroot leanCmd
  Lean.initSearchPath sysroot
  let cadical := (sysroot / "bin" / "cadical").withExtension System.FilePath.exeExtension
  if ← cadical.pathExists then TurboLean.ZygoteWorker.satSolverRef.set cadical.toString
  let sp ← Lean.searchPathRef.get
  let mut dedupSp : System.SearchPath := []
  for p in sp do
    if !dedupSp.contains p then
      dedupSp := dedupSp ++ [p]
  Lean.searchPathRef.set dedupSp
  match args with
  | ["--kernel-replay-module", moduleName] =>
    TurboLean.ZygoteWorker.replayAuditedModule (TurboLean.ZygoteWorker.parseModuleName moduleName)
    return
  | ["--verify-proof-irrelevant-olean-update", moduleName, oldPath, newPath] =>
    TurboLean.ZygoteWorker.verifyProofIrrelevantOleanUpdate
      (TurboLean.ZygoteWorker.parseModuleName moduleName)
      (System.FilePath.mk oldPath)
      (System.FilePath.mk newPath)
    return
  | "--kernel-replay-closure" :: moduleNames =>
    if moduleNames.isEmpty then
      throw <| IO.userError "--kernel-replay-closure requires at least one module"
    let parsed := moduleNames.toArray.map TurboLean.ZygoteWorker.parseModuleName
    TurboLean.ZygoteWorker.replayAuditedModuleClosure parsed
    return
  | "--audit-modules" :: modArgs =>
    let stdout ← IO.getStdout
    let (ffiArgs, rest) := modArgs.partition (·.startsWith "--ffi-allow=")
    let (stubArgs, rest) := rest.partition (·.startsWith "--stub-ok=")
    let (fastMapArgs, rest) := rest.partition (·.startsWith "--fast-map=")
    let (allowSorryFlags, rest) := rest.partition (· == "--allow-sorry")
    let (skipReplayFlags, rest) := rest.partition (· == "--skip-child-replay")
    let (importAuditFlags, rest) := rest.partition (· == "--audit-imports")
    let isImportAudit := !importAuditFlags.isEmpty
    let (shardFlag, mods) := rest.partition (· == "--shard")
    let allowSorry := !allowSorryFlags.isEmpty
    let ffiAllow := ffiArgs.toArray.filterMap fun a =>
      match ((a.drop 12).toString.splitOn "=") with
      | [m, d, sym] => some (TurboLean.ZygoteWorker.parseModuleName m, TurboLean.ZygoteWorker.parseModuleName d, sym)
      | _ => none
    let fastMapOpt : Option (List (String × String)) := Id.run do
      let mut out : List (String × String) := []
      for a in fastMapArgs do
        match ((a.drop 11).toString.splitOn ":") with
        | [ho, hg] =>
          let o := TurboLean.ZygoteWorker.decodeHexToString ho
          let g := TurboLean.ZygoteWorker.decodeHexToString hg
          if o.isEmpty || g.isEmpty then return none
          out := (o, g) :: out
        | _ => return none
      return some out.reverse
    let audited := mods.filter (!·.trimAscii.isEmpty)
    -- `--shard` audits exactly one compiled shard module, exempting validated `--stub-ok=` prefix
    -- stubs and reporting its theorems; stubs are never exempt in whole-module audits.
    let (ok, violations, decls, declTypes, sorryDecls, csimpEntries) ← match shardFlag.isEmpty, audited, fastMapOpt with
      | true, _, _ =>
        if stubArgs.isEmpty && fastMapArgs.isEmpty then
          let (ok, vs, cs) ← TurboLean.ZygoteWorker.auditCompiledModules mods ffiAllow (!skipReplayFlags.isEmpty) allowSorry isImportAudit
          pure (ok, vs, none, none, [], cs)
        else pure (false, ["[TurboLean.KernelGate] --stub-ok / --fast-map requires --shard"], none, none, [], [])
      | false, _, none =>
        pure (false, ["[TurboLean.KernelGate] malformed --fast-map argument"], none, none, [], [])
      | false, [m], some fmap =>
        if !skipReplayFlags.isEmpty then
          pure (false, ["[TurboLean.KernelGate] --skip-child-replay forbidden with --shard"], none, none, [], [])
        else
          let nm := TurboLean.ZygoteWorker.parseModuleName m.trimAscii.toString
          let (vs, ds, dts, sds, cs) ← TurboLean.ZygoteWorker.auditShardModule (m.trimAscii.toString, nm) ffiAllow
            (stubArgs.toArray.map fun a => (a.drop 10).toString) fmap allowSorry
          pure (vs.isEmpty && !nm.isAnonymous, vs, some ds, some dts, sds, cs)
      | false, _, _ => pure (false, ["[TurboLean.KernelGate] --shard audits exactly one module"], none, none, [], [])
    let ok := ok && ffiAllow.size == ffiArgs.length
    let declsJson := match decls with
      | some ds => s!",\"decls\":[{TurboLean.ZygoteWorker.jsonStrList ds.toList}]"
      | none => ""
    let declTypesJson := match declTypes with
      | some dts => s!",\"decl_types\":\{{TurboLean.ZygoteWorker.jsonKvObj dts}}"
      | none => ""
    let sorryJson := if sorryDecls.isEmpty then ""
      else s!",\"used_sorry\":true,\"sorry_decls\":[{TurboLean.ZygoteWorker.jsonStrList sorryDecls}]"
    let csimpJson := if csimpEntries.isEmpty then ""
      else
        let items := csimpEntries.map fun (t, f, r) =>
          s!"[\"{TurboLean.ZygoteWorker.jsonEscape t}\",\"{TurboLean.ZygoteWorker.jsonEscape f}\",\"{TurboLean.ZygoteWorker.jsonEscape r}\"]"
        s!",\"csimp_entries\":[{String.intercalate "," items}]"
    stdout.putStrLn s!"\{\"ok\":{ok},\"audited\":[{TurboLean.ZygoteWorker.jsonStrList audited}],\"violations\":[{TurboLean.ZygoteWorker.jsonStrList violations}]{declsJson}{declTypesJson}{sorryJson}{csimpJson}}"
    stdout.flush
    if !ok then
      IO.Process.exit 1
    return
  | "--statement-dump" :: mods =>
    statementHashCliMain mods
    return
  | ["--public-sig", mod] =>
    let j ← TurboLean.ZygoteWorker.dumpPublicSignatureJson mod
    IO.println j
    return
  -- Declaration identity: read the theorems (and their canonical `statement-v1` kernel type hashes)
  -- a compiled probe declares within `[minLine, maxLine]` from its `.olean` (data only,
  -- initializers disabled), never from output the probe controls.
  | ["--decl-identity", mod, minLineStr, maxLineStr] =>
    let nm := TurboLean.ZygoteWorker.parseModuleName mod
    let env ← Lean.importModules #[{ module := nm, importAll := true }] {} 0 #[] true false .private
    let some idx := env.getModuleIdx? nm | throw (IO.userError s!"module `{mod}` not imported")
    let some minLine := minLineStr.trimAscii.toString.toNat? | throw (IO.userError s!"invalid minLine `{minLineStr}`")
    let some maxLine := maxLineStr.trimAscii.toString.toNat? | throw (IO.userError s!"invalid maxLine `{maxLineStr}`")
    let entries := (env.header.moduleData[idx.toNat]!.constants).filterMap fun c =>
      if c matches .thmInfo _ then
        (Lean.declRangeExt.find? (level := .server) env c.name).bind fun r =>
          let ln := r.selectionRange.pos.line
          if ln ≥ minLine && ln ≤ maxLine then
            let userNm := TurboLean.ZygoteWorker.canonicalName (Lean.privateToUserName c.name)
            let th := TurboLean.ZygoteWorker.kernelStatementHash c (some nm)
            some s!"\{\"name\":\"{TurboLean.ZygoteWorker.jsonEscape userNm}\",\"type_hash\":\"{TurboLean.ZygoteWorker.jsonEscape th}\",\"line\":{ln}}"
          else none
      else none
    IO.println s!"\{\"decls\":[{String.intercalate "," entries.toList}]}"
    return
  | _ => pure ()
  try discard <| Lake.importModulesUsingCache #[{ module := .anonymous }] {} 0 catch _ => pure ()
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let maxCheckpoints ← match (← IO.getEnv "TURBO_LEAN_ZYGOTE_MAX_CHECKPOINTS") with
    | some s => pure (match s.trimAscii.toString.toNat? with | some n => if n > 0 then n else 32 | none => 32)
    | none => pure 32
  let maxEnvCache : Nat := 16
  -- Envs are cached only under a host-supplied closure digest: the host re-reads the closure
  -- after each import and kills this worker unless the digest provably labels the bytes read.
  let mut envCache : Std.HashMap String (String × Lean.Environment) := {}
  let mut envCacheOrder : Array String := #[]
  let mut stateCache : Std.HashMap String (String × Command.State × List String × String × Nat) := {}
  let mut stateCacheOrder : Array String := #[]
  let mut compactCache : Std.HashMap String Environment := {}
  let mut compactOrder : Array String := #[]
  let mut prefixTreeByImport : Std.HashMap String (Array (String × Command.State × List String × String × Nat)) := {}
  -- Environment extensions registered by one import set are not safe to reuse through a
  -- different cached environment. Bind this process to the first `importsCsv` it serves.
  let mut boundImports? : Option String := none
  let mut poisoned := false
  let mut clones : Array UInt32 := #[]
  while true do
    let line ← stdin.getLine
    if line.isEmpty || line.trimAscii.toString == "shutdown" then
      clones ← TurboLean.ZygoteFork.reapClones clones
      for pid in clones do TurboLean.ZygoteFork.posixKillSigkill pid
      for pid in clones do discard <| TurboLean.ZygoteFork.posixWaitPid pid
      break
    let trimmed := line.trimAscii.toString
    if trimmed.isEmpty then
      continue
    if trimmed.startsWith "fork_clone:" then
      if poisoned || envCache.isEmpty || !(← TurboLean.ZygoteFork.isForkEnabled) then
        stdout.putStrLn "unavailable"
      else
        try
          stdout.flush
          clones ← TurboLean.ZygoteFork.reapClones clones
          TurboLean.ZygoteFork.finalizeTaskManager
          let pid ← try TurboLean.ZygoteFork.posixForkRaw catch e =>
            TurboLean.ZygoteFork.initTaskManager
            throw e
          if pid == 0 then
            clones := #[]
            let path := (trimmed.drop 11).toString
            try
              TurboLean.ZygoteFork.connectCloneChannel path 0
              TurboLean.ZygoteFork.connectCloneChannel (path ++ ".err") 2
              TurboLean.ZygoteFork.initTaskManagerUsing 2
            catch _ => TurboLean.ZygoteFork.posixExitImmediate 1
          else
            clones := clones.push pid
            TurboLean.ZygoteFork.initTaskManager
            stdout.putStrLn s!"clone {pid}"
        catch _ => stdout.putStrLn "unavailable"
      stdout.flush
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
    let (hexBody, rawModeFlag, prefixKey, hexPrefix) :=
      if raw1 == "batch_fission" || raw1.startsWith "batch_fission" ||
         raw1 == "race_candidates" || raw1.startsWith "race_candidates" then
        (parts.drop 4 |>.headD "", raw1, raw2, parts.drop 3 |>.headD "")
      else
        (raw1, raw2, parts.drop 3 |>.headD "", parts.drop 4 |>.headD "")
    let allowSorry := rawModeFlag == "allow_sorry" || rawModeFlag.startsWith "allow_sorry+"
    let modeFlag := if rawModeFlag == "allow_sorry" then "strict_all"
      else if rawModeFlag.startsWith "allow_sorry+" then (rawModeFlag.drop 12).toString
      else rawModeFlag
    let isDiagnoseHotspots := modeFlag == "diagnose_hotspots" || modeFlag.startsWith "diagnose_hotspots:"
    let hexOpts := parts.drop 5 |>.headD ""
    let hostClosureDigest := (parts.drop 6 |>.headD "").trimAscii.toString
    let encodedLeanArgs := if hexOpts.isEmpty then "" else TurboLean.ZygoteWorker.decodeHexToString hexOpts
    let isBatchFission := modeFlag == "batch_fission" || modeFlag.startsWith "batch_fission"
    let isRaceCandidates := modeFlag == "race_candidates" || modeFlag.startsWith "race_candidates"
    let (stubTargets, stubs, requiredTargets, fastMapOpt) := if modeFlag.startsWith "allow_stub:" ||
          modeFlag.startsWith "strict:" ||
          modeFlag.startsWith "batch_fission:" || modeFlag.startsWith "race_candidates:" then
        let rawCols := (modeFlag.splitOn ":").drop 1
        let lists := rawCols.map fun h =>
          ((TurboLean.ZygoteWorker.decodeHexToString h).splitOn "\n").filter (!·.isEmpty)
        let req := if modeFlag.startsWith "allow_stub:" || modeFlag.startsWith "strict:" then
            if rawCols.length > 2 then (lists.drop 2).headD [] else lists.headD []
          else []
        let fmapLines := if rawCols.length > 3 then (lists.drop 3).headD [] else []
        let fmapParsed : Option (List (String × String)) := Id.run do
          let mut out : List (String × String) := []
          for ln in fmapLines do
            match ln.splitOn "\t" with
            | [o, g] =>
              if o.isEmpty || g.isEmpty then return none
              out := (o, g) :: out
            | _ => return none
          return some out.reverse
        (lists.headD [], (lists.drop 1).headD [], req, fmapParsed)
      else ([], [], [], some [])
    let isProbeStub := modeFlag == "probe_stub"
    let isEmitOutline := modeFlag.startsWith "emit_outline_olean:"
    let allowStub := modeFlag == "allow_stub" || modeFlag.startsWith "allow_stub:" || isProbeStub || isEmitOutline ||
      ((modeFlag.startsWith "batch_fission:" || modeFlag.startsWith "race_candidates:") && !stubs.isEmpty)
    let evalMode := modeFlag == "eval" || modeFlag.startsWith "eval:"
    -- `strict_all`: no `sorry` stub is exempt anywhere, prefix checkpoints included (whole-file audits).
    let strictAll := modeFlag == "strict_all" || modeFlag.startsWith "strict_all:"
    let (customFileName?, customCwd?, emitOlean?) := if modeFlag.startsWith "eval:" || modeFlag.startsWith "strict_all:" || modeFlag.startsWith "diagnose_hotspots:" then
      let pfxLen := if modeFlag.startsWith "eval:" then 5 else if modeFlag.startsWith "strict_all:" then 11 else 18
      let metaParts := ((modeFlag.drop pfxLen).toString).splitOn ":"
      let hexFn := metaParts.headD ""
      let hexCwd := metaParts.drop 1 |>.headD ""
      let fnOpt := if hexFn.isEmpty then none else some (TurboLean.ZygoteWorker.decodeHexToString hexFn)
      let cwdOpt := if hexCwd.isEmpty then none else some (TurboLean.ZygoteWorker.decodeHexToString hexCwd)
      (fnOpt, cwdOpt, none)
    else if modeFlag.startsWith "emit_olean:" || isEmitOutline then
      let pfxLen := if isEmitOutline then 19 else 11
      let metaParts := ((modeFlag.drop pfxLen).toString).splitOn ":"
      let modStr := TurboLean.ZygoteWorker.decodeHexToString (metaParts.headD "")
      let oleanStr := TurboLean.ZygoteWorker.decodeHexToString (metaParts.drop 1 |>.headD "")
      let hexFn := metaParts.drop 2 |>.headD ""
      let fnOpt := if hexFn.isEmpty then none else some (TurboLean.ZygoteWorker.decodeHexToString hexFn)
      let modName := TurboLean.ZygoteWorker.parseModuleName modStr
      let emitOpt := if oleanStr.isEmpty then none else some (modName, System.FilePath.mk oleanStr)
      (fnOpt, none, emitOpt)
    else
      (none, none, none)
    let (stubs, stubTargets, requiredTargets) := if isEmitOutline then
      let metaParts := ((modeFlag.drop 19).toString).splitOn ":"
      let hexStubs := metaParts.drop 3 |>.headD ""
      let outlineStubs := if hexStubs.isEmpty then [] else
        (TurboLean.ZygoteWorker.decodeHexToString hexStubs).splitOn "\n" |>.filter (fun x => !x.isEmpty)
      (outlineStubs, ([] : List String), ([] : List String))
    else
      (stubs, stubTargets, requiredTargets)
    let targetCwd : System.FilePath := match customCwd? with
      | some c => if c.isEmpty then initCwd else System.FilePath.mk c
      | none => initCwd
    try IO.Process.setCurrentDir targetCwd catch _ => pure ()
    let bodyCode := if isBatchFission || isRaceCandidates then "" else TurboLean.ZygoteWorker.decodeHexToString hexBody
    let hexSubs := if isBatchFission || isRaceCandidates then (hexBody.splitOn ",").filter (fun s => !s.isEmpty) else []
    let (imports, isMod, isHeaderErr) := TurboLean.ZygoteWorker.parseImportsCsvSpec importsCsv
    if poisoned then
      let panicErr := TurboLean.ZygoteWorker.runtimePanicErr
      TurboLean.ZygoteWorker.emitZygoteReply stdout false none false false false false 0 0 0 0 0 0 "" [panicErr] [panicErr] []
      try IO.Process.setCurrentDir initCwd catch _ => pure ()
      continue
    if boundImports?.isSome && boundImports? != some importsCsv then
      let mismatchErr := s!"[TurboLean.ZygoteWorker] importsCsv changed ({boundImports?.getD ""} -> {importsCsv}); restart required"
      TurboLean.ZygoteWorker.emitZygoteReply stdout false none false false false false 0 0 0 0 0 0 "" [mismatchErr] [mismatchErr] []
      try IO.Process.setCurrentDir initCwd catch _ => pure ()
      continue
    if isHeaderErr then
      let fn := customFileName?.getD "<zygote-shard>"
      let ictx := Parser.mkInputContext bodyCode fn
      let (_, _, msgLog) ← Parser.parseHeader ictx
      let mut hErrs : List String := []
      let mut hMsgs : List String := []
      for msg in msgLog.toList do
        let txt ← msg.data.toString
        let formatted ← if evalMode then msg.toString
          else pure s!"{msg.fileName}:{msg.pos.line}:{msg.pos.column}: error: {txt.trimAsciiEnd.toString}"
        hMsgs := hMsgs ++ [formatted]
        if msg.severity == .error then
          hErrs := hErrs ++ [formatted]
      if hErrs.isEmpty then
        let fallback := s!"{fn}:1:0: error: invalid module header"
        hErrs := [fallback]
        hMsgs := hMsgs ++ [fallback]
      TurboLean.ZygoteWorker.emitZygoteReply stdout false none (!evalMode) false false false 0 0 0 0 0 0 "" hMsgs hErrs []
      try IO.Process.setCurrentDir initCwd catch _ => pure ()
      continue
    let hostKey? := if hostClosureDigest.isEmpty then none else some s!"host:{hostClosureDigest}"
    let cachedHit? := match envCache[importsCsv]?, hostKey? with
      | some (cachedKey, cachedEnv), some hostKey => if cachedKey == hostKey then some cachedEnv else none
      | _, _ => none
    let (envCacheHit, importUs, baseEnv?, envErr?) ← match cachedHit? with
      | some env => pure (true, 0, some env, none)
      | none => do
        let tImp0 ← IO.monoNanosNow
        let level : OLeanLevel := if isMod then .exported else .private
        try
          -- `Lake.importModulesUsingCache` calls `enableInitializersExecution` before `importModules`;
          -- passing an anonymous module triggers `importModules`'s pre-`withImporting` guard, leaving
          -- `runInitializersRef` enabled for `Lean.importModules (loadExts := true) (level := level)`.
          try discard <| Lake.importModulesUsingCache #[{ module := .anonymous }] {} 0 catch _ => pure ()
          let env ← Lean.importModules imports {} 1025 #[] false true level
          let tImp1 ← IO.monoNanosNow
          pure (false, (tImp1 - tImp0) / 1000, some env, none)
        catch e =>
          let tImp1 ← IO.monoNanosNow
          pure (false, (tImp1 - tImp0) / 1000, none, some (toString e))
    let envDiskKey? := hostKey?
    match baseEnv? with
    | some baseEnv =>
      if !envCacheHit then
        if let some validDiskKey := envDiskKey? then
          if envCache.size >= maxEnvCache && !envCache.contains importsCsv then
            match envCacheOrder[0]? with
            | some oldestKey =>
              envCache := envCache.erase oldestKey
              envCacheOrder := envCacheOrder.extract 1 envCacheOrder.size
            | none =>
              envCache := {}
          envCache := envCache.insert importsCsv (validDiskKey, baseEnv)
          if !envCacheOrder.contains importsCsv then
            envCacheOrder := envCacheOrder.push importsCsv
      let envDiskKey ← match envDiskKey? with
        | some k => pure k
        | none => do
          let nonce ← IO.monoNanosNow
          pure s!"uncached:{importsCsv}:{nonce}"
      let kgActive := !evalMode
      let fastMap := fastMapOpt.getD []
      if fastMapOpt.isNone then
        let mapErr := "[TurboLean.KernelGate] malformed fast-verify map in request mode flag"
        TurboLean.ZygoteWorker.emitZygoteReply stdout false (if isRaceCandidates then some "null" else none) kgActive true envCacheHit false importUs 0 0 0 0 0 "" [mapErr] [mapErr] []
      -- Reject disallowed or malformed `-D` options before any elaboration (`lean` exits 1 on them).
      else if let .error e ← (TurboLean.ZygoteWorker.applyEncodedLeanArgs {} encodedLeanArgs).toBaseIO then
        let optErr := s!"{customFileName?.getD "<zygote-shard>"}:1:0: error: {e}"
        TurboLean.ZygoteWorker.emitZygoteReply stdout false none kgActive true envCacheHit false importUs 0 0 0 0 0 "" [optErr] [optErr] []
      else if isDiagnoseHotspots then
        let fn := customFileName?.getD "<zygote-shard>"
        let prefixCode := if hexPrefix.isEmpty then "" else TurboLean.ZygoteWorker.decodeHexToString hexPrefix
        let fullDiagCode := if prefixCode.trimAscii.toString.isEmpty then bodyCode
          else if bodyCode.trimAscii.toString.isEmpty then prefixCode
          else
            let prefNewlines := prefixCode.toList.filter (· == '\n') |>.length
            let leadingNewlines := (bodyCode.takeWhile (· == '\n')).toString.toList.length
            let rest := if leadingNewlines >= prefNewlines then (bodyCode.drop prefNewlines).toString else bodyCode
            if prefixCode.endsWith "\n" then prefixCode ++ rest else prefixCode ++ "\n" ++ rest
        let (diagUs, diagHbs, diagMsgs, diagErrs, diagSuffix) ←
          TurboLean.ZygoteWorker.diagnoseShardHotspots baseEnv fullDiagCode fn encodedLeanArgs
        if diagErrs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
        TurboLean.ZygoteWorker.emitZygoteReply stdout false none kgActive true envCacheHit false importUs 0 diagUs diagHbs 0 0 "" diagMsgs diagErrs [] [] [] diagSuffix
      else if prefixKey.isEmpty || hexPrefix.isEmpty then
        let fn := customFileName?.getD "<zygote-shard>"
        let prefixCode := if hexPrefix.isEmpty then "" else TurboLean.ZygoteWorker.decodeHexToString hexPrefix
        let combineWithPref := fun (subCode : String) =>
          if prefixCode.trimAscii.toString.isEmpty then subCode else prefixCode ++ "\n" ++ subCode
        if isBatchFission then
          let (bOk, bElabUs, bHbs, bNodes, bVer, bOut, bMsgs, bErrs, bUsed, bDeclTypes) ←
            TurboLean.ZygoteWorker.runBatchFissionSubs hexSubs (fun sc => do
                let (ok, us, hbs, nodes, errs, msgs, outS, used, dts, _) ←
                  TurboLean.ZygoteWorker.checkShardWithEnv baseEnv (combineWithPref sc) allowStub false fn none encodedLeanArgs stubTargets stubs
                    (requiredTargets := some []) (fastMap := fastMap) (allowSorry := allowSorry)
                pure (ok, us, hbs, nodes, errs, msgs, outS, used, dts))
          if !bOk && bErrs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
          TurboLean.ZygoteWorker.emitZygoteReply stdout bOk none kgActive true envCacheHit false importUs 0 bElabUs bHbs bNodes bVer bOut bMsgs bErrs bUsed bDeclTypes
        else if isRaceCandidates then
          let evalRaceOnBase := fun (cc : String) => do
            let scHasExplicitStub := (cc.splitOn (":= " ++ ("sor" ++ "ry"))).length > 1
            if scHasExplicitStub then
              let raceStubErr := "[TurboLean.KernelGate] explicit " ++ ("sor" ++ "ry") ++ " stub forbidden in race candidate"
              pure (false, 0, 0, 0, [raceStubErr], [], "", [], [])
            else
              let (ok, us, hbs, nodes, errs, msgs, outS, used, dts, _) ←
                TurboLean.ZygoteWorker.checkShardWithEnv baseEnv (combineWithPref cc) allowStub false fn none encodedLeanArgs stubTargets stubs
                  (requiredTargets := some []) (fastMap := fastMap) (allowSorry := allowSorry)
              pure (ok, us, hbs, nodes, errs, msgs, outS, used, dts)
          let (rOk, winIdx, rElabUs, rHbs, rNodes, rVer, rOut, rMsgs, rErrs, rUsed, rDeclTypes) ←
            TurboLean.ZygoteWorker.runRaceCandidatesSubs hexSubs evalRaceOnBase false (some evalRaceOnBase)
          if !rOk && rErrs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
          TurboLean.ZygoteWorker.emitZygoteReply stdout rOk (some winIdx) kgActive true envCacheHit false importUs 0 rElabUs rHbs rNodes rVer rOut rMsgs rErrs rUsed rDeclTypes
        else
          let forkShard ← TurboLean.ZygoteFork.isSingleShardForkEnabled
          let (ok, elabUs, hbs, ptNodes, errs, msgs, capOut, usedConsts, declTypes, sorryDecls) ←
            if forkShard then
              TurboLean.ZygoteWorker.checkShardWithEnvForked baseEnv bodyCode allowStub evalMode fn emitOlean? encodedLeanArgs stubTargets stubs
                (requiredTargets := some requiredTargets) (fastMap := fastMap) (includeStubsInDeclTypes := isProbeStub)
                (allowSorry := allowSorry) (emitOutlineOlean := isEmitOutline)
            else
              TurboLean.ZygoteWorker.checkShardWithEnv baseEnv bodyCode allowStub evalMode fn emitOlean? encodedLeanArgs stubTargets stubs
                (requiredTargets := some requiredTargets) (fastMap := fastMap) (includeStubsInDeclTypes := isProbeStub)
                (allowSorry := allowSorry) (emitOutlineOlean := isEmitOutline)
          if !ok && errs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
          TurboLean.ZygoteWorker.emitZygoteReply stdout ok none kgActive true envCacheHit false importUs 0 elabUs hbs ptNodes (if ok then 1 else 0) capOut msgs errs usedConsts declTypes sorryDecls
      else
        let fnPref := customFileName?.getD "<zygote-prefix>"
        let cwdKey := targetCwd.toString
        let emitModKey := match emitOlean? with | some (m, _) => m.toString | none => ""
        let prefAllowStub := !evalMode && (emitOlean?.isNone || isEmitOutline) && !strictAll
        let prefAllowSorry := allowSorry && !evalMode && emitOlean?.isNone
        let optsCacheSuffix := (if hexOpts.isEmpty then "" else s!"\topts:{hexOpts}") ++
          (if prefAllowSorry then "\tallow_sorry:1" else "")
        let importStubKey := (if evalMode || emitOlean?.isSome then s!"{envDiskKey}\t{prefAllowStub}\t{evalMode}\t{fnPref}\t{cwdKey}\t{emitModKey}" else s!"{envDiskKey}\t{prefAllowStub}\t{evalMode}") ++ optsCacheSuffix
        let fullPrefixKey := (if evalMode || emitOlean?.isSome then s!"{envDiskKey}\t{prefAllowStub}\t{evalMode}\t{fnPref}\t{cwdKey}\t{emitModKey}\t{prefixKey}" else s!"{envDiskKey}\t{prefAllowStub}\t{evalMode}\t{prefixKey}") ++ optsCacheSuffix
        let prefixCode := TurboLean.ZygoteWorker.decodeHexToString hexPrefix
        let (prefixCacheHit, prefixUs, ckptState?, prefErrs, prefMsgs, prefOut, prefHbs, decodedPrefix?) ← match stateCache[fullPrefixKey]? with
          | some (cachedCode, st, cachedMsgs, cachedOut, cachedHbs) =>
            if cachedCode == prefixCode then
              pure (true, 0, some st, [], cachedMsgs, cachedOut, cachedHbs, none)
            else do
              let initOpts : Options := if evalMode then
                  Elab.async.setIfNotSet (Lean.internal.cmdlineSnapshots.setIfNotSet {} true) true
                else {}
              let opts ← TurboLean.ZygoteWorker.applyEncodedLeanArgs initOpts encodedLeanArgs
              let envForPref ← match emitOlean? with
                | some (modName, _) => pure (if modName.isAnonymous then baseEnv else baseEnv.setMainModule modName)
                | none =>
                  if evalMode then do
                    let mainMod ← TurboLean.ZygoteWorker.deriveEvalMainModule fnPref
                    pure (if mainMod.isAnonymous then baseEnv else baseEnv.setMainModule mainMod)
                  else pure baseEnv
              let baseState := Command.mkState envForPref {} (← TurboLean.ZygoteWorker.withToolchainSatSolver opts)
              let (pOk, pUs, pHbs, _pNodes, pErrs, pMsgs, pOut, _pUsed, _pDeclTypes, _pSorryDecls, nextSt) ←
                TurboLean.ZygoteWorker.runCommandsFromState baseState prefixCode fnPref prefAllowStub evalMode (finalRun := false)
                  (allowSorry := prefAllowSorry)
              if pErrs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
              if pOk then pure (false, pUs, some nextSt, [], pMsgs, pOut, pHbs, some prefixCode)
              else pure (false, pUs, none, pErrs, pMsgs, pOut, pHbs, some prefixCode)
          | none => do
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
                -- Pad with the ancestor's newlines (and trailing-line columns) so message
                -- positions match a from-scratch run of `prefixCode`.
                let lastLine := (prevCode.splitOn "\n").getLast!
                let padding := "".pushn '\n' (prevCode.toList.filter (· == '\n')).length ++ "".pushn ' ' lastLine.length
                let deltaCode := padding ++ (prefixCode.drop (String.length prevCode)).toString
                let (dOk, dUs, dHbs, _dNodes, dErrs, dMsgs, dOut, _dUsed, _dDeclTypes, _dSorryDecls, dNextSt) ←
                  TurboLean.ZygoteWorker.runCommandsFromState prevState deltaCode fnPref prefAllowStub evalMode (finalRun := false)
                    (allowSorry := prefAllowSorry)
                if dOk then
                  pure (some (false, dUs, some dNextSt, ([] : List String), prevMsgs ++ dMsgs, prevOut ++ dOut, prevHbs + dHbs, some prefixCode))
                else if dErrs.contains TurboLean.ZygoteWorker.runtimePanicErr then
                  -- Never retry a panicked delta from scratch: the retry may not panic again.
                  poisoned := true
                  pure (some (false, dUs, none, dErrs, prevMsgs ++ dMsgs, prevOut ++ dOut, prevHbs + dHbs, some prefixCode))
                else pure none
              | none => pure none
            match deltaRes? with
            | some res => pure res
            | none => do
              let initOpts : Options := if evalMode then
                  Elab.async.setIfNotSet (Lean.internal.cmdlineSnapshots.setIfNotSet {} true) true
                else {}
              let opts ← TurboLean.ZygoteWorker.applyEncodedLeanArgs initOpts encodedLeanArgs
              let envForPref ← match emitOlean? with
                | some (modName, _) => pure (if modName.isAnonymous then baseEnv else baseEnv.setMainModule modName)
                | none =>
                  if evalMode then do
                    let mainMod ← TurboLean.ZygoteWorker.deriveEvalMainModule fnPref
                    pure (if mainMod.isAnonymous then baseEnv else baseEnv.setMainModule mainMod)
                  else pure baseEnv
              let baseState := Command.mkState envForPref {} (← TurboLean.ZygoteWorker.withToolchainSatSolver opts)
              let (pOk, pUs, pHbs, _pNodes, pErrs, pMsgs, pOut, _pUsed, _pDeclTypes, _pSorryDecls, nextSt) ←
                TurboLean.ZygoteWorker.runCommandsFromState baseState prefixCode fnPref prefAllowStub evalMode (finalRun := false)
                  (allowSorry := prefAllowSorry)
              if pErrs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
              if pOk then pure (false, pUs, some nextSt, [], pMsgs, pOut, pHbs, some prefixCode)
              else pure (false, pUs, none, pErrs, pMsgs, pOut, pHbs, some prefixCode)
        -- `poisoned` was false on entry, so here it means the prefix/delta panicked (`ckptState? = none`).
        -- That ends the request: no combined retry (a retry need not panic again), no checkpoint, no
        -- artifact, and never a success reply.
        match ckptState?, poisoned with
        | _, true =>
          TurboLean.ZygoteWorker.emitZygoteReply stdout false (if isRaceCandidates then some "null" else none) kgActive true envCacheHit false importUs prefixUs 0 prefHbs 0 0 prefOut prefMsgs prefErrs []
        | some ckptState, false =>
          -- Imported prefixes leave map₂: only body-only checks without fast-verify mappings
          -- may use them. All prefix declarations are audited without stub exemptions first.
          let compactEligible := !evalMode && emitOlean?.isNone && !allowSorry &&
            fastMap.isEmpty && !isProbeStub && !isBatchFission &&
            (isRaceCandidates || (requiredTargets.length == 1 &&
              requiredTargets.all (fun n => !(TurboLean.ZygoteWorker.declaresHostName ckptState.env [] n)))) &&
            ckptState.scopes.length == 1 && (ckptState.scopes.head?.any fun scope =>
              scope.currNamespace == .anonymous && scope.openDecls.isEmpty && scope.varDecls.isEmpty)
          if compactEligible && !compactCache.contains fullPrefixKey &&
              TurboLean.ZygoteWorker.environmentOnlyPrefix baseEnv prefixCode then
                if let some env ← TurboLean.ZygoteWorker.compactPrefix? baseEnv ckptState.env imports (if isMod then .exported else .private) then
                  if compactOrder.size >= maxCheckpoints then
                    if let some key := compactOrder[0]? then compactCache := compactCache.erase key
                    compactOrder := compactOrder.extract 1 compactOrder.size
                  compactCache := compactCache.insert fullPrefixKey env
                  compactOrder := compactOrder.push fullPrefixKey
          let compactEnv? := if compactEligible then compactCache[fullPrefixKey]? else none
          if !prefixCacheHit then
            if stateCache.size >= maxCheckpoints then
              match stateCacheOrder[0]? with
              | some oldestKey =>
                stateCache := stateCache.erase oldestKey
                stateCacheOrder := stateCacheOrder.extract 1 stateCacheOrder.size
              | none => stateCache := {}
            stateCache := stateCache.insert fullPrefixKey (prefixCode, ckptState, prefMsgs, prefOut, prefHbs)
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
            let (ok, us, hbs, nodes, errs, msgs, outS, used, dts, _, _) ←
              TurboLean.ZygoteWorker.runCommandsFromState ckptState sc fn allowStub false stubTargets stubs
                (strictPrefix := !allowStub) (requiredTargets := some []) (fastMap := fastMap) (allowSorry := allowSorry)
            pure (ok, us, hbs, nodes, errs, msgs, outS, used, dts)
          if isBatchFission then
            if hexSubs.isEmpty then
              TurboLean.ZygoteWorker.emitZygoteReply stdout true none kgActive true envCacheHit prefixCacheHit importUs prefixUs 0 prefHbs 0 0 prefOut prefMsgs [] []
            else
              let (bOk, bElabUs, bHbs, bNodes, bVer, bOut, bMsgs, bErrs, bUsed, bDeclTypes) ←
                TurboLean.ZygoteWorker.runBatchFissionSubs hexSubs evalFromCkpt
              if !bOk && bErrs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
              TurboLean.ZygoteWorker.emitZygoteReply stdout bOk none kgActive true envCacheHit prefixCacheHit importUs prefixUs bElabUs bHbs bNodes bVer bOut bMsgs bErrs bUsed bDeclTypes
          else if isRaceCandidates then
            if hexSubs.isEmpty then
              TurboLean.ZygoteWorker.emitZygoteReply stdout false (some "null") kgActive true envCacheHit prefixCacheHit importUs prefixUs 0 prefHbs 0 0 prefOut prefMsgs [] []
            else
              let evalCandForkFromBase := fun (sc : String) => do
                let scHasExplicitStub := (sc.splitOn (":= " ++ ("sor" ++ "ry"))).length > 1
                if scHasExplicitStub then
                  let raceStubErr := "[TurboLean.KernelGate] explicit " ++ ("sor" ++ "ry") ++ " stub forbidden in race candidate"
                  pure (false, 0, 0, 0, [raceStubErr], [], "", [], [])
                else
                  let combined := if compactEnv?.isSome then sc else if prefixCode.endsWith "\n" then prefixCode ++ sc else prefixCode ++ "\n" ++ sc
                  let (ok, us, hbs, nodes, errs, msgs, outS, used, dts, _) ←
                    TurboLean.ZygoteWorker.checkShardWithEnv (compactEnv?.getD baseEnv) combined allowStub false fn none encodedLeanArgs stubTargets stubs
                      (requiredTargets := some []) (fastMap := fastMap) (allowSorry := allowSorry)
                  pure (ok, us, hbs, nodes, errs, msgs, outS, used, dts)
              let (rOk, winIdx, rElabUs, rHbs, rNodes, rVer, rOut, rMsgs, rErrs, rUsed, rDeclTypes) ←
                TurboLean.ZygoteWorker.runRaceCandidatesSubs hexSubs evalFromCkpt false (some evalCandForkFromBase)
              if !rOk && rErrs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
              TurboLean.ZygoteWorker.emitZygoteReply stdout rOk (some winIdx) kgActive true envCacheHit prefixCacheHit importUs prefixUs rElabUs rHbs rNodes rVer rOut rMsgs rErrs rUsed rDeclTypes [] s!",\"compact_prefix\":{compactEnv?.isSome}"
          else if bodyCode.trimAscii.toString.isEmpty then
            let mut emitOk := true
            let mut emitErrs : List String := []
            let mut emitSorryDecls : List String := []
            if !evalMode && !isProbeStub then
              let allNewNames := ckptState.env.constants.map₂.foldl (fun acc name _ => acc.push name) #[]
              let isImportedOrig := fun (origName : Name) =>
                !ckptState.env.constants.map₂.contains origName && (ckptState.env.find? origName).isSome
              let (exempt, stubViolations) :=
                if allowStub then TurboLean.ZygoteWorker.stubExemptSet ckptState.env stubs stubTargets fastMap else ({}, [])
              if allowStub && !stubViolations.isEmpty then
                emitOk := false
                emitErrs := emitErrs ++ stubViolations
              let fastViolations :=
                TurboLean.ZygoteWorker.validateFastVerifyKernelMap ckptState.env allNewNames isImportedOrig exempt.contains fastMap
              if !fastViolations.isEmpty then
                emitOk := false
                emitErrs := emitErrs ++ fastViolations
              if !allowSorry && (allowStub || strictAll) &&
                  TurboLean.ZygoteWorker.unexemptPrefixStub ckptState.env (if allowStub then stubs else []) stubTargets fastMap then
                emitOk := false
                emitErrs := emitErrs ++ ["[TurboLean.KernelGate] stubbed prefix holds a `sorry` theorem this check does not exempt"]
              else if allowSorry then
                let sorryAxName := Name.mkSimple ("sor" ++ "ryAx")
                for (pName, _) in ckptState.env.constants.map₂.toList do
                  if !exempt.contains pName &&
                      (TurboLean.ZygoteWorker.collectDeclAxioms {} ckptState.env pName exempt.contains).contains sorryAxName then
                    let userNm := TurboLean.ZygoteWorker.canonicalName (Lean.privateToUserName pName)
                    if !userNm.isEmpty && !((userNm.splitOn "._").length > 1) && !((userNm.splitOn "_proof_").length > 1) && !emitSorryDecls.contains userNm then
                      emitSorryDecls := emitSorryDecls ++ [userNm]
              let noNewDecls := ckptState.env.constants.map₂.isEmpty
              if (!requiredTargets.isEmpty && !requiredTargets.all (TurboLean.ZygoteWorker.declaresHostName ckptState.env fastMap)) ||
                  (requiredTargets.isEmpty && !stubTargets.isEmpty && noNewDecls) then
                emitOk := false
                emitErrs := emitErrs ++ ["[TurboLean.KernelGate] a checked declaration is missing from the elaborated environment"]
            if emitOk then
              if let some (modName, oleanPath) := emitOlean? then
                if isEmitOutline then
                  if allowSorry || evalMode then
                    emitOk := false
                    emitErrs := ["emit_outline_olean rejected allow_sorry or eval mode"]
                  else
                    let wrote ← TurboLean.ZygoteWorker.writeVerifiedOutlineOlean baseEnv ckptState.env modName oleanPath
                    if !wrote then
                      emitOk := false
                      emitErrs := ["emit_outline_olean failed module identity or kernel hygiene gate"]
                else if allowStub || prefAllowStub || allowSorry || evalMode then
                  emitOk := false
                  emitErrs := ["emit_olean rejected stubbed or eval mode"]
                else
                  let wrote ← TurboLean.ZygoteWorker.writeVerifiedModuleOlean baseEnv ckptState.env modName oleanPath
                  if !wrote then
                    emitOk := false
                    emitErrs := ["emit_olean failed module identity or kernel hygiene gate"]
            let prefPtNodes := if !evalMode then TurboLean.ZygoteWorker.countNewDeclExprNodes baseEnv ckptState.env else 0
            let prefUsed := if !evalMode then (TurboLean.ZygoteWorker.collectNewDeclUsedConstants baseEnv ckptState.env).toList else []
            let prefDeclTypes := if !evalMode then TurboLean.ZygoteWorker.collectNewTheoremTypeHashes baseEnv ckptState.env (isProbeStub || allowSorry) fastMap else []
            TurboLean.ZygoteWorker.emitZygoteReply stdout emitOk none kgActive true envCacheHit prefixCacheHit importUs prefixUs 0 prefHbs prefPtNodes (if emitOk then 1 else 0) prefOut prefMsgs emitErrs prefUsed prefDeclTypes emitSorryDecls
          else
            let targetState := match compactEnv?, ckptState.scopes.head? with
              | some env, some scope => Command.mkState env {} scope.opts
              | _, _ => ckptState
            let (ok, elabUs, dHbs, ptNodes, errs, dMsgs, dOut, usedConsts, declTypes, sorryDecls, finalSt) ←
              TurboLean.ZygoteWorker.runCommandsFromState targetState bodyCode fn allowStub evalMode stubTargets stubs
                (strictPrefix := strictAll) (requiredTargets := some requiredTargets) (fastMap := fastMap) (includeStubsInDeclTypes := isProbeStub)
                (allowSorry := allowSorry)
            let mut finalOk := ok
            let mut finalErrs := errs
            if finalOk then
              if let some (modName, oleanPath) := emitOlean? then
                if isEmitOutline then
                  if allowSorry || evalMode then
                    finalOk := false
                    finalErrs := finalErrs ++ ["emit_outline_olean rejected allow_sorry or eval mode"]
                  else
                    let wrote ← TurboLean.ZygoteWorker.writeVerifiedOutlineOlean baseEnv finalSt.env modName oleanPath
                    if !wrote then
                      finalOk := false
                      finalErrs := finalErrs ++ ["emit_outline_olean failed module identity or kernel hygiene gate"]
                else if allowStub || prefAllowStub || allowSorry || evalMode then
                  finalOk := false
                  finalErrs := finalErrs ++ ["emit_olean rejected stubbed or eval mode"]
                else
                  let wrote ← TurboLean.ZygoteWorker.writeVerifiedModuleOlean baseEnv finalSt.env modName oleanPath
                  if !wrote then
                    finalOk := false
                    finalErrs := finalErrs ++ ["emit_olean failed module identity or kernel hygiene gate"]
            let finalMsgs := if evalMode then prefMsgs ++ dMsgs else dMsgs
            let finalOut := if evalMode then prefOut ++ dOut else dOut
            let finalHbs := if evalMode then prefHbs + dHbs else dHbs
            let finalDeclTypes := if evalMode || isProbeStub then declTypes else Id.run do
              let prefDeclTypes := TurboLean.ZygoteWorker.collectNewTheoremTypeHashes baseEnv ckptState.env allowSorry fastMap
              let mut merged := prefDeclTypes
              for (dn, dh) in declTypes do
                if !(merged.any (fun (k, _) => k == dn)) then
                  merged := merged ++ [(dn, dh)]
              return merged
            if !finalOk && finalErrs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
            TurboLean.ZygoteWorker.emitZygoteReply stdout finalOk none kgActive true envCacheHit prefixCacheHit importUs prefixUs elabUs finalHbs ptNodes (if finalOk then 1 else 0) finalOut finalMsgs finalErrs usedConsts finalDeclTypes sorryDecls
        | none, false =>
          if !prefErrs.isEmpty &&
              prefErrs.all (fun e => e.startsWith "[TurboLean.KernelGate]" || e.startsWith "forbidden token detected:") then
            TurboLean.ZygoteWorker.emitZygoteReply stdout false (if isRaceCandidates then some "null" else none) kgActive true envCacheHit false importUs prefixUs 0 prefHbs 0 0 prefOut prefMsgs prefErrs []
          else
            -- Fallback: if prefix failed on its own (e.g. split mid-command or open namespace in prefix), elaborate combined prefix + body from baseEnv
            let prefixCode := decodedPrefix?.getD (TurboLean.ZygoteWorker.decodeHexToString hexPrefix)
            let fn := customFileName?.getD "<zygote-shard>"
            let evalCombined := fun (sc : String) => do
              let (ok, us, hbs, nodes, errs, msgs, outS, used, dts, _) ←
                TurboLean.ZygoteWorker.checkShardWithEnv baseEnv (prefixCode ++ "\n" ++ sc) allowStub false fn none encodedLeanArgs stubTargets stubs
                  (requiredTargets := some []) (fastMap := fastMap)
              pure (ok, us, hbs, nodes, errs, msgs, outS, used, dts)
            if isBatchFission then
              if hexSubs.isEmpty then
                TurboLean.ZygoteWorker.emitZygoteReply stdout false none kgActive true envCacheHit false importUs prefixUs 0 prefHbs 0 0 prefOut prefMsgs prefErrs []
              else if hexSubs.any (fun hs =>
                  let s := TurboLean.ZygoteWorker.decodeHexToString hs
                  (s.splitOn (":= " ++ ("sor" ++ "ry"))).length > 1) then
                let subStubErr := "[TurboLean.KernelGate] explicit " ++ ("sor" ++ "ry") ++ " stub forbidden in batch_fission subshard"
                TurboLean.ZygoteWorker.emitZygoteReply stdout false none kgActive true envCacheHit false importUs prefixUs 0 prefHbs 0 0 prefOut prefMsgs [subStubErr] []
              else
                let (bOk, bElabUs, bHbs, bNodes, bVer, bOut, bMsgs, bErrs, bUsed, bDeclTypes) ←
                  TurboLean.ZygoteWorker.runBatchFissionSubs hexSubs evalCombined
                if !bOk && bErrs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
                TurboLean.ZygoteWorker.emitZygoteReply stdout bOk none kgActive true envCacheHit false importUs prefixUs bElabUs bHbs bNodes bVer bOut bMsgs bErrs bUsed bDeclTypes
            else if isRaceCandidates then
              if hexSubs.isEmpty then
                TurboLean.ZygoteWorker.emitZygoteReply stdout false (some "null") kgActive true envCacheHit false importUs prefixUs 0 prefHbs 0 0 prefOut prefMsgs prefErrs []
              else
                let evalCandCombined := fun (sc : String) =>
                  let scHasExplicitStub := (sc.splitOn (":= " ++ ("sor" ++ "ry"))).length > 1
                  if scHasExplicitStub then
                    let raceStubErr := "[TurboLean.KernelGate] explicit " ++ ("sor" ++ "ry") ++ " stub forbidden in race candidate"
                    pure (false, 0, 0, 0, [raceStubErr], [], "", [], [])
                  else
                    evalCombined sc
                let (rOk, winIdx, rElabUs, rHbs, rNodes, rVer, rOut, rMsgs, rErrs, rUsed, rDeclTypes) ←
                  TurboLean.ZygoteWorker.runRaceCandidatesSubs hexSubs evalCandCombined (!prefErrs.isEmpty) (some evalCandCombined)
                if !rOk && rErrs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
                TurboLean.ZygoteWorker.emitZygoteReply stdout rOk (some winIdx) kgActive true envCacheHit false importUs prefixUs rElabUs rHbs rNodes rVer rOut rMsgs rErrs rUsed rDeclTypes
            else if bodyCode.trimAscii.toString.isEmpty then
              TurboLean.ZygoteWorker.emitZygoteReply stdout false none kgActive true envCacheHit false importUs prefixUs 0 prefHbs 0 0 prefOut prefMsgs prefErrs []
            else
              let prefNewlines := prefixCode.toList.filter (· == '\n') |>.length
              let leadingNewlines := (bodyCode.takeWhile (· == '\n')).toString.toList.length
              let rest := if isProbeStub then bodyCode
                else if leadingNewlines >= prefNewlines then (bodyCode.drop prefNewlines).toString
                else bodyCode
              let combined := if prefixCode.endsWith "\n" then prefixCode ++ rest else prefixCode ++ "\n" ++ rest
              let forkShard ← TurboLean.ZygoteFork.isSingleShardForkEnabled
              let (ok, elabUs, hbs, ptNodes, errs, msgs, capOut, usedConsts, declTypes, sorryDecls) ←
                if forkShard then
                  TurboLean.ZygoteWorker.checkShardWithEnvForked baseEnv combined allowStub evalMode fn emitOlean? encodedLeanArgs stubTargets stubs
                    (requiredTargets := some requiredTargets) (fastMap := fastMap) (includeStubsInDeclTypes := isProbeStub)
                    (allowSorry := allowSorry) (emitOutlineOlean := isEmitOutline)
                else
                  TurboLean.ZygoteWorker.checkShardWithEnv baseEnv combined allowStub evalMode fn emitOlean? encodedLeanArgs stubTargets stubs
                    (requiredTargets := some requiredTargets) (fastMap := fastMap) (includeStubsInDeclTypes := isProbeStub)
                    (allowSorry := allowSorry) (emitOutlineOlean := isEmitOutline)
              if !ok && errs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
              TurboLean.ZygoteWorker.emitZygoteReply stdout ok none kgActive true envCacheHit false importUs prefixUs elabUs hbs ptNodes (if ok then 1 else 0) capOut msgs errs usedConsts declTypes sorryDecls
    | none =>
      let rawErr := envErr?.getD "importModules failed"
      let formattedErr := match customFileName? with
        | some fn => if evalMode && !rawErr.startsWith fn then s!"{fn}:1:0: error: {rawErr}\n" else rawErr
        | none => rawErr
      TurboLean.ZygoteWorker.emitZygoteReply stdout false none false false false false importUs 0 0 0 0 0 "" [formattedErr] [formattedErr] []
    -- Bind even an empty `importsCsv` (implicit `Init`): its environment extensions are live too.
    if boundImports?.isNone then
      boundImports? := some importsCsv
    try IO.Process.setCurrentDir initCwd catch _ => pure ()
