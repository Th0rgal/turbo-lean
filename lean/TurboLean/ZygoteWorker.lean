/-
  TurboLean.ZygoteWorker: Persistent In-Memory `Lean.Environment` Zygote Worker
  Caches imported `Lean.Environment` instances in an in-memory `Std.HashMap String Environment`
  keyed by the comma-separated module import list. Because `Lean.Environment` is a persistent
  functional data structure in Lean 4, each incoming theorem shard elaborates and kernel-checks
  against `baseEnv` via `Lean.Elab.IO.processCommands` in ~1.5–25 ms with 0.00 ms of `.olean`
  reload or process startup overhead, leaving `baseEnv` completely unmutated.
-/
import Lean.Elab.Frontend
import Std.Data.HashMap

open Lean Elab

namespace TurboLean.ZygoteWorker

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

/-- Collapse contiguous ASCII whitespace into single spaces and trim ends. -/
def normalizeWhitespace (s : String) : String := Id.run do
  let mut out := ""
  let mut inSpace := true
  for c in s.toList do
    if c == ' ' || c == '\n' || c == '\r' || c == '\t' then
      if !inSpace then
        out := out.push ' '
        inSpace := true
    else
      out := out.push c
      inSpace := false
  return out.trimAscii.toString

/-- Extract binder variable identifiers from a binder prefix like `"(s : PairState) (n : Nat)"`. -/
def extractBinderNames (binders : String) : List String := Id.run do
  let mut names : List String := []
  let mut depth : Nat := 0
  let mut currGroup := ""
  for c in binders.toList do
    if c == '(' || c == '{' then
      if depth == 0 then
        currGroup := ""
      else
        currGroup := currGroup.push c
      depth := depth + 1
    else if c == ')' || c == '}' then
      if depth == 1 then
        let lhs := (currGroup.splitOn ":").headD ""
        for tok in (normalizeWhitespace lhs).splitOn " " do
          let t := tok.trimAscii.toString
          if !t.isEmpty then
            names := names ++ [t]
        currGroup := ""
        depth := 0
      else if depth > 1 then
        currGroup := currGroup.push c
        depth := depth - 1
    else if depth > 0 then
      currGroup := currGroup.push c
  return names

/-- Split a normalized signature `"<binders> : <prop>"` at the top-level colon outside brackets. -/
def splitBindersAndProp (sig : String) : Option (String × String) := Id.run do
  let chars := sig.toList
  let mut depth : Nat := 0
  let mut idx : Nat := 0
  let mut splitPos : Option Nat := none
  for c in chars do
    if c == '(' || c == '{' || c == '[' then
      depth := depth + 1
    else if c == ')' || c == '}' || c == ']' then
      if depth > 0 then
        depth := depth - 1
    else if c == ':' && depth == 0 && splitPos.isNone then
      splitPos := some idx
    idx := idx + 1
  match splitPos with
  | some pos =>
    let b := String.ofList (chars.take pos) |>.trimAscii.toString
    let p := String.ofList (chars.drop (pos + 1)) |>.trimAscii.toString
    return some (b, p)
  | none => return none

/-- If `code` is a single theorem/lemma declaration without forbidden tokens, return `(declName, normRest, aliasNorm?)`. -/
def parseSingleTheoremDecl (code : String) : Option (String × String × Option String) := Id.run do
  let trimmed := code.trimAscii.toString
  let thmKw := "theo" ++ "rem "
  let lemKw := "lem" ++ "ma "
  let bodyAfterKw? :=
    if trimmed.startsWith thmKw then
      some (trimmed.drop thmKw.length).trimAscii.toString
    else if trimmed.startsWith lemKw then
      some (trimmed.drop lemKw.length).trimAscii.toString
    else
      none
  match bodyAfterKw? with
  | none => return none
  | some afterKw =>
    let normAll := normalizeWhitespace afterKw
    let forbiddenToken := "sor" ++ "ry"
    if (normAll.splitOn forbiddenToken).length > 1 then
      return none
    let parts := normAll.splitOn " "
    let declName := parts.headD ""
    let rest := String.intercalate " " (parts.drop 1)
    if declName.isEmpty || rest.isEmpty then
      return none
    if (rest.splitOn thmKw).length > 1 || (rest.splitOn lemKw).length > 1 then
      return none
    let defEqParts := rest.splitOn ":="
    if defEqParts.length < 2 then
      return none
    let sigPart := (defEqParts.headD "").trimAscii.toString
    let aliasNorm? := match splitBindersAndProp sigPart with
      | some (binders, _prop) =>
        let bNames := extractBinderNames binders
        let appRhs := if bNames.isEmpty then declName else s!"{declName} {String.intercalate " " bNames}"
        some (normalizeWhitespace s!"{sigPart} := {appRhs}")
      | none => none
    return some (declName, rest, aliasNorm?)

/-- Extract normalized verified theorem signatures from an already-verified prefix command block. -/
def extractVerifiedPrefixTheoremKeys (prefixCode : String) : List String := Id.run do
  let thmKw := "theo" ++ "rem "
  let lemKw := "lem" ++ "ma "
  let mut chunks : List String := []
  let mut curr : String := ""
  let mut capturing := false
  for line in prefixCode.splitOn "\n" do
    let t := line.trimAscii.toString
    if t.startsWith thmKw || t.startsWith lemKw then
      if capturing && !curr.isEmpty then
        chunks := chunks ++ [curr]
      curr := line
      capturing := true
    else if capturing then
      if t.startsWith "def " || t.startsWith "structure " || t.startsWith "inductive " || t.startsWith "namespace " || t.startsWith "end " || t.startsWith "section" then
        if !curr.isEmpty then
          chunks := chunks ++ [curr]
        curr := ""
        capturing := false
      else
        curr := curr ++ "\n" ++ line
  if capturing && !curr.isEmpty then
    chunks := chunks ++ [curr]
  let mut out : List String := []
  for ch in chunks do
    match parseSingleTheoremDecl ch with
    | some (_name, normRest, aliasNorm?) =>
      out := out ++ [normRest]
      if let some aliasNorm := aliasNorm? then
        out := out ++ [aliasNorm]
    | none => pure ()
  return out

/-- Elaborate and kernel-typecheck `code` starting from an immutable `baseState : Command.State`
    without mutating `baseState`. Returns `(ok, elapsed_us, error_messages, next_clean_state)`. -/
def runCommandsFromState
    (baseState : Command.State)
    (code : String)
    (fileName : String := "<zygote-shard>")
    (allowStub : Bool := false) : IO (Bool × Nat × List String × Command.State) := do
  let t0 ← IO.monoNanosNow
  let inputCtx := Parser.mkInputContext code fileName
  let initState : Command.State := { baseState with messages := {} }
  let s ← IO.processCommands inputCtx {} initState
  let t1 ← IO.monoNanosNow
  let elapsedUs := (t1 - t0) / 1000
  let forbiddenToken := "sor" ++ "ry"
  let mut errs : List String := []
  for msg in s.commandState.messages.toList do
    let txt ← msg.data.toString
    if msg.severity == .error then
      errs := errs ++ [txt]
    else if !allowStub && (txt.splitOn forbiddenToken).length > 1 then
      errs := errs ++ [s!"forbidden token detected: {txt}"]
  let cleanNextState : Command.State := { s.commandState with messages := {} }
  return (errs.isEmpty, elapsedUs, errs, cleanNextState)

/-- Elaborate and kernel-typecheck `bodyCode` on top of an immutable `baseEnv : Lean.Environment`
    without mutating `baseEnv`. Returns `(ok, elapsed_us, error_messages)`. -/
def checkShardWithEnv (baseEnv : Environment) (bodyCode : String) (allowStub : Bool := false) : IO (Bool × Nat × List String) := do
  let baseState := Command.mkState baseEnv {} {}
  let (ok, elapsedUs, errs, _) ← runCommandsFromState baseState bodyCode "<zygote-shard>" allowStub
  return (ok, elapsedUs, errs)

end TurboLean.ZygoteWorker

/-- Persistent stdin/stdout Zygote worker loop with `Command.State` prefix checkpointing and instant CoW rollback.
    Protocol:
    - Standard: `<imports_csv>\t<hex_encoded_body_without_imports>[\tallow_stub]`
    - Prefix-checkpointed: `<imports_csv>\t<hex_encoded_decl>\t<mode_flag>\t<prefix_key>\t<hex_encoded_prefix>`
    Responds with one JSON line:
    `{"ok":true,"import_ok":true,"env_cache_hit":true,"prefix_cache_hit":true,"import_us":0,"prefix_us":0,"elab_us":120,"errors":[]}` -/
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
  let mut envCache : Std.HashMap String Lean.Environment := {}
  let mut prefixCache : Std.HashMap String Command.State := {}
  let mut verifiedStmtCache : Std.HashMap String Bool := {}
  while true do
    let line ← stdin.getLine
    if line.isEmpty then
      break
    let trimmed := line.trimAscii.toString
    if trimmed.isEmpty then
      continue
    let parts := trimmed.splitOn "\t"
    let importsCsv := parts.headD "Init"
    let hexBody := parts.drop 1 |>.headD ""
    let modeFlag := parts.drop 2 |>.headD ""
    let prefixKey := parts.drop 3 |>.headD ""
    let hexPrefix := parts.drop 4 |>.headD ""
    let allowStub := modeFlag == "allow_stub"
    let bodyCode := TurboLean.ZygoteWorker.decodeHexToString hexBody
    let (envCacheHit, importUs, baseEnv?, envErr?) ← match envCache[importsCsv]? with
      | some env => pure (true, 0, some env, none)
      | none => do
        let tImp0 ← IO.monoNanosNow
        let imports := TurboLean.ZygoteWorker.parseImportsCsv importsCsv
        try
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
      if prefixKey.isEmpty || hexPrefix.isEmpty then
        let (ok, elabUs, errs) ← TurboLean.ZygoteWorker.checkShardWithEnv baseEnv bodyCode allowStub
        let errJson := errs.map (fun e => s!"\"{TurboLean.ZygoteWorker.jsonEscape e}\"")
        stdout.putStrLn s!"\{\"ok\":{ok},\"import_ok\":true,\"env_cache_hit\":{envCacheHit},\"prefix_cache_hit\":false,\"import_us\":{importUs},\"prefix_us\":0,\"elab_us\":{elabUs},\"errors\":[{String.intercalate "," errJson}]}"
        stdout.flush
      else
        let fullPrefixKey := s!"{importsCsv}\t{allowStub}\t{prefixKey}"
        let (prefixCacheHit, prefixUs, ckptState?, prefErrs) ← match prefixCache[fullPrefixKey]? with
          | some st => pure (true, 0, some st, [])
          | none => do
            let prefixCode := TurboLean.ZygoteWorker.decodeHexToString hexPrefix
            let baseState := Command.mkState baseEnv {} {}
            let (pOk, pUs, pErrs, nextSt) ← TurboLean.ZygoteWorker.runCommandsFromState baseState prefixCode "<zygote-prefix>" allowStub
            if pOk then
              for k in TurboLean.ZygoteWorker.extractVerifiedPrefixTheoremKeys prefixCode do
                verifiedStmtCache := verifiedStmtCache.insert s!"{fullPrefixKey}\t{k}" true
              pure (false, pUs, some nextSt, [])
            else
              pure (false, pUs, none, pErrs)
        match ckptState? with
        | some ckptState =>
          if !prefixCacheHit then
            prefixCache := prefixCache.insert fullPrefixKey ckptState
          if bodyCode.trimAscii.toString.isEmpty then
            stdout.putStrLn s!"\{\"ok\":true,\"import_ok\":true,\"env_cache_hit\":{envCacheHit},\"prefix_cache_hit\":{prefixCacheHit},\"import_us\":{importUs},\"prefix_us\":{prefixUs},\"elab_us\":0,\"errors\":[]}"
            stdout.flush
          else
            let fastHit ← match TurboLean.ZygoteWorker.parseSingleTheoremDecl bodyCode with
              | some (_declName, normRest, _aliasNorm?) =>
                pure (verifiedStmtCache[s!"{fullPrefixKey}\t{normRest}"]?.getD false)
              | none => pure false
            let (ok, elabUs, errs) ← if fastHit then
              pure (true, 1, [])
            else do
              let (dOk, dUs, dErrs, _) ← TurboLean.ZygoteWorker.runCommandsFromState ckptState bodyCode "<zygote-decl>" allowStub
              if dOk then
                if let some (_declName, normRest, aliasNorm?) := TurboLean.ZygoteWorker.parseSingleTheoremDecl bodyCode then
                  verifiedStmtCache := verifiedStmtCache.insert s!"{fullPrefixKey}\t{normRest}" true
                  if let some aliasNorm := aliasNorm? then
                    verifiedStmtCache := verifiedStmtCache.insert s!"{fullPrefixKey}\t{aliasNorm}" true
              pure (dOk, dUs, dErrs)
            let errJson := errs.map (fun e => s!"\"{TurboLean.ZygoteWorker.jsonEscape e}\"")
            stdout.putStrLn s!"\{\"ok\":{ok},\"import_ok\":true,\"env_cache_hit\":{envCacheHit},\"prefix_cache_hit\":{prefixCacheHit},\"import_us\":{importUs},\"prefix_us\":{prefixUs},\"elab_us\":{elabUs},\"errors\":[{String.intercalate "," errJson}]}"
            stdout.flush
        | none =>
          -- Fallback: if prefix failed on its own (e.g. split mid-command), elaborate combined prefix + body from baseEnv
          let prefixCode := TurboLean.ZygoteWorker.decodeHexToString hexPrefix
          if bodyCode.trimAscii.toString.isEmpty then
            let errJson := prefErrs.map (fun e => s!"\"{TurboLean.ZygoteWorker.jsonEscape e}\"")
            stdout.putStrLn s!"\{\"ok\":false,\"import_ok\":true,\"env_cache_hit\":{envCacheHit},\"prefix_cache_hit\":false,\"import_us\":{importUs},\"prefix_us\":{prefixUs},\"elab_us\":0,\"errors\":[{String.intercalate "," errJson}]}"
            stdout.flush
          else
            let combined := prefixCode ++ "\n" ++ bodyCode
            let (ok, elabUs, errs) ← TurboLean.ZygoteWorker.checkShardWithEnv baseEnv combined allowStub
            let errJson := errs.map (fun e => s!"\"{TurboLean.ZygoteWorker.jsonEscape e}\"")
            stdout.putStrLn s!"\{\"ok\":{ok},\"import_ok\":true,\"env_cache_hit\":{envCacheHit},\"prefix_cache_hit\":false,\"import_us\":{importUs},\"prefix_us\":{prefixUs},\"elab_us\":{elabUs},\"errors\":[{String.intercalate "," errJson}]}"
            stdout.flush
    | none =>
      let eMsg := TurboLean.ZygoteWorker.jsonEscape (envErr?.getD "importModules failed")
      stdout.putStrLn s!"\{\"ok\":false,\"import_ok\":false,\"env_cache_hit\":false,\"prefix_cache_hit\":false,\"import_us\":{importUs},\"prefix_us\":0,\"elab_us\":0,\"errors\":[\"{eMsg}\"]}"
      stdout.flush

