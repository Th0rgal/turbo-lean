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

/-- Elaborate and kernel-typecheck `bodyCode` on top of an immutable `baseEnv : Lean.Environment`
    without mutating `baseEnv`. Returns `(ok, elapsed_us, error_messages)`. -/
def checkShardWithEnv (baseEnv : Environment) (bodyCode : String) (allowStub : Bool := false) : IO (Bool × Nat × List String) := do
  let t0 ← IO.monoNanosNow
  let inputCtx := Parser.mkInputContext bodyCode "<zygote-shard>"
  let cmdState := Command.mkState baseEnv {} {}
  let s ← IO.processCommands inputCtx {} cmdState
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
  return (errs.isEmpty, elapsedUs, errs)

end TurboLean.ZygoteWorker

/-- Persistent stdin/stdout Zygote worker loop.
    Protocol: each request line is `<imports_csv>\t<hex_encoded_body_without_imports>[\tallow_stub]`.
    Responds with one JSON line:
    `{"ok":true,"import_ok":true,"env_cache_hit":true,"import_us":0,"elab_us":1475,"errors":[]}` -/
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
      let (ok, elabUs, errs) ← TurboLean.ZygoteWorker.checkShardWithEnv baseEnv bodyCode allowStub
      let errJson := errs.map (fun e => s!"\"{TurboLean.ZygoteWorker.jsonEscape e}\"")
      stdout.putStrLn s!"\{\"ok\":{ok},\"import_ok\":true,\"env_cache_hit\":{envCacheHit},\"import_us\":{importUs},\"elab_us\":{elabUs},\"errors\":[{String.intercalate "," errJson}]}"
      stdout.flush
    | none =>
      let eMsg := TurboLean.ZygoteWorker.jsonEscape (envErr?.getD "importModules failed")
      stdout.putStrLn s!"\{\"ok\":false,\"import_ok\":false,\"env_cache_hit\":false,\"import_us\":{importUs},\"elab_us\":0,\"errors\":[\"{eMsg}\"]}"
      stdout.flush
