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

/-- Encode a UTF-8 string into lowercase ASCII hex. -/
def encodeStringToHex (s : String) : String := Id.run do
  let hexChars : Array Char := #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']
  let bytes := s.toUTF8
  let mut out := ""
  for i in [0:bytes.size] do
    let b := bytes.get! i
    out := out.push (hexChars[(b >>> 4).toNat]!)
    out := out.push (hexChars[(b &&& 0x0f).toNat]!)
  return out

/-- Encode a list of strings as comma-separated hex chunks. -/
def encodeHexList (xs : List String) : String :=
  String.intercalate "," (xs.map encodeStringToHex)

/-- Decode comma-separated hex chunks back into a list of strings. -/
def decodeHexList (csv : String) : List String :=
  if csv.isEmpty then []
  else (csv.splitOn ",").filter (!·.isEmpty) |>.map decodeHexToString

/-- Encode `(String × String)` pairs as comma-separated `hexK:hexV` chunks. -/
def encodeHexPairs (xs : List (String × String)) : String :=
  String.intercalate "," (xs.map fun (k, v) => s!"{encodeStringToHex k}:{encodeStringToHex v}")

/-- Decode comma-separated `hexK:hexV` chunks back into `(String × String)` pairs. -/
def decodeHexPairs (csv : String) : List (String × String) :=
  if csv.isEmpty then []
  else (csv.splitOn ",").filterMap fun item =>
    match item.splitOn ":" with
    | [hk, hv] => some (decodeHexToString hk, decodeHexToString hv)
    | _ => none

/-- Parse a dot-separated Lean module name (supporting `«...»` guillemet-escaped segments) into a `Lean.Name`. -/
def parseModuleName (s : String) : Name := Id.run do
  let trimmed := s.trimAscii.toString
  if trimmed.isEmpty then
    return Name.anonymous
  let mut parts : Array String := #[]
  let mut cur := ""
  let mut inGuillemet := false
  for c in trimmed.toList do
    if inGuillemet then
      if c == '»' then
        inGuillemet := false
      else
        cur := cur.push c
    else if c == '«' then
      inGuillemet := true
    else if c == '.' then
      parts := parts.push cur
      cur := ""
    else
      cur := cur.push c
  parts := parts.push cur
  return parts.foldl (fun acc p => if p.isEmpty then acc else Name.str acc p) Name.anonymous

/-- Parse an encoded `importsCsv` into `(Array Lean.Import, isModule, isHeaderErr)`. -/
def parseImportsCsvSpec (csv : String) : (Array Import × Bool × Bool) := Id.run do
  let trimmed := csv.trimAscii.toString
  if trimmed == "__HEADER_ERR__" then
    return (#[], false, true)
  if trimmed == "__PRELUDE__" then
    return (#[], false, false)
  if trimmed.isEmpty then
    return (#[{ module := `Init, isExported := true }, { module := `Init, isExported := true, isMeta := true }], false, false)
  let rawParts := (trimmed.splitOn ",").map (fun s => s.trimAscii.toString) |>.filter (fun s => !s.isEmpty)
  let isMod := rawParts.contains "__MODULE__"
  let hasPrelude := rawParts.contains "__PRELUDE__"
  let mut out : Array Import := #[]
  let mut hasExplicitInit := false
  for part in rawParts do
    if part == "__MODULE__" || part == "__PRELUDE__" then
      continue
    let (flagsOpt, modRaw) := match part.splitOn "@" with
      | f :: rest =>
        if rest.isEmpty then (none, part)
        else (some f, String.intercalate "@" rest)
      | [] => (none, part)
    let modName := parseModuleName modRaw
    if !modName.isAnonymous then
      if modName == `Init then
        hasExplicitInit := true
      let (isExp, isMet, impAll) := match flagsOpt with
        | some fl => (fl.contains 'p', fl.contains 'm', fl.contains 'a')
        | none => (!isMod, false, false)
      out := out.push { module := modName, isExported := isExp, isMeta := isMet, importAll := impAll }
  if !isMod && !hasPrelude && !hasExplicitInit then
    out := #[{ module := `Init, isExported := true }, { module := `Init, isExported := true, isMeta := true }] ++ out
  else if !isMod && !hasPrelude && hasExplicitInit && out.size == 1 && out[0]!.module == `Init && !out[0]!.isMeta then
    out := out.push { module := `Init, isExported := true, isMeta := true }
  return (out, isMod, false)

/-- Parse a comma-separated list of module names into `Array Lean.Import`. -/
def parseImportsCsv (csv : String) : Array Import :=
  (parseImportsCsvSpec csv).1

/-- Coalesce companion sibling imports (such as `ProofKit` alongside `Midnight.Spec`)
    when `ProofKit.olean` exists on `Lean.searchPathRef`, so a single `Lean.importModules`
    call caches the shared environment in `envCache`. -/
def coalesceImportsCsv (csv : String) : IO String := do
  let trimmed := csv.trimAscii.toString
  if trimmed == "__HEADER_ERR__" then
    return trimmed
  let mods := (trimmed.splitOn ",").map (fun s => s.trimAscii.toString) |>.filter (fun s => !s.isEmpty)
  if !mods.contains "__MODULE__" && mods.contains "Midnight.Spec" && !mods.contains "ProofKit" then
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

/-- Format `(key, val)` string pairs as a comma-separated JSON object body. -/
def jsonKvObj (kvs : List (String × String)) : String :=
  String.intercalate "," (kvs.map (fun (k, v) => s!"\"{jsonEscape k}\":\"{jsonEscape v}\""))

/-- Line written to the process stderr right before every reply. Panics printed straight to stderr
    (`set_option stderrAsMessages false`, other threads) precede it, so the host
    (`zygote.rs`, `ZYGOTE_STDERR_REPLY_MARK`) waits for it and then knows whether the request panicked. -/
def stderrReplyMark : String := "[TurboLean.ZygoteWorker] reply"

/-- Emit a single-line JSON Zygote reply and flush `stdout`. -/
def emitZygoteReply (stdout : IO.FS.Stream) (ok : Bool) (winIdx? : Option String) (kgActive importOk envHit prefHit : Bool)
    (importUs prefixUs elabUs hbs nodes subVerified : Nat) (outStr : String) (msgs errs used : List String)
    (declTypes : List (String × String) := [])
    (sorryDecls : List String := [])
    (extraJsonSuffix : String := "") : IO Unit := do
  let stderr ← IO.getStderr
  stderr.putStrLn s!"\n{stderrReplyMark}"
  stderr.flush
  let winPart := match winIdx? with | some w => s!"\"winning_candidate_idx\":{w}," | none => ""
  let kgPart := if importOk then s!"\"kernel_gate_active\":{kgActive}," else ""
  let sorryPart := if sorryDecls.isEmpty then ""
    else s!",\"used_sorry\":true,\"sorry_decls\":[{jsonStrList sorryDecls}]"
  stdout.putStrLn s!"\{\"ok\":{ok},{winPart}{kgPart}\"import_ok\":{importOk},\"env_cache_hit\":{envHit},\"prefix_cache_hit\":{prefHit},\"import_us\":{importUs},\"prefix_us\":{prefixUs},\"elab_us\":{elabUs},\"heartbeats\":{hbs},\"proof_term_nodes\":{nodes},\"subshards_verified\":{subVerified},\"stdout\":\"{jsonEscape outStr}\",\"messages\":[{jsonStrList msgs}],\"errors\":[{jsonStrList errs}],\"used_constants\":[{jsonStrList used}],\"decl_types\":\{{jsonKvObj declTypes}}{sorryPart}{extraJsonSuffix}}"
  stdout.flush

/-- The toolchain's `cadical`, set in `main` from the sysroot: `bv_decide` looks for it next to the
    running executable (for the zygote, a copy outside the toolchain) and then on `PATH`. -/
initialize satSolverRef : IO.Ref String ← IO.mkRef ""

/-- `opts` with `sat.solver` pointing at the toolchain's `cadical`, unless the shard sets it. -/
def withToolchainSatSolver (opts : Options) : IO Options := do
  let s ← satSolverRef.get
  return if s.isEmpty || opts.contains `sat.solver then opts else opts.set `sat.solver s

/-- Mirror of `is_allowed_lean_option` in `crates/turbo-lean/src/module_builder.rs`; keep the two
    in sync. `key` has every leading `weak.` already stripped. -/
def isAllowedLeanOption (key value : String) : Bool :=
  let warnStubKey := "warn." ++ ("sor" ++ "ry")
  if key == warnStubKey then value == "true"
  else if key == "debug.skipKernelTC" then value == "false"
  else
    ["pp.unicode.fun", "pp.mvars.anonymous", "autoImplicit", "relaxedAutoImplicit", "maxHeartbeats",
      "maxRecDepth", "maxSynthPendingDepth", "synthInstance.maxHeartbeats", "synthInstance.maxSize",
      "warningAsError", "exponentiation.threshold"].contains key ||
    ["linter.", "backward.", "experimental."].any (fun (p : String) => key.startsWith p)

/-- `key` with every leading `weak.` removed. -/
partial def stripWeakPrefixes (key : String) : String :=
  if key.startsWith "weak." then stripWeakPrefixes (key.drop 5).toString else key

/-- Apply CLI-style `-Dkey=value` options (Lake `leanOptions` / `moreLeanArgs` / `weakLeanArgs`)
    onto `opts` after imports are loaded. Every arg must pass the host allowlist
    (`is_allowed_lean_arg` in `module_builder.rs`), checked on the key with all `weak.` prefixes
    removed; values are then parsed exactly as `Lean.Language.Lean.setOption` / `reparseOptions`
    do. Anything else throws, so the request fails instead of silently dropping an option.
    After parsing, `debug.skipKernelTC := false` and the incomplete-proof warning option are forced regardless. -/
def applyEncodedLeanArgs (baseOpts : Options) (encodedArgs : String) : IO Options := do
  let decls ← getOptionDecls
  let mut opts := baseOpts
  for arg in encodedArgs.splitOn "\n" do
    if arg.isEmpty || arg ∈ ["--json", "-q", "--quiet"] then continue
    let bad := fun (why : String) => IO.userError s!"invalid Lean option {arg.quote}: {why}"
    if arg.startsWith "-j" || arg.startsWith "--threads=" || arg.startsWith "--tstack=" then
      let num := if arg.startsWith "-j" then (arg.drop 2).toString else ((arg.splitOn "=").drop 1).headD ""
      match num.toNat? with
      | some n => if n == 0 || n > (if arg.startsWith "--tstack=" then 1048576 else 64) then throw (bad "out of range")
      | none => throw (bad "not a number")
      continue
    let some kv := arg.dropPrefix? "-D" | throw (bad "not allowed")
    let k := (kv.toString.splitOn "=").headD ""
    let v := (kv.toString.drop (k.length + 1)).toString
    if !(kv.toString.contains '=') || k.isEmpty || v.isEmpty || v.any (fun (c : Char) => c.toNat < 32 || c.toNat == 127)
        || !k.all (fun (c : Char) => c.isAlphanum || c == '.' || c == '_' || c == '-') then
      throw (bad "malformed")
    if !isAllowedLeanOption (stripWeakPrefixes k) v then
      throw (bad "not on the allowlist (module_builder.rs is_allowed_lean_option)")
    let rawName := k.toName
    let isWeak := rawName.getRoot == `weak
    let name := rawName.replacePrefix `weak Name.anonymous
    match decls.find? name with
    | none => if !isWeak then throw (bad "unknown configuration option")
    | some decl =>
      opts ← match decl.defValue, v with
        | .ofBool _, "true" => pure (opts.set name true)
        | .ofBool _, "false" => pure (opts.set name false)
        | .ofBool _, _ => throw (bad "value must be true/false")
        | .ofNat _, _ => match v.toNat? with
          | some n => pure (opts.set name n)
          | none => throw (bad "value must be a natural number")
        | .ofString _, _ => pure (opts.set name v)
        | _, _ => throw (bad "cannot be set in the command line")
  -- Match the hardening flags forced last by the native module/PR subprocesses.
  -- The host owns the allowlist; the raw worker protocol cannot disable these gates.
  return (opts.setBool `debug.skipKernelTC false).setBool (Name.mkStr2 "warn" ("sor" ++ "ry")) true

/-- Error reported (and checked for) when a Lean runtime panic leaves the worker unusable. -/
def runtimePanicErr : String := "[TurboLean.ZygoteWorker] runtime panic; worker environment is unusable"

/-- Lean runtime panic output (`PANIC at <decl> <mod>:<line>:<col>: ...`, `INTERNAL PANIC: ...`) or the
    `EnvExtension` corruption it signals; plain mentions of the word `PANIC` do not match. -/
def isRuntimePanicText (s : String) : Bool :=
  ["PANIC at ", "INTERNAL PANIC", "invalid environment extension"].any (fun m => (s.splitOn m).length > 1)

end TurboLean.ZygoteWorker
